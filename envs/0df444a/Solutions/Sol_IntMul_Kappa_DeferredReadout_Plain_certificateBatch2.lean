-- Prove2me | solution 1 for IntMul.Kappa.DeferredReadout.Plain.certificateBatch2
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T08:52:53.660253+00:00
-- url     : https://prove2.me/submissions/44074a0e-77f5-45b8-9cf4-28b660461b6e

import Definitions.Def_IntMul_Kappa_DeferredReadoutPlain

namespace PlainBatch1ReadoutAccess
open IntMul.Kappa.DeferredReadout

/-- A lookup tree carries the original flat array and a proof for its indexed access. -/
structure Guide (α : Type) where
  flat : Array α
  size : Nat
  get : Nat → Option α
  size_ok : flat.size = size
  get_ok : ∀ i, get i = flat[i]?

def Guide.leaf {α : Type} (xs : Array α) (n : Nat) (h : xs.size = n) : Guide α :=
  ⟨xs,n, fun i => xs[i]?,h,fun _ => rfl⟩

def Guide.join {α : Type} (l r : Guide α) (n : Nat) (hn : l.size+r.size=n) : Guide α where
  flat := l.flat ++ r.flat
  size := n
  get i := if i<l.size then l.get i else r.get (i-l.size)
  size_ok := by simpa [l.size_ok,r.size_ok] using hn
  get_ok i := by
    simp only [Array.getElem?_append, l.size_ok, l.get_ok, r.get_ok]

/-- The array in the result type gives each child its published literal
chunk. This uses ordinary type inference and kernel-checked array equations. -/
structure Table {α : Type} (xs : Array α) (n : Nat) where
  get : Nat → Option α
  size_ok : xs.size = n
  get_ok : ∀ i, get i = xs[i]?

def Table.leaf {α : Type} {xs : Array α} (n : Nat) (h : xs.size=n) : Table xs n :=
  ⟨fun i => xs[i]?,h,fun _ => rfl⟩

def Table.append {α : Type} {xs ys : Array α} (n m : Nat)
    (l : Table xs n) (r : Table ys m) : Table (xs ++ ys) (n+m) where
  get i := if i<n then l.get i else r.get (i-n)
  size_ok := by simp [l.size_ok,r.size_ok]
  get_ok i := by simp only [Array.getElem?_append,l.size_ok,l.get_ok,r.get_ok]

def Table.guide {α : Type} {xs : Array α} {n : Nat} (t : Table xs n) : Guide α :=
  ⟨xs,n,t.get,t.size_ok,t.get_ok⟩

structure Index (d : Block) where
  rs : Guide Nat
  bs : Guide Frame
  ids : Guide Identity
  es : Guide Edge
  ts : Guide (List Event)
  hr : rs.flat=d.rows
  hb : bs.flat=d.frames
  hi : ids.flat=d.ids
  he : es.flat=d.edges
  ht : ts.flat=d.targets

variable {d : Block} (f : Index d)

def Index.entry : RowTable := fun r j => (((((f.rs.get r).getD 0 >>> (5*j)) % 32 : Nat) : Int)) - 16
def Index.basis (n : Nat) := (f.bs.get n).getD []
def Index.idAt (n : Nat) := (f.ids.get n).getD default
def Index.edgeAt (n : Nat) := (f.es.get n).getD default
def Index.events (n : Nat) := (f.ts.get n).getD []

theorem Index.entry_eq : f.entry = d.entry := by
  funext r j
  simp [Index.entry, Block.entry, f.rs.get_ok, f.hr]
theorem Index.basis_eq : f.basis = d.basis := by
  funext i; simp [Index.basis, Block.basis, f.bs.get_ok, f.hb]
theorem Index.id_eq : f.idAt = d.identity := by
  funext i; simp [Index.idAt, Block.identity, f.ids.get_ok, f.hi]
theorem Index.edge_eq : f.edgeAt = d.edge := by
  funext i; simp [Index.edgeAt, Block.edge, f.es.get_ok, f.he]
theorem Index.events_eq (i : Nat) : f.events i = d.targets[i]?.getD [] := by
  simp [Index.events, f.ts.get_ok, f.ht]

def Index.checkId (i : Nat) := validIdentity 23 f.entry (f.idAt i)
def Index.checkEdge (i : Nat) : Bool :=
  let e := f.edgeAt i
  (e.refs.all fun j => decide (j < f.ids.size)) &&
  edgeCheck f.idAt (f.basis e.first) (f.basis e.second) e.refs
def Index.trans (a b : Event) : Bool :=
  a.frame == b.frame || (decide (a.edge < f.es.size) &&
     (f.edgeAt a.edge).first == a.frame && (f.edgeAt a.edge).second == b.frame)
def Index.timeline (f : Index d) : List Event → Bool
  | [] | [_] => true
  | a :: b :: rest => f.trans a b && Index.timeline f (b :: rest)

theorem Index.time_eq (xs : List Event) : f.timeline xs = d.timelineOK xs := by
  induction xs using List.twoStepInduction with
  | nil => rfl
  | singleton => rfl
  | cons_cons a b rest _ ih =>
    simp only [Index.timeline, Block.timelineOK, Index.trans, Block.transitionOK,
      f.edge_eq, ← f.es.size_ok, f.he, ih b]

private theorem arrayAll {α : Type} [Inhabited α] (xs : Array α) (p : α → Bool)
    (h : ∀ i < xs.size, p (xs[i]?.getD default) = true) : xs.toList.all p = true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨i,hi,he⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hx)
  specialize h i hi
  simpa [hi,he] using h

def Within (p : Nat → Bool) (a n : Nat) := ∀ j, a ≤ j → j < a+n → p j = true

theorem within_leaf {p : Nat → Bool} {a n : Nat}
    (h : (List.range n).all (fun j => p (a+j)) = true) : Within p a n := by
  intro j hlo hhi
  have hj : j-a<n := by omega
  have hit := List.all_eq_true.mp h (j-a) (List.mem_range.mpr hj)
  rwa [Nat.add_sub_of_le hlo] at hit

theorem within_join {p : Nat → Bool} {a l r : Nat} (hl : Within p a l)
    (hr : Within p (a+l) r) : Within p a (l+r) := by
  intro j hj hjr
  by_cases h : j<a+l
  · exact hl j hj h
  · exact hr j (by omega) (by omega)

theorem Index.identities (h : Within f.checkId 0 f.ids.size) : d.identitiesOK = true := by
  apply arrayAll
  intro i hi
  rw [← f.hi, f.ids.size_ok] at hi
  simpa [Index.checkId,f.entry_eq,f.id_eq,Block.identity] using h i (Nat.zero_le _) (by simpa using hi)

theorem Index.edges (h : Within f.checkEdge 0 f.es.size) : d.edgesOK = true := by
  apply arrayAll
  intro i hi
  rw [← f.he, f.es.size_ok] at hi
  simpa [Index.checkEdge,f.edge_eq,f.id_eq,f.basis_eq,← f.ids.size_ok, f.hi,
    Block.edgeOK, Block.edge] using h i (Nat.zero_le _) (by simpa using hi)

theorem Index.times (h : Within (fun i => f.timeline (f.events i)) 0 f.ts.size) : d.timelinesOK = true := by
  apply arrayAll
  intro i hi
  have hdi := hi
  rw [← f.ht, f.ts.size_ok] at hi
  simpa [f.time_eq,f.events_eq,hdi] using h i (Nat.zero_le _) (by simpa using hi)

end PlainBatch1ReadoutAccess

open PlainBatch1ReadoutAccess IntMul.Kappa.DeferredReadout
set_option maxRecDepth 12000
set_option maxHeartbeats 0
private def table_rows : Table Plain.rows 1126 := by
  unfold Plain.rows
  exact (Table.append 572 554 (Table.append 260 312 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 156 156 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))))
 (Table.append 260 294 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 156 138 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 52 86 (Table.leaf 52 rfl)
 (Table.append 52 34 (Table.leaf 52 rfl)
 (Table.leaf 34 rfl))))))

private def table_bases : Table Plain.bases 4230 := by
  unfold Plain.bases
  exact (Table.append 2132 2098 (Table.append 1040 1092 (Table.append 520 520 (Table.append 260 260 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))))
 (Table.append 260 260 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))))
 (Table.append 520 572 (Table.append 260 260 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))))
 (Table.append 260 312 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 156 156 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))))))
 (Table.append 1040 1058 (Table.append 520 520 (Table.append 260 260 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))))
 (Table.append 260 260 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))))
 (Table.append 520 538 (Table.append 260 260 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))))
 (Table.append 260 278 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 156 122 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 52 70 (Table.leaf 52 rfl)
 (Table.append 52 18 (Table.leaf 52 rfl)
 (Table.leaf 18 rfl))))))))

private def table_identities : Table Plain.identities 2937 := by
  unfold Plain.identities
  exact (Table.append 1456 1481 (Table.append 728 728 (Table.append 364 364 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))))
 (Table.append 364 364 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))))
 (Table.append 728 753 (Table.append 364 364 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))))
 (Table.append 364 389 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 208 181 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 77 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 25 (Table.leaf 52 rfl)
 (Table.leaf 25 rfl)))))))

private def table_edges : Table Plain.edges 5781 := by
  unfold Plain.edges
  exact (Table.append 2912 2869 (Table.append 1456 1456 (Table.append 728 728 (Table.append 364 364 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))))
 (Table.append 364 364 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))))
 (Table.append 728 728 (Table.append 364 364 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))))
 (Table.append 364 364 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))))))
 (Table.append 1456 1413 (Table.append 728 728 (Table.append 364 364 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))))
 (Table.append 364 364 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))))
 (Table.append 728 685 (Table.append 364 364 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))))
 (Table.append 364 321 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 156 165 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 61 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 9 (Table.leaf 52 rfl)
 (Table.leaf 9 rfl))))))))

private def table_timelines : Table Plain.timelines 1771 := by
  unfold Plain.timelines
  exact (Table.append 884 887 (Table.append 416 468 (Table.append 208 208 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 208 260 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))))
 (Table.append 468 419 (Table.append 208 260 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))))
 (Table.append 208 211 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 107 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 55 (Table.leaf 52 rfl)
 (Table.append 52 3 (Table.leaf 52 rfl)
 (Table.leaf 3 rfl)))))))

private def view : Index Plain.schedule where
  rs := table_rows.guide
  bs := table_bases.guide
  ids := table_identities.guide
  es := table_edges.guide
  ts := table_timelines.guide
  hr := rfl
  hb := rfl
  hi := rfl
  he := rfl
  ht := rfl

private theorem indices489 : Within (view.checkId) 489 25 := within_leaf (by decide +kernel)

private theorem indices514 : Within (view.checkId) 514 25 := within_leaf (by decide +kernel)

private theorem indices539 : Within (view.checkId) 539 25 := within_leaf (by decide +kernel)

private theorem indices564 : Within (view.checkId) 564 25 := within_leaf (by decide +kernel)

private theorem indices589 : Within (view.checkId) 589 25 := within_leaf (by decide +kernel)

private theorem indices614 : Within (view.checkId) 614 25 := within_leaf (by decide +kernel)

private theorem indices639 : Within (view.checkId) 639 25 := within_leaf (by decide +kernel)

private theorem indices664 : Within (view.checkId) 664 25 := within_leaf (by decide +kernel)

private theorem indices689 : Within (view.checkId) 689 25 := within_leaf (by decide +kernel)

private theorem indices714 : Within (view.checkId) 714 25 := within_leaf (by decide +kernel)

private theorem indices739 : Within (view.checkId) 739 25 := within_leaf (by decide +kernel)

private theorem indices764 : Within (view.checkId) 764 25 := within_leaf (by decide +kernel)

private theorem indices789 : Within (view.checkId) 789 25 := within_leaf (by decide +kernel)

private theorem indices814 : Within (view.checkId) 814 25 := within_leaf (by decide +kernel)

private theorem indices839 : Within (view.checkId) 839 25 := within_leaf (by decide +kernel)

private theorem indices864 : Within (view.checkId) 864 25 := within_leaf (by decide +kernel)

private theorem indices889 : Within (view.checkId) 889 25 := within_leaf (by decide +kernel)

private theorem indices914 : Within (view.checkId) 914 25 := within_leaf (by decide +kernel)

private theorem indices939 : Within (view.checkId) 939 25 := within_leaf (by decide +kernel)

private theorem indices964 : Within (view.checkId) 964 15 := within_leaf (by decide +kernel)

private theorem indicesPart : Within (view.checkId) 489 490 :=
  (within_join (a:=489) (l:=250) (r:=240) (within_join (a:=489) (l:=125) (r:=125) (within_join (a:=489) (l:=50) (r:=75) (within_join (a:=489) (l:=25) (r:=25) indices489 indices514) (within_join (a:=539) (l:=25) (r:=50) indices539 (within_join (a:=564) (l:=25) (r:=25) indices564 indices589))) (within_join (a:=614) (l:=50) (r:=75) (within_join (a:=614) (l:=25) (r:=25) indices614 indices639) (within_join (a:=664) (l:=25) (r:=50) indices664 (within_join (a:=689) (l:=25) (r:=25) indices689 indices714)))) (within_join (a:=739) (l:=125) (r:=115) (within_join (a:=739) (l:=50) (r:=75) (within_join (a:=739) (l:=25) (r:=25) indices739 indices764) (within_join (a:=789) (l:=25) (r:=50) indices789 (within_join (a:=814) (l:=25) (r:=25) indices814 indices839))) (within_join (a:=864) (l:=50) (r:=65) (within_join (a:=864) (l:=25) (r:=25) indices864 indices889) (within_join (a:=914) (l:=25) (r:=40) indices914 (within_join (a:=939) (l:=25) (r:=15) indices939 indices964)))))

private theorem ed963 : Within (view.checkEdge) 963 25 := within_leaf (by decide +kernel)

private theorem ed988 : Within (view.checkEdge) 988 25 := within_leaf (by decide +kernel)

private theorem ed1013 : Within (view.checkEdge) 1013 25 := within_leaf (by decide +kernel)

private theorem ed1038 : Within (view.checkEdge) 1038 25 := within_leaf (by decide +kernel)

private theorem ed1063 : Within (view.checkEdge) 1063 25 := within_leaf (by decide +kernel)

private theorem ed1088 : Within (view.checkEdge) 1088 25 := within_leaf (by decide +kernel)

private theorem ed1113 : Within (view.checkEdge) 1113 25 := within_leaf (by decide +kernel)

private theorem ed1138 : Within (view.checkEdge) 1138 25 := within_leaf (by decide +kernel)

private theorem ed1163 : Within (view.checkEdge) 1163 25 := within_leaf (by decide +kernel)

private theorem ed1188 : Within (view.checkEdge) 1188 25 := within_leaf (by decide +kernel)

private theorem ed1213 : Within (view.checkEdge) 1213 25 := within_leaf (by decide +kernel)

private theorem ed1238 : Within (view.checkEdge) 1238 25 := within_leaf (by decide +kernel)

private theorem ed1263 : Within (view.checkEdge) 1263 25 := within_leaf (by decide +kernel)

private theorem ed1288 : Within (view.checkEdge) 1288 25 := within_leaf (by decide +kernel)

private theorem ed1313 : Within (view.checkEdge) 1313 25 := within_leaf (by decide +kernel)

private theorem ed1338 : Within (view.checkEdge) 1338 25 := within_leaf (by decide +kernel)

private theorem ed1363 : Within (view.checkEdge) 1363 25 := within_leaf (by decide +kernel)

private theorem ed1388 : Within (view.checkEdge) 1388 25 := within_leaf (by decide +kernel)

private theorem ed1413 : Within (view.checkEdge) 1413 25 := within_leaf (by decide +kernel)

private theorem ed1438 : Within (view.checkEdge) 1438 25 := within_leaf (by decide +kernel)

private theorem ed1463 : Within (view.checkEdge) 1463 25 := within_leaf (by decide +kernel)

private theorem ed1488 : Within (view.checkEdge) 1488 25 := within_leaf (by decide +kernel)

private theorem ed1513 : Within (view.checkEdge) 1513 25 := within_leaf (by decide +kernel)

private theorem ed1538 : Within (view.checkEdge) 1538 25 := within_leaf (by decide +kernel)

private theorem ed1563 : Within (view.checkEdge) 1563 25 := within_leaf (by decide +kernel)

private theorem ed1588 : Within (view.checkEdge) 1588 25 := within_leaf (by decide +kernel)

private theorem ed1613 : Within (view.checkEdge) 1613 25 := within_leaf (by decide +kernel)

private theorem ed1638 : Within (view.checkEdge) 1638 25 := within_leaf (by decide +kernel)

private theorem ed1663 : Within (view.checkEdge) 1663 25 := within_leaf (by decide +kernel)

private theorem ed1688 : Within (view.checkEdge) 1688 25 := within_leaf (by decide +kernel)

private theorem ed1713 : Within (view.checkEdge) 1713 25 := within_leaf (by decide +kernel)

private theorem ed1738 : Within (view.checkEdge) 1738 25 := within_leaf (by decide +kernel)

private theorem ed1763 : Within (view.checkEdge) 1763 25 := within_leaf (by decide +kernel)

private theorem ed1788 : Within (view.checkEdge) 1788 25 := within_leaf (by decide +kernel)

private theorem ed1813 : Within (view.checkEdge) 1813 25 := within_leaf (by decide +kernel)

private theorem ed1838 : Within (view.checkEdge) 1838 25 := within_leaf (by decide +kernel)

private theorem ed1863 : Within (view.checkEdge) 1863 25 := within_leaf (by decide +kernel)

private theorem ed1888 : Within (view.checkEdge) 1888 25 := within_leaf (by decide +kernel)

private theorem ed1913 : Within (view.checkEdge) 1913 14 := within_leaf (by decide +kernel)

private theorem edPart : Within (view.checkEdge) 963 964 :=
  (within_join (a:=963) (l:=475) (r:=489) (within_join (a:=963) (l:=225) (r:=250) (within_join (a:=963) (l:=100) (r:=125) (within_join (a:=963) (l:=50) (r:=50) (within_join (a:=963) (l:=25) (r:=25) ed963 ed988) (within_join (a:=1013) (l:=25) (r:=25) ed1013 ed1038)) (within_join (a:=1063) (l:=50) (r:=75) (within_join (a:=1063) (l:=25) (r:=25) ed1063 ed1088) (within_join (a:=1113) (l:=25) (r:=50) ed1113 (within_join (a:=1138) (l:=25) (r:=25) ed1138 ed1163)))) (within_join (a:=1188) (l:=125) (r:=125) (within_join (a:=1188) (l:=50) (r:=75) (within_join (a:=1188) (l:=25) (r:=25) ed1188 ed1213) (within_join (a:=1238) (l:=25) (r:=50) ed1238 (within_join (a:=1263) (l:=25) (r:=25) ed1263 ed1288))) (within_join (a:=1313) (l:=50) (r:=75) (within_join (a:=1313) (l:=25) (r:=25) ed1313 ed1338) (within_join (a:=1363) (l:=25) (r:=50) ed1363 (within_join (a:=1388) (l:=25) (r:=25) ed1388 ed1413))))) (within_join (a:=1438) (l:=250) (r:=239) (within_join (a:=1438) (l:=125) (r:=125) (within_join (a:=1438) (l:=50) (r:=75) (within_join (a:=1438) (l:=25) (r:=25) ed1438 ed1463) (within_join (a:=1488) (l:=25) (r:=50) ed1488 (within_join (a:=1513) (l:=25) (r:=25) ed1513 ed1538))) (within_join (a:=1563) (l:=50) (r:=75) (within_join (a:=1563) (l:=25) (r:=25) ed1563 ed1588) (within_join (a:=1613) (l:=25) (r:=50) ed1613 (within_join (a:=1638) (l:=25) (r:=25) ed1638 ed1663)))) (within_join (a:=1688) (l:=125) (r:=114) (within_join (a:=1688) (l:=50) (r:=75) (within_join (a:=1688) (l:=25) (r:=25) ed1688 ed1713) (within_join (a:=1738) (l:=25) (r:=50) ed1738 (within_join (a:=1763) (l:=25) (r:=25) ed1763 ed1788))) (within_join (a:=1813) (l:=50) (r:=64) (within_join (a:=1813) (l:=25) (r:=25) ed1813 ed1838) (within_join (a:=1863) (l:=25) (r:=39) ed1863 (within_join (a:=1888) (l:=25) (r:=14) ed1888 ed1913))))))

private theorem tm295 : Within (fun i => view.timeline (view.events i)) 295 25 := within_leaf (by decide +kernel)

private theorem tm320 : Within (fun i => view.timeline (view.events i)) 320 25 := within_leaf (by decide +kernel)

private theorem tm345 : Within (fun i => view.timeline (view.events i)) 345 25 := within_leaf (by decide +kernel)

private theorem tm370 : Within (fun i => view.timeline (view.events i)) 370 25 := within_leaf (by decide +kernel)

private theorem tm395 : Within (fun i => view.timeline (view.events i)) 395 25 := within_leaf (by decide +kernel)

private theorem tm420 : Within (fun i => view.timeline (view.events i)) 420 25 := within_leaf (by decide +kernel)

private theorem tm445 : Within (fun i => view.timeline (view.events i)) 445 25 := within_leaf (by decide +kernel)

private theorem tm470 : Within (fun i => view.timeline (view.events i)) 470 25 := within_leaf (by decide +kernel)

private theorem tm495 : Within (fun i => view.timeline (view.events i)) 495 25 := within_leaf (by decide +kernel)

private theorem tm520 : Within (fun i => view.timeline (view.events i)) 520 25 := within_leaf (by decide +kernel)

private theorem tm545 : Within (fun i => view.timeline (view.events i)) 545 25 := within_leaf (by decide +kernel)

private theorem tm570 : Within (fun i => view.timeline (view.events i)) 570 20 := within_leaf (by decide +kernel)

private theorem tmPart : Within (fun i => view.timeline (view.events i)) 295 295 :=
  (within_join (a:=295) (l:=150) (r:=145) (within_join (a:=295) (l:=75) (r:=75) (within_join (a:=295) (l:=25) (r:=50) tm295 (within_join (a:=320) (l:=25) (r:=25) tm320 tm345)) (within_join (a:=370) (l:=25) (r:=50) tm370 (within_join (a:=395) (l:=25) (r:=25) tm395 tm420))) (within_join (a:=445) (l:=75) (r:=70) (within_join (a:=445) (l:=25) (r:=50) tm445 (within_join (a:=470) (l:=25) (r:=25) tm470 tm495)) (within_join (a:=520) (l:=25) (r:=45) tm520 (within_join (a:=545) (l:=25) (r:=20) tm545 tm570))))

theorem solution :
    (∀ i, 489 ≤ i → i < 979 → validIdentity 23 Plain.schedule.entry (Plain.schedule.identity i) = true) ∧
    (∀ i, 963 ≤ i → i < 1927 → Plain.schedule.edgeOK (Plain.schedule.edge i) = true) ∧
    (∀ i, 295 ≤ i → i < 590 → Plain.schedule.timelineOK (Plain.schedule.targets[i]?.getD []) = true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i ha hb
    simpa only [Index.checkId, view.entry_eq, view.id_eq] using indicesPart i ha (by omega)
  · intro i ha hb
    simpa only [Index.checkEdge, view.edge_eq, view.id_eq, view.basis_eq, ← view.ids.size_ok, view.hi,
      Block.edgeOK] using edPart i ha (by omega)
  · intro i ha hb
    simpa only [view.time_eq, view.events_eq] using tmPart i ha (by omega)
