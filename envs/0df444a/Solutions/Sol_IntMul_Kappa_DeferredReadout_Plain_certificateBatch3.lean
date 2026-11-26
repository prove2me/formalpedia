-- Prove2me | solution 1 for IntMul.Kappa.DeferredReadout.Plain.certificateBatch3
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T08:52:58.793667+00:00
-- url     : https://prove2.me/submissions/9807c984-e823-4cf6-8c28-c756ef55df39

import Definitions.Def_IntMul_Kappa_DeferredReadoutPlain

namespace PlainBatch2ReadoutAccess
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

end PlainBatch2ReadoutAccess

open PlainBatch2ReadoutAccess IntMul.Kappa.DeferredReadout
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

private theorem indices979 : Within (view.checkId) 979 25 := within_leaf (by decide +kernel)

private theorem indices1004 : Within (view.checkId) 1004 25 := within_leaf (by decide +kernel)

private theorem indices1029 : Within (view.checkId) 1029 25 := within_leaf (by decide +kernel)

private theorem indices1054 : Within (view.checkId) 1054 25 := within_leaf (by decide +kernel)

private theorem indices1079 : Within (view.checkId) 1079 25 := within_leaf (by decide +kernel)

private theorem indices1104 : Within (view.checkId) 1104 25 := within_leaf (by decide +kernel)

private theorem indices1129 : Within (view.checkId) 1129 25 := within_leaf (by decide +kernel)

private theorem indices1154 : Within (view.checkId) 1154 25 := within_leaf (by decide +kernel)

private theorem indices1179 : Within (view.checkId) 1179 25 := within_leaf (by decide +kernel)

private theorem indices1204 : Within (view.checkId) 1204 25 := within_leaf (by decide +kernel)

private theorem indices1229 : Within (view.checkId) 1229 25 := within_leaf (by decide +kernel)

private theorem indices1254 : Within (view.checkId) 1254 25 := within_leaf (by decide +kernel)

private theorem indices1279 : Within (view.checkId) 1279 25 := within_leaf (by decide +kernel)

private theorem indices1304 : Within (view.checkId) 1304 25 := within_leaf (by decide +kernel)

private theorem indices1329 : Within (view.checkId) 1329 25 := within_leaf (by decide +kernel)

private theorem indices1354 : Within (view.checkId) 1354 25 := within_leaf (by decide +kernel)

private theorem indices1379 : Within (view.checkId) 1379 25 := within_leaf (by decide +kernel)

private theorem indices1404 : Within (view.checkId) 1404 25 := within_leaf (by decide +kernel)

private theorem indices1429 : Within (view.checkId) 1429 25 := within_leaf (by decide +kernel)

private theorem indices1454 : Within (view.checkId) 1454 14 := within_leaf (by decide +kernel)

private theorem indicesPart : Within (view.checkId) 979 489 :=
  (within_join (a:=979) (l:=250) (r:=239) (within_join (a:=979) (l:=125) (r:=125) (within_join (a:=979) (l:=50) (r:=75) (within_join (a:=979) (l:=25) (r:=25) indices979 indices1004) (within_join (a:=1029) (l:=25) (r:=50) indices1029 (within_join (a:=1054) (l:=25) (r:=25) indices1054 indices1079))) (within_join (a:=1104) (l:=50) (r:=75) (within_join (a:=1104) (l:=25) (r:=25) indices1104 indices1129) (within_join (a:=1154) (l:=25) (r:=50) indices1154 (within_join (a:=1179) (l:=25) (r:=25) indices1179 indices1204)))) (within_join (a:=1229) (l:=125) (r:=114) (within_join (a:=1229) (l:=50) (r:=75) (within_join (a:=1229) (l:=25) (r:=25) indices1229 indices1254) (within_join (a:=1279) (l:=25) (r:=50) indices1279 (within_join (a:=1304) (l:=25) (r:=25) indices1304 indices1329))) (within_join (a:=1354) (l:=50) (r:=64) (within_join (a:=1354) (l:=25) (r:=25) indices1354 indices1379) (within_join (a:=1404) (l:=25) (r:=39) indices1404 (within_join (a:=1429) (l:=25) (r:=14) indices1429 indices1454)))))

private theorem ed1927 : Within (view.checkEdge) 1927 25 := within_leaf (by decide +kernel)

private theorem ed1952 : Within (view.checkEdge) 1952 25 := within_leaf (by decide +kernel)

private theorem ed1977 : Within (view.checkEdge) 1977 25 := within_leaf (by decide +kernel)

private theorem ed2002 : Within (view.checkEdge) 2002 25 := within_leaf (by decide +kernel)

private theorem ed2027 : Within (view.checkEdge) 2027 25 := within_leaf (by decide +kernel)

private theorem ed2052 : Within (view.checkEdge) 2052 25 := within_leaf (by decide +kernel)

private theorem ed2077 : Within (view.checkEdge) 2077 25 := within_leaf (by decide +kernel)

private theorem ed2102 : Within (view.checkEdge) 2102 25 := within_leaf (by decide +kernel)

private theorem ed2127 : Within (view.checkEdge) 2127 25 := within_leaf (by decide +kernel)

private theorem ed2152 : Within (view.checkEdge) 2152 25 := within_leaf (by decide +kernel)

private theorem ed2177 : Within (view.checkEdge) 2177 25 := within_leaf (by decide +kernel)

private theorem ed2202 : Within (view.checkEdge) 2202 25 := within_leaf (by decide +kernel)

private theorem ed2227 : Within (view.checkEdge) 2227 25 := within_leaf (by decide +kernel)

private theorem ed2252 : Within (view.checkEdge) 2252 25 := within_leaf (by decide +kernel)

private theorem ed2277 : Within (view.checkEdge) 2277 25 := within_leaf (by decide +kernel)

private theorem ed2302 : Within (view.checkEdge) 2302 25 := within_leaf (by decide +kernel)

private theorem ed2327 : Within (view.checkEdge) 2327 25 := within_leaf (by decide +kernel)

private theorem ed2352 : Within (view.checkEdge) 2352 25 := within_leaf (by decide +kernel)

private theorem ed2377 : Within (view.checkEdge) 2377 25 := within_leaf (by decide +kernel)

private theorem ed2402 : Within (view.checkEdge) 2402 25 := within_leaf (by decide +kernel)

private theorem ed2427 : Within (view.checkEdge) 2427 25 := within_leaf (by decide +kernel)

private theorem ed2452 : Within (view.checkEdge) 2452 25 := within_leaf (by decide +kernel)

private theorem ed2477 : Within (view.checkEdge) 2477 25 := within_leaf (by decide +kernel)

private theorem ed2502 : Within (view.checkEdge) 2502 25 := within_leaf (by decide +kernel)

private theorem ed2527 : Within (view.checkEdge) 2527 25 := within_leaf (by decide +kernel)

private theorem ed2552 : Within (view.checkEdge) 2552 25 := within_leaf (by decide +kernel)

private theorem ed2577 : Within (view.checkEdge) 2577 25 := within_leaf (by decide +kernel)

private theorem ed2602 : Within (view.checkEdge) 2602 25 := within_leaf (by decide +kernel)

private theorem ed2627 : Within (view.checkEdge) 2627 25 := within_leaf (by decide +kernel)

private theorem ed2652 : Within (view.checkEdge) 2652 25 := within_leaf (by decide +kernel)

private theorem ed2677 : Within (view.checkEdge) 2677 25 := within_leaf (by decide +kernel)

private theorem ed2702 : Within (view.checkEdge) 2702 25 := within_leaf (by decide +kernel)

private theorem ed2727 : Within (view.checkEdge) 2727 25 := within_leaf (by decide +kernel)

private theorem ed2752 : Within (view.checkEdge) 2752 25 := within_leaf (by decide +kernel)

private theorem ed2777 : Within (view.checkEdge) 2777 25 := within_leaf (by decide +kernel)

private theorem ed2802 : Within (view.checkEdge) 2802 25 := within_leaf (by decide +kernel)

private theorem ed2827 : Within (view.checkEdge) 2827 25 := within_leaf (by decide +kernel)

private theorem ed2852 : Within (view.checkEdge) 2852 25 := within_leaf (by decide +kernel)

private theorem ed2877 : Within (view.checkEdge) 2877 13 := within_leaf (by decide +kernel)

private theorem edPart : Within (view.checkEdge) 1927 963 :=
  (within_join (a:=1927) (l:=475) (r:=488) (within_join (a:=1927) (l:=225) (r:=250) (within_join (a:=1927) (l:=100) (r:=125) (within_join (a:=1927) (l:=50) (r:=50) (within_join (a:=1927) (l:=25) (r:=25) ed1927 ed1952) (within_join (a:=1977) (l:=25) (r:=25) ed1977 ed2002)) (within_join (a:=2027) (l:=50) (r:=75) (within_join (a:=2027) (l:=25) (r:=25) ed2027 ed2052) (within_join (a:=2077) (l:=25) (r:=50) ed2077 (within_join (a:=2102) (l:=25) (r:=25) ed2102 ed2127)))) (within_join (a:=2152) (l:=125) (r:=125) (within_join (a:=2152) (l:=50) (r:=75) (within_join (a:=2152) (l:=25) (r:=25) ed2152 ed2177) (within_join (a:=2202) (l:=25) (r:=50) ed2202 (within_join (a:=2227) (l:=25) (r:=25) ed2227 ed2252))) (within_join (a:=2277) (l:=50) (r:=75) (within_join (a:=2277) (l:=25) (r:=25) ed2277 ed2302) (within_join (a:=2327) (l:=25) (r:=50) ed2327 (within_join (a:=2352) (l:=25) (r:=25) ed2352 ed2377))))) (within_join (a:=2402) (l:=250) (r:=238) (within_join (a:=2402) (l:=125) (r:=125) (within_join (a:=2402) (l:=50) (r:=75) (within_join (a:=2402) (l:=25) (r:=25) ed2402 ed2427) (within_join (a:=2452) (l:=25) (r:=50) ed2452 (within_join (a:=2477) (l:=25) (r:=25) ed2477 ed2502))) (within_join (a:=2527) (l:=50) (r:=75) (within_join (a:=2527) (l:=25) (r:=25) ed2527 ed2552) (within_join (a:=2577) (l:=25) (r:=50) ed2577 (within_join (a:=2602) (l:=25) (r:=25) ed2602 ed2627)))) (within_join (a:=2652) (l:=125) (r:=113) (within_join (a:=2652) (l:=50) (r:=75) (within_join (a:=2652) (l:=25) (r:=25) ed2652 ed2677) (within_join (a:=2702) (l:=25) (r:=50) ed2702 (within_join (a:=2727) (l:=25) (r:=25) ed2727 ed2752))) (within_join (a:=2777) (l:=50) (r:=63) (within_join (a:=2777) (l:=25) (r:=25) ed2777 ed2802) (within_join (a:=2827) (l:=25) (r:=38) ed2827 (within_join (a:=2852) (l:=25) (r:=13) ed2852 ed2877))))))

private theorem tm590 : Within (fun i => view.timeline (view.events i)) 590 25 := within_leaf (by decide +kernel)

private theorem tm615 : Within (fun i => view.timeline (view.events i)) 615 25 := within_leaf (by decide +kernel)

private theorem tm640 : Within (fun i => view.timeline (view.events i)) 640 25 := within_leaf (by decide +kernel)

private theorem tm665 : Within (fun i => view.timeline (view.events i)) 665 25 := within_leaf (by decide +kernel)

private theorem tm690 : Within (fun i => view.timeline (view.events i)) 690 25 := within_leaf (by decide +kernel)

private theorem tm715 : Within (fun i => view.timeline (view.events i)) 715 25 := within_leaf (by decide +kernel)

private theorem tm740 : Within (fun i => view.timeline (view.events i)) 740 25 := within_leaf (by decide +kernel)

private theorem tm765 : Within (fun i => view.timeline (view.events i)) 765 25 := within_leaf (by decide +kernel)

private theorem tm790 : Within (fun i => view.timeline (view.events i)) 790 25 := within_leaf (by decide +kernel)

private theorem tm815 : Within (fun i => view.timeline (view.events i)) 815 25 := within_leaf (by decide +kernel)

private theorem tm840 : Within (fun i => view.timeline (view.events i)) 840 25 := within_leaf (by decide +kernel)

private theorem tm865 : Within (fun i => view.timeline (view.events i)) 865 20 := within_leaf (by decide +kernel)

private theorem tmPart : Within (fun i => view.timeline (view.events i)) 590 295 :=
  (within_join (a:=590) (l:=150) (r:=145) (within_join (a:=590) (l:=75) (r:=75) (within_join (a:=590) (l:=25) (r:=50) tm590 (within_join (a:=615) (l:=25) (r:=25) tm615 tm640)) (within_join (a:=665) (l:=25) (r:=50) tm665 (within_join (a:=690) (l:=25) (r:=25) tm690 tm715))) (within_join (a:=740) (l:=75) (r:=70) (within_join (a:=740) (l:=25) (r:=50) tm740 (within_join (a:=765) (l:=25) (r:=25) tm765 tm790)) (within_join (a:=815) (l:=25) (r:=45) tm815 (within_join (a:=840) (l:=25) (r:=20) tm840 tm865))))

theorem solution :
    (∀ i, 979 ≤ i → i < 1468 → validIdentity 23 Plain.schedule.entry (Plain.schedule.identity i) = true) ∧
    (∀ i, 1927 ≤ i → i < 2890 → Plain.schedule.edgeOK (Plain.schedule.edge i) = true) ∧
    (∀ i, 590 ≤ i → i < 885 → Plain.schedule.timelineOK (Plain.schedule.targets[i]?.getD []) = true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i ha hb
    simpa only [Index.checkId, view.entry_eq, view.id_eq] using indicesPart i ha (by omega)
  · intro i ha hb
    simpa only [Index.checkEdge, view.edge_eq, view.id_eq, view.basis_eq, ← view.ids.size_ok, view.hi,
      Block.edgeOK] using edPart i ha (by omega)
  · intro i ha hb
    simpa only [view.time_eq, view.events_eq] using tmPart i ha (by omega)
