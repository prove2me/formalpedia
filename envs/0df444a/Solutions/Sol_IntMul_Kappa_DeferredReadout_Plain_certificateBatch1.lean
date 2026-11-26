-- Prove2me | solution 1 for IntMul.Kappa.DeferredReadout.Plain.certificateBatch1
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T08:51:15.98247+00:00
-- url     : https://prove2.me/submissions/c2ea9416-ebd1-4f4d-9c43-f17d69c6ab8f

import Definitions.Def_IntMul_Kappa_DeferredReadoutPlain

namespace PlainBatch0ReadoutAccess
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

end PlainBatch0ReadoutAccess

open PlainBatch0ReadoutAccess IntMul.Kappa.DeferredReadout
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

private theorem indices0 : Within (view.checkId) 0 25 := within_leaf (by decide +kernel)

private theorem indices25 : Within (view.checkId) 25 25 := within_leaf (by decide +kernel)

private theorem indices50 : Within (view.checkId) 50 25 := within_leaf (by decide +kernel)

private theorem indices75 : Within (view.checkId) 75 25 := within_leaf (by decide +kernel)

private theorem indices100 : Within (view.checkId) 100 25 := within_leaf (by decide +kernel)

private theorem indices125 : Within (view.checkId) 125 25 := within_leaf (by decide +kernel)

private theorem indices150 : Within (view.checkId) 150 25 := within_leaf (by decide +kernel)

private theorem indices175 : Within (view.checkId) 175 25 := within_leaf (by decide +kernel)

private theorem indices200 : Within (view.checkId) 200 25 := within_leaf (by decide +kernel)

private theorem indices225 : Within (view.checkId) 225 25 := within_leaf (by decide +kernel)

private theorem indices250 : Within (view.checkId) 250 25 := within_leaf (by decide +kernel)

private theorem indices275 : Within (view.checkId) 275 25 := within_leaf (by decide +kernel)

private theorem indices300 : Within (view.checkId) 300 25 := within_leaf (by decide +kernel)

private theorem indices325 : Within (view.checkId) 325 25 := within_leaf (by decide +kernel)

private theorem indices350 : Within (view.checkId) 350 25 := within_leaf (by decide +kernel)

private theorem indices375 : Within (view.checkId) 375 25 := within_leaf (by decide +kernel)

private theorem indices400 : Within (view.checkId) 400 25 := within_leaf (by decide +kernel)

private theorem indices425 : Within (view.checkId) 425 25 := within_leaf (by decide +kernel)

private theorem indices450 : Within (view.checkId) 450 25 := within_leaf (by decide +kernel)

private theorem indices475 : Within (view.checkId) 475 14 := within_leaf (by decide +kernel)

private theorem indicesPart : Within (view.checkId) 0 489 :=
  (within_join (a:=0) (l:=250) (r:=239) (within_join (a:=0) (l:=125) (r:=125) (within_join (a:=0) (l:=50) (r:=75) (within_join (a:=0) (l:=25) (r:=25) indices0 indices25) (within_join (a:=50) (l:=25) (r:=50) indices50 (within_join (a:=75) (l:=25) (r:=25) indices75 indices100))) (within_join (a:=125) (l:=50) (r:=75) (within_join (a:=125) (l:=25) (r:=25) indices125 indices150) (within_join (a:=175) (l:=25) (r:=50) indices175 (within_join (a:=200) (l:=25) (r:=25) indices200 indices225)))) (within_join (a:=250) (l:=125) (r:=114) (within_join (a:=250) (l:=50) (r:=75) (within_join (a:=250) (l:=25) (r:=25) indices250 indices275) (within_join (a:=300) (l:=25) (r:=50) indices300 (within_join (a:=325) (l:=25) (r:=25) indices325 indices350))) (within_join (a:=375) (l:=50) (r:=64) (within_join (a:=375) (l:=25) (r:=25) indices375 indices400) (within_join (a:=425) (l:=25) (r:=39) indices425 (within_join (a:=450) (l:=25) (r:=14) indices450 indices475)))))

private theorem ed0 : Within (view.checkEdge) 0 25 := within_leaf (by decide +kernel)

private theorem ed25 : Within (view.checkEdge) 25 25 := within_leaf (by decide +kernel)

private theorem ed50 : Within (view.checkEdge) 50 25 := within_leaf (by decide +kernel)

private theorem ed75 : Within (view.checkEdge) 75 25 := within_leaf (by decide +kernel)

private theorem ed100 : Within (view.checkEdge) 100 25 := within_leaf (by decide +kernel)

private theorem ed125 : Within (view.checkEdge) 125 25 := within_leaf (by decide +kernel)

private theorem ed150 : Within (view.checkEdge) 150 25 := within_leaf (by decide +kernel)

private theorem ed175 : Within (view.checkEdge) 175 25 := within_leaf (by decide +kernel)

private theorem ed200 : Within (view.checkEdge) 200 25 := within_leaf (by decide +kernel)

private theorem ed225 : Within (view.checkEdge) 225 25 := within_leaf (by decide +kernel)

private theorem ed250 : Within (view.checkEdge) 250 25 := within_leaf (by decide +kernel)

private theorem ed275 : Within (view.checkEdge) 275 25 := within_leaf (by decide +kernel)

private theorem ed300 : Within (view.checkEdge) 300 25 := within_leaf (by decide +kernel)

private theorem ed325 : Within (view.checkEdge) 325 25 := within_leaf (by decide +kernel)

private theorem ed350 : Within (view.checkEdge) 350 25 := within_leaf (by decide +kernel)

private theorem ed375 : Within (view.checkEdge) 375 25 := within_leaf (by decide +kernel)

private theorem ed400 : Within (view.checkEdge) 400 25 := within_leaf (by decide +kernel)

private theorem ed425 : Within (view.checkEdge) 425 25 := within_leaf (by decide +kernel)

private theorem ed450 : Within (view.checkEdge) 450 25 := within_leaf (by decide +kernel)

private theorem ed475 : Within (view.checkEdge) 475 25 := within_leaf (by decide +kernel)

private theorem ed500 : Within (view.checkEdge) 500 25 := within_leaf (by decide +kernel)

private theorem ed525 : Within (view.checkEdge) 525 25 := within_leaf (by decide +kernel)

private theorem ed550 : Within (view.checkEdge) 550 25 := within_leaf (by decide +kernel)

private theorem ed575 : Within (view.checkEdge) 575 25 := within_leaf (by decide +kernel)

private theorem ed600 : Within (view.checkEdge) 600 25 := within_leaf (by decide +kernel)

private theorem ed625 : Within (view.checkEdge) 625 25 := within_leaf (by decide +kernel)

private theorem ed650 : Within (view.checkEdge) 650 25 := within_leaf (by decide +kernel)

private theorem ed675 : Within (view.checkEdge) 675 25 := within_leaf (by decide +kernel)

private theorem ed700 : Within (view.checkEdge) 700 25 := within_leaf (by decide +kernel)

private theorem ed725 : Within (view.checkEdge) 725 25 := within_leaf (by decide +kernel)

private theorem ed750 : Within (view.checkEdge) 750 25 := within_leaf (by decide +kernel)

private theorem ed775 : Within (view.checkEdge) 775 25 := within_leaf (by decide +kernel)

private theorem ed800 : Within (view.checkEdge) 800 25 := within_leaf (by decide +kernel)

private theorem ed825 : Within (view.checkEdge) 825 25 := within_leaf (by decide +kernel)

private theorem ed850 : Within (view.checkEdge) 850 25 := within_leaf (by decide +kernel)

private theorem ed875 : Within (view.checkEdge) 875 25 := within_leaf (by decide +kernel)

private theorem ed900 : Within (view.checkEdge) 900 25 := within_leaf (by decide +kernel)

private theorem ed925 : Within (view.checkEdge) 925 25 := within_leaf (by decide +kernel)

private theorem ed950 : Within (view.checkEdge) 950 13 := within_leaf (by decide +kernel)

private theorem edPart : Within (view.checkEdge) 0 963 :=
  (within_join (a:=0) (l:=475) (r:=488) (within_join (a:=0) (l:=225) (r:=250) (within_join (a:=0) (l:=100) (r:=125) (within_join (a:=0) (l:=50) (r:=50) (within_join (a:=0) (l:=25) (r:=25) ed0 ed25) (within_join (a:=50) (l:=25) (r:=25) ed50 ed75)) (within_join (a:=100) (l:=50) (r:=75) (within_join (a:=100) (l:=25) (r:=25) ed100 ed125) (within_join (a:=150) (l:=25) (r:=50) ed150 (within_join (a:=175) (l:=25) (r:=25) ed175 ed200)))) (within_join (a:=225) (l:=125) (r:=125) (within_join (a:=225) (l:=50) (r:=75) (within_join (a:=225) (l:=25) (r:=25) ed225 ed250) (within_join (a:=275) (l:=25) (r:=50) ed275 (within_join (a:=300) (l:=25) (r:=25) ed300 ed325))) (within_join (a:=350) (l:=50) (r:=75) (within_join (a:=350) (l:=25) (r:=25) ed350 ed375) (within_join (a:=400) (l:=25) (r:=50) ed400 (within_join (a:=425) (l:=25) (r:=25) ed425 ed450))))) (within_join (a:=475) (l:=250) (r:=238) (within_join (a:=475) (l:=125) (r:=125) (within_join (a:=475) (l:=50) (r:=75) (within_join (a:=475) (l:=25) (r:=25) ed475 ed500) (within_join (a:=525) (l:=25) (r:=50) ed525 (within_join (a:=550) (l:=25) (r:=25) ed550 ed575))) (within_join (a:=600) (l:=50) (r:=75) (within_join (a:=600) (l:=25) (r:=25) ed600 ed625) (within_join (a:=650) (l:=25) (r:=50) ed650 (within_join (a:=675) (l:=25) (r:=25) ed675 ed700)))) (within_join (a:=725) (l:=125) (r:=113) (within_join (a:=725) (l:=50) (r:=75) (within_join (a:=725) (l:=25) (r:=25) ed725 ed750) (within_join (a:=775) (l:=25) (r:=50) ed775 (within_join (a:=800) (l:=25) (r:=25) ed800 ed825))) (within_join (a:=850) (l:=50) (r:=63) (within_join (a:=850) (l:=25) (r:=25) ed850 ed875) (within_join (a:=900) (l:=25) (r:=38) ed900 (within_join (a:=925) (l:=25) (r:=13) ed925 ed950))))))

private theorem tm0 : Within (fun i => view.timeline (view.events i)) 0 25 := within_leaf (by decide +kernel)

private theorem tm25 : Within (fun i => view.timeline (view.events i)) 25 25 := within_leaf (by decide +kernel)

private theorem tm50 : Within (fun i => view.timeline (view.events i)) 50 25 := within_leaf (by decide +kernel)

private theorem tm75 : Within (fun i => view.timeline (view.events i)) 75 25 := within_leaf (by decide +kernel)

private theorem tm100 : Within (fun i => view.timeline (view.events i)) 100 25 := within_leaf (by decide +kernel)

private theorem tm125 : Within (fun i => view.timeline (view.events i)) 125 25 := within_leaf (by decide +kernel)

private theorem tm150 : Within (fun i => view.timeline (view.events i)) 150 25 := within_leaf (by decide +kernel)

private theorem tm175 : Within (fun i => view.timeline (view.events i)) 175 25 := within_leaf (by decide +kernel)

private theorem tm200 : Within (fun i => view.timeline (view.events i)) 200 25 := within_leaf (by decide +kernel)

private theorem tm225 : Within (fun i => view.timeline (view.events i)) 225 25 := within_leaf (by decide +kernel)

private theorem tm250 : Within (fun i => view.timeline (view.events i)) 250 25 := within_leaf (by decide +kernel)

private theorem tm275 : Within (fun i => view.timeline (view.events i)) 275 20 := within_leaf (by decide +kernel)

private theorem tmPart : Within (fun i => view.timeline (view.events i)) 0 295 :=
  (within_join (a:=0) (l:=150) (r:=145) (within_join (a:=0) (l:=75) (r:=75) (within_join (a:=0) (l:=25) (r:=50) tm0 (within_join (a:=25) (l:=25) (r:=25) tm25 tm50)) (within_join (a:=75) (l:=25) (r:=50) tm75 (within_join (a:=100) (l:=25) (r:=25) tm100 tm125))) (within_join (a:=150) (l:=75) (r:=70) (within_join (a:=150) (l:=25) (r:=50) tm150 (within_join (a:=175) (l:=25) (r:=25) tm175 tm200)) (within_join (a:=225) (l:=25) (r:=45) tm225 (within_join (a:=250) (l:=25) (r:=20) tm250 tm275))))

theorem solution :
    (∀ i, 0 ≤ i → i < 489 → validIdentity 23 Plain.schedule.entry (Plain.schedule.identity i) = true) ∧
    (∀ i, 0 ≤ i → i < 963 → Plain.schedule.edgeOK (Plain.schedule.edge i) = true) ∧
    (∀ i, 0 ≤ i → i < 295 → Plain.schedule.timelineOK (Plain.schedule.targets[i]?.getD []) = true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i ha hb
    simpa only [Index.checkId, view.entry_eq, view.id_eq] using indicesPart i ha (by omega)
  · intro i ha hb
    simpa only [Index.checkEdge, view.edge_eq, view.id_eq, view.basis_eq, ← view.ids.size_ok, view.hi,
      Block.edgeOK] using edPart i ha (by omega)
  · intro i ha hb
    simpa only [view.time_eq, view.events_eq] using tmPart i ha (by omega)
