-- Prove2me | solution 1 for IntMul.Kappa.DeferredReadout.Plain.certificateBatch5
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T08:53:07.483975+00:00
-- url     : https://prove2.me/submissions/677b2b0c-aa9e-471b-87f1-f2b25e57e6fa

import Definitions.Def_IntMul_Kappa_DeferredReadoutPlain

namespace PlainBatch4ReadoutAccess
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

end PlainBatch4ReadoutAccess

open PlainBatch4ReadoutAccess IntMul.Kappa.DeferredReadout
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

private theorem indices1958 : Within (view.checkId) 1958 25 := within_leaf (by decide +kernel)

private theorem indices1983 : Within (view.checkId) 1983 25 := within_leaf (by decide +kernel)

private theorem indices2008 : Within (view.checkId) 2008 25 := within_leaf (by decide +kernel)

private theorem indices2033 : Within (view.checkId) 2033 25 := within_leaf (by decide +kernel)

private theorem indices2058 : Within (view.checkId) 2058 25 := within_leaf (by decide +kernel)

private theorem indices2083 : Within (view.checkId) 2083 25 := within_leaf (by decide +kernel)

private theorem indices2108 : Within (view.checkId) 2108 25 := within_leaf (by decide +kernel)

private theorem indices2133 : Within (view.checkId) 2133 25 := within_leaf (by decide +kernel)

private theorem indices2158 : Within (view.checkId) 2158 25 := within_leaf (by decide +kernel)

private theorem indices2183 : Within (view.checkId) 2183 25 := within_leaf (by decide +kernel)

private theorem indices2208 : Within (view.checkId) 2208 25 := within_leaf (by decide +kernel)

private theorem indices2233 : Within (view.checkId) 2233 25 := within_leaf (by decide +kernel)

private theorem indices2258 : Within (view.checkId) 2258 25 := within_leaf (by decide +kernel)

private theorem indices2283 : Within (view.checkId) 2283 25 := within_leaf (by decide +kernel)

private theorem indices2308 : Within (view.checkId) 2308 25 := within_leaf (by decide +kernel)

private theorem indices2333 : Within (view.checkId) 2333 25 := within_leaf (by decide +kernel)

private theorem indices2358 : Within (view.checkId) 2358 25 := within_leaf (by decide +kernel)

private theorem indices2383 : Within (view.checkId) 2383 25 := within_leaf (by decide +kernel)

private theorem indices2408 : Within (view.checkId) 2408 25 := within_leaf (by decide +kernel)

private theorem indices2433 : Within (view.checkId) 2433 14 := within_leaf (by decide +kernel)

private theorem indicesPart : Within (view.checkId) 1958 489 :=
  (within_join (a:=1958) (l:=250) (r:=239) (within_join (a:=1958) (l:=125) (r:=125) (within_join (a:=1958) (l:=50) (r:=75) (within_join (a:=1958) (l:=25) (r:=25) indices1958 indices1983) (within_join (a:=2008) (l:=25) (r:=50) indices2008 (within_join (a:=2033) (l:=25) (r:=25) indices2033 indices2058))) (within_join (a:=2083) (l:=50) (r:=75) (within_join (a:=2083) (l:=25) (r:=25) indices2083 indices2108) (within_join (a:=2133) (l:=25) (r:=50) indices2133 (within_join (a:=2158) (l:=25) (r:=25) indices2158 indices2183)))) (within_join (a:=2208) (l:=125) (r:=114) (within_join (a:=2208) (l:=50) (r:=75) (within_join (a:=2208) (l:=25) (r:=25) indices2208 indices2233) (within_join (a:=2258) (l:=25) (r:=50) indices2258 (within_join (a:=2283) (l:=25) (r:=25) indices2283 indices2308))) (within_join (a:=2333) (l:=50) (r:=64) (within_join (a:=2333) (l:=25) (r:=25) indices2333 indices2358) (within_join (a:=2383) (l:=25) (r:=39) indices2383 (within_join (a:=2408) (l:=25) (r:=14) indices2408 indices2433)))))

private theorem ed3854 : Within (view.checkEdge) 3854 25 := within_leaf (by decide +kernel)

private theorem ed3879 : Within (view.checkEdge) 3879 25 := within_leaf (by decide +kernel)

private theorem ed3904 : Within (view.checkEdge) 3904 25 := within_leaf (by decide +kernel)

private theorem ed3929 : Within (view.checkEdge) 3929 25 := within_leaf (by decide +kernel)

private theorem ed3954 : Within (view.checkEdge) 3954 25 := within_leaf (by decide +kernel)

private theorem ed3979 : Within (view.checkEdge) 3979 25 := within_leaf (by decide +kernel)

private theorem ed4004 : Within (view.checkEdge) 4004 25 := within_leaf (by decide +kernel)

private theorem ed4029 : Within (view.checkEdge) 4029 25 := within_leaf (by decide +kernel)

private theorem ed4054 : Within (view.checkEdge) 4054 25 := within_leaf (by decide +kernel)

private theorem ed4079 : Within (view.checkEdge) 4079 25 := within_leaf (by decide +kernel)

private theorem ed4104 : Within (view.checkEdge) 4104 25 := within_leaf (by decide +kernel)

private theorem ed4129 : Within (view.checkEdge) 4129 25 := within_leaf (by decide +kernel)

private theorem ed4154 : Within (view.checkEdge) 4154 25 := within_leaf (by decide +kernel)

private theorem ed4179 : Within (view.checkEdge) 4179 25 := within_leaf (by decide +kernel)

private theorem ed4204 : Within (view.checkEdge) 4204 25 := within_leaf (by decide +kernel)

private theorem ed4229 : Within (view.checkEdge) 4229 25 := within_leaf (by decide +kernel)

private theorem ed4254 : Within (view.checkEdge) 4254 25 := within_leaf (by decide +kernel)

private theorem ed4279 : Within (view.checkEdge) 4279 25 := within_leaf (by decide +kernel)

private theorem ed4304 : Within (view.checkEdge) 4304 25 := within_leaf (by decide +kernel)

private theorem ed4329 : Within (view.checkEdge) 4329 25 := within_leaf (by decide +kernel)

private theorem ed4354 : Within (view.checkEdge) 4354 25 := within_leaf (by decide +kernel)

private theorem ed4379 : Within (view.checkEdge) 4379 25 := within_leaf (by decide +kernel)

private theorem ed4404 : Within (view.checkEdge) 4404 25 := within_leaf (by decide +kernel)

private theorem ed4429 : Within (view.checkEdge) 4429 25 := within_leaf (by decide +kernel)

private theorem ed4454 : Within (view.checkEdge) 4454 25 := within_leaf (by decide +kernel)

private theorem ed4479 : Within (view.checkEdge) 4479 25 := within_leaf (by decide +kernel)

private theorem ed4504 : Within (view.checkEdge) 4504 25 := within_leaf (by decide +kernel)

private theorem ed4529 : Within (view.checkEdge) 4529 25 := within_leaf (by decide +kernel)

private theorem ed4554 : Within (view.checkEdge) 4554 25 := within_leaf (by decide +kernel)

private theorem ed4579 : Within (view.checkEdge) 4579 25 := within_leaf (by decide +kernel)

private theorem ed4604 : Within (view.checkEdge) 4604 25 := within_leaf (by decide +kernel)

private theorem ed4629 : Within (view.checkEdge) 4629 25 := within_leaf (by decide +kernel)

private theorem ed4654 : Within (view.checkEdge) 4654 25 := within_leaf (by decide +kernel)

private theorem ed4679 : Within (view.checkEdge) 4679 25 := within_leaf (by decide +kernel)

private theorem ed4704 : Within (view.checkEdge) 4704 25 := within_leaf (by decide +kernel)

private theorem ed4729 : Within (view.checkEdge) 4729 25 := within_leaf (by decide +kernel)

private theorem ed4754 : Within (view.checkEdge) 4754 25 := within_leaf (by decide +kernel)

private theorem ed4779 : Within (view.checkEdge) 4779 25 := within_leaf (by decide +kernel)

private theorem ed4804 : Within (view.checkEdge) 4804 13 := within_leaf (by decide +kernel)

private theorem edPart : Within (view.checkEdge) 3854 963 :=
  (within_join (a:=3854) (l:=475) (r:=488) (within_join (a:=3854) (l:=225) (r:=250) (within_join (a:=3854) (l:=100) (r:=125) (within_join (a:=3854) (l:=50) (r:=50) (within_join (a:=3854) (l:=25) (r:=25) ed3854 ed3879) (within_join (a:=3904) (l:=25) (r:=25) ed3904 ed3929)) (within_join (a:=3954) (l:=50) (r:=75) (within_join (a:=3954) (l:=25) (r:=25) ed3954 ed3979) (within_join (a:=4004) (l:=25) (r:=50) ed4004 (within_join (a:=4029) (l:=25) (r:=25) ed4029 ed4054)))) (within_join (a:=4079) (l:=125) (r:=125) (within_join (a:=4079) (l:=50) (r:=75) (within_join (a:=4079) (l:=25) (r:=25) ed4079 ed4104) (within_join (a:=4129) (l:=25) (r:=50) ed4129 (within_join (a:=4154) (l:=25) (r:=25) ed4154 ed4179))) (within_join (a:=4204) (l:=50) (r:=75) (within_join (a:=4204) (l:=25) (r:=25) ed4204 ed4229) (within_join (a:=4254) (l:=25) (r:=50) ed4254 (within_join (a:=4279) (l:=25) (r:=25) ed4279 ed4304))))) (within_join (a:=4329) (l:=250) (r:=238) (within_join (a:=4329) (l:=125) (r:=125) (within_join (a:=4329) (l:=50) (r:=75) (within_join (a:=4329) (l:=25) (r:=25) ed4329 ed4354) (within_join (a:=4379) (l:=25) (r:=50) ed4379 (within_join (a:=4404) (l:=25) (r:=25) ed4404 ed4429))) (within_join (a:=4454) (l:=50) (r:=75) (within_join (a:=4454) (l:=25) (r:=25) ed4454 ed4479) (within_join (a:=4504) (l:=25) (r:=50) ed4504 (within_join (a:=4529) (l:=25) (r:=25) ed4529 ed4554)))) (within_join (a:=4579) (l:=125) (r:=113) (within_join (a:=4579) (l:=50) (r:=75) (within_join (a:=4579) (l:=25) (r:=25) ed4579 ed4604) (within_join (a:=4629) (l:=25) (r:=50) ed4629 (within_join (a:=4654) (l:=25) (r:=25) ed4654 ed4679))) (within_join (a:=4704) (l:=50) (r:=63) (within_join (a:=4704) (l:=25) (r:=25) ed4704 ed4729) (within_join (a:=4754) (l:=25) (r:=38) ed4754 (within_join (a:=4779) (l:=25) (r:=13) ed4779 ed4804))))))

private theorem tm1180 : Within (fun i => view.timeline (view.events i)) 1180 25 := within_leaf (by decide +kernel)

private theorem tm1205 : Within (fun i => view.timeline (view.events i)) 1205 25 := within_leaf (by decide +kernel)

private theorem tm1230 : Within (fun i => view.timeline (view.events i)) 1230 25 := within_leaf (by decide +kernel)

private theorem tm1255 : Within (fun i => view.timeline (view.events i)) 1255 25 := within_leaf (by decide +kernel)

private theorem tm1280 : Within (fun i => view.timeline (view.events i)) 1280 25 := within_leaf (by decide +kernel)

private theorem tm1305 : Within (fun i => view.timeline (view.events i)) 1305 25 := within_leaf (by decide +kernel)

private theorem tm1330 : Within (fun i => view.timeline (view.events i)) 1330 25 := within_leaf (by decide +kernel)

private theorem tm1355 : Within (fun i => view.timeline (view.events i)) 1355 25 := within_leaf (by decide +kernel)

private theorem tm1380 : Within (fun i => view.timeline (view.events i)) 1380 25 := within_leaf (by decide +kernel)

private theorem tm1405 : Within (fun i => view.timeline (view.events i)) 1405 25 := within_leaf (by decide +kernel)

private theorem tm1430 : Within (fun i => view.timeline (view.events i)) 1430 25 := within_leaf (by decide +kernel)

private theorem tm1455 : Within (fun i => view.timeline (view.events i)) 1455 20 := within_leaf (by decide +kernel)

private theorem tmPart : Within (fun i => view.timeline (view.events i)) 1180 295 :=
  (within_join (a:=1180) (l:=150) (r:=145) (within_join (a:=1180) (l:=75) (r:=75) (within_join (a:=1180) (l:=25) (r:=50) tm1180 (within_join (a:=1205) (l:=25) (r:=25) tm1205 tm1230)) (within_join (a:=1255) (l:=25) (r:=50) tm1255 (within_join (a:=1280) (l:=25) (r:=25) tm1280 tm1305))) (within_join (a:=1330) (l:=75) (r:=70) (within_join (a:=1330) (l:=25) (r:=50) tm1330 (within_join (a:=1355) (l:=25) (r:=25) tm1355 tm1380)) (within_join (a:=1405) (l:=25) (r:=45) tm1405 (within_join (a:=1430) (l:=25) (r:=20) tm1430 tm1455))))

theorem solution :
    (∀ i, 1958 ≤ i → i < 2447 → validIdentity 23 Plain.schedule.entry (Plain.schedule.identity i) = true) ∧
    (∀ i, 3854 ≤ i → i < 4817 → Plain.schedule.edgeOK (Plain.schedule.edge i) = true) ∧
    (∀ i, 1180 ≤ i → i < 1475 → Plain.schedule.timelineOK (Plain.schedule.targets[i]?.getD []) = true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i ha hb
    simpa only [Index.checkId, view.entry_eq, view.id_eq] using indicesPart i ha (by omega)
  · intro i ha hb
    simpa only [Index.checkEdge, view.edge_eq, view.id_eq, view.basis_eq, ← view.ids.size_ok, view.hi,
      Block.edgeOK] using edPart i ha (by omega)
  · intro i ha hb
    simpa only [view.time_eq, view.events_eq] using tmPart i ha (by omega)
