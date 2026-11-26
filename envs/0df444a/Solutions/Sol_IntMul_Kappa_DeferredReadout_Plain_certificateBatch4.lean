-- Prove2me | solution 1 for IntMul.Kappa.DeferredReadout.Plain.certificateBatch4
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T08:53:03.337107+00:00
-- url     : https://prove2.me/submissions/430977ff-f243-48ed-932c-cafc3f7412d5

import Definitions.Def_IntMul_Kappa_DeferredReadoutPlain

namespace PlainBatch3ReadoutAccess
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

end PlainBatch3ReadoutAccess

open PlainBatch3ReadoutAccess IntMul.Kappa.DeferredReadout
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

private theorem indices1468 : Within (view.checkId) 1468 25 := within_leaf (by decide +kernel)

private theorem indices1493 : Within (view.checkId) 1493 25 := within_leaf (by decide +kernel)

private theorem indices1518 : Within (view.checkId) 1518 25 := within_leaf (by decide +kernel)

private theorem indices1543 : Within (view.checkId) 1543 25 := within_leaf (by decide +kernel)

private theorem indices1568 : Within (view.checkId) 1568 25 := within_leaf (by decide +kernel)

private theorem indices1593 : Within (view.checkId) 1593 25 := within_leaf (by decide +kernel)

private theorem indices1618 : Within (view.checkId) 1618 25 := within_leaf (by decide +kernel)

private theorem indices1643 : Within (view.checkId) 1643 25 := within_leaf (by decide +kernel)

private theorem indices1668 : Within (view.checkId) 1668 25 := within_leaf (by decide +kernel)

private theorem indices1693 : Within (view.checkId) 1693 25 := within_leaf (by decide +kernel)

private theorem indices1718 : Within (view.checkId) 1718 25 := within_leaf (by decide +kernel)

private theorem indices1743 : Within (view.checkId) 1743 25 := within_leaf (by decide +kernel)

private theorem indices1768 : Within (view.checkId) 1768 25 := within_leaf (by decide +kernel)

private theorem indices1793 : Within (view.checkId) 1793 25 := within_leaf (by decide +kernel)

private theorem indices1818 : Within (view.checkId) 1818 25 := within_leaf (by decide +kernel)

private theorem indices1843 : Within (view.checkId) 1843 25 := within_leaf (by decide +kernel)

private theorem indices1868 : Within (view.checkId) 1868 25 := within_leaf (by decide +kernel)

private theorem indices1893 : Within (view.checkId) 1893 25 := within_leaf (by decide +kernel)

private theorem indices1918 : Within (view.checkId) 1918 25 := within_leaf (by decide +kernel)

private theorem indices1943 : Within (view.checkId) 1943 15 := within_leaf (by decide +kernel)

private theorem indicesPart : Within (view.checkId) 1468 490 :=
  (within_join (a:=1468) (l:=250) (r:=240) (within_join (a:=1468) (l:=125) (r:=125) (within_join (a:=1468) (l:=50) (r:=75) (within_join (a:=1468) (l:=25) (r:=25) indices1468 indices1493) (within_join (a:=1518) (l:=25) (r:=50) indices1518 (within_join (a:=1543) (l:=25) (r:=25) indices1543 indices1568))) (within_join (a:=1593) (l:=50) (r:=75) (within_join (a:=1593) (l:=25) (r:=25) indices1593 indices1618) (within_join (a:=1643) (l:=25) (r:=50) indices1643 (within_join (a:=1668) (l:=25) (r:=25) indices1668 indices1693)))) (within_join (a:=1718) (l:=125) (r:=115) (within_join (a:=1718) (l:=50) (r:=75) (within_join (a:=1718) (l:=25) (r:=25) indices1718 indices1743) (within_join (a:=1768) (l:=25) (r:=50) indices1768 (within_join (a:=1793) (l:=25) (r:=25) indices1793 indices1818))) (within_join (a:=1843) (l:=50) (r:=65) (within_join (a:=1843) (l:=25) (r:=25) indices1843 indices1868) (within_join (a:=1893) (l:=25) (r:=40) indices1893 (within_join (a:=1918) (l:=25) (r:=15) indices1918 indices1943)))))

private theorem ed2890 : Within (view.checkEdge) 2890 25 := within_leaf (by decide +kernel)

private theorem ed2915 : Within (view.checkEdge) 2915 25 := within_leaf (by decide +kernel)

private theorem ed2940 : Within (view.checkEdge) 2940 25 := within_leaf (by decide +kernel)

private theorem ed2965 : Within (view.checkEdge) 2965 25 := within_leaf (by decide +kernel)

private theorem ed2990 : Within (view.checkEdge) 2990 25 := within_leaf (by decide +kernel)

private theorem ed3015 : Within (view.checkEdge) 3015 25 := within_leaf (by decide +kernel)

private theorem ed3040 : Within (view.checkEdge) 3040 25 := within_leaf (by decide +kernel)

private theorem ed3065 : Within (view.checkEdge) 3065 25 := within_leaf (by decide +kernel)

private theorem ed3090 : Within (view.checkEdge) 3090 25 := within_leaf (by decide +kernel)

private theorem ed3115 : Within (view.checkEdge) 3115 25 := within_leaf (by decide +kernel)

private theorem ed3140 : Within (view.checkEdge) 3140 25 := within_leaf (by decide +kernel)

private theorem ed3165 : Within (view.checkEdge) 3165 25 := within_leaf (by decide +kernel)

private theorem ed3190 : Within (view.checkEdge) 3190 25 := within_leaf (by decide +kernel)

private theorem ed3215 : Within (view.checkEdge) 3215 25 := within_leaf (by decide +kernel)

private theorem ed3240 : Within (view.checkEdge) 3240 25 := within_leaf (by decide +kernel)

private theorem ed3265 : Within (view.checkEdge) 3265 25 := within_leaf (by decide +kernel)

private theorem ed3290 : Within (view.checkEdge) 3290 25 := within_leaf (by decide +kernel)

private theorem ed3315 : Within (view.checkEdge) 3315 25 := within_leaf (by decide +kernel)

private theorem ed3340 : Within (view.checkEdge) 3340 25 := within_leaf (by decide +kernel)

private theorem ed3365 : Within (view.checkEdge) 3365 25 := within_leaf (by decide +kernel)

private theorem ed3390 : Within (view.checkEdge) 3390 25 := within_leaf (by decide +kernel)

private theorem ed3415 : Within (view.checkEdge) 3415 25 := within_leaf (by decide +kernel)

private theorem ed3440 : Within (view.checkEdge) 3440 25 := within_leaf (by decide +kernel)

private theorem ed3465 : Within (view.checkEdge) 3465 25 := within_leaf (by decide +kernel)

private theorem ed3490 : Within (view.checkEdge) 3490 25 := within_leaf (by decide +kernel)

private theorem ed3515 : Within (view.checkEdge) 3515 25 := within_leaf (by decide +kernel)

private theorem ed3540 : Within (view.checkEdge) 3540 25 := within_leaf (by decide +kernel)

private theorem ed3565 : Within (view.checkEdge) 3565 25 := within_leaf (by decide +kernel)

private theorem ed3590 : Within (view.checkEdge) 3590 25 := within_leaf (by decide +kernel)

private theorem ed3615 : Within (view.checkEdge) 3615 25 := within_leaf (by decide +kernel)

private theorem ed3640 : Within (view.checkEdge) 3640 25 := within_leaf (by decide +kernel)

private theorem ed3665 : Within (view.checkEdge) 3665 25 := within_leaf (by decide +kernel)

private theorem ed3690 : Within (view.checkEdge) 3690 25 := within_leaf (by decide +kernel)

private theorem ed3715 : Within (view.checkEdge) 3715 25 := within_leaf (by decide +kernel)

private theorem ed3740 : Within (view.checkEdge) 3740 25 := within_leaf (by decide +kernel)

private theorem ed3765 : Within (view.checkEdge) 3765 25 := within_leaf (by decide +kernel)

private theorem ed3790 : Within (view.checkEdge) 3790 25 := within_leaf (by decide +kernel)

private theorem ed3815 : Within (view.checkEdge) 3815 25 := within_leaf (by decide +kernel)

private theorem ed3840 : Within (view.checkEdge) 3840 14 := within_leaf (by decide +kernel)

private theorem edPart : Within (view.checkEdge) 2890 964 :=
  (within_join (a:=2890) (l:=475) (r:=489) (within_join (a:=2890) (l:=225) (r:=250) (within_join (a:=2890) (l:=100) (r:=125) (within_join (a:=2890) (l:=50) (r:=50) (within_join (a:=2890) (l:=25) (r:=25) ed2890 ed2915) (within_join (a:=2940) (l:=25) (r:=25) ed2940 ed2965)) (within_join (a:=2990) (l:=50) (r:=75) (within_join (a:=2990) (l:=25) (r:=25) ed2990 ed3015) (within_join (a:=3040) (l:=25) (r:=50) ed3040 (within_join (a:=3065) (l:=25) (r:=25) ed3065 ed3090)))) (within_join (a:=3115) (l:=125) (r:=125) (within_join (a:=3115) (l:=50) (r:=75) (within_join (a:=3115) (l:=25) (r:=25) ed3115 ed3140) (within_join (a:=3165) (l:=25) (r:=50) ed3165 (within_join (a:=3190) (l:=25) (r:=25) ed3190 ed3215))) (within_join (a:=3240) (l:=50) (r:=75) (within_join (a:=3240) (l:=25) (r:=25) ed3240 ed3265) (within_join (a:=3290) (l:=25) (r:=50) ed3290 (within_join (a:=3315) (l:=25) (r:=25) ed3315 ed3340))))) (within_join (a:=3365) (l:=250) (r:=239) (within_join (a:=3365) (l:=125) (r:=125) (within_join (a:=3365) (l:=50) (r:=75) (within_join (a:=3365) (l:=25) (r:=25) ed3365 ed3390) (within_join (a:=3415) (l:=25) (r:=50) ed3415 (within_join (a:=3440) (l:=25) (r:=25) ed3440 ed3465))) (within_join (a:=3490) (l:=50) (r:=75) (within_join (a:=3490) (l:=25) (r:=25) ed3490 ed3515) (within_join (a:=3540) (l:=25) (r:=50) ed3540 (within_join (a:=3565) (l:=25) (r:=25) ed3565 ed3590)))) (within_join (a:=3615) (l:=125) (r:=114) (within_join (a:=3615) (l:=50) (r:=75) (within_join (a:=3615) (l:=25) (r:=25) ed3615 ed3640) (within_join (a:=3665) (l:=25) (r:=50) ed3665 (within_join (a:=3690) (l:=25) (r:=25) ed3690 ed3715))) (within_join (a:=3740) (l:=50) (r:=64) (within_join (a:=3740) (l:=25) (r:=25) ed3740 ed3765) (within_join (a:=3790) (l:=25) (r:=39) ed3790 (within_join (a:=3815) (l:=25) (r:=14) ed3815 ed3840))))))

private theorem tm885 : Within (fun i => view.timeline (view.events i)) 885 25 := within_leaf (by decide +kernel)

private theorem tm910 : Within (fun i => view.timeline (view.events i)) 910 25 := within_leaf (by decide +kernel)

private theorem tm935 : Within (fun i => view.timeline (view.events i)) 935 25 := within_leaf (by decide +kernel)

private theorem tm960 : Within (fun i => view.timeline (view.events i)) 960 25 := within_leaf (by decide +kernel)

private theorem tm985 : Within (fun i => view.timeline (view.events i)) 985 25 := within_leaf (by decide +kernel)

private theorem tm1010 : Within (fun i => view.timeline (view.events i)) 1010 25 := within_leaf (by decide +kernel)

private theorem tm1035 : Within (fun i => view.timeline (view.events i)) 1035 25 := within_leaf (by decide +kernel)

private theorem tm1060 : Within (fun i => view.timeline (view.events i)) 1060 25 := within_leaf (by decide +kernel)

private theorem tm1085 : Within (fun i => view.timeline (view.events i)) 1085 25 := within_leaf (by decide +kernel)

private theorem tm1110 : Within (fun i => view.timeline (view.events i)) 1110 25 := within_leaf (by decide +kernel)

private theorem tm1135 : Within (fun i => view.timeline (view.events i)) 1135 25 := within_leaf (by decide +kernel)

private theorem tm1160 : Within (fun i => view.timeline (view.events i)) 1160 20 := within_leaf (by decide +kernel)

private theorem tmPart : Within (fun i => view.timeline (view.events i)) 885 295 :=
  (within_join (a:=885) (l:=150) (r:=145) (within_join (a:=885) (l:=75) (r:=75) (within_join (a:=885) (l:=25) (r:=50) tm885 (within_join (a:=910) (l:=25) (r:=25) tm910 tm935)) (within_join (a:=960) (l:=25) (r:=50) tm960 (within_join (a:=985) (l:=25) (r:=25) tm985 tm1010))) (within_join (a:=1035) (l:=75) (r:=70) (within_join (a:=1035) (l:=25) (r:=50) tm1035 (within_join (a:=1060) (l:=25) (r:=25) tm1060 tm1085)) (within_join (a:=1110) (l:=25) (r:=45) tm1110 (within_join (a:=1135) (l:=25) (r:=20) tm1135 tm1160))))

theorem solution :
    (∀ i, 1468 ≤ i → i < 1958 → validIdentity 23 Plain.schedule.entry (Plain.schedule.identity i) = true) ∧
    (∀ i, 2890 ≤ i → i < 3854 → Plain.schedule.edgeOK (Plain.schedule.edge i) = true) ∧
    (∀ i, 885 ≤ i → i < 1180 → Plain.schedule.timelineOK (Plain.schedule.targets[i]?.getD []) = true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i ha hb
    simpa only [Index.checkId, view.entry_eq, view.id_eq] using indicesPart i ha (by omega)
  · intro i ha hb
    simpa only [Index.checkEdge, view.edge_eq, view.id_eq, view.basis_eq, ← view.ids.size_ok, view.hi,
      Block.edgeOK] using edPart i ha (by omega)
  · intro i ha hb
    simpa only [view.time_eq, view.events_eq] using tmPart i ha (by omega)
