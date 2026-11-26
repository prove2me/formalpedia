-- Prove2me | solution 1 for IntMul.Kappa.DeferredReadout.Staircase.certificateBatch5
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T08:53:09.404977+00:00
-- url     : https://prove2.me/submissions/e870da0c-3730-494f-beb7-3b7e0579a44a

import Definitions.Def_IntMul_Kappa_DeferredReadoutStaircase

namespace StaircaseBatch4ReadoutAccess
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

end StaircaseBatch4ReadoutAccess

open StaircaseBatch4ReadoutAccess IntMul.Kappa.DeferredReadout
set_option maxRecDepth 12000
set_option maxHeartbeats 0
private def table_rows : Table Staircase.rows 1123 := by
  unfold Staircase.rows
  exact (Table.append 572 551 (Table.append 260 312 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
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
 (Table.append 260 291 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 156 135 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 52 83 (Table.leaf 52 rfl)
 (Table.append 52 31 (Table.leaf 52 rfl)
 (Table.leaf 31 rfl))))))

private def table_bases : Table Staircase.bases 4157 := by
  unfold Staircase.bases
  exact (Table.append 2080 2077 (Table.append 1040 1040 (Table.append 520 520 (Table.append 260 260 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
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
 (Table.append 520 520 (Table.append 260 260 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
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
 (Table.leaf 52 rfl)))))))
 (Table.append 1040 1037 (Table.append 520 520 (Table.append 260 260 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
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
 (Table.append 520 517 (Table.append 260 260 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))))
 (Table.append 260 257 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 104 153 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 101 (Table.leaf 52 rfl)
 (Table.append 52 49 (Table.leaf 52 rfl)
 (Table.leaf 49 rfl))))))))

private def table_identities : Table Staircase.identities 3606 := by
  unfold Staircase.identities
  exact (Table.append 1820 1786 (Table.append 884 936 (Table.append 416 468 (Table.append 208 208 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
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
 (Table.append 468 468 (Table.append 208 260 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))))
 (Table.append 208 260 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))))))
 (Table.append 884 902 (Table.append 416 468 (Table.append 208 208 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
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
 (Table.append 468 434 (Table.append 208 260 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 156 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))))
 (Table.append 208 226 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 122 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 70 (Table.leaf 52 rfl)
 (Table.append 52 18 (Table.leaf 52 rfl)
 (Table.leaf 18 rfl))))))))

private def table_edges : Table Staircase.edges 5552 := by
  unfold Staircase.edges
  exact (Table.append 2756 2796 (Table.append 1352 1404 (Table.append 676 676 (Table.append 312 364 (Table.append 156 156 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))))
 (Table.append 312 364 (Table.append 156 156 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))))
 (Table.append 676 728 (Table.append 312 364 (Table.append 156 156 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 52 104 (Table.leaf 52 rfl)
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
 (Table.append 1404 1392 (Table.append 676 728 (Table.append 312 364 (Table.append 156 156 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 52 104 (Table.leaf 52 rfl)
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
 (Table.append 676 716 (Table.append 312 364 (Table.append 156 156 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))))
 (Table.append 364 352 (Table.append 156 208 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 104 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))))
 (Table.append 156 196 (Table.append 52 104 (Table.leaf 52 rfl)
 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl)))
 (Table.append 104 92 (Table.append 52 52 (Table.leaf 52 rfl)
 (Table.leaf 52 rfl))
 (Table.append 52 40 (Table.leaf 52 rfl)
 (Table.leaf 40 rfl))))))))

private def table_timelines : Table Staircase.timelines 1771 := by
  unfold Staircase.timelines
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

private def view : Index Staircase.schedule where
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

private theorem indices2404 : Within (view.checkId) 2404 25 := within_leaf (by decide +kernel)

private theorem indices2429 : Within (view.checkId) 2429 25 := within_leaf (by decide +kernel)

private theorem indices2454 : Within (view.checkId) 2454 25 := within_leaf (by decide +kernel)

private theorem indices2479 : Within (view.checkId) 2479 25 := within_leaf (by decide +kernel)

private theorem indices2504 : Within (view.checkId) 2504 25 := within_leaf (by decide +kernel)

private theorem indices2529 : Within (view.checkId) 2529 25 := within_leaf (by decide +kernel)

private theorem indices2554 : Within (view.checkId) 2554 25 := within_leaf (by decide +kernel)

private theorem indices2579 : Within (view.checkId) 2579 25 := within_leaf (by decide +kernel)

private theorem indices2604 : Within (view.checkId) 2604 25 := within_leaf (by decide +kernel)

private theorem indices2629 : Within (view.checkId) 2629 25 := within_leaf (by decide +kernel)

private theorem indices2654 : Within (view.checkId) 2654 25 := within_leaf (by decide +kernel)

private theorem indices2679 : Within (view.checkId) 2679 25 := within_leaf (by decide +kernel)

private theorem indices2704 : Within (view.checkId) 2704 25 := within_leaf (by decide +kernel)

private theorem indices2729 : Within (view.checkId) 2729 25 := within_leaf (by decide +kernel)

private theorem indices2754 : Within (view.checkId) 2754 25 := within_leaf (by decide +kernel)

private theorem indices2779 : Within (view.checkId) 2779 25 := within_leaf (by decide +kernel)

private theorem indices2804 : Within (view.checkId) 2804 25 := within_leaf (by decide +kernel)

private theorem indices2829 : Within (view.checkId) 2829 25 := within_leaf (by decide +kernel)

private theorem indices2854 : Within (view.checkId) 2854 25 := within_leaf (by decide +kernel)

private theorem indices2879 : Within (view.checkId) 2879 25 := within_leaf (by decide +kernel)

private theorem indices2904 : Within (view.checkId) 2904 25 := within_leaf (by decide +kernel)

private theorem indices2929 : Within (view.checkId) 2929 25 := within_leaf (by decide +kernel)

private theorem indices2954 : Within (view.checkId) 2954 25 := within_leaf (by decide +kernel)

private theorem indices2979 : Within (view.checkId) 2979 25 := within_leaf (by decide +kernel)

private theorem indices3004 : Within (view.checkId) 3004 1 := within_leaf (by decide +kernel)

private theorem indicesPart : Within (view.checkId) 2404 601 :=
  (within_join (a:=2404) (l:=300) (r:=301) (within_join (a:=2404) (l:=150) (r:=150) (within_join (a:=2404) (l:=75) (r:=75) (within_join (a:=2404) (l:=25) (r:=50) indices2404 (within_join (a:=2429) (l:=25) (r:=25) indices2429 indices2454)) (within_join (a:=2479) (l:=25) (r:=50) indices2479 (within_join (a:=2504) (l:=25) (r:=25) indices2504 indices2529))) (within_join (a:=2554) (l:=75) (r:=75) (within_join (a:=2554) (l:=25) (r:=50) indices2554 (within_join (a:=2579) (l:=25) (r:=25) indices2579 indices2604)) (within_join (a:=2629) (l:=25) (r:=50) indices2629 (within_join (a:=2654) (l:=25) (r:=25) indices2654 indices2679)))) (within_join (a:=2704) (l:=150) (r:=151) (within_join (a:=2704) (l:=75) (r:=75) (within_join (a:=2704) (l:=25) (r:=50) indices2704 (within_join (a:=2729) (l:=25) (r:=25) indices2729 indices2754)) (within_join (a:=2779) (l:=25) (r:=50) indices2779 (within_join (a:=2804) (l:=25) (r:=25) indices2804 indices2829))) (within_join (a:=2854) (l:=75) (r:=76) (within_join (a:=2854) (l:=25) (r:=50) indices2854 (within_join (a:=2879) (l:=25) (r:=25) indices2879 indices2904)) (within_join (a:=2929) (l:=50) (r:=26) (within_join (a:=2929) (l:=25) (r:=25) indices2929 indices2954) (within_join (a:=2979) (l:=25) (r:=1) indices2979 indices3004)))))

private theorem ed3701 : Within (view.checkEdge) 3701 25 := within_leaf (by decide +kernel)

private theorem ed3726 : Within (view.checkEdge) 3726 25 := within_leaf (by decide +kernel)

private theorem ed3751 : Within (view.checkEdge) 3751 25 := within_leaf (by decide +kernel)

private theorem ed3776 : Within (view.checkEdge) 3776 25 := within_leaf (by decide +kernel)

private theorem ed3801 : Within (view.checkEdge) 3801 25 := within_leaf (by decide +kernel)

private theorem ed3826 : Within (view.checkEdge) 3826 25 := within_leaf (by decide +kernel)

private theorem ed3851 : Within (view.checkEdge) 3851 25 := within_leaf (by decide +kernel)

private theorem ed3876 : Within (view.checkEdge) 3876 25 := within_leaf (by decide +kernel)

private theorem ed3901 : Within (view.checkEdge) 3901 25 := within_leaf (by decide +kernel)

private theorem ed3926 : Within (view.checkEdge) 3926 25 := within_leaf (by decide +kernel)

private theorem ed3951 : Within (view.checkEdge) 3951 25 := within_leaf (by decide +kernel)

private theorem ed3976 : Within (view.checkEdge) 3976 25 := within_leaf (by decide +kernel)

private theorem ed4001 : Within (view.checkEdge) 4001 25 := within_leaf (by decide +kernel)

private theorem ed4026 : Within (view.checkEdge) 4026 25 := within_leaf (by decide +kernel)

private theorem ed4051 : Within (view.checkEdge) 4051 25 := within_leaf (by decide +kernel)

private theorem ed4076 : Within (view.checkEdge) 4076 25 := within_leaf (by decide +kernel)

private theorem ed4101 : Within (view.checkEdge) 4101 25 := within_leaf (by decide +kernel)

private theorem ed4126 : Within (view.checkEdge) 4126 25 := within_leaf (by decide +kernel)

private theorem ed4151 : Within (view.checkEdge) 4151 25 := within_leaf (by decide +kernel)

private theorem ed4176 : Within (view.checkEdge) 4176 25 := within_leaf (by decide +kernel)

private theorem ed4201 : Within (view.checkEdge) 4201 25 := within_leaf (by decide +kernel)

private theorem ed4226 : Within (view.checkEdge) 4226 25 := within_leaf (by decide +kernel)

private theorem ed4251 : Within (view.checkEdge) 4251 25 := within_leaf (by decide +kernel)

private theorem ed4276 : Within (view.checkEdge) 4276 25 := within_leaf (by decide +kernel)

private theorem ed4301 : Within (view.checkEdge) 4301 25 := within_leaf (by decide +kernel)

private theorem ed4326 : Within (view.checkEdge) 4326 25 := within_leaf (by decide +kernel)

private theorem ed4351 : Within (view.checkEdge) 4351 25 := within_leaf (by decide +kernel)

private theorem ed4376 : Within (view.checkEdge) 4376 25 := within_leaf (by decide +kernel)

private theorem ed4401 : Within (view.checkEdge) 4401 25 := within_leaf (by decide +kernel)

private theorem ed4426 : Within (view.checkEdge) 4426 25 := within_leaf (by decide +kernel)

private theorem ed4451 : Within (view.checkEdge) 4451 25 := within_leaf (by decide +kernel)

private theorem ed4476 : Within (view.checkEdge) 4476 25 := within_leaf (by decide +kernel)

private theorem ed4501 : Within (view.checkEdge) 4501 25 := within_leaf (by decide +kernel)

private theorem ed4526 : Within (view.checkEdge) 4526 25 := within_leaf (by decide +kernel)

private theorem ed4551 : Within (view.checkEdge) 4551 25 := within_leaf (by decide +kernel)

private theorem ed4576 : Within (view.checkEdge) 4576 25 := within_leaf (by decide +kernel)

private theorem ed4601 : Within (view.checkEdge) 4601 25 := within_leaf (by decide +kernel)

private theorem edPart : Within (view.checkEdge) 3701 925 :=
  (within_join (a:=3701) (l:=450) (r:=475) (within_join (a:=3701) (l:=225) (r:=225) (within_join (a:=3701) (l:=100) (r:=125) (within_join (a:=3701) (l:=50) (r:=50) (within_join (a:=3701) (l:=25) (r:=25) ed3701 ed3726) (within_join (a:=3751) (l:=25) (r:=25) ed3751 ed3776)) (within_join (a:=3801) (l:=50) (r:=75) (within_join (a:=3801) (l:=25) (r:=25) ed3801 ed3826) (within_join (a:=3851) (l:=25) (r:=50) ed3851 (within_join (a:=3876) (l:=25) (r:=25) ed3876 ed3901)))) (within_join (a:=3926) (l:=100) (r:=125) (within_join (a:=3926) (l:=50) (r:=50) (within_join (a:=3926) (l:=25) (r:=25) ed3926 ed3951) (within_join (a:=3976) (l:=25) (r:=25) ed3976 ed4001)) (within_join (a:=4026) (l:=50) (r:=75) (within_join (a:=4026) (l:=25) (r:=25) ed4026 ed4051) (within_join (a:=4076) (l:=25) (r:=50) ed4076 (within_join (a:=4101) (l:=25) (r:=25) ed4101 ed4126))))) (within_join (a:=4151) (l:=225) (r:=250) (within_join (a:=4151) (l:=100) (r:=125) (within_join (a:=4151) (l:=50) (r:=50) (within_join (a:=4151) (l:=25) (r:=25) ed4151 ed4176) (within_join (a:=4201) (l:=25) (r:=25) ed4201 ed4226)) (within_join (a:=4251) (l:=50) (r:=75) (within_join (a:=4251) (l:=25) (r:=25) ed4251 ed4276) (within_join (a:=4301) (l:=25) (r:=50) ed4301 (within_join (a:=4326) (l:=25) (r:=25) ed4326 ed4351)))) (within_join (a:=4376) (l:=125) (r:=125) (within_join (a:=4376) (l:=50) (r:=75) (within_join (a:=4376) (l:=25) (r:=25) ed4376 ed4401) (within_join (a:=4426) (l:=25) (r:=50) ed4426 (within_join (a:=4451) (l:=25) (r:=25) ed4451 ed4476))) (within_join (a:=4501) (l:=50) (r:=75) (within_join (a:=4501) (l:=25) (r:=25) ed4501 ed4526) (within_join (a:=4551) (l:=25) (r:=50) ed4551 (within_join (a:=4576) (l:=25) (r:=25) ed4576 ed4601))))))

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
    (∀ i, 2404 ≤ i → i < 3005 → validIdentity 23 Staircase.schedule.entry (Staircase.schedule.identity i) = true) ∧
    (∀ i, 3701 ≤ i → i < 4626 → Staircase.schedule.edgeOK (Staircase.schedule.edge i) = true) ∧
    (∀ i, 1180 ≤ i → i < 1475 → Staircase.schedule.timelineOK (Staircase.schedule.targets[i]?.getD []) = true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i ha hb
    simpa only [Index.checkId, view.entry_eq, view.id_eq] using indicesPart i ha (by omega)
  · intro i ha hb
    simpa only [Index.checkEdge, view.edge_eq, view.id_eq, view.basis_eq, ← view.ids.size_ok, view.hi,
      Block.edgeOK] using edPart i ha (by omega)
  · intro i ha hb
    simpa only [view.time_eq, view.events_eq] using tmPart i ha (by omega)
