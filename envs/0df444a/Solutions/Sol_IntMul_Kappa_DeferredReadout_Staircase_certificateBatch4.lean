-- Prove2me | solution 1 for IntMul.Kappa.DeferredReadout.Staircase.certificateBatch4
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T08:53:05.616418+00:00
-- url     : https://prove2.me/submissions/3db166a8-1c52-47f5-b5e1-9b98f9d943cd

import Definitions.Def_IntMul_Kappa_DeferredReadoutStaircase

namespace StaircaseBatch3ReadoutAccess
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

end StaircaseBatch3ReadoutAccess

open StaircaseBatch3ReadoutAccess IntMul.Kappa.DeferredReadout
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

private theorem indices1803 : Within (view.checkId) 1803 25 := within_leaf (by decide +kernel)

private theorem indices1828 : Within (view.checkId) 1828 25 := within_leaf (by decide +kernel)

private theorem indices1853 : Within (view.checkId) 1853 25 := within_leaf (by decide +kernel)

private theorem indices1878 : Within (view.checkId) 1878 25 := within_leaf (by decide +kernel)

private theorem indices1903 : Within (view.checkId) 1903 25 := within_leaf (by decide +kernel)

private theorem indices1928 : Within (view.checkId) 1928 25 := within_leaf (by decide +kernel)

private theorem indices1953 : Within (view.checkId) 1953 25 := within_leaf (by decide +kernel)

private theorem indices1978 : Within (view.checkId) 1978 25 := within_leaf (by decide +kernel)

private theorem indices2003 : Within (view.checkId) 2003 25 := within_leaf (by decide +kernel)

private theorem indices2028 : Within (view.checkId) 2028 25 := within_leaf (by decide +kernel)

private theorem indices2053 : Within (view.checkId) 2053 25 := within_leaf (by decide +kernel)

private theorem indices2078 : Within (view.checkId) 2078 25 := within_leaf (by decide +kernel)

private theorem indices2103 : Within (view.checkId) 2103 25 := within_leaf (by decide +kernel)

private theorem indices2128 : Within (view.checkId) 2128 25 := within_leaf (by decide +kernel)

private theorem indices2153 : Within (view.checkId) 2153 25 := within_leaf (by decide +kernel)

private theorem indices2178 : Within (view.checkId) 2178 25 := within_leaf (by decide +kernel)

private theorem indices2203 : Within (view.checkId) 2203 25 := within_leaf (by decide +kernel)

private theorem indices2228 : Within (view.checkId) 2228 25 := within_leaf (by decide +kernel)

private theorem indices2253 : Within (view.checkId) 2253 25 := within_leaf (by decide +kernel)

private theorem indices2278 : Within (view.checkId) 2278 25 := within_leaf (by decide +kernel)

private theorem indices2303 : Within (view.checkId) 2303 25 := within_leaf (by decide +kernel)

private theorem indices2328 : Within (view.checkId) 2328 25 := within_leaf (by decide +kernel)

private theorem indices2353 : Within (view.checkId) 2353 25 := within_leaf (by decide +kernel)

private theorem indices2378 : Within (view.checkId) 2378 25 := within_leaf (by decide +kernel)

private theorem indices2403 : Within (view.checkId) 2403 1 := within_leaf (by decide +kernel)

private theorem indicesPart : Within (view.checkId) 1803 601 :=
  (within_join (a:=1803) (l:=300) (r:=301) (within_join (a:=1803) (l:=150) (r:=150) (within_join (a:=1803) (l:=75) (r:=75) (within_join (a:=1803) (l:=25) (r:=50) indices1803 (within_join (a:=1828) (l:=25) (r:=25) indices1828 indices1853)) (within_join (a:=1878) (l:=25) (r:=50) indices1878 (within_join (a:=1903) (l:=25) (r:=25) indices1903 indices1928))) (within_join (a:=1953) (l:=75) (r:=75) (within_join (a:=1953) (l:=25) (r:=50) indices1953 (within_join (a:=1978) (l:=25) (r:=25) indices1978 indices2003)) (within_join (a:=2028) (l:=25) (r:=50) indices2028 (within_join (a:=2053) (l:=25) (r:=25) indices2053 indices2078)))) (within_join (a:=2103) (l:=150) (r:=151) (within_join (a:=2103) (l:=75) (r:=75) (within_join (a:=2103) (l:=25) (r:=50) indices2103 (within_join (a:=2128) (l:=25) (r:=25) indices2128 indices2153)) (within_join (a:=2178) (l:=25) (r:=50) indices2178 (within_join (a:=2203) (l:=25) (r:=25) indices2203 indices2228))) (within_join (a:=2253) (l:=75) (r:=76) (within_join (a:=2253) (l:=25) (r:=50) indices2253 (within_join (a:=2278) (l:=25) (r:=25) indices2278 indices2303)) (within_join (a:=2328) (l:=50) (r:=26) (within_join (a:=2328) (l:=25) (r:=25) indices2328 indices2353) (within_join (a:=2378) (l:=25) (r:=1) indices2378 indices2403)))))

private theorem ed2776 : Within (view.checkEdge) 2776 25 := within_leaf (by decide +kernel)

private theorem ed2801 : Within (view.checkEdge) 2801 25 := within_leaf (by decide +kernel)

private theorem ed2826 : Within (view.checkEdge) 2826 25 := within_leaf (by decide +kernel)

private theorem ed2851 : Within (view.checkEdge) 2851 25 := within_leaf (by decide +kernel)

private theorem ed2876 : Within (view.checkEdge) 2876 25 := within_leaf (by decide +kernel)

private theorem ed2901 : Within (view.checkEdge) 2901 25 := within_leaf (by decide +kernel)

private theorem ed2926 : Within (view.checkEdge) 2926 25 := within_leaf (by decide +kernel)

private theorem ed2951 : Within (view.checkEdge) 2951 25 := within_leaf (by decide +kernel)

private theorem ed2976 : Within (view.checkEdge) 2976 25 := within_leaf (by decide +kernel)

private theorem ed3001 : Within (view.checkEdge) 3001 25 := within_leaf (by decide +kernel)

private theorem ed3026 : Within (view.checkEdge) 3026 25 := within_leaf (by decide +kernel)

private theorem ed3051 : Within (view.checkEdge) 3051 25 := within_leaf (by decide +kernel)

private theorem ed3076 : Within (view.checkEdge) 3076 25 := within_leaf (by decide +kernel)

private theorem ed3101 : Within (view.checkEdge) 3101 25 := within_leaf (by decide +kernel)

private theorem ed3126 : Within (view.checkEdge) 3126 25 := within_leaf (by decide +kernel)

private theorem ed3151 : Within (view.checkEdge) 3151 25 := within_leaf (by decide +kernel)

private theorem ed3176 : Within (view.checkEdge) 3176 25 := within_leaf (by decide +kernel)

private theorem ed3201 : Within (view.checkEdge) 3201 25 := within_leaf (by decide +kernel)

private theorem ed3226 : Within (view.checkEdge) 3226 25 := within_leaf (by decide +kernel)

private theorem ed3251 : Within (view.checkEdge) 3251 25 := within_leaf (by decide +kernel)

private theorem ed3276 : Within (view.checkEdge) 3276 25 := within_leaf (by decide +kernel)

private theorem ed3301 : Within (view.checkEdge) 3301 25 := within_leaf (by decide +kernel)

private theorem ed3326 : Within (view.checkEdge) 3326 25 := within_leaf (by decide +kernel)

private theorem ed3351 : Within (view.checkEdge) 3351 25 := within_leaf (by decide +kernel)

private theorem ed3376 : Within (view.checkEdge) 3376 25 := within_leaf (by decide +kernel)

private theorem ed3401 : Within (view.checkEdge) 3401 25 := within_leaf (by decide +kernel)

private theorem ed3426 : Within (view.checkEdge) 3426 25 := within_leaf (by decide +kernel)

private theorem ed3451 : Within (view.checkEdge) 3451 25 := within_leaf (by decide +kernel)

private theorem ed3476 : Within (view.checkEdge) 3476 25 := within_leaf (by decide +kernel)

private theorem ed3501 : Within (view.checkEdge) 3501 25 := within_leaf (by decide +kernel)

private theorem ed3526 : Within (view.checkEdge) 3526 25 := within_leaf (by decide +kernel)

private theorem ed3551 : Within (view.checkEdge) 3551 25 := within_leaf (by decide +kernel)

private theorem ed3576 : Within (view.checkEdge) 3576 25 := within_leaf (by decide +kernel)

private theorem ed3601 : Within (view.checkEdge) 3601 25 := within_leaf (by decide +kernel)

private theorem ed3626 : Within (view.checkEdge) 3626 25 := within_leaf (by decide +kernel)

private theorem ed3651 : Within (view.checkEdge) 3651 25 := within_leaf (by decide +kernel)

private theorem ed3676 : Within (view.checkEdge) 3676 25 := within_leaf (by decide +kernel)

private theorem edPart : Within (view.checkEdge) 2776 925 :=
  (within_join (a:=2776) (l:=450) (r:=475) (within_join (a:=2776) (l:=225) (r:=225) (within_join (a:=2776) (l:=100) (r:=125) (within_join (a:=2776) (l:=50) (r:=50) (within_join (a:=2776) (l:=25) (r:=25) ed2776 ed2801) (within_join (a:=2826) (l:=25) (r:=25) ed2826 ed2851)) (within_join (a:=2876) (l:=50) (r:=75) (within_join (a:=2876) (l:=25) (r:=25) ed2876 ed2901) (within_join (a:=2926) (l:=25) (r:=50) ed2926 (within_join (a:=2951) (l:=25) (r:=25) ed2951 ed2976)))) (within_join (a:=3001) (l:=100) (r:=125) (within_join (a:=3001) (l:=50) (r:=50) (within_join (a:=3001) (l:=25) (r:=25) ed3001 ed3026) (within_join (a:=3051) (l:=25) (r:=25) ed3051 ed3076)) (within_join (a:=3101) (l:=50) (r:=75) (within_join (a:=3101) (l:=25) (r:=25) ed3101 ed3126) (within_join (a:=3151) (l:=25) (r:=50) ed3151 (within_join (a:=3176) (l:=25) (r:=25) ed3176 ed3201))))) (within_join (a:=3226) (l:=225) (r:=250) (within_join (a:=3226) (l:=100) (r:=125) (within_join (a:=3226) (l:=50) (r:=50) (within_join (a:=3226) (l:=25) (r:=25) ed3226 ed3251) (within_join (a:=3276) (l:=25) (r:=25) ed3276 ed3301)) (within_join (a:=3326) (l:=50) (r:=75) (within_join (a:=3326) (l:=25) (r:=25) ed3326 ed3351) (within_join (a:=3376) (l:=25) (r:=50) ed3376 (within_join (a:=3401) (l:=25) (r:=25) ed3401 ed3426)))) (within_join (a:=3451) (l:=125) (r:=125) (within_join (a:=3451) (l:=50) (r:=75) (within_join (a:=3451) (l:=25) (r:=25) ed3451 ed3476) (within_join (a:=3501) (l:=25) (r:=50) ed3501 (within_join (a:=3526) (l:=25) (r:=25) ed3526 ed3551))) (within_join (a:=3576) (l:=50) (r:=75) (within_join (a:=3576) (l:=25) (r:=25) ed3576 ed3601) (within_join (a:=3626) (l:=25) (r:=50) ed3626 (within_join (a:=3651) (l:=25) (r:=25) ed3651 ed3676))))))

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
    (∀ i, 1803 ≤ i → i < 2404 → validIdentity 23 Staircase.schedule.entry (Staircase.schedule.identity i) = true) ∧
    (∀ i, 2776 ≤ i → i < 3701 → Staircase.schedule.edgeOK (Staircase.schedule.edge i) = true) ∧
    (∀ i, 885 ≤ i → i < 1180 → Staircase.schedule.timelineOK (Staircase.schedule.targets[i]?.getD []) = true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i ha hb
    simpa only [Index.checkId, view.entry_eq, view.id_eq] using indicesPart i ha (by omega)
  · intro i ha hb
    simpa only [Index.checkEdge, view.edge_eq, view.id_eq, view.basis_eq, ← view.ids.size_ok, view.hi,
      Block.edgeOK] using edPart i ha (by omega)
  · intro i ha hb
    simpa only [view.time_eq, view.events_eq] using tmPart i ha (by omega)
