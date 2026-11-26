-- Prove2me | solution 1 for IntMul.Kappa.DeferredReadout.Staircase.certificateBatch6
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T08:53:15.195496+00:00
-- url     : https://prove2.me/submissions/de5ccfae-a4c6-465e-8203-dd2fe6ddface

import Definitions.Def_IntMul_Kappa_DeferredReadoutStaircase

namespace StaircaseBatch5ReadoutAccess
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

end StaircaseBatch5ReadoutAccess

open StaircaseBatch5ReadoutAccess IntMul.Kappa.DeferredReadout
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

private theorem indices3005 : Within (view.checkId) 3005 25 := within_leaf (by decide +kernel)

private theorem indices3030 : Within (view.checkId) 3030 25 := within_leaf (by decide +kernel)

private theorem indices3055 : Within (view.checkId) 3055 25 := within_leaf (by decide +kernel)

private theorem indices3080 : Within (view.checkId) 3080 25 := within_leaf (by decide +kernel)

private theorem indices3105 : Within (view.checkId) 3105 25 := within_leaf (by decide +kernel)

private theorem indices3130 : Within (view.checkId) 3130 25 := within_leaf (by decide +kernel)

private theorem indices3155 : Within (view.checkId) 3155 25 := within_leaf (by decide +kernel)

private theorem indices3180 : Within (view.checkId) 3180 25 := within_leaf (by decide +kernel)

private theorem indices3205 : Within (view.checkId) 3205 25 := within_leaf (by decide +kernel)

private theorem indices3230 : Within (view.checkId) 3230 25 := within_leaf (by decide +kernel)

private theorem indices3255 : Within (view.checkId) 3255 25 := within_leaf (by decide +kernel)

private theorem indices3280 : Within (view.checkId) 3280 25 := within_leaf (by decide +kernel)

private theorem indices3305 : Within (view.checkId) 3305 25 := within_leaf (by decide +kernel)

private theorem indices3330 : Within (view.checkId) 3330 25 := within_leaf (by decide +kernel)

private theorem indices3355 : Within (view.checkId) 3355 25 := within_leaf (by decide +kernel)

private theorem indices3380 : Within (view.checkId) 3380 25 := within_leaf (by decide +kernel)

private theorem indices3405 : Within (view.checkId) 3405 25 := within_leaf (by decide +kernel)

private theorem indices3430 : Within (view.checkId) 3430 25 := within_leaf (by decide +kernel)

private theorem indices3455 : Within (view.checkId) 3455 25 := within_leaf (by decide +kernel)

private theorem indices3480 : Within (view.checkId) 3480 25 := within_leaf (by decide +kernel)

private theorem indices3505 : Within (view.checkId) 3505 25 := within_leaf (by decide +kernel)

private theorem indices3530 : Within (view.checkId) 3530 25 := within_leaf (by decide +kernel)

private theorem indices3555 : Within (view.checkId) 3555 25 := within_leaf (by decide +kernel)

private theorem indices3580 : Within (view.checkId) 3580 25 := within_leaf (by decide +kernel)

private theorem indices3605 : Within (view.checkId) 3605 1 := within_leaf (by decide +kernel)

private theorem indicesPart : Within (view.checkId) 3005 601 :=
  (within_join (a:=3005) (l:=300) (r:=301) (within_join (a:=3005) (l:=150) (r:=150) (within_join (a:=3005) (l:=75) (r:=75) (within_join (a:=3005) (l:=25) (r:=50) indices3005 (within_join (a:=3030) (l:=25) (r:=25) indices3030 indices3055)) (within_join (a:=3080) (l:=25) (r:=50) indices3080 (within_join (a:=3105) (l:=25) (r:=25) indices3105 indices3130))) (within_join (a:=3155) (l:=75) (r:=75) (within_join (a:=3155) (l:=25) (r:=50) indices3155 (within_join (a:=3180) (l:=25) (r:=25) indices3180 indices3205)) (within_join (a:=3230) (l:=25) (r:=50) indices3230 (within_join (a:=3255) (l:=25) (r:=25) indices3255 indices3280)))) (within_join (a:=3305) (l:=150) (r:=151) (within_join (a:=3305) (l:=75) (r:=75) (within_join (a:=3305) (l:=25) (r:=50) indices3305 (within_join (a:=3330) (l:=25) (r:=25) indices3330 indices3355)) (within_join (a:=3380) (l:=25) (r:=50) indices3380 (within_join (a:=3405) (l:=25) (r:=25) indices3405 indices3430))) (within_join (a:=3455) (l:=75) (r:=76) (within_join (a:=3455) (l:=25) (r:=50) indices3455 (within_join (a:=3480) (l:=25) (r:=25) indices3480 indices3505)) (within_join (a:=3530) (l:=50) (r:=26) (within_join (a:=3530) (l:=25) (r:=25) indices3530 indices3555) (within_join (a:=3580) (l:=25) (r:=1) indices3580 indices3605)))))

private theorem ed4626 : Within (view.checkEdge) 4626 25 := within_leaf (by decide +kernel)

private theorem ed4651 : Within (view.checkEdge) 4651 25 := within_leaf (by decide +kernel)

private theorem ed4676 : Within (view.checkEdge) 4676 25 := within_leaf (by decide +kernel)

private theorem ed4701 : Within (view.checkEdge) 4701 25 := within_leaf (by decide +kernel)

private theorem ed4726 : Within (view.checkEdge) 4726 25 := within_leaf (by decide +kernel)

private theorem ed4751 : Within (view.checkEdge) 4751 25 := within_leaf (by decide +kernel)

private theorem ed4776 : Within (view.checkEdge) 4776 25 := within_leaf (by decide +kernel)

private theorem ed4801 : Within (view.checkEdge) 4801 25 := within_leaf (by decide +kernel)

private theorem ed4826 : Within (view.checkEdge) 4826 25 := within_leaf (by decide +kernel)

private theorem ed4851 : Within (view.checkEdge) 4851 25 := within_leaf (by decide +kernel)

private theorem ed4876 : Within (view.checkEdge) 4876 25 := within_leaf (by decide +kernel)

private theorem ed4901 : Within (view.checkEdge) 4901 25 := within_leaf (by decide +kernel)

private theorem ed4926 : Within (view.checkEdge) 4926 25 := within_leaf (by decide +kernel)

private theorem ed4951 : Within (view.checkEdge) 4951 25 := within_leaf (by decide +kernel)

private theorem ed4976 : Within (view.checkEdge) 4976 25 := within_leaf (by decide +kernel)

private theorem ed5001 : Within (view.checkEdge) 5001 25 := within_leaf (by decide +kernel)

private theorem ed5026 : Within (view.checkEdge) 5026 25 := within_leaf (by decide +kernel)

private theorem ed5051 : Within (view.checkEdge) 5051 25 := within_leaf (by decide +kernel)

private theorem ed5076 : Within (view.checkEdge) 5076 25 := within_leaf (by decide +kernel)

private theorem ed5101 : Within (view.checkEdge) 5101 25 := within_leaf (by decide +kernel)

private theorem ed5126 : Within (view.checkEdge) 5126 25 := within_leaf (by decide +kernel)

private theorem ed5151 : Within (view.checkEdge) 5151 25 := within_leaf (by decide +kernel)

private theorem ed5176 : Within (view.checkEdge) 5176 25 := within_leaf (by decide +kernel)

private theorem ed5201 : Within (view.checkEdge) 5201 25 := within_leaf (by decide +kernel)

private theorem ed5226 : Within (view.checkEdge) 5226 25 := within_leaf (by decide +kernel)

private theorem ed5251 : Within (view.checkEdge) 5251 25 := within_leaf (by decide +kernel)

private theorem ed5276 : Within (view.checkEdge) 5276 25 := within_leaf (by decide +kernel)

private theorem ed5301 : Within (view.checkEdge) 5301 25 := within_leaf (by decide +kernel)

private theorem ed5326 : Within (view.checkEdge) 5326 25 := within_leaf (by decide +kernel)

private theorem ed5351 : Within (view.checkEdge) 5351 25 := within_leaf (by decide +kernel)

private theorem ed5376 : Within (view.checkEdge) 5376 25 := within_leaf (by decide +kernel)

private theorem ed5401 : Within (view.checkEdge) 5401 25 := within_leaf (by decide +kernel)

private theorem ed5426 : Within (view.checkEdge) 5426 25 := within_leaf (by decide +kernel)

private theorem ed5451 : Within (view.checkEdge) 5451 25 := within_leaf (by decide +kernel)

private theorem ed5476 : Within (view.checkEdge) 5476 25 := within_leaf (by decide +kernel)

private theorem ed5501 : Within (view.checkEdge) 5501 25 := within_leaf (by decide +kernel)

private theorem ed5526 : Within (view.checkEdge) 5526 25 := within_leaf (by decide +kernel)

private theorem ed5551 : Within (view.checkEdge) 5551 1 := within_leaf (by decide +kernel)

private theorem edPart : Within (view.checkEdge) 4626 926 :=
  (within_join (a:=4626) (l:=475) (r:=451) (within_join (a:=4626) (l:=225) (r:=250) (within_join (a:=4626) (l:=100) (r:=125) (within_join (a:=4626) (l:=50) (r:=50) (within_join (a:=4626) (l:=25) (r:=25) ed4626 ed4651) (within_join (a:=4676) (l:=25) (r:=25) ed4676 ed4701)) (within_join (a:=4726) (l:=50) (r:=75) (within_join (a:=4726) (l:=25) (r:=25) ed4726 ed4751) (within_join (a:=4776) (l:=25) (r:=50) ed4776 (within_join (a:=4801) (l:=25) (r:=25) ed4801 ed4826)))) (within_join (a:=4851) (l:=125) (r:=125) (within_join (a:=4851) (l:=50) (r:=75) (within_join (a:=4851) (l:=25) (r:=25) ed4851 ed4876) (within_join (a:=4901) (l:=25) (r:=50) ed4901 (within_join (a:=4926) (l:=25) (r:=25) ed4926 ed4951))) (within_join (a:=4976) (l:=50) (r:=75) (within_join (a:=4976) (l:=25) (r:=25) ed4976 ed5001) (within_join (a:=5026) (l:=25) (r:=50) ed5026 (within_join (a:=5051) (l:=25) (r:=25) ed5051 ed5076))))) (within_join (a:=5101) (l:=225) (r:=226) (within_join (a:=5101) (l:=100) (r:=125) (within_join (a:=5101) (l:=50) (r:=50) (within_join (a:=5101) (l:=25) (r:=25) ed5101 ed5126) (within_join (a:=5151) (l:=25) (r:=25) ed5151 ed5176)) (within_join (a:=5201) (l:=50) (r:=75) (within_join (a:=5201) (l:=25) (r:=25) ed5201 ed5226) (within_join (a:=5251) (l:=25) (r:=50) ed5251 (within_join (a:=5276) (l:=25) (r:=25) ed5276 ed5301)))) (within_join (a:=5326) (l:=125) (r:=101) (within_join (a:=5326) (l:=50) (r:=75) (within_join (a:=5326) (l:=25) (r:=25) ed5326 ed5351) (within_join (a:=5376) (l:=25) (r:=50) ed5376 (within_join (a:=5401) (l:=25) (r:=25) ed5401 ed5426))) (within_join (a:=5451) (l:=50) (r:=51) (within_join (a:=5451) (l:=25) (r:=25) ed5451 ed5476) (within_join (a:=5501) (l:=25) (r:=26) ed5501 (within_join (a:=5526) (l:=25) (r:=1) ed5526 ed5551))))))

private theorem tm1475 : Within (fun i => view.timeline (view.events i)) 1475 25 := within_leaf (by decide +kernel)

private theorem tm1500 : Within (fun i => view.timeline (view.events i)) 1500 25 := within_leaf (by decide +kernel)

private theorem tm1525 : Within (fun i => view.timeline (view.events i)) 1525 25 := within_leaf (by decide +kernel)

private theorem tm1550 : Within (fun i => view.timeline (view.events i)) 1550 25 := within_leaf (by decide +kernel)

private theorem tm1575 : Within (fun i => view.timeline (view.events i)) 1575 25 := within_leaf (by decide +kernel)

private theorem tm1600 : Within (fun i => view.timeline (view.events i)) 1600 25 := within_leaf (by decide +kernel)

private theorem tm1625 : Within (fun i => view.timeline (view.events i)) 1625 25 := within_leaf (by decide +kernel)

private theorem tm1650 : Within (fun i => view.timeline (view.events i)) 1650 25 := within_leaf (by decide +kernel)

private theorem tm1675 : Within (fun i => view.timeline (view.events i)) 1675 25 := within_leaf (by decide +kernel)

private theorem tm1700 : Within (fun i => view.timeline (view.events i)) 1700 25 := within_leaf (by decide +kernel)

private theorem tm1725 : Within (fun i => view.timeline (view.events i)) 1725 25 := within_leaf (by decide +kernel)

private theorem tm1750 : Within (fun i => view.timeline (view.events i)) 1750 21 := within_leaf (by decide +kernel)

private theorem tmPart : Within (fun i => view.timeline (view.events i)) 1475 296 :=
  (within_join (a:=1475) (l:=150) (r:=146) (within_join (a:=1475) (l:=75) (r:=75) (within_join (a:=1475) (l:=25) (r:=50) tm1475 (within_join (a:=1500) (l:=25) (r:=25) tm1500 tm1525)) (within_join (a:=1550) (l:=25) (r:=50) tm1550 (within_join (a:=1575) (l:=25) (r:=25) tm1575 tm1600))) (within_join (a:=1625) (l:=75) (r:=71) (within_join (a:=1625) (l:=25) (r:=50) tm1625 (within_join (a:=1650) (l:=25) (r:=25) tm1650 tm1675)) (within_join (a:=1700) (l:=25) (r:=46) tm1700 (within_join (a:=1725) (l:=25) (r:=21) tm1725 tm1750))))

theorem solution :
    (∀ i, 3005 ≤ i → i < 3606 → validIdentity 23 Staircase.schedule.entry (Staircase.schedule.identity i) = true) ∧
    (∀ i, 4626 ≤ i → i < 5552 → Staircase.schedule.edgeOK (Staircase.schedule.edge i) = true) ∧
    (∀ i, 1475 ≤ i → i < 1771 → Staircase.schedule.timelineOK (Staircase.schedule.targets[i]?.getD []) = true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i ha hb
    simpa only [Index.checkId, view.entry_eq, view.id_eq] using indicesPart i ha (by omega)
  · intro i ha hb
    simpa only [Index.checkEdge, view.edge_eq, view.id_eq, view.basis_eq, ← view.ids.size_ok, view.hi,
      Block.edgeOK] using edPart i ha (by omega)
  · intro i ha hb
    simpa only [view.time_eq, view.events_eq] using tmPart i ha (by omega)
