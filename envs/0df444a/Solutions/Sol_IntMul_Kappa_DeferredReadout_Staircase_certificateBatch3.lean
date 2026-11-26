-- Prove2me | solution 1 for IntMul.Kappa.DeferredReadout.Staircase.certificateBatch3
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T08:53:01.296471+00:00
-- url     : https://prove2.me/submissions/8ec93402-7816-4f5b-be6e-1259e2b5553d

import Definitions.Def_IntMul_Kappa_DeferredReadoutStaircase

namespace StaircaseBatch2ReadoutAccess
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

end StaircaseBatch2ReadoutAccess

open StaircaseBatch2ReadoutAccess IntMul.Kappa.DeferredReadout
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

private theorem indices1202 : Within (view.checkId) 1202 25 := within_leaf (by decide +kernel)

private theorem indices1227 : Within (view.checkId) 1227 25 := within_leaf (by decide +kernel)

private theorem indices1252 : Within (view.checkId) 1252 25 := within_leaf (by decide +kernel)

private theorem indices1277 : Within (view.checkId) 1277 25 := within_leaf (by decide +kernel)

private theorem indices1302 : Within (view.checkId) 1302 25 := within_leaf (by decide +kernel)

private theorem indices1327 : Within (view.checkId) 1327 25 := within_leaf (by decide +kernel)

private theorem indices1352 : Within (view.checkId) 1352 25 := within_leaf (by decide +kernel)

private theorem indices1377 : Within (view.checkId) 1377 25 := within_leaf (by decide +kernel)

private theorem indices1402 : Within (view.checkId) 1402 25 := within_leaf (by decide +kernel)

private theorem indices1427 : Within (view.checkId) 1427 25 := within_leaf (by decide +kernel)

private theorem indices1452 : Within (view.checkId) 1452 25 := within_leaf (by decide +kernel)

private theorem indices1477 : Within (view.checkId) 1477 25 := within_leaf (by decide +kernel)

private theorem indices1502 : Within (view.checkId) 1502 25 := within_leaf (by decide +kernel)

private theorem indices1527 : Within (view.checkId) 1527 25 := within_leaf (by decide +kernel)

private theorem indices1552 : Within (view.checkId) 1552 25 := within_leaf (by decide +kernel)

private theorem indices1577 : Within (view.checkId) 1577 25 := within_leaf (by decide +kernel)

private theorem indices1602 : Within (view.checkId) 1602 25 := within_leaf (by decide +kernel)

private theorem indices1627 : Within (view.checkId) 1627 25 := within_leaf (by decide +kernel)

private theorem indices1652 : Within (view.checkId) 1652 25 := within_leaf (by decide +kernel)

private theorem indices1677 : Within (view.checkId) 1677 25 := within_leaf (by decide +kernel)

private theorem indices1702 : Within (view.checkId) 1702 25 := within_leaf (by decide +kernel)

private theorem indices1727 : Within (view.checkId) 1727 25 := within_leaf (by decide +kernel)

private theorem indices1752 : Within (view.checkId) 1752 25 := within_leaf (by decide +kernel)

private theorem indices1777 : Within (view.checkId) 1777 25 := within_leaf (by decide +kernel)

private theorem indices1802 : Within (view.checkId) 1802 1 := within_leaf (by decide +kernel)

private theorem indicesPart : Within (view.checkId) 1202 601 :=
  (within_join (a:=1202) (l:=300) (r:=301) (within_join (a:=1202) (l:=150) (r:=150) (within_join (a:=1202) (l:=75) (r:=75) (within_join (a:=1202) (l:=25) (r:=50) indices1202 (within_join (a:=1227) (l:=25) (r:=25) indices1227 indices1252)) (within_join (a:=1277) (l:=25) (r:=50) indices1277 (within_join (a:=1302) (l:=25) (r:=25) indices1302 indices1327))) (within_join (a:=1352) (l:=75) (r:=75) (within_join (a:=1352) (l:=25) (r:=50) indices1352 (within_join (a:=1377) (l:=25) (r:=25) indices1377 indices1402)) (within_join (a:=1427) (l:=25) (r:=50) indices1427 (within_join (a:=1452) (l:=25) (r:=25) indices1452 indices1477)))) (within_join (a:=1502) (l:=150) (r:=151) (within_join (a:=1502) (l:=75) (r:=75) (within_join (a:=1502) (l:=25) (r:=50) indices1502 (within_join (a:=1527) (l:=25) (r:=25) indices1527 indices1552)) (within_join (a:=1577) (l:=25) (r:=50) indices1577 (within_join (a:=1602) (l:=25) (r:=25) indices1602 indices1627))) (within_join (a:=1652) (l:=75) (r:=76) (within_join (a:=1652) (l:=25) (r:=50) indices1652 (within_join (a:=1677) (l:=25) (r:=25) indices1677 indices1702)) (within_join (a:=1727) (l:=50) (r:=26) (within_join (a:=1727) (l:=25) (r:=25) indices1727 indices1752) (within_join (a:=1777) (l:=25) (r:=1) indices1777 indices1802)))))

private theorem ed1850 : Within (view.checkEdge) 1850 25 := within_leaf (by decide +kernel)

private theorem ed1875 : Within (view.checkEdge) 1875 25 := within_leaf (by decide +kernel)

private theorem ed1900 : Within (view.checkEdge) 1900 25 := within_leaf (by decide +kernel)

private theorem ed1925 : Within (view.checkEdge) 1925 25 := within_leaf (by decide +kernel)

private theorem ed1950 : Within (view.checkEdge) 1950 25 := within_leaf (by decide +kernel)

private theorem ed1975 : Within (view.checkEdge) 1975 25 := within_leaf (by decide +kernel)

private theorem ed2000 : Within (view.checkEdge) 2000 25 := within_leaf (by decide +kernel)

private theorem ed2025 : Within (view.checkEdge) 2025 25 := within_leaf (by decide +kernel)

private theorem ed2050 : Within (view.checkEdge) 2050 25 := within_leaf (by decide +kernel)

private theorem ed2075 : Within (view.checkEdge) 2075 25 := within_leaf (by decide +kernel)

private theorem ed2100 : Within (view.checkEdge) 2100 25 := within_leaf (by decide +kernel)

private theorem ed2125 : Within (view.checkEdge) 2125 25 := within_leaf (by decide +kernel)

private theorem ed2150 : Within (view.checkEdge) 2150 25 := within_leaf (by decide +kernel)

private theorem ed2175 : Within (view.checkEdge) 2175 25 := within_leaf (by decide +kernel)

private theorem ed2200 : Within (view.checkEdge) 2200 25 := within_leaf (by decide +kernel)

private theorem ed2225 : Within (view.checkEdge) 2225 25 := within_leaf (by decide +kernel)

private theorem ed2250 : Within (view.checkEdge) 2250 25 := within_leaf (by decide +kernel)

private theorem ed2275 : Within (view.checkEdge) 2275 25 := within_leaf (by decide +kernel)

private theorem ed2300 : Within (view.checkEdge) 2300 25 := within_leaf (by decide +kernel)

private theorem ed2325 : Within (view.checkEdge) 2325 25 := within_leaf (by decide +kernel)

private theorem ed2350 : Within (view.checkEdge) 2350 25 := within_leaf (by decide +kernel)

private theorem ed2375 : Within (view.checkEdge) 2375 25 := within_leaf (by decide +kernel)

private theorem ed2400 : Within (view.checkEdge) 2400 25 := within_leaf (by decide +kernel)

private theorem ed2425 : Within (view.checkEdge) 2425 25 := within_leaf (by decide +kernel)

private theorem ed2450 : Within (view.checkEdge) 2450 25 := within_leaf (by decide +kernel)

private theorem ed2475 : Within (view.checkEdge) 2475 25 := within_leaf (by decide +kernel)

private theorem ed2500 : Within (view.checkEdge) 2500 25 := within_leaf (by decide +kernel)

private theorem ed2525 : Within (view.checkEdge) 2525 25 := within_leaf (by decide +kernel)

private theorem ed2550 : Within (view.checkEdge) 2550 25 := within_leaf (by decide +kernel)

private theorem ed2575 : Within (view.checkEdge) 2575 25 := within_leaf (by decide +kernel)

private theorem ed2600 : Within (view.checkEdge) 2600 25 := within_leaf (by decide +kernel)

private theorem ed2625 : Within (view.checkEdge) 2625 25 := within_leaf (by decide +kernel)

private theorem ed2650 : Within (view.checkEdge) 2650 25 := within_leaf (by decide +kernel)

private theorem ed2675 : Within (view.checkEdge) 2675 25 := within_leaf (by decide +kernel)

private theorem ed2700 : Within (view.checkEdge) 2700 25 := within_leaf (by decide +kernel)

private theorem ed2725 : Within (view.checkEdge) 2725 25 := within_leaf (by decide +kernel)

private theorem ed2750 : Within (view.checkEdge) 2750 25 := within_leaf (by decide +kernel)

private theorem ed2775 : Within (view.checkEdge) 2775 1 := within_leaf (by decide +kernel)

private theorem edPart : Within (view.checkEdge) 1850 926 :=
  (within_join (a:=1850) (l:=475) (r:=451) (within_join (a:=1850) (l:=225) (r:=250) (within_join (a:=1850) (l:=100) (r:=125) (within_join (a:=1850) (l:=50) (r:=50) (within_join (a:=1850) (l:=25) (r:=25) ed1850 ed1875) (within_join (a:=1900) (l:=25) (r:=25) ed1900 ed1925)) (within_join (a:=1950) (l:=50) (r:=75) (within_join (a:=1950) (l:=25) (r:=25) ed1950 ed1975) (within_join (a:=2000) (l:=25) (r:=50) ed2000 (within_join (a:=2025) (l:=25) (r:=25) ed2025 ed2050)))) (within_join (a:=2075) (l:=125) (r:=125) (within_join (a:=2075) (l:=50) (r:=75) (within_join (a:=2075) (l:=25) (r:=25) ed2075 ed2100) (within_join (a:=2125) (l:=25) (r:=50) ed2125 (within_join (a:=2150) (l:=25) (r:=25) ed2150 ed2175))) (within_join (a:=2200) (l:=50) (r:=75) (within_join (a:=2200) (l:=25) (r:=25) ed2200 ed2225) (within_join (a:=2250) (l:=25) (r:=50) ed2250 (within_join (a:=2275) (l:=25) (r:=25) ed2275 ed2300))))) (within_join (a:=2325) (l:=225) (r:=226) (within_join (a:=2325) (l:=100) (r:=125) (within_join (a:=2325) (l:=50) (r:=50) (within_join (a:=2325) (l:=25) (r:=25) ed2325 ed2350) (within_join (a:=2375) (l:=25) (r:=25) ed2375 ed2400)) (within_join (a:=2425) (l:=50) (r:=75) (within_join (a:=2425) (l:=25) (r:=25) ed2425 ed2450) (within_join (a:=2475) (l:=25) (r:=50) ed2475 (within_join (a:=2500) (l:=25) (r:=25) ed2500 ed2525)))) (within_join (a:=2550) (l:=125) (r:=101) (within_join (a:=2550) (l:=50) (r:=75) (within_join (a:=2550) (l:=25) (r:=25) ed2550 ed2575) (within_join (a:=2600) (l:=25) (r:=50) ed2600 (within_join (a:=2625) (l:=25) (r:=25) ed2625 ed2650))) (within_join (a:=2675) (l:=50) (r:=51) (within_join (a:=2675) (l:=25) (r:=25) ed2675 ed2700) (within_join (a:=2725) (l:=25) (r:=26) ed2725 (within_join (a:=2750) (l:=25) (r:=1) ed2750 ed2775))))))

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
    (∀ i, 1202 ≤ i → i < 1803 → validIdentity 23 Staircase.schedule.entry (Staircase.schedule.identity i) = true) ∧
    (∀ i, 1850 ≤ i → i < 2776 → Staircase.schedule.edgeOK (Staircase.schedule.edge i) = true) ∧
    (∀ i, 590 ≤ i → i < 885 → Staircase.schedule.timelineOK (Staircase.schedule.targets[i]?.getD []) = true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i ha hb
    simpa only [Index.checkId, view.entry_eq, view.id_eq] using indicesPart i ha (by omega)
  · intro i ha hb
    simpa only [Index.checkEdge, view.edge_eq, view.id_eq, view.basis_eq, ← view.ids.size_ok, view.hi,
      Block.edgeOK] using edPart i ha (by omega)
  · intro i ha hb
    simpa only [view.time_eq, view.events_eq] using tmPart i ha (by omega)
