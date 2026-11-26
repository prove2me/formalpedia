-- Prove2me | solution 1 for IntMul.Kappa.DeferredReadout.Staircase.auxiliaryReadouts
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T08:58:14.451427+00:00
-- url     : https://prove2.me/submissions/d95e7317-9f02-4bb6-8724-098ffaaa0fc5

import Definitions.Def_IntMul_Kappa_DeferredReadoutProjectors
import Definitions.Def_IntMul_Kappa_DeferredReadoutStaircase
import Theorems.Thm_IntMul_Kappa_DeferredReadout_auxiliaryReadoutsOfCertificates
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_nesting
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_gramCertificateBatch1
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_gramCertificateBatch2
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_gramCertificateBatch3
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_gramCertificateBatch4
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_gramCertificateBatch5
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_gramCertificateBatch6
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_gramCertificateBatch7
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_gramCertificateBatch8
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_gramCertificateBatch9
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_gramCertificateBatch10
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_gramCertificateBatch11
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_gramCertificateBatch12
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_gramCertificateBatch13
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_gramCertificateBatch14

namespace StaircaseAbsorptionReadoutAccess
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

end StaircaseAbsorptionReadoutAccess

open StaircaseAbsorptionReadoutAccess IntMul.Kappa.DeferredReadout
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

private theorem concreteGram (i : Nat) (hi : i < 4157) :
    ∃ c : GramCertificate, c.ok Staircase.schedule.entry (Staircase.schedule.basis i) = true := by
  by_cases h312 : i < 312
  · exact IntMul.Kappa.DeferredReadout.Staircase.gramCertificateBatch1 i (by omega) h312
  by_cases h624 : i < 624
  · exact IntMul.Kappa.DeferredReadout.Staircase.gramCertificateBatch2 i (by omega) h624
  by_cases h936 : i < 936
  · exact IntMul.Kappa.DeferredReadout.Staircase.gramCertificateBatch3 i (by omega) h936
  by_cases h1248 : i < 1248
  · exact IntMul.Kappa.DeferredReadout.Staircase.gramCertificateBatch4 i (by omega) h1248
  by_cases h1560 : i < 1560
  · exact IntMul.Kappa.DeferredReadout.Staircase.gramCertificateBatch5 i (by omega) h1560
  by_cases h1872 : i < 1872
  · exact IntMul.Kappa.DeferredReadout.Staircase.gramCertificateBatch6 i (by omega) h1872
  by_cases h2184 : i < 2184
  · exact IntMul.Kappa.DeferredReadout.Staircase.gramCertificateBatch7 i (by omega) h2184
  by_cases h2496 : i < 2496
  · exact IntMul.Kappa.DeferredReadout.Staircase.gramCertificateBatch8 i (by omega) h2496
  by_cases h2808 : i < 2808
  · exact IntMul.Kappa.DeferredReadout.Staircase.gramCertificateBatch9 i (by omega) h2808
  by_cases h3120 : i < 3120
  · exact IntMul.Kappa.DeferredReadout.Staircase.gramCertificateBatch10 i (by omega) h3120
  by_cases h3432 : i < 3432
  · exact IntMul.Kappa.DeferredReadout.Staircase.gramCertificateBatch11 i (by omega) h3432
  by_cases h3744 : i < 3744
  · exact IntMul.Kappa.DeferredReadout.Staircase.gramCertificateBatch12 i (by omega) h3744
  by_cases h4056 : i < 4056
  · exact IntMul.Kappa.DeferredReadout.Staircase.gramCertificateBatch13 i (by omega) h4056
  exact IntMul.Kappa.DeferredReadout.Staircase.gramCertificateBatch14 i (by omega) hi

private def boundsAt (i : Nat) : Bool := (view.events i).all fun e => decide (e.frame < view.bs.size)
private theorem boundsRange0 : Within (boundsAt) 0 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange32 : Within (boundsAt) 32 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange64 : Within (boundsAt) 64 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange96 : Within (boundsAt) 96 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange128 : Within (boundsAt) 128 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange160 : Within (boundsAt) 160 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange192 : Within (boundsAt) 192 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange224 : Within (boundsAt) 224 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange256 : Within (boundsAt) 256 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange288 : Within (boundsAt) 288 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange320 : Within (boundsAt) 320 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange352 : Within (boundsAt) 352 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange384 : Within (boundsAt) 384 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange416 : Within (boundsAt) 416 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange448 : Within (boundsAt) 448 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange480 : Within (boundsAt) 480 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange512 : Within (boundsAt) 512 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange544 : Within (boundsAt) 544 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange576 : Within (boundsAt) 576 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange608 : Within (boundsAt) 608 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange640 : Within (boundsAt) 640 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange672 : Within (boundsAt) 672 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange704 : Within (boundsAt) 704 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange736 : Within (boundsAt) 736 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange768 : Within (boundsAt) 768 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange800 : Within (boundsAt) 800 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange832 : Within (boundsAt) 832 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange864 : Within (boundsAt) 864 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange896 : Within (boundsAt) 896 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange928 : Within (boundsAt) 928 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange960 : Within (boundsAt) 960 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange992 : Within (boundsAt) 992 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1024 : Within (boundsAt) 1024 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1056 : Within (boundsAt) 1056 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1088 : Within (boundsAt) 1088 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1120 : Within (boundsAt) 1120 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1152 : Within (boundsAt) 1152 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1184 : Within (boundsAt) 1184 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1216 : Within (boundsAt) 1216 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1248 : Within (boundsAt) 1248 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1280 : Within (boundsAt) 1280 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1312 : Within (boundsAt) 1312 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1344 : Within (boundsAt) 1344 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1376 : Within (boundsAt) 1376 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1408 : Within (boundsAt) 1408 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1440 : Within (boundsAt) 1440 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1472 : Within (boundsAt) 1472 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1504 : Within (boundsAt) 1504 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1536 : Within (boundsAt) 1536 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1568 : Within (boundsAt) 1568 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1600 : Within (boundsAt) 1600 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1632 : Within (boundsAt) 1632 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1664 : Within (boundsAt) 1664 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1696 : Within (boundsAt) 1696 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1728 : Within (boundsAt) 1728 32 :=
  within_leaf (by decide +kernel)

private theorem boundsRange1760 : Within (boundsAt) 1760 11 :=
  within_leaf (by decide +kernel)

private theorem boundsRangeAll : Within (boundsAt) 0 1771 :=
  (within_join (a:=0) (l:=896) (r:=875) (within_join (a:=0) (l:=448) (r:=448) (within_join (a:=0) (l:=224) (r:=224) (within_join (a:=0) (l:=96) (r:=128) (within_join (a:=0) (l:=32) (r:=64) boundsRange0 (within_join (a:=32) (l:=32) (r:=32) boundsRange32 boundsRange64)) (within_join (a:=96) (l:=64) (r:=64) (within_join (a:=96) (l:=32) (r:=32) boundsRange96 boundsRange128) (within_join (a:=160) (l:=32) (r:=32) boundsRange160 boundsRange192))) (within_join (a:=224) (l:=96) (r:=128) (within_join (a:=224) (l:=32) (r:=64) boundsRange224 (within_join (a:=256) (l:=32) (r:=32) boundsRange256 boundsRange288)) (within_join (a:=320) (l:=64) (r:=64) (within_join (a:=320) (l:=32) (r:=32) boundsRange320 boundsRange352) (within_join (a:=384) (l:=32) (r:=32) boundsRange384 boundsRange416)))) (within_join (a:=448) (l:=224) (r:=224) (within_join (a:=448) (l:=96) (r:=128) (within_join (a:=448) (l:=32) (r:=64) boundsRange448 (within_join (a:=480) (l:=32) (r:=32) boundsRange480 boundsRange512)) (within_join (a:=544) (l:=64) (r:=64) (within_join (a:=544) (l:=32) (r:=32) boundsRange544 boundsRange576) (within_join (a:=608) (l:=32) (r:=32) boundsRange608 boundsRange640))) (within_join (a:=672) (l:=96) (r:=128) (within_join (a:=672) (l:=32) (r:=64) boundsRange672 (within_join (a:=704) (l:=32) (r:=32) boundsRange704 boundsRange736)) (within_join (a:=768) (l:=64) (r:=64) (within_join (a:=768) (l:=32) (r:=32) boundsRange768 boundsRange800) (within_join (a:=832) (l:=32) (r:=32) boundsRange832 boundsRange864))))) (within_join (a:=896) (l:=448) (r:=427) (within_join (a:=896) (l:=224) (r:=224) (within_join (a:=896) (l:=96) (r:=128) (within_join (a:=896) (l:=32) (r:=64) boundsRange896 (within_join (a:=928) (l:=32) (r:=32) boundsRange928 boundsRange960)) (within_join (a:=992) (l:=64) (r:=64) (within_join (a:=992) (l:=32) (r:=32) boundsRange992 boundsRange1024) (within_join (a:=1056) (l:=32) (r:=32) boundsRange1056 boundsRange1088))) (within_join (a:=1120) (l:=96) (r:=128) (within_join (a:=1120) (l:=32) (r:=64) boundsRange1120 (within_join (a:=1152) (l:=32) (r:=32) boundsRange1152 boundsRange1184)) (within_join (a:=1216) (l:=64) (r:=64) (within_join (a:=1216) (l:=32) (r:=32) boundsRange1216 boundsRange1248) (within_join (a:=1280) (l:=32) (r:=32) boundsRange1280 boundsRange1312)))) (within_join (a:=1344) (l:=224) (r:=203) (within_join (a:=1344) (l:=96) (r:=128) (within_join (a:=1344) (l:=32) (r:=64) boundsRange1344 (within_join (a:=1376) (l:=32) (r:=32) boundsRange1376 boundsRange1408)) (within_join (a:=1440) (l:=64) (r:=64) (within_join (a:=1440) (l:=32) (r:=32) boundsRange1440 boundsRange1472) (within_join (a:=1504) (l:=32) (r:=32) boundsRange1504 boundsRange1536))) (within_join (a:=1568) (l:=96) (r:=107) (within_join (a:=1568) (l:=32) (r:=64) boundsRange1568 (within_join (a:=1600) (l:=32) (r:=32) boundsRange1600 boundsRange1632)) (within_join (a:=1664) (l:=64) (r:=43) (within_join (a:=1664) (l:=32) (r:=32) boundsRange1664 boundsRange1696) (within_join (a:=1728) (l:=32) (r:=11) boundsRange1728 boundsRange1760))))))

theorem solution (t : Fin 1771) :
    (∀ U ∈ Staircase.framesAt t, IsCompl U (gramForm.orthogonal U)) ∧
    (readoutEdges (Staircase.framesAt t) (targetDirection t)).Pairwise
      (fun earlier later => later * earlier = earlier) := by
  classical
  let d := Staircase.schedule
  have ex (i : Nat) (hi : i<d.frames.size) :
      ∃ c : GramCertificate, c.ok d.entry (d.basis i) = true := by
    have size : d.frames.size = 4157 := by
      change Staircase.schedule.frames.size = 4157
      rw [← view.hb, view.bs.size_ok] <;> rfl
    exact concreteGram i (by omega)
  let cert (i : Nat) := if hi : i < d.frames.size then Classical.choose (ex i hi) else default
  have hg (i : Nat) (hi : i < d.frames.size) : (cert i).ok d.entry (d.basis i) = true := by
    simpa only [cert, dif_pos hi] using Classical.choose_spec (ex i hi)
  have he : ∀ e ∈ d.targets[t.val]?.getD [], e.frame < d.frames.size := by
    intro e h
    have hb := boundsRangeAll t.val (Nat.zero_le _) (by simpa using t.isLt)
    have hm : e ∈ view.events t.val := by simpa only [view.events_eq] using h
    have hlt := of_decide_eq_true (List.all_eq_true.mp hb e hm)
    simpa only [← view.bs.size_ok, view.hb] using hlt
  exact auxiliaryReadoutsOfCertificates d cert _ (targetDirection t) hg he (Staircase.nesting t)
