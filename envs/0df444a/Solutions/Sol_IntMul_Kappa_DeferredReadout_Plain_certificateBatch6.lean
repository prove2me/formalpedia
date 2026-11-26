-- Prove2me | solution 1 for IntMul.Kappa.DeferredReadout.Plain.certificateBatch6
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T08:53:12.794522+00:00
-- url     : https://prove2.me/submissions/6b77dd9e-c32d-47e4-8c25-3025bcb28400

import Definitions.Def_IntMul_Kappa_DeferredReadoutPlain

namespace PlainBatch5ReadoutAccess
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

end PlainBatch5ReadoutAccess

open PlainBatch5ReadoutAccess IntMul.Kappa.DeferredReadout
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

private theorem indices2447 : Within (view.checkId) 2447 25 := within_leaf (by decide +kernel)

private theorem indices2472 : Within (view.checkId) 2472 25 := within_leaf (by decide +kernel)

private theorem indices2497 : Within (view.checkId) 2497 25 := within_leaf (by decide +kernel)

private theorem indices2522 : Within (view.checkId) 2522 25 := within_leaf (by decide +kernel)

private theorem indices2547 : Within (view.checkId) 2547 25 := within_leaf (by decide +kernel)

private theorem indices2572 : Within (view.checkId) 2572 25 := within_leaf (by decide +kernel)

private theorem indices2597 : Within (view.checkId) 2597 25 := within_leaf (by decide +kernel)

private theorem indices2622 : Within (view.checkId) 2622 25 := within_leaf (by decide +kernel)

private theorem indices2647 : Within (view.checkId) 2647 25 := within_leaf (by decide +kernel)

private theorem indices2672 : Within (view.checkId) 2672 25 := within_leaf (by decide +kernel)

private theorem indices2697 : Within (view.checkId) 2697 25 := within_leaf (by decide +kernel)

private theorem indices2722 : Within (view.checkId) 2722 25 := within_leaf (by decide +kernel)

private theorem indices2747 : Within (view.checkId) 2747 25 := within_leaf (by decide +kernel)

private theorem indices2772 : Within (view.checkId) 2772 25 := within_leaf (by decide +kernel)

private theorem indices2797 : Within (view.checkId) 2797 25 := within_leaf (by decide +kernel)

private theorem indices2822 : Within (view.checkId) 2822 25 := within_leaf (by decide +kernel)

private theorem indices2847 : Within (view.checkId) 2847 25 := within_leaf (by decide +kernel)

private theorem indices2872 : Within (view.checkId) 2872 25 := within_leaf (by decide +kernel)

private theorem indices2897 : Within (view.checkId) 2897 25 := within_leaf (by decide +kernel)

private theorem indices2922 : Within (view.checkId) 2922 15 := within_leaf (by decide +kernel)

private theorem indicesPart : Within (view.checkId) 2447 490 :=
  (within_join (a:=2447) (l:=250) (r:=240) (within_join (a:=2447) (l:=125) (r:=125) (within_join (a:=2447) (l:=50) (r:=75) (within_join (a:=2447) (l:=25) (r:=25) indices2447 indices2472) (within_join (a:=2497) (l:=25) (r:=50) indices2497 (within_join (a:=2522) (l:=25) (r:=25) indices2522 indices2547))) (within_join (a:=2572) (l:=50) (r:=75) (within_join (a:=2572) (l:=25) (r:=25) indices2572 indices2597) (within_join (a:=2622) (l:=25) (r:=50) indices2622 (within_join (a:=2647) (l:=25) (r:=25) indices2647 indices2672)))) (within_join (a:=2697) (l:=125) (r:=115) (within_join (a:=2697) (l:=50) (r:=75) (within_join (a:=2697) (l:=25) (r:=25) indices2697 indices2722) (within_join (a:=2747) (l:=25) (r:=50) indices2747 (within_join (a:=2772) (l:=25) (r:=25) indices2772 indices2797))) (within_join (a:=2822) (l:=50) (r:=65) (within_join (a:=2822) (l:=25) (r:=25) indices2822 indices2847) (within_join (a:=2872) (l:=25) (r:=40) indices2872 (within_join (a:=2897) (l:=25) (r:=15) indices2897 indices2922)))))

private theorem ed4817 : Within (view.checkEdge) 4817 25 := within_leaf (by decide +kernel)

private theorem ed4842 : Within (view.checkEdge) 4842 25 := within_leaf (by decide +kernel)

private theorem ed4867 : Within (view.checkEdge) 4867 25 := within_leaf (by decide +kernel)

private theorem ed4892 : Within (view.checkEdge) 4892 25 := within_leaf (by decide +kernel)

private theorem ed4917 : Within (view.checkEdge) 4917 25 := within_leaf (by decide +kernel)

private theorem ed4942 : Within (view.checkEdge) 4942 25 := within_leaf (by decide +kernel)

private theorem ed4967 : Within (view.checkEdge) 4967 25 := within_leaf (by decide +kernel)

private theorem ed4992 : Within (view.checkEdge) 4992 25 := within_leaf (by decide +kernel)

private theorem ed5017 : Within (view.checkEdge) 5017 25 := within_leaf (by decide +kernel)

private theorem ed5042 : Within (view.checkEdge) 5042 25 := within_leaf (by decide +kernel)

private theorem ed5067 : Within (view.checkEdge) 5067 25 := within_leaf (by decide +kernel)

private theorem ed5092 : Within (view.checkEdge) 5092 25 := within_leaf (by decide +kernel)

private theorem ed5117 : Within (view.checkEdge) 5117 25 := within_leaf (by decide +kernel)

private theorem ed5142 : Within (view.checkEdge) 5142 25 := within_leaf (by decide +kernel)

private theorem ed5167 : Within (view.checkEdge) 5167 25 := within_leaf (by decide +kernel)

private theorem ed5192 : Within (view.checkEdge) 5192 25 := within_leaf (by decide +kernel)

private theorem ed5217 : Within (view.checkEdge) 5217 25 := within_leaf (by decide +kernel)

private theorem ed5242 : Within (view.checkEdge) 5242 25 := within_leaf (by decide +kernel)

private theorem ed5267 : Within (view.checkEdge) 5267 25 := within_leaf (by decide +kernel)

private theorem ed5292 : Within (view.checkEdge) 5292 25 := within_leaf (by decide +kernel)

private theorem ed5317 : Within (view.checkEdge) 5317 25 := within_leaf (by decide +kernel)

private theorem ed5342 : Within (view.checkEdge) 5342 25 := within_leaf (by decide +kernel)

private theorem ed5367 : Within (view.checkEdge) 5367 25 := within_leaf (by decide +kernel)

private theorem ed5392 : Within (view.checkEdge) 5392 25 := within_leaf (by decide +kernel)

private theorem ed5417 : Within (view.checkEdge) 5417 25 := within_leaf (by decide +kernel)

private theorem ed5442 : Within (view.checkEdge) 5442 25 := within_leaf (by decide +kernel)

private theorem ed5467 : Within (view.checkEdge) 5467 25 := within_leaf (by decide +kernel)

private theorem ed5492 : Within (view.checkEdge) 5492 25 := within_leaf (by decide +kernel)

private theorem ed5517 : Within (view.checkEdge) 5517 25 := within_leaf (by decide +kernel)

private theorem ed5542 : Within (view.checkEdge) 5542 25 := within_leaf (by decide +kernel)

private theorem ed5567 : Within (view.checkEdge) 5567 25 := within_leaf (by decide +kernel)

private theorem ed5592 : Within (view.checkEdge) 5592 25 := within_leaf (by decide +kernel)

private theorem ed5617 : Within (view.checkEdge) 5617 25 := within_leaf (by decide +kernel)

private theorem ed5642 : Within (view.checkEdge) 5642 25 := within_leaf (by decide +kernel)

private theorem ed5667 : Within (view.checkEdge) 5667 25 := within_leaf (by decide +kernel)

private theorem ed5692 : Within (view.checkEdge) 5692 25 := within_leaf (by decide +kernel)

private theorem ed5717 : Within (view.checkEdge) 5717 25 := within_leaf (by decide +kernel)

private theorem ed5742 : Within (view.checkEdge) 5742 25 := within_leaf (by decide +kernel)

private theorem ed5767 : Within (view.checkEdge) 5767 14 := within_leaf (by decide +kernel)

private theorem edPart : Within (view.checkEdge) 4817 964 :=
  (within_join (a:=4817) (l:=475) (r:=489) (within_join (a:=4817) (l:=225) (r:=250) (within_join (a:=4817) (l:=100) (r:=125) (within_join (a:=4817) (l:=50) (r:=50) (within_join (a:=4817) (l:=25) (r:=25) ed4817 ed4842) (within_join (a:=4867) (l:=25) (r:=25) ed4867 ed4892)) (within_join (a:=4917) (l:=50) (r:=75) (within_join (a:=4917) (l:=25) (r:=25) ed4917 ed4942) (within_join (a:=4967) (l:=25) (r:=50) ed4967 (within_join (a:=4992) (l:=25) (r:=25) ed4992 ed5017)))) (within_join (a:=5042) (l:=125) (r:=125) (within_join (a:=5042) (l:=50) (r:=75) (within_join (a:=5042) (l:=25) (r:=25) ed5042 ed5067) (within_join (a:=5092) (l:=25) (r:=50) ed5092 (within_join (a:=5117) (l:=25) (r:=25) ed5117 ed5142))) (within_join (a:=5167) (l:=50) (r:=75) (within_join (a:=5167) (l:=25) (r:=25) ed5167 ed5192) (within_join (a:=5217) (l:=25) (r:=50) ed5217 (within_join (a:=5242) (l:=25) (r:=25) ed5242 ed5267))))) (within_join (a:=5292) (l:=250) (r:=239) (within_join (a:=5292) (l:=125) (r:=125) (within_join (a:=5292) (l:=50) (r:=75) (within_join (a:=5292) (l:=25) (r:=25) ed5292 ed5317) (within_join (a:=5342) (l:=25) (r:=50) ed5342 (within_join (a:=5367) (l:=25) (r:=25) ed5367 ed5392))) (within_join (a:=5417) (l:=50) (r:=75) (within_join (a:=5417) (l:=25) (r:=25) ed5417 ed5442) (within_join (a:=5467) (l:=25) (r:=50) ed5467 (within_join (a:=5492) (l:=25) (r:=25) ed5492 ed5517)))) (within_join (a:=5542) (l:=125) (r:=114) (within_join (a:=5542) (l:=50) (r:=75) (within_join (a:=5542) (l:=25) (r:=25) ed5542 ed5567) (within_join (a:=5592) (l:=25) (r:=50) ed5592 (within_join (a:=5617) (l:=25) (r:=25) ed5617 ed5642))) (within_join (a:=5667) (l:=50) (r:=64) (within_join (a:=5667) (l:=25) (r:=25) ed5667 ed5692) (within_join (a:=5717) (l:=25) (r:=39) ed5717 (within_join (a:=5742) (l:=25) (r:=14) ed5742 ed5767))))))

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
    (∀ i, 2447 ≤ i → i < 2937 → validIdentity 23 Plain.schedule.entry (Plain.schedule.identity i) = true) ∧
    (∀ i, 4817 ≤ i → i < 5781 → Plain.schedule.edgeOK (Plain.schedule.edge i) = true) ∧
    (∀ i, 1475 ≤ i → i < 1771 → Plain.schedule.timelineOK (Plain.schedule.targets[i]?.getD []) = true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i ha hb
    simpa only [Index.checkId, view.entry_eq, view.id_eq] using indicesPart i ha (by omega)
  · intro i ha hb
    simpa only [Index.checkEdge, view.edge_eq, view.id_eq, view.basis_eq, ← view.ids.size_ok, view.hi,
      Block.edgeOK] using edPart i ha (by omega)
  · intro i ha hb
    simpa only [view.time_eq, view.events_eq] using tmPart i ha (by omega)
