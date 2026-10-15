-- Prove2me | solution 1 for OAI.Paper320.quantitative_separation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:59:56.361244+00:00
-- url     : https://prove2.me/submissions/d7b2c036-c3c7-48d2-9740-16816468327d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/Separation.lean:L12-L21
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.Paper320.quantitative_separation.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_Paper320_quantitative_separation) verbatim and is proved by it.
import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tower
import Definitions.Def_OAI_Combinatorics_Sensitivity_TowerProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_ProfileArithmetic
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_OAI_Combinatorics_Sensitivity_Or
import Definitions.Def_OAI_Combinatorics_Sensitivity_Reindex
import Definitions.Def_OAI_Combinatorics_Sensitivity_Construction
import Definitions.Def_OAI_Combinatorics_Sensitivity_FixedCoordinates
import Definitions.Def_OAI_Combinatorics_Sensitivity_LabelingEvents
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCyclic
import Definitions.Def_OAI_Combinatorics_Sensitivity_Iterates
import Theorems.Thm_OAI_Paper320_Tournament_card_badLabelings_le
import Theorems.Thm_OAI_Paper320_ballPredicate_sensitivityAt_zero_le
import Theorems.Thm_OAI_Paper320_blockSensitivityAt_compose_zero_le
import Theorems.Thm_OAI_Paper320_exists_blockSensitivityAt_family
import Theorems.Thm_OAI_Paper320_initialFamily_joint
import Theorems.Thm_OAI_Paper320_le_blockSensitivityAt_of_family
import Theorems.Thm_OAI_Paper320_quantitative_profile_bounds
import Theorems.Thm_OAI_Paper320_sensitivity_orCopies_le
import Theorems.Thm_OAI_Paper320_towerFamily_blocks
import Theorems.Thm_OAI_Paper320_tower_four_recurrences

-- ---- from OAI.Combinatorics.Sensitivity.HammingBase ----
namespace OAI

/-! Hamming balls used by the initial nested predicates. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I C : Type} [Fintype I]

theorem ballPredicate_eq_true [Fintype C] (centers : C → I → Bool) (R : ℕ)
    (x : I → Bool) :
    ballPredicate centers R x = true ↔ ∃ c, hammingDist x (centers c) ≤ R := by
  simp [ballPredicate]

theorem ballPredicate_nested [Fintype C] (centers : C → I → Bool)
    {R S : ℕ} (hRS : R ≤ S) (x : I → Bool)
    (h : ballPredicate centers R x = true) : ballPredicate centers S x = true := by
  rcases (ballPredicate_eq_true centers R x).1 h with ⟨c, hc⟩
  exact (ballPredicate_eq_true centers S x).2 ⟨c, hc.trans hRS⟩

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveProfiles ----
namespace OAI

/-! The side and joint profiles count literal flips of the same raw input. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem sensitivityAt_le_sideSensitivity {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) (q : Fin h) (x : I → Bool)
    (hx : F q x = b) : sensitivityAt (F q) x ≤ sideSensitivity F b := by
  apply Finset.le_sup_of_le (Finset.mem_univ q)
  apply Finset.le_sup_of_le (Finset.mem_univ x)
  simp [hx]

theorem sideSensitivity_le {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) (B : ℕ)
    (hB : ∀ q x, F q x = b → sensitivityAt (F q) x ≤ B) :
    sideSensitivity F b ≤ B := by
  apply Finset.sup_le
  intro q _
  apply Finset.sup_le
  intro x _
  split_ifs with hx
  · exact hB q x hx
  · exact Nat.zero_le _

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.Basic ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Finite Boolean flips and the exact maximum/witness interfaces for sensitivity. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I J K : Type}

theorem flip_insert (x : I → Bool) (i : I) (B : Finset I) (hi : i ∉ B) :
    flip x (insert i B) = flip (flip x B) {i} := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [flip, hi]
  · simp [flip, hji]

section Finite

variable [Fintype I]

theorem flip_differences (x y : I → Bool) :
    flip x (Finset.univ.filter fun i => x i ≠ y i) = y := by
  funext i
  cases hx : x i <;> cases hy : y i <;> simp [flip, hx, hy]

theorem sensitivityAt_le_card (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivityAt f x ≤ Fintype.card I :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem sensitivityAt_le_sensitivity (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivityAt f x ≤ sensitivity f :=
  Finset.le_sup (Finset.mem_univ x)

theorem sensitivity_le (f : (I → Bool) → Bool) {n : ℕ}
    (h : ∀ x, sensitivityAt f x ≤ n) : sensitivity f ≤ n :=
  Finset.sup_le fun x _ => h x

theorem sensitivityAt_eq_zero_iff (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivityAt f x = 0 ↔ ∀ i, f (flip x {i}) = f x := by
  simp [sensitivityAt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

theorem blockSensitivityAt_le_blockSensitivity (f : (I → Bool) → Bool) (x : I → Bool) :
    blockSensitivityAt f x ≤ blockSensitivity f :=
  Finset.le_sup (Finset.mem_univ x)

theorem blockSensitivityAt_le (f : (I → Bool) → Bool) (x : I → Bool) {n : ℕ}
    (h : ∀ blocks : Finset (Finset I),
      (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) →
      (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x) → blocks.card ≤ n) :
    blockSensitivityAt f x ≤ n := by
  apply Finset.sup_le
  intro blocks _
  split_ifs with hb
  · exact h blocks hb.1 hb.2
  · exact Nat.zero_le _

theorem eq_of_singleton_invariant (f : (I → Bool) → Bool)
    (h : ∀ x i, f (flip x {i}) = f x) (x y : I → Bool) : f x = f y := by
  have hflip (B : Finset I) : f (flip x B) = f x := by
    induction B using Finset.induction with
    | empty => simp
    | @insert i B hi ih => rw [flip_insert x i B hi, h, ih]
  rw [← flip_differences x y, hflip]

theorem sensitivity_pos_of_nonconstant (f : (I → Bool) → Bool)
    (h : ∃ x y, f x ≠ f y) : 0 < sensitivity f := by
  by_contra hn
  have hz : sensitivity f = 0 := Nat.eq_zero_of_not_pos hn
  have hi (x : I → Bool) (i : I) : f (flip x {i}) = f x := by
    apply (sensitivityAt_eq_zero_iff f x).mp _ i
    exact Nat.eq_zero_of_le_zero ((sensitivityAt_le_sensitivity f x).trans_eq hz)
  obtain ⟨x, y, hxy⟩ := h
  exact hxy (eq_of_singleton_invariant f hi x y)

end Finite
end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.InitialPredicates ----
namespace OAI

/-! The separated Hamming-ball predicates and their explicit sensitive blocks. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem baseBlock_card {M L : ℕ} (j : Fin M) : (baseBlock (L := L) j).card = L := by
  have h : (baseBlock (L := L) j).card = (Finset.univ : Finset (Fin L)).card := by
    apply Finset.card_bij (fun p _ => p.2)
    · intro p _
      exact Finset.mem_univ _
    · intro p hp q hq hpq
      exact Prod.ext (((mem_baseBlock j p).mp hp).trans ((mem_baseBlock j q).mp hq).symm) hpq
    · intro b _
      exact ⟨(j, b), (mem_baseBlock j (j, b)).mpr rfl, rfl⟩
  simpa using h

theorem baseBlock_nonempty {M L : ℕ} (hL : 0 < L) (j : Fin M) :
    (baseBlock (L := L) j).Nonempty := by
  rw [← Finset.card_pos, baseBlock_card]
  exact hL

theorem baseBlock_disjoint {M L : ℕ} :
    Pairwise fun i j : Fin M => Disjoint (baseBlock (L := L) i) (baseBlock j) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  rintro ⟨a, b⟩ hi hj
  simp only [mem_baseBlock] at hi hj
  exact hij (hi.symm.trans hj)

theorem flip_zero_baseBlock {M L : ℕ} (j : Fin M) :
    flip (fun _ : Fin M × Fin L => false) (baseBlock j) = blockCenter j := by
  ext p
  simp [flip, blockCenter]

theorem hammingDist_zero_blockCenter {M L : ℕ} (j : Fin M) :
    hammingDist (fun _ : Fin M × Fin L => false) (blockCenter j) = L := by
  have hs : (Finset.univ.filter fun p : Fin M × Fin L => false ≠ blockCenter j p) =
      baseBlock j := by
    ext p
    simp [blockCenter]
  rw [hammingDist, hs, baseBlock_card]

theorem hammingDist_blockCenter {M L : ℕ} (i j : Fin M) (hij : i ≠ j) :
    hammingDist (blockCenter (L := L) i) (blockCenter j) = 2 * L := by
  have hs : (Finset.univ.filter fun p : Fin M × Fin L =>
      blockCenter i p ≠ blockCenter j p) =
      baseBlock i ∪ baseBlock j := by
    ext ⟨a, b⟩
    by_cases ha : a = i <;> by_cases hb : a = j <;> simp_all [blockCenter]
  rw [hammingDist, hs]
  rw [Finset.card_union_of_disjoint (baseBlock_disjoint hij), baseBlock_card, baseBlock_card]
  omega

theorem initialFamily_nested (d M : ℕ) : NestedFamily (initialFamily d M) := by
  constructor
  intro q q' x hqq hx
  exact ballPredicate_nested blockCenter (by omega) x hx

theorem initialFamily_zero (d M : ℕ) (q : Fin (d + 1)) :
    initialFamily d M q (fun _ => false) = false := by
  have hn : ¬ ∃ c : Fin M,
      hammingDist (fun _ : Fin M × Fin (d + 2) => false) (blockCenter c) ≤ d - q.val := by
    rintro ⟨c, hc⟩
    rw [hammingDist_zero_blockCenter] at hc
    omega
  simp [initialFamily, ballPredicate, hn]

theorem initialFamily_baseBlock (d M : ℕ) (q : Fin (d + 1)) (j : Fin M) :
    initialFamily d M q (flip (fun _ => false) (baseBlock j)) = true := by
  rw [flip_zero_baseBlock]
  apply (ballPredicate_eq_true blockCenter (d - q.val) (blockCenter j)).2
  exact ⟨j, by simp⟩

theorem initialFamily_side_zero (d M : ℕ) :
    sideSensitivity (initialFamily d M) false ≤ d + 2 := by
  apply sideSensitivity_le
  intro q x hx
  have hs : ∀ a b : Fin M, a ≠ b →
      2 * ((d - q.val) + 1) < hammingDist (blockCenter (L := d + 2) a) (blockCenter b) := by
    intro a b hab
    rw [hammingDist_blockCenter a b hab]
    omega
  exact (ballPredicate_sensitivityAt_zero_le blockCenter (d - q.val) hs x hx).trans
    (by omega)

theorem initialFamily_side_one (d M : ℕ) :
    sideSensitivity (initialFamily d M) true ≤ (d + 2) * M := by
  apply sideSensitivity_le
  intro q x _
  simpa [Nat.mul_comm] using sensitivityAt_le_card (initialFamily d M q) x

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveDefinitions ----
namespace OAI

/-! The literal target-row and labeled-gate construction. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem rowClause_eq_true_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    rowClause T label F q x i = true ↔
      (∀ c, F (Fin.last h) (recursiveChild x i c) = true) ∧
      ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) = false := by
  simp only [rowClause, decide_eq_true_eq]

theorem recursiveFamily_eq_false_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    recursiveFamily T label F q x = false ↔ ∀ i, rowClause T label F q x i = false := by
  simp [recursiveFamily]

theorem recursiveFamily_zero {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hr : 0 < r) (hzero : ∀ q, F q (fun _ => false) = false) (q : Fin h) :
    recursiveFamily T label F q (fun _ => false) = false := by
  rw [recursiveFamily_eq_false_iff]
  intro i
  cases hi : rowClause T label F q (fun _ => false) i
  · rfl
  · have ht := ((rowClause_eq_true_iff T label F q (fun _ => false) i).mp hi).1
      (⟨0, hr⟩ : Fin r)
    have hz := hzero (Fin.last h)
    change F (Fin.last h) (fun _ => false) = true at ht
    simp [hz] at ht

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveBlocks ----
namespace OAI

/-! Disjoint zero-input blocks lift to every column of a chosen row. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem rowLift_nonempty {k r : ℕ} {I : Type} (i : Fin k) (B : Finset I)
    (hr : 0 < r) (hB : B.Nonempty) : (rowLift (r := r) i B).Nonempty := by
  obtain ⟨a, ha⟩ := hB
  exact ⟨((i, ⟨0, hr⟩), a), (mem_rowLift i B _).mpr ⟨rfl, ha⟩⟩

theorem rowLift_disjoint_of_ne {k r : ℕ} {I : Type} (i j : Fin k)
    (B C : Finset I) (hij : i ≠ j) : Disjoint (rowLift (r := r) i B) (rowLift j C) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact hij (((mem_rowLift i B p).mp hp).1.symm.trans ((mem_rowLift j C p).mp hq).1)

theorem rowLift_disjoint {k r : ℕ} {I : Type} (i j : Fin k) (B C : Finset I)
    (hBC : Disjoint B C) : Disjoint (rowLift (r := r) i B) (rowLift j C) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact Finset.disjoint_left.mp hBC ((mem_rowLift i B p).mp hp).2
    ((mem_rowLift j C p).mp hq).2

theorem rowLift_family_disjoint {k r : ℕ} {I K : Type} (blocks : K → Finset I)
    (hB : Pairwise fun a b => Disjoint (blocks a) (blocks b)) :
    Pairwise fun a b : Fin k × K =>
      Disjoint (rowLift (r := r) a.1 (blocks a.2)) (rowLift b.1 (blocks b.2)) := by
  intro a b hab
  by_cases hrow : a.1 = b.1
  · apply rowLift_disjoint
    apply hB
    intro hcol
    exact hab (Prod.ext hrow hcol)
  · exact rowLift_disjoint_of_ne _ _ _ _ hrow

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.Tower ----
namespace OAI

/-! An indexed tower of the literal recursive construction and its common blocks. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem tower_block_index_card {k : ℕ} {K : Type} [Fintype K] (n : ℕ) :
    Fintype.card (TowerBlockIndex k K n) = k ^ n * Fintype.card K := by
  induction n with
  | zero =>
    change Fintype.card K = k ^ 0 * Fintype.card K
    simp
  | succ n ih =>
    change Fintype.card (Fin k × TowerBlockIndex k K n) = _
    simp only [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]
    ring

theorem towerBlocks_nonempty {k r : ℕ} {I K : Type} (blocks : K → Finset I)
    (hr : 0 < r) (hne : ∀ b, (blocks b).Nonempty) (n : ℕ) (b : TowerBlockIndex k K n) :
    (towerBlocks (r := r) blocks n b).Nonempty := by
  induction n with
  | zero => exact hne b
  | succ n ih => exact rowLift_nonempty b.1 _ hr (ih b.2)

theorem towerBlocks_pairwise {k r : ℕ} {I K : Type} (blocks : K → Finset I)
    (hd : Pairwise fun a b => Disjoint (blocks a) (blocks b)) (n : ℕ) :
    Pairwise fun a b => Disjoint (towerBlocks (k := k) (r := r) blocks n a) (towerBlocks blocks n b) := by
  induction n with
  | zero => exact hd
  | succ n ih => exact rowLift_family_disjoint (towerBlocks blocks n) ih

theorem towerFamily_zero {k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (hr : 0 < r) (n h : ℕ) (hbase : ∀ q, base (h + n) q (fun _ => false) = false) :
    ∀ q, towerFamily T label base n h q (fun _ => false) = false := by
  induction n generalizing h with
  | zero =>
    change ∀ q, base h q (fun _ => false) = false
    simpa only [Nat.add_zero] using hbase
  | succ n ih =>
    apply recursiveFamily_zero T label _ hr
    apply ih
    have he : (h + 1) + n = h + (n + 1) := by omega
    rw [he]
    exact hbase

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.Composition ----
namespace OAI

/-! Disjoint Boolean composition, with each child retaining its own raw coordinates. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320

variable {I J : Type}

theorem compose_zero (f : (I → Bool) → Bool) (g : (J → Bool) → Bool)
    (hg : g (fun _ => false) = false) :
    compose f g (fun _ => false) = f (fun _ => false) := by
  simp [compose, hg]

section Finite
variable [Fintype I] [Fintype J]

end Finite
end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.Or ----
namespace OAI

/-! Balancing the zero and one sensitivities by an OR of disjoint copies. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320

variable {I K : Type} [Fintype K]

theorem orCopies_zero (f : (I → Bool) → Bool) (hf : f (fun _ => false) = false) :
    orCopies (K := K) f (fun _ => false) = false := by
  rw [orCopies, compose_zero _ _ hf, orBits_zero]

variable [Fintype I]

theorem card_le_blockSensitivityAt_orBits_zero :
    Fintype.card K ≤ blockSensitivityAt (orBits (K := K)) (fun _ => false) := by
  apply le_blockSensitivityAt_of_family orBits (fun _ => false) (fun k : K => {k})
  · intro k
    simp
  · intro k l hkl
    simpa using hkl
  · intro k
    have h : orBits (flip (fun _ : K => false) {k}) = true :=
      (orBits_eq_true _).mpr ⟨k, by simp⟩
    simp [h]

theorem blockSensitivityAt_orCopies_zero (f : (I → Bool) → Bool)
    (hf : f (fun _ => false) = false) :
    Fintype.card K * blockSensitivityAt f (fun _ => false) ≤
      blockSensitivityAt (orCopies (K := K) f) (fun _ => false) := by
  exact (Nat.mul_le_mul_right _ card_le_blockSensitivityAt_orBits_zero).trans
    (blockSensitivityAt_compose_zero_le orBits f hf)

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.Reindex ----
namespace OAI

/-! Coordinate equivalences preserve the two literal Boolean complexity measures. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I J : Type}

theorem flip_reindex (e : I ≃ J) (x : J → Bool) (B : Finset I) :
    (fun i => flip x (B.map e.toEmbedding) (e i)) =
      flip (fun i => x (e i)) B := by
  funext i
  simp [flip]

theorem flip_reindex_singleton (e : I ≃ J) (x : J → Bool) (i : I) :
    (fun a => flip x {e i} (e a)) = flip (fun a => x (e a)) {i} := by
  simpa using flip_reindex e x {i}

section Finite
variable [Fintype I] [Fintype J]

theorem sensitivityAt_reindex (e : I ≃ J) (f : (I → Bool) → Bool) (x : J → Bool) :
    sensitivityAt (reindex e f) x = sensitivityAt f (fun i => x (e i)) := by
  have hs : (Finset.univ.filter fun j =>
      reindex e f (flip x {j}) ≠ reindex e f x).map e.symm.toEmbedding =
      Finset.univ.filter (fun i =>
        f (flip (fun a => x (e a)) {i}) ≠ f (fun a => x (e a))) := by
    ext i
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change f (fun a => flip x {e i} (e a)) ≠ f (fun a => x (e a)) ↔ _
    rw [flip_reindex_singleton]
  simpa only [sensitivityAt, Finset.card_map] using congrArg Finset.card hs

theorem sensitivity_reindex (e : I ≃ J) (f : (I → Bool) → Bool) :
    sensitivity (reindex e f) = sensitivity f := by
  apply Nat.le_antisymm
  · apply sensitivity_le
    intro x
    rw [sensitivityAt_reindex]
    exact sensitivityAt_le_sensitivity f _
  · apply sensitivity_le
    intro x
    have h := sensitivityAt_le_sensitivity (reindex e f) (fun j => x (e.symm j))
    rw [sensitivityAt_reindex] at h
    simpa only [Equiv.symm_apply_apply] using h

theorem blockSensitivityAt_le_reindex (e : I ≃ J) (f : (I → Bool) → Bool)
    (x : J → Bool) :
    blockSensitivityAt f (fun i => x (e i)) ≤ blockSensitivityAt (reindex e f) x := by
  apply blockSensitivityAt_le
  intro blocks hd hb
  have h := le_blockSensitivityAt_of_family (reindex e f) x
    (fun B : blocks => B.val.map e.toEmbedding)
    (fun B => (hb B.val B.property).1.map (f := e.toEmbedding))
    (by
      intro A B hAB
      apply (Finset.disjoint_map e.toEmbedding).mpr
      exact hd A.val A.property B.val B.property (fun h => hAB (Subtype.ext h)))
    (by
      intro B
      change f (fun i => flip x (B.val.map e.toEmbedding) (e i)) ≠ _
      rw [flip_reindex]
      exact (hb B.val B.property).2)
  simpa only [Fintype.card_coe] using h

theorem blockSensitivityAt_reindex (e : I ≃ J) (f : (I → Bool) → Bool)
    (x : J → Bool) :
    blockSensitivityAt (reindex e f) x = blockSensitivityAt f (fun i => x (e i)) := by
  apply Nat.le_antisymm
  · have h := blockSensitivityAt_le_reindex e.symm (reindex e f) (fun i => x (e i))
    simpa only [Equiv.apply_symm_apply, reindex_symm] using h
  · exact blockSensitivityAt_le_reindex e f x

end Finite
end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.Construction ----
namespace OAI

/-! The initial family, recursively constructed predicates, and final OR. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem construction_base_nested (d M : ℕ) :
    NestedFamily (constructionBase d M (d + 1)) := by
  simpa only [constructionBase, baseExtension_same] using initialFamily_nested d M

theorem construction_base_zero (d M : ℕ) :
    ∀ q, constructionBase d M (1 + d) q (fun _ => false) = false := by
  rw [Nat.add_comm 1 d]
  simpa only [constructionBase, baseExtension_same] using initialFamily_zero d M

theorem construction_base_blocks (d M : ℕ) :
    ∀ b q, constructionBase d M (1 + d) q
      (flip (fun _ => false) (baseBlock b)) = true := by
  rw [Nat.add_comm 1 d]
  intro b q
  simpa only [constructionBase, baseExtension_same] using initialFamily_baseBlock d M q b

theorem terminalPredicate_zero {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    terminalPredicate d T A (fun _ => false) = false :=
  towerFamily_zero T.toTournament A.label (constructionBase d M) hr d 1
    (construction_base_zero d M) 0

theorem terminalPredicate_blocks {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r)
    (b : TowerBlockIndex (2 * M ^ 2 + 1) (Fin M) d) :
    terminalPredicate d T A (flip (fun _ => false)
      (towerBlocks (r := r) (baseBlock (L := d + 2)) d b)) = true :=
  towerFamily_blocks T.toTournament A.label (constructionBase d M)
    (baseBlock (L := d + 2)) hr d 1 (construction_base_zero d M)
    (construction_base_blocks d M) b 0

theorem terminalPredicate_blockSensitivity {M r : ℕ} (d : ℕ)
    (T : RegularTournament M) (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    M * (2 * M ^ 2 + 1) ^ d ≤ blockSensitivityAt (terminalPredicate d T A) (fun _ => false) := by
  have h := le_blockSensitivityAt_of_family (terminalPredicate d T A) (fun _ => false)
    (towerBlocks (r := r) (baseBlock (L := d + 2)) d)
    (towerBlocks_nonempty (baseBlock (L := d + 2)) hr
      (baseBlock_nonempty (by omega)) d)
    (towerBlocks_pairwise (baseBlock (L := d + 2)) baseBlock_disjoint d)
    (fun b => by rw [terminalPredicate_blocks d T A hr, terminalPredicate_zero d T A hr]; decide)
  simpa only [tower_block_index_card, Fintype.card_fin, Nat.mul_comm] using h

theorem construction_profiles {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hM : 0 < M) (hr : 0 < r)
    (hbudget : ((max r 16 : ℕ) : ℝ) / M * 3 ^ (d + 1) ≤ 2) :
    ∀ n ≤ d,
      towerSide T.toTournament A.label (constructionBase d M) (d + 1) n false ≤
        2 * (d + 2) * M ^ n ∧
      towerSide T.toTournament A.label (constructionBase d M) (d + 1) n true ≤
        2 * (d + 2) * M ^ (n + 1) := by
  have hstep (n : ℕ) (hn : n < d) := tower_four_recurrences T A (constructionBase d M)
    (d + 1) n (by omega) hr (construction_base_nested d M)
  apply quantitative_profile_bounds d (d + 2) M r hM hbudget
    (towerSide T.toTournament A.label (constructionBase d M) (d + 1))
    (towerJoint T.toTournament A.label (constructionBase d M) (d + 1))
  · simpa only [towerSide_zero, constructionBase, baseExtension_same] using initialFamily_side_zero d M
  · simpa only [towerSide_zero, constructionBase, baseExtension_same] using initialFamily_side_one d M
  · simpa only [towerJoint_zero, constructionBase, baseExtension_same] using initialFamily_joint d M false
  · simpa only [towerJoint_zero, constructionBase, baseExtension_same] using initialFamily_joint d M true
  · exact fun n hn => (hstep n hn).2.2.1
  · exact fun n hn => (hstep n hn).1
  · exact fun n hn => (hstep n hn).2.2.2
  · exact fun n hn => (hstep n hn).2.1

theorem terminalPredicate_sensitivityAt {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hM : 0 < M) (hr : 0 < r)
    (hbudget : ((max r 16 : ℕ) : ℝ) / M * 3 ^ (d + 1) ≤ 2) :
    (∀ x, terminalPredicate d T A x = false →
      sensitivityAt (terminalPredicate d T A) x ≤ 2 * (d + 2) * M ^ d) ∧
    (∀ x, terminalPredicate d T A x = true →
      sensitivityAt (terminalPredicate d T A) x ≤ 2 * (d + 2) * M ^ (d + 1)) := by
  have hs := construction_profiles d T A hM hr hbudget d (le_refl d)
  have he : d + 1 - d = 1 := by omega
  simp only [towerSide] at hs
  rw [he] at hs
  exact ⟨fun x hx => (sensitivityAt_le_sideSensitivity _ false 0 x hx).trans hs.1,
    fun x hx => (sensitivityAt_le_sideSensitivity _ true 0 x hx).trans hs.2⟩

theorem finalBoolean_zero {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    finalBoolean d T A (fun _ => false) = false :=
  orCopies_zero _ (terminalPredicate_zero d T A hr)

theorem finalBoolean_sensitivity {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hM : 0 < M) (hr : 0 < r)
    (hbudget : ((max r 16 : ℕ) : ℝ) / M * 3 ^ (d + 1) ≤ 2) :
    sensitivity (finalBoolean d T A) ≤ 2 * (d + 2) * M ^ (d + 1) := by
  obtain ⟨h₀, h₁⟩ := terminalPredicate_sensitivityAt d T A hM hr hbudget
  have h := sensitivity_orCopies_le (K := Fin M) (terminalPredicate d T A) _ _ h₀ h₁
  have he : M * (2 * (d + 2) * M ^ d) = 2 * (d + 2) * M ^ (d + 1) := by ring
  simpa only [finalBoolean, Fintype.card_fin, he, max_self] using h

theorem finalBoolean_blockSensitivity {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    M ^ 2 * (2 * M ^ 2 + 1) ^ d ≤ blockSensitivityAt (finalBoolean d T A) (fun _ => false) := by
  have h := (Nat.mul_le_mul_left M (terminalPredicate_blockSensitivity d T A hr)).trans
    (by simpa only [Fintype.card_fin] using
      blockSensitivityAt_orCopies_zero (K := Fin M) _ (terminalPredicate_zero d T A hr))
  change M ^ 2 * (2 * M ^ 2 + 1) ^ d ≤ blockSensitivityAt
    (orCopies (K := Fin M) (terminalPredicate d T A)) (fun _ => false)
  calc
    _ = M * (M * (2 * M ^ 2 + 1) ^ d) := by ring
    _ ≤ _ := h

theorem finalWitness_zero {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    finalWitness d T A (fun _ => false) = false := finalBoolean_zero d T A hr

theorem finalWitness_sensitivity {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hM : 0 < M) (hr : 0 < r)
    (hbudget : ((max r 16 : ℕ) : ℝ) / M * 3 ^ (d + 1) ≤ 2) :
    sensitivity (finalWitness d T A) ≤ 2 * (d + 2) * M ^ (d + 1) := by
  rw [finalWitness, sensitivity_reindex]
  exact finalBoolean_sensitivity d T A hM hr hbudget

theorem finalWitness_blockSensitivity {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    M ^ 2 * (2 * M ^ 2 + 1) ^ d ≤ blockSensitivityAt (finalWitness d T A) (fun _ => false) := by
  rw [finalWitness, blockSensitivityAt_reindex]
  exact finalBoolean_blockSensitivity d T A hr

theorem constructionDimension_pos {d M r : ℕ} (hM : 0 < M) (hr : 0 < r) :
    0 < constructionDimension d M r := by
  unfold constructionDimension
  positivity

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.LabelingEvents ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

/-! Exact counts of target-constant label constraints on sixteen vertices. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320.Tournament
variable {k r n : ℕ} (T : Tournament k)

theorem mem_labelingEvent_iff {v : Fin n → Fin k} {m : Fin n → Fin r}
    {A : (Fin k × Fin k) → Fin r} (hv : Function.Injective v) :
    A ∈ T.labelingEvent v m ↔ ∀ i j, T.Adj (v i) (v j) → A (v i,v j) = m j := by
  simp only [labelingEvent, ite_eq_left hv, Finset.mem_filter, Finset.mem_univ, true_and]

theorem labelingEvent_subset_bad {v : Fin n → Fin k} {m : Fin n → Fin r} :
    T.labelingEvent v m ⊆ T.badLabelings n r := by
  intro A hA
  exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ _,
    Finset.mem_biUnion.mpr ⟨m,Finset.mem_univ _,hA⟩⟩

end Paper320.Tournament

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.LabelingBounds ----
namespace OAI

/-! Symbolic estimates for the sixteen-vertex labeling union bound. -/

namespace Paper320

theorem le_ceil_sqrt_sq (M : ℕ) : M ≤ (Nat.ceil (Real.sqrt M))^2 := by
  have hs := Nat.le_ceil (Real.sqrt (M : ℝ))
  have hr := Real.sqrt_nonneg (M : ℝ)
  have he := Real.sq_sqrt (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  have hh : (M : ℝ) ≤ (Nat.ceil (Real.sqrt M) : ℝ)^2 := by nlinarith
  exact_mod_cast hh

theorem labeling_space_large {M : ℕ} (hM : 3 ≤ M) :
    120 ≤ (2*M^2+1)*(2*M^2+1) := by
  have : 19 ≤ 2*M^2+1 := by nlinarith
  nlinarith

end Paper320

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.LabelingEstimate ----
namespace OAI

/-! An explicit numerical union-bound estimate. -/

namespace Paper320

theorem labeling_union_bound_numerator {M r : ℕ} (hM : 3 ≤ M) (hMr : M ≤ r^2) :
    (2*M^2+1)^16 * M^20 ≤ 3^16 * r^104 := by
  have hk : 2*M^2+1 ≤ 3*M^2 := by nlinarith
  have hp : M^52 ≤ r^104 := by
    calc
      M^52 ≤ (r^2)^52 := Nat.pow_le_pow_left hMr 52
      _ = r^104 := by rw [← pow_mul]
  calc
    (2*M^2+1)^16 * M^20 ≤ (3*M^2)^16 * M^20 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hk 16)
    _ = 3^16 * M^52 := by rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add]
    _ ≤ 3^16 * r^104 := Nat.mul_le_mul_left _ hp

theorem labeling_union_bound_constant {M : ℕ} (hM : 3 ≤ M) :
    3^16 < M^20 := by
  calc
    3^16 ≤ M^16 := Nat.pow_le_pow_left hM 16
    _ < M^20 := Nat.pow_lt_pow_right (by omega) (by omega)

theorem labeling_power_bound {M r : ℕ} (hM : 3 ≤ M) (hMr : M ≤ r^2) :
    (2*M^2+1)^16 < r^104 := by
  have hr : 0 < r := (Nat.pow_pos_iff.mp
    (lt_of_lt_of_le (show 0 < M by omega) hMr)).resolve_right (by omega)
  apply Nat.lt_of_mul_lt_mul_right (a := M^20)
  calc
    (2*M^2+1)^16 * M^20 ≤ 3^16*r^104 := labeling_union_bound_numerator hM hMr
    _ < M^20*r^104 := Nat.mul_lt_mul_of_pos_right (labeling_union_bound_constant hM)
      (pow_pos hr 104)
    _ = r^104*M^20 := Nat.mul_comm _ _

end Paper320

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.Labeling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! A finite union bound supplies a good edge labeling. -/

noncomputable section
open scoped Classical

namespace Paper320

namespace Tournament
variable {k r : ℕ} (T : Tournament k)

theorem goodLabeling_exists_of_power_bound (hr : 0 < r) (hN : 120 ≤ k*k)
    (hkr : k^16 < r^104) : Nonempty (GoodLabeling T r) := by
  have htotal : k^16*r^16*r^(k*k-120) < r^(k*k) := by
    calc
      k^16*r^16*r^(k*k-120) < r^104*r^16*r^(k*k-120) :=
        Nat.mul_lt_mul_of_pos_right
          (Nat.mul_lt_mul_of_pos_right hkr (pow_pos hr 16)) (pow_pos hr _)
      _ = r^(104+16+(k*k-120)) := by rw [pow_add, pow_add]
      _ = r^(k*k) := congrArg (fun e : ℕ => r^e) (by omega)
  have hc : (T.badLabelings 16 r).card <
      (Finset.univ : Finset ((Fin k × Fin k) → Fin r)).card := by
    simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
      using (T.card_badLabelings_le (r := r) (n := 16)).trans_lt htotal
  obtain ⟨A,_,hA⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  refine ⟨⟨fun i j => A (i,j), ?_⟩⟩
  intro I hI m
  by_contra hn
  let e : Fin 16 ≃ I := (Finset.equivFinOfCardEq hI).symm
  let v : Fin 16 → Fin k := fun i => (e i).val
  have hv : Function.Injective v := Subtype.val_injective.comp e.injective
  have hevent : A ∈ T.labelingEvent v (fun i => m (v i)) := by
    apply T.mem_labelingEvent_iff hv |>.mpr
    intro i j ha
    by_contra h
    exact hn ⟨v i,(e i).property,v j,(e j).property,ha,h⟩
  apply hA
  exact T.labelingEvent_subset_bad hevent

end Tournament

theorem goodLabeling_exists {M r : ℕ} (hM : 3 ≤ M) (hMr : M ≤ r^2)
    (T : Tournament (2*M^2+1)) : Nonempty (GoodLabeling T r) := by
  have hr : 0 < r := (Nat.pow_pos_iff.mp
    (lt_of_lt_of_le (show 0 < M by omega) hMr)).resolve_right (by omega)
  exact T.goodLabeling_exists_of_power_bound hr (labeling_space_large hM)
    (labeling_power_bound hM hMr)

theorem regular_goodLabeling_exists {M : ℕ} (hM : 3 ≤ M) :
    Nonempty (GoodLabeling (regularCyclicTournament M).toTournament
      (Nat.ceil (Real.sqrt M))) :=
  goodLabeling_exists hM (le_ceil_sqrt_sq M) _

namespace GoodLabeling

end GoodLabeling
end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.ParameterBounds ----
namespace OAI

/-! Uniform numerical estimates for the size parameter. -/

namespace Paper320

theorem parameter_ge_eighty_one {d M : ℕ} (hd : 1 ≤ d) (hM : 9 ^ (d + 1) ≤ M) :
    81 ≤ M := by
  have hp : (9 : ℕ) ^ 2 ≤ 9 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at hp
  exact hp.trans hM

theorem ceil_sqrt_max_le_two_sqrt {M : ℕ} (hM : 81 ≤ M) :
    (max (Nat.ceil (Real.sqrt (M : ℝ))) 16 : ℕ) ≤ 2 * Real.sqrt (M : ℝ) := by
  have hs : (9 : ℝ) ≤ Real.sqrt (M : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact_mod_cast hM
  have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg (M : ℝ))
  push_cast
  exact max_le (by linarith) (by linarith)

theorem parameter_sqrt_lower {d M : ℕ} (hM : 9 ^ (d + 1) ≤ M) :
    (3 : ℝ) ^ (d + 1) ≤ Real.sqrt (M : ℝ) := by
  apply Real.le_sqrt_of_sq_le
  calc
    ((3 : ℝ) ^ (d + 1)) ^ 2 = ((3 : ℝ) ^ 2) ^ (d + 1) := by
      simp only [← pow_mul, Nat.mul_comm]
    _ = (9 : ℝ) ^ (d + 1) := by norm_num
    _ ≤ M := by exact_mod_cast hM

theorem parameter_epsilon_budget {d M : ℕ} (hd : 1 ≤ d) (hM : 9 ^ (d + 1) ≤ M) :
    ((max (Nat.ceil (Real.sqrt (M : ℝ))) 16 : ℕ) : ℝ) / M * 3 ^ (d + 1) ≤ 2 := by
  have h81 := parameter_ge_eighty_one hd hM
  have hpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hm := ceil_sqrt_max_le_two_sqrt h81
  have hp := parameter_sqrt_lower hM
  calc
    _ ≤ (2 * Real.sqrt (M : ℝ)) / M * Real.sqrt (M : ℝ) :=
      mul_le_mul (div_le_div_of_nonneg_right hm hpos.le) hp (by positivity) (by positivity)
    _ = 2 := by
      field_simp
      nlinarith [Real.sq_sqrt hpos.le]

end Paper320

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.Iterates ----
namespace OAI

/-! Repeated disjoint composition with explicit finite raw-coordinate types. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I : Type} [Fintype I]

theorem nonconstant_of_blockSensitivityAt_pos (f : (I → Bool) → Bool) (x : I → Bool)
    (h : 0 < blockSensitivityAt f x) : ∃ y z, f y ≠ f z := by
  obtain ⟨blocks, hc, _, hb⟩ := exists_blockSensitivityAt_family f x
  have hn : blocks.Nonempty := Finset.card_pos.mp (hc.symm ▸ h)
  obtain ⟨B, hB⟩ := hn
  exact ⟨flip x B, x, (hb B hB).2⟩

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.ConstructedSeed ----
namespace OAI

/-! All construction parameters and labels are supplied unconditionally. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem construction_label_count_pos {M : ℕ} (hM : 0 < M) :
    0 < Nat.ceil (Real.sqrt (M : ℝ)) := by
  have h := le_ceil_sqrt_sq M
  by_contra hn
  have he : Nat.ceil (Real.sqrt (M : ℝ)) = 0 := by omega
  rw [he] at h
  norm_num at h
  omega

theorem exists_constructed_seed (d M : ℕ) (hd : 1 ≤ d) (hM : 9 ^ (d + 1) ≤ M) :
    ∃ f : (Fin (constructionDimension d M (Nat.ceil (Real.sqrt (M : ℝ)))) → Bool) → Bool,
      0 < constructionDimension d M (Nat.ceil (Real.sqrt (M : ℝ))) ∧
      f (fun _ => false) = false ∧ (∃ x y, f x ≠ f y) ∧
      sensitivity f ≤ 2 * (d + 2) * M ^ (d + 1) ∧
      M ^ 2 * (2 * M ^ 2 + 1) ^ d ≤ blockSensitivityAt f (fun _ => false) := by
  have h81 := parameter_ge_eighty_one hd hM
  have hMp : 0 < M := by omega
  have hr := construction_label_count_pos hMp
  obtain ⟨A⟩ := regular_goodLabeling_exists (show 3 ≤ M by omega)
  let f := finalWitness d (regularCyclicTournament M) A
  have hs := finalWitness_sensitivity d (regularCyclicTournament M) A hMp hr
    (parameter_epsilon_budget hd hM)
  have hb := finalWitness_blockSensitivity d (regularCyclicTournament M) A hr
  have hbp : 0 < M ^ 2 * (2 * M ^ 2 + 1) ^ d := by positivity
  have hnc := nonconstant_of_blockSensitivityAt_pos f (fun _ => false) (hbp.trans_le hb)
  exact ⟨f, constructionDimension_pos hMp hr,
    finalWitness_zero d (regularCyclicTournament M) A hr, hnc, hs, hb⟩

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.SeparationArithmetic ----
namespace OAI

/-! The exact final ratio, the depth-nine seed gap, and exponential divergence. -/

noncomputable section
open Filter
open scoped Topology

namespace Paper320

theorem seed_ratio_identity (d : ℕ) {L M k : ℝ} (hL : L ≠ 0) (hM : M ≠ 0) :
    (M ^ 2 * k ^ d) / (2 * L * M ^ (d + 1)) ^ 2 =
      (k / M ^ 2) ^ d / (4 * L ^ 2) := by
  have hp : (M ^ 2) ^ d = (M ^ d) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 d]
  rw [div_pow, hp, pow_succ]
  field_simp
  ring

theorem seed_ratio_lower (d : ℕ) {M : ℝ} (hM : 0 < M) :
    (2 : ℝ) ^ d / (4 * ((d : ℝ) + 2) ^ 2) ≤
      (M ^ 2 * (2 * M ^ 2 + 1) ^ d) /
        (2 * ((d : ℝ) + 2) * M ^ (d + 1)) ^ 2 := by
  rw [seed_ratio_identity d (by positivity) (ne_of_gt hM)]
  have hk : 2 ≤ (2 * M ^ 2 + 1) / M ^ 2 := by
    apply (le_div_iff₀ (pow_pos hM 2)).mpr
    linarith
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hk d) (by positivity)

theorem ratio_of_bounds {I : Type} [Fintype I] (f : (I → Bool) → Bool)
    (s b : ℝ) (hpos : 0 < (sensitivity f : ℝ))
    (hs : (sensitivity f : ℝ) ≤ s) (hb : b ≤ (blockSensitivityAt f (fun _ => false) : ℝ))
    (hb0 : 0 ≤ b) :
    b / s ^ 2 ≤ (blockSensitivity f : ℝ) / (sensitivity f : ℝ) ^ 2 := by
  have hsp : 0 < s := lt_of_lt_of_le hpos hs
  apply (le_div_iff₀ (pow_pos hpos 2)).mpr
  calc
    _ ≤ (b / s ^ 2) * s ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos.le hs 2) (div_nonneg hb0 (sq_nonneg s))
    _ = b := div_mul_cancel₀ _ (ne_of_gt (pow_pos hsp 2))
    _ ≤ (blockSensitivityAt f (fun _ => false) : ℝ) := hb
    _ ≤ (blockSensitivity f : ℝ) := by
      exact_mod_cast blockSensitivityAt_le_blockSensitivity f (fun _ => false)

theorem quantitative_ratio_of_bounds {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (d M : ℕ) (hM : 0 < M)
    (hnc : ∃ x y, f x ≠ f y)
    (hs : sensitivity f ≤ 2 * (d + 2) * M ^ (d + 1))
    (hb : M ^ 2 * (2 * M ^ 2 + 1) ^ d ≤ blockSensitivityAt f (fun _ => false)) :
    (2 : ℝ) ^ d / (4 * ((d : ℝ) + 2) ^ 2) ≤
      (blockSensitivity f : ℝ) / (sensitivity f : ℝ) ^ 2 := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  apply (seed_ratio_lower d hMr).trans
  apply ratio_of_bounds
  · exact_mod_cast sensitivity_pos_of_nonconstant f hnc
  · exact_mod_cast hs
  · exact_mod_cast hb
  · positivity

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.Separation ----
namespace OAI

/-! Quantitative, unbounded quadratic, and fixed-power separations of sensitivity. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem quantitative_separation (d : ℕ) (hd : 1 ≤ d) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      0 < n ∧ f (fun _ => false) = false ∧
      (∃ x y : Fin n → Bool, f x ≠ f y) ∧
      (2 : ℝ) ^ d / (4 * ((d : ℝ) + 2) ^ 2) ≤
        (blockSensitivity f : ℝ) / (sensitivity f : ℝ) ^ 2 := by
  let M : ℕ := 9 ^ (d + 1)
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨f, hn, hf, hnc, hs, hb⟩ := exists_constructed_seed d M hd (by rfl)
  exact ⟨_, f, hn, hf, hnc, quantitative_ratio_of_bounds f d M hM hnc hs hb⟩

end Paper320

end

end OAI

-- ---- mission target ----
open OAI OAI.Paper320
open scoped Classical

theorem solution (d : ℕ) (hd : 1 ≤ d) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      0 < n ∧ f (fun _ => false) = false ∧
      (∃ x y : Fin n → Bool, f x ≠ f y) ∧
      (2 : ℝ) ^ d / (4 * ((d : ℝ) + 2) ^ 2) ≤
        (blockSensitivity f : ℝ) / (sensitivity f : ℝ) ^ 2 := by
  first
    | exact OAI.Paper320.quantitative_separation d hd
    | exact OAI.Paper320.quantitative_separation
    | (apply OAI.Paper320.quantitative_separation <;> assumption)
    | (intros; apply OAI.Paper320.quantitative_separation <;> assumption)
