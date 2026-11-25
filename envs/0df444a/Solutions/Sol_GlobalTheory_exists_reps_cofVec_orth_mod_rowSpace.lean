-- Prove2me | solution 1 for GlobalTheory.exists_reps_cofVec_orth_mod_rowSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:35:04.892811+00:00
-- url     : https://prove2.me/submissions/a0d24a8e-3dfd-4a25-9709-1ea8cdd19582

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MinorSmulEqRowSpaceOfCofVecOrth
import Theorems.Thm_GlobalTheory_minor_smul_eq_rowSpace_of_cofVec_orth
import Theorems.Thm_GlobalTheory_exists_reps_ideal_inv_lattice
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (S0 B : Submodule (𝓞 K) V) (I : Ideal (𝓞 K)) (r s : ℕ) (Y : Matrix (Fin r) (Fin (r + 1)) (𝓞 K)) (b₀ : Fin (r + 1)), S0.FG → finrank K (Submodule.span K (S0 : Set V)) = s → I ≠ ⊥ → I • B ≤ S0 → (Y.submatrix id b₀.succAbove).det ≠ 0 → ∃ reps : Finset (Fin (r + 1) → V), reps.card ≤ Ideal.absNorm (Ideal.span {(Y.submatrix id b₀.succAbove).det} * I) ^ (s * r) ∧ ∀ u : Fin (r + 1) → V, (∀ b, u b ∈ B) → ∑ b, Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec Y b • u b = 0 → ∃ u₀ ∈ reps, ∃ v : Fin r → V, (∀ a, v a ∈ S0) ∧ ∀ b, u b = u₀ b + ∑ a, Y a b • v a := by
  intro K V _ _ _ _ _ _ _ _ S0 B I r s Y b₀ hS hs hI hIB hd
  classical
  set d := (Y.submatrix id b₀.succAbove).det with hd_def
  have hJ : Ideal.span {d} * I ≠ ⊥ := by
    refine mul_ne_zero ?_ hI
    simpa using hd
  obtain ⟨R, hR, hrep⟩ := exists_reps_ideal_inv_lattice K V S0 _ hS hJ
  rw [hs] at hR
  have hdK : algebraMap (𝓞 K) K d ≠ 0 := fun h =>
    hd (IsFractionRing.injective (𝓞 K) K (by simpa using h))
  refine ⟨(Fintype.piFinset fun _ : Fin r => R).image (fun w b => ∑ a, Y a b • w a), ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    exact Nat.pow_le_pow_left hR r
  · intro u huB hu
    let w : Fin r → V := fun a =>
      ∑ c, (Y.submatrix id b₀.succAbove).adjugate c a • u (b₀.succAbove c)
    have hwB : ∀ a, w a ∈ B := fun a =>
      B.sum_mem fun c _ => B.smul_mem _ (huB _)
    let v' : Fin r → V := fun a => (algebraMap (𝓞 K) K d)⁻¹ • w a
    have hdv : ∀ a, d • v' a = w a := fun a => by
      rw [← algebraMap_smul K d, smul_inv_smul₀ hdK]
    have huv : ∀ b, u b = ∑ a, Y a b • v' a := by
      intro b
      have h := minor_smul_eq_rowSpace_of_cofVec_orth K V r Y b₀ u hu b
      apply smul_right_injective V hdK
      simp only [algebraMap_smul]
      rw [h, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_comm d, hdv]
    have hv' : ∀ a, ∀ j ∈ Ideal.span {d} * I, j • v' a ∈ S0 := by
      intro a j hj
      obtain ⟨i, hi, rfl⟩ := Ideal.mem_span_singleton_mul.mp hj
      rw [mul_comm, mul_smul, hdv]
      exact hIB (Submodule.smul_mem_smul hi (hwB a))
    choose y hyR hy using fun a => hrep (v' a) (hv' a)
    refine ⟨_, Finset.mem_image_of_mem _ (Fintype.mem_piFinset.mpr hyR), fun a => v' a - y a, hy, ?_⟩
    intro b
    rw [huv b, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← smul_add, add_sub_cancel]
end GlobalTheory
