-- Prove2me | solution 1 for GlobalTheory.siegel_eq_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:45:23.613004+00:00
-- url     : https://prove2.me/submissions/7cf4b7e6-b382-440d-920d-74c7c9b45d58

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FiniteAbsLeOneMulMemRange
import Theorems.Thm_GlobalTheory_fderiv_vecMulVec_eq_zero
import Theorems.Thm_GlobalTheory_IsSiegel_smul
import Theorems.Thm_GlobalTheory_convex_phDom
import Theorems.Thm_GlobalTheory_isOpen_phDom
import Theorems.Thm_GlobalTheory_of_symm_mem_phDom
import Theorems.Thm_GlobalTheory_phSym_eq_self_of_isSymm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_rkU_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology
open GlobalTheory
variable {g : ℕ} {H : Matrix (Fin g) (Fin g) ℂ → ℂ}
namespace GlobalTheory
theorem _root_.solution (hol : IsHoloSiegel g H) (hH : IsSpInvariant g H)
    (hb : ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ τ ∈ SiegelH (Fin g),
      (τ.map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ‖H τ‖ ≤ K)
    {τ σ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) (hσ : σ ∈ SiegelH (Fin g)) :
    H τ = H σ := by
  have key : ∀ τ ∈ SiegelH (Fin g), ∀ V : Matrix (Fin g) (Fin g) ℂ, V.IsSymm →
      fderiv ℂ (fun x : Fin g → Fin g → ℂ => H (phSym (of x))) (of.symm τ) (of.symm V) = 0 := by
    intro τ hτ V hV
    set L := fderiv ℂ (fun x : Fin g → Fin g → ℂ => H (phSym (of x))) (of.symm τ) with hL
    let M : Matrix (Fin g) (Fin g) ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun S => L (of.symm (imC τ * S * (imC τ)ᵀ))
        map_add' := fun S T => by
          rw [Matrix.mul_add, Matrix.add_mul]
          exact L.map_add _ _
        map_smul' := fun c S => by
          rw [Matrix.mul_smul, Matrix.smul_mul]
          exact L.map_smul _ _ }
    have hM : ∀ (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) (e : Fin g),
        M (vecMulVec (fun l => (U.val e l : ℂ)) fun l => (U.val e l : ℂ)) = 0 := by
      intro U e
      rw [← fderiv_vecMulVec_eq_zero hol hH hb U e hτ]
      change L _ = L _
      rw [mul_vecMulVec, vecMulVec_mul, vecMul_transpose]
    have h1 : ∀ i, M (single i i 1) = 0 := fun i => by
      rw [← hM 1 i]
      congr 1
      ext a b
      simp [vecMulVec_apply, single_apply, one_apply, ite_and]
      split_ifs <;> rfl
    have h2 : ∀ i j, M (single i j 1) + M (single j i 1) = 0 := fun i j => by
      by_cases hij : i = j
      · simp [hij, h1]
      have h := hM (rkU (Pi.single i 1) (Pi.single j 1) (by simp [hij])) i
      have e : (vecMulVec (fun l => ((rkU (Pi.single i 1) (Pi.single j 1)
          (by simp [hij])).val i l : ℂ)) fun l => ((rkU (Pi.single i 1) (Pi.single j 1)
          (by simp [hij])).val i l : ℂ)) =
          single i i 1 + single j j 1 + (single i j 1 + single j i 1) := by
        ext a b
        simp only [rkU_val, vecMulVec_apply, single_apply, one_apply, ite_and, Matrix.add_apply,
          Pi.single_apply, eq_comm (b := j)]
        split_ifs <;> norm_num
      rwa [e, map_add, map_add, map_add, h1, h1, zero_add, zero_add] at h
    have h3 : ∀ S : Matrix (Fin g) (Fin g) ℂ, S.IsSymm → M S = 0 := fun S hS => by
      have e1 : M S = ∑ i, ∑ j, S i j * M (single i j 1) := by
        conv_lhs => rw [matrix_eq_sum_single S]
        simp only [map_sum, ← smul_eq_mul, ← map_smul, smul_single]
        simp
      have e2 : M S = ∑ i, ∑ j, S i j * M (single j i 1) := by
        rw [e1, Finset.sum_comm]
        simp only [hS.apply]
      have : M S + M S = 0 := by
        nth_rw 1 [e1]
        simp only [e2, ← Finset.sum_add_distrib, ← mul_add, h2, mul_zero, Finset.sum_const_zero]
      linear_combination (1 / 2 : ℂ) * this
    have hu : IsUnit (imC τ).det := by
      have : imC τ = Complex.ofRealHom.mapMatrix (τ.map Complex.im) := rfl
      rw [this, ← RingHom.map_det]
      exact hτ.2.det_pos.ne'.isUnit.map _
    have h4 := h3 ((imC τ)⁻¹ * V * ((imC τ)⁻¹)ᵀ) (by
      simp only [IsSymm, transpose_mul, transpose_transpose, hV.eq, Matrix.mul_assoc])
    rw [← h4]
    change L _ = L _
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← transpose_mul, mul_nonsing_inv _ hu, transpose_one,
      Matrix.mul_one, mul_nonsing_inv_cancel_left _ _ hu]
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, τ + (t : ℂ) • (σ - τ) ∈ SiegelH (Fin g) := fun t ht => by
    have h : phSym _ ∈ SiegelH (Fin g) := (convex_phDom g).add_smul_sub_mem
      (of_symm_mem_phDom hτ) (of_symm_mem_phDom hσ) ht
    rwa [← phSym_eq_self_of_isSymm (hτ.1.add ((hσ.1.sub hτ.1).smul (t : ℂ)))]
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ =>
      H (phSym (of (of.symm τ + (t : ℂ) • of.symm (σ - τ))))) 0 t := fun t ht => by
    have h1 : HasDerivAt (fun s : ℂ => (of.symm τ + s • of.symm (σ - τ) : Fin g → Fin g → ℂ))
        (of.symm (σ - τ)) t := by
      simpa using ((hasDerivAt_id (t : ℂ)).smul_const
        (of.symm (σ - τ) : Fin g → Fin g → ℂ)).const_add (of.symm τ)
    have h2 := (hol.differentiableAt ((isOpen_phDom g).mem_nhds
      (of_symm_mem_phDom (hmem t ht)))).hasFDerivAt.comp_hasDerivAt_of_eq (t : ℂ) h1 rfl
    rw [key _ (hmem t ht) _ (hσ.1.sub hτ.1)] at h2
    exact h2.comp_ofReal
  have h := constant_of_has_deriv_right_zero
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt) 1 (by simp)
  simp only [ofReal_one, ofReal_zero, one_smul, zero_smul, add_zero, Equiv.apply_symm_apply,
    phSym_eq_self_of_isSymm hτ.1] at h
  have e : of (of.symm τ + of.symm (σ - τ)) = σ := add_sub_cancel τ σ
  rw [← h, e, phSym_eq_self_of_isSymm hσ.1]
end GlobalTheory
