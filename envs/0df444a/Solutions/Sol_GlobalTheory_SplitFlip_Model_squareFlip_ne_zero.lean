-- Prove2me | solution 1 for GlobalTheory.SplitFlip.Model.squareFlip_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:32:51.416667+00:00
-- url     : https://prove2.me/submissions/ae3e7b8e-148c-4524-957a-0b687942d6f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OmAUnipFourierInv
import Theorems.Thm_GlobalTheory_SplitFlip_Model_isPrimFrame_mul
import Theorems.Thm_GlobalTheory_SplitFlip_Model_sum_invFourierSum
import Theorems.Thm_GlobalTheory_SplitFlip_apow_ne_zero
import Theorems.Thm_GlobalTheory_SplitFlip_fourierSum_apply
import Theorems.Thm_GlobalTheory_SplitFlip_frameMatrixFirstColumnBlock_mul_apply
import Theorems.Thm_GlobalTheory_SplitFlip_glLat_stdLat
import Theorems.Thm_GlobalTheory_SplitFlip_isPrimitiveFrame_standardBasis
import Theorems.Thm_GlobalTheory_SplitFlip_latA_blockLat
import Theorems.Thm_GlobalTheory_SplitFlip_smallF_of_isEmpty
import Theorems.Thm_GlobalTheory_SplitFlip_splitTheta_fFun_frameFirstBlock_mul
import Theorems.Thm_GlobalTheory_SplitFlip_vecMul_blockScale_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Model
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitFlip.Model
theorem _root_.solution [IsEmpty A'] {ϖ : kˣ} (hϖ : IsUnif ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    {e : ℕ} (he : 1 ≤ e) (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) (P : Finset D) (Φ : Matrix A' D k → ℂ) (hΦ : Φ 0 ≠ 0) :
    squareFlip (haarVol (KO k A')) σ ψ ν ϖ e P Φ ≠ 0 := by
  classical
  intro H
  have hψ' : HasConductor ψ⁻¹ 1 := fun x => by simpa only [AddChar.inv_apply', inv_eq_one] using hψ x
  let I := IsLocalRing.maximalIdeal 𝒪[k] ^ e
  let K : Matrix D D 𝒪[k] := Matrix.of fun r j =>
    if j ∈ Pᶜ then Quotient.out (Ideal.Quotient.mk I ((1 : Matrix D D 𝒪[k]) r j)) else (1 : Matrix D D 𝒪[k]) r j
  have hK : IsUnit K := by
    rw [Matrix.isUnit_iff_isUnit_det, ← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have : (IsLocalRing.residue 𝒪[k]).mapMatrix K = (IsLocalRing.residue 𝒪[k]).mapMatrix 1 := by
      ext r j
      simp only [RingHom.mapMatrix_apply, map_apply, K, of_apply]
      split_ifs
      · exact Ideal.Quotient.eq.2 (Ideal.pow_le_self (by omega) (Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out _)))
      · rfl
    rw [this]; simp
  obtain ⟨u, hu⟩ := hK
  let g : GL D k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u * blockScale ϖ e Pᶜ
  have hg : ∀ x, x ᵥ* g.val ∈ blockLat ϖ e Pᶜ ↔ x ∈ stdLat k D := fun x => by
    rw [Units.val_mul, ← vecMul_vecMul, vecMul_blockScale_mem]
    exact (show _ ∈ glLat (stdLat k D) from glLat_stdLat (k := k) (D := D) ▸ ⟨u, rfl⟩) x
  have hprim := isPrimFrame_mul (isPrimitiveFrame_standardBasis σ) g hg
  let S₀ : A → ↥(Pᶜ) → Res k e := fun i j => Ideal.Quotient.mk I ((1 : Matrix D D 𝒪[k]) (σ (.inl i)) j)
  have hX : setCols Pᶜ (X0 k σ * g.val) ((ϖ ^ e)⁻¹ • liftRes S₀) = X0 k σ * g.val := by
    ext i j
    by_cases h : j ∈ Pᶜ
    · rw [frameMatrixFirstColumnBlock_mul_apply]
      simp only [setCols, of_apply, dif_pos h, g, Units.val_mul, blockScale, diagGL_val, mul_diagonal, blockUnits,
        if_pos h]
      show _ = ((u.val (σ (.inl i)) j : 𝒪[k]) : k) * _
      rw [hu]
      simp only [K, of_apply, if_pos h, Matrix.smul_apply, liftRes, S₀, Units.smul_def, smul_eq_mul]
      ring
    · simp only [setCols, of_apply, dif_neg h]
  have h5 := sum_invFourierSum hϖ hψ' e Pᶜ (phiA (haarVol (KO k A')) σ ν ϖ e (blockLat ϖ e P) (fourierSum ψ ϖ e P Φ))
    (X0 k σ * g.val) S₀
  rw [squareFlip] at H
  rw [H, hX, phiA, latA_blockLat, if_pos hprim, ← invT_invT g, splitTheta_fFun_frameFirstBlock_mul, smallF_of_isEmpty] at h5
  have h6 : fourierSum ψ ϖ e P Φ 0 = Φ 0 := by
    have h : ∀ T, setCols P (0 : Matrix A' D k) T = 0 := fun T => Subsingleton.elim _ _
    simp [fourierSum_apply, h, pairCols]
  rw [h6] at h5
  simp [hΦ, apow_ne_zero] at h5
end GlobalTheory.SplitFlip.Model
