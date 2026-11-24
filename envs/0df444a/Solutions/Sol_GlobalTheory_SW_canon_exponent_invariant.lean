-- Prove2me | solution 1 for GlobalTheory.SW.canon_exponent_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:30:33.126776+00:00
-- url     : https://prove2.me/submissions/3914e51b-b3a7-4230-b60e-bec47d3f9caa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CanonicalThetaExponentSymplecticInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
namespace GlobalTheory.SW
open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_add' {α β : Type} (M N : Matrix α β ℚ) :
    _root_.GlobalTheory.SW.qm (M + N) = _root_.GlobalTheory.SW.qm M + _root_.GlobalTheory.SW.qm N := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm]
open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_neg' {α β : Type} (M : Matrix α β ℚ) :
    _root_.GlobalTheory.SW.qm (-M) = -_root_.GlobalTheory.SW.qm M := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm]
open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_mul_siegel_theta_transformation {α β γ : Type} [Fintype β] (M : Matrix α β ℚ) (N : Matrix β γ ℚ) :
    _root_.GlobalTheory.SW.qm (M * N) = _root_.GlobalTheory.SW.qm M * _root_.GlobalTheory.SW.qm N := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm, Matrix.mul_apply]
open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_transpose' {α β : Type} (M : Matrix α β ℚ) :
    _root_.GlobalTheory.SW.qm Mᵀ = (_root_.GlobalTheory.SW.qm M)ᵀ := rfl
open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_zero' {α β : Type} : _root_.GlobalTheory.SW.qm (0 : Matrix α β ℚ) = 0 := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm]
open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_one' : _root_.GlobalTheory.SW.qm (1 : Matrix ι ι ℚ) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [_root_.GlobalTheory.SW.qm, one_apply, h]
open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma sub_conjTranspose_of_isSymm (τ : Matrix ι ι ℂ) (hτ : τ.IsSymm) :
    τ - τᴴ = (2 * I) • τ.map fun z => (z.im : ℂ) := by
  ext i j
  have h := hτ.apply i j
  simp only [Matrix.sub_apply, conjTranspose_apply, Matrix.smul_apply, map_apply, smul_eq_mul, h]
  rw [show star (τ i j) = conj (τ i j) from rfl, Complex.sub_conj]
  push_cast
  ring
open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_conjTranspose_eq_transpose {α β : Type} (M : Matrix α β ℚ) :
    (_root_.GlobalTheory.SW.qm M)ᴴ = (_root_.GlobalTheory.SW.qm M)ᵀ := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm, conjTranspose_apply]
open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma re_star_dotProduct_ofReal_mulVec (Y : Matrix ι ι ℝ) (v : ι → ℂ) :
    (star v ⬝ᵥ (Y.map (fun t => (t : ℂ)) *ᵥ v)).re =
      (fun i => (v i).re) ⬝ᵥ (Y *ᵥ fun i => (v i).re) + (fun i => (v i).im) ⬝ᵥ (Y *ᵥ fun i => (v i).im) := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Complex.re_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.mul_re, Complex.mul_im]
open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma dotProduct_transpose_mulVec_self (N : Matrix ι ι ℂ) (ζ : ι → ℂ) :
    ζ ⬝ᵥ (Nᵀ *ᵥ ζ) = ζ ⬝ᵥ (N *ᵥ ζ) := by
  rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec]
end GlobalTheory.SW
end

set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW
open Matrix Complex
open scoped ComplexConjugate Real
namespace GlobalTheory.SW
namespace _root_.GlobalTheory.SW
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∀ τ ∈ _root_.GlobalTheory.SW.Siegel ι, ∀ ζ : ι → ℂ, (ζ ᵥ* (_root_.GlobalTheory.SW.spDen σ τ)⁻¹) ⬝ᵥ ((_root_.GlobalTheory.SW.spAct σ τ).map fun z => (z.im : ℂ))⁻¹ *ᵥ (ζ ᵥ* (_root_.GlobalTheory.SW.spDen σ τ)⁻¹) + 2 * I * (ζ ⬝ᵥ ((_root_.GlobalTheory.SW.spDen σ τ)⁻¹ * _root_.GlobalTheory.SW.qm σ.toBlocks₂₁) *ᵥ ζ) = ζ ⬝ᵥ (τ.map fun z => (z.im : ℂ))⁻¹ *ᵥ ζ := by
  intro ι _ _ σ hσ τ hτ ζ
  obtain ⟨hsym, hpos⟩ := hτ
  have h2 := SymplecticGroup.mem_iff'.mp hσ
  rw [← fromBlocks_toBlocks σ] at h2
  simp [Matrix.J, fromBlocks_transpose, fromBlocks_multiply] at h2
  obtain ⟨r1, r2, r3, r4⟩ := h2
  replace r1 := congrArg _root_.GlobalTheory.SW.qm r1
  replace r2 := congrArg _root_.GlobalTheory.SW.qm r2
  replace r3 := congrArg _root_.GlobalTheory.SW.qm r3
  replace r4 := congrArg _root_.GlobalTheory.SW.qm r4
  simp only [qm_add', qm_neg', qm_mul_siegel_theta_transformation, qm_transpose',
    qm_zero', qm_one'] at r1 r2 r3 r4
  set A := _root_.GlobalTheory.SW.qm σ.toBlocks₁₁ with hA
  set B := _root_.GlobalTheory.SW.qm σ.toBlocks₁₂ with hB
  set C := _root_.GlobalTheory.SW.qm σ.toBlocks₂₁ with hC
  set D := _root_.GlobalTheory.SW.qm σ.toBlocks₂₂ with hD
  set J := _root_.GlobalTheory.SW.spDen σ τ with hJdef
  have hJ : J = C * τ + D := rfl
  set M := A * τ + B with hM
  have hact : _root_.GlobalTheory.SW.spAct σ τ = M * J⁻¹ := rfl
  set Y := τ.map fun z => (z.im : ℂ) with hYdef
  have hY : τ - τᴴ = (2 * I) • Y := sub_conjTranspose_of_isSymm τ hsym
  have hτt : τᵀ = τ := hsym
  have hCh : Cᴴ = Cᵀ := qm_conjTranspose_eq_transpose _
  have hDh : Dᴴ = Dᵀ := qm_conjTranspose_eq_transpose _
  have hAh : Aᴴ = Aᵀ := qm_conjTranspose_eq_transpose _
  have hBh : Bᴴ = Bᵀ := qm_conjTranspose_eq_transpose _
  have hI1 : Jᴴ * M - Mᴴ * J = τ - τᴴ := by
    rw [hJ, hM, conjTranspose_add, conjTranspose_add, conjTranspose_mul, conjTranspose_mul, hCh, hDh, hAh, hBh]
    have hE : (τᴴ * Cᵀ + Dᵀ) * (A * τ + B) - (τᴴ * Aᵀ + Bᵀ) * (C * τ + D) =
        τᴴ * (Cᵀ * A + -(Aᵀ * C)) * τ + τᴴ * (Cᵀ * B + -(Aᵀ * D)) + (Dᵀ * A + -(Bᵀ * C)) * τ +
          (Dᵀ * B + -(Bᵀ * D)) := by noncomm_ring
    rw [hE, r1, r2, r3, r4]
    noncomm_ring
  have hI2 : Mᵀ * J = Jᵀ * M := by
    rw [hJ, hM, transpose_add, transpose_add, transpose_mul, transpose_mul, hτt]
    have hE : (τ * Aᵀ + Bᵀ) * (C * τ + D) - (τ * Cᵀ + Dᵀ) * (A * τ + B) =
        -(τ * (Cᵀ * A + -(Aᵀ * C)) * τ) - τ * (Cᵀ * B + -(Aᵀ * D)) - (Dᵀ * A + -(Bᵀ * C)) * τ -
          (Dᵀ * B + -(Bᵀ * D)) := by noncomm_ring
    rw [r1, r2, r3, r4] at hE
    rw [← sub_eq_zero, hE]
    noncomm_ring
  have hYr : Y = (τ.map Complex.im).map (fun t => (t : ℂ)) := rfl
  have hdetY : Y.det ≠ 0 := by
    have : Y.det = ((τ.map Complex.im).det : ℂ) := by
      rw [hYr]
      exact (RingHom.map_det Complex.ofRealHom _).symm
    rw [this, Complex.ofReal_ne_zero]
    exact hpos.det_pos.ne'
  have h2I : (2 * I : ℂ) ≠ 0 := by simp
  have hdetJ : J.det ≠ 0 := by
    intro hdet
    obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have h0 : star v ⬝ᵥ ((Jᴴ * M - Mᴴ * J) *ᵥ v) = 0 := by
      rw [sub_mulVec, dotProduct_sub, ← mulVec_mulVec, ← mulVec_mulVec, hJv, mulVec_zero,
        dotProduct_zero, dotProduct_mulVec, ← star_mulVec, hJv, star_zero, zero_dotProduct, sub_zero]
    rw [hI1, hY, smul_mulVec, dotProduct_smul, smul_eq_mul, mul_eq_zero] at h0
    have h1 := congrArg Complex.re (h0.resolve_left h2I)
    rw [hYr, re_star_dotProduct_ofReal_mulVec, Complex.zero_re] at h1
    have hna := hpos.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).re)
    have hnb := hpos.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).im)
    simp only [star_trivial] at hna hnb
    have ha : (fun i => (v i).re) = 0 := by
      by_contra h
      have := hpos.dotProduct_mulVec_pos h
      simp only [star_trivial] at this
      linarith
    have hb : (fun i => (v i).im) = 0 := by
      by_contra h
      have := hpos.dotProduct_mulVec_pos h
      simp only [star_trivial] at this
      linarith
    apply hv
    funext i
    apply Complex.ext
    · simpa using congrFun ha i
    · simpa using congrFun hb i
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.mpr hdetJ
  have hYu : IsUnit Y.det := isUnit_iff_ne_zero.mpr hdetY
  have hJJ : J * J⁻¹ = 1 := mul_nonsing_inv J hJu
  have hJJ' : J⁻¹ * J = 1 := nonsing_inv_mul J hJu
  have hYY : Y⁻¹ * Y = 1 := nonsing_inv_mul Y hYu
  have hτ'sym : (M * J⁻¹).IsSymm := by
    have hJtu : IsUnit Jᵀ.det := by rwa [det_transpose]
    unfold Matrix.IsSymm
    rw [transpose_mul, transpose_nonsing_inv]
    calc (Jᵀ)⁻¹ * Mᵀ = (Jᵀ)⁻¹ * (Mᵀ * J) * J⁻¹ := by simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = M * J⁻¹ := by rw [hI2, ← Matrix.mul_assoc (Jᵀ)⁻¹, nonsing_inv_mul _ hJtu, Matrix.one_mul]
  set Y' := (_root_.GlobalTheory.SW.spAct σ τ).map fun z => (z.im : ℂ) with hY'def
  have hY' : (2 * I) • Y' = M * J⁻¹ - (M * J⁻¹)ᴴ := by
    rw [hY'def, hact]
    exact (sub_conjTranspose_of_isSymm _ hτ'sym).symm
  have hkey : Jᴴ * Y' * J = Y := by
    apply smul_right_injective _ h2I
    calc (2 * I) • (Jᴴ * Y' * J) = Jᴴ * ((2 * I) • Y') * J := by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = Jᴴ * (M * J⁻¹ - (M * J⁻¹)ᴴ) * J := by rw [hY']
      _ = Jᴴ * M - Mᴴ * J := by
        rw [conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul]
        congr 1
        · simp only [Matrix.mul_assoc, hJJ', Matrix.mul_one]
        · rw [← Matrix.mul_assoc Jᴴ, ← conjTranspose_mul, hJJ', conjTranspose_one, Matrix.one_mul]
      _ = (2 * I) • Y := by rw [hI1, hY]
  have hY'inv : Y'⁻¹ = J * Y⁻¹ * Jᴴ := by
    apply Matrix.inv_eq_left_inv
    calc J * Y⁻¹ * Jᴴ * Y' = J * Y⁻¹ * (Jᴴ * Y' * J) * J⁻¹ := by
          simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = 1 := by rw [hkey, Matrix.mul_assoc J, hYY, Matrix.mul_one, hJJ]
  have hJh : Jᴴ = Jᵀ - (2 * I) • (Y * Cᵀ) := by
    have hτh : τᴴ = τ - (2 * I) • Y := by rw [← hY]; abel
    rw [hJ, conjTranspose_add, conjTranspose_mul, transpose_add, transpose_mul, hCh, hDh, hτt, hτh,
      Matrix.sub_mul, Matrix.smul_mul]
    abel
  have hJt : Jᵀ * (J⁻¹)ᵀ = 1 := by rw [← transpose_mul, hJJ', transpose_one]
  have hmat : J⁻¹ * (J * Y⁻¹ * Jᴴ) * (J⁻¹)ᵀ = Y⁻¹ - (2 * I) • (J⁻¹ * C)ᵀ := by
    rw [hJh, transpose_mul]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hJJ',
      Matrix.one_mul]
    rw [Matrix.mul_assoc Y⁻¹ Jᵀ, hJt, Matrix.mul_one, hYY, Matrix.one_mul]
  rw [hY'inv, ← dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, mulVec_mulVec, hmat, sub_mulVec,
    dotProduct_sub, smul_mulVec, dotProduct_smul, dotProduct_transpose_mulVec_self, smul_eq_mul]
  ring
end _root_.GlobalTheory.SW
end GlobalTheory.SW
