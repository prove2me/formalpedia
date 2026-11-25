-- Prove2me | solution 1 for GlobalTheory.HolTheta.normal_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:16:03.660642+00:00
-- url     : https://prove2.me/submissions/d0eff69d-f5b7-473b-9995-0247c703c312

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsThetaHolomorphic
import Theorems.Thm_GlobalTheory_RiemannRel_det_ne_zero
import Theorems.Thm_GlobalTheory_RiemannRel_hermForm_col
import Theorems.Thm_GlobalTheory_RiemannRel_hermForm_mulVec
import Theorems.Thm_GlobalTheory_RiemannRel_of_cols_mulVec
import Theorems.Thm_GlobalTheory_RiemannRel_symm_posDef
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.HolTheta
open Matrix GlobalTheory.CanTh GlobalTheory.RiemannRel
variable {g : ℕ}
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
open Matrix
variable {g : ℕ}
namespace GlobalTheory.HolTheta
namespace _root_.GlobalTheory.HolTheta
theorem _root_.solution (G : Matrix (Fin g) (Fin g) ℂ) (e f : Fin g → Fin g → ℂ) (hG : G.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G z z).re)
    (hee : ∀ j k, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (e j) (e k)).im = 0) (hff : ∀ j k, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (f j) (f k)).im = 0)
    (hef : ∀ j k, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (e j) (f k)).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k)
    {A τ : Matrix (Fin g) (Fin g) ℂ} (hA : A = Matrix.of fun i j => e j i)
    (hτ : τ = A⁻¹ * Matrix.of fun i j => f j i) :
    IsUnit A.det ∧ τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧
      ∀ z w, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G z w = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (_root_.GlobalTheory.CanTh.imInv τ) (A⁻¹ *ᵥ z) (A⁻¹ *ᵥ w) := by
  set F : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => f j i with hF
  have hAe : ∀ k, A *ᵥ Pi.single k 1 = e k := fun k => by
    rw [hA]; exact _root_.GlobalTheory.RiemannRel.of_cols_mulVec e k
  have hFf : ∀ k, F *ᵥ Pi.single k 1 = f k := fun k => _root_.GlobalTheory.RiemannRel.of_cols_mulVec f k
  have h1 : ∀ j k, ((Aᵀ * G * A.map (starRingEnd ℂ)) j k).im = 0 := fun j k => by
    rw [← _root_.GlobalTheory.RiemannRel.hermForm_col, hAe, hAe]; exact hee j k
  have h2 : ∀ j k, ((Aᵀ * G * F.map (starRingEnd ℂ)) j k).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k :=
    fun j k => by rw [← _root_.GlobalTheory.RiemannRel.hermForm_col, hAe, hFf]; exact hef j k
  have h3 : ∀ j k, ((Fᵀ * G * F.map (starRingEnd ℂ)) j k).im = 0 := fun j k => by
    rw [← _root_.GlobalTheory.RiemannRel.hermForm_col, hFf, hFf]; exact hff j k
  have hdet : A.det ≠ 0 := _root_.GlobalTheory.RiemannRel.det_ne_zero G A F hpos h1 h2
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hAτ : A * τ = F := by
    rw [hτ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv A hunit, Matrix.one_mul]
  obtain ⟨hsymm, hpd⟩ := _root_.GlobalTheory.RiemannRel.symm_posDef G A τ hG hdet hpos h1
    (by rw [hAτ]; exact h2) (by rw [hAτ]; exact h3)
  refine ⟨hunit, hsymm, hpd, ?_⟩
  set M := Aᵀ * G * A.map (starRingEnd ℂ) with hMdef
  have hMreal : (M.map Complex.re).map Complex.ofReal = M := by
    ext j k
    apply Complex.ext
    · simp
    · simp [h1 j k]
  have hinv : M.map Complex.re * τ.map Complex.im = 1 := by
    ext j k
    have h := h2 j k
    rw [← hAτ, Matrix.map_mul, ← Matrix.mul_assoc, Matrix.mul_apply, Complex.im_sum] at h
    rw [Matrix.mul_apply]
    have hsum : ∀ l, ((M j l) * (starRingEnd ℂ) (τ l k)).im = -((M j l).re * (τ l k).im) := by
      intro l
      rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, h1 j l]
      ring
    simp only [Matrix.map_apply] at h ⊢
    rw [Finset.sum_congr rfl (fun l _ => hsum l), Finset.sum_neg_distrib] at h
    linarith
  have hM : M = _root_.GlobalTheory.CanTh.imInv τ := by
    unfold _root_.GlobalTheory.CanTh.imInv
    rw [Matrix.inv_eq_left_inv hinv, hMreal]
  intro z w
  have hz : ∀ v : Fin g → ℂ, v = A *ᵥ (A⁻¹ *ᵥ v) := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hunit, Matrix.one_mulVec]
  conv_lhs => rw [hz z, hz w]
  rw [_root_.GlobalTheory.RiemannRel.hermForm_mulVec, ← hMdef, hM]
  rfl
end _root_.GlobalTheory.HolTheta
end GlobalTheory.HolTheta
