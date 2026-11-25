-- Prove2me | solution 1 for GlobalTheory.SpMove.normalAt_spAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:40:38.470698+00:00
-- url     : https://prove2.me/submissions/ee8b73c3-4479-4195-80c5-b0ebc157dd2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolUnifReparam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_EntireEqZeroOrEqZeroOfMulEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaLawSymplecticNormalForm
import Theorems.Thm_GlobalTheory_SpMove_thetaChar_half
import Theorems.Thm_GlobalTheory_SpMove_jAut_transpose_mulVec_mem_iff
import Theorems.Thm_GlobalTheory_SpMove_exists_theta_law
import Theorems.Thm_GlobalTheory_KeyPow_NormalAt_mem_siegelH
import Theorems.Thm_GlobalTheory_exists_holUnif_reparam
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_isUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SpMove
namespace GlobalTheory.SpMove
theorem _root_.solution : ∀ (x : KeyIn ℂ) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c : ℂ) (sp : Matrix (Fin x.P.g ⊕ Fin x.P.g) (Fin x.P.g ⊕ Fin x.P.g) ℤ) (n n' k k' : Fin x.P.g → ℤ), sp ∈ Matrix.symplecticGroup (Fin x.P.g) ℤ → GlobalTheory.KeyPow.ThetaLaw x.P.g sp n n' k k' → c ≠ 0 → GlobalTheory.KeyPow.NormalAt x τ M (fun i => (n i : ℂ) / 2) (fun i => (n' i : ℂ) / 2) c → ∃ (M' : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c' : ℂ), c' ≠ 0 ∧ M'.det ^ 4 / c' ^ 8 = M.det ^ 4 / c ^ 8 ∧ GlobalTheory.KeyPow.NormalAt x (Key.Chi.spAct sp τ) M' (fun i => (k i : ℂ) / 2) (fun i => (k' i : ℂ) / 2) c' := by
  intro x τ M c sp n n' k k' hsp hlaw hc hN
  have hτ := hN.mem_siegelH
  obtain ⟨u, -, -, hΛ, hrig, hfn, hv⟩ := hN
  have hj := Key.Chi.jAut_isUnit hsp hτ
  have hτ' := Key.Chi.spAct_mem hsp hτ
  obtain ⟨r, hr, H⟩ := exists_theta_law hsp hlaw hτ
  set j := Key.Chi.jAut sp τ with hjdef
  have hj0 : j.det ≠ 0 := hj.ne_zero
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact pow_ne_zero 4 hj0 (by rw [← hr]; simp)
  have e1 : j.transpose * (j⁻¹).transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hj, Matrix.transpose_one]
  have e2 : (j⁻¹).transpose * j.transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hj, Matrix.transpose_one]
  let φ : (Fin x.P.g → ℂ) ≃ₗ[ℂ] (Fin x.P.g → ℂ) := Matrix.toLin'OfInv e2 e1
  have hφ : ∀ z, φ z = j.transpose.mulVec z := fun _ => rfl
  have hE : Differentiable ℂ fun z => Complex.exp (Real.pi * Complex.I * Key.Chi.expArg sp τ (φ z)) := by
    simp only [hφ, Key.Chi.expArg, dotProduct, Matrix.mulVec]
    fun_prop
  obtain ⟨u', -, hΛ', hrig', hfn', hv'⟩ := exists_holUnif_reparam x.P.A x.P.L x.P.g u φ _ hE
    (fun _ => Complex.exp_ne_zero _) (by simp [Key.Chi.expArg])
  refine ⟨M * j⁻¹, c / r, div_ne_zero hc hr0, ?_, u', hτ'.1, hτ'.2, fun z => ?_, hrig' _ hrig, ?_,
    fun i => hv' _ _ ?_⟩
  · rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', div_pow, hr]
    field_simp
  · rw [hΛ', hΛ, hφ]
    exact jAut_transpose_mulVec_mem_iff hsp hτ z
  · convert hfn' _ _ hfn using 2 with z
    have h1 := H (φ z)
    have h2 : Key.Chi.zAct sp τ (φ z) = z := by
      rw [Key.Chi.zAct, hφ, Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
    rw [h2] at h1
    rw [thetaChar_half, thetaChar_half, h1]
    field_simp
  · have h3 : φ ((M * j⁻¹) i) = M i := by
      rw [hφ, Matrix.mulVec_transpose]
      change ((M * j⁻¹) * j) i = M i
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hj, Matrix.mul_one]
    rw [map_smul, h3]
    exact hv i
end GlobalTheory.SpMove
