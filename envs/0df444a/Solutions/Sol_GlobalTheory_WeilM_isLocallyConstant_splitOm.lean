-- Prove2me | solution 1 for GlobalTheory.WeilM.isLocallyConstant_splitOm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:27:00.637072+00:00
-- url     : https://prove2.me/submissions/2e33cdd7-5689-443c-979a-b7267215451a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsLocallyConstantSplitOm
import Theorems.Thm_GlobalTheory_WeilM_isLocallyConstant_orbit
import Theorems.Thm_GlobalTheory_WeilM_eventually_comp_eq
import Theorems.Thm_GlobalTheory_WeilM_eventually_char_eq_one
import Theorems.Thm_GlobalTheory_WeilM_flat_symm_apply
import Theorems.Thm_GlobalTheory_WeilM_splitOm_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel Filter
open scoped NNReal Topology Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
omit [DecidableEq α] [Fintype κ]
namespace GlobalTheory.WeilM
theorem _root_.solution (χ : (F × F)ˣ →* Circle) (hχ : Continuous χ) (J : Matrix β β (F × F)) (σ : κ ≃ α × β)
    {φ : (κ → F) → ℂ} (hφ : φ ∈ SB (κ → F)) : IsLocallyConstant fun h => splitOm (distribHaarChar F) χ J σ h φ := by
  refine isLocallyConstant_orbit _ ?_
  have c0 : Continuous (ugFst J) :=
    (Units.continuous_map (f := ((RingHom.fst F F).mapMatrix : Matrix β β (F × F) →+* Matrix β β F).toMonoidHom)
      (continuous_id.matrix_map (f := Prod.fst) continuous_fst)).comp continuous_subtype_val
  have c1 : Continuous fun h => GeneralLinearGroup.det (ugFst J h) :=
    Units.continuous_iff.mpr ⟨(Units.continuous_val.comp c0).matrix_det, (Units.continuous_val.comp c0.inv).matrix_det⟩
  have c2 : Continuous (χ.comp (Units.map (MonoidHom.inl F F))) :=
    hχ.comp (Units.continuous_map (continuous_id.prodMk continuous_const))
  have hc : ∀ M : UG (swapA F) J → Matrix β β F, Continuous M →
      Continuous fun q : UG (swapA F) J × (κ → F) => flat σ ((flat σ).symm q.2 * (M q.1)ᵀ) := fun M hM => by
    refine continuous_pi fun k => ?_
    simp only [flat_apply, mul_apply, flat_symm_apply, transpose_apply]
    fun_prop
  filter_upwards [(c1.tendsto' 1 1 (by simp)).eventually (eventually_char_eq_one _ c2),
    eventually_comp_eq (p₀ := 1) (fun p v => flat σ ((flat σ).symm v * ((ugFst J p)⁻¹).valᵀ))
      (fun p v => flat σ ((flat σ).symm v * (ugFst J p).valᵀ)) (hc _ (Units.continuous_val.comp c0.inv)) (hc _ (Units.continuous_val.comp c0))
      (by simp) (by simp) (fun p v => by
        simp only [Function.comp, LinearEquiv.symm_apply_apply, Matrix.mul_assoc, ← transpose_mul, Units.mul_inv,
          transpose_one, Matrix.mul_one, LinearEquiv.apply_symm_apply]) hφ] with h h1 h2
  funext u
  have h3 : splitChar (distribHaarChar F) χ (Fintype.card α) (GeneralLinearGroup.det (ugFst J h)) = 1 := by
    have := h1.1
    simp only [MonoidHom.comp_apply] at this
    simp [splitChar, this, h1.2]
  rw [splitOm_apply, h3, one_mul]
  exact h2 u
end GlobalTheory.WeilM
