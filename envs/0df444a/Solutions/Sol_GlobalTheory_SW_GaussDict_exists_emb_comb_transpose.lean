-- Prove2me | solution 1 for GlobalTheory.SW.GaussDict.exists_emb_comb_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:26:02.80823+00:00
-- url     : https://prove2.me/submissions/a9eec732-182d-480e-a8b0-42cd39832788

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_GaussianQuadFormRationalCoordsHermitian
import Theorems.Thm_GlobalTheory_SW_Dict_exists_emb_comb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.GaussDict
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
namespace GlobalTheory.SW.GaussDict
theorem _root_.solution (w : (E →+* ℂ) → ℂ) :
    ∃ c : Fin (Module.finrank ℚ E) → ℂ, ∀ σ : E →+* ℂ,
      ∑ j, σ (Module.finBasis ℚ E j) * c j = w σ := by
  classical
  let e : (E →+* ℂ) ≃ Fin (Module.finrank ℚ E) :=
    Fintype.equivFinOfCardEq (NumberField.Embeddings.card E ℂ)

  let A : Matrix (Fin (Module.finrank ℚ E)) (Fin (Module.finrank ℚ E)) ℂ :=
    Matrix.of fun i j => e.symm i (Module.finBasis ℚ E j)
  have hT : Function.Surjective Aᵀ.mulVec := by
    intro c
    obtain ⟨w', hw'⟩ := GlobalTheory.SW.Dict.exists_emb_comb (E := E) c
    refine ⟨fun i => w' (e.symm i), funext fun j => ?_⟩
    rw [← hw' j]
    exact e.symm.sum_comp (fun σ => σ (Module.finBasis ℚ E j) * w' σ)
  have hA : IsUnit A := by
    have h := Matrix.mulVec_surjective_iff_isUnit.mp hT
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose] at h
    exact (Matrix.isUnit_iff_isUnit_det _).mpr h
  obtain ⟨c, hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hA (fun i => w (e.symm i))
  refine ⟨c, fun σ => ?_⟩
  have h := congrFun hc (e σ)
  simpa [Matrix.mulVec, dotProduct, A] using h
end GlobalTheory.SW.GaussDict
