-- Prove2me | solution 1 for GlobalTheory.FiniteCovolume.isUStab_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:45.158204+00:00
-- url     : https://prove2.me/submissions/611b301d-f5e6-42cd-a045-7ea3c8de9755

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FinMuOfFiniteCovolume

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.FiniteCovolume
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.FiniteCovolume
theorem _root_.solution {r : ℕ} {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
    {γ : GL (Fin r) E} (h : IsUStab G Λ γ) : IsUStab G Λ γ⁻¹ := by
  have key : ∀ v : Fin r → E, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E)
      (Matrix.mulVec ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · rw [← h.1, key, key]
  · have hx := h.2 (Matrix.mulVec ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) x)
    rw [key] at hx
    exact hx.symm
end GlobalTheory.FiniteCovolume
