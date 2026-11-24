-- Prove2me | solution 1 for GlobalTheory.MajInv.lact_mem_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:29:42.7231+00:00
-- url     : https://prove2.me/submissions/ac726913-a1d0-4f99-95e6-bdbca2d5a4c0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajLactRmul
import Theorems.Thm_GlobalTheory_MajInv_gram_lact

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
open GlobalTheory GlobalTheory.MajInv
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.MajInv
theorem _root_.solution {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : lact γ x ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · have e1 : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
    rw [e1, Matrix.det_mul, show ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det =
      τ.1 (γ : Matrix (Fin r) (Fin r) E).det by rw [RingHom.map_det]; rfl]
    refine mul_ne_zero ?_ (hx τ).1
    have hu : IsUnit ((γ : Matrix (Fin r) (Fin r) E).det) :=
      (Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit
    exact (hu.map τ.1).ne_zero
  · have := (hx τ).2 i
    unfold dmin at this ⊢
    rwa [gram_lact X hγ]
end GlobalTheory.MajInv
