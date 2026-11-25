-- Prove2me | solution 1 for GlobalTheory.maj_lact_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:09.248282+00:00
-- url     : https://prove2.me/submissions/316ab65a-4792-487a-a268-f5b7331a3463

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajLactRmul
import Theorems.Thm_GlobalTheory_MajInv_maj_rmul
import Theorems.Thm_GlobalTheory_MajInv_lact_mem_dom
import Theorems.Thm_GlobalTheory_MajInv_maj_lact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthogonalFrameDomain_rmul_mem_dom


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
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory
theorem _root_.solution :
    (∀ (r : ℕ) (X : Data E r) (γ : GL (Fin r) E), IsUStab X.Gm X.Λ γ → ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj (lact γ (rmul x b)) τ (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ.1) v) = X.maj x τ v) := by
  intro r X γ hγ x hx b hb
  refine ⟨MajInv.lact_mem_dom X hγ (OrthogonalFrameDomain.rmul_mem_dom X hx hb), fun τ v => ?_⟩
  rw [MajInv.maj_lact X hγ, MajInv.maj_rmul X hx hb]
end GlobalTheory
