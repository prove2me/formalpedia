-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.Swap.continuous_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:01:09.422332+00:00
-- url     : https://prove2.me/submissions/e63c2652-a15b-4fa2-bfca-1912c976bd1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearDescentPartialFourierEqFourierDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc GlobalTheory.JR.LinDesc.Swap
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
  [StarRing E] (A : Et F E)
namespace GlobalTheory.JR.LinDesc.Swap
theorem _root_.solution {r : ℕ} {τ : A.K} {p : Fin r → F} (hG : A.IsGen τ p) (lam : F) :
    Continuous (fun q : A.K × A.K => pt A hG lam q.1 q.2) := by
  unfold pt
  have he : Continuous (bas A hG).equivFun :=
    IsModuleTopology.continuous_of_linearMap (bas A hG).equivFun.toLinearMap
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  exact continuous_const.prodMk ((he.comp continuous_fst).prodMk
    ((continuous_pi fun i => htr.comp (continuous_const.mul continuous_snd)).prodMk continuous_const))
end GlobalTheory.JR.LinDesc.Swap
