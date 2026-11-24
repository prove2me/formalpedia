-- Prove2me | solution 1 for GlobalTheory.Mem.RayData.finite_cnt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:57:11.902122+00:00
-- url     : https://prove2.me/submissions/85d04a10-f40f-4594-ba6f-aae6cea06eb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem
open NumberField IsDedekindDomain
attribute [instance] RayData.grp RayData.fin
open GlobalTheory.Mem.RayData
variable {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)
namespace GlobalTheory.Mem.RayData
theorem _root_.solution (c : D.G) (n : ℕ) :
    Finite {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ Ideal.absNorm I = n ∧ D.cls I = c} := by
  have hs : {I : Ideal (𝓞 K) | IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ Ideal.absNorm I = n ∧
      D.cls I = c}.Finite :=
    (Ideal.finite_setOfPred_absNorm_eq n).subset fun I hI => hI.2.1
  exact hs.to_subtype
end GlobalTheory.Mem.RayData
