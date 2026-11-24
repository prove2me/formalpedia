-- Prove2me | solution 1 for GlobalTheory.LatPair.resChar_residue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:11.480664+00:00
-- url     : https://prove2.me/submissions/20030a19-ca72-4e74-8981-a5661413a1ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
open SplitWeil
namespace GlobalTheory.LatPair
theorem _root_.solution {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (q : Unif k) (s : 𝒪[k]) :
    resChar ψ hψ q (residue 𝒪[k] s) = ψ (q.inv * s) :=
  congrArg (fun z : Circle => (z : ℂ)) (apply_inv_mul_congr hψ q (residue_surjective (R := 𝒪[k]) _).choose_spec)
end GlobalTheory.LatPair
