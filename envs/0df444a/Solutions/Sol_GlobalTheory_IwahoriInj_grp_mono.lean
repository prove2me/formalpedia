-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.grp_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:55.406043+00:00
-- url     : https://prove2.me/submissions/943b0ed5-f617-4418-8d0d-1e07cc38cacc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.IwahoriInj
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.IwahoriInj
theorem _root_.solution {f g : n → n → ℤ} (hf : Conc f) (hg : Conc g) (h : ∀ a b, g a b ≤ f a b) :
    grp k hf ≤ grp k hg := fun _ hx =>
  ⟨fun i j => (hx.1 i j).mono (h i j), fun i j => (hx.2 i j).mono (h i j)⟩
end GlobalTheory.IwahoriInj
