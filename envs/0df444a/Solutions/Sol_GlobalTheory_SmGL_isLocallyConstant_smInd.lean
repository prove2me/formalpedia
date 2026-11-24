-- Prove2me | solution 1 for GlobalTheory.SmGL.isLocallyConstant_smInd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:50:14.036556+00:00
-- url     : https://prove2.me/submissions/150a74dd-563e-4bc1-a053-e644c5f815b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open GlobalTheory
open GlobalTheory.SmGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.SmGL
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {P : Subgroup G} {σ : Representation ℂ P W} (f : smoothPart (ind P σ)) :
    IsLocallyConstant (f.1.1 : G → W) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have h : {g : G | ind P σ g f.1 = f.1} ∈ nhds ((fun y => x⁻¹ * y) x) :=
    IsOpen.mem_nhds f.2 (by simp)
  filter_upwards [(continuous_const_mul x⁻¹).continuousAt.preimage_mem_nhds h] with y hy
  have hy' : f.1.1 (x * (x⁻¹ * y)) = f.1.1 x := congrFun (congrArg Subtype.val hy) x
  rwa [mul_inv_cancel_left] at hy'
end GlobalTheory.SmGL
