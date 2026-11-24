-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.iwahoriProj_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:50:13.986122+00:00
-- url     : https://prove2.me/submissions/8eeed856-7100-47ab-bc87-e6704c018ae2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Theorems.Thm_GlobalTheory_IwahoriInj_mem_fixed
import Theorems.Thm_GlobalTheory_IwahoriInj_inj_chambers
import Theorems.Thm_GlobalTheory_IwahoriInj_grp_ray_zero_le
import Theorems.Thm_GlobalTheory_IwahoriInj_eventually_mem_twKer

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
namespace GlobalTheory.IwahoriInj
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V) (hπ : IsSmooth π) :
    Function.Injective (iwahoriProj π) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv => Subtype.ext ?_
  have h1 : v.1 ∈ twKer π (unipB k n) 1 := (Submodule.Quotient.mk_eq_zero _).1 (congrArg Subtype.val hv)
  obtain ⟨m, hm⟩ := (eventually_mem_twKer h1).exists
  exact inj_chambers hπ (chamber_ray 0) (chamber_ray m) v.1
    (mem_fixed.2 fun h hh => mem_fixed.1 v.2 h (grp_ray_zero_le hh)) hm
end GlobalTheory.IwahoriInj
