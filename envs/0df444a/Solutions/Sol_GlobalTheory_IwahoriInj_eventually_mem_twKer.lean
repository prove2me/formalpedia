-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.eventually_mem_twKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:12:43.328392+00:00
-- url     : https://prove2.me/submissions/662862e9-3316-4c9e-9e2f-2284296925fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Theorems.Thm_GlobalTheory_IwahoriInj_sub_mem_twKer
import Theorems.Thm_GlobalTheory_IwahoriInj_eventually_mem_ray

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
variable {g f f' : n → n → ℤ} {i j : n}
variable {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL n k) V}
variable [LinearOrder n]
namespace GlobalTheory.IwahoriInj
theorem _root_.solution {v : V} (hv : v ∈ twKer π (unipB k n) 1) :
    ∀ᶠ m : ℕ in Filter.atTop, v ∈ twKer π (grp k (chamber_ray (n := n) m).1) 1 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, w, rfl⟩ := hx
    filter_upwards [eventually_mem_ray u.2] with m hm
    simpa using sub_mem_twKer hm w
  | zero => simp
  | add x y _ _ hx hy =>
    filter_upwards [hx, hy] with m h1 h2 using add_mem h1 h2
  | smul a x _ hx =>
    filter_upwards [hx] with m h1 using Submodule.smul_mem _ a h1
end GlobalTheory.IwahoriInj
