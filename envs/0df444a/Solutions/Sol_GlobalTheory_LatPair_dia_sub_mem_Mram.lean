-- Prove2me | solution 1 for GlobalTheory.LatPair.dia_sub_mem_Mram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:38:47.476279+00:00
-- url     : https://prove2.me/submissions/d5ea704e-38a4-4f62-a11c-2171a85f6533

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Theorems.Thm_GlobalTheory_LatPair_mem_Mram

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
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n M)
namespace GlobalTheory.LatPair
theorem _root_.solution (c : 𝓀[k]ˣ) : dia c φ - φ ∈ Mram k n M := by
  letI := Fintype.ofFinite 𝓀[k]ˣ
  refine (mem_Mram _).2 fun P => ?_
  simp only [Pi.sub_apply, dia_apply, Finset.sum_sub_distrib, smul_smul, sub_eq_zero]
  exact Equiv.sum_comp (Equiv.mulLeft c) fun d => φ (d • P)
end GlobalTheory.LatPair
