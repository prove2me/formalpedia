-- Prove2me | solution 1 for GlobalTheory.LatPair.Mram_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:54:39.083108+00:00
-- url     : https://prove2.me/submissions/3c235b74-abfd-42b4-9e21-1b12b450a36b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Theorems.Thm_GlobalTheory_LatPair_dia_sub_mem_Mram
import Theorems.Thm_GlobalTheory_LatPair_dia_smul_eq_iff

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
namespace GlobalTheory.LatPair
theorem _root_.solution [Fintype n] [Nonempty n] {c : 𝓀[k]ˣ} (hc : c ≠ 1) : Mram k n ℂ ≠ ⊥ := by
  classical
  obtain ⟨P⟩ : Nonempty (Pair k n) := inferInstance
  intro h
  have h1 := dia_sub_mem_Mram (k := k) (n := n) (Pi.single P (1 : ℂ)) c
  rw [h, Submodule.mem_bot] at h1
  have h2 := congrFun h1 P
  simp [dia_smul_eq_iff, hc] at h2
end GlobalTheory.LatPair
