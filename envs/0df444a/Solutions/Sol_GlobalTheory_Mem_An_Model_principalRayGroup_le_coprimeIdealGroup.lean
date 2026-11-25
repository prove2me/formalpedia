-- Prove2me | solution 1 for GlobalTheory.Mem.An.Model.principalRayGroup_le_coprimeIdealGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:04:25.540903+00:00
-- url     : https://prove2.me/submissions/b2a3f4bd-ebd1-47cd-94b3-5cf08eb0ef09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NormOneSevenOneTwo
import Theorems.Thm_GlobalTheory_Mem_An_Model_mem_rayI_of_coprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An GlobalTheory.Mem.An.Model
namespace GlobalTheory.Mem.An.Model
theorem _root_.solution {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) : rayP 𝔮 ≤ rayI 𝔮 := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro I ⟨a, ha, hI⟩
  refine mem_rayI_of_coprime 𝔮 _ ?_ ?_ I hI
  · intro h0
    apply I.ne_zero
    rw [hI, h0]
    exact FractionalIdeal.coeIdeal_bot
  · rw [Ideal.eq_top_iff_one]
    have hmem : a - (a - 1) ∈ Ideal.span {a} ⊔ 𝔮 :=
      Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) (Ideal.mem_sup_right ha)
    simpa using hmem
end GlobalTheory.Mem.An.Model
