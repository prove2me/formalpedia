-- Prove2me | solution 1 for GlobalTheory.TestLat.Model.map_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:16:55.799147+00:00
-- url     : https://prove2.me/submissions/a61d7a18-af1f-429e-a07f-ecd28a3e8407

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsSelfDualE
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotIsSelfDualETwo
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.TestLat GlobalTheory.TestLat.Model
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}
namespace GlobalTheory.TestLat.Model
theorem _root_.solution (σ : K →+* K) {x : K} (hx : x ∈ (algebraMap (𝓞 K) K).range) :
    σ x ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨⟨σ y, (RingOfIntegers.isIntegral_coe y).map σ.toIntAlgHom⟩, rfl⟩
end GlobalTheory.TestLat.Model
