-- Prove2me | solution 1 for GlobalTheory.AdLat.UnitRoot.trace_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:24:36.529316+00:00
-- url     : https://prove2.me/submissions/ebeaa46d-d9b1-4aa0-acf4-bb51fd2bd44e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdele
import Theorems.Thm_GlobalTheory_AdLat_UnitRoot_invol
import Theorems.Thm_GlobalTheory_AdLat_UnitRoot_tmul_fixed
import Theorems.Thm_GlobalTheory_AdLat_UnitRoot_sg_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.UnitRoot
variable (F : Type) [Field F] [NumberField F]
variable (E : Type) [Field E] [NumberField E] [Algebra F E]
variable {F E}
namespace GlobalTheory.AdLat.UnitRoot
theorem _root_.solution (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) {z : RA F E}
    (hz : z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) :
    ∃ b, z + sg (FiniteAdeleRing (𝓞 F) F) c z = incl F b ⊗ₜ[F] 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hx
    rw [sg_tmul, ← TensorProduct.tmul_add]
    refine tmul_fixed c h2 hc ha ?_ (by rw [map_add, invol c h2 hc, add_comm])
    obtain ⟨s, hs⟩ := conj_mem c x hx
    obtain ⟨t, rfl⟩ := hx
    exact ⟨t + s, by rw [map_add, hs]⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ h1 h2 =>
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    exact ⟨a + b, by rw [map_add, map_add, TensorProduct.add_tmul, ← ha, ← hb]; ring⟩
  | neg y _ h1 =>
    obtain ⟨a, ha⟩ := h1
    exact ⟨-a, by rw [map_neg, map_neg, TensorProduct.neg_tmul, ← ha]; ring⟩
end GlobalTheory.AdLat.UnitRoot
