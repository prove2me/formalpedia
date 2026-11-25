-- Prove2me | solution 1 for GlobalTheory.AdLat.UnitRoot.norm_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:28:15.968528+00:00
-- url     : https://prove2.me/submissions/d5c6b277-420b-4a0b-8aac-c52ed39200f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdele
import Theorems.Thm_GlobalTheory_AdLat_UnitRoot_invol
import Theorems.Thm_GlobalTheory_AdLat_UnitRoot_tmul_fixed
import Theorems.Thm_GlobalTheory_AdLat_UnitRoot_sg_tmul
import Theorems.Thm_GlobalTheory_AdLat_UnitRoot_sg_sg
import Theorems.Thm_GlobalTheory_AdLat_UnitRoot_trace_mem
import Theorems.Thm_GlobalTheory_AdLat_adele_mul_integral
import Theorems.Thm_GlobalTheory_AdLat_galoisAut_mem_adelicCompletionOfElementSet


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
    ∃ b, z * sg (FiniteAdeleRing (𝓞 F) F) c z = incl F b ⊗ₜ[F] 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hx
    rw [sg_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    refine tmul_fixed c h2 hc (fun v => adele_mul_integral F (ha v) (ha v)) ?_
      (by rw [map_mul, invol c h2 hc, mul_comm])
    obtain ⟨s, hs⟩ := conj_mem c x hx
    obtain ⟨t, rfl⟩ := hx
    exact ⟨t * s, by rw [map_mul, hs]⟩
  | zero => exact ⟨0, by simp⟩
  | add y z hy hz h1 h3 =>
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h3
    obtain ⟨d, hd⟩ := trace_mem c h2 hc ((hatRing F E).mul_mem hy
      (galoisAut_mem_adelicCompletionOfElementSet F c (conj_mem c) hz))
    rw [map_mul, sg_sg c h2 hc] at hd
    exact ⟨a + b + d, by
      rw [map_add, map_add, map_add, TensorProduct.add_tmul, TensorProduct.add_tmul,
        ← ha, ← hb, ← hd]; ring⟩
  | neg y _ h1 =>
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, by rw [map_neg, ← ha]; ring⟩
end GlobalTheory.AdLat.UnitRoot
