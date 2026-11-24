-- Prove2me | solution 1 for GlobalTheory.SeriesNakayama.mem_pow_smul_top_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:59:56.824134+00:00
-- url     : https://prove2.me/submissions/40e442f0-8e3e-4d00-851c-8230311002b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SpanModEquationsLift
import Theorems.Thm_GlobalTheory_SeriesNakayama_mem_pow_smul_top_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.SeriesNakayama
namespace GlobalTheory.SeriesNakayama
theorem _root_.solution {O ι : Type*} [CommRing O] (π : O) (n : ℕ) (x : ι → O) :
    x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule O (ι → O)) ↔
      ∀ i, x i ∈ (Ideal.span {π} ^ n • ⊤ : Submodule O O) := by
  simp only [mem_pow_smul_top_iff]
  refine ⟨fun ⟨y, hy⟩ i => ⟨y i, congrFun hy i⟩, fun h => ?_⟩
  choose y hy using h
  exact ⟨y, funext hy⟩
end GlobalTheory.SeriesNakayama
