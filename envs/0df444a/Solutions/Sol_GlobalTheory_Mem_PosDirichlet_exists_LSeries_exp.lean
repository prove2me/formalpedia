-- Prove2me | solution 1 for GlobalTheory.Mem.PosDirichlet.exists_LSeries_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:08:29.990812+00:00
-- url     : https://prove2.me/submissions/d36d29d0-a2d9-440e-b403-e9f5348e9574

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DedekindZetaFactorizationRay
import Theorems.Thm_GlobalTheory_Mem_PosDirichlet_exists_LSeries
import Theorems.Thm_GlobalTheory_Mem_PosDirichlet_exp_sub_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem
open GlobalTheory.Mem.PosDirichlet
namespace GlobalTheory.Mem.PosDirichlet
theorem _root_.solution {F : ℂ → ℂ} (hF : PosDirichlet F) :
    ∃ b : ℕ → ℂ, 0 ≤ b ∧ 0 < b 1 ∧ LSeries.abscissaOfAbsConv b ≤ 1 ∧
      ∀ s : ℂ, 1 < s.re → LSeries b s = Complex.exp (F s) := by
  obtain ⟨b, hb, h⟩ := hF.exp_sub_one.exists_LSeries
  have hδ : (0 : ℕ → ℂ) ≤ LSeries.delta := fun n => by
    by_cases hn : n = 1 <;> simp [LSeries.delta, hn]
  have h2 : ∀ s : ℂ, 1 < s.re → LSeriesHasSum (LSeries.delta + b) s (Complex.exp (F s)) := by
    intro s hs
    have h0 : LSeriesHasSum LSeries.delta s 1 := by
      unfold LSeriesHasSum
      have := hasSum_ite_eq (1 : ℕ) (1 : ℂ)
      convert this using 2 with n
      rw [LSeries.term_delta]
    simpa using h0.add (h s hs)
  refine ⟨LSeries.delta + b, add_nonneg hδ hb, ?_, ?_, fun s hs => (h2 s hs).LSeries_eq⟩
  · have : LSeries.delta 1 = 1 := by simp [LSeries.delta]
    rw [Pi.add_apply, this]
    exact add_pos_of_pos_of_nonneg one_pos (hb 1)
  · refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1) fun y hy => ?_
    exact (h2 y (by simpa using hy)).LSeriesSummable
end GlobalTheory.Mem.PosDirichlet
