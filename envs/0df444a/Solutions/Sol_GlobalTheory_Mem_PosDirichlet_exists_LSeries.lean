-- Prove2me | solution 1 for GlobalTheory.Mem.PosDirichlet.exists_LSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:57:15.163822+00:00
-- url     : https://prove2.me/submissions/88d150aa-a016-48db-9c11-560defc41338

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DedekindZetaFactorizationRay

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
    ∃ b : ℕ → ℂ, 0 ≤ b ∧ ∀ s : ℂ, 1 < s.re → LSeriesHasSum b s (F s) := by
  obtain ⟨ι, w, N, hw, hN, h⟩ := hF
  refine ⟨fun n => ∑' i : N ⁻¹' {n}, (w i : ℂ), fun n => tsum_nonneg fun i =>
    Complex.zero_le_real.2 (hw i.1), fun s hs => ?_⟩
  have h1 := (h s hs).tsum_fiberwise N
  unfold LSeriesHasSum
  suffices e : ∀ n, LSeries.term (fun n => ∑' i : N ⁻¹' {n}, (w i : ℂ)) s n =
      ∑' i : N ⁻¹' {n}, (w i : ℂ) * (N i : ℂ) ^ (-s) by
    rw [funext e]; exact h1
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · haveI : IsEmpty (N ⁻¹' {0}) := ⟨fun i => hN i i.2⟩
    simp
  · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, ← tsum_mul_right]
    refine tsum_congr fun i => ?_
    have : N i = n := i.2
    rw [this]
end GlobalTheory.Mem.PosDirichlet
