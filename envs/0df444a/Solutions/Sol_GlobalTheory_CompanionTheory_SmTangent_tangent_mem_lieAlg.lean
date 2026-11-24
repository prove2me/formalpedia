-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmTangent.tangent_mem_lieAlg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:02:24.688396+00:00
-- url     : https://prove2.me/submissions/9909a9e5-4d5b-476f-bdd5-c297c69e9d9e

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SmComplete
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraOfTangentCurve
import Theorems.Thm_GlobalTheory_CompanionTheory_SmTangent_matrix_tendsto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmTangent
namespace GlobalTheory.CompanionTheory.SmTangent
theorem _root_.solution : ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)), IsClosedMatrixGroup G →
    ∀ (γ : ℝ → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ), γ 0 = 1 →
      (∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ G) → HasDerivAt γ Y 0 → Y ∈ lieAlg G := by
  intro n G hG γ Y h0 hev hd t
  obtain ⟨hcl, h1G, hmul, -⟩ := hG
  have hpowG : ∀ g ∈ G, ∀ k : ℕ, g ^ k ∈ G := by
    intro g hg k
    induction k with
    | zero => simpa using h1G
    | succ k ih => rw [pow_succ]; exact hmul _ ih _ hg
  have hs : Tendsto (fun k : ℕ => t / (k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat t
  refine hcl.mem_of_tendsto (matrix_tendsto n γ Y h0 hd t) ?_
  filter_upwards [hs.eventually hev] with k hk
  exact hpowG _ hk k
end GlobalTheory.CompanionTheory.SmTangent
