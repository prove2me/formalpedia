-- Prove2me | solution 1 for GlobalTheory.LocBounded.exists_coeffs_of_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:50:13.240267+00:00
-- url     : https://prove2.me/submissions/742e3808-9074-4de6-96e8-a5713de871bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedOfIsIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
noncomputable section
open GlobalTheory GlobalTheory.LocBounded
namespace GlobalTheory.LocBounded
theorem _root_.solution {K : Type} [Field K] {n : ℕ} (N : Matrix (Fin n) (Fin n) K)
    {g : Matrix (Fin n) (Fin n) K} (hg : g ∈ Algebra.adjoin K {N}) :
    ∃ c : Fin n → K, g = ∑ k, c k • N ^ (k : ℕ) := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hg
  obtain ⟨p, rfl⟩ := hg
  have hmon := N.charpoly_monic
  have e : aeval N p = aeval N (p %ₘ N.charpoly) := by
    conv_lhs => rw [← modByMonic_add_div p N.charpoly]
    simp [Matrix.aeval_self_charpoly]
  change ∃ c : Fin n → K, aeval N p = _
  rw [e]
  by_cases h0 : p %ₘ N.charpoly = 0
  · exact ⟨0, by simp [h0]⟩
  refine ⟨fun k => (p %ₘ N.charpoly).coeff k, ?_⟩
  have hdeg : (p %ₘ N.charpoly).natDegree < n := by
    rw [natDegree_lt_iff_degree_lt h0]
    have := degree_modByMonic_lt p hmon
    rwa [Matrix.charpoly_degree_eq_dim, Fintype.card_fin] at this
  rw [aeval_eq_sum_range' hdeg, Finset.sum_range (fun i => (p %ₘ N.charpoly).coeff i • N ^ i)]
end GlobalTheory.LocBounded
