-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Counting.exists_ncard_entrywiseBox_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:34:35.956361+00:00
-- url     : https://prove2.me/submissions/7470c155-28ac-4507-a184-553d9e087ae6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalDiscreteness_Counting
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsNcardEntrywiseBoxLe
import Theorems.Thm_GroundTheory_Automorphic_CuspidalSpectrum_exists_natCast_mul_integral_of_isCompact
import Theorems.Thm_GroundTheory_Automorphic_CuspidalSpectrum_exists_ncard_integers_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Counting
open GroundTheory.Automorphic.CuspidalSpectrum
namespace GlobalTheory.CompanionTheory.Counting
theorem _root_.solution (K : Type) [Field K] [NumberField K] (n : ℕ)
    (𝒦 : Set (FiniteAdeleRing (𝓞 K) K)) (h𝒦 : IsCompact 𝒦) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : Fin n → Fin n → ℝ, (∀ i j, 0 ≤ T i j) →
      (setOf fun γ : GL (Fin n) K => (∀ i j,
        algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) ∈ 𝒦 ∧
        ∀ w : InfinitePlace K, w ((γ : Matrix (Fin n) (Fin n) K) i j) ≤ T i j)).Finite ∧
      ((Set.ncard (setOf fun γ : GL (Fin n) K => (∀ i j,
        algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) ∈ 𝒦 ∧
        ∀ w : InfinitePlace K, w ((γ : Matrix (Fin n) (Fin n) K) i j) ≤ T i j)) : ℕ) : ℝ) ≤
        ∏ i, ∏ j, C * (1 + T i j) ^ Module.finrank ℚ K := by
  obtain ⟨m, hm, hint⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_natCast_mul_integral_of_isCompact K h𝒦
  obtain ⟨C₀, hC₀, hcount⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_ncard_integers_le K
  have hw : ∀ (w : InfinitePlace K) (x : K), w ((m : K) * x) = (m : ℝ) * w x := by
    intro w x
    rw [← w.norm_embedding_eq, map_mul, norm_mul, w.norm_embedding_eq, w.norm_embedding_eq, w.map_natCast]
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmK : (m : K) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨C₀ * (m : ℝ) ^ Module.finrank ℚ K, mul_nonneg hC₀ (by positivity), ?_⟩
  intro T hT
  have hA : ∀ p : Fin n × Fin n,
      (((↑) : 𝓞 K → K) '' {z | ∀ w : InfinitePlace K, w (z : K) ≤ (m : ℝ) * T p.1 p.2}).Finite ∧
      ((((↑) : 𝓞 K → K) '' {z | ∀ w : InfinitePlace K, w (z : K) ≤ (m : ℝ) * T p.1 p.2}).ncard : ℝ) ≤
        C₀ * (1 + (m : ℝ) * T p.1 p.2) ^ Module.finrank ℚ K := by
    intro p
    obtain ⟨hf, hc⟩ := hcount ((m : ℝ) * T p.1 p.2) (mul_nonneg (by positivity) (hT p.1 p.2))
    exact ⟨hf.image _, le_trans (by exact_mod_cast Set.ncard_image_le hf) hc⟩
  let F : GL (Fin n) K → (Fin n × Fin n → K) := fun γ p => (m : K) * (γ : Matrix (Fin n) (Fin n) K) p.1 p.2
  obtain ⟨t, ht⟩ : ∃ t : Finset (Fin n × Fin n → K), t = Fintype.piFinset fun p => (hA p).1.toFinset := ⟨_, rfl⟩
  have key : ∀ γ : GL (Fin n) K, (∀ i j, algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) ∈ 𝒦 ∧
      ∀ w : InfinitePlace K, w ((γ : Matrix (Fin n) (Fin n) K) i j) ≤ T i j) → F γ ∈ (t : Set (Fin n × Fin n → K)) := by
    intro γ hγ
    rw [Finset.mem_coe, ht, Fintype.mem_piFinset]
    intro p
    rw [Set.Finite.mem_toFinset]
    obtain ⟨z, hz⟩ := hint _ (hγ p.1 p.2).1
    refine ⟨z, fun w => ?_, hz⟩
    rw [hz, hw]
    exact mul_le_mul_of_nonneg_left ((hγ p.1 p.2).2 w) (by positivity)
  have inj : ∀ γ γ' : GL (Fin n) K, F γ = F γ' → γ = γ' := by
    intro γ γ' h
    ext i j
    exact mul_left_cancel₀ hmK (congrFun h (i, j))
  refine ⟨?_, ?_⟩
  · exact Set.Finite.of_finite_image ((t.finite_toSet).subset (Set.image_subset_iff.mpr fun γ hγ => key γ hγ))
      (fun γ _ γ' _ h => inj γ γ' h)
  · refine le_trans (Nat.cast_le.mpr (Set.ncard_le_ncard_of_injOn F (fun γ hγ => key γ hγ)
      (fun γ _ γ' _ h => inj γ γ' h) t.finite_toSet)) ?_
    rw [Set.ncard_coe_finset, ht, Fintype.card_piFinset, Nat.cast_prod, Fintype.prod_prod_type]
    apply Finset.prod_le_prod (fun _ _ => Finset.prod_nonneg fun _ _ => by positivity)
    intro i _
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro j _
    rw [← Set.ncard_eq_toFinset_card _ (hA (i, j)).1]
    refine le_trans (hA (i, j)).2 ?_
    rw [mul_assoc, ← mul_pow]
    apply mul_le_mul_of_nonneg_left _ hC₀
    apply pow_le_pow_left₀ (by nlinarith [hT i j])
    nlinarith [hT i j]
end GlobalTheory.CompanionTheory.Counting
