-- Prove2me | solution 1 for LimitPoA.RegVar.corollary_3_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T20:02:02.620135+00:00
-- url     : https://prove2.me/submissions/60e56f78-8f0c-47c3-aba7-4ca032b071ec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_LimitPoA_RegVar_Model
import Definitions.Def_LimitPoA_RegVar_Limit
import Definitions.Def_LimitPoA_RegVar_Decomp
import Theorems.Thm_LimitPoA_RegVar_lemma_3
import Theorems.Thm_LimitPoA_RegVar_corollary_3_1

open Filter Topology LimitPoA.RegVar KellyStochasticNetworks

theorem solution (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (hnd : ∀ a, ∃ x, 0 < x ∧ τ a x ≠ 0)
    (hsd : IsScalableByDecomposition Γ τ) :
    IsAsymptoticallyWellDesigned Γ τ := by
  have hL := lemma_3 Γ hΓ τ hτ hnd
  refine (hL.out 0 2).mpr ?_
  intro d dInf hreg
  obtain ⟨φ, hφ, hdec, m, cls, g, hAD⟩ := hsd d dInf hreg
  -- the subsequence is regular with the same limit distribution
  have hreg' : IsRegular Γ (d ∘ φ) dInf := by
    obtain ⟨⟨hnn, hT⟩, hdich, hratio⟩ := hreg
    refine ⟨⟨fun n k => hnn _ k, hT.comp hφ.tendsto_atTop⟩, fun k => ?_, fun k => ?_⟩
    · rcases hdich k with h | ⟨L, h⟩
      · exact Or.inl (h.comp hφ.tendsto_atTop)
      · exact Or.inr ⟨L, h.comp hφ.tendsto_atTop⟩
    · exact (hratio k).comp hφ.tendsto_atTop
  -- the regular groups of the subsequence are those of the sequence
  have hK : Kreg Γ (d ∘ φ) = Kreg Γ d := by
    ext k
    simp only [Kreg, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases hreg.2.1 k with h' | ⟨L, h'⟩
      · exact h'
      · exact absurd (h'.comp hφ.tendsto_atTop) (not_tendsto_nhds_of_tendsto_atTop h L)
    · intro h
      exact h.comp hφ.tendsto_atTop
  have hdec' : IsDecomposable Γ (Kreg Γ (d ∘ φ))
      (fun n => restrict Γ (Kreg Γ (d ∘ φ)) ((d ∘ φ) n)) := by
    rw [hK]; exact hdec
  have hAD' : IsAsymDecomp Γ τ (Kreg Γ (d ∘ φ))
      (fun n => restrict Γ (Kreg Γ (d ∘ φ)) ((d ∘ φ) n)) m cls g := by
    rw [hK]; exact hAD
  exact ⟨φ, hφ, corollary_3_1 Γ hΓ τ hτ hnd (d ∘ φ) dInf hreg' hdec' m cls g hAD'⟩
