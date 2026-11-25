-- Prove2me | solution 1 for GlobalTheory.Mass.OrbMono.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:52:09.124144+00:00
-- url     : https://prove2.me/submissions/74e82385-d9fe-437f-a25c-11e5dd3f729e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumMonoSubadditive
import Theorems.Thm_GlobalTheory_Mass_OrbMono_orbSum_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.OrbMono
namespace GlobalTheory.Mass.OrbMono
theorem _root_.solution : ∀ (G α : Type) [Group G] [MulAction G α] , (∀ (X Y : Set α) (N N' : α → ℝ≥0∞), X ⊆ Y → (∀ x ∈ X, N x ≤ N' x) → orbSum G X N ≤ orbSum G Y N') ∧ (∀ (X : Set α) (B : ℝ≥0∞), orbSum G X (fun _ => B) = B * orbMass G X) ∧ (∀ (ι : Type) (s : Finset ι) (X : Set α) (Xi : ι → Set α) (N : α → ℝ≥0∞), X ⊆ ⋃ i ∈ s, Xi i → orbSum G X N ≤ ∑ i ∈ s, orbSum G (Xi i) N) ∧ (∀ (X : Set α) (s : Set α), (∀ x ∈ X, ∃ y ∈ s, ∃ g : G, g • y = x) → orbMass G X ≤ ((s.encard : ℕ∞) : ℝ≥0∞)) ∧ (∀ (X : Set α) (N N' : α → ℝ≥0∞), orbSum G X (fun x => N x + N' x) = orbSum G X N + orbSum G X N') := by
  intro G α _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X Y N N' hXY hN
    simp only [orbSum_eq]
    refine ENNReal.tsum_le_tsum fun q => ?_
    by_cases hq : Quotient.out q ∈ X
    · rw [if_pos hq, if_pos (hXY hq)]
      gcongr
      exact hN _ hq
    · rw [if_neg hq]
      exact zero_le
  · intro X B
    simp only [orbMass, orbSum]
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun q => by rw [mul_one, mul_comm]
  · intro ι s X Xi N hX
    simp only [orbSum_eq]
    rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
    refine ENNReal.tsum_le_tsum fun q => ?_
    by_cases hq : Quotient.out q ∈ X
    · obtain ⟨i, hi, hqi⟩ := Set.mem_iUnion₂.1 (hX hq)
      refine le_trans ?_ (Finset.single_le_sum (fun j _ => zero_le) hi)
      simp [hq, hqi]
    · rw [if_neg hq]
      exact zero_le
  · intro X s hs
    have key : ∀ q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
        ∃ y : s, (Quotient.mk _ (y : α) : MulAction.orbitRel.Quotient G α) = q.1 := by
      rintro ⟨q, hq⟩
      obtain ⟨y, hy, g, hg⟩ := hs _ hq
      refine ⟨⟨y, hy⟩, ?_⟩
      exact (Quotient.sound (MulAction.orbitRel_apply.2 ⟨g⁻¹, by simp [← hg]⟩)).trans
        (Quotient.out_eq q)
    choose φ hφ using key
    have hinj : Function.Injective φ := by
      intro a b h
      apply Subtype.ext
      rw [← hφ a, ← hφ b, h]
    calc orbMass G X
        = ∑' q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
            ((ENat.card (MulAction.stabilizer G (Quotient.out q.1)) : ℕ∞) : ℝ≥0∞)⁻¹ * 1 := rfl
      _ ≤ ∑' q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
            (fun _ : s => (1 : ℝ≥0∞)) (φ q) := by
          refine ENNReal.tsum_le_tsum fun q => ?_
          rw [mul_one]
          apply ENNReal.inv_le_one.2
          have h1 : (1 : ℕ∞) ≤ ENat.card (MulAction.stabilizer G (Quotient.out q.1)) :=
            (ENat.one_le_card_iff_nonempty _).2 ⟨1⟩
          exact_mod_cast h1
      _ ≤ ∑' _ : s, (1 : ℝ≥0∞) := ENNReal.tsum_comp_le_tsum_of_injective hinj _
      _ = s.encard := ENNReal.tsum_set_one s
  · intro X N N'
    simp only [orbSum]
    rw [← ENNReal.tsum_add]
    exact tsum_congr fun q => mul_add _ _ _
end GlobalTheory.Mass.OrbMono
