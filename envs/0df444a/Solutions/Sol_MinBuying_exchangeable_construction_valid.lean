-- Prove2me | solution 1 for MinBuying.exchangeable_construction_valid
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:37:18.378523+00:00
-- url     : https://prove2.me/submissions/308ea26e-a7a4-429a-926c-1df55f328b01

import Definitions.Def_MinBuying_ExchangeableConstruction

open MeasureTheory Set MinBuying
open scoped BigOperators ENNReal
noncomputable section
namespace MinBuyingGapValidProof

private lemma type_size_bounds (n : ℕ) (i : Fin n) : 1 ≤ gapTypeSize n i ∧ gapTypeSize n i ≤ n := by
  refine ⟨le_max_left _ _,max_le (by have hi := i.isLt; omega) (Nat.div_le_self _ _)⟩

private lemma subsets_nonempty (n : ℕ) (i : Fin n) : (gapSubsets n i).Nonempty := by
  apply Finset.powersetCard_nonempty.mpr
  simpa using (type_size_bounds n i).2

private lemma uniformAtoms_probability {α β : Type*} [MeasurableSpace β]
    (s : Finset α) (hs : s.Nonempty) (f : α → β) : IsProbabilityMeasure (uniformAtoms s f) := by
  constructor
  simp only [uniformAtoms,Measure.smul_apply,Measure.finsetSum_apply,Measure.dirac_apply_of_mem,
    Set.mem_univ,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hs.card_pos.ne') (by simp)

private lemma type_probability (n : ℕ) (i : Fin n) : IsProbabilityMeasure (gapTypeLaw n i) :=
  uniformAtoms_probability _ (subsets_nonempty n i) _

private lemma weights_sum (n : ℕ) : gapZeroWeight n + ∑ i : Fin n, gapTypeWeight n i = 1 := by
  unfold gapZeroWeight gapTypeWeight
  rw [← Finset.mul_sum,Fin.sum_univ_eq_sum_range]
  have h := geom_sum_mul_neg (1/4 : ℝ) n
  norm_num at h
  nlinarith only [h]

private lemma weight_nonneg (n : ℕ) (i : Fin n) : 0 ≤ gapTypeWeight n i := by
  unfold gapTypeWeight; positivity

private lemma zero_weight_nonneg (n : ℕ) : 0 ≤ gapZeroWeight n := by
  unfold gapZeroWeight; positivity

private lemma gap_probability (n : ℕ) : IsProbabilityMeasure (exchangeableGapLaw n) := by
  haveI : ∀ i : Fin n, IsProbabilityMeasure (gapTypeLaw n i) := fun i => type_probability n i
  constructor
  simp only [exchangeableGapLaw,Measure.add_apply,Measure.smul_apply,Measure.finsetSum_apply,
    Measure.dirac_apply_of_mem,Set.mem_univ,measure_univ,smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => weight_nonneg n i),
    ← ENNReal.ofReal_add (zero_weight_nonneg n) (Finset.sum_nonneg (fun i _ => weight_nonneg n i)),weights_sum]
  simp

private lemma valuation_nonneg (n : ℕ) (i : Fin n) (S : Finset (Fin n)) (j : Fin n) :
    0 ≤ gapValuation n i S j := by
  unfold gapValuation;split_ifs <;> positivity

private lemma gap_nonneg (n : ℕ) : ∀ᵐ v ∂exchangeableGapLaw n, ∀ j, 0 ≤ v j := by
  rw [ae_iff]
  have hatom : ∀ (i : Fin n) (S : Finset (Fin n)),
      Measure.dirac (gapValuation n i S) {v | ¬ ∀ j, 0 ≤ v j} = 0 := by
    intro i S
    simp [Measure.dirac_apply',valuation_nonneg]
  simp [exchangeableGapLaw,gapTypeLaw,uniformAtoms,Measure.add_apply,Measure.smul_apply,
    Measure.finsetSum_apply,hatom,Measure.dirac_apply',valuation_nonneg]

private lemma type_exchangeable (n : ℕ) (i : Fin n) : Exchangeable (gapTypeLaw n i) := by
  classical
  intro σ
  have hm : Measurable (permuteCoordinates σ) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply (σ j))
  have hval : ∀ S : Finset (Fin n), permuteCoordinates σ (gapValuation n i S) =
      gapValuation n i (σ.symm.finsetCongr S) := by
    intro S
    funext j
    simp [permuteCoordinates,gapValuation,Equiv.finsetCongr_apply]
  have hfamily : (gapSubsets n i).map σ.symm.finsetCongr.toEmbedding = gapSubsets n i := by
    rw [Equiv.finsetCongr_toEmbedding,gapSubsets,← Finset.powersetCard_map]
    simp
  unfold gapTypeLaw uniformAtoms
  rw [Measure.map_smul,Measure.map_finset_sum hm.aemeasurable]
  simp_rw [Measure.map_dirac,hval]
  congr 1
  have hsum := Finset.sum_map (gapSubsets n i) σ.symm.finsetCongr.toEmbedding
    (fun S => Measure.dirac (gapValuation n i S))
  rw [hfamily] at hsum
  exact hsum.symm

private lemma gap_exchangeable (n : ℕ) : Exchangeable (exchangeableGapLaw n) := by
  intro σ
  have hm : Measurable (permuteCoordinates σ) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply (σ j))
  unfold exchangeableGapLaw
  rw [Measure.map_add _ _ hm,Measure.map_smul,Measure.map_dirac,Measure.map_finset_sum hm.aemeasurable]
  simp only [permuteCoordinates,Measure.map_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [type_exchangeable n i σ]

private lemma gap_finite_support (n : ℕ) :
    ∃ S : Finset (Valuations n), ∀ᵐ v ∂exchangeableGapLaw n, v ∈ S := by
  classical
  let S : Finset (Valuations n) := insert (fun _ => 0)
    (Finset.univ.biUnion (fun i : Fin n => (gapSubsets n i).image (gapValuation n i)))
  have hzero : (fun _ : Fin n => (0:ℝ)) ∈ S := Finset.mem_insert_self _ _
  have hmem : ∀ (i : Fin n) (T : Finset (Fin n)), T ∈ gapSubsets n i → gapValuation n i T ∈ S := by
    intro i T hT
    apply Finset.mem_insert_of_mem
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨T,hT,rfl⟩⟩
  refine ⟨S,?_⟩
  unfold exchangeableGapLaw
  rw [ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure (by simpa using hzero) _
  · rw [ae_finsetSum_measure_iff]
    intro i _
    apply Measure.ae_smul_measure
    unfold gapTypeLaw uniformAtoms
    apply Measure.ae_smul_measure
    rw [ae_finsetSum_measure_iff]
    intro T hT
    simpa using hmem i T hT

end MinBuyingGapValidProof

theorem solution (n : ℕ) :
    ValidLaw (exchangeableGapLaw n) ∧ Exchangeable (exchangeableGapLaw n) ∧
    ∃ S : Finset (Valuations n), ∀ᵐ v ∂exchangeableGapLaw n, v ∈ S := by
  exact ⟨⟨MinBuyingGapValidProof.gap_probability n,MinBuyingGapValidProof.gap_nonneg n⟩,
    MinBuyingGapValidProof.gap_exchangeable n,MinBuyingGapValidProof.gap_finite_support n⟩
