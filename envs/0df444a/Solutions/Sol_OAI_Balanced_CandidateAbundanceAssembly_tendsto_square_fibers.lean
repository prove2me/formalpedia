-- Prove2me | solution 1 for OAI.Balanced.CandidateAbundanceAssembly.tendsto_square_fibers
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:18:09.811973+00:00
-- url     : https://prove2.me/submissions/4e23ad9d-2297-4652-af34-a4285823b031

import Mathlib
import Definitions.Def_OAIQ63Br002
import Definitions.Def_OAIQ63Br003

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_PartialAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PartialAlignment
open TupleAlignment

variable {F : Type*}

theorem alignment_exponent_identity (J : Finset (Fin 4)) :
    (freePositions J).card + (4 - (fixedPositions J).card) =
      2 * (freshGenerators J).card := by
  have h : ∀ J : Finset (Fin 4),
      (freePositions J).card + (4 - (fixedPositions J).card) =
        2 * (freshGenerators J).card := by decide
  exact h J

variable [Field F]

section Finite
variable [Fintype F] [DecidableEq F]

theorem card_alignedPartialOffsets_le (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    Fintype.card (AlignedPartialOffsets d hd σ g c J a) ≤
      Fintype.card F ^ (freePositions J).card := by
  calc
    Fintype.card (AlignedPartialOffsets d hd σ g c J a) ≤
        Fintype.card ({i : Fin 4 // i ∈ freePositions J} → F) :=
      Fintype.card_le_of_injective _
        (alignedFreeCoordinates_injective d hd σ g hg c J a)
    _ = _ := by simp

theorem partial_alignment_probability_le (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    ((PMF.uniformOfFintype (PartialOffsets J a)).toOuterMeasure
      {o | ∀ i, OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)}).toReal ≤
      (Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions J).card) := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]
  change (Fintype.card (AlignedPartialOffsets d hd σ g c J a) : ℝ) /
    (Fintype.card (PartialOffsets J a) : ℝ) ≤ _
  rw [card_partialOffsets, Nat.cast_pow]
  have hcard : (Fintype.card (AlignedPartialOffsets d hd σ g c J a) : ℝ) ≤
      (Fintype.card F : ℝ) ^ (freePositions J).card := by
    exact_mod_cast card_alignedPartialOffsets_le d hd σ g hg c J a
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    (Fintype.card (AlignedPartialOffsets d hd σ g c J a) : ℝ) /
        (Fintype.card F : ℝ) ^ (2 * (freshGenerators J).card) ≤
      (Fintype.card F : ℝ) ^ (freePositions J).card /
        (Fintype.card F : ℝ) ^ (2 * (freshGenerators J).card) :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ = _ := by
      rw [← alignment_exponent_identity J, pow_add, div_mul_eq_div_div,
        div_self (pow_ne_zero _ hq), one_div, inv_pow]

theorem original_conditional_alignment_probability_le (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    (((PMF.uniformOfFintype (Fin 4 → Bool → F)).filter
      {o | ∀ i ∈ J, o i = a i} (partialOffsets_supported J a)).toOuterMeasure
      {o | ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)}).toReal ≤
      (Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions J).card) := by
  rw [partialOffsets_conditional_law, PMF.toOuterMeasure_map_apply]
  exact partial_alignment_probability_le d hd σ g hg c J a

end Finite
end Balanced.PartialAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_GlobalPartialAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PartialAlignment
open TupleAlignment ConditionalRestriction

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem global_conditional_alignment_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F)
    (hg : ∀ i, T.generator i ≠ g) (c : F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (((PMF.uniformOfFintype (MergedPairs F)).filter
      {M | ∀ d, d ∈ D → M d = a d} (fixed_supported (fun d => d ∈ D) a)).toOuterMeasure
      {M | ∀ i, OnLine (tuplePoint M T i) (g,c)}).toReal ≤
      (Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions (exposedTupleIndices T D)).card) := by
  let hd := adjacent_ne_of_injective T hT
  let E : Set (Fin 4 → Bool → F) :=
    {o | ∀ i, OnLine (tuplePositionEquiv T.generator hd T.side o i) (g,c)}
  have h := congrArg (fun law => (law.toOuterMeasure E).toReal)
    (global_exposed_tuple_law T hT D a)
  rw [PMF.toOuterMeasure_map_apply] at h
  calc
    _ = (((PMF.uniformOfFintype (Fin 4 → Bool → F)).filter
        {o | ∀ i ∈ exposedTupleIndices T D, o i = a (T.generator i)}
        (partialOffsets_supported (exposedTupleIndices T D)
          (fun i => a (T.generator i)))).toOuterMeasure E).toReal := h
    _ ≤ _ := original_conditional_alignment_probability_le
      T.generator hd T.side g hg c (exposedTupleIndices T D) (fun i => a (T.generator i))

theorem canonical_conditional_alignment_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F)
    (hg : ∀ i, T.generator i ≠ g) (c : F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure
      {M | ∀ i, OnLine (tuplePoint M T i) (g,c)}).toReal ≤
      (Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions (exposedTupleIndices T D)).card) := by
  simpa only [offsetLaw_eq_uniform] using
    global_conditional_alignment_probability_le T hT g hg c D a

end
end Balanced.PartialAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_GeneratorEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Finset

section FiniteLabels
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem card_restrictedGeneratorLabels (old : Finset α) (mask : Finset (Fin 4)) :
    (restrictedGeneratorLabels old mask).card =
      old.card ^ mask.card * Fintype.card α ^ (4 - mask.card) := by
  rw [restrictedGeneratorLabels, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, Finset.card_univ]
  rw [Finset.prod_ite]
  have hcomp : ((Finset.univ : Finset (Fin 4)) \ mask).card = 4 - mask.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp
  simp [← Finset.sdiff_eq_filter, hcomp]

theorem generatorLabelsWithOldCount_subset (old : Finset α) (j : ℕ) :
    generatorLabelsWithOldCount old j ⊆
      (Finset.univ.powersetCard j).biUnion (restrictedGeneratorLabels old) := by
  intro g hg
  let mask : Finset (Fin 4) := Finset.univ.filter (fun i => g i ∈ old)
  have hmask : mask.card = j := (Finset.mem_filter.mp hg).2
  refine Finset.mem_biUnion.mpr ⟨mask,
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hmask⟩, ?_⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  by_cases hi : i ∈ mask
  · simpa only [ite_eq_left hi] using (Finset.mem_filter.mp hi).2
  · simp [hi]

theorem card_generatorLabelsWithOldCount_le (old : Finset α) (j : ℕ) :
    (generatorLabelsWithOldCount old j).card ≤
      Nat.choose 4 j * old.card ^ j * Fintype.card α ^ (4 - j) := by
  calc
    (generatorLabelsWithOldCount old j).card ≤
        ((Finset.univ.powersetCard j).biUnion (restrictedGeneratorLabels old)).card :=
      Finset.card_le_card (generatorLabelsWithOldCount_subset old j)
    _ ≤ ∑ mask ∈ Finset.univ.powersetCard j, (restrictedGeneratorLabels old mask).card :=
      Finset.card_biUnion_le
    _ = ∑ _mask ∈ (Finset.univ : Finset (Fin 4)).powersetCard j,
        old.card ^ j * Fintype.card α ^ (4 - j) := by
      apply Finset.sum_congr rfl
      intro mask hmask
      rw [card_restrictedGeneratorLabels, (Finset.mem_powersetCard.mp hmask).2]
    _ = Nat.choose 4 j * old.card ^ j * Fintype.card α ^ (4 - j) := by
      simp [Nat.mul_assoc]

theorem card_tupleCodesWithOldCount_le (old : Finset α) (j : ℕ) :
    (tupleCodesWithOldCount old j).card ≤
      16 * (Nat.choose 4 j * old.card ^ j * Fintype.card α ^ (4 - j)) := by
  rw [tupleCodesWithOldCount, Finset.product_eq_sprod, Finset.card_product, Finset.card_univ]
  have hbits : Fintype.card (Fin 4 → Bool) = 16 := by decide
  rw [hbits, Nat.mul_comm]
  exact Nat.mul_le_mul_left 16 (card_generatorLabelsWithOldCount_le old j)

end FiniteLabels

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateExposure

noncomputable section
open scoped Classical BigOperators
open PartialAlignment TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem pmf_outer_ne_top {α : Type*} (p : PMF α) (E : Set α) :
    p.toOuterMeasure E ≠ ⊤ := by
  rw [PMF.toOuterMeasure_apply]
  exact p.tsum_coe_indicator_ne_top E

private theorem pmf_real_mono {α : Type*} (p : PMF α) {E H : Set α}
    (h : E ∩ p.support ⊆ H) :
    (p.toOuterMeasure E).toReal ≤ (p.toOuterMeasure H).toReal :=
  ENNReal.toReal_mono (pmf_outer_ne_top p H) (p.toOuterMeasure_mono h)

theorem prescribed_line_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F)
    (hg : ∀ i, T.generator i ≠ g) (c : F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    conditionalProbability D a {M | ∀ i, OnLine (tuplePoint M T i) (g,c)} ≤
      (Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions (exposedTupleIndices T D)).card) :=
  canonical_conditional_alignment_probability_le T hT g hg c D a

theorem unspecified_line_probability_le_sum (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F)
    (hg : ∀ i, T.generator i ≠ g)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    conditionalProbability D a (alignedInDirection T g) ≤
      (Fintype.card F : ℝ) *
        ((Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions (exposedTupleIndices T D)).card)) := by
  let E : F → Set (MergedPairs F) := fun c => {M | ∀ i, OnLine (tuplePoint M T i) (g,c)}
  have hE : alignedInDirection T g = ⋃ c, E c := by ext M; simp [alignedInDirection, E]
  unfold conditionalProbability
  rw [hE]
  have hfinite : (∑ c, (exposedLaw D a).toOuterMeasure (E c)) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.mpr (fun c _ => pmf_outer_ne_top _ _)
  calc
    _ ≤ (∑ c, (exposedLaw D a).toOuterMeasure (E c)).toReal :=
      ENNReal.toReal_mono hfinite (MeasureTheory.measure_iUnion_fintype_le _ E)
    _ = ∑ c, ((exposedLaw D a).toOuterMeasure (E c)).toReal := by
      rw [ENNReal.toReal_sum (fun c _ => pmf_outer_ne_top _ _)]
    _ ≤ ∑ _c : F, (Fintype.card F : ℝ)⁻¹ ^
        (4 - (fixedPositions (exposedTupleIndices T D)).card) := by
      apply Finset.sum_le_sum
      intro c _
      exact prescribed_line_probability_le T hT g hg c D a
    _ = _ := by simp

theorem unspecified_line_probability_le_of_fixed (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F)
    (hg : ∀ i, T.generator i ≠ g)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (hfixed : (fixedPositions (exposedTupleIndices T D)).Nonempty) :
    conditionalProbability D a (alignedInDirection T g) ≤
      (Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions (exposedTupleIndices T D)).card) := by
  obtain ⟨i, hi⟩ := hfixed
  have hold : T.generator i ∈ D ∧ T.generator (i + 1) ∈ D := by
    simpa only [fixedPositions, exposedTupleIndices, Finset.mem_filter,
      Finset.mem_univ, true_and] using hi
  let c := lineEval g (tuplePoint a T i)
  apply le_trans (pmf_real_mono (exposedLaw D a) (H :=
    {M | ∀ j, OnLine (tuplePoint M T j) (g,c)}) ?_)
    (prescribed_line_probability_le T hT g hg c D a)
  rintro M ⟨⟨b, hb⟩, hsupport⟩
  have hexposed : ∀ d, d ∈ D → M d = a d :=
    (PMF.mem_support_filter_iff (canonical_exposure_supported D a)).mp hsupport |>.1
  have hpoint : tuplePoint M T i = tuplePoint a T i := by
    simp only [tuplePoint, constituent, hexposed _ hold.1, hexposed _ hold.2]
  have hbc : b = c := by
    have hi := hb i
    rw [hpoint] at hi
    exact hi.symm
  change ∀ j, OnLine (tuplePoint M T j) (g,c)
  simpa only [hbc] using hb

private theorem alignmentExponent_le_three (j : ℕ) : alignmentExponent j ≤ 3 := by
  unfold alignmentExponent
  split_ifs <;> omega

private theorem alignmentExponent_le_nonfixed (J : Finset (Fin 4))
    (h : (fixedPositions J).card ≠ 0) :
    alignmentExponent J.card ≤ 4 - (fixedPositions J).card := by
  have htable : ∀ J : Finset (Fin 4), (fixedPositions J).card ≠ 0 →
      alignmentExponent J.card ≤ 4 - (fixedPositions J).card := by decide
  exact htable J h

theorem unspecified_line_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F)
    (hg : ∀ i, T.generator i ≠ g)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    conditionalProbability D a (alignedInDirection T g) ≤
      (Fintype.card F : ℝ)⁻¹ ^ alignmentExponent (exposedTupleIndices T D).card := by
  let J := exposedTupleIndices T D
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := by positivity
  have hi0 : 0 ≤ (Fintype.card F : ℝ)⁻¹ := by positivity
  have hi1 : (Fintype.card F : ℝ)⁻¹ ≤ 1 := by simpa using (inv_le_one₀ (by positivity : (0 : ℝ) < Fintype.card F)).mpr hq
  by_cases hf : (fixedPositions J).card = 0
  · have h := unspecified_line_probability_le_sum T hT g hg D a
    change _ ≤ (Fintype.card F : ℝ) * ((Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions J).card)) at h
    rw [hf] at h
    simp only [Nat.sub_zero] at h
    have heq : (Fintype.card F : ℝ) * (Fintype.card F : ℝ)⁻¹ ^ 4 =
        (Fintype.card F : ℝ)⁻¹ ^ 3 := by field_simp
    rw [heq] at h
    exact h.trans (pow_le_pow_of_le_one hi0 hi1 (alignmentExponent_le_three J.card))
  · exact (unspecified_line_probability_le_of_fixed T hT g hg D a
      (Finset.card_pos.mp (Nat.pos_of_ne_zero hf))).trans
        (pow_le_pow_of_le_one hi0 hi1 (alignmentExponent_le_nonfixed J hf))

theorem successful_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F)
    (hg : ∀ i, T.generator i ≠ g)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    conditionalProbability D a (successfulInDirection T g) ≤
      (Fintype.card F : ℝ)⁻¹ ^ alignmentExponent (exposedTupleIndices T D).card := by
  apply le_trans (pmf_real_mono (exposedLaw D a) ?_)
    (unspecified_line_probability_le T hT g hg D a)
  exact fun _ h => h.1.1

end
end Balanced.CandidateExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateFirstMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateExposure

noncomputable section
open scoped Classical BigOperators
open PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem card_tupleCodesWithOldCount_le_bounded (D : Finset (Direction F))
    (m j : ℕ) (hD : D.card ≤ m) (hj : j ≤ 4) :
    (tupleCodesWithOldCount D j).card ≤
      (4096 * (m + 1) ^ 4) * Fintype.card F ^ (4 - j) := by
  have hchoose : Nat.choose 4 j ≤ 16 := by interval_cases j <;> decide
  have hpow : D.card ^ j ≤ (m + 1) ^ 4 := by
    exact (Nat.pow_le_pow_left (by omega : D.card ≤ m + 1) j).trans
      (Nat.pow_le_pow_right (by omega) hj)
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hdir : Fintype.card (Direction F) ≤ 2 * Fintype.card F := by
    simp only [Direction, Fintype.card_option]
    omega
  have htwo : 2 ^ (4 - j) ≤ 16 := by
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 - j ≤ 4))
  calc
    (tupleCodesWithOldCount D j).card ≤
        16 * (Nat.choose 4 j * D.card ^ j * Fintype.card (Direction F) ^ (4 - j)) :=
      card_tupleCodesWithOldCount_le D j
    _ ≤ 16 * (16 * (m + 1) ^ 4 * (2 * Fintype.card F) ^ (4 - j)) := by gcongr
    _ = 16 * (16 * (m + 1) ^ 4 * (2 ^ (4 - j) * Fintype.card F ^ (4 - j))) := by rw [Nat.mul_pow]
    _ ≤ 16 * (16 * (m + 1) ^ 4 * (16 * Fintype.card F ^ (4 - j))) := by gcongr
    _ = _ := by ring

theorem card_tuplesWithExposure_le (g : Direction F) (D : Finset (Direction F))
    (m j : ℕ) (hD : D.card ≤ m) (hj : j ≤ 4) :
    (tuplesWithExposure g D j).card ≤
      (4096 * (m + 1) ^ 4) * Fintype.card F ^ (4 - j) := by
  apply le_trans (Finset.card_le_card_of_injOn
    (fun T : FourTuple F => (T.generator, T.side)) ?_ ?_)
    (card_tupleCodesWithOldCount_le_bounded D m j hD hj)
  · intro T hT
    have hjT := (Finset.mem_filter.mp hT).2
    change (T.generator, T.side) ∈ tupleCodesWithOldCount D j
    simpa [tupleCodesWithOldCount, generatorLabelsWithOldCount, exposedTupleIndices] using hjT
  · intro T _ U _ h
    cases T
    cases U
    cases h
    rfl

private theorem counting_alignment_scale (q : ℝ) (hq : 1 ≤ q) (j : ℕ) (hj : j ≤ 4) :
    q ^ (4 - j) * q⁻¹ ^ alignmentExponent j ≤ if j = 0 then q else 1 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  interval_cases j <;> norm_num [alignmentExponent] <;> field_simp <;> nlinarith

theorem success_sum_withExposure_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m j : ℕ) (hD : D.card ≤ m) (hj : j ≤ 4) :
    (∑ T ∈ tuplesWithExposure g D j,
      conditionalProbability D a (successfulInDirection T g)) ≤
      (4096 * (m + 1) ^ 4 : ℝ) * (if j = 0 then (Fintype.card F : ℝ) else 1) := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  calc
    _ ≤ ∑ _T ∈ tuplesWithExposure g D j,
        (Fintype.card F : ℝ)⁻¹ ^ alignmentExponent j := by
      apply Finset.sum_le_sum
      intro T hT
      obtain ⟨hgood, hjT⟩ := Finset.mem_filter.mp hT
      obtain ⟨hinj, htarget⟩ := (Finset.mem_filter.mp hgood).2
      simpa only [hjT] using successful_probability_le T hinj g htarget D a
    _ = ((tuplesWithExposure g D j).card : ℝ) *
        (Fintype.card F : ℝ)⁻¹ ^ alignmentExponent j := by simp
    _ ≤ ((4096 * (m + 1) ^ 4 : ℝ) * (Fintype.card F : ℝ) ^ (4 - j)) *
        (Fintype.card F : ℝ)⁻¹ ^ alignmentExponent j := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_tuplesWithExposure_le g D m j hD hj
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (counting_alignment_scale _ hq j hj) (by positivity)

theorem successProbabilitySum_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    successProbabilitySum g D a ≤ (20480 * (m + 1) ^ 4 : ℝ) * Fintype.card F := by
  have hpartition := Finset.sum_fiberwise_of_maps_to
    (s := eligibleTuples g) (t := Finset.range 5)
    (g := fun T => (exposedTupleIndices T D).card)
    (fun T _ => Finset.mem_range.mpr (by
      have h := Finset.card_le_univ (exposedTupleIndices T D)
      simp only [Fintype.card_fin] at h
      omega))
    (fun T => conditionalProbability D a (successfulInDirection T g))
  unfold successProbabilitySum
  rw [← hpartition]
  change (∑ j ∈ Finset.range 5, ∑ T ∈ tuplesWithExposure g D j,
    conditionalProbability D a (successfulInDirection T g)) ≤ _
  calc
    _ ≤ ∑ j ∈ Finset.range 5,
        (4096 * (m + 1) ^ 4 : ℝ) * (if j = 0 then (Fintype.card F : ℝ) else 1) := by
      apply Finset.sum_le_sum
      intro j hj
      exact success_sum_withExposure_le g D a m j hD (by
        have := Finset.mem_range.mp hj
        omega)
    _ ≤ _ := by
      norm_num [Finset.sum_range_succ]
      have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
      have h := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ (m + 1) ^ 4)
      nlinarith

theorem overlapProbabilitySum_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    overlapProbabilitySum g D a ≤ (16384 * (m + 1) ^ 4 : ℝ) := by
  have hpartition := Finset.sum_fiberwise_eq_sum_filter (eligibleTuples g)
    (Finset.Icc 1 4) (fun T => (exposedTupleIndices T D).card)
    (fun T => conditionalProbability D a (successfulInDirection T g))
  have hfilter : (eligibleTuples g).filter
      (fun T => (exposedTupleIndices T D).card ∈ Finset.Icc 1 4) =
      (eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card) := by
    apply Finset.filter_congr
    intro T _
    have h := Finset.card_le_univ (exposedTupleIndices T D)
    simp only [Fintype.card_fin] at h
    simp only [Finset.mem_Icc]
    omega
  rw [hfilter] at hpartition
  unfold overlapProbabilitySum
  rw [← hpartition]
  change (∑ j ∈ Finset.Icc 1 4, ∑ T ∈ tuplesWithExposure g D j,
    conditionalProbability D a (successfulInDirection T g)) ≤ _
  calc
    _ ≤ ∑ _j ∈ Finset.Icc 1 4, (4096 * (m + 1) ^ 4 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hj0, hj4⟩ := Finset.mem_Icc.mp hj
      have h := success_sum_withExposure_le g D a m j hD hj4
      simpa only [ite_eq_right (by omega : j ≠ 0), mul_one] using h
    _ = _ := by norm_num; ring

end
end Balanced.CandidateExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateConditionalMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateExposure

noncomputable section
open scoped Classical BigOperators
open MeasureTheory PartialAlignment

section FiniteMean
variable {Ω A : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

theorem integral_eventCount_eq_sum (p : PMF Ω) (s : Finset A) (E : A → Set Ω) :
    (∫ ω, ((s.filter (fun a => ω ∈ E a)).card : ℝ) ∂p.toMeasure) =
      ∑ a ∈ s, (p.toOuterMeasure (E a)).toReal := by
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [PMF.toOuterMeasure_apply_fintype,
    ENNReal.toReal_sum (fun ω _ => by
      by_cases h : ω ∈ E a
      · simpa only [Set.indicator_of_mem h] using p.apply_ne_top ω
      · simp [Set.indicator_of_notMem h])]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : ω ∈ E a <;> simp [h]
end FiniteMean

end
end Balanced.CandidateExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteFixedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ConditionalRestriction

noncomputable section
open scoped Classical BigOperators
open MeasureTheory TupleAlignment

variable {D A : Type*} [Fintype D] [Fintype A] [DecidableEq D] [Nonempty A]

theorem uniform_map_fixArray (P : D → Prop) (a : D → A) :
    (PMF.uniformOfFintype (D → A)).map (fixArray P a) =
      (PMF.uniformOfFintype (D → A)).filter
        {ω | ∀ d, P d → ω d = a d} (fixed_supported P a) := by
  let e : {d : D // ¬ P d} ↪ D := ⟨Subtype.val, Subtype.val_injective⟩
  have hr := uniform_map_restrict (A := A) e
  have he := uniform_map_equiv (fixedFreshEquiv P a).symm
  rw [uniform_fixed_filter, ← he, PMF.map_comp, ← hr, PMF.map_comp]
  congr 1

variable [MeasurableSpace A] [MeasurableSingletonClass A]

theorem pi_uniform_toMeasure :
    Measure.pi (fun _ : D => (PMF.uniformOfFintype A).toMeasure) =
      (PMF.uniformOfFintype (D → A)).toMeasure := by
  apply Measure.ext_of_singleton
  intro ω
  rw [Measure.pi_singleton, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp [PMF.uniformOfFintype_apply, Nat.cast_pow, ENNReal.inv_pow]

theorem integral_fixArray_eq_filtered (P : D → Prop) (a : D → A) (f : (D → A) → ℝ) :
    (∫ ω, f (fixArray P a ω) ∂Measure.pi
      (fun _ : D => (PMF.uniformOfFintype A).toMeasure)) =
    ∫ ω, f ω ∂((PMF.uniformOfFintype (D → A)).filter
      {ω | ∀ d, P d → ω d = a d} (fixed_supported P a)).toMeasure := by
  rw [pi_uniform_toMeasure, ← uniform_map_fixArray,
    ← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  symm
  exact integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable

end
end Balanced.ConditionalRestriction

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_RootPatternModel
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Balanced.TupleAlignment

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

attribute [local instance] OAI.Balanced.TupleAlignment.instMeasurableSpace_solutions
theorem rootPatternModel_measure (g : Direction F) :
    (rootPatternModel g).measure = (offsetLaw F).toMeasure := by
  change Measure.pi (fun _ : Direction F =>
    (PMF.uniformOfFintype (Bool → F)).toMeasure) = (offsetLaw F).toMeasure
  apply Measure.ext_of_singleton
  intro M
  simp only [Measure.pi_singleton,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, offsetLaw, Finset.prod_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    MergedPairs, Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]

theorem rootPatternModel_fixedExpectation_exposed (g : Direction F)
    (K : Finset (Direction F)) (x : MergedPairs F) (f : MergedPairs F → ℝ) :
    (rootPatternModel g).fixedExpectation K x f =
      ∫ M, f M ∂(CandidateExposure.exposedLaw K x).toMeasure := by
  have h := ConditionalRestriction.integral_fixArray_eq_filtered
    (fun d => d ∈ K) x f
  simp only [CandidateExposure.exposedLaw, PartialAlignment.offsetLaw_eq_uniform]
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with M
  congr 1
  funext d
  simp only [PatternModel.fixCoordinates, ConditionalRestriction.fixArray]
  split_ifs <;> rfl

end Balanced.TupleAlignment

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateLabelBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateExposure

noncomputable section
open scoped Classical BigOperators
open TupleAlignment PartialAlignment MeasureTheory

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [Fintype F] in

theorem not_disjoint_generatorSet_iff (T : FourTuple F) (D : Finset (Direction F)) :
    ¬ Disjoint (generatorSet T) D ↔ 0 < (exposedTupleIndices T D).card := by
  rw [Finset.not_disjoint_iff, Finset.card_pos]
  constructor
  · rintro ⟨d, hd, hD⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hD⟩⟩
  · rintro ⟨i, hi⟩
    exact ⟨T.generator i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
      (Finset.mem_filter.mp hi).2⟩

end
end Balanced.CandidateExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced.PatternModel

variable (P : PatternModel)

lemma measurable_fixCoordinates (K : Finset P.Color) (x : P.Sample) :
    Measurable (P.fixCoordinates K x) := by
  classical
  apply Measurable.of_eval
  intro c
  by_cases hc : c ∈ K
  · simp [fixCoordinates, hc]
  · simpa [fixCoordinates, hc] using (measurable_pi_apply c)

lemma measurable_indicator (a : P.Label) : Measurable (P.indicator a) :=
  measurable_const.indicator (P.eventMeasurable a)

lemma indicator_nonneg (a : P.Label) (ω : P.Sample) : 0 ≤ P.indicator a ω := by
  classical
  simp only [indicator, Set.indicator_apply]
  split_ifs <;> norm_num

lemma indicator_le_one (a : P.Label) (ω : P.Sample) : P.indicator a ω ≤ 1 := by
  classical
  simp only [indicator, Set.indicator_apply]
  split_ifs <;> norm_num

lemma integrable_fixed_of_bound (K : Finset P.Color) (x : P.Sample)
    {f : P.Sample → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ ω, ‖f ω‖ ≤ C) :
    Integrable (fun ω => f (P.fixCoordinates K x ω)) P.measure := by
  exact Integrable.of_bound
    (hf.comp (P.measurable_fixCoordinates K x)).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => hC _)

lemma integrable_fixed_indicator (K : Finset P.Color) (x : P.Sample) (a : P.Label) :
    Integrable (fun ω => P.indicator a (P.fixCoordinates K x ω)) P.measure := by
  apply P.integrable_fixed_of_bound K x (P.measurable_indicator a) 1
  intro ω
  simpa only [Real.norm_eq_abs, abs_of_nonneg (P.indicator_nonneg a ω)] using
    P.indicator_le_one a ω

lemma fixedExpectation_nonneg (K : Finset P.Color) (x : P.Sample)
    {f : P.Sample → ℝ} (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ P.fixedExpectation K x f :=
  integral_nonneg fun _ => hf _

lemma fixedExpectation_indicator_nonneg (K : Finset P.Color) (x : P.Sample) (a : P.Label) :
    0 ≤ P.fixedExpectation K x (P.indicator a) :=
  P.fixedExpectation_nonneg K x (P.indicator_nonneg a)

lemma fixedExpectation_indicator_le_one (K : Finset P.Color) (x : P.Sample) (a : P.Label) :
    P.fixedExpectation K x (P.indicator a) ≤ 1 := by
  calc
    P.fixedExpectation K x (P.indicator a) ≤ P.fixedExpectation K x (fun _ => 1) := by
      apply integral_mono (P.integrable_fixed_indicator K x a) (integrable_const 1)
      intro ω
      exact P.indicator_le_one a _
    _ = 1 := P.fixedExpectation_const K x 1

lemma positiveProduct_nonneg (K₀ : Finset P.Color) (x : P.Sample)
    (as : List P.Label) (ω : P.Sample) : 0 ≤ P.positiveProduct K₀ x as ω := by
  apply List.prod_nonneg
  intro t ht
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp ht
  exact add_nonneg (P.indicator_nonneg a ω) (P.fixedExpectation_indicator_nonneg K₀ x a)

lemma positiveProduct_le (K₀ : Finset P.Color) (x : P.Sample)
    (as : List P.Label) (ω : P.Sample) : P.positiveProduct K₀ x as ω ≤ 2 ^ as.length := by
  induction as with
  | nil => simp [positiveProduct]
  | cons a as ih =>
    simp only [positiveProduct, List.map_cons, List.prod_cons, List.length_cons]
    rw [pow_succ']
    apply mul_le_mul _ ih (P.positiveProduct_nonneg K₀ x as ω) (by norm_num)
    have h₁ := P.indicator_le_one a ω
    have h₂ := P.fixedExpectation_indicator_le_one K₀ x a
    linarith

lemma measurable_positiveProduct (K₀ : Finset P.Color) (x : P.Sample)
    (as : List P.Label) : Measurable (P.positiveProduct K₀ x as) := by
  induction as with
  | nil => exact measurable_const
  | cons a as ih =>
    exact ((P.measurable_indicator a).add measurable_const).mul ih

lemma integrable_fixed_positiveProduct (K₀ K : Finset P.Color) (x y : P.Sample)
    (as : List P.Label) :
    Integrable (fun ω => P.positiveProduct K₀ x as (P.fixCoordinates K y ω)) P.measure := by
  apply P.integrable_fixed_of_bound K y (P.measurable_positiveProduct K₀ x as) (2 ^ as.length)
  intro ω
  simpa only [Real.norm_eq_abs, abs_of_nonneg (P.positiveProduct_nonneg K₀ x as ω)] using
    P.positiveProduct_le K₀ x as ω

lemma productWeight_nonneg (K₀ : Finset P.Color) (x : P.Sample) (as : List P.Label) :
    0 ≤ P.productWeight K₀ x as :=
  P.fixedExpectation_nonneg K₀ x (P.positiveProduct_nonneg K₀ x as)

lemma positiveProduct_perm (K₀ : Finset P.Color) (x : P.Sample)
    {as bs : List P.Label} (h : as.Perm bs) :
    P.positiveProduct K₀ x as = P.positiveProduct K₀ x bs := by
  funext ω
  exact (h.map _).prod_eq

lemma productWeight_perm (K₀ : Finset P.Color) (x : P.Sample)
    {as bs : List P.Label} (h : as.Perm bs) :
    P.productWeight K₀ x as = P.productWeight K₀ x bs := by
  unfold productWeight
  rw [P.positiveProduct_perm K₀ x h]

lemma indicator_eq_of_agree (a : P.Label) (ω η : P.Sample)
    (h : ∀ c ∈ P.support a, ω c = η c) : P.indicator a ω = P.indicator a η := by
  classical
  have he := P.dependsOn a ω η h
  by_cases hω : ω ∈ P.event a
  · have hη := he.mp hω
    simp [indicator, hω, hη]
  · have hη : η ∉ P.event a := fun hη => hω (he.mpr hη)
    simp [indicator, hω, hη]

lemma positiveProduct_eq_of_agree (K₀ : Finset P.Color) (x : P.Sample)
    (as : List P.Label) (ω η : P.Sample)
    (h : ∀ a ∈ as, ∀ c ∈ P.support a, ω c = η c) :
    P.positiveProduct K₀ x as ω = P.positiveProduct K₀ x as η := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    change (P.indicator a ω + _) * P.positiveProduct K₀ x as ω =
      (P.indicator a η + _) * P.positiveProduct K₀ x as η
    rw [P.indicator_eq_of_agree a ω η (h a (by simp))]
    rw [ih (fun b hb => h b (by simp [hb]))]

lemma positiveProduct_dependsOn (K₀ : Finset P.Color) (x : P.Sample)
    (as : List P.Label) (ω η : P.Sample)
    (h : ∀ c ∈ K₀ ∪ P.additionalSupport K₀ as, ω c = η c) :
    P.positiveProduct K₀ x as ω = P.positiveProduct K₀ x as η := by
  classical
  apply P.positiveProduct_eq_of_agree K₀ x as ω η
  intro a ha c hc
  apply h c
  by_cases hc₀ : c ∈ K₀
  · exact Finset.mem_union_left _ hc₀
  · apply Finset.mem_union_right
    simp only [additionalSupport, Finset.mem_biUnion, List.mem_toFinset, Finset.mem_sdiff]
    exact ⟨a, ha, hc, hc₀⟩

end Balanced.PatternModel

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Balanced.Pattern

variable {Ω I : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {E : I → Type*} [∀ i, MeasurableSpace (E i)]
variable {ξ : (i : I) → Ω → E i}

theorem indepFun_of_disjoint_supports
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i))
    (S T : Finset I) (hST : Disjoint S T)
    (f : ((i : S) → E i) → ℝ) (g : ((i : T) → E i) → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    IndepFun (fun ω => f (fun i => ξ i ω))
      (fun ω => g (fun i => ξ i ω)) μ := by
  exact (hξ.indepFun_finset S T hST hξm).comp hf hg

theorem integral_prod_eq_zero_of_isolated [IsProbabilityMeasure μ]
    {A : Type*} [DecidableEq A] (s : Finset A) {a : A} (ha : a ∈ s)
    (X : A → Ω → ℝ)
    (hind : IndepFun (X a) (fun ω => ∏ b ∈ s.erase a, X b ω) μ)
    (hX : AEStronglyMeasurable (X a) μ)
    (hrest : AEStronglyMeasurable (fun ω => ∏ b ∈ s.erase a, X b ω) μ)
    (hmean : (∫ ω, X a ω ∂μ) = 0) :
    (∫ ω, ∏ b ∈ s, X b ω ∂μ) = 0 := by
  have hprod (ω : Ω) : (∏ b ∈ s, X b ω) =
      X a ω * ∏ b ∈ s.erase a, X b ω :=
    (Finset.mul_prod_erase s (fun b => X b ω) ha).symm
  simp_rw [hprod]
  rw [hind.integral_fun_mul_eq_mul_integral hX hrest, hmean, zero_mul]

theorem indepFun_pattern_prod
    {A : Type*} [DecidableEq A] [DecidableEq I]
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i))
    (C : A → Finset I)
    (F : (a : A) → ((i : C a) → E i) → ℝ)
    (hF : ∀ a, Measurable (F a))
    (s : Finset A) (a : A)
    (hdisj : ∀ b ∈ s, Disjoint (C a) (C b)) :
    IndepFun (fun ω => F a (fun i => ξ i ω))
      (fun ω => ∏ b ∈ s, F b (fun i => ξ i ω)) μ := by
  let U : Finset I := s.biUnion C
  let G : ((i : U) → E i) → ℝ := fun z =>
    ∏ b : s, F b (fun i => z ⟨i, Finset.mem_biUnion.mpr
      ⟨b, b.property, i.property⟩⟩)
  have hU : Disjoint (C a) U := by
    apply Finset.disjoint_left.mpr
    intro i hi hiU
    obtain ⟨b, hb, hib⟩ := Finset.mem_biUnion.mp hiU
    exact Finset.disjoint_left.mp (hdisj b hb) hi hib
  have hG : Measurable G := by
    apply Finset.measurable_fun_prod
    intro b _
    exact (hF b).comp (Measurable.of_eval (fun _ => measurable_pi_apply _))
  have hind := indepFun_of_disjoint_supports hξ hξm (C a) U hU (F a) G (hF a) hG
  have hGeq : (fun ω => G (fun i => ξ i ω)) =
      (fun ω => ∏ b ∈ s, F b (fun i => ξ i ω)) := by
    funext ω
    exact Finset.prod_coe_sort s (fun b => F b (fun i => ξ i ω))
  rw [hGeq] at hind
  exact hind

theorem integral_centered_pattern_prod_eq_zero [IsProbabilityMeasure μ]
    {A : Type*} [DecidableEq A] [DecidableEq I]
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i))
    (C : A → Finset I)
    (F : (a : A) → ((i : C a) → E i) → ℝ)
    (hF : ∀ a, Measurable (F a))
    (hFi : ∀ a, Integrable (fun ω => F a (fun i => ξ i ω)) μ)
    (s : Finset A) {a : A} (ha : a ∈ s)
    (hdisj : ∀ b ∈ s.erase a, Disjoint (C a) (C b)) :
    (∫ ω, ∏ b ∈ s,
      (F b (fun i => ξ i ω) - ∫ w, F b (fun i => ξ i w) ∂μ) ∂μ) = 0 := by
  let p : A → ℝ := fun b => ∫ w, F b (fun i => ξ i w) ∂μ
  let Fc : (b : A) → ((i : C b) → E i) → ℝ := fun b z => F b z - p b
  have hFc : ∀ b, Measurable (Fc b) := fun b => (hF b).sub_const (p b)
  have hXm (b : A) : Measurable (fun ω => Fc b (fun i => ξ i ω)) :=
    (hFc b).comp (Measurable.of_eval (fun coordinate => hξm coordinate))
  apply integral_prod_eq_zero_of_isolated s ha (fun b ω => Fc b (fun i => ξ i ω))
  · exact indepFun_pattern_prod hξ hξm C Fc hFc (s.erase a) a hdisj
  · exact (hXm a).aestronglyMeasurable
  · exact (Finset.measurable_fun_prod _ (fun b _ => hXm b)).aestronglyMeasurable
  · simp [Fc, p, integral_sub (hFi a) (integrable_const _)]

end Balanced.Pattern

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternModelCancellation
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Balanced.PatternProof

variable (P : PatternModel)

lemma measurable_fillFresh (K : Finset P.Color) (x : P.Sample) (a : P.Label) :
    Measurable (fillFresh P K x a) := by
  classical
  apply Measurable.of_eval
  intro c
  by_cases hc : c ∈ P.support a \ K
  · simpa [fillFresh, hc] using (measurable_pi_apply (⟨c, hc⟩ : ↥(P.support a \ K)))
  · simp [fillFresh, hc, measurable_const]

lemma measurable_indicator (a : P.Label) : Measurable (P.indicator a) :=
  measurable_const.indicator (P.eventMeasurable a)

lemma indicator_mem_Icc (a : P.Label) (ω : P.Sample) :
    P.indicator a ω ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  by_cases h : ω ∈ P.event a <;> simp [PatternModel.indicator, h]

lemma indicator_fillFresh_eq_fixed (K : Finset P.Color) (x ω : P.Sample) (a : P.Label) :
    P.indicator a (fillFresh P K x a (fun c => ω c)) =
      P.indicator a (P.fixCoordinates K x ω) := by
  classical
  have hcoords : ∀ c ∈ P.support a,
      fillFresh P K x a (fun c => ω c) c = P.fixCoordinates K x ω c := by
    intro c hc
    by_cases hK : c ∈ K <;> simp [fillFresh, PatternModel.fixCoordinates, hc, hK]
  have hmem := P.dependsOn a _ _ hcoords
  simp only [PatternModel.indicator, Set.indicator_apply, hmem]

theorem fixedExpectation_centered_prod_eq_zero
    (K : Finset P.Color) (x : P.Sample) (n : ℕ) (a : Fin n → P.Label)
    (i : Fin n)
    (hisol : ∀ j, i ≠ j → Disjoint (P.support (a i) \ K) (P.support (a j) \ K)) :
    P.fixedExpectation K x (fun ω => ∏ j,
      (P.indicator (a j) ω - P.fixedExpectation K x (P.indicator (a j)))) = 0 := by
  classical
  let : IsProbabilityMeasure P.measure := by
    unfold PatternModel.measure
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let C : Fin n → Finset P.Color := fun j => P.support (a j) \ K
  let F : (j : Fin n) → ((c : C j) → P.Value c) → ℝ :=
    fun j z => P.indicator (a j) (fillFresh P K x (a j) z)
  have hF (j : Fin n) : Measurable (F j) :=
    (measurable_indicator P (a j)).comp (measurable_fillFresh P K x (a j))
  have hξ : iIndepFun (fun c (ω : P.Sample) => ω c) P.measure := by
    exact iIndepFun_pi (fun _ => aemeasurable_id)
  have hFi (j : Fin n) : Integrable (fun ω : P.Sample => F j (fun c => ω c)) P.measure := by
    apply Integrable.of_mem_Icc 0 1
    · have hm : Measurable (fun ω : P.Sample => fun c : C j => ω c) :=
        Measurable.of_eval (fun color => measurable_pi_apply (color : P.Color))
      exact ((hF j).comp hm).aemeasurable
    · exact Filter.Eventually.of_forall (fun ω => indicator_mem_Icc P (a j) _)
  have hcanc := Balanced.Pattern.integral_centered_pattern_prod_eq_zero
    hξ (fun c => measurable_pi_apply c) C F hF hFi Finset.univ (Finset.mem_univ i)
    (fun j hj => hisol j (Finset.mem_erase.mp hj).1.symm)
  dsimp only [F, C] at hcanc
  simp_rw [indicator_fillFresh_eq_fixed] at hcanc
  simpa only [PatternModel.fixedExpectation] using hcanc

lemma measurable_fixedCoordinates (K : Finset P.Color) (x : P.Sample) :
    Measurable (P.fixCoordinates K x) := by
  classical
  apply Measurable.of_eval
  intro c
  by_cases hc : c ∈ K
  · simp [PatternModel.fixCoordinates, hc, measurable_const]
  · simpa [PatternModel.fixCoordinates, hc] using (measurable_pi_apply c)

lemma fixedExpectation_indicator_mem_Icc (K : Finset P.Color) (x : P.Sample) (a : P.Label) :
    P.fixedExpectation K x (P.indicator a) ∈ Set.Icc (0 : ℝ) 1 := by
  let : IsProbabilityMeasure P.measure := by
    unfold PatternModel.measure
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hm : Measurable (fun ω => P.indicator a (P.fixCoordinates K x ω)) :=
    (measurable_indicator P a).comp (measurable_fixedCoordinates P K x)
  have hr := fun ω => indicator_mem_Icc P a (P.fixCoordinates K x ω)
  have hi : Integrable (fun ω => P.indicator a (P.fixCoordinates K x ω)) P.measure :=
    Integrable.of_mem_Icc 0 1 hm.aemeasurable (Filter.Eventually.of_forall hr)
  constructor
  · exact integral_nonneg (fun ω => (hr ω).1)
  · have hb := integral_mono_ae hi (integrable_const (1 : ℝ))
      (Filter.Eventually.of_forall (fun ω => (hr ω).2))
    simpa [PatternModel.fixedExpectation] using hb

theorem abs_fixedExpectation_centered_prod_le
    (K : Finset P.Color) (x : P.Sample) (n : ℕ) (a : Fin n → P.Label) :
    |P.fixedExpectation K x (fun ω => ∏ j,
      (P.indicator (a j) ω - P.fixedExpectation K x (P.indicator (a j))))| ≤
    P.fixedExpectation K x (fun ω => ∏ j,
      (P.indicator (a j) ω + P.fixedExpectation K x (P.indicator (a j)))) := by
  classical
  let : IsProbabilityMeasure P.measure := by
    unfold PatternModel.measure
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let f : Fin n → P.Sample → ℝ := fun j ω => P.indicator (a j) (P.fixCoordinates K x ω)
  let m : Fin n → ℝ := fun j => P.fixedExpectation K x (P.indicator (a j))
  have hfm (j : Fin n) : Measurable (f j) :=
    (measurable_indicator P (a j)).comp (measurable_fixedCoordinates P K x)
  have hfr (j : Fin n) (ω : P.Sample) : f j ω ∈ Set.Icc (0 : ℝ) 1 :=
    indicator_mem_Icc P (a j) _
  have hmr (j : Fin n) : m j ∈ Set.Icc (0 : ℝ) 1 :=
    fixedExpectation_indicator_mem_Icc P K x (a j)
  have henvm : Measurable (fun ω => ∏ j, (f j ω + m j)) :=
    Finset.measurable_fun_prod _ (fun j _ => (hfm j).add_const (m j))
  have henvr (ω : P.Sample) : (∏ j, (f j ω + m j)) ∈ Set.Icc (0 : ℝ) (2 ^ n) := by
    constructor
    · exact Finset.prod_nonneg (fun j _ => add_nonneg (hfr j ω).1 (hmr j).1)
    · calc
        (∏ j, (f j ω + m j)) ≤ ∏ _j : Fin n, (2 : ℝ) := by
          apply Finset.prod_le_prod
          · intro j _
            exact add_nonneg (hfr j ω).1 (hmr j).1
          · intro j _
            have hf := (hfr j ω).2
            have hm := (hmr j).2
            linarith
        _ = 2 ^ n := by simp
  have henvi : Integrable (fun ω => ∏ j, (f j ω + m j)) P.measure :=
    Integrable.of_mem_Icc 0 (2 ^ n) henvm.aemeasurable (Filter.Eventually.of_forall henvr)
  change |∫ ω, ∏ j, (f j ω - m j) ∂P.measure| ≤ ∫ ω, ∏ j, (f j ω + m j) ∂P.measure
  refine abs_integral_le_integral_abs.trans
    (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) henvi ?_)
  filter_upwards with ω
  rw [Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro j _
    exact abs_nonneg _
  · intro j _
    have hf := (hfr j ω).1
    have hm := (hmr j).1
    exact abs_le.mpr ⟨by linarith, by linarith⟩

end Balanced.PatternProof

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternModelExpansion
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced.PatternModelMoments

variable (P : PatternModel)

lemma centered_product_integrable (K : Finset P.Color) (x : P.Sample)
    (n : ℕ) (a : Fin n → P.Label) :
    Integrable (fun ω => ∏ j, (P.indicator (a j) (P.fixCoordinates K x ω) -
      P.fixedExpectation K x (P.indicator (a j)))) P.measure := by
  let : IsProbabilityMeasure P.measure := by
    unfold PatternModel.measure
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hm (j : Fin n) : Measurable (fun ω =>
      P.indicator (a j) (P.fixCoordinates K x ω) -
        P.fixedExpectation K x (P.indicator (a j))) :=
    ((PatternProof.measurable_indicator P (a j)).comp
      (PatternProof.measurable_fixedCoordinates P K x)).sub_const _
  apply Integrable.of_bound
    (Finset.measurable_fun_prod _ (fun j _ => hm j)).aestronglyMeasurable 1
  filter_upwards with ω
  rw [Real.norm_eq_abs, Finset.abs_prod]
  apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
  intro j _
  have hi := PatternProof.indicator_mem_Icc P (a j) (P.fixCoordinates K x ω)
  have hmean := PatternProof.fixedExpectation_indicator_mem_Icc P K x (a j)
  exact abs_le.mpr ⟨by linarith [hi.1, hi.2, hmean.1, hmean.2],
    by linarith [hi.1, hi.2, hmean.1, hmean.2]⟩

lemma fixedExpectation_count_eq_sum (K : Finset P.Color) (x : P.Sample) :
    P.fixedExpectation K x P.count =
      ∑ a, P.fixedExpectation K x (P.indicator a) := by
  let : IsProbabilityMeasure P.measure := by
    unfold PatternModel.measure
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  unfold PatternModel.fixedExpectation PatternModel.count
  exact integral_finsetSum _ (fun a _ =>
    Integrable.of_mem_Icc 0 1
      (((PatternProof.measurable_indicator P a).comp
        (PatternProof.measurable_fixedCoordinates P K x)).aemeasurable)
      (Filter.Eventually.of_forall (fun ω =>
        PatternProof.indicator_mem_Icc P a (P.fixCoordinates K x ω))))

theorem centered_moment_expansion (K : Finset P.Color) (x : P.Sample) (s : ℕ) :
    P.fixedExpectation K x
      (fun ω => |P.count ω - P.fixedExpectation K x P.count| ^ (2 * s)) =
      ∑ a : Fin (2 * s) → P.Label, P.fixedExpectation K x
        (fun ω => ∏ j, (P.indicator (a j) ω -
          P.fixedExpectation K x (P.indicator (a j)))) := by
  classical
  have hcenter (ω : P.Sample) :
      P.count ω - P.fixedExpectation K x P.count =
        ∑ a, (P.indicator a ω - P.fixedExpectation K x (P.indicator a)) := by
    rw [fixedExpectation_count_eq_sum, Finset.sum_sub_distrib]
    rfl
  have habs (z : ℝ) : |z| ^ (2 * s) = z ^ (2 * s) := by
    rw [pow_mul, pow_mul, sq_abs]
  simp_rw [habs, hcenter, Fintype.sum_pow]
  unfold PatternModel.fixedExpectation
  exact integral_finsetSum _ (fun a _ => centered_product_integrable P K x (2 * s) a)

attribute [local instance] Classical.propDecidable

theorem centered_moment_le_noIsolated (K : Finset P.Color) (x : P.Sample) (s : ℕ) :
    P.fixedExpectation K x
      (fun ω => |P.count ω - P.fixedExpectation K x P.count| ^ (2 * s)) ≤
      ∑ a : Fin (2 * s) → P.Label,
        if noIsolated P K a then
          P.fixedExpectation K x (fun ω => ∏ j,
            (P.indicator (a j) ω + P.fixedExpectation K x (P.indicator (a j))))
        else 0 := by
  classical
  rw [centered_moment_expansion]
  apply Finset.sum_le_sum
  intro a _
  by_cases hno : noIsolated P K a
  · rw [ite_eq_left hno]
    exact (le_abs_self _).trans
      (PatternProof.abs_fixedExpectation_centered_prod_le P K x (2 * s) a)
  · rw [ite_eq_right hno]
    have hiso : ∃ i, ∀ j, j ≠ i →
        ¬ ((P.support (a j) \ K) ∩ (P.support (a i) \ K)).Nonempty := by
      simpa only [noIsolated, not_forall, not_exists, not_and] using hno
    obtain ⟨i, hi⟩ := hiso
    have hdisj (j : Fin (2 * s)) (hij : i ≠ j) :
        Disjoint (P.support (a i) \ K) (P.support (a j) \ K) := by
      apply Finset.disjoint_left.mpr
      intro c hci hcj
      exact hi j hij.symm ⟨c, Finset.mem_inter.mpr ⟨hcj, hci⟩⟩
    rw [PatternProof.fixedExpectation_centered_prod_eq_zero P K x (2 * s) a i hdisj]

end Balanced.PatternModelMoments

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_OverlapOrdering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.OverlapOrdering

variable {α : Type*} [DecidableEq α]

theorem exists_pair_partition (G : SimpleGraph α) (I : Finset α) :
    ∃ R S U : Finset α,
      R ∪ S ∪ U = I ∧ Disjoint R S ∧ Disjoint R U ∧ Disjoint S U ∧
      R.card = S.card ∧
      (∀ v ∈ S, ∃ u ∈ R, G.Adj u v) ∧
      (∀ u ∈ U, ∀ v ∈ U, ¬ G.Adj u v) := by
  classical
  refine Finset.strongInductionOn I ?_
  intro I ih
  by_cases he : ∃ a ∈ I, ∃ b ∈ I, G.Adj a b
  · obtain ⟨a, ha, b, hb, habG⟩ := he
    have hab : a ≠ b := habG.ne
    let J := (I.erase a).erase b
    have hJI : J ⊂ I := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨(Finset.erase_subset b (I.erase a)).trans (Finset.erase_subset a I), ?_⟩
      intro h
      have : a ∈ J := h.symm ▸ ha
      simp [J] at this
    obtain ⟨R, S, U, hcover, hRS, hRU, hSU, hcard, hpartners, hind⟩ := ih J hJI
    have hRsub : R ⊆ J := by
      rw [← hcover]
      exact (Finset.subset_union_left).trans Finset.subset_union_left
    have hSsub : S ⊆ J := by
      rw [← hcover]
      exact (Finset.subset_union_right).trans Finset.subset_union_left
    have hUsub : U ⊆ J := by
      rw [← hcover]
      exact Finset.subset_union_right
    have haR : a ∉ R := by intro h; have := hRsub h; simp [J] at this
    have haS : a ∉ S := by intro h; have := hSsub h; simp [J] at this
    have haU : a ∉ U := by intro h; have := hUsub h; simp [J] at this
    have hbR : b ∉ R := by intro h; have := hRsub h; simp [J] at this
    have hbS : b ∉ S := by intro h; have := hSsub h; simp [J] at this
    have hbU : b ∉ U := by intro h; have := hUsub h; simp [J] at this
    refine ⟨insert a R, insert b S, U, ?_, ?_, ?_, ?_, ?_, ?_, hind⟩
    · ext x
      have hx := Finset.ext_iff.mp hcover x
      simp only [Finset.mem_union, Finset.mem_insert] at hx ⊢
      simp only [J, Finset.mem_erase] at hx
      grind
    · simp [Finset.disjoint_insert_left, Finset.disjoint_insert_right,
        hab.symm, hbR, haS, hRS]
    · simp [Finset.disjoint_insert_left, haU, hRU]
    · simp [Finset.disjoint_insert_left, hbU, hSU]
    · simp [Finset.card_insert_of_notMem haR, Finset.card_insert_of_notMem hbS, hcard]
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ⟨a, Finset.mem_insert_self _ _, habG⟩
      · obtain ⟨u, hu, huv⟩ := hpartners v hv
        exact ⟨u, Finset.mem_insert_of_mem hu, huv⟩
  · refine ⟨∅, ∅, I, by simp, by simp, by simp, by simp, by simp, by simp, ?_⟩
    intro u hu v hv huv
    exact he ⟨u, hu, v, hv, huv⟩

theorem exists_three_level_ranking (G : SimpleGraph α) (I : Finset α)
    (hneighbour : ∀ v ∈ I, ∃ u ∈ I, G.Adj u v) :
    ∃ R ⊆ I, ∃ h : α → ℕ,
      2 * R.card ≤ I.card ∧ (∀ v, h v ≤ 2) ∧
      (∀ v ∈ I, v ∉ R → ∃ u ∈ I, G.Adj u v ∧ h u < h v) := by
  classical
  obtain ⟨R, S, U, hcover, hRS, hRU, hSU, hcard, hpartners, hind⟩ :=
    exists_pair_partition G I
  have hRsub : R ⊆ I := by
    rw [← hcover]
    exact (Finset.subset_union_left).trans Finset.subset_union_left
  have hSsub : S ⊆ I := by
    rw [← hcover]
    exact (Finset.subset_union_right).trans Finset.subset_union_left
  have hcardbound : 2 * R.card ≤ I.card := by
    have h := Finset.card_le_card (Finset.union_subset hRsub hSsub)
    rw [Finset.card_union_of_disjoint hRS, ← hcard] at h
    omega
  let height : α → ℕ := fun v => if v ∈ R then 0 else if v ∈ S then 1 else 2
  refine ⟨R, hRsub, height, hcardbound, ?_, ?_⟩
  · intro v
    dsimp [height]
    split_ifs <;> omega
  · intro v hv hvR
    by_cases hvS : v ∈ S
    · obtain ⟨u, hu, huv⟩ := hpartners v hvS
      exact ⟨u, hRsub hu, huv, by simp [height, hu, hvR, hvS]⟩
    · have hvU : v ∈ U := by
        rw [← hcover] at hv
        simpa [hvR, hvS] using hv
      obtain ⟨u, hu, huv⟩ := hneighbour v hv
      have huU : u ∉ U := fun huU => hind u huU v hvU huv
      have huRS : u ∈ R ∨ u ∈ S := by
        rw [← hcover] at hu
        simpa [huU] using hu
      refine ⟨u, hu, huv, ?_⟩
      rcases huRS with huR | huS
      · simp [height, huR, hvR, hvS]
      · by_cases huR : u ∈ R <;> simp [height, huR, huS, hvR, hvS]

theorem exists_sorted_permutation {n : ℕ} (f : Fin n → ℕ)
    (hf : Function.Injective f) :
    ∃ π : Equiv.Perm (Fin n), StrictMono (f ∘ π) := by
  classical
  let S := Finset.univ.image f
  have hcard : S.card = n := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  let g : Fin n → S := fun i => ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · intro i j hij
      exact hf (congrArg Subtype.val hij)
    · intro x
      obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp x.property
      refine ⟨i, ?_⟩
      apply Subtype.ext
      exact hix
  let e : Fin n ≃ S := Equiv.ofBijective g hg
  let o : Fin n ≃o S := S.orderIsoOfFin hcard
  let π : Equiv.Perm (Fin n) := o.toEquiv.trans e.symm
  have hkey : ∀ i, f (π i) = (o i).val := by
    intro i
    exact congrArg Subtype.val (e.apply_symm_apply (o i))
  refine ⟨π, ?_⟩
  intro i j hij
  change f (π i) < f (π j)
  rw [hkey, hkey]
  exact o.strictMono hij

theorem exists_permutation_with_few_roots {n : ℕ} (G : SimpleGraph (Fin n))
    (hneighbour : ∀ v, ∃ u, G.Adj u v) :
    ∃ π : Equiv.Perm (Fin n), ∃ R : Finset (Fin n),
      2 * R.card ≤ n ∧
      ∀ i, i ∉ R → ∃ j, j < i ∧ G.Adj (π j) (π i) := by
  classical
  obtain ⟨R, hR, height, hcard, hheight, hprev⟩ :=
    exists_three_level_ranking G Finset.univ (by
      intro v hv
      obtain ⟨u, huv⟩ := hneighbour v
      exact ⟨u, Finset.mem_univ u, huv⟩)
  let rank : Fin n → ℕ := fun v => height v * n + v.val
  have hrank : Function.Injective rank := by
    intro u v huv
    apply Fin.ext
    have he := congrArg (fun z => z % n) huv
    simpa [rank, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt u.isLt,
      Nat.mod_eq_of_lt v.isLt] using he
  have hlt : ∀ u v, height u < height v → rank u < rank v := by
    intro u v huv
    dsimp [rank]
    calc
      height u * n + u.val < (height u + 1) * n := by nlinarith [u.isLt]
      _ ≤ height v * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt huv)
      _ ≤ height v * n + v.val := Nat.le_add_right _ _
  obtain ⟨π, hπ⟩ := exists_sorted_permutation rank hrank
  refine ⟨π, R.image π.symm, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ π.symm.injective]
    simpa using hcard
  · intro i hi
    have hiR : π i ∉ R := by
      intro h
      apply hi
      exact Finset.mem_image.mpr ⟨π i, h, π.symm_apply_apply i⟩
    obtain ⟨u, hu, huadj, huh⟩ := hprev (π i) (Finset.mem_univ _) hiR
    refine ⟨π.symm u, ?_, by simpa using huadj⟩
    apply hπ.lt_iff_lt.mp
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hlt u (π i) huh

theorem exists_even_permutation_with_few_roots {s : ℕ}
    (G : SimpleGraph (Fin (2 * s))) (hneighbour : ∀ v, ∃ u, G.Adj u v) :
    ∃ π : Equiv.Perm (Fin (2 * s)), ∃ R : Finset (Fin (2 * s)),
      R.card ≤ s ∧
      ∀ i, i ∉ R → ∃ j, j < i ∧ G.Adj (π j) (π i) := by
  obtain ⟨π, R, hcard, hprev⟩ := exists_permutation_with_few_roots G hneighbour
  exact ⟨π, R, by omega, hprev⟩

theorem exists_pattern_ordering {γ : Type*} [DecidableEq γ] {s : ℕ}
    (C : Fin (2 * s) → Finset γ) (K₀ : Finset γ)
    (hnoiso : ∀ i, ∃ j, j ≠ i ∧ ((C j \ K₀) ∩ (C i \ K₀)).Nonempty) :
    ∃ π : Equiv.Perm (Fin (2 * s)), ∃ R : Finset (Fin (2 * s)),
      R.card ≤ s ∧ ∀ i, i ∉ R →
        ∃ j, j < i ∧ ((C (π j) \ K₀) ∩ (C (π i) \ K₀)).Nonempty := by
  let G : SimpleGraph (Fin (2 * s)) := {
    Adj := fun i j => i ≠ j ∧ ((C i \ K₀) ∩ (C j \ K₀)).Nonempty
    symm := by
      constructor
      intro i j hij
      exact ⟨hij.1.symm, by simpa only [Finset.inter_comm] using hij.2⟩
    loopless := by
      constructor
      intro i hii
      exact hii.1 rfl }
  have hG : ∀ v, ∃ u, G.Adj u v := by
    intro v
    obtain ⟨u, huv, hC⟩ := hnoiso v
    exact ⟨u, huv, hC⟩
  obtain ⟨π, R, hcard, hprev⟩ := exists_even_permutation_with_few_roots G hG
  refine ⟨π, R, hcard, ?_⟩
  intro i hi
  obtain ⟨j, hji, hGji⟩ := hprev i hi
  exact ⟨j, hji, hGji.2⟩

end Balanced.OverlapOrdering

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PatternMoments

open scoped BigOperators

variable {Ω A Y : Type*} [Fintype Ω] [Fintype A] [Fintype Y]

lemma scheduleCost_nonneg {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (schedule : List Bool) : 0 ≤ scheduleCost M L schedule := by
  induction schedule with
  | nil => simp [scheduleCost]
  | cons root rest ih =>
      simp only [scheduleCost]
      exact mul_nonneg (by split <;> assumption) ih

theorem scheduledWeight_le
    (W : List A → ℝ) (overlap : List A → A → Prop)
    [∀ pre a, Decidable (overlap pre a)]
    (N : ℕ) (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hfree : ∀ pre, pre.length < N →
      (∑ a, W (a :: pre)) ≤ M * W pre)
    (htouch : ∀ pre, pre.length < N →
      (∑ a, if overlap pre a then W (a :: pre) else 0) ≤ L * W pre)
    (schedule : List Bool) (pre : List A)
    (hlen : pre.length + schedule.length ≤ N) :
    scheduledWeight W overlap schedule pre ≤
      scheduleCost M L schedule * W pre := by
  classical
  induction schedule generalizing pre with
  | nil => simp [scheduledWeight, scheduleCost]
  | cons root rest ih =>
      have hshort : pre.length < N := by simp only [List.length_cons] at hlen; omega
      have hrest (a : A) : (a :: pre).length + rest.length ≤ N := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlen
      have hnonneg := scheduleCost_nonneg hM hL rest
      calc
        scheduledWeight W overlap (root :: rest) pre ≤
            ∑ a, if root = true ∨ overlap pre a then
              scheduleCost M L rest * W (a :: pre) else 0 := by
          apply Finset.sum_le_sum
          intro a _
          split_ifs
          · exact ih (a :: pre) (hrest a)
          · exact le_rfl
        _ = scheduleCost M L rest *
            (∑ a, if root = true ∨ overlap pre a then W (a :: pre) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          split_ifs <;> simp
        _ ≤ scheduleCost M L rest * ((if root then M else L) * W pre) := by
          apply mul_le_mul_of_nonneg_left _ hnonneg
          cases root with
          | false => simpa using htouch pre hshort
          | true => simpa using hfree pre hshort
        _ = scheduleCost M L (root :: rest) * W pre := by
          simp only [scheduleCost]
          ring

lemma scheduleCost_eq (C q : ℝ) (schedule : List Bool) :
    scheduleCost (C * q) C schedule = C ^ schedule.length * q ^ rootCount schedule := by
  induction schedule with
  | nil => simp [scheduleCost, rootCount]
  | cons root rest ih =>
      cases root <;> simp [scheduleCost, rootCount, ih, pow_succ, pow_add] <;> ring

theorem scheduleCost_le_power {C q : ℝ} (hC : 0 ≤ C) (hq : 1 ≤ q)
    (schedule : List Bool) (s : ℕ) (hroots : rootCount schedule ≤ s) :
    scheduleCost (C * q) C schedule ≤ C ^ schedule.length * q ^ s := by
  rw [scheduleCost_eq]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hroots) (pow_nonneg hC _)

attribute [local instance] Classical.propDecidable

theorem scheduledWeight_eq_sum
    (W : List A → ℝ) (overlap : List A → A → Prop)
    [∀ pre a, Decidable (overlap pre a)]
    (schedule : List Bool) (pre : List A) :
    scheduledWeight W overlap schedule pre =
      ∑ a : Fin schedule.length → A,
        if scheduleAllowed overlap schedule (List.ofFn a) pre then
          W ((List.ofFn a).reverse ++ pre) else 0 := by
  classical
  induction schedule generalizing pre with
  | nil => simp [scheduledWeight, scheduleAllowed]
  | cons root rest ih =>
      simp only [List.length_cons]
      rw [← (Fin.consEquiv (fun _ : Fin (rest.length + 1) => A)).sum_comp
        (fun a => if scheduleAllowed overlap (root :: rest) (List.ofFn a) pre then
          W ((List.ofFn a).reverse ++ pre) else 0), Fintype.sum_prod_type]
      simp only [scheduledWeight]
      apply Finset.sum_congr rfl
      intro a _
      rw [ih]
      by_cases ha : root = true ∨ overlap pre a
      · simp [ha, Fin.consEquiv, scheduleAllowed, List.reverse_cons,
          List.append_assoc]
      · simp [ha, Fin.consEquiv, scheduleAllowed]

theorem scheduledWeight_eq_sum_of_length
    (W : List A → ℝ) (overlap : List A → A → Prop)
    [∀ pre a, Decidable (overlap pre a)]
    (schedule : List Bool) (pre : List A) (n : ℕ) (hlen : schedule.length = n) :
    scheduledWeight W overlap schedule pre =
      ∑ a : Fin n → A, if scheduleAllowed overlap schedule (List.ofFn a) pre then
        W ((List.ofFn a).reverse ++ pre) else 0 := by
  subst n
  exact scheduledWeight_eq_sum W overlap schedule pre

theorem sum_le_card_mul_of_reordered_cover
    {T : Type*} [Fintype T]
    (W : A → ℝ) (eligible : A → Prop) (test : T → A → Prop)
    (reorder : T → Equiv.Perm A) (B : ℝ)
    (hW : ∀ a, 0 ≤ W a)
    (hinvariant : ∀ t a, W (reorder t a) = W a)
    (hcover : ∀ a, eligible a → ∃ t, test t (reorder t a))
    (hbound : ∀ t, (∑ a, if test t a then W a else 0) ≤ B) :
    (∑ a, if eligible a then W a else 0) ≤ (Fintype.card T : ℝ) * B := by
  classical
  calc
    (∑ a, if eligible a then W a else 0) ≤
        ∑ a, ∑ t, if test t (reorder t a) then W (reorder t a) else 0 := by
      apply Finset.sum_le_sum
      intro a _
      by_cases he : eligible a
      · obtain ⟨t, ht⟩ := hcover a he
        rw [ite_eq_left he, ← hinvariant t a]
        exact (by simpa [ht] using
          (Finset.single_le_sum
            (f := fun t => if test t (reorder t a) then W (reorder t a) else 0)
            (fun t _ => by split_ifs <;> first | exact hW _ | exact le_rfl)
            (Finset.mem_univ t) :
            (if test t (reorder t a) then W (reorder t a) else 0) ≤
              ∑ t, if test t (reorder t a) then W (reorder t a) else 0))
      · simp only [ite_eq_right he]
        exact Finset.sum_nonneg fun t _ => by split_ifs <;> first | exact hW _ | exact le_rfl
    _ = ∑ t, ∑ a, if test t a then W a else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      exact Equiv.sum_comp (reorder t) (fun a => if test t a then W a else 0)
    _ ≤ ∑ _t : T, B := Finset.sum_le_sum fun t _ => hbound t
    _ = (Fintype.card T : ℝ) * B := by simp

theorem weighted_ordering_bound
    (W : List A → ℝ) (overlap : List A → A → Prop)
    [∀ pre a, Decidable (overlap pre a)]
    (n s : ℕ) (C q : ℝ) (hC : 0 ≤ C) (hq : 1 ≤ q)
    (eligible : (Fin n → A) → Prop)
    (hW : ∀ pre, 0 ≤ W pre) (hnil : W [] = 1)
    (hperm : ∀ l₁ l₂, l₁.Perm l₂ → W l₁ = W l₂)
    (hfree : ∀ pre, pre.length < n →
      (∑ a, W (a :: pre)) ≤ (C * q) * W pre)
    (htouch : ∀ pre, pre.length < n →
      (∑ a, if overlap pre a then W (a :: pre) else 0) ≤ C * W pre)
    (hordering : ∀ a, eligible a → ∃ π : Equiv.Perm (Fin n),
      ∃ σ : Fin n → Bool, rootCount (List.ofFn σ) ≤ s ∧
        scheduleAllowed overlap (List.ofFn σ) (List.ofFn (fun i => a (π i))) []) :
    (∑ a : Fin n → A, if eligible a then W (List.ofFn a).reverse else 0) ≤
      (Nat.factorial n : ℝ) * 2 ^ n * C ^ n * q ^ s := by
  classical
  let T := Equiv.Perm (Fin n) × (Fin n → Bool)
  let test : T → (Fin n → A) → Prop := fun t a =>
    rootCount (List.ofFn t.2) ≤ s ∧
      scheduleAllowed overlap (List.ofFn t.2) (List.ofFn a) []
  have hinvariant (t : T) (a : Fin n → A) :
      W (List.ofFn (tuplePermutation t.1 a)).reverse = W (List.ofFn a).reverse := by
    apply hperm
    exact (List.reverse_perm _).trans ((t.1.ofFn_comp_perm a).trans (List.reverse_perm _).symm)
  have hcover (a : Fin n → A) (ha : eligible a) :
      ∃ t : T, test t (tuplePermutation t.1 a) := by
    obtain ⟨π, σ, hs, ha'⟩ := hordering a ha
    exact ⟨(π, σ), hs, ha'⟩
  have hbound (t : T) :
      (∑ a : Fin n → A, if test t a then W (List.ofFn a).reverse else 0) ≤
        C ^ n * q ^ s := by
    by_cases hs : rootCount (List.ofFn t.2) ≤ s
    · have hexpand := scheduledWeight_eq_sum_of_length W overlap (List.ofFn t.2) [] n
        (List.length_ofFn (f := t.2))
      simp only [List.append_nil] at hexpand
      calc
        (∑ a : Fin n → A, if test t a then W (List.ofFn a).reverse else 0) =
            scheduledWeight W overlap (List.ofFn t.2) [] := by
          simpa only [test, hs, true_and] using hexpand.symm
        _ ≤ scheduleCost (C * q) C (List.ofFn t.2) * W [] := by
          apply scheduledWeight_le W overlap n (C * q) C
            (mul_nonneg hC (le_trans (by norm_num) hq)) hC hfree htouch
          simp
        _ ≤ C ^ n * q ^ s := by
          rw [hnil, mul_one]
          simpa using scheduleCost_le_power hC hq (List.ofFn t.2) s hs
    · simp [test, hs, mul_nonneg (pow_nonneg hC _) (pow_nonneg (by linarith : 0 ≤ q) _)]
  have hfinal := sum_le_card_mul_of_reordered_cover
    (fun a : Fin n → A => W (List.ofFn a).reverse) eligible test
    (fun t : T => tuplePermutation t.1) (C ^ n * q ^ s)
    (fun a => hW _) hinvariant hcover (fun t => by
      convert hbound t using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> rfl)
  convert hfinal using 1
  all_goals try with_reducible_and_instances rfl
  simp only [T, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin,
    Fintype.card_fun, Fintype.card_bool, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

end Balanced.PatternMoments

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternOrderingAdapter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PatternMoments

open scoped BigOperators

variable {A γ : Type*}

theorem scheduleAllowed_ofFn_of_precedes (rel : A → A → Prop) :
    ∀ {n : ℕ} (σ : Fin n → Bool) (x : Fin n → A) (pre : List A),
      (∀ i, σ i = true ∨ (∃ b ∈ pre, rel b (x i)) ∨
        ∃ j, j < i ∧ rel (x j) (x i)) →
      scheduleAllowed (fun pre a => ∃ b ∈ pre, rel b a)
        (List.ofFn σ) (List.ofFn x) pre := by
  intro n
  induction n with
  | zero =>
      intro σ x pre h
      simp [scheduleAllowed]
  | succ n ih =>
      intro σ x pre h
      rw [List.ofFn_succ, List.ofFn_succ]
      constructor
      · rcases h 0 with hroot | hpre | ⟨j, hj, hrel⟩
        · exact Or.inl hroot
        · exact Or.inr hpre
        · exact (Fin.not_lt_zero j hj).elim
      · apply ih (fun i => σ i.succ) (fun i => x i.succ) (x 0 :: pre)
        intro i
        rcases h i.succ with hroot | hpre | ⟨j, hj, hrel⟩
        · exact Or.inl hroot
        · exact Or.inr (Or.inl ⟨hpre.choose, List.mem_cons_of_mem _ hpre.choose_spec.1,
            hpre.choose_spec.2⟩)
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
          · exact Or.inr (Or.inl ⟨x 0, List.mem_cons_self, hrel⟩)
          · exact Or.inr (Or.inr ⟨j, Fin.succ_lt_succ_iff.mp hj, hrel⟩)

theorem rootCount_ofFn {n : ℕ} (σ : Fin n → Bool) :
    rootCount (List.ofFn σ) = ∑ i, if σ i then 1 else 0 := by
  induction n with
  | zero => simp [rootCount]
  | succ n ih =>
      simp only [List.ofFn_succ, rootCount, Fin.sum_univ_succ]
      rw [ih]

theorem rootCount_ofFn_mem {n : ℕ} (R : Finset (Fin n)) :
    rootCount (List.ofFn (fun i => decide (i ∈ R))) = R.card := by
  rw [rootCount_ofFn]
  simp

variable [DecidableEq γ]

lemma supportOverlap_iff (C : A → Finset γ) (K₀ : Finset γ)
    (pre : List A) (a : A) :
    supportOverlap C K₀ pre a ↔
      ∃ b ∈ pre, ((C b \ K₀) ∩ (C a \ K₀)).Nonempty := by
  classical
  induction pre with
  | nil => simp [supportOverlap]
  | cons b pre ih =>
      simp only [supportOverlap, List.foldr_cons, Finset.disjoint_union_right,
        not_and_or] at ih ⊢
      rw [ih]
      simp [Finset.not_disjoint_iff_nonempty_inter, Finset.inter_comm, or_comm]

theorem exists_support_schedule {s : ℕ} (C : A → Finset γ) (K₀ : Finset γ)
    (a : Fin (2 * s) → A)
    (hnoiso : ∀ i, ∃ j, j ≠ i ∧ ((C (a j) \ K₀) ∩ (C (a i) \ K₀)).Nonempty) :
    ∃ π : Equiv.Perm (Fin (2 * s)), ∃ σ : Fin (2 * s) → Bool,
      rootCount (List.ofFn σ) ≤ s ∧
      scheduleAllowed (supportOverlap C K₀) (List.ofFn σ)
        (List.ofFn (fun i => a (π i))) [] := by
  classical
  obtain ⟨π, R, hcard, hprev⟩ :=
    OverlapOrdering.exists_pattern_ordering (fun i => C (a i)) K₀ hnoiso
  refine ⟨π, fun i => decide (i ∈ R), ?_, ?_⟩
  · simpa only [rootCount_ofFn_mem] using hcard
  · have hoverlap : supportOverlap C K₀ =
        (fun pre b => ∃ c ∈ pre, ((C c \ K₀) ∩ (C b \ K₀)).Nonempty) := by
      funext pre b
      exact propext (supportOverlap_iff C K₀ pre b)
    rw [hoverlap]
    apply scheduleAllowed_ofFn_of_precedes
    intro i
    by_cases hi : i ∈ R
    · exact Or.inl (by simp [hi])
    · exact Or.inr (Or.inr (hprev i hi))

end Balanced.PatternMoments

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternCenteredAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.PatternModelMoments
attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

theorem centered_moment_bound_of_weight_costs
    (P : PatternModel) (K : Finset P.Color) (x : P.Sample)
    (s : ℕ) (q C : ℝ) (hq : 1 ≤ q) (hC : 0 ≤ C)
    (W : List P.Label → ℝ)
    (hW : ∀ pre, 0 ≤ W pre) (hnil : W [] = 1)
    (hperm : ∀ pre post, pre.Perm post → W pre = W post)
    (henvelope : ∀ a : Fin (2 * s) → P.Label,
      W (List.ofFn a).reverse =
        P.fixedExpectation K x (fun ω => ∏ j,
          (P.indicator (a j) ω + P.fixedExpectation K x (P.indicator (a j)))))
    (hfree : ∀ pre, pre.length < 2 * s →
      (∑ a, W (a :: pre)) ≤ (C * q) * W pre)
    (htouch : ∀ pre, pre.length < 2 * s →
      (∑ a, if PatternMoments.supportOverlap P.support K pre a then W (a :: pre) else 0) ≤
        C * W pre) :
    P.fixedExpectation K x
      (fun ω => |P.count ω - P.fixedExpectation K x P.count| ^ (2 * s)) ≤
        ((2 * s).factorial : ℝ) * 2 ^ (2 * s) * C ^ (2 * s) * q ^ s := by
  classical
  calc
    P.fixedExpectation K x
        (fun ω => |P.count ω - P.fixedExpectation K x P.count| ^ (2 * s)) ≤
        ∑ a : Fin (2 * s) → P.Label,
          if noIsolated P K a then
            P.fixedExpectation K x (fun ω => ∏ j,
              (P.indicator (a j) ω + P.fixedExpectation K x (P.indicator (a j))))
          else 0 := centered_moment_le_noIsolated P K x s
    _ = ∑ a : Fin (2 * s) → P.Label,
          if noIsolated P K a then W (List.ofFn a).reverse else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> first | exact (henvelope a).symm | rfl
    _ ≤ ((2 * s).factorial : ℝ) * 2 ^ (2 * s) * C ^ (2 * s) * q ^ s := by
      exact PatternMoments.weighted_ordering_bound W
        (PatternMoments.supportOverlap P.support K) (2 * s) s C q hC hq
        (noIsolated P K) hW hnil hperm hfree htouch
        (fun a ha => PatternMoments.exists_support_schedule P.support K a ha)

end Balanced.PatternModelMoments

namespace Balanced.PatternModelMoments
attribute [local instance] Classical.propDecidable

theorem productWeight_ofFn_reverse
    (P : PatternModel) (K : Finset P.Color) (x : P.Sample)
    (n : ℕ) (a : Fin n → P.Label) :
    P.productWeight K x (List.ofFn a).reverse =
      P.fixedExpectation K x (fun ω => ∏ j,
        (P.indicator (a j) ω + P.fixedExpectation K x (P.indicator (a j)))) := by
  unfold PatternModel.productWeight PatternModel.positiveProduct
  congr 1
  funext ω
  simp [List.prod_ofFn]

theorem centered_moment_bound_of_productWeight_costs
    (P : PatternModel) (K : Finset P.Color) (x : P.Sample)
    (s : ℕ) (q C : ℝ) (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hfree : ∀ pre, pre.length < 2 * s →
      (∑ a, P.productWeight K x (a :: pre)) ≤ (C * q) * P.productWeight K x pre)
    (htouch : ∀ pre, pre.length < 2 * s →
      (∑ a, if PatternMoments.supportOverlap P.support K pre a then
        P.productWeight K x (a :: pre) else 0) ≤ C * P.productWeight K x pre) :
    P.fixedExpectation K x
      (fun ω => |P.count ω - P.fixedExpectation K x P.count| ^ (2 * s)) ≤
        ((2 * s).factorial : ℝ) * 2 ^ (2 * s) * C ^ (2 * s) * q ^ s := by
  apply centered_moment_bound_of_weight_costs P K x s q C hq hC
    (P.productWeight K x) (P.productWeight_nonneg K x) (P.productWeight_nil K x)
  · intro pre post h
    exact P.productWeight_perm K x h
  · exact productWeight_ofFn_reverse P K x (2 * s)
  · exact hfree
  · exact htouch

end Balanced.PatternModelMoments

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternPrefixSupport
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PatternModel

attribute [local instance] Classical.propDecidable

variable (P : PatternModel)

lemma mem_freshPrefixSupport_iff (K₀ : Finset P.Color) (pre : List P.Label)
    (c : P.Color) :
    c ∈ P.freshPrefixSupport K₀ pre ↔
      ∃ a ∈ pre, c ∈ P.support a ∧ c ∉ K₀ := by
  induction pre with
  | nil => simp
  | cons a pre ih => simp [ih, or_comm]

end Balanced.PatternModel

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternSupportCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PatternModel

attribute [local instance] Classical.propDecidable

variable (P : PatternModel)

lemma additionalSupport_eq_freshPrefixSupport (K₀ : Finset P.Color)
    (pre : List P.Label) :
    P.additionalSupport K₀ pre = P.freshPrefixSupport K₀ pre := by
  classical
  ext c
  simp only [additionalSupport, Finset.mem_biUnion, List.mem_toFinset,
    Finset.mem_sdiff, P.mem_freshPrefixSupport_iff]

end Balanced.PatternModel

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternMarginals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators ENNReal

namespace Balanced.PatternMarginals

theorem weighted_lintegral_le_of_marginal_bound
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {X : κ → Type*} [∀ c, MeasurableSpace (X c)]
    (μ : ∀ c, Measure (X c)) [∀ c, IsProbabilityMeasure (μ c)]
    (K : Finset κ) (f Z : (∀ c, X c) → ℝ≥0∞) (C : ℝ≥0∞)
    (hf : Measurable f) (hZ : Measurable Z)
    (hdepends : ∀ x y, (∀ c ∈ K, x c = y c) → f x = f y)
    (hbound : ∀ x, lmarginal μ (Finset.univ \ K) Z x ≤ C) :
    (∫⁻ x, f x * Z x ∂Measure.pi μ) ≤ C * ∫⁻ x, f x ∂Measure.pi μ := by
  classical
  rw [← lintegral_const_mul C hf]
  apply lintegral_le_of_lmarginal_le (Finset.univ \ K) (hf.mul hZ)
    (measurable_const.mul hf)
  intro x
  have hfx (y : (c : ↥(Finset.univ \ K)) → X c) :
      f (Function.updateFinset x (Finset.univ \ K) y) = f x := by
    apply hdepends
    intro c hc
    simp [Function.updateFinset_def, hc]
  change (∫⁻ y, f (Function.updateFinset x (Finset.univ \ K) y) *
      Z (Function.updateFinset x (Finset.univ \ K) y)
        ∂Measure.pi (fun c : ↥(Finset.univ \ K) => μ c)) ≤
    ∫⁻ y, C * f (Function.updateFinset x (Finset.univ \ K) y)
      ∂Measure.pi (fun c : ↥(Finset.univ \ K) => μ c)
  simp_rw [hfx]
  have hZup : Measurable (fun y : (c : ↥(Finset.univ \ K)) → X c =>
      Z (Function.updateFinset x (Finset.univ \ K) y)) := hZ.comp measurable_updateFinset
  rw [lintegral_const_mul (f x) hZup]
  simpa only [lmarginal, lintegral_const, measure_univ, mul_one, mul_comm C] using
    mul_le_mul' (le_refl (f x)) (hbound x)

theorem weighted_integral_le_of_marginal_bound
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {X : κ → Type*} [∀ c, MeasurableSpace (X c)]
    (μ : ∀ c, Measure (X c)) [∀ c, IsProbabilityMeasure (μ c)]
    (K : Finset κ) (F Z : (∀ c, X c) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hF : Measurable F) (hZ : Measurable Z)
    (hFn : ∀ x, 0 ≤ F x) (hZn : ∀ x, 0 ≤ Z x)
    (hFi : Integrable F (Measure.pi μ))
    (hdepends : ∀ x y, (∀ c ∈ K, x c = y c) → F x = F y)
    (hbound : ∀ x, lmarginal μ (Finset.univ \ K)
      (fun y => ENNReal.ofReal (Z y)) x ≤ ENNReal.ofReal C) :
    (∫ x, F x * Z x ∂Measure.pi μ) ≤ C * ∫ x, F x ∂Measure.pi μ := by
  have hE := weighted_lintegral_le_of_marginal_bound μ K
    (fun x => ENNReal.ofReal (F x)) (fun x => ENNReal.ofReal (Z x))
    (ENNReal.ofReal C) hF.ennreal_ofReal hZ.ennreal_ofReal
    (by intro x y hxy; rw [hdepends x y hxy]) hbound
  have hfinite : (∫⁻ x, ENNReal.ofReal (F x) ∂Measure.pi μ) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hF.aestronglyMeasurable
      (Filter.Eventually.of_forall hFn)).mpr hFi
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) hE
  rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun x => mul_nonneg (hFn x) (hZn x)))
      (hF.mul hZ).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hFn)
      hF.aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_mul (hFn _)]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using hreal

end Balanced.PatternMarginals

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternMomentModel
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators ENNReal

namespace Balanced.PatternModel
open scoped _root_.Balanced

theorem measurable_fixCoordinates_map (P : PatternModel) (K : Finset P.Color)
    (x : P.Sample) : Measurable (P.fixCoordinates K x) := by
  classical
  apply measurable_pi_iff.mpr
  intro c
  by_cases hc : c ∈ K
  · simp [fixCoordinates, hc]
  · simpa [fixCoordinates, hc] using
      (measurable_pi_apply c : Measurable (fun ω : P.Sample => ω c))

theorem lintegral_fixCoordinates_eq_lmarginal (P : PatternModel)
    (K : Finset P.Color) (x : P.Sample) (f : P.Sample → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ ω, f (P.fixCoordinates K x ω) ∂P.measure) =
      lmarginal P.law (Finset.univ \ K) f x := by
  classical
  let L := lmarginal P.law (Finset.univ \ K) f x
  have hcomp (y : P.Sample) (z : (c : ↥(Finset.univ \ K)) → P.Value c) :
      P.fixCoordinates K x (Function.updateFinset y (Finset.univ \ K) z) =
        Function.updateFinset x (Finset.univ \ K) z := by
    funext c
    by_cases hc : c ∈ K <;> simp [fixCoordinates, Function.updateFinset_def, hc]
  have hinner : lmarginal P.law (Finset.univ \ K)
      (fun ω => f (P.fixCoordinates K x ω)) = fun _ => L := by
    funext y
    simp only [lmarginal, hcomp, L]
  have hconst : lmarginal P.law (Finset.univ \ K) (fun _ : P.Sample => L) =
      fun _ => L := by
    funext y
    simp [lmarginal]
  have h := lintegral_eq_of_lmarginal_eq (Finset.univ \ K)
    (hf.comp (P.measurable_fixCoordinates_map K x)) measurable_const (hinner.trans hconst.symm)
  simpa only [measure, Function.comp_apply, lintegral_const, measure_univ, mul_one, L] using h

theorem fixCoordinates_comp (P : PatternModel) (K₀ K : Finset P.Color)
    (x y ω : P.Sample) :
    P.fixCoordinates K₀ x (P.fixCoordinates K y ω) =
      P.fixCoordinates (K₀ ∪ K) (P.fixCoordinates K₀ x y) ω := by
  classical
  funext c
  by_cases hc₀ : c ∈ K₀ <;> by_cases hc : c ∈ K <;>
    simp [fixCoordinates, hc₀, hc]

theorem fixedExpectation_mul_le_of_fixedBounds (P : PatternModel)
    (K₀ K : Finset P.Color) (x : P.Sample)
    (F Z : P.Sample → ℝ) (C BF BZ : ℝ) (hC : 0 ≤ C)
    (hF : Measurable F) (hZ : Measurable Z)
    (hFn : ∀ ω, 0 ≤ F ω) (hZn : ∀ ω, 0 ≤ Z ω)
    (hFB : ∀ ω, F ω ≤ BF) (hZB : ∀ ω, Z ω ≤ BZ)
    (hdepends : ∀ ω ω', (∀ c ∈ K₀ ∪ K, ω c = ω' c) → F ω = F ω')
    (hbound : ∀ y, P.fixedExpectation (K₀ ∪ K) y Z ≤ C) :
    P.fixedExpectation K₀ x (fun ω => F ω * Z ω) ≤
      C * P.fixedExpectation K₀ x F := by
  have hfixed_integrable (J : Finset P.Color) (y : P.Sample)
      (G : P.Sample → ℝ) (BG : ℝ) (hG : Measurable G)
      (hGn : ∀ ω, 0 ≤ G ω) (hGB : ∀ ω, G ω ≤ BG) :
      Integrable (fun ω => G (P.fixCoordinates J y ω)) (Measure.pi P.law) := by
    apply Integrable.of_bound
      (hG.comp (P.measurable_fixCoordinates_map J y)).aestronglyMeasurable BG
    exact Filter.Eventually.of_forall (fun ω => by
      change ‖G (P.fixCoordinates J y ω)‖ ≤ BG
      rw [Real.norm_eq_abs, abs_of_nonneg (hGn _)]
      exact hGB _)
  change (∫ ω, F (P.fixCoordinates K₀ x ω) * Z (P.fixCoordinates K₀ x ω)
      ∂Measure.pi P.law) ≤ C * ∫ ω, F (P.fixCoordinates K₀ x ω) ∂Measure.pi P.law
  apply PatternMarginals.weighted_integral_le_of_marginal_bound P.law K
    (fun ω => F (P.fixCoordinates K₀ x ω))
    (fun ω => Z (P.fixCoordinates K₀ x ω)) C hC
    (hF.comp (P.measurable_fixCoordinates_map K₀ x))
    (hZ.comp (P.measurable_fixCoordinates_map K₀ x))
    (fun ω => hFn _) (fun ω => hZn _)
    (hfixed_integrable K₀ x F BF hF hFn hFB)
  · intro ω ω' hω
    apply hdepends
    intro c hc
    by_cases hc₀ : c ∈ K₀
    · simp [fixCoordinates, hc₀]
    · have hcK : c ∈ K := (Finset.mem_union.mp hc).resolve_left hc₀
      simpa [fixCoordinates, hc₀] using hω c hcK
  · intro y
    have hZc : Measurable (fun ω => ENNReal.ofReal (Z (P.fixCoordinates K₀ x ω))) :=
      (hZ.comp (P.measurable_fixCoordinates_map K₀ x)).ennreal_ofReal
    rw [← P.lintegral_fixCoordinates_eq_lmarginal K y _ hZc]
    simp_rw [P.fixCoordinates_comp K₀ K x y]
    simp only [measure]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (hfixed_integrable (K₀ ∪ K) (P.fixCoordinates K₀ x y) Z BZ hZ hZn hZB)
      (Filter.Eventually.of_forall (fun ω => hZn _))]
    exact ENNReal.ofReal_le_ofReal (hbound (P.fixCoordinates K₀ x y))

theorem fixedExpectation_positive_extension_le (P : PatternModel)
    (K₀ K : Finset P.Color) (x : P.Sample)
    (F Z : P.Sample → ℝ) (C BF BZ : ℝ) (hC : 0 ≤ C)
    (hF : Measurable F) (hZ : Measurable Z)
    (hFn : ∀ ω, 0 ≤ F ω) (hZn : ∀ ω, 0 ≤ Z ω)
    (hFB : ∀ ω, F ω ≤ BF) (hZB : ∀ ω, Z ω ≤ BZ)
    (hdepends : ∀ ω ω', (∀ c ∈ K₀ ∪ K, ω c = ω' c) → F ω = F ω')
    (hbound : ∀ y, P.fixedExpectation (K₀ ∪ K) y Z ≤ C) :
    P.fixedExpectation K₀ x
        (fun ω => F ω * (Z ω + P.fixedExpectation K₀ x Z)) ≤
      (2 * C) * P.fixedExpectation K₀ x F := by
  have hmean : P.fixedExpectation K₀ x Z ≤ C := by
    have h := P.fixedExpectation_mul_le_of_fixedBounds K₀ K x
      (fun _ => 1) Z C 1 BZ hC measurable_const hZ
      (fun _ => zero_le_one) hZn (fun _ => le_rfl) hZB
      (by intros; rfl) hbound
    simpa [fixedExpectation, measure] using h
  have hmean_nonneg : 0 ≤ P.fixedExpectation K₀ x Z :=
    integral_nonneg (fun ω => hZn _)
  have hZi (J : Finset P.Color) (y : P.Sample) :
      Integrable (fun ω => Z (P.fixCoordinates J y ω)) (Measure.pi P.law) := by
    apply Integrable.of_bound
      (hZ.comp (P.measurable_fixCoordinates_map J y)).aestronglyMeasurable BZ
    exact Filter.Eventually.of_forall (fun ω => by
      change ‖Z (P.fixCoordinates J y ω)‖ ≤ BZ
      rw [Real.norm_eq_abs, abs_of_nonneg (hZn _)]
      exact hZB _)
  apply P.fixedExpectation_mul_le_of_fixedBounds K₀ K x F
    (fun ω => Z ω + P.fixedExpectation K₀ x Z)
    (2 * C) BF (BZ + P.fixedExpectation K₀ x Z) (mul_nonneg (by norm_num) hC)
    hF (hZ.add measurable_const) hFn
    (fun ω => add_nonneg (hZn ω) hmean_nonneg) hFB
    (fun ω => add_le_add (hZB ω) le_rfl) hdepends
  intro y
  have hadd : P.fixedExpectation (K₀ ∪ K) y
        (fun ω => Z ω + P.fixedExpectation K₀ x Z) =
      P.fixedExpectation (K₀ ∪ K) y Z + P.fixedExpectation K₀ x Z := by
    unfold fixedExpectation
    simp only [measure]
    rw [integral_add (hZi (K₀ ∪ K) y) (integrable_const _)]
    simp
  rw [hadd]
  linarith [hbound y]

end Balanced.PatternModel

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternWeightExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced.PatternModel
open scoped _root_.Balanced

theorem sum_productWeight_cons_eq (P : PatternModel)
    (K₀ : Finset P.Color) (x : P.Sample) (as : List P.Label) (S : Finset P.Label) :
    (∑ a ∈ S, P.productWeight K₀ x (a :: as)) =
      P.fixedExpectation K₀ x (fun ω => P.positiveProduct K₀ x as ω *
        ((∑ a ∈ S, P.indicator a ω) +
          P.fixedExpectation K₀ x (fun η => ∑ a ∈ S, P.indicator a η))) := by
  classical
  have hES : P.fixedExpectation K₀ x (fun η => ∑ a ∈ S, P.indicator a η) =
      ∑ a ∈ S, P.fixedExpectation K₀ x (P.indicator a) := by
    unfold fixedExpectation
    exact integral_finsetSum S (fun a _ => P.integrable_fixed_indicator K₀ x a)
  rw [hES]
  simp only [productWeight, fixedExpectation]
  rw [← integral_finsetSum S (fun a _ =>
    P.integrable_fixed_positiveProduct K₀ K₀ x x (a :: as))]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [positiveProduct, List.map_cons, List.prod_cons, fixedExpectation]
  rw [← Finset.sum_mul, Finset.sum_add_distrib]
  ring

theorem productWeight_subset_extension_le (P : PatternModel)
    (K₀ : Finset P.Color) (x : P.Sample) (as : List P.Label)
    (S : Finset P.Label) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y, P.fixedExpectation (K₀ ∪ P.additionalSupport K₀ as) y
      (fun ω => ∑ a ∈ S, P.indicator a ω) ≤ C) :
    (∑ a ∈ S, P.productWeight K₀ x (a :: as)) ≤
      (2 * C) * P.productWeight K₀ x as := by
  classical
  rw [P.sum_productWeight_cons_eq K₀ x as S]
  apply P.fixedExpectation_positive_extension_le K₀ (P.additionalSupport K₀ as) x
    (P.positiveProduct K₀ x as) (fun ω => ∑ a ∈ S, P.indicator a ω)
    C (2 ^ as.length) (S.card : ℝ) hC
    (P.measurable_positiveProduct K₀ x as)
    (Finset.measurable_sum S (fun a _ => P.measurable_indicator a))
    (P.positiveProduct_nonneg K₀ x as)
    (fun ω => Finset.sum_nonneg (fun a _ => P.indicator_nonneg a ω))
    (P.positiveProduct_le K₀ x as)
  · intro ω
    calc
      (∑ a ∈ S, P.indicator a ω) ≤ ∑ _a ∈ S, (1 : ℝ) :=
        Finset.sum_le_sum (fun a _ => P.indicator_le_one a ω)
      _ = (S.card : ℝ) := by simp
  · exact P.positiveProduct_dependsOn K₀ x as
  · exact hbound

theorem productWeight_free_extension_le (P : PatternModel)
    (K₀ : Finset P.Color) (x : P.Sample) (as : List P.Label)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y, P.fixedExpectation (K₀ ∪ P.additionalSupport K₀ as) y P.count ≤ C) :
    (∑ a, P.productWeight K₀ x (a :: as)) ≤ (2 * C) * P.productWeight K₀ x as := by
  exact P.productWeight_subset_extension_le K₀ x as Finset.univ C hC hbound

theorem productWeight_overlap_extension_le (P : PatternModel)
    (K₀ : Finset P.Color) (x : P.Sample) (as : List P.Label)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y, P.fixedExpectation (K₀ ∪ P.additionalSupport K₀ as) y
      (P.overlapCount K₀ (P.additionalSupport K₀ as)) ≤ C) :
    (∑ a, if Disjoint (P.support a \ K₀) (P.additionalSupport K₀ as)
      then 0 else P.productWeight K₀ x (a :: as)) ≤
        (2 * C) * P.productWeight K₀ x as := by
  classical
  have h := P.productWeight_subset_extension_le K₀ x as
    (Finset.univ.filter (fun a => ¬Disjoint (P.support a \ K₀) (P.additionalSupport K₀ as)))
    C hC (by
      intro y
      simp only [Finset.sum_filter, ite_not]
      exact hbound y)
  simpa only [Finset.sum_filter, ite_not] using h

theorem additionalSupport_card_le (P : PatternModel)
    (K₀ : Finset P.Color) (as : List P.Label) (r : ℕ)
    (h : ∀ a, (P.support a).card ≤ r) :
    (P.additionalSupport K₀ as).card ≤ as.length * r := by
  classical
  calc
    (P.additionalSupport K₀ as).card ≤
        ∑ a ∈ as.toFinset, (P.support a \ K₀).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ as.toFinset, r := Finset.sum_le_sum
      (fun a _ => (Finset.card_le_card Finset.sdiff_subset).trans (h a))
    _ = as.toFinset.card * r := by simp
    _ ≤ as.length * r := Nat.mul_le_mul_right r (List.toFinset_card_le as)

end Balanced.PatternModel

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteCenteredPatternLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace Balanced.PatternModel
open scoped _root_.Balanced

noncomputable section
open scoped Classical BigOperators
open MeasureTheory

theorem centered_moment_le_of_exposureBounds (P : PatternModel)
    (K₀ : Finset P.Color) (x : P.Sample) (s r : ℕ) (q C : ℝ)
    (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hsupport : ∀ a, (P.support a).card ≤ r)
    (htotal : ∀ K : Finset P.Color, K.card ≤ (2 * s) * r → ∀ y,
      P.fixedExpectation (K₀ ∪ K) y P.count ≤ C * q)
    (hoverlap : ∀ K : Finset P.Color, K.card ≤ (2 * s) * r → ∀ y,
      P.fixedExpectation (K₀ ∪ K) y (P.overlapCount K₀ K) ≤ C) :
    P.fixedExpectation K₀ x
      (fun ω => |P.count ω - P.fixedExpectation K₀ x P.count| ^ (2 * s)) ≤
        ((2 * s).factorial : ℝ) * 2 ^ (2 * s) * (2 * C) ^ (2 * s) * q ^ s := by
  apply PatternModelMoments.centered_moment_bound_of_productWeight_costs
    P K₀ x s q (2 * C) hq (by positivity)
  · intro pre hpre
    have hK : (P.additionalSupport K₀ pre).card ≤ (2 * s) * r :=
      (P.additionalSupport_card_le K₀ pre r hsupport).trans
        (Nat.mul_le_mul_right r (by omega))
    have h := P.productWeight_free_extension_le K₀ x pre (C * q)
      (mul_nonneg hC (by linarith))
      (fun y => htotal (P.additionalSupport K₀ pre) hK y)
    convert h using 1 <;> first | rfl | ring
  · intro pre hpre
    have hK : (P.additionalSupport K₀ pre).card ≤ (2 * s) * r :=
      (P.additionalSupport_card_le K₀ pre r hsupport).trans
        (Nat.mul_le_mul_right r (by omega))
    have h := P.productWeight_overlap_extension_le K₀ x pre C hC
      (fun y => hoverlap (P.additionalSupport K₀ pre) hK y)
    have heq :
        (∑ a, if PatternMoments.supportOverlap P.support K₀ pre a then
          P.productWeight K₀ x (a :: pre) else 0) =
        (∑ a, if Disjoint (P.support a \ K₀) (P.additionalSupport K₀ pre)
          then 0 else P.productWeight K₀ x (a :: pre)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [P.additionalSupport_eq_freshPrefixSupport]
      unfold PatternMoments.supportOverlap PatternModel.freshPrefixSupport
      split_ifs <;> simp_all
    rw [heq]
    exact h

theorem overlapCount_le_allExposed (P : PatternModel)
    (K₀ K : Finset P.Color) (ω : P.Sample) :
    P.overlapCount K₀ K ω ≤ P.overlapCount ∅ (K₀ ∪ K) ω := by
  unfold overlapCount
  apply Finset.sum_le_sum
  intro a _
  by_cases h : Disjoint (P.support a \ K₀) K
  · rw [ite_eq_left h]
    split_ifs
    · exact le_rfl
    · exact P.indicator_nonneg a ω
  · have hn : ¬ Disjoint (P.support a \ ∅) (K₀ ∪ K) := by
      obtain ⟨c, hc, hcK⟩ := Finset.not_disjoint_iff.mp h
      exact Finset.not_disjoint_iff.mpr ⟨c,
        by simpa using (Finset.mem_sdiff.mp hc).1,
        Finset.mem_union_right _ hcK⟩
    rw [ite_eq_right h, ite_eq_right hn]

theorem integrable_fixed_overlapCount (P : PatternModel)
    (D : Finset P.Color) (x : P.Sample) (K₀ K : Finset P.Color) :
    Integrable (fun ω => P.overlapCount K₀ K (P.fixCoordinates D x ω)) P.measure := by
  unfold overlapCount
  apply integrable_finsetSum
  intro a _
  by_cases h : Disjoint (P.support a \ K₀) K
  · simp only [ite_eq_left h]
    exact integrable_const 0
  · simp only [ite_eq_right h]
    exact P.integrable_fixed_indicator D x a

theorem centered_moment_le_of_allExposedBounds (P : PatternModel)
    (K₀ : Finset P.Color) (x : P.Sample) (s r : ℕ) (q C : ℝ)
    (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hsupport : ∀ a, (P.support a).card ≤ r)
    (htotal : ∀ D : Finset P.Color, D.card ≤ K₀.card + (2 * s) * r → ∀ y,
      P.fixedExpectation D y P.count ≤ C * q)
    (hoverlap : ∀ D : Finset P.Color, D.card ≤ K₀.card + (2 * s) * r → ∀ y,
      P.fixedExpectation D y (P.overlapCount ∅ D) ≤ C) :
    P.fixedExpectation K₀ x
      (fun ω => |P.count ω - P.fixedExpectation K₀ x P.count| ^ (2 * s)) ≤
        ((2 * s).factorial : ℝ) * 2 ^ (2 * s) * (2 * C) ^ (2 * s) * q ^ s := by
  apply P.centered_moment_le_of_exposureBounds K₀ x s r q C hq hC hsupport
  · intro K hK y
    exact htotal (K₀ ∪ K) ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hK _)) y
  · intro K hK y
    apply le_trans ?_ (hoverlap (K₀ ∪ K)
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hK _)) y)
    apply integral_mono (P.integrable_fixed_overlapCount (K₀ ∪ K) y K₀ K)
      (P.integrable_fixed_overlapCount (K₀ ∪ K) y ∅ (K₀ ∪ K))
    intro ω
    exact P.overlapCount_le_allExposed K₀ K _

end
end Balanced.PatternModel

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidatePrescribedLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidatePrescribed

noncomputable section
open scoped Classical
open Finset PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem fixedPositions_card_le (J : Finset (Fin 4)) :
    (fixedPositions J).card ≤ J.card := by
  apply Finset.card_le_card
  intro i hi
  exact (Finset.mem_filter.mp hi).2.1

theorem alignmentMass_le (old : Finset (Direction F)) (a : MergedPairs F)
    (l : Line F) (c : Code F) (j : ℕ)
    (hc : c ∈ tupleCodesWithOldCount old j) :
    alignmentMass old a l c ≤ (Fintype.card F : ℝ)⁻¹ ^ (4 - j) := by
  have hJ : (exposedTupleIndices (⟨c.1, c.2⟩ : FourTuple F) old).card = j :=
    (Finset.mem_filter.mp (Finset.mem_product.mp hc).1).2
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast (show 1 ≤ Fintype.card F from Fintype.card_pos)
  unfold alignmentMass
  split_ifs with he
  · have h := canonical_conditional_alignment_probability_le
      (⟨c.1, c.2⟩ : FourTuple F) he.1 l.1 he.2 l.2 old a
    change _ ≤ _ at h
    apply h.trans
    apply pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hq)
    have hf := fixedPositions_card_le
      (exposedTupleIndices (⟨c.1, c.2⟩ : FourTuple F) old)
    rw [hJ] at hf
    omega
  · positivity

theorem card_codes_le (old : Finset (Direction F)) (j : ℕ) (hj : j ≤ 4) :
    (tupleCodesWithOldCount old j).card ≤
      (4096 * (old.card + 1) ^ 4) * Fintype.card F ^ (4 - j) := by
  have hchoose : Nat.choose 4 j ≤ 16 := by
    interval_cases j <;> decide
  have hpow : old.card ^ j ≤ (old.card + 1) ^ 4 := by
    calc
      old.card ^ j ≤ (old.card + 1) ^ j := Nat.pow_le_pow_left (by omega) j
      _ ≤ (old.card + 1) ^ 4 := Nat.pow_le_pow_right (by omega) hj
  have hdir : Fintype.card (Direction F) ≤ 2 * Fintype.card F := by
    have hq : 0 < Fintype.card F := Fintype.card_pos
    simp only [Direction, Fintype.card_option]
    omega
  have htwo : 2 ^ (4 - j) ≤ 16 := by
    calc
      2 ^ (4 - j) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 16 := rfl
  calc
    (tupleCodesWithOldCount old j).card ≤
        16 * (Nat.choose 4 j * old.card ^ j * Fintype.card (Direction F) ^ (4-j)) :=
      card_tupleCodesWithOldCount_le old j
    _ ≤ 16 * (16 * (old.card + 1) ^ 4 * (2 * Fintype.card F) ^ (4-j)) := by
      gcongr
    _ = 256 * (old.card + 1) ^ 4 * (2 ^ (4-j) * Fintype.card F ^ (4-j)) := by
      rw [Nat.mul_pow]
      ring
    _ ≤ 256 * (old.card + 1) ^ 4 * (16 * Fintype.card F ^ (4-j)) := by
      gcongr
    _ = _ := by ring

theorem sum_alignmentMass_stratum_le (old : Finset (Direction F))
    (a : MergedPairs F) (l : Line F) (j : ℕ) (hj : j ≤ 4) :
    (∑ c ∈ tupleCodesWithOldCount old j, alignmentMass old a l c) ≤
      4096 * ((old.card : ℝ) + 1) ^ 4 := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hcount : ((tupleCodesWithOldCount old j).card : ℝ) ≤
      (4096 * ((old.card : ℝ) + 1) ^ 4) * (Fintype.card F : ℝ) ^ (4-j) := by
    exact_mod_cast card_codes_le old j hj
  calc
    (∑ c ∈ tupleCodesWithOldCount old j, alignmentMass old a l c) ≤
        ∑ _c ∈ tupleCodesWithOldCount old j, (Fintype.card F : ℝ)⁻¹ ^ (4-j) := by
      exact Finset.sum_le_sum (fun c hc => alignmentMass_le old a l c j hc)
    _ = ((tupleCodesWithOldCount old j).card : ℝ) *
        (Fintype.card F : ℝ)⁻¹ ^ (4-j) := by simp
    _ ≤ ((4096 * ((old.card : ℝ) + 1) ^ 4) * (Fintype.card F : ℝ) ^ (4-j)) *
        (Fintype.card F : ℝ)⁻¹ ^ (4-j) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ (ne_of_gt hq), one_pow, mul_one]

omit [Field F] in
theorem codes_stratum_eq_filter (old : Finset (Direction F)) (j : ℕ) :
    tupleCodesWithOldCount old j =
      (Finset.univ : Finset (Code F)).filter
        (fun c => (Finset.univ.filter (fun i => c.1 i ∈ old)).card = j) := by
  ext c
  simp [tupleCodesWithOldCount, generatorLabelsWithOldCount]

theorem sum_alignmentMass_le (old : Finset (Direction F))
    (a : MergedPairs F) (l : Line F) :
    (∑ c : Code F, alignmentMass old a l c) ≤
      20480 * ((old.card : ℝ) + 1) ^ 4 := by
  have hpartition :
      (∑ j ∈ Finset.range 5, ∑ c ∈ tupleCodesWithOldCount old j,
        alignmentMass old a l c) = ∑ c : Code F, alignmentMass old a l c := by
    simp_rw [codes_stratum_eq_filter]
    apply Finset.sum_fiberwise_of_maps_to
    intro c _
    apply Finset.mem_range.mpr
    have h := Finset.card_le_univ (Finset.univ.filter (fun i : Fin 4 => c.1 i ∈ old))
    simp only [Fintype.card_fin] at h
    omega
  rw [← hpartition]
  calc
    _ ≤ ∑ _j ∈ Finset.range 5, 4096 * ((old.card : ℝ) + 1) ^ 4 := by
      apply Finset.sum_le_sum
      intro j hj
      exact sum_alignmentMass_stratum_le old a l j (by have h := Finset.mem_range.mp hj; omega)
    _ = _ := by simp; ring

theorem alignmentMass_eq_sum (old : Finset (Direction F))
    (a : MergedPairs F) (l : Line F) (c : Code F) :
    alignmentMass old a l c =
      ∑ M : MergedPairs F, if c ∈ alignedCodes M l then (exposedLaw old a M).toReal else 0 := by
  by_cases he : Eligible l c
  · simp only [alignmentMass, ite_eq_left he, PMF.toOuterMeasure_apply_fintype]
    rw [ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro M _
      simp only [alignedCodes, Finset.mem_filter, Finset.mem_univ, true_and, he,
        Set.indicator_apply, Set.mem_ofPred_eq]
      split_ifs <;> simp
    · intro M _
      simp only [Set.indicator_apply]
      split_ifs
      · exact PMF.apply_ne_top _ _
      · simp
  · simp [alignmentMass, he, alignedCodes]

theorem expected_alignedCodes_eq (old : Finset (Direction F))
    (a : MergedPairs F) (l : Line F) :
    (∑ M : MergedPairs F,
      (exposedLaw old a M).toReal * ((alignedCodes M l).card : ℝ)) =
      ∑ c : Code F, alignmentMass old a l c := by
  simp_rw [alignmentMass_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _
  rw [← Finset.sum_filter]
  simp [mul_comm]

theorem expected_successfulCodes_le (old : Finset (Direction F))
    (a : MergedPairs F) (l : Line F) :
    (∑ M : MergedPairs F,
      (exposedLaw old a M).toReal * ((successfulCodes M l).card : ℝ)) ≤
      20480 * ((old.card : ℝ) + 1) ^ 4 := by
  calc
    _ ≤ ∑ M : MergedPairs F,
        (exposedLaw old a M).toReal * ((alignedCodes M l).card : ℝ) := by
      apply Finset.sum_le_sum
      intro M _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      exact_mod_cast Finset.card_filter_le (alignedCodes M l)
        (fun c => Function.Injective (tuplePoint M ⟨c.1, c.2⟩))
    _ = _ := expected_alignedCodes_eq old a l
    _ ≤ _ := sum_alignmentMass_le old a l

theorem expected_successfulCodes_le_of_card_le (old : Finset (Direction F))
    (a : MergedPairs F) (l : Line F) (m : ℕ) (hm : old.card ≤ m) :
    (∑ M : MergedPairs F,
      (exposedLaw old a M).toReal * ((successfulCodes M l).card : ℝ)) ≤
      20480 * ((m : ℝ) + 1) ^ 4 := by
  apply (expected_successfulCodes_le old a l).trans
  gcongr

end
end Balanced.CandidatePrescribed

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ProbabilityPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced

open MeasureTheory Filter
open scoped Topology

theorem pmf_outerReal_compl {Ω : Type*} (p : PMF Ω) (A : Set Ω) :
    (p.toOuterMeasure Aᶜ).toReal = 1 - (p.toOuterMeasure A).toReal := by
  let : MeasurableSpace Ω := ⊤
  have hA : MeasurableSet A := by trivial
  have hcompl := probReal_compl_eq_one_sub (μ := p.toMeasure) hA
  simpa only [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure_apply p hA,
    PMF.toMeasure_apply_eq_toOuterMeasure_apply p hA.compl] using hcompl

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateRootFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.TupleAlignment

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem choice_on_line_of_successful {M : MergedPairs F} {g : Direction F}
    {a : RootPrescription g} (ha : a ∈ successfulPrescriptions M g) :
    ∀ i, OnLine (tuplePoint M a.tuple i) (a.choice M).line := by
  obtain ⟨c, hc⟩ := (Finset.mem_filter.mp ha).2.1
  intro i
  change lineEval g (tuplePoint M a.tuple i) = lineEval g (tuplePoint M a.tuple 0)
  exact (hc i).trans (hc 0).symm

theorem rootFiberSquareCount_eq_pair_card (M : MergedPairs F) (g : Direction F) :
    rootFiberSquareCount M g = (commonLineSuccessPairs M g).card := by
  have hfiber (l : Line F) :
      (commonLineSuccessPairs M g).filter (fun ab => (ab.1.choice M).line = l) =
        ((successfulPrescriptions M g).filter (fun a => (a.choice M).line = l)).product
          ((successfulPrescriptions M g).filter (fun a => (a.choice M).line = l)) := by
    ext ab
    simp only [commonLineSuccessPairs, Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨ha, hb⟩, hab⟩, hal⟩
      exact ⟨⟨ha, hal⟩, hb, hab.symm.trans hal⟩
    · rintro ⟨⟨ha, hal⟩, hb, hbl⟩
      exact ⟨⟨⟨ha, hb⟩, hal.trans hbl.symm⟩, hal⟩
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun ab : RootPrescription g × RootPrescription g => (ab.1.choice M).line)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  simp only [rootFiberSquareCount, hfiber, Finset.product_eq_sprod, Finset.card_product, pow_two]

theorem mem_successfulPrescriptions_fiber_iff (M : MergedPairs F)
    {g : Direction F} (a : RootPrescription g) (c : F) :
    a ∈ (successfulPrescriptions M g).filter
      (fun b => (b.choice M).line = (g, c)) ↔
      (∀ i, OnLine (tuplePoint M a.tuple i) (g, c)) ∧
      Function.Injective (tuplePoint M a.tuple) := by
  constructor
  · intro ha
    obtain ⟨hs, hl⟩ := Finset.mem_filter.mp ha
    exact ⟨fun i => hl ▸ choice_on_line_of_successful hs i,
      (Finset.mem_filter.mp hs).2.2⟩
  · rintro ⟨hc, hd⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨c, hc⟩, hd⟩, ?_⟩
    exact Prod.ext rfl (hc 0)

theorem mem_commonLineSuccessPairs_iff (M : MergedPairs F)
    {g : Direction F} (ab : RootPrescription g × RootPrescription g) :
    ab ∈ commonLineSuccessPairs M g ↔
      (∃ c, (∀ i, OnLine (tuplePoint M ab.1.tuple i) (g, c)) ∧
        (∀ i, OnLine (tuplePoint M ab.2.tuple i) (g, c))) ∧
      Function.Injective (tuplePoint M ab.1.tuple) ∧
      Function.Injective (tuplePoint M ab.2.tuple) := by
  simp only [commonLineSuccessPairs, Finset.mem_filter, Finset.product_eq_sprod,
    Finset.mem_product]
  constructor
  · rintro ⟨⟨ha, hb⟩, hab⟩
    refine ⟨⟨(ab.1.choice M).line.2, ?_, ?_⟩,
      (Finset.mem_filter.mp ha).2.2, (Finset.mem_filter.mp hb).2.2⟩
    · exact choice_on_line_of_successful ha
    · intro i
      exact hab ▸ choice_on_line_of_successful hb i
  · rintro ⟨⟨c, ha, hb⟩, hia, hib⟩
    have hfa := (mem_successfulPrescriptions_fiber_iff M ab.1 c).mpr ⟨ha, hia⟩
    have hfb := (mem_successfulPrescriptions_fiber_iff M ab.2 c).mpr ⟨hb, hib⟩
    obtain ⟨hsa, hla⟩ := Finset.mem_filter.mp hfa
    obtain ⟨hsb, hlb⟩ := Finset.mem_filter.mp hfb
    exact ⟨⟨hsa, hsb⟩, hla.trans hlb.symm⟩

end
end Balanced.TupleAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteExposureTower
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ConditionalRestriction

noncomputable section
open scoped Classical
open MeasureTheory

universe u
variable {D A : Type u} [Fintype D] [Fintype A] [DecidableEq D] [Nonempty A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

theorem filtered_integral_mul_le (old extra : Finset D) (a : D → A)
    (f z : (D → A) → ℝ) (C Bf Bz : ℝ) (hC : 0 ≤ C)
    (hfn : ∀ ω, 0 ≤ f ω) (hzn : ∀ ω, 0 ≤ z ω)
    (hfb : ∀ ω, f ω ≤ Bf) (hzb : ∀ ω, z ω ≤ Bz)
    (hdepends : ∀ ω ω', (∀ d ∈ old ∪ extra, ω d = ω' d) → f ω = f ω')
    (hbound : ∀ y : D → A,
      (∫ ω, z ω ∂((PMF.uniformOfFintype (D → A)).filter
        {ω | ∀ d, d ∈ old ∪ extra → ω d = y d}
        (fixed_supported (fun d => d ∈ old ∪ extra) y)).toMeasure) ≤ C) :
    (∫ ω, f ω * z ω ∂((PMF.uniformOfFintype (D → A)).filter
      {ω | ∀ d, d ∈ old → ω d = a d}
      (fixed_supported (fun d => d ∈ old) a)).toMeasure) ≤
      C * ∫ ω, f ω ∂((PMF.uniformOfFintype (D → A)).filter
        {ω | ∀ d, d ∈ old → ω d = a d}
        (fixed_supported (fun d => d ∈ old) a)).toMeasure := by
  let P : PatternModel := uniformArrayModel (D := D) (A := A)
  have hconvert (J : Finset D) (y : D → A) (G : (D → A) → ℝ) :
      P.fixedExpectation J y G =
        ∫ ω, G ω ∂((PMF.uniformOfFintype (D → A)).filter
          {ω | ∀ d, d ∈ J → ω d = y d}
          (fixed_supported (fun d => d ∈ J) y)).toMeasure := by
    rw [← integral_fixArray_eq_filtered (fun d => d ∈ J) y G]
    apply integral_congr_ae
    filter_upwards [] with ω
    congr 1
    funext d
    dsimp [P, uniformArrayModel, PatternModel.fixCoordinates, fixArray]
    exact @ite_cond_congr A (d ∈ J) (d ∈ J)
      (Finset.decidableMem d J) (Classical.propDecidable _) (y d) (ω d) rfl
  rw [← hconvert old a (fun ω => f ω * z ω), ← hconvert old a f]
  apply P.fixedExpectation_mul_le_of_fixedBounds old extra a f z C Bf Bz hC
    (show Measurable f from measurable_of_countable f)
    (show Measurable z from measurable_of_countable z) hfn hzn hfb hzb hdepends
  intro y
  exact (hconvert (old ∪ extra) y z).trans_le (hbound y)

theorem integral_eq_of_eq_on_support {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (f g : Ω → ℝ) (h : ∀ ω ∈ p.support, f ω = g ω) :
    (∫ ω, f ω ∂p.toMeasure) = ∫ ω, g ω ∂p.toMeasure := by
  simp only [PMF.integral_eq_sum, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : ω ∈ p.support
  · rw [h ω hω]
  · have hp : p ω = 0 := by simpa [PMF.mem_support_iff] using hω
    simp [hp]

end
end Balanced.ConditionalRestriction

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidatePairCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidatePairs

noncomputable section
open scoped Classical BigOperators
open MeasureTheory PartialAlignment ConditionalRestriction
open CandidateExposure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem lineCount_eq_successfulCodes (M : MergedPairs F) (l : Line F) :
    lineCount M l = (CandidatePrescribed.successfulCodes M l).card := by
  apply Finset.card_bij (fun T _ => (T.generator, T.side))
  · intro T hT
    simpa [lineTuples, eligibleTuples, CandidatePrescribed.successfulCodes,
      CandidatePrescribed.alignedCodes, CandidatePrescribed.Eligible, and_assoc] using hT
  · intro T _ U _ h
    cases T
    cases U
    cases h
    rfl
  · intro c hc
    refine ⟨⟨c.1, c.2⟩, ?_, rfl⟩
    simpa [lineTuples, eligibleTuples, CandidatePrescribed.successfulCodes,
      CandidatePrescribed.alignedCodes, CandidatePrescribed.Eligible, and_assoc] using hc

theorem lineCount_le_card (M : MergedPairs F) (l : Line F) :
    lineCount M l ≤ Fintype.card (FourTuple F) := Finset.card_le_univ _

omit [Fintype F] in
theorem tuplePoint_eq_of_generators (T : FourTuple F) (M N : MergedPairs F)
    (h : ∀ d ∈ generatorSet T, M d = N d) (i : Fin 4) :
    tuplePoint M T i = tuplePoint N T i := by
  have hi : T.generator i ∈ generatorSet T := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hn : T.generator (i+1) ∈ generatorSet T :=
    Finset.mem_image.mpr ⟨i+1, Finset.mem_univ _, rfl⟩
  simp only [tuplePoint, constituent, h _ hi, h _ hn]

omit [Fintype F] in
theorem successfulInDirection_congr (T : FourTuple F) (g : Direction F)
    (M N : MergedPairs F) (h : ∀ d ∈ generatorSet T, M d = N d) :
    M ∈ successfulInDirection T g ↔ N ∈ successfulInDirection T g := by
  have heq : tuplePoint M T = tuplePoint N T := funext (tuplePoint_eq_of_generators T M N h)
  simp only [successfulInDirection, alignedInDirection, Set.mem_ofPred_eq, heq]

section Measurable
variable [MeasurableSpace F] [MeasurableSingletonClass F]

theorem conditional_lineCount_le (old : Finset (Direction F)) (a : MergedPairs F)
    (l : Line F) (m : ℕ) (hm : old.card ≤ m) :
    (∫ M, (lineCount M l : ℝ) ∂(exposedLaw old a).toMeasure) ≤
      (20480 * (m + 1) ^ 4 : ℝ) := by
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul, lineCount_eq_successfulCodes]
  exact CandidatePrescribed.expected_successfulCodes_le_of_card_le old a l m hm

theorem conditional_partnerCount_le (old : Finset (Direction F))
    (T : FourTuple F) (g : Direction F) (a : MergedPairs F)
    (m : ℕ) (hm : old.card ≤ m) :
    (∫ M, (lineCount M (targetLine g T M) : ℝ)
      ∂(exposedLaw (old ∪ generatorSet T) a).toMeasure) ≤
      (20480 * (m + 4 + 1) ^ 4 : ℝ) := by
  have heq := integral_eq_of_eq_on_support (exposedLaw (old ∪ generatorSet T) a)
    (fun M => (lineCount M (targetLine g T M) : ℝ))
    (fun M => (lineCount M (targetLine g T a) : ℝ)) (by
      intro M hM
      have hexposed := (PMF.mem_support_filter_iff
        (canonical_exposure_supported (old ∪ generatorSet T) a)).mp hM |>.1
      have hp := tuplePoint_eq_of_generators T M a
        (fun d hd => hexposed d (Finset.mem_union_right _ hd)) 0
      simp only [targetLine, hp])
  rw [heq]
  have hgen : (generatorSet T).card ≤ 4 := by
    exact (Finset.card_image_le).trans (by simp)
  have hu : (old ∪ generatorSet T).card ≤ m + 4 :=
    (Finset.card_union_le _ _).trans (by omega)
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    conditional_lineCount_le (old ∪ generatorSet T) a (targetLine g T a) (m + 4) hu

theorem exposed_integral_mul_le (old extra : Finset (Direction F)) (a : MergedPairs F)
    (f z : MergedPairs F → ℝ) (C Bf Bz : ℝ) (hC : 0 ≤ C)
    (hfn : ∀ M, 0 ≤ f M) (hzn : ∀ M, 0 ≤ z M)
    (hfb : ∀ M, f M ≤ Bf) (hzb : ∀ M, z M ≤ Bz)
    (hdep : ∀ M N, (∀ d ∈ old ∪ extra, M d = N d) → f M = f N)
    (hbound : ∀ y, (∫ M, z M ∂(exposedLaw (old ∪ extra) y).toMeasure) ≤ C) :
    (∫ M, f M * z M ∂(exposedLaw old a).toMeasure) ≤
      C * ∫ M, f M ∂(exposedLaw old a).toMeasure := by
  have huni : offsetLaw F = PMF.uniformOfFintype (MergedPairs F) := by
    apply PMF.ext
    intro M
    simp only [offsetLaw, PMF.uniformOfFintype_apply, Fintype.card_eq_nat_card]
  simp only [exposedLaw, huni] at hbound ⊢
  exact filtered_integral_mul_le (D := Direction F) (A := Bool → F)
    old extra a f z C Bf Bz hC hfn hzn hfb hzb hdep hbound

theorem integral_success_indicator (old : Finset (Direction F)) (a : MergedPairs F)
    (T : FourTuple F) (g : Direction F) :
    (∫ M, (if M ∈ successfulInDirection T g then (1 : ℝ) else 0)
      ∂(exposedLaw old a).toMeasure) =
      conditionalProbability old a (successfulInDirection T g) := by
  have hh := integral_eventCount_eq_sum (exposedLaw old a) ({T} : Finset (FourTuple F))
    (fun U => successfulInDirection U g)
  have heq : (fun M : MergedPairs F =>
      ((({T} : Finset (FourTuple F)).filter
        (fun U => M ∈ successfulInDirection U g)).card : ℝ)) =
      (fun M => if M ∈ successfulInDirection T g then 1 else 0) := by
    funext M
    by_cases hM : M ∈ successfulInDirection T g <;>
      simp only [Finset.filter_singleton, hM, ite_true, ite_false,
        Finset.card_singleton, Finset.card_empty, Nat.cast_one, Nat.cast_zero]
  rw [heq] at hh
  simpa only [Finset.sum_singleton, conditionalProbability] using hh

theorem conditional_first_partner_le (old : Finset (Direction F))
    (T : FourTuple F) (g : Direction F) (a : MergedPairs F)
    (m : ℕ) (hm : old.card ≤ m) :
    (∫ M, (if M ∈ successfulInDirection T g then
      (lineCount M (targetLine g T M) : ℝ) else 0)
      ∂(exposedLaw old a).toMeasure) ≤
      (20480 * (m + 4 + 1) ^ 4 : ℝ) *
        conditionalProbability old a (successfulInDirection T g) := by
  let f : MergedPairs F → ℝ := fun M => if M ∈ successfulInDirection T g then 1 else 0
  let z : MergedPairs F → ℝ := fun M => lineCount M (targetLine g T M)
  have h := exposed_integral_mul_le old (generatorSet T) a f z
    (20480 * (m + 4 + 1) ^ 4) 1 (Fintype.card (FourTuple F)) (by positivity)
    (fun M => by dsimp [f]; split_ifs <;> norm_num)
    (fun M => by dsimp [z]; positivity)
    (fun M => by dsimp [f]; split_ifs <;> norm_num)
    (fun M => by dsimp [z]; exact_mod_cast lineCount_le_card M (targetLine g T M))
    (by
      intro M N hMN
      have hs := successfulInDirection_congr T g M N
        (fun d hd => hMN d (Finset.mem_union_right _ hd))
      simp only [f, hs])
    (fun y => conditional_partnerCount_le old T g y m hm)
  change (∫ M, f M * z M ∂(exposedLaw old a).toMeasure) ≤
      _ * ∫ M, f M ∂(exposedLaw old a).toMeasure at h
  rw [show (∫ M, f M ∂(exposedLaw old a).toMeasure) =
    conditionalProbability old a (successfulInDirection T g) from
      integral_success_indicator old a T g] at h
  simpa only [f, z, ite_mul, one_mul, zero_mul] using h

theorem integral_sum_pmf {Ω I : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (s : Finset I) (f : I → Ω → ℝ) :
    (∫ ω, ∑ i ∈ s, f i ω ∂p.toMeasure) =
      ∑ i ∈ s, ∫ ω, f i ω ∂p.toMeasure := by
  simp only [PMF.integral_eq_sum, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem conditional_sum_first_partner_le (old : Finset (Direction F))
    (s : Finset (FourTuple F)) (g : Direction F) (a : MergedPairs F)
    (m : ℕ) (hm : old.card ≤ m) :
    (∫ M, (∑ T ∈ s, if M ∈ successfulInDirection T g then
      (lineCount M (targetLine g T M) : ℝ) else 0)
      ∂(exposedLaw old a).toMeasure) ≤
      (20480 * (m + 4 + 1) ^ 4 : ℝ) *
        ∑ T ∈ s, conditionalProbability old a (successfulInDirection T g) := by
  rw [integral_sum_pmf, Finset.mul_sum]
  exact Finset.sum_le_sum (fun T _ => conditional_first_partner_le old T g a m hm)

theorem conditional_pairCount_le (old : Finset (Direction F))
    (g : Direction F) (a : MergedPairs F) (m : ℕ) (hm : old.card ≤ m) :
    (∫ M, (pairCount g M : ℝ) ∂(exposedLaw old a).toMeasure) ≤
      (20480 * (m + 4 + 1) ^ 4 : ℝ) *
        (20480 * (m + 1) ^ 4) * Fintype.card F := by
  have h := conditional_sum_first_partner_le old (eligibleTuples g) g a m hm
  have hn : (0 : ℝ) ≤ 20480 * (m + 4 + 1) ^ 4 := by positivity
  have hb := mul_le_mul_of_nonneg_left (successProbabilitySum_le g old a m hm) hn
  have heq (M : MergedPairs F) : (pairCount g M : ℝ) =
      ∑ T ∈ eligibleTuples g, if M ∈ successfulInDirection T g then
        (lineCount M (targetLine g T M) : ℝ) else 0 := by
    simp only [pairCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  simp_rw [heq]
  exact h.trans (by simpa only [successProbabilitySum, mul_assoc] using hb)

theorem conditional_firstOverlapPairCount_le (old : Finset (Direction F))
    (g : Direction F) (a : MergedPairs F) (m : ℕ) (hm : old.card ≤ m) :
    (∫ M, (firstOverlapPairCount old g M : ℝ) ∂(exposedLaw old a).toMeasure) ≤
      (20480 * (m + 4 + 1) ^ 4 : ℝ) * (16384 * (m + 1) ^ 4) := by
  have h := conditional_sum_first_partner_le old
    ((eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T old).card)) g a m hm
  have hn : (0 : ℝ) ≤ 20480 * (m + 4 + 1) ^ 4 := by positivity
  have hb := mul_le_mul_of_nonneg_left (overlapProbabilitySum_le g old a m hm) hn
  have heq (M : MergedPairs F) : (firstOverlapPairCount old g M : ℝ) =
      ∑ T ∈ (eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T old).card),
        if M ∈ successfulInDirection T g then
          (lineCount M (targetLine g T M) : ℝ) else 0 := by
    simp only [firstOverlapPairCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  simp_rw [heq]
  exact h.trans hb

end Measurable
end
end Balanced.CandidatePairs

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidatePairPatternModel
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Balanced.CandidateExposure

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

theorem pairPatternModel_support_card_le (g : Direction F) (a : EligiblePair g) :
    ((pairPatternModel g).support a).card ≤ 8 := by
  have h₁ : (generatorSet a.1.val).card = 4 := by
    have hi := (Finset.mem_filter.mp a.1.property).2.1
    exact (Finset.card_image_of_injective _ hi).trans (by simp)
  have h₂ : (generatorSet a.2.val).card = 4 := by
    have hi := (Finset.mem_filter.mp a.2.property).2.1
    exact (Finset.card_image_of_injective _ hi).trans (by simp)
  calc
    _ ≤ (generatorSet a.1.val).card + (generatorSet a.2.val).card :=
      Finset.card_union_le _ _
    _ = 8 := by rw [h₁, h₂]

theorem pairPatternModel_count (g : Direction F) (M : MergedPairs F) :
    (pairPatternModel g).count M =
      ((Finset.univ.filter fun a : EligiblePair g => M ∈ pairSuccessEvent g a).card : ℝ) := by
  simp only [PatternModel.count, PatternModel.indicator, pairPatternModel,
    Set.indicator_apply, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem pairSuccessEvent_swap (g : Direction F) (a : EligiblePair g) :
    pairSuccessEvent g a.swap = pairSuccessEvent g a := by
  ext M
  constructor <;> rintro ⟨⟨c, h₁, h₂⟩, hi₁, hi₂⟩ <;>
    exact ⟨⟨c, h₂, h₁⟩, hi₂, hi₁⟩

theorem pairPatternModel_overlapCount (g : Direction F)
    (K₀ K : Finset (Direction F)) (M : MergedPairs F) :
    (pairPatternModel g).overlapCount K₀ K M =
      ((Finset.univ.filter fun a : EligiblePair g =>
        ¬ Disjoint ((generatorSet a.1.val ∪ generatorSet a.2.val) \ K₀) K ∧
          M ∈ pairSuccessEvent g a).card : ℝ) := by
  simp only [PatternModel.overlapCount, PatternModel.indicator, pairPatternModel,
    Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Set.indicator_apply]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

attribute [local instance] OAI.Balanced.CandidateExposure.pairModelMeasurableSpace
theorem pairPatternModel_measure (g : Direction F) :
    (pairPatternModel g).measure = (offsetLaw F).toMeasure :=
  TupleAlignment.rootPatternModel_measure g

theorem pairPatternModel_fixedExpectation_exposed (g : Direction F)
    (K : Finset (Direction F)) (x : MergedPairs F) (f : MergedPairs F → ℝ) :
    (pairPatternModel g).fixedExpectation K x f =
      ∫ M, f M ∂(exposedLaw K x).toMeasure :=
  TupleAlignment.rootPatternModel_fixedExpectation_exposed g K x f

theorem mem_pairSuccessEvent_iff (g : Direction F) (a : EligiblePair g)
    (M : MergedPairs F) :
    M ∈ pairSuccessEvent g a ↔
      M ∈ successfulInDirection a.1.val g ∧
      (∀ i, OnLine (tuplePoint M a.2.val i)
        (g, lineEval g (tuplePoint M a.1.val 0))) ∧
      Function.Injective (tuplePoint M a.2.val) := by
  constructor
  · rintro ⟨⟨c, h₁, h₂⟩, hi₁, hi₂⟩
    refine ⟨⟨⟨c, h₁⟩, hi₁⟩, ?_, hi₂⟩
    have hc : lineEval g (tuplePoint M a.1.val 0) = c := h₁ 0
    simpa only [hc] using h₂
  · rintro ⟨⟨⟨c, h₁⟩, hi₁⟩, h₂, hi₂⟩
    refine ⟨⟨c, h₁, ?_⟩, hi₁, hi₂⟩
    have hc : lineEval g (tuplePoint M a.1.val 0) = c := h₁ 0
    simpa only [hc] using h₂

end Balanced.CandidateExposure

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidatePairFibers
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidatePairs
noncomputable section
open scoped Classical BigOperators
open CandidateExposure TupleAlignment
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem sum_partner_eq_pair_card (g : Direction F) (M : MergedPairs F)
    (R : FourTuple F → Prop) :
    (∑ T ∈ (eligibleTuples g).filter R,
      if M ∈ successfulInDirection T g then lineCount M (targetLine g T M) else 0) =
      ((successfulPairs g M).filter (fun a => R a.1.val)).card := by
  have hline (T : FourTuple F) :
      lineCount M (targetLine g T M) =
        ∑ U : ↥(eligibleTuples g),
          if (∀ i, OnLine (tuplePoint M U.val i) (targetLine g T M)) ∧
            Function.Injective (tuplePoint M U.val) then 1 else 0 := by
    unfold lineCount lineTuples
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_subtype (eligibleTuples g)
      (p := fun U => U ∈ eligibleTuples g) (F := inferInstance) (fun _ => Iff.rfl)
      (fun tuple => if (∀ index, OnLine (tuplePoint M tuple index) (targetLine g T M)) ∧
        Function.Injective (tuplePoint M tuple) then (1 : ℕ) else 0)
  have hs := Finset.sum_subtype (eligibleTuples g)
    (p := fun T => T ∈ eligibleTuples g) (F := inferInstance) (fun _ => Iff.rfl)
    (fun T => if R T then
      (if M ∈ successfulInDirection T g then lineCount M (targetLine g T M) else 0) else 0)
  rw [Finset.sum_filter, hs]
  simp_rw [hline]
  simp only [successfulPairs, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hR : R T.val <;> by_cases hT : M ∈ successfulInDirection T.val g
  all_goals simp only [hR, hT, ite_true, ite_false]
  · apply Finset.sum_congr rfl
    intro U _
    simp only [mem_pairSuccessEvent_iff, hT, true_and, targetLine]
    split_ifs with hsuccess <;> simp [hsuccess]
  · symm
    apply Finset.sum_eq_zero
    intro U _
    simp only [mem_pairSuccessEvent_iff, hT, false_and, ite_false]
  · symm
    apply Finset.sum_eq_zero
    intro U _
    simp
  · symm
    apply Finset.sum_eq_zero
    intro U _
    simp

theorem pairCount_eq_successfulPairs_card (g : Direction F) (M : MergedPairs F) :
    pairCount g M = (successfulPairs g M).card := by
  simpa only [pairCount, Finset.filter_true] using
    sum_partner_eq_pair_card g M (fun _ => True)

theorem successfulPairs_card_eq_rootFiberSquareCount (g : Direction F) (M : MergedPairs F) :
    (successfulPairs g M).card = rootFiberSquareCount M g := by
  let e : EligiblePair g ≃ RootPrescription g × RootPrescription g :=
    Equiv.prodCongr (eligibleTupleEquivRootPrescription g)
      (eligibleTupleEquivRootPrescription g)
  have hevent (a : EligiblePair g) :
      M ∈ pairSuccessEvent g a ↔ e a ∈ commonLineSuccessPairs M g := by
    rw [mem_commonLineSuccessPairs_iff]
    simp only [e, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, equivRootPrescription_tuple,
      pairSuccessEvent, Set.mem_ofPred_eq]
  rw [rootFiberSquareCount_eq_pair_card]
  have h := Equiv.sum_comp e
    (fun ab => if ab ∈ commonLineSuccessPairs M g then (1 : ℕ) else 0)
  have hc : (Finset.univ.filter (fun ab : RootPrescription g × RootPrescription g =>
      ab ∈ commonLineSuccessPairs M g)) = commonLineSuccessPairs M g := by
    ext ab
    simp
  rw [← hc]
  simpa only [successfulPairs, Finset.card_eq_sum_ones, Finset.sum_filter, ← hevent] using h

theorem pairCount_eq_rootFiberSquareCount (g : Direction F) (M : MergedPairs F) :
    pairCount g M = rootFiberSquareCount M g :=
  (pairCount_eq_successfulPairs_card g M).trans
    (successfulPairs_card_eq_rootFiberSquareCount g M)

theorem pairPatternModel_count_eq_pairCount (g : Direction F) (M : MergedPairs F) :
    (pairPatternModel g).count M = (pairCount g M : ℝ) := by
  rw [pairPatternModel_count, pairCount_eq_successfulPairs_card]
  rfl

theorem firstOverlapPairCount_eq_card (D : Finset (Direction F))
    (g : Direction F) (M : MergedPairs F) :
    firstOverlapPairCount D g M =
      ((successfulPairs g M).filter
        (fun a => ¬ Disjoint (generatorSet a.1.val) D)).card := by
  have h := sum_partner_eq_pair_card g M
    (fun T => 0 < (PartialAlignment.exposedTupleIndices T D).card)
  convert h using 1
  · unfold firstOverlapPairCount
    apply Finset.sum_congr
    · ext T
      simp
    · intro T hT
      split_ifs <;> rfl
  · congr 1
    ext a
    simp only [Finset.mem_filter, not_disjoint_generatorSet_iff]

theorem swap_mem_successfulPairs (g : Direction F) (M : MergedPairs F)
    (a : EligiblePair g) : a.swap ∈ successfulPairs g M ↔ a ∈ successfulPairs g M := by
  simp only [successfulPairs, Finset.mem_filter, Finset.mem_univ, true_and,
    pairSuccessEvent_swap]

theorem second_overlap_card_eq_first (D : Finset (Direction F))
    (g : Direction F) (M : MergedPairs F) :
    ((successfulPairs g M).filter
      (fun a => ¬ Disjoint (generatorSet a.2.val) D)).card =
    ((successfulPairs g M).filter
      (fun a => ¬ Disjoint (generatorSet a.1.val) D)).card := by
  apply Finset.card_bij (fun a _ => a.swap)
  · intro a ha
    obtain ⟨hs, ho⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨(swap_mem_successfulPairs g M a).mpr hs, ho⟩
  · intro a ha b hb hab
    exact Prod.swap_injective hab
  · intro a ha
    obtain ⟨hs, ho⟩ := Finset.mem_filter.mp ha
    exact ⟨a.swap, Finset.mem_filter.mpr
      ⟨(swap_mem_successfulPairs g M a).mpr hs, ho⟩, Prod.swap_swap a⟩

theorem pairPatternModel_allExposed_overlap_le (D : Finset (Direction F))
    (g : Direction F) (M : MergedPairs F) :
    (pairPatternModel g).overlapCount ∅ D M ≤
      2 * (firstOverlapPairCount D g M : ℝ) := by
  let A := (successfulPairs g M).filter
    (fun a => ¬ Disjoint (generatorSet a.1.val) D)
  let B := (successfulPairs g M).filter
    (fun a => ¬ Disjoint (generatorSet a.2.val) D)
  let U := Finset.univ.filter (fun a : EligiblePair g =>
    ¬ Disjoint (generatorSet a.1.val ∪ generatorSet a.2.val) D ∧
      M ∈ pairSuccessEvent g a)
  have hsub : U ⊆ A ∪ B := by
    intro a ha
    obtain ⟨_, ho, hs⟩ := Finset.mem_filter.mp ha
    have hsuccess : a ∈ successfulPairs g M := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hs⟩
    by_cases hfirst : Disjoint (generatorSet a.1.val) D
    · apply Finset.mem_union_right
      refine Finset.mem_filter.mpr ⟨hsuccess, ?_⟩
      intro hsecond
      exact ho (Finset.disjoint_union_left.mpr ⟨hfirst, hsecond⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hsuccess, hfirst⟩)
  have hcard : U.card ≤ 2 * firstOverlapPairCount D g M := by
    calc
      U.card ≤ (A ∪ B).card := Finset.card_le_card hsub
      _ ≤ A.card + B.card := Finset.card_union_le _ _
      _ = 2 * firstOverlapPairCount D g M := by
        dsimp [A, B]
        rw [second_overlap_card_eq_first, ← firstOverlapPairCount_eq_card]
        omega
  rw [pairPatternModel_overlapCount]
  simp only [Finset.sdiff_empty]
  exact_mod_cast hcard

end
end Balanced.CandidatePairs

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidatePairMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidatePairs

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateExposure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem pairTotalConstant_nonneg (m : ℕ) : 0 ≤ pairTotalConstant m := by
  unfold pairTotalConstant
  positivity

theorem pairFirstOverlapConstant_nonneg (m : ℕ) : 0 ≤ pairFirstOverlapConstant m := by
  unfold pairFirstOverlapConstant
  positivity

theorem pairExposureConstant_nonneg (m : ℕ) : 0 ≤ pairExposureConstant m :=
  add_nonneg (pairTotalConstant_nonneg m)
    (mul_nonneg (by norm_num) (pairFirstOverlapConstant_nonneg m))

attribute [local instance] OAI.Balanced.CandidatePairs.pairMomentMeasurableSpace
theorem pairPatternModel_total_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (pairPatternModel g).fixedExpectation D a (pairPatternModel g).count ≤
      pairExposureConstant m * Fintype.card F := by
  rw [pairPatternModel_fixedExpectation_exposed]
  simp_rw [pairPatternModel_count_eq_pairCount]
  apply (conditional_pairCount_le D g a m hD).trans
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  exact le_add_of_nonneg_right
    (mul_nonneg (by norm_num) (pairFirstOverlapConstant_nonneg m))

theorem pairPatternModel_overlap_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (pairPatternModel g).fixedExpectation D a
      ((pairPatternModel g).overlapCount ∅ D) ≤ pairExposureConstant m := by
  rw [pairPatternModel_fixedExpectation_exposed]
  calc
    _ ≤ ∫ M, 2 * (firstOverlapPairCount D g M : ℝ) ∂(exposedLaw D a).toMeasure := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro M
      exact pairPatternModel_allExposed_overlap_le D g M
    _ = 2 * ∫ M, (firstOverlapPairCount D g M : ℝ) ∂(exposedLaw D a).toMeasure :=
      integral_const_mul _ _
    _ ≤ 2 * pairFirstOverlapConstant m :=
      mul_le_mul_of_nonneg_left (conditional_firstOverlapPairCount_le D g a m hD)
        (by norm_num)
    _ ≤ pairExposureConstant m := le_add_of_nonneg_left (pairTotalConstant_nonneg m)

theorem pairCenteredMomentConstant_nonneg (m s : ℕ) :
    0 ≤ pairCenteredMomentConstant m s := by
  unfold pairCenteredMomentConstant
  have hC := pairExposureConstant_nonneg (m + 16*s)
  positivity

theorem pairPatternModel_centered_moment_le (g : Direction F)
    (K₀ : Finset (Direction F)) (a : MergedPairs F) (m s : ℕ) (hK : K₀.card ≤ m) :
    (pairPatternModel g).fixedExpectation K₀ a
      (fun M => |(pairPatternModel g).count M -
        (pairPatternModel g).fixedExpectation K₀ a (pairPatternModel g).count|^(2*s)) ≤
      pairCenteredMomentConstant m s * (Fintype.card F : ℝ)^s := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos (α := F)
  apply (pairPatternModel g).centered_moment_le_of_allExposedBounds
    K₀ a s 8 (Fintype.card F) (pairExposureConstant (m + 16*s))
    hq (pairExposureConstant_nonneg _) (pairPatternModel_support_card_le g)
  · intro D hD y
    exact pairPatternModel_total_le g D y (m + 16*s) (by omega)
  · intro D hD y
    exact pairPatternModel_overlap_le g D y (m + 16*s) (by omega)

theorem pairCount_centered_moment_le (g : Direction F) (s : ℕ) :
    (∫ M, |(pairCount g M : ℝ) -
      ∫ N, (pairCount g N : ℝ) ∂(offsetLaw F).toMeasure|^(2*s)
      ∂(offsetLaw F).toMeasure) ≤
      pairCenteredMomentConstant 0 s * (Fintype.card F : ℝ)^s := by
  have h := pairPatternModel_centered_moment_le g ∅ (fun _ _ => 0) 0 s (by simp)
  simp only [PatternModel.fixedExpectation] at h
  rw [pairPatternModel_measure] at h
  simp_rw [pairPatternModel_count_eq_pairCount] at h
  exact h

theorem mean_pairCount_le (g : Direction F) :
    (∫ M, (pairCount g M : ℝ) ∂(offsetLaw F).toMeasure) ≤
      pairExposureConstant 0 * Fintype.card F := by
  have h := pairPatternModel_total_le g ∅ (fun _ _ => 0) 0 (by simp)
  simp only [PatternModel.fixedExpectation] at h
  rw [pairPatternModel_measure] at h
  simp_rw [pairPatternModel_count_eq_pairCount] at h
  exact h

theorem pairCount_upper_tail (g : Direction F) :
    (offsetLaw F).toMeasure.real
      {M | pairLinearThreshold * Fintype.card F < (pairCount g M : ℝ)} ≤
      pairCenteredMomentConstant 0 2 / (Fintype.card F : ℝ)^2 := by
  let q : ℝ := Fintype.card F
  let μ := (offsetLaw F).toMeasure
  let b : ℝ := ∫ M, (pairCount g M : ℝ) ∂μ
  have hq0 : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos (α := F)
  have hb : b ≤ pairExposureConstant 0 * q := mean_pairCount_le g
  have hsub : {M | pairLinearThreshold * q < (pairCount g M : ℝ)} ⊆
      {M | q^4 ≤ |(pairCount g M : ℝ) - b|^4} := by
    intro M hM
    have hh : (pairExposureConstant 0 + 1) * q < (pairCount g M : ℝ) := hM
    have hd : q ≤ |(pairCount g M : ℝ) - b| :=
      (show q ≤ (pairCount g M : ℝ) - b by nlinarith).trans (le_abs_self _)
    exact pow_le_pow_left₀ hq0.le hd 4
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun M => |(pairCount g M : ℝ) - b|^4)
    (Filter.Eventually.of_forall (fun _ => by positivity)) Integrable.of_finite (q^4)
  have hmoment : (∫ M, |(pairCount g M : ℝ) - b|^4 ∂μ) ≤
      pairCenteredMomentConstant 0 2 * q^2 := by
    simpa only [b, μ, q] using pairCount_centered_moment_le g 2
  have hbound : q^4 * μ.real {M | pairLinearThreshold * q < (pairCount g M : ℝ)} ≤
      pairCenteredMomentConstant 0 2 * q^2 :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (by positivity)).trans
      (hm.trans hmoment)
  change μ.real _ ≤ pairCenteredMomentConstant 0 2 / q^2
  calc
    _ ≤ (pairCenteredMomentConstant 0 2 * q^2) / q^4 := by
      apply (le_div_iff₀ (pow_pos hq0 4)).mpr
      simpa only [mul_comm] using hbound
    _ = pairCenteredMomentConstant 0 2 / q^2 := by
      field_simp

theorem pairCount_any_upper_tail :
    (offsetLaw F).toMeasure.real
      {M | ∃ g : Direction F,
        pairLinearThreshold * Fintype.card F < (pairCount g M : ℝ)} ≤
      2 * pairCenteredMomentConstant 0 2 / (Fintype.card F : ℝ) := by
  let E : Direction F → Set (MergedPairs F) :=
    fun g => {M | pairLinearThreshold * Fintype.card F < (pairCount g M : ℝ)}
  have heq : {M | ∃ g : Direction F,
      pairLinearThreshold * Fintype.card F < (pairCount g M : ℝ)} = ⋃ g, E g := by
    ext M
    simp [E]
  rw [heq]
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos (α := F)
  have hq0 : (0 : ℝ) < Fintype.card F := by linarith
  calc
    _ ≤ ∑ g : Direction F, (offsetLaw F).toMeasure.real (E g) :=
      measureReal_iUnion_fintype_le E
    _ ≤ ∑ _g : Direction F, pairCenteredMomentConstant 0 2 / (Fintype.card F : ℝ)^2 :=
      Finset.sum_le_sum (fun g _ => pairCount_upper_tail g)
    _ = ((Fintype.card F : ℝ) + 1) *
        (pairCenteredMomentConstant 0 2 / (Fintype.card F : ℝ)^2) := by
      simp [Direction, Fintype.card_option]
    _ ≤ (2 * (Fintype.card F : ℝ)) *
        (pairCenteredMomentConstant 0 2 / (Fintype.card F : ℝ)^2) := by
      gcongr
      · exact div_nonneg (pairCenteredMomentConstant_nonneg 0 2) (by positivity)
      · linarith
    _ = 2 * pairCenteredMomentConstant 0 2 / (Fintype.card F : ℝ) := by
      field_simp

theorem rootFiberSquareCount_any_upper_tail :
    (offsetLaw F).toMeasure.real
      {M | ∃ g : Direction F, pairLinearThreshold * Fintype.card F <
        (TupleAlignment.rootFiberSquareCount M g : ℝ)} ≤
      2 * pairCenteredMomentConstant 0 2 / (Fintype.card F : ℝ) := by
  simpa only [← pairCount_eq_rootFiberSquareCount] using
    (pairCount_any_upper_tail (F := F))

end
end Balanced.CandidatePairs

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateAbundanceAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateAbundanceAssembly

noncomputable section
open scoped Classical Topology
open Filter MeasureTheory TupleAlignment CandidateValidityAssembly CandidatePairs

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

attribute [local instance] OAI.Balanced.CandidateAbundanceAssembly.abundanceAssemblyMeasurableSpace
omit [DecidableEq F] in
private theorem measureReal_eq_offset (E : Set (MergedPairs F)) :
    (offsetLaw F).toMeasure.real E = offsetEventProbability E := by
  rw [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure_apply _
    (Set.toFinite E).measurableSet]
  rfl

section Limits
variable (F : ℕ → Type*) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
  [∀ n, DecidableEq (F n)]

omit [∀ n, DecidableEq (F n)] in
private theorem tendsto_good_of_bad (G B : ∀ n, Set (MergedPairs (F n)))
    (hcompl : ∀ n, G n = (B n)ᶜ)
    (hbad : Tendsto (fun n => offsetEventProbability (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => offsetEventProbability (G n)) atTop (𝓝 1) := by
  have heq (n : ℕ) : offsetEventProbability (G n) =
      1 - offsetEventProbability (B n) := by
    rw [hcompl n, offsetEventProbability, pmf_outerReal_compl]
    rfl
  simpa only [heq, sub_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub hbad

attribute [local instance] OAI.Balanced.CandidateAbundanceAssembly.abundanceAssemblyMeasurableSpace
theorem tendsto_square_fibers_oai
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability {M : MergedPairs (F n) |
      ∀ g, (rootFiberSquareCount M g : ℝ) ≤
        pairLinearThreshold * Fintype.card (F n)}) atTop (𝓝 1) := by
  have hqR : Tendsto (fun n => (Fintype.card (F n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  have hbad : Tendsto (fun n => offsetEventProbability {M : MergedPairs (F n) |
      ∃ g, pairLinearThreshold * Fintype.card (F n) <
        (rootFiberSquareCount M g : ℝ)}) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) ?_
      (hqR.const_div_atTop (2 * pairCenteredMomentConstant 0 2))
    intro n
    simpa only [measureReal_eq_offset, offsetEventProbability] using
      (rootFiberSquareCount_any_upper_tail (F := F n))
  apply tendsto_good_of_bad F _ _ (fun n => ?_) hbad
  ext M
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_lt]

end Limits
end
end Balanced.CandidateAbundanceAssembly

end OAI
end

theorem solution.{u_2} : type_of% @OAI.Balanced.CandidateAbundanceAssembly.tendsto_square_fibers_oai.{u_2} := @OAI.Balanced.CandidateAbundanceAssembly.tendsto_square_fibers_oai.{u_2}
