-- Prove2me | solution 1 for OAI.Balanced.CandidateIncidenceTests.candidateGraphResult_of_size_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:14:22.073749+00:00
-- url     : https://prove2.me/submissions/4c13bd26-92b2-4a47-ac60-ff46b9d67823

import Mathlib
import Definitions.Def_OAIQ63Br002
import Definitions.Def_OAIQ63Br003
import Theorems.Thm_OAI_Balanced_CandidateIncidenceTests_candidateGraphResult_of_incidence_estimates
import Theorems.Thm_OAI_Balanced_CandidateIncidenceTests_tendsto_smallGood

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_TupleAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.TupleAlignment

variable {F : Type*} [Field F]

section Finite
variable [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
theorem tuplePosition_uniform (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool) :
    (PMF.uniformOfFintype (Fin 4 → Bool → F)).map
      (tuplePositionEquiv d hd σ) = PMF.uniformOfFintype (Fin 4 → Point F) :=
  uniform_map_equiv (tuplePositionEquiv d hd σ)

end Finite

end Balanced.TupleAlignment

end OAI
end

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
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_GlobalTupleLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem tuplePoint_uniform (T : FourTuple F) (hT : Function.Injective T.generator) :
    (offsetLaw F).map (fun M => tuplePoint M T) =
      PMF.uniformOfFintype (Fin 4 → Point F) := by
  classical
  let hd := adjacent_ne_of_injective T hT
  let r : MergedPairs F → Fin 4 → Bool → F := fun M i => M (T.generator i)
  have hoff : offsetLaw F = PMF.uniformOfFintype (Direction F → Bool → F) := by
    ext M
    simp only [offsetLaw, PMF.uniformOfFintype_apply, Fintype.card_fun,
      Fintype.card_option, Fintype.card_bool]
  have hrestrict := uniform_map_restrict (ι := Fin 4) (D := Direction F)
    (A := Bool → F) ⟨T.generator, hT⟩
  simp only [Function.Embedding.coeFn_mk] at hrestrict
  have hf : (fun M => tuplePoint M T) = (tuplePositionEquiv T.generator hd T.side) ∘ r := by
    funext M i
    simp only [Function.comp_apply, tuplePositionEquiv_apply, tuplePoint, constituent]
    rfl
  rw [hf, ← PMF.map_comp, hoff]
  dsimp only [r]
  rw [hrestrict]
  exact tuplePosition_uniform T.generator hd T.side

end Balanced.TupleAlignment

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
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateLineGate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateLineGate

noncomputable section
open scoped Classical BigOperators
open CandidateExposure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in
theorem exposed_constituents_avoid (D : Finset (Direction F))
    (a : MergedPairs F) (L : Line F) (ha : L ∉ constituentLines a) :
    ∀ d ∈ D, ∀ b, constituent a d b ≠ L := by
  intro d _ b heq
  apply ha
  exact Finset.mem_image.mpr ⟨(d, b), Finset.mem_univ _, heq⟩

end
end Balanced.CandidateLineGate

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffineIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F]

theorem eq_of_onLine_same_direction (p : Point F) (l m : Line F)
    (hdir : l.1 = m.1) (hl : OnLine p l) (hm : OnLine p m) : l = m := by
  rw [line_eq_lineThrough p l hl, line_eq_lineThrough p m hm, hdir]

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateFreshIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateFreshIncidence

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem offset_probability_eq (T : FourTuple F)
    (hT : Function.Injective T.generator) (P : (Fin 4 → Point F) → Prop) :
    offsetEventProbability {M | P (tuplePoint M T)} = positionProbability P := by
  classical
  have h := congrArg (fun μ : PMF (Fin 4 → Point F) =>
    (μ.toOuterMeasure {p | P p}).toReal) (TupleAlignment.tuplePoint_uniform T hT)
  rw [PMF.toOuterMeasure_map_apply] at h
  exact h

omit [DecidableEq F] in
theorem positionProbability_eq_card (P : (Fin 4 → Point F) → Prop) :
    positionProbability P =
      (Fintype.card {p : Fin 4 → Point F // P p} : ℝ) / (Fintype.card F : ℝ)^8 := by
  classical
  rw [positionProbability, PMF.toOuterMeasure_uniformOfFintype_apply,
    ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_mul, Fintype.card_fun,
    Fintype.card_fin, Point, Fintype.card_prod, Nat.cast_pow, Nat.cast_mul]
  congr 1
  ring

omit [DecidableEq F] in
theorem positionProbability_mono {P Q : (Fin 4 → Point F) → Prop}
    (h : ∀ p, P p → Q p) : positionProbability P ≤ positionProbability Q := by
  classical
  rw [positionProbability_eq_card, positionProbability_eq_card]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Fintype.card_subtype_mono P Q h

omit [DecidableEq F] in
theorem positionProbability_exists_le {ι : Type*} [Fintype ι]
    (P : ι → (Fin 4 → Point F) → Prop) :
    positionProbability (fun p => ∃ i, P i p) ≤ ∑ i, positionProbability (P i) := by
  classical
  let : DecidablePred (fun p : Fin 4 → Point F => ∃ i, P i p) :=
    fun p => Classical.propDecidable (∃ i, P i p)
  simp_rw [positionProbability_eq_card]
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hc : Fintype.card {p : Fin 4 → Point F // ∃ i, P i p} ≤
      Fintype.card (Σ i, {p : Fin 4 → Point F // P i p}) := by
    classical
    let f : {p : Fin 4 → Point F // ∃ i, P i p} →
        Σ i, {p : Fin 4 → Point F // P i p} := fun p =>
      ⟨Classical.choose p.2, p.1, Classical.choose_spec p.2⟩
    apply Fintype.card_le_of_injective f
    intro p r h
    apply Subtype.ext
    exact congrArg (fun z : Σ i, {p : Fin 4 → Point F // P i p} => z.2.1) h
  rw [Fintype.card_sigma] at hc
  exact_mod_cast hc

omit [DecidableEq F] in
theorem positionProbability_rectangle (S : Fin 4 → Finset (Point F)) :
    positionProbability (fun p => ∀ i, p i ∈ S i) =
      (∏ i, ((S i).card : ℝ)) / (Fintype.card F : ℝ)^8 := by
  classical
  let : DecidablePred (fun p : Fin 4 → Point F => ∀ i, p i ∈ S i) :=
    fun p => Classical.propDecidable (∀ i, p i ∈ S i)
  rw [positionProbability_eq_card]
  congr 1
  have hc : Fintype.card {p : Fin 4 → Point F // ∀ i, p i ∈ S i} =
      ∏ i, (S i).card := by
    classical
    rw [Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun i x => x ∈ S i))]
    simp
  exact_mod_cast hc

theorem positionProbability_one_fixed (i : Fin 4) (y : Point F) (l : Line F) :
    positionProbability (fun p => ∀ j,
      p j ∈ if j = i then {y} else linePoints l) =
      (Fintype.card F : ℝ)⁻¹^5 := by
  classical
  rw [positionProbability_rectangle]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  fin_cases i <;> simp [Fin.prod_univ_four, linePoints_card] <;>
    field_simp

theorem aligned_fixed_position_le (i : Fin 4) (y : Point F) (l : Line F) :
    positionProbability (fun p => (∀ j, OnLine (p j) l) ∧ p i = y) ≤
      (Fintype.card F : ℝ)⁻¹^5 := by
  classical
  rw [← positionProbability_one_fixed i y l]
  apply positionProbability_mono
  intro p hp j
  by_cases hj : j = i
  · simp [hj, hp.2]
  · simp [hj, linePoints, hp.1 j]

theorem aligned_probability (l : Line F) :
    positionProbability (fun p => ∀ j, OnLine (p j) l) =
      (Fintype.card F : ℝ)⁻¹^4 := by
  classical
  have h := positionProbability_rectangle (fun _ : Fin 4 => linePoints l)
  simp only [linePoints, Finset.mem_filter, Finset.mem_univ, true_and] at h
  change positionProbability (fun p => ∀ j, OnLine (p j) l) =
    (∏ _i : Fin 4, ((linePoints l).card : ℝ)) / (Fintype.card F : ℝ)^8 at h
  rw [h, linePoints_card]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

omit [DecidableEq F] in
theorem positionProbability_exists_le_card {ι : Type*} [Fintype ι]
    (P : ι → (Fin 4 → Point F) → Prop) (r : ℝ)
    (h : ∀ i, positionProbability (P i) ≤ r) :
    positionProbability (fun p => ∃ i, P i p) ≤ (Fintype.card ι : ℝ) * r := by
  classical
  calc
    _ ≤ ∑ i, positionProbability (P i) := positionProbability_exists_le P
    _ ≤ ∑ _i : ι, r := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp

theorem same_direction_position_on_line_le (g : Direction F) (i : Fin 4) (l : Line F) :
    positionProbability (fun p =>
      (∃ c, ∀ j, OnLine (p j) (g,c)) ∧ OnLine (p i) l) ≤
      (Fintype.card F : ℝ)⁻¹^4 := by
  classical
  by_cases hgl : g = l.1
  · rw [← aligned_probability l]
    apply positionProbability_mono
    rintro p ⟨⟨c, hc⟩, hi⟩ j
    have heq : (g,c) = l := eq_of_onLine_same_direction (p i) (g,c) l hgl (hc i) hi
    simpa only [heq] using hc j
  · let P : F → (Fin 4 → Point F) → Prop := fun c p =>
      (∀ j, OnLine (p j) (g,c)) ∧ p i = lineIntersection (g,c) l
    have hsub : ∀ p, ((∃ c, ∀ j, OnLine (p j) (g,c)) ∧ OnLine (p i) l) →
        ∃ c, P c p := by
      rintro p ⟨⟨c, hc⟩, hi⟩
      refine ⟨c, hc, ?_⟩
      exact common_point_eq_of_lines_ne (g,c) l
        (fun heq => hgl (congrArg Prod.fst heq)) (p i) (lineIntersection (g,c) l)
        (hc i) hi (onLine_lineIntersection_left _ _ hgl)
        (onLine_lineIntersection_right _ _ hgl)
    calc
      _ ≤ positionProbability (fun p => ∃ c, P c p) := positionProbability_mono hsub
      _ ≤ (Fintype.card F : ℝ) * (Fintype.card F : ℝ)⁻¹^5 :=
        positionProbability_exists_le_card P _
          (fun c => aligned_fixed_position_le i (lineIntersection (g,c) l) (g,c))
      _ = _ := by
        have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
        field_simp

theorem same_direction_hits_line_le (g : Direction F) (l : Line F) :
    positionProbability (fun p =>
      (∃ c, ∀ j, OnLine (p j) (g,c)) ∧ ∃ i, OnLine (p i) l) ≤
      4 * (Fintype.card F : ℝ)⁻¹^4 := by
  classical
  let P : Fin 4 → (Fin 4 → Point F) → Prop := fun i p =>
    (∃ c, ∀ j, OnLine (p j) (g,c)) ∧ OnLine (p i) l
  apply (positionProbability_mono (Q := fun p => ∃ i, P i p) ?_).trans
  · simpa only [Fintype.card_fin, Nat.cast_ofNat] using
      positionProbability_exists_le_card P _ (fun i => same_direction_position_on_line_le g i l)
  · rintro p ⟨hc, i, hi⟩
    exact ⟨i, hc, hi⟩

end
end Balanced.CandidateFreshIncidence

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_UnexposedTupleLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.TupleAlignment

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem unexposed_generator_offsets_law (T : FourTuple F)
    (hinj : Function.Injective T.generator)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (hfresh : ∀ i, T.generator i ∉ D) :
    ((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (PartialAlignment.canonical_exposure_supported D a)).map
        (fun M i => M (T.generator i)) =
      PMF.uniformOfFintype (Fin 4 → Bool → F) := by
  have hempty : PartialAlignment.exposedTupleIndices T D = ∅ := by
    ext i
    simp [PartialAlignment.exposedTupleIndices, hfresh i]
  have hevent : {o : Fin 4 → Bool → F |
      ∀ i ∈ PartialAlignment.exposedTupleIndices T D,
        o i = a (T.generator i)} = Set.univ := by simp [hempty]
  have hfilter : (PMF.uniformOfFintype (Fin 4 → Bool → F)).filter
      {o | ∀ i ∈ PartialAlignment.exposedTupleIndices T D,
        o i = a (T.generator i)}
      (PartialAlignment.partialOffsets_supported
        (PartialAlignment.exposedTupleIndices T D) (fun i => a (T.generator i))) =
      PMF.uniformOfFintype (Fin 4 → Bool → F) := by
    ext o
    simp only [PMF.filter_apply, hevent, Set.indicator_univ, PMF.tsum_coe,
      inv_one, mul_one]
  simpa only [PartialAlignment.offsetLaw_eq_uniform] using
    (PartialAlignment.global_exposed_tuple_law T hinj D a).trans hfilter

theorem unexposed_tuplePoint_law (T : FourTuple F)
    (hinj : Function.Injective T.generator)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (hfresh : ∀ i, T.generator i ∉ D) :
    ((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (PartialAlignment.canonical_exposure_supported D a)).map
        (fun M => tuplePoint M T) = PMF.uniformOfFintype (Fin 4 → Point F) := by
  let hd := adjacent_ne_of_injective T hinj
  let r : MergedPairs F → Fin 4 → Bool → F := fun M i => M (T.generator i)
  have hf : (fun M => tuplePoint M T) =
      (tuplePositionEquiv T.generator hd T.side) ∘ r := by
    funext M i
    rfl
  rw [hf, ← PMF.map_comp]
  change (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
    (PartialAlignment.canonical_exposure_supported D a)).map r).map
      (tuplePositionEquiv T.generator hd T.side) = _
  rw [unexposed_generator_offsets_law T hinj D a hfresh]
  exact tuplePosition_uniform T.generator hd T.side

theorem unexposed_tuplePoint_event_probability (T : FourTuple F)
    (hinj : Function.Injective T.generator)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (hfresh : ∀ i, T.generator i ∉ D) (E : Set (Fin 4 → Point F)) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (PartialAlignment.canonical_exposure_supported D a)).toOuterMeasure
        {M | tuplePoint M T ∈ E}).toReal =
      offsetEventProbability {M | tuplePoint M T ∈ E} := by
  have hcond := congrArg (fun law : PMF (Fin 4 → Point F) =>
    (law.toOuterMeasure E).toReal) (unexposed_tuplePoint_law T hinj D a hfresh)
  have horiginal := congrArg (fun law : PMF (Fin 4 → Point F) =>
    (law.toOuterMeasure E).toReal) (tuplePoint_uniform T hinj)
  rw [PMF.toOuterMeasure_map_apply] at hcond horiginal
  exact hcond.trans horiginal.symm

end
end Balanced.TupleAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateConditionalFreshIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateFreshIncidence

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem conditional_probability_eq_positionProbability (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hfresh : ∀ i, T.generator i ∉ D)
    (P : (Fin 4 → Point F) → Prop) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (PartialAlignment.canonical_exposure_supported D a)).toOuterMeasure
        {M | P (tuplePoint M T)}).toReal = positionProbability P := by
  exact (TupleAlignment.unexposed_tuplePoint_event_probability T hT D a hfresh
    {p | P p}).trans (offset_probability_eq T hT P)

theorem conditional_tuple_hits_line_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hfresh : ∀ i, T.generator i ∉ D)
    (g : Direction F) (l : Line F) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (PartialAlignment.canonical_exposure_supported D a)).toOuterMeasure
        {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
          ∃ i, OnLine (tuplePoint M T i) l}).toReal ≤
      4 * (Fintype.card F : ℝ)⁻¹^4 := by
  rw [conditional_probability_eq_positionProbability T hT D a hfresh (fun p =>
    (∃ c, ∀ j, OnLine (p j) (g,c)) ∧ ∃ i, OnLine (p i) l)]
  exact same_direction_hits_line_le g l

end
end Balanced.CandidateFreshIncidence

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_PartialIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PartialAlignment
open TupleAlignment
noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in
private theorem card_fixed_function_coordinate {ι : Type*} [Fintype ι]
    [DecidableEq ι] (i : ι) (x : F) :
    Fintype.card {f : ι → F // f i = x} =
      Fintype.card F ^ (Fintype.card ι - 1) := by
  rw [Fintype.card_subtype]
  simpa only [Fintype.piFinset_univ, Finset.card_univ] using
    Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset F) i
      (Finset.mem_univ x)

theorem card_markedPartialOffsets_le (d : Fin 4 → Direction F)
    (hd : ∀ j, d j ≠ d (j + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ j, d j ≠ g) (c : F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F)
    (i : Fin 4) (hi : i ∈ freePositions J) (y : Point F) :
    Fintype.card (MarkedPartialOffsets d hd σ g c J a i y) ≤
      Fintype.card F ^ ((freePositions J).card - 1) := by
  classical
  by_cases hy : OnLine y (g,c)
  · let coord : F := (linePointEquiv g c) ⟨y,hy⟩
    let k : {j : Fin 4 // j ∈ freePositions J} := ⟨i,hi⟩
    let record : MarkedPartialOffsets d hd σ g c J a i y →
        {f : {j : Fin 4 // j ∈ freePositions J} → F // f k = coord} := fun o =>
      ⟨alignedFreeCoordinates d hd σ g c J a ⟨o.1,o.2.1⟩, by
        change (linePointEquiv g c)
          ⟨tuplePositionEquiv d hd σ o.1.1 i, o.2.1 i⟩ = coord
        apply congrArg (linePointEquiv g c)
        exact Subtype.ext o.2.2⟩
    have hinj : Function.Injective record := by
      intro o p h
      have hcoords := congrArg Subtype.val h
      have hpartial := alignedFreeCoordinates_injective d hd σ g hg c J a hcoords
      exact Subtype.ext (congrArg
        (fun z : AlignedPartialOffsets d hd σ g c J a => z.1) hpartial)
    calc
      _ ≤ Fintype.card
          {f : {j : Fin 4 // j ∈ freePositions J} → F // f k = coord} :=
        Fintype.card_le_of_injective record hinj
      _ = _ := by rw [card_fixed_function_coordinate]; simp
  · let : IsEmpty (MarkedPartialOffsets d hd σ g c J a i y) :=
      ⟨fun o => hy (o.2.2 ▸ o.2.1 i)⟩
    rw [Fintype.card_of_isEmpty]
    exact Nat.zero_le _

theorem partial_marked_alignment_probability_le (d : Fin 4 → Direction F)
    (hd : ∀ j, d j ≠ d (j + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ j, d j ≠ g) (c : F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F)
    (i : Fin 4) (hi : i ∈ freePositions J) (y : Point F) :
    ((PMF.uniformOfFintype (PartialOffsets J a)).toOuterMeasure
      {o | (∀ j, OnLine (tuplePositionEquiv d hd σ o.1 j) (g,c)) ∧
        tuplePositionEquiv d hd σ o.1 i = y}).toReal ≤
      (Fintype.card F : ℝ)⁻¹ ^ (5 - (fixedPositions J).card) := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]
  change (Fintype.card (MarkedPartialOffsets d hd σ g c J a i y) : ℝ) /
    (Fintype.card (PartialOffsets J a) : ℝ) ≤ _
  rw [card_partialOffsets, Nat.cast_pow]
  have hcard : (Fintype.card (MarkedPartialOffsets d hd σ g c J a i y) : ℝ) ≤
      (Fintype.card F : ℝ) ^ ((freePositions J).card - 1) := by
    exact_mod_cast card_markedPartialOffsets_le d hd σ g hg c J a i hi y
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hfree : 0 < (freePositions J).card := Finset.card_pos.mpr ⟨i,hi⟩
  have hfixed : (fixedPositions J).card ≤ 4 := by
    simpa only [Fintype.card_fin] using (fixedPositions J).card_le_univ
  have hexp : ((freePositions J).card - 1) + (5 - (fixedPositions J).card) =
      2 * (freshGenerators J).card := by
    have := alignment_exponent_identity J
    omega
  calc
    _ ≤ (Fintype.card F : ℝ) ^ ((freePositions J).card - 1) /
        (Fintype.card F : ℝ) ^ (2 * (freshGenerators J).card) :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ = _ := by
      rw [← hexp, pow_add, div_mul_eq_div_div, div_self (pow_ne_zero _ hq),
        one_div, inv_pow]

theorem original_conditional_marked_alignment_probability_le
    (d : Fin 4 → Direction F) (hd : ∀ j, d j ≠ d (j + 1))
    (σ : Fin 4 → Bool) (g : Direction F) (hg : ∀ j, d j ≠ g) (c : F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F)
    (i : Fin 4) (hi : i ∈ freePositions J) (y : Point F) :
    (((PMF.uniformOfFintype (Fin 4 → Bool → F)).filter
      {o | ∀ j ∈ J, o j = a j} (partialOffsets_supported J a)).toOuterMeasure
      {o | (∀ j, OnLine (tuplePositionEquiv d hd σ o j) (g,c)) ∧
        tuplePositionEquiv d hd σ o i = y}).toReal ≤
      (Fintype.card F : ℝ)⁻¹ ^ (5 - (fixedPositions J).card) := by
  rw [partialOffsets_conditional_law, PMF.toOuterMeasure_map_apply]
  exact partial_marked_alignment_probability_le d hd σ g hg c J a i hi y

theorem canonical_conditional_marked_alignment_probability_le
    (T : FourTuple F) (hT : Function.Injective T.generator)
    (g : Direction F) (hg : ∀ j, T.generator j ≠ g) (c : F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (i : Fin 4) (hi : i ∈ freePositions (exposedTupleIndices T D)) (y : Point F) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure
      {M | (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
        tuplePoint M T i = y}).toReal ≤
      (Fintype.card F : ℝ)⁻¹ ^ (5 - (fixedPositions (exposedTupleIndices T D)).card) := by
  let hd := adjacent_ne_of_injective T hT
  let E : Set (Fin 4 → Bool → F) := {o |
    (∀ j, OnLine (tuplePositionEquiv T.generator hd T.side o j) (g,c)) ∧
      tuplePositionEquiv T.generator hd T.side o i = y}
  have h := congrArg (fun law => (law.toOuterMeasure E).toReal)
    (global_exposed_tuple_law T hT D a)
  rw [PMF.toOuterMeasure_map_apply] at h
  have hle := original_conditional_marked_alignment_probability_le
    T.generator hd T.side g hg c (exposedTupleIndices T D)
      (fun j => a (T.generator j)) i hi y
  have hresult := h.trans_le hle
  simpa only [offsetLaw_eq_uniform, E, Set.preimage_ofPred_eq,
    tuplePositionEquiv_apply, tuplePoint, constituent] using hresult

theorem canonical_conditional_transverse_hit_probability_le
    (T : FourTuple F) (hT : Function.Injective T.generator)
    (g : Direction F) (hg : ∀ j, T.generator j ≠ g) (c : F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (i : Fin 4) (hi : i ∈ freePositions (exposedTupleIndices T D))
    (L : Line F) (htrans : g ≠ L.1) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure
      {M | (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
        OnLine (tuplePoint M T i) L}).toReal ≤
      (Fintype.card F : ℝ)⁻¹ ^ (5 - (fixedPositions (exposedTupleIndices T D)).card) := by
  have hevent : {M : MergedPairs F |
      (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧ OnLine (tuplePoint M T i) L} =
      {M | (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
        tuplePoint M T i = lineIntersection (g,c) L} := by
    ext M
    constructor
    · intro h
      refine ⟨h.1, ?_⟩
      exact common_point_eq_of_lines_ne (g,c) L
        (fun heq => htrans (congrArg Prod.fst heq))
        (tuplePoint M T i) (lineIntersection (g,c) L) (h.1 i) h.2
        (onLine_lineIntersection_left _ _ htrans)
        (onLine_lineIntersection_right _ _ htrans)
    · intro h
      refine ⟨h.1, ?_⟩
      rw [h.2]
      exact onLine_lineIntersection_right _ _ htrans
  rw [hevent]
  exact canonical_conditional_marked_alignment_probability_le T hT g hg c D a i hi _

private theorem pmf_outer_ne_top {α : Type*} (p : PMF α) (E : Set α) :
    p.toOuterMeasure E ≠ ⊤ := by
  have h : p.toOuterMeasure E ≤ 1 := by
    calc
      _ ≤ p.toOuterMeasure Set.univ := p.toOuterMeasure.mono (Set.subset_univ _)
      _ = 1 := by simp [PMF.toOuterMeasure_apply]
  exact ne_of_lt (h.trans_lt (by simp))

private theorem pmf_real_mono {α : Type*} (p : PMF α) {E G : Set α}
    (h : E ⊆ G) : (p.toOuterMeasure E).toReal ≤ (p.toOuterMeasure G).toReal :=
  ENNReal.toReal_mono (pmf_outer_ne_top p G) (p.toOuterMeasure.mono h)

theorem conditionalHitProbability_le_alignment (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (g : Direction F) (hg : ∀ j, T.generator j ≠ g)
    (i : Fin 4) (L : Line F) (c : F) :
    conditionalHitProbability T D a g i L c ≤
      (Fintype.card F : ℝ)⁻¹ ^ (4 - (fixedPositions (exposedTupleIndices T D)).card) := by
  exact (pmf_real_mono _ (fun _ h => h.1)).trans
    (canonical_conditional_alignment_probability_le T hT g hg c D a)

theorem card_possibleHitOffsets_le_one (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (g : Direction F) (i : Fin 4) (L : Line F)
    (hincident : T.generator i ∈ D ∨ T.generator (i + 1) ∈ D)
    (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L) :
    (possibleHitOffsets T D a g i L).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro c hc e he
  obtain ⟨M,hM,hMc,hML⟩ := (Finset.mem_filter.mp hc).2
  obtain ⟨N,hN,hNe,hNL⟩ := (Finset.mem_filter.mp he).2
  have hpoints : tuplePoint M T i = tuplePoint N T i := by
    rcases hincident with hi | hi
    · have hm : OnLine (tuplePoint M T i)
          (constituent a (T.generator i) (T.side i)) := by
        have h := onLine_lineIntersection_left
          (constituent M (T.generator i) (T.side i))
          (constituent M (T.generator (i + 1)) (!(T.side (i + 1))))
          (adjacent_ne_of_injective T hT i)
        simpa only [tuplePoint, constituent, hM _ hi] using h
      have hn : OnLine (tuplePoint N T i)
          (constituent a (T.generator i) (T.side i)) := by
        have h := onLine_lineIntersection_left
          (constituent N (T.generator i) (T.side i))
          (constituent N (T.generator (i + 1)) (!(T.side (i + 1))))
          (adjacent_ne_of_injective T hT i)
        simpa only [tuplePoint, constituent, hN _ hi] using h
      exact common_point_eq_of_lines_ne _ L (havoid _ hi _) _ _ hm hML hn hNL
    · have hm : OnLine (tuplePoint M T i)
          (constituent a (T.generator (i + 1)) (!(T.side (i + 1)))) := by
        have h := onLine_lineIntersection_right
          (constituent M (T.generator i) (T.side i))
          (constituent M (T.generator (i + 1)) (!(T.side (i + 1))))
          (adjacent_ne_of_injective T hT i)
        simpa only [tuplePoint, constituent, hM _ hi] using h
      have hn : OnLine (tuplePoint N T i)
          (constituent a (T.generator (i + 1)) (!(T.side (i + 1)))) := by
        have h := onLine_lineIntersection_right
          (constituent N (T.generator i) (T.side i))
          (constituent N (T.generator (i + 1)) (!(T.side (i + 1))))
          (adjacent_ne_of_injective T hT i)
        simpa only [tuplePoint, constituent, hN _ hi] using h
      exact common_point_eq_of_lines_ne _ L (havoid _ hi _) _ _ hm hML hn hNL
  exact (hMc i).symm.trans ((congrArg (lineEval g) hpoints).trans (hNe i))

theorem conditionalHitProbability_eq_zero_of_not_possible (T : FourTuple F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (g : Direction F) (i : Fin 4) (L : Line F) (c : F)
    (hc : c ∉ possibleHitOffsets T D a g i L) :
    conditionalHitProbability T D a g i L c = 0 := by
  unfold conditionalHitProbability
  have hz : ((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure
      {M | (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
        OnLine (tuplePoint M T i) L} = 0 := by
    apply (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
    apply Set.disjoint_left.mpr
    intro M hM hE
    have hexposed := (PMF.mem_support_filter_iff _).mp hM
    exact hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, M, hexposed.1, hE⟩)
  rw [hz, ENNReal.toReal_zero]

private theorem fixedPositions_card_zero_of_le_one (J : Finset (Fin 4))
    (hJ : J.card ≤ 1) : (fixedPositions J).card = 0 := by
  have h : ∀ J : Finset (Fin 4), J.card ≤ 1 → (fixedPositions J).card = 0 := by decide
  exact h J hJ

theorem sum_conditionalHitProbability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (g : Direction F) (hg : ∀ j, T.generator j ≠ g)
    (hsmall : (exposedTupleIndices T D).card ≤ 1)
    (i : Fin 4) (L : Line F) (htrans : g ≠ L.1)
    (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L) :
    (∑ c : F, conditionalHitProbability T D a g i L c) ≤
      (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  have hfixed := fixedPositions_card_zero_of_le_one (exposedTupleIndices T D) hsmall
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  by_cases hfree : i ∈ freePositions (exposedTupleIndices T D)
  · calc
      _ ≤ ∑ _c : F, (Fintype.card F : ℝ)⁻¹ ^ 5 := by
        apply Finset.sum_le_sum
        intro c _
        simpa only [conditionalHitProbability, hfixed, Nat.sub_zero] using
          canonical_conditional_transverse_hit_probability_le T hT g hg c D a i hfree L htrans
      _ = (Fintype.card F : ℝ) * (Fintype.card F : ℝ)⁻¹ ^ 5 := by simp
      _ = _ := by field_simp
  · have hincident : T.generator i ∈ D ∨ T.generator (i + 1) ∈ D := by
      by_contra h
      push Not at h
      apply hfree
      simp [freePositions, exposedTupleIndices, h.1, h.2]
    have hcount := card_possibleHitOffsets_le_one T hT D a g i L hincident havoid
    have hsum : (∑ c ∈ possibleHitOffsets T D a g i L,
        conditionalHitProbability T D a g i L c) =
        ∑ c : F, conditionalHitProbability T D a g i L c := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro c _ hc
      exact conditionalHitProbability_eq_zero_of_not_possible T D a g i L c hc
    rw [← hsum]
    calc
      _ ≤ ∑ _c ∈ possibleHitOffsets T D a g i L, (Fintype.card F : ℝ)⁻¹ ^ 4 := by
        apply Finset.sum_le_sum
        intro c _
        simpa only [hfixed, Nat.sub_zero] using
          conditionalHitProbability_le_alignment T hT D a g hg i L c
      _ = ((possibleHitOffsets T D a g i L).card : ℝ) *
          (Fintype.card F : ℝ)⁻¹ ^ 4 := by simp
      _ ≤ 1 * (Fintype.card F : ℝ)⁻¹ ^ 4 :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (by positivity)
      _ = _ := one_mul _

private theorem pmf_real_iUnion_le {α ι : Type*} [Fintype ι]
    (p : PMF α) (E : ι → Set α) :
    (p.toOuterMeasure (⋃ i, E i)).toReal ≤ ∑ i, (p.toOuterMeasure (E i)).toReal := by
  have htop : (∑ i, p.toOuterMeasure (E i)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i _ => pmf_outer_ne_top p (E i))
  have h := ENNReal.toReal_mono htop
    (MeasureTheory.measure_iUnion_fintype_le p.toOuterMeasure E)
  rw [ENNReal.toReal_sum (fun i _ => pmf_outer_ne_top p (E i))] at h
  exact h

theorem sum_conditional_any_hit_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (g : Direction F) (hg : ∀ j, T.generator j ≠ g)
    (hsmall : (exposedTupleIndices T D).card ≤ 1)
    (L : Line F) (htrans : g ≠ L.1)
    (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L) :
    (∑ c : F,
      (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
        (canonical_exposure_supported D a)).toOuterMeasure
        {M | (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
          ∃ i, OnLine (tuplePoint M T i) L}).toReal) ≤
      4 * (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  calc
    _ ≤ ∑ c : F, ∑ i : Fin 4, conditionalHitProbability T D a g i L c := by
      apply Finset.sum_le_sum
      intro c _
      have hevent : {M : MergedPairs F |
          (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧ ∃ i, OnLine (tuplePoint M T i) L} =
          ⋃ i : Fin 4, {M | (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
            OnLine (tuplePoint M T i) L} := by
        ext M
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
        constructor
        · rintro ⟨ha,i,hi⟩
          exact ⟨i,ha,hi⟩
        · rintro ⟨i,ha,hi⟩
          exact ⟨ha,i,hi⟩
      rw [hevent]
      exact pmf_real_iUnion_le _ _
    _ = ∑ i : Fin 4, ∑ c : F, conditionalHitProbability T D a g i L c :=
      Finset.sum_comm
    _ ≤ ∑ _i : Fin 4, (Fintype.card F : ℝ)⁻¹ ^ 4 := by
      apply Finset.sum_le_sum
      intro i _
      exact sum_conditionalHitProbability_le T hT D a g hg hsmall i L htrans havoid
    _ = _ := by simp

theorem canonical_conditional_one_exposed_hit_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (g : Direction F) (hg : ∀ j, T.generator j ≠ g)
    (hsmall : (exposedTupleIndices T D).card ≤ 1)
    (L : Line F) (htrans : g ≠ L.1)
    (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure
      {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
        ∃ i, OnLine (tuplePoint M T i) L}).toReal ≤
      4 * (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  have hevent : {M : MergedPairs F |
      (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧ ∃ i, OnLine (tuplePoint M T i) L} =
      ⋃ c : F, {M | (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
        ∃ i, OnLine (tuplePoint M T i) L} := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨c,hc⟩,hi⟩
      exact ⟨c,hc,hi⟩
    · rintro ⟨c,hc,hi⟩
      exact ⟨⟨c,hc⟩,hi⟩
  rw [hevent]
  exact (pmf_real_iUnion_le _ _).trans
    (sum_conditional_any_hit_probability_le T hT D a g hg hsmall L htrans havoid)

end
end Balanced.PartialAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidatePartialPointIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidatePartialPointIncidence

noncomputable section
open scoped Classical
open PartialAlignment

private theorem pmf_probability_mono {Ω : Type*} (μ : PMF Ω)
    {A B : Set Ω} (h : A ⊆ B) :
    (μ.toOuterMeasure A).toReal ≤ (μ.toOuterMeasure B).toReal := by
  have hu : μ.toOuterMeasure Set.univ = 1 :=
    (μ.toOuterMeasure_apply_eq_one_iff Set.univ).mpr (Set.subset_univ _)
  have hb : μ.toOuterMeasure B ≠ ⊤ := by
    apply ne_of_lt
    apply (μ.toOuterMeasure.mono (Set.subset_univ B)).trans_lt
    change μ.toOuterMeasure Set.univ < ⊤
    rw [hu]
    exact ENNReal.one_lt_top
  exact ENNReal.toReal_mono hb (μ.toOuterMeasure.mono h)

theorem fixedPositions_card_eq_zero_of_card_le_one (J : Finset (Fin 4))
    (hJ : J.card ≤ 1) : (fixedPositions J).card = 0 := by
  have h : ∀ K : Finset (Fin 4), K.card ≤ 1 → (fixedPositions K).card = 0 := by
    decide
  exact h J hJ

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem conditional_prescribed_line_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hD : (exposedTupleIndices T D).card ≤ 1)
    (g : Direction F) (hg : ∀ i, T.generator i ≠ g) (c : F) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure
        {M | ∀ i, OnLine (tuplePoint M T i) (g,c)}).toReal ≤
      (Fintype.card F : ℝ)⁻¹^4 := by
  simpa only [fixedPositions_card_eq_zero_of_card_le_one _ hD, Nat.sub_zero] using
    canonical_conditional_alignment_probability_le T hT g hg c D a

theorem conditional_tuple_hits_line_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hD : (exposedTupleIndices T D).card ≤ 1)
    (g : Direction F) (hg : ∀ i, T.generator i ≠ g) (L : Line F)
    (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure
        {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
          ∃ i, OnLine (tuplePoint M T i) L}).toReal ≤
      4 * (Fintype.card F : ℝ)⁻¹^4 := by
  by_cases htrans : g ≠ L.1
  · exact canonical_conditional_one_exposed_hit_probability_le
      T hT D a g hg hD L htrans havoid
  · have hdir : g = L.1 := by simpa only [ne_eq, not_not] using htrans
    have hb := conditional_prescribed_line_probability_le T hT D a hD g hg L.2
    have hm : (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
        (canonical_exposure_supported D a)).toOuterMeasure
        {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
          ∃ i, OnLine (tuplePoint M T i) L}).toReal ≤
        (Fintype.card F : ℝ)⁻¹^4 := by
      apply le_trans (pmf_probability_mono _ (B :=
        {M | ∀ j, OnLine (tuplePoint M T j) (g,L.2)}) ?_) hb
      rintro M ⟨⟨c,hc⟩,i,hi⟩ j
      have heq : (g,c) = L :=
        eq_of_onLine_same_direction (tuplePoint M T i) (g,c) L hdir (hc i) hi
      have hcL : c = L.2 := congrArg Prod.snd heq
      simpa only [hcL] using hc j
    have hn : 0 ≤ (Fintype.card F : ℝ)⁻¹^4 := by positivity
    linarith

end
end Balanced.CandidatePartialPointIncidence

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateGlobalLineMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateGlobalLine

noncomputable section
open scoped Classical BigOperators
open CandidateExposure PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem conditionalProbability_mono (D : Finset (Direction F)) (a : MergedPairs F)
    {E H : Set (MergedPairs F)} (h : E ⊆ H) :
    conditionalProbability D a E ≤ conditionalProbability D a H := by
  unfold conditionalProbability
  apply ENNReal.toReal_mono _ ((exposedLaw D a).toOuterMeasure.mono h)
  change (exposedLaw D a).toOuterMeasure H ≠ ⊤
  rw [PMF.toOuterMeasure_apply]
  exact (exposedLaw D a).tsum_coe_indicator_ne_top H

theorem lineSuccessEvent_probability_le (T : FourTuple F) (g : Direction F)
    (L : Line F) (D : Finset (Direction F)) (a : MergedPairs F) :
    conditionalProbability D a (lineSuccessEvent T g L) ≤
      conditionalProbability D a (successfulInDirection T g) :=
  conditionalProbability_mono D a (fun _ h => h.1)

theorem fresh_lineSuccessEvent_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F) (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (hfresh : (exposedTupleIndices T D).card = 0) :
    conditionalProbability D a (lineSuccessEvent T g L) ≤
      4 * (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  have hf : ∀ i, T.generator i ∉ D := by
    intro i hi
    have hempty := Finset.card_eq_zero.mp hfresh
    have hm : i ∈ exposedTupleIndices T D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    simp [hempty] at hm
  apply le_trans (conditionalProbability_mono D a (H :=
    {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
      ∃ i, OnLine (tuplePoint M T i) L}) (fun _ h => ⟨h.1.1, h.2⟩))
  exact CandidateFreshIncidence.conditional_tuple_hits_line_probability_le
    T hT D a hf g L

theorem one_old_lineSuccessEvent_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F)
    (hg : ∀ i, T.generator i ≠ g) (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (hone : (exposedTupleIndices T D).card = 1)
    (ha : L ∉ constituentLines a) :
    conditionalProbability D a (lineSuccessEvent T g L) ≤
      4 * (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  apply le_trans (conditionalProbability_mono D a (H :=
    {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
      ∃ i, OnLine (tuplePoint M T i) L}) (fun _ h => ⟨h.1.1, h.2⟩))
  exact CandidatePartialPointIncidence.conditional_tuple_hits_line_probability_le
    T hT D a hone.le g hg L (CandidateLineGate.exposed_constituents_avoid D a L ha)

theorem lineSuccess_sum_zero_one_le (g : Direction F) (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m j : ℕ)
    (hD : D.card ≤ m) (hj : j = 0 ∨ j = 1) (ha : L ∉ constituentLines a) :
    (∑ T ∈ tuplesWithExposure g D j,
      conditionalProbability D a (lineSuccessEvent T g L)) ≤
      (16384 * (m + 1) ^ 4 : ℝ) * (Fintype.card F : ℝ)⁻¹ ^ j := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ ∑ _T ∈ tuplesWithExposure g D j, 4 * (Fintype.card F : ℝ)⁻¹ ^ 4 := by
      apply Finset.sum_le_sum
      intro T hT
      obtain ⟨helig, hexp⟩ := Finset.mem_filter.mp hT
      obtain ⟨hinj, htarget⟩ := (Finset.mem_filter.mp helig).2
      rcases hj with rfl | rfl
      · exact fresh_lineSuccessEvent_probability_le T hinj g L D a hexp
      · exact one_old_lineSuccessEvent_probability_le T hinj g htarget L D a hexp ha
    _ = ((tuplesWithExposure g D j).card : ℝ) *
        (4 * (Fintype.card F : ℝ)⁻¹ ^ 4) := by simp
    _ ≤ ((4096 * (m + 1) ^ 4 : ℝ) * (Fintype.card F : ℝ) ^ (4-j)) *
        (4 * (Fintype.card F : ℝ)⁻¹ ^ 4) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_tuplesWithExposure_le g D m j hD (by omega)
    _ = _ := by
      rcases hj with rfl | rfl <;> norm_num <;> field_simp <;> ring

theorem sum_targets_lineSuccess_zero_one_le (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m j : ℕ)
    (hD : D.card ≤ m) (hj : j = 0 ∨ j = 1) (ha : L ∉ constituentLines a) :
    (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j,
      conditionalProbability D a (lineSuccessEvent T g L)) ≤
      (32768 * (m + 1) ^ 4 : ℝ) *
        (if j = 0 then (Fintype.card F : ℝ) else 1) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hd : (Fintype.card (Direction F) : ℝ) ≤ 2 * Fintype.card F := by
    have hn : 0 < Fintype.card F := Fintype.card_pos
    simp only [Direction, Fintype.card_option, Nat.cast_add, Nat.cast_one]
    have hp : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast hn
    linarith
  calc
    _ ≤ ∑ _g : Direction F,
        (16384 * (m + 1) ^ 4 : ℝ) * (Fintype.card F : ℝ)⁻¹ ^ j :=
      Finset.sum_le_sum (fun g _ => lineSuccess_sum_zero_one_le g L D a m j hD hj ha)
    _ = (Fintype.card (Direction F) : ℝ) *
        ((16384 * (m + 1) ^ 4 : ℝ) * (Fintype.card F : ℝ)⁻¹ ^ j) := by simp
    _ ≤ (2 * (Fintype.card F : ℝ)) *
        ((16384 * (m + 1) ^ 4 : ℝ) * (Fintype.card F : ℝ)⁻¹ ^ j) := by
      exact mul_le_mul_of_nonneg_right hd (by positivity)
    _ = _ := by
      rcases hj with rfl | rfl <;> norm_num <;> field_simp <;> ring

end
end Balanced.CandidateGlobalLine

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FullyExposedTargets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.TupleAlignment

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
theorem successfulPositions_unique_line (p : Fin 4 → Point F)
    (hp : Function.Injective p) (l m : Line F)
    (hl : ∀ i, OnLine (p i) l) (hm : ∀ i, OnLine (p i) m) : l = m := by
  exact eq_of_two_common_points (p 0) (p 1)
    (fun h => (by decide : (0 : Fin 4) ≠ 1) (hp h))
    l m (hl 0) (hl 1) (hm 0) (hm 1)

omit [Fintype F] [DecidableEq F] in
theorem successfulPositions_unique_target (p : Fin 4 → Point F)
    {g h : Direction F} (hg : SuccessfulPositions p g)
    (hh : SuccessfulPositions p h) : g = h := by
  obtain ⟨⟨c, hc⟩, hp⟩ := hg
  obtain ⟨⟨d, hd⟩, _⟩ := hh
  exact congrArg Prod.fst (successfulPositions_unique_line p hp (g, c) (h, d) hc hd)

omit [DecidableEq F] in
theorem successfulPositions_target_card_le_one (p : Fin 4 → Point F) :
    (Finset.univ.filter (SuccessfulPositions p)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro g hg h hh
  exact successfulPositions_unique_target p (Finset.mem_filter.mp hg).2
    (Finset.mem_filter.mp hh).2

omit [Fintype F] [DecidableEq F] in
theorem tuplePoint_eq_of_generator_agreement (T : FourTuple F)
    {M a : MergedPairs F} (h : ∀ i, M (T.generator i) = a (T.generator i)) :
    tuplePoint M T = tuplePoint a T := by
  funext i
  simp only [tuplePoint, constituent, h i, h (i + 1)]

omit [Fintype F] [DecidableEq F] in
theorem tuplePoint_eq_of_fully_exposed (T : FourTuple F)
    (D : Finset (Direction F)) (a M : MergedPairs F)
    (hT : ∀ i, T.generator i ∈ D)
    (hM : ∀ d, d ∈ D → M d = a d) : tuplePoint M T = tuplePoint a T :=
  tuplePoint_eq_of_generator_agreement T (fun i => hM _ (hT i))

theorem fully_exposed_tuplePoint_law (T : FourTuple F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (hT : ∀ i, T.generator i ∈ D) :
    ((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (PartialAlignment.canonical_exposure_supported D a)).map
        (fun M => tuplePoint M T) = PMF.pure (tuplePoint a T) := by
  simp only [PartialAlignment.offsetLaw_eq_uniform]
  rw [ConditionalRestriction.uniform_fixed_filter, PMF.map_comp]
  have hf : (fun M : ConditionalRestriction.FixedArray (fun d => d ∈ D) a =>
      tuplePoint M.1 T) = Function.const _ (tuplePoint a T) := by
    funext M
    exact tuplePoint_eq_of_fully_exposed T D a M.1 hT M.2
  simp only [Function.comp_def]
  rw [hf, PMF.map_const]

theorem fully_exposed_success_probability (T : FourTuple F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (hT : ∀ i, T.generator i ∈ D) (g : Direction F) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (PartialAlignment.canonical_exposure_supported D a)).toOuterMeasure
        {M | SuccessfulPositions (tuplePoint M T) g}).toReal =
      if SuccessfulPositions (tuplePoint a T) g then 1 else 0 := by
  have h := congrArg (fun law : PMF (Fin 4 → Point F) =>
    (law.toOuterMeasure {p | SuccessfulPositions p g}).toReal)
      (fully_exposed_tuplePoint_law T D a hT)
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_pure_apply] at h
  simpa only [Set.mem_ofPred_eq, Set.preimage_ofPred_eq, apply_ite,
    ENNReal.toReal_one, ENNReal.toReal_zero] using h

theorem sum_fully_exposed_success_probability_le_one (T : FourTuple F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (hT : ∀ i, T.generator i ∈ D) :
    (∑ g : Direction F,
      (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
        (PartialAlignment.canonical_exposure_supported D a)).toOuterMeasure
          {M | SuccessfulPositions (tuplePoint M T) g}).toReal) ≤ 1 := by
  simp_rw [fully_exposed_success_probability T D a hT]
  have hcard := successfulPositions_target_card_le_one (tuplePoint a T)
  have hsum : (∑ g : Direction F,
      if SuccessfulPositions (tuplePoint a T) g then (1 : ℝ) else 0) =
      ((Finset.univ.filter (SuccessfulPositions (tuplePoint a T))).card : ℝ) := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum, apply_ite, Nat.cast_one, Nat.cast_zero]
  rw [hsum]
  exact_mod_cast hcard

omit [Field F] in
theorem generators_exposed_of_code_oldCount_four (D : Finset (Direction F))
    (c : (Fin 4 → Direction F) × (Fin 4 → Bool))
    (hc : c ∈ tupleCodesWithOldCount D 4) : ∀ i, c.1 i ∈ D := by
  have hcard := (Finset.mem_filter.mp (Finset.mem_product.mp hc).1).2
  have hfull : (Finset.univ.filter (fun i : Fin 4 => c.1 i ∈ D)) = Finset.univ := by
    apply (Finset.card_eq_iff_eq_univ _).mp
    simpa only [Fintype.card_fin] using hcard
  intro i
  have hi : i ∈ Finset.univ.filter (fun i : Fin 4 => c.1 i ∈ D) := by
    rw [hfull]
    exact Finset.mem_univ _
  exact (Finset.mem_filter.mp hi).2

theorem sum_fully_exposed_code_success_probability_le
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (∑ c ∈ tupleCodesWithOldCount D 4, ∑ g : Direction F,
      (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
        (PartialAlignment.canonical_exposure_supported D a)).toOuterMeasure
          {M | SuccessfulPositions (tuplePoint M ⟨c.1, c.2⟩) g}).toReal) ≤
      16 * (D.card : ℝ) ^ 4 := by
  calc
    _ ≤ ∑ _c ∈ tupleCodesWithOldCount D 4, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro c hc
      exact sum_fully_exposed_success_probability_le_one ⟨c.1, c.2⟩ D a
        (generators_exposed_of_code_oldCount_four D c hc)
    _ = ((tupleCodesWithOldCount D 4).card : ℝ) := by simp
    _ ≤ 16 * (D.card : ℝ) ^ 4 := by
      have hcount : (tupleCodesWithOldCount D 4).card ≤ 16 * D.card ^ 4 := by
        simpa using card_tupleCodesWithOldCount_le D 4
      exact_mod_cast hcount

end
end Balanced.TupleAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateIncidenceMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateExposure

noncomputable section
open scoped Classical BigOperators
open PartialAlignment TupleAlignment MeasureTheory

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem success_sum_two_three_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m j : ℕ) (hD : D.card ≤ m) (hj : j = 2 ∨ j = 3) :
    (∑ T ∈ tuplesWithExposure g D j,
      conditionalProbability D a (successfulInDirection T g)) ≤
        (4096 * (m + 1) ^ 4 : ℝ) / Fintype.card F := by
  have hj4 : j ≤ 4 := by omega
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ ∑ _T ∈ tuplesWithExposure g D j,
        (Fintype.card F : ℝ)⁻¹ ^ alignmentExponent j := by
      apply Finset.sum_le_sum
      intro T hT
      obtain ⟨hgood, hjT⟩ := Finset.mem_filter.mp hT
      obtain ⟨hinj, hg⟩ := (Finset.mem_filter.mp hgood).2
      simpa only [hjT] using successful_probability_le T hinj g hg D a
    _ = ((tuplesWithExposure g D j).card : ℝ) *
        (Fintype.card F : ℝ)⁻¹ ^ alignmentExponent j := by simp
    _ ≤ ((4096 * (m + 1) ^ 4 : ℝ) * (Fintype.card F : ℝ) ^ (4-j)) *
        (Fintype.card F : ℝ)⁻¹ ^ alignmentExponent j := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_tuplesWithExposure_le g D m j hD hj4
    _ = _ := by rcases hj with rfl | rfl <;> norm_num [alignmentExponent] <;> field_simp

theorem sum_targets_success_two_three_le (D : Finset (Direction F))
    (a : MergedPairs F) (m j : ℕ) (hD : D.card ≤ m) (hj : j = 2 ∨ j = 3) :
    (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j,
      conditionalProbability D a (successfulInDirection T g)) ≤
        (8192 * (m + 1) ^ 4 : ℝ) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hdir : (Fintype.card (Direction F) : ℝ) ≤ 2 * Fintype.card F := by
    have hn : 0 < Fintype.card F := Fintype.card_pos
    have hd : Fintype.card (Direction F) ≤ 2 * Fintype.card F := by
      simp only [Direction, Fintype.card_option]
      omega
    exact_mod_cast hd
  calc
    _ ≤ ∑ _g : Direction F, (4096 * (m + 1) ^ 4 : ℝ) / Fintype.card F :=
      Finset.sum_le_sum (fun g _ => success_sum_two_three_le g D a m j hD hj)
    _ = (Fintype.card (Direction F) : ℝ) *
        ((4096 * (m + 1) ^ 4 : ℝ) / Fintype.card F) := by simp
    _ ≤ (2 * Fintype.card F : ℝ) *
        ((4096 * (m + 1) ^ 4 : ℝ) / Fintype.card F) := by gcongr
    _ = _ := by field_simp; ring

theorem sum_targets_success_four_le (D : Finset (Direction F)) (a : MergedPairs F) :
    (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D 4,
      conditionalProbability D a (successfulInDirection T g)) ≤
        16 * (D.card : ℝ)^4 := by
  let code : FourTuple F → (Fin 4 → Direction F) × (Fin 4 → Bool) :=
    fun T => (T.generator,T.side)
  have hinj : Function.Injective code := by
    intro T U h
    cases T
    cases U
    cases h
    rfl
  have htarget (g : Direction F) :
      (∑ T ∈ tuplesWithExposure g D 4,
        conditionalProbability D a (successfulInDirection T g)) ≤
      ∑ c ∈ tupleCodesWithOldCount D 4,
        conditionalProbability D a (successfulInDirection ⟨c.1,c.2⟩ g) := by
    have hsub : (tuplesWithExposure g D 4).image code ⊆ tupleCodesWithOldCount D 4 := by
      intro c hc
      obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hc
      have hj := (Finset.mem_filter.mp hT).2
      simpa [code, tupleCodesWithOldCount, generatorLabelsWithOldCount,
        exposedTupleIndices] using hj
    calc
      _ = ∑ c ∈ (tuplesWithExposure g D 4).image code,
          conditionalProbability D a (successfulInDirection ⟨c.1,c.2⟩ g) := by
        rw [Finset.sum_image (fun T _ U _ h => hinj h)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => ENNReal.toReal_nonneg)
  calc
    _ ≤ ∑ g : Direction F, ∑ c ∈ tupleCodesWithOldCount D 4,
        conditionalProbability D a (successfulInDirection ⟨c.1,c.2⟩ g) :=
      Finset.sum_le_sum (fun g _ => htarget g)
    _ = ∑ c ∈ tupleCodesWithOldCount D 4, ∑ g : Direction F,
        conditionalProbability D a (successfulInDirection ⟨c.1,c.2⟩ g) := Finset.sum_comm
    _ ≤ _ := sum_fully_exposed_code_success_probability_le D a

end
end Balanced.CandidateExposure

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

theorem rootPatternModel_support_card (g : Direction F) (a : RootPrescription g) :
    ((rootPatternModel g).support a).card = 4 := by
  exact (Finset.card_image_of_injective _ a.injective).trans (by simp)

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
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateIncidenceModel
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidence

noncomputable section
open scoped Classical BigOperators
open MeasureTheory TupleAlignment CandidateExposure

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

theorem allModel_support_card (R : Test F) (a : (allModel R).Label) :
    ((allModel R).support a).card = 4 := rootPatternModel_support_card a.1 a.2

theorem model_count (R : Test F) (g : Direction F) (M : MergedPairs F) :
    (model R g).count M = (tupleCount R g M : ℝ) := by
  have hc : (Finset.univ.filter (fun a : RootPrescription g => M ∈ event R g a)).card =
      tupleCount R g M := by
    apply Finset.card_bij (fun a _ => a.tuple)
    · intro a ha
      obtain ⟨_, hs⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨((eligibleTupleEquivRootPrescription g).symm a).2,hs⟩
    · intro a _ b _ hab
      apply (eligibleTupleEquivRootPrescription g).symm.injective
      exact Subtype.ext hab
    · intro T hT
      obtain ⟨hg,hs⟩ := Finset.mem_filter.mp hT
      let a := eligibleTupleEquivRootPrescription g ⟨T,hg⟩
      have ha : a.tuple = T := equivRootPrescription_tuple g ⟨T,hg⟩
      refine ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,ha⟩
      change M ∈ successfulInDirection a.tuple g ∧ R a.tuple g (tuplePoint M a.tuple)
      simpa only [ha] using hs
  rw [← hc]
  simp only [PatternModel.count, PatternModel.indicator, model,
    Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, Finset.sum_filter, Set.indicator_apply]

theorem allModel_count (R : Test F) (M : MergedPairs F) :
    (allModel R).count M = ∑ g : Direction F, (tupleCount R g M : ℝ) := by
  change (∑ a : Σ g : Direction F, RootPrescription g,
    (event R a.1 a.2).indicator (fun _ => (1 : ℝ)) M) = _
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl (fun g _ => model_count R g M)

attribute [local instance] OAI.Balanced.CandidateIncidence.incidenceModelMeasurableSpace
theorem allModel_measure (R : Test F) :
    (allModel R).measure = (offsetLaw F).toMeasure := rootPatternModel_measure (none : Direction F)

theorem allModel_fixedExpectation (R : Test F)
    (D : Finset (Direction F)) (a : MergedPairs F) (f : MergedPairs F → ℝ) :
    (allModel R).fixedExpectation D a f = ∫ M, f M ∂(exposedLaw D a).toMeasure :=
  rootPatternModel_fixedExpectation_exposed (none : Direction F) D a f

theorem allModel_fixed_count (R : Test F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (allModel R).fixedExpectation D a (allModel R).count =
      ∑ g : Direction F, ∑ T ∈ eligibleTuples g, conditionalProbability D a
        {M | M ∈ successfulInDirection T g ∧ R T g (tuplePoint M T)} := by
  rw [allModel_fixedExpectation]
  simp_rw [allModel_count]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro g _
  simpa only [tupleCount, conditionalProbability, Set.mem_ofPred_eq] using
    integral_eventCount_eq_sum (exposedLaw D a) (eligibleTuples g)
      (fun T => {M | M ∈ successfulInDirection T g ∧ R T g (tuplePoint M T)})

end
end Balanced.CandidateIncidence

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateGlobalLineTotals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateGlobalLine

noncomputable section
open scoped Classical BigOperators
open CandidateExposure PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem sum_targets_lineSuccess_stratum_le (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m j : ℕ)
    (hD : D.card ≤ m) (hj : j ≤ 4) (ha : L ∉ constituentLines a) :
    (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j,
      conditionalProbability D a (lineSuccessEvent T g L)) ≤
      (32768 * (m + 1) ^ 4 : ℝ) *
        (if j = 0 then (Fintype.card F : ℝ) else 1) := by
  by_cases hlow : j = 0 ∨ j = 1
  · exact sum_targets_lineSuccess_zero_one_le L D a m j hD hlow ha
  have hdrop : (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j,
      conditionalProbability D a (lineSuccessEvent T g L)) ≤
      ∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j,
        conditionalProbability D a (successfulInDirection T g) := by
    exact Finset.sum_le_sum (fun g _ => Finset.sum_le_sum
      (fun T _ => lineSuccessEvent_probability_le T g L D a))
  by_cases hmid : j = 2 ∨ j = 3
  · have h := hdrop.trans (sum_targets_success_two_three_le D a m j hD hmid)
    have hj0 : j ≠ 0 := by omega
    rw [ite_eq_right hj0, mul_one]
    exact h.trans (by gcongr; norm_num)
  · have hj4 : j = 4 := by omega
    subst j
    have h := hdrop.trans (sum_targets_success_four_le D a)
    norm_num only [show ¬ (4 : ℕ) = 0 by decide, ite_false, mul_one]
    apply h.trans
    have hm : (D.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast (by omega : D.card ≤ m+1)
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ D.card) hm 4
    nlinarith [show (0 : ℝ) ≤ (m+1)^4 by positivity]

theorem sum_targets_lineSuccess_le (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ)
    (hD : D.card ≤ m) (ha : L ∉ constituentLines a) :
    (∑ g : Direction F, ∑ T ∈ eligibleTuples g,
      conditionalProbability D a (lineSuccessEvent T g L)) ≤
      (163840 * (m + 1) ^ 4 : ℝ) * Fintype.card F := by
  have hpartition (g : Direction F) :
      (∑ T ∈ eligibleTuples g, conditionalProbability D a (lineSuccessEvent T g L)) =
      ∑ j ∈ Finset.range 5, ∑ T ∈ tuplesWithExposure g D j,
        conditionalProbability D a (lineSuccessEvent T g L) := by
    symm
    exact Finset.sum_fiberwise_of_maps_to
      (s := eligibleTuples g) (t := Finset.range 5)
      (g := fun T => (exposedTupleIndices T D).card)
      (fun T _ => Finset.mem_range.mpr (by
        have h := Finset.card_le_univ (exposedTupleIndices T D)
        simp only [Fintype.card_fin] at h
        omega)) _
  simp_rw [hpartition]
  rw [Finset.sum_comm]
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  calc
    _ ≤ ∑ _j ∈ Finset.range 5,
        (32768 * (m+1)^4 : ℝ) * Fintype.card F := by
      apply Finset.sum_le_sum
      intro j hj
      apply (sum_targets_lineSuccess_stratum_le L D a m j hD
        (by have := Finset.mem_range.mp hj; omega) ha).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      split_ifs
      · exact le_rfl
      · exact hq
    _ = _ := by norm_num; ring

theorem sum_targets_overlapping_lineSuccess_le (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ)
    (hD : D.card ≤ m) (ha : L ∉ constituentLines a) :
    (∑ g : Direction F,
      ∑ T ∈ (eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card),
        conditionalProbability D a (lineSuccessEvent T g L)) ≤
      (163840 * (m + 1) ^ 4 : ℝ) := by
  have hpartition (g : Direction F) :
      (∑ T ∈ (eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card),
        conditionalProbability D a (lineSuccessEvent T g L)) =
      ∑ j ∈ Finset.Icc 1 4, ∑ T ∈ tuplesWithExposure g D j,
        conditionalProbability D a (lineSuccessEvent T g L) := by
    have h := Finset.sum_fiberwise_eq_sum_filter (eligibleTuples g)
      (Finset.Icc 1 4) (fun T => (exposedTupleIndices T D).card)
      (fun T => conditionalProbability D a (lineSuccessEvent T g L))
    have heq : (eligibleTuples g).filter
        (fun T => (exposedTupleIndices T D).card ∈ Finset.Icc 1 4) =
        (eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card) := by
      apply Finset.filter_congr
      intro T _
      have hc := Finset.card_le_univ (exposedTupleIndices T D)
      simp only [Fintype.card_fin] at hc
      simp only [Finset.mem_Icc]
      omega
    rw [heq] at h
    exact h.symm
  simp_rw [hpartition]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _j ∈ Finset.Icc 1 4, (32768 * (m+1)^4 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hj1, hj4⟩ := Finset.mem_Icc.mp hj
      simpa only [ite_eq_right (by omega : j ≠ 0), mul_one] using
        sum_targets_lineSuccess_stratum_le L D a m j hD hj4 ha
    _ ≤ _ := by norm_num; nlinarith [show (0 : ℝ) ≤ (m+1)^4 by positivity]

end
end Balanced.CandidateGlobalLine

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

end
end Balanced.PatternModel

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternGate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PatternModel

noncomputable section
open scoped Classical BigOperators
open MeasureTheory

variable (P : PatternModel) (A : Finset P.Color) (E : Set P.Sample)
    (hE : MeasurableSet E)
    (hdep : ∀ x y, (∀ c ∈ A, x c = y c) → (x ∈ E ↔ y ∈ E))

theorem gated_support_card_le (r : ℕ) (hr : ∀ a, (P.support a).card ≤ r)
    (a : P.Label) : ((P.gated A E hE hdep).support a).card ≤ r + A.card := by
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right (hr a) _)

theorem gated_indicator (a : P.Label) (ω : P.Sample) :
    (P.gated A E hE hdep).indicator a ω = if ω ∈ E then P.indicator a ω else 0 := by
  by_cases h : ω ∈ E <;> simp [indicator, gated, Set.indicator_apply, h]

theorem gated_count (ω : P.Sample) :
    (P.gated A E hE hdep).count ω = if ω ∈ E then P.count ω else 0 := by
  unfold count
  simp_rw [gated_indicator]
  by_cases h : ω ∈ E <;> simp [h]

theorem gated_overlapCount (K₀ K : Finset P.Color) (hA : A ⊆ K₀) (ω : P.Sample) :
    (P.gated A E hE hdep).overlapCount K₀ K ω =
      if ω ∈ E then P.overlapCount K₀ K ω else 0 := by
  have hsupport (a : P.Label) :
      (P.support a ∪ A) \ K₀ = P.support a \ K₀ := by
    rw [Finset.union_sdiff_distrib, Finset.sdiff_eq_empty_iff_subset.mpr hA,
      Finset.union_empty]
  unfold overlapCount
  change (∑ a, if Disjoint ((P.support a ∪ A) \ K₀) K then 0 else
      (P.gated A E hE hdep).indicator a ω) = _
  simp_rw [hsupport, gated_indicator]
  by_cases h : ω ∈ E <;> simp [h]

include hdep

theorem gate_fixed_iff (D : Finset P.Color) (hAD : A ⊆ D) (x ω : P.Sample) :
    P.fixCoordinates D x ω ∈ E ↔ x ∈ E := by
  apply hdep
  intro c hc
  simp [fixCoordinates, hAD hc]

theorem fixedExpectation_gated_function (D : Finset P.Color) (hAD : A ⊆ D)
    (x : P.Sample) (f : P.Sample → ℝ) :
    P.fixedExpectation D x (fun ω => if ω ∈ E then f ω else 0) =
      if x ∈ E then P.fixedExpectation D x f else 0 := by
  unfold fixedExpectation
  by_cases hx : x ∈ E
  · simp only [ite_eq_left hx]
    apply integral_congr_ae
    filter_upwards [] with ω
    simp only [ite_eq_left ((gate_fixed_iff P A E hdep D hAD x ω).mpr hx)]
  · simp only [ite_eq_right hx]
    have hz : (fun ω => if P.fixCoordinates D x ω ∈ E then
        f (P.fixCoordinates D x ω) else (0 : ℝ)) = fun _ => 0 := by
      funext ω
      exact ite_eq_right (fun h => hx ((gate_fixed_iff P A E hdep D hAD x ω).mp h))
    rw [hz, integral_zero]

theorem gated_fixed_count (D : Finset P.Color) (hAD : A ⊆ D) (x : P.Sample) :
    (P.gated A E hE hdep).fixedExpectation D x (P.gated A E hE hdep).count =
      if x ∈ E then P.fixedExpectation D x P.count else 0 := by
  rw [gated_fixedExpectation]
  have hc : (P.gated A E hE hdep).count =
      fun ω => if ω ∈ E then P.count ω else 0 :=
    funext (gated_count P A E hE hdep)
  rw [hc]
  exact fixedExpectation_gated_function P A E hdep D hAD x P.count

theorem gated_fixed_overlapCount (K₀ K D : Finset P.Color)
    (hA₀ : A ⊆ K₀) (hAD : A ⊆ D) (x : P.Sample) :
    (P.gated A E hE hdep).fixedExpectation D x
      ((P.gated A E hE hdep).overlapCount K₀ K) =
      if x ∈ E then P.fixedExpectation D x (P.overlapCount K₀ K) else 0 := by
  rw [gated_fixedExpectation]
  have hc : (P.gated A E hE hdep).overlapCount K₀ K =
      fun ω => if ω ∈ E then P.overlapCount K₀ K ω else 0 :=
    funext (gated_overlapCount P A E hE hdep K₀ K hA₀)
  rw [hc]
  exact fixedExpectation_gated_function P A E hdep D hAD x (P.overlapCount K₀ K)

theorem gated_centered_moment_le (K₀ : Finset P.Color) (hA₀ : A ⊆ K₀)
    (x : P.Sample) (s r : ℕ) (q C : ℝ) (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hsupport : ∀ a, (P.support a).card ≤ r)
    (htotal : ∀ K : Finset P.Color, K.card ≤ (2 * s) * (r + A.card) →
      ∀ y, y ∈ E → P.fixedExpectation (K₀ ∪ K) y P.count ≤ C * q)
    (hoverlap : ∀ K : Finset P.Color, K.card ≤ (2 * s) * (r + A.card) →
      ∀ y, y ∈ E → P.fixedExpectation (K₀ ∪ K) y (P.overlapCount K₀ K) ≤ C) :
    (P.gated A E hE hdep).fixedExpectation K₀ x
      (fun ω => |(P.gated A E hE hdep).count ω -
        (P.gated A E hE hdep).fixedExpectation K₀ x
          (P.gated A E hE hdep).count| ^ (2 * s)) ≤
      ((2 * s).factorial : ℝ) * 2 ^ (2 * s) * (2 * C) ^ (2 * s) * q ^ s := by
  apply (P.gated A E hE hdep).centered_moment_le_of_exposureBounds
    K₀ x s (r + A.card) q C hq hC
    (fun a => gated_support_card_le P A E hE hdep r hsupport a)
  · intro K hK y
    rw [gated_fixed_count P A E hE hdep (K₀ ∪ K)
      (hA₀.trans Finset.subset_union_left) y]
    split_ifs with hy
    · exact htotal K hK y hy
    · exact mul_nonneg hC (by linarith)
  · intro K hK y
    rw [gated_fixed_overlapCount P A E hE hdep K₀ K (K₀ ∪ K) hA₀
      (hA₀.trans Finset.subset_union_left) y]
    split_ifs with hy
    · exact hoverlap K hK y hy
    · exact hC

end
end Balanced.PatternModel

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateGlobalLineModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateGlobalLine

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateExposure CandidateIncidence PartialAlignment

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

theorem allExposed_overlapCount_eq (L : Line F) (D : Finset (Direction F))
    (M : MergedPairs F) :
    (lineModel L).overlapCount ∅ D M = (allModel (oldLineTest L D)).count M := by
  unfold PatternModel.overlapCount PatternModel.count
  apply Finset.sum_congr rfl
  intro a _
  change (if Disjoint (generatorSet a.2.tuple \ ∅) D then 0 else
    (lineModel L).indicator a M) = (allModel (oldLineTest L D)).indicator a M
  simp only [Finset.sdiff_empty]
  by_cases h : Disjoint (generatorSet a.2.tuple) D
  · have hn : ¬ 0 < (exposedTupleIndices a.2.tuple D).card := by
      intro hp
      exact ((not_disjoint_generatorSet_iff a.2.tuple D).mpr hp) h
    simp [h, PatternModel.indicator, allModel, CandidateIncidence.event,
      oldLineTest, hn]
  · have hp := (not_disjoint_generatorSet_iff a.2.tuple D).mp h
    simp [h, PatternModel.indicator, allModel, CandidateIncidence.event,
      oldLineTest, lineHitTest, hp]

theorem lineModel_fixed_count_le (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ)
    (hD : D.card ≤ m) (ha : L ∉ constituentLines a) :
    (lineModel L).fixedExpectation D a (lineModel L).count ≤
      (163840 * (m+1)^4 : ℝ) * Fintype.card F := by
  rw [allModel_fixed_count]
  exact sum_targets_lineSuccess_le L D a m hD ha

theorem lineModel_fixed_allExposed (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (lineModel L).fixedExpectation D a ((lineModel L).overlapCount ∅ D) =
      ∑ g : Direction F,
      ∑ T ∈ (eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card),
        conditionalProbability D a (lineSuccessEvent T g L) := by
  have heq : (lineModel L).overlapCount ∅ D = (allModel (oldLineTest L D)).count :=
    funext (allExposed_overlapCount_eq L D)
  rw [heq]
  change (allModel (oldLineTest L D)).fixedExpectation D a
    (allModel (oldLineTest L D)).count = _
  rw [allModel_fixed_count]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  by_cases h : 0 < (exposedTupleIndices T D).card
  · simp only [oldLineTest, h, true_and, ite_eq_left, lineSuccessEvent]
  · simp [oldLineTest, h, conditionalProbability]

theorem lineModel_fixed_allExposed_le (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ)
    (hD : D.card ≤ m) (ha : L ∉ constituentLines a) :
    (lineModel L).fixedExpectation D a ((lineModel L).overlapCount ∅ D) ≤
      (163840 * (m+1)^4 : ℝ) := by
  rw [lineModel_fixed_allExposed]
  exact sum_targets_overlapping_lineSuccess_le L D a m hD ha

attribute [local instance] OAI.Balanced.CandidateGlobalLine.globalLineModelMeasurableSpace
theorem lineModel_fixed_overlap_le (L : Line F)
    (K₀ K : Finset (Direction F)) (a : MergedPairs F) (m : ℕ)
    (hD : (K₀ ∪ K).card ≤ m) (ha : L ∉ constituentLines a) :
    (lineModel L).fixedExpectation (K₀ ∪ K) a ((lineModel L).overlapCount K₀ K) ≤
      (163840 * (m+1)^4 : ℝ) := by
  apply le_trans _ (lineModel_fixed_allExposed_le L (K₀ ∪ K) a m hD ha)
  apply integral_mono
    ((lineModel L).integrable_fixed_overlapCount (K₀ ∪ K) a K₀ K)
    ((lineModel L).integrable_fixed_overlapCount (K₀ ∪ K) a ∅ (K₀ ∪ K))
  intro M
  exact (lineModel L).overlapCount_le_allExposed K₀ K _

theorem gatedLineModel_count (L : Line F) (M : MergedPairs F) :
    (gatedLineModel L).count M =
      if L ∉ constituentLines M then ∑ g : Direction F,
        (tupleCount (lineHitTest L) g M : ℝ) else 0 := by
  rw [PatternModel.gated_count, allModel_count]
  by_cases h : L ∉ constituentLines M
  · simp only [Set.mem_ofPred_eq, ite_eq_left h]
  · simp only [Set.mem_ofPred_eq, ite_eq_right h]

theorem gatedLineModel_measure (L : Line F) :
    (gatedLineModel L).measure = (offsetLaw F).toMeasure := allModel_measure (lineHitTest L)

theorem gatedLineModel_fixedExpectation (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (f : MergedPairs F → ℝ) :
    (gatedLineModel L).fixedExpectation D a f =
      ∫ M, f M ∂(exposedLaw D a).toMeasure := allModel_fixedExpectation (lineHitTest L) D a f

theorem gatedLineModel_initial_mean_le (L : Line F) (a : MergedPairs F) :
    (gatedLineModel L).fixedExpectation {L.1} a (gatedLineModel L).count ≤
      2621440 * (Fintype.card F : ℝ) := by
  rw [PatternModel.gated_fixed_count (lineModel L) {L.1}
    {M | L ∉ constituentLines M} (Set.toFinite _).measurableSet
    (lineGate_depends L) {L.1} (Finset.Subset.refl _) a]
  split_ifs with ha
  · simpa only [Nat.cast_one, show (163840 * (1+1)^4 : ℝ) = 2621440 by norm_num] using
      lineModel_fixed_count_le L {L.1} a 1 (by simp) ha
  · positivity

theorem gatedLineModel_centered_moment_le (L : Line F) (a : MergedPairs F) (s : ℕ) :
    (gatedLineModel L).fixedExpectation {L.1} a
      (fun M => |(gatedLineModel L).count M -
        (gatedLineModel L).fixedExpectation {L.1} a (gatedLineModel L).count| ^ (2*s)) ≤
      ((2*s).factorial : ℝ) * 2^(2*s) *
        (2 * (163840 * ((1 + 10*s : ℕ) + 1)^4 : ℝ))^(2*s) *
          (Fintype.card F : ℝ)^s := by
  apply PatternModel.gated_centered_moment_le (lineModel L) {L.1}
    {M | L ∉ constituentLines M} (Set.toFinite _).measurableSet
    (lineGate_depends L) {L.1} (by rfl) a s 4 (Fintype.card F)
    (163840 * ((1 + 10*s : ℕ) + 1)^4 : ℝ)
    (by exact_mod_cast Fintype.card_pos (α := F)) (by positivity)
    (fun b => (allModel_support_card _ b).le)
  · intro K hK y hy
    apply lineModel_fixed_count_le L ({L.1} ∪ K) y (1 + 10*s) _ hy
    have hc := Finset.card_union_le ({L.1} : Finset (Direction F)) K
    simp only [Finset.card_singleton] at hc hK
    omega
  · intro K hK y hy
    apply lineModel_fixed_overlap_le L {L.1} K y (1 + 10*s) _ hy
    have hc := Finset.card_union_le ({L.1} : Finset (Direction F)) K
    simp only [Finset.card_singleton] at hc hK
    omega

theorem globalLineMomentConstant_nonneg (s : ℕ) : 0 ≤ globalLineMomentConstant s := by
  unfold globalLineMomentConstant
  positivity

theorem gatedLineModel_centered_moment_bound (L : Line F) (a : MergedPairs F) (s : ℕ) :
    (gatedLineModel L).fixedExpectation {L.1} a
      (fun M => |(gatedLineModel L).count M -
        (gatedLineModel L).fixedExpectation {L.1} a (gatedLineModel L).count| ^ (2*s)) ≤
      globalLineMomentConstant s * (Fintype.card F : ℝ)^s :=
  gatedLineModel_centered_moment_le L a s

end
end Balanced.CandidateGlobalLine

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

omit [Field F] [Fintype F] [DecidableEq F] in
theorem RootPrescription.tuple_injective {g : Direction F} :
    Function.Injective (RootPrescription.tuple (F := F) (g := g)) := by
  intro a b h
  apply Prod.ext
  · apply DFunLike.ext
    intro i
    apply Subtype.ext
    exact congrArg (fun T : FourTuple F => T.generator i) h
  · exact congrArg FourTuple.side h

omit [Fintype F] [DecidableEq F] in
theorem RootPrescription.choice_injective {g : Direction F} (M : MergedPairs F) :
    Function.Injective (fun a : RootPrescription g => a.choice M) := by
  intro a b h
  exact RootPrescription.tuple_injective (congrArg SplitChoice.tuple h)

theorem choice_on_line_of_successful {M : MergedPairs F} {g : Direction F}
    {a : RootPrescription g} (ha : a ∈ successfulPrescriptions M g) :
    ∀ i, OnLine (tuplePoint M a.tuple i) (a.choice M).line := by
  obtain ⟨c, hc⟩ := (Finset.mem_filter.mp ha).2.1
  intro i
  change lineEval g (tuplePoint M a.tuple i) = lineEval g (tuplePoint M a.tuple 0)
  exact (hc i).trans (hc 0).symm

@[simp] theorem successfulChoices_card (M : MergedPairs F) (g : Direction F) :
    (successfulChoices M g).card = rootSuccessCount g M := by
  rw [successfulChoices, Finset.card_image_of_injective _
    (RootPrescription.choice_injective M), successfulPrescriptions_card]

end
end Balanced.TupleAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidatePrescriptionTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateRetentionTransport

noncomputable section
open scoped Classical BigOperators
open TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem exists_successful_prescription {M : MergedPairs F} {g : Direction F}
    {C : SplitChoice F} (hC : C ∈ successfulChoices M) (hdir : C.line.1 = g) :
    ∃ a ∈ successfulPrescriptions M g, a.choice M = C := by
  rcases C with ⟨l, T⟩
  change l.1 = g at hdir
  obtain ⟨hinj, havoid, hpoints, hline⟩ := (mem_successfulChoices M _).mp hC
  let a := RootPrescription.ofTuple g T hinj (by simpa only [hdir] using havoid)
  have htuple : a.tuple = T := rfl
  have hl : (a.choice M).line = l := by
    change lineThrough g (tuplePoint M T 0) = l
    rw [← hdir]
    exact Prod.ext rfl (hline 0)
  have hchoice : a.choice M = (⟨l, T⟩ : SplitChoice F) := by
    change (⟨(a.choice M).line, T⟩ : SplitChoice F) = ⟨l, T⟩
    rw [hl]
  refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨l.2, ?_⟩, ?_⟩, hchoice⟩
  · intro i
    simpa only [htuple, ← hdir] using hline i
  · simpa only [htuple] using hpoints

theorem prescription_choice_mem_successful {M : MergedPairs F} {g : Direction F}
    {a : RootPrescription g} (ha : a ∈ successfulPrescriptions M g) :
    a.choice M ∈ successfulChoices M := by
  apply (mem_successfulChoices M _).mpr
  exact ⟨RootPrescription.injective a, fun i => (a.1 i).2,
    (Finset.mem_filter.mp ha).2.2, choice_on_line_of_successful ha⟩

theorem successfulTest_at_target_eq_image (M : MergedPairs F) (g : Direction F)
    (P : SplitChoice F → Prop) :
    successfulTest M (fun C => C.line.1 = g ∧ P C) =
      ((successfulPrescriptions M g).filter (fun a => P (a.choice M))).image
        (fun a => a.choice M) := by
  ext C
  constructor
  · intro hC
    obtain ⟨hC, hdir, hP⟩ := (mem_successfulTest M _ C).mp hC
    obtain ⟨a, ha, heq⟩ := exists_successful_prescription hC hdir
    exact Finset.mem_image.mpr
      ⟨a, Finset.mem_filter.mpr ⟨ha, by simpa only [heq] using hP⟩, heq⟩
  · intro hC
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨ha, hP⟩ := Finset.mem_filter.mp ha
    exact (mem_successfulTest M _ _).mpr
      ⟨prescription_choice_mem_successful ha, rfl, hP⟩

theorem successfulTest_at_target_card (M : MergedPairs F) (g : Direction F)
    (P : SplitChoice F → Prop) :
    (successfulTest M (fun C => C.line.1 = g ∧ P C)).card =
      ((successfulPrescriptions M g).filter (fun a => P (a.choice M))).card := by
  rw [successfulTest_at_target_eq_image]
  exact Finset.card_image_of_injective _ (RootPrescription.choice_injective M)

theorem successfulTest_card_eq_sum_prescriptions (M : MergedPairs F)
    (P : SplitChoice F → Prop) :
    (successfulTest M P).card = ∑ g : Direction F,
      ((successfulPrescriptions M g).filter (fun a => P (a.choice M))).card := by
  have hfiber (g : Direction F) :
      (successfulTest M P).filter (fun C => C.line.1 = g) =
        successfulTest M (fun C => C.line.1 = g ∧ P C) := by
    ext C
    simp only [Finset.mem_filter, mem_successfulTest]
    tauto
  rw [Finset.card_eq_sum_card_fiberwise (f := fun C : SplitChoice F => C.line.1)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  simp only [hfiber, successfulTest_at_target_card]

end
end Balanced.CandidateRetentionTransport

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateIncidenceTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateRetentionTransport

noncomputable section
open scoped Classical BigOperators
open TupleAlignment CandidateIncidence CandidateGlobalLine

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem model_choiceTest_count (P : SplitChoice F → Prop)
    (g : Direction F) (M : MergedPairs F) :
    (model (choiceTest P) g).count M =
      (((successfulPrescriptions M g).filter (fun a => P (a.choice M))).card : ℝ) := by
  unfold PatternModel.count PatternModel.indicator model event
    choiceTest rootSuccessEvent successfulPrescriptions RootPrescription.choice
  rw [Finset.filter_filter, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  simp only [Nat.cast_one, Set.indicator_apply, Set.mem_ofPred_eq]

theorem allModel_choiceTest_count (P : SplitChoice F → Prop)
    (M : MergedPairs F) :
    (allModel (choiceTest P)).count M = ((successfulTest M P).card : ℝ) := by
  rw [successfulTest_card_eq_sum_prescriptions, Nat.cast_sum]
  change (∑ a : Σ g : Direction F, RootPrescription g,
    (event (choiceTest P) a.1 a.2).indicator (fun _ => (1 : ℝ)) M) = _
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl (fun g _ => model_choiceTest_count P g M)

theorem lineModel_count_eq_successfulTest (L : Line F) (M : MergedPairs F) :
    (lineModel L).count M =
      ((successfulTest M (fun C => ∃ p ∈ designated M C, OnLine p L)).card : ℝ) := by
  rw [← allModel_choiceTest_count]
  unfold PatternModel.count
  apply Finset.sum_congr rfl
  intro a _
  simp [PatternModel.indicator, lineModel, allModel, event, lineHitTest,
    choiceTest, designated, Set.indicator_apply]

end
end Balanced.CandidateRetentionTransport

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteMomentTail
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped Classical
namespace Balanced
open scoped _root_.Balanced

theorem upper_tail_of_centered_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℝ) (m A q C : ℝ) (s : ℕ) (hq : 0 < q)
    (hm : m ≤ A * q)
    (hi : Integrable (fun ω => |X ω - m| ^ (2*s)) μ)
    (hbound : (∫ ω, |X ω - m| ^ (2*s) ∂μ) ≤ C * q^s) :
    μ.real {ω | (A+1)*q < X ω} ≤ C / q^s := by
  have hsub : {ω | (A+1)*q < X ω} ⊆
      {ω | q^(2*s) ≤ |X ω-m|^(2*s)} := by
    intro ω hω
    have hd : q ≤ |X ω-m| :=
      (by change (A+1)*q < X ω at hω; linarith : q ≤ X ω-m).trans (le_abs_self _)
    exact pow_le_pow_left₀ hq.le hd (2*s)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω => |X ω-m|^(2*s))
    (Filter.Eventually.of_forall (fun _ => by positivity)) hi (q^(2*s))
  have hmul : q^(2*s) * μ.real {ω | (A+1)*q < X ω} ≤ C*q^s :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (by positivity)).trans
      (hmarkov.trans hbound)
  calc
    _ ≤ (C*q^s) / q^(2*s) := by
      apply (le_div_iff₀ (pow_pos hq (2*s))).mpr
      simpa only [mul_comm] using hmul
    _ = C / q^s := by
      rw [two_mul, pow_add]
      field_simp

namespace PatternModel

theorem measureReal_le_of_fixed_indicator_bound (P : PatternModel)
    (K : Finset P.Color) (x : P.Sample) (E : Set P.Sample)
    (hE : MeasurableSet E) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ a, P.fixedExpectation K a (E.indicator (fun _ => (1 : ℝ))) ≤ B) :
    P.measure.real E ≤ B := by
  let : IsProbabilityMeasure P.measure := by
    dsimp [measure]
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hempty (ω : P.Sample) : P.fixCoordinates ∅ x ω = ω := by
    funext c
    simp [fixCoordinates]
  have h := P.fixedExpectation_mul_le_of_fixedBounds ∅ K x
    (fun _ => 1) (E.indicator (fun _ => (1 : ℝ))) B 1 1 hB
    measurable_const (measurable_const.indicator hE)
    (fun _ => zero_le_one) (fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    (fun _ => le_rfl)
    (fun ω => by by_cases hω : ω ∈ E <;> simp [hω])
    (fun _ _ _ => rfl)
    (by simpa only [Finset.empty_union] using hbound)
  simpa [fixedExpectation, hempty, integral_indicator_const, hE] using h

end PatternModel
end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateGlobalLineTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateGlobalLine
noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateExposure CandidateIncidence Filter Topology

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

attribute [local instance] OAI.Balanced.CandidateGlobalLine.globalLineTailMeasurableSpace
theorem gatedLineModel_conditional_upper_tail (L : Line F)
    (a : MergedPairs F) (s : ℕ) :
    (exposedLaw {L.1} a).toMeasure.real
      {M | 2621441 * (Fintype.card F : ℝ) < (gatedLineModel L).count M} ≤
      globalLineMomentConstant s / (Fintype.card F : ℝ)^s := by
  have hmoment := gatedLineModel_centered_moment_bound L a s
  rw [gatedLineModel_fixedExpectation] at hmoment
  have h := upper_tail_of_centered_moment (exposedLaw {L.1} a).toMeasure
    (gatedLineModel L).count
    ((gatedLineModel L).fixedExpectation {L.1} a (gatedLineModel L).count)
    2621440 (Fintype.card F) (globalLineMomentConstant s) s
    (by exact_mod_cast Fintype.card_pos (α := F))
    (gatedLineModel_initial_mean_le L a) Integrable.of_finite hmoment
  norm_num only [show (2621440+1 : ℝ) = 2621441 by norm_num] at h
  exact h

theorem gatedLineModel_upper_tail (L : Line F) (s : ℕ) :
    (offsetLaw F).toMeasure.real
      {M | 2621441 * (Fintype.card F : ℝ) < (gatedLineModel L).count M} ≤
      globalLineMomentConstant s / (Fintype.card F : ℝ)^s := by
  rw [← gatedLineModel_measure L]
  apply (gatedLineModel L).measureReal_le_of_fixed_indicator_bound
    {L.1} (fun _ _ => 0) _ (Set.toFinite _).measurableSet _
    (div_nonneg (globalLineMomentConstant_nonneg s) (by positivity))
  intro a
  rw [gatedLineModel_fixedExpectation,
    integral_indicator_const _ (Set.toFinite _).measurableSet]
  simpa only [smul_eq_mul, mul_one] using gatedLineModel_conditional_upper_tail L a s

theorem globalLineCount_eq_successfulTest (L : Line F) (M : MergedPairs F) :
    globalLineCount L M =
      (CandidateRetentionTransport.successfulTest M
        (fun C => ∃ p ∈ designated M C, OnLine p L)).card := by
  apply Nat.cast_injective (R := ℝ)
  calc
    (globalLineCount L M : ℝ) = (lineModel L).count M := by
      rw [allModel_count]
      simp only [globalLineCount, Nat.cast_sum]
    _ = _ := CandidateRetentionTransport.lineModel_count_eq_successfulTest L M

theorem gatedLineModel_count_eq (L : Line F) (M : MergedPairs F) :
    (gatedLineModel L).count M =
      if L ∉ constituentLines M then (globalLineCount L M : ℝ) else 0 := by
  rw [gatedLineModel_count]
  simp only [globalLineCount, Nat.cast_sum]

theorem globalLineCount_upper_tail (L : Line F) (s : ℕ) :
    (offsetLaw F).toMeasure.real
      {M | L ∉ constituentLines M ∧
        2621441 * (Fintype.card F : ℝ) < globalLineCount L M} ≤
      globalLineMomentConstant s / (Fintype.card F : ℝ)^s := by
  have hset : {M : MergedPairs F | L ∉ constituentLines M ∧
        2621441 * (Fintype.card F : ℝ) < globalLineCount L M} =
      {M | 2621441 * (Fintype.card F : ℝ) < (gatedLineModel L).count M} := by
    ext M
    simp only [Set.mem_ofPred_eq, gatedLineModel_count_eq]
    have hn : (0 : ℝ) ≤ 2621441 * (Fintype.card F : ℝ) := by positivity
    by_cases hM : L ∉ constituentLines M
    · simp [hM]
    · simp [hM, not_lt_of_ge hn]
  rw [hset]
  exact gatedLineModel_upper_tail L s

theorem globalLineCount_any_upper_tail :
    (offsetLaw F).toMeasure.real
      {M | ∃ L : Line F, L ∉ constituentLines M ∧
        2621441 * (Fintype.card F : ℝ) < globalLineCount L M} ≤
      2 * globalLineMomentConstant 4 / (Fintype.card F : ℝ)^2 := by
  let E : Line F → Set (MergedPairs F) := fun L =>
    {M | L ∉ constituentLines M ∧
      2621441 * (Fintype.card F : ℝ) < globalLineCount L M}
  have heq : {M : MergedPairs F | ∃ L : Line F, L ∉ constituentLines M ∧
      2621441 * (Fintype.card F : ℝ) < globalLineCount L M} = ⋃ L, E L := by
    ext M
    simp only [E, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [heq]
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hq0 : (0 : ℝ) < Fintype.card F := by linarith
  have hcard : (Fintype.card (Line F) : ℝ) ≤ 2 * (Fintype.card F : ℝ)^2 := by
    simp only [Line, Direction, Fintype.card_prod, Fintype.card_option,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    nlinarith
  calc
    _ ≤ ∑ L : Line F, (offsetLaw F).toMeasure.real (E L) :=
      measureReal_iUnion_fintype_le E
    _ ≤ ∑ _L : Line F, globalLineMomentConstant 4 / (Fintype.card F : ℝ)^4 :=
      Finset.sum_le_sum (fun L _ => globalLineCount_upper_tail L 4)
    _ = (Fintype.card (Line F) : ℝ) *
        (globalLineMomentConstant 4 / (Fintype.card F : ℝ)^4) := by simp
    _ ≤ (2 * (Fintype.card F : ℝ)^2) *
        (globalLineMomentConstant 4 / (Fintype.card F : ℝ)^4) :=
      mul_le_mul_of_nonneg_right hcard
        (div_nonneg (globalLineMomentConstant_nonneg 4) (by positivity))
    _ = _ := by field_simp

theorem globalLineCount_all_tendsto_one
    (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hcard : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => (offsetLaw (F n)).toMeasure.real
      {M | ∀ L : Line (F n), L ∉ constituentLines M →
        (globalLineCount L M : ℝ) ≤ 2621441 * Fintype.card (F n)})
      atTop (𝓝 1) := by
  let bad : ℕ → ℝ := fun n => (offsetLaw (F n)).toMeasure.real
    {M | ∃ L : Line (F n), L ∉ constituentLines M ∧
      2621441 * (Fintype.card (F n) : ℝ) < globalLineCount L M}
  have hqR : Tendsto (fun n => (Fintype.card (F n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcard
  have hbound : Tendsto (fun n => 2 * globalLineMomentConstant 4 /
      (Fintype.card (F n) : ℝ)^2) atTop (𝓝 0) := by
    have h := (hqR.const_div_atTop (2 * globalLineMomentConstant 4)).mul
      (hqR.const_div_atTop 1)
    convert h using 1
    · funext n
      simp only [div_mul_div_comm, mul_one, pow_two]
    · norm_num
  have hbad : Tendsto bad atTop (𝓝 0) :=
    squeeze_zero (fun _ => measureReal_nonneg)
      (fun _ => globalLineCount_any_upper_tail) hbound
  have hall : Tendsto (fun n => 1 - bad n) atTop (𝓝 (1-0 : ℝ)) :=
    tendsto_const_nhds.sub hbad
  have heq (n : ℕ) : (offsetLaw (F n)).toMeasure.real
      {M | ∀ L : Line (F n), L ∉ constituentLines M →
        (globalLineCount L M : ℝ) ≤ 2621441 * Fintype.card (F n)} =
        1 - bad n := by
    have hset : {M : MergedPairs (F n) | ∀ L : Line (F n), L ∉ constituentLines M →
        (globalLineCount L M : ℝ) ≤ 2621441 * Fintype.card (F n)} =
        {M | ∃ L : Line (F n), L ∉ constituentLines M ∧
          2621441 * (Fintype.card (F n) : ℝ) < globalLineCount L M}ᶜ := by
      ext M
      simp
    rw [hset, measureReal_compl (Set.toFinite _).measurableSet]
    simp only [probReal_univ, bad]
  simpa only [sub_zero, ← heq] using hall

theorem globalLineCount_all_probability_tendsto_one
    (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hcard : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | ∀ L : Line (F n), L ∉ constituentLines M →
        (globalLineCount L M : ℝ) ≤ 2621441 * Fintype.card (F n)})
      atTop (𝓝 1) := by
  have heq (n : ℕ) (E : Set (MergedPairs (F n))) :
      offsetEventProbability E = (offsetLaw (F n)).toMeasure.real E := by
    rw [offsetEventProbability, Measure.real,
      (offsetLaw (F n)).toMeasure_apply_eq_toOuterMeasure_apply
        ((Set.toFinite E).measurableSet)]
  simpa only [heq] using globalLineCount_all_tendsto_one F hcard

theorem successfulTest_globalLine_all_probability_tendsto_one
    (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hcard : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | ∀ L : Line (F n), L ∉ constituentLines M →
        ((CandidateRetentionTransport.successfulTest M
          (fun C => ∃ p ∈ designated M C, OnLine p L)).card : ℝ) ≤
          2621441 * Fintype.card (F n)}) atTop (𝓝 1) := by
  simpa only [globalLineCount_eq_successfulTest] using
    globalLineCount_all_probability_tendsto_one F hcard

end
end Balanced.CandidateGlobalLine

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateIncidenceCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Balanced.CandidateIncidenceTests

universe u

theorem tendsto_globalGood
    (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | GlobalGood M 2621441}) atTop (𝓝 1) := by
  simpa only [GlobalGood] using
    CandidateGlobalLine.successfulTest_globalLine_all_probability_tendsto_one F hq

theorem candidateGraphResult_of_size_estimate_oai (c : ℝ) (hc : 0 < c)
    (hsize : ∀ (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
      [∀ n, DecidableEq (F n)],
      Tendsto (fun n => Fintype.card (F n)) atTop atTop →
      Tendsto (fun n => offsetEventProbability (F := F n) {M | SizeGood M c})
        atTop (𝓝 1)) : CandidateGraphResult.{u} := by
  refine candidateGraphResult_of_incidence_estimates c 2621441 hc (by norm_num)
    hsize ?_ ?_
  · intro F _ _ _ hq
    exact tendsto_smallGood F hq
  · intro F _ _ _ hq
    exact tendsto_globalGood F hq

end Balanced.CandidateIncidenceTests

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Balanced.CandidateIncidenceTests.candidateGraphResult_of_size_estimate_oai.{u} := @OAI.Balanced.CandidateIncidenceTests.candidateGraphResult_of_size_estimate_oai.{u}
