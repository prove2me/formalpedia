-- Prove2me | solution 1 for OAI.Balanced.candidateGraph_proof
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:17:46.354066+00:00
-- url     : https://prove2.me/submissions/d1e6e824-6f58-4130-995f-a9a6836438ef

import Mathlib
import Definitions.Def_OAIQ63Br002
import Definitions.Def_OAIQ63Br003
import Theorems.Thm_OAI_Balanced_CandidateIncidenceTests_candidateGraphResult_of_size_estimate
import Theorems.Thm_OAI_Balanced_ExternalWitnessTail_candidateSlots_of_uniform_moment

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

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

section Measurable
variable [MeasurableSpace F] [MeasurableSingletonClass F]

theorem integral_overlappingTupleCount (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (∫ M, (overlappingTupleCount g D M : ℝ) ∂(exposedLaw D a).toMeasure) =
      overlapProbabilitySum g D a := by
  exact integral_eventCount_eq_sum (exposedLaw D a)
    ((eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card))
    (fun T => successfulInDirection T g)

theorem conditional_overlappingTupleCount_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∫ M, (overlappingTupleCount g D M : ℝ) ∂(exposedLaw D a).toMeasure) ≤
      (16384 * (m + 1) ^ 4 : ℝ) := by
  rw [integral_overlappingTupleCount]
  exact overlapProbabilitySum_le g D a m hD
end Measurable

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

theorem lintegral_moment_le_pow_of_marginal_bound
    {κ A : Type*} [Fintype κ] [DecidableEq κ] [Fintype A]
    {X : κ → Type*} [∀ c, MeasurableSpace (X c)]
    (μ : ∀ c, Measure (X c)) [∀ c, IsProbabilityMeasure (μ c)]
    (I : A → (∀ c, X c) → ℝ≥0∞) (support : A → Finset κ)
    (r s : ℕ) (C : ℝ≥0∞)
    (hI : ∀ a, Measurable (I a))
    (hsupport : ∀ a, (support a).card ≤ r)
    (hdepends : ∀ a x y,
      (∀ c ∈ support a, x c = y c) → I a x = I a y)
    (hbound : ∀ K : Finset κ, K.card ≤ (s - 1) * r → ∀ x,
      lmarginal μ (Finset.univ \ K) (fun y => ∑ a, I a y) x ≤ C) :
    (∫⁻ x, (∑ a, I a x) ^ s ∂Measure.pi μ) ≤ C ^ s := by
  classical
  have hsum : Measurable (fun x => ∑ a, I a x) :=
    Finset.measurable_sum _ (fun a _ => hI a)
  have hprod (n : ℕ) (t : Fin n → A) : Measurable (fun x => ∏ j, I (t j) x) :=
    Finset.measurable_prod _ (fun j _ => hI (t j))
  have hexpand (n : ℕ) :
      (∫⁻ x, (∑ a, I a x) ^ n ∂Measure.pi μ) =
        ∑ t : Fin n → A, ∫⁻ x, ∏ j, I (t j) x ∂Measure.pi μ := by
    simp_rw [Fintype.sum_pow]
    exact lintegral_finsetSum _ (fun t _ => hprod n t)
  have htuple (n : ℕ) (hn : n < s) (t : Fin n → A) :
      (∫⁻ x, (∏ j, I (t j) x) * (∑ a, I a x) ∂Measure.pi μ) ≤
        C * ∫⁻ x, ∏ j, I (t j) x ∂Measure.pi μ := by
    let K : Finset κ := Finset.univ.biUnion (fun j => support (t j))
    have hK : K.card ≤ (s - 1) * r := by
      calc
        K.card ≤ ∑ j : Fin n, (support (t j)).card := Finset.card_biUnion_le
        _ ≤ ∑ _j : Fin n, r := Finset.sum_le_sum (fun j _ => hsupport (t j))
        _ = n * r := by simp
        _ ≤ (s - 1) * r := Nat.mul_le_mul_right r (by omega)
    apply weighted_lintegral_le_of_marginal_bound μ K
      (fun x => ∏ j, I (t j) x) (fun x => ∑ a, I a x) C (hprod n t) hsum
    · intro x y hxy
      apply Finset.prod_congr rfl
      intro j _
      apply hdepends (t j) x y
      intro c hc
      exact hxy c (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hc⟩)
    · exact hbound K hK
  have hstep (n : ℕ) (hn : n < s) :
      (∫⁻ x, (∑ a, I a x) ^ (n + 1) ∂Measure.pi μ) ≤
        C * ∫⁻ x, (∑ a, I a x) ^ n ∂Measure.pi μ := by
    calc
      (∫⁻ x, (∑ a, I a x) ^ (n + 1) ∂Measure.pi μ) =
          ∑ t : Fin n → A,
            ∫⁻ x, (∏ j, I (t j) x) * (∑ a, I a x) ∂Measure.pi μ := by
        simp_rw [pow_succ, Fintype.sum_pow, Finset.sum_mul]
        exact lintegral_finsetSum _ (fun t _ => (hprod n t).mul hsum)
      _ ≤ ∑ t : Fin n → A, C * ∫⁻ x, ∏ j, I (t j) x ∂Measure.pi μ :=
        Finset.sum_le_sum (fun t _ => htuple n hn t)
      _ = C * ∫⁻ x, (∑ a, I a x) ^ n ∂Measure.pi μ := by
        rw [← Finset.mul_sum, hexpand]
  have hmoment : ∀ n ≤ s,
      (∫⁻ x, (∑ a, I a x) ^ n ∂Measure.pi μ) ≤ C ^ n := by
    intro n
    induction n with
    | zero =>
        intro _
        simp
    | succ n ih =>
        intro hn
        calc
          (∫⁻ x, (∑ a, I a x) ^ (n + 1) ∂Measure.pi μ) ≤
              C * ∫⁻ x, (∑ a, I a x) ^ n ∂Measure.pi μ := hstep n (by omega)
          _ ≤ C * C ^ n := mul_le_mul' le_rfl (ih (by omega))
          _ = C ^ (n + 1) := by rw [pow_succ, mul_comm]
  exact hmoment s le_rfl

theorem integral_moment_le_pow_of_marginal_bound
    {κ A : Type*} [Fintype κ] [DecidableEq κ] [Fintype A]
    {X : κ → Type*} [∀ c, MeasurableSpace (X c)]
    (μ : ∀ c, Measure (X c)) [∀ c, IsProbabilityMeasure (μ c)]
    (I : A → (∀ c, X c) → ℝ) (support : A → Finset κ)
    (r s : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hI : ∀ a, Measurable (I a)) (hnonneg : ∀ a x, 0 ≤ I a x)
    (hsupport : ∀ a, (support a).card ≤ r)
    (hdepends : ∀ a x y,
      (∀ c ∈ support a, x c = y c) → I a x = I a y)
    (hbound : ∀ K : Finset κ, K.card ≤ (s - 1) * r → ∀ x,
      lmarginal μ (Finset.univ \ K)
        (fun y => ENNReal.ofReal (∑ a, I a y)) x ≤ ENNReal.ofReal C) :
    (∫ x, (∑ a, I a x) ^ s ∂Measure.pi μ) ≤ C ^ s := by
  classical
  have hsum (x : ∀ c, X c) : 0 ≤ ∑ a, I a x :=
    Finset.sum_nonneg (fun a _ => hnonneg a x)
  have hsum_meas : Measurable (fun x => ∑ a, I a x) :=
    Finset.measurable_sum _ (fun a _ => hI a)
  have hsum_ofReal (x : ∀ c, X c) :
      (∑ a, ENNReal.ofReal (I a x)) = ENNReal.ofReal (∑ a, I a x) :=
    (ENNReal.ofReal_sum_of_nonneg (fun a _ => hnonneg a x)).symm
  have hE := lintegral_moment_le_pow_of_marginal_bound μ
    (fun a x => ENNReal.ofReal (I a x)) support r s (ENNReal.ofReal C)
    (fun a => (hI a).ennreal_ofReal) hsupport
    (by
      intro a x y hxy
      rw [hdepends a x y hxy])
    (by
      intro K hK x
      simpa only [hsum_ofReal] using hbound K hK x)
  simp_rw [hsum_ofReal] at hE
  have hreal := ENNReal.toReal_mono (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hE
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => pow_nonneg (hsum x) s))
    (hsum_meas.pow_const s).aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_pow (hsum _) s]
  simpa only [ENNReal.toReal_pow, ENNReal.toReal_ofReal hC] using hreal

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

theorem fixed_moment_le_pow (P : PatternModel)
    (K₀ : Finset P.Color) (x : P.Sample) (r s : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hsupport : ∀ a, (P.support a).card ≤ r)
    (hbound : ∀ K : Finset P.Color, K.card ≤ (s - 1) * r → ∀ y,
      P.fixedExpectation (K₀ ∪ K) y P.count ≤ C) :
    P.fixedExpectation K₀ x (fun ω => P.count ω ^ s) ≤ C ^ s := by
  classical
  have hi_meas (a : P.Label) : Measurable (P.indicator a) :=
    measurable_const.indicator (P.eventMeasurable a)
  have hi_nonneg (a : P.Label) (ω : P.Sample) : 0 ≤ P.indicator a ω :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have hi_le (a : P.Label) (ω : P.Sample) : P.indicator a ω ≤ 1 := by
    simp only [indicator, Set.indicator_apply]
    split_ifs <;> norm_num
  have hc_meas : Measurable P.count :=
    Finset.measurable_sum _ (fun a _ => hi_meas a)
  have hc_nonneg (ω : P.Sample) : 0 ≤ P.count ω :=
    Finset.sum_nonneg (fun a _ => hi_nonneg a ω)
  have hc_le (ω : P.Sample) : P.count ω ≤ (Fintype.card P.Label : ℝ) := by
    calc
      P.count ω ≤ ∑ _a : P.Label, (1 : ℝ) :=
        Finset.sum_le_sum (fun a _ => hi_le a ω)
      _ = _ := by simp
  have hfixed_integrable (J : Finset P.Color) (y : P.Sample) :
      Integrable (fun ω => P.count (P.fixCoordinates J y ω)) P.measure := by
    change Integrable _ (Measure.pi P.law)
    apply Integrable.of_bound
      (hc_meas.comp (P.measurable_fixCoordinates_map J y)).aestronglyMeasurable
      (Fintype.card P.Label : ℝ)
    exact Filter.Eventually.of_forall (fun ω => by
      change ‖P.count (P.fixCoordinates J y ω)‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (hc_nonneg _)]
      exact hc_le _)
  have hresult := PatternMarginals.integral_moment_le_pow_of_marginal_bound P.law
    (fun a ω => P.indicator a (P.fixCoordinates K₀ x ω))
    (fun a => P.support a \ K₀) r s C hC
    (fun a => (hi_meas a).comp (P.measurable_fixCoordinates_map K₀ x))
    (fun a ω => hi_nonneg a _) (fun a => (Finset.card_le_card Finset.sdiff_subset).trans (hsupport a))
    (by
      intro a ω ω' hω
      have hevent := P.dependsOn a (P.fixCoordinates K₀ x ω)
        (P.fixCoordinates K₀ x ω') (by
          intro c hc
          by_cases hc₀ : c ∈ K₀
          · simp [fixCoordinates, hc₀]
          · simpa [fixCoordinates, hc₀] using
              hω c (Finset.mem_sdiff.mpr ⟨hc, hc₀⟩))
      simp only [indicator, Set.indicator_apply, hevent])
    (by
      intro K hK y
      change lmarginal P.law (Finset.univ \ K)
        (fun ω => ENNReal.ofReal (P.count (P.fixCoordinates K₀ x ω))) y ≤
          ENNReal.ofReal C
      have hFc : Measurable (fun ω => ENNReal.ofReal
          (P.count (P.fixCoordinates K₀ x ω))) :=
        (hc_meas.comp (P.measurable_fixCoordinates_map K₀ x)).ennreal_ofReal
      rw [← P.lintegral_fixCoordinates_eq_lmarginal K y _ hFc]
      simp_rw [P.fixCoordinates_comp K₀ K x y]
      rw [← ofReal_integral_eq_lintegral_ofReal
        (hfixed_integrable (K₀ ∪ K) (P.fixCoordinates K₀ x y))
        (Filter.Eventually.of_forall (fun ω => hc_nonneg _))]
      exact ENNReal.ofReal_le_ofReal (hbound K hK (P.fixCoordinates K₀ x y)))
  simpa only [fixedExpectation, measure, count] using hresult

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

end Balanced.PatternModel

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateValidityWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateValidityWitness

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
private theorem target_constituent_intersection_unique
    {M : MergedPairs F} {S : Line F} {d : Direction F} {s : Bool}
    (hd : d ≠ S.1) {x y : Point F}
    (hx : OnLine x S) (hy : OnLine y S)
    (hxd : OnLine x (constituent M d s))
    (hyd : OnLine y (constituent M d s)) : x = y := by
  apply common_point_eq_of_lines_ne S (constituent M d s)
    (fun h => hd (congrArg Prod.fst h).symm) x y hx hxd hy hyd

private theorem previous_next (i : Fin 4) : (i + 3) + 1 = i := by
  fin_cases i <;> decide

omit [Field F] [Fintype F] [DecidableEq F] in
private theorem adjacent_generators_ne {T : FourTuple F}
    (hT : Function.Injective T.generator) (i : Fin 4) :
    T.generator i ≠ T.generator (i + 1) := by
  intro h
  have hi := hT h
  fin_cases i <;> simp at hi

omit [Fintype F] [DecidableEq F] in

theorem purposeful_endpoints {M : MergedPairs F} {T : FourTuple F}
    (hT : Function.Injective T.generator) (i : Fin 4) :
    OnLine (tuplePoint M T i) (constituent M (T.generator i) (T.side i)) ∧
    OnLine (tuplePoint M T (i + 3))
      (constituent M (T.generator i) (!(T.side i))) := by
  constructor
  · exact onLine_lineIntersection_left _ _ (adjacent_generators_ne hT i)
  · have h := onLine_lineIntersection_right
      (constituent M (T.generator (i + 3)) (T.side (i + 3)))
      (constituent M (T.generator ((i + 3) + 1)) (!(T.side ((i + 3) + 1))))
      (adjacent_generators_ne hT (i + 3))
    simpa only [tuplePoint, previous_next] using h

omit [Fintype F] [DecidableEq F] in

theorem on_used_constituent_endpoint {M : MergedPairs F} {T : FourTuple F}
    {S : Line F} (h : SuccessfulOn M T S) (i : Fin 4) (s : Bool)
    {x : Point F} (hx : OnLine x S)
    (hxd : OnLine x (constituent M (T.generator i) s)) :
    x = tuplePoint M T i ∨ x = tuplePoint M T (i + 3) := by
  have hend := purposeful_endpoints (M := M) h.1 i
  by_cases hs : s = T.side i
  · left
    exact target_constituent_intersection_unique (h.2.1 i) hx (h.2.2.2 i)
      (hs ▸ hxd) hend.1
  · have hs' : s = !(T.side i) := Bool.eq_not_of_ne hs
    right
    exact target_constituent_intersection_unique (h.2.1 i) hx (h.2.2.2 (i + 3))
      (hs' ▸ hxd) hend.2

omit [Fintype F] in

theorem external_not_on_used_constituent {M : MergedPairs F} {T : FourTuple F}
    {S : Line F} (h : SuccessfulOn M T S) {x : Point F}
    (hx : OnLine x S) (hex : x ∉ designated M ⟨S, T⟩)
    (i : Fin 4) (s : Bool) :
    ¬ OnLine x (constituent M (T.generator i) s) := by
  intro hxd
  rcases on_used_constituent_endpoint h i s hx hxd with he | he
  · exact hex (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he.symm⟩)
  · exact hex (Finset.mem_image.mpr ⟨i + 3, Finset.mem_univ _, he.symm⟩)

omit [Fintype F] in

theorem external_witness_not_generator {M : MergedPairs F} {T : FourTuple F}
    {S : Line F} (h : SuccessfulOn M T S) {x y : Point F}
    (hx : OnLine x S) (hex : x ∉ designated M ⟨S, T⟩) {d : Direction F}
    (hw : PairWitness M d x y) : d ∉ generatorSet T := by
  intro hd
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨s, hs, _⟩ := hw
  exact external_not_on_used_constituent h hx hex i s hs

omit [Fintype F] [DecidableEq F] in

theorem pairWitness_partner_unique {M : MergedPairs F} {S : Line F}
    {d : Direction F} (hd : d ≠ S.1) {x y z : Point F}
    (hx : OnLine x S) (hy : OnLine y S) (hz : OnLine z S)
    (hne : x ≠ y) (hxy : PairWitness M d x y) (hxz : PairWitness M d x z) :
    y = z := by
  obtain ⟨s, hxs, hys⟩ := hxy
  obtain ⟨t, hxt, hzt⟩ := hxz
  cases s <;> cases t
  · exact target_constituent_intersection_unique hd hy hz hys hzt
  · exact False.elim (hne (target_constituent_intersection_unique hd hx hy hxt hys))
  · exact False.elim (hne (target_constituent_intersection_unique hd hx hy hxt hys))
  · exact target_constituent_intersection_unique hd hy hz hys hzt

omit [Fintype F] in

theorem external_witness_directions_distinct {M : MergedPairs F} {T : FourTuple F}
    {S : Line F} (h : SuccessfulOn M T S) {x : Point F}
    (hx : OnLine x S) (hex : x ∉ designated M ⟨S, T⟩)
    {i j : Fin 4} (hij : i ≠ j) {d e : Direction F}
    (hd : d ≠ S.1) (hi : PairWitness M d x (tuplePoint M T i))
    (hj : PairWitness M e x (tuplePoint M T j)) : d ≠ e := by
  intro hde
  subst e
  have hne : x ≠ tuplePoint M T i := by
    intro he
    exact hex (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he.symm⟩)
  exact hij (h.2.2.1 (pairWitness_partner_unique hd hx
    (h.2.2.2 i) (h.2.2.2 j) hne hi hj))

end Balanced.CandidateValidityWitness

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateBasics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem candidateSlot_offset_injective (M : MergedPairs F) (s : Slot F) :
    Set.InjOn (fun v : CandidateVertex F => v.2) (candidateSlot M s) := by
  intro v hv w hw hoff
  apply Prod.ext
  · exact (mem_candidateSlot.mp hv).2.trans (mem_candidateSlot.mp hw).2.symm
  · exact hoff

theorem candidateSlot_card_le (M : MergedPairs F) (s : Slot F) :
    (candidateSlot M s).card ≤ Fintype.card F := by
  calc
    (candidateSlot M s).card ≤ (Finset.univ : Finset F).card :=
      Finset.card_le_card_of_injOn (fun v : CandidateVertex F => v.2)
        (fun _ _ => Finset.mem_univ _) (candidateSlot_offset_injective M s)
    _ = Fintype.card F := Finset.card_univ

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateExposedWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateExposedWitness

open CandidateValidityWitness

variable {F : Type*} [Field F]

theorem forcedPoint_on_target (a : MergedPairs F) (S : Line F) (d : Direction F)
    (hd : d ≠ S.1) (s : Bool) : OnLine (forcedPoint a S d s) S :=
  onLine_lineIntersection_left S (constituent a d s) (Ne.symm hd)

theorem forcedPoint_on_constituent (a : MergedPairs F) (S : Line F)
    (d : Direction F) (hd : d ≠ S.1) (s : Bool) :
    OnLine (forcedPoint a S d s) (constituent a d s) :=
  onLine_lineIntersection_right S (constituent a d s) (Ne.symm hd)

theorem eq_forcedPoint {a : MergedPairs F} {S : Line F} {d : Direction F}
    (hd : d ≠ S.1) {s : Bool} {x : Point F}
    (hx : OnLine x S) (hxd : OnLine x (constituent a d s)) :
    x = forcedPoint a S d s := by
  exact common_point_eq_of_lines_ne S (constituent a d s)
    (fun he => hd (congrArg Prod.fst he).symm) x (forcedPoint a S d s)
    hx hxd (forcedPoint_on_target a S d hd s)
    (forcedPoint_on_constituent a S d hd s)

theorem pairWitness_iff_forcedPoints {M a : MergedPairs F} {S : Line F}
    {d : Direction F} (hd : d ≠ S.1) (hMa : M d = a d)
    {x y : Point F} (hx : OnLine x S) (hy : OnLine y S) :
    PairWitness M d x y ↔ ∃ s : Bool,
      x = forcedPoint a S d s ∧ y = forcedPoint a S d (!s) := by
  have hline (s : Bool) : constituent M d s = constituent a d s := by
    simp only [constituent, hMa]
  constructor
  · rintro ⟨s, hxs, hys⟩
    rw [hline] at hxs hys
    exact ⟨s, eq_forcedPoint hd hx hxs, eq_forcedPoint hd hy hys⟩
  · rintro ⟨s, rfl, rfl⟩
    refine ⟨s, ?_, ?_⟩
    · rw [hline]
      exact forcedPoint_on_constituent a S d hd s
    · rw [hline]
      exact forcedPoint_on_constituent a S d hd (!s)

theorem exists_external_iff_forcedPoint {M a : MergedPairs F} {S : Line F}
    {d : Direction F} (hd : d ≠ S.1) (hMa : M d = a d)
    {y : Point F} (hy : OnLine y S) (R : Point F → Prop) :
    (∃ x, OnLine x S ∧ PairWitness M d x y ∧ R x) ↔
      ∃ s : Bool, y = forcedPoint a S d (!s) ∧ R (forcedPoint a S d s) := by
  constructor
  · rintro ⟨x, hx, hw, hR⟩
    obtain ⟨s, hxs, hys⟩ := (pairWitness_iff_forcedPoints hd hMa hx hy).mp hw
    exact ⟨s, hys, hxs ▸ hR⟩
  · rintro ⟨s, hys, hR⟩
    refine ⟨forcedPoint a S d s, forcedPoint_on_target a S d hd s, ?_, hR⟩
    exact (pairWitness_iff_forcedPoints hd hMa
      (forcedPoint_on_target a S d hd s) hy).mpr ⟨s, rfl, hys⟩

theorem external_point_unique [Fintype F] [DecidableEq F]
    {M : MergedPairs F} {T : FourTuple F} {S : Line F}
    (h : SuccessfulOn M T S) {d : Direction F} (hd : d ≠ S.1)
    (i : Fin 4) {x y : Point F}
    (hx : OnLine x S) (hy : OnLine y S)
    (hex : x ∉ designated M ⟨S, T⟩)
    (hxi : PairWitness M d x (tuplePoint M T i))
    (hyi : PairWitness M d y (tuplePoint M T i)) : x = y := by
  have hsym {u v : Point F} (huv : PairWitness M d u v) :
      PairWitness M d v u := by
    obtain ⟨s, hs, ht⟩ := huv
    exact ⟨!s, ht, by simpa using hs⟩
  have hne : tuplePoint M T i ≠ x := by
    intro he
    exact hex (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he⟩)
  exact pairWitness_partner_unique hd (h.2.2.2 i) hx hy hne (hsym hxi) (hsym hyi)

end Balanced.CandidateExposedWitness

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FreshWitnessProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FreshWitnessProbability

open ConditionalRestriction TupleAlignment
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem offsetLaw_uniform : offsetLaw F = PMF.uniformOfFintype (MergedPairs F) := by
  ext M
  simp only [offsetLaw, PMF.uniformOfFintype_apply, Fintype.card_fun,
    Fintype.card_option, Fintype.card_bool]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exposedLaw_map_fresh (D : Finset (Direction F)) (a : MergedPairs F)
    (e : ι ↪ Direction F) (hfresh : ∀ i, e i ∉ D) :
    (exposedLaw D a).map (fun M i => M (e i)) =
      PMF.uniformOfFintype (ι → Bool → F) := by
  have h := uniform_conditional_restrict (A := Bool → F) e (fun d => d ∈ D) a
  have hset : {o : ι → Bool → F | ∀ i, e i ∈ D → o i = a (e i)} = Set.univ := by
    ext o
    simp [hfresh]
  have htarget : ((PMF.uniformOfFintype (ι → Bool → F)).filter
      {o | ∀ i, e i ∈ D → o i = a (e i)}
      (fixed_supported (fun i => e i ∈ D) (fun i => a (e i)))) =
      PMF.uniformOfFintype (ι → Bool → F) := by
    ext o
    simp only [PMF.filter_apply, hset, Set.indicator_univ, PMF.tsum_coe,
      inv_one, mul_one]
  rw [htarget] at h
  simpa only [exposedLaw, offsetLaw_uniform] using h

theorem prescribed_offsets_probability (D : Finset (Direction F)) (a : MergedPairs F)
    (e : ι ↪ Direction F) (hfresh : ∀ i, e i ∉ D) (b : ι → Bool → F) :
    ((exposedLaw D a).toOuterMeasure {M | ∀ i, M (e i) = b i}).toReal =
      (Fintype.card F : ℝ)⁻¹ ^ (2 * Fintype.card ι) := by
  have h := congrArg (fun p => (p.toOuterMeasure {b}).toReal)
    (exposedLaw_map_fresh D a e hfresh)
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton] at h
  have hevent : (fun M i => M (e i)) ⁻¹' {b} =
      {M : MergedPairs F | ∀ i, M (e i) = b i} := by
    ext M
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    exact funext_iff
  rw [hevent] at h
  simpa only [PMF.uniformOfFintype_apply, Fintype.card_fun,
    Fintype.card_bool, Nat.cast_pow, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, inv_pow, pow_mul] using h

theorem probability_exists_le_sum {Ω κ : Type*} [Fintype κ]
    (law : PMF Ω) (E : κ → Set Ω) :
    (law.toOuterMeasure {ω | ∃ i, ω ∈ E i}).toReal ≤
      ∑ i, (law.toOuterMeasure (E i)).toReal := by
  have hfinite (i : κ) : law.toOuterMeasure (E i) ≠ ⊤ := by
    rw [PMF.toOuterMeasure_apply]
    exact law.tsum_coe_indicator_ne_top _
  have h := ENNReal.toReal_mono
    (ENNReal.sum_ne_top.mpr (fun i _ => hfinite i))
    (MeasureTheory.measure_iUnion_fintype_le law.toOuterMeasure E)
  rw [ENNReal.toReal_sum (fun i _ => hfinite i)] at h
  simpa only [Set.ofPred_exists, Set.ofPred_mem_eq] using h

theorem oriented_pairs_probability
    (D : Finset (Direction F)) (a : MergedPairs F)
    (e : ι ↪ Direction F) (hfresh : ∀ i, e i ∉ D)
    (x y : ι → Point F) (σ : ι → Bool) :
    ((exposedLaw D a).toOuterMeasure {M | ∀ i,
      OnLine (x i) (constituent M (e i) (σ i)) ∧
      OnLine (y i) (constituent M (e i) (!(σ i)))}).toReal =
      (Fintype.card F : ℝ)⁻¹ ^ (2 * Fintype.card ι) := by
  let b (i : ι) (s : Bool) : F :=
    if s = σ i then lineEval (e i) (x i) else lineEval (e i) (y i)
  have hevent : {M : MergedPairs F | ∀ i,
      OnLine (x i) (constituent M (e i) (σ i)) ∧
      OnLine (y i) (constituent M (e i) (!(σ i)))} =
      {M | ∀ i, M (e i) = b i} := by
    ext M
    simp only [Set.mem_ofPred_eq, OnLine, constituent]
    constructor
    · intro h i
      funext s
      cases hs : σ i <;> cases s
      · simpa [b, hs] using (h i).1.symm
      · simpa [b, hs] using (h i).2.symm
      · simpa [b, hs] using (h i).2.symm
      · simpa [b, hs] using (h i).1.symm
    · intro h i
      have hfalse := congrFun (h i) false
      have htrue := congrFun (h i) true
      cases hs : σ i <;> simp_all [b]
  rw [hevent]
  exact prescribed_offsets_probability D a e hfresh b

theorem paired_witnesses_probability_le
    (D : Finset (Direction F)) (a : MergedPairs F)
    (e : ι ↪ Direction F) (hfresh : ∀ i, e i ∉ D)
    (x y : ι → Point F) :
    ((exposedLaw D a).toOuterMeasure {M | ∃ σ : ι → Bool, ∀ i,
      OnLine (x i) (constituent M (e i) (σ i)) ∧
      OnLine (y i) (constituent M (e i) (!(σ i)))}).toReal ≤
      (2 : ℝ) ^ Fintype.card ι *
        (Fintype.card F : ℝ)⁻¹ ^ (2 * Fintype.card ι) := by
  calc
    _ ≤ ∑ σ : ι → Bool, ((exposedLaw D a).toOuterMeasure {M | ∀ i,
        OnLine (x i) (constituent M (e i) (σ i)) ∧
        OnLine (y i) (constituent M (e i) (!(σ i)))}).toReal :=
      probability_exists_le_sum _ _
    _ = _ := by
      simp only [oriented_pairs_probability D a e hfresh, Finset.sum_const,
        Finset.card_univ, Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat]

end
end Balanced.FreshWitnessProbability

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FreshTupleConstraints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FreshTupleConstraints

open TupleAlignment FreshWitnessProbability
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem exposed_tuplePoint_uniform
    (D : Finset (Direction F)) (a : MergedPairs F) (T : FourTuple F)
    (hT : Function.Injective T.generator) (hfresh : ∀ i, T.generator i ∉ D) :
    (exposedLaw D a).map (fun M => tuplePoint M T) =
      PMF.uniformOfFintype (Fin 4 → Point F) := by
  let hd := adjacent_ne_of_injective T hT
  let r : MergedPairs F → Fin 4 → Bool → F := fun M i => M (T.generator i)
  have hr := exposedLaw_map_fresh D a ⟨T.generator, hT⟩ hfresh
  simp only [Function.Embedding.coeFn_mk] at hr
  have hf : (fun M => tuplePoint M T) =
      tuplePositionEquiv T.generator hd T.side ∘ r := by
    funext M i
    rfl
  rw [hf, ← PMF.map_comp]
  change ((exposedLaw D a).map (fun M i => M (T.generator i))).map _ = _
  rw [hr]
  exact tuplePosition_uniform T.generator hd T.side

theorem tuple_box_probability
    (D : Finset (Direction F)) (a : MergedPairs F) (T : FourTuple F)
    (hT : Function.Injective T.generator) (hfresh : ∀ i, T.generator i ∉ D)
    (B : Fin 4 → Finset (Point F)) :
    ((exposedLaw D a).toOuterMeasure
      {M | ∀ i, tuplePoint M T i ∈ B i}).toReal =
      (∏ i, ((B i).card : ℝ)) / (Fintype.card F : ℝ)^8 := by
  let E : Set (Fin 4 → Point F) := {p | ∀ i, p i ∈ B i}
  have h := congrArg (fun p => (p.toOuterMeasure E).toReal)
    (exposed_tuplePoint_uniform D a T hT hfresh)
  rw [PMF.toOuterMeasure_map_apply] at h
  have hcard : Fintype.card E = ∏ i, (B i).card := by
    change Fintype.card {p : Fin 4 → Point F // ∀ i, p i ∈ B i} = _
    rw [Fintype.card_congr (Equiv.subtypePiEquivPi
      (p := fun i p => p ∈ B i)), Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro i hi
    exact Fintype.card_coe (B i)
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, hcard] at h
  simpa only [E, Set.preimage_ofPred_eq, Fintype.card_fun, Point,
    Fintype.card_prod, Fintype.card_fin, Nat.cast_prod, Nat.cast_pow,
    Nat.cast_mul, ← pow_two, ← pow_mul] using h

theorem pinned_positions_probability
    (D : Finset (Direction F)) (a : MergedPairs F) (T : FourTuple F)
    (hT : Function.Injective T.generator) (hfresh : ∀ i, T.generator i ∉ D)
    (S : Line F) (J : Finset (Fin 4)) (x : Fin 4 → Point F)
    (hx : ∀ i ∈ J, OnLine (x i) S) :
    ((exposedLaw D a).toOuterMeasure {M |
      (∀ i, OnLine (tuplePoint M T i) S) ∧
      ∀ i ∈ J, tuplePoint M T i = x i}).toReal =
      (Fintype.card F : ℝ)⁻¹ ^ (4 + J.card) := by
  let B : Fin 4 → Finset (Point F) := fun i =>
    if i ∈ J then {x i} else linePoints S
  have hevent : {M : MergedPairs F |
      (∀ i, OnLine (tuplePoint M T i) S) ∧
      ∀ i ∈ J, tuplePoint M T i = x i} =
      {M | ∀ i, tuplePoint M T i ∈ B i} := by
    ext M
    constructor
    · rintro ⟨hon, hpin⟩ i
      by_cases hi : i ∈ J
      · simp [B, hi, hpin i hi]
      · simpa [B, hi, linePoints] using hon i
    · intro h
      constructor
      · intro i
        by_cases hi : i ∈ J
        · have hp : tuplePoint M T i = x i := by simpa [B, hi] using h i
          simpa [hp] using hx i hi
        · simpa [B, hi, linePoints] using h i
      · intro i hi
        simpa [B, hi] using h i
  rw [hevent, tuple_box_probability D a T hT hfresh B]
  have hprod : (∏ i, ((B i).card : ℝ)) =
      (Fintype.card F : ℝ)^(4 - J.card) := by
    simp only [B, apply_ite Finset.card, Finset.card_singleton,
      linePoints_card, Nat.cast_ite, Nat.cast_one]
    rw [Finset.prod_ite]
    have hc : (Finset.univ.filter (fun i : Fin 4 => i ∉ J)) = Jᶜ := by
      ext i
      simp
    simp only [Finset.prod_const_one, one_mul, Finset.prod_const, hc,
      Finset.card_compl, Fintype.card_fin]
  rw [hprod]
  have hj : J.card ≤ 4 := by simpa using J.card_le_univ
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hexp : (4 - J.card) + (4 + J.card) = 8 := by omega
  calc
    _ = (Fintype.card F : ℝ)^(4 - J.card) /
        ((Fintype.card F : ℝ)^(4 - J.card) *
          (Fintype.card F : ℝ)^(4 + J.card)) := by rw [← pow_add, hexp]
    _ = ((Fintype.card F : ℝ)^(4 + J.card))⁻¹ := by
      field_simp
    _ = _ := (inv_pow _ _).symm

theorem one_pinned_position_probability
    (D : Finset (Direction F)) (a : MergedPairs F) (T : FourTuple F)
    (hT : Function.Injective T.generator) (hfresh : ∀ i, T.generator i ∉ D)
    (S : Line F) (i : Fin 4) (x : Point F) (hx : OnLine x S) :
    ((exposedLaw D a).toOuterMeasure {M |
      (∀ j, OnLine (tuplePoint M T j) S) ∧ tuplePoint M T i = x}).toReal =
      (Fintype.card F : ℝ)⁻¹ ^ 5 := by
  have h := pinned_positions_probability D a T hT hfresh S {i} (fun _ => x)
    (fun _ _ => hx)
  simpa using h

end
end Balanced.FreshTupleConstraints

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ExposedWitnessProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ExposedWitnessProbability

open CandidateValidityWitness CandidateExposedWitness FreshWitnessProbability
open FreshTupleConstraints
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in

theorem exposedLaw_support_fixed (D : Finset (Direction F)) (a M : MergedPairs F)
    (hM : M ∈ (exposedLaw D a).support) (d : Direction F) (hd : d ∈ D) :
    M d = a d := by
  exact ((PMF.mem_support_filter_iff _).mp hM).1 d hd

theorem real_probability_mono_support {Ω : Type*} (law : PMF Ω) {E G : Set Ω}
    (h : E ∩ law.support ⊆ G) :
    (law.toOuterMeasure E).toReal ≤ (law.toOuterMeasure G).toReal := by
  apply ENNReal.toReal_mono
  · rw [PMF.toOuterMeasure_apply]
    exact law.tsum_coe_indicator_ne_top _
  · exact law.toOuterMeasure_mono h

theorem successful_external_probability_le
    (D : Finset (Direction F)) (a : MergedPairs F) (T : FourTuple F)
    (hT : Function.Injective T.generator) (hfresh : ∀ i, T.generator i ∉ D)
    (S : Line F) (d : Direction F) (hdD : d ∈ D) (hd : d ≠ S.1)
    (i : Fin 4) (R : MergedPairs F → Point F → Prop) :
    ((exposedLaw D a).toOuterMeasure {M | SuccessfulOn M T S ∧
      ∃ x, OnLine x S ∧ PairWitness M d x (tuplePoint M T i) ∧ R M x}).toReal ≤
      2 * (Fintype.card F : ℝ)⁻¹ ^ 5 := by
  let E (s : Bool) : Set (MergedPairs F) := {M |
    (∀ k, OnLine (tuplePoint M T k) S) ∧
    tuplePoint M T i = forcedPoint a S d (!s)}
  calc
    _ ≤ ((exposedLaw D a).toOuterMeasure {M | ∃ s, M ∈ E s}).toReal := by
      apply real_probability_mono_support
      rintro M ⟨⟨hS, hw⟩, hM⟩
      obtain ⟨s, hs, _⟩ := (exists_external_iff_forcedPoint hd
        (exposedLaw_support_fixed D a M hM d hdD) (hS.2.2.2 i) (R M)).mp hw
      exact ⟨s, hS.2.2.2, hs⟩
    _ ≤ ∑ s : Bool, ((exposedLaw D a).toOuterMeasure (E s)).toReal :=
      probability_exists_le_sum _ _
    _ = _ := by
      have hE (s : Bool) : ((exposedLaw D a).toOuterMeasure (E s)).toReal =
          (Fintype.card F : ℝ)⁻¹ ^ 5 :=
        one_pinned_position_probability D a T hT hfresh S i _
          (forcedPoint_on_target a S d hd (!s))
      simp only [hE, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
        nsmul_eq_mul, Nat.cast_ofNat]

end
end Balanced.ExposedWitnessProbability

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_ExposedOppositeSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ExposedOppositeSum

open CandidateValidityWitness FreshWitnessProbability ExposedWitnessProbability
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [DecidableEq F] in

theorem card_fourTuple : Fintype.card (FourTuple F) =
    16 * (Fintype.card F + 1)^4 := by
  let e : FourTuple F ≃ ((Fin 4 → Direction F) × (Fin 4 → Bool)) :=
    { toFun := fun T => (T.generator, T.side)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e]
  simp [Fintype.card_prod, Direction, mul_comm]

theorem freshTuples_card_le (D : Finset (Direction F)) :
    (freshTuples D).card ≤ 256 * Fintype.card F ^ 4 := by
  have hq : 0 < Fintype.card F := Fintype.card_pos
  calc
    _ ≤ Fintype.card (FourTuple F) := Finset.card_le_univ _
    _ = 16 * (Fintype.card F + 1)^4 := card_fourTuple
    _ ≤ 16 * (2 * Fintype.card F)^4 := by gcongr; omega
    _ = _ := by ring

end
end Balanced.ExposedOppositeSum

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FreshCoordinatePrescription
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FreshCoordinate

noncomputable section
open scoped Classical
attribute [local instance] Classical.propDecidable

variable {D A : Type*} [DecidableEq D]

variable [Fintype D] [Fintype A] [Nonempty A]

theorem probability_prescription_on_subtype (d : D)
    (G E : (D → A) → Prop) [Nonempty {f : D → A // G f}]
    (b : (D → A) → A)
    (hG : ∀ f a, G (Function.update f d a) ↔ G f)
    (hE : ∀ f a, E (Function.update f d a) ↔ E f)
    (hb : ∀ f a, b (Function.update f d a) = b f) :
    ((PMF.uniformOfFintype {f : D → A // G f}).toOuterMeasure
      {f | E f.1 ∧ f.1 d = b f.1}).toReal =
    ((PMF.uniformOfFintype {f : D → A // G f}).toOuterMeasure
      {f | E f.1}).toReal / Fintype.card A := by
  simp only [PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div,
    ENNReal.toReal_natCast]
  change (Fintype.card {f : {f : D → A // G f} // E f.1 ∧ f.1 d = b f.1} : ℝ) /
      Fintype.card {f : D → A // G f} =
    (Fintype.card {f : {f : D → A // G f} // E f.1} : ℝ) /
      Fintype.card {f : D → A // G f} / Fintype.card A
  have he : Fintype.card {f : {f : D → A // G f} // E f.1} =
      Fintype.card {f : D → A // G f ∧ E f} :=
    Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter G E)
  have hp : Fintype.card {f : {f : D → A // G f} // E f.1 ∧ f.1 d = b f.1} =
      Fintype.card {f : D → A // (G f ∧ E f) ∧ f d = b f} := by
    apply Fintype.card_congr
    exact (Equiv.subtypeSubtypeEquivSubtypeInter G
      (fun f => E f ∧ f d = b f)).trans
        (Equiv.subtypeEquivRight fun _ => and_assoc.symm)
  rw [he, hp]
  have hc : Fintype.card {f : D → A // G f ∧ E f} =
      Fintype.card {f : D → A // (G f ∧ E f) ∧ f d = b f} * Fintype.card A := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr (prescriptionEquiv d (fun f => G f ∧ E f) b
      (by intro f a; rw [hG, hE]) hb)
  have hcR : (Fintype.card {f : D → A // G f ∧ E f} : ℝ) =
      Fintype.card {f : D → A // (G f ∧ E f) ∧ f d = b f} * Fintype.card A := by
    exact_mod_cast hc
  rw [hcR]
  have hA : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

end
end Balanced.FreshCoordinate

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FreshTupleWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FreshTupleWitness

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
theorem tuplePoint_update_fresh (T : FourTuple F) (d : Direction F)
    (hd : ∀ i, T.generator i ≠ d) (M : MergedPairs F) (a : Bool → F) :
    tuplePoint (Function.update M d a) T = tuplePoint M T := by
  funext i
  simp only [tuplePoint, constituent, Function.update_of_ne (hd i),
    Function.update_of_ne (hd (i + 1))]

omit [Fintype F] [DecidableEq F] in
theorem pairPrescription_iff (M : MergedPairs F) (d : Direction F)
    (p r : Point F) (σ : Bool) :
    M d = pairPrescription d p r σ ↔
      OnLine p (constituent M d σ) ∧ OnLine r (constituent M d (!σ)) := by
  constructor
  · intro h
    constructor
    · simpa [pairPrescription, OnLine, constituent] using
        (congrFun h σ).symm
    · simpa [pairPrescription, OnLine, constituent] using
        (congrFun h (!σ)).symm
  · rintro ⟨hp, hr⟩
    funext b
    cases σ <;> cases b <;>
      simp_all [pairPrescription, OnLine, constituent]

omit [Field F] [Fintype F] in
theorem fixed_coordinates_update_invariant (P : Direction F → Prop)
    (a : MergedPairs F) (d : Direction F) (hPd : ¬ P d)
    (M : MergedPairs F) (v : Bool → F) :
    (∀ t, P t → Function.update M d v t = a t) ↔
      (∀ t, P t → M t = a t) := by
  apply forall_congr'
  intro t
  by_cases ht : P t
  · have htd : t ≠ d := by intro heq; exact hPd (heq ▸ ht)
    simp only [Function.update_of_ne htd]
  · simp only [ht, false_implies]

end
end Balanced.FreshTupleWitness

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

omit [Fintype F] in
theorem tuplePoint_eq_of_generators (T : FourTuple F) (M N : MergedPairs F)
    (h : ∀ d ∈ generatorSet T, M d = N d) (i : Fin 4) :
    tuplePoint M T i = tuplePoint N T i := by
  have hi : T.generator i ∈ generatorSet T := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hn : T.generator (i+1) ∈ generatorSet T :=
    Finset.mem_image.mpr ⟨i+1, Finset.mem_univ _, rfl⟩
  simp only [tuplePoint, constituent, h _ hi, h _ hn]

section Measurable
variable [MeasurableSpace F] [MeasurableSingletonClass F]

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

end Measurable
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

theorem pairLinearThreshold_pos : 0 < pairLinearThreshold := by
  unfold pairLinearThreshold
  linarith [pairExposureConstant_nonneg 0]

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

theorem slotLinearConstant_pos : 0 < slotLinearConstant :=
  div_pos (by norm_num) pairLinearThreshold_pos

end
end Balanced.CandidateAbundanceAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateWitnessProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateWitnessProbability

open CandidateValidityWitness FreshWitnessProbability

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem pairWitness_family_probability_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Finset (Direction F)) (a : MergedPairs F)
    (e : ι ↪ Direction F) (hfresh : ∀ i, e i ∉ D)
    (x y : ι → Point F) :
    ((exposedLaw D a).toOuterMeasure
      {M | ∀ i, PairWitness M (e i) (x i) (y i)}).toReal ≤
      (2 : ℝ) ^ Fintype.card ι *
        (Fintype.card F : ℝ)⁻¹ ^ (2 * Fintype.card ι) := by
  have hevent : {M : MergedPairs F | ∀ i, PairWitness M (e i) (x i) (y i)} =
      {M | ∃ σ : ι → Bool, ∀ i,
        OnLine (x i) (constituent M (e i) (σ i)) ∧
        OnLine (y i) (constituent M (e i) (!(σ i)))} := by
    ext M
    simp only [Set.mem_ofPred_eq, PairWitness]
    constructor
    · intro h
      choose σ hσ using h
      exact ⟨σ, hσ⟩
    · rintro ⟨σ, hσ⟩ i
      exact ⟨σ i, hσ i⟩
  rw [hevent]
  exact paired_witnesses_probability_le D a e hfresh x y

theorem pairWitness_probability_le
    (D : Finset (Direction F)) (a : MergedPairs F)
    (d : Direction F) (hd : d ∉ D) (x y : Point F) :
    ((exposedLaw D a).toOuterMeasure {M | PairWitness M d x y}).toReal ≤
      2 / (Fintype.card F : ℝ)^2 := by
  let e : Unit ↪ Direction F := ⟨fun _ => d, fun _ _ _ => Subsingleton.elim _ _⟩
  have h := pairWitness_family_probability_le D a e (fun _ => hd)
    (fun _ => x) (fun _ => y)
  change ((exposedLaw D a).toOuterMeasure
    {M | ∀ _ : Unit, PairWitness M d x y}).toReal ≤ _ at h
  simpa [div_eq_mul_inv] using h

end
end Balanced.CandidateWitnessProbability

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_ExposedExternalFresh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ExposedExternalFresh

noncomputable section
open scoped Classical BigOperators
attribute [local instance] Classical.propDecidable
open MeasureTheory CandidateValidityWitness CandidateExposedWitness
open FreshWitnessProbability FreshTupleConstraints ExposedWitnessProbability

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

attribute [local instance] OAI.Balanced.ExposedExternalFresh.externalFreshMeasurableSpace
omit [Field F] in

theorem probability_eq_integral_indicator (law : PMF (MergedPairs F))
    (E : MergedPairs F → Prop) :
    (law.toOuterMeasure {M | E M}).toReal =
      ∫ M, (if E M then (1 : ℝ) else 0) ∂law.toMeasure := by
  rw [PMF.integral_eq_sum, PMF.toOuterMeasure_apply_fintype,
    ENNReal.toReal_sum (fun M _ => by
      by_cases h : E M
      · simpa [Set.indicator_apply, h] using law.apply_ne_top M
      · simp [h])]
  apply Finset.sum_congr rfl
  intro M _
  by_cases h : E M <;> simp [h]

theorem conditional_fresh_pair_integral_le
    (D : Finset (Direction F)) (a : MergedPairs F) (T : FourTuple F)
    (e : Direction F) (heD : e ∉ D) (heT : e ∉ generatorSet T)
    (x : Point F) (j : Fin 4) :
    (∫ M, (if PairWitness M e x (tuplePoint M T j) then (1 : ℝ) else 0)
      ∂(exposedLaw (D ∪ generatorSet T) a).toMeasure) ≤
      2 / (Fintype.card F : ℝ)^2 := by
  have heq := ConditionalRestriction.integral_eq_of_eq_on_support
    (exposedLaw (D ∪ generatorSet T) a)
    (fun M => if PairWitness M e x (tuplePoint M T j) then (1 : ℝ) else 0)
    (fun M => if PairWitness M e x (tuplePoint a T j) then (1 : ℝ) else 0) (by
      intro M hM
      have hp := CandidatePairs.tuplePoint_eq_of_generators T M a
        (fun d hd => exposedLaw_support_fixed (D ∪ generatorSet T) a M hM d
          (Finset.mem_union_right _ hd)) j
      rw [hp])
  rw [heq, ← probability_eq_integral_indicator
    (exposedLaw (D ∪ generatorSet T) a)
    (fun M => PairWitness M e x (tuplePoint a T j))]
  exact CandidateWitnessProbability.pairWitness_probability_le
    (D ∪ generatorSet T) a e (by simpa using And.intro heD heT) x _

theorem pinned_fresh_pair_probability_le
    (D : Finset (Direction F)) (a : MergedPairs F) (T : FourTuple F)
    (hT : Function.Injective T.generator) (hfresh : ∀ i, T.generator i ∉ D)
    (S : Line F) (i : Fin 4) (p : Point F) (hp : OnLine p S)
    (e : Direction F) (heD : e ∉ D) (heT : e ∉ generatorSet T)
    (x : Point F) (j : Fin 4) :
    ((exposedLaw D a).toOuterMeasure {M |
      (∀ k, OnLine (tuplePoint M T k) S) ∧ tuplePoint M T i = p ∧
      PairWitness M e x (tuplePoint M T j)}).toReal ≤
      2 * (Fintype.card F : ℝ)⁻¹ ^ 7 := by
  let f : MergedPairs F → ℝ := fun M =>
    if (∀ k, OnLine (tuplePoint M T k) S) ∧ tuplePoint M T i = p then 1 else 0
  let z : MergedPairs F → ℝ := fun M =>
    if PairWitness M e x (tuplePoint M T j) then 1 else 0
  have ht := CandidatePairs.exposed_integral_mul_le D (generatorSet T) a f z
    (2 / (Fintype.card F : ℝ)^2) 1 1 (by positivity)
    (fun M => by dsimp [f]; split_ifs <;> norm_num)
    (fun M => by dsimp [z]; split_ifs <;> norm_num)
    (fun M => by dsimp [f]; split_ifs <;> norm_num)
    (fun M => by dsimp [z]; split_ifs <;> norm_num)
    (by
      intro M N hMN
      have hpoints : tuplePoint M T = tuplePoint N T := by
        funext k
        exact CandidatePairs.tuplePoint_eq_of_generators T M N
          (fun d hd => hMN d (Finset.mem_union_right _ hd)) k
      simp only [f, hpoints])
    (fun y => conditional_fresh_pair_integral_le D y T e heD heT x j)
  have hf : (∫ M, f M ∂(exposedLaw D a).toMeasure) =
      (Fintype.card F : ℝ)⁻¹ ^ 5 := by
    rw [show (∫ M, f M ∂(exposedLaw D a).toMeasure) =
      ((exposedLaw D a).toOuterMeasure {M |
        (∀ k, OnLine (tuplePoint M T k) S) ∧ tuplePoint M T i = p}).toReal from
      (by
        convert (probability_eq_integral_indicator (exposedLaw D a)
          (fun M => (∀ k, OnLine (tuplePoint M T k) S) ∧
            tuplePoint M T i = p)).symm using 1
        all_goals try with_reducible_and_instances rfl
        apply integral_congr_ae
        filter_upwards [] with M
        dsimp [f]
        split_ifs <;> rfl)]
    exact one_pinned_position_probability D a T hT hfresh S i p hp
  have heq :
      ((exposedLaw D a).toOuterMeasure {M |
        (∀ k, OnLine (tuplePoint M T k) S) ∧ tuplePoint M T i = p ∧
        PairWitness M e x (tuplePoint M T j)}).toReal =
      ∫ M, f M * z M ∂(exposedLaw D a).toMeasure := by
    rw [probability_eq_integral_indicator]
    apply integral_congr_ae
    filter_upwards [] with M
    dsimp [f, z]
    split_ifs <;> simp_all
  rw [heq]
  change (∫ M, f M * z M ∂(exposedLaw D a).toMeasure) ≤
    _ * (∫ M, f M ∂(exposedLaw D a).toMeasure) at ht
  rw [hf] at ht
  simpa only [div_eq_mul_inv, ← inv_pow, mul_assoc, ← pow_add] using ht

theorem successful_external_fresh_probability_le
    (D : Finset (Direction F)) (a : MergedPairs F) (T : FourTuple F)
    (hT : Function.Injective T.generator) (hfresh : ∀ i, T.generator i ∉ D)
    (S : Line F) (d : Direction F) (hdD : d ∈ D) (hd : d ≠ S.1)
    (e : Direction F) (heD : e ∉ D) (heT : e ∉ generatorSet T)
    (i j : Fin 4) :
    ((exposedLaw D a).toOuterMeasure {M | SuccessfulOn M T S ∧
      ∃ x, OnLine x S ∧ PairWitness M d x (tuplePoint M T i) ∧
        PairWitness M e x (tuplePoint M T j)}).toReal ≤
      4 * (Fintype.card F : ℝ)⁻¹ ^ 7 := by
  let E (s : Bool) : Set (MergedPairs F) := {M |
    (∀ k, OnLine (tuplePoint M T k) S) ∧
    tuplePoint M T i = forcedPoint a S d (!s) ∧
    PairWitness M e (forcedPoint a S d s) (tuplePoint M T j)}
  calc
    _ ≤ ((exposedLaw D a).toOuterMeasure {M | ∃ s, M ∈ E s}).toReal := by
      apply real_probability_mono_support
      rintro M ⟨⟨hS, hw⟩, hM⟩
      obtain ⟨s, hs, ht⟩ := (exists_external_iff_forcedPoint hd
        (exposedLaw_support_fixed D a M hM d hdD) (hS.2.2.2 i)
        (fun x => PairWitness M e x (tuplePoint M T j))).mp hw
      exact ⟨s, hS.2.2.2, hs, ht⟩
    _ ≤ ∑ s : Bool, ((exposedLaw D a).toOuterMeasure (E s)).toReal :=
      probability_exists_le_sum _ _
    _ ≤ ∑ _s : Bool, 2 * (Fintype.card F : ℝ)⁻¹ ^ 7 := by
      apply Finset.sum_le_sum
      intro s _
      exact pinned_fresh_pair_probability_le D a T hT hfresh S i
        (forcedPoint a S d (!s)) (forcedPoint_on_target a S d hd (!s))
        e heD heT (forcedPoint a S d s) j
    _ = _ := by simp; ring

end
end Balanced.ExposedExternalFresh

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_ExternalWitnessModel
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ExternalAssembly

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateValidityWitness
attribute [local instance] Classical.propDecidable

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
theorem targetLine_eq_of_success {M : MergedPairs F} {T : FourTuple F}
    {S : Line F} (h : SuccessfulOn M T S) : targetLine S.1 M T = S := by
  apply Prod.ext
  · rfl
  · exact h.2.2.2 0

omit [Field F] [Fintype F] in
theorem support_card_le (w : WitnessKey F) : (support w).card ≤ 6 := by
  have hT : (generatorSet w.1.1).card ≤ 4 := by
    simpa [generatorSet] using
      (Finset.card_image_le (s := Finset.univ) (f := w.1.1.generator))
  have he : ({w.2.1,w.2.2} : Finset (Direction F)).card ≤ 2 :=
    by simpa using (Finset.card_insert_le w.2.1 ({w.2.2} : Finset (Direction F)))
  exact (Finset.card_union_le _ _).trans (by omega)

theorem patternModel_count (g : Direction F) (M : MergedPairs F) :
    (patternModel g).count M = ((witnesses g M).card : ℝ) := by
  simp only [PatternModel.count, PatternModel.indicator, patternModel,
    witnesses, Set.indicator_apply, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem patternModel_support_card_le (g : Direction F) (w : WitnessKey F) :
    ((patternModel g).support w).card ≤ 6 := support_card_le w

attribute [local instance] OAI.Balanced.ExternalAssembly.externalModelMeasurableSpace
theorem patternModel_measure (g : Direction F) :
    (patternModel g).measure = (offsetLaw F).toMeasure :=
  TupleAlignment.rootPatternModel_measure g

theorem patternModel_fixedExpectation_exposed (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (f : MergedPairs F → ℝ) :
    (patternModel g).fixedExpectation D a f =
      ∫ M, f M ∂(CandidateExposure.exposedLaw D a).toMeasure :=
  TupleAlignment.rootPatternModel_fixedExpectation_exposed g D a f

end
end Balanced.ExternalAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_ExternalFreshGeneratorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ExternalAssembly

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateValidityWitness CandidateExposure
open ExposedOppositeSum ExposedExternalSum ExposedWitnessProbability
open ExposedExternalFresh FreshWitnessProbability
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem witness_probability_le_lines (g : Direction F) (w : WitnessKey F)
    (law : PMF (MergedPairs F)) :
    (law.toOuterMeasure (witnessEvent g w)).toReal ≤
      ∑ c : F, (law.toOuterMeasure
        (externalEvent w.1.1 (g,c) w.2.1 w.2.2 w.1.2.1 w.1.2.2)).toReal := by
  apply (real_probability_mono_support (E := witnessEvent g w)
    (G := {M | ∃ c : F, M ∈ externalEvent w.1.1 (g,c)
      w.2.1 w.2.2 w.1.2.1 w.1.2.2}) law ?_).trans
    (probability_exists_le_sum _ _)
  rintro M ⟨hw, _⟩
  obtain ⟨hs, _, _, _, _, _, _, x, hx, _, hd, he⟩ := hw
  exact ⟨lineEval g (tuplePoint M w.1.1 0), hs, x, hx, hd, he⟩

omit [Fintype F] in
theorem witness_probability_eq_zero_of_first_target (g : Direction F)
    (w : WitnessKey F) (h : w.2.1 = g) (law : PMF (MergedPairs F)) :
    (law.toOuterMeasure (witnessEvent g w)).toReal = 0 := by
  have he : witnessEvent g w = ∅ := by
    ext M
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hw
    exact hw.2.2.2.1 h
  rw [he]
  simp

omit [Fintype F] in
theorem witness_probability_eq_zero_of_second_generator (g : Direction F)
    (w : WitnessKey F) (h : w.2.2 ∈ generatorSet w.1.1)
    (law : PMF (MergedPairs F)) :
    (law.toOuterMeasure (witnessEvent g w)).toReal = 0 := by
  have he : witnessEvent g w = ∅ := by
    ext M
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hw
    exact hw.2.2.2.2.2.2.1 h
  rw [he]
  simp

theorem old_key_probability_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (w : WitnessKey F)
    (hT : w.1.1 ∈ freshTuples D) (hdD : w.2.1 ∈ D) :
    ((CandidateExposure.exposedLaw D a).toOuterMeasure (witnessEvent g w)).toReal ≤
      2 * (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  by_cases hd : w.2.1 = g
  · rw [witness_probability_eq_zero_of_first_target g w hd]
    positivity
  obtain ⟨hi, hf⟩ := (Finset.mem_filter.mp hT).2
  apply (witness_probability_le_lines g w _).trans
  calc
    _ ≤ ∑ _c : F, 2 * (Fintype.card F : ℝ)⁻¹ ^ 5 := by
      apply Finset.sum_le_sum
      intro c _
      exact successful_external_probability_le D a w.1.1 hi hf (g,c)
        w.2.1 hdD hd w.1.2.1
        (fun M x => PairWitness M w.2.2 x (tuplePoint M w.1.1 w.1.2.2))
    _ = _ := by
      have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

theorem old_fresh_key_probability_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (w : WitnessKey F)
    (hT : w.1.1 ∈ freshTuples D) (hdD : w.2.1 ∈ D) (heD : w.2.2 ∉ D) :
    ((CandidateExposure.exposedLaw D a).toOuterMeasure (witnessEvent g w)).toReal ≤
      4 * (Fintype.card F : ℝ)⁻¹ ^ 6 := by
  by_cases hd : w.2.1 = g
  · rw [witness_probability_eq_zero_of_first_target g w hd]
    positivity
  by_cases he : w.2.2 ∈ generatorSet w.1.1
  · rw [witness_probability_eq_zero_of_second_generator g w he]
    positivity
  obtain ⟨hi, hf⟩ := (Finset.mem_filter.mp hT).2
  apply (witness_probability_le_lines g w _).trans
  calc
    _ ≤ ∑ _c : F, 4 * (Fintype.card F : ℝ)⁻¹ ^ 7 := by
      apply Finset.sum_le_sum
      intro c _
      exact successful_external_fresh_probability_le D a w.1.1 hi hf (g,c)
        w.2.1 hdD hd w.2.2 heD he w.1.2.1 w.1.2.2
    _ = _ := by
      have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

theorem filter_freshGeneratorLabels (g : Direction F) (D E : Finset (Direction F))
    (M : MergedPairs F) :
    (freshGeneratorLabels D E).filter (fun w => M ∈ witnessEvent g w) =
      (witnesses g M).filter (fun w =>
        (∀ i, w.1.1.generator i ∉ D) ∧ w.2.1 ∈ D ∧ w.2.2 ∈ E) := by
  ext w
  have hi : M ∈ witnessEvent g w → Function.Injective w.1.1.generator := fun h => h.1.1
  simp only [freshGeneratorLabels, freshTuples, witnesses, Finset.mem_filter,
    Finset.mem_product, Finset.mem_univ, true_and, and_true]
  tauto

attribute [local instance] OAI.Balanced.ExternalAssembly.freshGeneratorMeasurableSpace
theorem freshGenerators_oldOld_integral_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (∫ M, (((witnesses g M).filter (fun w =>
      (∀ i, w.1.1.generator i ∉ D) ∧ w.2.1 ∈ D ∧ w.2.2 ∈ D)).card : ℝ)
      ∂(CandidateExposure.exposedLaw D a).toMeasure) ≤ 8192 * (D.card : ℝ)^2 := by
  simp_rw [← filter_freshGeneratorLabels]
  rw [integral_eventCount_eq_sum]
  calc
    _ ≤ ∑ _w ∈ freshGeneratorLabels D D, 2 * (Fintype.card F : ℝ)⁻¹ ^ 4 := by
      apply Finset.sum_le_sum
      intro w hw
      rcases Finset.mem_product.mp hw with ⟨hTi, hde⟩
      exact old_key_probability_le g D a w (Finset.mem_product.mp hTi).1
        (Finset.mem_product.mp hde).1
    _ = ((freshTuples D).card : ℝ) * 16 * (D.card : ℝ)^2 *
        (2 * (Fintype.card F : ℝ)⁻¹ ^ 4) := by
      simp only [Finset.sum_const, nsmul_eq_mul, freshGeneratorLabels,
        Finset.card_product, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ ≤ (256 * (Fintype.card F : ℝ)^4) * 16 * (D.card : ℝ)^2 *
        (2 * (Fintype.card F : ℝ)⁻¹ ^ 4) := by
      have hc : ((freshTuples D).card : ℝ) ≤ 256 * (Fintype.card F : ℝ)^4 := by
        exact_mod_cast freshTuples_card_le D
      gcongr
    _ = _ := by
      have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      field_simp
      ring

theorem freshGenerators_oldFresh_integral_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (∫ M, (((witnesses g M).filter (fun w =>
      (∀ i, w.1.1.generator i ∉ D) ∧ w.2.1 ∈ D ∧ w.2.2 ∉ D)).card : ℝ)
      ∂(CandidateExposure.exposedLaw D a).toMeasure) ≤ 32768 * (D.card : ℝ) / Fintype.card F := by
  let E : Finset (Direction F) := Finset.univ \ D
  have hE (e : Direction F) : e ∈ E ↔ e ∉ D := by simp [E]
  have hfilter (M : MergedPairs F) :
      (witnesses g M).filter (fun w =>
        (∀ i, w.1.1.generator i ∉ D) ∧ w.2.1 ∈ D ∧ w.2.2 ∉ D) =
      (freshGeneratorLabels D E).filter (fun w => M ∈ witnessEvent g w) := by
    rw [filter_freshGeneratorLabels]
    simp only [hE]
  simp_rw [hfilter]
  rw [integral_eventCount_eq_sum]
  have hc : ((freshTuples D).card : ℝ) ≤ 256 * (Fintype.card F : ℝ)^4 := by
    exact_mod_cast freshTuples_card_le D
  have he : (E.card : ℝ) ≤ 2 * Fintype.card F := by
    have hx := Finset.card_le_univ E
    have hq : 0 < Fintype.card F := Fintype.card_pos
    simp only [Direction, Fintype.card_option] at hx
    exact_mod_cast (show E.card ≤ 2 * Fintype.card F by omega)
  calc
    _ ≤ ∑ _w ∈ freshGeneratorLabels D E, 4 * (Fintype.card F : ℝ)⁻¹ ^ 6 := by
      apply Finset.sum_le_sum
      intro w hw
      rcases Finset.mem_product.mp hw with ⟨hTi, hde⟩
      exact old_fresh_key_probability_le g D a w (Finset.mem_product.mp hTi).1
        (Finset.mem_product.mp hde).1 ((hE _).mp (Finset.mem_product.mp hde).2)
    _ = ((freshTuples D).card : ℝ) * 16 * D.card * E.card *
        (4 * (Fintype.card F : ℝ)⁻¹ ^ 6) := by
      simp only [Finset.sum_const, nsmul_eq_mul, freshGeneratorLabels,
        Finset.card_product, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ ≤ (256 * (Fintype.card F : ℝ)^4) * 16 * D.card *
        (2 * Fintype.card F) * (4 * (Fintype.card F : ℝ)⁻¹ ^ 6) := by gcongr
    _ = _ := by
      have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      field_simp
      ring

theorem freshGenerators_firstOld_integral_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∫ M, (((witnesses g M).filter (fun w =>
      (∀ i, w.1.1.generator i ∉ D) ∧ w.2.1 ∈ D)).card : ℝ)
      ∂(CandidateExposure.exposedLaw D a).toMeasure) ≤
      8192 * (m : ℝ)^2 + 32768 * m := by
  have heq (M : MergedPairs F) :
      (((witnesses g M).filter (fun w =>
        (∀ i, w.1.1.generator i ∉ D) ∧ w.2.1 ∈ D)).card : ℝ) =
      (((witnesses g M).filter (fun w =>
        (∀ i, w.1.1.generator i ∉ D) ∧ w.2.1 ∈ D ∧ w.2.2 ∈ D)).card : ℝ) +
      (((witnesses g M).filter (fun w =>
        (∀ i, w.1.1.generator i ∉ D) ∧ w.2.1 ∈ D ∧ w.2.2 ∉ D)).card : ℝ) := by
    have hc := Finset.card_filter_add_card_filter_not
      (s := (witnesses g M).filter (fun w =>
        (∀ i, w.1.1.generator i ∉ D) ∧ w.2.1 ∈ D)) (fun w => w.2.2 ∈ D)
    simp only [Finset.filter_filter, and_assoc] at hc
    exact_mod_cast hc.symm
  simp_rw [heq]
  rw [integral_add Integrable.of_finite Integrable.of_finite]
  have hm : (D.card : ℝ) ≤ m := by exact_mod_cast hD
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  apply (add_le_add (freshGenerators_oldOld_integral_le g D a)
    (freshGenerators_oldFresh_integral_le g D a)).trans
  have hdiv : 32768 * (D.card : ℝ) / Fintype.card F ≤ 32768 * (D.card : ℝ) :=
    div_le_self (by positivity) hq
  apply (add_le_add le_rfl hdiv).trans
  gcongr

end
end Balanced.ExternalAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateOldExternalOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateOldExternal

noncomputable section
open scoped Classical BigOperators
open CandidateExposure CandidateValidityWitness CandidateExposedWitness PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem successfulOn_target {M : MergedPairs F} {g : Direction F} {T : FourTuple F}
    (hT : T ∈ eligibleTuples g) (hs : M ∈ successfulInDirection T g) :
    SuccessfulOn M T (targetLine M g T) := by
  obtain ⟨hinj, havoid⟩ := (Finset.mem_filter.mp hT).2
  obtain ⟨⟨c, hc⟩, hpoints⟩ := hs
  refine ⟨hinj, havoid, hpoints, ?_⟩
  intro i
  change lineEval g (tuplePoint M T i) = lineEval g (tuplePoint M T 0)
  exact (hc i).trans (hc 0).symm

theorem mem_oldOverlapWitnesses_iff (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) (T : FourTuple F) (i j : Fin 4) (d e : Direction F) (x : Point F) :
    (((T, (i,j)), (d,e)), x) ∈ oldOverlapWitnesses g D M ↔
      T ∈ eligibleTuples g ∧ 0 < (exposedTupleIndices T D).card ∧
      M ∈ successfulInDirection T g ∧ d ∈ D ∧ e ∈ D ∧
      IsExternalWitness M g T i j d e x := by
  simp only [oldOverlapWitnesses, oldOverlapKeys, Finset.product_eq_sprod,
    Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  tauto

theorem key_injective_on_oldOverlapWitnesses (g : Direction F)
    (D : Finset (Direction F)) (M : MergedPairs F) :
    Set.InjOn (Prod.fst : WitnessLabel F → WitnessKey F) (oldOverlapWitnesses g D M) := by
  rintro ⟨key, x⟩ hx ⟨key', y⟩ hy hkey
  change key = key' at hkey
  subst key'
  rcases key with ⟨⟨T, ⟨i,j⟩⟩, ⟨d,e⟩⟩
  rcases (mem_oldOverlapWitnesses_iff g D M T i j d e x).mp hx with
    ⟨hT, _, hs, _, _, hxline, hex, _, _, hd, _, _, _, hdx, _⟩
  rcases (mem_oldOverlapWitnesses_iff g D M T i j d e y).mp hy with
    ⟨_, _, _, _, _, hyline, _, _, _, _, _, _, _, hdy, _⟩
  have hxy := external_point_unique (successfulOn_target hT hs) hd i hxline hyline hex hdx hdy
  exact congrArg (fun z : Point F => (((T, (i,j)), (d,e)), z)) hxy

theorem card_oldOverlapWitnesses_le (g : Direction F)
    (D : Finset (Direction F)) (M : MergedPairs F) :
    (oldOverlapWitnesses g D M).card ≤
      16 * D.card ^ 2 * overlappingTupleCount g D M := by
  calc
    (oldOverlapWitnesses g D M).card ≤ (oldOverlapKeys g D M).card :=
      Finset.card_le_card_of_injOn Prod.fst
        (fun w hw => (Finset.mem_product.mp (Finset.mem_filter.mp hw).1).1)
        (key_injective_on_oldOverlapWitnesses g D M)
    _ = _ := by
      simp only [oldOverlapKeys, Finset.product_eq_sprod, Finset.card_product,
        Finset.card_univ, Fintype.card_prod, Fintype.card_fin, overlappingTupleCount]
      ring

theorem expected_oldOverlapWitnesses_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∑ M : MergedPairs F, (exposedLaw D a M).toReal *
      ((oldOverlapWitnesses g D M).card : ℝ)) ≤
      262144 * (m : ℝ)^2 * ((m : ℝ) + 1)^4 := by
  let : MeasurableSpace F := ⊤
  have hmean := conditional_overlappingTupleCount_le g D a m hD
  rw [PMF.integral_eq_sum] at hmean
  simp only [smul_eq_mul] at hmean
  have hcard (M : MergedPairs F) : ((oldOverlapWitnesses g D M).card : ℝ) ≤
      (16 * (m : ℝ)^2) * (overlappingTupleCount g D M : ℝ) := by
    exact_mod_cast (card_oldOverlapWitnesses_le g D M).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hD 2)))
  calc
    _ ≤ ∑ M : MergedPairs F, (exposedLaw D a M).toReal *
        ((16 * (m : ℝ)^2) * (overlappingTupleCount g D M : ℝ)) := by
      exact Finset.sum_le_sum (fun M _ =>
        mul_le_mul_of_nonneg_left (hcard M) ENNReal.toReal_nonneg)
    _ = (16 * (m : ℝ)^2) * ∑ M : MergedPairs F, (exposedLaw D a M).toReal *
        (overlappingTupleCount g D M : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M _
      ring
    _ ≤ (16 * (m : ℝ)^2) * (16384 * ((m : ℝ) + 1)^4) :=
      mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = _ := by ring

theorem keyWitnesses_eq_image (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) :
    (oldOverlapPrescriptions g D).filter (fun k => M ∈ keyEvent g k) =
      (oldOverlapWitnesses g D M).image Prod.fst := by
  ext k
  rcases k with ⟨⟨T, ⟨i,j⟩⟩, ⟨d,e⟩⟩
  constructor
  · intro hk
    rcases Finset.mem_filter.mp hk with ⟨hbase, hs, x, hx⟩
    have hb : T ∈ eligibleTuples g ∧ 0 < (exposedTupleIndices T D).card ∧
        d ∈ D ∧ e ∈ D := by
      simpa only [oldOverlapPrescriptions, Finset.product_eq_sprod, Finset.mem_product,
        Finset.mem_filter, Finset.mem_univ, and_true, and_assoc] using hbase
    exact Finset.mem_image.mpr ⟨(((T,(i,j)),(d,e)),x),
      (mem_oldOverlapWitnesses_iff g D M T i j d e x).mpr
        ⟨hb.1,hb.2.1,hs,hb.2.2.1,hb.2.2.2,hx⟩, rfl⟩
  · intro hk
    obtain ⟨⟨k,x⟩, hx, heq⟩ := Finset.mem_image.mp hk
    change k = ((T,(i,j)),(d,e)) at heq
    subst k
    obtain ⟨hT,hover,hs,hd,he,hw⟩ :=
      (mem_oldOverlapWitnesses_iff g D M T i j d e x).mp hx
    apply Finset.mem_filter.mpr
    refine ⟨?_, hs, x, hw⟩
    simp only [oldOverlapPrescriptions, Finset.product_eq_sprod, Finset.mem_product,
      Finset.mem_filter, Finset.mem_univ, and_true]
    exact ⟨⟨hT,hover⟩,hd,he⟩

theorem keyWitnesses_card (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) :
    ((oldOverlapPrescriptions g D).filter (fun k => M ∈ keyEvent g k)).card =
      (oldOverlapWitnesses g D M).card := by
  rw [keyWitnesses_eq_image]
  exact Finset.card_image_of_injOn (key_injective_on_oldOverlapWitnesses g D M)

end
end Balanced.CandidateOldExternal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_ExternalWitnessPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ExternalAssembly

noncomputable section
open scoped Classical BigOperators
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem filter_card_swapKey (g : Direction F) (M : MergedPairs F)
    (P : WitnessKey F → Prop) :
    ((witnesses g M).filter (fun w => P (swapKey w))).card =
      ((witnesses g M).filter P).card := by
  apply Finset.card_bij (fun w _ => swapKey w)
  · intro w hw
    obtain ⟨hw, hP⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨(swapKey_mem_witnesses g M w).mpr hw, hP⟩
  · intro w hw v hv h
    have h' := congrArg swapKey h
    simpa only [swapKey_swapKey] using h'
  · intro w hw
    obtain ⟨hw, hP⟩ := Finset.mem_filter.mp hw
    exact ⟨swapKey w, Finset.mem_filter.mpr
      ⟨(swapKey_mem_witnesses g M w).mpr hw, by simpa using hP⟩, by simp⟩

theorem card_le_bothFresh_add_twice_firstOld (g : Direction F)
    (M : MergedPairs F) (D : Finset (Direction F)) :
    (witnesses g M).card ≤
      ((witnesses g M).filter (fun w => w.2.1 ∉ D ∧ w.2.2 ∉ D)).card +
      2 * ((witnesses g M).filter (fun w => w.2.1 ∈ D)).card := by
  have hswap : ((witnesses g M).filter (fun w => w.2.2 ∈ D)).card =
      ((witnesses g M).filter (fun w => w.2.1 ∈ D)).card := by
    convert filter_card_swapKey g M (fun w => w.2.1 ∈ D) using 1 <;>
      congr 1 <;> symm <;> apply Finset.filter_congr_decidable
  have h : (witnesses g M).card ≤
      ((witnesses g M).filter (fun w => w.2.1 ∉ D ∧ w.2.2 ∉ D)).card +
      ((witnesses g M).filter (fun w => w.2.1 ∈ D)).card +
      ((witnesses g M).filter (fun w => w.2.2 ∈ D)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro w hw
    by_cases hd : w.2.1 ∈ D <;> by_cases he : w.2.2 ∈ D <;> simp [hd, he]
  omega

theorem firstOld_card_eq_three_cases (g : Direction F)
    (M : MergedPairs F) (D : Finset (Direction F)) (P : FourTuple F → Prop) :
    ((witnesses g M).filter (fun w => w.2.1 ∈ D)).card =
      ((witnesses g M).filter (fun w => w.2.1 ∈ D ∧ w.2.2 ∈ D ∧ P w.1.1)).card +
      ((witnesses g M).filter (fun w => w.2.1 ∈ D ∧ w.2.2 ∉ D ∧ P w.1.1)).card +
      ((witnesses g M).filter (fun w => w.2.1 ∈ D ∧ ¬ P w.1.1)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hd : w.2.1 ∈ D <;> by_cases he : w.2.2 ∈ D <;>
    by_cases hP : P w.1.1 <;> simp [hd, he, hP]

theorem card_le_four_cases (g : Direction F) (M : MergedPairs F)
    (D : Finset (Direction F)) (P : FourTuple F → Prop) :
    (witnesses g M).card ≤
      ((witnesses g M).filter (fun w => w.2.1 ∉ D ∧ w.2.2 ∉ D)).card + 2 *
      (((witnesses g M).filter (fun w => w.2.1 ∈ D ∧ w.2.2 ∈ D ∧ P w.1.1)).card +
       ((witnesses g M).filter (fun w => w.2.1 ∈ D ∧ w.2.2 ∉ D ∧ P w.1.1)).card +
       ((witnesses g M).filter (fun w => w.2.1 ∈ D ∧ ¬ P w.1.1)).card) := by
  rw [← firstOld_card_eq_three_cases]
  exact card_le_bothFresh_add_twice_firstOld g M D

open MeasureTheory

attribute [local instance] OAI.Balanced.ExternalAssembly.instMeasurableSpace_solutions
theorem integral_card_le_four_cases (g : Direction F)
    (D : Finset (Direction F)) (P : FourTuple F → Prop)
    (law : PMF (MergedPairs F)) :
    (∫ M, ((witnesses g M).card : ℝ) ∂law.toMeasure) ≤
      (∫ M, (((witnesses g M).filter
        (fun w => w.2.1 ∉ D ∧ w.2.2 ∉ D)).card : ℝ) ∂law.toMeasure) + 2 *
      ((∫ M, (((witnesses g M).filter
        (fun w => w.2.1 ∈ D ∧ w.2.2 ∈ D ∧ P w.1.1)).card : ℝ) ∂law.toMeasure) +
       (∫ M, (((witnesses g M).filter
        (fun w => w.2.1 ∈ D ∧ w.2.2 ∉ D ∧ P w.1.1)).card : ℝ) ∂law.toMeasure) +
       (∫ M, (((witnesses g M).filter
        (fun w => w.2.1 ∈ D ∧ ¬ P w.1.1)).card : ℝ) ∂law.toMeasure)) := by
  simp only [PMF.integral_eq_sum, smul_eq_mul]
  calc
    _ ≤ ∑ M : MergedPairs F, (law M).toReal *
        ((((witnesses g M).filter (fun w => w.2.1 ∉ D ∧ w.2.2 ∉ D)).card : ℝ) +
          2 * (((((witnesses g M).filter
            (fun w => w.2.1 ∈ D ∧ w.2.2 ∈ D ∧ P w.1.1)).card : ℝ)) +
            (((witnesses g M).filter
            (fun w => w.2.1 ∈ D ∧ w.2.2 ∉ D ∧ P w.1.1)).card : ℝ) +
            (((witnesses g M).filter
            (fun w => w.2.1 ∈ D ∧ ¬ P w.1.1)).card : ℝ))) := by
      apply Finset.sum_le_sum
      intro M hM
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      exact_mod_cast card_le_four_cases g M D P
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      simp only [mul_left_comm _ (2 : ℝ), ← Finset.mul_sum]

end
end Balanced.ExternalAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_ExternalWitnessOldBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ExternalAssembly

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateExposure CandidateValidityWitness PartialAlignment
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem oldOld_overlap_card_le (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) :
    ((witnesses g M).filter (fun w => w.2.1 ∈ D ∧ w.2.2 ∈ D ∧
      0 < (exposedTupleIndices w.1.1 D).card)).card ≤
      (CandidateOldExternal.oldOverlapWitnesses g D M).card := by
  rw [← CandidateOldExternal.keyWitnesses_card]
  apply Finset.card_le_card
  intro w hw
  rcases w with ⟨⟨T, i, j⟩, d, e⟩
  obtain ⟨hw, hdD, heD, hover⟩ := Finset.mem_filter.mp hw
  obtain ⟨hs, hij, hde, hd, he, hdT, heT, x, hx, hex, hdi, hej⟩ :=
    (mem_witnesses g M _).mp hw
  have hT : T ∈ eligibleTuples g :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.1, hs.2.1⟩
  have hsucc : M ∈ successfulInDirection T g :=
    ⟨⟨lineEval g (tuplePoint M T 0), hs.2.2.2⟩, hs.2.2.1⟩
  apply Finset.mem_filter.mpr
  constructor
  · simp only [CandidateOldExternal.oldOverlapPrescriptions, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_filter, Finset.mem_univ, and_true]
    exact ⟨⟨hT, hover⟩, hdD, heD⟩
  · exact ⟨hsucc, x, hx, hex, hij, hde, hd, he, hdT, heT, hdi, hej⟩

attribute [local instance] OAI.Balanced.ExternalAssembly.instMeasurableSpace_solutions_1
theorem oldOld_overlap_integral_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∫ M, (((witnesses g M).filter (fun w => w.2.1 ∈ D ∧ w.2.2 ∈ D ∧
      0 < (exposedTupleIndices w.1.1 D).card)).card : ℝ)
        ∂(exposedLaw D a).toMeasure) ≤ 262144 * (m : ℝ)^2 * ((m : ℝ) + 1)^4 := by
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  apply le_trans _ (CandidateOldExternal.expected_oldOverlapWitnesses_le g D a m hD)
  apply Finset.sum_le_sum
  intro M hM
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  exact_mod_cast oldOld_overlap_card_le g D M

end
end Balanced.ExternalAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FreshDoublePrescription
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FreshCoordinate

noncomputable section
open scoped Classical

variable {D A : Type*} [Fintype D] [Fintype A] [DecidableEq D] [Nonempty A]

theorem probability_two_prescriptions_on_subtype (d e : D) (hde : d ≠ e)
    (G E : (D → A) → Prop) [Nonempty {f : D → A // G f}]
    (b₁ b₂ : (D → A) → A)
    (hGd : ∀ f a, G (Function.update f d a) ↔ G f)
    (hGe : ∀ f a, G (Function.update f e a) ↔ G f)
    (hEd : ∀ f a, E (Function.update f d a) ↔ E f)
    (hEe : ∀ f a, E (Function.update f e a) ↔ E f)
    (hb₁d : ∀ f a, b₁ (Function.update f d a) = b₁ f)
    (hb₂d : ∀ f a, b₂ (Function.update f d a) = b₂ f)
    (hb₂e : ∀ f a, b₂ (Function.update f e a) = b₂ f) :
    ((PMF.uniformOfFintype {f : D → A // G f}).toOuterMeasure
      {f | E f.1 ∧ f.1 d = b₁ f.1 ∧ f.1 e = b₂ f.1}).toReal =
    ((PMF.uniformOfFintype {f : D → A // G f}).toOuterMeasure
      {f | E f.1}).toReal / (Fintype.card A : ℝ)^2 := by
  have h := probability_prescription_on_subtype d G
    (fun f => E f ∧ f e = b₂ f) b₁ hGd
    (by
      intro f a
      rw [hEd, Function.update_of_ne hde.symm, hb₂d]) hb₁d
  rw [probability_prescription_on_subtype e G E b₂ hGe hEe hb₂e] at h
  simpa only [and_assoc, and_left_comm, and_comm, div_div, pow_two] using h

end
end Balanced.FreshCoordinate

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_FreshExternalWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FreshExternalWitness

noncomputable section
open scoped Classical BigOperators
open FreshTupleWitness TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem two_prescriptions_on_subtype
    (d e : Direction F) (hde : d ≠ e)
    (G E : MergedPairs F → Prop) [Nonempty {M : MergedPairs F // G M}]
    (b c : MergedPairs F → Bool → F)
    (hGd : ∀ M v, G (Function.update M d v) ↔ G M)
    (hGe : ∀ M v, G (Function.update M e v) ↔ G M)
    (hEd : ∀ M v, E (Function.update M d v) ↔ E M)
    (hEe : ∀ M v, E (Function.update M e v) ↔ E M)
    (hbd : ∀ M v, b (Function.update M d v) = b M)
    (hbe : ∀ M v, b (Function.update M e v) = b M)
    (hce : ∀ M v, c (Function.update M e v) = c M) :
    ((PMF.uniformOfFintype {M : MergedPairs F // G M}).toOuterMeasure
      {M | (E M.1 ∧ M.1 d = b M.1) ∧ M.1 e = c M.1}).toReal =
    ((PMF.uniformOfFintype {M : MergedPairs F // G M}).toOuterMeasure
      {M | E M.1}).toReal / (Fintype.card F : ℝ)^4 := by
  have h := FreshCoordinate.probability_two_prescriptions_on_subtype e d hde.symm
    G E c b hGe hGd hEe hEd hce hbe hbd
  have hcard : (Fintype.card (Bool → F) : ℝ)^2 = (Fintype.card F : ℝ)^4 := by
    simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow]
    ring
  rw [hcard] at h
  simpa only [and_assoc, and_left_comm, and_comm] using h

omit [Fintype F] in
theorem targetPoint_update_fresh (g : Direction F) (T : FourTuple F)
    (z : F) (d : Direction F) (hd : ∀ i, T.generator i ≠ d)
    (M : MergedPairs F) (v : Bool → F) :
    targetPoint g T z (Function.update M d v) = targetPoint g T z M := by
  unfold targetPoint
  rw [tuplePoint_update_fresh T d hd]

omit [Fintype F] [DecidableEq F] in
theorem exists_targetPoint (g : Direction F) (T : FourTuple F)
    (M : MergedPairs F) (x : Point F)
    (hx : OnLine x (g, lineEval g (tuplePoint M T 0))) :
    ∃ z, targetPoint g T z M = x := by
  refine ⟨linePointsEquiv (g, lineEval g (tuplePoint M T 0)) ⟨x, hx⟩, ?_⟩
  exact congrArg Subtype.val ((linePointsEquiv
    (g, lineEval g (tuplePoint M T 0))).symm_apply_apply ⟨x, hx⟩)

theorem orientedEvent_probability_eq
    (G : MergedPairs F → Prop) [Nonempty {M : MergedPairs F // G M}]
    (g : Direction F) (T : FourTuple F) (d e : Direction F)
    (hde : d ≠ e) (hd : ∀ k, T.generator k ≠ d)
    (he : ∀ k, T.generator k ≠ e)
    (hGd : ∀ M v, G (Function.update M d v) ↔ G M)
    (hGe : ∀ M v, G (Function.update M e v) ↔ G M)
    (i j : Fin 4) (σ τ : Bool) (z : F) :
    ((PMF.uniformOfFintype {M : MergedPairs F // G M}).toOuterMeasure
      {M | orientedEvent g T d e i j σ τ z M.1}).toReal =
      fiberSuccessProbability G g T / (Fintype.card F : ℝ)^4 := by
  have h := two_prescriptions_on_subtype d e hde G
    (fun M => (∃ c, ∀ k, OnLine (tuplePoint M T k) (g,c)) ∧
      Function.Injective (tuplePoint M T))
    (fun M => pairPrescription d (targetPoint g T z M) (tuplePoint M T i) σ)
    (fun M => pairPrescription e (targetPoint g T z M) (tuplePoint M T j) τ)
    hGd hGe
    (by intro M v; rw [tuplePoint_update_fresh T d hd])
    (by intro M v; rw [tuplePoint_update_fresh T e he])
    (by intro M v; rw [targetPoint_update_fresh g T z d hd,
      tuplePoint_update_fresh T d hd])
    (by intro M v; rw [targetPoint_update_fresh g T z e he,
      tuplePoint_update_fresh T e he])
    (by intro M v; rw [targetPoint_update_fresh g T z e he,
      tuplePoint_update_fresh T e he])
  simp_rw [pairPrescription_iff] at h
  exact h

theorem fixedFiber_probability_eq (D : Finset (Direction F)) (a : MergedPairs F)
    (E : Set (MergedPairs F)) :
    ((PMF.uniformOfFintype {M : MergedPairs F // fixedValues D a M}).toOuterMeasure
      {M | M.1 ∈ E}).toReal = CandidateExposure.conditionalProbability D a E := by
  unfold CandidateExposure.conditionalProbability CandidateExposure.exposedLaw
  simp only [PartialAlignment.offsetLaw_eq_uniform]
  rw [ConditionalRestriction.uniform_fixed_filter, PMF.toOuterMeasure_map_apply]
  exact FiniteUniformFibers.probability_fintype_congr _ _ rfl

theorem sum_fiberSuccessProbability_eq (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (∑ r : RootPrescription g, fiberSuccessProbability (fixedValues D a) g r.tuple) =
      CandidateExposure.successProbabilitySum g D a := by
  have hp (T : FourTuple F) : fiberSuccessProbability (fixedValues D a) g T =
      CandidateExposure.conditionalProbability D a
        (CandidateExposure.successfulInDirection T g) := by
    unfold fiberSuccessProbability
    calc
      _ = ((PMF.uniformOfFintype {M : MergedPairs F // fixedValues D a M}).toOuterMeasure
          {M | M.1 ∈ CandidateExposure.successfulInDirection T g}).toReal :=
        FiniteUniformFibers.probability_fintype_congr _ _ rfl
      _ = _ := fixedFiber_probability_eq D a (CandidateExposure.successfulInDirection T g)
  simp_rw [hp]
  let f : FourTuple F → ℝ := fun T => CandidateExposure.conditionalProbability D a
    (CandidateExposure.successfulInDirection T g)
  have he := Equiv.sum_comp (CandidateExposure.eligibleTupleEquivRootPrescription g)
    (fun r => f r.tuple)
  simp only [CandidateExposure.equivRootPrescription_tuple] at he
  have hs := Finset.sum_subtype (CandidateExposure.eligibleTuples g)
    (p := fun T => T ∈ CandidateExposure.eligibleTuples g)
    (F := inferInstance) (fun _ => Iff.rfl) f
  exact (hs.trans he).symm

end
end Balanced.FreshExternalWitness

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_FreshExternalCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FreshExternalWitness

noncomputable section
open scoped Classical BigOperators
open FreshTupleWitness TupleAlignment CandidateExposure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem orientedEvent_conditional_probability_eq
    (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F)
    (T : FourTuple F) (de : Direction F × Direction F)
    (hde : de ∈ freshPairs D T) (i j : Fin 4) (σ τ : Bool) (z : F) :
    conditionalProbability D a {M | orientedEvent g T de.1 de.2 i j σ τ z M} =
      fiberSuccessProbability (fixedValues D a) g T / (Fintype.card F : ℝ)^4 := by
  obtain ⟨hne, hdD, heD, hd, he⟩ := (mem_freshPairs D T de).mp hde
  have h := orientedEvent_probability_eq (fixedValues D a) g T de.1 de.2 hne hd he
    (fixed_coordinates_update_invariant (fun d => d ∈ D) a de.1 hdD)
    (fixed_coordinates_update_invariant (fun d => d ∈ D) a de.2 heD) i j σ τ z
  calc
    _ = ((PMF.uniformOfFintype {M : MergedPairs F // fixedValues D a M}).toOuterMeasure
        {M | M.1 ∈ {N | orientedEvent g T de.1 de.2 i j σ τ z N}}).toReal :=
      (fixedFiber_probability_eq D a _).symm
    _ = _ := by
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      exact FiniteUniformFibers.probability_fintype_congr _ _ rfl

theorem tuple_probabilitySum_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (T : FourTuple F) (i j : Fin 4) :
    (∑ de ∈ freshPairs D T, ∑ σ : Bool, ∑ τ : Bool, ∑ z : F,
      conditionalProbability D a {M | orientedEvent g T de.1 de.2 i j σ τ z M}) ≤
      (16 / Fintype.card F : ℝ) * fiberSuccessProbability (fixedValues D a) g T := by
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos (α := F)
  have hUcard : ((freshPairs D T).card : ℝ) ≤ ((Fintype.card F : ℝ) + 1)^2 := by
    have h := Finset.card_le_univ (freshPairs D T)
    simp only [Fintype.card_prod, Direction, Fintype.card_option] at h
    rw [pow_two]
    exact_mod_cast h
  have hUm : ((freshPairs D T).card : ℝ) ≤ 4 * (Fintype.card F : ℝ)^2 := by
    nlinarith [sq_nonneg ((Fintype.card F : ℝ) - 1)]
  have hp : 0 ≤ fiberSuccessProbability (fixedValues D a) g T := ENNReal.toReal_nonneg
  calc
    _ = ∑ _de ∈ freshPairs D T, ∑ _σ : Bool, ∑ _τ : Bool, ∑ _z : F,
        fiberSuccessProbability (fixedValues D a) g T / (Fintype.card F : ℝ)^4 := by
      apply Finset.sum_congr rfl
      intro de hde
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro τ _
      apply Finset.sum_congr rfl
      intro z _
      exact orientedEvent_conditional_probability_eq g D a T de hde i j σ τ z
    _ = 4 * ((freshPairs D T).card : ℝ) * Fintype.card F *
        fiberSuccessProbability (fixedValues D a) g T / (Fintype.card F : ℝ)^4 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
      ring
    _ ≤ 4 * (4 * (Fintype.card F : ℝ)^2) * Fintype.card F *
        fiberSuccessProbability (fixedValues D a) g T / (Fintype.card F : ℝ)^4 := by gcongr
    _ = _ := by field_simp; ring

theorem probabilitySum_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) (i j : Fin 4) :
    probabilitySum g D a i j ≤ (327680 * (m + 1)^4 : ℝ) := by
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ ∑ r : RootPrescription g,
        (16 / Fintype.card F : ℝ) *
          fiberSuccessProbability (fixedValues D a) g r.tuple := by
      apply Finset.sum_le_sum
      intro r _
      exact tuple_probabilitySum_le g D a r.tuple i j
    _ = (16 / Fintype.card F : ℝ) * successProbabilitySum g D a := by
      rw [← Finset.mul_sum, sum_fiberSuccessProbability_eq]
    _ ≤ (16 / Fintype.card F : ℝ) *
        ((20480 * (m + 1)^4 : ℝ) * Fintype.card F) := by
      apply mul_le_mul_of_nonneg_left (successProbabilitySum_le g D a m hD)
      positivity
    _ = _ := by field_simp; ring

theorem all_positions_probabilitySum_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∑ i : Fin 4, ∑ j : Fin 4, probabilitySum g D a i j) ≤
      (5242880 * (m + 1)^4 : ℝ) := by
  calc
    _ ≤ ∑ _i : Fin 4, ∑ _j : Fin 4, (327680 * (m + 1)^4 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact probabilitySum_le g D a m hD i j
    _ = _ := by simp; ring

end
end Balanced.FreshExternalWitness

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_FreshExternalCountBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FreshExternalWitness

noncomputable section
open scoped Classical BigOperators
open TupleAlignment CandidateExposure CandidateValidityWitness MeasureTheory

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
theorem sourceEvent_iff_witnessEvent (g : Direction F) (T : FourTuple F)
    (i j : Fin 4) (de : Direction F × Direction F) (M : MergedPairs F) :
    sourceEvent g T i j de M ↔
      M ∈ ExternalAssembly.witnessEvent g ((T, (i,j)), de) := by
  constructor
  · rintro ⟨c, x, hs, hx, hex, hij, hd, he, hdi, hej⟩
    have hline : ExternalAssembly.targetLine g M T = (g,c) :=
      ExternalAssembly.targetLine_eq_of_success hs
    have hde := external_witness_directions_distinct hs hx hex hij hd hdi hej
    have hdT := external_witness_not_generator hs hx hex hdi
    have heT := external_witness_not_generator hs hx hex hej
    simp only [ExternalAssembly.witnessEvent, Set.mem_ofPred_eq, hline]
    exact ⟨hs, hij, hde, hd, he, hdT, heT, x, hx, hex, hdi, hej⟩
  · rintro ⟨hs, hij, _, hd, he, _, _, x, hx, hex, hdi, hej⟩
    exact ⟨lineEval g (tuplePoint M T 0), x, hs, hx, hex, hij, hd, he, hdi, hej⟩

theorem sourceEvent_eligible (g : Direction F) (T : FourTuple F)
    (i j : Fin 4) (de : Direction F × Direction F) (M : MergedPairs F)
    (h : sourceEvent g T i j de M) : T ∈ eligibleTuples g := by
  obtain ⟨c, x, hs, _⟩ := h
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.1, hs.2.1⟩

theorem sourceEvent_freshPairs_iff (g : Direction F) (D : Finset (Direction F))
    (T : FourTuple F) (i j : Fin 4) (de : Direction F × Direction F)
    (M : MergedPairs F) (h : sourceEvent g T i j de M) :
    de ∈ freshPairs D T ↔ de.1 ∉ D ∧ de.2 ∉ D := by
  have hw := (sourceEvent_iff_witnessEvent g T i j de M).mp h
  obtain ⟨_, _, hde, _, _, hdT, heT, _⟩ := hw
  have hdf : ∀ k, T.generator k ≠ de.1 := by
    intro k hk
    exact hdT (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩)
  have hef : ∀ k, T.generator k ≠ de.2 := by
    intro k hk
    exact heT (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩)
  rw [mem_freshPairs]
  constructor
  · intro hmem
    exact ⟨hmem.2.1, hmem.2.2.1⟩
  · rintro ⟨hdD, heD⟩
    exact ⟨hde, hdD, heD, hdf, hef⟩

omit [Fintype F] in
theorem sourceEvent_has_orientedEvent (g : Direction F) (T : FourTuple F)
    (i j : Fin 4) (de : Direction F × Direction F) (M : MergedPairs F)
    (h : sourceEvent g T i j de M) :
    ∃ σ τ z, orientedEvent g T de.1 de.2 i j σ τ z M := by
  obtain ⟨c, x, hs, hx, _, _, _, _, hdi, hej⟩ := h
  have hc : lineEval g (tuplePoint M T 0) = c := hs.2.2.2 0
  have hx' : OnLine x (g, lineEval g (tuplePoint M T 0)) := by
    simpa only [hc] using hx
  obtain ⟨z, hz⟩ := exists_targetPoint g T M x hx'
  obtain ⟨σ, hσ⟩ := hdi
  obtain ⟨τ, hτ⟩ := hej
  refine ⟨σ, τ, z, ?_⟩
  unfold orientedEvent
  rw [hz]
  exact ⟨⟨⟨⟨c, hs.2.2.2⟩, hs.2.2.1⟩, hσ⟩, hτ⟩

private theorem outerProbability_mono {Ω : Type*} (p : PMF Ω)
    {E H : Set Ω} (h : E ⊆ H) :
    (p.toOuterMeasure E).toReal ≤ (p.toOuterMeasure H).toReal := by
  apply ENNReal.toReal_mono
  · rw [PMF.toOuterMeasure_apply]
    exact p.tsum_coe_indicator_ne_top H
  · exact p.toOuterMeasure_mono (fun _ hx => h hx.1)

theorem sourceEvent_probability_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (T : FourTuple F) (i j : Fin 4)
    (de : Direction F × Direction F) :
    conditionalProbability D a {M | sourceEvent g T i j de M} ≤
      ∑ σ : Bool, ∑ τ : Bool, ∑ z : F,
        conditionalProbability D a {M | orientedEvent g T de.1 de.2 i j σ τ z M} := by
  let E : (Bool × Bool × F) → Set (MergedPairs F) :=
    fun s => {M | orientedEvent g T de.1 de.2 i j s.1 s.2.1 s.2.2 M}
  have hsub : {M | sourceEvent g T i j de M} ⊆ {M | ∃ s, M ∈ E s} := by
    intro M hM
    obtain ⟨σ, τ, z, hz⟩ := sourceEvent_has_orientedEvent g T i j de M hM
    exact ⟨(σ, τ, z), hz⟩
  calc
    _ ≤ ((exposedLaw D a).toOuterMeasure {M | ∃ s, M ∈ E s}).toReal :=
      outerProbability_mono _ hsub
    _ ≤ ∑ s, ((exposedLaw D a).toOuterMeasure (E s)).toReal :=
      FreshWitnessProbability.probability_exists_le_sum _ E
    _ = _ := by simp only [Fintype.sum_prod_type, E, conditionalProbability]

theorem sourceProbabilitySum_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    sourceProbabilitySum g D a ≤ (5242880 * (m + 1)^4 : ℝ) := by
  apply le_trans _ (all_positions_probabilitySum_le g D a m hD)
  unfold sourceProbabilitySum probabilitySum
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro r _
  apply Finset.sum_le_sum
  intro de _
  exact sourceEvent_probability_le g D a r.tuple i j de

omit [Field F] in
private theorem sum_roots_eq_all (g : Direction F) (f : FourTuple F → ℕ)
    (hf : ∀ T, T ∉ eligibleTuples g → f T = 0) :
    (∑ r : RootPrescription g, f r.tuple) = ∑ T : FourTuple F, f T := by
  have he := Equiv.sum_comp (eligibleTupleEquivRootPrescription g)
    (fun r => f r.tuple)
  simp only [equivRootPrescription_tuple] at he
  have hs := Finset.sum_subtype (eligibleTuples g)
    (p := fun T => T ∈ eligibleTuples g)
    (F := inferInstance) (fun _ => Iff.rfl) f
  calc
    _ = ∑ T ∈ eligibleTuples g, f T := (hs.trans he).symm
    _ = ∑ T : FourTuple F, f T := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro T _ hT
      exact hf T hT

private theorem sourceLabelCount_eq (g : Direction F) (D : Finset (Direction F))
    (T : FourTuple F) (i j : Fin 4) (M : MergedPairs F) :
    ((freshPairs D T).filter (fun de => sourceEvent g T i j de M)).card =
      ∑ de : Direction F × Direction F,
        if sourceEvent g T i j de M ∧ de.1 ∉ D ∧ de.2 ∉ D then 1 else 0 := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, freshPairs]
  apply Finset.sum_congr rfl
  intro de _
  by_cases hs : sourceEvent g T i j de M
  · have hmem := sourceEvent_freshPairs_iff g D T i j de M hs
    rw [mem_freshPairs] at hmem
    simp only [hs, ite_true, true_and, hmem]
  · simp only [hs, ite_false, false_and]
    split <;> rfl

theorem canonical_fresh_count_eq (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) :
    ((ExternalAssembly.witnesses g M).filter
      (fun w => w.2.1 ∉ D ∧ w.2.2 ∉ D)).card = sourceWitnessCount g D M := by
  unfold sourceWitnessCount
  have hs (i j : Fin 4) :
      (∑ r : RootPrescription g,
        ((freshPairs D r.tuple).filter
          (fun de => sourceEvent g r.tuple i j de M)).card) =
      ∑ T : FourTuple F,
        ((freshPairs D T).filter (fun de => sourceEvent g T i j de M)).card := by
    apply sum_roots_eq_all g (fun T =>
      ((freshPairs D T).filter (fun de => sourceEvent g T i j de M)).card)
    intro T hT
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro de _ hs
    exact hT (sourceEvent_eligible g T i j de M hs)
  simp_rw [hs, sourceLabelCount_eq]
  simp only [ExternalAssembly.witnesses, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [← sourceEvent_iff_witnessEvent, ite_and]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

section Measurable
variable [MeasurableSpace F] [MeasurableSingletonClass F]

theorem integral_sourceWitnessCount (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) :
    (∫ M, (sourceWitnessCount g D M : ℝ) ∂(exposedLaw D a).toMeasure) =
      sourceProbabilitySum g D a := by
  simp only [sourceWitnessCount, Nat.cast_sum]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  unfold sourceProbabilitySum
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro r _
  exact integral_eventCount_eq_sum (exposedLaw D a) (freshPairs D r.tuple)
    (fun de => {M | sourceEvent g r.tuple i j de M})

theorem sourceWitnessCount_mean_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∫ M, (sourceWitnessCount g D M : ℝ) ∂(exposedLaw D a).toMeasure) ≤
      (5242880 * (m + 1)^4 : ℝ) := by
  rw [integral_sourceWitnessCount]
  exact sourceProbabilitySum_le g D a m hD

theorem canonical_fresh_count_integral_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ)
    (hD : D.card ≤ m) :
    (∫ M, (((ExternalAssembly.witnesses g M).filter
      (fun w => w.2.1 ∉ D ∧ w.2.2 ∉ D)).card : ℝ)
      ∂(exposedLaw D a).toMeasure) ≤ (5242880 * (m + 1)^4 : ℝ) := by
  simp_rw [canonical_fresh_count_eq]
  exact sourceWitnessCount_mean_le g D a m hD

end Measurable
end
end Balanced.FreshExternalWitness

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FreshRandomWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators
attribute [local instance] Classical.propDecidable

namespace Balanced.FreshRandomWitness

open FreshWitnessProbability FreshTupleWitness CandidateValidityWitness

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem exposedLaw_eq_uniform_fiber (D : Finset (Direction F)) (a : MergedPairs F) :
    exposedLaw D a =
      (PMF.uniformOfFintype
        (ConditionalRestriction.FixedArray (fun d => d ∈ D) a)).map Subtype.val := by
  simp only [exposedLaw, PartialAlignment.offsetLaw_eq_uniform]
  exact @Balanced.uniform_filter_eq_subtype_map (MergedPairs F) inferInstance inferInstance
    {M | ∀ d, d ∈ D → M d = a d}
    (inferInstance : Fintype (ConditionalRestriction.FixedArray (fun d => d ∈ D) a))
    (inferInstance : Nonempty (ConditionalRestriction.FixedArray (fun d => d ∈ D) a))
    ⟨a, by intro d hd; rfl, PMF.mem_support_uniformOfFintype _⟩

theorem prescription_probability (D : Finset (Direction F)) (a : MergedPairs F)
    (d : Direction F) (hd : d ∉ D)
    (E : MergedPairs F → Prop) (b : MergedPairs F → Bool → F)
    (hE : ∀ M v, E (Function.update M d v) ↔ E M)
    (hb : ∀ M v, b (Function.update M d v) = b M) :
    ((exposedLaw D a).toOuterMeasure {M | E M ∧ M d = b M}).toReal =
      ((exposedLaw D a).toOuterMeasure {M | E M}).toReal /
        (Fintype.card F : ℝ)^2 := by
  rw [exposedLaw_eq_uniform_fiber]
  simp only [PMF.toOuterMeasure_map_apply]
  have h := FreshCoordinate.probability_prescription_on_subtype d
    (fun M : MergedPairs F => ∀ t, t ∈ D → M t = a t) E b
    (fixed_coordinates_update_invariant (fun t => t ∈ D) a d hd) hE hb
  change ((PMF.uniformOfFintype
    (ConditionalRestriction.FixedArray (fun t => t ∈ D) a)).toOuterMeasure
      {M | E M.val ∧ M.val d = b M.val}).toReal =
    ((PMF.uniformOfFintype
    (ConditionalRestriction.FixedArray (fun t => t ∈ D) a)).toOuterMeasure
      {M | E M.val}).toReal / (Fintype.card F : ℝ)^2
  have hcard : (Fintype.card (Bool → F) : ℝ) = (Fintype.card F : ℝ)^2 := by
    simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow]
  rw [hcard] at h
  simpa only [PMF.toOuterMeasure_uniformOfFintype_apply, Fintype.card_eq_nat_card] using h

theorem oriented_pair_probability (D : Finset (Direction F)) (a : MergedPairs F)
    (d : Direction F) (hd : d ∉ D) (E : MergedPairs F → Prop)
    (x y : MergedPairs F → Point F) (σ : Bool)
    (hE : ∀ M v, E (Function.update M d v) ↔ E M)
    (hx : ∀ M v, x (Function.update M d v) = x M)
    (hy : ∀ M v, y (Function.update M d v) = y M) :
    ((exposedLaw D a).toOuterMeasure {M | E M ∧
      OnLine (x M) (constituent M d σ) ∧
      OnLine (y M) (constituent M d (!σ))}).toReal =
      ((exposedLaw D a).toOuterMeasure {M | E M}).toReal /
        (Fintype.card F : ℝ)^2 := by
  have h := prescription_probability D a d hd E
    (fun M => pairPrescription d (x M) (y M) σ) hE
    (by intro M v; rw [hx, hy])
  simpa only [pairPrescription_iff] using h

end Balanced.FreshRandomWitness

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateMixedExternal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateMixedExternal

noncomputable section
open scoped Classical BigOperators
open CandidateExposure CandidateValidityWitness CandidateExposedWitness
open FreshTupleWitness

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
theorem successful_on_tupleTarget {g : Direction F} {T : FourTuple F}
    {M : MergedPairs F} (h : M ∈ successfulInDirection T g) :
    ∀ i, OnLine (tuplePoint M T i) (tupleTarget g T M) := by
  obtain ⟨⟨c, hc⟩, _⟩ := h
  intro i
  exact (hc i).trans (hc 0).symm

omit [Fintype F] in
theorem mixedExternalEvent_forces {g : Direction F} {T : FourTuple F}
    {a M : MergedPairs F} {d e : Direction F} {i j : Fin 4}
    (hd : d ≠ g) (hDa : M d = a d)
    (h : M ∈ mixedExternalEvent g T d e i j) :
    ∃ s : Bool × Bool, M ∈ forcedFreshEvent g T a d e j s.1 s.2 := by
  obtain ⟨hS, x, hx, _, _, ⟨σ, hxd, _⟩, ⟨τ, hxe, hje⟩⟩ := h
  have hxa : OnLine x (constituent a d σ) := by
    simpa only [constituent, hDa] using hxd
  have hforced : x = forcedPoint a (tupleTarget g T M) d σ :=
    eq_forcedPoint hd hx hxa
  exact ⟨(σ, τ), hS, hforced ▸ hxe, hje⟩

theorem forcedFreshEvent_probability
    (g : Direction F) (T : FourTuple F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (d e : Direction F) (heD : e ∉ D)
    (heT : ∀ k, T.generator k ≠ e) (j : Fin 4) (σ τ : Bool) :
    conditionalProbability D a (forcedFreshEvent g T a d e j σ τ) =
      conditionalProbability D a (successfulInDirection T g) /
        (Fintype.card F : ℝ)^2 := by
  apply FreshRandomWitness.oriented_pair_probability D a e heD
    (fun M => M ∈ successfulInDirection T g)
    (fun M => forcedPoint a (tupleTarget g T M) d σ)
    (fun M => tuplePoint M T j) τ
  · intro M v
    simp only [successfulInDirection, alignedInDirection, Set.mem_ofPred_eq,
      tuplePoint_update_fresh T e heT]
  · intro M v
    simp only [tupleTarget, tuplePoint_update_fresh T e heT]
  · intro M v
    rw [tuplePoint_update_fresh T e heT]

theorem mixedExternalEvent_probability_le
    (g : Direction F) (T : FourTuple F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (d e : Direction F) (hdD : d ∈ D) (hdg : d ≠ g)
    (heD : e ∉ D) (heT : ∀ k, T.generator k ≠ e) (i j : Fin 4) :
    conditionalProbability D a (mixedExternalEvent g T d e i j) ≤
      4 * conditionalProbability D a (successfulInDirection T g) /
        (Fintype.card F : ℝ)^2 := by
  let E (s : Bool × Bool) := forcedFreshEvent g T a d e j s.1 s.2
  have hmono : conditionalProbability D a (mixedExternalEvent g T d e i j) ≤
      conditionalProbability D a {M | ∃ s, M ∈ E s} := by
    apply ENNReal.toReal_mono
    · rw [PMF.toOuterMeasure_apply]
      exact (exposedLaw D a).tsum_coe_indicator_ne_top _
    · apply PMF.toOuterMeasure_mono
      rintro M ⟨hM, hs⟩
      have hfixed : ∀ t, t ∈ D → M t = a t :=
        (PMF.mem_support_filter_iff
          (PartialAlignment.canonical_exposure_supported D a)).mp hs |>.1
      exact mixedExternalEvent_forces hdg (hfixed d hdD) hM
  calc
    _ ≤ conditionalProbability D a {M | ∃ s, M ∈ E s} := hmono
    _ ≤ ∑ s : Bool × Bool, conditionalProbability D a (E s) :=
      FreshWitnessProbability.probability_exists_le_sum (exposedLaw D a) E
    _ = ∑ _s : Bool × Bool,
        conditionalProbability D a (successfulInDirection T g) /
          (Fintype.card F : ℝ)^2 := by
      apply Finset.sum_congr rfl
      intro s _
      exact forcedFreshEvent_probability g T D a d e heD heT j s.1 s.2
    _ = _ := by simp; ring

theorem sum_freshWitness_probability_le
    (g : Direction F) (T : FourTuple F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (d : Direction F) (hdD : d ∈ D) (hdg : d ≠ g) :
    (∑ e ∈ freshWitnessDirections g T D, ∑ i : Fin 4, ∑ j : Fin 4,
      conditionalProbability D a (mixedExternalEvent g T d e i j)) ≤
      128 * conditionalProbability D a (successfulInDirection T g) /
        (Fintype.card F : ℝ) := by
  let p := conditionalProbability D a (successfulInDirection T g)
  have hp : 0 ≤ p := ENNReal.toReal_nonneg
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos (α := F)
  have hcard : ((freshWitnessDirections g T D).card : ℝ) ≤
      (Fintype.card F : ℝ) + 1 := by
    exact_mod_cast (show (freshWitnessDirections g T D).card ≤ Fintype.card F + 1 by
      simpa only [Direction, Fintype.card_option] using
        Finset.card_le_univ (freshWitnessDirections g T D))
  calc
    _ ≤ ∑ _e ∈ freshWitnessDirections g T D, ∑ _i : Fin 4, ∑ _j : Fin 4,
        4 * p / (Fintype.card F : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro e he
      have he' := (Finset.mem_filter.mp he).2
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply mixedExternalEvent_probability_le g T D a d e hdD hdg he'.1
      intro k hk
      exact he'.2.2 (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩)
    _ = ((freshWitnessDirections g T D).card : ℝ) *
        (64 * p / (Fintype.card F : ℝ)^2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ ((Fintype.card F : ℝ) + 1) *
        (64 * p / (Fintype.card F : ℝ)^2) := by gcongr
    _ ≤ 128 * p / (Fintype.card F : ℝ) := by
      apply (le_div_iff₀ hq).mpr
      have hq0 := ne_of_gt hq
      field_simp
      nlinarith [mul_nonneg hp (sub_nonneg.mpr hq1)]

theorem mixedExternalProbabilitySum_le_overlap
    (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F) :
    mixedExternalProbabilitySum g D a ≤
      (128 * (D.card : ℝ) / Fintype.card F) * overlapProbabilitySum g D a := by
  unfold mixedExternalProbabilitySum overlapProbabilitySum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro T hT
  have hp : 0 ≤ conditionalProbability D a (successfulInDirection T g) :=
    ENNReal.toReal_nonneg
  calc
    _ ≤ ∑ _d ∈ oldWitnessDirections g T D,
        128 * conditionalProbability D a (successfulInDirection T g) /
          (Fintype.card F : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd' := Finset.mem_filter.mp hd
      exact sum_freshWitness_probability_le g T D a d hd'.1 hd'.2.1
    _ = ((oldWitnessDirections g T D).card : ℝ) *
        (128 * conditionalProbability D a (successfulInDirection T g) /
          (Fintype.card F : ℝ)) := by simp
    _ ≤ (D.card : ℝ) *
        (128 * conditionalProbability D a (successfulInDirection T g) /
          (Fintype.card F : ℝ)) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Finset.card_filter_le D (fun d => d ≠ g ∧ d ∉ generatorSet T)
      · positivity
    _ = _ := by ring

theorem mixedExternalProbabilitySum_le
    (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m) :
    mixedExternalProbabilitySum g D a ≤
      2097152 * ((m : ℝ) + 1)^5 / (Fintype.card F : ℝ) := by
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcard : (D.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast (by omega : D.card ≤ m + 1)
  calc
    _ ≤ (128 * (D.card : ℝ) / Fintype.card F) * overlapProbabilitySum g D a :=
      mixedExternalProbabilitySum_le_overlap g D a
    _ ≤ (128 * (D.card : ℝ) / Fintype.card F) * (16384 * ((m : ℝ) + 1)^4) := by
      apply mul_le_mul_of_nonneg_left (overlapProbabilitySum_le g D a m hD)
      positivity
    _ ≤ (128 * ((m : ℝ) + 1) / Fintype.card F) *
        (16384 * ((m : ℝ) + 1)^4) := by gcongr
    _ = _ := by ring

end
end Balanced.CandidateMixedExternal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_MixedExternalAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateMixedExternal

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateExposure CandidateValidityWitness ExternalAssembly
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem witnessEvent_eq_mixedExternalEvent
    (g : Direction F) (D : Finset (Direction F)) (T : FourTuple F)
    (d e : Direction F) (i j : Fin 4) (hT : T ∈ eligibleTuples g)
    (hd : d ∈ oldWitnessDirections g T D)
    (he : e ∈ freshWitnessDirections g T D) :
    witnessEvent g ((T, (i,j)), (d,e)) = mixedExternalEvent g T d e i j := by
  have hT' := (Finset.mem_filter.mp hT).2
  have hd' := Finset.mem_filter.mp hd
  have he' := (Finset.mem_filter.mp he).2
  ext M
  constructor
  · rintro ⟨hs, hij, _, _, _, _, _, x, hx, hex, hdx, hex'⟩
    exact ⟨⟨⟨lineEval g (tuplePoint M T 0), hs.2.2.2⟩, hs.2.2.1⟩,
      x, hx, hex, hij, hdx, hex'⟩
  · rintro ⟨hs, x, hx, hex, hij, hdx, hex'⟩
    have hde : d ≠ e := by
      intro h
      exact he'.1 (h ▸ hd'.1)
    exact ⟨⟨hT'.1, hT'.2, hs.2, successful_on_tupleTarget hs⟩,
      hij, hde, hd'.2.1, he'.2.1, hd'.2.2, he'.2.2, x, hx, hex, hdx, hex'⟩

theorem mixedOverlap_filter_eq (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) :
    (witnesses g M).filter (mixedOverlapFilter D) =
      (mixedOverlapKeys g D).filter (fun w => M ∈ witnessEvent g w) := by
  ext w
  simp only [Finset.mem_filter, mem_witnesses, mixedOverlapKeys,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hw, hover, hd, he⟩
    have ht : w.1.1 ∈ eligibleTuples g := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw.1.1, hw.1.2.1⟩
    refine ⟨⟨⟨ht, hover⟩, ?_, ?_⟩, hw⟩
    · exact Finset.mem_filter.mpr ⟨hd, hw.2.2.2.1, hw.2.2.2.2.2.1⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, he, hw.2.2.2.2.1, hw.2.2.2.2.2.2.1⟩
  · rintro ⟨⟨ht, hd, he⟩, hw⟩
    exact ⟨hw, ht.2,
      (Finset.mem_filter.mp hd).1, (Finset.mem_filter.mp he).2.1⟩

attribute [local instance] OAI.Balanced.CandidateMixedExternal.mixedAssemblyMeasurableSpace
theorem integral_mixedOverlapCount_eq_keySum
    (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F) :
    (∫ M, (mixedOverlapCount g D M : ℝ) ∂(exposedLaw D a).toMeasure) =
      ∑ w ∈ mixedOverlapKeys g D, conditionalProbability D a (witnessEvent g w) := by
  simp only [mixedOverlapCount, mixedOverlap_filter_eq]
  exact integral_eventCount_eq_sum (exposedLaw D a) (mixedOverlapKeys g D)
    (witnessEvent g)

omit [Field F] in
theorem sum_mixedOverlapKeys (g : Direction F) (D : Finset (Direction F))
    (f : WitnessKey F → ℝ) :
    (∑ w ∈ mixedOverlapKeys g D, f w) =
      ∑ T ∈ (eligibleTuples g).filter
          (fun T => 0 < (PartialAlignment.exposedTupleIndices T D).card),
        ∑ d ∈ oldWitnessDirections g T D,
          ∑ e ∈ freshWitnessDirections g T D, ∑ i : Fin 4, ∑ j : Fin 4,
            f ((T,(i,j)),(d,e)) := by
  unfold mixedOverlapKeys
  rw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  conv_rhs => rw [← Finset.sum_ite_mem_eq]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hT : T ∈ (eligibleTuples g).filter
      (fun T => 0 < (PartialAlignment.exposedTupleIndices T D).card)
  · simp only [hT, true_and, ite_true, ite_and, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_mem_eq]
    calc
      _ = ∑ i : Fin 4, ∑ d ∈ oldWitnessDirections g T D,
          ∑ j : Fin 4, ∑ e ∈ freshWitnessDirections g T D,
            f ((T,(i,j)),(d,e)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = ∑ d ∈ oldWitnessDirections g T D, ∑ i : Fin 4,
          ∑ j : Fin 4, ∑ e ∈ freshWitnessDirections g T D,
            f ((T,(i,j)),(d,e)) := Finset.sum_comm
      _ = ∑ d ∈ oldWitnessDirections g T D, ∑ i : Fin 4,
          ∑ e ∈ freshWitnessDirections g T D, ∑ j : Fin 4,
            f ((T,(i,j)),(d,e)) := by
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro d _
        exact Finset.sum_comm
  · simp only [hT, false_and, ite_false, Finset.sum_const_zero]

theorem integral_mixedOverlapCount_eq
    (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F) :
    (∫ M, (mixedOverlapCount g D M : ℝ) ∂(exposedLaw D a).toMeasure) =
      mixedExternalProbabilitySum g D a := by
  rw [integral_mixedOverlapCount_eq_keySum, sum_mixedOverlapKeys]
  unfold mixedExternalProbabilitySum
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [witnessEvent_eq_mixedExternalEvent g D T d e i j
    (Finset.mem_filter.mp hT).1 hd he]

theorem integral_mixedOverlapCount_le
    (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m) :
    (∫ M, (mixedOverlapCount g D M : ℝ) ∂(exposedLaw D a).toMeasure) ≤
      2097152 * ((m : ℝ) + 1)^5 / (Fintype.card F : ℝ) := by
  rw [integral_mixedOverlapCount_eq]
  exact mixedExternalProbabilitySum_le g D a m hD

theorem integral_mixedOverlapCount_le_uniform
    (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m) :
    (∫ M, (mixedOverlapCount g D M : ℝ) ∂(exposedLaw D a).toMeasure) ≤
      2097152 * ((m : ℝ) + 1)^5 := by
  apply (integral_mixedOverlapCount_le g D a m hD).trans
  apply div_le_self
  · positivity
  · exact_mod_cast Fintype.card_pos (α := F)

end
end Balanced.CandidateMixedExternal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_ExternalWitnessMoments
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ExternalAssembly

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateExposure PartialAlignment
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem exposureConstant_pos (m : ℕ) : 0 < exposureConstant m := by
  unfold exposureConstant
  positivity

omit [Field F] [Fintype F] in
theorem not_overlap_iff_fresh (T : FourTuple F) (D : Finset (Direction F)) :
    ¬ 0 < (exposedTupleIndices T D).card ↔ ∀ k, T.generator k ∉ D := by
  constructor
  · intro h k hk
    apply h
    exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
  · intro h hp
    obtain ⟨k, hk⟩ := Finset.card_pos.mp hp
    exact h k (Finset.mem_filter.mp hk).2

attribute [local instance] OAI.Balanced.ExternalAssembly.instMeasurableSpace_solutions_2
theorem witnesses_mean_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∫ M, ((witnesses g M).card : ℝ) ∂(exposedLaw D a).toMeasure) ≤
      exposureConstant m := by
  have hf := FreshExternalWitness.canonical_fresh_count_integral_le g D a m hD
  have ho := oldOld_overlap_integral_le g D a m hD
  have hm := CandidateMixedExternal.integral_mixedOverlapCount_le_uniform g D a m hD
  have hg := freshGenerators_firstOld_integral_le g D a m hD
  have hpart := integral_card_le_four_cases g D
    (fun T => 0 < (exposedTupleIndices T D).card) (exposedLaw D a)
  apply hpart.trans
  apply add_le_add hf
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply add_le_add
  · apply add_le_add
    · convert ho using 1 <;> first | rfl | (apply integral_congr_ae; filter_upwards [] with M; congr 2; ext w; simp only [Finset.mem_filter])
    · convert hm using 1 <;> first | rfl | (apply integral_congr_ae; filter_upwards [] with M; congr 2; ext w; simp only [Finset.mem_filter, CandidateMixedExternal.mixedOverlapFilter]; tauto)
  · convert hg using 1 <;> first | rfl | (apply integral_congr_ae; filter_upwards [] with M; congr 2; ext w; simp only [Finset.mem_filter, not_overlap_iff_fresh]; tauto)

theorem patternModel_mean_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (patternModel g).fixedExpectation D a (patternModel g).count ≤
      exposureConstant m := by
  rw [patternModel_fixedExpectation_exposed]
  simp_rw [patternModel_count]
  exact witnesses_mean_le g D a m hD

theorem patternModel_moment_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m s : ℕ) (hD : D.card ≤ m) :
    (patternModel g).fixedExpectation D a (fun M => (patternModel g).count M ^ s) ≤
      exposureConstant (m + (s - 1) * 6) ^ s := by
  apply (patternModel g).fixed_moment_le_pow D a 6 s
    (exposureConstant (m + (s - 1) * 6)) (exposureConstant_pos _).le
    (patternModel_support_card_le g)
  intro K hK y
  apply patternModel_mean_le g (D ∪ K) y (m + (s - 1) * 6)
  exact (Finset.card_union_le D K).trans (Nat.add_le_add hD hK)

theorem witnesses_original_moment_le (g : Direction F) (s : ℕ) :
    (∫ M, ((witnesses g M).card : ℝ)^s ∂(offsetLaw F).toMeasure) ≤
      exposureConstant ((s - 1) * 6) ^ s := by
  have h := patternModel_moment_le g ∅ (fun _ _ => 0) 0 s (by simp)
  simp only [PatternModel.fixedExpectation] at h
  rw [patternModel_measure] at h
  simp_rw [patternModel_count] at h
  have hfix (M : MergedPairs F) :
      (patternModel g).fixCoordinates ∅ (fun _ _ => 0) M = M := by
    funext d
    simp [PatternModel.fixCoordinates]
  simp_rw [hfix] at h
  simpa only [zero_add] using h

end
end Balanced.ExternalAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateGraphEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Balanced
open scoped _root_.Balanced

open Filter
open scoped Topology

universe u

namespace CandidateGraphEndpoint

theorem externalMomentConstant_pos : 0 < externalMomentConstant :=
  pow_pos (ExternalAssembly.exposureConstant_pos _) _

theorem tendsto_sizeGood
    (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | CandidateIncidenceTests.SizeGood M
        CandidateAbundanceAssembly.slotLinearConstant}) atTop (𝓝 1) := by
  have hslots := ExternalWitnessTail.candidateSlots_of_uniform_moment
    externalMomentConstant externalMomentConstant_pos.le F hq
    (fun n g => ExternalAssembly.witnesses_original_moment_le g 400)
  convert hslots using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  congr 1
  ext M
  constructor
  · intro h s
    exact ⟨h s, candidateSlot_card_le M s⟩
  · intro h s
    exact (h s).1

end CandidateGraphEndpoint

theorem candidateGraph_proof_oai : CandidateGraphResult.{u} :=
  CandidateIncidenceTests.candidateGraphResult_of_size_estimate
    CandidateAbundanceAssembly.slotLinearConstant
    CandidateAbundanceAssembly.slotLinearConstant_pos
    CandidateGraphEndpoint.tendsto_sizeGood

end Balanced

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Balanced.candidateGraph_proof_oai.{u} := @OAI.Balanced.candidateGraph_proof_oai.{u}
