-- Prove2me | solution 1 for OAI.Balanced.CandidateIncidenceTests.tendsto_smallGood
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:14:45.754168+00:00
-- url     : https://prove2.me/submissions/4d9a69b1-dce9-4180-97bc-bae7398a8561

import Mathlib
import Definitions.Def_OAIQ63Br002
import Definitions.Def_OAIQ63Br003

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
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateGeneratorPairModel
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateGeneratorPair

noncomputable section
open scoped Classical BigOperators
open MeasureTheory TupleAlignment CandidateExposure

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

theorem support_card (e : Finset (Direction F)) (a : (patternModel e).Label) :
    ((patternModel e).support a).card = 4 :=
  rootPatternModel_support_card a.1 a.2

theorem patternModel_count (e : Finset (Direction F)) (M : MergedPairs F) :
    (patternModel e).count M = (count e M : ℝ) := by
  rw [count, CandidateRetentionTransport.successfulTest_card_eq_sum_prescriptions,
    Nat.cast_sum]
  unfold PatternModel.count
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro g _
  simp only [successfulPrescriptions, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter]
  simp only [PatternModel.indicator, patternModel, Set.indicator_apply,
    Set.mem_ofPred_eq, rootSuccessEvent, RootPrescription.choice_tuple]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

attribute [local instance] OAI.Balanced.CandidateGeneratorPair.instMeasurableSpace_solutions
theorem patternModel_measure (e : Finset (Direction F)) :
    (patternModel e).measure = (offsetLaw F).toMeasure := by
  exact rootPatternModel_measure (F := F) none

theorem fixedExpectation_exposed (e D : Finset (Direction F))
    (a : MergedPairs F) (f : MergedPairs F → ℝ) :
    (patternModel e).fixedExpectation D a f =
      ∫ M, f M ∂(exposedLaw D a).toMeasure := by
  exact rootPatternModel_fixedExpectation_exposed (F := F) none D a f

theorem count_eq_sum_eligible (e : Finset (Direction F)) (M : MergedPairs F) :
    count e M = ∑ g : Direction F,
      (((eligibleTuples g).filter (fun T => e ⊆ generatorSet T)).filter
        (fun T => M ∈ successfulInDirection T g)).card := by
  rw [count, CandidateRetentionTransport.successfulTest_card_eq_sum_prescriptions]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.card_bij (fun a _ => a.tuple)
  · intro a ha
    simp only [successfulPrescriptions, Finset.mem_filter] at ha
    obtain ⟨⟨_, hs⟩, he⟩ := ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨((eligibleTupleEquivRootPrescription g).symm a).2, he⟩, hs⟩
  · intro a _ b _ hab
    apply (eligibleTupleEquivRootPrescription g).symm.injective
    exact Subtype.ext hab
  · intro T hT
    obtain ⟨hT, hs⟩ := Finset.mem_filter.mp hT
    obtain ⟨hg, he⟩ := Finset.mem_filter.mp hT
    let a := eligibleTupleEquivRootPrescription g ⟨T, hg⟩
    have ha : a.tuple = T := equivRootPrescription_tuple g ⟨T, hg⟩
    refine ⟨a, ?_, ha⟩
    simp only [successfulPrescriptions, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · change M ∈ successfulInDirection a.tuple g
      simpa only [ha] using hs
    · change e ⊆ generatorSet a.tuple
      simpa only [ha] using he

theorem integral_count (e D : Finset (Direction F)) (a : MergedPairs F) :
    (∫ M, (count e M : ℝ) ∂(exposedLaw D a).toMeasure) = probabilitySum e D a := by
  simp_rw [count_eq_sum_eligible, Nat.cast_sum]
  rw [integral_finsetSum _ (fun g _ => Integrable.of_finite)]
  exact Finset.sum_congr rfl (fun g _ => integral_eventCount_eq_sum (exposedLaw D a)
    ((eligibleTuples g).filter (fun T => e ⊆ generatorSet T))
    (fun T => successfulInDirection T g))

omit [Field F] [Fintype F] in
theorem card_le_exposed_indices (e D : Finset (Direction F)) (T : FourTuple F)
    (heD : e ⊆ D) (heT : e ⊆ generatorSet T) :
    e.card ≤ (PartialAlignment.exposedTupleIndices T D).card := by
  have hsub : e ⊆ (PartialAlignment.exposedTupleIndices T D).image T.generator := by
    intro d hd
    obtain ⟨i, _, hdi⟩ := Finset.mem_image.mp (heT hd)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hdi ▸ heD hd⟩, hdi⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

theorem probabilitySum_le_exposure_strata (e D : Finset (Direction F))
    (a : MergedPairs F) (he : e.card = 2) (heD : e ⊆ D) :
    probabilitySum e D a ≤ ∑ j ∈ Finset.Icc 2 4, ∑ g : Direction F,
      ∑ T ∈ tuplesWithExposure g D j,
        conditionalProbability D a (successfulInDirection T g) := by
  rw [Finset.sum_comm]
  unfold probabilitySum
  apply Finset.sum_le_sum
  intro g _
  have hpartition := Finset.sum_fiberwise_eq_sum_filter (eligibleTuples g)
    (Finset.Icc 2 4) (fun T => (PartialAlignment.exposedTupleIndices T D).card)
    (fun T => conditionalProbability D a (successfulInDirection T g))
  change _ ≤ ∑ j ∈ Finset.Icc 2 4,
    ∑ T ∈ (eligibleTuples g).filter
      (fun T => (PartialAlignment.exposedTupleIndices T D).card = j),
      conditionalProbability D a (successfulInDirection T g)
  rw [hpartition]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro T hT
    obtain ⟨hT, heT⟩ := Finset.mem_filter.mp hT
    apply Finset.mem_filter.mpr
    refine ⟨hT, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
    · simpa only [he] using card_le_exposed_indices e D T heD heT
    · simpa only [Fintype.card_fin] using
        (PartialAlignment.exposedTupleIndices T D).card_le_univ
  · intro T _ _
    exact ENNReal.toReal_nonneg

end
end Balanced.CandidateGeneratorPair

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

theorem same_direction_fixed_position_le (g : Direction F) (i : Fin 4) (y : Point F) :
    positionProbability (fun p => (∃ c, ∀ j, OnLine (p j) (g,c)) ∧ p i = y) ≤
      (Fintype.card F : ℝ)⁻¹^5 := by
  classical
  apply (positionProbability_mono (Q := fun p =>
    (∀ j, OnLine (p j) (lineThrough g y)) ∧ p i = y) ?_).trans
      (aligned_fixed_position_le i y (lineThrough g y))
  rintro p ⟨⟨c, hc⟩, hi⟩
  refine ⟨?_, hi⟩
  intro j
  change lineEval g (p j) = lineEval g y
  exact (hc j).trans (by simpa [hi] using (hc i).symm)

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

theorem same_direction_contains_point_le (g : Direction F) (y : Point F) :
    positionProbability (fun p =>
      (∃ c, ∀ j, OnLine (p j) (g,c)) ∧ ∃ i, p i = y) ≤
      4 * (Fintype.card F : ℝ)⁻¹^5 := by
  classical
  let P : Fin 4 → (Fin 4 → Point F) → Prop := fun i p =>
    (∃ c, ∀ j, OnLine (p j) (g,c)) ∧ p i = y
  apply (positionProbability_mono (Q := fun p => ∃ i, P i p) ?_).trans
  · simpa only [Fintype.card_fin, Nat.cast_ofNat] using
      positionProbability_exists_le_card P _ (fun i => same_direction_fixed_position_le g i y)
  · rintro p ⟨hc, i, hi⟩
    exact ⟨i, hc, hi⟩

theorem aligned_position_on_other_line_le (i : Fin 4) (l k : Line F) (hlk : l ≠ k) :
    positionProbability (fun p => (∀ j, OnLine (p j) l) ∧ OnLine (p i) k) ≤
      (Fintype.card F : ℝ)⁻¹^5 := by
  classical
  apply (positionProbability_mono (Q := fun p =>
    (∀ j, OnLine (p j) l) ∧ p i = lineIntersection l k) ?_).trans
      (aligned_fixed_position_le i (lineIntersection l k) l)
  rintro p ⟨hl, hk⟩
  refine ⟨hl, ?_⟩
  by_cases hd : l.1 = k.1
  · exact (hlk (eq_of_onLine_same_direction (p i) l k hd (hl i) hk)).elim
  · exact common_point_eq_of_lines_ne l k hlk (p i) (lineIntersection l k)
      (hl i) hk (onLine_lineIntersection_left _ _ hd)
      (onLine_lineIntersection_right _ _ hd)

theorem through_point_hits_line_le (g : Direction F) (y : Point F) (k : Line F)
    (hyk : ¬ OnLine y k) :
    positionProbability (fun p =>
      (∀ j, OnLine (p j) (lineThrough g y)) ∧ ∃ i, OnLine (p i) k) ≤
      4 * (Fintype.card F : ℝ)⁻¹^5 := by
  classical
  have hlk : lineThrough g y ≠ k := by
    intro h
    exact hyk (h ▸ onLine_lineThrough g y)
  let P : Fin 4 → (Fin 4 → Point F) → Prop := fun i p =>
    (∀ j, OnLine (p j) (lineThrough g y)) ∧ OnLine (p i) k
  apply (positionProbability_mono (Q := fun p => ∃ i, P i p) ?_).trans
  · simpa only [Fintype.card_fin, Nat.cast_ofNat] using
      positionProbability_exists_le_card P _
        (fun i => aligned_position_on_other_line_le i (lineThrough g y) k hlk)
  · rintro p ⟨hc, i, hi⟩
    exact ⟨i, hc, hi⟩

theorem positionProbability_two_fixed (i j : Fin 4) (hij : i ≠ j)
    (y z : Point F) (l : Line F) :
    positionProbability (fun p => ∀ a,
      p a ∈ if a = i then {y} else if a = j then {z} else linePoints l) =
      (Fintype.card F : ℝ)⁻¹^6 := by
  classical
  rw [positionProbability_rectangle]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  fin_cases i <;> fin_cases j <;>
    simp_all [Fin.prod_univ_four, linePoints_card] <;> field_simp

theorem aligned_two_fixed_le (i j : Fin 4) (hij : i ≠ j)
    (y z : Point F) (l : Line F) :
    positionProbability (fun p =>
      (∀ a, OnLine (p a) l) ∧ p i = y ∧ p j = z) ≤
      (Fintype.card F : ℝ)⁻¹^6 := by
  classical
  rw [← positionProbability_two_fixed i j hij y z l]
  apply positionProbability_mono
  rintro p ⟨hl, hi, hj⟩ a
  by_cases hai : a = i
  · simp [hai, hi]
  · by_cases haj : a = j
    · simp [haj, hj, Ne.symm hij]
    · simp [hai, haj, linePoints, hl a]

theorem same_direction_two_positions_lines_le (g : Direction F)
    (i j : Fin 4) (hij : i ≠ j) (l k : Line F) (hlk : l ≠ k) :
    positionProbability (fun p =>
      (∃ c, ∀ a, OnLine (p a) (g,c)) ∧ OnLine (p i) l ∧ OnLine (p j) k) ≤
      (Fintype.card F : ℝ)⁻¹^5 := by
  classical
  by_cases hgl : g = l.1
  · apply (positionProbability_mono (Q := fun p =>
      (∀ a, OnLine (p a) l) ∧ OnLine (p j) k) ?_).trans
        (aligned_position_on_other_line_le j l k hlk)
    rintro p ⟨⟨c, hc⟩, hi, hj⟩
    have heq : (g,c) = l := eq_of_onLine_same_direction (p i) (g,c) l hgl (hc i) hi
    exact ⟨fun a => by simpa only [heq] using hc a, hj⟩
  · by_cases hgk : g = k.1
    · apply (positionProbability_mono (Q := fun p =>
        (∀ a, OnLine (p a) k) ∧ OnLine (p i) l) ?_).trans
          (aligned_position_on_other_line_le i k l (Ne.symm hlk))
      rintro p ⟨⟨c, hc⟩, hi, hj⟩
      have heq : (g,c) = k := eq_of_onLine_same_direction (p j) (g,c) k hgk (hc j) hj
      exact ⟨fun a => by simpa only [heq] using hc a, hi⟩
    · let P : F → (Fin 4 → Point F) → Prop := fun c p =>
        (∀ a, OnLine (p a) (g,c)) ∧
        p i = lineIntersection (g,c) l ∧ p j = lineIntersection (g,c) k
      have hsub : ∀ p,
          ((∃ c, ∀ a, OnLine (p a) (g,c)) ∧ OnLine (p i) l ∧ OnLine (p j) k) →
          ∃ c, P c p := by
        rintro p ⟨⟨c, hc⟩, hi, hj⟩
        refine ⟨c, hc, ?_, ?_⟩
        · exact common_point_eq_of_lines_ne (g,c) l
            (fun heq => hgl (congrArg Prod.fst heq)) (p i) (lineIntersection (g,c) l)
            (hc i) hi (onLine_lineIntersection_left _ _ hgl)
            (onLine_lineIntersection_right _ _ hgl)
        · exact common_point_eq_of_lines_ne (g,c) k
            (fun heq => hgk (congrArg Prod.fst heq)) (p j) (lineIntersection (g,c) k)
            (hc j) hj (onLine_lineIntersection_left _ _ hgk)
            (onLine_lineIntersection_right _ _ hgk)
      calc
        _ ≤ positionProbability (fun p => ∃ c, P c p) := positionProbability_mono hsub
        _ ≤ (Fintype.card F : ℝ) * (Fintype.card F : ℝ)⁻¹^6 :=
          positionProbability_exists_le_card P _ (fun c =>
            aligned_two_fixed_le i j hij (lineIntersection (g,c) l)
              (lineIntersection (g,c) k) (g,c))
        _ = _ := by
          have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
          field_simp

theorem same_direction_hits_two_lines_le (g : Direction F)
    (l k : Line F) (hlk : l ≠ k) :
    positionProbability (fun p =>
      (∃ c, ∀ a, OnLine (p a) (g,c)) ∧
      ∃ i j : Fin 4, i ≠ j ∧ OnLine (p i) l ∧ OnLine (p j) k) ≤
      12 * (Fintype.card F : ℝ)⁻¹^5 := by
  classical
  let I := {ij : Fin 4 × Fin 4 // ij.1 ≠ ij.2}
  let P : I → (Fin 4 → Point F) → Prop := fun ij p =>
    (∃ c, ∀ a, OnLine (p a) (g,c)) ∧ OnLine (p ij.1.1) l ∧ OnLine (p ij.1.2) k
  have hcard : Fintype.card I = 12 := by decide
  apply (positionProbability_mono (Q := fun p => ∃ ij, P ij p) ?_).trans
  · simpa only [hcard, Nat.cast_ofNat] using
      positionProbability_exists_le_card P _ (fun ij =>
        same_direction_two_positions_lines_le g ij.1.1 ij.1.2 ij.2 l k hlk)
  · rintro p ⟨hc, i, j, hij, hi, hj⟩
    exact ⟨⟨(i,j), hij⟩, hc, hi, hj⟩

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

theorem conditional_tuple_contains_point_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hfresh : ∀ i, T.generator i ∉ D)
    (g : Direction F) (y : Point F) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (PartialAlignment.canonical_exposure_supported D a)).toOuterMeasure
        {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
          ∃ i, tuplePoint M T i = y}).toReal ≤
      4 * (Fintype.card F : ℝ)⁻¹^5 := by
  rw [conditional_probability_eq_positionProbability T hT D a hfresh (fun p =>
    (∃ c, ∀ j, OnLine (p j) (g,c)) ∧ ∃ i, p i = y)]
  exact same_direction_contains_point_le g y

theorem conditional_tuple_through_point_hits_line_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hfresh : ∀ i, T.generator i ∉ D)
    (g : Direction F) (y : Point F) (k : Line F) (hyk : ¬ OnLine y k) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (PartialAlignment.canonical_exposure_supported D a)).toOuterMeasure
        {M | (∀ j, OnLine (tuplePoint M T j) (lineThrough g y)) ∧
          ∃ i, OnLine (tuplePoint M T i) k}).toReal ≤
      4 * (Fintype.card F : ℝ)⁻¹^5 := by
  rw [conditional_probability_eq_positionProbability T hT D a hfresh (fun p =>
    (∀ j, OnLine (p j) (lineThrough g y)) ∧ ∃ i, OnLine (p i) k)]
  exact through_point_hits_line_le g y k hyk

theorem conditional_tuple_hits_two_lines_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hfresh : ∀ i, T.generator i ∉ D)
    (g : Direction F) (l k : Line F) (hlk : l ≠ k) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (PartialAlignment.canonical_exposure_supported D a)).toOuterMeasure
        {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
          ∃ i j : Fin 4, i ≠ j ∧ OnLine (tuplePoint M T i) l ∧ OnLine (tuplePoint M T j) k}).toReal ≤
      12 * (Fintype.card F : ℝ)⁻¹^5 := by
  rw [conditional_probability_eq_positionProbability T hT D a hfresh (fun p =>
    (∃ c, ∀ j, OnLine (p j) (g,c)) ∧
    ∃ i j : Fin 4, i ≠ j ∧ OnLine (p i) l ∧ OnLine (p j) k)]
  exact same_direction_hits_two_lines_le g l k hlk

end
end Balanced.CandidateFreshIncidence

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

theorem conditionalProbability_mono (D : Finset (Direction F)) (a : MergedPairs F)
    {E H : Set (MergedPairs F)} (h : E ⊆ H) :
    conditionalProbability D a E ≤ conditionalProbability D a H := by
  apply ENNReal.toReal_mono _ ((exposedLaw D a).toOuterMeasure.mono h)
  change (exposedLaw D a).toOuterMeasure H ≠ ⊤
  rw [PMF.toOuterMeasure_apply]
  exact (exposedLaw D a).tsum_coe_indicator_ne_top H

theorem lineHit_probability_le_success (T : FourTuple F) (g : Direction F)
    (L : Line F) (D : Finset (Direction F)) (a : MergedPairs F) :
    conditionalProbability D a (successfulLineHit T g L) ≤
      conditionalProbability D a (successfulInDirection T g) :=
  conditionalProbability_mono D a (fun _ h => h.1)

theorem lineHit_probability_fresh_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F) (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (hfresh : (exposedTupleIndices T D).card = 0) :
    conditionalProbability D a (successfulLineHit T g L) ≤
      4 * (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  have hnone : ∀ i, T.generator i ∉ D := by
    intro i hi
    have hempty := Finset.card_eq_zero.mp hfresh
    have hm : i ∈ exposedTupleIndices T D := by simp [exposedTupleIndices, hi]
    simp only [hempty, Finset.notMem_empty] at hm
  apply (conditionalProbability_mono D a (H :=
    {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
      ∃ i, OnLine (tuplePoint M T i) L}) (fun _ h => ⟨h.1.1,h.2⟩)).trans
  exact CandidateFreshIncidence.conditional_tuple_hits_line_probability_le
    T hT D a hnone g L

theorem lineHit_sum_fresh_le (g : Direction F) (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∑ T ∈ tuplesWithExposure g D 0,
      conditionalProbability D a (successfulLineHit T g L)) ≤
        (16384 * (m + 1) ^ 4 : ℝ) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ ∑ _T ∈ tuplesWithExposure g D 0, 4 * (Fintype.card F : ℝ)⁻¹ ^ 4 := by
      apply Finset.sum_le_sum
      intro T hT
      obtain ⟨hgood, hfresh⟩ := Finset.mem_filter.mp hT
      exact lineHit_probability_fresh_le T (Finset.mem_filter.mp hgood).2.1 g L D a hfresh
    _ = ((tuplesWithExposure g D 0).card : ℝ) *
        (4 * (Fintype.card F : ℝ)⁻¹ ^ 4) := by simp
    _ ≤ ((4096 * (m + 1) ^ 4 : ℝ) * (Fintype.card F : ℝ)^4) *
        (4 * (Fintype.card F : ℝ)⁻¹ ^ 4) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_tuplesWithExposure_le g D m 0 hD (by omega)
    _ = _ := by field_simp; ring

theorem lineHit_probabilitySum_le (g : Direction F) (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∑ T ∈ eligibleTuples g,
      conditionalProbability D a (successfulLineHit T g L)) ≤
        (32768 * (m + 1) ^ 4 : ℝ) := by
  rw [← Finset.sum_filter_add_sum_filter_not (eligibleTuples g)
    (fun T => (exposedTupleIndices T D).card = 0)]
  have hpos : (eligibleTuples g).filter
      (fun T => ¬ (exposedTupleIndices T D).card = 0) =
      (eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card) := by
    apply Finset.filter_congr
    intro T _
    omega
  rw [hpos]
  have hsecond : (∑ T ∈ (eligibleTuples g).filter
      (fun T => 0 < (exposedTupleIndices T D).card),
      conditionalProbability D a (successfulLineHit T g L)) ≤
        (16384 * (m + 1) ^ 4 : ℝ) := by
    apply le_trans _ (overlapProbabilitySum_le g D a m hD)
    exact Finset.sum_le_sum (fun T _ => lineHit_probability_le_success T g L D a)
  have hfirst := lineHit_sum_fresh_le g L D a m hD
  change (∑ T ∈ (eligibleTuples g).filter
    (fun T => (exposedTupleIndices T D).card = 0),
    conditionalProbability D a (successfulLineHit T g L)) ≤ _ at hfirst
  linarith

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

lemma measurable_count : Measurable P.count := by
  classical
  exact Finset.measurable_sum _ fun a _ => P.measurable_indicator a

lemma integrable_fixed_of_bound (K : Finset P.Color) (x : P.Sample)
    {f : P.Sample → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ ω, ‖f ω‖ ≤ C) :
    Integrable (fun ω => f (P.fixCoordinates K x ω)) P.measure := by
  exact Integrable.of_bound
    (hf.comp (P.measurable_fixCoordinates K x)).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => hC _)

end Balanced.PatternModel

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateGeneratorPairMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateGeneratorPair

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateExposure

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

theorem probabilitySum_le (e D : Finset (Direction F)) (a : MergedPairs F)
    (he : e.card = 2) (heD : e ⊆ D) (m : ℕ) (hD : D.card ≤ m) :
    probabilitySum e D a ≤ (32768 * (m + 1)^4 : ℝ) := by
  have h := probabilitySum_le_exposure_strata e D a he heD
  have h2 := sum_targets_success_two_three_le D a m 2 hD (Or.inl rfl)
  have h3 := sum_targets_success_two_three_le D a m 3 hD (Or.inr rfl)
  have h4 := sum_targets_success_four_le D a
  have hcard : (D.card : ℝ) ≤ (m : ℝ) + 1 := by
    exact_mod_cast (show D.card ≤ m + 1 by omega)
  have hpow : (D.card : ℝ)^4 ≤ ((m : ℝ) + 1)^4 :=
    pow_le_pow_left₀ (by positivity) hcard _
  rw [show Finset.Icc 2 4 = {2, 3, 4} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at h
  have hn : 0 ≤ ((m : ℝ) + 1)^4 := by positivity
  linarith

attribute [local instance] OAI.Balanced.CandidateGeneratorPair.instMeasurableSpace_solutions_1
theorem fixed_count_le_of_subset (e D : Finset (Direction F)) (a : MergedPairs F)
    (he : e.card = 2) (heD : e ⊆ D) (m : ℕ) (hD : D.card ≤ m) :
    (patternModel e).fixedExpectation D a (patternModel e).count ≤
      (32768 * (m + 1)^4 : ℝ) := by
  rw [fixedExpectation_exposed]
  simp_rw [patternModel_count]
  rw [integral_count]
  exact probabilitySum_le e D a he heD m hD

theorem model_count_nonneg (e : Finset (Direction F)) (M : MergedPairs F) :
    0 ≤ (patternModel e).count M := by rw [patternModel_count]; positivity

theorem model_count_le_card (e : Finset (Direction F)) (M : MergedPairs F) :
    (patternModel e).count M ≤ Fintype.card (patternModel e).Label := by
  calc
    _ ≤ ∑ _a : (patternModel e).Label, (1 : ℝ) :=
      Finset.sum_le_sum (fun a _ => (patternModel e).indicator_le_one a M)
    _ = _ := by simp

theorem fixed_count_le (e D : Finset (Direction F)) (a : MergedPairs F)
    (he : e.card = 2) (m : ℕ) (hD : D.card ≤ m) :
    (patternModel e).fixedExpectation D a (patternModel e).count ≤
      (32768 * (m + 3)^4 : ℝ) := by
  let P := patternModel e
  have hbound (y : P.Sample) : P.fixedExpectation (D ∪ e) y P.count ≤
      (32768 * (m + 3)^4 : ℝ) := by
    have hc : (D ∪ e).card ≤ m + 2 := by
      have h := Finset.card_union_le D e
      omega
    have h := fixed_count_le_of_subset e (D ∪ e) y he (Finset.subset_union_right)
      (m + 2) hc
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring
  have h := P.fixedExpectation_mul_le_of_fixedBounds D e a
    (fun _ => 1) P.count (32768 * (m + 3)^4) 1
    (Fintype.card P.Label) (by positivity) measurable_const P.measurable_count
    (fun _ => zero_le_one) (model_count_nonneg e) (fun _ => le_rfl)
    (model_count_le_card e) (by intros; rfl) hbound
  simpa [PatternModel.fixedExpectation, PatternModel.measure] using h

theorem fixed_moment_le (e D : Finset (Direction F)) (a : MergedPairs F)
    (he : e.card = 2) (m s : ℕ) (hD : D.card ≤ m) :
    (patternModel e).fixedExpectation D a
      (fun M => (patternModel e).count M ^ s) ≤
      (32768 * ((m + (s - 1)*4 : ℕ) + 3)^4 : ℝ)^s := by
  apply (patternModel e).fixed_moment_le_pow D a 4 s _ (by positivity)
    (fun b => (support_card e b).le)
  intro K hK y
  exact fixed_count_le e (D ∪ K) y he (m + (s - 1)*4)
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hD hK))

theorem count_moment_le (e : Finset (Direction F)) (he : e.card = 2) (s : ℕ) :
    (∫ M, (count e M : ℝ)^s ∂(offsetLaw F).toMeasure) ≤
      (32768 * (((s - 1)*4 : ℕ) + 3)^4 : ℝ)^s := by
  have h := fixed_moment_le e ∅ (fun _ _ => 0) he 0 s (by simp)
  have hfix (M : MergedPairs F) :
      (patternModel e).fixCoordinates ∅ (fun _ _ => 0) M = M := by
    funext d
    simp [PatternModel.fixCoordinates]
  simp only [PatternModel.fixedExpectation] at h
  simp_rw [hfix, patternModel_count] at h
  rw [patternModel_measure] at h
  simpa only [zero_add] using h

end
end Balanced.CandidateGeneratorPair

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateIncidenceTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidenceTests

noncomputable section
open scoped Classical
open CandidateRetentionTransport

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [DecidableEq F] in

theorem card_test : Fintype.card (Test F) =
    (Fintype.card F) ^ 2 +
    (Fintype.card F) ^ 3 * (Fintype.card F + 1) +
    (Fintype.card F) ^ 2 * (Fintype.card F + 1) ^ 2 +
    (Fintype.card F + 1) ^ 2 +
    Fintype.card F * (Fintype.card F + 1) ^ 2 := by
  simp only [Test, Point, Line, Direction, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_option]
  ring

omit [DecidableEq F] in

theorem card_test_le : Fintype.card (Test F) ≤ 15 * (Fintype.card F) ^ 4 := by
  rw [card_test]
  let q := Fintype.card F
  have hq : 1 ≤ q := Fintype.card_pos
  have h1 : q ≤ q ^ 2 := by nlinarith
  have h2 : q ^ 2 ≤ q ^ 3 := by
    nlinarith [Nat.mul_le_mul_left q h1]
  have h3 : q ^ 3 ≤ q ^ 4 := by
    nlinarith [Nat.mul_le_mul_left q h2]
  change q ^ 2 + q ^ 3 * (q + 1) + q ^ 2 * (q + 1) ^ 2 +
    (q + 1) ^ 2 + q * (q + 1) ^ 2 ≤ 15 * q ^ 4
  nlinarith

theorem count_le (M : MergedPairs F) (t : Test F) :
    count M t ≤ Fintype.card (SplitChoice F) := by
  rcases t with p | (⟨p,l⟩ | (⟨l,k⟩ | (⟨d,e⟩ | ⟨g,l⟩)))
  all_goals simp only [count]
  all_goals first | exact Finset.card_le_univ _ | split_ifs <;> first
    | exact Finset.card_le_univ _ | exact Nat.zero_le _

universe u

end
end Balanced.CandidateIncidenceTests

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateGeneratorPairFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Balanced.CandidateIncidenceTests

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

attribute [local instance] OAI.Balanced.CandidateIncidenceTests.generatorFamilyMeasurableSpace
theorem generatorPair_raw_moment_le (d e : Direction F) (s : ℕ) :
    (∫ M, (count M (Sum.inr (Sum.inr (Sum.inr (Sum.inl (d,e))))) : ℝ)^s
      ∂(offsetLaw F).toMeasure) ≤
      (32768 * (((s-1)*4 : ℕ) + 3)^4 : ℝ)^s := by
  classical
  by_cases h : d ≠ e
  · simpa only [count, ite_eq_left h, CandidateGeneratorPair.count] using
      CandidateGeneratorPair.count_moment_le ({d,e} : Finset (Direction F))
        (by simp [h]) s
  · by_cases hs : s = 0
    · subst s
      simp
    · simp only [count, ite_eq_right h, Nat.cast_zero, zero_pow hs, integral_zero]
      positivity

end Balanced.CandidateIncidenceTests

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

theorem model_support_card (R : Test F) (g : Direction F) (a : RootPrescription g) :
    ((model R g).support a).card = 4 := rootPatternModel_support_card g a

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
theorem model_measure (R : Test F) (g : Direction F) :
    (model R g).measure = (offsetLaw F).toMeasure := rootPatternModel_measure g

theorem allModel_measure (R : Test F) :
    (allModel R).measure = (offsetLaw F).toMeasure := rootPatternModel_measure (none : Direction F)

theorem model_fixedExpectation (R : Test F) (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (f : MergedPairs F → ℝ) :
    (model R g).fixedExpectation D a f = ∫ M, f M ∂(exposedLaw D a).toMeasure :=
  rootPatternModel_fixedExpectation_exposed g D a f

theorem allModel_fixedExpectation (R : Test F)
    (D : Finset (Direction F)) (a : MergedPairs F) (f : MergedPairs F → ℝ) :
    (allModel R).fixedExpectation D a f = ∫ M, f M ∂(exposedLaw D a).toMeasure :=
  rootPatternModel_fixedExpectation_exposed (none : Direction F) D a f

theorem model_fixed_count (R : Test F) (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (model R g).fixedExpectation D a (model R g).count =
      ∑ T ∈ eligibleTuples g, conditionalProbability D a
        {M | M ∈ successfulInDirection T g ∧ R T g (tuplePoint M T)} := by
  rw [model_fixedExpectation]
  simp_rw [model_count]
  simpa only [tupleCount, conditionalProbability, Set.mem_ofPred_eq] using
    integral_eventCount_eq_sum (exposedLaw D a) (eligibleTuples g)
      (fun T => {M | M ∈ successfulInDirection T g ∧ R T g (tuplePoint M T)})

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

theorem lineHit_model_fixed_count_le (g : Direction F) (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (model (lineHitTest L) g).fixedExpectation D a (model (lineHitTest L) g).count ≤
      (32768 * (m + 1)^4 : ℝ) := by
  rw [model_fixed_count]
  exact lineHit_probabilitySum_le g L D a m hD

theorem lineHit_model_moment_le (g : Direction F) (L : Line F)
    (K₀ : Finset (Direction F)) (a : MergedPairs F) (m s : ℕ) (hK : K₀.card ≤ m) :
    (model (lineHitTest L) g).fixedExpectation K₀ a
      (fun M => (model (lineHitTest L) g).count M ^ s) ≤
        (32768 * ((m + (s-1)*4 : ℕ) + 1)^4 : ℝ)^s := by
  apply (model (lineHitTest L) g).fixed_moment_le_pow K₀ a 4 s _ (by positivity)
    (fun b => (model_support_card _ _ b).le)
  intro K hK' y
  exact lineHit_model_fixed_count_le g L (K₀ ∪ K) y (m + (s-1)*4)
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hK hK'))

end
end Balanced.CandidateIncidence

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateIncidenceCountTransport
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidence

noncomputable section
open scoped Classical BigOperators
open MeasureTheory TupleAlignment CandidateRetentionTransport

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

theorem model_count_eq_prescriptions (R : Test F) (g : Direction F)
    (M : MergedPairs F) :
    (model R g).count M =
      (((successfulPrescriptions M g).filter
        (fun a => R a.tuple g (tuplePoint M a.tuple))).card : ℝ) := by
  simp only [PatternModel.count, PatternModel.indicator, model, event,
    successfulPrescriptions, Finset.filter_filter, Finset.card_eq_sum_ones,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_filter,
    Set.indicator_apply, Set.mem_ofPred_eq, rootSuccessEvent]

theorem model_count_eq_successfulTest (R : Test F) (g : Direction F)
    (M : MergedPairs F) :
    (model R g).count M =
      ((successfulTest M (fun C => C.line.1 = g ∧ choiceTest R M C)).card : ℝ) := by
  rw [successfulTest_at_target_card]
  rw [model_count_eq_prescriptions]
  apply congrArg (fun prescriptions : Finset (RootPrescription g) =>
    (prescriptions.card : ℝ))
  apply Finset.filter_congr
  intro prescription _
  simp only [choiceTest, RootPrescription.choice_tuple,
    RootPrescription.choice_direction]

theorem allModel_count_eq_successfulTest (R : Test F) (M : MergedPairs F) :
    (allModel R).count M = ((successfulTest M (choiceTest R M)).card : ℝ) := by
  rw [successfulTest_card_eq_sum_prescriptions, Nat.cast_sum]
  rw [allModel_count]
  apply Finset.sum_congr rfl
  intro g _
  rw [← model_count]
  rw [model_count_eq_prescriptions]
  apply congrArg (fun prescriptions : Finset (RootPrescription g) =>
    (prescriptions.card : ℝ))
  apply Finset.filter_congr
  intro prescription _
  simp only [choiceTest, RootPrescription.choice_tuple,
    RootPrescription.choice_direction]

theorem lineHit_model_count (g : Direction F) (L : Line F) (M : MergedPairs F) :
    (model (lineHitTest L) g).count M =
      ((successfulTest M (fun C => C.line.1 = g ∧
        ∃ p ∈ designated M C, OnLine p L)).card : ℝ) := by
  rw [model_count_eq_successfulTest]
  congr 2
  ext C
  simp [choiceTest, lineHitTest, designated]

attribute [local instance] OAI.Balanced.CandidateIncidence.incidenceTransportMeasurableSpace
theorem lineHit_successfulTest_moment_le (g : Direction F) (L : Line F) (s : ℕ) :
    (∫ M, (((successfulTest M (fun C => C.line.1 = g ∧
      ∃ p ∈ designated M C, OnLine p L)).card : ℝ)^s)
      ∂(offsetLaw F).toMeasure) ≤
      (32768 * (((s-1)*4 : ℕ) + 1)^4 : ℝ)^s := by
  have h := lineHit_model_moment_le g L ∅ (fun _ _ => 0) 0 s (by simp)
  have hempty (M : MergedPairs F) :
      (model (lineHitTest L) g).fixCoordinates ∅ (fun _ _ => 0) M = M := by
    funext d
    simp only [PatternModel.fixCoordinates, Finset.notMem_empty, ite_false]
  simp only [PatternModel.fixedExpectation, Nat.zero_add] at h
  simp_rw [hempty] at h
  rw [model_measure] at h
  simpa only [lineHit_model_count] using h

end
end Balanced.CandidateIncidence

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateLineHitFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidenceTests

noncomputable section
open MeasureTheory
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

attribute [local instance] OAI.Balanced.CandidateIncidenceTests.lineHitFamilyMeasurableSpace
theorem lineHit_raw_moment_le (g : Direction F) (L : Line F) (s : ℕ) :
    (∫ M, (count M (Sum.inr (Sum.inr (Sum.inr (Sum.inr (g,L))))) : ℝ)^s
      ∂(offsetLaw F).toMeasure) ≤
      (32768 * (((s-1)*4 : ℕ) + 1)^4 : ℝ)^s := by
  simpa only [count] using CandidateIncidence.lineHit_successfulTest_moment_le g L s

end
end Balanced.CandidateIncidenceTests

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

theorem conditional_tuple_contains_point_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hD : (exposedTupleIndices T D).card ≤ 1)
    (g : Direction F) (hg : ∀ i, T.generator i ≠ g) (y : Point F) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure
        {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
          ∃ i, tuplePoint M T i = y}).toReal ≤
      (Fintype.card F : ℝ)⁻¹^4 := by
  apply le_trans (pmf_probability_mono _ (B :=
    {M | ∀ j, OnLine (tuplePoint M T j) (g, lineEval g y)}) ?_)
    (conditional_prescribed_line_probability_le T hT D a hD g hg _)
  rintro M ⟨⟨c, hc⟩, i, hi⟩ j
  have hy : lineEval g y = c := by simpa only [hi, OnLine] using hc i
  simpa only [hy] using hc j

theorem conditional_tuple_through_point_hits_line_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hD : (exposedTupleIndices T D).card ≤ 1)
    (g : Direction F) (hg : ∀ i, T.generator i ≠ g) (y : Point F) (k : Line F) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure
        {M | (∀ j, OnLine (tuplePoint M T j) (lineThrough g y)) ∧
          ∃ i, OnLine (tuplePoint M T i) k}).toReal ≤
      (Fintype.card F : ℝ)⁻¹^4 := by
  apply le_trans (pmf_probability_mono _ (B :=
    {M | ∀ j, OnLine (tuplePoint M T j) (g, lineEval g y)}) ?_)
    (conditional_prescribed_line_probability_le T hT D a hD g hg _)
  exact fun _ h => h.1

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

theorem conditional_tuple_hits_two_lines_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hD : (exposedTupleIndices T D).card ≤ 1)
    (g : Direction F) (hg : ∀ i, T.generator i ≠ g) (L K : Line F)
    (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure
        {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
          ∃ i j : Fin 4, i ≠ j ∧ OnLine (tuplePoint M T i) L ∧
            OnLine (tuplePoint M T j) K}).toReal ≤
      4 * (Fintype.card F : ℝ)⁻¹^4 := by
  apply le_trans (pmf_probability_mono _ (B :=
    {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
      ∃ i, OnLine (tuplePoint M T i) L}) ?_)
    (conditional_tuple_hits_line_probability_le T hT D a hD g hg L havoid)
  rintro M ⟨hc,i,j,hij,hi,hj⟩
  exact ⟨hc,i,hi⟩

end
end Balanced.CandidatePartialPointIncidence

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidatePointIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidatePointIncidence

noncomputable section
open scoped Classical BigOperators
open CandidateExposure PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem conditionalProbability_mono (D : Finset (Direction F)) (a : MergedPairs F)
    {E H : Set (MergedPairs F)} (h : E ⊆ H) :
    conditionalProbability D a E ≤ conditionalProbability D a H := by
  apply ENNReal.toReal_mono _ ((exposedLaw D a).toOuterMeasure.mono h)
  change (exposedLaw D a).toOuterMeasure H ≠ ⊤
  rw [PMF.toOuterMeasure_apply]
  exact (exposedLaw D a).tsum_coe_indicator_ne_top H

omit [Fintype F] [DecidableEq F] in
theorem pointEvent_subset_success (T : FourTuple F) (g : Direction F) (y : Point F) :
    pointEvent T g y ⊆ successfulInDirection T g := fun _ h => h.1

omit [Fintype F] [DecidableEq F] in
theorem pointLineEvent_subset_success (T : FourTuple F) (g : Direction F)
    (y : Point F) (K : Line F) :
    pointLineEvent T g y K ⊆ successfulInDirection T g := by
  rintro M ⟨hon, hinj, _⟩
  exact ⟨⟨lineEval g y, hon⟩, hinj⟩

theorem point_probability_fresh_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hfresh : ∀ i, T.generator i ∉ D)
    (g : Direction F) (y : Point F) :
    conditionalProbability D a (pointEvent T g y) ≤
      4 * (Fintype.card F : ℝ)⁻¹ ^ 5 := by
  apply (conditionalProbability_mono D a (H := {M |
    (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
      ∃ i, tuplePoint M T i = y}) (fun _ h => ⟨h.1.1, h.2⟩)).trans
  exact CandidateFreshIncidence.conditional_tuple_contains_point_probability_le
    T hT D a hfresh g y

theorem point_probability_one_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hD : (exposedTupleIndices T D).card ≤ 1)
    (g : Direction F) (hg : ∀ i, T.generator i ≠ g) (y : Point F) :
    conditionalProbability D a (pointEvent T g y) ≤
      (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  apply (conditionalProbability_mono D a (H := {M |
    (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
      ∃ i, tuplePoint M T i = y}) (fun _ h => ⟨h.1.1, h.2⟩)).trans
  exact CandidatePartialPointIncidence.conditional_tuple_contains_point_probability_le
    T hT D a hD g hg y

theorem pointLine_probability_fresh_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hfresh : ∀ i, T.generator i ∉ D)
    (g : Direction F) (y : Point F) (K : Line F) (hyK : ¬ OnLine y K) :
    conditionalProbability D a (pointLineEvent T g y K) ≤
      4 * (Fintype.card F : ℝ)⁻¹ ^ 5 := by
  apply (conditionalProbability_mono D a (H := {M |
    (∀ j, OnLine (tuplePoint M T j) (lineThrough g y)) ∧
      ∃ i, OnLine (tuplePoint M T i) K}) (fun _ h => ⟨h.1, h.2.2⟩)).trans
  exact CandidateFreshIncidence.conditional_tuple_through_point_hits_line_probability_le
    T hT D a hfresh g y K hyK

theorem pointLine_probability_one_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hD : (exposedTupleIndices T D).card ≤ 1)
    (g : Direction F) (hg : ∀ i, T.generator i ≠ g) (y : Point F) (K : Line F) :
    conditionalProbability D a (pointLineEvent T g y K) ≤
      (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  apply (conditionalProbability_mono D a (H := {M |
    (∀ j, OnLine (tuplePoint M T j) (lineThrough g y)) ∧
      ∃ i, OnLine (tuplePoint M T i) K}) (fun _ h => ⟨h.1, h.2.2⟩)).trans
  exact CandidatePartialPointIncidence.conditional_tuple_through_point_hits_line_probability_le
    T hT D a hD g hg y K

theorem sum_stratum_le (D : Finset (Direction F)) (a : MergedPairs F)
    (m j : ℕ) (hD : D.card ≤ m) (hj : j ≤ 4)
    (E : FourTuple F → Direction F → Set (MergedPairs F)) (C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ g T, T ∈ tuplesWithExposure g D j →
      conditionalProbability D a (E T g) ≤ C * (Fintype.card F : ℝ)⁻¹ ^ (5-j)) :
    (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j,
      conditionalProbability D a (E T g)) ≤ 8192 * C * ((m : ℝ)+1)^4 := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hdir : (Fintype.card (Direction F) : ℝ) ≤ 2 * Fintype.card F := by
    have hn : 0 < Fintype.card F := Fintype.card_pos
    have hd : Fintype.card (Direction F) ≤ 2 * Fintype.card F := by
      simp only [Direction, Fintype.card_option]
      omega
    exact_mod_cast hd
  have hexp : 5-j = (4-j)+1 := by omega
  calc
    _ ≤ ∑ g : Direction F, ((tuplesWithExposure g D j).card : ℝ) *
        (C * (Fintype.card F : ℝ)⁻¹ ^ (5-j)) := by
      apply Finset.sum_le_sum
      intro g _
      simpa using Finset.sum_le_sum (fun T hT => hE g T hT)
    _ ≤ ∑ _g : Direction F,
        ((4096 * ((m : ℝ)+1)^4) * (Fintype.card F : ℝ)^(4-j)) *
          (C * (Fintype.card F : ℝ)⁻¹ ^ (5-j)) := by
      apply Finset.sum_le_sum
      intro g _
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_tuplesWithExposure_le g D m j hD hj
    _ = (Fintype.card (Direction F) : ℝ) *
        (((4096 * ((m : ℝ)+1)^4) * (Fintype.card F : ℝ)^(4-j)) *
          (C * (Fintype.card F : ℝ)⁻¹ ^ (5-j))) := by simp
    _ ≤ (2 * (Fintype.card F : ℝ)) *
        (((4096 * ((m : ℝ)+1)^4) * (Fintype.card F : ℝ)^(4-j)) *
          (C * (Fintype.card F : ℝ)⁻¹ ^ (5-j))) := by gcongr
    _ = _ := by
      rw [hexp, pow_succ, inv_pow]
      field_simp
      ring

omit [Field F] [Fintype F] in
theorem fresh_of_exposure_zero (T : FourTuple F) (D : Finset (Direction F))
    (h : (exposedTupleIndices T D).card = 0) : ∀ i, T.generator i ∉ D := by
  have hz := Finset.card_eq_zero.mp h
  intro i hi
  have hm : i ∈ exposedTupleIndices T D := by simp [exposedTupleIndices, hi]
  rw [hz] at hm
  exact Finset.notMem_empty i hm

theorem point_sum_fresh_le (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m) (y : Point F) :
    (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D 0,
      conditionalProbability D a (pointEvent T g y)) ≤
        32768 * ((m : ℝ)+1)^4 := by
  apply (sum_stratum_le D a m 0 hD (by omega)
    (fun T g => pointEvent T g y) 4 (by norm_num) ?_).trans_eq
  · ring
  · intro g T hT
    obtain ⟨he, hz⟩ := Finset.mem_filter.mp hT
    exact point_probability_fresh_le T (Finset.mem_filter.mp he).2.1 D a
      (fresh_of_exposure_zero T D hz) g y

theorem point_sum_one_le (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m) (y : Point F) :
    (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D 1,
      conditionalProbability D a (pointEvent T g y)) ≤
        8192 * ((m : ℝ)+1)^4 := by
  apply (sum_stratum_le D a m 1 hD (by omega)
    (fun T g => pointEvent T g y) 1 (by norm_num) ?_).trans_eq
  · ring
  · intro g T hT
    obtain ⟨he, hz⟩ := Finset.mem_filter.mp hT
    obtain ⟨hinj, hg⟩ := (Finset.mem_filter.mp he).2
    simpa using point_probability_one_le T hinj D a hz.le g hg y

theorem pointLine_sum_fresh_le (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m) (y : Point F) (K : Line F) (hyK : ¬ OnLine y K) :
    (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D 0,
      conditionalProbability D a (pointLineEvent T g y K)) ≤
        32768 * ((m : ℝ)+1)^4 := by
  apply (sum_stratum_le D a m 0 hD (by omega)
    (fun T g => pointLineEvent T g y K) 4 (by norm_num) ?_).trans_eq
  · ring
  · intro g T hT
    obtain ⟨he, hz⟩ := Finset.mem_filter.mp hT
    exact pointLine_probability_fresh_le T (Finset.mem_filter.mp he).2.1 D a
      (fresh_of_exposure_zero T D hz) g y K hyK

theorem pointLine_sum_one_le (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m) (y : Point F) (K : Line F) :
    (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D 1,
      conditionalProbability D a (pointLineEvent T g y K)) ≤
        8192 * ((m : ℝ)+1)^4 := by
  apply (sum_stratum_le D a m 1 hD (by omega)
    (fun T g => pointLineEvent T g y K) 1 (by norm_num) ?_).trans_eq
  · ring
  · intro g T hT
    obtain ⟨he, hz⟩ := Finset.mem_filter.mp hT
    obtain ⟨hinj, hg⟩ := (Finset.mem_filter.mp he).2
    simpa using pointLine_probability_one_le T hinj D a hz.le g hg y K

end
end Balanced.CandidatePointIncidence

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidatePointIncidenceMean
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidatePointIncidence

noncomputable section
open scoped Classical BigOperators
open CandidateExposure PartialAlignment MeasureTheory

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem probabilitySum_eq_strata (D : Finset (Direction F)) (a : MergedPairs F)
    (E : FourTuple F → Direction F → Set (MergedPairs F)) :
    (∑ g : Direction F, ∑ T ∈ eligibleTuples g, conditionalProbability D a (E T g)) =
      ∑ j ∈ Finset.range 5, ∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j,
        conditionalProbability D a (E T g) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (s := eligibleTuples g) (t := Finset.range 5)
    (g := fun T => (exposedTupleIndices T D).card)
    (fun T _ => Finset.mem_range.mpr (by
      have hc := (exposedTupleIndices T D).card_le_univ
      simp only [Fintype.card_fin] at hc
      omega)) (fun T => conditionalProbability D a (E T g))

theorem probabilitySum_le_of_low (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m)
    (E : FourTuple F → Direction F → Set (MergedPairs F))
    (hsub : ∀ T g, E T g ⊆ successfulInDirection T g)
    (hzero : (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D 0,
      conditionalProbability D a (E T g)) ≤ 32768 * ((m : ℝ)+1)^4)
    (hone : (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D 1,
      conditionalProbability D a (E T g)) ≤ 8192 * ((m : ℝ)+1)^4) :
    (∑ g : Direction F, ∑ T ∈ eligibleTuples g,
      conditionalProbability D a (E T g)) ≤ 60000 * ((m : ℝ)+1)^4 := by
  have hdom (j : ℕ) : (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j,
      conditionalProbability D a (E T g)) ≤
      ∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j,
        conditionalProbability D a (successfulInDirection T g) := by
    apply Finset.sum_le_sum
    intro g _
    exact Finset.sum_le_sum (fun T _ => conditionalProbability_mono D a (hsub T g))
  have htwo := (hdom 2).trans (sum_targets_success_two_three_le D a m 2 hD (Or.inl rfl))
  have hthree := (hdom 3).trans (sum_targets_success_two_three_le D a m 3 hD (Or.inr rfl))
  have hfour := (hdom 4).trans (sum_targets_success_four_le D a)
  have hc : (D.card : ℝ)^4 ≤ ((m : ℝ)+1)^4 := by
    gcongr
    exact (show (D.card : ℝ) ≤ ↑m from by exact_mod_cast hD).trans (by linarith)
  rw [probabilitySum_eq_strata]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  nlinarith [pow_nonneg (show (0 : ℝ) ≤ (m : ℝ)+1 by positivity) 4]

theorem point_probabilitySum_le (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m) (y : Point F) :
    (∑ g : Direction F, ∑ T ∈ eligibleTuples g,
      conditionalProbability D a (pointEvent T g y)) ≤ 60000 * ((m : ℝ)+1)^4 :=
  probabilitySum_le_of_low D a m hD (fun T g => pointEvent T g y)
    (fun T g => pointEvent_subset_success T g y)
    (point_sum_fresh_le D a m hD y) (point_sum_one_le D a m hD y)

theorem pointLine_probabilitySum_le (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m) (y : Point F) (K : Line F) (hyK : ¬ OnLine y K) :
    (∑ g : Direction F, ∑ T ∈ eligibleTuples g,
      conditionalProbability D a (pointLineEvent T g y K)) ≤ 60000 * ((m : ℝ)+1)^4 :=
  probabilitySum_le_of_low D a m hD (fun T g => pointLineEvent T g y K)
    (fun T g => pointLineEvent_subset_success T g y K)
    (pointLine_sum_fresh_le D a m hD y K hyK) (pointLine_sum_one_le D a m hD y K)

omit [Fintype F] [DecidableEq F] in
theorem pointLine_model_event_eq (T : FourTuple F) (g : Direction F)
    (y : Point F) (K : Line F) :
    {M | M ∈ successfulInDirection T g ∧ pointLineTest y K T g (tuplePoint M T)} =
      pointLineEvent T g y K := by
  ext M
  constructor
  · rintro ⟨hs, hon, hhit⟩
    exact ⟨hon, hs.2, hhit⟩
  · rintro ⟨hon, hinj, hhit⟩
    exact ⟨⟨⟨lineEval g y, hon⟩, hinj⟩, hon, hhit⟩

theorem point_model_fixed_count_le (y : Point F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (CandidateIncidence.allModel (pointTest y)).fixedExpectation D a
      (CandidateIncidence.allModel (pointTest y)).count ≤ 60000 * ((m : ℝ)+1)^4 := by
  rw [CandidateIncidence.allModel_fixed_count]
  exact point_probabilitySum_le D a m hD y

theorem pointLine_model_fixed_count_le (y : Point F) (K : Line F) (hyK : ¬ OnLine y K)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (CandidateIncidence.allModel (pointLineTest y K)).fixedExpectation D a
      (CandidateIncidence.allModel (pointLineTest y K)).count ≤ 60000 * ((m : ℝ)+1)^4 := by
  rw [CandidateIncidence.allModel_fixed_count]
  simp_rw [pointLine_model_event_eq]
  exact pointLine_probabilitySum_le D a m hD y K hyK

theorem point_model_moment_le (y : Point F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m s : ℕ) (hD : D.card ≤ m) :
    (CandidateIncidence.allModel (pointTest y)).fixedExpectation D a
      (fun M => (CandidateIncidence.allModel (pointTest y)).count M ^ s) ≤
      (60000 * ((m + (s-1)*4 : ℕ)+1)^4 : ℝ)^s := by
  apply (CandidateIncidence.allModel (pointTest y)).fixed_moment_le_pow D a 4 s _
    (by positivity) (fun b => (CandidateIncidence.allModel_support_card _ b).le)
  intro J hJ b
  exact point_model_fixed_count_le y (D ∪ J) b (m + (s-1)*4)
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hD hJ))

theorem pointLine_model_moment_le (y : Point F) (K : Line F) (hyK : ¬ OnLine y K)
    (D : Finset (Direction F)) (a : MergedPairs F) (m s : ℕ) (hD : D.card ≤ m) :
    (CandidateIncidence.allModel (pointLineTest y K)).fixedExpectation D a
      (fun M => (CandidateIncidence.allModel (pointLineTest y K)).count M ^ s) ≤
      (60000 * ((m + (s-1)*4 : ℕ)+1)^4 : ℝ)^s := by
  apply (CandidateIncidence.allModel (pointLineTest y K)).fixed_moment_le_pow D a 4 s _
    (by positivity) (fun b => (CandidateIncidence.allModel_support_card _ b).le)
  intro J hJ b
  exact pointLine_model_fixed_count_le y K hyK (D ∪ J) b (m + (s-1)*4)
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hD hJ))

end
end Balanced.CandidatePointIncidence

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidatePointFamily
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidenceTests

noncomputable section
open scoped Classical
open MeasureTheory TupleAlignment CandidateRetentionTransport CandidateIncidence
open CandidatePointIncidence
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

theorem point_model_count (y : Point F) (M : MergedPairs F) :
    (allModel (pointTest y)).count M = (count M (Sum.inl y) : ℝ) := by
  rw [allModel_count_eq_successfulTest]
  simp only [count]
  congr 2
  ext C
  simp [_root_.OAI.Balanced.CandidateIncidence.choiceTest, pointTest, designated]

theorem pointLine_model_count (y : Point F) (K : Line F) (M : MergedPairs F) :
    (allModel (pointLineTest y K)).count M =
      ((successfulTest M (fun C => OnLine y C.line ∧
        ∃ p ∈ designated M C, OnLine p K)).card : ℝ) := by
  rw [allModel_count_eq_successfulTest]
  congr 2
  ext C
  simp only [mem_successfulTest]
  constructor
  · rintro ⟨hC, htest⟩
    change (∀ i, OnLine (tuplePoint M C.tuple i) (lineThrough C.line.1 y)) ∧
      (∃ i, OnLine (tuplePoint M C.tuple i) K) at htest
    have hline := ((mem_successfulChoices M C).mp hC).2.2.2
    refine ⟨hC, ?_, ?_⟩
    · change lineEval C.line.1 y = C.line.2
      exact (htest.1 0).symm.trans (hline 0)
    · obtain ⟨i, hi⟩ := htest.2
      exact ⟨tuplePoint M C.tuple i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hi⟩
  · rintro ⟨hC, hy, hhit⟩
    have hline := ((mem_successfulChoices M C).mp hC).2.2.2
    refine ⟨hC, ?_, ?_⟩
    · intro i
      change lineEval C.line.1 (tuplePoint M C.tuple i) = lineEval C.line.1 y
      exact (hline i).trans hy.symm
    · obtain ⟨p, hp, hon⟩ := hhit
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨i, hon⟩

attribute [local instance] OAI.Balanced.CandidateIncidenceTests.pointFamilyMeasurableSpace
theorem point_raw_moment_le (y : Point F) (s : ℕ) :
    (∫ M, (count M (Sum.inl y) : ℝ)^s ∂(offsetLaw F).toMeasure) ≤
      (60000 * (((s-1)*4 : ℕ)+1)^4 : ℝ)^s := by
  have h := point_model_moment_le y ∅ (fun _ _ => 0) 0 s (by simp)
  have hempty (M : MergedPairs F) :
      (allModel (pointTest y)).fixCoordinates ∅ (fun _ _ => 0) M = M := by
    funext d
    simp only [PatternModel.fixCoordinates, Finset.notMem_empty, ite_false]
  simp only [PatternModel.fixedExpectation, Nat.zero_add] at h
  simp_rw [hempty] at h
  rw [allModel_measure] at h
  simpa only [point_model_count] using h

theorem pointLine_raw_moment_le (y : Point F) (K : Line F) (s : ℕ) :
    (∫ M, (count M (Sum.inr (Sum.inl (y,K))) : ℝ)^s ∂(offsetLaw F).toMeasure) ≤
      (60000 * (((s-1)*4 : ℕ)+1)^4 : ℝ)^s := by
  by_cases hyK : OnLine y K
  · simp only [count, ite_eq_right (not_not.mpr hyK), Nat.cast_zero]
    cases s with
    | zero => simp
    | succ s =>
        simp only [zero_pow (Nat.succ_ne_zero s), integral_zero]
        positivity
  · have h := pointLine_model_moment_le y K hyK ∅ (fun _ _ => 0) 0 s (by simp)
    have hempty (M : MergedPairs F) :
        (allModel (pointLineTest y K)).fixCoordinates ∅ (fun _ _ => 0) M = M := by
      funext d
      simp only [PatternModel.fixCoordinates, Finset.notMem_empty, ite_false]
    simp only [PatternModel.fixedExpectation, Nat.zero_add] at h
    simp_rw [hempty] at h
    rw [allModel_measure] at h
    simpa only [pointLine_model_count, count, ite_eq_left hyK] using h

end
end Balanced.CandidateIncidenceTests

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateIncidenceInitialSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidenceSums

noncomputable section
open scoped Classical BigOperators
open PartialAlignment TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem probability_mono (D : Finset (Direction F)) (a : MergedPairs F)
    {E G : Set (MergedPairs F)} (h : E ⊆ G) :
    probability D a E ≤ probability D a G := by
  unfold probability
  apply ENNReal.toReal_mono _ (MeasureTheory.measure_mono h)
  have hu : ((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (canonical_exposure_supported D a)).toOuterMeasure Set.univ = 1 := by
    exact (PMF.toOuterMeasure_apply_eq_one_iff _ Set.univ).mpr (Set.subset_univ _)
  exact ne_of_lt ((MeasureTheory.measure_mono (Set.subset_univ G)).trans_lt
    (by rw [hu]; exact ENNReal.one_lt_top))

omit [Field F] in
theorem mem_admissibleCodes {D : Finset (Direction F)} {j : ℕ}
    {z : IncidenceCode F} (hz : z ∈ admissibleCodes D j) :
    Function.Injective z.1.1 ∧ (∀ i, z.1.1 i ≠ z.2) ∧
      (exposedTupleIndices (⟨z.1.1,z.1.2⟩ : FourTuple F) D).card = j := by
  obtain ⟨hcode,hinj,hg⟩ := Finset.mem_filter.mp hz
  refine ⟨hinj,hg,?_⟩
  have h := (Finset.mem_filter.mp
    (Finset.mem_product.mp (Finset.mem_product.mp hcode).1).1).2
  exact h

omit [Field F] in
theorem generators_fresh_of_mem_zero {D : Finset (Direction F)}
    {z : IncidenceCode F} (hz : z ∈ admissibleCodes D 0) :
    ∀ i, z.1.1 i ∉ D := by
  have hzero := Finset.card_eq_zero.mp (mem_admissibleCodes hz).2.2
  intro i hi
  have hmem : i ∈ exposedTupleIndices (⟨z.1.1,z.1.2⟩ : FourTuple F) D := by
    simpa [exposedTupleIndices] using hi
  rw [hzero] at hmem
  exact Finset.notMem_empty i hmem

omit [Field F] in
theorem card_admissibleCodes_le (D : Finset (Direction F)) (j : ℕ) :
    (admissibleCodes D j).card ≤
      (16 * (Nat.choose 4 j * D.card ^ j *
        Fintype.card (Direction F) ^ (4-j))) * Fintype.card (Direction F) := by
  calc
    _ ≤ ((tupleCodesWithOldCount D j).product
        (Finset.univ : Finset (Direction F))).card := Finset.card_filter_le _ _
    _ = (tupleCodesWithOldCount D j).card * Fintype.card (Direction F) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (card_tupleCodesWithOldCount_le D j)

omit [DecidableEq F] in
private theorem card_direction_le_twice :
    (Fintype.card (Direction F) : ℝ) ≤ 2 * Fintype.card F := by
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have h : Fintype.card (Direction F) ≤ 2 * Fintype.card F := by
    simp only [Direction, Fintype.card_option]
    omega
  exact_mod_cast h

theorem sum_zero_le (D : Finset (Direction F)) (f : IncidenceCode F → ℝ)
    (A : ℝ) (hA : 0 ≤ A)
    (hf : ∀ z ∈ admissibleCodes D 0, f z ≤ A * (Fintype.card F : ℝ)⁻¹^5) :
    (∑ z ∈ admissibleCodes D 0, f z) ≤ 512 * A := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : ((admissibleCodes D 0).card : ℝ) ≤
      16 * (Fintype.card (Direction F) : ℝ)^5 := by
    have hn : (admissibleCodes D 0).card ≤ 16 * Fintype.card (Direction F)^5 := by
      calc
        _ ≤ _ := card_admissibleCodes_le D 0
        _ = _ := by norm_num only [Nat.choose_zero_right, pow_zero, Nat.sub_zero]; ring
    exact_mod_cast hn
  calc
    _ ≤ ∑ _z ∈ admissibleCodes D 0, A * (Fintype.card F : ℝ)⁻¹^5 :=
      Finset.sum_le_sum hf
    _ = ((admissibleCodes D 0).card : ℝ) * (A * (Fintype.card F : ℝ)⁻¹^5) := by simp
    _ ≤ (16 * (Fintype.card (Direction F) : ℝ)^5) *
        (A * (Fintype.card F : ℝ)⁻¹^5) := by gcongr
    _ ≤ (16 * (2 * (Fintype.card F : ℝ))^5) *
        (A * (Fintype.card F : ℝ)⁻¹^5) := by
      gcongr
      exact card_direction_le_twice
    _ = _ := by field_simp; ring

theorem sum_one_le (D : Finset (Direction F)) (f : IncidenceCode F → ℝ)
    (A : ℝ) (hA : 0 ≤ A)
    (hf : ∀ z ∈ admissibleCodes D 1, f z ≤ A * (Fintype.card F : ℝ)⁻¹^4) :
    (∑ z ∈ admissibleCodes D 1, f z) ≤ 1024 * A * (D.card : ℝ) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : ((admissibleCodes D 1).card : ℝ) ≤
      64 * (D.card : ℝ) * (Fintype.card (Direction F) : ℝ)^4 := by
    have hn : (admissibleCodes D 1).card ≤
        64 * D.card * Fintype.card (Direction F)^4 := by
      calc
        _ ≤ _ := card_admissibleCodes_le D 1
        _ = _ := by norm_num only [Nat.choose_one_right, pow_one, Nat.reduceSub]; ring
    exact_mod_cast hn
  calc
    _ ≤ ∑ _z ∈ admissibleCodes D 1, A * (Fintype.card F : ℝ)⁻¹^4 :=
      Finset.sum_le_sum hf
    _ = ((admissibleCodes D 1).card : ℝ) * (A * (Fintype.card F : ℝ)⁻¹^4) := by simp
    _ ≤ (64 * (D.card : ℝ) * (Fintype.card (Direction F) : ℝ)^4) *
        (A * (Fintype.card F : ℝ)⁻¹^4) := by gcongr
    _ ≤ (64 * (D.card : ℝ) * (2 * (Fintype.card F : ℝ))^4) *
        (A * (Fintype.card F : ℝ)⁻¹^4) := by
      gcongr
      exact card_direction_le_twice
    _ = _ := by field_simp; ring

theorem code_probability_le_alignment (D : Finset (Direction F)) (a : MergedPairs F)
    (P : Direction F → (Fin 4 → Point F) → Prop) (z : IncidenceCode F) :
    probability D a (codeEvent P z) ≤ probability D a
      {M | (∃ c, ∀ i, OnLine (tuplePoint M ⟨z.1.1,z.1.2⟩ i) (z.2,c)) ∧
        P z.2 (tuplePoint M ⟨z.1.1,z.1.2⟩)} := by
  exact probability_mono D a (fun _ h => ⟨h.1.1,h.2⟩)

theorem two_lines_sum_zero_le (D : Finset (Direction F)) (a : MergedPairs F)
    (L K : Line F) (hLK : L ≠ K) :
    incidenceSum D a 0 (hitsTwoLines L K) ≤ 6144 := by
  change (∑ z ∈ admissibleCodes D 0, _) ≤ _
  refine (sum_zero_le D (fun z => probability D a (codeEvent (hitsTwoLines L K) z))
    12 (by norm_num) ?_).trans (by norm_num)
  intro z hz
  have hb := CandidateFreshIncidence.conditional_tuple_hits_two_lines_probability_le
    (⟨z.1.1,z.1.2⟩ : FourTuple F) (mem_admissibleCodes hz).1 D a
    (generators_fresh_of_mem_zero hz) z.2 L K hLK
  exact (code_probability_le_alignment D a _ z).trans hb

theorem two_lines_sum_one_le (D : Finset (Direction F)) (a : MergedPairs F)
    (L K : Line F) (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L) :
    incidenceSum D a 1 (hitsTwoLines L K) ≤ 4096 * (D.card : ℝ) := by
  change (∑ z ∈ admissibleCodes D 1, _) ≤ _
  refine (sum_one_le D (fun z => probability D a (codeEvent (hitsTwoLines L K) z))
    4 (by norm_num) ?_).trans (by norm_num)
  intro z hz
  have hz' := mem_admissibleCodes hz
  have hb := CandidatePartialPointIncidence.conditional_tuple_hits_two_lines_probability_le
    (⟨z.1.1,z.1.2⟩ : FourTuple F) hz'.1 D a (by omega) z.2 hz'.2.1 L K havoid
  exact (code_probability_le_alignment D a _ z).trans hb

end
end Balanced.CandidateIncidenceSums

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateIncidenceRootSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidenceSums

noncomputable section
open scoped Classical BigOperators
open PartialAlignment TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem rootCode_injective : Function.Injective (rootCode (F := F)) := by
  rintro ⟨g,a⟩ ⟨h,b⟩ hab
  have ht : g = h := congrArg Prod.snd hab
  cases ht
  apply congrArg (Sigma.mk g)
  apply Prod.ext
  · apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    exact congrFun (congrArg (fun z : IncidenceCode F => z.1.1) hab) i
  · exact congrArg (fun z : IncidenceCode F => z.1.2) hab

omit [Field F] in
theorem rootCode_mem {D : Finset (Direction F)} {j : ℕ}
    {r : TargetPrescription F} (hr : r ∈ rootCodes D j) :
    rootCode r ∈ admissibleCodes D j := by
  have hc := (Finset.mem_filter.mp hr).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_,Finset.mem_univ _⟩,
    r.2.injective, fun i => (r.2.1 i).2⟩
  refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,
    Finset.mem_univ _⟩
  exact hc

omit [Field F] in
theorem rootCode_surjective_on {D : Finset (Direction F)} {j : ℕ}
    {z : IncidenceCode F} (hz : z ∈ admissibleCodes D j) :
    ∃ r ∈ rootCodes D j, rootCode r = z := by
  have hz' := mem_admissibleCodes hz
  let a : RootPrescription z.2 :=
    (⟨fun i => ⟨z.1.1 i,hz'.2.1 i⟩,
      fun i k h => hz'.1 (congrArg Subtype.val h)⟩,z.1.2)
  refine ⟨⟨z.2,a⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
  · exact hz'.2.2
  · rfl

theorem rootIncidenceSum_eq_incidenceSum (D : Finset (Direction F))
    (a : MergedPairs F) (j : ℕ) (P : Direction F → (Fin 4 → Point F) → Prop) :
    rootIncidenceSum D a j P = incidenceSum D a j P := by
  unfold rootIncidenceSum incidenceSum
  apply Finset.sum_bij (fun r _ => rootCode r)
  · intro r hr
    exact rootCode_mem hr
  · intro r hr s hs h
    exact rootCode_injective h
  · intro z hz
    obtain ⟨r,hr,heq⟩ := rootCode_surjective_on hz
    exact ⟨r,hr,heq⟩
  · intro r hr
    rfl

theorem rootIncidenceSum_eq_iterated (D : Finset (Direction F))
    (a : MergedPairs F) (j : ℕ) (P : Direction F → (Fin 4 → Point F) → Prop) :
    rootIncidenceSum D a j P = ∑ g : Direction F, ∑ r : RootPrescription g,
      if (exposedTupleIndices r.tuple D).card = j then probability D a
        {M | SuccessfulPositions (tuplePoint M r.tuple) g ∧
          P g (tuplePoint M r.tuple)} else 0 := by
  unfold rootIncidenceSum rootCodes
  rw [Finset.sum_filter, Fintype.sum_sigma]

theorem root_two_lines_sum_zero_le (D : Finset (Direction F)) (a : MergedPairs F)
    (L K : Line F) (hLK : L ≠ K) :
    rootIncidenceSum D a 0 (hitsTwoLines L K) ≤ 6144 := by
  rw [rootIncidenceSum_eq_incidenceSum]
  exact two_lines_sum_zero_le D a L K hLK

theorem root_two_lines_sum_one_le (D : Finset (Direction F)) (a : MergedPairs F)
    (L K : Line F) (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L) :
    rootIncidenceSum D a 1 (hitsTwoLines L K) ≤ 4096 * (D.card : ℝ) := by
  rw [rootIncidenceSum_eq_incidenceSum]
  exact two_lines_sum_one_le D a L K havoid

end
end Balanced.CandidateIncidenceSums

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternMomentTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced.PatternTails

variable (P : PatternModel)

theorem fixed_tail_le_moment (K : Finset P.Color) (x : P.Sample)
    (f : P.Sample → ℝ) (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω)
    (B : ℝ) (hfB : ∀ ω, f ω ≤ B) (t : ℝ) (ht : 0 < t) (n : ℕ) :
    P.measure.real {ω | t ≤ f (P.fixCoordinates K x ω)} ≤
      P.fixedExpectation K x (fun ω => f ω ^ n) / t ^ n := by
  have hi : Integrable (fun ω => f (P.fixCoordinates K x ω) ^ n) P.measure := by
    apply P.integrable_fixed_of_bound K x (hf.pow_const n) (B ^ n)
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hf0 ω) n)]
    exact pow_le_pow_left₀ (hf0 ω) (hfB ω) n
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => pow_nonneg (hf0 (P.fixCoordinates K x ω)) n))
    hi (t ^ n)
  have hsub : {ω | t ≤ f (P.fixCoordinates K x ω)} ⊆
      {ω | t ^ n ≤ f (P.fixCoordinates K x ω) ^ n} := by
    intro ω hω
    exact pow_le_pow_left₀ ht.le hω n
  apply (le_div_iff₀ (pow_pos ht n)).mpr
  calc
    P.measure.real {ω | t ≤ f (P.fixCoordinates K x ω)} * t ^ n ≤
        P.measure.real {ω | t ^ n ≤ f (P.fixCoordinates K x ω) ^ n} * t ^ n :=
      mul_le_mul_of_nonneg_right (measureReal_mono hsub) (pow_nonneg ht.le n)
    _ ≤ P.fixedExpectation K x (fun ω => f ω ^ n) := by
      simpa only [mul_comm, PatternModel.fixedExpectation] using hm

lemma count_mem_Icc (ω : P.Sample) :
    P.count ω ∈ Set.Icc (0 : ℝ) (Fintype.card P.Label : ℝ) := by
  constructor
  · exact Finset.sum_nonneg (fun a _ => P.indicator_nonneg a ω)
  · calc
      P.count ω ≤ ∑ _a : P.Label, (1 : ℝ) :=
        Finset.sum_le_sum (fun a _ => P.indicator_le_one a ω)
      _ = _ := by simp

end Balanced.PatternTails

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternAllowedGate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced.PatternModel

universe u
noncomputable section
attribute [local instance] Classical.propDecidable

variable (P : PatternModel.{u}) (K₀ : Finset P.Color)
    (S : Set P.Sample) (hS : MeasurableSet S)
    (hdepends : ∀ x y, (∀ c ∈ K₀, x c = y c) → (x ∈ S ↔ y ∈ S))

theorem gateInitialEvent_support_card_le (r : ℕ)
    (hr : ∀ a, (P.support a).card ≤ r) (a : P.Label) :
    ((P.gateInitialEvent K₀ S hS hdepends).support a).card ≤ K₀.card + r :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add_left (hr a) _)

include hdepends in

theorem mem_allowed_fix_union_iff (K : Finset P.Color) (x ω : P.Sample) :
    P.fixCoordinates (K₀ ∪ K) x ω ∈ S ↔ x ∈ S := by
  apply hdepends
  intro c hc
  simp [fixCoordinates, Finset.mem_union_left K hc]

@[simp] theorem gateInitialEvent_fixed_count (K : Finset P.Color) (x : P.Sample) :
    (P.gateInitialEvent K₀ S hS hdepends).fixedExpectation (K₀ ∪ K) x
      (P.gateInitialEvent K₀ S hS hdepends).count =
      if x ∈ S then P.fixedExpectation (K₀ ∪ K) x P.count else 0 := by
  change (∫ ω : P.Sample,
    (P.gateInitialEvent K₀ S hS hdepends).count (P.fixCoordinates (K₀ ∪ K) x ω)
      ∂P.measure) = _
  by_cases hx : x ∈ S
  · rw [ite_eq_left hx]
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [P.gateInitialEvent_count,
      ite_eq_left ((P.mem_allowed_fix_union_iff K₀ S hdepends K x ω).mpr hx)]
  · rw [ite_eq_right hx]
    have hz : (fun ω : P.Sample =>
        (P.gateInitialEvent K₀ S hS hdepends).count (P.fixCoordinates (K₀ ∪ K) x ω)) =
        fun _ => 0 := by
      funext ω
      rw [P.gateInitialEvent_count, ite_eq_right]
      exact fun hω => hx ((P.mem_allowed_fix_union_iff K₀ S hdepends K x ω).mp hω)
    rw [hz, integral_zero]

@[simp] theorem gateInitialEvent_fixed_overlap (K : Finset P.Color) (x : P.Sample) :
    (P.gateInitialEvent K₀ S hS hdepends).fixedExpectation (K₀ ∪ K) x
      ((P.gateInitialEvent K₀ S hS hdepends).overlapCount K₀ K) =
      if x ∈ S then P.fixedExpectation (K₀ ∪ K) x (P.overlapCount K₀ K) else 0 := by
  change (∫ ω : P.Sample,
    (P.gateInitialEvent K₀ S hS hdepends).overlapCount K₀ K
      (P.fixCoordinates (K₀ ∪ K) x ω) ∂P.measure) = _
  by_cases hx : x ∈ S
  · rw [ite_eq_left hx]
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [P.gateInitialEvent_overlapCount,
      ite_eq_left ((P.mem_allowed_fix_union_iff K₀ S hdepends K x ω).mpr hx)]
  · rw [ite_eq_right hx]
    have hz : (fun ω : P.Sample =>
        (P.gateInitialEvent K₀ S hS hdepends).overlapCount K₀ K
          (P.fixCoordinates (K₀ ∪ K) x ω)) = fun _ => 0 := by
      funext ω
      rw [P.gateInitialEvent_overlapCount, ite_eq_right]
      exact fun hω => hx ((P.mem_allowed_fix_union_iff K₀ S hdepends K x ω).mp hω)
    rw [hz, integral_zero]

end
end Balanced.PatternModel

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateTwoLineMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidenceSums

noncomputable section
open scoped Classical BigOperators
open PartialAlignment TupleAlignment CandidateExposure CandidateIncidence MeasureTheory

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

theorem rootIncidenceSum_eq_tupleIncidenceSum (D : Finset (Direction F))
    (a : MergedPairs F) (j : ℕ) (P : Direction F → (Fin 4 → Point F) → Prop) :
    rootIncidenceSum D a j P = tupleIncidenceSum D a j P := by
  rw [rootIncidenceSum_eq_iterated]
  unfold tupleIncidenceSum
  apply Finset.sum_congr rfl
  intro g _
  let f : FourTuple F → ℝ := fun T =>
    if (exposedTupleIndices T D).card = j then conditionalProbability D a
      {M | M ∈ successfulInDirection T g ∧ P g (tuplePoint M T)} else 0
  have he := Equiv.sum_comp (eligibleTupleEquivRootPrescription g)
    (fun r : RootPrescription g => f r.tuple)
  simp only [equivRootPrescription_tuple] at he
  have hs := Finset.sum_subtype (eligibleTuples g)
    (p := fun T => T ∈ eligibleTuples g) (F := inferInstance) (fun _ => Iff.rfl) f
  have h := (hs.trans he).symm
  simpa only [f, tuplesWithExposure, Finset.sum_filter, probability,
    conditionalProbability, exposedLaw, successfulInDirection, alignedInDirection,
    SuccessfulPositions, Set.mem_ofPred_eq] using h

theorem tupleIncidenceSum_le_success (D : Finset (Direction F))
    (a : MergedPairs F) (j : ℕ) (P : Direction F → (Fin 4 → Point F) → Prop) :
    tupleIncidenceSum D a j P ≤ ∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j,
      conditionalProbability D a (successfulInDirection T g) := by
  apply Finset.sum_le_sum
  intro g _
  apply Finset.sum_le_sum
  intro T _
  exact conditionalProbability_mono D a (fun _ h => h.1)

theorem allModel_fixed_count_eq_sum_strata
    (D : Finset (Direction F)) (a : MergedPairs F)
    (P : Direction F → (Fin 4 → Point F) → Prop) :
    (allModel (fun _ g p => P g p)).fixedExpectation D a
      (allModel (fun _ g p => P g p)).count =
      ∑ j ∈ Finset.range 5, tupleIncidenceSum D a j P := by
  rw [allModel_fixed_count]
  unfold tupleIncidenceSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (s := eligibleTuples g) (t := Finset.range 5)
    (g := fun T => (exposedTupleIndices T D).card)
    (fun T _ => Finset.mem_range.mpr (by
      have h := Finset.card_le_univ (exposedTupleIndices T D)
      simp only [Fintype.card_fin] at h
      omega))
    (fun T => conditionalProbability D a
      {M | M ∈ successfulInDirection T g ∧ P g (tuplePoint M T)})

theorem twoLine_stratum_le (D : Finset (Direction F)) (a : MergedPairs F)
    (L K : Line F) (hLK : L ≠ K)
    (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L)
    (m j : ℕ) (hD : D.card ≤ m) (hj : j < 5) :
    tupleIncidenceSum D a j (hitsTwoLines L K) ≤ (8192 * (m+1)^4 : ℝ) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hDreal : (D.card : ℝ) ≤ m := by exact_mod_cast hD
  have hbase : (1 : ℝ) ≤ (m : ℝ)+1 := by linarith
  have hpow : (1 : ℝ) ≤ ((m : ℝ)+1)^4 := one_le_pow₀ hbase
  have hmpow : (m : ℝ) ≤ ((m : ℝ)+1)^4 := by
    have h := pow_le_pow_right₀ hbase (show 1 ≤ 4 by omega)
    simp only [pow_one] at h
    linarith
  interval_cases j
  · rw [← rootIncidenceSum_eq_tupleIncidenceSum]
    exact (root_two_lines_sum_zero_le D a L K hLK).trans (by linarith)
  · rw [← rootIncidenceSum_eq_tupleIncidenceSum]
    exact (root_two_lines_sum_one_le D a L K havoid).trans (by nlinarith)
  · exact (tupleIncidenceSum_le_success D a 2 _).trans
      (sum_targets_success_two_three_le D a m 2 hD (Or.inl rfl))
  · exact (tupleIncidenceSum_le_success D a 3 _).trans
      (sum_targets_success_two_three_le D a m 3 hD (Or.inr rfl))
  · apply (tupleIncidenceSum_le_success D a 4 _).trans
    apply (sum_targets_success_four_le D a).trans
    have hp : (D.card : ℝ)^4 ≤ ((m : ℝ)+1)^4 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 4
    nlinarith

theorem twoLine_model_fixed_count_le (D : Finset (Direction F))
    (a : MergedPairs F) (L K : Line F) (hLK : L ≠ K)
    (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L)
    (m : ℕ) (hD : D.card ≤ m) :
    (allModel (twoLineTest L K)).fixedExpectation D a
      (allModel (twoLineTest L K)).count ≤ (40960 * (m+1)^4 : ℝ) := by
  rw [show twoLineTest L K = (fun _ g p => hitsTwoLines L K g p) from rfl,
    allModel_fixed_count_eq_sum_strata]
  calc
    _ ≤ ∑ _j ∈ Finset.range 5, (8192 * (m+1)^4 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact twoLine_stratum_le D a L K hLK havoid m j hD (Finset.mem_range.mp hj)
    _ = _ := by simp; ring

omit [Field F] [Fintype F] in
theorem twoLineInitial_card_le (L K : Line F) : (twoLineInitial L K).card ≤ 2 := by
  calc
    _ ≤ ({K.1} : Finset (Direction F)).card + 1 := Finset.card_insert_le _ _
    _ = 2 := by simp

attribute [local instance] OAI.Balanced.CandidateIncidenceSums.twoLineMeasurableSpace
theorem twoLineModel_measure (L K : Line F) :
    (twoLineModel L K).measure = (offsetLaw F).toMeasure := allModel_measure (twoLineTest L K)

theorem twoLineModel_count (L K : Line F) (M : MergedPairs F) :
    (twoLineModel L K).count M =
      if M ∈ twoLineAllowed L K then (allModel (twoLineTest L K)).count M else 0 :=
  (allModel (twoLineTest L K)).gateInitialEvent_count (twoLineInitial L K)
    (twoLineAllowed L K) (Set.toFinite _).measurableSet (twoLineAllowed_depends L K) M

theorem twoLineModel_support_card (L K : Line F) (r : (twoLineModel L K).Label) :
    ((twoLineModel L K).support r).card ≤ 6 := by
  have h := (allModel (twoLineTest L K)).gateInitialEvent_support_card_le
    (twoLineInitial L K) (twoLineAllowed L K) (Set.toFinite _).measurableSet
    (twoLineAllowed_depends L K) 4 (fun a => (allModel_support_card _ a).le) r
  exact h.trans (by have := twoLineInitial_card_le L K; omega)

theorem twoLineModel_fixed_initial_count_le (L K : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (twoLineModel L K).fixedExpectation (twoLineInitial L K ∪ D) a
      (twoLineModel L K).count ≤ (40960 * (m+3)^4 : ℝ) := by
  change ((allModel (twoLineTest L K)).gateInitialEvent _ _ _ _).fixedExpectation
    _ _ _ ≤ _
  rw [PatternModel.gateInitialEvent_fixed_count]
  split_ifs with ha
  · have havoid : ∀ d ∈ twoLineInitial L K ∪ D, ∀ b, constituent a d b ≠ L := by
      intro d _ b heq
      have hd : d = L.1 := congrArg Prod.fst heq
      have hb : a d b = L.2 := congrArg Prod.snd heq
      rw [hd] at hb
      exact ha.2.1 b hb
    have hc : (twoLineInitial L K ∪ D).card ≤ m+2 :=
      (Finset.card_union_le _ _).trans (by have := twoLineInitial_card_le L K; omega)
    have h := twoLine_model_fixed_count_le (twoLineInitial L K ∪ D) a L K ha.1
      havoid (m+2) hc
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring
  · positivity

theorem twoLineModel_fixed_count_le (L K : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (twoLineModel L K).fixedExpectation D a (twoLineModel L K).count ≤
      (40960 * (m+3)^4 : ℝ) := by
  let P := twoLineModel L K
  have hbound (y : P.Sample) : P.fixedExpectation (D ∪ twoLineInitial L K) y
      P.count ≤ (40960 * (m+3)^4 : ℝ) := by
    exact (congrArg (fun E : Finset (Direction F) =>
      (twoLineModel L K).fixedExpectation E y (twoLineModel L K).count ≤
        (40960 * (m+3)^4 : ℝ)) (Finset.union_comm (twoLineInitial L K) D)).mp
          (twoLineModel_fixed_initial_count_le L K D y m hD)
  have h := P.fixedExpectation_mul_le_of_fixedBounds D (twoLineInitial L K) a
    (fun _ => 1) P.count (40960 * (m+3)^4 : ℝ) 1 (Fintype.card P.Label)
    (by positivity) measurable_const P.measurable_count
    (fun _ => zero_le_one) (fun M => (PatternTails.count_mem_Icc P M).1)
    (fun _ => le_rfl) (fun M => (PatternTails.count_mem_Icc P M).2)
    (by intros; rfl) hbound
  have hconst : P.fixedExpectation D a (fun _ => (1 : ℝ)) = 1 := by
    simp [PatternModel.fixedExpectation, PatternModel.measure]
  rw [hconst, mul_one] at h
  simpa only [one_mul] using h

theorem twoLineModel_fixed_moment_le (L K : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m s : ℕ) (hD : D.card ≤ m) :
    (twoLineModel L K).fixedExpectation D a (fun M => (twoLineModel L K).count M ^ s) ≤
      (40960 * (((m + (s-1)*6 : ℕ) : ℝ)+3)^4)^s := by
  apply (twoLineModel L K).fixed_moment_le_pow D a 6 s _ (by positivity)
    (twoLineModel_support_card L K)
  intro E hE y
  exact twoLineModel_fixed_count_le L K (D ∪ E) y (m+(s-1)*6)
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hD hE))

theorem twoLineModel_moment_le (L K : Line F) (s : ℕ) :
    (∫ M, (twoLineModel L K).count M ^ s ∂(offsetLaw F).toMeasure) ≤
      (40960 * ((((s-1)*6 : ℕ) : ℝ)+3)^4)^s := by
  have h := twoLineModel_fixed_moment_le L K ∅ (fun _ _ => 0) 0 s (by simp)
  simp only [PatternModel.fixedExpectation, zero_add] at h
  rw [twoLineModel_measure] at h
  exact h

end
end Balanced.CandidateIncidenceSums

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateTwoLineFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateTwoLineFamily

noncomputable section
open scoped Classical BigOperators
open CandidateIncidenceSums CandidateIncidence CandidateRetentionTransport TupleAlignment
open MeasureTheory

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in
theorem nonconstituent_iff (M : MergedPairs F) (L : Line F) :
    L ∉ constituentLines M ↔ ∀ b, M L.1 b ≠ L.2 := by
  constructor
  · intro h b hb
    apply h
    exact Finset.mem_image.mpr ⟨(L.1,b),Finset.mem_univ _,Prod.ext rfl hb⟩
  · intro h hm
    obtain ⟨⟨d,b⟩,_,heq⟩ := Finset.mem_image.mp hm
    have hd : d = L.1 := congrArg Prod.fst heq
    have hb : M d b = L.2 := congrArg Prod.snd heq
    rw [hd] at hb
    exact h b hb

omit [Field F] in
theorem allowed_iff (L K : Line F) (M : MergedPairs F) :
    M ∈ twoLineAllowed L K ↔
      L ≠ K ∧ L ∉ constituentLines M ∧ K ∉ constituentLines M := by
  simp only [twoLineAllowed, Set.mem_ofPred_eq, nonconstituent_iff]

omit [Fintype F] in
theorem positions_iff_points (M : MergedPairs F) (L K : Line F) (C : SplitChoice F)
    (hinj : Function.Injective (tuplePoint M C.tuple)) :
    hitsTwoLines L K C.line.1 (tuplePoint M C.tuple) ↔
      ∃ p ∈ designated M C, ∃ r ∈ designated M C,
        p ≠ r ∧ OnLine p L ∧ OnLine r K := by
  constructor
  · rintro ⟨i,j,hij,hi,hj⟩
    refine ⟨tuplePoint M C.tuple i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,
      tuplePoint M C.tuple j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,
      fun he => hij (hinj he),hi,hj⟩
  · rintro ⟨p,hp,r,hr,hpr,hpL,hrK⟩
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hr
    exact ⟨i,j,fun he => hpr (congrArg (tuplePoint M C.tuple) he),hpL,hrK⟩

theorem model_count_eq_test (L K : Line F) (M : MergedPairs F) :
    (twoLineModel L K).count M =
      (CandidateIncidenceTests.count M (Sum.inr (Sum.inr (Sum.inl (L,K)))) : ℝ) := by
  rw [twoLineModel_count, allModel_count_eq_successfulTest]
  simp only [allowed_iff, CandidateIncidenceTests.count, Nat.cast_ite, Nat.cast_zero]
  split_ifs with h
  · apply congrArg (fun s : Finset (SplitChoice F) => (s.card : ℝ))
    ext C
    simp only [mem_successfulTest]
    apply and_congr_right
    intro hC
    exact positions_iff_points M L K C ((mem_successfulChoices M C).mp hC).2.2.1
  · rfl

end
end Balanced.CandidateTwoLineFamily

namespace Balanced.CandidateIncidenceTests

noncomputable section
open scoped Classical
open MeasureTheory
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

attribute [local instance] OAI.Balanced.CandidateIncidenceTests.twoLineRawMeasurableSpace
theorem twoLine_raw_moment_le (L K : Line F) (s : ℕ) :
    (∫ M, (count M (Sum.inr (Sum.inr (Sum.inl (L,K)))) : ℝ)^s
      ∂(offsetLaw F).toMeasure) ≤
      (40960 * ((((s-1)*6 : ℕ) : ℝ)+3)^4)^s := by
  have h := CandidateIncidenceSums.twoLineModel_moment_le L K s
  simpa only [CandidateTwoLineFamily.model_count_eq_test] using h

end
end Balanced.CandidateIncidenceTests

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
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternTailAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Balanced.PatternTails

universe u v w

theorem polynomial_union_tail_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : ι → Set Ω)
    (q : ℝ) (hq : 0 < q) (d k : ℕ) (A C : ℝ) (hC : 0 ≤ C)
    (hcard : (Fintype.card ι : ℝ) ≤ A * q ^ d)
    (htail : ∀ i, μ.real (E i) ≤ C / q ^ (d + k)) :
    μ.real (⋃ i, E i) ≤ A * C / q ^ k := by
  calc
    μ.real (⋃ i, E i) ≤ ∑ i, μ.real (E i) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : ι, C / q ^ (d + k) := Finset.sum_le_sum (fun i _ => htail i)
    _ = (Fintype.card ι : ℝ) * (C / q ^ (d + k)) := by simp
    _ ≤ (A * q ^ d) * (C / q ^ (d + k)) :=
      mul_le_mul_of_nonneg_right hcard (div_nonneg hC (pow_nonneg hq.le _))
    _ = A * C / q ^ k := by
      rw [pow_add]
      field_simp

end Balanced.PatternTails

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateIncidenceProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology Classical

namespace Balanced.CandidateIncidenceTests

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

attribute [local instance] OAI.Balanced.CandidateIncidenceTests.incidenceMeasurableSpace
theorem small_test_tail_le (t : Test F) (C : ℝ)
    (hmom : (∫ M : MergedPairs F, (count M t : ℝ) ^ 500
      ∂(offsetLaw F).toMeasure) ≤ C) :
    (offsetLaw F).toMeasure.real
      {M | (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤ (count M t : ℝ)} ≤
        C / (Fintype.card F : ℝ) ^ 5 := by
  let P := TupleAlignment.rootPatternModel (none : Direction F)
  let x : MergedPairs F := fun _ _ => 0
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hpow : ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ)) ^ 500 =
      (Fintype.card F : ℝ) ^ 5 := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    norm_num
  have h := PatternTails.fixed_tail_le_moment P ∅ x
    (fun M => (count M t : ℝ)) (measurable_of_finite _)
    (fun _ => Nat.cast_nonneg _) (Fintype.card (SplitChoice F))
    (fun M => by exact_mod_cast count_le M t)
    ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ))
    (Real.rpow_pos_of_pos hq _) 500
  simp only [PatternModel.fixedExpectation] at h
  rw [TupleAlignment.rootPatternModel_measure] at h
  exact (h.trans (div_le_div_of_nonneg_right hmom (by positivity))).trans_eq
    (by rw [hpow])

theorem small_bad_probability_le (C : ℝ) (hC : 0 ≤ C)
    (hmom : ∀ t : Test F, (∫ M : MergedPairs F, (count M t : ℝ) ^ 500
      ∂(offsetLaw F).toMeasure) ≤ C) :
    offsetEventProbability (F := F)
      {M | ¬ SmallGood M (Nat.ceil ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ)))} ≤
        15 * C / Fintype.card F := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hc : (Fintype.card (Test F) : ℝ) ≤ 15 * (Fintype.card F : ℝ) ^ 4 := by
    exact_mod_cast card_test_le (F := F)
  have hu := PatternTails.polynomial_union_tail_le (offsetLaw F).toMeasure
    (fun t : Test F =>
      {M | (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤ (count M t : ℝ)})
    (Fintype.card F) hq 4 1 15 C hC hc (fun t => small_test_tail_le t C (hmom t))
  have hsub : {M : MergedPairs F |
      ¬ SmallGood M (Nat.ceil ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ)))} ⊆
      ⋃ t : Test F,
        {M | (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤ (count M t : ℝ)} := by
    intro M hM
    obtain ⟨t, ht⟩ := not_forall.mp hM
    refine Set.mem_iUnion.mpr ⟨t, ?_⟩
    have hn : Nat.ceil ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ)) ≤ count M t :=
      Nat.le_of_lt (Nat.lt_of_not_ge ht)
    change (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤ (count M t : ℝ)
    exact (Nat.le_ceil ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ))).trans
      (by exact_mod_cast hn)
  unfold offsetEventProbability
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (Set.toFinite _).measurableSet]
  exact (measureReal_mono hsub).trans (by simpa only [pow_one] using hu)

theorem tendsto_smallGood_of_moments
    (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    (hmom : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ t : Test (F n),
      (∫ M : MergedPairs (F n), (count M t : ℝ) ^ 500
        ∂(offsetLaw (F n)).toMeasure) ≤ C) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))})
      atTop (𝓝 1) := by
  obtain ⟨C, hC, hmom⟩ := hmom
  have hbad : Tendsto (fun n => offsetEventProbability (F := F n)
      {M | ¬ SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))})
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
    · filter_upwards [hmom] with n hn
      exact small_bad_probability_le C hC hn
    · simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
        ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp hq).const_mul
          (15 * C)
  have hp (n : ℕ) : offsetEventProbability (F := F n)
      {M | SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))} =
      1 - offsetEventProbability (F := F n)
      {M | ¬ SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))} := by
    simpa only [Set.compl_ofPred, not_not, offsetEventProbability] using
      pmf_outerReal_compl (offsetLaw (F n))
        {M | ¬ SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))}
  simp_rw [hp]
  simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hbad

end Balanced.CandidateIncidenceTests

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateSmallIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Balanced.CandidateIncidenceTests

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

theorem smallMomentConstant_pos (s : ℕ) : 0 < smallMomentConstant s := by
  unfold smallMomentConstant
  exact lt_of_lt_of_le (by positivity) (le_max_left _ _)

attribute [local instance] OAI.Balanced.CandidateIncidenceTests.smallFamilyMeasurableSpace
theorem small_raw_moment_le (t : Test F) (s : ℕ) :
    (∫ M : MergedPairs F, (count M t : ℝ)^s ∂(offsetLaw F).toMeasure) ≤
      smallMomentConstant s := by
  unfold smallMomentConstant
  rcases t with p | (⟨p,l⟩ | (⟨l,k⟩ | (⟨d,e⟩ | ⟨g,l⟩)))
  · exact (point_raw_moment_le p s).trans (le_max_left _ _)
  · exact (pointLine_raw_moment_le p l s).trans (le_max_left _ _)
  · exact (twoLine_raw_moment_le l k s).trans
      (le_max_of_le_right (le_max_left _ _))
  · exact (generatorPair_raw_moment_le d e s).trans
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  · exact (lineHit_raw_moment_le g l s).trans
      (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))

theorem tendsto_smallGood_oai
    (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))})
      atTop (𝓝 1) := by
  apply tendsto_smallGood_of_moments F hq
  exact ⟨smallMomentConstant 500, (smallMomentConstant_pos 500).le,
    Eventually.of_forall (fun _ t => small_raw_moment_le t 500)⟩

end Balanced.CandidateIncidenceTests

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Balanced.CandidateIncidenceTests.tendsto_smallGood_oai.{u} := @OAI.Balanced.CandidateIncidenceTests.tendsto_smallGood_oai.{u}
