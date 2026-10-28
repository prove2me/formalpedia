-- Prove2me | solution 1 for OAI.Balanced.ExternalWitnessTail.candidateSlots_of_uniform_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:19:39.875542+00:00
-- url     : https://prove2.me/submissions/58fbf508-b604-4dce-b255-fbafe36d58cb

import Mathlib
import Definitions.Def_OAIQ63Br002
import Definitions.Def_OAIQ63Br003
import Theorems.Thm_OAI_Balanced_CandidateAbundanceAssembly_tendsto_square_fibers
import Theorems.Thm_OAI_Balanced_CandidateAbundanceAssembly_tendsto_successful_roots

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

end
end Balanced.CandidatePrescribed

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateConstituentTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidatePrescribed

noncomputable section
open scoped Classical
open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem exposedLaw_apply_eq_zero_of_ne (old : Finset (Direction F))
    (a M : MergedPairs F) (g : Direction F) (hg : g ∈ old)
    (hne : M g ≠ a g) : exposedLaw old a M = 0 := by
  apply PMF.filter_apply_eq_zero_of_notMem
  intro h
  exact hne (h g hg)

theorem expected_constituentTargetCodes_le (old : Finset (Direction F))
    (a : MergedPairs F) (g : Direction F) (hg : g ∈ old) :
    (∑ M : MergedPairs F,
      (exposedLaw old a M).toReal * ((constituentTargetCodes M g).card : ℝ)) ≤
        40960 * ((old.card : ℝ) + 1) ^ 4 := by
  have hpoint (M : MergedPairs F) :
      (exposedLaw old a M).toReal * ((constituentTargetCodes M g).card : ℝ) ≤
      (exposedLaw old a M).toReal *
        (((successfulCodes M (constituent a g false)).card : ℝ) +
          ((successfulCodes M (constituent a g true)).card : ℝ)) := by
    by_cases he : M g = a g
    · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      have h := Finset.card_union_le
        (successfulCodes M (constituent M g false))
        (successfulCodes M (constituent M g true))
      simpa only [constituentTargetCodes, constituent, he, Nat.cast_add] using
        (show (((successfulCodes M (constituent M g false) ∪
          successfulCodes M (constituent M g true)).card : ℕ) : ℝ) ≤
          ((successfulCodes M (constituent M g false)).card : ℝ) +
          ((successfulCodes M (constituent M g true)).card : ℝ) by exact_mod_cast h)
    · rw [exposedLaw_apply_eq_zero_of_ne old a M g hg he]
      simp
  calc
    _ ≤ ∑ M : MergedPairs F, (exposedLaw old a M).toReal *
        (((successfulCodes M (constituent a g false)).card : ℝ) +
          ((successfulCodes M (constituent a g true)).card : ℝ)) :=
      Finset.sum_le_sum (fun M _ => hpoint M)
    _ = (∑ M : MergedPairs F, (exposedLaw old a M).toReal *
        ((successfulCodes M (constituent a g false)).card : ℝ)) +
        ∑ M : MergedPairs F, (exposedLaw old a M).toReal *
          ((successfulCodes M (constituent a g true)).card : ℝ) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ 20480 * ((old.card : ℝ) + 1) ^ 4 +
        20480 * ((old.card : ℝ) + 1) ^ 4 :=
      add_le_add (expected_successfulCodes_le old a (constituent a g false))
        (expected_successfulCodes_le old a (constituent a g true))
    _ = _ := by ring

end
end Balanced.CandidatePrescribed

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateConstituentMoments
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidatePrescribed

noncomputable section
open scoped Classical BigOperators
open MeasureTheory ConditionalRestriction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem constituentTargetPatternModel_support_card (g : Direction F) (c : Code F) :
    ((constituentTargetPatternModel g).support c).card ≤ 5 := by
  change (insert g (generatorSet (⟨c.1,c.2⟩ : FourTuple F))).card ≤ 5
  have hi := Finset.card_insert_le g (generatorSet (⟨c.1,c.2⟩ : FourTuple F))
  have hg : (generatorSet (⟨c.1,c.2⟩ : FourTuple F)).card ≤ 4 := by
    exact (Finset.card_image_le).trans (by simp)
  omega

theorem constituentTargetPatternModel_count (g : Direction F) (M : MergedPairs F) :
    (constituentTargetPatternModel g).count M =
      ((constituentTargetCodes M g).card : ℝ) := by
  simp only [PatternModel.count, PatternModel.indicator,
    constituentTargetPatternModel, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [← Finset.sum_filter]
  erw [Finset.filter_mem_eq_of_subset (Finset.subset_univ _)]
  simp

attribute [local instance] OAI.Balanced.CandidatePrescribed.instMeasurableSpace_solutions
attribute [local instance] OAI.Balanced.CandidatePrescribed.instMeasurableSingletonClass_solutions
theorem constituentTargetPatternModel_fixedExpectation (g : Direction F)
    (old : Finset (Direction F)) (a : MergedPairs F) (f : MergedPairs F → ℝ) :
    (constituentTargetPatternModel g).fixedExpectation old a f =
      ∑ M : MergedPairs F, (exposedLaw old a M).toReal * f M := by
  have hfix : (constituentTargetPatternModel g).fixCoordinates old a =
      fixArray (fun d => d ∈ old) a := by
    funext M d
    simp only [PatternModel.fixCoordinates, fixArray]
    congr 1
  unfold PatternModel.fixedExpectation
  rw [hfix]
  change (∫ M, f (fixArray (fun d => d ∈ old) a M) ∂Measure.pi
    (fun _ : Direction F => (PMF.uniformOfFintype (Bool → F)).toMeasure)) = _
  rw [integral_fixArray_eq_filtered]
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  congr 1
  funext M
  congr 2
  simp only [exposedLaw, PartialAlignment.offsetLaw_eq_uniform]

theorem constituentTarget_fixed_count_le_of_mem (g : Direction F)
    (old : Finset (Direction F)) (a : MergedPairs F) (hg : g ∈ old) :
    (constituentTargetPatternModel g).fixedExpectation old a
      (constituentTargetPatternModel g).count ≤
        40960 * ((old.card : ℝ) + 1) ^ 4 := by
  erw [constituentTargetPatternModel_fixedExpectation]
  simp_rw [constituentTargetPatternModel_count]
  exact expected_constituentTargetCodes_le old a g hg

theorem constituentTarget_count_measurable (g : Direction F) :
    Measurable (constituentTargetPatternModel g).count := by
  change Measurable (fun M : MergedPairs F => (constituentTargetPatternModel g).count M)
  exact measurable_of_countable _

theorem constituentTarget_count_nonneg (g : Direction F) (M : MergedPairs F) :
    0 ≤ (constituentTargetPatternModel g).count M := by
  rw [constituentTargetPatternModel_count]
  positivity

theorem constituentTarget_count_le_card (g : Direction F) (M : MergedPairs F) :
    (constituentTargetPatternModel g).count M ≤ Fintype.card (Code F) := by
  rw [constituentTargetPatternModel_count]
  exact_mod_cast Finset.card_le_univ (constituentTargetCodes M g)

theorem constituentTarget_fixed_count_le (g : Direction F)
    (old : Finset (Direction F)) (a : MergedPairs F) :
    (constituentTargetPatternModel g).fixedExpectation old a
      (constituentTargetPatternModel g).count ≤
        40960 * ((old.card : ℝ) + 2) ^ 4 := by
  let P := constituentTargetPatternModel g
  have hbound (y : P.Sample) : P.fixedExpectation (old ∪ {g}) y P.count ≤
      40960 * ((old.card : ℝ) + 2) ^ 4 := by
    have h := constituentTarget_fixed_count_le_of_mem g (old ∪ {g}) y (by simp)
    apply h.trans
    have hcard : ((old ∪ {g}).card : ℝ) ≤ (old.card : ℝ) + 1 := by
      exact_mod_cast (show (old ∪ {g}).card ≤ old.card + 1 by
        simpa using Finset.card_union_le old {g})
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have h := P.fixedExpectation_mul_le_of_fixedBounds old {g} a
    (fun _ => 1) P.count (40960 * ((old.card : ℝ) + 2) ^ 4)
    1 (Fintype.card (Code F)) (by positivity)
    measurable_const (constituentTarget_count_measurable g)
    (fun _ => zero_le_one) (constituentTarget_count_nonneg g)
    (fun _ => le_rfl) (constituentTarget_count_le_card g)
    (by intros; rfl) hbound
  simpa [PatternModel.fixedExpectation, PatternModel.measure] using h

theorem constituentTarget_moment_le (g : Direction F)
    (old : Finset (Direction F)) (a : MergedPairs F) (s : ℕ) :
    (∑ M : MergedPairs F, (exposedLaw old a M).toReal *
      ((constituentTargetCodes M g).card : ℝ) ^ s) ≤
      (40960 * (((old.card + (s - 1) * 5 : ℕ) : ℝ) + 2) ^ 4) ^ s := by
  let P := constituentTargetPatternModel g
  have hbound (K : Finset P.Color) (hK : K.card ≤ (s - 1) * 5)
      (y : P.Sample) : P.fixedExpectation (old ∪ K) y P.count ≤
        40960 * (((old.card + (s - 1) * 5 : ℕ) : ℝ) + 2) ^ 4 := by
    apply (constituentTarget_fixed_count_le g (old ∪ K) y).trans
    have hc : (old ∪ K).card ≤ old.card + (s - 1) * 5 :=
      (Finset.card_union_le old K).trans (Nat.add_le_add_left hK _)
    gcongr
  have h := P.fixed_moment_le_pow old a 5 s
    (40960 * (((old.card + (s - 1) * 5 : ℕ) : ℝ) + 2) ^ 4)
    (by positivity) (constituentTargetPatternModel_support_card g) hbound
  erw [constituentTargetPatternModel_fixedExpectation] at h
  simpa only [P, constituentTargetPatternModel_count] using h

theorem constituentTarget_moment_le_of_card_le (g : Direction F)
    (old : Finset (Direction F)) (a : MergedPairs F) (m s : ℕ)
    (hm : old.card ≤ m) :
    (∑ M : MergedPairs F, (exposedLaw old a M).toReal *
      ((constituentTargetCodes M g).card : ℝ) ^ s) ≤
      (40960 * (((m + (s - 1) * 5 : ℕ) : ℝ) + 2) ^ 4) ^ s := by
  apply (constituentTarget_moment_le g old a s).trans
  gcongr

end
end Balanced.CandidatePrescribed

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_ValidChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced

variable {F : Type*} [Field F]

namespace SplitGeometry

theorem adjacent_symm {M : MergedPairs F} {S : Line F} {p r : Point F}
    (h : Adjacent M S p r) : Adjacent M S r p := by
  rcases h with ⟨hp, hr, hne, d, hd, h⟩
  refine ⟨hr, hp, hne.symm, d, hd, ?_⟩
  exact h.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)

variable [Fintype F] [DecidableEq F]

variable {M : MergedPairs F} {g : Direction F} {C : SplitChoice F}

theorem valid_no_opposite (h : ValidChoice M g C) (i : Fin 4) :
    ¬ Adjacent M C.line (tuplePoint M C.tuple i)
      (tuplePoint M C.tuple (FourCycle.opposite i)) := by
  rcases h with ⟨_, _, _, _, _, _, h0, h1, _⟩
  fin_cases i
  · simpa [FourCycle.opposite] using h0
  · simpa [FourCycle.opposite] using h1
  · simpa [FourCycle.opposite] using fun ha => h0 (adjacent_symm ha)
  · simpa [FourCycle.opposite] using fun ha => h1 (adjacent_symm ha)

theorem valid_external_unique (h : ValidChoice M g C) (p : Point F)
    (hp : OnLine p C.line) (hext : p ∉ designated M C)
    (i j : Fin 4) (hi : Adjacent M C.line p (tuplePoint M C.tuple i))
    (hj : Adjacent M C.line p (tuplePoint M C.tuple j)) : i = j := by
  apply Finset.card_le_one.mp (h.2.2.2.2.2.2.2.2 p hp hext)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hj

end SplitGeometry
end Balanced

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
theorem adjacent_iff_witness (M : MergedPairs F) (S : Line F) (x y : Point F) :
    Adjacent M S x y ↔ OnLine x S ∧ OnLine y S ∧ x ≠ y ∧
      ∃ d, d ≠ S.1 ∧ PairWitness M d x y := by
  constructor
  · rintro ⟨hx, hy, hne, d, hd, h⟩
    refine ⟨hx, hy, hne, d, hd, ?_⟩
    rcases h with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  · rintro ⟨hx, hy, hne, d, hd, s, hxs, hys⟩
    refine ⟨hx, hy, hne, d, hd, ?_⟩
    cases s
    · exact Or.inl ⟨hxs, hys⟩
    · exact Or.inr ⟨hxs, hys⟩

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

theorem opposite_witness_not_generator {M : MergedPairs F} {T : FourTuple F}
    {S : Line F} (h : SuccessfulOn M T S) (i : Fin 4) {d : Direction F}
    (hw : PairWitness M d (tuplePoint M T i) (tuplePoint M T (i + 2))) :
    d ∉ generatorSet T := by
  intro hd
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨s, hs, ht⟩ := hw
  have hi := on_used_constituent_endpoint h j s (h.2.2.2 i) hs
  have hi' := on_used_constituent_endpoint h j (!s) (h.2.2.2 (i + 2)) ht
  have ha : i = j ∨ i = j + 3 := hi.imp (fun he => h.2.2.1 he) (fun he => h.2.2.1 he)
  have hb : i + 2 = j ∨ i + 2 = j + 3 := hi'.imp (fun he => h.2.2.1 he) (fun he => h.2.2.1 he)
  fin_cases i <;> fin_cases j <;> simp_all

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

theorem not_valid_has_bounded_witness {M : MergedPairs F} {T : FourTuple F}
    {S : Line F} (h : SuccessfulOn M T S)
    (hnot : ¬ ValidChoice M S.1 ⟨S, T⟩) :
    S ∈ constituentLines M ∨ OppositeWitness M T S ∨ ExternalDoubleWitness M T S := by
  classical
  by_cases hS : S ∈ constituentLines M
  · exact Or.inl hS
  right
  have hopp (i : Fin 4)
      (ha : Adjacent M S (tuplePoint M T i) (tuplePoint M T (i + 2))) :
      OppositeWitness M T S := by
    obtain ⟨_, _, _, d, hd, hw⟩ := (adjacent_iff_witness M S _ _).mp ha
    exact ⟨i, d, hd, opposite_witness_not_generator h i hw, hw⟩
  by_cases h0 : Adjacent M S (tuplePoint M T 0) (tuplePoint M T 2)
  · exact Or.inl (hopp 0 h0)
  by_cases h1 : Adjacent M S (tuplePoint M T 1) (tuplePoint M T 3)
  · exact Or.inl (hopp 1 h1)
  right
  by_contra hE
  apply hnot
  refine ⟨rfl, hS, h.1, h.2.1, h.2.2.1, h.2.2.2, h0, h1, ?_⟩
  intro x hx hex
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hij
  have hai := (Finset.mem_filter.mp hi).2
  have haj := (Finset.mem_filter.mp hj).2
  obtain ⟨_, _, _, d, hd, hdi⟩ := (adjacent_iff_witness M S _ _).mp hai
  obtain ⟨_, _, _, e, he, hej⟩ := (adjacent_iff_witness M S _ _).mp haj
  exact hE ⟨x, i, j, d, e, hx, hex, hij,
    external_witness_directions_distinct h hx hex hij hd hdi hej,
    hd, he, external_witness_not_generator h hx hex hdi,
    external_witness_not_generator h hx hex hej, hdi, hej⟩

theorem bounded_witness_not_valid {M : MergedPairs F} {T : FourTuple F}
    {S : Line F}
    (hw : S ∈ constituentLines M ∨ OppositeWitness M T S ∨ ExternalDoubleWitness M T S) :
    ¬ ValidChoice M S.1 ⟨S, T⟩ := by
  intro hv
  rcases hw with hS | ho | he
  · exact hv.2.1 hS
  · obtain ⟨i, d, hd, _, hw⟩ := ho
    have hne : tuplePoint M T i ≠ tuplePoint M T (i + 2) := by
      intro heq
      have hi := hv.2.2.2.2.1 heq
      fin_cases i <;> simp at hi
    have hadj := (adjacent_iff_witness M S _ _).mpr
      ⟨hv.2.2.2.2.2.1 i, hv.2.2.2.2.2.1 (i + 2), hne, d, hd, hw⟩
    exact SplitGeometry.valid_no_opposite hv i hadj
  · obtain ⟨x, i, j, d, e, hx, hex, hij, _, hd, he, _, _, hdi, hej⟩ := he
    have hne (k : Fin 4) : x ≠ tuplePoint M T k := by
      intro heq
      exact hex (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, heq.symm⟩)
    have hai := (adjacent_iff_witness M S _ _).mpr
      ⟨hx, hv.2.2.2.2.2.1 i, hne i, d, hd, hdi⟩
    have haj := (adjacent_iff_witness M S _ _).mpr
      ⟨hx, hv.2.2.2.2.2.1 j, hne j, e, he, hej⟩
    exact hij (SplitGeometry.valid_external_unique hv x hx hex i j hai haj)

theorem not_valid_iff_bounded_witness {M : MergedPairs F} {T : FourTuple F}
    {S : Line F} (h : SuccessfulOn M T S) :
    ¬ ValidChoice M S.1 ⟨S, T⟩ ↔
      S ∈ constituentLines M ∨ OppositeWitness M T S ∨ ExternalDoubleWitness M T S :=
  ⟨not_valid_has_bounded_witness h, bounded_witness_not_valid⟩

omit [Field F] in

theorem constituent_target_iff (M : MergedPairs F) (S : Line F) :
    S ∈ constituentLines M ↔ ∃ s : Bool, S = constituent M S.1 s := by
  constructor
  · intro hS
    obtain ⟨⟨d, s⟩, _, h⟩ := Finset.mem_image.mp hS
    have hd : d = S.1 := congrArg Prod.fst h
    exact ⟨s, by simpa only [hd] using h.symm⟩
  · rintro ⟨s, hs⟩
    exact Finset.mem_image.mpr ⟨(S.1, s), Finset.mem_univ _, hs.symm⟩

end Balanced.CandidateValidityWitness

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

section SingleSpace

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem probReal_inter_ge_sub (A G : Set Ω) (hG : MeasurableSet G) :
    μ.real A - (1 - μ.real G) ≤ μ.real (A ∩ G) := by
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := A) hG
  have hbound : μ.real (A \ G) ≤ 1 - μ.real G := by
    rw [← probReal_compl_eq_one_sub (μ := μ) hG]
    exact measureReal_mono (Set.sdiff_subset_compl A G)
  linarith

end SingleSpace

section VaryingSpaces

variable {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
variable (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]

theorem tendsto_probReal_inter_of_good
    {l : Filter ι} (A G : ∀ i, Set (Ω i)) (hGmeas : ∀ i, MeasurableSet (G i))
    {L : ℝ} (hA : Tendsto (fun i => (μ i).real (A i)) l (𝓝 L))
    (hG : Tendsto (fun i => (μ i).real (G i)) l (𝓝 1)) :
    Tendsto (fun i => (μ i).real (A i ∩ G i)) l (𝓝 L) := by
  have hlower : Tendsto (fun i => (μ i).real (A i) - (1 - (μ i).real (G i)))
      l (𝓝 L) := by
    simpa using hA.sub ((tendsto_const_nhds (x := (1 : ℝ))).sub hG)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hA
    (fun i => probReal_inter_ge_sub (μ i) (A i) (G i) (hGmeas i))
    (fun i => measureReal_mono Set.inter_subset_left)

end VaryingSpaces

theorem pmf_outerReal_mono {Ω : Type*} (p : PMF Ω) {A B : Set Ω} (h : A ⊆ B) :
    (p.toOuterMeasure A).toReal ≤ (p.toOuterMeasure B).toReal := by
  let : MeasurableSpace Ω := ⊤
  have hA : MeasurableSet A := by trivial
  have hB : MeasurableSet B := by trivial
  have hmono := measureReal_mono (μ := p.toMeasure) h
  simpa only [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure_apply p hA,
    PMF.toMeasure_apply_eq_toOuterMeasure_apply p hB] using hmono

theorem pmf_outerReal_compl {Ω : Type*} (p : PMF Ω) (A : Set Ω) :
    (p.toOuterMeasure Aᶜ).toReal = 1 - (p.toOuterMeasure A).toReal := by
  let : MeasurableSpace Ω := ⊤
  have hA : MeasurableSet A := by trivial
  have hcompl := probReal_compl_eq_one_sub (μ := p.toMeasure) hA
  simpa only [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure_apply p hA,
    PMF.toMeasure_apply_eq_toOuterMeasure_apply p hA.compl] using hcompl

theorem tendsto_pmf_outerReal_inter_of_good
    {ι : Type*} {Ω : ι → Type*} (p : ∀ i, PMF (Ω i))
    {l : Filter ι} (A G : ∀ i, Set (Ω i)) {L : ℝ}
    (hA : Tendsto (fun i => ((p i).toOuterMeasure (A i)).toReal) l (𝓝 L))
    (hG : Tendsto (fun i => ((p i).toOuterMeasure (G i)).toReal) l (𝓝 1)) :
    Tendsto (fun i => ((p i).toOuterMeasure (A i ∩ G i)).toReal) l (𝓝 L) := by
  let : ∀ i, MeasurableSpace (Ω i) := fun _ => ⊤
  have heq : ∀ i (E : Set (Ω i)), (p i).toMeasure.real E =
      ((p i).toOuterMeasure E).toReal := by
    intro i E
    exact congrArg ENNReal.toReal
      (PMF.toMeasure_apply_eq_toOuterMeasure_apply (p i) (by trivial))
  have hA' : Tendsto (fun i => (p i).toMeasure.real (A i)) l (𝓝 L) := by
    simpa only [heq] using hA
  have hG' : Tendsto (fun i => (p i).toMeasure.real (G i)) l (𝓝 1) := by
    simpa only [heq] using hG
  simpa only [heq] using tendsto_probReal_inter_of_good
    (fun i => (p i).toMeasure) A G (fun _ => by trivial) hA' hG'

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateConstituentTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateConstituentTail

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Filter CandidatePrescribed

section FiniteMarkov
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

private theorem power_tail_le (p : PMF Ω) (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x)
    (t : ℝ) (ht : 0 < t) (s : ℕ) :
    p.toMeasure.real {x | t ≤ f x} ≤ (∫ x, f x ^ s ∂p.toMeasure) / t ^ s := by
  have hsub : {x | t ≤ f x} ⊆ {x | t ^ s ≤ f x ^ s} :=
    fun x hx => pow_le_pow_left₀ ht.le hx s
  have hm := measureReal_mono (μ := p.toMeasure) hsub
  have hk := mul_meas_ge_le_integral_of_nonneg
    (μ := p.toMeasure) (f := fun x => f x ^ s)
    (Filter.Eventually.of_forall fun x => pow_nonneg (hf x) s)
    Integrable.of_finite (t ^ s)
  apply (le_div_iff₀ (pow_pos ht s)).mpr
  exact (mul_le_mul_of_nonneg_right hm (pow_pos ht s).le).trans
    (by simpa only [mul_comm] using hk)
end FiniteMarkov

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
attribute [local instance] OAI.Balanced.CandidateConstituentTail.instMeasurableSpace_solutions
local instance instMeasurableSingletonClass_solutions : MeasurableSingletonClass F := ⟨fun _ => trivial⟩

theorem exposedLaw_empty (a : MergedPairs F) : exposedLaw ∅ a = offsetLaw F := by
  apply PMF.ext
  intro M
  simp [exposedLaw, PMF.filter_apply]
  rw [← tsum_fintype (L := .unconditional _), PMF.tsum_coe]
  simp

theorem conditional_constituent_tail_le (g : Direction F)
    (old : Finset (Direction F)) (a : MergedPairs F) (m s : ℕ)
    (hm : old.card ≤ m) (t : ℝ) (ht : 0 < t) :
    ((exposedLaw old a).toOuterMeasure
      {M | t ≤ ((constituentTargetCodes M g).card : ℝ)}).toReal ≤
      (40960 * (((m + (s - 1) * 5 : ℕ) : ℝ) + 2)^4)^s / t^s := by
  have h := power_tail_le (exposedLaw old a)
    (fun M => ((constituentTargetCodes M g).card : ℝ)) (fun _ => Nat.cast_nonneg _)
    t ht s
  have he := constituentTarget_moment_le_of_card_le g old a m s hm
  rw [PMF.integral_eq_sum] at h
  simp only [smul_eq_mul] at h
  have hreal : (exposedLaw old a).toMeasure.real
      {M | t ≤ ((constituentTargetCodes M g).card : ℝ)} =
      ((exposedLaw old a).toOuterMeasure
      {M | t ≤ ((constituentTargetCodes M g).card : ℝ)}).toReal := by
    rw [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (Set.to_countable _).measurableSet]
  rw [hreal] at h
  exact h.trans (div_le_div_of_nonneg_right he (pow_pos ht s).le)

theorem single_direction_tail_le (g : Direction F) :
    offsetEventProbability {M : MergedPairs F |
      (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤
        ((constituentTargetCodes M g).card : ℝ)} ≤
      tailConstant / (Fintype.card F : ℝ)^3 := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have h := conditional_constituent_tail_le g ∅ (fun _ _ => (0 : F)) 0 300
    (by simp) ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ)) (Real.rpow_pos_of_pos hq _)
  rw [exposedLaw_empty] at h
  have hp : ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ)) ^ (300 : ℕ) =
      (Fintype.card F : ℝ)^3 := by
    rw [← Real.rpow_mul_natCast hq.le]
    norm_num
  rw [hp] at h
  simpa only [offsetEventProbability, tailConstant, Nat.zero_add] using h

theorem some_direction_tail_le :
    offsetEventProbability {M : MergedPairs F | ∃ g : Direction F,
      (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤
        ((constituentTargetCodes M g).card : ℝ)} ≤
      2 * tailConstant / (Fintype.card F : ℝ)^2 := by
  let E (g : Direction F) : Set (MergedPairs F) := {M |
    (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤
      ((constituentTargetCodes M g).card : ℝ)}
  have heq : {M : MergedPairs F | ∃ g : Direction F, M ∈ E g} = ⋃ g, E g := by
    ext M
    simp
  have hr (A : Set (MergedPairs F)) : (offsetLaw F).toMeasure.real A =
      offsetEventProbability A := by
    rw [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (Set.to_countable _).measurableSet]
    rfl
  have hu := measureReal_iUnion_fintype_le (μ := (offsetLaw F).toMeasure) E
  simp_rw [hr] at hu
  change offsetEventProbability {M : MergedPairs F | ∃ g : Direction F, M ∈ E g} ≤ _
  rw [heq]
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hq0 : (0 : ℝ) < Fintype.card F := lt_of_lt_of_le (by norm_num) hq
  have hB : 0 ≤ tailConstant := by unfold tailConstant; positivity
  calc
    _ ≤ ∑ g : Direction F, offsetEventProbability (E g) := hu
    _ ≤ ∑ _g : Direction F, tailConstant / (Fintype.card F : ℝ)^3 := by
      apply Finset.sum_le_sum
      intro g _
      exact single_direction_tail_le g
    _ = ((Fintype.card F : ℝ) + 1) * (tailConstant / (Fintype.card F : ℝ)^3) := by
      simp [Direction, Nat.cast_add, Nat.cast_one]
    _ ≤ (2 * (Fintype.card F : ℝ)) * (tailConstant / (Fintype.card F : ℝ)^3) := by
      apply mul_le_mul_of_nonneg_right (by linarith only [hq])
        (div_nonneg hB (pow_pos hq0 3).le)
    _ = _ := by field_simp

theorem tendsto_some_direction_tail
    (K : ℕ → Type*) [∀ n, Field (K n)] [∀ n, Fintype (K n)]
    [∀ n, DecidableEq (K n)]
    (hq : Tendsto (fun n => Fintype.card (K n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability {M : MergedPairs (K n) |
      ∃ g : Direction (K n), (Fintype.card (K n) : ℝ) ^ (1 / 100 : ℝ) ≤
        ((constituentTargetCodes M g).card : ℝ)}) atTop (𝓝 0) := by
  have hreal : Tendsto (fun n => (Fintype.card (K n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  have hz : Tendsto (fun n => 2 * tailConstant / (Fintype.card (K n) : ℝ)^2)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, div_eq_mul_inv, inv_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero] using
      ((tendsto_inv_atTop_zero.comp hreal).pow 2).const_mul (2 * tailConstant)
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg)
    (fun n => some_direction_tail_le (F := K n)) hz

end
end Balanced.CandidateConstituentTail

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
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateRetention
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.CandidateRetention

variable {Tuple Line : Type*} [DecidableEq Line]

theorem card_sq_le_image_card_mul_fiber_sq (tuples : Finset Tuple)
    (line : Tuple → Line) :
    (tuples.card : ℝ) ^ 2 ≤ ((tuples.image line).card : ℝ) *
      ∑ l ∈ tuples.image line, ((tuples.filter (fun t => line t = l)).card : ℝ) ^ 2 := by
  have hsum : (tuples.card : ℝ) =
      ∑ l ∈ tuples.image line, ((tuples.filter (fun t => line t = l)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image line tuples
  rw [hsum]
  simpa using Finset.sum_mul_sq_le_sq_mul_sq (tuples.image line)
    (fun _ => (1 : ℝ)) (fun l => ((tuples.filter (fun t => line t = l)).card : ℝ))

theorem fiber_sq_sum_mono [Fintype Line] {valid all : Finset Tuple}
    (hsub : valid ⊆ all) (line : Tuple → Line) :
    (∑ l, ((valid.filter (fun t => line t = l)).card : ℝ) ^ 2) ≤
      ∑ l, ((all.filter (fun t => line t = l)).card : ℝ) ^ 2 := by
  apply Finset.sum_le_sum
  intro l _
  have hc : (valid.filter (fun t => line t = l)).card ≤
      (all.filter (fun t => line t = l)).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ hsub)
  have hr : ((valid.filter (fun t => line t = l)).card : ℝ) ≤
      ((all.filter (fun t => line t = l)).card : ℝ) := by exact_mod_cast hc
  exact pow_le_pow_left₀ (by positivity) hr 2

theorem valid_card_sq_le_retained_mul_all_sq [Fintype Line]
    {valid all : Finset Tuple} (hsub : valid ⊆ all) (line : Tuple → Line) :
    (valid.card : ℝ) ^ 2 ≤ ((valid.image line).card : ℝ) *
      ∑ l, ((all.filter (fun t => line t = l)).card : ℝ) ^ 2 := by
  apply (card_sq_le_image_card_mul_fiber_sq valid line).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    (∑ l ∈ valid.image line, ((valid.filter (fun t => line t = l)).card : ℝ) ^ 2) ≤
        ∑ l, ((valid.filter (fun t => line t = l)).card : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
    _ ≤ _ := fiber_sq_sum_mono hsub line

theorem retained_card_lower_bound [Fintype Line]
    {valid all : Finset Tuple} (hsub : valid ⊆ all) (line : Tuple → Line)
    {a C q : ℝ} (ha : 0 ≤ a) (hC : 0 < C) (hq : 0 < q)
    (hmass : a * q ≤ valid.card)
    (hsquare : (∑ l, ((all.filter (fun t => line t = l)).card : ℝ) ^ 2) ≤ C * q) :
    (a ^ 2 / C) * q ≤ (valid.image line).card := by
  have hcs := valid_card_sq_le_retained_mul_all_sq hsub line
  have hmasssq : (a * q) ^ 2 ≤ (valid.card : ℝ) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg ha hq.le) hmass 2
  have hupper := mul_le_mul_of_nonneg_left hsquare
    (show (0 : ℝ) ≤ (valid.image line).card by positivity)
  have hmain : a ^ 2 * q ^ 2 ≤ ((valid.image line).card : ℝ) * (C * q) := by
    nlinarith
  have hcancel : a ^ 2 * q ≤ ((valid.image line).card : ℝ) * C := by
    nlinarith
  simpa [div_mul_eq_mul_div] using (div_le_iff₀ hC).mpr hcancel

end Balanced.CandidateRetention

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateRetentionBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateRetention

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem valid_line_image_card_le_slot (M : MergedPairs F) (s : Slot F)
    (valid : Finset (SplitChoice F))
    (hvalid : ∀ C ∈ valid, ValidChoice M s.1 C) :
    (valid.image SplitChoice.line).card ≤ (candidateSlot M s).card := by
  let f : Line F → CandidateVertex F := fun l => (s, l.2)
  apply Finset.card_le_card_of_injOn f
  · intro l hl
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hl
    have hc := hvalid C hC
    apply mem_candidateSlot.mpr
    refine ⟨?_, rfl⟩
    change SupportsValidTuple M (s.1, C.line.2)
    have hline : (s.1, C.line.2) = C.line := Prod.ext hc.1.symm rfl
    rw [hline]
    exact ⟨C.tuple, by simpa only [hc.1] using hc⟩
  · intro l hl k hk heq
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hk
    apply Prod.ext
    · exact (hvalid C hC).1.trans (hvalid D hD).1.symm
    · exact congrArg (fun v : CandidateVertex F => v.2) heq

theorem candidateSlot_lower_bound (M : MergedPairs F) (s : Slot F)
    {valid all : Finset (SplitChoice F)} (hsub : valid ⊆ all)
    (hvalid : ∀ C ∈ valid, ValidChoice M s.1 C)
    {a C q : ℝ} (ha : 0 ≤ a) (hC : 0 < C) (hq : 0 < q)
    (hmass : a * q ≤ valid.card)
    (hsquare : (∑ l : Line F,
      ((all.filter (fun T => T.line = l)).card : ℝ) ^ 2) ≤ C * q) :
    (a ^ 2 / C) * q ≤ ((candidateSlot M s).card : ℝ) := by
  have hret := retained_card_lower_bound hsub SplitChoice.line ha hC hq hmass hsquare
  have hslot : ((valid.image SplitChoice.line).card : ℝ) ≤ (candidateSlot M s).card := by
    exact_mod_cast valid_line_image_card_le_slot M s valid hvalid
  exact hret.trans hslot

end
end Balanced.CandidateRetention

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

theorem valid_add_invalid_eq_success (M : MergedPairs F) (g : Direction F) :
    (validPrescriptions M g).card + invalidSuccessCount M g = rootSuccessCount g M := by
  exact Finset.card_filter_add_card_filter_not _

theorem successfulChoices_fiber_card (M : MergedPairs F) (g : Direction F) (l : Line F) :
    ((successfulChoices M g).filter (fun C => C.line = l)).card =
      ((successfulPrescriptions M g).filter (fun a => (a.choice M).line = l)).card := by
  rw [successfulChoices, Finset.filter_image]
  exact Finset.card_image_of_injective _ (RootPrescription.choice_injective M)

theorem successfulChoices_square_sum (M : MergedPairs F) (g : Direction F) :
    (∑ l : Line F,
      (((successfulChoices M g).filter (fun C => C.line = l)).card : ℝ) ^ 2) =
        (rootFiberSquareCount M g : ℝ) := by
  simp only [rootFiberSquareCount, Nat.cast_sum, Nat.cast_pow,
    successfulChoices_fiber_card]

theorem candidateSlot_lower_bound_of_root_counts (M : MergedPairs F) (s : Slot F)
    {a C : ℝ} (ha : 0 ≤ a) (hC : 0 < C)
    (hmass : a * Fintype.card F + invalidSuccessCount M s.1 ≤ rootSuccessCount s.1 M)
    (hsquare : (rootFiberSquareCount M s.1 : ℝ) ≤ C * Fintype.card F) :
    (a ^ 2 / C) * Fintype.card F ≤ ((candidateSlot M s).card : ℝ) := by
  let V := (validPrescriptions M s.1).image (fun a => a.choice M)
  have hsub : V ⊆ successfulChoices M s.1 :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  have hvalid : ∀ D ∈ V, ValidChoice M s.1 D := by
    intro D hD
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hD
    exact (Finset.mem_filter.mp ha).2
  have hcard : V.card = (validPrescriptions M s.1).card :=
    Finset.card_image_of_injective _ (RootPrescription.choice_injective M)
  have hsplit : ((validPrescriptions M s.1).card : ℝ) +
      invalidSuccessCount M s.1 = rootSuccessCount s.1 M := by
    exact_mod_cast valid_add_invalid_eq_success M s.1
  have hmassV : a * Fintype.card F ≤ (V.card : ℝ) := by
    rw [hcard]
    linarith
  apply CandidateRetention.candidateSlot_lower_bound M s hsub hvalid ha hC
    (by exact_mod_cast Fintype.card_pos (α := F)) hmassV
  simpa only [successfulChoices_square_sum] using hsquare

end
end Balanced.TupleAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateValidityAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateValidityAssembly

noncomputable section
open scoped Classical
open TupleAlignment CandidateValidityWitness

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem successfulOn_of_mem {M : MergedPairs F} {g : Direction F}
    {a : RootPrescription g} (ha : a ∈ successfulPrescriptions M g) :
    SuccessfulOn M a.tuple (a.choice M).line := by
  exact ⟨a.injective, fun i => (a.1 i).2,
    (Finset.mem_filter.mp ha).2.2, choice_on_line_of_successful ha⟩

theorem invalidPrescriptions_eq_union (M : MergedPairs F) (g : Direction F) :
    (successfulPrescriptions M g).filter (fun a => ¬ ValidChoice M g (a.choice M)) =
      constituentFailures M g ∪ oppositeFailures M g ∪ externalFailures M g := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_union, constituentFailures,
    oppositeFailures, externalFailures]
  by_cases ha : a ∈ successfulPrescriptions M g
  · have hw := not_valid_iff_bounded_witness (successfulOn_of_mem ha)
    change (¬ ValidChoice M g (a.choice M)) ↔ _ at hw
    simp only [ha, true_and]
    rw [hw]
    exact or_assoc.symm
  · simp only [ha, false_and, false_or]

theorem invalidSuccessCount_le_failure_sum (M : MergedPairs F) (g : Direction F) :
    invalidSuccessCount M g ≤
      (constituentFailures M g).card + (oppositeFailures M g).card +
        (externalFailures M g).card := by
  unfold invalidSuccessCount
  rw [invalidPrescriptions_eq_union]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _)

omit [Field F] [Fintype F] [DecidableEq F] in
theorem prescriptionCode_injective {g : Direction F} :
    Function.Injective (prescriptionCode (F := F) (g := g)) := by
  intro a b hab
  apply RootPrescription.tuple_injective
  exact congrArg (fun c : CandidatePrescribed.Code F =>
    (⟨c.1, c.2⟩ : FourTuple F)) hab

theorem prescriptionCode_mem_constituentTargetCodes {M : MergedPairs F}
    {g : Direction F} {a : RootPrescription g}
    (ha : a ∈ constituentFailures M g) :
    prescriptionCode a ∈ CandidatePrescribed.constituentTargetCodes M g := by
  obtain ⟨hs, hc⟩ := Finset.mem_filter.mp ha
  obtain ⟨s, hline⟩ := (constituent_target_iff M (a.choice M).line).mp hc
  change (a.choice M).line = constituent M g s at hline
  have hmem : prescriptionCode a ∈
      CandidatePrescribed.successfulCodes M (constituent M g s) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩,
      (Finset.mem_filter.mp hs).2.2⟩
    · exact ⟨a.injective, fun i => (a.1 i).2⟩
    · intro i
      change OnLine (tuplePoint M a.tuple i) (constituent M g s)
      rw [← hline]
      exact choice_on_line_of_successful hs i
  cases s
  · exact Finset.mem_union_left _ hmem
  · exact Finset.mem_union_right _ hmem

theorem constituentFailures_card_le (M : MergedPairs F) (g : Direction F) :
    (constituentFailures M g).card ≤
      (CandidatePrescribed.constituentTargetCodes M g).card := by
  apply Finset.card_le_card_of_injOn prescriptionCode
    (fun _ ha => prescriptionCode_mem_constituentTargetCodes ha)
  intro a _ b _ hab
  exact prescriptionCode_injective hab

theorem invalidSuccessCount_le (M : MergedPairs F) (g : Direction F) :
    invalidSuccessCount M g ≤
      (CandidatePrescribed.constituentTargetCodes M g).card +
        (oppositeFailures M g).card + (externalFailures M g).card := by
  exact (invalidSuccessCount_le_failure_sum M g).trans
    (Nat.add_le_add_right
      (Nat.add_le_add_right (constituentFailures_card_le M g) _) _)

omit [Field F] [Fintype F] in

theorem card_le_witnesses {g : Direction F} {A : Type*} [DecidableEq A]
    (bad : Finset (RootPrescription g)) (witnesses : Finset A)
    (tuple : A → FourTuple F)
    (hcover : ∀ a ∈ bad, ∃ w ∈ witnesses, tuple w = a.tuple) :
    bad.card ≤ witnesses.card := by
  calc
    bad.card = (bad.image RootPrescription.tuple).card :=
      (Finset.card_image_of_injective _ RootPrescription.tuple_injective).symm
    _ ≤ (witnesses.image tuple).card := by
      apply Finset.card_le_card
      intro T hT
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hT
      obtain ⟨w, hw, heq⟩ := hcover a ha
      exact Finset.mem_image.mpr ⟨w, hw, heq⟩
    _ ≤ witnesses.card := Finset.card_image_le

theorem candidateSlot_lower_bound_of_failures (M : MergedPairs F) (s : Slot F)
    {C : ℝ} (hC : 0 < C)
    (hH : 8 * Fintype.card F ≤ rootSuccessCount s.1 M)
    (hconst : (CandidatePrescribed.constituentTargetCodes M s.1).card ≤ Fintype.card F)
    (hopp : (oppositeFailures M s.1).card ≤ Fintype.card F)
    (hext : (externalFailures M s.1).card ≤ Fintype.card F)
    (hY : (rootFiberSquareCount M s.1 : ℝ) ≤ C * Fintype.card F) :
    (25 / C) * Fintype.card F ≤ ((candidateSlot M s).card : ℝ) := by
  have hloss : invalidSuccessCount M s.1 ≤ 3 * Fintype.card F := by
    have h := invalidSuccessCount_le M s.1
    omega
  have hmass : (5 : ℝ) * Fintype.card F + invalidSuccessCount M s.1 ≤
      rootSuccessCount s.1 M := by
    have hlossR : (invalidSuccessCount M s.1 : ℝ) ≤ 3 * Fintype.card F := by
      exact_mod_cast hloss
    have hHR : (8 : ℝ) * Fintype.card F ≤ rootSuccessCount s.1 M := by
      exact_mod_cast hH
    linarith
  simpa only [show (5 : ℝ) ^ 2 = 25 by norm_num] using
    candidateSlot_lower_bound_of_root_counts M s (by norm_num : (0 : ℝ) ≤ 5)
      hC hmass hY

end
end Balanced.CandidateValidityAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateOldOppositeOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateOldOpposite

noncomputable section
open scoped Classical BigOperators
open CandidateExposure CandidateValidityWitness PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem mem_overlappingWitnesses_iff (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) (T : FourTuple F) (i : Fin 4) (d : Direction F) :
    ((T, i), d) ∈ overlappingWitnesses g D M ↔
      T ∈ eligibleTuples g ∧ 0 < (exposedTupleIndices T D).card ∧
      M ∈ successfulInDirection T g ∧ d ∈ D ∧ d ≠ g ∧
      d ∉ generatorSet T ∧ PairWitness M d (tuplePoint M T i)
        (tuplePoint M T (i + 2)) := by
  simp only [overlappingWitnesses, Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
    Finset.mem_univ, and_true]
  tauto

theorem card_overlappingWitnesses_le (g : Direction F)
    (D : Finset (Direction F)) (M : MergedPairs F) :
    (overlappingWitnesses g D M).card ≤ 4 * D.card * overlappingTupleCount g D M := by
  unfold overlappingWitnesses
  calc
    _ ≤ (((((eligibleTuples g).filter (fun T =>
        0 < (exposedTupleIndices T D).card)).filter
        (fun T => M ∈ successfulInDirection T g)).product
        (Finset.univ : Finset (Fin 4))).product D).card := Finset.card_filter_le _ _
    _ = _ := by
      simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ, Fintype.card_fin,
        overlappingTupleCount]
      ring

theorem expected_overlappingWitnesses_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∑ M : MergedPairs F, (exposedLaw D a M).toReal *
      ((overlappingWitnesses g D M).card : ℝ)) ≤
      65536 * (m : ℝ) * ((m : ℝ) + 1)^4 := by
  let : MeasurableSpace F := ⊤
  have hmean := conditional_overlappingTupleCount_le g D a m hD
  rw [PMF.integral_eq_sum] at hmean
  simp only [smul_eq_mul] at hmean
  have hcard (M : MergedPairs F) : ((overlappingWitnesses g D M).card : ℝ) ≤
      (4 * (m : ℝ)) * (overlappingTupleCount g D M : ℝ) := by
    exact_mod_cast (card_overlappingWitnesses_le g D M).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hD))
  calc
    _ ≤ ∑ M : MergedPairs F, (exposedLaw D a M).toReal *
        ((4 * (m : ℝ)) * (overlappingTupleCount g D M : ℝ)) := by
      apply Finset.sum_le_sum
      intro M _
      exact mul_le_mul_of_nonneg_left (hcard M) ENNReal.toReal_nonneg
    _ = (4 * (m : ℝ)) * ∑ M : MergedPairs F, (exposedLaw D a M).toReal *
        (overlappingTupleCount g D M : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M _
      ring
    _ ≤ (4 * (m : ℝ)) * (16384 * ((m : ℝ) + 1)^4) :=
      mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = _ := by ring

end
end Balanced.CandidateOldOpposite

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

theorem successful_opposite_iff_fixed_positions
    [Fintype F] [DecidableEq F] {M a : MergedPairs F} {T : FourTuple F}
    {S : Line F} (h : SuccessfulOn M T S) {d : Direction F}
    (hd : d ≠ S.1) (hMa : M d = a d) (i : Fin 4) :
    PairWitness M d (tuplePoint M T i) (tuplePoint M T (i + 2)) ↔
      ∃ s : Bool, tuplePoint M T i = forcedPoint a S d s ∧
        tuplePoint M T (i + 2) = forcedPoint a S d (!s) :=
  pairWitness_iff_forcedPoints hd hMa (h.2.2.2 i) (h.2.2.2 (i + 2))

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

theorem two_pinned_positions_probability
    (D : Finset (Direction F)) (a : MergedPairs F) (T : FourTuple F)
    (hT : Function.Injective T.generator) (hfresh : ∀ i, T.generator i ∉ D)
    (S : Line F) (i j : Fin 4) (hij : i ≠ j)
    (x y : Point F) (hx : OnLine x S) (hy : OnLine y S) :
    ((exposedLaw D a).toOuterMeasure {M |
      (∀ k, OnLine (tuplePoint M T k) S) ∧
      tuplePoint M T i = x ∧ tuplePoint M T j = y}).toReal =
      (Fintype.card F : ℝ)⁻¹ ^ 6 := by
  let p : Fin 4 → Point F := fun k => if k = i then x else y
  have hp : ∀ k ∈ ({i, j} : Finset (Fin 4)), OnLine (p k) S := by
    intro k hk
    by_cases hki : k = i
    · simpa [p, hki] using hx
    · simpa [p, hki] using hy
  have h := pinned_positions_probability D a T hT hfresh S {i, j} p hp
  simpa [p, hij, hij.symm] using h

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

theorem successful_opposite_probability_le
    (D : Finset (Direction F)) (a : MergedPairs F) (T : FourTuple F)
    (hT : Function.Injective T.generator) (hfresh : ∀ i, T.generator i ∉ D)
    (S : Line F) (d : Direction F) (hdD : d ∈ D) (hd : d ≠ S.1)
    (i : Fin 4) :
    ((exposedLaw D a).toOuterMeasure {M | SuccessfulOn M T S ∧
      PairWitness M d (tuplePoint M T i) (tuplePoint M T (i + 2))}).toReal ≤
      2 * (Fintype.card F : ℝ)⁻¹ ^ 6 := by
  let E (s : Bool) : Set (MergedPairs F) := {M |
    (∀ k, OnLine (tuplePoint M T k) S) ∧
    tuplePoint M T i = forcedPoint a S d s ∧
    tuplePoint M T (i + 2) = forcedPoint a S d (!s)}
  have hij : i ≠ i + 2 := by fin_cases i <;> decide
  calc
    _ ≤ ((exposedLaw D a).toOuterMeasure {M | ∃ s, M ∈ E s}).toReal := by
      apply real_probability_mono_support
      rintro M ⟨⟨hS, hw⟩, hM⟩
      obtain ⟨s, hs, ht⟩ := (successful_opposite_iff_fixed_positions hS hd
        (exposedLaw_support_fixed D a M hM d hdD) i).mp hw
      exact ⟨s, hS.2.2.2, hs, ht⟩
    _ ≤ ∑ s : Bool, ((exposedLaw D a).toOuterMeasure (E s)).toReal :=
      probability_exists_le_sum _ _
    _ = _ := by
      have hE (s : Bool) : ((exposedLaw D a).toOuterMeasure (E s)).toReal =
          (Fintype.card F : ℝ)⁻¹ ^ 6 :=
        two_pinned_positions_probability D a T hT hfresh S i (i + 2) hij
          _ _ (forcedPoint_on_target a S d hd s)
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

theorem oldOppositeFreshSum_le_div (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) :
    oldOppositeFreshSum g D a ≤ 2048 * (D.card : ℝ) / Fintype.card F := by
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : ((freshTuples D).card : ℝ) ≤ 256 * (Fintype.card F : ℝ)^4 := by
    exact_mod_cast freshTuples_card_le D
  have hd : ((D.erase g).card : ℝ) ≤ D.card := by
    exact_mod_cast Finset.card_erase_le (s := D) (a := g)
  calc
    _ ≤ ∑ _T ∈ freshTuples D, ∑ _c : F, ∑ _d ∈ D.erase g,
        ∑ _i : Fin 4, 2 * (Fintype.card F : ℝ)⁻¹ ^ 6 := by
      apply Finset.sum_le_sum
      intro T hT
      obtain ⟨hinj, hfresh⟩ := (Finset.mem_filter.mp hT).2
      apply Finset.sum_le_sum
      intro c _
      apply Finset.sum_le_sum
      intro d hdD
      apply Finset.sum_le_sum
      intro i _
      exact successful_opposite_probability_le D a T hinj hfresh (g,c) d
        (Finset.mem_erase.mp hdD).2 (Finset.mem_erase.mp hdD).1 i
    _ = ((freshTuples D).card : ℝ) * (Fintype.card F : ℝ) *
        ((D.erase g).card : ℝ) * (8 * (Fintype.card F : ℝ)⁻¹ ^ 6) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_ofNat]
      ring
    _ ≤ (256 * (Fintype.card F : ℝ)^4) * (Fintype.card F : ℝ) *
        (D.card : ℝ) * (8 * (Fintype.card F : ℝ)⁻¹ ^ 6) := by gcongr
    _ = _ := by field_simp; ring

theorem oldOppositeFreshSum_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) : oldOppositeFreshSum g D a ≤ 2048 * (D.card : ℝ) := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  exact (oldOppositeFreshSum_le_div g D a).trans (div_le_self (by positivity) hq)

private theorem probability_eq_weighted_indicator {Ω : Type*} [Fintype Ω]
    (law : PMF Ω) (E : Set Ω) :
    (law.toOuterMeasure E).toReal =
      ∑ ω, (law ω).toReal * (if ω ∈ E then 1 else 0) := by
  rw [PMF.toOuterMeasure_apply_fintype,
    ENNReal.toReal_sum (fun ω _ => by
      by_cases h : ω ∈ E
      · simpa only [Set.indicator_of_mem h] using law.apply_ne_top ω
      · simp [Set.indicator_of_notMem h])]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : ω ∈ E <;> simp [h]

theorem oldOppositeFreshCount_mean_eq (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (∑ M, ((exposedLaw D a) M).toReal * (oldOppositeFreshCount g D M : ℝ)) =
      oldOppositeFreshSum g D a := by
  unfold oldOppositeFreshCount oldOppositeFreshSum
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [probability_eq_weighted_indicator]
  apply Finset.sum_congr rfl
  intro M _
  by_cases h : SuccessfulOn M T (g,c) ∧
      PairWitness M d (tuplePoint M T i) (tuplePoint M T (i + 2))
  · simp [h]
  · simp [h]

theorem oldOppositeFreshCount_mean_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (∑ M, ((exposedLaw D a) M).toReal * (oldOppositeFreshCount g D M : ℝ)) ≤
      2048 * (D.card : ℝ) := by
  rw [oldOppositeFreshCount_mean_eq]
  exact oldOppositeFreshSum_le g D a

end
end Balanced.ExposedOppositeSum

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_OppositeCases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.OppositeAssembly

noncomputable section
open scoped Classical BigOperators
open CandidateExposure CandidateValidityWitness PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem witnesses_subset_cases (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : witnesses g M ⊆
      freshWitnesses g D M ∪
        (oldFreshWitnesses g D M ∪ CandidateOldOpposite.overlappingWitnesses g D M) := by
  rintro ⟨⟨T,i⟩,d⟩ hw
  by_cases hd : d ∈ D
  · apply Finset.mem_union_right
    by_cases hf : ∀ j, T.generator j ∉ D
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw,hd,hf⟩)
    · apply Finset.mem_union_right
      obtain ⟨hT,hs,hdg,hdT,hp⟩ := (mem_witnesses g M T i d).mp hw
      have hpos : 0 < (exposedTupleIndices T D).card := by
        apply Finset.card_pos.mpr
        push Not at hf
        obtain ⟨j,hj⟩ := hf
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
      exact (CandidateOldOpposite.mem_overlappingWitnesses_iff g D M T i d).mpr
        ⟨hT,hpos,hs,hd,hdg,hdT,hp⟩
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw,hd⟩)

theorem witnesses_card_le_cases (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : (witnesses g M).card ≤
      (freshWitnesses g D M).card + (oldFreshWitnesses g D M).card +
        (CandidateOldOpposite.overlappingWitnesses g D M).card := by
  have h := (Finset.card_le_card (witnesses_subset_cases g D M)).trans
    (Finset.card_union_le _ _)
  have h' := Finset.card_union_le (oldFreshWitnesses g D M)
    (CandidateOldOpposite.overlappingWitnesses g D M)
  omega

theorem oldFreshWitnesses_card_le (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : (oldFreshWitnesses g D M).card ≤
      ExposedOppositeSum.oldOppositeFreshCount g D M := by
  let S := ((((ExposedOppositeSum.freshTuples D).product (Finset.univ : Finset F)).product
    (D.erase g)).product (Finset.univ : Finset (Fin 4))).filter
    (fun x => SuccessfulOn M x.1.1.1 (g,x.1.1.2) ∧
      PairWitness M x.1.2 (tuplePoint M x.1.1.1 x.2)
        (tuplePoint M x.1.1.1 (x.2+2)))
  let f : Label F → ((FourTuple F × F) × Direction F) × Fin 4 :=
    fun w => (((w.1.1,lineEval g (tuplePoint M w.1.1 0)),w.2),w.1.2)
  have hmap : ∀ w ∈ oldFreshWitnesses g D M, f w ∈ S := by
    rintro ⟨⟨T,i⟩,d⟩ hw
    obtain ⟨hw,hd,hfresh⟩ := Finset.mem_filter.mp hw
    obtain ⟨hT,hs,hdg,hdT,hp⟩ := (mem_witnesses g M T i d).mp hw
    obtain ⟨hinj,havoid⟩ := (Finset.mem_filter.mp hT).2
    obtain ⟨⟨c,hc⟩,hpoints⟩ := hs
    have halign : ∀ j, OnLine (tuplePoint M T j)
        (g,lineEval g (tuplePoint M T 0)) := by
      intro j
      exact (hc j).trans (hc 0).symm
    apply Finset.mem_filter.mpr
    refine ⟨?_,⟨hinj,havoid,hpoints,halign⟩,hp⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,hinj,hfresh⟩,Finset.mem_univ _⟩,
        Finset.mem_erase.mpr ⟨hdg,hd⟩⟩,Finset.mem_univ _⟩
  have hinj : Set.InjOn f (oldFreshWitnesses g D M : Set (Label F)) := by
    intro x hx y hy he
    have hT := congrArg (fun z : ((FourTuple F × F) × Direction F) × Fin 4 => z.1.1.1) he
    have hi := congrArg (fun z : ((FourTuple F × F) × Direction F) × Fin 4 => z.2) he
    have hd := congrArg (fun z : ((FourTuple F × F) × Direction F) × Fin 4 => z.1.2) he
    exact Prod.ext (Prod.ext hT hi) hd
  have hc := Finset.card_le_card_of_injOn f hmap hinj
  have hS : S.card = ExposedOppositeSum.oldOppositeFreshCount g D M := by
    simp only [S, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product,
      ExposedOppositeSum.oldOppositeFreshCount]
  exact hc.trans_eq hS

end
end Balanced.OppositeAssembly

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

theorem oriented_pair_probability_on_event (T : FourTuple F) (d : Direction F)
    (hd : ∀ i, T.generator i ≠ d) (i j : Fin 4) (σ : Bool)
    (G : MergedPairs F → Prop) [Nonempty {M : MergedPairs F // G M}]
    (hG : ∀ M v, G (Function.update M d v) ↔ G M)
    (E : (Fin 4 → Point F) → Prop) :
    ((PMF.uniformOfFintype {M : MergedPairs F // G M}).toOuterMeasure
      {M | E (tuplePoint M.1 T) ∧
        OnLine (tuplePoint M.1 T i) (constituent M.1 d σ) ∧
        OnLine (tuplePoint M.1 T j) (constituent M.1 d (!σ))}).toReal =
    ((PMF.uniformOfFintype {M : MergedPairs F // G M}).toOuterMeasure
      {M | E (tuplePoint M.1 T)}).toReal / (Fintype.card F : ℝ)^2 := by
  have h := FreshCoordinate.probability_prescription_on_subtype d G
    (fun M => E (tuplePoint M T))
    (fun M => pairPrescription d (tuplePoint M T i) (tuplePoint M T j) σ)
    hG (by intro M v; rw [tuplePoint_update_fresh T d hd])
    (by intro M v; rw [tuplePoint_update_fresh T d hd])
  simp_rw [pairPrescription_iff] at h
  have hcard : (Fintype.card (Bool → F) : ℝ) = (Fintype.card F : ℝ)^2 := by
    simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow]
  rw [hcard] at h
  exact h

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
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_OppositeFreshConditional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.OppositeFreshConditional

noncomputable section
open scoped Classical BigOperators
attribute [local instance] Classical.propDecidable
open CandidateExposure CandidateValidityWitness FreshTupleWitness ConditionalRestriction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem uniform_probability_irrel {Ω : Type*} [Nonempty Ω]
    (f h : Fintype Ω) (E : Set Ω) :
    ((@PMF.uniformOfFintype Ω f inferInstance).toOuterMeasure E).toReal =
      ((@PMF.uniformOfFintype Ω h inferInstance).toOuterMeasure E).toReal := by
  cases Subsingleton.elim f h
  rfl

theorem exposed_probability_eq_fiber (D : Finset (Direction F)) (a : MergedPairs F)
    (E : Set (MergedPairs F)) :
    ((CandidateExposure.exposedLaw D a).toOuterMeasure E).toReal =
      ((PMF.uniformOfFintype (FixedArray (fun d => d ∈ D) a)).toOuterMeasure
        {M | M.1 ∈ E}).toReal := by
  simp only [CandidateExposure.exposedLaw, PartialAlignment.offsetLaw_eq_uniform]
  rw [uniform_fixed_filter, PMF.toOuterMeasure_map_apply]
  exact uniform_probability_irrel _ _ _

theorem oriented_probability (D : Finset (Direction F)) (a : MergedPairs F)
    (g : Direction F) (T : FourTuple F) (d : Direction F)
    (hd : d ∉ D) (hT : d ∉ generatorSet T) (i j : Fin 4) (σ : Bool) :
    ((CandidateExposure.exposedLaw D a).toOuterMeasure {M |
      M ∈ successfulInDirection T g ∧
      OnLine (tuplePoint M T i) (constituent M d σ) ∧
      OnLine (tuplePoint M T j) (constituent M d (!σ))}).toReal =
    ((CandidateExposure.exposedLaw D a).toOuterMeasure
      (successfulInDirection T g)).toReal / (Fintype.card F : ℝ)^2 := by
  rw [exposed_probability_eq_fiber, exposed_probability_eq_fiber]
  have hgen : ∀ k, T.generator k ≠ d := by
    intro k hk
    exact hT (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩)
  have h := oriented_pair_probability_on_event T d hgen i j σ
    (fun M => ∀ t, t ∈ D → M t = a t)
    (fixed_coordinates_update_invariant (fun t => t ∈ D) a d hd)
    (fun p => (∃ c, ∀ k, OnLine (p k) (g,c)) ∧ Function.Injective p)
  refine (uniform_probability_irrel _ _ _).trans (h.trans ?_)
  apply congrArg (fun r : ℝ => r / (Fintype.card F : ℝ)^2)
  exact uniform_probability_irrel _ _ _

theorem pair_probability_le (D : Finset (Direction F)) (a : MergedPairs F)
    (g : Direction F) (T : FourTuple F) (d : Direction F)
    (hd : d ∉ D) (hT : d ∉ generatorSet T) (i j : Fin 4) :
    ((CandidateExposure.exposedLaw D a).toOuterMeasure {M |
      M ∈ successfulInDirection T g ∧
      PairWitness M d (tuplePoint M T i) (tuplePoint M T j)}).toReal ≤
      2 * ((CandidateExposure.exposedLaw D a).toOuterMeasure
        (successfulInDirection T g)).toReal / (Fintype.card F : ℝ)^2 := by
  let E : Bool → Set (MergedPairs F) := fun σ => {M |
    M ∈ successfulInDirection T g ∧
    OnLine (tuplePoint M T i) (constituent M d σ) ∧
    OnLine (tuplePoint M T j) (constituent M d (!σ))}
  have heq : {M : MergedPairs F | M ∈ successfulInDirection T g ∧
      PairWitness M d (tuplePoint M T i) (tuplePoint M T j)} =
      {M | ∃ σ, M ∈ E σ} := by
    ext M
    simp only [Set.mem_ofPred_eq, E, PairWitness]
    constructor
    · rintro ⟨h, σ, hs⟩
      exact ⟨σ, h, hs⟩
    · rintro ⟨σ, h, hs⟩
      exact ⟨h, σ, hs⟩
  rw [heq]
  apply (FreshWitnessProbability.probability_exists_le_sum _ E).trans
  have hE (σ : Bool) :
      ((CandidateExposure.exposedLaw D a).toOuterMeasure (E σ)).toReal =
      ((CandidateExposure.exposedLaw D a).toOuterMeasure
        (successfulInDirection T g)).toReal / (Fintype.card F : ℝ)^2 :=
    oriented_probability D a g T d hd hT i j σ
  simp only [hE, Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  ring_nf
  exact le_rfl

end
end Balanced.OppositeFreshConditional

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_OppositeFreshMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.OppositeAssembly

noncomputable section
open scoped Classical BigOperators
open CandidateExposure CandidateValidityWitness MeasureTheory

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem freshWitnesses_subset_events (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : freshWitnesses g D M ⊆
      (freshTests g D).filter (fun w => M ∈ freshEvent g w) := by
  rintro ⟨⟨T,i⟩,d⟩ hw
  obtain ⟨hw,hd⟩ := Finset.mem_filter.mp hw
  obtain ⟨hT,hs,hdg,hdT,hp⟩ := (mem_witnesses g M T i d).mp hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨hT,Finset.mem_univ _⟩,Finset.mem_univ _⟩,hd,hdT⟩,hs,hp⟩

attribute [local instance] OAI.Balanced.OppositeAssembly.instMeasurableSpace_solutions
theorem freshWitnesses_mean_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
      ((freshWitnesses g D M).card : ℝ)) ≤ 327680 * ((m : ℝ)+1)^4 := by
  let μ := (CandidateExposure.exposedLaw D a).toMeasure
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  let p : FourTuple F → ℝ := fun T =>
    ((CandidateExposure.exposedLaw D a).toOuterMeasure (successfulInDirection T g)).toReal
  have hp (T : FourTuple F) : 0 ≤ p T := ENNReal.toReal_nonneg
  have hmean : (∑ T ∈ eligibleTuples g, p T) ≤
      (20480 * ((m : ℝ)+1)^4) * Fintype.card F :=
    successProbabilitySum_le g D a m hD
  have hsum : (∑ w ∈ freshTests g D,
      ((CandidateExposure.exposedLaw D a).toOuterMeasure (freshEvent g w)).toReal) ≤
      8 * ((Fintype.card F : ℝ)+1) / (Fintype.card F : ℝ)^2 *
        ∑ T ∈ eligibleTuples g, p T := by
    calc
      _ ≤ ∑ T ∈ eligibleTuples g, ∑ _i : Fin 4, ∑ _d : Direction F,
          2 * p T / (Fintype.card F : ℝ)^2 := by
        simp only [freshTests, Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
        apply Finset.sum_le_sum
        intro T hT
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro d hd
        by_cases hf : d ∉ D ∧ d ∉ generatorSet T
        · simp only [hf]
          exact OppositeFreshConditional.pair_probability_le D a g T d hf.1 hf.2 i (i+2)
        · simp only [hf, ite_false]
          exact div_nonneg (mul_nonneg (by norm_num) (hp T)) (by positivity)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          Direction, Fintype.card_option, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T _
        ring
  have hbound : (∫ M, ((freshWitnesses g D M).card : ℝ) ∂μ) ≤
      327680 * ((m : ℝ)+1)^4 := by
    calc
      _ ≤ ∫ M, (((freshTests g D).filter (fun w => M ∈ freshEvent g w)).card : ℝ) ∂μ := by
        apply integral_mono Integrable.of_finite Integrable.of_finite
        intro M
        exact Nat.cast_le.mpr (Finset.card_le_card (freshWitnesses_subset_events g D M))
      _ = ∑ w ∈ freshTests g D,
          ((CandidateExposure.exposedLaw D a).toOuterMeasure (freshEvent g w)).toReal :=
        integral_eventCount_eq_sum _ _ _
      _ ≤ _ := hsum
      _ ≤ 8 * ((Fintype.card F : ℝ)+1) / (Fintype.card F : ℝ)^2 *
          ((20480 * ((m : ℝ)+1)^4) * Fintype.card F) := by
        exact mul_le_mul_of_nonneg_left hmean (by positivity)
      _ ≤ _ := by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ (by positivity : 0 < (Fintype.card F : ℝ)^2)).mpr
        have hpos : 0 ≤ ((m : ℝ)+1)^4 := by positivity
        nlinarith [mul_nonneg hpos (mul_nonneg hq.le (sub_nonneg.mpr hq1))]
  rw [PMF.integral_eq_sum] at hbound
  simpa only [smul_eq_mul] using hbound

end
end Balanced.OppositeAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_OppositeAssembly
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.OppositeAssembly

noncomputable section
open scoped Classical BigOperators
open CandidateExposure CandidateValidityWitness MeasureTheory ConditionalRestriction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem meanBound_nonneg (m : ℕ) : 0 ≤ meanBound m := by unfold meanBound; positivity

theorem witnesses_mean_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
      ((witnesses g M).card : ℝ)) ≤ meanBound m := by
  have hold : (∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
      ((oldFreshWitnesses g D M).card : ℝ)) ≤ 2048 * (m : ℝ) := by
    calc
      _ ≤ ∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
          (ExposedOppositeSum.oldOppositeFreshCount g D M : ℝ) := by
        apply Finset.sum_le_sum
        intro M _
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        exact_mod_cast oldFreshWitnesses_card_le g D M
      _ ≤ 2048 * (D.card : ℝ) := ExposedOppositeSum.oldOppositeFreshCount_mean_le g D a
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
        (((freshWitnesses g D M).card : ℝ) + ((oldFreshWitnesses g D M).card : ℝ) +
          ((CandidateOldOpposite.overlappingWitnesses g D M).card : ℝ)) := by
      apply Finset.sum_le_sum
      intro M _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      exact_mod_cast witnesses_card_le_cases g D M
    _ = (∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
          ((freshWitnesses g D M).card : ℝ)) +
        (∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
          ((oldFreshWitnesses g D M).card : ℝ)) +
        (∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
          ((CandidateOldOpposite.overlappingWitnesses g D M).card : ℝ)) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ meanBound m := add_le_add
      (add_le_add (freshWitnesses_mean_le g D a m hD) hold)
      (CandidateOldOpposite.expected_overlappingWitnesses_le g D a m hD)

theorem witnessPatternModel_support_card (g : Direction F) (w : Label F) :
    ((witnessPatternModel g).support w).card ≤ 5 := by
  change (insert w.2 (generatorSet w.1.1)).card ≤ 5
  have h := Finset.card_insert_le w.2 (generatorSet w.1.1)
  have hG : (generatorSet w.1.1).card ≤ 4 :=
    Finset.card_image_le.trans (by simp)
  omega

theorem witnessPatternModel_count (g : Direction F) (M : MergedPairs F) :
    (witnessPatternModel g).count M = ((witnesses g M).card : ℝ) := by
  simp only [PatternModel.count,PatternModel.indicator,witnessPatternModel,
    Set.indicator_apply,Set.mem_ofPred_eq]
  rw [← Finset.sum_filter]
  simp
  congr 1
  ext label
  simp only [Finset.mem_filter]
  exact ⟨And.right, fun hlabel => ⟨Finset.mem_univ label, hlabel⟩⟩

attribute [local instance] OAI.Balanced.OppositeAssembly.instMeasurableSpace_solutions_1
theorem witnessPatternModel_fixedExpectation (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (f : MergedPairs F → ℝ) :
    (witnessPatternModel g).fixedExpectation D a f =
      ∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal * f M := by
  have hfix : (witnessPatternModel g).fixCoordinates D a =
      fixArray (fun d => d ∈ D) a := by
    funext M d
    simp only [PatternModel.fixCoordinates,fixArray]
    congr 1
  unfold PatternModel.fixedExpectation
  rw [hfix]
  change (∫ M, f (fixArray (fun d => d ∈ D) a M) ∂Measure.pi
    (fun _ : Direction F => (PMF.uniformOfFintype (Bool → F)).toMeasure)) = _
  rw [integral_fixArray_eq_filtered,PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  congr 1
  funext M
  congr 2
  simp only [CandidateExposure.exposedLaw,PartialAlignment.offsetLaw_eq_uniform]

theorem witnessPatternModel_fixed_count_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (witnessPatternModel g).fixedExpectation D a (witnessPatternModel g).count ≤
      meanBound m := by
  erw [witnessPatternModel_fixedExpectation]
  simp_rw [witnessPatternModel_count]
  exact witnesses_mean_le g D a m hD

theorem witnesses_moment_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m s : ℕ) (hD : D.card ≤ m) :
    (∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
      ((witnesses g M).card : ℝ)^s) ≤ (meanBound (m+(s-1)*5))^s := by
  let P := witnessPatternModel g
  have hbound (K : Finset P.Color) (hK : K.card ≤ (s-1)*5) (y : P.Sample) :
      P.fixedExpectation (D ∪ K) y P.count ≤ meanBound (m+(s-1)*5) := by
    exact witnessPatternModel_fixed_count_le g (D ∪ K) y (m+(s-1)*5)
      ((Finset.card_union_le D K).trans (Nat.add_le_add hD hK))
  have h := P.fixed_moment_le_pow D a 5 s (meanBound (m+(s-1)*5))
    (meanBound_nonneg _) (witnessPatternModel_support_card g) hbound
  erw [witnessPatternModel_fixedExpectation] at h
  simpa only [P,witnessPatternModel_count] using h

end
end Balanced.OppositeAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_OppositeTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.OppositeTail

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Filter CandidateExposure OppositeAssembly

section FiniteMarkov
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

private theorem power_tail_le (p : PMF Ω) (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x)
    (t : ℝ) (ht : 0 < t) (s : ℕ) :
    p.toMeasure.real {x | t ≤ f x} ≤ (∫ x, f x ^ s ∂p.toMeasure) / t ^ s := by
  have hsub : {x | t ≤ f x} ⊆ {x | t ^ s ≤ f x ^ s} :=
    fun x hx => pow_le_pow_left₀ ht.le hx s
  have hm := measureReal_mono (μ := p.toMeasure) hsub
  have hk := mul_meas_ge_le_integral_of_nonneg
    (μ := p.toMeasure) (f := fun x => f x ^ s)
    (Filter.Eventually.of_forall fun x => pow_nonneg (hf x) s)
    Integrable.of_finite (t ^ s)
  apply (le_div_iff₀ (pow_pos ht s)).mpr
  exact (mul_le_mul_of_nonneg_right hm (pow_pos ht s).le).trans
    (by simpa only [mul_comm] using hk)
end FiniteMarkov

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
attribute [local instance] OAI.Balanced.OppositeTail.instMeasurableSpace_solutions
local instance instMeasurableSingletonClass_solutions : MeasurableSingletonClass F := ⟨fun _ => trivial⟩

theorem exposedLaw_empty (a : MergedPairs F) : exposedLaw ∅ a = offsetLaw F := by
  apply PMF.ext
  intro M
  simp [exposedLaw, PMF.filter_apply]
  rw [← tsum_fintype (L := .unconditional _), PMF.tsum_coe]
  simp

theorem conditional_witness_tail_le (g : Direction F)
    (old : Finset (Direction F)) (a : MergedPairs F) (m s : ℕ)
    (hm : old.card ≤ m) (t : ℝ) (ht : 0 < t) :
    ((exposedLaw old a).toOuterMeasure
      {M | t ≤ ((witnesses g M).card : ℝ)}).toReal ≤
      (meanBound (m + (s - 1) * 5))^s / t^s := by
  have h := power_tail_le (exposedLaw old a)
    (fun M => ((witnesses g M).card : ℝ)) (fun _ => Nat.cast_nonneg _)
    t ht s
  have he := witnesses_moment_le g old a m s hm
  rw [PMF.integral_eq_sum] at h
  simp only [smul_eq_mul] at h
  have hreal : (exposedLaw old a).toMeasure.real
      {M | t ≤ ((witnesses g M).card : ℝ)} =
      ((exposedLaw old a).toOuterMeasure
      {M | t ≤ ((witnesses g M).card : ℝ)}).toReal := by
    rw [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (Set.to_countable _).measurableSet]
  rw [hreal] at h
  exact h.trans (div_le_div_of_nonneg_right he (pow_pos ht s).le)

theorem single_direction_tail_le (g : Direction F) :
    offsetEventProbability {M : MergedPairs F |
      (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤
        ((witnesses g M).card : ℝ)} ≤
      tailConstant / (Fintype.card F : ℝ)^3 := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have h := conditional_witness_tail_le g ∅ (fun _ _ => (0 : F)) 0 300
    (by simp) ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ)) (Real.rpow_pos_of_pos hq _)
  rw [exposedLaw_empty] at h
  have hp : ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ)) ^ (300 : ℕ) =
      (Fintype.card F : ℝ)^3 := by
    rw [← Real.rpow_mul_natCast hq.le]
    norm_num
  rw [hp] at h
  simpa only [offsetEventProbability, tailConstant, Nat.zero_add] using h

theorem some_direction_tail_le :
    offsetEventProbability {M : MergedPairs F | ∃ g : Direction F,
      (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤
        ((witnesses g M).card : ℝ)} ≤
      2 * tailConstant / (Fintype.card F : ℝ)^2 := by
  let E (g : Direction F) : Set (MergedPairs F) := {M |
    (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤
      ((witnesses g M).card : ℝ)}
  have heq : {M : MergedPairs F | ∃ g : Direction F, M ∈ E g} = ⋃ g, E g := by
    ext M
    simp
  have hr (A : Set (MergedPairs F)) : (offsetLaw F).toMeasure.real A =
      offsetEventProbability A := by
    rw [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (Set.to_countable _).measurableSet]
    rfl
  have hu := measureReal_iUnion_fintype_le (μ := (offsetLaw F).toMeasure) E
  simp_rw [hr] at hu
  change offsetEventProbability {M : MergedPairs F | ∃ g : Direction F, M ∈ E g} ≤ _
  rw [heq]
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hq0 : (0 : ℝ) < Fintype.card F := lt_of_lt_of_le (by norm_num) hq
  have hB : 0 ≤ tailConstant := by unfold tailConstant; exact pow_nonneg (meanBound_nonneg _) _
  calc
    _ ≤ ∑ g : Direction F, offsetEventProbability (E g) := hu
    _ ≤ ∑ _g : Direction F, tailConstant / (Fintype.card F : ℝ)^3 := by
      apply Finset.sum_le_sum
      intro g _
      exact single_direction_tail_le g
    _ = ((Fintype.card F : ℝ) + 1) * (tailConstant / (Fintype.card F : ℝ)^3) := by
      simp [Direction, Nat.cast_add, Nat.cast_one]
    _ ≤ (2 * (Fintype.card F : ℝ)) * (tailConstant / (Fintype.card F : ℝ)^3) := by
      apply mul_le_mul_of_nonneg_right (by linarith only [hq])
        (div_nonneg hB (pow_pos hq0 3).le)
    _ = _ := by field_simp

theorem tendsto_some_direction_tail
    (K : ℕ → Type*) [∀ n, Field (K n)] [∀ n, Fintype (K n)]
    [∀ n, DecidableEq (K n)]
    (hq : Tendsto (fun n => Fintype.card (K n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability {M : MergedPairs (K n) |
      ∃ g : Direction (K n), (Fintype.card (K n) : ℝ) ^ (1 / 100 : ℝ) ≤
        ((witnesses g M).card : ℝ)}) atTop (𝓝 0) := by
  have hreal : Tendsto (fun n => (Fintype.card (K n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  have hz : Tendsto (fun n => 2 * tailConstant / (Fintype.card (K n) : ℝ)^2)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, div_eq_mul_inv, inv_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero] using
      ((tendsto_inv_atTop_zero.comp hreal).pow 2).const_mul (2 * tailConstant)
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg)
    (fun n => some_direction_tail_le (F := K n)) hz

end
end Balanced.OppositeTail

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateOppositeTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateValidityAssembly

noncomputable section
open scoped Classical Topology
open TupleAlignment CandidateExposure CandidateValidityWitness Filter

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem oppositeFailures_witness_cover (M : MergedPairs F) (g : Direction F)
    (a : RootPrescription g) (ha : a ∈ oppositeFailures M g) :
    ∃ w ∈ OppositeAssembly.witnesses g M, w.1.1 = a.tuple := by
  obtain ⟨hs, i, d, hd, hdT, hp⟩ := Finset.mem_filter.mp ha
  refine ⟨((a.tuple, i), d), ?_, rfl⟩
  apply (OppositeAssembly.mem_witnesses g M a.tuple i d).mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.injective,
    fun j => (a.1 j).2⟩, ?_, hd, hdT, hp⟩
  exact (Finset.mem_filter.mp hs).2

theorem oppositeFailures_card_le_witnesses (M : MergedPairs F) (g : Direction F) :
    (oppositeFailures M g).card ≤ (OppositeAssembly.witnesses g M).card :=
  card_le_witnesses (oppositeFailures M g) (OppositeAssembly.witnesses g M)
    (fun w => w.1.1) (oppositeFailures_witness_cover M g)

theorem tendsto_oppositeFailures_some_large
    (K : ℕ → Type*) [∀ n, Field (K n)] [∀ n, Fintype (K n)]
    [∀ n, DecidableEq (K n)]
    (hq : Tendsto (fun n => Fintype.card (K n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability {M : MergedPairs (K n) |
      ∃ g, Fintype.card (K n) < (oppositeFailures M g).card}) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) ?_
    (OppositeTail.tendsto_some_direction_tail K hq)
  intro n
  apply pmf_outerReal_mono (offsetLaw (K n))
  rintro M ⟨g, hg⟩
  refine ⟨g, ?_⟩
  have hq1 : (1 : ℝ) ≤ Fintype.card (K n) := by
    exact_mod_cast Fintype.card_pos (α := K n)
  have hp : (Fintype.card (K n) : ℝ) ^ (1 / 100 : ℝ) ≤ Fintype.card (K n) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num : (1 / 100 : ℝ) ≤ 1)
  exact hp.trans ((show (Fintype.card (K n) : ℝ) ≤
    ((oppositeFailures M g).card : ℝ) by exact_mod_cast le_of_lt hg).trans
      (Nat.cast_le.mpr (oppositeFailures_card_le_witnesses M g)))

end
end Balanced.CandidateValidityAssembly

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

theorem tendsto_constituent_losses
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability {M : MergedPairs (F n) |
      ∀ g, (CandidatePrescribed.constituentTargetCodes M g).card ≤ Fintype.card (F n)})
      atTop (𝓝 1) := by
  have hbad : Tendsto (fun n => offsetEventProbability {M : MergedPairs (F n) |
      ∃ g, Fintype.card (F n) < (CandidatePrescribed.constituentTargetCodes M g).card})
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) ?_
      (CandidateConstituentTail.tendsto_some_direction_tail F hq)
    intro n
    apply pmf_outerReal_mono (offsetLaw (F n))
    rintro M ⟨g, hg⟩
    refine ⟨g, ?_⟩
    have hq1 : (1 : ℝ) ≤ Fintype.card (F n) := by
      exact_mod_cast Fintype.card_pos (α := F n)
    have hp : (Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ) ≤ Fintype.card (F n) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num : (1 / 100 : ℝ) ≤ 1)
    exact hp.trans (by exact_mod_cast le_of_lt hg)
  apply tendsto_good_of_bad F _ _ (fun n => ?_) hbad
  ext M
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_lt]

attribute [local instance] OAI.Balanced.CandidateAbundanceAssembly.abundanceAssemblyMeasurableSpace
theorem tendsto_candidateSlots_of_witness_tails
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    (hopp : Tendsto (fun n => offsetEventProbability {M : MergedPairs (F n) |
      ∃ g, Fintype.card (F n) < (oppositeFailures M g).card}) atTop (𝓝 0))
    (hext : Tendsto (fun n => offsetEventProbability {M : MergedPairs (F n) |
      ∃ g, Fintype.card (F n) < (externalFailures M g).card}) atTop (𝓝 0)) :
    Tendsto (fun n => offsetEventProbability {M : MergedPairs (F n) |
      ∀ s, slotLinearConstant * Fintype.card (F n) ≤ ((candidateSlot M s).card : ℝ) ∧
        (candidateSlot M s).card ≤ Fintype.card (F n)}) atTop (𝓝 1) := by
  let H (n : ℕ) : Set (MergedPairs (F n)) :=
    {M | ∀ g, 8 * Fintype.card (F n) ≤ rootSuccessCount g M}
  let Y (n : ℕ) : Set (MergedPairs (F n)) :=
    {M | ∀ g, (rootFiberSquareCount M g : ℝ) ≤ pairLinearThreshold * Fintype.card (F n)}
  let C (n : ℕ) : Set (MergedPairs (F n)) :=
    {M | ∀ g, (CandidatePrescribed.constituentTargetCodes M g).card ≤ Fintype.card (F n)}
  let O (n : ℕ) : Set (MergedPairs (F n)) :=
    {M | ∀ g, (oppositeFailures M g).card ≤ Fintype.card (F n)}
  let E (n : ℕ) : Set (MergedPairs (F n)) :=
    {M | ∀ g, (externalFailures M g).card ≤ Fintype.card (F n)}
  have hO : Tendsto (fun n => offsetEventProbability (O n)) atTop (𝓝 1) := by
    apply tendsto_good_of_bad F _ _ (fun n => ?_) hopp
    ext M
    simp only [O, Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_lt]
  have hE : Tendsto (fun n => offsetEventProbability (E n)) atTop (𝓝 1) := by
    apply tendsto_good_of_bad F _ _ (fun n => ?_) hext
    ext M
    simp only [E, Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_lt]
  have hHY := tendsto_pmf_outerReal_inter_of_good (fun n => offsetLaw (F n))
    H Y (tendsto_successful_roots F hq) (tendsto_square_fibers F hq)
  have hHYC := tendsto_pmf_outerReal_inter_of_good (fun n => offsetLaw (F n))
    (fun n => H n ∩ Y n) C hHY (tendsto_constituent_losses F hq)
  have hHYCO := tendsto_pmf_outerReal_inter_of_good (fun n => offsetLaw (F n))
    (fun n => (H n ∩ Y n) ∩ C n) O hHYC hO
  have hall := tendsto_pmf_outerReal_inter_of_good (fun n => offsetLaw (F n))
    (fun n => ((H n ∩ Y n) ∩ C n) ∩ O n) E hHYCO hE
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hall tendsto_const_nhds
  · intro n
    apply pmf_outerReal_mono (offsetLaw (F n))
    rintro M ⟨⟨⟨⟨hH, hY⟩, hC⟩, hO⟩, hE⟩ s
    exact ⟨candidateSlot_lower_bound_of_failures M s pairLinearThreshold_pos
      (hH s.1) (hC s.1) (hO s.1) (hE s.1) (hY s.1), candidateSlot_card_le M s⟩
  · intro n
    change offsetEventProbability (F := F n) _ ≤ 1
    rw [← measureReal_eq_offset]
    exact measureReal_le_one

theorem tendsto_candidateSlots_of_external_tail
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    (hext : Tendsto (fun n => offsetEventProbability {M : MergedPairs (F n) |
      ∃ g, Fintype.card (F n) < (externalFailures M g).card}) atTop (𝓝 0)) :
    Tendsto (fun n => offsetEventProbability {M : MergedPairs (F n) |
      ∀ s, slotLinearConstant * Fintype.card (F n) ≤ ((candidateSlot M s).card : ℝ) ∧
        (candidateSlot M s).card ≤ Fintype.card (F n)}) atTop (𝓝 1) :=
  tendsto_candidateSlots_of_witness_tails F hq
    (tendsto_oppositeFailures_some_large F hq) hext

end Limits
end
end Balanced.CandidateAbundanceAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_ExternalWitnessModel
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

theorem exists_witness_iff (g : Direction F) (M : MergedPairs F) (T : FourTuple F) :
    (∃ ij : Fin 4 × Fin 4, ∃ de : Direction F × Direction F,
      ((T, ij), de) ∈ witnesses g M) ↔
    SuccessfulOn M T (targetLine g M T) ∧
      ExternalDoubleWitness M T (targetLine g M T) := by
  constructor
  · rintro ⟨⟨i,j⟩, ⟨d,e⟩, hw⟩
    obtain ⟨hs, hij, hde, hd, he, hdT, heT, x, hx, hex, hdi, hej⟩ :=
      (mem_witnesses g M _).mp hw
    exact ⟨hs, x, i, j, d, e, hx, hex, hij, hde, hd, he, hdT, heT, hdi, hej⟩
  · rintro ⟨hs, x, i, j, d, e, hx, hex, hij, hde, hd, he, hdT, heT, hdi, hej⟩
    exact ⟨(i,j), (d,e), (mem_witnesses g M _).mpr
      ⟨hs, hij, hde, hd, he, hdT, heT, x, hx, hex, hdi, hej⟩⟩

end
end Balanced.ExternalAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateExternalTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateValidityAssembly

noncomputable section
open scoped Classical BigOperators
open TupleAlignment CandidateValidityWitness

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem externalFailures_witness_cover (M : MergedPairs F) (g : Direction F)
    (a : RootPrescription g) (ha : a ∈ externalFailures M g) :
    ∃ w ∈ ExternalAssembly.witnesses g M, w.1.1 = a.tuple := by
  obtain ⟨hs, hext⟩ := Finset.mem_filter.mp ha
  have hsuccess := successfulOn_of_mem hs
  have hline : ExternalAssembly.targetLine g M a.tuple = (a.choice M).line := rfl
  obtain ⟨ij, de, hw⟩ := (ExternalAssembly.exists_witness_iff g M a.tuple).mpr
    (by simpa only [hline] using And.intro hsuccess hext)
  exact ⟨((a.tuple, ij), de), hw, rfl⟩

theorem externalFailures_card_le_witnesses (M : MergedPairs F) (g : Direction F) :
    (externalFailures M g).card ≤ (ExternalAssembly.witnesses g M).card :=
  card_le_witnesses (externalFailures M g) (ExternalAssembly.witnesses g M)
    (fun w => w.1.1) (externalFailures_witness_cover M g)

end
end Balanced.CandidateValidityAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_ExternalWitnessTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ExternalWitnessTail

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Filter CandidateExposure ExternalAssembly

section FiniteMarkov
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

private theorem power_tail_le (p : PMF Ω) (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x)
    (t : ℝ) (ht : 0 < t) (s : ℕ) :
    p.toMeasure.real {x | t ≤ f x} ≤ (∫ x, f x ^ s ∂p.toMeasure) / t ^ s := by
  have hsub : {x | t ≤ f x} ⊆ {x | t ^ s ≤ f x ^ s} :=
    fun x hx => pow_le_pow_left₀ ht.le hx s
  have hm := measureReal_mono (μ := p.toMeasure) hsub
  have hk := mul_meas_ge_le_integral_of_nonneg
    (μ := p.toMeasure) (f := fun x => f x ^ s)
    (Filter.Eventually.of_forall fun x => pow_nonneg (hf x) s)
    Integrable.of_finite (t ^ s)
  apply (le_div_iff₀ (pow_pos ht s)).mpr
  exact (mul_le_mul_of_nonneg_right hm (pow_pos ht s).le).trans
    (by simpa only [mul_comm] using hk)
end FiniteMarkov

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
attribute [local instance] OAI.Balanced.ExternalWitnessTail.instMeasurableSpace_solutions
local instance instMeasurableSingletonClass_solutions : MeasurableSingletonClass F := ⟨fun _ => trivial⟩

theorem single_direction_tail_le (B : ℝ) (g : Direction F)
    (hmoment : (∫ M, ((witnesses g M).card : ℝ)^400 ∂(offsetLaw F).toMeasure) ≤ B) :
    offsetEventProbability {M : MergedPairs F |
      (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤ ((witnesses g M).card : ℝ)} ≤
      B / (Fintype.card F : ℝ)^4 := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have h := power_tail_le (offsetLaw F) (fun M => ((witnesses g M).card : ℝ))
    (fun _ => Nat.cast_nonneg _) ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ))
    (Real.rpow_pos_of_pos hq _) 400
  have hp : ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ)) ^ (400 : ℕ) =
      (Fintype.card F : ℝ)^4 := by
    rw [← Real.rpow_mul_natCast hq.le]
    norm_num
  rw [hp] at h
  have hr (E : Set (MergedPairs F)) : (offsetLaw F).toMeasure.real E =
      offsetEventProbability E := by
    rw [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure_apply _
      (Set.to_countable _).measurableSet]
    rfl
  rw [hr] at h
  exact h.trans (div_le_div_of_nonneg_right hmoment (pow_pos hq 4).le)

theorem some_direction_tail_le (B : ℝ) (hB : 0 ≤ B)
    (hmoment : ∀ g : Direction F,
      (∫ M, ((witnesses g M).card : ℝ)^400 ∂(offsetLaw F).toMeasure) ≤ B) :
    offsetEventProbability {M : MergedPairs F | ∃ g : Direction F,
      (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤
        ((witnesses g M).card : ℝ)} ≤
      2 * B / (Fintype.card F : ℝ)^3 := by
  let E (g : Direction F) : Set (MergedPairs F) := {M |
    (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤
      ((witnesses g M).card : ℝ)}
  have heq : {M : MergedPairs F | ∃ g : Direction F, M ∈ E g} = ⋃ g, E g := by
    ext M
    simp
  have hr (A : Set (MergedPairs F)) : (offsetLaw F).toMeasure.real A =
      offsetEventProbability A := by
    rw [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (Set.to_countable _).measurableSet]
    rfl
  have hu := measureReal_iUnion_fintype_le (μ := (offsetLaw F).toMeasure) E
  simp_rw [hr] at hu
  change offsetEventProbability {M : MergedPairs F | ∃ g : Direction F, M ∈ E g} ≤ _
  rw [heq]
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hq0 : (0 : ℝ) < Fintype.card F := lt_of_lt_of_le (by norm_num) hq
  calc
    _ ≤ ∑ g : Direction F, offsetEventProbability (E g) := hu
    _ ≤ ∑ _g : Direction F, B / (Fintype.card F : ℝ)^4 := by
      apply Finset.sum_le_sum
      intro g _
      exact single_direction_tail_le B g (hmoment g)
    _ = ((Fintype.card F : ℝ) + 1) * (B / (Fintype.card F : ℝ)^4) := by
      simp [Direction, Nat.cast_add, Nat.cast_one]
    _ ≤ (2 * (Fintype.card F : ℝ)) * (B / (Fintype.card F : ℝ)^4) := by
      apply mul_le_mul_of_nonneg_right (by linarith only [hq])
        (div_nonneg hB (pow_pos hq0 4).le)
    _ = _ := by field_simp

theorem tendsto_some_direction_tail (B : ℝ) (hB : 0 ≤ B)
    (K : ℕ → Type*) [∀ n, Field (K n)] [∀ n, Fintype (K n)]
    [∀ n, DecidableEq (K n)]
    (hq : Tendsto (fun n => Fintype.card (K n)) atTop atTop)
    (hmoment : ∀ n (g : Direction (K n)),
      (∫ M, ((witnesses g M).card : ℝ)^400 ∂(offsetLaw (K n)).toMeasure) ≤ B) :
    Tendsto (fun n => offsetEventProbability {M : MergedPairs (K n) |
      ∃ g : Direction (K n), (Fintype.card (K n) : ℝ) ^ (1 / 100 : ℝ) ≤
        ((witnesses g M).card : ℝ)}) atTop (𝓝 0) := by
  have hreal : Tendsto (fun n => (Fintype.card (K n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  have hz : Tendsto (fun n => 2 * B / (Fintype.card (K n) : ℝ)^3)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, div_eq_mul_inv, inv_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero] using
      ((tendsto_inv_atTop_zero.comp hreal).pow 3).const_mul (2 * B)
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg)
    (fun n => some_direction_tail_le (F := K n) B hB (hmoment n)) hz

theorem candidateSlots_of_uniform_moment_oai (B : ℝ) (hB : 0 ≤ B)
    (K : ℕ → Type*) [∀ n, Field (K n)] [∀ n, Fintype (K n)]
    [∀ n, DecidableEq (K n)]
    (hq : Tendsto (fun n => Fintype.card (K n)) atTop atTop)
    (hmoment : ∀ n (g : Direction (K n)),
      (∫ M, ((witnesses g M).card : ℝ)^400 ∂(offsetLaw (K n)).toMeasure) ≤ B) :
    Tendsto (fun n => offsetEventProbability {M : MergedPairs (K n) |
      ∀ s, CandidateAbundanceAssembly.slotLinearConstant * Fintype.card (K n) ≤
        ((candidateSlot M s).card : ℝ) ∧
        (candidateSlot M s).card ≤ Fintype.card (K n)}) atTop (𝓝 1) := by
  apply CandidateAbundanceAssembly.tendsto_candidateSlots_of_external_tail K hq
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) ?_
    (tendsto_some_direction_tail B hB K hq hmoment)
  intro n
  apply pmf_outerReal_mono (offsetLaw (K n))
  rintro M ⟨g, hg⟩
  refine ⟨g, ?_⟩
  have hq1 : (1 : ℝ) ≤ Fintype.card (K n) := by
    exact_mod_cast Fintype.card_pos (α := K n)
  have hp : (Fintype.card (K n) : ℝ) ^ (1 / 100 : ℝ) ≤ Fintype.card (K n) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num : (1 / 100 : ℝ) ≤ 1)
  exact hp.trans ((show (Fintype.card (K n) : ℝ) ≤
    ((CandidateValidityAssembly.externalFailures M g).card : ℝ) by
      exact_mod_cast le_of_lt hg).trans (Nat.cast_le.mpr
        (CandidateValidityAssembly.externalFailures_card_le_witnesses M g)))

end
end Balanced.ExternalWitnessTail

end OAI
end

theorem solution.{u_2} : type_of% @OAI.Balanced.ExternalWitnessTail.candidateSlots_of_uniform_moment_oai.{u_2} := @OAI.Balanced.ExternalWitnessTail.candidateSlots_of_uniform_moment_oai.{u_2}
