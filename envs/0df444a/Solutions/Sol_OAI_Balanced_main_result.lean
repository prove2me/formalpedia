-- Prove2me | solution 1 for OAI.Balanced.main_result
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:28:58.484423+00:00
-- url     : https://prove2.me/submissions/b6dcff64-e78e-4425-9713-8f7de933524f

import Mathlib
import Definitions.Def_BalancedRyser
import Definitions.Def_OAIQ63Br004
import Theorems.Thm_OAI_Balanced_deletion_domination
import Theorems.Thm_OAI_Balanced_deterministic_reduction
import Theorems.Thm_OAI_Balanced_pencil_local
import Theorems.Thm_OAI_Balanced_robust_deletion

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_Hypergraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PartiteHypergraph

variable {r n : ℕ}

@[simp] theorem covers_empty_iff (H : PartiteHypergraph r n) :
    H.Covers ∅ ↔ H.edges = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    rcases h e he with ⟨i, hi⟩
    exact Finset.notMem_empty _ hi
  · intro h e he
    simp [h] at he

end Balanced.PartiteHypergraph

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_DeletionFieldTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Balanced.FieldTransport

variable {F G : Type*} [Field F] [Field G]

variable [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]

omit [DecidableEq F] [DecidableEq G] in
@[simp] theorem cardinal_field (e : F ≃+* G) : Fintype.card G = Fintype.card F :=
  (Fintype.card_congr e.toEquiv).symm

end Balanced.FieldTransport

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_SelectedDeletionEventsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Balanced.SelectedDeletion

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {κ : Kernel F} {c C : ℝ}

theorem sum_deletionEventIndicator (hκ : IsExperiment κ c C)
    (E : Finset (Line F) → Prop) (M : MergedPairs F) (s : Output F) :
    (∑ D : DeletionSet F 3,
      if E D.val then
        (if (configuration M s).deletedLines = D.val then κ M s else 0)
      else 0) =
      if E (configuration M s).deletedLines then κ M s else 0 := by
  classical
  calc
    _ = ∑ D : DeletionSet F 3,
        if (configuration M s).deletedLines = D.val then
          (if E (configuration M s).deletedLines then κ M s else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro D _
      by_cases h : (configuration M s).deletedLines = D.val
      · simp [h]
      · simp [h]
    _ = _ := by
      by_cases hE : E (configuration M s).deletedLines
      · simp only [ite_eq_left hE]
        exact sum_deletionIndicator hκ M s
      · simp [hE]

theorem sum_event_deletionJointMass (hκ : IsExperiment κ c C)
    (E : Finset (Line F) → Prop) :
    (∑ D : DeletionSet F 3, if E D.val then deletionJointMass κ D else 0) =
      jointMass κ (fun M s => E (configuration M s).deletedLines) := by
  classical
  have hsplit : ∀ D : DeletionSet F 3,
      (if E D.val then deletionJointMass κ D else 0) =
      ∑ M, ((offsetLaw F) M).toReal * ∑ s,
        if E D.val then
          (if (configuration M s).deletedLines = D.val then κ M s else 0)
        else 0 := by
    intro D
    by_cases h : E D.val
    · simp only [ite_eq_left h, deletionJointMass, jointMass]
      apply Finset.sum_congr rfl
      intro M _
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)
    · simp [h]
  simp_rw [hsplit]
  unfold jointMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  convert sum_deletionEventIndicator hκ E M s using 1
  all_goals try with_reducible_and_instances rfl

theorem realizingLaw_eventProbability (hκ : IsExperiment κ c C)
    (Q : PMF (DeletionSet F 3)) (hQ : RealizesConditionalLaw κ Q)
    (E : Finset (Line F) → Prop) :
    deletionEventProbability Q (fun D => E D.val) =
      jointMass κ (fun M s => E (configuration M s).deletedLines) / successMass κ := by
  classical
  change (∑ D : DeletionSet F 3, if E D.val then (Q D).toReal else 0) = _
  calc
    _ = ∑ D : DeletionSet F 3,
        (if E D.val then deletionJointMass κ D else 0) / successMass κ := by
      apply Finset.sum_congr rfl
      intro D _
      by_cases h : E D.val
      · simpa only [ite_eq_left h] using hQ D
      · simp [h]
    _ = _ := by rw [← Finset.sum_div, sum_event_deletionJointMass hκ E]

theorem jointMass_eq_success_mul_eventProbability (hκ : IsExperiment κ c C)
    (hsuccess : 0 < successMass κ)
    (Q : PMF (DeletionSet F 3)) (hQ : RealizesConditionalLaw κ Q)
    (E : Finset (Line F) → Prop) :
    jointMass κ (fun M s => E (configuration M s).deletedLines) =
      successMass κ * deletionEventProbability Q (fun D => E D.val) := by
  rw [realizingLaw_eventProbability hκ Q hQ E]
  field_simp [ne_of_gt hsuccess]

end Balanced.SelectedDeletion

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffineDoubleCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open scoped BigOperators

section DoubleCounting

variable {P L : Type*} [Fintype L]
variable (I : P → L → Prop) [DecidableRel I]

theorem sum_line_count_eq_sum_point_count (U : Finset P) :
    (∑ l : L, (U.filter fun p => I p l).card) =
      ∑ p ∈ U, ((Finset.univ : Finset L).filter fun l => I p l).card := by
  simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow] using
    (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (r := I) (s := U) (t := Finset.univ)).symm

theorem sum_line_count (U : Finset P) (r : ℕ)
    (hpoint : ∀ p ∈ U,
      ((Finset.univ : Finset L).filter fun l => I p l).card = r) :
    (∑ l : L, (U.filter fun p => I p l).card) = r * U.card := by
  rw [sum_line_count_eq_sum_point_count]
  calc
    (∑ p ∈ U, ((Finset.univ : Finset L).filter fun l => I p l).card) =
        ∑ _p ∈ U, r := Finset.sum_congr rfl hpoint
    _ = r * U.card := by simp [Nat.mul_comm]

end DoubleCounting

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffineMomentAlgebraLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace Balanced.StabilityAffineArithmetic

theorem auxiliary_degree_lt_quarter {q δ d : ℝ} (hq : 100 ≤ q) (_hd : 0 ≤ d)
    (hdegree : d ^ 2 < 2 * δ) (hskew : δ < (201 / 10000 : ℝ) * q ^ 2) :
    d < q / 4 := by
  by_contra hn
  have hdn : q / 4 ≤ d := le_of_not_gt hn
  have hp := mul_nonneg (show 0 ≤ d - q / 4 by linarith)
    (show 0 ≤ d + q / 4 by linarith)
  nlinarith

theorem tangent_margin {q b δ d : ℝ} (hq : 100 ≤ q) (hb : b ≤ q) (hd : 0 ≤ d)
    (hdegree : d ^ 2 < 2 * δ) (hskew : δ < (201 / 10000 : ℝ) * q ^ 2) :
    d + 1 < (2 / 3 : ℝ) * (2 * q - b - 2 * δ / (q + 1)) := by
  have hdq := auxiliary_degree_lt_quarter hq hd hdegree hskew
  have hqpos : 0 < q + 1 := by linarith
  have hratio : 2 * δ / (q + 1) < q / 20 := by
    apply (div_lt_iff₀ hqpos).2
    nlinarith [sq_nonneg q]
  linarith

end Balanced.StabilityAffineArithmetic

end

section

namespace Balanced.StabilityArithmetic

theorem delta_pos {ζ : ℝ} (hζ : 0 < ζ) :
    0 < min (ζ / 4) (1 / 100 : ℝ) := by
  exact lt_min (by positivity) (by norm_num)

theorem hole_bound {q h Δ ζ : ℝ} (hq : 100 ≤ q)
    (hh : h < min (ζ / 4) (1 / 100 : ℝ) * q ^ 2)
    (hΔ : Δ ≤ h + q + 1) :
    Δ < (201 / 10000 : ℝ) * q ^ 2 := by
  have hmin : min (ζ / 4) (1 / 100 : ℝ) ≤ 1 / 100 := min_le_right _ _
  have hm := mul_le_mul_of_nonneg_right hmin (sq_nonneg q)
  have hfactor : 0 ≤ (q - 100) * (101 * q + 100) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem reduction_bounds {q ζ h Δ : ℝ} (hq : 100 ≤ q) (hζ : 0 < ζ)
    (hthreshold : 4 / ζ ≤ q)
    (hh : h < min (ζ / 4) (1 / 100 : ℝ) * q ^ 2)
    (hΔ : Δ ≤ h + q + 1) :
    0 < (⌊q / 3⌋ : ℝ) ∧
    q ≤ (3 / 2 : ℝ) * (q + 1) - (⌊q / 3⌋ : ℝ) ∧
    Δ < (2 / 9 : ℝ) * ((⌊q / 3⌋ : ℝ) + 1) ^ 2 ∧
    (1 - ζ) * q < q - 2 * Δ / (q + 1) := by
  have hqpos : 0 < q := by linarith
  have hqone : 0 < q + 1 := by linarith
  have hβlo : q / 3 < (⌊q / 3⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hβhi : (⌊q / 3⌋ : ℝ) ≤ q / 3 := Int.floor_le _
  have hβpos : 0 < (⌊q / 3⌋ : ℝ) := by linarith
  refine ⟨hβpos, by linarith, ?_, ?_⟩
  · have hholes := hole_bound hq hh hΔ
    have hq2 : 0 < q ^ 2 := sq_pos_of_pos hqpos
    have hprod : 0 < ((⌊q / 3⌋ : ℝ) + 1 - q / 3) *
        ((⌊q / 3⌋ : ℝ) + 1 + q / 3) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  · have hδpos := delta_pos hζ
    have hδζ : min (ζ / 4) (1 / 100 : ℝ) ≤ ζ / 4 := min_le_left _ _
    have hζq : 4 ≤ ζ * q := (div_le_iff₀ hζ).mp hthreshold |>.trans_eq (mul_comm q ζ)
    have hδq := mul_le_mul_of_nonneg_right hδζ hqpos.le
    have hratio : Δ / (q + 1) < min (ζ / 4) (1 / 100 : ℝ) * q + 1 := by
      apply (div_lt_iff₀ hqone).2
      nlinarith
    rw [mul_div_assoc]
    nlinarith

end Balanced.StabilityArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CorePencilReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

theorem corePencilEvent_of_not_nearCoverFailure
    (hstable : PrimeStability.{u}) (hprime : Nat.Prime (Fintype.card F))
    {ζ : ℝ} (hζ : 0 < ζ)
    (hlarge : max (100 : ℝ) (4 / ζ) ≤ (Fintype.card F : ℝ))
    {D : Finset (Line F)}
    (hnear : ¬ NearCoverFailure (stabilityDensity ζ) D) :
    CorePencilEvent ζ D := by
  intro C hdisj hcard hcover
  apply hstable F hprime ζ hζ hlarge C hcard
  by_contra h
  exact hnear ⟨C, hdisj, hcard, hcover, le_of_not_gt h⟩

theorem corePencilFailure_subset_nearCoverFailure
    (hstable : PrimeStability.{u}) (hprime : Nat.Prime (Fintype.card F))
    {ζ : ℝ} (hζ : 0 < ζ)
    (hlarge : max (100 : ℝ) (4 / ζ) ≤ (Fintype.card F : ℝ)) :
    {D : Finset (Line F) | ¬ CorePencilEvent ζ D} ⊆
      {D | NearCoverFailure (stabilityDensity ζ) D} := by
  intro D hD
  by_contra hnear
  exact hD (corePencilEvent_of_not_nearCoverFailure hstable hprime hζ hlarge hnear)

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CorePencilAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u

namespace CorePencilAssembly

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

theorem eventProbability_mono {k : ℕ} (Q : PMF (DeletionSet F k))
    {E E' : DeletionSet F k → Prop} (h : ∀ D, E D → E' D) :
    deletionEventProbability Q E ≤ deletionEventProbability Q E' := by
  classical
  unfold deletionEventProbability
  apply Finset.sum_le_sum
  intro D _
  by_cases hD : E D
  · simp [hD, h D hD]
  · simp only [ite_eq_right hD]
    split_ifs
    · exact ENNReal.toReal_nonneg
    · exact le_rfl

end CorePencilAssembly

theorem corePencilResult_of_robustDeletion_primeStability
    (hdeletion : RobustDeletionResult.{u}) (hstable : PrimeStability.{u}) :
    CorePencilResult.{u} := by
  intro k hk K hK ζ hζ ε hε
  have hδ : 0 < stabilityDensity ζ := StabilityArithmetic.delta_pos hζ
  obtain ⟨N, hN⟩ := (hdeletion k hk K hK).2.2 (stabilityDensity ζ) hδ ε hε
  obtain ⟨M, hM⟩ := exists_nat_ge (max (100 : ℝ) (4 / ζ))
  refine ⟨max N M, ?_⟩
  intro F _ _ _ hprime hq hkq Q hQ
  have hNq : N ≤ Fintype.card F := (le_max_left N M).trans hq
  have hMq : M ≤ Fintype.card F := (le_max_right N M).trans hq
  have hlarge : max (100 : ℝ) (4 / ζ) ≤ (Fintype.card F : ℝ) :=
    hM.trans (Nat.cast_le.mpr hMq)
  calc
    deletionEventProbability Q (fun D => ¬ CorePencilEvent ζ D.val) ≤
        deletionEventProbability Q (fun D => BadCoreCover (stabilityDensity ζ) D.val) := by
      apply CorePencilAssembly.eventProbability_mono
      intro D hD
      exact corePencilFailure_subset_nearCoverFailure hstable hprime hζ hlarge hD
    _ < ε := hN F hNq hkq Q hQ

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_Projective2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F]

theorem affineDualPoint_injective : Function.Injective (affineDualPoint (F := F)) := by
  intro l m h
  have hh := congrArg dualLine h
  simpa only [affineDualPoint, dualLine_dualPoint, Option.some.injEq] using hh

theorem projective_incident_dual (P : ProjectivePoint F) (l : ProjectiveLine F) :
    ProjectiveIncident P l ↔ ProjectiveIncident (dualPoint l) (dualLine P) := by
  cases P with
  | inl p =>
    rcases p with ⟨x,y⟩
    cases l with
    | none => simp [ProjectiveIncident, dualPoint, dualLine, ThroughProjective]
    | some l =>
      rcases l with ⟨d,b⟩
      cases d with
      | none => simp [ProjectiveIncident, dualPoint, dualLine, ThroughProjective, OnLine, lineEval]
      | some m =>
        simp only [ProjectiveIncident, dualPoint, dualLine, ThroughProjective, OnLine, lineEval]
        constructor <;> intro h <;> linear_combination h
  | inr d =>
    cases d with
    | none =>
      cases l with
      | none => simp [ProjectiveIncident, dualPoint, dualLine]
      | some l =>
        rcases l with ⟨d,b⟩
        cases d <;> simp [ProjectiveIncident, dualPoint, dualLine, ThroughProjective]
    | some m =>
      cases l with
      | none => simp [ProjectiveIncident, dualPoint, dualLine, ThroughProjective]
      | some l =>
        rcases l with ⟨d,b⟩
        cases d <;> simp [ProjectiveIncident, dualPoint, dualLine, ThroughProjective, OnLine, lineEval, eq_comm]

variable [Fintype F] [DecidableEq F]

theorem missedProjective_eq_disjSum (C : Finset (Line F)) :
    missedProjective C = (missedAffine C).disjSum
      (Finset.univ \ representedDirections C) := by
  ext P
  simp only [missedProjective, Finset.mem_filter, Finset.mem_univ, true_and]
  cases P with
  | inl p => simp [missedAffine, ThroughProjective]
  | inr d =>
    simp [representedDirections, ThroughProjective]
    constructor
    · intro h b hb
      exact h d b hb rfl
    · intro h a b hab had
      subst a
      exact h b hab

theorem card_missedProjective (C : Finset (Line F)) :
    (missedProjective C).card = (missedAffine C).card +
      (Fintype.card F + 1 - (representedDirections C).card) := by
  rw [missedProjective_eq_disjSum, Finset.card_disjSum, Finset.card_sdiff]
  simp [Direction]

omit [Fintype F] in
@[simp] theorem card_dualPointSet (C : Finset (Line F)) :
    (dualPointSet C).card = C.card := by
  exact Finset.card_image_of_injective C affineDualPoint_injective

theorem mem_skew_dualLine_iff (C : Finset (Line F)) (P : ProjectivePoint F) :
    dualLine P ∈ skewProjective (dualPointSet C) ↔ P ∈ missedProjective C := by
  simp only [skewProjective, dualPointSet, missedProjective,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.forall_mem_image]
  apply forall_congr'
  intro l
  apply forall_congr'
  intro hl
  exact not_congr (projective_incident_dual P (some l)).symm

theorem card_skew_dualPointSet (C : Finset (Line F)) :
    (skewProjective (dualPointSet C)).card = (missedProjective C).card := by
  symm
  apply Finset.card_equiv projectiveDuality
  intro P
  exact (mem_skew_dualLine_iff C P).symm

theorem card_skew_dualPointSet_exact (C : Finset (Line F)) :
    (skewProjective (dualPointSet C)).card = (missedAffine C).card +
      (Fintype.card F + 1 - (representedDirections C).card) := by
  rw [card_skew_dualPointSet, card_missedProjective]

theorem card_skew_dualPointSet_le (C : Finset (Line F)) :
    (skewProjective (dualPointSet C)).card ≤
      (missedAffine C).card + Fintype.card F + 1 := by
  rw [card_skew_dualPointSet_exact]
  omega

omit [Fintype F] in
theorem card_dualPointSet_on_line (C : Finset (Line F)) (l : ProjectiveLine F) :
    ((dualPointSet C).filter (fun P => ProjectiveIncident P l)).card =
      (C.filter (fun m => ThroughProjective m (dualPoint l))).card := by
  unfold dualPointSet
  rw [Finset.filter_image, Finset.card_image_of_injective _ affineDualPoint_injective]
  congr 1
  ext m
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro hm
  have hd := projective_incident_dual (dualPoint l) (some m)
  simpa only [affineDualPoint, dualLine_dualPoint, ProjectiveIncident] using hd.symm

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_ProjectiveNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace ProjectiveNormalization

open scoped BigOperators

variable {F : Type*} [Field F]

private theorem coordPerm_apply (permutation : Equiv.Perm (Fin 3)) (vector : V F) :
    coordPerm permutation vector = fun index => vector (permutation index) := rfl

theorem pointToInfinity_apply (P : ProjectivePoint F) :
    (pointToInfinity P).point P = Sum.inr none := by
  cases P with
  | inl p =>
    rcases p with ⟨x,y⟩
    simp [pointToInfinity, Collineation.trans, addCoordinate, permuteCoordinates,
      ofLinear, pointEquiv, coordAdd, coordPerm_apply, homogeneousPoint,
      normalizeProjective, Equiv.swap_apply_def]
  | inr d =>
    cases d <;> simp [pointToInfinity, Collineation.refl, Collineation.trans,
      addCoordinate, permuteCoordinates, ofLinear, pointEquiv, coordAdd,
      coordPerm_apply, homogeneousPoint, normalizeProjective, Equiv.swap_apply_def]

theorem verticalToInfinity_point (b : F) :
    (verticalToInfinity b).point (Sum.inr none) = Sum.inr none := by
  simp [verticalToInfinity, Collineation.trans, addCoordinate, permuteCoordinates,
    ofLinear, pointEquiv, coordAdd, coordPerm_apply, homogeneousPoint,
    normalizeProjective, Equiv.swap_apply_def]

theorem verticalToInfinity_line (b : F) :
    (verticalToInfinity b).line (some (none, b)) = none := by
  simp [verticalToInfinity, Collineation.trans, addCoordinate, permuteCoordinates,
    ofLinear, lineEquiv, coordAdd, coordPerm_apply, homogeneousLine,
    normalizeLine, Equiv.swap_apply_def]

theorem exists_flag_normalization (P : ProjectivePoint F) (l : ProjectiveLine F)
    (h : ProjectiveIncident P l) :
    ∃ e : Collineation F, e.point P = Sum.inr none ∧ e.line l = none := by
  let a := pointToInfinity P
  have hp : a.point P = Sum.inr none := pointToInfinity_apply P
  have hi : ProjectiveIncident (Sum.inr none) (a.line l) := by
    rw [← hp]
    exact (a.incident P l).mpr h
  cases hl : a.line l with
  | none => exact ⟨a, hp, hl⟩
  | some L =>
    rcases L with ⟨d,b⟩
    have hd : d = none := by
      simpa only [hl, ProjectiveIncident, ThroughProjective] using hi
    subst d
    refine ⟨a.trans (verticalToInfinity b), ?_, ?_⟩
    · change (verticalToInfinity b).point (a.point P) = _
      rw [hp, verticalToInfinity_point]
    · change (verticalToInfinity b).line (a.line l) = _
      rw [hl, verticalToInfinity_line]

section FiniteSets

variable [Fintype F] [DecidableEq F]

omit [Fintype F] in
theorem card_image (e : Collineation F) (B : Finset (ProjectivePoint F)) :
    (B.image e.point).card = B.card :=
  Finset.card_image_of_injective B e.point.injective

omit [Fintype F] in
theorem image_filter_incident (e : Collineation F) (B : Finset (ProjectivePoint F))
    (l : ProjectiveLine F) :
    (B.image e.point).filter (fun Q => ProjectiveIncident Q (e.line l)) =
      (B.filter (fun P => ProjectiveIncident P l)).image e.point := by
  rw [Finset.filter_image]
  congr 1
  ext P
  simp [e.incident]

omit [Fintype F] in
theorem card_filter_incident (e : Collineation F) (B : Finset (ProjectivePoint F))
    (l : ProjectiveLine F) :
    ((B.image e.point).filter (fun Q => ProjectiveIncident Q (e.line l))).card =
      (B.filter (fun P => ProjectiveIncident P l)).card := by
  rw [image_filter_incident, card_image]

theorem card_skew_image (e : Collineation F) (B : Finset (ProjectivePoint F)) :
    (skewProjective (B.image e.point)).card = (skewProjective B).card := by
  symm
  apply Finset.card_equiv e.line
  intro l
  simp only [skewProjective, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.forall_mem_image, e.incident]

theorem card_tangents_image (e : Collineation F) (B : Finset (ProjectivePoint F))
    (P : ProjectivePoint F) :
    (Finset.univ.filter (fun l : ProjectiveLine F =>
      ProjectiveIncident (e.point P) l ∧
        ((B.image e.point).filter (fun Q => ProjectiveIncident Q l)).card = 1)).card =
    (Finset.univ.filter (fun l : ProjectiveLine F =>
      ProjectiveIncident P l ∧ (B.filter (fun Q => ProjectiveIncident Q l)).card = 1)).card := by
  symm
  apply Finset.card_equiv e.line
  intro l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    e.incident, card_filter_incident]

theorem exists_tangent_normalization (B : Finset (ProjectivePoint F))
    (P : ProjectivePoint F) (l : ProjectiveLine F)
    (h : B.filter (fun Q => ProjectiveIncident Q l) = {P}) :
    ∃ e : Collineation F,
      e.point P = Sum.inr none ∧ e.line l = none ∧
      (B.image e.point).filter (fun Q => ProjectiveIncident Q none) = {Sum.inr none} ∧
      (B.image e.point).card = B.card ∧
      (skewProjective (B.image e.point)).card = (skewProjective B).card := by
  have hi : ProjectiveIncident P l := by
    have hm : P ∈ B.filter (fun Q => ProjectiveIncident Q l) := by rw [h]; simp
    exact (Finset.mem_filter.mp hm).2
  obtain ⟨e, hp, hl⟩ := exists_flag_normalization P l hi
  refine ⟨e, hp, hl, ?_, card_image e B, card_skew_image e B⟩
  rw [← hl, image_filter_incident, h, Finset.image_singleton, hp]

omit [Fintype F] in
theorem eq_affinePart_disjSum (B : Finset (ProjectivePoint F))
    (h : B.filter (fun Q => ProjectiveIncident Q none) = {Sum.inr none}) :
    B = B.toLeft.disjSum {none} := by
  have hr : B.toRight = {none} := by
    ext d
    have hd := Finset.ext_iff.mp h (Sum.inr d)
    simp only [Finset.mem_filter] at hd
    simpa only [Finset.mem_toRight, ProjectiveIncident,
      and_true, Finset.mem_singleton, Sum.inr.injEq] using hd
  rw [← hr, Finset.toLeft_disjSum_toRight]

omit [Fintype F] in
theorem card_affinePart_add_one (B : Finset (ProjectivePoint F))
    (h : B.filter (fun Q => ProjectiveIncident Q none) = {Sum.inr none}) :
    B.toLeft.card + 1 = B.card := by
  conv_rhs => rw [eq_affinePart_disjSum B h]
  simp

theorem card_skew_codes (U : Finset (Point F)) :
    (Finset.univ.filter (fun z : Fin 2 → F =>
      ∀ p ∈ U, ¬ OnLine p (some (z 1), z 0))).card =
    (skewProjective (U.disjSum {none})).card := by
  apply Finset.card_bij (fun z _ => some (some (z 1), z 0))
  · intro z hz
    simp only [skewProjective, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [ProjectiveIncident, ThroughProjective] using hz
  · intro z hz w hw he
    have he' : z 1 = w 1 ∧ z 0 = w 0 := by simpa using he
    ext i
    fin_cases i <;> simp_all
  · intro l hl
    simp only [skewProjective, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    cases l with
    | none => simp [ProjectiveIncident] at hl
    | some l =>
      rcases l with ⟨d,b⟩
      cases d with
      | none => simp [ProjectiveIncident, ThroughProjective] at hl
      | some m =>
        refine ⟨![b,m], ?_, by simp⟩
        simpa [ProjectiveIncident, ThroughProjective] using hl

theorem exists_normalized_affine_set (B : Finset (ProjectivePoint F))
    (P : ProjectivePoint F) (l : ProjectiveLine F)
    (h : B.filter (fun Q => ProjectiveIncident Q l) = {P}) :
    ∃ (e : Collineation F) (U : Finset (Point F)),
      e.point P = Sum.inr none ∧ e.line l = none ∧
      B.image e.point = U.disjSum {none} ∧
      U.card + 1 = B.card ∧
      (Finset.univ.filter (fun z : Fin 2 → F =>
        ∀ p ∈ U, ¬ OnLine p (some (z 1), z 0))).card = (skewProjective B).card := by
  obtain ⟨e, hp, hl, hi, hc, hs⟩ := exists_tangent_normalization B P l h
  refine ⟨e, (B.image e.point).toLeft, hp, hl,
    eq_affinePart_disjSum _ hi, ?_, ?_⟩
  · rw [card_affinePart_add_one _ hi, hc]
  · rw [card_skew_codes, ← eq_affinePart_disjSum _ hi, hs]

omit [Fintype F] in
theorem card_normalized_vertical_section (U : Finset (Point F)) (c : F) :
    ((U.disjSum {none}).filter (fun P => ProjectiveIncident P (some (none,c)))).card =
      (U.filter (fun p => p.1 = c)).card + 1 := by
  have h : (U.disjSum {none}).filter (fun P => ProjectiveIncident P (some (none,c))) =
      (U.filter (fun p => p.1 = c)).disjSum {none} := by
    ext P
    simp only [Finset.mem_filter]
    cases P <;> simp [ProjectiveIncident, ThroughProjective, OnLine, lineEval, eq_comm]
  rw [h, Finset.card_disjSum]
  simp

omit [Fintype F] in
theorem card_normalized_infinity_section (U : Finset (Point F)) :
    ((U.disjSum {none}).filter (fun P => ProjectiveIncident P none)).card = 1 := by
  have h : (U.disjSum {none}).filter (fun P => ProjectiveIncident P none) =
      {Sum.inr (none : Direction F)} := by
    ext P
    simp only [Finset.mem_filter]
    cases P <;> simp [ProjectiveIncident]
  rw [h, Finset.card_singleton]

theorem card_normalized_tangents (U : Finset (Point F)) :
    (Finset.univ.filter (fun l : ProjectiveLine F =>
      ProjectiveIncident (Sum.inr none) l ∧
        ((U.disjSum {none}).filter (fun P => ProjectiveIncident P l)).card = 1)).card =
      (Finset.univ.filter (fun c : F => ∀ p ∈ U, p.1 ≠ c)).card + 1 := by
  have h : Finset.univ.filter (fun l : ProjectiveLine F =>
      ProjectiveIncident (Sum.inr none) l ∧
        ((U.disjSum {none}).filter (fun P => ProjectiveIncident P l)).card = 1) =
      insert none ((Finset.univ.filter (fun c : F => ∀ p ∈ U, p.1 ≠ c)).image
        (fun c => some (none,c))) := by
    ext l
    cases l with
    | none =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [card_normalized_infinity_section]
      simp [ProjectiveIncident]
    | some l =>
      rcases l with ⟨d,c⟩
      cases d with
      | none =>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [card_normalized_vertical_section]
        simp [ProjectiveIncident, ThroughProjective,
          Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      | some m =>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simp [ProjectiveIncident, ThroughProjective]
  rw [h, Finset.card_insert_of_notMem (by simp)]
  rw [Finset.card_image_of_injective _ (by
    intro c d hcd
    simpa using hcd)]

theorem exists_normalized_affine_set_with_tangents (B : Finset (ProjectivePoint F))
    (P : ProjectivePoint F) (l : ProjectiveLine F)
    (h : B.filter (fun Q => ProjectiveIncident Q l) = {P}) :
    ∃ (e : Collineation F) (U : Finset (Point F)),
      e.point P = Sum.inr none ∧ e.line l = none ∧
      B.image e.point = U.disjSum {none} ∧ U.card + 1 = B.card ∧
      (Finset.univ.filter (fun z : Fin 2 → F =>
        ∀ p ∈ U, ¬ OnLine p (some (z 1), z 0))).card = (skewProjective B).card ∧
      (Finset.univ.filter (fun L : ProjectiveLine F =>
        ProjectiveIncident P L ∧ (B.filter (fun Q => ProjectiveIncident Q L)).card = 1)).card =
        (Finset.univ.filter (fun c : F => ∀ p ∈ U, p.1 ≠ c)).card + 1 := by
  obtain ⟨e, U, hp, hl, hU, hc, hs⟩ := exists_normalized_affine_set B P l h
  refine ⟨e, U, hp, hl, hU, hc, hs, ?_⟩
  rw [← card_tangents_image e B P, hp, hU, card_normalized_tangents]

end FiniteSets

end ProjectiveNormalization
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_SmallProjectiveArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.SmallProjectiveArithmetic

theorem exists_interpolation_degree (δ : ℕ) (hδ : 0 < δ) :
    ∃ d : ℕ, d ^ 2 < 2 * δ ∧ 2 * δ < (d + 1) * (d + 2) := by
  let d := Nat.sqrt (2 * δ - 1)
  have hs : d ^ 2 ≤ 2 * δ - 1 := Nat.sqrt_le' _
  have ht : 2 * δ - 1 < (d + 1) * (d + 1) := Nat.lt_succ_sqrt _
  have hpred : 2 * δ - 1 + 1 = 2 * δ := by omega
  refine ⟨d, by omega, ?_⟩
  nlinarith

theorem three_degree_lt_order {q δ d : ℕ}
    (hsmall : (δ : ℝ) < (201 / 10000 : ℝ) * (q : ℝ) ^ 2)
    (hd : d ^ 2 < 2 * δ) : 3 * d < q := by
  have hdR : (d : ℝ) ^ 2 < 2 * (δ : ℝ) := by exact_mod_cast hd
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hs : (3 * (d : ℝ)) ^ 2 < (q : ℝ) ^ 2 := by nlinarith [sq_nonneg (q : ℝ)]
  have hlin : 3 * (d : ℝ) < q := by nlinarith
  exact_mod_cast hlin

theorem half_line_of_degree_bound {q d on : ℕ}
    (hd : 3 * d < q) (hon : q - d ≤ on) :
    q + 1 ≤ 2 * on := by
  omega

theorem half_line_skew_refinement (q on off missing δ : ℕ)
    (hline : on + missing = q + 1)
    (hsize : off + on ≤ q)
    (hhalf : q + 1 ≤ 2 * on)
    (hcount : missing * (q - off) ≤ δ) :
    (q : ℝ) + 1 - 2 * (δ : ℝ) / ((q : ℝ) + 1) ≤ on := by
  have hon : on ≤ q - off := by omega
  have hcount' : missing * on ≤ δ := (Nat.mul_le_mul_left missing hon).trans hcount
  have hlineR : (on : ℝ) + missing = (q : ℝ) + 1 := by exact_mod_cast hline
  have hhalfR : (q : ℝ) + 1 ≤ 2 * (on : ℝ) := by exact_mod_cast hhalf
  have hcountR : (missing : ℝ) * on ≤ δ := by exact_mod_cast hcount'
  have hnonneg : (0 : ℝ) ≤ missing := Nat.cast_nonneg _
  have hpay : ((q : ℝ) + 1 - on) * ((q : ℝ) + 1) ≤ 2 * δ := by
    nlinarith
  have hq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hdiv : (q : ℝ) + 1 - on ≤ 2 * (δ : ℝ) / ((q : ℝ) + 1) :=
    (le_div_iff₀ hq).mpr hpay
  linarith

end Balanced.SmallProjectiveArithmetic

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_SmallProjectiveStabilityReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u

theorem primeStability_of_smallProjective
    (hprojective : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      Nat.Prime (Fintype.card F) → 100 ≤ Fintype.card F →
      ∀ B : Finset (ProjectivePoint F), B.card ≤ Fintype.card F →
        ((skewProjective B).card : ℝ) <
          (201 / 10000 : ℝ) * (Fintype.card F : ℝ) ^ 2 →
        ∃ l : ProjectiveLine F,
          (Fintype.card F : ℝ) - 2 * (skewProjective B).card /
            ((Fintype.card F : ℝ) + 1) ≤
              ((B.filter (fun P => ProjectiveIncident P l)).card : ℝ)) :
    PrimeStability.{u} := by
  intro F _ _ _ hprime ζ hζ hlarge C hcard hmiss
  have hq : (100 : ℝ) ≤ (Fintype.card F : ℝ) :=
    (le_max_left _ _).trans hlarge
  have hthreshold : 4 / ζ ≤ (Fintype.card F : ℝ) :=
    (le_max_right _ _).trans hlarge
  have hholes : ((skewProjective (dualPointSet C)).card : ℝ) ≤
      ((uncoveredPoints C).card : ℝ) + (Fintype.card F : ℝ) + 1 := by
    exact_mod_cast card_skew_dualPointSet_le C
  have hsmall := StabilityArithmetic.hole_bound hq hmiss hholes
  have hBcard : (dualPointSet C).card ≤ Fintype.card F := by
    simpa only [card_dualPointSet] using hcard
  obtain ⟨l, hl⟩ := hprojective F hprime (by exact_mod_cast hq)
    (dualPointSet C) hBcard hsmall
  have hconclusion :=
    (StabilityArithmetic.reduction_bounds hq hζ hthreshold hmiss hholes).2.2.2
  refine ⟨dualPoint l, ?_⟩
  simpa only [card_dualPointSet_on_line, pencilSize] using hconclusion.le.trans hl

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_StabilityPolynomial2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.StabilityPolynomial

open MvPolynomial

variable {F σ : Type*} [Field F]

theorem exists_nonzero_vanishing_with_support
    (M : Finset (σ →₀ ℕ)) (S : Finset (σ → F)) (hcard : S.card < M.card) :
    ∃ p : MvPolynomial σ F, p ≠ 0 ∧ p.support ⊆ M ∧
      ∀ x ∈ S, eval x p = 0 := by
  classical
  let V := restrictSupport F (M : Set (σ →₀ ℕ))
  let b : Module.Basis M F V := basisRestrictSupport F (M : Set (σ →₀ ℕ))
  let : Module.Finite F V := Module.Finite.of_basis b
  let E : V →ₗ[F] (S → F) :=
    { toFun := fun p x => eval x.val p.val
      map_add' := by intro p q; ext x; simp
      map_smul' := by intro a p; ext x; simp }
  have hdim : Module.finrank F (S → F) < Module.finrank F V := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_basis b]
    simpa using hcard
  obtain ⟨p, hp, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := E) hdim)
  refine ⟨p.val, ?_, p.property, ?_⟩
  · intro hz
    exact hne (Subtype.ext hz)
  · intro x hx
    exact congrFun (LinearMap.mem_ker.mp hp) ⟨x, hx⟩

theorem exists_nonzero_vanishing_degree_le
    (M : Finset (σ →₀ ℕ)) (S : Finset (σ → F)) (d : ℕ)
    (hcard : S.card < M.card)
    (hdegree : ∀ m ∈ M, m.sum (fun _ n => n) ≤ d) :
    ∃ p : MvPolynomial σ F, p ≠ 0 ∧ p.totalDegree ≤ d ∧
      ∀ x ∈ S, eval x p = 0 := by
  obtain ⟨p, hp, hs, hv⟩ := exists_nonzero_vanishing_with_support M S hcard
  refine ⟨p, hp, ?_, hv⟩
  apply (mem_restrictTotalDegree σ d p).mp
  intro m hm
  exact hdegree m (hs hm)

lemma pairExponent_injective : Function.Injective pairExponent := by
  intro a b h
  have h0 := congrArg (fun m : Fin 2 →₀ ℕ => m 0) h
  have h1 := congrArg (fun m : Fin 2 →₀ ℕ => m 1) h
  simp only [pairExponent, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide),
    Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide), add_zero, zero_add] at h0 h1
  exact Prod.ext h0 h1

lemma sum_pairExponent (a : ℕ × ℕ) :
    (pairExponent a).sum (fun _ n => n) = a.1 + a.2 := by
  simp [pairExponent, Finsupp.sum_add_index']

lemma mem_trianglePairs (d : ℕ) (a : ℕ × ℕ) :
    a ∈ trianglePairs d ↔ a.1 + a.2 ≤ d := by
  simp only [trianglePairs, Finset.mem_biUnion, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal]
  constructor
  · rintro ⟨k, hk, he⟩
    omega
  · intro h
    exact ⟨a.1 + a.2, by omega, rfl⟩

lemma twice_card_trianglePairs (d : ℕ) :
    2 * (trianglePairs d).card = (d + 1) * (d + 2) := by
  have hdis : (↑(Finset.range (d + 1)) : Set ℕ).PairwiseDisjoint
      Finset.HasAntidiagonal.antidiagonal := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro a hai haj
    exact hij ((Finset.HasAntidiagonal.mem_antidiagonal.mp hai).symm.trans (Finset.HasAntidiagonal.mem_antidiagonal.mp haj))
  rw [trianglePairs, Finset.card_biUnion hdis]
  simp only [Finset.Nat.card_antidiagonal, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul, mul_one]
  have hsum := Finset.sum_range_id_mul_two (d + 1)
  simp only [Nat.add_sub_cancel] at hsum
  nlinarith

theorem exists_bivariate_vanishing
    (S : Finset (Fin 2 → F)) (d : ℕ)
    (hsize : 2 * S.card < (d + 1) * (d + 2)) :
    ∃ p : MvPolynomial (Fin 2) F, p ≠ 0 ∧ p.totalDegree ≤ d ∧
      ∀ x ∈ S, eval x p = 0 := by
  classical
  let M := (trianglePairs d).image pairExponent
  apply exists_nonzero_vanishing_degree_le M S d
  · have hc : M.card = (trianglePairs d).card :=
      Finset.card_image_of_injective _ pairExponent_injective
    have ht := twice_card_trianglePairs d
    omega
  · intro m hm
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hm
    rw [sum_pairExponent]
    exact (mem_trianglePairs d a).mp ha

end Balanced.StabilityPolynomial

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_FiniteGridVanishing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.StabilityPolynomial

open scoped BigOperators

variable {K : Type*} [Field K] [Fintype K]

open Polynomial in

theorem field_polynomial_prod :
    (∏ a : K, (Polynomial.X - Polynomial.C a)) =
      (Polynomial.X : K[X]) ^ Fintype.card K - Polynomial.X := by
  classical
  have hm : (Polynomial.X ^ Fintype.card K - Polynomial.X : K[X]).Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [Polynomial.degree_X]
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card K)
  have hr : (Polynomial.X ^ Fintype.card K - Polynomial.X : K[X]).roots.card =
      (Polynomial.X ^ Fintype.card K - Polynomial.X : K[X]).natDegree := by
    rw [FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card]
    exact Finset.card_univ
  have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hr
  rw [FiniteField.roots_X_pow_card_sub_X] at h
  exact h

open MvPolynomial

theorem field_coordinate_prod {σ : Type*} (i : σ) :
    (∏ a : K, (X i - C a)) = (X i : MvPolynomial σ K) ^ Fintype.card K - X i := by
  classical
  have h := congrArg (Polynomial.eval₂RingHom (C : K →+* MvPolynomial σ K) (X i))
    (field_polynomial_prod (K := K))
  simpa using h

theorem field_coordinate_totalDegree {σ : Type*} (i : σ) :
    ((X i : MvPolynomial σ K) ^ Fintype.card K - X i).totalDegree =
      Fintype.card K := by
  rw [sub_eq_add_neg,
    totalDegree_add_eq_left_of_totalDegree_lt (show
      (- (X i : MvPolynomial σ K)).totalDegree <
        ((X i : MvPolynomial σ K) ^ Fintype.card K).totalDegree by
          simpa using (Fintype.one_lt_card : 1 < Fintype.card K))]
  exact totalDegree_X_pow _ _

theorem field_coordinate_ne_zero {σ : Type*} (i : σ) :
    (X i : MvPolynomial σ K) ^ Fintype.card K - X i ≠ 0 := by
  intro h
  have hdeg := congrArg totalDegree h
  rw [field_coordinate_totalDegree, totalDegree_zero] at hdeg
  exact Fintype.card_ne_zero hdeg

theorem finite_grid_decomposition {σ : Type*} [Fintype σ]
    (H : MvPolynomial σ K) (hH : ∀ x : σ → K, eval x H = 0) :
    ∃ G : σ → MvPolynomial σ K,
      (∀ i, (((X i) ^ Fintype.card K - X i) * G i).totalDegree ≤ H.totalDegree) ∧
      H = ∑ i, ((X i) ^ Fintype.card K - X i) * G i := by
  classical
  obtain ⟨G, hdeg, heq⟩ := combinatorial_nullstellensatz_exists_linearCombination
    (fun _ : σ => Finset.univ) (fun _ => Finset.univ_nonempty)
    H (fun x _ => hH x)
  refine ⟨G, ?_, ?_⟩
  · intro i
    simpa only [field_coordinate_prod] using hdeg i
  · rw [heq, Finsupp.linearCombination_apply]
    rw [Finsupp.sum_fintype G (fun i a => a • ∏ r : K, (X i - C r))
      (fun _ => zero_smul _ _)]
    simp only [smul_eq_mul, field_coordinate_prod, mul_comm]

theorem finite_grid_decomposition_degree {σ : Type*} [Fintype σ]
    (H : MvPolynomial σ K) (hH : ∀ x : σ → K, eval x H = 0) :
    ∃ G : σ → MvPolynomial σ K,
      (∀ i, (G i).totalDegree ≤ H.totalDegree - Fintype.card K) ∧
      H = ∑ i, ((X i) ^ Fintype.card K - X i) * G i := by
  obtain ⟨G, hdeg, heq⟩ := finite_grid_decomposition H hH
  refine ⟨G, ?_, heq⟩
  intro i
  by_cases hGi : G i = 0
  · simp [hGi]
  · have hd := hdeg i
    rw [totalDegree_mul_of_isDomain (field_coordinate_ne_zero i) hGi,
      field_coordinate_totalDegree] at hd
    omega

theorem bivariate_grid_decomposition_degree
    (H : MvPolynomial (Fin 2) K)
    (hH : ∀ x : Fin 2 → K, eval x H = 0) :
    ∃ f g : MvPolynomial (Fin 2) K,
      f.totalDegree ≤ H.totalDegree - Fintype.card K ∧
      g.totalDegree ≤ H.totalDegree - Fintype.card K ∧
      H = ((X 0) ^ Fintype.card K - X 0) * f +
        ((X 1) ^ Fintype.card K - X 1) * g := by
  obtain ⟨G, hdeg, heq⟩ := finite_grid_decomposition_degree H hH
  exact ⟨G 0, G 1, hdeg 0, hdeg 1, by simpa only [Fin.sum_univ_two] using heq⟩

end Balanced.StabilityPolynomial

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_RedeiPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.StabilityPolynomial

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F]

theorem eval_redeiFactor_eq_zero_iff (p : Point F) (z : Fin 2 → F) :
    eval z (redeiFactor p) = 0 ↔ OnLine p (some (z 1), z 0) := by
  simp only [redeiFactor, map_sub, map_add, map_mul, eval_X, eval_C,
    OnLine, lineEval]
  constructor <;> intro h <;> linear_combination -h

theorem redeiFactor_ne_zero (p : Point F) : redeiFactor p ≠ 0 := by
  intro h
  have he := congrArg (eval ![p.2 + 1, 0]) h
  simp [redeiFactor] at he

theorem redeiPolynomial_ne_zero (U : Finset (Point F)) : redeiPolynomial U ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun p _ => redeiFactor_ne_zero p)

theorem redeiFactor_totalDegree_le (p : Point F) : (redeiFactor p).totalDegree ≤ 1 := by
  have hmul : (C p.1 * (X 1 : MvPolynomial (Fin 2) F)).totalDegree ≤ 1 := by
    exact (totalDegree_mul _ _).trans (by simp)
  exact (totalDegree_sub_C_le _ _).trans
    ((totalDegree_add _ _).trans (max_le (by simp) hmul))

theorem redeiFactor_coeff_X (p : Point F) :
    (redeiFactor p).coeff (Finsupp.single 0 1) = 1 := by
  have hzero : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 1 := by
    intro h
    have hz := congrArg (fun m : Fin 2 →₀ ℕ => m 0) h
    simp at hz
  simp [redeiFactor, coeff_X, coeff_C_mul, coeff_C, Finsupp.single_eq_single_iff, hzero]

theorem redeiFactor_totalDegree (p : Point F) : (redeiFactor p).totalDegree = 1 := by
  apply Nat.le_antisymm (redeiFactor_totalDegree_le p)
  have hm : Finsupp.single (0 : Fin 2) 1 ∈ (redeiFactor p).support := by
    rw [mem_support_iff, redeiFactor_coeff_X]
    exact one_ne_zero
  simpa using le_totalDegree hm

theorem redeiPolynomial_totalDegree (U : Finset (Point F)) :
    (redeiPolynomial U).totalDegree = U.card := by
  classical
  induction U using Finset.induction_on with
  | empty => simp [redeiPolynomial]
  | @insert p U hp ih =>
    rw [redeiPolynomial, Finset.prod_insert hp]
    change (redeiFactor p * redeiPolynomial U).totalDegree = (insert p U).card
    rw [totalDegree_mul_of_isDomain (redeiFactor_ne_zero p) (redeiPolynomial_ne_zero U),
      redeiFactor_totalDegree]
    rw [ih, Finset.card_insert_of_notMem hp]
    omega

theorem redeiPolynomial_totalDegree_le (U : Finset (Point F)) :
    (redeiPolynomial U).totalDegree ≤ U.card := by
  classical
  calc
    (redeiPolynomial U).totalDegree ≤ ∑ p ∈ U, (redeiFactor p).totalDegree :=
      totalDegree_finsetProd _ _
    _ ≤ ∑ _p ∈ U, 1 := Finset.sum_le_sum fun p _ => redeiFactor_totalDegree_le p
    _ = U.card := by simp

theorem redei_mul_vanishes
    (U : Finset (Point F)) (a : MvPolynomial (Fin 2) F)
    (ha : ∀ z : Fin 2 → F,
      (∀ p ∈ U, ¬ OnLine p (some (z 1), z 0)) → eval z a = 0) :
    ∀ z : Fin 2 → F, eval z (redeiPolynomial U * a) = 0 := by
  classical
  intro z
  by_cases h : ∃ p ∈ U, OnLine p (some (z 1), z 0)
  · obtain ⟨p, hp, hon⟩ := h
    rw [map_mul]
    have hz : eval z (redeiPolynomial U) = 0 := by
      rw [redeiPolynomial, map_prod]
      exact Finset.prod_eq_zero hp ((eval_redeiFactor_eq_zero_iff p z).mpr hon)
    rw [hz, zero_mul]
  · rw [map_mul, ha z (by simpa only [not_exists, not_and] using h), mul_zero]

theorem redei_mul_totalDegree_le
    (U : Finset (Point F)) (a : MvPolynomial (Fin 2) F) :
    (redeiPolynomial U * a).totalDegree ≤ U.card + a.totalDegree :=
  (totalDegree_mul _ _).trans (Nat.add_le_add_right (redeiPolynomial_totalDegree_le U) _)

theorem redei_mul_totalDegree
    (U : Finset (Point F)) (a : MvPolynomial (Fin 2) F) (ha : a ≠ 0) :
    (redeiPolynomial U * a).totalDegree = U.card + a.totalDegree := by
  rw [totalDegree_mul_of_isDomain (redeiPolynomial_ne_zero U) ha,
    redeiPolynomial_totalDegree]

variable [Fintype F]

theorem mem_nonverticalSkewCodes (U : Finset (Point F)) (z : Fin 2 → F) :
    z ∈ nonverticalSkewCodes U ↔ ∀ p ∈ U, ¬ OnLine p (some (z 1), z 0) := by
  classical
  simp only [nonverticalSkewCodes, Finset.mem_filter, Finset.mem_univ, true_and]

theorem exists_redei_auxiliary (U : Finset (Point F)) (d : ℕ)
    (hsize : 2 * (nonverticalSkewCodes U).card < (d + 1) * (d + 2)) :
    ∃ a : MvPolynomial (Fin 2) F, a ≠ 0 ∧ a.totalDegree ≤ d ∧
      ∀ z : Fin 2 → F,
        (∀ p ∈ U, ¬ OnLine p (some (z 1), z 0)) → eval z a = 0 := by
  obtain ⟨a, hne, hdeg, hvan⟩ := exists_bivariate_vanishing (nonverticalSkewCodes U) d hsize
  exact ⟨a, hne, hdeg, fun z hz => hvan z ((mem_nonverticalSkewCodes U z).mpr hz)⟩

theorem redei_mul_decomposition
    (U : Finset (Point F)) (a : MvPolynomial (Fin 2) F)
    (ha : ∀ z : Fin 2 → F,
      (∀ p ∈ U, ¬ OnLine p (some (z 1), z 0)) → eval z a = 0) :
    ∃ f g : MvPolynomial (Fin 2) F,
      f.totalDegree ≤ U.card + a.totalDegree - Fintype.card F ∧
      g.totalDegree ≤ U.card + a.totalDegree - Fintype.card F ∧
      redeiPolynomial U * a = ((X 0) ^ Fintype.card F - X 0) * f +
        ((X 1) ^ Fintype.card F - X 1) * g := by
  obtain ⟨f, g, hf, hg, heq⟩ := bivariate_grid_decomposition_degree
    (redeiPolynomial U * a) (redei_mul_vanishes U a ha)
  have hdeg := Nat.sub_le_sub_right (redei_mul_totalDegree_le U a) (Fintype.card F)
  exact ⟨f, g, hf.trans hdeg, hg.trans hdeg, heq⟩

end Balanced.StabilityPolynomial

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_StabilityLeadingPart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.StabilityPolynomial

open MvPolynomial
open scoped BigOperators

variable {F σ : Type*} [Field F]

theorem homogeneousComponent_mul_of_degree_le
    (p r : MvPolynomial σ F) (m n : ℕ)
    (hp : p.totalDegree ≤ m) (hr : r.totalDegree ≤ n) :
    homogeneousComponent (m + n) (p * r) =
      homogeneousComponent m p * homogeneousComponent n r := by
  classical
  ext d
  rw [coeff_homogeneousComponent, coeff_mul, coeff_mul]
  by_cases hd : d.degree = m + n
  · rw [ite_eq_left hd]
    apply Finset.sum_congr rfl
    intro x hx
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
    by_cases hpx : p.coeff x.1 = 0
    · simp [hpx]
    by_cases hrx : r.coeff x.2 = 0
    · simp [hrx]
    have hpm : x.1.degree ≤ m :=
      (le_totalDegree (mem_support_iff.mpr hpx)).trans hp
    have hrn : x.2.degree ≤ n :=
      (le_totalDegree (mem_support_iff.mpr hrx)).trans hr
    have hsum : x.1.degree + x.2.degree = m + n := by
      rw [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hx, hd]
    have hm : x.1.degree = m := by omega
    have hn : x.2.degree = n := by omega
    simp [hm, hn]
  · rw [ite_eq_right hd]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
    have hsum : x.1.degree + x.2.degree = d.degree := by
      rw [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hx]
    by_cases hm : x.1.degree = m
    · have hn : x.2.degree ≠ n := by omega
      simp [hn]
    · simp [hm]

theorem topHomogeneousComponent_ne_zero (p : MvPolynomial σ F) (hp : p ≠ 0) :
    homogeneousComponent p.totalDegree p ≠ 0 := by
  classical
  have hs : p.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (mt support_eq_empty.mp hp)
  obtain ⟨d, hd, heq⟩ := p.support.exists_mem_eq_sup hs Finsupp.degree
  have hdeg : d.degree = p.totalDegree := heq.symm
  intro hz
  have hc := congrArg (fun polynomial : MvPolynomial σ F => polynomial.coeff d) hz
  rw [coeff_homogeneousComponent, ite_eq_left hdeg, MvPolynomial.coeff_zero] at hc
  exact (mem_support_iff.mp hd) hc

theorem dehomogenize_ne_zero_of_homogeneous
    {p : MvPolynomial (Fin 2) F} {n : ℕ}
    (hhom : p.IsHomogeneous n) (hp : p ≠ 0) :
    dehomogenize p ≠ 0 := by
  intro hz
  have h := Polynomial.homogenize_eq_of_isHomogeneous hhom hz
  rw [Polynomial.homogenize_zero] at h
  exact hp h.symm

theorem natDegree_dehomogenize_le (p : MvPolynomial (Fin 2) F) :
    (dehomogenize p).natDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [← p.support_sum_monomial_coeff, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  have hbound := le_totalDegree (p := p) hd
  have hmono : dehomogenize (monomial d (p.coeff d)) =
      Polynomial.C (p.coeff d) * Polynomial.X ^ d 0 := by
    simp [dehomogenize, aeval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two]
  rw [hmono]
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  rw [Polynomial.natDegree_X_pow]
  have hsum : d.sum (fun _ e => e) = d 0 + d 1 := by
    rw [Finsupp.sum_fintype]
    · simp [Fin.sum_univ_two]
    · simp
  rw [hsum] at hbound
  omega

theorem natDegree_leadingSpecialization_le (n : ℕ) (p : MvPolynomial (Fin 2) F) :
    (leadingSpecialization n p).natDegree ≤ n :=
  (natDegree_dehomogenize_le _).trans (homogeneousComponent_isHomogeneous n p).totalDegree_le

theorem leadingSpecialization_ne_zero (p : MvPolynomial (Fin 2) F) (hp : p ≠ 0) :
    leadingSpecialization p.totalDegree p ≠ 0 :=
  dehomogenize_ne_zero_of_homogeneous (homogeneousComponent_isHomogeneous _ _)
    (topHomogeneousComponent_ne_zero p hp)

theorem leadingSpecialization_mul_of_degree_le
    (p r : MvPolynomial (Fin 2) F) (m n : ℕ)
    (hp : p.totalDegree ≤ m) (hr : r.totalDegree ≤ n) :
    leadingSpecialization (m + n) (p * r) =
      leadingSpecialization m p * leadingSpecialization n r := by
  simp only [leadingSpecialization,
    homogeneousComponent_mul_of_degree_le p r m n hp hr, map_mul]

theorem leadingSpecialization_redeiFactor (p : Point F) :
    leadingSpecialization 1 (redeiFactor p) = Polynomial.X + Polynomial.C p.1 := by
  have hhom : (X (R := F) 0 + C p.1 * X 1 : MvPolynomial (Fin 2) F).IsHomogeneous 1 :=
    (isHomogeneous_X F 0).add (isHomogeneous_C_mul_X p.1 1)
  simp only [leadingSpecialization, redeiFactor, map_sub,
    homogeneousComponent_eq_self hhom,
    homogeneousComponent_of_mem (isHomogeneous_C (Fin 2) p.2)]
  simp [dehomogenize]

theorem leadingSpecialization_redeiPolynomial (U : Finset (Point F)) :
    leadingSpecialization U.card (redeiPolynomial U) = redeiLeadingProduct U := by
  classical
  induction U using Finset.induction_on with
  | empty => simp [leadingSpecialization, redeiPolynomial, redeiLeadingProduct, dehomogenize]
  | @insert p U hp ih =>
    rw [redeiPolynomial, Finset.prod_insert hp]
    change leadingSpecialization (insert p U).card (redeiFactor p * redeiPolynomial U) = _
    rw [Finset.card_insert_of_notMem hp, Nat.add_comm U.card 1,
      leadingSpecialization_mul_of_degree_le _ _ 1 U.card
        (redeiFactor_totalDegree_le p) (redeiPolynomial_totalDegree_le U),
      leadingSpecialization_redeiFactor, ih]
    simp [redeiLeadingProduct, hp]

theorem homogeneousComponent_grid_term (i : Fin 2) (q s : ℕ) (hq : 1 < q)
    (f : MvPolynomial (Fin 2) F) (hf : f.totalDegree ≤ s) :
    homogeneousComponent (q + s) ((X i ^ q - X i) * f) =
      X i ^ q * homogeneousComponent s f := by
  rw [sub_mul, map_sub,
    homogeneousComponent_mul_of_degree_le _ _ q s (by simp) hf,
    homogeneousComponent_eq_self (isHomogeneous_X_pow i q)]
  have hlow : (X i * f).totalDegree < q + s := by
    apply (totalDegree_mul _ _).trans_lt
    simp only [totalDegree_X]
    omega
  rw [homogeneousComponent_eq_zero _ _ hlow, sub_zero]

theorem leadingSpecialization_grid_term (i : Fin 2) (q s : ℕ) (hq : 1 < q)
    (f : MvPolynomial (Fin 2) F) (hf : f.totalDegree ≤ s) :
    leadingSpecialization (q + s) ((X i ^ q - X i) * f) =
      (dehomogenize (X i)) ^ q * leadingSpecialization s f := by
  simp only [leadingSpecialization, homogeneousComponent_grid_term i q s hq f hf,
    map_mul, map_pow]

theorem redei_leading_identity
    (U : Finset (Point F)) (a f g : MvPolynomial (Fin 2) F) (q : ℕ)
    (hq : 1 < q) (hn : q ≤ U.card + a.totalDegree)
    (hf : f.totalDegree ≤ U.card + a.totalDegree - q)
    (hg : g.totalDegree ≤ U.card + a.totalDegree - q)
    (hid : redeiPolynomial U * a = (X 0 ^ q - X 0) * f + (X 1 ^ q - X 1) * g) :
    redeiLeadingProduct U * leadingSpecialization a.totalDegree a =
      Polynomial.X ^ q * leadingSpecialization (U.card + a.totalDegree - q) f +
        leadingSpecialization (U.card + a.totalDegree - q) g := by
  have hsum : q + (U.card + a.totalDegree - q) = U.card + a.totalDegree :=
    Nat.add_sub_of_le hn
  have h := congrArg (leadingSpecialization (U.card + a.totalDegree)) hid
  rw [leadingSpecialization_mul_of_degree_le _ _ U.card a.totalDegree
    (redeiPolynomial_totalDegree_le U) le_rfl, leadingSpecialization_redeiPolynomial] at h
  have hadd (p r : MvPolynomial (Fin 2) F) (n : ℕ) :
      leadingSpecialization n (p + r) = leadingSpecialization n p + leadingSpecialization n r := by
    simp only [leadingSpecialization, map_add]
  rw [hadd, ← hsum, leadingSpecialization_grid_term 0 q _ hq f hf,
    leadingSpecialization_grid_term 1 q _ hq g hg] at h
  simpa [dehomogenize] using h

variable [Fintype F]

theorem card_le_totalDegree_of_grid_vanishing {τ : Type*} [Finite τ]
    (p : MvPolynomial τ F) (hp : p ≠ 0)
    (hvan : ∀ x : τ → F, eval x p = 0) :
    Fintype.card F ≤ p.totalDegree := by
  classical
  by_contra hn
  have hlt : p.totalDegree < Fintype.card F := Nat.lt_of_not_ge hn
  apply hp
  apply eq_zero_of_eval_zero_at_prod_finset p (fun _ => Finset.univ)
  · intro i
    simpa only [Finset.card_univ] using (degreeOf_le_totalDegree p i).trans_lt hlt
  · intro x _
    exact hvan x

theorem card_le_redei_auxiliary_degree
    (U : Finset (Point F)) (a : MvPolynomial (Fin 2) F) (ha : a ≠ 0)
    (hvan : ∀ z : Fin 2 → F,
      (∀ p ∈ U, ¬ OnLine p (some (z 1), z 0)) → eval z a = 0) :
    Fintype.card F ≤ U.card + a.totalDegree := by
  have h := card_le_totalDegree_of_grid_vanishing (redeiPolynomial U * a)
    (mul_ne_zero (redeiPolynomial_ne_zero U) ha) (redei_mul_vanishes U a hvan)
  rwa [redei_mul_totalDegree U a ha] at h

theorem exists_redei_leading_identity (U : Finset (Point F)) (d : ℕ)
    (hsize : 2 * (nonverticalSkewCodes U).card < (d + 1) * (d + 2)) :
    ∃ A f g : Polynomial F,
      A ≠ 0 ∧ A.natDegree ≤ d ∧
      f.natDegree ≤ U.card + d - Fintype.card F ∧
      g.natDegree ≤ U.card + d - Fintype.card F ∧
      redeiLeadingProduct U * A = Polynomial.X ^ Fintype.card F * f + g := by
  obtain ⟨a, ha, had, hvan⟩ := exists_redei_auxiliary U d hsize
  obtain ⟨f, g, hf, hg, hid⟩ := redei_mul_decomposition U a hvan
  let s := U.card + a.totalDegree - Fintype.card F
  refine ⟨leadingSpecialization a.totalDegree a, leadingSpecialization s f,
    leadingSpecialization s g, leadingSpecialization_ne_zero a ha,
    (natDegree_leadingSpecialization_le _ _).trans had, ?_, ?_, ?_⟩
  · exact (natDegree_leadingSpecialization_le _ _).trans
      (Nat.sub_le_sub_right (Nat.add_le_add_left had U.card) _)
  · exact (natDegree_leadingSpecialization_le _ _).trans
      (Nat.sub_le_sub_right (Nat.add_le_add_left had U.card) _)
  · exact redei_leading_identity U a f g (Fintype.card F) Fintype.one_lt_card
      (card_le_redei_auxiliary_degree U a ha hvan) hf hg hid

end Balanced.StabilityPolynomial

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_StabilityCoprimeReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.StabilityCoprimeReduction

open Polynomial
open StabilityPolynomial
open scoped BigOperators

variable {F : Type*} [Field F]

theorem exists_coprime_grid_reduction
    (H f g : F[X]) (q : ℕ) (hH : H ≠ 0) (hf : f ≠ 0)
    (heq : H = X ^ q * f + g) :
    ∃ D f₀ g₀ : F[X],
      D ≠ 0 ∧ IsCoprime f₀ g₀ ∧ f₀ ≠ 0 ∧
      f₀.natDegree ≤ f.natDegree ∧ g₀.natDegree ≤ g.natDegree ∧
      f = D * f₀ ∧ g = D * g₀ ∧
      H = D * (X ^ q * f₀ + g₀) ∧
      X ^ q * f₀ + g₀ ≠ 0 ∧ X ^ q * f₀ + g₀ ∣ H := by
  classical
  let : GCDMonoid F[X] := EuclideanDomain.gcdMonoid F[X]
  let D := GCDMonoid.gcd f g
  have hD : D ≠ 0 := gcd_ne_zero_of_left hf
  have hDf : D * (f / D) = f :=
    EuclideanDomain.mul_div_cancel' hD (GCDMonoid.gcd_dvd_left f g)
  have hDg : D * (g / D) = g :=
    EuclideanDomain.mul_div_cancel' hD (GCDMonoid.gcd_dvd_right f g)
  have hfactor : H = D * (X ^ q * (f / D) + g / D) := by
    calc
      H = X ^ q * f + g := heq
      _ = X ^ q * (D * (f / D)) + D * (g / D) := by rw [hDf, hDg]
      _ = D * (X ^ q * (f / D) + g / D) := by ring
  have hquot : X ^ q * (f / D) + g / D ≠ 0 := by
    intro hz
    apply hH
    simpa [hz] using hfactor
  refine ⟨D, f / D, g / D, hD,
    isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hD,
    left_div_gcd_ne_zero hf,
    natDegree_le_natDegree (degree_div_le f D),
    natDegree_le_natDegree (degree_div_le g D),
    hDf.symm, hDg.symm, hfactor, hquot, ?_⟩
  exact ⟨D, hfactor.trans (mul_comm _ _)⟩

theorem redeiLeadingProduct_monic (U : Finset (Point F)) :
    (redeiLeadingProduct U).Monic :=
  monic_prod_of_monic U (fun p : Point F => X + C p.1)
    (fun p _ => monic_X_add_C p.1)

theorem redeiLeadingProduct_natDegree (U : Finset (Point F)) :
    (redeiLeadingProduct U).natDegree = U.card := by
  classical
  rw [redeiLeadingProduct, natDegree_prod_of_monic U
    (fun p : Point F => X + C p.1) (fun p _ => monic_X_add_C p.1)]
  simp

theorem multiplier_ne_zero_of_low_remainder
    (R A f g : F[X]) (q : ℕ) (hR : R ≠ 0) (hA : A ≠ 0)
    (hg : g.natDegree < R.natDegree)
    (heq : R * A = X ^ q * f + g) : f ≠ 0 := by
  intro hf
  have hRA : R * A = g := by simpa [hf] using heq
  have hdeg := congrArg Polynomial.natDegree hRA
  rw [natDegree_mul hR hA] at hdeg
  omega

variable [Fintype F]

theorem card_le_card_add_auxiliary_bound
    (U : Finset (Point F)) (d : ℕ)
    (hsize : 2 * (nonverticalSkewCodes U).card < (d + 1) * (d + 2)) :
    Fintype.card F ≤ U.card + d := by
  obtain ⟨a, ha, had, hvan⟩ := exists_redei_auxiliary U d hsize
  exact (card_le_redei_auxiliary_degree U a ha hvan).trans (Nat.add_le_add_left had U.card)

theorem exists_coprime_redei_identity
    (U : Finset (Point F)) (d : ℕ)
    (hsize : 2 * (nonverticalSkewCodes U).card < (d + 1) * (d + 2))
    (hdq : d < Fintype.card F) :
    ∃ A D f g : F[X],
      A ≠ 0 ∧ A.natDegree ≤ d ∧ D ≠ 0 ∧ IsCoprime f g ∧ f ≠ 0 ∧
      f.natDegree ≤ U.card + d - Fintype.card F ∧
      g.natDegree ≤ U.card + d - Fintype.card F ∧
      redeiLeadingProduct U * A = D * (X ^ Fintype.card F * f + g) ∧
      X ^ Fintype.card F * f + g ≠ 0 ∧
      X ^ Fintype.card F * f + g ∣ redeiLeadingProduct U * A := by
  obtain ⟨A, f, g, hA, hAd, hfdeg, hgdeg, heq⟩ := exists_redei_leading_identity U d hsize
  have hR : redeiLeadingProduct U ≠ 0 := (redeiLeadingProduct_monic U).ne_zero
  have horder := card_le_card_add_auxiliary_bound U d hsize
  have hU : 0 < U.card := by omega
  have hsmall : g.natDegree < (redeiLeadingProduct U).natDegree := by
    rw [redeiLeadingProduct_natDegree]
    omega
  have hf : f ≠ 0 := multiplier_ne_zero_of_low_remainder _ _ _ _ _ hR hA hsmall heq
  obtain ⟨D, f₀, g₀, hD, hcop, hf₀, hfd, hgd, _, _, hfactor, hnonzero, hdiv⟩ :=
    exists_coprime_grid_reduction (redeiLeadingProduct U * A) f g (Fintype.card F)
      (mul_ne_zero hR hA) hf heq
  exact ⟨A, D, f₀, g₀, hA, hAd, hD, hcop, hf₀,
    hfd.trans hfdeg, hgd.trans hgdeg, hfactor, hnonzero, hdiv⟩

end Balanced.StabilityCoprimeReduction

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_StabilityRootDivisibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.StabilityPolynomial

open Polynomial

variable {F : Type*} [Field F] [Fintype F]

theorem splits_dvd_vanishing_mul_derivative {R : F[X]} (hR : R.Splits) :
    R ∣ (X ^ Fintype.card F - X) * derivative R := by
  induction hR using Submonoid.closure_induction with
  | mem P hP =>
    rcases hP with (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · simp
    · have hroot : (X - C (-c) : F[X]) ∣ X ^ Fintype.card F - X := by
        apply dvd_iff_isRoot.mpr
        simp [IsRoot, FiniteField.pow_card]
      simpa using hroot
  | one => simp
  | mul P Q _ _ hP hQ =>
    have hsum := dvd_add (mul_dvd_mul hP (dvd_refl Q))
      (mul_dvd_mul (dvd_refl P) hQ)
    convert hsum using 1
    all_goals try with_reducible_and_instances rfl
    rw [derivative_mul]
    ring

theorem split_mul_dvd_vanishing_derivative_mul
    {R : F[X]} (hR : R.Splits) (A : F[X]) :
    R * A ∣ (X ^ Fintype.card F - X) * derivative (R * A) * A := by
  obtain ⟨T, hT⟩ := splits_dvd_vanishing_mul_derivative hR
  refine ⟨T * A + (X ^ Fintype.card F - X) * derivative A, ?_⟩
  rw [derivative_mul]
  calc
    (X ^ Fintype.card F - X) * (derivative R * A + R * derivative A) * A =
        ((X ^ Fintype.card F - X) * derivative R) * A ^ 2 +
          (R * A) * ((X ^ Fintype.card F - X) * derivative A) := by ring
    _ = R * A * (T * A + (X ^ Fintype.card F - X) * derivative A) := by
      rw [hT]
      ring

theorem redei_wronskian_divisibility
    {R A f g : F[X]} (hR : R.Splits)
    (hidentity : R * A = X ^ Fintype.card F * f + g) :
    R * A ∣ (X * f + g) * (derivative f * g - derivative g * f) * A := by
  let H := R * A
  let V : F[X] := X ^ Fintype.card F - X
  have hH : H = X ^ Fintype.card F * f + g := hidentity
  have hdH : derivative H = X ^ Fintype.card F * derivative f + derivative g := by
    rw [hH, derivative_add, derivative_mul, derivative_X_pow]
    simp
  have hfirst : X * f + g = H - V * f := by
    rw [hH]
    dsimp [V]
    ring
  have hsecond : derivative f * g - derivative g * f =
      derivative f * H - f * derivative H := by
    rw [hdH, hH]
    ring
  have hdiv : H ∣ V * derivative H * A :=
    split_mul_dvd_vanishing_derivative_mul hR A
  have hdiv' := dvd_mul_of_dvd_left hdiv (f ^ 2)
  have hmain : H ∣ H * ((H * derivative f - f * derivative H -
      V * f * derivative f) * A) := dvd_mul_right H _
  have hsum := dvd_add hmain hdiv'
  change H ∣ _
  rw [hfirst, hsecond]
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem redei_factor_wronskian_divisibility
    {R A H f g : F[X]} (hR : R.Splits) (hR0 : R ≠ 0)
    (hdiv : H ∣ R * A)
    (hidentity : H = X ^ Fintype.card F * f + g) :
    H ∣ (X * f + g) * (derivative f * g - derivative g * f) * A := by
  obtain ⟨S, B, hS, hB, hH⟩ := exists_dvd_and_dvd_of_dvd_mul hdiv
  have hsplit := hR.of_dvd hR0 hS
  have hSB : S * B = X ^ Fintype.card F * f + g := hH.symm.trans hidentity
  have hbase := redei_wronskian_divisibility hsplit hSB
  obtain ⟨C, hC⟩ := hB
  rw [hH, hC]
  simpa only [mul_assoc] using dvd_mul_of_dvd_left hbase C

end Balanced.StabilityPolynomial

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_StabilityLargeFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.StabilityPolynomial

open Polynomial
open scoped BigOperators Classical

variable {F : Type*} [Field F]

theorem rootMultiplicity_linear_product
    {ι : Type*} (s : Finset ι) (a : ι → F) (c : F) :
    rootMultiplicity c (∏ i ∈ s, (X - C (a i))) =
      (s.filter fun i => a i = c).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hprod : (∏ j ∈ s, (X - C (a j) : F[X])) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => X_sub_C_ne_zero (a j)
    rw [Finset.prod_insert hi,
      rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero (a i)) hprod),
      rootMultiplicity_X_sub_C, ih]
    by_cases hc : a i = c
    · simp [hc, Finset.filter_insert, hi, Nat.add_comm]
    · simp [hc, Ne.symm hc, Finset.filter_insert]

theorem rootMultiplicity_le_natDegree (A : F[X]) (hA : A ≠ 0) (c : F) :
    rootMultiplicity c A ≤ A.natDegree := by
  have h := natDegree_le_of_dvd (pow_rootMultiplicity_dvd A c) hA
  simpa only [natDegree_pow, natDegree_X_sub_C, mul_one] using h

theorem power_dvd_linear_product_card_bound
    {ι : Type*} (s : Finset ι) (a : ι → F) {A : F[X]} (hA : A ≠ 0)
    (c : F) (n : ℕ)
    (hdiv : (X - C c) ^ n ∣ (∏ i ∈ s, (X - C (a i))) * A) :
    n ≤ (s.filter fun i => a i = c).card + A.natDegree := by
  classical
  have hprod : (∏ i ∈ s, (X - C (a i) : F[X])) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero (a i)
  have h := (le_rootMultiplicity_iff (mul_ne_zero hprod hA)).mpr hdiv
  rw [rootMultiplicity_mul (mul_ne_zero hprod hA), rootMultiplicity_linear_product] at h
  exact h.trans (Nat.add_le_add_left (rootMultiplicity_le_natDegree A hA c) _)

theorem large_fiber_of_power_dvd
    {ι : Type*} (s : Finset ι) (a : ι → F) {A : F[X]} (hA : A ≠ 0)
    (c : F) (n : ℕ)
    (hdiv : (X - C c) ^ n ∣ (∏ i ∈ s, (X - C (a i))) * A) :
    n - A.natDegree ≤ (s.filter fun i => a i = c).card := by
  have h := power_dvd_linear_product_card_bound s a hA c n hdiv
  omega

variable [Fintype F]

theorem linear_pow_card (c : F) :
    (X - C c : F[X]) ^ Fintype.card F = X ^ Fintype.card F - C c := by
  have h := map_sub (FiniteField.frobeniusAlgHom F F[X]) (X : F[X]) (C c)
  change (X - C c) ^ Fintype.card F =
    X ^ Fintype.card F - (C c) ^ Fintype.card F at h
  simpa only [← C_pow, FiniteField.pow_card] using h

theorem frobenius_linear_factorization (a b : F) (ha : a ≠ 0) :
    C a * X ^ Fintype.card F + C b =
      C a * (X - C (-b / a)) ^ Fintype.card F := by
  rw [linear_pow_card, mul_sub, ← C_mul]
  have h : a * (-b / a) = -b := by field_simp
  rw [h, C_neg]
  ring

theorem large_fiber_of_frobenius_divisor
    {ι : Type*} (s : Finset ι) (x : ι → F) {A : F[X]} (hA : A ≠ 0)
    (a b : F) (ha : a ≠ 0)
    (hdiv : C a * X ^ Fintype.card F + C b ∣
      (∏ i ∈ s, (X + C (x i))) * A) :
    Fintype.card F - A.natDegree ≤ (s.filter fun i => x i = b / a).card := by
  classical
  have hpower : (X - C (-b / a)) ^ Fintype.card F ∣
      (∏ i ∈ s, (X + C (x i))) * A := by
    apply dvd_trans _ hdiv
    rw [frobenius_linear_factorization a b ha]
    exact dvd_mul_left _ _
  have h := large_fiber_of_power_dvd s (fun i => -x i) hA (-b / a)
    (Fintype.card F) (by simpa only [C_neg, sub_neg_eq_add] using hpower)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext i
  simp only [Finset.mem_filter]
  rw [neg_div, neg_inj]

theorem redei_large_vertical_fiber
    (U : Finset (Point F)) {A : F[X]} (hA : A ≠ 0)
    (a b : F) (ha : a ≠ 0)
    (hdiv : C a * X ^ Fintype.card F + C b ∣
      (∏ p ∈ U, (X + C p.1)) * A) :
    Fintype.card F - A.natDegree ≤
      (U.filter fun p => OnLine p (none, b / a)).card := by
  have hfiber : U.filter (fun point => OnLine point (none, b / a)) =
      U.filter (fun point => point.1 = b / a) :=
    Finset.filter_congr fun point _ => Iff.rfl
  rw [hfiber]
  exact large_fiber_of_frobenius_divisor U Prod.fst hA a b ha hdiv

end Balanced.StabilityPolynomial

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_StabilityPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.StabilityPolynomial

open Polynomial

variable {K : Type*} [Field K]

theorem derivatives_eq_zero_of_coprime_wronskian
    {f g : K[X]} (hcop : IsCoprime f g)
    (hW : derivative f * g - derivative g * f = 0) :
    derivative f = 0 ∧ derivative g = 0 := by
  have hW' : wronskian g f = 0 := by
    simpa only [wronskian, mul_comm] using hW
  exact (hcop.symm.wronskian_eq_zero_iff.mp hW').symm

theorem eq_C_of_derivative_eq_zero_of_natDegree_lt_char
    {p : ℕ} [CharP K p] {f : K[X]}
    (hdeg : f.natDegree < p) (hd : derivative f = 0) :
    f = C (f.coeff 0) := by
  apply eq_C_of_natDegree_eq_zero
  by_contra hn
  have hpos : 0 < f.natDegree := Nat.pos_of_ne_zero hn
  have hsucc : f.natDegree - 1 + 1 = f.natDegree := Nat.sub_add_cancel hpos
  have hcast : (f.natDegree : K) ≠ 0 := by
    intro hz
    exact Nat.not_dvd_of_pos_of_lt hpos hdeg
      ((CharP.cast_eq_zero_iff K p f.natDegree).mp hz)
  have hcoeff : f.coeff f.natDegree * (f.natDegree : K) = 0 := by
    have h := congrArg (fun r : K[X] => r.coeff (f.natDegree - 1)) hd
    simpa only [coeff_derivative, ← Nat.cast_add_one, hsucc, coeff_zero] using h
  have hzero : f = 0 := by
    apply leadingCoeff_eq_zero.mp
    exact (mul_eq_zero.mp hcoeff).resolve_right hcast
  exact hn (by simp [hzero])

theorem constants_of_coprime_wronskian_of_natDegree_lt_char
    {p : ℕ} [CharP K p] {f g : K[X]}
    (hcop : IsCoprime f g)
    (hf : f.natDegree < p) (hg : g.natDegree < p)
    (hW : derivative f * g - derivative g * f = 0) :
    f = C (f.coeff 0) ∧ g = C (g.coeff 0) := by
  obtain ⟨hdf, hdg⟩ := derivatives_eq_zero_of_coprime_wronskian hcop hW
  exact ⟨eq_C_of_derivative_eq_zero_of_natDegree_lt_char hf hdf,
    eq_C_of_derivative_eq_zero_of_natDegree_lt_char hg hdg⟩

end Balanced.StabilityPolynomial

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_StabilityAlgebraAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.StabilityPolynomial

open Polynomial Classical

variable {F : Type*} [Field F] [Fintype F]

theorem vertical_fiber_of_coprime_wronskian
    (hprime : Nat.Prime (Fintype.card F)) (U : Finset (Point F))
    {A f g : F[X]} (hA : A ≠ 0) (hf : f ≠ 0)
    (hcop : IsCoprime f g)
    (hfdeg : f.natDegree < Fintype.card F)
    (hgdeg : g.natDegree < Fintype.card F)
    (hW : derivative f * g - derivative g * f = 0)
    (hdiv : X ^ Fintype.card F * f + g ∣ redeiLeadingProduct U * A) :
    ∃ c : F, Fintype.card F - A.natDegree ≤
      (U.filter fun p => OnLine p (none, c)).card := by
  classical
  let : Fact (Nat.Prime (Fintype.card F)) := ⟨hprime⟩
  let : CharP F (Fintype.card F) := charP_of_card_eq_prime rfl
  obtain ⟨hfc, hgc⟩ := constants_of_coprime_wronskian_of_natDegree_lt_char
    hcop hfdeg hgdeg hW
  have ha : f.coeff 0 ≠ 0 := by
    intro hz
    apply hf
    simpa [hz] using hfc
  refine ⟨g.coeff 0 / f.coeff 0, ?_⟩
  apply redei_large_vertical_fiber U hA (f.coeff 0) (g.coeff 0) ha
  rw [hfc, hgc] at hdiv
  simpa only [redeiLeadingProduct, mul_comm] using hdiv

theorem redei_coprime_wronskian_divisor
    (U : Finset (Point F)) {A f g : F[X]}
    (hdiv : X ^ Fintype.card F * f + g ∣ redeiLeadingProduct U * A) :
    X ^ Fintype.card F * f + g ∣
      (X * f + g) * (derivative f * g - derivative g * f) * A := by
  apply redei_factor_wronskian_divisibility
    (R := redeiLeadingProduct U) (hidentity := rfl)
    (hR0 := StabilityCoprimeReduction.redeiLeadingProduct_monic U |>.ne_zero)
    (hdiv := hdiv)
  exact Splits.prod fun p _ => Splits.X_add_C p.1

omit [Fintype F] in
private theorem equal_degree_wronskian_budget (f g : F[X]) (heq : f.natDegree = g.natDegree)
    (hW : derivative f * g - derivative g * f ≠ 0) :
    (derivative f * g - derivative g * f).natDegree + 2 ≤ 2 * f.natDegree := by
  have hf : f ≠ 0 := by intro h; simp [h] at hW
  have hg : g ≠ 0 := by intro h; simp [h] at hW
  let c : F := f.leadingCoeff / g.leadingCoeff
  let h : F[X] := f - C c * g
  have hc : c ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hf) (leadingCoeff_ne_zero.mpr hg)
  have hid : derivative h * g - derivative g * h = derivative f * g - derivative g * f := by
    dsimp [h]
    rw [derivative_sub, derivative_mul, derivative_C]
    ring
  have hh : h ≠ 0 := by
    intro hz
    have := hid
    simp [hz] at this
    exact hW this.symm
  have hdrop : h.natDegree < f.natDegree := by
    apply (natDegree_lt_iff_degree_lt hh).2
    rw [← degree_eq_natDegree hf]
    apply degree_sub_lt_left
    · rw [degree_mul, degree_C hc, zero_add, degree_eq_natDegree hf,
        degree_eq_natDegree hg, heq]
    · exact hf
    · rw [leadingCoeff_mul, leadingCoeff_C]
      dsimp [c]
      exact (div_mul_cancel₀ _ (leadingCoeff_ne_zero.mpr hg)).symm
  have hident : wronskian g h = derivative f * g - derivative g * f := by
    calc
      wronskian g h = derivative h * g - derivative g * h := by
        unfold wronskian
        ring
      _ = _ := hid
  have hw : wronskian g h ≠ 0 := by
    rw [hident]
    exact hW
  have hbound := natDegree_wronskian_lt_add hw
  rw [hident, ← heq] at hbound
  omega

omit [Fintype F] in
private theorem assembled_asymmetric_degree_budget (f g : F[X]) (s : ℕ)
    (hf : f ≠ 0) (hfs : f.natDegree ≤ s) (hgs : g.natDegree ≤ s)
    (hW : derivative f * g - derivative g * f ≠ 0) :
    (X * f + g).natDegree + (derivative f * g - derivative g * f).natDegree + 1 ≤
      f.natDegree + 2 * s := by
  have hL := natDegree_add_le (X * f) g
  rw [natDegree_X_mul hf] at hL
  have hstandard : (derivative f * g - derivative g * f).natDegree <
      f.natDegree + g.natDegree := by
    have hi : wronskian g f = derivative f * g - derivative g * f := by
      unfold wronskian
      ring
    have hb := natDegree_wronskian_lt_add (show wronskian g f ≠ 0 by rwa [hi])
    rw [hi] at hb
    omega
  rcases lt_trichotomy f.natDegree g.natDegree with hlt | heq | hgt
  · rw [max_eq_right (by omega)] at hL
    omega
  · have hsharp := equal_degree_wronskian_budget f g heq hW
    rw [← heq, max_eq_left (by omega)] at hL
    omega
  · rw [max_eq_left (by omega)] at hL
    omega

omit [Fintype F] in
private theorem assembled_zero_factor (f g A : F[X]) (q s d : ℕ)
    (hf : f ≠ 0) (hA : A ≠ 0)
    (hfs : f.natDegree ≤ s) (hgs : g.natDegree ≤ s)
    (hgq : g.natDegree < q) (hAd : A.natDegree ≤ d)
    (hgap : 2 * s + d < q + 1)
    (hdiv : X ^ q * f + g ∣ (X * f + g) * (derivative f * g - derivative g * f) * A) :
    X * f + g = 0 ∨ derivative f * g - derivative g * f = 0 := by
  by_contra hn
  push Not at hn
  have hLW := mul_ne_zero hn.1 hn.2
  have hprod := mul_ne_zero hLW hA
  have hdegree := natDegree_le_of_dvd hdiv hprod
  have hH : (X ^ q * f + g).natDegree = f.natDegree + q := by
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow_mul q hf]
    rw [natDegree_X_pow_mul q hf]
    omega
  rw [hH, natDegree_mul hLW hA, natDegree_mul hn.1 hn.2] at hdegree
  have hbudget := assembled_asymmetric_degree_budget f g s hf hfs hgs hn.2
  omega

private theorem empty_columns_le_auxiliary_degree (U : Finset (Point F)) {A f g : F[X]} (hA : A ≠ 0)
    (hfirst : X * f + g = 0)
    (hdiv : X ^ Fintype.card F * f + g ∣ redeiLeadingProduct U * A) :
    (Finset.univ.filter fun c : F => ∀ p ∈ U, p.1 ≠ c).card ≤ A.natDegree := by
  classical
  let S := Finset.univ.filter fun c : F => ∀ p ∈ U, p.1 ≠ c
  have hroot : ∀ c ∈ S, A.eval (-c) = 0 := by
    intro c hc
    have hc' : ∀ p ∈ U, p.1 ≠ c := (Finset.mem_filter.mp hc).2
    have hH : (X ^ Fintype.card F * f + g).eval (-c) = 0 := by
      have hh := congrArg (fun P : F[X] => P.eval (-c)) hfirst
      simpa only [eval_add, eval_mul, eval_pow, eval_X, eval_zero,
        FiniteField.pow_card] using hh
    have hRA : (redeiLeadingProduct U * A).eval (-c) = 0 := by
      obtain ⟨Q, hQ⟩ := hdiv
      rw [hQ, eval_mul, hH, zero_mul]
    have hR : (redeiLeadingProduct U).eval (-c) ≠ 0 := by
      simp only [redeiLeadingProduct, eval_prod, eval_add, eval_X, eval_C]
      apply Finset.prod_ne_zero_iff.mpr
      intro p hp hz
      apply hc' p hp
      linear_combination hz
    rw [eval_mul] at hRA
    exact (mul_eq_zero.mp hRA).resolve_left hR
  have hcard : (S.image fun c => -c).card ≤ A.natDegree := by
    apply card_le_degree_of_subset_roots
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_roots hA).2 (hroot c hc)
  simpa only [Finset.card_image_of_injective S neg_injective] using hcard

theorem normalized_prime_stability
    (hprime : Nat.Prime (Fintype.card F)) (U : Finset (Point F)) (d : ℕ)
    (hU : U.card ≤ Fintype.card F)
    (hsize : 2 * (nonverticalSkewCodes U).card < (d + 1) * (d + 2))
    (hgap : 3 * d < Fintype.card F + 1)
    (hempty : d < (Finset.univ.filter fun c : F => ∀ p ∈ U, p.1 ≠ c).card) :
    ∃ c : F, Fintype.card F - d ≤
      (U.filter fun p => OnLine p (none, c)).card := by
  classical
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hdq : d < Fintype.card F := by omega
  obtain ⟨A, D, f, g, hA, hAd, _hD, hcop, hf, hfd, hgd, _heq, _hH, hdiv⟩ :=
    StabilityCoprimeReduction.exists_coprime_redei_identity U d hsize hdq
  have hfs : f.natDegree ≤ d := by omega
  have hgs : g.natDegree ≤ d := by omega
  have hfq : f.natDegree < Fintype.card F := by omega
  have hgq : g.natDegree < Fintype.card F := by omega
  have hdivW := redei_coprime_wronskian_divisor U hdiv
  rcases assembled_zero_factor f g A (Fintype.card F) d d hf hA hfs hgs hgq hAd
      (by omega) hdivW with hfirst | hW
  · have hcount := empty_columns_le_auxiliary_degree U hA hfirst hdiv
    omega
  · obtain ⟨c, hc⟩ := vertical_fiber_of_coprime_wronskian hprime U hA hf hcop hfq hgq hW hdiv
    exact ⟨c, (show Fintype.card F - d ≤ Fintype.card F - A.natDegree by omega).trans hc⟩

end Balanced.StabilityPolynomial

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_ProjectiveIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem projectiveLinePoints_some (l : Line F) :
    projectiveLinePoints (some l) = (linePoints l).disjSum {l.1} := by
  ext P
  rw [mem_projectiveLinePoints]
  cases P <;> simp [linePoints, ProjectiveIncident,
    ThroughProjective, eq_comm]

theorem projectiveLinePoints_none :
    projectiveLinePoints (none : ProjectiveLine F) =
      (∅ : Finset (Point F)).disjSum Finset.univ := by
  ext P
  rw [mem_projectiveLinePoints]
  cases P <;> simp [ProjectiveIncident]

theorem card_projectiveLinePoints (l : ProjectiveLine F) :
    (projectiveLinePoints l).card = Fintype.card F + 1 := by
  cases l with
  | none => simp [projectiveLinePoints_none, Direction]
  | some l => simp [projectiveLinePoints_some, linePoints_card]

theorem card_projectivePencil (P : ProjectivePoint F) :
    (projectivePencil P).card = Fintype.card F + 1 := by
  have h : (projectiveLinePoints (dualLine P)).card = (projectivePencil P).card := by
    apply Finset.card_equiv projectiveDuality
    intro Q
    simp only [mem_projectiveLinePoints, mem_projectivePencil]
    change ProjectiveIncident Q (dualLine P) ↔ ProjectiveIncident P (dualLine Q)
    simpa only [dualPoint_dualLine] using (projective_incident_dual P (dualLine Q)).symm
  rw [← h, card_projectiveLinePoints]

omit [Fintype F] in

theorem eq_projectiveJoin_of_incident (P Q : ProjectivePoint F) (hPQ : P ≠ Q)
    (l : ProjectiveLine F) (hP : ProjectiveIncident P l)
    (hQ : ProjectiveIncident Q l) : l = projectiveJoin P Q := by
  cases P with
  | inl p =>
    cases Q with
    | inl q =>
      cases l with
      | none => exact False.elim hP
      | some l =>
        apply congrArg some
        exact eq_of_two_common_points p q (fun h => hPQ (congrArg Sum.inl h))
          l (joiningLine p q) hP hQ (onLine_joiningLine_left p q)
          (onLine_joiningLine_right p q)
    | inr d =>
      cases l with
      | none => exact False.elim hP
      | some l =>
        apply congrArg some
        change l.1 = d at hQ
        rw [line_eq_lineThrough p l hP, hQ]
  | inr d =>
    cases Q with
    | inl p =>
      cases l with
      | none => exact False.elim hQ
      | some l =>
        apply congrArg some
        change l.1 = d at hP
        rw [line_eq_lineThrough p l hQ, hP]
    | inr e =>
      cases l with
      | none => rfl
      | some l =>
        change l.1 = d at hP
        change l.1 = e at hQ
        exact False.elim (hPQ (congrArg Sum.inr (hP.symm.trans hQ)))

omit [Fintype F] in
theorem eq_of_two_common_projective_points (P Q : ProjectivePoint F) (hPQ : P ≠ Q)
    (l m : ProjectiveLine F) (hPl : ProjectiveIncident P l)
    (hQl : ProjectiveIncident Q l) (hPm : ProjectiveIncident P m)
    (hQm : ProjectiveIncident Q m) : l = m :=
  (eq_projectiveJoin_of_incident P Q hPQ l hPl hQl).trans
    (eq_projectiveJoin_of_incident P Q hPQ m hPm hQm).symm

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_StabilitySkewCountLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace Balanced
open scoped _root_.Balanced

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem card_nonSkew_pencil_erase_le (B : Finset (ProjectivePoint F))
    (ell : ProjectiveLine F) (P : ProjectivePoint F)
    (hP : ProjectiveIncident P ell) (hPB : P ∉ B) :
    (((projectivePencil P).erase ell).filter (fun l => l ∉ skewProjective B)).card ≤
      (B \ projectiveLinePoints ell).card := by
  classical
  apply Finset.card_le_card_of_surjOn (projectiveJoin P)
  intro l hl
  change l ∈ ((projectivePencil P).erase ell).filter (fun l => l ∉ skewProjective B) at hl
  simp only [Finset.mem_filter, Finset.mem_erase, mem_projectivePencil] at hl
  obtain ⟨⟨hlne, hPl⟩, hbad⟩ := hl
  have hex : ∃ Q ∈ B, ProjectiveIncident Q l := by
    simpa only [skewProjective, Finset.mem_filter, Finset.mem_univ, true_and,
      not_forall, not_not, exists_prop] using hbad
  obtain ⟨Q, hQB, hQl⟩ := hex
  have hPQ : P ≠ Q := fun h => hPB (h.symm ▸ hQB)
  have hQell : ¬ ProjectiveIncident Q ell := by
    intro h
    exact hlne (eq_of_two_common_projective_points P Q hPQ l ell hPl hQl hP h)
  refine ⟨Q, ?_, ?_⟩
  · exact Finset.mem_sdiff.mpr ⟨hQB, by simpa using hQell⟩
  · exact (eq_projectiveJoin_of_incident P Q hPQ l hPl hQl).symm

theorem card_skewThroughExcept_ge (B : Finset (ProjectivePoint F))
    (ell : ProjectiveLine F) (P : ProjectivePoint F)
    (hP : ProjectiveIncident P ell) (hPB : P ∉ B) :
    Fintype.card F - (B \ projectiveLinePoints ell).card ≤
      (skewThroughExcept B ell P).card := by
  have hcount : ((projectivePencil P).erase ell).card = Fintype.card F := by
    rw [Finset.card_erase_of_mem ((mem_projectivePencil P ell).mpr hP), card_projectivePencil]
    omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (projectivePencil P).erase ell) (p := fun l => l ∈ skewProjective B)
  have hblocked := card_nonSkew_pencil_erase_le B ell P hP hPB
  change (((projectivePencil P).erase ell).filter (fun l => l ∈ skewProjective B)).card +
    (((projectivePencil P).erase ell).filter (fun l => l ∉ skewProjective B)).card =
    ((projectivePencil P).erase ell).card at hsplit
  unfold skewThroughExcept
  omega

theorem skewThroughExcept_disjoint (B : Finset (ProjectivePoint F))
    (ell : ProjectiveLine F) {P Q : ProjectivePoint F} (hPQ : P ≠ Q)
    (hP : ProjectiveIncident P ell) (hQ : ProjectiveIncident Q ell) :
    Disjoint (skewThroughExcept B ell P) (skewThroughExcept B ell Q) := by
  apply Finset.disjoint_left.mpr
  intro l hlP hlQ
  obtain ⟨hlne, hPl, _⟩ := (mem_skewThroughExcept B ell P l).mp hlP
  obtain ⟨_, hQl, _⟩ := (mem_skewThroughExcept B ell Q l).mp hlQ
  exact hlne (eq_of_two_common_projective_points P Q hPQ l ell hPl hQl hP hQ)

theorem missing_mul_order_sub_offLine_le_skew (B : Finset (ProjectivePoint F))
    (ell : ProjectiveLine F) :
    (projectiveLinePoints ell \ B).card *
      (Fintype.card F - (B \ projectiveLinePoints ell).card) ≤
      (skewProjective B).card := by
  classical
  let S := projectiveLinePoints ell \ B
  have hdis : (↑S : Set (ProjectivePoint F)).PairwiseDisjoint (skewThroughExcept B ell) := by
    intro P hP Q hQ hPQ
    exact skewThroughExcept_disjoint B ell hPQ
      ((mem_projectiveLinePoints ell P).mp (Finset.mem_sdiff.mp hP).1)
      ((mem_projectiveLinePoints ell Q).mp (Finset.mem_sdiff.mp hQ).1)
  have hsub : S.biUnion (skewThroughExcept B ell) ⊆ skewProjective B := by
    intro l hl
    obtain ⟨P, _, hPl⟩ := Finset.mem_biUnion.mp hl
    exact ((mem_skewThroughExcept B ell P l).mp hPl).2.2
  calc
    S.card * (Fintype.card F - (B \ projectiveLinePoints ell).card) =
        ∑ _P ∈ S, (Fintype.card F - (B \ projectiveLinePoints ell).card) := by simp
    _ ≤ ∑ P ∈ S, (skewThroughExcept B ell P).card := by
      apply Finset.sum_le_sum
      intro P hP
      exact card_skewThroughExcept_ge B ell P
        ((mem_projectiveLinePoints ell P).mp (Finset.mem_sdiff.mp hP).1)
        (Finset.mem_sdiff.mp hP).2
    _ = (S.biUnion (skewThroughExcept B ell)).card := (Finset.card_biUnion hdis).symm
    _ ≤ (skewProjective B).card := Finset.card_le_card hsub

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_StabilityTangents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.StabilityTangents

open scoped BigOperators
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem intersection_card_zero_iff (B : Finset (ProjectivePoint F)) (l : ProjectiveLine F) :
    (B.filter (fun P => ProjectiveIncident P l)).card = 0 ↔ l ∈ skewProjective B := by
  simp [Finset.card_eq_zero, Finset.filter_eq_empty_iff, skewProjective]

theorem sum_intersections_le_card (B : Finset (ProjectivePoint F))
    (P : ProjectivePoint F) (hPB : P ∉ B) (S : Finset (ProjectiveLine F))
    (hS : S ⊆ projectivePencil P) :
    ∑ l ∈ S, (B.filter (fun Q => ProjectiveIncident Q l)).card ≤ B.card := by
  have hswap : (∑ l ∈ S, (B.filter (fun Q => ProjectiveIncident Q l)).card) =
      ∑ Q ∈ B, (S.filter (ProjectiveIncident Q)).card := by
    simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := ProjectiveIncident) (s := B) (t := S)).symm
  rw [hswap]
  calc
    ∑ Q ∈ B, (S.filter (ProjectiveIncident Q)).card ≤ ∑ _Q ∈ B, 1 := by
      apply Finset.sum_le_sum
      intro Q hQB
      apply Finset.card_le_one.mpr
      intro l hl m hm
      exact eq_of_two_common_projective_points P Q (fun h => hPB (h.symm ▸ hQB)) l m
        ((mem_projectivePencil P l).mp (hS (Finset.mem_filter.mp hl).1))
        (Finset.mem_filter.mp hl).2
        ((mem_projectivePencil P m).mp (hS (Finset.mem_filter.mp hm).1))
        (Finset.mem_filter.mp hm).2
    _ = B.card := by simp

theorem twice_card_le_intersections_and_small (B : Finset (ProjectivePoint F))
    (S : Finset (ProjectiveLine F)) :
    2 * S.card ≤ (∑ l ∈ S, (B.filter (fun P => ProjectiveIncident P l)).card) +
      2 * (S.filter (fun l => l ∈ skewProjective B)).card +
      (S.filter (fun l => l ∈ tangents B)).card := by
  let n := fun l => (B.filter (fun P => ProjectiveIncident P l)).card
  have hpoint (l : ProjectiveLine F) :
      2 ≤ n l + (if n l = 0 then 2 else 0) + (if n l = 1 then 1 else 0) := by
    split_ifs <;> omega
  have hs := Finset.sum_le_sum (s := S) (fun l _ => hpoint l)
  have hz : (∑ l ∈ S, if n l = 0 then 2 else 0) =
      2 * (S.filter (fun l => l ∈ skewProjective B)).card := by
    simp only [n, intersection_card_zero_iff]
    rw [← Finset.sum_filter]
    simp [Nat.mul_comm]
  have ht : (∑ l ∈ S, if n l = 1 then 1 else 0) =
      (S.filter (fun l => l ∈ tangents B)).card := by
    simp only [n, ← mem_tangents]
    rw [← Finset.sum_filter]
    simp
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at hs
  rw [hz, ht] at hs
  simpa only [n, Nat.mul_comm S.card 2] using hs

theorem sum_pencil_erase_filter_le (ell : ProjectiveLine F) (T : Finset (ProjectiveLine F)) :
    (∑ P ∈ projectiveLinePoints ell,
      (((projectivePencil P).erase ell).filter (fun l => l ∈ T)).card) ≤ T.card := by
  let fibers := fun P => ((projectivePencil P).erase ell).filter (fun l => l ∈ T)
  have hd : (↑(projectiveLinePoints ell) : Set (ProjectivePoint F)).PairwiseDisjoint fibers := by
    intro P hP Q hQ hPQ
    apply Finset.disjoint_left.mpr
    intro l hlP hlQ
    obtain ⟨hlne, hPl⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp hlP).1
    obtain ⟨_, hQl⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp hlQ).1
    exact hlne (eq_of_two_common_projective_points P Q hPQ l ell
      ((mem_projectivePencil P l).mp hPl) ((mem_projectivePencil Q l).mp hQl)
      ((mem_projectiveLinePoints ell P).mp hP) ((mem_projectiveLinePoints ell Q).mp hQ))
  have hsub : (projectiveLinePoints ell).biUnion fibers ⊆ T := by
    intro l hl
    obtain ⟨P, _, hPl⟩ := Finset.mem_biUnion.mp hl
    exact (Finset.mem_filter.mp hPl).2
  rw [← Finset.card_biUnion hd]
  exact Finset.card_le_card hsub

theorem total_tangents_bound (B : Finset (ProjectivePoint F))
    (ell : ProjectiveLine F) (hell : ell ∈ skewProjective B) :
    2 * Fintype.card F * (Fintype.card F + 1) ≤
      B.card * (Fintype.card F + 1) + 2 * (skewProjective B).card + (tangents B).card := by
  have hlocal (P : ProjectivePoint F) (hP : P ∈ projectiveLinePoints ell) :
      2 * Fintype.card F ≤ B.card +
        2 * (((projectivePencil P).erase ell).filter (fun l => l ∈ skewProjective B)).card +
        (((projectivePencil P).erase ell).filter (fun l => l ∈ tangents B)).card := by
    have hPB : P ∉ B := by
      intro hPB
      exact (Finset.mem_filter.mp hell).2 P hPB ((mem_projectiveLinePoints ell P).mp hP)
    have hc : ((projectivePencil P).erase ell).card = Fintype.card F := by
      rw [Finset.card_erase_of_mem ((mem_projectivePencil P ell).mpr
        ((mem_projectiveLinePoints ell P).mp hP)), card_projectivePencil]
      omega
    have hs := sum_intersections_le_card B P hPB ((projectivePencil P).erase ell)
      (Finset.erase_subset _ _)
    have ht := twice_card_le_intersections_and_small B ((projectivePencil P).erase ell)
    rw [hc] at ht
    omega
  have hs := Finset.sum_le_sum (s := projectiveLinePoints ell) hlocal
  have hzero := sum_pencil_erase_filter_le ell (skewProjective B)
  have hone := sum_pencil_erase_filter_le ell (tangents B)
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
    ← Finset.mul_sum, card_projectiveLinePoints] at hs
  nlinarith

theorem sum_tangencies (B : Finset (ProjectivePoint F)) :
    (∑ P ∈ B, ((tangents B).filter (ProjectiveIncident P)).card) = (tangents B).card := by
  calc
    (∑ P ∈ B, ((tangents B).filter (ProjectiveIncident P)).card) =
        ∑ l ∈ tangents B, (B.filter (fun P => ProjectiveIncident P l)).card := by
      simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow] using
        (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (r := ProjectiveIncident) (s := B) (t := tangents B))
    _ = ∑ _l ∈ tangents B, 1 := by
      apply Finset.sum_congr rfl
      intro l hl
      exact (mem_tangents B l).mp hl
    _ = (tangents B).card := by simp

theorem exists_tangent_rich_point (B : Finset (ProjectivePoint F))
    (hB : B.Nonempty) (ell : ProjectiveLine F) (hell : ell ∈ skewProjective B)
    (hsize : (B.card : ℝ) ≤ (3 / 2 : ℝ) * ((Fintype.card F : ℝ) + 1)) :
    ∃ P ∈ B, (2 / 3 : ℝ) * (2 * (Fintype.card F : ℝ) - B.card -
      2 * ((skewProjective B).card : ℝ) / ((Fintype.card F : ℝ) + 1)) ≤
      (((tangents B).filter (ProjectiveIncident P)).card : ℝ) := by
  let a : ℝ := (2 / 3 : ℝ) * (2 * (Fintype.card F : ℝ) - B.card -
      2 * ((skewProjective B).card : ℝ) / ((Fintype.card F : ℝ) + 1))
  by_cases ha : a ≤ 0
  · obtain ⟨P, hP⟩ := hB
    exact ⟨P, hP, ha.trans (Nat.cast_nonneg _)⟩
  have hapos : 0 ≤ a := le_of_lt (lt_of_not_ge ha)
  have htotal : 2 * (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1) ≤
      (B.card : ℝ) * ((Fintype.card F : ℝ) + 1) +
        2 * ((skewProjective B).card : ℝ) + ((tangents B).card : ℝ) := by
    exact_mod_cast total_tangents_bound B ell hell
  have hq : (Fintype.card F : ℝ) + 1 ≠ 0 := by positivity
  have haeq : (3 / 2 : ℝ) * ((Fintype.card F : ℝ) + 1) * a =
      2 * (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1) -
        (B.card : ℝ) * ((Fintype.card F : ℝ) + 1) -
        2 * ((skewProjective B).card : ℝ) := by
    dsimp [a]
    field_simp
  have hmean : (B.card : ℝ) * a ≤ ((tangents B).card : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hsize hapos
    rw [haeq] at hm
    linarith
  have hsumR : (∑ P ∈ B, (((tangents B).filter (ProjectiveIncident P)).card : ℝ)) =
      ((tangents B).card : ℝ) := by exact_mod_cast sum_tangencies B
  apply Finset.exists_le_of_sum_le hB
  calc
    (∑ _P ∈ B, a) = (B.card : ℝ) * a := by simp
    _ ≤ ((tangents B).card : ℝ) := hmean
    _ = ∑ P ∈ B, (((tangents B).filter (ProjectiveIncident P)).card : ℝ) := hsumR.symm

theorem skew_nonempty_of_card_le_order (B : Finset (ProjectivePoint F))
    (hB : B.card ≤ Fintype.card F) : (skewProjective B).Nonempty := by
  by_contra hempty
  have hnone : skewProjective B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  have hpos (l : ProjectiveLine F) :
      1 ≤ (B.filter (fun P => ProjectiveIncident P l)).card := by
    have hne : (B.filter (fun P => ProjectiveIncident P l)).card ≠ 0 := by
      intro hz
      have hm := (intersection_card_zero_iff B l).mp hz
      simp [hnone] at hm
    omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun l _ => hpos l)
  have hsum : (∑ l : ProjectiveLine F, (B.filter (fun P => ProjectiveIncident P l)).card) =
      (Fintype.card F + 1) * B.card := by
    apply sum_line_count ProjectiveIncident B (Fintype.card F + 1)
    intro P _
    exact card_projectivePencil P
  have hcard : Fintype.card (ProjectiveLine F) =
      Fintype.card F ^ 2 + Fintype.card F + 1 := by
    simp only [ProjectiveLine, Line, Direction, Fintype.card_option, Fintype.card_prod]
    ring
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, mul_one, hcard, hsum] at hs
  nlinarith

theorem card_skew_empty : (skewProjective (∅ : Finset (ProjectivePoint F))).card =
    Fintype.card F ^ 2 + Fintype.card F + 1 := by
  simp [skewProjective, ProjectiveLine, Line, Direction]
  ring

theorem nonempty_of_small_skew (B : Finset (ProjectivePoint F))
    (hskew : ((skewProjective B).card : ℝ) <
      (201 / 10000 : ℝ) * (Fintype.card F : ℝ) ^ 2) : B.Nonempty := by
  by_contra hB
  have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
  rw [he, card_skew_empty] at hskew
  push_cast at hskew
  nlinarith [sq_nonneg (Fintype.card F : ℝ), Nat.cast_nonneg (α := ℝ) (Fintype.card F)]

theorem exists_tangent_flag_with_margin (B : Finset (ProjectivePoint F)) (d : ℕ)
    (hq : (100 : ℝ) ≤ (Fintype.card F : ℝ)) (hB : B.card ≤ Fintype.card F)
    (hdegree : (d : ℝ) ^ 2 < 2 * ((skewProjective B).card : ℝ))
    (hskew : ((skewProjective B).card : ℝ) <
      (201 / 10000 : ℝ) * (Fintype.card F : ℝ) ^ 2) :
    ∃ P ∈ B, ∃ ell ∈ tangents B, ProjectiveIncident P ell ∧
      (d : ℝ) + 1 < (((tangents B).filter (ProjectiveIncident P)).card : ℝ) := by
  have hBn := nonempty_of_small_skew B hskew
  obtain ⟨ell0, hell0⟩ := skew_nonempty_of_card_le_order B hB
  have hBR : (B.card : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hB
  obtain ⟨P, hPB, hP⟩ := exists_tangent_rich_point B hBn ell0 hell0 (by linarith)
  have hm := StabilityAffineArithmetic.tangent_margin hq hBR
    (Nat.cast_nonneg d) hdegree hskew
  have hstrict : (d : ℝ) + 1 <
      (((tangents B).filter (ProjectiveIncident P)).card : ℝ) := hm.trans_le hP
  have hpos : 0 < ((tangents B).filter (ProjectiveIncident P)).card := by
    have hposR : (0 : ℝ) < (((tangents B).filter (ProjectiveIncident P)).card : ℝ) := by
      linarith [Nat.cast_nonneg (α := ℝ) d]
    exact_mod_cast hposR
  obtain ⟨ell, hell⟩ := Finset.card_pos.mp hpos
  exact ⟨P, hPB, ell, (Finset.mem_filter.mp hell).1,
    (Finset.mem_filter.mp hell).2, hstrict⟩

end Balanced.StabilityTangents

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_SmallProjectiveStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]

theorem small_projective_line_refinement (B : Finset (ProjectivePoint F))
    (ell : ProjectiveLine F) (hB : B.card ≤ Fintype.card F)
    (hhalf : Fintype.card F + 1 ≤
      2 * (B.filter (fun P => ProjectiveIncident P ell)).card) :
    (Fintype.card F : ℝ) - 2 * ((skewProjective B).card : ℝ) /
      ((Fintype.card F : ℝ) + 1) ≤
        ((B.filter (fun P => ProjectiveIncident P ell)).card : ℝ) := by
  have hf : B.filter (fun P => ProjectiveIncident P ell) =
      B ∩ projectiveLinePoints ell := by ext P; simp
  rw [hf] at hhalf ⊢
  have hline : (B ∩ projectiveLinePoints ell).card +
      (projectiveLinePoints ell \ B).card = Fintype.card F + 1 := by
    rw [Finset.inter_comm B, Nat.add_comm, Finset.card_sdiff_add_card_inter,
      card_projectiveLinePoints]
  have hsize : (B \ projectiveLinePoints ell).card +
      (B ∩ projectiveLinePoints ell).card ≤ Fintype.card F := by
    rw [Finset.card_sdiff_add_card_inter]
    exact hB
  have hstrong := SmallProjectiveArithmetic.half_line_skew_refinement
    (Fintype.card F) (B ∩ projectiveLinePoints ell).card
    (B \ projectiveLinePoints ell).card (projectiveLinePoints ell \ B).card
    (skewProjective B).card hline hsize hhalf
    (missing_mul_order_sub_offLine_le_skew B ell)
  linarith

omit [Fintype F] in
theorem vertical_fiber_le_projective_section (U : Finset (Point F)) (c : F) :
    (U.filter (fun p => OnLine p (none,c))).card ≤
      ((U.disjSum {none}).filter
        (fun P => ProjectiveIncident P (some (none,c)))).card := by
  apply Finset.card_le_card_of_injOn Sum.inl
  · intro p hp
    obtain ⟨hpU, hpOn⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.inl_mem_disjSum.mpr hpU, hpOn⟩
  · intro p hp q hq h
    exact Sum.inl.inj h

theorem card_nonvertical_skew_codes_explicit (U : Finset (Point F)) :
    (StabilityPolynomial.nonverticalSkewCodes U).card =
      (Finset.univ.filter (fun z : Fin 2 → F =>
        ∀ p ∈ U, ¬ OnLine p (some (z 1), z 0))).card := by
  apply congrArg Finset.card
  ext z
  simp only [StabilityPolynomial.mem_nonverticalSkewCodes, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem small_projective_stability
    (hprime : Nat.Prime (Fintype.card F)) (hq : 100 ≤ Fintype.card F)
    (B : Finset (ProjectivePoint F)) (hB : B.card ≤ Fintype.card F)
    (hsmall : ((skewProjective B).card : ℝ) <
      (201 / 10000 : ℝ) * (Fintype.card F : ℝ) ^ 2) :
    ∃ ell : ProjectiveLine F,
      (Fintype.card F : ℝ) - 2 * ((skewProjective B).card : ℝ) /
        ((Fintype.card F : ℝ) + 1) ≤
          ((B.filter (fun P => ProjectiveIncident P ell)).card : ℝ) := by
  classical
  have hδ : 0 < (skewProjective B).card :=
    Finset.card_pos.mpr (StabilityTangents.skew_nonempty_of_card_le_order B hB)
  obtain ⟨d, hd2, hdim⟩ :=
    SmallProjectiveArithmetic.exists_interpolation_degree (skewProjective B).card hδ
  have hdq := SmallProjectiveArithmetic.three_degree_lt_order hsmall hd2
  obtain ⟨P, hPB, ell, hell, hPell, hrich⟩ :=
    StabilityTangents.exists_tangent_flag_with_margin B d (by exact_mod_cast hq) hB
      (by exact_mod_cast hd2) hsmall
  have hsingle : B.filter (fun Q => ProjectiveIncident Q ell) = {P} := by
    obtain ⟨Q, hQ⟩ := Finset.card_eq_one.mp ((StabilityTangents.mem_tangents B ell).mp hell)
    have hPQ : P = Q := by
      have hm : P ∈ B.filter (fun Q => ProjectiveIncident Q ell) :=
        Finset.mem_filter.mpr ⟨hPB, hPell⟩
      rw [hQ] at hm
      exact Finset.mem_singleton.mp hm
    simpa [hPQ] using hQ
  obtain ⟨e, U, heP, heell, heU, hUcard, hskew, htangent⟩ :=
    ProjectiveNormalization.exists_normalized_affine_set_with_tangents B P ell hsingle
  have hU : U.card ≤ Fintype.card F := by omega
  have hcodes : (StabilityPolynomial.nonverticalSkewCodes U).card =
      (skewProjective B).card := (card_nonvertical_skew_codes_explicit U).trans hskew
  have hempty : d < (Finset.univ.filter fun c : F => ∀ p ∈ U, p.1 ≠ c).card := by
    have ht : ((StabilityTangents.tangents B).filter (ProjectiveIncident P)).card =
        (Finset.univ.filter fun c : F => ∀ p ∈ U, p.1 ≠ c).card + 1 := by
      simpa only [StabilityTangents.tangents, Finset.filter_filter,
        and_comm] using htangent
    rw [ht] at hrich
    have hn : d + 1 < (Finset.univ.filter fun c : F => ∀ p ∈ U, p.1 ≠ c).card + 1 := by
      exact_mod_cast hrich
    omega
  obtain ⟨c, hc⟩ := StabilityPolynomial.normalized_prime_stability hprime U d hU
    (by rw [hcodes]; exact hdim) (by omega) (by simpa only using hempty)
  let m : ProjectiveLine F := some (none,c)
  let old : ProjectiveLine F := e.line.symm m
  have htransport : ((U.disjSum {none}).filter
      (fun Q => ProjectiveIncident Q m)).card =
        (B.filter (fun Q => ProjectiveIncident Q old)).card := by
    have ht := ProjectiveNormalization.card_filter_incident e B old
    simpa only [old, Equiv.apply_symm_apply, heU] using ht
  have hlarge : Fintype.card F - d ≤
      (B.filter (fun Q => ProjectiveIncident Q old)).card := by
    rw [← htransport]
    simpa only [m] using hc.trans (vertical_fiber_le_projective_section U c)
  refine ⟨old, small_projective_line_refinement B old hB ?_⟩
  exact SmallProjectiveArithmetic.half_line_of_degree_bound hdq hlarge

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_PrimeStabilityEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u

theorem primeStability_proof : PrimeStability.{u} := by
  apply primeStability_of_smallProjective
  intro F field finite dec hprime hq B hB hsmall
  have hdec : dec = Classical.decEq F := Subsingleton.elim _ _
  cases hdec
  exact small_projective_stability hprime hq B hB hsmall

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.KernelBridge

open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*}

variable [Field F] [Fintype F] [DecidableEq F]

theorem retained_tuple_injective (Q : RetentionRule F) (M : MergedPairs F)
    (g : Direction F) :
    Set.InjOn (fun c : ChoiceCode F => c.2) (↑(Q.candidates M g) : Set (ChoiceCode F)) := by
  intro c hc d hd htuple
  have vc := Q.valid M g c hc
  have vd := Q.valid M g d hd
  apply Q.uniqueLine M g c d hc hd
  apply Prod.ext (vc.1.trans vd.1.symm)
  have hp := vc.2.2.2.2.2.1 (0 : Fin 4)
  have hq := vd.2.2.2.2.2.1 (0 : Fin 4)
  change lineEval c.1.1 (tuplePoint M (decodeTuple c.2) 0) = c.1.2 at hp
  change lineEval d.1.1 (tuplePoint M (decodeTuple d.2) 0) = d.1.2 at hq
  have hcdir : c.1.1 = g := vc.1
  have hddir : d.1.1 = g := vd.1
  change c.2 = d.2 at htuple
  rw [hcdir, htuple] at hp
  rw [hddir] at hq
  exact hp.symm.trans hq

end
end Balanced.Local.KernelBridge

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalSelectedKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.KernelBridge

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem sum_transported_event (κ : SelectedDeletion.Kernel F) (M : MergedPairs F)
    (E : Output F → Prop) :
    (∑ v, if E v then transportedKernel κ M v else 0) =
      ∑ y, if E (encodeOutput M y) then κ M y else 0 := by
  rw [← Finset.sum_filter]
  unfold transportedKernel
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp

theorem transported_nonneg (κ : SelectedDeletion.Kernel F)
    (hκ : ∀ M y, 0 ≤ κ M y) : ∀ M v, 0 ≤ transportedKernel κ M v := by
  intro M v
  unfold transportedKernel
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact hκ M y
  · exact le_rfl

theorem exists_positive_preimage (κ : SelectedDeletion.Kernel F)
    (hκ : ∀ M y, 0 ≤ κ M y) {M : MergedPairs F} {v : Output F}
    (hv : 0 < transportedKernel κ M v) :
    ∃ y, encodeOutput M y = v ∧ 0 < κ M y := by
  unfold transportedKernel at hv
  obtain ⟨y, _, hy⟩ := (Finset.sum_pos_iff_of_nonneg (fun y _ => by
    split_ifs
    · exact hκ M y
    · exact le_rfl)).mp hv
  by_cases he : encodeOutput M y = v
  · exact ⟨y, he, by simpa [he] using hy⟩
  · simp [he] at hy

theorem canonical_choice_mem (M : MergedPairs F) (g : Direction F) (a : F)
    (h : ValidChoice M g (retainedChoice M (g, a))) :
    encodeChoice (retainedChoice M (g, a)) ∈ (canonicalRetention (F := F)).candidates M g := by
  apply Finset.mem_image.mpr
  refine ⟨(g, a), ?_, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, rfl, ?_⟩
  exact ⟨(retainedChoice M (g, a)).tuple, h⟩

theorem positive_outputs_tuple_eq
    (κ : SelectedDeletion.Kernel F) (c C : ℝ)
    (hκ : SelectedDeletion.IsExperiment κ c C) (M : MergedPairs F)
    (x y : SelectedDeletion.Output F) (hx : 0 < κ M x) (hy : 0 < κ M y)
    (s : Slot F) (heq : (encodeOutput M x s).2 = (encodeOutput M y s).2) :
    x s = y s := by
  have vx := (hκ.2.2.2 M x hx).1.2 s
  have vy := (hκ.2.2.2 M y hy).1.2 s
  have hc := retained_tuple_injective (canonicalRetention (F := F)) M s.1
    (canonical_choice_mem M s.1 (x s) vx)
    (canonical_choice_mem M s.1 (y s) vy) heq
  exact congrArg (fun z : ChoiceCode F => z.1.2) hc

theorem transported_cylinder_le
    (κ : SelectedDeletion.Kernel F) (c C K : ℝ) (hK : 0 ≤ K)
    (hκ : SelectedDeletion.IsExperiment κ c C)
    (hcyl : ∀ M (S : Finset (Slot F)) (a : SelectedDeletion.Output F),
      SelectedDeletion.fixedCylinderMass κ M S a ≤
        (K / Fintype.card F) ^ S.card)
    (M : MergedPairs F) (S : Finset (Slot F)) (t : Slot F → TupleCode F) :
    (∑ v, if ∀ s ∈ S, (v s).2 = t s then transportedKernel κ M v else 0) ≤
      (K / Fintype.card F) ^ S.card := by
  have hsum := sum_transported_event κ M (fun v => ∀ s ∈ S, (v s).2 = t s)
  have hsum' : (∑ v, if ∀ s ∈ S, (v s).2 = t s then transportedKernel κ M v else 0) =
      ∑ y, if ∀ s ∈ S, (encodeOutput M y s).2 = t s then κ M y else 0 := by
    convert hsum using 1
    · apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> rfl
    · apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> rfl
  rw [hsum']
  by_cases hex : ∃ y : SelectedDeletion.Output F,
      0 < κ M y ∧ ∀ s ∈ S, (encodeOutput M y s).2 = t s
  · obtain ⟨a, ha, hat⟩ := hex
    apply le_trans _ (hcyl M S a)
    unfold SelectedDeletion.fixedCylinderMass
    apply Finset.sum_le_sum
    intro y _
    by_cases hy : 0 < κ M y
    · by_cases ht : ∀ s ∈ S, (encodeOutput M y s).2 = t s
      · have hya : ∀ s ∈ S, y s = a s := by
          intro s hs
          exact positive_outputs_tuple_eq κ c C hκ M y a hy ha s
            ((ht s hs).trans (hat s hs).symm)
        split_ifs; try contradiction
        exact le_rfl
      · simp only [ht, ite_false]
        split_ifs
        · exact hκ.1 M y
        · exact le_rfl
    · have hz : κ M y = 0 := le_antisymm (le_of_not_gt hy) (hκ.1 M y)
      simp [hz]
  · have hz : (∑ y : SelectedDeletion.Output F,
        if ∀ s ∈ S, (encodeOutput M y s).2 = t s then κ M y else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro y _
      split_ifs with ht
      · exact le_antisymm (le_of_not_gt (fun hy => hex ⟨y, hy, ht⟩)) (hκ.1 M y)
      · rfl
    rw [hz]
    positivity

theorem transported_kernelConditions
    (κ : SelectedDeletion.Kernel F) (c C K : ℝ) (hK : 0 ≤ K)
    (hκ : SelectedDeletion.IsExperiment κ c C)
    (hcyl : ∀ M (S : Finset (Slot F)) (a : SelectedDeletion.Output F),
      SelectedDeletion.fixedCylinderMass κ M S a ≤
        (K / Fintype.card F) ^ S.card) :
    KernelConditions canonicalRetention (transportedKernel κ) K := by
  refine ⟨transported_nonneg κ hκ.1, ?_, ?_, transported_cylinder_le κ c C K hK hκ hcyl⟩
  · intro M
    have hs := sum_transported_event κ M (fun _ => True)
    have hs' : (∑ v, transportedKernel κ M v) = ∑ y, κ M y := by
      simpa using hs
    exact hs'.trans_le (hκ.2.1 M)
  · intro M v hv
    obtain ⟨y, rfl, hy⟩ := exists_positive_preimage κ hκ.1 hv
    have hvalid := hκ.2.2.2 M y hy
    have hgood : SelectedDeletion.InitialGood M c C := by
      by_contra hbad
      have hz := hκ.2.2.1 M hbad y
      linarith
    rw [configuration_encodeOutput]
    refine ⟨hvalid.1, hvalid.2, ?_, ?_⟩
    · intro s
      exact canonical_choice_mem M s.1 (y s) (hvalid.1.2 s)
    · intro p
      exact hgood.1.2.2.2.1 p

theorem original_offset_atom_real (M : MergedPairs F) :
    ((offsetLaw F) M).toReal = (Fintype.card (MergedPairs F) : ℝ)⁻¹ := by
  simp [offsetLaw]

theorem transported_probability_eq_jointMass (κ : SelectedDeletion.Kernel F)
    (E : Configuration F → Prop) :
    selectedProbability (transportedKernel κ) E =
      SelectedDeletion.jointMass κ (fun M y => E (SelectedDeletion.configuration M y)) := by
  have hinner : ∀ M : MergedPairs F,
      (∑ v : Output F, if E (configuration M v) then transportedKernel κ M v else 0) =
        ∑ y : SelectedDeletion.Output F,
          if E (SelectedDeletion.configuration M y) then κ M y else 0 := by
    intro M
    have hs := sum_transported_event κ M (fun v => E (configuration M v))
    simpa only [configuration_encodeOutput] using hs
  unfold selectedProbability SelectedDeletion.jointMass
  simp_rw [hinner, original_offset_atom_real]
  rw [← Finset.mul_sum]
  simp [div_eq_mul_inv, mul_comm]

end
end Balanced.Local.KernelBridge

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_DistinctRoleLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal Classical

namespace Balanced.DistinctRole

variable {D F : Type*} [Field F]

variable [Fintype D] [Fintype F]

instance distinctNonempty :
    Nonempty {M : D → Bool → F // ∀ d, M d false ≠ M d true} :=
  ⟨⟨fun _ b => if b then 0 else 1, by simp⟩⟩

end Balanced.DistinctRole

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_SizeThreshold
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

theorem eventually_size_condition (rho : ℝ) (hrho : 0 < rho) :
    ∀ᶠ q : ℕ in atTop,
      4 ≤ q ∧ 2 * (1 + (Nat.ceil (Real.log (q : ℝ)) : ℝ)) < rho * q := by
  have hlogReal : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ (rho / 4) * ‖x‖ :=
    Real.isLittleO_log_id_atTop.bound (by positivity)
  have hlog :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop) hlogReal
  have hlarge : ∀ᶠ q : ℕ in atTop, (8 / rho : ℝ) < q :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop)
      (eventually_gt_atTop (8 / rho))
  filter_upwards [hlog, hlarge, eventually_ge_atTop 4] with q hlog hlarge hq
  refine ⟨hq, ?_⟩
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hqnonneg : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hlognonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqone
  have hlogbound : Real.log (q : ℝ) ≤ (rho / 4) * q := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hlognonneg, abs_of_nonneg hqnonneg] using hlog
  have hceil : (Nat.ceil (Real.log (q : ℝ)) : ℝ) < Real.log (q : ℝ) + 1 :=
    Nat.ceil_lt_add_one hlognonneg
  have hrhoq : 8 < rho * (q : ℝ) := by
    have := (div_lt_iff₀ hrho).mp hlarge
    nlinarith
  nlinarith

theorem exists_size_threshold (rho : ℝ) (hrho : 0 < rho) :
    ∃ q0 : ℕ, ∀ q : ℕ, q0 ≤ q →
      4 ≤ q ∧ 2 * (1 + (Nat.ceil (Real.log (q : ℝ)) : ℝ)) < rho * q := by
  exact eventually_atTop.1 (eventually_size_condition rho hrho)

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PrimeConfigurationAssembly
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Filter
open scoped Topology

universe u

theorem balancedCounterexample_of_configuration
    (hdet : DeterministicReduction.{u})
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (C : Configuration F) (ρ : ℝ) (B : ℕ)
    (hq : 4 ≤ Fintype.card F) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hV : C.Valid) (hC : C.Compatible) (hO : C.Occupancy ρ B)
    (hCore : C.CoreConcentration ρ) (hLocal : C.LocalCondition)
    (hsize : 2 * (1 + (B : ℝ)) < ρ * Fintype.card F) :
    BalancedCounterexample (Fintype.card F) := by
  obtain ⟨H, hI, hN, hCover, _⟩ :=
    hdet F C ρ B hq hρ0 hρ1 hV hC hO hCore hLocal hsize
  exact ⟨H, hI, hN, hCover⟩

theorem mainResult_of_prime_configurations
    (hdet : DeterministicReduction.{0})
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (N : ℕ)
    (hconfiguration : ∀ (q : ℕ) (hq : q.Prime), N ≤ q →
      letI : Fact q.Prime := ⟨hq⟩
      ∃ C : Configuration (ZMod q),
        C.Valid ∧ C.Compatible ∧
        C.Occupancy ρ ⌈Real.log (q : ℝ)⌉₊ ∧
        C.CoreConcentration ρ ∧ C.LocalCondition) : MainResult := by
  obtain ⟨Nsize, hsize⟩ := exists_size_threshold ρ hρ0
  refine ⟨max N Nsize, ?_⟩
  intro q hq hprime
  let : Fact q.Prime := ⟨hprime⟩
  have hN : N ≤ q := (le_max_left N Nsize).trans hq
  have hNs : Nsize ≤ q := (le_max_right N Nsize).trans hq
  obtain ⟨C, hV, hC, hO, hCore, hLocal⟩ := hconfiguration q hprime hN
  obtain ⟨hfour, hlarge⟩ := hsize q hNs
  have hcard : Fintype.card (ZMod q) = q := ZMod.card q
  have h := balancedCounterexample_of_configuration hdet C ρ
    ⌈Real.log (q : ℝ)⌉₊ (by simpa only [hcard] using hfour) hρ0 hρ1
    hV hC hO hCore hLocal (by simpa only [hcard] using hlarge)
  simpa only [hcard] using h

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_SelectedJointAssembly
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty _root_.OAI.Balanced.instDecidableProjectiveIncident
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.SelectedJointAssembly

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem offset_real_mass :
    ∑ M : MergedPairs F, ((offsetLaw F) M).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun M _ => (offsetLaw F).apply_ne_top M)]
  have h : ∑ M : MergedPairs F, (offsetLaw F) M = 1 := by
    simpa only [tsum_fintype] using (offsetLaw F).tsum_coe
  rw [h, ENNReal.toReal_one]

theorem successMass_le_one (κ : SelectedDeletion.Kernel F)
    (hsub : ∀ M, ∑ s, κ M s ≤ 1) : SelectedDeletion.successMass κ ≤ 1 := by
  unfold SelectedDeletion.successMass SelectedDeletion.jointMass
  simp only [ite_true, if_true, ↓reduceIte]
  calc
    (∑ M, ((offsetLaw F) M).toReal * ∑ s, κ M s) ≤
        ∑ M, ((offsetLaw F) M).toReal * 1 :=
      Finset.sum_le_sum (fun M _ => mul_le_mul_of_nonneg_left (hsub M) ENNReal.toReal_nonneg)
    _ = 1 := by simp only [mul_one, offset_real_mass]

theorem successMass_le_three_errors (κ : SelectedDeletion.Kernel F)
    (hnonneg : ∀ M s, 0 ≤ κ M s)
    (E₁ E₂ E₃ : MergedPairs F → SelectedDeletion.Output F → Prop)
    (hcover : ∀ M s, 0 < κ M s → E₁ M s ∨ E₂ M s ∨ E₃ M s) :
    SelectedDeletion.successMass κ ≤ SelectedDeletion.jointMass κ E₁ +
      SelectedDeletion.jointMass κ E₂ + SelectedDeletion.jointMass κ E₃ := by
  have hpoint (M : MergedPairs F) (s : SelectedDeletion.Output F) :
      κ M s ≤ (if E₁ M s then κ M s else 0) +
        (if E₂ M s then κ M s else 0) + (if E₃ M s then κ M s else 0) := by
    by_cases hpos : 0 < κ M s
    · rcases hcover M s hpos with h₁ | h₂ | h₃
      all_goals split_ifs <;> linarith [hnonneg M s]
    · have hz : κ M s = 0 := le_antisymm (le_of_not_gt hpos) (hnonneg M s)
      simp only [hz, ite_self, add_zero, le_refl]
  unfold SelectedDeletion.successMass SelectedDeletion.jointMass
  simp only [ite_true, if_true, ↓reduceIte]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro M _
  rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun s _ => hpoint M s))
    ENNReal.toReal_nonneg

theorem exists_positive_output_avoiding_three (κ : SelectedDeletion.Kernel F)
    (hnonneg : ∀ M s, 0 ≤ κ M s)
    (E₁ E₂ E₃ : MergedPairs F → SelectedDeletion.Output F → Prop)
    (hsmall : SelectedDeletion.jointMass κ E₁ + SelectedDeletion.jointMass κ E₂ +
      SelectedDeletion.jointMass κ E₃ < SelectedDeletion.successMass κ) :
    ∃ M s, 0 < κ M s ∧ ¬ E₁ M s ∧ ¬ E₂ M s ∧ ¬ E₃ M s := by
  by_contra hn
  have hcover : ∀ M s, 0 < κ M s → E₁ M s ∨ E₂ M s ∨ E₃ M s := by
    intro M s hpos
    by_cases h₁ : E₁ M s
    · exact Or.inl h₁
    by_cases h₂ : E₂ M s
    · exact Or.inr (Or.inl h₂)
    by_cases h₃ : E₃ M s
    · exact Or.inr (Or.inr h₃)
    exact False.elim (hn ⟨M, s, hpos, h₁, h₂, h₃⟩)
  exact (not_le_of_gt hsmall) (successMass_le_three_errors κ hnonneg E₁ E₂ E₃ hcover)

theorem coreConcentration_iff_pencilEvent (C : Configuration F) (ρ : ℝ) :
    C.CoreConcentration ρ ↔ CorePencilEvent (ρ / 4) C.deletedLines := by
  have hcore : uncoveredPoints C.deletedLines = C.core := by
    ext p
    simp only [uncoveredPoints, Configuration.core, Finset.mem_filter]
  unfold Configuration.CoreConcentration CorePencilEvent
  rw [hcore]
  constructor
  · intro h L hdisj hcard hcover
    exact h L (fun l hl hdel => Finset.disjoint_left.mp hdisj hl hdel) hcard hcover
  · intro h L hav hcard hcover
    exact h L (Finset.disjoint_left.mpr hav) hcard hcover

theorem exists_configuration_of_joint_errors
    (κ : SelectedDeletion.Kernel F) {c Cbound ρ : ℝ}
    (hexp : SelectedDeletion.IsExperiment κ c Cbound)
    (hsmall : SelectedDeletion.occupancyFailureMass κ ρ +
      SelectedDeletion.jointMass κ (fun M s =>
        ¬ (SelectedDeletion.configuration M s).CoreConcentration ρ) +
      SelectedDeletion.jointMass κ (fun M s =>
        ¬ (SelectedDeletion.configuration M s).LocalCondition) <
      SelectedDeletion.successMass κ) :
    ∃ C : Configuration F, C.Valid ∧ C.Compatible ∧
      C.Occupancy ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊ ∧
      C.CoreConcentration ρ ∧ C.LocalCondition := by
  obtain ⟨M, s, hpos, hO, hCore, hLocal⟩ := exists_positive_output_avoiding_three
    κ hexp.1 _ _ _ hsmall
  have hv := hexp.2.2.2 M s hpos
  exact ⟨SelectedDeletion.configuration M s, hv.1, hv.2,
    not_not.mp hO, not_not.mp hCore, not_not.mp hLocal⟩

end
end Balanced.SelectedJointAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_MainAssembly
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Filter
open scoped Topology

noncomputable section
open scoped Classical

theorem selectedLocalTransport_proof : SelectedLocalTransport := by
  intro F _ _ _ κ c C K hK hexp hcyl
  refine ⟨Local.KernelBridge.canonicalRetention,
    Local.KernelBridge.transportedKernel κ, ?_, ?_⟩
  · exact Local.KernelBridge.transported_kernelConditions κ c C K hK hexp hcyl
  · exact Local.KernelBridge.transported_probability_eq_jointMass κ

theorem selectedCoreTransport_proof : SelectedCoreTransport := by
  intro F _ _ _ κ c C Q hexp hreal hpos E
  exact SelectedDeletion.jointMass_eq_success_mul_eventProbability hexp hpos Q hreal E

theorem mainResult_of_selected_results_and_transports
    (hdet : DeterministicReduction.{0})
    (hselected : SelectedDeletionResult.{0})
    (hcore : CorePencilResult.{0}) (hlocal : Local.PencilLocalResult.{0})
    (hLocalTransport : SelectedLocalTransport)
    (hCoreTransport : SelectedCoreTransport) : MainResult := by
  obtain ⟨c, Cbound, K, ρ, a₀, C₀, ε, N,
    hc, hC, hK, hρ0, hρ1, ha₀, hC₀, hNfour, hεnonneg, hεlim, hkernel⟩ := hselected
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  obtain ⟨εL, hεLlim, hεLnonneg, NL, hlocalBound⟩ := hlocal K hKpos
  have htol : 0 < a₀ / 4 := by positivity
  obtain ⟨NC, hcoreBound⟩ := hcore 3 (by norm_num) C₀ hC₀.le (ρ / 4)
    (by positivity) (a₀ / 4) htol
  obtain ⟨NE, hE⟩ := eventually_atTop.1 (hεlim.eventually_lt_const htol)
  obtain ⟨NEL, hEL⟩ := eventually_atTop.1 (hεLlim.eventually_lt_const htol)
  let Nall := max N (max NL (max NC (max NE NEL)))
  apply mainResult_of_prime_configurations hdet ρ hρ0 hρ1 Nall
  intro q hprime hlarge
  let : Fact q.Prime := ⟨hprime⟩
  have hNq : N ≤ q := (le_max_left N _).trans hlarge
  have hNLq : NL ≤ q := by dsimp [Nall] at hlarge; omega
  have hNCq : NC ≤ q := by dsimp [Nall] at hlarge; omega
  have hNEq : NE ≤ q := by dsimp [Nall] at hlarge; omega
  have hNELq : NEL ≤ q := by dsimp [Nall] at hlarge; omega
  have hcard : Fintype.card (ZMod q) = q := ZMod.card q
  obtain ⟨κ, hexp, _, hcylinder, hsuccess, hoccupancy, Q, hreal, hdom⟩ :=
    hkernel (ZMod q) (by simpa only [hcard] using hNq)
  have hsuccesspos : 0 < SelectedDeletion.successMass κ := ha₀.trans_le hsuccess
  have hsuccessone : SelectedDeletion.successMass κ ≤ 1 :=
    SelectedJointAssembly.successMass_le_one κ hexp.2.1
  obtain ⟨R, w, hw, hevent⟩ := hLocalTransport (ZMod q) κ c Cbound K hKpos.le hexp hcylinder
  have hlocalError := hlocalBound (ZMod q) (by simpa only [hcard] using hNLq) R w hw
  rw [hevent] at hlocalError
  have hcoreError := hcoreBound (ZMod q) (by simpa only [hcard] using hprime)
    (by simpa only [hcard] using hNCq)
    (by rw [hcard]; omega) Q hdom
  have hcoreIdentity := hCoreTransport (ZMod q) κ c Cbound Q hexp hreal hsuccesspos
    (fun D => ¬ CorePencilEvent (ρ / 4) D)
  have hcoreIdentity' :
      SelectedDeletion.jointMass κ (fun M s =>
        ¬ (SelectedDeletion.configuration M s).CoreConcentration ρ) =
      SelectedDeletion.successMass κ *
        deletionEventProbability Q (fun D => ¬ CorePencilEvent (ρ / 4) D.val) := by
    simpa only [SelectedJointAssembly.coreConcentration_iff_pencilEvent] using hcoreIdentity
  have hprobNonneg : 0 ≤
      deletionEventProbability Q (fun D => ¬ CorePencilEvent (ρ / 4) D.val) := by
    unfold deletionEventProbability
    apply Finset.sum_nonneg
    intro D _
    split_ifs
    · exact ENNReal.toReal_nonneg
    · exact le_rfl
  have hjointCore : SelectedDeletion.jointMass κ (fun M s =>
      ¬ (SelectedDeletion.configuration M s).CoreConcentration ρ) < a₀ / 4 := by
    rw [hcoreIdentity']
    calc
      _ ≤ 1 * deletionEventProbability Q
          (fun D => ¬ CorePencilEvent (ρ / 4) D.val) :=
        mul_le_mul_of_nonneg_right hsuccessone hprobNonneg
      _ < a₀ / 4 := by simpa only [one_mul] using hcoreError
  have hsmallO : SelectedDeletion.occupancyFailureMass κ ρ < a₀ / 4 := by
    exact hoccupancy.trans_lt (by simpa only [hcard] using hE q hNEq)
  have hsmallL : SelectedDeletion.jointMass κ (fun M s =>
      ¬ (SelectedDeletion.configuration M s).LocalCondition) < a₀ / 4 := by
    exact hlocalError.trans_lt (by simpa only [hcard] using hEL q hNELq)
  obtain ⟨C, hV, hCompat, hO, hConcentration, hLoc⟩ :=
    SelectedJointAssembly.exists_configuration_of_joint_errors κ hexp
      (by linarith)
  exact ⟨C, hV, hCompat, by simpa only [hcard] using hO, hConcentration, hLoc⟩

end

theorem mainResult_of_selectedDeletion_corePencil_local_deterministic
    (hdet : DeterministicReduction.{0})
    (hselected : SelectedDeletionResult.{0})
    (hcore : CorePencilResult.{0}) (hlocal : Local.PencilLocalResult.{0}) :
    MainResult :=
  mainResult_of_selected_results_and_transports hdet hselected hcore hlocal
    selectedLocalTransport_proof selectedCoreTransport_proof

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternExposureBoundary
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced.PatternModel

variable (P : PatternModel)

@[simp] theorem count_eq_zero_of_isEmpty [IsEmpty P.Label] (ω : P.Sample) :
    P.count ω = 0 := by
  simp [count]

end Balanced.PatternModel

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Results
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w

open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced

theorem prime_stability : PrimeStability.{u} := primeStability_proof

theorem core_pencil : CorePencilResult.{u} :=
  corePencilResult_of_robustDeletion_primeStability robust_deletion prime_stability

theorem main_result_oai : MainResult :=
  mainResult_of_selectedDeletion_corePencil_local_deterministic
    deterministic_reduction deletion_domination core_pencil pencil_local

end Balanced

end OAI
end

theorem solution : type_of% @OAI.Balanced.main_result_oai := @OAI.Balanced.main_result_oai
