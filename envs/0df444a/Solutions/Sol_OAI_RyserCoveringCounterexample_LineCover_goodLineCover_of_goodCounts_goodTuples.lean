-- Prove2me | solution 1 for OAI.RyserCoveringCounterexample.LineCover.goodLineCover_of_goodCounts_goodTuples
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T04:30:08.519162+00:00
-- url     : https://prove2.me/submissions/9cab3383-0307-4e9f-bcb5-fc53094a6742

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIW2RY002
import Theorems.Thm_OAI_RyserCoveringCounterexample_Incidence_uniform_incidence_bound

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_AffineJoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

section Join

variable [DecidableEq F]

theorem eq_joinLine_of_incidence {p q : Point F} {l : AffineLine F}
    (hpq : p ≠ q) (hpl : Incidence p l) (hql : Incidence q l) :
    l = joinLine p q :=
  line_eq_of_two_incident_points hpq hpl hql
    (incidence_joinLine_left p q) (incidence_joinLine_right p q)

theorem existsUnique_lineThrough_pair {p q : Point F} (hpq : p ≠ q) :
    ∃! l : AffineLine F, Incidence p l ∧ Incidence q l := by
  refine ⟨joinLine p q, ⟨incidence_joinLine_left p q,
    incidence_joinLine_right p q⟩, ?_⟩
  intro l hl
  exact eq_joinLine_of_incidence hpq hl.1 hl.2

end Join

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_ProjectiveJoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

theorem existsUnique_projectiveLine_of_ne {p q : ProjectivePoint F}
    (hpq : p ≠ q) :
    ∃! l : ProjectiveLine F, ProjectiveIncidence p l ∧ ProjectiveIncidence q l := by
  classical
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      have hpq' : p ≠ q := fun h => hpq (congrArg Sum.inl h)
      obtain ⟨l, hl, huniq⟩ := existsUnique_lineThrough_pair hpq'
      refine ⟨some l, hl, ?_⟩
      intro m hm
      cases m with
      | none => exact hm.1.elim
      | some m => exact congrArg some (huniq m hm)
    | inr d =>
      refine ⟨some (lineThrough d p), ⟨rfl, rfl⟩, ?_⟩
      intro m hm
      cases m with
      | none => exact hm.1.elim
      | some m =>
        apply congrArg some
        exact line_eq_of_direction_eq_of_incidence hm.2.symm hm.1 rfl
  | inr d =>
    cases q with
    | inl q =>
      refine ⟨some (lineThrough d q), ⟨rfl, rfl⟩, ?_⟩
      intro m hm
      cases m with
      | none => exact hm.2.elim
      | some m =>
        apply congrArg some
        exact line_eq_of_direction_eq_of_incidence hm.1.symm hm.2 rfl
    | inr e =>
      refine ⟨none, ⟨trivial, trivial⟩, ?_⟩
      intro m hm
      cases m with
      | none => rfl
      | some m =>
        have hde : d = e := hm.1.trans hm.2.symm
        exact (hpq (congrArg Sum.inr hde)).elim

theorem eq_projectiveLine_of_common_incidence
    {p q : ProjectivePoint F} {l m : ProjectiveLine F}
    (hpq : p ≠ q)
    (hpl : ProjectiveIncidence p l) (hql : ProjectiveIncidence q l)
    (hpm : ProjectiveIncidence p m) (hqm : ProjectiveIncidence q m) : l = m := by
  obtain ⟨k, _, huniq⟩ := existsUnique_projectiveLine_of_ne hpq
  exact (huniq l ⟨hpl, hql⟩).trans (huniq m ⟨hpm, hqm⟩).symm

theorem eq_projectivePoint_of_common_incidence
    {l m : ProjectiveLine F} {p q : ProjectivePoint F}
    (hlm : l ≠ m)
    (hpl : ProjectiveIncidence p l) (hpm : ProjectiveIncidence p m)
    (hql : ProjectiveIncidence q l) (hqm : ProjectiveIncidence q m) : p = q := by
  obtain ⟨x, _, huniq⟩ := existsUnique_projectivePoint_of_ne hlm
  exact (huniq p ⟨hpl, hpm⟩).trans (huniq q ⟨hql, hqm⟩).symm

theorem eq_affineLine_of_common_projective_incidence
    {p q : ProjectivePoint F} {l m : AffineLine F}
    (hpq : p ≠ q)
    (hpl : ProjectiveIncidence p (some l))
    (hql : ProjectiveIncidence q (some l))
    (hpm : ProjectiveIncidence p (some m))
    (hqm : ProjectiveIncidence q (some m)) : l = m :=
  Option.some.inj (eq_projectiveLine_of_common_incidence hpq hpl hql hpm hqm)

theorem ne_of_projectiveIncidence_of_not_projectiveIncidence
    {p q : ProjectivePoint F} {l : ProjectiveLine F}
    (hpl : ProjectiveIncidence p l) (hql : ¬ ProjectiveIncidence q l) : p ≠ q := by
  intro hpq
  exact hql (hpq ▸ hpl)

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_Overlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {P Λ : Type*} [instDecidableEqP : DecidableEq P] [instDecidableEqΛ : DecidableEq Λ]

theorem incidence_double_count (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) :
    (∑ l ∈ L, (X.filter fun x => I x l).card) =
      ∑ x ∈ X, multiplicity I L x := let _ := instDecidableEqP; let _ := instDecidableEqΛ; by
  simp only [multiplicity, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

theorem sum_multiplicity_eq_covered_add_excess
    (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) :
    (∑ x ∈ X, multiplicity I L x) =
      (coveredPoints I X L).card + overlapExcess I X L := let _ := instDecidableEqP; let _ := instDecidableEqΛ; by
  calc
    _ = ∑ x ∈ X, ((if 0 < multiplicity I L x then 1 else 0) +
        (multiplicity I L x - 1)) := by
      apply Finset.sum_congr rfl
      intro x hx
      cases h : multiplicity I L x with
      | zero => simp
      | succ n => simp [Nat.add_comm]
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_boole]
      rfl

theorem incidence_eq_covered_add_excess
    (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) :
    (∑ l ∈ L, (X.filter fun x => I x l).card) =
      (coveredPoints I X L).card + overlapExcess I X L := by
  rw [incidence_double_count, sum_multiplicity_eq_covered_add_excess]

theorem covered_add_uncovered_card
    (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) :
    (coveredPoints I X L).card + (X \ coveredPoints I X L).card = X.card := let _ := instDecidableEqΛ; by
  rw [Nat.add_comm]
  exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)

theorem cover_count_bounds
    (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ)
    (d q e0 e1 b δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ d) (hq : 0 < q) (he1 : 0 ≤ e1)
    (hsize : d * q ^ 2 - e0 ≤ (X.card : ℝ))
    (hline : ∀ l ∈ L, ((X.filter fun x => I x l).card : ℝ) ≤ d * q + e1)
    (huncovered : ((X \ coveredPoints I X L).card : ℝ) ≤ b)
    (hcard : (L.card : ℝ) ≤ q) :
    (overlapExcess I X L : ℝ) ≤ e0 + q * e1 + b ∧
      q - (L.card : ℝ) ≤ (e0 + q * e1 + b) / (δ * q) := by
  let N : ℝ := X.card
  let M : ℝ := L.card
  let C : ℝ := (coveredPoints I X L).card
  let U : ℝ := (X \ coveredPoints I X L).card
  let E : ℝ := overlapExcess I X L
  let J : ℝ := ∑ l ∈ L, ((X.filter fun x => I x l).card : ℝ)
  have hcount : J = C + E := by
    dsimp [J, C, E]
    exact_mod_cast incidence_eq_covered_add_excess I X L
  have hpartition : C + U = N := by
    dsimp [C, U, N]
    exact_mod_cast covered_add_uncovered_card I X L
  have hupper : J ≤ M * (d * q + e1) := by
    calc
      J ≤ ∑ _l ∈ L, (d * q + e1) := Finset.sum_le_sum hline
      _ = _ := by simp [M, mul_add]
  have hcap : 0 ≤ d * q + e1 :=
    add_nonneg (mul_nonneg (hδ.le.trans hd) hq.le) he1
  have hupperQ := hupper.trans (mul_le_mul_of_nonneg_right hcard hcap)
  have hE0 : 0 ≤ E := Nat.cast_nonneg _
  have hmerr : M * e1 ≤ q * e1 := mul_le_mul_of_nonneg_right hcard he1
  have hN : d * q ^ 2 - e0 ≤ N := hsize
  have hU : U ≤ b := huncovered
  have hM : M ≤ q := hcard
  have hEbound : E ≤ e0 + q * e1 + b := by
    nlinarith [hupperQ, hcount, hpartition, hN, hU]
  have hgap : d * q * (q - M) ≤ e0 + q * e1 + b := by
    nlinarith [hupper, hcount, hpartition, hN, hU, hE0, hmerr]
  have hscale : δ * q * (q - M) ≤ d * q * (q - M) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd hq.le)
      (sub_nonneg.mpr hM)
  refine ⟨hEbound, ?_⟩
  apply (le_div_iff₀ (mul_pos hδ hq)).2
  simpa only [mul_comm] using hscale.trans hgap

theorem heavyPoints_card_mul_le_excess
    (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) (T : ℝ) (hT : 1 < T) :
    ((heavyPoints I X L T).card : ℝ) * (T - 1) ≤ (overlapExcess I X L : ℝ) := let _ := instDecidableEqP; let _ := instDecidableEqΛ; by
  have hsum : (∑ x ∈ X, ((multiplicity I L x - 1 : ℕ) : ℝ)) =
      (overlapExcess I X L : ℝ) := by simp only [overlapExcess, Nat.cast_sum]
  rw [← hsum]
  calc
    _ = ∑ _x ∈ heavyPoints I X L T, (T - 1) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ heavyPoints I X L T, ((multiplicity I L x - 1 : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      have hxT : T ≤ (multiplicity I L x : ℝ) := (Finset.mem_filter.mp hx).2
      have hnR : (1 : ℝ) ≤ multiplicity I L x := hT.le.trans hxT
      have hn : 1 ≤ multiplicity I L x := by exact_mod_cast hnR
      rw [Nat.cast_sub hn, Nat.cast_one]
      exact sub_le_sub_right hxT 1
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (by intro x hx hxnot; exact Nat.cast_nonneg _)

theorem orderedPairMass_le_light_add_heavy
    (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) (T R : ℝ)
    (hT : 0 ≤ T) (hR : ∀ x ∈ X, (multiplicity I L x : ℝ) ≤ R) :
    (orderedPairMass I X L : ℝ) ≤ T * (overlapExcess I X L : ℝ) +
      R * ∑ x ∈ heavyPoints I X L T, (multiplicity I L x : ℝ) := let _ := instDecidableEqP; let _ := instDecidableEqΛ; by
  have hpoint (x : P) (hx : x ∈ X) :
      (multiplicity I L x : ℝ) * ((multiplicity I L x - 1 : ℕ) : ℝ) ≤
        T * ((multiplicity I L x - 1 : ℕ) : ℝ) +
          if T ≤ (multiplicity I L x : ℝ) then R * (multiplicity I L x : ℝ) else 0 := by
    have ha0 : 0 ≤ ((multiplicity I L x - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hn0 : 0 ≤ (multiplicity I L x : ℝ) := Nat.cast_nonneg _
    have haN : ((multiplicity I L x - 1 : ℕ) : ℝ) ≤ (multiplicity I L x : ℝ) := by
      exact_mod_cast Nat.sub_le (multiplicity I L x) 1
    by_cases hh : T ≤ (multiplicity I L x : ℝ)
    · simp only [ite_eq_left hh]
      have hp := mul_le_mul_of_nonneg_left (haN.trans (hR x hx)) hn0
      nlinarith [mul_nonneg hT ha0]
    · simpa only [ite_eq_right hh, add_zero] using
        mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hh)) ha0
  have hsum := Finset.sum_le_sum hpoint
  simpa only [orderedPairMass, overlapExcess, heavyPoints, Nat.cast_sum,
    Nat.cast_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_filter,
    mul_ite, mul_zero] using hsum

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open scoped Classical

variable {F : Type*} [instFieldF : Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F]

theorem coverPencil_subset (L : Finset (AffineLine F)) (p : ProjectivePoint F) :
    coverPencil L p ⊆ L := let _ := instFintypeF; Finset.filter_subset _ _

theorem left_ne_right {t : ℕ} (a : LineTuple F t) (i j : Fin t) :
    a (Sum.inl i) ≠ a (Sum.inr j) := let _ := instFieldF; let _ := instFintypeF; let _ := instDecidableEqF; by
  intro h
  cases a.injective h

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_DeletionDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {P : Type*} [DecidableEq P]

variable {shapes : Finset (Finset P)} {D n : ℕ}

variable [instFintypeP : Fintype P]

theorem mem_survivors_active {ignore : Finset (Finset P)}
    {ω : Fin n → Outcome shapes D} {x : P} :
    x ∈ survivors ignore ω ↔ ∀ L ∈ selected ω \ ignore, x ∉ L := by
  rw [mem_survivors]
  constructor
  · intro h L hL hxL
    rcases Finset.mem_sdiff.mp hL with ⟨hsel, hI⟩
    rcases mem_selected.mp hsel with ⟨i, s, hs, rfl⟩
    exact h i (mem_deleted.mpr ⟨s, hs, hI, hxL⟩)
  · intro h i hx
    rcases mem_deleted.mp hx with ⟨s, hs, hI, hxs⟩
    exact h s.val (Finset.mem_sdiff.mpr
      ⟨mem_selected.mpr ⟨i, s, hs, rfl⟩, hI⟩) hxs

theorem survivors_insert_eq_of_not_selected
    {ignore : Finset (Finset P)} {ω : Fin n → Outcome shapes D}
    {L : Finset P} (hL : L ∉ selected ω) :
    survivors (insert L ignore) ω = survivors ignore ω := by
  ext x
  rw [mem_survivors_active, mem_survivors_active,
    Finset.sdiff_insert_of_notMem hL ignore]

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Probability_Finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample

namespace FiniteLaw

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem expectation_smul (μ : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    μ.expectation (fun ω => c * f ω) = c * μ.expectation f := by
  simp [expectation, Finset.mul_sum, mul_left_comm]

theorem prob_mono (μ : FiniteLaw Ω) {P Q : Ω → Prop} (hPQ : ∀ ω, P ω → Q ω) :
    μ.prob P ≤ μ.prob Q := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : P ω
  · simp [hp, hPQ ω hp]
  · by_cases hq : Q ω <;> simp [hp, hq, μ.nonneg ω]

theorem prob_union_le (μ : FiniteLaw Ω) (P Q : Ω → Prop) :
    μ.prob (fun ω => P ω ∨ Q ω) ≤ μ.prob P + μ.prob Q := by
  classical
  rw [prob, prob, prob, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp, hq, μ.nonneg]

theorem prob_ge_le_expectation_div (μ : FiniteLaw Ω) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) {t : ℝ} (ht : 0 < t) :
    μ.prob (fun ω => t ≤ f ω) ≤ μ.expectation f / t := by
  have h := μ.prob_le_expectation (fun ω => t ≤ f ω) (fun ω => t⁻¹ * f ω)
    (fun ω => mul_nonneg (inv_nonneg.mpr ht.le) (hf ω))
    (fun ω hω => by simpa [ht.ne'] using mul_le_mul_of_nonneg_left hω (inv_nonneg.mpr ht.le))
  rw [expectation_smul] at h
  simpa [div_eq_mul_inv, mul_comm] using h

theorem expectation_prod (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (f : Ω × Γ → ℝ) :
    (μ.prod ν).expectation f = μ.expectation (fun ω => ν.expectation (fun γ => f (ω, γ))) := by
  simp [expectation, prod, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem eq_uniform_of_weight_eq [Nonempty Ω] (mu : FiniteLaw Ω)
    (h : ∀ x y, mu.weight x = mu.weight y) : mu = uniform Ω := by
  apply ext_weight
  funext x
  change mu.weight x = (Fintype.card Ω : ℝ)⁻¹
  have hN : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : (Fintype.card Ω : ℝ) * mu.weight x = 1 := by
    calc
      _ = ∑ y : Ω, mu.weight x := by simp
      _ = ∑ y : Ω, mu.weight y :=
        Finset.sum_congr rfl (fun y _ => (h y x).symm)
      _ = 1 := mu.total
  calc
    mu.weight x = (Fintype.card Ω : ℝ)⁻¹ *
        ((Fintype.card Ω : ℝ) * mu.weight x) := by
      rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]
    _ = (Fintype.card Ω : ℝ)⁻¹ := by rw [hsum, mul_one]

end FiniteLaw

end RyserCoveringCounterexample

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Probability_Product
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.FiniteLaw

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem map_weight_eq_prob (μ : FiniteLaw Ω) (f : Ω → Γ) (γ : Γ) :
    (map μ f).weight γ = μ.prob (fun ω => f ω = γ) := rfl

theorem map_uniform_of_fiber_card_eq [Nonempty Ω] [Nonempty Γ] (f : Ω → Γ)
    (hfiber : ∀ y z : Γ,
      Nat.card {x : Ω // f x = y} = Nat.card {x : Ω // f x = z}) :
    (uniform Ω).map f = uniform Γ := by
  classical
  apply eq_uniform_of_weight_eq
  intro y z
  rw [map_weight_eq_prob, map_weight_eq_prob, uniform_prob, uniform_prob]
  have hc : (Finset.univ.filter (fun x : Ω => f x = y)).card =
      (Finset.univ.filter (fun x : Ω => f x = z)).card := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hfiber y z
  rw [hc]

theorem uniform_prod (Ω Γ : Type*) [Fintype Ω] [Fintype Γ]
    [Nonempty Ω] [Nonempty Γ] :
    uniform (Ω × Γ) = (uniform Ω).prod (uniform Γ) :=
  (eq_uniform_of_weight_eq ((uniform Ω).prod (uniform Γ)) (fun _ _ => rfl)).symm

theorem prob_prod_average (mu : FiniteLaw Ω) (nu : FiniteLaw Γ)
    (P : Ω × Γ → Prop) :
    (mu.prod nu).prob P = mu.expectation (fun x => nu.prob (fun y => P (x, y))) := by
  simp only [prob_eq_expectation]
  exact expectation_prod mu nu (fun z => if P z then 1 else 0)

end RyserCoveringCounterexample.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_CleanCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {shapes : Finset (Finset (Point F))} {D n : ℕ}

theorem cleanLines_subset (ω : Fin n → Outcome shapes D) (L : Finset (AffineLine F)) :
    cleanLines ω L ⊆ L := Finset.filter_subset _ _

theorem cleanLines_not_selected {ω : Fin n → Outcome shapes D}
    {L : Finset (AffineLine F)} {l : AffineLine F} (hl : l ∈ cleanLines ω L) :
    linePoints l ∉ selected ω := (Finset.mem_filter.mp hl).2

theorem survivor_incidence_not_selected {ω : Fin n → Outcome shapes D}
    {x : Point F} {l : AffineLine F} (hx : x ∈ survivors ∅ ω)
    (hl : Incidence x l) : linePoints l ∉ selected ω := by
  intro hs
  have hactive : linePoints l ∈ selected ω \ ∅ := by simpa using hs
  exact mem_survivors_active.mp hx (linePoints l) hactive ((mem_linePoints x l).mpr hl)

theorem survivors_inter_cleanLines (ω : Fin n → Outcome shapes D)
    (L : Finset (AffineLine F)) :
    survivors ∅ ω ∩ L.biUnion linePoints =
      survivors ∅ ω ∩ (cleanLines ω L).biUnion linePoints := by
  ext x
  constructor
  · intro hx
    obtain ⟨hs, hc⟩ := Finset.mem_inter.mp hx
    obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_inter.mpr ⟨hs, Finset.mem_biUnion.mpr
      ⟨l, Finset.mem_filter.mpr ⟨hl, survivor_incidence_not_selected hs
        ((mem_linePoints x l).mp hxl)⟩, hxl⟩⟩
  · intro hx
    obtain ⟨hs, hc⟩ := Finset.mem_inter.mp hx
    obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_inter.mpr ⟨hs,
      Finset.mem_biUnion.mpr ⟨l, cleanLines_subset ω L hl, hxl⟩⟩

theorem survivors_sdiff_cleanLines (ω : Fin n → Outcome shapes D)
    (L : Finset (AffineLine F)) :
    survivors ∅ ω \ L.biUnion linePoints =
      survivors ∅ ω \ (cleanLines ω L).biUnion linePoints := by
  ext x
  constructor
  · intro hx
    obtain ⟨hs, hc⟩ := Finset.mem_sdiff.mp hx
    refine Finset.mem_sdiff.mpr ⟨hs, ?_⟩
    intro hclean
    obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp hclean
    exact hc (Finset.mem_biUnion.mpr ⟨l, cleanLines_subset ω L hl, hxl⟩)
  · intro hx
    obtain ⟨hs, hc⟩ := Finset.mem_sdiff.mp hx
    refine Finset.mem_sdiff.mpr ⟨hs, ?_⟩
    intro horig
    have hboth := Finset.mem_inter.mpr ⟨hs, horig⟩
    rw [survivors_inter_cleanLines] at hboth
    exact hc (Finset.mem_inter.mp hboth).2

theorem coverPencil_mono {L K : Finset (AffineLine F)} (h : L ⊆ K)
    (p : ProjectivePoint F) : coverPencil L p ⊆ coverPencil K p := by
  intro l hl
  obtain ⟨hL, hi⟩ := (mem_coverPencil L p l).mp hl
  exact (mem_coverPencil K p l).mpr ⟨h hL, hi⟩

theorem coveredPoints_eq_inter_biUnion (X : Finset (Point F))
    (L : Finset (AffineLine F)) :
    coveredPoints Incidence X L = X ∩ L.biUnion linePoints := by
  ext x
  change x ∈ X.filter (fun x => 0 < multiplicity Incidence L x) ↔ _
  rw [Finset.mem_filter, Finset.mem_inter]
  unfold multiplicity
  have hfilter :
      @Finset.filter _ (Incidence x) (fun l => Classical.propDecidable (Incidence x l)) L =
        L.filter (Incidence x) := Finset.filter_congr_decidable _ _ _
  rw [hfilter]
  constructor
  · rintro ⟨hx, hn⟩
    obtain ⟨l, hl⟩ := Finset.card_pos.mp hn
    obtain ⟨hL, hi⟩ := Finset.mem_filter.mp hl
    exact ⟨hx, Finset.mem_biUnion.mpr ⟨l, hL, (mem_linePoints x l).mpr hi⟩⟩
  · rintro ⟨hx, hl⟩
    obtain ⟨l, hL, hi⟩ := Finset.mem_biUnion.mp hl
    exact ⟨hx, Finset.card_pos.mpr ⟨l,
      Finset.mem_filter.mpr ⟨hL, (mem_linePoints x l).mp hi⟩⟩⟩

theorem survivors_ignore_tuple_eq {t : ℕ} (ω : Fin n → Outcome shapes D)
    (a : LineTuple F t) (ha : ∀ i, linePoints (a i) ∉ selected ω) :
    survivors (tupleShapes a) ω = survivors ∅ ω := by
  have hd : selected ω \ tupleShapes a = selected ω := by
    ext S
    simp only [Finset.mem_sdiff]
    constructor
    · exact And.left
    · intro hs
      refine ⟨hs, ?_⟩
      intro ht
      obtain ⟨i, rfl⟩ := (mem_tupleShapes a S).mp ht
      exact ha i hs
  ext x
  rw [mem_survivors_active, mem_survivors_active, hd, Finset.sdiff_empty]

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_CoverEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {shapes : Finset (Finset (Point F))} {D n : ℕ}

theorem filter_incidence_eq_inter (X : Finset (Point F)) (l : AffineLine F) :
    (X.filter fun x => Incidence x l) = X ∩ linePoints l := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_inter, mem_linePoints]

theorem sdiff_coveredPoints_eq (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    X \ coveredPoints Incidence X L = X \ L.biUnion linePoints := by
  rw [coveredPoints_eq_inter_biUnion]
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_inter]
  constructor
  · rintro ⟨hx, hn⟩
    exact ⟨hx, fun h => hn ⟨hx, h⟩⟩
  · rintro ⟨hx, hn⟩
    exact ⟨hx, fun h => hn h.2⟩

theorem survivors_ignore_clean_line_eq (ω : Fin n → Outcome shapes D)
    (L : Finset (AffineLine F)) {l : AffineLine F} (hl : l ∈ cleanLines ω L) :
    survivors {linePoints l} ω = survivors ∅ ω := by
  simpa only [Finset.insert_empty] using
    (survivors_insert_eq_of_not_selected (ignore := ∅)
      (cleanLines_not_selected hl))

theorem clean_cover_count_bounds (ω : Fin n → Outcome shapes D)
    (L : Finset (AffineLine F)) (τ δ e0 e1 b : ℝ)
    (hδ : 0 < δ) (hτ : δ ≤ τ) (he1 : 0 ≤ e1)
    (htotal : τ * (Fintype.card F : ℝ) ^ 2 - e0 ≤ (survivors ∅ ω).card)
    (hlines : ∀ l : AffineLine F,
      ((survivors {linePoints l} ω ∩ linePoints l).card : ℝ) ≤
        τ * (Fintype.card F : ℝ) + e1)
    (hmiss : ((survivors ∅ ω \ L.biUnion linePoints).card : ℝ) ≤ b)
    (hcard : L.card ≤ Fintype.card F) :
    (overlapExcess Incidence (survivors ∅ ω) (cleanLines ω L) : ℝ) ≤
        e0 + (Fintype.card F : ℝ) * e1 + b ∧
      (Fintype.card F : ℝ) - (cleanLines ω L).card ≤
        (e0 + (Fintype.card F : ℝ) * e1 + b) / (δ * Fintype.card F) := by
  have hq : 0 < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := F)
  apply cover_count_bounds Incidence (survivors ∅ ω) (cleanLines ω L)
    τ (Fintype.card F) e0 e1 b δ hδ hτ hq he1 htotal
  · intro l hl
    have hfilter :
        @Finset.filter _ (fun x => Incidence x l)
          (fun x => Classical.propDecidable (Incidence x l)) (survivors ∅ ω) =
          (survivors ∅ ω).filter (fun x => Incidence x l) :=
      Finset.filter_congr_decidable _ _ _
    rw [hfilter, filter_incidence_eq_inter, ← survivors_ignore_clean_line_eq ω L hl]
    exact hlines l
  · rw [sdiff_coveredPoints_eq, ← survivors_sdiff_cleanLines]
    exact hmiss
  · exact_mod_cast (Finset.card_le_card (cleanLines_subset ω L)).trans hcard

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_DisjointPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

theorem exists_subset_card_slot_injective
    {P I J : Type*} [DecidableEq P] [DecidableEq I] [DecidableEq J]
    (left : P → I) (right : P → J) (D h : ℕ) (S : Finset P)
    (hleft : ∀ i, (S.filter fun x => left x = i).card ≤ D)
    (hright : ∀ j, (S.filter fun x => right x = j).card ≤ D)
    (hlarge : 2 * D * h < S.card) :
    ∃ T : Finset P, T ⊆ S ∧ T.card = h ∧
      Set.InjOn left (T : Set P) ∧ Set.InjOn right (T : Set P) := by
  classical
  induction h generalizing S with
  | zero =>
      refine ⟨∅, Finset.empty_subset S, by simp, ?_, ?_⟩
      · simpa only [Finset.coe_empty] using Set.injOn_empty left
      · simpa only [Finset.coe_empty] using Set.injOn_empty right
  | succ h ih =>
      obtain ⟨x, hx⟩ := Finset.card_pos.mp
        (lt_of_le_of_lt (Nat.zero_le _) hlarge)
      let B := (S.filter fun y => left y = left x) ∪
        (S.filter fun y => right y = right x)
      let U := S \ B
      have hUS : U ⊆ S := Finset.sdiff_subset
      have hB : B.card ≤ 2 * D := by
        calc
          B.card ≤ (S.filter fun y => left y = left x).card +
              (S.filter fun y => right y = right x).card :=
            Finset.card_union_le _ _
          _ ≤ D + D := Nat.add_le_add (hleft (left x)) (hright (right x))
          _ = 2 * D := (Nat.two_mul D).symm
      have hUlarge : 2 * D * h < U.card := by
        have hcount : S.card ≤ U.card + B.card :=
          Finset.card_le_card_sdiff_add_card
        have hexpand : 2 * D * h + 2 * D < S.card := by
          simpa only [Nat.mul_succ] using hlarge
        have hsum : 2 * D * h + 2 * D < U.card + 2 * D :=
          hexpand.trans_le (hcount.trans (Nat.add_le_add_left hB U.card))
        exact Nat.add_lt_add_iff_right.mp hsum
      have hUleft : ∀ i, (U.filter fun y => left y = i).card ≤ D := by
        intro i
        exact (Finset.card_le_card
          (Finset.filter_subset_filter (fun y => left y = i) hUS)).trans (hleft i)
      have hUright : ∀ j, (U.filter fun y => right y = j).card ≤ D := by
        intro j
        exact (Finset.card_le_card
          (Finset.filter_subset_filter (fun y => right y = j) hUS)).trans (hright j)
      obtain ⟨T, hTU, hcard, hTL, hTR⟩ := ih U hUleft hUright hUlarge
      have havoid (y : P) (hy : y ∈ T) :
          left y ≠ left x ∧ right y ≠ right x := by
        have hyU := Finset.mem_sdiff.mp (hTU hy)
        constructor
        · intro heq
          exact hyU.2 (Finset.mem_union.mpr
            (Or.inl (Finset.mem_filter.mpr ⟨hyU.1, heq⟩)))
        · intro heq
          exact hyU.2 (Finset.mem_union.mpr
            (Or.inr (Finset.mem_filter.mpr ⟨hyU.1, heq⟩)))
      have hxT : x ∉ T := fun hxT => (havoid x hxT).1 rfl
      refine ⟨insert x T, ?_, ?_, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hx
        · exact hUS (hTU hy)
      · rw [Finset.card_insert_of_notMem hxT, hcard]
      · rw [Finset.coe_insert]
        refine (Set.injOn_insert hxT).2 ⟨hTL, ?_⟩
        rintro ⟨y, hy, heq⟩
        exact (havoid y hy).1 heq
      · rw [Finset.coe_insert]
        refine (Set.injOn_insert hxT).2 ⟨hTR, ?_⟩
        rintro ⟨y, hy, heq⟩
        exact (havoid y hy).2 heq

theorem exists_disjoint_coordinate_sample
    {P I J : Type*} [DecidableEq P] [DecidableEq I] [DecidableEq J]
    (S : Finset P) (left : P → I) (right : P → J) (D h : ℕ)
    (hleft : ∀ i, (S.filter fun x => left x = i).card ≤ D)
    (hright : ∀ j, (S.filter fun x => right x = j).card ≤ D)
    (hlarge : 2 * D * h < S.card) :
    ∃ e : Fin h ↪ ↥S,
      Function.Injective (fun k => left (e k).val) ∧
      Function.Injective (fun k => right (e k).val) := by
  classical
  obtain ⟨T, hTS, hcard, hTL, hTR⟩ :=
    exists_subset_card_slot_injective left right D h S hleft hright hlarge
  let q : Fin h ≃ ↥T := (Finset.equivFinOfCardEq (s := T) hcard).symm
  let e : Fin h ↪ ↥S :=
    { toFun := fun k => ⟨(q k).val, hTS (q k).property⟩
      inj' := by
        intro i j hij
        apply q.injective
        apply Subtype.ext
        exact congrArg (fun x : ↥S => x.val) hij }
  refine ⟨e, ?_, ?_⟩
  · intro i j hij
    apply q.injective
    apply Subtype.ext
    change left (q i).val = left (q j).val at hij
    exact hTL (q i).property (q j).property hij
  · intro i j hij
    apply q.injective
    apply Subtype.ext
    change right (q i).val = right (q j).val at hij
    exact hTR (q i).property (q j).property hij

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_SamplingNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.LineCover

theorem half_pow_le_descFactorial (n k : ℕ) (h : 2 * k ≤ n) :
    ((n : ℝ) / 2) ^ k ≤ (n.descFactorial k : ℝ) := by
  have hk : k ≤ n := (Nat.le_mul_of_pos_left k (by decide : 0 < 2)).trans h
  have hkn : k ≤ n + 1 := hk.trans (Nat.le_succ n)
  have hr : (2 : ℝ) * k ≤ n := by exact_mod_cast h
  have hbase : (n : ℝ) / 2 ≤ ((n + 1 - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub hkn, Nat.cast_add, Nat.cast_one]
    linarith
  calc
    ((n : ℝ) / 2) ^ k ≤ (((n + 1 - k : ℕ) : ℝ)) ^ k :=
      pow_le_pow_left₀ (by positivity) hbase k
    _ ≤ (n.descFactorial k : ℝ) := by
      exact_mod_cast Nat.pow_sub_le_descFactorial n k

theorem low_occupancy_quotient_le (m D R t h : ℕ)
    (hm : 0 < m) (hlarge : 4 * h ≤ m) :
    (t : ℝ) ^ (2 * h) * ((m : ℝ) * D * R) ^ h /
        (m.descFactorial (2 * h) : ℝ) ≤
      (4 * (D : ℝ) * (t : ℝ) ^ 2 * R / m) ^ h := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hden : ((m : ℝ) / 2) ^ (2 * h) ≤ (m.descFactorial (2 * h) : ℝ) :=
    half_pow_le_descFactorial m (2 * h) (by simpa only [← Nat.mul_assoc] using hlarge)
  have hpos : 0 < ((m : ℝ) / 2) ^ (2 * h) := by positivity
  calc
    _ ≤ (t : ℝ) ^ (2 * h) * ((m : ℝ) * D * R) ^ h /
        (((m : ℝ) / 2) ^ (2 * h)) :=
      div_le_div_of_nonneg_left (by positivity) hpos hden
    _ = ((t : ℝ) ^ 2 * ((m : ℝ) * D * R) / ((m : ℝ) / 2) ^ 2) ^ h := by
      simp only [div_pow, mul_pow, pow_mul]
    _ = _ := by
      congr 1
      field_simp
      ring

theorem high_occupancy_quotient_le (R N D t h : ℕ)
    (hR : 0 < R) (hN : 0 < N) (hRlarge : 2 * h ≤ R) (hNlarge : 2 * h ≤ N) :
    (t : ℝ) ^ (2 * h) * ((D : ℝ) * N) ^ h /
        ((R.descFactorial h : ℝ) * (N.descFactorial h : ℝ)) ≤
      (4 * (D : ℝ) * (t : ℝ) ^ 2 / R) ^ h := by
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : ((R : ℝ) / 2) ^ h * ((N : ℝ) / 2) ^ h ≤
      (R.descFactorial h : ℝ) * (N.descFactorial h : ℝ) :=
    mul_le_mul (half_pow_le_descFactorial R h hRlarge)
      (half_pow_le_descFactorial N h hNlarge) (by positivity) (by positivity)
  have hpos : 0 < ((R : ℝ) / 2) ^ h * ((N : ℝ) / 2) ^ h := by positivity
  calc
    _ ≤ (t : ℝ) ^ (2 * h) * ((D : ℝ) * N) ^ h /
        (((R : ℝ) / 2) ^ h * ((N : ℝ) / 2) ^ h) :=
      div_le_div_of_nonneg_left (by positivity) hpos hden
    _ = ((t : ℝ) ^ 2 * ((D : ℝ) * N) / (((R : ℝ) / 2) * ((N : ℝ) / 2))) ^ h := by
      simp only [div_pow, mul_pow, pow_mul]
    _ = _ := by
      congr 1
      field_simp
      ring

end RyserCoveringCounterexample.LineCover

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_FiniteFailureNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.LineCover

private theorem half_sq_le_descFactorial_two (m : ℕ) (hm : 2 ≤ m) :
    (m : ℝ) ^ 2 / 2 ≤ (m.descFactorial 2 : ℝ) := by
  have hm1 : 1 ≤ m := (by decide : 1 ≤ 2).trans hm
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hhalf : (m : ℝ) / 2 ≤ (m : ℝ) - 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg m)
  have hfactor : m.descFactorial 2 = (m - 1) * m := by
    simpa only [Nat.descFactorial_one] using Nat.descFactorial_succ m 1
  rw [hfactor, Nat.cast_mul, Nat.cast_sub hm1, Nat.cast_one]
  nlinarith only [hmul]

private theorem half_le_nat_sub_cast (m j : ℕ) (h : 2 * j ≤ m) :
    (m : ℝ) / 2 ≤ ((m - j : ℕ) : ℝ) := by
  have hjm : j ≤ m := (Nat.le_mul_of_pos_left j (by decide : 0 < 2)).trans h
  have hR : (2 : ℝ) * j ≤ m := by exact_mod_cast h
  rw [Nat.cast_sub hjm]
  linarith

theorem low_sampling_failure_le_coarse (m D R t h K : ℕ) (P δ : ℝ)
    (hm : 4 ≤ m) (hδ : 0 < δ) (hlarge : 4 * h ≤ m) (hP : 0 ≤ P) :
    2 * P / (δ * (m.descFactorial 2 : ℝ)) +
      ((2 * t).descFactorial 2 : ℝ) * R / ((m - 1 : ℕ) : ℝ) +
      ((2 * t).descFactorial 3 : ℝ) * R / ((m - 2 : ℕ) : ℝ) +
      (K : ℝ) * (t : ℝ) ^ (2 * h) * ((m * D * R : ℕ) : ℝ) ^ h /
        (m.descFactorial (2 * h) : ℝ) ≤
    4 * P / (δ * (m : ℝ) ^ 2) +
      8 * (t : ℝ) ^ 2 * R / m +
      16 * (t : ℝ) ^ 3 * R / m +
      (K : ℝ) * (4 * (D : ℝ) * (t : ℝ) ^ 2 * R / m) ^ h := by
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 4) hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hpairden : δ * ((m : ℝ) ^ 2 / 2) ≤ δ * (m.descFactorial 2 : ℝ) :=
    mul_le_mul_of_nonneg_left
      (half_sq_le_descFactorial_two m ((by decide : 2 ≤ 4).trans hm)) hδ.le
  have hpair : 2 * P / (δ * (m.descFactorial 2 : ℝ)) ≤
      4 * P / (δ * (m : ℝ) ^ 2) := by
    calc
      _ ≤ 2 * P / (δ * ((m : ℝ) ^ 2 / 2)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hpairden
      _ = _ := by
        field_simp [hδ.ne', hmR.ne']
        ring
  have htwo : ((2 * t).descFactorial 2 : ℝ) ≤ 4 * (t : ℝ) ^ 2 := by
    calc
      _ ≤ ((2 * t : ℕ) : ℝ) ^ 2 := by
        exact_mod_cast Nat.descFactorial_le_pow (2 * t) 2
      _ = _ := by
        rw [Nat.cast_mul, Nat.cast_ofNat]
        ring
  have hthree : ((2 * t).descFactorial 3 : ℝ) ≤ 8 * (t : ℝ) ^ 3 := by
    calc
      _ ≤ ((2 * t : ℕ) : ℝ) ^ 3 := by
        exact_mod_cast Nat.descFactorial_le_pow (2 * t) 3
      _ = _ := by
        rw [Nat.cast_mul, Nat.cast_ofNat]
        ring
  have hsub1 : (m : ℝ) / 2 ≤ ((m - 1 : ℕ) : ℝ) :=
    half_le_nat_sub_cast m 1 ((by decide : 2 * 1 ≤ 4).trans hm)
  have hsub2 : (m : ℝ) / 2 ≤ ((m - 2 : ℕ) : ℝ) :=
    half_le_nat_sub_cast m 2 hm
  have hparallel : ((2 * t).descFactorial 2 : ℝ) * R /
      ((m - 1 : ℕ) : ℝ) ≤ 8 * (t : ℝ) ^ 2 * R / m := by
    calc
      _ ≤ (4 * (t : ℝ) ^ 2 * R) / ((m : ℝ) / 2) :=
        div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_right htwo (Nat.cast_nonneg R)) (by positivity) hsub1
      _ = _ := by
        field_simp [hmR.ne']
        ring
  have hconcurrent : ((2 * t).descFactorial 3 : ℝ) * R /
      ((m - 2 : ℕ) : ℝ) ≤ 16 * (t : ℝ) ^ 3 * R / m := by
    calc
      _ ≤ (8 * (t : ℝ) ^ 3 * R) / ((m : ℝ) / 2) :=
        div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_right hthree (Nat.cast_nonneg R)) (by positivity) hsub2
      _ = _ := by
        field_simp [hmR.ne']
        ring
  have hoccupancy :
      (K : ℝ) * (t : ℝ) ^ (2 * h) * ((m * D * R : ℕ) : ℝ) ^ h /
          (m.descFactorial (2 * h) : ℝ) ≤
        (K : ℝ) * (4 * (D : ℝ) * (t : ℝ) ^ 2 * R / m) ^ h := by
    simpa only [Nat.cast_mul, mul_assoc, mul_div_assoc] using
      mul_le_mul_of_nonneg_left (low_occupancy_quotient_le m D R t h hmpos hlarge)
        (Nat.cast_nonneg K)
  exact add_le_add (add_le_add (add_le_add hpair hparallel) hconcurrent) hoccupancy

theorem high_occupancy_term_le_coarse (R N D t h K : ℕ)
    (hR : 0 < R) (hN : 0 < N) (hRlarge : 2 * h ≤ R) (hNlarge : 2 * h ≤ N) :
    (K : ℝ) * (t.descFactorial h : ℝ) ^ 2 * ((D * N : ℕ) : ℝ) ^ h /
        ((R.descFactorial h : ℝ) * (N.descFactorial h : ℝ)) ≤
      (K : ℝ) * (4 * (D : ℝ) * (t : ℝ) ^ 2 / R) ^ h := by
  have hfall : (t.descFactorial h : ℝ) ≤ (t : ℝ) ^ h := by
    exact_mod_cast Nat.descFactorial_le_pow t h
  have hfall2 : (t.descFactorial h : ℝ) ^ 2 ≤ (t : ℝ) ^ (2 * h) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hfall 2).trans_eq
      (pow_mul' (t : ℝ) 2 h).symm
  have hnum : (t.descFactorial h : ℝ) ^ 2 * ((D : ℝ) * N) ^ h ≤
      (t : ℝ) ^ (2 * h) * ((D : ℝ) * N) ^ h :=
    mul_le_mul_of_nonneg_right hfall2 (by positivity)
  have hratio :
      (t.descFactorial h : ℝ) ^ 2 * ((D : ℝ) * N) ^ h /
          ((R.descFactorial h : ℝ) * (N.descFactorial h : ℝ)) ≤
        (4 * (D : ℝ) * (t : ℝ) ^ 2 / R) ^ h :=
    (div_le_div_of_nonneg_right hnum
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).trans
        (high_occupancy_quotient_le R N D t h hR hN hRlarge hNlarge)
  simpa only [Nat.cast_mul, mul_assoc, mul_div_assoc] using
    mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg K)

end RyserCoveringCounterexample.LineCover

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_FailureNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open Filter Topology

theorem low_concurrency_ratio_le {q m R κ : ℝ} (hq : 0 < q)
    (hm : q / 2 ≤ m) (hR : R ≤ q ^ (1 / 2 + κ / 4)) :
    R / m ≤ 2 * q ^ (-(1 / 2 - κ / 4)) := by
  calc
    R / m ≤ q ^ (1 / 2 + κ / 4) / (q / 2) :=
      div_le_div₀ (Real.rpow_nonneg hq.le _) hR (by positivity) hm
    _ = 2 * (q ^ (1 / 2 + κ / 4) / q) := by
      field_simp [hq.ne']

    _ = 2 * q ^ (-(1 / 2 - κ / 4)) := by
      rw [← Real.rpow_sub_one hq.ne']
      congr 2
      ring

theorem high_concurrency_inverse_le {q R κ : ℝ} (hq : 0 < q)
    (hR : q ^ (1 / 2 + κ / 4) ≤ R) :
    1 / R ≤ q ^ (-(1 / 2 + κ / 4)) := by
  calc
    1 / R ≤ 1 / q ^ (1 / 2 + κ / 4) :=
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hq _) hR
    _ = q ^ (-(1 / 2 + κ / 4)) := by rw [Real.rpow_neg hq.le, one_div]

theorem sampling_occupancy_le_power (D h t : ℕ) {q K B C β : ℝ}
    (hq : 0 < q) (hK0 : 0 ≤ K) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hK : K ≤ (D : ℝ) * q ^ (D : ℝ))
    (hbase : B ≤ C * (t : ℝ) ^ 2 * q ^ (-β)) :
    K * B ^ h ≤ ((D : ℝ) * C ^ h) *
      ((t : ℝ) ^ (2 * h) * q ^ (-((h : ℝ) * β - D))) := by
  let _ := hK0
  let _ := hC
  have hp := pow_le_pow_left₀ hB hbase h
  have hjoin : q ^ (D : ℝ) * (q ^ (-β)) ^ h =
      q ^ (-((h : ℝ) * β - D)) := by
    rw [← Real.rpow_mul_natCast hq.le, ← Real.rpow_add hq]
    congr 1
    ring
  calc
    K * B ^ h ≤ ((D : ℝ) * q ^ (D : ℝ)) *
        (C * (t : ℝ) ^ 2 * q ^ (-β)) ^ h :=
      mul_le_mul hK hp (pow_nonneg hB _) (by positivity)
    _ = ((D : ℝ) * C ^ h) * (t : ℝ) ^ (2 * h) *
        (q ^ (D : ℝ) * (q ^ (-β)) ^ h) := by
      simp only [mul_pow, pow_mul]
      ring
    _ = _ := by rw [hjoin]; ring

theorem high_survivor_term_le {q E R N δ ρ κ : ℝ} (D : ℕ)
    (hq : 0 < q) (hδ : 0 < δ) (hρ : 0 < ρ) (hE0 : 0 ≤ E)
    (hE : E ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10))
    (hR : q ^ (1 / 2 + κ / 4) ≤ R) (hN : ρ * q / 2 ≤ N) :
    2 * E / (δ * R * N) ≤
      (4 * ((D : ℝ) + 4) / (δ * ρ)) * q ^ (-(3 * κ / 20)) := by
  let _ := hE0
  have hR0 : 0 < R := lt_of_lt_of_le (Real.rpow_pos_of_pos hq _) hR
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hden : δ * q ^ (1 / 2 + κ / 4) * (ρ * q / 2) ≤ δ * R * N :=
    mul_le_mul (mul_le_mul_of_nonneg_left hR hδ.le) hN (by positivity)
      (mul_nonneg hδ.le hR0.le)
  have hratio : q ^ (3 / 2 + κ / 10) /
      (q ^ (1 / 2 + κ / 4) * q) = q ^ (-(3 * κ / 20)) := by
    rw [← Real.rpow_add_one hq.ne', ← Real.rpow_sub hq]
    congr 1
    ring
  calc
    2 * E / (δ * R * N) ≤
        (2 * (((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10))) /
          (δ * q ^ (1 / 2 + κ / 4) * (ρ * q / 2)) :=
      div_le_div₀ (by positivity) (by linarith) (by positivity) hden
    _ = (4 * ((D : ℝ) + 4) / (δ * ρ)) *
        (q ^ (3 / 2 + κ / 10) / (q ^ (1 / 2 + κ / 4) * q)) := by
      field_simp
      ring
    _ = _ := by rw [hratio]

theorem low_coarse_failure_le_envelope (D m R K : ℕ) {δ A κ q P : ℝ}
    (hq : 0 < q) (hδ : 0 < δ) (hm : q / 2 ≤ (m : ℝ))
    (hR : (R : ℝ) ≤ q ^ (1 / 2 + κ / 4))
    (hK : (K : ℝ) ≤ (D : ℝ) * q ^ (D : ℝ))
    (hP : P / (m : ℝ) ^ 2 ≤
      4 * (((D : ℝ) + 4) * q ^ (-(7 * κ / 30)) + q ^ (-(3 * κ / 4)))) :
    let t := (logarithmicSampleSize A q : ℝ)
    let h := 10 * (D + 1)
    4 * P / (δ * (m : ℝ) ^ 2) + 8 * t ^ 2 * R / m +
      16 * t ^ 3 * R / m + (K : ℝ) * (4 * (D : ℝ) * t ^ 2 * R / m) ^ h ≤
      lowFailureEnvelope D δ A κ q := by
  let t := logarithmicSampleSize A q
  let h := 10 * (D + 1)
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hm
  have hratio := low_concurrency_ratio_le hq hm hR
  have hpair : 4 * P / (δ * (m : ℝ) ^ 2) ≤
      (16 / δ) * (((D : ℝ) + 4) * q ^ (-(7 * κ / 30)) + q ^ (-(3 * κ / 4))) := by
    have hh := mul_le_mul_of_nonneg_left hP (by positivity : 0 ≤ 4 / δ)
    calc
      _ = (4 / δ) * (P / (m : ℝ) ^ 2) := by
        field_simp [hδ.ne', hm0.ne']

      _ ≤ (4 / δ) *
          (4 * (((D : ℝ) + 4) * q ^ (-(7 * κ / 30)) + q ^ (-(3 * κ / 4)))) := hh
      _ = _ := by ring
  have hparallel : 8 * (t : ℝ) ^ 2 * R / m ≤
      16 * ((t : ℝ) ^ 2 * q ^ (-(1 / 2 - κ / 4))) := by
    have hh := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 8 * (t : ℝ) ^ 2)
    calc
      _ = (8 * (t : ℝ) ^ 2) * ((R : ℝ) / m) := by ring
      _ ≤ (8 * (t : ℝ) ^ 2) * (2 * q ^ (-(1 / 2 - κ / 4))) := hh
      _ = _ := by ring
  have hconcurrent : 16 * (t : ℝ) ^ 3 * R / m ≤
      32 * ((t : ℝ) ^ 3 * q ^ (-(1 / 2 - κ / 4))) := by
    have hh := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 16 * (t : ℝ) ^ 3)
    calc
      _ = (16 * (t : ℝ) ^ 3) * ((R : ℝ) / m) := by ring
      _ ≤ (16 * (t : ℝ) ^ 3) * (2 * q ^ (-(1 / 2 - κ / 4))) := hh
      _ = _ := by ring
  have hbase : 4 * (D : ℝ) * (t : ℝ) ^ 2 * R / m ≤
      (8 * (D : ℝ)) * (t : ℝ) ^ 2 * q ^ (-(1 / 2 - κ / 4)) := by
    have hh := mul_le_mul_of_nonneg_left hratio
      (by positivity : 0 ≤ 4 * (D : ℝ) * (t : ℝ) ^ 2)
    calc
      _ = (4 * (D : ℝ) * (t : ℝ) ^ 2) * ((R : ℝ) / m) := by ring
      _ ≤ (4 * (D : ℝ) * (t : ℝ) ^ 2) * (2 * q ^ (-(1 / 2 - κ / 4))) := hh
      _ = _ := by ring
  have hoccupancy := sampling_occupancy_le_power D h t hq (Nat.cast_nonneg K)
    (by positivity : 0 ≤ 4 * (D : ℝ) * (t : ℝ) ^ 2 * R / m)
    (by positivity : 0 ≤ 8 * (D : ℝ)) hK hbase
  dsimp only [lowFailureEnvelope]
  dsimp only [t, h] at hparallel hconcurrent hoccupancy
  linarith

theorem high_coarse_failure_le_envelope (D R N K : ℕ) {δ ρ A κ q E : ℝ}
    (hq : 0 < q) (hδ : 0 < δ) (hρ : 0 < ρ) (hE0 : 0 ≤ E)
    (hE : E ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10))
    (hR : q ^ (1 / 2 + κ / 4) ≤ (R : ℝ)) (hN : ρ * q / 2 ≤ (N : ℝ))
    (hK : (K : ℝ) ≤ (D : ℝ) * q ^ (D : ℝ)) :
    let t := (logarithmicSampleSize A q : ℝ)
    let h := 10 * (D + 1)
    2 * E / (δ * R * N) + (t ^ 2 + t ^ 3) / R +
      (K : ℝ) * (4 * (D : ℝ) * t ^ 2 / R) ^ h ≤
      highFailureEnvelope D δ ρ A κ q := by
  let t := logarithmicSampleSize A q
  let h := 10 * (D + 1)
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le (Real.rpow_pos_of_pos hq _) hR
  have hsurvivors := high_survivor_term_le D hq hδ hρ hE0 hE hR hN
  have hinverse := high_concurrency_inverse_le hq hR
  have hgeometry : ((t : ℝ) ^ 2 + (t : ℝ) ^ 3) / R ≤
      (t : ℝ) ^ 2 * q ^ (-(1 / 2 + κ / 4)) +
        (t : ℝ) ^ 3 * q ^ (-(1 / 2 + κ / 4)) := by
    have hh := mul_le_mul_of_nonneg_left hinverse
      (by positivity : 0 ≤ (t : ℝ) ^ 2 + (t : ℝ) ^ 3)
    calc
      _ = ((t : ℝ) ^ 2 + (t : ℝ) ^ 3) * (1 / (R : ℝ)) := by ring
      _ ≤ ((t : ℝ) ^ 2 + (t : ℝ) ^ 3) * q ^ (-(1 / 2 + κ / 4)) := hh
      _ = _ := by ring
  have hbase : 4 * (D : ℝ) * (t : ℝ) ^ 2 / R ≤
      (4 * (D : ℝ)) * (t : ℝ) ^ 2 * q ^ (-(1 / 2 + κ / 4)) := by
    have hh := mul_le_mul_of_nonneg_left hinverse
      (by positivity : 0 ≤ 4 * (D : ℝ) * (t : ℝ) ^ 2)
    calc
      _ = (4 * (D : ℝ) * (t : ℝ) ^ 2) * (1 / (R : ℝ)) := by ring
      _ ≤ (4 * (D : ℝ) * (t : ℝ) ^ 2) * q ^ (-(1 / 2 + κ / 4)) := hh
      _ = _ := by ring
  have hoccupancy := sampling_occupancy_le_power D h t hq (Nat.cast_nonneg K)
    (by positivity : 0 ≤ 4 * (D : ℝ) * (t : ℝ) ^ 2 / R)
    (by positivity : 0 ≤ 4 * (D : ℝ)) hK hbase
  dsimp only [highFailureEnvelope]
  dsimp only [t, h] at hgeometry hoccupancy
  linarith

theorem low_sampling_failure_le_envelope (D m R K : ℕ) {δ A κ q P : ℝ}
    (hq : 0 < q) (hδ : 0 < δ) (hm : q / 2 ≤ (m : ℝ))
    (hm4 : 4 ≤ m) (hlarge : 4 * (10 * (D + 1)) ≤ m) (hP0 : 0 ≤ P)
    (hR : (R : ℝ) ≤ q ^ (1 / 2 + κ / 4))
    (hK : (K : ℝ) ≤ (D : ℝ) * q ^ (D : ℝ))
    (hP : P / (m : ℝ) ^ 2 ≤
      4 * (((D : ℝ) + 4) * q ^ (-(7 * κ / 30)) + q ^ (-(3 * κ / 4)))) :
    let t := logarithmicSampleSize A q
    let h := 10 * (D + 1)
    2 * P / (δ * (m.descFactorial 2 : ℝ)) +
      ((2 * t).descFactorial 2 : ℝ) * R / ((m - 1 : ℕ) : ℝ) +
      ((2 * t).descFactorial 3 : ℝ) * R / ((m - 2 : ℕ) : ℝ) +
      (K : ℝ) * (t : ℝ) ^ (2 * h) * ((m * D * R : ℕ) : ℝ) ^ h /
        (m.descFactorial (2 * h) : ℝ) ≤ lowFailureEnvelope D δ A κ q :=
  (low_sampling_failure_le_coarse m D R (logarithmicSampleSize A q)
    (10 * (D + 1)) K P δ hm4 hδ hlarge hP0).trans
      (low_coarse_failure_le_envelope D m R K hq hδ hm hR hK hP)

theorem high_sampling_failure_le_envelope (D R N K : ℕ) {δ ρ A κ q E : ℝ}
    (hq : 0 < q) (hδ : 0 < δ) (hρ : 0 < ρ) (hE0 : 0 ≤ E)
    (hE : E ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10))
    (hR : q ^ (1 / 2 + κ / 4) ≤ (R : ℝ)) (hN : ρ * q / 2 ≤ (N : ℝ))
    (hRlarge : 2 * (10 * (D + 1)) ≤ R) (hNlarge : 2 * (10 * (D + 1)) ≤ N)
    (hK : (K : ℝ) ≤ (D : ℝ) * q ^ (D : ℝ)) :
    let t := logarithmicSampleSize A q
    let h := 10 * (D + 1)
    2 * E / (δ * R * N) + ((t : ℝ) ^ 2 + (t : ℝ) ^ 3) / R +
      (K : ℝ) * (t.descFactorial h : ℝ) ^ 2 * ((D * N : ℕ) : ℝ) ^ h /
        ((R.descFactorial h : ℝ) * (N.descFactorial h : ℝ)) ≤
      highFailureEnvelope D δ ρ A κ q := by
  have hR0 : 0 < R := by
    exact_mod_cast lt_of_lt_of_le (Real.rpow_pos_of_pos hq _) hR
  have hN0 : 0 < N := by
    have hNreal : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
    exact_mod_cast hNreal
  exact (add_le_add (le_refl _)
    (high_occupancy_term_le_coarse R N D (logarithmicSampleSize A q)
      (10 * (D + 1)) K hR0 hN0 hRlarge hNlarge)).trans
        (high_coarse_failure_le_envelope (A := A) D R N K hq hδ hρ hE0 hE hR hN hK)

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_GoodTuples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {D : ℕ} {δ : ℝ}

namespace GoodTuples

variable {process : DeletionProcess F D δ} {h t : ℕ} {ω : process.Config}

theorem clean_crosscard_ge (hgood : GoodTuples process h t ω)
    (L : Finset (AffineLine F)) (a : LineTuple F t)
    (ha : AdmissibleTuple process.shapes D h a)
    (hclean : ∀ i, a i ∈ cleanLines ω L) :
    δ * (t : ℝ) ^ 2 / 2 ≤
      ((process.survivorSet ω ∩ crossPoints a).card : ℝ) := by
  have heq := survivors_ignore_tuple_eq ω a
    (fun i => cleanLines_not_selected (hclean i))
  have hbound := hgood a ha
  change δ * (t : ℝ) ^ 2 / 2 ≤
    ((survivors (tupleShapes a) ω ∩ crossPoints a).card : ℝ) at hbound
  change δ * (t : ℝ) ^ 2 / 2 ≤
    ((survivors ∅ ω ∩ crossPoints a).card : ℝ)
  rw [heq] at hbound
  exact hbound

theorem no_sparse_clean_tuple (hgood : GoodTuples process h t ω)
    (L : Finset (AffineLine F)) (a : LineTuple F t)
    (ha : AdmissibleTuple process.shapes D h a)
    (hclean : ∀ i, a i ∈ cleanLines ω L)
    (hsmall : ((process.survivorSet ω ∩ crossPoints a).card : ℝ) <
      δ * (t : ℝ) ^ 2 / 2) : False :=
  (not_lt_of_ge (hgood.clean_crosscard_ge L a ha hclean)) hsmall

end GoodTuples

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_ProjectiveLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [instFieldF : Field F] [instFintypeF : Fintype F] [DecidableEq F]

theorem leftDegree_projectiveLinesOf (L : Finset (AffineLine F)) (x : Point F) :
    Incidence.leftDegree ProjectiveIncidence (projectiveLinesOf L) (Sum.inl x) =
      multiplicity Incidence L x := let _ := instFintypeF; by
  unfold Incidence.leftDegree projectiveLinesOf multiplicity
  have houter :
      @Finset.filter _ (ProjectiveIncidence (Sum.inl x))
        (fun l => Classical.propDecidable (ProjectiveIncidence (Sum.inl x) l))
        (L.image some) = (L.image some).filter (ProjectiveIncidence (Sum.inl x)) :=
    Finset.filter_congr_decidable _ _ _
  have hinner :
      @Finset.filter _ (Incidence x) (fun l => Classical.propDecidable (Incidence x l)) L =
        L.filter (Incidence x) := Finset.filter_congr_decidable _ _ _
  rw [houter, hinner, Finset.filter_image, Finset.card_image_of_injective _ (Option.some_injective _)]
  congr 1

theorem incidenceCount_projective_lifts (X : Finset (Point F))
    (L : Finset (AffineLine F)) :
    Incidence.incidenceCount ProjectiveIncidence (projectivePointsOf X)
      (projectiveLinesOf L) = ∑ x ∈ X, multiplicity Incidence L x := by
  unfold Incidence.incidenceCount projectivePointsOf
  rw [Finset.sum_image]
  · exact Finset.sum_congr rfl (fun x _ => leftDegree_projectiveLinesOf L x)
  · intro x hx y hy hxy
    exact Sum.inl.inj hxy

theorem multiplicity_eq_finite_pencil (L : Finset (AffineLine F)) (x : Point F) :
    multiplicity Incidence L x =
      (L.filter fun l => ProjectiveIncidence (Sum.inl x) (some l)).card := let _ := instFintypeF; by
  unfold multiplicity
  have hfilter :
      @Finset.filter _ (Incidence x) (fun l => Classical.propDecidable (Incidence x l)) L =
        L.filter (Incidence x) := Finset.filter_congr_decidable _ _ _
  rw [hfilter]
  congr 1

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_HeavyIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F]

theorem heavy_incidence_sum_le
    (hq : Incidence.incidenceThreshold ≤ Fintype.card F)
    (hsub : Incidence.SmallProperSubfields F)
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (T : ℝ)
    (hheavy : ((heavyPoints Incidence X L T).card : ℝ) ≤
      (Fintype.card F : ℝ) ^ (1 + Incidence.savingExponent))
    (hL : L.card ≤ Fintype.card F) :
    (∑ x ∈ heavyPoints Incidence X L T, (multiplicity Incidence L x : ℝ)) ≤
      (Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 - Incidence.savingExponent) := by
  have hqone : 1 ≤ (Fintype.card F : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α := F)))
  have hqpow : (Fintype.card F : ℝ) ≤
      (Fintype.card F : ℝ) ^ (1 + Incidence.savingExponent) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hqone
        (show (1 : ℝ) ≤ 1 + Incidence.savingExponent by
          linarith [Incidence.savingExponent_pos]))
  have hbound := Incidence.uniform_incidence_bound F hq hsub
    (projectivePointsOf (heavyPoints Incidence X L T)) (projectiveLinesOf L)
    (by simpa only [card_projectivePointsOf] using hheavy)
    (by
      rw [card_projectiveLinesOf]
      exact (show (L.card : ℝ) ≤ (Fintype.card F : ℝ) by
        exact_mod_cast hL).trans hqpow)
  rw [incidenceCount_projective_lifts, Nat.cast_sum] at hbound
  exact hbound

theorem orderedPairMass_le_of_uniform_incidence
    (hq : Incidence.incidenceThreshold ≤ Fintype.card F)
    (hsub : Incidence.SmallProperSubfields F)
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (T R : ℝ)
    (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hheavy : ((heavyPoints Incidence X L T).card : ℝ) ≤
      (Fintype.card F : ℝ) ^ (1 + Incidence.savingExponent))
    (hL : L.card ≤ Fintype.card F)
    (hpencil : ∀ p : ProjectivePoint F, ((coverPencil L p).card : ℝ) ≤ R) :
    (orderedPairMass Incidence X L : ℝ) ≤
      T * (overlapExcess Incidence X L : ℝ) +
        R * (Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 - Incidence.savingExponent) := by
  have hpoint : ∀ x ∈ X, (multiplicity Incidence L x : ℝ) ≤ R := by
    intro x _
    rw [multiplicity_eq_finite_pencil]
    simpa only [coverPencil] using hpencil (Sum.inl x)
  exact (orderedPairMass_le_light_add_heavy Incidence X L T R hT hpoint).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (heavy_incidence_sum_le hq hsub X L T hheavy hL) hR))

theorem heavyPoints_card_le_of_excess
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (T B : ℝ)
    (hT : 1 < T) (hE : (overlapExcess Incidence X L : ℝ) ≤ B) :
    ((heavyPoints Incidence X L T).card : ℝ) ≤ B / (T - 1) := let _ := instFintypeF; by
  apply (le_div_iff₀ (sub_pos.mpr hT)).2
  exact (heavyPoints_card_mul_le_excess Incidence X L T hT).trans hE

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_HighSamples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F]

theorem highTuple_mem (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    {t : ℕ} (s : HighSample L p t) (i : Fin t ⊕ Fin t) : highTuple L p s i ∈ L := by
  cases i with
  | inl i => exact coverPencil_subset L p (s.1 i).property
  | inr i => exact complementPopulation_mem L p (s.2 i)

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_HighDegeneracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F]

theorem highParallelLines_card_le (L : Finset (AffineLine F))
    (p : ProjectivePoint F) {t : ℕ} (b : Fin t ↪ ComplementPopulation L p) :
    (highParallelLines L p b).card ≤ t := by
  have hone (j : Fin t) :
      (Finset.univ.filter fun k : PencilPopulation L p => k.val.1 = (b j).val.1).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro k hk k' hk'
    have hd := (Finset.mem_filter.mp hk).2
    have hd' := (Finset.mem_filter.mp hk').2
    cases p with
    | inl x =>
      apply Subtype.ext
      exact line_eq_of_direction_eq_of_incidence (hd.trans hd'.symm)
        (pencilPopulation_incident L (Sum.inl x) k)
        (pencilPopulation_incident L (Sum.inl x) k')
    | inr d =>
      have hkdir : d = k.val.1 := pencilPopulation_incident L (Sum.inr d) k
      exact (complementPopulation_not_incident L (Sum.inr d) (b j)
        (hkdir.trans hd)).elim
  calc
    _ ≤ ∑ j : Fin t,
        (Finset.univ.filter fun k : PencilPopulation L p => k.val.1 = (b j).val.1).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin t, 1 := Finset.sum_le_sum (fun j _ => hone j)
    _ = t := by simp

theorem highCollisionLines_card_le (L : Finset (AffineLine F))
    (p : ProjectivePoint F) {t : ℕ} (b : Fin t ↪ ComplementPopulation L p) :
    (highCollisionLines L p b).card ≤ t * t := by
  have hone (ij : Fin t × Fin t) :
      (Finset.univ.filter fun k : PencilPopulation L p => ij.1 ≠ ij.2 ∧
        ∃ x : ProjectivePoint F, ProjectiveIncidence x (some k.val) ∧
          ProjectiveIncidence x (some (b ij.1).val) ∧
          ProjectiveIncidence x (some (b ij.2).val)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro k hk k' hk'
    obtain ⟨hij, x, hxk, hxc, hxc'⟩ := (Finset.mem_filter.mp hk).2
    obtain ⟨_, y, hyk, hyc, hyc'⟩ := (Finset.mem_filter.mp hk').2
    have hlines : (b ij.1).val ≠ (b ij.2).val := by
      intro he
      exact hij (b.injective (Subtype.ext he))
    have hxy : x = y := eq_projectivePoint_of_common_incidence
      (fun he => hlines (Option.some.inj he)) hxc hxc' hyc hyc'
    subst y
    have hxp : x ≠ p := ne_of_projectiveIncidence_of_not_projectiveIncidence
      hxc (complementPopulation_not_incident L p (b ij.1))
    apply Subtype.ext
    exact eq_affineLine_of_common_projective_incidence hxp.symm
      (pencilPopulation_incident L p k) hxk
      (pencilPopulation_incident L p k') hyk
  calc
    _ ≤ ∑ ij : Fin t × Fin t,
        (Finset.univ.filter fun k : PencilPopulation L p => ij.1 ≠ ij.2 ∧
          ∃ x : ProjectivePoint F, ProjectiveIncidence x (some k.val) ∧
            ProjectiveIncidence x (some (b ij.1).val) ∧
            ProjectiveIncidence x (some (b ij.2).val)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _ij : Fin t × Fin t, 1 := Finset.sum_le_sum (fun ij _ => hone ij)
    _ = t * t := by simp

theorem highBadLines_card_le (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    {t : ℕ} (b : Fin t ↪ ComplementPopulation L p) :
    (highBadLines L p b).card ≤ t + t * t :=
  (Finset.card_union_le (highParallelLines L p b) (highCollisionLines L p b)).trans (Nat.add_le_add
    (highParallelLines_card_le L p b) (highCollisionLines_card_le L p b))

theorem highTuple_grid_of_avoids (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    {t : ℕ} (s : HighSample L p t)
    (havoid : ∀ i, s.1 i ∉ highBadLines L p s.2) :
    FiniteCrossings (highTuple L p s) ∧ (crossPoints (highTuple L p s)).card = t * t := by
  have hfinite (i j : Fin t) :
      ∃ x, Incidence x (s.1 i).val ∧ Incidence x (s.2 j).val := by
    have hdir : (s.1 i).val.1 ≠ (s.2 j).val.1 := by
      intro he
      apply havoid i
      exact Finset.mem_union_left _
        ((mem_highParallelLines L p s.2 (s.1 i)).mpr ⟨j, he⟩)
    exact (existsUnique_incident_of_ne_direction _ _ hdir).exists
  let f : Fin t × Fin t → Point F := fun ij => Classical.choose (hfinite ij.1 ij.2)
  have hf (ij : Fin t × Fin t) :
      Incidence (f ij) (s.1 ij.1).val ∧ Incidence (f ij) (s.2 ij.2).val :=
    Classical.choose_spec (hfinite ij.1 ij.2)
  have hinj : Function.Injective f := by
    intro ij kl he
    have hkl := hf kl
    rw [← he] at hkl
    have hxp : (Sum.inl (f ij) : ProjectivePoint F) ≠ p :=
      ne_of_projectiveIncidence_of_not_projectiveIncidence
        (l := some (s.2 ij.2).val)
        (hf ij).2 (complementPopulation_not_incident L p (s.2 ij.2))
    have hfirst : ij.1 = kl.1 := by
      apply s.1.injective
      apply Subtype.ext
      exact eq_affineLine_of_common_projective_incidence hxp.symm
        (pencilPopulation_incident L p (s.1 ij.1)) (hf ij).1
        (pencilPopulation_incident L p (s.1 kl.1)) hkl.1
    have hsecond : ij.2 = kl.2 := by
      by_contra hne
      apply havoid ij.1
      apply Finset.mem_union_right
      apply (mem_highCollisionLines L p s.2 (s.1 ij.1)).mpr
      exact ⟨ij.2, kl.2, hne, Sum.inl (f ij), (hf ij).1, (hf ij).2, hkl.2⟩
    exact Prod.ext hfirst hsecond
  have hset : crossPoints (highTuple L p s) = Finset.univ.image f := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, j, hi, hj⟩ := (mem_crossPoints (highTuple L p s) x).mp hx
      have he : f (i, j) = x := eq_of_common_incidence_of_ne_lines
        (pencil_ne_complement L p (s.1 i) (s.2 j))
        (hf (i, j)).1 (hf (i, j)).2 hi hj
      exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, he⟩
    · intro hx
      obtain ⟨ij, _, rfl⟩ := Finset.mem_image.mp hx
      exact (mem_crossPoints (highTuple L p s) (f ij)).mpr
        ⟨ij.1, ij.2, (hf ij).1, (hf ij).2⟩
  refine ⟨hfinite, ?_⟩
  rw [hset, Finset.card_image_of_injective _ hinj]
  simp

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_HighIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem pencil_eq_at_complement
    (x : Point F) (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    (c : ComplementPopulation L p) (k l : PencilPopulation L p)
    (hxc : Incidence x c.val) (hxk : Incidence x k.val) (hxl : Incidence x l.val) :
    k = l := by
  apply Subtype.ext
  exact eq_affineLine_of_common_projective_incidence
    (ne_of_projectiveIncidence_of_not_projectiveIncidence
      ((projectiveIncidence_finite_affine x c.val).mpr hxc)
      (complementPopulation_not_incident L p c))
    ((projectiveIncidence_finite_affine x k.val).mpr hxk)
    (pencilPopulation_incident L p k)
    ((projectiveIncidence_finite_affine x l.val).mpr hxl)
    (pencilPopulation_incident L p l)

private theorem pointCrossPairs_card_le
    (x : Point F) (L : Finset (AffineLine F)) (p : ProjectivePoint F) :
    (Finset.univ.filter fun kc : PencilPopulation L p × ComplementPopulation L p =>
      Incidence x kc.1.val ∧ Incidence x kc.2.val).card ≤
      multiplicity Incidence L x - 1 := by
  let B := Finset.univ.filter fun kc : PencilPopulation L p × ComplementPopulation L p =>
    Incidence x kc.1.val ∧ Incidence x kc.2.val
  change B.card ≤ multiplicity Incidence L x - 1
  by_cases hB : B.Nonempty
  · obtain ⟨kc, hkc⟩ := hB
    have hxkc := (Finset.mem_filter.mp hkc).2
    let C := (L.filter (Incidence x)).erase kc.1.val
    have hk : kc.1.val ∈ L.filter (Incidence x) :=
      Finset.mem_filter.mpr ⟨coverPencil_subset L p kc.1.property, hxkc.1⟩
    let f : ↥B → ↥C := fun q =>
      ⟨q.val.2.val, Finset.mem_erase.mpr
        ⟨(pencil_ne_complement L p kc.1 q.val.2).symm,
          Finset.mem_filter.mpr ⟨complementPopulation_mem L p q.val.2,
            (Finset.mem_filter.mp q.property).2.2⟩⟩⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Prod.ext
      · exact pencil_eq_at_complement x L p a.val.2 a.val.1 b.val.1
          (Finset.mem_filter.mp a.property).2.2
          (Finset.mem_filter.mp a.property).2.1
          (Finset.mem_filter.mp b.property).2.1
      · exact Subtype.ext (congrArg (fun z : ↥C => z.val) hab)
    calc
      B.card ≤ C.card := Finset.card_le_card_of_injective hf
      _ = multiplicity Incidence L x - 1 := by
        have hfilter :
            @Finset.filter _ (Incidence x)
              (fun l => Classical.propDecidable (Incidence x l)) L =
                L.filter (Incidence x) := Finset.filter_congr_decidable _ _ _
        unfold multiplicity
        rw [hfilter]
        exact Finset.card_erase_of_mem hk
  · rw [Finset.not_nonempty_iff_eq_empty.mp hB, Finset.card_empty]
    exact Nat.zero_le _

theorem highCrossPairs_card_le
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (p : ProjectivePoint F) :
    (highCrossPairs X L p).card ≤ overlapExcess Incidence X L := by
  let B (x : Point F) :=
    Finset.univ.filter fun kc : PencilPopulation L p × ComplementPopulation L p =>
      Incidence x kc.1.val ∧ Incidence x kc.2.val
  have hcover : highCrossPairs X L p = X.biUnion B := by
    ext kc
    simp only [mem_highCrossPairs, Finset.mem_biUnion, B,
      Finset.mem_filter, Finset.mem_univ, true_and]
  calc
    (highCrossPairs X L p).card = (X.biUnion B).card := congrArg Finset.card hcover
    _ ≤ ∑ x ∈ X, (B x).card := Finset.card_biUnion_le
    _ ≤ ∑ x ∈ X, (multiplicity Incidence L x - 1) :=
      Finset.sum_le_sum fun x _ => pointCrossPairs_card_le x L p
    _ = overlapExcess Incidence X L := rfl

theorem highShapePairs_card_le
    (S : Finset (Point F)) (L : Finset (AffineLine F)) (p : ProjectivePoint F) (D : ℕ)
    (hsparse : ∀ l, S ≠ linePoints l → (S ∩ linePoints l).card ≤ D) :
    (highShapePairs S L p).card ≤ D * (L \ coverPencil L p).card := by
  let B := highShapePairs S L p
  have hfiber (c : ComplementPopulation L p) :
      (B.filter fun kc => kc.2 = c).card ≤ D := by
    by_cases heq : S = linePoints c.val
    · have hempty : (B.filter fun kc => kc.2 = c) = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨kc, hkc⟩
        have hm := (mem_highShapePairs S L p kc).mp (Finset.mem_filter.mp hkc).1
        have hc : kc.2 = c := (Finset.mem_filter.mp hkc).2
        exact hm.2.2 (heq.trans
          (congrArg (fun a : ComplementPopulation L p => linePoints a.val) hc.symm))
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
    · let T := B.filter fun kc => kc.2 = c
      let xof (q : ↥T) : Point F :=
        Classical.choose ((mem_highShapePairs S L p q.val).mp
          (Finset.mem_filter.mp q.property).1).1
      have hxof (q : ↥T) : xof q ∈ S ∧
          Incidence (xof q) q.val.1.val ∧ Incidence (xof q) q.val.2.val :=
        Classical.choose_spec ((mem_highShapePairs S L p q.val).mp
          (Finset.mem_filter.mp q.property).1).1
      have hxc (q : ↥T) : Incidence (xof q) c.val := by
        have hq := (hxof q).2.2
        rw [(Finset.mem_filter.mp q.property).2] at hq
        exact hq
      let f : ↥T → ↥(S ∩ linePoints c.val) := fun q =>
        ⟨xof q, Finset.mem_inter.mpr
          ⟨(hxof q).1, (mem_linePoints (xof q) c.val).mpr (hxc q)⟩⟩
      have hf : Function.Injective f := by
        intro a b hab
        have hxy : xof a = xof b :=
          congrArg (fun z : ↥(S ∩ linePoints c.val) => z.val) hab
        apply Subtype.ext
        apply Prod.ext
        · apply pencil_eq_at_complement (xof a) L p c a.val.1 b.val.1
          · exact hxc a
          · exact (hxof a).2.1
          · rw [hxy]
            exact (hxof b).2.1
        · exact (Finset.mem_filter.mp a.property).2.trans
            (Finset.mem_filter.mp b.property).2.symm
      exact (Finset.card_le_card_of_injective hf).trans (hsparse c.val heq)
  have hsplit : B.card = ∑ c : ComplementPopulation L p,
      (B.filter fun kc => kc.2 = c).card :=
    Finset.card_eq_sum_card_fiberwise (f := Prod.snd)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  calc
    (highShapePairs S L p).card = ∑ c : ComplementPopulation L p,
        (B.filter fun kc => kc.2 = c).card := hsplit
    _ ≤ ∑ _c : ComplementPopulation L p, D := Finset.sum_le_sum fun c _ => hfiber c
    _ = D * (L \ coverPencil L p).card := by simp [ComplementPopulation, Nat.mul_comm]

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_HighOccupancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem highShapePairs_matching_of_large
    (S : Finset (Point F)) (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    (D h : ℕ) {t : ℕ} (s : HighSample L p t)
    (hsparse : ∀ l : AffineLine F, S ≠ linePoints l → (S ∩ linePoints l).card ≤ D)
    (hnot : S ∉ tupleShapes (highTuple L p s))
    (hlarge : 2 * D * h < (S ∩ crossPoints (highTuple L p s)).card) :
    ∃ i j : Fin h ↪ Fin t, ∀ k,
      (s.1 (i k), s.2 (j k)) ∈ highShapePairs S L p := by
  let P := S ∩ crossPoints (highTuple L p s)
  have hex (x : ↥P) : ∃ ij : Fin t × Fin t,
      Incidence x.val (s.1 ij.1).val ∧ Incidence x.val (s.2 ij.2).val := by
    obtain ⟨i, j, hi, hj⟩ :=
      (mem_crossPoints (highTuple L p s) x.val).mp (Finset.mem_inter.mp x.property).2
    exact ⟨(i, j), hi, hj⟩
  let rep : ↥P → Fin t × Fin t := fun x => Classical.choose (hex x)
  have hrep (x : ↥P) :
      Incidence x.val (s.1 (rep x).1).val ∧ Incidence x.val (s.2 (rep x).2).val :=
    Classical.choose_spec (hex x)
  have hnotleft (i : Fin t) : S ≠ linePoints (s.1 i).val := by
    intro he
    exact hnot ((mem_tupleShapes (highTuple L p s) S).mpr ⟨Sum.inl i, he.symm⟩)
  have hnotright (j : Fin t) : S ≠ linePoints (s.2 j).val := by
    intro he
    exact hnot ((mem_tupleShapes (highTuple L p s) S).mpr ⟨Sum.inr j, he.symm⟩)
  have hleft (i : Fin t) :
      (Finset.univ.filter fun x : ↥P => (rep x).1 = i).card ≤ D := by
    calc
      _ ≤ (S ∩ linePoints (s.1 i).val).card := by
        apply Finset.card_le_card_of_injOn (fun x : ↥P => x.val)
        · intro x hx
          have hxi := (Finset.mem_filter.mp hx).2
          refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp x.property).1, ?_⟩
          apply (mem_linePoints x.val (s.1 i).val).mpr
          simpa only [hxi] using (hrep x).1
        · intro x _ y _ hxy
          exact Subtype.ext hxy
      _ ≤ D := hsparse _ (hnotleft i)
  have hright (j : Fin t) :
      (Finset.univ.filter fun x : ↥P => (rep x).2 = j).card ≤ D := by
    calc
      _ ≤ (S ∩ linePoints (s.2 j).val).card := by
        apply Finset.card_le_card_of_injOn (fun x : ↥P => x.val)
        · intro x hx
          have hxj := (Finset.mem_filter.mp hx).2
          refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp x.property).1, ?_⟩
          apply (mem_linePoints x.val (s.2 j).val).mpr
          simpa only [hxj] using (hrep x).2
        · intro x _ y _ hxy
          exact Subtype.ext hxy
      _ ≤ D := hsparse _ (hnotright j)
  obtain ⟨e, hei, hej⟩ := exists_disjoint_coordinate_sample
    (Finset.univ : Finset ↥P) (fun x => (rep x).1) (fun x => (rep x).2)
    D h hleft hright (by simpa only [Finset.card_univ, Fintype.card_coe] using hlarge)
  let i : Fin h ↪ Fin t := ⟨fun k => (rep (e k).val).1, hei⟩
  let j : Fin h ↪ Fin t := ⟨fun k => (rep (e k).val).2, hej⟩
  refine ⟨i, j, ?_⟩
  intro k
  apply (mem_highShapePairs S L p (s.1 (i k), s.2 (j k))).mpr
  refine ⟨?_, hnotleft (i k), hnotright (j k)⟩
  exact ⟨(e k).val.val, (Finset.mem_inter.mp (e k).val.property).1,
    (hrep (e k).val).1, (hrep (e k).val).2⟩

theorem highSurvivorPoints_card_le
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    {t : ℕ} (s : HighSample L p t) :
    (X ∩ crossPoints (highTuple L p s)).card ≤ highSurvivorPairCount X L p s := by
  let P := X ∩ crossPoints (highTuple L p s)
  let Q := Finset.univ.filter fun ij : Fin t × Fin t =>
    (s.1 ij.1, s.2 ij.2) ∈ highCrossPairs X L p
  have hex (x : ↥P) : ∃ ij : Fin t × Fin t,
      Incidence x.val (s.1 ij.1).val ∧ Incidence x.val (s.2 ij.2).val := by
    obtain ⟨i, j, hi, hj⟩ :=
      (mem_crossPoints (highTuple L p s) x.val).mp (Finset.mem_inter.mp x.property).2
    exact ⟨(i, j), hi, hj⟩
  let rep : ↥P → Fin t × Fin t := fun x => Classical.choose (hex x)
  have hrep (x : ↥P) :
      Incidence x.val (s.1 (rep x).1).val ∧ Incidence x.val (s.2 (rep x).2).val :=
    Classical.choose_spec (hex x)
  let enc : ↥P → ↥Q := fun x => ⟨rep x, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (mem_highCrossPairs X L p _).mpr
      ⟨x.val, (Finset.mem_inter.mp x.property).1, (hrep x).1, (hrep x).2⟩⟩⟩
  have hinj : Function.Injective enc := by
    intro x y hxy
    have he : rep x = rep y := congrArg Subtype.val hxy
    have hy := hrep y
    rw [← he] at hy
    apply Subtype.ext
    exact eq_of_common_incidence_of_ne_lines
      (pencil_ne_complement L p (s.1 (rep x).1) (s.2 (rep x).2))
      (hrep x).1 (hrep x).2 hy.1 hy.2
  exact Finset.card_le_card_of_injective hinj

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_InjectionSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.InjectionSampling

universe u v w

theorem restriction_fiber_natCard_eq
    {I : Type u} {J : Type v} {Ω : Type w} [Finite I]
    (j : I ↪ J) (v₀ v₁ : I ↪ Ω) :
    Nat.card {sample : J ↪ Ω // restrict j sample = v₀} =
      Nat.card {sample : J ↪ Ω // restrict j sample = v₁} := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    v₀ v₁ v₀.injective v₁.injective
  let E : (J ↪ Ω) ≃ (J ↪ Ω) :=
    Equiv.embeddingCongr (Equiv.refl J) σ
  refine Nat.card_congr
    (E.subtypeEquiv
      (p := fun sample => restrict j sample = v₀)
      (q := fun sample => restrict j sample = v₁) ?_)
  intro sample
  constructor
  · intro hu
    apply Function.Embedding.ext
    intro i
    change σ (sample (j i)) = v₁ i
    have hi := congrArg (fun b : I ↪ Ω => b i) hu
    change sample (j i) = v₀ i at hi
    exact (congrArg σ hi).trans (hσ i)
  · intro hu
    apply Function.Embedding.ext
    intro i
    change sample (j i) = v₀ i
    apply σ.injective
    have hi := congrArg (fun b : I ↪ Ω => b i) hu
    change σ (sample (j i)) = v₁ i at hi
    exact hi.trans (hσ i).symm

theorem natCard_embeddings
    {A : Type u} {B : Type v} [Finite A] [Finite B] :
    Nat.card (A ↪ B) =
      (Nat.card B).descFactorial (Nat.card A) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Fintype B := Fintype.ofFinite B
  simpa only [Nat.card_eq_fintype_card] using
    (Fintype.card_embedding_eq (α := A) (β := B))

section Laws

variable {I : Type u} {J : Type v} {Ω : Type w}
  [Fintype I] [Fintype J] [Fintype Ω]

theorem map_uniform_restrict [Nonempty (J ↪ Ω)] [Nonempty (I ↪ Ω)]
    (j : I ↪ J) :
    (FiniteLaw.uniform (J ↪ Ω)).map (restrict j) =
      FiniteLaw.uniform (I ↪ Ω) :=
  FiniteLaw.map_uniform_of_fiber_card_eq (restrict j)
    (restriction_fiber_natCard_eq j)

theorem prob_restrict [Nonempty (J ↪ Ω)] [Nonempty (I ↪ Ω)]
    (j : I ↪ J) (P : (I ↪ Ω) → Prop) :
    (FiniteLaw.uniform (J ↪ Ω)).prob (fun sample => P (restrict j sample)) =
      (FiniteLaw.uniform (I ↪ Ω)).prob P := by
  calc
    _ = ((FiniteLaw.uniform (J ↪ Ω)).map (restrict j)).prob P :=
      (FiniteLaw.prob_map _ _ _).symm
    _ = _ := by rw [map_uniform_restrict j]

theorem map_uniform_coordinate [Nonempty (I ↪ Ω)] [Nonempty Ω] (i : I) :
    (FiniteLaw.uniform (I ↪ Ω)).map (fun sample => sample i) =
      FiniteLaw.uniform Ω := by
  classical
  apply FiniteLaw.map_uniform_of_fiber_card_eq
  intro a b
  let E : (I ↪ Ω) ≃ (I ↪ Ω) :=
    Equiv.embeddingCongr (Equiv.refl I) (Equiv.swap a b)
  refine Nat.card_congr
    (E.subtypeEquiv
      (p := fun sample => sample i = a)
      (q := fun sample => sample i = b) ?_)
  intro sample
  change sample i = a ↔ Equiv.swap a b (sample i) = b
  constructor
  · intro hu
    rw [hu, Equiv.swap_apply_left]
  · intro hu
    apply (Equiv.swap a b).injective
    simpa only [Equiv.swap_apply_left] using hu

theorem prob_coordinate [Nonempty (I ↪ Ω)] [Nonempty Ω]
    (i : I) (P : Ω → Prop) :
    (FiniteLaw.uniform (I ↪ Ω)).prob (fun sample => P (sample i)) =
      (FiniteLaw.uniform Ω).prob P := by
  calc
    _ = ((FiniteLaw.uniform (I ↪ Ω)).map (fun sample => sample i)).prob P :=
      (FiniteLaw.prob_map _ _ _).symm
    _ = _ := by rw [map_uniform_coordinate i]

theorem expectation_coordinate [Nonempty (I ↪ Ω)] [Nonempty Ω]
    (i : I) (f : Ω → ℝ) :
    (FiniteLaw.uniform (I ↪ Ω)).expectation (fun sample => f (sample i)) =
      (FiniteLaw.uniform Ω).expectation f := by
  calc
    _ = ((FiniteLaw.uniform (I ↪ Ω)).map (fun sample => sample i)).expectation f :=
      (FiniteLaw.expectation_map _ _ _).symm
    _ = _ := by rw [map_uniform_coordinate i]

end Laws

theorem law_eq_uniform (I : Type u) (Ω : Type v) [Fintype I] [Fintype Ω]
    [Nonempty (I ↪ Ω)] (hle : Nat.card I ≤ Nat.card Ω) :
    law I Ω hle = FiniteLaw.uniform (I ↪ Ω) := rfl

theorem law_prob (I : Type u) (Ω : Type v) [Fintype I] [Fintype Ω]
    (hle : Nat.card I ≤ Nat.card Ω) (P : (I ↪ Ω) → Prop) :
    (law I Ω hle).prob P =
      (Nat.card {sample : I ↪ Ω // P sample} : ℝ) /
        ((Nat.card Ω).descFactorial (Nat.card I) : ℝ) := by
  classical
  let : Nonempty (I ↪ Ω) := sample_nonempty I Ω hle
  simpa only [law_eq_uniform, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Fintype.card_embedding_eq] using
    (FiniteLaw.uniform_prob (I ↪ Ω) P)

variable {I : Type u} {J : Type v} {Ω : Type w}
  [Fintype I] [Fintype J] [Fintype Ω]

theorem prob_law_restrict (j : I ↪ J)
    (hJ : Nat.card J ≤ Nat.card Ω) (hI : Nat.card I ≤ Nat.card Ω)
    (P : (I ↪ Ω) → Prop) :
    (law J Ω hJ).prob (fun sample => P (restrict j sample)) =
      (law I Ω hI).prob P := by
  let : Nonempty (J ↪ Ω) := sample_nonempty J Ω hJ
  let : Nonempty (I ↪ Ω) := sample_nonempty I Ω hI
  simpa only [law_eq_uniform] using (prob_restrict j P)

end RyserCoveringCounterexample.InjectionSampling

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_TwoPopulationSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

open scoped BigOperators

namespace RyserCoveringCounterexample

namespace InjectionSampling

theorem card_pairSample_relation_le
    {A B : Type*} [Fintype A] [Fintype B]
    (S : Finset (A × B)) (h : ℕ) :
    Fintype.card {z : (Fin h ↪ A) × (Fin h ↪ B) //
      ∀ i, (z.1 i, z.2 i) ∈ S} ≤ S.card ^ h := by
  classical
  let enc : {z : (Fin h ↪ A) × (Fin h ↪ B) //
      ∀ i, (z.1 i, z.2 i) ∈ S} → (Fin h → ↥S) :=
    fun z i => ⟨(z.val.1 i, z.val.2 i), z.property i⟩
  have hinj : Function.Injective enc := by
    intro z w hzw
    apply Subtype.ext
    apply Prod.ext
    · apply Function.Embedding.ext
      intro i
      exact congrArg (fun f : Fin h → ↥S => (f i).val.1) hzw
    · apply Function.Embedding.ext
      intro i
      exact congrArg (fun f : Fin h → ↥S => (f i).val.2) hzw
  simpa only [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin] using
    Fintype.card_le_of_injective enc hinj

theorem prob_restrict_product
    {A B I J K L : Type*}
    [Fintype A] [Fintype B] [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    [Nonempty (J ↪ A)] [Nonempty (I ↪ A)]
    [Nonempty (L ↪ B)] [Nonempty (K ↪ B)]
    (i : I ↪ J) (j : K ↪ L) (P : (I ↪ A) × (K ↪ B) → Prop) :
    ((FiniteLaw.uniform (J ↪ A)).prod (FiniteLaw.uniform (L ↪ B))).prob
        (fun z => P (restrict i z.1, restrict j z.2)) =
      ((FiniteLaw.uniform (I ↪ A)).prod (FiniteLaw.uniform (K ↪ B))).prob P := by
  rw [FiniteLaw.prob_prod_average, FiniteLaw.prob_prod_average]
  calc
    _ = (FiniteLaw.uniform (J ↪ A)).expectation
        (fun a => (FiniteLaw.uniform (K ↪ B)).prob
          (fun b => P (restrict i a, b))) := by
      congr 1
      funext a
      exact prob_restrict j (fun b => P (restrict i a, b))
    _ = _ := by
      simpa only [FiniteLaw.expectation_map] using
        congrArg
          (fun mu : FiniteLaw (I ↪ A) => mu.expectation
            (fun a => (FiniteLaw.uniform (K ↪ B)).prob (fun b => P (a, b))))
          (map_uniform_restrict (Ω := A) i)

theorem prob_pairSample_relation_le
    {A B : Type*} [Fintype A] [Fintype B]
    (S : Finset (A × B)) (h : ℕ)
    [Nonempty (Fin h ↪ A)] [Nonempty (Fin h ↪ B)] :
    ((FiniteLaw.uniform (Fin h ↪ A)).prod (FiniteLaw.uniform (Fin h ↪ B))).prob
        (fun z => ∀ i, (z.1 i, z.2 i) ∈ S) ≤
      (S.card : ℝ) ^ h /
        ((Fintype.card A).descFactorial h * (Fintype.card B).descFactorial h : ℝ) := by
  classical
  rw [← FiniteLaw.uniform_prod, FiniteLaw.uniform_prob]
  have hfilter :
      @Finset.filter _ (fun z : (Fin h ↪ A) × (Fin h ↪ B) =>
          ∀ i, (z.1 i, z.2 i) ∈ S)
        (fun z => Classical.propDecidable (∀ i, (z.1 i, z.2 i) ∈ S)) Finset.univ =
      Finset.univ.filter (fun z : (Fin h ↪ A) × (Fin h ↪ B) =>
        ∀ i, (z.1 i, z.2 i) ∈ S) :=
    Finset.filter_congr_decidable _ _ _
  rw [hfilter]
  have hnat : (Finset.univ.filter (fun z : (Fin h ↪ A) × (Fin h ↪ B) =>
      ∀ i, (z.1 i, z.2 i) ∈ S)).card ≤ S.card ^ h := by
    simpa only [Fintype.card_subtype] using card_pairSample_relation_le S h
  have hreal : ((Finset.univ.filter (fun z : (Fin h ↪ A) × (Fin h ↪ B) =>
      ∀ i, (z.1 i, z.2 i) ∈ S)).card : ℝ) ≤ ((S.card ^ h : ℕ) : ℝ) :=
    Nat.cast_le.mpr hnat
  rw [Nat.cast_pow] at hreal
  simpa only [Fintype.card_prod, Fintype.card_embedding_eq, Fintype.card_fin,
    Nat.cast_mul] using
    (div_le_div_of_nonneg_right hreal
      (Nat.cast_nonneg (Fintype.card ((Fin h ↪ A) × (Fin h ↪ B))) :
        (0 : ℝ) ≤ (Fintype.card ((Fin h ↪ A) × (Fin h ↪ B)) : ℝ)))

theorem prob_restricted_relation_le
    {A B : Type*} [Fintype A] [Fintype B] {h t : ℕ}
    [Nonempty (Fin t ↪ A)] [Nonempty (Fin h ↪ A)]
    [Nonempty (Fin t ↪ B)] [Nonempty (Fin h ↪ B)]
    (S : Finset (A × B)) (i j : Fin h ↪ Fin t) :
    ((FiniteLaw.uniform (Fin t ↪ A)).prod (FiniteLaw.uniform (Fin t ↪ B))).prob
        (fun z => ∀ k, (z.1 (i k), z.2 (j k)) ∈ S) ≤
      (S.card : ℝ) ^ h /
        ((Fintype.card A).descFactorial h * (Fintype.card B).descFactorial h : ℝ) := by
  change ((FiniteLaw.uniform (Fin t ↪ A)).prod
      (FiniteLaw.uniform (Fin t ↪ B))).prob
      (fun z => (fun w : (Fin h ↪ A) × (Fin h ↪ B) =>
        ∀ k, (w.1 k, w.2 k) ∈ S) (restrict i z.1, restrict j z.2)) ≤ _
  rw [prob_restrict_product i j (fun w : (Fin h ↪ A) × (Fin h ↪ B) =>
    ∀ k, (w.1 k, w.2 k) ∈ S)]
  exact prob_pairSample_relation_le S h

theorem prob_relation_matching_le
    {A B : Type*} [Fintype A] [Fintype B] {h t : ℕ}
    [Nonempty (Fin t ↪ A)] [Nonempty (Fin h ↪ A)]
    [Nonempty (Fin t ↪ B)] [Nonempty (Fin h ↪ B)]
    (S : Finset (A × B)) :
    ((FiniteLaw.uniform (Fin t ↪ A)).prod (FiniteLaw.uniform (Fin t ↪ B))).prob
        (fun z => ∃ i j : Fin h ↪ Fin t, ∀ k, (z.1 (i k), z.2 (j k)) ∈ S) ≤
      (t.descFactorial h : ℝ) ^ 2 * (S.card : ℝ) ^ h /
        ((Fintype.card A).descFactorial h * (Fintype.card B).descFactorial h : ℝ) := by
  classical
  let mu := (FiniteLaw.uniform (Fin t ↪ A)).prod (FiniteLaw.uniform (Fin t ↪ B))
  calc
    _ ≤ ∑ i : Fin h ↪ Fin t,
        mu.prob (fun z => ∃ j : Fin h ↪ Fin t,
          ∀ k, (z.1 (i k), z.2 (j k)) ∈ S) :=
      mu.prob_exists_le _
    _ ≤ ∑ i : Fin h ↪ Fin t, ∑ j : Fin h ↪ Fin t,
        mu.prob (fun z => ∀ k, (z.1 (i k), z.2 (j k)) ∈ S) := by
      apply Finset.sum_le_sum
      intro i _
      exact mu.prob_exists_le _
    _ ≤ ∑ _i : Fin h ↪ Fin t, ∑ _j : Fin h ↪ Fin t,
        (S.card : ℝ) ^ h /
          ((Fintype.card A).descFactorial h * (Fintype.card B).descFactorial h : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact prob_restricted_relation_le S i j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_embedding_eq, Fintype.card_fin]
      ring

end InjectionSampling

end RyserCoveringCounterexample

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_TwoPopulationMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.InjectionSampling

theorem prob_product_average_right
    {A B : Type*} [Fintype A] [Fintype B]
    (mu : FiniteLaw A) (nu : FiniteLaw B) (P : A × B → Prop) :
    (mu.prod nu).prob P = nu.expectation (fun b => mu.prob (fun a => P (a, b))) := by
  rw [FiniteLaw.prob_prod_average]
  unfold FiniteLaw.expectation FiniteLaw.prob
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  by_cases hp : P (a, b) <;> simp [hp, mul_comm]

theorem prob_coordinate_product
    {A B I J : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J]
    [Nonempty A] [Nonempty B] [Nonempty (I ↪ A)] [Nonempty (J ↪ B)]
    (i : I) (j : J) (P : A × B → Prop) :
    ((FiniteLaw.uniform (I ↪ A)).prod (FiniteLaw.uniform (J ↪ B))).prob
        (fun z => P (z.1 i, z.2 j)) =
      ((FiniteLaw.uniform A).prod (FiniteLaw.uniform B)).prob P := by
  rw [FiniteLaw.prob_prod_average, FiniteLaw.prob_prod_average]
  calc
    _ = (FiniteLaw.uniform (I ↪ A)).expectation
        (fun a => (FiniteLaw.uniform B).prob (fun b => P (a i, b))) := by
      congr 1
      funext a
      exact prob_coordinate j (fun b => P (a i, b))
    _ = _ := expectation_coordinate i
      (fun a => (FiniteLaw.uniform B).prob (fun b => P (a, b)))

theorem prob_coordinate_pair_mem
    {A B I J : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J]
    [Nonempty A] [Nonempty B] [Nonempty (I ↪ A)] [Nonempty (J ↪ B)]
    (S : Finset (A × B)) (i : I) (j : J) :
    ((FiniteLaw.uniform (I ↪ A)).prod (FiniteLaw.uniform (J ↪ B))).prob
        (fun z => (z.1 i, z.2 j) ∈ S) =
      (S.card : ℝ) / ((Fintype.card A : ℝ) * Fintype.card B) := by
  rw [prob_coordinate_product, ← FiniteLaw.uniform_prod, FiniteLaw.uniform_prob]
  have hfilter : @Finset.filter _ (fun z => z ∈ S)
      (fun z => Classical.propDecidable (z ∈ S)) Finset.univ = S := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hfilter, Fintype.card_prod, Nat.cast_mul]

theorem expectation_relationCount
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    {t : ℕ} [Nonempty (Fin t ↪ A)] [Nonempty (Fin t ↪ B)]
    (S : Finset (A × B)) :
    ((FiniteLaw.uniform (Fin t ↪ A)).prod (FiniteLaw.uniform (Fin t ↪ B))).expectation
        (fun z => (relationCount S z : ℝ)) =
      (t : ℝ) ^ 2 * S.card / ((Fintype.card A : ℝ) * Fintype.card B) := by
  let mu := (FiniteLaw.uniform (Fin t ↪ A)).prod (FiniteLaw.uniform (Fin t ↪ B))
  have hcount (z : (Fin t ↪ A) × (Fin t ↪ B)) :
      (relationCount S z : ℝ) =
        ∑ ij : Fin t × Fin t, if (z.1 ij.1, z.2 ij.2) ∈ S then 1 else 0 :=
    Finset.natCast_card_filter _ _
  calc
    _ = mu.expectation (fun z =>
        ∑ ij : Fin t × Fin t, if (z.1 ij.1, z.2 ij.2) ∈ S then 1 else 0) := by
      congr 1
      funext z
      exact hcount z
    _ = ∑ ij : Fin t × Fin t,
        mu.expectation (fun z => if (z.1 ij.1, z.2 ij.2) ∈ S then 1 else 0) :=
      mu.expectation_sum _
    _ = ∑ ij : Fin t × Fin t,
        mu.prob (fun z => (z.1 ij.1, z.2 ij.2) ∈ S) := by
      apply Finset.sum_congr rfl
      intro ij _
      rw [FiniteLaw.prob_eq_expectation]
      congr 1
      funext z
      by_cases hz : (z.1 ij.1, z.2 ij.2) ∈ S <;> simp [hz]
    _ = ∑ _ij : Fin t × Fin t,
        (S.card : ℝ) / ((Fintype.card A : ℝ) * Fintype.card B) := by
      apply Finset.sum_congr rfl
      intro ij _
      exact prob_coordinate_pair_mem S ij.1 ij.2
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      ring

theorem prob_hits_finset_le
    {A : Type*} [Fintype A] [Nonempty A] {t : ℕ} [Nonempty (Fin t ↪ A)]
    (S : Finset A) :
    (FiniteLaw.uniform (Fin t ↪ A)).prob (fun z => ∃ i, z i ∈ S) ≤
      (t : ℝ) * S.card / Fintype.card A := by
  have hfilter : @Finset.filter _ (fun a => a ∈ S)
      (fun a => Classical.propDecidable (a ∈ S)) Finset.univ = S := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  calc
    _ ≤ ∑ i : Fin t, (FiniteLaw.uniform (Fin t ↪ A)).prob (fun z => z i ∈ S) :=
      (FiniteLaw.uniform (Fin t ↪ A)).prob_exists_le _
    _ = ∑ _i : Fin t, (S.card : ℝ) / Fintype.card A := by
      apply Finset.sum_congr rfl
      intro i _
      rw [prob_coordinate i, FiniteLaw.uniform_prob, hfilter]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end RyserCoveringCounterexample.InjectionSampling

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_HighProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem high_probability_large_survivorPairs
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    {t : ℕ} [Nonempty (PencilPopulation L p)] [Nonempty (ComplementPopulation L p)]
    [Nonempty (Fin t ↪ PencilPopulation L p)]
    [Nonempty (Fin t ↪ ComplementPopulation L p)]
    (δ : ℝ) (hδ : 0 < δ) (ht : 0 < t) :
    (highUniformLaw L p t).prob
        (fun s => δ * (t : ℝ) ^ 2 / 2 ≤ (highSurvivorPairCount X L p s : ℝ)) ≤
      2 * (overlapExcess Incidence X L : ℝ) /
        (δ * (coverPencil L p).card * (L \ coverPencil L p).card) := by
  have ht' : 0 < (t : ℝ) := Nat.cast_pos.mpr ht
  have hR : 0 < ((coverPencil L p).card : ℝ) := by
    simpa only [Fintype.card_coe] using
      (Nat.cast_pos.mpr (Fintype.card_pos (α := PencilPopulation L p)) :
        (0 : ℝ) < Fintype.card (PencilPopulation L p))
  have hN : 0 < ((L \ coverPencil L p).card : ℝ) := by
    simpa only [Fintype.card_coe] using
      (Nat.cast_pos.mpr (Fintype.card_pos (α := ComplementPopulation L p)) :
        (0 : ℝ) < Fintype.card (ComplementPopulation L p))
  have hthreshold : 0 < δ * (t : ℝ) ^ 2 / 2 :=
    div_pos (mul_pos hδ (pow_pos ht' 2)) (by norm_num)
  have hmean : (highUniformLaw L p t).expectation
      (fun s => (highSurvivorPairCount X L p s : ℝ)) =
      (t : ℝ) ^ 2 * (highCrossPairs X L p).card /
        ((coverPencil L p).card * (L \ coverPencil L p).card : ℝ) := by
    have hcount (s : HighSample L p t) :
        highSurvivorPairCount X L p s =
          InjectionSampling.relationCount (highCrossPairs X L p) s := by
      unfold highSurvivorPairCount InjectionSampling.relationCount
      apply congrArg Finset.card
      ext ij
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [hcount]
    simpa only [highUniformLaw, Fintype.card_coe] using
      (InjectionSampling.expectation_relationCount (highCrossPairs X L p) (t := t))
  have hcard : ((highCrossPairs X L p).card : ℝ) ≤
      (overlapExcess Incidence X L : ℝ) :=
    Nat.cast_le.mpr (highCrossPairs_card_le X L p)
  calc
    _ ≤ (highUniformLaw L p t).expectation
        (fun s => (highSurvivorPairCount X L p s : ℝ)) / (δ * (t : ℝ) ^ 2 / 2) :=
      (highUniformLaw L p t).prob_ge_le_expectation_div _
        (fun s => Nat.cast_nonneg _) hthreshold
    _ = 2 * (highCrossPairs X L p).card /
        (δ * (coverPencil L p).card * (L \ coverPencil L p).card) := by
      rw [hmean]
      field_simp [ne_of_gt hδ, ne_of_gt hR, ne_of_gt hN, ne_of_gt ht']

    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcard (by norm_num))
      (mul_nonneg (mul_nonneg hδ.le hR.le) hN.le)

theorem high_probability_badLines
    (L : Finset (AffineLine F)) (p : ProjectivePoint F) {t : ℕ}
    [Nonempty (PencilPopulation L p)]
    [Nonempty (Fin t ↪ PencilPopulation L p)]
    [Nonempty (Fin t ↪ ComplementPopulation L p)] :
    (highUniformLaw L p t).prob (fun s => ∃ i, s.1 i ∈ highBadLines L p s.2) ≤
      ((t : ℝ) ^ 2 + (t : ℝ) ^ 3) / (coverPencil L p).card := by
  rw [highUniformLaw, InjectionSampling.prob_product_average_right]
  calc
    _ ≤ (FiniteLaw.uniform (Fin t ↪ ComplementPopulation L p)).expectation
        (fun _ => (t : ℝ) * ((t : ℝ) + (t : ℝ) * t) / (coverPencil L p).card) := by
      apply FiniteLaw.expectation_mono
      intro b
      have hcard : ((highBadLines L p b).card : ℝ) ≤ ((t + t * t : ℕ) : ℝ) :=
        Nat.cast_le.mpr (highBadLines_card_le L p b)
      rw [Nat.cast_add, Nat.cast_mul] at hcard
      calc
        _ ≤ (t : ℝ) * (highBadLines L p b).card / (coverPencil L p).card := by
          simpa only [Fintype.card_coe] using
            InjectionSampling.prob_hits_finset_le (highBadLines L p b)
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    _ = _ := by
      rw [FiniteLaw.expectation_const]
      ring

theorem high_probability_occupancy
    (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    (shapes : Finset (Finset (Point F))) (D h : ℕ) {t : ℕ}
    [Nonempty (Fin t ↪ PencilPopulation L p)]
    [Nonempty (Fin t ↪ ComplementPopulation L p)]
    [Nonempty (Fin h ↪ PencilPopulation L p)]
    [Nonempty (Fin h ↪ ComplementPopulation L p)]
    (hsparse : SparseShapes shapes D) :
    (highUniformLaw L p t).prob (fun s => ∃ S ∈ shapes,
        S ∉ tupleShapes (highTuple L p s) ∧
          2 * D * h < (S ∩ crossPoints (highTuple L p s)).card) ≤
      (shapes.card : ℝ) * (t.descFactorial h : ℝ) ^ 2 *
        ((D * (L \ coverPencil L p).card : ℕ) : ℝ) ^ h /
        (((coverPencil L p).card.descFactorial h : ℝ) *
          ((L \ coverPencil L p).card.descFactorial h : ℝ)) := by
  let mu := highUniformLaw L p t
  have hone (S : ↥shapes) :
      mu.prob (fun s => ∃ i j : Fin h ↪ Fin t,
        ∀ k, (s.1 (i k), s.2 (j k)) ∈ highShapePairs S.val L p) ≤
        (t.descFactorial h : ℝ) ^ 2 *
          ((D * (L \ coverPencil L p).card : ℕ) : ℝ) ^ h /
          (((coverPencil L p).card.descFactorial h : ℝ) *
            ((L \ coverPencil L p).card.descFactorial h : ℝ)) := by
    have hcard : ((highShapePairs S.val L p).card : ℝ) ≤
        ((D * (L \ coverPencil L p).card : ℕ) : ℝ) :=
      Nat.cast_le.mpr (highShapePairs_card_le S.val L p D (hsparse S.val S.property))
    calc
      _ ≤ (t.descFactorial h : ℝ) ^ 2 * (highShapePairs S.val L p).card ^ h /
          (((coverPencil L p).card.descFactorial h : ℝ) *
            ((L \ coverPencil L p).card.descFactorial h : ℝ)) := by
        simpa only [mu, highUniformLaw, Fintype.card_coe] using
          (InjectionSampling.prob_relation_matching_le
            (highShapePairs S.val L p) (h := h) (t := t))
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard h) (sq_nonneg _))
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  calc
    _ ≤ mu.prob (fun s => ∃ S : ↥shapes, ∃ i j : Fin h ↪ Fin t,
        ∀ k, (s.1 (i k), s.2 (j k)) ∈ highShapePairs S.val L p) := by
      apply mu.prob_mono
      intro s hs
      obtain ⟨S, hS, hnot, hlarge⟩ := hs
      exact ⟨⟨S, hS⟩, highShapePairs_matching_of_large
        S L p D h s (hsparse S hS) hnot hlarge⟩
    _ ≤ ∑ S : ↥shapes, mu.prob (fun s => ∃ i j : Fin h ↪ Fin t,
        ∀ k, (s.1 (i k), s.2 (j k)) ∈ highShapePairs S.val L p) :=
      mu.prob_exists_le _
    _ ≤ ∑ _S : ↥shapes,
        (t.descFactorial h : ℝ) ^ 2 *
          ((D * (L \ coverPencil L p).card : ℕ) : ℝ) ^ h /
          (((coverPencil L p).card.descFactorial h : ℝ) *
            ((L \ coverPencil L p).card.descFactorial h : ℝ)) :=
      Finset.sum_le_sum (fun S _ => hone S)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      ring

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_HighConcurrency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem highConcurrency_exists_admissible
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    (shapes : Finset (Finset (Point F))) (D h t : ℕ) (δ : ℝ)
    (hsparse : SparseShapes shapes D) (hδ : 0 < δ)
    (hh : 1 ≤ h) (hht : h ≤ t)
    (htR : t ≤ (coverPencil L p).card)
    (htN : t ≤ (L \ coverPencil L p).card)
    (hfailure : highFailureBound X L p shapes D h t δ < 1) :
    ∃ a : LineTuple F t, (∀ k, a k ∈ L) ∧
      AdmissibleTuple shapes D h a ∧
        ((X ∩ crossPoints a).card : ℝ) < δ * (t : ℝ) ^ 2 / 2 := by
  have htpos : 0 < t := lt_of_lt_of_le Nat.zero_lt_one (hh.trans hht)
  let : Nonempty (PencilPopulation L p) := Fintype.card_pos_iff.mp
    (by simpa only [Fintype.card_coe] using (lt_of_lt_of_le htpos htR))
  let : Nonempty (ComplementPopulation L p) := Fintype.card_pos_iff.mp
    (by simpa only [Fintype.card_coe] using (lt_of_lt_of_le htpos htN))
  let : Nonempty (Fin t ↪ PencilPopulation L p) :=
    InjectionSampling.sample_nonempty (Fin t) (PencilPopulation L p)
      (by simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_coe] using htR)
  let : Nonempty (Fin t ↪ ComplementPopulation L p) :=
    InjectionSampling.sample_nonempty (Fin t) (ComplementPopulation L p)
      (by simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_coe] using htN)
  let : Nonempty (Fin h ↪ PencilPopulation L p) :=
    InjectionSampling.sample_nonempty (Fin h) (PencilPopulation L p)
      (by simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_coe]
        using hht.trans htR)
  let : Nonempty (Fin h ↪ ComplementPopulation L p) :=
    InjectionSampling.sample_nonempty (Fin h) (ComplementPopulation L p)
      (by simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_coe]
        using hht.trans htN)
  let mu := highUniformLaw L p t
  let BadSurvivors : HighSample L p t → Prop :=
    fun s => δ * (t : ℝ) ^ 2 / 2 ≤ (highSurvivorPairCount X L p s : ℝ)
  let BadGeometry : HighSample L p t → Prop :=
    fun s => ∃ i, s.1 i ∈ highBadLines L p s.2
  let BadOccupancy : HighSample L p t → Prop := fun s => ∃ S ∈ shapes,
    S ∉ tupleShapes (highTuple L p s) ∧
      2 * D * h < (S ∩ crossPoints (highTuple L p s)).card
  have hsurvivors := high_probability_large_survivorPairs X L p δ hδ htpos
  have hgeometry := high_probability_badLines L p (t := t)
  have hoccupancy := high_probability_occupancy L p shapes D h (t := t) hsparse
  have hbound : mu.prob (fun s => BadSurvivors s ∨ BadGeometry s ∨ BadOccupancy s) ≤
      highFailureBound X L p shapes D h t δ := by
    have hu := (mu.prob_union_le BadSurvivors (fun s => BadGeometry s ∨ BadOccupancy s)).trans
      (add_le_add hsurvivors
        ((mu.prob_union_le BadGeometry BadOccupancy).trans
          (add_le_add hgeometry hoccupancy)))
    simpa only [highFailureBound, add_assoc] using hu
  have hsmall := hbound.trans_lt hfailure
  have hex : ∃ s : HighSample L p t,
      ¬ (BadSurvivors s ∨ BadGeometry s ∨ BadOccupancy s) := by
    by_contra hn
    have hall (s : HighSample L p t) :
        BadSurvivors s ∨ BadGeometry s ∨ BadOccupancy s :=
      not_not.mp (fun hs => hn ⟨s, hs⟩)
    have heq : mu.prob (fun s => BadSurvivors s ∨ BadGeometry s ∨ BadOccupancy s) = 1 := by
      calc
        _ = mu.prob (fun _ => True) := by
          congr 1
          funext s
          exact propext ⟨fun _ => trivial, fun _ => hall s⟩
        _ = 1 := mu.prob_true
    rw [heq] at hsmall
    exact (lt_irrefl (1 : ℝ)) hsmall
  obtain ⟨s, hs⟩ := hex
  have havoid (i : Fin t) : s.1 i ∉ highBadLines L p s.2 := by
    intro hi
    exact hs (Or.inr (Or.inl ⟨i, hi⟩))
  have hgrid := highTuple_grid_of_avoids L p s havoid
  have hocc : ∀ S ∈ shapes, S ∉ tupleShapes (highTuple L p s) →
      (S ∩ crossPoints (highTuple L p s)).card ≤ 2 * D * h := by
    intro S hS hnot
    by_contra hlarge
    exact hs (Or.inr (Or.inr ⟨S, hS, hnot, lt_of_not_ge hlarge⟩))
  have hpair : (highSurvivorPairCount X L p s : ℝ) < δ * (t : ℝ) ^ 2 / 2 :=
    lt_of_not_ge (fun he => hs (Or.inl he))
  refine ⟨highTuple L p s, highTuple_mem L p s, ⟨hgrid.1, hgrid.2, hocc⟩, ?_⟩
  exact (Nat.cast_le.mpr (highSurvivorPoints_card_le X L p s)).trans_lt hpair

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_LowDegeneracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover.LowDegeneracy

open InjectionSampling

private theorem natCard_le_mul_of_fibers
    {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (R : ℕ)
    (h : ∀ b, Nat.card {a : A // f a = b} ≤ R) :
    Nat.card A ≤ Nat.card B * R := by
  classical
  calc
    Nat.card A = ∑ b : B, Nat.card {a : A // f a = b} := by
      rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f)]
      exact Nat.card_sigma
    _ ≤ ∑ _b : B, R := Finset.sum_le_sum (fun b _ => h b)
    _ = Nat.card B * R := by
      simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
        Nat.card_eq_fintype_card]

variable {F : Type*} [instFieldF : Field F] [instDecidableEqF : DecidableEq F]

theorem eq_pairMeet {L : Finset (AffineLine F)} (u : Fin 2 ↪ ↥L)
    {p : ProjectivePoint F}
    (h0 : ProjectiveIncidence p (some (u 0).val))
    (h1 : ProjectiveIncidence p (some (u 1).val)) : p = pairMeet u :=
  (Classical.choose_spec
    (existsUnique_projective_incident_of_ne_lines (pair_lines_ne u))).2 p ⟨h0, h1⟩

theorem card_sameDirection_le (L : Finset (AffineLine F)) (R : ℕ)
    (hR : ∀ d : Direction F, (L.filter fun l => l.1 = d).card ≤ R) :
    Nat.card {u : Fin 2 ↪ ↥L // SameDirection u} ≤ L.card * R := let _ := instFieldF; by
  classical
  let A := {u : Fin 2 ↪ ↥L // SameDirection u}
  let f : A → ↥L := fun u => u.val 0
  have hf : ∀ l, Nat.card {u : A // f u = l} ≤ R := by
    intro l
    let g : {u : A // f u = l} → ↥(L.filter fun k => k.1 = l.val.1) :=
      fun u => ⟨(u.val.val 1).val, Finset.mem_filter.mpr
        ⟨(u.val.val 1).property,
          u.val.property.symm.trans
            (congrArg (fun k : ↥L => k.val.1) u.property)⟩⟩
    have hg : Function.Injective g := by
      intro u v huv
      apply Subtype.ext
      apply Subtype.ext
      apply Function.Embedding.ext
      intro i
      fin_cases i
      · exact u.property.trans v.property.symm
      · apply Subtype.ext
        exact congrArg (fun z : ↥(L.filter fun k => k.1 = l.val.1) => z.val) huv
    exact (Nat.card_le_card_of_injective g hg).trans
      (by simpa only [Nat.card_eq_finsetCard] using hR l.val.1)
  simpa only [Nat.card_eq_finsetCard] using natCard_le_mul_of_fibers f R hf

theorem card_concurrent_le (L : Finset (AffineLine F)) (R : ℕ)
    (hR : ∀ p : ProjectivePoint F,
      (L.filter fun l => ProjectiveIncidence p (some l)).card ≤ R) :
    Nat.card {u : Fin 3 ↪ ↥L // Concurrent u} ≤
      L.card.descFactorial 2 * R := by
  classical
  let A := {u : Fin 3 ↪ ↥L // Concurrent u}
  let f : A → (Fin 2 ↪ ↥L) := fun u => firstPair u.val
  have hf : ∀ e, Nat.card {u : A // f u = e} ≤ R := by
    intro e
    let g : {u : A // f u = e} →
        ↥(L.filter fun l => ProjectiveIncidence (pairMeet e) (some l)) :=
      fun u => ⟨(u.val.val 2).val, by
        refine Finset.mem_filter.mpr ⟨(u.val.val 2).property, ?_⟩
        obtain ⟨p, hp⟩ := u.val.property
        have h0 : u.val.val 0 = e 0 :=
          congrArg (fun b : Fin 2 ↪ ↥L => b 0) u.property
        have h1 : u.val.val 1 = e 1 :=
          congrArg (fun b : Fin 2 ↪ ↥L => b 1) u.property
        have heq : p = pairMeet e := eq_pairMeet e
          (by rw [← h0]; exact hp 0) (by rw [← h1]; exact hp 1)
        exact heq ▸ hp 2⟩
    have hg : Function.Injective g := by
      intro u v huv
      have he : firstPair u.val.val = firstPair v.val.val :=
        u.property.trans v.property.symm
      apply Subtype.ext
      apply Subtype.ext
      apply Function.Embedding.ext
      intro i
      fin_cases i
      · exact congrArg (fun b : Fin 2 ↪ ↥L => b 0) he
      · exact congrArg (fun b : Fin 2 ↪ ↥L => b 1) he
      · apply Subtype.ext
        exact congrArg (fun z :
          ↥(L.filter fun l => ProjectiveIncidence (pairMeet e) (some l)) => z.val) huv
    exact (Nat.card_le_card_of_injective g hg).trans
      (by simpa only [Nat.card_eq_finsetCard] using hR (pairMeet e))
  simpa only [natCard_embeddings, Nat.card_fin, Nat.card_eq_finsetCard] using
    natCard_le_mul_of_fibers f R hf

private theorem prob_le_of_card
    {Ω : Type*} [Fintype Ω] (k R : ℕ)
    (hle : Nat.card (Fin (k + 1)) ≤ Nat.card Ω)
    (P : (Fin (k + 1) ↪ Ω) → Prop)
    (hcard : Nat.card {u : Fin (k + 1) ↪ Ω // P u} ≤
      (Nat.card Ω).descFactorial k * R) :
    (law (Fin (k + 1)) Ω hle).prob P ≤
      (R : ℝ) / ((Nat.card Ω - k : ℕ) : ℝ) := by
  have hk : k ≤ Nat.card Ω := by
    have h := hle
    rw [Nat.card_fin] at h
    omega
  have hn : ((Nat.card Ω).descFactorial k : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr hk).ne'
  rw [law_prob, Nat.card_fin]
  calc
    _ ≤ (((Nat.card Ω).descFactorial k * R : ℕ) : ℝ) /
        ((Nat.card Ω).descFactorial (k + 1) : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)
    _ = (R : ℝ) / ((Nat.card Ω - k : ℕ) : ℝ) := by
      rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_mul]
      rw [mul_comm (((Nat.card Ω - k : ℕ) : ℝ))
        (((Nat.card Ω).descFactorial k : ℝ))]
      exact mul_div_mul_left _ _ hn

theorem prob_sameDirection_le (L : Finset (AffineLine F)) (R : ℕ)
    (hL : 2 ≤ L.card)
    (hR : ∀ d : Direction F, (L.filter fun l => l.1 = d).card ≤ R) :
    (law (Fin 2) ↥L (by simpa using hL)).prob SameDirection ≤
      (R : ℝ) / ((L.card - 1 : ℕ) : ℝ) := by
  have hcard : Nat.card {u : Fin 2 ↪ ↥L // SameDirection u} ≤
      (Nat.card ↥L).descFactorial 1 * R := by
    simpa only [Nat.card_eq_finsetCard, Nat.descFactorial_one] using
      card_sameDirection_le L R hR
  simpa only [Nat.card_eq_finsetCard] using
    prob_le_of_card (Ω := ↥L) 1 R (by simpa using hL) SameDirection hcard

theorem prob_concurrent_le (L : Finset (AffineLine F)) (R : ℕ)
    (hL : 3 ≤ L.card)
    (hR : ∀ p : ProjectivePoint F,
      (L.filter fun l => ProjectiveIncidence p (some l)).card ≤ R) :
    (law (Fin 3) ↥L (by simpa using hL)).prob Concurrent ≤
      (R : ℝ) / ((L.card - 2 : ℕ) : ℝ) := by
  have hcard : Nat.card {u : Fin 3 ↪ ↥L // Concurrent u} ≤
      (Nat.card ↥L).descFactorial 2 * R := by
    simpa only [Nat.card_eq_finsetCard] using card_concurrent_le L R hR
  simpa only [Nat.card_eq_finsetCard] using
    prob_le_of_card (Ω := ↥L) 2 R (by simpa using hL) Concurrent hcard

theorem prob_exists_restrict_le
    {I Ω : Type*} [Fintype I] [Fintype Ω] (k : ℕ)
    (hI : Nat.card I ≤ Nat.card Ω) (hk : Nat.card (Fin k) ≤ Nat.card Ω)
    (P : (Fin k ↪ Ω) → Prop) (B : ℝ)
    (hP : (law (Fin k) Ω hk).prob P ≤ B) :
    (law I Ω hI).prob (fun u => ∃ j : Fin k ↪ I, P (restrict j u)) ≤
      ((Nat.card I).descFactorial k : ℝ) * B := by
  classical
  calc
    _ ≤ ∑ j : Fin k ↪ I, (law I Ω hI).prob (fun u => P (restrict j u)) :=
      FiniteLaw.prob_exists_le _ _
    _ = ∑ _j : Fin k ↪ I, (law (Fin k) Ω hk).prob P := by
      apply Finset.sum_congr rfl
      intro j _
      exact prob_law_restrict j hI hk P
    _ ≤ ∑ _j : Fin k ↪ I, B := Finset.sum_le_sum (fun _ _ => hP)
    _ = ((Nat.card I).descFactorial k : ℝ) * B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_embedding_eq, Fintype.card_fin, Nat.card_eq_fintype_card]

theorem anyParallel_iff {I : Type*} {L : Finset (AffineLine F)} (u : I ↪ ↥L) :
    AnyParallel u ↔ ∃ i j, i ≠ j ∧ (u i).val.1 = (u j).val.1 := let _ := instFieldF; let _ := instDecidableEqF; by
  classical
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j 0, j 1, fun h => (by decide : (0 : Fin 2) ≠ 1) (j.injective h), hj⟩
  · rintro ⟨i, j, hij, hdir⟩
    let e : Fin 2 ↪ I :=
      { toFun := ![i, j]
        inj' := by
          intro a b hab
          fin_cases a <;> fin_cases b <;> simp_all }
    exact ⟨e, hdir⟩

theorem anyConcurrent_iff {I : Type*} {L : Finset (AffineLine F)} (u : I ↪ ↥L) :
    AnyConcurrent u ↔ ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      ∃ p : ProjectivePoint F,
        ProjectiveIncidence p (some (u i).val) ∧
        ProjectiveIncidence p (some (u j).val) ∧
        ProjectiveIncidence p (some (u k).val) := let _ := instDecidableEqF; by
  classical
  constructor
  · rintro ⟨j, p, hp⟩
    refine ⟨j 0, j 1, j 2, ?_, ?_, ?_, p, hp 0, hp 1, hp 2⟩
    · exact fun h => (by decide : (0 : Fin 3) ≠ 1) (j.injective h)
    · exact fun h => (by decide : (0 : Fin 3) ≠ 2) (j.injective h)
    · exact fun h => (by decide : (1 : Fin 3) ≠ 2) (j.injective h)
  · rintro ⟨i, j, k, hij, hik, hjk, p, hi, hj, hk⟩
    let e : Fin 3 ↪ I :=
      { toFun := ![i, j, k]
        inj' := by
          intro a b hab
          fin_cases a <;> fin_cases b <;> simp_all }
    refine ⟨e, p, ?_⟩
    intro a
    fin_cases a
    · exact hi
    · exact hj
    · exact hk

theorem prob_anyParallel_le {I : Type*} [Fintype I]
    (L : Finset (AffineLine F)) (R : ℕ)
    (hI : Nat.card I ≤ Nat.card ↥L) (hL : 2 ≤ L.card)
    (hR : ∀ d : Direction F, (L.filter fun l => l.1 = d).card ≤ R) :
    (law I ↥L hI).prob AnyParallel ≤
      ((Nat.card I).descFactorial 2 : ℝ) * R / ((L.card - 1 : ℕ) : ℝ) := by
  have hevent : (AnyParallel : (I ↪ ↥L) → Prop) =
      (fun u => ∃ j : Fin 2 ↪ I, SameDirection (restrict j u)) := by
    funext u
    rfl
  rw [hevent]
  simpa only [mul_div_assoc] using
    prob_exists_restrict_le 2 hI (by simpa using hL) SameDirection
      ((R : ℝ) / ((L.card - 1 : ℕ) : ℝ)) (prob_sameDirection_le L R hL hR)

theorem prob_anyConcurrent_le {I : Type*} [Fintype I]
    (L : Finset (AffineLine F)) (R : ℕ)
    (hI : Nat.card I ≤ Nat.card ↥L) (hL : 3 ≤ L.card)
    (hR : ∀ p : ProjectivePoint F,
      (L.filter fun l => ProjectiveIncidence p (some l)).card ≤ R) :
    (law I ↥L hI).prob AnyConcurrent ≤
      ((Nat.card I).descFactorial 3 : ℝ) * R / ((L.card - 2 : ℕ) : ℝ) := by
  have hevent : (AnyConcurrent : (I ↪ ↥L) → Prop) =
      (fun u => ∃ j : Fin 3 ↪ I, Concurrent (restrict j u)) := by
    funext u
    rfl
  rw [hevent]
  simpa only [mul_div_assoc] using
    prob_exists_restrict_le 3 hI (by simpa using hL) Concurrent
      ((R : ℝ) / ((L.card - 2 : ℕ) : ℝ)) (prob_concurrent_le L R hL hR)

theorem prob_tuple_parallel_le (L : Finset (AffineLine F)) (t R : ℕ)
    (ht : 2 * t ≤ L.card) (hL : 2 ≤ L.card)
    (hR : ∀ d : Direction F, (L.filter fun l => l.1 = d).card ≤ R) :
    (law (Fin t ⊕ Fin t) ↥L (by simpa [Nat.card_sum, two_mul] using ht)).prob
        AnyParallel ≤
      ((2 * t).descFactorial 2 : ℝ) * R / ((L.card - 1 : ℕ) : ℝ) := by
  simpa only [Nat.card_sum, Nat.card_fin, ← two_mul] using
    prob_anyParallel_le (I := Fin t ⊕ Fin t) L R
      (by simpa [Nat.card_sum, two_mul] using ht) hL hR

theorem prob_tuple_concurrent_le (L : Finset (AffineLine F)) (t R : ℕ)
    (ht : 2 * t ≤ L.card) (hL : 3 ≤ L.card)
    (hR : ∀ p : ProjectivePoint F,
      (L.filter fun l => ProjectiveIncidence p (some l)).card ≤ R) :
    (law (Fin t ⊕ Fin t) ↥L (by simpa [Nat.card_sum, two_mul] using ht)).prob
        AnyConcurrent ≤
      ((2 * t).descFactorial 3 : ℝ) * R / ((L.card - 2 : ℕ) : ℝ) := by
  simpa only [Nat.card_sum, Nat.card_fin, ← two_mul] using
    prob_anyConcurrent_le (I := Fin t ⊕ Fin t) L R
      (by simpa [Nat.card_sum, two_mul] using ht) hL hR

end RyserCoveringCounterexample.LineCover.LowDegeneracy

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_PairSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

open scoped BigOperators

namespace RyserCoveringCounterexample.InjectionSampling

theorem card_disjoint_pair_assignments_le
    {Ω : Type*} [Fintype Ω] (B : Finset (Ω × Ω)) (h : ℕ) :
    Fintype.card {u : (Fin h ⊕ Fin h) ↪ Ω //
      ∀ k, (u (Sum.inl k), u (Sum.inr k)) ∈ B} ≤ B.card ^ h := by
  classical
  let encode : {u : (Fin h ⊕ Fin h) ↪ Ω //
      ∀ k, (u (Sum.inl k), u (Sum.inr k)) ∈ B} → (Fin h → ↥B) :=
    fun u k => ⟨(u.val (Sum.inl k), u.val (Sum.inr k)), u.property k⟩
  have hencode : Function.Injective encode := by
    intro u v huv
    apply Subtype.ext
    apply Function.Embedding.ext
    intro slot
    cases slot with
    | inl k => exact congrArg (fun f : Fin h → ↥B => (f k).val.1) huv
    | inr k => exact congrArg (fun f : Fin h → ↥B => (f k).val.2) huv
  simpa only [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin] using
    Fintype.card_le_of_injective encode hencode

theorem prob_disjoint_pairs_le
    {I Ω : Type*} [Fintype I] [Fintype Ω] [Nonempty (I ↪ Ω)]
    {h : ℕ} (j : (Fin h ⊕ Fin h) ↪ I) (B : Finset (Ω × Ω)) :
    (FiniteLaw.uniform (I ↪ Ω)).prob
        (fun u => ∀ k, (u (j (Sum.inl k)), u (j (Sum.inr k))) ∈ B) ≤
      (B.card : ℝ) ^ h /
        ((Fintype.card Ω).descFactorial (2 * h) : ℝ) := by
  classical
  let : Nonempty ((Fin h ⊕ Fin h) ↪ Ω) :=
    ⟨j.trans (Classical.choice (inferInstance : Nonempty (I ↪ Ω)))⟩
  let P : ((Fin h ⊕ Fin h) ↪ Ω) → Prop :=
    fun u => ∀ k, (u (Sum.inl k), u (Sum.inr k)) ∈ B
  change (FiniteLaw.uniform (I ↪ Ω)).prob (fun u => P (restrict j u)) ≤ _
  rw [prob_restrict j P, FiniteLaw.uniform_prob]
  have hfilter :
      @Finset.filter _ P (fun sample => Classical.propDecidable (P sample))
          Finset.univ = Finset.univ.filter P :=
    Finset.filter_congr_decidable _ _ _
  rw [hfilter]
  have hnat : (Finset.univ.filter P).card ≤ B.card ^ h := by
    simpa only [Fintype.card_subtype] using card_disjoint_pair_assignments_le B h
  have hreal : ((Finset.univ.filter P).card : ℝ) ≤ ((B.card ^ h : ℕ) : ℝ) :=
    Nat.cast_le.mpr hnat
  rw [Nat.cast_pow] at hreal
  calc
    _ ≤ (B.card : ℝ) ^ h / Fintype.card ((Fin h ⊕ Fin h) ↪ Ω) :=
      div_le_div_of_nonneg_right hreal (Nat.cast_nonneg _)
    _ = _ := by
      simp only [Fintype.card_embedding_eq, Fintype.card_sum, Fintype.card_fin,
        ← Nat.two_mul]

theorem prob_exists_disjoint_pairs_descFactorial_le
    {Ω : Type*} [Fintype Ω] {h t : ℕ}
    [Nonempty ((Fin t ⊕ Fin t) ↪ Ω)] (B : Finset (Ω × Ω)) :
    (FiniteLaw.uniform ((Fin t ⊕ Fin t) ↪ Ω)).prob
        (fun u => ∃ left right : Fin h ↪ Fin t,
          ∀ k, (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ B) ≤
      (t.descFactorial h : ℝ) ^ 2 * (B.card : ℝ) ^ h /
        ((Fintype.card Ω).descFactorial (2 * h) : ℝ) := by
  classical
  let μ := FiniteLaw.uniform ((Fin t ⊕ Fin t) ↪ Ω)
  calc
    _ ≤ ∑ left : Fin h ↪ Fin t,
        μ.prob (fun u => ∃ right : Fin h ↪ Fin t,
          ∀ k, (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ B) :=
      μ.prob_exists_le _
    _ ≤ ∑ left : Fin h ↪ Fin t, ∑ right : Fin h ↪ Fin t,
        μ.prob (fun u =>
          ∀ k, (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ B) := by
      apply Finset.sum_le_sum
      intro left _
      exact μ.prob_exists_le _
    _ ≤ ∑ _left : Fin h ↪ Fin t, ∑ _right : Fin h ↪ Fin t,
        (B.card : ℝ) ^ h /
          ((Fintype.card Ω).descFactorial (2 * h) : ℝ) := by
      apply Finset.sum_le_sum
      intro left _
      apply Finset.sum_le_sum
      intro right _
      exact prob_disjoint_pairs_le (Function.Embedding.sumMap left right) B
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_embedding_eq, Fintype.card_fin]
      ring

theorem prob_exists_disjoint_pairs_le
    {Ω : Type*} [Fintype Ω] {h t : ℕ}
    [Nonempty ((Fin t ⊕ Fin t) ↪ Ω)] (B : Finset (Ω × Ω)) :
    (FiniteLaw.uniform ((Fin t ⊕ Fin t) ↪ Ω)).prob
        (fun u => ∃ left right : Fin h ↪ Fin t,
          ∀ k, (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ B) ≤
      (t : ℝ) ^ (2 * h) * (B.card : ℝ) ^ h /
        ((Fintype.card Ω).descFactorial (2 * h) : ℝ) := by
  have hslots : (t.descFactorial h : ℝ) ≤ (t : ℝ) ^ h := by
    have hcast : (t.descFactorial h : ℝ) ≤ ((t ^ h : ℕ) : ℝ) :=
      Nat.cast_le.mpr (Nat.descFactorial_le_pow t h)
    simpa only [Nat.cast_pow] using hcast
  calc
    _ ≤ (t.descFactorial h : ℝ) ^ 2 * (B.card : ℝ) ^ h /
        ((Fintype.card Ω).descFactorial (2 * h) : ℝ) :=
      prob_exists_disjoint_pairs_descFactorial_le B
    _ ≤ ((t : ℝ) ^ h) ^ 2 * (B.card : ℝ) ^ h /
        ((Fintype.card Ω).descFactorial (2 * h) : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hslots 2)
        (pow_nonneg (Nat.cast_nonneg _) h)
    _ = _ := by rw [← pow_mul, Nat.mul_comm h 2]

end RyserCoveringCounterexample.InjectionSampling

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_SamplingDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [instFieldF : Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F]

theorem liftSample_mem (L : Finset (AffineLine F)) {t : ℕ}
    (u : CoverSample L t) (i : Fin t ⊕ Fin t) : liftSample L u i ∈ L := let _ := instFieldF; let _ := instFintypeF; let _ := instDecidableEqF;
  (u i).property

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_LowOccupancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem card_shapePairs_le
    (shapes : Finset (Finset (Point F))) (L : Finset (AffineLine F))
    {D R : ℕ} (hSparse : SparseShapes shapes D)
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R)
    {S : Finset (Point F)} (hS : S ∈ shapes) :
    (shapePairs L S).card ≤ L.card * D * R := by
  classical
  have hfiber (a : ↥L) :
      ((shapePairs L S).filter fun p => p.1 = a).card ≤ D * R := by
    by_cases ha : S = linePoints a.val
    · have hempty : (shapePairs L S).filter (fun p => p.1 = a) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro p hp hpa
        have hne := ((mem_shapePairs L S p).mp hp).2.1
        apply hne
        simpa only [hpa] using ha
      simp only [hempty, Finset.card_empty, Nat.zero_le]
    · let C := S ∩ linePoints a.val
      let pool := C.biUnion fun x => coverPencil L (Sum.inl x)
      calc
        ((shapePairs L S).filter fun p => p.1 = a).card ≤ pool.card := by
          apply Finset.card_le_card_of_injOn (fun p : ↥L × ↥L => p.2.val)
          · intro p hp
            have hpa := (Finset.mem_filter.mp hp).2
            obtain ⟨_, _, _, x, hx, hfirst, hsecond⟩ :=
              (mem_shapePairs L S p).mp (Finset.mem_filter.mp hp).1
            apply Finset.mem_biUnion.mpr
            refine ⟨x, Finset.mem_inter.mpr ⟨hx, ?_⟩, ?_⟩
            · apply (mem_linePoints x a.val).mpr
              simpa only [hpa] using hfirst
            · exact (mem_coverPencil L (Sum.inl x) p.2.val).mpr
                ⟨p.2.property, hsecond⟩
          · intro p hp q hq hpq
            apply Prod.ext
            · exact (Finset.mem_filter.mp hp).2.trans
                (Finset.mem_filter.mp hq).2.symm
            · exact Subtype.ext hpq
        _ ≤ ∑ x ∈ C, (coverPencil L (Sum.inl x)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _x ∈ C, R := Finset.sum_le_sum fun x _ => hR (Sum.inl x)
        _ = C.card * R := by simp only [Finset.sum_const, Nat.nsmul_eq_mul]
        _ ≤ D * R := Nat.mul_le_mul_right R (hSparse S hS a.val ha)
  calc
    (shapePairs L S).card =
        ∑ a : ↥L, ((shapePairs L S).filter fun p => p.1 = a).card :=
      Finset.card_eq_sum_card_fiberwise
        (s := shapePairs L S) (t := Finset.univ) (f := Prod.fst)
        (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _a : ↥L, D * R := Finset.sum_le_sum fun a _ => hfiber a
    _ = L.card * D * R := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        Nat.nsmul_eq_mul, Nat.mul_assoc]

theorem shape_ne_linePoints_of_not_mem_tupleShapes
    {t : ℕ} (a : LineTuple F t) {S : Finset (Point F)}
    (hS : S ∉ tupleShapes a) (slot : Fin t ⊕ Fin t) :
    S ≠ linePoints (a slot) := by
  intro heq
  exact hS ((mem_tupleShapes a S).mpr ⟨slot, heq.symm⟩)

theorem exists_disjoint_shapePairs_of_occupancy
    (shapes : Finset (Finset (Point F))) (L : Finset (AffineLine F))
    {D h t : ℕ} (hSparse : SparseShapes shapes D)
    {S : Finset (Point F)} (hS : S ∈ shapes) (u : CoverSample L t)
    (hnot : S ∉ tupleShapes (liftSample L u))
    (hlarge : 2 * D * h < (S ∩ crossPoints (liftSample L u)).card) :
    ∃ left right : Fin h ↪ Fin t, ∀ k,
      (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ shapePairs L S := by
  classical
  let a := liftSample L u
  let C := S ∩ crossPoints a
  have hrepr (x : ↥C) : ∃ i j : Fin t,
      Incidence x.val (a (Sum.inl i)) ∧ Incidence x.val (a (Sum.inr j)) :=
    (mem_crossPoints a x.val).mp (Finset.mem_inter.mp x.property).2
  let left : ↥C → Fin t := fun x => Classical.choose (hrepr x)
  let right : ↥C → Fin t :=
    fun x => Classical.choose (Classical.choose_spec (hrepr x))
  have hinc (x : ↥C) :
      Incidence x.val (a (Sum.inl (left x))) ∧
        Incidence x.val (a (Sum.inr (right x))) :=
    Classical.choose_spec (Classical.choose_spec (hrepr x))
  have hne (slot : Fin t ⊕ Fin t) : S ≠ linePoints (a slot) :=
    shape_ne_linePoints_of_not_mem_tupleShapes a hnot slot
  have hfiber (coord : ↥C → Fin t) (side : Fin t → Fin t ⊕ Fin t)
      (hcoord : ∀ x : ↥C, Incidence x.val (a (side (coord x)))) (i : Fin t) :
      ((Finset.univ : Finset ↥C).filter fun x => coord x = i).card ≤ D := by
    calc
      _ ≤ (S ∩ linePoints (a (side i))).card := by
        apply Finset.card_le_card_of_injOn (fun x : ↥C => x.val)
        · intro x hx
          refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp x.property).1, ?_⟩
          apply (mem_linePoints x.val (a (side i))).mpr
          simpa only [(Finset.mem_filter.mp hx).2] using hcoord x
        · intro x _ y _ hxy
          exact Subtype.ext hxy
      _ ≤ D := hSparse S hS (a (side i)) (hne (side i))
  have hlarge' : 2 * D * h < (Finset.univ : Finset ↥C).card := by
    simpa only [Finset.card_univ, Fintype.card_coe] using hlarge
  obtain ⟨e, hleft, hright⟩ := exists_disjoint_coordinate_sample
    (Finset.univ : Finset ↥C) left right D h
    (hfiber left Sum.inl (fun x => (hinc x).1))
    (hfiber right Sum.inr (fun x => (hinc x).2)) hlarge'
  let i : Fin h ↪ Fin t := ⟨fun k => left (e k).val, hleft⟩
  let j : Fin h ↪ Fin t := ⟨fun k => right (e k).val, hright⟩
  refine ⟨i, j, ?_⟩
  intro k
  let x : ↥C := (e k).val
  apply (mem_shapePairs L S _).mpr
  refine ⟨?_, hne (Sum.inl (i k)), hne (Sum.inr (j k)),
    x.val, (Finset.mem_inter.mp x.property).1, (hinc x).1, (hinc x).2⟩
  intro heq
  have hslots := u.injective heq
  cases hslots

theorem prob_shape_occupancy_le
    (shapes : Finset (Finset (Point F))) (L : Finset (AffineLine F))
    {D R h t : ℕ} [Nonempty (CoverSample L t)]
    (hSparse : SparseShapes shapes D)
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R)
    {S : Finset (Point F)} (hS : S ∈ shapes) :
    (FiniteLaw.uniform (CoverSample L t)).prob (fun u =>
      S ∉ tupleShapes (liftSample L u) ∧
        2 * D * h < (S ∩ crossPoints (liftSample L u)).card) ≤
      (t : ℝ) ^ (2 * h) * ((L.card * D * R : ℕ) : ℝ) ^ h /
        (L.card.descFactorial (2 * h) : ℝ) := by
  classical
  let μ := FiniteLaw.uniform (CoverSample L t)
  have hcard : ((shapePairs L S).card : ℝ) ≤ ((L.card * D * R : ℕ) : ℝ) :=
    Nat.cast_le.mpr (card_shapePairs_le shapes L hSparse hR hS)
  calc
    _ ≤ μ.prob (fun u => ∃ left right : Fin h ↪ Fin t, ∀ k,
        (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ shapePairs L S) := by
      apply μ.prob_mono
      intro u hu
      exact exists_disjoint_shapePairs_of_occupancy shapes L hSparse hS u hu.1 hu.2
    _ ≤ (t : ℝ) ^ (2 * h) * ((shapePairs L S).card : ℝ) ^ h /
        (L.card.descFactorial (2 * h) : ℝ) := by
      simpa only [Fintype.card_coe] using
        (InjectionSampling.prob_exists_disjoint_pairs_le
          (h := h) (t := t) (shapePairs L S))
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard h)
        (pow_nonneg (Nat.cast_nonneg _) (2 * h))

theorem prob_bad_occupancy_le
    (shapes : Finset (Finset (Point F))) (L : Finset (AffineLine F))
    {D R h t : ℕ} [Nonempty (CoverSample L t)]
    (hSparse : SparseShapes shapes D)
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R) :
    (FiniteLaw.uniform (CoverSample L t)).prob (fun u =>
      ∃ S ∈ shapes, S ∉ tupleShapes (liftSample L u) ∧
        2 * D * h < (S ∩ crossPoints (liftSample L u)).card) ≤
      (shapes.card : ℝ) * (t : ℝ) ^ (2 * h) * ((L.card * D * R : ℕ) : ℝ) ^ h /
        (L.card.descFactorial (2 * h) : ℝ) := by
  classical
  let μ := FiniteLaw.uniform (CoverSample L t)
  calc
    _ = μ.prob (fun u => ∃ S : ↥shapes,
        S.val ∉ tupleShapes (liftSample L u) ∧
          2 * D * h < (S.val ∩ crossPoints (liftSample L u)).card) := by
      congr 1
      funext u
      apply propext
      constructor
      · rintro ⟨S, hS, hbad⟩
        exact ⟨⟨S, hS⟩, hbad⟩
      · rintro ⟨S, hbad⟩
        exact ⟨S.val, S.property, hbad⟩
    _ ≤ ∑ S : ↥shapes, μ.prob (fun u =>
        S.val ∉ tupleShapes (liftSample L u) ∧
          2 * D * h < (S.val ∩ crossPoints (liftSample L u)).card) :=
      μ.prob_exists_le _
    _ ≤ ∑ _S : ↥shapes,
        (t : ℝ) ^ (2 * h) * ((L.card * D * R : ℕ) : ℝ) ^ h /
          (L.card.descFactorial (2 * h) : ℝ) := by
      apply Finset.sum_le_sum
      intro S _
      exact prob_shape_occupancy_le shapes L hSparse hR S.property
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      ring

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_PairCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F]

theorem mem_survivorPairs (X : Finset (Point F)) (L : Finset (AffineLine F))
    (a b : AffineLine F) :
    (a, b) ∈ survivorPairs X L ↔
      a ∈ L ∧ b ∈ L ∧ a ≠ b ∧ ∃ x ∈ X, Incidence x a ∧ Incidence x b := by
  simp only [survivorPairs, Finset.mem_biUnion, Finset.mem_offDiag,
    Finset.mem_filter]
  constructor
  · rintro ⟨x, hx, ⟨ha, hxa⟩, ⟨hb, hxb⟩, hab⟩
    exact ⟨ha, hb, hab, x, hx, hxa, hxb⟩
  · rintro ⟨ha, hb, hab, x, hx, hxa, hxb⟩
    exact ⟨x, hx, ⟨ha, hxa⟩, ⟨hb, hxb⟩, hab⟩

theorem survivorPairs_fibers_disjoint
    (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    (X : Set (Point F)).PairwiseDisjoint
      (fun x => (L.filter (Incidence x)).offDiag) := by
  intro x _ y _ hxy
  apply Finset.disjoint_left.mpr
  intro p hx hy
  obtain ⟨hxa, hxb, hab⟩ := Finset.mem_offDiag.mp hx
  obtain ⟨hya, hyb, _⟩ := Finset.mem_offDiag.mp hy
  apply hxy
  exact eq_of_common_incidence_of_ne_lines hab
    (Finset.mem_filter.mp hxa).2 (Finset.mem_filter.mp hxb).2
    (Finset.mem_filter.mp hya).2 (Finset.mem_filter.mp hyb).2

theorem card_survivorPairs (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    (survivorPairs X L).card =
      ∑ x ∈ X, (L.filter (Incidence x)).card *
        ((L.filter (Incidence x)).card - 1) := by
  rw [survivorPairs, Finset.card_biUnion (survivorPairs_fibers_disjoint X L)]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Finset.offDiag_card, Nat.mul_sub_left_distrib, Nat.mul_one]

theorem card_survivorPairs_eq_orderedPairMass
    (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    (survivorPairs X L).card = orderedPairMass Incidence X L := by
  rw [card_survivorPairs]
  unfold orderedPairMass multiplicity
  apply Finset.sum_congr rfl
  intro x _
  apply congrArg (fun n : ℕ => n * (n - 1))
  apply congrArg Finset.card
  ext l
  simp only [Finset.mem_filter]

theorem mem_populationSurvivorPairs
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (p : ↥L × ↥L) :
    p ∈ populationSurvivorPairs X L ↔
      p.1 ≠ p.2 ∧ ∃ x ∈ X, Incidence x p.1.val ∧ Incidence x p.2.val := by
  simp only [populationSurvivorPairs, Finset.mem_filter, Finset.mem_univ,
    true_and, mem_survivorPairs, p.1.property, p.2.property]
  exact and_congr (not_congr Subtype.val_inj) Iff.rfl

theorem card_populationSurvivorPairs
    (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    (populationSurvivorPairs X L).card = (survivorPairs X L).card := by
  apply Finset.card_bij (fun p _ => (p.1.val, p.2.val))
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro p _ q _ hpq
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hpq)
    · exact Subtype.ext (congrArg Prod.snd hpq)
  · intro p hp
    have hm := (mem_survivorPairs X L p.1 p.2).mp hp
    refine ⟨(⟨p.1, hm.1⟩, ⟨p.2, hm.2.1⟩), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩

theorem card_populationSurvivorPairs_eq_orderedPairMass
    (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    (populationSurvivorPairs X L).card = orderedPairMass Incidence X L := by
  rw [card_populationSurvivorPairs, card_survivorPairs_eq_orderedPairMass]

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_SurvivorSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F]

theorem card_cross_survivors_le_hitCount (X : Finset (Point F))
    {t : ℕ} (a : LineTuple F t) :
    (X ∩ crossPoints a).card ≤ crossHitCount X a := by
  classical
  let S := X ∩ crossPoints a
  have hex (x : ↥S) : ∃ p : Fin t × Fin t,
      Incidence x.val (a (Sum.inl p.1)) ∧ Incidence x.val (a (Sum.inr p.2)) := by
    obtain ⟨i, j, hi, hj⟩ :=
      (mem_crossPoints a x.val).mp (Finset.mem_inter.mp x.property).2
    exact ⟨(i, j), hi, hj⟩
  let rep (x : ↥S) : Fin t × Fin t := Classical.choose (hex x)
  have hrep (x : ↥S) :
      Incidence x.val (a (Sum.inl (rep x).1)) ∧
        Incidence x.val (a (Sum.inr (rep x).2)) := Classical.choose_spec (hex x)
  let encode : ↥S → {p : Fin t × Fin t // CrossHit X a p} := fun x =>
    ⟨rep x, x.val, (Finset.mem_inter.mp x.property).1, (hrep x).1, (hrep x).2⟩
  have hinj : Function.Injective encode := by
    intro x y hxy
    have hp : rep x = rep y := congrArg Subtype.val hxy
    apply Subtype.ext
    exact eq_of_common_incidence_of_ne_lines (left_ne_right a (rep x).1 (rep x).2)
      (hrep x).1 (hrep x).2
      (by simpa only [hp] using (hrep y).1)
      (by simpa only [hp] using (hrep y).2)
  calc
    (X ∩ crossPoints a).card = Fintype.card ↥S := (Fintype.card_coe S).symm
    _ ≤ Fintype.card {p : Fin t × Fin t // CrossHit X a p} :=
      Fintype.card_le_of_injective encode hinj
    _ = crossHitCount X a := by
      rw [Fintype.card_subtype]
      unfold crossHitCount
      apply congrArg Finset.card
      ext p
      simp only [Finset.mem_filter]

theorem crossHitCount_eq_sum (X : Finset (Point F)) {t : ℕ}
    (a : LineTuple F t) :
    (crossHitCount X a : ℝ) =
      ∑ p : Fin t × Fin t, if CrossHit X a p then (1 : ℝ) else 0 := let _ := instFintypeF; let _ := instDecidableEqF; by
  exact Finset.natCast_card_filter (CrossHit X a) Finset.univ

theorem prob_crossHit_le (X : Finset (Point F)) (L : Finset (AffineLine F))
    {t : ℕ} [Nonempty (CoverSample L t)] (p : Fin t × Fin t) :
    (FiniteLaw.uniform (CoverSample L t)).prob
        (fun u => CrossHit X (liftSample L u) p) ≤
      (orderedPairMass Incidence X L : ℝ) / (L.card.descFactorial 2 : ℝ) := let _ := instFintypeF; let _ := instDecidableEqF; by
  classical
  let left : Fin 1 ↪ Fin t := ⟨fun _ => p.1, fun _ _ _ => Subsingleton.elim _ _⟩
  let right : Fin 1 ↪ Fin t := ⟨fun _ => p.2, fun _ _ _ => Subsingleton.elim _ _⟩
  have h := InjectionSampling.prob_disjoint_pairs_le
    (Function.Embedding.sumMap left right) (populationSurvivorPairs X L)
  have hevent :
      (fun u : CoverSample L t => ∀ k : Fin 1,
        (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ populationSurvivorPairs X L) =
        (fun u => CrossHit X (liftSample L u) p) := by
    funext u
    apply propext
    have hne : u (Sum.inl p.1) ≠ u (Sum.inr p.2) := by
      intro heq
      exact Sum.inl_ne_inr (u.injective heq)
    change (∀ _k : Fin 1,
      (u (Sum.inl p.1), u (Sum.inr p.2)) ∈ populationSurvivorPairs X L) ↔ _
    constructor
    · intro hu
      exact ((mem_populationSurvivorPairs X L _).mp (hu 0)).2
    · intro hu _k
      exact (mem_populationSurvivorPairs X L _).mpr ⟨hne, hu⟩
  change (FiniteLaw.uniform (CoverSample L t)).prob
      (fun u => ∀ k : Fin 1,
        (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ populationSurvivorPairs X L) ≤ _ at h
  rw [hevent] at h
  simpa only [pow_one, Nat.mul_one, Fintype.card_coe,
    card_populationSurvivorPairs_eq_orderedPairMass] using h

theorem expectation_crossHitCount_le
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    {t : ℕ} [Nonempty (CoverSample L t)] :
    (FiniteLaw.uniform (CoverSample L t)).expectation
        (fun u => (crossHitCount X (liftSample L u) : ℝ)) ≤
      (t : ℝ) ^ 2 * (orderedPairMass Incidence X L : ℝ) /
        (L.card.descFactorial 2 : ℝ) := by
  let μ := FiniteLaw.uniform (CoverSample L t)
  calc
    _ = μ.expectation (fun u => ∑ p : Fin t × Fin t,
        if CrossHit X (liftSample L u) p then (1 : ℝ) else 0) := by
      congr 1
      funext u
      exact crossHitCount_eq_sum X (liftSample L u)
    _ = ∑ p : Fin t × Fin t, μ.expectation
        (fun u => if CrossHit X (liftSample L u) p then (1 : ℝ) else 0) :=
      μ.expectation_sum _
    _ = ∑ p : Fin t × Fin t, μ.prob (fun u => CrossHit X (liftSample L u) p) := by
      apply Finset.sum_congr rfl
      intro p _
      exact (μ.prob_eq_expectation _).symm
    _ ≤ ∑ _p : Fin t × Fin t,
        (orderedPairMass Incidence X L : ℝ) / (L.card.descFactorial 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro p _
      exact prob_crossHit_le X L p
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      ring

theorem prob_many_cross_survivors_le
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    {t : ℕ} [Nonempty (CoverSample L t)] {δ : ℝ} (hδ : 0 < δ) (ht : 0 < t) :
    (FiniteLaw.uniform (CoverSample L t)).prob
        (fun u => δ * (t : ℝ) ^ 2 / 2 ≤
          ((X ∩ crossPoints (liftSample L u)).card : ℝ)) ≤
      2 * (orderedPairMass Incidence X L : ℝ) /
        (δ * (L.card.descFactorial 2 : ℝ)) := by
  let μ := FiniteLaw.uniform (CoverSample L t)
  have htR : 0 < (t : ℝ) := Nat.cast_pos.mpr ht
  have hthreshold : 0 < δ * (t : ℝ) ^ 2 / 2 := by positivity
  calc
    _ ≤ μ.prob (fun u => δ * (t : ℝ) ^ 2 / 2 ≤
        (crossHitCount X (liftSample L u) : ℝ)) := by
      apply μ.prob_mono
      intro u hu
      exact hu.trans (Nat.cast_le.mpr (card_cross_survivors_le_hitCount X _))
    _ ≤ μ.expectation (fun u => (crossHitCount X (liftSample L u) : ℝ)) /
        (δ * (t : ℝ) ^ 2 / 2) :=
      μ.prob_ge_le_expectation_div _ (fun _ => Nat.cast_nonneg _) hthreshold
    _ ≤ ((t : ℝ) ^ 2 * (orderedPairMass Incidence X L : ℝ) /
        (L.card.descFactorial 2 : ℝ)) / (δ * (t : ℝ) ^ 2 / 2) :=
      div_le_div_of_nonneg_right (expectation_crossHitCount_le X L) hthreshold.le
    _ = _ := by
      by_cases hden : (L.card.descFactorial 2 : ℝ) = 0
      · simp only [hden, div_zero, mul_zero, zero_div]
      · field_simp [hδ.ne', htR.ne', hden]

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_TupleGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F] {t : ℕ}

theorem finiteCrossings_of_no_parallel (a : LineTuple F t) (h : NoParallel a) :
    FiniteCrossings a := let _ := instFintypeF; let _ := instDecidableEqF; by
  intro i j
  exact (existsUnique_incident_of_ne_direction (a (Sum.inl i)) (a (Sum.inr j))
    (h _ _ (by intro he; cases he))).exists

theorem crossPoints_eq_image_grid (a : LineTuple F t)
    (g : Fin t × Fin t → Point F)
    (hg : ∀ ij, Incidence (g ij) (a (Sum.inl ij.1)) ∧
      Incidence (g ij) (a (Sum.inr ij.2))) :
    crossPoints a = Finset.univ.image g := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, j, hi, hj⟩ := (mem_crossPoints a x).mp hx
    apply Finset.mem_image.mpr
    refine ⟨(i, j), Finset.mem_univ _, ?_⟩
    exact eq_of_common_incidence_of_ne_lines (left_ne_right a i j)
      (hg (i, j)).1 (hg (i, j)).2 hi hj
  · intro hx
    obtain ⟨ij, _, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_crossPoints a (g ij)).mpr ⟨ij.1, ij.2, (hg ij).1, (hg ij).2⟩

theorem crossPoints_card_of_grid (a : LineTuple F t)
    (g : Fin t × Fin t → Point F)
    (hg : ∀ ij, Incidence (g ij) (a (Sum.inl ij.1)) ∧
      Incidence (g ij) (a (Sum.inr ij.2)))
    (hinj : Function.Injective g) : (crossPoints a).card = t * t := by
  rw [crossPoints_eq_image_grid a g hg, Finset.card_image_of_injective _ hinj]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]

theorem grid_injective_of_no_concurrentTriple (a : LineTuple F t)
    (g : Fin t × Fin t → Point F)
    (hg : ∀ ij, Incidence (g ij) (a (Sum.inl ij.1)) ∧
      Incidence (g ij) (a (Sum.inr ij.2)))
    (h : NoConcurrentTriple a) : Function.Injective g := let _ := instFintypeF; let _ := instDecidableEqF; by
  rintro ⟨i, j⟩ ⟨k, l⟩ he
  have hleft : Incidence (g (i, j)) (a (Sum.inl k)) := by
    rw [he]
    exact (hg (k, l)).1
  have hright : Incidence (g (i, j)) (a (Sum.inr l)) := by
    rw [he]
    exact (hg (k, l)).2
  have hik : i = k := by
    by_contra hik
    exact h (Sum.inl (g (i, j))) (Sum.inl i) (Sum.inl k) (Sum.inr j)
      (fun hi => hik (Sum.inl.inj hi))
      (by intro hi; cases hi) (by intro hi; cases hi)
      (hg (i, j)).1 hleft (hg (i, j)).2
  have hjl : j = l := by
    by_contra hjl
    exact h (Sum.inl (g (i, j))) (Sum.inl i) (Sum.inr j) (Sum.inr l)
      (by intro hi; cases hi) (by intro hi; cases hi)
      (fun hi => hjl (Sum.inr.inj hi))
      (hg (i, j)).1 (hg (i, j)).2 hright
  exact Prod.ext hik hjl

theorem finiteCrossings_card_of_no_parallel_no_concurrentTriple
    (a : LineTuple F t) (hp : NoParallel a) (hc : NoConcurrentTriple a) :
    FiniteCrossings a ∧ (crossPoints a).card = t * t := by
  have hfinite := finiteCrossings_of_no_parallel a hp
  choose g hg using hfinite
  let grid : Fin t × Fin t → Point F := fun ij => g ij.1 ij.2
  have hgrid : ∀ ij, Incidence (grid ij) (a (Sum.inl ij.1)) ∧
      Incidence (grid ij) (a (Sum.inr ij.2)) := fun ij => hg ij.1 ij.2
  exact ⟨finiteCrossings_of_no_parallel a hp, crossPoints_card_of_grid a grid hgrid
    (grid_injective_of_no_concurrentTriple a grid hgrid hc)⟩

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_LowConcurrency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F]

theorem direction_card_le_of_coverPencil
    (L : Finset (AffineLine F)) {R : ℕ}
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R)
    (d : Direction F) : (L.filter fun l => l.1 = d).card ≤ R := let _ := instFintypeF; by
  simpa only [coverPencil, ProjectiveIncidence, eq_comm] using hR (Sum.inr d)

private theorem prob_four_union_le {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (P Q R S : Ω → Prop) :
    μ.prob (fun u => P u ∨ Q u ∨ R u ∨ S u) ≤
      μ.prob P + μ.prob Q + μ.prob R + μ.prob S := by
  calc
    _ ≤ μ.prob P + μ.prob (fun u => Q u ∨ R u ∨ S u) :=
      μ.prob_union_le _ _
    _ ≤ μ.prob P + (μ.prob Q + μ.prob (fun u => R u ∨ S u)) :=
      add_le_add (le_refl (μ.prob P)) (μ.prob_union_le Q (fun u => R u ∨ S u))
    _ ≤ μ.prob P + (μ.prob Q + (μ.prob R + μ.prob S)) :=
      add_le_add (le_refl (μ.prob P))
        (add_le_add (le_refl (μ.prob Q)) (μ.prob_union_le R S))
    _ = _ := by simp only [add_assoc]

private theorem prob_uniform_parallel_le (L : Finset (AffineLine F)) (t R : ℕ)
    [Nonempty (CoverSample L t)] (hsize : 2 * t ≤ L.card) (hL : 3 ≤ L.card)
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R) :
    (FiniteLaw.uniform (CoverSample L t)).prob LowDegeneracy.AnyParallel ≤
      ((2 * t).descFactorial 2 : ℝ) * R / ((L.card - 1 : ℕ) : ℝ) := by
  have hbound := LowDegeneracy.prob_tuple_parallel_le L t R hsize
    ((by decide : 2 ≤ 3).trans hL) (direction_card_le_of_coverPencil L hR)
  rw [InjectionSampling.law_eq_uniform] at hbound
  exact hbound

private theorem prob_uniform_concurrent_le (L : Finset (AffineLine F)) (t R : ℕ)
    [Nonempty (CoverSample L t)] (hsize : 2 * t ≤ L.card) (hL : 3 ≤ L.card)
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R) :
    (FiniteLaw.uniform (CoverSample L t)).prob LowDegeneracy.AnyConcurrent ≤
      ((2 * t).descFactorial 3 : ℝ) * R / ((L.card - 2 : ℕ) : ℝ) := let _ := instFintypeF; by
  have hbound := LowDegeneracy.prob_tuple_concurrent_le L t R hsize hL hR
  rw [InjectionSampling.law_eq_uniform] at hbound
  exact hbound

theorem prob_lowBad_le
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    (shapes : Finset (Finset (Point F))) (D R h t : ℕ) (δ : ℝ)
    [Nonempty (CoverSample L t)]
    (hδ : 0 < δ) (ht : 0 < t) (hsize : 2 * t ≤ L.card) (hL : 3 ≤ L.card)
    (hSparse : SparseShapes shapes D)
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R) :
    (FiniteLaw.uniform (CoverSample L t)).prob (LowBad X L shapes D h t δ) ≤
      lowFailureBound X L shapes D R h t δ := by
  unfold LowBad lowFailureBound
  apply (prob_four_union_le (FiniteLaw.uniform (CoverSample L t)) _ _ _ _).trans
  exact add_le_add
    (add_le_add
      (add_le_add (prob_many_cross_survivors_le X L hδ ht)
        (prob_uniform_parallel_le L t R hsize hL hR))
      (prob_uniform_concurrent_le L t R hsize hL hR))
    (prob_bad_occupancy_le (h := h) (t := t) shapes L hSparse hR)

theorem admissible_of_not_lowBad
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    (shapes : Finset (Finset (Point F))) (D h t : ℕ) (δ : ℝ)
    (u : CoverSample L t) (hu : ¬ LowBad X L shapes D h t δ u) :
    AdmissibleTuple shapes D h (liftSample L u) ∧
      ((X ∩ crossPoints (liftSample L u)).card : ℝ) < δ * (t : ℝ) ^ 2 / 2 := by
  have hmany : ¬ δ * (t : ℝ) ^ 2 / 2 ≤
      ((X ∩ crossPoints (liftSample L u)).card : ℝ) :=
    fun he => hu (Or.inl he)
  have hparallel : ¬ LowDegeneracy.AnyParallel u :=
    fun he => hu (Or.inr (Or.inl he))
  have hconcurrent : ¬ LowDegeneracy.AnyConcurrent u :=
    fun he => hu (Or.inr (Or.inr (Or.inl he)))
  have hoccupied : ¬ ∃ S ∈ shapes, S ∉ tupleShapes (liftSample L u) ∧
      2 * D * h < (S ∩ crossPoints (liftSample L u)).card :=
    fun he => hu (Or.inr (Or.inr (Or.inr he)))
  have hp : NoParallel (liftSample L u) := by
    intro i j hij hdir
    exact hparallel ((LowDegeneracy.anyParallel_iff u).mpr ⟨i, j, hij, hdir⟩)
  have hc : NoConcurrentTriple (liftSample L u) := by
    intro p i j k hij hik hjk hi hj hk
    exact hconcurrent ((LowDegeneracy.anyConcurrent_iff u).mpr
      ⟨i, j, k, hij, hik, hjk, p, hi, hj, hk⟩)
  obtain ⟨hfinite, hcard⟩ :=
    finiteCrossings_card_of_no_parallel_no_concurrentTriple (liftSample L u) hp hc
  refine ⟨⟨hfinite, hcard, ?_⟩, lt_of_not_ge hmany⟩
  intro S hS hnot
  exact Nat.le_of_not_gt (fun hlarge => hoccupied ⟨S, hS, hnot, hlarge⟩)

theorem exists_low_sample_of_failureBound_lt_one
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    (shapes : Finset (Finset (Point F))) (D R h t : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (ht : 0 < t) (hsize : 2 * t ≤ L.card) (hL : 3 ≤ L.card)
    (hSparse : SparseShapes shapes D)
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R)
    (hbudget : lowFailureBound X L shapes D R h t δ < 1) :
    ∃ a : LineTuple F t, (∀ i, a i ∈ L) ∧ AdmissibleTuple shapes D h a ∧
      ((X ∩ crossPoints a).card : ℝ) < δ * (t : ℝ) ^ 2 / 2 := by
  classical
  let : Nonempty (CoverSample L t) := InjectionSampling.sample_nonempty
    (Fin t ⊕ Fin t) ↥L (by simpa [Nat.card_sum, two_mul] using hsize)
  let μ := FiniteLaw.uniform (CoverSample L t)
  have hprob := prob_lowBad_le X L shapes D R h t δ hδ ht hsize hL hSparse hR
  have hex : ∃ u : CoverSample L t, ¬ LowBad X L shapes D h t δ u := by
    by_contra hnone
    have hall (u : CoverSample L t) : LowBad X L shapes D h t δ u := by
      by_contra hu
      exact hnone ⟨u, hu⟩
    have hone : 1 ≤ μ.prob (LowBad X L shapes D h t δ) := by
      simpa only [FiniteLaw.prob_true] using
        (μ.prob_mono (P := fun _ => True) (Q := LowBad X L shapes D h t δ)
          (fun u _ => hall u))
    exact (not_le_of_gt (hprob.trans_lt hbudget)) hone
  obtain ⟨u, hu⟩ := hex
  exact ⟨liftSample L u, liftSample_mem L u,
    admissible_of_not_lowBad X L shapes D h t δ u hu⟩

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_MaxConcurrency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem coverPencil_card_le_maxConcurrency (L : Finset (AffineLine F))
    (p : ProjectivePoint F) : (coverPencil L p).card ≤ maxConcurrency L :=
  Classical.choose_spec (exists_max_coverPencil L) p

theorem card_complement_add_card_coverPencil (L : Finset (AffineLine F))
    (p : ProjectivePoint F) :
    (L \ coverPencil L p).card + (coverPencil L p).card = L.card :=
  Finset.card_sdiff_add_card_eq_card (coverPencil_subset L p)

theorem complement_card_ge_half_of_count_bounds
    (L : Finset (AffineLine F)) (p : ProjectivePoint F) (q ρ b δ : ℝ)
    (hcount : q - b / (δ * q) ≤ (L.card : ℝ))
    (herror : b / (δ * q) ≤ ρ * q / 2)
    (hp : ((coverPencil L p).card : ℝ) < (1 - ρ) * q) :
    ρ * q / 2 ≤ ((L \ coverPencil L p).card : ℝ) := by
  have hsum : ((L \ coverPencil L p).card : ℝ) +
      ((coverPencil L p).card : ℝ) = (L.card : ℝ) := by
    exact_mod_cast card_complement_add_card_coverPencil L p
  nlinarith

theorem complement_card_ge_half_of_no_large_pencil
    (L : Finset (AffineLine F)) (q ρ b δ : ℝ)
    (hcount : q - b / (δ * q) ≤ (L.card : ℝ))
    (herror : b / (δ * q) ≤ ρ * q / 2)
    (hsmall : ∀ p : ProjectivePoint F,
      ((coverPencil L p).card : ℝ) < (1 - ρ) * q)
    (p : ProjectivePoint F) :
    ρ * q / 2 ≤ ((L \ coverPencil L p).card : ℝ) :=
  complement_card_ge_half_of_count_bounds L p q ρ b δ hcount herror (hsmall p)

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_RigidityNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open Filter Topology

theorem rigidityBudget_eq_errors (D : ℕ) {κ q : ℝ} (hq : 0 < q) :
    rigidityBudget D κ q =
      q ^ (3 / 2 + κ / 10) + q * ((D : ℝ) + q ^ (1 / 2 + κ / 10)) + 2 * q := by
  have hmul : q * q ^ (1 / 2 + κ / 10) = q ^ (3 / 2 + κ / 10) := by
    calc
      _ = q ^ (1 : ℝ) * q ^ (1 / 2 + κ / 10) := by rw [Real.rpow_one]
      _ = q ^ ((1 : ℝ) + (1 / 2 + κ / 10)) := (Real.rpow_add hq _ _).symm
      _ = _ := by congr 1; ring
  unfold rigidityBudget
  rw [mul_add, hmul]
  ring

theorem rigidityBudget_le (D : ℕ) {κ q : ℝ} (hκ : 0 ≤ κ) (hq : 1 ≤ q) :
    rigidityBudget D κ q ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10) := by
  have hpow : q ≤ q ^ (3 / 2 + κ / 10) := by
    calc
      q = q ^ (1 : ℝ) := (Real.rpow_one q).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ (D : ℝ) + 2 by positivity)
  unfold rigidityBudget
  nlinarith only [hmul]

theorem pair_mass_ratio_le_coarse (D : ℕ) {q κ m B R P : ℝ}
    (hq : 1 ≤ q)
    (hB : B ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10))
    (hR : R ≤ q ^ (1 / 2 + κ / 4)) (hm : q / 2 ≤ m)
    (hP : P ≤ q ^ (1 / 2 - κ / 3) * B + R * q ^ (3 / 2 - κ)) :
    P / m ^ 2 ≤
      4 * (((D : ℝ) + 4) * q ^ (-(7 * κ / 30)) + q ^ (-(3 * κ / 4))) := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have he₁ : (1 / 2 - κ / 3) + (3 / 2 + κ / 10) = 2 - 7 * κ / 30 := by ring
  have he₂ : (1 / 2 + κ / 4) + (3 / 2 - κ) = 2 - 3 * κ / 4 := by ring
  have hnum : P ≤ ((D : ℝ) + 4) * q ^ (2 - 7 * κ / 30) +
      q ^ (2 - 3 * κ / 4) := by
    calc
      P ≤ q ^ (1 / 2 - κ / 3) * B + R * q ^ (3 / 2 - κ) := hP
      _ ≤ q ^ (1 / 2 - κ / 3) * (((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10)) +
          q ^ (1 / 2 + κ / 4) * q ^ (3 / 2 - κ) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hqpos.le _))
          (mul_le_mul_of_nonneg_right hR (Real.rpow_nonneg hqpos.le _))
      _ = _ := by
        rw [mul_left_comm (q ^ (1 / 2 - κ / 3)) ((D : ℝ) + 4)
          (q ^ (3 / 2 + κ / 10))]
        simp only [← Real.rpow_add hqpos, he₁, he₂]
  have hden : (q / 2) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (by positivity) hm 2
  have hdiv (a : ℝ) : q ^ a / q ^ 2 = q ^ (a - 2) :=
    (Real.rpow_sub_natCast hqpos.ne' a 2).symm
  calc
    P / m ^ 2 ≤
        (((D : ℝ) + 4) * q ^ (2 - 7 * κ / 30) + q ^ (2 - 3 * κ / 4)) /
          (q / 2) ^ 2 :=
      div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 4 * (((D : ℝ) + 4) * (q ^ (2 - 7 * κ / 30) / q ^ 2) +
        q ^ (2 - 3 * κ / 4) / q ^ 2) := by
      field_simp [hqpos.ne']
      ring
    _ = _ := by
      rw [hdiv (2 - 7 * κ / 30), hdiv (2 - 3 * κ / 4),
        show (2 - 7 * κ / 30) - 2 = -(7 * κ / 30) by ring,
        show (2 - 3 * κ / 4) - 2 = -(3 * κ / 4) by ring]

theorem rigidity_pair_ratio_le (D : ℕ) {q κ m E R P : ℝ}
    (hq : 1 ≤ q) (hκ : 0 ≤ κ) (hm : q / 2 ≤ m)
    (hR : R ≤ q ^ (1 / 2 + κ / 4)) (hE : E ≤ rigidityBudget D κ q)
    (hpair : P ≤ q ^ (1 / 2 - κ / 3) * E + R * q ^ (3 / 2 - κ)) :
    P / m ^ 2 ≤
      4 * (((D : ℝ) + 4) * q ^ (-(7 * κ / 30)) + q ^ (-(3 * κ / 4))) :=
  pair_mass_ratio_le_coarse D hq (hE.trans (rigidityBudget_le D hκ hq)) hR hm hpair

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_RigiditySampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem exists_admissible_of_no_large_pencil
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    (shapes : Finset (Finset (Point F))) (D : ℕ) (δ ρ A : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ)
    (hq : Incidence.incidenceThreshold ≤ Fintype.card F)
    (hsub : Incidence.SmallProperSubfields F)
    (params : RigidityParameters D δ ρ A Incidence.savingExponent (Fintype.card F))
    (hsparse : SparseShapes shapes D)
    (hshapes : shapes.card ≤ D * Fintype.card F ^ D)
    (hL : L.card ≤ Fintype.card F)
    (hE : (overlapExcess Incidence X L : ℝ) ≤
      rigidityBudget D Incidence.savingExponent (Fintype.card F))
    (hgap : (Fintype.card F : ℝ) - L.card ≤
      rigidityBudget D Incidence.savingExponent (Fintype.card F) /
        (δ * Fintype.card F))
    (hsmall : ∀ p : ProjectivePoint F,
      ((coverPencil L p).card : ℝ) < (1 - ρ) * Fintype.card F) :
    ∃ a : LineTuple F (logarithmicSampleSize A (Fintype.card F)),
      (∀ i, a i ∈ L) ∧ AdmissibleTuple shapes D (10 * (D + 1)) a ∧
        ((X ∩ crossPoints a).card : ℝ) <
          δ * (logarithmicSampleSize A (Fintype.card F) : ℝ) ^ 2 / 2 := by
  let q : ℝ := Fintype.card F
  let κ : ℝ := Incidence.savingExponent
  let t := logarithmicSampleSize A q
  let h := 10 * (D + 1)
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one params.q_one
  have hκ : 0 ≤ κ := Incidence.savingExponent_pos.le
  have hm : q / 2 ≤ (L.card : ℝ) := by
    have hg := params.gap_half
    linarith
  have hcount : q - rigidityBudget D κ q / (δ * q) ≤ (L.card : ℝ) := by
    linarith
  have hh : 1 ≤ h := by dsimp [h]; omega
  have ht : 0 < t := lt_of_lt_of_le Nat.zero_lt_one (hh.trans params.h_t)
  have hK : (shapes.card : ℝ) ≤ (D : ℝ) * q ^ (D : ℝ) := by
    have hhcast : (shapes.card : ℝ) ≤ (D : ℝ) * (Fintype.card F : ℝ) ^ D := by
      exact_mod_cast hshapes
    simpa only [Real.rpow_natCast] using hhcast
  by_cases hlow : (maxConcurrency L : ℝ) ≤ q ^ (1 / 2 + κ / 4)
  · have hheavy : ((heavyPoints Incidence X L (q ^ (1 / 2 - κ / 3))).card : ℝ) ≤
        q ^ (1 + κ) :=
      (heavyPoints_card_le_of_excess X L _ _ params.T_one hE).trans params.heavy
    have hpair := orderedPairMass_le_of_uniform_incidence hq hsub X L
      (q ^ (1 / 2 - κ / 3)) (maxConcurrency L)
      (Real.rpow_nonneg hqpos.le _) (Nat.cast_nonneg _) hheavy hL
      (fun p => Nat.cast_le.mpr (coverPencil_card_le_maxConcurrency L p))
    have hratio := rigidity_pair_ratio_le D params.q_one hκ hm hlow hE hpair
    have hm4 : 4 ≤ L.card := by exact_mod_cast params.m_four.trans hm
    have hmH : 4 * h ≤ L.card := by exact_mod_cast params.m_h.trans hm
    have hmT : 2 * t ≤ L.card := by exact_mod_cast params.m_t.trans hm
    have hfailure : lowFailureBound X L shapes D (maxConcurrency L) h t δ < 1 := by
      have hbound := low_sampling_failure_le_envelope (A := A) D L.card (maxConcurrency L)
        shapes.card hqpos hδ hm hm4 hmH
        (Nat.cast_nonneg (orderedPairMass Incidence X L)) hlow hK hratio
      exact (show lowFailureBound X L shapes D (maxConcurrency L) h t δ ≤
        lowFailureEnvelope D δ A κ q from hbound).trans_lt params.low
    exact exists_low_sample_of_failureBound_lt_one X L shapes D (maxConcurrency L)
      h t δ hδ ht hmT (by omega) hsparse
      (coverPencil_card_le_maxConcurrency L) hfailure
  · let p := maxCenter L
    have hR : q ^ (1 / 2 + κ / 4) ≤ ((coverPencil L p).card : ℝ) :=
      (lt_of_not_ge hlow).le
    have hN : ρ * q / 2 ≤ ((L \ coverPencil L p).card : ℝ) :=
      complement_card_ge_half_of_no_large_pencil L q ρ
        (rigidityBudget D κ q) δ hcount params.gap_rho hsmall p
    have htR : t ≤ (coverPencil L p).card := by exact_mod_cast params.r_t.trans hR
    have htN : t ≤ (L \ coverPencil L p).card := by exact_mod_cast params.n_t.trans hN
    have hhR : 2 * h ≤ (coverPencil L p).card := by exact_mod_cast params.r_h.trans hR
    have hhN : 2 * h ≤ (L \ coverPencil L p).card := by exact_mod_cast params.n_h.trans hN
    have hfailure : highFailureBound X L p shapes D h t δ < 1 := by
      have hbound := high_sampling_failure_le_envelope (A := A) D (coverPencil L p).card
        (L \ coverPencil L p).card shapes.card hqpos hδ hρ
        (Nat.cast_nonneg (overlapExcess Incidence X L))
        (hE.trans (rigidityBudget_le D hκ params.q_one)) hR hN hhR hhN hK
      exact (show highFailureBound X L p shapes D h t δ ≤
        highFailureEnvelope D δ ρ A κ q from hbound).trans_lt params.high
    exact highConcurrency_exists_admissible X L p shapes D h t δ hsparse hδ
      hh params.h_t htR htN hfailure

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_Rigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {D : ℕ} {δ ρ A : ℝ}

theorem goodLineCover_of_goodCounts_goodTuples_oai
    (process : DeletionProcess F D δ) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hq : Incidence.incidenceThreshold ≤ Fintype.card F)
    (hsub : Incidence.SmallProperSubfields F)
    (params : RigidityParameters D δ ρ A Incidence.savingExponent (Fintype.card F))
    (ω : process.Config)
    (hcounts : GoodCounts process (Incidence.savingExponent / 10) ω)
    (htuples : GoodTuples process (10 * (D + 1))
      (logarithmicSampleSize A (Fintype.card F)) ω) :
    GoodLineCover δ ρ ω := by
  let q : ℝ := Fintype.card F
  let κ : ℝ := Incidence.savingExponent
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one params.q_one
  have hτ : δ * q ≤ process.survival * q :=
    mul_le_mul_of_nonneg_right process.survivalLower hqpos.le
  refine ⟨?_, ?_⟩
  · intro l
    have hl := (hcounts.2 l).1
    have herr := params.lineerror
    change δ * q / 2 ≤ retainedCount {linePoints l} (linePoints l) ω
    linarith
  · intro L hL hmiss
    by_contra hnone
    have hsmall (p : ProjectivePoint F) :
        ((coverPencil L p).card : ℝ) < (1 - ρ) * q :=
      lt_of_not_ge (fun hp => hnone ⟨p, hp⟩)
    let K := cleanLines ω L
    have hK : K.card ≤ Fintype.card F :=
      (Finset.card_le_card (cleanLines_subset ω L)).trans hL
    have hsmallK (p : ProjectivePoint F) :
        ((coverPencil K p).card : ℝ) < (1 - ρ) * q :=
      (Nat.cast_le.mpr (Finset.card_le_card
        (coverPencil_mono (cleanLines_subset ω L) p))).trans_lt (hsmall p)
    have htotal : process.survival * q ^ 2 - q ^ (3 / 2 + κ / 10) ≤
        ((survivors ∅ ω).card : ℝ) := by
      have h := (abs_le.mp hcounts.1).1
      linarith
    have hlines (l : AffineLine F) :
        ((survivors {linePoints l} ω ∩ linePoints l).card : ℝ) ≤
          process.survival * q + ((D : ℝ) + q ^ (1 / 2 + κ / 10)) := by
      have h := (hcounts.2 l).2
      change retainedCount {linePoints l} (linePoints l) ω ≤ _
      linarith
    have hmissR : ((survivors ∅ ω \ L.biUnion linePoints).card : ℝ) ≤ 2 * q := by
      dsimp only [q]
      exact_mod_cast hmiss
    have hb := clean_cover_count_bounds ω L process.survival δ
      (q ^ (3 / 2 + κ / 10)) ((D : ℝ) + q ^ (1 / 2 + κ / 10)) (2 * q)
      hδ process.survivalLower (by positivity) htotal hlines hmissR hL
    have hbudget := rigidityBudget_eq_errors D (κ := κ) hqpos
    rw [← hbudget] at hb
    obtain ⟨a, haK, ha, hfew⟩ := exists_admissible_of_no_large_pencil
      (survivors ∅ ω) K process.shapes D δ ρ A hδ hρ hq hsub params
      process.sparse process.shapeCount hK hb.1 hb.2 hsmallK
    exact htuples.no_sparse_clean_tuple L a ha haK hfew

end RyserCoveringCounterexample.LineCover

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.RyserCoveringCounterexample.LineCover.goodLineCover_of_goodCounts_goodTuples_oai.{u_1} := @OAI.RyserCoveringCounterexample.LineCover.goodLineCover_of_goodCounts_goodTuples_oai.{u_1}
