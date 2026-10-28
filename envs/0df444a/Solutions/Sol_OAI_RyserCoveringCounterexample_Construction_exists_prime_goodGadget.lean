-- Prove2me | solution 1 for OAI.RyserCoveringCounterexample.Construction.exists_prime_goodGadget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T04:29:02.95847+00:00
-- url     : https://prove2.me/submissions/c6c6430e-cedb-437a-b930-0b7c1f38c851

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIW2RY002
import Theorems.Thm_OAI_RyserCoveringCounterexample_LineCover_goodLineCover_of_goodCounts_goodTuples

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

theorem eq_affineLine_of_common_projective_incidence
    {p q : ProjectivePoint F} {l m : AffineLine F}
    (hpq : p ≠ q)
    (hpl : ProjectiveIncidence p (some l))
    (hql : ProjectiveIncidence q (some l))
    (hpm : ProjectiveIncidence p (some m))
    (hqm : ProjectiveIncidence q (some m)) : l = m :=
  Option.some.inj (eq_projectiveLine_of_common_incidence hpq hpl hql hpm hqm)

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_CoverPencil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem covered_points_on_missing_pencil_line
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (ell : AffineLine F)
    (hcover : ∀ x ∈ X, ∃ l ∈ L, Incidence x l)
    (hpell : ProjectiveIncidence p (some ell)) (hell : ell ∉ L) :
    (X ∩ linePoints ell).card ≤ 1 + (L \ affinePencil p).card := by
  classical
  let T := X ∩ linePoints ell
  let A := T.filter fun x => Sum.inl x = p
  let R := L \ affinePencil p
  have hA : A.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    exact Sum.inl.inj ((Finset.mem_filter.mp hx).2.trans
      (Finset.mem_filter.mp hy).2.symm)
  have hintersection : ∀ m ∈ R, (T ∩ linePoints m).card ≤ 1 := by
    intro m hm
    have hmL : m ∈ L := (Finset.mem_sdiff.mp hm).1
    have hne : ell ≠ m := fun heq => hell (heq.symm ▸ hmL)
    apply le_trans (Finset.card_le_card ?_) (card_linePoints_inter_le_one hne)
    intro x hx
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).2,
        (Finset.mem_inter.mp hx).2⟩
  have hsub : T ⊆ A ∪ R.biUnion (fun m => T ∩ linePoints m) := by
    intro x hx
    have hxX : x ∈ X := (Finset.mem_inter.mp hx).1
    have hxell : Incidence x ell :=
      (mem_linePoints _ _).mp (Finset.mem_inter.mp hx).2
    obtain ⟨m, hmL, hxm⟩ := hcover x hxX
    by_cases hmp : m ∈ affinePencil p
    · have hxp : Sum.inl x = p := by
        by_contra hne
        have heq : ell = m := eq_affineLine_of_common_projective_incidence
          hne hxell hpell hxm ((mem_affinePencil _ _).mp hmp)
        exact hell (heq.symm ▸ hmL)
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hxp⟩)
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr
        ⟨m, Finset.mem_sdiff.mpr ⟨hmL, hmp⟩,
          Finset.mem_inter.mpr ⟨hx, (mem_linePoints _ _).mpr hxm⟩⟩
  calc
    (X ∩ linePoints ell).card = T.card := rfl
    _ ≤ (A ∪ R.biUnion (fun m => T ∩ linePoints m)).card :=
      Finset.card_le_card hsub
    _ ≤ A.card + (R.biUnion (fun m => T ∩ linePoints m)).card := Finset.card_union_le _ _
    _ ≤ 1 + ∑ m ∈ R, (T ∩ linePoints m).card :=
      Nat.add_le_add hA Finset.card_biUnion_le
    _ ≤ 1 + ∑ _m ∈ R, 1 := Nat.add_le_add_left (Finset.sum_le_sum hintersection) 1
    _ = 1 + (L \ affinePencil p).card := by simp [R]

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F]

variable [instFintypeF : Fintype F]

theorem cubeMap_bijective (h : Nat.Coprime 3 (Fintype.card F - 1)) :
    Function.Bijective (cubeMap : Point F → Point F) := by
  have hc := cube_bijective h
  constructor
  · intro p q hpq
    have hx := congrArg (fun r : Point F => r.1) hpq
    have hy := congrArg (fun r : Point F => r.2) hpq
    exact Prod.ext (hc.injective hx) hy
  · rintro ⟨x, y⟩
    obtain ⟨z, hz⟩ := hc.surjective x
    exact ⟨(z, y), Prod.ext hz rfl⟩

variable [instDecidableEqF : DecidableEq F]

theorem cubicShape_eq_image_linePoints (d z : F) :
    cubicShape d z = (linePoints (some d, z)).image cubeMap := by
  ext p
  constructor
  · intro hp
    obtain ⟨x, rfl⟩ := mem_cubicShape.mp hp
    refine Finset.mem_image.mpr ⟨(x, d * x + z), ?_, rfl⟩
    apply (mem_linePoints _ _).mpr
    change d * x + z - d * x = z
    ring
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    refine mem_cubicShape.mpr ⟨q.1, ?_⟩
    apply Prod.ext
    · rfl
    · have hq' : q.2 - d * q.1 = z := (mem_linePoints _ _).mp hq
      change d * q.1 + z = q.2
      simpa [add_comm] using (sub_eq_iff_eq_add.mp hq').symm

open Polynomial

theorem coprime_three_zmod_card_sub_one {p : ℕ} [Fact p.Prime] (hpmod : p % 3 = 2) :
    Nat.Coprime 3 (Fintype.card (ZMod p) - 1) := by
  rw [ZMod.card]
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  intro hd
  have hz := Nat.mod_eq_zero_of_dvd hd
  omega

end RyserCoveringCounterexample.Construction

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

theorem expectation_add (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.expectation (fun ω => f ω + g ω) = μ.expectation f + μ.expectation g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_sub (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.expectation (fun ω => f ω - g ω) = μ.expectation f - μ.expectation g := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

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
-- module Solutions.OAIW2_RyserCov.Ryser_Probability_Exponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.FiniteLaw

lemma expectation_mul_left_real {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    p.expectation (fun a => c * f a) = c * p.expectation f := by
  classical
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma exp_le_one_add_add_sq {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := (le_abs_self (Real.exp x - 1 - x)).trans
    (Real.abs_exp_sub_one_sub_id_le hx)
  linarith

lemma expectation_exp_le_of_mean_zero {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (z : Ω → ℝ) (M v θ : ℝ)
    (hz : p.expectation z = 0)
    (hbound : ∀ a, |z a| ≤ M)
    (hsecond : p.expectation (fun a => (z a) ^ 2) ≤ v)
    (hθ : |θ| * M ≤ 1) :
    p.expectation (fun a => Real.exp (θ * z a)) ≤
      Real.exp (θ ^ 2 * v) := by
  classical
  have hpoint (a : Ω) :
      Real.exp (θ * z a) ≤ 1 + θ * z a + θ ^ 2 * (z a) ^ 2 := by
    have habs : |θ * z a| ≤ 1 := calc
      |θ * z a| = |θ| * |z a| := abs_mul _ _
      _ ≤ |θ| * M := mul_le_mul_of_nonneg_left (hbound a) (abs_nonneg θ)
      _ ≤ 1 := hθ
    have he := exp_le_one_add_add_sq habs
    nlinarith [he]
  have hlin :
      (∑ a, p.weight a * (θ * z a)) = θ * p.expectation z := by
    exact expectation_mul_left_real p θ z
  have hquad :
      (∑ a, p.weight a * (θ ^ 2 * (z a) ^ 2)) =
        θ ^ 2 * p.expectation (fun a => (z a) ^ 2) := by
    exact expectation_mul_left_real p (θ ^ 2) (fun a => (z a) ^ 2)
  calc
    p.expectation (fun a => Real.exp (θ * z a)) ≤
        p.expectation (fun a => 1 + θ * z a + θ ^ 2 * (z a) ^ 2) := by
      unfold expectation
      exact Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (hpoint a) (p.nonneg a)
    _ = 1 + θ * p.expectation z +
        θ ^ 2 * p.expectation (fun a => (z a) ^ 2) := by
      change (∑ a, p.weight a * (1 + θ * z a + θ ^ 2 * (z a) ^ 2)) = _
      simp only [mul_add, mul_one, Finset.sum_add_distrib]
      rw [p.total, hlin, hquad]
    _ = 1 + θ ^ 2 * p.expectation (fun a => (z a) ^ 2) := by
      rw [hz]
      ring
    _ ≤ 1 + θ ^ 2 * v :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hsecond (sq_nonneg θ))
    _ ≤ Real.exp (θ ^ 2 * v) := by
      simpa only [add_comm] using Real.add_one_le_exp (θ ^ 2 * v)

lemma iterated_centered_mgf_le
    {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteLaw A) (q : A → FiniteLaw B)
    (f : A → B → ℝ) (head : A → ℝ)
    (center θ v V : ℝ)
    (hhead : p.expectation (fun a => Real.exp (θ * (head a - center))) ≤
      Real.exp (θ ^ 2 * v))
    (htail : ∀ a, (q a).expectation
        (fun b => Real.exp (θ * (f a b - head a))) ≤ Real.exp (θ ^ 2 * V)) :
    p.expectation (fun a => (q a).expectation
      (fun b => Real.exp (θ * (f a b - center)))) ≤
        Real.exp (θ ^ 2 * (v + V)) := by
  classical
  have hsplit (a : A) :
      (q a).expectation (fun b => Real.exp (θ * (f a b - center))) =
        Real.exp (θ * (head a - center)) *
          (q a).expectation (fun b => Real.exp (θ * (f a b - head a))) := by
    rw [← expectation_mul_left_real]
    congr 1
    funext b
    rw [← Real.exp_add]
    congr 1
    ring
  have hinner (a : A) :
      (q a).expectation (fun b => Real.exp (θ * (f a b - center))) ≤
        Real.exp (θ ^ 2 * V) * Real.exp (θ * (head a - center)) := by
    rw [hsplit]
    have h := mul_le_mul_of_nonneg_left (htail a)
      (Real.exp_pos (θ * (head a - center))).le
    simpa only [mul_comm] using h
  calc
    p.expectation (fun a => (q a).expectation
        (fun b => Real.exp (θ * (f a b - center)))) ≤
        p.expectation (fun a =>
          Real.exp (θ ^ 2 * V) * Real.exp (θ * (head a - center))) := by
      unfold expectation
      exact Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (hinner a) (p.nonneg a)
    _ = Real.exp (θ ^ 2 * V) *
        p.expectation (fun a => Real.exp (θ * (head a - center))) :=
      expectation_mul_left_real p _ _
    _ ≤ Real.exp (θ ^ 2 * V) * Real.exp (θ ^ 2 * v) :=
      mul_le_mul_of_nonneg_left hhead (Real.exp_pos _).le
    _ = Real.exp (θ ^ 2 * (v + V)) := by
      rw [← Real.exp_add]
      congr 1
      ring

lemma chernoff_upper {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (f : Ω → ℝ) (u θ : ℝ) (hθ : 0 ≤ θ) :
    p.prob (fun a => u ≤ f a) ≤
      Real.exp (-θ * u) * p.expectation (fun a => Real.exp (θ * f a)) := by
  classical
  unfold prob expectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  by_cases huf : u ≤ f a
  · simp only [ite_eq_left huf]
    have he : 1 ≤ Real.exp (-θ * u) * Real.exp (θ * f a) := calc
      1 = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ Real.exp (-θ * u + θ * f a) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hθ (sub_nonneg.mpr huf)]
      _ = Real.exp (-θ * u) * Real.exp (θ * f a) := Real.exp_add _ _
    calc
      p.weight a = p.weight a * 1 := by ring
      _ ≤ p.weight a * (Real.exp (-θ * u) * Real.exp (θ * f a)) :=
        mul_le_mul_of_nonneg_left he (p.nonneg a)
      _ = Real.exp (-θ * u) * (p.weight a * Real.exp (θ * f a)) := by ring
  · simp only [ite_eq_right huf]
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (p.nonneg a) (Real.exp_pos _).le)

lemma chernoff_upper_of_mgf {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (f : Ω → ℝ) (u θ V : ℝ)
    (hθ : 0 ≤ θ)
    (hmgf : p.expectation (fun a => Real.exp (θ * f a)) ≤
      Real.exp (θ ^ 2 * V)) :
    p.prob (fun a => u ≤ f a) ≤ Real.exp (θ ^ 2 * V - θ * u) := by
  calc
    p.prob (fun a => u ≤ f a) ≤
        Real.exp (-θ * u) * p.expectation (fun a => Real.exp (θ * f a)) :=
      chernoff_upper p f u θ hθ
    _ ≤ Real.exp (-θ * u) * Real.exp (θ ^ 2 * V) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (θ ^ 2 * V - θ * u) := by
      rw [← Real.exp_add]
      congr 1
      ring

lemma bernstein_scalar_optimization
    (M V u P : ℝ)
    (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 / M →
      P ≤ Real.exp (t ^ 2 * V - t * u)) :
    P ≤ Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  by_cases hcut : u / (2 * V) ≤ 1 / M
  · have ht : 0 < u / (2 * V) :=
      div_pos hu (mul_pos (by norm_num) hV)
    have hexp :
        (u / (2 * V)) ^ 2 * V - (u / (2 * V)) * u =
          -(1 / 4 : ℝ) * (u ^ 2 / V) := by
      field_simp [ne_of_gt hV]; ring
    calc
      P ≤ Real.exp ((u / (2 * V)) ^ 2 * V - (u / (2 * V)) * u) :=
        h _ ht hcut
      _ ≤ Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
        apply Real.exp_le_exp.mpr
        rw [hexp]
        nlinarith [min_le_left (u ^ 2 / V) (u / M)]
  · have hcross : 2 * V < u * M := by
      have ht : 1 / M < u / (2 * V) := lt_of_not_ge hcut
      have ht' :=
        (div_lt_div_iff₀ hM (mul_pos (by norm_num) hV)).mp ht
      simpa using ht'
    have hnum : V - u * M ≤ -(u * M) / 4 := by
      nlinarith [mul_pos hu hM]
    have hexp :
        (1 / M) ^ 2 * V - (1 / M) * u ≤
          -(1 / 4 : ℝ) * (u / M) := by
      calc
        (1 / M) ^ 2 * V - (1 / M) * u =
            (V - u * M) / M ^ 2 := by
          field_simp [ne_of_gt hM]
        _ ≤ (-(u * M) / 4) / M ^ 2 :=
          div_le_div_of_nonneg_right hnum (sq_nonneg M)
        _ = -(1 / 4 : ℝ) * (u / M) := by
          field_simp [ne_of_gt hM]
    calc
      P ≤ Real.exp ((1 / M) ^ 2 * V - (1 / M) * u) :=
        h _ (div_pos (by norm_num) hM) le_rfl
      _ ≤ Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
        apply Real.exp_le_exp.mpr
        have hmin :
            -(1 / 4 : ℝ) * (u / M) ≤
              -(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M) := by
          nlinarith [min_le_right (u ^ 2 / V) (u / M)]
        exact hexp.trans hmin

lemma prob_abs_ge_le_add {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (f : Ω → ℝ) (u : ℝ) :
    p.prob (fun a => u ≤ |f a|) ≤
      p.prob (fun a => u ≤ f a) + p.prob (fun a => u ≤ -f a) := by
  classical
  unfold prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a ha
  change (if u ≤ |f a| then p.weight a else 0) ≤
    (if u ≤ f a then p.weight a else 0) + (if u ≤ -f a then p.weight a else 0)
  by_cases hs : 0 ≤ f a
  · rw [abs_of_nonneg hs]
    split_ifs <;> linarith [p.nonneg a]
  · rw [abs_of_nonpos (le_of_not_ge hs)]
    split_ifs <;> linarith [p.nonneg a]

lemma bernstein_abs_tail_of_mgf {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (f : Ω → ℝ) (M V u : ℝ)
    (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hmgf : ∀ θ : ℝ, |θ| * M ≤ 1 →
      p.expectation (fun a => Real.exp (θ * f a)) ≤
        Real.exp (θ ^ 2 * V)) :
    p.prob (fun a => u ≤ |f a|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  have upper : p.prob (fun a => u ≤ f a) ≤
      Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
    apply bernstein_scalar_optimization M V u _ hM hV hu
    intro θ hθ hθM
    have hadm : |θ| * M ≤ 1 := by
      rw [abs_of_pos hθ]
      exact (le_div_iff₀ hM).mp hθM
    exact chernoff_upper_of_mgf p f u θ V hθ.le (hmgf θ hadm)
  have lower : p.prob (fun a => u ≤ -f a) ≤
      Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
    apply bernstein_scalar_optimization M V u _ hM hV hu
    intro θ hθ hθM
    have hadm : |θ| * M ≤ 1 := by
      rw [abs_of_pos hθ]
      exact (le_div_iff₀ hM).mp hθM
    have hadmneg : |-θ| * M ≤ 1 := by
      simpa only [abs_neg] using hadm
    have hneg : p.expectation (fun a => Real.exp (θ * (-f a))) ≤
        Real.exp (θ ^ 2 * V) := by
      simpa only [neg_mul, mul_neg, neg_sq] using hmgf (-θ) hadmneg
    exact chernoff_upper_of_mgf p (fun a => -f a) u θ V hθ.le hneg
  calc
    p.prob (fun a => u ≤ |f a|) ≤
        p.prob (fun a => u ≤ f a) + p.prob (fun a => u ≤ -f a) :=
      prob_abs_ge_le_add p f u
    _ ≤ Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) +
        Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) :=
      add_le_add upper lower
    _ = 2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by ring

end RyserCoveringCounterexample.FiniteLaw

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

section ProductCoordinates

variable {I : Type*} [Fintype I] [DecidableEq I]
  {A : I → Type*} [∀ i, Fintype (A i)]

theorem expectation_pi_coordinate (μ : ∀ i, FiniteLaw (A i))
    (i : I) (f : A i → ℝ) :
    (pi μ).expectation (fun ω => f (ω i)) = (μ i).expectation f := by
  classical
  let g : ∀ j, A j → ℝ := fun j a => if h : j = i then f (h ▸ a) else 1
  have hg (ω : ∀ j, A j) : (∏ j, g j (ω j)) = f (ω i) := by
    dsimp only [g]
    simp only [Fintype.prod_dite_eq']
  have he (j : I) : (μ j).expectation (g j) =
      if h : j = i then (μ i).expectation f else 1 := by
    by_cases h : j = i
    · subst j
      simp [g]
    · simp [g, h, expectation_const]
  calc
    _ = (pi μ).expectation (fun ω => ∏ j, g j (ω j)) := by
      congr 1
      funext ω
      exact (hg ω).symm
    _ = ∏ j, (μ j).expectation (g j) := expectation_pi_product μ g
    _ = _ := by simp_rw [he]; simp

theorem prob_pi_coordinate (μ : ∀ i, FiniteLaw (A i))
    (i : I) (P : A i → Prop) :
    (pi μ).prob (fun ω => P (ω i)) = (μ i).prob P := by
  classical
  rw [prob_eq_expectation, prob_eq_expectation]
  exact expectation_pi_coordinate μ i (fun a => if P a then 1 else 0)

end ProductCoordinates

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem map_weight_eq_prob (μ : FiniteLaw Ω) (f : Ω → Γ) (γ : Γ) :
    (map μ f).weight γ = μ.prob (fun ω => f ω = γ) := rfl

theorem map_uniform_equiv [Nonempty Ω] [Nonempty Γ] (e : Ω ≃ Γ) :
    (uniform Ω).map e = uniform Γ := by
  classical
  apply ext_weight
  funext y
  simp [map, uniform, ← e.eq_symm_apply, Fintype.card_congr e]

theorem pi_uniform {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] :
    pi (fun i => uniform (A i)) = uniform (∀ i, A i) :=
  eq_uniform_of_weight_eq (pi (fun i => uniform (A i))) (fun _ _ => rfl)

end RyserCoveringCounterexample.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Probability_RareAnchor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample

lemma rareAnchor_centering_raw
    {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω)
    (htotal : (∑ ω, w ω) = 1)
    (g : Ω → ℝ) (b C r : ℝ)
    (E : Ω → Prop) [DecidablePred E]
    (hbound : ∀ ω, |g ω - b| ≤ C)
    (houtside : ∀ ω, ¬ E ω → g ω = b)
    (hrare : (∑ ω, if E ω then w ω else 0) ≤ r) :
    let m := ∑ ω, w ω * g ω
    (∑ ω, w ω * (g ω - m)) = 0 ∧
      (∀ ω, |g ω - m| ≤ 2 * C) ∧
      (∑ ω, w ω * (g ω - m) ^ 2) ≤ C ^ 2 * r := by
  classical
  let m : ℝ := ∑ ω, w ω * g ω
  change
    (∑ ω, w ω * (g ω - m)) = 0 ∧
      (∀ ω, |g ω - m| ≤ 2 * C) ∧
      (∑ ω, w ω * (g ω - m) ^ 2) ≤ C ^ 2 * r

  have hconst (a : ℝ) : (∑ ω, w ω * a) = a := by
    rw [← Finset.sum_mul, htotal, one_mul]

  have hmlo : b - C ≤ m := by
    calc
      b - C = ∑ ω, w ω * (b - C) := (hconst _).symm
      _ ≤ ∑ ω, w ω * g ω := by
        apply Finset.sum_le_sum
        intro ω _
        apply mul_le_mul_of_nonneg_left _ (hw ω)
        have hlo := (abs_le.mp (hbound ω)).1
        linarith
      _ = m := rfl

  have hmhi : m ≤ b + C := by
    calc
      m = ∑ ω, w ω * g ω := rfl
      _ ≤ ∑ ω, w ω * (b + C) := by
        apply Finset.sum_le_sum
        intro ω _
        apply mul_le_mul_of_nonneg_left _ (hw ω)
        have hhi := (abs_le.mp (hbound ω)).2
        linarith
      _ = b + C := hconst _

  have hmean0 : (∑ ω, w ω * (g ω - m)) = 0 := by
    calc
      (∑ ω, w ω * (g ω - m)) =
          (∑ ω, w ω * g ω) - (∑ ω, w ω * m) := by
        simp only [mul_sub, Finset.sum_sub_distrib]
      _ = m - m := by
        change m - (∑ ω, w ω * m) = m - m
        rw [hconst m]
      _ = 0 := sub_self m

  have hcenterBound : ∀ ω, |g ω - m| ≤ 2 * C := by
    intro ω
    rcases abs_le.mp (hbound ω) with ⟨hlo, hhi⟩
    apply abs_le.mpr
    constructor <;> linarith

  have hsqBound : ∀ ω, (g ω - b) ^ 2 ≤ C ^ 2 := by
    intro ω
    rcases abs_le.mp (hbound ω) with ⟨hlo, hhi⟩
    have hminus : 0 ≤ C - (g ω - b) := by
      linarith
    have hplus : 0 ≤ C + (g ω - b) := by
      linarith
    have hprod := mul_nonneg hminus hplus
    nlinarith

  have hanchor :
      (∑ ω, w ω * (g ω - b) ^ 2) ≤ C ^ 2 * r := by
    calc
      (∑ ω, w ω * (g ω - b) ^ 2) ≤
          ∑ ω, (if E ω then w ω else 0) * C ^ 2 := by
        apply Finset.sum_le_sum
        intro ω _
        by_cases hE : E ω
        · simp only [ite_eq_left hE]
          exact mul_le_mul_of_nonneg_left (hsqBound ω) (hw ω)
        · simp [hE, houtside ω hE]
      _ = (∑ ω, if E ω then w ω else 0) * C ^ 2 := by
        rw [Finset.sum_mul]
      _ ≤ r * C ^ 2 :=
        mul_le_mul_of_nonneg_right hrare (sq_nonneg C)
      _ = C ^ 2 * r := mul_comm _ _

  have hvariance :
      (∑ ω, w ω * (g ω - b) ^ 2) =
        (∑ ω, w ω * (g ω - m) ^ 2) + (m - b) ^ 2 := by
    calc
      (∑ ω, w ω * (g ω - b) ^ 2) =
          ∑ ω,
            (w ω * (g ω - m) ^ 2 +
              (w ω * (g ω - m)) * (2 * (m - b)) +
              w ω * (m - b) ^ 2) := by
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ = (∑ ω, w ω * (g ω - m) ^ 2) +
            (∑ ω, w ω * (g ω - m)) * (2 * (m - b)) +
            (∑ ω, w ω) * (m - b) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.sum_mul, ← Finset.sum_mul]
      _ = (∑ ω, w ω * (g ω - m) ^ 2) + (m - b) ^ 2 := by
        simp only [hmean0, htotal, zero_mul, one_mul, add_zero]

  refine ⟨hmean0, hcenterBound, ?_⟩
  have hshiftNonneg := sq_nonneg (m - b)
  linarith [hvariance, hanchor]

lemma FiniteLaw.rareAnchor_centering
    {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω)
    (g : Ω → ℝ) (b C r : ℝ)
    (E : Ω → Prop) [DecidablePred E]
    (hbound : ∀ ω, |g ω - b| ≤ C)
    (houtside : ∀ ω, ¬ E ω → g ω = b)
    (hrare : μ.prob E ≤ r) :
    μ.expectation (fun ω => g ω - μ.expectation g) = 0 ∧
      (∀ ω, |g ω - μ.expectation g| ≤ 2 * C) ∧
      μ.expectation (fun ω => (g ω - μ.expectation g) ^ 2)
        ≤ C ^ 2 * r := by
  exact @rareAnchor_centering_raw Ω _
    μ.weight μ.nonneg μ.total g b C r E
    (fun ω => Classical.propDecidable (E ω))
    hbound houtside hrare

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Probability_Exposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Exposure

open scoped BigOperators

variable {Omega : Type*} [instFintypeOmega : Fintype Omega]

theorem cons_head_tail {n : Nat} (w : Fin (n + 1) → Omega) :
    Fin.cons (w 0) (fun i => w i.succ) = w := let _ := instFintypeOmega;
  (splitConfig n).left_inv w

theorem expectation_pi_succ {n : Nat}
    (mu : Fin (n + 1) → FiniteLaw Omega)
    (f : (Fin (n + 1) → Omega) → ℝ) :
    (FiniteLaw.pi mu).expectation f =
      (mu 0).expectation (headMean mu f) := by
  classical
  change (∑ w, (∏ i, (mu i).weight (w i)) * f w) =
    ∑ x, (mu 0).weight x *
      (∑ tail : Fin n → Omega,
        (∏ i, (mu i.succ).weight (tail i)) * f (Fin.cons x tail))
  calc
    _ = ∑ p : Omega × (Fin n → Omega),
        ((mu 0).weight p.1 * ∏ i, (mu i.succ).weight (p.2 i)) *
          f (Fin.cons p.1 p.2) := by
      refine Fintype.sum_equiv (splitConfig n) _ _ ?_
      intro w
      change (∏ i, (mu i).weight (w i)) * f w =
        ((mu 0).weight (w 0) * ∏ i : Fin n, (mu i.succ).weight (w i.succ)) *
          f (Fin.cons (w 0) (fun i => w i.succ))
      rw [cons_head_tail, Fin.prod_univ_succ]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tail _
      ring

theorem mean_difference_bound {A : Type*} [Fintype A]
    (p : FiniteLaw A) (f g : A → ℝ) (C : ℝ)
    (h : ∀ a, |f a - g a| ≤ C) :
    |p.expectation f - p.expectation g| ≤ C := by
  have hlo : p.expectation (fun a => g a - C) ≤ p.expectation f := by
    apply p.expectation_mono
    intro a
    have hh := (abs_le.mp (h a)).1
    linarith
  have hhi : p.expectation f ≤ p.expectation (fun a => g a + C) := by
    apply p.expectation_mono
    intro a
    have hh := (abs_le.mp (h a)).2
    linarith
  rw [FiniteLaw.expectation_sub, FiniteLaw.expectation_const] at hlo
  rw [FiniteLaw.expectation_add, FiniteLaw.expectation_const] at hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem second_moment_le {A : Type*} [Fintype A]
    (p : FiniteLaw A) (f : A → ℝ) (C : ℝ)
    (h : ∀ a, |f a| ≤ C) :
    p.expectation (fun a => (f a) ^ 2) ≤ C ^ 2 := by
  calc
    _ ≤ p.expectation (fun _ => C ^ 2) := by
      apply p.expectation_mono
      intro a
      rcases abs_le.mp (h a) with ⟨hl, hu⟩
      have hp : 0 ≤ (C - f a) * (C + f a) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    _ = C ^ 2 := p.expectation_const _

theorem update_cons_zero {n : Nat} (x y : Omega) (tail : Fin n → Omega) :
    Function.update
        (Fin.cons (n := let _ := instFintypeOmega; n) (α := fun _ : Fin (n + 1) => Omega) x tail) 0 y =
      Fin.cons (n := n) (α := fun _ : Fin (n + 1) => Omega) y tail :=
  Fin.update_cons_zero (n := n) (α := fun _ : Fin (n + 1) => Omega) x tail y

theorem cons_update {n : Nat} (x y : Omega) (tail : Fin n → Omega) (i : Fin n) :
    Fin.cons (n := let _ := instFintypeOmega; n) (α := fun _ : Fin (n + 1) => Omega) x
        (Function.update tail i y) =
      Function.update
        (Fin.cons (n := n) (α := fun _ : Fin (n + 1) => Omega) x tail) i.succ y :=
  Fin.cons_update (n := n) (α := fun _ : Fin (n + 1) => Omega) x tail i y

theorem exposureBounds_of_coordinateBound (M : ℝ) (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (c : Fin n → ℝ)
    (hcoord : ∀ i w x, |f (Function.update w i x) - f w| ≤ c i)
    (hM : ∀ i, c i ≤ M) :
    ExposureBounds M n mu f (fun i => (c i) ^ 2) := by
  classical
  induction n with
  | zero => trivial
  | succ n ih =>
    have hdiam (x y : Omega) :
        |headMean mu f x - headMean mu f y| ≤ c 0 := by
      apply mean_difference_bound
      intro tail
      simpa only [update_cons_zero] using hcoord 0 (Fin.cons y tail) x
    have hcenter (x : Omega) :
        |headMean mu f x - (mu 0).expectation (headMean mu f)| ≤ c 0 := by
      have hh := mean_difference_bound (mu 0) (fun _ => headMean mu f x)
        (headMean mu f) (c 0) (hdiam x)
      simpa only [FiniteLaw.expectation_const] using hh
    refine ⟨fun x => (hcenter x).trans (hM 0), ?_, ?_⟩
    · exact second_moment_le (mu 0)
        (fun x => headMean mu f x - (mu 0).expectation (headMean mu f))
        (c 0) hcenter
    · intro x
      refine ih (fun i => mu i.succ) (fun tail => f (Fin.cons x tail))
        (fun i => c i.succ) ?_ (fun i => hM i.succ)
      intro i tail y
      simpa only [cons_update] using hcoord i.succ (Fin.cons x tail) y

theorem exposureBounds_of_rareAnchor (M : ℝ) (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (e : Omega) (C r : Fin n → ℝ) (rare : Fin n → Omega → Prop)
    (hanchor : ∀ i w, |f w - f (Function.update w i e)| ≤ C i)
    (houtside : ∀ i w, ¬ rare i (w i) → f w = f (Function.update w i e))
    (hrare : ∀ i, (mu i).prob (rare i) ≤ r i)
    (hM : ∀ i, 2 * C i ≤ M) :
    ExposureBounds M n mu f (fun i => (C i) ^ 2 * r i) := by
  classical
  induction n with
  | zero => trivial
  | succ n ih =>
    have hhead (x : Omega) :
        |headMean mu f x - headMean mu f e| ≤ C 0 := by
      apply mean_difference_bound
      intro tail
      simpa only [update_cons_zero] using hanchor 0 (Fin.cons x tail)
    have hheadoutside (x : Omega) (hx : ¬ rare 0 x) :
        headMean mu f x = headMean mu f e := by
      apply congrArg ((FiniteLaw.pi (fun i : Fin n => mu i.succ)).expectation)
      funext tail
      simpa only [update_cons_zero] using houtside 0 (Fin.cons x tail) hx
    rcases FiniteLaw.rareAnchor_centering (mu 0) (headMean mu f)
      (headMean mu f e) (C 0) (r 0) (rare 0) hhead hheadoutside (hrare 0)
      with ⟨hzero, hcenter, hsecond⟩
    refine ⟨fun x => (hcenter x).trans (hM 0), hsecond, ?_⟩
    intro x
    refine ih (fun i => mu i.succ) (fun tail => f (Fin.cons x tail))
      (fun i => C i.succ) (fun i => r i.succ) (fun i => rare i.succ)
      ?_ ?_ (fun i => hrare i.succ) (fun i => hM i.succ)
    · intro i tail
      simpa only [cons_update] using hanchor i.succ (Fin.cons x tail)
    · intro i tail hnot
      simpa only [cons_update] using houtside i.succ (Fin.cons x tail) hnot

end RyserCoveringCounterexample.Exposure

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Probability_Concentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Concentration

open scoped BigOperators
open Exposure

variable {Omega : Type*} [Fintype Omega]

theorem exposure_mgf (M : ℝ) (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (v : Fin n → ℝ) (theta : ℝ)
    (hb : ExposureBounds M n mu f v) (htheta : |theta| * M ≤ 1) :
    (FiniteLaw.pi mu).expectation
      (fun w => Real.exp (theta * (f w - (FiniteLaw.pi mu).expectation f)))
      ≤ Real.exp (theta ^ 2 * ∑ i, v i) := by
  classical
  induction n with
  | zero =>
    have hf : f = fun _ => f (fun i => Fin.elim0 i) := by
      funext w
      apply congrArg f
      funext i
      exact Fin.elim0 i
    rw [hf]
    simp [FiniteLaw.expectation_const]
  | succ n ih =>
    rcases hb with ⟨hbound, hsecond, hrec⟩
    have hzero : (mu 0).expectation
        (fun x => headMean mu f x - (mu 0).expectation (headMean mu f)) = 0 := by
      rw [FiniteLaw.expectation_sub, FiniteLaw.expectation_const, sub_self]
    have hhead := FiniteLaw.expectation_exp_le_of_mean_zero (mu 0)
      (fun x => headMean mu f x - (mu 0).expectation (headMean mu f))
      M (v 0) theta hzero hbound hsecond htheta
    have htail (x : Omega) :
        (FiniteLaw.pi (fun i : Fin n => mu i.succ)).expectation
          (fun w => Real.exp (theta * (f (Fin.cons x w) - headMean mu f x)))
          ≤ Real.exp (theta ^ 2 * ∑ i : Fin n, v i.succ) := by
      exact ih (fun i => mu i.succ) (fun w => f (Fin.cons x w))
        (fun i => v i.succ) (hrec x)
    calc
      _ = (mu 0).expectation (fun x =>
          (FiniteLaw.pi (fun i : Fin n => mu i.succ)).expectation
            (fun w => Real.exp (theta *
              (f (Fin.cons x w) - (FiniteLaw.pi mu).expectation f)))) :=
        expectation_pi_succ (n := n) mu
          (fun w : Fin (n + 1) → Omega =>
            Real.exp (theta * (f w - (FiniteLaw.pi mu).expectation f)))
      _ = (mu 0).expectation (fun x =>
          (FiniteLaw.pi (fun i : Fin n => mu i.succ)).expectation
            (fun w => Real.exp (theta *
              (f (Fin.cons x w) - (mu 0).expectation (headMean mu f))))) := by
        rw [expectation_pi_succ mu f]
      _ ≤ Real.exp (theta ^ 2 * (v 0 + ∑ i : Fin n, v i.succ)) :=
        FiniteLaw.iterated_centered_mgf_le (mu 0)
          (fun _ => FiniteLaw.pi (fun i : Fin n => mu i.succ))
          (fun x w => f (Fin.cons x w)) (headMean mu f)
          ((mu 0).expectation (headMean mu f)) theta (v 0)
          (∑ i : Fin n, v i.succ) hhead htail
      _ = _ := by rw [Fin.sum_univ_succ]

theorem concentration (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (v : Fin n → ℝ) (M V u : ℝ)
    (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hb : ExposureBounds M n mu f v) (hv : (∑ i, v i) ≤ V) :
    (FiniteLaw.pi mu).prob
        (fun w => u ≤ |f w - (FiniteLaw.pi mu).expectation f|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  apply FiniteLaw.bernstein_abs_tail_of_mgf (FiniteLaw.pi mu)
    (fun w => f w - (FiniteLaw.pi mu).expectation f) M V u hM hV hu
  intro theta htheta
  exact (exposure_mgf M n mu f v theta hb htheta).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hv (sq_nonneg theta)))

theorem coordinate_concentration (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (c : Fin n → ℝ) (M V u : ℝ)
    (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hcoord : ∀ i w x, |f (Function.update w i x) - f w| ≤ c i)
    (hcM : ∀ i, c i ≤ M) (hcV : (∑ i, (c i) ^ 2) ≤ V) :
    (FiniteLaw.pi mu).prob
        (fun w => u ≤ |f w - (FiniteLaw.pi mu).expectation f|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  exact concentration n mu f (fun i => (c i) ^ 2) M V u hM hV hu
    (exposureBounds_of_coordinateBound M n mu f c hcoord hcM) hcV

theorem rare_anchor_concentration (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (e : Omega) (C r : Fin n → ℝ) (rare : Fin n → Omega → Prop)
    (M V u : ℝ) (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hanchor : ∀ i w, |f w - f (Function.update w i e)| ≤ C i)
    (houtside : ∀ i w, ¬ rare i (w i) → f w = f (Function.update w i e))
    (hrare : ∀ i, (mu i).prob (rare i) ≤ r i)
    (hCM : ∀ i, 2 * C i ≤ M)
    (hCV : (∑ i, (C i) ^ 2 * r i) ≤ V) :
    (FiniteLaw.pi mu).prob
        (fun w => u ≤ |f w - (FiniteLaw.pi mu).expectation f|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  exact concentration n mu f (fun i => (C i) ^ 2 * r i) M V u hM hV hu
    (exposureBounds_of_rareAnchor M n mu f e C r rare hanchor houtside hrare hCM)
    hCV

end RyserCoveringCounterexample.Concentration

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

variable (I Ω : Type*) [Fintype I]

theorem finCoordinateEquiv_update [DecidableEq I]
    (w : Fin (Fintype.card I) → Ω) (j : Fin (Fintype.card I)) (x : Ω) :
    finCoordinateEquiv I Ω (Function.update w j x) =
      Function.update (finCoordinateEquiv I Ω w) ((Fintype.equivFin I).symm j) x := by
  funext i
  change Function.update w j x (Fintype.equivFin I i) =
    Function.update (fun i => w (Fintype.equivFin I i)) ((Fintype.equivFin I).symm j) x i
  by_cases hi : i = (Fintype.equivFin I).symm j
  · subst i
    simp
  · have hij : Fintype.equivFin I i ≠ j := by
      intro h
      apply hi
      have h' := congrArg (Fintype.equivFin I).symm h
      simpa only [Equiv.symm_apply_apply] using h'
    simp [Function.update, hi, hij]

variable {I Ω} [DecidableEq I] [Fintype Ω] [Nonempty Ω]

theorem uniform_coordinate_concentration
    (f : (I → Ω) → ℝ) (c M V u : ℝ)
    (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hcoord : ∀ i w x, |f (Function.update w i x) - f w| ≤ c)
    (hcM : c ≤ M) (hcV : (Fintype.card I : ℝ) * c ^ 2 ≤ V) :
    (FiniteLaw.uniform (I → Ω)).prob
        (fun w => u ≤ |f w - (FiniteLaw.uniform (I → Ω)).expectation f|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  have hcoord' : ∀ (j : Fin (Fintype.card I)) (w : Fin (Fintype.card I) → Ω) x,
      |f (finCoordinateEquiv I Ω (Function.update w j x)) -
        f (finCoordinateEquiv I Ω w)| ≤ c := by
    intro j w x
    rw [finCoordinateEquiv_update]
    exact hcoord _ _ _
  have h := Concentration.coordinate_concentration (Fintype.card I)
    (fun _ => FiniteLaw.uniform Ω) (fun w => f (finCoordinateEquiv I Ω w))
    (fun _ => c) M V u hM hV hu hcoord' (fun _ => hcM) (by simpa using hcV)
  have hmean :
      (FiniteLaw.pi (fun _ : Fin (Fintype.card I) => FiniteLaw.uniform Ω)).expectation
        (fun w => f (finCoordinateEquiv I Ω w)) =
      (FiniteLaw.uniform (I → Ω)).expectation f := by
    rw [FiniteLaw.pi_uniform]
    calc
      _ = ((FiniteLaw.uniform (Fin (Fintype.card I) → Ω)).map
          (finCoordinateEquiv I Ω)).expectation f :=
        (FiniteLaw.expectation_map _ _ _).symm
      _ = _ := by rw [FiniteLaw.map_uniform_equiv]
  rw [hmean, FiniteLaw.pi_uniform] at h
  have hprob :
      (FiniteLaw.uniform (Fin (Fintype.card I) → Ω)).prob
        (fun w => u ≤ |f (finCoordinateEquiv I Ω w) -
          (FiniteLaw.uniform (I → Ω)).expectation f|) =
      (FiniteLaw.uniform (I → Ω)).prob
        (fun w => u ≤ |f w - (FiniteLaw.uniform (I → Ω)).expectation f|) := by
    calc
      _ = ((FiniteLaw.uniform (Fin (Fintype.card I) → Ω)).map
          (finCoordinateEquiv I Ω)).prob
          (fun w => u ≤ |f w - (FiniteLaw.uniform (I → Ω)).expectation f|) :=
        (FiniteLaw.prob_map _ _ _).symm
      _ = _ := by rw [FiniteLaw.map_uniform_equiv]
  rw [hprob] at h
  exact h

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem mixed_covered_points_on_missing_pencil_line
    (X B : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (ell : AffineLine F)
    (hcover : ∀ x ∈ X, x ∈ B ∨ ∃ l ∈ L, Incidence x l)
    (hpell : ProjectiveIncidence p (some ell)) (hell : ell ∉ L) :
    (X ∩ linePoints ell).card ≤ 1 + (L \ affinePencil p).card + B.card := by
  have hlinecover : ∀ x ∈ X \ B, ∃ l ∈ L, Incidence x l := by
    intro x hx
    rcases hcover x (Finset.mem_sdiff.mp hx).1 with hxB | hxL
    · exact ((Finset.mem_sdiff.mp hx).2 hxB).elim
    · exact hxL
  have hbound := covered_points_on_missing_pencil_line (X \ B) L p ell
    hlinecover hpell hell
  have hsub : X ∩ linePoints ell ⊆ ((X \ B) ∩ linePoints ell) ∪ B := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_right _ hxB
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx).1, hxB⟩,
          (Finset.mem_inter.mp hx).2⟩)
  calc
    (X ∩ linePoints ell).card ≤ (((X \ B) ∩ linePoints ell) ∪ B).card :=
      Finset.card_le_card hsub
    _ ≤ ((X \ B) ∩ linePoints ell).card + B.card := Finset.card_union_le _ _
    _ ≤ 1 + (L \ affinePencil p).card + B.card := Nat.add_le_add_right hbound _

theorem mixed_cover_eq_parallel_of_near_pencil
    (Y B : Finset (Point F)) (L : Finset (AffineLine F))
    (hlarge : 200 < 19 * Fintype.card F)
    (hlines : ∀ ell : AffineLine F,
      Fintype.card F ≤ 8 * (Y ∩ linePoints ell).card)
    (hcover : ∀ y ∈ Y, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell)
    (hbudget : 2 * L.card + B.card ≤ 2 * Fintype.card F)
    (hnear : ∃ p : ProjectivePoint F,
      99 * Fintype.card F ≤ 100 * (L ∩ affinePencil p).card) :
    ∃ d : Direction F, L = affinePencil (Sum.inr d) ∧ B = ∅ := by
  obtain ⟨p, hp⟩ := hnear
  have hLcard : L.card ≤ Fintype.card F := by omega
  have hdecomp := Finset.card_sdiff_add_card_inter L (affinePencil p)
  have hforced : affinePencil p ⊆ L := by
    intro ell hell
    by_contra hmissing
    have hpell : ProjectiveIncidence p (some ell) :=
      (mem_affinePencil _ _).mp hell
    have hcount := mixed_covered_points_on_missing_pencil_line Y B L p ell
      hcover hpell hmissing
    have hlower := hlines ell
    omega
  cases p with
  | inl p =>
      have hcard := Finset.card_le_card hforced
      rw [card_affinePencil_finite] at hcard
      omega
  | inr d =>
      have heq : affinePencil (Sum.inr d) = L :=
        Finset.eq_of_subset_of_card_le hforced (by simpa using hLcard)
      have hL : L.card = Fintype.card F := by rw [← heq, card_affinePencil_infinite]
      have hB : B.card = 0 := by omega
      exact ⟨d, heq.symm, Finset.card_eq_zero.mp hB⟩

theorem missed_points_subset_of_mixed_cover
    (Y B : Finset (Point F)) (L : Finset (AffineLine F))
    (hcover : ∀ y ∈ Y, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell) :
    Y \ L.biUnion linePoints ⊆ B := by
  intro y hy
  rcases hcover y (Finset.mem_sdiff.mp hy).1 with hyB | ⟨ell, hell, hyell⟩
  · exact hyB
  · exact ((Finset.mem_sdiff.mp hy).2
      (Finset.mem_biUnion.mpr ⟨ell, hell, (mem_linePoints _ _).mpr hyell⟩)).elim

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetConsequences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem gadgetCoverProperty_of_near_pencils
    (Y : Finset (Point F))
    (hlarge : 200 < 19 * Fintype.card F)
    (hlines : ∀ ell : AffineLine F,
      Fintype.card F ≤ 8 * (Y ∩ linePoints ell).card)
    (hnear : ∀ (B : Finset (Point F)) (L : Finset (AffineLine F)),
      (∀ y ∈ Y, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell) →
      2 * L.card + B.card ≤ 2 * Fintype.card F →
      ∃ p : ProjectivePoint F,
        99 * Fintype.card F ≤ 100 * (L ∩ affinePencil p).card) :
    GadgetCoverProperty Y := by
  intro B L hcover hbudget
  exact mixed_cover_eq_parallel_of_near_pencil Y B L hlarge hlines
    hcover hbudget (hnear B L hcover hbudget)

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

theorem cubeMap_mem_cubicShape_iff
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (w : Point k) (d z : k) :
    cubeMap w ∈ cubicShape d z ↔ Incidence w (some d, z) := by
  rw [cubicShape_eq_image_linePoints]
  constructor
  · intro hw
    obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp hw
    have hsame : v = w := (cubeMap_bijective hcop).injective hvw
    subst v
    exact (mem_linePoints _ _).mp hv
  · intro hw
    exact Finset.mem_image.mpr ⟨w, (mem_linePoints _ _).mpr hw, rfl⟩

theorem cubeMap_mem_transformedRetained_iff
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (a : GadgetOutcome k) (w : Point k) :
    cubeMap w ∈ transformedRetained a ↔ w ∈ retainedPoints a := by
  constructor
  · intro hw
    obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp hw
    exact (cubeMap_bijective hcop).injective hvw ▸ hv
  · intro hw
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩

theorem transformedRetained_eq_survivors
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (a : GadgetOutcome k) :
    transformedRetained a = Finset.univ \ cubicDeletionUnion a := by
  ext p
  obtain ⟨w, rfl⟩ := (cubeMap_bijective hcop).surjective p
  rw [cubeMap_mem_transformedRetained_iff hcop]
  simp [mem_retainedPoints, cubicDeletionUnion, cubeMap_mem_cubicShape_iff hcop,
    omittedLine]

end RyserCoveringCounterexample.Construction

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

theorem survivors_mono_ignore {ignore larger : Finset (Finset P)}
    (h : ignore ⊆ larger) (ω : Fin n → Outcome shapes D) :
    survivors ignore ω ⊆ survivors larger ω := by
  intro x hx
  apply mem_survivors.mpr
  intro i hxi
  rcases mem_deleted.mp hxi with ⟨s, hs, hnot, hxs⟩
  exact mem_survivors.mp hx i
    (mem_deleted.mpr ⟨s, hs, fun hI => hnot (h hI), hxs⟩)

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
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetShapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable (k : Type*) [Field k] [Fintype k] [DecidableEq k]

variable {k}

theorem selected_cubicShapes_ne_linePoints {n : ℕ}
    (ω : Fin n → LineCover.Outcome (cubicShapes k) 3)
    (hcard : 3 < Fintype.card k) {S : Finset (Point k)}
    (hS : S ∈ LineCover.selected ω) (ell : AffineLine k) : S ≠ linePoints ell := by
  obtain ⟨i, T, _, rfl⟩ := LineCover.mem_selected.mp hS
  exact cubicShapes_member_ne_linePoints hcard T.property ell

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_Process
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

namespace DeletionProcess

variable {δ : ℝ} (process : DeletionProcess F D δ)

theorem point_survival_ge (x : Point F) :
    δ ≤ process.law.prob (fun ω => x ∈ process.survivorSet ω) := by
  change δ ≤ (FiniteLaw.pi process.trials).prob (fun ω => x ∈ survivors ∅ ω)
  rw [process.uniformSurvival]
  exact process.survivalLower

end DeletionProcess
end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_SurvivalNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.LineCover

theorem one_quarter_le_survival_pow (q n : ℕ) (hq : 2 ≤ q) (hn : n ≤ q - 1) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (q : ℝ)) ^ n := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hinv : 1 / (q : ℝ) ≤ 1 := (div_le_one hq0).2 (by linarith)
  have hb0 : (0 : ℝ) ≤ 1 - 1 / (q : ℝ) := sub_nonneg.mpr hinv
  have hb1 : 1 - 1 / (q : ℝ) ≤ 1 := by
    have hnonneg : (0 : ℝ) ≤ 1 / (q : ℝ) := div_nonneg (by norm_num) hq0.le
    linarith
  exact (one_quarter_le_survival_pow_pred q hq).trans
    (pow_le_pow_of_le_one hb0 hb1 hn)

theorem one_quarter_le_survival_pow_sub_two (q : ℕ) (hq : 2 ≤ q) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (q : ℝ)) ^ (q - 2) :=
  one_quarter_le_survival_pow q (q - 2) hq (Nat.sub_le_sub_left (by decide : 1 ≤ 2) q)

theorem quarter_mul_le_survival_mean (q : ℕ) (hq : 2 ≤ q) :
    (q : ℝ) / 4 ≤ (q : ℝ) * (1 - 1 / (q : ℝ)) ^ (q - 2) := by
  have h := mul_le_mul_of_nonneg_left (one_quarter_le_survival_pow_sub_two q hq)
    (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  simpa only [mul_one_div] using h

end RyserCoveringCounterexample.LineCover

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Probability_ProductMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.FiniteLaw

theorem map_map {Ω Γ Λ : Type*} [Fintype Ω] [Fintype Γ] [Fintype Λ]
    (mu : FiniteLaw Ω) (f : Ω → Γ) (g : Γ → Λ) :
    (mu.map f).map g = mu.map (g ∘ f) := by
  apply ext_weight
  funext z
  simp only [map_weight_eq_prob, prob_map, Function.comp_apply]

theorem map_pi {I : Type*} [Fintype I] [DecidableEq I]
    {A B : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (mu : ∀ i, FiniteLaw (A i)) (f : ∀ i, A i → B i) :
    (pi mu).map (fun a i => f i (a i)) = pi (fun i => (mu i).map (f i)) := by
  apply ext_weight
  funext b
  rw [map_weight_eq_prob]
  calc
    (pi mu).prob (fun a => (fun i => f i (a i)) = b) =
        (pi mu).prob (fun a => ∀ i, f i (a i) = b i) := by
      congr 1
      funext a
      exact propext ⟨fun h i => congrFun h i, fun h => funext h⟩
    _ = ∏ i, (mu i).prob (fun a => f i a = b i) :=
      prob_pi mu (fun i a => f i a = b i)
    _ = (pi (fun i => (mu i).map (f i))).weight b := by
      simp only [pi_weight, map_weight_eq_prob]

end RyserCoveringCounterexample.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetProcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

theorem gadgetLaw_map_config :
    (gadgetLaw k).map gadgetConfig = FiniteLaw.pi (gadgetTrials (k := k)) := by
  let f : (Fin (Fintype.card (NonzeroSlope k)) → k) →
      (Fin (Fintype.card (NonzeroSlope k)) → LineCover.Outcome (cubicShapes k) 3) :=
    fun a i => cubicTrialOutcome (gadgetSlope i) (a i)
  have hconfig : gadgetConfig (k := k) = f ∘ gadgetInterceptEquiv := rfl
  rw [hconfig, ← FiniteLaw.map_map]
  have hreindex : (gadgetLaw k).map gadgetInterceptEquiv =
      FiniteLaw.pi (fun _ : Fin (Fintype.card (NonzeroSlope k)) =>
        FiniteLaw.uniform k) := by
    rw [gadgetLaw, FiniteLaw.pi_uniform, FiniteLaw.map_uniform_equiv,
      FiniteLaw.pi_uniform]
  rw [hreindex]
  exact FiniteLaw.map_pi (fun _ => FiniteLaw.uniform k)
    (fun i => cubicTrialOutcome (gadgetSlope i))

theorem gadgetConfig_survivors
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (a : GadgetOutcome k) :
    LineCover.survivors ∅ (gadgetConfig a) = transformedRetained a := by
  rw [transformedRetained_eq_survivors hcop]
  ext x
  have hright : x ∈ Finset.univ \ cubicDeletionUnion a ↔
      ∀ d : NonzeroSlope k, x ∉ cubicShape d.val (a d) := by
    simp [cubicDeletionUnion]
  rw [hright, LineCover.mem_survivors]
  simp only [gadgetConfig, deleted_empty_cubicTrialOutcome]
  constructor
  · intro h d
    simpa only [gadgetSlope, Equiv.symm_apply_apply] using
      h ((Fintype.equivFin (NonzeroSlope k)) d)
  · intro h i
    exact h (gadgetSlope i)

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetGood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

theorem gadgetConfig_survivors_ignoring_line
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (hcard : 3 < Fintype.card k)
    (a : GadgetOutcome k) (ell : AffineLine k) :
    LineCover.survivors {linePoints ell} (gadgetConfig a) = transformedRetained a := by
  have hnot : linePoints ell ∉ LineCover.selected (gadgetConfig a) := by
    intro hmem
    exact selected_cubicShapes_ne_linePoints (gadgetConfig a) hcard hmem ell rfl
  calc
    _ = LineCover.survivors ∅ (gadgetConfig a) :=
      LineCover.survivors_insert_eq_of_not_selected hnot
    _ = transformedRetained a := gadgetConfig_survivors hcop a

theorem gadget_line_density_of_goodLineCover
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (hcard : 3 < Fintype.card k)
    (a : GadgetOutcome k)
    (hgood : LineCover.GoodLineCover (1 / 4) (1 / 100) (gadgetConfig a))
    (ell : AffineLine k) :
    Fintype.card k ≤ 8 * (transformedRetained a ∩ linePoints ell).card := by
  have h := hgood.1 ell
  rw [gadgetConfig_survivors_ignoring_line hcop hcard a ell] at h
  have hreal : (Fintype.card k : ℝ) ≤
      8 * ((transformedRetained a ∩ linePoints ell).card : ℝ) := by linarith
  exact_mod_cast hreal

theorem gadget_near_pencil_of_goodLineCover
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (a : GadgetOutcome k)
    (hgood : LineCover.GoodLineCover (1 / 4) (1 / 100) (gadgetConfig a))
    (B : Finset (Point k)) (L : Finset (AffineLine k))
    (hcover : ∀ y ∈ transformedRetained a, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell)
    (hbudget : 2 * L.card + B.card ≤ 2 * Fintype.card k) :
    ∃ p : ProjectivePoint k,
      99 * Fintype.card k ≤ 100 * (L ∩ affinePencil p).card := by
  have hL : L.card ≤ Fintype.card k := by omega
  have hB : B.card ≤ 2 * Fintype.card k := by omega
  have hmiss : (LineCover.survivors ∅ (gadgetConfig a) \ L.biUnion linePoints).card ≤
      2 * Fintype.card k := by
    rw [gadgetConfig_survivors hcop a]
    exact (Finset.card_le_card (missed_points_subset_of_mixed_cover
      (transformedRetained a) B L hcover)).trans hB
  obtain ⟨p, hp⟩ := hgood.2 L hL hmiss
  have heq : LineCover.coverPencil L p = L ∩ affinePencil p := by
    ext ell
    simp only [LineCover.mem_coverPencil, Finset.mem_inter, mem_affinePencil]
  rw [heq] at hp
  refine ⟨p, ?_⟩
  have hreal : (99 : ℝ) * Fintype.card k ≤
      100 * ((L ∩ affinePencil p).card : ℝ) := by linarith
  exact_mod_cast hreal

theorem goodGadget_of_events
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (hcard : 3 < Fintype.card k)
    (hlarge : 200 < 19 * Fintype.card k) (a : GadgetOutcome k)
    (horiginal : OriginalLineDensity a)
    (hgood : LineCover.GoodLineCover (1 / 4) (1 / 100) (gadgetConfig a)) :
    GoodGadget a := by
  have hlines := gadget_line_density_of_goodLineCover hcop hcard a hgood
  refine ⟨horiginal, hlines, ?_⟩
  exact gadgetCoverProperty_of_near_pencils (transformedRetained a) hlarge hlines
    (gadget_near_pencil_of_goodLineCover hcop a hgood)

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetOriginalCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

theorem originalLineSurvivors_eq_retained_filter (a : GadgetOutcome k)
    (d : NonzeroSlope k) (z : k) (hz : z ≠ a d) :
    originalLineSurvivors a d z =
      (retainedPoints a).filter (fun p => Incidence p (some d.val, z)) := by
  ext p
  simp only [mem_originalLineSurvivors, Finset.mem_filter, mem_retainedPoints]
  constructor
  · rintro ⟨hp, havoid⟩
    refine ⟨?_, hp⟩
    intro e
    by_cases hed : e = d
    · subst e
      intro he
      change projection (some d.val) p = z at hp
      change projection (some d.val) p = a d at he
      exact hz (hp.symm.trans he)
    · exact havoid e hed
  · rintro ⟨havoid, hp⟩
    exact ⟨hp, fun e _ => havoid e⟩

theorem originalLineCount_eq_retained_filter_card (a : GadgetOutcome k)
    (d : NonzeroSlope k) (z : k) (hz : z ≠ a d) :
    originalLineCount a d z =
      ((retainedPoints a).filter (fun p => Incidence p (some d.val, z))).card := by
  rw [originalLineCount, originalLineSurvivors_eq_retained_filter a d z hz]

theorem originalLineSurvivors_update_same (a : GadgetOutcome k)
    (d : NonzeroSlope k) (z x : k) :
    originalLineSurvivors (Function.update a d x) d z = originalLineSurvivors a d z := by
  ext p
  simp only [mem_originalLineSurvivors]
  constructor
  · rintro ⟨hp, havoid⟩
    refine ⟨hp, ?_⟩
    intro e hed
    simpa only [omittedLine, Function.update_of_ne hed] using havoid e hed
  · rintro ⟨hp, havoid⟩
    refine ⟨hp, ?_⟩
    intro e hed
    simpa only [omittedLine, Function.update_of_ne hed] using havoid e hed

private theorem originalLineSurvivors_card_le_add_one_of_agree_off
    (a b : GadgetOutcome k) (d : NonzeroSlope k) (z : k) (i : NonzeroSlope k)
    (hid : i ≠ d) (hagree : ∀ e, e ≠ i → a e = b e) :
    (originalLineSurvivors a d z).card ≤ (originalLineSurvivors b d z).card + 1 := by
  have hlines : (some d.val, z) ≠ omittedLine b i := by
    intro h
    apply hid
    apply Subtype.ext
    exact (Option.some.inj (congrArg Prod.fst h)).symm
  have hinter :
      (linePoints (some d.val, z) ∩ linePoints (omittedLine b i)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_inter.mp hp
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_inter.mp hq
    exact eq_of_common_incidence_of_ne_lines hlines
      ((mem_linePoints _ _).mp hp₁) ((mem_linePoints _ _).mp hp₂)
      ((mem_linePoints _ _).mp hq₁) ((mem_linePoints _ _).mp hq₂)
  have hsub : originalLineSurvivors a d z ⊆
      originalLineSurvivors b d z ∪
        (linePoints (some d.val, z) ∩ linePoints (omittedLine b i)) := by
    intro p hp
    by_cases hb : p ∈ originalLineSurvivors b d z
    · exact Finset.mem_union_left _ hb
    · apply Finset.mem_union_right
      have hp' := (mem_originalLineSurvivors a d z p).mp hp
      refine Finset.mem_inter.mpr ⟨(mem_linePoints _ _).mpr hp'.1, ?_⟩
      apply (mem_linePoints _ _).mpr
      by_contra hnot
      apply hb
      apply (mem_originalLineSurvivors b d z p).mpr
      refine ⟨hp'.1, ?_⟩
      intro e hed
      by_cases hei : e = i
      · subst e
        exact hnot
      · change ¬ Incidence p (some e.val, b e)
        rw [← hagree e hei]
        exact hp'.2 e hed
  calc
    (originalLineSurvivors a d z).card ≤
        (originalLineSurvivors b d z ∪
          (linePoints (some d.val, z) ∩ linePoints (omittedLine b i))).card :=
      Finset.card_le_card hsub
    _ ≤ (originalLineSurvivors b d z).card +
        (linePoints (some d.val, z) ∩ linePoints (omittedLine b i)).card :=
      Finset.card_union_le _ _
    _ ≤ (originalLineSurvivors b d z).card + 1 := Nat.add_le_add_left hinter _

theorem originalLineCount_update_abs_le (a : GadgetOutcome k)
    (d : NonzeroSlope k) (z : k) (i : NonzeroSlope k) (x : k) :
    |originalLineCount (Function.update a i x) d z - originalLineCount a d z| ≤ 2 := by
  by_cases hid : i = d
  · subst i
    simp only [originalLineCount, originalLineSurvivors_update_same, sub_self, abs_zero]
    norm_num
  · have hforward := originalLineSurvivors_card_le_add_one_of_agree_off
      (Function.update a i x) a d z i hid (by
        intro e hei
        exact Function.update_of_ne hei x a)
    have hreverse := originalLineSurvivors_card_le_add_one_of_agree_off
      a (Function.update a i x) d z i hid (by
        intro e hei
        exact (Function.update_of_ne hei x a).symm)
    have hforwardR : originalLineCount (Function.update a i x) d z ≤
        originalLineCount a d z + 1 := by
      unfold originalLineCount
      exact_mod_cast hforward
    have hreverseR : originalLineCount a d z ≤
        originalLineCount (Function.update a i x) d z + 1 := by
      unfold originalLineCount
      exact_mod_cast hreverse
    apply abs_le.mpr
    constructor <;> linarith

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetOriginalExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

private theorem expectation_finset_sum
    {Ω ι : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (s : Finset ι) (f : ι → Ω → ℝ) :
    μ.expectation (fun a => ∑ i ∈ s, f i a) =
      ∑ i ∈ s, μ.expectation (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, FiniteLaw.expectation_const]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, FiniteLaw.expectation_add, ih]

theorem card_nonzeroSlope :
    Fintype.card (NonzeroSlope k) = Fintype.card k - 1 := by
  change Fintype.card {e : k // ¬e = 0} = _
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

theorem prob_originalPoint_survival (d : NonzeroSlope k) (w : Point k) :
    (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).prob
        (fun a => ∀ e, e ≠ d → ¬Incidence w (omittedLine a e)) =
      (1 - 1 / (Fintype.card k : ℝ)) ^ (Fintype.card k - 2) := by
  classical
  have hsingle (e : NonzeroSlope k) :
      (FiniteLaw.uniform k).prob
          (fun z : k => Incidence w (some e.val, z)) =
        1 / (Fintype.card k : ℝ) := by
    rw [FiniteLaw.prob]
    rw [Finset.sum_eq_single_of_mem
      (projection (some e.val) w) (Finset.mem_univ _)]
    · simp [Incidence, FiniteLaw.uniform, one_div]
    · intro b _ hb
      apply ite_eq_right
      intro h
      exact hb (show projection (some e.val) w = b from h).symm
  have hcoord (e : NonzeroSlope k) :
      (FiniteLaw.uniform k).prob
          (fun z : k => e ≠ d → ¬Incidence w (some e.val, z)) =
        if e = d then 1 else 1 - 1 / (Fintype.card k : ℝ) := by
    by_cases he : e = d
    · simp [he]
    · simp only [ne_eq, he, not_false_eq_true, true_implies, ite_false]
      rw [FiniteLaw.prob_compl, hsingle e]
  change
    (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).prob
        (fun a => ∀ e, e ≠ d → ¬Incidence w (some e.val, a e)) = _
  rw [FiniteLaw.prob_pi
    (A := fun _ : NonzeroSlope k => k)
    (fun _ : NonzeroSlope k => FiniteLaw.uniform k)
    (fun (e : NonzeroSlope k) (b : k) =>
      e ≠ d → ¬Incidence w (some e.val, b))]
  simp_rw [hcoord]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  rw [Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ d), Finset.card_univ,
    card_nonzeroSlope]
  simp only [Nat.sub_sub]

theorem expectation_originalLineCount (d : NonzeroSlope k) (z : k) :
    (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).expectation
        (fun a => originalLineCount a d z) =
      (Fintype.card k : ℝ) *
        (1 - 1 / (Fintype.card k : ℝ)) ^ (Fintype.card k - 2) := by
  classical
  have hcount (a : GadgetOutcome k) :
      originalLineCount a d z =
        ∑ w ∈ linePoints (some d.val, z),
          if ∀ e : NonzeroSlope k, e ≠ d → ¬Incidence w (omittedLine a e)
          then (1 : ℝ) else 0 := by
    simp only [originalLineCount, originalLineSurvivors, Finset.sum_boole]
  calc
    _ = ∑ w ∈ linePoints (some d.val, z),
        (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).expectation
          (fun a => if ∀ e : NonzeroSlope k,
              e ≠ d → ¬Incidence w (omittedLine a e)
            then (1 : ℝ) else 0) := by
      simpa only [← hcount] using
        (expectation_finset_sum
          (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k))
          (linePoints (some d.val, z))
          (fun (w : Point k) (a : GadgetOutcome k) =>
            if ∀ e : NonzeroSlope k, e ≠ d → ¬Incidence w (omittedLine a e)
            then (1 : ℝ) else 0))
    _ = ∑ w ∈ linePoints (some d.val, z),
        (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).prob
          (fun a => ∀ e, e ≠ d → ¬Incidence w (omittedLine a e)) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [FiniteLaw.prob_eq_expectation]
      apply congrArg (FiniteLaw.expectation
        (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)))
      funext a
      by_cases h : ∀ e : NonzeroSlope k,
          e ≠ d → ¬Incidence w (omittedLine a e)
      · simp
      · simp
    _ = _ := by
      simp only [prob_originalPoint_survival, Finset.sum_const,
        nsmul_eq_mul, card_linePoints]

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_TailNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open Filter Topology

theorem tendsto_log_pow_mul_rpow_neg_atTop (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun q : ℝ => (Real.log q) ^ k * q ^ (-a)) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun q : ℝ => (Real.log q) ^ k / q ^ a) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (s := a) (k : ℝ) ha).tendsto_div_nhds_zero
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with q hq
  simp only [Real.rpow_neg hq, div_eq_mul_inv]

theorem tendsto_rpow_mul_exp_neg_rpow_atTop (r : ℝ) {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun q : ℝ => q ^ r * Real.exp (-c * q ^ a)) atTop (𝓝 0) := by
  refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (r / a) c hc).comp (tendsto_rpow_atTop ha)).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with q hq
  dsimp only [Function.comp_apply]
  rw [← Real.rpow_mul hq, mul_div_cancel₀ r ha.ne']

theorem tendsto_polynomial_mul_exp_neg_rpow_atTop (p : Polynomial ℝ) {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun q : ℝ => p.eval q * Real.exp (-c * q ^ a)) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
      simpa only [Polynomial.eval_add, add_mul, add_zero] using hp.add hr
  | monomial k b =>
      simpa only [Polynomial.eval_monomial, Real.rpow_natCast, mul_assoc, mul_zero] using
        (tendsto_rpow_mul_exp_neg_rpow_atTop (k : ℝ) ha hc).const_mul b

theorem tendsto_count_failure_atTop {D ε : ℝ} (hD : 0 < D) (hε : 0 < ε) :
    Tendsto (fun q : ℝ =>
      2 * (1 + q * (q + 1)) * Real.exp (-q ^ (2 * ε) / (16 * D ^ 5)))
      atTop (𝓝 0) := by
  have hc : 0 < (16 * D ^ 5)⁻¹ := by positivity
  have ha : 0 < 2 * ε := by positivity
  have h := tendsto_polynomial_mul_exp_neg_rpow_atTop
    (2 * (1 + Polynomial.X * (Polynomial.X + 1)) : Polynomial ℝ) ha hc
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

theorem tendsto_logarithmicSampleSize_atTop {A : ℝ} (hA : 0 < A) :
    Tendsto (fun q : ℝ => (logarithmicSampleSize A q : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun q => Nat.le_ceil (A * Real.log q))
  exact Real.tendsto_log_atTop.const_mul_atTop hA

theorem tendsto_sampleSize_pow_mul_rpow_neg_atTop (k : ℕ) {A a : ℝ}
    (hA : 0 < A) (ha : 0 < a) :
    Tendsto (fun q : ℝ => (logarithmicSampleSize A q : ℝ) ^ k * q ^ (-a))
      atTop (𝓝 0) := by
  have hbound : Tendsto
      (fun q : ℝ => (A + 1) ^ k * ((Real.log q) ^ k * q ^ (-a)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_log_pow_mul_rpow_neg_atTop k ha).const_mul
      ((A + 1) ^ k)
  apply squeeze_zero' ?_ ?_ hbound
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with q hq
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hq _)
  · filter_upwards [eventually_ge_atTop (0 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1] with q hq hlog
    have harg : 0 ≤ A * Real.log q := mul_nonneg hA.le (by linarith)
    have hceil : (logarithmicSampleSize A q : ℝ) ≤ A * Real.log q + 1 :=
      (Nat.ceil_lt_add_one harg).le
    have hs : (logarithmicSampleSize A q : ℝ) ≤ (A + 1) * Real.log q := by
      nlinarith
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg (logarithmicSampleSize A q)) hs k
    simpa only [mul_pow, mul_assoc] using
      mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hq (-a))

theorem log_affine_line_count_le {q : ℝ} (hq : 4 ≤ q) :
    Real.log (q * (q + 1)) ≤ (5 / 2 : ℝ) * Real.log q := by
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q + 1 := by linarith
  have hsmall := Real.log_le_log hq1 (show q + 1 ≤ 2 * q by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hq0.ne'] at hsmall
  have hlarge := Real.log_le_log
    (show 0 < (2 : ℝ) ^ 2 by norm_num) (show (2 : ℝ) ^ 2 ≤ q by nlinarith)
  rw [Real.log_pow] at hlarge
  norm_num only [Nat.cast_ofNat] at hlarge
  rw [Real.log_mul hq0.ne' hq1.ne']
  nlinarith

theorem tuple_failure_le_envelope {q A c0 : ℝ} (t : ℕ) (hq : 4 ≤ q)
    (hA : 0 < A) (ht : A * Real.log q ≤ (t : ℝ)) :
    2 * (q * (q + 1)) ^ (2 * t) * Real.exp (-c0 * (t : ℝ) ^ 2) ≤
      2 * Real.exp (-(c0 - 5 / A) * (t : ℝ) ^ 2) := by
  have hq0 : 0 < q := by linarith
  have hb : 0 < q * (q + 1) := mul_pos hq0 (by linarith)
  have hlog := log_affine_line_count_le hq
  have hcount : (q * (q + 1)) ^ (2 * t) ≤
      Real.exp (5 * (t : ℝ) * Real.log q) := by
    rw [← Real.exp_log (pow_pos hb (2 * t))]
    apply Real.exp_le_exp.mpr
    rw [Real.log_pow]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg t)]
  have hlogDiv : Real.log q ≤ (t : ℝ) / A :=
    (le_div_iff₀ hA).2 (by nlinarith [ht])
  have hexponent : 5 * (t : ℝ) * Real.log q - c0 * (t : ℝ) ^ 2 ≤
      -(c0 - 5 / A) * (t : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hlogDiv
      (show 0 ≤ 5 * (t : ℝ) by positivity)
    simp only [div_eq_mul_inv] at hmul ⊢
    nlinarith
  calc
    2 * (q * (q + 1)) ^ (2 * t) * Real.exp (-c0 * (t : ℝ) ^ 2) ≤
        2 * Real.exp (5 * (t : ℝ) * Real.log q) *
          Real.exp (-c0 * (t : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcount (by norm_num)) (Real.exp_pos _).le
    _ = 2 * Real.exp (5 * (t : ℝ) * Real.log q - c0 * (t : ℝ) ^ 2) := by
      rw [mul_assoc, ← Real.exp_add, sub_eq_add_neg, neg_mul]
    _ ≤ 2 * Real.exp (-(c0 - 5 / A) * (t : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num)

theorem tendsto_tuple_failure_atTop {A c0 : ℝ} (hc0 : 0 < c0) (hA : 5 / c0 < A) :
    Tendsto (fun q : ℝ =>
      2 * (q * (q + 1)) ^ (2 * logarithmicSampleSize A q) *
        Real.exp (-c0 * (logarithmicSampleSize A q : ℝ) ^ 2)) atTop (𝓝 0) := by
  have hA0 : 0 < A := lt_trans (div_pos (by norm_num) hc0) hA
  have hfive : 5 < A * c0 := (div_lt_iff₀ hc0).mp hA
  have hcoefficient : 0 < c0 - 5 / A := by
    have hdiv : 5 / A < c0 := (div_lt_iff₀ hA0).2 (by nlinarith)
    linarith
  have hsquare : Tendsto
      (fun q : ℝ => (logarithmicSampleSize A q : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp
      (tendsto_logarithmicSampleSize_atTop hA0)
  have henvelope : Tendsto
      (fun q : ℝ => 2 * Real.exp (-(c0 - 5 / A) *
        (logarithmicSampleSize A q : ℝ) ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_zero, one_mul, mul_zero] using
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        0 (c0 - 5 / A) hcoefficient).comp hsquare).const_mul (2 : ℝ)
  apply squeeze_zero' ?_ ?_ henvelope
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with q hq
    have hq0 : 0 ≤ q := by linarith
    positivity
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with q hq
    exact tuple_failure_le_envelope (logarithmicSampleSize A q) hq hA0
      (Nat.le_ceil (A * Real.log q))

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetOriginalDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Construction

open Filter Topology

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

theorem prob_originalLineCount_lt_five (hq : 2048 ≤ Fintype.card k)
    (d : NonzeroSlope k) (z : k) :
    (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).prob
        (fun a => originalLineCount a d z < 5) ≤
      Real.exp (-(Fintype.card k : ℝ) / 2048) := by
  classical
  let q : ℝ := Fintype.card k
  have hqR : 2048 ≤ q := by
    dsimp only [q]
    exact_mod_cast hq
  have hq0 : 0 < q := by linarith
  have hcoordinates : (Fintype.card (NonzeroSlope k) : ℝ) ≤ q := by
    dsimp only [q]
    exact_mod_cast Fintype.card_le_of_injective
      (fun d : NonzeroSlope k => d.val) Subtype.val_injective
  have hmean : q / 4 ≤
      (FiniteLaw.uniform (GadgetOutcome k)).expectation (fun a => originalLineCount a d z) := by
    have hm := LineCover.quarter_mul_le_survival_mean (Fintype.card k) (by omega)
    rw [← expectation_originalLineCount d z, FiniteLaw.pi_uniform] at hm
    exact hm
  have htail := uniform_coordinate_concentration
    (fun a : GadgetOutcome k => originalLineCount a d z)
    2 2 (4 * q) (q / 8) (by norm_num) (by positivity) (by positivity)
    (fun i a x => originalLineCount_update_abs_le a d z i x)
    (by norm_num) (by nlinarith)
  have hratio : (q / 8) ^ 2 / (4 * q) = q / 256 := by
    field_simp [hq0.ne']; ring
  have hmin : min ((q / 8) ^ 2 / (4 * q)) ((q / 8) / 2) = q / 256 := by
    rw [hratio]
    apply min_eq_left
    linarith
  rw [hmin] at htail
  have hexponent : -(1 / 4 : ℝ) * (q / 256) = -q / 1024 := by ring
  rw [hexponent] at htail
  have hbad :
      (FiniteLaw.uniform (GadgetOutcome k)).prob (fun a => originalLineCount a d z < 5) ≤
      (FiniteLaw.uniform (GadgetOutcome k)).prob
        (fun a => q / 8 ≤ |originalLineCount a d z -
          (FiniteLaw.uniform (GadgetOutcome k)).expectation
            (fun a => originalLineCount a d z)|) := by
    apply FiniteLaw.prob_mono
    intro a ha
    have habs := neg_le_abs (originalLineCount a d z -
      (FiniteLaw.uniform (GadgetOutcome k)).expectation (fun a => originalLineCount a d z))
    linarith
  have htwo : (2 : ℝ) ≤ Real.exp (q / 2048) := by
    have he := Real.add_one_le_exp (q / 2048)
    linarith
  rw [FiniteLaw.pi_uniform]
  change _ ≤ Real.exp (-q / 2048)
  calc
    _ ≤ 2 * Real.exp (-q / 1024) := hbad.trans htail
    _ ≤ Real.exp (q / 2048) * Real.exp (-q / 1024) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = Real.exp (-q / 2048) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem not_originalLineDensity_imp_exists_small_count (a : GadgetOutcome k)
    (ha : ¬ OriginalLineDensity a) :
    ∃ j : NonzeroSlope k × k, originalLineCount a j.1 j.2 < 5 := by
  classical
  simp only [OriginalLineDensity, not_forall, not_le] at ha
  obtain ⟨d, z, hz, hcard⟩ := ha
  refine ⟨(d, z), ?_⟩
  rw [originalLineCount_eq_retained_filter_card a d z hz]
  exact_mod_cast hcard

theorem prob_not_originalLineDensity_le (hq : 2048 ≤ Fintype.card k) :
    (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).prob
        (fun a => ¬ OriginalLineDensity a) ≤
      (Fintype.card k : ℝ) ^ 2 * Real.exp (-(Fintype.card k : ℝ) / 2048) := by
  classical
  let μ := FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)
  have htests : (Fintype.card (NonzeroSlope k × k) : ℝ) ≤ (Fintype.card k : ℝ) ^ 2 := by
    rw [Fintype.card_prod, Nat.cast_mul]
    have hc : (Fintype.card (NonzeroSlope k) : ℝ) ≤ (Fintype.card k : ℝ) := by
      exact_mod_cast Fintype.card_le_of_injective
        (fun d : NonzeroSlope k => d.val) Subtype.val_injective
    simpa only [pow_two] using
      mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (Fintype.card k))
  calc
    _ ≤ μ.prob (fun a => ∃ j : NonzeroSlope k × k, originalLineCount a j.1 j.2 < 5) :=
      μ.prob_mono not_originalLineDensity_imp_exists_small_count
    _ ≤ ∑ j : NonzeroSlope k × k,
        μ.prob (fun a => originalLineCount a j.1 j.2 < 5) :=
      μ.prob_exists_le _
    _ ≤ ∑ _j : NonzeroSlope k × k, Real.exp (-(Fintype.card k : ℝ) / 2048) := by
      apply Finset.sum_le_sum
      intro j _
      exact prob_originalLineCount_lt_five hq j.1 j.2
    _ = (Fintype.card (NonzeroSlope k × k) : ℝ) *
        Real.exp (-(Fintype.card k : ℝ) / 2048) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right htests (Real.exp_pos _).le

theorem prob_originalLineDensity_ge (hq : 2048 ≤ Fintype.card k) :
    1 - (Fintype.card k : ℝ) ^ 2 * Real.exp (-(Fintype.card k : ℝ) / 2048) ≤
      (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).prob
        OriginalLineDensity := by
  have h := prob_not_originalLineDensity_le (k := k) hq
  rw [FiniteLaw.prob_compl] at h
  linarith

theorem tendsto_originalDensity_failure_atTop :
    Tendsto (fun q : ℕ => (q : ℝ) ^ 2 * Real.exp (-(q : ℝ) / 2048))
      atTop (𝓝 0) := by
  have h : Tendsto (fun q : ℝ => q ^ 2 * Real.exp (-q / 2048)) atTop (𝓝 0) := by
    have h' := LineCover.tendsto_rpow_mul_exp_neg_rpow_atTop
      (2 : ℝ) (a := 1) (c := 1 / 2048) (by norm_num) (by norm_num)
    simpa [Real.rpow_natCast, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h'
  exact h.comp tendsto_natCast_atTop_atTop

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_SmallPrimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

private theorem exists_mem_mod_three_eq_two_of_prod
    (L : List ℕ) (hL : L.prod % 3 = 2) :
    ∃ p ∈ L, p % 3 = 2 := by
  induction L with
  | nil => simp at hL
  | cons a L ih =>
      by_cases ha : a % 3 = 2
      · exact ⟨a, List.mem_cons_self, ha⟩
      · have hmod : a % 3 = 0 ∨ a % 3 = 1 := by
          have := Nat.mod_lt a (by decide : 0 < 3)
          omega
        rcases hmod with ha0 | ha1
        · simp only [List.prod_cons, Nat.mul_mod, ha0, zero_mul, Nat.zero_mod] at hL
          contradiction
        · have htail : L.prod % 3 = 2 := by
            simpa only [List.prod_cons, Nat.mul_mod, ha1, one_mul, Nat.mod_mod] using hL
          obtain ⟨p, hp, hpmod⟩ := ih htail
          exact ⟨p, List.mem_cons_of_mem a hp, hpmod⟩

theorem exists_prime_dvd_mod_three_eq_two {n : ℕ} (hn : n % 3 = 2) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p % 3 = 2 := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨p, hp, hpmod⟩ :=
    exists_mem_mod_three_eq_two_of_prod n.primeFactorsList
      (by simpa only [Nat.prod_primeFactorsList hn0] using hn)
  exact ⟨p, Nat.prime_of_mem_primeFactorsList hp,
    Nat.dvd_of_mem_primeFactorsList hp, hpmod⟩

theorem exists_prime_gt_mod_three_eq_two (B : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ p % 3 = 2 := by
  let N := 3 * B.factorial - 1
  have hfacpos := Nat.factorial_pos B
  have hsucc : N + 1 = 3 * B.factorial := by
    dsimp [N]
    exact Nat.sub_add_cancel (by omega)
  have hNmod : N % 3 = 2 := by omega
  obtain ⟨p, hp, hpN, hpmod⟩ := exists_prime_dvd_mod_three_eq_two hNmod
  refine ⟨p, ?_, hp, hpmod⟩
  by_contra hnot
  have hpB : p ≤ B := Nat.le_of_not_gt hnot
  have hpfac : p ∣ B.factorial := Nat.dvd_factorial hp.pos hpB
  have hpprod : p ∣ 3 * B.factorial := dvd_mul_of_dvd_right hpfac 3
  have hsub : 3 * B.factorial - N = 1 := by omega
  have hpone : p ∣ 1 := by
    have h := Nat.dvd_sub hpprod hpN
    simpa only [hsub] using h
  have hple := Nat.le_of_dvd (by decide : 0 < 1) hpone
  have hptwo := hp.two_le
  omega

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Field_SubfieldBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F] [Fintype F]

theorem subfield_card_lt_of_ne_top (S : Subfield F) [Fintype S]
    (hS : S ≠ ⊤) : Fintype.card S < Fintype.card F := by
  apply Fintype.card_lt_of_injective_not_surjective
    (fun x : S => (x : F)) Subtype.val_injective
  intro hsurj
  apply hS
  apply top_unique
  intro x _
  obtain ⟨y, hy⟩ := hsurj x
  exact hy ▸ y.property

variable {p n : ℕ} [CharP F p]

theorem subfield_eq_top_of_card_eq_char (hp : p.Prime)
    (hcard : Fintype.card F = p) (S : Subfield F) : S = ⊤ := by
  classical
  let : Fintype S := Fintype.ofFinite S
  by_contra hS
  obtain ⟨m, _, hm⟩ := FiniteField.card S p
  have hpS : p ≤ Fintype.card S := by
    rw [hm]
    simpa only [pow_one] using
      (Nat.pow_le_pow_right hp.pos m.property : p ^ 1 ≤ p ^ (m : ℕ))
  have hlt := subfield_card_lt_of_ne_top S hS
  rw [hcard] at hlt
  exact (not_lt_of_ge hpS) hlt

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Field_ExtensionSubfields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

theorem primeField_subfield_eq_top (p : ℕ) [Fact p.Prime]
    (S : Subfield (ZMod p)) : S = ⊤ :=
  subfield_eq_top_of_card_eq_char (Fact.out : p.Prime) (ZMod.card p) S

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_Deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {P : Type*} [DecidableEq P]
  {shapes : Finset (Finset P)} {D n : ℕ}

theorem contribution_card_le (ignore : Finset (Finset P)) (test : Finset P)
    (a : Outcome shapes D) (H : ℕ)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H) :
    (contribution ignore test a).card ≤ D * H := by
  let A := a.val.filter (fun L => L.val ∉ ignore)
  change (A.biUnion Subtype.val ∩ test).card ≤ D * H
  rw [Finset.biUnion_inter]
  calc
    _ ≤ ∑ L ∈ A, (L.val ∩ test).card := Finset.card_biUnion_le
    _ ≤ ∑ _L ∈ A, H := Finset.sum_le_sum fun L hL =>
      hshape L.val L.property (Finset.mem_filter.mp hL).2
    _ = A.card * H := by simp
    _ ≤ D * H := Nat.mul_le_mul_right H
      ((Finset.card_filter_le a.val _).trans a.property)

private theorem card_sub_card_le_card_of_sdiff_subset
    {A B K : Finset P} (h : A \ B ⊆ K) :
    (A.card : ℝ) - (B.card : ℝ) ≤ (K.card : ℝ) := by
  have hc : A.card ≤ K.card + B.card :=
    (Finset.card_le_card_sdiff_add_card (s := A) (t := B)).trans
      (Nat.add_le_add_right (Finset.card_le_card h) B.card)
  have hr : (A.card : ℝ) ≤ (K.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast hc
  linarith

variable [instFintypeP : Fintype P]

theorem survivors_update_sdiff_subset (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n)
    (a : Outcome shapes D) :
    (survivors ignore (Function.update ω i a) ∩ test) \
        (survivors ignore ω ∩ test) ⊆ contribution ignore test (ω i) := by
  intro x hx
  rcases Finset.mem_sdiff.mp hx with ⟨hxnew, hxold⟩
  rcases Finset.mem_inter.mp hxnew with ⟨hxs, hxP⟩
  refine Finset.mem_inter.mpr ⟨?_, hxP⟩
  by_contra hxi
  apply hxold
  refine Finset.mem_inter.mpr ⟨mem_survivors.mpr ?_, hxP⟩
  intro j
  by_cases hji : j = i
  · subst j
    exact hxi
  · have hj := mem_survivors.mp hxs j
    simpa only [Function.update_of_ne hji] using hj

theorem survivors_sdiff_update_subset (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n)
    (a : Outcome shapes D) :
    (survivors ignore ω ∩ test) \
        (survivors ignore (Function.update ω i a) ∩ test) ⊆
      contribution ignore test a := by
  intro x hx
  rcases Finset.mem_sdiff.mp hx with ⟨hxold, hxnew⟩
  rcases Finset.mem_inter.mp hxold with ⟨hxs, hxP⟩
  refine Finset.mem_inter.mpr ⟨?_, hxP⟩
  by_contra hxa
  apply hxnew
  refine Finset.mem_inter.mpr ⟨mem_survivors.mpr ?_, hxP⟩
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self] using hxa
  · have hj := mem_survivors.mp hxs j
    simpa only [Function.update_of_ne hji] using hj

theorem retainedCount_update_bounds (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n)
    (a : Outcome shapes D) :
    -((contribution ignore test a).card : ℝ) ≤
        retainedCount ignore test (Function.update ω i a) - retainedCount ignore test ω ∧
      retainedCount ignore test (Function.update ω i a) - retainedCount ignore test ω ≤
        ((contribution ignore test (ω i)).card : ℝ) := by
  have hup := card_sub_card_le_card_of_sdiff_subset
    (survivors_update_sdiff_subset ignore test ω i a)
  have hdown := card_sub_card_le_card_of_sdiff_subset
    (survivors_sdiff_update_subset ignore test ω i a)
  change -((contribution ignore test a).card : ℝ) ≤
      ((survivors ignore (Function.update ω i a) ∩ test).card : ℝ) -
        ((survivors ignore ω ∩ test).card : ℝ) ∧ _
  exact ⟨by linarith, hup⟩

theorem retainedCount_update_abs_le (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n)
    (a : Outcome shapes D) :
    |retainedCount ignore test (Function.update ω i a) - retainedCount ignore test ω| ≤
      ((contribution ignore test (ω i)).card : ℝ) +
        ((contribution ignore test a).card : ℝ) := by
  obtain ⟨hlo, hhi⟩ := retainedCount_update_bounds ignore test ω i a
  have ho : 0 ≤ ((contribution ignore test (ω i)).card : ℝ) := Nat.cast_nonneg _
  have hn : 0 ≤ ((contribution ignore test a).card : ℝ) := Nat.cast_nonneg _
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem retainedCount_empty_bounds (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n) :
    0 ≤ retainedCount ignore test (Function.update ω i (emptyOutcome shapes D)) -
        retainedCount ignore test ω ∧
      retainedCount ignore test (Function.update ω i (emptyOutcome shapes D)) -
        retainedCount ignore test ω ≤ ((contribution ignore test (ω i)).card : ℝ) := by
  simpa only [contribution_emptyOutcome, Finset.card_empty, Nat.cast_zero, neg_zero]
    using retainedCount_update_bounds ignore test ω i (emptyOutcome shapes D)

theorem retainedCount_empty_abs_le (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n) :
    |retainedCount ignore test ω -
        retainedCount ignore test (Function.update ω i (emptyOutcome shapes D))| ≤
      ((contribution ignore test (ω i)).card : ℝ) := by
  obtain ⟨hlo, hhi⟩ := retainedCount_empty_bounds ignore test ω i
  rw [abs_sub_comm, abs_of_nonneg hlo]
  exact hhi

theorem not_rare_retainedCount_eq (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n)
    (h : ¬ rare ignore test (ω i)) :
    retainedCount ignore test ω =
      retainedCount ignore test (Function.update ω i (emptyOutcome shapes D)) := by
  have he : contribution ignore test (ω i) = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp h
  obtain ⟨hlo, hhi⟩ := retainedCount_empty_bounds ignore test ω i
  rw [he, Finset.card_empty, Nat.cast_zero] at hhi
  linarith

theorem retainedCount_empty_abs_le_mul (ignore : Finset (Finset P))
    (test : Finset P) (H : ℕ)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H)
    (ω : Fin n → Outcome shapes D) (i : Fin n) :
    |retainedCount ignore test ω -
        retainedCount ignore test (Function.update ω i (emptyOutcome shapes D))| ≤
      (D : ℝ) * (H : ℝ) := by
  apply (retainedCount_empty_abs_le ignore test ω i).trans
  exact_mod_cast contribution_card_le ignore test (ω i) H hshape

section FiniteExpectations

variable {Ω : Type*} [Fintype Ω]

theorem expectation_card_inter (μ : FiniteLaw Ω) (S : Ω → Finset P)
    (test : Finset P) :
    μ.expectation (fun ω => ((S ω ∩ test).card : ℝ)) =
      ∑ x ∈ test, μ.prob (fun ω => x ∈ S ω) := let _ := instFintypeP; by
  have hc (ω : Ω) : ((S ω ∩ test).card : ℝ) =
      ∑ x ∈ test, if x ∈ S ω then (1 : ℝ) else 0 := by
    simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_comm]
  simp only [FiniteLaw.expectation, hc, Finset.mul_sum,
    FiniteLaw.prob, mul_ite, mul_one, mul_zero]
  calc
    _ = ∑ x ∈ test, ∑ ω, if x ∈ S ω then μ.weight ω else (0 : ℝ) :=
      Finset.sum_comm (s := Finset.univ) (t := test)
        (f := fun (ω : Ω) (x : P) => if x ∈ S ω then μ.weight ω else (0 : ℝ))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hx : x ∈ S ω <;> simp only [hx, ite_true, ite_false]

theorem prob_nonempty_inter_le (μ : FiniteLaw Ω) (S : Ω → Finset P)
    (test : Finset P) :
    μ.prob (fun ω => (S ω ∩ test).Nonempty) ≤
      ∑ x ∈ test, μ.prob (fun ω => x ∈ S ω) := by
  rw [← expectation_card_inter μ S test]
  apply μ.prob_le_expectation
  · intro ω
    exact Nat.cast_nonneg _
  · intro ω hω
    exact Nat.one_le_cast.mpr (Finset.one_le_card.mpr hω)

end FiniteExpectations

theorem prob_rare_le (μ : FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) :
    μ.prob (rare ignore test) ≤
      ∑ x ∈ test, μ.prob (fun a => x ∈ deleted ignore a) :=
  prob_nonempty_inter_le μ (deleted ignore) test

theorem expectation_retainedCount (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) :
    (FiniteLaw.pi μ).expectation (retainedCount ignore test) =
      ∑ x ∈ test, (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ignore ω) :=
  expectation_card_inter (FiniteLaw.pi μ) (survivors ignore) test

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_CountConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {P : Type*} [Fintype P] [DecidableEq P]
  {shapes : Finset (Finset P)} {D n : ℕ}

theorem prob_rare_le_of_pointwise (μ : FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (p₀ : ℝ)
    (hpoint : ∀ x ∈ test, μ.prob (fun a => x ∈ deleted ignore a) ≤ p₀) :
    μ.prob (rare ignore test) ≤ (test.card : ℝ) * p₀ := by
  calc
    _ ≤ ∑ x ∈ test, μ.prob (fun a => x ∈ deleted ignore a) :=
      prob_rare_le μ ignore test
    _ ≤ ∑ _x ∈ test, p₀ := Finset.sum_le_sum fun x hx => hpoint x hx
    _ = (test.card : ℝ) * p₀ := by simp

theorem retainedCount_coordinate_concentration
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (H : ℕ)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H)
    (M V u : ℝ) (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hCM : 2 * (D : ℝ) * (H : ℝ) ≤ M)
    (hCV : (n : ℝ) * (2 * (D : ℝ) * (H : ℝ)) ^ 2 ≤ V) :
    (FiniteLaw.pi μ).prob (fun ω => u ≤
        |retainedCount ignore test ω -
          (FiniteLaw.pi μ).expectation (retainedCount ignore test)|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  apply Concentration.coordinate_concentration n μ (retainedCount ignore test)
    (fun _ => 2 * (D : ℝ) * (H : ℝ)) M V u hM hV hu
  · intro i ω a
    have hold : ((contribution ignore test (ω i)).card : ℝ) ≤
        (D : ℝ) * (H : ℝ) := by
      exact_mod_cast contribution_card_le ignore test (ω i) H hshape
    have hnew : ((contribution ignore test a).card : ℝ) ≤
        (D : ℝ) * (H : ℝ) := by
      exact_mod_cast contribution_card_le ignore test a H hshape
    apply (retainedCount_update_abs_le ignore test ω i a).trans
    linarith
  · intro i
    exact hCM
  · simpa using hCV

theorem retainedCount_rare_concentration
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (H : ℕ)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H)
    (p₀ : ℝ)
    (hpoint : ∀ i x, x ∈ test → (μ i).prob (fun a => x ∈ deleted ignore a) ≤ p₀)
    (M V u : ℝ) (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hCM : 2 * (D : ℝ) * (H : ℝ) ≤ M)
    (hCV : (n : ℝ) * ((D : ℝ) * (H : ℝ)) ^ 2 *
      ((test.card : ℝ) * p₀) ≤ V) :
    (FiniteLaw.pi μ).prob (fun ω => u ≤
        |retainedCount ignore test ω -
          (FiniteLaw.pi μ).expectation (retainedCount ignore test)|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  apply Concentration.rare_anchor_concentration n μ (retainedCount ignore test)
    (emptyOutcome shapes D) (fun _ => (D : ℝ) * (H : ℝ))
    (fun _ => (test.card : ℝ) * p₀) (fun _ => rare ignore test)
    M V u hM hV hu
  · intro i ω
    exact retainedCount_empty_abs_le_mul ignore test H hshape ω i
  · intro i ω h
    exact not_rare_retainedCount_eq ignore test ω i h
  · intro i
    exact prob_rare_le_of_pointwise (μ i) ignore test p₀ (hpoint i)
  · intro i
    simpa only [mul_assoc] using hCM
  · simpa [mul_assoc] using hCV

theorem prob_lt_le_prob_centered {Ω : Type*} [Fintype Ω]
    (ν : FiniteLaw Ω) (f : Ω → ℝ) (u : ℝ)
    (hmean : 2 * u ≤ ν.expectation f) :
    ν.prob (fun ω => f ω < u) ≤
      ν.prob (fun ω => u ≤ |f ω - ν.expectation f|) := by
  apply ν.prob_mono
  intro ω hω
  have hneg := neg_le_abs (f ω - ν.expectation f)
  linarith

theorem retainedCount_rare_lower_tail
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (H : ℕ)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H)
    (p₀ : ℝ)
    (hpoint : ∀ i x, x ∈ test → (μ i).prob (fun a => x ∈ deleted ignore a) ≤ p₀)
    (M V u : ℝ) (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hCM : 2 * (D : ℝ) * (H : ℝ) ≤ M)
    (hCV : (n : ℝ) * ((D : ℝ) * (H : ℝ)) ^ 2 *
      ((test.card : ℝ) * p₀) ≤ V)
    (hmean : 2 * u ≤ (FiniteLaw.pi μ).expectation (retainedCount ignore test)) :
    (FiniteLaw.pi μ).prob (fun ω => retainedCount ignore test ω < u) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) :=
  (prob_lt_le_prob_centered (FiniteLaw.pi μ) (retainedCount ignore test) u hmean).trans
    (retainedCount_rare_concentration μ ignore test H hshape p₀ hpoint M V u
      hM hV hu hCM hCV)

theorem expectation_retainedCount_ge_of_base_survival
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (δ : ℝ)
    (hbase : ∀ x ∈ test,
      δ ≤ (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ∅ ω)) :
    δ * (test.card : ℝ) ≤
      (FiniteLaw.pi μ).expectation (retainedCount ignore test) := by
  rw [expectation_retainedCount]
  calc
    δ * (test.card : ℝ) = ∑ _x ∈ test, δ := by simp [mul_comm]
    _ ≤ ∑ x ∈ test, (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ignore ω) := by
      apply Finset.sum_le_sum
      intro x hx
      apply (hbase x hx).trans
      apply (FiniteLaw.pi μ).prob_mono
      intro ω hω
      exact survivors_mono_ignore (Finset.empty_subset ignore) ω hω

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_MeanCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover.DeletionProcess

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {D : ℕ} {δ : ℝ} (process : DeletionProcess F D δ)

theorem expectation_base_count (test : Finset (Point F)) :
    process.law.expectation (retainedCount ∅ test) =
      process.survival * (test.card : ℝ) := by
  change (FiniteLaw.pi process.trials).expectation (retainedCount ∅ test) = _
  rw [expectation_retainedCount]
  simp_rw [process.uniformSurvival]
  simp [mul_comm]

theorem expectation_totalCount :
    process.law.expectation
        (retainedCount ∅ (Finset.univ : Finset (Point F))) =
      process.survival * (Fintype.card F : ℝ) ^ 2 := by
  rw [process.expectation_base_count]
  simp only [Finset.card_univ, card_point, Nat.cast_pow]

theorem expectation_base_lineCount (l : AffineLine F) :
    process.law.expectation (retainedCount ∅ (linePoints l)) =
      process.survival * (Fintype.card F : ℝ) := by
  simpa only [card_linePoints] using process.expectation_base_count (linePoints l)

theorem prob_selected_line_le (l : AffineLine F) :
    process.law.prob (fun ω => linePoints l ∈ selected ω) ≤
      (D : ℝ) / (Fintype.card F : ℝ) := by
  change (FiniteLaw.pi process.trials).prob
      (fun ω => linePoints l ∈ selected ω) ≤ _
  calc
    _ = (FiniteLaw.pi process.trials).prob
        (fun ω => ∃ i, ∃ S ∈ (ω i).val, S.val = linePoints l) := by
      congr 1
      funext ω
      exact propext mem_selected
    _ ≤ ∑ i, (FiniteLaw.pi process.trials).prob
        (fun ω => ∃ S ∈ (ω i).val, S.val = linePoints l) :=
      FiniteLaw.prob_exists_le (FiniteLaw.pi process.trials)
        (fun i ω => ∃ S ∈ (ω i).val, S.val = linePoints l)
    _ = ∑ i, (process.trials i).prob
        (fun a => ∃ S ∈ a.val, S.val = linePoints l) := by
      apply Finset.sum_congr rfl
      intro i _
      exact FiniteLaw.prob_pi_coordinate process.trials i
        (fun a => ∃ S ∈ a.val, S.val = linePoints l)
    _ ≤ (D : ℝ) / (Fintype.card F : ℝ) := process.lineCap l

theorem mem_ignored_line_survivors_imp (l : AffineLine F)
    (ω : process.Config) (x : Point F)
    (hx : x ∈ survivors {linePoints l} ω) :
    x ∈ survivors ∅ ω ∨ linePoints l ∈ selected ω := by
  by_cases hselected : linePoints l ∈ selected ω
  · exact Or.inr hselected
  · left
    have heq := survivors_insert_eq_of_not_selected
      (ignore := ∅) (ω := ω) hselected
    simp only [Finset.insert_empty] at heq
    exact heq ▸ hx

theorem prob_mem_ignored_line_le (l : AffineLine F) (x : Point F) :
    process.law.prob (fun ω => x ∈ survivors {linePoints l} ω) ≤
      process.survival + (D : ℝ) / (Fintype.card F : ℝ) := by
  calc
    _ ≤ process.law.prob
        (fun ω => x ∈ survivors ∅ ω ∨ linePoints l ∈ selected ω) :=
      process.law.prob_mono
        (fun ω hx => process.mem_ignored_line_survivors_imp l ω x hx)
    _ ≤ process.law.prob (fun ω => x ∈ survivors ∅ ω) +
        process.law.prob (fun ω => linePoints l ∈ selected ω) :=
      process.law.prob_union_le _ _
    _ ≤ process.survival + (D : ℝ) / (Fintype.card F : ℝ) :=
      add_le_add (process.uniformSurvival x).le (process.prob_selected_line_le l)

theorem expectation_ignored_lineCount_bounds (l : AffineLine F) :
    process.survival * (Fintype.card F : ℝ) ≤
        process.law.expectation (retainedCount {linePoints l} (linePoints l)) ∧
      process.law.expectation (retainedCount {linePoints l} (linePoints l)) ≤
        process.survival * (Fintype.card F : ℝ) + (D : ℝ) := by
  constructor
  · rw [← process.expectation_base_lineCount l]
    apply process.law.expectation_mono
    intro ω
    change ((survivors ∅ ω ∩ linePoints l).card : ℝ) ≤
      ((survivors {linePoints l} ω ∩ linePoints l).card : ℝ)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hs, hl⟩
    exact Finset.mem_inter.mpr
      ⟨survivors_mono_ignore (Finset.empty_subset {linePoints l}) ω hs, hl⟩
  · change (FiniteLaw.pi process.trials).expectation
        (retainedCount {linePoints l} (linePoints l)) ≤ _
    rw [expectation_retainedCount]
    calc
      _ ≤ ∑ _x ∈ linePoints l,
          (process.survival + (D : ℝ) / (Fintype.card F : ℝ)) :=
        Finset.sum_le_sum fun x _ => process.prob_mem_ignored_line_le l x
      _ = (Fintype.card F : ℝ) *
          (process.survival + (D : ℝ) / (Fintype.card F : ℝ)) := by
        simp only [Finset.sum_const, nsmul_eq_mul, card_linePoints]
      _ = process.survival * (Fintype.card F : ℝ) + (D : ℝ) := by
        have hq : (Fintype.card F : ℝ) ≠ 0 := by
          exact_mod_cast (Fintype.card_ne_zero (α := F))
        rw [mul_add, mul_div_cancel₀ (D : ℝ) hq,
          mul_comm (Fintype.card F : ℝ) process.survival]

end RyserCoveringCounterexample.LineCover.DeletionProcess

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_CountEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover.DeletionProcess

variable {F : Type*} [Field F] [Fintype F] [instDecidableEqF : DecidableEq F]
  {D : ℕ} {δ : ℝ} (process : DeletionProcess F D δ)

private theorem fieldCard_pos_real : 0 < (Fintype.card F : ℝ) := let _ := instDecidableEqF; by
  exact_mod_cast Fintype.card_pos (α := F)

theorem total_count_concentration (hD : 0 < D) (u : ℝ) (hu : 0 < u) :
    process.law.prob (fun ω => u ≤
        |retainedCount ∅ Finset.univ ω -
          process.survival * (Fintype.card F : ℝ) ^ 2|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) *
        min (u ^ 2 / (4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ) ^ 3))
          (u / (2 * (D : ℝ) ^ 2 * (Fintype.card F : ℝ)))) := by
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hq := fieldCard_pos_real (F := F)
  have hn : (process.trialsCount : ℝ) ≤ (D : ℝ) * (Fintype.card F : ℝ) := by
    exact_mod_cast process.trialsCount_le
  have hC : 2 * (D : ℝ) * ((D * Fintype.card F : ℕ) : ℝ) =
      2 * (D : ℝ) ^ 2 * (Fintype.card F : ℝ) := by
    rw [Nat.cast_mul]
    ring
  have hV : (process.trialsCount : ℝ) *
      (2 * (D : ℝ) * ((D * Fintype.card F : ℕ) : ℝ)) ^ 2 ≤
        4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ) ^ 3 := by
    rw [hC]
    calc
      _ ≤ ((D : ℝ) * (Fintype.card F : ℝ)) *
          (2 * (D : ℝ) ^ 2 * (Fintype.card F : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right hn (sq_nonneg _)
      _ = _ := by ring
  have h := retainedCount_coordinate_concentration process.trials ∅ Finset.univ
    (D * Fintype.card F)
    (fun S hS _ => by simpa using process.shapeSize S hS)
    (2 * (D : ℝ) ^ 2 * (Fintype.card F : ℝ))
    (4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ) ^ 3) u
    (by positivity) (by positivity) hu hC.le hV
  change process.law.prob (fun ω => u ≤
      |retainedCount ∅ Finset.univ ω -
        process.law.expectation (retainedCount ∅ Finset.univ)|) ≤ _ at h
  rw [process.expectation_totalCount] at h
  exact h

theorem ignored_line_count_concentration (hD : 0 < D) (l : AffineLine F)
    (u : ℝ) (hu : 0 < u) :
    process.law.prob (fun ω => u ≤
        |retainedCount {linePoints l} (linePoints l) ω -
          process.law.expectation (retainedCount {linePoints l} (linePoints l))|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) *
        min (u ^ 2 / (4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ)))
          (u / (2 * (D : ℝ) ^ 2))) := by
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hq := fieldCard_pos_real (F := F)
  have hn : (process.trialsCount : ℝ) ≤ (D : ℝ) * (Fintype.card F : ℝ) := by
    exact_mod_cast process.trialsCount_le
  have hC : 2 * (D : ℝ) * (D : ℝ) = 2 * (D : ℝ) ^ 2 := by ring
  have hV : (process.trialsCount : ℝ) * (2 * (D : ℝ) * (D : ℝ)) ^ 2 ≤
      4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ) := by
    calc
      _ ≤ ((D : ℝ) * (Fintype.card F : ℝ)) *
          (2 * (D : ℝ) * (D : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right hn (sq_nonneg _)
      _ = _ := by ring
  exact retainedCount_coordinate_concentration process.trials {linePoints l}
    (linePoints l) D
    (fun S hS hnot => process.sparse S hS l (by simpa using hnot))
    (2 * (D : ℝ) ^ 2) (4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ)) u
    (by positivity) (by positivity) hu hC.le hV

end RyserCoveringCounterexample.LineCover.DeletionProcess

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_CountTailNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

theorem count_variance_ratio {q D ε k : ℝ} (hq : 0 < q) (hD : D ≠ 0) :
    (q ^ (k + 1 / 2 + ε)) ^ 2 / (4 * D ^ 5 * q ^ (2 * k + 1)) =
      q ^ (2 * ε) / (4 * D ^ 5) := by
  have hp : (q ^ (k + 1 / 2 + ε)) ^ 2 =
      q ^ (2 * ε) * q ^ (2 * k + 1) := by
    calc
      _ = q ^ ((k + 1 / 2 + ε) * (2 : ℝ)) := by
        rw [Real.rpow_mul hq.le, Real.rpow_two]
      _ = q ^ (2 * ε + (2 * k + 1)) := by congr 1; ring
      _ = _ := Real.rpow_add hq _ _
  rw [hp]
  have hpow : q ^ (2 * k + 1) ≠ 0 := (Real.rpow_pos_of_pos hq _).ne'
  field_simp [hD, hpow]

theorem count_coordinate_ratio {q D ε k : ℝ} (hq : 0 < q) (hD : D ≠ 0) :
    q ^ (k + 1 / 2 + ε) / (2 * D ^ 2 * q ^ k) =
      q ^ (1 / 2 + ε) / (2 * D ^ 2) := by
  rw [show k + 1 / 2 + ε = (1 / 2 + ε) + k by ring, Real.rpow_add hq]
  have hpow : q ^ k ≠ 0 := (Real.rpow_pos_of_pos hq _).ne'
  field_simp [hD, hpow]

theorem count_variance_ratio_le_coordinate {q D ε : ℝ}
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hε : ε ≤ 1 / 2) :
    q ^ (2 * ε) / (4 * D ^ 5) ≤ q ^ (1 / 2 + ε) / (2 * D ^ 2) := by
  have hD0 : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq
  have hp : q ^ (2 * ε) ≤ q ^ (1 / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have hDpow : D ^ 2 ≤ D ^ 5 := by
    calc
      D ^ 2 = D ^ 2 * 1 := by ring
      _ ≤ D ^ 2 * D ^ 3 := mul_le_mul_of_nonneg_left (one_le_pow₀ hD) (sq_nonneg D)
      _ = D ^ 5 := by ring
  have hden : 2 * D ^ 2 ≤ 4 * D ^ 5 := by nlinarith [sq_nonneg D]
  exact div_le_div₀ (Real.rpow_nonneg hq0 _) hp (by positivity) hden

theorem count_tail_le_stretched_exp {q D ε k : ℝ}
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hε : ε ≤ 1 / 2) :
    2 * Real.exp (-(1 / 4 : ℝ) *
      min ((q ^ (k + 1 / 2 + ε)) ^ 2 / (4 * D ^ 5 * q ^ (2 * k + 1)))
        (q ^ (k + 1 / 2 + ε) / (2 * D ^ 2 * q ^ k))) ≤
      2 * Real.exp (-q ^ (2 * ε) / (16 * D ^ 5)) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hD0 : D ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hD)
  rw [count_variance_ratio hq0 hD0, count_coordinate_ratio hq0 hD0,
    min_eq_left (count_variance_ratio_le_coordinate hq hD hε)]
  have hexponent : -(1 / 4 : ℝ) * (q ^ (2 * ε) / (4 * D ^ 5)) =
      -q ^ (2 * ε) / (16 * D ^ 5) := by
    field_simp [hD0]
    ring
  rw [hexponent]

theorem total_count_tail_le_stretched_exp {q ε : ℝ} {D : ℕ}
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hε : ε ≤ 1 / 2) :
    2 * Real.exp (-(1 / 4 : ℝ) *
      min ((q ^ (3 / 2 + ε)) ^ 2 / (4 * (D : ℝ) ^ 5 * q ^ 3))
        (q ^ (3 / 2 + ε) / (2 * (D : ℝ) ^ 2 * q))) ≤
      2 * Real.exp (-q ^ (2 * ε) / (16 * (D : ℝ) ^ 5)) := by
  have hDr : 1 ≤ (D : ℝ) := by exact_mod_cast hD
  simpa only [one_add_one_eq_two, mul_one, Real.rpow_one,
    show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num,
    show (2 : ℝ) + 1 = (3 : ℕ) by norm_num, Real.rpow_natCast] using
    (count_tail_le_stretched_exp (q := q) (D := (D : ℝ)) (ε := ε) (k := 1) hq hDr hε)

theorem line_count_tail_le_stretched_exp {q ε : ℝ} {D : ℕ}
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hε : ε ≤ 1 / 2) :
    2 * Real.exp (-(1 / 4 : ℝ) *
      min ((q ^ (1 / 2 + ε)) ^ 2 / (4 * (D : ℝ) ^ 5 * q))
        (q ^ (1 / 2 + ε) / (2 * (D : ℝ) ^ 2))) ≤
      2 * Real.exp (-q ^ (2 * ε) / (16 * (D : ℝ) ^ 5)) := by
  have hDr : 1 ≤ (D : ℝ) := by exact_mod_cast hD
  simpa only [mul_zero, zero_add, Real.rpow_zero, Real.rpow_one, mul_one] using
    (count_tail_le_stretched_exp (q := q) (D := (D : ℝ)) (ε := ε) (k := 0) hq hDr hε)

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_GoodCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {D : ℕ} {δ : ℝ}

namespace DeletionProcess

variable (process : DeletionProcess F D δ)

theorem prob_not_goodCounts (ε : ℝ) (hD : 1 ≤ D)
    (_hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    process.law.prob (fun ω => ¬ GoodCounts process ε ω) ≤
      2 * (1 + (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1)) *
        Real.exp (-(Fintype.card F : ℝ) ^ (2 * ε) / (16 * (D : ℝ) ^ 5)) := by
  have hqNat : 1 ≤ Fintype.card F :=
    Nat.succ_le_iff.mpr (Fintype.card_pos (α := F))
  have hq : 1 ≤ (Fintype.card F : ℝ) := by exact_mod_cast hqNat
  have hq0 : 0 < (Fintype.card F : ℝ) := lt_of_lt_of_le zero_lt_one hq
  have hD0 : 0 < D := lt_of_lt_of_le Nat.zero_lt_one hD
  let T : process.Config → Prop := fun ω =>
    (Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 + ε) ≤
      |((survivors ∅ ω).card : ℝ) - process.survival * (Fintype.card F : ℝ) ^ 2|
  let L : AffineLine F → process.Config → Prop := fun l ω =>
    (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤
      |retainedCount {linePoints l} (linePoints l) ω -
        process.law.expectation (retainedCount {linePoints l} (linePoints l))|
  let B : ℝ := 2 * Real.exp
    (-(Fintype.card F : ℝ) ^ (2 * ε) / (16 * (D : ℝ) ^ 5))
  have htotal : process.law.prob T ≤ B := by
    have h := (process.total_count_concentration hD0
      ((Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 + ε))
      (Real.rpow_pos_of_pos hq0 _)).trans
        (total_count_tail_le_stretched_exp hq hD hεhalf)
    simpa only [T, B, retainedCount, Finset.inter_univ] using h
  have hline (l : AffineLine F) : process.law.prob (L l) ≤ B := by
    exact (process.ignored_line_count_concentration hD0 l
      ((Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 + ε))
      (Real.rpow_pos_of_pos hq0 _)).trans
        (line_count_tail_le_stretched_exp hq hD hεhalf)
  have hcover : ∀ ω, ¬ GoodCounts process ε ω → T ω ∨ ∃ l, L l ω := by
    intro ω hbad
    by_cases ht : T ω
    · exact Or.inl ht
    · right
      by_contra hlines
      apply hbad
      refine ⟨?_, ?_⟩
      · exact (lt_of_not_ge ht).le
      · intro l
        have hl : ¬ L l ω := fun h => hlines ⟨l, h⟩
        have habs :
            |retainedCount {linePoints l} (linePoints l) ω -
              process.law.expectation (retainedCount {linePoints l} (linePoints l))| ≤
            (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 + ε) := (lt_of_not_ge hl).le
        obtain ⟨hlo, hhi⟩ := abs_le.mp habs
        obtain ⟨hmlo, hmhi⟩ := process.expectation_ignored_lineCount_bounds l
        constructor <;> linarith
  calc
    _ ≤ process.law.prob (fun ω => T ω ∨ ∃ l, L l ω) :=
      process.law.prob_mono hcover
    _ ≤ process.law.prob T + process.law.prob (fun ω => ∃ l, L l ω) :=
      process.law.prob_union_le T (fun ω => ∃ l, L l ω)
    _ ≤ B + ∑ l, process.law.prob (L l) :=
      add_le_add htotal (FiniteLaw.prob_exists_le process.law L)
    _ ≤ B + ∑ _l : AffineLine F, B :=
      add_le_add le_rfl (Finset.sum_le_sum fun l _ => hline l)
    _ = (1 + (Fintype.card (AffineLine F) : ℝ)) * B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ = _ := by
      simp only [card_affineLine, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      dsimp only [B]
      ring

end DeletionProcess
end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_TupleConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

theorem countTailConstant_pos {D H : ℕ} {δ : ℝ}
    (hD : 0 < D) (hH : 0 < H) (hδ : 0 < δ) :
    0 < countTailConstant D H δ := by
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hH
  unfold countTailConstant
  apply lt_min <;> positivity

theorem tupleTailConstant_pos {D h : ℕ} {δ : ℝ}
    (hD : 0 < D) (hh : 0 < h) (hδ : 0 < δ) :
    0 < tupleTailConstant D h δ :=
  countTailConstant_pos hD
    (Nat.mul_pos (Nat.mul_pos (by decide) hD) hh) hδ

private theorem variance_budget_real (n D q C t : ℝ)
    (hD : 0 ≤ D) (hq : 0 < q) (hn : n ≤ D * q) :
    n * C ^ 2 * (t ^ 2 * (D / q)) ≤ D ^ 2 * C ^ 2 * t ^ 2 := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hscale : 0 ≤ C ^ 2 * (t ^ 2 * (D / q)) :=
    mul_nonneg (sq_nonneg C)
      (mul_nonneg (sq_nonneg t) (div_nonneg hD (le_of_lt hq)))
  calc
    n * C ^ 2 * (t ^ 2 * (D / q)) =
        n * (C ^ 2 * (t ^ 2 * (D / q))) := by ring
    _ ≤ (D * q) * (C ^ 2 * (t ^ 2 * (D / q))) :=
      mul_le_mul_of_nonneg_right hn hscale
    _ = D ^ 2 * C ^ 2 * t ^ 2 := by
      field_simp [hq0]

private theorem tail_exponent_identity (D C T δ : ℝ)
    (hD : 0 < D) (hC : 0 < C) (hT : 0 < T) :
    -(1 / 4 : ℝ) *
        min (((δ * T ^ 2 / 2) ^ 2) / (D ^ 2 * C ^ 2 * T ^ 2))
          ((δ * T ^ 2 / 2) / (2 * C)) =
      -(min (δ ^ 2 / (16 * D ^ 2 * C ^ 2))
          (δ / (16 * C))) * T ^ 2 := by
  let a : ℝ := δ ^ 2 / (16 * D ^ 2 * C ^ 2)
  let b : ℝ := δ / (16 * C)
  have hA :
      ((δ * T ^ 2 / 2) ^ 2) / (D ^ 2 * C ^ 2 * T ^ 2) =
        4 * a * T ^ 2 := by
    dsimp [a]
    field_simp [ne_of_gt hD, ne_of_gt hC, ne_of_gt hT]; ring
  have hB : (δ * T ^ 2 / 2) / (2 * C) = 4 * b * T ^ 2 := by
    dsimp [b]
    field_simp [ne_of_gt hC]; ring
  change -(1 / 4 : ℝ) * min _ _ = -(min a b) * T ^ 2
  rw [hA, hB]
  rcases le_total a b with h | h
  · have hs : 4 * a * T ^ 2 ≤ 4 * b * T ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4))
        (sq_nonneg T)
    rw [min_eq_left hs, min_eq_left h]
    ring
  · have hs : 4 * b * T ^ 2 ≤ 4 * a * T ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4))
        (sq_nonneg T)
    rw [min_eq_right hs, min_eq_right h]
    ring

section General

variable {P : Type*} [Fintype P] [DecidableEq P]
  {shapes : Finset (Finset P)} {D n : ℕ}

theorem retainedCount_square_lower_tail
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (H q t : ℕ) (δ : ℝ)
    (hD : 0 < D) (hH : 0 < H) (hq : 0 < q) (ht : 0 < t) (hδ : 0 < δ)
    (hn : n ≤ D * q) (hcard : test.card = t * t)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H)
    (hpoint : ∀ i x, x ∈ test →
      (μ i).prob (fun a => x ∈ deleted ∅ a) ≤ (D : ℝ) / (q : ℝ))
    (hbase : ∀ x ∈ test,
      δ ≤ (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ∅ ω)) :
    (FiniteLaw.pi μ).prob
        (fun ω => retainedCount ignore test ω < δ * (t : ℝ) ^ 2 / 2) ≤
      2 * Real.exp (-(countTailConstant D H δ) * (t : ℝ) ^ 2) := by
  let C : ℝ := (D : ℝ) * (H : ℝ)
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hH
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have htr : 0 < (t : ℝ) := by exact_mod_cast ht
  have hC : 0 < C := mul_pos hDr hHr
  have hnr : (n : ℝ) ≤ (D : ℝ) * (q : ℝ) := by exact_mod_cast hn
  have hcardReal : (test.card : ℝ) = (t : ℝ) ^ 2 := by
    rw [hcard, Nat.cast_mul, pow_two]
  have hpointIgnore : ∀ i x, x ∈ test →
      (μ i).prob (fun a => x ∈ deleted ignore a) ≤ (D : ℝ) / (q : ℝ) := by
    intro i x hx
    calc
      _ ≤ (μ i).prob (fun a => x ∈ deleted ∅ a) := by
        apply (μ i).prob_mono
        intro a hxa
        rcases mem_deleted.mp hxa with ⟨L, hL, hnot, hxL⟩
        exact mem_deleted.mpr ⟨L, hL, by simp, hxL⟩
      _ ≤ _ := hpoint i x hx
  have hCV : (n : ℝ) * C ^ 2 * ((test.card : ℝ) * ((D : ℝ) / (q : ℝ))) ≤
      (D : ℝ) ^ 2 * C ^ 2 * (t : ℝ) ^ 2 := by
    rw [hcardReal]
    exact variance_budget_real (n : ℝ) (D : ℝ) (q : ℝ) C (t : ℝ)
      hDr.le hqr hnr
  have hmean0 := expectation_retainedCount_ge_of_base_survival μ ignore test δ hbase
  rw [hcardReal] at hmean0
  have hmean : 2 * (δ * (t : ℝ) ^ 2 / 2) ≤
      (FiniteLaw.pi μ).expectation (retainedCount ignore test) := by
    calc
      _ = δ * (t : ℝ) ^ 2 := by ring
      _ ≤ _ := hmean0
  have htail := retainedCount_rare_lower_tail μ ignore test H hshape
    ((D : ℝ) / (q : ℝ)) hpointIgnore
    (2 * C) ((D : ℝ) ^ 2 * C ^ 2 * (t : ℝ) ^ 2)
    (δ * (t : ℝ) ^ 2 / 2)
    (by positivity) (by positivity) (by positivity)
    (le_of_eq (by dsimp [C]; ring)) hCV hmean
  apply htail.trans_eq
  apply congrArg (fun z : ℝ => 2 * Real.exp z)
  simpa only [countTailConstant, C] using
    tail_exponent_identity (D : ℝ) C (t : ℝ) δ hDr hC htr

end General

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {shapes : Finset (Finset (Point F))} {D n h t : ℕ}

theorem admissibleTuple_lower_tail
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (a : LineTuple F t) (ha : AdmissibleTuple shapes D h a)
    (δ : ℝ) (hD : 0 < D) (hh : 0 < h) (ht : 0 < t) (hδ : 0 < δ)
    (hn : n ≤ D * Fintype.card F)
    (hpoint : ∀ i x,
      (μ i).prob (fun b => x ∈ deleted ∅ b) ≤ (D : ℝ) / (Fintype.card F : ℝ))
    (hbase : ∀ x,
      δ ≤ (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ∅ ω)) :
    (FiniteLaw.pi μ).prob (fun ω =>
        retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2) ≤
      2 * Real.exp (-(tupleTailConstant D h δ) * (t : ℝ) ^ 2) := by
  have hH : 0 < 2 * D * h := Nat.mul_pos (Nat.mul_pos (by decide) hD) hh
  have hq : 0 < Fintype.card F := Fintype.card_pos_iff.mpr ⟨0⟩
  simpa only [tupleTailConstant] using retainedCount_square_lower_tail
    μ (tupleShapes a) (crossPoints a) (2 * D * h) (Fintype.card F) t δ
    hD hH hq ht hδ hn ha.2.1 ha.2.2
    (fun i x _ => hpoint i x) (fun x _ => hbase x)

theorem prob_exists_admissibleTuple_bad_le
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (δ : ℝ) (hD : 0 < D) (hh : 0 < h) (ht : 0 < t) (hδ : 0 < δ)
    (hn : n ≤ D * Fintype.card F)
    (hpoint : ∀ i x,
      (μ i).prob (fun b => x ∈ deleted ∅ b) ≤ (D : ℝ) / (Fintype.card F : ℝ))
    (hbase : ∀ x,
      δ ≤ (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ∅ ω)) :
    (FiniteLaw.pi μ).prob (fun ω => ∃ a : LineTuple F t,
        AdmissibleTuple shapes D h a ∧
          retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2) ≤
      2 * (Fintype.card (LineTuple F t) : ℝ) *
        Real.exp (-(tupleTailConstant D h δ) * (t : ℝ) ^ 2) := by
  classical
  calc
    _ ≤ ∑ a : LineTuple F t, (FiniteLaw.pi μ).prob (fun ω =>
        AdmissibleTuple shapes D h a ∧
          retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2) :=
      (FiniteLaw.pi μ).prob_exists_le _
    _ ≤ ∑ _a : LineTuple F t,
        2 * Real.exp (-(tupleTailConstant D h δ) * (t : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : AdmissibleTuple shapes D h a
      · calc
          _ ≤ (FiniteLaw.pi μ).prob (fun ω =>
              retainedCount (tupleShapes a) (crossPoints a) ω <
                δ * (t : ℝ) ^ 2 / 2) := by
            apply (FiniteLaw.pi μ).prob_mono
            intro ω hω
            exact hω.2
          _ ≤ _ := admissibleTuple_lower_tail μ a ha δ hD hh ht hδ hn hpoint hbase
      · simp only [ha, false_and, FiniteLaw.prob_false]
        positivity
    _ = _ := by simp [mul_assoc, mul_comm]

theorem card_lineTuple_le (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (t : ℕ) :
    Fintype.card (LineTuple F t) ≤
      (Fintype.card F * (Fintype.card F + 1)) ^ (2 * t) := by
  classical
  calc
    Fintype.card (LineTuple F t) ≤
        Fintype.card ((Fin t ⊕ Fin t) → AffineLine F) :=
      Fintype.card_le_of_injective
        (fun a : LineTuple F t =>
          (a : (Fin t ⊕ Fin t) → AffineLine F))
        Function.Embedding.coe_injective
    _ = _ := by
      rw [Fintype.card_fun]
      simp [AffineLine, Direction, two_mul, Nat.mul_comm]

theorem prob_exists_admissibleTuple_bad_le_card_bound
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (δ : ℝ) (hD : 0 < D) (hh : 0 < h) (ht : 0 < t) (hδ : 0 < δ)
    (hn : n ≤ D * Fintype.card F)
    (hpoint : ∀ i x,
      (μ i).prob (fun b => x ∈ deleted ∅ b) ≤ (D : ℝ) / (Fintype.card F : ℝ))
    (hbase : ∀ x,
      δ ≤ (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ∅ ω)) :
    (FiniteLaw.pi μ).prob (fun ω => ∃ a : LineTuple F t,
        AdmissibleTuple shapes D h a ∧
          retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2) ≤
      2 * ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1)) ^ (2 * t) *
        Real.exp (-(tupleTailConstant D h δ) * (t : ℝ) ^ 2) := by
  have hcard : (Fintype.card (LineTuple F t) : ℝ) ≤
      ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1)) ^ (2 * t) := by
    exact_mod_cast card_lineTuple_le F t
  apply (prob_exists_admissibleTuple_bad_le μ δ hD hh ht hδ hn hpoint hbase).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcard (by norm_num : (0 : ℝ) ≤ 2))
    (Real.exp_pos _).le

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

theorem not_goodTuples_iff (process : DeletionProcess F D δ) (h t : ℕ)
    (ω : process.Config) :
    ¬ GoodTuples process h t ω ↔
      ∃ a : LineTuple F t, AdmissibleTuple process.shapes D h a ∧
        retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2 := by
  classical
  simp only [GoodTuples, not_forall, not_le, exists_prop]

theorem DeletionProcess.prob_not_goodTuples (process : DeletionProcess F D δ)
    (h t : ℕ) (hD : 0 < D) (hh : 0 < h) (ht : 0 < t) (hδ : 0 < δ) :
    process.law.prob (fun ω => ¬ GoodTuples process h t ω) ≤
      2 * ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1)) ^ (2 * t) *
        Real.exp (-(tupleTailConstant D h δ) * (t : ℝ) ^ 2) := by
  calc
    _ ≤ process.law.prob (fun ω => ∃ a : LineTuple F t,
        AdmissibleTuple process.shapes D h a ∧
          retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2) := by
      apply process.law.prob_mono
      intro ω hω
      exact (not_goodTuples_iff process h t ω).mp hω
    _ ≤ _ := prob_exists_admissibleTuple_bad_le_card_bound process.trials δ
      hD hh ht hδ process.trialsCount_le process.pointCap
      (fun x => process.point_survival_ge x)

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section
open Filter Topology

theorem savingExponent_lt_tenth : savingExponent < 1 / 10 := by
  norm_num [savingExponent]

end
end RyserCoveringCounterexample.Incidence

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

theorem low_occupancy_decay_pos (D : ℕ) {κ : ℝ} (hκ : κ ≤ 1) :
    0 < ((10 * (D + 1) : ℕ) : ℝ) * (1 / 2 - κ / 4) - D := by
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hmul := mul_nonneg (by positivity : 0 ≤ (D : ℝ) + 1)
    (sub_nonneg.mpr hκ)
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  nlinarith

theorem high_occupancy_decay_pos (D : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 < ((10 * (D + 1) : ℕ) : ℝ) * (1 / 2 + κ / 4) - D := by
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hmul := mul_pos (by positivity : 0 < (D : ℝ) + 1) hκ
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  nlinarith

theorem tendsto_lowFailureEnvelope_atTop (D : ℕ) (δ : ℝ) {A κ : ℝ}
    (hA : 0 < A) (hκ : 0 < κ) (hκone : κ ≤ 1) :
    Tendsto (lowFailureEnvelope D δ A κ) atTop (𝓝 0) := by
  have hfirst := (tendsto_rpow_neg_atTop
    (by positivity : 0 < 7 * κ / 30)).const_mul ((D : ℝ) + 4)
  have hsecond := tendsto_rpow_neg_atTop (by positivity : 0 < 3 * κ / 4)
  have hsurvivors := (hfirst.add hsecond).const_mul (16 / δ)
  have hdecay : 0 < (1 / 2 : ℝ) - κ / 4 := by linarith
  have hparallel := (tendsto_sampleSize_pow_mul_rpow_neg_atTop 2 hA hdecay).const_mul
    (16 : ℝ)
  have hconcurrent := (tendsto_sampleSize_pow_mul_rpow_neg_atTop 3 hA hdecay).const_mul
    (32 : ℝ)
  have hoccupancy := (tendsto_sampleSize_pow_mul_rpow_neg_atTop
    (2 * (10 * (D + 1))) hA (low_occupancy_decay_pos D hκone)).const_mul
      ((D : ℝ) * (8 * (D : ℝ)) ^ (10 * (D + 1)))
  unfold lowFailureEnvelope
  simpa only [mul_zero, add_zero] using
    (hsurvivors.add (hparallel.add hconcurrent)).add hoccupancy

theorem tendsto_highFailureEnvelope_atTop (D : ℕ) (δ ρ : ℝ) {A κ : ℝ}
    (hA : 0 < A) (hκ : 0 < κ) :
    Tendsto (highFailureEnvelope D δ ρ A κ) atTop (𝓝 0) := by
  have hsurvivors := (tendsto_rpow_neg_atTop
    (by positivity : 0 < 3 * κ / 20)).const_mul (4 * ((D : ℝ) + 4) / (δ * ρ))
  have hdecay : 0 < (1 / 2 : ℝ) + κ / 4 := by positivity
  have hgeometry := (tendsto_sampleSize_pow_mul_rpow_neg_atTop 2 hA hdecay).add
    (tendsto_sampleSize_pow_mul_rpow_neg_atTop 3 hA hdecay)
  have hoccupancy := (tendsto_sampleSize_pow_mul_rpow_neg_atTop
    (2 * (10 * (D + 1))) hA (high_occupancy_decay_pos D hκ)).const_mul
      ((D : ℝ) * (4 * (D : ℝ)) ^ (10 * (D + 1)))
  unfold highFailureEnvelope
  simpa only [mul_zero, add_zero] using
    (hsurvivors.add hgeometry).add hoccupancy

theorem eventually_lowFailureEnvelope_lt_one (D : ℕ) (δ : ℝ) {A κ : ℝ}
    (hA : 0 < A) (hκ : 0 < κ) (hκone : κ ≤ 1) :
    ∀ᶠ q : ℝ in atTop, lowFailureEnvelope D δ A κ q < 1 :=
  (tendsto_order.mp (tendsto_lowFailureEnvelope_atTop D δ hA hκ hκone)).2 1
    (by norm_num)

theorem eventually_highFailureEnvelope_lt_one (D : ℕ) (δ ρ : ℝ) {A κ : ℝ}
    (hA : 0 < A) (hκ : 0 < κ) :
    ∀ᶠ q : ℝ in atTop, highFailureEnvelope D δ ρ A κ q < 1 :=
  (tendsto_order.mp (tendsto_highFailureEnvelope_atTop D δ ρ hA hκ)).2 1
    (by norm_num)

theorem eventually_sampleSize_le_mul_rpow {A a c : ℝ}
    (hA : 0 < A) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ q : ℝ in atTop, (logarithmicSampleSize A q : ℝ) ≤ c * q ^ a := by
  have hlim := tendsto_sampleSize_pow_mul_rpow_neg_atTop 1 hA ha
  filter_upwards [(tendsto_order.mp hlim).2 c hc,
    eventually_gt_atTop (0 : ℝ)] with q hsmall hq
  rw [pow_one, Real.rpow_neg hq.le, ← div_eq_mul_inv] at hsmall
  exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hq _)).mp hsmall).le

theorem eventually_sampling_size_bounds (D : ℕ) {A ρ κ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hκ : 0 < κ) :
    ∀ᶠ q : ℝ in atTop,
      8 ≤ q ∧
      10 * (D + 1) ≤ logarithmicSampleSize A q ∧
      (4 * (10 * (D + 1)) : ℝ) ≤ q / 2 ∧
      2 * (logarithmicSampleSize A q : ℝ) ≤ q / 2 ∧
      2 * (logarithmicSampleSize A q : ℝ) ≤ q ^ (1 / 2 + κ / 4) ∧
      2 * (logarithmicSampleSize A q : ℝ) ≤ ρ * q / 2 := by
  have hlog := (tendsto_logarithmicSampleSize_atTop hA).eventually_ge_atTop
    (((10 * (D + 1) : ℕ) : ℝ))
  have hlinear := eventually_sampleSize_le_mul_rpow hA (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hpencil := eventually_sampleSize_le_mul_rpow hA
    (by positivity : 0 < (1 / 2 : ℝ) + κ / 4) (by norm_num : (0 : ℝ) < 1 / 2)
  have hcomplement := eventually_sampleSize_le_mul_rpow hA (by norm_num : (0 : ℝ) < 1)
    (by positivity : 0 < ρ / 4)
  filter_upwards [eventually_ge_atTop (8 : ℝ), hlog, hlinear, hpencil, hcomplement,
    eventually_ge_atTop (8 * (10 * ((D : ℝ) + 1)))] with
      q hq ht hlo hhi hco hlarge
  have htNat : 10 * (D + 1) ≤ logarithmicSampleSize A q := by exact_mod_cast ht
  rw [Real.rpow_one] at hlo hco
  refine ⟨hq, htNat, ?_, ?_, ?_, ?_⟩ <;> nlinarith

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

private theorem eventually_mul_rpow_le_mul (C c a b : ℝ)
    (hc : 0 < c) (hab : a < b) :
    ∀ᶠ q : ℝ in atTop, C * q ^ a ≤ c * q ^ b := by
  have hgap : 0 < b - a := sub_pos.mpr hab
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop hgap).eventually_ge_atTop (C / c)] with q hq hlarge
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hC : C ≤ q ^ (b - a) * c := (div_le_iff₀ hc).mp hlarge
  calc
    C * q ^ a ≤ (q ^ (b - a) * c) * q ^ a :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hqpos.le _)
    _ = c * q ^ b := by
      rw [mul_comm (q ^ (b - a)) c, mul_assoc, ← Real.rpow_add hqpos]
      rw [show b - a + a = b by ring]

private theorem eventually_rigidityBudget_div_le (D : ℕ) {δ c κ : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hκ : 0 ≤ κ) (hκmax : κ ≤ 1 / 10) :
    ∀ᶠ q : ℝ in atTop, rigidityBudget D κ q / (δ * q) ≤ c * q / 2 := by
  have hsmall := eventually_mul_rpow_le_mul ((D : ℝ) + 4) (δ * c / 2)
    (3 / 2 + κ / 10) 2 (by positivity) (by linarith)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall] with q hq hsmallq
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  apply (div_le_iff₀ (mul_pos hδ hqpos)).2
  calc
    rigidityBudget D κ q ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10) :=
      rigidityBudget_le D hκ hq
    _ ≤ (δ * c / 2) * q ^ (2 : ℝ) := hsmallq
    _ = (c * q / 2) * (δ * q) := by rw [Real.rpow_two]; ring

theorem eventually_rigidityBudget_div_le_min (D : ℕ) {δ ρ κ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hκ : 0 < κ) (hκmax : κ ≤ 1 / 10) :
    ∀ᶠ q : ℝ in atTop,
      rigidityBudget D κ q / (δ * q) ≤ min (q / 2) (ρ * q / 2) := by
  filter_upwards [eventually_rigidityBudget_div_le D hδ zero_lt_one hκ.le hκmax,
    eventually_rigidityBudget_div_le D hδ hρ hκ.le hκmax] with q hleft hright
  exact le_min (by simpa only [one_mul] using hleft) hright

theorem eventually_rigidity_heavy_bounds (D : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (hκmax : κ ≤ 1 / 10) :
    ∀ᶠ q : ℝ in atTop,
      1 < q ^ (1 / 2 - κ / 3) ∧
        rigidityBudget D κ q / (q ^ (1 / 2 - κ / 3) - 1) ≤ q ^ (1 + κ) := by
  have hd : 0 < (1 / 2 : ℝ) - κ / 3 := by linarith
  have hgap : (3 / 2 : ℝ) + κ / 10 < (1 + κ) + (1 / 2 - κ / 3) := by
    linarith
  have hsmall := eventually_mul_rpow_le_mul (2 * ((D : ℝ) + 4)) 1
    (3 / 2 + κ / 10) ((1 + κ) + (1 / 2 - κ / 3)) zero_lt_one hgap
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop hd).eventually_ge_atTop 2, hsmall]
      with q hq hT hsmallq
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  rw [one_mul, Real.rpow_add hqpos (1 + κ) (1 / 2 - κ / 3)] at hsmallq
  have hscaled := mul_le_mul_of_nonneg_left hT
    (Real.rpow_nonneg hqpos.le (1 + κ))
  constructor
  · linarith
  · apply (div_le_iff₀ (by linarith : 0 < q ^ (1 / 2 - κ / 3) - 1)).2
    calc
      rigidityBudget D κ q ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10) :=
        rigidityBudget_le D hκ.le hq
      _ ≤ q ^ (1 + κ) * (q ^ (1 / 2 - κ / 3) - 1) := by
        nlinarith only [hsmallq, hscaled]

theorem eventually_line_error_le_half {δ κ : ℝ}
    (hδ : 0 < δ) (hκmax : κ ≤ 1 / 10) :
    ∀ᶠ q : ℝ in atTop, q ^ (1 / 2 + κ / 10) ≤ δ * q / 2 := by
  have hsmall := eventually_mul_rpow_le_mul 1 (δ / 2) (1 / 2 + κ / 10) 1
    (by positivity) (by linarith)
  filter_upwards [hsmall] with q hsmallq
  calc
    q ^ (1 / 2 + κ / 10) ≤ (δ / 2) * q ^ (1 : ℝ) := by
      simpa only [one_mul] using hsmallq
    _ = δ * q / 2 := by rw [Real.rpow_one]; ring

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_RigidityParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open Filter Topology

theorem eventually_rigidityParameters (D : ℕ) {δ ρ A κ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hA : 0 < A) (hκ : 0 < κ)
    (hκsmall : κ ≤ 1 / 10) :
    ∀ᶠ q : ℝ in atTop, RigidityParameters D δ ρ A κ q := by
  have hsizes := eventually_sampling_size_bounds D hA hρ hκ
  have hgaps := eventually_rigidityBudget_div_le_min D hδ hρ hκ hκsmall
  have hheavy := eventually_rigidity_heavy_bounds D hκ hκsmall
  have hlow := eventually_lowFailureEnvelope_lt_one D δ hA hκ
    (show κ ≤ 1 by linarith)
  have hhigh := eventually_highFailureEnvelope_lt_one D δ ρ hA hκ
  have hline := eventually_line_error_le_half hδ hκsmall
  filter_upwards [hsizes, hgaps, hheavy, hlow, hhigh, hline] with
    q hsize hgap hheavyq hlo hhi hlin
  rcases hsize with ⟨hq, hht, hmh, hmt, hrt, hnt⟩
  have hhtR : ((10 * (D + 1) : ℕ) : ℝ) ≤ (logarithmicSampleSize A q : ℝ) := by
    exact_mod_cast hht
  have ht0 : (0 : ℝ) ≤ logarithmicSampleSize A q := Nat.cast_nonneg _
  refine {
    q_one := by linarith
    m_four := by linarith
    m_h := ?_
    m_t := hmt
    h_t := hht
    r_t := by linarith
    r_h := by linarith
    n_t := by linarith
    n_h := by linarith
    T_one := hheavyq.1
    gap_half := hgap.trans (min_le_left _ _)
    gap_rho := hgap.trans (min_le_right _ _)
    heavy := hheavyq.2
    low := hlo
    high := hhi
    lineerror := hlin }
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using hmh

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_LineCover_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology
open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

universe u

theorem prob_not_goodLineCover_le
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {D : ℕ} {δ ρ A : ℝ} (process : DeletionProcess F D δ)
    (hD : 0 < D) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hq : Incidence.incidenceThreshold ≤ Fintype.card F)
    (hsub : Incidence.SmallProperSubfields F)
    (params : RigidityParameters D δ ρ A Incidence.savingExponent (Fintype.card F)) :
    process.law.prob (fun ω => ¬ GoodLineCover δ ρ ω) ≤
      linecoverFailureBound D δ A (Fintype.card F) := by
  let h := 10 * (D + 1)
  let t := logarithmicSampleSize A (Fintype.card F)
  have hh : 0 < h := by dsimp [h]; omega
  have ht : 0 < t := lt_of_lt_of_le hh params.h_t
  have hε : 0 < Incidence.savingExponent / 10 := by
    exact div_pos Incidence.savingExponent_pos (by norm_num)
  have hεhalf : Incidence.savingExponent / 10 ≤ 1 / 2 := by
    linarith [Incidence.savingExponent_lt_tenth]
  have hcounts := process.prob_not_goodCounts (Incidence.savingExponent / 10)
    (by omega : 1 ≤ D) hε hεhalf
  have htuples := process.prob_not_goodTuples h t hD hh ht hδ
  have hbad : process.law.prob (fun ω => ¬ GoodLineCover δ ρ ω) ≤
      process.law.prob (fun ω =>
        ¬ GoodCounts process (Incidence.savingExponent / 10) ω ∨
        ¬ GoodTuples process h t ω) := by
    apply process.law.prob_mono
    intro ω hnot
    by_cases hc : GoodCounts process (Incidence.savingExponent / 10) ω
    · right
      intro htup
      exact hnot (goodLineCover_of_goodCounts_goodTuples process hδ hρ hq hsub
        params ω hc htup)
    · exact Or.inl hc
  exact hbad.trans ((process.law.prob_union_le _ _).trans (add_le_add hcounts htuples))

theorem tendsto_linecoverFailureBound (D : ℕ) {δ A : ℝ}
    (hD : 0 < D) (hδ : 0 < δ)
    (hA : 5 / tupleTailConstant D (10 * (D + 1)) δ < A) :
    Tendsto (linecoverFailureBound D δ A) atTop (𝓝 0) := by
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hc0 := tupleTailConstant_pos hD
    (show 0 < 10 * (D + 1) by omega) hδ
  have hc := tendsto_count_failure_atTop hDr
    (show 0 < Incidence.savingExponent / 10 from
      div_pos Incidence.savingExponent_pos (by norm_num))
  have ht := tendsto_tuple_failure_atTop hc0 hA
  unfold linecoverFailureBound
  simpa only [add_zero] using hc.add ht

theorem uniform_linecover_probability (D : ℕ) (δ ρ : ℝ)
    (hD : 0 < D) (hδ : 0 < δ) (hρ : 0 < ρ) (η : ℝ) (hη : 0 < η) :
    ∃ Q : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      Q ≤ Fintype.card F → Incidence.SmallProperSubfields F →
      ∀ process : DeletionProcess F D δ,
        1 - η ≤ process.law.prob (GoodLineCover δ ρ) := by
  let c0 := tupleTailConstant D (10 * (D + 1)) δ
  have hc0 : 0 < c0 := tupleTailConstant_pos hD (by omega) hδ
  let A := 6 / c0
  have hA : 0 < A := div_pos (by norm_num) hc0
  have hA5 : 5 / c0 < A := div_lt_div_of_pos_right (by norm_num) hc0
  have hnumeric := eventually_rigidityParameters D hδ hρ hA
    Incidence.savingExponent_pos Incidence.savingExponent_lt_tenth.le
  have hfailure : ∀ᶠ q : ℝ in atTop, linecoverFailureBound D δ A q ≤ η :=
    (tendsto_linecoverFailureBound D hD hδ hA5).eventually_le_const hη
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp (hnumeric.and hfailure)
  refine ⟨max ⌈R⌉₊ Incidence.incidenceThreshold, ?_⟩
  intro F instField instFintype instDecidable hQ hsub process
  have hRcard : R ≤ (Fintype.card F : ℝ) :=
    (Nat.le_ceil R).trans (by
      exact_mod_cast (le_max_left ⌈R⌉₊ Incidence.incidenceThreshold).trans hQ)
  have hq : Incidence.incidenceThreshold ≤ Fintype.card F :=
    (le_max_right ⌈R⌉₊ Incidence.incidenceThreshold).trans hQ
  obtain ⟨params, hbound⟩ := hR (Fintype.card F) hRcard
  have hprob := (prob_not_goodLineCover_le process hD hδ hρ hq hsub params).trans hbound
  rw [process.law.prob_compl] at hprob
  linarith

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology
noncomputable section

namespace RyserCoveringCounterexample.Construction

theorem exists_prime_goodGadget_above (B : ℕ) :
    ∃ (p : ℕ) (hp : p.Prime), B < p ∧ 5 < p ∧ p % 3 = 2 ∧
      letI : Fact p.Prime := ⟨hp⟩
      ∃ a : GadgetOutcome (ZMod p), GoodGadget a := by
  classical
  obtain ⟨Q, hQ⟩ := LineCover.uniform_linecover_probability
    3 (1 / 4) (1 / 100) (by norm_num) (by norm_num) (by norm_num)
    (1 / 4) (by norm_num)
  have hsmall : ∀ᶠ q : ℕ in atTop,
      (q : ℝ) ^ 2 * Real.exp (-(q : ℝ) / 2048) < 1 / 4 :=
    (tendsto_order.mp tendsto_originalDensity_failure_atTop).2 _ (by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hsmall
  obtain ⟨p, hpbound, hp, hpmod⟩ :=
    exists_prime_gt_mod_three_eq_two (B + Q + N + 2048)
  have hpB : B < p := by omega
  have hp5 : 5 < p := by omega
  have hpQ : Q ≤ p := by omega
  have hpN : N ≤ p := by omega
  have hp2048 : 2048 ≤ p := by omega
  refine ⟨p, hp, hpB, hp5, hpmod, ?_⟩
  let : Fact p.Prime := ⟨hp⟩
  have hcard : 3 < Fintype.card (ZMod p) := by simpa using (show 3 < p by omega)
  have hcop : Nat.Coprime 3 (Fintype.card (ZMod p) - 1) :=
    coprime_three_zmod_card_sub_one hpmod
  have hsub : Incidence.SmallProperSubfields (ZMod p) := by
    intro M hM
    exact (hM (primeField_subfield_eq_top p M)).elim
  have hline := hQ (ZMod p) (by simpa using hpQ) hsub
    (cubicDeletionProcess hcop hcard)
  change 1 - (1 / 4 : ℝ) ≤
    (FiniteLaw.pi (gadgetTrials (k := ZMod p))).prob
      (LineCover.GoodLineCover (1 / 4) (1 / 100)) at hline
  rw [← gadgetLaw_map_config, FiniteLaw.prob_map] at hline
  have horiginal := prob_originalLineDensity_ge (k := ZMod p)
    (by simpa using hp2048)
  change 1 - (Fintype.card (ZMod p) : ℝ) ^ 2 *
      Real.exp (-(Fintype.card (ZMod p) : ℝ) / 2048) ≤
    (gadgetLaw (ZMod p)).prob OriginalLineDensity at horiginal
  have hfailure : (Fintype.card (ZMod p) : ℝ) ^ 2 *
      Real.exp (-(Fintype.card (ZMod p) : ℝ) / 2048) < 1 / 4 := by
    simpa using hN p hpN
  have hex : ∃ a : GadgetOutcome (ZMod p), OriginalLineDensity a ∧
      LineCover.GoodLineCover (1 / 4) (1 / 100) (gadgetConfig a) := by
    by_contra hnot
    have himp : ∀ a : GadgetOutcome (ZMod p), OriginalLineDensity a →
        ¬ LineCover.GoodLineCover (1 / 4) (1 / 100) (gadgetConfig a) := by
      intro a ha hgood
      exact hnot ⟨a, ha, hgood⟩
    have hmono := (gadgetLaw (ZMod p)).prob_mono himp
    rw [FiniteLaw.prob_compl] at hmono
    linarith
  obtain ⟨a, ha, hgood⟩ := hex
  refine ⟨a, goodGadget_of_events hcop hcard ?_ a ha hgood⟩
  simpa using (show 200 < 19 * p by omega)

theorem exists_prime_goodGadget_oai :
    ∃ (p : ℕ) (hp : p.Prime), 5 < p ∧ p % 3 = 2 ∧
      letI : Fact p.Prime := ⟨hp⟩
      ∃ a : GadgetOutcome (ZMod p), GoodGadget a := by
  obtain ⟨p, hp, _, hp5, hpmod, ha⟩ := exists_prime_goodGadget_above 0
  exact ⟨p, hp, hp5, hpmod, ha⟩

end RyserCoveringCounterexample.Construction

end

end OAI
end

theorem solution : type_of% @OAI.RyserCoveringCounterexample.Construction.exists_prime_goodGadget_oai := @OAI.RyserCoveringCounterexample.Construction.exists_prime_goodGadget_oai
