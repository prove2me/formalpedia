-- Prove2me | solution 1 for HindsightGain.Uniform.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T02:59:01.725774+00:00
-- url     : https://prove2.me/submissions/abb4903f-2e45-4a86-b0dc-465c342f7d5e

import Mathlib
import Definitions.Def_HindsightGain_Uniform_rademacher

section
set_option autoImplicit false
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.deprecated false
noncomputable section

namespace HindsightGain.Uniform.Dev.Khin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- flip coordinate `i` -/
def flipAt (i : ι) (ε : ι → Bool) : ι → Bool := Function.update ε i (!ε i)

/-- Walsh function -/
def chi (A : Finset ι) (ε : ι → Bool) : ℝ := ∏ i ∈ A, sign (ε i)

/-- average over the cube -/
def avg (f : (ι → Bool) → ℝ) : ℝ := (∑ ε, f ε) / (Fintype.card (ι → Bool) : ℝ)

/-- Walsh coefficient -/
def coef (f : (ι → Bool) → ℝ) (A : Finset ι) : ℝ := avg (fun ε => f ε * chi A ε)

/-- the cube Laplacian -/
def Lop (f : (ι → Bool) → ℝ) (ε : ι → Bool) : ℝ := (∑ i, (f ε - f (flipAt i ε))) / 2

lemma sign_not (b : Bool) : sign (!b) = - sign b := by cases b <;> simp [sign]

lemma sign_mul_self (b : Bool) : sign b * sign b = 1 := by cases b <;> simp [sign]

lemma card_cube_pos : (0 : ℝ) < (Fintype.card (ι → Bool) : ℝ) := by
  have : 0 < Fintype.card (ι → Bool) := Fintype.card_pos
  exact_mod_cast this

lemma flipAt_flipAt (i : ι) (ε : ι → Bool) : flipAt i (flipAt i ε) = ε := by
  ext j
  by_cases h : j = i
  · subst h; simp [flipAt]
  · simp [flipAt, h]

lemma sum_flipAt (i : ι) (g : (ι → Bool) → ℝ) : ∑ ε, g (flipAt i ε) = ∑ ε, g ε :=
  Equiv.sum_comp (Function.Involutive.toPerm (flipAt i) (fun ε => flipAt_flipAt i ε)) g

lemma sum_eq_zero_of_flip (i : ι) (g : (ι → Bool) → ℝ) (h : ∀ ε, g (flipAt i ε) = - g ε) :
    ∑ ε, g ε = 0 := by
  have h1 := sum_flipAt i g
  simp only [h, Finset.sum_neg_distrib] at h1
  linarith

lemma chi_flipAt (A : Finset ι) (i : ι) (ε : ι → Bool) :
    chi A (flipAt i ε) = if i ∈ A then - chi A ε else chi A ε := by
  unfold chi
  by_cases hi : i ∈ A
  · rw [if_pos hi, ← Finset.mul_prod_erase A _ hi, ← Finset.mul_prod_erase A (fun j => sign (ε j)) hi]
    have : ∏ j ∈ A.erase i, sign (flipAt i ε j) = ∏ j ∈ A.erase i, sign (ε j) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have : j ≠ i := Finset.ne_of_mem_erase hj
      simp [flipAt, this]
    rw [this]
    simp [flipAt, sign_not]
  · rw [if_neg hi]
    refine Finset.prod_congr rfl fun j hj => ?_
    have : j ≠ i := fun h => hi (h ▸ hj)
    simp [flipAt, this]

lemma chi_mul_self (A : Finset ι) (ε : ι → Bool) : chi A ε * chi A ε = 1 := by
  unfold chi
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => sign_mul_self _

lemma chi_empty (ε : ι → Bool) : chi (∅ : Finset ι) ε = 1 := by simp [chi]

lemma orth (A B : Finset ι) :
    ∑ ε, chi A ε * chi B ε = if A = B then (Fintype.card (ι → Bool) : ℝ) else 0 := by
  by_cases hAB : A = B
  · subst hAB
    simp [chi_mul_self]
  · rw [if_neg hAB]
    have : ∃ i, ¬ (i ∈ A ↔ i ∈ B) := by
      by_contra hc
      push_neg at hc
      exact hAB (Finset.ext hc)
    obtain ⟨i, hi⟩ := this
    apply sum_eq_zero_of_flip i
    intro ε
    simp only [chi_flipAt]
    by_cases h1 : i ∈ A <;> by_cases h2 : i ∈ B <;> simp_all

lemma complete (ε η : ι → Bool) :
    ∑ A : Finset ι, chi A ε * chi A η = if ε = η then (Fintype.card (ι → Bool) : ℝ) else 0 := by
  have h1 : ∀ A : Finset ι, chi A ε * chi A η = ∏ i ∈ A, (sign (ε i) * sign (η i)) := by
    intro A; unfold chi; rw [Finset.prod_mul_distrib]
  simp_rw [h1]
  have h2 : ∑ A : Finset ι, ∏ i ∈ A, (sign (ε i) * sign (η i))
      = ∏ i, (1 + sign (ε i) * sign (η i)) := by
    rw [Finset.prod_one_add, Finset.powerset_univ]
  rw [h2]
  by_cases h : ε = η
  · subst h
    rw [if_pos rfl]
    have : ∀ i, (1 + sign (ε i) * sign (ε i)) = 2 := fun i => by rw [sign_mul_self]; norm_num
    simp [this, Fintype.card_fun]
  · rw [if_neg h]
    have : ∃ i, ε i ≠ η i := by
      by_contra hc; push_neg at hc; exact h (funext hc)
    obtain ⟨i, hi⟩ := this
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases h1 : ε i <;> cases h2 : η i <;> simp_all [sign]

lemma expansion (f : (ι → Bool) → ℝ) (ε : ι → Bool) :
    f ε = ∑ A : Finset ι, coef f A * chi A ε := by
  have hN := card_cube_pos (ι := ι)
  unfold coef avg
  have : ∀ A : Finset ι, (∑ η, f η * chi A η) / (Fintype.card (ι → Bool) : ℝ) * chi A ε
      = (∑ η, f η * (chi A η * chi A ε)) / (Fintype.card (ι → Bool) : ℝ) := by
    intro A
    rw [div_mul_eq_mul_div, Finset.sum_mul]
    simp_rw [mul_assoc]
  simp_rw [this]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, complete]
  simp

lemma avg_mul_expansion (f g : (ι → Bool) → ℝ) (d : Finset ι → ℝ)
    (hg : ∀ ε, g ε = ∑ A : Finset ι, d A * chi A ε) :
    avg (fun ε => f ε * g ε) = ∑ A : Finset ι, d A * coef f A := by
  unfold avg coef avg
  simp_rw [hg, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun ε _ => ?_
  ring

lemma Lop_expansion (f : (ι → Bool) → ℝ) (ε : ι → Bool) :
    Lop f ε = ∑ A : Finset ι, ((A.card : ℝ) * coef f A) * chi A ε := by
  unfold Lop
  have key : ∀ A : Finset ι, ∑ i, (coef f A * chi A ε - coef f A * chi A (flipAt i ε))
      = 2 * (((A.card : ℝ) * coef f A) * chi A ε) := by
    intro A
    simp_rw [chi_flipAt]
    have : ∀ i : ι, (coef f A * chi A ε - coef f A * (if i ∈ A then -chi A ε else chi A ε))
        = if i ∈ A then 2 * (coef f A * chi A ε) else 0 := by
      intro i; split_ifs <;> ring
    simp_rw [this]
    rw [← Finset.sum_filter]
    simp
    ring
  have h1 : ∑ i, (f ε - f (flipAt i ε)) =
      ∑ A : Finset ι, ∑ i, (coef f A * chi A ε - coef f A * chi A (flipAt i ε)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [expansion f ε, expansion f (flipAt i ε), ← Finset.sum_sub_distrib]
  rw [h1]
  simp_rw [key]
  rw [← Finset.mul_sum]
  ring

lemma coef_even (f : (ι → Bool) → ℝ) (hf : ∀ ε, f (fun i => !ε i) = f ε) (A : Finset ι)
    (hA : Odd A.card) : coef f A = 0 := by
  have hneg : ∀ ε : ι → Bool, chi A (fun i => !ε i) = - chi A ε := by
    intro ε
    unfold chi
    have : ∀ i, sign (!ε i) = -1 * sign (ε i) := fun i => by rw [sign_not]; ring
    simp_rw [this]
    rw [Finset.prod_mul_distrib, Finset.prod_const, hA.neg_one_pow]
    ring
  have hs : ∑ ε : ι → Bool, f ε * chi A ε = ∑ ε : ι → Bool, f (fun i => !ε i) * chi A (fun i => !ε i) := by
    let e : (ι → Bool) ≃ (ι → Bool) :=
      ⟨fun ε i => !ε i, fun ε i => !ε i, fun ε => by ext; simp, fun ε => by ext; simp⟩
    exact (Equiv.sum_comp e (fun ε => f ε * chi A ε)).symm
  simp_rw [hf, hneg, mul_neg, Finset.sum_neg_distrib] at hs
  unfold coef avg
  have : ∑ ε : ι → Bool, f ε * chi A ε = 0 := by linarith
  rw [this]; simp

lemma szarek_even (f : (ι → Bool) → ℝ) (hf : ∀ ε, f (fun i => !ε i) = f ε) :
    avg (fun ε => f ε * f ε) - (avg f) ^ 2 ≤ (avg (fun ε => f ε * Lop f ε)) / 2 := by
  have e1 : avg (fun ε => f ε * f ε) = ∑ A : Finset ι, coef f A * coef f A :=
    avg_mul_expansion f f _ (expansion f)
  have e2 : avg (fun ε => f ε * Lop f ε) = ∑ A : Finset ι, ((A.card : ℝ) * coef f A) * coef f A :=
    avg_mul_expansion f (Lop f) _ (Lop_expansion f)
  have e3 : avg f = coef f ∅ := by
    unfold coef; simp [chi_empty]
  rw [e1, e2, e3]
  have hsplit : ∑ A : Finset ι, coef f A * coef f A
      = coef f ∅ * coef f ∅ + ∑ A ∈ Finset.univ.erase ∅, coef f A * coef f A :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
  have hle : ∑ A ∈ Finset.univ.erase ∅, coef f A * coef f A ≤
      (∑ A : Finset ι, ((A.card : ℝ) * coef f A) * coef f A) / 2 := by
    rw [le_div_iff₀ (by norm_num), Finset.sum_mul]
    have hs2 : ∑ A : Finset ι, ((A.card : ℝ) * coef f A) * coef f A
        = ∑ A ∈ Finset.univ.erase ∅, ((A.card : ℝ) * coef f A) * coef f A := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ∅)]; simp
    rw [hs2]
    refine Finset.sum_le_sum fun A hA => ?_
    have hne : A ≠ ∅ := Finset.ne_of_mem_erase hA
    have hc : 1 ≤ A.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
    by_cases hodd : Odd A.card
    · rw [coef_even f hf A hodd]; simp
    · have h2 : 2 ≤ A.card := by
        rcases Nat.even_or_odd A.card with he | ho
        · obtain ⟨k, hk⟩ := he; omega
        · exact absurd ho hodd
      have : (2 : ℝ) ≤ A.card := by exact_mod_cast h2
      nlinarith [mul_self_nonneg (coef f A)]
  rw [pow_two]
  linarith

lemma avg_mono (f g : (ι → Bool) → ℝ) (h : ∀ ε, f ε ≤ g ε) : avg f ≤ avg g := by
  unfold avg
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun ε _ => h ε) card_cube_pos.le

/-- the Rademacher sum on the cube -/
def rsum (a : ι → ℝ) (ε : ι → Bool) : ℝ := ∑ i, sign (ε i) * a i

lemma rsum_flipAt (a : ι → ℝ) (i : ι) (ε : ι → Bool) :
    rsum a (flipAt i ε) = rsum a ε - 2 * sign (ε i) * a i := by
  unfold rsum
  have : ∀ j, sign (flipAt i ε j) * a j
      = sign (ε j) * a j + if j = i then -2 * sign (ε i) * a i else 0 := by
    intro j
    by_cases h : j = i
    · subst h; simp [flipAt, sign_not]; ring
    · simp [flipAt, h]
  simp_rw [this]
  rw [Finset.sum_add_distrib]
  simp
  ring

lemma avg_rsum_sq (a : ι → ℝ) : avg (fun ε => rsum a ε * rsum a ε) = ∑ i, a i ^ 2 := by
  have hN := card_cube_pos (ι := ι)
  have h1 : ∀ ε, rsum a ε * rsum a ε
      = ∑ i, ∑ j, (a i * a j) * (chi {i} ε * chi {j} ε) := by
    intro ε
    unfold rsum
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [chi]; ring
  unfold avg
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ i, ∑ ε : ι → Bool, ∑ j, (a i * a j) * (chi {i} ε * chi {j} ε) = a i ^ 2 * (Fintype.card (ι → Bool) : ℝ) := by
    intro i
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, orth, Finset.singleton_inj]
    simp [Finset.sum_ite_eq]
    ring
  simp_rw [h2]
  rw [← Finset.sum_mul]
  field_simp

lemma szarek_finite (a : ι → ℝ) :
    ∑ i, a i ^ 2 ≤ 2 * (avg (fun ε => |rsum a ε|)) ^ 2 := by
  set f : (ι → Bool) → ℝ := fun ε => |rsum a ε| with hfdef
  have heven : ∀ ε, f (fun i => !ε i) = f ε := by
    intro ε
    have : rsum a (fun i => !ε i) = - rsum a ε := by
      unfold rsum
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sign_not]; ring
    simp only [hfdef, this, abs_neg]
  have h1 := szarek_even f heven
  have hff : ∀ ε, f ε * f ε = rsum a ε * rsum a ε := fun ε => abs_mul_abs_self _
  have h2 : avg (fun ε => f ε * Lop f ε) ≤ avg (fun ε => rsum a ε * rsum a ε) := by
    apply avg_mono
    intro ε
    unfold Lop
    rw [mul_div_assoc', Finset.mul_sum, div_le_iff₀ (by norm_num)]
    have h3 : ∀ i, f ε * (f ε - f (flipAt i ε))
        ≤ (rsum a ε * rsum a ε - rsum a ε * rsum a (flipAt i ε)) := by
      intro i
      have : rsum a ε * rsum a (flipAt i ε) ≤ f ε * f (flipAt i ε) := by
        calc rsum a ε * rsum a (flipAt i ε) ≤ |rsum a ε * rsum a (flipAt i ε)| := le_abs_self _
          _ = _ := abs_mul _ _
      rw [mul_sub, hff]
      linarith
    calc ∑ i, f ε * (f ε - f (flipAt i ε))
        ≤ ∑ i, (rsum a ε * rsum a ε - rsum a ε * rsum a (flipAt i ε)) :=
          Finset.sum_le_sum fun i _ => h3 i
      _ = rsum a ε * rsum a ε * 2 := by
          simp_rw [rsum_flipAt]
          have : ∀ i, rsum a ε * rsum a ε - rsum a ε * (rsum a ε - 2 * sign (ε i) * a i)
              = 2 * (sign (ε i) * a i) * rsum a ε := fun i => by ring
          simp_rw [this]
          rw [← Finset.sum_mul, ← Finset.mul_sum]
          unfold rsum; ring
  have h4 : avg (fun ε => f ε * f ε) = ∑ i, a i ^ 2 := by
    rw [← avg_rsum_sq]; simp_rw [hff]
  rw [avg_rsum_sq] at h2
  have : avg f = avg (fun ε => |rsum a ε|) := rfl
  rw [this] at h1
  linarith

end HindsightGain.Uniform.Dev.Khin

end
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace HindsightGain.Uniform.Dev.Khin

instance signLaw_prob (J : Type) [Countable J] : IsProbabilityMeasure (signLaw J) := by
  unfold signLaw; infer_instance

/-- partial sums of the sign series -/
def Sn (b : ℕ → ℝ) (N : ℕ) (ε : ℕ → Bool) : ℝ := ∑ k ∈ Finset.range N, sign (ε k) * b k

lemma measurable_sign : Measurable sign := measurable_of_finite _

lemma measurable_Sn (b : ℕ → ℝ) (N : ℕ) : Measurable (Sn b N) := by
  unfold Sn
  exact Finset.measurable_sum _ fun k _ =>
    ((measurable_sign.comp (measurable_pi_apply k)).mul_const (b k))

lemma integral_restrict (s : Finset ℕ) (g : (s → Bool) → ℝ) :
    ∫ ε, g (s.restrict ε) ∂(signLaw ℕ) = avg g := by
  unfold signLaw
  rw [← integral_map (Finset.measurable_restrict s).aemeasurable (measurable_of_finite g).aestronglyMeasurable,
    Measure.infinitePi_map_restrict, integral_fintype (Integrable.of_finite)]
  unfold avg
  have h1 : ∀ x : s → Bool, (Measure.pi fun _ : s => (PMF.uniformOfFintype Bool).toMeasure).real {x}
      = (Fintype.card (s → Bool) : ℝ)⁻¹ := by
    intro x
    rw [Measure.real, Measure.pi_singleton]
    simp [PMF.toMeasure_apply_singleton, PMF.uniformOfFintype_apply, ENNReal.toReal_prod,
      Fintype.card_fun]
  simp_rw [h1, smul_eq_mul]
  rw [← Finset.mul_sum, div_eq_inv_mul]

lemma Sn_eq (b : ℕ → ℝ) (N : ℕ) (ε : ℕ → Bool) :
    Sn b N ε = rsum (fun i : (Finset.range N) => b i) ((Finset.range N).restrict ε) := by
  unfold Sn rsum
  exact (Finset.sum_coe_sort (Finset.range N) (fun i => sign (ε i) * b i)).symm

lemma integral_Sn_sq (b : ℕ → ℝ) (N : ℕ) :
    ∫ ε, (Sn b N ε) ^ 2 ∂(signLaw ℕ) = ∑ k ∈ Finset.range N, b k ^ 2 := by
  have : ∀ ε, (Sn b N ε) ^ 2 = (fun η => rsum (fun i : (Finset.range N) => b i) η *
      rsum (fun i : (Finset.range N) => b i) η) ((Finset.range N).restrict ε) := by
    intro ε; simp only [Sn_eq, sq]
  simp_rw [this]
  refine (integral_restrict (Finset.range N) (fun η => rsum (fun i : (Finset.range N) => b i) η *
      rsum (fun i : (Finset.range N) => b i) η)).trans ?_
  rw [avg_rsum_sq]
  exact Finset.sum_coe_sort (Finset.range N) (fun i => b i ^ 2)

lemma integral_abs_Sn (b : ℕ → ℝ) (N : ℕ) :
    ∫ ε, |Sn b N ε| ∂(signLaw ℕ) = avg (fun η => |rsum (fun i : (Finset.range N) => b i) η|) := by
  simp_rw [Sn_eq]
  exact integral_restrict (Finset.range N) (fun η => |rsum (fun i : (Finset.range N) => b i) η|)

lemma szarek_Sn (b : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, b k ^ 2 ≤ 2 * (∫ ε, |Sn b N ε| ∂(signLaw ℕ)) ^ 2 := by
  rw [integral_abs_Sn, ← Finset.sum_coe_sort (Finset.range N) (fun i => b i ^ 2)]
  exact szarek_finite (fun i : (Finset.range N) => b i)

/-- the `k`-th sign coordinate -/
def Xp (k : ℕ) (ε : ℕ → Bool) : ℝ := sign (ε k)

lemma measurable_Xp (k : ℕ) : Measurable (Xp k) := measurable_sign.comp (measurable_pi_apply k)

lemma hX (k : ℕ) : StronglyMeasurable (Xp k) := (measurable_Xp k).stronglyMeasurable

lemma iIndep_Xp : iIndepFun Xp (signLaw ℕ) := by
  unfold signLaw
  exact iIndepFun_infinitePi (P := fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)
    (X := fun _ => sign) (fun _ => measurable_sign)

lemma integral_Xp (k : ℕ) : ∫ ε, Xp k ε ∂(signLaw ℕ) = 0 := by
  have h : ∫ ε, Xp k ε ∂(signLaw ℕ)
      = avg (fun η : ({k} : Finset ℕ) → Bool => sign (η ⟨k, Finset.mem_singleton_self k⟩)) :=
    integral_restrict {k} (fun η : ({k} : Finset ℕ) → Bool => sign (η ⟨k, Finset.mem_singleton_self k⟩))
  rw [h]
  unfold avg
  rw [sum_eq_zero_of_flip ⟨k, Finset.mem_singleton_self k⟩]
  · simp
  · intro η
    simp [flipAt, sign_not]

lemma bound_Sn (b : ℕ → ℝ) (N : ℕ) (ε : ℕ → Bool) : ‖Sn b N ε‖ ≤ ∑ k ∈ Finset.range N, |b k| := by
  unfold Sn
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  have : ‖sign (ε k)‖ = 1 := by cases ε k <;> simp [sign]
  rw [this, one_mul]; exact le_of_eq (Real.norm_eq_abs _)

lemma integrable_Sn (b : ℕ → ℝ) (N : ℕ) : Integrable (Sn b N) (signLaw ℕ) :=
  Integrable.of_bound (measurable_Sn b N).aestronglyMeasurable _
    (Filter.Eventually.of_forall (bound_Sn b N))

lemma martingale_Sn (b : ℕ → ℝ) :
    Martingale (fun N => Sn b (N + 1)) (Filtration.natural Xp hX) (signLaw ℕ) := by
  have hadp : StronglyAdapted (Filtration.natural Xp hX) (fun N => Sn b (N + 1)) := by
    intro N
    have : Sn b (N + 1) = ∑ k ∈ Finset.range (N + 1), fun ε => b k * Xp k ε := by
      funext ε; simp [Sn, Xp, mul_comm]
    show StronglyMeasurable[(Filtration.natural Xp hX) N] (Sn b (N + 1))
    rw [this]
    refine Finset.stronglyMeasurable_sum _ fun k hk => ?_
    have hk' : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact (((Filtration.stronglyAdapted_natural hX k).mono
      ((Filtration.natural Xp hX).mono hk')).const_smul (b k))
  refine martingale_nat hadp (fun N => integrable_Sn b _) fun i => ?_
  have hdec : Sn b (i + 1 + 1) = fun ε => Sn b (i + 1) ε + b (i + 1) * Xp (i + 1) ε := by
    funext ε; simp only [Sn, Xp, Finset.sum_range_succ _ (i + 1)]; ring
  rw [hdec]
  have hint2 : Integrable (fun ε => b (i + 1) * Xp (i + 1) ε) (signLaw ℕ) :=
    ((integrable_Sn b (i + 2)).sub (integrable_Sn b (i + 1))).congr
      (Filter.Eventually.of_forall fun ε => by
        simp only [Pi.sub_apply, Sn, Xp, Finset.sum_range_succ _ (i + 1)]; ring)
  have h1 := condExp_add (integrable_Sn b (i + 1)) hint2 ((Filtration.natural Xp hX) i)
  have h2 : (signLaw ℕ)[Sn b (i + 1) | (Filtration.natural Xp hX) i] = Sn b (i + 1) :=
    condExp_of_stronglyMeasurable ((Filtration.natural Xp hX).le i) (hadp i) (integrable_Sn b _)
  have hind : Indep (MeasurableSpace.comap (Xp (i + 1)) inferInstance)
      ((Filtration.natural Xp hX) i) (signLaw ℕ) := by
    have h := indep_iSup_of_disjoint (m := fun k => MeasurableSpace.comap (Xp k) inferInstance)
      (fun k => (measurable_Xp k).comap_le) ((iIndepFun_iff_iIndep _ _ _).mp iIndep_Xp)
      (S := {i + 1}) (T := Set.Iic i) (by simp)
    simpa [Filtration.natural] using h
  have h3 := condExp_indep_eq (μ := signLaw ℕ) (measurable_Xp (i + 1)).comap_le
    ((Filtration.natural Xp hX).le i) (comap_measurable (Xp (i + 1))).stronglyMeasurable hind
  have h4 := condExp_smul (b (i + 1)) (Xp (i + 1)) ((Filtration.natural Xp hX) i) (μ := signLaw ℕ)
  filter_upwards [h1, h3, h4] with ε e1 e3 e4
  have e5 : (signLaw ℕ)[fun ε => b (i + 1) * Xp (i + 1) ε | (Filtration.natural Xp hX) i] ε = 0 := by
    have : (signLaw ℕ)[fun ε => b (i + 1) * Xp (i + 1) ε | (Filtration.natural Xp hX) i] ε
        = b (i + 1) * (signLaw ℕ)[Xp (i + 1) | (Filtration.natural Xp hX) i] ε := e4
    rw [this, e3, integral_Xp]; simp
  have e6 : (signLaw ℕ)[fun ε => Sn b (i + 1) ε + b (i + 1) * Xp (i + 1) ε | (Filtration.natural Xp hX) i] ε
      = Sn b (i + 1) ε := by
    have e1' : (signLaw ℕ)[fun ε => Sn b (i + 1) ε + b (i + 1) * Xp (i + 1) ε | (Filtration.natural Xp hX) i] ε
        = ((signLaw ℕ)[Sn b (i + 1) | (Filtration.natural Xp hX) i] +
        (signLaw ℕ)[fun ε => b (i + 1) * Xp (i + 1) ε | (Filtration.natural Xp hX) i]) ε := e1
    rw [e1']
    simp only [Pi.add_apply, h2, e5, add_zero]
  exact e6.symm

/-- coefficients as a function -/
abbrev co (a : SequenceL2) : ℕ → ℝ := fun k => a k

lemma a_sq_summable (a : SequenceL2) : Summable (fun k => (a k) ^ 2) := by
  have := (lp.memℓp a).summable (by simp)
  simpa [Real.norm_eq_abs, Real.rpow_two, sq_abs] using this

lemma norm_sq_eq_tsum (a : SequenceL2) : ‖a‖ ^ 2 = ∑' k, (a k) ^ 2 := by
  have := lp.norm_rpow_eq_tsum (p := 2) (by simp) a
  simpa [Real.norm_eq_abs, Real.rpow_two, sq_abs] using this

lemma sum_sq_le (a : SequenceL2) (N : ℕ) : ∑ k ∈ Finset.range N, (a k) ^ 2 ≤ ‖a‖ ^ 2 := by
  rw [norm_sq_eq_tsum]
  exact (a_sq_summable a).sum_le_tsum _ (fun k _ => sq_nonneg _)

lemma integral_abs_Sn_le (a : SequenceL2) (N : ℕ) :
    ∫ ε, |Sn (co a) N ε| ∂(signLaw ℕ) ≤ (1 + ‖a‖ ^ 2) / 2 := by
  have hi : Integrable (fun ε => |Sn (co a) N ε|) (signLaw ℕ) := (integrable_Sn _ N).abs
  have hi2 : Integrable (fun ε => (Sn (co a) N ε) ^ 2) (signLaw ℕ) :=
    Integrable.of_bound ((measurable_Sn _ N).pow_const 2).aestronglyMeasurable
      ((∑ k ∈ Finset.range N, |co a k|) ^ 2)
      (Filter.Eventually.of_forall fun ε => by
        rw [Real.norm_eq_abs, abs_pow]
        have := bound_Sn (co a) N ε
        rw [Real.norm_eq_abs] at this
        exact pow_le_pow_left₀ (abs_nonneg _) this 2)
  calc ∫ ε, |Sn (co a) N ε| ∂(signLaw ℕ)
      ≤ ∫ ε, ((1 + (Sn (co a) N ε) ^ 2) / 2) ∂(signLaw ℕ) := by
        refine integral_mono hi ((integrable_const _).add hi2 |>.div_const 2) fun ε => ?_
        simp only [Pi.add_apply]
        nlinarith [sq_nonneg (|Sn (co a) N ε| - 1), sq_abs (Sn (co a) N ε)]
    _ = (1 + ∑ k ∈ Finset.range N, (a k) ^ 2) / 2 := by
        rw [integral_div, integral_add (integrable_const _) hi2, integral_Sn_sq]
        simp
    _ ≤ _ := by
        have := sum_sq_le a N
        linarith

lemma ae_exists_tendsto (a : SequenceL2) :
    ∀ᵐ ε ∂(signLaw ℕ), ∃ c, Tendsto (fun N => Sn (co a) N ε) atTop (𝓝 c) := by
  have hm := martingale_Sn (co a)
  have hbdd : ∀ N, eLpNorm (Sn (co a) (N + 1)) 1 (signLaw ℕ) ≤
      ((((1 + ‖a‖ ^ 2) / 2).toNNReal : NNReal) : ℝ≥0∞) := by
    intro N
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (integrable_Sn _ _)]
    simp_rw [Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (integral_abs_Sn_le a (N + 1))
  filter_upwards [hm.submartingale.exists_ae_tendsto_of_bdd hbdd] with ε hε
  obtain ⟨c, hc⟩ := hε
  exact ⟨c, (Filter.tendsto_add_atTop_iff_nat 1).mp hc⟩

lemma signSeries_eq_of_tendsto (a : SequenceL2) (ε : ℕ → Bool) (l : ℝ)
    (h : Tendsto (fun N => Sn (co a) N ε) atTop (𝓝 l)) : signSeries a ε = l := by
  have hex : ∃ l : ℝ, Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, sign (ε k) * a k) atTop (𝓝 l) :=
    ⟨l, h⟩
  unfold signSeries
  rw [dif_pos hex]
  exact tendsto_nhds_unique (Classical.choose_spec hex) h

lemma signSeries_ae_tendsto (a : SequenceL2) :
    ∀ᵐ ε ∂(signLaw ℕ), Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, sign (ε k) * a k)
      Filter.atTop (nhds (signSeries a ε)) := by
  filter_upwards [ae_exists_tendsto a] with ε hε
  obtain ⟨c, hc⟩ := hε
  rw [signSeries_eq_of_tendsto a ε c hc]
  exact hc

lemma signSeries_measurable (a : SequenceL2) : Measurable (signSeries a) := by
  classical
  have hmeas : ∀ N, StronglyMeasurable (fun ε => Sn (co a) N ε) :=
    fun N => (measurable_Sn _ N).stronglyMeasurable
  have h1 : MeasurableSet {ε : ℕ → Bool | ∃ c, Tendsto (fun N => Sn (co a) N ε) atTop (𝓝 c)} :=
    StronglyMeasurable.measurableSet_exists_tendsto hmeas
  have h2 : signSeries a = fun ε => if ∃ c, Tendsto (fun N => Sn (co a) N ε) atTop (𝓝 c)
      then limUnder atTop (fun N => Sn (co a) N ε) else 0 := by
    funext ε
    by_cases h : ∃ c, Tendsto (fun N => Sn (co a) N ε) atTop (𝓝 c)
    · rw [if_pos h]
      obtain ⟨c, hc⟩ := h
      rw [signSeries_eq_of_tendsto a ε c hc, hc.limUnder_eq]
    · rw [if_neg h]
      unfold signSeries
      exact dif_neg h
  rw [h2]
  exact Measurable.ite h1 (StronglyMeasurable.limUnder hmeas).measurable measurable_const

lemma signSeries_sub (a b : SequenceL2) :
    signSeries (a - b) =ᵐ[signLaw ℕ] fun ε => signSeries a ε - signSeries b ε := by
  filter_upwards [ae_exists_tendsto a, ae_exists_tendsto b, ae_exists_tendsto (a - b)]
    with ε ha hb hab
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := hb
  have h : Tendsto (fun N => Sn (co (a - b)) N ε) atTop (𝓝 (c - d)) := by
    have := hc.sub hd
    refine this.congr fun N => ?_
    simp only [Sn, co, lp.coeFn_sub, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [signSeries_eq_of_tendsto _ ε _ h, signSeries_eq_of_tendsto _ ε _ hc,
    signSeries_eq_of_tendsto _ ε _ hd]

lemma rho_eq {f : (ℕ → Bool) → ℝ} (hf : MemLp f 2 (signLaw ℕ)) :
    (eLpNorm f 2 (signLaw ℕ)).toReal = Real.sqrt (∫ ε, f ε ^ 2 ∂(signLaw ℕ)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun ε => by positivity) _)]
  simp [Real.sqrt_eq_rpow, Real.rpow_two]

lemma memLp_Sn (b : ℕ → ℝ) (N : ℕ) : MemLp (Sn b N) 2 (signLaw ℕ) :=
  MemLp.of_bound (measurable_Sn b N).aestronglyMeasurable _
    (Filter.Eventually.of_forall (bound_Sn b N))

lemma rho_Sn (b : ℕ → ℝ) (N : ℕ) :
    (eLpNorm (Sn b N) 2 (signLaw ℕ)).toReal = Real.sqrt (∑ k ∈ Finset.range N, b k ^ 2) := by
  rw [rho_eq (memLp_Sn b N), integral_Sn_sq]

lemma Sn_diff (b : ℕ → ℝ) (N M : ℕ) (h : N ≤ M) (ε : ℕ → Bool) :
    Sn b M ε - Sn b N ε = Sn (fun k => if N ≤ k then b k else 0) M ε := by
  unfold Sn
  rw [← Finset.sum_range_add_sum_Ico _ h, ← Finset.sum_range_add_sum_Ico _ h]
  have h1 : ∑ k ∈ Finset.range N, sign (ε k) * (if N ≤ k then b k else 0) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have : ¬ N ≤ k := by have := Finset.mem_range.mp hk; omega
    simp [this]
  have h2 : ∑ k ∈ Finset.Ico N M, sign (ε k) * (if N ≤ k then b k else 0)
      = ∑ k ∈ Finset.Ico N M, sign (ε k) * b k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have : N ≤ k := (Finset.mem_Ico.mp hk).1
    simp [this]
  rw [h1, h2]; ring

lemma sum_sq_tail (b : ℕ → ℝ) (N M : ℕ) (h : N ≤ M) :
    ∑ k ∈ Finset.range M, (if N ≤ k then b k else 0) ^ 2
      = ∑ k ∈ Finset.range M, b k ^ 2 - ∑ k ∈ Finset.range N, b k ^ 2 := by
  rw [← Finset.sum_range_add_sum_Ico _ h, ← Finset.sum_range_add_sum_Ico (fun k => b k ^ 2) h]
  have h1 : ∑ k ∈ Finset.range N, (if N ≤ k then b k else 0) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have : ¬ N ≤ k := by have := Finset.mem_range.mp hk; omega
    simp [this]
  have h2 : ∑ k ∈ Finset.Ico N M, (if N ≤ k then b k else 0) ^ 2 = ∑ k ∈ Finset.Ico N M, b k ^ 2 := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have : N ≤ k := (Finset.mem_Ico.mp hk).1
    simp [this]
  rw [h1, h2]; ring

lemma tail_le (a : SequenceL2) (N : ℕ) :
    eLpNorm (fun ε => signSeries a ε - Sn (co a) N ε) 2 (signLaw ℕ)
      ≤ ENNReal.ofReal (Real.sqrt (‖a‖ ^ 2 - ∑ k ∈ Finset.range N, (a k) ^ 2)) := by
  have hlim : ∀ᵐ ε ∂(signLaw ℕ), Tendsto (fun M => Sn (co a) M ε - Sn (co a) N ε) atTop
      (𝓝 (signSeries a ε - Sn (co a) N ε)) := by
    filter_upwards [signSeries_ae_tendsto a] with ε h
    exact h.sub_const _
  have hF := MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2) (μ := signLaw ℕ)
    (f := fun M ε => Sn (co a) M ε - Sn (co a) N ε)
    (fun M => ((measurable_Sn _ M).sub (measurable_Sn _ N)).aestronglyMeasurable)
    (fun ε => signSeries a ε - Sn (co a) N ε) hlim
  refine hF.trans ?_
  refine (Filter.liminf_le_liminf (v := fun _ => ENNReal.ofReal (Real.sqrt (‖a‖ ^ 2 -
    ∑ k ∈ Finset.range N, (a k) ^ 2))) ?_).trans_eq (Filter.liminf_const _)
  filter_upwards [Filter.eventually_ge_atTop N] with M hM
  have h1 : (fun ε => Sn (co a) M ε - Sn (co a) N ε)
      = Sn (fun k => if N ≤ k then co a k else 0) M := funext (Sn_diff (co a) N M hM)
  rw [h1]
  rw [← ENNReal.ofReal_toReal (memLp_Sn _ M).eLpNorm_ne_top, rho_Sn, sum_sq_tail _ N M hM]
  refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
  have := sum_sq_le a M
  simp only [co]
  linarith

lemma memLp_tail (a : SequenceL2) (N : ℕ) :
    MemLp (fun ε => signSeries a ε - Sn (co a) N ε) 2 (signLaw ℕ) :=
  ⟨((signSeries_measurable a).sub (measurable_Sn _ N)).aestronglyMeasurable,
    lt_of_le_of_lt (tail_le a N) ENNReal.ofReal_lt_top⟩

lemma memLp_signSeries_two (a : SequenceL2) : MemLp (signSeries a) 2 (signLaw ℕ) := by
  have h := (memLp_tail a 0).add (memLp_Sn (co a) 0)
  have e : signSeries a = (fun ε => signSeries a ε - Sn (co a) 0 ε) + Sn (co a) 0 := by
    funext ε; simp
  rw [e]; exact h

/-- the `L²` seminorm as a real number -/
def rho (f : (ℕ → Bool) → ℝ) : ℝ := (eLpNorm f 2 (signLaw ℕ)).toReal

lemma rho_le_add {f g : (ℕ → Bool) → ℝ} (hf : MemLp f 2 (signLaw ℕ)) (hg : MemLp g 2 (signLaw ℕ)) :
    rho f ≤ rho (fun ε => f ε - g ε) + rho g := by
  have hfg : MemLp (fun ε => f ε - g ε) 2 (signLaw ℕ) := hf.sub hg
  have h := eLpNorm_add_le (p := 2) (μ := signLaw ℕ) hfg.1 hg.1 (by norm_num)
  have e : ((fun ε => f ε - g ε) + g) = f := by funext ε; simp
  rw [e] at h
  unfold rho
  rw [← ENNReal.toReal_add hfg.eLpNorm_ne_top hg.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfg.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩) h

lemma rho_swap (f g : (ℕ → Bool) → ℝ) : rho (fun ε => g ε - f ε) = rho (fun ε => f ε - g ε) := by
  unfold rho
  have : (fun ε => g ε - f ε) = -(fun ε => f ε - g ε) := by funext ε; simp
  rw [this, eLpNorm_neg]

lemma rho_tail_le (a : SequenceL2) (N : ℕ) :
    rho (fun ε => signSeries a ε - Sn (co a) N ε)
      ≤ Real.sqrt (‖a‖ ^ 2 - ∑ k ∈ Finset.range N, (a k) ^ 2) :=
  ENNReal.toReal_le_of_le_ofReal (Real.sqrt_nonneg _) (tail_le a N)

lemma sigma_tendsto (a : SequenceL2) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, (a k) ^ 2) atTop (𝓝 (‖a‖ ^ 2)) := by
  rw [norm_sq_eq_tsum]
  exact (a_sq_summable a).hasSum.tendsto_sum_nat

lemma r_tendsto (a : SequenceL2) :
    Tendsto (fun N => Real.sqrt (‖a‖ ^ 2 - ∑ k ∈ Finset.range N, (a k) ^ 2)) atTop (𝓝 0) := by
  have h : Tendsto (fun N => ‖a‖ ^ 2 - ∑ k ∈ Finset.range N, (a k) ^ 2) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := ‖a‖ ^ 2)).sub (sigma_tendsto a)
    rwa [sub_self] at this
  have := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at this
  exact this

lemma sqrt_sigma_tendsto (a : SequenceL2) :
    Tendsto (fun N => Real.sqrt (∑ k ∈ Finset.range N, (a k) ^ 2)) atTop (𝓝 ‖a‖) := by
  have := (Real.continuous_sqrt.tendsto _).comp (sigma_tendsto a)
  rw [Real.sqrt_sq (norm_nonneg a)] at this
  exact this

lemma rho_signSeries (a : SequenceL2) : rho (signSeries a) = ‖a‖ := by
  have hT := memLp_signSeries_two a
  have h1 : Tendsto (fun N => rho (Sn (co a) N)) atTop (𝓝 ‖a‖) := by
    simpa [rho, rho_Sn] using sqrt_sigma_tendsto a
  have h2 : Tendsto (fun N => rho (Sn (co a) N)) atTop (𝓝 (rho (signSeries a))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun N => dist_nonneg) (fun N => ?_) (r_tendsto a)
    rw [Real.dist_eq, abs_le]
    have hS := memLp_Sn (co a) N
    have t := rho_tail_le a N
    have u1 := rho_le_add hT hS
    have u2 := rho_le_add hS hT
    rw [rho_swap] at u2
    constructor <;> linarith
  exact tendsto_nhds_unique h2 h1

lemma integral_abs_le_rho {f : (ℕ → Bool) → ℝ} (hf : MemLp f 2 (signLaw ℕ)) :
    ∫ ε, |f ε| ∂(signLaw ℕ) ≤ rho f := by
  have h1 := eLpNorm_le_eLpNorm_of_exponent_le (μ := signLaw ℕ) (p := 1) (q := 2)
    (by norm_num) hf.1
  have hi : Integrable f (signLaw ℕ) := hf.integrable (by norm_num)
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hi] at h1
  simp_rw [Real.norm_eq_abs] at h1
  exact (ENNReal.ofReal_le_iff_le_toReal hf.eLpNorm_ne_top).mp h1

lemma signSeries_memLp (a : SequenceL2) :
    MemLp (signSeries a) 2 (signLaw ℕ) ∧ ∫ ε, (signSeries a ε)^2 ∂(signLaw ℕ) = ‖a‖^2 := by
  refine ⟨memLp_signSeries_two a, ?_⟩
  have h := rho_signSeries a
  unfold rho at h
  rw [rho_eq (memLp_signSeries_two a)] at h
  have hnn : 0 ≤ ∫ ε, (signSeries a ε)^2 ∂(signLaw ℕ) := integral_nonneg fun ε => sq_nonneg _
  have := Real.sq_sqrt hnn
  rw [h] at this
  exact this.symm

lemma szarek_N (a : SequenceL2) (N : ℕ) :
    Real.sqrt (∑ k ∈ Finset.range N, (a k) ^ 2) ≤
      Real.sqrt 2 * (∫ ε, |signSeries a ε| ∂(signLaw ℕ) +
        Real.sqrt (‖a‖ ^ 2 - ∑ k ∈ Finset.range N, (a k) ^ 2)) := by
  have hT := (memLp_signSeries_two a)
  have hD := memLp_tail a N
  have hTi : Integrable (fun ε => |signSeries a ε|) (signLaw ℕ) :=
    (hT.integrable (by norm_num)).abs
  have hDi : Integrable (fun ε => |signSeries a ε - Sn (co a) N ε|) (signLaw ℕ) :=
    (hD.integrable (by norm_num)).abs
  have hm : ∫ ε, |Sn (co a) N ε| ∂(signLaw ℕ) ≤
      ∫ ε, |signSeries a ε| ∂(signLaw ℕ) + ∫ ε, |signSeries a ε - Sn (co a) N ε| ∂(signLaw ℕ) := by
    rw [← integral_add hTi hDi]
    refine integral_mono (integrable_Sn _ N).abs (hTi.add hDi) fun ε => ?_
    simp only [Pi.add_apply]
    have := abs_sub_abs_le_abs_sub (Sn (co a) N ε) (signSeries a ε)
    rw [abs_sub_comm] at this
    linarith
  have hr := (integral_abs_le_rho hD).trans (rho_tail_le a N)
  have hm0 : 0 ≤ ∫ ε, |Sn (co a) N ε| ∂(signLaw ℕ) := integral_nonneg fun ε => abs_nonneg _
  have hs := szarek_Sn (co a) N
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hm' : ∫ ε, |Sn (co a) N ε| ∂(signLaw ℕ) ≤
      ∫ ε, |signSeries a ε| ∂(signLaw ℕ) + Real.sqrt (‖a‖ ^ 2 - ∑ k ∈ Finset.range N, (a k) ^ 2) :=
    hm.trans (by linarith)
  calc ∑ k ∈ Finset.range N, (a k) ^ 2 ≤ 2 * (∫ ε, |Sn (co a) N ε| ∂(signLaw ℕ)) ^ 2 := hs
    _ ≤ 2 * (∫ ε, |signSeries a ε| ∂(signLaw ℕ) +
        Real.sqrt (‖a‖ ^ 2 - ∑ k ∈ Finset.range N, (a k) ^ 2)) ^ 2 := by
        gcongr
    _ = (Real.sqrt 2 * (∫ ε, |signSeries a ε| ∂(signLaw ℕ) +
        Real.sqrt (‖a‖ ^ 2 - ∑ k ∈ Finset.range N, (a k) ^ 2))) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]

lemma szarek (a : SequenceL2) : ‖a‖ ≤ Real.sqrt 2 * ∫ ε, |signSeries a ε| ∂(signLaw ℕ) := by
  have h1 := sqrt_sigma_tendsto a
  have h2 : Tendsto (fun N => Real.sqrt 2 * (∫ ε, |signSeries a ε| ∂(signLaw ℕ) +
      Real.sqrt (‖a‖ ^ 2 - ∑ k ∈ Finset.range N, (a k) ^ 2))) atTop
      (𝓝 (Real.sqrt 2 * (∫ ε, |signSeries a ε| ∂(signLaw ℕ) + 0))) :=
    (tendsto_const_nhds.add (r_tendsto a)).const_mul _
  rw [add_zero] at h2
  exact le_of_tendsto_of_tendsto' h1 h2 (szarek_N a)

end HindsightGain.Uniform.Dev.Khin
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace HindsightGain.Uniform.Dev.Mau
open HindsightGain.Uniform HindsightGain.Uniform.Dev.Khin

/-- the fair coin on `Bool` -/
abbrev coin : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure coin := by unfold coin; infer_instance

instance (J : Type) [Countable J] : IsProbabilityMeasure (signLaw J) := by
  unfold signLaw; infer_instance

lemma coin_singleton (b : Bool) : coin {b} = 1 / 2 := by
  unfold coin
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b)]
  simp [PMF.uniformOfFintype_apply]

lemma coin_not : coin.map (fun b : Bool => !b) = coin := by
  rw [Measure.ext_iff_singleton]
  intro b
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton b)]
  have : (fun b : Bool => !b) ⁻¹' {b} = {!b} := by
    ext x; cases x <;> cases b <;> simp
  rw [this, coin_singleton, coin_singleton]

lemma integral_coin (f : Bool → ℝ) : ∫ b, f b ∂coin = (f true + f false) / 2 := by
  rw [integral_fintype Integrable.of_finite]
  simp only [Fintype.sum_bool, measureReal_def, coin_singleton, smul_eq_mul]
  simp
  ring

lemma sign_not (b : Bool) : sign (!b) = - sign b := by
  cases b <;> simp [sign]

lemma mau_measurable_sign : Measurable sign := measurable_from_top

lemma signSeries_flip (a : SequenceL2) (ε : ℕ → Bool) :
    signSeries a (fun k => !ε k) = - signSeries a ε := by
  have hps : ∀ N, ∑ k ∈ Finset.range N, sign (!ε k) * a k
      = - ∑ k ∈ Finset.range N, sign (ε k) * a k := by
    intro N
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sign_not]; ring
  classical
  by_cases h : ∃ l : ℝ, Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, sign (ε k) * a k) atTop (𝓝 l)
  · have h2 : ∃ l : ℝ, Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, sign (!ε k) * a k) atTop (𝓝 l) := by
      obtain ⟨l, hl⟩ := h
      exact ⟨-l, by simpa [hps] using hl.neg⟩
    unfold signSeries
    rw [dif_pos h, dif_pos h2]
    have s1 := Classical.choose_spec h
    have s2 := Classical.choose_spec h2
    have s2' : Tendsto (fun N : ℕ => -∑ k ∈ Finset.range N, sign (ε k) * a k) atTop
        (𝓝 (Classical.choose h2)) := by simpa only [hps] using s2
    have := tendsto_nhds_unique s1.neg s2'
    exact this.symm
  · have h2 : ¬ ∃ l : ℝ, Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, sign (!ε k) * a k) atTop (𝓝 l) := by
      rintro ⟨l, hl⟩
      apply h
      refine ⟨-l, ?_⟩
      have : Tendsto (fun N : ℕ => -∑ k ∈ Finset.range N, sign (!ε k) * a k) atTop (𝓝 (-l)) := hl.neg
      simpa [hps] using this
    unfold signSeries
    rw [dif_neg h, dif_neg h2]; simp

lemma flip_measurePreserving :
    MeasurePreserving (fun (ε : ℕ → Bool) k => !ε k) (signLaw ℕ) (signLaw ℕ) := by
  refine ⟨by fun_prop, ?_⟩
  unfold signLaw
  have := Measure.infinitePi_map_pi (μ := fun _ : ℕ => coin) (f := fun _ b => !b) (by fun_prop)
  simpa [coin_not] using this


lemma measurable_sup'_pt {Ω T : Type} [MeasurableSpace Ω] (F : Finset T)
    (hF : F.Nonempty) (f : T → Ω → ℝ) (hm : ∀ t ∈ F, Measurable (f t)) :
    Measurable (fun w => F.sup' hF (fun t => f t w)) := by
  have := Finset.measurable_sup' hF hm
  convert this using 1
  ext w; simp [Finset.sup'_apply]

lemma integrable_sup' {Ω T : Type} [MeasurableSpace Ω] {μ : Measure Ω} (F : Finset T)
    (hF : F.Nonempty) (f : T → Ω → ℝ) (hm : ∀ t ∈ F, Measurable (f t))
    (hi : ∀ t ∈ F, Integrable (f t) μ) :
    Integrable (fun w => F.sup' hF (fun t => f t w)) μ := by
  refine Integrable.mono' (g := fun w => ∑ t ∈ F, ‖f t w‖)
    (integrable_finsetSum _ fun t ht => (hi t ht).norm)
    (measurable_sup'_pt F hF f hm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  obtain ⟨t0, ht0, e⟩ := Finset.exists_mem_eq_sup' hF (fun t => f t w)
  rw [e]
  exact Finset.single_le_sum (f := fun t => ‖f t w‖) (fun _ _ => norm_nonneg _) ht0

lemma signSeries_integrable (a : SequenceL2) : Integrable (signSeries a) (signLaw ℕ) :=
  (signSeries_memLp a).1.integrable (by norm_num)

/-- One coordinate of Maurer's contraction, for a finite index set. -/
lemma step_one {T : Type} (F : Finset T) (hF : F.Nonempty) (g ψ : T → ℝ) (a : T → SequenceL2)
    (h : ∀ t t', ψ t - ψ t' ≤ ‖a t - a t'‖) :
    (F.sup' hF (fun t => g t + ψ t) + F.sup' hF (fun t => g t - ψ t)) / 2 ≤
      ∫ w, F.sup' hF (fun t => g t + Real.sqrt 2 * signSeries (a t) w) ∂(signLaw ℕ) := by
  set ν := signLaw ℕ with hν
  set r := Real.sqrt 2 with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  set A : (ℕ → Bool) → ℝ := fun w => F.sup' hF (fun t => g t + r * signSeries (a t) w) with hA
  have hAi : Integrable A ν := by
    refine integrable_sup' F hF (fun t w => g t + r * signSeries (a t) w) (fun t _ => ?_) (fun t _ => ?_)
    · exact measurable_const.add (measurable_const.mul (signSeries_measurable _))
    · exact (integrable_const _).add ((signSeries_integrable _).const_mul r)
  have hB : ∀ w, F.sup' hF (fun t => g t - r * signSeries (a t) w) = A (fun k => !w k) := by
    intro w
    simp only [hA, signSeries_flip]
    congr 1; ext t; ring
  have hflip : ∫ w, A (fun k => !w k) ∂ν = ∫ w, A w ∂ν := by
    have hAm : Measurable A :=
      measurable_sup'_pt F hF _ (fun t _ => measurable_const.add
        (measurable_const.mul (signSeries_measurable _)))
    have := integral_map (μ := ν) (φ := fun (ε : ℕ → Bool) k => !ε k)
      flip_measurePreserving.aemeasurable (f := A) hAm.aestronglyMeasurable
    rw [flip_measurePreserving.map_eq] at this
    exact this.symm
  obtain ⟨t1, ht1, e1⟩ := Finset.exists_mem_eq_sup' hF (fun t => g t + ψ t)
  obtain ⟨t2, ht2, e2⟩ := Finset.exists_mem_eq_sup' hF (fun t => g t - ψ t)
  have hX1 := signSeries_integrable (a t1)
  have hX2 := signSeries_integrable (a t2)
  have hD : Integrable (fun w => |signSeries (a t1) w - signSeries (a t2) w|) ν :=
    (hX1.sub hX2).abs
  have hsz : ‖a t1 - a t2‖ ≤ r * ∫ w, |signSeries (a t1) w - signSeries (a t2) w| ∂ν := by
    have h1 := szarek (a t1 - a t2)
    have h2 : ∫ w, |signSeries (a t1 - a t2) w| ∂ν
        = ∫ w, |signSeries (a t1) w - signSeries (a t2) w| ∂ν :=
      integral_congr_ae ((signSeries_sub (a t1) (a t2)).mono fun w hw => by simp [hw])
    rw [h2] at h1; exact h1
  have hpt : ∀ w, g t1 + g t2 + r * |signSeries (a t1) w - signSeries (a t2) w|
      ≤ A w + A (fun k => !w k) := by
    intro w
    rw [← hB w]
    have l1 : g t1 + r * signSeries (a t1) w ≤ A w :=
      Finset.le_sup' (fun t => g t + r * signSeries (a t) w) ht1
    have l2 : g t2 + r * signSeries (a t2) w ≤ A w :=
      Finset.le_sup' (fun t => g t + r * signSeries (a t) w) ht2
    have m1 : g t1 - r * signSeries (a t1) w ≤ F.sup' hF (fun t => g t - r * signSeries (a t) w) :=
      Finset.le_sup' (fun t => g t - r * signSeries (a t) w) ht1
    have m2 : g t2 - r * signSeries (a t2) w ≤ F.sup' hF (fun t => g t - r * signSeries (a t) w) :=
      Finset.le_sup' (fun t => g t - r * signSeries (a t) w) ht2
    rcases le_total (signSeries (a t2) w) (signSeries (a t1) w) with hle | hle
    · rw [abs_of_nonneg (by linarith)]; nlinarith
    · rw [abs_of_nonpos (by linarith)]; nlinarith
  have hint : g t1 + g t2 + r * ∫ w, |signSeries (a t1) w - signSeries (a t2) w| ∂ν
      ≤ ∫ w, A w ∂ν + ∫ w, A (fun k => !w k) ∂ν := by
    have hAflip : Integrable (fun w => A (fun k => !w k)) ν := by
      have := flip_measurePreserving.integrable_comp_of_integrable hAi
      exact this
    rw [← integral_add hAi hAflip]
    have : ∫ w, (g t1 + g t2 + r * |signSeries (a t1) w - signSeries (a t2) w|) ∂ν
        = g t1 + g t2 + r * ∫ w, |signSeries (a t1) w - signSeries (a t2) w| ∂ν := by
      rw [integral_add (integrable_const _) (hD.const_mul r), integral_const_mul]
      simp
    rw [← this]
    exact integral_mono ((integrable_const _).add (hD.const_mul r)) (hAi.add hAflip) hpt
  have := h t1 t2
  rw [e1, e2]
  rw [hflip] at hint
  linarith

end HindsightGain.Uniform.Dev.Mau
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace HindsightGain.Uniform.Dev.Mau
open HindsightGain.Uniform HindsightGain.Uniform.Dev.Khin

/-- one coordinate of the mixed space: a coin and a sign sequence -/
abbrev mu1 : Measure (Bool × (ℕ → Bool)) := coin.prod (signLaw ℕ)

/-- the mixed product space -/
abbrev Pm (n : ℕ) : Measure (Fin n → Bool × (ℕ → Bool)) := Measure.pi (fun _ => mu1)

section
variable {T : Type} (F : Finset T) (hF : F.Nonempty) {n : ℕ}
  (ψ : Fin n → T → ℝ) (φ : Fin n → T → SequenceL2)

/-- coordinate `i` of the mixed sum: replaced (`i ∈ R`) or not -/
def tmi (R : Finset (Fin n)) (i : Fin n) (ω : Fin n → Bool × (ℕ → Bool)) (t : T) : ℝ :=
  if i ∈ R then Real.sqrt 2 * signSeries (φ i t) (ω i).2 else sign (ω i).1 * ψ i t

def tm (R : Finset (Fin n)) (ω : Fin n → Bool × (ℕ → Bool)) (t : T) : ℝ :=
  ∑ i, tmi ψ φ R i ω t

def FR (R : Finset (Fin n)) (ω : Fin n → Bool × (ℕ → Bool)) : ℝ :=
  F.sup' hF (fun t => tm ψ φ R ω t)

lemma measurable_tmi (R : Finset (Fin n)) (i : Fin n) (t : T) :
    Measurable (fun ω => tmi ψ φ R i ω t) := by
  unfold tmi
  split_ifs
  · exact measurable_const.mul ((signSeries_measurable _).comp
      (measurable_snd.comp (measurable_pi_apply i)))
  · exact (mau_measurable_sign.comp (measurable_fst.comp (measurable_pi_apply i))).mul measurable_const

lemma integrable_tmi (R : Finset (Fin n)) (i : Fin n) (t : T) :
    Integrable (fun ω => tmi ψ φ R i ω t) (Pm n) := by
  unfold tmi
  split_ifs
  · have hmp : MeasurePreserving (fun ω : Fin n → Bool × (ℕ → Bool) => (ω i).2) (Pm n)
        (signLaw ℕ) := (measurePreserving_snd (μ := coin) (ν := signLaw ℕ)).comp
        (measurePreserving_eval (fun _ : Fin n => mu1) i)
    exact (hmp.integrable_comp_of_integrable (signSeries_integrable (φ i t))).const_mul _
  · refine Integrable.of_bound (C := |ψ i t|) ?_ ?_
    · exact ((mau_measurable_sign.comp (measurable_fst.comp (measurable_pi_apply i))).mul
        measurable_const).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ω => ?_
      have : |sign (ω i).1| = 1 := by
        rcases (ω i).1 <;> simp [sign]
      simp [this]

lemma measurable_tm (R : Finset (Fin n)) (t : T) : Measurable (fun ω => tm ψ φ R ω t) := by
  unfold tm
  exact Finset.measurable_sum _ fun i _ => measurable_tmi ψ φ R i t

lemma integrable_tm (R : Finset (Fin n)) (t : T) : Integrable (fun ω => tm ψ φ R ω t) (Pm n) := by
  unfold tm
  exact integrable_finsetSum _ fun i _ => integrable_tmi ψ φ R i t

lemma integrable_FR (R : Finset (Fin n)) : Integrable (FR F hF ψ φ R) (Pm n) :=
  integrable_sup' F hF (fun t ω => tm ψ φ R ω t) (fun t _ => measurable_tm ψ φ R t)
    (fun t _ => integrable_tm ψ φ R t)

end

lemma integral_prod_fst (k : Bool → ℝ) : ∫ x, k x.1 ∂mu1 = ∫ b, k b ∂coin := by
  have h := measurePreserving_fst (μ := coin) (ν := signLaw ℕ)
  calc ∫ x, k x.1 ∂mu1 = ∫ b, k b ∂(mu1.map Prod.fst) :=
        (integral_map h.aemeasurable measurable_from_top.aestronglyMeasurable).symm
    _ = _ := by rw [h.map_eq]

lemma integral_prod_snd (k : (ℕ → Bool) → ℝ) (hk : Measurable k) :
    ∫ x, k x.2 ∂mu1 = ∫ w, k w ∂(signLaw ℕ) := by
  have h := measurePreserving_snd (μ := coin) (ν := signLaw ℕ)
  calc ∫ x, k x.2 ∂mu1 = ∫ b, k b ∂(mu1.map Prod.snd) :=
        (integral_map h.aemeasurable hk.aestronglyMeasurable).symm
    _ = _ := by rw [h.map_eq]

section
variable {T : Type} (F : Finset T) (hF : F.Nonempty) {m : ℕ}
  (ψ : Fin (m + 1) → T → ℝ) (φ : Fin (m + 1) → T → SequenceL2)

/-- the contribution of the coordinates other than `a` -/
def Gr (a : Fin (m + 1)) (R : Finset (Fin (m + 1))) (r : Fin m → Bool × (ℕ → Bool)) (t : T) : ℝ :=
  ∑ j : Fin m, (if a.succAbove j ∈ R then Real.sqrt 2 * signSeries (φ (a.succAbove j) t) (r j).2
    else sign (r j).1 * ψ (a.succAbove j) t)

lemma tm_insertNth (a : Fin (m + 1)) (R : Finset (Fin (m + 1))) (x : Bool × (ℕ → Bool))
    (r : Fin m → Bool × (ℕ → Bool)) (t : T) :
    tm ψ φ R (Fin.insertNth a x r) t = tmi ψ φ R a (Fin.insertNth a x r) t
      + Gr ψ φ a R r t := by
  unfold tm Gr
  rw [Fin.sum_univ_succAbove _ a]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [tmi, Fin.insertNth_apply_succAbove]

lemma tmi_a_notin (a : Fin (m + 1)) (R : Finset (Fin (m + 1))) (ha : a ∉ R)
    (x : Bool × (ℕ → Bool)) (r : Fin m → Bool × (ℕ → Bool)) (t : T) :
    tmi ψ φ R a (Fin.insertNth a x r) t = sign x.1 * ψ a t := by
  simp [tmi, ha]

lemma tmi_a_insert (a : Fin (m + 1)) (R : Finset (Fin (m + 1)))
    (x : Bool × (ℕ → Bool)) (r : Fin m → Bool × (ℕ → Bool)) (t : T) :
    tmi ψ φ (insert a R) a (Fin.insertNth a x r) t = Real.sqrt 2 * signSeries (φ a t) x.2 := by
  simp [tmi]

lemma Gr_insert (a : Fin (m + 1)) (R : Finset (Fin (m + 1))) (r : Fin m → Bool × (ℕ → Bool))
    (t : T) : Gr ψ φ a (insert a R) r t = Gr ψ φ a R r t := by
  unfold Gr
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Finset.mem_insert, Fin.succAbove_ne]

end

lemma integral_split {m : ℕ} (a : Fin (m + 1))
    (H : (Fin (m + 1) → Bool × (ℕ → Bool)) → ℝ) (hH : Integrable H (Pm (m + 1))) :
    ∫ ω, H ω ∂(Pm (m + 1)) = ∫ r, ∫ x, H (Fin.insertNth a x r) ∂mu1 ∂(Pm m) ∧
    Integrable (fun r => ∫ x, H (Fin.insertNth a x r) ∂mu1) (Pm m) := by
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => mu1) a).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Bool × (ℕ → Bool)) a)
  have hint : Integrable (fun p => H (Fin.insertNth a p.1 p.2)) (mu1.prod (Pm m)) := by
    exact hmp.integrable_comp_of_integrable hH
  refine ⟨?_, ?_⟩
  · have := hmp.integral_comp' H
    refine Eq.trans this.symm ?_
    exact integral_prod_symm _ hint
  · exact hint.integral_prod_right

section
variable {T : Type} (F : Finset T) (hF : F.Nonempty) {m : ℕ}
  (ψ : Fin (m + 1) → T → ℝ) (φ : Fin (m + 1) → T → SequenceL2)

lemma step_mono (a : Fin (m + 1)) (R : Finset (Fin (m + 1)))
    (ha : a ∉ R)
    (h : ∀ i t t', ψ i t - ψ i t' ≤ ‖φ i t - φ i t'‖) :
    ∫ ω, FR F hF ψ φ R ω ∂(Pm (m + 1)) ≤ ∫ ω, FR F hF ψ φ (insert a R) ω ∂(Pm (m + 1)) := by
  obtain ⟨e1, i1⟩ := integral_split a _ (integrable_FR F hF ψ φ R)
  obtain ⟨e2, i2⟩ := integral_split a _ (integrable_FR F hF ψ φ (insert a R))
  rw [e1, e2]
  refine integral_mono i1 i2 fun r => ?_
  set G : T → ℝ := Gr ψ φ a R r with hG
  have hL : ∀ x : Bool × (ℕ → Bool), FR F hF ψ φ R (Fin.insertNth a x r)
      = F.sup' hF (fun t => G t + sign x.1 * ψ a t) := by
    intro x
    unfold FR
    refine Finset.sup'_congr hF rfl fun t _ => ?_
    rw [tm_insertNth, tmi_a_notin ψ φ a R ha]; ring
  have hR : ∀ x : Bool × (ℕ → Bool), FR F hF ψ φ (insert a R) (Fin.insertNth a x r)
      = F.sup' hF (fun t => G t + Real.sqrt 2 * signSeries (φ a t) x.2) := by
    intro x
    unfold FR
    refine Finset.sup'_congr hF rfl fun t _ => ?_
    rw [tm_insertNth, tmi_a_insert, Gr_insert]; ring
  simp only [hL, hR]
  rw [integral_prod_fst (fun b => F.sup' hF (fun t => G t + sign b * ψ a t)),
    integral_prod_snd (fun w => F.sup' hF (fun t => G t + Real.sqrt 2 * signSeries (φ a t) w))
      (measurable_sup'_pt F hF (fun t w => G t + Real.sqrt 2 * signSeries (φ a t) w)
        (fun t _ => measurable_const.add (measurable_const.mul (signSeries_measurable _)))),
    integral_coin]
  have := step_one F hF G (ψ a) (φ a) (h a)
  simp only [sign, if_true, Bool.false_eq_true, if_false]
  simpa [sub_eq_add_neg, add_comm] using this

end

lemma induction_step {T : Type} (F : Finset T) (hF : F.Nonempty) {n : ℕ}
    (ψ : Fin n → T → ℝ) (φ : Fin n → T → SequenceL2)
    (h : ∀ i t t', ψ i t - ψ i t' ≤ ‖φ i t - φ i t'‖) (R : Finset (Fin n)) :
    ∫ ω, FR F hF ψ φ ∅ ω ∂(Pm n) ≤ ∫ ω, FR F hF ψ φ R ω ∂(Pm n) := by
  induction R using Finset.induction_on with
  | empty => exact le_rfl
  | insert a s ha ih =>
    refine ih.trans ?_
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := a.pos; omega⟩
    exact step_mono F hF ψ φ a s ha h

/-- the curried coordinates of `signLaw (Fin n × ℕ)` are `n` independent `signLaw ℕ` -/
lemma curry_map (n : ℕ) :
    (signLaw (Fin n × ℕ)).map (fun (δ : Fin n × ℕ → Bool) i k => δ (i, k))
      = Measure.pi (fun _ : Fin n => signLaw ℕ) := by
  have := Measure.infinitePi_map_curry (ι := Fin n) (κ := ℕ) (X := Bool) (fun _ _ => coin)
  rw [Measure.infinitePi_eq_pi (ι := Fin n)] at this
  exact this

lemma measurable_curry (n : ℕ) :
    Measurable (fun (δ : Fin n × ℕ → Bool) i k => δ (i, k)) := by fun_prop

lemma proj1_map (n : ℕ) :
    (Pm n).map (fun (ω : Fin n → Bool × (ℕ → Bool)) i => (ω i).1)
      = signLaw (Fin n) := by
  have h := Measure.pi_map_pi (μ := fun _ : Fin n => mu1) (f := fun _ => Prod.fst)
    (fun _ => measurable_fst.aemeasurable)
  have h2 := measurePreserving_fst (μ := coin) (ν := signLaw ℕ)
  simp only [h2.map_eq] at h
  unfold signLaw
  rw [Measure.infinitePi_eq_pi]
  exact h

lemma proj2_map (n : ℕ) :
    (Pm n).map (fun (ω : Fin n → Bool × (ℕ → Bool)) i => (ω i).2)
      = Measure.pi (fun _ : Fin n => signLaw ℕ) := by
  have h := Measure.pi_map_pi (μ := fun _ : Fin n => mu1) (f := fun _ => Prod.snd)
    (fun _ => measurable_snd.aemeasurable)
  have h2 := measurePreserving_snd (μ := coin) (ν := signLaw ℕ)
  simp only [h2.map_eq] at h
  exact h

section
variable {T : Type} (F : Finset T) (hF : F.Nonempty) {n : ℕ}
  (ψ : Fin n → T → ℝ) (φ : Fin n → T → SequenceL2)

/-- the finite scalar supremum -/
def Fsc (ε : Fin n → Bool) : ℝ := F.sup' hF (fun t => ∑ i, sign (ε i) * ψ i t)

/-- the finite vector supremum, on the curried space -/
def Fvc (w : Fin n → ℕ → Bool) : ℝ := F.sup' hF (fun t => ∑ i, signSeries (φ i t) (w i))

/-- the finite vector supremum on `Fin n × ℕ → Bool` -/
def Fvec (δ : Fin n × ℕ → Bool) : ℝ :=
  F.sup' hF (fun t => ∑ i, signSeries (φ i t) (fun k => δ (i, k)))

lemma sup'_const_mul (r : ℝ) (hr : 0 ≤ r) (f : T → ℝ) :
    F.sup' hF (fun t => r * f t) = r * F.sup' hF f := by
  obtain ⟨t0, ht0, e0⟩ := Finset.exists_mem_eq_sup' hF f
  obtain ⟨t1, ht1, e1⟩ := Finset.exists_mem_eq_sup' hF (fun t => r * f t)
  apply le_antisymm
  · rw [e1]
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' f ht1) hr
  · rw [e0]
    exact Finset.le_sup' (fun t => r * f t) ht0

lemma FR_empty (ω : Fin n → Bool × (ℕ → Bool)) :
    FR F hF ψ φ ∅ ω = Fsc F hF ψ (fun i => (ω i).1) := by
  unfold FR Fsc tm tmi
  simp

lemma FR_univ (ω : Fin n → Bool × (ℕ → Bool)) :
    FR F hF ψ φ Finset.univ ω = Real.sqrt 2 * Fvc F hF φ (fun i => (ω i).2) := by
  unfold FR Fvc tm tmi
  rw [← sup'_const_mul F hF _ (Real.sqrt_nonneg 2)]
  refine Finset.sup'_congr hF rfl fun t _ => ?_
  simp [Finset.mul_sum]

lemma measurable_Fvc : Measurable (Fvc F hF φ) := by
  have key : ∀ t ∈ F, Measurable (fun w : Fin n → ℕ → Bool => ∑ i, signSeries (φ i t) (w i)) := by
    intro t _
    refine Finset.measurable_sum Finset.univ (fun i _ => ?_)
    have h1 : Measurable (fun w : Fin n → ℕ → Bool => w i) := measurable_pi_apply i
    exact (signSeries_measurable (φ i t)).comp h1
  exact measurable_sup'_pt F hF
    (fun t (w : Fin n → ℕ → Bool) => ∑ i, signSeries (φ i t) (w i)) key

lemma integral_Fsc : ∫ ε, Fsc F hF ψ ε ∂(signLaw (Fin n)) =
    ∫ ω, FR F hF ψ φ ∅ ω ∂(Pm n) := by
  have hm : AEMeasurable (fun (ω : Fin n → Bool × (ℕ → Bool)) i => (ω i).1) (Pm n) :=
    Measurable.aemeasurable (measurable_pi_lambda _ fun i =>
      measurable_fst.comp (measurable_pi_apply i))
  have := integral_map (μ := Pm n) hm (f := Fsc F hF ψ)
    (Measurable.of_discrete.aestronglyMeasurable)
  rw [proj1_map n] at this
  rw [this]
  simp only [FR_empty]

lemma integral_Fvec : ∫ δ, Fvec F hF φ δ ∂(signLaw (Fin n × ℕ)) =
    ∫ ω, Fvc F hF φ (fun i => (ω i).2) ∂(Pm n) := by
  rw [← integral_map (φ := fun (ω : Fin n → Bool × (ℕ → Bool)) i => (ω i).2)
    (Measurable.aemeasurable (measurable_pi_lambda _ fun i =>
      measurable_snd.comp (measurable_pi_apply i)))
    (measurable_Fvc F hF φ).aestronglyMeasurable, proj2_map n, ← curry_map n,
    integral_map (measurable_curry n).aemeasurable (measurable_Fvc F hF φ).aestronglyMeasurable]
  rfl

theorem core_le (h : ∀ i t t', ψ i t - ψ i t' ≤ ‖φ i t - φ i t'‖) :
    ∫ ε, Fsc F hF ψ ε ∂(signLaw (Fin n)) ≤
      Real.sqrt 2 * ∫ δ, Fvec F hF φ δ ∂(signLaw (Fin n × ℕ)) := by
  rw [integral_Fsc F hF ψ φ, integral_Fvec F hF φ, ← integral_const_mul]
  have := induction_step F hF ψ φ h Finset.univ
  simpa only [FR_univ] using this

lemma coord_measurePreserving (i : Fin n) :
    MeasurePreserving (fun (δ : Fin n × ℕ → Bool) k => δ (i, k)) (signLaw (Fin n × ℕ))
      (signLaw ℕ) := by
  have h1 : MeasurePreserving (fun (δ : Fin n × ℕ → Bool) i k => δ (i, k))
      (signLaw (Fin n × ℕ)) (Measure.pi (fun _ : Fin n => signLaw ℕ)) :=
    ⟨measurable_curry n, curry_map n⟩
  exact (measurePreserving_eval (fun _ : Fin n => signLaw ℕ) i).comp h1

theorem integrable_Fvec : Integrable (Fvec F hF φ) (signLaw (Fin n × ℕ)) := by
  have key : ∀ t ∈ F, Measurable
      (fun δ : Fin n × ℕ → Bool => ∑ i, signSeries (φ i t) (fun k => δ (i, k))) :=
    fun t _ => Finset.measurable_sum _ fun i _ =>
      (signSeries_measurable _).comp (by fun_prop)
  have key2 : ∀ t ∈ F, Integrable
      (fun δ : Fin n × ℕ → Bool => ∑ i, signSeries (φ i t) (fun k => δ (i, k)))
      (signLaw (Fin n × ℕ)) :=
    fun t _ => integrable_finsetSum _ fun i _ =>
      (coord_measurePreserving i).integrable_comp_of_integrable (signSeries_integrable _)
  exact integrable_sup' F hF (fun t (δ : Fin n × ℕ → Bool) => ∑ i, signSeries (φ i t) (fun k => δ (i, k))) key key2

end

end HindsightGain.Uniform.Dev.Mau
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace HindsightGain.Uniform.Dev.Mau
open HindsightGain.Uniform

lemma extendedMean_coe {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ)
    (hf : Integrable f μ) :
    extendedMean μ (fun ω => ((f ω : ℝ) : EReal)) = ((∫ ω, f ω ∂μ : ℝ) : EReal) := by
  unfold extendedMean
  have e1 : ∀ ω, ((f ω : ℝ) : EReal).toENNReal = ENNReal.ofReal (f ω) := fun ω => rfl
  have e2 : ∀ ω, (-((f ω : ℝ) : EReal)).toENNReal = ENNReal.ofReal (-f ω) := fun ω => by
    rw [← EReal.coe_neg]; rfl
  simp only [e1, e2]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  have h1 : ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≠ ⊤ := hf.lintegral_lt_top.ne
  have h2 : ∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ ≠ ⊤ := hf.neg.lintegral_lt_top.ne
  rw [EReal.coe_sub, EReal.coe_ennreal_toReal h1, EReal.coe_ennreal_toReal h2]

lemma extendedMean_mono {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → EReal)
    (h : ∀ ω, X ω ≤ Y ω) : extendedMean μ X ≤ extendedMean μ Y := by
  unfold extendedMean
  refine EReal.sub_le_sub ?_ ?_
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.2
      (lintegral_mono fun ω => EReal.toENNReal_le_toENNReal (h ω))
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.2
      (lintegral_mono fun ω => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (h ω)))

lemma extendedMean_le_iSup {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : ℕ → Ω → ℝ) (hm : ∀ m, Measurable (x m)) (hi : ∀ m, Integrable (x m) μ)
    (hmono : ∀ ω, Monotone (fun m => x m ω)) :
    extendedMean μ (fun ω => ⨆ m, ((x m ω : ℝ) : EReal)) ≤
      ⨆ m, ((∫ ω, x m ω ∂μ : ℝ) : EReal) := by
  set P : ℕ → ℝ≥0∞ := fun m => ∫⁻ ω, ENNReal.ofReal (x m ω) ∂μ with hP
  set N : ℕ → ℝ≥0∞ := fun m => ∫⁻ ω, ENNReal.ofReal (-x m ω) ∂μ with hN
  have hPm : Monotone P := fun a b hab => lintegral_mono fun ω =>
    ENNReal.ofReal_le_ofReal (hmono ω hab)
  have hNa : Antitone N := fun a b hab => lintegral_mono fun ω =>
    ENNReal.ofReal_le_ofReal (neg_le_neg (hmono ω hab))
  have hN0 : N 0 ≠ ⊤ := (hi 0).neg.lintegral_lt_top.ne
  have pt1 : ∀ ω, (⨆ m, ((x m ω : ℝ) : EReal)).toENNReal = ⨆ m, ENNReal.ofReal (x m ω) := by
    intro ω
    exact Monotone.map_iSup_of_continuousAt (f := EReal.toENNReal)
      EReal.continuous_toENNReal.continuousAt (fun a b h => EReal.toENNReal_le_toENNReal h)
      EReal.toENNReal_bot
  have pt2 : ∀ ω, (-⨆ m, ((x m ω : ℝ) : EReal)).toENNReal = ⨅ m, ENNReal.ofReal (-x m ω) := by
    intro ω
    have := Antitone.map_iSup_of_continuousAt (f := fun e : EReal => (-e).toENNReal)
      (g := fun m => ((x m ω : ℝ) : EReal))
      (EReal.continuous_toENNReal.comp continuous_neg).continuousAt
      (fun a b h => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 h))
      (by simp)
    rw [this]
    refine iInf_congr fun m => ?_
    rw [← EReal.coe_neg]; rfl
  have hPsup : ∫⁻ ω, (⨆ m, ((x m ω : ℝ) : EReal)).toENNReal ∂μ = ⨆ m, P m := by
    simp only [pt1]
    exact lintegral_iSup (fun m => (hm m).ennreal_ofReal)
      (fun a b hab ω => ENNReal.ofReal_le_ofReal (hmono ω hab))
  have hNinf : ∫⁻ ω, (-⨆ m, ((x m ω : ℝ) : EReal)).toENNReal ∂μ = ⨅ m, N m := by
    simp only [pt2]
    exact lintegral_iInf (fun m => (hm m).neg.ennreal_ofReal)
      (fun a b hab ω => ENNReal.ofReal_le_ofReal (neg_le_neg (hmono ω hab))) hN0
  have hterm : ∀ m, (P m : EReal) - (N m : EReal) = ((∫ ω, x m ω ∂μ : ℝ) : EReal) := by
    intro m
    rw [← extendedMean_coe μ _ (hi m)]
    rfl
  have hT1 : Tendsto (fun m => (P m : EReal)) atTop (𝓝 ((⨆ m, P m : ℝ≥0∞) : EReal)) :=
    (continuous_coe_ennreal_ereal.tendsto _).comp (tendsto_atTop_iSup hPm)
  have hT2 : Tendsto (fun m => (N m : EReal)) atTop (𝓝 ((⨅ m, N m : ℝ≥0∞) : EReal)) :=
    (continuous_coe_ennreal_ereal.tendsto _).comp (tendsto_atTop_iInf hNa)
  have hNtop : (⨅ m, N m : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top hN0 (iInf_le N 0)
  have hca := EReal.continuousAt_add (p := (((⨆ m, P m : ℝ≥0∞) : EReal),
      -((⨅ m, N m : ℝ≥0∞) : EReal)))
    (Or.inr (by
      simp only [ne_eq, EReal.neg_eq_bot_iff]
      exact fun h => hNtop (by simpa using h)))
    (Or.inl (by
      have : (0 : EReal) ≤ ((⨆ m, P m : ℝ≥0∞) : EReal) := EReal.coe_ennreal_nonneg _
      intro h
      have h' : ((⨆ m, P m : ℝ≥0∞) : EReal) = ⊥ := h
      rw [h'] at this
      exact absurd (le_bot_iff.1 this) (by simp)))
  have hT : Tendsto (fun m => (P m : EReal) - (N m : EReal)) atTop
      (𝓝 (((⨆ m, P m : ℝ≥0∞) : EReal) - ((⨅ m, N m : ℝ≥0∞) : EReal))) := by
    simp only [sub_eq_add_neg]
    exact hca.tendsto.comp (hT1.prodMk_nhds (hT2.neg))
  unfold extendedMean
  rw [hPsup, hNinf]
  refine le_of_tendsto' hT fun m => ?_
  rw [hterm]
  exact le_iSup (fun m => ((∫ ω, x m ω ∂μ : ℝ) : EReal)) m

end HindsightGain.Uniform.Dev.Mau
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace HindsightGain.Uniform.Dev.Mau
open HindsightGain.Uniform HindsightGain.Uniform.Dev.Khin

lemma extendedMean_bot {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    extendedMean μ (fun _ => (⊥ : EReal)) = ⊥ := by
  unfold extendedMean
  simp

lemma main_nonempty {S : Type} [Countable S] [Nonempty S] (n : ℕ)
    (ψ : Fin n → S → ℝ) (φ : Fin n → S → SequenceL2)
    (h : ∀ i s s', ψ i s - ψ i s' ≤ ‖φ i s - φ i s'‖) :
    scalarComplexity n ψ ≤ (Real.sqrt 2 : EReal) * vectorComplexity n φ := by
  obtain ⟨e, he⟩ := exists_surjective_nat S
  set ψ' : Fin n → ℕ → ℝ := fun i j => ψ i (e j) with hψ'
  set φ' : Fin n → ℕ → SequenceL2 := fun i j => φ i (e j) with hφ'
  have h' : ∀ i j j', ψ' i j - ψ' i j' ≤ ‖φ' i j - φ' i j'‖ := fun i j j' => h i _ _
  let F : ℕ → Finset ℕ := fun m => Finset.range (m + 1)
  have hF : ∀ m, (F m).Nonempty := fun m => Finset.nonempty_range_add_one
  -- scalar side
  have hX : ∀ ε : Fin n → Bool, (⨆ s : S, ((∑ i, sign (ε i) * ψ i s : ℝ) : EReal))
      = ⨆ m, ((Fsc (F m) (hF m) ψ' ε : ℝ) : EReal) := by
    intro ε
    rw [← he.iSup_comp (fun s => ((∑ i, sign (ε i) * ψ i s : ℝ) : EReal))]
    apply le_antisymm
    · refine iSup_le fun j => ?_
      refine le_trans ?_ (le_iSup _ j)
      exact EReal.coe_le_coe_iff.2 (Finset.le_sup' (fun j => ∑ i, sign (ε i) * ψ' i j)
        (Finset.self_mem_range_succ j))
    · refine iSup_le fun m => ?_
      obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (hF m) (fun j => ∑ i, sign (ε i) * ψ' i j)
      unfold Fsc
      rw [hj]
      exact le_iSup (fun j => ((∑ i, sign (ε i) * ψ i (e j) : ℝ) : EReal)) j
  have hmono : ∀ ε : Fin n → Bool, Monotone (fun m => Fsc (F m) (hF m) ψ' ε) := by
    intro ε a b hab
    unfold Fsc
    exact Finset.sup'_mono _ (Finset.range_mono (by omega)) _
  have h1 : scalarComplexity n ψ ≤ ⨆ m, ((∫ ε, Fsc (F m) (hF m) ψ' ε ∂(signLaw (Fin n)) : ℝ) : EReal) := by
    unfold scalarComplexity
    simp only [hX]
    exact extendedMean_le_iSup (signLaw (Fin n)) (fun m ε => Fsc (F m) (hF m) ψ' ε)
      (fun m => Measurable.of_discrete) (fun m => Integrable.of_finite) hmono
  refine h1.trans (iSup_le fun m => ?_)
  have h2 := core_le (F m) (hF m) ψ' φ' h'
  have h3 : ((∫ δ, Fvec (F m) (hF m) φ' δ ∂(signLaw (Fin n × ℕ)) : ℝ) : EReal) ≤ vectorComplexity n φ := by
    rw [← extendedMean_coe _ _ (integrable_Fvec (F m) (hF m) φ')]
    unfold vectorComplexity
    refine extendedMean_mono _ _ _ fun δ => ?_
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (hF m)
      (fun j => ∑ i, signSeries (φ' i j) (fun k => δ (i, k)))
    unfold Fvec
    rw [hj]
    exact le_iSup (fun s : S => ((∑ i, signSeries (φ i s) (fun k => δ (i, k)) : ℝ) : EReal)) (e j)
  calc ((∫ ε, Fsc (F m) (hF m) ψ' ε ∂(signLaw (Fin n)) : ℝ) : EReal)
      ≤ ((Real.sqrt 2 * ∫ δ, Fvec (F m) (hF m) φ' δ ∂(signLaw (Fin n × ℕ)) : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.2 h2
    _ = (Real.sqrt 2 : EReal) * ((∫ δ, Fvec (F m) (hF m) φ' δ ∂(signLaw (Fin n × ℕ)) : ℝ) : EReal) :=
        EReal.coe_mul _ _
    _ ≤ (Real.sqrt 2 : EReal) * vectorComplexity n φ :=
        mul_le_mul_of_nonneg_left h3 (EReal.coe_nonneg.2 (Real.sqrt_nonneg _))

end HindsightGain.Uniform.Dev.Mau

namespace HindsightGain.Uniform
open HindsightGain.Uniform.Dev.Mau in
theorem chk_theorem_7 {S : Type} [Countable S] (n : ℕ) (hn : 1 ≤ n)
    (ψ : Fin n → S → ℝ) (φ : Fin n → S → SequenceL2)
    (h : ∀ i s s', ψ i s - ψ i s' ≤ ‖φ i s - φ i s'‖) :
    scalarComplexity n ψ ≤ (Real.sqrt 2 : EReal) * vectorComplexity n φ := by
  rcases isEmpty_or_nonempty S with hS | hS
  · have : scalarComplexity n ψ = ⊥ := by
      unfold scalarComplexity
      simp only [iSup_of_empty]
      exact extendedMean_bot _
    rw [this]; exact bot_le
  · exact main_nonempty n ψ φ h

end HindsightGain.Uniform
end
end

theorem solution : type_of% @HindsightGain.Uniform.chk_theorem_7 := @HindsightGain.Uniform.chk_theorem_7
