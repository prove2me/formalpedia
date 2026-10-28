-- Prove2me | solution 1 for OAI.Lech.complex_estimate_allModule
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:17:07.884643+00:00
-- url     : https://prove2.me/submissions/7556e707-f8af-48ef-bc19-20346b187920

import Mathlib
import Definitions.Def_OAIQ032L007
import Definitions.Def_OAIQ032L013
import Definitions.Def_OAIQ032L014
import Definitions.Def_OAIQ032L017
import Theorems.Thm_OAI_Lech_ReesRoot_sum_estimate
import Theorems.Thm_OAI_Lech_SourceGraded_acyclicity_finite_torsion

section
-- module Solutions.OAIQ032_LECH.Multiplicity_NumericalSupport
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Lech.Numerical
open Polynomial

lemma H_monic (h : ℕ) : (H h).Monic := by
  exact monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)

lemma H_natDegree (h : ℕ) : (H h).natDegree = h := by
  unfold H
  rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)]
  simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_id]

lemma H_eval_zero (h : ℕ) : (H h).eval 0 = (h.factorial : ℝ) := by
  unfold H
  simp only [eval_prod, eval_add, eval_X, eval_C, zero_add]
  norm_cast
  exact Finset.prod_range_add_one_eq_factorial h

lemma ρ_spec (n : ℕ) (j : Fin n) :
    -((j.val : ℝ) + 2) < ρ n j ∧ ρ n j < -((j.val : ℝ) + 1) ∧
      (H (n+1)).derivative.eval (ρ n j) = 0 :=
  (derivative_root_exists n j).choose_spec

lemma ρ_strictAnti (n : ℕ) : StrictAnti (ρ n) := by
  intro i j hij
  have hv : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast hij
  have hi := (ρ_spec n i).1
  have hj := (ρ_spec n j).2.1
  linarith

lemma derivative_factorization (n : ℕ) :
    (H (n+1)).derivative =
      (∏ j : Fin n, (X - C (ρ n j))) * C ((n : ℝ) + 1) := by
  have hm : (∏ j : Fin n, (X - C (ρ n j))).Monic :=
    monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)
  have hd : (∏ j : Fin n, (X - C (ρ n j))) ∣ (H (n+1)).derivative := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact pairwise_coprime_X_sub_C (ρ_strictAnti n).injective hij
    · intro j _
      exact dvd_iff_isRoot.mpr (ρ_spec n j).2.2
  have hdeg : (H (n+1)).derivative.natDegree ≤
      (∏ j : Fin n, (X - C (ρ n j))).natDegree := by
    rw [natDegree_derivative, H_natDegree, natDegree_finsetProd_X_sub_C_eq_card]
    simp
  have hc : (H (n+1)).derivative.leadingCoeff = (n : ℝ) + 1 := by
    simp [leadingCoeff_derivative, H_natDegree, H_monic]
  simpa only [hc] using eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le hm hd hdeg

lemma roundedRoot_error (n s : ℕ) (j : Fin n) :
    |(roundedRoot n s j : ℝ) - (s : ℝ) * ρ n j| ≤ 1 := by
  have hl := Int.floor_le ((s : ℝ) * ρ n j)
  have hu := Int.lt_floor_add_one ((s : ℝ) * ρ n j)
  rw [abs_le]
  dsimp [roundedRoot]
  constructor <;> linarith

lemma roundedRoot_positions (n : ℕ) :
    ∀ᶠ s : ℕ in Filter.atTop, ∀ j : Fin n,
      -((j.val : ℝ) + 2) * s < (roundedRoot n s j : ℝ) ∧
      (roundedRoot n s j : ℝ) < -((j.val : ℝ) + 1) * s := by
  apply Filter.eventually_all.mpr
  intro j
  have hρ := ρ_spec n j
  have hδ : 0 < ρ n j + ((j.val : ℝ) + 2) := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (ρ n j + ((j.val : ℝ) + 2)))
  filter_upwards [Filter.eventually_ge_atTop N, Filter.eventually_ge_atTop 1] with s hs hs1
  have hs' : (N : ℝ) ≤ s := by exact_mod_cast hs
  have hspos : 0 < (s : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs1)
  have herror := roundedRoot_error n s j
  have hf := Int.floor_le ((s : ℝ) * ρ n j)
  change (roundedRoot n s j : ℝ) ≤ _ at hf
  have hr : 1 < (s : ℝ) * (ρ n j + ((j.val : ℝ) + 2)) := by
    exact (div_lt_iff₀ hδ).mp (hN.trans_le hs')
  rw [abs_le] at herror
  constructor <;> nlinarith

lemma derivative_eval (n : ℕ) (x : ℝ) :
    (H (n+1)).derivative.eval x = P n x * ((n : ℝ) + 1) := by
  rw [derivative_factorization]
  simp only [eval_mul, eval_prod, eval_sub, eval_X, eval_C, P]

lemma integral_P (n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n+1) :
    (∫ x in -(i : ℝ)..0, P n x) = (n.factorial : ℝ) := by
  have hi0 : i - 1 < n+1 := by omega
  have hz : (H (n+1)).eval (-(i : ℝ)) = 0 := by
    convert H_eval_zero_at (n+1) (i-1) hi0 using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    rw [Nat.cast_sub hi, Nat.cast_one]
    ring
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x => (H (n+1)).eval x / ((n : ℝ)+1))
      (P n x) x := by
    intro x
    have hd := ((H (n+1)).hasDerivAt x).div_const ((n : ℝ)+1)
    rw [derivative_eval, mul_div_cancel_right₀ _ (by positivity)] at hd
    exact hd
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)]
  · rw [H_eval_zero, hz, zero_div, sub_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]
    field_simp
  · have hc : Continuous (P n) := by
      unfold P
      fun_prop
    exact hc.intervalIntegrable _ _

lemma abs_prod_sub_prod_le {α : Type*} (t : Finset α) (a b : α → ℝ)
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (ha : ∀ j ∈ t, |a j| ≤ B) (hb : ∀ j ∈ t, |b j| ≤ B)
    (hab : ∀ j ∈ t, |a j - b j| ≤ δ) :
    |∏ j ∈ t, a j - ∏ j ∈ t, b j| ≤ δ * (B + 1) ^ t.card := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hδ
  | @insert j t hj ih =>
    have ha' : ∀ k ∈ t, |a k| ≤ B := fun k hk => ha k (Finset.mem_insert_of_mem hk)
    have hb' : ∀ k ∈ t, |b k| ≤ B := fun k hk => hb k (Finset.mem_insert_of_mem hk)
    have hab' : ∀ k ∈ t, |a k - b k| ≤ δ :=
      fun k hk => hab k (Finset.mem_insert_of_mem hk)
    have hprod : |∏ k ∈ t, a k| ≤ B ^ t.card := by
      rw [Finset.abs_prod]
      simpa using Finset.prod_le_prod (fun index _ => abs_nonneg (a index)) ha'
    have hp : B ^ t.card ≤ (B+1) ^ t.card := pow_le_pow_left₀ hB (by linarith) _
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    calc
      |a j * ∏ k ∈ t, a k - b j * ∏ k ∈ t, b k| =
          |(a j - b j) * (∏ k ∈ t, a k) + b j *
            ((∏ k ∈ t, a k) - ∏ k ∈ t, b k)| := by congr 1; ring
      _ ≤ |a j - b j| * |∏ k ∈ t, a k| +
          |b j| * |(∏ k ∈ t, a k) - ∏ k ∈ t, b k| := by
        simpa only [abs_mul] using abs_add_le
          ((a j - b j) * (∏ k ∈ t, a k))
          (b j * ((∏ k ∈ t, a k) - ∏ k ∈ t, b k))
      _ ≤ δ * (B+1) ^ t.card + B * (δ * (B+1) ^ t.card) := by
        apply add_le_add
        · exact mul_le_mul (hab j (Finset.mem_insert_self _ _)) (hprod.trans hp)
            (abs_nonneg _) hδ
        · exact mul_le_mul (hb j (Finset.mem_insert_self _ _)) (ih ha' hb' hab')
            (abs_nonneg _) hB
      _ = δ * (B+1) ^ (t.card+1) := by rw [pow_succ]; ring

lemma abs_ρ_le (n : ℕ) (j : Fin n) : |ρ n j| ≤ (n : ℝ)+1 := by
  have hρ := ρ_spec n j
  have hj : (j.val : ℝ)+1 ≤ n := by exact_mod_cast j.isLt
  rw [abs_le]
  constructor <;> linarith

lemma abs_mem_interval {n : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (-((n : ℝ)+1)) 0) :
    |x| ≤ (n : ℝ)+1 := by
  rw [abs_le]
  exact ⟨hx.1, hx.2.trans (by positivity)⟩

lemma bound_nonneg (n : ℕ) : 0 ≤ bound n := by unfold bound; positivity

lemma P_lipschitz (n : ℕ) {x y : ℝ}
    (hx : x ∈ Set.Icc (-((n : ℝ)+1)) 0)
    (hy : y ∈ Set.Icc (-((n : ℝ)+1)) 0) :
    |P n x - P n y| ≤ |x-y| * bound n := by
  have hfactor : ∀ z ∈ Set.Icc (-((n : ℝ)+1)) 0, ∀ j : Fin n,
      |z - ρ n j| ≤ 2*(n : ℝ)+3 := by
    intro z hz j
    calc
      |z - ρ n j| ≤ |z| + |ρ n j| := abs_sub _ _
      _ ≤ ((n : ℝ)+1) + ((n : ℝ)+1) := add_le_add (abs_mem_interval hz) (abs_ρ_le n j)
      _ ≤ 2*(n : ℝ)+3 := by linarith
  have h := abs_prod_sub_prod_le Finset.univ
    (fun j : Fin n => x - ρ n j) (fun j : Fin n => y - ρ n j)
    (by positivity : 0 ≤ 2*(n : ℝ)+3) (abs_nonneg (x-y))
    (fun j _ => hfactor x hx j) (fun j _ => hfactor y hy j)
    (fun j _ => by rw [sub_sub_sub_cancel_right])
  norm_num [P, bound, add_assoc] at h ⊢
  exact h

lemma scaledRoot_error {n s : ℕ} (hs : 0 < s) (j : Fin n) :
    |(roundedRoot n s j : ℝ) / s - ρ n j| ≤ 1 / s := by
  have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
  have heq : (roundedRoot n s j : ℝ) / s - ρ n j =
      ((roundedRoot n s j : ℝ) - (s : ℝ) * ρ n j) / s := by field_simp
  rw [heq, abs_div, abs_of_pos hs']
  exact div_le_div_of_nonneg_right (roundedRoot_error n s j) hs'.le

lemma Ps_error (n s : ℕ) (hs : 0 < s) {x : ℝ}
    (hx : x ∈ Set.Icc (-((n : ℝ)+1)) 0) :
    |Ps n s x - P n x| ≤ (1 / s) * bound n := by
  have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
  have hs1 : 1 ≤ (s : ℝ) := by exact_mod_cast hs
  have hδ : (1 : ℝ) / s ≤ 1 := (div_le_iff₀ hs').mpr (by linarith)
  have hfactor : ∀ j : Fin n, |x - ρ n j| ≤ 2*(n : ℝ)+2 := by
    intro j
    calc
      |x - ρ n j| ≤ |x| + |ρ n j| := abs_sub _ _
      _ ≤ ((n : ℝ)+1) + ((n : ℝ)+1) := add_le_add (abs_mem_interval hx) (abs_ρ_le n j)
      _ = 2*(n : ℝ)+2 := by ring
  have hfactor' : ∀ j : Fin n,
      |x - (roundedRoot n s j : ℝ)/s| ≤ 2*(n : ℝ)+3 := by
    intro j
    have he : |ρ n j - (roundedRoot n s j : ℝ)/s| ≤ 1 := by
      rw [abs_sub_comm]
      exact (scaledRoot_error hs j).trans hδ
    calc
      |x - (roundedRoot n s j : ℝ)/s| =
        |(x - ρ n j) + (ρ n j - (roundedRoot n s j : ℝ)/s)| := by congr 1; ring
      _ ≤ |x - ρ n j| + |ρ n j - (roundedRoot n s j : ℝ)/s| := abs_add_le _ _
      _ ≤ (2*(n : ℝ)+2) + 1 := add_le_add (hfactor j) he
      _ = 2*(n : ℝ)+3 := by ring
  have h := abs_prod_sub_prod_le Finset.univ
    (fun j : Fin n => x - (roundedRoot n s j : ℝ)/s) (fun j : Fin n => x - ρ n j)
    (by positivity : 0 ≤ 2*(n : ℝ)+3) (by positivity : 0 ≤ (1 : ℝ)/s)
    (fun j _ => hfactor' j) (fun j _ => (hfactor j).trans (by linarith))
    (fun j _ => by
      rw [sub_sub_sub_cancel_left, abs_sub_comm]
      exact scaledRoot_error hs j)
  norm_num [P, Ps, bound, add_assoc] at h ⊢
  exact h

lemma riemann_error (f : ℝ → ℝ) (hf : Continuous f) (a ε B : ℝ)
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (m : ℕ)
    (hlip : ∀ x ∈ Set.Icc a (a + m * ε), ∀ y ∈ Set.Icc a (a + m * ε),
      |f x - f y| ≤ |x - y| * B) :
    |ε * (∑ k ∈ Finset.range m, f (a + k * ε)) -
      ∫ x in a..(a + m * ε), f x| ≤ m * ε ^ 2 * B := by
  let p : ℕ → ℝ := fun k => a + k * ε
  have hdiff (k : ℕ) : p (k+1) - p k = ε := by dsimp [p]; push_cast; ring
  have hstep (k : ℕ) : p k ≤ p (k+1) := by linarith [hdiff k]
  have hcell (k : ℕ) (hk : k < m) :
      |ε * f (p k) - ∫ x in p k..p (k+1), f x| ≤ ε^2 * B := by
    have hpk : p k ∈ Set.Icc a (a + m * ε) := by
      have hkm : (k : ℝ) ≤ m := by exact_mod_cast hk.le
      dsimp [p]
      constructor
      · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg k) hε)
      · exact add_le_add_right (mul_le_mul_of_nonneg_right hkm hε) a
    have hright : p (k+1) ≤ a + m * ε := by
      have hkm : ((k+1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hk
      exact add_le_add_right (mul_le_mul_of_nonneg_right hkm hε) a
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := p k) (b := p (k+1)) (C := ε * B) (f := fun x => f (p k) - f x) (by
        intro x hx
        rw [Set.uIoc_of_le (hstep k)] at hx
        have hx' : x ∈ Set.Icc a (a + m * ε) :=
          ⟨hpk.1.trans hx.1.le, hx.2.trans hright⟩
        have hdist : |p k - x| ≤ ε := by
          rw [abs_of_nonpos (by linarith only [hx.1] : p k - x ≤ 0)]
          linarith only [hdiff k, hx.2]
        simpa only [Real.norm_eq_abs] using
          (hlip _ hpk _ hx').trans (mul_le_mul_of_nonneg_right hdist hB))
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _), intervalIntegral.integral_const, hdiff,
      smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hε] at hh
    nlinarith [hh]
  have hsum := (Finset.abs_sum_le_sum_abs
    (fun k => ε * f (p k) - ∫ x in p k..p (k+1), f x) (Finset.range m)).trans
    (Finset.sum_le_sum (fun k hk => hcell k (Finset.mem_range.mp hk)))
  have hint := intervalIntegral.sum_integral_adjacent_intervals
    (μ := MeasureTheory.volume) (a := p) (n := m) (fun k _ => hf.intervalIntegrable (p k) (p (k+1)))
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hint] at hsum
  simpa [p, pow_two, mul_assoc] using hsum

lemma layer_error (n i s : ℕ) (hi : 1 ≤ i) (hin : i ≤ n+1) (hs : 0 < s) :
    |normalizedLayer n i s - (n.factorial : ℝ)| ≤
      2 * ((n : ℝ)+1) * bound n / s := by
  have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
  have hsn : (s : ℝ) ≠ 0 := ne_of_gt hs'
  have hin' : (i : ℝ) ≤ (n : ℝ)+1 := by exact_mod_cast hin
  have hb := bound_nonneg n
  have hsub : Set.Icc (-(i : ℝ)) 0 ⊆ Set.Icc (-((n : ℝ)+1)) 0 := by
    intro x hx
    exact ⟨by linarith only [hx.1, hin'], hx.2⟩
  have hright : -(i : ℝ) + (i*s : ℕ) * (1 / (s : ℝ)) = 0 := by
    push_cast
    field_simp; ring
  have hc : Continuous (P n) := by unfold P; fun_prop
  have hr := riemann_error (P n) hc (-(i : ℝ)) (1 / s) (bound n)
    (by positivity) hb (i*s) (by
      rw [hright]
      intro x hx y hy
      exact P_lipschitz n (hsub hx) (hsub hy))
  rw [hright, integral_P n i hi hin] at hr
  simp only [mul_one_div] at hr
  have herr : ((i*s : ℕ) : ℝ) * (1 / (s : ℝ))^2 * bound n =
      (i : ℝ) * bound n / s := by push_cast; field_simp
  rw [herr] at hr
  have hpoint : ∀ k ∈ Finset.range (i*s),
      -(i : ℝ) + (k : ℝ) / s ∈ Set.Icc (-((n : ℝ)+1)) 0 := by
    intro k hk
    have hk' : (k : ℝ) ≤ (i : ℝ) * s := by
      exact_mod_cast (Finset.mem_range.mp hk).le
    apply hsub
    constructor
    · exact le_add_of_nonneg_right (by positivity)
    · have hkdiv : (k : ℝ) / s ≤ (i : ℝ) := (div_le_iff₀ hs').mpr hk'
      linarith
  have hp := (Finset.abs_sum_le_sum_abs
    (fun k : ℕ => Ps n s (-(i : ℝ) + k/s) - P n (-(i : ℝ) + k/s))
    (Finset.range (i*s))).trans (Finset.sum_le_sum
      (fun k hk => Ps_error n s hs (hpoint k hk)))
  rw [Finset.sum_sub_distrib] at hp
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hp
  have hp' := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (1 : ℝ)/s)
  have heq : (1 / (s : ℝ)) * (((i*s : ℕ) : ℝ) * ((1 / s) * bound n)) =
      (i : ℝ) * bound n / s := by push_cast; field_simp
  rw [heq, ← abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ)/s), ← abs_mul,
    mul_sub] at hp'
  have htotal := (abs_add_le
    (normalizedLayer n i s - (1 / s) * ∑ k ∈ Finset.range (i*s), P n (-(i : ℝ) + k/s))
    ((1 / s) * (∑ k ∈ Finset.range (i*s), P n (-(i : ℝ) + k/s)) - n.factorial)).trans
    (add_le_add hp' hr)
  rw [sub_add_sub_cancel] at htotal
  calc
    |normalizedLayer n i s - (n.factorial : ℝ)| ≤
        (i : ℝ)*bound n/s + (i : ℝ)*bound n/s := htotal
    _ ≤ 2 * ((n : ℝ)+1) * bound n / s := by
      have hle := mul_le_mul_of_nonneg_right hin' (div_nonneg hb hs'.le)
      calc
        (i : ℝ)*bound n/s + (i : ℝ)*bound n/s = 2*((i : ℝ)*(bound n/s)) := by ring
        _ ≤ 2*(((n : ℝ)+1)*(bound n/s)) :=
          mul_le_mul_of_nonneg_left hle (by norm_num)
        _ = 2*((n : ℝ)+1)*bound n/s := by ring


lemma layer_eq (n i s : ℕ) (hs : 0 < s) :
    layer n i s = (s : ℝ)^(n+1) * normalizedLayer n i s := by
  have hsn : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hterm (k : ℕ) :
      (∏ j : Fin n, ((k : ℝ) - (i : ℝ)*s - (roundedRoot n s j : ℝ))) =
      (s : ℝ)^n * Ps n s (-(i : ℝ) + k/s) := by
    unfold Ps
    rw [show (s : ℝ)^n = ∏ _j : Fin n, (s : ℝ) by simp, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    field_simp
    ring
  unfold layer normalizedLayer
  simp_rw [hterm]
  rw [← Finset.mul_sum, pow_succ]
  field_simp

lemma normalized_layer_error (n i s : ℕ) (hi : 1 ≤ i) (hin : i ≤ n+1) (hs : 0 < s) :
    |layer n i s / (s : ℝ)^(n+1) - (n.factorial : ℝ)| ≤
      2 * ((n : ℝ)+1) * bound n / s := by
  have hsn : (s : ℝ)^(n+1) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hs.ne')
  rw [layer_eq n i s hs, mul_div_cancel_left₀ _ hsn]
  exact layer_error n i s hi hin hs



end Lech.Numerical

namespace Lech.Numerical
 

lemma weighted_error_bound {ι : Type*} [Fintype ι] (b ε σ : ι → ℝ) (A : ℝ)
    (hb : ∀ i, 0 ≤ b i) (hσ : ∀ i, |σ i|=1) (hε : ∀ i, |ε i| ≤ A) :
    |∑ i, σ i*b i*ε i| ≤ A*∑ i,b i := by
  calc
    _  ≤  ∑ i, |σ i*b i*ε i| := Finset.abs_sum_le_sum_abs _ _
    _  ≤  ∑ i, A*b i := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,abs_mul,hσ i,one_mul,abs_of_nonneg (hb i)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hε i) (hb i)
    _ = _ := (Finset.mul_sum _ _ _).symm

lemma layer_zero (n s : ℕ) : layer n 0 s=0 := by simp [layer]

 

theorem from_sum_estimate (n s : ℕ) (hs : 0 < s)
    (b : Fin (n+2) → ℝ) (hb : ∀ i, 0 ≤ b i) (μ L : ℝ) (hμ : 0 ≤ μ)
    (hχ : 0 ≤ (n.factorial:ℝ)*L+μ*∑ i, (-1:ℝ)^i.val*b i*layer n i.val s)
    (halt : ∑ i, (-1:ℝ)^i.val*b i=0) :
    μ*(s:ℝ)^(n+1)*(b 0-
      (2*((n:ℝ)+1)*bound n/(n.factorial:ℝ))/s*∑ i,b i) ≤ L := by
  let E : ℝ := 2*((n:ℝ)+1)*bound n/s
  let N : ℝ := (s:ℝ)^(n+1)
  let c : ℝ := n.factorial
  let ε (i : Fin (n+1)) := layer n i.succ.val s/N-c
  have hN : 0 < N := by dsimp [N]; positivity
  have hc : 0 < c := by dsimp [c]; exact_mod_cast n.factorial_pos
  have hE : 0 ≤ E := by dsimp [E]; positivity [bound_nonneg n]
  have he (i : Fin (n+1)) : |ε i| ≤ E := by
    exact normalized_layer_error n i.succ.val s (by simp only [Fin.val_succ]; omega)
      (by have := i.isLt; simp only [Fin.val_succ]; omega) hs
  have herror := weighted_error_bound (fun i : Fin (n+1) => b i.succ) ε
    (fun i => (-1:ℝ)^i.succ.val) E (fun i => hb i.succ)
    (fun i => by rw [abs_pow]; norm_num) he
  have htail : ∑ i : Fin (n+1), (-1:ℝ)^i.succ.val*b i.succ = -b 0 := by
    rw [Fin.sum_univ_succ] at halt
    simp only [Fin.val_zero,pow_zero,one_mul] at halt
    linarith
  have hbs : (∑ i : Fin (n+1), b i.succ) ≤ ∑ i,b i := by
    conv_rhs => rw [Fin.sum_univ_succ]
    linarith [hb 0]
  have her : (∑ i : Fin (n+1), (-1:ℝ)^i.succ.val*b i.succ*ε i) ≤ E*∑ i,b i :=
    (le_abs_self _).trans (herror.trans (mul_le_mul_of_nonneg_left hbs hE))
  have hlayer (i : Fin (n+1)) : layer n i.succ.val s=N*(c+ε i) := by
    dsimp [ε]
    field_simp
    ring
  have hsumeq : (∑ i : Fin (n+2), (-1:ℝ)^i.val*b i*layer n i.val s)=
      N*((-c*b 0)+(∑ i : Fin (n+1), (-1:ℝ)^i.succ.val*b i.succ*ε i)) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero,layer_zero,mul_zero,zero_add]
    simp_rw [hlayer]
    calc
      _ = N*(c*(∑ i : Fin (n+1), (-1:ℝ)^i.succ.val*b i.succ)+
        ∑ i : Fin (n+1), (-1:ℝ)^i.succ.val*b i.succ*ε i) := by
          rw [mul_add,Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = _ := by rw [htail]; ring
  have hsumle : (∑ i : Fin (n+2), (-1:ℝ)^i.val*b i*layer n i.val s) ≤ 
      N*(-c*b 0+E*∑ i,b i) := by
    rw [hsumeq]
    exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _) her) hN.le
  have hχ' : 0 ≤ c*L+μ*(N*(-c*b 0+E*∑ i,b i)) :=
    hχ.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hsumle hμ))
  have hEeq : E/c=(2*((n:ℝ)+1)*bound n/(n.factorial:ℝ))/s := by
    dsimp [E,c]
    ring
  have h := (mul_le_mul_iff_right₀ hc).mp (show c*(μ*N*(b 0-(E/c)*∑ i,b i)) ≤ c*L by
    have heq : c*(μ*N*(b 0-(E/c)*∑ i,b i))=
        -(μ*(N*(-c*b 0+E*∑ i,b i))) := by
      field_simp
      ring
    rw [heq]
    linarith only [hχ'])
  simpa only [hEeq,N] using h
end Lech.Numerical

namespace Lech.Numerical



theorem uniform_from_sum_estimate (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (s : ℕ), 0 < s → ∀ (b : Fin (n+2) → ℝ),
      (∀ i, 0 ≤ b i) → ∀ (μ L : ℝ), 0 ≤ μ → 0 ≤ L →
      (∑ i, (-1:ℝ)^i.val*b i=0) →
      (GoodRoots n s → 0 ≤ (n.factorial:ℝ)*L+
        μ*∑ i, (-1:ℝ)^i.val*b i*layer n i.val s) →
      μ*(s:ℝ)^(n+1)*(b 0-A/s*∑ i,b i) ≤ L := by
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (roundedRoot_positions n)
  let C : ℝ := 2*((n:ℝ)+1)*bound n/(n.factorial:ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity [bound_nonneg n]
  refine ⟨max C (N:ℝ), hC.trans (le_max_left _ _), ?_⟩
  intro s hs b hb μ L hμ hL halt hχ
  have hs' : 0 < (s:ℝ) := by exact_mod_cast hs
  have hbs : b 0 ≤ ∑ i,b i := Finset.single_le_sum (fun i _ => hb i) (Finset.mem_univ 0)
  have hB : 0 ≤ ∑ i,b i := Finset.sum_nonneg (fun i _ => hb i)
  by_cases hsN : N ≤ s
  · have hh : GoodRoots n s := hN s hsN
    have hmain := from_sum_estimate n s hs b hb μ L hμ (hχ hh) halt
    apply le_trans ?_ hmain
    apply mul_le_mul_of_nonneg_left ?_ (mul_nonneg hμ (pow_nonneg hs'.le _))
    apply sub_le_sub_left
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (le_max_left C (N:ℝ)) hs'.le) hB
  · have hNs : (s:ℝ) ≤ (N:ℝ) := by exact_mod_cast (le_of_lt (Nat.lt_of_not_ge hsN))
    have hsA : (s:ℝ) ≤ max C (N:ℝ) := hNs.trans (le_max_right _ _)
    have hA : 1 ≤ max C (N:ℝ)/(s:ℝ) := (le_div_iff₀ hs').mpr (by simpa using hsA)
    have hbr : b 0-max C (N:ℝ)/(s:ℝ)*∑ i,b i ≤ 0 := by
      have := mul_le_mul_of_nonneg_right hA hB
      simp only [one_mul] at this
      linarith
    exact (mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hμ (pow_nonneg hs'.le _)) hbr).trans hL
end Lech.Numerical

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootStripComplement
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProductSourceCover
open scoped BigOperators

lemma signed_reverse (h : ℕ) (b : ℤ → ℝ) (f : ℕ → ℝ) :
    (-1:ℝ)^h*(∑ k∈Finset.range (h+1),(-1:ℝ)^k*b (-(h:ℤ)+k)*f (h-k))=
      ∑ i∈Finset.range (h+1),(-1:ℝ)^i*b (-(i:ℤ))*f i := by
  rw [Finset.mul_sum,←Finset.sum_range_reflect
    (fun i => (-1:ℝ)^i*b (-(i:ℤ))*f i) (h+1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k≤h := by have := Finset.mem_range.mp hk; omega
  have he : h+1-1-k=h-k := by omega
  rw [he]
  have hp : -(h:ℤ)+(k:ℤ) = -((h-k:ℕ):ℤ) := by omega
  have hs : (-1:ℝ)^h*(-1:ℝ)^k=(-1:ℝ)^(h-k) := by
    conv_lhs => rw [show h=(h-k)+k by omega,pow_add]
    have hsq : (-1:ℝ)^k*(-1:ℝ)^k=1 := by rw [←mul_pow]; norm_num
    rw [mul_assoc,hsq,mul_one]
  rw [hp,←mul_assoc,←mul_assoc,hs]

end Lech.ProductSourceCover

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ComplexEstimate
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover
universe u


lemma rank_zero_reverse (h : ℕ) (b : ℤ → ℕ)
    (hb : ∑ i∈Finset.range (h+1),(-1:ℝ)^i*(b (-(i:ℤ)):ℝ)=0) :
    ∑ k∈Finset.range (h+1),(-1:ℝ)^k*(b (-(h:ℤ)+k):ℝ)=0 := by
  have he := signed_reverse h (fun p => (b p:ℝ)) (fun _=>1)
  simp only [mul_one,hb] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ (by norm_num))

 

theorem complex_estimate_basis (n : ℕ) [LinearOrder (Chart n)] :
    ∃ A : ℝ,0≤A ∧ ∀ {R : Type u} [CommRing R] [Nontrivial R]
      (I : Ideal R) (z : Fin (n+1) → R)
      (_hgen : Ideal.span (Set.range z)=I)
      (ell : TorsionLength I) (_hds : ell.DirectSumZero)
      (_hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
      (_ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
        (R ⧸ Ideal.span (Set.range (fun j => z j^a))))=
          a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
      (_hK : ∀ a : ℕ,1≤a → ∀ i : ℤ,i<0 →
        ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
      (F : CochainComplex (ModuleCat.{u} R) ℤ)
      (b : ℤ → ℕ) (_B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
      (_hb : ∀ p,p < -(n+1:ℤ) ∨ 0<p → IsZero (F.X p))
      (_hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic),
        (∀ i,powerTorsion I (F.homology i) ∧ ell.value (F.homology i)≠⊤) ∧
        (∀ i : ℤ,i≠0 → ell.value (F.homology i)=0) ∧
        ∀ s : ℕ,0 < s →
          (∀ p : ℤ,(F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1)))) →
          (∑ i∈Finset.range (n+2),(-1:ℝ)^i*(b (-(i:ℤ)):ℝ)=0) →
          ell.realValue (ModuleCat.of R (R ⧸ I))*(s:ℝ)^(n+1)*
            ((b 0:ℝ)-A/s*∑ i∈Finset.range (n+2),(b (-(i:ℤ)):ℝ))≤
              ell.realValue (F.homology 0) := by
  obtain ⟨A,hA,hest⟩ := Numerical.uniform_from_sum_estimate n
  refine ⟨A,hA,?_⟩
  intro R _ _ I z hgen ell hds hmu ha hK F b B hb hac
  have hf : ∀ p,Module.Free R (F.X p) := fun p => Module.Free.of_basis (B p)
  have hfin : ∀ p,Module.Finite R (F.X p) := fun p => Module.Finite.of_basis (B p)
  have hz : ∀ j,z j∈I := fun j => hgen ▸ Ideal.subset_span ⟨j,rfl⟩
  have hbf : ∀ p,p < -((n+1:ℕ):ℤ) ∨ 0<p → IsZero (F.X p) := by
    simpa only [Nat.cast_add,Nat.cast_one] using hb
  have hpure := SourceGraded.acyclicity_finite_torsion I z hgen ell F hmu ha hK hf hfin hbf hac
  refine ⟨hpure.1,hpure.2,?_⟩
  intro s hs hd halt
  have hbr := rank_zero_reverse (n+1) b halt
  simp only [Nat.cast_add,Nat.cast_one] at hbr
  have H := hest s hs (fun i => (b (-(i.val:ℤ)):ℝ)) (fun _ => Nat.cast_nonneg _)
    (ell.realValue (ModuleCat.of R (R ⧸ I))) (ell.realValue (F.homology 0))
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have halt' : (∑ i : Fin (n+2),(-1:ℝ)^i.val*(b (-(i.val:ℤ)):ℝ))=0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (-1:ℝ)^i*(b (-(i:ℤ)):ℝ)) (n+2)]
    exact halt
  have he : (∑ i : Fin (n+2),(b (-(i.val:ℤ)):ℝ))=
      ∑ i∈Finset.range (n+2),(b (-(i:ℤ)):ℝ) :=
    Fin.sum_univ_eq_sum_range (fun i => (b (-(i:ℤ)):ℝ)) (n+2)
  apply (show _ from H halt' ?_) |> fun hh => by simpa only [Fin.val_zero,Nat.cast_zero,neg_zero,he] using hh
  intro hr
  have hr' : RootPositions n s (Numerical.roundedRoot n s) := by
    intro j
    constructor
    · exact_mod_cast (hr j).1
    · exact_mod_cast (hr j).2
  have ht := ReesRoot.sum_estimate I z hz hgen ell hds hmu ha hK F s hd b B hf hfin hb hac hbr
    (Numerical.roundedRoot n s) hr'
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1:ℝ)^i*(b (-(i:ℤ)):ℝ)*Numerical.layer n i s) (n+2)]
  exact ht
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ComplexEstimateAllModule
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Lech.ProductSourceCover
open scoped ENNReal
namespace Lech
universe u
 

theorem complex_estimate_allModule_oai (d : ℕ) (hd : 0<d) :
    ∃ A : ℝ,0≤A ∧ ∀ {C : Type u} [CommRing C] [Nontrivial C]
      (z : Fin d → C) (ell : AllModuleLength C) (e : ℝ) (_he : 0≤e)
      (_hmu : ell.value (ModuleCat.of C (C ⧸ Ideal.span (Set.range z))) = ENNReal.ofReal e)
      (_ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of C
        (C ⧸ Ideal.span (Set.range (fun j => z j^a)))) = (a:ℝ≥0∞)^d*ENNReal.ofReal e)
      (_hK : ∀ a : ℕ,1≤a → ∀ i : ℤ,i < 0 →
        ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
      (F : CochainComplex (ModuleCat.{u} C) ℤ)
      (_hf : ∀ i,Module.Free C (F.X i)) (_hfin : ∀ i,Module.Finite C (F.X i))
      (_hb : ∀ i,i < -(d:ℤ) ∨ 0 < i → IsZero (F.X i))
      (_hac : ∀ j,(((baseChangeFunctor C (Localization.Away (z j))).mapHomologicalComplex _).obj F).Acyclic)
      (s : ℕ) (_hs : 0 < s)
      (_hδ : ∀ i : ℤ,(F.d i (i+1)).hom.range ≤
        (Ideal.span (Set.range z))^s • (⊤ : Submodule C (F.X (i+1))))
      (_halt : ∑ i∈Finset.range (d+1),(-1:ℝ)^i*(Module.finrank C (F.X (-(i:ℤ))):ℝ)=0),
      e*(s:ℝ)^d*((Module.finrank C (F.X 0):ℝ)-A/s*
        ∑ i∈Finset.range (d+1),(Module.finrank C (F.X (-(i:ℤ))):ℝ)) ≤
          (ell.value (F.homology 0)).toReal := by
  classical
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  let : LinearOrder (Chart n) := LinearOrder.lift' (Fintype.equivFin (Chart n))
    (Fintype.equivFin (Chart n)).injective
  obtain ⟨A,hA,H⟩ := complex_estimate_basis n
  refine ⟨A,hA,?_⟩
  intro C _ _ z ell e he hmu ha hK F hf hfin hb hac s hs hδ halt
  let I := Ideal.span (Set.range z)
  let l := ell.torsionLength I
  let b : ℤ → ℕ := fun i => Module.finrank C (F.X i)
  let B : ∀ i,Module.Basis (Fin (b i)) C (F.X i) := fun i => by
    letI := hf i
    letI := hfin i
    exact Module.finBasis C (F.X i)
  have hds : l.DirectSumZero := fun M _ _ _ _ hh => ell.directSum_zero M hh
  have hlmu : l.value (ModuleCat.of C (C ⧸ I)) ≠ ⊤ := by
    change ell.value _ ≠ ⊤
    rw [hmu]
    exact ENNReal.ofReal_ne_top
  have hla (a : ℕ) (ha0 : 0<a) : l.value (ModuleCat.of C
      (C ⧸ Ideal.span (Set.range (fun j => z j^a)))) =
        a^(n+1) • l.value (ModuleCat.of C (C ⧸ I)) := by
    change ell.value _ = a^(n+1) • ell.value _
    rw [ha a ha0,hmu]
    simp only [nsmul_eq_mul,Nat.cast_pow]
  have H' := (H I z rfl l hds hlmu hla hK F b B (by
    simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_succ] using hb) hac).2.2 s hs hδ halt
  change (ell.value (ModuleCat.of C (C ⧸ I))).toReal * _ * _ ≤ _ at H'
  rw [hmu,ENNReal.toReal_ofReal he] at H'
  exact H'
end Lech

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.complex_estimate_allModule_oai.{u} := @OAI.Lech.complex_estimate_allModule_oai.{u}
