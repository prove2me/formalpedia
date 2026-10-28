-- Prove2me | solution 1 for OAI.LargePrimeGaps.unorderedWeight_internal_marked_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T05:02:01.297654+00:00
-- url     : https://prove2.me/submissions/54158bad-9f0f-41d4-b1e7-24f17803ac9e

import Mathlib
import Definitions.Def_OAIW2PG000
import Theorems.Thm_OAI_LargePrimeGaps_marked_average_uniform_asymptotic

section
-- module Solutions.OAIW2_P344.Compat
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_Indices
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

theorem log_pos_of_two_le {X : ℕ} (hX : 2 ≤ X) : 0 < Real.log (X : ℝ) :=
  Real.log_pos (by exact_mod_cast (show 1 < X by omega))

open Filter

theorem blockLength_le_mul_log {lam : ℝ} (hlam : 0 ≤ lam) {X : ℕ} (hX : 2 ≤ X) :
    (blockLength lam X : ℝ) ≤ lam * Real.log (X : ℝ) :=
  Nat.floor_le (mul_nonneg hlam (log_pos_of_two_le hX).le)

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_DivisorSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

theorem logCoordinates_nonneg {ι : Type*} {X : ℕ} (hX : 2 ≤ X)
    {d : ι → ℕ} (hd : ∀ i, 0 < d i) (i : ι) : 0 ≤ logCoordinates X d i := by
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hd i)) (log_pos_of_two_le hX).le

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_OrthantIntegrals
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

theorem deleteCoordinate_eq_orthant_integral {j : ℕ} {f : (Fin (j+1) → ℝ) → ℝ}
    (hf : Function.support f ⊆ {t | ∀ i, 0 < t i}) (t : Fin j → ℝ) :
    deleteCoordinate f t = ∫ u in Ici (0:ℝ), f (Fin.snoc t u) := by
  unfold deleteCoordinate
  rw [← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hu : u ∈ Ici (0:ℝ)
  · rw [Set.indicator_of_mem hu]
  · rw [Set.indicator_of_notMem hu]
    by_contra hn
    apply hu
    change 0 ≤ u
    simpa only [Fin.snoc_last] using (hf hn (Fin.last j)).le

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_SingularSeries
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

theorem residueCount_le_card (H : Finset ℤ) (p : ℕ) : residueCount H p ≤ H.card :=
  Finset.card_image_le

theorem bernoulli_second_order (s : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ (1-u)^s - (1-(s:ℝ)*u) ∧
    (1-u)^s - (1-(s:ℝ)*u) ≤ (s:ℝ)^2*u^2 := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hid : (1-u)^(s+1) - (1-((s+1:ℕ):ℝ)*u) =
        (1-u)*((1-u)^s-(1-(s:ℝ)*u))+(s:ℝ)*u^2 := by
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      ring
    rw [hid]
    constructor
    · exact add_nonneg (mul_nonneg (by linarith) ih.1) (by positivity)
    · have hh := mul_le_mul_of_nonneg_left ih.2 (by linarith : 0≤1-u)
      have hpos : 0 ≤ (s:ℝ)^2*u^2 := by positivity
      have hsm : (1-u)*((s:ℝ)^2*u^2) ≤ (s:ℝ)^2*u^2 := by nlinarith
      push_cast
      nlinarith [sq_nonneg u, Nat.cast_nonneg (α:=ℝ) s]

theorem generic_local_error (s : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    |(1-(s:ℝ)/(p:ℝ))/(1-1/(p:ℝ))^s - 1| ≤
      ((s:ℝ)^2 * (2:ℝ)^s) / (p:ℝ)^2 := by
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hp0 : (0:ℝ)<p := by linarith
  have hu0 : 0 ≤ (1:ℝ)/p := by positivity
  have hu1 : (1:ℝ)/p ≤ 1/2 := (one_div_le_one_div_of_le (by norm_num) hpR)
  have hs := bernoulli_second_order s hu0 (by linarith)
  have hm : (s:ℝ)*(1/(p:ℝ))=(s:ℝ)/(p:ℝ) := by ring
  rw [hm] at hs
  have hd0 : 0 < (1-(1:ℝ)/p)^s := pow_pos (by linarith) _
  have hdp : (1/2:ℝ)^s ≤ (1-1/(p:ℝ))^s :=
    pow_le_pow_left₀ (by norm_num) (by linarith) s
  have hnum : (1-(s:ℝ)/(p:ℝ))/(1-1/(p:ℝ))^s ≤ 1 := by
    apply (div_le_one hd0).mpr
    nlinarith [hs.1]
  rw [abs_of_nonpos (by linarith : (1-(s:ℝ)/(p:ℝ))/(1-1/(p:ℝ))^s-1≤0)]
  calc
    _ = ((1-1/(p:ℝ))^s - (1-(s:ℝ)/(p:ℝ))) / (1-1/(p:ℝ))^s := by simp only [sub_div, div_self hd0.ne']; ring
    _ ≤ ((s:ℝ)^2 * (1/(p:ℝ))^2) / (1-1/(p:ℝ))^s := by
      apply div_le_div_of_nonneg_right _ hd0.le
      exact hs.2
    _ ≤ ((s:ℝ)^2 * (1/(p:ℝ))^2) / (1/2:ℝ)^s :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hdp
    _ = _ := by simp only [div_pow, one_pow]; field_simp

theorem differenceProduct_pos (H : Finset ℤ) : 0 < differenceProduct H := by
  classical
  apply Finset.prod_pos
  intro a _
  apply Finset.prod_pos
  intro b hb
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  exact Int.natAbs_pos.mpr (sub_ne_zero.mpr hba.symm)

theorem prime_dvd_differenceProduct_of_collision {H : Finset ℤ} {p : ℕ}
    {a b : ℤ} (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b)
    (hmod : a % (p:ℤ) = b % (p:ℤ)) : p ∣ differenceProduct H := by
  have hd : (p:ℤ) ∣ a-b := Int.dvd_of_emod_eq_zero
    (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hmod)
  have hdN : p ∣ (a-b).natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  exact hdN.trans ((Finset.dvd_prod_of_mem (fun b => (a-b).natAbs)
    (Finset.mem_erase.mpr ⟨hab.symm, hb⟩)).trans
    (Finset.dvd_prod_of_mem (fun a => ∏ b ∈ H.erase a, (a-b).natAbs) ha))

theorem residueCount_eq_card_of_not_dvd (H : Finset ℤ) {p : ℕ}
    (hp : ¬p ∣ differenceProduct H) : residueCount H p = H.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  by_contra hne
  exact hp (prime_dvd_differenceProduct_of_collision ha hb hne hab)

theorem differenceProduct_le (H : Finset ℤ) {M : ℕ}
    (hM : ∀ a ∈ H, ∀ b ∈ H, (a-b).natAbs ≤ M) :
    differenceProduct H ≤ M^(H.card*(H.card-1)) := by
  classical
  calc
    _ ≤ ∏ a ∈ H, M^(H.card-1) := by
      apply Finset.prod_le_prod'
      intro a ha
      calc
        _ ≤ ∏ _b ∈ H.erase a, M := Finset.prod_le_prod' fun b hb =>
          hM a ha b (Finset.mem_erase.mp hb).2
        _ = _ := by simp [Finset.card_erase_of_mem ha]
    _ = _ := by simp [← pow_mul, Nat.mul_comm]

theorem abs_log_le_two_abs_sub_one {x : ℝ} (hx : 1/2 ≤ x) :
    |Real.log x| ≤ 2*|x-1| := by
  have hx0 : 0<x := by linarith
  by_cases hx1 : 1 ≤ x
  · rw [abs_of_nonneg (Real.log_nonneg hx1), abs_of_nonneg (by linarith)]
    linarith [Real.log_le_sub_one_of_pos hx0]
  · have hx1' : x ≤ 1 := le_of_not_ge hx1
    rw [abs_of_nonpos (Real.log_nonpos hx0.le hx1'), abs_of_nonpos (by linarith)]
    have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hx0)
    rw [Real.log_inv] at hh
    have hi : x⁻¹-1 ≤ 2*(1-x) := by
      have hh : (1:ℝ) / x ≤ 2*(1-x)+1 := (div_le_iff₀ hx0).mpr (by nlinarith)
      simpa only [one_div] using (sub_le_iff_le_add).mpr hh
    linarith

theorem abs_log_one_sub_le {u : ℝ} (hu0 : 0≤u) (hu1 : u≤1/2) :
    |Real.log (1-u)| ≤ 2*u := by
  have hh := abs_log_le_two_abs_sub_one (x:=1-u) (by linarith)
  simpa only [sub_sub_cancel_left, abs_neg, abs_of_nonneg hu0] using hh

theorem singularLocal_ge_half (H : Finset ℤ) {p : ℕ} (hp : 2 ≤ p)
    (hps : 2 * H.card ≤ p) : 1/2 ≤ singularLocal H p := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have hs : (2:ℝ)*H.card ≤ p := by exact_mod_cast hps
  have hn : (residueCount H p:ℝ) ≤ H.card := by exact_mod_cast residueCount_le_card H p
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hd0 : 0 ≤ 1-(1:ℝ)/p := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hpR
    linarith
  have hd1 : 1-(1:ℝ)/p ≤ 1 := sub_le_self _ (by positivity)
  have hpow : (1-(1:ℝ)/p)^H.card ≤ 1 := pow_le_one₀ hd0 hd1
  have hn0 : 1/2 ≤ 1-(residueCount H p:ℝ)/p := by
    have hh : (residueCount H p:ℝ)/p ≤ 1/2 := (div_le_iff₀ hp0).mpr (by linarith)
    linarith
  unfold singularLocal
  have hdpos : 0 < 1-(1:ℝ)/p := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hpR
    linarith
  exact hn0.trans (le_div_self (by linarith) (pow_pos hdpos _) hpow)

theorem singularLocal_log_generic (H : Finset ℤ) {p : ℕ} (hp : 2 ≤ p)
    (hps : 2*H.card ≤ p) (hdiv : ¬p ∣ differenceProduct H) :
    |Real.log (singularLocal H p)| ≤
      2*((H.card:ℝ)^2*(2:ℝ)^H.card)/(p:ℝ)^2 := by
  have h1 := abs_log_le_two_abs_sub_one (singularLocal_ge_half H hp hps)
  have h2 : |singularLocal H p-1| ≤ ((H.card:ℝ)^2*(2:ℝ)^H.card)/(p:ℝ)^2 := by
    simpa only [singularLocal, residueCount_eq_card_of_not_dvd H hdiv] using
      generic_local_error H.card hp
  calc
    _ ≤ 2*|singularLocal H p-1| := h1
    _ ≤ 2*(((H.card:ℝ)^2*(2:ℝ)^H.card)/(p:ℝ)^2) := by gcongr
    _ = _ := by ring

theorem singularLocal_log_bound (H : Finset ℤ) {p : ℕ} (hp : 2 ≤ p)
    (hps : 2*H.card ≤ p) :
    |Real.log (singularLocal H p)| ≤ 4*(H.card:ℝ)/(p:ℝ) := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hs : (2:ℝ)*H.card ≤ p := by exact_mod_cast hps
  have hn : (residueCount H p:ℝ) ≤ H.card := by exact_mod_cast residueCount_le_card H p
  have hn0 : 0 ≤ (residueCount H p:ℝ)/p := by positivity
  have hn1 : (residueCount H p:ℝ)/p ≤ 1/2 := (div_le_iff₀ hp0).mpr (by linarith)
  have hq1 : (1:ℝ)/p ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hpR
  have hlog1 := abs_log_one_sub_le hn0 hn1
  have hlog2 := abs_log_one_sub_le (by positivity : 0≤(1:ℝ)/p) hq1
  rw [singularLocal, Real.log_div (by linarith : (1-(residueCount H p:ℝ)/p) ≠ 0)
    (pow_ne_zero _ (by linarith : (1-(1:ℝ)/p) ≠ 0)), Real.log_pow]
  calc
    _ ≤ |Real.log (1-(residueCount H p:ℝ)/p)| +
          |(H.card:ℝ)*Real.log (1-(1:ℝ)/p)| := abs_sub _ _
    _ = |Real.log (1-(residueCount H p:ℝ)/p)| +
          (H.card:ℝ)*|Real.log (1-(1:ℝ)/p)| := by rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ H.card from Nat.cast_nonneg _)]
    _ ≤ 2*((residueCount H p:ℝ)/p) + (H.card:ℝ)*(2*((1:ℝ)/p)) := by gcongr
    _ ≤ _ := by
      have hh := div_le_div_of_nonneg_right hn hp0.le
      calc
        _ ≤ 2*((H.card:ℝ)/p) + (H.card:ℝ)*(2*((1:ℝ)/p)) := by gcongr
        _ = _ := by ring

theorem sum_reciprocal_sq_le {S : Finset ℕ} {y : ℕ} (hy : 0 < y)
    (hS : ∀ n ∈ S, y < n) : (∑ n ∈ S, (1:ℝ)/(n:ℝ)^2) ≤ 1/(y:ℝ) := by
  classical
  by_cases hempty : S = ∅
  · subst S
    simp
  let N := S.sup id
  have hsub : S ⊆ Finset.Ico y (N+1) := by
    intro n hn
    exact Finset.mem_Ico.mpr ⟨(hS n hn).le, Nat.lt_succ_iff.mpr (Finset.le_sup (f:=id) hn)⟩
  have hN : y ≤ N+1 := by
    obtain ⟨n, hn⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    exact (Finset.mem_Ico.mp (hsub hn)).1.trans (Finset.mem_Ico.mp (hsub hn)).2.le
  have htel : (∑ n ∈ Finset.Ico y (N+1), ((1:ℝ)/(n:ℝ)-1/((n:ℝ)+1))) =
      1/(y:ℝ)-1/(N+1:ℕ) := by
    rw [Finset.sum_Ico_eq_sub _ hN]
    have hh (k : ℕ) : (∑ n ∈ Finset.range k, ((1:ℝ)/(n:ℝ)-1/((n:ℝ)+1))) =
        (1:ℝ)/(0:ℕ)-1/(k:ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        Finset.sum_range_sub' (fun n : ℕ => (1:ℝ)/(n:ℝ)) k
    rw [hh, hh]
    ring
  have hstep (n : ℕ) (hn : y < n) :
      (1:ℝ)/(n:ℝ)^2 ≤ (1:ℝ)/((n:ℝ)-1)-1/(n:ℝ) := by
    have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    have hid : (1:ℝ)/((n:ℝ)-1)-1/(n:ℝ) = 1/((n:ℝ)*((n:ℝ)-1)) := by
      field_simp [show (n:ℝ) ≠ 0 by linarith, show (n:ℝ)-1 ≠ 0 by linarith]
      ring
    rw [hid]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith

  let T := S.image (fun n => n-1)
  have hi : Set.InjOn (fun n : ℕ => n-1) ↑S := by
    intro n hn m hm he
    have := hS n hn
    have := hS m hm
    change n-1=m-1 at he
    omega
  have he : (∑ n ∈ S, ((1:ℝ)/((n:ℝ)-1)-1/(n:ℝ))) =
      ∑ n ∈ T, ((1:ℝ)/(n:ℝ)-1/((n:ℝ)+1)) := by
    rw [Finset.sum_image hi]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Nat.cast_sub (by have := hS n hn; omega), Nat.cast_one]
    congr 2
    ring
  calc
    _ ≤ ∑ n ∈ S, ((1:ℝ)/((n:ℝ)-1)-1/(n:ℝ)) :=
      Finset.sum_le_sum fun n hn => hstep n (hS n hn)
    _ = _ := he
    _ ≤ ∑ n ∈ Finset.Ico y (N+1), ((1:ℝ)/(n:ℝ)-1/((n:ℝ)+1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
        have := hS n hn
        have hsup : n ≤ N := Finset.le_sup (f:=id) hn
        simp only [Finset.mem_Ico]
        change y ≤ n-1 ∧ n-1<N+1
        omega
      · intro n hn _
        have hn0 : (0:ℝ)<n := by exact_mod_cast (hy.trans_le (Finset.mem_Ico.mp hn).1)
        exact sub_nonneg.mpr (one_div_le_one_div_of_le hn0 (by linarith))
    _ = 1/(y:ℝ)-1/(N+1:ℕ) := htel
    _ ≤ _ := sub_le_self _ (by positivity)

theorem prime_divisor_reciprocal_sum_le {D y : ℕ} (hD : 0 < D) (hy : 1 < y)
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p ∧ y < p ∧ p ∣ D) :
    (∑ p ∈ S, (1:ℝ)/(p:ℝ)) ≤ Real.log D / ((y:ℝ)*Real.log y) := by
  have hy0 : (0:ℝ)<y := by exact_mod_cast (show 0<y by omega)
  have hy1 : (1:ℝ)<y := by exact_mod_cast hy
  have hlogy : 0 < Real.log (y:ℝ) := Real.log_pos hy1
  have hsub : S ⊆ D.primeFactors := fun p hp =>
    Nat.mem_primeFactors.mpr ⟨(hS p hp).1, (hS p hp).2.2, hD.ne'⟩
  have hprod : (∏ p ∈ S, p) ≤ D := Nat.le_of_dvd hD
    ((Finset.prod_dvd_prod_of_subset S D.primeFactors id hsub).trans (Nat.prod_primeFactors_dvd D))
  have hprodpos : (0:ℝ) < ∏ p ∈ S, (p:ℝ) := Finset.prod_pos fun p hp => by
    exact_mod_cast (hS p hp).1.pos
  have hlogs : (∑ p ∈ S, Real.log (p:ℝ)) ≤ Real.log D := by
    rw [← Real.log_prod (s:=S) (f:=fun p : ℕ => (p:ℝ))
      (fun p hp => (ne_of_gt (by exact_mod_cast (hS p hp).1.pos : (0:ℝ)<p)))]
    exact Real.log_le_log hprodpos (by
      simpa only [Nat.cast_prod] using (show ((∏ p ∈ S, p : ℕ):ℝ) ≤ (D:ℝ) by exact_mod_cast hprod))
  calc
    _ ≤ ∑ p ∈ S, Real.log (p:ℝ) / ((y:ℝ)*Real.log y) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpy : (y:ℝ)≤p := by exact_mod_cast (hS p hp).2.1.le
      have hlogp := Real.log_le_log hy0 hpy
      calc
        _ ≤ 1/(y:ℝ) := one_div_le_one_div_of_le hy0 hpy
        _ = Real.log (y:ℝ)/((y:ℝ)*Real.log y) := by field_simp
        _ ≤ _ := div_le_div_of_nonneg_right hlogp (by positivity)
    _ = (∑ p ∈ S, Real.log (p:ℝ))/((y:ℝ)*Real.log y) := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right hlogs (by positivity)

theorem singularLocal_log_sum_bound (H : Finset ℤ) {y : ℕ} (hy : 1<y)
    (hys : 2*H.card ≤ y) (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ y < p) :
    (∑ p ∈ S, |Real.log (singularLocal H p)|) ≤ singularTailBound H y := by
  classical
  let K : ℝ := 2*((H.card:ℝ)^2*(2:ℝ)^H.card)
  have hK : 0≤K := by dsimp [K]; positivity
  have hsum : (∑ p ∈ S, |Real.log (singularLocal H p)|) ≤
      (∑ p ∈ S, K*(1/(p:ℝ)^2)) +
      ∑ p ∈ S.filter (fun p => p ∣ differenceProduct H), 4*(H.card:ℝ)*(1/(p:ℝ)) := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    by_cases hd : p ∣ differenceProduct H
    · simp only [hd, ite_true]
      have hh := singularLocal_log_bound H (hS p hp).1.two_le (hys.trans (hS p hp).2.le)
      calc
        _ ≤ 4*(H.card:ℝ)/(p:ℝ) := hh
        _ ≤ K*(1/(p:ℝ)^2) + 4*(H.card:ℝ)*(1/(p:ℝ)) := by
          have h0 : 0≤K*(1/(p:ℝ)^2) := by positivity
          simpa only [mul_one_div] using
            (le_add_of_nonneg_left h0 : 4*(H.card:ℝ)*(1/(p:ℝ)) ≤
              K*(1/(p:ℝ)^2) + 4*(H.card:ℝ)*(1/(p:ℝ)))
    · simp only [hd, ite_false, add_zero]
      simpa only [K, mul_one_div] using
        singularLocal_log_generic H (hS p hp).1.two_le (hys.trans (hS p hp).2.le) hd
  have hinv := sum_reciprocal_sq_le (show 0<y by omega) (fun p hp => (hS p hp).2)
  have hdiv := prime_divisor_reciprocal_sum_le (differenceProduct_pos H) hy
    (S.filter (fun p => p ∣ differenceProduct H)) (by
      intro p hp
      obtain ⟨hpS, hd⟩ := Finset.mem_filter.mp hp
      exact ⟨(hS p hpS).1, (hS p hpS).2, hd⟩)
  calc
    _ ≤ _ := hsum
    _ = K*(∑ p ∈ S, 1/(p:ℝ)^2) +
        4*(H.card:ℝ)*(∑ p ∈ S.filter (fun p => p ∣ differenceProduct H), 1/(p:ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ K*(1/(y:ℝ)) + 4*(H.card:ℝ)*(Real.log (differenceProduct H)/((y:ℝ)*Real.log y)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hinv hK)
        (mul_le_mul_of_nonneg_left hdiv (by positivity))
    _ = _ := by unfold singularTailBound K; ring

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_SingularTails
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

theorem singularTailFactor_pos (H : Finset ℤ) {y : ℕ} (hys : 2*H.card ≤ y) (p : ℕ) :
    0 < singularTailFactor H y p := by
  unfold singularTailFactor
  split_ifs with h
  · have hh := singularLocal_ge_half H h.1.two_le (hys.trans h.2.le)
    linarith
  · norm_num

theorem singularTail_log_summable_bound (H : Finset ℤ) {y : ℕ} (hy : 1<y)
    (hys : 2*H.card ≤ y) :
    Summable (fun p : ℕ => Real.log (singularTailFactor H y p)) ∧
    |∑' p : ℕ, Real.log (singularTailFactor H y p)| ≤ singularTailBound H y := by
  have hfin (S : Finset ℕ) :
      (∑ p ∈ S, |Real.log (singularTailFactor H y p)|) ≤ singularTailBound H y := by
    have hh := singularLocal_log_sum_bound H hy hys (S.filter (fun p => p.Prime ∧ y<p))
      (fun p hp => (Finset.mem_filter.mp hp).2)
    simpa only [Finset.sum_filter, singularTailFactor, apply_ite Real.log,
      Real.log_one, apply_ite abs, abs_zero] using hh
  have hs := summable_of_sum_le (fun p => abs_nonneg (Real.log (singularTailFactor H y p))) hfin
  refine ⟨summable_abs_iff.mp hs, ?_⟩
  calc
    _ ≤ ∑' p : ℕ, |Real.log (singularTailFactor H y p)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f:=fun p : ℕ => Real.log (singularTailFactor H y p)) (by
        simpa only [Real.norm_eq_abs] using hs)
    _ ≤ _ := hs.tsum_le_of_sum_le hfin

theorem singularTail_pos_and_log_bound (H : Finset ℤ) {y : ℕ} (hy : 1<y)
    (hys : 2*H.card ≤ y) :
    0 < singularTail H y ∧ |Real.log (singularTail H y)| ≤ singularTailBound H y := by
  have hs := singularTail_log_summable_bound H hy hys
  have he : singularTail H y = Real.exp (∑' p : ℕ, Real.log (singularTailFactor H y p)) :=
    (Real.rexp_tsum_eq_tprod (singularTailFactor_pos H hys) hs.1).symm
  rw [he, Real.log_exp]
  exact ⟨Real.exp_pos _, hs.2⟩

theorem singularTail_error (H : Finset ℤ) {y : ℕ} (hy : 1<y)
    (hys : 2*H.card ≤ y) (hsmall : singularTailBound H y ≤ 1) :
    |singularTail H y - 1| ≤ 2*singularTailBound H y := by
  obtain ⟨hpos, hlog⟩ := singularTail_pos_and_log_bound H hy hys
  have he := Real.abs_exp_sub_one_le (hlog.trans hsmall)
  rw [Real.exp_log hpos] at he
  exact he.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))

theorem singularSeries_eq_truncation_mul_tail (H : Finset ℤ) {y : ℕ} (hy : 1<y)
    (hys : 2*H.card ≤ y) :
    singularSeries H = singularTruncation H y * singularTail H y := by
  classical
  let head : ℕ → ℝ := fun p => if p ∈ Nat.primesLE y then singularLocal H p else 1
  have hh : HasProd head (singularTruncation H y) := by
    have hh : HasProd head (∏ p ∈ Nat.primesLE y, head p) :=
      hasProd_prod_of_ne_finset_one (s:=Nat.primesLE y) (f:=head)
      (fun p hp => ite_eq_right hp)
    simpa only [head, singularTruncation, Finset.prod_ite_mem, Finset.inter_self] using hh
  have ht := Real.hasProd_of_hasSum_log (singularTailFactor_pos H hys)
    (singularTail_log_summable_bound H hy hys).1.hasSum
  have hp : (fun p => head p * singularTailFactor H y p) =
      (fun p : ℕ => if p.Prime then singularLocal H p else 1) := by
    funext p
    simp only [head, singularTailFactor, Nat.mem_primesLE]
    split_ifs <;> first | omega | simp_all
  have htt : HasProd (singularTailFactor H y) (singularTail H y) := by
    simpa only [singularTail, ← ht.tprod_eq] using ht
  have hfull := hh.mul htt
  rw [hp] at hfull
  simpa only [singularSeries, Nat.Primes.tprod_eq_tprod_ite] using hfull.tprod_eq

theorem unit_indicator_sum (q : ℕ) [NeZero q] :
    (∑ x : ZMod q, if IsUnit x then (1:ℝ) else 0) = (q.totient:ℝ) := by
  classical
  have he : (Finset.univ.filter fun x : ZMod q => IsUnit x) =
      Finset.univ.image (fun x : (ZMod q)ˣ => (x:ZMod q)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    change IsUnit x ↔ ∃ u : (ZMod q)ˣ, (u:ZMod q) = x
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨u, hu⟩
    · rintro ⟨u, rfl⟩
      exact u.isUnit
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, he]
  rw [Finset.card_image_of_injective _ Units.val_injective, Finset.card_univ,
    ZMod.card_units_eq_totient]

theorem shifted_unit_indicator_sum {q : ℕ} [NeZero q] (x : ZMod q) :
    (∑ a : ZMod q, if IsUnit (x-a) then (1:ℝ) else 0) = (q.totient:ℝ) := by
  classical
  have hh := (Equiv.subLeft x).sum_comp (fun a : ZMod q => if IsUnit a then (1:ℝ) else 0)
  exact hh.trans (unit_indicator_sum q)

theorem siftedCount_sum (s q : ℕ) [NeZero q] :
    (∑ a : Fin s → ZMod q, siftedCount a) = (q:ℝ)*(q.totient:ℝ)^s := by
  classical
  unfold siftedCount
  rw [Finset.sum_comm]
  have hf (x : ZMod q) :
      (∑ a : Fin s → ZMod q, ∏ i : Fin s, if IsUnit (x-a i) then (1:ℝ) else 0) =
      (q.totient:ℝ)^s := by
    calc
      _ = ∏ _i : Fin s, ∑ b : ZMod q, if IsUnit (x-b) then (1:ℝ) else 0 :=
        (Fintype.prod_sum (fun (_i : Fin s) (b : ZMod q) =>
          if IsUnit (x-b) then (1:ℝ) else 0)).symm
      _ = _ := by simp only [shifted_unit_indicator_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [hf]
  simp

theorem normalizedSiftedCount_sum (s q : ℕ) [NeZero q] :
    (∑ a : Fin s → ZMod q, normalizedSiftedCount a) = (q:ℝ)^s := by
  classical
  have hq : (q:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have ht : (q.totient:ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  unfold normalizedSiftedCount
  rw [← Finset.sum_div, ← Finset.mul_sum, siftedCount_sum]
  rw [div_pow]
  field_simp

theorem siftedCount_crt {s m n : ℕ} [NeZero m] [NeZero n]
    (hcop : m.Coprime n) (a : Fin s → ZMod (m*n)) :
    siftedCount a =
      siftedCount (fun i => (ZMod.chineseRemainder hcop (a i)).1) *
      siftedCount (fun i => (ZMod.chineseRemainder hcop (a i)).2) := by
  classical
  let e := ZMod.chineseRemainder hcop
  have hu (y : ZMod (m*n)) : IsUnit y ↔ IsUnit (e y) := by
    constructor
    · intro hy
      exact hy.map e.toMonoidHom
    · intro hy
      have hh := hy.map e.symm.toMonoidHom
      change IsUnit (e.symm (e y)) at hh
      simpa only [e.symm_apply_apply] using hh
  have hi (x : ZMod (m*n)) (i : Fin s) :
      (if IsUnit (x-a i) then (1:ℝ) else 0) =
      (if IsUnit ((e x).1-(e (a i)).1) then (1:ℝ) else 0) *
      (if IsUnit ((e x).2-(e (a i)).2) then (1:ℝ) else 0) := by
    simp only [hu, e.map_sub, Prod.isUnit_iff, Prod.fst_sub, Prod.snd_sub]
    split_ifs <;> first | omega | simp_all
  unfold siftedCount
  simp_rw [hi, Finset.prod_mul_distrib]
  have he := e.toEquiv.sum_comp (fun x : ZMod m × ZMod n =>
      (∏ i : Fin s, if IsUnit (x.1-(e (a i)).1) then (1:ℝ) else 0) *
      (∏ i : Fin s, if IsUnit (x.2-(e (a i)).2) then (1:ℝ) else 0))
  change _ = _ at he
  calc
    _ = ∑ x : ZMod m × ZMod n,
      (∏ i : Fin s, if IsUnit (x.1-(e (a i)).1) then (1:ℝ) else 0) *
      (∏ i : Fin s, if IsUnit (x.2-(e (a i)).2) then (1:ℝ) else 0) := he
    _ = _ := by
      rw [Fintype.sum_prod_type]
      exact (Fintype.sum_mul_sum
        (fun x : ZMod m => ∏ i : Fin s, if IsUnit (x-(e (a i)).1) then (1:ℝ) else 0)
        (fun x : ZMod n => ∏ i : Fin s, if IsUnit (x-(e (a i)).2) then (1:ℝ) else 0)).symm

theorem normalizedSiftedCount_crt {s m n : ℕ} [NeZero m] [NeZero n]
    (hcop : m.Coprime n) (a : Fin s → ZMod (m*n)) :
    normalizedSiftedCount a =
      normalizedSiftedCount (fun i => (ZMod.chineseRemainder hcop (a i)).1) *
      normalizedSiftedCount (fun i => (ZMod.chineseRemainder hcop (a i)).2) := by
  rw [normalizedSiftedCount, siftedCount_crt hcop, Nat.totient_mul hcop]
  simp only [normalizedSiftedCount, Nat.cast_mul, mul_div_mul_comm, mul_pow]
  ring

theorem product_indicator (s : ℕ) (P : Fin s → Prop) [DecidablePred P] :
    (∏ i : Fin s, if P i then (1:ℝ) else 0) = if ∀ i, P i then 1 else 0 := by
  classical
  by_cases h : ∀ i, P i
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem siftedCount_prime {s p : ℕ} [NeZero p] (hp : Nat.Prime p) (a : Fin s → ZMod p) :
    siftedCount a = (p:ℝ) - (Finset.univ.image a).card := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have he : (Finset.univ.filter fun x : ZMod p => ∀ i, x ≠ a i) =
      Finset.univ \ Finset.univ.image a := by
    ext x
    simp [eq_comm]
  unfold siftedCount
  simp_rw [isUnit_iff_ne_zero, sub_ne_zero, product_indicator]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, he]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Nat.cast_sub]
  · simp [ZMod.card]
  · exact Finset.card_le_card (Finset.subset_univ _)

theorem normalizedSiftedCount_prime {s p : ℕ} [NeZero p] (hp : Nat.Prime p) (a : Fin s → ZMod p) :
    normalizedSiftedCount a =
      (1 - ((Finset.univ.image a).card:ℝ)/(p:ℝ)) / (1-1/(p:ℝ))^s := by
  classical
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p:ℝ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [normalizedSiftedCount, siftedCount_prime hp, Nat.totient_prime hp]
  rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  have hd : (1:ℝ)-1/p = ((p:ℝ)-1)/p := by field_simp
  rw [hd]
  simp only [div_pow]
  field_simp

theorem siftedTuple_eq {s q : ℕ} [NeZero q] (a : Fin s → ℤ) :
    siftedTuple a q = normalizedSiftedCount (fun i => (a i : ZMod q)) := by
  simp only [siftedTuple, dite_eq_right (NeZero.ne q)]

theorem siftedTuple_crt {s m n : ℕ} [NeZero m] [NeZero n]
    (hcop : m.Coprime n) (a : Fin s → ℤ) :
    siftedTuple a (m*n) = siftedTuple a m * siftedTuple a n := by
  simp only [siftedTuple_eq]
  rw [normalizedSiftedCount_crt hcop]
  simp only [map_intCast, Prod.fst_intCast, Prod.snd_intCast]

theorem siftedTuple_one {s : ℕ} (a : Fin s → ℤ) : siftedTuple a 1 = 1 := by
  classical
  have hu (x : ZMod 1) : IsUnit x := by
    convert isUnit_one (M:=ZMod 1) using 1
    exact Subsingleton.elim _ _
  simp only [siftedTuple_eq, normalizedSiftedCount, siftedCount, hu, ite_true]
  simp

theorem siftedTuple_product {s : ℕ} (a : Fin s → ℤ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) :
    siftedTuple a (∏ p ∈ P, p) = ∏ p ∈ P, siftedTuple a p := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [siftedTuple_one]
  | @insert p P hp ih =>
    have hpP := hP p (Finset.mem_insert_self p P)
    have hP' (q) (hq : q ∈ P) := hP q (Finset.mem_insert_of_mem hq)
    let hp0 : NeZero p := ⟨hpP.ne_zero⟩
    let hprod0 : NeZero (∏ q ∈ P, q) := ⟨Finset.prod_ne_zero_iff.mpr
      (fun q hq => (hP' q hq).ne_zero)⟩
    have hc : p.Coprime (∏ q ∈ P, q) := Nat.Coprime.prod_right fun q hq => by
      apply hpP.coprime_iff_not_dvd.mpr
      intro hd
      have he := ((hP' q hq).dvd_iff_eq hpP.ne_one).mp hd
      exact hp (he.symm ▸ hq)
    simp only [Finset.prod_insert hp]
    rw [siftedTuple_crt hc, ih hP']

theorem siftedCount_nonneg {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) :
    0 ≤ siftedCount a := by
  unfold siftedCount
  positivity

theorem siftedCount_le {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) :
    siftedCount a ≤ (q:ℝ) := by
  classical
  calc
    _ ≤ ∑ _x : ZMod q, (1:ℝ) := by
      unfold siftedCount
      apply Finset.sum_le_sum
      intro x _
      exact Finset.prod_le_one (fun _ _ => by positivity) (fun _ _ => by split_ifs <;> norm_num)
    _ = _ := by simp

theorem normalizedSiftedCount_nonneg {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) :
    0 ≤ normalizedSiftedCount a :=
  div_nonneg (mul_nonneg (by positivity) (siftedCount_nonneg a)) (Nat.cast_nonneg _)

theorem normalizedSiftedCount_le {s q : ℕ} [NeZero q] (a : Fin s → ZMod q) :
    normalizedSiftedCount a ≤ (q:ℝ)^s := by
  have hq : (0:ℝ)<q := by exact_mod_cast NeZero.pos q
  have ht : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hdiv : (q:ℝ)/q.totient ≤ q := (div_le_self hq.le ht)
  unfold normalizedSiftedCount
  calc
    _ ≤ (q:ℝ)^s * q / q := div_le_div_of_nonneg_right
      (mul_le_mul (pow_le_pow_left₀ (by positivity) hdiv s) (siftedCount_le a)
        (siftedCount_nonneg a) (by positivity)) hq.le
    _ = _ := mul_div_cancel_right₀ _ hq.ne'

theorem residueCount_eq_card_zmod (H : Finset ℤ) {q : ℕ} [NeZero q] :
    residueCount H q = (H.image fun a : ℤ => (a : ZMod q)).card := by
  classical
  have he : (H.image fun a => a % (q:ℤ)).image (fun a : ℤ => (a : ZMod q)) =
      H.image (fun a : ℤ => (a : ZMod q)) := by
    rw [Finset.image_image]
    congr 1
    funext a
    exact ZMod.intCast_mod a q
  rw [← he]
  symm
  apply Finset.card_image_of_injOn
  intro a ha b hb heq
  obtain ⟨a', _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b', _, rfl⟩ := Finset.mem_image.mp hb
  have hh := (ZMod.intCast_eq_intCast_iff _ _ q).mp heq
  change (a' % (q:ℤ)) % (q:ℤ) = (b' % (q:ℤ)) % (q:ℤ) at hh
  simpa only [Int.emod_emod] using hh

theorem siftedTuple_prime_eq {s p : ℕ} (hp : Nat.Prime p) (a : Fin s → ℤ)
    (ha : Function.Injective a) :
    siftedTuple a p = singularLocal (Finset.univ.image a) p := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [siftedTuple_eq, normalizedSiftedCount_prime hp, singularLocal,
    residueCount_eq_card_zmod, Finset.image_image,
    Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin]
  rfl

theorem siftedTuple_primorial_eq {s y : ℕ} (a : Fin s → ℤ) (ha : Function.Injective a) :
    siftedTuple a (∏ p ∈ Nat.primesLE y, p) = singularTruncation (Finset.univ.image a) y := by
  rw [siftedTuple_product a _ (fun p hp => (Nat.mem_primesLE.mp hp).2)]
  exact Finset.prod_congr rfl fun p hp => siftedTuple_prime_eq (Nat.mem_primesLE.mp hp).2 a ha

theorem rangeResidue_card_bounds (h : ℕ) {q c : ℕ} (hq : 0<q) (hc : c<q) :
    h/q ≤ (rangeResidue h q c).card ∧ (rangeResidue h q c).card ≤ h/q+1 := by
  have hlo : (Finset.range (h/q)).card ≤ (rangeResidue h q c).card := by
    apply Finset.card_le_card_of_injOn (fun k => q*k+c)
    · intro k hk
      have hh := Nat.mul_le_mul_left q (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
      have hh' : q*k+q ≤ q*(h/q) := by simpa only [Nat.mul_succ] using hh
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
        change q*k+c<h
        have hd : q*(h/q) ≤ h := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self h q
        omega), ?_⟩
      simp only [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_eq_of_lt hc]
    · intro k _ l _ heq
      exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel heq)
  have hup : (rangeResidue h q c).card ≤ (Finset.range (h/q+1)).card := by
    apply Finset.card_le_card_of_injOn (fun n => n/q)
    · intro n hn
      have hh : n/q ≤ h/q := Nat.div_le_div_right (Finset.mem_range.mp (Finset.mem_filter.mp hn).1).le
      exact Finset.mem_range.mpr (by dsimp only; omega)
    · intro n hn m hm heq
      have hnmod := (Finset.mem_filter.mp hn).2
      have hmmod := (Finset.mem_filter.mp hm).2
      have hnform := Nat.div_add_mod n q
      have hmform := Nat.div_add_mod m q
      change n/q=m/q at heq
      rw [heq, hnmod] at hnform
      rw [hmmod] at hmform
      omega
  simpa only [Finset.card_range] using And.intro hlo hup

theorem cyclicFiber_card_bounds (a : ℤ) (h q : ℕ) [NeZero q] (r : ZMod q) :
    h/q ≤ (cyclicFiber a h q r).card ∧ (cyclicFiber a h q r).card ≤ h/q+1 := by
  classical
  have hpred (n : ℕ) : (a:ZMod q)+(n:ZMod q)=r ↔ n%q=(r-(a:ZMod q)).val := by
    rw [← eq_sub_iff_add_eq']
    constructor
    · intro he
      simpa only [ZMod.val_natCast] using congrArg ZMod.val he
    · intro he
      apply ZMod.val_injective q
      simpa only [ZMod.val_natCast] using he
  have hc : (cyclicFiber a h q r).card = (rangeResidue h q (r-(a:ZMod q)).val).card := by
    apply Finset.card_bij (fun (n : Fin h) _ => (n:ℕ))
    · intro n hn
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr n.isLt, ?_⟩
      exact (hpred n).mp (Finset.mem_filter.mp hn).2
    · intro n _ m _ he
      exact Fin.ext he
    · intro n hn
      obtain ⟨hn, hmod⟩ := Finset.mem_filter.mp hn
      refine ⟨⟨n, Finset.mem_range.mp hn⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hpred n).mpr hmod⟩
  rw [hc]
  exact rangeResidue_card_bounds h (NeZero.pos q) (ZMod.val_lt _)

theorem residueTuple_fiber_card {s h q : ℕ} [NeZero q] (a : Fin s → ℤ) (r : Fin s → ZMod q) :
    (Finset.univ.filter fun n : Fin s → Fin h => residueTuple a n = r).card =
      ∏ i : Fin s, (cyclicFiber (a i) h q (r i)).card := by
  classical
  have he : (Finset.univ.filter fun n : Fin s → Fin h => residueTuple a n = r) =
      Fintype.piFinset (fun i => cyclicFiber (a i) h q (r i)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      cyclicFiber, funext_iff, residueTuple]
  rw [he, Fintype.card_piFinset]

theorem residueTuple_sum_bounds {s h q : ℕ} [NeZero q] (a : Fin s → ℤ)
    (f : (Fin s → ZMod q) → ℝ) (hf : ∀ r, 0≤f r) :
    ((h/q:ℕ):ℝ)^s * (∑ r, f r) ≤ (∑ n : Fin s → Fin h, f (residueTuple a n)) ∧
    (∑ n : Fin s → Fin h, f (residueTuple a n)) ≤ ((h/q+1:ℕ):ℝ)^s * (∑ r, f r) := by
  classical
  have he : (∑ n : Fin s → Fin h, f (residueTuple a n)) =
      ∑ r : Fin s → ZMod q,
        ((Finset.univ.filter fun n : Fin s → Fin h => residueTuple a n = r).card:ℝ) * f r := by
    rw [← Finset.sum_fiberwise Finset.univ (residueTuple (q:=q) a) (fun n => f (residueTuple a n))]
    apply Finset.sum_congr rfl
    intro r _
    calc
      _ = ∑ _n ∈ Finset.univ.filter (fun n : Fin s → Fin h => residueTuple a n = r), f r := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [(Finset.mem_filter.mp hn).2]
      _ = _ := by simp
  rw [he]
  have hcard (r : Fin s → ZMod q) : ((h/q:ℕ):ℝ)^s ≤
      ((Finset.univ.filter fun n : Fin s → Fin h => residueTuple a n = r).card:ℝ) ∧
      ((Finset.univ.filter fun n : Fin s → Fin h => residueTuple a n = r).card:ℝ) ≤
        ((h/q+1:ℕ):ℝ)^s := by
    rw [residueTuple_fiber_card, Nat.cast_prod]
    constructor
    · calc
        _ = ∏ _i : Fin s, ((h/q:ℕ):ℝ) := by simp
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => by
          exact_mod_cast (cyclicFiber_card_bounds (a i) h q (r i)).1
    · calc
        _ ≤ ∏ _i : Fin s, ((h/q+1:ℕ):ℝ) :=
          Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => by
            exact_mod_cast (cyclicFiber_card_bounds (a i) h q (r i)).2
        _ = _ := by simp
  simp only [Finset.mul_sum]
  exact ⟨Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hcard r).1 (hf r),
    Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hcard r).2 (hf r)⟩

theorem boxTuple_collision_count {s h : ℕ} (a : Fin s → ℤ) {i j : Fin s} (hij : i≠j) :
    (Finset.univ.filter fun n : Fin s → Fin h => boxTuple a n i = boxTuple a n j).card ≤
      h^(s-1) := by
  classical
  have hc : Fintype.card {k : Fin s // k ≠ j} = s-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  calc
    _ ≤ (Finset.univ : Finset ({k : Fin s // k ≠ j} → Fin h)).card := by
      apply Finset.card_le_card_of_injOn (fun n k => n k.val)
      · intro n _
        exact Finset.mem_univ _
      · intro n hn m hm he
        have hi := congrFun he ⟨i, hij⟩
        have hn' := (Finset.mem_filter.mp hn).2
        have hm' := (Finset.mem_filter.mp hm).2
        funext k
        by_cases hk : k=j
        · subst k
          unfold boxTuple at hn' hm'
          have hci : (n i:ℕ)=(m i:ℕ) := congrArg Fin.val hi
          apply Fin.ext
          omega
        · exact congrFun he ⟨k, hk⟩
    _ = _ := by simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hc]

theorem boxTuple_nondistinct_count {s h : ℕ} (a : Fin s → ℤ) :
    (Finset.univ.filter fun n : Fin s → Fin h => ¬ Function.Injective (boxTuple a n)).card ≤
      s^2 * h^(s-1) := by
  classical
  let pairs : Finset (Fin s × Fin s) := Finset.univ.filter fun ij => ij.1 ≠ ij.2
  let bad (ij : Fin s × Fin s) := Finset.univ.filter fun n : Fin s → Fin h =>
    boxTuple a n ij.1 = boxTuple a n ij.2
  have hsub : (Finset.univ.filter fun n : Fin s → Fin h => ¬ Function.Injective (boxTuple a n)) ⊆
      pairs.biUnion bad := by
    intro n hn
    have hni := (Finset.mem_filter.mp hn).2
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨i, j, he, hne⟩ := hni
    exact Finset.mem_biUnion.mpr ⟨(i,j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
  calc
    _ ≤ (pairs.biUnion bad).card := Finset.card_le_card hsub
    _ ≤ pairs.card * h^(s-1) := Finset.card_biUnion_le_card_mul pairs bad _ fun ij hij =>
      boxTuple_collision_count a (Finset.mem_filter.mp hij).2
    _ ≤ s^2 * h^(s-1) := Nat.mul_le_mul_right _ (by
      calc
        pairs.card ≤ (Finset.univ : Finset (Fin s × Fin s)).card := Finset.card_filter_le _ _
        _ = _ := by simp [pow_two])

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_BoxMeans
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

theorem siftedTuple_boxTuple {s h q : ℕ} [NeZero q] (a : Fin s → ℤ) (n : Fin s → Fin h) :
    siftedTuple (boxTuple a n) q = normalizedSiftedCount (residueTuple (q:=q) a n) := by
  rw [siftedTuple_eq]
  congr 1
  funext i
  simp only [boxTuple, residueTuple, Int.cast_add, Int.cast_natCast]

theorem truncatedBoxMean_bounds {s h q : ℕ} [NeZero q] (hh : 0<h) (hq : q≤h)
    (a : Fin s → ℤ) :
    (1-(q:ℝ)/h)^s ≤ truncatedBoxMean (h:=h) a q ∧
    truncatedBoxMean (h:=h) a q ≤ (1+(q:ℝ)/h)^s := by
  have hhR : (0:ℝ)<h := by exact_mod_cast hh
  have hqR : (q:ℝ)≤h := by exact_mod_cast hq
  have hdiv : ((h/q:ℕ):ℝ)*(q:ℝ) ≤ h := by exact_mod_cast Nat.div_mul_le_self h q
  have hfloor : (h:ℝ)-(q:ℝ) ≤ ((h/q:ℕ):ℝ)*(q:ℝ) := by
    have he := Nat.div_add_mod h q
    have hm := Nat.mod_lt h (NeZero.pos q)
    have heR : ((h/q:ℕ):ℝ)*(q:ℝ)+(h%q:ℕ)=h := by
      exact_mod_cast (by simpa only [Nat.mul_comm] using he : h/q*q+h%q=h)
    have hmR : ((h%q:ℕ):ℝ)<q := by exact_mod_cast hm
    linarith
  have hb := residueTuple_sum_bounds (h:=h) a (@normalizedSiftedCount s q _) normalizedSiftedCount_nonneg
  rw [normalizedSiftedCount_sum] at hb
  simp_rw [← siftedTuple_boxTuple] at hb
  unfold truncatedBoxMean
  constructor
  · calc
      _ = ((h:ℝ)-(q:ℝ))^s/(h:ℝ)^s := by rw [← div_pow]; congr 1; field_simp
      _ ≤ (((h/q:ℕ):ℝ)*(q:ℝ))^s/(h:ℝ)^s := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (sub_nonneg.mpr hqR) hfloor s) (by positivity)
      _ ≤ _ := by rw [mul_pow]; exact div_le_div_of_nonneg_right hb.1 (by positivity)
  · calc
      _ ≤ (((h/q+1:ℕ):ℝ)*(q:ℝ))^s/(h:ℝ)^s := by
        rw [mul_pow]; exact div_le_div_of_nonneg_right hb.2 (by positivity)
      _ ≤ ((h:ℝ)+(q:ℝ))^s/(h:ℝ)^s := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by push_cast; nlinarith) s) (by positivity)
      _ = _ := by rw [← div_pow]; congr 1; field_simp

theorem distinctTruncatedBoxMean_le {s h q : ℕ} [NeZero q] (a : Fin s → ℤ) :
    distinctTruncatedBoxMean (h:=h) a q ≤ truncatedBoxMean (h:=h) a q := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro n _ _
  rw [siftedTuple_eq]
  exact normalizedSiftedCount_nonneg _

theorem truncatedBoxMean_sub_distinct_le {s h q : ℕ} [NeZero q] (hh : 0<h)
    (a : Fin s → ℤ) :
    truncatedBoxMean (h:=h) a q - distinctTruncatedBoxMean (h:=h) a q ≤
      (s:ℝ)^2*(q:ℝ)^s/(h:ℝ) := by
  classical
  by_cases hs : s=0
  · subst s
    have hall : distinctBox (h:=h) a = Finset.univ := by
      ext n
      simp [distinctBox, Function.Injective]
    simp [truncatedBoxMean, distinctTruncatedBoxMean, hall]
  have hhR : (0:ℝ)<h := by exact_mod_cast hh
  have hsum := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin s → Fin h))
    (fun n => Function.Injective (boxTuple a n)) (fun n => siftedTuple (boxTuple a n) q)
  have hb : (∑ n ∈ Finset.univ.filter (fun n : Fin s → Fin h => ¬Function.Injective (boxTuple a n)),
      siftedTuple (boxTuple a n) q) ≤ (s:ℝ)^2*(h:ℝ)^(s-1)*(q:ℝ)^s := by
    calc
      _ ≤ ((Finset.univ.filter fun n : Fin s → Fin h => ¬Function.Injective (boxTuple a n)).card:ℝ) *
          (q:ℝ)^s := by
        simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ ((q:ℝ)^s) (fun n _ => by
          rw [siftedTuple_eq]
          exact normalizedSiftedCount_le _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast boxTuple_nondistinct_count (h:=h) a)
        (by positivity)
  unfold truncatedBoxMean distinctTruncatedBoxMean distinctBox
  rw [← sub_div]
  calc
    _ ≤ ((s:ℝ)^2*(h:ℝ)^(s-1)*(q:ℝ)^s)/(h:ℝ)^s := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith [hsum]
    _ = _ := by
      have hp : (h:ℝ)^s=(h:ℝ)^(s-1)*(h:ℝ) := by
        rw [← pow_succ]; congr 1; omega
      rw [hp]
      field_simp

theorem distinctTruncatedBoxMean_error {s h q : ℕ} [NeZero q] (hh : 0<h) (hq : q≤h)
    (a : Fin s → ℤ) :
    |distinctTruncatedBoxMean (h:=h) a q-1| ≤ boxTruncationError s h q := by
  have hb := truncatedBoxMean_bounds hh hq a
  have hd := truncatedBoxMean_sub_distinct_le (q:=q) hh a
  have hle := distinctTruncatedBoxMean_le (q:=q) (h:=h) a
  unfold boxTruncationError
  apply abs_le.mpr
  constructor
  · have hl := neg_abs_le ((1-(q:ℝ)/h)^s-1)
    have hpos := abs_nonneg ((1+(q:ℝ)/h)^s-1)
    linarith
  · have hu := le_abs_self ((1+(q:ℝ)/h)^s-1)
    have hpos := abs_nonneg ((1-(q:ℝ)/h)^s-1)
    have hnn : 0≤(s:ℝ)^2*(q:ℝ)^s/h := by positivity
    linarith

theorem singularTailBound_le_uniform {s M y : ℕ} (a : Fin s → ℤ)
    (ha : Function.Injective a) (hy : 1<y)
    (hd : ∀ i j, (a i-a j).natAbs ≤ M) :
    singularTailBound (Finset.univ.image a) y ≤ uniformSingularTailBound s M y := by
  have hc : (Finset.univ.image a).card=s := by
    rw [Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin]
  have hb := differenceProduct_le (Finset.univ.image a) (M:=M) (by
    intro x hx z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
    exact hd i j)
  rw [hc] at hb
  have hl : Real.log (differenceProduct (Finset.univ.image a)) ≤
      ((s*(s-1):ℕ):ℝ)*Real.log M := by
    rw [← Real.log_pow]
    apply Real.log_le_log
    · exact_mod_cast differenceProduct_pos (Finset.univ.image a)
    · exact_mod_cast hb
  unfold singularTailBound uniformSingularTailBound
  rw [hc]
  apply add_le_add le_rfl
  calc
    _ ≤ 4*(s:ℝ)*(((s*(s-1):ℕ):ℝ)*Real.log M)/((y:ℝ)*Real.log y) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl (by positivity))
        (mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast (show 1≤y by omega))))
    _ = _ := by ring

theorem uniformSingularTailBound_nonneg (s : ℕ) {M y : ℕ} (hM : 0<M) (hy : 1<y) :
    0 ≤ uniformSingularTailBound s M y := by
  have hlogM : 0≤Real.log (M:ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  have hlogy : 0≤Real.log (y:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤y by omega))
  unfold uniformSingularTailBound
  positivity

theorem singularBoxMean_sub_truncation {s h M y : ℕ} (a : Fin s → ℤ)
    (hy : 1<y) (hys : 2*s≤y) (hd : boxDiameterBound (h:=h) a M)
    (hB : uniformSingularTailBound s M y≤1) :
    |singularBoxMean (h:=h) a-distinctTruncatedBoxMean (h:=h) a (primorial y)| ≤
      2*uniformSingularTailBound s M y*distinctTruncatedBoxMean (h:=h) a (primorial y) := by
  classical
  let : NeZero (primorial y) := ⟨(primorial_pos y).ne'⟩
  have hpoint (n : Fin s → Fin h) (hn : n∈distinctBox a) :
      |singularSeries (Finset.univ.image (boxTuple a n))-siftedTuple (boxTuple a n) (primorial y)| ≤
      2*uniformSingularTailBound s M y*siftedTuple (boxTuple a n) (primorial y) := by
    have hi := (Finset.mem_filter.mp hn).2
    have hc : (Finset.univ.image (boxTuple a n)).card=s := by
      rw [Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]
    have hut := singularTailBound_le_uniform (boxTuple a n) hi hy (hd n)
    have ht := singularTail_error (Finset.univ.image (boxTuple a n)) hy (by simpa only [hc] using hys)
      (hut.trans hB)
    have hp : 0 ≤ siftedTuple (boxTuple a n) (primorial y) := by
      rw [siftedTuple_eq]
      exact normalizedSiftedCount_nonneg _
    rw [singularSeries_eq_truncation_mul_tail _ hy (by simpa only [hc] using hys),
      ← siftedTuple_primorial_eq _ hi, ← primorial_eq_prod_primesLE]
    calc
      _ = siftedTuple (boxTuple a n) (primorial y)*|singularTail (Finset.univ.image (boxTuple a n)) y-1| := by
        rw [← mul_sub_one, abs_mul, abs_of_nonneg hp]
      _ ≤ siftedTuple (boxTuple a n) (primorial y)*(2*uniformSingularTailBound s M y) :=
        mul_le_mul_of_nonneg_left (ht.trans (mul_le_mul_of_nonneg_left hut (by norm_num))) hp
      _ = _ := by ring
  unfold singularBoxMean distinctTruncatedBoxMean
  rw [← sub_div, abs_div, abs_of_nonneg (by positivity : 0≤(h:ℝ)^s), ← Finset.sum_sub_distrib]
  calc
    _ ≤ (∑ n ∈ distinctBox a, |singularSeries (Finset.univ.image (boxTuple a n))-
        siftedTuple (boxTuple a n) (primorial y)|)/(h:ℝ)^s :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (∑ n ∈ distinctBox a, 2*uniformSingularTailBound s M y*
        siftedTuple (boxTuple a n) (primorial y))/(h:ℝ)^s :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum hpoint) (by positivity)
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem singularBoxMean_error {s h M y : ℕ} (a : Fin s → ℤ) (hh : 0<h)
    (hM : 0<M) (hy : 1<y) (hys : 2*s≤y) (hd : boxDiameterBound (h:=h) a M)
    (hB : uniformSingularTailBound s M y≤1) (hq : primorial y≤h) :
    |singularBoxMean (h:=h) a-1| ≤ boxTruncationError s h (primorial y) +
      2*uniformSingularTailBound s M y*(1+(primorial y:ℝ)/h)^s := by
  let : NeZero (primorial y) := ⟨(primorial_pos y).ne'⟩
  have hb := uniformSingularTailBound_nonneg s hM hy
  calc
    _ ≤ |singularBoxMean (h:=h) a-distinctTruncatedBoxMean (h:=h) a (primorial y)| +
        |distinctTruncatedBoxMean (h:=h) a (primorial y)-1| := abs_sub_le _ _ _
    _ ≤ 2*uniformSingularTailBound s M y*distinctTruncatedBoxMean (h:=h) a (primorial y) +
        boxTruncationError s h (primorial y) := add_le_add
      (singularBoxMean_sub_truncation a hy hys hd hB) (distinctTruncatedBoxMean_error hh hq a)
    _ ≤ 2*uniformSingularTailBound s M y*(1+(primorial y:ℝ)/h)^s +
        boxTruncationError s h (primorial y) := add_le_add_left
      (mul_le_mul_of_nonneg_left ((distinctTruncatedBoxMean_le (q:=primorial y) a).trans (truncatedBoxMean_bounds hh hq a).2)
        (show 0 ≤ 2*uniformSingularTailBound s M y from mul_nonneg (by norm_num) hb)) _
    _ = _ := by ring

theorem singularCutoffScale_pos (s : ℕ) : 0<singularCutoffScale s := by
  unfold singularCutoffScale
  positivity

theorem singularCutoff_tendsto (s : ℕ) : Tendsto (singularCutoff s) atTop atTop :=
  tendsto_nat_floor_atTop.comp (Tendsto.atTop_div_const (singularCutoffScale_pos s)
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

theorem singularCutoff_ratio_tendsto (s : ℕ) :
    Tendsto (fun h : ℕ => (singularCutoff s h:ℝ)/Real.log h) atTop (𝓝 (1/singularCutoffScale s)) := by
  have hh := (tendsto_nat_floor_mul_div_atTop (a:=1/singularCutoffScale s)
    (one_div_nonneg.mpr (singularCutoffScale_pos s).le)).comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  simpa only [singularCutoff, one_div_mul_eq_div, Function.comp_def] using hh

theorem log_div_singularCutoff_tendsto (s : ℕ) :
    Tendsto (fun h : ℕ => Real.log h/(singularCutoff s h:ℝ)) atTop (𝓝 (singularCutoffScale s)) := by
  simpa only [inv_div, one_div, inv_inv] using (singularCutoff_ratio_tendsto s).inv₀
    (one_div_ne_zero (singularCutoffScale_pos s).ne')

theorem primorial_singularCutoff_power_bound (s : ℕ) {h : ℕ} (hh : 0<h) :
    (primorial (singularCutoff s h):ℝ)^(s+1) ≤ (h:ℝ)^(1/2:ℝ) := by
  have hhR : (0:ℝ)<h := by exact_mod_cast hh
  have hlog : 0≤Real.log (h:ℝ) := Real.log_nonneg (by exact_mod_cast hh)
  have hfloor := Nat.floor_le (div_nonneg hlog (singularCutoffScale_pos s).le)
  change (singularCutoff s h:ℝ) ≤ Real.log h/singularCutoffScale s at hfloor
  have hb := (le_div_iff₀ (singularCutoffScale_pos s)).mp hfloor
  have hexp : ((singularCutoff s h:ℝ)*((s:ℝ)+1))*Real.log 4 ≤ Real.log h*(1/2) := by
    unfold singularCutoffScale at hb
    nlinarith
  calc
    _ ≤ ((4:ℝ)^(singularCutoff s h))^(s+1) := pow_le_pow_left₀ (by positivity)
      (by exact_mod_cast primorial_le_four_pow (singularCutoff s h)) _
    _ = Real.exp (((singularCutoff s h:ℝ)*((s:ℝ)+1))*Real.log 4) := by
      rw [← pow_mul, ← Real.exp_log (by norm_num : (0:ℝ)<4), ← Real.exp_nat_mul]
      rw [Real.log_exp]
      push_cast
      congr 1
    _ ≤ _ := by rw [Real.rpow_def_of_pos hhR]; exact Real.exp_le_exp.mpr hexp

theorem primorial_singularCutoff_ratio_tendsto (s r : ℕ) (hr : r ≤ s+1) :
    Tendsto (fun h : ℕ => (primorial (singularCutoff s h):ℝ)^r/(h:ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun h : ℕ => (h:ℝ)^(-(1/2:ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Filter.Eventually.of_forall fun h => by positivity
  · filter_upwards [eventually_ge_atTop 1] with h hh
    have hhR : (0:ℝ)<h := by exact_mod_cast hh
    calc
      _ ≤ (primorial (singularCutoff s h):ℝ)^(s+1)/(h:ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast (Nat.pow_le_pow_right
          (primorial_pos (singularCutoff s h)) hr)) hhR.le
      _ ≤ (h:ℝ)^(1/2:ℝ)/(h:ℝ) := div_le_div_of_nonneg_right
        (primorial_singularCutoff_power_bound s (by omega)) hhR.le
      _ = _ := by
        have he := Real.rpow_sub hhR (1/2:ℝ) 1
        norm_num only [Real.rpow_one, show (1/2:ℝ)-1=-(1/2) by norm_num] at he
        exact he.symm

theorem primorial_singularCutoff_div_tendsto (s : ℕ) :
    Tendsto (fun h : ℕ => (primorial (singularCutoff s h):ℝ)/(h:ℝ)) atTop (𝓝 0) := by
  simpa only [pow_one] using primorial_singularCutoff_ratio_tendsto s 1 (by omega)

theorem log_mul_div_singularCutoff_tendsto (s : ℕ) {K : ℕ} (hK : 0<K) :
    Tendsto (fun h : ℕ => Real.log (K*h:ℕ)/(singularCutoff s h:ℝ)) atTop (𝓝 (singularCutoffScale s)) := by
  have hy := tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp (singularCutoff_tendsto s)
  have hz : Tendsto (fun h : ℕ => Real.log (K:ℝ)/(singularCutoff s h:ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv, Pi.inv_apply, Function.comp_apply] using hy.inv_tendsto_atTop.const_mul (Real.log (K:ℝ))
  have ht := hz.add (log_div_singularCutoff_tendsto s)
  rw [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with h hh
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hK.ne') (by exact_mod_cast (show h≠0 by omega)), add_div]

theorem uniformSingularTailBound_tendsto (s : ℕ) {K : ℕ} (hK : 0<K) :
    Tendsto (fun h : ℕ => uniformSingularTailBound s (K*h) (singularCutoff s h)) atTop (𝓝 0) := by
  have hy := tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp (singularCutoff_tendsto s)
  have hl := Real.tendsto_log_atTop.comp hy
  have ht := (hy.inv_tendsto_atTop.const_mul (2*((s:ℝ)^2*(2:ℝ)^s))).add
    (((log_mul_div_singularCutoff_tendsto s hK).mul hl.inv_tendsto_atTop).const_mul
      (4*(s:ℝ)*((s*(s-1):ℕ):ℝ)))
  simp only [mul_zero, add_zero] at ht
  convert ht using 1
  ext h
  unfold uniformSingularTailBound
  simp only [div_eq_mul_inv, mul_inv_rev, Pi.inv_apply, Function.comp_apply]
  ring

theorem boxTruncationError_tendsto (s : ℕ) :
    Tendsto (fun h : ℕ => boxTruncationError s h (primorial (singularCutoff s h))) atTop (𝓝 0) := by
  have hq := primorial_singularCutoff_div_tendsto s
  have hl := ((tendsto_const_nhds (x:=(1:ℝ)).sub hq).pow s).sub (tendsto_const_nhds (x:=(1:ℝ)))
  have hu := ((tendsto_const_nhds (x:=(1:ℝ)).add hq).pow s).sub (tendsto_const_nhds (x:=(1:ℝ)))
  have hd := (primorial_singularCutoff_ratio_tendsto s s (by omega)).const_mul ((s:ℝ)^2)
  have ht := (hl.abs.add hu.abs).add hd
  simp only [sub_zero, one_pow, sub_self, add_zero, abs_zero, mul_zero] at ht
  convert ht using 1
  ext h
  unfold boxTruncationError
  ring

theorem singularBoxError_tendsto (s : ℕ) {K : ℕ} (hK : 0<K) :
    Tendsto (singularBoxError s K) atTop (𝓝 0) := by
  have ht := (boxTruncationError_tendsto s).add
    (((uniformSingularTailBound_tendsto s hK).const_mul 2).mul
      ((tendsto_const_nhds (x:=(1:ℝ))).add (primorial_singularCutoff_div_tendsto s) |>.pow s))
  simp only [mul_zero, zero_mul, add_zero] at ht
  exact ht

theorem singularBoxMean_error_eventually (s : ℕ) {K : ℕ} (hK : 0<K) :
    ∀ᶠ h : ℕ in atTop, ∀ a : Fin s → ℤ, boxDiameterBound (h:=h) a (K*h) →
      |singularBoxMean (h:=h) a-1| ≤ singularBoxError s K h := by
  have hB := (uniformSingularTailBound_tendsto s hK).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  have hq := (primorial_singularCutoff_div_tendsto s).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [eventually_ge_atTop 1, (singularCutoff_tendsto s).eventually_ge_atTop 2,
      (singularCutoff_tendsto s).eventually_ge_atTop (2*s), hB, hq] with h hh hy hys hB hq
  intro a hd
  have hqh : primorial (singularCutoff s h) ≤ h := by
    have hhR : (0:ℝ)<h := by exact_mod_cast hh
    have ht := (div_lt_one hhR).mp hq
    exact_mod_cast ht.le
  exact singularBoxMean_error a (by omega) (Nat.mul_pos hK (by omega)) (by omega) hys hd hB.le hqh

theorem singularBoxMean_uniform (s : ℕ) {K : ℕ} (hK : 0<K) {ε : ℝ} (hε : 0<ε) :
    ∃ h₀ : ℕ, ∀ h≥h₀, ∀ a : Fin s → ℤ, boxDiameterBound (h:=h) a (K*h) →
      |singularBoxMean (h:=h) a-1| < ε := by
  have he := (singularBoxError_tendsto s hK).eventually (gt_mem_nhds hε)
  have hb := (singularBoxMean_error_eventually s hK).and he
  obtain ⟨h₀, hh₀⟩ := Filter.eventually_atTop.mp hb
  exact ⟨h₀, fun h hh a hd => ((hh₀ h hh).1 a hd).trans_lt (hh₀ h hh).2⟩

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_ZetaKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

theorem mem_nonemptySubsets {ι : Type*} {s S : Finset ι} :
    S∈nonemptySubsets s ↔ S.Nonempty ∧ S⊆s := by
  classical
  simp [nonemptySubsets, Finset.nonempty_iff_ne_empty]

theorem sum_nonemptySubsets_sign {ι : Type*} {s : Finset ι} (hs : s.Nonempty) :
    (∑ S∈nonemptySubsets s, (-1:ℤ)^S.card) = -1 := by
  classical
  have h := Finset.sum_erase_add s.powerset (fun S => (-1:ℤ)^S.card) (Finset.empty_mem_powerset s)
  rw [Finset.sum_powerset_neg_one_pow_card_of_nonempty hs] at h
  simpa only [Finset.card_empty, pow_zero, add_eq_zero_iff_eq_neg, nonemptySubsets] using h

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_EulerProducts
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

theorem mem_fiberSubsetFamily {ι α : Type*} [Fintype ι] (b : ι → α)
    (R : Finset α) (S : Finset ι) :
    S∈fiberSubsetFamily b R ↔ S.Nonempty ∧ ∃ r∈R, ∀ i∈S, b i=r := by
  classical
  simp only [fiberSubsetFamily, Finset.mem_biUnion, mem_nonemptySubsets]
  constructor
  · rintro ⟨r,hr,hS,hsub⟩
    exact ⟨hS,r,hr,fun i hi => (Finset.mem_filter.mp (hsub hi)).2⟩
  · rintro ⟨hS,r,hr,hsub⟩
    exact ⟨r,hr,hS,fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsub i hi⟩⟩

theorem disjoint_nonemptySubsets_fibers {ι α : Type*} [Fintype ι] (b : ι → α)
    {r s : α} (hrs : r≠s) :
    Disjoint (nonemptySubsets (Finset.univ.filter fun i => b i=r))
      (nonemptySubsets (Finset.univ.filter fun i => b i=s)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro S hSr hSs
  rcases mem_nonemptySubsets.mp hSr with ⟨hS,hR⟩
  have hT := (mem_nonemptySubsets.mp hSs).2
  rcases hS with ⟨i,hi⟩
  exact hrs ((Finset.mem_filter.mp (hR hi)).2.symm.trans (Finset.mem_filter.mp (hT hi)).2)

theorem fiberSubsetFamily_sign_sum {ι α : Type*} [Fintype ι] (b : ι → α)
    (R : Finset α) (hR : ∀ r∈R, ∃ i, b i=r) :
    (∑ S∈fiberSubsetFamily b R, (-1:ℤ)^S.card) = -(R.card:ℤ) := by
  classical
  rw [fiberSubsetFamily, Finset.sum_biUnion]
  · have hs (r : α) (hr : r∈R) : (Finset.univ.filter fun i => b i=r).Nonempty := by
      rcases hR r hr with ⟨i,hi⟩
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
    calc
      _ = ∑ _r∈R, (-1:ℤ) := Finset.sum_congr rfl (fun r hr => sum_nonemptySubsets_sign (hs r hr))
      _ = _ := by simp
  · intro r _ s _ hrs
    exact disjoint_nonemptySubsets_fibers b hrs

theorem mem_fiberSubsetFamily_image {ι α : Type*} [Fintype ι] [DecidableEq α] (b : ι → α)
    (S : Finset ι) :
    S∈fiberSubsetFamily b (Finset.univ.image b) ↔
      S.Nonempty ∧ ∀ i∈S, ∀ j∈S, b i=b j := by
  classical
  rw [mem_fiberSubsetFamily]
  constructor
  · rintro ⟨hS,r,_,hb⟩
    exact ⟨hS,fun i hi j hj => (hb i hi).trans (hb j hj).symm⟩
  · rintro ⟨hS,hb⟩
    rcases hS with ⟨i,hi⟩
    exact ⟨⟨i,hi⟩,b i,Finset.mem_image_of_mem _ (Finset.mem_univ _),fun j hj => hb j hj i hi⟩

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_FourierNormalization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

section FourierNormalization

open scoped FourierTransform SchwartzMap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem radianFourier_inversion (G : SchwartzMap V ℂ) (v : V) :
    (∫ u : V, radianFourier G u * Complex.exp (-Complex.I*(inner ℝ u v : ℂ))) = G v := by
  let A : ℝ := 2*Real.pi
  have hA : 0<A := by dsimp [A]; positivity
  let f := fun u : V => (𝓕⁻ G) u * Complex.exp (-Complex.I*((A*inner ℝ u v : ℝ):ℂ))
  have hscale : (∫ u : V, f (A⁻¹ • u)) = A^Module.finrank ℝ V • ∫ u : V, f u := by
    simpa only [inv_pow, inv_inv] using Measure.integral_comp_smul_of_nonneg volume f A⁻¹ (hR:= (inv_pos.mpr hA).le)
  have hinv : (∫ u : V, f u) = G v := by
    have hh := congrArg (fun H : SchwartzMap V ℂ => H v) (FourierTransform.fourier_fourierInv_eq (F := SchwartzMap V ℂ) G)
    rw [SchwartzMap.fourier_coe, Real.fourier_eq'] at hh
    convert hh using 1
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp only [f, A]
    rw [smul_eq_mul, mul_comm]
    congr 2
    push_cast
    ring_nf
  calc
    _ = ∫ u : V, (A^Module.finrank ℝ V)⁻¹ • f (A⁻¹ • u) := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [radianFourier, smul_apply,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
        frequencyDilation_apply]
      dsimp only [f, A]
      rw [real_inner_smul_left]
      have ht : 2*Real.pi*((2*Real.pi)⁻¹*inner ℝ u v) = inner ℝ u v := by field_simp
      rw [ht]
      simp only [Complex.real_smul, mul_assoc]
    _ = (A^Module.finrank ℝ V)⁻¹ • ∫ u : V, f (A⁻¹ • u) := integral_smul _ _
    _ = (A^Module.finrank ℝ V)⁻¹ • (A^Module.finrank ℝ V • G v) := by rw [hscale, hinv]
    _ = G v := by rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hA.ne'), one_smul]

theorem sourceFourier_inversion (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : V) :
    (∫ u : V, sourceFourier ℓ F hF hFs u *
      Complex.exp (-(ℓ v : ℂ)-Complex.I*(inner ℝ u v : ℂ))) = F v := by
  calc
    _ = Complex.exp (-(ℓ v : ℂ)) *
        ∫ u : V, sourceFourier ℓ F hF hFs u *
          Complex.exp (-Complex.I*(inner ℝ u v : ℂ)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      rw [sub_eq_add_neg, Complex.exp_add]
      ring_nf
    _ = Complex.exp (-(ℓ v : ℂ)) * (Complex.exp (ℓ v : ℂ)*F v) := by
      rw [sourceFourier, radianFourier_inversion, laplaceSchwartz_apply]
    _ = F v := by rw [← mul_assoc, ← Complex.exp_add]; simp

end FourierNormalization

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_ContourSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

theorem nonemptySubsets_singleton {ι : Type*} (i : ι) :
    nonemptySubsets {i} = {{i}} := by
  classical
  ext S
  simp [nonemptySubsets,Finset.subset_singleton_iff]
  aesop

theorem nonemptySubsets_pair {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i≠j) :
    nonemptySubsets {i,j} = {{i},{j},{i,j}} := by
  classical
  ext S
  simp only [nonemptySubsets, Finset.mem_erase, Finset.mem_powerset,
    Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨hne,he⟩
    have h : S=∅ ∨ S={i} ∨ S={j} ∨ S={i,j} := by
      have hp := Finset.mem_powerset.mpr he
      simp [Finset.powerset_insert] at hp
      aesop
    exact h.resolve_left (hne)
  · rintro (rfl|rfl|rfl) <;> simp

theorem fiberKernel_singleton {ι : Type*} (i : ι) (w : ι → ℂ) :
    fiberKernel {i} w = w i := by
  simp [fiberKernel,nonemptySubsets_singleton]

theorem fiberKernel_pair {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i≠j) (w : ι → ℂ) :
    fiberKernel {i,j} w = w i*w j/(w i+w j) := by
  rw [fiberKernel,nonemptySubsets_pair hij]
  have h1 : ({j} : Finset ι)≠{i,j} := by simp [Finset.ext_iff,hij]
  have h2 : ({i} : Finset ι)≠{j} := by simp [hij]
  have h3 : ({i} : Finset ι)≠{i,j} := by simp [Finset.ext_iff,hij.symm]
  simp [h1,h2,h3,hij,div_eq_mul_inv]
  ring

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_FourierDerivatives
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

section FourierDerivative

open scoped FourierTransform SchwartzMap ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

open LineDeriv

theorem radianFourier_lineDeriv (G : SchwartzMap V ℂ) (m u : V) :
    radianFourier (∂_{m} G) u = -Complex.I*(inner ℝ u m:ℂ)*radianFourier G u := by
  have hg : (inner ℝ · m).HasTemperateGrowth := by fun_prop
  simp only [radianFourier,SchwartzMap.fourierInv_lineDerivOp_eq,
    smul_apply,SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
    frequencyDilation_apply,SchwartzMap.smulLeftCLM_apply hg,real_inner_smul_left,
    smul_eq_mul,Complex.real_smul]
  push_cast
  field_simp

theorem radianFourier_add (G H : SchwartzMap V ℂ) (u : V) :
    radianFourier (G+H) u = radianFourier G u+radianFourier H u := by
  simp only [radianFourier, FourierTransform.fourierInv_add, map_add, smul_add, add_apply]

theorem radianFourier_const_mul (c : ℂ) (G : SchwartzMap V ℂ) (u : V) :
    radianFourier (c • G) u = c*radianFourier G u := by
  simp only [radianFourier, FourierTransform.fourierInv_smul, map_smul, smul_apply,Complex.real_smul,smul_eq_mul]
  ring

theorem radianFourier_laplaceLineDeriv (ℓ : V →L[ℝ] ℝ) (m : V)
    (G : SchwartzMap V ℂ) (u : V) :
    radianFourier (laplaceLineDeriv ℓ m G) u =
      ((ℓ m : ℂ)+Complex.I*(inner ℝ u m:ℂ))*radianFourier G u := by
  rw [laplaceLineDeriv, radianFourier_add, radianFourier_const_mul,
    radianFourier_const_mul, radianFourier_lineDeriv]
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem laplaceLineDeriv_apply (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (m v : V) :
    laplaceLineDeriv ℓ m (laplaceSchwartz ℓ F hF hFs) v =
      Complex.exp (ℓ v : ℂ)*(-fderiv ℝ F v m) := by
  have hlin := Complex.ofRealCLM.hasFDerivAt.comp v ℓ.hasFDerivAt
  have he := hlin.cexp
  have hf := he.mul ((hFs.differentiable (by simp)).differentiableAt.hasFDerivAt (x := v))
  simp only [laplaceLineDeriv, add_apply, smul_apply, smul_eq_mul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, laplaceSchwartz_apply]
  change (ℓ m:ℂ)*(Complex.exp (ℓ v:ℂ)*F v) +
    -1*(fderiv ℝ (fun v => Complex.exp (ℓ v:ℂ)*F v) v m) = _
  have hd := congrArg (fun A : V →L[ℝ] ℂ => A m) hf.fderiv
  simp only [Function.comp_apply, add_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul] at hd
  change (fderiv ℝ (fun x => Complex.exp (ℓ x:ℂ)*F x) v) m =
    Complex.exp (ℓ v:ℂ)*fderiv ℝ F v m + F v*(Complex.exp (ℓ v:ℂ)*(ℓ m:ℂ)) at hd
  rw [hd]
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem laplaceLineDeriv_laplaceSchwartz (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (m : V) :
    laplaceLineDeriv ℓ m (laplaceSchwartz ℓ F hF hFs) =
      laplaceSchwartz ℓ (fun v => -fderiv ℝ F v m) (hF.fderiv_apply ℝ m |>.neg)
        (contDiff_signedLineDeriv F hFs m) := by
  ext v
  exact laplaceLineDeriv_apply ℓ F hF hFs m v

theorem sourceFourier_signedLineDeriv (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (m u : V) :
    sourceFourier ℓ (fun v => -fderiv ℝ F v m) (hF.fderiv_apply ℝ m |>.neg)
        (contDiff_signedLineDeriv F hFs m) u =
      ((ℓ m:ℂ)+Complex.I*(inner ℝ u m:ℂ))*sourceFourier ℓ F hF hFs u := by
  unfold sourceFourier
  rw [← laplaceLineDeriv_laplaceSchwartz, radianFourier_laplaceLineDeriv]

theorem sourceFourier_signedDirections (ℓ : V →L[ℝ] ℝ) (ms : List V) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (u : V) :
    sourceFourier ℓ (signedDirections ms F) (signedDirections_compact ms F hF)
        (signedDirections_smooth ms F hFs) u =
      (ms.map (fun m => ((ℓ m:ℂ)+Complex.I*(inner ℝ u m:ℂ)))).prod *
        sourceFourier ℓ F hF hFs u := by
  induction ms with
  | nil => simp [signedDirections]
  | cons m ms ih =>
    change sourceFourier ℓ (fun v => -fderiv ℝ (signedDirections ms F) v m) _ _ u = _
    rw [sourceFourier_signedLineDeriv ℓ (signedDirections ms F)
      (signedDirections_compact ms F hF) (signedDirections_smooth ms F hFs),ih]
    simp only [List.map_cons,List.prod_cons,mul_assoc]

theorem sourceFourier_derivative_inversion (ℓ : V →L[ℝ] ℝ) (ms : List V) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : V) :
    (∫ u : V, sourceFourier ℓ F hF hFs u *
      (ms.map (fun m => ((ℓ m:ℂ)+Complex.I*(inner ℝ u m:ℂ)))).prod *
      Complex.exp (-(ℓ v:ℂ)-Complex.I*(inner ℝ u v:ℂ))) = signedDirections ms F v := by
  rw [← sourceFourier_inversion ℓ (signedDirections ms F)
    (signedDirections_compact ms F hF) (signedDirections_smooth ms F hFs) v]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [sourceFourier_signedDirections,mul_comm (sourceFourier ℓ F hF hFs u)]

end FourierDerivative

theorem familyKernel_fibers {ι α : Type*} [Fintype ι] (b : ι → α)
    (R : Finset α) (w : ι → ℂ) :
    familyKernel (fiberSubsetFamily b R) w =
      ∏ r∈R, fiberKernel (Finset.univ.filter fun i => b i=r) w := by
  classical
  unfold familyKernel fiberSubsetFamily fiberKernel
  rw [Finset.prod_biUnion]
  intro r _ s _ hrs
  exact disjoint_nonemptySubsets_fibers b hrs

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_LaplaceTransform
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

section FourierLaplace

open scoped FourierTransform SchwartzMap ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem positiveOrthantMeasure_eq_restrict (α : Type*) [Fintype α] :
    positiveOrthantMeasure α = volume.restrict (Set.pi univ (fun _ : α => Ioi (0:ℝ))) := by
  rw [volume_pi,Measure.restrict_pi_pi]
  rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem product_laplace_exp_eq {α : Type*} [Fintype α] (ℓ : V →L[ℝ] ℝ)
    (m : α → V) (u : V) (y : α → ℝ) :
    (∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ))) =
      Complex.exp (-(ℓ (rayVector m y):ℂ)-Complex.I*(inner ℝ u (rayVector m y):ℂ)) := by
  rw [← Complex.exp_sum]
  congr 1
  simp only [rayVector,map_sum,map_smul,smul_eq_mul,inner_sum,inner_smul_right,
    Complex.ofReal_sum,Complex.ofReal_mul]
  rw [← Finset.sum_neg_distrib,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold laplaceFrequency
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem norm_product_laplace_exp {α : Type*} [Fintype α] (ℓ : V →L[ℝ] ℝ)
    (m : α → V) (u : V) (y : α → ℝ) :
    ‖∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ))‖ =
      ∏ i, Real.exp (-ℓ (m i) * y i) := by
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp [Complex.norm_exp,laplaceFrequency]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem integral_product_laplace_exp {α : Type*} [Fintype α]
    (ℓ : V →L[ℝ] ℝ) (m : α → V) (hm : ∀ i, 0<ℓ (m i)) (u : V) :
    (∫ y, ∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ))
      ∂positiveOrthantMeasure α) = ∏ i, (laplaceFrequency ℓ (m i) u)⁻¹ := by
  rw [positiveOrthantMeasure,integral_fintype_prod_eq_prod
    (fun i (y : ℝ) => Complex.exp (-laplaceFrequency ℓ (m i) u * (y:ℂ)))]
  apply Finset.prod_congr rfl
  intro i _
  simpa using integral_exp_mul_complex_Ioi (a:=-laplaceFrequency ℓ (m i) u)
    (by simp [hm i]) 0

theorem schwartz_product_laplace_integrable {α : Type*} [Fintype α]
    (Ψ : SchwartzMap V ℂ) (ℓ : V →L[ℝ] ℝ) (m : α → V) (hm : ∀ i, 0<ℓ (m i)) :
    Integrable (fun z : V × (α → ℝ) => Ψ z.1 *
      ∏ i, Complex.exp (-laplaceFrequency ℓ (m i) z.1 * (z.2 i:ℂ)))
      (volume.prod (positiveOrthantMeasure α)) := by
  have he : Integrable (fun y : α → ℝ => ∏ i, Real.exp (-ℓ (m i)*y i))
      (positiveOrthantMeasure α) := by
    exact Integrable.fintype_prod (f := fun i y => Real.exp (-ℓ (m i)*y))
      (μ := fun _ => volume.restrict (Ioi 0))
      (fun i => integrableOn_exp_mul_Ioi (by linarith [hm i]) 0)
  have hb := (Ψ.integrable (μ := volume)).norm.mul_prod he
  apply hb.mono'
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul (Ψ.continuous.comp continuous_fst)
    apply continuous_finsetProd
    intro i _
    unfold laplaceFrequency
    fun_prop
  · filter_upwards [] with z
    rw [norm_mul,norm_product_laplace_exp]

theorem schwartz_product_laplace_interchange {α : Type*} [Fintype α]
    (Ψ : SchwartzMap V ℂ) (ℓ : V →L[ℝ] ℝ) (m : α → V) (hm : ∀ i, 0<ℓ (m i)) :
    (∫ u : V, Ψ u*(∏ i, (laplaceFrequency ℓ (m i) u)⁻¹)) =
      ∫ y, (∫ u : V, Ψ u *
        Complex.exp (-(ℓ (rayVector m y):ℂ)-Complex.I*(inner ℝ u (rayVector m y):ℂ)))
        ∂positiveOrthantMeasure α := by
  calc
    _ = ∫ u : V, ∫ y, Ψ u*(∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ)))
        ∂positiveOrthantMeasure α := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [integral_const_mul,integral_product_laplace_exp ℓ m hm]
    _ = ∫ y, (∫ u : V, Ψ u*(∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ))))
        ∂positiveOrthantMeasure α :=
      integral_integral_swap (schwartz_product_laplace_integrable Ψ ℓ m hm)
    _ = _ := by simp only [product_laplace_exp_eq]

theorem sourceFourier_product_laplace {α : Type*} [Fintype α]
    (ℓ : V →L[ℝ] ℝ) (F : V → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (m : α → V) (hm : ∀ i, 0<ℓ (m i)) :
    (∫ u : V, sourceFourier ℓ F hF hFs u*(∏ i, (laplaceFrequency ℓ (m i) u)⁻¹)) =
      ∫ y, F (rayVector m y) ∂positiveOrthantMeasure α := by
  rw [schwartz_product_laplace_interchange _ ℓ m hm]
  simp only [sourceFourier_inversion]

theorem sourceFourier_derivative_laplace {α : Type*} [Fintype α]
    (ℓ : V →L[ℝ] ℝ) (ms : List V) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (m : α → V) (hm : ∀ i, 0<ℓ (m i)) :
    (∫ u : V, sourceFourier ℓ F hF hFs u *
      (ms.map (fun m => laplaceFrequency ℓ m u)).prod *
      (∏ i, (laplaceFrequency ℓ (m i) u)⁻¹)) =
      ∫ y, signedDirections ms F (rayVector m y) ∂positiveOrthantMeasure α := by
  rw [← sourceFourier_product_laplace ℓ (signedDirections ms F)
    (signedDirections_compact ms F hF) (signedDirections_smooth ms F hFs) m hm]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [sourceFourier_signedDirections ℓ ms F hF hFs u]
  simp only [laplaceFrequency,mul_comm (sourceFourier ℓ F hF hFs u)]

end FourierLaplace

theorem fiberKernel_card_le_two {ι : Type*} (S : Finset ι) (hS : S.card≤2) (w : ι → ℂ) :
    fiberKernel S w = (∏ i∈S, w i)*if S.card=2 then (∑ i∈S, w i)⁻¹ else 1 := by
  classical
  have hc : S.card=0 ∨ S.card=1 ∨ S.card=2 := by omega
  rcases hc with hc|hc|hc
  · have hs : S=∅ := Finset.card_eq_zero.mp hc
    subst S
    simp [fiberKernel,nonemptySubsets]
  · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hc
    simp [fiberKernel_singleton]
  · obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hc
    simp [fiberKernel_pair hij,hij,div_eq_mul_inv]

theorem familyKernel_small_fibers {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (hR : ∀ i, b i∈R)
    (hcard : ∀ r∈R, (Finset.univ.filter fun i => b i=r).card≤2) (w : ι → ℂ) :
    familyKernel (fiberSubsetFamily b R) w =
      (∏ i, w i)*(∏ r∈R.filter (fun r => (Finset.univ.filter fun i => b i=r).card=2),
        (∑ i∈Finset.univ.filter (fun i => b i=r), w i)⁻¹) := by
  classical
  rw [familyKernel_fibers]
  calc
    _ = ∏ r∈R, (∏ i∈Finset.univ.filter (fun i => b i=r), w i)*
        (if (Finset.univ.filter (fun i => b i=r)).card=2 then
          (∑ i∈Finset.univ.filter (fun i => b i=r), w i)⁻¹ else 1) := by
      apply Finset.prod_congr rfl
      intro r hr
      exact fiberKernel_card_le_two _ (hcard r hr) w
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_fiberwise_of_maps_to (fun i _ => hR i)]
      congr 1
      exact (Finset.prod_filter ..).symm

section SmallFiberCoefficient

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem laplaceFrequency_sum {α : Type*} (ℓ : V →L[ℝ] ℝ) (S : Finset α)
    (m : α → V) (u : V) :
    laplaceFrequency ℓ (∑ i∈S, m i) u = ∑ i∈S, laplaceFrequency ℓ (m i) u := by
  simp [laplaceFrequency,map_sum,inner_sum,Complex.ofReal_sum,Finset.mul_sum,Finset.sum_add_distrib]

@[simp] theorem laplaceFrequency_fiberRay {ι α : Type*} [Fintype ι]
    (b : ι → α) (r : α) (u : EuclideanSpace ℝ ι) :
    laplaceFrequency (fourierCoordinateSum ι) (fiberRay b r) u =
      ∑ i∈Finset.univ.filter (fun i => b i=r), frequencyW (u i) := by
  classical
  simp [fiberRay,laplaceFrequency_sum]

theorem fiberRay_positive {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (r : doubleFibers b R) :
    0 < fourierCoordinateSum ι (fiberRay b r.val) := by
  classical
  have hr : (Finset.univ.filter (fun i => b i=r.val)).card=2 :=
    (Finset.mem_filter.mp r.property).2
  have h := congrArg Complex.re (laplaceFrequency_fiberRay b r.val (0 : EuclideanSpace ℝ ι))
  simp only [laplaceFrequency_re,Complex.re_sum,frequencyW_re,Finset.sum_const] at h
  rw [h,hr]
  norm_num

theorem small_fiber_kernelConstant {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (hR : ∀ i, b i∈R)
    (hcard : ∀ r∈R, (Finset.univ.filter fun i => b i=r).card≤2)
    (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    kernelConstant (sourceFourier (fourierCoordinateSum ι) F hF hFs) (fiberSubsetFamily b R) =
      ∫ y, signedDirections (coordinateDirectionList ι) F
        (rayVector (fun r : doubleFibers b R => fiberRay b r.val) y)
          ∂positiveOrthantMeasure (doubleFibers b R) := by
  classical
  rw [← sourceFourier_derivative_laplace (fourierCoordinateSum ι) (coordinateDirectionList ι)
    F hF hFs (fun r : doubleFibers b R => fiberRay b r.val) (fiberRay_positive b R)]
  unfold kernelConstant
  apply integral_congr_ae
  filter_upwards [] with u
  rw [contourKernel,familyKernel_small_fibers b R hR hcard,coordinateDirectionList_multiplier]
  simp only [laplaceFrequency_fiberRay]
  have hp := Finset.prod_coe_sort (s := doubleFibers b R)
    (f := fun r : α => (∑ i∈Finset.univ.filter (fun i => b i=r), frequencyW (u i))⁻¹)
  rw [hp,mul_assoc]
  rfl

end SmallFiberCoefficient

theorem shiftFamily_nonempty {ι : Type*} [Fintype ι] (b : ι → ℤ) :
    ∀ S∈shiftFamily b, S.Nonempty := by
  intro S hS
  exact ((mem_fiberSubsetFamily b (Finset.univ.image b) S).mp hS).1

theorem shiftFamily_sign_sum {ι : Type*} [Fintype ι] (b : ι → ℤ) :
    (∑ S∈shiftFamily b, (-1:ℤ)^S.card) = -((Finset.univ.image b).card:ℤ) := by
  apply fiberSubsetFamily_sign_sum
  intro r hr
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hr
  exact ⟨i,hi⟩

open Topology

open scoped Convolution ContDiff Pointwise

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_CumulativeProfiles
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem cumulativeExtension_tail {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ)
    (hf : ∀ y, f y≠0 → ∀ i, y i≤T)
    (v : EuclideanSpace ℝ ι) (hv : ∀ i, 0≤v i) :
    cumulativeExtension T f v = cumulativeTail f v := by
  have hs : MeasurableSet {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i} := by
    rw [Set.ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_le (continuous_const (y := v i)) (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i)).measurableSet
  unfold cumulativeExtension cumulativeTail
  rw [convolution_def]
  change (∫ t, cubeIndicator T t * f (v-t)) = _
  rw [← integral_sub_left_eq_self (fun t => cubeIndicator T t * f (v-t)) volume v]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [sub_sub_cancel]
  by_cases hfy : f y=0
  · simp [Set.indicator,hfy]
  · by_cases hy : ∀ i, v i≤y i
    · rw [Set.indicator_of_mem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∈negativeCube T := by
        intro i
        change -T≤v i-y i ∧ v i-y i≤0
        constructor <;> linarith [hf y hfy i,hv i,hy i]
      simp [cubeIndicator,Set.indicator_of_mem hcube]
    · rw [Set.indicator_of_notMem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∉negativeCube T := by
        intro h
        apply hy
        intro i
        have := (h i).2
        change v i-y i≤0 at this
        linarith
      simp [cubeIndicator,Set.indicator_of_notMem hcube]

section GeneralDirections

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem signedDirectionalList_smooth (ms : List V) (F : V → ℂ)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (signedDirectionalList ms F) := by
  induction ms with
  | nil => exact hF
  | cons m ms ih =>
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const |>.neg

theorem signedDirectionalList_compact (ms : List V) (F : V → ℂ)
    (hF : HasCompactSupport F) : HasCompactSupport (signedDirectionalList ms F) := by
  induction ms with
  | nil => exact hF
  | cons m ms ih => exact (ih.fderiv_apply ℝ m).neg

theorem signedDirectionalList_affine (ms : List V) (F : W → ℂ)
    (hF : ContDiff ℝ ∞ F) (A : V →L[ℝ] W) (c : W) :
    signedDirectionalList ms (fun v => F (c+A v)) =
      fun v => signedDirectionalList (ms.map A) F (c+A v) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    have hd := signedDirectionalList_smooth (ms.map A) F hF
    have hA (v : V) : HasFDerivAt (fun v => c+A v) A v := by
      simpa using (A.hasFDerivAt (x := v)).const_add c
    ext v
    change -fderiv ℝ (signedDirectionalList ms (fun v => F (c+A v))) v m = _
    rw [ih]
    have he := ((hd.differentiable (by simp) (c+A v)).hasFDerivAt.comp v (hA v)).fderiv
    simp only [Function.comp_def] at he
    rw [he]
    rfl

theorem signedDirectionalList_tsupport (ms : List V) (F : V → ℂ) :
    tsupport (signedDirectionalList ms F) ⊆ tsupport F := by
  induction ms with
  | nil => exact Set.Subset.rfl
  | cons m ms ih =>
    change tsupport (fun v => - fderiv ℝ (signedDirectionalList ms F) v m) ⊆ _
    change tsupport (-(fun v => fderiv ℝ (signedDirectionalList ms F) v m)) ⊆ _
    rw [tsupport_neg]
    exact (tsupport_fderiv_apply_subset ℝ m).trans ih

end GeneralDirections

theorem finTailEmbed_single (n : ℕ) (i : Fin n) :
    finTailEmbed n (Pi.single i 1) = Pi.single i.succ 1 := by
  ext j
  cases j using Fin.cases with
  | zero => simp
  | succ j => simp [Pi.single_apply,Fin.succ_inj]

theorem finDirections_succ (n : ℕ) :
    finDirections (n+1) = Pi.single 0 1 :: (finDirections n).map (finTailEmbed n) := by
  simp only [finDirections,List.finRange_succ,List.map_cons,List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (finTailEmbed_single n i).symm

theorem fin_cons_affine {n : ℕ} (a : ℝ) (x : Fin n → ℝ) :
    Fin.cons a x = Pi.single 0 a + finTailEmbed n x := by
  ext i
  cases i using Fin.cases <;> simp

theorem fin_cons_closedEmbedding (n : ℕ) (a : ℝ) :
    IsClosedEmbedding (fun x : Fin n → ℝ => (Fin.cons a x : Fin (n+1) → ℝ)) := by
  have h : Function.Injective (finTailEmbed n) := by
    intro x y hxy
    ext i
    have := congrFun hxy i.succ
    simpa using this
  have he := LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr h)
  have hc := (Homeomorph.addLeft (Pi.single 0 a : Fin (n+1) → ℝ)).isClosedEmbedding.comp he
  convert hc using 1
  funext x
  exact fin_cons_affine a x

theorem fin_cons_head_closedEmbedding (n : ℕ) (y : Fin n → ℝ) :
    IsClosedEmbedding (fun a : ℝ => (Fin.cons a y : Fin (n+1) → ℝ)) := by
  have he : IsClosedEmbedding (fun a : ℝ => a • (Pi.single 0 1 : Fin (n+1) → ℝ)) :=
    isClosedEmbedding_smul_left (by intro h; have := congrFun h 0; simp at this)
  have hc := (Homeomorph.addRight (Fin.cons 0 y : Fin (n+1) → ℝ)).isClosedEmbedding.comp he
  convert hc using 1
  ext a i
  cases i using Fin.cases <;> simp

theorem piTail_integral_cons {n : ℕ} (v : Fin (n+1) → ℝ)
    (f : (Fin (n+1) → ℝ) → ℂ) (hf : Integrable f (piTailMeasure v)) :
    (∫ x, f x ∂piTailMeasure v) =
      ∫ y, (∫ a in Ioi (v 0), f (Fin.cons a y)) ∂piTailMeasure (fun i => v i.succ) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have hm := measurePreserving_piFinSuccAbove
    (fun i : Fin (n+1) => volume.restrict (Ioi (v i))) 0
  have he : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.cons p.1 p.2 := by
    intro p
    simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
  dsimp only [e] at he
  have hprod : Integrable (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2))
      ((volume.restrict (Ioi (v 0))).prod (piTailMeasure (fun i => v i.succ))) := by
    have hh := (hm.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hf
    simpa only [Fin.zero_succAbove,he,Function.comp_def,piTailMeasure] using hh
  calc
    _ = ∫ p : ℝ × (Fin n → ℝ), f (Fin.cons p.1 p.2)
        ∂((volume.restrict (Ioi (v 0))).prod (piTailMeasure (fun i => v i.succ))) := by
      have hh := hm.symm.integral_comp' f
      simpa only [Fin.zero_succAbove,he,piTailMeasure] using hh.symm
    _ = _ := integral_prod_symm _ hprod

theorem fin_cons_head_affine {n : ℕ} (a : ℝ) (y : Fin n → ℝ) :
    Fin.cons a y = a • (Pi.single 0 1 : Fin (n+1) → ℝ) + Fin.cons 0 y := by
  ext i
  cases i using Fin.cases <;> simp

theorem fin_cons_hasDerivAt {n : ℕ} (y : Fin n → ℝ) (a : ℝ) :
    HasDerivAt (fun a => (Fin.cons a y : Fin (n+1) → ℝ)) (Pi.single 0 1) a := by
  have he : (fun a : ℝ => (Fin.cons a y : Fin (n+1) → ℝ)) =
      fun a => a • (Pi.single 0 1 : Fin (n+1) → ℝ) + Fin.cons 0 y :=
    funext (fun a => fin_cons_head_affine a y)
  rw [he]
  simpa using ((hasDerivAt_id a).smul_const (Pi.single 0 1 : Fin (n+1) → ℝ)).add_const
    (Fin.cons 0 y)

theorem fin_cons_head_smooth {n : ℕ} (y : Fin n → ℝ) :
    ContDiff ℝ ∞ (fun a => (Fin.cons a y : Fin (n+1) → ℝ)) := by
  have he : (fun a : ℝ => (Fin.cons a y : Fin (n+1) → ℝ)) =
      fun a => a • (Pi.single 0 1 : Fin (n+1) → ℝ) + Fin.cons 0 y :=
    funext (fun a => fin_cons_head_affine a y)
  rw [he]
  fun_prop

theorem fin_cons_tail_smooth {n : ℕ} (a : ℝ) :
    ContDiff ℝ ∞ (fun y : Fin n → ℝ => (Fin.cons a y : Fin (n+1) → ℝ)) := by
  simp_rw [fin_cons_affine]
  fun_prop

theorem piTail_signedDirections_FTC (n : ℕ) (F : (Fin n → ℝ) → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : Fin n → ℝ) :
    (∫ x, signedDirectionalList (finDirections n) F x ∂piTailMeasure v) = F v := by
  induction n with
  | zero =>
    simp only [finDirections,List.finRange_zero,List.map_nil,signedDirectionalList,List.foldr_nil]
    unfold piTailMeasure
    rw [Measure.pi_of_empty (x := v)]
    exact integral_dirac F v
  | succ n ih =>
    rw [finDirections_succ]
    let ms := (finDirections n).map (finTailEmbed n)
    let H := signedDirectionalList ms F
    have hHc : HasCompactSupport H := signedDirectionalList_compact ms F hF
    have hHs : ContDiff ℝ ∞ H := signedDirectionalList_smooth ms F hFs
    have hfull : Integrable (signedDirectionalList (Pi.single 0 1 :: ms) F) (piTailMeasure v) :=
      (signedDirectionalList_smooth _ F hFs).continuous.integrable_of_hasCompactSupport
        (signedDirectionalList_compact _ F hF)
    rw [piTail_integral_cons v _ hfull]
    have hinner (y : Fin n → ℝ) :
        (∫ a in Ioi (v 0), signedDirectionalList (Pi.single 0 1 :: ms) F (Fin.cons a y)) =
          H (Fin.cons (v 0) y) := by
      have hc : HasCompactSupport (fun a : ℝ => H (Fin.cons a y)) :=
        hHc.comp_isClosedEmbedding (fin_cons_head_closedEmbedding n y)
      have hs : ContDiff ℝ ∞ (fun a : ℝ => H (Fin.cons a y)) :=
        hHs.comp (fin_cons_head_smooth y)
      have hd (a : ℝ) : deriv (fun a : ℝ => H (Fin.cons a y)) a =
          fderiv ℝ H (Fin.cons a y) (Pi.single 0 1) := by
        exact ((hHs.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt a
          (fin_cons_hasDerivAt y a)).deriv
      have he : (fun a : ℝ => signedDirectionalList (Pi.single 0 1 :: ms) F (Fin.cons a y)) =
          fun a => -deriv (fun a : ℝ => H (Fin.cons a y)) a := by
        funext a
        rw [hd]
        rfl
      rw [he,integral_neg,HasCompactSupport.integral_Ioi_deriv_eq (hs.of_le (by simp)) hc,neg_neg]
    simp_rw [hinner]
    let G : (Fin n → ℝ) → ℂ := fun y => F (Fin.cons (v 0) y)
    have hGc : HasCompactSupport G := hF.comp_isClosedEmbedding (fin_cons_closedEmbedding n (v 0))
    have hGs : ContDiff ℝ ∞ G := hFs.comp (fin_cons_tail_smooth (v 0))
    have hg : (fun y : Fin n → ℝ => H (Fin.cons (v 0) y)) = signedDirectionalList (finDirections n) G := by
      have he := signedDirectionalList_affine (finDirections n) F hFs (finTailEmbed n)
        (Pi.single 0 (v 0))
      simpa only [← fin_cons_affine] using he.symm
    rw [hg,ih G hGc hGs (fun i => v i.succ)]
    dsimp only [G]
    congr 1
    ext i
    cases i using Fin.cases <;> rfl

theorem complexCumulativeExtension_compact {ι : Type*} [Fintype ι]
    (T : ℝ) (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) :
    HasCompactSupport (complexCumulativeExtension T F) :=
  HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (cubeIndicator_compact T) hF

theorem complexCumulativeExtension_smooth {ι : Type*} [Fintype ι]
    (T : ℝ) (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F)
    (hFs : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (complexCumulativeExtension T F) :=
  hF.contDiff_convolution_right _ (cubeIndicator_integrable T).locallyIntegrable hFs

theorem complexCumulativeExtension_tail {ι : Type*} [Fintype ι]
    (T : ℝ) (F : EuclideanSpace ℝ ι → ℂ)
    (hF : ∀ y, F y≠0 → ∀ i, y i≤T)
    (v : EuclideanSpace ℝ ι) (hv : ∀ i, 0≤v i) :
    complexCumulativeExtension T F v = ∫ y in {y | ∀ i, v i≤y i}, F y := by
  have hs : MeasurableSet {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i} := by
    rw [Set.ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_le (continuous_const (y := v i))
      (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i)).measurableSet
  unfold complexCumulativeExtension
  rw [convolution_def]
  change (∫ t, cubeIndicator T t • F (v-t)) = _
  rw [← integral_sub_left_eq_self (fun t => cubeIndicator T t • F (v-t)) volume v]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [sub_sub_cancel]
  by_cases hFy : F y=0
  · simp [Set.indicator,hFy]
  · by_cases hy : ∀ i, v i≤y i
    · rw [Set.indicator_of_mem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∈negativeCube T := by
        intro i
        change -T≤v i-y i ∧ v i-y i≤0
        constructor <;> linarith [hF y hFy i,hv i,hy i]
      simp [cubeIndicator,Set.indicator_of_mem hcube]
    · rw [Set.indicator_of_notMem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∉negativeCube T := by
        intro h
        apply hy
        intro i
        have := (h i).2
        change v i-y i≤0 at this
        linarith
      simp [cubeIndicator,Set.indicator_of_notMem hcube]

theorem signedDirections_cumulative {ι : Type*} [Fintype ι]
    (T : ℝ) (ms : List (EuclideanSpace ℝ ι)) (F : EuclideanSpace ℝ ι → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    signedDirections ms (complexCumulativeExtension T F) =
      complexCumulativeExtension T (signedDirections ms F) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    ext v
    change -fderiv ℝ (signedDirections ms (complexCumulativeExtension T F)) v m = _
    rw [ih]
    have hc := signedDirections_compact ms F hF
    have hs := signedDirections_smooth ms F hFs
    unfold complexCumulativeExtension
    rw [(hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      (cubeIndicator_integrable T).locallyIntegrable (hs.of_le (by simp)) v).fderiv]
    rw [convolution_precompR_apply _ (cubeIndicator_integrable T).locallyIntegrable
      (hc.fderiv ℝ) (hs.continuous_fderiv (by simp))]
    simp only [convolution_def,ContinuousLinearMap.lsmul_apply,
      signedDirections,List.foldr_cons,smul_neg,integral_neg]

theorem euclideanTail_signedDirections_FTC (n : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x in {x | ∀ i, v i≤x i}, signedDirections (euclideanFinDirections n) F x) = F v := by
  let e := (EuclideanSpace.equiv (Fin n) ℝ).symm
  have hc : HasCompactSupport (fun x => F (e x)) :=
    hF.comp_isClosedEmbedding e.toHomeomorph.isClosedEmbedding
  have hs : ContDiff ℝ ∞ (fun x => F (e x)) := hFs.comp e.contDiff
  have hFTC := piTail_signedDirections_FTC n (fun x => F (e x)) hc hs v.ofLp
  have ha := signedDirectionalList_affine (finDirections n) F hFs e.toContinuousLinearMap 0
  simp only [zero_add] at ha
  have htail : piTailMeasure v.ofLp = volume.restrict (Ici v.ofLp) := by
    unfold piTailMeasure
    rw [← Measure.restrict_pi_pi]
    exact Measure.restrict_congr_set (Measure.univ_pi_Ioi_ae_eq_Ici (μ := fun _ => volume))
  change signedDirectionalList (finDirections n) (fun x => F (e x)) =
    fun x => signedDirections (euclideanFinDirections n) F (e x) at ha
  rw [htail,ha] at hFTC
  have he := (PiLp.volume_preserving_toLp (Fin n)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
    (signedDirections (euclideanFinDirections n) F) {x | ∀ i, v i≤x i}
  convert he.symm.trans hFTC using 1
  exact congrArg F (by simp [e])

theorem signedDirections_coordinate_eq_fin (n : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    signedDirections (coordinateDirectionList (Fin n)) F =
      signedDirections (euclideanFinDirections n) F := by
  ext v
  rw [← sourceFourier_derivative_inversion (fourierCoordinateSum (Fin n))
    (coordinateDirectionList (Fin n)) F hF hFs v,
    ← sourceFourier_derivative_inversion (fourierCoordinateSum (Fin n))
    (euclideanFinDirections n) F hF hFs v]
  apply integral_congr_ae
  filter_upwards [] with u
  change sourceFourier _ F hF hFs u *
    ((coordinateDirectionList (Fin n)).map (fun m => laplaceFrequency _ m u)).prod * _ =
    sourceFourier _ F hF hFs u *
    ((euclideanFinDirections n).map (fun m => laplaceFrequency _ m u)).prod * _
  rw [coordinateDirectionList_multiplier,euclideanFinDirections_multiplier]

theorem complexCumulativeExtension_signed_full (n : ℕ) (T : ℝ)
    (F : EuclideanSpace ℝ (Fin n) → ℂ) (hF : HasCompactSupport F)
    (hFs : ContDiff ℝ ∞ F) (hT : ∀ y∈tsupport F, ∀ i, y i≤T)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ∀ i, 0≤v i) :
    signedDirections (coordinateDirectionList (Fin n)) (complexCumulativeExtension T F) v =
      F v := by
  rw [signedDirections_coordinate_eq_fin n _ (complexCumulativeExtension_compact T F hF)
    (complexCumulativeExtension_smooth T F hF hFs),signedDirections_cumulative T _ F hF hFs]
  rw [complexCumulativeExtension_tail T _ _ v hv]
  · exact euclideanTail_signedDirections_FTC n F hF hFs v
  · intro y hy i
    exact hT y (signedDirectionalList_tsupport (euclideanFinDirections n) F
      (subset_tsupport _ hy)) i

theorem complexCumulativeExtension_ofReal {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ) :
    complexCumulativeExtension T (fun y => (f y:ℂ)) =
      fun v => (cumulativeExtension T f v:ℂ) := by
  ext v
  simp only [complexCumulativeExtension,cumulativeExtension,convolution_def,
    ContinuousLinearMap.lsmul_apply,ContinuousLinearMap.mul_apply',
    Complex.real_smul,← Complex.ofReal_mul,integral_complex_ofReal]

theorem profile_coordinate_upper {n : ℕ} {tau : ℝ} {f : (Fin n → ℝ) → ℝ}
    (hf : tsupport f ⊆ positiveSimplex n tau) (y : Fin n → ℝ) (hy : y∈tsupport f)
    (i : Fin n) : y i≤tau := by
  have hh := hf hy
  exact (Finset.single_le_sum (fun j _ => (hh.1 j).le) (Finset.mem_univ i)).trans hh.2.le

theorem cumulativeProfile_tail {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n tau) (v : Fin n → ℝ) (hv : ∀ i, 0≤v i) :
    cumulativeProfile tau f v = ∫ y in Ici v, f y := by
  unfold cumulativeProfile
  rw [cumulativeExtension_tail tau _ _ _ hv]
  · unfold cumulativeTail
    have hm := (PiLp.volume_preserving_ofLp (Fin n)).setIntegral_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding f (Ici v)
    exact hm
  · intro y hy i
    exact profile_coordinate_upper hf y.ofLp (subset_tsupport f hy) i

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_TensorProfiles
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem cumulativeProfile_budget {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n tau) : HasBudget (cumulativeProfile tau f) tau := by
  intro v hv hsum
  rw [cumulativeProfile_tail tau f hf v hv]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  by_contra hne
  have hh := hf (subset_tsupport f hne)
  have he : tau≤coordinateSum y :=
    hsum.le.trans (Finset.sum_le_sum (fun i _ => hy i))
  exact (not_lt_of_ge he) hh.2

theorem cumulativeProfile_signed_full {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ positiveSimplex n tau)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ∀ i, 0≤v i) :
    signedDirections (coordinateDirectionList (Fin n))
      (fun y : EuclideanSpace ℝ (Fin n) => (cumulativeProfile tau f y.ofLp:ℂ)) v =
      (f v.ofLp:ℂ) := by
  have hfc : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin n) => (f y.ofLp:ℂ)) :=
    (hf.comp_isClosedEmbedding (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isClosedEmbedding).comp_left
      Complex.ofReal_zero
  have hF : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => (f y.ofLp:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hfs.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff)
  have hT : ∀ y∈tsupport (fun y : EuclideanSpace ℝ (Fin n) => (f y.ofLp:ℂ)),
      ∀ i, y i≤tau := by
    intro y hy i
    have hsub := tsupport_comp_subset (g := (Complex.ofReal : ℝ → ℂ)) Complex.ofReal_zero
      (fun y : EuclideanSpace ℝ (Fin n) => f y.ofLp)
    have hp := tsupport_comp_subset_preimage f (EuclideanSpace.equiv (Fin n) ℝ).continuous
    exact profile_coordinate_upper hsupp y.ofLp (hp (hsub hy)) i
  have hh := complexCumulativeExtension_signed_full n tau _ hfc hF hT v hv
  rw [complexCumulativeExtension_ofReal] at hh
  convert hh using 1
  congr 2

theorem appendMeasurableEquiv_measurePreserving (n m : ℕ) :
    MeasurePreserving (appendMeasurableEquiv n m) := by
  let e := (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (n+m) => ℝ) finSumFinEquiv)
  have he : appendMeasurableEquiv n m=e := by
    ext p i
    change Fin.append p.1 p.2 i = e p i
    cases i using Fin.addCases with
    | left i => simp [e,MeasurableEquiv.coe_piCongrLeft,
        MeasurableEquiv.coe_sumPiEquivProdPi_symm,Equiv.piCongrLeft]
    | right i => simp [e,MeasurableEquiv.coe_piCongrLeft,
        MeasurableEquiv.coe_sumPiEquivProdPi_symm,Equiv.piCongrLeft]
  rw [he]
  exact (volume_measurePreserving_piCongrLeft (fun _ : Fin (n+m) => ℝ) finSumFinEquiv).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ Fin m => ℝ))

theorem tensorProfile_tsupport {n m : ℕ} {a b : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin m → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n a) (hg : tsupport g ⊆ positiveSimplex m b) :
    tsupport (tensorProfile f g) ⊆ positiveSimplex (n+m) (a+b) := by
  intro v hv
  have hleft : (fun i : Fin n => v (i.castAdd m)) ∈ tsupport f := by
    exact tsupport_comp_subset_preimage (f := fun x : Fin (n+m) → ℝ =>
      fun i : Fin n => x (i.castAdd m)) f
      (continuous_pi (fun i => continuous_apply _)) (tsupport_mul_subset_left hv)
  have hright : (fun i : Fin m => v (i.natAdd n)) ∈ tsupport g := by
    exact tsupport_comp_subset_preimage (f := fun x : Fin (n+m) → ℝ =>
      fun i : Fin m => x (i.natAdd n)) g
      (continuous_pi (fun i => continuous_apply _)) (tsupport_mul_subset_right hv)
  refine ⟨?_,?_⟩
  · intro i
    cases i using Fin.addCases with
    | left i => exact (hf hleft).1 i
    | right i => exact (hg hright).1 i
  · change (∑ i, v i)<a+b
    rw [Fin.sum_univ_add]
    exact add_lt_add (hf hleft).2 (hg hright).2

theorem tensorProfile_tail {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (v : Fin n → ℝ) (w : Fin m → ℝ) :
    (∫ y in Ici (Fin.append v w), tensorProfile f g y) =
      (∫ y in Ici v, f y)*(∫ y in Ici w, g y) := by
  have hd : (appendMeasurableEquiv n m) ⁻¹' Ici (Fin.append v w) = (Ici v) ×ˢ (Ici w) := by
    ext p
    change (∀ i, Fin.append v w i≤Fin.append p.1 p.2 i) ↔ _
    constructor
    · intro h
      exact ⟨fun i => by simpa using h (i.castAdd m),fun i => by simpa using h (i.natAdd n)⟩
    · rintro ⟨h1,h2⟩ i
      cases i using Fin.addCases with
      | left i => simpa using h1 i
      | right i => simpa using h2 i
  have hm := (appendMeasurableEquiv_measurePreserving n m).setIntegral_preimage_emb
    (appendMeasurableEquiv n m).measurableEmbedding (tensorProfile f g) (Ici (Fin.append v w))
  rw [hd] at hm
  rw [← hm]
  simp only [appendMeasurableEquiv_apply,tensorProfile_append]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod_mul f g

theorem cumulativeProfile_tensor {n m : ℕ} {a b : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin m → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n a) (hg : tsupport g ⊆ positiveSimplex m b)
    (v : Fin n → ℝ) (w : Fin m → ℝ) (hv : ∀ i, 0≤v i) (hw : ∀ i, 0≤w i) :
    cumulativeProfile (a+b) (tensorProfile f g) (Fin.append v w) =
      cumulativeProfile a f v*cumulativeProfile b g w := by
  rw [cumulativeProfile_tail (a+b) _ (tensorProfile_tsupport f g hf hg),
    cumulativeProfile_tail a f hf _ hv,cumulativeProfile_tail b g hg _ hw,tensorProfile_tail]
  intro i
  cases i using Fin.addCases with
  | left i => simpa using hv i
  | right i => simpa using hw i

theorem divisorSum_tensor (X M : ℕ) {n m : ℕ}
    (F : (Fin n → ℝ) → ℝ) (G : (Fin m → ℝ) → ℝ) (b : Fin n → ℕ) (c : Fin m → ℕ) :
    divisorSum X (tensorProfile F G) M (Fin.append b c)=
      divisorSum X F M b*divisorSum X G M c := by
  classical
  unfold divisorSum
  rw [Finset.sum_mul_sum, ←Finset.sum_product']
  symm
  apply Finset.sum_equiv (Fin.appendEquiv n m)
  · intro p
    simp only [Finset.mem_product,Fintype.mem_piFinset,Fin.appendEquiv_apply]
    constructor
    · rintro ⟨h1,h2⟩ i
      cases i using Fin.addCases with
      | left i => simpa using h1 i
      | right i => simpa using h2 i
    · intro h
      exact ⟨fun i => by simpa using h (i.castAdd m),fun i => by simpa using h (i.natAdd n)⟩
  · intro p _
    exact (divisorCoefficient_tensor X F G p.1 p.2).symm

theorem divisorSum_congr_orthant {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ℕ} (hX : 2≤X) (M : ℕ) (b : ι → ℕ) (F G : (ι → ℝ) → ℝ)
    (hFG : ∀ v, (∀ i, 0≤v i) → F v=G v) : divisorSum X F M b=divisorSum X G M b := by
  apply Finset.sum_congr rfl
  intro d hd
  unfold divisorCoefficient
  congr 1
  apply hFG
  apply logCoordinates_nonneg hX
  intro i
  exact Nat.pos_of_mem_divisors ((Fintype.mem_piFinset.mp hd) i)

theorem divisorCoefficient_snoc_one (X : ℕ) {n : ℕ}
    (F : (Fin (n+1) → ℝ) → ℝ) (d : Fin n → ℕ) :
    divisorCoefficient X F (Fin.snoc d 1)=
      divisorCoefficient X (fun v => F (Fin.snoc v 0)) d := by
  simp [divisorCoefficient,logCoordinates_snoc,Fin.prod_univ_castSucc]

theorem divisorCoefficient_snoc_prime_zero {X M a n : ℕ} (hX : 2≤X) (hM : X<M+a)
    (F : (Fin (n+1) → ℝ) → ℝ) {rho : ℝ} (hrho : rho<1) (hb : HasBudget F rho)
    (d : Fin n → ℕ) (hd : ∀ i, 0<d i) : divisorCoefficient X F (Fin.snoc d (M+a))=0 := by
  have hp : 0<M+a := by omega
  have hcoord := logCoordinates_nonneg hX (d := Fin.snoc d (M+a)) (by
    intro i; cases i using Fin.lastCases <;> simp [hp,hd])
  have hs : rho<∑ i,logCoordinates X (Fin.snoc d (M+a)) i := by
    apply hrho.trans
    apply lt_of_lt_of_le _ (Finset.single_le_sum (fun i _ => hcoord i) (Finset.mem_univ (Fin.last n)))
    simp only [logCoordinates,Fin.snoc_last]
    apply (lt_div_iff₀ (log_pos_of_two_le hX)).mpr
    simpa only [one_mul] using Real.log_lt_log (by exact_mod_cast (by omega : 0<X))
      (by exact_mod_cast hM)
  rw [divisorCoefficient,hb _ hcoord hs,mul_zero]

theorem divisorSum_snoc (X M : ℕ) {n : ℕ} (F : (Fin (n+1) → ℝ) → ℝ)
    (b : Fin n → ℕ) (a : ℕ) :
    divisorSum X F M (Fin.snoc b a)=
      ∑ r∈(M+a).divisors, ∑ d∈Fintype.piFinset (fun i => (M+b i).divisors),
        divisorCoefficient X F (Fin.snoc d r) := by
  classical
  unfold divisorSum
  rw [←Finset.sum_product']
  symm
  apply Finset.sum_equiv (Fin.snocEquiv (fun _ : Fin (n+1) => ℕ))
  · intro p
    simp only [Finset.mem_product,Fintype.mem_piFinset,Fin.snocEquiv]
    constructor
    · rintro ⟨h1,h2⟩ i
      cases i using Fin.lastCases with
      | last => simpa using h1
      | cast i => simpa using h2 i
    · intro h
      exact ⟨by simpa using h (Fin.last n),fun i => by simpa using h i.castSucc⟩
  · intro p _
    rfl

theorem divisorSum_prime_delete {X M a n : ℕ} (hX : 2≤X) (hM : X<M+a)
    (hp : Nat.Prime (M+a)) (F : (Fin (n+1) → ℝ) → ℝ)
    {rho : ℝ} (hrho : rho<1) (hb : HasBudget F rho) (b : Fin n → ℕ) :
    divisorSum X F M (Fin.snoc b a)=divisorSum X (fun v => F (Fin.snoc v 0)) M b := by
  rw [divisorSum_snoc,hp.divisors]
  rw [Finset.sum_insert (by simpa using hp.ne_one.symm),Finset.sum_singleton]
  have hz : (∑ d∈Fintype.piFinset (fun i => (M+b i).divisors),
      divisorCoefficient X F (Fin.snoc d (M+a)))=0 := by
    apply Finset.sum_eq_zero
    intro d hd
    exact divisorCoefficient_snoc_prime_zero hX hM F hrho hb d
      (fun i => Nat.pos_of_mem_divisors ((Fintype.mem_piFinset.mp hd) i))
  rw [hz,add_zero]
  apply Finset.sum_congr rfl
  intro d _
  exact divisorCoefficient_snoc_one X F d

theorem rayVector_fiber_nonneg {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (y : doubleFibers b R → ℝ) (hy : ∀ r, 0≤y r) (i : ι) :
    0≤rayVector (fun r : doubleFibers b R => fiberRay b r.val) y i := by
  classical
  simp only [rayVector,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,fiberRay_apply]
  exact Finset.sum_nonneg (fun r _ => mul_nonneg (hy r) (by split_ifs <;> norm_num))

theorem rayVector_singleton_zero {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (i : ι)
    (hi : (Finset.univ.filter fun j => b j=b i).card=1)
    (y : doubleFibers b R → ℝ) :
    rayVector (fun r : doubleFibers b R => fiberRay b r.val) y i=0 := by
  classical
  simp only [rayVector,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,fiberRay_apply]
  apply Finset.sum_eq_zero
  intro r _
  have hr : b i≠r.val := by
    intro he
    have hh := (Finset.mem_filter.mp r.property).2
    rw [←he,hi] at hh
    norm_num at hh
  simp [hr]

theorem cumulativeProfile_kernel_small_fibers {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ positiveSimplex n tau)
    {α : Type*} (b : Fin n → α) (R : Finset α) (hR : ∀ i,b i∈R)
    (hcard : ∀ r∈R, (Finset.univ.filter fun i => b i=r).card≤2)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (cumulativeProfile tau f v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (cumulativeProfile tau f v.ofLp:ℂ))) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin n))
      (fun v => (cumulativeProfile tau f v.ofLp:ℂ)) hF hFs) (fiberSubsetFamily b R) =
      ∫ y, (f (rayVector (fun r : doubleFibers b R => fiberRay b r.val) y).ofLp:ℂ)
        ∂positiveOrthantMeasure (doubleFibers b R) := by
  rw [small_fiber_kernelConstant b R hR hcard]
  apply integral_congr_ae
  rw [positiveOrthantMeasure_eq_restrict]
  filter_upwards [ae_restrict_mem (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioi))] with y hy
  exact cumulativeProfile_signed_full tau f hf hfs hsupp _
    (rayVector_fiber_nonneg b R y (fun r => (hy r (Set.mem_univ r)).le))

theorem cumulativeProfile_kernel_singleton_zero {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ positiveSimplex n tau)
    {α : Type*} (b : Fin n → α) (R : Finset α) (hR : ∀ i,b i∈R)
    (hcard : ∀ r∈R, (Finset.univ.filter fun i => b i=r).card≤2)
    (i : Fin n) (hi : (Finset.univ.filter fun j => b j=b i).card=1)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (cumulativeProfile tau f v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (cumulativeProfile tau f v.ofLp:ℂ))) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin n))
      (fun v => (cumulativeProfile tau f v.ofLp:ℂ)) hF hFs) (fiberSubsetFamily b R)=0 := by
  rw [cumulativeProfile_kernel_small_fibers f hf hfs hsupp b R hR hcard]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  have hz : f (rayVector (fun r : doubleFibers b R => fiberRay b r.val) y).ofLp=0 := by
    by_contra hne
    have hh := (hsupp (subset_tsupport f hne)).1 i
    have he := rayVector_singleton_zero b R i hi y
    change 0<rayVector (fun r : doubleFibers b R => fiberRay b r.val) y i at hh
    rw [he] at hh
    exact lt_irrefl _ hh
  simp [hz]

theorem castAdd_ne_addNat_self {n : ℕ} (i j : Fin n) : i.castAdd n ≠ j.addNat n := by
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_addNat] at hval
  omega

theorem addNat_ne_castAdd_self {n : ℕ} (i j : Fin n) : i.addNat n ≠ j.castAdd n :=
  (castAdd_ne_addNat_self j i).symm

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_EqualityPatterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem sum_patterns {ι α K : Type*} [Fintype ι] [Fintype α] [AddCommMonoid K]
    (f : (ι → α) → K) :
    (∑ r : Setoid ι, ∑ b∈patternClass (α:=α) r, f b)=∑ b : ι → α, f b := by
  classical
  simp only [patternClass]
  exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _

theorem append_fiber_card {m n : ℕ} {α : Type*} (a : Fin m → α) (b : Fin n → α) (r : α) :
    (Finset.univ.filter fun i => Fin.append a b i=r).card=
      (Finset.univ.filter fun i => a i=r).card+(Finset.univ.filter fun i => b i=r).card := by
  classical
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Fin.sum_univ_add,Fin.append_left,Fin.append_right]

theorem append_fiber_card_le_two {m n : ℕ} {α : Type*}
    (a : Fin m → α) (b : Fin n → α) (ha : Function.Injective a) (hb : Function.Injective b) (r : α) :
    (Finset.univ.filter fun i => Fin.append a b i=r).card≤2 := by
  classical
  rw [append_fiber_card]
  have h1 : (Finset.univ.filter fun i => a i=r).card≤1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact ha ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  have h2 : (Finset.univ.filter fun i => b i=r).card≤1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact hb ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  omega

theorem append_left_singleton {m n : ℕ} {α : Type*}
    (a : Fin m → α) (b : Fin n → α) (ha : Function.Injective a)
    (i : Fin m) (hi : a i∉Set.range b) :
    (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b (i.castAdd n)).card=1 := by
  classical
  have he : (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b (i.castAdd n))=
      {i.castAdd n} := by
    ext j
    cases j using Fin.addCases with
    | left j => simp [ha.eq_iff]
    | right j =>
      have hn : b j≠a i := fun h => hi ⟨j,h⟩
      have hne : Fin.natAdd m j≠i.castAdd n := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
        omega
      simp [hn,hne]
  rw [he,Finset.card_singleton]

theorem append_right_singleton {m n : ℕ} {α : Type*}
    (a : Fin m → α) (b : Fin n → α) (hb : Function.Injective b)
    (i : Fin n) (hi : b i∉Set.range a) :
    (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b (i.natAdd m)).card=1 := by
  classical
  have he : (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b (i.natAdd m))=
      {i.natAdd m} := by
    ext j
    cases j using Fin.addCases with
    | left j =>
      have hn : a j≠b i := fun h => hi ⟨j,h⟩
      have hne : j.castAdd n≠Fin.natAdd m i := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
        omega
      simp [hn,hne]
    | right j => simp [hb.eq_iff]
  rw [he,Finset.card_singleton]

theorem cumulative_tensor_unmatched_kernel_zero {m n : ℕ} {tau : ℝ}
    (f : (Fin m → ℝ) → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f ⊆ positiveSimplex m tau) (hsg : tsupport g ⊆ positiveSimplex n tau)
    {α : Type*} (a : Fin m → α) (b : Fin n → α)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : Set.range a≠Set.range b)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (m+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f g) v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (m+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f g) v.ofLp:ℂ))) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin (m+n)))
      (fun v => (cumulativeProfile (tau+tau) (tensorProfile f g) v.ofLp:ℂ)) hF hFs)
      (fiberSubsetFamily (Fin.append a b) (Finset.univ.image (Fin.append a b)))=0 := by
  classical
  have hh : ∃ i : Fin (m+n),
      (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b i).card=1 := by
    by_cases hsub : Set.range a⊆Set.range b
    · have hnot : ¬Set.range b⊆Set.range a := fun h => hab (Set.Subset.antisymm hsub h)
      obtain ⟨v,⟨i,rfl⟩,hi⟩ := Set.not_subset.mp hnot
      exact ⟨i.natAdd m,append_right_singleton a b hb i hi⟩
    · obtain ⟨v,⟨i,rfl⟩,hi⟩ := Set.not_subset.mp hsub
      exact ⟨i.castAdd n,append_left_singleton a b ha i hi⟩
  obtain ⟨i,hi⟩ := hh
  exact cumulativeProfile_kernel_singleton_zero (tensorProfile f g)
    (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs)
    (tensorProfile_tsupport f g hsf hsg) (Fin.append a b) _
    (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ _))
    (fun r _ => append_fiber_card_le_two a b ha hb r) i hi hF hFs

theorem blockLength_ratio_tendsto {lam : ℝ} (hlam : 0≤lam) :
    Tendsto (fun X : ℕ => (blockLength lam X:ℝ)/Real.log X) atTop (𝓝 lam) := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp hlog
  have hlo : Tendsto (fun X : ℕ => lam-(Real.log (X:ℝ))⁻¹) atTop (𝓝 lam) := by
    simpa using tendsto_const_nhds.sub hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 2] with X hX
    have hL := log_pos_of_two_le hX
    apply (le_div_iff₀ hL).mpr
    have hh := (Nat.lt_floor_add_one (lam*Real.log (X:ℝ))).le
    dsimp [blockLength]
    have he : (lam-(Real.log (X:ℝ))⁻¹)*Real.log X=lam*Real.log X-1 := by
      field_simp
    rw [he]
    linarith
  · filter_upwards [eventually_ge_atTop 2] with X hX
    exact (div_le_iff₀ (log_pos_of_two_le hX)).mpr (blockLength_le_mul_log hlam hX)

theorem blockLength_tendsto {lam : ℝ} (hlam : 0<lam) :
    Tendsto (blockLength lam) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hlam)

theorem blockLength_densityCutoff_eventually {lam : ℝ} (hlam : 0≤lam) (K : ℕ) :
    ∀ᶠ X : ℕ in atTop, K*blockLength lam X≤densityCutoff 2 (Real.log X) := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,hlog.eventually_ge_atTop ((K:ℝ)*lam)] with X hX hL
  apply (Nat.le_floor_iff (by positivity : 0≤(Real.log (X:ℝ))^2)).mpr
  push_cast
  have hh := blockLength_le_mul_log hlam hX
  nlinarith [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg K),
    mul_le_mul_of_nonneg_right hL (log_pos_of_two_le hX).le]

theorem uniform_singularBoxMean_tendsto (s : ℕ) {K : ℕ} (hK : 0<K)
    (H : ℕ → ℕ) (a : ℕ → Fin s → ℤ) (hH : Tendsto H atTop atTop)
    (hdiam : ∀ᶠ X : ℕ in atTop, boxDiameterBound (h:=H X) (a X) (K*H X)) :
    Tendsto (fun X => singularBoxMean (h:=H X) (a X)) atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨h₀,hh₀⟩ := singularBoxMean_uniform s hK hε
  filter_upwards [hH.eventually_ge_atTop h₀,hdiam] with X hX hd
  exact (by simpa only [Real.dist_eq] using hh₀ (H X) hX (a X) hd)

theorem numericPattern_ker {ι : Type*} [Fintype ι] (r : Setoid ι) :
    Setoid.ker (numericPattern r)=r := by
  apply Setoid.ext
  intro i j
  change (Fintype.equivFin (Quotient r) (Quotient.mk r i)).val=
    (Fintype.equivFin (Quotient r) (Quotient.mk r j)).val ↔ r i j
  rw [Fin.val_inj,(Fintype.equivFin (Quotient r)).injective.eq_iff,Quotient.eq]

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_Detectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem ker_comp_injective {ι α β : Type*} (b : ι → α) (f : α → β) (hf : Function.Injective f) :
    Setoid.ker (f∘b)=Setoid.ker b := by
  apply Setoid.ext
  intro i j
  exact hf.eq_iff

theorem numericPattern_int_ker {ι : Type*} [Fintype ι] (r : Setoid ι) :
    Setoid.ker (fun i => (numericPattern r i:ℤ))=r := by
  have h := ker_comp_injective (numericPattern r) (fun n : ℕ => (n:ℤ)) (by intro m n hm; exact_mod_cast (show (m:ℤ)=(n:ℤ) from hm))
  exact h.trans (numericPattern_ker r)

theorem shiftFamily_eq_of_ker {ι : Type*} [Fintype ι] (b c : ι → ℤ)
    (h : Setoid.ker b=Setoid.ker c) : shiftFamily b=shiftFamily c := by
  classical
  ext S
  simp only [shiftFamily,mem_fiberSubsetFamily_image]
  have hc (i j : ι) : b i=b j ↔ c i=c j := by
    change (Setoid.ker b) i j ↔ (Setoid.ker c) i j
    rw [h]
  constructor <;> rintro ⟨hS,he⟩
  · exact ⟨hS,fun i hi j hj => (hc i j).mp (he i hi j hj)⟩
  · exact ⟨hS,fun i hi j hj => (hc i j).mpr (he i hi j hj)⟩

theorem patternBoxShifts_family {n s h : ℕ} (p : Fin n → Fin s)
    (a : Fin s → ℕ) (u : Fin s → Fin h)
    (hu : u∈distinctBox (fun j => (a j:ℤ))) :
    shiftFamily (fun i => (patternBoxShifts p a u i:ℤ))=
      shiftFamily (fun i => ((p i).val:ℤ)) := by
  apply shiftFamily_eq_of_ker
  apply Setoid.ext
  intro i j
  have hi := (Finset.mem_filter.mp hu).2
  change ((patternBoxShifts p a u i:ℤ)=(patternBoxShifts p a u j:ℤ)) ↔
    ((p i).val:ℤ)=((p j).val:ℤ)
  have he (i : Fin n) : (patternBoxShifts p a u i:ℤ)=boxTuple (fun j => (a j:ℤ)) u (p i) := by
    simp only [patternBoxShifts,boxTuple,Nat.cast_add]
  rw [he,he,hi.eq_iff]
  constructor
  · intro h; rw [h]
  · intro h; apply Fin.ext; exact_mod_cast h

theorem patternBoxShifts_image {n s h : ℕ} (p : Fin n → Fin s)
    (hp : Function.Surjective p) (a : Fin s → ℕ) (u : Fin s → Fin h) :
    (Finset.univ.image fun i => (patternBoxShifts p a u i:ℤ))=
      Finset.univ.image (boxTuple (fun j => (a j:ℤ)) u) := by
  classical
  ext x
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨p i,by simp only [boxTuple,patternBoxShifts,Nat.cast_add]⟩
  · rintro ⟨j,rfl⟩
    obtain ⟨i,rfl⟩ := hp j
    exact ⟨i,by simp only [boxTuple,patternBoxShifts,Nat.cast_add]⟩

theorem surjective_shiftFamily_sign_sum {n s : ℕ} (p : Fin n → Fin s)
    (hp : Function.Surjective p) :
    (∑ S∈shiftFamily (fun i => ((p i).val:ℤ)),(-1:ℤ)^S.card)=-(s:ℤ) := by
  classical
  rw [shiftFamily_sign_sum]
  have he : (Finset.univ.image fun i => ((p i).val:ℤ))=
      Finset.univ.image (fun j : Fin s => (j.val:ℤ)) := by
    ext x
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨p i,rfl⟩
    · rintro ⟨j,rfl⟩; obtain ⟨i,rfl⟩ := hp j; exact ⟨i,rfl⟩
  rw [he,Finset.card_image_of_injective]
  · simp only [Finset.card_univ,Fintype.card_fin]
  · intro i j hij; apply Fin.ext; exact_mod_cast (show (i.val:ℤ)=(j.val:ℤ) from hij)

theorem box_sum_scaled_norm_le {s h : ℕ} (a : Fin s → ℤ)
    (f g : (Fin s → Fin h) → ℂ) {L E : ℝ} (hL : 0<L) (hE : 0≤E)
    (herr : ∀ u∈distinctBox a, ‖(L:ℂ)^s*f u-g u‖≤E) :
    ‖(∑ u∈distinctBox a,f u)-(∑ u∈distinctBox a,g u)/(L:ℂ)^s‖≤((h:ℝ)/L)^s*E := by
  classical
  have hb : ‖∑ u∈distinctBox a,((L:ℂ)^s*f u-g u)‖≤(h:ℝ)^s*E := by
    calc
      _ ≤ ∑ _u∈distinctBox (h:=h) a,E := norm_sum_le_of_le _ herr
      _ = ((distinctBox (h:=h) a).card:ℝ)*E := by simp
      _ ≤ (h:ℝ)^s*E := by
        apply mul_le_mul_of_nonneg_right _ hE
        have hc := Finset.card_le_card (show distinctBox (h:=h) a⊆Finset.univ from Finset.subset_univ _)
        simpa only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using
          (show ((distinctBox (h:=h) a).card:ℝ)≤(Fintype.card (Fin s → Fin h):ℝ) from by exact_mod_cast hc)
  rw [Finset.sum_sub_distrib,←Finset.mul_sum] at hb
  have hLc : (L:ℂ)≠0 := by exact_mod_cast ne_of_gt hL
  have he : (∑ u∈distinctBox a,f u)-(∑ u∈distinctBox a,g u)/(L:ℂ)^s=
      ((L:ℂ)^s*(∑ u∈distinctBox a,f u)-∑ u∈distinctBox a,g u)/(L:ℂ)^s := by
    field_simp [hLc]
  rw [he,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  apply (div_le_iff₀ (pow_pos hL _)).mpr
  apply le_trans hb
  apply le_of_eq
  rw [div_pow]
  field_simp

theorem box_sum_errors_tendsto_zero (s : ℕ) (H : ℕ → ℕ) (a : ℕ → Fin s → ℤ)
    (L E : ℕ → ℝ) (lam : ℝ)
    (f g : (X : ℕ) → (Fin s → Fin (H X)) → ℂ)
    (hL : ∀ᶠ X in atTop,0<L X)
    (hHL : Tendsto (fun X => (H X:ℝ)/L X) atTop (𝓝 lam))
    (hE : Tendsto E atTop (𝓝 0))
    (herr : ∀ᶠ X in atTop, ∀ u∈distinctBox (a X),‖(L X:ℂ)^s*f X u-g X u‖≤E X) :
    Tendsto (fun X => (∑ u∈distinctBox (a X),f X u)-
      (∑ u∈distinctBox (a X),g X u)/(L X:ℂ)^s) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a:=fun X => ((H X:ℝ)/L X)^s*|E X|)
  · filter_upwards [hL,herr] with X hLX hX
    exact box_sum_scaled_norm_le (a X) (f X) (g X) hLX (abs_nonneg _) (fun u hu =>
      (hX u hu).trans (le_abs_self _))
  · simpa only [abs_zero,mul_zero] using (hHL.pow s).mul hE.abs

theorem natural_boxDiameterBound {s h K : ℕ} (a : Fin s → ℕ) (ha : ∀ j,a j≤K*h) :
    boxDiameterBound (h:=h) (fun j => (a j:ℤ)) ((K+1)*h) := by
  intro u i j
  dsimp [boxTuple]
  have hi := (u i).isLt
  have hj := (u j).isLt
  have hai := ha i
  have haj := ha j
  have hk : K*h+h=(K+1)*h := by ring
  omega

theorem average_const_mul (X : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    average X (fun m => c*f m)=c*average X f := by
  simp only [average,←Finset.mul_sum,mul_div_assoc]

theorem average_finset_sum {α : Type*} (X : ℕ) (S : Finset α) (f : α → ℕ → ℝ) :
    average X (fun m => ∑ i∈S,f i m)=∑ i∈S,average X (f i) := by
  unfold average
  rw [Finset.sum_comm,Finset.sum_div]

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_PatternMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem box_series_scaled_tendsto {s K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → Fin s → ℕ)
    (ha : ∀ᶠ X : ℕ in atTop, ∀ j,a X j≤K*blockLength lam X) (c : ℂ) :
    Tendsto (fun X : ℕ =>
      (∑ u∈distinctBox (h:=blockLength lam X) (fun j => (a X j:ℤ)),
        (singularSeries (Finset.univ.image (boxTuple (fun j => (a X j:ℤ)) u)):ℂ)*c)/
        (Real.log X:ℂ)^s) atTop (𝓝 ((lam:ℂ)^s*c)) := by
  classical
  let H := blockLength lam
  let az := fun X j => (a X j:ℤ)
  have hL : ∀ᶠ X : ℕ in atTop,0<Real.log X := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    exact log_pos_of_two_le hX
  have hHL := blockLength_ratio_tendsto hlam.le
  have hmean : Tendsto (fun X => singularBoxMean (h:=H X) (az X)) atTop (𝓝 1) := by
    apply uniform_singularBoxMean_tendsto s (K:=K+1) (by omega) H az (blockLength_tendsto hlam)
    filter_upwards [ha] with X hX
    exact natural_boxDiameterBound (a X) hX
  have hh := ((Complex.continuous_ofReal.continuousAt.tendsto.comp hHL).pow s).mul
    (Complex.continuous_ofReal.continuousAt.tendsto.comp hmean)
  have hh' := hh.mul_const c
  simp only [Complex.ofReal_one,mul_one] at hh'
  apply hh'.congr'
  filter_upwards [hL,(blockLength_tendsto hlam).eventually_ge_atTop 1] with X hLX hHX
  have hHC : ((H X:ℕ):ℂ)≠0 := by exact_mod_cast (show H X≠0 by dsimp [H]; omega)
  have hLC : (Real.log X:ℂ)≠0 := by exact_mod_cast ne_of_gt hLX
  change (((H X:ℝ)/(Real.log X):ℝ):ℂ)^s * (singularBoxMean (h:=H X) (az X):ℂ)*c = _
  simp only [←Finset.sum_mul,←Complex.ofReal_sum,singularBoxMean,
    Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
  dsimp only [az,H]
  dsimp only [H] at hHC
  rw [div_pow]
  field_simp [hHC]

theorem distinctBox_init {s h : ℕ} (a : Fin (s+1) → ℕ) (u : Fin (s+1) → Fin h)
    (hu : u∈distinctBox (fun j => (a j:ℤ))) :
    (fun j : Fin s => u j.castSucc)∈distinctBox (fun j : Fin s => (a j.castSucc:ℤ)) := by
  classical
  simp only [distinctBox,Finset.mem_filter,Finset.mem_univ,true_and] at hu ⊢
  exact hu.comp (Fin.castSucc_injective s)

theorem patternBoxShifts_ne_mark {n s h : ℕ} (p : Fin n → Fin s)
    (a : Fin (s+1) → ℕ) (u : Fin (s+1) → Fin h)
    (hu : u∈distinctBox (fun j => (a j:ℤ))) (i : Fin n) :
    patternBoxShifts p (fun j => a j.castSucc) (fun j => u j.castSucc) i≠
      a (Fin.last s)+(u (Fin.last s):ℕ) := by
  intro he
  have hj : boxTuple (fun j => (a j:ℤ)) u (p i).castSucc=
      boxTuple (fun j => (a j:ℤ)) u (Fin.last s) := by
    dsimp only [patternBoxShifts] at he
    dsimp only [boxTuple]
    exact_mod_cast he
  have hi := (Finset.mem_filter.mp hu).2 hj
  exact Fin.castSucc_ne_last (p i) hi

theorem marked_patternBoxShifts_image {n s h : ℕ} (p : Fin n → Fin s)
    (hp : Function.Surjective p) (a : Fin (s+1) → ℕ) (u : Fin (s+1) → Fin h) :
    insert ((a (Fin.last s)+(u (Fin.last s):ℕ):ℕ):ℤ)
      (Finset.univ.image fun i => (patternBoxShifts p (fun j => a j.castSucc)
        (fun j => u j.castSucc) i:ℤ))=
      Finset.univ.image (boxTuple (fun j => (a j:ℤ)) u) := by
  classical
  rw [patternBoxShifts_image p hp]
  ext x
  simp only [Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro (rfl | ⟨j,rfl⟩)
    · exact ⟨Fin.last s,by simp only [boxTuple,Nat.cast_add]⟩
    · exact ⟨j.castSucc,rfl⟩
  · rintro ⟨j,rfl⟩
    cases j using Fin.lastCases with
    | last => left; simp only [boxTuple,Nat.cast_add]
    | cast j => exact Or.inr ⟨j,rfl⟩

theorem marked_box_pattern_limit (hBV : BombieriVinogradov) {n s K : ℕ}
    {lam : ℝ} (hlam : 0<lam) (p : Fin n → Fin s) (hp : Function.Surjective p)
    (a : ℕ → Fin (s+1) → ℕ)
    (ha : ∀ᶠ X : ℕ in atTop, ∀ j,a X j≤K*blockLength lam X)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ u∈distinctBox (h:=blockLength lam X) (fun j => (a X j:ℤ)),
      (average X (fun m => divisorSum X F m
        (patternBoxShifts p (fun j => a X j.castSucc) (fun j => u j.castSucc))*
        theta (m+(a X (Fin.last s)+(u (Fin.last s):ℕ)))):ℂ)/(Real.log X:ℂ)) atTop
      (𝓝 ((lam:ℂ)^(s+1)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin n))
          (fun v => (F v.ofLp:ℂ)) hF hFs) (shiftFamily (fun i => ((p i).val:ℤ))))) := by
  classical
  let B := shiftFamily (fun i => ((p i).val:ℤ))
  let c := kernelConstant (sourceFourier (fourierCoordinateSum (Fin n))
    (fun v => (F v.ofLp:ℂ)) hF hFs) B
  let H := blockLength lam
  let az := fun X j => (a X j:ℤ)
  let f := fun X (u : Fin (s+1) → Fin (H X)) =>
    (average X (fun m => divisorSum X F m
      (patternBoxShifts p (fun j => a X j.castSucc) (fun j => u j.castSucc))*
      theta (m+(a X (Fin.last s)+(u (Fin.last s):ℕ)))):ℂ)/(Real.log X:ℂ)
  let g := fun X (u : Fin (s+1) → Fin (H X)) =>
    (singularSeries (Finset.univ.image (boxTuple (az X) u)):ℂ)*c
  have hD : (0:ℝ)<(K+1:ℕ)*lam := mul_pos (by positivity) hlam
  have hH : ∀ᶠ X : ℕ in atTop, (((K+1)*H X:ℕ):ℝ)≤((K+1:ℕ):ℝ)*lam*(Real.log X)^(1:ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    simpa only [Nat.cast_mul,Real.rpow_one,mul_assoc] using
      mul_le_mul_of_nonneg_left (blockLength_le_mul_log hlam.le hX) (Nat.cast_nonneg (K+1))
  obtain ⟨E,hE,herr⟩ := marked_average_uniform_asymptotic hBV F rho hrho hrhohalf hbudget
    hF hFs M hM hbound B (shiftFamily_nonempty _) s 2 (by omega)
    (surjective_shiftFamily_sign_sum p hp) (fun X => (K+1)*H X) hD hH
  have hL : ∀ᶠ X : ℕ in atTop,0<Real.log X := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    exact log_pos_of_two_le hX
  have herror : ∀ᶠ X in atTop, ∀ u∈distinctBox (az X),
      ‖(Real.log X:ℂ)^(s+1)*f X u-g X u‖≤E X := by
    filter_upwards [herr,ha,hL,blockLength_densityCutoff_eventually hlam.le (2*(K+1))]
      with X hX haX hLX hcut
    intro u hu
    have hb (j : Fin (s+1)) : a X j+(u j:ℕ)≤(K+1)*H X := by
      have hi := (u j).isLt
      have hh := haX j
      dsimp [H] at hi
      dsimp [H]
      rw [Nat.add_mul,one_mul]
      omega
    have hz := hX (patternBoxShifts p (fun j => a X j.castSucc) (fun j => u j.castSucc))
      (patternBoxShifts_family p _ _ (distinctBox_init (a X) u hu))
      (a X (Fin.last s)+(u (Fin.last s):ℕ)) (hb (Fin.last s))
      (patternBoxShifts_ne_mark p (a X) u hu) ((K+1)*H X)
      (fun i => hb (p i).castSucc) (hb (Fin.last s))
      (by simpa only [Nat.mul_assoc] using hcut)
    rw [marked_patternBoxShifts_image p hp] at hz
    have hLC : (Real.log X:ℂ)≠0 := by exact_mod_cast ne_of_gt hLX
    convert hz using 1
    dsimp [f,g,c,az]
    congr 1
    rw [pow_succ]
    field_simp
  have he := box_sum_errors_tendsto_zero (s+1) H az (fun X => Real.log X) E lam f g
    hL (blockLength_ratio_tendsto hlam.le) hE herror
  have hmain : Tendsto (fun X => (∑ u∈distinctBox (az X),g X u)/(Real.log X:ℂ)^(s+1))
      atTop (𝓝 ((lam:ℂ)^(s+1)*c)) := by
    simpa only [g,az,H,←Finset.sum_mul] using box_series_scaled_tendsto hlam a ha c
  have hh := he.add hmain
  simp only [sub_add_cancel,zero_add] at hh
  exact hh

theorem patternLabels_surjective {ι : Type*} [Fintype ι] (r : Setoid ι) :
    Function.Surjective (patternLabels r) := by
  intro j
  obtain ⟨i,hi⟩ := Quotient.mk_surjective ((Fintype.equivFin (Quotient r)).symm j)
  refine ⟨i,?_⟩
  simp only [patternLabels,hi,Equiv.apply_symm_apply]

theorem patternTupleEquiv_labels {n : ℕ} (r : Setoid (Fin n)) (h a : ℕ)
    (b : {b // b∈patternClass (α:=Fin h) r}) :
    patternBoxShifts (patternLabels r) (fun _ => a)
      (patternTupleEquiv r h a b).val=(fun i => a+(b.val i:ℕ)) := by
  funext i
  simp only [patternBoxShifts,patternLabels,patternTupleEquiv_apply,Equiv.symm_apply_apply]
  rfl

theorem permutedLabels_fiber_sum {n : ℕ} (e : Equiv.Perm (Fin n)) (r : Fin n) {K : Type*} [AddCommMonoid K]
    (w : Fin (n+n) → K) :
    (∑ i∈Finset.univ.filter (fun i => permutedLabels e i=r), w i)=w (r.castAdd n)+w ((e.symm r).natAdd n) := by
  classical
  rw [Finset.sum_filter,Fin.sum_univ_add]
  simp [permutedLabels,←Equiv.eq_symm_apply]

@[simp] theorem permutedLabels_fiber_card {n : ℕ} (e : Equiv.Perm (Fin n)) (r : Fin n) :
    (Finset.univ.filter fun i => permutedLabels e i=r).card=2 := by
  simpa using permutedLabels_fiber_sum e r (fun _ => (1:ℕ))

theorem permutedLabels_classical_fiber {n : ℕ} (e : Equiv.Perm (Fin n)) (r : Fin n) :
    @Finset.filter (Fin (n+n)) (fun i => permutedLabels e i=r)
      (fun _ => Classical.propDecidable _) Finset.univ =
      Finset.univ.filter (fun i => permutedLabels e i=r) := by
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

theorem permutedLabels_kernel {n : ℕ} (e : Equiv.Perm (Fin n)) (w : Fin (n+n) → ℂ) :
    familyKernel (fiberSubsetFamily (permutedLabels e) Finset.univ) w =
      (∏ i,w i)*(∏ i : Fin n,(w (i.castAdd n)+w ((e.symm i).natAdd n))⁻¹) := by
  rw [familyKernel_small_fibers (permutedLabels e) Finset.univ (fun i => Finset.mem_univ _) (by
    intro r _
    rw [permutedLabels_classical_fiber,permutedLabels_fiber_card])]
  simp only [permutedLabels_classical_fiber,permutedLabels_fiber_card,Finset.filter_true,
    permutedLabels_fiber_sum]

theorem permutedRay_frequency {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) (u : EuclideanSpace ℝ (Fin (n+n))) :
    laplaceFrequency (fourierCoordinateSum (Fin (n+n))) (permutedRay e i) u =
      frequencyW (u (i.castAdd n))+frequencyW (u ((e.symm i).natAdd n)) := by
  unfold permutedRay
  simp only [laplaceFrequency,map_add,inner_add_right,Complex.ofReal_add,
    fourierCoordinateSum_apply]
  simp [frequencyW,EuclideanSpace.inner_single_right]
  ring

theorem permutedRay_positive {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    0<fourierCoordinateSum (Fin (n+n)) (permutedRay e i) := by
  have h := congrArg Complex.re (permutedRay_frequency e i 0)
  simp only [laplaceFrequency_re,Complex.add_re,frequencyW_re] at h
  rw [h]
  norm_num

theorem rayVector_permuted {n : ℕ} (e : Equiv.Perm (Fin n)) (y : Fin n → ℝ) :
    (rayVector (permutedRay e) y).ofLp=Fin.append y (y ∘ e) := by
  classical
  ext i
  cases i using Fin.addCases with
  | left i => simp [rayVector,permutedRay,WithLp.ofLp_sum,Finset.sum_apply,
      smul_eq_mul,Pi.single_apply,Finset.sum_add_distrib,castAdd_ne_addNat_self]
  | right i =>
    have he (x : Fin n) : i=e.symm x ↔ x=e i := by
      constructor
      · intro h; rw [h]; simp
      · intro h; rw [h]; simp
    simp [rayVector,permutedRay,WithLp.ofLp_sum,Finset.sum_apply,
      smul_eq_mul,Pi.single_apply,Finset.sum_add_distrib,addNat_ne_castAdd_self,he]

theorem permuted_kernelConstant {n : ℕ} (e : Equiv.Perm (Fin n))
    (F : EuclideanSpace ℝ (Fin (n+n)) → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin (n+n))) F hF hFs)
      (fiberSubsetFamily (permutedLabels e) Finset.univ) =
      ∫ y, signedDirections (coordinateDirectionList (Fin (n+n))) F (rayVector (permutedRay e) y)
        ∂positiveOrthantMeasure (Fin n) := by
  rw [←sourceFourier_derivative_laplace (fourierCoordinateSum (Fin (n+n)))
    (coordinateDirectionList (Fin (n+n))) F hF hFs (permutedRay e) (permutedRay_positive e)]
  unfold kernelConstant
  apply integral_congr_ae
  filter_upwards [] with u
  rw [contourKernel,permutedLabels_kernel,coordinateDirectionList_multiplier]
  simp only [permutedRay_frequency,mul_assoc]

theorem cumulative_tensor_permuted_kernel {n : ℕ} (e : Equiv.Perm (Fin n)) {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ positiveSimplex n tau) (hsym : SymmetricFunction f)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ))) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin (n+n)))
      (fun v => (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)) hF hFs)
      (fiberSubsetFamily (permutedLabels e) Finset.univ) = (l2Mass f:ℂ) := by
  rw [permuted_kernelConstant]
  have he : (∫ y, signedDirections (coordinateDirectionList (Fin (n+n)))
      (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
        (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)) (rayVector (permutedRay e) y)
      ∂positiveOrthantMeasure (Fin n)) =
      ∫ y, (f y^2:ℂ) ∂positiveOrthantMeasure (Fin n) := by
    apply integral_congr_ae
    rw [positiveOrthantMeasure_eq_restrict]
    filter_upwards [ae_restrict_mem (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioi))] with y hy
    rw [cumulativeProfile_signed_full (tau+tau) (tensorProfile f f)
      (tensorProfile_compact f f hf hf) (tensorProfile_smooth f f hfs hfs)
      (tensorProfile_tsupport f f hsupp hsupp)]
    · rw [rayVector_permuted,tensorProfile_append,hsym,pow_two]
      simp only [Complex.ofReal_mul]
    · intro i
      rw [rayVector_permuted]
      cases i using Fin.addCases with
      | left i => simpa using (hy i (Set.mem_univ i)).le
      | right i => simpa using (hy (e i) (Set.mem_univ (e i))).le
  rw [he]
  simp_rw [←Complex.ofReal_pow]
  rw [integral_complex_ofReal,positiveOrthantMeasure_eq_restrict]
  congr 1
  unfold l2Mass
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hfz : f y=0 := by
    by_contra hne
    exact hy (fun i _ => (hsupp (subset_tsupport f hne)).1 i)
  simp [hfz]

theorem injective_same_range_perm {n : ℕ} {α : Type*}
    (a b : Fin n → α) (hb : Function.Injective b)
    (hab : Set.range a=Set.range b) : ∃ e : Equiv.Perm (Fin n), b=a ∘ e := by
  classical
  have hs : ∀ i,∃ j,a j=b i := by
    intro i
    have : b i ∈ Set.range a := hab.symm ▸ Set.mem_range_self i
    exact this
  choose e he using hs
  have hei : Function.Injective e := by
    intro i j hij
    apply hb
    rw [←he i,←he j,hij]
  exact ⟨Equiv.ofBijective e ⟨hei,Finite.surjective_of_injective hei⟩,by funext i; exact (he i).symm⟩

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_WeightMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem blockOffset_eventually {lam : ℝ} (hlam : 0<lam) :
    ∀ᶠ X : ℕ in atTop,blockLength lam X+1≤2*blockLength lam X := by
  filter_upwards [(blockLength_tendsto hlam).eventually_ge_atTop 1] with X hX
  omega

theorem matchedPattern_injective {n : ℕ} : Function.Injective (@matchedPattern n) := by
  intro e f hef
  apply Equiv.ext
  intro i
  have he : (matchedPattern e) ((e i).castAdd n) (i.natAdd n) := by
    change permutedLabels e ((e i).castAdd n)=permutedLabels e (i.natAdd n)
    simp [permutedLabels]
  rw [hef] at he
  change permutedLabels f ((e i).castAdd n)=permutedLabels f (i.natAdd n) at he
  simpa [permutedLabels] using he

theorem matchedPattern_quotient_card {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Fintype.card (Quotient (matchedPattern e))=n := by
  have hs : Function.Surjective (permutedLabels e) := by
    intro j
    exact ⟨j.castAdd n,by simp [permutedLabels]⟩
  have eqv : Quotient (matchedPattern e) ≃ Fin n :=
    Setoid.quotientKerEquivOfSurjective (permutedLabels e) hs
  exact (Fintype.card_congr eqv).trans (Fintype.card_fin n)

theorem ker_eq_bot_iff_injective {α β : Type*} (f : α → β) :
    Setoid.ker f=⊥ ↔ Function.Injective f := by
  constructor
  · intro h x y hxy
    change (Setoid.ker f) x y at hxy
    rw [h] at hxy
    exact hxy
  · intro h
    apply Setoid.ext
    intro x y
    exact h.eq_iff

theorem numericPattern_left_injective {m n : ℕ} (r : Setoid (Fin (m+n)))
    (h : Setoid.comap (Fin.castAdd n) r=⊥) :
    Function.Injective (fun i : Fin m => numericPattern r (i.castAdd n)) := by
  apply (ker_eq_bot_iff_injective _).mp
  have he : Setoid.ker (fun i : Fin m => numericPattern r (i.castAdd n))=
      Setoid.comap (Fin.castAdd n) (Setoid.ker (numericPattern r)) := rfl
  rw [he,numericPattern_ker,h]

theorem numericPattern_right_injective {m n : ℕ} (r : Setoid (Fin (m+n)))
    (h : Setoid.comap (Fin.natAdd m) r=⊥) :
    Function.Injective (fun i : Fin n => numericPattern r (i.natAdd m)) := by
  apply (ker_eq_bot_iff_injective _).mp
  have he : Setoid.ker (fun i : Fin n => numericPattern r (i.natAdd m))=
      Setoid.comap (Fin.natAdd m) (Setoid.ker (numericPattern r)) := rfl
  rw [he,numericPattern_ker,h]

theorem injective_ranges_card {m n : ℕ} {α : Type*} (a : Fin m → α) (b : Fin n → α)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : Set.range a=Set.range b) : m=n := by
  have e : Fin m ≃ Fin n := (Equiv.ofInjective a ha).trans
    ((Equiv.setCongr hab).trans (Equiv.ofInjective b hb).symm)
  simpa using Fintype.card_congr e

theorem matching_pattern_eq {n : ℕ} (r : Setoid (Fin (n+n)))
    (hleft : Setoid.comap (Fin.castAdd n) r=⊥)
    (hright : Setoid.comap (Fin.natAdd n) r=⊥)
    (hrange : Set.range (fun i : Fin n => numericPattern r (i.castAdd n))=
      Set.range (fun i : Fin n => numericPattern r (i.natAdd n))) :
    ∃ e : Equiv.Perm (Fin n),r=matchedPattern e := by
  let a := fun i : Fin n => numericPattern r (i.castAdd n)
  let b := fun i : Fin n => numericPattern r (i.natAdd n)
  have ha : Function.Injective a := numericPattern_left_injective r hleft
  have hb : Function.Injective b := numericPattern_right_injective r hright
  obtain ⟨e,he⟩ := injective_same_range_perm a b hb hrange
  refine ⟨e,?_⟩
  rw [←numericPattern_ker r]
  have hf : numericPattern r=a ∘ permutedLabels e := by
    funext i
    cases i using Fin.addCases with
    | left i => simp [a,permutedLabels]
    | right i => simpa [b,permutedLabels] using congrFun he i
  rw [hf,ker_comp_injective _ _ ha]
  rfl

theorem matchedPattern_family {n : ℕ} (e : Equiv.Perm (Fin n)) :
    equalityPatternFamily (matchedPattern e)=fiberSubsetFamily (permutedLabels e) Finset.univ := by
  classical
  have hi : Finset.univ.image (permutedLabels e)=Finset.univ := by
    ext j
    simp only [Finset.mem_image,Finset.mem_univ,true_and,iff_true]
    exact ⟨j.castAdd n,by simp [permutedLabels]⟩
  rw [←hi]
  unfold equalityPatternFamily shiftFamily
  ext S
  simp only [mem_fiberSubsetFamily_image]
  have he (i j : Fin (n+n)) :
      (numericPattern (matchedPattern e) i:ℤ)=(numericPattern (matchedPattern e) j:ℤ) ↔
        permutedLabels e i=permutedLabels e j := by
    change (Setoid.ker (fun x => (numericPattern (matchedPattern e) x:ℤ))) i j ↔
      (matchedPattern e) i j
    rw [numericPattern_int_ker]
  simp_rw [he]

theorem sum_matched_patterns {n : ℕ} (c : ℂ) (A : Setoid (Fin (n+n)) → ℂ)
    (hzero : ∀ r,r∉Set.range (@matchedPattern n) → A r=0)
    (hvalue : ∀ e : Equiv.Perm (Fin n),A (matchedPattern e)=c) :
    (∑ r,A r)=(n.factorial:ℂ)*c := by
  classical
  calc
    _ = ∑ r∈Finset.univ.image (@matchedPattern n),A r := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro r _ hr
      apply hzero r
      rintro ⟨e,rfl⟩
      exact hr (Finset.mem_image_of_mem _ (Finset.mem_univ e))
    _ = ∑ e : Equiv.Perm (Fin n),A (matchedPattern e) :=
      Finset.sum_image (fun _ _ _ _ h => matchedPattern_injective h)
    _ = _ := by simp [hvalue,Fintype.card_perm]

theorem cumulative_pair_unmatched {m n : ℕ} {tau : ℝ}
    (f : (Fin m → ℝ) → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex m tau) (hsg : tsupport g⊆positiveSimplex n tau)
    (r : Setoid (Fin (m+n)))
    (hl : Setoid.comap (Fin.castAdd n) r=⊥) (hr : Setoid.comap (Fin.natAdd m) r=⊥)
    (hne : Set.range (fun i : Fin m => numericPattern r (i.castAdd n))≠
      Set.range (fun i : Fin n => numericPattern r (i.natAdd m))) :
    cumulativePatternKernel (tau+tau) (tensorProfile f g)
      (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r=0 := by
  let a := fun i : Fin m => numericPattern r (i.castAdd n)
  let b := fun i : Fin n => numericPattern r (i.natAdd m)
  have ha := numericPattern_left_injective r hl
  have hb := numericPattern_right_injective r hr
  have he : Fin.append a b=numericPattern r := by
    funext i
    cases i using Fin.addCases <;> simp [a,b]
  have hfamily : equalityPatternFamily r=
      fiberSubsetFamily (Fin.append a b) (Finset.univ.image (Fin.append a b)) := by
    unfold equalityPatternFamily shiftFamily
    ext S
    simp only [mem_fiberSubsetFamily_image,he,Int.natCast_inj]
  unfold cumulativePatternKernel
  rw [hfamily]
  convert cumulative_tensor_unmatched_kernel_zero f g hf hg hfs hgs hsf hsg a b ha hb hne
    (realEuclidean_compact _ (cumulativeProfile_compact _ _ (tensorProfile_compact f g hf hg)))
    (realEuclidean_smooth _ (cumulativeProfile_smooth _ _
      (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs))) using 1
  congr 2
  ext x
  simp

theorem cumulative_pair_matched {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsym : SymmetricFunction f)
    (e : Equiv.Perm (Fin n)) :
    cumulativePatternKernel (tau+tau) (tensorProfile f f)
      (tensorProfile_compact f f hf hf) (tensorProfile_smooth f f hfs hfs) (matchedPattern e)=
      (l2Mass f:ℂ) := by
  unfold cumulativePatternKernel
  rw [matchedPattern_family]
  exact cumulative_tensor_permuted_kernel e f hf hfs hsf hsym _ _

theorem cumulative_square_pattern_sum {n : ℕ} {tau : ℝ} (lam : ℝ)
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsym : SymmetricFunction f) :
    (∑ r : Setoid (Fin (n+n)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*cumulativePatternKernel (tau+tau) (tensorProfile f f)
          (tensorProfile_compact f f hf hf) (tensorProfile_smooth f f hfs hfs) r))=
      (alpha lam n*l2Mass f:ℂ) := by
  classical
  let A := fun r : Setoid (Fin (n+n)) =>
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*cumulativePatternKernel (tau+tau) (tensorProfile f f)
          (tensorProfile_compact f f hf hf) (tensorProfile_smooth f f hfs hfs) r)
  have hz : ∀ r,r∉Set.range (@matchedPattern n) → A r=0 := by
    intro r hr
    by_cases hl : Setoid.comap (Fin.castAdd n) r=⊥
    · by_cases hr' : Setoid.comap (Fin.natAdd n) r=⊥
      · have hne : Set.range (fun i : Fin n => numericPattern r (i.castAdd n))≠
            Set.range (fun i : Fin n => numericPattern r (i.natAdd n)) := by
          intro he
          obtain ⟨e,rfl⟩ := matching_pattern_eq r hl hr' he
          exact hr ⟨e,rfl⟩
        simp only [A,cumulative_pair_unmatched f f hf hf hfs hfs hsf hsf r hl hr' hne,mul_zero]
      · simp only [A,tensorCoefficient,subsetCoefficient,ite_eq_right hr',mul_zero,Complex.ofReal_zero,zero_mul]
    · simp only [A,tensorCoefficient,subsetCoefficient,ite_eq_right hl,zero_mul,Complex.ofReal_zero]
  have hv : ∀ e : Equiv.Perm (Fin n), A (matchedPattern e)=
      ((n.factorial:ℂ)⁻¹)^2*((lam:ℂ)^n*(l2Mass f:ℂ)) := by
    intro e
    simp only [A,tensorCoefficient,matchedPattern_left,matchedPattern_right,subsetCoefficient,
      ↓reduceIte,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast,
      matchedPattern_quotient_card,cumulative_pair_matched f hf hfs hsf hsym e,pow_two]
  have hh := sum_matched_patterns _ A hz hv
  change (∑ r,A r)=_
  rw [hh]
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast n.factorial_ne_zero
  simp only [alpha,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
  field_simp

theorem cumulative_cross_pattern_sum {m n : ℕ} (hmn : m≠n) {tau : ℝ} (lam : ℝ)
    (f : (Fin m → ℝ) → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex m tau) (hsg : tsupport g⊆positiveSimplex n tau) :
    (∑ r : Setoid (Fin (m+n)),
      (tensorCoefficient (subsetCoefficient m) (subsetCoefficient n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r))=0 := by
  apply Finset.sum_eq_zero
  intro r _
  by_cases hl : Setoid.comap (Fin.castAdd n) r=⊥
  · by_cases hr : Setoid.comap (Fin.natAdd m) r=⊥
    · have hne : Set.range (fun i : Fin m => numericPattern r (i.castAdd n))≠
          Set.range (fun i : Fin n => numericPattern r (i.natAdd m)) := by
        intro he
        exact hmn (injective_ranges_card _ _ (numericPattern_left_injective r hl)
          (numericPattern_right_injective r hr) he)
      rw [cumulative_pair_unmatched f g hf hg hfs hgs hsf hsg r hl hr hne,mul_zero,mul_zero]
    · simp only [tensorCoefficient,subsetCoefficient,ite_eq_right hr,mul_zero,Complex.ofReal_zero,zero_mul]
  · simp only [tensorCoefficient,subsetCoefficient,ite_eq_right hl,zero_mul,Complex.ofReal_zero]

@[simp] theorem cumulativeProfile_fin_zero {tau : ℝ} (f : (Fin 0 → ℝ) → ℝ)
    (hsf : tsupport f⊆positiveSimplex 0 tau) (v : Fin 0 → ℝ) :
    cumulativeProfile tau f v=f 0 := by
  rw [cumulativeProfile_tail tau f hsf v (fun i => Fin.elim0 i)]
  rw [Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  have he : Ici v=(Set.univ : Set (Fin 0 → ℝ)) := by
    ext x
    simp only [Set.mem_Ici,Set.mem_univ,iff_true]
    exact fun i => Fin.elim0 i
  rw [he,setIntegral_univ]
  exact integral_dirac f 0

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_ProfileSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem cumulativeProfile_perm_orthant {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hsupp : tsupport f⊆positiveSimplex n tau)
    (hsym : SymmetricFunction f) (e : Equiv.Perm (Fin n))
    (v : Fin n → ℝ) (hv : ∀ i,0≤v i) :
    cumulativeProfile tau f (v ∘ e)=cumulativeProfile tau f v := by
  change cumulativeProfile tau f (fun i => v (e i))=cumulativeProfile tau f v
  rw [cumulativeProfile_tail tau f hsupp _ (fun i => hv (e i)),
    cumulativeProfile_tail tau f hsupp _ hv]
  let q := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e.symm
  have hq : MeasurePreserving q volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) e.symm
  have hq_apply (x : Fin n → ℝ) : q x=x ∘ e := by
    funext i
    simp [q,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  have he : q ⁻¹' {x : Fin n → ℝ | ∀ i,v (e i)≤x i}={x : Fin n → ℝ | ∀ i,v i≤x i} := by
    ext x
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,hq_apply,Function.comp_apply]
    constructor
    · intro h i
      simpa using h (e.symm i)
    · intro h i
      exact h (e i)
  have hh := hq.integral_comp' (fun x => ({x : Fin n → ℝ | ∀ i,v (e i)≤x i}).indicator f x)
  have hefun : (fun x => ({x : Fin n → ℝ | ∀ i,v (e i)≤x i}).indicator f (q x))=
      ({x : Fin n → ℝ | ∀ i,v i≤x i}).indicator f := by
    funext x
    have hx : (∀ i,v (e i)≤q x i) ↔ ∀ i,v i≤x i := by
      simpa only [Set.mem_preimage,Set.mem_ofPred_eq] using
        (Set.ext_iff.mp he x)
    have hm : q x∈{x : Fin n → ℝ | ∀ i,v (e i)≤x i} ↔ x∈{x : Fin n → ℝ | ∀ i,v i≤x i} := hx
    by_cases hvx : x∈{x : Fin n → ℝ | ∀ i,v i≤x i}
    · rw [Set.indicator_of_mem (hm.mpr hvx),Set.indicator_of_mem hvx,hq_apply,hsym]
    · rw [Set.indicator_of_notMem (fun h => hvx (hm.mp h)),Set.indicator_of_notMem hvx]
  rw [hefun,integral_indicator (by measurability), integral_indicator (by measurability)] at hh
  exact hh.symm

theorem divisorSum_perm_orthant {n X m : ℕ} (hX : 2≤X)
    (F : (Fin n → ℝ) → ℝ)
    (hF : ∀ (e : Equiv.Perm (Fin n)) v,(∀ i,0≤v i) → F (v ∘ e)=F v)
    (e : Equiv.Perm (Fin n)) (b : Fin n → ℕ) :
    divisorSum X F m (b ∘ e)=divisorSum X F m b := by
  classical
  unfold divisorSum
  symm
  apply Finset.sum_equiv (functionPerm e)
  · intro d
    simp only [Fintype.mem_piFinset,functionPerm,Equiv.coe_fn_mk,Function.comp_apply]
    exact e.surjective.forall
  · intro d hd
    change divisorCoefficient X F d=divisorCoefficient X F (d ∘ e)
    unfold divisorCoefficient
    have hp : ∀ i,0<d i := fun i => Nat.pos_of_mem_divisors ((Fintype.mem_piFinset.mp hd) i)
    have he : logCoordinates X (d ∘ e)=(logCoordinates X d) ∘ e := rfl
    rw [he,hF e _ (logCoordinates_nonneg hX hp)]
    congr 1
    exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm

theorem subsetEnumeration_image {h n : ℕ} (S : {S : Finset (Fin h) // S.card=n}) :
    Finset.univ.image (subsetEnumeration S)=S.1 := by
  classical
  ext x
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    exact (S.1.orderIsoOfFin S.2 i).2
  · intro hx
    refine ⟨(S.1.orderIsoOfFin S.2).symm ⟨x,hx⟩,?_⟩
    change ((S.1.orderIsoOfFin S.2) ((S.1.orderIsoOfFin S.2).symm ⟨x,hx⟩)).val=x
    simp

theorem enumeratePerm_image {h n : ℕ}
    (t : {S : Finset (Fin h) // S.card=n} × Equiv.Perm (Fin n)) :
    Finset.univ.image (enumeratePerm t).val=t.1.1 := by
  classical
  rw [←subsetEnumeration_image t.1]
  ext x
  simp only [Finset.mem_image,Finset.mem_univ,true_and,enumeratePerm,Function.comp_apply]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨t.2 i,hi⟩
  · rintro ⟨i,hi⟩
    exact ⟨t.2.symm i,by simpa using hi⟩

theorem enumeratePerm_bijective (h n : ℕ) :
    Function.Bijective (enumeratePerm (h:=h) (n:=n)) := by
  classical
  constructor
  · rintro ⟨S,e⟩ ⟨T,d⟩ he
    have hST : S=T := by
      apply Subtype.ext
      rw [←enumeratePerm_image (S,e),←enumeratePerm_image (T,d),he]
    subst T
    have hed : e=d := by
      apply Equiv.ext
      intro i
      apply (subsetEnumeration S).injective
      exact congrFun (congrArg Subtype.val he) i
    subst d
    rfl
  · intro b
    let S : {S : Finset (Fin h) // S.card=n} :=
      ⟨Finset.univ.image b.val,by rw [Finset.card_image_of_injective _ b.2]; simp⟩
    have he : Set.range (subsetEnumeration S)=Set.range b.val := by
      ext x
      have hh := Finset.ext_iff.mp (subsetEnumeration_image S) x
      simpa only [Finset.mem_image,Finset.mem_univ,true_and,S,Set.mem_range] using hh
    obtain ⟨e,he⟩ := injective_same_range_perm (subsetEnumeration S) b.val b.2 he
    exact ⟨(S,e),Subtype.ext he.symm⟩

theorem average_div (X : ℕ) (f : ℕ → ℝ) (a : ℝ) :
    average X (fun m => f m/a)=average X f/a := by
  simpa only [div_eq_mul_inv,mul_comm] using average_const_mul X a⁻¹ f

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_MarkedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem deleteCoordinate_smooth {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (deleteCoordinate f) := by
  let K := (fun v : Fin (n+1) → ℝ => -v (Fin.last n)) '' tsupport f
  have hK : IsCompact K := hf.isCompact.image (continuous_apply _ |>.neg)
  let g : (Fin n → ℝ) → ℝ → ℝ := fun t u => f (Fin.snoc t (-u))
  have hgs : ∀ t u,t∈(Set.univ : Set (Fin n → ℝ)) → u∉K → g t u=0 := by
    intro t u _ hu
    by_contra hn
    apply hu
    refine ⟨Fin.snoc t (-u),subset_tsupport f hn,?_⟩
    simp
  have hsm : ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × ℝ => (Fin.snoc p.1 (-p.2) : Fin (n+1) → ℝ)) := by
    apply contDiff_pi.mpr
    intro i
    cases i using Fin.lastCases with
    | last => simpa using contDiff_snd.neg
    | cast i => simpa [Function.comp_def] using (contDiff_apply ℝ ℝ i).comp contDiff_fst
  have hh := MeasureTheory.contDiffOn_convolution_right_with_param
    (μ:=volume) (ContinuousLinearMap.mul ℝ ℝ) isOpen_univ hK hgs
    (f:=fun _ : ℝ => (1:ℝ)) (continuous_const.locallyIntegrable) (hfs.comp hsm).contDiffOn
  have hg : ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × ℝ =>
      ((fun _ : ℝ => (1:ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] g p.1) p.2) := by
    rwa [Set.univ_prod_univ,contDiffOn_univ] at hh
  have H := hg.comp (contDiff_id.prodMk (contDiff_const (c:=(0:ℝ))))
  change ContDiff ℝ ∞ (fun x => ∫ t : ℝ, f (Fin.snoc x t))
  simpa only [Function.comp_def,convolution_def,ContinuousLinearMap.mul_apply',one_mul,
    zero_sub,g,neg_neg,deleteCoordinate,id_eq] using H

theorem deleteCoordinate_tsupport_subset {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : HasCompactSupport f) :
    tsupport (deleteCoordinate f) ⊆
      (fun v : Fin (n+1) → ℝ => fun i : Fin n => v i.castSucc) '' tsupport f := by
  have hk := hf.isCompact.image (continuous_pi (fun i : Fin n => continuous_apply i.castSucc))
  apply closure_minimal _ hk.isClosed
  intro t ht
  by_contra hn
  apply ht
  unfold deleteCoordinate
  apply integral_eq_zero_of_ae
  filter_upwards [] with u
  by_contra hfu
  exact hn ⟨Fin.snoc t u,subset_tsupport f hfu,by ext i; simp⟩

theorem deleteCoordinate_compact {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : HasCompactSupport f) : HasCompactSupport (deleteCoordinate f) := by
  exact (hf.isCompact.image (continuous_pi (fun i : Fin n => continuous_apply i.castSucc))).of_isClosed_subset
    (isClosed_tsupport _) (deleteCoordinate_tsupport_subset f hf)

theorem deleteCoordinate_interior_support {n : ℕ} {tau : ℝ}
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : HasCompactSupport f)
    (hs : tsupport f⊆positiveSimplex (n+1) tau) :
    tsupport (deleteCoordinate f) ⊆positiveSimplex n tau := by
  intro t ht
  obtain ⟨v,hv,rfl⟩ := deleteCoordinate_tsupport_subset f hf ht
  have hv' := hs hv
  refine ⟨fun i => hv'.1 i.castSucc,?_⟩
  have hh : coordinateSum v=coordinateSum (fun i : Fin n => v i.castSucc)+v (Fin.last n) := by
    exact Fin.sum_univ_castSucc (fun i => v i)
  have hp := hv'.1 (Fin.last n)
  linarith [hv'.2]

theorem deleteCoordinate_symmetric {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ)
    (hs : SymmetricFunction f) : SymmetricFunction (deleteCoordinate f) := by
  intro e t
  unfold deleteCoordinate
  apply integral_congr_ae
  filter_upwards [] with u
  have he : Fin.snoc (t ∘ e) u=(Fin.snoc t u : Fin (n+1) → ℝ) ∘ fixLastPerm e := by
    ext i
    cases i using Fin.lastCases <;> simp
  rw [he,hs]

theorem pi_restrict_Ici {n : ℕ} (v : Fin n → ℝ) :
    Measure.pi (fun i => volume.restrict (Ici (v i)))=volume.restrict (Ici v) := by
  rw [←Measure.restrict_pi_pi]
  congr 1
  ext x
  simp

theorem integral_Ici_snoc {n : ℕ} (v : Fin (n+1) → ℝ)
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : IntegrableOn f (Ici v)) :
    (∫ x in Ici v,f x)=∫ y in Ici (fun i : Fin n => v i.castSucc),
      ∫ a in Ici (v (Fin.last n)),f (Fin.snoc y a) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) (Fin.last n)
  have hm := measurePreserving_piFinSuccAbove
    (fun i : Fin (n+1) => volume.restrict (Ici (v i))) (Fin.last n)
  have he : ∀ p : ℝ × (Fin n → ℝ), e.symm p=Fin.snoc p.2 p.1 := by
    intro p
    simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
  have hfi : Integrable f (Measure.pi (fun i => volume.restrict (Ici (v i)))) := by
    rw [pi_restrict_Ici]
    exact hf
  have hh := hm.symm.integral_comp' f
  have hi := (hm.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hfi
  dsimp only [e] at he
  simp only [Fin.succAbove_last_apply,he,Function.comp_def,pi_restrict_Ici] at hh hi
  rw [←hh]
  exact integral_prod_symm _ hi

theorem cumulativeProfile_delete_tail {n : ℕ} {tau : ℝ}
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : HasCompactSupport f)
    (hfs : ContDiff ℝ ∞ f) (hs : tsupport f⊆positiveSimplex (n+1) tau)
    (v : Fin n → ℝ) (hv : ∀ i,0≤v i) :
    cumulativeProfile tau f (Fin.snoc v 0)=cumulativeProfile tau (deleteCoordinate f) v := by
  have hs' := deleteCoordinate_interior_support f hf hs
  rw [cumulativeProfile_tail tau f hs,cumulativeProfile_tail tau _ hs' _ hv]
  · rw [integral_Ici_snoc _ _ (hfs.continuous.integrable_of_hasCompactSupport hf).integrableOn]
    simp only [Fin.snoc_castSucc,Fin.snoc_last]
    apply setIntegral_congr_fun measurableSet_Ici
    intro t _
    exact (deleteCoordinate_eq_orthant_integral (fun _ h => (hs (subset_tsupport f h)).1) t).symm
  · intro i
    cases i using Fin.lastCases <;> simp [hv]

theorem AdmissibleFamily.all_properties {tau : ℝ} {k : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f) (j : ℕ) :
    ContDiff ℝ ∞ (f j) ∧ HasCompactSupport (f j) ∧
    tsupport (f j)⊆positiveSimplex j tau ∧ SymmetricFunction (f j) := by
  by_cases hj : j≤k
  · exact hf.2.1 j hj
  · rw [hf.2.2 j (by omega)]
    refine ⟨contDiff_const,HasCompactSupport.zero,by simp,?_⟩
    intro e v
    rfl

theorem deletedFamily_admissible {tau : ℝ} {k : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f) :
    AdmissibleFamily tau k (deletedFamily f) := by
  refine ⟨hf.1,?_,?_⟩
  · intro j _
    obtain ⟨hjs,hjc,hjt,hjy⟩ := hf.all_properties j
    obtain ⟨hns,hnc,hnt,hny⟩ := hf.all_properties (j+1)
    refine ⟨hjs.add (deleteCoordinate_smooth _ hnc hns),
      hjc.add (deleteCoordinate_compact _ hnc),?_,?_⟩
    · exact (tsupport_add (f j) (deleteCoordinate (f (j+1)))).trans
        (Set.union_subset hjt (deleteCoordinate_interior_support _ hnc hnt))
    · intro e v
      exact congrArg₂ (·+·) (hjy e v) (deleteCoordinate_symmetric _ hny e v)
  · intro j hj
    have h1 := hf.2.2 j hj
    have h2 := hf.2.2 (j+1) (by omega)
    ext t
    simp [deletedFamily,h1,h2]

theorem cumulativeProfile_deletedFamily {tau : ℝ} {k : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f)
    (j : ℕ) (v : Fin j → ℝ) (hv : ∀ i,0≤v i) :
    cumulativeProfile tau (deletedFamily f j) v=
      cumulativeProfile tau (f j) v+cumulativeProfile tau (f (j+1)) (Fin.snoc v 0) := by
  obtain ⟨hjs,hjc,hjt,hjy⟩ := hf.all_properties j
  obtain ⟨hns,hnc,hnt,hny⟩ := hf.all_properties (j+1)
  have hg := (deletedFamily_admissible hf).all_properties j
  rw [cumulativeProfile_delete_tail _ hnc hns hnt v hv,
    cumulativeProfile_tail tau _ hg.2.2.1 _ hv,cumulativeProfile_tail tau _ hjt _ hv,
    cumulativeProfile_tail tau _ (deleteCoordinate_interior_support _ hnc hnt) _ hv]
  exact integral_add (hjs.continuous.integrable_of_hasCompactSupport hjc).integrableOn
    ((deleteCoordinate_smooth _ hnc hns).continuous.integrable_of_hasCompactSupport
      (deleteCoordinate_compact _ hnc)).integrableOn

theorem divisorSum_add {n : ℕ} (X M : ℕ) (F G : (Fin n → ℝ) → ℝ) (b : Fin n → ℕ) :
    divisorSum X (F+G) M b=divisorSum X F M b+divisorSum X G M b := by
  simp only [divisorSum,divisorCoefficient,Pi.add_apply,mul_add,Finset.sum_add_distrib]

theorem divisorSum_internal_family_delete {tau : ℝ} {k X M a : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f)
    (htau : tau<1) (hX : 2≤X) (hM : X<M+a) (hp : Nat.Prime (M+a))
    (j : ℕ) (b : Fin j → ℕ) :
    divisorSum X (cumulativeProfile tau (f j)) M b+
      divisorSum X (cumulativeProfile tau (f (j+1))) M (Fin.snoc b a)=
      divisorSum X (cumulativeProfile tau (deletedFamily f j)) M b := by
  have hn := hf.all_properties (j+1)
  rw [divisorSum_prime_delete hX hM hp _ htau (cumulativeProfile_budget tau _ hn.2.2.1)]
  rw [←divisorSum_add]
  apply divisorSum_congr_orthant hX
  intro v hv
  exact (cumulativeProfile_deletedFamily hf j v hv).symm

theorem subsetEnumeration_range {h n : ℕ} (S : {S : Finset (Fin h) // S.card=n}) :
    Set.range (subsetEnumeration S)=(S.val : Set (Fin h)) := by
  ext x
  have hh := Finset.ext_iff.mp (subsetEnumeration_image S) x
  simpa only [Set.mem_range,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_coe] using hh

theorem setDivisor_eq_enumeration {X M h a n : ℕ} (hX : 2≤X)
    (F : (j : ℕ) → (Fin j → ℝ) → ℝ)
    (hF : ∀ j (e : Equiv.Perm (Fin j)) v,(∀ i,0≤v i) → F j (v ∘ e)=F j v)
    (S : Finset (Fin h)) (hn : S.card=n) (b : Fin n → Fin h)
    (hb : Function.Injective b) (hr : Set.range b=(S:Set (Fin h))) :
    setDivisor F X M h a S=divisorSum X (F n) M (fun i => a+(b i:ℕ)) := by
  subst n
  obtain ⟨e,he⟩ := injective_same_range_perm (subsetEnumeration ⟨S,rfl⟩) b hb
    ((subsetEnumeration_range ⟨S,rfl⟩).trans hr.symm)
  rw [he]
  exact (divisorSum_perm_orthant hX (F S.card) (hF S.card) e
    (fun i => a+(subsetEnumeration ⟨S,rfl⟩ i:ℕ))).symm

theorem snoc_subsetEnumeration_injective {h : ℕ} (S : Finset (Fin h)) {c : Fin h} (hc : c∉S) :
    Function.Injective (Fin.snoc (subsetEnumeration ⟨S,rfl⟩) c) := by
  intro i j hij
  cases i using Fin.lastCases with
  | last =>
    cases j using Fin.lastCases with
    | last => rfl
    | cast j =>
      simp only [Fin.snoc_last,Fin.snoc_castSucc] at hij
      have hj : subsetEnumeration ⟨S,rfl⟩ j∈S := by
        have hh : subsetEnumeration ⟨S,rfl⟩ j∈Set.range (subsetEnumeration ⟨S,rfl⟩) := ⟨j,rfl⟩
        rwa [subsetEnumeration_range] at hh
      exact False.elim (hc (hij.symm ▸ hj))
  | cast i =>
    cases j using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last,Fin.snoc_castSucc] at hij
      have hi : subsetEnumeration ⟨S,rfl⟩ i∈S := by
        have hh : subsetEnumeration ⟨S,rfl⟩ i∈Set.range (subsetEnumeration ⟨S,rfl⟩) := ⟨i,rfl⟩
        rwa [subsetEnumeration_range] at hh
      exact False.elim (hc (hij ▸ hi))
    | cast j =>
      simp only [Fin.snoc_castSucc] at hij
      exact congrArg Fin.castSucc ((subsetEnumeration ⟨S,rfl⟩).injective hij)

theorem snoc_subsetEnumeration_range {h : ℕ} (S : Finset (Fin h)) (c : Fin h) :
    Set.range (Fin.snoc (subsetEnumeration ⟨S,rfl⟩) c)=↑(insert c S : Finset (Fin h)) := by
  ext x
  simp only [Set.mem_range,Finset.mem_coe,Finset.mem_insert]
  constructor
  · rintro ⟨i,rfl⟩
    cases i using Fin.lastCases with
    | last => simp
    | cast i =>
      right
      simp only [Fin.snoc_castSucc]
      have hh : subsetEnumeration ⟨S,rfl⟩ i∈Set.range (subsetEnumeration ⟨S,rfl⟩) := ⟨i,rfl⟩
      rwa [subsetEnumeration_range] at hh
  · rintro (rfl | hx)
    · exact ⟨Fin.last _,by simp⟩
    · have hx' : x∈Set.range (subsetEnumeration ⟨S,rfl⟩) := by rwa [subsetEnumeration_range]
      obtain ⟨i,rfl⟩ := hx'
      exact ⟨i.castSucc,by simp⟩

theorem setDivisor_insert_eq_snoc {X M h a : ℕ} (hX : 2≤X)
    (F : (j : ℕ) → (Fin j → ℝ) → ℝ)
    (hF : ∀ j (e : Equiv.Perm (Fin j)) v,(∀ i,0≤v i) → F j (v ∘ e)=F j v)
    (S : Finset (Fin h)) {c : Fin h} (hc : c∉S) :
    setDivisor F X M h a (insert c S)=
      divisorSum X (F (S.card+1)) M
        (Fin.snoc (fun i => a+(subsetEnumeration ⟨S,rfl⟩ i:ℕ)) (a+(c:ℕ))) := by
  rw [setDivisor_eq_enumeration hX F hF _ (Finset.card_insert_of_notMem hc)
    _ (snoc_subsetEnumeration_injective S hc) (snoc_subsetEnumeration_range S c)]
  congr 1
  funext i
  cases i using Fin.lastCases <;> simp

theorem finiteSubsetWeight_prime_delete {tau : ℝ} {k X M h a : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f)
    (htau : tau<1) (hX : 2≤X) (c : Fin h) (hM : X<M+(a+(c:ℕ)))
    (hp : Nat.Prime (M+(a+(c:ℕ)))) :
    finiteSubsetWeight tau f X M h a Finset.univ=
      finiteSubsetWeight tau (deletedFamily f) X M h a (Finset.univ.erase c) := by
  classical
  have hsym : ∀ j (e : Equiv.Perm (Fin j)) v,(∀ i,0≤v i) →
      cumulativeProfile tau (f j) (v ∘ e)=cumulativeProfile tau (f j) v := by
    intro j
    have hj := hf.all_properties j
    exact cumulativeProfile_perm_orthant _ hj.2.2.1 hj.2.2.2
  have he : (Finset.univ : Finset (Fin h))=insert c (Finset.univ.erase c) := by simp
  unfold finiteSubsetWeight
  conv_lhs => rw [he,Finset.sum_powerset_insert (Finset.notMem_erase c Finset.univ),←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  have hc : c∉S := fun h => Finset.notMem_erase c Finset.univ ((Finset.mem_powerset.mp hS) h)
  rw [setDivisor_insert_eq_snoc hX _ hsym S hc]
  exact divisorSum_internal_family_delete hf htau hX hM hp S.card _

theorem setDivisor_fixed_card {X M h a n : ℕ}
    (F : (j : ℕ) → (Fin j → ℝ) → ℝ) (S : Finset (Fin h)) (hn : S.card=n) :
    setDivisor F X M h a S=
      divisorSum X (F n) M (fun i => a+(subsetEnumeration ⟨S,hn⟩ i:ℕ)) := by
  subst n
  rfl

theorem setDivisor_level_sum (X M h a n : ℕ)
    (F : (j : ℕ) → (Fin j → ℝ) → ℝ) :
    (∑ S ∈ Finset.powersetCard n (Finset.univ : Finset (Fin h)),setDivisor F X M h a S)=
      unorderedBlock X h a (F n) M := by
  classical
  rw [Finset.sum_subtype (p:=fun S : Finset (Fin h) => S.card=n)
    (Finset.powersetCard n Finset.univ) (by intro S; simp)]
  unfold unorderedBlock
  apply Finset.sum_congr rfl
  intro S _
  exact setDivisor_fixed_card F S.val S.property

theorem finiteSubsetWeight_eq_unordered_levels {tau : ℝ} {k X M h a : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f) (hk : k≤h) :
    finiteSubsetWeight tau f X M h a Finset.univ=
      ∑ j : Fin (k+1),unorderedBlock X h a (cumulativeProfile tau (f j)) M := by
  unfold finiteSubsetWeight
  rw [Finset.sum_powerset]
  simp only [Finset.card_univ,Fintype.card_fin,setDivisor_level_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => unorderedBlock X h a (cumulativeProfile tau (f j)) M) (k+1)]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega : k+1≤h+1))
  intro j _ hj
  have hjk : k<j := by simp only [Finset.mem_range,not_lt] at hj; omega
  rw [hf.2.2 j hjk,cumulativeProfile_zero,unorderedBlock_zero]

theorem unorderedWeight_eq_finiteSubsetWeight {tau lam : ℝ} {k X M : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f)
    (hk : k≤blockLength lam X) :
    unorderedWeight tau lam k f X M=
      finiteSubsetWeight tau f X M (blockLength lam X) (blockLength lam X+1) Finset.univ := by
  exact (finiteSubsetWeight_eq_unordered_levels hf hk).symm

theorem enumeratePerm_subset_iff {h n : ℕ}
    (S : {S : Finset (Fin h) // S.card=n}) (e : Equiv.Perm (Fin n)) (B : Finset (Fin h)) :
    (∀ i,(enumeratePerm (S,e)).val i∈B) ↔ S.val⊆B := by
  constructor
  · intro hi x hx
    rw [←enumeratePerm_image (S,e)] at hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact hi i
  · intro hS i
    apply hS
    rw [←enumeratePerm_image (S,e)]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

theorem restrictedBlock_eq_unordered {n X h a m : ℕ} (hX : 2≤X)
    (F : (Fin n → ℝ) → ℝ) (B : Finset (Fin h))
    (hsym : ∀ (e : Equiv.Perm (Fin n)) v,(∀ i,0≤v i) → F (v ∘ e)=F v) :
    restrictedBlock X h a F (subsetCoefficient n) B m=restrictedUnorderedBlock X h a F B m := by
  classical
  unfold restrictedBlock
  have he : (∑ b : Fin n → Fin h,subsetCoefficient n (Setoid.ker b)*
      (if ∀ i,b i∈B then divisorSum X F m (fun i => a+(b i:ℕ)) else 0))=
      ∑ b : {b : Fin n → Fin h // Function.Injective b},
        (n.factorial:ℝ)⁻¹*(if ∀ i,b.val i∈B then divisorSum X F m (fun i => a+(b.val i:ℕ)) else 0) := by
    simp only [subsetCoefficient,Setoid.ker_eq_bot_iff,ite_mul,zero_mul]
    rw [←Finset.sum_filter]
    exact Finset.sum_subtype (p:=fun b : Fin n → Fin h => Function.Injective b)
      (Finset.univ.filter fun b : Fin n → Fin h => Function.Injective b) (by simp) _
  rw [he]
  rw [←Fintype.sum_equiv (Equiv.ofBijective enumeratePerm (enumeratePerm_bijective h n))
    (fun t => (n.factorial:ℝ)⁻¹*(if ∀ i,(enumeratePerm t).val i∈B then
      divisorSum X F m (fun i => a+((enumeratePerm t).val i:ℕ)) else 0)) _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  unfold restrictedUnorderedBlock
  apply Finset.sum_congr rfl
  intro S _
  have hd (e : Equiv.Perm (Fin n)) :
      divisorSum X F m (fun i => a+((enumeratePerm (S,e)).val i:ℕ))=
      divisorSum X F m (fun i => a+(subsetEnumeration S i:ℕ)) :=
    divisorSum_perm_orthant hX F hsym e (fun i => a+(subsetEnumeration S i:ℕ))
  simp only [hd,enumeratePerm_subset_iff,Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
  have hn : (n.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [←mul_assoc, mul_inv_cancel₀ hn,one_mul]

theorem setDivisor_subset_level_sum (X M h a n : ℕ)
    (F : (j : ℕ) → (Fin j → ℝ) → ℝ) (B : Finset (Fin h)) :
    (∑ S ∈ Finset.powersetCard n (Finset.univ : Finset (Fin h)),
      if S⊆B then setDivisor F X M h a S else 0)=
      restrictedUnorderedBlock X h a (F n) B M := by
  classical
  rw [Finset.sum_subtype (p:=fun S : Finset (Fin h) => S.card=n)
    (Finset.powersetCard n Finset.univ) (by intro S; simp)]
  unfold restrictedUnorderedBlock
  apply Finset.sum_congr rfl
  intro S _
  rw [setDivisor_fixed_card F S.val S.property]

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_RestrictedWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem finiteSubsetWeight_eq_restricted_levels {tau : ℝ} {k X M h a : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f) (hk : k≤h)
    (B : Finset (Fin h)) :
    finiteSubsetWeight tau f X M h a B=
      ∑ j : Fin (k+1),restrictedUnorderedBlock X h a (cumulativeProfile tau (f j)) B M := by
  classical
  unfold finiteSubsetWeight
  have he : B.powerset=(Finset.univ.powerset : Finset (Finset (Fin h))).filter (fun S => S⊆B) := by
    ext S
    simp
  rw [he,Finset.sum_filter,Finset.sum_powerset]
  simp only [Finset.card_univ,Fintype.card_fin,setDivisor_subset_level_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => restrictedUnorderedBlock X h a (cumulativeProfile tau (f j)) B M) (k+1)]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega : k+1≤h+1))
  intro j _ hj
  have hjk : k<j := by simp only [Finset.mem_range,not_lt] at hj; omega
  rw [hf.2.2 j hjk,cumulativeProfile_zero,restrictedUnorderedBlock_zero]

theorem restrictedWeight_eq_finiteSubsetWeight {tau lam : ℝ} {k X m : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f)
    (hX : 2≤X) (hk : k≤blockLength lam X) (c : Fin (blockLength lam X)) :
    restrictedWeight tau lam k f X m c=
      finiteSubsetWeight tau f X m (blockLength lam X) (blockLength lam X+1) (Finset.univ.erase c) := by
  rw [finiteSubsetWeight_eq_restricted_levels hf hk]
  unfold restrictedWeight
  apply Finset.sum_congr rfl
  intro j _
  have hj := hf.all_properties j
  exact restrictedBlock_eq_unordered hX _ _ (cumulativeProfile_perm_orthant _ hj.2.2.1 hj.2.2.2)

theorem unorderedWeight_prime_delete {tau lam : ℝ} {k X m : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f)
    (htau : tau<1) (hX : 2≤X) (hk : k≤blockLength lam X) (hm : X < m)
    (c : Fin (blockLength lam X)) (hp : Nat.Prime (m+(blockLength lam X+1+(c:ℕ)))) :
    unorderedWeight tau lam k f X m=restrictedWeight tau lam k (deletedFamily f) X m c := by
  rw [unorderedWeight_eq_finiteSubsetWeight hf hk,
    restrictedWeight_eq_finiteSubsetWeight (deletedFamily_admissible hf) hX hk]
  exact finiteSubsetWeight_prime_delete hf htau hX c (by omega) hp

theorem coincident_double_sum {s h : ℕ} (a : ℤ) (F : (Fin (s+1) → Fin h) → ℂ) :
    (∑ u∈distinctBox (s:=s) (h:=h) (fun _ => a),∑ c : Fin h,
       if ∀ j,u j≠c then F (Fin.snoc u c) else 0)=
      ∑ v∈distinctBox (s:=s+1) (h:=h) (fun _ => a),F v := by
  classical
  simp only [distinctBox,Finset.sum_filter,constant_boxTuple_injective_iff]
  have he (u : Fin s → Fin h) :
      (if Function.Injective u then ∑ c : Fin h,if ∀ j,u j≠c then F (Fin.snoc u c) else 0 else 0)=
        ∑ c : Fin h,if Function.Injective u ∧ c∉Set.range u then F (Fin.snoc u c) else 0 := by
    by_cases hu : Function.Injective u <;> simp [hu,Set.mem_range]
  simp only [he]
  rw [Finset.sum_comm]
  calc
    _ = ∑ t : Fin h × (Fin s → Fin h),
        if Function.Injective t.2 ∧ t.1∉Set.range t.2 then F (Fin.snoc t.2 t.1) else 0 :=
      (Fintype.sum_prod_type _).symm
    _ = _ := by
      apply Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (s+1) => Fin h))
      intro t
      change (if Function.Injective t.2 ∧ t.1∉Set.range t.2 then F (Fin.snoc t.2 t.1) else 0)=
        (if Function.Injective (Fin.snoc t.2 t.1) then F (Fin.snoc t.2 t.1) else 0)
      exact if_congr Fin.snoc_injective_iff.symm rfl rfl

theorem patternTupleEquiv_avoid {n h : ℕ} (r : Setoid (Fin n)) (a : ℕ)
    (b : {b // b∈patternClass (α:=Fin h) r}) (c : Fin h) :
    (∀ i,b.val i≠c) ↔ ∀ j,(patternTupleEquiv r h a b).val j≠c := by
  constructor
  · intro hb j
    obtain ⟨i,hi⟩ := (patternLabels_surjective r) j
    have he := congrFun (patternTupleEquiv_labels r h a b) i
    simp only [patternBoxShifts,hi] at he
    have hv : (patternTupleEquiv r h a b).val j=b.val i := by
      apply Fin.ext
      omega
    simpa only [hv] using hb i
  · intro hb i
    have he := congrFun (patternTupleEquiv_labels r h a b) i
    simp only [patternBoxShifts] at he
    have hv : (patternTupleEquiv r h a b).val (patternLabels r i)=b.val i := by
      apply Fin.ext
      omega
    simpa only [hv] using hb (patternLabels r i)

theorem pattern_restricted_marked_sum_eq_box {n : ℕ} (r : Setoid (Fin n)) (h X : ℕ)
    (F : (Fin n → ℝ) → ℝ) :
    (∑ b∈patternClass (α:=Fin h) r,∑ c : Fin h,if ∀ i,b i≠c then
      (average X (fun m => divisorSum X F m (fun i => h+1+(b i:ℕ))*theta (m+(h+1+(c:ℕ)))):ℂ)/(Real.log X:ℂ)
      else 0)=
    ∑ v∈distinctBox (s:=Fintype.card (Quotient r)+1) (h:=h) (fun _ => ((h+1:ℕ):ℤ)),
      (average X (fun m => divisorSum X F m
        (patternBoxShifts (patternLabels r) (fun _ => h+1) (fun j => v j.castSucc))*
        theta (m+(h+1+(v (Fin.last _):ℕ)))):ℂ)/(Real.log X:ℂ) := by
  classical
  rw [←coincident_double_sum]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]
  conv_lhs => rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Fintype.sum_equiv (patternTupleEquiv r h ((h+1:ℕ):ℤ))
  intro b
  rw [patternTupleEquiv_labels r h (h+1) b]
  apply Finset.sum_congr rfl
  intro c _
  simp only [←patternTupleEquiv_avoid r (h+1) b c]

theorem restricted_marked_pattern_limit (hBV : BombieriVinogradov) {n : ℕ}
    {lam : ℝ} (hlam : 0<lam) (r : Setoid (Fin n))
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ b∈patternClass (α:=Fin (blockLength lam X)) r,∑ c : Fin (blockLength lam X),
      if ∀ i,b i≠c then (average X (fun m => divisorSum X F m (fun i => blockLength lam X+1+(b i:ℕ))*
        theta (m+(blockLength lam X+1+(c:ℕ)))):ℂ)/(Real.log X:ℂ) else 0) atTop
      (𝓝 ((lam:ℂ)^(Fintype.card (Quotient r)+1)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin n))
          (fun v => (F v.ofLp:ℂ)) hF hFs)
        (shiftFamily (fun i => (numericPattern r i:ℤ))))) := by
  have ha : ∀ᶠ X : ℕ in atTop,∀ _j : Fin (Fintype.card (Quotient r)+1),
      blockLength lam X+1≤2*blockLength lam X := by
    filter_upwards [blockOffset_eventually hlam] with X hX j
    exact hX
  have hh := marked_box_pattern_limit hBV hlam (patternLabels r) (patternLabels_surjective r)
    (fun X _ => blockLength lam X+1) ha F rho hrho hrhohalf hbudget hF hFs M hM hbound
  apply hh.congr'
  exact Eventually.of_forall fun X => (pattern_restricted_marked_sum_eq_box r _ X F).symm

theorem restrictedBlock_marked_expansion {n X h : ℕ}
    (F : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ) :
    (internalMarked X h (fun m c => restrictedBlock X h (h+1) F k (Finset.univ.erase c) m):ℂ)=
      ∑ b : Fin n → Fin h,(k (Setoid.ker b):ℂ)*∑ c : Fin h,if ∀ i,b i≠c then
        (average X (fun m => divisorSum X F m (fun i => h+1+(b i:ℕ))*theta (m+(h+1+(c:ℕ)))):ℂ)/(Real.log X:ℂ)
        else 0 := by
  classical
  unfold internalMarked restrictedBlock
  simp only [Finset.mem_erase,Finset.mem_univ,and_true,Finset.sum_mul,Finset.sum_div,
    average_finset_sum,Complex.ofReal_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hb : ∀ i,b i≠c
  · simp only [ite_eq_left hb]
    simp only [←mul_div_assoc,average_div]
    simp only [mul_assoc,average_const_mul,Complex.ofReal_div,Complex.ofReal_mul]
  · simp only [ite_eq_right hb,mul_zero,zero_mul,zero_div]
    simp [average]

theorem restrictedBlock_marked_limit (hBV : BombieriVinogradov) {n : ℕ}
    {lam : ℝ} (hlam : 0<lam)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (k : Setoid (Fin n) → ℝ) :
    Tendsto (fun X : ℕ => (internalMarked X (blockLength lam X) (fun m c =>
      restrictedBlock X (blockLength lam X) (blockLength lam X+1) F k (Finset.univ.erase c) m):ℂ)) atTop
      (𝓝 (∑ r : Setoid (Fin n),(k r:ℂ)*((lam:ℂ)^(Fintype.card (Quotient r)+1)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin n))
          (fun v => (F v.ofLp:ℂ)) (realEuclidean_compact F hF) (realEuclidean_smooth F hFs))
        (equalityPatternFamily r)))) := by
  classical
  obtain ⟨M,hM⟩ := hFs.continuous.bounded_above_of_compact_support hF
  have hh := tendsto_finsetSum Finset.univ (fun r _ =>
    (restricted_marked_pattern_limit hBV hlam r F rho hrho hrhohalf hbudget
      (realEuclidean_compact F hF) (realEuclidean_smooth F hFs) M
      ((norm_nonneg (F 0)).trans (hM 0)) (fun v _ => by simpa only [Real.norm_eq_abs] using hM v)).const_mul (k r:ℂ))
  apply hh.congr'
  exact Eventually.of_forall (fun X => by
    dsimp only
    rw [restrictedBlock_marked_expansion]
    calc
      (∑ r : Setoid (Fin n), (k r:ℂ)*∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
        ∑ c : Fin (blockLength lam X),if ∀ i,b i≠c then
        (average X (fun m => divisorSum X F m (fun i => blockLength lam X+1+(b i:ℕ))*
          theta (m+(blockLength lam X+1+(c:ℕ)))):ℂ)/(Real.log X:ℂ) else 0) =
        ∑ r : Setoid (Fin n),∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
          (k (Setoid.ker b):ℂ)*∑ c : Fin (blockLength lam X),if ∀ i,b i≠c then
            (average X (fun m => divisorSum X F m (fun i => blockLength lam X+1+(b i:ℕ))*
              theta (m+(blockLength lam X+1+(c:ℕ)))):ℂ)/(Real.log X:ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [(mem_patternClass r b).mp hb]
      _ = _ := sum_patterns _
    apply Finset.sum_congr (by ext b; simp)
    intro b _
    rfl)

theorem restrictedBlock_mul {n p : ℕ} (X h a m : ℕ)
    (F : (Fin n → ℝ) → ℝ) (G : (Fin p → ℝ) → ℝ)
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) (B : Finset (Fin h)) :
    restrictedBlock X h a F k B m*restrictedBlock X h a G l B m=
      restrictedBlock X h a (tensorProfile F G) (tensorCoefficient k l) B m := by
  classical
  unfold restrictedBlock
  rw [Finset.sum_mul_sum,←Finset.sum_product']
  apply Finset.sum_equiv (Fin.appendEquiv n p)
  · intro bc; simp
  intro bc _
  rw [show (Fin.appendEquiv n p) bc=Fin.append bc.1 bc.2 from rfl]
  simp only [tensorCoefficient,append_ker_left,append_ker_right]
  have he : (fun i => a+((Fin.append bc.1 bc.2 i :Fin h):ℕ))=
      Fin.append (fun i => a+(bc.1 i:ℕ)) (fun i => a+(bc.2 i:ℕ)) := by
    funext i
    cases i using Fin.addCases <;> simp
  rw [he,divisorSum_tensor]
  have hc : (∀ i,Fin.append bc.1 bc.2 i∈B) ↔ (∀ i,bc.1 i∈B) ∧ (∀ j,bc.2 j∈B) := by
    simp only [Fin.forall_fin_add,Fin.append_left,Fin.append_right]
  simp only [hc]
  split_ifs <;> simp_all
  all_goals ring

theorem restrictedBlock_congr_orthant {n X : ℕ} (hX : 2≤X) (h a m : ℕ)
    (F G : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ) (B : Finset (Fin h))
    (hFG : ∀ v,(∀ i,0≤v i) → F v=G v) :
    restrictedBlock X h a F k B m=restrictedBlock X h a G k B m := by
  apply Finset.sum_congr rfl
  intro b _
  rw [divisorSum_congr_orthant hX m _ F G hFG]

theorem restrictedBlock_cumulative_mul {n p X : ℕ} (hX : 2≤X) (h a m : ℕ) {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : tsupport f⊆positiveSimplex n tau) (hg : tsupport g⊆positiveSimplex p tau)
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) (B : Finset (Fin h)) :
    restrictedBlock X h a (cumulativeProfile tau f) k B m*
      restrictedBlock X h a (cumulativeProfile tau g) l B m=
    restrictedBlock X h a (cumulativeProfile (tau+tau) (tensorProfile f g)) (tensorCoefficient k l) B m := by
  rw [restrictedBlock_mul]
  apply restrictedBlock_congr_orthant hX
  intro v hv
  let v1 := fun i : Fin n => v (i.castAdd p)
  let v2 := fun i : Fin p => v (i.natAdd n)
  have he : v=Fin.append v1 v2 := by
    funext i
    cases i using Fin.addCases <;> simp [v1,v2]
  rw [he,tensorProfile_append]
  exact (cumulativeProfile_tensor f g hf hg v1 v2 (fun i => hv _) (fun i => hv _)).symm

theorem internalMarked_congr {X h : ℕ} {H G : ℕ → Fin h → ℝ}
    (he : ∀ m c,H m c=G m c) : internalMarked X h H=internalMarked X h G := by
  unfold internalMarked
  congr 1
  funext m
  exact Finset.sum_congr rfl fun c _ => by rw [he]

theorem internalMarked_finset_sum {α : Type*} (X h : ℕ) (S : Finset α)
    (H : α → ℕ → Fin h → ℝ) :
    internalMarked X h (fun m c => ∑ i∈S,H i m c)=∑ i∈S,internalMarked X h (H i) := by
  unfold internalMarked
  simp only [Finset.sum_mul,Finset.sum_div,average_finset_sum]
  rw [Finset.sum_comm]

theorem restricted_cumulative_pair_limit (hBV : BombieriVinogradov) {n p : ℕ} {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau) :
    Tendsto (fun X : ℕ => (internalMarked X (blockLength lam X) (fun m c =>
      restrictedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) (Finset.univ.erase c) m*
      restrictedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau g) (subsetCoefficient p) (Finset.univ.erase c) m):ℂ))
      atTop (𝓝 ((lam:ℂ)*∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r))) := by
  have hh := restrictedBlock_marked_limit hBV hlam
    (cumulativeProfile (tau+tau) (tensorProfile f g)) (tau+tau) (by positivity) (by linarith)
    (cumulativeProfile_budget _ _ (tensorProfile_tsupport f g hsf hsg))
    (cumulativeProfile_compact _ _ (tensorProfile_compact f g hf hg))
    (cumulativeProfile_smooth _ _ (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs))
    (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p))
  have he : (∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^(Fintype.card (Quotient r)+1)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r))=
      (lam:ℂ)*∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [pow_succ]
    ring
  change Tendsto _ _ (𝓝 (∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^(Fintype.card (Quotient r)+1)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r))) at hh
  rw [he] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  apply congrArg (fun z : ℝ => (z:ℂ))
  symm
  apply internalMarked_congr
  intro m c
  exact restrictedBlock_cumulative_mul hX _ _ m f g hsf hsg _ _ _

theorem restricted_cumulative_square_limit (hBV : BombieriVinogradov) {n : ℕ} {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsym : SymmetricFunction f) :
    Tendsto (fun X : ℕ => internalMarked X (blockLength lam X) (fun m c =>
      restrictedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) (Finset.univ.erase c) m^2))
      atTop (𝓝 (lam*alpha lam n*l2Mass f)) := by
  have hh := restricted_cumulative_pair_limit hBV htau htau2 hlam f f hf hf hfs hfs hsf hsf
  rw [cumulative_square_pattern_sum lam f hf hfs hsf hsym] at hh
  have hh' := Complex.continuous_re.continuousAt.tendsto.comp hh
  simpa [Function.comp_def,Complex.mul_re,←pow_two,mul_assoc] using hh'

theorem restricted_cumulative_cross_limit (hBV : BombieriVinogradov) {n p : ℕ} (hnp : n≠p) {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau) :
    Tendsto (fun X : ℕ => internalMarked X (blockLength lam X) (fun m c =>
      restrictedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) (Finset.univ.erase c) m*
      restrictedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau g) (subsetCoefficient p) (Finset.univ.erase c) m))
      atTop (𝓝 0) := by
  have hh := restricted_cumulative_pair_limit hBV htau htau2 hlam f g hf hg hfs hgs hsf hsg
  rw [cumulative_cross_pattern_sum hnp lam f g hf hg hfs hgs hsf hsg,mul_zero] at hh
  exact Complex.continuous_re.continuousAt.tendsto.comp hh

theorem restrictedWeight_marked_limit (hBV : BombieriVinogradov) {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam) :
    Tendsto (fun X : ℕ => internalMarked X (blockLength lam X) (fun m c => restrictedWeight tau lam k f X m c^2))
      atTop (𝓝 (lam*familyW lam k f)) := by
  classical
  let H := fun (j : Fin (k+1)) X m (c : Fin (blockLength lam X)) =>
    restrictedBlock X (blockLength lam X) (blockLength lam X+1)
      (cumulativeProfile tau (f j)) (subsetCoefficient j) (Finset.univ.erase c) m
  have hp (i j : Fin (k+1)) :
      Tendsto (fun X : ℕ => internalMarked X (blockLength lam X) (fun m c => H i X m c*H j X m c)) atTop
        (𝓝 (if i=j then lam*alpha lam i*l2Mass (f i) else 0)) := by
    have hfi := hf.2.1 i (by omega : (i:ℕ)≤k)
    have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
    by_cases hij : i=j
    · subst j
      simp only [↓reduceIte]
      simpa only [H,pow_two] using restricted_cumulative_square_limit hBV htau htau2 hlam
        (f i) hfi.2.1 hfi.1 hfi.2.2.1 hfi.2.2.2
    · simp only [ite_eq_right hij]
      have hne : (i:ℕ)≠(j:ℕ) := fun h => hij (Fin.ext h)
      exact restricted_cumulative_cross_limit hBV hne htau htau2 hlam
        (f i) (f j) hfi.2.1 hfj.2.1 hfi.1 hfj.1 hfi.2.2.1 hfj.2.2.1
  have hs := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => hp i j
  have he (X : ℕ) : internalMarked X (blockLength lam X) (fun m c => restrictedWeight tau lam k f X m c^2)=
      ∑ i : Fin (k+1),∑ j : Fin (k+1),internalMarked X (blockLength lam X) (fun m c => H i X m c*H j X m c) := by
    simp only [restrictedWeight,pow_two,Finset.sum_mul,Finset.mul_sum,internalMarked_finset_sum]
    rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte] at hs
  have hv : (∑ i : Fin (k+1),lam*alpha lam i*l2Mass (f i))=lam*familyW lam k f := by
    simp only [mul_assoc,←Finset.mul_sum]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => alpha lam j*l2Mass (f j)) (k+1)
  rw [hv] at hs
  exact hs.congr' (Eventually.of_forall fun X => (he X).symm)

theorem detector_I_eq (X h m : ℕ) :
    detector X (Finset.Ioc h (2*h)) m=
      (∑ c : Fin h,theta (m+(h+1+(c:ℕ))))/Real.log X := by
  unfold detector
  congr 1
  have he : Finset.Ioc h (2*h)=Finset.Ico (h+1) (h+1+h) := by
    ext i
    simp only [Finset.mem_Ioc,Finset.mem_Ico]
    omega
  rw [he,Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  symm
  exact Fin.sum_univ_eq_sum_range (fun c : ℕ => theta (m+(h+1+c))) h

theorem unorderedWeight_internal_delete_average {tau lam : ℝ} {k X : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : tau<1) (hX : 2≤X) (hk : k≤blockLength lam X) :
    average X (fun m => unorderedWeight tau lam k f X m^2*
      detector X (Finset.Ioc (blockLength lam X) (2*blockLength lam X)) m)=
      internalMarked X (blockLength lam X) (fun m c => restrictedWeight tau lam k (deletedFamily f) X m c^2) := by
  classical
  unfold internalMarked average
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  simp only [detector_I_eq,←mul_div_assoc,Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hp : Nat.Prime (m+(blockLength lam X+1+(c:ℕ)))
  · rw [unorderedWeight_prime_delete hf htau hX hk (Finset.mem_Ioc.mp hm).1 c hp]
  · simp [theta,hp]

theorem unorderedWeight_internal_marked_limit_oai (hBV : BombieriVinogradov) {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam) :
    Tendsto (fun X : ℕ => average X (fun m => unorderedWeight tau lam k f X m^2*
      detector X (Finset.Ioc (blockLength lam X) (2*blockLength lam X)) m))
      atTop (𝓝 (familyV lam k f)) := by
  have hh := restrictedWeight_marked_limit hBV (deletedFamily f) (deletedFamily_admissible hf)
    htau htau2 hlam
  change Tendsto _ _ (𝓝 (familyV lam k f)) at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2,(blockLength_tendsto hlam).eventually_ge_atTop k] with X hX hk
  exact (unorderedWeight_internal_delete_average f hf (by linarith) hX hk).symm

end LargePrimeGaps

end OAI
end

theorem solution : type_of% @OAI.LargePrimeGaps.unorderedWeight_internal_marked_limit_oai := @OAI.LargePrimeGaps.unorderedWeight_internal_marked_limit_oai
