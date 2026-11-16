-- Prove2me | solution 1 for GuthMaynard.abs_card_box_mul_sub_mod_le_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:21:29.800245+00:00
-- url     : https://prove2.me/submissions/4e919bcc-aaf2-41dd-92b7-4a4ce7ef7c45

import Mathlib
import Theorems.Thm_ArtinPrimitiveRoots_abs_card_box_mul_sub_mod_le

section
set_option autoImplicit false
namespace GuthMaynard.Twisted
open Finset
noncomputable section
/-!
# Twisted fourth moment (Maynard–Pratt, Lemma 24 input): blueprint

Target: `GuthMaynard.maynard_pratt_twisted_fourth_moment`.
Mathematics: `PLAN.md` and `BRIEF.md` in
`~/claude/guth-maynard-mission/proofs/maynard_pratt_twisted_fourth_moment/`.
Every `sorry` below is a stub proved by a Part; the assembly at the end is proved from the stubs.
-/
/-! ## Definitions -/

/-- The divisor function as a real number. -/
def dv (n : ℕ) : ℝ := (n.divisors.card : ℝ)

/-- `ρ(n; ℓ, h) = #{(x, y) mod n : ℓxy ≡ h}`. -/
def rho (n ℓ : ℕ) (h : ℤ) : ℕ :=
  #((Finset.range n ×ˢ Finset.range n).filter
    (fun z : ℕ × ℕ => (n : ℤ) ∣ (ℓ : ℤ) * z.1 * z.2 - h))

/-- The size of the error in the box count, without its constant. -/
def E0 (n : ℕ) (h : ℤ) : ℝ :=
  dv h.natAbs ^ 2 * |(h : ℝ)| * (dv n * (1 + Real.log n)) ^ 3 * (n : ℝ) ^ (3 / 4 : ℝ)

/-! ## Part S: the partition function, Abel summation, reindexing -/

/-! ## Part X: the expansion -/

end
end GuthMaynard.Twisted
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted.PartB
open Finset
noncomputable section
/-!
# Part B: counting on the modular hyperbola with a general residue

`rho_fourier`, `rho_le`, `box_count`.  The box count extends the Proved
`ArtinPrimitiveRoots.abs_card_box_mul_sub_mod_le` (with `S = 1`, coprime residue) to a general
residue by the gcd decomposition `a = e s a₂`, `b = f b₁` (`e f = gcd(r, n)`, Möbius over
`s ∣ f`), and identifies the density as `rho / n²` by letting the box `[0, mn)²` grow.
-/
/-- The weight in the error term. -/
def W (n : ℕ) : ℝ :=
  (n : ℝ) ^ (3 / 4 : ℝ) * ((n.divisors.card : ℝ) * (1 + Real.log n)) ^ 3

theorem W_aux (n : ℕ) (hn : 0 < n) :
    1 ≤ (n : ℝ) ^ (3 / 4 : ℝ) ∧ 1 ≤ (n.divisors.card : ℝ) ∧ 0 ≤ Real.log n := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨Real.one_le_rpow h1 (by norm_num), ?_, Real.log_nonneg h1⟩
  have : 0 < n.divisors.card := Finset.card_pos.mpr ⟨1, by simp [hn.ne']⟩
  exact_mod_cast this

theorem card_le_W (n : ℕ) (hn : 0 < n) : (n.divisors.card : ℝ) ≤ W n := by
  obtain ⟨h1, h2, h3⟩ := W_aux n hn
  have hb1 : (n.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) * (1 + Real.log n) := by nlinarith
  have hb1' : 1 ≤ (n.divisors.card : ℝ) * (1 + Real.log n) := le_trans h2 hb1
  unfold W
  calc (n.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) * (1 + Real.log n) := hb1
    _ ≤ ((n.divisors.card : ℝ) * (1 + Real.log n)) ^ 3 := le_self_pow₀ hb1' (by norm_num)
    _ ≤ _ := le_mul_of_one_le_left (by positivity) h1

theorem one_le_W (n : ℕ) (hn : 0 < n) : 1 ≤ W n :=
  le_trans (W_aux n hn).2.1 (card_le_W n hn)

theorem W_mono (m n : ℕ) (hmn : m ∣ n) (hn : 0 < n) : W m ≤ W n := by
  have hm : 0 < m := Nat.pos_of_dvd_of_pos hmn hn
  have hle : (m : ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd hn hmn
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨h1, h2, h3⟩ := W_aux m hm
  have hc : (m.divisors.card : ℝ) ≤ n.divisors.card := by
    exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' hmn)
  have hl : Real.log m ≤ Real.log n := Real.log_le_log (by linarith) hle
  unfold W
  have hr : (m : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hle (by norm_num)
  have hb : (m.divisors.card : ℝ) * (1 + Real.log m) ≤ (n.divisors.card : ℝ) * (1 + Real.log n) :=
    mul_le_mul hc (by linarith) (by linarith) (by linarith)
  have hb0 : 0 ≤ (m.divisors.card : ℝ) * (1 + Real.log m) := by positivity
  exact mul_le_mul hr (pow_le_pow_left₀ hb0 hb 3) (by positivity) (by positivity)

/-- The main-term numerator of the Proved lemma (it is `φ(n)`, which is never used). -/
def Phi (n : ℕ) : ℤ := ∑ l ∈ n.divisors, ArithmeticFunction.moebius l * ((n / l : ℕ) : ℤ)

def kap (n : ℕ) : ℝ := (Phi n : ℝ) / (n : ℝ) ^ 2

theorem abs_kap_le (n : ℕ) (hn : 0 < n) : |kap n| ≤ W n / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hP : |(Phi n : ℝ)| ≤ n.divisors.card * n := by
    have : |Phi n| ≤ n.divisors.card * n := by
      unfold Phi
      calc |∑ l ∈ n.divisors, ArithmeticFunction.moebius l * ((n / l : ℕ) : ℤ)|
          ≤ ∑ l ∈ n.divisors, |ArithmeticFunction.moebius l * ((n / l : ℕ) : ℤ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ l ∈ n.divisors, (n : ℤ) := by
            apply Finset.sum_le_sum
            intro l _
            rw [abs_mul]
            have h1 := ArithmeticFunction.abs_moebius_le_one (n := l)
            have h2 : |((n / l : ℕ) : ℤ)| ≤ n := by
              rw [Nat.abs_cast]; exact_mod_cast Nat.div_le_self n l
            calc _ ≤ 1 * (n : ℤ) := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
              _ = n := one_mul _
        _ = _ := by simp
    exact_mod_cast this
  unfold kap
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 2),
    div_le_div_iff₀ (by positivity) hn']
  have h3 := card_le_W n hn
  calc |(Phi n : ℝ)| * n ≤ (n.divisors.card * n) * n := by gcongr
    _ ≤ (W n * n) * n := by gcongr
    _ = W n * (n : ℝ) ^ 2 := by ring

theorem base (n : ℕ) (hn : 0 < n) (a : ℤ) (ha : IsCoprime a (n : ℤ)) (A₁ B₁ A₂ B₂ : ℤ)
    (h₁ : A₁ ≤ B₁) (h₂ : A₂ ≤ B₂) :
    |(#((Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter
        (fun p : ℤ × ℤ => (n : ℤ) ∣ p.1 * p.2 - a)) : ℝ) -
      ((B₁ - A₁ : ℤ) : ℝ) * ((B₂ - A₂ : ℤ) : ℝ) * kap n| ≤
      3 * W n * ((((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ) + 2) / n + 1) := by
  have h := ArtinPrimitiveRoots.abs_card_box_mul_sub_mod_le n 1 hn one_pos squarefree_one 0 0 a ha
    (by simp) A₁ B₁ A₂ B₂ h₁ h₂
  simp only [Nat.cast_one, one_dvd, true_and, mul_one, Nat.coprime_one_right_eq_true,
    Finset.filter_true] at h
  unfold kap Phi W
  rw [← mul_div_assoc]
  convert h using 1
  ring

def cdiv (A k : ℤ) : ℤ := -((-A) / k)

theorem le_mul_iff_cdiv (A k x : ℤ) (hk : 0 < k) : A ≤ k * x ↔ cdiv A k ≤ x := by
  unfold cdiv
  rw [neg_le, Int.le_ediv_iff_mul_le hk]
  constructor <;> intro h <;> linarith

theorem mul_lt_iff_cdiv (B k x : ℤ) (hk : 0 < k) : k * x < B ↔ x < cdiv B k := by
  rw [← not_le, ← not_le, le_mul_iff_cdiv B k x hk]

theorem cdiv_mono (A B k : ℤ) (hk : 0 < k) (h : A ≤ B) : cdiv A k ≤ cdiv B k :=
  (le_mul_iff_cdiv A k _ hk).mp (le_trans h ((le_mul_iff_cdiv B k _ hk).mpr le_rfl))

theorem cdiv_spec (A k : ℤ) (hk : 0 < k) : A ≤ k * cdiv A k ∧ k * cdiv A k < A + k := by
  refine ⟨(le_mul_iff_cdiv A k _ hk).mpr le_rfl, ?_⟩
  have h : ¬ A ≤ k * (cdiv A k - 1) := by rw [le_mul_iff_cdiv A k _ hk]; omega
  rw [mul_sub, mul_one] at h
  linarith

theorem cdiv_len (A B k : ℤ) (hk : 0 < k) :
    |((cdiv B k - cdiv A k : ℤ) : ℝ) - ((B - A : ℤ) : ℝ) / k| ≤ 1 := by
  obtain ⟨a1, a2⟩ := cdiv_spec A k hk
  obtain ⟨b1, b2⟩ := cdiv_spec B k hk
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have a1' : (A : ℝ) ≤ k * cdiv A k := by exact_mod_cast a1
  have a2' : (k : ℝ) * cdiv A k < A + k := by exact_mod_cast a2
  have b1' : (B : ℝ) ≤ k * cdiv B k := by exact_mod_cast b1
  have b2' : (k : ℝ) * cdiv B k < B + k := by exact_mod_cast b2
  have e : ((cdiv B k - cdiv A k : ℤ) : ℝ) - ((B - A : ℤ) : ℝ) / k =
      ((k : ℝ) * cdiv B k - k * cdiv A k - (B - A)) / k := by
    push_cast; field_simp
  rw [e, abs_div, abs_of_pos hk', div_le_one hk', abs_le]
  constructor <;> linarith

theorem card_scaled (A₁ B₁ A₂ B₂ k₁ k₂ : ℤ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (Q : ℤ → ℤ → Prop) [∀ x y, Decidable (Q x y)] :
    #((Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter
        (fun p : ℤ × ℤ => k₁ ∣ p.1 ∧ k₂ ∣ p.2 ∧ Q (p.1 / k₁) (p.2 / k₂))) =
    #((Finset.Ico (cdiv A₁ k₁) (cdiv B₁ k₁) ×ˢ Finset.Ico (cdiv A₂ k₂) (cdiv B₂ k₂)).filter
        (fun p : ℤ × ℤ => Q p.1 p.2)) := by
  symm
  refine Finset.card_bij' (fun p _ => (k₁ * p.1, k₂ * p.2)) (fun p _ => (p.1 / k₁, p.2 / k₂))
    ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    simp only [mem_filter, mem_product, mem_Ico] at hp ⊢
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, hQ⟩ := hp
    refine ⟨⟨⟨(le_mul_iff_cdiv _ _ _ hk₁).mpr h1, (mul_lt_iff_cdiv _ _ _ hk₁).mpr h2⟩,
      (le_mul_iff_cdiv _ _ _ hk₂).mpr h3, (mul_lt_iff_cdiv _ _ _ hk₂).mpr h4⟩,
      dvd_mul_right _ _, dvd_mul_right _ _, ?_⟩
    rwa [Int.mul_ediv_cancel_left _ hk₁.ne', Int.mul_ediv_cancel_left _ hk₂.ne']
  · rintro ⟨a, b⟩ hp
    simp only [mem_filter, mem_product, mem_Ico] at hp ⊢
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, ⟨x, rfl⟩, ⟨y, rfl⟩, hQ⟩ := hp
    rw [Int.mul_ediv_cancel_left _ hk₁.ne', Int.mul_ediv_cancel_left _ hk₂.ne'] at hQ ⊢
    exact ⟨⟨⟨(le_mul_iff_cdiv _ _ _ hk₁).mp h1, (mul_lt_iff_cdiv _ _ _ hk₁).mp h2⟩,
      (le_mul_iff_cdiv _ _ _ hk₂).mp h3, (mul_lt_iff_cdiv _ _ _ hk₂).mp h4⟩, hQ⟩
  · rintro ⟨x, y⟩ _
    simp [Int.mul_ediv_cancel_left _ hk₁.ne', Int.mul_ediv_cancel_left _ hk₂.ne']
  · rintro ⟨a, b⟩ hp
    simp only [mem_filter] at hp
    obtain ⟨_, ⟨x, rfl⟩, ⟨y, rfl⟩, _⟩ := hp
    simp [Int.mul_ediv_cancel_left _ hk₁.ne', Int.mul_ediv_cancel_left _ hk₂.ne']

theorem sum_moebius_divisors (m : ℕ) :
    ∑ s ∈ m.divisors, ArithmeticFunction.moebius s = if m = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
    ArithmeticFunction.one_apply]

theorem inner_mobius (e f : ℕ) (he : 0 < e) (hf : 0 < f) (n₃ : ℕ) (r₃ a b : ℤ) :
    ∑ s ∈ f.divisors, ArithmeticFunction.moebius s *
      (if ((e : ℤ) * s) ∣ a ∧ (f : ℤ) ∣ b ∧
          (n₃ : ℤ) ∣ (s : ℤ) * (a / ((e : ℤ) * s)) * (b / (f : ℤ)) - r₃ then (1 : ℤ) else 0) =
    if (e : ℤ) ∣ a ∧ (f : ℤ) ∣ b ∧ (n₃ : ℤ) ∣ (a / e) * (b / f) - r₃ ∧
        Int.gcd (a / e) f = 1 then 1 else 0 := by
  by_cases hea : (e : ℤ) ∣ a
  swap
  · rw [if_neg (fun h => hea h.1)]
    apply Finset.sum_eq_zero
    intro s _
    rw [if_neg (fun h => hea (dvd_trans (dvd_mul_right _ _) h.1)), mul_zero]
  obtain ⟨a₁, rfl⟩ := hea
  have he' : (e : ℤ) ≠ 0 := by exact_mod_cast he.ne'
  rw [Int.mul_ediv_cancel_left _ he']
  have hterm : ∀ s ∈ f.divisors, ArithmeticFunction.moebius s *
      (if ((e : ℤ) * s) ∣ (e : ℤ) * a₁ ∧ (f : ℤ) ∣ b ∧
          (n₃ : ℤ) ∣ (s : ℤ) * ((e : ℤ) * a₁ / ((e : ℤ) * s)) * (b / (f : ℤ)) - r₃
        then (1 : ℤ) else 0) =
      (if (s : ℤ) ∣ a₁ then ArithmeticFunction.moebius s else 0) *
        (if (f : ℤ) ∣ b ∧ (n₃ : ℤ) ∣ a₁ * (b / f) - r₃ then 1 else 0) := by
    intro s hs
    have hs0 : (s : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hs).ne'
    by_cases hsa : (s : ℤ) ∣ a₁
    · obtain ⟨a₂, rfl⟩ := hsa
      have h1 : (e : ℤ) * s ∣ e * (s * a₂) := ⟨a₂, by ring⟩
      have h2 : (e : ℤ) * (s * a₂) / (e * s) = a₂ := by
        rw [← mul_assoc, Int.mul_ediv_cancel_left _ (mul_ne_zero he' hs0)]
      rw [h2, if_pos (dvd_mul_right _ _)]
      simp only [h1, true_and]
    · have h3 : ¬ ((e : ℤ) * s ∣ e * a₁) := fun h => hsa ((mul_dvd_mul_iff_left he').mp h)
      rw [if_neg hsa, if_neg (fun h => h3 h.1)]
      simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.sum_filter]
  have hf' : (f : ℤ) ≠ 0 := by exact_mod_cast hf.ne'
  have hfilt : f.divisors.filter (fun s : ℕ => (s : ℤ) ∣ a₁) = (Int.gcd a₁ f).divisors := by
    ext s
    simp only [mem_filter, Nat.mem_divisors]
    rw [← Int.natCast_dvd_natCast (m := s) (n := Int.gcd a₁ f), Int.dvd_coe_gcd_iff,
      Int.natCast_dvd_natCast]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨⟨h2, h1⟩, by simp [Int.gcd_eq_zero_iff, hf.ne']⟩
    · rintro ⟨⟨h1, h2⟩, _⟩
      exact ⟨⟨h2, hf.ne'⟩, h1⟩
  rw [hfilt, sum_moebius_divisors]
  have he1 : (e : ℤ) ∣ e * a₁ := dvd_mul_right _ _
  by_cases h1 : Int.gcd a₁ f = 1 <;>
    by_cases h2 : ((f : ℤ) ∣ b ∧ (n₃ : ℤ) ∣ a₁ * (b / f) - r₃) <;>
    simp [h1, h2, he1]

theorem outer_A (e f n₃ : ℕ) (he : 0 < e) (hf : 0 < f) (r₃ a b : ℤ)
    (hP : (e : ℤ) ∣ a ∧ (f : ℤ) ∣ b ∧ (n₃ : ℤ) ∣ (a / e) * (b / f) - r₃ ∧
      Int.gcd (a / e) f = 1) :
    ((e * f * n₃ : ℕ) : ℤ) ∣ a * b - ((e * f : ℕ) : ℤ) * r₃ ∧ e = Int.gcd a ((e * f : ℕ) : ℤ) := by
  obtain ⟨⟨a₁, rfl⟩, ⟨b₁, rfl⟩, hdiv, hgcd⟩ := hP
  have he' : (e : ℤ) ≠ 0 := by exact_mod_cast he.ne'
  have hf' : (f : ℤ) ≠ 0 := by exact_mod_cast hf.ne'
  rw [Int.mul_ediv_cancel_left _ he'] at hdiv hgcd
  rw [Int.mul_ediv_cancel_left _ hf'] at hdiv
  constructor
  · obtain ⟨c, hc⟩ := hdiv
    exact ⟨c, by push_cast; linear_combination ((e : ℤ) * f) * hc⟩
  · push_cast
    rw [Int.gcd_mul_left, hgcd]
    simp

theorem outer_B (e₀ f n₃ : ℕ) (he : 0 < e₀) (hf : 0 < f) (r₃ a₁ b : ℤ)
    (hgcd : Int.gcd ((e₀ : ℤ) * a₁) ((e₀ * f : ℕ) : ℤ) = e₀)
    (h : ((e₀ * f * n₃ : ℕ) : ℤ) ∣ (e₀ : ℤ) * a₁ * b - ((e₀ * f : ℕ) : ℤ) * r₃) :
    (f : ℤ) ∣ b ∧ (n₃ : ℤ) ∣ a₁ * (b / f) - r₃ ∧ Int.gcd a₁ f = 1 := by
  have he' : (e₀ : ℤ) ≠ 0 := by exact_mod_cast he.ne'
  have hf' : (f : ℤ) ≠ 0 := by exact_mod_cast hf.ne'
  have hg1 : Int.gcd a₁ f = 1 := by
    push_cast at hgcd
    rw [Int.gcd_mul_left, Int.natAbs_natCast] at hgcd
    exact Nat.eq_of_mul_eq_mul_left he (by rw [hgcd, mul_one])
  have hfb : (f : ℤ) ∣ b := by
    have h1 : (e₀ : ℤ) * f ∣ (e₀ : ℤ) * a₁ * b - ((e₀ * f : ℕ) : ℤ) * r₃ :=
      dvd_trans ⟨(n₃ : ℤ), by push_cast; ring⟩ h
    have h2 : (e₀ : ℤ) * f ∣ (e₀ : ℤ) * (a₁ * b) := by
      have := dvd_add h1 (dvd_mul_right ((e₀ : ℤ) * f) r₃)
      push_cast at this
      have e : (e₀ : ℤ) * (a₁ * b) =
          (e₀ : ℤ) * a₁ * b - (e₀ : ℤ) * f * r₃ + (e₀ : ℤ) * f * r₃ := by ring
      rw [e]
      exact this
    have h3 : (f : ℤ) ∣ a₁ * b := (mul_dvd_mul_iff_left he').mp h2
    exact Int.dvd_of_dvd_mul_right_of_gcd_one (by rwa [mul_comm] at h3)
      (by rwa [Int.gcd_comm])
  refine ⟨hfb, ?_, hg1⟩
  obtain ⟨b₁, rfl⟩ := hfb
  rw [Int.mul_ediv_cancel_left _ hf']
  have h4 : ((e₀ : ℤ) * f) * n₃ ∣ ((e₀ : ℤ) * f) * (a₁ * b₁ - r₃) := by
    convert h using 1
    · push_cast; ring
    · push_cast; ring
  exact (mul_dvd_mul_iff_left (mul_ne_zero he' hf')).mp h4

theorem outer_ident (g n₃ : ℕ) (hg : 0 < g) (r₃ a b : ℤ) :
    ∑ e ∈ g.divisors, (if (e : ℤ) ∣ a ∧ ((g / e : ℕ) : ℤ) ∣ b ∧
        (n₃ : ℤ) ∣ (a / e) * (b / ((g / e : ℕ) : ℤ)) - r₃ ∧
        Int.gcd (a / e) ((g / e : ℕ) : ℤ) = 1 then (1 : ℤ) else 0) =
    if ((g * n₃ : ℕ) : ℤ) ∣ a * b - (g : ℤ) * r₃ then 1 else 0 := by
  have hA : ∀ e ∈ g.divisors, ((e : ℤ) ∣ a ∧ ((g / e : ℕ) : ℤ) ∣ b ∧
        (n₃ : ℤ) ∣ (a / e) * (b / ((g / e : ℕ) : ℤ)) - r₃ ∧
        Int.gcd (a / e) ((g / e : ℕ) : ℤ) = 1) →
      ((g * n₃ : ℕ) : ℤ) ∣ a * b - (g : ℤ) * r₃ ∧ e = Int.gcd a g := by
    intro e he hP
    obtain ⟨f, rfl⟩ := Nat.dvd_of_mem_divisors he
    have hepos : 0 < e := Nat.pos_of_mul_pos_right hg |> fun _ => Nat.pos_of_ne_zero (by rintro rfl; simp at hg)
    have hfpos : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hg)
    rw [Nat.mul_div_cancel_left f hepos] at hP
    exact outer_A e f n₃ hepos hfpos r₃ a b hP
  by_cases h : ((g * n₃ : ℕ) : ℤ) ∣ a * b - (g : ℤ) * r₃
  · rw [if_pos h]
    obtain ⟨e₀, he₀⟩ : ∃ e₀ : ℕ, Int.gcd a g = e₀ := ⟨_, rfl⟩
    have he₀g : e₀ ∣ g := by
      have : ((Int.gcd a g : ℕ) : ℤ) ∣ (g : ℤ) := Int.gcd_dvd_right a g
      rw [he₀] at this
      exact_mod_cast this
    have he₀a : (e₀ : ℤ) ∣ a := by rw [← he₀]; exact Int.gcd_dvd_left a g
    have hB : (e₀ : ℤ) ∣ a ∧ ((g / e₀ : ℕ) : ℤ) ∣ b ∧
        (n₃ : ℤ) ∣ (a / e₀) * (b / ((g / e₀ : ℕ) : ℤ)) - r₃ ∧
        Int.gcd (a / e₀) ((g / e₀ : ℕ) : ℤ) = 1 := by
      obtain ⟨f, rfl⟩ := he₀g
      obtain ⟨a₁, rfl⟩ := he₀a
      have hepos : 0 < e₀ := Nat.pos_of_ne_zero (by rintro rfl; simp at hg)
      have hfpos : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hg)
      have he' : (e₀ : ℤ) ≠ 0 := by exact_mod_cast hepos.ne'
      rw [Nat.mul_div_cancel_left f hepos, Int.mul_ediv_cancel_left _ he']
      obtain ⟨h1, h2, h3⟩ := outer_B e₀ f n₃ hepos hfpos r₃ a₁ b he₀ h
      exact ⟨dvd_mul_right _ _, h1, h2, h3⟩
    have hiff : ∀ e ∈ g.divisors, (((e : ℤ) ∣ a ∧ ((g / e : ℕ) : ℤ) ∣ b ∧
        (n₃ : ℤ) ∣ (a / e) * (b / ((g / e : ℕ) : ℤ)) - r₃ ∧
        Int.gcd (a / e) ((g / e : ℕ) : ℤ) = 1) ↔ e = e₀) := by
      intro e he
      constructor
      · intro hP; rw [← he₀]; exact (hA e he hP).2
      · rintro rfl; exact hB
    rw [Finset.sum_congr rfl (fun e he => if_congr (hiff e he) rfl rfl), Finset.sum_ite_eq',
      if_pos (Nat.mem_divisors.mpr ⟨he₀g, hg.ne'⟩)]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro e he
    rw [if_neg (fun hP => h (hA e he hP).1)]

/-- The pointwise decomposition of the indicator of `g n₃ ∣ ab - g r₃`. -/
theorem indicator_ident (g n₃ : ℕ) (hg : 0 < g) (r₃ a b : ℤ) :
    (if ((g * n₃ : ℕ) : ℤ) ∣ a * b - (g : ℤ) * r₃ then (1 : ℤ) else 0) =
    ∑ e ∈ g.divisors, ∑ s ∈ (g / e).divisors, ArithmeticFunction.moebius s *
      (if ((e : ℤ) * s) ∣ a ∧ ((g / e : ℕ) : ℤ) ∣ b ∧
          (n₃ : ℤ) ∣ (s : ℤ) * (a / ((e : ℤ) * s)) * (b / ((g / e : ℕ) : ℤ)) - r₃
        then (1 : ℤ) else 0) := by
  rw [← outer_ident g n₃ hg r₃ a b]
  apply Finset.sum_congr rfl
  intro e he
  have hepos : 0 < e := Nat.pos_of_mem_divisors he
  have hfpos : 0 < g / e :=
    Nat.div_pos (Nat.le_of_dvd hg (Nat.dvd_of_mem_divisors he)) hepos
  exact (inner_mobius e (g / e) hepos hfpos n₃ r₃ a b).symm

theorem piece0 (n₃ : ℕ) (hn₃ : 0 < n₃) (r₃ : ℤ) (hcop : IsCoprime r₃ (n₃ : ℤ)) (s : ℤ) :
    ∃ κ : ℝ, |κ| ≤ W n₃ / n₃ ∧ ∀ A₁ B₁ A₂ B₂ : ℤ, A₁ ≤ B₁ → A₂ ≤ B₂ →
      |(#((Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter
          (fun p : ℤ × ℤ => (n₃ : ℤ) ∣ s * p.1 * p.2 - r₃)) : ℝ) -
        ((B₁ - A₁ : ℤ) : ℝ) * ((B₂ - A₂ : ℤ) : ℝ) * κ| ≤
        3 * W n₃ * ((((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ) + 2) / n₃ + 1) := by
  have hW := one_le_W n₃ hn₃
  by_cases hs : IsCoprime s (n₃ : ℤ)
  · obtain ⟨u, v, huv⟩ := hs
    refine ⟨kap n₃, abs_kap_le n₃ hn₃, ?_⟩
    intro A₁ B₁ A₂ B₂ h₁ h₂
    have hfilt : (Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter
          (fun p : ℤ × ℤ => (n₃ : ℤ) ∣ s * p.1 * p.2 - r₃) =
        (Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter
          (fun p : ℤ × ℤ => (n₃ : ℤ) ∣ p.1 * p.2 - u * r₃) := by
      apply Finset.filter_congr
      rintro ⟨x, y⟩ _
      constructor
      · rintro ⟨c, hc⟩
        exact ⟨u * c + v * x * y, by linear_combination u * hc - (x * y) * huv⟩
      · rintro ⟨c, hc⟩
        exact ⟨s * c - v * r₃, by linear_combination s * hc + r₃ * huv⟩
    rw [hfilt]
    have hu : IsCoprime u (n₃ : ℤ) := ⟨s, v, by linear_combination huv⟩
    exact base n₃ hn₃ (u * r₃) (hu.mul_left hcop) A₁ B₁ A₂ B₂ h₁ h₂
  · refine ⟨0, by rw [abs_zero]; positivity, ?_⟩
    intro A₁ B₁ A₂ B₂ h₁ h₂
    have hempty : (Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter
          (fun p : ℤ × ℤ => (n₃ : ℤ) ∣ s * p.1 * p.2 - r₃) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      rintro ⟨x, y⟩ _ ⟨c, hc⟩
      obtain ⟨u, v, huv⟩ := hcop
      exact hs ⟨u * x * y, v - u * c, by linear_combination huv + u * hc⟩
    have hw₁ : (0 : ℝ) ≤ ((B₁ - A₁ : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr h₁
    have hw₂ : (0 : ℝ) ≤ ((B₂ - A₂ : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr h₂
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero, sub_zero, abs_zero]
    exact mul_nonneg (by linarith)
      (add_nonneg (div_nonneg (by linarith) (Nat.cast_nonneg _)) zero_le_one)

theorem round_arith (Wn N w₁ w₂ k₁ k₂ l₁ l₂ κ T : ℝ) (hW : 1 ≤ Wn) (hN : 1 ≤ N)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂)
    (h₁ : |l₁ - w₁ / k₁| ≤ 1) (h₂ : |l₂ - w₂ / k₂| ≤ 1) (hκ : |κ| ≤ Wn / N)
    (hT : |T - l₁ * l₂ * κ| ≤ 3 * Wn * ((l₁ + l₂ + 2) / N + 1)) :
    |T - κ / (k₁ * k₂) * w₁ * w₂| ≤ 16 * Wn * (1 + (w₁ + w₂) / N) := by
  have hN0 : 0 < N := by linarith
  have hx₁ : 0 ≤ w₁ / k₁ := div_nonneg hw₁ (by linarith)
  have hx₁' : w₁ / k₁ ≤ w₁ := div_le_self hw₁ hk₁
  have hx₂ : 0 ≤ w₂ / k₂ := div_nonneg hw₂ (by linarith)
  have hx₂' : w₂ / k₂ ≤ w₂ := div_le_self hw₂ hk₂
  have e : κ / (k₁ * k₂) * w₁ * w₂ = (w₁ / k₁) * (w₂ / k₂) * κ := by
    have : k₁ ≠ 0 := by linarith
    have : k₂ ≠ 0 := by linarith
    field_simp
  rw [e]
  generalize w₁ / k₁ = x₁ at *
  generalize w₂ / k₂ = x₂ at *
  rw [abs_le] at h₁ h₂
  obtain ⟨h1a, h1b⟩ := h₁
  obtain ⟨h2a, h2b⟩ := h₂
  have hd : |l₁ * l₂ - x₁ * x₂| ≤ w₁ + w₂ + 1 := by
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 + (l₁ - x₁)) (by linarith : (0:ℝ) ≤ 1 + (l₂ - x₂)),
        mul_nonneg (by linarith : (0:ℝ) ≤ 1 - (l₁ - x₁)) (by linarith : (0:ℝ) ≤ 1 - (l₂ - x₂)),
        mul_nonneg hx₂ (by linarith : (0:ℝ) ≤ 1 + (l₁ - x₁)),
        mul_nonneg hx₁ (by linarith : (0:ℝ) ≤ 1 + (l₂ - x₂))]
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 + (l₁ - x₁)) (by linarith : (0:ℝ) ≤ 1 - (l₂ - x₂)),
        mul_nonneg (by linarith : (0:ℝ) ≤ 1 - (l₁ - x₁)) (by linarith : (0:ℝ) ≤ 1 + (l₂ - x₂)),
        mul_nonneg hx₂ (by linarith : (0:ℝ) ≤ 1 - (l₁ - x₁)),
        mul_nonneg hx₁ (by linarith : (0:ℝ) ≤ 1 - (l₂ - x₂))]
  have h3 : |T - x₁ * x₂ * κ| ≤ |T - l₁ * l₂ * κ| + |κ| * (w₁ + w₂ + 1) := by
    calc |T - x₁ * x₂ * κ| = |(T - l₁ * l₂ * κ) + (l₁ * l₂ - x₁ * x₂) * κ| := by
          congr 1; ring
      _ ≤ |T - l₁ * l₂ * κ| + |(l₁ * l₂ - x₁ * x₂) * κ| := abs_add_le _ _
      _ ≤ _ := by
          have h7 := mul_le_mul_of_nonneg_left hd (abs_nonneg κ)
          rw [abs_mul]
          linarith [mul_comm |κ| |l₁ * l₂ - x₁ * x₂|]
  have hl : l₁ + l₂ + 2 ≤ w₁ + w₂ + 4 := by linarith
  have h4 : 3 * Wn * ((l₁ + l₂ + 2) / N + 1) ≤ 3 * Wn * ((w₁ + w₂ + 4) / N + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [div_le_div_of_nonneg_right hl hN0.le]) (by linarith)
  have h5 : |κ| * (w₁ + w₂ + 1) ≤ Wn / N * (w₁ + w₂ + 1) :=
    mul_le_mul_of_nonneg_right hκ (by linarith)
  have h6 : 3 * Wn * ((w₁ + w₂ + 4) / N + 1) + Wn / N * (w₁ + w₂ + 1) ≤
      16 * Wn * (1 + (w₁ + w₂) / N) := by
    have hu : 1 / N ≤ 1 := by rw [div_le_one hN0]; exact hN
    have hu0 : 0 < 1 / N := by positivity
    have e1 : 3 * Wn * ((w₁ + w₂ + 4) / N + 1) + Wn / N * (w₁ + w₂ + 1) =
        Wn * (4 * (w₁ + w₂) * (1 / N) + 13 * (1 / N) + 3) := by ring
    have e2 : 16 * Wn * (1 + (w₁ + w₂) / N) = Wn * (16 + 16 * (w₁ + w₂) * (1 / N)) := by ring
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    nlinarith [mul_nonneg (add_nonneg hw₁ hw₂) hu0.le]
  linarith

theorem piece (n₃ : ℕ) (hn₃ : 0 < n₃) (r₃ : ℤ) (hcop : IsCoprime r₃ (n₃ : ℤ)) (s k₁ k₂ : ℤ)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) :
    ∃ δ : ℝ, ∀ A₁ B₁ A₂ B₂ : ℤ, A₁ ≤ B₁ → A₂ ≤ B₂ →
      |(#((Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter
          (fun p : ℤ × ℤ => k₁ ∣ p.1 ∧ k₂ ∣ p.2 ∧
            (n₃ : ℤ) ∣ s * (p.1 / k₁) * (p.2 / k₂) - r₃)) : ℝ) -
        δ * ((B₁ - A₁ : ℤ) : ℝ) * ((B₂ - A₂ : ℤ) : ℝ)| ≤
        16 * W n₃ * (1 + (((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ)) / n₃) := by
  obtain ⟨κ, hκ, hbox⟩ := piece0 n₃ hn₃ r₃ hcop s
  refine ⟨κ / ((k₁ : ℝ) * k₂), ?_⟩
  intro A₁ B₁ A₂ B₂ h₁ h₂
  have hc : #((Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter
          (fun p : ℤ × ℤ => k₁ ∣ p.1 ∧ k₂ ∣ p.2 ∧
            (n₃ : ℤ) ∣ s * (p.1 / k₁) * (p.2 / k₂) - r₃)) =
      #((Finset.Ico (cdiv A₁ k₁) (cdiv B₁ k₁) ×ˢ Finset.Ico (cdiv A₂ k₂) (cdiv B₂ k₂)).filter
        (fun p : ℤ × ℤ => (n₃ : ℤ) ∣ s * p.1 * p.2 - r₃)) :=
    card_scaled A₁ B₁ A₂ B₂ k₁ k₂ hk₁ hk₂ (fun x y => (n₃ : ℤ) ∣ s * x * y - r₃)
  rw [hc]
  have hT := hbox _ _ _ _ (cdiv_mono A₁ B₁ k₁ hk₁ h₁) (cdiv_mono A₂ B₂ k₂ hk₂ h₂)
  have hk₁' : (1 : ℤ) ≤ k₁ := hk₁
  have hk₂' : (1 : ℤ) ≤ k₂ := hk₂
  exact round_arith (W n₃) n₃ _ _ k₁ k₂ _ _ κ _ (one_le_W n₃ hn₃) (by exact_mod_cast hn₃)
    (by exact_mod_cast sub_nonneg.mpr h₁) (by exact_mod_cast sub_nonneg.mpr h₂)
    (by exact_mod_cast hk₁') (by exact_mod_cast hk₂')
    (cdiv_len A₁ B₁ k₁ hk₁) (cdiv_len A₂ B₂ k₂ hk₂) hκ hT

theorem key_scale (g N x : ℝ) (hg : 1 ≤ g) (hN : 0 < N) (_hx : 0 ≤ x) :
    1 + x / N ≤ g * (1 + x / (g * N)) := by
  have hg0 : g ≠ 0 := by linarith
  have e : g * (x / (g * N)) = x / N := by field_simp
  rw [mul_add, mul_one, e]
  linarith

theorem core (g n₃ : ℕ) (hg : 0 < g) (hn₃ : 0 < n₃) (r₃ : ℤ) (hcop : IsCoprime r₃ (n₃ : ℤ)) :
    ∃ D : ℝ, ∀ A₁ B₁ A₂ B₂ : ℤ, A₁ ≤ B₁ → A₂ ≤ B₂ →
      |(#((Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter
          (fun p : ℤ × ℤ => ((g * n₃ : ℕ) : ℤ) ∣ p.1 * p.2 - (g : ℤ) * r₃)) : ℝ) -
        D * ((B₁ - A₁ : ℤ) : ℝ) * ((B₂ - A₂ : ℤ) : ℝ)| ≤
        16 * (g.divisors.card : ℝ) ^ 2 * W n₃ *
          (1 + (((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ)) / n₃) := by
  have hp : ∀ e s : ℕ, ∃ δ : ℝ, e ∈ g.divisors → s ∈ (g / e).divisors →
      ∀ A₁ B₁ A₂ B₂ : ℤ, A₁ ≤ B₁ → A₂ ≤ B₂ →
      |(#((Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter
          (fun p : ℤ × ℤ => ((e : ℤ) * s) ∣ p.1 ∧ ((g / e : ℕ) : ℤ) ∣ p.2 ∧
            (n₃ : ℤ) ∣ (s : ℤ) * (p.1 / ((e : ℤ) * s)) * (p.2 / ((g / e : ℕ) : ℤ)) - r₃)) : ℝ) -
        δ * ((B₁ - A₁ : ℤ) : ℝ) * ((B₂ - A₂ : ℤ) : ℝ)| ≤
        16 * W n₃ * (1 + (((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ)) / n₃) := by
    intro e s
    by_cases he : e ∈ g.divisors ∧ s ∈ (g / e).divisors
    · have hepos : 0 < e := Nat.pos_of_mem_divisors he.1
      have hspos : 0 < s := Nat.pos_of_mem_divisors he.2
      have hfpos : 0 < g / e :=
        Nat.div_pos (Nat.le_of_dvd hg (Nat.dvd_of_mem_divisors he.1)) hepos
      obtain ⟨δ, hδ⟩ := piece n₃ hn₃ r₃ hcop s ((e : ℤ) * s) ((g / e : ℕ) : ℤ)
        (by positivity) (by exact_mod_cast hfpos)
      exact ⟨δ, fun _ _ => hδ⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ he⟩
  choose δ hδ using hp
  refine ⟨∑ e ∈ g.divisors, ∑ s ∈ (g / e).divisors,
    (ArithmeticFunction.moebius s : ℝ) * δ e s, ?_⟩
  intro A₁ B₁ A₂ B₂ h₁ h₂
  have hW := one_le_W n₃ hn₃
  have hw₁ : (0 : ℝ) ≤ ((B₁ - A₁ : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr h₁
  have hw₂ : (0 : ℝ) ≤ ((B₂ - A₂ : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr h₂
  have hR : 0 ≤ 16 * W n₃ * (1 + (((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ)) / n₃) :=
    mul_nonneg (by linarith)
      (add_nonneg zero_le_one (div_nonneg (by linarith) (Nat.cast_nonneg _)))
  have hZ : ((#((Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter
          (fun p : ℤ × ℤ => ((g * n₃ : ℕ) : ℤ) ∣ p.1 * p.2 - (g : ℤ) * r₃)) : ℕ) : ℤ) =
      ∑ e ∈ g.divisors, ∑ s ∈ (g / e).divisors, ArithmeticFunction.moebius s *
        ((#((Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter
          (fun p : ℤ × ℤ => ((e : ℤ) * s) ∣ p.1 ∧ ((g / e : ℕ) : ℤ) ∣ p.2 ∧
            (n₃ : ℤ) ∣ (s : ℤ) * (p.1 / ((e : ℤ) * s)) * (p.2 / ((g / e : ℕ) : ℤ)) - r₃)) : ℕ) : ℤ) := by
    rw [Finset.natCast_card_filter,
      Finset.sum_congr rfl (fun p _ => indicator_ident g n₃ hg r₃ p.1 p.2), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.natCast_card_filter, Finset.mul_sum]
  have hcount : (#((Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter
          (fun p : ℤ × ℤ => ((g * n₃ : ℕ) : ℤ) ∣ p.1 * p.2 - (g : ℤ) * r₃)) : ℝ) =
      ∑ e ∈ g.divisors, ∑ s ∈ (g / e).divisors, (ArithmeticFunction.moebius s : ℝ) *
        (#((Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter
          (fun p : ℤ × ℤ => ((e : ℤ) * s) ∣ p.1 ∧ ((g / e : ℕ) : ℤ) ∣ p.2 ∧
            (n₃ : ℤ) ∣ (s : ℤ) * (p.1 / ((e : ℤ) * s)) * (p.2 / ((g / e : ℕ) : ℤ)) - r₃)) : ℝ) := by
    exact_mod_cast hZ
  rw [hcount, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ e ∈ g.divisors, ∑ s ∈ (g / e).divisors,
        16 * W n₃ * (1 + (((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ)) / n₃) := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro e he
        rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro s hs
        have hμ : |(ArithmeticFunction.moebius s : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := s)
        have h3 := hδ e s he hs A₁ B₁ A₂ B₂ h₁ h₂
        rw [mul_assoc, mul_assoc, ← mul_sub, abs_mul, ← mul_assoc]
        calc _ ≤ 1 * _ := mul_le_mul hμ h3 (abs_nonneg _) zero_le_one
          _ = _ := one_mul _
    _ ≤ ∑ e ∈ g.divisors, (g.divisors.card : ℝ) *
          (16 * W n₃ * (1 + (((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ)) / n₃)) := by
        apply Finset.sum_le_sum
        intro e he
        rw [Finset.sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ hR
        exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hg.ne'
          (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors he)))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

theorem core' (n : ℕ) (hn : 0 < n) (r : ℤ) :
    ∃ D : ℝ, ∀ A₁ B₁ A₂ B₂ : ℤ, A₁ ≤ B₁ → A₂ ≤ B₂ →
      |(#((Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter
          (fun p : ℤ × ℤ => (n : ℤ) ∣ p.1 * p.2 - r)) : ℝ) -
        D * ((B₁ - A₁ : ℤ) : ℝ) * ((B₂ - A₂ : ℤ) : ℝ)| ≤
        16 * ((Int.gcd r n).divisors.card : ℝ) ^ 2 * (Int.gcd r n : ℝ) * W n *
          (1 + (((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ)) / n) := by
  obtain ⟨g, hgdef⟩ : ∃ g : ℕ, Int.gcd r n = g := ⟨_, rfl⟩
  have hgn : g ∣ n := by
    have : ((Int.gcd r n : ℕ) : ℤ) ∣ (n : ℤ) := Int.gcd_dvd_right r n
    rw [hgdef] at this
    exact_mod_cast this
  have hgr : (g : ℤ) ∣ r := by rw [← hgdef]; exact Int.gcd_dvd_left r n
  obtain ⟨n₃, rfl⟩ := hgn
  obtain ⟨r₃, rfl⟩ := hgr
  have hg : 0 < g := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hn₃ : 0 < n₃ := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hcop : IsCoprime r₃ (n₃ : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    push_cast at hgdef
    rw [Int.gcd_mul_left, Int.natAbs_natCast] at hgdef
    exact Nat.eq_of_mul_eq_mul_left hg (by rw [hgdef, mul_one])
  obtain ⟨D, hD⟩ := core g n₃ hg hn₃ r₃ hcop
  refine ⟨D, ?_⟩
  intro A₁ B₁ A₂ B₂ h₁ h₂
  rw [hgdef]
  refine (hD A₁ B₁ A₂ B₂ h₁ h₂).trans ?_
  have hW := W_mono n₃ (g * n₃) (dvd_mul_left _ _) hn
  have hW1 := one_le_W n₃ hn₃
  have hw₁ : (0 : ℝ) ≤ ((B₁ - A₁ : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr h₁
  have hw₂ : (0 : ℝ) ≤ ((B₂ - A₂ : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr h₂
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hn₃' : (0 : ℝ) < n₃ := by exact_mod_cast hn₃
  have key := key_scale g n₃ (((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ)) hg1 hn₃'
    (by linarith)
  have hcast : ((g * n₃ : ℕ) : ℝ) = (g : ℝ) * n₃ := by push_cast; ring
  rw [hcast]
  have hd0 : (0 : ℝ) ≤ 16 * (g.divisors.card : ℝ) ^ 2 := by positivity
  have hpos : (0 : ℝ) ≤ 1 + (((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ)) / n₃ :=
    add_nonneg zero_le_one (div_nonneg (by linarith) hn₃'.le)
  calc 16 * (g.divisors.card : ℝ) ^ 2 * W n₃ *
        (1 + (((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ)) / n₃)
      ≤ 16 * (g.divisors.card : ℝ) ^ 2 * W (g * n₃) *
        ((g : ℝ) * (1 + (((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ)) / ((g : ℝ) * n₃))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hW hd0) key hpos
          (mul_nonneg hd0 (by linarith))
    _ = _ := by ring

theorem gen (n ℓ : ℕ) (hn : 0 < n) (hℓ : 0 < ℓ) (h : ℤ) (hh : h ≠ 0) :
    ∃ D : ℝ, ∀ A₁ B₁ A₂ B₂ : ℤ, A₁ ≤ B₁ → A₂ ≤ B₂ →
      |(#((Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter
          (fun p : ℤ × ℤ => (n : ℤ) ∣ (ℓ : ℤ) * p.1 * p.2 - h)) : ℝ) -
        D * ((B₁ - A₁ : ℤ) : ℝ) * ((B₂ - A₂ : ℤ) : ℝ)| ≤
        16 * ((h.natAbs.divisors.card : ℝ) ^ 2 * |(h : ℝ)| * W n) *
          (1 + (((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ)) / n) := by
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : ℕ, Nat.gcd ℓ n = g₀ := ⟨_, rfl⟩
  have hg₀pos : 0 < g₀ := by rw [← hg₀]; exact Nat.gcd_pos_of_pos_right ℓ hn
  have hWn := one_le_W n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hdiv : (g₀ : ℤ) ∣ h
  swap
  · refine ⟨0, ?_⟩
    intro A₁ B₁ A₂ B₂ h₁ h₂
    have hw₁ : (0 : ℝ) ≤ ((B₁ - A₁ : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr h₁
    have hw₂ : (0 : ℝ) ≤ ((B₂ - A₂ : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr h₂
    have hempty : (Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter
          (fun p : ℤ × ℤ => (n : ℤ) ∣ (ℓ : ℤ) * p.1 * p.2 - h) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      rintro ⟨x, y⟩ _ hd
      apply hdiv
      have h1 : (g₀ : ℤ) ∣ (n : ℤ) := by rw [← hg₀]; exact_mod_cast Nat.gcd_dvd_right ℓ n
      have h2 : (g₀ : ℤ) ∣ (ℓ : ℤ) := by rw [← hg₀]; exact_mod_cast Nat.gcd_dvd_left ℓ n
      have h3 : (g₀ : ℤ) ∣ (ℓ : ℤ) * x * y - h := dvd_trans h1 hd
      have h4 : (g₀ : ℤ) ∣ (ℓ : ℤ) * x * y := Dvd.dvd.mul_right (Dvd.dvd.mul_right h2 x) y
      have h5 := dvd_sub h4 h3
      rwa [sub_sub_cancel] at h5
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul, sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by positivity)
      (abs_nonneg _)) (by linarith))) (add_nonneg zero_le_one (div_nonneg (by linarith) hn'.le))
  · obtain ⟨h', rfl⟩ := hdiv
    obtain ⟨n', rfl⟩ : g₀ ∣ n := by rw [← hg₀]; exact Nat.gcd_dvd_right ℓ n
    obtain ⟨ℓ', rfl⟩ : g₀ ∣ ℓ := by rw [← hg₀]; exact Nat.gcd_dvd_left ℓ _
    have hn'pos : 0 < n' := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hh' : h' ≠ 0 := by rintro rfl; simp at hh
    have hcop : Nat.Coprime ℓ' n' := by
      rw [Nat.gcd_mul_left] at hg₀
      exact Nat.eq_of_mul_eq_mul_left hg₀pos (by rw [hg₀, mul_one])
    obtain ⟨u, v, huv⟩ : IsCoprime (ℓ' : ℤ) (n' : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
    obtain ⟨D, hD⟩ := core' n' hn'pos (u * h')
    refine ⟨D, ?_⟩
    intro A₁ B₁ A₂ B₂ h₁ h₂
    have hw₁ : (0 : ℝ) ≤ ((B₁ - A₁ : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr h₁
    have hw₂ : (0 : ℝ) ≤ ((B₂ - A₂ : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr h₂
    have hg₀' : (g₀ : ℤ) ≠ 0 := by exact_mod_cast hg₀pos.ne'
    have hfilt : (Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter
          (fun p : ℤ × ℤ => ((g₀ * n' : ℕ) : ℤ) ∣ ((g₀ * ℓ' : ℕ) : ℤ) * p.1 * p.2 - (g₀ : ℤ) * h') =
        (Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter
          (fun p : ℤ × ℤ => (n' : ℤ) ∣ p.1 * p.2 - u * h') := by
      apply Finset.filter_congr
      rintro ⟨x, y⟩ _
      have e1 : ((g₀ * n' : ℕ) : ℤ) ∣ ((g₀ * ℓ' : ℕ) : ℤ) * x * y - (g₀ : ℤ) * h' ↔
          (n' : ℤ) ∣ (ℓ' : ℤ) * x * y - h' := by
        have e2 : ((g₀ * ℓ' : ℕ) : ℤ) * x * y - (g₀ : ℤ) * h' =
            (g₀ : ℤ) * ((ℓ' : ℤ) * x * y - h') := by push_cast; ring
        rw [e2]
        push_cast
        exact mul_dvd_mul_iff_left hg₀'
      show ((g₀ * n' : ℕ) : ℤ) ∣ ((g₀ * ℓ' : ℕ) : ℤ) * x * y - (g₀ : ℤ) * h' ↔
          (n' : ℤ) ∣ x * y - u * h'
      rw [e1]
      constructor
      · rintro ⟨c, hc⟩
        exact ⟨u * c + v * x * y, by linear_combination u * hc - (x * y) * huv⟩
      · rintro ⟨c, hc⟩
        exact ⟨ℓ' * c - v * h', by linear_combination (ℓ' : ℤ) * hc + h' * huv⟩
    rw [hfilt]
    refine (hD A₁ B₁ A₂ B₂ h₁ h₂).trans ?_
    obtain ⟨g, hgdef⟩ : ∃ g : ℕ, Int.gcd (u * h') n' = g := ⟨_, rfl⟩
    rw [hgdef]
    have hgh : (g : ℤ) ∣ h' := by
      have e3 : h' = (ℓ' : ℤ) * (u * h') + (v * h') * n' := by linear_combination (-h') * huv
      rw [e3, ← hgdef]
      exact dvd_add (Dvd.dvd.mul_left (Int.gcd_dvd_left _ _) _)
        (Dvd.dvd.mul_left (Int.gcd_dvd_right _ _) _)
    have hHpos : 0 < ((g₀ : ℤ) * h').natAbs := Int.natAbs_pos.mpr hh
    have hdvd : g₀ * g ∣ ((g₀ : ℤ) * h').natAbs := by
      rw [← Int.natCast_dvd]
      push_cast
      exact mul_dvd_mul_left _ hgh
    have hgpos : 0 < g := Nat.pos_of_ne_zero (by rintro rfl; simp at hdvd; omega)
    have hdc : (g.divisors.card : ℝ) ≤ (((g₀ : ℤ) * h').natAbs.divisors.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hHpos.ne'
        (dvd_trans (dvd_mul_left g g₀) hdvd))
    have hle : (g₀ : ℝ) * g ≤ |(((g₀ : ℤ) * h' : ℤ) : ℝ)| := by
      have := Nat.le_of_dvd hHpos hdvd
      have h2 : ((((g₀ : ℤ) * h').natAbs : ℕ) : ℝ) = |(((g₀ : ℤ) * h' : ℤ) : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [← h2]
      exact_mod_cast this
    have hW := W_mono n' (g₀ * n') (dvd_mul_left _ _) hn
    have hW1 := one_le_W n' hn'pos
    have hg₀1 : (1 : ℝ) ≤ g₀ := by exact_mod_cast hg₀pos
    have hn'r : (0 : ℝ) < n' := by exact_mod_cast hn'pos
    have key := key_scale g₀ n' (((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ)) hg₀1 hn'r
      (by linarith)
    have hcast : ((g₀ * n' : ℕ) : ℝ) = (g₀ : ℝ) * n' := by push_cast; ring
    rw [hcast]
    have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg _
    have hdg0 : (0 : ℝ) ≤ (g.divisors.card : ℝ) := Nat.cast_nonneg _
    have hpos : (0 : ℝ) ≤ 1 + (((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ)) / n' :=
      add_nonneg zero_le_one (div_nonneg (by linarith) hn'r.le)
    have hpos2 : (0 : ℝ) ≤ 1 + (((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ)) / ((g₀ : ℝ) * n') :=
      add_nonneg zero_le_one (div_nonneg (by linarith) (by positivity))
    have hsq : (g.divisors.card : ℝ) ^ 2 ≤ (((g₀ : ℤ) * h').natAbs.divisors.card : ℝ) ^ 2 :=
      pow_le_pow_left₀ hdg0 hdc 2
    calc 16 * (g.divisors.card : ℝ) ^ 2 * (g : ℝ) * W n' *
          (1 + (((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ)) / n')
        ≤ 16 * (((g₀ : ℤ) * h').natAbs.divisors.card : ℝ) ^ 2 * (g : ℝ) * W (g₀ * n') *
          ((g₀ : ℝ) * (1 + (((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ)) / ((g₀ : ℝ) * n'))) := by
          apply mul_le_mul _ key hpos (by positivity)
          apply mul_le_mul _ hW (by linarith) (by positivity)
          apply mul_le_mul_of_nonneg_right _ hg0
          linarith
      _ = 16 * ((((g₀ : ℤ) * h').natAbs.divisors.card : ℝ) ^ 2 * ((g₀ : ℝ) * g) * W (g₀ * n')) *
          (1 + (((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ)) / ((g₀ : ℝ) * n')) := by ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hpos2
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact mul_le_mul_of_nonneg_left hle (by positivity)

/-! ## `rho`: Fourier expansion and the trivial bound -/

end
end GuthMaynard.Twisted.PartB
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted
open Finset
noncomputable section
/-! ## Part B: counting on the modular hyperbola with a general residue -/

end
end GuthMaynard.Twisted
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted.PartB
open Finset
noncomputable section

end
end GuthMaynard.Twisted.PartB
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted
open Finset
noncomputable section

end
end GuthMaynard.Twisted
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted.PartB
open Finset
noncomputable section
/-! ## The box count -/
theorem sum_range_mul_periodic (n m : ℕ) (f : ℕ → ℕ) (hf : ∀ a, f (a + n) = f a) :
    ∑ a ∈ Finset.range (m * n), f a = m * ∑ a ∈ Finset.range n, f a := by
  have hf' : ∀ k a, f (k * n + a) = f a := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      rw [show (k + 1) * n + a = (k * n + a) + n by ring, hf, ih]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show (m + 1) * n = m * n + n by ring, Finset.sum_range_add, ih,
      Finset.sum_congr rfl (fun a _ => hf' m a)]
    ring

theorem card_periodic (n m : ℕ) (P : ℕ → ℕ → Prop) [∀ a b, Decidable (P a b)]
    (h1 : ∀ a b, P (a + n) b ↔ P a b) (h2 : ∀ a b, P a (b + n) ↔ P a b) :
    #((Finset.range (m * n) ×ˢ Finset.range (m * n)).filter (fun z : ℕ × ℕ => P z.1 z.2)) =
      m ^ 2 * #((Finset.range n ×ˢ Finset.range n).filter (fun z : ℕ × ℕ => P z.1 z.2)) := by
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_product, Finset.sum_product]
  dsimp only
  have hin : ∀ a, ∑ b ∈ Finset.range (m * n), (if P a b then 1 else 0) =
      m * ∑ b ∈ Finset.range n, (if P a b then 1 else 0) := fun a =>
    sum_range_mul_periodic n m (fun b => if P a b then 1 else 0)
      (fun b => if_congr (h2 a b) rfl rfl)
  rw [Finset.sum_congr rfl (fun a _ => hin a),
    sum_range_mul_periodic n m (fun a => m * ∑ b ∈ Finset.range n, (if P a b then 1 else 0))
      (fun a => by
        show m * ∑ b ∈ Finset.range n, (if P (a + n) b then 1 else 0) = _
        rw [Finset.sum_congr rfl (fun b _ => if_congr (h1 a b) rfl rfl)]),
    ← Finset.mul_sum]
  ring

theorem card_cast (a₁ b₁ a₂ b₂ : ℕ) (P : ℤ → ℤ → Prop) [∀ x y, Decidable (P x y)] :
    #((Finset.Ico (a₁ : ℤ) b₁ ×ˢ Finset.Ico (a₂ : ℤ) b₂).filter (fun p : ℤ × ℤ => P p.1 p.2)) =
    #((Finset.Ico a₁ b₁ ×ˢ Finset.Ico a₂ b₂).filter (fun p : ℕ × ℕ => P p.1 p.2)) := by
  symm
  refine Finset.card_bij' (fun p _ => ((p.1 : ℤ), (p.2 : ℤ)))
    (fun p _ => (p.1.toNat, p.2.toNat)) ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    simp only [mem_filter, mem_product, mem_Ico] at hp ⊢
    exact ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, hp.2⟩
  · rintro ⟨x, y⟩ hp
    simp only [mem_filter, mem_product, mem_Ico] at hp ⊢
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, hP⟩ := hp
    have hx : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg (by omega)
    have hy : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg (by omega)
    refine ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, ?_⟩
    rw [hx, hy]
    exact hP
  · rintro ⟨x, y⟩ _
    simp
  · rintro ⟨x, y⟩ hp
    simp only [mem_filter, mem_product, mem_Ico] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, hP⟩ := hp
    simp only [Prod.mk.injEq]
    exact ⟨Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)⟩

theorem eq_of_scaled_bound (X Y K : ℝ)
    (h : ∀ m : ℕ, 1 ≤ m → |(m : ℝ) ^ 2 * X - (m : ℝ) ^ 2 * Y| ≤ K * (1 + m)) : X = Y := by
  by_contra hne
  have hδ : 0 < |X - Y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hK : 0 ≤ K := by
    have h1 := h 1 le_rfl
    have h2 := abs_nonneg (((1 : ℕ) : ℝ) ^ 2 * X - ((1 : ℕ) : ℝ) ^ 2 * Y)
    push_cast at h1 h2
    linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * K / |X - Y| + 1)
  have hq : 0 ≤ 2 * K / |X - Y| := by positivity
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hm1' : 1 ≤ m := by exact_mod_cast hm1
  have hb := h m hm1'
  have e : (m : ℝ) ^ 2 * X - (m : ℝ) ^ 2 * Y = (m : ℝ) ^ 2 * (X - Y) := by ring
  rw [e, abs_mul, abs_of_nonneg (by positivity)] at hb
  have h2 : 2 * K < m * |X - Y| := by
    have h3 : 2 * K / |X - Y| < m := by linarith
    rwa [div_lt_iff₀ hδ] at h3
  nlinarith [mul_nonneg hK (by linarith : (0 : ℝ) ≤ (m : ℝ) - 1),
    mul_lt_mul_of_pos_left h2 (by linarith : (0 : ℝ) < (m : ℝ))]

theorem gen_nat (n ℓ : ℕ) (hn : 0 < n) (hℓ : 0 < ℓ) (h : ℤ) (hh : h ≠ 0) :
    ∃ D : ℝ, ∀ a₁ b₁ a₂ b₂ : ℕ, a₁ ≤ b₁ → a₂ ≤ b₂ →
      |(#((Finset.Ico a₁ b₁ ×ˢ Finset.Ico a₂ b₂).filter
          (fun z : ℕ × ℕ => (n : ℤ) ∣ (ℓ : ℤ) * z.1 * z.2 - h)) : ℝ) -
        D * ((b₁ : ℝ) - a₁) * ((b₂ : ℝ) - a₂)| ≤
        16 * E0 n h * (1 + (((b₁ : ℝ) - a₁) + ((b₂ : ℝ) - a₂)) / n) := by
  obtain ⟨D, hD⟩ := gen n ℓ hn hℓ h hh
  refine ⟨D, ?_⟩
  intro a₁ b₁ a₂ b₂ h₁ h₂
  have hb := hD (a₁ : ℤ) b₁ a₂ b₂ (by exact_mod_cast h₁) (by exact_mod_cast h₂)
  have hc : #((Finset.Ico (a₁ : ℤ) b₁ ×ˢ Finset.Ico (a₂ : ℤ) b₂).filter
        (fun p : ℤ × ℤ => (n : ℤ) ∣ (ℓ : ℤ) * p.1 * p.2 - h)) =
      #((Finset.Ico a₁ b₁ ×ˢ Finset.Ico a₂ b₂).filter
        (fun z : ℕ × ℕ => (n : ℤ) ∣ (ℓ : ℤ) * z.1 * z.2 - h)) :=
    card_cast a₁ b₁ a₂ b₂ (fun x y => (n : ℤ) ∣ (ℓ : ℤ) * x * y - h)
  have hE : (h.natAbs.divisors.card : ℝ) ^ 2 * |(h : ℝ)| * W n = E0 n h := by
    unfold E0 dv W
    ring
  rw [hc, hE] at hb
  push_cast at hb
  exact hb

theorem box_count : ∃ C : ℝ, 0 < C ∧ ∀ (n ℓ : ℕ) (h : ℤ) (p q : ℕ), 1 ≤ n → 1 ≤ ℓ → h ≠ 0 →
    |(#((Finset.Icc 1 p ×ˢ Finset.Icc 1 q).filter
        (fun z : ℕ × ℕ => (n : ℤ) ∣ (ℓ : ℤ) * z.1 * z.2 - h)) : ℝ) -
      (rho n ℓ h : ℝ) / (n : ℝ) ^ 2 * p * q| ≤ C * E0 n h * (1 + ((p : ℝ) + q) / n) := by
  refine ⟨16, by norm_num, ?_⟩
  intro n ℓ h p q hn hℓ hh
  obtain ⟨D, hD⟩ := gen_nat n ℓ hn hℓ h hh
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hE0 : 0 ≤ E0 n h := by
    unfold E0 dv
    have := Real.log_nonneg (by exact_mod_cast hn : (1 : ℝ) ≤ n)
    positivity
  have hDval : (rho n ℓ h : ℝ) = D * (n : ℝ) ^ 2 := by
    apply eq_of_scaled_bound _ _ (32 * E0 n h)
    intro m hm
    have hb := hD 0 (m * n) 0 (m * n) (Nat.zero_le _) (Nat.zero_le _)
    have hper : #((Finset.range (m * n) ×ˢ Finset.range (m * n)).filter
          (fun z : ℕ × ℕ => (n : ℤ) ∣ (ℓ : ℤ) * z.1 * z.2 - h)) = m ^ 2 * rho n ℓ h :=
      card_periodic n m (fun a b : ℕ => (n : ℤ) ∣ (ℓ : ℤ) * a * b - h)
        (fun a b => by
          have e : (ℓ : ℤ) * ((a + n : ℕ) : ℤ) * b - h =
              ((ℓ : ℤ) * a * b - h) + (n : ℤ) * ((ℓ : ℤ) * b) := by push_cast; ring
          rw [e]
          exact dvd_add_left (dvd_mul_right _ _))
        (fun a b => by
          have e : (ℓ : ℤ) * a * ((b + n : ℕ) : ℤ) - h =
              ((ℓ : ℤ) * a * b - h) + (n : ℤ) * ((ℓ : ℤ) * a) := by push_cast; ring
          rw [e]
          exact dvd_add_left (dvd_mul_right _ _))
    rw [Nat.Ico_zero_eq_range, hper] at hb
    push_cast at hb
    simp only [sub_zero] at hb
    have e1 : (m : ℝ) ^ 2 * (D * (n : ℝ) ^ 2) = D * ((m : ℝ) * n) * ((m : ℝ) * n) := by ring
    have e2 : ((m : ℝ) * n + (m : ℝ) * n) / n = 2 * m := by field_simp; ring
    rw [e1]
    rw [e2] at hb
    refine hb.trans ?_
    nlinarith [mul_nonneg hE0 (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hI : ∀ p : ℕ, Finset.Ico 1 (p + 1) = Finset.Icc 1 p := by
    intro p
    ext x
    simp
  have hfin := hD 1 (p + 1) 1 (q + 1) (by omega) (by omega)
  rw [hI, hI] at hfin
  push_cast at hfin
  simp only [add_sub_cancel_right] at hfin
  have hDr : (rho n ℓ h : ℝ) / (n : ℝ) ^ 2 = D := by
    rw [hDval]
    field_simp
  rw [hDr]
  exact hfin

end
end GuthMaynard.Twisted.PartB
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted
open Finset
noncomputable section
alias box_count := GuthMaynard.Twisted.PartB.box_count

/-! ## Part W: the variation of `ω_h` -/

/-! ## Part M: arithmetic sums -/

/-! ## Part G: Gaussian replacement and Poisson summation -/

/-! ## Part H: the resonant frequencies -/

/-! ## Part A: Proposition G -/

/-! ## Assembly -/
theorem abs_card_box_mul_sub_mod_le_of_ne_zero_dev :
    ∃ C : ℝ, 0 < C ∧ ∀ (n ℓ : ℕ) (h : ℤ) (p q : ℕ), 1 ≤ n → 1 ≤ ℓ → h ≠ 0 →
      |(((Finset.Icc 1 p ×ˢ Finset.Icc 1 q).filter
          (fun z : ℕ × ℕ => (n : ℤ) ∣ (ℓ : ℤ) * z.1 * z.2 - h)).card : ℝ) -
        (((Finset.range n ×ˢ Finset.range n).filter
          (fun z : ℕ × ℕ => (n : ℤ) ∣ (ℓ : ℤ) * z.1 * z.2 - h)).card : ℝ) / (n : ℝ) ^ 2 * p * q| ≤
      C * ((h.natAbs.divisors.card : ℝ) ^ 2 * |(h : ℝ)| *
          ((n.divisors.card : ℝ) * (1 + Real.log n)) ^ 3 * (n : ℝ) ^ (3 / 4 : ℝ)) *
        (1 + ((p : ℝ) + q) / n) :=
  box_count

end
end GuthMaynard.Twisted
end

section
set_option autoImplicit false
open GuthMaynard
open GuthMaynard.Twisted
open Finset
noncomputable section
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (n ℓ : ℕ) (h : ℤ) (p q : ℕ), 1 ≤ n → 1 ≤ ℓ → h ≠ 0 →
      |(((Finset.Icc 1 p ×ˢ Finset.Icc 1 q).filter
          (fun z : ℕ × ℕ => (n : ℤ) ∣ (ℓ : ℤ) * z.1 * z.2 - h)).card : ℝ) -
        (((Finset.range n ×ˢ Finset.range n).filter
          (fun z : ℕ × ℕ => (n : ℤ) ∣ (ℓ : ℤ) * z.1 * z.2 - h)).card : ℝ) / (n : ℝ) ^ 2 * p * q| ≤
      C * ((h.natAbs.divisors.card : ℝ) ^ 2 * |(h : ℝ)| *
          ((n.divisors.card : ℝ) * (1 + Real.log n)) ^ 3 * (n : ℝ) ^ (3 / 4 : ℝ)) *
        (1 + ((p : ℝ) + q) / n) := by
  exact GuthMaynard.Twisted.abs_card_box_mul_sub_mod_le_of_ne_zero_dev
end
end
