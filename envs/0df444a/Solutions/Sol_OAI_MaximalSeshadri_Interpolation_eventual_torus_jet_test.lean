-- Prove2me | solution 1 for OAI.MaximalSeshadri.Interpolation.eventual_torus_jet_test
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:23:57.535056+00:00
-- url     : https://prove2.me/submissions/9898775e-c792-4df6-b56d-28a6fb16de7f

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

set_option Elab.async false
set_option linter.all false

section
namespace OAI

section
namespace MaximalSeshadri.Interpolation

open scoped BigOperators Pointwise

theorem zero_of_moments {α K : Type*} [DecidableEq α] [Field K]
    (s : Finset α) (x c : α → K) (hx : Set.InjOn x s)
    (hm : ∀ n < s.card, ∑ a ∈ s, c a * (x a) ^ n = 0) :
    ∀ a ∈ s, c a = 0 := by
  classical
  let E : Fin s.card ≃ s := (s.equivFin).symm
  have hE : Function.Injective (fun i : Fin s.card => x (E i)) := by
    intro i j hij
    apply E.injective
    apply Subtype.ext
    exact hx (E i).property (E j).property hij
  have hsum (n : Fin s.card) :
      ∑ j : Fin s.card, c (E j) * x (E j) ^ (n : ℕ) = 0 := by
    rw [show (∑ j : Fin s.card, c (E j) * x (E j) ^ (n : ℕ)) =
        ∑ j : s, c j * x j ^ (n : ℕ) from
      E.sum_comp (fun j : s => c j * x j ^ (n : ℕ))]
    rw [show (∑ j : s, c j * x j ^ (n : ℕ)) =
        ∑ j ∈ s, c j * x j ^ (n : ℕ) from
      Finset.sum_coe_sort s (fun j => c j * x j ^ (n : ℕ))]
    exact hm n n.isLt
  have hzero := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hE hsum
  intro a ha
  have h := congrFun hzero (E.symm ⟨a, ha⟩)
  simpa using h

@[simp] theorem mem_row (s : Finset (ℤ × ℤ)) (x y : ℤ) :
    x ∈ row s y ↔ (x, y) ∈ s := by
  simp only [row, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨h, rfl⟩, rfl⟩
    exact h
  · intro h
    exact ⟨(x, y), ⟨h, rfl⟩, rfl⟩

theorem row_nonempty {s : Finset (ℤ × ℤ)} {y : ℤ} (hy : y ∈ rows s) :
    (row s y).Nonempty := by
  obtain ⟨⟨x, z⟩, h, rfl⟩ := Finset.mem_image.mp hy
  exact ⟨x, (mem_row s x z).mpr h⟩

def rowMoment (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (a : ℕ) (y : ℤ) : ℂ :=
  ∑ x ∈ row s y, c (x, y) * (x : ℂ) ^ a

def EulerJetZero (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (m : ℕ) : Prop :=
  ∀ a b : ℕ, a + b < m →
    ∑ y ∈ rows s, rowMoment s c a y * (y : ℂ) ^ b = 0

theorem row_zero_of_euler_jet (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (m : ℕ) (y : ℤ) (hy : y ∈ rows s)
    (hsize : (row s y).card + (rows s).card ≤ m + 1)
    (hjet : EulerJetZero s c m) : ∀ x ∈ row s y, c (x, y) = 0 := by
  apply zero_of_moments (row s y) (fun x : ℤ => (x : ℂ)) (fun x => c (x, y))
  · exact (Int.cast_injective).injOn
  intro a ha
  apply zero_of_moments (rows s) (fun y : ℤ => (y : ℂ)) (rowMoment s c a)
    (Int.cast_injective.injOn) _ y hy
  intro b hb
  exact hjet a b (by omega)

theorem card_sub_one_le_span (s : Finset ℤ) (hs : s.Nonempty) :
    (s.card : ℝ) - 1 ≤ (s.max' hs : ℝ) - (s.min' hs : ℝ) := by
  have hle : s.min' hs ≤ s.max' hs := s.min'_le _ (s.max'_mem hs)
  have hsub : s ⊆ Finset.Icc (s.min' hs) (s.max' hs) := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨s.min'_le x hx, s.le_max' x hx⟩
  have hc := Finset.card_le_card hsub
  have hi : (s.card : ℤ) ≤ s.max' hs + 1 - s.min' hs := by
    rw [← Int.card_Icc_of_le _ _ (by omega)]
    exact_mod_cast hc
  have hr : (s.card : ℝ) ≤ (s.max' hs : ℝ) + 1 - (s.min' hs : ℝ) := by
    exact_mod_cast hi
  linarith

def transverse (x₀ y₀ shear sign : ℝ) (p : ℝ × ℝ) : ℝ :=
  sign * (p.1 - x₀ - shear * (p.2 - y₀))

def balancedStrip (ρ h x₀ y₀ shear sign : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ transverse x₀ y₀ shear sign p ∧
    h * transverse x₀ y₀ shear sign p ≤ ρ * (p.2 - y₀) ∧
    (ρ - h) * transverse x₀ y₀ shear sign p ≤ ρ * (y₀ + ρ - p.2)}

theorem balanced_row_constraints (ρ h x₀ y₀ shear sign : ℝ)
    (hh : 0 ≤ h) (hhρ : h ≤ ρ) (hsign : sign ^ 2 = 1)
    (xs : Finset ℤ) (hxs : xs.Nonempty) (y : ℤ)
    (hs : ∀ x ∈ xs, ((x : ℝ), (y : ℝ)) ∈ balancedStrip ρ h x₀ y₀ shear sign) :
    h * ((xs.card : ℝ) - 1) ≤ ρ * ((y : ℝ) - y₀) ∧
    (ρ - h) * ((xs.card : ℝ) - 1) ≤ ρ * (y₀ + ρ - (y : ℝ)) := by
  let lo := xs.min' hxs
  let hi := xs.max' hxs
  have hlo := hs lo (xs.min'_mem hxs)
  have hhi := hs hi (xs.max'_mem hxs)
  have hw := card_sub_one_le_span xs hxs
  change (xs.card : ℝ) - 1 ≤ (hi : ℝ) - (lo : ℝ) at hw
  have hwidth : ∃ x ∈ xs, (hi : ℝ) - (lo : ℝ) ≤
      transverse x₀ y₀ shear sign ((x : ℝ), (y : ℝ)) := by
    have hc : sign = 1 ∨ sign = -1 := sq_eq_one_iff.mp hsign
    rcases hc with rfl | rfl
    · refine ⟨hi, xs.max'_mem hxs, ?_⟩
      have h := hlo.1
      dsimp [transverse] at h ⊢
      linarith
    · refine ⟨lo, xs.min'_mem hxs, ?_⟩
      have h := hhi.1
      dsimp [transverse] at h ⊢
      linarith
  obtain ⟨x, hx, hxx⟩ := hwidth
  have hp := hs x hx
  constructor
  · exact (mul_le_mul_of_nonneg_left (hw.trans hxx) hh).trans hp.2.1
  · exact (mul_le_mul_of_nonneg_left (hw.trans hxx) (sub_nonneg.mpr hhρ)).trans hp.2.2

theorem balanced_diagram_card (ρ h x₀ y₀ shear sign : ℝ)
    (hρ : 0 < ρ) (hh : 0 ≤ h) (hhρ : h ≤ ρ) (hsign : sign ^ 2 = 1)
    (s : Finset (ℤ × ℤ)) (hs : s.Nonempty)
    (hsupp : ∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ balancedStrip ρ h x₀ y₀ shear sign) :
    ∃ y ∈ rows s, ((row s y).card : ℝ) + ((rows s).card : ℝ) ≤ ρ + 2 := by
  have hrows : (rows s).Nonempty := hs.image _
  obtain ⟨y, hy, hmin⟩ := (rows s).exists_min_image (fun y => (row s y).card) hrows
  refine ⟨y, hy, ?_⟩
  let k : ℝ := (row s y).card
  have hb (z : ℤ) (hz : z ∈ rows s) :
      h * (k - 1) ≤ ρ * ((z : ℝ) - y₀) ∧
      (ρ - h) * (k - 1) ≤ ρ * (y₀ + ρ - (z : ℝ)) := by
    have hk : k ≤ ((row s z).card : ℝ) := by
      dsimp [k]
      exact_mod_cast hmin z hz
    have hc := balanced_row_constraints ρ h x₀ y₀ shear sign hh hhρ hsign
      (row s z) (row_nonempty hz) z (fun x hx => hsupp (x, z) ((mem_row s x z).mp hx))
    constructor
    · exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hk _) hh).trans hc.1
    · exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hk _) (sub_nonneg.mpr hhρ)).trans hc.2
  have hlo := (hb ((rows s).min' hrows) ((rows s).min'_mem hrows)).1
  have hhi := (hb ((rows s).max' hrows) ((rows s).max'_mem hrows)).2
  have hspan := card_sub_one_le_span (rows s) hrows
  have hprod := mul_le_mul_of_nonneg_left hspan hρ.le
  change k + ((rows s).card : ℝ) ≤ ρ + 2
  nlinarith

theorem balanced_triangle_euler_test (ρ h x₀ y₀ shear sign : ℝ)
    (hρ : 0 < ρ) (hh : 0 ≤ h) (hhρ : h ≤ ρ) (hsign : sign ^ 2 = 1)
    (s : Finset (ℤ × ℤ)) (hs : s.Nonempty)
    (hsupp : ∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ balancedStrip ρ h x₀ y₀ shear sign)
    (c : ℤ × ℤ → ℂ) (hc : ∀ p ∈ s, c p ≠ 0)
    (m : ℕ) (hm : ρ < (m : ℝ)) : ¬ EulerJetZero s c m := by
  intro hj
  obtain ⟨y, hy, hsize⟩ := balanced_diagram_card ρ h x₀ y₀ shear sign hρ hh hhρ hsign s hs hsupp
  have hint : (row s y).card + (rows s).card ≤ m + 1 := by
    have hh : (((row s y).card + (rows s).card : ℕ) : ℝ) < ((m + 2 : ℕ) : ℝ) := by
      push_cast
      linarith
    have hn : (row s y).card + (rows s).card < m + 2 := by exact_mod_cast hh
    omega
  obtain ⟨x, hx⟩ := row_nonempty hy
  exact hc (x, y) ((mem_row s x y).mp hx) (row_zero_of_euler_jet s c m y hy hint hj x hx)

theorem transverse_affine (x₀ y₀ shear sign : ℝ) (p q : ℝ × ℝ)
    (a b : ℝ) (hab : a + b = 1) :
    transverse x₀ y₀ shear sign (a • p + b • q) =
      a * transverse x₀ y₀ shear sign p + b * transverse x₀ y₀ shear sign q := by
  dsimp [transverse]
  linear_combination sign * (x₀ - shear * y₀) * hab

theorem convex_balancedStrip (ρ h x₀ y₀ shear sign : ℝ) :
    Convex ℝ (balancedStrip ρ h x₀ y₀ shear sign) := by
  intro p hp q hq a b ha hb hab
  have ht := transverse_affine x₀ y₀ shear sign p q a b hab
  refine ⟨?_, ?_, ?_⟩
  · rw [ht]
    exact add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1)
  · calc
      h * transverse x₀ y₀ shear sign (a • p + b • q) =
          a * (h * transverse x₀ y₀ shear sign p) +
          b * (h * transverse x₀ y₀ shear sign q) := by rw [ht]; ring
      _ ≤ a * (ρ * (p.2 - y₀)) + b * (ρ * (q.2 - y₀)) :=
        add_le_add (mul_le_mul_of_nonneg_left hp.2.1 ha)
          (mul_le_mul_of_nonneg_left hq.2.1 hb)
      _ = ρ * ((a • p + b • q).2 - y₀) := by
        dsimp
        linear_combination -(ρ * y₀) * hab
  · calc
      (ρ - h) * transverse x₀ y₀ shear sign (a • p + b • q) =
          a * ((ρ - h) * transverse x₀ y₀ shear sign p) +
          b * ((ρ - h) * transverse x₀ y₀ shear sign q) := by rw [ht]; ring
      _ ≤ a * (ρ * (y₀ + ρ - p.2)) + b * (ρ * (y₀ + ρ - q.2)) :=
        add_le_add (mul_le_mul_of_nonneg_left hp.2.2 ha)
          (mul_le_mul_of_nonneg_left hq.2.2 hb)
      _ = ρ * (y₀ + ρ - (a • p + b • q).2) := by
        dsimp
        linear_combination ρ * (y₀ + ρ) * hab

end MaximalSeshadri.Interpolation
end

end OAI
end

section
namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
theorem exists_odd_integer_between (lo hi : ℝ) (hlen : 2 < hi - lo) :
    ∃ i : ℤ, Odd i ∧ lo < (i : ℝ) ∧ (i : ℝ) < hi := by
  let k : ℤ := ⌊(lo + 1) / 2⌋
  refine ⟨2 * k + 1, odd_two_mul_add_one k, ?_, ?_⟩
  · have h := Int.lt_floor_add_one ((lo + 1) / 2)
    change (lo + 1) / 2 < (k : ℝ) + 1 at h
    push_cast
    linarith
  · have h := Int.floor_le ((lo + 1) / 2)
    change (k : ℝ) ≤ (lo + 1) / 2 at h
    push_cast
    linarith

theorem primitive_direction_coordinates (d H T R : ℝ)
    (hd : 0 < d) (hH : 0 < H) (hT : 1 < T)
    (hR1 : 2 * (d * H) ≤ R) (hR2 : 8 * (1 + T) / d < R) :
    ∃ (t : ℝ) (i j : ℤ), T < t ∧ 0 < i ∧ 0 < j ∧ IsCoprime i j ∧
      (i : ℝ) / d + (j : ℝ) * (d * H * t / (1 + t)) = R ∧
      (j : ℝ) * (d * H / (1 + t)) < (i : ℝ) / d := by
  let W := d * H
  have hW : 0 < W := mul_pos hd hH
  have hR : 0 < R := lt_of_lt_of_le (by positivity : 0 < 2 * W) hR1
  have htwoW : 0 < 2 * W := by positivity
  have hx : 1 ≤ R / (2 * W) := (le_div_iff₀ htwoW).mpr (by simpa using hR1)
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  let j : ℤ := 2 ^ n
  have hj : 0 < j := pow_pos (by norm_num) _
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hjlo : (j : ℝ) * (2 * W) ≤ R := by
    apply (le_div_iff₀ htwoW).mp
    simpa [j] using hnlo
  have hjhi : R < (j : ℝ) * (4 * W) := by
    have h := (div_lt_iff₀ htwoW).mp hnhi
    rw [pow_succ] at h
    have hjcast : (j : ℝ) = (2 : ℝ) ^ n := by simp [j]
    rw [← hjcast] at h
    nlinarith only [h]
  let a₀ := W * T / (1 + T)
  have hTp : 0 < 1 + T := by linarith
  have ha₀ : a₀ * (1 + T) = W * T := div_mul_cancel₀ _ hTp.ne'
  have hgap : (W - a₀) * (1 + T) = W := by nlinarith only [ha₀]
  have hR2' : 8 * (1 + T) < d * R := by
    have h := (div_lt_iff₀ hd).mp hR2
    nlinarith only [h]
  have hintlen : 2 < d * (R - (j : ℝ) * a₀) - d * (R - (j : ℝ) * W) := by
    apply (mul_lt_mul_iff_left₀ hTp).mp
    have hprod := mul_lt_mul_of_pos_left hjhi hd
    have heq :
        (d * (R - (j : ℝ) * a₀) - d * (R - (j : ℝ) * W)) * (1 + T) =
          d * (j : ℝ) * W := by
      calc
        _ = d * (j : ℝ) * ((W - a₀) * (1 + T)) := by ring
        _ = _ := by rw [hgap]
    rw [heq]
    nlinarith only [hprod, hR2']
  obtain ⟨i, hiOdd, hilo, hihi⟩ := exists_odd_integer_between
    (d * (R - (j : ℝ) * W)) (d * (R - (j : ℝ) * a₀)) hintlen
  have hiR : 0 < (i : ℝ) := by
    have hprod : 0 < d * (R - (j : ℝ) * W) :=
      mul_pos hd (by nlinarith only [hjlo, hR])
    exact hprod.trans hilo
  have hi : 0 < i := by exact_mod_cast hiR
  have hprim : IsCoprime i j := (Int.isCoprime_two_right.mpr hiOdd).pow_right
  let a := (R - (i : ℝ) / d) / (j : ℝ)
  have ha : a * (j : ℝ) = R - (i : ℝ) / d := div_mul_cancel₀ _ hjR.ne'
  have hilo' : R - (j : ℝ) * W < (i : ℝ) / d :=
    (lt_div_iff₀ hd).mpr (by nlinarith only [hilo])
  have hihi' : (i : ℝ) / d < R - (j : ℝ) * a₀ :=
    (div_lt_iff₀ hd).mpr (by nlinarith only [hihi])
  have ha₀a : a₀ < a := by
    apply (mul_lt_mul_iff_left₀ hjR).mp
    nlinarith only [hihi', ha]
  have haW : a < W := by
    apply (mul_lt_mul_iff_left₀ hjR).mp
    nlinarith only [hilo', ha]
  have ha₀pos : 0 < a₀ := div_pos (mul_pos hW (by linarith)) hTp
  have hap : 0 < a := ha₀pos.trans ha₀a
  have hWa : 0 < W - a := sub_pos.mpr haW
  let t := a / (W - a)
  have ht : T < t := by
    apply (lt_div_iff₀ hWa).mpr
    nlinarith only [ha₀a, ha₀, hTp]
  have htp : 0 < 1 + t := by linarith
  have hta : W * t / (1 + t) = a := by
    dsimp [t]
    field_simp
    nlinarith only [haW, hW]
  have htb : W / (1 + t) = W - a := by
    have haeq := (div_eq_iff htp.ne').mp hta
    apply (div_eq_iff htp.ne').mpr
    nlinarith only [haeq]
  refine ⟨t, i, j, ht, hi, hj, hprim, ?_, ?_⟩
  · change (i : ℝ) / d + (j : ℝ) * (W * t / (1 + t)) = R
    rw [hta]
    nlinarith only [ha]
  · change (j : ℝ) * (W / (1 + t)) < (i : ℝ) / d
    rw [htb]
    nlinarith only [ha, hjlo, hR]

def directionProjection (i j : ℤ) (p : ℝ × ℝ) : ℝ :=
  (i : ℝ) * p.2 - (j : ℝ) * p.1

end MaximalSeshadri.Interpolation
end

end OAI
end

section
namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
def triangleDoubleArea (p₀ p₁ p₂ : ℝ × ℝ) : ℝ :=
  |(p₁.1 - p₀.1) * (p₂.2 - p₀.2) - (p₂.1 - p₀.1) * (p₁.2 - p₀.2)|

theorem triangle_subset_balanced (p₀ p₁ p₂ : ℝ × ℝ) (ρ : ℝ)
    (hρ : 0 < ρ) (_h01 : p₀.2 ≤ p₁.2) (_h12 : p₁.2 ≤ p₂.2)
    (hrange : p₂.2 - p₀.2 = ρ)
    (harea : triangleDoubleArea p₀ p₁ p₂ = ρ ^ 2) :
    ∃ shear sign : ℝ, sign ^ 2 = 1 ∧
      convexHull ℝ {p₀, p₁, p₂} ⊆
        balancedStrip ρ (p₁.2 - p₀.2) p₀.1 p₀.2 shear sign := by
  let shear := (p₂.1 - p₀.1) / ρ
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hs : shear * ρ = p₂.1 - p₀.1 := div_mul_cancel₀ _ hρne
  obtain ⟨sign, hsign, hm⟩ : ∃ sign : ℝ, sign ^ 2 = 1 ∧
      sign * (p₁.1 - p₀.1 - shear * (p₁.2 - p₀.2)) = ρ := by
    change |(p₁.1 - p₀.1) * (p₂.2 - p₀.2) -
      (p₂.1 - p₀.1) * (p₁.2 - p₀.2)| = ρ ^ 2 at harea
    rw [hrange] at harea
    rcases (abs_eq (sq_nonneg ρ)).mp harea with h | h
    · refine ⟨1, by norm_num, ?_⟩
      apply (mul_left_inj' hρne).mp
      dsimp [shear]
      field_simp
      nlinarith [h]
    · refine ⟨-1, by norm_num, ?_⟩
      apply (mul_left_inj' hρne).mp
      dsimp [shear]
      field_simp
      nlinarith [h]
  refine ⟨shear, sign, hsign, ?_⟩
  apply convexHull_min _ (convex_balancedStrip _ _ _ _ _ _)
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with hp | hp | hp <;> subst p
  · have ht : transverse p₀.1 p₀.2 shear sign p₀ = 0 := by simp [transverse]
    change 0 ≤ transverse p₀.1 p₀.2 shear sign p₀ ∧ _
    rw [ht]
    simp only [mul_zero, sub_self, mul_zero, le_refl, true_and]
    have : p₀.2 + ρ - p₀.2 = ρ := by ring
    rw [this]
    positivity
  · change 0 ≤ sign * (p₁.1 - p₀.1 - shear * (p₁.2 - p₀.2)) ∧ _
    change 0 ≤ transverse p₀.1 p₀.2 shear sign p₁ ∧
      (p₁.2 - p₀.2) * transverse p₀.1 p₀.2 shear sign p₁ ≤ _ ∧ _
    have ht : transverse p₀.1 p₀.2 shear sign p₁ = ρ := hm
    rw [ht]
    refine ⟨hρ.le, ?_, ?_⟩ <;> nlinarith
  · have ht : transverse p₀.1 p₀.2 shear sign p₂ = 0 := by
      dsimp [transverse]
      rw [hrange, hs]
      ring
    change 0 ≤ transverse p₀.1 p₀.2 shear sign p₂ ∧ _
    rw [ht]
    refine ⟨le_refl _, ?_, ?_⟩
    · rw [hrange]
      nlinarith
    · have : p₀.2 + ρ - p₂.2 = 0 := by linarith
      rw [this]
      simp

theorem triangle_euler_test (p₀ p₁ p₂ : ℝ × ℝ) (ρ : ℝ)
    (hρ : 0 < ρ) (h01 : p₀.2 ≤ p₁.2) (h12 : p₁.2 ≤ p₂.2)
    (hrange : p₂.2 - p₀.2 = ρ)
    (harea : triangleDoubleArea p₀ p₁ p₂ = ρ ^ 2)
    (s : Finset (ℤ × ℤ)) (hs : s.Nonempty)
    (hsupp : ∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ convexHull ℝ {p₀, p₁, p₂})
    (c : ℤ × ℤ → ℂ) (hc : ∀ p ∈ s, c p ≠ 0)
    (m : ℕ) (hm : ρ < (m : ℝ)) : ¬ EulerJetZero s c m := by
  obtain ⟨shear, sign, hsign, hsub⟩ :=
    triangle_subset_balanced p₀ p₁ p₂ ρ hρ h01 h12 hrange harea
  exact balanced_triangle_euler_test ρ (p₁.2 - p₀.2) p₀.1 p₀.2 shear sign
    hρ (sub_nonneg.mpr h01) (by linarith) hsign s hs
    (fun p hp => hsub (hsupp p hp)) c hc m hm

noncomputable def fallingSequence : Polynomial.Sequence ℂ where
  elems' := descPochhammer ℂ
  degree_eq' n := by
    rw [Polynomial.degree_eq_natDegree (monic_descPochhammer ℂ n).ne_zero,
      descPochhammer_natDegree]

theorem linearMap_zero_power_of_falling (L : Polynomial ℂ →ₗ[ℂ] ℂ) (n : ℕ)
    (h : ∀ i ≤ n, L (descPochhammer ℂ i) = 0) : L (Polynomial.X ^ n) = 0 := by
  have hspan : Submodule.span ℂ (fallingSequence '' Set.Iic n) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro p ⟨i, hi, rfl⟩
    exact h i hi
  have hunit (i : ℕ) (_ : i ≤ n) : IsUnit (fallingSequence i).leadingCoeff := by
    change IsUnit (descPochhammer ℂ i).leadingCoeff
    rw [(monic_descPochhammer ℂ i).leadingCoeff]
    exact isUnit_one
  rw [fallingSequence.span_degreeLE hunit] at hspan
  apply hspan
  simp only [Polynomial.mem_degreeLE, Polynomial.degree_X_pow, le_refl]

def FallingJetZero (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (m : ℕ) : Prop :=
  ∀ a b : ℕ, a + b < m →
    ∑ y ∈ rows s, (∑ x ∈ row s y,
      c (x, y) * (descPochhammer ℂ a).eval (x : ℂ)) *
        (descPochhammer ℂ b).eval (y : ℂ) = 0

theorem fallingJetZero_eulerJetZero (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (m : ℕ) (hj : FallingJetZero s c m) : EulerJetZero s c m := by
  intro a b hab
  let L : Polynomial ℂ →ₗ[ℂ] ℂ :=
    ∑ y ∈ rows s, (y : ℂ) ^ b • polynomialMoment (row s y) (fun x => c (x, y))
  have hL (i : ℕ) (hi : i ≤ a) : L (descPochhammer ℂ i) = 0 := by
    let d : ℤ → ℂ := fun y => ∑ x ∈ row s y,
      c (x, y) * (descPochhammer ℂ i).eval (x : ℂ)
    have hM (j : ℕ) (hj' : j ≤ b) :
        polynomialMoment (rows s) d (descPochhammer ℂ j) = 0 := by
      simpa only [polynomialMoment_apply] using hj i j (by omega)
    have hpow := linearMap_zero_power_of_falling (polynomialMoment (rows s) d) b hM
    simpa [L, d, mul_comm] using hpow
  have hpow := linearMap_zero_power_of_falling L a hL
  simpa [L, rowMoment, mul_comm] using hpow

end MaximalSeshadri.Interpolation
end

end OAI
end

section
namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
theorem sum_rows {M : Type*} [AddCommMonoid M]
    (s : Finset (ℤ × ℤ)) (f : ℤ × ℤ → M) :
    ∑ y ∈ rows s, ∑ x ∈ row s y, f (x, y) = ∑ p ∈ s, f p := by
  classical
  trans ∑ y ∈ rows s, ∑ p ∈ s with p.2 = y, f p
  · apply Finset.sum_congr rfl
    intro y _
    unfold row
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro p hp
      have h := (Finset.mem_filter.mp hp).2
      exact congrArg f (Prod.ext rfl h.symm)
    · intro p hp q hq h
      apply Prod.ext h
      exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
  · exact Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem Prod.snd hp) f

theorem laurentEval_eq_sum (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (u z : ℂ) :
    laurentEval s c u z = ∑ p ∈ s, c p * u ^ p.1 * z ^ p.2 := by
  unfold laurentEval
  simp_rw [Finset.sum_mul]
  exact sum_rows s (fun p => c p * u ^ p.1 * z ^ p.2)

def MomentJetZero {α : Type*} (s : Finset α) (c x y : α → ℂ) (m : ℕ) : Prop :=
  ∀ a b : ℕ, a + b < m → ∑ p ∈ s, c p * x p ^ a * y p ^ b = 0

theorem eulerJetZero_iff_momentJetZero (s : Finset (ℤ × ℤ))
    (c : ℤ × ℤ → ℂ) (m : ℕ) :
    EulerJetZero s c m ↔ MomentJetZero s c (fun p => (p.1 : ℂ)) (fun p => (p.2 : ℂ)) m := by
  have he (a b : ℕ) :
      (∑ y ∈ rows s, rowMoment s c a y * (y : ℂ) ^ b) =
        ∑ p ∈ s, c p * (p.1 : ℂ) ^ a * (p.2 : ℂ) ^ b := by
    simp_rw [rowMoment, Finset.sum_mul]
    exact sum_rows s (fun p => c p * (p.1 : ℂ) ^ a * (p.2 : ℂ) ^ b)
  unfold EulerJetZero MomentJetZero
  simp_rw [he]

theorem contDiffAt_zpow_ne_zero (q : ℤ) (w : ℂ) (hw : w ≠ 0) (n : WithTop ℕ∞) :
    ContDiffAt ℂ n (fun u : ℂ => u ^ q) w :=
  (analyticAt_id.zpow hw).contDiffAt

theorem laurentEval_mixed_deriv (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (u z : ℂ) (hu : u ≠ 0) (hz : z ≠ 0) (a b : ℕ) :
    iteratedDeriv b (fun v : ℂ => iteratedDeriv a (fun w : ℂ => laurentEval s c w v) u) z =
      ∑ p ∈ s, c p * (descPochhammer ℂ a).eval (p.1 : ℂ) * u ^ (p.1 - (a : ℤ)) *
        (descPochhammer ℂ b).eval (p.2 : ℂ) * z ^ (p.2 - (b : ℤ)) := by
  have hi (v : ℂ) :
      iteratedDeriv a (fun w : ℂ => laurentEval s c w v) u =
        ∑ p ∈ s, c p * (descPochhammer ℂ a).eval (p.1 : ℂ) *
          u ^ (p.1 - (a : ℤ)) * v ^ p.2 := by
    simp_rw [laurentEval_eq_sum]
    rw [iteratedDeriv_fun_sum (fun p _ =>
      (contDiffAt_const.mul (contDiffAt_zpow_ne_zero p.1 u hu a)).mul contDiffAt_const)]
    apply Finset.sum_congr rfl
    intro p _
    rw [iteratedDeriv_mul_const_field, iteratedDeriv_const_mul_field,
      iteratedDeriv_eq_iterate, iter_deriv_zpow, descPochhammer_eval_eq_prod_range]
    ring
  simp_rw [hi]
  rw [iteratedDeriv_fun_sum (fun p _ =>
    contDiffAt_const.mul (contDiffAt_zpow_ne_zero p.2 z hz b))]
  apply Finset.sum_congr rfl
  intro p _
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_zpow]
  simp_rw [descPochhammer_eval_eq_prod_range]
  ring

theorem mixedJetZero_moments (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (u z : ℂ) (hu : u ≠ 0) (hz : z ≠ 0) (m : ℕ)
    (hjet : MixedJetZero (laurentEval s c) u z m) :
    MomentJetZero s (fun p => c p * u ^ p.1 * z ^ p.2)
      (fun p => (p.1 : ℂ)) (fun p => (p.2 : ℂ)) m := by
  apply (eulerJetZero_iff_momentJetZero _ _ _).mp
  apply fallingJetZero_eulerJetZero
  intro a b hab
  have h := hjet a b hab
  rw [laurentEval_mixed_deriv s c u z hu hz] at h
  have heq : (∑ p ∈ s, c p * (descPochhammer ℂ a).eval (p.1 : ℂ) *
      u ^ (p.1 - (a : ℤ)) * (descPochhammer ℂ b).eval (p.2 : ℂ) *
        z ^ (p.2 - (b : ℤ))) * (u ^ a * z ^ b) =
      ∑ p ∈ s, (c p * u ^ p.1 * z ^ p.2) *
        (descPochhammer ℂ a).eval (p.1 : ℂ) * (descPochhammer ℂ b).eval (p.2 : ℂ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [zpow_sub₀ hu, zpow_sub₀ hz, zpow_natCast, zpow_natCast]
    field_simp
  simp_rw [Finset.sum_mul]
  rw [sum_rows s (fun p => (c p * u ^ p.1 * z ^ p.2) *
    (descPochhammer ℂ a).eval (p.1 : ℂ) * (descPochhammer ℂ b).eval (p.2 : ℂ))]
  rw [← heq, h, zero_mul]

theorem MomentJetZero.polynomial {α : Type*} (s : Finset α) (c x y : α → ℂ) (m : ℕ)
    (hjet : MomentJetZero s c x y m) (P : MvPolynomial Bool ℂ) (hP : P.totalDegree < m) :
    ∑ p ∈ s, c p * MvPolynomial.eval (Bool.rec (y p) (x p)) P = 0 := by
  classical
  simp_rw [MvPolynomial.eval_eq', Fintype.prod_bool]
  change (∑ p ∈ s, c p * ∑ d ∈ P.support, P.coeff d * (x p ^ d true * y p ^ d false)) = 0
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro d hd
  have hdeg : d true + d false < m := by
    have h := MvPolynomial.le_totalDegree hd
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_bool] at h
    exact h.trans_lt hP
  calc
    (∑ p ∈ s, c p * (P.coeff d * (x p ^ d true * y p ^ d false))) =
        P.coeff d * ∑ p ∈ s, c p * x p ^ d true * y p ^ d false := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = 0 := by rw [hjet _ _ hdeg, mul_zero]

noncomputable def affinePolynomial (a b c : ℂ) : MvPolynomial Bool ℂ :=
  MvPolynomial.C a * MvPolynomial.X true +
    MvPolynomial.C b * MvPolynomial.X false + MvPolynomial.C c

theorem affinePolynomial_degree (a b c : ℂ) : (affinePolynomial a b c).totalDegree ≤ 1 := by
  unfold affinePolynomial
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · simpa using MvPolynomial.totalDegree_mul (MvPolynomial.C a) (MvPolynomial.X true)
    · simpa using MvPolynomial.totalDegree_mul (MvPolynomial.C b) (MvPolynomial.X false)
  · simp

theorem MomentJetZero.affine {α : Type*} (s : Finset α) (c x y : α → ℂ) (m : ℕ)
    (hjet : MomentJetZero s c x y m) (A B C D E F : ℂ) :
    MomentJetZero s c (fun p => A * x p + B * y p + C)
      (fun p => D * x p + E * y p + F) m := by
  intro a b hab
  have ha : ((affinePolynomial A B C) ^ a).totalDegree ≤ a :=
    (MvPolynomial.totalDegree_pow _ _).trans (by nlinarith only [affinePolynomial_degree A B C])
  have hb : ((affinePolynomial D E F) ^ b).totalDegree ≤ b :=
    (MvPolynomial.totalDegree_pow _ _).trans (by nlinarith only [affinePolynomial_degree D E F])
  have hdeg : ((affinePolynomial A B C) ^ a * (affinePolynomial D E F) ^ b).totalDegree < m :=
    (MvPolynomial.totalDegree_mul _ _).trans_lt ((add_le_add ha hb).trans_lt hab)
  have h := hjet.polynomial s c x y m _ hdeg
  simpa [affinePolynomial, mul_assoc] using h

theorem primitiveRoot_fourier_sum (r : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r) (n : ℤ) :
    ∑ l ∈ Finset.range r, ζ ^ ((l : ℤ) * n) = if (r : ℤ) ∣ n then (r : ℂ) else 0 := by
  have hp (l : ℕ) : ζ ^ ((l : ℤ) * n) = (ζ ^ n) ^ l := by
    rw [mul_comm, zpow_mul, zpow_natCast]
  simp_rw [hp]
  by_cases hn : (r : ℤ) ∣ n
  · rw [ite_eq_left hn, (hζ.zpow_eq_one_iff_dvd n).mpr hn]
    simp
  · rw [ite_eq_right hn, geom_sum_eq (mt (hζ.zpow_eq_one_iff_dvd n).mp hn)]
    have heq : (ζ ^ n) ^ r = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm n (r : ℤ), zpow_mul,
        zpow_natCast, hζ.pow_eq_one, one_zpow]
    rw [heq]
    simp

theorem root_project_moments {α : Type*} (s : Finset α) (c x y : α → ℂ)
    (height : α → ℤ) (r m : ℕ) (hr : 0 < r) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r)
    (hjet : ∀ l < r, MomentJetZero s (fun p => c p * ζ ^ ((l : ℤ) * height p)) x y m)
    (e : ℤ) : MomentJetZero (s.filter (fun p => (r : ℤ) ∣ height p - e)) c x y m := by
  classical
  have hζ0 : ζ ≠ 0 := (hζ.isUnit hr.ne').ne_zero
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  intro a b hab
  have hz : (∑ l ∈ Finset.range r, ζ ^ (-((l : ℤ) * e)) *
      ∑ p ∈ s, (c p * ζ ^ ((l : ℤ) * height p)) * x p ^ a * y p ^ b) = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    rw [hjet l (Finset.mem_range.mp hl) a b hab, mul_zero]
  have heq : (∑ l ∈ Finset.range r, ζ ^ (-((l : ℤ) * e)) *
      ∑ p ∈ s, (c p * ζ ^ ((l : ℤ) * height p)) * x p ^ a * y p ^ b) =
      (r : ℂ) * ∑ p ∈ s.filter (fun p => (r : ℤ) ∣ height p - e), c p * x p ^ a * y p ^ b := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hs (p : α) : (∑ l ∈ Finset.range r,
        ζ ^ (-((l : ℤ) * e)) * ((c p * ζ ^ ((l : ℤ) * height p)) * x p ^ a * y p ^ b)) =
        (c p * x p ^ a * y p ^ b) *
          (if (r : ℤ) ∣ height p - e then (r : ℂ) else 0) := by
      rw [← primitiveRoot_fourier_sum r ζ hζ (height p - e), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      have hp : ζ ^ (-((l : ℤ) * e)) * ζ ^ ((l : ℤ) * height p) =
          ζ ^ ((l : ℤ) * (height p - e)) := by
        rw [← zpow_add₀ hζ0]
        congr 1
        ring
      calc
        _ = (c p * x p ^ a * y p ^ b) *
            (ζ ^ (-((l : ℤ) * e)) * ζ ^ ((l : ℤ) * height p)) := by ring
        _ = _ := by rw [hp]
    simp_rw [hs]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp [mul_comm]
  rw [heq] at hz
  exact (mul_eq_zero.mp hz).resolve_left hrC

theorem MomentJetZero.image {α β : Type*} [Nonempty α] [DecidableEq β]
    (s : Finset α) (c : α → ℂ) (f : α → β) (hf : Set.InjOn f s)
    (x y : β → ℂ) (m : ℕ) (hjet : MomentJetZero s c (x ∘ f) (y ∘ f) m) :
    MomentJetZero (s.image f) (c ∘ Function.invFunOn f s) x y m := by
  classical
  intro a b hab
  rw [Finset.sum_image (fun p hp q hq he => hf hp hq he)]
  convert hjet a b hab using 1
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Function.comp_apply, hf.leftInvOn_invFunOn hp]

end MaximalSeshadri.Interpolation
end

end OAI
end

section
namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
def latticeHeight (i j : ℤ) (p : ℤ × ℤ) : ℤ := i * p.2 - j * p.1

def latticeCoord (r : ℕ) (i j a b : ℤ) (e p : ℤ × ℤ) : ℤ × ℤ :=
  (a * (p.1 - e.1) + b * (p.2 - e.2),
    (latticeHeight i j p - latticeHeight i j e) / (r : ℤ))

theorem latticeCoord_reconstruct (r : ℕ) (i j a b : ℤ) (e p : ℤ × ℤ)
    (hbez : a * i + b * j = 1)
    (hp : (r : ℤ) ∣ latticeHeight i j p - latticeHeight i j e) :
    (i * (latticeCoord r i j a b e p).1 - r * b * (latticeCoord r i j a b e p).2,
      j * (latticeCoord r i j a b e p).1 + r * a * (latticeCoord r i j a b e p).2) =
      (p.1 - e.1, p.2 - e.2) := by
  have hd := Int.mul_ediv_cancel' hp
  dsimp [latticeHeight] at hd
  apply Prod.ext
  · dsimp [latticeCoord, latticeHeight]
    linear_combination (p.1 - e.1) * hbez - b * hd
  · dsimp [latticeCoord, latticeHeight]
    linear_combination (p.2 - e.2) * hbez + a * hd

theorem latticeCoord_injOn (r : ℕ) (i j a b : ℤ) (e : ℤ × ℤ)
    (hbez : a * i + b * j = 1) :
    Set.InjOn (latticeCoord r i j a b e)
      {p | (r : ℤ) ∣ latticeHeight i j p - latticeHeight i j e} := by
  intro p hp q hq he
  have hp' := latticeCoord_reconstruct r i j a b e p hbez hp
  have hq' := latticeCoord_reconstruct r i j a b e q hbez hq
  rw [he] at hp'
  have hdiff := hp'.symm.trans hq'
  exact Prod.ext (by linarith only [congrArg Prod.fst hdiff])
    (by linarith only [congrArg Prod.snd hdiff])

noncomputable def cyclicTorusPoint (ζ : ℂ) (i j : ℤ) (l : ℕ) : ℂ × ℂ :=
  (ζ ^ (-((l : ℤ) * j)), ζ ^ ((l : ℤ) * i))

theorem cyclicTorusPoint_character (ζ : ℂ) (hζ : ζ ≠ 0) (i j : ℤ) (l : ℕ)
    (p : ℤ × ℤ) :
    (cyclicTorusPoint ζ i j l).1 ^ p.1 * (cyclicTorusPoint ζ i j l).2 ^ p.2 =
      ζ ^ ((l : ℤ) * latticeHeight i j p) := by
  dsimp [cyclicTorusPoint, latticeHeight]
  rw [← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ]
  congr 1
  ring

theorem cyclicTorusPoint_injective (ζ : ℂ) (r : ℕ) (hr : 0 < r)
    (hζ : IsPrimitiveRoot ζ r) (i j : ℤ) (hprim : IsCoprime i j) :
    Function.Injective (fun l : Fin r => cyclicTorusPoint ζ i j l) := by
  obtain ⟨a, b, hab⟩ := hprim
  intro l n he
  have hχ := congrArg (fun p : ℂ × ℂ => p.1 ^ (-b) * p.2 ^ a) he
  have hζ0 := (hζ.isUnit hr.ne').ne_zero
  simp only [cyclicTorusPoint_character ζ hζ0 i j _ (-b, a)] at hχ
  have hh : latticeHeight i j (-b, a) = 1 := by dsimp [latticeHeight]; nlinarith only [hab]
  rw [hh] at hχ
  simp only [mul_one, zpow_natCast] at hχ
  exact Fin.ext (hζ.pow_inj l.isLt n.isLt hχ)

noncomputable def latticeAffine (r : ℕ) (i j a b : ℤ) (e : ℤ × ℤ) :
    (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) where
  toFun p := ((a : ℝ) * (p.1 - e.1) + (b : ℝ) * (p.2 - e.2),
    ((i : ℝ) * (p.2 - e.2) - (j : ℝ) * (p.1 - e.1)) / r)
  linear :=
    { toFun := fun p => ((a : ℝ) * p.1 + (b : ℝ) * p.2,
        ((i : ℝ) * p.2 - (j : ℝ) * p.1) / r)
      map_add' := by intro p q; ext <;> dsimp <;> ring
      map_smul' := by intro c p; ext <;> dsimp <;> ring }
  map_vadd' := by intro p v; ext <;> dsimp <;> ring

theorem latticeCoord_cast (r : ℕ) (hr : 0 < r) (i j a b : ℤ) (e p : ℤ × ℤ)
    (hp : (r : ℤ) ∣ latticeHeight i j p - latticeHeight i j e) :
    (((latticeCoord r i j a b e p).1 : ℝ), ((latticeCoord r i j a b e p).2 : ℝ)) =
      latticeAffine r i j a b e ((p.1 : ℝ), (p.2 : ℝ)) := by
  have hrR : ((r : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  apply Prod.ext
  · simp [latticeCoord, latticeAffine]
  · dsimp [latticeCoord, latticeAffine]
    rw [Int.cast_div hp hrR]
    push_cast
    simp only [latticeHeight]
    push_cast
    ring

theorem latticeAffine_det (r : ℕ) (i j a b : ℤ) (e : ℤ × ℤ)
    (hbez : a * i + b * j = 1) (p q v : ℝ × ℝ) :
    ((latticeAffine r i j a b e q).1 - (latticeAffine r i j a b e p).1) *
        ((latticeAffine r i j a b e v).2 - (latticeAffine r i j a b e p).2) -
      ((latticeAffine r i j a b e v).1 - (latticeAffine r i j a b e p).1) *
        ((latticeAffine r i j a b e q).2 - (latticeAffine r i j a b e p).2) =
      ((q.1 - p.1) * (v.2 - p.2) - (v.1 - p.1) * (q.2 - p.2)) / r := by
  have hbR : (a : ℝ) * i + (b : ℝ) * j = 1 := by exact_mod_cast hbez
  dsimp [latticeAffine]
  linear_combination (((q.1 - p.1) * (v.2 - p.2) - (v.1 - p.1) *
    (q.2 - p.2)) / r) * hbR

theorem MomentJetZero.congr {α : Type*} (s : Finset α)
    (c c' x x' y y' : α → ℂ) (m : ℕ) (hjet : MomentJetZero s c x y m)
    (hc : ∀ p ∈ s, c' p = c p) (hx : ∀ p ∈ s, x' p = x p)
    (hy : ∀ p ∈ s, y' p = y p) : MomentJetZero s c' x' y' m := by
  intro a b hab
  convert hjet a b hab using 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [hc p hp, hx p hp, hy p hp]

theorem latticeCoord_cast_complex (r : ℕ) (hr : 0 < r) (i j a b : ℤ) (e p : ℤ × ℤ)
    (hp : (r : ℤ) ∣ latticeHeight i j p - latticeHeight i j e) :
    (((latticeCoord r i j a b e p).1 : ℂ), ((latticeCoord r i j a b e p).2 : ℂ)) =
      ((a : ℂ) * p.1 + (b : ℂ) * p.2 - ((a : ℂ) * e.1 + (b : ℂ) * e.2),
        (-(j : ℂ) / r) * p.1 + ((i : ℂ) / r) * p.2 +
          (((j : ℂ) * e.1 - (i : ℂ) * e.2) / r)) := by
  have hrC : ((r : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  apply Prod.ext
  · simp only [latticeCoord, Int.cast_add, Int.cast_mul, Int.cast_sub]
    ring
  · dsimp only [latticeCoord]
    rw [Int.cast_div hp hrC]
    simp only [latticeHeight]
    push_cast
    ring

theorem lattice_coordinate_moments (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (r m : ℕ)
    (hr : 0 < r) (i j a b : ℤ) (e : ℤ × ℤ)
    (hcos : ∀ p ∈ s, (r : ℤ) ∣ latticeHeight i j p - latticeHeight i j e)
    (hjet : MomentJetZero s c (fun p => (p.1 : ℂ)) (fun p => (p.2 : ℂ)) m) :
    MomentJetZero s c (fun p => ((latticeCoord r i j a b e p).1 : ℂ))
      (fun p => ((latticeCoord r i j a b e p).2 : ℂ)) m := by
  have h := MomentJetZero.affine s c (fun p => (p.1 : ℂ)) (fun p => (p.2 : ℂ)) m hjet
    (a : ℂ) (b : ℂ) (-((a : ℂ) * e.1 + (b : ℂ) * e.2))
    (-(j : ℂ) / r) ((i : ℂ) / r)
    (((j : ℂ) * e.1 - (i : ℂ) * e.2) / r)
  intro x y hxy
  convert h x y hxy using 1
  apply Finset.sum_congr rfl
  intro p hp
  have heq := latticeCoord_cast_complex r hr i j a b e p (hcos p hp)
  have h1 := congrArg Prod.fst heq
  have h2 := congrArg Prod.snd heq
  dsimp only at h1 h2
  dsimp only
  rw [h1, h2]
  simp only [sub_eq_add_neg]

theorem lattice_moments (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (r m : ℕ)
    (hr : 0 < r) (i j a b : ℤ) (e : ℤ × ℤ) (hbez : a * i + b * j = 1)
    (hcos : ∀ p ∈ s, (r : ℤ) ∣ latticeHeight i j p - latticeHeight i j e)
    (hjet : MomentJetZero s c (fun p => (p.1 : ℂ)) (fun p => (p.2 : ℂ)) m) :
    EulerJetZero (s.image (latticeCoord r i j a b e))
      (c ∘ Function.invFunOn (latticeCoord r i j a b e) s) m := by
  have hinj : Set.InjOn (latticeCoord r i j a b e) s :=
    (latticeCoord_injOn r i j a b e hbez).mono hcos
  have h' := lattice_coordinate_moments s c r m hr i j a b e hcos hjet
  exact (eulerJetZero_iff_momentJetZero _ _ _).mpr
    (MomentJetZero.image s c (latticeCoord r i j a b e) hinj
      (fun p => (p.1 : ℂ)) (fun p => (p.2 : ℂ)) m h')

theorem latticeAffine_snd_sub (r : ℕ) (i j a b : ℤ) (e : ℤ × ℤ)
    (p q : ℝ × ℝ) :
    (latticeAffine r i j a b e q).2 - (latticeAffine r i j a b e p).2 =
      (directionProjection i j q - directionProjection i j p) / r := by
  dsimp [latticeAffine, directionProjection]
  ring

theorem sqrt_mul_div (r : ℕ) (hr : 0 < r) (H : ℝ) (hH : 0 < H) :
    Real.sqrt ((r : ℝ) * H) / r = Real.sqrt (H / r) := by
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  rw [Real.sqrt_div (le_of_lt hH), Real.sqrt_mul hrR.le]
  have hs : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hrR
  have hs2 := Real.sq_sqrt hrR.le
  apply (div_eq_div_iff hrR.ne' hs.ne').mpr
  calc
    _ = Real.sqrt H * (Real.sqrt (r : ℝ)) ^ 2 := by ring
    _ = _ := by rw [hs2]

end MaximalSeshadri.Interpolation
end

end OAI
end

section
namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
theorem triangle_cyclic_jet_test (p₀ p₁ p₂ : ℝ × ℝ) (H : ℝ) (hH : 0 < H)
    (r : ℕ) (hr : 0 < r) (i j : ℤ) (hprim : IsCoprime i j)
    (h01 : directionProjection i j p₀ ≤ directionProjection i j p₁)
    (h12 : directionProjection i j p₁ ≤ directionProjection i j p₂)
    (hrange : directionProjection i j p₂ - directionProjection i j p₀ =
      Real.sqrt ((r : ℝ) * H))
    (harea : triangleDoubleArea p₀ p₁ p₂ = H)
    (s : Finset (ℤ × ℤ)) (hs : s.Nonempty)
    (hsupp : ∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ convexHull ℝ {p₀, p₁, p₂})
    (c : ℤ × ℤ → ℂ) (hc : ∀ p ∈ s, c p ≠ 0)
    (m : ℕ) (hm : Real.sqrt (H / r) < (m : ℝ))
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r) :
    ∃ l : Fin r, ¬ MixedJetZero (laurentEval s c)
      (cyclicTorusPoint ζ i j l).1 (cyclicTorusPoint ζ i j l).2 m := by
  classical
  by_contra! hall
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hζ0 : ζ ≠ 0 := (hζ.isUnit hr.ne').ne_zero
  have hmoment (l : ℕ) (hl : l < r) :
      MomentJetZero s (fun p => c p * ζ ^ ((l : ℤ) * latticeHeight i j p))
        (fun p => (p.1 : ℂ)) (fun p => (p.2 : ℂ)) m := by
    have h := mixedJetZero_moments s c (cyclicTorusPoint ζ i j l).1
      (cyclicTorusPoint ζ i j l).2
      (zpow_ne_zero _ hζ0) (zpow_ne_zero _ hζ0) m (hall ⟨l, hl⟩)
    apply h.congr s _ _ _ _ _ _ m
    · intro p _
      rw [mul_assoc, cyclicTorusPoint_character ζ hζ0]
    · intro _ _; rfl
    · intro _ _; rfl
  obtain ⟨e, he⟩ := hs
  let s' := s.filter (fun p => (r : ℤ) ∣ latticeHeight i j p - latticeHeight i j e)
  have hs' : s'.Nonempty := ⟨e, by simp [s', he]⟩
  have hcos : ∀ p ∈ s', (r : ℤ) ∣ latticeHeight i j p - latticeHeight i j e :=
    fun _ hp => (Finset.mem_filter.mp hp).2
  have hproject : MomentJetZero s' c (fun p => (p.1 : ℂ)) (fun p => (p.2 : ℂ)) m :=
    root_project_moments s c _ _ (latticeHeight i j) r m hr ζ hζ hmoment (latticeHeight i j e)
  obtain ⟨a, b, hbez⟩ := hprim
  let f := latticeCoord r i j a b e
  let F := latticeAffine r i j a b e
  have hinj : Set.InjOn f s' := (latticeCoord_injOn r i j a b e hbez).mono hcos
  have hjet := lattice_moments s' c r m hr i j a b e hbez hcos hproject
  have h01' : (F p₀).2 ≤ (F p₁).2 := by
    have h := div_nonneg (sub_nonneg.mpr h01) hrR.le
    rw [← latticeAffine_snd_sub r i j a b e p₀ p₁] at h
    exact sub_nonneg.mp h
  have h12' : (F p₁).2 ≤ (F p₂).2 := by
    have h := div_nonneg (sub_nonneg.mpr h12) hrR.le
    rw [← latticeAffine_snd_sub r i j a b e p₁ p₂] at h
    exact sub_nonneg.mp h
  have hrange' : (F p₂).2 - (F p₀).2 = Real.sqrt (H / r) := by
    rw [latticeAffine_snd_sub, hrange, sqrt_mul_div r hr H hH]
  have harea' : triangleDoubleArea (F p₀) (F p₁) (F p₂) = (Real.sqrt (H / r)) ^ 2 := by
    dsimp only [triangleDoubleArea, F]
    rw [latticeAffine_det r i j a b e hbez, abs_div, abs_of_pos hrR]
    change triangleDoubleArea p₀ p₁ p₂ / r = _
    rw [harea, Real.sq_sqrt (div_pos hH hrR).le]
  have hsupp' : ∀ q ∈ s'.image f, ((q.1 : ℝ), (q.2 : ℝ)) ∈
      convexHull ℝ {F p₀, F p₁, F p₂} := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    rw [latticeCoord_cast r hr i j a b e p (hcos p hp)]
    have hmem : F ((p.1 : ℝ), (p.2 : ℝ)) ∈ F '' convexHull ℝ {p₀, p₁, p₂} :=
      Set.mem_image_of_mem F (hsupp p (Finset.mem_filter.mp hp).1)
    simpa only [AffineMap.image_convexHull, Set.image_insert_eq, Set.image_singleton] using hmem
  have hc' : ∀ q ∈ s'.image f, (c ∘ Function.invFunOn f s') q ≠ 0 := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    simp only [Function.comp_apply, hinj.leftInvOn_invFunOn hp]
    exact hc p (Finset.mem_filter.mp hp).1
  exact triangle_euler_test (F p₀) (F p₁) (F p₂) (Real.sqrt (H / r))
    (Real.sqrt_pos.mpr (div_pos hH hrR)) h01' h12' hrange' harea'
    (s'.image f) (hs'.image f) hsupp' _ hc' m hm hjet

theorem scaled_compressed_triangle (d H t k : ℝ) :
    k • compressedTriangle d H t =
      convexHull ℝ {(k * (d * H * t / (1 + t)), 0),
        (-(k * (d * H / (1 + t))), 0), (0, k / d)} := by
  rw [compressedTriangle, ← convexHull_smul]
  simp only [Set.smul_set_insert, Set.smul_set_singleton, Prod.smul_mk, smul_eq_mul,
    mul_neg, mul_zero, mul_one_div]
  rw [Set.insert_comm]

theorem scaled_compressed_area (d H t k : ℝ) (hd : 0 < d) (hH : 0 < H) (ht : 0 < t) :
    triangleDoubleArea (k * (d * H * t / (1 + t)), 0)
      (-(k * (d * H / (1 + t))), 0) (0, k / d) = k ^ 2 * H := by
  have htp : 1 + t ≠ 0 := by positivity
  have heq : (-(k * (d * H / (1 + t))) - k * (d * H * t / (1 + t))) * (k / d) =
      -(k ^ 2 * H) := by
    field_simp
    ring
  dsimp [triangleDoubleArea]
  simp only [sub_zero, mul_zero, sub_self, zero_sub]
  rw [heq, abs_neg, abs_of_nonneg (mul_nonneg (sq_nonneg k) hH.le)]

theorem sqrt_scale (k x : ℝ) (hk : 0 ≤ k) :
    Real.sqrt (k ^ 2 * x) = k * Real.sqrt x := by
  rw [Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk]

theorem compressed_cyclic_jet_test (d H t : ℝ) (hd : 0 < d) (hH : 0 < H) (ht : 0 < t)
    (r : ℕ) (hr : 0 < r) (i j : ℤ) (hj : 0 < j) (hprim : IsCoprime i j)
    (hlen : (i : ℝ) / d + (j : ℝ) * (d * H * t / (1 + t)) = Real.sqrt ((r : ℝ) * H))
    (hsep : (j : ℝ) * (d * H / (1 + t)) < (i : ℝ) / d)
    (k m : ℕ) (hk : 0 < k) (hm : (k : ℝ) * Real.sqrt (H / r) < (m : ℝ))
    (s : Finset (ℤ × ℤ)) (hs : s.Nonempty)
    (hsupp : ∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ (k : ℝ) • compressedTriangle d H t)
    (c : ℤ × ℤ → ℂ) (hc : ∀ p ∈ s, c p ≠ 0) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r) :
    ∃ l : Fin r, ¬ MixedJetZero (laurentEval s c)
      (cyclicTorusPoint ζ i j l).1 (cyclicTorusPoint ζ i j l).2 m := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  let A := d * H * t / (1 + t)
  let B := d * H / (1 + t)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have h01 : directionProjection i j ((k : ℝ) * A, 0) ≤
      directionProjection i j (-((k : ℝ) * B), 0) := by
    dsimp [directionProjection]
    nlinarith only [mul_pos hjR (mul_pos hkR hA), mul_pos hjR (mul_pos hkR hB)]
  have h12 : directionProjection i j (-((k : ℝ) * B), 0) ≤
      directionProjection i j (0, (k : ℝ) / d) := by
    have h := mul_le_mul_of_nonneg_left hsep.le hkR.le
    dsimp [directionProjection]
    dsimp [B] at *
    calc
      _ = (k : ℝ) * ((j : ℝ) * (d * H / (1 + t))) := by ring
      _ ≤ (k : ℝ) * ((i : ℝ) / d) := h
      _ = _ := by ring
  have hsqrt : Real.sqrt ((r : ℝ) * ((k : ℝ) ^ 2 * H)) =
      (k : ℝ) * Real.sqrt ((r : ℝ) * H) := by
    rw [show (r : ℝ) * ((k : ℝ) ^ 2 * H) = (k : ℝ) ^ 2 * ((r : ℝ) * H) by ring,
      sqrt_scale _ _ hkR.le]
  have hrange : directionProjection i j (0, (k : ℝ) / d) -
      directionProjection i j ((k : ℝ) * A, 0) =
      Real.sqrt ((r : ℝ) * ((k : ℝ) ^ 2 * H)) := by
    rw [hsqrt, ← hlen]
    dsimp [directionProjection, A]
    ring
  have hm' : Real.sqrt ((k : ℝ) ^ 2 * H / r) < (m : ℝ) := by
    rw [mul_div_assoc, sqrt_scale _ _ hkR.le]
    exact hm
  apply triangle_cyclic_jet_test ((k : ℝ) * A, 0) (-((k : ℝ) * B), 0)
    (0, (k : ℝ) / d) ((k : ℝ) ^ 2 * H) (mul_pos (sq_pos_of_pos hkR) hH)
    r hr i j hprim h01 h12 hrange (scaled_compressed_area d H t k hd hH ht)
    s hs _ c hc m hm' ζ hζ
  intro p hp
  simpa only [scaled_compressed_triangle] using hsupp p hp

theorem eventual_torus_jet_test (d H T : ℝ) (hd : 0 < d) (hH : 0 < H) (hT : 1 < T) :
    ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      ∃ t : ℝ, T < t ∧ ∃ points : Fin r → ℂ × ℂ,
        Function.Injective points ∧ (∀ l, (points l).1 ≠ 0 ∧ (points l).2 ≠ 0) ∧
        ∀ (k m : ℕ), 0 < k → 0 < m → (k : ℝ) * Real.sqrt (H / r) < (m : ℝ) →
          ∀ (s : Finset (ℤ × ℤ)), s.Nonempty →
            (∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ (k : ℝ) • compressedTriangle d H t) →
            ∀ c : ℤ × ℤ → ℂ, (∀ p ∈ s, c p ≠ 0) →
              ∃ l : Fin r, ¬ MixedJetZero (laurentEval s c) (points l).1 (points l).2 m := by
  have hlim : Filter.Tendsto (fun r : ℕ => Real.sqrt ((r : ℝ) * H))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hH)
  have hev := (hlim.eventually (Filter.eventually_ge_atTop (2 * (d * H)))).and
    (hlim.eventually (Filter.eventually_gt_atTop (8 * (1 + T) / d)))
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max r₀ 1, by omega, ?_⟩
  intro r hr
  have hrpos : 0 < r := by omega
  obtain ⟨hR1, hR2⟩ := hr₀ r (by omega)
  obtain ⟨t, i, j, ht, _hi, hj, hprim, hlen, hsep⟩ :=
    primitive_direction_coordinates d H T (Real.sqrt ((r : ℝ) * H)) hd hH hT hR1 hR2
  let ζ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (r : ℂ))
  have hζ : IsPrimitiveRoot ζ r := Complex.isPrimitiveRoot_exp r hrpos.ne'
  have hζ0 : ζ ≠ 0 := (hζ.isUnit hrpos.ne').ne_zero
  refine ⟨t, ht, (fun l => cyclicTorusPoint ζ i j l),
    cyclicTorusPoint_injective ζ r hrpos hζ i j hprim, ?_, ?_⟩
  · intro l
    exact ⟨zpow_ne_zero _ hζ0, zpow_ne_zero _ hζ0⟩
  · intro k m hk _hm hm s hs hsupp c hc
    exact compressed_cyclic_jet_test d H t hd hH (by linarith) r hrpos i j hj hprim hlen hsep
      k m hk hm s hs hsupp c hc ζ hζ

open scoped BigOperators ContDiff
open Filter Topology

end MaximalSeshadri.Interpolation
end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Interpolation.eventual_torus_jet_test := @OAI.MaximalSeshadri.Interpolation.eventual_torus_jet_test
