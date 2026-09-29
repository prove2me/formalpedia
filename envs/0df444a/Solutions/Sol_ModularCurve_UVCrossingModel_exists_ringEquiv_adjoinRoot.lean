-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_ringEquiv_adjoinRoot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ae622fd1-af9b-5b00-870c-86d55783eb4b

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingChart
import Theorems.Thm_ModularCurve_UVCrossingModel_chartHom_X
import Theorems.Thm_ModularCurve_UVCrossingModel_chartHom_C
import Theorems.Thm_ModularCurve_UVCrossingModel_U_quadratic
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_mem_fixedSubring_eq_add_mul_U
import Theorems.Thm_ModularCurve_UVCrossingModel_range_chartHom_eq_fixedSubring
import Theorems.Thm_ModularCurve_UVCrossingModel_chartHom_injective
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_uvSwapEquiv_eq_and_mk_eq_of_mem_fixedSubring
import Theorems.Thm_MvPowerSeries_exists_rename_swap_eq_add_mul_X
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_adjoinRoot

set_option autoImplicit false

noncomputable section

namespace K1Aux

p2m_open "MvPowerSeries P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_adjoinRoot.MvPowerSeries Finsupp"

section general

variable {R : Type*} [CommRing R]

noncomputable abbrev ij (i j : ℕ) : Fin 2 →₀ ℕ := single 0 i + single 1 j

theorem ij_apply_zero (i j : ℕ) : ij i j 0 = i := by simp [ij]

theorem ij_apply_one (i j : ℕ) : ij i j 1 = j := by simp [ij]

theorem ij_eq (d : Fin 2 →₀ ℕ) : ij (d 0) (d 1) = d := by
  ext k; fin_cases k <;> simp [ij]

theorem exists_eq_ij (d : Fin 2 →₀ ℕ) : ∃ i j : ℕ, d = ij i j := ⟨d 0, d 1, (ij_eq d).symm⟩

theorem ij_sub_ij (i j a b : ℕ) : ij i j - ij a b = ij (i - a) (j - b) := by
  ext k; fin_cases k <;> simp [ij]

theorem ij_le_ij_iff (a b i j : ℕ) : ij a b ≤ ij i j ↔ a ≤ i ∧ b ≤ j := by
  constructor
  · intro h; exact ⟨by simpa [ij] using h 0, by simpa [ij] using h 1⟩
  · rintro ⟨ha, hb⟩ k; fin_cases k <;> simp [ij, ha, hb]

theorem X_zero_mul_X_one : (X 0 * X 1 : MvPowerSeries (Fin 2) R) = monomial (ij 1 1) 1 := by
  rw [X_def, X_def, monomial_mul_monomial, one_mul]

theorem coeff_X_zero_mul_X_one_mul (φ : MvPowerSeries (Fin 2) R) (i j : ℕ) :
    coeff (ij i j) (X 0 * X 1 * φ) = if 1 ≤ i ∧ 1 ≤ j then coeff (ij (i - 1) (j - 1)) φ else 0 := by
  rw [X_zero_mul_X_one, coeff_monomial_mul, ij_sub_ij, one_mul]
  simp only [ij_le_ij_iff]

end general

variable {W : Type*} [CommRing W]

noncomputable abbrev rel (W : Type*) [CommRing W] : MvPowerSeries (Fin 2) (PowerSeries W) := X 0 * X 1 - C PowerSeries.X

noncomputable def nf (F : MvPowerSeries (Fin 2) (PowerSeries W)) : MvPowerSeries (Fin 2) W :=
  fun d => ∑ m ∈ Finset.range (min (d 0) (d 1) + 1),
    PowerSeries.coeff m (coeff (ij (d 0 - m) (d 1 - m)) F)

noncomputable def quo (F : MvPowerSeries (Fin 2) (PowerSeries W)) : MvPowerSeries (Fin 2) (PowerSeries W) :=
  fun d => PowerSeries.mk fun n => -∑ m ∈ Finset.range (min (d 0) (d 1) + 1),
    PowerSeries.coeff (n + 1 + m) (coeff (ij (d 0 - m) (d 1 - m)) F)

theorem coeff_nf (F : MvPowerSeries (Fin 2) (PowerSeries W)) (i j : ℕ) :
    coeff (ij i j) (nf F) = ∑ m ∈ Finset.range (min i j + 1),
      PowerSeries.coeff m (coeff (ij (i - m) (j - m)) F) := by
  show nf F (ij i j) = _
  simp only [nf, ij_apply_zero, ij_apply_one]

theorem coeff_coeff_quo (F : MvPowerSeries (Fin 2) (PowerSeries W)) (i j n : ℕ) :
    PowerSeries.coeff n (coeff (ij i j) (quo F)) = -∑ m ∈ Finset.range (min i j + 1),
      PowerSeries.coeff (n + 1 + m) (coeff (ij (i - m) (j - m)) F) := by
  show PowerSeries.coeff n (quo F (ij i j)) = _
  simp only [quo, ij_apply_zero, ij_apply_one, PowerSeries.coeff_mk]

theorem coeff_rel_mul (G : MvPowerSeries (Fin 2) (PowerSeries W)) (i j : ℕ) :
    coeff (ij i j) (rel W * G) =
      (if 1 ≤ i ∧ 1 ≤ j then coeff (ij (i - 1) (j - 1)) G else 0) - PowerSeries.X * coeff (ij i j) G := by
  rw [sub_mul, map_sub, coeff_X_zero_mul_X_one_mul, coeff_C_mul]

theorem rel_mul_quo (F : MvPowerSeries (Fin 2) (PowerSeries W)) :
    rel W * quo F = F - map PowerSeries.C (nf F) := by
  ext d n
  obtain ⟨i, j, rfl⟩ := exists_eq_ij d
  rw [coeff_rel_mul, map_sub, map_sub, coeff_map, map_sub, coeff_nf, PowerSeries.coeff_C]
  rcases Nat.eq_zero_or_pos (min i j) with hij | hij
  ·
    have hcond : ¬(1 ≤ i ∧ 1 ≤ j) := by omega
    rw [if_neg hcond, map_zero, zero_sub, hij, zero_add]
    cases n with
    | zero =>
      rw [PowerSeries.coeff_zero_X_mul, neg_zero, if_pos rfl, Finset.sum_range_one, Nat.sub_zero, Nat.sub_zero,
        sub_self]
    | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, coeff_coeff_quo, hij, zero_add, Finset.sum_range_one,
        Nat.sub_zero, Nat.sub_zero, Nat.add_zero, neg_neg, if_neg (Nat.succ_ne_zero n), sub_zero]
  · have hcond : 1 ≤ i ∧ 1 ≤ j := by omega
    have hmin : min (i - 1) (j - 1) + 1 = min i j := by omega
    rw [if_pos hcond]
    cases n with
    | zero =>
      rw [PowerSeries.coeff_zero_X_mul, sub_zero, coeff_coeff_quo, hmin, if_pos rfl,
        Finset.sum_range_succ' (fun m => PowerSeries.coeff m (coeff (ij (i - m) (j - m)) F)),
        Nat.sub_zero, Nat.sub_zero]
      have : ∀ m : ℕ, PowerSeries.coeff (0 + 1 + m) (coeff (ij (i - 1 - m) (j - 1 - m)) F) =
          PowerSeries.coeff (m + 1) (coeff (ij (i - (m + 1)) (j - (m + 1))) F) := by
        intro m
        rw [show 0 + 1 + m = m + 1 by omega, show i - 1 - m = i - (m + 1) by omega,
          show j - 1 - m = j - (m + 1) by omega]
      rw [Finset.sum_congr rfl (fun m _ => this m)]
      ring
    | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, coeff_coeff_quo, coeff_coeff_quo, hmin,
        if_neg (Nat.succ_ne_zero n), sub_zero,
        Finset.sum_range_succ' (fun m => PowerSeries.coeff (n + 1 + m) (coeff (ij (i - m) (j - m)) F)),
        Nat.sub_zero, Nat.sub_zero, Nat.add_zero]
      have : ∀ m : ℕ, PowerSeries.coeff (n + 1 + 1 + m) (coeff (ij (i - 1 - m) (j - 1 - m)) F) =
          PowerSeries.coeff (n + 1 + (m + 1)) (coeff (ij (i - (m + 1)) (j - (m + 1))) F) := by
        intro m
        rw [show n + 1 + 1 + m = n + 1 + (m + 1) by omega, show i - 1 - m = i - (m + 1) by omega,
          show j - 1 - m = j - (m + 1) by omega]
      rw [Finset.sum_congr rfl (fun m _ => this m)]
      ring

theorem eq_zero_of_C_eq_neg_X_mul (a : W) (g : PowerSeries W) (h : PowerSeries.C a = 0 - PowerSeries.X * g) :
    a = 0 ∧ g = 0 := by
  have ha : a = 0 := by
    have := congrArg (PowerSeries.coeff 0) h
    rwa [PowerSeries.coeff_zero_C, map_sub, PowerSeries.coeff_zero_X_mul, map_zero, sub_zero] at this
  refine ⟨ha, ?_⟩
  ext n
  have := congrArg (PowerSeries.coeff (n + 1)) h
  rw [ha, map_zero, map_zero, map_sub, map_zero, PowerSeries.coeff_succ_X_mul, zero_sub,
    eq_comm, neg_eq_zero] at this
  rw [this, map_zero]

theorem eq_zero_of_map_C_eq_rel_mul (Ft : MvPowerSeries (Fin 2) W) (G : MvPowerSeries (Fin 2) (PowerSeries W))
    (h : map PowerSeries.C Ft = rel W * G) : Ft = 0 ∧ G = 0 := by
  have hc : ∀ i j, PowerSeries.C (coeff (ij i j) Ft) =
      (if 1 ≤ i ∧ 1 ≤ j then coeff (ij (i - 1) (j - 1)) G else 0) - PowerSeries.X * coeff (ij i j) G := by
    intro i j
    rw [← coeff_rel_mul, ← h, coeff_map]
  have key : ∀ k i j, min i j = k → coeff (ij i j) Ft = 0 ∧ coeff (ij i j) G = 0 := by
    intro k
    induction k with
    | zero =>
      intro i j hij
      have := hc i j
      rw [if_neg (by omega)] at this
      exact eq_zero_of_C_eq_neg_X_mul _ _ this
    | succ k ih =>
      intro i j hij
      have := hc i j
      rw [if_pos (by omega), (ih (i - 1) (j - 1) (by omega)).2] at this
      exact eq_zero_of_C_eq_neg_X_mul _ _ this
  constructor
  · ext d
    obtain ⟨i, j, rfl⟩ := exists_eq_ij d
    rw [map_zero]; exact (key _ i j rfl).1
  · ext d
    obtain ⟨i, j, rfl⟩ := exists_eq_ij d
    rw [map_zero]; exact congrArg _ (key _ i j rfl).2

theorem rel_mem_nonZeroDivisors : rel W ∈
    nonZeroDivisors (MvPowerSeries (Fin 2) (PowerSeries W)) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro G hG
  exact (eq_zero_of_map_C_eq_rel_mul 0 G (by rw [map_zero, mul_comm, hG])).2

noncomputable def toQuot : MvPowerSeries (Fin 2) W →+* MvPowerSeries (Fin 2) (PowerSeries W) ⧸ Ideal.span {rel W} :=
  (Ideal.Quotient.mk _).comp (map PowerSeries.C)

theorem toQuot_apply (F : MvPowerSeries (Fin 2) W) :
    toQuot F = Ideal.Quotient.mk (Ideal.span {rel W}) (map PowerSeries.C F) := rfl

theorem toQuot_injective : Function.Injective (toQuot (W := W)) := by
  rw [injective_iff_map_eq_zero]
  intro F hF
  rw [toQuot_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hF
  obtain ⟨G, hG⟩ := hF
  exact (eq_zero_of_map_C_eq_rel_mul F G hG).1

theorem toQuot_nf (F : MvPowerSeries (Fin 2) (PowerSeries W)) :
    toQuot (nf F) = Ideal.Quotient.mk (Ideal.span {rel W}) F := by
  rw [toQuot_apply, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  exact ⟨-quo F, by rw [mul_neg, rel_mul_quo]; ring⟩

theorem toQuot_surjective : Function.Surjective (toQuot (W := W)) := by
  intro x
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨nf F, toQuot_nf F⟩

noncomputable def equivQuot : MvPowerSeries (Fin 2) W ≃+* MvPowerSeries (Fin 2) (PowerSeries W) ⧸ Ideal.span {rel W} :=
  RingEquiv.ofBijective toQuot ⟨toQuot_injective, toQuot_surjective⟩

theorem equivQuot_apply (F : MvPowerSeries (Fin 2) W) :
    equivQuot F = Ideal.Quotient.mk (Ideal.span {rel W}) (map PowerSeries.C F) := rfl

theorem equivQuot_X (s : Fin 2) : equivQuot (X s : MvPowerSeries (Fin 2) W) = Ideal.Quotient.mk (Ideal.span {rel W}) (X s) := by
  rw [equivQuot_apply, map_X]

theorem equivQuot_C (w : W) : equivQuot (C w : MvPowerSeries (Fin 2) W) =
    Ideal.Quotient.mk (Ideal.span {rel W}) (C (PowerSeries.C w)) := by
  rw [equivQuot_apply, map_C]

theorem equivQuot_X_zero_mul_X_one : equivQuot (X 0 * X 1 : MvPowerSeries (Fin 2) W) =
    Ideal.Quotient.mk (Ideal.span {rel W}) (C PowerSeries.X) := by
  rw [map_mul, equivQuot_X, equivQuot_X, ← map_mul, Ideal.Quotient.eq]
  exact Ideal.mem_span_singleton.mpr (dvd_refl _)

theorem smul_ij (k a b : ℕ) : k • ij a b = ij (k * a) (k * b) := by
  ext t; fin_cases t <;> simp [ij]

theorem eq_zero_of_forall_mem_span_pow (x : MvPowerSeries (Fin 2) (PowerSeries W) ⧸ Ideal.span {rel W})
    (hx : ∀ B : ℕ, x ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {rel W}) (C PowerSeries.X)} ^ B) : x = 0 := by
  obtain ⟨y, rfl⟩ := equivQuot.surjective x
  rw [map_eq_zero_iff _ equivQuot.injective]
  ext d
  obtain ⟨i, j, rfl⟩ := exists_eq_ij d
  have := hx (min i j + 1)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this
  obtain ⟨r, hr⟩ := this
  obtain ⟨r', rfl⟩ := equivQuot.surjective r
  rw [← equivQuot_X_zero_mul_X_one, ← map_pow, ← map_mul] at hr
  have hy := equivQuot.injective hr
  have hnle : ¬((min i j + 1) • ij 1 1 ≤ ij i j) := fun h => by
    rw [smul_ij, ij_le_ij_iff] at h; omega
  rw [hy, map_zero, X_zero_mul_X_one, monomial_pow, one_pow, coeff_monomial_mul, if_neg hnle]

end K1Aux

namespace MvPowerSeries
p2m_export "MvPowerSeries" "X_def map_X map_C eval₂_C coeff coeff_zero_C rename_X C X coeff_monomial_mul coeff_mul_monomial monomial_pow X_pow_dvd_iff monomial_mul_monomial map monomial map_map coeff_zero coeff_zero_X_mul coeff_C_mul rename coeff_C ext eval₂_X coeff_map eval₂ exists_rename_swap_eq_add_mul_X"
p2m_open "MvPowerSeries"

open Finsupp

variable {W : Type*} [CommRing W]

private noncomputable abbrev ij' (i j : ℕ) : Fin 2 →₀ ℕ := single 0 i + single 1 j

private theorem ij'_eq (d : Fin 2 →₀ ℕ) : d = ij' (d 0) (d 1) := by
  ext k
  fin_cases k <;> simp [ij']

private theorem coeff_mul_X_zero_sub_X_one (h : MvPowerSeries (Fin 2) W) (i j : ℕ) :
    coeff (ij' i j) (h * (X 0 - X 1)) =
      (if 1 ≤ i then coeff (ij' (i - 1) j) h else 0) - (if 1 ≤ j then coeff (ij' i (j - 1)) h else 0) := by
  rw [mul_sub, map_sub]
  have hX0 : (X 0 : MvPowerSeries (Fin 2) W) = monomial (single 0 1) 1 := rfl
  have hX1 : (X 1 : MvPowerSeries (Fin 2) W) = monomial (single 1 1) 1 := rfl
  congr 1
  · rw [hX0, coeff_mul_monomial, mul_one]
    by_cases hi : 1 ≤ i
    · have heq : ij' i j - single 0 1 = ij' (i - 1) j := by
        ext k; fin_cases k <;> simp [ij']
      rw [if_pos, if_pos hi, heq]
      intro k; fin_cases k <;> simp [ij', hi]
    · rw [if_neg, if_neg hi]
      intro hle; apply hi; simpa [ij'] using hle 0
  · rw [hX1, coeff_mul_monomial, mul_one]
    by_cases hj : 1 ≤ j
    · have heq : ij' i j - single 1 1 = ij' i (j - 1) := by
        ext k; fin_cases k <;> simp [ij']
      rw [if_pos, if_pos hj, heq]
      intro k; fin_cases k <;> simp [ij', hj]
    · rw [if_neg, if_neg hj]
      intro hle; apply hj; simpa [ij'] using hle 1

theorem eq_zero_of_mul_X_zero_sub_X_one_eq_zero' (h : MvPowerSeries (Fin 2) W)
    (hh : h * (X 0 - X 1) = 0) : h = 0 := by
  have key : ∀ j i : ℕ, coeff (ij' i j) h = 0 := by
    intro j
    induction j with
    | zero =>
      intro i
      have := congrArg (coeff (ij' (i + 1) 0)) hh
      rw [coeff_mul_X_zero_sub_X_one, map_zero] at this
      simpa using this
    | succ j ih =>
      intro i
      have := congrArg (coeff (ij' (i + 1) (j + 1))) hh
      rw [coeff_mul_X_zero_sub_X_one, map_zero] at this
      simp only [le_add_iff_nonneg_left, zero_le, if_true, Nat.add_sub_cancel] at this
      rw [ih (i + 1), sub_zero] at this
      exact this
  ext d
  obtain ⟨i, j, rfl⟩ : ∃ i j, d = ij' i j := ⟨d 0, d 1, ij'_eq d⟩
  rw [map_zero]
  exact key j i

theorem eq_of_rename_swap_add_mul_X_eq' {A B A' B' : MvPowerSeries (Fin 2) W}
    (hA : rename (⇑(Equiv.swap (0 : Fin 2) 1)) A = A) (hB : rename (⇑(Equiv.swap (0 : Fin 2) 1)) B = B)
    (hA' : rename (⇑(Equiv.swap (0 : Fin 2) 1)) A' = A') (hB' : rename (⇑(Equiv.swap (0 : Fin 2) 1)) B' = B')
    (h : A + B * X 0 = A' + B' * X 0) : A = A' ∧ B = B' := by
  have h1 : (A - A') + (B - B') * X 0 = 0 := by linear_combination h
  have h2 := congrArg (rename (⇑(Equiv.swap (0 : Fin 2) 1))) h1
  rw [map_add, map_mul, map_sub, map_sub, hA, hA', hB, hB', rename_X, Equiv.swap_apply_left,
    map_zero] at h2
  have h3 : (B - B') * (X 0 - X 1) = 0 := by linear_combination h1 - h2
  have hB0 := eq_zero_of_mul_X_zero_sub_X_one_eq_zero' _ h3
  have hBB : B = B' := sub_eq_zero.mp hB0
  refine ⟨?_, hBB⟩
  rw [hBB, sub_self, zero_mul, add_zero] at h1
  exact sub_eq_zero.mp h1

end MvPowerSeries

namespace K1Aux

open Polynomial ModularCurve ModularCurve.UVCrossingModel

section P2

variable (W : Type*) [CommRing W]

noncomputable def Ft : (PowerSeries (PowerSeries W))[X] :=
  Polynomial.X ^ 2 - Polynomial.C (PowerSeries.X : PowerSeries (PowerSeries W)) * Polynomial.X +
    Polynomial.C (PowerSeries.C (PowerSeries.X : PowerSeries W))

theorem Ft_eq : Ft W = Polynomial.X ^ 2 + Polynomial.C (-(PowerSeries.X : PowerSeries (PowerSeries W))) * Polynomial.X +
    Polynomial.C (PowerSeries.C (PowerSeries.X : PowerSeries W)) := by
  rw [Ft, Polynomial.C_neg]; ring

theorem Ft_monic : (Ft W).Monic := by
  rw [Ft_eq]; monicity!

theorem Ft_natDegree [Nontrivial W] : (Ft W).natDegree = 2 := by
  rw [Ft_eq]; compute_degree!

theorem eval₂_Ft : Polynomial.eval₂ (chartHom (PowerSeries.X : PowerSeries W)) (U PowerSeries.X) (Ft W) = 0 := by
  simp only [Ft, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, chartHom_X, chartHom_C]
  exact U_quadratic _

noncomputable def φt : AdjoinRoot (Ft W) →+* UVCrossingModel (PowerSeries W) PowerSeries.X :=
  AdjoinRoot.lift (chartHom PowerSeries.X) (U PowerSeries.X) (eval₂_Ft W)

theorem φt_root : φt W (AdjoinRoot.root (Ft W)) = U PowerSeries.X := AdjoinRoot.lift_root (eval₂_Ft W)

theorem φt_of (g : PowerSeries (PowerSeries W)) : φt W (AdjoinRoot.of (Ft W) g) = chartHom PowerSeries.X g :=
  AdjoinRoot.lift_of (eval₂_Ft W)

theorem hreg_t : ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (PowerSeries W)) * MvPowerSeries.X 1 -
    MvPowerSeries.C PowerSeries.X) ∈ nonZeroDivisors (MvPowerSeries (Fin 2) (PowerSeries W)) :=
  rel_mem_nonZeroDivisors

theorem range_chartHom_t : (chartHom (PowerSeries.X : PowerSeries W)).range = fixedSubring PowerSeries.X :=
  range_chartHom_eq_fixedSubring (hreg_t W) eq_zero_of_forall_mem_span_pow

theorem chartHom_t_injective : Function.Injective (chartHom (PowerSeries.X : PowerSeries W)) := by
  refine chartHom_injective ?_ ?_
  · rw [mem_nonZeroDivisors_iff_right]
    intro g hg
    ext n
    have := congrArg (PowerSeries.coeff (n + 1)) hg
    rwa [mul_comm, PowerSeries.coeff_succ_X_mul, map_zero] at this
  · intro x hx
    ext m
    rw [map_zero]
    exact PowerSeries.X_pow_dvd_iff.mp (hx (m + 1)) m (Nat.lt_succ_self m)

theorem φt_surjective : Function.Surjective (φt W) := by
  intro x
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_mem_fixedSubring_eq_add_mul_U (PowerSeries.X : PowerSeries W) x
  rw [← range_chartHom_t, RingHom.mem_range] at ha hb
  obtain ⟨ga, rfl⟩ := ha
  obtain ⟨gb, rfl⟩ := hb
  exact ⟨AdjoinRoot.of (Ft W) ga + AdjoinRoot.of (Ft W) gb * AdjoinRoot.root (Ft W), by
    rw [map_add, map_mul, φt_of, φt_of, φt_root]⟩

theorem chart_uniq (ga gb : PowerSeries (PowerSeries W))
    (h : chartHom PowerSeries.X ga + chartHom PowerSeries.X gb * U PowerSeries.X = 0) : ga = 0 ∧ gb = 0 := by
  have ha : chartHom PowerSeries.X ga ∈ fixedSubring (PowerSeries.X : PowerSeries W) :=
    range_chartHom_t W ▸ ⟨ga, rfl⟩
  have hb : chartHom PowerSeries.X gb ∈ fixedSubring (PowerSeries.X : PowerSeries W) :=
    range_chartHom_t W ▸ ⟨gb, rfl⟩
  obtain ⟨A, hA, hAe⟩ := exists_uvSwapEquiv_eq_and_mk_eq_of_mem_fixedSubring (hreg_t W) ha
  obtain ⟨B, hB, hBe⟩ := exists_uvSwapEquiv_eq_and_mk_eq_of_mem_fixedSubring (hreg_t W) hb
  have hmem : A + B * MvPowerSeries.X 0 ∈ uvCrossingIdeal (PowerSeries W) PowerSeries.X := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change mk PowerSeries.X (A + B * MvPowerSeries.X 0) = 0
    rw [map_add, map_mul, hAe, hBe]
    exact h
  change A + B * MvPowerSeries.X 0 ∈ Ideal.span {rel W} at hmem
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨H, hH⟩ := hmem
  obtain ⟨P, Q, hP, hQ, rfl⟩ := MvPowerSeries.exists_rename_swap_eq_add_mul_X H
  have hq : MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) (rel W) = rel W := uvSwapEquiv_crossing PowerSeries.X
  have hA' : MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) A = A := hA
  have hB' : MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) B = B := hB
  have hqP : MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) (rel W * P) = rel W * P := by
    rw [map_mul, hq, hP]
  have hqQ : MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) (rel W * Q) = rel W * Q := by
    rw [map_mul, hq, hQ]
  obtain ⟨hAq, hBq⟩ := MvPowerSeries.eq_of_rename_swap_add_mul_X_eq' hA' hB' hqP hqQ
    (by rw [hH]; ring)
  have hA0 : chartHom PowerSeries.X ga = 0 := by
    rw [← hAe, hAq]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  have hB0 : chartHom PowerSeries.X gb = 0 := by
    rw [← hBe, hBq]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  exact ⟨chartHom_t_injective W (by rw [hA0, map_zero]), chartHom_t_injective W (by rw [hB0, map_zero])⟩

theorem φt_injective : Function.Injective (φt W) := by
  rcases subsingleton_or_nontrivial W with hW | hW
  · intro a b _
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective b
    rw [Subsingleton.elim p q]
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  have hpmod : AdjoinRoot.mk (Ft W) p = AdjoinRoot.mk (Ft W) (p %ₘ Ft W) := by
    rw [AdjoinRoot.mk_eq_mk]
    refine ⟨p /ₘ Ft W, ?_⟩
    have := Polynomial.modByMonic_add_div p (Ft W)
    linear_combination -this
  have hf1 : Ft W ≠ 1 := by
    intro h1
    have := Ft_natDegree W
    rw [h1, Polynomial.natDegree_one] at this
    exact absurd this (by norm_num)
  have hdeg : (p %ₘ Ft W).natDegree ≤ 1 := by
    have := Polynomial.natDegree_modByMonic_lt p (Ft_monic W) hf1
    rw [Ft_natDegree] at this
    omega
  have hrexp : p %ₘ Ft W = Polynomial.C ((p %ₘ Ft W).coeff 1) * Polynomial.X + Polynomial.C ((p %ₘ Ft W).coeff 0) :=
    Polynomial.eq_X_add_C_of_natDegree_le_one hdeg
  rw [hpmod] at hz ⊢
  have hz' : chartHom PowerSeries.X ((p %ₘ Ft W).coeff 0) +
      chartHom PowerSeries.X ((p %ₘ Ft W).coeff 1) * U PowerSeries.X = 0 := by
    rw [hrexp, map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_add, map_mul,
      φt_of, φt_of, φt_root] at hz
    linear_combination hz
  obtain ⟨h0, h1⟩ := chart_uniq W _ _ hz'
  rw [hrexp, h0, h1]
  simp

noncomputable def et : UVCrossingModel (PowerSeries W) PowerSeries.X ≃+* AdjoinRoot (Ft W) :=
  (RingEquiv.ofBijective (φt W) ⟨φt_injective W, φt_surjective W⟩).symm

theorem et_U : et W (U PowerSeries.X) = AdjoinRoot.root (Ft W) := by
  rw [et, RingEquiv.symm_apply_eq]; exact (φt_root W).symm

theorem et_chartHom (g : PowerSeries (PowerSeries W)) : et W (chartHom PowerSeries.X g) = AdjoinRoot.of (Ft W) g := by
  rw [et, RingEquiv.symm_apply_eq]; exact (φt_of W g).symm

noncomputable def E : MvPowerSeries (Fin 2) W ≃+* AdjoinRoot (Ft W) :=
  (equivQuot (W := W)).trans (et W)

theorem E_apply (F : MvPowerSeries (Fin 2) W) : E W F = et W (equivQuot F) := rfl

theorem E_X_zero : E W (MvPowerSeries.X 0) = AdjoinRoot.root (Ft W) := by
  rw [E_apply, equivQuot_X]
  exact et_U W

theorem E_S : E W (MvPowerSeries.X 0 + MvPowerSeries.X 1) = AdjoinRoot.of (Ft W) PowerSeries.X := by
  rw [E_apply, map_add, equivQuot_X, equivQuot_X, ← et_chartHom, chartHom_X]
  rfl

theorem E_C (w : W) : E W (MvPowerSeries.C w) = AdjoinRoot.of (Ft W) (PowerSeries.C (PowerSeries.C w)) := by
  rw [E_apply, equivQuot_C, ← et_chartHom, chartHom_C]
  rfl

theorem E_uv : E W (MvPowerSeries.X 0 * MvPowerSeries.X 1) = AdjoinRoot.of (Ft W) (PowerSeries.C PowerSeries.X) := by
  rw [E_apply, equivQuot_X_zero_mul_X_one, ← et_chartHom, chartHom_C]
  rfl

end P2

section eps

variable {R : Type*} [CommRing R]

theorem ker_map_mk_span (a : R) :
    RingHom.ker (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {a}))) = Ideal.span {PowerSeries.C a} := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hf
    have hc : ∀ n, a ∣ PowerSeries.coeff n f := fun n => by
      have := congrArg (PowerSeries.coeff n) hf
      rwa [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
    choose b hb using hc
    exact ⟨PowerSeries.mk b, by ext n; rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hb]⟩
  · rintro ⟨g, rfl⟩
    rw [map_mul, PowerSeries.map_C, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a),
      map_zero, zero_mul]

end eps

section P3

variable (W : Type*) [CommRing W] (c : W)

noncomputable abbrev Ic : Ideal (PowerSeries W) := Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C c}

noncomputable abbrev Jc : Ideal (PowerSeries (PowerSeries W)) :=
  Ideal.span {PowerSeries.C ((PowerSeries.X : PowerSeries W) - PowerSeries.C c)}

noncomputable def ftarget : (PowerSeries (PowerSeries W ⧸ Ic W c))[X] :=
  Polynomial.X ^ 2 - Polynomial.C (PowerSeries.X : PowerSeries (PowerSeries W ⧸ Ic W c)) * Polynomial.X +
    Polynomial.C (PowerSeries.C (Ideal.Quotient.mk (Ic W c) (PowerSeries.C c)))

theorem map_Jc : Ideal.map (AdjoinRoot.of (Ft W)) (Jc W c) = Ideal.map (E W) (uvCrossingIdeal W c) := by
  rw [Ideal.map_span, Set.image_singleton, show uvCrossingIdeal W c = Ideal.span {_} from rfl,
    Ideal.map_span, Set.image_singleton, map_sub (E W), E_uv, E_C, map_sub, map_sub]

noncomputable def θc : PowerSeries (PowerSeries W) →+* PowerSeries (PowerSeries W ⧸ Ic W c) :=
  PowerSeries.map (Ideal.Quotient.mk (Ic W c))

theorem θc_surjective : Function.Surjective (θc W c) :=
  PowerSeries.map_surjective _ Ideal.Quotient.mk_surjective

theorem θc_X : θc W c PowerSeries.X = PowerSeries.X := PowerSeries.map_X _

theorem θc_C (g : PowerSeries W) : θc W c (PowerSeries.C g) = PowerSeries.C (Ideal.Quotient.mk (Ic W c) g) :=
  PowerSeries.map_C _ _

theorem ker_θc : RingHom.ker (θc W c) = Jc W c := ker_map_mk_span _

theorem mk_Ic_X : Ideal.Quotient.mk (Ic W c) PowerSeries.X = Ideal.Quotient.mk (Ic W c) (PowerSeries.C c) := by
  rw [Ideal.Quotient.eq]
  exact Ideal.subset_span rfl

theorem map_Ft_θc : (Ft W).map (θc W c) = ftarget W c := by
  rw [Ft, ftarget]
  simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, θc_X, θc_C, mk_Ic_X]

theorem eval₂_ftarget : (Ft W).eval₂ ((AdjoinRoot.of (ftarget W c)).comp (θc W c)) (AdjoinRoot.root (ftarget W c)) = 0 := by
  rw [← Polynomial.eval₂_map, map_Ft_θc]
  exact AdjoinRoot.eval₂_root _

noncomputable def Ψ : AdjoinRoot (Ft W) →+* AdjoinRoot (ftarget W c) :=
  AdjoinRoot.lift ((AdjoinRoot.of (ftarget W c)).comp (θc W c)) (AdjoinRoot.root (ftarget W c)) (eval₂_ftarget W c)

theorem Ψ_root : Ψ W c (AdjoinRoot.root (Ft W)) = AdjoinRoot.root (ftarget W c) := AdjoinRoot.lift_root _

theorem Ψ_of (g : PowerSeries (PowerSeries W)) : Ψ W c (AdjoinRoot.of (Ft W) g) = AdjoinRoot.of (ftarget W c) (θc W c g) :=
  AdjoinRoot.lift_of _

theorem Ψ_comp_mk : (Ψ W c).comp (AdjoinRoot.mk (Ft W)) = (AdjoinRoot.mk (ftarget W c)).comp (Polynomial.mapRingHom (θc W c)) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · rw [RingHom.comp_apply, RingHom.comp_apply, AdjoinRoot.mk_C, Ψ_of, Polynomial.coe_mapRingHom,
      Polynomial.map_C, AdjoinRoot.mk_C]
  · rw [RingHom.comp_apply, RingHom.comp_apply, AdjoinRoot.mk_X, Ψ_root, Polynomial.coe_mapRingHom,
      Polynomial.map_X, AdjoinRoot.mk_X]

theorem Ψ_mk (p : (PowerSeries (PowerSeries W))[X]) :
    Ψ W c (AdjoinRoot.mk (Ft W) p) = AdjoinRoot.mk (ftarget W c) (p.map (θc W c)) :=
  RingHom.congr_fun (Ψ_comp_mk W c) p

theorem Ψ_surjective : Function.Surjective (Ψ W c) := by
  intro y
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
  obtain ⟨p, rfl⟩ := Polynomial.map_surjective (θc W c) (θc_surjective W c) q
  exact ⟨AdjoinRoot.mk _ p, Ψ_mk W c p⟩

theorem mem_of_Ψ_eq_zero (x : AdjoinRoot (Ft W)) (hx : Ψ W c x = 0) :
    x ∈ Ideal.map (AdjoinRoot.of (Ft W)) (Jc W c) := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [Ψ_mk, AdjoinRoot.mk_eq_zero] at hx
  obtain ⟨q', hq'⟩ := hx
  obtain ⟨q, rfl⟩ := Polynomial.map_surjective (θc W c) (θc_surjective W c) q'
  have hmem : p - Ft W * q ∈ Ideal.map (Polynomial.C) (Jc W c) := by
    rw [Ideal.mem_map_C_iff]
    intro n
    have h0 : (p - Ft W * q).map (θc W c) = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_mul, map_Ft_θc, hq', sub_self]
    have hn := congrArg (fun r => Polynomial.coeff r n) h0
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hn
    rw [← ker_θc, RingHom.mem_ker]
    exact hn
  have hp : AdjoinRoot.mk (Ft W) p = AdjoinRoot.mk (Ft W) (p - Ft W * q) := by
    rw [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul, sub_zero]
  rw [hp, show AdjoinRoot.of (Ft W) = (AdjoinRoot.mk (Ft W)).comp Polynomial.C from rfl, ← Ideal.map_map]
  exact Ideal.mem_map_of_mem _ hmem

noncomputable def Λ₀ : MvPowerSeries (Fin 2) W →+* AdjoinRoot (ftarget W c) :=
  (Ψ W c).comp (E W).toRingHom

theorem Λ₀_apply (F : MvPowerSeries (Fin 2) W) : Λ₀ W c F = Ψ W c (E W F) := rfl

theorem Λ₀_rel : Λ₀ W c (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C c) = 0 := by
  have h0 : Ideal.Quotient.mk (Ic W c) ((PowerSeries.X : PowerSeries W) - PowerSeries.C c) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rw [Λ₀_apply, map_sub, E_uv, E_C, ← map_sub, ← map_sub, Ψ_of, θc_C, h0, map_zero, map_zero]

noncomputable def Λ : UVCrossingModel W c →+* AdjoinRoot (ftarget W c) :=
  Ideal.Quotient.lift (uvCrossingIdeal W c) (Λ₀ W c) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, Λ₀_rel, mul_zero])

theorem Λ_mk (F : MvPowerSeries (Fin 2) W) : Λ W c (Ideal.Quotient.mk _ F) = Ψ W c (E W F) := rfl

theorem Λ_surjective : Function.Surjective (Λ W c) := by
  intro y
  obtain ⟨x, rfl⟩ := Ψ_surjective W c y
  obtain ⟨F, rfl⟩ := (E W).surjective x
  exact ⟨Ideal.Quotient.mk _ F, rfl⟩

theorem Λ_injective : Function.Injective (Λ W c) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Λ_mk] at hx
  have h1 := mem_of_Ψ_eq_zero W c _ hx
  rw [map_Jc, Ideal.mem_map_iff_of_surjective (E W) (E W).surjective] at h1
  obtain ⟨G, hG, hGF⟩ := h1
  rw [← (E W).injective hGF]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hG

noncomputable def efinal : UVCrossingModel W c ≃+* AdjoinRoot (ftarget W c) :=
  RingEquiv.ofBijective (Λ W c) ⟨Λ_injective W c, Λ_surjective W c⟩

theorem efinal_mk (F : MvPowerSeries (Fin 2) W) :
    efinal W c (Ideal.Quotient.mk _ F) = Ψ W c (E W F) := rfl

theorem efinal_U : efinal W c (U c) = AdjoinRoot.root (ftarget W c) := by
  show efinal W c (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) = _
  rw [efinal_mk, E_X_zero, Ψ_root]

theorem efinal_S : efinal W c (S c) = AdjoinRoot.of (ftarget W c) PowerSeries.X := by
  show efinal W c (Ideal.Quotient.mk _ (MvPowerSeries.X 0) + Ideal.Quotient.mk _ (MvPowerSeries.X 1)) = _
  rw [← map_add, efinal_mk, E_S, Ψ_of, θc_X]

theorem efinal_const (w : W) : efinal W c (const c w) =
    AdjoinRoot.of (ftarget W c) (PowerSeries.C (Ideal.Quotient.mk (Ic W c) (PowerSeries.C w))) := by
  show efinal W c (Ideal.Quotient.mk _ (MvPowerSeries.C w)) = _
  rw [efinal_mk, E_C, Ψ_of, θc_C]

end P3

end K1Aux

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (c : W) :
    ∃ e : UVCrossingModel W c ≃+*
        AdjoinRoot (Polynomial.X ^ 2 -
          Polynomial.C (PowerSeries.X : PowerSeries (PowerSeries W ⧸
            Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C c})) * Polynomial.X +
          Polynomial.C (PowerSeries.C (Ideal.Quotient.mk
            (Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C c}) (PowerSeries.C c)))),
      e (U c) = AdjoinRoot.root _ ∧
      e (S c) = AdjoinRoot.of _ PowerSeries.X ∧
      ∀ w : W, e (const c w) = AdjoinRoot.of _ (PowerSeries.C (Ideal.Quotient.mk
            (Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C c}) (PowerSeries.C w))) :=
  ⟨K1Aux.efinal W c, K1Aux.efinal_U W c, K1Aux.efinal_S W c, K1Aux.efinal_const W c⟩

end

end S_ModularCurve_UVCrossingModel_exists_ringEquiv_adjoinRoot
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_adjoinRoot (solution)
