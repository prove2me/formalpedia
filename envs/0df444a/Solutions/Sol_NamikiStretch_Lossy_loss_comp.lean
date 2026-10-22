-- Prove2me | solution 1 for NamikiStretch.Lossy.loss_comp
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T20:09:08.891609+00:00
-- url     : https://prove2.me/submissions/4c1c8d81-e2ca-49e8-9396-6c6b553db99f

import Mathlib
import Definitions.Def_NamikiStretch_Lossy_Protocol

open QAlgorithms.Papers.Independent.Dependency50.P39
open QAlgorithms.Papers.Independent.Frontier30.P21
open Finset

noncomputable def lcoefX (e : ℝ) (m n l : ℕ) : ℝ :=
  Real.sqrt (Nat.choose (m + l) l : ℝ) * Real.sqrt (Nat.choose (n + l) l : ℝ) *
    Real.sqrt e ^ m * Real.sqrt e ^ n * (1 - e) ^ l

theorem termX_eq (e : ℝ) (ρ : ℕ → ℕ → ℂ) (m n l : ℕ) :
    vacuumLossTerm e ρ m n l = (lcoefX e m n l : ℂ) * ρ (m + l) (n + l) := rfl

theorem lcoefX_nonneg {e : ℝ} (he1 : e ≤ 1) (m n l : ℕ) : 0 ≤ lcoefX e m n l := by
  unfold lcoefX
  have : 0 ≤ (1 - e) ^ l := pow_nonneg (by linarith) _
  positivity

theorem lcoefX_summable {e : ℝ} (he0 : 0 < e) (he1 : e < 1) (m n : ℕ) :
    Summable (lcoefX e m n) := by
  have hr : ‖(1 - e)‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
  have h1 := summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) m hr
  have h2 := summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) n hr
  refine Summable.of_nonneg_of_le (fun l => lcoefX_nonneg he1.le m n l) (fun l => ?_) (h1.add h2)
  have hc1 : ((m + l).choose l : ℝ) = ((l + m).choose m : ℝ) := by
    rw [add_comm m l, Nat.choose_symm_add]
  have hc2 : ((n + l).choose l : ℝ) = ((l + n).choose n : ℝ) := by
    rw [add_comm n l, Nat.choose_symm_add]
  have hs : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → Real.sqrt a * Real.sqrt b ≤ a + b := by
    intro a b ha hb
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb,
      Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  have hse : Real.sqrt e ≤ 1 := Real.sqrt_le_one.mpr he1.le
  have hp : Real.sqrt e ^ m * Real.sqrt e ^ n ≤ 1 :=
    mul_le_one₀ (pow_le_one₀ (Real.sqrt_nonneg _) hse) (by positivity)
      (pow_le_one₀ (Real.sqrt_nonneg _) hse)
  have hq : 0 ≤ (1 - e) ^ l := pow_nonneg (by linarith) _
  calc lcoefX e m n l
      = (Real.sqrt ((m + l).choose l : ℝ) * Real.sqrt ((n + l).choose l : ℝ)) *
          (Real.sqrt e ^ m * Real.sqrt e ^ n) * (1 - e) ^ l := by unfold lcoefX; ring
    _ ≤ (((m + l).choose l : ℝ) + ((n + l).choose l : ℝ)) * 1 * (1 - e) ^ l := by
        apply mul_le_mul_of_nonneg_right _ hq
        exact mul_le_mul (hs _ _ (by positivity) (by positivity)) hp (by positivity) (by positivity)
    _ = _ := by rw [hc1, hc2]; ring

theorem chooseX_id (m l l' : ℕ) :
    ((m + l).choose l : ℝ) * ((m + l + l').choose l' : ℝ) =
      ((m + (l + l')).choose (l + l') : ℝ) * ((l + l').choose l : ℝ) := by
  have h := Nat.choose_mul (n := m + l + l') (k := m + l) (s := m) (by omega)
  have e1 : (m + l + l').choose (m + l) = (m + l + l').choose l' := Nat.choose_symm_add
  have e2 : (m + l).choose m = (m + l).choose l := Nat.choose_symm_add
  have e3 : (m + l + l').choose m = (m + (l + l')).choose (l + l') := by
    rw [add_assoc]; exact Nat.choose_symm_add
  have e4 : m + l + l' - m = l + l' := by omega
  have e5 : m + l - m = l := by omega
  rw [e1, e2, e3, e4, e5] at h
  rw [mul_comm]
  exact_mod_cast h

theorem termX_id {η η' : ℝ} (hη'0 : 0 ≤ η') (m n l l' : ℕ) :
    lcoefX η m n l * lcoefX η' (m + l) (n + l) l' =
      (Real.sqrt ((m + (l + l')).choose (l + l') : ℝ) *
        Real.sqrt ((n + (l + l')).choose (l + l') : ℝ) *
        (Real.sqrt η * Real.sqrt η') ^ m * (Real.sqrt η * Real.sqrt η') ^ n) *
      (((l + l').choose l : ℝ) * ((1 - η) * η') ^ l * (1 - η') ^ l') := by
  have A : Real.sqrt ((m + l).choose l : ℝ) * Real.sqrt ((m + l + l').choose l' : ℝ) =
      Real.sqrt ((m + (l + l')).choose (l + l') : ℝ) * Real.sqrt ((l + l').choose l : ℝ) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity), chooseX_id]
  have B : Real.sqrt ((n + l).choose l : ℝ) * Real.sqrt ((n + l + l').choose l' : ℝ) =
      Real.sqrt ((n + (l + l')).choose (l + l') : ℝ) * Real.sqrt ((l + l').choose l : ℝ) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity), chooseX_id]
  have Cc : Real.sqrt ((l + l').choose l : ℝ) * Real.sqrt ((l + l').choose l : ℝ) =
      ((l + l').choose l : ℝ) := Real.mul_self_sqrt (by positivity)
  have D : Real.sqrt η' ^ l * Real.sqrt η' ^ l = η' ^ l := by
    rw [← mul_pow, Real.mul_self_sqrt hη'0]
  have : lcoefX η m n l * lcoefX η' (m + l) (n + l) l' =
      (Real.sqrt ((m + l).choose l : ℝ) * Real.sqrt ((m + l + l').choose l' : ℝ)) *
      (Real.sqrt ((n + l).choose l : ℝ) * Real.sqrt ((n + l + l').choose l' : ℝ)) *
      (Real.sqrt η ^ m * Real.sqrt η ^ n) * (1 - η) ^ l *
      (Real.sqrt η' ^ m * Real.sqrt η' ^ n) * (Real.sqrt η' ^ l * Real.sqrt η' ^ l) *
      (1 - η') ^ l' := by
    unfold lcoefX; ring
  rw [this, A, B, D]
  generalize Real.sqrt ((l + l').choose l : ℝ) = q at Cc ⊢
  rw [← Cc, mul_pow (1 - η)]
  ring

theorem coefX_id {η η' : ℝ} (hη0 : 0 ≤ η) (hη'0 : 0 ≤ η') (m n L : ℕ) :
    ∑ x ∈ antidiagonal L, lcoefX η m n x.1 * lcoefX η' (m + x.1) (n + x.1) x.2 =
      lcoefX (η * η') m n L := by
  have hsum : ∀ x ∈ antidiagonal L, lcoefX η m n x.1 * lcoefX η' (m + x.1) (n + x.1) x.2 =
      (Real.sqrt ((m + L).choose L : ℝ) * Real.sqrt ((n + L).choose L : ℝ) *
        (Real.sqrt η * Real.sqrt η') ^ m * (Real.sqrt η * Real.sqrt η') ^ n) *
      ((L.choose x.1 : ℝ) * ((1 - η) * η') ^ x.1 * (1 - η') ^ x.2) := by
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [termX_id hη'0, hx]
  rw [sum_congr rfl hsum, ← mul_sum]
  have hbin : ∑ x ∈ antidiagonal L, (L.choose x.1 : ℝ) * ((1 - η) * η') ^ x.1 * (1 - η') ^ x.2 =
      (1 - η * η') ^ L := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      show (1 - η * η') = (1 - η) * η' + (1 - η') by ring, add_pow]
    refine sum_congr rfl (fun k _ => ?_)
    ring
  rw [hbin, lcoefX, Real.sqrt_mul hη0]

theorem solution (η η' : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hη'0 : 0 < η')
    (hη'1 : η' < 1) (X : FockOperator) (hX : IsDensity X) :
    let K : ℕ → ℕ → ℂ := fun m n => X (fockKet n) m
    (∀ a b : ℕ, Summable (vacuumLossTerm η' K a b)) ∧
    (∀ a b : ℕ, Summable (vacuumLossTerm η (vacuumLossKernel η' K) a b)) ∧
    (∀ a b : ℕ, Summable (vacuumLossTerm (η * η') K a b)) ∧
    ∀ m n : ℕ, vacuumLossKernel η (vacuumLossKernel η' K) m n =
      vacuumLossKernel (η * η') K m n := by
  intro K
  have hK : ∀ a b, ‖K a b‖ ≤ ‖X‖ := by
    intro a b
    calc ‖K a b‖ ≤ ‖X (fockKet b)‖ := lp.norm_apply_le_norm (by norm_num) _ _
      _ ≤ ‖X‖ * ‖fockKet b‖ := X.le_opNorm _
      _ = ‖X‖ := by
        rw [fockKet, lp.norm_single (by norm_num), norm_one, mul_one]
  have hee0 : 0 < η * η' := mul_pos hη0 hη'0
  have hee1 : η * η' < 1 := by nlinarith
  have hsumK : ∀ e : ℝ, 0 < e → e < 1 → ∀ a b, Summable (vacuumLossTerm e K a b) := by
    intro e he0 he1 a b
    refine Summable.of_norm_bounded ((lcoefX_summable he0 he1 a b).mul_left ‖X‖) (fun l => ?_)
    rw [termX_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (lcoefX_nonneg he1.le a b l),
      mul_comm]
    exact mul_le_mul_of_nonneg_right (hK _ _) (lcoefX_nonneg he1.le a b l)
  -- the double family
  let G : ℕ → ℕ → ℕ × ℕ → ℂ := fun m n p =>
    ((lcoefX η m n p.1 * lcoefX η' (m + p.1) (n + p.1) p.2 : ℝ) : ℂ) * K (m + p.1 + p.2) (n + p.1 + p.2)
  let e := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)
  have hA : ∀ m n, Summable (fun p : ℕ × ℕ => lcoefX η m n p.1 * lcoefX η' (m + p.1) (n + p.1) p.2) := by
    intro m n
    rw [← e.summable_iff]
    refine (summable_sigma_of_nonneg (fun x => mul_nonneg (lcoefX_nonneg hη1.le _ _ _)
      (lcoefX_nonneg hη'1.le _ _ _))).mpr ⟨fun L => Summable.of_finite, ?_⟩
    have : (fun L => ∑' y : antidiagonal L, (fun p : ℕ × ℕ =>
        lcoefX η m n p.1 * lcoefX η' (m + p.1) (n + p.1) p.2) (e ⟨L, y⟩)) =
        lcoefX (η * η') m n := by
      funext L
      rw [← coefX_id hη0.le hη'0.le]
      exact Finset.tsum_subtype (antidiagonal L) (fun p : ℕ × ℕ =>
        lcoefX η m n p.1 * lcoefX η' (m + p.1) (n + p.1) p.2)
    rw [this]
    exact lcoefX_summable hee0 hee1 m n
  have hG : ∀ m n, Summable (G m n) := by
    intro m n
    refine Summable.of_norm_bounded ((hA m n).mul_left ‖X‖) (fun p => ?_)
    have h0 : 0 ≤ lcoefX η m n p.1 * lcoefX η' (m + p.1) (n + p.1) p.2 :=
      mul_nonneg (lcoefX_nonneg hη1.le _ _ _) (lcoefX_nonneg hη'1.le _ _ _)
    simp only [G]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0, mul_comm]
    exact mul_le_mul_of_nonneg_right (hK _ _) h0
  have hrow : ∀ m n l, vacuumLossTerm η (vacuumLossKernel η' K) m n l = ∑' l', G m n (l, l') := by
    intro m n l
    rw [termX_eq, vacuumLossKernel, ← tsum_mul_left]
    refine tsum_congr (fun l' => ?_)
    rw [termX_eq]
    simp only [G]
    push_cast; ring
  refine ⟨hsumK η' hη'0 hη'1, fun a b => ?_, hsumK (η * η') hee0 hee1, fun m n => ?_⟩
  · rw [show vacuumLossTerm η (vacuumLossKernel η' K) a b = fun l => ∑' l', G a b (l, l') from
      funext (hrow a b)]
    exact (hG a b).prod
  · have hs := (e.summable_iff.mpr (hG m n)).tsum_sigma
    simp only [Function.comp] at hs
    rw [vacuumLossKernel, tsum_congr (hrow m n), ← (hG m n).tsum_prod, ← e.tsum_eq, hs,
      vacuumLossKernel]
    refine tsum_congr (fun L => ?_)
    show ∑' c : antidiagonal L, G m n c = _
    rw [Finset.tsum_subtype (antidiagonal L) (G m n), termX_eq]
    have : ∀ x ∈ antidiagonal L, G m n x =
        ((lcoefX η m n x.1 * lcoefX η' (m + x.1) (n + x.1) x.2 : ℝ) : ℂ) * K (m + L) (n + L) := by
      intro x hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      simp only [G]
      rw [add_assoc m, add_assoc n, hx]
    rw [sum_congr rfl this, ← sum_mul, ← Complex.ofReal_sum, coefX_id hη0.le hη'0.le]
