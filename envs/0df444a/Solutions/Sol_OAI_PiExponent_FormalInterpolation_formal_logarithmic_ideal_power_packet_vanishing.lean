-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.formal_logarithmic_ideal_power_packet_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:10:43.030748+00:00
-- url     : https://prove2.me/submissions/565dee42-b4eb-4969-8dc2-91f99f31dc6c

import Mathlib
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

open OAI.PiExponent.FormalInterpolation in
theorem pie_lift_coeff {m : ℕ} (D : PowerSeries ℂ) (b : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff b (liftSeries m D) =
      if b.tail = 0 then PowerSeries.coeff (b 0) D else 0 := by
  conv_lhs => rw [← Finsupp.cons_tail b]
  rw [← MvPowerSeries.coeff_coeff_finSuccEquiv]
  simp only [liftSeries, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe,
    Function.comp_apply, RingEquiv.coe_toRingHom]
  rw [show (MvPowerSeries.finSuccEquiv ℂ m)
      ((MvPowerSeries.finSuccEquiv ℂ m).symm.toRingEquiv (PowerSeries.map MvPowerSeries.C D))
      = PowerSeries.map MvPowerSeries.C D from
    (MvPowerSeries.finSuccEquiv ℂ m).apply_symm_apply _]
  rw [PowerSeries.coeff_map, MvPowerSeries.coeff_C]

open OAI.PiExponent.FormalInterpolation in
theorem pie_aeval_lift {m : ℕ} (p : Polynomial ℂ) :
    Polynomial.aeval (MvPowerSeries.X (0 : Fin (m + 1)) : MvPowerSeries (Fin (m + 1)) ℂ) p =
      liftSeries m (p : PowerSeries ℂ) := by
  have : (Polynomial.aeval (MvPowerSeries.X (0 : Fin (m + 1)) :
      MvPowerSeries (Fin (m + 1)) ℂ)).toRingHom =
      (liftSeries m).comp (Polynomial.coeToPowerSeries.ringHom) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C, RingHom.coe_comp,
        Function.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C]
      simp only [liftSeries, RingHom.coe_comp, Function.comp_apply, PowerSeries.map_C]
      rw [MvPowerSeries.algebraMap_apply]
      apply (MvPowerSeries.finSuccEquiv ℂ m).injective
      simp [MvPowerSeries.finSuccEquiv_C]
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X, RingHom.coe_comp,
        Function.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
      simp only [liftSeries, RingHom.coe_comp, Function.comp_apply, PowerSeries.map_X]
      apply (MvPowerSeries.finSuccEquiv ℂ m).injective
      simp [MvPowerSeries.finSuccEquiv_X_zero]
  exact congrArg (fun f => f p) this

/-- every monomial in the support has weight at least `B` -/
def pieLW {m : ℕ} (φ : (Fin (m + 1) →₀ ℕ) → ℝ) (B : ℝ) (f : MvPowerSeries (Fin (m + 1)) ℂ) : Prop :=
  ∀ b, MvPowerSeries.coeff b f ≠ 0 → B ≤ φ b

section
variable {m : ℕ} {φ : (Fin (m + 1) →₀ ℕ) → ℝ}

theorem pieLW_mono {B B' : ℝ} (h : B' ≤ B) {f : MvPowerSeries (Fin (m + 1)) ℂ} (hf : pieLW φ B f) :
    pieLW φ B' f := fun b hb => h.trans (hf b hb)

theorem pieLW_zero {B : ℝ} : pieLW φ B (0 : MvPowerSeries (Fin (m + 1)) ℂ) := by
  intro b hb; simp at hb

theorem pieLW_add {B : ℝ} {f g : MvPowerSeries (Fin (m + 1)) ℂ} (hf : pieLW φ B f)
    (hg : pieLW φ B g) : pieLW φ B (f + g) := by
  intro b hb
  rw [map_add] at hb
  by_cases h : MvPowerSeries.coeff b f = 0
  · rw [h, zero_add] at hb; exact hg b hb
  · exact hf b h

theorem pieLW_mul (hφ : ∀ x y, φ (x + y) = φ x + φ y) {B B' : ℝ}
    {f g : MvPowerSeries (Fin (m + 1)) ℂ} (hf : pieLW φ B f) (hg : pieLW φ B' g) :
    pieLW φ (B + B') (f * g) := by
  intro b hb
  rw [MvPowerSeries.coeff_mul] at hb
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx, hφ]
  exact add_le_add (hf _ (left_ne_zero_of_mul hne)) (hg _ (right_ne_zero_of_mul hne))

theorem pieLW_pow (hφ : ∀ x y, φ (x + y) = φ x + φ y) (hφ0 : φ 0 = 0) {B : ℝ}
    {f : MvPowerSeries (Fin (m + 1)) ℂ} (hf : pieLW φ B f) (k : ℕ) :
    pieLW φ (k * B) (f ^ k) := by
  induction k with
  | zero =>
    intro b hb
    rw [pow_zero, MvPowerSeries.coeff_one] at hb
    split_ifs at hb with h
    · subst h; simp [hφ0]
    · exact absurd rfl hb
  | succ k ih =>
    rw [pow_succ]
    have := pieLW_mul hφ ih hf
    refine pieLW_mono (le_of_eq ?_) this
    push_cast; ring

theorem pieLW_span (hφ : ∀ x y, φ (x + y) = φ x + φ y) (hφnn : ∀ x, 0 ≤ φ x) {B : ℝ}
    {S : Set (MvPowerSeries (Fin (m + 1)) ℂ)} (hS : ∀ s ∈ S, pieLW φ B s)
    {f : MvPowerSeries (Fin (m + 1)) ℂ} (hf : f ∈ Ideal.span S) : pieLW φ B f := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact pieLW_zero
  | add x y _ _ hx hy => exact pieLW_add hx hy
  | smul a x _ hx =>
    have h0 : pieLW φ 0 a := fun b _ => hφnn b
    have := pieLW_mul hφ h0 hx
    rw [zero_add] at this
    exact this

theorem pieLW_ideal_pow (hφ : ∀ x y, φ (x + y) = φ x + φ y) (hφnn : ∀ x, 0 ≤ φ x) {B : ℝ}
    {I : Ideal (MvPowerSeries (Fin (m + 1)) ℂ)} (hI : ∀ f ∈ I, pieLW φ B f) (n : ℕ) :
    ∀ f ∈ I ^ n, pieLW φ (n * B) f := by
  induction n with
  | zero => intro f _ b _; simp [hφnn b]
  | succ n ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf (fun x hx y hy => ?_) (fun x y hx hy => pieLW_add hx hy)
    have := pieLW_mul hφ (ih x hx) (hI y hy)
    refine pieLW_mono (le_of_eq ?_) this
    push_cast; ring
end

open OAI.PiExponent.FormalInterpolation in
theorem solution
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ)
    (r : Fin m → ℂ) (R : ℝ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (hR : 0 < R)
    (hscale : ∀ i, R ≤ (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ (FormalInterpolation.logarithmicCentersIdeal
      (fun j : Fin K => fun i => (j.val : ℂ) * r i) T e) ^ n)
    (rho : InterpolationMatrix.Row K v0 theta w ((n : ℝ) * R)) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
      (FormalInterpolation.formalJet (fun i => (rho.1.val : ℂ) * r i) P) = 0 := by
  classical
  set rw := InterpolationMatrix.rowWeights v0 theta w with hrw
  have hrw0 : rw 0 = v0 := rfl
  have hrwpos : ∀ i, 0 < rw i := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hv0
    · show 0 < w k / theta
      exact div_pos (hw k) htheta
  set c : Fin m → ℂ := fun i => (rho.1.val : ℂ) * r i
  set J := FormalInterpolation.formalJet c
  let φ : (Fin (m + 1) →₀ ℕ) → ℝ := fun b => ∑ i, rw i * (b i : ℝ)
  have hφ : ∀ x y, φ (x + y) = φ x + φ y := by
    intro x y; simp only [φ, Finsupp.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]
  have hφ0 : φ 0 = 0 := by simp [φ]
  have hφnn : ∀ x, 0 ≤ φ x := fun x =>
    Finset.sum_nonneg (fun i _ => mul_nonneg (hrwpos i).le (Nat.cast_nonneg _))
  -- step 1: membership in the single local ideal
  have hPj : P ∈ (logarithmicCenterIdeal c T e) ^ n := by
    have hle : logarithmicCentersIdeal (fun j : Fin K => fun i => (j.val : ℂ) * r i) T e ≤
        logarithmicCenterIdeal c T e :=
      Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ rho.1))
    exact Ideal.pow_right_mono hle n hP
  -- step 2: images of the generators
  have hJ0 : J (MvPolynomial.X 0 - 1) = MvPowerSeries.X 0 := by
    simp [J, FormalInterpolation.formalJet]
  have hgen : ∀ i, pieLW φ R (J (logarithmicCoordinate c T i ^ e i)) := by
    intro i
    rw [map_pow]
    refine pieLW_mono (hscale i) ?_
    have hbase : pieLW φ (rw i) (J (logarithmicCoordinate c T i)) := by
      refine Fin.cases ?_ (fun k => ?_) i
      · simp only [logarithmicCoordinate, Fin.cases_zero]
        rw [hJ0]
        intro b hb
        rw [MvPowerSeries.coeff_X] at hb
        split_ifs at hb with h
        · subst h
          simp only [φ]
          rw [Finset.sum_eq_single 0]
          · simp
          · intro j _ hj; simp [Ne.symm hj]
          · simp
        · exact absurd rfl hb
      · have hJk : J (logarithmicCoordinate c T k.succ) = MvPowerSeries.X k.succ +
            liftSeries m (PowerSeries.log ℂ -
              ((InterpolationMatrix.truncatedLog (T k) : Polynomial ℂ) : PowerSeries ℂ)) := by
          simp only [logarithmicCoordinate, Fin.cases_succ, map_sub]
          rw [← Polynomial.aeval_algHom_apply, hJ0, pie_aeval_lift]
          simp [J, FormalInterpolation.formalJet, MvPowerSeries.algebraMap_apply]
          ring
        rw [hJk]
        intro b hb
        rw [map_add, pie_lift_coeff, MvPowerSeries.coeff_X] at hb
        by_cases hb1 : b = Finsupp.single k.succ 1
        · subst hb1
          simp only [φ]
          rw [Finset.sum_eq_single k.succ]
          · simp
          · intro j _ hj; simp [Ne.symm hj]
          · simp
        · rw [if_neg hb1, zero_add] at hb
          split_ifs at hb with ht
          · have htail : ∀ j : Fin m, b j.succ = 0 := fun j => by
              have := DFunLike.congr_fun ht j
              simpa [Finsupp.tail, Fin.tail] using this
            have hTk : T k ≤ b 0 := by
              by_contra hlt
              push Not at hlt
              apply hb
              simp [InterpolationMatrix.truncatedLog, Polynomial.coeff_coe,
                PowerSeries.coeff_trunc, hlt]
            have : φ b = rw 0 * (b 0 : ℝ) := by
              simp only [φ, Fin.sum_univ_succ, htail, Nat.cast_zero, mul_zero,
                Finset.sum_const_zero, add_zero]
            rw [this, hrw0]
            have h1 := hT k
            have h2 : (T k : ℝ) ≤ b 0 := by exact_mod_cast hTk
            nlinarith
          · exact absurd rfl hb
    have := pieLW_pow hφ hφ0 hbase (e i)
    refine pieLW_mono (le_of_eq ?_) this
    ring
  -- step 3: the image ideal
  have hmap : (logarithmicCenterIdeal c T e).map J =
      Ideal.span (Set.range (fun i => J (logarithmicCoordinate c T i ^ e i))) := by
    rw [logarithmicCenterIdeal, Ideal.map_span, ← Set.range_comp]
    rfl
  have hJP : J P ∈ ((logarithmicCenterIdeal c T e).map J) ^ n := by
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem J hPj
  rw [hmap] at hJP
  have hW := pieLW_ideal_pow hφ hφnn (fun f hf => pieLW_span hφ hφnn
    (by rintro _ ⟨i, rfl⟩; exact hgen i) hf) n (J P) hJP
  by_contra hne
  have hlow := hW _ hne
  have hmem := rho.2.2
  simp only [OAI.PiExponent.strictWeightedSimplex, Finset.mem_filter] at hmem
  have : φ (InterpolationMatrix.exponentVector rho.2.val) = ∑ i, rw i * (rho.2.val i : ℝ) := by
    simp [φ, InterpolationMatrix.exponentVector]
  rw [this] at hlow
  linarith [hmem.2]
