-- Prove2me | solution 1 for NumberField.mixedEmbedding.exists_contDiff_periodic_normAtPlace_eq_exp_polarCoord_units_and_fst_eq_and_snd_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ae68a5dd-2325-55a6-96c3-8f10bc51d9d6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_mixedEmbedding_exists_contDiff_periodic_normAtPlace_eq_exp_polarCoord_units_and_fst_eq_and_snd_eq

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical

namespace ExpPolar

variable (K : Type) [Field K] [NumberField K]

noncomputable abbrev eI : InfinitePlace K ≃ Fin (Fintype.card (InfinitePlace K)) := Fintype.equivFin _

noncomputable abbrev eC : {w : InfinitePlace K // IsComplex w} ≃ Fin (nrComplexPlaces K) := Fintype.equivFin _

noncomputable def P (s : {w : InfinitePlace K // IsReal w} → ℤˣ)
    (p : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin (nrComplexPlaces K) → ℝ)) : mixedSpace K :=
  (fun w => (((s w : ℤˣ) : ℤ) : ℝ) * Real.exp (p.1 (eI K w.1)),
   fun w => ((Real.exp (p.1 (eI K w.1) / 2) : ℝ) : ℂ) *
     Complex.exp (((2 * Real.pi * p.2 (eC K w) : ℝ) : ℂ) * Complex.I))

noncomputable def sgn (y : mixedSpace K) : {w : InfinitePlace K // IsReal w} → ℤˣ :=
  fun w => if 0 < y.1 w then 1 else -1

private noncomputable def _root_.ExpPolar.arg (y : mixedSpace K) : Fin (nrComplexPlaces K) → ℝ :=
  fun j => Complex.arg (y.2 ((eC K).symm j)) / (2 * Real.pi)

p2m_export "ExpPolar" "arg"
theorem P_fst (s : {w : InfinitePlace K // IsReal w} → ℤˣ)
    (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ)
    (w : {w : InfinitePlace K // IsReal w}) :
    (P K s (x, θ)).1 w = (((s w : ℤˣ) : ℤ) : ℝ) * Real.exp (x (eI K w.1)) := rfl

theorem P_snd (s : {w : InfinitePlace K // IsReal w} → ℤˣ)
    (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ)
    (w : {w : InfinitePlace K // IsComplex w}) :
    (P K s (x, θ)).2 w = ((Real.exp (x (eI K w.1) / 2) : ℝ) : ℂ) *
      Complex.exp (((2 * Real.pi * θ (eC K w) : ℝ) : ℂ) * Complex.I) := rfl

theorem abs_units_int_cast (s : ℤˣ) : |((s : ℤ) : ℝ)| = 1 := by
  rcases Int.units_eq_one_or s with h | h <;> simp [h]

theorem contDiff_P (s : {w : InfinitePlace K // IsReal w} → ℤˣ) : ContDiff ℝ (⊤ : ℕ∞) (P K s) := by
  refine ContDiff.prodMk ?_ ?_
  · refine contDiff_pi' fun w => ?_
    exact contDiff_const.mul (Real.contDiff_exp.comp ((contDiff_apply ℝ ℝ (eI K w.1)).comp contDiff_fst))
  · refine contDiff_pi' fun w => ?_
    refine ContDiff.mul ?_ ?_
    · exact Complex.ofRealCLM.contDiff.comp
        (Real.contDiff_exp.comp (((contDiff_apply ℝ ℝ (eI K w.1)).comp contDiff_fst).div_const _))
    · refine Complex.contDiff_exp.comp ?_
      refine ContDiff.mul ?_ contDiff_const
      exact Complex.ofRealCLM.contDiff.comp
        (contDiff_const.mul ((contDiff_apply ℝ ℝ (eC K w)).comp contDiff_snd))

theorem P_periodic (s : {w : InfinitePlace K // IsReal w} → ℤˣ)
    (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ)
    (k : Fin (nrComplexPlaces K) → ℤ) :
    P K s (x, θ + fun j => (k j : ℝ)) = P K s (x, θ) := by
  refine Prod.ext rfl (funext fun w => ?_)
  rw [P_snd, P_snd, Pi.add_apply]
  congr 1
  have : (((2 * Real.pi * (θ (eC K w) + (k (eC K w) : ℝ)) : ℝ) : ℂ) * Complex.I) =
      ((2 * Real.pi * θ (eC K w) : ℝ) : ℂ) * Complex.I + (k (eC K w) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem P_mul (s s' : {w : InfinitePlace K // IsReal w} → ℤˣ)
    (x x' : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ θ' : Fin (nrComplexPlaces K) → ℝ) :
    P K (s * s') (x + x', θ + θ') = P K s (x, θ) * P K s' (x', θ') := by
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · show (P K (s * s') (x + x', θ + θ')).1 w = (P K s (x, θ)).1 w * (P K s' (x', θ')).1 w
    rw [P_fst, P_fst, P_fst, Pi.mul_apply, Units.val_mul, Int.cast_mul, Pi.add_apply, Real.exp_add]
    ring
  · show (P K (s * s') (x + x', θ + θ')).2 w = (P K s (x, θ)).2 w * (P K s' (x', θ')).2 w
    rw [P_snd, P_snd, P_snd, Pi.add_apply, Pi.add_apply, add_div, Real.exp_add, Complex.ofReal_mul]
    have : (((2 * Real.pi * (θ (eC K w) + θ' (eC K w)) : ℝ) : ℂ) * Complex.I) =
        ((2 * Real.pi * θ (eC K w) : ℝ) : ℂ) * Complex.I + ((2 * Real.pi * θ' (eC K w) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_add]
    ring

theorem normAtPlace_P (s : {w : InfinitePlace K // IsReal w} → ℤˣ)
    (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ) (w : InfinitePlace K) :
    normAtPlace w (P K s (x, θ)) = Real.exp (x (eI K w) / (w.mult : ℝ)) := by
  by_cases hw : IsReal w
  · rw [normAtPlace_apply_of_isReal hw, P_fst, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_units_int_cast, one_mul, Real.abs_exp, mult_isReal ⟨w, hw⟩, Nat.cast_one, div_one]
  · have hw' : IsComplex w := not_isReal_iff_isComplex.mp hw
    rw [normAtPlace_apply_of_isComplex hw', P_snd, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, Real.abs_exp, mult_isComplex ⟨w, hw'⟩, Nat.cast_ofNat]

theorem fst_ne_zero {y : mixedSpace K} (hy : IsUnit y) (w : {w : InfinitePlace K // IsReal w}) : y.1 w ≠ 0 :=
  ((Prod.isUnit_iff.1 hy).1.map (Pi.evalMonoidHom (fun _ => ℝ) w)).ne_zero

theorem snd_ne_zero {y : mixedSpace K} (hy : IsUnit y) (w : {w : InfinitePlace K // IsComplex w}) : y.2 w ≠ 0 :=
  ((Prod.isUnit_iff.1 hy).2.map (Pi.evalMonoidHom (fun _ => ℂ) w)).ne_zero

theorem P_sgn_log_arg (y : mixedSpace K) (hy : IsUnit y) :
    P K (sgn K y) (fun i => (((eI K).symm i).mult : ℝ) * Real.log (normAtPlace ((eI K).symm i) y), arg K y) = y := by
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · rw [P_fst, Equiv.symm_apply_apply, mult_isReal, Nat.cast_one, one_mul, normAtPlace_apply_of_isReal w.2,
      Real.exp_log (norm_pos_iff.2 (fst_ne_zero K hy w)), Real.norm_eq_abs]
    unfold sgn
    by_cases h : 0 < y.1 w
    · rw [if_pos h, Units.val_one, Int.cast_one, one_mul, abs_of_pos h]
    · rw [if_neg h, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul,
        abs_of_neg (lt_of_le_of_ne (not_lt.1 h) (fst_ne_zero K hy w)), neg_neg]
  · rw [P_snd, Equiv.symm_apply_apply, mult_isComplex, Nat.cast_ofNat, normAtPlace_apply_of_isComplex w.2]
    unfold arg
    rw [Equiv.symm_apply_apply, mul_div_cancel_left₀ _ (two_ne_zero), Real.exp_log (norm_pos_iff.2 (snd_ne_zero K hy w)),
      mul_div_cancel₀ _ (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
    exact Complex.norm_mul_exp_arg_mul_I _

theorem sgn_mul (y y' : mixedSpace K) (hy : IsUnit y) (hy' : IsUnit y') : sgn K (y * y') = sgn K y * sgn K y' := by
  funext w
  have ha := fst_ne_zero K hy w
  have hb := fst_ne_zero K hy' w
  simp only [sgn, Pi.mul_apply, Prod.fst_mul]
  rcases lt_or_gt_of_ne ha with ha | ha <;> rcases lt_or_gt_of_ne hb with hb | hb
  · rw [if_pos (mul_pos_of_neg_of_neg ha hb), if_neg (not_lt.2 ha.le), if_neg (not_lt.2 hb.le)]; simp
  · rw [if_neg (not_lt.2 (mul_neg_of_neg_of_pos ha hb).le), if_neg (not_lt.2 ha.le), if_pos hb]; simp
  · rw [if_neg (not_lt.2 (mul_neg_of_pos_of_neg ha hb).le), if_pos ha, if_neg (not_lt.2 hb.le)]; simp
  · rw [if_pos (mul_pos ha hb), if_pos ha, if_pos hb]; simp

theorem arg_mul (y y' : mixedSpace K) (hy : IsUnit y) (hy' : IsUnit y') :
    ∃ k : Fin (nrComplexPlaces K) → ℤ, arg K (y * y') = arg K y + arg K y' + fun j => (k j : ℝ) := by
  have h : ∀ j : Fin (nrComplexPlaces K), ∃ k : ℤ,
      Complex.arg ((y * y').2 ((eC K).symm j)) - (Complex.arg (y.2 ((eC K).symm j)) + Complex.arg (y'.2 ((eC K).symm j))) =
        2 * Real.pi * k := by
    intro j
    rw [← Real.Angle.angle_eq_iff_two_pi_dvd_sub, Real.Angle.coe_add, Prod.snd_mul, Pi.mul_apply]
    exact Complex.arg_mul_coe_angle (snd_ne_zero K hy _) (snd_ne_zero K hy' _)
  choose k hk using h
  refine ⟨k, funext fun j => ?_⟩
  simp only [arg, Pi.add_apply]
  have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have h := hk j
  rw [sub_eq_iff_eq_add] at h
  rw [h, add_div, mul_div_cancel_left₀ _ hπ, add_div]
  ring

theorem bound (C : Set (mixedSpace K)) (hC : IsCompact C) (hCu : ∀ y ∈ C, IsUnit y) :
    ∃ R : ℝ, ∀ (s : {w : InfinitePlace K // IsReal w} → ℤˣ)
      (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ),
      P K s (x, θ) ∈ C → ∀ i, |x i| ≤ R := by
  let F : mixedSpace K → (InfinitePlace K → ℝ) := fun y w => (w.mult : ℝ) * Real.log (normAtPlace w y)
  have hF : ContinuousOn F C := by
    refine continuousOn_pi.2 fun w => ?_
    exact (continuousOn_const.mul (((continuous_normAtPlace w).continuousOn).log
      (fun y hy => ((hCu y hy).map (normAtPlace w)).ne_zero)))
  obtain ⟨R, hR⟩ := hC.exists_bound_of_continuousOn hF
  refine ⟨R, fun s x θ hmem i => ?_⟩
  have h1 := hR _ hmem
  have h2 : F (P K s (x, θ)) ((eI K).symm i) = x i := by
    simp only [F]
    rw [normAtPlace_P, Equiv.apply_symm_apply, Real.log_exp, mul_div_cancel₀ _ mult_coe_ne_zero]
  rw [← h2, ← Real.norm_eq_abs]
  exact (norm_le_pi_norm _ _).trans h1

end ExpPolar

open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K] :
    ∃ (P : ({w : InfinitePlace K // w.IsReal} → ℤˣ) →
          (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin (nrComplexPlaces K) → ℝ) → mixedSpace K)
      (sgn : mixedSpace K → ({w : InfinitePlace K // w.IsReal} → ℤˣ))
      (arg : mixedSpace K → (Fin (nrComplexPlaces K) → ℝ)),
      (∀ s, ContDiff ℝ (⊤ : ℕ∞) (P s)) ∧
      (∀ s (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ)
          (k : Fin (nrComplexPlaces K) → ℤ), P s (x, θ + fun j => (k j : ℝ)) = P s (x, θ)) ∧
      (∀ s s' (x x' : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ θ' : Fin (nrComplexPlaces K) → ℝ),
          P (s * s') (x + x', θ + θ') = P s (x, θ) * P s' (x', θ')) ∧
      (∀ s (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ) (w : InfinitePlace K),
          normAtPlace w (P s (x, θ)) = Real.exp (x (Fintype.equivFin (InfinitePlace K) w) / (w.mult : ℝ))) ∧
      (∀ y : mixedSpace K, IsUnit y →
          P (sgn y) (fun i => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) *
              Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) y), arg y) = y) ∧
      (∀ y y' : mixedSpace K, IsUnit y → IsUnit y' →
          sgn (y * y') = sgn y * sgn y' ∧
            ∃ k : Fin (nrComplexPlaces K) → ℤ, arg (y * y') = arg y + arg y' + fun j => (k j : ℝ)) ∧
      (∀ C : Set (mixedSpace K), IsCompact C → (∀ y ∈ C, IsUnit y) →
          ∃ R : ℝ, ∀ s (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ),
            P s (x, θ) ∈ C → ∀ i, |x i| ≤ R) ∧
      (∀ s (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ)
          (w : {w : InfinitePlace K // w.IsReal}),
          (P s (x, θ)).1 w = (((s w : ℤˣ) : ℤ) : ℝ) * Real.exp (x (Fintype.equivFin (InfinitePlace K) w.1))) ∧
      (∀ s (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ)
          (w : {w : InfinitePlace K // w.IsComplex}),
          (P s (x, θ)).2 w = Complex.exp (((x (Fintype.equivFin (InfinitePlace K) w.1) / 2 : ℝ) : ℂ) +
            2 * Real.pi * Complex.I * ((θ (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} w) : ℝ) : ℂ))) ∧
      (∀ (y : mixedSpace K) (w : {w : InfinitePlace K // w.IsReal}), sgn y w = if 0 < y.1 w then 1 else -1) ∧
      (∀ (y : mixedSpace K) (j : Fin (nrComplexPlaces K)),
          arg y j = Complex.arg (y.2 ((Fintype.equivFin {w : InfinitePlace K // w.IsComplex}).symm j)) / (2 * Real.pi)) := by
  refine ⟨ExpPolar.P K, ExpPolar.sgn K, ExpPolar.arg K, ExpPolar.contDiff_P K, ExpPolar.P_periodic K, ExpPolar.P_mul K,
    ExpPolar.normAtPlace_P K, ExpPolar.P_sgn_log_arg K,
    fun y y' hy hy' => ⟨ExpPolar.sgn_mul K y y' hy hy', ExpPolar.arg_mul K y y' hy hy'⟩, ExpPolar.bound K,
    fun s x θ w => rfl, fun s x θ w => ?_, fun y w => rfl, fun y j => rfl⟩
  rw [ExpPolar.P_snd, Complex.exp_add, Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf

end S_NumberField_mixedEmbedding_exists_contDiff_periodic_normAtPlace_eq_exp_polarCoord_units_and_fst_eq_and_snd_eq
end P2MW
export P2MW.S_NumberField_mixedEmbedding_exists_contDiff_periodic_normAtPlace_eq_exp_polarCoord_units_and_fst_eq_and_snd_eq (solution)
