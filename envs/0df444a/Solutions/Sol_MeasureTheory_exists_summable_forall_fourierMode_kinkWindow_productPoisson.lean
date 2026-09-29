-- Prove2me | solution 1 for MeasureTheory.exists_summable_forall_fourierMode_kinkWindow_productPoisson
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/2ad092f9-8f39-5406-88b2-bbbf87a54456

import Mathlib
import Theorems.Thm_MeasureTheory_exists_summable_forall_norm_setIntegral_mul_cexp_le_prod_of_contDiff_of_periodic
import Theorems.Thm_MeasureTheory_exists_summable_forall_fourierMode_absOneSubExp_mul_productPoisson_of_contDiff_of_periodic
import Theorems.Thm_MeasureTheory_exists_summable_forall_fourierMode_normSqLogGerm_mul_productPoisson_of_contDiff_of_periodic
import Theorems.Thm_MeasureTheory_hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_summable_forall_fourierMode_kinkWindow_productPoisson

set_option autoImplicit false

open MeasureTheory

namespace PKAux44

theorem continuous_modeChar {c : ℕ} (m : Fin c → ℤ) :
    Continuous fun θ : Fin c → ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))) := by
  have h1 : Continuous fun θ : Fin c → ℝ => (∑ j, (m j : ℝ) * θ j : ℝ) :=
    continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp h1)).neg

theorem continuous_xChar {r : ℕ} (ξ : Fin r → ℝ) :
    Continuous fun x : Fin r → ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) := by
  have h1 : Continuous fun x : Fin r → ℝ => (∑ k, ξ k * x k : ℝ) :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_apply k)
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp h1)).neg

theorem norm_xChar {r : ℕ} (ξ x : Fin r → ℝ) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ)))‖ = 1 := by
  rw [show -(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ)) =
      ((-(2 * Real.pi * (∑ k, ξ k * x k)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem integrable_xChar_mul {r : ℕ} (ξ : Fin r → ℝ) {f : (Fin r → ℝ) → ℂ} (hf : Integrable f) :
    Integrable fun x : Fin r → ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * f x :=
  hf.bdd_mul (continuous_xChar ξ).aestronglyMeasurable (Filter.Eventually.of_forall fun x => (norm_xChar ξ x).le)

theorem continuous_germ :
    Continuous fun q : ℝ × ℝ => ((‖(1 : ℂ) - Complex.exp ((q.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (q.2 : ℝ))‖ ^ 2 * Real.log ‖(1 : ℂ) - Complex.exp ((q.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (q.2 : ℝ))‖ : ℝ) : ℂ) := by
  have hρ : Continuous fun q : ℝ × ℝ =>
      ‖(1 : ℂ) - Complex.exp ((q.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (q.2 : ℝ))‖ :=
    continuous_norm.comp (continuous_const.sub (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_fst.div_const 2)).add
        (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)))))
  have h2 : Continuous fun t : ℝ => t ^ 2 * Real.log t :=
    by
    refine (continuous_id.mul Real.continuous_mul_log).congr fun t => ?_
    simp only [Pi.mul_apply, id_eq, sq]
    ring
  exact Complex.continuous_ofReal.comp (h2.comp hρ)

theorem continuous_germ_apply {r c : ℕ} (x : Fin r → ℝ) (k : Fin r) (j : Fin c) :
    Continuous fun θ : Fin c → ℝ => ((‖(1 : ℂ) - Complex.exp ((x k / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ ^ 2 * Real.log ‖(1 : ℂ) - Complex.exp ((x k / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ : ℝ) : ℂ) :=
  continuous_germ.comp (f := fun θ : Fin c → ℝ => (x k, θ j)) (continuous_const.prodMk (continuous_apply j))

theorem cexp_arg_add_one (s t : ℝ) :
    Complex.exp (((s / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((t + 1 : ℝ) : ℂ)) =
      Complex.exp (((s / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)) := by
  rw [Complex.ofReal_add, Complex.ofReal_one, mul_add, mul_one, ← add_assoc, Complex.exp_add,
    Complex.exp_two_pi_mul_I, mul_one]

theorem integrableOn_cube {c : ℕ} {f : (Fin c → ℝ) → ℂ} (hf : Continuous f) :
    IntegrableOn f (Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1)) volume :=
  (ContinuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ : Fin c => (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))) hf.continuousOn).mono_set
    (Set.pi_mono fun _ _ => Set.Ico_subset_Icc_self)

theorem hasCompactSupport_of_box {r : ℕ} {f : (Fin r → ℝ) → ℂ} (R : ℝ)
    (h : ∀ x : Fin r → ℝ, (∃ k, R < |x k|) → f x = 0) : HasCompactSupport f := by
  refine HasCompactSupport.intro (isCompact_univ_pi fun _ : Fin r => (isCompact_Icc : IsCompact (Set.Icc (-R) R))) ?_
  intro x hx
  apply h
  by_contra hcon
  push_neg at hcon
  exact hx (Set.mem_univ_pi.mpr fun k => Set.mem_Icc.mpr (abs_le.mp (hcon k)))

theorem prod_inv_sq_le_one {r : ℕ} (x : Fin r → ℝ) : ∏ k, (1 + |x k|)⁻¹ ^ 2 ≤ 1 :=
  Finset.prod_le_one (fun k _ => by positivity)
    (fun k _ => pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith [abs_nonneg (x k)])))

end PKAux44

open PKAux44 in
theorem solution
    {r c : ℕ} (kC : Fin c → Fin r) {ιR : Type} [Fintype ιR] (kR : ιR → Fin r)
    (B : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (C : ιR → (Fin r → ℝ) × (Fin c → ℝ) → ℂ)
    (E : Fin c → (Fin r → ℝ) × (Fin c → ℝ) → ℂ)
    (hB : ContDiff ℝ (⊤ : ℕ∞) B) (hC : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (C i)) (hE : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (E j))
    (hper : ∀ (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c),
      B (p.1, p.2 + Pi.single j 1) = B p ∧ (∀ i, C i (p.1, p.2 + Pi.single j 1) = C i p) ∧
        ∀ j', E j' (p.1, p.2 + Pi.single j 1) = E j' p)
    (S : Set (Fin r → ℝ)) (hS : IsCompact S)
    (hsupp : ∀ p : (Fin r → ℝ) × (Fin c → ℝ), p.1 ∉ S → B p = 0 ∧ (∀ i, C i p = 0) ∧ ∀ j, E j p = 0) :
    let G : (Fin r → ℝ) × (Fin c → ℝ) → ℂ := fun p =>
      B p + ∑ i, ((|1 - Real.exp (p.1 (kR i))| : ℝ) : ℂ) * C i p +
        ∑ j, ((‖(1 : ℂ) - Complex.exp ((p.1 (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 j : ℝ))‖ ^ 2 *
              Real.log ‖(1 : ℂ) - Complex.exp ((p.1 (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 j : ℝ))‖ : ℝ) : ℂ) *
            E j p
    let Gm : (Fin c → ℤ) → (Fin r → ℝ) → ℂ := fun m x =>
      ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
        G (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))
    ∃ Cm : (Fin c → ℤ) → ℝ, (∀ m, 0 ≤ Cm m) ∧ Summable Cm ∧
      (∀ m, Continuous (Gm m) ∧ Integrable (Gm m) ∧
        (∀ x : Fin r → ℝ, ‖Gm m x‖ ≤ Cm m * ∏ k, (1 + |x k|)⁻¹ ^ 2) ∧
        (∀ ξ : Fin r → ℝ,
          ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * Gm m x‖ ≤
            Cm m * ∏ k, (1 + |ξ k|)⁻¹ ^ 2)) ∧
      ∀ p : (Fin r → ℝ) × (Fin c → ℝ),
        HasSum (fun m : Fin c → ℤ => Gm m p.1 * Complex.exp (2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * p.2 j : ℝ) : ℂ)))
          (G p) := by
  intro G Gm
  classical

  obtain ⟨R, hR0, hSR⟩ := hS.isBounded.subset_closedBall_lt 0 0
  have hbox : ∀ x : Fin r → ℝ, (∃ k, R < |x k|) → x ∉ S := by
    rintro x ⟨k, hk⟩ hx
    have h1 : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hSR hx
    have h2 : |x k| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x k
    linarith
  have hsB : ∀ p : (Fin r → ℝ) × (Fin c → ℝ), (∃ k, R < |p.1 k|) → B p = 0 :=
    fun p h => (hsupp p (hbox p.1 h)).1
  have hsC : ∀ (i : ιR) (p : (Fin r → ℝ) × (Fin c → ℝ)), (∃ k, R < |p.1 k|) → C i p = 0 :=
    fun i p h => (hsupp p (hbox p.1 h)).2.1 i
  have hsE : ∀ (j : Fin c) (p : (Fin r → ℝ) × (Fin c → ℝ)), (∃ k, R < |p.1 k|) → E j p = 0 :=
    fun j p h => (hsupp p (hbox p.1 h)).2.2 j
  have hpB : ∀ (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c), B (p.1, p.2 + Pi.single j 1) = B p :=
    fun p j => (hper p j).1
  have hpC : ∀ (i : ιR) (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c), C i (p.1, p.2 + Pi.single j 1) = C i p :=
    fun i p j => (hper p j).2.1 i
  have hpE : ∀ (j' : Fin c) (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c), E j' (p.1, p.2 + Pi.single j 1) = E j' p :=
    fun j' p j => (hper p j).2.2 j'
  have hpB' : ∀ (x : Fin r → ℝ) (θ : Fin c → ℝ) (j : Fin c), B (x, θ + Pi.single j 1) = B (x, θ) :=
    fun x θ j => hpB (x, θ) j
  have hpC' : ∀ (i : ιR) (x : Fin r → ℝ) (θ : Fin c → ℝ) (j : Fin c), C i (x, θ + Pi.single j 1) = C i (x, θ) :=
    fun i x θ j => hpC i (x, θ) j
  have hpE' : ∀ (j' : Fin c) (x : Fin r → ℝ) (θ : Fin c → ℝ) (j : Fin c), E j' (x, θ + Pi.single j 1) = E j' (x, θ) :=
    fun j' x θ j => hpE j' (x, θ) j

  obtain ⟨hBreg, CB, hCBs, hCB0, hCBx, hCBξ⟩ :=
    MeasureTheory.exists_summable_forall_norm_setIntegral_mul_cexp_le_prod_of_contDiff_of_periodic B hB R hR0.le hsB hpB
  have hT1 : ∀ i : ιR, ∃ Ci : (Fin c → ℤ) → ℝ, (∀ m, 0 ≤ Ci m) ∧ Summable Ci ∧
      ∀ m : Fin c → ℤ, Continuous (fun x : Fin r → ℝ => (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), ((|1 - Real.exp (x (kR i))| : ℝ) : ℂ) * C i (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))) ∧
        Integrable (fun x : Fin r → ℝ => (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), ((|1 - Real.exp (x (kR i))| : ℝ) : ℂ) * C i (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))) ∧
        (∀ x : Fin r → ℝ, ‖(∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), ((|1 - Real.exp (x (kR i))| : ℝ) : ℂ) * C i (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))‖ ≤ Ci m * ∏ k, (1 + |x k|)⁻¹ ^ 2) ∧
        (∀ ξ : Fin r → ℝ, ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), ((|1 - Real.exp (x (kR i))| : ℝ) : ℂ) * C i (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))‖ ≤ Ci m * ∏ k, (1 + |ξ k|)⁻¹ ^ 2) :=
    fun i => MeasureTheory.exists_summable_forall_fourierMode_absOneSubExp_mul_productPoisson_of_contDiff_of_periodic
      (C i) (hC i) R hR0.le (hsC i) (hpC i) (kR i)
  choose CC hCC using hT1
  have hT2 : ∀ j : Fin c, ∃ Cj : (Fin c → ℤ) → ℝ, (∀ m, 0 ≤ Cj m) ∧ Summable Cj ∧
      ∀ m : Fin c → ℤ, Continuous (fun x : Fin r → ℝ => (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), ((‖(1 : ℂ) - Complex.exp ((x (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ ^ 2 * Real.log ‖(1 : ℂ) - Complex.exp ((x (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ : ℝ) : ℂ) * E j (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))) ∧
        Integrable (fun x : Fin r → ℝ => (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), ((‖(1 : ℂ) - Complex.exp ((x (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ ^ 2 * Real.log ‖(1 : ℂ) - Complex.exp ((x (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ : ℝ) : ℂ) * E j (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))) ∧
        (∀ x : Fin r → ℝ, ‖(∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), ((‖(1 : ℂ) - Complex.exp ((x (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ ^ 2 * Real.log ‖(1 : ℂ) - Complex.exp ((x (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ : ℝ) : ℂ) * E j (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))‖ ≤ Cj m * ∏ k, (1 + |x k|)⁻¹ ^ 2) ∧
        (∀ ξ : Fin r → ℝ, ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), ((‖(1 : ℂ) - Complex.exp ((x (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ ^ 2 * Real.log ‖(1 : ℂ) - Complex.exp ((x (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ : ℝ) : ℂ) * E j (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))‖ ≤ Cj m * ∏ k, (1 + |ξ k|)⁻¹ ^ 2) :=
    fun j => MeasureTheory.exists_summable_forall_fourierMode_normSqLogGerm_mul_productPoisson_of_contDiff_of_periodic
      (E j) (hE j) R hR0.le (hsE j) (hpE j) (kC j) j
  choose CE hCE using hT2

  have hcontG : ∀ x : Fin r → ℝ, Continuous fun θ : Fin c → ℝ => G (x, θ) := by
    intro x
    simp only [G]
    refine Continuous.add (Continuous.add ?_ ?_) ?_
    · exact hB.continuous.comp (continuous_const.prodMk continuous_id)
    · exact continuous_finsetSum _ fun i _ =>
        continuous_const.mul ((hC i).continuous.comp (continuous_const.prodMk continuous_id))
    · exact continuous_finsetSum _ fun j _ =>
        (continuous_germ_apply x (kC j) j).mul ((hE j).continuous.comp (continuous_const.prodMk continuous_id))
  have hperG : ∀ (x : Fin r → ℝ) (θ : Fin c → ℝ) (j : Fin c), G (x, θ + Pi.single j 1) = G (x, θ) := by
    intro x θ j
    have h1 : ∀ j' : Fin c,
        Complex.exp (((x (kC j') / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (((θ + Pi.single j 1 : Fin c → ℝ) j' : ℝ) : ℂ)) =
          Complex.exp (((x (kC j') / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((θ j' : ℝ) : ℂ)) := by
      intro j'
      rw [Pi.add_apply, Pi.single_apply]
      split_ifs with h
      · exact cexp_arg_add_one _ _
      · rw [add_zero]
    simp only [G, hpB', hpC', hpE', h1]

  have hGm : ∀ (m : Fin c → ℤ) (x : Fin r → ℝ),
      Gm m x = (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), B (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) + ∑ i, (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), ((|1 - Real.exp (x (kR i))| : ℝ) : ℂ) * C i (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) + ∑ j, (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), ((‖(1 : ℂ) - Complex.exp ((x (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ ^ 2 * Real.log ‖(1 : ℂ) - Complex.exp ((x (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ : ℝ) : ℂ) * E j (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) := by
    intro m x
    have iB : Integrable (fun θ : Fin c → ℝ => B (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) (volume.restrict (Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1))) :=
      integrableOn_cube ((hB.continuous.comp (continuous_const.prodMk continuous_id)).mul (continuous_modeChar m))
    have iC : ∀ i : ιR, Integrable (fun θ : Fin c → ℝ => ((|1 - Real.exp (x (kR i))| : ℝ) : ℂ) * C i (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))
        (volume.restrict (Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1))) := fun i =>
      integrableOn_cube ((continuous_const.mul ((hC i).continuous.comp (continuous_const.prodMk continuous_id))).mul
        (continuous_modeChar m))
    have iE : ∀ j : Fin c, Integrable (fun θ : Fin c → ℝ => ((‖(1 : ℂ) - Complex.exp ((x (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ ^ 2 * Real.log ‖(1 : ℂ) - Complex.exp ((x (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ : ℝ) : ℂ) * E j (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))
        (volume.restrict (Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1))) := fun j =>
      integrableOn_cube (((continuous_germ_apply x (kC j) j).mul
        ((hE j).continuous.comp (continuous_const.prodMk continuous_id))).mul (continuous_modeChar m))
    have iBC : Integrable (fun θ : Fin c → ℝ => B (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))) +
        ∑ i, ((|1 - Real.exp (x (kR i))| : ℝ) : ℂ) * C i (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) (volume.restrict (Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1))) :=
      iB.add (integrable_finsetSum _ fun i _ => iC i)
    simp only [Gm, G]
    simp only [add_mul, Finset.sum_mul]
    rw [integral_add iBC (integrable_finsetSum _ fun j _ => iE j),
      integral_add iB (integrable_finsetSum _ fun i _ => iC i),
      integral_finsetSum _ (fun i _ => iC i), integral_finsetSum _ (fun j _ => iE j)]
  have hGm' : ∀ m : Fin c → ℤ,
      Gm m = fun x => (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), B (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) + ∑ i, (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), ((|1 - Real.exp (x (kR i))| : ℝ) : ℂ) * C i (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) + ∑ j, (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), ((‖(1 : ℂ) - Complex.exp ((x (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ ^ 2 * Real.log ‖(1 : ℂ) - Complex.exp ((x (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ : ℝ) : ℂ) * E j (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) :=
    fun m => funext (hGm m)
  have hIB : ∀ m : Fin c → ℤ, Integrable (fun x : Fin r → ℝ => (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), B (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))) := fun m =>
    (hBreg m).1.continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_of_box (f := fun x : Fin r → ℝ => (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), B (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))) R (hBreg m).2)

  have hC0 : ∀ m : Fin c → ℤ, 0 ≤ CB m + ∑ i, CC i m + ∑ j, CE j m := fun m =>
    add_nonneg (add_nonneg (hCB0 m) (Finset.sum_nonneg fun i _ => (hCC i).1 m))
      (Finset.sum_nonneg fun j _ => (hCE j).1 m)
  have hCsum : Summable fun m : Fin c → ℤ => CB m + ∑ i, CC i m + ∑ j, CE j m :=
    (hCBs.add (summable_sum fun i _ => (hCC i).2.1)).add (summable_sum fun j _ => (hCE j).2.1)
  have hxb : ∀ (m : Fin c → ℤ) (x : Fin r → ℝ), ‖Gm m x‖ ≤ (CB m + ∑ i, CC i m + ∑ j, CE j m) * ∏ k, (1 + |x k|)⁻¹ ^ 2 := by
    intro m x
    rw [hGm m x, add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (hCBx m x) ?_)) ?_)
    · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ((hCC i).2.2 m).2.2.1 x)
    · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ((hCE j).2.2 m).2.2.1 x)
  have hξb : ∀ (m : Fin c → ℤ) (ξ : Fin r → ℝ),
      ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * Gm m x‖ ≤ (CB m + ∑ i, CC i m + ∑ j, CE j m) * ∏ k, (1 + |ξ k|)⁻¹ ^ 2 := by
    intro m ξ
    have hfun : (fun x : Fin r → ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * Gm m x) = fun x =>
        Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), B (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) + ∑ i, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), ((|1 - Real.exp (x (kR i))| : ℝ) : ℂ) * C i (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) +
          ∑ j, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), ((‖(1 : ℂ) - Complex.exp ((x (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ ^ 2 * Real.log ‖(1 : ℂ) - Complex.exp ((x (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ : ℝ) : ℂ) * E j (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) := by
      funext x
      rw [hGm m x, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
    have jB : Integrable (fun x : Fin r → ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), B (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))) := integrable_xChar_mul ξ (hIB m)
    have jC : ∀ i : ιR, Integrable (fun x : Fin r → ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), ((|1 - Real.exp (x (kR i))| : ℝ) : ℂ) * C i (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))) := fun i =>
      integrable_xChar_mul ξ ((hCC i).2.2 m).2.1
    have jE : ∀ j : Fin c, Integrable (fun x : Fin r → ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), ((‖(1 : ℂ) - Complex.exp ((x (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ ^ 2 * Real.log ‖(1 : ℂ) - Complex.exp ((x (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ : ℝ) : ℂ) * E j (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))) := fun j =>
      integrable_xChar_mul ξ ((hCE j).2.2 m).2.1
    have jBC : Integrable (fun x : Fin r → ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), B (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) +
        ∑ i, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1), ((|1 - Real.exp (x (kR i))| : ℝ) : ℂ) * C i (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))))) := jB.add (integrable_finsetSum _ fun i _ => jC i)
    rw [hfun, integral_add jBC (integrable_finsetSum _ fun j _ => jE j),
      integral_add jB (integrable_finsetSum _ fun i _ => jC i),
      integral_finsetSum _ (fun i _ => jC i), integral_finsetSum _ (fun j _ => jE j),
      add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (hCBξ m ξ) ?_)) ?_)
    · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ((hCC i).2.2 m).2.2.2 ξ)
    · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ((hCE j).2.2 m).2.2.2 ξ)
  refine ⟨fun m => CB m + ∑ i, CC i m + ∑ j, CE j m, hC0, hCsum, fun m => ⟨?_, ?_, hxb m, hξb m⟩, ?_⟩
  · rw [hGm' m]
    exact ((hBreg m).1.continuous.add (continuous_finsetSum _ fun i _ => ((hCC i).2.2 m).1)).add
      (continuous_finsetSum _ fun j _ => ((hCE j).2.2 m).1)
  · rw [hGm' m]
    exact ((hIB m).add (integrable_finsetSum _ fun i _ => ((hCC i).2.2 m).2.1)).add
      (integrable_finsetSum _ fun j _ => ((hCE j).2.2 m).2.1)

  · intro p
    obtain ⟨x, θ⟩ := p
    have hsumG : Summable fun m : Fin c → ℤ => ‖Gm m x‖ := by
      refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hCsum
      exact (hxb m x).trans (mul_le_of_le_one_right (hC0 m) (prod_inv_sq_le_one x))
    have hK4 := MeasureTheory.hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable
      (fun θ' : Fin c → ℝ => G (x, θ')) (hcontG x) (fun θ' j => hperG x θ' j) (by simpa only [Gm] using hsumG) θ
    simpa only [Gm] using hK4

end S_MeasureTheory_exists_summable_forall_fourierMode_kinkWindow_productPoisson
end P2MW
export P2MW.S_MeasureTheory_exists_summable_forall_fourierMode_kinkWindow_productPoisson (solution)
