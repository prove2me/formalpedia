-- Prove2me | solution 1 for MTT.modularIntegral_integrable
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-07T13:14:27.538071+00:00
-- url     : https://prove2.me/submissions/5fc57e46-aca9-46c5-8924-bbc987875a2e

import Definitions.Def_MTT_Cohomology
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import Theorems.Thm_MTT_cuspForm_bounded_near_rational

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators MatrixGroups
open MTT.Cohomology MeasureTheory Filter UpperHalfPlane Set Asymptotics

namespace P2MMII

variable {N k : ℕ}

/-- The vertical ray over the rational point `r`. -/
def ray (r : ℚ) (t : ℝ) : ℂ := (r : ℂ) + Complex.I * t

@[simp] theorem ray_im (r : ℚ) (t : ℝ) : (ray r t).im = t := by simp [ray]

theorem hray_eq (r : ℚ) {t : ℝ} (ht : 0 < t) :
    UpperHalfPlane.ofComplex (ray r t) = ⟨ray r t, by rw [ray_im]; exact ht⟩ :=
  UpperHalfPlane.ofComplex_apply_of_im_pos _

theorem continuous_ray (r : ℚ) : Continuous (ray r) := by
  unfold ray; fun_prop

theorem continuousOn_hray (r : ℚ) :
    ContinuousOn (fun t : ℝ => UpperHalfPlane.ofComplex (ray r t)) (Ioi 0) := by
  simp only [UpperHalfPlane.ofComplex_apply_eq_ite, continuousOn_iff_continuous_domRestrict,
    continuous_induced_rng]
  exact ((continuous_ray r).comp continuous_subtype_val).congr (by simp +contextual)

theorem tendsto_hray (r : ℚ) :
    Tendsto (fun t : ℝ => UpperHalfPlane.ofComplex (ray r t)) atTop atImInfty := by
  rw [UpperHalfPlane.atImInfty, tendsto_comap_iff]
  refine Filter.tendsto_atTop_mono' _ ?_ tendsto_id
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Function.comp_apply, hray_eq r ht]
  simp [UpperHalfPlane.im]

/-- The cusp at infinity really is a cusp of `Γ₁(N)`. -/
theorem factCusp {N : ℕ} (hN : 0 < N) : Fact (IsCusp OnePoint.infty (MTT.GammaOne N)) := by
  have : NeZero N := ⟨hN.ne'⟩
  refine ⟨?_⟩
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff']
  exact ⟨1, by simp⟩

/-- The integrand of the modular integral. -/
def G (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (P : Polynomial ℂ) (r : ℚ) (t : ℝ) : ℂ :=
  f (UpperHalfPlane.ofComplex (ray r t)) * P.eval (ray r t)

theorem continuousOn_G (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (P : Polynomial ℂ) (r : ℚ) :
    ContinuousOn (G f P r) (Ioi 0) :=
  ((CuspFormClass.holo f).continuous.comp_continuousOn (continuousOn_hray r)).mul
    (P.continuous.comp (continuous_ray r)).continuousOn

/-! ### Decay at infinity -/

theorem isBigO_ray (r : ℚ) : (fun t : ℝ => ray r t) =O[atTop] fun t : ℝ => t := by
  rw [isBigO_iff]
  refine ⟨|(r : ℝ)| + 1, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have h1 : ‖ray r t‖ ≤ |(r : ℝ)| + t := by
    refine (norm_add_le _ _).trans ?_
    simp [ray, abs_of_nonneg ht0]
  have h2 : ‖t‖ = t := by rw [Real.norm_eq_abs, abs_of_nonneg ht0]
  rw [h2]
  nlinarith [abs_nonneg ((r : ℝ))]

theorem isBigO_poly (P : Polynomial ℂ) (r : ℚ) :
    (fun t : ℝ => P.eval (ray r t)) =O[atTop] fun t : ℝ => t ^ P.natDegree := by
  rw [isBigO_iff]
  refine ⟨(∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖) * (|(r : ℝ)| + 1) ^ P.natDegree, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  set B : ℝ := (|(r : ℝ)| + 1) * t with hB
  have hB1 : (1 : ℝ) ≤ B := by
    rw [hB]
    nlinarith [abs_nonneg ((r : ℝ))]
  have hbound : ‖ray r t‖ ≤ B := by
    have h1 : ‖ray r t‖ ≤ |(r : ℝ)| + t := by
      refine (norm_add_le _ _).trans ?_
      simp [ray, abs_of_nonneg ht0]
    rw [hB]
    nlinarith [abs_nonneg ((r : ℝ))]
  calc ‖P.eval (ray r t)‖
      ≤ ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ * ‖ray r t‖ ^ i := by
        rw [Polynomial.eval_eq_sum_range]
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun i _ => by rw [norm_mul, norm_pow]
    _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ * B ^ P.natDegree := by
        refine Finset.sum_le_sum fun i hi => ?_
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact le_trans (pow_le_pow_left₀ (norm_nonneg _) hbound i)
          (pow_le_pow_right₀ hB1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    _ = (∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖) *
          (|(r : ℝ)| + 1) ^ P.natDegree * ‖t ^ P.natDegree‖ := by
        rw [← Finset.sum_mul, hB, mul_pow, Real.norm_eq_abs, abs_pow,
          abs_of_nonneg ht0]
        ring

theorem isBigO_G (hN : 0 < N) (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (P : Polynomial ℂ) (r : ℚ) :
    ∃ b : ℝ, 0 < b ∧ G f P r =O[atTop] fun t : ℝ => Real.exp (-b * t) := by
  have : NeZero N := ⟨hN.ne'⟩
  have := factCusp hN
  obtain ⟨c, hc, hO⟩ := CuspFormClass.exp_decay_atImInfty' f
  refine ⟨c / 2, by linarith, ?_⟩
  have h1 : (fun t : ℝ => f (UpperHalfPlane.ofComplex (ray r t))) =O[atTop]
      fun t : ℝ => Real.exp (-c * t) := by
    refine (hO.comp_tendsto (tendsto_hray r)).congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [Function.comp_apply, hray_eq r ht]
    simp [UpperHalfPlane.im]
  have h2 : (fun t : ℝ => P.eval (ray r t)) =O[atTop] fun t : ℝ => Real.exp (c / 2 * t) :=
    (isBigO_poly P r).trans (isLittleO_pow_exp_pos_mul_atTop P.natDegree
      (by linarith : (0:ℝ) < c / 2)).isBigO
  refine ((h1.mul h2).congr' EventuallyEq.rfl (Eventually.of_forall fun t => ?_))
  show Real.exp (-c * t) * Real.exp (c / 2 * t) = Real.exp (-(c / 2) * t)
  rw [← Real.exp_add]
  ring_nf

/-! ### The two halves -/

theorem integrableOn_far (hN : 0 < N) (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (P : Polynomial ℂ) (r : ℚ) : IntegrableOn (G f P r) (Ioi (1 : ℝ)) := by
  obtain ⟨b, hb, hO⟩ := isBigO_G hN f P r
  have hloc : LocallyIntegrableOn (G f P r) (Ici (1 : ℝ)) :=
    ((continuousOn_G f P r).mono
      (show Ici (1:ℝ) ⊆ Ioi 0 from fun t ht =>
        Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one (Set.mem_Ici.mp ht)))).locallyIntegrableOn
      measurableSet_Ici
  have hint : IntegrableOn (G f P r) (Ici (1 : ℝ)) :=
    hloc.integrableOn_of_isBigO_atTop hO
      ⟨Ioi (0 : ℝ), Ioi_mem_atTop 0, exp_neg_integrableOn_Ioi 0 hb⟩
  exact hint.mono_set Ioi_subset_Ici_self

theorem integrableOn_near (hN : 0 < N) (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (P : Polynomial ℂ) (r : ℚ) : IntegrableOn (G f P r) (Ioc (0 : ℝ) 1) := by
  obtain ⟨Cf, hCf⟩ := MTT.cuspForm_bounded_near_rational hN f r
  obtain ⟨Cp, hCp⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    (f := fun t : ℝ => P.eval (ray r t)) (P.continuous.comp (continuous_ray r)).continuousOn
  have hmeas : AEStronglyMeasurable (G f P r) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((continuousOn_G f P r).mono
      (show Ioc (0:ℝ) 1 ⊆ Ioi 0 from fun t ht => ht.1)).aestronglyMeasurable measurableSet_Ioc
  refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => Cf * Cp) (integrable_const _) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have h1 : ‖f (UpperHalfPlane.ofComplex (ray r t))‖ ≤ Cf := hCf t ht.1 ht.2
  have h2 : ‖P.eval (ray r t)‖ ≤ Cp := hCp t ⟨le_of_lt ht.1, ht.2⟩
  calc ‖G f P r t‖ = ‖f (UpperHalfPlane.ofComplex (ray r t))‖ * ‖P.eval (ray r t)‖ := norm_mul _ _
    _ ≤ Cf * Cp := by
        refine mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)

end P2MMII

open P2MMII in
theorem solution {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (P : Polynomial ℂ) (r : ℚ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => f (UpperHalfPlane.ofComplex ((r : ℂ) + Complex.I * t)) *
        P.eval ((r : ℂ) + Complex.I * t))
      (Set.Ioi (0 : ℝ)) MeasureTheory.volume := by
  have hG : (fun t : ℝ => f (UpperHalfPlane.ofComplex ((r : ℂ) + Complex.I * t)) *
      P.eval ((r : ℂ) + Complex.I * t)) = G f P r := rfl
  rw [hG, ← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0:ℝ) ≤ 1)]
  exact (integrableOn_near hN f P r).union (integrableOn_far hN f P r)
