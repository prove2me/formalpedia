-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_character_logderiv_growth_constant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:04:52.821108+00:00
-- url     : https://prove2.me/submissions/ff179841-4a07-48db-914a-93003b8e9238

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_mrtCharacterNormalized_logderiv

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Basic
namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations







@[simp] theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n := by
  simp [liouville, ArithmeticFunction.liouville_apply_mul]

@[simp] theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouville
  exact_mod_cast h





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.EulerMaclaurin
namespace Erdos970

open _root_.Finset _root_.Interval _root_.MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MertensClassical
namespace Erdos970


namespace Real

open _root_.Real _root_.Filter _root_.Asymptotics



end Real

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology




end Issue1584

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open ArithmeticFunction hiding log













































attribute [fun_prop] measurable_from_top












section
open _root_.MeasureTheory _root_.Set

namespace LogZetaInteg



@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]






end LogZetaInteg
end











section
open _root_.MeasureTheory _root_.Set








end












































end Mertens

end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterCenterBounds
namespace OAI

/-! The Mobius inverse bounds the reciprocal L-function on Re(s)=2
uniformly in the modulus. Combining this with the q-dependent Abel bound
gives growth of the normalized nonprincipal character L-function on a
fixed disk. No zero-free region is asserted here. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.ArithmeticFunction
open scoped _root_.BigOperators _root_.Classical _root_.LSeries.notation _root_.ArithmeticFunction.Moebius

variable {q : ℕ} [NeZero q]


lemma mrtCharacterInverseConstant_pos : 0 < mrtCharacterInverseConstant := by
  unfold mrtCharacterInverseConstant
  have : 0 ≤ ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (2 : ℂ) n‖ :=
    tsum_nonneg fun _ => norm_nonneg _
  linarith








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.StrongPNT.Erdos970.PNT2_LogDerivative
namespace Erdos970




open _root_.Filter _root_.Metric _root_.Set _root_.Bornology _root_.Function


open _root_.Classical

lemma lem_frho_zero (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (_hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    f ρ = 0 := h_rho_in_KfR1.2

lemma lem_m_rho_is_nat (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hR_lt_1 : R < 1) :
    ∀ (ρ : ℂ) (_h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f),
    analyticOrderAt f ρ ≠ ⊤ := by
  intro ρ h_rho_in_KfR1
                                           
  have hρ_closed_R1 : ρ ∈ Metric.closedBall (0 : ℂ) R1 := h_rho_in_KfR1.1
                                    
  have hR1_le_R : R1 ≤ R := by linarith
  have hR1_lt_one : R1 < 1 := by linarith
                       
  have hρ_ball1 : ρ ∈ Metric.ball (0 : ℂ) 1 := by
    have hdist_le : dist ρ (0 : ℂ) ≤ R1 := (Metric.mem_closedBall.mp hρ_closed_R1)
    have hdist_lt : dist ρ (0 : ℂ) < 1 := by linarith
    simpa [Metric.mem_ball] using hdist_lt
                       
  have hf_at_ρ : AnalyticAt ℂ f ρ := by
                                      
    have hsubset : Metric.closedBall (0 : ℂ) R1 ⊆ Metric.closedBall (0 : ℂ) 1 :=
      Metric.closedBall_subset_closedBall (le_of_lt hR1_lt_one)
    have hρ_closed1 : ρ ∈ Metric.closedBall (0 : ℂ) 1 := hsubset hρ_closed_R1
    exact h_f_analytic ρ hρ_closed1
                                                    
  by_contra htop
                                                           
  have h_eventually_zero : ∀ᶠ z in nhds ρ, f z = 0 := by
    have h_equiv : (analyticOrderAt f ρ = ⊤ ↔ ∀ᶠ z in nhds ρ, f z = 0) := by
      simp [analyticOrderAt, hf_at_ρ]
    exact h_equiv.mp (by simpa using htop)
                                                     
  have hf_on_ball : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hz' : z ∈ Metric.closedBall (0 : ℂ) 1 :=
      (Metric.ball_subset_closedBall : Metric.ball (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 1) hz
    exact h_f_analytic z hz'
                                  
  have h_preconn : IsPreconnected (Metric.ball (0 : ℂ) 1) :=
    (Metric.isConnected_ball (by exact (zero_lt_one : (0 : ℝ) < 1))).isPreconnected
                                                  
  have h_eqOn_zero : Set.EqOn f 0 (Metric.ball (0 : ℂ) 1) :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hf_on_ball h_preconn hρ_ball1
      h_eventually_zero
                                 
  have h0_in_ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simp [Metric.mem_ball]
  have : f 0 = 0 := by
    have h := h_eqOn_zero h0_in_ball
    simpa [Pi.zero_apply] using h
  exact h_f_nonzero_at_zero this

lemma analyticOrderAt_ge_one_of_zero (f : ℂ → ℂ) (z : ℂ) (hf : AnalyticAt ℂ f z) (hz : f z = 0) (hfinite : analyticOrderAt f z ≠ ⊤) : analyticOrderAt f z ≥ 1 := by
                                                                 
  have h_order_ne_zero : analyticOrderAt f z ≠ 0 := by
    intro h_order_zero
                                                              
    have h_f_ne_zero : f z ≠ 0 := by
      rw [← AnalyticAt.analyticOrderAt_eq_zero hf]
      exact h_order_zero
                                    
    exact h_f_ne_zero hz
                                                                      
  cases' h : analyticOrderAt f z with n
  ·                                 
                               
    rw [h] at hfinite
    exact False.elim (hfinite rfl)
  ·                                                 

    rw [h] at h_order_ne_zero
    have n_ne_zero : n ≠ 0 := by
      intro n_zero
      rw [n_zero, Nat.cast_zero] at h_order_ne_zero
      exact h_order_ne_zero rfl
                                 
    have n_ge_one : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr n_ne_zero
                            
    exact Nat.cast_le.mpr n_ge_one

lemma lem_m_rho_ge_1 (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hR_lt_1 : R < 1) :
    ∀ (ρ : ℂ) (_h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f),
    analyticOrderAt f ρ ≥ 1 := by
  intro ρ h_rho_in_KfR1
                                                     
  have h_f_rho_zero : f ρ = 0 := lem_frho_zero R R1 hR1_pos hR1_lt_R f h_f_analytic ρ h_rho_in_KfR1
                                                        
  have h_order_finite : analyticOrderAt f ρ ≠ ⊤ := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 ρ h_rho_in_KfR1
                       
  have h_f_analytic_at_rho : AnalyticAt ℂ f ρ := by
    apply h_f_analytic
                                            
    have h_R1_lt_1 : R1 < 1 := by linarith
    have h_rho_in_R1 : ρ ∈ Metric.closedBall 0 R1 := h_rho_in_KfR1.1
    exact Metric.closedBall_subset_closedBall (le_of_lt h_R1_lt_1) h_rho_in_R1
                                                                          
  exact analyticOrderAt_ge_one_of_zero f ρ h_f_analytic_at_rho h_f_rho_zero h_order_finite

































































































variable {R R1 r B : ℝ} {f : ℂ → ℂ} {h_σ : ℂ → (ℂ → ℂ)}
variable (hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
variable (hR1_pos : 0 < R1)
variable (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
variable (h_f_zero : f 0 = 1)
variable (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
variable (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)


























































































end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterZeroTerms
namespace OAI

/-! Transfer the normalized disk expansion back to the actual L-functions.
Every zero in the finite disk lies left of the line of evaluation, so its
logarithmic-derivative contribution has nonnegative real part.
-/

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.BigOperators _root_.Classical

variable {q : ℕ} [NeZero q]



lemma mrtCharacterPhysicalPoint_real (σ t : ℝ) :
    mrtCharacterPhysicalPoint t (mrtCharacterRealDiskPoint σ) =
      (σ : ℂ) + Complex.I * (t : ℂ) := by
  unfold mrtCharacterPhysicalPoint mrtCharacterRealDiskPoint
  push_cast
  ring

lemma mrtCharacterNormalizedLFunction_deriv (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) (z : ℂ) :
    deriv (mrtCharacterNormalizedLFunction χ t) z =
      (deriv (DirichletCharacter.LFunction χ) (mrtCharacterPhysicalPoint t z) * (3 / 2 : ℂ)) /
        DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (t : ℂ)) := by
  have ha : HasDerivAt (mrtCharacterPhysicalPoint t) (3 / 2 : ℂ) z := by
    exact (hasDerivAt_const_mul (3 / 2 : ℂ)).const_add
      ((2 : ℂ) + Complex.I * (t : ℂ))
  exact (((DirichletCharacter.differentiable_LFunction hχ _).hasDerivAt.comp z ha).div_const
    (DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (t : ℂ)))).deriv

lemma mrtCharacterNormalized_logderiv_eq (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) (z : ℂ)
    (hn : DirichletCharacter.LFunction χ (mrtCharacterPhysicalPoint t z) ≠ 0) :
    deriv (mrtCharacterNormalizedLFunction χ t) z / mrtCharacterNormalizedLFunction χ t z =
      (3 / 2 : ℂ) *
        (deriv (DirichletCharacter.LFunction χ) (mrtCharacterPhysicalPoint t z) /
          DirichletCharacter.LFunction χ (mrtCharacterPhysicalPoint t z)) := by
  have hc : DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (t : ℂ)) ≠ 0 :=
    χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by norm_num)
  rw [mrtCharacterNormalizedLFunction_deriv χ hχ]
  change (_ / _) / (DirichletCharacter.LFunction χ (mrtCharacterPhysicalPoint t z) / _) = _
  field_simp [hn, hc]

lemma mrtCharacterNormalizedZeros_physical_zero (χ : DirichletCharacter ℂ q)
    (t : ℝ) {ρ : ℂ} (hρ : ρ ∈ mrtCharacterNormalizedZeros χ t) :
    DirichletCharacter.LFunction χ (mrtCharacterPhysicalPoint t ρ) = 0 := by
  have hzero : mrtCharacterNormalizedLFunction χ t ρ = 0 := hρ.2
  have hc : DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (t : ℂ)) ≠ 0 :=
    χ.LFunction_ne_zero_of_one_le_re (Or.inr (by
      intro h; have := congrArg Complex.re h; norm_num at this)) (by norm_num)
  exact (div_eq_zero_iff.mp hzero).resolve_right hc

lemma mrtCharacterNormalizedZeros_re (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) {ρ : ℂ} (hρ : ρ ∈ mrtCharacterNormalizedZeros χ t) :
    ρ.re < -(2 / 3 : ℝ) := by
  by_contra! h
  have hs : 1 ≤ (mrtCharacterPhysicalPoint t ρ).re := by
    norm_num [mrtCharacterPhysicalPoint, Complex.mul_re]
    linarith
  exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) hs
    (mrtCharacterNormalizedZeros_physical_zero χ t hρ)

lemma mrtCharacterRealDiskPoint_norm {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    ‖mrtCharacterRealDiskPoint σ‖ ≤ 3 / 4 := by
  rw [mrtCharacterRealDiskPoint, Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith

lemma mrtCharacter_zeroTerm_re_nonneg (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) {σ : ℝ} (hσ : 1 < σ)
    {ρ : ℂ} (hρ : ρ ∈ mrtCharacterNormalizedZeros χ t) :
    0 ≤ (((analyticOrderAt (mrtCharacterNormalizedLFunction χ t) ρ).toNat : ℂ) /
      (mrtCharacterRealDiskPoint σ - ρ)).re := by
  have hr := mrtCharacterNormalizedZeros_re χ hχ t hρ
  have hd : 0 ≤ (mrtCharacterRealDiskPoint σ - ρ).re := by
    simp only [Complex.sub_re, mrtCharacterRealDiskPoint, Complex.ofReal_re]
    linarith
  rw [Complex.div_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hd) (Complex.normSq_nonneg _)

/-- A logarithmic-derivative upper bound to the right of one, obtained by
dropping the nonnegative zero terms from the actual finite expansion. -/
theorem mrtCharacter_neg_logderiv_re_le (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (t : ℂ)) /
      DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))).re ≤
        (2 / 3 : ℝ) * mrtCharacterLogDerivativeConstant *
          Real.log ((2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4)) := by
  let z := mrtCharacterRealDiskPoint σ
  have hp : DirichletCharacter.LFunction χ (mrtCharacterPhysicalPoint t z) ≠ 0 := by
    rw [mrtCharacterPhysicalPoint_real]
    exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by simpa using hσ.le)
  have hn : mrtCharacterNormalizedLFunction χ t z ≠ 0 := by
    exact div_ne_zero hp (χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by norm_num))
  have he := mrtCharacterNormalized_logderiv χ hχ t (mrtCharacterRealDiskPoint_norm hσ hσ2) hn
  have hre := (Complex.abs_re_le_norm _).trans he
  have hs : 0 ≤ ∑ ρ ∈ (mrtCharacterNormalizedZeros_finite χ hχ t).toFinset,
      (((analyticOrderAt (mrtCharacterNormalizedLFunction χ t) ρ).toNat : ℂ) / (z - ρ)).re := by
    apply sum_nonneg
    intro ρ hρ
    exact mrtCharacter_zeroTerm_re_nonneg χ hχ t hσ
      ((mrtCharacterNormalizedZeros_finite χ hχ t).mem_toFinset.mp hρ)
  rw [Complex.sub_re, Complex.re_sum] at hre
  have hlow := (abs_le.mp hre).1
  rw [mrtCharacterNormalized_logderiv_eq χ hχ t z hp, mrtCharacterPhysicalPoint_real] at hlow
  norm_num [Complex.mul_re] at hlow
  simp only [neg_div, Complex.neg_re]
  nlinarith

lemma mrtCharacter_zero_multiplicity_pos (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) {ρ : ℂ} (hρ : ρ ∈ mrtCharacterNormalizedZeros χ t) :
    1 ≤ (analyticOrderAt (mrtCharacterNormalizedLFunction χ t) ρ).toNat := by
  have hf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      AnalyticAt ℂ (mrtCharacterNormalizedLFunction χ t) z := by
    intro z _
    exact (mrtCharacterNormalizedLFunction_differentiable χ hχ t).analyticAt z
  have hf0 : mrtCharacterNormalizedLFunction χ t 0 ≠ 0 := by
    rw [mrtCharacterNormalizedLFunction_zero]
    exact one_ne_zero
  have hfinite := Erdos970.lem_m_rho_is_nat (15 / 16) (7 / 8)
    (by norm_num) (by norm_num) (mrtCharacterNormalizedLFunction χ t) hf hf0
    (by norm_num) ρ hρ
  have hpos := Erdos970.lem_m_rho_ge_1 (15 / 16) (7 / 8)
    (by norm_num) (by norm_num) (mrtCharacterNormalizedLFunction χ t) hf hf0
    (by norm_num) ρ hρ
  simpa using ENat.toNat_le_toNat hpos hfinite

lemma mrtCharacter_real_zero_mem (χ : DirichletCharacter ℂ q)
    (t : ℝ) {β : ℝ} (hβ : 3 / 4 ≤ β) (hβ1 : β ≤ 1)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) = 0) :
    mrtCharacterRealDiskPoint β ∈ mrtCharacterNormalizedZeros χ t := by
  have hn : ‖mrtCharacterRealDiskPoint β‖ ≤ 7 / 8 := by
    rw [mrtCharacterRealDiskPoint, Complex.norm_real, Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith
  refine ⟨by simpa using hn, ?_⟩
  change DirichletCharacter.LFunction χ
    (mrtCharacterPhysicalPoint t (mrtCharacterRealDiskPoint β)) / _ = 0
  rw [mrtCharacterPhysicalPoint_real, hzero, zero_div]

/-- A zero at height `t` contributes its full reciprocal distance; the
other zeros have nonnegative real contributions. -/
lemma mrtCharacter_zero_sum_lower (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (t : ℝ) {σ β : ℝ} (hσ : 1 < σ) (hβ : 3 / 4 ≤ β) (hβ1 : β ≤ 1)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) = 0) :
    (3 / 2 : ℝ) / (σ - β) ≤
      ∑ ρ ∈ (mrtCharacterNormalizedZeros_finite χ hχ t).toFinset,
        (((analyticOrderAt (mrtCharacterNormalizedLFunction χ t) ρ).toNat : ℂ) /
          (mrtCharacterRealDiskPoint σ - ρ)).re := by
  let w := mrtCharacterRealDiskPoint β
  have hw := mrtCharacter_real_zero_mem χ t hβ hβ1 hzero
  have hm := mrtCharacter_zero_multiplicity_pos χ hχ t hw
  have hd0 : 0 < σ - β := by linarith
  have hd : 0 < (2 / 3 : ℝ) * (σ - β) := mul_pos (by norm_num) hd0
  have hdiff : mrtCharacterRealDiskPoint σ - w =
      (((2 / 3 : ℝ) * (σ - β) : ℝ) : ℂ) := by
    dsimp [w, mrtCharacterRealDiskPoint]
    push_cast
    ring
  have hterm : (3 / 2 : ℝ) / (σ - β) ≤
      (((analyticOrderAt (mrtCharacterNormalizedLFunction χ t) w).toNat : ℂ) /
        (mrtCharacterRealDiskPoint σ - w)).re := by
    rw [hdiff]
    change (3 / 2 : ℝ) / (σ - β) ≤
      ((((analyticOrderAt (mrtCharacterNormalizedLFunction χ t) w).toNat : ℝ) : ℂ) /
        (((2 / 3 : ℝ) * (σ - β) : ℝ) : ℂ)).re
    rw [← Complex.ofReal_div, Complex.ofReal_re]
    calc
      _ = 1 / ((2 / 3 : ℝ) * (σ - β)) := by field_simp [ne_of_gt hd0]
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hm) hd.le
  exact hterm.trans (single_le_sum
    (fun ρ hρ => mrtCharacter_zeroTerm_re_nonneg χ hχ t hσ
      ((mrtCharacterNormalizedZeros_finite χ hχ t).mem_toFinset.mp hρ))
    ((mrtCharacterNormalizedZeros_finite χ hχ t).mem_toFinset.mpr hw))

/-- The one-zero upper bound, with its negative reciprocal term retained. -/
theorem mrtCharacter_neg_logderiv_re_le_of_zero (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) {σ β : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2)
    (hβ : 3 / 4 ≤ β) (hβ1 : β ≤ 1)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) = 0) :
    (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (t : ℂ)) /
      DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))).re ≤
        (2 / 3 : ℝ) * mrtCharacterLogDerivativeConstant *
          Real.log ((2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4)) - 1 / (σ - β) := by
  let z := mrtCharacterRealDiskPoint σ
  have hp : DirichletCharacter.LFunction χ (mrtCharacterPhysicalPoint t z) ≠ 0 := by
    rw [mrtCharacterPhysicalPoint_real]
    exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by simpa using hσ.le)
  have hn : mrtCharacterNormalizedLFunction χ t z ≠ 0 :=
    div_ne_zero hp (χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by norm_num))
  have he := mrtCharacterNormalized_logderiv χ hχ t (mrtCharacterRealDiskPoint_norm hσ hσ2) hn
  have hre := (Complex.abs_re_le_norm _).trans he
  have hs := mrtCharacter_zero_sum_lower χ hχ t hσ hβ hβ1 hzero
  have hfrac : (3 / 2 : ℝ) / (σ - β) = (3 / 2 : ℝ) * (1 / (σ - β)) := by ring
  rw [hfrac] at hs
  rw [Complex.sub_re, Complex.re_sum] at hre
  have hlow := (abs_le.mp hre).1
  rw [mrtCharacterNormalized_logderiv_eq χ hχ t z hp, mrtCharacterPhysicalPoint_real] at hlow
  norm_num [Complex.mul_re] at hlow
  simp only [neg_div, Complex.neg_re]
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterLogGrowth
namespace OAI

/-! One absolute constant in the nonprincipal disk bounds, with all
modulus and height dependence kept in log(q*(abs(t)+2)). -/

namespace TwoPointCorrelations


lemma mrt_character_height_split (q : ℕ) [NeZero q] (t : ℝ) :
    mrtCharacterHeight q t=Real.log (q:ℝ)+Real.log (|t|+2) := by
  exact Real.log_mul (by exact_mod_cast NeZero.ne q) (by positivity)

lemma mrt_character_height_ge (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log (|t|+2) ≤ mrtCharacterHeight q t := by
  rw [mrt_character_height_split]
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  linarith [Real.log_nonneg hq]




lemma mrtCharacterLogDerivativeConstant_pos : 0 < mrtCharacterLogDerivativeConstant := by
  have hl : 0 < Real.log ((15/16:ℝ)/(7/8)) := Real.log_pos (by norm_num)
  unfold mrtCharacterLogDerivativeConstant
  positivity

lemma mrt_character_log_disk_growth (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log ((2*q:ℝ)*mrtCharacterInverseConstant*(|t|+4)) ≤
      (Real.log (4*mrtCharacterInverseConstant)/Real.log 2+1)*mrtCharacterHeight q t := by
  have hK : 1 ≤ mrtCharacterInverseConstant := by
    unfold mrtCharacterInverseConstant
    exact le_add_of_nonneg_right (tsum_nonneg (fun _ => norm_nonneg _))
  have hq : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  have hA : 0 < 4*mrtCharacterInverseConstant := by positivity
  have hlogA : 0 ≤ Real.log (4*mrtCharacterInverseConstant) :=
    Real.log_nonneg (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hH : Real.log 2 ≤ mrtCharacterHeight q t :=
    (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])).trans
      (mrt_character_height_ge q t)
  have hr : Real.log (4*mrtCharacterInverseConstant) ≤
      (Real.log (4*mrtCharacterInverseConstant)/Real.log 2)*mrtCharacterHeight q t := by
    calc
      _ = (Real.log (4*mrtCharacterInverseConstant)/Real.log 2)*Real.log 2 :=
        (div_mul_cancel₀ _ hlog2.ne').symm
      _  ≤  _ := mul_le_mul_of_nonneg_left hH (div_nonneg hlogA hlog2.le)
  have hc : (2*q:ℝ)*mrtCharacterInverseConstant*(|t|+4) ≤
      (4*mrtCharacterInverseConstant)*((q:ℝ)*(|t|+2)) := by
    calc
      _ = ((q:ℝ)*mrtCharacterInverseConstant)*(2*(|t|+4)) := by ring
      _  ≤  ((q:ℝ)*mrtCharacterInverseConstant)*(4*(|t|+2)) :=
        mul_le_mul_of_nonneg_left (by linarith [abs_nonneg t]) (by positivity)
      _ = _ := by ring
  calc
    _  ≤  Real.log ((4*mrtCharacterInverseConstant)*((q:ℝ)*(|t|+2))) :=
      Real.log_le_log (by positivity) hc
    _ = Real.log (4*mrtCharacterInverseConstant)+mrtCharacterHeight q t :=
      Real.log_mul hA.ne' (by positivity)
    _  ≤  _ := by nlinarith

theorem mrt_character_logderiv_growth_constant : ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℕ) [NeZero q], ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ t σ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv (DirichletCharacter.LFunction χ) ((σ:ℂ)+Complex.I*(t:ℂ))/
        DirichletCharacter.LFunction χ ((σ:ℂ)+Complex.I*(t:ℂ))).re ≤
          C*mrtCharacterHeight q t ∧
      ∀ β : ℝ, 3/4 ≤ β → β ≤ 1 →
        DirichletCharacter.LFunction χ ((β:ℂ)+Complex.I*(t:ℂ))=0 →
        (-deriv (DirichletCharacter.LFunction χ) ((σ:ℂ)+Complex.I*(t:ℂ))/
          DirichletCharacter.LFunction χ ((σ:ℂ)+Complex.I*(t:ℂ))).re ≤
            C*mrtCharacterHeight q t-1/(σ-β) := by
  let C := (2/3:ℝ)*mrtCharacterLogDerivativeConstant*
    (Real.log (4*mrtCharacterInverseConstant)/Real.log 2+1)
  have hC : 0 < C := by
    have hD := mrtCharacterLogDerivativeConstant_pos
    have hK := mrtCharacterInverseConstant_pos
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hK1 : 1 ≤ mrtCharacterInverseConstant := by
      unfold mrtCharacterInverseConstant
      exact le_add_of_nonneg_right (tsum_nonneg (fun _ => norm_nonneg _))
    have hlogK : 0 ≤ Real.log (4*mrtCharacterInverseConstant) :=
      Real.log_nonneg (by linarith)
    dsimp only [C]
    positivity
  refine ⟨C,hC,?_⟩
  intro q _ χ hχ t σ hσ hσ2
  have hE : (2/3:ℝ)*mrtCharacterLogDerivativeConstant*
      Real.log ((2*q:ℝ)*mrtCharacterInverseConstant*(|t|+4)) ≤ C*mrtCharacterHeight q t := by
    dsimp only [C]
    calc
      _  ≤  ((2/3:ℝ)*mrtCharacterLogDerivativeConstant)*
          ((Real.log (4*mrtCharacterInverseConstant)/Real.log 2+1)*mrtCharacterHeight q t) :=
        mul_le_mul_of_nonneg_left (mrt_character_log_disk_growth q t)
          (mul_nonneg (by norm_num) mrtCharacterLogDerivativeConstant_pos.le)
      _ = _ := by ring
  refine ⟨(mrtCharacter_neg_logderiv_re_le χ hχ t hσ hσ2).trans hE,?_⟩
  intro β hβ hβ1 hzero
  exact (mrtCharacter_neg_logderiv_re_le_of_zero χ hχ t hσ hσ2 hβ hβ1 hzero).trans
    (sub_le_sub_right hE _)

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_character_logderiv_growth_constant := @OAI.TwoPointCorrelations.mrt_character_logderiv_growth_constant
