-- Prove2me | solution 1 for HermiteLaptop.MaxAgree.eq_8_9
-- status  : ACCEPTED   (prove)
-- author  : @hypercube
-- created : 2026-11-18T15:55:01.521244+00:00
-- url     : https://prove2.me/submissions/e64b6d72-aaba-4389-bd66-a9d2cc443aa6

import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_8
import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_9
import Definitions.Def_HermiteLaptop_MaxAgree_KSpokes
import Definitions.Def_HermiteLaptop_MaxAgree_Hermite

set_option autoImplicit false

/- Endpoints.lean -/
section
open MeasureTheory ProbabilityTheory Finset
open scoped RealInnerProductSpace
namespace HermiteLaptop.MaxAgree
open PrivateAgnosticHalfspace
local notation "G" => PrivateAgnosticHalfspace.Gaussian.Vec

/-- Parseval for indicators of two measurable Gaussian cells. -/
theorem cell_pair_parseval (d : ℕ) (A B : Set (G d)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    HasSum (fun κ : Fin d → ℕ =>
      (∫ x in A, Gaussian.hermite d κ x ∂Gaussian.gaussian d) *
      (∫ x in B, Gaussian.hermite d κ x ∂Gaussian.gaussian d))
      (∫ x, A.indicator (fun _ => (1:ℝ)) x * B.indicator (fun _ => (1:ℝ)) x ∂Gaussian.gaussian d) := by
  let μ := Gaussian.gaussian d
  let : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure (stdGaussian (G d)))
  obtain ⟨b, hb⟩ := (Gaussian.lemma_B_8 d).2.2.1
  let F (S : Set (G d)) (hS : MeasurableSet S) := indicatorConstLp 2 hS (measure_ne_top μ S) (1:ℝ)
  have hF (S : Set (G d)) (hS : MeasurableSet S) :
      (fun x => F S hS x) =ᵐ[μ] S.indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
  have hcoeff (S : Set (G d)) (hS : MeasurableSet S) (κ : Fin d → ℕ) :
      ⟪F S hS, b κ⟫ = ∫ x in S, Gaussian.hermite d κ x ∂μ := by
    rw [L2.inner_indicatorConstLp_eq_setIntegral_inner ℝ (b κ) hS (1:ℝ) (measure_ne_top μ S)]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (μ := μ) (hb κ)] with x hx
    simp [hx]
  have hinner : ⟪F A hA, F B hB⟫ =
      ∫ x, A.indicator (fun _ => (1:ℝ)) x * B.indicator (fun _ => (1:ℝ)) x ∂μ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hF A hA, hF B hB] with x hx hy
    simp [hx, hy, mul_comm]
  rw [← hinner]
  refine (b.hasSum_inner_mul_inner (F A hA) (F B hB)).congr_fun fun κ => ?_
  rw [real_inner_comm (F B hB) (b κ), hcoeff, hcoeff]

private theorem hermNorm_reflect (n : ℕ) (x : ℝ) :
    AMPLowDeg.RankOne.hermNorm n (-x) = (-1:ℝ)^n * AMPLowDeg.RankOne.hermNorm n x := by
  let P := (Polynomial.hermite n).map (Int.castRingHom ℝ)
  have he : P.eval (-x) = (-1:ℝ)^n * P.eval x := by
    simp only [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
    apply sum_congr rfl
    intro j hj
    have hpar : Even n ↔ Even j := by
      apply Nat.even_add.mp
      by_contra h
      have hzero := Polynomial.coeff_hermite_of_odd_add (Nat.not_even_iff_odd.mp h)
      exact Polynomial.mem_support_iff.mp hj (by simp [P, Polynomial.coeff_map, hzero])
    rw [show -x = (-1:ℝ)*x by ring, mul_pow, neg_one_pow_congr hpar]
    ring
  change P.eval (-x) / _ = (-1:ℝ)^n * (P.eval x / _)
  rw [he, mul_div_assoc]

private theorem tensorHermite_reflect (d : ℕ) (κ : Fin d → ℕ) (x : G d) :
    Gaussian.hermite d κ (-x) = (-1:ℝ)^Gaussian.degree κ * Gaussian.hermite d κ x := by
  change (∏ i, AMPLowDeg.RankOne.hermNorm (κ i) (-(x i))) = _
  simp_rw [hermNorm_reflect, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rfl

theorem cell_endpoint_hasSum (d : ℕ) (A : Set (G d)) (hA : MeasurableSet A) (ρ : ℝ)
    (hρ : ρ=1 ∨ ρ=(-1)) :
    HasSum (fun κ : Fin d → ℕ => ρ^Gaussian.degree κ * (∫ x in A, Gaussian.hermite d κ x ∂Gaussian.gaussian d)^2)
      (∫ x, A.indicator (fun _ => (1:ℝ)) x * A.indicator (fun _ => (1:ℝ)) (ρ • x) ∂Gaussian.gaussian d) := by
  rcases hρ with rfl | rfl
  · simpa [sq] using cell_pair_parseval d A A hA hA
  let N := LinearIsometryEquiv.neg ℝ (E := G d)
  let B := (fun x : G d => -x) ⁻¹' A
  have hB : MeasurableSet B := measurable_neg hA
  have hN : MeasurePreserving (fun x : G d => -x) (Gaussian.gaussian d) (Gaussian.gaussian d) :=
    ⟨measurable_neg, stdGaussian_map N⟩
  have hcoeff (κ : Fin d → ℕ) : (∫ x in B, Gaussian.hermite d κ x ∂Gaussian.gaussian d) =
      (-1:ℝ)^Gaussian.degree κ * ∫ x in A, Gaussian.hermite d κ x ∂Gaussian.gaussian d := by
    have hh := hN.setIntegral_preimage_emb N.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      (fun x => Gaussian.hermite d κ (-x)) A
    simp only [neg_neg] at hh
    rw [hh]
    simp only [tensorHermite_reflect, integral_const_mul]
  have hcell (x : G d) : B.indicator (fun _ => (1:ℝ)) x = A.indicator (fun _ => (1:ℝ)) (-x) := by
    by_cases hx : -x ∈ A
    · simp [B, hx]
    · simp [B, hx]
  simp only [neg_one_smul]
  have hp := cell_pair_parseval d A B hA hB
  simp only [hcell] at hp
  refine hp.congr_fun fun κ => ?_
  rw [hcoeff]
  ring

end HermiteLaptop.MaxAgree
end

/- MehlerChange.lean -/
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace HermiteLaptop.MaxAgree
open PrivateAgnosticHalfspace.Gaussian (Vec gaussian)

private noncomputable def gd (d : ℕ) (x : Vec d) : ℝ :=
  (Real.sqrt (2*Real.pi))⁻¹ ^ d * Real.exp (-‖x‖^2/2)

private theorem piDensity (d : ℕ) :
    (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) =
      (volume : Measure (Fin d → ℝ)).withDensity (fun z => ENNReal.ofReal
        (∏ i, gaussianPDFReal 0 1 (z i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi, Measure.restrict_pi_pi]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod (fun i => (integrable_gaussianPDFReal 0 1).integrableOn))
    (ae_of_all _ (fun x => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg 0 1 (x i))))]
  rw [integral_fintype_prod_eq_prod (fun (_ : Fin d) x => gaussianPDFReal 0 1 x)]
  simp_rw [gaussianReal_apply_eq_integral _ one_ne_zero]
  rw [ENNReal.ofReal_prod_of_nonneg]
  intro i _
  exact integral_nonneg (gaussianPDFReal_nonneg _ _)

private theorem gd_toLp (d : ℕ) (u : Fin d → ℝ) :
    gd d (WithLp.toLp 2 u) = ∏ i, gaussianPDFReal 0 1 (u i) := by
  simp only [gd, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [← Finset.sum_div, ← Finset.sum_neg_distrib]

private theorem gd_integral {d : ℕ} (f : Vec d → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂gaussian d) = ∫ x, gd d x * f x := by
  rw [gaussian, ← map_pi_eq_stdGaussian, integral_map (by fun_prop) hf.aestronglyMeasurable,
    piDensity]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _]
  rw [← (PiLp.volume_preserving_toLp (Fin d)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with u
  simp only [gd_toLp, ENNReal.toReal_ofReal (Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg 0 1 (u i))), smul_eq_mul]


private noncomputable def km (d : ℕ) (ρ : ℝ) (x y : Vec d) : ℝ :=
  (1 - ρ^2) ^ (-(d:ℝ)/2) *
    Real.exp ((2*ρ*inner ℝ x y - ρ^2*(‖x‖^2+‖y‖^2))/(2*(1-ρ^2)))

private theorem density_factor {d : ℕ} (ρ : ℝ) (hρ : -1 < ρ ∧ ρ < 1) (x y : Vec d) :
    ((Real.sqrt (1-ρ^2))^d)⁻¹ * gd d ((Real.sqrt (1-ρ^2))⁻¹ • (y - ρ • x)) =
        gd d y * km d ρ x y := by
  have hp : 0 < 1-ρ^2 := by nlinarith [mul_pos (sub_pos.mpr hρ.2) (show 0 < 1+ρ by linarith [hρ.1])]
  have hb : 0 < Real.sqrt (1-ρ^2) := Real.sqrt_pos.mpr hp
  have hpow : ((Real.sqrt (1-ρ^2))^d)⁻¹ = (1-ρ^2)^(-(d : ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hp.le, ← Real.rpow_neg hp.le]
    congr 1
    ring
  have hn : ‖(Real.sqrt (1-ρ^2))⁻¹ • (y - ρ • x)‖^2 =
      (‖y‖^2 - 2*ρ*inner ℝ x y + ρ^2*‖x‖^2)/(1-ρ^2) := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hp.le,
      norm_sub_sq_real, real_inner_smul_right, real_inner_comm y x, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  unfold gd km
  rw [hn, hpow]
  have he : -((‖y‖^2-2*ρ*inner ℝ x y+ρ^2*‖x‖^2)/(1-ρ^2))/2 =
      -‖y‖^2/2 + (2*ρ*inner ℝ x y-ρ^2*(‖x‖^2+‖y‖^2))/(2*(1-ρ^2)) := by
    field_simp [hp.ne']
    ring
  rw [he, Real.exp_add]
  ring

/-- Conditional Gaussian regression, written against the product marginal. -/
private theorem gd_conditional {d : ℕ} (ρ : ℝ) (hρ : -1 < ρ ∧ ρ < 1)
    (x : Vec d) (F : Vec d → ℝ) (hF : Measurable F) :
    (∫ y, F (ρ • x + Real.sqrt (1-ρ^2) • y) ∂gaussian d) =
    ∫ y, km d ρ x y * F y ∂gaussian d := by
  let b := Real.sqrt (1-ρ^2)
  have hp : 0 < 1-ρ^2 := by nlinarith [mul_pos (sub_pos.mpr hρ.2) (show 0 < 1+ρ by linarith [hρ.1])]
  have hb : 0 < b := Real.sqrt_pos.mpr hp
  let G (y : Vec d) := gd d (b⁻¹ • (y-ρ • x)) * F y
  rw [gd_integral (fun y => F (ρ • x + Real.sqrt (1-ρ^2) • y)) (by fun_prop),
    gd_integral (fun y => km d ρ x y * F y) (by unfold km; fun_prop)]
  calc
    _ = ∫ y : Vec d, G (ρ • x + b • y) := by
      apply integral_congr_ae
      filter_upwards with y
      change gd d y * F _ = gd d (b⁻¹ • (ρ • x + b • y - ρ • x)) * F _
      simp [smul_smul, hb.ne']
      exact Or.inl rfl
    _ = (b^d)⁻¹ * ∫ y : Vec d, G y := by
      have hs := Measure.integral_comp_smul_of_nonneg (volume : Measure (Vec d))
        (fun v => G (ρ • x + v)) b (hR := hb.le)
      simpa only [integral_add_left_eq_self, smul_eq_mul, finrank_euclideanSpace_fin] using hs
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      simp only [G, ← mul_assoc, b, density_factor ρ hρ]


/-- The probability of a correlated Gaussian pair lying in the same prescribed cell
is its Mehler kernel integral over the product cell. -/
theorem mehler_cell_change (d : ℕ) (A : Set (Vec d)) (hA : MeasurableSet A)
    (ρ : ℝ) (hρ : -1 < ρ ∧ ρ < 1)
    (hI : IntegrableOn (fun z : Vec d × Vec d =>
      (1 - ρ ^ 2) ^ (-(d : ℝ) / 2) *
        Real.exp ((2 * ρ * inner ℝ z.1 z.2 - ρ ^ 2 * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)) /
          (2 * (1 - ρ ^ 2)))) (A ×ˢ A) ((gaussian d).prod (gaussian d))) :
    ((gaussian d).prod (gaussian d)).real
      {z : Vec d × Vec d | z.1 ∈ A ∧ ρ • z.1 + Real.sqrt (1-ρ^2) • z.2 ∈ A} =
    ∫ z in A ×ˢ A,
      (1 - ρ ^ 2) ^ (-(d : ℝ) / 2) *
        Real.exp ((2 * ρ * inner ℝ z.1 z.2 - ρ ^ 2 * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)) /
          (2 * (1 - ρ ^ 2))) ∂(gaussian d).prod (gaussian d) := by
  let g := gaussian d
  let S := {z : Vec d × Vec d | z.1 ∈ A ∧ ρ • z.1 + Real.sqrt (1-ρ^2) • z.2 ∈ A}
  have : IsProbabilityMeasure g := inferInstanceAs (IsProbabilityMeasure (stdGaussian (Vec d)))
  have hS : MeasurableSet S := (hA.preimage measurable_fst).inter
    (hA.preimage (show Measurable (fun z : Vec d × Vec d => ρ • z.1 + Real.sqrt (1-ρ^2) • z.2) by fun_prop))
  change (g.prod g).real S = ∫ z in A ×ˢ A, km d ρ z.1 z.2 ∂g.prod g
  rw [← integral_indicator_one hS]
  have hSI : Integrable (S.indicator (1 : Vec d × Vec d → ℝ)) (g.prod g) := (integrable_const _).indicator hS
  have hIK : IntegrableOn (fun z : Vec d × Vec d => km d ρ z.1 z.2) (A ×ˢ A) (g.prod g) := hI
  rw [integral_prod _ hSI, setIntegral_prod _ hIK, ← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, ← integral_indicator hA]
    have h := gd_conditional ρ hρ x (A.indicator (fun _ => (1:ℝ))) (measurable_const.indicator hA)
    calc
      _ = ∫ y, A.indicator (fun _ => (1:ℝ)) (ρ • x + Real.sqrt (1-ρ^2) • y) ∂g := by
        apply integral_congr_ae
        filter_upwards with y
        by_cases hy : ρ • x + Real.sqrt (1-ρ^2) • y ∈ A <;> simp [S, hx, hy]
      _ = _ := h.trans (by
        apply integral_congr_ae
        filter_upwards with y
        by_cases hy : y ∈ A <;> simp [hy])
  · rw [Set.indicator_of_notMem hx]
    simp [S, hx]

end HermiteLaptop.MaxAgree
end

/- Interior.lean -/
section
open MeasureTheory ProbabilityTheory Set
open PrivateAgnosticHalfspace.Gaussian

namespace HermiteLaptop.MaxAgree

private theorem stability_geom (t : ℝ) (h0 : 0 ≤ t) (ht : t < 1) (d : ℕ) :
    Summable (fun κ : Fin d → ℕ => t ^ degree κ) := by
  induction d with
  | zero =>
    let := Fintype.ofSubsingleton (fun i : Fin 0 => (Fin.elim0 i : ℕ))
    exact (hasSum_fintype _).summable
  | succ d ih =>
    apply (Fin.consEquiv (fun _ : Fin (d+1) => ℕ)).summable_iff.mp
    have h := (summable_geometric_of_lt_one h0 ht).mul_of_nonneg ih
      (fun n => pow_nonneg h0 n) (fun a => pow_nonneg h0 (degree a))
    apply h.congr
    rintro ⟨n, a⟩
    change t^n * t^degree a = t^(∑ i, Fin.cons n a i)
    rw [Fin.sum_cons, pow_add]
    rfl

private theorem stability_hermite_norm_bound (d : ℕ) (A : Set (Vec d)) (κ : Fin d → ℕ) :
    (∫ x in A, ‖hermite d κ x‖ ∂gaussian d) ≤ 1 := by
  let : IsProbabilityMeasure (gaussian d) := inferInstanceAs (IsProbabilityMeasure (stdGaussian _))
  obtain ⟨_, hLp, ⟨b, hb⟩, _⟩ := lemma_B_8 d
  have hi := (hLp κ).integrable (by norm_num)
  apply (setIntegral_le_integral hi.norm (ae_of_all _ (fun x => norm_nonneg (hermite d κ x)))).trans
  rw [integral_norm_eq_lintegral_enorm hi.1, ← eLpNorm_one_eq_lintegral_enorm]
  rw [← b.orthonormal.norm_eq_one κ, Lp.norm_def, eLpNorm_congr_ae (hb κ)]
  exact ENNReal.toReal_mono (hLp κ).2.ne
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hi.1)

/-- Mehler's correlation density with respect to independent standard Gaussians. -/
noncomputable def stabilityMehlerKernel (d : ℕ) (ρ : ℝ) (z : Vec d × Vec d) : ℝ :=
  (1 - ρ^2)^(-(d : ℝ)/2) *
    Real.exp ((2*ρ*inner ℝ z.1 z.2 - ρ^2*(‖z.1‖^2+‖z.2‖^2))/(2*(1-ρ^2)))

private theorem stability_cell_mehler_aux (d : ℕ) (A : Set (Vec d))
    (ρ : ℝ) (hρ : -1 < ρ ∧ ρ < 1) :
    IntegrableOn (stabilityMehlerKernel d ρ) (A ×ˢ A) ((gaussian d).prod (gaussian d)) ∧
    HasSum (fun κ : Fin d → ℕ => ρ ^ degree κ * (∫ x in A, hermite d κ x ∂gaussian d)^2)
      (∫ z in A ×ˢ A, stabilityMehlerKernel d ρ z ∂(gaussian d).prod (gaussian d)) := by
  let : IsProbabilityMeasure (gaussian d) := inferInstanceAs (IsProbabilityMeasure (stdGaussian _))
  let μ := (gaussian d).restrict A
  let F := fun (κ : Fin d → ℕ) (z : Vec d × Vec d) => ρ^degree κ * (hermite d κ z.1 * hermite d κ z.2)
  have hI (κ : Fin d → ℕ) : Integrable (F κ) (μ.prod μ) := by
    have h := ((lemma_B_8 d).2.1 κ).integrable (by norm_num)
    exact (h.integrableOn.mul_prod h.integrableOn).const_mul _
  have hbound : Summable (fun κ : Fin d → ℕ => ∫ z, ‖F κ z‖ ∂μ.prod μ) := by
    apply (stability_geom |ρ| (abs_nonneg _) (abs_lt.mpr hρ) d).of_nonneg_of_le
      (fun κ => integral_nonneg (fun z => norm_nonneg _))
    intro κ
    simp only [F, norm_mul, norm_pow, integral_const_mul, Real.norm_eq_abs]
    have h := stability_hermite_norm_bound d A κ
    simp only [Real.norm_eq_abs] at h
    have h0 : 0 ≤ ∫ x, |hermite d κ x| ∂μ := integral_nonneg (fun _ => abs_nonneg _)
    change (∫ x, |hermite d κ x| ∂μ) ≤ 1 at h
    apply mul_le_of_le_one_right (pow_nonneg (abs_nonneg _) _)
    rw [integral_prod_mul (fun x => |hermite d κ x|) (fun x => |hermite d κ x|)]
    exact mul_le_one₀ h h0 h
  have hs := hasSum_integral_of_summable_integral_norm hI hbound
  have he (z : Vec d × Vec d) := (lemma_B_9 d z.1 z.2 ρ hρ).tsum_eq
  have hint (κ : Fin d → ℕ) : (∫ z, F κ z ∂μ.prod μ) =
      ρ ^ degree κ * (∫ x in A, hermite d κ x ∂gaussian d)^2 := by
    rw [show (∫ z, F κ z ∂μ.prod μ) = _ from integral_const_mul _ _,
      integral_prod_mul (hermite d κ) (hermite d κ)]
    rw [sq]
  simp_rw [hint] at hs
  have heq : stabilityMehlerKernel d ρ = fun z => ∑' κ, F κ z := by
    funext z
    simpa only [F, ←mul_assoc, stabilityMehlerKernel] using (he z).symm
  simp only [IntegrableOn, ← Measure.prod_restrict]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold stabilityMehlerKernel
    fun_prop
  · rw [hasFiniteIntegral_iff_enorm, heq]
    refine lt_of_le_of_lt (lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)) ?_
    change (∫⁻ z, ∑' κ, ‖F κ z‖ₑ ∂μ.prod μ) < ⊤
    rw [lintegral_tsum (fun κ => (hI κ).1.enorm)]
    simpa only [ofReal_integral_norm_eq_lintegral_enorm (hI _)] using hbound.tsum_ofReal_lt_top
  · rw [heq]
    exact hs

theorem stability_cell_mehler_integrable (d : ℕ) (A : Set (Vec d)) (_hA : MeasurableSet A)
    (ρ : ℝ) (hρ : -1 < ρ ∧ ρ < 1) :
    IntegrableOn (stabilityMehlerKernel d ρ) (A ×ˢ A) ((gaussian d).prod (gaussian d)) :=
  (stability_cell_mehler_aux d A ρ hρ).1

theorem stability_cell_mehler_hasSum (d : ℕ) (A : Set (Vec d)) (_hA : MeasurableSet A)
    (ρ : ℝ) (hρ : -1 < ρ ∧ ρ < 1) :
    HasSum (fun κ : Fin d → ℕ => ρ ^ degree κ * (∫ x in A, hermite d κ x ∂gaussian d)^2)
      (∫ z in A ×ˢ A, stabilityMehlerKernel d ρ z ∂(gaussian d).prod (gaussian d)) :=
  (stability_cell_mehler_aux d A ρ hρ).2

end HermiteLaptop.MaxAgree
end

/- Cells.lean -/
section
open MeasureTheory ProbabilityTheory Set
open PrivateAgnosticHalfspace.Gaussian

namespace HermiteLaptop.MaxAgree

/-- The Gaussian noise stability of a measurable cell, including both degenerate correlations. -/
theorem cell_correlated_hasSum (d : ℕ) (A : Set (Vec d)) (hA : MeasurableSet A)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    HasSum (fun κ : Fin d → ℕ => ρ ^ degree κ * (∫ x in A, hermite d κ x ∂gaussian d)^2)
      (((gaussian d).prod (gaussian d)).real
        {z : Vec d × Vec d | z.1 ∈ A ∧ ρ • z.1 + Real.sqrt (1-ρ^2) • z.2 ∈ A}) := by
  by_cases he : ρ = 1 ∨ ρ = -1
  · let B := A ∩ (fun x : Vec d => ρ • x) ⁻¹' A
    have hB : MeasurableSet B := hA.inter (hA.preimage (by fun_prop))
    have hz : Real.sqrt (1-ρ^2) = 0 := by rcases he with rfl | rfl <;> norm_num
    have hset : {z : Vec d × Vec d | z.1 ∈ A ∧ ρ • z.1 + Real.sqrt (1-ρ^2) • z.2 ∈ A}
        = B ×ˢ Set.univ := by ext z; simp [B, hz]
    let : IsProbabilityMeasure (gaussian d) := inferInstanceAs (IsProbabilityMeasure (stdGaussian _))
    rw [hset, measureReal_prod_prod, probReal_univ, mul_one, ← integral_indicator_one hB]
    have hfun : (B.indicator (1 : Vec d → ℝ)) = fun x =>
        A.indicator (fun _ => (1 : ℝ)) x * A.indicator (fun _ => (1 : ℝ)) (ρ • x) := by
      funext x
      by_cases hx : x ∈ A <;> by_cases hy : ρ • x ∈ A <;> simp [B, hx, hy]
    rw [hfun]
    exact cell_endpoint_hasSum d A hA ρ he
  · have hρ' : -1 < ρ ∧ ρ < 1 := by
      push Not at he
      exact ⟨lt_of_le_of_ne hρ.1 (Ne.symm he.2), lt_of_le_of_ne hρ.2 he.1⟩
    rw [mehler_cell_change d A hA ρ hρ' (stability_cell_mehler_integrable d A hA ρ hρ')]
    exact stability_cell_mehler_hasSum d A hA ρ hρ'

end HermiteLaptop.MaxAgree
end

/- SpokeIndex.lean -/
section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace HermiteLaptop.MaxAgree

theorem spokeIndex_measurable {k : ℕ} : Measurable (spokeIndex (k := k)) := by
  classical
  unfold spokeIndex
  generalize List.finRange k = l
  induction l with
  | nil => exact measurable_const
  | cons p l ih =>
    have h : MeasurableSet {x : Fin k → ℝ | ∀ q, x q ≤ x p} := by
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter (fun q => measurableSet_le (measurable_pi_apply q) (measurable_pi_apply p))
    simp only [List.find?_cons]
    convert Measurable.ite h (measurable_const (a := p.val)) ih using 1
    ext x
    by_cases hmax : ∀ q, x q ≤ x p <;> simp [hmax]
    all_goals exact fun _ => Classical.propDecidable _

end HermiteLaptop.MaxAgree
end

/- Collision.lean -/
section
open MeasureTheory ProbabilityTheory Set Function WithLp
open scoped ENNReal RealInnerProductSpace
open PrivateAgnosticHalfspace.Gaussian (Vec gaussian hermite degree)
namespace HermiteLaptop.MaxAgree

private def strictCell {k : ℕ} (i : Fin k) : Set (Fin k → ℝ) :=
  {x | ∀ j, j ≠ i → x j < x i}

private lemma strictCell_spoke {k : ℕ} {p : Fin k} {x : Fin k → ℝ} (hp : x ∈ strictCell p) :
    spokeIndex x = p.val := by
  classical
  have hpmax (q : Fin k) : x q ≤ x p := by
    rcases eq_or_ne q p with rfl | h
    · exact le_rfl
    · exact (hp q h).le
  unfold spokeIndex
  cases h : (List.finRange k).find? (fun p => decide (∀ q, x q ≤ x p)) with
  | none =>
    have hno := List.find?_eq_none.mp h p (List.mem_finRange p)
    simp [hpmax] at hno
  | some q =>
    have hq : ∀ j, x j ≤ x q := by
      simpa only [decide_eq_true_eq] using List.find?_some (p := fun p => decide (∀ j, x j ≤ x p)) h
    have heq : q = p := by
      by_contra hne
      exact (hp q hne).not_ge (hq p)
    simp [heq]

private lemma gaussPi_injective_ae (k : ℕ) : ∀ᵐ x ∂(gaussPi k), Injective x := by
  have : IsProbabilityMeasure (gaussPi k) := inferInstanceAs (IsProbabilityMeasure (Measure.pi _))
  let g := gaussianReal 0 1
  let : NullSingletonClass g := nullSingletonClass_gaussianReal one_ne_zero
  let : IsProbabilityMeasure g := inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))
  have ind : iIndepFun (fun (i : Fin k) (x : Fin k → ℝ) => x i) (gaussPi k) :=
    iIndepFun_pi (μ := fun _ => g) (X := fun _ => id) (fun _ => aemeasurable_id)
  have law (i : Fin k) : HasLaw (fun x : Fin k → ℝ => x i) g (gaussPi k) :=
    (measurePreserving_eval (fun _ : Fin k => g) i).hasLaw
  have h (i j : Fin k) : ∀ᵐ x ∂(gaussPi k), i ≠ j → x i ≠ x j := by
    by_cases h : i = j
    · simp [h]
    have pair := (ind.indepFun h).hasLaw_prod (law i) (law j)
    have d : ∀ᵐ z : ℝ × ℝ ∂g.prod g, z.1 ≠ z.2 := by
      apply (Measure.ae_prod_iff_ae_ae ((measurableSet_eq_fun measurable_fst measurable_snd).compl)).2
      exact ae_of_all _ fun x => (g.ae_ne x).mono fun y hy => Ne.symm hy
    have hp : Measurable (fun z : ℝ × ℝ => z.1 ≠ z.2) :=
      measurableSet_setOfPred.1 ((measurableSet_eq_fun measurable_fst measurable_snd).compl)
    simpa [h] using (pair.ae_iff hp).2 d
  filter_upwards [ae_all_iff.2 (fun i => ae_all_iff.2 (h i))] with x hx i j hij
  exact by_contra fun hne => hx i j hne hij

private lemma strictCell_exists {k : ℕ} (hk : 0 < k) {x : Fin k → ℝ} (hx : Injective x) :
    ∃ i, x ∈ strictCell i := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
  exact ⟨i, fun j hji => lt_of_le_of_ne (hi j (Finset.mem_univ _)) (fun h => hji (hx h))⟩

def winner {k : ℕ} (p : Fin k) : Set (Vec k) := {x | spokeIndex (ofLp x) = p.val}

private theorem winner_meas {k : ℕ} (p : Fin k) : MeasurableSet (winner p) :=
  measurableSet_eq_fun (spokeIndex_measurable.comp (by fun_prop)) measurable_const

private theorem winner_coeff {k : ℕ} (p : Fin k) (α : Fin k → ℕ) :
    (∫ x in winner p, hermite k α x ∂gaussian k) = hermCoeff p α := by
  let e := MeasurableEquiv.toLp 2 (Fin k → ℝ)
  have he : (gaussPi k).map e = gaussian k := map_pi_eq_stdGaussian
  rw [← he, setIntegral_map_equiv]
  have hset : (e ⁻¹' winner p) =ᵐ[gaussPi k] argmaxRegion p := by
    filter_upwards [gaussPi_injective_ae k] with x hx
    obtain ⟨i, hi⟩ := strictCell_exists (Nat.zero_lt_of_lt p.isLt) hx
    apply propext
    change (spokeIndex x = p.val) ↔ ∀ j, x j ≤ x p
    rw [strictCell_spoke hi]
    constructor
    · intro hp; have hi' : i = p := Fin.ext hp
      subst p
      intro j
      by_cases h : j=i
      · simp [h]
      · exact (hi j h).le
    · intro h
      by_contra hne
      exact (hi p (fun h => hne (congrArg Fin.val h.symm))).not_ge (h i)
  rw [setIntegral_congr_set hset]
  have hA : MeasurableSet (argmaxRegion p) := by
    simp only [argmaxRegion, ofPred_forall]
    exact MeasurableSet.iInter fun q => measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _)
  unfold hermCoeff
  rw [← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ argmaxRegion p <;> simp [hx]
  rfl

/-- A spectral sum over multi-indices can be regrouped by total Hermite degree. -/
private theorem level_hasSum {k : ℕ} (p : Fin k) (ρ b : ℝ)
    (h : HasSum (fun α : Fin k → ℕ => ρ^(∑ i, α i) * hermCoeff p α ^ 2) b) :
    HasSum (fun m : ℕ => ρ^m * levelWeight p m) b := by
  let e := Finset.Nat.sigmaAntidiagonalTupleEquivTuple k
  have hh := e.hasSum_iff.mpr h
  apply hh.sigma
  intro m
  convert hasSum_fintype (fun α : Finset.Nat.antidiagonalTuple k m => ρ^m * hermCoeff p α.val ^ 2) using 1
  · funext α
    change ρ^(∑ i, α.val i)*_ = _
    rw [Finset.Nat.mem_antidiagonalTuple.mp α.property]
    rfl
  · simp only [levelWeight, Finset.mul_sum]
    exact (Finset.sum_coe_sort _ (fun i => ρ^m * hermCoeff p i^2)).symm

private theorem spoke_lt {k : ℕ} (hk : 1 ≤ k) (x : Fin k → ℝ) : spokeIndex x < k := by
  unfold spokeIndex
  cases (List.finRange k).find? (fun p => decide (∀ q, x q ≤ x p)) with
  | none => exact hk
  | some p => exact p.isLt

def jointWinner {k : ℕ} (p : Fin k) (ρ : ℝ) : Set (Vec k × Vec k) :=
  {z | z.1 ∈ winner p ∧ ρ • z.1 + Real.sqrt (1-ρ^2) • z.2 ∈ winner p}

private theorem jointWinner_meas {k : ℕ} (p : Fin k) (ρ : ℝ) : MeasurableSet (jointWinner p ρ) :=
  ((winner_meas p).preimage measurable_fst).inter ((winner_meas p).preimage (by fun_prop))

theorem collision_eq_sum {k : ℕ} (hk : 1 ≤ k) (ρ : ℝ) :
    collisionProb k ρ = ∑ p : Fin k, ((gaussian k).prod (gaussian k)).real (jointWinner p ρ) := by
  let e := MeasurableEquiv.toLp 2 (Fin k → ℝ)
  have he : MeasurePreserving e (gaussPi k) (gaussian k) := ⟨e.measurable, map_pi_eq_stdGaussian⟩
  let : IsProbabilityMeasure (gaussPi k) := inferInstanceAs (IsProbabilityMeasure (Measure.pi _))
  let : IsProbabilityMeasure (gaussian k) := inferInstanceAs (IsProbabilityMeasure (stdGaussian _))
  have hp := he.prod he
  have hd : Pairwise (Disjoint on (fun p : Fin k => jointWinner p ρ)) := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    intro z hz hw
    exact hpq (Fin.ext (hz.1.symm.trans hw.1))
  have hu : (Prod.map e e) ⁻¹' (⋃ p, jointWinner p ρ) =
      {z | spokeIndex z.1 = spokeIndex (corrPartner ρ z.1 z.2)} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    change (∃ p : Fin k, spokeIndex z.1 = p.val ∧ spokeIndex (corrPartner ρ z.1 z.2) = p.val) ↔ _
    constructor
    · rintro ⟨p, hp, hq⟩
      exact hp.trans hq.symm
    · intro h
      exact ⟨⟨_,spoke_lt hk z.1⟩, rfl, h.symm⟩
  rw [← measureReal_iUnion_fintype hd (fun p => jointWinner_meas p ρ)]
  have hm := hp.measure_preimage (MeasurableSet.iUnion (fun p => jointWinner_meas p ρ)).nullMeasurableSet
  rw [hu] at hm
  exact congrArg ENNReal.toReal hm

theorem level_collision_sum {k : ℕ} (p : Fin k) (ρ : ℝ) (hρ : ρ ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun m : ℕ => ρ^m * levelWeight p m)
      (((gaussian k).prod (gaussian k)).real (jointWinner p ρ)) := by
  apply level_hasSum
  have h := cell_correlated_hasSum k (winner p) (winner_meas p) ρ hρ
  simpa only [winner_coeff, degree, jointWinner] using h

end HermiteLaptop.MaxAgree
end

/- CellSymmetry.lean -/
section
open MeasureTheory ProbabilityTheory Finset
namespace HermiteLaptop.MaxAgree

private theorem hermCoeff_perm {k : ℕ} (e : Equiv.Perm (Fin k)) (p : Fin k) (α : Fin k → ℕ) :
    hermCoeff (e p) α = hermCoeff p (α ∘ e) := by
  let F := MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) e
  have hm : MeasurePreserving F (gaussPi k) (gaussPi k) :=
    measurePreserving_piCongrLeft (fun _ : Fin k => gaussianReal 0 1) e
  have hF (x : Fin k → ℝ) (i : Fin k) : F x (e i) = x i :=
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin k => ℝ) e x i
  have hcell (x : Fin k → ℝ) : F x ∈ argmaxRegion (e p) ↔ x ∈ argmaxRegion p := by
    change (∀ q, F x q ≤ F x (e p)) ↔ ∀ q, x q ≤ x p
    constructor
    · intro h q
      simpa only [hF] using h (e q)
    · intro h q
      obtain ⟨j, rfl⟩ := e.surjective q
      simpa only [hF] using h j
  have hH (x : Fin k → ℝ) : hMulti α (F x) = hMulti (α ∘ e) x := by
    unfold hMulti
    rw [← Equiv.prod_comp e (fun q => hNorm (α q) (F x q))]
    simp only [hF, Function.comp_apply]
  unfold hermCoeff
  rw [← hm.integral_comp' (fun z => (argmaxRegion (e p)).indicator (fun _ => (1 : ℝ)) z * hMulti α z)]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  by_cases hx : x ∈ argmaxRegion p
  · simp [hx, (hcell x).2 hx, hH]
  · simp [hx, mt (hcell x).1 hx]

/-- Relabelling the Gaussian coordinates preserves the total Hermite mass at each degree. -/
theorem levelWeight_same_label {k : ℕ} (p q : Fin k) (m : ℕ) : levelWeight p m = levelWeight q m := by
  classical
  let e := Equiv.swap q p
  have hcomp (α : Fin k → ℕ) : (α ∘ e) ∘ e = α := by
    ext i
    simp [e]
  have he : e q = p := Equiv.swap_apply_left _ _
  have hdeg (α : Fin k → ℕ) (h : α ∈ Finset.Nat.antidiagonalTuple k m) :
      α ∘ e ∈ Finset.Nat.antidiagonalTuple k m := by
    rw [Finset.Nat.mem_antidiagonalTuple] at h ⊢
    exact (Equiv.sum_comp e α).trans h
  unfold levelWeight
  apply Finset.sum_nbij' (fun α => α ∘ e) (fun α => α ∘ e) hdeg hdeg
      (fun α _ => hcomp α) (fun α _ => hcomp α)
  intro α _
  rw [← he, hermCoeff_perm]

theorem coeffC_eq_label_weight (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    coeffC k m = (k:ℝ) * levelWeight (⟨0,hk⟩ : Fin k) m := by
  unfold coeffC
  simp only [fun p => levelWeight_same_label p (⟨0,hk⟩ : Fin k) m, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end HermiteLaptop.MaxAgree
end

/- Sol_HermiteLaptop_MaxAgree_eq_8_9.lean -/
section
namespace HermiteLaptop.MaxAgree

/-- Sum the individual cell expansions and use permutation symmetry on a Hermite level. -/
theorem collisionSeriesAssembly {k : ℕ} (hk : 1 ≤ k)
    (mass : ℝ → Fin k → ℝ)
    (cell : ∀ ρ ∈ Set.Icc (-1 : ℝ) 1, ∀ p, HasSum
      (fun m : ℕ => ρ ^ m * levelWeight p m) (mass ρ p))
    (partition : ∀ ρ ∈ Set.Icc (-1 : ℝ) 1, collisionProb k ρ = ∑ p, mass ρ p)
    (symm : ∀ (m : ℕ) (p : Fin k), levelWeight p m = levelWeight (⟨0,hk⟩ : Fin k) m) :
    (∀ ρ ∈ Set.Icc (-1 : ℝ) 1,
      (∀ p : Fin k, Summable (fun m : ℕ => ρ ^ m * levelWeight p m)) ∧
      collisionProb k ρ = ∑ p : Fin k, ∑' m : ℕ, ρ ^ m * levelWeight p m ∧
      HasSum (fun m : ℕ => coeffC k m * ρ ^ m) (collisionProb k ρ)) ∧
    ∀ m : ℕ, coeffC k m = (k : ℝ) * levelWeight (⟨0, hk⟩ : Fin k) m ∧ 0 ≤ coeffC k m := by
  constructor
  · intro ρ hρ
    refine ⟨fun p => (cell ρ hρ p).summable, ?_, ?_⟩
    · simpa only [fun p => (cell ρ hρ p).tsum_eq] using partition ρ hρ
    · have hsum (s : Finset (Fin k)) :
          HasSum (fun m : ℕ => ∑ p ∈ s, ρ^m * levelWeight p m) (∑ p ∈ s, mass ρ p) := by
        induction s using Finset.induction_on with
        | empty => simpa only [Finset.sum_empty] using (hasSum_zero (α := ℝ) (β := ℕ))
        | @insert p s hp ih =>
          simp only [Finset.sum_insert hp]
          exact (cell ρ hρ p).add ih
      rw [partition ρ hρ]
      simpa only [coeffC, Finset.sum_mul, Finset.mul_sum, mul_comm] using hsum Finset.univ
  · intro m
    constructor
    · simp [coeffC, symm m, nsmul_eq_mul]
    · unfold coeffC levelWeight
      positivity

end HermiteLaptop.MaxAgree

open HermiteLaptop.MaxAgree
open PrivateAgnosticHalfspace.Gaussian (gaussian)

theorem solution (k : ℕ) (hk : 1 ≤ k) :
    (∀ ρ ∈ Set.Icc (-1 : ℝ) 1,
      (∀ p : Fin k, Summable (fun m : ℕ => ρ ^ m * levelWeight p m)) ∧
      collisionProb k ρ = ∑ p : Fin k, ∑' m : ℕ, ρ ^ m * levelWeight p m ∧
      HasSum (fun m : ℕ => coeffC k m * ρ ^ m) (collisionProb k ρ)) ∧
    ∀ m : ℕ, coeffC k m = (k : ℝ) * levelWeight (⟨0, hk⟩ : Fin k) m ∧ 0 ≤ coeffC k m  := by
  exact collisionSeriesAssembly hk
    (fun ρ p => ((gaussian k).prod (gaussian k)).real (jointWinner p ρ))
    (fun ρ hρ p => level_collision_sum p ρ hρ)
    (fun ρ _ => collision_eq_sum hk ρ)
    (fun m p => levelWeight_same_label p ⟨0,hk⟩ m)
end
