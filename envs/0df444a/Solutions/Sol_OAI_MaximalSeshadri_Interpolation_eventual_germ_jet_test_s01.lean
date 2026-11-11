-- Prove2me | solution 1 for OAI.MaximalSeshadri.Interpolation.eventual_germ_jet_test_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:17:08.489225+00:00
-- url     : https://prove2.me/submissions/890eba62-2d89-4575-85cb-82718657a1ba

import Mathlib
import Definitions.Def_Q223SES005
import Theorems.Thm_OAI_MaximalSeshadri_Interpolation_eventual_torus_jet_test_s01

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_CompressionRanks
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology

theorem finite_jet_rank_persistence {α ι : Type*} [Finite ι]
    (l : Filter α) (r m : ℕ) (points : Fin r → ℂ × ℂ)
    (f : α → ι → ℂ → ℂ → ℂ) (f₀ : ι → ℂ → ℂ → ℂ)
    (hconv : ∀ i j, Tendsto (fun s => finiteJetColumn r m points (f s i) j) l
      (𝓝 (finiteJetColumn r m points (f₀ i) j)))
    (h₀ : LinearIndependent ℂ (fun i => finiteJetColumn r m points (f₀ i))) :
    ∀ᶠ s in l, LinearIndependent ℂ (fun i => finiteJetColumn r m points (f s i)) := by
  have hlim : Tendsto (fun s i => finiteJetColumn r m points (f s i)) l
      (𝓝 (fun i => finiteJetColumn r m points (f₀ i))) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (hconv i))
  exact hlim.eventually h₀.eventually

theorem contDiff_iteratedDeriv_parameter (f : ℂ → ℂ → ℂ)
    (hf : ContDiff ℂ ∞ (Function.uncurry f)) (n : ℕ) :
    ContDiff ℂ ∞ (fun p : ℂ × ℂ => iteratedDeriv n (f p.1) p.2) := by
  induction n with
  | zero =>
    exact hf
  | succ n ih =>
    have hh : ContDiff ℂ ∞ (Function.uncurry
        (fun p : ℂ × ℂ => fun z : ℂ => iteratedDeriv n (f p.1) z)) := by
      exact ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
    have hd := hh.fderiv contDiff_snd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (∞ : ℕ∞ω) + 1 ≤ ∞)
    have ha := hd.clm_apply (contDiff_const (c := (1 : ℂ)))
    simpa only [iteratedDeriv_succ, deriv] using ha

theorem compression_row_smooth (B h : ℕ) :
    ContDiff ℂ ∞ (fun p : ℂ × ℂ => (1 + p.1 * p.2) ^ B * p.2 ^ h) := by
  fun_prop

theorem compression_row_derivative_limit (B h n : ℕ) (z : ℂ) :
    Tendsto (fun s : ℂ => iteratedDeriv n (fun y : ℂ => (1 + s * y) ^ B * y ^ h) z)
      (𝓝 0) (𝓝 (iteratedDeriv n (fun y : ℂ => y ^ h) z)) := by
  have hc := (contDiff_iteratedDeriv_parameter
    (fun s y : ℂ => (1 + s * y) ^ B * y ^ h) (compression_row_smooth B h) n).continuous
  have hh := (hc.comp (continuous_id.prodMk (continuous_const (y := z)))).tendsto (0 : ℂ)
  change Tendsto (fun s : ℂ => iteratedDeriv n (fun y : ℂ =>
    (1 + s * y) ^ B * y ^ h) z) (𝓝 0)
    (𝓝 (iteratedDeriv n (fun y : ℂ => (1 + 0 * y) ^ B * y ^ h) z)) at hh
  simpa only [zero_mul, add_zero, one_pow, one_mul] using hh

theorem mixed_deriv_separated (f g : ℂ → ℂ) (a b : ℕ) (u z : ℂ) :
    iteratedDeriv b (fun y => iteratedDeriv a (fun x => f x * g y) u) z =
      iteratedDeriv a f u * iteratedDeriv b g z := by
  simp_rw [iteratedDeriv_mul_const_field]
  rw [iteratedDeriv_const_mul_field]

theorem compression_mixed_derivative_limit (q : ℤ) (B h a b : ℕ) (u z : ℂ) :
    Tendsto (fun s : ℂ => iteratedDeriv b (fun y => iteratedDeriv a
      (fun x => x ^ q * ((1 + s * y) ^ B * y ^ h)) u) z) (𝓝 0)
      (𝓝 (iteratedDeriv b (fun y => iteratedDeriv a (fun x => x ^ q * y ^ h) u) z)) := by
  simp_rw [mixed_deriv_separated]
  exact tendsto_const_nhds.mul (compression_row_derivative_limit B h b z)

theorem compression_finite_rank {ι : Type*} [Finite ι] (q : ι → ℤ) (B h : ι → ℕ)
    (r m : ℕ) (points : Fin r → ℂ × ℂ)
    (h₀ : LinearIndependent ℂ (fun i => finiteJetColumn r m points
      (fun u z => u ^ q i * z ^ h i))) :
    ∀ᶠ s : ℂ in 𝓝 0, LinearIndependent ℂ (fun i => finiteJetColumn r m points
      (fun u z => u ^ q i * ((1 + s * z) ^ B i * z ^ h i))) := by
  apply finite_jet_rank_persistence (𝓝 (0 : ℂ)) r m points _ _ _ h₀
  intro i j
  dsimp only [finiteJetColumn]
  split_ifs
  · exact compression_mixed_derivative_limit (q i) (B i) (h i) j.2.1 j.2.2
      (points j.1).1 (points j.1).2
  · exact tendsto_const_nhds

theorem linearIndependent_of_span_le {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℂ V] (u v : ι → V)
    (hu : LinearIndependent ℂ u)
    (hspan : Submodule.span ℂ (Set.range u) ≤ Submodule.span ℂ (Set.range v)) :
    LinearIndependent ℂ v := by
  let := Module.Finite.span_of_finite ℂ (Set.finite_range v)
  apply linearIndependent_iff_card_le_finrank_span.mpr
  rw [← finrank_span_eq_card hu]
  exact Submodule.finrank_mono hspan

theorem iteratedDeriv_polynomial (P : Polynomial ℂ) (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => P.eval z) =
      fun z => (((Polynomial.derivative : Module.End ℂ (Polynomial ℂ)) ^ n) P).eval z := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have he : deriv (fun z : ℂ => P.eval z) = fun z => P.derivative.eval z := by
      funext z
      exact P.deriv
    rw [he, ih, Module.End.iterate_succ]
    rfl

theorem polynomialJetMap_eq (r m : ℕ) (points : Fin r → ℂ × ℂ) (q : ℤ)
    (P : Polynomial ℂ) :
    polynomialJetMap r m points q P = finiteJetColumn r m points
      (fun u z => u ^ q * P.eval z) := by
  funext j
  simp only [polynomialJetMap, LinearMap.pi_apply, finiteJetColumn]
  split_ifs <;> simp only [LinearMap.smul_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, Polynomial.coe_aeval_eq_eval, smul_eq_mul,
    mixed_deriv_separated, iteratedDeriv_polynomial, LinearMap.zero_apply]

theorem polynomial_image_mem_span {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : Polynomial ℂ →ₗ[ℂ] V) (P : Polynomial ℂ) (n : ℕ) (hP : P.natDegree ≤ n) :
    L P ∈ Submodule.span ℂ (Set.range fun j : Fin (n + 1) => L (Polynomial.X ^ (j : ℕ))) := by
  classical
  rw [← P.sum_monomial_eq, Polynomial.sum_def, map_sum]
  apply Submodule.sum_mem
  intro j hj
  have hjn : j < n + 1 := by
    have h := (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)).trans hP
    omega
  have he : Polynomial.monomial j (P.coeff j) = (P.coeff j) • (Polynomial.X : Polynomial ℂ) ^ j := by
    simp [Polynomial.smul_eq_C_mul, Polynomial.C_mul_X_pow_eq_monomial]
  rw [he, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hjn⟩, rfl⟩)

theorem compressionRowMap_inverse (s : ℂ) (hs : s ≠ 0) (B h : ℕ) :
    compressionRowMap s B ((Polynomial.C s⁻¹ * (Polynomial.X - 1)) ^ h) =
      (1 + Polynomial.C s * Polynomial.X) ^ B * Polynomial.X ^ h := by
  have he : Polynomial.C s⁻¹ * ((1 + Polynomial.C s * Polynomial.X) - 1) =
      (Polynomial.X : Polynomial ℂ) := by
    rw [add_sub_cancel_left, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hs,
      Polynomial.C_1, one_mul]
  simp only [compressionRowMap, LinearMap.coe_mk, AddHom.coe_mk, Polynomial.pow_comp,
    Polynomial.mul_comp, Polynomial.C_comp, Polynomial.sub_comp, Polynomial.X_comp,
    Polynomial.one_comp, he]

theorem compression_inverse_degree (s : ℂ) (h : ℕ) :
    ((Polynomial.C s⁻¹ * (Polynomial.X - 1)) ^ h).natDegree ≤ h := by
  have ha : (Polynomial.C s⁻¹ * (Polynomial.X - 1)).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_mul_le).trans ?_
    simp only [Polynomial.natDegree_C, zero_add]
    exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  exact (Polynomial.natDegree_pow_le).trans (by simpa using Nat.mul_le_mul_left h ha)


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_ConvergentSeries
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
open scoped BigOperators Topology
open Filter Set

lemma monomialDeriv_eq (n a : ℕ) :
    monomialDeriv n a = iteratedDeriv a (fun x : ℂ => x ^ n) := by
  ext x
  simp only [monomialDeriv, iteratedDeriv_pow]

lemma deriv_monomialDeriv (n a : ℕ) :
    deriv (monomialDeriv n a) = monomialDeriv n (a + 1) := by
  simp only [monomialDeriv_eq, iteratedDeriv_succ]

lemma differentiable_monomialDeriv (n a : ℕ) :
    Differentiable ℂ (monomialDeriv n a) := by
  unfold monomialDeriv
  fun_prop

lemma seriesPartial_zero (c : Exponent → ℂ) : seriesPartial c 0 0 = seriesEval c := by
  ext x z
  simp [seriesPartial, seriesEval, monomialDeriv]

lemma deriv_seriesPartial_left (c : Exponent → ℂ) (R : ℝ)
    (hs : DerivativeSummable c R) (a b : ℕ) (x z : ℂ)
    (hx : ‖x‖ < R) (hz : ‖z‖ ≤ R) :
    deriv (fun w => seriesPartial c a b w z) x = seriesPartial c (a + 1) b x z := by
  have hsum := Complex.hasSum_deriv_of_summable_norm (hs a b)
    (U := Metric.ball (0 : ℂ) R)
    (F := fun p : Exponent => fun w : ℂ => c p * monomialDeriv p.1 a w *
      monomialDeriv p.2 b z)
    (fun p => ((differentiable_monomialDeriv p.1 a).const_mul (c p)).mul_const
      (monomialDeriv p.2 b z) |>.differentiableOn)
    Metric.isOpen_ball
    (fun p w hw => norm_seriesTerm_le c R a b p w z
      (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hw).le) hz)
    (by simpa only [Metric.mem_ball, dist_zero_right] using hx)
  have he (p : Exponent) :
      deriv (fun w : ℂ => c p * monomialDeriv p.1 a w * monomialDeriv p.2 b z) x =
        c p * monomialDeriv p.1 (a + 1) x * monomialDeriv p.2 b z := by
    rw [deriv_mul_const_field, deriv_const_mul_field, deriv_monomialDeriv]
  simpa only [seriesPartial, he] using hsum.tsum_eq.symm

lemma deriv_seriesPartial_right (c : Exponent → ℂ) (R : ℝ)
    (hs : DerivativeSummable c R) (a b : ℕ) (x z : ℂ)
    (hx : ‖x‖ ≤ R) (hz : ‖z‖ < R) :
    deriv (fun w => seriesPartial c a b x w) z = seriesPartial c a (b + 1) x z := by
  have hsum := Complex.hasSum_deriv_of_summable_norm (hs a b)
    (U := Metric.ball (0 : ℂ) R)
    (F := fun p : Exponent => fun w : ℂ => c p * monomialDeriv p.1 a x *
      monomialDeriv p.2 b w)
    (fun p => ((differentiable_monomialDeriv p.2 b).const_mul
      (c p * monomialDeriv p.1 a x)).differentiableOn)
    Metric.isOpen_ball
    (fun p w hw => norm_seriesTerm_le c R a b p x w hx
      (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hw).le))
    (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  have he (p : Exponent) :
      deriv (fun w : ℂ => c p * monomialDeriv p.1 a x * monomialDeriv p.2 b w) z =
        c p * monomialDeriv p.1 a x * monomialDeriv p.2 (b + 1) z := by
    rw [deriv_const_mul_field, deriv_monomialDeriv]
  simpa only [seriesPartial, he] using hsum.tsum_eq.symm

lemma iteratedDeriv_series_left (c : Exponent → ℂ) (R : ℝ)
    (hs : DerivativeSummable c R) (a : ℕ) (x z : ℂ)
    (hx : ‖x‖ < R) (hz : ‖z‖ < R) :
    iteratedDeriv a (fun w => seriesEval c w z) x = seriesPartial c a 0 x z := by
  induction a generalizing x with
  | zero => simp [← seriesPartial_zero]
  | succ a ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv a (fun w => seriesEval c w z) =ᶠ[𝓝 x]
        (fun w => seriesPartial c a 0 w z) := by
      filter_upwards [((continuous_norm.tendsto x).eventually (gt_mem_nhds hx))] with w hw
      exact ih w hw
    rw [he.deriv_eq]
    exact deriv_seriesPartial_left c R hs a 0 x z hx hz.le

lemma iteratedDeriv_series_right (c : Exponent → ℂ) (R : ℝ)
    (hs : DerivativeSummable c R) (a b : ℕ) (x z : ℂ)
    (hx : ‖x‖ < R) (hz : ‖z‖ < R) :
    iteratedDeriv b (fun w => seriesPartial c a 0 x w) z = seriesPartial c a b x z := by
  induction b generalizing z with
  | zero => rfl
  | succ b ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv b (fun w => seriesPartial c a 0 x w) =ᶠ[𝓝 z]
        (fun w => seriesPartial c a b x w) := by
      filter_upwards [((continuous_norm.tendsto z).eventually (gt_mem_nhds hz))] with w hw
      exact ih w hw
    rw [he.deriv_eq]
    exact deriv_seriesPartial_right c R hs a b x z hx.le hz

theorem mixedDeriv_seriesEval (c : Exponent → ℂ) (R : ℝ)
    (hs : DerivativeSummable c R) (a b : ℕ) (x z : ℂ)
    (hx : ‖x‖ < R) (hz : ‖z‖ < R) :
    iteratedDeriv b (fun v => iteratedDeriv a (fun u => seriesEval c u v) x) z =
      seriesPartial c a b x z := by
  have he : (fun v => iteratedDeriv a (fun u => seriesEval c u v) x) =ᶠ[𝓝 z]
      (fun v => seriesPartial c a 0 x v) := by
    filter_upwards [((continuous_norm.tendsto z).eventually (gt_mem_nhds hz))] with v hv
    exact iteratedDeriv_series_left c R hs a x v hx hv
  rw [he.iteratedDeriv_eq b]
  exact iteratedDeriv_series_right c R hs a b x z hx hz

lemma descFactorial_radius_le (n a : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    (n.descFactorial a : ℝ) * ρ ^ (n - a) ≤
      (n : ℝ) ^ a * (ρ ^ n / ρ ^ a) := by
  by_cases h : a ≤ n
  · have he : ρ ^ (n - a) = ρ ^ n / ρ ^ a := by
      apply (eq_div_iff (pow_ne_zero _ hρ.ne')).2
      rw [← pow_add, Nat.sub_add_cancel h]
    rw [← he]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.descFactorial_le_pow n a)
      (pow_nonneg hρ.le _)
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.cast_zero, zero_mul]
    positivity

theorem derivativeSummable_of_absolute (c : Exponent → ℂ) (R ρ : ℝ)
    (hR : 0 < R) (hρ : 0 < ρ) (hsmall : ρ < R)
    (hc : AbsolutelyConvergentAt c R) : DerivativeSummable c ρ := by
  let C : ℝ := ∑' p : Exponent, ‖c p‖ * R ^ (p.1 + p.2)
  have hC : 0 ≤ C := tsum_nonneg (fun p => by positivity)
  have hb (p : Exponent) : ‖c p‖ ≤ C / R ^ (p.1 + p.2) := by
    apply (le_div_iff₀ (pow_pos hR _)).2
    exact hc.le_tsum p (fun p _ => by positivity)
  have ht0 : 0 ≤ ρ / R := div_nonneg hρ.le hR.le
  have ht : ‖ρ / R‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg ht0]
    exact (div_lt_one hR).2 hsmall
  intro a b
  have hsum := ((summable_pow_mul_geometric_of_norm_lt_one a ht).mul_of_nonneg
    (summable_pow_mul_geometric_of_norm_lt_one b ht)
    (fun n => by positivity) (fun n => by positivity)).mul_left (C / (ρ ^ a * ρ ^ b))
  refine Summable.of_nonneg_of_le (fun p => by unfold derivativeMajorant; positivity)
    (fun p => ?_) hsum
  unfold derivativeMajorant
  calc
    _ ≤ (C / R ^ (p.1 + p.2)) *
        ((p.1 : ℝ) ^ a * (ρ ^ p.1 / ρ ^ a)) *
        ((p.2 : ℝ) ^ b * (ρ ^ p.2 / ρ ^ b)) := by
      apply mul_le_mul _ (descFactorial_radius_le p.2 b ρ hρ) (by positivity) (by positivity)
      exact mul_le_mul (hb p) (descFactorial_radius_le p.1 a ρ hρ)
        (by positivity) (by positivity)
    _ = C / (ρ ^ a * ρ ^ b) *
        ((p.1 : ℝ) ^ a * (ρ / R) ^ p.1 * ((p.2 : ℝ) ^ b * (ρ / R) ^ p.2)) := by
      rw [pow_add, div_pow, div_pow]
      ring

lemma derivativeSummable_of_norm_le (c d : Exponent → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hd : DerivativeSummable d R) (hcd : ∀ p, ‖c p‖ ≤ ‖d p‖) : DerivativeSummable c R := by
  intro a b
  refine Summable.of_nonneg_of_le (fun p => by unfold derivativeMajorant; positivity)
    (fun p => ?_) (hd a b)
  unfold derivativeMajorant
  gcongr
  exact hcd p

theorem mixedDeriv_limit_of_coefficients {α : Type*} (l : Filter α)
    (c : α → Exponent → ℂ) (c₀ d : Exponent → ℂ) (R : ℝ) (hR : 0 < R)
    (hd : DerivativeSummable d R)
    (hlim : ∀ p, Tendsto (fun v => c v p) l (𝓝 (c₀ p)))
    (hb : ∀ᶠ v in l, ∀ p, ‖c v p‖ ≤ ‖d p‖)
    (a b : ℕ) (x z : ℂ) (hx : ‖x‖ < R) (hz : ‖z‖ < R) :
    Tendsto (fun v => iteratedDeriv b (fun y => iteratedDeriv a
      (fun w => seriesEval (c v) w y) x) z) l (𝓝 (seriesPartial c₀ a b x z)) := by
  have hsum := tendsto_tsum_of_dominated_convergence (hd a b)
    (fun p => ((hlim p).mul_const (monomialDeriv p.1 a x)).mul_const
      (monomialDeriv p.2 b z))
    (hb.mono (fun v hv p => (norm_seriesTerm_le (c v) R a b p x z hx.le hz.le).trans (by
      unfold derivativeMajorant
      gcongr
      exact hv p)))
  apply hsum.congr'
  filter_upwards [hb] with v hv
  exact (mixedDeriv_seriesEval (c v) R (derivativeSummable_of_norm_le _ _ _ hR.le hd hv)
    a b x z hx hz).symm


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_WeightedRescaling
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
open scoped BigOperators Topology
open Filter Set

lemma norm_rescaleCoeff_mono (c : Exponent → ℂ) (t : ℝ) (e : Exponent)
    (he : StrictInitial c t e) (s s₀ : ℝ) (hs : 0 ≤ s) (hss : s ≤ s₀) (p : Exponent) :
    ‖rescaleCoeff c t e s p‖ ≤ ‖rescaleCoeff c t e s₀ p‖ := by
  by_cases hp : c p = 0
  · simp [rescaleCoeff, hp]
  have hw : 0 ≤ exponentWeight t p - exponentWeight t e := by
    by_cases hpe : p = e
    · simp [hpe]
    · exact (sub_pos.mpr (he.2 p hp hpe)).le
  simp only [rescaleCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hs _), abs_of_nonneg (Real.rpow_nonneg (hs.trans hss) _)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs hss hw) (norm_nonneg _)

lemma rescaleCoeff_eq_scaled (c : Exponent → ℂ) (t : ℝ) (e : Exponent)
    (s : ℝ) (hs : 0 < s) (p : Exponent) :
    rescaleCoeff c t e s p = (((s ^ exponentWeight t e)⁻¹ : ℝ) : ℂ) *
      c p * (s : ℂ) ^ p.1 * ((s ^ t : ℝ) : ℂ) ^ p.2 := by
  rw [rescaleCoeff, Real.rpow_sub hs, exponentWeight, Real.rpow_add hs,
    Real.rpow_natCast, Real.rpow_mul_natCast hs.le]
  push_cast
  ring

lemma absolute_rescaleCoeff (c : Exponent → ℂ) (t : ℝ) (e : Exponent)
    (R K s : ℝ) (hR : 0 ≤ R) (hK : 0 ≤ K) (hs : 0 < s)
    (hc : AbsolutelyConvergentAt c R) (hx : s * K ≤ R) (hz : s ^ t * K ≤ R) :
    AbsolutelyConvergentAt (rescaleCoeff c t e s) K := by
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_)
    (hc.mul_left (s ^ exponentWeight t e)⁻¹)
  rw [rescaleCoeff_eq_scaled c t e s hs, norm_mul, norm_mul, norm_mul,
    norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hs, abs_of_nonneg (Real.rpow_nonneg hs.le _),
    abs_of_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hs.le _))]
  calc
    _ = (s ^ exponentWeight t e)⁻¹ * ‖c p‖ * ((s * K) ^ p.1 * (s ^ t * K) ^ p.2) := by
      rw [pow_add, mul_pow, mul_pow]
      ring
    _ ≤ (s ^ exponentWeight t e)⁻¹ * (‖c p‖ * R ^ (p.1 + p.2)) := by
      rw [pow_add]
      calc
        _ ≤ (s ^ exponentWeight t e)⁻¹ * ‖c p‖ * (R ^ p.1 * R ^ p.2) := by
          gcongr
        _ = _ := by ring

lemma rescaleCoeff_tendsto (c : Exponent → ℂ) (t : ℝ) (e : Exponent)
    (he : StrictInitial c t e) (p : Exponent) :
    Tendsto (fun s => rescaleCoeff c t e s p) (𝓝 (0 : ℝ)) (𝓝 (initialCoeff c e p)) := by
  by_cases hp : p = e
  · subst p
    simp [rescaleCoeff, initialCoeff]
  by_cases hc : c p = 0
  · simp [rescaleCoeff, initialCoeff, hp, hc]
  have hw := sub_pos.mpr (he.2 p hc hp)
  have hr := (Real.continuous_rpow_const hw.le).tendsto (0 : ℝ)
  rw [Real.zero_rpow hw.ne'] at hr
  simpa [rescaleCoeff, initialCoeff, hp] using
    (Complex.continuous_ofReal.continuousAt.tendsto.comp hr).const_mul (c p)

lemma seriesPartial_initialCoeff (c : Exponent → ℂ) (e : Exponent) (a b : ℕ) (x z : ℂ) :
    seriesPartial (initialCoeff c e) a b x z =
      c e * monomialDeriv e.1 a x * monomialDeriv e.2 b z := by
  unfold seriesPartial
  rw [tsum_eq_single e (fun p hp => by simp [initialCoeff, hp])]
  simp [initialCoeff]

theorem mixedDeriv_rescale_tendsto (c : Exponent → ℂ) (t : ℝ) (e : Exponent)
    (ht : 0 < t) (he : StrictInitial c t e) (hc : ConvergentSeries c)
    (a b : ℕ) (x z : ℂ) :
    Tendsto (fun s => iteratedDeriv b (fun y => iteratedDeriv a
      (fun w => seriesEval (rescaleCoeff c t e s) w y) x) z)
      (𝓝[>] (0 : ℝ)) (𝓝 (c e * monomialDeriv e.1 a x * monomialDeriv e.2 b z)) := by
  obtain ⟨R, hR, hc⟩ := hc
  let K : ℝ := max ‖x‖ ‖z‖ + 1
  have hK : 0 < K := by dsimp [K] <;> positivity
  have hx : ‖x‖ < K := by dsimp [K] <;> linarith [le_max_left ‖x‖ ‖z‖]
  have hz : ‖z‖ < K := by dsimp [K] <;> linarith [le_max_right ‖x‖ ‖z‖]
  have h₁ : Tendsto (fun s : ℝ => s * (2 * K)) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa using (tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 0) (𝓝 0)).mul_const (2 * K)
  have h₂ : Tendsto (fun s : ℝ => s ^ t * (2 * K)) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa [Real.zero_rpow ht.ne'] using
      ((Real.continuous_rpow_const ht.le).tendsto (0 : ℝ)).mul_const (2 * K)
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s ∧ s * (2 * K) < R ∧ s ^ t * (2 * K) < R := by
    filter_upwards [self_mem_nhdsWithin,
        ((h₁.eventually (gt_mem_nhds hR)).filter_mono nhdsWithin_le_nhds),
        ((h₂.eventually (gt_mem_nhds hR)).filter_mono nhdsWithin_le_nhds)] with s hs h1 h2
    exact ⟨hs, h1, h2⟩
  obtain ⟨s₀, hs₀, hsx, hsz⟩ := hsmall.exists
  have habs := absolute_rescaleCoeff c t e R (2 * K) s₀ hR.le (by positivity)
    hs₀ hc hsx.le hsz.le
  have hdom := derivativeSummable_of_absolute (rescaleCoeff c t e s₀) (2 * K) K
    (by positivity) hK (by linarith) habs
  have hb : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ p,
      ‖rescaleCoeff c t e s p‖ ≤ ‖rescaleCoeff c t e s₀ p‖ := by
    filter_upwards [self_mem_nhdsWithin,
      ((eventually_lt_nhds hs₀).filter_mono nhdsWithin_le_nhds)] with s hs hss p
    exact norm_rescaleCoeff_mono c t e he s s₀ hs.le hss.le p
  simpa only [seriesPartial_initialCoeff] using
    mixedDeriv_limit_of_coefficients (𝓝[>] (0 : ℝ)) (rescaleCoeff c t e)
      (initialCoeff c e) (rescaleCoeff c t e s₀) K hK hdom
      (fun p => (rescaleCoeff_tendsto c t e he p).mono_left nhdsWithin_le_nhds)
      hb a b x z hx hz

lemma seriesEval_rescale (c : Exponent → ℂ) (t : ℝ) (e : Exponent)
    (s : ℝ) (hs : 0 < s) (x z : ℂ) :
    seriesEval (rescaleCoeff c t e s) x z =
      (((s ^ exponentWeight t e)⁻¹ : ℝ) : ℂ) *
        seriesEval c ((s : ℂ) * x) (((s ^ t : ℝ) : ℂ) * z) := by
  unfold seriesEval
  rw [← tsum_mul_left]
  apply tsum_congr
  intro p
  rw [rescaleCoeff_eq_scaled c t e s hs, mul_pow, mul_pow]
  ring

lemma iteratedDeriv_dilation (f : ℂ → ℂ) (s : ℂ) (a : ℕ) :
    iteratedDeriv a (fun x => f (s * x)) = fun x => s ^ a * iteratedDeriv a f (s * x) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [deriv_const_mul_field, deriv_comp_mul_left]
    simp only [smul_eq_mul, iteratedDeriv_succ, pow_succ]
    ring

lemma mixedDeriv_dilation (f : ℂ → ℂ → ℂ) (A s t : ℂ) (a b : ℕ) (x z : ℂ) :
    iteratedDeriv b (fun y => iteratedDeriv a (fun w => A * f (s * w) (t * y)) x) z =
      A * s ^ a * t ^ b *
        iteratedDeriv b (fun y => iteratedDeriv a (fun w => f w y) (s * x)) (t * z) := by
  have ha (y : ℂ) : iteratedDeriv a (fun w => A * f (s * w) (t * y)) x =
      A * (s ^ a * iteratedDeriv a (fun w => f w (t * y)) (s * x)) := by
    rw [iteratedDeriv_const_mul_field]
    congr 1
    exact congrFun (iteratedDeriv_dilation (fun w => f w (t * y)) s a) x
  simp_rw [ha, iteratedDeriv_const_mul_field]
  rw [congrFun (iteratedDeriv_dilation
    (fun y => iteratedDeriv a (fun w => f w y) (s * x)) t b) z]
  ring

lemma mixedDeriv_rescale (c : Exponent → ℂ) (t : ℝ) (e : Exponent)
    (s : ℝ) (hs : 0 < s) (a b : ℕ) (x z : ℂ) :
    iteratedDeriv b (fun y => iteratedDeriv a
      (fun w => seriesEval (rescaleCoeff c t e s) w y) x) z =
      (((s ^ exponentWeight t e)⁻¹ : ℝ) : ℂ) * (s : ℂ) ^ a * ((s ^ t : ℝ) : ℂ) ^ b *
        iteratedDeriv b (fun y => iteratedDeriv a (fun w => seriesEval c w y)
          ((s : ℂ) * x)) (((s ^ t : ℝ) : ℂ) * z) := by
  simp_rw [seriesEval_rescale c t e s hs]
  exact mixedDeriv_dilation _ _ _ _ _ _ _ _

lemma finiteJetColumn_const_mul (r m : ℕ) (p : Fin r → ℂ × ℂ)
    (A : ℂ) (f : ℂ → ℂ → ℂ) :
    finiteJetColumn r m p (fun x z => A * f x z) = A • finiteJetColumn r m p f := by
  funext j
  simp only [finiteJetColumn, Pi.smul_apply, smul_eq_mul]
  split_ifs
  · simp_rw [iteratedDeriv_const_mul_field]
  · simp

lemma finiteJetColumn_monomial (r m : ℕ) (p : Fin r → ℂ × ℂ)
    (e : Exponent) (j : JetIndex r m) :
    finiteJetColumn r m p (fun x z => x ^ e.1 * z ^ e.2) j =
      if j.2.1.val + j.2.2.val < m then
        monomialDeriv e.1 j.2.1 (p j.1).1 * monomialDeriv e.2 j.2.2 (p j.1).2 else 0 := by
  unfold finiteJetColumn
  simp_rw [iteratedDeriv_mul_const_field, iteratedDeriv_const_mul_field, monomialDeriv_eq]

lemma rescale_jet_limit {ι : Type*} [Finite ι] (c : ι → Exponent → ℂ)
    (e : ι → Exponent) (t : ℝ) (ht : 0 < t)
    (he : ∀ i, StrictInitial (c i) t (e i)) (hc : ∀ i, ConvergentSeries (c i))
    (r m : ℕ) (p : Fin r → ℂ × ℂ)
    (h : LinearIndependent ℂ (fun i => finiteJetColumn r m p
      (fun x z => x ^ (e i).1 * z ^ (e i).2))) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, LinearIndependent ℂ (fun i =>
      finiteJetColumn r m p (seriesEval (rescaleCoeff (c i) t (e i) s))) := by
  have hlim (i : ι) (j : JetIndex r m) :
      Tendsto (fun s => finiteJetColumn r m p
        (seriesEval (rescaleCoeff (c i) t (e i) s)) j) (𝓝[>] (0 : ℝ))
        (𝓝 (finiteJetColumn r m p
          (fun x z => c i (e i) * (x ^ (e i).1 * z ^ (e i).2)) j)) := by
    rw [finiteJetColumn_const_mul]
    simp only [Pi.smul_apply, smul_eq_mul, finiteJetColumn_monomial]
    unfold finiteJetColumn
    split_ifs with hj
    · simpa only [mul_assoc] using mixedDeriv_rescale_tendsto (c i) t (e i) ht
        (he i) (hc i) j.2.1 j.2.2 (p j.1).1 (p j.1).2
    · simp
  apply finite_jet_rank_persistence _ _ _ _ _ _ hlim
  simp_rw [finiteJetColumn_const_mul]
  simpa only [Pi.smul_def', Units.smul_def, Units.val_mk0] using
    h.units_smul (fun i => Units.mk0 (c i (e i)) (he i).1)

lemma finiteJetColumn_rescale (r m : ℕ) (p : Fin r → ℂ × ℂ)
    (c : Exponent → ℂ) (e : Exponent) (t s : ℝ) (hs : 0 < s) :
    finiteJetColumn r m p (seriesEval (rescaleCoeff c t e s)) =
      (((s ^ exponentWeight t e)⁻¹ : ℝ) : ℂ) •
        dilationJetScale r m (s : ℂ) ((s ^ t : ℝ) : ℂ)
          (finiteJetColumn r m (fun j => ((s : ℂ) * (p j).1,
            ((s ^ t : ℝ) : ℂ) * (p j).2)) (seriesEval c)) := by
  funext j
  simp only [finiteJetColumn, Pi.smul_apply, dilationJetScale, LinearMap.pi_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  split_ifs with hj
  · rw [mixedDeriv_rescale c t e s hs]
    ring
  · simp

lemma rescale_jet_rank {ι : Type*} (c : ι → Exponent → ℂ) (e : ι → Exponent)
    (t s : ℝ) (hs : 0 < s) (r m : ℕ) (p : Fin r → ℂ × ℂ)
    (h : LinearIndependent ℂ (fun i => finiteJetColumn r m p
      (seriesEval (rescaleCoeff (c i) t (e i) s)))) :
    LinearIndependent ℂ (fun i => finiteJetColumn r m
      (fun j => ((s : ℂ) * (p j).1, ((s ^ t : ℝ) : ℂ) * (p j).2)) (seriesEval (c i))) := by
  let A : ι → ℂˣ := fun i => Units.mk0 (((s ^ exponentWeight t (e i))⁻¹ : ℝ) : ℂ)
    (by exact_mod_cast inv_ne_zero (Real.rpow_pos_of_pos hs _).ne')
  simp_rw [finiteJetColumn_rescale r m p _ _ t s hs] at h
  apply LinearIndependent.of_comp (dilationJetScale r m (s : ℂ) ((s ^ t : ℝ) : ℂ))
  exact (LinearIndependent.units_smul_iff _ A).mp h

theorem initial_monomial_jet_transfer_strict {ι : Type*} [Finite ι]
    (c : ι → Exponent → ℂ) (e : ι → Exponent) (t : ℝ) (ht : 0 < t)
    (he : ∀ i, StrictInitial (c i) t (e i)) (hc : ∀ i, ConvergentSeries (c i))
    (r m : ℕ) (p : Fin r → ℂ × ℂ) (hp : Function.Injective p)
    (h : LinearIndependent ℂ (fun i => finiteJetColumn r m p
      (fun x z => x ^ (e i).1 * z ^ (e i).2))) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : Fin r → ℂ × ℂ, Function.Injective q ∧
      (∀ j, ‖(q j).1‖ < ε ∧ ‖(q j).2‖ < ε) ∧
      LinearIndependent ℂ (fun i => finiteJetColumn r m q (seriesEval (c i))) := by
  have hl := rescale_jet_limit c e t ht he hc r m p h
  have hx (j : Fin r) : Tendsto (fun s : ℝ => (s : ℂ) * (p j).1)
      (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa using (Complex.continuous_ofReal.tendsto (0 : ℝ)).mul_const (p j).1
  have hz (j : Fin r) : Tendsto (fun s : ℝ => ((s ^ t : ℝ) : ℂ) * (p j).2)
      (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hr := (Real.continuous_rpow_const ht.le).tendsto (0 : ℝ)
    simpa [Real.zero_rpow ht.ne'] using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hr).mul_const (p j).2
  have hnear : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ j : Fin r,
      ‖(s : ℂ) * (p j).1‖ < ε ∧ ‖((s ^ t : ℝ) : ℂ) * (p j).2‖ < ε := by
    apply Filter.eventually_all.mpr
    intro j
    filter_upwards [(((hx j).norm.eventually
      (by simpa using gt_mem_nhds hε)).filter_mono nhdsWithin_le_nhds),
      (((hz j).norm.eventually (by simpa using gt_mem_nhds hε)).filter_mono
        nhdsWithin_le_nhds)] with s hs ht
    exact ⟨hs, ht⟩
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  obtain ⟨s, hs, hli, hn⟩ := (hpos.and (hl.and hnear)).exists
  refine ⟨fun j => ((s : ℂ) * (p j).1, ((s ^ t : ℝ) : ℂ) * (p j).2), ?_, hn,
    rescale_jet_rank c e t s hs r m p hli⟩
  intro i j hij
  apply hp
  apply Prod.ext
  · exact mul_left_cancel₀ (by exact_mod_cast hs.ne') (congrArg Prod.fst hij)
  · exact mul_left_cancel₀ (by exact_mod_cast (Real.rpow_pos_of_pos hs t).ne')
      (congrArg Prod.snd hij)


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_InitialBasis
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
open scoped BigOperators Topology
open Filter Set

theorem exists_commonDerivativeRadius (V : Submodule ℂ (Exponent → ℂ))
    [FiniteDimensional ℂ V] (hc : ∀ c ∈ V, ConvergentSeries c) :
    ∃ R : ℝ, 0 < R ∧ ∀ c ∈ V, DerivativeSummable c R := by
  classical
  let b := Module.finBasis ℂ V
  have hh (i : Fin (Module.finrank ℂ V)) : ConvergentSeries (b i : Exponent → ℂ) :=
    hc _ (b i).property
  choose ρ hρ ha using hh
  have he : ∀ᶠ R : ℝ in 𝓝[>] 0, ∀ i, R < ρ i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (gt_mem_nhds (hρ i)).filter_mono nhdsWithin_le_nhds
  have hp : ∀ᶠ R : ℝ in 𝓝[>] 0, 0 < R := self_mem_nhdsWithin
  obtain ⟨R, hR, hRi⟩ := (hp.and he).exists
  have hb (i) : DerivativeSummable (b i : Exponent → ℂ) R :=
    derivativeSummable_of_absolute _ (ρ i) R (hρ i) hR (hRi i) (ha i)
  refine ⟨R, hR, ?_⟩
  intro c hcV
  let f : V := ⟨c, hcV⟩
  let D := derivativeSeriesSubmodule R hR.le
  have hm : ((∑ i, b.repr f i • b i : V) : Exponent → ℂ) ∈ D := by
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact D.sum_mem (fun i _ => D.smul_mem _ (hb i))
  change DerivativeSummable ((∑ i, b.repr f i • b i : V) : Exponent → ℂ) R at hm
  simpa only [b.sum_repr f] using hm

lemma seriesJetMap_eq (V : Submodule ℂ (Exponent → ℂ)) (R : ℝ)
    (hs : ∀ c ∈ V, DerivativeSummable c R) (r m : ℕ) (p : Fin r → ℂ × ℂ)
    (hp : ∀ j, ‖(p j).1‖ < R ∧ ‖(p j).2‖ < R) (f : V) :
    seriesJetMap V R hs r m p hp f = finiteJetColumn r m p (seriesEval f) := by
  ext j
  simp only [seriesJetMap, LinearMap.pi_apply, finiteJetColumn]
  split_ifs
  · exact (mixedDeriv_seriesEval f R (hs f f.property) j.2.1 j.2.2
      (p j.1).1 (p j.1).2 (hp j.1).1 (hp j.1).2).symm
  · rfl

lemma exponentWeight_nonneg (t : ℝ) (ht : 0 ≤ t) (p : Exponent) :
    0 ≤ exponentWeight t p := by unfold exponentWeight; positivity

lemma exponentWeight_mono (t u : ℝ) (htu : t ≤ u) (p : Exponent) :
    exponentWeight t p ≤ exponentWeight u p := by
  unfold exponentWeight
  gcongr

lemma continuous_exponentWeight (p : Exponent) : Continuous (fun t => exponentWeight t p) := by
  unfold exponentWeight
  fun_prop

lemma finite_boundedWeight (t M : ℝ) (ht : 0 < t) :
    {p : Exponent | exponentWeight t p < M}.Finite := by
  refine (Set.finite_Iic (⟨⌈M⌉₊, ⌈M / t⌉₊⟩ : Exponent)).subset ?_
  intro p hp
  change p.1 ≤ ⌈M⌉₊ ∧ p.2 ≤ ⌈M / t⌉₊
  have hp' : (p.1 : ℝ) + t * p.2 < M := hp
  have h1 : (p.1 : ℝ) ≤ M := by nlinarith [Nat.cast_nonneg (α := ℝ) p.2]
  have h2 : (p.2 : ℝ) ≤ M / t := by
    apply (le_div_iff₀ ht).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) p.1]
  exact ⟨(Nat.cast_le (α := ℝ)).mp (h1.trans (Nat.le_ceil M)),
    (Nat.cast_le (α := ℝ)).mp (h2.trans (Nat.le_ceil (M / t)))⟩

lemma LexInitial.beta_lt_of_eq_weight {c : Exponent → ℂ} {t : ℝ} {e p : Exponent}
    (he : LexInitial c t e) (hp : c p ≠ 0) (hne : p ≠ e)
    (hw : exponentWeight t e = exponentWeight t p) : e.2 < p.2 := by
  have hle := (he.2 p hp).2 hw
  refine lt_of_le_of_ne hle ?_
  intro hβ
  apply hne
  apply Prod.ext
  · have hα : (e.1 : ℝ) = p.1 := by simpa [exponentWeight, hβ] using hw
    exact (Nat.cast_inj.mp hα).symm
  · exact hβ.symm

theorem exists_strictWeight_of_lex {ι : Type*} [Finite ι]
    (c : ι → Exponent → ℂ) (e : ι → Exponent) (t : ℝ) (ht : 0 < t)
    (he : ∀ i, LexInitial (c i) t (e i)) :
    ∃ u : ℝ, t < u ∧ ∀ i, StrictInitial (c i) u (e i) := by
  classical
  let := Fintype.ofFinite ι
  let M : ℝ := 1 + ∑ i, exponentWeight t (e i)
  have hem (i : ι) : exponentWeight t (e i) < M := by
    have hh := Finset.single_le_sum (f := fun i => exponentWeight t (e i))
      (fun i _ => exponentWeight_nonneg t ht.le (e i)) (Finset.mem_univ i)
    dsimp [M]
    linarith
  let B : Set Exponent := {p | exponentWeight t p < M}
  have hB : B.Finite := finite_boundedWeight t M ht
  let := hB.fintype
  have hlow : ∀ᶠ u : ℝ in 𝓝[>] t, ∀ i : ι, ∀ p : B,
      c i p ≠ 0 → (p : Exponent) ≠ e i → exponentWeight u (e i) < exponentWeight u p := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro p
    by_cases hp : c i p = 0
    · exact Filter.Eventually.of_forall (fun _ h => (h hp).elim)
    by_cases hpe : (p : Exponent) = e i
    · exact Filter.Eventually.of_forall (fun _ _ h => (h hpe).elim)
    by_cases hw : exponentWeight t (e i) < exponentWeight t p
    · have hh : Continuous (fun u => exponentWeight u p - exponentWeight u (e i)) :=
        (continuous_exponentWeight p).sub (continuous_exponentWeight (e i))
      filter_upwards [((hh.tendsto t).eventually (lt_mem_nhds (sub_pos.mpr hw))).filter_mono
          nhdsWithin_le_nhds] with u hu _ _
      exact sub_pos.mp hu
    · have heq := le_antisymm (he i |>.2 p hp).1 (le_of_not_gt hw)
      have hβ := (he i).beta_lt_of_eq_weight hp hpe heq
      filter_upwards [self_mem_nhdsWithin] with u hu _ _
      have hβR : ((e i).2 : ℝ) < (p : Exponent).2 := by exact_mod_cast hβ
      have hmul := mul_pos (sub_pos.mpr hu) (sub_pos.mpr hβR)
      dsimp [exponentWeight] at heq ⊢
      nlinarith
  have hbelow : ∀ᶠ u : ℝ in 𝓝[>] t, ∀ i : ι, exponentWeight u (e i) < M := by
    apply Filter.eventually_all.mpr
    intro i
    exact (((continuous_exponentWeight (e i)).tendsto t).eventually
      (gt_mem_nhds (hem i))).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ u : ℝ in 𝓝[>] t, t < u := self_mem_nhdsWithin
  obtain ⟨u, htu, hlu, hbu⟩ := (hpos.and (hlow.and hbelow)).exists
  refine ⟨u, htu, fun i => ⟨(he i).1, ?_⟩⟩
  intro p hp hpe
  by_cases hpb : p ∈ B
  · exact hlu i ⟨p, hpb⟩ hp hpe
  · have hM : M ≤ exponentWeight t p := le_of_not_gt hpb
    exact (hbu i).trans_le (hM.trans (exponentWeight_mono t u htu.le p))

lemma lexKey_le_iff (t : ℝ) (p q : Exponent) :
    lexKey t p ≤ lexKey t q ↔ exponentWeight t p ≤ exponentWeight t q ∧
      (exponentWeight t p = exponentWeight t q → p.2 ≤ q.2) :=
  Prod.Lex.toLex_le_toLex'

lemma lexKey_injective (t : ℝ) : Function.Injective (lexKey t) := by
  intro p q h
  have hy : p.2 = q.2 := congrArg (fun z : ℝ ×ₗ ℕ => (ofLex z).2) h
  have hw : exponentWeight t p = exponentWeight t q :=
    congrArg (fun z : ℝ ×ₗ ℕ => (ofLex z).1) h
  apply Prod.ext
  · have hα : (p.1 : ℝ) = q.1 := by simpa [exponentWeight, hy] using hw
    exact Nat.cast_inj.mp hα
  · exact hy

lemma LexInitial.key_le {c : Exponent → ℂ} {t : ℝ} {e : Exponent}
    (h : LexInitial c t e) {p : Exponent} (hp : c p ≠ 0) :
    lexKey t e ≤ lexKey t p := (lexKey_le_iff t e p).mpr (h.2 p hp)

theorem exists_lexInitial (c : Exponent → ℂ) (t : ℝ) (ht : 0 < t)
    (hc : c ≠ 0) : ∃ e, LexInitial c t e := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, c p ≠ 0 := by
    by_contra! h
    exact hc (funext h)
  let B : Set Exponent := {q | c q ≠ 0 ∧ exponentWeight t q < exponentWeight t p + 1}
  have hB : B.Finite :=
    (finite_boundedWeight t (exponentWeight t p + 1) ht).subset fun _ h => h.2
  have hpB : p ∈ B := ⟨hp, lt_add_one _⟩
  obtain ⟨e, heB, he⟩ := Set.exists_min_image B (lexKey t) hB ⟨p, hpB⟩
  refine ⟨e, heB.1, fun q hq => (lexKey_le_iff t e q).mp ?_⟩
  by_cases hqB : q ∈ B
  · exact he q hqB
  · have hqp : exponentWeight t p + 1 ≤ exponentWeight t q := by
      by_contra! h
      exact hqB ⟨hq, h⟩
    have hep := ((lexKey_le_iff t e p).mp (he p hpB)).1
    apply Prod.Lex.toLex_le_toLex.mpr
    exact Or.inl (by dsimp [lexKey] <;> linarith)

theorem linearIndependent_of_lexInitial {ι : Type*} (c : ι → Exponent → ℂ)
    (e : ι → Exponent) (t : ℝ) (he : ∀ i, LexInitial (c i) t (e i))
    (hinj : Function.Injective e) : LinearIndependent ℂ c := by
  classical
  rw [linearIndependent_iff']
  intro s a hsum i hi
  by_contra hai
  let A := s.filter (fun j => a j ≠ 0)
  have hAi : i ∈ A := Finset.mem_filter.mpr ⟨hi, hai⟩
  obtain ⟨j, hjA, hj⟩ := A.exists_min_image (fun j => lexKey t (e j)) ⟨i, hAi⟩
  have hjS := (Finset.mem_filter.mp hjA).1
  have haj := (Finset.mem_filter.mp hjA).2
  have hzero (l : ι) (hl : l ∈ s) (hlj : l ≠ j) : a l * c l (e j) = 0 := by
    by_cases hal : a l = 0
    · simp [hal]
    have hlA : l ∈ A := Finset.mem_filter.mpr ⟨hl, hal⟩
    have hcl : c l (e j) = 0 := by
      by_contra hcl
      have hkey := le_antisymm (hj l hlA) ((he l).key_le hcl)
      have hej : e j = e l := lexKey_injective t hkey
      exact hlj (hinj hej).symm
    simp [hcl]
  have hs : (∑ l ∈ s, a l * c l (e j)) = a j * c j (e j) := by
    exact Finset.sum_eq_single j hzero (fun h => (h hjS).elim)
  have hh := congrFun hsum (e j)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hh
  rw [hs] at hh
  exact (mul_ne_zero haj (he j).1) hh


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_Moments
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MaximalSeshadri.Interpolation

open scoped BigOperators Pointwise

theorem planeForm_nonneg_on_hull (a b c : ℝ) (s : Set (ℝ × ℝ))
    (h : ∀ p ∈ s, 0 ≤ planeForm a b c p) :
    ∀ p ∈ convexHull ℝ s, 0 ≤ planeForm a b c p := by
  have hconv : Convex ℝ {p : ℝ × ℝ | 0 ≤ planeForm a b c p} := by
    intro p hp q hq u v hu hv huv
    change 0 ≤ a * (u * p.1 + v * q.1) + b * (u * p.2 + v * q.2) + c
    have hmul := add_nonneg (mul_nonneg hu hp) (mul_nonneg hv hq)
    dsimp [planeForm] at hmul
    calc
      0 ≤ u * (a * p.1 + b * p.2 + c) + v * (a * q.1 + b * q.2 + c) := hmul
      _ = a * (u * p.1 + v * q.1) + b * (u * p.2 + v * q.2) + c := by
        nlinarith [congrArg (fun z : ℝ => z * c) huv]
  exact convexHull_min h hconv


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_TriangleJets
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise

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


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_LaurentMoments
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

theorem contDiffAt_zpow_ne_zero (q : ℤ) (w : ℂ) (hw : w ≠ 0) (n : WithTop ℕ∞) :
    ContDiffAt ℂ n (fun u : ℂ => u ^ q) w :=
  (analyticAt_id.zpow hw).contDiffAt

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


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_RowCompression
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology

theorem compression_column_mem_span {Q : Type*} [Fintype Q]
    (q : Q → ℤ) (B n : Q → ℕ) (r m : ℕ) (points : Fin r → ℂ × ℂ)
    (s : ℂ) (hs : s ≠ 0) (i : RowIndex n) :
    finiteJetColumn r m points (fun u z => u ^ q i.1 *
      ((1 + s * z) ^ B i.1 * z ^ (i.2 : ℕ))) ∈
      Submodule.span ℂ (Set.range fun j : RowIndex n => finiteJetColumn r m points
        (fun u z => u ^ q j.1 * (1 + s * z) ^ (B j.1 + (j.2 : ℕ)))) := by
  let L := (polynomialJetMap r m points (q i.1)).comp (compressionRowMap s (B i.1))
  have hp := polynomial_image_mem_span L
    ((Polynomial.C s⁻¹ * (Polynomial.X - 1)) ^ (i.2 : ℕ)) (n i.1)
    ((compression_inverse_degree s i.2).trans (by omega))
  have hv : L ((Polynomial.C s⁻¹ * (Polynomial.X - 1)) ^ (i.2 : ℕ)) =
      finiteJetColumn r m points (fun u z => u ^ q i.1 *
        ((1 + s * z) ^ B i.1 * z ^ (i.2 : ℕ))) := by
    dsimp only [L, LinearMap.comp_apply]
    rw [compressionRowMap_inverse s hs, polynomialJetMap_eq]
    congr 1
    funext u z
    simp
  rw [hv] at hp
  apply (Submodule.span_mono ?_) hp
  rintro _ ⟨j, rfl⟩
  refine ⟨⟨i.1, j⟩, ?_⟩
  dsimp only [L, LinearMap.comp_apply]
  rw [compressionRowMap_pow, polynomialJetMap_eq]
  congr 1
  funext u z
  simp

theorem compression_rank_to_powers {Q : Type*} [Fintype Q]
    (q : Q → ℤ) (B n : Q → ℕ) (r m : ℕ) (points : Fin r → ℂ × ℂ)
    (s : ℂ) (hs : s ≠ 0)
    (h : LinearIndependent ℂ (fun i : RowIndex n => finiteJetColumn r m points
      (fun u z => u ^ q i.1 * ((1 + s * z) ^ B i.1 * z ^ (i.2 : ℕ))))) :
    LinearIndependent ℂ (fun i : RowIndex n => finiteJetColumn r m points
      (fun u z => u ^ q i.1 * (1 + s * z) ^ (B i.1 + (i.2 : ℕ)))) := by
  apply linearIndependent_of_span_le _ _ h
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact compression_column_mem_span q B n r m points s hs i

theorem iteratedDeriv_affine_pow (s : ℂ) (b N : ℕ) :
    iteratedDeriv b (fun z : ℂ => (1 + s * z) ^ N) =
      fun z => s ^ b * iteratedDeriv b (fun z : ℂ => z ^ N) (1 + s * z) := by
  have hd : ContDiff ℂ (b : ℕ∞ω) (fun z : ℂ => (1 + z) ^ N) := by fun_prop
  rw [show (fun z : ℂ => (1 + s * z) ^ N) =
    (fun z : ℂ => (fun y : ℂ => (1 + y) ^ N) (s * z)) by rfl,
    iteratedDeriv_comp_const_mul hd s]
  funext z
  congr 1
  exact congrFun (iteratedDeriv_comp_const_add b (fun z : ℂ => z ^ N) 1) (s * z)

theorem verticalJetScale_column (r m : ℕ) (points : Fin r → ℂ × ℂ)
    (s : ℂ) (q : ℤ) (N : ℕ) :
    verticalJetScale r m s
      (finiteJetColumn r m (fun i => ((points i).1, 1 + s * (points i).2))
        (fun u z => u ^ q * z ^ N)) =
      finiteJetColumn r m points (fun u z => u ^ q * (1 + s * z) ^ N) := by
  funext j
  simp only [verticalJetScale, LinearMap.pi_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, finiteJetColumn]
  split_ifs
  · simp only [mixed_deriv_separated, iteratedDeriv_affine_pow]
    ring
  · exact mul_zero _

theorem compression_powers_to_original {Q : Type*} [Fintype Q]
    (q : Q → ℤ) (B n : Q → ℕ) (r m : ℕ) (points : Fin r → ℂ × ℂ) (s : ℂ)
    (h : LinearIndependent ℂ (fun i : RowIndex n => finiteJetColumn r m points
      (fun u z => u ^ q i.1 * (1 + s * z) ^ (B i.1 + (i.2 : ℕ))))) :
    LinearIndependent ℂ (fun i : RowIndex n =>
      finiteJetColumn r m (fun i => ((points i).1, 1 + s * (points i).2))
        (fun u z => u ^ q i.1 * z ^ (B i.1 + (i.2 : ℕ)))) := by
  apply LinearIndependent.of_comp (verticalJetScale r m s)
  simpa only [Function.comp_def, verticalJetScale_column] using h

theorem affine_vertical_tuple_injective {r : ℕ} (points : Fin r → ℂ × ℂ)
    (hi : Function.Injective points) (s : ℂ) (hs : s ≠ 0) :
    Function.Injective (fun i => ((points i).1, 1 + s * (points i).2)) := by
  intro i j hij
  apply hi
  apply Prod.ext
  · simpa only using congrArg (fun p : ℂ × ℂ => p.1) hij
  · have h := congrArg Prod.snd hij
    exact (mul_left_cancel₀ hs) (add_left_cancel h)

theorem compression_exists_tuple {Q : Type*} [Fintype Q]
    (q : Q → ℤ) (B n : Q → ℕ) (r m : ℕ) (points : Fin r → ℂ × ℂ)
    (hi : Function.Injective points) (hnz : ∀ i, (points i).1 ≠ 0)
    (h₀ : LinearIndependent ℂ (fun i : RowIndex n => finiteJetColumn r m points
      (fun u z => u ^ q i.1 * z ^ (i.2 : ℕ)))) :
    ∃ p : Fin r → ℂ × ℂ, Function.Injective p ∧
      (∀ i, (p i).1 ≠ 0 ∧ (p i).2 ≠ 0) ∧
      LinearIndependent ℂ (fun i : RowIndex n => finiteJetColumn r m p
        (fun u z => u ^ q i.1 * z ^ (B i.1 + (i.2 : ℕ)))) := by
  have hrank := compression_finite_rank (fun i : RowIndex n => q i.1)
    (fun i => B i.1) (fun i => (i.2 : ℕ)) r m points h₀
  have hn : ∀ᶠ s : ℂ in 𝓝 0, ∀ i, 1 + s * (points i).2 ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    have ht : Tendsto (fun s : ℂ => 1 + s * (points i).2) (𝓝 0) (𝓝 1) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℂ => (1 : ℂ)) (𝓝 0) (𝓝 1)).add
        ((tendsto_id : Tendsto (id : ℂ → ℂ) (𝓝 0) (𝓝 0)).mul_const (points i).2)
    exact ht.eventually_ne one_ne_zero
  have he : ∀ᶠ s : ℂ in 𝓝[≠] 0, s ≠ 0 := eventually_mem_nhdsWithin
  obtain ⟨s, hs, hrank, hn⟩ := (he.and
    ((hrank.and hn).filter_mono nhdsWithin_le_nhds)).exists
  refine ⟨(fun i => ((points i).1, 1 + s * (points i).2)),
    affine_vertical_tuple_injective points hi s hs, ?_, ?_⟩
  · intro i
    exact ⟨hnz i, hn i⟩
  · exact compression_powers_to_original q B n r m points s
      (compression_rank_to_powers q B n r m points s hs hrank)


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_LaurentJets
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
theorem MomentJetZero.polynomials {ι : Type*} (s : Finset ι) (c x y : ι → ℂ)
    (m : ℕ) (h : MomentJetZero s c x y m) (P Q : Polynomial ℂ)
    (hdeg : P.natDegree + Q.natDegree < m) :
    ∑ i ∈ s, c i * P.eval (x i) * Q.eval (y i) = 0 := by
  classical
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a ha
  have hab : a + b < m := (Nat.add_le_add
    (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp ha))
    (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hb))).trans_lt hdeg
  calc
    (∑ i ∈ s, c i * (P.coeff a * x i ^ a) * (Q.coeff b * y i ^ b)) =
        (P.coeff a * Q.coeff b) * ∑ i ∈ s, c i * x i ^ a * y i ^ b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [h a b hab, mul_zero]

theorem momentJetZero_of_falling {ι : Type*} (s : Finset ι) (c x y : ι → ℂ)
    (m : ℕ) (h : ∀ a b : ℕ, a + b < m →
      ∑ i ∈ s, c i * (descPochhammer ℂ a).eval (x i) *
        (descPochhammer ℂ b).eval (y i) = 0) : MomentJetZero s c x y m := by
  intro a b hab
  let L : Polynomial ℂ →ₗ[ℂ] ℂ := ∑ i ∈ s, (c i * y i ^ b) • Polynomial.leval (x i)
  have hl (j : ℕ) (hj : j ≤ a) : L (descPochhammer ℂ j) = 0 := by
    let M : Polynomial ℂ →ₗ[ℂ] ℂ := ∑ i ∈ s,
      (c i * (descPochhammer ℂ j).eval (x i)) • Polynomial.leval (y i)
    have hm (l : ℕ) (hl : l ≤ b) : M (descPochhammer ℂ l) = 0 := by
      simpa [M] using h j l (by omega)
    have he := linearMap_zero_power_of_falling M b hm
    simpa [L, M, mul_assoc, mul_left_comm, mul_comm] using he
  have he := linearMap_zero_power_of_falling L a hl
  simpa [L, mul_assoc, mul_left_comm, mul_comm] using he

theorem indexedLaurent_mixed_deriv {ι : Type*} (s : Finset ι) (e : ι → ℤ × ℤ)
    (c : ι → ℂ) (u z : ℂ) (hu : u ≠ 0) (hz : z ≠ 0) (a b : ℕ) :
    iteratedDeriv b (fun v => iteratedDeriv a (fun w => indexedLaurent s e c w v) u) z =
      ∑ i ∈ s, c i * (descPochhammer ℂ a).eval ((e i).1 : ℂ) *
        u ^ ((e i).1 - (a : ℤ)) * (descPochhammer ℂ b).eval ((e i).2 : ℂ) *
          z ^ ((e i).2 - (b : ℤ)) := by
  have hi (v : ℂ) : iteratedDeriv a (fun w => indexedLaurent s e c w v) u =
      ∑ i ∈ s, c i * (descPochhammer ℂ a).eval ((e i).1 : ℂ) *
        u ^ ((e i).1 - (a : ℤ)) * v ^ (e i).2 := by
    unfold indexedLaurent
    rw [iteratedDeriv_fun_sum (fun i _ =>
      (contDiffAt_const.mul (contDiffAt_zpow_ne_zero (e i).1 u hu a)).mul contDiffAt_const)]
    apply Finset.sum_congr rfl
    intro i _
    rw [iteratedDeriv_mul_const_field, iteratedDeriv_const_mul_field,
      iteratedDeriv_eq_iterate, iter_deriv_zpow, descPochhammer_eval_eq_prod_range]
    ring
  simp_rw [hi]
  rw [iteratedDeriv_fun_sum (fun i _ =>
    contDiffAt_const.mul (contDiffAt_zpow_ne_zero (e i).2 z hz b))]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_zpow]
  simp_rw [descPochhammer_eval_eq_prod_range]
  ring

theorem indexedLaurent_deriv_scaled {ι : Type*} (s : Finset ι) (e : ι → ℤ × ℤ)
    (c : ι → ℂ) (u z : ℂ) (hu : u ≠ 0) (hz : z ≠ 0) (a b : ℕ) :
    (iteratedDeriv b (fun v => iteratedDeriv a (fun w => indexedLaurent s e c w v) u) z) *
      (u ^ a * z ^ b) =
      ∑ i ∈ s, (c i * u ^ (e i).1 * z ^ (e i).2) *
        (descPochhammer ℂ a).eval ((e i).1 : ℂ) *
        (descPochhammer ℂ b).eval ((e i).2 : ℂ) := by
  rw [indexedLaurent_mixed_deriv s e c u z hu hz, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [zpow_sub₀ hu, zpow_sub₀ hz, zpow_natCast, zpow_natCast]
  field_simp

theorem indexedLaurent_jet_iff_moments {ι : Type*} (s : Finset ι) (e : ι → ℤ × ℤ)
    (c : ι → ℂ) (u z : ℂ) (hu : u ≠ 0) (hz : z ≠ 0) (m : ℕ) :
    MixedJetZero (indexedLaurent s e c) u z m ↔
      MomentJetZero s (fun i => c i * u ^ (e i).1 * z ^ (e i).2)
        (fun i => ((e i).1 : ℂ)) (fun i => ((e i).2 : ℂ)) m := by
  constructor
  · intro hj
    apply momentJetZero_of_falling
    intro a b hab
    rw [← indexedLaurent_deriv_scaled s e c u z hu hz, hj a b hab, zero_mul]
  · intro hm a b hab
    have hh := hm.polynomials s _ _ _ m (descPochhammer ℂ a) (descPochhammer ℂ b)
      (by simpa only [descPochhammer_natDegree] using hab)
    rw [← indexedLaurent_deriv_scaled s e c u z hu hz] at hh
    exact (mul_eq_zero.mp hh).resolve_right (mul_ne_zero (pow_ne_zero a hu) (pow_ne_zero b hz))

theorem finiteJetColumn_indexedLaurent {ι : Type*} (s : Finset ι)
    (e : ι → ℤ × ℤ) (c : ι → ℂ) (r m : ℕ) (points : Fin r → ℂ × ℂ)
    (hnz : ∀ i, (points i).1 ≠ 0 ∧ (points i).2 ≠ 0) :
    finiteJetColumn r m points (indexedLaurent s e c) =
      ∑ i ∈ s, c i • finiteJetColumn r m points
        (fun u z => u ^ (e i).1 * z ^ (e i).2) := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, finiteJetColumn]
  split_ifs with hab
  · rw [indexedLaurent_mixed_deriv s e c _ _ (hnz j.1).1 (hnz j.1).2]
    apply Finset.sum_congr rfl
    intro i _
    rw [mixed_deriv_separated (fun u : ℂ => u ^ (e i).1)
      (fun z : ℂ => z ^ (e i).2)]
    simp only [iteratedDeriv_eq_iterate, iter_deriv_zpow,
      descPochhammer_eval_eq_prod_range]
    ring
  · simp

theorem finiteJetColumn_eq_zero_iff (r m : ℕ) (points : Fin r → ℂ × ℂ)
    (f : ℂ → ℂ → ℂ) :
    finiteJetColumn r m points f = 0 ↔ ∀ i, MixedJetZero f (points i).1 (points i).2 m := by
  constructor
  · intro h i a b hab
    have ha : a < m := by omega
    have hb : b < m := by omega
    have he := congrFun h (i, ⟨a, ha⟩, ⟨b, hb⟩)
    simpa only [finiteJetColumn, hab, ite_true, if_true, Pi.zero_apply] using he
  · intro h
    funext j
    simp only [finiteJetColumn, Pi.zero_apply]
    split_ifs with hab
    · exact h j.1 j.2.1 j.2.2 hab
    · rfl

theorem shear_monomial (u v : ℂ) (hu : u ≠ 0) (a b : ℤ) :
    u ^ (a + b) * (v / u) ^ b = u ^ a * v ^ b := by
  rw [zpow_add₀ hu, div_zpow]
  field_simp

theorem shearLaurent_jet {ι : Type*} (s : Finset ι) (e : ι → ℤ × ℤ) (c : ι → ℂ)
    (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) (m : ℕ)
    (h : MixedJetZero (indexedLaurent s (fun i => ((e i).1 + (e i).2, (e i).2)) c)
      u (v / u) m) : MixedJetZero (indexedLaurent s e c) u v m := by
  have hm := (indexedLaurent_jet_iff_moments s _ c u (v / u) hu
    (div_ne_zero hv hu) m).mp h
  have hc (i : ι) : c i * u ^ ((e i).1 + (e i).2) * (v / u) ^ (e i).2 =
      c i * u ^ (e i).1 * v ^ (e i).2 := by
    rw [mul_assoc, shear_monomial u v hu, ← mul_assoc]
  simp only [hc, Int.cast_add] at hm
  have hf := MomentJetZero.affine s _ _ _ m hm 1 (-1) 0 0 1 0
  apply (indexedLaurent_jet_iff_moments s e c u v hu hv m).mpr
  simpa only [one_mul, neg_one_mul, add_zero, zero_mul, zero_add, add_neg_cancel_right] using hf

theorem shear_tuple_injective {r : ℕ} (points : Fin r → ℂ × ℂ)
    (hi : Function.Injective points) (hnz : ∀ i, (points i).1 ≠ 0) :
    Function.Injective (fun i => ((points i).1, (points i).2 / (points i).1)) := by
  intro i j hij
  have h1 : (points i).1 = (points j).1 := by
    simpa only using congrArg (fun p : ℂ × ℂ => p.1) hij
  have h2 : (points i).2 / (points i).1 = (points j).2 / (points j).1 :=
    congrArg (fun p : ℂ × ℂ => p.2) hij
  rw [h1] at h2
  exact hi (Prod.ext h1 ((div_left_inj' (hnz j)).mp h2))

theorem shear_jet_rank {ι : Type*} (e : ι → ℤ × ℤ) (r m : ℕ)
    (points : Fin r → ℂ × ℂ) (hnz : ∀ i, (points i).1 ≠ 0 ∧ (points i).2 ≠ 0)
    (h : LinearIndependent ℂ (fun i => finiteJetColumn r m points
      (fun u z => u ^ (e i).1 * z ^ (e i).2))) :
    LinearIndependent ℂ (fun i => finiteJetColumn r m
      (fun l => ((points l).1, (points l).2 / (points l).1))
        (fun x z => x ^ ((e i).1 + (e i).2) * z ^ (e i).2)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc i hi
  have hpn : ∀ l, (points l).1 ≠ 0 ∧ (points l).2 / (points l).1 ≠ 0 :=
    fun l => ⟨(hnz l).1, div_ne_zero (hnz l).2 (hnz l).1⟩
  have hz : finiteJetColumn r m
      (fun l => ((points l).1, (points l).2 / (points l).1))
      (indexedLaurent s (fun i => ((e i).1 + (e i).2, (e i).2)) c) = 0 := by
    rw [finiteJetColumn_indexedLaurent s _ c r m _ hpn]
    exact hc
  have hz' : finiteJetColumn r m points (indexedLaurent s e c) = 0 := by
    apply (finiteJetColumn_eq_zero_iff r m points _).mpr
    intro l
    exact shearLaurent_jet s e c _ _ (hnz l).1 (hnz l).2 m
      ((finiteJetColumn_eq_zero_iff r m _ _).mp hz l)
  rw [finiteJetColumn_indexedLaurent s e c r m points hnz] at hz'
  exact linearIndependent_iff'.mp h s c hz' i hi

theorem diagonal_row_compression {Q : Type*} [Fintype Q]
    (q : Q → ℤ) (B n : Q → ℕ) (r m : ℕ) (points : Fin r → ℂ × ℂ)
    (hi : Function.Injective points) (hnz : ∀ i, (points i).1 ≠ 0)
    (h₀ : LinearIndependent ℂ (fun i : RowIndex n => finiteJetColumn r m points
      (fun u z => u ^ q i.1 * z ^ (i.2 : ℕ)))) :
    ∃ p : Fin r → ℂ × ℂ, Function.Injective p ∧
      (∀ i, (p i).1 ≠ 0 ∧ (p i).2 ≠ 0) ∧
      LinearIndependent ℂ (fun i : RowIndex n => finiteJetColumn r m p
        (fun x z => x ^ (q i.1 + ((B i.1 + (i.2 : ℕ) : ℕ) : ℤ)) *
          z ^ (B i.1 + (i.2 : ℕ)))) := by
  obtain ⟨p, hpi, hpn, hp⟩ := compression_exists_tuple q B n r m points hi hnz h₀
  let e : RowIndex n → ℤ × ℤ := fun i => (q i.1, (B i.1 + (i.2 : ℕ) : ℕ))
  have hp' : LinearIndependent ℂ (fun i => finiteJetColumn r m p
      (fun u z => u ^ (e i).1 * z ^ (e i).2)) := by
    simpa only [e, zpow_natCast] using hp
  refine ⟨(fun l => ((p l).1, (p l).2 / (p l).1)),
    shear_tuple_injective p hpi (fun i => (hpn i).1), ?_, ?_⟩
  · intro i
    exact ⟨(hpn i).1, div_ne_zero (hpn i).2 (hpn i).1⟩
  · simpa only [e, zpow_natCast] using shear_jet_rank e r m p hpn hp'

theorem indexedLaurent_nonzeroSupport {ι : Type*} (s : Finset ι)
    (e : ι → ℤ × ℤ) (c : ι → ℂ) :
    indexedLaurent (s.filter (fun i => c i ≠ 0)) e c = indexedLaurent s e c := by
  classical
  funext u z
  simp only [indexedLaurent, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h <;> simp_all

theorem indexedLaurent_image {ι : Type*} [Nonempty ι] (s : Finset ι)
    (e : ι → ℤ × ℤ) (c : ι → ℂ) (he : Set.InjOn e s) :
    indexedLaurent s e c = laurentEval (s.image e) (c ∘ Function.invFunOn e s) := by
  classical
  funext u z
  rw [laurentEval_eq_sum, Finset.sum_image (fun i hi j hj hij => he hi hj hij)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Function.comp_apply, he.leftInvOn_invFunOn hi]

theorem monomial_jet_rank_of_test (Ω : Set (ℝ × ℝ)) (r m : ℕ)
    (points : Fin r → ℂ × ℂ) (hnz : ∀ l, (points l).1 ≠ 0 ∧ (points l).2 ≠ 0)
    (htest : ∀ (s : Finset (ℤ × ℤ)), s.Nonempty →
      (∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ Ω) →
      ∀ c : ℤ × ℤ → ℂ, (∀ p ∈ s, c p ≠ 0) →
        ∃ l : Fin r, ¬ MixedJetZero (laurentEval s c) (points l).1 (points l).2 m)
    {ι : Type*} (e : ι → ℤ × ℤ) (he : Function.Injective e)
    (hΩ : ∀ i, (((e i).1 : ℝ), ((e i).2 : ℝ)) ∈ Ω) :
    LinearIndependent ℂ (fun i => finiteJetColumn r m points
      (fun u z => u ^ (e i).1 * z ^ (e i).2)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc i hi
  by_contra hci
  let s' := s.filter (fun i => c i ≠ 0)
  have hi' : i ∈ s' := Finset.mem_filter.mpr ⟨hi, hci⟩
  have hs' : s'.Nonempty := ⟨i, hi'⟩
  let : Nonempty ι := ⟨i⟩
  have he' : Set.InjOn e s' := he.injOn
  have hz : finiteJetColumn r m points (indexedLaurent s e c) = 0 := by
    rw [finiteJetColumn_indexedLaurent s e c r m points hnz]
    exact hc
  rw [← indexedLaurent_nonzeroSupport s e c] at hz
  change finiteJetColumn r m points (indexedLaurent s' e c) = 0 at hz
  rw [indexedLaurent_image s' e c he'] at hz
  obtain ⟨l, hl⟩ := htest (s'.image e) (hs'.image e)
    (by intro p hp; obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp; exact hΩ j)
    (c ∘ Function.invFunOn e s') (by
      intro p hp
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
      simpa only [Function.comp_apply, he'.leftInvOn_invFunOn hj] using
        (Finset.mem_filter.mp hj).2)
  exact hl ((finiteJetColumn_eq_zero_iff r m points _).mp hz l)


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_QuadrilateralRows
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology

theorem mem_rowTriangle_of_inequalities (a b c q h : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hh : 0 ≤ h)
    (hl : c * q + a * h ≤ a * c) (hr : -c * q + b * h ≤ b * c) :
    (q, h) ∈ rowTriangle a b c := by
  let D := c * (a + b)
  have hD : 0 < D := mul_pos hc (add_pos ha hb)
  let w : Fin 3 → ℝ := ![(a * c - a * h - c * q) / D,
    (b * c - b * h + c * q) / D, h / c]
  let z : Fin 3 → ℝ × ℝ := ![(-b, 0), (a, 0), (0, c)]
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w i := by
    intro i _
    fin_cases i
    · exact div_nonneg (by linarith) hD.le
    · exact div_nonneg (by linarith) hD.le
    · exact div_nonneg hh hc.le
  have hsum : ∑ i : Fin 3, w i = 1 := by
    simp only [Fin.sum_univ_three]
    dsimp [w, D]
    field_simp
    ring
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 3)), z i ∈ rowTriangle a b c := by
    intro i _
    apply subset_convexHull ℝ _
    fin_cases i <;> simp [z]
  have hm := (convex_convexHull ℝ _).sum_mem hw hsum hz
  have heq : ∑ i : Fin 3, w i • z i = (q, h) := by
    simp only [Fin.sum_univ_three]
    apply Prod.ext <;> dsimp [w, z, D]
    · field_simp
      ring
    · field_simp
      ring
  rwa [heq] at hm

theorem nodeQuadrilateral_constraints (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b ≤ c * (a + b))
    (x y : ℝ) (h : (x, y) ∈ nodeQuadrilateral a b c) :
    0 ≤ x ∧ 0 ≤ y ∧ c * x + (a - c) * y ≤ a * c ∧
      (b - c) * x + c * y ≤ b * c := by
  have hx := planeForm_nonneg_on_hull 1 0 0
    {(0, 0), (a, 0), (c, c), (0, b)} (by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp [planeForm, ha.le, hc.le]) (x, y) h
  have hy := planeForm_nonneg_on_hull 0 1 0
    {(0, 0), (a, 0), (c, c), (0, b)} (by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp [planeForm, hb.le, hc.le]) (x, y) h
  have hl := planeForm_nonneg_on_hull (-c) (c - a) (a * c)
    {(0, 0), (a, 0), (c, c), (0, b)} (by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> dsimp [planeForm] <;> nlinarith [mul_pos ha hc]) (x, y) h
  have hr := planeForm_nonneg_on_hull (c - b) (-c) (b * c)
    {(0, 0), (a, 0), (c, c), (0, b)} (by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> dsimp [planeForm] <;> nlinarith [mul_pos hb hc]) (x, y) h
  dsimp [planeForm] at hx hy hl hr
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem diagonal_compress_mem (a b c x y h : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b ≤ c * (a + b))
    (hxy : (x, y) ∈ nodeQuadrilateral a b c) (hh : 0 ≤ h) (hhx : h ≤ x) (hhy : h ≤ y) :
    (x - y, h) ∈ rowTriangle a b c := by
  obtain ⟨hx, hy, hl, hr⟩ := nodeQuadrilateral_constraints a b c ha hb hc hab x y hxy
  apply mem_rowTriangle_of_inequalities a b c (x - y) h ha hb hc hh
  · by_cases hq : y ≤ x
    · nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hhy)]
    · have hyx : x ≤ y := le_of_not_ge hq
      have hxc : x ≤ c := by
        by_contra hn
        have hx' : c < x := lt_of_not_ge hn
        nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hyx), mul_pos hb (sub_pos.mpr hx')]
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr (hhx.trans hxc)),
        mul_nonneg hc.le (sub_nonneg.mpr hyx)]
  · by_cases hq : x ≤ y
    · nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hhx)]
    · have hyx : y ≤ x := le_of_not_ge hq
      have hyc : y ≤ c := by
        by_contra hn
        have hy' : c < y := lt_of_not_ge hn
        nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hyx), mul_pos ha (sub_pos.mpr hy')]
      nlinarith [mul_nonneg hb.le (sub_nonneg.mpr (hhy.trans hyc)),
        mul_nonneg hc.le (sub_nonneg.mpr hyx)]

theorem diagonalRow_nonempty (s : Finset (ℕ × ℕ)) (q : diagonalRows s) :
    (diagonalRow s q).Nonempty := by
  obtain ⟨p, hp, he⟩ := Finset.mem_image.mp q.property
  exact ⟨p, Finset.mem_filter.mpr ⟨hp, he⟩⟩

theorem rowStart_add_min (p : ℕ × ℕ) :
    rowStart (diagonalIndex p) + min p.1 p.2 = p.2 := by
  simp only [rowStart, diagonalIndex]
  omega

theorem rowEmbedding_second (s : Finset (ℕ × ℕ)) (p : s) :
    rowStart (rowEmbedding s p).1 + ((rowEmbedding s p).2 : ℕ) = p.val.2 :=
  rowStart_add_min p

theorem rowEmbedding_first (s : Finset (ℕ × ℕ)) (p : s) :
    ((rowEmbedding s p).1 : ℤ) +
      ((rowStart (rowEmbedding s p).1 + ((rowEmbedding s p).2 : ℕ) : ℕ) : ℤ) = p.val.1 := by
  rw [rowEmbedding_second]
  change (p.val.1 : ℤ) - p.val.2 + p.val.2 = p.val.1
  omega

theorem rowEmbedding_injective (s : Finset (ℕ × ℕ)) : Function.Injective (rowEmbedding s) := by
  intro p p' h
  have hq := congrArg (fun i : RowIndex (fun q : diagonalRows s => rowHeight s q) => (i.1 : ℤ)) h
  have he := congrArg (fun i : RowIndex (fun q : diagonalRows s => rowHeight s q) =>
    rowStart i.1 + (i.2 : ℕ)) h
  rw [rowEmbedding_second, rowEmbedding_second] at he
  apply Subtype.ext
  apply Prod.ext
  · change (p.val.1 : ℤ) - p.val.2 = (p'.val.1 : ℤ) - p'.val.2 at hq
    omega
  · exact he

theorem rowEnvelope_dominated (s : Finset (ℕ × ℕ))
    (i : RowIndex (fun q : diagonalRows s => rowHeight s q)) :
    ∃ p ∈ s, diagonalIndex p = i.1 ∧ (i.2 : ℕ) ≤ min p.1 p.2 := by
  obtain ⟨p, hp, he⟩ := Finset.exists_mem_eq_sup (diagonalRow s i.1) (diagonalRow_nonempty s i.1)
    (fun p => min p.1 p.2)
  have hle : (i.2 : ℕ) ≤ rowHeight s i.1 := Nat.le_of_lt_succ i.2.isLt
  refine ⟨p, (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2, ?_⟩
  exact he ▸ hle

theorem compressed_row_exponent_injective {Q : Type*} (q : Q → ℤ)
    (hq : Function.Injective q) (n : Q → ℕ) :
    Function.Injective (fun i : RowIndex n => (q i.1, ((i.2 : ℕ) : ℤ))) := by
  intro i j h
  have hq' : i.1 = j.1 := hq (congrArg Prod.fst h)
  obtain ⟨i, a⟩ := i
  obtain ⟨j, b⟩ := j
  dsimp at hq'
  subst j
  have he : ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) := congrArg Prod.snd h
  have hh : a = b := Fin.ext (by exact_mod_cast he)
  subst b
  rfl

theorem rowEnvelope_mem_triangle (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b ≤ c * (a + b))
    (s : Finset (ℕ × ℕ))
    (hs : ∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ nodeQuadrilateral a b c)
    (i : RowIndex (fun q : diagonalRows s => rowHeight s q)) :
    (((i.1 : ℤ) : ℝ), ((i.2 : ℕ) : ℝ)) ∈ rowTriangle a b c := by
  obtain ⟨p, hp, hq, hh⟩ := rowEnvelope_dominated s i
  have hx : ((i.2 : ℕ) : ℝ) ≤ (p.1 : ℝ) := by
    exact_mod_cast hh.trans (min_le_left _ _)
  have hy : ((i.2 : ℕ) : ℝ) ≤ (p.2 : ℝ) := by
    exact_mod_cast hh.trans (min_le_right _ _)
  have he : (((i.1 : ℤ) : ℝ)) = (p.1 : ℝ) - p.2 := by
    rw [← hq]
    simp only [diagonalIndex, Int.cast_sub, Int.cast_natCast]
  rw [he]
  exact diagonal_compress_mem a b c _ _ _ ha hb hc hab (hs p hp) (Nat.cast_nonneg _) hx hy

theorem quadrilateral_jet_rank_of_triangle_test (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b ≤ c * (a + b))
    (r m : ℕ) (points : Fin r → ℂ × ℂ) (hi : Function.Injective points)
    (hnz : ∀ l, (points l).1 ≠ 0 ∧ (points l).2 ≠ 0)
    (htest : ∀ s : Finset (ℤ × ℤ), s.Nonempty →
      (∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ rowTriangle a b c) →
      ∀ d : ℤ × ℤ → ℂ, (∀ p ∈ s, d p ≠ 0) →
        ∃ l : Fin r, ¬ MixedJetZero (laurentEval s d) (points l).1 (points l).2 m)
    (s : Finset (ℕ × ℕ))
    (hs : ∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ nodeQuadrilateral a b c) :
    ∃ p : Fin r → ℂ × ℂ, Function.Injective p ∧
      (∀ i, (p i).1 ≠ 0 ∧ (p i).2 ≠ 0) ∧
      LinearIndependent ℂ (fun e : s => finiteJetColumn r m p
        (fun x z => x ^ e.val.1 * z ^ e.val.2)) := by
  classical
  let q : diagonalRows s → ℤ := Subtype.val
  let n : diagonalRows s → ℕ := fun q => rowHeight s q
  have h₀ : LinearIndependent ℂ (fun i : RowIndex n => finiteJetColumn r m points
      (fun u z => u ^ q i.1 * z ^ (i.2 : ℕ))) := by
    have he := compressed_row_exponent_injective q Subtype.val_injective n
    have hh := monomial_jet_rank_of_test (rowTriangle a b c) r m points hnz htest
      (fun i : RowIndex n => (q i.1, ((i.2 : ℕ) : ℤ))) he
      (by simpa only [Int.cast_natCast] using rowEnvelope_mem_triangle a b c ha hb hc hab s hs)
    simpa only [zpow_natCast] using hh
  obtain ⟨p, hpi, hpn, hp⟩ := diagonal_row_compression q (fun q => rowStart q) n
    r m points hi (fun l => (hnz l).1) h₀
  refine ⟨p, hpi, hpn, ?_⟩
  have hres := hp.comp (rowEmbedding s) (rowEmbedding_injective s)
  convert hres using 1
  all_goals try with_reducible_and_instances rfl
  funext e
  congr 1
  funext x z
  dsimp only [q]
  rw [rowEmbedding_first, rowEmbedding_second, zpow_natCast]

open scoped BigOperators Topology
open Filter Set


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_TorusJets
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise

theorem scaled_compressed_triangle (d H t k : ℝ) :
    k • compressedTriangle d H t =
      convexHull ℝ {(k * (d * H * t / (1 + t)), 0),
        (-(k * (d * H / (1 + t))), 0), (0, k / d)} := by
  rw [compressedTriangle, ← convexHull_smul]
  simp only [Set.smul_set_insert, Set.smul_set_singleton, Prod.smul_mk, smul_eq_mul,
    mul_neg, mul_zero, mul_one_div]
  rw [Set.insert_comm]

open scoped BigOperators ContDiff
open Filter Topology


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_GermInterpolation
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
open scoped BigOperators Topology
open Filter Set

theorem exists_initial_basis (V : Submodule ℂ (Exponent → ℂ))
    [FiniteDimensional ℂ V] (t : ℝ) (ht : 0 < t) :
    (initialExponentSet V t).Finite ∧
      ∃ b : Module.Basis (initialExponentSet V t) ℂ V,
        ∀ e, LexInitial (b e : Exponent → ℂ) t e := by
  classical
  let E := initialExponentSet V t
  have hex (e : E) : ∃ c : V, LexInitial (c : Exponent → ℂ) t e := by
    obtain ⟨c, hc, he⟩ := e.property
    exact ⟨⟨c, hc⟩, he⟩
  choose c hc using hex
  have hli : LinearIndependent ℂ c := by
    apply LinearIndependent.of_comp V.subtype
    exact linearIndependent_of_lexInitial (fun e => (c e : Exponent → ℂ))
      (fun e => e.val) t hc Subtype.val_injective
  have : Finite E := hli.finite
  let := Fintype.ofFinite E
  let ev : V →ₗ[ℂ] (E → ℂ) := LinearMap.pi (fun e => (LinearMap.proj e.val).comp V.subtype)
  have hev : Function.Injective ev := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro f hf
    by_contra hf0
    have hcoeff : (f : Exponent → ℂ) ≠ 0 := by
      intro h
      exact hf0 (Subtype.ext h)
    obtain ⟨e, he⟩ := exists_lexInitial f t ht hcoeff
    let ee : E := ⟨e, ⟨f, f.property, he⟩⟩
    have hh := congrFun (LinearMap.mem_ker.mp hf) ee
    exact he.1 hh
  have hcard : Fintype.card E = Module.finrank ℂ V := by
    apply le_antisymm hli.fintype_card_le_finrank
    simpa only [Module.finrank_pi] using LinearMap.finrank_le_finrank_of_injective hev
  refine ⟨Set.toFinite _, ?_⟩
  refine ⟨Module.Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' hcard).ge, ?_⟩
  intro e
  simpa only [Module.Basis.mk_apply] using hc e

theorem initial_monomial_jet_transfer (V : Submodule ℂ (Exponent → ℂ))
    [FiniteDimensional ℂ V] (hc : ∀ c ∈ V, ConvergentSeries c)
    (t : ℝ) (ht : 0 < t) (r m : ℕ) (p : Fin r → ℂ × ℂ)
    (hp : Function.Injective p)
    (hjet : LinearIndependent ℂ (fun e : initialExponentSet V t =>
      finiteJetColumn r m p (fun x z => x ^ e.val.1 * z ^ e.val.2))) :
    ∃ R : ℝ, 0 < R ∧ (∀ c ∈ V, DerivativeSummable c R) ∧
      ∀ ε : ℝ, 0 < ε → ∃ q : Fin r → ℂ × ℂ, Function.Injective q ∧
        (∀ j, ‖(q j).1‖ < min ε R ∧ ‖(q j).2‖ < min ε R) ∧
        Function.Injective (fun f : V => finiteJetColumn r m q (seriesEval f)) := by
  classical
  obtain ⟨hE, b, hb⟩ := exists_initial_basis V t ht
  have := hE.to_subtype
  have hc' (e : initialExponentSet V t) : ConvergentSeries (b e : Exponent → ℂ) :=
    hc _ (b e).property
  obtain ⟨u, htu, hu⟩ := exists_strictWeight_of_lex
    (fun e => (b e : Exponent → ℂ)) (fun e => e.val) t ht hb
  obtain ⟨R, hR, hDR⟩ := exists_commonDerivativeRadius V hc
  refine ⟨R, hR, hDR, ?_⟩
  intro ε hε
  obtain ⟨q, hqi, hqn, hqj⟩ := initial_monomial_jet_transfer_strict
    (fun e => (b e : Exponent → ℂ)) (fun e => e.val) u (ht.trans htu) hu hc'
    r m p hp hjet (min ε R) (lt_min hε hR)
  have hqR (j) : ‖(q j).1‖ < R ∧ ‖(q j).2‖ < R :=
    ⟨(hqn j).1.trans_le (min_le_right _ _), (hqn j).2.trans_le (min_le_right _ _)⟩
  refine ⟨q, hqi, hqn, ?_⟩
  have hjli : LinearIndependent ℂ (seriesJetMap V R hDR r m q hqR ∘ b) := by
    simpa only [Function.comp_def, seriesJetMap_eq] using hqj
  have hinj := LinearMap.injective_of_linearIndependent b.span_eq hjli
  intro f g hfg
  apply hinj
  simpa only [seriesJetMap_eq] using hfg

theorem rowTriangle_scaled (d H t k : ℝ) :
    rowTriangle (k * (d * H * t / (1 + t))) (k * (d * H / (1 + t))) (k / d) =
      k • compressedTriangle d H t := by
  rw [scaled_compressed_triangle, rowTriangle, Set.insert_comm]

theorem scaled_node_parameters (d H t k : ℝ) (hd : 0 < d) (hH : 0 < H)
    (ht : 0 < t) (hk : 0 < k) (hweight : d ^ 2 * H * t < (1 + t) ^ 2) :
    (k * (d * H * t / (1 + t))) * (k * (d * H / (1 + t))) ≤
      (k / d) * (k * (d * H * t / (1 + t)) + k * (d * H / (1 + t))) := by
  have hden : 0 < 1 + t := by positivity
  have heq : (k / d) * (k * (d * H * t / (1 + t)) + k * (d * H / (1 + t))) =
      k ^ 2 * H := by
    field_simp <;> ring
  rw [heq]
  have hmul : d ^ 2 * H * t * (k ^ 2 * H) ≤ (1 + t) ^ 2 * (k ^ 2 * H) :=
    mul_le_mul_of_nonneg_right hweight.le (by positivity)
  have heq2 : (k * (d * H * t / (1 + t))) * (k * (d * H / (1 + t))) *
      (1 + t) ^ 2 = d ^ 2 * H * t * (k ^ 2 * H) := by
    field_simp
  apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hden)).mp
  rw [heq2, mul_comm (k ^ 2 * H)]
  exact hmul

theorem eventual_germ_jet_test_s01_oai (d H T : ℝ) (hd : 0 < d) (hH : 0 < H) (hT : 1 < T)
    (hweight : ∀ t : ℝ, T < t → d ^ 2 * H * t < (1 + t) ^ 2)
    (V : ℕ → Submodule ℂ (Exponent → ℂ))
    [∀ k, FiniteDimensional ℂ (V k)]
    (hconv : ∀ k c, c ∈ V k → ConvergentSeries c)
    (hbound : ∀ k, 0 < k → ∀ t, T < t → ∀ e ∈ initialExponentSet (V k) t,
      ((e.1 : ℝ), (e.2 : ℝ)) ∈ nodeQuadrilateral
        ((k : ℝ) * (d * H * t / (1 + t)))
        ((k : ℝ) * (d * H / (1 + t))) ((k : ℝ) / d)) :
    ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      ∀ k m : ℕ, 0 < k → 0 < m → (k : ℝ) * Real.sqrt (H / r) < (m : ℝ) →
      ∃ R : ℝ, 0 < R ∧ (∀ c ∈ V k, DerivativeSummable c R) ∧
        ∀ ε : ℝ, 0 < ε → ∃ q : Fin r → ℂ × ℂ, Function.Injective q ∧
          (∀ j, ‖(q j).1‖ < min ε R ∧ ‖(q j).2‖ < min ε R) ∧
          Function.Injective (fun f : V k => finiteJetColumn r m q (seriesEval f)) := by
  classical
  obtain ⟨r₀, hr₀, htorus⟩ := eventual_torus_jet_test_s01 d H T hd hH hT
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr k m hk hm hkm
  obtain ⟨t, ht, p, hpi, hpn, hp⟩ := htorus r hr
  have ht0 : 0 < t := by linarith
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  obtain ⟨hE, _, _⟩ := exists_initial_basis (V k) t ht0
  let s := hE.toFinset
  have hmem (e : Exponent) : e ∈ s ↔ e ∈ initialExponentSet (V k) t := hE.mem_toFinset
  have htest : ∀ s : Finset (ℤ × ℤ), s.Nonempty →
      (∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ rowTriangle
        ((k : ℝ) * (d * H * t / (1 + t)))
        ((k : ℝ) * (d * H / (1 + t))) ((k : ℝ) / d)) →
      ∀ c : ℤ × ℤ → ℂ, (∀ p ∈ s, c p ≠ 0) →
        ∃ l : Fin r, ¬ MixedJetZero (laurentEval s c) (p l).1 (p l).2 m := by
    simpa only [rowTriangle_scaled] using hp k m hk hm hkm
  obtain ⟨q, hqi, _, hq⟩ := quadrilateral_jet_rank_of_triangle_test
    ((k : ℝ) * (d * H * t / (1 + t)))
    ((k : ℝ) * (d * H / (1 + t))) ((k : ℝ) / d)
    (by positivity) (by positivity) (by positivity)
    (scaled_node_parameters d H t k hd hH ht0 hk0 (hweight t ht))
    r m p hpi hpn htest s (fun e he => hbound k hk t ht e ((hmem e).mp he))
  have hq' : LinearIndependent ℂ (fun e : initialExponentSet (V k) t =>
      finiteJetColumn r m q (fun x z => x ^ e.val.1 * z ^ e.val.2)) := by
    let f : initialExponentSet (V k) t → s := fun e => ⟨e.val, (hmem e.val).mpr e.property⟩
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun e : s => e.val) h
    exact hq.comp f hf
  exact initial_monomial_jet_transfer (V k) (hconv k) t ht0 r m q hqi hq'

end MaximalSeshadri.Interpolation

end



end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Interpolation.eventual_germ_jet_test_s01_oai := @OAI.MaximalSeshadri.Interpolation.eventual_germ_jet_test_s01_oai
