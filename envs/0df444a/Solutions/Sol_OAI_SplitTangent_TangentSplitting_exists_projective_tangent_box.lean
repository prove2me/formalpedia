-- Prove2me | solution 1 for OAI.SplitTangent.TangentSplitting.exists_projective_tangent_box
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T19:38:34.178035+00:00
-- url     : https://prove2.me/submissions/f1dc6f71-d55b-48c9-9d5f-ec7db14e3227

import Mathlib
import Definitions.Def_SplitTangentIntegrability
import Definitions.Def_OAIQWST002

section
-- module Solutions.OAIQW_SplitTangent.RationalTrivialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Trivialization. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

universe u

open scoped Topology
open Filter

namespace SplitTangent.TangentSplitting
section
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)


theorem coordinateMatrix_mulVec (x : X.Carrier) (z v : Model X) :
    Matrix.mulVec (fun i j => S.coordinateMatrix x i j z) v = S.coordinateProjector x z v :=
  LinearMap.toMatrix'_mulVec _ _

theorem coordinateMatrix_idempotent (x : X.Carrier) {z : Model X}
    (hz : z ∈ (chartAt (Model X) x).target) (i j : Fin X.dim) :
    ∑ k, S.coordinateMatrix x i k z * S.coordinateMatrix x k j z =
      S.coordinateMatrix x i j z := by
  have hcomp : (S.coordinateProjector x z).toLinearMap.comp
      (S.coordinateProjector x z).toLinearMap = (S.coordinateProjector x z).toLinearMap := by
    apply LinearMap.ext
    intro v
    exact S.coordinateProjector_idempotent x hz v
  have hM := congrArg LinearMap.toMatrix' hcomp
  rw [LinearMap.toMatrix'_comp] at hM
  exact congrFun (congrFun hM i) j



end

end SplitTangent.TangentSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.BoxTransportBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Box Transport Base. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle
universe u

namespace SplitTangent.ReciprocalCharts

lemma torus_open : IsOpen torus :=
  (isOpen_ne_fun continuous_fst continuous_const).inter
    (isOpen_ne_fun continuous_snd continuous_const)
lemma torus_dense : Dense torus := by
  exact (dense_compl_singleton (0 : ℂ)).prod (dense_compl_singleton (0 : ℂ))

lemma coord_ne_zero (b : Bool) {z : ℂ} (hz : z ≠ 0) : coord b z ≠ 0 := by
  cases b <;> simpa [coord] using hz
lemma changeChart_torus (b c : Bool) {w : ℂ × ℂ} (hw : w ∈ torus) :
    changeChart b c w ∈ torus := ⟨coord_ne_zero b hw.1,coord_ne_zero c hw.2⟩
lemma coord_deriv (b : Bool) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (coord b) (scale b z) z := by
  cases b
  · exact hasDerivAt_id z
  · exact hasDerivAt_inv hz
lemma coord_analytic (b : Bool) {z : ℂ} (hz : z ≠ 0) : AnalyticAt ℂ (coord b) z := by
  cases b
  · exact analyticAt_id
  · exact analyticAt_id.inv hz
lemma changeChart_analytic (b c : Bool) {w : ℂ × ℂ} (hw : w ∈ torus) :
    AnalyticAt ℂ (changeChart b c) w :=
  ((coord_analytic b hw.1).comp analyticAt_fst).prod
    ((coord_analytic c hw.2).comp analyticAt_snd)
lemma changeChart_fderiv (b c : Bool) {w : ℂ × ℂ} (hw : w ∈ torus) :
    fderiv ℂ (changeChart b c) w =
      (scale b w.1 • ContinuousLinearMap.fst ℂ ℂ ℂ).prod
        (scale c w.2 • ContinuousLinearMap.snd ℂ ℂ ℂ) := by
  have hf := (coord_deriv b hw.1).comp_hasFDerivAt (𝕜 := ℂ) w hasFDerivAt_fst
  have hg := (coord_deriv c hw.2).comp_hasFDerivAt (𝕜 := ℂ) w hasFDerivAt_snd
  exact (hf.prodMk hg).fderiv
lemma changeChart_fderiv_first (b c : Bool) {w : ℂ × ℂ} (hw : w ∈ torus) :
    fderiv ℂ (changeChart b c) w (1,0) = scale b w.1 • (1,0) := by
  rw [changeChart_fderiv b c hw]
  simp
lemma changeChart_fderiv_second (b c : Bool) {w : ℂ × ℂ} (hw : w ∈ torus) :
    fderiv ℂ (changeChart b c) w (0,1) = scale c w.2 • (0,1) := by
  rw [changeChart_fderiv b c hw]
  simp


lemma changeChart_analytic_on_overlap (a b c d : Bool) {w : ℂ × ℂ}
    (hw : w ∈ overlap a b c d) :
    AnalyticAt ℂ (changeChart (Bool.xor a c) (Bool.xor b d)) w := by
  apply AnalyticAt.prod
  · have hf : AnalyticAt ℂ (coord (Bool.xor a c)) w.1 := by
      by_cases h : a = c
      · subst c; simp only [Bool.xor_self]; exact analyticAt_id
      · exact coord_analytic _ (hw.1 h)
    exact hf.comp analyticAt_fst
  · have hf : AnalyticAt ℂ (coord (Bool.xor b d)) w.2 := by
      by_cases h : b = d
      · subst d; simp only [Bool.xor_self]; exact analyticAt_id
      · exact coord_analytic _ (hw.2 h)
    exact hf.comp analyticAt_snd

lemma changeChart_transition (a b c d : Bool) (w : ℂ × ℂ) :
    changeChart c d (changeChart (Bool.xor a c) (Bool.xor b d) w) = changeChart a b w := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [changeChart,coord]

end SplitTangent.ReciprocalCharts

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.FormalBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Formal Boxes. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle Filter Topology
universe u
namespace SplitTangent

 

namespace FormalCauchy

variable {V : Type*} [AddCommGroup V] [Module ℂ V]


open scoped MvPowerSeries.WithPiTopology

section
variable {R σ τ : Type*} [CommRing R] [Fintype σ]

section Topology
variable [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_formal_pderiv (i : τ) :
    Continuous (MvPowerSeries.pderiv _ i : MvPowerSeries τ R → MvPowerSeries τ R) := by
  apply continuous_pi
  intro d
  change Continuous (fun p : MvPowerSeries τ R =>
    MvPowerSeries.coeff d (MvPowerSeries.pderiv _ i p))
  simp_rw [MvPowerSeries.coeff_pderiv]
  exact (MvPowerSeries.WithPiTopology.continuous_coeff R _).mul continuous_const

end Topology



end

variable {R A σ : Type*} [CommRing R] [CommRing A] [Algebra R A]



theorem deriveCoefficients_add (δ : Derivation R A A) (f g : MvPowerSeries σ A) :
    deriveCoefficients δ (f + g) = deriveCoefficients δ f + deriveCoefficients δ g :=
  (coefficientDerivation δ).map_add f g

theorem deriveCoefficients_mul (δ : Derivation R A A) (f g : MvPowerSeries σ A) :
    deriveCoefficients δ (f * g) =
      f * deriveCoefficients δ g + g * deriveCoefficients δ f :=
  (coefficientDerivation δ).leibniz f g

section Topology
variable [TopologicalSpace A] [IsTopologicalRing A]

omit [IsTopologicalRing A] in
theorem continuous_deriveCoefficients (δ : Derivation R A A) (hδ : Continuous δ) :
    Continuous (deriveCoefficients (σ := σ) δ) := by
  apply continuous_pi
  intro d
  exact hδ.comp (MvPowerSeries.WithPiTopology.continuous_coeff A d)

end Topology
variable {τ : Type*} [Fintype σ]

theorem polynomial_coefficient_chain_rule (δ : Derivation R A A)
    (a : σ → MvPowerSeries τ A) (ha : MvPowerSeries.HasSubst a)
    (p : MvPolynomial σ A) :
    deriveCoefficients δ (MvPowerSeries.subst a (p : MvPowerSeries σ A)) =
      MvPowerSeries.subst a (deriveCoefficients δ (p : MvPowerSeries σ A)) +
        ∑ j : σ, MvPowerSeries.subst a (MvPowerSeries.pderiv _ j (p : MvPowerSeries σ A)) *
          deriveCoefficients δ (a j) := by
  classical
  have hz : MvPowerSeries.subst a (0 : MvPowerSeries σ A) = 0 := by
    simpa using (MvPowerSeries.substAlgHom ha).map_zero
  have h1 : MvPowerSeries.subst a (1 : MvPowerSeries σ A) = 1 := by
    simpa using (MvPowerSeries.substAlgHom ha).map_one
  induction p using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.coe_C, hz]
  | add p q hp hq =>
    simp only [MvPolynomial.coe_add, MvPowerSeries.subst_add ha, deriveCoefficients_add,
      map_add, add_mul, Finset.sum_add_distrib] at *
    rw [hp, hq]
    ring
  | mul_X p x hp =>
    simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, deriveCoefficients_mul, deriveCoefficients_X,
      mul_zero, zero_add, Derivation.leibniz, smul_eq_mul, MvPowerSeries.pderiv_X, MvPowerSeries.subst_add ha, MvPowerSeries.subst_mul ha,
      MvPowerSeries.subst_X ha, hz, h1,
      apply_ite, Pi.single_apply]
    rw [hp]
    simp [mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_comm, mul_left_comm, add_left_comm]

 

theorem formal_coefficient_chain_rule (δ : Derivation R A A)
    (a : σ → MvPowerSeries τ A) (ha : MvPowerSeries.HasSubst a)
    (p : MvPowerSeries σ A) :
    deriveCoefficients δ (MvPowerSeries.subst a p) =
      MvPowerSeries.subst a (deriveCoefficients δ p) +
        ∑ j : σ, MvPowerSeries.subst a (MvPowerSeries.pderiv _ j p) *
          deriveCoefficients δ (a j) := by
  let : UniformSpace A := ⊥
  have hδ : Continuous δ := continuous_of_discreteTopology
  have hleft : Continuous (fun p : MvPowerSeries σ A =>
      deriveCoefficients δ (MvPowerSeries.subst a p)) :=
    (continuous_deriveCoefficients δ hδ).comp (MvPowerSeries.continuous_subst ha)
  have hright : Continuous (fun p : MvPowerSeries σ A =>
      MvPowerSeries.subst a (deriveCoefficients δ p) +
        ∑ j : σ, MvPowerSeries.subst a (MvPowerSeries.pderiv _ j p) *
          deriveCoefficients δ (a j)) := by
    apply Continuous.add
    · exact (MvPowerSeries.continuous_subst ha).comp (continuous_deriveCoefficients δ hδ)
    · apply continuous_finsetSum
      intro j _
      exact ((MvPowerSeries.continuous_subst ha).comp
        (continuous_formal_pderiv j)).mul continuous_const
  have heq := MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries.equalizer hleft hright
    (show _ = _ from funext fun q => polynomial_coefficient_chain_rule δ a ha q)
  exact congrFun heq p



end FormalCauchy
end SplitTangent
section ReconstructionImports

open Set Filter Topology
namespace SplitTangent.DiagonalRationality

 

theorem iteratedDeriv_zero_of_growth {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {n : ℕ} {C : ℝ} (hbound : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ n)
    {k : ℕ} (hk : n < k) : iteratedDeriv k f 0 = 0 := by
  have hb : ∀ R : ℝ, 1 ≤ R →
      ‖iteratedDeriv k f 0‖ ≤ (k.factorial : ℝ) * C / R ^ (k - n) := by
    intro R hR
    have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) k hR0
      hf.diffContOnCl (fun z hz => by
        have hzR : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_zero_right] using hz
        simpa only [hzR] using hbound z (hzR ▸ hR))
    convert h using 1
    rw [pow_sub₀ R hR0.ne' hk.le]
    field_simp
  apply norm_le_zero_iff.mp
  apply ge_of_tendsto (show Tendsto (fun R : ℝ => (k.factorial : ℝ) * C / R ^ (k - n))
      atTop (nhds 0) from tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega)))
  exact (eventually_ge_atTop 1).mono (fun R hR => hb R hR)


theorem eq_taylorPolynomial_of_growth {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {n : ℕ} {C : ℝ} (hbound : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ n)
    (z : ℂ) : f z = (taylorPolynomial f n).eval z := by
  rw [← Complex.taylorSeries_eq_of_entire' 0 z hf]
  rw [tsum_eq_sum (s := Finset.range (n + 1)) (fun k hk => by
    have hnk : n < k := by simpa using hk
    rw [iteratedDeriv_zero_of_growth hf hbound hnk]
    simp)]
  simp [taylorPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]


theorem lineSections_growth {d : ℤ} (s : lineSections d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → ‖s.val.1 z‖ ≤ C * ‖z‖ ^ d := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℂ) 1).image s.property.2.1.continuous).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; norm_num at hz
  rw [s.property.2.2 z hz0, norm_mul, norm_zpow]
  rw [mul_comm (max C 0)]
  apply mul_le_mul_of_nonneg_left _ (zpow_nonneg (norm_nonneg _) _)
  apply (hC _ ?_).trans (le_max_left _ _)
  refine ⟨z⁻¹, ?_, rfl⟩
  simp only [Metric.mem_closedBall, dist_zero_right, norm_inv]
  exact inv_le_one_of_one_le₀ hz

 
theorem lineSections_ext {d : ℤ} {s t : lineSections d}
    (h : s.val.1 = t.val.1) : s = t := by
  apply Subtype.ext
  apply Prod.ext h
  apply Continuous.ext_on (dense_compl_singleton (0 : ℂ))
    s.property.2.1.continuous t.property.2.1.continuous
  intro z hz
  have hz0 : z ≠ 0 := hz
  have hs := s.property.2.2 z⁻¹ (inv_ne_zero hz0)
  have ht := t.property.2.2 z⁻¹ (inv_ne_zero hz0)
  simp only [inv_inv] at hs ht
  have he : (z⁻¹) ^ d * s.val.2 z = (z⁻¹) ^ d * t.val.2 z := by
    rw [← hs, ← ht, h]
  exact mul_left_cancel₀ (zpow_ne_zero _ (inv_ne_zero hz0)) he

 
theorem lineSections_eq_zero_of_neg {d : ℤ} (hd : d < 0) (s : lineSections d) : s = 0 := by
  obtain ⟨C, hC, hb⟩ := lineSections_growth s
  have hb0 : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖s.val.1 z‖ ≤ C * ‖z‖ ^ (0 : ℕ) := by
    intro z hz
    simpa using (hb z hz).trans (mul_le_mul_of_nonneg_left
      (zpow_le_one_of_nonpos₀ hz hd.le) hC)
  have hc : ∀ z : ℂ, s.val.1 z = s.val.1 0 := by
    intro z
    simpa [taylorPolynomial, Polynomial.eval_monomial] using
      eq_taylorPolynomial_of_growth s.property.1 hb0 z
  have hzero : s.val.1 0 = 0 := by
    apply norm_le_zero_iff.mp
    apply ge_of_tendsto (show Tendsto (fun R : ℝ => C * R ^ d) atTop (nhds 0) by
      simpa using (tendsto_zpow_atTop_zero hd).const_mul C)
    apply (eventually_ge_atTop (1 : ℝ)).mono
    intro R hR
    have hnorm : ‖(R : ℂ)‖ = R := by simp [abs_of_nonneg (by linarith : 0 ≤ R)]
    have hh := hb (R : ℂ) (by rw [hnorm]; exact hR)
    simpa only [hnorm, hc] using hh
  apply lineSections_ext
  funext z
  exact (hc z).trans hzero


theorem sectionJet_injective (n : ℕ) : Function.Injective (sectionJet (n : ℤ) n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro s hs
  obtain ⟨C, hC, hb⟩ := lineSections_growth s
  have hb' : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖s.val.1 z‖ ≤ C * ‖z‖ ^ n := by
    simpa only [zpow_natCast] using hb
  apply lineSections_ext
  funext z
  rw [eq_taylorPolynomial_of_growth s.property.1 hb' z]
  simp only [taylorPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  apply Finset.sum_eq_zero
  intro k hk
  have hc : iteratedDeriv k s.val.1 0 = 0 := congrFun hs ⟨k, Finset.mem_range.mp hk⟩
  simp [hc]

instance lineSections_finite (d : ℤ) : Module.Finite ℂ (lineSections d) := by
  by_cases hd : 0 ≤ d
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hd
    exact Module.Finite.of_injective (sectionJet (n : ℤ) n) (sectionJet_injective n)
  · have : Subsingleton (lineSections d) := ⟨fun s t =>
      (lineSections_eq_zero_of_neg (lt_of_not_ge hd) s).trans
        (lineSections_eq_zero_of_neg (lt_of_not_ge hd) t).symm⟩
    infer_instance

theorem finrank_lineSections_le (d : ℤ) :
    Module.finrank ℂ (lineSections d) ≤ (d + 1).toNat := by
  by_cases hd : 0 ≤ d
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hd
    simpa using LinearMap.finrank_le_finrank_of_injective (sectionJet_injective n)
  · have : Subsingleton (lineSections d) := ⟨fun s t =>
      (lineSections_eq_zero_of_neg (lt_of_not_ge hd) s).trans
        (lineSections_eq_zero_of_neg (lt_of_not_ge hd) t).symm⟩
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _

open PowerSeries



theorem orderFiltration_eq_zero {T : ℂ → PowerSeries ℂ} {d : ℤ}
    (hT : ∀ z : ℂ, z ≠ 0 → constantCoeff (T z) = z ^ d) {k : ℕ}
    (hk : d - 2 * (k : ℤ) < 0) (s : orderFiltration T k) : s = 0 := by
  have hcoeff : ∀ n, coeff n s.val.val.1 = 0 ∧ coeff n s.val.val.2 = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hnk : n < k
      · exact s.property n hnk
      · let t : orderFiltration T n := ⟨s.val, fun j hj => ih j hj⟩
        have ht := lineSections_eq_zero_of_neg (d := d - 2 * (n : ℤ)) (by omega)
          (leadingSection hT n t)
        exact (leadingSection_eq_zero_iff hT n t).mp ht
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact PowerSeries.ext (fun n => (hcoeff n).1)
  · exact PowerSeries.ext (fun n => (hcoeff n).2)

theorem finite_of_kernel {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    (f : V →ₗ[ℂ] W) [Module.Finite ℂ (LinearMap.ker f)] : Module.Finite ℂ V := by
  have : Module.Finite ℂ (V ⧸ LinearMap.ker f) :=
    Module.Finite.of_injective f.quotKerEquivRange.toLinearMap f.quotKerEquivRange.injective
  exact Module.Finite.of_submodule_quotient (LinearMap.ker f)

 

theorem filtration_dimension_bound {T : ℂ → PowerSeries ℂ} {d : ℤ}
    (hT : ∀ z : ℂ, z ≠ 0 → constantCoeff (T z) = z ^ d) (N k : ℕ)
    (hN : d - 2 * ((k+N : ℕ) : ℤ) < 0) :
    Module.Finite ℂ (orderFiltration T k) ∧
      Module.finrank ℂ (orderFiltration T k) ≤
        ∑ j ∈ Finset.range N, (d - 2 * ((k+j : ℕ) : ℤ) + 1).toNat := by
  induction N generalizing k with
  | zero =>
    have : Subsingleton (orderFiltration T k) := ⟨fun s t =>
      (orderFiltration_eq_zero hT (by simpa using hN) s).trans
        (orderFiltration_eq_zero hT (by simpa using hN) t).symm⟩
    exact ⟨inferInstance, by simp [Module.finrank_zero_of_subsingleton]⟩
  | succ N ih =>
    have hn : d - 2 * ((k+1+N : ℕ) : ℤ) < 0 := by convert hN using 1; omega
    obtain ⟨hfinite, hbound⟩ := ih (k+1) hn
    have : Module.Finite ℂ (orderFiltration T (k+1)) := hfinite
    have : Module.Finite ℂ (LinearMap.ker (leadingSection hT k)) :=
      Module.Finite.equiv (leadingKernelEquiv hT k).symm
    have : Module.Finite ℂ (orderFiltration T k) := finite_of_kernel (V := orderFiltration T k) (W := lineSections (d - 2 * (k : ℤ))) (leadingSection hT k)
    refine ⟨inferInstance, ?_⟩
    have hrank := LinearMap.finrank_range_add_finrank_ker (K := ℂ)
      (V := orderFiltration T k) (V₂ := lineSections (d - 2 * (k : ℤ))) (leadingSection hT k)
    have hrange := (LinearMap.range (leadingSection hT k)).finrank_le
    have hline := finrank_lineSections_le (d - 2 * (k : ℤ))
    have hker := (leadingKernelEquiv hT k).finrank_eq
    rw [Finset.sum_range_succ']
    have hshift : (∑ j ∈ Finset.range N, (d - 2 * ((k+(j+1) : ℕ) : ℤ) + 1).toNat) =
        ∑ j ∈ Finset.range N, (d - 2 * ((k+1+j : ℕ) : ℤ) + 1).toNat := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 2
      omega
    rw [hshift]
    simp only [Nat.add_zero]
    omega

theorem sum_descending_odds (N : ℕ) :
    ∑ j ∈ Finset.range N, (2 * (N-j) - 1) = N ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero]
    rw [ih]
    have h : 2 * (N+1) - 1 = 2*N+1 := by omega
    rw [h]
    ring

 

theorem formalSections_dimension_bound {T : ℂ → PowerSeries ℂ} (d m : ℕ)
    (hT : ∀ z : ℂ, z ≠ 0 → constantCoeff (T z) = z ^ ((d : ℤ) + 2 * (m : ℤ))) :
    Module.Finite ℂ (formalSections T) ∧
      Module.finrank ℂ (formalSections T) ≤ (m+d+1)^2 := by
  obtain ⟨hf,hb⟩ := filtration_dimension_bound hT (m+d+1) 0 (by push_cast; omega)
  have : Module.Finite ℂ (orderFiltration T 0) := hf
  refine ⟨Module.Finite.equiv (zeroFiltrationEquiv T), ?_⟩
  rw [← (zeroFiltrationEquiv T).finrank_eq]
  apply hb.trans
  rw [← sum_descending_odds (m+d+1)]
  apply Finset.sum_le_sum
  intro j hj
  have hj' := Finset.mem_range.mp hj
  simp only [Nat.zero_add]
  omega

 

theorem twice_polynomial_dimension_gt (d : ℕ) :
    (4*(d+1)+d+1)^2 < 2*(4*(d+1)+1)^2 := by ring_nf; omega


theorem polynomialFunction_injective : Function.Injective polynomialFunction := by
  intro p q h
  exact Polynomial.funext (fun z => by simpa using congrFun h z)

theorem biPolynomial_injective (m : ℕ) : Function.Injective (biPolynomial m) := by
  intro a b h
  funext i j
  simpa using congrArg (fun p : Polynomial (Polynomial ℂ) => (p.coeff j.val).coeff i.val) h

theorem expandPolynomial_injective : Function.Injective expandPolynomial := by
  intro p q h
  have he := Polynomial.coe_injective (ℂ → ℂ) h
  have he' := congrArg (fun f : Polynomial (ℂ → ℂ) => f.comp (Polynomial.X - Polynomial.C id)) he
  have hc : (Polynomial.X + Polynomial.C id : Polynomial (ℂ → ℂ)).comp
      (Polynomial.X - Polynomial.C id) = Polynomial.X := by simp
  simp only [Polynomial.comp_assoc, hc, Polynomial.comp_X] at he'
  exact Polynomial.map_injective polynomialFunction.toRingHom polynomialFunction_injective he'

theorem polynomial_coe_sum {ι R : Type*} [Semiring R] (s : Finset ι)
    (f : ι → Polynomial R) :
    ((∑ i ∈ s, f i : Polynomial R) : PowerSeries R) = ∑ i ∈ s, (f i : PowerSeries R) :=
  map_sum Polynomial.coeToPowerSeries.ringHom f s

theorem normalPolynomialSection_eq_expand (m : ℕ) (a : BiCoefficients m) :
    normalPolynomialSection m a = expandPolynomial (biPolynomial m a) := by
  simp only [normalPolynomialSection, expandPolynomial, biPolynomial,
    Polynomial.map_sum, Polynomial.map_monomial, Polynomial.sum_comp,
    Polynomial.monomial_comp, polynomial_coe_sum, Polynomial.coe_mul,
    Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_C, Polynomial.coe_X]
  apply Finset.sum_congr rfl
  intro j hj
  have he : polynomialFunction (∑ i, Polynomial.monomial i.val (a i j)) =
      fun z => ∑ i, a i j * z ^ i.val := by
    ext z
    simp [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  change C (fun z => ∑ i, a i j * z ^ i.val) * (C id + X) ^ j.val =
    C (polynomialFunction (∑ i, Polynomial.monomial i.val (a i j))) * (X + C id) ^ j.val
  rw [he, add_comm (C id) X]

theorem normalPolynomialSection_injective (m : ℕ) :
    Function.Injective (normalPolynomialSection m) := by
  intro a b h
  rw [normalPolynomialSection_eq_expand, normalPolynomialSection_eq_expand] at h
  exact biPolynomial_injective m (expandPolynomial_injective h)

theorem finrank_biCoefficients (m : ℕ) : Module.finrank ℂ (BiCoefficients m) = (m+1)^2 := by
  simp [BiCoefficients, Module.finrank_pi_fintype, pow_two]

theorem exists_polynomial_relation {T : ℂ → PowerSeries ℂ} (d : ℕ)
    (hT : ∀ z : ℂ, z ≠ 0 → constantCoeff (T z) = z ^ (d : ℤ))
    (s t : formalSections T) :
    ∃ ab : BiCoefficients (4*(d+1)) × BiCoefficients (4*(d+1)),
      ab ≠ 0 ∧ relationMap s t (4*(d+1)) ab = 0 := by
  let m := 4*(d+1)
  have hTw : ∀ z : ℂ, z ≠ 0 →
      constantCoeff (twistTransition m z * T z) = z ^ ((d : ℤ) + 2*(m : ℤ)) := by
    intro z hz
    simp only [map_mul, twistTransition, map_pow, constantCoeff_C, map_add,
      constantCoeff_X, add_zero]
    rw [hT z hz, mul_pow]
    rw [zpow_add₀ hz]
    rw [show (2 : ℤ) * (m : ℤ) = ((2*m : ℕ) : ℤ) by omega]
    simp only [zpow_natCast, pow_mul, pow_two]
    ring
  obtain ⟨hf, hb⟩ := formalSections_dimension_bound d m hTw
  let : Module.Finite ℂ (formalSections (fun z => twistTransition m z * T z)) := hf
  have hdim : Module.finrank ℂ (formalSections (fun z => twistTransition m z * T z)) <
      Module.finrank ℂ (BiCoefficients m × BiCoefficients m) := by
    rw [Module.finrank_prod, finrank_biCoefficients]
    have h := twice_polynomial_dimension_gt d
    dsimp [m] at hb ⊢
    omega
  obtain ⟨ab, hab, hne⟩ := (Submodule.ne_bot_iff _).mp
    (LinearMap.ker_ne_bot_of_finrank_lt (f := relationMap s t m) hdim)
  exact ⟨ab, hne, hab⟩

 

theorem entireSeries_cancel {f g : PowerSeries (ℂ → ℂ)}
    (hf : ∀ k, Differentiable ℂ (coeff k f))
    (hg : Differentiable ℂ (constantCoeff g))
    (hg0 : ∃ z : ℂ, constantCoeff g z ≠ 0) (hfg : f*g = 0) : f = 0 := by
  obtain ⟨z₀,hz₀⟩ := hg0
  have he : ∀ᶠ z in nhds z₀, constantCoeff g z ≠ 0 :=
    hg.continuous.continuousAt.eventually_ne hz₀
  apply PowerSeries.ext
  intro k
  change coeff k f = fun _ => 0
  apply AnalyticOnNhd.eq_of_eventuallyEq
    (fun z _ => (hf k).analyticAt z) analyticOnNhd_const
  filter_upwards [he] with z hz
  have hg' : evaluateCoefficients z g ≠ 0 := by
    intro h
    have hc := congrArg (coeff 0) h
    apply hz
    simpa only [coeff_evaluateCoefficients, coeff_zero_eq_constantCoeff, map_zero] using hc
  have h := congrArg (evaluateCoefficients z) hfg
  simp only [map_mul, map_zero] at h
  have hf' := (mul_eq_zero.mp h).resolve_right hg'
  simpa using congrArg (coeff k) hf'

 

theorem exists_rational_relation {T : ℂ → PowerSeries ℂ} (d : ℕ)
    (hT : ∀ z : ℂ, z ≠ 0 → constantCoeff (T z) = z ^ (d : ℤ))
    (s t : formalSections T) (hs : ∃ z : ℂ, constantCoeff s.val.1 z ≠ 0) :
    ∃ a b : BiCoefficients (4*(d+1)), b ≠ 0 ∧
      normalPolynomialSection (4*(d+1)) a * s.val.1 +
      normalPolynomialSection (4*(d+1)) b * t.val.1 = 0 := by
  obtain ⟨⟨a,b⟩,hne,hrel⟩ := exists_polynomial_relation d hT s t
  have hfirst : normalPolynomialSection (4*(d+1)) a * s.val.1 +
      normalPolynomialSection (4*(d+1)) b * t.val.1 = 0 :=
    congrArg (fun w => w.val.1) hrel
  refine ⟨a,b,?_,hfirst⟩
  intro hb
  subst b
  have hzero : normalPolynomialSection (4*(d+1)) 0 = 0 := by
    rw [normalPolynomialSection_eq_linear, map_zero]
  rw [hzero, zero_mul, add_zero] at hfirst
  have ha := entireSeries_cancel (normalPolynomialSection_entire _ a)
    (by simpa only [coeff_zero_eq_constantCoeff] using s.property.1 0) hs hfirst
  have ha' : a = 0 := normalPolynomialSection_injective _ (ha.trans hzero.symm)
  exact hne (by simp [ha'])

 

theorem entireSeries_vanishing_of_mul {f g : PowerSeries (ℂ → ℂ)}
    (hf : ∀ k, Differentiable ℂ (coeff k f))
    (hg : Differentiable ℂ (constantCoeff g))
    (hg0 : ∃ z : ℂ, constantCoeff g z ≠ 0) {r : ℕ}
    (hmul : ∀ k < r, coeff k (f*g) = 0) : ∀ k < r, coeff k f = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hkr
    obtain ⟨q,hq⟩ := X_pow_dvd_iff.mpr (fun j hj => ih j hj (hj.trans hkr))
    have hc : coeff k (f*g) = coeff k f * constantCoeff g := by
      rw [hq, mul_assoc]
      rw [coeff_X_pow_mul', coeff_X_pow_mul']
      simp [coeff_zero_eq_constantCoeff]
    have hzero : coeff k f * constantCoeff g = 0 := hc.symm.trans (hmul k hkr)
    obtain ⟨z₀,hz₀⟩ := hg0
    apply AnalyticOnNhd.eq_of_eventuallyEq
      (fun z _ => (hf k).analyticAt z) analyticOnNhd_const
    filter_upwards [hg.continuous.continuousAt.eventually_ne hz₀] with z hz
    exact (mul_eq_zero.mp (congrFun hzero z)).resolve_right hz



@[simp] theorem normalPolynomial_coe (m : ℕ) (a : BiCoefficients m) :
    (normalPolynomial m a : PowerSeries (ℂ → ℂ)) = normalPolynomialSection m a := by
  simp [normalPolynomial, normalPolynomialSection, polynomial_coe_sum]

 
theorem cancel_normal_order {A B : Polynomial (ℂ → ℂ)}
    {s t : PowerSeries (ℂ → ℂ)}
    (hA : ∀ k, Differentiable ℂ (A.coeff k))
    (hs : Differentiable ℂ (constantCoeff s))
    (hs0 : ∃ z : ℂ, constantCoeff s z ≠ 0)
    (hrel : (A : PowerSeries (ℂ → ℂ))*s + (B : PowerSeries (ℂ → ℂ))*t = 0) :
    Polynomial.X ^ B.natTrailingDegree ∣ A := by
  have hB : X ^ B.natTrailingDegree ∣ (B : PowerSeries (ℂ → ℂ)) :=
    X_pow_dvd_iff.mpr (by
      intro k hk
      simpa only [Polynomial.coeff_coe] using
        (Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hk))
  have hAs : X ^ B.natTrailingDegree ∣ (A : PowerSeries (ℂ → ℂ))*s := by
    have h := dvd_mul_of_dvd_left hB t
    have he : (A : PowerSeries (ℂ → ℂ))*s = -((B : PowerSeries (ℂ → ℂ))*t) :=
      eq_neg_of_add_eq_zero_left hrel
    rw [he]
    exact dvd_neg.mpr h
  apply Polynomial.X_pow_dvd_iff.mpr
  simpa only [Polynomial.coeff_coe] using
    (entireSeries_vanishing_of_mul
      (by simpa only [Polynomial.coeff_coe] using hA) hs hs0 (X_pow_dvd_iff.mp hAs))

 

theorem exists_reduced_polynomial_relation {A B : Polynomial (ℂ → ℂ)}
    {s t : PowerSeries (ℂ → ℂ)}
    (hA : ∀ k, Differentiable ℂ (A.coeff k))
    (hB : ∀ k, Differentiable ℂ (B.coeff k)) (hB0 : B ≠ 0)
    (hs : Differentiable ℂ (constantCoeff s))
    (hs0 : ∃ z : ℂ, constantCoeff s z ≠ 0)
    (hrel : (A : PowerSeries (ℂ → ℂ))*s + (B : PowerSeries (ℂ → ℂ))*t = 0) :
    ∃ (r : ℕ) (A' B' : Polynomial (ℂ → ℂ)),
      A = Polynomial.X ^ r * A' ∧ B = Polynomial.X ^ r * B' ∧
      B'.coeff 0 ≠ 0 ∧ (∀ k, Differentiable ℂ (A'.coeff k)) ∧
      (∀ k, Differentiable ℂ (B'.coeff k)) ∧
      (A' : PowerSeries (ℂ → ℂ))*s + (B' : PowerSeries (ℂ → ℂ))*t = 0 := by
  let r := B.natTrailingDegree
  obtain ⟨A',hA'⟩ := cancel_normal_order hA hs hs0 hrel
  change A = Polynomial.X ^ r * A' at hA'
  obtain ⟨B',hB'⟩ := Polynomial.X_pow_dvd_iff.mpr
    (fun k hk => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hk :
      ∀ k < r, B.coeff k = 0)
  have hca (k : ℕ) : A'.coeff k = A.coeff (k+r) := by
    rw [hA', Polynomial.coeff_X_pow_mul]
  have hcb (k : ℕ) : B'.coeff k = B.coeff (k+r) := by
    rw [hB', Polynomial.coeff_X_pow_mul]
  refine ⟨r,A',B',hA',hB',?_,fun k => ?_,fun k => ?_,?_⟩
  · rw [hcb 0, Nat.zero_add]
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hB0
  · rw [hca k]
    exact hA (k+r)
  · rw [hcb k]
    exact hB (k+r)
  · apply X_pow_mul_cancel (k := r)
    rw [mul_zero]
    rw [hA',hB'] at hrel
    simpa only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, mul_add,
      mul_assoc] using hrel

 

theorem exists_common_nonzero {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf0 : f ≠ 0) (hg0 : ∃ z : ℂ, g z ≠ 0) :
    ∃ z : ℂ, f z ≠ 0 ∧ g z ≠ 0 := by
  obtain ⟨z₀,hz₀⟩ := hg0
  by_contra h
  have he : f =ᶠ[nhds z₀] (fun _ => 0) := by
    filter_upwards [hg.continuous.continuousAt.eventually_ne hz₀] with z hz
    by_contra hfz
    exact h ⟨z,hfz,hz⟩
  apply hf0
  exact AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hf.analyticAt z) analyticOnNhd_const he



theorem polynomialEvaluation_analytic (p : Polynomial (ℂ → ℂ))
    (hp : ∀ k, Differentiable ℂ (p.coeff k)) (w : ℂ × ℂ) :
    AnalyticAt ℂ (polynomialEvaluation p) w := by
  have ht (k : ℕ) : AnalyticAt ℂ (fun u : ℂ × ℂ => p.coeff k u.1 * u.2 ^ k) w :=
    (((hp k).analyticAt w.1).comp
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt w)).mul
        (((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt w).pow k)
  have he : polynomialEvaluation p =
      ∑ k ∈ p.support, (fun u : ℂ × ℂ => p.coeff k u.1 * u.2 ^ k) := by
    funext u
    simp [polynomialEvaluation, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  rw [he]
  exact Finset.analyticAt_sum p.support (fun k _ => ht k)

 

theorem polynomial_quotient_analytic {A B : Polynomial (ℂ → ℂ)}
    (hA : ∀ k, Differentiable ℂ (A.coeff k))
    (hB : ∀ k, Differentiable ℂ (B.coeff k)) {z : ℂ} (hz : B.coeff 0 z ≠ 0) :
    AnalyticAt ℂ (fun w => -polynomialEvaluation A w / polynomialEvaluation B w) (z,0) := by
  exact (polynomialEvaluation_analytic A hA (z,0)).neg.div
    (polynomialEvaluation_analytic B hB (z,0)) (by simpa using hz)


theorem taylorSeries_quotient_relation (A B : Polynomial ℂ) (hB : B.coeff 0 ≠ 0) :
    taylorSeries (fun z => -A.eval z / B.eval z) * (B : PowerSeries ℂ) + A = 0 := by
  have ha := polynomial_analyticAt A 0
  have hb := polynomial_analyticAt B 0
  have hb0 : B.eval 0 ≠ 0 := by simpa only [← Polynomial.coeff_zero_eq_eval_zero] using hB
  have hq : AnalyticAt ℂ (fun z => -A.eval z / B.eval z) 0 := ha.neg.div hb hb0
  have he : (fun z => (-A.eval z / B.eval z) * B.eval z + A.eval z) =ᶠ[nhds 0]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [hb.continuousAt.eventually_ne hb0] with z hz
    field_simp
    ring
  have ht := taylorSeries_congr he
  rw [taylorSeries_zero] at ht
  change taylorSeries ((fun z => -A.eval z / B.eval z) * (fun z => B.eval z) +
    (fun z => A.eval z)) = 0 at ht
  rw [taylorSeries_add (hq.mul hb) ha, taylorSeries_mul hq hb,
    taylorSeries_polynomial, taylorSeries_polynomial] at ht
  exact ht

 

theorem taylorSeries_quotient_eq (A B : Polynomial ℂ) (hB : B.coeff 0 ≠ 0)
    (s t : PowerSeries ℂ) (hs : constantCoeff s ≠ 0)
    (hrel : (A : PowerSeries ℂ)*s + (B : PowerSeries ℂ)*t = 0) :
    taylorSeries (fun z => -A.eval z / B.eval z) = t * s⁻¹ := by
  have hq := taylorSeries_quotient_relation A B hB
  have hBn : (B : PowerSeries ℂ) ≠ 0 := by
    intro h
    apply hB
    simpa only [Polynomial.coeff_coe, map_zero] using congrArg (coeff 0) h
  have he : taylorSeries (fun z => -A.eval z / B.eval z) * s = t := by
    apply mul_left_cancel₀ hBn
    calc
      (B : PowerSeries ℂ) * (taylorSeries (fun z => -A.eval z / B.eval z) * s) =
          (taylorSeries (fun z => -A.eval z / B.eval z) * B) * s := by ring
      _ = (-A) * s := by rw [eq_neg_of_add_eq_zero_left hq]
      _ = B * t := by linear_combination -hrel
  calc
    taylorSeries (fun z => -A.eval z / B.eval z) =
        (taylorSeries (fun z => -A.eval z / B.eval z) * s) * s⁻¹ := by
          rw [mul_assoc, PowerSeries.mul_inv_cancel s hs, mul_one]
    _ = t * s⁻¹ := by rw [he]

 
theorem hasFPowerSeries_formal_quotient (A B : Polynomial ℂ) (hB : B.coeff 0 ≠ 0)
    (s t : PowerSeries ℂ) (hs : constantCoeff s ≠ 0)
    (hrel : (A : PowerSeries ℂ)*s + (B : PowerSeries ℂ)*t = 0) :
    HasFPowerSeriesAt (fun z => -A.eval z / B.eval z)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => coeff n (t*s⁻¹))) 0 := by
  have hq : AnalyticAt ℂ (fun z => -A.eval z / B.eval z) 0 :=
    (polynomial_analyticAt A 0).neg.div (polynomial_analyticAt B 0)
      (by simpa only [← Polynomial.coeff_zero_eq_eval_zero] using hB)
  convert hasFPowerSeries_taylorSeries hq using 1
  rw [taylorSeries_quotient_eq A B hB s t hs hrel]



theorem reduced_relation_converges {A B : Polynomial (ℂ → ℂ)}
    {s t : PowerSeries (ℂ → ℂ)} {z : ℂ}
    (hB : B.coeff 0 z ≠ 0) (hs : constantCoeff s z ≠ 0)
    (hrel : (A : PowerSeries (ℂ → ℂ))*s + (B : PowerSeries (ℂ → ℂ))*t = 0) :
    HasFPowerSeriesAt
      (fun v => -polynomialEvaluation A (z,v) / polynomialEvaluation B (z,v))
      (FormalMultilinearSeries.ofScalars ℂ (fun n =>
        coeff n (evaluateCoefficients z t * (evaluateCoefficients z s)⁻¹))) 0 := by
  have he := congrArg (evaluateCoefficients z) hrel
  simp only [map_add, map_mul, map_zero, evaluateCoefficients_polynomial] at he
  have hs' : constantCoeff (evaluateCoefficients z s) ≠ 0 := by
    simpa only [← coeff_zero_eq_constantCoeff, coeff_evaluateCoefficients] using hs
  simpa only [polynomialFiber_eval] using
    hasFPowerSeries_formal_quotient (polynomialFiber A z) (polynomialFiber B z)
      (by simpa using hB) (evaluateCoefficients z s) (evaluateCoefficients z t) hs' he

 

theorem exists_convergent_rational_quotient {T : ℂ → PowerSeries ℂ} (d : ℕ)
    (hT : ∀ z : ℂ, z ≠ 0 → constantCoeff (T z) = z ^ (d : ℤ))
    (s t : formalSections T) (hs : ∃ z : ℂ, constantCoeff s.val.1 z ≠ 0) :
    ∃ (a b : BiCoefficients (4*(d+1))) (r : ℕ)
      (A B : Polynomial (ℂ → ℂ)) (z : ℂ),
      b ≠ 0 ∧ normalPolynomial (4*(d+1)) a = Polynomial.X ^ r * A ∧
      normalPolynomial (4*(d+1)) b = Polynomial.X ^ r * B ∧
      (∀ k, Differentiable ℂ (A.coeff k)) ∧
      (∀ k, Differentiable ℂ (B.coeff k)) ∧
      B.coeff 0 z ≠ 0 ∧ constantCoeff s.val.1 z ≠ 0 ∧
      AnalyticAt ℂ (fun w => -polynomialEvaluation A w / polynomialEvaluation B w) (z,0) ∧
      (∀ w : ℂ, B.coeff 0 w ≠ 0 → constantCoeff s.val.1 w ≠ 0 →
        HasFPowerSeriesAt
          (fun v => -polynomialEvaluation A (w,v) / polynomialEvaluation B (w,v))
          (FormalMultilinearSeries.ofScalars ℂ (fun n => coeff n
            (evaluateCoefficients w t.val.1 * (evaluateCoefficients w s.val.1)⁻¹))) 0) := by
  obtain ⟨a,b,hb,hrel⟩ := exists_rational_relation d hT s t hs
  have hal (k : ℕ) : Differentiable ℂ ((normalPolynomial (4*(d+1)) a).coeff k) := by
    simpa only [← Polynomial.coeff_coe, normalPolynomial_coe] using
      normalPolynomialSection_entire (4*(d+1)) a k
  have hbl (k : ℕ) : Differentiable ℂ ((normalPolynomial (4*(d+1)) b).coeff k) := by
    simpa only [← Polynomial.coeff_coe, normalPolynomial_coe] using
      normalPolynomialSection_entire (4*(d+1)) b k
  have hbn : normalPolynomial (4*(d+1)) b ≠ 0 := by
    intro h
    apply hb
    apply normalPolynomialSection_injective (4*(d+1))
    rw [← normalPolynomial_coe, h, Polynomial.coe_zero]
    simp [normalPolynomialSection_eq_linear]
  have hsD : Differentiable ℂ (constantCoeff s.val.1) := by
    simpa only [coeff_zero_eq_constantCoeff] using s.property.1 0
  obtain ⟨r,A,B,hA,hB,hB0,hAD,hBD,hrel'⟩ :=
    exists_reduced_polynomial_relation hal hbl hbn hsD hs
      (by simpa only [normalPolynomial_coe] using hrel)
  obtain ⟨z,hBz,hsz⟩ := exists_common_nonzero (hBD 0) hsD hB0 hs
  exact ⟨a,b,r,A,B,z,hb,hA,hB,hAD,hBD,hBz,hsz,
    polynomial_quotient_analytic hAD hBD hBz,
    fun w hwB hws => reduced_relation_converges hwB hws hrel'⟩

 

theorem exists_common_nonzero_finset {ι : Type*} (q : Finset ι)
    (f : ι → ℂ → ℂ) (g : ℂ → ℂ)
    (hf : ∀ i ∈ q, Differentiable ℂ (f i)) (hg : Differentiable ℂ g)
    (hf0 : ∀ i ∈ q, f i ≠ 0) (hg0 : ∃ z, g z ≠ 0) :
    ∃ z, g z ≠ 0 ∧ ∀ i ∈ q, f i z ≠ 0 := by
  classical
  induction q using Finset.induction_on with
  | empty =>
    obtain ⟨z,hz⟩ := hg0
    exact ⟨z,hz,by simp⟩
  | @insert i q hi ih =>
    obtain ⟨z₀,hg₀,hf₀⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hf0 j (Finset.mem_insert_of_mem hj))
    let h : ℂ → ℂ := fun z => g z * ∏ j ∈ q, f j z
    have hD : Differentiable ℂ h := hg.mul
      (Differentiable.fun_finsetProd (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    have hh0 : ∃ z, h z ≠ 0 := ⟨z₀, mul_ne_zero hg₀ (Finset.prod_ne_zero_iff.mpr hf₀)⟩
    obtain ⟨z,hiz,hz⟩ := exists_common_nonzero (hf i (Finset.mem_insert_self i q))
      hD (hf0 i (Finset.mem_insert_self i q)) hh0
    have hz' : g z ≠ 0 ∧ ∀ j ∈ q, f j z ≠ 0 := by
      simpa only [h, mul_ne_zero_iff, Finset.prod_ne_zero_iff] using hz
    exact ⟨z,hz'.1,fun j hj => by
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hiz
      · exact hz'.2 j hj⟩



end SplitTangent.DiagonalRationality

open Set Filter Topology Polynomial PowerSeries
namespace SplitTangent.FormalProjective
section


namespace ChartData
variable {ι : Type*} [Fintype ι] {p : ι → ℂ[X]} (F : ChartData p)
  (a : ι → ℂ[X]) (ha : ∑ i, a i * p i = 1)



include ha in
theorem localSection_constant (k j : ι) (z : ℂ) (hk : (p k).eval z ≠ 0) :
    PowerSeries.constantCoeff (F.localSection a k j z) = (p j).eval z := by
  simp only [localSection,map_mul,PowerSeries.constantCoeff_inv,
    F.frame_constant a ha k z hk,inv_inv,F.diagonal k j z hk]
  field_simp

include ha in
theorem sectionValue_constant (j : ι) (z : ℂ) :
    PowerSeries.constantCoeff (F.sectionValue a j z) = (p j).eval z :=
  F.localSection_constant a ha (F.active z) j z (F.active_nonzero z)



end ChartData

open SplitTangent.DiagonalRationality



namespace TwoChartData
variable {ι : Type*} [Fintype ι] {d : ℕ} {p q : ι → ℂ[X]} (F : TwoChartData d p q)
  (a b : ι → ℂ[X]) (ha : ∑ i, a i * p i = 1) (hb : ∑ i, b i * q i = 1)

include ha hb in
theorem normalizedTransition_constant (z : ℂ) (hz : z ≠ 0) :
    PowerSeries.constantCoeff (F.normalizedTransition a b z) = z ^ (d : ℤ) := by
  let k := F.finite.active z
  have hk : (p k).eval z ≠ 0 := F.finite.active_nonzero z
  have hq := F.infinity_nonzero z hz k hk
  change PowerSeries.constantCoeff ((F.finite.frame a k z)⁻¹ *
    PowerSeries.subst (reciprocalNormal z) (F.infinity.frame b k z⁻¹)) = _
  rw [map_mul,PowerSeries.constantCoeff_inv,
    constant_subst (reciprocalNormal_constant z),F.finite.frame_constant a ha k z hk,
    F.infinity.frame_constant b hb k z⁻¹ hq,inv_inv,F.diagonal_transition z hz k,
    mul_assoc,mul_inv_cancel₀ hq,mul_one,zpow_natCast]


include ha hb in
theorem normalizedSection_constant (j : ι) (z : ℂ) :
    PowerSeries.constantCoeff (F.normalizedSection a b ha hb j).val.1 z = (p j).eval z := by
  change PowerSeries.constantCoeff (F.finite.sectionSeries a j) z = _
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simpa only [ChartData.sectionSeries,PowerSeries.coeff_mk,
    PowerSeries.coeff_zero_eq_constantCoeff] using F.finite.sectionValue_constant a ha j z

end TwoChartData
end

open SplitTangent.DiagonalRationality
namespace ChartData
variable {ι : Type*} [Fintype ι] {p : ι → ℂ[X]} (F : ChartData p)
  (a : ι → ℂ[X]) (ha : ∑ i, a i * p i = 1)

include ha in
theorem sectionValue_ratio (k j : ι) (z : ℂ) (hk : (p k).eval z ≠ 0) :
    F.sectionValue a j z * (F.sectionValue a k z)⁻¹ = F.ratio k j z := by
  have hs : PowerSeries.constantCoeff (F.sectionValue a k z) ≠ 0 := by
    rw [F.sectionValue_constant a ha k z]; exact hk
  have hmul : F.sectionValue a j z = F.ratio k j z * F.sectionValue a k z := by
    rw [F.sectionValue_eq a ha k j z hk,F.sectionValue_eq a ha k k z hk,
      localSection,localSection,F.identity k z hk,mul_one,mul_comm]
  rw [hmul,mul_assoc,PowerSeries.mul_inv_cancel _ hs,mul_one]

end ChartData
end SplitTangent.FormalProjective

namespace SplitTangent.DiagonalRationality

 

theorem simultaneous_reconstruction_on_diagonal_patch {ι : Type*} [Fintype ι]
    {T : ℂ → PowerSeries ℂ} (d : ℕ)
    (hT : ∀ z : ℂ, z ≠ 0 → PowerSeries.constantCoeff (T z) = z ^ (d : ℤ))
    (s : formalSections T) (t : ι → formalSections T)
    (hs : ∃ z : ℂ, PowerSeries.constantCoeff s.val.1 z ≠ 0) :
    ∃ (a b : ι → BiCoefficients (4*(d+1))) (r : ι → ℕ)
      (A B : ι → Polynomial (ℂ → ℂ)) (U : Set ℂ),
      IsOpen U ∧ U.Nonempty ∧
      (∀ i, b i ≠ 0 ∧ normalPolynomial (4*(d+1)) (a i) = Polynomial.X ^ r i * A i ∧
        normalPolynomial (4*(d+1)) (b i) = Polynomial.X ^ r i * B i) ∧
      ∀ z ∈ U, PowerSeries.constantCoeff s.val.1 z ≠ 0 ∧ ∀ i,
        (B i).coeff 0 z ≠ 0 ∧
        AnalyticAt ℂ (fun w => -polynomialEvaluation (A i) w / polynomialEvaluation (B i) w) (z,0) ∧
        HasFPowerSeriesAt
          (fun v => -polynomialEvaluation (A i) (z,v) / polynomialEvaluation (B i) (z,v))
          (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n
            (evaluateCoefficients z (t i).val.1 * (evaluateCoefficients z s.val.1)⁻¹))) 0 := by
  classical
  choose a b r A B z hb ha hbP hAD hBD hBz hsZ hq hc using
    fun i => exists_convergent_rational_quotient d hT s (t i) hs
  have hsD : Differentiable ℂ (PowerSeries.constantCoeff s.val.1) := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using s.property.1 0
  obtain ⟨w,hsw,hw⟩ := exists_common_nonzero_finset Finset.univ
    (fun i => (B i).coeff 0) (PowerSeries.constantCoeff s.val.1)
    (fun i _ => hBD i 0) hsD
    (fun i _ he => hBz i (congrFun he (z i))) hs
  let H : ℂ → ℂ := fun z => PowerSeries.constantCoeff s.val.1 z * ∏ i, (B i).coeff 0 z
  have hHD : Differentiable ℂ H := hsD.mul (Differentiable.fun_finsetProd (fun i _ => hBD i 0))
  let U : Set ℂ := {z | H z ≠ 0}
  refine ⟨a,b,r,A,B,U,isOpen_ne_fun hHD.continuous continuous_const,
    ⟨w,mul_ne_zero hsw (Finset.prod_ne_zero_iff.mpr hw)⟩,
    fun i => ⟨hb i,ha i,hbP i⟩,?_⟩
  intro z hz
  have hz' : PowerSeries.constantCoeff s.val.1 z ≠ 0 ∧ ∀ i, (B i).coeff 0 z ≠ 0 := by
    simpa only [U,H,mem_ofPred_eq,mul_ne_zero_iff,Finset.prod_ne_zero_iff,Finset.mem_univ,true_implies] using hz
  refine ⟨hz'.1,fun i => ⟨hz'.2 i,polynomial_quotient_analytic (hAD i) (hBD i) (hz'.2 i),
    hc i z (hz'.2 i) hz'.1⟩⟩

end SplitTangent.DiagonalRationality

end ReconstructionImports
open Set Filter Topology

namespace SplitTangent.HolomorphicJets
section
open SplitTangent.DiagonalRationality
variable {σ : Type*} [Fintype σ]


theorem analyticJet_hasSeries {g : ℂ → σ → ℂ} (hg : AnalyticAt ℂ g 0) :
    HasFPowerSeriesAt g (jetSeries (analyticJet g)) 0 := by
  apply HasFPowerSeriesAt.pi
  intro i
  exact hasFPowerSeries_taylorSeries (analyticAt_pi_iff.mp hg i)

 

theorem composeCoefficient_analyticJet {g : ℂ → σ → ℂ} {h : (σ → ℂ) → ℂ}
    (hg : AnalyticAt ℂ g 0) (hh : AnalyticAt ℂ h (g 0)) (n : ℕ) :
    composeCoefficient h (analyticJet g) n = PowerSeries.coeff n (taylorSeries (h ∘ g)) := by
  obtain ⟨q,hq⟩ := hh
  have hq' : HasFPowerSeriesAt h q (analyticJet g 0) := by simpa using hq
  rw [composeCoefficient_eq_formal _ hq']
  have hc := hq.comp (analyticJet_hasSeries hg)
  have ht := hasFPowerSeries_taylorSeries hc.analyticAt
  have he := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n)
    (ht.eq_formalMultilinearSeries hc)
  exact he.symm.trans (FormalMultilinearSeries.coeff_ofScalars
    (p := fun k => PowerSeries.coeff k (taylorSeries (h ∘ g))) (n := n))

end
section
open SplitTangent.DiagonalRationality
open PowerSeries

 
theorem formalComposition_outer_causal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (p : FormalMultilinearSeries ℂ E F) {q r : FormalMultilinearSeries ℂ F G} {n : ℕ}
    (h : ∀ k, k ≤ n → q k = r k) : (q.comp p) n = (r.comp p) n := by
  unfold FormalMultilinearSeries.comp
  apply Finset.sum_congr rfl
  intro c _
  ext v
  simp only [FormalMultilinearSeries.compAlongComposition_apply]
  rw [h c.length c.length_le]

 
theorem coeff_subst_trunc {R : Type*} [CommRing R] (b f : PowerSeries R)
    (hb : constantCoeff b = 0) (n : ℕ) :
    coeff n (subst b f) = coeff n (subst b (trunc (n+1) f : PowerSeries R)) := by
  have hs := HasSubst.of_constantCoeff_zero' hb
  obtain ⟨c,hc⟩ := (X_dvd_iff.mpr hb)
  have he := congrArg (subst b) (eq_X_pow_mul_shift_add_trunc (n+1) f)
  rw [subst_add hs,subst_mul hs,subst_pow hs,subst_X hs,hc,mul_pow] at he
  rw [hc,he,map_add,mul_assoc,coeff_X_pow_mul']
  simp

 

theorem coeff_subst_congr {R : Type*} [CommRing R] (b f g : PowerSeries R)
    (hb : constantCoeff b = 0) (n : ℕ) (h : ∀ k, k ≤ n → coeff k f = coeff k g) :
    coeff n (subst b f) = coeff n (subst b g) := by
  rw [coeff_subst_trunc b f hb n,coeff_subst_trunc b g hb n]
  have ht : trunc (n+1) f = trunc (n+1) g := by
    ext k
    simp only [coeff_trunc]
    split_ifs with hk
    · exact h k (by omega)
    · rfl
  rw [ht]


theorem taylorSeries_polynomial_comp (p : Polynomial ℂ) {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) :
    taylorSeries (fun z => p.eval (g z)) = Polynomial.aeval (taylorSeries g) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add,map_add]
    change taylorSeries ((fun z => p.eval (g z)) + (fun z => q.eval (g z))) = _
    rw [taylorSeries_add (f := fun z => p.eval (g z)) (g := fun z => q.eval (g z))
      ((polynomial_analyticAt p (g 0)).comp hg) ((polynomial_analyticAt q (g 0)).comp hg),hp,hq]
  | monomial n c =>
    simp only [Polynomial.eval_monomial,Polynomial.aeval_monomial]
    change taylorSeries ((fun _ => c) * (fun z => g z ^ n)) = _
    rw [taylorSeries_mul (f := fun _ => c) (g := fun z => g z ^ n) analyticAt_const (hg.pow n),taylorSeries_const]
    congr 1
    induction n with
    | zero => simp [taylorSeries_const]
    | succ n ih =>
      simp only [pow_succ]
      change taylorSeries ((fun z => g z ^ n) * g) = _
      rw [taylorSeries_mul (f := fun z => g z ^ n) (g := g) (hg.pow n) hg,ih]

 

theorem coeff_taylor_comp_trunc {h g : ℂ → ℂ} (hh : AnalyticAt ℂ h 0)
    (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) (n : ℕ) :
    coeff n (taylorSeries (h ∘ g)) =
      coeff n (taylorSeries (fun z => (trunc (n+1) (taylorSeries h)).eval (g z))) := by
  let p := trunc (n+1) (taylorSeries h)
  have hha : HasFPowerSeriesAt h
      (FormalMultilinearSeries.ofScalars ℂ (fun k => coeff k (taylorSeries h))) (g 0) := by
    rw [hg0]; exact hasFPowerSeries_taylorSeries hh
  have hpa : HasFPowerSeriesAt (fun z => p.eval z)
      (FormalMultilinearSeries.ofScalars ℂ (fun k => p.coeff k)) (g 0) := by
    rw [hg0]
    simpa only [taylorSeries_polynomial,Polynomial.coeff_coe] using
      hasFPowerSeries_taylorSeries (polynomial_analyticAt p 0)
  let q := FormalMultilinearSeries.ofScalars ℂ (fun k => coeff k (taylorSeries g))
  have hq : HasFPowerSeriesAt g q 0 := hasFPowerSeries_taylorSeries hg
  have hc := hha.comp hq
  have hd := hpa.comp hq
  have he : (FormalMultilinearSeries.ofScalars ℂ (fun k => coeff k (taylorSeries h))).comp q n =
      (FormalMultilinearSeries.ofScalars ℂ (fun k => p.coeff k)).comp q n := by
    apply formalComposition_outer_causal
    intro k hk
    simp only [FormalMultilinearSeries.ofScalars,p,coeff_trunc,ite_eq_left (by omega : k < n+1)]
  have ht := (hasFPowerSeries_taylorSeries hc.analyticAt).eq_formalMultilinearSeries hc
  have hu := (hasFPowerSeries_taylorSeries hd.analyticAt).eq_formalMultilinearSeries hd
  have het := congrArg (fun s : FormalMultilinearSeries ℂ ℂ ℂ => s.coeff n) ht
  have heu := congrArg (fun s : FormalMultilinearSeries ℂ ℂ ℂ => s.coeff n) hu
  rw [FormalMultilinearSeries.coeff_ofScalars] at het heu
  exact het.trans ((congrArg (fun L : ContinuousMultilinearMap ℂ (fun _ : Fin n => ℂ) ℂ =>
    L (fun _ => 1)) he).trans heu.symm)

 

theorem taylorSeries_comp_zero {h g : ℂ → ℂ} (hh : AnalyticAt ℂ h 0)
    (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) :
    taylorSeries (h ∘ g) = subst (taylorSeries g) (taylorSeries h) := by
  have hzero : constantCoeff (taylorSeries g) = 0 := by
    rw [← coeff_zero_eq_constantCoeff,coeff_taylorSeries]; simpa using hg0
  have hs := HasSubst.of_constantCoeff_zero' hzero
  ext n
  rw [coeff_taylor_comp_trunc hh hg hg0 n,taylorSeries_polynomial_comp _ hg,
    coeff_subst_trunc _ _ hzero n,subst_coe hs]

end
open SplitTangent.DiagonalRationality PowerSeries
variable {σ : Type*} [Fintype σ]


omit [Fintype σ] in
@[simp] theorem reparamJet_zero (b : PowerSeries ℂ) (f : ℕ → σ → ℂ)
    (hb : constantCoeff b = 0) : reparamJet b f 0 = f 0 := by
  funext i
  rw [reparamJet,coeff_subst_trunc b _ hb 0,trunc_one_left]
  simp; rfl

 

omit [Fintype σ] in
theorem reparamJet_eq_analyticJet (f : ℕ → σ → ℂ) {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) {k n : ℕ} (hkn : k ≤ n) :
    reparamJet (taylorSeries g) f k =
      analyticJet (fun v => jetPolynomial f n (g v)) k := by
  have hb : constantCoeff (taylorSeries g) = 0 := by
    rw [← coeff_zero_eq_constantCoeff,coeff_taylorSeries]; simpa using hg0
  funext i
  unfold reparamJet analyticJet
  simp_rw [← polynomialJet_eval]
  have he := coeff_subst_congr (taylorSeries g) (PowerSeries.mk (fun l => f l i))
    (polynomialJet f n i : PowerSeries ℂ) hb k (by
      intro l hl
      simp only [coeff_mk,Polynomial.coeff_coe,polynomialJet_coeff,
        ite_eq_left (hl.trans hkn)])
  rw [he]
  have ht := taylorSeries_comp_zero (polynomial_analyticAt (polynomialJet f n i) 0) hg hg0
  rw [taylorSeries_polynomial] at ht
  exact (congrArg (coeff k) ht).symm

 

theorem formalSubst_reparam (f : ℕ → σ → ℂ) {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) {h : (σ → ℂ) → ℂ}
    (hh : AnalyticAt ℂ h (f 0)) :
    formalSubst h (reparamJet (taylorSeries g) f) =
      subst (taylorSeries g) (formalSubst h f) := by
  have hb : constantCoeff (taylorSeries g) = 0 := by
    rw [← coeff_zero_eq_constantCoeff,coeff_taylorSeries]; simpa using hg0
  ext n
  rw [coeff_formalSubst,composeCoefficient_causal h
    (fun k hk => reparamJet_eq_analyticJet f hg hg0 hk)]
  have hpoly : AnalyticAt ℂ (jetPolynomial f n) (g 0) := by
    rw [hg0]; exact (jetPolynomial_hasSeries f n).analyticAt
  have hG : AnalyticAt ℂ (fun v => jetPolynomial f n (g v)) 0 := hpoly.comp hg
  have hhG : AnalyticAt ℂ h (jetPolynomial f n (g 0)) := by simpa [hg0] using hh
  rw [composeCoefficient_analyticJet hG hhG]
  have hhF : AnalyticAt ℂ h (jetPolynomial f n 0) := by simpa using hh
  have hF := (jetPolynomial_hasSeries f n).analyticAt
  have ht := taylorSeries_comp_zero (hhF.comp hF) hg hg0
  change coeff n (taylorSeries ((h ∘ jetPolynomial f n) ∘ g)) = _
  rw [ht]
  apply coeff_subst_congr _ _ _ hb n
  intro k hk
  rw [coeff_formalSubst]
  exact (composeCoefficient_eq_laterJet f hh hk).symm

end SplitTangent.HolomorphicJets
namespace SplitTangent.FormalCauchy
open PowerSeries



theorem dCoeff_subst {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (δ : Derivation R A A) (b f : PowerSeries A) (hb : HasSubst b) :
    dCoeff δ (subst b f) = subst b (dCoeff δ f) +
      subst b (derivative _ f) * dCoeff δ b := by
  simpa only [dCoeff,PowerSeries.subst,PowerSeries.derivative,
    Finset.univ_unique,Finset.sum_singleton] using
    formal_coefficient_chain_rule δ (fun _ : Unit => b) hb.const f


theorem eval_dCoeff_subst {U : Set ℂ} (hU : IsOpen U) (u : ℂ)
    (b f : PowerSeries (AnalyticFunction U)) (hb : HasSubst b) :
    PowerSeries.map (analyticEvaluation U u) (dCoeff (analyticDerivation hU) (subst b f)) =
      subst (PowerSeries.map (analyticEvaluation U u) b)
        (PowerSeries.map (analyticEvaluation U u) (dCoeff (analyticDerivation hU) f)) +
      subst (PowerSeries.map (analyticEvaluation U u) b)
        (derivative _ (PowerSeries.map (analyticEvaluation U u) f)) *
      PowerSeries.map (analyticEvaluation U u) (dCoeff (analyticDerivation hU) b) := by
  have hm (g : PowerSeries (AnalyticFunction U)) :
      PowerSeries.map (analyticEvaluation U u) (subst b g) =
        subst (PowerSeries.map (analyticEvaluation U u) b)
          (PowerSeries.map (analyticEvaluation U u) g) := PowerSeries.map_subst hb g
  have hd : PowerSeries.map (analyticEvaluation U u) (derivative _ f) =
      derivative _ (PowerSeries.map (analyticEvaluation U u) f) := by
    ext n
    simp only [coeff_map,coeff_derivative,map_mul,map_add,map_natCast,map_one]
  rw [dCoeff_subst _ _ _ hb,map_add,map_mul,hm,hm,hd]




theorem eval_dCoeff_pullback {U W : Set ℂ} (hU : IsOpen U) (hW : IsOpen W)
    (α : ℂ → ℂ) (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    {u : ℂ} (hu : u ∈ W) (f : PowerSeries (AnalyticFunction U)) :
    PowerSeries.map (analyticEvaluation W u) (dCoeff (analyticDerivation hW)
      (PowerSeries.map (analyticPullback α hα hαU).toRingHom f)) =
      C (deriv α u) * PowerSeries.map (analyticEvaluation U (α u))
        (dCoeff (analyticDerivation hU) f) := by
  ext n
  rw [coeff_eval_dCoeff hW hu,coeff_C_mul,coeff_eval_dCoeff hU (hαU hu)]
  simp only [coeff_map,analyticPullback,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom]
  change deriv ((coeff n f).val ∘ α) u = deriv α u * deriv (coeff n f).val (α u)
  rw [deriv_comp u ((coeff n f).property _ (hαU hu)).differentiableAt
    (hα u hu).differentiableAt,mul_comm]

end SplitTangent.FormalCauchy
namespace SplitTangent.HolomorphicJets
section
open PowerSeries SplitTangent.DiagonalRationality SplitTangent.FormalCauchy


theorem sourceNormalFamily_hasSubst {W : Set ℂ} (α : ℂ → ℂ)
    (hα : AnalyticOnNhd ℂ α W) : HasSubst (sourceNormalFamily α hα) := by
  apply HasSubst.of_constantCoeff_zero'
  apply Subtype.ext
  funext u
  change coeff 0 (sourceNormal α u) = 0
  rw [coeff_zero_eq_constantCoeff_apply,sourceNormal_constant]

 

theorem sourceDifference_tangent {α : ℂ → ℂ} {u v : ℂ}
    (hα : AnalyticAt ℂ α u) (hα' : AnalyticAt ℂ α (u+v)) :
    tangentDeriv (sourceDifference α) (u,v) =
      normalDeriv (sourceDifference α) (u,v) - deriv α u := by
  have hD := sourceDifference_analytic hα hα'
  rw [← tangentDeriv_eq hD,← normalDeriv_eq hD]
  have h₁ := ((hα'.differentiableAt.hasDerivAt.comp u
    ((hasDerivAt_id u).add_const v)).sub hα.differentiableAt.hasDerivAt).deriv
  have h₂ := ((hα'.differentiableAt.hasDerivAt.comp v
    ((hasDerivAt_const v u).add (hasDerivAt_id v))).sub_const (α u)).deriv
  simp only [zero_add,mul_one] at h₁ h₂
  convert h₁.trans (congrArg (fun z => z - deriv α u) h₂.symm) using 1 <;>
    congr 1

theorem taylorSeries_sub {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorSeries (f-g) = taylorSeries f - taylorSeries g := by
  ext n
  simp only [map_sub,coeff_taylorSeries]
  rw [iteratedDeriv_sub hf.contDiffAt hg.contDiffAt,sub_div]

 

theorem eval_dCoeff_sourceNormal {W : Set ℂ} (hW : IsOpen W)
    (α : ℂ → ℂ) (hα : AnalyticOnNhd ℂ α W) {u : ℂ} (hu : u ∈ W) :
    PowerSeries.map (analyticEvaluation W u)
        (dCoeff (analyticDerivation hW) (sourceNormalFamily α hα)) =
      derivative _ (sourceNormal α u) - C (deriv α u) := by
  have hD := sourceDifference_analytic (hα u hu) (by simpa using hα u hu : AnalyticAt ℂ α (u+0))
  have hi : AnalyticAt ℂ (fun v : ℂ => (u,v)) 0 := analyticAt_const.prod analyticAt_id
  have hn : AnalyticAt ℂ (fun v => normalDeriv (sourceDifference α) (u,v)) 0 :=
    (normalDeriv_analytic hD).comp hi
  have he : (fun v => tangentDeriv (sourceDifference α) (u,v)) =ᶠ[nhds 0]
      (fun v => normalDeriv (sourceDifference α) (u,v) - deriv α u) := by
    have hs : ContinuousAt (fun v : ℂ => u+v) 0 := by fun_prop
    have ha0 : ∀ᶠ z in nhds u, AnalyticAt ℂ α z := (hα u hu).eventually_analyticAt
    have ha : ∀ᶠ v in nhds (0 : ℂ), AnalyticAt ℂ α (u+v) :=
      Filter.Tendsto.eventually (by simpa only [ContinuousAt,add_zero] using hs : Tendsto (fun v : ℂ => u+v) (nhds 0) (nhds u)) ha0
    filter_upwards [ha] with v hv
    exact sourceDifference_tangent (hα u hu) hv
  have hd : (fun v => normalDeriv (sourceDifference α) (u,v)) =ᶠ[nhds 0]
      deriv (fun v => sourceDifference α (u,v)) := by
    filter_upwards [hi.continuousAt hD.eventually_analyticAt] with v hv
    exact (normalDeriv_eq hv).symm
  ext n
  rw [coeff_eval_dCoeff hW hu]
  simp only [sourceNormalFamily,coeff_mk]
  change deriv (fun z => coeff n (taylorSeries (fun v => sourceDifference α (z,v)))) u = _
  rw [deriv_normalCoefficient hD,taylorSeries_congr he]
  change coeff n (taylorSeries ((fun v => normalDeriv (sourceDifference α) (u,v)) -
    (fun _ => deriv α u))) = _
  rw [taylorSeries_sub hn analyticAt_const,taylorSeries_const,taylorSeries_congr hd,taylorSeries_deriv]
  rfl

end
section
open PowerSeries SplitTangent.DiagonalRationality SplitTangent.FormalCauchy
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

 

omit [DecidableEq σ] in
theorem substitutedMatrix_idempotent (P : σ → σ → (σ → ℂ) → ℂ)
    (f : ℕ → σ → ℂ) (hP : ∀ i j, AnalyticAt ℂ (P i j) (f 0))
    (he : ∀ i j, (fun x => ∑ k, P i k x * P k j x) =ᶠ[nhds (f 0)] P i j) :
    substitutedMatrix P f * substitutedMatrix P f = substitutedMatrix P f := by
  funext i j
  simp only [substitutedMatrix,Matrix.mul_apply]
  have hs := formalSubst_sum Finset.univ (fun k x => P i k x * P k j x) f
    (fun k _ => (hP i k).mul (hP k j))
  rw [formalSubst_congr f (he i j)] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro k _
  exact (formalSubst_mul f (hP i k) (hP k j)).symm

 
omit [DecidableEq σ] in
theorem projector_source_identity {R : Type*} [CommRing R]
    (M : Matrix σ σ R) (a b : R) (v w : σ → R)
    (hM : M*M=M) (hv : v=M.mulVec w) :
    b • v = M.mulVec (a • w + (b-a) • v) := by
  have hm : M.mulVec v = v := by
    rw [hv,Matrix.mulVec_mulVec,hM]
  rw [Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul,hm,← hv]
  rw [← add_smul]
  simp



theorem eval_pullback {U W : Set ℂ} (α : ℂ → ℂ)
    (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U) (u : ℂ)
    (f : PowerSeries (AnalyticFunction U)) :
    PowerSeries.map (analyticEvaluation W u)
      (PowerSeries.map (analyticPullback α hα hαU).toRingHom f) =
      PowerSeries.map (analyticEvaluation U (α u)) f := by
  ext n
  rfl

omit [Fintype σ] [DecidableEq σ] in
theorem eval_sourceTransform {U W : Set ℂ} (α : ℂ → ℂ)
    (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    (F : σ → PowerSeries (AnalyticFunction U)) (u : ℂ) (i : σ) :
    PowerSeries.map (analyticEvaluation W u) (sourceTransform α hα hαU F i) =
      subst (sourceNormal α u) (PowerSeries.map (analyticEvaluation U (α u)) (F i)) := by
  have hm := PowerSeries.map_subst (h := analyticEvaluation W u)
    (sourceNormalFamily_hasSubst α hα)
    (PowerSeries.map (analyticPullback α hα hαU).toRingHom (F i))
  change PowerSeries.map (analyticEvaluation W u) (sourceTransform α hα hαU F i) =
    subst (PowerSeries.map (analyticEvaluation W u) (sourceNormalFamily α hα))
      (PowerSeries.map (analyticEvaluation W u)
        (PowerSeries.map (analyticPullback α hα hαU).toRingHom (F i))) at hm
  rw [sourceNormalFamily_eval,eval_pullback] at hm
  exact hm

omit [Fintype σ] [DecidableEq σ] in
theorem normal_sourceTransform {U W : Set ℂ} (α : ℂ → ℂ)
    (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    (F : σ → PowerSeries (AnalyticFunction U)) (u : ℂ) (i : σ) :
    derivative _ (PowerSeries.map (analyticEvaluation W u) (sourceTransform α hα hαU F i)) =
      derivative _ (sourceNormal α u) * subst (sourceNormal α u)
        (derivative _ (PowerSeries.map (analyticEvaluation U (α u)) (F i))) := by
  rw [eval_sourceTransform,derivative_subst
    (HasSubst.of_constantCoeff_zero' (sourceNormal_constant α u)),mul_comm]

 
omit [Fintype σ] [DecidableEq σ] in
theorem tangent_sourceTransform {U W : Set ℂ} (hU : IsOpen U) (hW : IsOpen W)
    (α : ℂ → ℂ) (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    (F : σ → PowerSeries (AnalyticFunction U)) {u : ℂ} (hu : u ∈ W) (i : σ) :
    PowerSeries.map (analyticEvaluation W u)
      (dCoeff (analyticDerivation hW) (sourceTransform α hα hαU F i)) =
      C (deriv α u) * subst (sourceNormal α u)
        (PowerSeries.map (analyticEvaluation U (α u)) (dCoeff (analyticDerivation hU) (F i))) +
      (derivative _ (sourceNormal α u) - C (deriv α u)) * subst (sourceNormal α u)
        (derivative _ (PowerSeries.map (analyticEvaluation U (α u)) (F i))) := by
  rw [sourceTransform,eval_dCoeff_subst hW u _ _ (sourceNormalFamily_hasSubst α hα),
    sourceNormalFamily_eval,eval_dCoeff_pullback hU hW α hα hαU hu,
    eval_pullback,eval_dCoeff_sourceNormal hW α hα hu,
    subst_mul (HasSubst.of_constantCoeff_zero' (sourceNormal_constant α u)),subst_C]
  congr 1
  exact mul_comm _ _

 

omit [DecidableEq σ] in
theorem substitutedMatrix_sourceTransform {U W : Set ℂ} (α : ℂ → ℂ)
    (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    (F : σ → PowerSeries (AnalyticFunction U)) {u : ℂ} (hu : u ∈ W)
    (P : σ → σ → (σ → ℂ) → ℂ)
    (hP : ∀ i j, AnalyticAt ℂ (P i j) (fun l => coeff 0 (F l) (α u))) :
    substitutedMatrix P (fun n i => coeff n (sourceTransform α hα hαU F i) u) =
      (substitutedMatrix P (fun n i => coeff n (F i) (α u))).map (subst (sourceNormal α u)) := by
  have hb : AnalyticAt ℂ (fun v => sourceDifference α (u,v)) 0 :=
    (sourceDifference_analytic (hα u hu) (by simpa using hα u hu : AnalyticAt ℂ α (u+0))).comp
      (analyticAt_const.prod analyticAt_id)
  have hz : sourceDifference α (u,0) = 0 := by simp [sourceDifference]
  have hf : (fun n i => coeff n (sourceTransform α hα hαU F i) u) =
      reparamJet (sourceNormal α u) (fun n i => coeff n (F i) (α u)) := by
    funext n i
    have he := congrArg (coeff n) (eval_sourceTransform α hα hαU F u i)
    have hm : PowerSeries.map (analyticEvaluation U (α u)) (F i) =
        PowerSeries.mk (fun k => coeff k (F i) (α u)) := by
      ext k
      simp
    rw [hm] at he
    exact he
  rw [hf]
  funext i j
  exact formalSubst_reparam _ hb hz (hP i j)

end
open PowerSeries SplitTangent.FormalCauchy
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

 

omit [DecidableEq σ] in
theorem cauchy_source_covariance {U W : Set ℂ} (hU : IsOpen U) (hW : IsOpen W)
    (α : ℂ → ℂ) (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    (F : σ → PowerSeries (AnalyticFunction U)) {u : ℂ} (hu : u ∈ W)
    (P : σ → σ → (σ → ℂ) → ℂ)
    (hP : ∀ i j, AnalyticAt ℂ (P i j) (fun l => coeff 0 (F l) (α u)))
    (hidem : ∀ i j, (fun x => ∑ k, P i k x * P k j x)
      =ᶠ[nhds (fun l => coeff 0 (F l) (α u))] P i j)
    (hsol : (fun i => derivative _ (PowerSeries.map (analyticEvaluation U (α u)) (F i))) =
      (substitutedMatrix P (fun n i => coeff n (F i) (α u))).mulVec
        (fun i => PowerSeries.map (analyticEvaluation U (α u)) (dCoeff (analyticDerivation hU) (F i)))) :
    (fun i => derivative _ (PowerSeries.map (analyticEvaluation W u) (sourceTransform α hα hαU F i))) =
      (substitutedMatrix P (fun n i => coeff n (sourceTransform α hα hαU F i) u)).mulVec
        (fun i => PowerSeries.map (analyticEvaluation W u)
          (dCoeff (analyticDerivation hW) (sourceTransform α hα hαU F i))) := by
  let M₀ := substitutedMatrix P (fun n i => coeff n (F i) (α u))
  have hb := HasSubst.of_constantCoeff_zero' (sourceNormal_constant α u)
  let r : PowerSeries ℂ →+* PowerSeries ℂ := (substAlgHom hb).toRingHom
  have hr : (r : PowerSeries ℂ → PowerSeries ℂ) = subst (sourceNormal α u) := coe_substAlgHom hb
  let M := M₀.map r
  let v : σ → PowerSeries ℂ := fun i => r (derivative _ (PowerSeries.map (analyticEvaluation U (α u)) (F i)))
  let w : σ → PowerSeries ℂ := fun i => r (PowerSeries.map (analyticEvaluation U (α u))
    (dCoeff (analyticDerivation hU) (F i)))
  have hM₀ : M₀*M₀=M₀ := substitutedMatrix_idempotent P _ hP hidem
  have hM : M*M=M := by
    change M₀.map r * M₀.map r = M₀.map r
    rw [← Matrix.map_mul,hM₀]
  have hv : v=M.mulVec w := by
    funext i
    have hs := congrArg r (congrFun hsol i)
    exact hs.trans (r.map_mulVec M₀ _ i)
  have hn : (fun i => derivative _ (PowerSeries.map (analyticEvaluation W u)
      (sourceTransform α hα hαU F i))) = derivative _ (sourceNormal α u) • v := by
    funext i
    simpa only [Pi.smul_apply,smul_eq_mul,v,hr] using normal_sourceTransform α hα hαU F u i
  have ht : (fun i => PowerSeries.map (analyticEvaluation W u)
      (dCoeff (analyticDerivation hW) (sourceTransform α hα hαU F i))) =
      C (deriv α u) • w + (derivative _ (sourceNormal α u) - C (deriv α u)) • v := by
    funext i
    simpa only [Pi.smul_apply,Pi.add_apply,smul_eq_mul,v,w,hr] using
      tangent_sourceTransform hU hW α hα hαU F hu i
  have hm : substitutedMatrix P (fun n i => coeff n (sourceTransform α hα hαU F i) u) = M := by
    simpa only [M,M₀,hr] using substitutedMatrix_sourceTransform α hα hαU F hu P hP
  rw [hn,ht,hm]
  exact projector_source_identity M (C (deriv α u)) (derivative _ (sourceNormal α u)) v w hM hv

end SplitTangent.HolomorphicJets
namespace SplitTangent.HolomorphicJets
section
open PowerSeries SplitTangent.FormalCauchy SplitTangent.DiagonalRationality
variable {σ τ : Type*} [Fintype σ] [Fintype τ]



theorem sourceNormal_inv (u : ℂ) (hu : u ≠ 0) :
    sourceNormal (fun z : ℂ => z⁻¹) u = (C u + X)⁻¹ - C u⁻¹ := by
  have ha : AnalyticAt ℂ (fun v : ℂ => u+v) 0 := analyticAt_const.add analyticAt_id
  have hi : AnalyticAt ℂ (fun v : ℂ => (u+v)⁻¹) 0 := ha.fun_inv (by simpa using hu)
  have hl : taylorSeries (fun v : ℂ => u+v) = C u + X := by
    have he : (fun v : ℂ => u+v) =
        (fun v => Polynomial.eval v ((Polynomial.C u + Polynomial.X) : Polynomial ℂ)) := by
      funext v
      simp
    rw [he,taylorSeries_polynomial]
    simp
  have he : (fun v : ℂ => (u+v)⁻¹ * (u+v)) =ᶠ[nhds 0] (fun _ => 1) := by
    filter_upwards [ha.continuousAt.eventually_ne (by simpa using hu : u+(0:ℂ)≠0)] with v hv
    exact inv_mul_cancel₀ hv
  have hp := taylorSeries_congr he
  change taylorSeries ((fun v : ℂ => (u+v)⁻¹) * (fun v : ℂ => u+v)) = _ at hp
  rw [taylorSeries_mul hi ha,hl,taylorSeries_const] at hp
  have hc : constantCoeff (C u + X) ≠ 0 := by simpa using hu
  have hinv : taylorSeries (fun v : ℂ => (u+v)⁻¹) = (C u+X)⁻¹ := by
    calc
      _ = (taylorSeries (fun v : ℂ => (u+v)⁻¹) * (C u+X)) * (C u+X)⁻¹ := by
        rw [mul_assoc,PowerSeries.mul_inv_cancel _ hc,mul_one]
      _ = _ := by rw [hp]; simp
  unfold sourceNormal sourceDifference
  change taylorSeries ((fun v : ℂ => (u+v)⁻¹) - (fun _ => u⁻¹)) = _
  rw [taylorSeries_sub hi analyticAt_const,hinv,taylorSeries_const]

end
section
open PowerSeries SplitTangent.FormalCauchy SplitTangent.DiagonalRationality
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [Fintype σ] [DecidableEq σ] in
theorem normalVector_of_series {U : Set ℂ} (F : σ → PowerSeries (AnalyticFunction U)) (u : ℂ) :
    normalVector (fun n i => coeff n (F i) u) =
      fun i => derivative _ (PowerSeries.map (analyticEvaluation U u) (F i)) := by
  funext i
  change derivative _ (PowerSeries.mk (fun n => coeff n (F i) u)) = _
  congr 1
  ext n
  rw [coeff_mk,coeff_map]
  rfl

omit [Fintype σ] [DecidableEq σ] in
theorem tangentVector_of_series {U : Set ℂ} (hU : IsOpen U)
    (F : σ → PowerSeries (AnalyticFunction U)) {u : ℂ} (hu : u ∈ U) :
    tangentVector (fun n z i => coeff n (F i) z) u =
      fun i => PowerSeries.map (analyticEvaluation U u) (dCoeff (analyticDerivation hU) (F i)) := by
  funext i; ext n
  simp only [tangentVector,coeff_mk,coeff_eval_dCoeff hU hu]

omit [Fintype σ] [DecidableEq σ] in
theorem sourceFamily_eval {U W : Set ℂ} (α : ℂ → ℂ)
    (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    (f : ℕ → ℂ → σ → ℂ) (hf : ∀ n i, AnalyticOnNhd ℂ (fun u => f n u i) U)
    (u : ℂ) :
    (fun n => sourceFamily α hα hαU f hf n u) =
      reparamJet (sourceNormal α u) (fun n => f n (α u)) := by
  funext n i
  have he := eval_sourceTransform α hα hαU (familySeries f hf) u i
  rw [familySeries_eval] at he
  have hc := congrArg (coeff n) he
  change coeff n (sourceTransform α hα hαU (familySeries f hf) i) u = _ at hc
  exact hc

 

omit [DecidableEq σ] in
theorem CauchyOn.source {U W : Set ℂ} (hU : IsOpen U) (hW : IsOpen W)
    {g : ℂ → σ → ℂ} {P : σ → σ → (σ → ℂ) → ℂ}
    {f : ℕ → ℂ → σ → ℂ} (hf : CauchyOn U g P f)
    (α : ℂ → ℂ) (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    (hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (P i j) (g u))
    (hidem : ∀ u ∈ U, ∀ i j, (fun x => ∑ k, P i k x * P k j x) =ᶠ[nhds (g u)] P i j) :
    CauchyOn W (g ∘ α) P (sourceFamily α hα hαU f hf.1) := by
  let F := familySeries f hf.1
  let G := sourceTransform α hα hαU F
  refine ⟨?_, ?_, ?_⟩
  · intro n i; exact (coeff n (G i)).property
  · intro u hu
    change (fun n => sourceFamily α hα hαU f hf.1 n u) 0 = (g ∘ α) u
    rw [sourceFamily_eval,reparamJet_zero _ _ (sourceNormal_constant α u),hf.2.1 _ (hαU hu)]
    rfl
  · intro u hu
    change normalVector (fun n i => coeff n (G i) u) =
      (substitutedMatrix P (fun n i => coeff n (G i) u)).mulVec
        (tangentVector (fun n z i => coeff n (G i) z) u)
    rw [normalVector_of_series,tangentVector_of_series hW G hu]
    apply cauchy_source_covariance hU hW α hα hαU F hu P
    · intro i j
      simpa only [F,familySeries_coeff,hf.2.1 _ (hαU hu)] using hP i j (α u) (hαU hu)
    · intro i j
      simpa only [F,familySeries_coeff,hf.2.1 _ (hαU hu)] using hidem (α u) (hαU hu) i j
    · have hs := hf.2.2 (α u) (hαU hu)
      have he : (fun n z i => coeff n (F i) z) = f := by
        funext n z i; exact familySeries_coeff f hf.1 z i n
      rw [← he,normalVector_of_series,tangentVector_of_series hU F (hαU hu)] at hs
      exact hs

 

omit [DecidableEq σ] in
theorem cauchyOn_source_glue {U W : Set ℂ} (hU : IsOpen U) (hW : IsOpen W)
    {g : ℂ → σ → ℂ} {P : σ → σ → (σ → ℂ) → ℂ}
    {f : ℕ → ℂ → σ → ℂ} (hf : CauchyOn U g P f)
    (α : ℂ → ℂ) (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    {f' : ℕ → ℂ → σ → ℂ} (hf' : CauchyOn W (g ∘ α) P f')
    (hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (P i j) (g u))
    (hidem : ∀ u ∈ U, ∀ i j, (fun x => ∑ k, P i k x * P k j x) =ᶠ[nhds (g u)] P i j) :
    ∀ n u, u ∈ W → reparamJet (sourceNormal α u) (fun k => f k (α u)) n = f' n u := by
  intro n u hu
  have he := cauchyOn_unique hW (hf.source hU hW α hα hαU hP hidem) hf' n u hu
  exact (congrFun (sourceFamily_eval α hα hαU f hf.1 u) n).symm.trans he

end

end SplitTangent.HolomorphicJets

namespace SplitTangent.TangentSplitting

section
open HolomorphicJets PowerSeries
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)





theorem localJet_source_glue {g g' : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (hg' : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g')
    {W : Set ℂ} (hW : IsOpen W) (α : ℂ → ℂ) (hα : AnalyticOnNhd ℂ α W)
    (he : Set.EqOn g' (g ∘ α) W) (x : X.Carrier) {u : ℂ}
    (hu : u ∈ W) (hx : u ∈ coordinateDomain g' x) (n : ℕ) :
    reparamJet (sourceNormal α u) (fun k => S.localJet hg x k (α u)) n =
      S.localJet hg' x n u := by
  let U := coordinateDomain g x
  let W' := W ∩ coordinateDomain g' x
  have hU : IsOpen U := coordinateDomain_open hg x
  have hW' : IsOpen W' := hW.inter (coordinateDomain_open hg' x)
  have hα' : AnalyticOnNhd ℂ α W' := hα.mono Set.inter_subset_left
  have hαU : MapsTo α W' U := by
    intro z hz
    change g (α z) ∈ (chartAt (Model X) x).source
    rw [← (show g' z = g (α z) from he hz.1)]
    exact hz.2
  have he' : Set.EqOn (coordinateCurve g' x) (coordinateCurve g x ∘ α) W' := by
    intro z hz
    change (chartAt (Model X) x) (g' z) = (chartAt (Model X) x) (g (α z))
    exact congrArg (chartAt (Model X) x) (he hz.1)
  apply cauchyOn_source_glue hU hW' (S.localJet_solution hg x) α hα' hαU
    (((S.localJet_solution hg' x).mono Set.inter_subset_right).congr_initial he')
    ?_ ?_ n u ⟨hu,hx⟩
  · intro i j z hz
    exact S.coordinateMatrix_analytic x i j _ ((chartAt (Model X) x).map_source hz)
  · intro z hz i j
    have ht := (chartAt (Model X) x).map_source hz
    filter_upwards [(chartAt (Model X) x).open_target.mem_nhds ht] with w hw
    exact S.coordinateMatrix_idempotent x hw i j

 

theorem scalarJet_source_glue {g g' : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (hg' : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g')
    {W : Set ℂ} (hW : IsOpen W) (α : ℂ → ℂ) (hα : AnalyticOnNhd ℂ α W)
    (he : Set.EqOn g' (g ∘ α) W) {u : ℂ} (hu : u ∈ W)
    (h : X.Carrier → ℂ) (hh : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω h (g' u)) :
    subst (sourceNormal α u) (S.scalarJet hg h (α u)) = S.scalarJet hg' h u := by
  let x := g' u
  have hx : u ∈ coordinateDomain g' x := mem_chart_source (Model X) x
  have he0 : g' u = g (α u) := he hu
  have hxg : α u ∈ coordinateDomain g x := by
    change g (α u) ∈ (chartAt (Model X) x).source
    rw [← he0]
    exact hx
  have hhg : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω h (g (α u)) := by
    rw [← he0]; exact hh
  rw [S.scalarJet_eq_local hg h x hxg hhg, S.scalarJet_eq_local hg' h x hx hh]
  have hj : (fun n => S.localJet hg' x n u) =
      reparamJet (sourceNormal α u) (fun n => S.localJet hg x n (α u)) := by
    funext n
    exact (S.localJet_source_glue hg hg' hW α hα he x hu hx n).symm
  rw [hj]
  have hnormal : AnalyticAt ℂ (fun v => sourceDifference α (u,v)) 0 :=
    (sourceDifference_analytic (hα u hu) (by simpa using hα u hu)).comp
      (analyticAt_const.prod analyticAt_id)
  have h0 : sourceDifference α (u,0) = 0 := by simp [sourceDifference]
  have hcoord : AnalyticAt ℂ (scalarCoordinate h x) (S.localJet hg x 0 (α u)) := by
    rw [(S.localJet_solution hg x).2.1 (α u) hxg]
    exact scalarCoordinate_analytic hxg hhg
  exact (formalSubst_reparam _ hnormal h0 hcoord).symm

end

open HolomorphicJets PowerSeries

end SplitTangent.TangentSplitting

section CurveImports

open Filter Topology Polynomial
namespace SplitTangent.ProjectiveLine



theorem finite_nonanalytic {f : ℂ → ℂ} (hf : Meromorphic f)
    (hInf : MeromorphicAtInfinity f) : {z : ℂ | ¬ AnalyticAt ℂ f z}.Finite := by
  have he : ∀ᶠ w in nhds 0, w ≠ 0 → AnalyticAt ℂ (fun z => f z⁻¹) w := by
    simpa only [eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff] using
      hInf.eventually_analyticAt
  obtain ⟨r,hr,hrsub⟩ := Metric.eventually_nhds_iff.mp he
  have hlarge : ∀ z : ℂ, r⁻¹ < ‖z‖ → AnalyticAt ℂ f z := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h; simp only [h, norm_zero] at hz
      exact (not_lt_of_ge (inv_nonneg.mpr hr.le)) hz
    have hinv : dist z⁻¹ 0 < r := by
      rw [dist_zero_right, norm_inv, inv_lt_comm₀ (norm_pos_iff.mpr hz0) hr]
      exact hz
    have ha := hrsub hinv (inv_ne_zero hz0)
    have hc := ha.comp (analyticAt_id.inv hz0)
    simpa only [Function.comp_def, inv_inv] using hc
  have hK := (isCompact_closedBall (0 : ℂ) r⁻¹).finite_sdiff_of_mem_codiscreteWithin
    ((hf.meromorphicOn (s := Metric.closedBall 0 r⁻¹)).analyticAt_mem_codiscreteWithin)
  apply hK.subset
  intro z hz
  exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using
    (not_lt.mp (fun h => hz (hlarge z h))), hz⟩

 

theorem exists_polynomial_denominator {f : ℂ → ℂ} (hf : Meromorphic f)
    (hInf : MeromorphicAtInfinity f) :
    ∃ q : ℂ[X], q ≠ 0 ∧ Differentiable ℂ (fun z => q.eval z * f z) := by
  classical
  let B := (finite_nonanalytic hf hInf).toFinset
  choose n hn using fun x => hf x
  let q : ℂ[X] := ∏ a ∈ B, (X - C a) ^ n a
  refine ⟨q, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (fun a ha => pow_ne_zero _ (X_sub_C_ne_zero a))
  · intro z
    by_cases hz : z ∈ B
    · have hfactor : q = (X - C z) ^ n z * ∏ a ∈ B.erase z, (X - C a) ^ n a := by
        exact (Finset.mul_prod_erase B _ hz).symm
      have han : AnalyticAt ℂ
          (fun t => (∏ a ∈ B.erase z, (X - C a) ^ n a).eval t * ((t-z)^n z * f t)) z :=
        (AnalyticOnNhd.eval_polynomial (∏ a ∈ B.erase z, (X - C a) ^ n a) z (mem_univ z)).mul
          (by simpa only [smul_eq_mul] using hn z)
      apply han.differentiableAt.congr_of_eventuallyEq
      filter_upwards with t
      simp only [hfactor, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
      ring
    · have hz' : AnalyticAt ℂ f z := by simpa [B] using hz
      exact (by fun_prop : DifferentiableAt ℂ (fun t => q.eval t) z).mul hz'.differentiableAt

 

theorem polynomial_growth_atInfinity {f : ℂ → ℂ} (hInf : MeromorphicAtInfinity f) :
    ∃ (n : ℕ) (C R : ℝ), ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖^n := by
  obtain ⟨n,hn⟩ := hInf
  let h : ℂ → ℂ := fun w => w^n * f w⁻¹
  have hh : AnalyticAt ℂ h 0 := by simpa [h, smul_eq_mul] using hn
  have he : ∀ᶠ w in nhds 0, ‖h w‖ < ‖h 0‖ + 1 :=
    hh.continuousAt.norm.eventually_lt_const (by linarith)
  obtain ⟨r,hr,hrsub⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨n, ‖h 0‖+1, max 1 (r⁻¹+1), ?_⟩
  intro z hz
  have hzn : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hz)
  have hzlarge : r⁻¹ < ‖z‖ := by have := (le_max_right 1 (r⁻¹+1)).trans hz; linarith
  have hw : dist z⁻¹ 0 < r := by
    rw [dist_zero_right, norm_inv, inv_lt_comm₀ hzn hr]
    exact hzlarge
  have hb : ‖h z⁻¹‖ ≤ ‖h 0‖+1 := (hrsub hw).le
  have heq : ‖f z‖ = ‖z‖^n * ‖h z⁻¹‖ := by
    simp only [h, inv_inv, norm_mul, norm_pow, norm_inv]
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hzn.ne', one_pow, one_mul]
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hb (pow_nonneg (norm_nonneg _) _)).trans_eq (mul_comm _ _)

 
theorem iteratedDeriv_zero_of_tail_growth {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {n : ℕ} {C R₀ : ℝ} (hbound : ∀ z : ℂ, R₀ ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖^n)
    {k : ℕ} (hk : n < k) : iteratedDeriv k f 0 = 0 := by
  have hb : ∀ R : ℝ, max 1 R₀ ≤ R →
      ‖iteratedDeriv k f 0‖ ≤ (k.factorial : ℝ) * C / R^(k-n) := by
    intro R hR
    have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hR)
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) k hR0
      hf.diffContOnCl (fun z hz => by
        have hzR : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_zero_right] using hz
        simpa only [hzR] using hbound z (hzR ▸ ((le_max_right _ _).trans hR)))
    convert h using 1
    rw [pow_sub₀ R hR0.ne' hk.le]
    field_simp
  apply norm_le_zero_iff.mp
  apply ge_of_tendsto (show Tendsto (fun R : ℝ => (k.factorial : ℝ) * C / R^(k-n))
      atTop (nhds 0) from tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega)))
  exact (eventually_ge_atTop (max 1 R₀)).mono (fun R hR => hb R hR)

 

theorem exists_polynomial_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hInf : MeromorphicAtInfinity f) : ∃ p : ℂ[X], ∀ z, f z = p.eval z := by
  obtain ⟨n,C,R,hb⟩ := polynomial_growth_atInfinity hInf
  refine ⟨∑ k ∈ Finset.range (n+1), monomial k ((k.factorial : ℂ)⁻¹ * iteratedDeriv k f 0), ?_⟩
  intro z
  rw [← Complex.taylorSeries_eq_of_entire' 0 z hf]
  rw [tsum_eq_sum (s := Finset.range (n+1)) (fun k hk => by
    have hnk : n < k := by simpa using hk
    rw [iteratedDeriv_zero_of_tail_growth hf hb hnk]
    simp)]
  simp [Polynomial.eval_finsetSum, Polynomial.eval_monomial]

 
theorem meromorphicAt_polynomial_eval {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x)
    (p : ℂ[X]) : MeromorphicAt (fun z => p.eval (f z)) x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [eval_add, Pi.add_apply] using hp.fun_add hq
  | monomial n a => simpa only [eval_monomial, Pi.mul_apply, Pi.pow_apply] using (MeromorphicAt.const a x).fun_mul (hf.fun_pow n)

 

theorem rationality {f : ℂ → ℂ} (hf : Meromorphic f)
    (hInf : MeromorphicAtInfinity f) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z, q.eval z * f z = p.eval z) ∧
      ∀ z, q.eval z ≠ 0 → f z = p.eval z / q.eval z := by
  obtain ⟨q,hq,hqf⟩ := exists_polynomial_denominator hf hInf
  have hqInf : MeromorphicAtInfinity (fun z => q.eval z * f z) := by
    exact (meromorphicAt_polynomial_eval (MeromorphicAt.id 0).inv q).mul hInf
  obtain ⟨p,hp⟩ := exists_polynomial_of_entire hqf hqInf
  refine ⟨p,q,hq,hp,?_⟩
  intro z hz
  exact (eq_div_iff hz).mpr (by simpa only [mul_comm] using hp z)

end SplitTangent.ProjectiveLine

namespace SplitTangent

 

theorem projectiveCoordinates_change {N : ℕ} (p : ProjectiveSpace N)
    (i j k : Fin (N+1)) (hk : p.rep k ≠ 0) :
    projectiveCoordinates i p j = projectiveCoordinates k p j / projectiveCoordinates k p i := by
  simp only [projectiveCoordinates, div_eq_mul_inv, mul_inv_rev, inv_inv]
  calc
    (p.rep i)⁻¹ * p.rep j = ((p.rep k)⁻¹ * p.rep k) * ((p.rep i)⁻¹ * p.rep j) := by
      rw [inv_mul_cancel₀ hk, one_mul]
    _ = _ := by ring

 

theorem projective_ratio_meromorphic {X : ComplexManifold.{u}}
    (e : ProjectiveEmbedding X) (g : ℂ → X.Carrier)
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (i j : Fin (e.N+1)) : Meromorphic (fun z => projectiveCoordinates i (e.map (g z)) j) := by
  intro z
  obtain ⟨k,hk⟩ : ∃ k, (e.map (g z)).rep k ≠ 0 := by
    by_contra h
    push Not at h
    exact (e.map (g z)).rep_nonzero (funext h)
  have ha : AnalyticAt ℂ (fun w => projectiveCoordinates k (e.map (g w))) z :=
    (((e.holomorphic k).contMDiffAt ((e.open_patch k).mem_nhds hk)).comp z
      hg.contMDiffAt).contDiffAt.analyticAt
  have hj : AnalyticAt ℂ (fun w => projectiveCoordinates k (e.map (g w)) j) z :=
    (ContinuousLinearMap.proj j : (Fin (e.N+1) → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp ha
  have hi : AnalyticAt ℂ (fun w => projectiveCoordinates k (e.map (g w)) i) z :=
    (ContinuousLinearMap.proj i : (Fin (e.N+1) → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp ha
  apply (hj.meromorphicAt.div hi.meromorphicAt).congr
  apply Filter.EventuallyEq.filter_mono _ nhdsWithin_le_nhds
  filter_upwards [hg.continuous.continuousAt.preimage_mem_nhds ((e.open_patch k).mem_nhds hk)] with w hw
  exact (projectiveCoordinates_change (e.map (g w)) i j k hw).symm

 

theorem rationalCurve_ratio_meromorphicAtInfinity {X : ComplexManifold.{u}}
    (e : ProjectiveEmbedding X) (g : RationalCurve X) (i j : Fin (e.N+1)) :
    ProjectiveLine.MeromorphicAtInfinity (fun z => projectiveCoordinates i (e.map (g.finite z)) j) := by
  apply (projective_ratio_meromorphic e g.infinity g.infinity_holomorphic i j 0).congr
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := hz
  rw [g.overlap z⁻¹ (inv_ne_zero hz0), inv_inv]

 

theorem rationalCurve_ratios_are_rational {X : ComplexManifold.{u}}
    (e : ProjectiveEmbedding X) (g : RationalCurve X) (i j : Fin (e.N+1)) :
    ∃ p q : ℂ[X], q ≠ 0 ∧
      (∀ z, q.eval z * projectiveCoordinates i (e.map (g.finite z)) j = p.eval z) ∧
      ∀ z, q.eval z ≠ 0 → projectiveCoordinates i (e.map (g.finite z)) j = p.eval z / q.eval z :=
  ProjectiveLine.rationality
    (projective_ratio_meromorphic e g.finite g.finite_holomorphic i j)
    (rationalCurve_ratio_meromorphicAtInfinity e g i j)

namespace PolynomialTuple


theorem frequently_eval_ne_zero (p : ℂ[X]) (hp : p ≠ 0) (z : ℂ) :
    ∃ᶠ w in nhds z, p.eval w ≠ 0 := by
  by_contra h
  have he : ∀ᶠ w in nhds z, p.eval w = 0 := by simpa only [not_frequently, not_ne_iff] using h
  exact hp (p.eq_zero_of_infinite_isRoot (infinite_of_mem_nhds z he))

 

theorem common_denominator {ι : Type*} [Fintype ι] (f : ι → ℂ → ℂ)
    (hf : ∀ i, ∃ p q : ℂ[X], q ≠ 0 ∧ ∀ z, q.eval z * f i z = p.eval z) :
    ∃ (P : ι → ℂ[X]) (Q : ℂ[X]), Q ≠ 0 ∧ ∀ i z, Q.eval z * f i z = (P i).eval z := by
  classical
  choose p q hq he using hf
  let Q : ℂ[X] := ∏ j, q j
  let P : ι → ℂ[X] := fun i => p i * ∏ j ∈ Finset.univ.erase i, q j
  refine ⟨P,Q,Finset.prod_ne_zero_iff.mpr (fun i _ => hq i),?_⟩
  intro i z
  have hQ : Q = q i * ∏ j ∈ Finset.univ.erase i, q j :=
    (Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i)).symm
  simp only [P,hQ,Polynomial.eval_mul]
  rw [mul_assoc, mul_comm ((∏ j ∈ Finset.univ.erase i, q j).eval z), ← mul_assoc, he]

end PolynomialTuple

 

theorem rationalCurve_polynomial_presentation {X : ComplexManifold.{u}}
    (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ P : Fin (e.N+1) → ℂ[X], Finset.univ.gcd P = 1 ∧
      ∀ (z : ℂ) (k j : Fin (e.N+1)), (e.map (g.finite z)).rep k ≠ 0 →
        (P j).eval z = projectiveCoordinates k (e.map (g.finite z)) j * (P k).eval z := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, (e.map (g.finite 0)).rep i ≠ 0 := by
    by_contra! h
    exact (e.map (g.finite 0)).rep_nonzero (funext h)
  obtain ⟨A,Q,hQ,hA⟩ := PolynomialTuple.common_denominator
    (fun j z => projectiveCoordinates i (e.map (g.finite z)) j)
    (fun j => by
      obtain ⟨p,q,hq,hpq,_⟩ := rationalCurve_ratios_are_rational e g i j
      exact ⟨p,q,hq,hpq⟩)
  have hAi : A i = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply infinite_of_mem_nhds (0 : ℂ)
    filter_upwards [g.finite_holomorphic.continuous.continuousAt.preimage_mem_nhds
      ((e.open_patch i).mem_nhds hi)] with z hz
    rw [← hA i z]
    simp only [projectiveCoordinates, inv_mul_cancel₀ hz, mul_one]
  let D := Finset.univ.gcd A
  have hD : D ≠ 0 := Finset.gcd_ne_zero_iff.mpr ⟨i,Finset.mem_univ i,hAi ▸ hQ⟩
  obtain ⟨P,hAP,hP⟩ := Finset.extract_gcd A (Finset.univ_nonempty)
  have hAP' : ∀ j, A j = D * P j := fun j => hAP j (Finset.mem_univ j)
  refine ⟨P,hP,?_⟩
  intro z k j hk
  have hnear : ∀ᶠ w in nhds z, (e.map (g.finite w)).rep k ≠ 0 :=
    g.finite_holomorphic.continuous.continuousAt.preimage_mem_nhds ((e.open_patch k).mem_nhds hk)
  have hc : ContinuousAt (fun w => projectiveCoordinates k (e.map (g.finite w)) j) z :=
    (continuous_apply j).continuousAt.comp
      (((e.holomorphic k).contMDiffAt ((e.open_patch k).mem_nhds hk)).comp z
        g.finite_holomorphic.contMDiffAt).continuousAt
  apply tendsto_nhds_unique_of_frequently_eq
    (by fun_prop : ContinuousAt (fun w => (P j).eval w) z)
    (hc.mul (by fun_prop : ContinuousAt (fun w => (P k).eval w) z))
  apply ((PolynomialTuple.frequently_eval_ne_zero D hD z).and_eventually hnear).mono
  rintro w ⟨hw,hkw⟩
  have hAw : ∀ l, Q.eval w * projectiveCoordinates i (e.map (g.finite w)) l =
      D.eval w * (P l).eval w := by
    intro l
    rw [hA l w,hAP' l,Polynomial.eval_mul]
  have hiw : (e.map (g.finite w)).rep i ≠ 0 := by
    intro hzero
    obtain ⟨l,hl⟩ := PolynomialTuple.basepoint_free P hP w
    have he := hAw l
    simp only [projectiveCoordinates,hzero,inv_zero,zero_mul,mul_zero] at he
    exact hl ((mul_eq_zero.mp he.symm).resolve_left hw)
  have he : D.eval w * (P j).eval w =
      projectiveCoordinates k (e.map (g.finite w)) j * (D.eval w * (P k).eval w) := by
    rw [← hAw j,← hAw k]
    simp only [projectiveCoordinates]
    field_simp
  change (P j).eval w = projectiveCoordinates k (e.map (g.finite w)) j * (P k).eval w
  exact mul_left_cancel₀ hw (he.trans (by ring))

namespace PolynomialTuple

theorem primitive_of_basepoint_free {ι : Type*} [Fintype ι] (P : ι → ℂ[X])
    (hP : ∀ z : ℂ, ∃ i, (P i).eval z ≠ 0) : Finset.univ.gcd P = 1 := by
  classical
  rw [← Finset.normalize_gcd, normalize_eq_one]
  apply Polynomial.isUnit_iff_degree_eq_zero.mpr
  by_contra h
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_root (Finset.univ.gcd P) h
  obtain ⟨i,hi⟩ := hP z
  exact hi (hz.dvd (Finset.gcd_dvd (Finset.mem_univ i)))

 
theorem reflect_transition (p : ℂ[X]) (d : ℕ) (hp : p.natDegree ≤ d)
    (z : ℂ) (hz : z ≠ 0) : (p.reflect d).eval z⁻¹ * z^d = p.eval z := by
  let := invertibleOfNonzero hz
  simpa only [invOf_eq_inv, Polynomial.eval₂_id] using
    Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) z d p hp

 

theorem exists_primitive_reflection {ι : Type*} [Fintype ι] (P : ι → ℂ[X])
    (hP : Finset.univ.gcd P = 1) :
    ∃ d : ℕ, (∀ i, (P i).natDegree ≤ d) ∧
      Finset.univ.gcd (fun i => (P i).reflect d) = 1 := by
  classical
  let I := Finset.univ.filter (fun i => P i ≠ 0)
  have hI : I.Nonempty := by
    obtain ⟨i,hi⟩ := basepoint_free P hP 0
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,fun h => hi (h ▸ Polynomial.eval_zero)⟩⟩
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image I (fun j => (P j).natDegree) hI
  have hi0 := (Finset.mem_filter.mp hi).2
  have hbound : ∀ j, (P j).natDegree ≤ (P i).natDegree := by
    intro j
    by_cases hj : P j = 0
    · simp only [hj,Polynomial.natDegree_zero,Nat.zero_le]
    · exact hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj⟩)
  refine ⟨(P i).natDegree,hbound,primitive_of_basepoint_free _ ?_⟩
  intro z
  by_cases hz : z = 0
  · refine ⟨i,?_⟩
    simpa only [hz,← Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_reflect,Polynomial.revAt_zero,
      Polynomial.coeff_natDegree] using (Polynomial.leadingCoeff_ne_zero.mpr hi0)
  · obtain ⟨j,hj⟩ := basepoint_free P hP z⁻¹
    refine ⟨j,?_⟩
    intro he
    have ht := reflect_transition (P j) (P i).natDegree (hbound j) z⁻¹ (inv_ne_zero hz)
    rw [inv_inv,he,zero_mul] at ht
    exact hj ht.symm

end PolynomialTuple

 

theorem rationalCurve_two_chart_polynomials {X : ComplexManifold.{u}}
    (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ (d : ℕ) (P Q : Fin (e.N+1) → ℂ[X]),
      Finset.univ.gcd P = 1 ∧ Finset.univ.gcd Q = 1 ∧
      (∀ i, (P i).natDegree ≤ d ∧ Q i = (P i).reflect d) ∧
      (∀ z k j, (e.map (g.finite z)).rep k ≠ 0 →
        (P j).eval z = projectiveCoordinates k (e.map (g.finite z)) j * (P k).eval z) ∧
      (∀ z k j, (e.map (g.infinity z)).rep k ≠ 0 →
        (Q j).eval z = projectiveCoordinates k (e.map (g.infinity z)) j * (Q k).eval z) ∧
      (∀ z, z ≠ 0 → ∀ i, (P i).eval z = z^d * (Q i).eval z⁻¹) := by
  obtain ⟨P,hP,hfinite⟩ := rationalCurve_polynomial_presentation e g
  obtain ⟨d,hd,hQ⟩ := PolynomialTuple.exists_primitive_reflection P hP
  let Q : Fin (e.N+1) → ℂ[X] := fun i => (P i).reflect d
  have htrans : ∀ z, z ≠ 0 → ∀ i, (P i).eval z = z^d * (Q i).eval z⁻¹ := by
    intro z hz i
    exact (PolynomialTuple.reflect_transition (P i) d (hd i) z hz).symm.trans (mul_comm _ _)
  refine ⟨d,P,Q,hP,hQ,fun i => ⟨hd i,rfl⟩,hfinite,?_,htrans⟩
  intro z k j hk
  have hnear : ∀ᶠ w in nhds z, (e.map (g.infinity w)).rep k ≠ 0 :=
    g.infinity_holomorphic.continuous.continuousAt.preimage_mem_nhds ((e.open_patch k).mem_nhds hk)
  have hc : ContinuousAt (fun w => projectiveCoordinates k (e.map (g.infinity w)) j) z :=
    (continuous_apply j).continuousAt.comp
      (((e.holomorphic k).contMDiffAt ((e.open_patch k).mem_nhds hk)).comp z
        g.infinity_holomorphic.contMDiffAt).continuousAt
  apply tendsto_nhds_unique_of_frequently_eq
    (by fun_prop : ContinuousAt (fun w => (Q j).eval w) z)
    (hc.mul (by fun_prop : ContinuousAt (fun w => (Q k).eval w) z))
  have hfreq : ∃ᶠ w in nhds z, w ≠ (0 : ℂ) := by
    simpa only [Polynomial.eval_X] using
      PolynomialTuple.frequently_eval_ne_zero Polynomial.X Polynomial.X_ne_zero z
  apply (hfreq.and_eventually hnear).mono
  rintro w ⟨hw,hkw⟩
  change (Q j).eval w = projectiveCoordinates k (e.map (g.infinity w)) j * (Q k).eval w
  have ho := g.overlap w⁻¹ (inv_ne_zero hw)
  simp only [inv_inv] at ho
  have he := hfinite w⁻¹ k j (ho ▸ hkw)
  rw [ho,htrans w⁻¹ (inv_ne_zero hw) j,htrans w⁻¹ (inv_ne_zero hw) k,inv_inv] at he
  exact mul_left_cancel₀ (pow_ne_zero d (inv_ne_zero hw)) (he.trans (by ring))

end SplitTangent

end CurveImports

namespace SplitTangent
open HolomorphicJets FormalProjective PowerSeries
variable {X : ComplexManifold.{u}}



namespace TangentSplitting
variable (S : TangentSplitting X)



theorem exists_projective_formal_data (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ (d : ℕ) (p q : Fin (e.N+1) → Polynomial ℂ) (a b : Fin (e.N+1) → Polynomial ℂ)
      (F : TwoChartData d p q),
      (∑ i, a i * p i = 1) ∧ (∑ i, b i * q i = 1) ∧
      (∀ k j z, F.finite.ratio k j z =
        S.scalarJet g.finite_holomorphic (fun x => projectiveCoordinates k (e.map x) j) z) ∧
      (∀ k j z, F.infinity.ratio k j z =
        S.scalarJet g.infinity_holomorphic (fun x => projectiveCoordinates k (e.map x) j) z) ∧
      (∀ k z, (p k).eval z ≠ 0 ↔ (e.map (g.finite z)).rep k ≠ 0) := by
  obtain ⟨d,p,q,hp,hq,_,hfinite,hinfinity,htrans⟩ := rationalCurve_two_chart_polynomials e g
  obtain ⟨a,ha⟩ := PolynomialTuple.bezout p hp
  obtain ⟨b,hb⟩ := PolynomialTuple.bezout q hq
  let F₀ := S.projectiveChartData e g.finite_holomorphic p hp hfinite
  let FInfty := S.projectiveChartData e g.infinity_holomorphic q hq hinfinity
  have ho : ∀ k j z, z ≠ 0 → (p k).eval z ≠ 0 →
      F₀.ratio k j z = subst (DiagonalRationality.reciprocalNormal z) (FInfty.ratio k j z⁻¹) := by
    intro k j z hz hk
    have ht := (polynomial_presentation_patch e hp hfinite z k).mp hk
    have he : Set.EqOn g.finite (g.infinity ∘ fun z : ℂ => z⁻¹) {z : ℂ | z ≠ 0} := by
      intro z hz; exact g.overlap z hz
    have hi : AnalyticOnNhd ℂ (fun z : ℂ => z⁻¹) {z : ℂ | z ≠ 0} := by
      intro z hz; exact analyticAt_id.fun_inv hz
    have hs := S.scalarJet_source_glue g.infinity_holomorphic g.finite_holomorphic
      (isOpen_ne_fun continuous_id continuous_const) (fun z : ℂ => z⁻¹) hi he hz
      (fun x => projectiveCoordinates k (e.map x) j)
      ((e.scalar_holomorphic k j).contMDiffAt ((e.open_patch k).mem_nhds ht))
    rw [sourceNormal_inv z hz] at hs
    exact hs.symm
  let F : TwoChartData d p q := ⟨F₀,FInfty,htrans,ho⟩
  exact ⟨d,p,q,a,b,F,ha,hb,fun _ _ _ => rfl,fun _ _ _ => rfl,
    fun k z => polynomial_presentation_patch e hp hfinite z k⟩

end TangentSplitting
end SplitTangent

open Filter Topology

namespace SplitTangent.HolomorphicJets
section
open DiagonalRationality Filter Topology
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem composeJet_analyticJet {G : ℂ → σ → ℂ} {H : (σ → ℂ) → τ → ℂ}
    (hG : AnalyticAt ℂ G 0) (hH : AnalyticAt ℂ H (G 0)) :
    composeJet H (analyticJet G) = analyticJet (H ∘ G) := by
  funext n i
  exact composeCoefficient_analyticJet hG (analyticAt_pi_iff.mp hH i) n

omit [Fintype τ] in
theorem composeJet_germ {H K : (σ → ℂ) → τ → ℂ} (f : ℕ → σ → ℂ)
    (h : H =ᶠ[𝓝 (f 0)] K) : composeJet H f = composeJet K f := by
  funext n i
  simpa only [coeff_formalSubst,composeJet] using
    congrArg (PowerSeries.coeff n) (formalSubst_congr f (h.mono fun x hx => congrFun hx i))

theorem composeJet_assoc {υ : Type*} [Fintype υ]
    (H : (σ → ℂ) → τ → ℂ) (K : (τ → ℂ) → υ → ℂ) (f : ℕ → σ → ℂ)
    (hH : AnalyticAt ℂ H (f 0)) (hK : AnalyticAt ℂ K (H (f 0))) :
    composeJet K (composeJet H f) = composeJet (K ∘ H) f := by
  funext n i
  exact composeCoefficient_assoc H (fun y => K y i) f hH (analyticAt_pi_iff.mp hK i) n

theorem analyticJet_eq_germ {G K : ℂ → σ → ℂ}
    (hG : AnalyticAt ℂ G 0) (hK : AnalyticAt ℂ K 0)
    (h : analyticJet G = analyticJet K) : G =ᶠ[𝓝 0] K := by
  have hp := analyticJet_hasSeries hG
  rw [h] at hp
  filter_upwards [hp.eventually_hasSum_sub,(analyticJet_hasSeries hK).eventually_hasSum_sub]
    with z hz hk
  exact hz.unique hk



end

open DiagonalRationality Filter Topology
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

 

theorem lift_convergent_family {H : (σ → ℂ) → τ → ℂ} (f : ℕ → ℂ → σ → ℂ) {z : ℂ}
    (hH : AnalyticAt ℂ H (f 0 z)) (hi : Function.Injective (fderiv ℂ H (f 0 z)))
    (hf0 : ContinuousAt (f 0) z) {Q : ℂ × ℂ → τ → ℂ}
    (hQ : AnalyticAt ℂ Q (z,0))
    (hj : ∀ᶠ u in 𝓝 z, analyticJet (fun v => Q (u,v)) = composeJet H (fun n => f n u)) :
    ∃ G : ℂ × ℂ → σ → ℂ, AnalyticAt ℂ G (z,0) ∧
      ∀ᶠ u in 𝓝 z, analyticJet (fun v => G (u,v)) = fun n => f n u := by
  obtain ⟨r,hr,_,hri⟩ := AnalyticRetraction.exists_left_inverse hH hi
  have hzero (u : ℂ) (hu : analyticJet (fun v => Q (u,v)) = composeJet H (fun n => f n u)) :
      Q (u,0) = H (f 0 u) := by
    simpa only [analyticJet_zero,composeJet_zero] using congrFun hu 0
  have hrQ : AnalyticAt ℂ r (Q (z,0)) := hzero z hj.self_of_nhds ▸ hr
  have hG : AnalyticAt ℂ (r ∘ Q) (z,0) := hrQ.comp hQ
  refine ⟨r ∘ Q,hG,?_⟩
  have hHnear := hf0 hH.eventually_analyticAt
  have hrnear := (hH.continuousAt.comp hf0) hr.eventually_analyticAt
  have hinear := hf0 (eventually_eventually_nhds.mpr hri)
  have hc : ContinuousAt (fun u : ℂ => (u,(0:ℂ))) z := continuousAt_id.prodMk continuousAt_const
  have hQnear := hc hQ.eventually_analyticAt
  filter_upwards [hj,hHnear,hrnear,hinear,hQnear] with u hju hHu hru hiu hQu
  change AnalyticAt ℂ H (f 0 u) at hHu
  change AnalyticAt ℂ r (H (f 0 u)) at hru
  change (∀ᶠ y in 𝓝 (f 0 u), r (H y) = y) at hiu
  change AnalyticAt ℂ Q (u,0) at hQu
  have hQu' : AnalyticAt ℂ (fun v => Q (u,v)) 0 :=
    hQu.comp (analyticAt_const.prod analyticAt_id)
  have hru' : AnalyticAt ℂ r (Q (u,0)) := hzero u hju ▸ hru
  change analyticJet (r ∘ (fun v => Q (u,v))) = fun n => f n u
  rw [← composeJet_analyticJet hQu' hru',hju,composeJet_assoc H r (fun n => f n u) hHu hru]
  exact (composeJet_germ (fun n => f n u) (H := r ∘ H) (K := id) hiu).trans (composeJet_id _)

end SplitTangent.HolomorphicJets

namespace SplitTangent.HolomorphicJets
open DiagonalRationality Filter Topology PowerSeries
variable {σ : Type*} [Fintype σ]

theorem taylorSeries_eq_germ {h k : ℂ → ℂ} (hh : AnalyticAt ℂ h 0)
    (hk : AnalyticAt ℂ k 0) (he : taylorSeries h = taylorSeries k) : h =ᶠ[𝓝 0] k := by
  have hp := hasFPowerSeries_taylorSeries hh
  rw [he] at hp
  filter_upwards [hp.eventually_hasSum_sub,(hasFPowerSeries_taylorSeries hk).eventually_hasSum_sub]
    with z hz hk
  exact hz.unique hk

 

theorem joint_germ_of_slice_germs {H K : ℂ × ℂ → ℂ} {z : ℂ}
    (hH : AnalyticAt ℂ H (z,0)) (hK : AnalyticAt ℂ K (z,0))
    (h : ∀ᶠ u in 𝓝 z, (fun v => H (u,v)) =ᶠ[𝓝 0] (fun v => K (u,v))) :
    H =ᶠ[𝓝 (z,0)] K := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hH.eventually_analyticAt.and hK.eventually_analyticAt)
  have hf : ∀ᶠ w : ℂ × ℂ in 𝓝 (z,0),
      (fun v => H (w.1,v)) =ᶠ[𝓝 0] (fun v => K (w.1,v)) :=
    (show ContinuousAt (fun w : ℂ × ℂ => w.1) (z,0) from continuousAt_fst) h
  filter_upwards [Metric.ball_mem_nhds (z,0) hr,hf] with w hw hwg
  have hw' : w.1 ∈ Metric.ball z r ∧ w.2 ∈ Metric.ball 0 r := by
    simpa only [← ball_prod_same,Set.mem_prod] using hw
  have hHa : AnalyticOnNhd ℂ (fun v => H (w.1,v)) (Metric.ball 0 r) := by
    intro v hv
    have ha := (hball (show (w.1,v) ∈ Metric.ball (z,0) r by
      rw [← ball_prod_same]; exact ⟨hw'.1,hv⟩)).1
    exact ha.comp (analyticAt_const.prod analyticAt_id)
  have hKa : AnalyticOnNhd ℂ (fun v => K (w.1,v)) (Metric.ball 0 r) := by
    intro v hv
    have ha := (hball (show (w.1,v) ∈ Metric.ball (z,0) r by
      rw [← ball_prod_same]; exact ⟨hw'.1,hv⟩)).2
    exact ha.comp (analyticAt_const.prod analyticAt_id)
  exact hHa.eqOn_of_preconnected_of_eventuallyEq hKa (convex_ball (0:ℂ) r).isPreconnected
    (Metric.mem_ball_self hr) hwg hw'.2

theorem normalVector_analyticJet {G : ℂ × ℂ → σ → ℂ} {u : ℂ}
    (hG : AnalyticAt ℂ G (u,0)) (i : σ) :
    normalVector (analyticJet (fun v => G (u,v))) i =
      taylorSeries (fun v => normalDeriv (fun w => G w i) (u,v)) := by
  have he : deriv (fun v => G (u,v) i) =ᶠ[𝓝 0]
      (fun v => normalDeriv (fun w => G w i) (u,v)) := by
    have hc : ContinuousAt (fun v : ℂ => (u,v)) 0 := continuousAt_const.prodMk continuousAt_id
    filter_upwards [hc hG.eventually_analyticAt] with v hv
    exact normalDeriv_eq (analyticAt_pi_iff.mp hv i)
  have hm : (PowerSeries.mk fun n => coeff n (taylorSeries (fun v => G (u,v) i))) =
      taylorSeries (fun v => G (u,v) i) := by ext n; simp
  simpa only [normalVector,analyticJet,hm] using
    (taylorSeries_deriv (fun v => G (u,v) i)).symm.trans (taylorSeries_congr he)

theorem tangentVector_analyticJet {G : ℂ × ℂ → σ → ℂ} {f : ℕ → ℂ → σ → ℂ}
    {u : ℂ} (hG : AnalyticAt ℂ G (u,0))
    (hf : ∀ᶠ z in 𝓝 u, analyticJet (fun v => G (z,v)) = fun n => f n z) (i : σ) :
    tangentVector f u i = taylorSeries (fun v => tangentDeriv (fun w => G w i) (u,v)) := by
  ext n
  simp only [tangentVector,coeff_mk]
  rw [← deriv_normalCoefficient (analyticAt_pi_iff.mp hG i)]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hf] with z hz
  exact (congrFun (congrFun hz n) i).symm

theorem substitutedMatrix_analyticJet {G : ℂ × ℂ → σ → ℂ} {u : ℂ}
    (hG : AnalyticAt ℂ G (u,0)) (P : σ → σ → (σ → ℂ) → ℂ)
    (hP : ∀ i j, AnalyticAt ℂ (P i j) (G (u,0))) (i j : σ) :
    substitutedMatrix P (analyticJet (fun v => G (u,v))) i j =
      taylorSeries (fun v => P i j (G (u,v))) := by
  ext n
  simp only [substitutedMatrix,coeff_formalSubst]
  have ha : AnalyticAt ℂ (fun v => G (u,v)) 0 :=
    hG.comp (analyticAt_const.prod analyticAt_id)
  exact composeCoefficient_analyticJet (g := fun v => G (u,v)) ha (hP i j) n

 

theorem cauchy_analytic_fiber {U : Set ℂ} {g : ℂ → σ → ℂ}
    {P : σ → σ → (σ → ℂ) → ℂ} {f : ℕ → ℂ → σ → ℂ}
    (hf : CauchyOn U g P f) {u : ℂ} (hu : u ∈ U)
    {G : ℂ × ℂ → σ → ℂ} (hG : AnalyticAt ℂ G (u,0))
    (hP : ∀ i j, AnalyticAt ℂ (P i j) (G (u,0)))
    (hj : ∀ᶠ z in 𝓝 u, analyticJet (fun v => G (z,v)) = fun n => f n z) (i : σ) :
    (fun v => normalDeriv (fun w => G w i) (u,v)) =ᶠ[𝓝 0]
      (fun v => ∑ j, P i j (G (u,v)) * tangentDeriv (fun w => G w j) (u,v)) := by
  have ha : AnalyticAt ℂ (fun v => G (u,v)) 0 :=
    hG.comp (analyticAt_const.prod analyticAt_id)
  have htan (j : σ) : AnalyticAt ℂ (fun v => tangentDeriv (fun w => G w j) (u,v)) 0 :=
    (directionDeriv_analytic (analyticAt_pi_iff.mp hG j) (1,0)).comp
      (analyticAt_const.prod analyticAt_id)
  apply taylorSeries_eq_germ
    ((normalDeriv_analytic (analyticAt_pi_iff.mp hG i)).comp
      (analyticAt_const.prod analyticAt_id))
    (Finset.univ.analyticAt_fun_sum fun j _ => ((hP i j).comp (f := fun v => G (u,v)) ha).fun_mul (htan j))
  have he := congrFun (hf.2.2 u hu) i
  rw [← hj.self_of_nhds,normalVector_analyticJet hG] at he
  refine he.trans ?_
  simp only [Matrix.mulVec,dotProduct]
  rw [taylorSeries_sum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [substitutedMatrix_analyticJet hG P hP,
      tangentVector_analyticJet hG hj]
    exact (taylorSeries_mul (f := fun v => P i j (G (u,v)))
      (g := fun v => tangentDeriv (fun w => G w j) (u,v))
      ((hP i j).comp (f := fun v => G (u,v)) ha) (htan j)).symm
  · intro j _
    exact ((hP i j).comp (f := fun v => G (u,v)) ha).fun_mul (htan j)

 

theorem cauchy_analytic_joint {U : Set ℂ} (hU : IsOpen U) {g : ℂ → σ → ℂ}
    {P : σ → σ → (σ → ℂ) → ℂ} {f : ℕ → ℂ → σ → ℂ}
    (hf : CauchyOn U g P f) {z : ℂ} (hz : z ∈ U)
    {G : ℂ × ℂ → σ → ℂ} (hG : AnalyticAt ℂ G (z,0))
    (hP : ∀ i j, AnalyticAt ℂ (P i j) (G (z,0)))
    (hj : ∀ᶠ u in 𝓝 z, analyticJet (fun v => G (u,v)) = fun n => f n u) :
    ∀ᶠ w in 𝓝 (z,0), ∀ i,
      normalDeriv (fun w => G w i) w =
        ∑ j, P i j (G w) * tangentDeriv (fun w => G w j) w := by
  have hc : ContinuousAt (fun u : ℂ => (u,(0:ℂ))) z :=
    continuousAt_id.prodMk continuousAt_const
  have hGa : ∀ᶠ u in 𝓝 z, AnalyticAt ℂ G (u,0) := hc hG.eventually_analyticAt
  have hPa : ∀ᶠ u in 𝓝 z, ∀ i j, AnalyticAt ℂ (P i j) (G (u,0)) := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    exact (hG.continuousAt.comp (f := fun u : ℂ => (u,(0:ℂ))) hc) (hP i j).eventually_analyticAt
  apply Filter.eventually_all.mpr
  intro i
  apply joint_germ_of_slice_germs
    (normalDeriv_analytic (analyticAt_pi_iff.mp hG i))
    (Finset.univ.analyticAt_fun_sum fun j _ => ((hP i j).comp hG).fun_mul
      (directionDeriv_analytic (analyticAt_pi_iff.mp hG j) (1,0)))
  filter_upwards [hU.mem_nhds hz,hGa,hPa,eventually_eventually_nhds.mpr hj]
    with u hu hGu hPu hju
  exact cauchy_analytic_fiber hf hu hGu hPu hju i

end SplitTangent.HolomorphicJets

namespace SplitTangent.TangentSplitting
open HolomorphicJets DiagonalRationality Filter Topology
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)



theorem cauchy_chart_inverse {x : X.Carrier} {G : ℂ × ℂ → Model X} {w : ℂ × ℂ}
    (hG : AnalyticAt ℂ G w) (ht : G w ∈ (chartAt (Model X) x).target)
    (hde : fderiv ℂ G w (0,1) = S.coordinateProjector x (G w) (fderiv ℂ G w (1,0))) :
    let F := (chartAt (Model X) x).symm ∘ G
    mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (0,1) =
      S.projector (F w) (mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (1,0)) := by
  let c := chartAt (Model X) x
  let t := trivializationAt (Model X) (Tangent X) x
  have hb : c.symm (G w) ∈ t.baseSet := c.map_target ht
  have hci := contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) ht
  have hcD : mfderiv 𝓘(ℂ,Model X) (ModelWithCorners X) c.symm (G w) =
      t.symmL ℂ (c.symm (G w)) := by
    have he := TangentBundle.symmL_trivializationAt (I := ModelWithCorners X) hb
    have he' : t.symmL ℂ (c.symm (G w)) =
        mfderiv 𝓘(ℂ,Model X) (ModelWithCorners X) c.symm (c (c.symm (G w))) := by
      simpa [extChartAt_coe_symm,extChartAt_coe,ModelWithCorners,c,t] using he
    rw [c.right_inv ht] at he'
    exact he'.symm
  change mfderiv _ _ (c.symm ∘ G) w (0,1) =
    S.projector _ (mfderiv _ _ (c.symm ∘ G) w (1,0))
  have hmG : MDifferentiableAt 𝓘(ℂ,ℂ × ℂ) 𝓘(ℂ,Model X) G w :=
    (show ContMDiffAt 𝓘(ℂ,ℂ × ℂ) 𝓘(ℂ,Model X) ω G w from
      hG.contDiffAt.contMDiffAt).mdifferentiableAt (by simp)
  have hmci : MDifferentiableAt 𝓘(ℂ,Model X) (ModelWithCorners X) c.symm (G w) :=
    hci.mdifferentiableAt (by simp)
  have he (v : ℂ × ℂ) : mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) (c.symm ∘ G) w v =
      t.symmL ℂ (c.symm (G w)) (fderiv ℂ G w v) := by
    rw [mfderiv_comp w hmci hmG]
    change mfderiv 𝓘(ℂ,Model X) (ModelWithCorners X) c.symm (G w)
      (mfderiv 𝓘(ℂ,ℂ × ℂ) 𝓘(ℂ,Model X) G w v) = _
    rw [mfderiv_eq_fderiv]
    exact congrArg (fun L => L (fderiv ℂ G w v)) hcD
  rw [he,he]
  rw [hde]
  simp only [coordinateProjector,ContinuousLinearMap.comp_apply]
  rw [t.symmL_continuousLinearMapAt hb]
  rfl



end SplitTangent.TangentSplitting

namespace SplitTangent.HolomorphicJets
open DiagonalRationality Filter Topology
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

 

theorem image_eq_of_jets {H : (σ → ℂ) → τ → ℂ} (f : ℕ → ℂ → σ → ℂ) {z : ℂ}
    (hH : AnalyticAt ℂ H (f 0 z)) (hf0 : ContinuousAt (f 0) z)
    {G : ℂ × ℂ → σ → ℂ} {Q : ℂ × ℂ → τ → ℂ}
    (hG : AnalyticAt ℂ G (z,0)) (hQ : AnalyticAt ℂ Q (z,0))
    (hjG : ∀ᶠ u in 𝓝 z, analyticJet (fun v => G (u,v)) = fun n => f n u)
    (hjQ : ∀ᶠ u in 𝓝 z, analyticJet (fun v => Q (u,v)) = composeJet H (fun n => f n u)) :
    (H ∘ G) =ᶠ[𝓝 (z,0)] Q := by
  have h0 (u : ℂ) (hu : analyticJet (fun v => G (u,v)) = fun n => f n u) :
      G (u,0) = f 0 u := by simpa only [analyticJet_zero] using congrFun hu 0
  have hHG : AnalyticAt ℂ (H ∘ G) (z,0) := (h0 z hjG.self_of_nhds ▸ hH).comp hG
  have hc : ContinuousAt (fun u : ℂ => (u,(0:ℂ))) z := continuousAt_id.prodMk continuousAt_const
  have hs : ∀ᶠ u in 𝓝 z, (fun v => H (G (u,v))) =ᶠ[𝓝 0] (fun v => Q (u,v)) := by
    filter_upwards [hjG,hjQ,hf0 hH.eventually_analyticAt,hc hG.eventually_analyticAt,
      hc hQ.eventually_analyticAt] with u hgu hqu hHu hGu hQu
    have hGu' : AnalyticAt ℂ (fun v => G (u,v)) 0 :=
      hGu.comp (analyticAt_const.prod analyticAt_id)
    have hQu' : AnalyticAt ℂ (fun v => Q (u,v)) 0 :=
      hQu.comp (analyticAt_const.prod analyticAt_id)
    have hHu' : AnalyticAt ℂ H (G (u,0)) := h0 u hgu ▸ hHu
    apply analyticJet_eq_germ (hHu'.comp (f := fun v => G (u,v)) hGu') hQu'
    rw [← composeJet_analyticJet hGu' hHu',hgu,hqu]
  suffices h : ∀ᶠ w in 𝓝 (z,0), ∀ j, H (G w) j = Q w j by
    exact h.mono fun w hw => funext hw
  apply Filter.eventually_all.mpr
  intro j
  have he := joint_germ_of_slice_germs (analyticAt_pi_iff.mp hHG j)
    (analyticAt_pi_iff.mp hQ j) (hs.mono fun u hu => hu.mono fun v hv => congrFun hv j)
  exact he

end SplitTangent.HolomorphicJets

namespace SplitTangent.DiagonalRationality
open Polynomial



theorem normalBiPolynomial_map (m : ℕ) (a : BiCoefficients m) :
    (normalBiPolynomial m a).map polynomialFunction.toRingHom = normalPolynomial m a := by
  apply Polynomial.coe_injective (ℂ → ℂ)
  rw [normalPolynomial_coe,normalPolynomialSection_eq_expand]
  simp only [normalBiPolynomial,Polynomial.map_comp,Polynomial.map_add,Polynomial.map_X,
    Polynomial.map_C,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,polynomialFunction_X,expandPolynomial]

 

theorem exists_bivariate_of_coefficients (A : Polynomial (ℂ → ℂ))
    (hA : ∀ n, ∃ p : Polynomial ℂ, polynomialFunction p = A.coeff n) :
    ∃ P : Polynomial (Polynomial ℂ), P.map polynomialFunction.toRingHom = A := by
  classical
  choose p hp using hA
  refine ⟨∑ n ∈ A.support, Polynomial.monomial n (p n),?_⟩
  simp only [Polynomial.map_sum,Polynomial.map_monomial]
  change ∑ n ∈ A.support, Polynomial.monomial n (polynomialFunction (p n)) = A
  simpa only [hp,Polynomial.sum] using Polynomial.sum_monomial_eq A

 

theorem bivariate_of_normal_division (m : ℕ) (a : BiCoefficients m)
    {r : ℕ} {A : Polynomial (ℂ → ℂ)}
    (hA : normalPolynomial m a = Polynomial.X ^ r * A) :
    ∃ P : Polynomial (Polynomial ℂ), P.map polynomialFunction.toRingHom = A := by
  apply exists_bivariate_of_coefficients
  intro n
  refine ⟨(normalBiPolynomial m a).coeff (n+r),?_⟩
  have he := congrArg (fun p : Polynomial (ℂ → ℂ) => p.coeff (n+r))
    ((normalBiPolynomial_map m a).trans hA)
  simpa only [Polynomial.coeff_map,Polynomial.coeff_X_pow_mul,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using he


end SplitTangent.DiagonalRationality

namespace SplitTangent.FormalProjective
open SplitTangent.DiagonalRationality

 

theorem reconstruct_projective_bivariate {ι : Type*} [Fintype ι] {d : ℕ}
    {p q : ι → Polynomial ℂ} (F : TwoChartData d p q)
    (a b : ι → Polynomial ℂ) (ha : ∑ i, a i * p i = 1) (hb : ∑ i, b i * q i = 1) :
    ∃ (k : ι) (A B : ι → Polynomial (Polynomial ℂ)) (U : Set ℂ),
      IsOpen U ∧ U.Nonempty ∧ ∀ z ∈ U, (p k).eval z ≠ 0 ∧ ∀ j,
        ((B j).coeff 0).eval z ≠ 0 ∧
        AnalyticAt ℂ (fun w => -bivariateEvaluation (A j) w / bivariateEvaluation (B j) w) (z,0) ∧
        HasFPowerSeriesAt
          (fun v => -bivariateEvaluation (A j) (z,v) / bivariateEvaluation (B j) (z,v))
          (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n
            (F.finite.ratio k j z))) 0 := by
  obtain ⟨k,hk⟩ := F.finite.basepoint_free 0
  let s := F.normalizedSection a b ha hb k
  let t := F.normalizedSection a b ha hb
  have hs : ∃ z : ℂ, PowerSeries.constantCoeff s.val.1 z ≠ 0 := by
    exact ⟨0, by simpa only [s,F.normalizedSection_constant a b ha hb k 0] using hk⟩
  obtain ⟨A',B',r,A,B,U,hU,hUn,hpoly,h⟩ := simultaneous_reconstruction_on_diagonal_patch d
    (F.normalizedTransition_constant a b ha hb) s t hs
  choose AA hAA using fun j => bivariate_of_normal_division _ (A' j) (hpoly j).2.1
  choose BB hBB using fun j => bivariate_of_normal_division _ (B' j) (hpoly j).2.2
  refine ⟨k,AA,BB,U,hU,hUn,?_⟩
  intro z hz
  obtain ⟨hsk,hr⟩ := h z hz
  have hp : (p k).eval z ≠ 0 := by
    simpa only [s,F.normalizedSection_constant a b ha hb k z] using hsk
  refine ⟨hp,fun j => ⟨?_,?_,?_⟩⟩
  · simpa only [← hBB j,Polynomial.coeff_map,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
      polynomialFunction_apply] using (hr j).1
  · simpa only [← hAA j,← hBB j,evaluate_polynomial_map] using (hr j).2.1
  · have hq : evaluateCoefficients z (t j).val.1 * (evaluateCoefficients z s.val.1)⁻¹ =
        F.finite.ratio k j z := by
      change evaluateCoefficients z (F.finite.sectionSeries a j) *
        (evaluateCoefficients z (F.finite.sectionSeries a k))⁻¹ = _
      rw [TwoChartData.sectionSeries_evaluate,TwoChartData.sectionSeries_evaluate,
        F.finite.sectionValue_ratio a ha k j z hp]
    simpa only [← hAA j,← hBB j,evaluate_polynomial_map,hq] using (hr j).2.2

end SplitTangent.FormalProjective

namespace SplitTangent.TangentSplitting
section
open HolomorphicJets DiagonalRationality PowerSeries
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem exists_bivariate_cauchy_patch (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ (k : Fin (e.N+1)) (A B : Fin (e.N+1) → Polynomial (Polynomial ℂ)) (U : Set ℂ),
      IsOpen U ∧ U.Nonempty ∧ ∀ z ∈ U, (e.map (g.finite z)).rep k ≠ 0 ∧ ∀ j,
        ((B j).coeff 0).eval z ≠ 0 ∧
        AnalyticAt ℂ (fun w => -bivariateEvaluation (A j) w / bivariateEvaluation (B j) w) (z,0) ∧
        HasFPowerSeriesAt
          (fun v => -bivariateEvaluation (A j) (z,v) / bivariateEvaluation (B j) (z,v))
          (FormalMultilinearSeries.ofScalars ℂ (fun n => coeff n
            (S.scalarJet g.finite_holomorphic (fun x => projectiveCoordinates k (e.map x) j) z))) 0 := by
  obtain ⟨d,p,q,a,b,F,ha,hb,hfinite,_,hpatch⟩ := S.exists_projective_formal_data e g
  obtain ⟨k,A,B,U,hU,hUn,hR⟩ := FormalProjective.reconstruct_projective_bivariate F a b ha hb
  refine ⟨k,A,B,U,hU,hUn,?_⟩
  intro z hz
  obtain ⟨hk,hj⟩ := hR z hz
  refine ⟨(hpatch k z).mp hk,fun j => ⟨(hj j).1,(hj j).2.1,?_⟩⟩
  simpa only [hfinite] using (hj j).2.2

end

open HolomorphicJets DiagonalRationality PowerSeries Filter Topology
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem exists_rational_cauchy_coordinates (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ (z : ℂ) (k : Fin (e.N+1)) (A B : Fin (e.N+1) → Polynomial (Polynomial ℂ))
      (G : ℂ × ℂ → Model X), AnalyticAt ℂ G (z,0) ∧
      (∀ j, ((B j).coeff 0).eval z ≠ 0) ∧
      (e.map (g.finite z)).rep k ≠ 0 ∧
      (∀ᶠ w in nhds (z,0), e.withinChart k (g.finite z) (G w) =
        fun j => -bivariateEvaluation (A j) w / bivariateEvaluation (B j) w) ∧
      ∀ᶠ u in nhds z, analyticJet (fun v => G (u,v)) =
        fun n => S.localJet g.finite_holomorphic (g.finite z) n u := by
  obtain ⟨k,A,B,U,hU,hUn,hR⟩ := S.exists_bivariate_cauchy_patch e g
  obtain ⟨z,hz⟩ := hUn
  let x := g.finite z
  let f := S.localJet g.finite_holomorphic x
  let H := e.withinChart k x
  let Q : ℂ × ℂ → Fin (e.N+1) → ℂ :=
    fun w j => -bivariateEvaluation (A j) w / bivariateEvaluation (B j) w
  have hsol := S.localJet_solution g.finite_holomorphic x
  have hx : z ∈ coordinateDomain g.finite x := mem_chart_source (Model X) x
  have hzero : f 0 z = (chartAt (Model X) x) x := hsol.2.1 z hx
  have hf0 : ContinuousAt (f 0) z :=
    (analyticAt_pi_iff.mpr (fun i => hsol.1 0 i z hx)).continuousAt
  have hH : AnalyticAt ℂ H (f 0 z) := by
    rw [hzero]
    exact e.withinChart_analytic k x hx (hR z hz).1
  have hi : Function.Injective (fderiv ℂ H (f 0 z)) := by
    rw [hzero]
    exact e.withinChart_immersion k x hx (hR z hz).1
  have hQ : AnalyticAt ℂ Q (z,0) := analyticAt_pi_iff.mpr (fun j => ((hR z hz).2 j).2.1)
  have hj : ∀ᶠ u in nhds z,
      analyticJet (fun v => Q (u,v)) = composeJet H (fun n => f n u) := by
    filter_upwards [hU.mem_nhds hz,(coordinateDomain_open g.finite_holomorphic x).mem_nhds hx]
      with u hu hux
    funext n j
    have hp := ((hR u hu).2 j).2.2
    have ht := hasFPowerSeries_taylorSeries hp.analyticAt
    have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n)
      (ht.eq_formalMultilinearSeries hp)
    simp only [FormalMultilinearSeries.coeff_ofScalars] at hc
    change coeff n (taylorSeries (fun v => Q (u,v) j)) = _
    rw [hc,S.scalarJet_eq_local g.finite_holomorphic _ x hux
      ((e.scalar_holomorphic k j).contMDiffAt ((e.open_patch k).mem_nhds (hR u hu).1)),
      coeff_formalSubst]
    rfl
  obtain ⟨G,hG,hjG⟩ := lift_convergent_family f hH hi hf0 hQ hj
  refine ⟨z,k,A,B,G,hG,fun j => ((hR z hz).2 j).1,(hR z hz).1,?_,hjG⟩
  exact image_eq_of_jets f hH hf0 hG hQ hjG hj

end SplitTangent.TangentSplitting

section FiniteBaseImport
open Polynomial
namespace SplitTangent.RationalSurface

attribute [local instance] OAI.SplitTangent.RationalSurface.formalBoxesDecidableEqRatFunc
variable {ι : Type*} [Fintype ι]

 

theorem finite_common_zeros (p : ι → B) {q : R} (hq : q ≠ 0)
    (a : ι → B) (hbez : ∑ i, a i * p i = C q)
    (hvertical : ∀ s : ℂ, ∃ i, (p i).map (Polynomial.evalRingHom s) ≠ 0) :
    Set.Finite {w : ℂ × ℂ | ∀ i, eval (p i) w = 0} := by
  let Z : Set (ℂ × ℂ) := {w | ∀ i, eval (p i) w = 0}
  apply Set.Finite.of_finite_fibers Prod.fst
  · apply (Polynomial.finite_setOfPred_isRoot hq).subset
    rintro s ⟨w,hw,rfl⟩
    have he := congrArg (fun p : B => eval p w) hbez
    simpa only [eval,Polynomial.eval₂_finsetSum,Polynomial.eval₂_mul,
      show ∀ i, (p i).eval₂ (Polynomial.evalRingHom w.1) w.2 = 0 from hw,
      mul_zero,Finset.sum_const_zero,Polynomial.eval₂_C,Polynomial.IsRoot,Polynomial.coe_evalRingHom,Set.mem_ofPred_eq] using he.symm
  · intro s hs
    obtain ⟨i,hi⟩ := hvertical s
    apply ((Set.finite_singleton s).prod (Polynomial.finite_setOfPred_isRoot hi)).subset
    rintro w ⟨hw,hws⟩
    have he : w.1 = s := hws
    refine ⟨he,?_⟩
    change ((p i).map (Polynomial.evalRingHom s)).eval w.2 = 0
    rw [Polynomial.eval_map,← he]
    exact hw i

 
theorem common_denominator (p : ι → Polynomial K) :
    ∃ (q : R) (P : ι → B), q ≠ 0 ∧
      ∀ i, (P i).map (algebraMap R K) = C (algebraMap R K q) * p i := by
  let := Polynomial.algebra (R := R) (A := K)
  let := Polynomial.isLocalization (nonZeroDivisors R) K
  obtain ⟨q,hq⟩ := IsLocalization.exist_integer_multiples_of_finite
    ((nonZeroDivisors R).map (Polynomial.C : R →+* B)) p
  obtain ⟨r,hr,he⟩ := q.property
  have hqr : (q : B) = C r := he.symm
  choose P hP using hq
  refine ⟨r,P,nonZeroDivisors.ne_zero hr,?_⟩
  intro i
  have hh := hP i
  change (P i).map (algebraMap R K) = _ at hh
  rw [hqr] at hh
  rw [Algebra.smul_def] at hh
  change (P i).map (algebraMap R K) = (C r).map (algebraMap R K) * p i at hh
  simpa only [Polynomial.map_C] using hh

 
theorem no_vertical_component (p : ι → B) (hp : Finset.univ.gcd p = 1) (s : ℂ) :
    ∃ i, (p i).map (Polynomial.evalRingHom s) ≠ 0 := by
  by_contra! h
  have hd : C (X - C s : R) ∣ Finset.univ.gcd p := by
    apply Finset.dvd_gcd
    intro i hi
    rw [C_dvd_iff_dvd_coeff]
    intro n
    rw [Polynomial.dvd_iff_isRoot]
    have he := congrArg (fun q : Polynomial ℂ => q.coeff n) (h i)
    simpa [Polynomial.coeff_map,Polynomial.IsRoot] using he
  rw [hp] at hd
  have hu := Polynomial.isUnit_C.mp (isUnit_of_dvd_one hd)
  have hz := hu.map (Polynomial.evalRingHom s)
  simp at hz

 
theorem generic_gcd_eq_one (p : ι → B) (hp : Finset.univ.gcd p = 1) :
    Finset.univ.gcd (fun i => (p i).map (algebraMap R K)) = 1 := by
  classical
  let d := Finset.univ.gcd (fun i => (p i).map (algebraMap R K))
  have hd : d ≠ 0 := by
    intro he
    have hall := Finset.gcd_eq_zero_iff.mp he
    have hz : Finset.univ.gcd p = 0 := Finset.gcd_eq_zero_iff.mpr (by
      intro i hi
      exact (Polynomial.map_eq_zero_iff (IsFractionRing.injective R K)).mp (hall i hi))
    exact one_ne_zero (hp.symm.trans hz)
  let q := IsLocalization.integerNormalization (nonZeroDivisors R) d
  obtain ⟨b,hb,hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) d
  have hbunit : IsUnit (C (algebraMap R K b)) := Polynomial.isUnit_C.mpr
    (isUnit_iff_ne_zero.mpr (fun he => nonZeroDivisors.ne_zero hb ((IsFractionRing.injective R K) (he.trans (map_zero _).symm))))
  have hpd : q.primPart.map (algebraMap R K) ∣ d := by
    have hh := Polynomial.map_dvd (algebraMap R K) q.primPart_dvd
    change _ ∣ q.map (algebraMap R K) at hh
    rw [hq,Algebra.smul_def,Polynomial.algebraMap_apply] at hh
    exact hbunit.dvd_mul_left.mp hh
  have hqall : q.primPart ∣ Finset.univ.gcd p := by
    apply Finset.dvd_gcd
    intro i hi
    apply q.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (K := K)
    exact hpd.trans (Finset.gcd_dvd hi)
  rw [hp] at hqall
  have hdu : IsUnit d := Polynomial.isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart
    hd (isUnit_of_dvd_one hqall)
  simpa only [d,Finset.normalize_gcd] using normalize_eq_one.mpr hdu

 

omit [Fintype ι] in
theorem generic_gcd_mem_span (p : ι → Polynomial K) (s : Finset ι) :
    s.gcd p ∈ Ideal.span (Set.range p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.gcd_insert]
    obtain ⟨a,b,h⟩ := exists_gcd_eq_mul_add_mul (p i) (s.gcd p)
    rw [h]
    exact (Ideal.span (Set.range p)).add_mem
      ((Ideal.span (Set.range p)).mul_mem_right a (Ideal.subset_span ⟨i,rfl⟩))
      ((Ideal.span (Set.range p)).mul_mem_right b ih)

 

theorem vertical_bezout (p : ι → B) (hp : Finset.univ.gcd p = 1) :
    ∃ (q : R) (a : ι → B), q ≠ 0 ∧ ∑ i, a i * p i = C q := by
  have hg := generic_gcd_eq_one p hp
  have hm := generic_gcd_mem_span (fun i => (p i).map (algebraMap R K)) Finset.univ
  rw [hg] at hm
  obtain ⟨b,hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp hm
  obtain ⟨q,a,hq,ha⟩ := common_denominator b
  refine ⟨q,a,hq,?_⟩
  apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
  simp only [Polynomial.map_sum,Polynomial.map_mul,ha,Polynomial.map_C]
  simp only [mul_assoc,← Finset.mul_sum,hb,mul_one]

 

theorem finite_zero_set (p : ι → B) (hp : Finset.univ.gcd p = 1) :
    Set.Finite {w : ℂ × ℂ | ∀ i, eval (p i) w = 0} := by
  obtain ⟨q,a,hq,ha⟩ := vertical_bezout p hp
  exact finite_common_zeros p hq a ha (no_vertical_component p hp)

 
theorem eval_analytic (p : B) (w : ℂ × ℂ) : AnalyticAt ℂ (eval p) w := by
  have ht (n : ℕ) : AnalyticAt ℂ (fun u : ℂ × ℂ => (p.coeff n).eval u.1 * u.2 ^ n) w :=
    (((p.coeff n).differentiable.analyticAt w.1).comp
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt w)).mul
        (((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt w).pow n)
  have he : eval p = ∑ n ∈ p.support, (fun u : ℂ × ℂ => (p.coeff n).eval u.1 * u.2 ^ n) := by
    funext u
    simp [eval,Polynomial.eval₂_eq_sum,Polynomial.sum_def]
  rw [he]
  exact Finset.analyticAt_sum p.support (fun n _ => ht n)

 
theorem polynomial_ratio_tuple (A D : ι → B) :
    ∃ p : ι → B, ∀ (w : ℂ × ℂ), (∀ i, eval (D i) w ≠ 0) →
      ∀ j, eval (p j) w = (∏ i, eval (D i) w) * (-eval (A j) w / eval (D j) w) := by
  classical
  refine ⟨fun j => - A j * ∏ i ∈ Finset.univ.erase j, D i,?_⟩
  intro w hw j
  have hp : eval (D j) w * ∏ i ∈ Finset.univ.erase j, eval (D i) w =
      ∏ i, eval (D i) w := Finset.mul_prod_erase Finset.univ (fun i => eval (D i) w) (Finset.mem_univ j)
  simp only [eval,Polynomial.eval₂_mul,Polynomial.eval₂_neg,Polynomial.eval₂_finsetProd]
  change -eval (A j) w * (∏ i ∈ Finset.univ.erase j, eval (D i) w) =
    (∏ i, eval (D i) w) * (-eval (A j) w / eval (D j) w)
  rw [← hp]
  field_simp [hw j]

 

theorem primitive_ratio_tuple [Nonempty ι] (A D : ι → B) (k : ι) :
    ∃ (P : ι → B), Finset.univ.gcd P = 1 ∧
      Set.Finite {w : ℂ × ℂ | ∀ j, eval (P j) w = 0} ∧
      ∀ w, (∀ i, eval (D i) w ≠ 0) → -eval (A k) w / eval (D k) w = 1 →
        eval (P k) w ≠ 0 ∧ ∀ j, eval (P j) w / eval (P k) w =
          -eval (A j) w / eval (D j) w := by
  classical
  obtain ⟨p,hp⟩ := polynomial_ratio_tuple A D
  obtain ⟨P,hP,hg⟩ := Finset.extract_gcd p Finset.univ_nonempty
  let q := Finset.univ.gcd p
  have he (j : ι) (w : ℂ × ℂ) : eval (p j) w = eval q w * eval (P j) w := by
    rw [hP j (Finset.mem_univ j)]
    exact Polynomial.eval₂_mul _ _
  refine ⟨P,hg,finite_zero_set P hg,?_⟩
  intro w hw hk
  have hpk : eval (p k) w ≠ 0 := by
    rw [hp w hw k,hk,mul_one]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hw i)
  have hq : eval q w ≠ 0 := by
    intro hz
    exact hpk (by rw [he k w,hz,zero_mul])
  have hPk : eval (P k) w ≠ 0 := by
    intro hz
    exact hpk (by rw [he k w,hz,mul_zero])
  refine ⟨hPk,fun j => ?_⟩
  apply (div_eq_iff hPk).mpr
  apply mul_left_cancel₀ hq
  rw [← he j w,hp w hw j]
  have hh := he k w
  rw [hp w hw k,hk,mul_one] at hh
  rw [hh]
  ring

end SplitTangent.RationalSurface

end FiniteBaseImport
namespace SplitTangent.TangentSplitting
open HolomorphicJets DiagonalRationality Filter Topology
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem exists_rational_tangent_germ (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ (z : ℂ) (k : Fin (e.N+1)) (P : Fin (e.N+1) → Polynomial (Polynomial ℂ))
      (F : ℂ × ℂ → X.Carrier),
      Finset.univ.gcd P = 1 ∧
      Set.Finite {w : ℂ × ℂ | ∀ j, RationalSurface.eval (P j) w = 0} ∧
      ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F (z,0) ∧
      (∀ᶠ u in 𝓝 z, F (u,0) = g.finite u) ∧
      (∀ᶠ w in 𝓝 (z,0), RationalSurface.eval (P k) w ≠ 0 ∧
        (e.map (F w)).rep k ≠ 0 ∧ ∀ j,
          RationalSurface.eval (P j) w / RationalSurface.eval (P k) w =
            projectiveCoordinates k (e.map (F w)) j) ∧
      ∀ᶠ w in 𝓝 (z,0),
        mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (0,1) =
          S.projector (F w) (mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (1,0)) := by
  obtain ⟨z,k,A,B,G,hG,hB,hk,hQ,hj⟩ := S.exists_rational_cauchy_coordinates e g
  let x := g.finite z
  let c := chartAt (Model X) x
  have hx : z ∈ coordinateDomain g.finite x := mem_chart_source (Model X) x
  have hU := coordinateDomain_open g.finite_holomorphic x
  have hf := S.localJet_solution g.finite_holomorphic x
  have h0 : ∀ᶠ u in 𝓝 z, G (u,0) = c (g.finite u) := by
    filter_upwards [hj,hU.mem_nhds hx] with u hju hu
    have he := congrFun hju 0
    rw [analyticJet_zero] at he
    exact he.trans (hf.2.1 u hu)
  have ht : G (z,0) ∈ c.target := h0.self_of_nhds ▸ c.map_source hx
  have hM : ∀ i j, AnalyticAt ℂ (S.coordinateMatrix x i j) (G (z,0)) :=
    fun i j => S.coordinateMatrix_analytic x i j _ ht
  have hde := cauchy_analytic_joint hU hf hx hG hM hj
  have hde' : ∀ᶠ w in 𝓝 (z,0), G w ∈ c.target ∧
      fderiv ℂ G w (0,1) = S.coordinateProjector x (G w) (fderiv ℂ G w (1,0)) := by
    filter_upwards [hde,hG.eventually_analyticAt,hG.continuousAt (c.open_target.mem_nhds ht)]
      with w hw hGw htw
    refine ⟨htw,?_⟩
    rw [← S.coordinateMatrix_mulVec]
    funext i
    simpa only [normalDeriv,tangentDeriv,directionDeriv,fderiv_apply hGw.differentiableAt,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,Matrix.mulVec,dotProduct]
      using hw i
  let F := c.symm ∘ G
  have hF : ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F (z,0) :=
    (contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) ht).comp _
        hG.contDiffAt.contMDiffAt
  have hFg : ∀ᶠ u in 𝓝 z, F (u,0) = g.finite u := by
    filter_upwards [h0,hU.mem_nhds hx] with u hu hux
    change c.symm (G (u,0)) = _
    rw [hu,c.left_inv hux]
  have hFk : ∀ᶠ w in 𝓝 (z,0), (e.map (F w)).rep k ≠ 0 := by
    have hk' : (e.map (F (z,0))).rep k ≠ 0 := by rw [hFg.self_of_nhds]; exact hk
    exact hF.continuousAt ((e.open_patch k).mem_nhds hk')
  have hBn : ∀ᶠ w in 𝓝 (z,0), ∀ j, RationalSurface.eval (B j) w ≠ 0 := by
    rw [Filter.eventually_all]
    intro j
    apply (RationalSurface.eval_analytic (B j) (z,0)).continuousAt.eventually_ne
    simpa only [RationalSurface.eval,Polynomial.eval₂_at_zero,Polynomial.coe_evalRingHom] using hB j
  obtain ⟨P,hP,hfinite,hPr⟩ := RationalSurface.primitive_ratio_tuple A B k
  refine ⟨z,k,P,F,hP,hfinite,hF,hFg,?_,?_⟩
  · filter_upwards [hQ,hFk,hBn] with w hw hkw hBw
    have he (j) : projectiveCoordinates k (e.map (F w)) j =
        -RationalSurface.eval (A j) w / RationalSurface.eval (B j) w := congrFun hw j
    have he1 : -RationalSurface.eval (A k) w / RationalSurface.eval (B k) w = 1 := by
      rw [← he k]
      exact inv_mul_cancel₀ hkw
    obtain ⟨hPk,hPj⟩ := hPr w hBw he1
    exact ⟨hPk,hkw,fun j => (hPj j).trans (he j).symm⟩
  · filter_upwards [hde',hG.eventually_analyticAt] with w hw hGw
    exact S.cauchy_chart_inverse hGw hw.1 hw.2

end SplitTangent.TangentSplitting

open Filter Topology

namespace SplitTangent.ProjectiveEmbedding
section
variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)



theorem isClosed_cone [CompactSpace X.Carrier] :
    IsClosed {v : Fin (e.N+1) → ℂ | ∃ x, e.Incidence x v} := by
  have h := isClosedMap_snd_of_compactSpace _ e.isClosed_incidence
  convert h using 1
  ext v
  simp only [mem_image,mem_ofPred_eq,Prod.exists]
  aesop



theorem cone_local_equations [CompactSpace X.Carrier] {v : Fin (e.N+1) → ℂ}
    (hv : v ≠ 0) (hvX : ∃ x, e.Incidence x v) :
    ∃ D : (Fin (e.N+1) → ℂ) → (Fin (e.N+1) → ℂ), AnalyticAt ℂ D v ∧
      ∀ᶠ w in 𝓝 v, (∃ x, e.Incidence x w) ↔ D w = 0 := by
  obtain ⟨x,hx⟩ := hvX
  obtain ⟨i,hi⟩ := Function.ne_iff.mp (e.map x).rep_nonzero
  change (e.map x).rep i ≠ 0 at hi
  have hvi : v i ≠ 0 := by
    intro hz
    apply hv
    ext j
    rw [(e.incidence_iff_coordinates hi).mp hx j,hz,zero_mul]
    rfl
  let c := chartAt (Model X) x
  let H := e.withinChart i x
  let n := e.normalize i
  have hcx : x ∈ c.source := mem_chart_source (Model X) x
  have hn : n v = H (c x) := by
    rw [e.incidence_iff_normalize hi hvi] at hx
    simpa [H,withinChart,c] using hx
  have hH : AnalyticAt ℂ H (c x) := e.withinChart_analytic i x hcx hi
  obtain ⟨r,hr,hr0,hri⟩ := AnalyticRetraction.exists_left_inverse hH
    (e.withinChart_immersion i x hcx hi)
  have hrn : AnalyticAt ℂ (r ∘ n) v := (hn ▸ hr).comp (e.normalize_analytic hvi)
  have hrn0 : r (n v) = c x := hn ▸ hr0
  have heq : ∀ᶠ y in 𝓝 x, y ∈ c.source ∧ (e.map y).rep i ≠ 0 ∧
      r (projectiveCoordinates i (e.map y)) = c y := by
    have hri' := (c.continuousAt hcx).eventually hri
    filter_upwards [c.open_source.mem_nhds hcx,(e.open_patch i).mem_nhds hi,hri'] with y hy hiy hry
    refine ⟨hy,hiy,?_⟩
    change r (projectiveCoordinates i (e.map (c.symm (c y)))) = c y at hry
    rwa [c.left_inv hy] at hry
  obtain ⟨U,hUsub,hU,hxU⟩ := mem_nhds_iff.mp heq
  have hloc := e.incidence_localizes hv hx hU hxU
  have hH' : AnalyticAt ℂ H ((r ∘ n) v) := by simpa only [Function.comp_apply,hrn0] using hH
  have hR : AnalyticAt ℂ (fun w => H (r (n w))) v := hH'.comp hrn
  let D := fun w => H (r (n w)) - n w
  refine ⟨D,hR.sub (e.normalize_analytic hvi),?_⟩
  have hc : ContinuousAt (fun w => c.symm (r (n w))) v := by
    apply (c.continuousAt_symm (c.map_source hcx)).comp_of_eq hrn.continuousAt
    exact hrn0
  have hx0 : c.symm (r (n v)) = x := by rw [hrn0,c.left_inv hcx]
  have hp : ∀ᶠ w in 𝓝 v, (e.map (c.symm (r (n w)))).rep i ≠ 0 :=
    hc.eventually (hx0 ▸ (e.open_patch i).mem_nhds hi)
  have hni : ∀ᶠ w in 𝓝 v, w i ≠ 0 := (continuous_apply i).continuousAt.eventually_ne hvi
  filter_upwards [hloc,hp,hni] with w hw hpw hiw
  change (∃ y, e.Incidence y w) ↔ H (r (n w)) - n w = 0
  rw [sub_eq_zero]
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨hcy,hiy,hry⟩ := hUsub (hw y hy)
    have hnw : n w = projectiveCoordinates i (e.map y) :=
      (e.incidence_iff_normalize hiy hiw).mp hy
    rw [hnw,hry]
    exact congrArg (projectiveCoordinates i ∘ e.map) (c.left_inv hcy)
  · intro h
    refine ⟨c.symm (r (n w)),(e.incidence_iff_normalize hpw hiw).mpr ?_⟩
    exact h.symm

theorem cone_local_equations_any [CompactSpace X.Carrier] {v : Fin (e.N+1) → ℂ}
    (hv : v ≠ 0) :
    ∃ D : (Fin (e.N+1) → ℂ) → (Fin (e.N+1) → ℂ), AnalyticAt ℂ D v ∧
      ∀ᶠ w in 𝓝 v, (∃ x, e.Incidence x w) ↔ D w = 0 := by
  by_cases h : ∃ x, e.Incidence x v
  · exact e.cone_local_equations hv h
  · refine ⟨fun _ => 1,analyticAt_const,?_⟩
    filter_upwards [e.isClosed_cone.isOpen_compl.mem_nhds h] with w hw
    constructor
    · exact fun hh => False.elim (hw hh)
    · intro hh
      exact False.elim (one_ne_zero (congrFun hh 0 : (1 : ℂ) = 0))

end

variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 

theorem cone_continuation [CompactSpace X.Carrier] {Q : E → Fin (e.N+1) → ℂ}
    {U : Set E} (hU : IsPreconnected U) (hQ : AnalyticOnNhd ℂ Q U)
    (hnz : ∀ z ∈ U, Q z ≠ 0)
    (hstart : (U ∩ interior {z | ∃ x, e.Incidence x (Q z)}).Nonempty) :
    ∀ z ∈ U, ∃ x, e.Incidence x (Q z) := by
  apply AnalyticContinuation.subset_of_local_analytic_equations (F := Fin (e.N+1) → ℂ) hU _ hstart
  intro z hz
  obtain ⟨D,hD,he⟩ := e.cone_local_equations_any (hnz z hz)
  exact ⟨D ∘ Q,hD.comp (hQ z hz),(hQ z hz).continuousAt.eventually he⟩



theorem exists_global_regular_lift [CompactSpace X.Carrier]
    (Q : ℂ × ℂ → Fin (e.N+1) → ℂ) (hQ : AnalyticOnNhd ℂ Q univ)
    (hB : Set.Finite {z | Q z = 0})
    (F₀ : ℂ × ℂ → X.Carrier) (a : ℂ × ℂ)
    (hstart : ∀ᶠ z in 𝓝 a, Q z ≠ 0 ∧ e.Incidence (F₀ z) (Q z)) :
    ∃ F : ℂ × ℂ → X.Carrier,
      ContMDiffOn 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F {z | Q z ≠ 0} ∧
      (∀ z, Q z ≠ 0 → e.Incidence (F z) (Q z)) ∧ F =ᶠ[𝓝 a] F₀ := by
  let U := {z | Q z ≠ 0}
  have hrank : 1 < Module.rank ℝ (ℂ × ℂ) := by
    rw [rank_prod',Complex.rank_real_complex]
    norm_num
  have hUconn : IsPreconnected U :=
    (hB.countable.isPathConnected_compl_of_one_lt_rank hrank).isConnected.isPreconnected
  have hUopen : IsOpen U := hB.isClosed.isOpen_compl
  have hne : (U ∩ interior {z | ∃ x, e.Incidence x (Q z)}).Nonempty := by
    refine ⟨a,hstart.self_of_nhds.1,mem_interior_iff_mem_nhds.mpr ?_⟩
    filter_upwards [hstart] with z hz
    exact ⟨F₀ z,hz.2⟩
  have hcone : ∀ z ∈ U, ∃ x, e.Incidence x (Q z) :=
    e.cone_continuation hUconn (hQ.mono (subset_univ U)) (fun _ hz => hz) hne
  let F := fun z => if hz : z ∈ U then (hcone z hz).choose else F₀ a
  have hF (z : ℂ × ℂ) (hz : z ∈ U) : e.Incidence (F z) (Q z) := by
    dsimp only [F]
    rw [dite_eq_left hz]
    exact (hcone z hz).choose_spec
  refine ⟨F,?_,hF,?_⟩
  · intro z hz
    apply ContMDiffAt.contMDiffWithinAt
    apply e.holomorphic_of_incidence (hQ z (mem_univ z)) hz
    filter_upwards [hUopen.mem_nhds hz] with w hw
    exact hF w hw
  · filter_upwards [hstart] with z hz
    exact e.incidence_unique hz.1 (hF z hz.1) hz.2

end SplitTangent.ProjectiveEmbedding

namespace SplitTangent.TangentSplitting
section
open Filter Topology
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 

theorem chart_derivative {F : E → X.Carrier} {z : E} {x : X.Carrier}
    (hF : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z)
    (hx : F z ∈ (chartAt (Model X) x).source) :
    fderiv ℂ ((chartAt (Model X) x) ∘ F) z =
      ((trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (F z)).comp
        (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z) := by
  have hc := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hx
  have ht : (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (F z) =
      mfderiv (ModelWithCorners X) 𝓘(ℂ,Model X) (chartAt (Model X) x) (F z) :=
    TangentBundle.continuousLinearMapAt_trivializationAt (I := ModelWithCorners X) hx
  rw [ht]
  exact mfderiv_eq_fderiv.symm.trans (mfderiv_comp z
    (hc.mdifferentiableAt (by simp)) (hF.mdifferentiableAt (by simp)))

theorem chart_pde_iff {F : E → X.Carrier} {z : E} {x : X.Carrier} (a b : E)
    (hF : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z)
    (hx : F z ∈ (chartAt (Model X) x).source) :
    (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z b =
        S.projector (F z) (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z a)) ↔
      fderiv ℂ ((chartAt (Model X) x) ∘ F) z b =
        S.coordinateProjector x ((chartAt (Model X) x) (F z))
          (fderiv ℂ ((chartAt (Model X) x) ∘ F) z a) := by
  let t := trivializationAt (Model X) (Tangent X) x
  have ht : F z ∈ t.baseSet := hx
  have hd (v : E) : fderiv ℂ ((chartAt (Model X) x) ∘ F) z v =
      t.continuousLinearMapAt ℂ (F z) (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z v) :=
    congrArg (fun L : E →L[ℂ] Model X => L v) (chart_derivative hF hx)
  rw [hd a,hd b]
  change _ ↔ t.continuousLinearMapAt ℂ (F z) _ =
    t.continuousLinearMapAt ℂ ((chartAt (Model X) x).symm ((chartAt (Model X) x) (F z)))
      (S.projector _ (t.symmL ℂ _ (t.continuousLinearMapAt ℂ (F z) _)))
  rw [(chartAt (Model X) x).left_inv hx,t.symmL_continuousLinearMapAt ht]
  constructor
  · intro h
    exact congrArg (t.continuousLinearMapAt ℂ (F z)) h
  · intro h
    have hh := congrArg (t.symmL ℂ (F z)) h
    simpa only [t.symmL_continuousLinearMapAt ht] using hh

 
theorem pde_local_equations {F : E → X.Carrier} {z : E} (a b : E)
    (hF : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z) :
    ∃ f : E → Model X, AnalyticAt ℂ f z ∧ ∀ᶠ w in 𝓝 z,
      (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F w b =
        S.projector (F w) (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F w a)) ↔ f w = 0 := by
  let x := F z
  let c := chartAt (Model X) x
  let G := c ∘ F
  have hx : F z ∈ c.source := mem_chart_source (Model X) x
  have hc := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hx
  have hG : AnalyticAt ℂ G z := (hc.comp z hF).contDiffAt.analyticAt
  let f := fun w => fderiv ℂ G w b - S.coordinateProjector x (G w) (fderiv ℂ G w a)
  refine ⟨f,?_,?_⟩
  · have hd (v : E) : AnalyticAt ℂ (fun w => fderiv ℂ G w v) z :=
      (ContinuousLinearMap.apply ℂ (Model X) v).analyticAt _ |>.comp hG.fderiv
    apply (hd b).sub
    rw [← funext fun w => S.coordinateMatrix_mulVec x (G w) (fderiv ℂ G w a)]
    apply analyticAt_pi_iff.mpr
    intro i
    change AnalyticAt ℂ (fun w => ∑ j, S.coordinateMatrix x i j (G w) *
      (fderiv ℂ G w a) j) z
    apply Finset.analyticAt_fun_sum
    intro j _
    exact ((S.coordinateMatrix_analytic x i j (G z) (c.map_source hx)).comp (f := G) (x := z) hG).mul
      (analyticAt_pi_iff.mp (hd a) j)
  · have hFnear := (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hF
    have hxnear := hF.continuousAt.eventually (c.open_source.mem_nhds hx)
    filter_upwards [hFnear,hxnear] with w hw hxw
    exact (S.chart_pde_iff a b hw hxw).trans sub_eq_zero.symm

 

theorem pde_continuation {F : E → X.Carrier} {U : Set E} (a b : E)
    (hU : IsPreconnected U) (hF : ∀ z ∈ U, ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z)
    (hstart : (U ∩ interior {z | mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z b =
        S.projector (F z) (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z a)}).Nonempty) :
    ∀ z ∈ U, mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z b =
      S.projector (F z) (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z a) := by
  apply AnalyticContinuation.subset_of_local_analytic_equations (F := Model X) hU _ hstart
  exact fun z hz => S.pde_local_equations a b (hF z hz)

end

section
open Filter Topology
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem exists_global_regular_tangent_box [CompactSpace X.Carrier]
    (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ (z : ℂ) (P : Fin (e.N+1) → Polynomial (Polynomial ℂ))
      (F : ℂ × ℂ → X.Carrier),
      Finset.univ.gcd P = 1 ∧
      Set.Finite {w : ℂ × ℂ | ∀ j, RationalSurface.eval (P j) w = 0} ∧
      (∃ j, RationalSurface.eval (P j) (z,0) ≠ 0) ∧
      (∀ᶠ u in 𝓝 z, F (u,0) = g.finite u) ∧
      (∀ w, (∃ j, RationalSurface.eval (P j) w ≠ 0) →
        ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F w ∧
        e.Incidence (F w) (fun j => RationalSurface.eval (P j) w) ∧
        mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (0,1) =
          S.projector (F w) (mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (1,0))) := by
  obtain ⟨z,k,P,F₀,hP,hB,hF₀,hdiag,hrep,hpde⟩ := S.exists_rational_tangent_germ e g
  let Q := fun w : ℂ × ℂ => fun j => RationalSurface.eval (P j) w
  have hQ : AnalyticOnNhd ℂ Q univ := fun w _ =>
    analyticAt_pi_iff.mpr (fun j => RationalSurface.eval_analytic (P j) w)
  have hQzero (w) : Q w = 0 ↔ ∀ j, RationalSurface.eval (P j) w = 0 :=
    funext_iff
  have hfinite : Set.Finite {w | Q w = 0} := by
    simpa only [hQzero] using hB
  have hstart : ∀ᶠ w in 𝓝 (z,0), Q w ≠ 0 ∧ e.Incidence (F₀ w) (Q w) := by
    filter_upwards [hrep] with w hw
    refine ⟨fun hz => hw.1 (congrFun hz k), (e.incidence_iff_coordinates hw.2.1).mpr ?_⟩
    intro j
    have hh := (div_eq_iff hw.1).mp (hw.2.2 j)
    exact hh.trans (mul_comm _ _)
  obtain ⟨F,hF,hinc,hagree⟩ := e.exists_global_regular_lift Q hQ hfinite F₀ (z,0) hstart
  let U := {w | Q w ≠ 0}
  have hUopen : IsOpen U := hfinite.isClosed.isOpen_compl
  have hFA (w) (hw : w ∈ U) : ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F w :=
    (hF w hw).contMDiffAt (hUopen.mem_nhds hw)
  have hrank : 1 < Module.rank ℝ (ℂ × ℂ) := by
    rw [rank_prod',Complex.rank_real_complex]
    norm_num
  have hUconn : IsPreconnected U :=
    (hfinite.countable.isPathConnected_compl_of_one_lt_rank hrank).isConnected.isPreconnected
  have hPDEnear : ∀ᶠ w in 𝓝 (z,0),
      mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (0,1) =
        S.projector (F w) (mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (1,0)) := by
    filter_upwards [hpde,hagree.eventuallyEq_nhds] with w hw he
    rw [he.mfderiv_eq,he.self_of_nhds]
    exact hw
  have hglobal := S.pde_continuation (F := F) (U := U) (1,0) (0,1) hUconn hFA
    ⟨(z,0),hstart.self_of_nhds.1,mem_interior_iff_mem_nhds.mpr hPDEnear⟩
  refine ⟨z,P,F,hP,hB,⟨k,hrep.self_of_nhds.1⟩,?_,?_⟩
  · have hline : Tendsto (fun u : ℂ => (u,(0 : ℂ))) (𝓝 z) (𝓝 (z,(0 : ℂ))) :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [hdiag,hline.eventually hagree] with u hu he
    exact he.trans hu
  · intro w hw
    have hwU : w ∈ U := by
      obtain ⟨j,hj⟩ := hw
      exact fun he => hj (congrFun he j)
    exact ⟨hFA w hwU,hinc w hwU,hglobal w hwU⟩

end

open Filter Topology
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']


lemma projectedInChart_eq {F : E → X.Carrier} {z : E} {x : X.Carrier} (v : E)
    (hF : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z)
    (hx : F z ∈ (chartAt (Model X) x).source) :
    S.projectedInChart x F v z =
      (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (F z)
        (S.projector (F z) (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z v)) := by
  let t := trivializationAt (Model X) (Tangent X) x
  have ht : F z ∈ t.baseSet := hx
  have hd : fderiv ℂ ((chartAt (Model X) x) ∘ F) z v =
      t.continuousLinearMapAt ℂ (F z) (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z v) :=
    congrArg (fun L : E →L[ℂ] Model X => L v) (chart_derivative hF hx)
  simp only [projectedInChart,hd,coordinateProjector,ContinuousLinearMap.comp_apply]
  rw [(chartAt (Model X) x).left_inv hx,t.symmL_continuousLinearMapAt ht]

lemma projectedInChart_analytic {F : E → X.Carrier} {z : E} {x : X.Carrier} (v : E)
    (hF : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z)
    (hx : F z ∈ (chartAt (Model X) x).source) :
    AnalyticAt ℂ (S.projectedInChart x F v) z := by
  let c := chartAt (Model X) x
  let G := c ∘ F
  have hc := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hx
  have hG : AnalyticAt ℂ G z := (hc.comp z hF).contDiffAt.analyticAt
  have hd : AnalyticAt ℂ (fun w => fderiv ℂ G w v) z :=
    (ContinuousLinearMap.apply ℂ (Model X) v).analyticAt _ |>.comp hG.fderiv
  change AnalyticAt ℂ (fun w => S.coordinateProjector x (G w) (fderiv ℂ G w v)) z
  rw [← funext fun w => S.coordinateMatrix_mulVec x (G w) (fderiv ℂ G w v)]
  apply analyticAt_pi_iff.mpr
  intro i
  change AnalyticAt ℂ (fun w => ∑ j, S.coordinateMatrix x i j (G w) * (fderiv ℂ G w v) j) z
  apply Finset.analyticAt_fun_sum
  intro j _
  exact ((S.coordinateMatrix_analytic x i j (G z) (c.map_source hx)).comp hG).mul
    (analyticAt_pi_iff.mp hd j)

lemma chart_wedge_iff {F : E → X.Carrier} {A : E → ℂ} {z : E} {x : X.Carrier}
    (hF : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z)
    (hx : F z ∈ (chartAt (Model X) x).source) :
    S.WedgeAt F A z ↔ ∀ v w : E,
      fderiv ℂ A z v • S.projectedInChart x F w z =
        fderiv ℂ A z w • S.projectedInChart x F v z := by
  let t := trivializationAt (Model X) (Tangent X) x
  have ht : F z ∈ t.baseSet := hx
  simp only [WedgeAt,projectedInChart_eq S _ hF hx,← map_smul]
  constructor
  · intro h v w
    exact congrArg (t.continuousLinearMapAt ℂ (F z)) (h v w)
  · intro h v w
    have H := congrArg (t.symmL ℂ (F z)) (h v w)
    dsimp only [t] at H ⊢
    simpa only [Bundle.Trivialization.symmL_continuousLinearMapAt (trivializationAt (Model X) (Tangent X) x) ht] using H

 
theorem WedgeAt.comp {F : E → X.Carrier} {A : E → ℂ} {f : E' → E} {z : E'}
    (hW : S.WedgeAt F A (f z))
    (hF : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F (f z))
    (hA : DifferentiableAt ℂ A (f z)) (hf : DifferentiableAt ℂ f z) :
    S.WedgeAt (F ∘ f) (A ∘ f) z := by
  intro v w
  rw [fderiv_comp z hA hf,mfderiv_comp z (hF.mdifferentiableAt (by simp)) hf.mdifferentiableAt,
    mfderiv_eq_fderiv]
  exact hW (fderiv ℂ f z v) (fderiv ℂ f z w)

 

theorem wedgeAt_of_frequently {F : E → X.Carrier} {A : E → ℂ} {z : E}
    (hF : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z)
    (hA : AnalyticAt ℂ A z) (hW : ∃ᶠ w in 𝓝 z, S.WedgeAt F A w) :
    S.WedgeAt F A z := by
  let x := F z
  let c := chartAt (Model X) x
  have hx : F z ∈ c.source := mem_chart_source (Model X) x
  have hnear := (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hF
  have hxnear := hF.continuousAt.eventually (c.open_source.mem_nhds hx)
  apply (S.chart_wedge_iff hF hx).mpr
  intro v w
  have hd (v : E) : ContinuousAt (fun q => fderiv ℂ A q v) z :=
    hA.fderiv.continuousAt.clm_apply continuousAt_const
  have hl := (hd v).smul (S.projectedInChart_analytic w hF hx).continuousAt
  have hr := (hd w).smul (S.projectedInChart_analytic v hF hx).continuousAt
  apply tendsto_nhds_unique_of_frequently_eq hl hr
  exact (hW.and_eventually (hnear.and hxnear)).mono (fun q hq =>
    (S.chart_wedge_iff hq.2.1 hq.2.2).mp hq.1 v w)

end SplitTangent.TangentSplitting

namespace SplitTangent.ExceptionalTangency
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 
theorem factor_fderiv (n : ℕ) {h : ℂ × ℂ → ℂ} {w : ℂ × ℂ}
    (hh : DifferentiableAt ℂ h w) (v : ℂ × ℂ) :
    fderiv ℂ (fun w : ℂ × ℂ => w.1 ^ (n+1) * h w) w v =
      w.1 ^ n * (((n+1 : ℕ) : ℂ) * h w * v.1 + w.1 * fderiv ℂ h w v) := by
  have H := ((hasFDerivAt_fst (𝕜 := ℂ) (p := w)).pow (n+1)).mul hh.hasFDerivAt
  change fderiv ℂ ((fun w : ℂ × ℂ => w.1 ^ (n+1)) * h) w v = _
  rw [H.fderiv]
  simp only [add_apply,smul_apply,
    smul_eq_mul,Nat.add_sub_cancel,nsmul_eq_mul]
  rw [pow_succ]
  change w.1 ^ n * w.1 * (fderiv ℂ h w v) + h w *
    (↑(n+1) * w.1 ^ n * v.1) = _
  ring



end SplitTangent.ExceptionalTangency

namespace SplitTangent.ComplexManifold
open Filter Topology Metric Set
variable {X : ComplexManifold.{u}}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 

theorem chart_derivative {F : E → X.Carrier} {z : E} {x : X.Carrier}
    (hF : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z)
    (hx : F z ∈ (chartAt (Model X) x).source) :
    fderiv ℂ ((chartAt (Model X) x) ∘ F) z =
      ((trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (F z)).comp
        (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z) := by
  have hc := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hx
  have ht : (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (F z) =
      mfderiv (ModelWithCorners X) 𝓘(ℂ,Model X) (chartAt (Model X) x) (F z) :=
    TangentBundle.continuousLinearMapAt_trivializationAt (I := ModelWithCorners X) hx
  rw [ht]
  exact mfderiv_eq_fderiv.symm.trans (mfderiv_comp z
    (hc.mdifferentiableAt (by simp)) (hF.mdifferentiableAt (by simp)))

 
theorem locally_eq_of_mfderiv_zero {F : E → X.Carrier} {U : Set E}
    (hU : IsOpen U) (hF : ContMDiffOn 𝓘(ℂ,E) (ModelWithCorners X) ω F U)
    (hd : ∀ z ∈ U, mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z = 0)
    {z : E} (hz : z ∈ U) : ∀ᶠ w in 𝓝 z, F w = F z := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  let c := chartAt (Model X) (F z)
  have hzF := hF.contMDiffAt (hU.mem_nhds hz)
  have hp : ∀ᶠ w in 𝓝 z, F w ∈ c.source :=
    hzF.continuousAt.eventually (c.open_source.mem_nhds (mem_chart_source (Model X) (F z)))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (Filter.Eventually.and (hU.mem_nhds hz) hp)
  have ha (w : E) (hw : w ∈ ball z r) : AnalyticAt ℂ (c ∘ F) w := by
    have hc := contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) (F z)) (hball hw).2
    exact (hc.comp w (hF.contMDiffAt (hU.mem_nhds (hball hw).1))).contDiffAt.analyticAt
  have hd' (w : E) (hw : w ∈ ball z r) : fderiv ℂ (c ∘ F) w = 0 := by
    rw [chart_derivative (hF.contMDiffAt (hU.mem_nhds (hball hw).1)) (hball hw).2,
      hd w (hball hw).1,ContinuousLinearMap.comp_zero]
    rfl
  filter_upwards [Metric.ball_mem_nhds z hr] with w hw
  apply c.injOn (hball hw).2 (mem_chart_source (Model X) (F z))
  exact isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball z r).isPreconnected
    (fun w hw => (ha w hw).differentiableAt.differentiableWithinAt) hd' hw (mem_ball_self hr)

 

theorem eq_of_mfderiv_zero {F : E → X.Carrier} {U : Set E}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hF : ContMDiffOn 𝓘(ℂ,E) (ModelWithCorners X) ω F U)
    (hd : ∀ z ∈ U, mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z = 0)
    {z w : E} (hz : z ∈ U) (hw : w ∈ U) : F z = F w := by
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hconn
  have hl : IsLocallyConstant (fun q : U => F q) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro q
    exact continuous_subtype_val.continuousAt.eventually (locally_eq_of_mfderiv_zero hU hF hd q.2)
  exact hl.apply_eq_of_preconnectedSpace ⟨z,hz⟩ ⟨w,hw⟩

 

theorem curve_eq_of_mfderiv_zero_off_finite {F : ℂ → X.Carrier} {B : Set ℂ}
    (hB : B.Finite) (hF : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω F)
    (hd : ∀ z ∉ B, mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) F z = 0)
    (z w : ℂ) : F z = F w := by
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  have hconn := (hB.countable.isPathConnected_compl_of_one_lt_rank hrank).isConnected.isPreconnected
  have hden : Dense Bᶜ := hB.countable.dense_compl ℝ
  obtain ⟨a,ha⟩ := hden.nonempty
  have hc : F = fun _ => F a := Continuous.ext_on hden hF.continuous continuous_const
    (fun x hx => eq_of_mfderiv_zero hB.isClosed.isOpen_compl hconn hF.contMDiffOn hd hx ha)
  rw [congrFun hc z,congrFun hc w]

end SplitTangent.ComplexManifold

namespace SplitTangent.ExceptionalTangency
open Filter Topology
open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma kills_second_of_wedge (n : ℕ) {z : ℂ} {h : ℂ × ℂ → ℂ}
    (hh : AnalyticAt ℂ h (0,z)) (hu : h (0,z) ≠ 0)
    (A B : ℂ × ℂ → E) (hA : ContinuousAt A (0,z)) (hB : ContinuousAt B (0,z))
    (hwedge : ∀ᶠ w in 𝓝 (0,z),
      (fderiv ℂ (fun w : ℂ × ℂ => w.1 ^ (n+1) * h w) w (1,0)) • B w =
      (fderiv ℂ (fun w : ℂ × ℂ => w.1 ^ (n+1) * h w) w (0,1)) • A w) :
    B (0,z) = 0 := by
  let L := fun w : ℂ × ℂ =>
    (((n+1 : ℕ) : ℂ) * h w + w.1 * fderiv ℂ h w (1,0)) • B w
  let R := fun w : ℂ × ℂ => (w.1 * fderiv ℂ h w (0,1)) • A w
  have hL : ContinuousAt L (0,z) :=
    ((continuousAt_const.mul hh.continuousAt).add
      (continuousAt_fst.mul (hh.fderiv.continuousAt.clm_apply continuousAt_const))).smul hB
  have hR : ContinuousAt R (0,z) :=
    (continuousAt_fst.mul (hh.fderiv.continuousAt.clm_apply continuousAt_const)).smul hA
  have hline : Tendsto (fun r : ℂ => (r,z)) (𝓝[≠] 0) (𝓝 (0,z)) :=
    (continuousAt_id.prodMk continuousAt_const).mono_left nhdsWithin_le_nhds
  have he : (fun r : ℂ => L (r,z)) =ᶠ[𝓝[≠] 0] (fun r => R (r,z)) := by
    filter_upwards [hline.eventually hwedge,hline.eventually hh.eventually_analyticAt,
      self_mem_nhdsWithin] with r hr har hr0
    have hn : r ^ n ≠ 0 := pow_ne_zero _ hr0
    rw [factor_fderiv n har.differentiableAt,factor_fderiv n har.differentiableAt] at hr
    simp only [mul_one,mul_zero,zero_add] at hr
    rw [mul_smul,mul_smul] at hr
    exact smul_right_injective E hn hr
  have h0 := tendsto_nhds_unique_of_eventuallyEq (hL.tendsto.comp hline) (hR.tendsto.comp hline) he
  have hn : (((n+1 : ℕ) : ℂ) * h (0,z)) ≠ 0 := mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero n) hu
  have hs : (((n+1 : ℕ) : ℂ) * h (0,z)) • B (0,z) = 0 := by
    simpa only [L,R,zero_mul,add_zero,zero_smul] using h0
  exact (smul_eq_zero.mp hs).resolve_left hn
end SplitTangent.ExceptionalTangency

namespace SplitTangent.TangentSplitting
open Filter Topology
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

theorem kills_exceptional_of_wedge (n : ℕ) {z : ℂ} {h : ℂ × ℂ → ℂ}
    {F : ℂ × ℂ → X.Carrier} (hF : ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F (0,z))
    (hh : AnalyticAt ℂ h (0,z)) (hu : h (0,z) ≠ 0)
    (hW : ∀ᶠ w in 𝓝 (0,z), S.WedgeAt F (fun w : ℂ × ℂ => w.1^(n+1)*h w) w) :
    S.projector (F (0,z)) (mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F (0,z) (0,1)) = 0 := by
  let x := F (0,z)
  let c := chartAt (Model X) x
  let t := trivializationAt (Model X) (Tangent X) x
  have hx : F (0,z) ∈ c.source := mem_chart_source (Model X) x
  have hnear := (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hF
  have hxnear := hF.continuousAt.eventually (c.open_source.mem_nhds hx)
  have hk : S.projectedInChart x F (0,1) (0,z) = 0 := by
    apply ExceptionalTangency.kills_second_of_wedge n hh hu
      (S.projectedInChart x F (1,0)) (S.projectedInChart x F (0,1))
      (S.projectedInChart_analytic (1,0) hF hx).continuousAt
      (S.projectedInChart_analytic (0,1) hF hx).continuousAt
    filter_upwards [hW,hnear,hxnear] with w hw hFw hxw
    exact (S.chart_wedge_iff hFw hxw).mp hw (1,0) (0,1)
  rw [S.projectedInChart_eq (0,1) hF hx] at hk
  have H := congrArg (t.symmL ℂ (F (0,z))) hk
  change t.symmL ℂ (F (0,z)) (t.continuousLinearMapAt ℂ (F (0,z)) _) = _ at H
  simpa only [t.symmL_continuousLinearMapAt hx,map_zero] using H

 

theorem constant_exceptional {F : ℂ × ℂ → X.Carrier} {h k : ℂ × ℂ → ℂ}
    (n m : ℕ) (hF : ∀ z : ℂ, ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F (0,z))
    (hh : ∀ z : ℂ, AnalyticAt ℂ h (0,z)) (hk : ∀ z : ℂ, AnalyticAt ℂ k (0,z))
    (hB : Set.Finite {z : ℂ | h (0,z) = 0 ∨ k (0,z) = 0})
    (hW : ∀ z : ℂ, ∀ᶠ w in 𝓝 (0,z), S.WedgeAt F (fun w : ℂ × ℂ => w.1^(n+1)*h w) w)
    (hV : ∀ z : ℂ, ∀ᶠ w in 𝓝 (0,z), S.swap.WedgeAt F (fun w : ℂ × ℂ => w.1^(m+1)*k w) w)
    (z w : ℂ) : F (0,z) = F (0,w) := by
  let i : ℂ → ℂ × ℂ := fun z => (0,z)
  have hi : ContDiff ℂ ω i := contDiff_const.prodMk contDiff_id
  have hc : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω (F ∘ i) :=
    fun z => (hF z).comp z hi.contMDiff.contMDiffAt
  apply ComplexManifold.curve_eq_of_mfderiv_zero_off_finite hB hc _ z w
  intro a ha
  have hu : h (0,a) ≠ 0 := fun h => ha (Or.inl h)
  have ku : k (0,a) ≠ 0 := fun h => ha (Or.inr h)
  have hp := S.kills_exceptional_of_wedge n (hF a) (hh a) hu (hW a)
  have hq := S.swap.kills_exceptional_of_wedge m (hF a) (hk a) ku (hV a)
  have hd : mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F (0,a) (0,1) = 0 := by
    change _ - S.projector _ _ = 0 at hq
    rw [hp,sub_zero] at hq
    exact hq
  rw [mfderiv_comp a ((hF a).mdifferentiableAt (by simp)) (hi.contMDiff.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv]
  have hid : fderiv ℂ i a = (ContinuousLinearMap.inr ℂ ℂ ℂ) := by
    exact ((hasFDerivAt_const (0 : ℂ) a).prodMk (hasFDerivAt_id a)).fderiv
  rw [hid]
  apply ContinuousLinearMap.ext
  intro v
  change ℂ at v
  have hv : (0,v) = v • ((0,1) : ℂ × ℂ) := by simp
  let d : (ℂ × ℂ) →L[ℂ] Tangent X (F (0,a)) := mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F (0,a)
  have hd' : d (0,1) = 0 := hd
  change d (0,v) = 0
  rw [hv,map_smul,hd',smul_zero]

end SplitTangent.TangentSplitting

open Filter Topology Metric Set

 

open MvPowerSeries
namespace SplitTangent.FormalBlowup

lemma exp_eta (d : Fin 2 →₀ ℕ) : exp (d 0) (d 1) = d := by
  ext i; fin_cases i <;> simp

lemma coeff_blowup (f : D) (a b : ℕ) :
    coeff (exp (a+b) b) (blowup f) = coeff (exp a b) f := by
  rw [blowup,substAlgHom_apply,coeff_subst coordinateSubstitution_hasSubst]
  rw [finsum_eq_single _ (exp a b)]
  · rw [substituted_monomial]
    simp only [exp_zero,exp_one]
    rw [variable_monomial,coeff_monomial,ite_eq_left rfl,smul_eq_mul,mul_one]
  · intro d hd
    rw [substituted_monomial,variable_monomial,coeff_monomial,ite_eq_right,smul_zero]
    intro H
    have H0 := congrArg (fun d : Fin 2 →₀ ℕ => d 0) H
    have H1 := congrArg (fun d : Fin 2 →₀ ℕ => d 1) H
    simp only [exp_zero,exp_one] at H0 H1
    have H2 : d 0 = a := by omega
    exact hd (by rw [← exp_eta d,H2,← H1])

lemma coeff_x_pow_mul (f : D) (a b k : ℕ) :
    coeff (exp (a+k) b) (x^k * f) = coeff (exp a b) f := by
  rw [X_pow_eq,coeff_monomial_mul,ite_eq_left,one_mul]
  · have H : exp (a+k) b - Finsupp.single 0 k = exp a b := by
      ext i
      fin_cases i <;> simp [exp]
    rw [H]
  · intro i
    fin_cases i <;> simp [exp]

 

lemma coeff_transform_initial (k a b : ℕ) (hab : a+b=k)
    (f : (highOrder k).restrictScalars ℂ) :
    coeff (exp 0 b) (transform k f) = coeff (exp a b) f := by
  have H := congrArg (coeff (exp k b)) (exceptional_mul_transform k f)
  have hx : exp k b = exp (0+k) b := by simp
  rw [hx,coeff_x_pow_mul] at H
  have Hb : coeff (exp (0+k) b) (blowup (f : D)) = coeff (exp a b) f := by
    simpa only [hab,zero_add] using coeff_blowup (f : D) a b
  exact H.trans Hb


lemma transform_monomial (k a b : ℕ) (h : k ≤ a+b) :
    transform k ⟨x^a*y^b,monomial_mem_highOrder k a b h⟩ = x^(a+b-k)*y^b := by
  apply mul_left_cancel₀ (pow_ne_zero _ x_ne_zero)
  rw [exceptional_mul_transform,map_mul,map_pow,map_pow,blowup_x,blowup_y,mul_pow]
  change x^a * (x^b*y^b) = x^k*(x^(a+b-k)*y^b)
  rw [← mul_assoc,← pow_add,← mul_assoc,← pow_add,Nat.add_sub_of_le h]


lemma row_coeff (f : D) (b : ℕ) : PowerSeries.coeff b (row f) = coeff (exp 0 b) f := by
  change coeff (Finsupp.single () b) (killCompl yEmbedding f) = _
  rw [coeff_killCompl,Finsupp.embDomain_single]
  simp [exp,yEmbedding]

lemma insertRow_coeff (g : PowerSeries ℂ) (b : ℕ) :
    coeff (exp 0 b) (insertRow g) = PowerSeries.coeff b g := by
  have H := coeff_embDomain_rename yEmbedding g (Finsupp.single () b)
  simpa [Finsupp.embDomain_single,exp,yEmbedding,insertRow,PowerSeries.coeff] using H

lemma self_sub_insertRow (f : D) : x ∣ f - insertRow (row f) := by
  rw [← pow_one (x : D)]
  apply X_pow_dvd_iff.mpr
  intro d hd
  have hd0 : d 0 = 0 := by omega
  have he : d = exp 0 (d 1) := by rw [← hd0,exp_eta]
  rw [map_sub,he,insertRow_coeff,row_coeff,sub_self]

lemma row_initial_order_le (k a b : ℕ) (hab : a+b=k)
    (f : (highOrder k).restrictScalars ℂ) (hf : coeff (exp a b) (f : D) ≠ 0) :
    (row (transform k f)).order.toNat ≤ k ∧ row (transform k f) ≠ 0 := by
  have hc : PowerSeries.coeff b (row (transform k f)) ≠ 0 := by
    rw [row_coeff,coeff_transform_initial k a b hab]
    exact hf
  have hne : row (transform k f) ≠ 0 := by intro h; simp [h] at hc
  refine ⟨?_,hne⟩
  have hle := PowerSeries.order_le b hc
  have hb := ENat.toNat_le_toNat hle (by simp)
  simp only [ENat.toNat_natCast] at hb
  omega

lemma initial_factor (f : D) (hf : row f ≠ 0) :
    ∃ v : D, IsUnit v ∧ x ∣ f - y^(row f).order.toNat * v := by
  refine ⟨insertRow (PowerSeries.divXPowOrder (row f)),?_,?_⟩
  · apply IsUnit.map insertRow
    rw [PowerSeries.isUnit_iff_constantCoeff,isUnit_iff_ne_zero]
    exact mt PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.mp hf
  · have H := congrArg insertRow (PowerSeries.X_pow_order_mul_divXPowOrder (f := row f))
    simp only [map_mul,map_pow,insertRow_X] at H
    rw [H]
    exact self_sub_insertRow f

 

lemma submodule_eq_top_of_nilpotent {A : Type*} [CommRing A] [Algebra ℂ A]
    (V : Submodule ℂ A) (t : A) (ht : IsNilpotent t)
    (hstable : ∀ v ∈ V, t*v ∈ V)
    (hmod : ∀ a : A, ∃ v ∈ V, ∃ w : A, a = v+t*w) : V = ⊤ := by
  have hp : ∀ n : ℕ, ∀ v ∈ V, t^n*v ∈ V := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro v hv
      simpa only [pow_succ',mul_assoc] using hstable (t^n*v) (ih v hv)
  have hl : ∀ n : ℕ, ∀ a : A, ∃ v ∈ V, ∃ w : A, a = v+t^n*w := by
    intro n
    induction n with
    | zero => intro a; exact ⟨0,V.zero_mem,a,by simp⟩
    | succ n ih =>
      intro a
      obtain ⟨v,hv,w,hw⟩ := ih a
      obtain ⟨v',hv',w',hw'⟩ := hmod w
      refine ⟨v+t^n*v',V.add_mem hv (hp n v' hv'),w',?_⟩
      rw [hw,hw',pow_succ]
      ring
  obtain ⟨n,hn⟩ := ht
  apply top_unique
  intro a ha
  obtain ⟨v,hv,w,hw⟩ := hl n a
  rw [hw]
  simpa [hn] using hv

lemma exceptional_power_in_sup (J : Ideal D) (f : D) (hf : f ∈ J) (hr : row f ≠ 0) :
    y^(row f).order.toNat ∈ J ⊔ Ideal.span {x} := by
  obtain ⟨v,hv,hd⟩ := initial_factor f hr
  let K : Ideal D := J ⊔ Ideal.span {x}
  have hF : f ∈ K := (show J ≤ K from le_sup_left) hf
  have hD : f-y^(row f).order.toNat*v ∈ K :=
    (show Ideal.span {x} ≤ K from le_sup_right) (Ideal.mem_span_singleton.mpr hd)
  have hM : y^(row f).order.toNat*v ∈ K := by
    convert K.sub_mem hF hD using 1; ring
  obtain ⟨u,rfl⟩ := hv
  have H := K.mul_mem_right (↑u⁻¹) hM
  simpa only [mul_assoc,Units.val_inv_eq_inv_val,Units.mul_inv, mul_one] using H

 

lemma low_remainder (J : Ideal D) (q : ℕ) (hyq : y^q ∈ J ⊔ Ideal.span {x})
    (f : D) : f - insertRow ((row f).trunc q : PowerSeries ℂ) ∈ J ⊔ Ideal.span {x} := by
  let K : Ideal D := J ⊔ Ideal.span {x}
  have h1 : f-insertRow (row f) ∈ K := (show Ideal.span {x} ≤ K from le_sup_right)
    (Ideal.mem_span_singleton.mpr (self_sub_insertRow f))
  have H := congrArg insertRow (PowerSeries.eq_X_pow_mul_shift_add_trunc q (row f))
  simp only [map_add,map_mul,map_pow,insertRow_X] at H
  have h2 : insertRow (row f)-insertRow ((row f).trunc q : PowerSeries ℂ) ∈ K := by
    rw [H,add_sub_cancel_right]
    exact K.mul_mem_right _ hyq
  convert K.add_mem h1 h2 using 1; ring



lemma transform_mem (I : Ideal D) (k : ℕ) (hI : I ≤ highOrder k) (f : I) :
    transform k ⟨f,hI f.property⟩ ∈ transformIdeal I k hI := Ideal.subset_span ⟨f,rfl⟩

 

lemma exists_x_pow_mem (I : Ideal D) [FiniteDimensional ℂ (D ⧸ I)] : ∃ n : ℕ, x^n ∈ I := by
  let : IsArtinianRing (D ⧸ I) := IsArtinianRing.of_finite ℂ (D ⧸ I)
  obtain ⟨n,hn⟩ := IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I
  refine ⟨n,hn (Ideal.pow_mem_pow ?_ n)⟩
  rw [IsLocalRing.mem_maximalIdeal,mem_nonunits_iff,MvPowerSeries.isUnit_iff_constantCoeff]
  simp [x]

lemma exists_x_pow_mem_transform (I : Ideal D) (k : ℕ) (hI : I ≤ highOrder k)
    [FiniteDimensional ℂ (D ⧸ I)] : ∃ n : ℕ, x^n ∈ transformIdeal I k hI := by
  obtain ⟨n,hn⟩ := exists_x_pow_mem I
  have hkn : k ≤ n := by
    by_contra h
    have H := mem_highOrder.mp (hI hn) (exp n 0) (by simpa using Nat.lt_of_not_ge h)
    simp [exp,X_pow_eq] at H
  have H := transform_mem I k hI ⟨x^n,hn⟩
  refine ⟨n-k,?_⟩
  have ht : transform k ⟨x^n,hI hn⟩ = x^(n-k) := by
    simpa only [pow_zero,mul_one,Nat.add_zero] using transform_monomial k n 0 (by simpa using hkn)
  rw [ht] at H
  exact H

lemma insertRow_trunc (g : PowerSeries ℂ) (q : ℕ) :
    insertRow (g.trunc q : PowerSeries ℂ) =
      ∑ b ∈ Finset.range q, (PowerSeries.coeff b g) • y^b := by
  rw [PowerSeries.trunc_apply,Nat.Ico_zero_eq_range]
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum, map_sum]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_monomial]
  apply Finset.sum_congr rfl
  intro b hb
  rw [PowerSeries.monomial_eq_C_mul_X_pow,map_mul,map_pow,insertRow_X]
  change (MvPowerSeries.rename yEmbedding (PowerSeries.C _)) * y^b = _
  rw [PowerSeries.C_apply,rename_C,smul_eq_C_mul]

 

lemma quotient_transform_surjective (J : Ideal D) (k : ℕ)
    (hnil : ∃ n : ℕ, x^n ∈ J)
    (q : ℕ) (hq : q ≤ k) (hyq : y^q ∈ J ⊔ Ideal.span {x}) :
    Function.Surjective ((Ideal.Quotient.mkₐ ℂ J).toLinearMap.comp (transform k)) := by
  let Q := Ideal.Quotient.mkₐ ℂ J
  let T := Q.toLinearMap.comp (transform k)
  let V := T.range
  have hY : ∀ b : ℕ, b ≤ k → Q (y^b) ∈ V := by
    intro b hb
    have hab : k ≤ k-b+b := by omega
    refine ⟨⟨x^(k-b)*y^b,monomial_mem_highOrder k (k-b) b hab⟩,?_⟩
    change Q (transform k _) = Q (y^b)
    rw [transform_monomial k (k-b) b hab]
    congr 1
    have he : k-b+b-k=0 := by omega
    simp [he]
  have hstable : ∀ v ∈ V, Q x * v ∈ V := by
    rintro v ⟨f,rfl⟩
    refine ⟨⟨x*f,(highOrder k).mul_mem_left x f.property⟩,?_⟩
    change Q (transform k _) = Q x * Q (transform k f)
    rw [transform_mul,blowup_x,map_mul]
  have hpoly (f : D) : Q (insertRow ((row f).trunc q : PowerSeries ℂ)) ∈ V := by
    rw [insertRow_trunc,map_sum]
    apply V.sum_mem
    intro b hb
    rw [map_smul]
    exact V.smul_mem _ (hY b ((Finset.mem_range.mp hb).le.trans hq))
  have hmod : ∀ a : D ⧸ J, ∃ v ∈ V, ∃ w : D ⧸ J, a = v+Q x*w := by
    intro a
    obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective a
    have H := low_remainder J q hyq f
    obtain ⟨j,hj,z,hz,he⟩ := Submodule.mem_sup.mp H
    obtain ⟨w,rfl⟩ := Ideal.mem_span_singleton.mp hz
    have heq := congrArg Q he
    have hjQ : Q j = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hj
    simp only [map_add,map_sub,map_mul,hjQ,zero_add] at heq
    refine ⟨Q (insertRow ((row f).trunc q : PowerSeries ℂ)),hpoly f,Q w,?_⟩
    change Q f = _
    linear_combination -heq
  have hnilQ : IsNilpotent (Q x) := by
    obtain ⟨n,hn⟩ := hnil
    refine ⟨n,?_⟩
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hn
  exact LinearMap.range_eq_top.mp (submodule_eq_top_of_nilpotent V (Q x) hnilQ hstable hmod)

lemma strict_transform_surjective (I : Ideal D) (k : ℕ) (hI : I ≤ highOrder k)
    [FiniteDimensional ℂ (D ⧸ I)]
    (f : I) (a b : ℕ) (hab : a+b=k) (hf : coeff (exp a b) (f : D) ≠ 0) :
    Function.Surjective ((Ideal.Quotient.mkₐ ℂ (transformIdeal I k hI)).toLinearMap.comp
      (transform k)) := by
  let f' : (highOrder k).restrictScalars ℂ := ⟨f,hI f.property⟩
  obtain ⟨hq,hr⟩ := row_initial_order_le k a b hab f' hf
  exact quotient_transform_surjective (transformIdeal I k hI) k
    (exists_x_pow_mem_transform I k hI) _ hq
    (exceptional_power_in_sup (transformIdeal I k hI) (transform k f')
      (transform_mem I k hI f) hr)

 

theorem finite_colength_strict_drop (I : Ideal D) (k : ℕ) (hk : 0 < k)
    (hI : I ≤ highOrder k) [FiniteDimensional ℂ (D ⧸ I)]
    (f : I) (a b : ℕ) (hab : a+b=k) (hf : coeff (exp a b) (f : D) ≠ 0) :
    FiniteDimensional ℂ (D ⧸ transformIdeal I k hI) ∧
      Module.finrank ℂ (D ⧸ transformIdeal I k hI) < Module.finrank ℂ (D ⧸ I) := by
  let M := (highOrder k).restrictScalars ℂ
  let L := (Ideal.Quotient.mkₐ ℂ I).toLinearMap.comp M.subtype
  let T := (Ideal.Quotient.mkₐ ℂ (transformIdeal I k hI)).toLinearMap.comp (transform k)
  have hker : L.ker ≤ T.ker := by
    intro g hg
    have hgI : (g : D) ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hg
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (transform_mem I k hI ⟨g,hgI⟩)
  let F := L.ker.liftQ T hker
  have hF : Function.Surjective F := by
    intro z
    obtain ⟨g,hg⟩ := strict_transform_surjective I k hI f a b hab hf z
    exact ⟨Submodule.Quotient.mk g,hg⟩
  let : FiniteDimensional ℂ (M ⧸ L.ker) := L.quotKerEquivRange.symm.finiteDimensional
  have : FiniteDimensional ℂ (D ⧸ transformIdeal I k hI) := Module.Finite.of_surjective F hF
  refine ⟨inferInstance,?_⟩
  have hproper : L.range < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    have hr : (Ideal.Quotient.mkₐ ℂ I) 1 ∈ L.range := by rw [htop]; trivial
    obtain ⟨g,hg⟩ := hr
    have hd : (g : D)-1 ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change (Ideal.Quotient.mkₐ ℂ I) ((g : D)-1) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hg
    have hone : (1 : D) ∈ highOrder k := by
      have hh := (highOrder k).sub_mem g.property (hI hd)
      simpa using hh
    have H := mem_highOrder.mp hone 0 (by simpa using hk)
    simp at H
  calc
    Module.finrank ℂ (D ⧸ transformIdeal I k hI) ≤ Module.finrank ℂ (M ⧸ L.ker) :=
      LinearMap.finrank_le_finrank_of_surjective hF
    _ = Module.finrank ℂ L.range := LinearEquiv.finrank_eq L.quotKerEquivRange
    _ < Module.finrank ℂ (D ⧸ I) := Submodule.finrank_lt hproper.ne



lemma exists_minimal_order (I : Ideal D) (hproper : I ≠ ⊤)
    [FiniteDimensional ℂ (D ⧸ I)] :
    ∃ k : ℕ, 0 < k ∧ I ≤ highOrder k ∧
      ∃ f : I, ∃ a b : ℕ, a+b=k ∧ coeff (exp a b) (f : D) ≠ 0 := by
  classical
  let P : ℕ → Prop := fun n => ∃ f : I, ∃ a b : ℕ, a+b=n ∧ coeff (exp a b) (f : D) ≠ 0
  have hex : ∃ n, P n := by
    obtain ⟨n,hn⟩ := exists_x_pow_mem I
    refine ⟨n,⟨x^n,hn⟩,n,0,by omega,?_⟩
    simp [exp,X_pow_eq]
  let k := Nat.find hex
  obtain ⟨f,a,b,hab,hf⟩ := Nat.find_spec hex
  have hI : I ≤ highOrder k := by
    intro g hg
    apply mem_highOrder.mpr
    intro d hd
    by_contra hc
    have hc' : coeff (exp (d 0) (d 1)) g ≠ 0 := by simpa only [exp_eta] using hc
    exact Nat.find_min hex hd ⟨⟨g,hg⟩,d 0,d 1,rfl,hc'⟩
  have hk : 0 < k := by
    by_contra hn
    have hk0 : k=0 := by omega
    have ha : a=0 := by omega
    have hb : b=0 := by omega
    have hunit : IsUnit (f : D) := by
      apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
      apply isUnit_iff_ne_zero.mpr
      simpa [ha,hb,exp] using hf
    exact hproper (I.eq_top_of_isUnit_mem f.property hunit)
  exact ⟨k,hk,hI,f,a,b,hab,hf⟩

lemma blowup_monomial (d : Fin 2 →₀ ℕ) (c : ℂ) :
    blowup (monomial d c) = monomial (exp (d 0+d 1) (d 1)) c := by
  rw [blowup,substAlgHom_apply,subst_monomial coordinateSubstitution_hasSubst,
    substituted_monomial,← Algebra.smul_def,variable_monomial,← map_smul,smul_eq_mul,mul_one]

lemma polynomialTransform_factor (k : ℕ) (p : B) (hp : (p : D) ∈ highOrder k) :
    x^k * (polynomialTransform k p : D) = blowup (p : D) := by
  rw [polynomialTransform,← MvPolynomial.coeToMvPowerSeries.ringHom_apply,map_sum,Finset.mul_sum]
  conv_rhs => rw [MvPolynomial.as_sum p]
  rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply,MvPolynomial.coe_monomial]
  have hk : k ≤ d 0+d 1 := by
    by_contra h
    have hc := mem_highOrder.mp hp d (by omega)
    rw [MvPolynomial.coeff_coe] at hc
    exact MvPolynomial.mem_support_iff.mp hd hc
  rw [X_pow_eq,monomial_mul_monomial,one_mul,blowup_monomial]
  have he : Finsupp.single 0 k + exp (d 0+d 1-k) (d 1) = exp (d 0+d 1) (d 1) := by
    ext i
    fin_cases i <;> simp [exp]
    omega
  rw [he]

lemma transform_polynomial (k : ℕ) (p : B) (hp : (p : D) ∈ highOrder k) :
    transform k ⟨p,hp⟩ = (polynomialTransform k p : D) := by
  apply mul_left_cancel₀ (pow_ne_zero _ x_ne_zero)
  rw [exceptional_mul_transform,polynomialTransform_factor k p hp]

 

lemma mem_ideal_of_rectangle_zero (I : Ideal D) (A B : ℕ)
    (hx : x^A ∈ I) (hy : y^B ∈ I) (f : D)
    (hf : ∀ d : Fin 2 →₀ ℕ, d 0 < A → d 1 < B → coeff d f = 0) : f ∈ I := by
  let fX : D := fun d => if A ≤ d 0 then coeff d f else 0
  have hdX : x^A ∣ fX := by
    apply X_pow_dvd_iff.mpr
    intro d hd
    change (if A ≤ d 0 then coeff d f else 0) = 0
    rw [ite_eq_right (not_le.mpr hd)]
  have hdY : y^B ∣ f-fX := by
    apply X_pow_dvd_iff.mpr
    intro d hd
    rw [map_sub]
    change coeff d f - (if A ≤ d 0 then coeff d f else 0) = 0
    by_cases hA : A ≤ d 0
    · rw [ite_eq_left hA,sub_self]
    · rw [ite_eq_right hA,sub_zero]
      exact hf d (Nat.lt_of_not_ge hA) hd
  obtain ⟨g,hg⟩ := hdX
  obtain ⟨h,hh⟩ := hdY
  have hX : fX ∈ I := by rw [hg]; exact I.mul_mem_right g hx
  have hY : f-fX ∈ I := by rw [hh]; exact I.mul_mem_right h hy
  simpa using I.add_mem hY hX


lemma rectangleMap_apply (A B : ℕ) (c : Fin A × Fin B → ℂ) :
    rectangleMap A B c = ∑ ab : Fin A × Fin B, monomial (exp ab.1 ab.2) (c ab) := by
  simp [rectangleMap]

lemma rectangleMap_coeff (A B : ℕ) (f : D) (d : Fin 2 →₀ ℕ)
    (hA : d 0 < A) (hB : d 1 < B) :
    coeff d (rectangleMap A B (fun ab => coeff (exp ab.1 ab.2) f)) = coeff d f := by
  classical
  rw [rectangleMap_apply,map_sum]
  let i : Fin A × Fin B := (⟨d 0,hA⟩,⟨d 1,hB⟩)
  rw [Finset.sum_eq_single i]
  · simp [i,exp_eta]
  · intro j hj hji
    rw [coeff_monomial,ite_eq_right]
    intro he
    apply hji
    apply Prod.ext <;> apply Fin.ext
    · have H := congrArg (fun d : Fin 2 →₀ ℕ => d 0) he
      simpa [i] using H.symm
    · have H := congrArg (fun d : Fin 2 →₀ ℕ => d 1) he
      simpa [i] using H.symm
  · simp

 
theorem finite_colength_of_coordinate_powers (I : Ideal D) (A B : ℕ)
    (hx : x^A ∈ I) (hy : y^B ∈ I) : FiniteDimensional ℂ (D ⧸ I) := by
  let T := (Ideal.Quotient.mkₐ ℂ I).toLinearMap.comp (rectangleMap A B)
  apply Module.Finite.of_surjective T
  intro z
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨fun ab => coeff (exp ab.1 ab.2) f,?_⟩
  apply Ideal.Quotient.eq.mpr
  apply mem_ideal_of_rectangle_zero I A B hx hy
  intro d hdA hdB
  rw [map_sub,rectangleMap_coeff A B f d hdA hdB,sub_self]


open MvPowerSeries



end SplitTangent.FormalBlowup

namespace SplitTangent.PolynomialBlowup
open FormalBlowup

lemma embed_shear (c : ℂ) (p : P) : embed (shear c p) = FormalBlowup.shear c (embed p) := by
  have h : embed.comp (shear c) = (FormalBlowup.shear c).comp embed := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [x,y]
  exact AlgHom.congr_fun h p

lemma embed_blowup (p : P) : embed (blowup p) = FormalBlowup.blowup (embed p) := by
  have h : embed.comp blowup = FormalBlowup.blowup.comp embed := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply,embed_X]
    rw [FormalBlowup.blowup,MvPowerSeries.substAlgHom_X]
    fin_cases i <;> simp [x,y,FormalBlowup.coordinateSubstitution]
  exact AlgHom.congr_fun h p

lemma polynomial_factor (k : ℕ) (p : P) (hp : embed p ∈ highOrder k) :
    MvPolynomial.X (R := ℂ) (0 : Fin 2)^k * polynomialTransform k p = blowup p := by
  apply MvPolynomial.coe_injective (Fin 2) ℂ
  change embed (_ * _) = embed (blowup p)
  rw [map_mul,map_pow,embed_X,embed_blowup]
  exact polynomialTransform_factor k p hp

lemma shift_blowup (c : ℂ) (p : P) : shift (0,c) (blowup p) = blowup (shear c p) := by
  have h : (shift (0,c)).comp blowup = blowup.comp (shear c) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp
    · simp [mul_add, mul_comm]
  exact AlgHom.congr_fun h p

 

lemma transform_at_direction (c : ℂ) (k : ℕ) (p : P) (hp : embed p ∈ highOrder k) :
    embed (shift (0,c) (polynomialTransform k p)) =
      transform k ⟨FormalBlowup.shear c (embed p),
        (shear_mem_highOrder_iff c (embed p) k).mpr hp⟩ := by
  apply mul_left_cancel₀ (pow_ne_zero k x_ne_zero)
  rw [exceptional_mul_transform]
  have h := congrArg (embed ∘ shift (0,c)) (polynomial_factor k p hp)
  simp only [Function.comp_apply,map_mul,map_pow,shift_X₀,MvPolynomial.C_0,
    add_zero,embed_X,shift_blowup,embed_blowup,embed_shear] at h
  exact h

lemma transform_span {ι : Type*} (f : ι → D) (k : ℕ)
    (hI : Ideal.span (Set.range f) ≤ highOrder k) :
    transformIdeal (Ideal.span (Set.range f)) k hI =
      Ideal.span (Set.range (fun i => transform k ⟨f i,hI (Ideal.subset_span ⟨i,rfl⟩)⟩)) := by
  let J := Ideal.span (Set.range (fun i => transform k ⟨f i,hI (Ideal.subset_span ⟨i,rfl⟩)⟩))
  have hpre : Ideal.span (Set.range f) ≤ transformPreimage k J := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨hI (Ideal.subset_span ⟨i,rfl⟩),Ideal.subset_span ⟨i,rfl⟩⟩
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨g,rfl⟩
    obtain ⟨hg,htg⟩ := hpre g.property
    exact htg
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact transform_mem (Ideal.span (Set.range f)) k hI ⟨f i,Ideal.subset_span ⟨i,rfl⟩⟩

lemma shear_baseIdeal {ι : Type*} (p : ι → P) (c : ℂ) :
    shearIdeal (baseIdeal p) c = baseIdeal (fun i => shear c (p i)) := by
  simp only [shearIdeal,baseIdeal,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact (embed_shear c (p i)).symm

lemma baseIdeal_shift_transform {ι : Type*} (p : ι → P) (k : ℕ)
    (hI : baseIdeal p ≤ highOrder k) (c : ℂ)
    (hJ : shearIdeal (baseIdeal p) c ≤ highOrder k) :
    baseIdeal (fun i => shift (0,c) (polynomialTransform k (p i))) =
      transformIdeal (shearIdeal (baseIdeal p) c) k hJ := by
  simp only [shear_baseIdeal] at hJ ⊢
  simp only [baseIdeal]
  rw [transform_span]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  simpa only [embed_shear] using transform_at_direction c k (p i) (hI (Ideal.subset_span ⟨i,rfl⟩))

end SplitTangent.PolynomialBlowup

namespace SplitTangent.FormalBlowup

lemma order_eq_of_initial (k : ℕ) (f : D) (hf : f ∈ highOrder k)
    (a b : ℕ) (hab : a+b=k) (hc : coeff (exp a b) f ≠ 0) : f.order = k := by
  apply le_antisymm
  · have h := order_le hc
    simpa only [Finsupp.degree_eq_sum,Fin.sum_univ_two,exp_zero,exp_one,hab] using h
  · exact hf

lemma initial_of_order_eq (k : ℕ) (f : D) (h : f.order = k) :
    ∃ a b : ℕ, a+b=k ∧ coeff (exp a b) f ≠ 0 := by
  obtain ⟨d,hd,hdeg⟩ := (order_eq_nat.mp h).1
  refine ⟨d 0,d 1,?_,?_⟩
  · simpa [Finsupp.degree_eq_sum,Fin.sum_univ_two] using hdeg
  · simpa only [exp_eta] using hd

 
theorem uniform_colength_drop (I : Ideal D) (k : ℕ) (hk : 0 < k)
    (hI : I ≤ highOrder k) [FiniteDimensional ℂ (D ⧸ I)]
    (f : I) (a b : ℕ) (hab : a+b=k) (hf : coeff (exp a b) (f : D) ≠ 0) (c : ℂ) :
    FiniteDimensional ℂ (D ⧸ transformIdeal (shearIdeal I c) k (shearIdeal_le_highOrder I k hI c)) ∧
    Module.finrank ℂ (D ⧸ transformIdeal (shearIdeal I c) k (shearIdeal_le_highOrder I k hI c)) <
      Module.finrank ℂ (D ⧸ I) := by
  let : FiniteDimensional ℂ (D ⧸ shearIdeal I c) :=
    Module.Finite.of_surjective (shearQuotientEquiv I c).toLinearMap (shearQuotientEquiv I c).surjective
  have hm : shear c (f : D) ∈ shearIdeal I c := Ideal.mem_map_of_mem _ f.property
  have ho : (shear c (f : D)).order = k := by
    rw [order_shear]
    exact order_eq_of_initial k f (hI f.property) a b hab hf
  obtain ⟨a',b',hab',hf'⟩ := initial_of_order_eq k _ ho
  obtain ⟨hfin,hlt⟩ := finite_colength_strict_drop (shearIdeal I c) k hk
    (shearIdeal_le_highOrder I k hI c) ⟨shear c (f : D),hm⟩ a' b' hab' hf'
  refine ⟨hfin,?_⟩
  simpa only [(shearQuotientEquiv I c).toLinearEquiv.finrank_eq] using hlt

lemma order_le_swap (f : D) : f.order ≤ (swap f).order := by
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (swapCoordinates i).order := by
    apply le_iInf
    intro i
    rw [one_le_order_iff_constCoeff_eq_zero]
    fin_cases i <;> simp [swapCoordinates,x,y]
  calc
    f.order = 1 * f.order := (one_mul _).symm
    _ ≤ (⨅ i, (swapCoordinates i).order) * f.order := mul_le_mul h1 le_rfl bot_le bot_le
    _ ≤ (swap f).order := by simpa only [swap,substAlgHom_apply] using le_order_subst swapCoordinates_hasSubst f
lemma order_swap (f : D) : (swap f).order = f.order := by
  apply le_antisymm
  · have H := order_le_swap (swap f)
    rwa [swap_swap] at H
  · exact order_le_swap f
lemma swap_mem_highOrder_iff (f : D) (k : ℕ) : swap f ∈ highOrder k ↔ f ∈ highOrder k := by
  change ((k : ℕ∞) ≤ (swap f).order) ↔ (k : ℕ∞) ≤ f.order
  rw [order_swap]
lemma swapIdeal_le_highOrder (I : Ideal D) (k : ℕ) (hI : I ≤ highOrder k) :
    swapIdeal I ≤ highOrder k := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro f hf
  exact (swap_mem_highOrder_iff f k).mpr (hI hf)

end SplitTangent.FormalBlowup

namespace SplitTangent.PolynomialBlowup
section
open FormalBlowup

lemma embed_swap (p : P) : embed (swap p) = FormalBlowup.swap (embed p) := by
  have h : embed.comp swap = FormalBlowup.swap.comp embed := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [x,y]
  exact AlgHom.congr_fun h p
lemma swap_baseIdeal {ι : Type*} (p : ι → P) :
    swapIdeal (baseIdeal p) = baseIdeal (fun i => swap (p i)) := by
  simp only [swapIdeal,baseIdeal,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact (embed_swap (p i)).symm



lemma child_finite_drop {ι : Type*} (p : ι → P) (k : ℕ) (hk : 0 < k)
    (hI : baseIdeal p ≤ highOrder k) [FiniteDimensional ℂ (D ⧸ baseIdeal p)]
    (f : baseIdeal p) (a b : ℕ) (hab : a+b=k) (hf : coeff (exp a b) (f : D) ≠ 0) (c : ℂ) :
    FiniteDimensional ℂ (D ⧸ baseIdeal (child p k c)) ∧
    Module.finrank ℂ (D ⧸ baseIdeal (child p k c)) < Module.finrank ℂ (D ⧸ baseIdeal p) := by
  have he : baseIdeal (child p k c) =
      transformIdeal (shearIdeal (baseIdeal p) c) k (shearIdeal_le_highOrder _ k hI c) :=
    baseIdeal_shift_transform p k hI c (shearIdeal_le_highOrder _ k hI c)
  rw [he]
  exact uniform_colength_drop (baseIdeal p) k hk hI f a b hab hf c

lemma swap_finite {ι : Type*} (p : ι → P) [FiniteDimensional ℂ (D ⧸ baseIdeal p)] :
    FiniteDimensional ℂ (D ⧸ baseIdeal (fun i => swap (p i))) := by
  rw [← swap_baseIdeal]
  exact Module.Finite.of_surjective (swapQuotientEquiv (baseIdeal p)).toLinearMap
    (swapQuotientEquiv (baseIdeal p)).surjective
lemma swap_finrank {ι : Type*} (p : ι → P) :
    Module.finrank ℂ (D ⧸ baseIdeal (fun i => swap (p i))) = Module.finrank ℂ (D ⧸ baseIdeal p) := by
  rw [← swap_baseIdeal]
  exact (swapQuotientEquiv (baseIdeal p)).toLinearEquiv.finrank_eq.symm

lemma swap_child_finite_drop {ι : Type*} (p : ι → P) (k : ℕ) (hk : 0 < k)
    (hI : baseIdeal p ≤ highOrder k) [FiniteDimensional ℂ (D ⧸ baseIdeal p)]
    (f : baseIdeal p) (a b : ℕ) (hab : a+b=k) (hf : coeff (exp a b) (f : D) ≠ 0) (c : ℂ) :
    FiniteDimensional ℂ (D ⧸ baseIdeal (child (fun i => swap (p i)) k c)) ∧
    Module.finrank ℂ (D ⧸ baseIdeal (child (fun i => swap (p i)) k c)) <
      Module.finrank ℂ (D ⧸ baseIdeal p) := by
  let := swap_finite p
  have hs : baseIdeal (fun i => swap (p i)) ≤ highOrder k := by
    rw [← swap_baseIdeal]
    exact swapIdeal_le_highOrder _ k hI
  have hm : FormalBlowup.swap (f : D) ∈ baseIdeal (fun i => swap (p i)) := by
    rw [← swap_baseIdeal]
    exact Ideal.mem_map_of_mem _ f.property
  have ho : (FormalBlowup.swap (f : D)).order = k := by
    rw [order_swap]
    exact order_eq_of_initial k f (hI f.property) a b hab hf
  obtain ⟨a',b',hab',hf'⟩ := initial_of_order_eq k _ ho
  obtain ⟨hfin,hlt⟩ := child_finite_drop (fun i => swap (p i)) k hk hs
    ⟨FormalBlowup.swap (f : D),hm⟩ a' b' hab' hf' c
  exact ⟨hfin,by simpa only [swap_finrank] using hlt⟩



lemma value_add (p q : P) (w : ℂ × ℂ) : value (p+q) w = value p w + value q w := (valueHom w).map_add p q
lemma value_mul (p q : P) (w : ℂ × ℂ) : value (p*q) w = value p w * value q w := (valueHom w).map_mul p q
lemma value_pow (p : P) (n : ℕ) (w : ℂ × ℂ) : value (p^n) w = value p w ^ n := (valueHom w).map_pow p n

lemma constant_embed (p : P) : MvPowerSeries.constantCoeff (embed p) = value p 0 := by
  have H : constant.comp embed = valueHom 0 := by
    apply MvPolynomial.algHom_ext
    intro i
    change MvPowerSeries.constantCoeff (embed (MvPolynomial.X i)) = (valueHom 0) (MvPolynomial.X i)
    rw [embed_X]
    fin_cases i <;> simp [valueHom]
  exact AlgHom.congr_fun H p

lemma baseIdeal_ne_top_iff {ι : Type*} (p : ι → P) :
    baseIdeal p ≠ ⊤ ↔ ∀ i, value (p i) 0 = 0 := by
  constructor
  · intro hp i
    by_contra hi
    apply hp
    apply (baseIdeal p).eq_top_of_isUnit_mem (Ideal.subset_span ⟨i,rfl⟩)
    rw [MvPowerSeries.isUnit_iff_constantCoeff,isUnit_iff_ne_zero,constant_embed]
    exact hi
  · intro h
    have H : baseIdeal p ≤ RingHom.ker (MvPowerSeries.constantCoeff : D →+* ℂ) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change MvPowerSeries.constantCoeff (embed (p i)) = 0
      rw [constant_embed,h i]
    exact ne_top_of_le_ne_top (RingHom.ker_ne_top _) H
lemma baseIdeal_eq_top_iff {ι : Type*} (p : ι → P) :
    baseIdeal p = ⊤ ↔ ∃ i, value (p i) 0 ≠ 0 := by
  classical
  simpa only [not_not,not_forall] using not_congr (baseIdeal_ne_top_iff p)

lemma value_shift (p : P) (a w : ℂ × ℂ) : value (shift a p) w = value p (w+a) := by
  have H : (valueHom w).comp (shift a) = valueHom (w+a) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [valueHom,shift]
  exact AlgHom.congr_fun H p
lemma value_blowup (p : P) (w : ℂ × ℂ) : value (blowup p) w = value p (w.1,w.1*w.2) := by
  have H : (valueHom w).comp blowup = valueHom (w.1,w.1*w.2) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [valueHom,blowup]
  exact AlgHom.congr_fun H p
lemma value_swap (p : P) (w : ℂ × ℂ) : value (swap p) w = value p (w.2,w.1) := by
  have H : (valueHom w).comp swap = valueHom (w.2,w.1) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [valueHom,swap]
  exact AlgHom.congr_fun H p

 

lemma child_factor {ι : Type*} (p : ι → P) (k : ℕ) (hI : baseIdeal p ≤ highOrder k)
    (c : ℂ) (i : ι) (w : ℂ × ℂ) :
    w.1^k * value (child p k c i) w = value (p i) (w.1,w.1*(w.2+c)) := by
  have H := congrArg (fun q => value q (w+(0,c)))
    (polynomial_factor k (p i) (hI (Ideal.subset_span ⟨i,rfl⟩)))
  simpa only [value_mul,value_pow,value_X₀,value_blowup,value_shift,child,
    Prod.fst_add,Prod.snd_add,Prod.fst,Prod.snd,add_zero] using H



lemma linePolynomial_eval (p : P) (c : ℂ) : (linePolynomial p).eval c = value p (0,c) := by
  have H : (Polynomial.aeval c).comp linePolynomial = valueHom (0,c) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [linePolynomial,valueHom]
  simpa [Polynomial.aeval_def, Algebra.algebraMap_self, value] using AlgHom.congr_fun H p

lemma row_embed (p : P) : row (embed p) = (linePolynomial p : PowerSeries ℂ) := by
  have H : row.comp embed = (Polynomial.coeToPowerSeries.algHom ℂ).comp linePolynomial := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · change row (embed (MvPolynomial.X 0)) = _
      rw [embed_X]
      have h0 : row (X 0) = 0 := killCompl_X_eq_zero (by simp [yEmbedding])
      rw [h0]
      simp [linePolynomial]
    · change row (embed (MvPolynomial.X 1)) = _
      rw [embed_X]
      have h1 : row (X 1) = PowerSeries.X := killCompl_X ()
      rw [h1]
      simp [linePolynomial,Polynomial.coeToPowerSeries.algHom_apply]
  simpa only [AlgHom.comp_apply,Polynomial.coeToPowerSeries.algHom_apply,
    Algebra.algebraMap_self,PowerSeries.map_id,id_eq] using AlgHom.congr_fun H p

lemma exists_generator_initial {ι : Type*} (p : ι → P) (k : ℕ)
    (hI : baseIdeal p ≤ highOrder k) (f : baseIdeal p)
    (a b : ℕ) (hab : a+b=k) (hf : coeff (exp a b) (f : D) ≠ 0) :
    ∃ i : ι, ∃ a' b' : ℕ, a'+b'=k ∧ coeff (exp a' b') (embed (p i)) ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have hJ : baseIdeal p ≤ highOrder (k+1) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    apply mem_highOrder.mpr
    intro d hd
    by_cases he : d 0+d 1=k
    · simpa only [exp_eta] using hn i (d 0) (d 1) he
    · exact mem_highOrder.mp (hI (Ideal.subset_span ⟨i,rfl⟩)) d (by omega)
  exact hf (mem_highOrder.mp (hJ f.property) (exp a b) (by simp [hab]))

 

theorem finite_bad_directions {ι : Type*} (p : ι → P) (k : ℕ)
    (hI : baseIdeal p ≤ highOrder k) (f : baseIdeal p)
    (a b : ℕ) (hab : a+b=k) (hf : coeff (exp a b) (f : D) ≠ 0) :
    {c : ℂ | baseIdeal (child p k c) ≠ ⊤}.Finite := by
  obtain ⟨i,a',b',hab',hc⟩ := exists_generator_initial p k hI f a b hab hf
  have hi := hI (Ideal.subset_span ⟨i,rfl⟩)
  have hrow : row (transform k ⟨embed (p i),hi⟩) ≠ 0 :=
    (row_initial_order_le k a' b' hab' ⟨embed (p i),hi⟩ hc).2
  have hpoly : linePolynomial (polynomialTransform k (p i)) ≠ 0 := by
    intro he
    have H : row (transform k ⟨embed (p i),hi⟩) = 0 := by
      have ht := transform_polynomial k (p i) hi
      change transform k ⟨embed (p i),hi⟩ = embed (polynomialTransform k (p i)) at ht
      exact (congrArg row ht).trans ((row_embed _).trans (by simp [he]))
    exact hrow H
  apply (Polynomial.finite_setOfPred_isRoot hpoly).subset
  intro c hc
  have H := (baseIdeal_ne_top_iff (child p k c)).mp hc i
  change value (shift (0,c) (polynomialTransform k (p i))) 0 = 0 at H
  rw [value_shift,zero_add] at H
  exact (linePolynomial_eval _ c).trans H

end

section
open FormalBlowup Filter Topology

lemma value_analytic (p : P) (w : ℂ × ℂ) : AnalyticAt ℂ (value p) w := by
  change AnalyticAt ℂ (fun z => value p z) w
  induction p using MvPolynomial.induction_on with
  | C a => simpa only [value_C] using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ × ℂ => a) w)
  | add p q hp hq => simpa only [value_add,Pi.add_apply] using hp.fun_add hq
  | mul_X p i hp =>
      have hi : AnalyticAt ℂ (fun z : ℂ × ℂ => ![z.1,z.2] i) w := by
        fin_cases i
        · simpa using ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt w)
        · simpa using ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt w)
      simpa only [value,valueHom,map_mul,MvPolynomial.aeval_X] using hp.fun_mul hi

lemma finite_isolated {T : Type*} [TopologicalSpace T] [T1Space T] {B : Set T}
    (hB : B.Finite) (a : T) : ∀ᶠ z in 𝓝 a, z ∈ B → z = a := by
  have hn : a ∈ (B \ {a})ᶜ := by simp
  filter_upwards [(hB.sdiff (t := {a})).isClosed.isOpen_compl.mem_nhds hn] with z hz hzb
  by_contra hza
  exact hz ⟨hzb,hza⟩

lemma child_isolated {ι : Type*} (p : ι → P) (k : ℕ)
    (hI : baseIdeal p ≤ highOrder k) (f : baseIdeal p)
    (a b : ℕ) (hab : a+b=k) (hf : coeff (exp a b) (f : D) ≠ 0)
    (hp : IsolatedAtOrigin p) (c : ℂ) : IsolatedAtOrigin (child p k c) := by
  have hbad := finite_bad_directions p k hI f a b hab hf
  have he := finite_isolated hbad c
  have hadd : Tendsto (fun z : ℂ => z+c) (𝓝 0) (𝓝 c) := by
    simpa only [id_eq,zero_add] using (continuousAt_id.add_const c).tendsto (x := (0 : ℂ))
  have hz := hadd.eventually he
  have hmap : Tendsto (fun w : ℂ × ℂ => (w.1,w.1*(w.2+c))) (𝓝 0) (𝓝 0) := by
    convert (continuous_fst.prodMk (continuous_fst.mul (continuous_snd.add_const c))).tendsto (0 : ℂ × ℂ) using 1 <;> first | rfl | simp only [Pi.mul_apply,Prod.fst_zero,Prod.snd_zero,zero_mul,Prod.mk_zero_zero]
  have hp' := hmap.eventually hp
  have hz' := (continuous_snd.tendsto (0 : ℂ × ℂ)).eventually hz
  filter_upwards [hp',hz'] with w hw hwz hzero
  have H : (w.1,w.1*(w.2+c)) = (0 : ℂ × ℂ) := by
    apply hw
    intro i
    rw [← child_factor p k hI c i w,hzero i,mul_zero]
  have hx : w.1 = 0 := congrArg Prod.fst H
  have hchild : baseIdeal (child p k (w.2+c)) ≠ ⊤ := by
    apply (baseIdeal_ne_top_iff _).mpr
    intro i
    have hi := hzero i
    change value (shift (0,c) (polynomialTransform k (p i))) w = 0 at hi
    change value (shift (0,w.2+c) (polynomialTransform k (p i))) 0 = 0
    rw [value_shift,zero_add]
    have hw : w + (0,c) = (0,w.2+c) := Prod.ext (by simpa using hx) rfl
    simpa only [value_shift,hw] using hi
  have hy : w.2 = 0 := add_right_cancel ((hwz hchild).trans (zero_add c).symm)
  exact Prod.ext hx hy

end

open FormalBlowup

lemma X_dvd_of_linePolynomial_eq_zero {p : P} (hp : linePolynomial p = 0) :
    MvPolynomial.X 0 ∣ p := by
  apply MvPolynomial.X_dvd_iff_modMonomial_eq_zero.mpr
  ext d
  by_cases hd : 1 ≤ d 0
  · have hle : Finsupp.single 0 1 ≤ d := Finsupp.single_le_iff.mpr hd
    simp only [MvPolynomial.coeff_modMonomial_of_le _ hle,MvPolynomial.coeff_zero]
  · have hd0 : d 0 = 0 := by omega
    have hrow : row (embed p) = 0 := by rw [row_embed,hp]; simp
    have H := congrArg (PowerSeries.coeff (d 1)) hrow
    rw [row_coeff] at H
    have he : exp 0 (d 1) = d := by rw [← hd0,exp_eta]
    have hnle : ¬Finsupp.single 0 1 ≤ d := by simpa [Finsupp.single_le_iff] using hd
    simpa only [MvPolynomial.coeff_modMonomial_of_not_le _ hnle,MvPolynomial.coeff_zero,
      he,embed_apply,MvPolynomial.coeff_coe,map_zero] using H

lemma blowup_injective : Function.Injective blowup := by
  apply (injective_iff_map_eq_zero blowup).mpr
  intro p hp
  apply MvPolynomial.ext
  intro d
  have H := congrArg (fun q : P => coeff (exp (d 0+d 1) (d 1)) (embed q)) hp
  rw [embed_blowup,coeff_blowup] at H
  simpa only [exp_eta,embed_apply,MvPolynomial.coeff_coe,map_zero,MvPowerSeries.coeff_zero,
    MvPolynomial.coeff_zero] using H

 

theorem coordinate_exceptional_factor {p : P} (hp : p ≠ 0) (h0 : value p 0 = 0) :
    ∃ n : ℕ, ∃ q : P, blowup p = MvPolynomial.X 0 ^ (n+1) * q ∧
      linePolynomial q ≠ 0 := by
  have hb : blowup p ≠ 0 := fun h => hp (blowup_injective (h.trans (map_zero blowup).symm))
  obtain ⟨m,q,hn,hq⟩ := WfDvdMonoid.max_power_factor hb (MvPolynomial.X_prime (i := (0 : Fin 2))).irreducible
  have hl : linePolynomial q ≠ 0 := fun h => hn (X_dvd_of_linePolynomial_eq_zero h)
  have hb0 : linePolynomial (blowup p) = 0 := by
    apply Polynomial.funext
    intro z
    rw [linePolynomial_eval,value_blowup]
    simpa only [zero_mul,Prod.mk_zero_zero,Polynomial.eval_zero] using h0
  have hm : m ≠ 0 := by
    intro hm
    rw [hm,pow_zero,one_mul] at hq
    exact hl (hq ▸ hb0)
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  exact ⟨n,q,hq,hl⟩



lemma power_times_unit_product (i : Fin 2) (s : Finset (ℂ × ℂ)) :
    ∃ (n : ℕ) (u : D), IsUnit u ∧
      (∏ b ∈ s, (MvPowerSeries.X i - MvPowerSeries.C (![b.1,b.2] i))) =
        MvPowerSeries.X i ^ n * u := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0,1,isUnit_one,by simp⟩
  | @insert b s hb ih =>
    obtain ⟨n,u,hu,he⟩ := ih
    rw [Finset.prod_insert hb,he]
    by_cases hz : ![b.1,b.2] i = 0
    · refine ⟨n+1,u,hu,?_⟩
      simp only [hz,map_zero,sub_zero,pow_succ]; ring
    · refine ⟨n,(MvPowerSeries.X i - MvPowerSeries.C (![b.1,b.2] i))*u,?_,by ring⟩
      apply IsUnit.mul _ hu
      rw [MvPowerSeries.isUnit_iff_constantCoeff,isUnit_iff_ne_zero]
      simpa only [map_sub,MvPowerSeries.constantCoeff_X,MvPowerSeries.constantCoeff_C,zero_sub,neg_ne_zero] using hz

lemma coordinate_power_of_finite_zeros {ι : Type*} (p : ι → P)
    (hB : Set.Finite {w : ℂ × ℂ | ∀ j, value (p j) w = 0}) (i : Fin 2) :
    ∃ n : ℕ, MvPowerSeries.X i ^ n ∈ baseIdeal p := by
  classical
  let s := hB.toFinset
  let q : P := ∏ b ∈ s, (MvPolynomial.X i - MvPolynomial.C (![b.1,b.2] i))
  let J : Ideal P := Ideal.span (Set.range p)
  have hq : q ∈ J.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
    intro z hz
    have he : ![z 0,z 1] = z := by ext j; fin_cases j <;> simp
    have hm : (z 0,z 1) ∈ s := by
      rw [Set.Finite.mem_toFinset]
      intro j
      change MvPolynomial.aeval ![z 0,z 1] (p j) = 0
      rw [he]
      exact hz (p j) (Ideal.subset_span ⟨j,rfl⟩)
    dsimp only [q]
    rw [map_prod]
    apply Finset.prod_eq_zero hm
    simp only [map_sub,MvPolynomial.aeval_X,MvPolynomial.aeval_C,he,Algebra.algebraMap_self,RingHom.id_apply,sub_self]
  obtain ⟨m,hm⟩ := hq
  have heJ : Ideal.map embed J = baseIdeal p := by
    simp only [J,baseIdeal,Ideal.map_span,← Set.range_comp]
    rfl
  have hmem : embed q ^ m ∈ baseIdeal p := by
    rw [← heJ,← map_pow]
    exact Ideal.mem_map_of_mem _ hm
  obtain ⟨n,u,hu,he⟩ := power_times_unit_product i s
  have hqe : embed q = MvPowerSeries.X i ^ n * u := by
    dsimp only [q]
    simpa only [map_prod,map_sub,embed_X,embed_C] using he
  rw [hqe,mul_pow,← pow_mul] at hmem
  exact ⟨n*m,(baseIdeal p).mul_unit_mem_iff_mem (hu.pow m) |>.mp hmem⟩

 

theorem finite_colength_of_finite_zeros {ι : Type*} (p : ι → P)
    (hB : Set.Finite {w : ℂ × ℂ | ∀ j, value (p j) w = 0}) :
    FiniteDimensional ℂ (D ⧸ baseIdeal p) := by
  obtain ⟨a,ha⟩ := coordinate_power_of_finite_zeros p hB 0
  obtain ⟨b,hb⟩ := coordinate_power_of_finite_zeros p hB 1
  exact finite_colength_of_coordinate_powers (baseIdeal p) a b ha hb

lemma finite_zeros_shift {ι : Type*} (p : ι → P)
    (hB : Set.Finite {w : ℂ × ℂ | ∀ j, value (p j) w = 0}) (a : ℂ × ℂ) :
    Set.Finite {w : ℂ × ℂ | ∀ j, value (shift a (p j)) w = 0} := by
  apply (hB.image (fun w => w-a)).subset
  intro w hw
  exact ⟨w+a,fun j => (value_shift _ _ _).symm.trans (hw j),add_sub_cancel_right w a⟩

end SplitTangent.PolynomialBlowup

namespace SplitTangent.IsolatedZero

 

theorem lower_bound_on_disc {f : ℂ → ℂ} {r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hf : ∀ z ∈ closedBall (0 : ℂ) r, DifferentiableAt ℂ f z)
    (hn : ∀ z ∈ closedBall (0 : ℂ) r, f z ≠ 0)
    (hb : ∀ z ∈ sphere (0 : ℂ) r, c ≤ ‖f z‖) : c ≤ ‖f 0‖ := by
  have hd : DiffContOnCl ℂ (fun z => (f z)⁻¹) (ball (0 : ℂ) r) := by
    refine ⟨?_,?_⟩
    · intro z hz
      exact ((hf z (ball_subset_closedBall hz)).inv (hn z (ball_subset_closedBall hz))).differentiableWithinAt
    · rw [closure_ball _ hr.ne']
      exact fun z hz => ((hf z hz).continuousAt.inv₀ (hn z hz)).continuousWithinAt
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := (0 : ℂ)) (r := r))
    hd (C := c⁻¹) (fun z hz => ?_) (subset_closure (mem_ball_self hr))
  · rw [norm_inv] at h
    exact (inv_le_inv₀ (norm_pos_iff.mpr (hn 0 (mem_closedBall_self hr.le))) hc).mp h
  · rw [frontier_ball _ hr.ne'] at hz
    rw [norm_inv]
    exact (inv_le_inv₀ (norm_pos_iff.mpr (hn z (sphere_subset_closedBall hz))) hc).mpr (hb z hz)

 

theorem nonzero_of_punctured_nonzero {f : ℂ × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hn : ∀ᶠ w in 𝓝[≠] (0 : ℂ × ℂ), f w ≠ 0) : f 0 ≠ 0 := by
  intro hzero
  have hn' : ∀ᶠ w in 𝓝 (0 : ℂ × ℂ), w ≠ 0 → f w ≠ 0 := by
    simpa only [eventually_nhdsWithin_iff,mem_compl_iff,mem_singleton_iff] using hn
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hf.eventually_analyticAt.and hn')
  let R := r / 2
  have hR : 0 < R := half_pos hr
  have hxy {x y : ℂ} (hx : ‖x‖ < R) (hy : ‖y‖ ≤ R) :
      (x,y) ∈ ball (0 : ℂ × ℂ) r := by
    rw [mem_ball_zero_iff,Prod.norm_def,max_lt_iff]
    exact ⟨hx.trans (half_lt_self hr),hy.trans_lt (half_lt_self hr)⟩
  have h0y {y : ℂ} (hy : y ∈ sphere (0 : ℂ) R) :
      AnalyticAt ℂ f (0,y) ∧ f (0,y) ≠ 0 := by
    have hy' : ‖y‖ = R := by simpa using hy
    have ht := hball (hxy (x := 0) (by simpa using hR) hy'.le)
    refine ⟨ht.1,ht.2 ?_⟩
    intro he
    have he' : y = 0 := congrArg Prod.snd he
    rw [he',norm_zero] at hy'
    exact hR.ne' hy'.symm
  have hc : ContinuousOn (fun y : ℂ => ‖f (0,y)‖) (sphere 0 R) := by
    intro y hy
    exact ((h0y hy).1.continuousAt.comp (continuousAt_const.prodMk continuousAt_id)).norm.continuousWithinAt
  obtain ⟨y₀,hy₀,hmin⟩ := (isCompact_sphere (0 : ℂ) R).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hR.le) hc
  let c := ‖f (0,y₀)‖ / 2
  have hcpos : 0 < c := half_pos (norm_pos_iff.mpr (h0y hy₀).2)
  have hbound : ∀ᶠ x : ℂ in 𝓝 0, ∀ y ∈ sphere (0 : ℂ) R, c < ‖f (x,y)‖ := by
    apply (isCompact_sphere (0 : ℂ) R).eventually_forall_of_forall_eventually
    intro y hy
    exact (h0y hy).1.continuousAt.norm.eventually (lt_mem_nhds
      ((half_lt_self (norm_pos_iff.mpr (h0y hy₀).2)).trans_le (hmin hy)))
  have hsmall : ∀ᶠ x : ℂ in 𝓝 0, ‖f (x,0)‖ < c := by
    have hcont : ContinuousAt (fun x : ℂ => ‖f (x,(0 : ℂ))‖) 0 :=
      (hf.continuousAt.comp (f := fun x : ℂ => (x,(0 : ℂ)))
        (continuousAt_id.prodMk continuousAt_const)).norm
    apply Filter.Tendsto.eventually (p := fun q : ℝ => q < c) hcont
    change {q : ℝ | q < c} ∈ 𝓝 ‖f (0 : ℂ × ℂ)‖
    rw [hzero,norm_zero]
    exact gt_mem_nhds hcpos
  have hcontra : ∀ᶠ x : ℂ in 𝓝[≠] 0, False := by
    filter_upwards [hbound.filter_mono nhdsWithin_le_nhds,hsmall.filter_mono nhdsWithin_le_nhds,
      (show ∀ᶠ x : ℂ in 𝓝 0, x ∈ ball 0 R from ball_mem_nhds 0 hR).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with x hb hs hx hx0
    have hx' : ‖x‖ < R := by simpa using hx
    have hnz (y : ℂ) (hy : y ∈ closedBall (0 : ℂ) R) : f (x,y) ≠ 0 := by
      apply (hball (hxy hx' (by simpa using hy))).2
      intro he
      exact hx0 (congrArg Prod.fst he)
    have hdf (y : ℂ) (hy : y ∈ closedBall (0 : ℂ) R) :
        DifferentiableAt ℂ (fun y : ℂ => f (x,y)) y :=
      ((hball (hxy hx' (by simpa using hy))).1.differentiableAt).comp y
        ((differentiableAt_const x).prodMk differentiableAt_id)
    exact (not_le_of_gt hs) (lower_bound_on_disc hR hcpos hdf hnz (fun y hy => (hb y hy).le))
  exact hcontra.exists.elim (fun _ h => h)

 
theorem nonzero_of_punctured_nonzero_at {f : ℂ × ℂ → ℂ} {a : ℂ × ℂ}
    (hf : AnalyticAt ℂ f a) (hn : ∀ᶠ w in 𝓝[≠] a, f w ≠ 0) : f a ≠ 0 := by
  have hn' : ∀ᶠ w in 𝓝 a, w ≠ a → f w ≠ 0 := by
    simpa only [eventually_nhdsWithin_iff,mem_compl_iff,mem_singleton_iff] using hn
  have ht : ContinuousAt (fun w : ℂ × ℂ => w + a) 0 := continuousAt_id.add_const a
  have hft : AnalyticAt ℂ (fun w : ℂ × ℂ => f (w+a)) 0 := by
    simpa only [Function.comp_def,Pi.add_apply,id_eq,zero_add] using hf.comp_of_eq (analyticAt_id.add (analyticAt_const)) (zero_add a)
  have hnt : ∀ᶠ w in 𝓝[≠] (0 : ℂ × ℂ), f (w+a) ≠ 0 := by
    have he : ∀ᶠ w in 𝓝 (0 : ℂ × ℂ), w + a ≠ a → f (w+a) ≠ 0 := by
      have ht' : Tendsto (fun w : ℂ × ℂ => w+a) (𝓝 0) (𝓝 a) := by simpa only [ContinuousAt,zero_add] using ht
      exact ht'.eventually hn'
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w hw hne
    apply hw
    simpa only [ne_eq,add_eq_right] using (show w ≠ 0 from hne)
  simpa only [zero_add] using nonzero_of_punctured_nonzero hft hnt

end SplitTangent.IsolatedZero

namespace SplitTangent.ProjectiveEmbedding
variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)

 

theorem nonzero_of_continuous_incidence {Q : ℂ × ℂ → Fin (e.N+1) → ℂ}
    {F : ℂ × ℂ → X.Carrier} {a : ℂ × ℂ} (hQ : AnalyticAt ℂ Q a)
    (hF : ContinuousAt F a) (hnz : ∀ᶠ w in 𝓝[≠] a, Q w ≠ 0)
    (hi : ∀ᶠ w in 𝓝[≠] a, e.Incidence (F w) (Q w)) : Q a ≠ 0 := by
  obtain ⟨i,hpi⟩ := Function.ne_iff.mp (e.map (F a)).rep_nonzero
  change (e.map (F a)).rep i ≠ 0 at hpi
  have hp : ∀ᶠ w in 𝓝 a, (e.map (F w)).rep i ≠ 0 :=
    hF.eventually ((e.open_patch i).mem_nhds hpi)
  have hni : ∀ᶠ w in 𝓝[≠] a, Q w i ≠ 0 := by
    filter_upwards [hp.filter_mono nhdsWithin_le_nhds,hnz,hi] with w hw hn hh
    intro hz
    apply hn
    ext j
    rw [(e.incidence_iff_coordinates hw).mp hh j,hz,zero_mul]
    rfl
  have hqa : Q a i ≠ 0 := IsolatedZero.nonzero_of_punctured_nonzero_at
    ((ContinuousLinearMap.proj i : (Fin (e.N+1) → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp hQ) hni
  intro hz
  exact hqa (congrFun hz i)

end SplitTangent.ProjectiveEmbedding

open Filter Topology Set Metric
namespace SplitTangent.AffineBlowup


variable {Y : Type*} [TopologicalSpace Y]

 

theorem tendsto_of_constant_exceptional {F H₁ H₂ : ℂ × ℂ → Y} {a : Y}
    (h₁ : ∀ z ∈ closedBall (0 : ℂ) 1, ContinuousAt H₁ (0,z))
    (h₂ : ∀ z ∈ closedBall (0 : ℂ) 1, ContinuousAt H₂ (0,z))
    (hc₁ : ∀ z ∈ closedBall (0 : ℂ) 1, H₁ (0,z) = a)
    (hc₂ : ∀ z ∈ closedBall (0 : ℂ) 1, H₂ (0,z) = a)
    (hf₁ : ∀ w : ℂ × ℂ, w.1 ≠ 0 → H₁ w = F (first w))
    (hf₂ : ∀ w : ℂ × ℂ, w.1 ≠ 0 → H₂ w = F (second w)) :
    Tendsto F (𝓝[≠] (0 : ℂ × ℂ)) (𝓝 a) := by
  apply tendsto_def.mpr
  intro V hV
  have he₁ : ∀ᶠ x : ℂ in 𝓝 0, ∀ z ∈ closedBall (0 : ℂ) 1, H₁ (x,z) ∈ V := by
    apply (isCompact_closedBall (0 : ℂ) 1).eventually_forall_of_forall_eventually
    intro z hz
    have ht := (h₁ z hz).tendsto
    rw [hc₁ z hz] at ht
    exact ht.eventually hV
  have he₂ : ∀ᶠ x : ℂ in 𝓝 0, ∀ z ∈ closedBall (0 : ℂ) 1, H₂ (x,z) ∈ V := by
    apply (isCompact_closedBall (0 : ℂ) 1).eventually_forall_of_forall_eventually
    intro z hz
    have ht := (h₂ z hz).tendsto
    rw [hc₂ z hz] at ht
    exact ht.eventually hV
  have hp₁ : ∀ᶠ w : ℂ × ℂ in 𝓝 0, ∀ z ∈ closedBall (0 : ℂ) 1, H₁ (w.1,z) ∈ V :=
    (continuous_fst.tendsto (0 : ℂ × ℂ)).eventually he₁
  have hp₂ : ∀ᶠ w : ℂ × ℂ in 𝓝 0, ∀ z ∈ closedBall (0 : ℂ) 1, H₂ (w.2,z) ∈ V :=
    (continuous_snd.tendsto (0 : ℂ × ℂ)).eventually he₂
  filter_upwards [hp₁.filter_mono nhdsWithin_le_nhds,hp₂.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with w hw₁ hw₂ hw0
  change F w ∈ V
  have hn : w ≠ 0 := hw0
  rcases le_total ‖w.2‖ ‖w.1‖ with hle | hle
  · have hx : w.1 ≠ 0 := by
      intro hx
      apply hn
      have hy : w.2 = 0 := norm_eq_zero.mp (le_antisymm (by simpa only [hx,norm_zero] using hle) (norm_nonneg _))
      exact Prod.ext hx hy
    have hz : w.2 / w.1 ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall_zero_iff,norm_div]
      exact (div_le_one (norm_pos_iff.mpr hx)).mpr hle
    have h := hw₁ (w.2/w.1) hz
    rw [hf₁ (w.1,w.2/w.1) hx] at h
    simpa [first,mul_div_cancel₀ _ hx] using h
  · have hy : w.2 ≠ 0 := by
      intro hy
      apply hn
      have hx : w.1 = 0 := norm_eq_zero.mp (le_antisymm (by simpa only [hy,norm_zero] using hle) (norm_nonneg _))
      exact Prod.ext hx hy
    have hz : w.1 / w.2 ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall_zero_iff,norm_div]
      exact (div_le_one (norm_pos_iff.mpr hy)).mpr hle
    have h := hw₂ (w.1/w.2) hz
    rw [hf₂ (w.2,w.1/w.2) hy] at h
    simpa [second,mul_div_cancel₀ _ hy] using h

end SplitTangent.AffineBlowup

namespace SplitTangent.ProjectiveEmbedding
open Filter Topology
variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)

lemma incidence_zero (x : X.Carrier) : e.Incidence x 0 := by
  intro i j
  simp

end SplitTangent.ProjectiveEmbedding

namespace SplitTangent.TangentSplitting
open Filter Topology
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma WedgeAt.congr {F G : E → X.Carrier} {A B : E → ℂ} {z : E}
    (hW : S.WedgeAt F A z) (hF : F =ᶠ[𝓝 z] G) (hA : A =ᶠ[𝓝 z] B) :
    S.WedgeAt G B z := by
  intro v w
  have hder : mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z =
      mfderiv 𝓘(ℂ,E) (ModelWithCorners X) G z := hF.mfderiv_eq
  rw [← hA.fderiv_eq,← hder,← hF.self_of_nhds]
  exact hW v w
end SplitTangent.TangentSplitting

namespace SplitTangent.PolynomialBlowup
lemma value_sub (p q : P) (w : ℂ × ℂ) : value (p-q) w = value p w - value q w :=
  (valueHom w).map_sub p q

lemma shift_shift (a b : ℂ × ℂ) (p : P) : shift a (shift b p) = shift (a+b) p := by
  have H : (shift a).comp (shift b) = shift (a+b) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [shift] <;> ring
  exact AlgHom.congr_fun H p
lemma shift_zero (p : P) : shift 0 p = p := by
  have H : shift 0 = AlgHom.id ℂ P := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [shift]
  exact AlgHom.congr_fun H p
lemma shift_injective (a : ℂ × ℂ) : Function.Injective (shift a) := by
  intro p q h
  have H := congrArg (shift (-a)) h
  simpa only [shift_shift,neg_add_cancel,shift_zero] using H
lemma polynomial_swap_swap (p : P) : swap (swap p) = p := by
  have H : swap.comp swap = AlgHom.id ℂ P := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [swap]
  exact AlgHom.congr_fun H p
lemma polynomial_swap_injective : Function.Injective swap := by
  intro p q h
  have H := congrArg swap h
  simpa only [polynomial_swap_swap] using H
end SplitTangent.PolynomialBlowup

namespace SplitTangent.AffineBlowup
open Filter Topology Metric
variable {Y : Type*} [TopologicalSpace Y]
lemma tendsto_of_local_constant_exceptional {F G₁ G₂ : ℂ × ℂ → Y} {a : Y}
    (h₁ : ∀ z ∈ closedBall (0 : ℂ) 1, ContinuousAt G₁ (0,z))
    (h₂ : ∀ z ∈ closedBall (0 : ℂ) 1, ContinuousAt G₂ (0,z))
    (hc₁ : ∀ z ∈ closedBall (0 : ℂ) 1, G₁ (0,z) = a)
    (hc₂ : ∀ z ∈ closedBall (0 : ℂ) 1, G₂ (0,z) = a)
    (hf₁ : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ᶠ w in 𝓝 (0,z), w.1 ≠ 0 → G₁ w = F (first w))
    (hf₂ : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ᶠ w in 𝓝 (0,z), w.1 ≠ 0 → G₂ w = F (second w)) :
    Tendsto F (𝓝[≠] (0 : ℂ × ℂ)) (𝓝 a) := by
  classical
  let H₁ : ℂ × ℂ → Y := fun w => if w.1 = 0 then G₁ w else F (first w)
  let H₂ : ℂ × ℂ → Y := fun w => if w.1 = 0 then G₂ w else F (second w)
  have he₁ (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) : H₁ =ᶠ[𝓝 (0,z)] G₁ := by
    filter_upwards [hf₁ z hz] with w hw
    dsimp only [H₁]
    split_ifs with hx
    · rfl
    · exact (hw hx).symm
  have he₂ (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) : H₂ =ᶠ[𝓝 (0,z)] G₂ := by
    filter_upwards [hf₂ z hz] with w hw
    dsimp only [H₂]
    split_ifs with hx
    · rfl
    · exact (hw hx).symm
  apply tendsto_of_constant_exceptional (H₁ := H₁) (H₂ := H₂)
    (fun z hz => (h₁ z hz).congr_of_eventuallyEq (he₁ z hz))
    (fun z hz => (h₂ z hz).congr_of_eventuallyEq (he₂ z hz))
  · intro z hz; simpa only [H₁,ite_eq_left rfl] using hc₁ z hz
  · intro z hz; simpa only [H₂,ite_eq_left rfl] using hc₂ z hz
  · intro w hw; simp only [H₁,ite_eq_right hw]
  · intro w hw; simp only [H₂,ite_eq_right hw]
end SplitTangent.AffineBlowup

namespace SplitTangent.BasePointRemoval
open Filter Topology Set
open PolynomialBlowup
open FormalBlowup (D highOrder polynomialTransform)
variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X) (S : TangentSplitting X)

lemma tuple_analytic (p : Fin (e.N+1) → P) (w : ℂ × ℂ) : AnalyticAt ℂ (tuple e p) w :=
  AnalyticAt.pi (fun i => value_analytic (p i) w)

lemma tuple_child (p : Fin (e.N+1) → P) (k : ℕ) (hI : baseIdeal p ≤ highOrder k)
    (c : ℂ) (w : ℂ × ℂ) :
    tuple e p (w.1,w.1*(w.2+c)) = w.1^k • tuple e (child p k c) w := by
  ext j; exact (child_factor p k hI c j w).symm

lemma lift_holomorphic [CompactSpace X.Carrier] (x₀ : X.Carrier)
    {p : Fin (e.N+1) → P} {z : ℂ × ℂ} (hp : tuple e p z ≠ 0)
    (hc : ∀ᶠ w in 𝓝 z, ∃ x, e.Incidence x (tuple e p w)) :
    ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω (lift e x₀ p) z := by
  apply e.holomorphic_of_incidence (tuple_analytic e p z) hp
  exact hc.mono (fun w hw => e.coneLift_incidence x₀ hw)

lemma frequently_first_ne (z : ℂ × ℂ) : ∃ᶠ w in 𝓝 z, w.1 ≠ 0 := by
  by_cases hz : z.1 = 0
  · have ht : Tendsto (fun r : ℂ => (r,z.2)) (𝓝[≠] 0) (𝓝 z) := by
      have H := (continuousAt_id.prodMk continuousAt_const : ContinuousAt (fun r : ℂ => (r,z.2)) 0)
      simpa only [id_eq,← hz,Prod.mk.eta] using H.mono_left nhdsWithin_le_nhds
    exact ht.frequently (show ∃ᶠ r : ℂ in 𝓝[≠] 0, (r,z.2).1 ≠ 0 from
      Filter.Eventually.frequently self_mem_nhdsWithin)
  · exact (continuous_fst.continuousAt.eventually_ne hz).frequently

lemma blowup_contDiff (c : ℂ) : ContDiff ℂ ω (fun w : ℂ × ℂ => (w.1,w.1*(w.2+c))) :=
  contDiff_fst.prodMk (contDiff_fst.mul (contDiff_snd.add contDiff_const))

lemma cone_child [CompactSpace X.Carrier] {p : Fin (e.N+1) → P} (k : ℕ)
    (hI : baseIdeal p ≤ highOrder k) (c : ℂ)
    (hc : ∀ᶠ w in 𝓝 (0 : ℂ × ℂ), ∃ x, e.Incidence x (tuple e p w)) :
    ∀ᶠ w in 𝓝 (0 : ℂ × ℂ), ∃ x, e.Incidence x (tuple e (child p k c) w) := by
  let β : ℂ × ℂ → ℂ × ℂ := fun w => (w.1,w.1*(w.2+c))
  have hβ : Continuous β := (blowup_contDiff c).continuous
  have h0 : β 0 = 0 := by simp [β]
  have hp := hβ.continuousAt.tendsto.eventually (h0 ▸ hc)
  obtain ⟨U,hUsub,hU,hU0⟩ := _root_.mem_nhds_iff.mp hp
  filter_upwards [hU.mem_nhds hU0] with z hz
  apply e.isClosed_cone.mem_of_frequently_of_tendsto _ (tuple_analytic e (child p k c) z).continuousAt.tendsto
  apply ((frequently_first_ne z).and_eventually (hU.mem_nhds hz)).mono
  intro w hw
  obtain ⟨x,hx⟩ := hUsub hw.2
  rw [tuple_child e p k hI c w] at hx
  exact ⟨x,(e.incidence_smul_iff (pow_ne_zero _ hw.1)).mp hx⟩



lemma value_child_coordinate (A : P) (c : ℂ) :
    value (shift (0,c) (blowup A)) = fun w : ℂ × ℂ => value A (w.1,w.1*(w.2+c)) := by
  funext w
  rw [value_shift,value_blowup]
  simp only [Prod.fst_add,Prod.snd_add,add_zero]

lemma lift_child_eq (x₀ : X.Carrier) {p : Fin (e.N+1) → P} (k : ℕ)
    (hI : baseIdeal p ≤ highOrder k) (c : ℂ) {w : ℂ × ℂ} (hw : w.1 ≠ 0)
    (hc : ∃ x, e.Incidence x (tuple e (child p k c) w)) :
    lift e x₀ (child p k c) w = lift e x₀ p (w.1,w.1*(w.2+c)) := by
  dsimp only [lift]
  rw [tuple_child e p k hI c w,e.coneLift_smul x₀ (pow_ne_zero _ hw) hc]

lemma admissible_child [CompactSpace X.Carrier] (x₀ : X.Carrier)
    {p : Fin (e.N+1) → P} {A B : P} (k : ℕ) (hI : baseIdeal p ≤ highOrder k)
    (c : ℂ) (hp : Admissible e S x₀ p A B) :
    Admissible e S x₀ (child p k c) (shift (0,c) (blowup A)) (shift (0,c) (blowup B)) := by
  have hc := cone_child e k hI c hp.1
  refine ⟨hc,?_⟩
  let β : ℂ × ℂ → ℂ × ℂ := fun w => (w.1,w.1*(w.2+c))
  have hβ : ContDiff ℂ ω β := blowup_contDiff c
  have hβ0 : β 0 = 0 := by simp [β]
  obtain ⟨V,hVsub,hV,hV0⟩ := _root_.mem_nhds_iff.mp (hp.1.and hp.2)
  obtain ⟨U₀,hU₀sub,hU₀,hU₀0⟩ := _root_.mem_nhds_iff.mp hc
  let U := U₀ ∩ β ⁻¹' V
  have hU : IsOpen U := hU₀.inter (hV.preimage hβ.continuous)
  have hU0 : (0 : ℂ × ℂ) ∈ U := ⟨hU₀0,by change β 0 ∈ V; rw [hβ0]; exact hV0⟩
  have hhol (z : ℂ × ℂ) (hz : z ∈ U) (hn : tuple e (child p k c) z ≠ 0) :
      ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω (lift e x₀ (child p k c)) z :=
    lift_holomorphic e x₀ hn (Filter.Eventually.mono (hU₀.mem_nhds hz.1) hU₀sub)
  have hoff (z : ℂ × ℂ) (hz : z ∈ U) (hx : z.1 ≠ 0)
      (hn : tuple e (child p k c) z ≠ 0) :
      S.WedgeAt (lift e x₀ (child p k c)) (value (shift (0,c) (blowup A))) z ∧
      S.swap.WedgeAt (lift e x₀ (child p k c)) (value (shift (0,c) (blowup B))) z := by
    have hnparent : tuple e p (β z) ≠ 0 := by
      rw [tuple_child e p k hI c z]
      exact smul_ne_zero (pow_ne_zero _ hx) hn
    have hFp := lift_holomorphic e x₀ hnparent (Filter.Eventually.mono (hV.mem_nhds hz.2) (fun w hw => (hVsub hw).1))
    have heq : lift e x₀ (child p k c) =ᶠ[𝓝 z] lift e x₀ p ∘ β := by
      filter_upwards [hU₀.mem_nhds hz.1,continuous_fst.continuousAt.eventually_ne hx] with w hw hxw
      exact lift_child_eq e x₀ k hI c hxw (hU₀sub hw)
    have hW := (hVsub hz.2).2 hnparent
    constructor
    · have h := hW.1.comp S hFp (value_analytic A (β z)).differentiableAt (hβ.differentiable (by simp) z)
      apply h.congr S heq.symm
      exact Filter.Eventually.of_forall (fun w => (congrFun (value_child_coordinate A c) w).symm)
    · have h := hW.2.comp S.swap hFp (value_analytic B (β z)).differentiableAt (hβ.differentiable (by simp) z)
      apply h.congr S.swap heq.symm
      exact Filter.Eventually.of_forall (fun w => (congrFun (value_child_coordinate B c) w).symm)
  filter_upwards [hU.mem_nhds hU0] with z hz hn
  have hfreq := (frequently_first_ne z).and_eventually
    (Filter.Eventually.and (hU.mem_nhds hz) ((tuple_analytic e (child p k c) z).continuousAt.eventually_ne hn))
  constructor
  · apply S.wedgeAt_of_frequently (hhol z hz hn) (value_analytic _ z)
    exact hfreq.mono (fun w hw => (hoff w hw.2.1 hw.1 hw.2.2).1)
  · apply S.swap.wedgeAt_of_frequently (hhol z hz hn) (value_analytic _ z)
    exact hfreq.mono (fun w hw => (hoff w hw.2.1 hw.1 hw.2.2).2)

lemma tuple_swap (p : Fin (e.N+1) → P) (w : ℂ × ℂ) :
    tuple e (fun i => swap (p i)) w = tuple e p w.swap := by
  ext i; exact value_swap (p i) w

lemma admissible_swap [CompactSpace X.Carrier] (x₀ : X.Carrier)
    {p : Fin (e.N+1) → P} {A B : P} (hp : Admissible e S x₀ p A B) :
    Admissible e S x₀ (fun i => swap (p i)) (swap A) (swap B) := by
  have hσ : ContDiff ℂ ω (Prod.swap : ℂ × ℂ → ℂ × ℂ) := contDiff_snd.prodMk contDiff_fst
  have h0 : Prod.swap (0 : ℂ × ℂ) = 0 := rfl
  have hq := hσ.continuous.continuousAt.tendsto.eventually (h0 ▸ hp.1)
  refine ⟨?_,?_⟩
  · simpa only [tuple_swap] using hq
  · obtain ⟨U,hUsub,hU,hU0⟩ := _root_.mem_nhds_iff.mp (hp.1.and hp.2)
    have hnear := hσ.continuous.continuousAt.tendsto.eventually (h0 ▸ hU.mem_nhds hU0)
    filter_upwards [hnear] with z hz hn
    rw [tuple_swap] at hn
    have hF := lift_holomorphic e x₀ hn (Filter.Eventually.mono (hU.mem_nhds hz) (fun w hw => (hUsub hw).1))
    have hW := (hUsub hz).2 hn
    have heq : lift e x₀ p ∘ Prod.swap = lift e x₀ (fun i => swap (p i)) := by
      funext w; dsimp only [lift,Function.comp_apply]; rw [tuple_swap]
    have hAe : value A ∘ Prod.swap = value (swap A) := by funext w; exact (value_swap A w).symm
    have hBe : value B ∘ Prod.swap = value (swap B) := by funext w; exact (value_swap B w).symm
    constructor
    · simpa only [heq,hAe] using hW.1.comp S hF (value_analytic A z.swap).differentiableAt (hσ.differentiable (by simp) z)
    · simpa only [heq,hBe] using hW.2.comp S.swap hF (value_analytic B z.swap).differentiableAt (hσ.differentiable (by simp) z)

lemma isolated_swap {p : Fin (e.N+1) → P} (hp : IsolatedAtOrigin p) :
    IsolatedAtOrigin (fun i => swap (p i)) := by
  have ht : Tendsto (Prod.swap : ℂ × ℂ → ℂ × ℂ) (𝓝 0) (𝓝 0) := continuous_swap.continuousAt
  filter_upwards [ht.eventually hp] with w hw hn
  have H := hw (fun i => (value_swap (p i) w).symm.trans (hn i))
  have := congrArg Prod.swap H
  simpa only [Prod.swap_swap,Prod.swap_zero] using this

lemma tuple_shift (p : Fin (e.N+1) → P) (a w : ℂ × ℂ) :
    tuple e (fun i => shift a (p i)) w = tuple e p (w+a) := by
  ext i; exact value_shift (p i) a w

lemma regular_shift_data [CompactSpace X.Carrier] (x₀ : X.Carrier)
    {p : Fin (e.N+1) → P} {A B : P} (a : ℂ × ℂ)
    (hp : Admissible e S x₀ (fun i => shift a (p i)) (shift a A) (shift a B))
    (hn : tuple e (fun i => shift a (p i)) 0 ≠ 0) :
    ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω (lift e x₀ p) a ∧
    ∀ᶠ w in 𝓝 a, S.WedgeAt (lift e x₀ p) (value A) w ∧ S.swap.WedgeAt (lift e x₀ p) (value B) w := by
  let f : ℂ × ℂ → ℂ × ℂ := fun w => w-a
  have hf : ContDiff ℂ ω f := contDiff_id.sub contDiff_const
  have hf0 : f a = 0 := sub_self a
  have hF := lift_holomorphic e x₀ hn hp.1
  have heq : lift e x₀ (fun i => shift a (p i)) ∘ f = lift e x₀ p := by
    funext w
    dsimp only [lift,Function.comp_apply]
    rw [tuple_shift]
    simp only [f,sub_add_cancel]
  have hAe : value (shift a A) ∘ f = value A := by funext w; simp only [Function.comp_apply,value_shift,f,sub_add_cancel]
  have hBe : value (shift a B) ∘ f = value B := by funext w; simp only [Function.comp_apply,value_shift,f,sub_add_cancel]
  constructor
  · rw [← heq]
    exact (hf0 ▸ hF).comp a hf.contMDiff.contMDiffAt
  · have hh := (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hF
    have hnear : ∀ᶠ z in 𝓝 (0 : ℂ × ℂ),
        ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω (lift e x₀ (fun i => shift a (p i))) z ∧
        S.WedgeAt (lift e x₀ (fun i => shift a (p i))) (value (shift a A)) z ∧
        S.swap.WedgeAt (lift e x₀ (fun i => shift a (p i))) (value (shift a B)) z := by
      filter_upwards [hh,hp.2,(tuple_analytic e (fun i => shift a (p i)) 0).continuousAt.eventually_ne hn] with z hz hw hnz
      exact ⟨hz,hw hnz⟩
    filter_upwards [hf.continuous.continuousAt.tendsto.eventually (hf0 ▸ hnear)] with w hw
    constructor
    · simpa only [heq,hAe] using hw.2.1.comp S hw.1 (value_analytic (shift a A) (f w)).differentiableAt (hf.differentiable (by simp) w)
    · simpa only [heq,hBe] using hw.2.2.comp S.swap hw.1 (value_analytic (shift a B) (f w)).differentiableAt (hf.differentiable (by simp) w)

lemma transformed_curve_data [CompactSpace X.Carrier] (x₀ : X.Carrier)
    {p : Fin (e.N+1) → P} {A B : P} (k : ℕ) (hI : baseIdeal p ≤ highOrder k)
    (hp : Admissible e S x₀ p A B)
    (hn : ∀ c : ℂ, tuple e (child p k c) 0 ≠ 0) :
    ∀ c : ℂ,
      ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω (lift e x₀ (fun i => polynomialTransform k (p i))) (0,c) ∧
      ∀ᶠ w in 𝓝 (0,c),
        S.WedgeAt (lift e x₀ (fun i => polynomialTransform k (p i))) (value (blowup A)) w ∧
        S.swap.WedgeAt (lift e x₀ (fun i => polynomialTransform k (p i))) (value (blowup B)) w := by
  intro c
  exact regular_shift_data e S x₀ (0,c) (admissible_child e S x₀ k hI c hp) (hn c)

lemma transformed_curve_constant [CompactSpace X.Carrier] (x₀ : X.Carrier)
    {p : Fin (e.N+1) → P} {A B : P} (k : ℕ) (hI : baseIdeal p ≤ highOrder k)
    (hp : Admissible e S x₀ p A B)
    (hA : A ≠ 0) (hA0 : value A 0 = 0) (hB : B ≠ 0) (hB0 : value B 0 = 0)
    (hn : ∀ c : ℂ, tuple e (child p k c) 0 ≠ 0) (z w : ℂ) :
    lift e x₀ (fun i => polynomialTransform k (p i)) (0,z) =
    lift e x₀ (fun i => polynomialTransform k (p i)) (0,w) := by
  obtain ⟨n,a,ha,hna⟩ := coordinate_exceptional_factor hA hA0
  obtain ⟨m,b,hb,hnb⟩ := coordinate_exceptional_factor hB hB0
  have hea : value (blowup A) = fun w : ℂ × ℂ => w.1^(n+1)*value a w := by
    funext w; rw [ha,value_mul,value_pow,value_X₀]
  have heb : value (blowup B) = fun w : ℂ × ℂ => w.1^(m+1)*value b w := by
    funext w; rw [hb,value_mul,value_pow,value_X₀]
  have hfinite : Set.Finite {z : ℂ | value a (0,z) = 0 ∨ value b (0,z) = 0} := by
    have H := (Polynomial.finite_setOfPred_isRoot hna).union (Polynomial.finite_setOfPred_isRoot hnb)
    simpa only [Set.ofPred_or, Polynomial.IsRoot,linePolynomial_eval] using H
  have hd := transformed_curve_data e S x₀ k hI hp hn
  apply S.constant_exceptional n m (fun c => (hd c).1) (fun c => value_analytic a (0,c))
    (fun c => value_analytic b (0,c)) hfinite _ _ z w
  · intro c
    simpa only [← hea] using (hd c).2.mono (fun w hw => hw.1)
  · intro c
    simpa only [← heb] using (hd c).2.mono (fun w hw => hw.2)

lemma tuple_transformed_factor (p : Fin (e.N+1) → P) (k : ℕ) (hI : baseIdeal p ≤ highOrder k)
    (w : ℂ × ℂ) : tuple e p (AffineBlowup.first w) =
      w.1^k • tuple e (fun i => polynomialTransform k (p i)) w := by
  have hc : child p k 0 = fun i => polynomialTransform k (p i) := by
    funext i; exact shift_zero _
  simpa only [hc,add_zero,AffineBlowup.first] using tuple_child e p k hI 0 w

lemma transformed_lift_near (x₀ : X.Carrier) {p : Fin (e.N+1) → P}
    (k : ℕ) (hI : baseIdeal p ≤ highOrder k)
    (hc : ∀ᶠ w in 𝓝 (0 : ℂ × ℂ), ∃ x, e.Incidence x (tuple e p w)) (c : ℂ) :
    ∀ᶠ w in 𝓝 (0,c), w.1 ≠ 0 →
      lift e x₀ (fun i => polynomialTransform k (p i)) w = lift e x₀ p (AffineBlowup.first w) := by
  have ht : Tendsto AffineBlowup.first (𝓝 (0,c)) (𝓝 (0 : ℂ × ℂ)) := by
    change Tendsto (fun w : ℂ × ℂ => (w.1,w.1*w.2)) _ _
    simpa only [AffineBlowup.first,Pi.mul_apply,Prod.fst,Prod.snd,zero_mul,Prod.mk_zero_zero] using
      (continuous_fst.prodMk (continuous_fst.mul continuous_snd)).tendsto ((0,c) : ℂ × ℂ)
  filter_upwards [ht.eventually hc] with w hw hx
  have hd := tuple_transformed_factor e p k hI w
  have hc' : ∃ x, e.Incidence x (tuple e (fun i => polynomialTransform k (p i)) w) := by
    obtain ⟨x,hh⟩ := hw
    rw [hd] at hh
    exact ⟨x,(e.incidence_smul_iff (pow_ne_zero _ hx)).mp hh⟩
  dsimp only [lift]
  rw [hd,e.coneLift_smul x₀ (pow_ne_zero _ hx) hc']

lemma lift_swap (x₀ : X.Carrier) (p : Fin (e.N+1) → P) (w : ℂ × ℂ) :
    lift e x₀ (fun i => swap (p i)) w = lift e x₀ p w.swap := by
  dsimp only [lift]; rw [tuple_swap]

 

theorem nonzero_of_regular_children [CompactSpace X.Carrier] (x₀ : X.Carrier)
    {p : Fin (e.N+1) → P} {A B : P} (k : ℕ) (hI : baseIdeal p ≤ highOrder k)
    (hIs : baseIdeal (fun i => swap (p i)) ≤ highOrder k)
    (hp : Admissible e S x₀ p A B) (hiso : IsolatedAtOrigin p)
    (hA : A ≠ 0) (hA0 : value A 0 = 0) (hB : B ≠ 0) (hB0 : value B 0 = 0)
    (hn₁ : ∀ c : ℂ, tuple e (child p k c) 0 ≠ 0)
    (hn₂ : ∀ c : ℂ, tuple e (child (fun i => swap (p i)) k c) 0 ≠ 0) : tuple e p 0 ≠ 0 := by
  classical
  let ps : Fin (e.N+1) → P := fun i => swap (p i)
  let G₁ := lift e x₀ (fun i => polynomialTransform k (p i))
  let G₂ := lift e x₀ (fun i => polynomialTransform k (ps i))
  have hs := admissible_swap e S x₀ hp
  have hA' : swap A ≠ 0 := fun h => hA (polynomial_swap_injective (h.trans (map_zero swap).symm))
  have hB' : swap B ≠ 0 := fun h => hB (polynomial_swap_injective (h.trans (map_zero swap).symm))
  have hA0' : value (swap A) 0 = 0 := by simpa only [value_swap,Prod.fst_zero,Prod.snd_zero,Prod.mk_zero_zero] using hA0
  have hB0' : value (swap B) 0 = 0 := by simpa only [value_swap,Prod.fst_zero,Prod.snd_zero,Prod.mk_zero_zero] using hB0
  have hg₁ (z : ℂ) : ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω G₁ (0,z) :=
    (transformed_curve_data e S x₀ k hI hp hn₁ z).1
  have hg₂ (z : ℂ) : ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω G₂ (0,z) :=
    (transformed_curve_data e S x₀ k hIs hs hn₂ z).1
  have hc₁ (z w : ℂ) : G₁ (0,z) = G₁ (0,w) :=
    transformed_curve_constant e S x₀ k hI hp hA hA0 hB hB0 hn₁ z w
  have hc₂ (z w : ℂ) : G₂ (0,z) = G₂ (0,w) :=
    transformed_curve_constant e S x₀ k hIs hs hA' hA0' hB' hB0' hn₂ z w
  have hf₁ (z : ℂ) : ∀ᶠ w in 𝓝 (0,z), w.1 ≠ 0 → G₁ w = lift e x₀ p (AffineBlowup.first w) :=
    transformed_lift_near e x₀ k hI hp.1 z
  have hf₂ (z : ℂ) : ∀ᶠ w in 𝓝 (0,z), w.1 ≠ 0 → G₂ w = lift e x₀ p (AffineBlowup.second w) := by
    filter_upwards [transformed_lift_near e x₀ k hIs hs.1 z] with w hw hx
    change lift e x₀ (fun i => polynomialTransform k (swap (p i))) w = _
    rw [hw hx,lift_swap]
    rfl
  have hcommon : G₁ (0,1) = G₂ (0,1) := by
    have ht : Tendsto (fun r : ℂ => (r,1)) (𝓝[≠] 0) (𝓝 ((0,1) : ℂ × ℂ)) :=
      (continuousAt_id.prodMk continuousAt_const).mono_left nhdsWithin_le_nhds
    apply tendsto_nhds_unique_of_eventuallyEq ((hg₁ 1).continuousAt.tendsto.comp ht)
      ((hg₂ 1).continuousAt.tendsto.comp ht)
    filter_upwards [ht.eventually (hf₁ 1),ht.eventually (hf₂ 1),self_mem_nhdsWithin] with r hr₁ hr₂ hr
    dsimp only [Function.comp_apply]
    rw [hr₁ hr,hr₂ hr]
    simp only [AffineBlowup.first,AffineBlowup.second,mul_one]
  have hlim : Tendsto (lift e x₀ p) (𝓝[≠] (0 : ℂ × ℂ)) (𝓝 (G₁ (0,0))) := by
    apply AffineBlowup.tendsto_of_local_constant_exceptional
      (fun z _ => (hg₁ z).continuousAt) (fun z _ => (hg₂ z).continuousAt)
      (fun z _ => hc₁ z 0) (fun z _ => (hc₂ z 1).trans (hcommon.symm.trans (hc₁ 1 0)))
      (fun z _ => hf₁ z) (fun z _ => hf₂ z)
  let F := Function.update (lift e x₀ p) 0 (G₁ (0,0))
  have hF : ContinuousAt F 0 := continuousAt_update_same.mpr hlim
  have heq : F =ᶠ[𝓝[≠] (0 : ℂ × ℂ)] lift e x₀ p := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact Function.update_of_ne hw _ _
  apply e.nonzero_of_continuous_incidence (tuple_analytic e p 0) hF
  · filter_upwards [hiso.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w hw hn hz
    exact hn (hw (fun i => congrFun hz i))
  · filter_upwards [hp.1.filter_mono nhdsWithin_le_nhds,heq] with w hw he
    rw [he]
    exact e.coneLift_incidence x₀ hw

lemma child_coordinate_nonzero {A : P} (hA : A ≠ 0) (c : ℂ) :
    shift (0,c) (blowup A) ≠ 0 := by
  intro h
  apply hA
  apply blowup_injective
  apply shift_injective (0,c)
  simpa only [map_zero] using h

lemma child_coordinate_origin {A : P} (hA : value A 0 = 0) (c : ℂ) :
    value (shift (0,c) (blowup A)) 0 = 0 := by
  simpa only [value_shift,zero_add,value_blowup,Prod.fst,Prod.snd,zero_mul,Prod.mk_zero_zero] using hA

lemma swap_child_isolated {p : Fin (e.N+1) → P} (k : ℕ)
    (hI : baseIdeal p ≤ highOrder k) (f : baseIdeal p)
    (a b : ℕ) (hab : a+b=k) (hf : MvPowerSeries.coeff (FormalBlowup.exp a b) (f : D) ≠ 0)
    (hp : IsolatedAtOrigin p) (c : ℂ) : IsolatedAtOrigin (child (fun i => swap (p i)) k c) := by
  have hs : baseIdeal (fun i => swap (p i)) ≤ highOrder k := by
    rw [← swap_baseIdeal]
    exact FormalBlowup.swapIdeal_le_highOrder _ k hI
  have hm : FormalBlowup.swap (f : D) ∈ baseIdeal (fun i => swap (p i)) := by
    rw [← swap_baseIdeal]
    exact Ideal.mem_map_of_mem _ f.property
  have ho : (FormalBlowup.swap (f : D)).order = k := by
    rw [FormalBlowup.order_swap]
    exact FormalBlowup.order_eq_of_initial k f (hI f.property) a b hab hf
  obtain ⟨a',b',hab',hf'⟩ := FormalBlowup.initial_of_order_eq k _ ho
  exact child_isolated _ k hs ⟨_,hm⟩ a' b' hab' hf' (isolated_swap e hp) c

 

theorem no_basepoint [CompactSpace X.Carrier] (x₀ : X.Carrier)
    (p : Fin (e.N+1) → P) [FiniteDimensional ℂ (D ⧸ baseIdeal p)]
    (A B : P) (hp : Admissible e S x₀ p A B) (hiso : IsolatedAtOrigin p)
    (hA : A ≠ 0) (hA0 : value A 0 = 0) (hB : B ≠ 0) (hB0 : value B 0 = 0) :
    tuple e p 0 ≠ 0 := by
  classical
  generalize hn : Module.finrank ℂ (D ⧸ baseIdeal p) = n
  induction n using Nat.strong_induction_on generalizing p A B with
  | h n ih =>
    by_cases ht : baseIdeal p = ⊤
    · obtain ⟨i,hi⟩ := (baseIdeal_eq_top_iff p).mp ht
      exact fun h => hi (congrFun h i)
    · obtain ⟨k,hk,hI,f,a,b,hab,hf⟩ := FormalBlowup.exists_minimal_order (baseIdeal p) ht
      have hs : baseIdeal (fun i => swap (p i)) ≤ highOrder k := by
        rw [← swap_baseIdeal]
        exact FormalBlowup.swapIdeal_le_highOrder _ k hI
      apply nonzero_of_regular_children e S x₀ k hI hs hp hiso hA hA0 hB hB0
      · intro c
        obtain ⟨hfin,hlt⟩ := child_finite_drop p k hk hI f a b hab hf c
        let := hfin
        apply ih _ (by omega) (child p k c) (shift (0,c) (blowup A)) (shift (0,c) (blowup B))
          (admissible_child e S x₀ k hI c hp) (child_isolated p k hI f a b hab hf hiso c)
          (child_coordinate_nonzero hA c) (child_coordinate_origin hA0 c)
          (child_coordinate_nonzero hB c) (child_coordinate_origin hB0 c) rfl
      · intro c
        obtain ⟨hfin,hlt⟩ := swap_child_finite_drop p k hk hI f a b hab hf c
        let := hfin
        have hA' : swap A ≠ 0 := fun h => hA (polynomial_swap_injective (h.trans (map_zero swap).symm))
        have hB' : swap B ≠ 0 := fun h => hB (polynomial_swap_injective (h.trans (map_zero swap).symm))
        have hA0' : value (swap A) 0 = 0 := by simpa only [value_swap,Prod.fst_zero,Prod.snd_zero,Prod.mk_zero_zero] using hA0
        have hB0' : value (swap B) 0 = 0 := by simpa only [value_swap,Prod.fst_zero,Prod.snd_zero,Prod.mk_zero_zero] using hB0
        apply ih _ (by omega) (child (fun i => swap (p i)) k c)
          (shift (0,c) (blowup (swap A))) (shift (0,c) (blowup (swap B)))
          (admissible_child e S x₀ k hs c (admissible_swap e S x₀ hp))
          (swap_child_isolated e k hI f a b hab hf hiso c)
          (child_coordinate_nonzero hA' c) (child_coordinate_origin hA0' c)
          (child_coordinate_nonzero hB' c) (child_coordinate_origin hB0' c) rfl

 

theorem nonzero_everywhere [CompactSpace X.Carrier] (x₀ : X.Carrier)
    (p : Fin (e.N+1) → P) (A B : P)
    (hB : Set.Finite {w : ℂ × ℂ | ∀ j, value (p j) w = 0})
    (hcone : ∀ w, ∃ x, e.Incidence x (tuple e p w))
    (hreg : ∀ w, tuple e p w ≠ 0 →
      S.WedgeAt (lift e x₀ p) (value A) w ∧ S.swap.WedgeAt (lift e x₀ p) (value B) w)
    (hA : ∀ c : ℂ, A ≠ MvPolynomial.C c) (hB' : ∀ c : ℂ, B ≠ MvPolynomial.C c)
    (a : ℂ × ℂ) : tuple e p a ≠ 0 := by
  let p' := fun i => shift a (p i)
  let A' := shift a (A - MvPolynomial.C (value A a))
  let B' := shift a (B - MvPolynomial.C (value B a))
  have hfin := finite_zeros_shift p hB a
  let := finite_colength_of_finite_zeros p' hfin
  have hi : IsolatedAtOrigin p' := finite_isolated hfin 0
  let β : ℂ × ℂ → ℂ × ℂ := fun w => w+a
  have hβ : ContDiff ℂ ω β := contDiff_id.add contDiff_const
  have hF : lift e x₀ p' = lift e x₀ p ∘ β := by
    funext w; dsimp only [lift,Function.comp_apply,β,p']; rw [tuple_shift]
  have hAeq : value A' = (fun w => value A w - value A a) ∘ β := by
    funext w; simp only [A',Function.comp_apply,β,value_shift,value_sub,value_C]
  have hBeq : value B' = (fun w => value B w - value B a) ∘ β := by
    funext w; simp only [B',Function.comp_apply,β,value_shift,value_sub,value_C]
  have had : Admissible e S x₀ p' A' B' := by
    refine ⟨Filter.Eventually.of_forall ?_,Filter.Eventually.of_forall ?_⟩
    · intro w; simpa only [p',tuple_shift] using hcone (w+a)
    · intro w hw
      have hn : tuple e p (β w) ≠ 0 := by simpa only [p',tuple_shift,β] using hw
      have hh := hreg (β w) hn
      have hhol := lift_holomorphic e x₀ hn (Filter.Eventually.of_forall hcone)
      have hwa : S.WedgeAt (lift e x₀ p) (fun w => value A w - value A a) (β w) := by
        simpa only [TangentSplitting.WedgeAt,fderiv_sub_const] using hh.1
      have hwb : S.swap.WedgeAt (lift e x₀ p) (fun w => value B w - value B a) (β w) := by
        simpa only [TangentSplitting.WedgeAt,fderiv_sub_const] using hh.2
      rw [hF,hAeq,hBeq]
      exact ⟨hwa.comp S hhol ((value_analytic A _).differentiableAt.sub_const _) (hβ.differentiable (by simp) w),
        hwb.comp S.swap hhol ((value_analytic B _).differentiableAt.sub_const _) (hβ.differentiable (by simp) w)⟩
  have hAn : A' ≠ 0 := by
    intro hz
    exact hA _ (sub_eq_zero.mp (shift_injective a (hz.trans (map_zero (shift a)).symm)))
  have hBn : B' ≠ 0 := by
    intro hz
    exact hB' _ (sub_eq_zero.mp (shift_injective a (hz.trans (map_zero (shift a)).symm)))
  have hA0 : value A' 0 = 0 := by rw [hAeq]; simp only [Function.comp_apply,β,zero_add,sub_self]
  have hB0 : value B' 0 = 0 := by rw [hBeq]; simp only [Function.comp_apply,β,zero_add,sub_self]
  have hh := no_basepoint e S x₀ p' A' B' had hi hAn hA0 hBn hB0
  simpa only [p',tuple_shift,zero_add] using hh

end SplitTangent.BasePointRemoval

namespace SplitTangent.TangentSplitting
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

lemma wedges_of_pde {F : ℂ × ℂ → X.Carrier} {z : ℂ × ℂ}
    (hpde : mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F z (0,1) =
      S.projector (F z) (mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F z (1,0))) :
    S.WedgeAt F (fun w => w.1+w.2) z ∧ S.swap.WedgeAt F Prod.fst z := by
  let d : (ℂ × ℂ) →L[ℂ] TangentSpace (ModelWithCorners X) (F z) :=
    mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F z
  have hde : d (0,1) = S.projector (F z) (d (1,0)) := hpde
  have hd (w : ℂ × ℂ) : d w = w.1 • d (1,0) + w.2 • d (0,1) := by
    have hw : w = w.1 • (1,0) + w.2 • (0,1) := by ext <;> simp
    conv_lhs => rw [hw]
    rw [map_add,map_smul,map_smul]
  have hp (w : ℂ × ℂ) : S.projector (F z) (d w) =
      (w.1+w.2) • S.projector (F z) (d (1,0)) := by
    rw [hd,map_add,map_smul,map_smul,hde,S.idempotent,add_smul]
  have hq (w : ℂ × ℂ) : S.swap.projector (F z) (d w) =
      w.1 • S.swap.projector (F z) (d (1,0)) := by
    change d w - S.projector (F z) (d w) = w.1 • (d (1,0) - S.projector (F z) (d (1,0)))
    rw [hp,hd,hde,add_smul,smul_sub]
    abel
  have hda : fderiv ℂ (fun w : ℂ × ℂ => w.1+w.2) z =
      ContinuousLinearMap.fst ℂ ℂ ℂ + ContinuousLinearMap.snd ℂ ℂ ℂ :=
    (hasFDerivAt_fst.add hasFDerivAt_snd).fderiv
  have hdb : fderiv ℂ (Prod.fst : ℂ × ℂ → ℂ) z = ContinuousLinearMap.fst ℂ ℂ ℂ :=
    hasFDerivAt_fst.fderiv
  constructor
  · intro v w
    change fderiv ℂ (fun w : ℂ × ℂ => w.1+w.2) z v • S.projector (F z) (d w) =
      fderiv ℂ (fun w : ℂ × ℂ => w.1+w.2) z w • S.projector (F z) (d v)
    rw [hda,hp w,hp v]
    change (v.1+v.2) • ((w.1+w.2) • _) = (w.1+w.2) • ((v.1+v.2) • _)
    rw [smul_smul,smul_smul,mul_comm]
  · intro v w
    change fderiv ℂ (Prod.fst : ℂ × ℂ → ℂ) z v • S.swap.projector (F z) (d w) =
      fderiv ℂ (Prod.fst : ℂ × ℂ → ℂ) z w • S.swap.projector (F z) (d v)
    rw [hdb,hq w,hq v]
    change v.1 • (w.1 • _) = w.1 • (v.1 • _)
    rw [smul_smul,smul_smul,mul_comm]

end SplitTangent.TangentSplitting

namespace SplitTangent.ComplexManifold
open Filter Topology
variable {X : ComplexManifold.{u}}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma equality_local_equations {F G : E → X.Carrier} {z : E}
    (hF : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z)
    (hG : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω G z) :
    ∃ f : E → ℂ × Model X, AnalyticAt ℂ f z ∧
      ∀ᶠ w in 𝓝 z, F w = G w ↔ f w = 0 := by
  classical
  by_cases he : F z = G z
  · let c := chartAt (Model X) (F z)
    have hFc : F z ∈ c.source := mem_chart_source (Model X) (F z)
    have hGc : G z ∈ c.source := he ▸ hFc
    have hc := IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) (F z)
    have hFA := ((contMDiffAt_of_mem_maximalAtlas hc hFc).comp z hF).contDiffAt.analyticAt
    have hGA := ((contMDiffAt_of_mem_maximalAtlas hc hGc).comp z hG).contDiffAt.analyticAt
    refine ⟨fun w => (0,c (F w)-c (G w)), analyticAt_const.prod (hFA.sub hGA),?_⟩
    filter_upwards [hF.continuousAt.eventually (c.open_source.mem_nhds hFc),
      hG.continuousAt.eventually (c.open_source.mem_nhds hGc)] with w hwF hwG
    constructor
    · intro h; simp only [h,sub_self,Prod.zero_eq_mk]
    · intro h
      have hh := congrArg Prod.snd h
      exact c.injOn hwF hwG (sub_eq_zero.mp hh)
  · refine ⟨fun _ => (1,0),analyticAt_const,?_⟩
    have hn : ∀ᶠ w in 𝓝 z, F w ≠ G w :=
      (hF.continuousAt.prodMk hG.continuousAt).eventually
        (isClosed_diagonal.isOpen_compl.mem_nhds he)
    filter_upwards [hn] with w hw
    simp only [hw,Prod.zero_eq_mk,Prod.mk.injEq,one_ne_zero,false_and]

 
theorem eqOn_of_eventuallyEq {F G : E → X.Carrier} {U : Set E}
    (hU : IsPreconnected U)
    (hF : ∀ z ∈ U, ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z)
    (hG : ∀ z ∈ U, ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω G z)
    {a : E} (ha : a ∈ U) (he : F =ᶠ[𝓝 a] G) : Set.EqOn F G U := by
  exact AnalyticContinuation.subset_of_local_analytic_equations hU
    (fun z hz => equality_local_equations (hF z hz) (hG z hz))
    ⟨a,ha,mem_interior_iff_mem_nhds.mpr he⟩

end SplitTangent.ComplexManifold

namespace SplitTangent.RationalSurface
open PolynomialBlowup

lemma value_toMv (p : B) (w : ℂ × ℂ) : value (toMv p) w = eval p w := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [toMv,value,valueHom,eval,map_add] using congrArg₂ (· + ·) hp hq
  | monomial n p =>
    simp only [toMv,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_monomial,eval,
      value,valueHom,map_mul,map_pow,MvPolynomial.aeval_X,Matrix.cons_val_one,Matrix.cons_val_zero]
    congr 1
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [Polynomial.eval₂_add,map_add] using congrArg₂ (· + ·) hp hq
    | monomial m c => simp

end SplitTangent.RationalSurface

namespace SplitTangent.TangentSplitting
section
open Filter Topology PolynomialBlowup BasePointRemoval
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem exists_affine_polynomial_tangent_box [CompactSpace X.Carrier]
    (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ (z : ℂ) (P : Fin (e.N+1) → Polynomial (Polynomial ℂ)) (F : ℂ × ℂ → X.Carrier),
      (∀ w, (fun j => RationalSurface.eval (P j) w) ≠ 0) ∧
      (∀ w, e.Incidence (F w) (fun j => RationalSurface.eval (P j) w)) ∧
      ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F ∧
      (∀ᶠ u in 𝓝 z, F (u,0) = g.finite u) ∧
      (∀ w, mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (0,1) =
        S.projector (F w) (mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (1,0))) := by
  classical
  obtain ⟨z,P,F,hP,hB,hz,hdiag,hF⟩ := S.exists_global_regular_tangent_box e g
  let p := fun j => RationalSurface.toMv (P j)
  let x₀ := g.finite z
  let G := lift e x₀ p
  have htuple (w : ℂ × ℂ) : tuple e p w = fun j => RationalSurface.eval (P j) w := by
    funext j; exact RationalSurface.value_toMv (P j) w
  have hfinite : Set.Finite {w : ℂ × ℂ | ∀ j, value (p j) w = 0} := by
    simpa only [p,RationalSurface.value_toMv] using hB
  have hne (w : ℂ × ℂ) : tuple e p w ≠ 0 ↔ ∃ j, RationalSurface.eval (P j) w ≠ 0 := by
    simp only [htuple,ne_eq,funext_iff,Pi.zero_apply,not_forall]
  have hcone (w : ℂ × ℂ) : ∃ x, e.Incidence x (tuple e p w) := by
    by_cases hw : tuple e p w = 0
    · exact ⟨x₀,hw ▸ e.incidence_zero x₀⟩
    · exact ⟨F w,htuple w ▸ (hF w ((hne w).mp hw)).2.1⟩
  have hagree (w : ℂ × ℂ) (hw : tuple e p w ≠ 0) : G =ᶠ[𝓝 w] F := by
    filter_upwards [(tuple_analytic e p w).continuousAt.eventually_ne hw] with a ha
    exact e.coneLift_eq x₀ ha (htuple a ▸ (hF a ((hne a).mp ha)).2.1)
  have hreg (w : ℂ × ℂ) (hw : tuple e p w ≠ 0) :
      S.WedgeAt G (fun a => a.1+a.2) w ∧ S.swap.WedgeAt G Prod.fst w := by
    have he := hagree w hw
    apply S.wedges_of_pde
    rw [he.mfderiv_eq,he.self_of_nhds]
    exact (hF w ((hne w).mp hw)).2.2
  let A : PolynomialBlowup.P := MvPolynomial.X 0 + MvPolynomial.X 1
  let B : PolynomialBlowup.P := MvPolynomial.X 0
  have hA : value A = fun w : ℂ × ℂ => w.1+w.2 := by funext w; simp [A,value,valueHom]
  have hBB : value B = Prod.fst := by funext w; simp [B,value,valueHom]
  have hAnc (c : ℂ) : A ≠ MvPolynomial.C c := by
    intro he
    have h0 : (0 : ℂ) = c := by simpa [A,value,valueHom] using congrArg (fun q => value q (0,0)) he
    have h1 : (1 : ℂ) = c := by simpa [A,value,valueHom] using congrArg (fun q => value q (1,0)) he
    exact one_ne_zero (h1.trans h0.symm)
  have hBnc (c : ℂ) : B ≠ MvPolynomial.C c := by
    intro he
    have h0 : (0 : ℂ) = c := by simpa [B,value,valueHom] using congrArg (fun q => value q (0,0)) he
    have h1 : (1 : ℂ) = c := by simpa [B,value,valueHom] using congrArg (fun q => value q (1,0)) he
    exact one_ne_zero (h1.trans h0.symm)
  have hnonzero (w : ℂ × ℂ) : tuple e p w ≠ 0 :=
    nonzero_everywhere e S x₀ p A B hfinite hcone (by simpa only [hA,hBB] using hreg) hAnc hBnc w
  refine ⟨z,P,G,?_,?_,?_,?_,?_⟩
  · intro w; simpa only [htuple] using hnonzero w
  · intro w; exact htuple w ▸ e.coneLift_incidence x₀ (hcone w)
  · exact fun w => lift_holomorphic e x₀ (hnonzero w) (Filter.Eventually.of_forall hcone)
  · have he (u : ℂ) : G (u,0) = F (u,0) := (hagree (u,0) (hnonzero _)).self_of_nhds
    simpa only [he] using hdiag
  · intro w
    have he := hagree w (hnonzero w)
    rw [he.mfderiv_eq,he.self_of_nhds]
    exact (hF w ((hne w).mp (hnonzero w))).2.2

end

open Filter Topology

end SplitTangent.TangentSplitting

namespace SplitTangent.RationalSurface
open Polynomial


lemma RationalOn.const (U : Set (ℂ × ℂ)) (c : ℂ) : RationalOn U (fun _ => c) := by
  refine ⟨C (C c),1,?_⟩
  intro w hw; simp [eval]

lemma RationalOn.add {U : Set (ℂ × ℂ)} {f g : ℂ × ℂ → ℂ}
    (hf : RationalOn U f) (hg : RationalOn U g) : RationalOn U (fun w => f w + g w) := by
  obtain ⟨A,D,hf⟩ := hf
  obtain ⟨A',D',hg⟩ := hg
  refine ⟨A*D'+A'*D,D*D',?_⟩
  intro w hw
  obtain ⟨hn,he⟩ := hf w hw
  obtain ⟨hn',he'⟩ := hg w hw
  simp only [eval₂_mul,eval₂_add,eval]
  change eval D w * eval D' w ≠ 0 ∧
    (f w+g w)*(eval D w*eval D' w) = eval A w*eval D' w+eval A' w*eval D w
  exact ⟨mul_ne_zero hn hn',by rw [← he,← he']; ring⟩

lemma RationalOn.neg {U : Set (ℂ × ℂ)} {f : ℂ × ℂ → ℂ}
    (hf : RationalOn U f) : RationalOn U (fun w => -f w) := by
  obtain ⟨A,D,hf⟩ := hf
  refine ⟨-A,D,?_⟩
  intro w hw
  exact ⟨(hf w hw).1,by simpa only [eval,eval₂_neg,neg_mul] using congrArg Neg.neg (hf w hw).2⟩

lemma RationalOn.sub {U : Set (ℂ × ℂ)} {f g : ℂ × ℂ → ℂ}
    (hf : RationalOn U f) (hg : RationalOn U g) : RationalOn U (fun w => f w-g w) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma RationalOn.mul {U : Set (ℂ × ℂ)} {f g : ℂ × ℂ → ℂ}
    (hf : RationalOn U f) (hg : RationalOn U g) : RationalOn U (fun w => f w*g w) := by
  obtain ⟨A,D,hf⟩ := hf
  obtain ⟨A',D',hg⟩ := hg
  refine ⟨A*A',D*D',?_⟩
  intro w hw
  have he := (hf w hw).2
  have he' := (hg w hw).2
  refine ⟨by simpa only [eval,eval₂_mul] using mul_ne_zero (hf w hw).1 (hg w hw).1,?_⟩
  simp only [eval,eval₂_mul]
  change (f w*g w)*(eval D w*eval D' w) = eval A w*eval A' w
  rw [← he,← he']; ring

lemma RationalOn.inv {U : Set (ℂ × ℂ)} {f : ℂ × ℂ → ℂ}
    (hf : RationalOn U f) (hn : ∀ w ∈ U, f w ≠ 0) : RationalOn U (fun w => (f w)⁻¹) := by
  obtain ⟨A,D,hf⟩ := hf
  refine ⟨D,A,?_⟩
  intro w hw
  rw [← (hf w hw).2]
  exact ⟨mul_ne_zero (hn w hw) (hf w hw).1,by rw [← mul_assoc,inv_mul_cancel₀ (hn w hw),one_mul]⟩

lemma rational_polynomial_eval₂ {R' : Type*} [Semiring R'] {U : Set (ℂ × ℂ)}
    (H : (ℂ × ℂ) → R' →+* ℂ) (g : ℂ × ℂ → ℂ)
    (hH : ∀ a, RationalOn U (fun w => H w a)) (hg : RationalOn U g) (p : Polynomial R') :
    RationalOn U (fun w => p.eval₂ (H w) (g w)) := by
  induction p using Polynomial.induction_on with
  | C a => simpa only [Polynomial.eval₂_C] using hH a
  | add p q hp hq => simpa only [eval₂_add] using hp.add hq
  | monomial n a hp =>
      simpa only [pow_succ,← mul_assoc,eval₂_mul,Polynomial.eval₂_X] using hp.mul hg

lemma RationalOn.eval_comp {U : Set (ℂ × ℂ)} {f g : ℂ × ℂ → ℂ}
    (hf : RationalOn U f) (hg : RationalOn U g) (p : B) :
    RationalOn U (fun w => eval p (f w,g w)) := by
  apply rational_polynomial_eval₂ (fun w => Polynomial.evalRingHom (f w)) g _ hg p
  intro a
  exact rational_polynomial_eval₂ (fun _ => RingHom.id ℂ) f (RationalOn.const U) hf a

 

theorem primitive_tuple_of_rational {ι : Type*} [Fintype ι] [Nonempty ι]
    {U : Set (ℂ × ℂ)} (V : ℂ × ℂ → ι → ℂ)
    (hV : ∀ j, RationalOn U (fun w => V w j)) (hn : ∀ w ∈ U, V w ≠ 0) :
    ∃ p : ι → B, Finset.univ.gcd p = 1 ∧
      Set.Finite {w : ℂ × ℂ | ∀ j, eval (p j) w = 0} ∧
      ∀ w ∈ U, ∃ c : ℂ, c ≠ 0 ∧ (fun j => eval (p j) w) = c • V w := by
  classical
  choose A D hD using hV
  let q : ι → B := fun j => A j * ∏ i ∈ Finset.univ.erase j, D i
  obtain ⟨p,hp,hpg⟩ := Finset.extract_gcd q Finset.univ_nonempty
  let d := Finset.univ.gcd q
  have he (j : ι) (w : ℂ × ℂ) : eval (q j) w = eval d w * eval (p j) w := by
    rw [hp j (Finset.mem_univ j)]; exact eval₂_mul _ _
  refine ⟨p,hpg,finite_zero_set p hpg,?_⟩
  intro w hw
  let r := ∏ i, eval (D i) w
  have hr : r ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (hD i w hw).1)
  have hq (j : ι) : eval (q j) w = r * V w j := by
    have hprod := Finset.mul_prod_erase Finset.univ (fun i => eval (D i) w) (Finset.mem_univ j)
    dsimp only [q]
    simp only [eval,eval₂_mul,eval₂_finsetProd]
    change eval (A j) w * (∏ i ∈ Finset.univ.erase j, eval (D i) w) = r * V w j
    rw [← (hD j w hw).2]
    calc
      V w j * eval (D j) w * (∏ i ∈ Finset.univ.erase j, eval (D i) w) =
        V w j * r := by rw [mul_assoc,hprod]
      _ = r * V w j := mul_comm _ _
  have hd : eval d w ≠ 0 := by
    intro hz
    apply hn w hw
    funext j
    have hh := (he j w).symm.trans (hq j)
    change V w j = 0
    apply (mul_eq_zero.mp (by simpa only [hz,zero_mul] using hh.symm)).resolve_left hr
  refine ⟨r / eval d w,div_ne_zero hr hd,?_⟩
  funext j
  change eval (p j) w = (r / eval d w) * V w j
  apply mul_left_cancel₀ hd
  rw [← he,hq]
  field_simp

end SplitTangent.RationalSurface

namespace SplitTangent.TangentSplitting
open Filter Topology Set PolynomialBlowup BasePointRemoval
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

lemma wedges_iff_tangency {F : ℂ × ℂ → X.Carrier} {z : ℂ × ℂ} :
    (S.WedgeAt F Prod.fst z ∧ S.swap.WedgeAt F Prod.snd z) ↔
    (mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F z (1,0) ∈ S.first (F z) ∧
     mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F z (0,1) ∈ S.second (F z)) := by
  let d : (ℂ × ℂ) →L[ℂ] Tangent X (F z) := mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F z
  have hdf : fderiv ℂ (Prod.fst : ℂ × ℂ → ℂ) z = ContinuousLinearMap.fst ℂ ℂ ℂ := hasFDerivAt_fst.fderiv
  have hds : fderiv ℂ (Prod.snd : ℂ × ℂ → ℂ) z = ContinuousLinearMap.snd ℂ ℂ ℂ := hasFDerivAt_snd.fderiv
  have hd (w : ℂ × ℂ) : d w = w.1 • d (1,0) + w.2 • d (0,1) := by
    have hw : w = w.1 • (1,0) + w.2 • (0,1) := by ext <;> simp
    conv_lhs => rw [hw]
    rw [map_add,map_smul,map_smul]
  constructor
  · intro h
    have ht := h.1 (1,0) (0,1)
    have hs := h.2 (0,1) (1,0)
    simp only [hdf,ContinuousLinearMap.coe_fst',one_smul,zero_smul] at ht
    simp only [hds,ContinuousLinearMap.coe_snd',one_smul,zero_smul] at hs
    refine ⟨?_,ht⟩
    change ∃ v, S.projector (F z) v = d (1,0)
    refine ⟨d (1,0),?_⟩
    change d (1,0) - S.projector (F z) (d (1,0)) = 0 at hs
    exact (sub_eq_zero.mp hs).symm
  · rintro ⟨⟨v,hv⟩,ht⟩
    change S.projector (F z) (d (0,1)) = 0 at ht
    have hs : S.projector (F z) (d (1,0)) = d (1,0) := by
      change S.projector (F z) v = d (1,0) at hv
      rw [← hv,S.idempotent]
    have hp (w : ℂ × ℂ) : S.projector (F z) (d w) = w.1 • d (1,0) := by
      rw [hd,map_add,map_smul,map_smul,hs,ht,smul_zero,add_zero]
    have hq (w : ℂ × ℂ) : S.swap.projector (F z) (d w) = w.2 • d (0,1) := by
      change d w - S.projector (F z) (d w) = _
      rw [hp,hd]; abel
    constructor
    · intro v w
      change fderiv ℂ (Prod.fst : ℂ × ℂ → ℂ) z v • S.projector (F z) (d w) =
        fderiv ℂ (Prod.fst : ℂ × ℂ → ℂ) z w • S.projector (F z) (d v)
      rw [hdf,hp w,hp v]
      change v.1 • (w.1 • _) = w.1 • (v.1 • _)
      rw [smul_smul,smul_smul,mul_comm]
    · intro v w
      change fderiv ℂ (Prod.snd : ℂ × ℂ → ℂ) z v • S.swap.projector (F z) (d w) =
        fderiv ℂ (Prod.snd : ℂ × ℂ → ℂ) z w • S.swap.projector (F z) (d v)
      rw [hds,hq w,hq v]
      change v.2 • (w.2 • _) = w.2 • (v.2 • _)
      rw [smul_smul,smul_smul,mul_comm]

 

theorem extend_rational_tangent_map [CompactSpace X.Carrier]
    (e : ProjectiveEmbedding X) (x₀ : X.Carrier) {U : Set (ℂ × ℂ)}
    (hU : IsOpen U) (hdense : Dense U) (F : ℂ × ℂ → X.Carrier)
    (V : ℂ × ℂ → Fin (e.N+1) → ℂ)
    (hV : ∀ j, RationalSurface.RationalOn U (fun w => V w j))
    (hn : ∀ w ∈ U, V w ≠ 0) (hi : ∀ w ∈ U, e.Incidence (F w) (V w))
    (hw : ∀ w ∈ U, S.WedgeAt F Prod.fst w ∧ S.swap.WedgeAt F Prod.snd w) :
    ∃ H : ℂ × ℂ → X.Carrier,
      ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω H ∧ EqOn H F U ∧
      (∀ w, S.WedgeAt H Prod.fst w ∧ S.swap.WedgeAt H Prod.snd w) := by
  obtain ⟨P,hprim,hfin,hprop⟩ := RationalSurface.primitive_tuple_of_rational V hV hn
  let p := fun j => RationalSurface.toMv (P j)
  let H := lift e x₀ p
  have htuple (w : ℂ × ℂ) : tuple e p w = fun j => RationalSurface.eval (P j) w := by
    funext j; exact RationalSurface.value_toMv (P j) w
  have hfinite : Set.Finite {w : ℂ × ℂ | ∀ j, value (p j) w = 0} := by
    simpa only [p,RationalSurface.value_toMv] using hfin
  have hprop' (w : ℂ × ℂ) (hw : w ∈ U) : tuple e p w ≠ 0 ∧ e.Incidence (F w) (tuple e p w) := by
    obtain ⟨c,hc,he⟩ := hprop w hw
    rw [htuple,he]
    exact ⟨smul_ne_zero hc (hn w hw),(e.incidence_smul_iff hc).mpr (hi w hw)⟩
  have hcone (w : ℂ × ℂ) : ∃ x, e.Incidence x (tuple e p w) := by
    apply e.isClosed_cone.mem_of_frequently_of_tendsto _ (tuple_analytic e p w).continuousAt
    exact (mem_closure_iff_frequently.mp (hdense w)).mono (fun a ha => ⟨F a,(hprop' a ha).2⟩)
  have hagree : EqOn H F U := by
    intro w hw
    exact e.coneLift_eq x₀ (hprop' w hw).1 (hprop' w hw).2
  have hnear (w : ℂ × ℂ) (hw : w ∈ U) : H =ᶠ[𝓝 w] F :=
    Filter.Eventually.mono (hU.mem_nhds hw) (fun a ha => hagree ha)
  have hreg (w : ℂ × ℂ) (hnw : tuple e p w ≠ 0) :
      S.WedgeAt H Prod.fst w ∧ S.swap.WedgeAt H Prod.snd w := by
    have hhol : ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω H w :=
      lift_holomorphic e x₀ hnw (Filter.Eventually.of_forall hcone)
    have hfreq := (mem_closure_iff_frequently.mp (hdense w)).mono (fun a ha =>
      And.intro ((hw a ha).1.congr S (hnear a ha).symm Filter.EventuallyEq.rfl)
        ((hw a ha).2.congr S.swap (hnear a ha).symm Filter.EventuallyEq.rfl))
    exact ⟨S.wedgeAt_of_frequently hhol (analyticAt_fst) (hfreq.mono (fun _ h => h.1)),
      S.swap.wedgeAt_of_frequently hhol (analyticAt_snd) (hfreq.mono (fun _ h => h.2))⟩
  let A : PolynomialBlowup.P := MvPolynomial.X 0
  let B : PolynomialBlowup.P := MvPolynomial.X 1
  have hA : value A = (Prod.fst : ℂ × ℂ → ℂ) := by funext w; simp [A,value,valueHom]
  have hB : value B = (Prod.snd : ℂ × ℂ → ℂ) := by funext w; simp [B,value,valueHom]
  have hAnc (c : ℂ) : A ≠ MvPolynomial.C c := by
    intro he
    have h0 : (0 : ℂ) = c := by simpa [A,value,valueHom] using congrArg (fun q => value q (0,0)) he
    have h1 : (1 : ℂ) = c := by simpa [A,value,valueHom] using congrArg (fun q => value q (1,0)) he
    exact one_ne_zero (h1.trans h0.symm)
  have hBnc (c : ℂ) : B ≠ MvPolynomial.C c := by
    intro he
    have h0 : (0 : ℂ) = c := by simpa [B,value,valueHom] using congrArg (fun q => value q (0,0)) he
    have h1 : (1 : ℂ) = c := by simpa [B,value,valueHom] using congrArg (fun q => value q (0,1)) he
    exact one_ne_zero (h1.trans h0.symm)
  have hall (w : ℂ × ℂ) : tuple e p w ≠ 0 :=
    nonzero_everywhere e S x₀ p A B hfinite hcone (by simpa only [hA,hB] using hreg) hAnc hBnc w
  exact ⟨H,(fun w => lift_holomorphic e x₀ (hall w) (Filter.Eventually.of_forall hcone)),
    hagree,fun w => hreg w (hall w)⟩

end SplitTangent.TangentSplitting

namespace SplitTangent
namespace TangentSplitting
open ReciprocalCharts
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

lemma tangency_comp_changeChart {H : ℂ × ℂ → X.Carrier}
    (hH : ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω H)
    (ht : ∀ w, mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) H w (1,0) ∈ S.first (H w) ∧
      mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) H w (0,1) ∈ S.second (H w))
    (b c : Bool) {w : ℂ × ℂ} (hw : w ∈ torus) :
    mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) (H ∘ changeChart b c) w (1,0) ∈
      S.first (H (changeChart b c w)) ∧
    mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) (H ∘ changeChart b c) w (0,1) ∈
      S.second (H (changeChart b c w)) := by
  let d : (ℂ × ℂ) →L[ℂ] Tangent X (H (changeChart b c w)) :=
    mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) H (changeChart b c w)
  have hd : mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) (H ∘ changeChart b c) w =
      d.comp (fderiv ℂ (changeChart b c) w) := by
    rw [mfderiv_comp w ((hH _).mdifferentiableAt (by simp))
      (changeChart_analytic b c hw).differentiableAt.mdifferentiableAt,mfderiv_eq_fderiv]
    rfl
  constructor
  · rw [hd]
    change d (fderiv ℂ (changeChart b c) w (1,0)) ∈ _
    rw [changeChart_fderiv_first b c hw,map_smul]
    exact (S.first _).smul_mem _ (ht _).1
  · rw [hd]
    change d (fderiv ℂ (changeChart b c) w (0,1)) ∈ _
    rw [changeChart_fderiv_second b c hw,map_smul]
    exact (S.second _).smul_mem _ (ht _).2

lemma rational_changeChart_fst (b : Bool) :
    RationalSurface.RationalOn torus (fun w => coord b w.1) := by
  cases b
  · exact RationalSurface.RationalOn.fst torus
  · exact (RationalSurface.RationalOn.fst torus).inv (fun _ h => h.1)

lemma rational_changeChart_snd (b : Bool) :
    RationalSurface.RationalOn torus (fun w => coord b w.2) := by
  cases b
  · exact RationalSurface.RationalOn.snd torus
  · exact (RationalSurface.RationalOn.snd torus).inv (fun _ h => h.2)

 

theorem exists_projective_tangent_box_oai [CompactSpace X.Carrier]
    (e : ProjectiveEmbedding X) (g : RationalCurve X) : Nonempty (TangentBox S g) := by
  obtain ⟨z,P,F,hn,hi,hF,hdiag,hpde⟩ := S.exists_affine_polynomial_tangent_box e g
  let L : ℂ × ℂ → ℂ × ℂ := fun w => (w.2,w.1-w.2)
  let H₀ := F ∘ L
  have hL : ContDiff ℂ ω L := contDiff_snd.prodMk (contDiff_fst.sub contDiff_snd)
  have hH₀ : ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω H₀ := hF.comp hL.contMDiff
  have hA : (fun w : ℂ × ℂ => w.1+w.2) ∘ L = Prod.fst := by
    funext w; simp [L]
  have hB : Prod.fst ∘ L = Prod.snd := rfl
  have hW₀ (w : ℂ × ℂ) : S.WedgeAt H₀ Prod.fst w ∧ S.swap.WedgeAt H₀ Prod.snd w := by
    obtain ⟨ha,hb⟩ := S.wedges_of_pde (hpde (L w))
    rw [← hA,← hB]
    exact ⟨ha.comp S (hF _) (analyticAt_fst.add analyticAt_snd).differentiableAt
        (hL.differentiable (by simp) w),
      hb.comp S.swap (hF _) (analyticAt_fst.differentiableAt) (hL.differentiable (by simp) w)⟩
  have hT₀ (w : ℂ × ℂ) := (S.wedges_iff_tangency).mp (hW₀ w)
  have hline : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω (fun u : ℂ => F (u,0)) :=
    hF.comp ((contDiff_id.prodMk contDiff_const : ContDiff ℂ ω (fun u : ℂ => (u,(0 : ℂ)))).contMDiff)
  have hdiagall := ComplexManifold.eqOn_of_eventuallyEq isPreconnected_univ
    (fun u _ => hline u) (fun u _ => g.finite_holomorphic u) (mem_univ z) hdiag
  have hD₀ (u : ℂ) : H₀ (u,u) = g.finite u := by
    simpa only [H₀,Function.comp_apply,L,sub_self] using hdiagall (mem_univ u)
  have hcharts (a b : Bool) : ∃ H : ℂ × ℂ → X.Carrier,
      ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω H ∧
      EqOn H (H₀ ∘ changeChart a b) torus ∧
      (∀ w, S.WedgeAt H Prod.fst w ∧ S.swap.WedgeAt H Prod.snd w) := by
    let V : ℂ × ℂ → Fin (e.N+1) → ℂ := fun w j => RationalSurface.eval (P j) (L (changeChart a b w))
    apply S.extend_rational_tangent_map e (g.finite 0) torus_open torus_dense
      (H₀ ∘ changeChart a b) V
    · intro j
      exact (rational_changeChart_snd b).eval_comp
        ((rational_changeChart_fst a).sub (rational_changeChart_snd b)) (P j)
    · intro w _; exact hn (L (changeChart a b w))
    · intro w _; exact hi (L (changeChart a b w))
    · intro w hw
      exact (S.wedges_iff_tangency).mpr (S.tangency_comp_changeChart hH₀ hT₀ a b hw)
  choose H hH hEq hW using hcharts
  have heq (a b c d : Bool) (w : ℂ × ℂ) (hw : w ∈ overlap a b c d) :
      H a b w = H c d (changeChart (Bool.xor a c) (Bool.xor b d) w) := by
    apply tendsto_nhds_unique_of_frequently_eq (hH a b w).continuousAt
      ((hH c d _).continuousAt.comp (changeChart_analytic_on_overlap a b c d hw).continuousAt)
    apply (mem_closure_iff_frequently.mp (torus_dense w)).mono
    intro v hv
    change H a b v = H c d (changeChart (Bool.xor a c) (Bool.xor b d) v)
    rw [hEq a b hv,hEq c d (changeChart_torus _ _ hv)]
    simp only [Function.comp_apply]
    exact congrArg H₀ (changeChart_transition a b c d v).symm
  have hzero (w : ℂ × ℂ) : H false false w = H₀ w := by
    apply tendsto_nhds_unique_of_frequently_eq (hH false false w).continuousAt (hH₀ w).continuousAt
    apply (mem_closure_iff_frequently.mp (torus_dense w)).mono
    intro v hv
    exact hEq false false hv
  have hinfty (u : ℂ) : H true true (u,u) = g.infinity u := by
    have hc : Continuous (fun v : ℂ => H true true (v,v)) :=
      (hH true true).continuous.comp (continuous_id.prodMk continuous_id)
    apply tendsto_nhds_unique_of_frequently_eq hc.continuousAt (g.infinity_holomorphic u).continuousAt
    apply (mem_closure_iff_frequently.mp ((dense_compl_singleton (0 : ℂ)) u)).mono
    intro v hv
    have hv' : v ≠ 0 := hv
    rw [hEq true true (show (v,v) ∈ torus from ⟨hv',hv'⟩)]
    change H₀ (v⁻¹,v⁻¹) = _
    rw [hD₀,g.overlap v⁻¹ (inv_ne_zero hv'),inv_inv]
  exact ⟨⟨H,hH,heq,fun u => (hzero (u,u)).trans (hD₀ u),hinfty,
    fun a b w => (S.wedges_iff_tangency).mp (hW a b w)⟩⟩

end TangentSplitting
end SplitTangent

end

end OAI
end

theorem solution.{u} : type_of% @OAI.SplitTangent.TangentSplitting.exists_projective_tangent_box_oai.{u} := @OAI.SplitTangent.TangentSplitting.exists_projective_tangent_box_oai.{u}
