-- Prove2me | solution 1 for OAI.CrouzeixHilbert.Conformal.ExteriorCollar.holomorphic_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:47:20.612205+00:00
-- url     : https://prove2.me/submissions/9900c83b-7855-43e5-b8a3-7f0d1ec32c17

import Mathlib
import Definitions.Def_CrouzeixHilbert
import Definitions.Def_OAIQWCH000
import Theorems.Thm_OAI_CrouzeixHilbert_Boundary_endpoint_le_two_of_physical_tests
import Theorems.Thm_OAI_CrouzeixHilbert_Conformal_ExteriorCollar_physical_intertwines
import Theorems.Thm_OAI_CrouzeixHilbert_Conformal_ExteriorCollar_physical_laurent_tests
import Theorems.Thm_OAI_CrouzeixHilbert_Conformal_InteriorCollar_spectralRadius_coordinate_lt_one
import Theorems.Thm_OAI_CrouzeixHilbert_Disk_integral_matrixHolomorphic
import Theorems.Thm_OAI_CrouzeixHilbert_disk_endpoint_extremal
import Theorems.Thm_OAI_CrouzeixHilbert_exists_polynomial_uniform_approx
import Theorems.Thm_OAI_CrouzeixHilbert_sum_integral_eq_zero_of_null_homology

section
-- module Solutions.OAIQW_CrouzeixHilbert.ContourExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contour Existence. -/

noncomputable section

open scoped Topology InnerProductSpace TensorProduct Matrix.Norms.L2Operator

open Set Filter Metric

namespace CrouzeixHilbert

theorem SmoothContour.intervalIntegrable_indexIntegrand (Γ : SmoothContour) {a : ℂ}
    (ha : a ∉ Γ.path '' Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun t => deriv Γ.path t / (Γ.path t - a))
      MeasureTheory.volume (0 : ℝ) 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le zero_le_one]
  apply Γ.smooth.continuous_deriv_one.continuousOn.div
    (Γ.smooth.continuous.sub continuous_const).continuousOn
  intro t ht he
  exact ha ⟨t, ht, sub_eq_zero.mp he⟩

theorem SmoothContour.index_eq_zero_of_re_pos (Γ : SmoothContour) {a c : ℂ}
    (hc : c ≠ 0) (h : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c * (Γ.path t - a)).re) :
    Γ.index a = 0 := by
  have hnz (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Γ.path t - a ≠ 0 := by
    intro he
    simpa only [he, mul_zero, Complex.zero_re, lt_self_iff_false] using h t ht
  have ha : a ∉ Γ.path '' Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, he⟩
    exact hnz t ht (sub_eq_zero.mpr he)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => Complex.log (c * (Γ.path t - a)))
        (deriv Γ.path t / (Γ.path t - a)) t := by
    have he := (((Γ.smooth.differentiable (by norm_num) t).hasDerivAt.sub_const a).const_mul c).clog_real
      (Complex.mem_slitPlane_iff.mpr (Or.inl (h t ht)))
    simpa only [mul_div_mul_left _ _ hc] using he
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le zero_le_one] using ht))
    (Γ.intervalIntegrable_indexIntegrand ha)
  rw [Γ.closed, sub_self] at he
  simp only [SmoothContour.index, he, mul_zero]

theorem SmoothContour.index_eq_zero_of_convex (Γ : SmoothContour) {V : Set ℂ}
    (hV : Convex ℝ V) (hVc : IsClosed V) (hΓ : Γ.path '' Icc (0 : ℝ) 1 ⊆ V)
    {a : ℂ} (ha : a ∉ V) :
    Γ.index a = 0 := by
  obtain ⟨l, r, hla, hlV⟩ :=
    RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ) hV hVc ha
  have hl (z : ℂ) : l z = l 1 * z := by
    calc
      l z = l (z • (1 : ℂ)) := by simp
      _ = z • l 1 := l.map_smul z 1
      _ = l 1 * z := by simp [mul_comm]
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      0 < (l 1 * (Γ.path t - a)).re := by
    rw [← hl, map_sub, Complex.sub_re]
    exact sub_pos.mpr (hla.trans (hlV _ (hΓ ⟨t, ht, rfl⟩)))
  apply Γ.index_eq_zero_of_re_pos ?_ hp
  intro he
  have := hp 0 ⟨le_rfl, zero_le_one⟩
  simp only [he, zero_mul, Complex.zero_re, lt_self_iff_false] at this

theorem hasDerivAt_unitCirclePath (t : ℝ) :
    HasDerivAt unitCirclePath (unitCirclePath t * (2 * (Real.pi : ℂ) * Complex.I)) t := by
  convert! (hasDerivAt_circleMap 0 1 (2 * Real.pi * t)).scomp t
    ((hasDerivAt_id t).const_mul (2 * Real.pi)) using 1
  simp only [unitCirclePath, mul_one, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.NumericalRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact numerical closure, supremum norms, and spectral containment. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem supNorm_bddAbove {E : Type*} [NormedAddCommGroup E] {S : Set ℂ}
    {F : ℂ → E} (hS : IsCompact S) (hF : ContinuousOn F S) :
    BddAbove (insert 0 ((fun z => ‖F z‖) '' S)) :=
  (hS.bddAbove_image hF.norm).insert 0

theorem supNorm_nonneg {E : Type*} [NormedAddCommGroup E] {S : Set ℂ}
    {F : ℂ → E} (hb : BddAbove (insert 0 ((fun z => ‖F z‖) '' S))) :
    0 ≤ supNorm S F :=
  le_csSup hb (by simp)

theorem norm_le_supNorm {E : Type*} [NormedAddCommGroup E] {S : Set ℂ}
    {F : ℂ → E} (hb : BddAbove (insert 0 ((fun z => ‖F z‖) '' S)))
    {z : ℂ} (hz : z ∈ S) : ‖F z‖ ≤ supNorm S F :=
  le_csSup hb (Set.mem_insert_of_mem 0 ⟨z, hz, rfl⟩)

end CrouzeixHilbert
end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.HomologicalCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Homological Cauchy. -/

noncomputable section

open Set Filter Metric MeasureTheory

open scoped Topology

namespace CrouzeixHilbert

theorem null_homology_integral {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Γ : ι → SmoothContour) (c : ι → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hΓ : ∀ i, (Γ i).trace ⊆ U)
    (hnull : ∀ w ∉ U, ∑ i, c i * (Γ i).index w = 0)
    {f : ℂ → E} (hf : DifferentiableOn ℂ f U) :
    ∑ i, c i • (Γ i).integral f = 0 :=
  sum_integral_eq_zero_of_null_homology Γ c hU hΓ hnull hf

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.InteriorCollar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interior Collar. -/

noncomputable section

open Set Filter Metric Topology Function Complex

namespace CrouzeixHilbert.Conformal

namespace InteriorCollar

variable {U : Set ℂ} (R : InteriorCollar U)

lemma zero_mem_disk : (0 : ℂ) ∈ ball 0 R.radius := mem_ball_zero_iff.mpr (by simpa using R.one_lt_radius.trans' zero_lt_one)

lemma h_zero_mem : R.h 0 ∈ U := R.bijective_h.mapsTo (mem_ball_self zero_lt_one)

lemma f_h_zero : R.f (R.h 0) = 0 := R.inverse.2 (R.disk_subset R.zero_mem_disk)

end InteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BoundaryForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Forms. -/

noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open MeasureTheory

namespace CrouzeixHilbert.Boundary

section FieldAction

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem fieldAction_apply_ae (L : α → E →L[ℝ] E) (hL : AEStronglyMeasurable L μ)
    (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ 1) (u : Lp E 2 μ) :
    fieldAction L hL hLn u =ᵐ[μ] fun t => L t (u t) := by
  unfold fieldAction
  dsimp only [LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  exact MemLp.coeFn_toLp _

end FieldAction

section L2Multipliers

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {k : ℕ}

theorem lpLeft_apply_ae (F : α → Matrix (Fin k) (Fin k) ℂ)
    (hm : AEStronglyMeasurable F μ) (hn : ∀ᵐ t ∂μ, ‖F t‖ ≤ 1)
    (u : Lp (HS k) 2 μ) :
    lpLeft F hm hn u =ᵐ[μ] fun t => toHS (F t * ofHS (u t)) :=
  fieldAction_apply_ae _ _ _ _

theorem lpRight_apply_ae (F : α → Matrix (Fin k) (Fin k) ℂ)
    (hm : AEStronglyMeasurable F μ) (hn : ∀ᵐ t ∂μ, ‖F t‖ ≤ 1)
    (u : Lp (HS k) 2 μ) :
    lpRight F hm hn u =ᵐ[μ] fun t => toHS (ofHS (u t) * F t) :=
  fieldAction_apply_ae _ _ _ _

end L2Multipliers

end CrouzeixHilbert.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Fourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace lp Classical Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert.Boundary

attribute [local instance] OAI.CrouzeixHilbert.Boundary.instFactLtRealOfNat_solutions
lemma matrixFourierBasis_repr {k : ℕ} (u : BoundaryL2 k) (a : ℤ × (Fin k × Fin k)) :
    (matrixFourierBasis k).repr u a = fourierCoeff (lpEntry a.2 u) a.1 := by
  rw [HilbertBasis.repr_apply_apply, matrixFourierBasis_apply, inner_matrixFourier,
    ← coe_fourierBasis, ← HilbertBasis.repr_apply_apply, fourierBasis_repr]

end CrouzeixHilbert.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BoundaryOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Operators. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace

namespace CrouzeixHilbert.Boundary

attribute [local instance] OAI.CrouzeixHilbert.Boundary.boundaryOperatorsFactOnePos
lemma norm_kernelOperator_le {k : ℕ} (m : CircleKernel)
    (hm : ∀ x, 0 ≤ m x) (hm1 : ∀ x, ∫ y, m (x,y) ∂circleMeasure = 1)
    (hm2 : ∀ y, ∫ x, m (x,y) ∂circleMeasure = 1) :
    ‖kernelOperator (k := k) m hm hm1 hm2‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖kernelLp m u‖ ≤ 1 * ‖u‖
  simpa only [one_mul] using norm_kernelLp_le m hm hm1 hm2 u

end CrouzeixHilbert.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.SteinMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stein Metric. -/

noncomputable section

open Set Filter

open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator

namespace CrouzeixHilbert.Metric

section Stein

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
theorem summable_steinSeries (T : A) (hT : spectralRadius ℂ T < 1) :
    Summable (fun j : ℕ => star (T ^ j) * T ^ j) := by
  have hs := summable_norm_pow T hT
  have hsmall : ∀ᶠ j in atTop, ‖T ^ j‖ ≤ 1 := by
    exact (hs.tendsto_atTop_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun j hj => hj.le)
  apply hs.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hsmall] with j hj
  calc
    ‖star (T ^ j) * T ^ j‖ ≤ ‖star (T ^ j)‖ * ‖T ^ j‖ := norm_mul_le _ _
    _ = ‖T ^ j‖ * ‖T ^ j‖ := by rw [norm_star]
    _ ≤ ‖T ^ j‖ * 1 := mul_le_mul_of_nonneg_left hj (norm_nonneg _)
    _ = ‖T ^ j‖ := mul_one _

theorem steinSeries_nonneg (T : A) : 0 ≤ steinSeries T :=
  tsum_nonneg (fun _ => star_mul_self_nonneg _)

omit [PartialOrder A] [StarOrderedRing A] in
theorem steinSeries_eq_one_add (T : A) (hT : spectralRadius ℂ T < 1) :
    steinSeries T = 1 + star T * steinSeries T * T := by
  have hs := summable_steinSeries T hT
  have he : (fun j : ℕ => star (T ^ (j + 1)) * T ^ (j + 1)) =
      (fun j : ℕ => star T * (star (T ^ j) * T ^ j) * T) := by
    funext j
    rw [pow_succ, star_mul]
    simp only [mul_assoc]
  have hz := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, pow_zero, star_one, mul_one] at hz
  rw [he, (hs.mul_left (star T)).tsum_mul_right T, hs.tsum_mul_left (star T)] at hz
  exact hz.symm

theorem one_le_steinSeries (T : A) (hT : spectralRadius ℂ T < 1) :
    1 ≤ steinSeries T := by
  rw [steinSeries_eq_one_add T hT]
  exact le_add_of_nonneg_right (star_left_conjugate_nonneg (steinSeries_nonneg T) T)

omit [PartialOrder A] [StarOrderedRing A] in
theorem steinSeries_sub (T : A) (hT : spectralRadius ℂ T < 1) :
    steinSeries T - star T * steinSeries T * T = 1 := by
  nth_rw 1 [steinSeries_eq_one_add T hT]
  exact add_sub_cancel_right _ _

end Stein

section Minimization

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem Feasible.nonneg {T H : A} {τ : ℝ} (h : Feasible T τ H) : 0 ≤ H :=
  zero_le_one.trans h.lower

variable [Nontrivial A]

theorem Feasible.one_le {T H : A} {τ : ℝ} (h : Feasible T τ H) : 1 ≤ τ := by
  have he : algebraMap ℝ A 1 ≤ algebraMap ℝ A τ := by simpa using h.lower.trans h.upper
  exact algebraMap_le_algebraMap.mp he

theorem Feasible.norm_le {T H : A} {τ : ℝ} (h : Feasible T τ H) : ‖H‖ ≤ τ :=
  (CStarAlgebra.norm_le_iff_le_algebraMap H (zero_le_one.trans h.one_le) h.nonneg).mpr h.upper

omit [Nontrivial A] in
theorem steinSeries_feasible (T : A) (hT : spectralRadius ℂ T < 1) :
    Feasible T ‖steinSeries T‖ (steinSeries T) := by
  refine ⟨one_le_steinSeries T hT, ?_, ?_⟩
  · exact (CStarAlgebra.norm_le_iff_le_algebraMap _ (norm_nonneg _)
      (steinSeries_nonneg T)).mp le_rfl
  · exact sub_nonneg.mp (by rw [steinSeries_sub T hT]; exact zero_le_one)

theorem exists_minimizing_metric [FiniteDimensional ℂ A]
    (T : A) (hT : spectralRadius ℂ T < 1) :
    ∃ (τ : ℝ) (H : A), Feasible T τ H ∧ 1 ≤ τ ∧
      ∀ (τ' : ℝ) (H' : A), Feasible T τ' H' → τ ≤ τ' := by
  let : ProperSpace A := FiniteDimensional.proper ℂ A
  let H₀ := steinSeries T
  have h₀ := steinSeries_feasible T hT
  let M : Set A := {H | 1 ≤ H ∧ star T * H * T ≤ H}
  have hMc : IsClosed M := (isClosed_le continuous_const continuous_id).inter
    (isClosed_le ((continuous_const.mul continuous_id).mul continuous_const) continuous_id)
  let K := Metric.closedBall (0 : A) ‖H₀‖ ∩ M
  have hKc : IsCompact K := (isCompact_closedBall (0 : A) ‖H₀‖).inter_right hMc
  have hKne : K.Nonempty := by
    refine ⟨H₀, ?_⟩
    simp only [K, mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
    exact ⟨le_rfl, h₀.lower, h₀.stein⟩
  obtain ⟨H, hHK, hmin⟩ := hKc.exists_isMinOn hKne continuous_norm.continuousOn
  have hH0 : 0 ≤ H := zero_le_one.trans hHK.2.1
  refine ⟨‖H‖, H, ⟨hHK.2.1, ?_, hHK.2.2⟩, ?_, ?_⟩
  · exact (CStarAlgebra.norm_le_iff_le_algebraMap H (norm_nonneg H) hH0).mp le_rfl
  · have h : ‖(1 : A)‖ ≤ ‖H‖ :=
      CStarAlgebra.norm_le_norm_of_nonneg_of_le zero_le_one hHK.2.1
    simpa only [norm_one] using h
  · intro τ' H' hH'
    by_cases hb : ‖H'‖ ≤ ‖H₀‖
    · have h'K : H' ∈ K := ⟨by simpa using hb, hH'.lower, hH'.stein⟩
      exact (hmin h'K).trans hH'.norm_le
    · have hbound : ‖H‖ ≤ ‖H₀‖ := by simpa using hHK.1
      exact (hbound.trans (le_of_not_ge hb)).trans hH'.norm_le

end Minimization

section Similarity

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem norm_le_one_iff_star_mul_self_le (a : A) :
    ‖a‖ ≤ 1 ↔ star a * a ≤ 1 := by
  rw [← CStarAlgebra.norm_le_one_iff_of_nonneg (star a * a)
    (star_mul_self_nonneg a), CStarRing.norm_star_mul_self]
  constructor <;> intro h <;> nlinarith [norm_nonneg a]

variable [Nontrivial A]

theorem Feasible.sqrt_similarity {T H : A} {τ : ℝ} (h : Feasible T τ H) :
    IsUnit (CFC.sqrt H) ∧
      ‖CFC.sqrt H * T * Ring.inverse (CFC.sqrt H)‖ ≤ 1 ∧
      ‖CFC.sqrt H‖ * ‖Ring.inverse (CFC.sqrt H)‖ ≤ Real.sqrt τ := by
  let S := CFC.sqrt H
  let R := Ring.inverse S
  have hS0 : 0 ≤ S := CFC.sqrt_nonneg H
  have hS1 : (1 : A) ≤ S := by
    simpa only [CFC.sqrt_one] using CFC.sqrt_le_sqrt (1 : A) H h.lower
  have hSpos : IsStrictlyPositive S := isStrictlyPositive_one.of_le hS1
  have hu : IsUnit S := hSpos.isUnit
  have hR0 : 0 ≤ R := (CFC.ringInverse_nonneg_iff_nonneg_of_isUnit hu).mpr hS0
  have hR1 : R ≤ (1 : A) := by
    simpa only [Ring.inverse_one] using CStarAlgebra.ringInverse_le_ringInverse hS1
  have hRS : R * S = 1 := Ring.inverse_mul_cancel S hu
  have hSR : S * R = 1 := Ring.mul_inverse_cancel S hu
  have hRSa : star R = R := (IsSelfAdjoint.of_nonneg hR0).star_eq
  have hSSa : star S = S := (IsSelfAdjoint.of_nonneg hS0).star_eq
  have hSS : S * S = H := CFC.sqrt_mul_sqrt_self H h.nonneg
  have hconj := star_left_conjugate_le_conjugate h.stein R
  have hright : star R * H * R = 1 := by
    rw [hRSa, ← hSS, ← mul_assoc, hRS, one_mul, hSR]
  have hleft : star R * (star T * H * T) * R =
      star (S * T * R) * (S * T * R) := by
    rw [star_mul, star_mul, hSSa, ← hSS]
    noncomm_ring
  rw [hleft, hright] at hconj
  refine ⟨hu, (norm_le_one_iff_star_mul_self_le _).mpr hconj, ?_⟩
  have hRn : ‖R‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg R hR0).mpr hR1
  change ‖S‖ * ‖R‖ ≤ Real.sqrt τ
  calc
    ‖S‖ * ‖R‖ ≤ ‖S‖ * 1 := mul_le_mul_of_nonneg_left hRn (norm_nonneg _)
    _ = Real.sqrt ‖H‖ := by simpa only [S, mul_one] using CFC.norm_sqrt H h.nonneg
    _ ≤ Real.sqrt τ := Real.sqrt_le_sqrt h.norm_le

theorem Feasible.sqrt_spectrum {T H : A} {τ : ℝ} (h : Feasible T τ H) :
    spectrum ℂ (CFC.sqrt H * T * Ring.inverse (CFC.sqrt H)) = spectrum ℂ T := by
  obtain ⟨u, hu⟩ := h.sqrt_similarity.1
  rw [← hu]
  simpa only [Ring.inverse_unit] using spectrum.units_conjugate (R := ℂ) (a := T) (u := u)

end Similarity

end CrouzeixHilbert.Metric

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Compression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compression. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace

namespace CrouzeixHilbert.Compression

section Multiplication

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem fieldAction_apply_ae (L : α → E →L[ℂ] E) (hL : AEStronglyMeasurable L μ)
    (C : ℝ) (hC : 0 ≤ C) (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ C) (u : Lp E 2 μ) :
    fieldAction L hL C hC hLn u =ᵐ[μ] fun t => L t (u t) := by
  unfold fieldAction
  dsimp only [LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  exact MemLp.coeFn_toLp _

theorem norm_fieldAction_le (L : α → E →L[ℂ] E) (hL : AEStronglyMeasurable L μ)
    (C : ℝ) (hC : 0 ≤ C) (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ C) :
    ‖fieldAction L hL C hC hLn‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro u
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [fieldAction_apply_ae L hL C hC hLn u, hLn] with t ht hn
  rw [ht]
  exact ((L t).le_opNorm _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

end Multiplication

section Isometry

variable {α E : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [CompactSpace α] [SecondCountableTopology α] {μ : Measure α} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem integral_eq_compression (R L : C(α, E →L[ℂ] E))
    (hmass : ∫ t, star (R t) * R t ∂μ = 1) (C : ℝ) (hC : 0 ≤ C)
    (hLn : ∀ t, ‖L t‖ ≤ C) :
    (∫ t, star (R t) * L t * R t ∂μ) =
      (isometry R hmass).toContinuousLinearMap.adjoint.comp
        ((fieldAction L L.continuous.aestronglyMeasurable C hC
          (Filter.Eventually.of_forall hLn)).comp (isometry R hmass).toContinuousLinearMap) := by
  have hi : Integrable (fun t => star (R t) * L t * R t) μ :=
    ((R.continuous.star.mul L.continuous).mul R.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.integral_apply hi,
    ← integral_inner (𝕜 := ℂ) (f := fun t => (star (R t) * L t * R t) y)
      ((ContinuousLinearMap.apply ℂ E y).integrable_comp hi) x]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    LinearIsometry.coe_toContinuousLinearMap, isometry_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [lift_apply_ae R x,
    fieldAction_apply_ae L L.continuous.aestronglyMeasurable C hC
      (Filter.Eventually.of_forall hLn) (lift R y), lift_apply_ae R y] with t hx hL hy
  rw [hx, hL, hy]
  exact ContinuousLinearMap.adjoint_inner_right (R t) x (L t (R t y))

theorem norm_integral_le (R L : C(α, E →L[ℂ] E))
    (hmass : ∫ t, star (R t) * R t ∂μ = 1) (C : ℝ) (hC : 0 ≤ C)
    (hLn : ∀ t, ‖L t‖ ≤ C) :
    ‖∫ t, star (R t) * L t * R t ∂μ‖ ≤ C := by
  rw [integral_eq_compression R L hmass C hC hLn]
  let V := (isometry R hmass).toContinuousLinearMap
  have hn : ‖V‖ ≤ 1 := (isometry R hmass).norm_toContinuousLinearMap_le
  calc
    _ ≤ ‖V.adjoint‖ * (‖fieldAction L L.continuous.aestronglyMeasurable C hC
        (Filter.Eventually.of_forall hLn)‖ * ‖V‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (C * 1) := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact mul_le_mul hn (mul_le_mul (norm_fieldAction_le _ _ _ _ _) hn
        (norm_nonneg V) hC) (mul_nonneg (norm_nonneg _) (norm_nonneg V)) (by norm_num)
    _ = C := by ring

end Isometry

end CrouzeixHilbert.Compression

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Resolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resolvent. -/

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem nonneg_re_inner_of_unit (T : Operator H)
    (h : ∀ x : H, ‖x‖ = 1 → 0 ≤ (⟪x, T x⟫_ℂ).re) (x : H) :
    0 ≤ (⟪x, T x⟫_ℂ).re := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let v : H := (‖x‖ : ℂ)⁻¹ • x
  have hv : ‖v‖ = 1 := by simp [v, norm_smul, hn.ne']
  have ht := h v hv
  have he : (⟪v, T v⟫_ℂ).re = ‖x‖⁻¹ * (‖x‖⁻¹ * (⟪x, T x⟫_ℂ).re) := by
    simp [v, Complex.mul_re, mul_comm]
  rw [he] at ht
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hn)).mp
    ((mul_nonneg_iff_of_pos_left (inv_pos.mpr hn)).mp ht)

variable [CompleteSpace H]

theorem isPositive_add_adjoint_of_unit (T : Operator H)
    (h : ∀ x : H, ‖x‖ = 1 → 0 ≤ (⟪x, T x⟫_ℂ).re) :
    (T + star T).IsPositive := by
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨IsSelfAdjoint.add_star_self T, fun x => ?_⟩
  have ht := nonneg_re_inner_of_unit T h x
  change 0 ≤ (⟪(T + star T) x, x⟫_ℂ).re
  simp only [add_apply, inner_add_left,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
    Complex.add_re]
  have he : (⟪T x, x⟫_ℂ).re = (⟪x, T x⟫_ℂ).re := inner_re_symm (𝕜 := ℂ) _ _
  rw [he]
  linarith only [ht]

theorem isPositive_supporting_halfplane (A : Operator H) (z q : ℂ)
    (hsupport : ∀ w ∈ numericalRange A, 0 ≤ (star q * (z - w)).re) :
    (star q • (algebraMap ℂ (Operator H) z - A) +
      star (star q • (algebraMap ℂ (Operator H) z - A))).IsPositive := by
  apply isPositive_add_adjoint_of_unit
  intro x hx
  have h := hsupport ⟪x, A x⟫_ℂ ⟨x, hx, rfl⟩
  simpa [inner_smul_right, inner_sub_right, inner_self_eq_norm_sq_to_K, hx,
    Algebra.algebraMap_eq_smul_one] using h

theorem resolvent_hermitian_congruence (A : Operator H) (z q : ℂ)
    (hz : IsUnit (algebraMap ℂ (Operator H) z - A)) :
    let E := algebraMap ℂ (Operator H) z - A
    let R := Ring.inverse E
    star R * (star q • E + star (star q • E)) * R = q • R + star (q • R) := by
  dsimp only
  let E := algebraMap ℂ (Operator H) z - A
  let R := Ring.inverse E
  have hER : E * R = 1 := Ring.mul_inverse_cancel E hz
  change star R * (star q • E + star (star q • E)) * R = q • R + star (q • R)
  have hstar : star R * star E = 1 := by rw [← star_mul, hER, star_one]
  calc
    star R * (star q • E + star (star q • E)) * R =
        star q • (star R * (E * R)) + q • ((star R * star E) * R) := by
      simp only [star_smul, star_star, mul_add, add_mul, mul_smul_comm,
        smul_mul_assoc, mul_assoc]
    _ = star q • star R + q • R := by rw [hER, hstar, mul_one, one_mul]
    _ = q • R + star (q • R) := by rw [star_smul, add_comm]

theorem isPositive_original_resolvent (A : Operator H) (z q : ℂ)
    (hz : IsUnit (algebraMap ℂ (Operator H) z - A))
    (hsupport : ∀ w ∈ numericalRange A, 0 ≤ (star q * (z - w)).re) :
    (q • Ring.inverse (algebraMap ℂ (Operator H) z - A) +
      star (q • Ring.inverse (algebraMap ℂ (Operator H) z - A))).IsPositive := by
  have hp := (isPositive_supporting_halfplane A z q hsupport).adjoint_conj
    (Ring.inverse (algebraMap ℂ (Operator H) z - A))
  change (star (Ring.inverse (algebraMap ℂ (Operator H) z - A)) *
    (star q • (algebraMap ℂ (Operator H) z - A) +
      star (star q • (algebraMap ℂ (Operator H) z - A))) *
      Ring.inverse (algebraMap ℂ (Operator H) z - A)).IsPositive at hp
  rwa [resolvent_hermitian_congruence A z q hz] at hp

theorem isPositive_original_resolvent_of_not_mem (A : Operator H) (z q : ℂ)
    (hz : z ∉ numericalClosure A)
    (hsupport : ∀ w ∈ numericalRange A, 0 ≤ (star q * (z - w)).re) :
    (q • Ring.inverse (algebraMap ℂ (Operator H) z - A) +
      star (q • Ring.inverse (algebraMap ℂ (Operator H) z - A))).IsPositive := by
  apply isPositive_original_resolvent A z q _ hsupport
  change z ∈ resolventSet ℂ A
  by_contra he
  exact hz (spectrum_subset_numericalClosure A he)

theorem isPositive_contraction_defect (T : Operator H) (hn : ‖T‖ ≤ 1) :
    (1 - star T * T).IsPositive := by
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨by simp [IsSelfAdjoint, star_mul], fun x => ?_⟩
  have ht : ‖T x‖ ≤ ‖x‖ := by
    calc
      ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = ‖x‖ := one_mul _
  change 0 ≤ RCLike.re ⟪x - ContinuousLinearMap.adjoint T (T x), x⟫_ℂ
  simp only [inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
    map_sub, ← norm_sq_eq_re_inner]
  nlinarith only [ht, norm_nonneg x, norm_nonneg (T x)]

theorem disk_resolvent_congruence (T : Operator H) (hT : IsUnit (1 - T)) :
    let R := Ring.inverse (1 - T)
    star R * (1 - star T * T) * R = R + star R - 1 := by
  let E := 1 - T
  let R := Ring.inverse E
  have hER : E * R = 1 := Ring.mul_inverse_cancel E hT
  have hstar : star R * star E = 1 := by rw [← star_mul, hER, star_one]
  have hid : 1 - star T * T = star E + E - star E * E := by
    simp only [E, star_sub, star_one]
    noncomm_ring
  change star R * (1 - star T * T) * R = R + star R - 1
  rw [hid]
  calc
    star R * (star E + E - star E * E) * R =
        (star R * star E) * R + star R * (E * R) -
          (star R * star E) * (E * R) := by noncomm_ring
    _ = R + star R - 1 := by rw [hstar, hER, one_mul, mul_one, one_mul]

theorem isPositive_diskResolvent (T : Operator H) (hn : ‖T‖ ≤ 1)
    (hu : IsUnit (1 - T)) :
    (Ring.inverse (1 - T) + star (Ring.inverse (1 - T)) - 1).IsPositive := by
  have hp := (isPositive_contraction_defect T hn).adjoint_conj (Ring.inverse (1 - T))
  have hp' : (star (Ring.inverse (1 - T)) * (1 - star T * T) *
      Ring.inverse (1 - T)).IsPositive := by
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.comp_assoc] using hp
  rw [disk_resolvent_congruence T hu] at hp'
  exact hp'

theorem isPositive_diskDensity (D : Operator H) (hD : ‖D‖ ≤ 1) (ζ : ℂ)
    (hζ : ‖ζ‖ = 1) (hu : IsUnit (1 - ζ⁻¹ • D)) : (diskDensity D ζ).IsPositive := by
  apply isPositive_diskResolvent _ _ hu
  rw [norm_smul, norm_inv, hζ, inv_one, one_mul]
  exact hD

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.DiskCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disk Calculus. -/

noncomputable section

open MeasureTheory

open scoped Topology

namespace CrouzeixHilbert.Disk

section Series

attribute [local instance] OAI.CrouzeixHilbert.Disk.instFactLtRealOfNat_solutions
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

lemma integral_fourier (n : ℤ) : ∫ t : CircleSpace, fourier n t ∂σ = if n = 0 then 1 else 0 := by
  have h := congrFun (@fourierCoeff_fourier 1 _ n) 0
  simpa only [fourierCoeff, neg_zero, fourier_zero, one_smul, Pi.single_apply,
    eq_comm] using h

lemma integral_fourier_smul (a : A) (n : ℤ) :
    ∫ t : CircleSpace, fourier n t • a ∂σ = if n = 0 then a else 0 := by
  rw [integral_smul_const, integral_fourier]
  split_ifs <;> simp

lemma integral_fourier_series (a : ℕ → A) (ha : Summable (fun n => ‖a n‖)) (k : ℕ → ℤ) :
    (∫ t : CircleSpace, ∑' n : ℕ, fourier (k n) t • a n ∂σ) =
      ∑' n : ℕ, if k n = 0 then a n else 0 := by
  rw [← integral_tsum_of_summable_integral_norm]
  · simp only [integral_fourier_smul]
  · intro n
    exact ((fourier _).continuous.smul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · simpa only [norm_smul, norm_fourier, one_mul, integral_const, probReal_univ, one_smul] using ha

end Series

section Density

attribute [local instance] OAI.CrouzeixHilbert.Disk.instFactLtRealOfNat_solutions
variable {A : Type*} [CStarAlgebra A]

theorem integral_moment (D : A) (hD : spectralRadius ℂ D < 1) (j : ℕ) :
    ∫ t : CircleSpace, fourier (j : ℤ) t • phi D t ∂σ = D ^ j := by
  have hc₁ := continuous_diskInverse D hD
  have hi₁ : Integrable (fun t : CircleSpace => Ring.inverse (1 - (fourier 1 t)⁻¹ • D)) σ :=
    hc₁.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi₂ : Integrable (fun t : CircleSpace =>
      star (Ring.inverse (1 - (fourier 1 t)⁻¹ • D))) σ :=
    hc₁.star.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs := Metric.summable_norm_pow D hD
  have hs' : Summable (fun n : ℕ => ‖star (D ^ n)‖) := by simpa only [norm_star] using hs
  have hleft : (∫ t : CircleSpace,
      fourier (j : ℤ) t • Ring.inverse (1 - (fourier 1 t)⁻¹ • D) ∂σ) = D ^ j := by
    simp_rw [disk_inverse_series D hD, ← tsum_const_smul'', smul_smul, ← fourier_add]
    rw [integral_fourier_series _ hs]
    convert tsum_ite_eq j (fun n : ℕ => D ^ n) using 1
    congr 1
    ext n
    simp only [add_neg_eq_zero, Nat.cast_inj, eq_comm]
  have hright : (∫ t : CircleSpace,
      fourier (j : ℤ) t • star (Ring.inverse (1 - (fourier 1 t)⁻¹ • D)) ∂σ) =
        if j = 0 then 1 else 0 := by
    simp_rw [disk_inverse_series D hD, tsum_star, star_smul, fourier_neg,
      starRingEnd_apply, star_star, ← tsum_const_smul'', smul_smul, ← fourier_add]
    rw [integral_fourier_series _ hs']
    by_cases hj : j = 0
    · simp [hj]
    · rw [ite_eq_right hj]
      have hz : ∀ n : ℕ, (if (j : ℤ) + (n : ℤ) = 0 then star (D ^ n) else 0) = 0 := by
        intro n
        simp only [← Nat.cast_add, Nat.cast_eq_zero, Nat.add_eq_zero_iff,
          hj, false_and, ↓reduceIte]
      simp only [hz, tsum_zero]
  simp only [phi, smul_sub, smul_add]
  have hsplit := integral_sub ((hi₁.fourier_smul (j : ℤ)).add
    (hi₂.fourier_smul (j : ℤ))) ((integrable_const (1 : A)).fourier_smul (j : ℤ))
  simp only [Pi.add_apply] at hsplit
  rw [hsplit, integral_add (hi₁.fourier_smul (j : ℤ)) (hi₂.fourier_smul (j : ℤ)),
    hleft, hright, integral_fourier_smul]
  simp only [Nat.cast_eq_zero, add_sub_cancel_right]

theorem integral_phi (D : A) (hD : spectralRadius ℂ D < 1) : ∫ t, phi D t ∂σ = 1 := by
  simpa only [Nat.cast_zero, fourier_zero, one_smul, pow_zero] using integral_moment D hD 0

end Density

section OperatorPositivity

universe u

attribute [local instance] OAI.CrouzeixHilbert.Disk.instFactLtRealOfNat_solutions
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem phi_isPositive (D : Operator H) (hn : ‖D‖ ≤ 1) (hD : spectralRadius ℂ D < 1)
    (t : CircleSpace) : (phi D t).IsPositive := by
  exact isPositive_diskDensity D hn (fourier 1 t) (norm_fourier _ _)
    (inverse_one_sub_of_summable _ (summable_diskPowers D hD t)).1

end OperatorPositivity

end CrouzeixHilbert.Disk

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.TensorDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor Density. -/

noncomputable section

open MeasureTheory Set Filter

open scoped Topology InnerProductSpace TensorProduct Matrix.Norms.L2Operator

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

attribute [local instance] OAI.CrouzeixHilbert.tensorDensityOperatorRealNormedSpace
attribute [local instance] OAI.CrouzeixHilbert.tensorDensityOperatorCompleteSpace
theorem tensorOperator_mul (A D : Operator H) {m : ℕ} (B C : Coeff m) :
    tensorOperator (A * D) (B * C) = tensorOperator A B * tensorOperator D C := by
  ext x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (tensorOperator (A * D) (B * C)).continuous
      ((tensorOperator A B).continuous.comp (tensorOperator D C).continuous)) ?_
  intro v
  simp only [tensorOperator, map_mul, mul_apply_eq_comp,
    ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_mul]

variable [CompleteSpace H]

theorem tensorOperator_star (A : Operator H) {m : ℕ} (B : Coeff m) :
    tensorOperator (star A) (star B) = star (tensorOperator A B) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq ((tensorOperator (star A) (star B)).continuous.inner continuous_const)
      (continuous_id.inner continuous_const)) ?_
  intro a
  refine UniformSpace.Completion.induction_on y
    (isClosed_eq (continuous_const.inner continuous_id)
      (continuous_const.inner (tensorOperator A B).continuous)) ?_
  intro b
  simp only [tensorOperator, ContinuousLinearMap.completion_apply_coe,
    UniformSpace.Completion.inner_coe, map_star]
  induction a using TensorProduct.induction_on with
  | zero => first | (simp only [map_zero]; done) | (simp only [UniformSpace.Completion.coe_zero, map_zero]; done) | simp
  | tmul x u =>
    induction b using TensorProduct.induction_on with
    | zero => first | (simp only [map_zero]; done) | (simp only [UniformSpace.Completion.coe_zero, map_zero]; done) | simp
    | tmul y v => simp [ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    | add b c hb hc => simp only [inner_add_right, map_add, hb, hc]
  | add a c ha hc => simp only [inner_add_left, map_add, ha, hc]

section PositiveDensity

attribute [local instance] OAI.CrouzeixHilbert.tensorDensityOperatorRealNormedSpace
attribute [local instance] OAI.CrouzeixHilbert.tensorDensityOperatorCompleteSpace
variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [CompactSpace α] [SecondCountableTopology α] {μ : Measure α} [IsFiniteMeasure μ]

omit [MeasurableSpace α] [BorelSpace α] [CompactSpace α] [SecondCountableTopology α] in
theorem amplifiedRoot_star_mul (Λ : C(α, Operator H)) (hΛ : ∀ t, 0 ≤ Λ t)
    (m : ℕ) (t : α) :
    star (amplifiedRoot Λ hΛ m t) * amplifiedRoot Λ hΛ m t = tensorOperator (Λ t) (1 : Coeff m) := by
  change star (tensorOperator _ _) * tensorOperator _ _ = _
  rw [← tensorOperator_star, ← tensorOperator_mul, star_one, one_mul,
    Compression.densityRoot_star_mul]

omit [SecondCountableTopology α] in
theorem amplifiedRoot_mass (Λ : C(α, Operator H)) (hΛ : ∀ t, 0 ≤ Λ t)
    (hmass : ∫ t, Λ t ∂μ = 1) (m : ℕ) :
    ∫ t, star (amplifiedRoot Λ hΛ m t) * amplifiedRoot Λ hΛ m t ∂μ = 1 := by
  simp only [amplifiedRoot_star_mul, ← tensorOperatorCLM_apply]
  rw [(tensorOperatorCLM (H := H) (1 : Coeff m)).integral_comp_comm,
    hmass, tensorOperatorCLM_apply, tensorOperator_one]
  exact Λ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [MeasurableSpace α] [BorelSpace α] [CompactSpace α] [SecondCountableTopology α] in
theorem amplifiedRoot_sandwich (Λ : C(α, Operator H)) (hΛ : ∀ t, 0 ≤ Λ t)
    {m : ℕ} (F : C(α, Coeff m)) (t : α) :
    star (amplifiedRoot Λ hΛ m t) * coefficientField (H := H) F t *
      amplifiedRoot Λ hΛ m t = tensorOperator (Λ t) (F t) := by
  change star (tensorOperator _ _) * tensorOperator _ _ * tensorOperator _ _ = _
  rw [← tensorOperator_star, ← tensorOperator_mul, ← tensorOperator_mul,
    star_one, one_mul, mul_one, mul_one, Compression.densityRoot_star_mul]

theorem norm_integral_tensor_density_le (Λ : C(α, Operator H)) (hΛ : ∀ t, 0 ≤ Λ t)
    (hmass : ∫ t, Λ t ∂μ = 1) {m : ℕ} (F : C(α, Coeff m))
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀ t, ‖F t‖ ≤ C) :
    ‖∫ t, tensorOperator (Λ t) (F t) ∂μ‖ ≤ C := by
  simp_rw [← amplifiedRoot_sandwich Λ hΛ F]
  apply Compression.norm_integral_le _ _ (amplifiedRoot_mass Λ hΛ hmass m) C hC
  intro t
  change ‖tensorOperator (1 : Operator H) (F t)‖ ≤ C
  calc
    ‖tensorOperator (1 : Operator H) (F t)‖ ≤ ‖(1 : Operator H)‖ * ‖F t‖ := norm_tensorOperator_le _ _
    _ ≤ 1 * ‖F t‖ := mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le (norm_nonneg _)
    _ ≤ C := by simpa only [one_mul] using hF t

end PositiveDensity

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.CauchyProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cauchy Projection. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace TensorProduct Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

namespace Boundary

theorem boundaryField_apply_ae {n : ℕ} (U : C(CircleSpace, Coeff n)) :
    boundaryField U =ᵐ[circleMeasure] fun t => toHS (U t) :=
  ContinuousMap.coeFn_toLp _ _

theorem toHS_single {n : ℕ} (i j : Fin n) :
    toHS (Matrix.single i j (1 : ℂ)) = EuclideanSpace.single (i,j) (1 : ℂ) := by
  ext ⟨a,b⟩
  change (Matrix.single i j (1 : ℂ)) a b = _
  simp only [Matrix.single_apply, PiLp.single_apply]
  by_cases hai : a = i <;> by_cases hbj : b = j <;> simp [hai, hbj, Prod.ext_iff, eq_comm]

@[simp] theorem boundaryField_matrixLaurentMonomial {n : ℕ}
    (a : ℤ × (Fin n × Fin n)) (c : ℂ) :
    boundaryField (matrixLaurentMonomial a c) = c • matrixFourier a := by
  apply Lp.ext
  filter_upwards [boundaryField_apply_ae (matrixLaurentMonomial a c),
    matrixFourier_apply_ae a, Lp.coeFn_smul c (matrixFourier a)] with t hu hf hs
  rw [hu, hs, Pi.smul_apply, hf]
  change toHS ((c * fourier a.1 t) • Matrix.single a.2.1 a.2.2 (1 : ℂ)) = _
  rw [← toHSCLM_apply, map_smul, toHSCLM_apply, toHS_single, mul_smul]

theorem boundary_real_inner_eq_re {n : ℕ} (u v : BoundaryL2 n) :
    ⟪u, v⟫_ℝ = (⟪u, v⟫_ℂ).re := boundary_real_inner u v

theorem eq_of_inner_matrixLaurentMonomial {n : ℕ} {u v : BoundaryL2 n}
    (h : ∀ (a : ℤ × (Fin n × Fin n)) (c : ℂ),
      ⟪u, boundaryField (matrixLaurentMonomial a c)⟫_ℝ =
      ⟪v, boundaryField (matrixLaurentMonomial a c)⟫_ℝ) : u = v := by
  apply (matrixFourierBasis n).repr.injective
  ext a
  simp only [HilbertBasis.repr_apply_apply, matrixFourierBasis_apply]
  rw [← inner_conj_symm (matrixFourier a) u, ← inner_conj_symm (matrixFourier a) v]
  congr 1
  apply Complex.ext
  · have hr := h a 1
    simpa only [boundaryField_matrixLaurentMonomial, one_smul,
      boundary_real_inner_eq_re] using hr
  · have hi := h a Complex.I
    simp only [boundaryField_matrixLaurentMonomial, boundary_real_inner_eq_re,
      inner_smul_right, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_sub] at hi
    exact neg_injective hi

end Boundary

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.PolynomialApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial Approximation. -/

noncomputable section

open scoped Topology

open Set Filter Metric MeasureTheory

namespace CrouzeixHilbert

theorem SmoothContour.integral_deriv_mul_eq_zero_of_holomorphic
    (Γ : SmoothContour) {U : Set ℂ} (hU : IsOpen U) (hc : Convex ℝ U)
    (hΓ : Γ.trace ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    (∫ t in (0 : ℝ)..1, deriv Γ.path t * f (Γ.path t)) = 0 := by
  obtain ⟨g, hg⟩ := hc.exists_forall_hasDerivWithinAt hf
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => g (Γ.path t)) (deriv Γ.path t * f (Γ.path t)) t := by
    have he := ((hg _ (hΓ ⟨t, ht, rfl⟩)).hasDerivAt
      (hU.mem_nhds (hΓ ⟨t, ht, rfl⟩))).hasFDerivAt.restrictScalars ℝ
    convert! he.comp_hasDerivAt t (Γ.smooth.differentiable (by norm_num) t).hasDerivAt using 1
  have hi : IntervalIntegrable (fun t => deriv Γ.path t * f (Γ.path t))
      volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact Γ.smooth.continuous_deriv_one.continuousOn.mul
      (hf.continuousOn.comp Γ.smooth.continuous.continuousOn
        (fun t ht => hΓ ⟨t, ht, rfl⟩))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le zero_le_one] using ht)) hi
  simpa only [Γ.closed, sub_self] using he

theorem SmoothContour.cauchy_formula_convex (Γ : SmoothContour) {U : Set ℂ}
    (hU : IsOpen U) (hc : Convex ℝ U) (hΓ : Γ.trace ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {z : ℂ}
    (hz : z ∈ U) (hzΓ : z ∉ Γ.trace) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (∫ t in (0 : ℝ)..1, deriv Γ.path t * f (Γ.path t) / (Γ.path t - z)) =
      Γ.index z * f z := by
  have hd : DifferentiableOn ℂ (dslope f z) U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds hz)).mpr hf
  have hi : IntervalIntegrable (fun t => deriv Γ.path t * dslope f z (Γ.path t))
      volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact Γ.smooth.continuous_deriv_one.continuousOn.mul
      (hd.continuousOn.comp Γ.smooth.continuous.continuousOn (fun t ht => hΓ ⟨t, ht, rfl⟩))
  have he : (∫ t in (0 : ℝ)..1, deriv Γ.path t * f (Γ.path t) / (Γ.path t - z)) =
      (∫ t in (0 : ℝ)..1, deriv Γ.path t * dslope f z (Γ.path t)) +
      (∫ t in (0 : ℝ)..1, deriv Γ.path t / (Γ.path t - z)) * f z := by
    rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_add hi
      ((Γ.intervalIntegrable_indexIntegrand hzΓ).mul_const (f z))]
    apply intervalIntegral.integral_congr
    intro t ht
    have hne : Γ.path t ≠ z := fun he => hzΓ ⟨t, by simpa using ht, he⟩
    dsimp only
    rw [dslope_of_ne _ hne]
    simp only [slope, vsub_eq_sub, smul_eq_mul]
    ring
  rw [he, Γ.integral_deriv_mul_eq_zero_of_holomorphic hU hc hΓ hd, zero_add]
  exact (mul_assoc _ _ _).symm

open scoped Matrix.Norms.L2Operator

universe u

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.HolomorphicAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Holomorphic Algebra. -/

noncomputable section

open Set Filter Metric Topology Complex MeasureTheory

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace CrouzeixHilbert

lemma exists_polynomial_tendstoUniformlyOn {K U : Set ℂ}
    (hK : IsCompact K) (hc : Convex ℝ K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    ∃ p : ℕ → Polynomial ℂ, TendstoUniformlyOn (fun n z => (p n).eval z) f atTop K := by
  have happrox (n : ℕ) : ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖p.eval z - f z‖ < (1 : ℝ)/(n+1) :=
    exists_polynomial_uniform_approx hK hc hU hKU hf (by positivity)
  choose p hp using happrox
  refine ⟨p, Metric.tendstoUniformlyOn_iff.mpr (fun ε hε => ?_)⟩
  have ht : Tendsto (fun n : ℕ => (1 : ℝ)/(n+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn z hz
  rw [dist_comm, dist_eq_norm]
  exact (hp n z hz).trans hn

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.CircleAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Circle Analytic. -/

noncomputable section

open Set Metric Filter Topology Complex ComplexConjugate MeasureTheory

open scoped InnerProductSpace

namespace CrouzeixHilbert.Boundary

attribute [local instance] OAI.CrouzeixHilbert.Boundary.circleAnalyticFactZeroLtOne
lemma fourierCoeff_inverse_holomorphic {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E}
    (hf : DifferentiableOn ℂ f (closedBall 0 1)) (n : ℕ) :
    fourierCoeff (fun t : CircleSpace => f (circleCoordinate t)⁻¹) (n : ℤ) =
      if n = 0 then f 0 else 0 := by
  change (∫ t : CircleSpace, fourier (-(n : ℤ)) t • f (circleCoordinate t)⁻¹ ∂circleMeasure) = _
  simp_rw [← circleCoordinate_inverse_pow]
  rw [integral_holomorphic_inverse_circleCoordinate (f := fun u => u^n • f u)
    ((differentiableOn_id.pow n).smul hf)]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn, zero_pow hn]

lemma repr_boundaryField {k : ℕ} (F : C(CircleSpace, Coeff k))
    (a : ℤ × (Fin k × Fin k)) :
    (matrixFourierBasis k).repr (boundaryField F) a =
      fourierCoeff (fun t => F t a.2.1 a.2.2) a.1 := by
  rw [matrixFourierBasis_repr]
  apply congrFun (fourierCoeff_congr_ae ?_) a.1
  filter_upwards [lpEntry_apply_ae a.2 (boundaryField F), boundaryField_apply_ae F] with t he hf
  rw [he, hf]
  rfl

lemma fourierProj_boundaryField_inverse_zero {k : ℕ} (F : C(CircleSpace, Coeff k))
    {f : ℂ → Coeff k} (hf : EntrywiseHolomorphic (closedBall 0 1) f) (h0 : f 0 = 0)
    (hF : ∀ t, F t = f (circleCoordinate t)⁻¹) :
    fourierProjC k 0 (boundaryField F) = 0 ∧ fourierProjC k 1 (boundaryField F) = 0 := by
  classical
  have hr (a : ℤ × (Fin k × Fin k)) (ha : 0 ≤ a.1) :
      (matrixFourierBasis k).repr (boundaryField F) a = 0 := by
    rcases a with ⟨n,i,j⟩
    obtain ⟨m,rfl⟩ := Int.eq_ofNat_of_zero_le ha
    rw [repr_boundaryField]
    simp_rw [hF]
    rw [fourierCoeff_inverse_holomorphic (hf i j)]
    split_ifs <;> simp [h0]
  constructor
  · apply (matrixFourierBasis k).repr.injective
    ext a
    rw [repr_fourierProjC, map_zero]
    change (if frequencyPart 0 a.1 then _ else 0) = 0
    split_ifs with ha
    · exact hr a (le_of_eq ((frequencyPart_zero a.1).mp ha).symm)
    · rfl
  · apply (matrixFourierBasis k).repr.injective
    ext a
    rw [repr_fourierProjC, map_zero]
    change (if frequencyPart 1 a.1 then _ else 0) = 0
    split_ifs with ha
    · exact hr a ((frequencyPart_pos a.1).mp ha).le
    · rfl

lemma fourierProj_boundaryField_inverse_neg {k : ℕ} (F : C(CircleSpace, Coeff k))
    {f : ℂ → Coeff k} (hf : EntrywiseHolomorphic (closedBall 0 1) f) (h0 : f 0 = 0)
    (hF : ∀ t, F t = f (circleCoordinate t)⁻¹) :
    fourierProjC k 2 (boundaryField F) = boundaryField F := by
  have hh := congrArg (fun L : BoundaryL2 k →L[ℂ] BoundaryL2 k => L (boundaryField F))
    (fourierProjC_total k)
  have hz := fourierProj_boundaryField_inverse_zero F hf h0 hF
  simpa only [add_apply, hz.1, hz.2, zero_add,
    ContinuousLinearMap.id_apply] using hh

lemma boundaryCauchy_inverse_zero {k : ℕ} (M : BoundaryL2 k →L[ℝ] BoundaryL2 k)
    (F : C(CircleSpace, Coeff k)) {f : ℂ → Coeff k}
    (hf : EntrywiseHolomorphic (closedBall 0 1) f) (h0 : f 0 = 0)
    (hF : ∀ t, F t = f (circleCoordinate t)⁻¹) :
    boundaryCauchy M (boundaryField F) = 0 := by
  have hz := fourierProj_boundaryField_inverse_zero F hf h0 hF
  change fourierProjC k 0 (boundaryField F) + fourierProjC k 1 (boundaryField F) +
    fourierProjC k 2 (M (fourierProjC k 1 (boundaryField F))) = 0
  simp only [hz.1, hz.2, map_zero, add_zero]

open scoped Classical in

lemma fourierProj_matrixFourier {k : ℕ} (i : Fin 3) (a : ℤ × (Fin k × Fin k)) :
    fourierProjC k i (matrixFourier a) = if frequencyPart i a.1 then matrixFourier a else 0 := by
  classical
  apply (matrixFourierBasis k).repr.injective
  ext b
  rw [repr_fourierProjC]
  by_cases hba : b = a
  · subst b
    split_ifs <;> simp only [map_zero, lp.coeFn_zero, Pi.zero_apply]
  · have hz : (matrixFourierBasis k).repr (matrixFourier a) b = 0 := by
      rw [← matrixFourierBasis_apply, HilbertBasis.repr_self]
      simp [hba]
    split_ifs <;> simp only [hz, map_zero, lp.coeFn_zero, Pi.zero_apply]

end CrouzeixHilbert.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.AngularRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular Radius. -/

noncomputable section

open Set Filter Metric Topology Function Complex MeasureTheory

namespace CrouzeixHilbert.Boundary

lemma integral_scaled_circleCoordinate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) (R : ℝ) :
    (∫ t, f ((R : ℂ) * circleCoordinate t) ∂circleMeasure) = Real.circleAverage f 0 R := by
  rw [integral_circleCoordinate_eq_circleAverage (fun z => f ((R : ℂ) * z))]
  unfold Real.circleAverage
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [circleMap, zero_add, ofReal_one, one_mul]

lemma integral_scaled_coordinate_cauchy {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : ℂ → E) {R : ℝ} (hR : 0 < R) :
    (∫ t, ((R : ℂ) * circleCoordinate t) • f ((R : ℂ) * circleCoordinate t)
        ∂circleMeasure) =
      (2 * (Real.pi : ℂ) * I)⁻¹ • (∮ z in C(0, R), f z) := by
  rw [integral_scaled_circleCoordinate (fun z => z • f z) R,
    Real.circleAverage_eq_circleIntegral hR.ne']
  congr 1
  apply circleIntegral.integral_congr hR.le
  intro z hz
  have hn : z ≠ 0 := norm_pos_iff.mp (by rw [mem_sphere_zero_iff_norm.mp hz]; exact hR)
  simp only [sub_zero, smul_smul, inv_mul_cancel₀ hn, one_smul]

lemma integral_scaled_deform {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) {f : ℂ → E}
    (hc : ContinuousOn f (closedBall 0 R \ ball 0 r))
    (hd : DifferentiableOn ℂ f (ball 0 R \ closedBall 0 r)) :
    (∫ t, ((R : ℂ) * circleCoordinate t) • f ((R : ℂ) * circleCoordinate t)
      ∂circleMeasure) =
    ∫ t, ((r : ℂ) * circleCoordinate t) • f ((r : ℂ) * circleCoordinate t)
      ∂circleMeasure := by
  rw [integral_scaled_coordinate_cauchy f (hr.trans_le hrR),
    integral_scaled_coordinate_cauchy f hr]
  congr 1
  apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR countable_empty hc
  intro z hz
  exact (hd z hz.1).differentiableAt ((isOpen_ball.sdiff isClosed_closedBall).mem_nhds hz.1)

lemma integral_laurent_deform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) {f : ℂ → E}
    (hc : ContinuousOn f (closedBall 0 R \ ball 0 r))
    (hd : DifferentiableOn ℂ f (ball 0 R \ closedBall 0 r)) (j : ℤ) :
    (∫ t, (((R : ℂ) * circleCoordinate t)^j) • f ((R : ℂ) * circleCoordinate t)
      ∂circleMeasure) =
    ∫ t, (((r : ℂ) * circleCoordinate t)^j) • f ((r : ℂ) * circleCoordinate t)
      ∂circleMeasure := by
  have hn {z : ℂ} (hz : z ∈ closedBall 0 R \ ball 0 r) : z ≠ 0 := by
    have hle : r ≤ ‖z‖ := not_lt.mp (mt mem_ball_zero_iff.mpr hz.2)
    exact norm_pos_iff.mp (hr.trans_le hle)
  have hh := integral_scaled_deform hr hrR
    (f := fun z => z^(j-1) • f z)
    ((continuousOn_id.zpow₀ (j-1) (fun z hz => Or.inl (hn hz))).smul hc)
    ((((differentiableOn_id (𝕜 := ℂ)).zpow (Or.inl (fun z hz => hn ⟨ball_subset_closedBall hz.1,
      fun h => hz.2 (ball_subset_closedBall h)⟩)))).smul hd)
  have hs {z : ℂ} (hz : z ≠ 0) : z * z^(j-1) = z^j := by
    rw [← zpow_one_add₀ hz]
    congr 1
    omega
  have hRz (t : CircleSpace) : (R : ℂ) * circleCoordinate t ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr (hr.trans_le hrR).ne') (circleCoordinate_ne_zero t)
  have hrz (t : CircleSpace) : (r : ℂ) * circleCoordinate t ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr hr.ne') (circleCoordinate_ne_zero t)
  simpa only [smul_smul, hs (hRz _), hs (hrz _)] using hh

end CrouzeixHilbert.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BoundaryKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Kernel. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

open Boundary

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

lemma norm_boundaryOperator_le (hc : Convex ℝ U) (k : ℕ) :
    ‖C.boundaryOperator hc k‖ ≤ 1 :=
  norm_kernelOperator_le C.boundaryKernel (C.boundaryKernel_nonnegative hc)
    C.boundaryKernel_integral_right C.boundaryKernel_integral_left

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ExteriorContour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior Contour. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

open Boundary

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

lemma boundaryContour_deriv (t : ℝ) :
    deriv C.boundaryContour.path t =
      (2 * (Real.pi : ℂ) * I) * C.boundaryNormal (t : CircleSpace) := by
  have hc : C.radius < ‖unitCirclePath t‖ := by rw [unitCirclePath_norm]; exact C.radius_lt_one
  have hd := ((C.analytic _ hc).differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt
    t (hasDerivAt_unitCirclePath t)
  change HasDerivAt C.boundaryContour.path _ t at hd
  rw [hd.deriv]
  change (unitCirclePath t * (2 * (Real.pi : ℂ) * I)) * deriv C.G (unitCirclePath t) = _
  change _ = (2 * (Real.pi : ℂ) * I) * (circleCoordinate (t : CircleSpace) * _)
  rw [circleCoordinate_coe]
  change (circleMap 0 1 (2 * Real.pi * t) * (2 * (Real.pi : ℂ) * I)) * _ = _
  unfold unitCirclePath
  ring

lemma boundaryContour_trace_subset : C.boundaryContour.trace ⊆ frontier U := by
  rintro z ⟨t,ht,rfl⟩
  exact C.boundary.mapsTo (mem_sphere_zero_iff_norm.mpr (unitCirclePath_norm t))

lemma boundaryContour_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      (∫ t in (0 : ℝ)..1, deriv C.boundaryContour.path t • f (C.boundaryContour.path t)) =
    ∫ t, C.boundaryNormal t • f (C.boundaryMap t) ∂circleMeasure := by
  rw [integral_circleMeasure_eq_interval, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [C.boundaryContour_deriv, smul_smul, inv_mul_cancel_left₀]
  · congr 1
    change f (C.G (unitCirclePath t)) = f (C.G (circleCoordinate (t : CircleSpace)))
    rw [circleCoordinate_coe]
    rfl
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero

lemma exterior_value_not_mem (hU : IsOpen U) {t : ℂ} (ht : 1 ≤ ‖t‖) : C.G t ∉ U := by
  rcases ht.eq_or_lt with he|he
  · have hb := C.boundary.mapsTo (mem_sphere_zero_iff_norm.mpr he.symm)
    exact fun hz => hb.2 (hU.interior_eq.symm ▸ hz)
  · exact fun h => C.outside.mapsTo he (subset_closure h)

lemma reciprocalDenominator_inverse {z t : ℂ} (ht : C.radius < ‖t‖) :
    C.reciprocalDenominator z t⁻¹ = t⁻¹ * (C.G t - z) := by
  rw [C.laurent t ht, reciprocalDenominator]
  have hn : t ≠ 0 := norm_pos_iff.mp (C.radius_pos.trans ht)
  field_simp
  ring

lemma reciprocalDenominator_ne_zero (hU : IsOpen U) {z u : ℂ} (hz : z ∈ U)
    (hu : u ∈ closedBall 0 1) : C.reciprocalDenominator z u ≠ 0 := by
  by_cases hu0 : u = 0
  · simpa only [hu0, reciprocalDenominator, zero_mul, add_zero] using C.leading_ne_zero
  have ht : 1 ≤ ‖u⁻¹‖ := by
    rw [norm_inv]
    exact (one_le_inv₀ (norm_pos_iff.mpr hu0)).mpr (mem_closedBall_zero_iff.mp hu)
  have he := C.reciprocalDenominator_inverse (z := z) (C.radius_lt_one.trans_le ht)
  rw [inv_inv] at he
  rw [he]
  exact mul_ne_zero hu0 (sub_ne_zero.mpr (fun h => C.exterior_value_not_mem hU ht (h ▸ hz)))

lemma differentiableOn_reciprocalCauchy (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) :
    DifferentiableOn ℂ (C.reciprocalCauchy z) (closedBall 0 1) := by
  apply DifferentiableOn.div
  · exact (differentiableOn_const _).sub ((differentiableOn_id.pow 2).mul
      (C.regular_analytic.deriv.differentiableOn.mono C.closed_unit_subset_reciprocalDisk))
  · exact (differentiableOn_const _).add (differentiableOn_id.mul
      ((C.regular_analytic.differentiableOn.mono C.closed_unit_subset_reciprocalDisk).sub_const z))
  · exact fun u hu => C.reciprocalDenominator_ne_zero hU hz hu

lemma reciprocalCauchy_boundary (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) (t : CircleSpace) :
    C.reciprocalCauchy z (circleCoordinate t)⁻¹ =
      C.boundaryNormal t / (C.boundaryMap t - z) := by
  have ht : C.radius < ‖circleCoordinate t‖ := by rw [norm_circleCoordinate]; exact C.radius_lt_one
  rw [reciprocalCauchy, C.reciprocalDenominator_inverse ht, ← C.deriv_laurent ht]
  change deriv C.G (circleCoordinate t) / ((circleCoordinate t)⁻¹ * (C.G (circleCoordinate t) - z)) = _
  simp only [boundaryNormal, boundaryMap, ContinuousMap.coe_mk]
  have hden : C.G (circleCoordinate t) - z ≠ 0 :=
    sub_ne_zero.mpr fun he =>
      C.exterior_value_not_mem hU (norm_circleCoordinate t).ge (he ▸ hz)
  field_simp [hden]

lemma boundaryContour_index_inside (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) :
    C.boundaryContour.index z = 1 := by
  change (2 * (Real.pi : ℂ) * I)⁻¹ •
    (∫ t in (0 : ℝ)..1, deriv C.boundaryContour.path t * (C.boundaryContour.path t - z)⁻¹) = 1
  rw [show (fun t : ℝ => deriv C.boundaryContour.path t * (C.boundaryContour.path t - z)⁻¹) =
      fun t => deriv C.boundaryContour.path t • (C.boundaryContour.path t - z)⁻¹ from rfl,
    C.boundaryContour_integral (fun w => (w - z)⁻¹)]
  change (∫ t, C.boundaryNormal t / (C.boundaryMap t - z) ∂circleMeasure) = 1
  simp_rw [← C.reciprocalCauchy_boundary hU hz]
  rw [integral_holomorphic_inverse_circleCoordinate (C.differentiableOn_reciprocalCauchy hU hz)]
  simp [reciprocalCauchy, reciprocalDenominator, C.leading_ne_zero]

lemma boundaryContour_index_outside (hc : Convex ℝ U) {z : ℂ} (hz : z ∉ closure U) :
    C.boundaryContour.index z = 0 :=
  C.boundaryContour.index_eq_zero_of_convex hc.closure isClosed_closure
    (C.boundaryContour_trace_subset.trans frontier_subset_closure) hz

lemma physical_cauchy_formula (hU : IsOpen U) {V : Set ℂ} (hV : IsOpen V)
    (hcV : Convex ℝ V) (hUV : closure U ⊆ V) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f V) {z : ℂ} (hz : z ∈ U) :
    (∫ t, (C.boundaryNormal t / (C.boundaryMap t - z)) * f (C.boundaryMap t)
      ∂circleMeasure) = f z := by
  have hztrace : z ∉ C.boundaryContour.trace := by
    intro he
    exact (C.boundaryContour_trace_subset he).2 (hU.interior_eq.symm ▸ hz)
  have he := C.boundaryContour.cauchy_formula_convex hV hcV
    (C.boundaryContour_trace_subset.trans (frontier_subset_closure.trans hUV)) hf
    (hUV (subset_closure hz)) hztrace
  rw [C.boundaryContour_index_inside hU hz, one_mul] at he
  have hi := C.boundaryContour_integral (fun w => f w / (w - z))
  simp only [smul_eq_mul] at hi
  have hmul (a b c : ℂ) : a * (b / c) = a * b / c := by ring
  have hmul' (a b c : ℂ) : a * (b / c) = (a / c) * b := by ring
  simp_rw [hmul] at hi
  rw [hi] at he
  convert he using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by ring

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Faber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Faber. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

open Boundary

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

lemma physicalCoefficient_inside (hU : IsOpen U) (j : ℤ) {z : ℂ} (hz : z ∈ U) :
    C.physicalCoefficient j z =
      ∫ t, (circleCoordinate t)^j * (C.boundaryNormal t /
        (C.boundaryMap t - z)) ∂circleMeasure := by
  have hsub : closedBall (0 : ℂ) 2 \ ball 0 1 ⊆ {t | C.radius < ‖t‖} := by
    intro t ht
    exact C.radius_lt_one.trans_le (not_lt.mp (mt mem_ball_zero_iff.mpr ht.2))
  have hn : ∀ t ∈ closedBall (0 : ℂ) 2 \ ball 0 1, C.G t - z ≠ 0 := by
    intro t ht
    exact sub_ne_zero.mpr (fun he => C.exterior_value_not_mem hU
      (not_lt.mp (mt mem_ball_zero_iff.mpr ht.2)) (he ▸ hz))
  have hs : ball (0 : ℂ) 2 \ closedBall 0 1 ⊆ closedBall (0 : ℂ) 2 \ ball 0 1 :=
    fun t ht => ⟨ball_subset_closedBall ht.1, fun he => ht.2 (ball_subset_closedBall he)⟩
  have he := integral_laurent_deform (f := fun t => t * deriv C.G t / (C.G t - z))
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 2)
    ((continuousOn_id.mul (C.analytic.deriv.continuousOn.mono hsub)).div
      ((C.analytic.continuousOn.mono hsub).sub continuousOn_const) hn)
    ((differentiableOn_id.mul (C.analytic.deriv.differentiableOn.mono (hs.trans hsub))).div
      ((C.analytic.differentiableOn.mono (hs.trans hsub)).sub_const z)
      (fun t ht => hn t (hs ht))) j
  simpa only [ofReal_ofNat, ofReal_one, one_mul, smul_eq_mul, physicalCoefficient,
    boundaryNormal, boundaryMap, ContinuousMap.coe_mk] using he

lemma physicalCoefficient_inside_neg (hU : IsOpen U) {z : ℂ} (hz : z ∈ U)
    {n : ℕ} (hn : n ≠ 0) : C.physicalCoefficient (-(n : ℤ)) z = 0 := by
  rw [C.physicalCoefficient_inside hU _ hz]
  simp_rw [← C.reciprocalCauchy_boundary hU hz, zpow_neg, zpow_natCast, ← inv_pow]
  rw [integral_holomorphic_inverse_circleCoordinate (f := fun u => u^n * C.reciprocalCauchy z u)
    ((differentiableOn_id.pow n).mul (C.differentiableOn_reciprocalCauchy hU hz))]
  simp [zero_pow hn]

lemma physicalCoefficient_inside_zero (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) :
    C.physicalCoefficient 0 z = 1 := by
  rw [C.physicalCoefficient_inside hU _ hz]
  simp_rw [zpow_zero, one_mul, ← C.reciprocalCauchy_boundary hU hz]
  rw [integral_holomorphic_inverse_circleCoordinate (C.differentiableOn_reciprocalCauchy hU hz)]
  simp [reciprocalCauchy, reciprocalDenominator, C.leading_ne_zero]

lemma physicalCoefficient_closed_neg (hU : IsOpen U) {z : ℂ} (hz : z ∈ closure U)
    {n : ℕ} (hn : n ≠ 0) : C.physicalCoefficient (-(n : ℤ)) z = 0 := by
  exact (Set.EqOn.of_subset_closure
    (fun _ hy => C.physicalCoefficient_inside_neg hU hy hn)
    ((C.differentiableOn_physicalCoefficient _).continuousOn.mono C.closure_subset_outerDomain)
    continuousOn_const subset_closure (Subset.refl _)) hz

lemma physicalCoefficient_closed_zero (hU : IsOpen U) {z : ℂ} (hz : z ∈ closure U) :
    C.physicalCoefficient 0 z = 1 := by
  exact (Set.EqOn.of_subset_closure
    (fun _ hy => C.physicalCoefficient_inside_zero hU hy)
    ((C.differentiableOn_physicalCoefficient _).continuousOn.mono C.closure_subset_outerDomain)
    continuousOn_const subset_closure (Subset.refl _)) hz

lemma correctionMoment_outer (j : ℕ) {v : ℂ} (hv : v ∈ C.reciprocalDisk) :
    (∫ t, (2 * circleCoordinate t)^j *
      C.correction (2 * circleCoordinate t)⁻¹ v ∂circleMeasure) = C.correctionMoment j v := by
  have hs : closedBall (0 : ℂ) 2 \ ball 0 1 ⊆ {t | C.radius < ‖t‖} := by
    intro t ht
    exact C.radius_lt_one.trans_le (not_lt.mp (mt mem_ball_zero_iff.mpr ht.2))
  have hn : ∀ t ∈ closedBall (0 : ℂ) 2 \ ball 0 1, t ≠ 0 := fun t ht =>
    norm_pos_iff.mp (C.radius_pos.trans (hs ht))
  have hi : MapsTo (fun t : ℂ => t⁻¹) (closedBall 0 2 \ ball 0 1) C.reciprocalDisk :=
    fun t ht => C.inverse_mem_reciprocalDisk (hs ht)
  have hd : DifferentiableOn ℂ (fun t : ℂ => C.correction t⁻¹ v) (closedBall 0 2 \ ball 0 1) :=
    (C.differentiableOn_correction_left hv).comp (differentiableOn_id.inv hn) hi
  have he := integral_laurent_deform (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) ≤ 2) hd.continuousOn
    (hd.mono (fun t ht => ⟨ball_subset_closedBall ht.1, fun he => ht.2 (ball_subset_closedBall he)⟩)) (j : ℤ)
  simpa only [smul_eq_mul, ofReal_ofNat, ofReal_one, one_mul, zpow_natCast, correctionMoment] using he

lemma circle_model_moment (j : ℕ) {w : ℂ} (hw : ‖w‖ < 2) :
    (∫ t, (2 * circleCoordinate t)^j *
      (2 * circleCoordinate t / (2 * circleCoordinate t - w)) ∂circleMeasure) = w^j := by
  have hc := Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (f := fun z : ℂ => z^j) countable_empty (mem_ball_zero_iff.mpr hw)
    (continuous_id.pow j).continuousOn
    (fun z _ => (differentiableAt_id.pow j))
  have he := integral_scaled_coordinate_cauchy (fun z : ℂ => (z-w)⁻¹ • z^j)
    (by norm_num : (0 : ℝ) < 2)
  rw [hc] at he
  convert he using 1
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [ofReal_ofNat, smul_eq_mul, div_eq_mul_inv]
  ring

lemma physicalCoefficient_boundary (j : ℕ) {w : ℂ} (hw : ‖w‖ = 1) :
    C.physicalCoefficient (j : ℤ) (C.G w) = w^j + C.correctionMoment j w⁻¹ := by
  have hwC : C.radius < ‖w‖ := hw.symm ▸ C.radius_lt_one
  have hdiff (t : CircleSpace) : 2 * circleCoordinate t ≠ w := by
    intro he
    have hnorm := congrArg norm he
    rw [norm_mul, norm_ofNat, norm_circleCoordinate, mul_one, hw] at hnorm
    norm_num at hnorm
  have hsplit (t : CircleSpace) :
      (2 * circleCoordinate t)^j *
        ((2 * circleCoordinate t * deriv C.G (2 * circleCoordinate t)) /
          (C.G (2 * circleCoordinate t) - C.G w)) =
      (2 * circleCoordinate t)^j * (2 * circleCoordinate t / (2 * circleCoordinate t - w)) +
      (2 * circleCoordinate t)^j * C.correction (2 * circleCoordinate t)⁻¹ w⁻¹ := by
    rw [C.correction_eq (C.twice_coordinate_mem t) hwC (hdiff t)]
    ring
  have hc1 : Continuous (fun t : CircleSpace =>
      (2 * circleCoordinate t)^j * (2 * circleCoordinate t / (2 * circleCoordinate t - w))) :=
    ((continuous_const.mul circleCoordinate.continuous).pow j).mul
      ((continuous_const.mul circleCoordinate.continuous).div
        ((continuous_const.mul circleCoordinate.continuous).sub continuous_const)
        (fun t => sub_ne_zero.mpr (hdiff t)))
  have hc2 : Continuous (fun t : CircleSpace =>
      (2 * circleCoordinate t)^j * C.correction (2 * circleCoordinate t)⁻¹ w⁻¹) :=
    ((continuous_const.mul circleCoordinate.continuous).pow j).mul
      (C.continuousOn_correction.comp_continuous
        (((continuous_const.mul circleCoordinate.continuous).inv₀
          (fun t => mul_ne_zero (by norm_num) (circleCoordinate_ne_zero t))).prodMk continuous_const)
        (fun t => ⟨C.inverse_mem_reciprocalDisk (C.twice_coordinate_mem t), C.inverse_mem_reciprocalDisk hwC⟩))
  simp only [physicalCoefficient, zpow_natCast, hsplit]
  rw [integral_add (hc1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hc2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    circle_model_moment j (by rw [hw]; norm_num), C.correctionMoment_outer j (C.inverse_mem_reciprocalDisk hwC)]

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.LaurentSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Laurent Split. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

lemma exists_finite_principal_part {V : Set ℂ} (hV : IsOpen V) (h0V : (0 : ℂ) ∈ V)
    (n : ℕ) {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h V) :
    ∃ (p : Polynomial ℂ) (q : ℂ → ℂ), DifferentiableOn ℂ q V ∧ q 0 = 0 ∧
      ∀ t : ℂ, t ≠ 0 → t⁻¹ ∈ V → t^n * h t⁻¹ = p.eval t + q t⁻¹ := by
  induction n generalizing h with
  | zero =>
    refine ⟨Polynomial.C (h 0), fun u => h u - h 0, hh.sub_const _, sub_self _, ?_⟩
    intro t ht htV
    simp
  | succ n ih =>
    have hd : DifferentiableOn ℂ (dslope h 0) V :=
      (differentiableOn_dslope (hV.mem_nhds h0V)).mpr hh
    obtain ⟨p,q,hq,hq0,he⟩ := ih hd
    refine ⟨Polynomial.C (h 0) * Polynomial.X^(n+1) + p, q, hq, hq0, ?_⟩
    intro t ht htV
    have hh' : h t⁻¹ = h 0 + t⁻¹ * dslope h 0 t⁻¹ := by
      rw [dslope_of_ne _ (inv_ne_zero ht), slope_def_field]
      simp only [sub_zero]
      field_simp
      ring
    rw [hh', mul_add, pow_succ]
    have hp : t^n * t * (t⁻¹ * dslope h 0 t⁻¹) = t^n * dslope h 0 t⁻¹ := by
      field_simp
    rw [hp, he t ht htV]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, pow_succ]
    ring

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

lemma power_finite_principal_part (n : ℕ) :
    ∃ (p : Polynomial ℂ) (q : ℂ → ℂ), DifferentiableOn ℂ q C.reciprocalDisk ∧ q 0 = 0 ∧
      ∀ t : ℂ, C.radius < ‖t‖ → (C.G t)^n = p.eval t + q t⁻¹ := by
  have hh : DifferentiableOn ℂ (fun u => (C.leading + u * C.regular u)^n) C.reciprocalDisk :=
    ((differentiableOn_const _).add
      (differentiableOn_id.mul C.regular_analytic.differentiableOn)).pow n
  obtain ⟨p,q,hq,hq0,he⟩ := exists_finite_principal_part isOpen_ball
    (mem_ball_self (inv_pos.mpr C.radius_pos)) n hh
  refine ⟨p,q,hq,hq0,fun t ht => ?_⟩
  have ht0 := norm_pos_iff.mp (C.radius_pos.trans ht)
  rw [← he t ht0 (C.inverse_mem_reciprocalDisk ht), ← mul_pow, C.laurent t ht]
  congr 1
  field_simp

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.PhysicalFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Fourier. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace CrouzeixHilbert

namespace Boundary

lemma kernelLp_complex_smul {k : ℕ} (m : CircleKernel) (c : ℂ) (u : BoundaryL2 k) :
    kernelLp m (c • u) = c • kernelLp m u := by
  apply Lp.ext
  filter_upwards [kernelLp_apply_ae m (c • u), kernelLp_apply_ae m u,
    Lp.coeFn_smul c (kernelLp m u)] with x hcu hu hsmul
  simp only [hcu, hsmul, Pi.smul_apply, hu, kernelApply]
  calc
    _ = ∫ y, c • (m (x,y) • u y) ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c u] with y hy
      rw [hy]
      exact smul_comm (m (x,y)) c (u y)
    _ = _ := integral_smul c _

@[simp] lemma boundaryField_add {k : ℕ} (F G : C(CircleSpace, Coeff k)) :
    boundaryField (F+G) = boundaryField F + boundaryField G := by
  apply Lp.ext
  filter_upwards [boundaryField_apply_ae (F+G), boundaryField_apply_ae F, boundaryField_apply_ae G,
    Lp.coeFn_add (boundaryField F) (boundaryField G)] with t hfg hf hg hsum
  simp only [hfg, hsum, Pi.add_apply, hf, hg, ContinuousMap.add_apply]
  exact (toHSCLM k).map_add _ _

@[simp] lemma boundaryField_smul {k : ℕ} (c : ℂ) (F : C(CircleSpace, Coeff k)) :
    boundaryField (c • F) = c • boundaryField F := by
  apply Lp.ext
  filter_upwards [boundaryField_apply_ae (c • F), boundaryField_apply_ae F,
    Lp.coeFn_smul c (boundaryField F)] with t hcf hf hs
  simp only [hcf, hs, Pi.smul_apply, hf, ContinuousMap.smul_apply]
  exact (toHSCLM k).map_smul _ _

@[simp] lemma boundaryField_zero {k : ℕ} : boundaryField (0 : C(CircleSpace, Coeff k)) = 0 := by
  apply Lp.ext
  filter_upwards [boundaryField_apply_ae (0 : C(CircleSpace, Coeff k)), Lp.coeFn_zero (E := HS k) (p := 2) circleMeasure] with t he hz
  rw [he, hz]
  exact (toHSCLM k).map_zero

end Boundary

namespace Conformal.ExteriorCollar

open Boundary

variable {U : Set ℂ} (C : ExteriorCollar U)

lemma boundaryKernel_complex (w t : CircleSpace) :
    (C.boundaryKernel (w,t) : ℂ) = 1 + C.boundaryCorrection (w,t) + conj (C.boundaryCorrection (w,t)) := by
  change (((1 : ℝ) + 2 * (C.boundaryCorrection (w,t)).re : ℝ) : ℂ) = _
  apply Complex.ext <;> simp [add_re, add_im, mul_re, mul_im]
  ring

lemma boundaryKernel_moment {j : ℕ} (hj : j ≠ 0) (w : CircleSpace) :
    (∫ t, (C.boundaryKernel (w,t) : ℂ) * (circleCoordinate t)^j ∂circleMeasure) =
      C.correctionMoment j (circleCoordinate w)⁻¹ := by
  have hb : Continuous (fun t => C.boundaryCorrection (w,t)) :=
    C.boundaryCorrection.continuous.comp (continuous_const.prodMk continuous_id)
  have hp := circleCoordinate.continuous.pow j
  have hi1 : Integrable (fun t => (circleCoordinate t)^j) circleMeasure :=
    hp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun t => (circleCoordinate t)^j * C.boundaryCorrection (w,t)) circleMeasure :=
    (hp.mul hb).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi3 : Integrable (fun t => conj (C.boundaryCorrection (w,t)) * (circleCoordinate t)^j) circleMeasure :=
    ((continuous_conj.comp hb).mul hp).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hz : (∫ t : CircleSpace, ((circleCoordinate t)⁻¹)^j * C.boundaryCorrection (w,t)
      ∂circleMeasure) = 0 := by
    change (∫ t, ((circleCoordinate t)⁻¹)^j *
      C.correction (circleCoordinate t)⁻¹ (circleCoordinate w)⁻¹ ∂circleMeasure) = 0
    rw [integral_holomorphic_inverse_circleCoordinate
      (f := fun v => v^j * C.correction v (circleCoordinate w)⁻¹)
      ((differentiableOn_id.pow j).mul
        ((C.differentiableOn_correction_left (C.circle_inverse_mem w)).mono C.closed_unit_subset_reciprocalDisk))]
    simp
  have h3 : (∫ t, conj (C.boundaryCorrection (w,t)) * (circleCoordinate t)^j ∂circleMeasure) = 0 := by
    have he := congrArg conj hz
    rw [← integral_conj] at he
    simp only [map_zero] at he
    convert he using 1
    apply integral_congr_ae
    filter_upwards [] with t
    rw [map_mul, map_pow, Complex.inv_eq_conj (norm_circleCoordinate t), conj_conj]
    ring
  have h1 : (∫ t : CircleSpace, (circleCoordinate t)^j ∂circleMeasure) = 0 := by
    rw [integral_holomorphic_circleCoordinate (f := fun z => z^j) (differentiableOn_id.pow j)]
    exact zero_pow hj
  have he (t : CircleSpace) : (C.boundaryKernel (w,t) : ℂ) * (circleCoordinate t)^j =
      (circleCoordinate t)^j + (circleCoordinate t)^j * C.boundaryCorrection (w,t) +
        conj (C.boundaryCorrection (w,t)) * (circleCoordinate t)^j := by
    rw [C.boundaryKernel_complex]; ring
  simp_rw [he]
  have hi12 : Integrable (fun t => (circleCoordinate t)^j + (circleCoordinate t)^j *
      C.boundaryCorrection (w,t)) circleMeasure := hi1.add hi2
  rw [integral_add hi12 hi3, integral_add hi1 hi2, h1, h3, zero_add, add_zero]
  rfl

lemma boundaryCauchy_complex_smul (hc : Convex ℝ U) {k : ℕ} (c : ℂ) (u : BoundaryL2 k) :
    boundaryCauchy (C.boundaryOperator hc k) (c • u) =
      c • boundaryCauchy (C.boundaryOperator hc k) u := by
  change fourierProjC k 0 (c • u) + fourierProjC k 1 (c • u) +
    fourierProjC k 2 (kernelLp C.boundaryKernel (fourierProjC k 1 (c • u))) =
    c • (fourierProjC k 0 u + fourierProjC k 1 u +
      fourierProjC k 2 (kernelLp C.boundaryKernel (fourierProjC k 1 u)))
  simp only [map_smul, kernelLp_complex_smul, smul_add]

lemma kernelLp_fourier_pos (hc : Convex ℝ U) {k : ℕ} (j : ℕ) (hj : j ≠ 0) (i l : Fin k) :
    C.boundaryOperator hc k (matrixFourier ((j : ℤ),i,l)) =
      boundaryField (C.correctionChannel (j,i,l)) := by
  apply Lp.ext
  filter_upwards [kernelLp_apply_ae C.boundaryKernel (matrixFourier ((j : ℤ),i,l)),
    boundaryField_apply_ae (C.correctionChannel (j,i,l))] with w hw hv
  change kernelLp C.boundaryKernel _ w = _
  rw [hw, hv]
  change (∫ t, C.boundaryKernel (w,t) • matrixFourier ((j : ℤ),i,l) t ∂circleMeasure) =
    toHS (C.correctionMoment j (circleCoordinate w)⁻¹ • Matrix.single i l (1 : ℂ))
  rw [← toHSCLM_apply, map_smul, toHSCLM_apply, toHS_single]
  calc
    _ = ∫ t, ((C.boundaryKernel (w,t) : ℂ) * (circleCoordinate t)^j) •
        EuclideanSpace.single (i,l) (1 : ℂ) ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [matrixFourier_apply_ae ((j : ℤ),i,l)] with t ht
      rw [ht, circleCoordinate_pow, mul_smul]
      rfl
    _ = _ := by rw [integral_smul_const, C.boundaryKernel_moment hj]

lemma correctionChannel_negative {k : ℕ} (a : ℕ × (Fin k × Fin k)) :
    fourierProjC k 2 (boundaryField (C.correctionChannel a)) =
      boundaryField (C.correctionChannel a) := by
  apply fourierProj_boundaryField_inverse_neg (f := fun v =>
    C.correctionMoment a.1 v • Matrix.single a.2.1 a.2.2 (1 : ℂ))
  · intro i l
    exact ((C.differentiableOn_correctionMoment a.1).mono
      C.closed_unit_subset_reciprocalDisk).mul_const _
  · simp
  · exact fun _ => rfl

lemma boundaryCauchy_matrixFourier (hU : IsOpen U) (hc : Convex ℝ U) {k : ℕ}
    (a : ℤ × (Fin k × Fin k)) :
    boundaryCauchy (C.boundaryOperator hc k) (matrixFourier a) =
      boundaryField (C.physicalChannel a) := by
  classical
  change fourierProjC k 0 (matrixFourier a) + fourierProjC k 1 (matrixFourier a) +
    fourierProjC k 2 (C.boundaryOperator hc k (fourierProjC k 1 (matrixFourier a))) = _
  simp only [fourierProj_matrixFourier, frequencyPart_zero, frequencyPart_pos]
  rcases a with ⟨j,i,l⟩
  rcases lt_trichotomy j 0 with hj|hj|hj
  · simp only [ne_of_lt hj, not_lt_of_gt hj, ↓reduceIte, map_zero, zero_add]
    have he : C.physicalChannel (j,i,l) = 0 := by
      ext t a b
      obtain ⟨n,hn⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.mpr hj.le)
      have hjn : j = -(n : ℤ) := by omega
      have hn0 : n ≠ 0 := by omega
      change C.physicalCoefficient j (C.boundaryMap t) * _ = _
      rw [hjn, C.physicalCoefficient_closed_neg hU (C.boundaryMap_mem_frontier t).1 hn0]
      simp
    rw [he, boundaryField_zero]
  · subst j
    simp only [lt_self_iff_false, ↓reduceIte, map_zero, add_zero]
    have he : C.physicalChannel (0,i,l) = matrixLaurentMonomial (0,i,l) 1 := by
      ext t a b
      change C.physicalCoefficient 0 (C.boundaryMap t) * _ = _
      rw [C.physicalCoefficient_closed_zero hU (C.boundaryMap_mem_frontier t).1]
      simp [matrixLaurentMonomial]
    rw [he, boundaryField_matrixLaurentMonomial, one_smul]
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hj.le
    have hn : n ≠ 0 := by omega
    simp only [ne_of_gt hj, hj, ↓reduceIte, zero_add]
    rw [C.kernelLp_fourier_pos hc n hn, C.correctionChannel_negative]
    have he : C.physicalChannel ((n : ℤ),i,l) =
        matrixLaurentMonomial ((n : ℤ),i,l) 1 + C.correctionChannel (n,i,l) := by
      ext t a b
      change C.physicalCoefficient (n : ℤ) (C.G (circleCoordinate t)) * _ = _
      rw [C.physicalCoefficient_boundary n (norm_circleCoordinate t)]
      simp only [ContinuousMap.add_apply, matrixLaurentMonomial, correctionChannel,
        scalarChannel, ContinuousMap.coe_mk, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul, one_mul, circleCoordinate_pow, add_mul]
    rw [he, boundaryField_add, boundaryField_matrixLaurentMonomial, one_smul]

lemma boundaryCauchy_matrixLaurentMonomial (hU : IsOpen U) (hc : Convex ℝ U) {k : ℕ}
    (a : ℤ × (Fin k × Fin k)) (c : ℂ) :
    boundaryCauchy (C.boundaryOperator hc k) (boundaryField (matrixLaurentMonomial a c)) =
      boundaryField (c • C.physicalChannel a) := by
  rw [boundaryField_matrixLaurentMonomial, C.boundaryCauchy_complex_smul,
    C.boundaryCauchy_matrixFourier hU hc, boundaryField_smul]

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.PhysicalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Projection. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace CrouzeixHilbert

namespace Boundary

lemma boundaryField_sum {k : ℕ} {ι : Type*} (s : Finset ι) (F : ι → C(CircleSpace, Coeff k)) :
    boundaryField (∑ i ∈ s, F i) = ∑ i ∈ s, boundaryField (F i) :=
  map_sum (boundaryFieldCLM k) F s

end Boundary

namespace Conformal.ExteriorCollar

open Boundary

variable {U : Set ℂ} (C : ExteriorCollar U)

lemma boundaryCauchy_polynomialCircle (hU : IsOpen U) (hc : Convex ℝ U) {k : ℕ}
    (p : Polynomial ℂ) (i l : Fin k) :
    boundaryCauchy (C.boundaryOperator hc k)
      (boundaryField (scalarChannel i l (polynomialCircle p))) =
      boundaryField (scalarChannel i l (C.physicalPolynomialTrace p)) := by
  have hp : scalarChannel i l (polynomialCircle p) =
      ∑ j ∈ Finset.range (p.natDegree+1), matrixLaurentMonomial ((j : ℤ),i,l) (p.coeff j) := by
    ext t a b
    simp only [ContinuousMap.sum_apply, Matrix.sum_apply, scalarChannel, polynomialCircle,
      ContinuousMap.coe_mk, Matrix.smul_apply, smul_eq_mul, matrixLaurentMonomial,
      Polynomial.eval_eq_sum_range, Finset.sum_mul, circleCoordinate_pow]
  have hv : scalarChannel i l (C.physicalPolynomialTrace p) =
      ∑ j ∈ Finset.range (p.natDegree+1), p.coeff j • C.physicalChannel ((j : ℤ),i,l) := by
    ext t a b
    simp only [ContinuousMap.sum_apply, Matrix.sum_apply, scalarChannel, physicalPolynomialTrace,
      physicalPolynomial, physicalChannel, ContinuousMap.coe_mk, ContinuousMap.smul_apply,
      Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
  rw [hp, hv, boundaryField_sum, map_sum, boundaryField_sum]
  exact Finset.sum_congr rfl (fun j _ => C.boundaryCauchy_matrixLaurentMonomial hU hc _ _)

lemma physicalPolynomial_inside (hU : IsOpen U) (p : Polynomial ℂ) {z : ℂ} (hz : z ∈ U) :
    C.physicalPolynomial p z = ∫ t, p.eval (circleCoordinate t) *
      (C.boundaryNormal t / (C.boundaryMap t - z)) ∂circleMeasure := by
  have hd (t : CircleSpace) : C.boundaryMap t - z ≠ 0 := by
    intro he
    exact (C.boundaryMap_mem_frontier t).2 (hU.interior_eq.symm ▸ (sub_eq_zero.mp he ▸ hz))
  have hk : Continuous (fun t => C.boundaryNormal t / (C.boundaryMap t-z)) :=
    C.boundaryNormal.continuous.div (C.boundaryMap.continuous.sub continuous_const) hd
  simp only [physicalPolynomial, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  rw [integral_finsetSum _ (fun j _ =>
    (show Continuous (fun t : CircleSpace => p.coeff j * circleCoordinate t ^ j *
      (C.boundaryNormal t / (C.boundaryMap t-z))) from
      (continuous_const.mul (circleCoordinate.continuous.pow j)).mul hk).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [C.physicalCoefficient_inside hU _ hz]
  simp only [zpow_natCast, mul_assoc, integral_const_mul]

lemma cauchy_inverse_q_zero (hU : IsOpen U) {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (closedBall 0 1)) (hq0 : q 0 = 0)
    {z : ℂ} (hz : z ∈ U) :
    (∫ t, q (circleCoordinate t)⁻¹ * (C.boundaryNormal t / (C.boundaryMap t-z))
      ∂circleMeasure) = 0 := by
  simp_rw [← C.reciprocalCauchy_boundary hU hz]
  have he := integral_holomorphic_inverse_circleCoordinate
    (hq.mul (C.differentiableOn_reciprocalCauchy hU hz))
  simpa only [Pi.mul_apply, hq0, zero_mul] using he

lemma physicalPolynomial_of_power_split (hU : IsOpen U) (p : Polynomial ℂ) (q : ℂ → ℂ)
    (hq : DifferentiableOn ℂ q C.reciprocalDisk) (hq0 : q 0 = 0) (n : ℕ)
    (hsplit : ∀ t, C.radius < ‖t‖ → (C.G t)^n = p.eval t + q t⁻¹) :
    EqOn (C.physicalPolynomial p) (fun z => z^n) (closure U) := by
  have he : EqOn (C.physicalPolynomial p) (fun z => z^n) U := by
    intro z hz
    have hcp := C.physical_cauchy_formula hU isOpen_univ (convex_univ : Convex ℝ (univ : Set ℂ))
      (subset_univ _) (differentiableOn_id.pow n) hz
    have hd (t : CircleSpace) : C.boundaryMap t - z ≠ 0 := by
      intro he
      exact (C.boundaryMap_mem_frontier t).2 (hU.interior_eq.symm ▸ (sub_eq_zero.mp he ▸ hz))
    have hk : Continuous (fun t => C.boundaryNormal t / (C.boundaryMap t-z)) :=
      C.boundaryNormal.continuous.div (C.boundaryMap.continuous.sub continuous_const) hd
    have hqc : Continuous (fun t : CircleSpace => q (circleCoordinate t)⁻¹) :=
      hq.continuousOn.comp_continuous
        (circleCoordinate.continuous.inv₀ circleCoordinate_ne_zero) C.circle_inverse_mem
    have hi1 : Integrable (fun t => p.eval (circleCoordinate t) *
        (C.boundaryNormal t / (C.boundaryMap t-z))) circleMeasure := ((polynomialCircle p).continuous.fun_mul hk).integrable_of_hasCompactSupport
      (μ := circleMeasure)
      (HasCompactSupport.of_compactSpace _)
    have hi2 := (hqc.fun_mul hk).integrable_of_hasCompactSupport (μ := circleMeasure)
      (HasCompactSupport.of_compactSpace _)
    have halg (t : CircleSpace) : C.boundaryNormal t / (C.boundaryMap t - z) * (C.boundaryMap t)^n =
        p.eval (circleCoordinate t) * (C.boundaryNormal t / (C.boundaryMap t - z)) +
        q (circleCoordinate t)⁻¹ * (C.boundaryNormal t / (C.boundaryMap t - z)) := by
      change _ * (C.G (circleCoordinate t))^n = _
      rw [hsplit _ (by rw [norm_circleCoordinate]; exact C.radius_lt_one)]
      ring
    change (∫ t, (C.boundaryNormal t / (C.boundaryMap t-z)) * (C.boundaryMap t)^n
      ∂circleMeasure) = z^n at hcp
    simp_rw [halg] at hcp
    rw [integral_add hi1 hi2, C.cauchy_inverse_q_zero hU
      (hq.mono C.closed_unit_subset_reciprocalDisk) hq0 hz, add_zero] at hcp
    exact (C.physicalPolynomial_inside hU p hz).trans hcp
  exact Set.EqOn.of_subset_closure he
    ((C.differentiableOn_physicalPolynomial p).continuousOn.mono C.closure_subset_outerDomain)
    (continuous_id.pow n).continuousOn subset_closure (Subset.refl _)

lemma boundaryCauchy_physical_power (hU : IsOpen U) (hc : Convex ℝ U) {k : ℕ}
    (n : ℕ) (i l : Fin k) :
    boundaryCauchy (C.boundaryOperator hc k)
      (boundaryField (scalarChannel i l (C.boundaryMap^n))) =
      boundaryField (scalarChannel i l (C.boundaryMap^n)) := by
  obtain ⟨p,q,hq,hq0,hsplit⟩ := C.power_finite_principal_part n
  let Q : C(CircleSpace, ℂ) := ⟨fun t => q (circleCoordinate t)⁻¹,
    hq.continuousOn.comp_continuous
      (circleCoordinate.continuous.inv₀ circleCoordinate_ne_zero) C.circle_inverse_mem⟩
  have hqz : boundaryCauchy (C.boundaryOperator hc k) (boundaryField (scalarChannel i l Q)) = 0 := by
    apply boundaryCauchy_inverse_zero (f := fun z => q z • Matrix.single i l (1 : ℂ))
    · intro a b
      exact (hq.mono C.closed_unit_subset_reciprocalDisk).mul_const _
    · simp [hq0]
    · exact fun _ => rfl
  have he : scalarChannel i l (C.boundaryMap^n) =
      scalarChannel i l (polynomialCircle p) + scalarChannel i l Q := by
    ext t a b
    change (C.G (circleCoordinate t))^n * _ = _
    rw [hsplit _ (by rw [norm_circleCoordinate]; exact C.radius_lt_one)]
    simp only [ContinuousMap.add_apply, scalarChannel, ContinuousMap.coe_mk,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, polynomialCircle, Q]
  have hpe : C.physicalPolynomialTrace p = C.boundaryMap^n := by
    ext t
    exact C.physicalPolynomial_of_power_split hU p q hq hq0 n hsplit
      (C.boundaryMap_mem_frontier t).1
  conv_lhs => rw [he]
  rw [boundaryField_add, map_add, hqz, add_zero, C.boundaryCauchy_polynomialCircle hU hc, hpe]

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.PhysicalModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Module. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace CrouzeixHilbert

namespace Boundary

lemma realCLM_eq_of_matrixLaurent {k : ℕ} {L R : BoundaryL2 k →L[ℝ] BoundaryL2 k}
    (h : ∀ a c, L (boundaryField (matrixLaurentMonomial a c)) =
      R (boundaryField (matrixLaurentMonomial a c))) : L = R := by
  have ha : L.adjoint = R.adjoint := by
    apply ContinuousLinearMap.ext
    intro v
    apply eq_of_inner_matrixLaurentMonomial
    intro a c
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, h]
  simpa only [ContinuousLinearMap.adjoint_adjoint] using
    congrArg (fun T : BoundaryL2 k →L[ℝ] BoundaryL2 k => T.adjoint) ha

lemma lpLeft_boundaryField {k : ℕ} (F V : C(CircleSpace, Coeff k))
    (hF : ∀ t, ‖F t‖ ≤ 1) :
    lpLeft F F.continuous.aestronglyMeasurable (Eventually.of_forall hF)
      (boundaryField V) = boundaryField (F*V) := by
  apply Lp.ext
  filter_upwards [lpLeft_apply_ae F F.continuous.aestronglyMeasurable (Eventually.of_forall hF)
    (boundaryField V), boundaryField_apply_ae V, boundaryField_apply_ae (F*V)] with t ht hv hfv
  rw [ht, hv, hfv, ofHS_toHS]
  rfl

lemma lpRight_boundaryField {k : ℕ} (F V : C(CircleSpace, Coeff k))
    (hF : ∀ t, ‖F t‖ ≤ 1) :
    lpRight F F.continuous.aestronglyMeasurable (Eventually.of_forall hF)
      (boundaryField V) = boundaryField (V*F) := by
  apply Lp.ext
  filter_upwards [lpRight_apply_ae F F.continuous.aestronglyMeasurable (Eventually.of_forall hF)
    (boundaryField V), boundaryField_apply_ae V, boundaryField_apply_ae (V*F)] with t ht hv hfv
  rw [ht, hv, hfv, ofHS_toHS]
  rfl

end Boundary

namespace Conformal.ExteriorCollar

open Boundary

variable {U : Set ℂ} (C : ExteriorCollar U)

lemma boundaryCauchy_polynomialTrace (hU : IsOpen U) (hc : Convex ℝ U) {k : ℕ}
    (p : Polynomial ℂ) (i l : Fin k) :
    boundaryCauchy (C.boundaryOperator hc k)
      (boundaryField (scalarChannel i l
        (C.analyticTrace (subset_univ _) p.eval p.continuous.continuousOn))) =
      boundaryField (scalarChannel i l
        (C.analyticTrace (subset_univ _) p.eval p.continuous.continuousOn)) := by
  have he : scalarChannel i l
      (C.analyticTrace (subset_univ _) p.eval p.continuous.continuousOn) =
      ∑ j ∈ Finset.range (p.natDegree+1), p.coeff j • scalarChannel i l (C.boundaryMap^j) := by
    ext t a b
    simp only [analyticTrace, scalarChannel, ContinuousMap.coe_mk, ContinuousMap.sum_apply,
      Matrix.sum_apply, ContinuousMap.smul_apply, Matrix.smul_apply, ContinuousMap.pow_apply,
      Polynomial.eval_eq_sum_range, Finset.sum_mul, smul_eq_mul, mul_assoc]
  rw [he, boundaryField_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [boundaryField_smul, C.boundaryCauchy_complex_smul, C.boundaryCauchy_physical_power hU hc]

lemma boundaryCauchy_analyticTrace (hU : IsOpen U) (hc : Convex ℝ U)
    (hb : Bornology.IsBounded U) {V : Set ℂ} (hV : IsOpen V) (hUV : closure U ⊆ V)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f V) {k : ℕ} (i l : Fin k) :
    boundaryCauchy (C.boundaryOperator hc k)
      (boundaryField (scalarChannel i l (C.analyticTrace hUV f hf.continuousOn))) =
      boundaryField (scalarChannel i l (C.analyticTrace hUV f hf.continuousOn)) := by
  obtain ⟨p,hp⟩ := exists_polynomial_tendstoUniformlyOn hb.isCompact_closure hc.closure hV hUV hf
  let Fn (n : ℕ) := scalarChannel i l
    (C.analyticTrace (subset_univ _) (p n).eval (p n).continuous.continuousOn)
  let F := scalarChannel i l (C.analyticTrace hUV f hf.continuousOn)
  have ht : Tendsto Fn atTop (𝓝 F) := by
    have hs : TendstoUniformly (fun n t => (p n).eval (C.boundaryMap t))
        (fun t => f (C.boundaryMap t)) atTop := by
      have he : C.boundaryMap ⁻¹' closure U = univ :=
        eq_univ_of_forall (fun t => (C.boundaryMap_mem_frontier t).1)
      simpa only [he, tendstoUniformlyOn_univ, Function.comp_def] using
        hp.comp C.boundaryMap
    have hct : Tendsto (fun n => C.analyticTrace (subset_univ _) (p n).eval
        (p n).continuous.continuousOn) atTop (𝓝 (C.analyticTrace hUV f hf.continuousOn)) :=
      ContinuousMap.tendsto_iff_tendstoUniformly.mpr hs
    let T : ℂ →L[ℂ] Coeff k := (ContinuousLinearMap.id ℂ ℂ).smulRight (Matrix.single i l 1)
    exact ((ContinuousLinearMap.compLeftContinuous ℂ CircleSpace T).continuous.tendsto _).comp hct
  have hlt := ((boundaryFieldCLM k).continuous.tendsto F).comp ht
  have hrt := (boundaryCauchy (C.boundaryOperator hc k)).continuous.tendsto _ |>.comp hlt
  have heq : ∀ n, boundaryCauchy (C.boundaryOperator hc k) (boundaryFieldCLM k (Fn n)) =
      boundaryFieldCLM k (Fn n) := fun n => C.boundaryCauchy_polynomialTrace hU hc (p n) i l
  simp only [Function.comp_def, heq] at hrt
  exact tendsto_nhds_unique hrt hlt

lemma boundaryCauchy_matrixAnalyticTrace (hU : IsOpen U) (hc : Convex ℝ U)
    (hb : Bornology.IsBounded U) {V : Set ℂ} (hV : IsOpen V) (hUV : closure U ⊆ V)
    {k : ℕ} {f : ℂ → Coeff k} (hf : EntrywiseHolomorphic V f) :
    boundaryCauchy (C.boundaryOperator hc k)
      (boundaryField (C.matrixAnalyticTrace hUV f hf.continuousOn)) =
      boundaryField (C.matrixAnalyticTrace hUV f hf.continuousOn) := by
  classical
  have he : C.matrixAnalyticTrace hUV f hf.continuousOn =
      ∑ i : Fin k, ∑ l : Fin k,
        scalarChannel i l (C.analyticTrace hUV (fun z => f z i l) (hf i l).continuousOn) := by
    ext t a b
    simp only [matrixAnalyticTrace, scalarChannel, analyticTrace, ContinuousMap.coe_mk,
      ContinuousMap.sum_apply, Matrix.smul_single, smul_eq_mul, mul_one]
    exact congrArg (fun M : Coeff k => M a b) (Matrix.matrix_eq_sum_single (f (C.boundaryMap t)))
  rw [he, boundaryField_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [boundaryField_sum, map_sum]
  exact Finset.sum_congr rfl (fun l _ => C.boundaryCauchy_analyticTrace hU hc hb hV hUV (hf i l) i l)

lemma physicalRepresentative_trace {k : ℕ} (a : ℤ × (Fin k × Fin k)) (c : ℂ) :
    C.matrixAnalyticTrace C.closure_subset_outerDomain (C.physicalRepresentative a c)
      (C.physicalRepresentative_holomorphic a c).continuousOn = c • C.physicalChannel a := by
  ext t i j
  simp only [matrixAnalyticTrace, physicalRepresentative, physicalChannel, scalarChannel,
    ContinuousMap.coe_mk, ContinuousMap.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc]

lemma boundaryCauchy_left_module (hU : IsOpen U) (hc : Convex ℝ U)
    (hb : Bornology.IsBounded U) {V : Set ℂ} (hV : IsOpen V) (hUV : closure U ⊆ V)
    {k : ℕ} {f : ℂ → Coeff k} (hf : EntrywiseHolomorphic V f)
    (hF : ∀ t, ‖C.matrixAnalyticTrace hUV f hf.continuousOn t‖ ≤ 1) :
    let F := C.matrixAnalyticTrace hUV f hf.continuousOn
    let M := C.boundaryOperator hc k
    (boundaryCauchy M).comp ((lpLeft F F.continuous.aestronglyMeasurable
      (Eventually.of_forall hF)).comp (boundaryCauchy M)) =
    (lpLeft F F.continuous.aestronglyMeasurable (Eventually.of_forall hF)).comp (boundaryCauchy M) := by
  dsimp only
  apply realCLM_eq_of_matrixLaurent
  intro a c
  simp only [ContinuousLinearMap.comp_apply, C.boundaryCauchy_matrixLaurentMonomial hU hc]
  rw [lpLeft_boundaryField (C.matrixAnalyticTrace hUV f hf.continuousOn) (c • C.physicalChannel a) hF]
  let W := V ∩ C.outerDomain
  have hw : closure U ⊆ W := fun z hz => ⟨hUV hz, C.closure_subset_outerDomain hz⟩
  have hprod : EntrywiseHolomorphic W (fun z => f z * C.physicalRepresentative a c z) := by
    intro i j
    simp only [Matrix.mul_apply]
    apply DifferentiableOn.fun_sum
    intro l _
    exact ((hf i l).mono inter_subset_left).fun_mul
      ((C.physicalRepresentative_holomorphic a c l j).mono inter_subset_right)
  have he : C.matrixAnalyticTrace hUV f hf.continuousOn * (c • C.physicalChannel a) =
      C.matrixAnalyticTrace hw (fun z => f z * C.physicalRepresentative a c z) hprod.continuousOn := by
    rw [← C.physicalRepresentative_trace]
    rfl
  rw [he]
  exact C.boundaryCauchy_matrixAnalyticTrace hU hc hb (hV.inter C.isOpen_outerDomain) hw hprod

lemma boundaryCauchy_right_module (hU : IsOpen U) (hc : Convex ℝ U)
    (hb : Bornology.IsBounded U) {V : Set ℂ} (hV : IsOpen V) (hUV : closure U ⊆ V)
    {k : ℕ} {f : ℂ → Coeff k} (hf : EntrywiseHolomorphic V f)
    (hF : ∀ t, ‖C.matrixAnalyticTrace hUV f hf.continuousOn t‖ ≤ 1) :
    let F := C.matrixAnalyticTrace hUV f hf.continuousOn
    let M := C.boundaryOperator hc k
    (boundaryCauchy M).comp ((lpRight F F.continuous.aestronglyMeasurable
      (Eventually.of_forall hF)).comp (boundaryCauchy M)) =
    (lpRight F F.continuous.aestronglyMeasurable (Eventually.of_forall hF)).comp (boundaryCauchy M) := by
  dsimp only
  apply realCLM_eq_of_matrixLaurent
  intro a c
  simp only [ContinuousLinearMap.comp_apply, C.boundaryCauchy_matrixLaurentMonomial hU hc]
  rw [lpRight_boundaryField (C.matrixAnalyticTrace hUV f hf.continuousOn) (c • C.physicalChannel a) hF]
  let W := V ∩ C.outerDomain
  have hw : closure U ⊆ W := fun z hz => ⟨hUV hz, C.closure_subset_outerDomain hz⟩
  have hprod : EntrywiseHolomorphic W (fun z => C.physicalRepresentative a c z * f z) := by
    intro i j
    simp only [Matrix.mul_apply]
    apply DifferentiableOn.fun_sum
    intro l _
    exact ((C.physicalRepresentative_holomorphic a c i l).mono inter_subset_right).fun_mul
      ((hf l j).mono inter_subset_left)
  have he : (c • C.physicalChannel a) * C.matrixAnalyticTrace hUV f hf.continuousOn =
      C.matrixAnalyticTrace hw (fun z => C.physicalRepresentative a c z * f z) hprod.continuousOn := by
    rw [← C.physicalRepresentative_trace]
    rfl
  rw [he]
  exact C.boundaryCauchy_matrixAnalyticTrace hU hc hb (hV.inter C.isOpen_outerDomain) hw hprod

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.AngularTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular Transport. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped InnerProductSpace

namespace CrouzeixHilbert.Conformal

open Boundary

lemma angular_derivative_real_nonneg {g : ℂ → ℂ} {z : ℂ} (hz : ‖z‖ = 1)
    (hga : DifferentiableAt ℂ g z) (hnt : ∀ w, ‖w‖ = 1 → ‖g w‖ = 1)
    (hmax : IsLocalMaxOn (fun w => ‖g w‖^2) (closedBall 0 1) z) :
    (z * deriv g z / g z).im = 0 ∧ 0 ≤ (z * deriv g z / g z).re := by
  have hgz : ‖g z‖ = 1 := hnt z hz
  have hinv : (g z)⁻¹ = conj (g z) := Complex.inv_eq_conj hgz
  have hc : HasDerivAt (fun t : ℝ => g (z * circleMap 0 1 t)) ((z * I) * deriv g z) 0 := by
    have hp : HasDerivAt (fun t : ℝ => z * circleMap 0 1 t) (z * I) 0 := by
      simpa [circleMap_zero] using (hasDerivAt_circleMap 0 1 0).const_mul z
    have hg' : HasDerivAt g (deriv g z) (z * circleMap 0 1 (0 : ℝ)) := by
      simpa [circleMap_zero] using hga.hasDerivAt
    simpa [Function.comp_def, mul_comm] using (hg'.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0 hp
  have hc0 : ∀ t : ℝ, ‖g (z * circleMap 0 1 t)‖ ^ 2 = 1 := by
    intro t
    rw [hnt _ (by rw [norm_mul, hz]; simp), one_pow]
  have hd0 := (hc.norm_sq.congr_of_eventuallyEq (Eventually.of_forall (fun t => (hc0 t).symm))).unique
    (hasDerivAt_const (0 : ℝ) (1 : ℝ))
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply] at hd0
  simp only [circleMap_zero, ofReal_one, ofReal_zero, zero_mul, exp_zero, mul_one] at hd0
  have he0 : (z * deriv g z * conj (g z)).im = 0 := by
    have halg : (((z * I) * deriv g z) * conj (g z)).re =
        -(z * deriv g z * conj (g z)).im := by
      simp only [Complex.mul_re, Complex.mul_im, I_re, I_im, mul_zero, mul_one]
      ring
    change 2 * (((z * I) * deriv g z) * conj (g z)).re = 0 at hd0
    rw [halg] at hd0
    linarith
  have hdir := hmax.hasFDerivWithinAt_nonpos
    (hga.hasDerivAt.hasFDerivAt.restrictScalars ℝ).norm_sq.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset
      ((convex_closedBall (0 : ℂ) (1 : ℝ)).segment_subset
        (mem_closedBall_zero_iff.mpr hz.le) (mem_closedBall_self zero_le_one)))
  simp only [ContinuousLinearMap.comp_apply, smul_apply] at hdir
  simp only [innerSL_apply_apply] at hdir
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply] at hdir
  simp only [two_smul, zero_sub] at hdir
  change (((-z) * deriv g z) * conj (g z)).re +
    (((-z) * deriv g z) * conj (g z)).re ≤ 0 at hdir
  simp only [neg_mul, neg_re] at hdir
  rw [div_eq_mul_inv, hinv]
  exact ⟨he0, by linarith⟩

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

lemma angularJacobian_real_nonneg (t : CircleSpace) :
    (C.angularJacobian R t).im = 0 ∧ 0 ≤ (C.angularJacobian R t).re := by
  let g := R.f ∘ C.G
  have ht : C.radius < ‖circleCoordinate t‖ := by rw [norm_circleCoordinate]; exact C.radius_lt_one
  have hfg : DifferentiableAt ℂ R.f (C.G (circleCoordinate t)) :=
    (R.analytic_f _ (R.closure_subset_domain (C.boundaryMap_mem_frontier t).1)).differentiableAt
  have hg : DifferentiableAt ℂ g (circleCoordinate t) :=
    hfg.comp (circleCoordinate t) (C.analytic _ ht).differentiableAt
  have hn : ∀ w, ‖w‖ = 1 → ‖g w‖ = 1 := fun w hw => R.boundary_norm _
    (C.boundary.mapsTo (mem_sphere_zero_iff_norm.mpr hw))
  have hmax : IsLocalMaxOn (fun w => ‖g w‖^2) (closedBall 0 1) (circleCoordinate t) := by
    filter_upwards [nhdsWithin_le_nhds (C.parameter_open.mem_nhds ht), self_mem_nhdsWithin] with w hw hw1
    rw [hn _ (norm_circleCoordinate t), one_pow]
    have hwle : ‖g w‖ ≤ 1 := by
      rcases (mem_closedBall_zero_iff.mp hw1).eq_or_lt with h|h
      · exact (hn w h).le
      · exact (mem_ball_zero_iff.mp (R.bijective_f.mapsTo (C.inside ⟨hw,h⟩))).le
    nlinarith [norm_nonneg (g w)]
  have hp := angular_derivative_real_nonneg (norm_circleCoordinate t) hg hn hmax
  have hd : deriv g (circleCoordinate t) = deriv R.f (C.G (circleCoordinate t)) *
      deriv C.G (circleCoordinate t) :=
    deriv_comp _ (R.analytic_f _ (R.closure_subset_domain (C.boundaryMap_mem_frontier t).1)).differentiableAt
      (C.analytic _ ht).differentiableAt
  rw [hd] at hp
  have he : C.angularJacobian R t = circleCoordinate t *
      (deriv R.f (C.G (circleCoordinate t)) * deriv C.G (circleCoordinate t)) / g (circleCoordinate t) := by
    change circleCoordinate t * deriv C.G (circleCoordinate t) *
      deriv R.f (C.G (circleCoordinate t)) / R.f (C.G (circleCoordinate t)) = _
    dsimp only [g, Function.comp_def]
    ring
  rw [he]
  exact hp

lemma physical_integral_zero (hc : Convex ℝ U) {V : Set ℂ}
    (hV : IsOpen V) (hUV : closure U ⊆ V) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g V) :
    (∫ t, C.boundaryNormal t * g (C.boundaryMap t) ∂circleMeasure) = 0 := by
  have hs := null_homology_integral (fun _ : Fin 1 => C.boundaryContour)
    (fun _ => (1 : ℂ)) hV (fun _ => C.boundaryContour_trace_subset.trans
      (frontier_subset_closure.trans hUV))
    (U := V) (fun (w : ℂ) (hw : w ∉ V) => by
      simpa using C.boundaryContour_index_outside hc (z := w)
        (fun hwc => hw (hUV hwc))) hg
  simp only [Fin.sum_univ_one, one_smul] at hs
  change (∫ t, C.boundaryNormal t • g (C.boundaryMap t) ∂circleMeasure) = 0
  rw [← C.boundaryContour_integral g]
  exact hs

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.AngularMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular Moments. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

open Boundary

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

lemma interiorBoundary_ne_zero (t : CircleSpace) : C.interiorBoundary R t ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [C.norm_interiorBoundary]; exact one_ne_zero)

lemma integral_angularJacobian_pow_succ (hc : Convex ℝ U) (n : ℕ) :
    (∫ t, C.angularJacobian R t * (C.interiorBoundary R t)^(n+1) ∂circleMeasure) = 0 := by
  have hz := C.physical_integral_zero hc R.isOpen_domain R.closure_subset_domain
    (R.analytic_f.deriv.differentiableOn.fun_mul (R.analytic_f.differentiableOn.pow n))
  convert hz using 1
  apply integral_congr_ae
  filter_upwards [] with t
  change (C.boundaryNormal t * deriv R.f (C.boundaryMap t) / C.interiorBoundary R t) *
    C.interiorBoundary R t ^ (n+1) = C.boundaryNormal t *
      (deriv R.f (C.boundaryMap t) * C.interiorBoundary R t ^ n)
  rw [pow_succ]
  field_simp [C.interiorBoundary_ne_zero R t]

lemma integral_angularJacobian (hU : IsOpen U) (hc : Convex ℝ U) :
    (∫ t, C.angularJacobian R t ∂circleMeasure) = 1 := by
  let a := R.h 0
  have haU : a ∈ U := R.h_zero_mem
  have ha : a ∈ R.domain := R.closure_subset_domain (subset_closure haU)
  have hfa : R.f a = 0 := R.f_h_zero
  let g := dslope R.f a
  have hg : AnalyticOnNhd ℂ g R.domain :=
    ((differentiableOn_dslope (R.isOpen_domain.mem_nhds ha)).mpr
      R.analytic_f.differentiableOn).analyticOnNhd R.isOpen_domain
  have hgn : ∀ z ∈ R.domain, g z ≠ 0 := by
    intro z hz
    by_cases he : z = a
    · subst z
      simpa only [g, dslope_same] using deriv_ne_zero_of_injOn R.isOpen_domain R.analytic_f.differentiableOn R.injective_f ha
    · dsimp only [g]
      rw [dslope_of_ne _ he, slope_def_module, hfa, sub_zero, smul_eq_mul]
      exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr he))
        (fun hh => he (R.injective_f hz ha (hh.trans hfa.symm)))
  have hfgg : ∀ z, (z-a) * g z = R.f z := fun z => by
    simpa only [smul_eq_mul, hfa, sub_zero] using sub_smul_dslope R.f a z
  have hd : ∀ z ∈ R.domain, deriv R.f z = g z + (z-a) * deriv g z := by
    intro z hz
    have heq : (fun w => (w-a) * g w) = R.f := funext hfgg
    have ht := ((hasDerivAt_id z).sub_const a).mul (hg z hz).differentiableAt.hasDerivAt
    have hd := ht.deriv
    change deriv (fun w => (w-a) * g w) z = 1 * g z + (z-a) * deriv g z at hd
    simpa only [heq, one_mul] using hd
  let v : ℂ → ℂ := fun z => deriv g z / g z
  have hv : DifferentiableOn ℂ v R.domain := hg.deriv.differentiableOn.div
    hg.differentiableOn hgn
  have hz := C.physical_integral_zero hc R.isOpen_domain R.closure_subset_domain hv
  have hba (t : CircleSpace) : C.boundaryMap t ≠ a := fun he =>
    (C.boundaryMap_mem_frontier t).2 (hU.interior_eq.symm ▸ (he ▸ haU))
  have hbc (t : CircleSpace) : C.boundaryMap t ∈ R.domain :=
    R.closure_subset_domain (C.boundaryMap_mem_frontier t).1
  have heq (t : CircleSpace) : C.angularJacobian R t =
      C.boundaryNormal t / (C.boundaryMap t-a) + C.boundaryNormal t * v (C.boundaryMap t) := by
    change C.boundaryNormal t * deriv R.f (C.boundaryMap t) / R.f (C.boundaryMap t) = _
    rw [hd _ (hbc t), ← hfgg]
    dsimp only [v]
    field_simp [hgn _ (hbc t), sub_ne_zero.mpr (hba t)]
  have hi1 : Integrable (fun t => C.boundaryNormal t / (C.boundaryMap t-a)) circleMeasure :=
    (C.boundaryNormal.continuous.div (C.boundaryMap.continuous.sub continuous_const)
      (fun t => sub_ne_zero.mpr (hba t))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun t => C.boundaryNormal t * v (C.boundaryMap t)) circleMeasure :=
    (C.boundaryNormal.continuous.mul (hv.continuousOn.comp_continuous
      C.boundaryMap.continuous hbc)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  simp_rw [heq]
  rw [integral_add hi1 hi2, hz, add_zero]
  have hh := C.boundaryContour_index_inside hU haU
  change (2 * (Real.pi : ℂ) * I)⁻¹ •
    (∫ t in (0 : ℝ)..1, deriv C.boundaryContour.path t * (C.boundaryContour.path t - a)⁻¹) = 1 at hh
  rw [show (fun t : ℝ => deriv C.boundaryContour.path t * (C.boundaryContour.path t - a)⁻¹) =
      fun t => deriv C.boundaryContour.path t • (C.boundaryContour.path t - a)⁻¹ from rfl,
    C.boundaryContour_integral (fun w => (w-a)⁻¹)] at hh
  exact hh

lemma integral_angularJacobian_pow (hU : IsOpen U) (hc : Convex ℝ U) (n : ℕ) :
    (∫ t, C.angularJacobian R t * (C.interiorBoundary R t)^n ∂circleMeasure) =
      if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp only [pow_zero, mul_one, ↓reduceIte]; exact C.integral_angularJacobian R hU hc
  | succ n => simpa only [Nat.succ_ne_zero, ↓reduceIte] using C.integral_angularJacobian_pow_succ R hc n

lemma conj_angularJacobian (t : CircleSpace) : conj (C.angularJacobian R t) = C.angularJacobian R t := by
  apply Complex.ext <;> simp [(C.angularJacobian_real_nonneg R t).1]

lemma integral_angularJacobian_zpow (hU : IsOpen U) (hc : Convex ℝ U) (j : ℤ) :
    (∫ t, C.angularJacobian R t * (C.interiorBoundary R t)^j ∂circleMeasure) =
      if j = 0 then 1 else 0 := by
  cases j with
  | ofNat n =>
    change (∫ t, C.angularJacobian R t * (C.interiorBoundary R t)^(n : ℤ) ∂circleMeasure) =
      if (n : ℤ) = 0 then 1 else 0
    simpa only [zpow_natCast, Nat.cast_eq_zero] using C.integral_angularJacobian_pow R hU hc n
  | negSucc n =>
    have he (t : CircleSpace) : C.angularJacobian R t * (C.interiorBoundary R t)^((Int.negSucc n)) =
        conj (C.angularJacobian R t * (C.interiorBoundary R t)^(n+1)) := by
      rw [zpow_negSucc, ← inv_pow, Complex.inv_eq_conj (C.norm_interiorBoundary R t),
        map_mul, C.conj_angularJacobian, map_pow]
    simp_rw [he]
    rw [integral_conj, C.integral_angularJacobian_pow_succ R hc, map_zero]
    simp

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.AngularMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular Measure. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

open Boundary

namespace ExteriorCollar

attribute [local instance] OAI.CrouzeixHilbert.Conformal.instFactLtRealOfNat_solutions
variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

lemma circleCoordinate_interiorAngle (t : CircleSpace) :
    circleCoordinate (C.interiorAngle R t) = C.interiorBoundary R t := by
  simp only [circleCoordinate, fourier_one]
  rw [← AddCircle.homeomorphCircle_apply (by norm_num : (1 : ℝ) ≠ 0)]
  exact congrArg Subtype.val ((AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).apply_symm_apply _)

lemma fourier_interiorAngle (j : ℤ) (t : CircleSpace) :
    fourier j (C.interiorAngle R t) = (C.interiorBoundary R t)^j := by
  rw [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow]
  have he := C.circleCoordinate_interiorAngle R t
  simp only [circleCoordinate, fourier_one] at he
  rw [he]

lemma angularIntegralCLM_eq (hU : IsOpen U) (hc : Convex ℝ U) :
    C.angularIntegralCLM R = circleIntegralCLM := by
  apply ContinuousLinearMap.ext_on (s := range (fourier (T := (1 : ℝ))))
  · rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
      span_fourier_closure_eq_top, Submodule.top_coe]
  · rintro f ⟨j,rfl⟩
    change (∫ t, C.angularJacobian R t * fourier j (C.interiorAngle R t) ∂circleMeasure) =
      ∫ t, fourier j t ∂circleMeasure
    simp_rw [C.fourier_interiorAngle]
    rw [C.integral_angularJacobian_zpow R hU hc, Disk.integral_fourier]

lemma integral_angularChange {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (hU : IsOpen U) (hc : Convex ℝ U) (f : C(CircleSpace, E)) :
    (∫ t, C.angularJacobian R t • f (C.interiorAngle R t) ∂circleMeasure) =
      ∫ t, f t ∂circleMeasure := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro l
  have h1 : Integrable (fun t => C.angularJacobian R t • f (C.interiorAngle R t)) circleMeasure :=
    ((C.angularJacobian R).continuous.smul (f.continuous.comp (C.interiorAngle R).continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable f circleMeasure := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← l.integral_comp_comm h1, ← l.integral_comp_comm h2]
  simp only [map_smul, smul_eq_mul]
  exact congrArg (fun L : C(CircleSpace, ℂ) →L[ℂ] ℂ => L ⟨l ∘ f, l.continuous.comp f.continuous⟩)
    (C.angularIntegralCLM_eq R hU hc)

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.PhysicalDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Density. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physicalDensityOperatorRealNormedSpace
lemma operatorDensity_nonneg (D : Operator H) (hD : spectralRadius ℂ D < 1)
    (hN : ‖D‖ ≤ 1) (t : CircleSpace) : 0 ≤ C.operatorDensity R D hD t := by
  have he : C.angularJacobian R t = ((C.angularJacobian R t).re : ℂ) := by
    apply Complex.ext <;> simp [(C.angularJacobian_real_nonneg R t).1]
  change 0 ≤ C.angularJacobian R t • Disk.phi D (C.interiorAngle R t)
  rw [he]
  exact smul_nonneg (by simpa using (C.angularJacobian_real_nonneg R t).2)
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr (Disk.phi_isPositive D hN hD _))

lemma integral_operatorDensity (D : Operator H) (hD : spectralRadius ℂ D < 1)
    (hU : IsOpen U) (hc : Convex ℝ U) :
    (∫ t, C.operatorDensity R D hD t ∂circleMeasure) = 1 := by
  change (∫ t, C.angularJacobian R t • Disk.phi D (C.interiorAngle R t) ∂circleMeasure) = 1
  exact (C.integral_angularChange R hU hc ⟨Disk.phi D, Disk.continuous_phi D hD⟩).trans
    (Disk.integral_phi D hD)

lemma integral_operatorDensity_pullback (D : Operator H) (hD : spectralRadius ℂ D < 1)
    (hU : IsOpen U) (hc : Convex ℝ U) {m : ℕ} (F : C(CircleSpace, Coeff m)) :
    (∫ t, tensorOperator (C.operatorDensity R D hD t) (F (C.interiorAngle R t)) ∂circleMeasure) =
      ∫ t, tensorOperator (Disk.phi D t) (F t) ∂circleMeasure := by
  let V : C(CircleSpace, Operator (Amplification H m)) :=
    ⟨fun t => tensorOperator (Disk.phi D t) (F t),
      ((tensorBilinearCLM m).continuous.comp (Disk.continuous_phi D hD)).clm_apply F.continuous⟩
  have he (t : CircleSpace) : tensorOperator (C.operatorDensity R D hD t) (F (C.interiorAngle R t)) =
      C.angularJacobian R t • V (C.interiorAngle R t) := by
    change tensorOperator (C.angularJacobian R t • Disk.phi D (C.interiorAngle R t)) _ = _
    exact (tensorOperatorCLM _).map_smul _ _
  simp_rw [he]
  exact C.integral_angularChange R hU hc V

end Conformal.ExteriorCollar

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

lemma matrixDensity_posSemidef {n : ℕ} (D : Operator (EuclideanSpace ℂ (Fin n)))
    (hD : spectralRadius ℂ D < 1) (hN : ‖D‖ ≤ 1) (t : CircleSpace) :
    (C.matrixDensity R D hD t).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact map_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm
    (C.operatorDensity_nonneg R D hD hN t)

lemma integral_matrixDensity {n : ℕ} (D : Operator (EuclideanSpace ℂ (Fin n)))
    (hD : spectralRadius ℂ D < 1) (hU : IsOpen U) (hc : Convex ℝ U) :
    (∫ t, C.matrixDensity R D hD t ∂circleMeasure) = 1 := by
  let : ContinuousSMul ℂ (EuclideanSpace ℂ (Fin n)) := IsBoundedSMul.continuousSMul
  let : CompleteSpace (Operator (EuclideanSpace ℂ (Fin n))) :=
    ContinuousLinearMap.instCompleteSpace
  have hi : Integrable (C.operatorDensity R D hD) circleMeasure :=
    (C.operatorDensity R D hD).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ t, operatorToMatrix n (C.operatorDensity R D hD t) ∂circleMeasure) = 1
  rw [(operatorToMatrix n).integral_comp_comm hi, C.integral_operatorDensity R D hD hU hc]
  exact map_one (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm

lemma tensorIntegral_matrixDensity_pullback {n : ℕ} (D : Operator (EuclideanSpace ℂ (Fin n)))
    (hD : spectralRadius ℂ D < 1) (hU : IsOpen U) (hc : Convex ℝ U)
    (F : C(CircleSpace, Coeff n)) :
    Boundary.tensorIntegral (C.matrixDensity R D hD) (F.comp (C.interiorAngle R)) =
      ∫ t, tensorOperator (Disk.phi D t) (F t) ∂circleMeasure := by
  change (∫ t, tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) (C.matrixDensity R D hD t)) (F (C.interiorAngle R t)) ∂circleMeasure) = _
  simp only [matrixDensity, ContinuousMap.coe_mk, operatorToMatrix_apply, StarAlgEquiv.apply_symm_apply]
  exact C.integral_operatorDensity_pullback R D hD hU hc F

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ResolventMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resolvent Moments. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma operatorResolvent_add_star_nonneg (A : Operator H) (hKU : numericalClosure A ⊆ U)
    (hU : IsOpen U) (hc : Convex ℝ U) (t : CircleSpace) :
    0 ≤ C.operatorResolvent A hKU hU t + star (C.operatorResolvent A hKU hU t) := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  apply isPositive_original_resolvent_of_not_mem
  · exact fun ht => C.boundaryMap_not_mem hU t (hKU ht)
  · intro w hw
    exact C.supporting_normal hc (norm_circleCoordinate t) (subset_closure (hKU (subset_closure hw)))

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BoundaryMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Moments. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

variable {n : ℕ} (A : Operator (EuclideanSpace ℂ (Fin n)))
    (hKU : numericalClosure A ⊆ U) (hU : IsOpen U)

lemma matrixResolventDensity_posSemidef (hc : Convex ℝ U) (t : CircleSpace) :
    (C.matrixResolventDensity A hKU hU t).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  let e := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm
  let Q := C.operatorResolvent A hKU hU t
  have he : e (Q + star Q) = (C.matrixResolventDensity A hKU hU t) := by
    rw [map_add]
    change e Q + e (star Q) = e Q + star (e Q)
    exact congrArg (e Q + ·) (e.map_star' Q)
  rw [← he]
  exact map_nonneg e (C.operatorResolvent_add_star_nonneg A hKU hU hc t)

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.MetricBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric Boundary. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

variable {n : ℕ} (hn : 0 < n) (A : Operator (EuclideanSpace ℂ (Fin n)))
    (hKU : numericalClosure A ⊆ U) (hU : IsOpen U) (hc : Convex ℝ U)
    (hb : Bornology.IsBounded U)

include C hn hKU hU hc hb in
lemma minimizing_metric_sqrt_le_two (κ : ℝ) (H : Coeff n)
    (hH : CrouzeixHilbert.Metric.Feasible
      (operatorToMatrix n (holomorphicEval A R.domain R.f)) (κ ^ 2) H)
    (hmin : ∀ s J, CrouzeixHilbert.Metric.Feasible
      (operatorToMatrix n (holomorphicEval A R.domain R.f)) s J → κ ^ 2 ≤ s) :
    κ ≤ 2 := by
  by_cases hk : κ ≤ 1
  · exact hk.trans (by norm_num)
  have hκ : 1 < κ := lt_of_not_ge hk
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let e := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)
  let T : Coeff n := operatorToMatrix n (holomorphicEval A R.domain R.f)
  change CrouzeixHilbert.Metric.Feasible T (κ ^ 2) H at hH
  have hT : spectralRadius ℂ T < 1 := by
    simpa only [T, operatorToMatrix_apply, spectralRadius, AlgEquiv.spectrum_eq] using
      R.spectralRadius_coordinate_lt_one A hKU
  let S := e (CFC.sqrt H)
  let D := e (CFC.sqrt H * T * Ring.inverse (CFC.sqrt H))
  have hN : ‖D‖ ≤ 1 := by
    rw [← Matrix.cstar_norm_def]
    exact hH.sqrt_similarity.2.1
  have hD : spectralRadius ℂ D < 1 := by
    simpa only [D, spectralRadius, AlgEquiv.spectrum_eq, hH.sqrt_spectrum] using hT
  have hI : S * holomorphicEval A R.domain R.f = D * S := by
    have he : e T = holomorphicEval A R.domain R.f := e.apply_symm_apply _
    rw [← he]
    change e (CFC.sqrt H) * e T = e _ * e (CFC.sqrt H)
    rw [← map_mul, ← map_mul, mul_assoc (CFC.sqrt H * T),
      Ring.inverse_mul_cancel _ hH.sqrt_similarity.1, mul_one]
  obtain ⟨X,Y,Q,V,_,_,_,_,hXY,hX,hY,hx,hy,hV,hKV,_,hQ,hQV,_,hQI⟩ :=
    disk_endpoint_extremal hn T hT hκ H hH hmin
  let W := R.domain ∩ R.f ⁻¹' V
  have hW : IsOpen W := R.analytic_f.continuousOn.isOpen_inter_preimage R.isOpen_domain hV
  have hUW : closure U ⊆ W := fun z hz =>
    ⟨R.closure_subset_domain hz, hKV (R.closed_f.mapsTo hz)⟩
  have hfW : EntrywiseHolomorphic W (matrixRationalFunction Q ∘ R.f) := fun i j =>
    (hQ i j).comp (R.analytic_f.differentiableOn.mono inter_subset_left) (fun z hz => hz.2)
  let F := C.matrixAnalyticTrace hUW (matrixRationalFunction Q ∘ R.f) hfW.continuousOn
  have hF : ∀ t, ‖F t‖ ≤ 1 := by
    intro t
    exact hQV _ (le_of_eq (R.boundary_norm _ (C.boundaryMap_mem_frontier t)))
  let F₀ : C(CircleSpace, Coeff n) :=
    ⟨fun t => matrixRationalFunction Q (circleCoordinate t),
      hQ.continuousOn.comp_continuous circleCoordinate.continuous
        (fun t => hKV (mem_closedBall_zero_iff.mpr (norm_circleCoordinate t).le))⟩
  have hF₀ : F = F₀.comp (C.interiorAngle R) := by
    ext t i j
    change matrixRationalFunction Q (R.f (C.boundaryMap t)) i j =
      matrixRationalFunction Q (circleCoordinate (C.interiorAngle R t)) i j
    rw [C.circleCoordinate_interiorAngle R]
    rfl
  have hInt : tensorIntegral (C.matrixDensity R D hD) F (vectorization X) = vectorization Y := by
    rw [hF₀, C.tensorIntegral_matrixDensity_pullback R D hD hU hc]
    change (∫ t, tensorOperator (Disk.phi D t)
      (matrixRationalFunction Q (fourier 1 t)) ∂Disk.σ) (vectorization X) = _
    rw [Disk.integral_matrixHolomorphic D hN hD hV hKV hQ]
    exact hQI
  have hS : IsSelfAdjoint (tensorOperator S (1 : Coeff n)) := by
    change star (tensorOperator S (1 : Coeff n)) = tensorOperator S (1 : Coeff n)
    rw [← tensorOperator_star, star_one]
    have hs : IsSelfAdjoint S := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg H)).map e
    rw [hs.star_eq]
  exact endpoint_le_two_of_physical_tests (C.boundaryOperator hc n)
    (C.norm_boundaryOperator_le hc n) (C.matrixResolventDensity A hKU hU)
    (C.matrixDensity R D hD) F (C.matrixResolventDensity_posSemidef A hKU hU hc)
    (C.matrixDensity_posSemidef R D hD hN) (C.integral_matrixDensity R D hD hU hc) hF
    (C.boundaryCauchy_left_module hU hc hb hW hUW hfW hF)
    (C.boundaryCauchy_right_module hU hc hb hW hUW hfW hF)
    (tensorOperator S (1 : Coeff n)) hS X Y hX hY hXY κ (zero_lt_one.trans hκ) hx hy hInt
    (C.physical_laurent_tests A hKU hU R hc D S hN hD hI)

include C hn hKU hU hc hb in
lemma exists_conformal_contraction :
    ∃ S J D : Operator (EuclideanSpace ℂ (Fin n)),
      J * S = 1 ∧ S * J = 1 ∧ ‖S‖ * ‖J‖ ≤ 2 ∧ ‖D‖ ≤ 1 ∧
      spectralRadius ℂ D < 1 ∧ S * holomorphicEval A R.domain R.f = D * S := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let e := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)
  let T : Coeff n := operatorToMatrix n (holomorphicEval A R.domain R.f)
  have hT : spectralRadius ℂ T < 1 := by
    simpa only [T, operatorToMatrix_apply, spectralRadius, AlgEquiv.spectrum_eq] using
      R.spectralRadius_coordinate_lt_one A hKU
  obtain ⟨τ,H,hH,hτ,hmin⟩ := CrouzeixHilbert.Metric.exists_minimizing_metric T hT
  have hτ0 : 0 ≤ τ := zero_le_one.trans hτ
  have hκ : Real.sqrt τ ≤ 2 := C.minimizing_metric_sqrt_le_two R hn A hKU hU hc hb
    (Real.sqrt τ) H (by simpa only [Real.sq_sqrt hτ0] using hH)
    (by simpa only [Real.sq_sqrt hτ0] using hmin)
  let S := e (CFC.sqrt H)
  let J := e (Ring.inverse (CFC.sqrt H))
  let D := e (CFC.sqrt H * T * Ring.inverse (CFC.sqrt H))
  refine ⟨S,J,D,?_,?_,?_,?_,?_,?_⟩
  · change e _ * e _ = 1
    rw [← map_mul, Ring.inverse_mul_cancel _ hH.sqrt_similarity.1, map_one]
  · change e _ * e _ = 1
    rw [← map_mul, Ring.mul_inverse_cancel _ hH.sqrt_similarity.1, map_one]
  · change ‖e _‖ * ‖e _‖ ≤ 2
    rw [← Matrix.cstar_norm_def, ← Matrix.cstar_norm_def]
    exact hH.sqrt_similarity.2.2.trans hκ
  · change ‖e _‖ ≤ 1
    rw [← Matrix.cstar_norm_def]
    exact hH.sqrt_similarity.2.1
  · simpa only [D, spectralRadius, AlgEquiv.spectrum_eq, hH.sqrt_spectrum] using hT
  · have he : e T = holomorphicEval A R.domain R.f := e.apply_symm_apply _
    rw [← he]
    change e (CFC.sqrt H) * e T = e _ * e (CFC.sqrt H)
    rw [← map_mul, ← map_mul, mul_assoc (CFC.sqrt H * T),
      Ring.inverse_mul_cancel _ hH.sqrt_similarity.1, mul_one]

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.CompleteFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete Finite. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

lemma norm_tensorOperator_one_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : Operator H) (m : ℕ) : ‖tensorOperator A (1 : Coeff m)‖ ≤ ‖A‖ := by
  have h1 : ‖(1 : Coeff m)‖ ≤ 1 := by
    rw [Matrix.cstar_norm_def, map_one]
    exact ContinuousLinearMap.norm_id_le
  exact (norm_tensorOperator_le A (1 : Coeff m)).trans
    ((mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans_eq (mul_one _))

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

variable {n : ℕ} (hn : 0 < n) (A : Operator (EuclideanSpace ℂ (Fin n)))
    (hKU : numericalClosure A ⊆ U) (hU : IsOpen U) (hc : Convex ℝ U)
    (hb : Bornology.IsBounded U)

include C R hn hKU hU hc hb

lemma holomorphic_bound_oai {V : Set ℂ} (hV : IsOpen V) (hUV : closure U ⊆ V)
    {m : ℕ} {F : ℂ → Coeff m} (hF : EntrywiseHolomorphic V F) :
    ‖matrixHolomorphicEval A V F‖ ≤ 2 * supNorm (closure U) F := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨S,J,D,hJS,_,hcond,hN,hD,hI⟩ := C.exists_conformal_contraction R hn A hKU hU hc hb
  let Λ := C.operatorDensity R D hD
  let F₀ := C.matrixAnalyticTrace hUV F hF.continuousOn
  let L := ∫ t, tensorOperator (Λ t) (F₀ t) ∂circleMeasure
  have hs : tensorOperator S (1 : Coeff m) * matrixHolomorphicEval A V F =
      L * tensorOperator S (1 : Coeff m) :=
    C.physical_intertwines R hU hc A D S hKU hN hD hI hV hUV hF
  have hi : tensorOperator J (1 : Coeff m) * tensorOperator S (1 : Coeff m) = 1 := by
    rw [← tensorOperator_mul, hJS, one_mul, tensorOperator_one]
  have he : matrixHolomorphicEval A V F =
      tensorOperator J (1 : Coeff m) * L * tensorOperator S (1 : Coeff m) := by
    calc
      _ = (tensorOperator J (1 : Coeff m) * tensorOperator S (1 : Coeff m)) *
          matrixHolomorphicEval A V F := by rw [hi, one_mul]
      _ = _ := by rw [mul_assoc, hs, ← mul_assoc]
  have hsup := supNorm_bddAbove hb.isCompact_closure (hF.continuousOn.mono hUV)
  have hc0 := supNorm_nonneg hsup
  have hnL : ‖L‖ ≤ supNorm (closure U) F :=
    norm_integral_tensor_density_le Λ (C.operatorDensity_nonneg R D hD hN)
      (C.integral_operatorDensity R D hD hU hc) F₀ _ hc0
      (fun t => norm_le_supNorm hsup (C.boundaryMap_mem_frontier t).1)
  rw [he]
  calc
    ‖tensorOperator J (1 : Coeff m) * L * tensorOperator S (1 : Coeff m)‖ ≤
        (‖tensorOperator J (1 : Coeff m)‖ * ‖L‖) * ‖tensorOperator S (1 : Coeff m)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (‖J‖ * supNorm (closure U) F) * ‖S‖ :=
      mul_le_mul (mul_le_mul (norm_tensorOperator_one_le J m) hnL (norm_nonneg _) (norm_nonneg _))
        (norm_tensorOperator_one_le S m) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hc0)
    _ = (‖S‖ * ‖J‖) * supNorm (closure U) F := by ring
    _ ≤ 2 * supNorm (closure U) F := mul_le_mul_of_nonneg_right hcond hc0

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end

theorem solution : type_of% @OAI.CrouzeixHilbert.Conformal.ExteriorCollar.holomorphic_bound_oai := @OAI.CrouzeixHilbert.Conformal.ExteriorCollar.holomorphic_bound_oai
