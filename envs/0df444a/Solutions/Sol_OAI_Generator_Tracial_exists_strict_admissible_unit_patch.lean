-- Prove2me | solution 1 for OAI.Generator.Tracial.exists_strict_admissible_unit_patch
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:15:44.2847+00:00
-- url     : https://prove2.me/submissions/e2713f96-d3d9-4a5f-90e1-1be51da18c06

import Mathlib
import Definitions.Def_OAIQ11Fg012
import Theorems.Thm_OAI_Generator_Tracial_exists_unitResidual_local_compression

section
-- module Solutions.OAIQ11_FG.FactorGeneration_ProjectionLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A nonzero projection in a diffuse tracial algebra contains nonzero projections of arbitrarily small trace. -/

/-! Monotone projection limits with trace bounds, giving chain bounds for prescribed trace cuts. -/

/-! Exact trace cuts in a diffuse coordinate algebra. -/

/-! Algebraic part of Popa 1308.3982v3, Lemma 3.2: adding a supported
partial unitary in the residual corner. The small mixed-word estimates and
the existence of an appropriate patch are separate analytic requirements. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace CornerUnitary
variable {p q : AlgebraProjection M}

theorem patch_extends (v : CornerUnitary p) (w : CornerUnitary q) (hpq : p.val*q.val=0) :
    (patch v w hpq).val*(star v.val*v.val)=v.val := by
  have hqp : q.val*p.val=0 := by
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq,q.property.isSelfAdjoint.star_eq,star_zero]
      using congrArg star hpq
  change (v.val+w.val)*(star v.val*v.val)=v.val
  rw [v.initial,add_mul,v.mul_support]
  have he : w.val*p.val=0 := by
    calc w.val*p.val=(w.val*q.val)*p.val := by rw [w.mul_support]
         _ = 0 := by rw [mul_assoc,hqp,mul_zero]
  rw [he,add_zero]

theorem trace_norm_sq (τ : TracialRepresentation M) (v : CornerUnitary p) :
    τ.norm₂ v.val ^ 2 = (τ.trace p.val).re := by
  have he := congrArg Complex.re (τ.trace_star_mul v.val)
  rw [v.initial] at he
  simpa only [← Complex.ofReal_pow,Complex.ofReal_re] using he.symm

end CornerUnitary

end

/-! Dyadic projections inside a diffuse algebra with faithful trace. -/
section
open UltrapowerBridge
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)

theorem halfTraceCut_trace (p : AlgebraProjection M) :
    τ.trace (halfTraceCut τ hdiff p).val = ((τ.trace p.val).re/2 : ℝ) :=
  (exists_half_trace_cut τ hdiff p).choose_spec.2

theorem splitProjection_trace (p : AlgebraProjection M) (b : Bool) :
    τ.trace (splitProjection τ hdiff p b).val = ((τ.trace p.val).re/2 : ℝ) := by
  cases b
  · exact halfTraceCut_trace τ hdiff p
  · change τ.trace (p.val-(halfTraceCut τ hdiff p).val)=_
    have he : τ.trace (p.val-(halfTraceCut τ hdiff p).val)=
        τ.trace p.val-τ.trace (halfTraceCut τ hdiff p).val := inner_sub_right _ _ _
    have hreal : τ.trace p.val = ((τ.trace p.val).re : ℂ) := by
      have h := τ.trace_star_mul p.val
      rw [p.property.isSelfAdjoint.star_eq,p.property.isIdempotentElem.eq] at h
      rw [h,← Complex.ofReal_pow,Complex.ofReal_re]
    rw [he,halfTraceCut_trace,hreal]
    simp only [Complex.ofReal_re]
    push_cast
    ring

theorem dyadicProjection_trace (p : AlgebraProjection M) (n : ℕ) (i : DyadicIndex n) :
    (τ.trace (dyadicProjection τ hdiff p n i).val).re = (τ.trace p.val).re/(2:ℝ)^n := by
  induction n with
  | zero => simp [dyadicProjection]
  | succ n ih =>
    change (τ.trace (splitProjection τ hdiff (dyadicProjection τ hdiff p n i.1) i.2).val).re = _
    rw [splitProjection_trace,Complex.ofReal_re,ih,pow_succ]
    ring

end

/-! Finite spectral sums in the constructed dyadic projection algebras. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem projection_trace_real (τ : TracialRepresentation M) (p : AlgebraProjection M) :
    τ.trace p.val = ((τ.trace p.val).re : ℂ) := by
  have h := τ.trace_star_mul p.val
  rw [p.property.isSelfAdjoint.star_eq,p.property.isIdempotentElem.eq] at h
  rw [h,← Complex.ofReal_pow,Complex.ofReal_re]

variable {ι : Type*} [Fintype ι]

theorem projectionSum_trace (τ : TracialRepresentation M)
    (a : ι → AlgebraProjection M) (c : ι → ℂ) :
    τ.trace (projectionSum a c)=∑ i, c i*τ.trace (a i).val := by
  change coordinateTraceLinear τ (∑ i, c i • (a i).val)=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (coordinateTraceLinear τ).map_smul (c i) (a i).val

variable (τ : TracialRepresentation M)
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)

theorem dyadicEval_refine (p : AlgebraProjection M) (n : ℕ) (c : DyadicIndex n → ℂ) :
    dyadicEval τ hdiff p (n+1) (fun i => c i.1)=dyadicEval τ hdiff p n c := by
  change (∑ i : DyadicIndex n × Bool, c i.1 •
    (splitProjection τ hdiff (dyadicProjection τ hdiff p n i.1) i.2).val)=_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool,add_comm,← smul_add,splitProjection_sum]

theorem dyadicEval_lift (p : AlgebraProjection M) {m n : ℕ} (hmn : m ≤ n)
    (c : DyadicIndex m → ℂ) :
    ∃ d : DyadicIndex n → ℂ, dyadicEval τ hdiff p m c=dyadicEval τ hdiff p n d := by
  induction n,hmn using Nat.le_induction with
  | base => exact ⟨c,rfl⟩
  | succ n hmn ih =>
    obtain ⟨d,hd⟩ := ih
    exact ⟨fun i => d i.1,hd.trans (dyadicEval_refine τ hdiff p n d).symm⟩

theorem dyadicEval_trace (p : AlgebraProjection M) (n : ℕ) (c : DyadicIndex n → ℂ) :
    τ.trace (dyadicEval τ hdiff p n c)=
      ∑ i, c i*((τ.trace p.val).re/(2:ℝ)^n : ℝ) := by
  rw [projectionSum_trace]
  apply Finset.sum_congr rfl
  intro i _
  rw [projection_trace_real,dyadicProjection_trace]

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_CornerTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Trace estimates in the actual ambient algebra. The corner scalar uses
its normalized trace. These estimates do not assume or assert the existence
of a local-quantizing projection. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem norm_trace_mul_le (x y : M.toStarSubalgebra) :
    ‖τ.trace (x*y)‖ ≤ τ.norm₂ x * τ.norm₂ y := by
  have he := norm_inner_le_norm (𝕜 := ℂ)
    (((star x : M.toStarSubalgebra) : H →L[ℂ] H) τ.vector)
    ((y : H →L[ℂ] H) τ.vector)
  have hi : inner ℂ (((star x : M.toStarSubalgebra) : H →L[ℂ] H) τ.vector)
      ((y : H →L[ℂ] H) τ.vector) = τ.trace (x*y) := by
    change inner ℂ (star (x : H →L[ℂ] H) τ.vector) ((y : H →L[ℂ] H) τ.vector) = _
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
    rfl
  rw [hi] at he
  change ‖τ.trace (x*y)‖ ≤ τ.norm₂ (star x)*τ.norm₂ y at he
  simpa only [τ.norm₂_star] using he

end

/-! Actual noncommutative L1 on the coordinate algebra: trace(sqrt(x* x)).
The supported L2-to-L1 estimate retains the square root of the support trace.
No quantizing projection or conditional expectation theorem is assumed. -/

/-! A finite compression-energy estimate yields a nonzero corner projection with simultaneous L1 control. -/

/-! The scalar trace estimate for a term with two supported patch letters.
It reduces to the actual compressed middle coefficient and keeps trace(q),
not trace(p), as the scale of the error. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

namespace CornerUnitary

theorem norm₂_eq_support {q : AlgebraProjection M} (v : CornerUnitary q) :
    τ.norm₂ v.val=τ.norm₂ q.val := by
  have he := v.trace_norm_sq τ
  rw [projection_trace_sq τ _ q.property] at he
  nlinarith [show 0 ≤ τ.norm₂ v.val from norm_nonneg _,show 0 ≤ τ.norm₂ q.val from norm_nonneg _]

end CornerUnitary

theorem two_patch_trace_le (q : AlgebraProjection M) (v w : CornerUnitary q)
    (a x b : M.toStarSubalgebra) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖τ.trace (a*v.val*x*w.val*b)‖ ≤ τ.norm₂ (q.val*x*q.val)*τ.norm₂ q.val := by
  have he : a*v.val*x*w.val*b = (a*v.val)*(q.val*x*q.val)*(w.val*b) := by
    simp only [← mul_assoc]
    rw [mul_assoc a v.val q.val,v.mul_support]
    simp only [mul_assoc]
    rw [← mul_assoc q.val w.val b,w.support_mul]
  have hr : τ.trace ((a*v.val)*(q.val*x*q.val)*(w.val*b)) =
      τ.trace ((q.val*x*q.val)*(w.val*b*a*v.val)) := by
    rw [mul_assoc (a*v.val) (q.val*x*q.val) (w.val*b),τ.trace_mul_comm (a*v.val)]
    simp only [mul_assoc]
  have hnorm : ‖w.val*b*a‖ ≤ 1 := by
    have hw : ‖w.val*b‖ ≤ 1 := (norm_mul_le _ _).trans
      (by nlinarith [w.norm_le_one,norm_nonneg w.val,norm_nonneg b])
    exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (w.val*b),norm_nonneg a])
  rw [he,hr]
  have hn : τ.norm₂ (w.val*b*a*v.val) ≤ τ.norm₂ q.val := by
    exact ((τ.norm₂_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hnorm)).trans_eq
      (v.norm₂_eq_support τ)
  exact (norm_trace_mul_le τ _ _).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _))

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_PartialUnitaries
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Popa's extension order on actual supported partial unitaries, and its
exact L2 distance identity. -/

/-! Actual L2 limits of partial unitaries and upper bounds of increasing
sequences, using their exact support-trace distance. -/

/-! Actual orthogonal corner unitaries from dyadic trace cuts. These supply
weakly vanishing scalar matrix coefficients for the scalar-commutant case
of Popa's coordinate nonintertwining criterion. -/
section
open Filter
open scoped Topology BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)

/-- The next sign is centered even after multiplication by an arbitrary
member of the previous finite dyadic algebra. -/
theorem dyadicRademacher_centered_over_previous (p : AlgebraProjection M) (n : ℕ)
    (c : DyadicIndex n → ℂ) :
    τ.trace (dyadicEval τ hdiff p n c*dyadicRademacher τ hdiff p n)=0 := by
  rw [← dyadicEval_refine τ hdiff p n c]
  unfold dyadicRademacher dyadicEval
  rw [projectionSum_mul _ (dyadicProjection_orthogonal τ hdiff p (n+1))]
  rw [dyadicEval_trace]
  change (∑ i : DyadicIndex n × Bool,
    (c i.1*dyadicSign n i)*((τ.trace p.val).re/(2:ℝ)^(n+1) : ℝ))=0
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro i _
  rw [Fintype.sum_bool]
  simp [dyadicSign]

theorem dyadicRademacher_trace_mul_of_lt (p : AlgebraProjection M) {m n : ℕ} (hmn : m < n) :
    τ.trace (dyadicRademacher τ hdiff p m*dyadicRademacher τ hdiff p n)=0 := by
  obtain ⟨c,hc⟩ := dyadicEval_lift τ hdiff p (Nat.succ_le_iff.mpr hmn) (dyadicSign m)
  change τ.trace (dyadicEval τ hdiff p (m+1) (dyadicSign m)*_)=0
  rw [hc]
  exact dyadicRademacher_centered_over_previous τ hdiff p n c

theorem dyadicRademacher_trace_mul_of_ne (p : AlgebraProjection M) {m n : ℕ} (hmn : m ≠ n) :
    τ.trace (dyadicRademacher τ hdiff p m*dyadicRademacher τ hdiff p n)=0 := by
  rcases lt_or_gt_of_ne hmn with h | h
  · exact dyadicRademacher_trace_mul_of_lt τ hdiff p h
  · rw [τ.trace_mul_comm]
    exact dyadicRademacher_trace_mul_of_lt τ hdiff p h

theorem coordinate_inner_eq_trace (a b : M.toStarSubalgebra) :
    inner ℂ ((a : H →L[ℂ] H) τ.vector) ((b : H →L[ℂ] H) τ.vector)=τ.trace (star a*b) := by
  change _ = inner ℂ τ.vector (star (a : H →L[ℂ] H) ((b : H →L[ℂ] H) τ.vector))
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]

theorem dyadicRademacher_norm₂ (p : AlgebraProjection M) (n : ℕ) :
    τ.norm₂ (dyadicRademacher τ hdiff p n)=τ.norm₂ p.val := by
  have he := (dyadicCornerUnitary τ hdiff p n).trace_norm_sq τ
  rw [projection_trace_sq τ p.val p.property] at he
  change τ.norm₂ (dyadicRademacher τ hdiff p n)^2=τ.norm₂ p.val^2 at he
  have h₁ : 0 ≤ τ.norm₂ (dyadicRademacher τ hdiff p n) := norm_nonneg _
  have h₂ : 0 ≤ τ.norm₂ p.val := norm_nonneg _
  nlinarith

end

/-! Popa 1308.3982v3, §1.5, scalar-target specialization. The sequence is
constructed from actual dyadic trace cuts in each nonzero corner; neither
nonintertwining nor Haar existence is an assumption. -/
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

omit [CompleteSpace H] in
/-- Bessel's inequality makes the coefficients of an orthonormal sequence vanish. -/
theorem orthonormal_inner_tendsto_zero (v : ℕ → H) (hv : Orthonormal ℂ v) (x : H) :
    Tendsto (fun n => inner ℂ x (v n)) atTop (𝓝 0) := by
  have ht := (hv.inner_products_summable x).tendsto_atTop_zero
  have hh : Tendsto (fun n => inner ℂ (v n) x) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have he := ht (Iio_mem_nhds (sq_pos_of_pos hε))
    obtain ⟨N,hN⟩ := eventually_atTop.mp he
    refine ⟨N,fun n hn => ?_⟩
    rw [dist_zero_right]
    have h : ‖inner ℂ (v n) x‖^2 < ε^2 := hN n hn
    nlinarith [norm_nonneg (inner ℂ (v n) x)]
  have hs := hh.star
  simp only [star_zero] at hs
  change Tendsto (fun n => (starRingEnd ℂ) (inner ℂ (v n) x)) atTop (𝓝 0) at hs
  simpa only [inner_conj_symm] using hs

variable (τ : TracialRepresentation M)
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)

theorem dyadicRademacher_weak_trace_zero (p : AlgebraProjection M) (hp : p.val ≠ 0) (x : H) :
    Tendsto (fun n => inner ℂ x ((dyadicRademacher τ hdiff p n : H →L[ℂ] H) τ.vector))
      atTop (𝓝 0) := by
  let s : ℝ := τ.norm₂ p.val
  have hs : 0 < s := lt_of_le_of_ne (norm_nonneg _) (fun h => hp ((τ.norm₂_eq_zero_iff p.val).mp h.symm))
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  let v : ℕ → H := fun n => (s : ℂ)⁻¹ • ((dyadicRademacher τ hdiff p n : H →L[ℂ] H) τ.vector)
  have hv : Orthonormal ℂ v := by
    constructor
    · intro n
      change ‖(s : ℂ)⁻¹ • ((dyadicRademacher τ hdiff p n : H →L[ℂ] H) τ.vector)‖=1
      rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hs.le]
      change s⁻¹*τ.norm₂ (dyadicRademacher τ hdiff p n)=1
      rw [dyadicRademacher_norm₂]
      exact inv_mul_cancel₀ hs.ne'
    · intro m n hmn
      dsimp [v]
      rw [inner_smul_left,inner_smul_right,coordinate_inner_eq_trace,
        dyadicRademacher_star,dyadicRademacher_trace_mul_of_ne τ hdiff p hmn,mul_zero,mul_zero]
  have ht := (orthonormal_inner_tendsto_zero v hv x).const_mul (s : ℂ)
  simp only [mul_zero] at ht
  apply ht.congr
  intro n
  dsimp [v]
  rw [inner_smul_right,← mul_assoc,mul_inv_cancel₀ hsC,one_mul]

/-- The same sequence has vanishing ambient mixed traces, even when the
coefficients belong to M and the partial unitaries belong to P. -/
theorem inclusion_corner_mixed_trace_zero {P : VonNeumannAlgebra H} (hPM : P ≤ M)
    (hdiffP : ∀ p : P.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : P.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)
    (p : AlgebraProjection P) (hp : p.val ≠ 0) (x y : M.toStarSubalgebra) :
    Tendsto (fun n => τ.trace (x*coordinateInclusion hPM
      (dyadicCornerUnitary (restrictedTrace τ hPM) hdiffP p n).val*y)) atTop (𝓝 0) := by
  have ht := dyadicRademacher_weak_trace_zero (restrictedTrace τ hPM) hdiffP p hp
    (((star (y*x) : M.toStarSubalgebra) : H →L[ℂ] H) τ.vector)
  apply ht.congr
  intro n
  change inner ℂ (((star (y*x) : M.toStarSubalgebra) : H →L[ℂ] H) τ.vector)
    ((coordinateInclusion hPM (dyadicCornerUnitary (restrictedTrace τ hPM) hdiffP p n).val : H →L[ℂ] H) τ.vector)=_
  rw [coordinate_inner_eq_trace,star_star,τ.trace_mul_comm (x*_) y,← mul_assoc]

/-- Actual simultaneous scalar nonintertwining choices in every nonzero
corner, with arbitrary finite sets of ambient left and right coefficients. -/
theorem exists_cornerUnitary_small_mixed_traces {P : VonNeumannAlgebra H} (hPM : P ≤ M)
    (hdiffP : ∀ p : P.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : P.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)
    (p : AlgebraProjection P) (hp : p.val ≠ 0)
    (F G : Finset M.toStarSubalgebra) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : CornerUnitary p, ∀ x ∈ F, ∀ y ∈ G,
      ‖τ.trace (x*coordinateInclusion hPM v.val*y)‖ < ε := by
  have he : ∀ᶠ n : ℕ in atTop, ∀ x ∈ F, ∀ y ∈ G,
      ‖τ.trace (x*coordinateInclusion hPM
        (dyadicCornerUnitary (restrictedTrace τ hPM) hdiffP p n).val*y)‖ < ε := by
    rw [eventually_all_finset]
    intro x hx
    rw [eventually_all_finset]
    intro y hy
    have ht := (inclusion_corner_mixed_trace_zero τ hPM hdiffP p hp x y).norm
    simp only [norm_zero] at ht
    exact ht (Iio_mem_nhds hε)
  obtain ⟨n,hn⟩ := he.exists
  exact ⟨dyadicCornerUnitary (restrictedTrace τ hPM) hdiffP p n,hn⟩

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_PatchingWords
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Ordered signed mixed words in Popa 1308.3982v3, Lemma 3.2.
The L2 continuity estimate keeps the order of every coefficient. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem signedLetter_norm (v : M.toStarSubalgebra) (s : Bool) :
    ‖signedLetter v s‖=‖v‖ := by
  cases s
  · rfl
  · change ‖star (v : H →L[ℂ] H)‖=‖(v : H →L[ℂ] H)‖
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact ContinuousLinearMap.adjoint.norm_map _

theorem patchingWord_norm_le_one (v : M.toStarSubalgebra) (hv : ‖v‖ ≤ 1)
    (xs : List (Bool × M.toStarSubalgebra)) (hx : ∀ a ∈ xs, ‖a.2‖ ≤ 1) :
    ‖patchingWord v xs‖ ≤ 1 := by
  induction xs with
  | nil => exact (IsStarProjection.one (M.toStarSubalgebra)).norm_le
  | cons a xs ih =>
    have ha := hx a (by simp)
    have ht := ih (fun b hb => hx b (by simp [hb]))
    have hs : ‖signedLetter v a.1*a.2‖ ≤ 1 :=
      (norm_mul_le _ _).trans ((mul_le_mul (by rw [signedLetter_norm]; exact hv) ha
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1))
    exact (norm_mul_le _ _).trans ((mul_le_mul hs ht (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1))

/-- Actual simultaneous control of signed one-patch terms, including arbitrary
ambient coefficients. This uses the constructed corner unitaries in P. -/
theorem exists_cornerUnitary_small_signed_traces (τ : TracialRepresentation M)
    {P : VonNeumannAlgebra H} (hPM : P ≤ M)
    (hdiffP : ∀ p : P.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : P.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (p : AlgebraProjection P) (hp : p.val ≠ 0) (F G : Finset M.toStarSubalgebra)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ v : CornerUnitary p, ∀ x ∈ F, ∀ y ∈ G, ∀ s : Bool,
      ‖τ.trace (x*signedLetter (coordinateInclusion hPM v.val) s*y)‖ < ε := by
  classical
  obtain ⟨v,hv⟩ := exists_cornerUnitary_small_mixed_traces τ hPM hdiffP p hp
    (F ∪ G.image star) (G ∪ F.image star) ε hε
  refine ⟨v,fun x hx y hy s => ?_⟩
  cases s
  · exact hv x (Finset.mem_union_left _ hx) y (Finset.mem_union_left _ hy)
  · have hh := hv (star y) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y,hy,rfl⟩))
      (star x) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩))
    have he : τ.trace (star (x*star (coordinateInclusion hPM v.val)*y)) =
        star (τ.trace (x*star (coordinateInclusion hPM v.val)*y)) := by
      let z := x*star (coordinateInclusion hPM v.val)*y
      change inner ℂ τ.vector (star (z : H →L[ℂ] H) τ.vector)=
        star (inner ℂ τ.vector ((z : H →L[ℂ] H) τ.vector))
      rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
      exact (inner_conj_symm _ _).symm
    simp only [star_mul,star_star,← mul_assoc] at he
    rw [he,norm_star] at hh
    exact hh

end

/-! The scalar-commutant specialization of the error-constrained chain and
Zorn step in Popa 1308.3982v3 Lemma 3.2. The internal coefficients are in F;
only the two endpoints may be 1. No local-quantization or growth assumption. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem patchingCoefficients_norm (F : Set M.toStarSubalgebra)
    (hF : ∀ x ∈ F, ‖x‖ ≤ 1) (xs : List (Bool × M.toStarSubalgebra))
    (hx : patchingCoefficients F xs) : ∀ a ∈ xs, ‖a.2‖ ≤ 1 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases xs with
    | nil =>
      have ha : ‖a.2‖ ≤ 1 := by
        rcases hx with h | h
        · exact hF _ h
        · rw [Set.mem_singleton_iff.mp h]; exact (IsStarProjection.one (M.toStarSubalgebra)).norm_le
      simpa using ha
    | cons b xs =>
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hF _ hx.1
      · exact ih hx.2 c hc

end

/-! The error-constrained partial unitaries stay in the prescribed algebra P,
while all word coefficients and the trace live in M. This prevents replacing
the source inclusion P subset M by the trivial inclusion M subset M. -/

/-! Finite enumeration of the actual ordered word family. Only endpoints may
be 1. The middle segments retain all signs and their precise lengths. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem mem_boundedLists {α : Type*} (A : Finset α) (n : ℕ) (xs : List α) :
    xs ∈ boundedLists A n ↔ xs.length ≤ n ∧ ∀ a ∈ xs, a ∈ A := by
  classical
  induction n generalizing xs with
  | zero => cases xs <;> simp [boundedLists]
  | succ n ih =>
    cases xs with
    | nil => simp [boundedLists]
    | cons a xs => simp [boundedLists, ih, List.length_cons, and_left_comm]

theorem patchingCoefficients_mem (F : Set M.toStarSubalgebra)
    (xs : List (Bool × M.toStarSubalgebra)) (hx : patchingCoefficients F xs) :
    ∀ a ∈ xs, a.2 ∈ F ∪ {1} := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases xs with
    | nil => simpa [patchingCoefficients, or_comm] using hx
    | cons b xs =>
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact Or.inl hx.1
      · exact ih hx.2 c hc

theorem mem_middleWordFamily (F : Finset M.toStarSubalgebra) (n : ℕ)
    (x : M.toStarSubalgebra) (xs : List (Bool × M.toStarSubalgebra)) :
    (x,xs) ∈ middleWordFamily F n ↔
      x ∈ F ∧ xs.length+2 ≤ n ∧ ∀ a ∈ xs,a.2 ∈ F := by
  classical
  simp only [middleWordFamily,Finset.mem_filter,Finset.mem_product,
    mem_boundedLists,mem_signedAlphabet]
  constructor
  · rintro ⟨⟨hx,hlen,ha⟩,hb⟩; exact ⟨hx,hb,ha⟩
  · rintro ⟨hx,hb,ha⟩; exact ⟨⟨hx,by omega,ha⟩,hb⟩

theorem mem_outerWordFamily (v : M.toStarSubalgebra) (F : Finset M.toStarSubalgebra)
    (n : ℕ) (x : M.toStarSubalgebra) (xs : List (Bool × M.toStarSubalgebra))
    (hx : x ∈ (F : Set M.toStarSubalgebra) ∪ {1}) (hlen : xs.length ≤ n)
    (ha : ∀ a ∈ xs,a.2 ∈ (F : Set M.toStarSubalgebra) ∪ {1}) :
    x*patchingWord v xs ∈ outerWordFamily v F n := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨(x,xs),Finset.mem_product.mpr ⟨by simpa using hx.symm,?_⟩,rfl⟩
  exact (mem_boundedLists _ _ _).mpr ⟨hlen,fun a h => by
    simpa using (ha a h).symm⟩

end

/-! The two moment bounds in Popa Lemma 3.2 equation (6), derived from
admissibility for the actual signed internal segment, including length zero. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem patchingCoefficients_of_internal (F : Set M.toStarSubalgebra)
    (xs : List (Bool × M.toStarSubalgebra)) (hx : ∀ a ∈ xs,a.2 ∈ F) :
    patchingCoefficients F xs := by
  induction xs with
  | nil => trivial
  | cons a xs ih =>
    cases xs with
    | nil => exact Or.inl (hx a (by simp))
    | cons b xs =>
      exact ⟨hx a (by simp),ih (fun c hc => hx c (by simp [hc]))⟩

theorem patchingCoefficients_append_endpoint (F : Set M.toStarSubalgebra)
    (xs : List (Bool × M.toStarSubalgebra)) (hx : ∀ a ∈ xs,a.2 ∈ F)
    (a : Bool × M.toStarSubalgebra) (ha : a.2 ∈ F ∪ {1}) :
    patchingCoefficients F (xs ++ [a]) := by
  induction xs with
  | nil => exact ha
  | cons b xs ih =>
    have ht := ih (fun c hc => hx c (by simp [hc]))
    cases xs with
    | nil => exact ⟨hx b (by simp),ht⟩
    | cons c xs => exact ⟨hx b (by simp),ht⟩

theorem patchingWord_append (v : M.toStarSubalgebra)
    (xs ys : List (Bool × M.toStarSubalgebra)) :
    patchingWord v (xs++ys)=patchingWord v xs*patchingWord v ys := by
  induction xs with
  | nil => simp [patchingWord]
  | cons a xs ih => simp [patchingWord,ih,mul_assoc]

theorem admissible_middle_trace (v : PartialUnitary M) (f : AlgebraProjection M)
    (F : Set M.toStarSubalgebra) (n : ℕ) (ε : ℕ → ℝ)
    (hv : PatchingAdmissible τ f F n ε v) (hcenter : ∀ x ∈ F,τ.trace x=0)
    (x : M.toStarSubalgebra) (xs : List (Bool × M.toStarSubalgebra))
    (hx : x ∈ F) (hxs : ∀ a ∈ xs,a.2 ∈ F) (hlen : xs.length ≤ n) :
    ‖τ.trace (x*patchingWord v.val xs)‖ ≤
      middleMomentError ε xs.length*(τ.trace v.support.val).re := by
  cases xs with
  | nil => simp [patchingWord,middleMomentError,hcenter x hx]
  | cons a xs =>
    exact hv.2 x (Or.inl hx) (a::xs) (by simp) hlen
      (patchingCoefficients_of_internal F _ hxs)

/-- Appending a positive v and prepending v* gives an admitted word of length r+2.
The two new endpoint coefficients are exactly 1. -/
theorem admissible_middle_second_trace (v : PartialUnitary M) (f : AlgebraProjection M)
    (F : Set M.toStarSubalgebra) (n : ℕ) (ε : ℕ → ℝ)
    (hv : PatchingAdmissible τ f F n ε v)
    (x : M.toStarSubalgebra) (xs : List (Bool × M.toStarSubalgebra))
    (hx : x ∈ F) (hxs : ∀ a ∈ xs,a.2 ∈ F) (hlen : xs.length+2 ≤ n) :
    ‖τ.trace (star v.val*(x*patchingWord v.val xs)*v.val)‖ ≤
      ε (xs.length+2)*(τ.trace v.support.val).re := by
  let ys : List (Bool × M.toStarSubalgebra) := (true,x)::(xs++[(false,1)])
  have hi : ∀ a ∈ (true,x)::xs,a.2 ∈ F := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hx
    · exact hxs a ha
  have hc : patchingCoefficients F ys :=
    patchingCoefficients_append_endpoint F ((true,x)::xs) hi (false,1) (Or.inr rfl)
  have hy : ys.length=xs.length+2 := by simp [ys]
  have hh := hv.2 1 (Or.inr rfl) ys (by rw [hy]; omega) (by rw [hy]; exact hlen) hc
  rw [hy] at hh
  simpa only [ys,patchingWord,patchingWord_append,signedLetter, Bool.false_eq_true,
    ↓reduceIte, mul_one,one_mul,mul_assoc] using hh

theorem middleWordFamily_moments (v : PartialUnitary M) (f : AlgebraProjection M)
    (F : Finset M.toStarSubalgebra) (n : ℕ) (ε : ℕ → ℝ)
    (hv : PatchingAdmissible τ f (F : Set M.toStarSubalgebra) n ε v)
    (hcenter : ∀ x ∈ F,τ.trace x=0)
    (i : M.toStarSubalgebra × List (Bool × M.toStarSubalgebra))
    (hi : i ∈ middleWordFamily F n) :
    ‖τ.trace (i.1*patchingWord v.val i.2)‖ ≤
        middleMomentError ε i.2.length*(τ.trace v.support.val).re ∧
      ‖τ.trace (star v.val*(i.1*patchingWord v.val i.2)*v.val)‖ ≤
        ε (i.2.length+2)*(τ.trace v.support.val).re := by
  obtain ⟨hx,hlen,hxs⟩ := (mem_middleWordFamily F n i.1 i.2).mp hi
  exact ⟨admissible_middle_trace τ v f F n ε hv hcenter i.1 i.2 hx hxs (by omega),
    admissible_middle_second_trace τ v f F n ε hv i.1 i.2 hx hxs hlen⟩

end

/-! Actual noncommutative binary expansion in Popa Lemma 3.2, equation (1).
Each list entry retains the number of patch letters used and its ordered
operator product. There is no commuting-coefficient hypothesis. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem sum_map_left_mul (a : M.toStarSubalgebra) (xs : List M.toStarSubalgebra) :
    (xs.map (fun x => a*x)).sum=a*xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,mul_add]

theorem signedLetter_add (v w : M.toStarSubalgebra) (s : Bool) :
    signedLetter (v+w) s=signedLetter v s+signedLetter w s := by
  cases s <;> simp [signedLetter,star_add]

theorem patchingExpansion_sum (v w : M.toStarSubalgebra)
    (xs : List (Bool × M.toStarSubalgebra)) :
    ((patchingExpansion v w xs).map Prod.snd).sum=patchingWord (v+w) xs := by
  induction xs with
  | nil => simp [patchingExpansion,patchingWord]
  | cons a xs ih =>
    simp only [patchingExpansion,List.map_append,List.sum_append,List.map_map,Function.comp_def]
    have hv : ((patchingExpansion v w xs).map (fun z => signedLetter v a.1*a.2*z.2)).sum =
        (signedLetter v a.1*a.2)*((patchingExpansion v w xs).map Prod.snd).sum := by
      simpa only [List.map_map,Function.comp_def] using
        sum_map_left_mul (signedLetter v a.1*a.2) ((patchingExpansion v w xs).map Prod.snd)
    have hw : ((patchingExpansion v w xs).map (fun z => signedLetter w a.1*a.2*z.2)).sum =
        (signedLetter w a.1*a.2)*((patchingExpansion v w xs).map Prod.snd).sum := by
      simpa only [List.map_map,Function.comp_def] using
        sum_map_left_mul (signedLetter w a.1*a.2) ((patchingExpansion v w xs).map Prod.snd)
    rw [hv,hw,ih]
    simp only [patchingWord,signedLetter_add,add_mul]

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_PatchingBounds
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Exact positive tolerance recurrence used in Popa Lemma 3.2. -/
section

theorem patchingTolerance_pos (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    0 < patchingTolerance δ k := by
  induction k with
  | zero => exact hδ
  | succ k ih => exact mul_pos (pow_pos (by norm_num) _) ih

theorem patchingTolerance_four_mul_le (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    4*patchingTolerance δ k ≤ patchingTolerance δ (k+1) := by
  have hp : (4 : ℝ) ≤ 2^(k+2) := by
    have h := one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := k)
    rw [pow_add]
    norm_num
    nlinarith only [h]
  exact mul_le_mul_of_nonneg_right hp (patchingTolerance_pos δ hδ k).le

theorem patchingTolerance_mono (δ : ℝ) (hδ : 0 < δ) : Monotone (patchingTolerance δ) := by
  apply monotone_nat_of_le_succ
  intro k
  have hp := patchingTolerance_pos δ hδ k
  have hh := patchingTolerance_four_mul_le δ hδ k
  linarith

theorem middleMomentError_nonneg (ε : ℕ → ℝ) (hε : ∀ k,0 ≤ ε k) (r : ℕ) :
    0 ≤ middleMomentError ε r := by
  unfold middleMomentError
  split
  · exact le_rfl
  · exact hε r

/-- Choose eta=delta/3. Both middle moments fit within 2 epsilon_(r+2)/3. -/
theorem patchingTolerance_middle_budget (δ : ℝ) (hδ : 0 < δ) (r : ℕ) :
    δ/3+(middleMomentError (patchingTolerance δ) r+patchingTolerance δ (r+2))/3 ≤
      2*patchingTolerance δ (r+2)/3 := by
  have hm : middleMomentError (patchingTolerance δ) r ≤ patchingTolerance δ r := by
    unfold middleMomentError
    split
    · exact (patchingTolerance_pos δ hδ r).le
    · exact le_rfl
  have hd : δ ≤ patchingTolerance δ r := patchingTolerance_mono δ hδ (Nat.zero_le r)
  have hstep := patchingTolerance_four_mul_le δ hδ r
  have hstep2 := patchingTolerance_mono δ hδ (show r+1 ≤ r+2 by omega)
  have hp := patchingTolerance_pos δ hδ r
  linarith

end

/-! Explicit binary masks for the existing ordered expansion. A true bit is a
patch letter. Occurrences are retained even when their operator values coincide. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem mem_binaryMasks (n : ℕ) (bs : List Bool) :
    bs ∈ binaryMasks n ↔ bs.length=n := by
  induction n generalizing bs with
  | zero => simp [binaryMasks]
  | succ n ih =>
    cases bs with
    | nil => simp [binaryMasks]
    | cons b bs => cases b <;> simp [binaryMasks,ih]

theorem binaryMasks_length (n : ℕ) : (binaryMasks n).length=2^n := by
  induction n with
  | zero => simp [binaryMasks]
  | succ n ih => simp [binaryMasks,ih,pow_succ]; omega

theorem patchingExpansion_eq_masks (v w : M.toStarSubalgebra)
    (xs : List (Bool × M.toStarSubalgebra)) :
    patchingExpansion v w xs = (binaryMasks xs.length).map
      (fun bs => (bs.count true,maskedWord v w xs bs)) := by
  induction xs with
  | nil => simp [patchingExpansion,binaryMasks,maskedWord]
  | cons a xs ih =>
    simp [patchingExpansion,binaryMasks,ih,List.map_map,Function.comp_def,maskedWord]

theorem maskedWord_append (v w : M.toStarSubalgebra)
    (xs ys : List (Bool × M.toStarSubalgebra)) (bs cs : List Bool)
    (hlen : bs.length=xs.length) :
    maskedWord v w (xs++ys) (bs++cs) = maskedWord v w xs bs*maskedWord v w ys cs := by
  induction xs generalizing bs with
  | nil => have hb : bs=[] := List.length_eq_zero_iff.mp hlen; simp [hb,maskedWord]
  | cons a xs ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs => simp [maskedWord,ih bs (by simpa using hlen),mul_assoc]

theorem maskedWord_no_patch (v w : M.toStarSubalgebra)
    (xs : List (Bool × M.toStarSubalgebra)) :
    maskedWord v w xs (List.replicate xs.length false)=patchingWord v xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [maskedWord,patchingWord,List.replicate_succ,ih]

theorem maskedWord_norm_le_one (v w : M.toStarSubalgebra) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (xs : List (Bool × M.toStarSubalgebra)) (bs : List Bool)
    (hx : ∀ a ∈ xs,‖a.2‖ ≤ 1) : ‖maskedWord v w xs bs‖ ≤ 1 := by
  induction xs generalizing bs with
  | nil => exact (IsStarProjection.one _).norm_le
  | cons a xs ih =>
    have hp : ‖if bs.headD false then w else v‖ ≤ 1 := by split <;> assumption
    have ha := hx a (by simp)
    have ht := ih bs.tail (fun c hc => hx c (by simp [hc]))
    have hs : ‖signedLetter (if bs.headD false then w else v) a.1*a.2‖ ≤ 1 := by
      apply (norm_mul_le _ _).trans
      rw [signedLetter_norm]
      exact (mul_le_mul hp ha (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
    exact (norm_mul_le _ _).trans
      ((mul_le_mul hs ht (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1))

/-- Locate the first patch, with no earlier patch occurrences. -/
theorem exists_first_true (bs : List Bool) (h : 1 ≤ bs.count true) :
    ∃ i cs,bs=List.replicate i false++true::cs := by
  induction bs with
  | nil => simp at h
  | cons b bs ih =>
    cases b with
    | true => exact ⟨0,bs,rfl⟩
    | false =>
      obtain ⟨i,cs,he⟩ := ih (by simpa using h)
      exact ⟨i+1,cs,by simp [List.replicate_succ,he]⟩

/-- Locate the first two patches; all bits before and between them are false. -/
theorem exists_first_two_true (bs : List Bool) (h : 2 ≤ bs.count true) :
    ∃ i r cs,bs=List.replicate i false++true::(List.replicate r false++true::cs) := by
  obtain ⟨i,ds,he⟩ := exists_first_true bs (by omega)
  have hd : 1 ≤ ds.count true := by
    rw [he] at h
    simpa [List.count_replicate] using h
  obtain ⟨r,cs,hr⟩ := exists_first_true ds hd
  exact ⟨i,r,cs,by rw [he,hr]⟩

/-- The second moment has full word length only for the two-endpoint mask. -/
theorem first_two_full_length_iff (i r : ℕ) (cs : List Bool) :
    r+2=(List.replicate i false++true::(List.replicate r false++true::cs)).length ↔
      i=0 ∧ cs=[] := by
  simp only [List.length_append,List.length_replicate,List.length_cons]
  rw [← List.length_eq_zero_iff]
  omega

end

/-! Mask uniqueness and a deliberately coarse budget that avoids off-by-one
counts: 2^k ordinary budgets plus one exceptional budget fit epsilon_k. -/
section

theorem binaryMasks_nodup (n : ℕ) : (binaryMasks n).Nodup := by
  induction n with
  | zero => simp [binaryMasks]
  | succ n ih =>
    rw [binaryMasks,List.nodup_append]
    refine ⟨ih.map (fun _ _ h => List.cons.inj h |>.2),
      ih.map (fun _ _ h => List.cons.inj h |>.2),?_⟩
    intro a ha b hb
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hb
    simp

theorem count_true_zero_iff (bs : List Bool) :
    bs.count true=0 ↔ bs=List.replicate bs.length false := by
  induction bs with
  | nil => simp
  | cons b bs ih => cases b <;> simp [List.replicate_succ,ih]

theorem first_two_eq_exceptional (i r : ℕ) (cs : List Bool)
    (h : r+2=(List.replicate i false++true::(List.replicate r false++true::cs)).length) :
    List.replicate i false++true::(List.replicate r false++true::cs) =
      exceptionalMask (List.replicate i false++true::(List.replicate r false++true::cs)).length := by
  obtain ⟨hi,hcs⟩ := (first_two_full_length_iff i r cs).mp h
  subst i; subst cs
  simp [exceptionalMask,Nat.add_comm]
  omega

theorem sum_indicator_le {α : Type*} [DecidableEq α] (xs : List α) (hn : xs.Nodup)
    (a : α) (B : ℝ) (hB : 0 ≤ B) :
    (xs.map (fun b => if b=a then B else 0)).sum ≤ B := by
  have he : (xs.map (fun b => if b=a then B else 0)).sum = (xs.count a : ℝ)*B := by
    clear hn
    induction xs with
    | nil => simp
    | cons b xs ih =>
      by_cases h : b=a
      · subst b; simp [ih,add_mul]; ring
      · simp [h,ih]
  rw [he]
  have hh : xs.count a ≤ 1 := (List.nodup_iff_count_le_one.mp hn) a
  have hh' : (xs.count a : ℝ) ≤ 1 := by exact_mod_cast hh
  exact (mul_le_mul_of_nonneg_right hh' hB).trans_eq (one_mul B)

theorem sum_three_budgets {α : Type*} [DecidableEq α]
    (xs : List α) (hn : xs.Nodup) (f : α → ℝ) (a b : α) (C A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ x ∈ xs,f x ≤ C+(if x=a then A else 0)+(if x=b then B else 0)) :
    (xs.map f).sum ≤ (xs.length : ℝ)*C+A+B := by
  have he : (xs.map (fun x => C+(if x=a then A else 0)+(if x=b then B else 0))).sum =
      (xs.length : ℝ)*C+(xs.map (fun x => if x=a then A else 0)).sum+
        (xs.map (fun x => if x=b then B else 0)).sum := by
    clear hn hf
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
                      rw [ih]; ring
  have hle : (xs.map f).sum ≤
      (xs.map (fun x => C+(if x=a then A else 0)+(if x=b then B else 0))).sum := by
    clear he hn
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons,List.sum_cons]
      exact add_le_add (hf x (by simp))
        (ih (fun y hy => hf y (by simp [hy])))
  rw [he] at hle
  have h₁ := sum_indicator_le xs hn a A hA
  have h₂ := sum_indicator_le xs hn b B hB
  linarith

/-- The coarse ordinary+exceptional budget is exactly epsilon_k. The two
special masks are each counted only once; no binomial count is assumed. -/
theorem patchingTolerance_mask_budget (δ : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (2^k : ℝ)*(2*patchingTolerance δ (k-1)/3)+2*patchingTolerance δ k/3 =
      patchingTolerance δ k := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel,patchingTolerance_succ]
  rw [show j+2=(j+1)+1 by omega,pow_succ]
  ring

end

/-! Extract actual coefficient segments and fixed one-patch outer factors.
These lemmas apply to the source lists without assuming segment membership. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem exists_list_split {α : Type*} (xs : List α) (i : ℕ) (hi : i < xs.length) :
    ∃ pre a post,xs=pre++a::post ∧ pre.length=i := by
  induction i generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at hi
    | cons a xs => exact ⟨[],a,xs,rfl,rfl⟩
  | succ i ih =>
    cases xs with
    | nil => simp at hi
    | cons a xs =>
      obtain ⟨pre,b,post,he,hp⟩ := ih xs (by simpa using hi)
      exact ⟨a::pre,b,post,by simp [he],by simp [hp]⟩

theorem exists_list_split_two {α : Type*} (xs : List α) (i r : ℕ)
    (hlen : i+r+2 ≤ xs.length) :
    ∃ pre a mid b post,xs=pre++a::(mid++b::post) ∧ pre.length=i ∧ mid.length=r := by
  obtain ⟨pre,a,rest,he,hp⟩ := exists_list_split xs i (by omega)
  have hr : r < rest.length := by rw [he,List.length_append,List.length_cons,hp] at hlen; omega
  obtain ⟨mid,b,post,hm,hl⟩ := exists_list_split rest r hr
  exact ⟨pre,a,mid,b,post,by rw [he,hm],hp,hl⟩

theorem patchingCoefficients_before (F : Set M.toStarSubalgebra)
    (pre : List (Bool × M.toStarSubalgebra)) (a : Bool × M.toStarSubalgebra)
    (post : List (Bool × M.toStarSubalgebra))
    (h : patchingCoefficients F (pre++a::post)) :
    (∀ c ∈ pre,c.2 ∈ F) ∧ patchingCoefficients F (a::post) := by
  induction pre with
  | nil => exact ⟨by simp,h⟩
  | cons b pre ih =>
    have hb : b.2 ∈ F ∧ patchingCoefficients F (pre++a::post) := by
      cases pre <;> exact h
    obtain ⟨hi,ht⟩ := ih hb.2
    exact ⟨fun c hc => by
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hb.1
      · exact hi c hc,ht⟩

theorem patchingCoefficients_middle (F : Set M.toStarSubalgebra)
    (pre mid post : List (Bool × M.toStarSubalgebra)) (a b : Bool × M.toStarSubalgebra)
    (h : patchingCoefficients F (pre++a::(mid++b::post))) :
    a.2 ∈ F ∧ (∀ c ∈ mid,c.2 ∈ F) := by
  have ht := (patchingCoefficients_before F pre a (mid++b::post) h).2
  have hi := (patchingCoefficients_before F (a::mid) b post ht).1
  exact ⟨hi a (by simp),fun c hc => hi c (by simp [hc])⟩

theorem maskedWord_first_two (v w : M.toStarSubalgebra)
    (pre mid post : List (Bool × M.toStarSubalgebra)) (a b : Bool × M.toStarSubalgebra)
    (cs : List Bool) :
    maskedWord v w (pre++a::(mid++b::post))
      (List.replicate pre.length false++true::(List.replicate mid.length false++true::cs)) =
      patchingWord v pre*signedLetter w a.1*(a.2*patchingWord v mid)*
        signedLetter w b.1*(b.2*maskedWord v w post cs) := by
  rw [maskedWord_append v w pre _ _ _ (List.length_replicate ..),maskedWord_no_patch]
  simp only [maskedWord,List.headD_cons,List.tail_cons,↓reduceIte]
  rw [maskedWord_append v w mid _ _ _ (List.length_replicate ..),maskedWord_no_patch]
  simp [maskedWord,mul_assoc]

/-- Every mask with at least two true bits yields its actual internal middle
segment, with no assumptions about a separately supplied finite list. -/
theorem maskedWord_two_decomposition (F : Set M.toStarSubalgebra)
    (xs : List (Bool × M.toStarSubalgebra)) (hc : patchingCoefficients F xs)
    (bs : List Bool) (hlen : bs.length=xs.length) (hcount : 2 ≤ bs.count true) :
    ∃ pre a mid b post cs,
      xs=pre++a::(mid++b::post) ∧
      bs=List.replicate pre.length false++true::(List.replicate mid.length false++true::cs) ∧
      a.2 ∈ F ∧ (∀ c ∈ mid,c.2 ∈ F) ∧ cs.length=post.length ∧
      mid.length+2 ≤ xs.length := by
  obtain ⟨i,r,cs,hbs⟩ := exists_first_two_true bs hcount
  have hlen' : i+r+2+cs.length=xs.length := by
    rw [hbs] at hlen
    simp only [List.length_append,List.length_replicate,List.length_cons] at hlen
    omega
  obtain ⟨pre,a,mid,b,post,hxs,hp,hm⟩ := exists_list_split_two xs i r (by omega)
  have hi := patchingCoefficients_middle F pre mid post a b (by rwa [← hxs])
  have ht : cs.length=post.length := by
    rw [hxs,List.length_append,List.length_cons,List.length_append,List.length_cons,hp,hm] at hlen'
    omega
  exact ⟨pre,a,mid,b,post,cs,hxs,by simpa [hp,hm] using hbs,hi.1,hi.2,ht,by omega⟩

theorem maskedWord_one (v w : M.toStarSubalgebra)
    (pre post : List (Bool × M.toStarSubalgebra)) (a : Bool × M.toStarSubalgebra) :
    maskedWord v w (pre++a::post)
      (List.replicate pre.length false++true::List.replicate post.length false) =
      patchingWord v pre*signedLetter w a.1*(a.2*patchingWord v post) := by
  rw [maskedWord_append v w pre _ _ _ (List.length_replicate ..),maskedWord_no_patch]
  simp [maskedWord,maskedWord_no_patch,mul_assoc]

end

/-! The triangle inequality for the exact noncommutative mask expansion. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem trace_list_sum (xs : List M.toStarSubalgebra) :
    τ.trace xs.sum=(xs.map τ.trace).sum := by
  induction xs with
  | nil => exact inner_zero_right _
  | cons x xs ih => simp only [List.sum_cons,List.map_cons,cornerTrace_add,ih]

theorem norm_list_sum_le (xs : List ℂ) : ‖xs.sum‖ ≤ (xs.map norm).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simpa only [List.sum_cons,List.map_cons] using
      (norm_add_le x xs.sum).trans (add_le_add le_rfl ih)

theorem patching_trace_sum_le (v w x₀ : M.toStarSubalgebra)
    (xs : List (Bool × M.toStarSubalgebra)) :
    ‖τ.trace (x₀*patchingWord (v+w) xs)‖ ≤
      ((binaryMasks xs.length).map (fun bs => ‖τ.trace (x₀*maskedWord v w xs bs)‖)).sum := by
  rw [← patchingExpansion_sum,patchingExpansion_eq_masks]
  simp only [List.map_map,Function.comp_def]
  rw [← sum_map_left_mul,trace_list_sum]
  simpa only [List.map_map,Function.comp_def] using norm_list_sum_le
    ((((binaryMasks xs.length).map (fun bs => maskedWord v w xs bs)).map (fun z => x₀*z)).map τ.trace)

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_LocalPatches
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Construct local patches in the actual f=1 residual. Both residual trace
terms are retained. Admissibility of the full extended word family is not asserted. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

/-- Choose the patch unitary after q, so the same q controls all two-letter
terms and the signed one-letter traces are as small as prescribed. -/
theorem exists_unitResidual_controlled_patch
    (v : PartialUnitary M) (hvN : v.val.val ∈ N)
    (hsmall : (τ.trace v.support.val).re ≤ 1/4)
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra) (A B : ι → ℝ)
    (hAB : ∀ i ∈ F,0 ≤ A i+B i)
    (hA : ∀ i ∈ F,‖τ.trace (x i)‖ ≤ A i*(τ.trace v.support.val).re)
    (hB : ∀ i ∈ F,‖τ.trace (star v.val*x i*v.val)‖ ≤ B i*(τ.trace v.support.val).re)
    (L R : Finset M.toStarSubalgebra) (η κ : ℝ) (hη : 0 < η) (hκ : 0 < κ) :
    ∃ (q : AlgebraProjection M) (w : CornerUnitary q),
      q ≤ unitResidual v ∧ q.val ≠ 0 ∧ q.val.val ∈ N ∧ w.val.val ∈ N ∧
      (∀ a ∈ L,∀ b ∈ R,∀ s : Bool,‖τ.trace (a*signedLetter w.val s*b)‖ < κ*(τ.trace q.val).re) ∧
      (∀ i ∈ F,∀ u z : CornerUnitary q,∀ a b : M.toStarSubalgebra,‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
        ‖τ.trace (a*u.val*x i*z.val*b)‖ < (η+(A i+B i)/3)*(τ.trace q.val).re) := by
  obtain ⟨q,hqp,hq,hqN,hlocal⟩ := exists_unitResidual_local_compression τ hNM hfactor hdiff hirr hsep
    v hvN hsmall F x A B hAB hA hB η hη
  let qN := projectionInSubalgebra q hqN
  have hqN0 : qN.val ≠ 0 := by
    intro hz
    exact hq (Subtype.ext (congrArg (fun a : N.toStarSubalgebra => a.val) hz))
  obtain ⟨w,hw⟩ := exists_cornerUnitary_small_signed_traces τ hNM hdiff qN hqN0 L R
    (κ*(τ.trace q.val).re) (mul_pos hκ (projection_trace_pos τ q.val q.property hq))
  let wM : CornerUnitary q := {
    val := coordinateInclusion hNM w.val
    initial := by
      rw [← map_star,← map_mul,w.initial]
      rfl
    final := by
      rw [← map_star,← map_mul,w.final]
      rfl }
  refine ⟨q,wM,hqp,hq,hqN,w.val.property,hw,fun i hi u z a b ha hb => ?_⟩
  have hh := (hlocal i hi).1
  calc _ ≤ τ.norm₂ (q.val*x i*q.val)*τ.norm₂ q.val := two_patch_trace_le τ q u z a (x i) b ha hb
       _ < ((η+(A i+B i)/3)*τ.norm₂ q.val)*τ.norm₂ q.val :=
         mul_lt_mul_of_pos_right hh (corner_norm₂_pos τ q hq)
       _ = _ := by rw [projection_trace_sq τ q.val q.property]; ring

end

/-! A single actual residual patch controls every finite internal word of the
source family. All scalar moment premises are proved from admissibility. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem exists_admissible_family_patch
    (F : Finset M.toStarSubalgebra) (hcenter : ∀ x ∈ F,τ.trace x=0)
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (v : PartialUnitary M)
    (hv : PatchingAdmissibleIn (P := N) τ (identityProjection M) F n (patchingTolerance δ) v)
    (hsmall : (τ.trace v.support.val).re ≤ 1/4)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ (q : AlgebraProjection M) (w : CornerUnitary q),
      q ≤ unitResidual v ∧ q.val ≠ 0 ∧ q.val.val ∈ N ∧ w.val.val ∈ N ∧
      (∀ a ∈ outerWordFamily v.val F n,∀ b ∈ outerWordFamily v.val F n,∀ s : Bool,
        ‖τ.trace (a*signedLetter w.val s*b)‖ < κ*(τ.trace q.val).re) ∧
      (∀ x ∈ F,∀ xs : List (Bool × M.toStarSubalgebra),
        xs.length+2 ≤ n → (∀ a ∈ xs,a.2 ∈ F) →
        ∀ u z : CornerUnitary q,∀ a b : M.toStarSubalgebra,‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
        ‖τ.trace (a*u.val*(x*patchingWord v.val xs)*z.val*b)‖ <
          (2*patchingTolerance δ (xs.length+2)/3)*(τ.trace q.val).re) := by
  let X := middleWordFamily F n
  let mid := fun i : M.toStarSubalgebra × List (Bool × M.toStarSubalgebra) =>
    i.1*patchingWord v.val i.2
  let A := fun i : M.toStarSubalgebra × List (Bool × M.toStarSubalgebra) =>
    middleMomentError (patchingTolerance δ) i.2.length
  let B := fun i : M.toStarSubalgebra × List (Bool × M.toStarSubalgebra) =>
    patchingTolerance δ (i.2.length+2)
  have hm := middleWordFamily_moments τ v (identityProjection M) F n
    (patchingTolerance δ) hv.1 hcenter
  obtain ⟨q,w,hqp,hq,hqN,hwN,hfirst,hsecond⟩ := exists_unitResidual_controlled_patch τ hNM
    hfactor hdiff hirr hsep v hv.2 hsmall X mid A B
    (fun i _ => add_nonneg
      (middleMomentError_nonneg _ (fun k => (patchingTolerance_pos δ hδ k).le) _)
      (patchingTolerance_pos δ hδ _).le)
    (fun i hi => (hm i hi).1) (fun i hi => (hm i hi).2)
    (outerWordFamily v.val F n) (outerWordFamily v.val F n)
    (δ/3) κ (by positivity) hκ
  refine ⟨q,w,hqp,hq,hqN,hwN,hfirst,?_⟩
  intro x hx xs hlen hxs u z a b ha hb
  have hi : (x,xs) ∈ X := (mem_middleWordFamily F n x xs).mpr ⟨hx,hlen,hxs⟩
  have hh := hsecond (x,xs) hi u z a b ha hb
  exact hh.trans_le (mul_le_mul_of_nonneg_right (patchingTolerance_middle_budget δ hδ xs.length)
    (projection_trace_pos τ q.val q.property hq).le)

end

/-! Trace estimates for each actual binary-mask term, using the constructed
finite families. No moment estimate or middle-family extraction is assumed. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem maskedWord_one_decomposition
    (xs : List (Bool × M.toStarSubalgebra)) (bs : List Bool)
    (hlen : bs.length=xs.length) (hcount : bs.count true=1) :
    ∃ pre a post,xs=pre++a::post ∧
      bs=List.replicate pre.length false++true::List.replicate post.length false := by
  obtain ⟨i,cs,hbs⟩ := exists_first_true bs (by omega)
  have hc : cs.count true=0 := by simpa [hbs,List.count_replicate] using hcount
  have hcs := (count_true_zero_iff cs).mp hc
  have hl : i+1+cs.length=xs.length := by
    rw [hbs] at hlen
    simp only [List.length_append,List.length_replicate,List.length_cons] at hlen
    omega
  obtain ⟨pre,a,post,hxs,hp⟩ := exists_list_split xs i (by omega)
  have ht : cs.length=post.length := by rw [hxs,List.length_append,List.length_cons,hp] at hl; omega
  refine ⟨pre,a,post,hxs,?_⟩
  simpa only [hp,ht] using (hbs.trans (congrArg (fun ds => List.replicate i false++true::ds) hcs))

theorem maskedWord_one_trace_lt (v : PartialUnitary M) {q : AlgebraProjection M}
    (w : CornerUnitary q) (F : Finset M.toStarSubalgebra) (n : ℕ) (κ : ℝ)
    (hfirst : ∀ a ∈ outerWordFamily v.val F n,∀ b ∈ outerWordFamily v.val F n,∀ s : Bool,
      ‖τ.trace (a*signedLetter w.val s*b)‖ < κ*(τ.trace q.val).re)
    (x₀ : M.toStarSubalgebra) (hx₀ : x₀ ∈ (F : Set M.toStarSubalgebra) ∪ {1})
    (xs : List (Bool × M.toStarSubalgebra)) (hn : xs.length ≤ n)
    (hc : patchingCoefficients (F : Set M.toStarSubalgebra) xs)
    (bs : List Bool) (hlen : bs.length=xs.length) (hcount : bs.count true=1) :
    ‖τ.trace (x₀*maskedWord v.val w.val xs bs)‖ < κ*(τ.trace q.val).re := by
  obtain ⟨pre,a,post,hxs,hbs⟩ := maskedWord_one_decomposition xs bs hlen hcount
  have hall := patchingCoefficients_mem (F : Set M.toStarSubalgebra) xs hc
  have hpre : ∀ c ∈ pre,c.2 ∈ (F : Set M.toStarSubalgebra) ∪ {1} := by
    intro c hc; apply hall c; simp [hxs,hc]
  have hpost : ∀ c ∈ post,c.2 ∈ (F : Set M.toStarSubalgebra) ∪ {1} := by
    intro c hc; apply hall c; simp [hxs,hc]
  have ha : a.2 ∈ (F : Set M.toStarSubalgebra) ∪ {1} := hall a (by simp [hxs])
  have hsize : pre.length+1+post.length ≤ n := by simpa [hxs,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hn
  have hL := mem_outerWordFamily v.val F n x₀ pre hx₀ (by omega) hpre
  have hR := mem_outerWordFamily v.val F n a.2 post ha (by omega) hpost
  have hh := hfirst _ hL _ hR a.1
  rw [hxs,hbs,maskedWord_one]
  simpa only [mul_assoc] using hh

theorem maskedWord_two_trace_lt (v : PartialUnitary M) {q : AlgebraProjection M}
    (w : CornerUnitary q) (F : Finset M.toStarSubalgebra) (n : ℕ) (δ : ℝ)
    (hF : ∀ x ∈ F,‖x‖ ≤ 1)
    (hsecond : ∀ x ∈ F,∀ ys : List (Bool × M.toStarSubalgebra),
      ys.length+2 ≤ n → (∀ a ∈ ys,a.2 ∈ F) →
      ∀ u z : CornerUnitary q,∀ a b : M.toStarSubalgebra,‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      ‖τ.trace (a*u.val*(x*patchingWord v.val ys)*z.val*b)‖ <
        (2*patchingTolerance δ (ys.length+2)/3)*(τ.trace q.val).re)
    (x₀ : M.toStarSubalgebra) (h₀ : ‖x₀‖ ≤ 1)
    (xs : List (Bool × M.toStarSubalgebra)) (hn : xs.length ≤ n)
    (hc : patchingCoefficients (F : Set M.toStarSubalgebra) xs)
    (bs : List Bool) (hlen : bs.length=xs.length) (hcount : 2 ≤ bs.count true) :
    ∃ r,r+2 ≤ xs.length ∧
      (bs ≠ exceptionalMask xs.length → r+2 ≤ xs.length-1) ∧
      ‖τ.trace (x₀*maskedWord v.val w.val xs bs)‖ <
        (2*patchingTolerance δ (r+2)/3)*(τ.trace q.val).re := by
  obtain ⟨pre,a,mid,b,post,cs,hxs,hbs,ha,hm,ht,hsize⟩ :=
    maskedWord_two_decomposition (F : Set M.toStarSubalgebra) xs hc bs hlen hcount
  have hall := patchingCoefficients_norm (F : Set M.toStarSubalgebra) hF xs hc
  have hpre : ∀ c ∈ pre,‖c.2‖ ≤ 1 := by intro c hc; apply hall c; simp [hxs,hc]
  have hpost : ∀ c ∈ post,‖c.2‖ ≤ 1 := by intro c hc; apply hall c; simp [hxs,hc]
  have hb : ‖b.2‖ ≤ 1 := hall b (by simp [hxs])
  have hp := patchingWord_norm_le_one v.val v.unitary.norm_le_one pre hpre
  have ht' := maskedWord_norm_le_one v.val w.val v.unitary.norm_le_one w.norm_le_one post cs hpost
  have hL : ‖x₀*patchingWord v.val pre‖ ≤ 1 := (norm_mul_le _ _).trans
    ((mul_le_mul h₀ hp (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1))
  have hR : ‖b.2*maskedWord v.val w.val post cs‖ ≤ 1 := (norm_mul_le _ _).trans
    ((mul_le_mul hb ht' (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1))
  refine ⟨mid.length,hsize,?_,?_⟩
  · intro he
    by_contra h
    have heq : mid.length+2=xs.length := by omega
    have heq' : mid.length+2=
        (List.replicate pre.length false++true::(List.replicate mid.length false++true::cs)).length := by
      rw [← hbs,hlen,heq]
    have hh := first_two_eq_exceptional pre.length mid.length cs heq'
    rw [← hbs,hlen] at hh
    exact he hh
  · have hh := hsecond a.2 ha mid (by omega) hm
      (signedCornerUnitary w a.1) (signedCornerUnitary w b.1)
      (x₀*patchingWord v.val pre) (b.2*maskedWord v.val w.val post cs) hL hR
    rw [hxs,hbs,maskedWord_first_two]
    simpa only [signedCornerUnitary_val,mul_assoc] using hh

end

/-! Strict support growth for the actual f=1 admissible set. The single patch
is chosen from the finite coefficient families before any word is tested. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem unitResidualPatch_extends (v : PartialUnitary M) (q : AlgebraProjection M)
    (w : CornerUnitary q) (hq : q ≤ unitResidual v) : v ≤ unitResidualPatch v q w hq := by
  have hh := v.unitary.patch_extends w (unitResidual_orthogonal v q hq)
  change (v.unitary.patch w (unitResidual_orthogonal v q hq)).val*v.support.val=v.val
  simpa only [v.unitary.initial] using hh

theorem unitResidualPatch_trace (v : PartialUnitary M) (q : AlgebraProjection M)
    (w : CornerUnitary q) (hq : q ≤ unitResidual v) :
    (τ.trace (unitResidualPatch v q w hq).support.val).re =
      (τ.trace v.support.val).re+(τ.trace q.val).re := by
  change (τ.trace (v.support.val+q.val)).re=_
  rw [cornerTrace_add,Complex.add_re]

variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

/-- The full extension satisfies every original admissibility inequality and
has strictly greater support trace. No patch growth premise is assumed. -/
theorem exists_strict_admissible_unit_patch_oai
    (F : Finset M.toStarSubalgebra) (hF : ∀ x ∈ F,‖x‖ ≤ 1)
    (hcenter : ∀ x ∈ F,τ.trace x=0) (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (v : PartialUnitary M)
    (hv : PatchingAdmissibleIn (P := N) τ (identityProjection M) F n (patchingTolerance δ) v)
    (hsmall : (τ.trace v.support.val).re ≤ 1/4) :
    ∃ u : PartialUnitary M,
      PatchingAdmissibleIn (P := N) τ (identityProjection M) F n (patchingTolerance δ) u ∧
      v ≤ u ∧ (τ.trace v.support.val).re < (τ.trace u.support.val).re := by
  classical
  obtain ⟨q,w,hqp,hq,hqN,hwN,hfirst,hsecond⟩ := exists_admissible_family_patch τ hNM
    hfactor hdiff hirr hsep F hcenter n δ hδ v hv hsmall (δ/3) (by positivity)
  let u := unitResidualPatch v q w hqp
  have htq := projection_trace_pos τ q.val q.property hq
  have htv : 0 ≤ (τ.trace v.support.val).re := by
    rw [← v.unitary.trace_norm_sq τ]; positivity
  have hg : (τ.trace u.support.val).re=(τ.trace v.support.val).re+(τ.trace q.val).re :=
    unitResidualPatch_trace τ v q w hqp
  refine ⟨u,⟨⟨?_,?_⟩,?_⟩,unitResidualPatch_extends v q w hqp,by rw [hg]; linarith⟩
  · exact one_mul _
  · intro x₀ hx₀ xs hpos hn hc
    have h₀ : ‖x₀‖ ≤ 1 := by
      rcases hx₀ with h | h
      · exact hF x₀ h
      · rw [Set.mem_singleton_iff.mp h]; exact (IsStarProjection.one _).norm_le
    let k := xs.length
    let A := patchingTolerance δ k*(τ.trace v.support.val).re
    let B := (2*patchingTolerance δ k/3)*(τ.trace q.val).re
    let C := (2*patchingTolerance δ (k-1)/3)*(τ.trace q.val).re
    have hεk := patchingTolerance_pos δ hδ k
    have hεprev := patchingTolerance_pos δ hδ (k-1)
    have hA : 0 ≤ A := mul_nonneg (patchingTolerance_pos δ hδ k).le htv
    have hB : 0 ≤ B := mul_nonneg (by positivity) htq.le
    have hC : 0 ≤ C := mul_nonneg (by positivity) htq.le
    have hκ : (δ/3)*(τ.trace q.val).re ≤ C := by
      have hd : δ ≤ patchingTolerance δ (k-1) := patchingTolerance_mono δ hδ (Nat.zero_le _)
      apply mul_le_mul_of_nonneg_right _ htq.le
      linarith
    have hterm : ∀ bs ∈ binaryMasks k,
        ‖τ.trace (x₀*maskedWord v.val w.val xs bs)‖ ≤
          C+(if bs=List.replicate k false then A else 0)+(if bs=exceptionalMask k then B else 0) := by
      intro bs hbs
      have hlen : bs.length=xs.length := (mem_binaryMasks k bs).mp hbs
      have hAi : 0 ≤ (if bs=List.replicate k false then A else 0) := by split_ifs <;> positivity
      have hBi : 0 ≤ (if bs=exceptionalMask k then B else 0) := by split_ifs <;> positivity
      by_cases hz : bs.count true=0
      · have he : bs=List.replicate k false := by
          simpa only [hlen] using (count_true_zero_iff bs).mp hz
        have hh : ‖τ.trace (x₀*maskedWord v.val w.val xs bs)‖ ≤ A := by
          rw [he,maskedWord_no_patch]
          exact hv.1.2 x₀ hx₀ xs hpos hn hc
        rw [ite_eq_left he]
        linarith
      · by_cases ho : bs.count true=1
        · have hh := (maskedWord_one_trace_lt τ v w F n (δ/3) hfirst x₀ hx₀ xs hn hc bs hlen ho).le.trans hκ
          linarith
        · obtain ⟨r,hr,hex,hbound⟩ := maskedWord_two_trace_lt τ v w F n δ hF hsecond x₀ h₀ xs hn hc bs hlen (by omega)
          by_cases he : bs=exceptionalMask k
          · have hmono := patchingTolerance_mono δ hδ hr
            have hb : (2*patchingTolerance δ (r+2)/3)*(τ.trace q.val).re ≤ B := by
              apply mul_le_mul_of_nonneg_right _ htq.le
              linarith
            have hh := hbound.le.trans hb
            rw [ite_eq_left he]
            linarith
          · have hmono := patchingTolerance_mono δ hδ (hex he)
            have hb : (2*patchingTolerance δ (r+2)/3)*(τ.trace q.val).re ≤ C := by
              apply mul_le_mul_of_nonneg_right _ htq.le
              linarith
            have hh := hbound.le.trans hb
            linarith
    have hsum := sum_three_budgets (binaryMasks k) (binaryMasks_nodup k)
      (fun bs => ‖τ.trace (x₀*maskedWord v.val w.val xs bs)‖)
      (List.replicate k false) (exceptionalMask k) C A B hA hB hterm
    have hbudget : ((binaryMasks k).length : ℝ)*C+B=patchingTolerance δ k*(τ.trace q.val).re := by
      rw [binaryMasks_length,Nat.cast_pow,Nat.cast_ofNat]
      have hh := congrArg (fun z : ℝ => z*(τ.trace q.val).re) (patchingTolerance_mask_budget δ k hpos)
      dsimp [C,B]
      nlinarith only [hh]
    have hh := (patching_trace_sum_le τ v.val w.val x₀ xs).trans hsum
    change ‖τ.trace (x₀*patchingWord (v.val+w.val) xs)‖ ≤ _
    rw [hg]
    dsimp [A] at hh
    nlinarith only [hh,hbudget]
  · exact N.add_mem hv.2 hwN

end Generator.Tracial

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.exists_strict_admissible_unit_patch_oai.{u_1} := @OAI.Generator.Tracial.exists_strict_admissible_unit_patch_oai.{u_1}
