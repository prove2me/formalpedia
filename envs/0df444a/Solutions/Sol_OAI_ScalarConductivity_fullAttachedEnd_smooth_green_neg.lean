-- Prove2me | solution 1 for OAI.ScalarConductivity.fullAttachedEnd_smooth_green_neg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:13:36.135539+00:00
-- url     : https://prove2.me/submissions/f05c0a3d-2a8d-424c-9c8d-6bc51cc43fed

import Mathlib
import Definitions.Def_OAIQ059C008

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusFourierTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

lemma mFourier_norm_one {d : Type*} [Fintype d] (h : d → ℤ)
    (x : UnitAddTorus d) : ‖mFourier h x‖=1 := by
  simp [mFourier,fourier_apply,norm_prod,Circle.norm_coe]

end

open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CylinderGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

lemma poisson_complex_hermitian_green {q : ℝ → ℂ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (m R : ℝ) (a : ℂ) :
    (∫ t in (0:ℝ)..R,
      inner ℂ (axialDecayField m (-(m:ℂ)*a) t) (deriv q t) +
      (m^2:ℝ)*inner ℂ (axialDecayField m a t) (q t)) =
      (m:ℂ)*inner ℂ a (q 0)-(m*Real.exp (-m*R):ℝ)*inner ℂ a (q R) := by
  have he (t : ℝ) : HasDerivAt (fun t : ℝ => (Real.exp (-m*t):ℂ))
      ((Real.exp (-m*t)*(-m):ℝ):ℂ) t := by
    simpa only [id_eq,mul_one] using (((hasDerivAt_id t).const_mul (-m)).exp).ofReal_comp
  have hd (t : ℝ) : HasDerivAt
      (fun t : ℝ => (-(m:ℂ)*(Real.exp (-m*t):ℂ)*starRingEnd ℂ a)*q t)
      (inner ℂ (axialDecayField m (-(m:ℂ)*a) t) (deriv q t) +
        (m^2:ℝ)*inner ℂ (axialDecayField m a t) (q t)) t := by
    convert! (((he t).const_mul (-(m:ℂ))).mul_const (starRingEnd ℂ a)).mul
      ((hq.differentiable (by simp) t).hasDerivAt) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [axialDecayField,RCLike.inner_apply,map_mul,map_neg,Complex.conj_ofReal,
      Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_pow]
    ring
  have hc : Continuous (fun t : ℝ =>
      inner ℂ (axialDecayField m (-(m:ℂ)*a) t) (deriv q t) +
        (m^2:ℝ)*inner ℂ (axialDecayField m a t) (q t)) := by
    exact ((axialDecayField_continuous _ _).inner (hq.continuous_deriv (by simp))).add
      (continuous_const.mul ((axialDecayField_continuous _ _).inner hq.continuous))
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (hc.intervalIntegrable 0 R)
  rw [H]
  simp only [mul_zero,Real.exp_zero,Complex.ofReal_one,mul_one,RCLike.inner_apply,
    Complex.ofReal_mul]
  ring

lemma finiteDecay_green_inner {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (m R : ℝ) (hR : 0≤R) (a : ℂ) :
    inner ℂ (finiteDecayLp m R (-(m:ℂ)*a)) (smoothFiniteAxisLp (hq.continuous_deriv (by simp)) R)+
      (m^2:ℝ)*inner ℂ (finiteDecayLp m R a) (smoothFiniteAxisLp hq.continuous R)=
      (m:ℂ)*inner ℂ a (q 0)-(m*Real.exp (-m*R):ℝ)*inner ℂ a (q R) := by
  have h1 := L2.integrable_inner (𝕜:=ℂ) (finiteDecayLp m R (-(m:ℂ)*a))
    (smoothFiniteAxisLp (hq.continuous_deriv (by simp)) R)
  have h2 := L2.integrable_inner (𝕜:=ℂ) (finiteDecayLp m R a) (smoothFiniteAxisLp hq.continuous R)
  rw [L2.inner_def,L2.inner_def,←integral_const_mul,←integral_add h1 (h2.const_mul _)]
  have he : (∫ t,inner ℂ (finiteDecayLp m R (-(m:ℂ)*a) t)
      (smoothFiniteAxisLp (hq.continuous_deriv (by simp)) R t)+
      (m^2:ℝ)*inner ℂ (finiteDecayLp m R a t) (smoothFiniteAxisLp hq.continuous R t)
      ∂FiniteAxisMeasure R)=
      ∫ t in Ioc (0:ℝ) R,inner ℂ (axialDecayField m (-(m:ℂ)*a) t) (deriv q t)+
      (m^2:ℝ)*inner ℂ (axialDecayField m a t) (q t) := by
    apply integral_congr_ae
    filter_upwards [finiteDecayLp_ae m R (-(m:ℂ)*a),finiteDecayLp_ae m R a,
      smoothFiniteAxisLp_ae (hq.continuous_deriv (by simp)) R,smoothFiniteAxisLp_ae hq.continuous R]
      with t h1 h2 h3 h4
    rw [h1,h2,h3,h4]
  rw [he,←intervalIntegral.integral_of_le hR]
  exact poisson_complex_hermitian_green hq m R a

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_EndPoissonJets
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

local instance instMeasureSpaceUnitAddCircle_solutions_6_r28d5ce_1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
lemma endPoissonJet_hasSum (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) (hR : 0 ≤ R) (f : spectralTraceGraph (torusRate s)) :
    HasSum (fun h => endPoissonModeJet s R h (f.val 0 h)) (endPoissonJet s hs R hR f) := by
  have ht : Tendsto (fun F : Finset TorusModes => fun j => ∑ h ∈ F,endPoissonModeJet s R h (f.val 0 h) j)
      atTop (𝓝 (fun j => endPoissonJet s hs R hR f j)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    exact endPoissonJet_component_hasSum s hs R hR f j
  have hmap := (PiLp.continuous_toLp 2 (fun _ : Fin 4 => CylinderL2 (FiniteAxisMeasure R))).continuousAt.tendsto.comp ht
  change Tendsto (fun F : Finset TorusModes => ∑ h ∈ F,endPoissonModeJet s R h (f.val 0 h)) atTop _
  convert hmap using 1
  all_goals try with_reducible_and_instances rfl
  funext F
  apply PiLp.ext
  intro j
  simp only [Function.comp_apply,WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply]

end

open Set MeasureTheory Filter Topology
open scoped ENNReal

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_CylinderModeGreen
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

local instance cylinderModeGreenMeasureSpace_r28d5ce_1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
lemma cylinderMode_inner (R : ℝ) (h k : TorusModes) (f g : FiniteAxisL2 R) :
    inner ℂ (cylinderMode (FiniteAxisMeasure R) h f) (cylinderMode (FiniteAxisMeasure R) k g)=
      if h=k then inner ℂ f g else 0 := by
  by_cases he : h=k
  · subst k
    rw [ite_eq_left rfl]
    exact (cylinderMode (FiniteAxisMeasure R) h).inner_map_map f g
  · rw [ite_eq_right he]
    exact cylinderMode_orthogonal (FiniteAxisMeasure R) he f g

lemma flatCylinderEnergy_distinct_modes (s : Fin 3 → ℝ) {q : ℝ → ℂ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (R : ℝ) (h k : TorusModes) (a : ℂ) (hne : h≠k) :
    flatCylinderEnergy s (endPoissonModeJet s R h a) (smoothCylinderModeJet hq R k)=0 := by
  simp only [flatCylinderEnergy,endPoissonModeJet,smoothCylinderModeJet,WithLp.ofLp_toLp,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
    cylinderMode_inner,ite_eq_right hne,mul_zero,add_zero]

lemma torusRate_sq_of_lower (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2) (h : TorusModes) :
    torusRate s h^2=torusQuadratic s h := by
  apply Real.sq_sqrt
  exact (show (0:ℝ)≤(1/2)*((h 0:ℝ)^2+(h 1:ℝ)^2) by positivity).trans (hs _ _)

lemma flatCylinderEnergy_same_mode (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (R : ℝ) (h : TorusModes) (a : ℂ) :
    flatCylinderEnergy s (endPoissonModeJet s R h a) (smoothCylinderModeJet hq R h)=
      inner ℂ (finiteDecayLp (torusRate s h) R (-(torusRate s h:ℂ)*a))
        (smoothFiniteAxisLp (hq.continuous_deriv (by simp)) R)+
      ((torusRate s h)^2:ℝ)*inner ℂ (finiteDecayLp (torusRate s h) R a)
        (smoothFiniteAxisLp hq.continuous R) := by
  simp only [flatCylinderEnergy,endPoissonModeJet,smoothCylinderModeJet,WithLp.ofLp_toLp,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
    cylinderMode_inner,ite_true,endModeCoefficient]
  simp only [finiteDecayLp_smul,inner_smul_left,inner_smul_right,map_mul,map_intCast,Complex.conj_I]
  rw [torusRate_sq_of_lower s hs h]
  simp only [torusQuadratic,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_intCast,Complex.ofReal_ofNat]
  ring_nf
  simp only [Complex.I_sq]
  ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CylinderSeriesGreen
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem flatCylinder_series_mode_green (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (R : ℝ) (hR : 0≤R)
    (f : spectralTraceGraph (torusRate s)) (k : TorusModes) :
    flatCylinderEnergy s (endPoissonJet s hs R hR f) (smoothCylinderModeJet hq R k)=
      (torusRate s k:ℂ)*inner ℂ (f.val 0 k) (q 0)-
        (torusRate s k*Real.exp (-torusRate s k*R):ℝ)*inner ℂ (f.val 0 k) (q R) := by
  have H := (flatCylinderEnergyLeftCLM s (smoothCylinderModeJet hq R k)).hasSum
    (endPoissonJet_hasSum s hs R hR f)
  have Hsingle : HasSum (fun h => flatCylinderEnergy s
      (endPoissonModeJet s R h (f.val 0 h)) (smoothCylinderModeJet hq R k))
      (flatCylinderEnergy s (endPoissonModeJet s R k (f.val 0 k)) (smoothCylinderModeJet hq R k)) :=
    hasSum_single k (fun h hne => flatCylinderEnergy_distinct_modes s hq R h k _ hne)
  have he := H.unique Hsingle
  change flatCylinderEnergy s (endPoissonJet s hs R hR f) (smoothCylinderModeJet hq R k)=_ at he
  rw [he,flatCylinderEnergy_same_mode s hs hq R k _]
  exact finiteDecay_green_inner hq _ R hR _

theorem flatCylinder_series_polynomial_green (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (q : TorusModes → ℝ → ℂ) (hq : ∀ k,ContDiff ℝ (↑(⊤:ℕ∞)) (q k))
    (R : ℝ) (hR : 0≤R) (f : spectralTraceGraph (torusRate s)) (F : Finset TorusModes) :
    flatCylinderEnergy s (endPoissonJet s hs R hR f) (∑ k∈F,smoothCylinderModeJet (hq k) R k)=
      ∑ k∈F,((torusRate s k:ℂ)*inner ℂ (f.val 0 k) (q k 0)-
        (torusRate s k*Real.exp (-torusRate s k*R):ℝ)*inner ℂ (f.val 0 k) (q k R)) := by
  change flatCylinderEnergyRightCLM s (endPoissonJet s hs R hR f) _=_
  rw [map_sum]
  exact Finset.sum_congr rfl (fun k _ => flatCylinder_series_mode_green s hs (hq k) R hR f k)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CylinderJetOrthogonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma cylinderJetMode_smooth {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (R : ℝ) (h : TorusModes) :
    cylinderJetMode R h (smoothAxisModeJet hq R h)=smoothCylinderModeJet hq R h := by
  ext j
  fin_cases j <;> rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CylinderPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma cylinderPolynomialJetL_apply (R : ℝ) (p : TorusModes →₀ smoothComplexAxis) :
    cylinderPolynomialJetL R p=
      ∑ h∈p.support,smoothCylinderModeJet (smoothComplexAxis_smooth (p h)) R h := by
  rw [cylinderPolynomialJetL,Finsupp.lsum_apply]
  exact Finset.sum_congr rfl (fun h _ => cylinderJetMode_smooth _ R h)

open Set MeasureTheory Filter Topology
open scoped ENNReal

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CylinderCompletedGreen
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma spectralWeightedPair_single (s : Fin 3 → ℝ) (g : SpectralL2 TorusModes)
    (h : TorusModes) (a : ℂ) :
    spectralWeightedPairL s g (spectralTraceSingleL s h a)=
      inner ℂ (g h) ((Real.sqrt (torusRate s h):ℂ)*a) := by
  change inner ℂ g (lp.single 2 h ((Real.sqrt (torusRate s h):ℂ)*a))=_
  exact lp.inner_single_right h _ g

lemma spectralWeightedPair_initial (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s))
    (h : TorusModes) (a : ℂ) :
    spectralWeightedPairL s (f.val 1) (spectralTraceSingleL s h a)=
      (torusRate s h:ℂ)*inner ℂ (f.val 0 h) a := by
  rw [spectralWeightedPair_single,f.property h]
  have he : (Real.sqrt (torusRate s h):ℂ)^2=(torusRate s h:ℂ) := by
    exact_mod_cast Real.sq_sqrt (show 0≤torusRate s h from Real.sqrt_nonneg _)
  simp only [RCLike.inner_apply,map_mul,Complex.conj_ofReal]
  calc
    _=(Real.sqrt (torusRate s h):ℂ)^2*(starRingEnd ℂ (f.val 0 h)*a) := by ring
    _=_ := by rw [he]; ring

lemma spectralWeightedPair_terminal (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s))
    {R : ℝ} (hR : 0≤R) (h : TorusModes) (a : ℂ) :
    spectralWeightedPairL s (spectralEndWeight s R f) (spectralTraceSingleL s h a)=
      (torusRate s h*Real.exp (-torusRate s h*R):ℝ)*inner ℂ (f.val 0 h) a := by
  rw [spectralWeightedPair_single]
  change inner ℂ ((Real.exp (-torusRate s h*|R|):ℂ)*(f.val 1 h)) _=_
  rw [abs_of_nonneg hR]
  change inner ℂ ((Real.exp (-torusRate s h*R):ℂ) • (f.val 1 h)) _=_
  rw [inner_smul_left]
  rw [←spectralWeightedPair_single,spectralWeightedPair_initial]
  simp only [Complex.conj_ofReal,Complex.ofReal_mul]
  ring

lemma spectralWeightedPair_polynomial (s : Fin 3 → ℝ) (g : SpectralL2 TorusModes)
    (t : ℝ) (p : TorusModes →₀ smoothComplexAxis) :
    spectralWeightedPairL s g (cylinderPolynomialTraceL s t p)=
      ∑ h∈p.support,spectralWeightedPairL s g (spectralTraceSingleL s h (p h t)) := by
  rw [cylinderPolynomialTraceL,Finsupp.lsum_apply,Finsupp.sum,map_sum]
  rfl

theorem flatCylinder_completed_green (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {R : ℝ} (hR : 0<R) (f : spectralTraceGraph (torusRate s))
    (z : cylinderSobolevGraph s R) :
    flatCylinderEnergy s (endPoissonJet s hs R hR.le f) z.val.1=
      spectralWeightedPairL s (f.val 1) z.val.2.1-
        spectralWeightedPairL s (spectralEndWeight s R f) z.val.2.2 := by
  let J : CylinderTraceAmbient s R →L[ℂ] FiniteCylinderJets R := ContinuousLinearMap.fst ℂ _ _
  let T₀ : CylinderTraceAmbient s R →L[ℂ] spectralTraceGraph (torusRate s) :=
    (ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)
  let T₁ : CylinderTraceAmbient s R →L[ℂ] spectralTraceGraph (torusRate s) :=
    (ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)
  let L := (flatCylinderEnergyRightCLM s (endPoissonJet s hs R hR.le f)).comp J-
    (((spectralWeightedPairL s (f.val 1)).comp T₀)-
      ((spectralWeightedPairL s (spectralEndWeight s R f)).comp T₁))
  have hr : LinearMap.range (cylinderPolynomialGraphL s R)≤L.ker := by
    rintro _ ⟨p,rfl⟩
    change flatCylinderEnergy s (endPoissonJet s hs R hR.le f) (cylinderPolynomialJetL R p)-
      (spectralWeightedPairL s (f.val 1) (cylinderPolynomialTraceL s 0 p)-
        spectralWeightedPairL s (spectralEndWeight s R f) (cylinderPolynomialTraceL s R p))=0
    rw [cylinderPolynomialJetL_apply,flatCylinder_series_polynomial_green,
      spectralWeightedPair_polynomial,spectralWeightedPair_polynomial]
    simp only [spectralWeightedPair_initial,spectralWeightedPair_terminal s f hR.le,Finset.sum_sub_distrib]
    ring
  have hz := Submodule.topologicalClosure_minimal _ hr L.isClosed_ker z.property
  exact sub_eq_zero.mp hz

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_CylinderPoissonTrace
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma spectralTraceSingle_hasSum (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) :
    HasSum (fun h => spectralTraceSingleL s h (f.val 0 h)) f := by
  have hc (j : Fin 2) :
      HasSum (fun h => (spectralTraceSingleL s h (f.val 0 h)).val j) (f.val j) := by
    fin_cases j
    · exact lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) (f.val 0)
    · have H := lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) (f.val 1)
      convert H using 1
      · funext h
        change (lp.single 2 h ((Real.sqrt (torusRate s h):ℂ)*f.val 0 h) : SpectralL2 TorusModes)=lp.single 2 h (f.val 1 h)
        rw [f.property h]
      · rfl
  have ht : Tendsto (fun F : Finset TorusModes => fun j =>
        ∑ h∈F,(spectralTraceSingleL s h (f.val 0 h)).val j) atTop
      (𝓝 (fun j => f.val j)) := tendsto_pi_nhds.mpr hc
  have H := (PiLp.continuous_toLp 2 (fun _ : Fin 2 => SpectralL2 TorusModes)).continuousAt.tendsto.comp ht
  change Tendsto (fun F : Finset TorusModes => ∑ h∈F,spectralTraceSingleL s h (f.val 0 h)) atTop (𝓝 f)
  apply tendsto_subtype_rng.mpr
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext F
  apply PiLp.ext
  intro j
  simp only [Function.comp_apply,WithLp.ofLp_toLp,Submodule.coe_sum,WithLp.ofLp_sum,Finset.sum_apply]

lemma cylinderPolynomialJetL_single (R : ℝ) (h : TorusModes) (q : smoothComplexAxis) :
    cylinderPolynomialJetL R (Finsupp.single h q)=
      smoothCylinderModeJet (smoothComplexAxis_smooth q) R h := by
  rw [cylinderPolynomialJetL,Finsupp.lsum_single]
  exact cylinderJetMode_smooth _ R h

lemma cylinderPolynomialTraceL_single (s : Fin 3 → ℝ) (t : ℝ) (h : TorusModes)
    (q : smoothComplexAxis) :
    cylinderPolynomialTraceL s t (Finsupp.single h q)=spectralTraceSingleL s h (q t) := by
  rw [cylinderPolynomialTraceL,Finsupp.lsum_single]
  rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CylinderSlopeGreen
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma complex_linear_axis_deriv (r : ℝ) :
    deriv (fun t : ℝ => (r:ℂ)*(t:ℂ))=(fun _ => (r:ℂ)) := by
  funext t
  exact ((hasDerivAt_id t).ofReal_comp.const_mul (r:ℂ)).deriv.trans (by simp)

lemma cylinderSlopeJet_derivative (r R : ℝ) :
    cylinderSlopeJet r R 1=cylinderMode (FiniteAxisMeasure R) 0
      (smoothFiniteAxisLp (continuous_const : Continuous (fun _ : ℝ => (r:ℂ))) R) := by
  change cylinderMode _ _ (smoothFiniteAxisLp (q:=deriv (fun t : ℝ => (r:ℂ)*(t:ℂ))) _ _) = _
  congr 1
  apply Lp.ext
  filter_upwards [smoothFiniteAxisLp_ae ((complex_linear_axis_smooth r).continuous_deriv (by simp)) R,
    smoothFiniteAxisLp_ae (continuous_const : Continuous (fun _ : ℝ => (r:ℂ))) R] with t ht hu
  rw [ht,hu,complex_linear_axis_deriv]

lemma cylinderSlopeJet_angular (r R : ℝ) : cylinderSlopeJet r R 2=0 ∧ cylinderSlopeJet r R 3=0 := by
  simp [cylinderSlopeJet,smoothCylinderModeJet]

lemma constant_derivative_inner {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (r R : ℝ) (hR : 0≤R) :
    inner ℂ (smoothFiniteAxisLp (continuous_const : Continuous (fun _ : ℝ => (r:ℂ))) R)
      (smoothFiniteAxisLp (hq.continuous_deriv (by simp)) R)=(r:ℂ)*(q R-q 0) := by
  rw [L2.inner_def]
  have he : (∫ t,inner ℂ
        (smoothFiniteAxisLp (continuous_const : Continuous (fun _ : ℝ => (r:ℂ))) R t)
        (smoothFiniteAxisLp (hq.continuous_deriv (by simp)) R t)∂FiniteAxisMeasure R)=
      ∫ t in Ioc (0:ℝ) R,(r:ℂ)*deriv q t := by
    apply integral_congr_ae
    filter_upwards [smoothFiniteAxisLp_ae (continuous_const : Continuous (fun _ : ℝ => (r:ℂ))) R,
      smoothFiniteAxisLp_ae (hq.continuous_deriv (by simp)) R] with t ht hu
    rw [ht,hu]
    simp only [RCLike.inner_apply,Complex.conj_ofReal,mul_comm]
  rw [he,integral_const_mul,←intervalIntegral.integral_of_le hR]
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun t _ => hq.differentiable (by simp) t)
    ((hq.continuous_deriv (by simp)).intervalIntegrable 0 R)]

lemma spectralMean_single (s : Fin 3 → ℝ) (h : TorusModes) (a : ℂ) :
    spectralMeanCLM s (spectralTraceSingleL s h a)=if h=0 then a else 0 := by
  change (lp.single 2 h a : SpectralL2 TorusModes) 0=_
  by_cases hh : h=0
  · subst h; simp
  · simp [lp.single_apply,hh]

lemma flatCylinder_slope_mode_green (s : Fin 3 → ℝ)
    {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (r R : ℝ) (hR : 0≤R) (h : TorusModes) :
    flatCylinderEnergy s (cylinderSlopeJet r R) (smoothCylinderModeJet hq R h)=
      (r:ℂ)*(spectralMeanCLM s (spectralTraceSingleL s h (q R))-
        spectralMeanCLM s (spectralTraceSingleL s h (q 0))) := by
  rw [flatCylinderEnergy,cylinderSlopeJet_derivative,
    (cylinderSlopeJet_angular r R).1,(cylinderSlopeJet_angular r R).2]
  simp only [inner_zero_left,mul_zero,add_zero]
  change inner ℂ (cylinderMode _ 0 (smoothFiniteAxisLp continuous_const R))
    (cylinderMode _ h (smoothFiniteAxisLp (hq.continuous_deriv (by simp)) R))=_
  rw [cylinderMode_inner,spectralMean_single,spectralMean_single]
  by_cases hh : h=0
  · subst h
    rw [ite_eq_left rfl,ite_eq_left rfl]
    exact constant_derivative_inner hq r R hR
  · simp [hh,Ne.symm hh]

lemma spectralMean_polynomial (s : Fin 3 → ℝ) (t : ℝ) (p : TorusModes →₀ smoothComplexAxis) :
    spectralMeanCLM s (cylinderPolynomialTraceL s t p)=
      ∑ h∈p.support,spectralMeanCLM s (spectralTraceSingleL s h (p h t)) := by
  rw [cylinderPolynomialTraceL,Finsupp.lsum_apply,Finsupp.sum,map_sum]
  rfl

theorem flatCylinder_slope_completed_green (s : Fin 3 → ℝ) (r R : ℝ) (hR : 0≤R)
    (z : cylinderSobolevGraph s R) :
    flatCylinderEnergy s (cylinderSlopeJet r R) z.val.1=
      (r:ℂ)*(spectralMeanCLM s z.val.2.2-spectralMeanCLM s z.val.2.1) := by
  let J : CylinderTraceAmbient s R →L[ℂ] FiniteCylinderJets R := ContinuousLinearMap.fst ℂ _ _
  let T₀ : CylinderTraceAmbient s R →L[ℂ] spectralTraceGraph (torusRate s) :=
    (ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)
  let T₁ : CylinderTraceAmbient s R →L[ℂ] spectralTraceGraph (torusRate s) :=
    (ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)
  let L := (flatCylinderEnergyRightCLM s (cylinderSlopeJet r R)).comp J-
    (r:ℂ) • ((spectralMeanCLM s).comp T₁-(spectralMeanCLM s).comp T₀)
  have hr : LinearMap.range (cylinderPolynomialGraphL s R)≤L.ker := by
    rintro _ ⟨p,rfl⟩
    change flatCylinderEnergy s (cylinderSlopeJet r R) (cylinderPolynomialJetL R p)-
      (r:ℂ)*(spectralMeanCLM s (cylinderPolynomialTraceL s R p)-
        spectralMeanCLM s (cylinderPolynomialTraceL s 0 p))=0
    rw [cylinderPolynomialJetL_apply]
    change flatCylinderEnergyRightCLM s (cylinderSlopeJet r R) _-_ = 0
    rw [map_sum,spectralMean_polynomial,spectralMean_polynomial]
    change (∑ h∈p.support,flatCylinderEnergy s (cylinderSlopeJet r R)
      (smoothCylinderModeJet (smoothComplexAxis_smooth (p h)) R h))-_ = 0
    simp only [flatCylinder_slope_mode_green s _ r R hR,
      Finset.mul_sum,Finset.sum_sub_distrib,mul_sub]
    ring
  exact sub_eq_zero.mp (Submodule.topologicalClosure_minimal _ hr L.isClosed_ker z.property)

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma spectralWeightedPair_real (s : Fin 3 → ℝ) (f g : spectralTraceGraph (torusRate s)) :
    (spectralWeightedPairL s (f.val 1) g).re=
      inner ℝ (spectralGraphWeight (torusRate s) f) (spectralGraphWeight (torusRate s) g) := by
  change (inner ℂ (f.val 1) (g.val 1)).re=inner ℝ (f.val 1) (g.val 1)
  rw [lp.inner_eq_tsum (𝕜:=ℂ),Complex.re_tsum (lp.summable_inner (𝕜:=ℂ) (f.val 1) (g.val 1)),
    lp.inner_eq_tsum (𝕜:=ℝ)]
  rfl

lemma spectralMean_real (s : Fin 3 → ℝ) (g : spectralTraceGraph (torusRate s)) :
    (spectralMeanCLM s g).re=spectralGraphMean (torusRate s) g := rfl

theorem cylinderEndJet_real_green (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (r : ℝ) {R : ℝ} (hR : 0<R) (f : spectralTraceGraph (torusRate s))
    (z : cylinderSobolevGraph s R) :
    (flatCylinderEnergy s (cylinderEndJet s hs r R hR.le f) z.val.1).re=
      inner ℝ (spectralGraphWeight (torusRate s) f)
        (spectralGraphWeight (torusRate s) z.val.2.1)-
      r*spectralGraphMean (torusRate s) z.val.2.1+
      cylinderTerminalFlux s r R f z.val.2.2 := by
  have hadd : flatCylinderEnergy s (cylinderEndJet s hs r R hR.le f) z.val.1=
      flatCylinderEnergy s (endPoissonJet s hs R hR.le f) z.val.1+
        flatCylinderEnergy s (cylinderSlopeJet r R) z.val.1 :=
    map_add (flatCylinderEnergyLeftCLM s z.val.1) _ _
  rw [hadd,flatCylinder_completed_green s hs hR f z,
    flatCylinder_slope_completed_green s r R hR.le z]
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,spectralWeightedPair_real,spectralMean_real,cylinderTerminalFlux]
  ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_AttachedFlatTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma attachedFlatTensor_energy_density (s : Fin 3 → ℝ) {a : ℝ} (ha : a≠0) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) (v w : Fin 3 → ℝ) :
    |(sourceCollarJacobian i j x).det| *((attachedCartesianMatrix a i j x*ᵥv) ⬝ᵥ
      (attachedFlatTensor s a i j x*ᵥ(attachedCartesianMatrix a i j x*ᵥw)))=
        |a| *angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
          (v ⬝ᵥ (flatCylinderMatrix s*ᵥw)) := by
  rw [attachedFlatTensor_energy s ha i j hx,sourceFlatDensity,sourceFaceAngleMatrix_det]
  field_simp [abs_ne_zero.mpr (sourceCollarJacobian_extended_ne_zero i j hx)]

lemma attachedCartesianMatrix_poisson_derivative (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) (v : Fin 3 → ℝ) :
    fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) (sourceCollarPiece i j x) v=
      (attachedCartesianMatrix a i j x*ᵥ(fun k : Fin 3 =>
        (endPoissonField s f k.succ (a*(x 0-b),torusAngles (sourceFaceAngles i j x))).re)) ⬝ᵥ v := by
  rw [attachedEndPoisson_real_fderiv s hs f a b i j hx ht]
  have hfield (k : Fin 3) : attachedEndPoissonField s f a b k.succ (sourceCollarPiece i j x)=
      endPoissonField s f k.succ (a*(x 0-b),torusAngles (sourceFaceAngles i j x)) := by
    obtain ⟨htx,hi,hj⟩ := mem_sourceExtendedBox.mp (sourceCollarOpenBox_subset hx)
    rw [←sourceFaceAngles_physical i j hi hj,attachedEndPoissonField_angular s f a b k.succ htx]
  simp_rw [hfield]
  rw [attachedCartesianMatrix,Matrix.mulVec_mulVec]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_AffineCylinderIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
attribute [local instance] OAI.ScalarConductivity.affineCylinderIntegralMeasureSpace
local instance affineCylinderIntegralProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma integrable_affineEndCoordinates {a b l r R : ℝ} (ha : a≠0)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    {F : ℝ × UnitAddTorus (Fin 2) → ℝ}
    (hF : Integrable F ((FiniteAxisMeasure R).prod volume)) :
    Integrable (F ∘ affineEndCoordinates a b) ((volume.restrict (Ioc l r)).prod volume) := by
  have hle := affineEndCoordinates_interval_le ha hT
  have hν : sourceCylinderMeasure 0 R=(FiniteAxisMeasure R).prod volume := by
    rfl
  have hμ : sourceCylinderMeasure l r=(volume.restrict (Ioc l r)).prod volume := by
    rfl
  rw [hν,hμ] at hle
  have h := (hF.smul_measure (c:=ENNReal.ofReal |a⁻¹|) ENNReal.ofReal_ne_top).mono_measure hle
  exact (integrable_map_measure h.aestronglyMeasurable
    (measurable_affineEndCoordinates a b).aemeasurable).mp h

lemma integral_affineEndCoordinates_neg {a b l r R : ℝ} (ha : a<0) (hlr : l ≤ r)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    (hl : a*(l-b)=R) (hr : a*(r-b)=0) (hR : 0≤R)
    {F : ℝ × UnitAddTorus (Fin 2) → ℝ}
    (hF : Integrable F ((FiniteAxisMeasure R).prod volume)) :
    |a| *(∫ z,F (affineEndCoordinates a b z) ∂(volume.restrict (Ioc l r)).prod volume)=
      ∫ z,F z ∂(FiniteAxisMeasure R).prod volume := by
  have hg := integrable_affineEndCoordinates ha.ne hT hF
  rw [integral_prod (fun z => F (affineEndCoordinates a b z)) hg,integral_prod F hF,abs_of_neg ha,
    ←intervalIntegral.integral_of_le hlr,←intervalIntegral.integral_of_le hR]
  have he : (fun t => ∫ θ,F (affineEndCoordinates a b (t,θ)))=
      (fun t => (fun u => ∫ θ,F (u,θ)) (a*t-a*b)) := by
    funext t
    simp only [affineEndCoordinates,Prod.map_apply,affineEndTime,id_eq]
    rw [mul_sub]
  rw [he,neg_mul]
  change -(a • (∫ t in l..r,(fun u => ∫ θ,F (u,θ)) (a*t-a*b)))=_
  rw [intervalIntegral.smul_integral_comp_mul_sub (fun u => ∫ θ,F (u,θ)) a (a*b)]
  rw [←mul_sub,←mul_sub,hl,hr,intervalIntegral.integral_symm,neg_neg]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_CylinderFourierComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.cylinderFourierCompleteMeasureSpace
lemma cylinderCoefficient_fourier {μ : Measure ℝ} [SFinite μ]
    (q : lp (fun _ : TorusModes => Lp ℂ 2 μ) 2) (h : TorusModes) :
    cylinderCoefficientLp (cylinderFourier μ q) h = q h := by
  classical
  apply ext_inner_left ℂ
  intro f
  rw [←cylinderMode_inner_coefficient]
  have he : cylinderMode μ h f=cylinderFourier μ (lp.single 2 h f) :=
    ((cylinderMode_orthogonal μ).linearIsometry_apply_single f).symm
  rw [he,(cylinderFourier μ).inner_map_map,lp.inner_single_left]

lemma cylinderFourierEquiv_symm_apply {μ : Measure ℝ} [SFinite μ]
    (F : CylinderL2 μ) (h : TorusModes) :
    (cylinderFourierEquiv μ).symm F h = cylinderCoefficientLp F h := by
  have he := cylinderCoefficient_fourier ((cylinderFourierEquiv μ).symm F) h
  change cylinderCoefficientLp ((cylinderFourierEquiv μ) ((cylinderFourierEquiv μ).symm F)) h=_ at he
  simpa only [LinearIsometryEquiv.apply_symm_apply] using he.symm

theorem cylinderCoefficient_hasSum {μ : Measure ℝ} [SFinite μ] (F : CylinderL2 μ) :
    HasSum (fun h => cylinderMode μ h (cylinderCoefficientLp F h)) F := by
  have hh := cylinderFourier_hasSum μ ((cylinderFourierEquiv μ).symm F)
  simp only [cylinderFourierEquiv_symm_apply] at hh
  change HasSum _ ((cylinderFourierEquiv μ) ((cylinderFourierEquiv μ).symm F)) at hh
  simpa only [LinearIsometryEquiv.apply_symm_apply] using hh

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_CylinderFourierGraph
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma cylinderJetCoefficient_hasSum (R : ℝ) (J : FiniteCylinderJets R) :
    HasSum (fun h => cylinderJetMode R h (cylinderJetCoefficient R J h)) J := by
  have ht : Tendsto (fun F : Finset TorusModes => fun j =>
      ∑ h ∈ F,cylinderJetMode R h (cylinderJetCoefficient R J h) j)
      atTop (𝓝 (fun j => J j)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    exact cylinderCoefficient_hasSum (J j)
  have hmap := (PiLp.continuous_toLp 2 (fun _ : Fin 4 => CylinderL2 (FiniteAxisMeasure R))).continuousAt.tendsto.comp ht
  change Tendsto (fun F : Finset TorusModes => ∑ h ∈ F,cylinderJetMode R h (cylinderJetCoefficient R J h)) atTop _
  convert hmap using 1
  all_goals try with_reducible_and_instances rfl
  funext F
  apply PiLp.ext
  intro j
  simp only [Function.comp_apply,WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply]

theorem cylinderGraph_of_smooth_coefficients (s : Fin 3 → ℝ) (R : ℝ)
    (J : FiniteCylinderJets R) (q : TorusModes → smoothComplexAxis)
    (hq : ∀ h,cylinderJetCoefficient R J h=smoothAxisModeJet (smoothComplexAxis_smooth (q h)) R h)
    (f₀ f₁ : spectralTraceGraph (torusRate s))
    (hf₀ : ∀ h,f₀.val 0 h=q h 0) (hf₁ : ∀ h,f₁.val 0 h=q h R) :
    (J,(f₀,f₁))∈cylinderSobolevGraph s R := by
  classical
  have hsum := cylinderJetCoefficient_hasSum R J
  simp only [hq,cylinderJetMode_smooth] at hsum
  have hg := hsum.prodMk ((spectralTraceSingle_hasSum s f₀).prodMk (spectralTraceSingle_hasSum s f₁))
  apply mem_closure_of_tendsto hg
  apply Eventually.of_forall
  intro F
  apply Submodule.sum_mem
  intro h _
  refine ⟨Finsupp.single h (q h),?_⟩
  change (cylinderPolynomialJetL R (Finsupp.single h (q h)),
      (cylinderPolynomialTraceL s 0 (Finsupp.single h (q h)),
      cylinderPolynomialTraceL s R (Finsupp.single h (q h))))=_
  rw [cylinderPolynomialJetL_single,cylinderPolynomialTraceL_single,cylinderPolynomialTraceL_single,hf₀,hf₁]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusDirectionalFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
attribute [local instance] OAI.ScalarConductivity.torusDirectionalFourierMeasureSpace
local instance torusDirectionalFourierProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma torusCoordinateShift_add (j : Fin 2) (s t : ℝ) :
    torusCoordinateShift j (s+t)=torusCoordinateShift j s+torusCoordinateShift j t := by
  ext i
  by_cases hi : i=j <;> simp [torusCoordinateShift,hi]

theorem mFourierCoeff_of_directional_derivative
    (f : C(UnitAddTorus (Fin 2),ℂ)) (j : Fin 2) (K : ℝ) (hK : 0≤K)
    (hLip : ∀ t θ, ‖f (θ+torusCoordinateShift j t)-f θ‖≤K*|t|)
    {d : UnitAddTorus (Fin 2) → ℂ} (hd : AEStronglyMeasurable d volume)
    (hder : ∀ᵐ θ : UnitAddTorus (Fin 2),
      HasDerivAt (fun t => f (θ+torusCoordinateShift j t)) (d θ) 0)
    (h : TorusModes) :
    mFourierCoeff d h = (2*Real.pi*Complex.I*(h j)) * mFourierCoeff f h := by
  let F : ℝ → UnitAddTorus (Fin 2) → ℂ := fun t θ =>
    mFourier (-h) θ * f (θ+torusCoordinateShift j t)
  have hFc (t : ℝ) : Continuous (F t) :=
    (mFourier (-h)).continuous.mul (f.continuous.comp (continuous_id.add continuous_const))
  have hFL : ∀ᵐ θ : UnitAddTorus (Fin 2),
      LipschitzOnWith (Real.nnabs K) (fun t => F t θ) univ := by
    apply Eventually.of_forall
    intro θ
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro t s
    have he : θ+torusCoordinateShift j t=
        (θ+torusCoordinateShift j s)+torusCoordinateShift j (t-s) := by
      rw [add_assoc,←torusCoordinateShift_add,add_sub_cancel]
    calc
      dist (F t θ) (F s θ)=‖f (θ+torusCoordinateShift j t)-f (θ+torusCoordinateShift j s)‖ := by
        rw [dist_eq_norm]
        simp only [F,←mul_sub,norm_mul,mFourier_norm_one,one_mul]
      _≤K*|t-s| := by rw [he]; exact hLip (t-s) (θ+torusCoordinateShift j s)
      _=(Real.nnabs K:ℝ)*dist t s := by rw [Real.coe_nnabs,abs_of_nonneg hK,Real.dist_eq]
  have hI := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ:=(volume : Measure (UnitAddTorus (Fin 2))))
    (F:=F) (F':=fun θ => mFourier (-h) θ*d θ)
    (s:=univ) (bound:=fun _ => K) (x₀:=(0:ℝ)) (univ_mem)
    (Eventually.of_forall fun t => (hFc t).aestronglyMeasurable)
    ((hFc 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((mFourier (-h)).continuous.aestronglyMeasurable.mul hd) hFL
    (integrable_const _) (hder.mono fun θ hθ => hθ.const_mul _)
  have he : (fun t => ∫ θ,F t θ) =
      fun t : ℝ => Complex.exp (2*Real.pi*Complex.I*(h j)*t)*mFourierCoeff f h := by
    funext t
    change mFourierCoeff (fun θ => f (θ+torusCoordinateShift j t)) h=_
    rw [mFourierCoeff_translation,mFourier_coordinateShift]
  rw [he] at hI
  have hE := ((((hasDerivAt_id (0:ℝ)).ofReal_comp).const_mul
    (2*Real.pi*Complex.I*(h j))).cexp).mul_const (mFourierCoeff f h)
  have heD := hI.2.unique hE
  simpa only [mFourierCoeff,smul_eq_mul,id_eq,Complex.ofReal_zero,mul_zero,
    Complex.exp_zero,Complex.ofReal_one,mul_one,one_mul] using heD

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusDirectionalDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal

lemma torusRealProjection_add (x y : TorusRealPlane) :
    torusRealProjection (x+y)=torusRealProjection x+torusRealProjection y := by
  ext j
  simp [torusRealProjection]

lemma torusRealProjection_direction (j : Fin 2) (t : ℝ) :
    torusRealProjection (t • Pi.single j (1:ℝ))=torusCoordinateShift j t := by
  ext i
  by_cases hij : i=j <;> simp [torusRealProjection,torusCoordinateShift,hij]

attribute [local instance] OAI.ScalarConductivity.torusDirectionalDerivativeMeasureSpace
local instance torusDirectionalDerivativeProbabilityMeasure_r28d5ce_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
lemma torusRealRepresentative_ae {P : TorusRealPlane → Prop}
    (h : ∀ᵐ x ∂(volume : Measure TorusRealPlane),P x) :
    ∀ᵐ θ : UnitAddTorus (Fin 2), P (torusRealRepresentative θ) := by
  let K : Set TorusRealPlane := {x | ∀ i,x i∈Ioc (0:ℝ) (0+1)}
  have hK : MeasurableSet K := MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)
  have hp := (measurePreserving_subtype_coe hK).comp
    (measurePreserving_equivPiIoc (fun _ : Fin 2 => (0:ℝ)))
  exact hp.quasiMeasurePreserving.ae (ae_restrict_of_ae h)

lemma torusDirectionalDerivative_eq (f : UnitAddTorus (Fin 2) → ℂ) (j : Fin 2)
    (θ : UnitAddTorus (Fin 2)) :
    torusDirectionalDerivative f j θ=deriv (fun t => f (θ+torusCoordinateShift j t)) 0 := by
  unfold torusDirectionalDerivative lineDeriv
  congr 2
  ext t
  change f (torusRealProjection (torusRealRepresentative θ+t • Pi.single j 1))=_
  rw [torusRealProjection_add,torusRealProjection_representative,torusRealProjection_direction]

lemma measurable_torusDirectionalDerivative {f : UnitAddTorus (Fin 2) → ℂ}
    (hf : Continuous f) (j : Fin 2) : Measurable (torusDirectionalDerivative f j) :=
  (measurable_lineDeriv (hf.comp continuous_torusRealProjection)).comp measurable_torusRealRepresentative

lemma torusDirectionalDerivative_ae (f : C(UnitAddTorus (Fin 2),ℂ)) (K : ℝ≥0)
    (hLip : ∀ j t θ, ‖f (θ+torusCoordinateShift j t)-f θ‖≤(K:ℝ)*|t|) (j : Fin 2) :
    ∀ᵐ θ : UnitAddTorus (Fin 2),
      HasDerivAt (fun t => f (θ+torusCoordinateShift j t)) (torusDirectionalDerivative f j θ) 0 := by
  have hd : ∀ᵐ x ∂(volume : Measure TorusRealPlane),
      DifferentiableAt ℝ (fun y => f (torusRealProjection y)) x :=
    (torusRealLift_lipschitz f K hLip).ae_differentiableAt
  filter_upwards [torusRealRepresentative_ae hd] with θ hθ
  have he (t : ℝ) : f (torusRealProjection (torusRealRepresentative θ+t • Pi.single j 1))=
      f (θ+torusCoordinateShift j t) := by
    rw [torusRealProjection_add,torusRealProjection_representative,torusRealProjection_direction]
  simpa only [HasLineDerivAt,he,torusDirectionalDerivative] using (hθ.lineDifferentiableAt (v:=Pi.single j 1)).hasLineDerivAt

theorem torusDirectionalDerivative_fourier (f : C(UnitAddTorus (Fin 2),ℂ)) (K : ℝ≥0)
    (hLip : ∀ j t θ, ‖f (θ+torusCoordinateShift j t)-f θ‖≤(K:ℝ)*|t|)
    (j : Fin 2) (h : TorusModes) :
    mFourierCoeff (torusDirectionalDerivative f j) h=
      (2*Real.pi*Complex.I*(h j))*mFourierCoeff f h :=
  mFourierCoeff_of_directional_derivative f j K K.coe_nonneg (hLip j)
    (measurable_torusDirectionalDerivative f.continuous j).aestronglyMeasurable
    (torusDirectionalDerivative_ae f K hLip j) h

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SmoothCompactParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Metric

section CompactParameter
variable {E Q P G : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [TopologicalSpace P] [SecondCountableTopology P] [CompactSpace P]
  [MeasurableSpace P] [BorelSpace P]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {μ : Measure P} [IsFiniteMeasure μ]

omit [CompleteSpace G] in
lemma hasDerivAt_compact_parameter {F D : ℝ × P → G}
    (hF : Continuous F) (hD : Continuous D)
    (hd : ∀ x p, HasDerivAt (fun y => F (y,p)) (D (x,p)) x) (x : ℝ) :
    HasDerivAt (fun y => ∫ p, F (y,p) ∂μ) (∫ p, D (x,p) ∂μ) x := by
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod (isCompact_univ : IsCompact (univ : Set P))).exists_bound_of_continuousOn
    hD.continuousOn
  have hFs (y : ℝ) : Continuous (fun p => F (y,p)) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hDs (y : ℝ) : Continuous (fun p => D (y,p)) :=
    hD.comp (continuous_const.prodMk continuous_id)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=μ) (F:=fun y p => F (y,p)) (F':=fun y p => D (y,p))
    (s:=closedBall x 1) (bound:=fun _ => C)
    (closedBall_mem_nhds x (by norm_num))
    (Eventually.of_forall fun y => (hFs y).aestronglyMeasurable)
    ((hFs x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hDs x).aestronglyMeasurable ?_ (integrable_const _) ?_).2
  · exact Eventually.of_forall (fun p y hy => hC (y,p) ⟨hy,mem_univ p⟩)
  · exact Eventually.of_forall (fun p y _ => hd y p)

end CompactParameter
end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_AngularCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.angularCoefficientMeasureSpace
attribute [local instance] OAI.ScalarConductivity.angularCoefficientProbabilityMeasure
lemma sourceAngularCoefficient_hasDerivAt {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b : ℝ) (h : TorusModes) (t : ℝ) :
    HasDerivAt (sourceAngularCoefficient f a b h)
      (mFourierCoeff (sourceAngularAxial f a b t) h) t := by
  have hF : Continuous (fun z : ℝ × UnitAddTorus (Fin 2) =>
      mFourier (-h) z.2 * (f (sourceAngularCollar (a*z.1+b) z.2) : ℂ)) := by
    apply ((mFourier (-h)).continuous.comp continuous_snd).mul
    exact Complex.continuous_ofReal.comp (hf.continuous.comp
      (contDiff_sourceAngularPolynomial_joint.continuous.comp
        ((continuous_const.mul continuous_fst |>.add continuous_const).prodMk
          (continuous_sourceRayCoordinates.comp continuous_snd))))
  have hD := ((mFourier (-h)).continuous.comp continuous_snd).mul
    (continuous_sourceAngularAxial hf a b)
  apply hasDerivAt_compact_parameter hF hD
  intro u θ
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun v => f (sourceAngularCollar (a*v+b) θ)) :=
    hf.comp (contDiff_sourceAngularPolynomial_joint.comp
      ((contDiff_const.mul contDiff_id |>.add contDiff_const).prodMk contDiff_const))
  simpa only [sourceAngularAxial,Function.comp_def,Pi.mul_apply] using
    (((hg.differentiable (by simp)).differentiableAt (x:=u)).hasDerivAt.ofReal_comp).const_mul
      (mFourier (-h) θ)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_AngularJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal

attribute [local instance] OAI.ScalarConductivity.angularJetFiniteCylinderMeasureSpace
attribute [local instance] OAI.ScalarConductivity.angularJetFiniteCylinderProbabilityMeasure
lemma sourceAngularLpJet_ae {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b R : ℝ) (j : Fin 4) :
    sourceAngularLpJet hf a b R j =ᵐ[(FiniteAxisMeasure R).prod volume]
      sourceAngularJet f a b j :=
  (sourceAngularJet_memLp hf a b R j).coeFn_toLp

lemma mFourierCoeff_div_const (f : UnitAddTorus (Fin 2) → ℂ) (h : TorusModes) (c : ℂ) :
    mFourierCoeff (fun θ => f θ/c) h=mFourierCoeff f h/c := by
  simp only [mFourierCoeff,smul_eq_mul,←mul_div_assoc,integral_div]

lemma torusDirectionalDerivative_scaled_fourier (f : C(UnitAddTorus (Fin 2),ℂ)) (K : ℝ≥0)
    (hLip : ∀ j t θ, ‖f (θ+torusCoordinateShift j t)-f θ‖≤(K:ℝ)*|t|)
    (j : Fin 2) (h : TorusModes) :
    mFourierCoeff (fun θ => torusDirectionalDerivative f j θ/(2*Real.pi)) h=
      (Complex.I*(h j))*mFourierCoeff f h := by
  rw [mFourierCoeff_div_const,torusDirectionalDerivative_fourier f K hLip]
  have hp : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

lemma sourceAngularJet_fourier {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b R : ℝ) (h : TorusModes)
    {t : ℝ} (ht : t∈Icc (0:ℝ) R) (j : Fin 4) :
    mFourierCoeff (fun θ => sourceAngularJet f a b j (t,θ)) h=
      ![sourceAngularCoefficient f a b h t,deriv (sourceAngularCoefficient f a b h) t,
        (Complex.I*(h 0))*sourceAngularCoefficient f a b h t,
        (Complex.I*(h 1))*sourceAngularCoefficient f a b h t] j := by
  obtain ⟨K,hK⟩ := sourceAngularTest_lipschitz hf a b R
  have ha (k : Fin 2) := torusDirectionalDerivative_scaled_fourier
    ⟨fun θ => sourceAngularTest f a b (t,θ),
      (continuous_sourceAngularTest hf a b).comp (continuous_const.prodMk continuous_id)⟩
    K (hK t ht) k h
  fin_cases j
  · rfl
  · exact (sourceAngularCoefficient_hasDerivAt hf a b h t).deriv.symm
  · exact ha 0
  · exact ha 1

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalTensorPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma attachedFaceTensorList_local (s : Fin 3 → ℝ) (a : ℝ)
    (ks : List (Fin 4 × Fin 4)) (y : Fin 3 → ℝ)
    (hy : ∃ k∈ks,y∈sourceFlatPatch k.1 k.2) :
    ∃ k∈ks,y∈sourceFlatPatch k.1 k.2 ∧
      attachedFaceTensorList s a ks y=attachedPhysicalFlatTensor s a k.1 k.2 y := by
  classical
  induction ks with
  | nil => simp at hy
  | cons k ks ih =>
    by_cases hk : y∈sourceFlatPatch k.1 k.2
    · refine ⟨k,List.mem_cons_self,hk,?_⟩
      simp only [attachedFaceTensorList,List.foldr_cons,ite_eq_left hk,attachedPatchTensor]
    · obtain ⟨l,hl,hy⟩ := hy
      obtain ⟨l,hl,hly,he⟩ := ih ⟨l,(List.mem_cons.mp hl).resolve_left
        (fun e => hk (e ▸ hy)),hy⟩
      refine ⟨l,List.mem_cons_of_mem k hl,hly,?_⟩
      simpa only [attachedFaceTensorList,List.foldr_cons,ite_eq_right hk] using he

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalFaceUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma squareFace_interior_unique (i k : Fin 4) {a b : ℝ} (ha : |a|<1)
    (he : squareFace i a=squareFace k b) : i=k := by
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have ha₁ := (abs_lt.mp ha).1
  have ha₂ := (abs_lt.mp ha).2
  fin_cases i <;> fin_cases k <;>
    simp [squareFace,squareFaceBase,squareFaceDirection] at h0 h1 ⊢ <;> linarith

lemma sourceCollarPiece_open_unique (i j k l : Fin 4) {x z : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox)
    (hz : z∈sourceExtendedBox (-(1:ℝ)/100) (1/100))
    (he : sourceCollarPiece i j x=sourceCollarPiece k l z) : i=k ∧ j=l := by
  obtain ⟨hzt,hza,hzb⟩ := mem_sourceExtendedBox.mp hz
  have hx' := sourceCollarOpenBox_subset hx
  obtain ⟨hxt,hxa,hxb⟩ := mem_sourceExtendedBox.mp hx'
  have hxR : 0 < sourceCollarRadius j (x 0) (x 2) :=
    (by norm_num : (0:ℝ)<1/50).trans_le (sourceCollarRadius_extended j hxt hxb).1
  have hzR : 0 < sourceCollarRadius l (z 0) (z 2) :=
    (by norm_num : (0:ℝ)<1/50).trans_le (sourceCollarRadius_extended l hzt hzb).1
  have hR : sourceCollarRadius j (x 0) (x 2)=sourceCollarRadius l (z 0) (z 2) := by
    have hh := congrArg sourceRadial he
    rwa [sourceCollarPiece_radial_pos i j hxR.le hxa,
      sourceCollarPiece_radial_pos k l hzR.le hza] at hh
  have ht : x 0=z 0 := by
    have hh := congrArg sourceCollarTime he
    rwa [sourceCollarPiece_time_pos i j hxR.le (by linarith [hxt.2]) hxa hxb,
      sourceCollarPiece_time_pos k l hzR.le (by linarith [hzt.2]) hza hzb] at hh
  constructor
  · apply squareFace_interior_unique i k hx.2.1
    have hh := congrArg (fun y : Fin 3 → ℝ => ![y 0/sourceLength,y 1]) he
    rw [sourceCollarPiece_angular,sourceCollarPiece_angular,←hR] at hh
    exact smul_right_injective (Fin 2 → ℝ) hxR.ne' hh
  · apply squareFace_interior_unique j l hx.2.2
    have hh := congrArg sourceCrossCoordinates he
    rw [sourceCollarPiece_cross_pos i j hxR.le hxa,
      sourceCollarPiece_cross_pos k l hzR.le hza,←ht] at hh
    exact smul_right_injective (Fin 2 → ℝ) (by linarith [hxt.2] : 1-x 0≠0) hh

lemma attachedFaceTensorList_unique (s : Fin 3 → ℝ) (a : ℝ)
    (ks : List (Fin 4 × Fin 4)) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) (hk : (i,j)∈ks) :
    attachedFaceTensorList s a ks (sourceCollarPiece i j x)=
      attachedPhysicalFlatTensor s a i j (sourceCollarPiece i j x) := by
  obtain ⟨k,_,hy,he⟩ := attachedFaceTensorList_local s a ks _
    ⟨(i,j),hk,⟨x,sourceCollarOpenBox_subset hx,rfl⟩⟩
  obtain ⟨z,hz,hze⟩ := hy
  obtain ⟨hi,hj⟩ := sourceCollarPiece_open_unique i j k.1 k.2 hx hz hze.symm
  simpa only [←hi,←hj] using he

lemma attachedCollarTensor_open (s : Fin 3 → ℝ) (a : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : x∈sourceCollarOpenBox) :
    attachedCollarTensor s a (sourceCollarPiece i j x)=
      attachedFlatTensor s a i j x := by
  rw [attachedCollarTensor,attachedFaceTensorList_unique s a _ i j hx (by simp)]
  simp only [attachedPhysicalFlatTensor,sourceCollarInverse_point i j hx]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalTestEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma clm_eq_coordinate_dot (L : (Fin 3 → ℝ) →L[ℝ] ℝ) (v : Fin 3 → ℝ) :
    L v=(fun k => L (Pi.single k 1)) ⬝ᵥ v := by
  have hv : v=∑ k : Fin 3,v k • Pi.single k (1:ℝ) := by
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum,map_smul,smul_eq_mul,dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma attachedFlatTestCovector_transport (φ : (Fin 3 → ℝ) → ℝ) {a : ℝ} (ha : a≠0)
    (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    attachedCartesianMatrix a i j x*ᵥattachedFlatTestCovector φ a i j x=
      physicalTestCovector φ (sourceCollarPiece i j x) := by
  rw [attachedFlatTestCovector,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (attachedCartesianMatrix_det_ne_zero ha i j hx)),Matrix.one_mulVec]

lemma physicalTestCovector_chain (φ : (Fin 3 → ℝ) → ℝ)
    (i j : Fin 4) (x : Fin 3 → ℝ)
    (hφ : DifferentiableAt ℝ φ (sourceCollarPiece i j x)) :
    physicalTestCovector (φ ∘ sourceCollarPiece i j) x=
      (sourceCollarJacobian i j x)ᵀ *ᵥ physicalTestCovector φ (sourceCollarPiece i j x) := by
  ext k
  rw [physicalTestCovector,(hφ.hasFDerivAt.comp x (sourceCollarPiece_hasFDeriv i j x)).fderiv]
  change fderiv ℝ φ (sourceCollarPiece i j x)
    (sourceCollarDerivative i j x (Pi.single k 1))=_
  change fderiv ℝ φ (sourceCollarPiece i j x)
    (sourceCollarJacobian i j x*ᵥPi.single k 1)=_
  rw [Matrix.mulVec_single_one,clm_eq_coordinate_dot]
  simp only [physicalTestCovector,Matrix.mulVec,Matrix.transpose_apply,dotProduct]
  apply Finset.sum_congr rfl
  intro q _
  simp [Matrix.col,mul_comm]

theorem attachedFlatTestCovector_chain (φ : (Fin 3 → ℝ) → ℝ) {a : ℝ} (ha : a≠0)
    (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100))
    (hφ : DifferentiableAt ℝ φ (sourceCollarPiece i j x)) :
    physicalTestCovector (φ ∘ sourceCollarPiece i j) x=
      sourceFaceAngleMatrix i j x*ᵥ(endAxialMatrix a*ᵥattachedFlatTestCovector φ a i j x) := by
  rw [physicalTestCovector_chain φ i j x hφ,
    ←attachedFlatTestCovector_transport φ ha i j hx,attachedCartesianMatrix,
    ←Matrix.mulVec_mulVec,sourceCartesianGradient_chain i j hx]

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma sourceExtendedBox_open_ae {l r : ℝ} (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    ∀ᵐ x∂volume.restrict (sourceExtendedBox l r),x∈sourceCollarOpenBox := by
  let B := sourceExtendedBox (-(1:ℝ)/100) (1/100)
  have hB : volume (frontier B)=0 := (convex_Icc _ _).addHaar_frontier volume
  have hn : ∀ᵐ x : Fin 3 → ℝ,x∉frontier B := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hB
  filter_upwards [ae_restrict_mem (show MeasurableSet (sourceExtendedBox l r) from measurableSet_Icc),
    ae_restrict_of_ae hn] with x hx hn
  have hxB : x∈B := by
    obtain ⟨ht,hi,hj⟩ := mem_sourceExtendedBox.mp hx
    exact mem_sourceExtendedBox.mpr ⟨⟨hl.trans ht.1,ht.2.trans hr⟩,hi,hj⟩
  rw [sourceCollarOpenBox_eq_interior]
  by_contra h
  exact hn ⟨subset_closure hxB,h⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_AngularGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
attribute [local instance] OAI.ScalarConductivity.angularGraphMeasureSpace
local instance angularGraphIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma smoothAxisModeJet_ae {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (R : ℝ) (h : TorusModes) (j : Fin 4) :
    (smoothAxisModeJet hq R h) j =ᵐ[FiniteAxisMeasure R]
      fun t => ![q t,deriv q t,(Complex.I*(h 0))*q t,(Complex.I*(h 1))*q t] j := by
  have hq₀ := smoothFiniteAxisLp_ae hq.continuous R
  have hq₁ := smoothFiniteAxisLp_ae (hq.continuous_deriv (by simp)) R
  have hq₂ := Lp.coeFn_smul (Complex.I*(h 0:ℂ)) (smoothFiniteAxisLp hq.continuous R)
  have hq₃ := Lp.coeFn_smul (Complex.I*(h 1:ℂ)) (smoothFiniteAxisLp hq.continuous R)
  fin_cases j
  · exact hq₀
  · exact hq₁
  · exact hq₂.trans (hq₀.mono fun t ht => by simp [ht,smul_eq_mul])
  · exact hq₃.trans (hq₀.mono fun t ht => by simp [ht,smul_eq_mul])

lemma sourceAngularLpJet_coefficient {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b R : ℝ) (h : TorusModes) :
    cylinderJetCoefficient R (sourceAngularLpJet hf a b R) h=
      smoothAxisModeJet (sourceAngularCoefficient_smooth hf a b h) R h := by
  apply PiLp.ext
  intro j
  apply Lp.ext
  filter_upwards [cylinderCoefficientLp_ae (sourceAngularLpJet hf a b R j) h,
    Measure.ae_ae_of_ae_prod (sourceAngularLpJet_ae hf a b R j),
    smoothAxisModeJet_ae (sourceAngularCoefficient_smooth hf a b h) R h j,
    ae_restrict_mem measurableSet_Ioc] with t ht₁ ht₂ ht₃ htm
  change cylinderCoefficientLp (sourceAngularLpJet hf a b R j) h t=_
  rw [ht₁,ht₃]
  calc
    cylinderCoefficient (sourceAngularLpJet hf a b R j) h t=
        mFourierCoeff (fun θ => sourceAngularJet f a b j (t,θ)) h := by
      unfold cylinderCoefficient mFourierCoeff
      apply integral_congr_ae
      filter_upwards [ht₂] with θ hθ
      rw [hθ]
    _=_ := sourceAngularJet_fourier hf a b R h (Ioc_subset_Icc_self htm) j

theorem sourceAngularLpJet_graph (s : Fin 3 → ℝ) {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b R : ℝ) :
    (sourceAngularLpJet hf a b R,
      (smoothCollarTrace s b hf,smoothCollarTrace s (a*R+b) hf))∈cylinderSobolevGraph s R := by
  let q : TorusModes → smoothComplexAxis := fun h =>
    ⟨sourceAngularCoefficient f a b h,sourceAngularCoefficient_smooth hf a b h⟩
  apply cylinderGraph_of_smooth_coefficients s R _ q
    (sourceAngularLpJet_coefficient hf a b R) _ _
  · intro h
    rw [smoothCollarTrace_fst]
    simp [q,sourceAngularCoefficient]
  · intro h
    rw [smoothCollarTrace_fst]
    rfl

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal

lemma hasDerivAt_outer_of_strict_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} {g : ℝ → ℝ} {x d : ℝ} {v : E}
    (hg : HasStrictDerivAt g d x) (hd : d≠0)
    (hF : HasDerivAt (F ∘ g) v x) : HasDerivAt F (d⁻¹ • v) (g x) := by
  let q := hg.localInverse g d x hd
  have hq : q (g x)=x := hg.eventually_left_inverse hd |>.self_of_nhds
  have h := hF.scomp_of_eq (g x) (hg.to_localInverse hd).hasDerivAt hq.symm
  apply h.congr_of_eventuallyEq
  filter_upwards [hg.eventually_right_inverse hd] with y hy
  exact congrArg F hy.symm

lemma hasStrictDerivAt_faceRayAngle (w : ℝ) (j : Fin 4) (b : ℝ) :
    HasStrictDerivAt (faceRayAngle w j) (faceRayDensity w j b) b :=
  hasStrictDerivAt_of_hasDerivAt_of_continuousAt
    (Filter.Eventually.of_forall fun x => hasDerivAt_faceRayAngle w j x)
    (continuous_faceRayDensity w j).continuousAt

lemma faceRayDensity_pos' {w : ℝ} (hw : 0<w) (j : Fin 4) (b : ℝ) :
    0<faceRayDensity w j b := by
  fin_cases j <;> dsimp [faceRayDensity] <;> positivity

lemma torusDirectionalDerivative_of_face (F : UnitAddTorus (Fin 2) → ℂ)
    (θ : UnitAddTorus (Fin 2)) (k : Fin 2) {w : ℝ} (hw : 0<w)
    (i : Fin 4) (b : ℝ) (v : ℂ)
    (hF : HasDerivAt (fun u => F (θ+torusCoordinateShift k
      (faceRayAngle w i u-faceRayAngle w i b))) v b) :
    torusDirectionalDerivative F k θ=(faceRayDensity w i b)⁻¹ • v := by
  have h := hasDerivAt_outer_of_strict_comp (F:=fun t => F (θ+torusCoordinateShift k t))
    ((hasStrictDerivAt_faceRayAngle w i b).sub_const (faceRayAngle w i b))
    (faceRayDensity_pos' hw i b).ne' hF
  simpa only [sub_self,torusDirectionalDerivative_eq] using h.deriv

lemma hasDerivAt_coordinate_update (x : Fin 3 → ℝ) (k : Fin 3) :
    HasDerivAt (fun u => Function.update x k u) (Pi.single k 1) (x k) := by
  apply hasDerivAt_pi.mpr
  intro l
  by_cases hl : l=k
  · subst l
    simp only [Function.update_self,Pi.single_eq_same]
    exact hasDerivAt_id' (x k)
  · simpa [Function.update_of_ne hl,Pi.single_apply,hl] using hasDerivAt_const (x k) (x l)

lemma physicalTestCovector_update {f : (Fin 3 → ℝ) → ℝ} {point : Fin 3 → ℝ}
    (hf : DifferentiableAt ℝ f point) (k : Fin 3) :
    HasDerivAt (fun u => f (Function.update point k u)) (physicalTestCovector f point k) (point k) := by
  simpa only [Function.update_eq_self,Function.comp_def,physicalTestCovector] using
    hf.hasFDerivAt.comp_hasDerivAt_of_eq (point k) (hasDerivAt_coordinate_update point k)
      (Function.update_eq_self k point).symm

lemma sourceAngularTest_face0 {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b t : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : a*t+b=x 0) (h1 : |x 1|<1) (h2 : |x 2|≤1) :
    torusDirectionalDerivative (fun θ => sourceAngularTest f a b (t,θ)) 0
      (torusAngles (sourceFaceAngles i j x))=
      (faceRayDensity 1 i (x 1))⁻¹ •
        (physicalTestCovector (f ∘ sourceCollarPiece i j) x 1 : ℂ) := by
  apply torusDirectionalDerivative_of_face _ _ _ (by norm_num) i (x 1)
  have hd := (physicalTestCovector_update
    ((hf.differentiable (by simp)).differentiableAt.comp x
      (sourceCollarPiece_hasFDeriv i j x).differentiableAt) 1).ofReal_comp
  apply hd.congr_of_eventuallyEq
  have hn : ∀ᶠ u in 𝓝 (x 1), |u|<1 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds h1
  filter_upwards [hn] with u hu
  dsimp only [Function.comp_def,sourceAngularTest]
  congr 1
  rw [sourceFaceAngles_torus,hx]
  have he : ![((faceRayAngle 1 i (x 1):ℝ):UnitAddCircle),
      ((faceRayAngle sourceRadialWidth j (x 2):ℝ):UnitAddCircle)]+
      torusCoordinateShift 0 (faceRayAngle 1 i u-faceRayAngle 1 i (x 1))=
      ![((faceRayAngle 1 i u:ℝ):UnitAddCircle),
        ((faceRayAngle sourceRadialWidth j (x 2):ℝ):UnitAddCircle)] := by
    ext k
    fin_cases k <;> simp [torusCoordinateShift]
  rw [he,sourceAngular_face _ _ _ _ _ hu.le h2]
  congr 2
  ext k
  fin_cases k <;> simp

lemma sourceAngularTest_face1 {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b t : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : a*t+b=x 0) (h1 : |x 1|≤1) (h2 : |x 2|<1) :
    torusDirectionalDerivative (fun θ => sourceAngularTest f a b (t,θ)) 1
      (torusAngles (sourceFaceAngles i j x))=
      (faceRayDensity sourceRadialWidth j (x 2))⁻¹ •
        (physicalTestCovector (f ∘ sourceCollarPiece i j) x 2 : ℂ) := by
  apply torusDirectionalDerivative_of_face _ _ _ (by norm_num [sourceRadialWidth,sourceHole]) j (x 2)
  have hd := (physicalTestCovector_update
    ((hf.differentiable (by simp)).differentiableAt.comp x
      (sourceCollarPiece_hasFDeriv i j x).differentiableAt) 2).ofReal_comp
  apply hd.congr_of_eventuallyEq
  have hn : ∀ᶠ u in 𝓝 (x 2), |u|<1 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds h2
  filter_upwards [hn] with u hu
  dsimp only [Function.comp_def,sourceAngularTest]
  congr 1
  rw [sourceFaceAngles_torus,hx]
  have he : ![((faceRayAngle 1 i (x 1):ℝ):UnitAddCircle),
      ((faceRayAngle sourceRadialWidth j (x 2):ℝ):UnitAddCircle)]+
      torusCoordinateShift 1 (faceRayAngle sourceRadialWidth j u-faceRayAngle sourceRadialWidth j (x 2))=
      ![((faceRayAngle 1 i (x 1):ℝ):UnitAddCircle),
        ((faceRayAngle sourceRadialWidth j u:ℝ):UnitAddCircle)] := by
    ext k
    fin_cases k <;> simp [torusCoordinateShift]
  rw [he,sourceAngular_face _ _ _ _ _ h1 hu.le]
  congr 2
  ext k
  fin_cases k <;> simp

lemma sourceAngularAxial_face {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b t : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : a*t+b=x 0) (h1 : |x 1|≤1) (h2 : |x 2|≤1) :
    sourceAngularAxial f a b t (torusAngles (sourceFaceAngles i j x))=
      (a*physicalTestCovector (f ∘ sourceCollarPiece i j) x 0 : ℝ) := by
  have hd := (physicalTestCovector_update
    ((hf.differentiable (by simp)).differentiableAt.comp x
      (sourceCollarPiece_hasFDeriv i j x).differentiableAt) 0).comp_of_eq t
      (((hasDerivAt_id t).const_mul a).add_const b) hx.symm
  have he : (fun u => f (sourceAngularCollar (a*u+b) (torusAngles (sourceFaceAngles i j x))))=
      (fun u => (f ∘ sourceCollarPiece i j) (Function.update x 0 (a*u+b))) := by
    funext u
    dsimp only [Function.comp_def]
    rw [sourceFaceAngles_torus,sourceAngular_face _ _ _ _ _ h1 h2]
    congr 2
    ext k
    fin_cases k <;> simp
  unfold sourceAngularAxial
  rw [he]
  change ((deriv ((fun u => (f ∘ sourceCollarPiece i j) (Function.update x 0 u)) ∘
    (fun u => a*u+b)) t : ℝ) : ℂ)=_
  have hd' := hd.deriv
  simpa only [id_eq,mul_one,mul_comm] using congrArg Complex.ofReal hd'

theorem sourceAngularJet_face {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b t : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : a*t+b=x 0) (h1 : |x 1|<1) (h2 : |x 2|<1) :
    (fun k : Fin 3 => (sourceAngularJet f a b k.succ
      (t,torusAngles (sourceFaceAngles i j x))).re)=
      ![a*physicalTestCovector (f ∘ sourceCollarPiece i j) x 0,
        physicalTestCovector (f ∘ sourceCollarPiece i j) x 1/(2*Real.pi*faceRayDensity 1 i (x 1)),
        physicalTestCovector (f ∘ sourceCollarPiece i j) x 2/(2*Real.pi*faceRayDensity sourceRadialWidth j (x 2))] := by
  ext k
  fin_cases k
  · change (sourceAngularAxial f a b t (torusAngles (sourceFaceAngles i j x))).re=_
    exact congrArg Complex.re (sourceAngularAxial_face hf a b t i j hx h1.le h2.le)
  · change (torusDirectionalDerivative (fun θ => sourceAngularTest f a b (t,θ)) 0
      (torusAngles (sourceFaceAngles i j x))/(2*Real.pi)).re=
        physicalTestCovector (f ∘ sourceCollarPiece i j) x 1/(2*Real.pi*faceRayDensity 1 i (x 1))
    rw [sourceAngularTest_face0 hf a b t i j hx h1 h2.le]
    rw [Complex.real_smul]
    norm_cast
    ring
  · change (torusDirectionalDerivative (fun θ => sourceAngularTest f a b (t,θ)) 1
      (torusAngles (sourceFaceAngles i j x))/(2*Real.pi)).re=
        physicalTestCovector (f ∘ sourceCollarPiece i j) x 2/(2*Real.pi*faceRayDensity sourceRadialWidth j (x 2))
    rw [sourceAngularTest_face1 hf a b t i j hx h1.le h2]
    rw [Complex.real_smul]
    norm_cast
    ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_AngularPhysicalTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal

theorem sourceAngularJet_attachedCovector {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) {a : ℝ} (ha : a≠0) (b : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : x∈sourceCollarOpenBox) :
    (fun k : Fin 3 => (sourceAngularJet f a⁻¹ b k.succ
      (a*(x 0-b),torusAngles (sourceFaceAngles i j x))).re)=
      attachedFlatTestCovector f a i j x := by
  have h1 : |x 1|<1 := by exact hx.2.1
  have h2 : |x 2|<1 := by exact hx.2.2
  have ht : a⁻¹*(a*(x 0-b))+b=x 0 := by field_simp; ring
  rw [sourceAngularJet_face hf a⁻¹ b (a*(x 0-b)) i j ht h1 h2]
  have h := attachedFlatTestCovector_chain f ha i j (sourceCollarOpenBox_subset hx)
    ((hf.differentiable (by simp)).differentiableAt)
  have h0 := congrFun h 0
  have h1' := congrFun h 1
  have h2' := congrFun h 2
  simp only [sourceFaceAngleMatrix,endAxialMatrix,mulVec_diagonal] at h0 h1' h2'
  change physicalTestCovector (f ∘ sourceCollarPiece i j) x 0=
    1*(a*attachedFlatTestCovector f a i j x 0) at h0
  change physicalTestCovector (f ∘ sourceCollarPiece i j) x 1=
    (2*Real.pi*faceRayDensity 1 i (x 1))*(1*attachedFlatTestCovector f a i j x 1) at h1'
  change physicalTestCovector (f ∘ sourceCollarPiece i j) x 2=
    (2*Real.pi*faceRayDensity sourceRadialWidth j (x 2))*(1*attachedFlatTestCovector f a i j x 2) at h2'
  ext k
  fin_cases k
  · change a⁻¹*physicalTestCovector (f ∘ sourceCollarPiece i j) x 0=_
    rw [h0]; field_simp [ha]; rfl
  · change physicalTestCovector (f ∘ sourceCollarPiece i j) x 1/(2*Real.pi*faceRayDensity 1 i (x 1))=_
    rw [h1']
    field_simp [(faceRayDensity_pos' (w:=1) (by norm_num) i (x 1)).ne',Real.pi_ne_zero]; rfl
  · change physicalTestCovector (f ∘ sourceCollarPiece i j) x 2/(2*Real.pi*faceRayDensity sourceRadialWidth j (x 2))=_
    rw [h2']
    field_simp [(faceRayDensity_pos' (w:=sourceRadialWidth) (by norm_num [sourceRadialWidth,sourceHole]) j (x 2)).ne',Real.pi_ne_zero]; rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_ParentFullEndH1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

lemma sourceCollarTime_local_inverse (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) :
    sourceCollarTime=ᶠ[𝓝 (sourceCollarPiece i j x)]
      (fun y => sourceCollarInverse i j y 0) := by
  change ∀ᶠ y in 𝓝 (sourceCollarPiece i j x),sourceCollarTime y=sourceCollarInverse i j y 0
  rw [←sourceCollarPiece_map_nhds i j hx,Filter.eventually_map]
  filter_upwards [isOpen_sourceCollarOpenBox.mem_nhds hx,
    sourceCollarInverse_eventually_left i j hx] with y hy hi
  rw [hi,sourceCollarPiece_time_open hy]

lemma sourceCollarTime_differentiable_open (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) :
    DifferentiableAt ℝ sourceCollarTime (sourceCollarPiece i j x) := by
  have hd := (sourceCollarInverse_hasStrictFDeriv i j hx).hasFDerivAt.differentiableAt
  exact ((differentiableAt_pi.mp hd) 0).congr_of_eventuallyEq
    (sourceCollarTime_local_inverse i j hx)

lemma attachedCartesianMatrix_axial_derivative (a b : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : x∈sourceCollarOpenBox) :
    physicalTestCovector (fun y => a*(sourceCollarTime y-b)) (sourceCollarPiece i j x)=
      attachedCartesianMatrix a i j x*ᵥPi.single 0 1 := by
  let F : (Fin 3 → ℝ) → ℝ := fun y => a*(sourceCollarTime y-b)
  have hd : DifferentiableAt ℝ F (sourceCollarPiece i j x) :=
    ((sourceCollarTime_differentiable_open i j hx).sub_const b).const_mul a
  have he : (F ∘ sourceCollarPiece i j)=ᶠ[𝓝 x] (fun y => a*(y 0-b)) := by
    filter_upwards [isOpen_sourceCollarOpenBox.mem_nhds hx] with y hy
    simp only [Function.comp_apply,F,sourceCollarPiece_time_open hy]
  have hf : physicalTestCovector (F ∘ sourceCollarPiece i j) x=Pi.single 0 a := by
    ext k
    rw [physicalTestCovector,he.fderiv_eq,
      (((hasFDerivAt_apply (𝕜:=ℝ) (0:Fin 3) x).sub_const b).const_mul a).fderiv]
    fin_cases k <;> simp
  have hc := physicalTestCovector_chain F i j x hd
  have ht : (sourceCollarJacobian i j x)ᵀ *ᵥ
      (attachedCartesianMatrix a i j x*ᵥPi.single 0 1)=Pi.single 0 a := by
    rw [attachedCartesianMatrix,←Matrix.mulVec_mulVec,
      sourceCartesianGradient_chain i j (sourceCollarOpenBox_subset hx)]
    ext k
    fin_cases k <;> simp [sourceFaceAngleMatrix,endAxialMatrix,Matrix.mulVec_diagonal]
  have hn : IsUnit (sourceCollarJacobian i j x)ᵀ.det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr (sourceCollarJacobian_extended_ne_zero i j (sourceCollarOpenBox_subset hx))
  have hh := congrArg (fun v => (sourceCollarJacobian i j x)ᵀ⁻¹*ᵥv)
    (hc.symm.trans (hf.trans ht.symm))
  simpa only [Matrix.mulVec_mulVec,←Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hn,
    Matrix.one_mulVec,Matrix.one_mul] using hh

lemma fullAttachedEndGradient_transport (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (a b κ : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) :
    fullAttachedEndGradient s f a b κ (sourceCollarPiece i j x)=
      attachedCartesianMatrix a i j x*ᵥ
        fullEndFlatCovector s f κ (a*(x 0-b)) (torusAngles (sourceFaceAngles i j x)) := by
  have hp : physicalTestCovector (fun y => (attachedEndPoissonField s f a b 0 y).re)
      (sourceCollarPiece i j x)=attachedCartesianMatrix a i j x*ᵥ
        (fun k : Fin 3 => (endPoissonField s f k.succ
          (a*(x 0-b),torusAngles (sourceFaceAngles i j x))).re) := by
    ext k
    simp only [physicalTestCovector,attachedCartesianMatrix_poisson_derivative s hs f a b i j hx ht,
      dotProduct_single,mul_one]
  change physicalTestCovector (fun y => (attachedEndPoissonField s f a b 0 y).re)
      (sourceCollarPiece i j x)+κ •
        physicalTestCovector (fun y => a*(sourceCollarTime y-b)) (sourceCollarPiece i j x)=_
  rw [hp,attachedCartesianMatrix_axial_derivative a b i j hx,fullEndFlatCovector,
    Matrix.mulVec_add,Matrix.mulVec_smul]

theorem fullAttachedEnd_test_energy (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ) (φ : (Fin 3 → ℝ) → ℝ)
    {a b : ℝ} (ha : a≠0) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) :
    |(sourceCollarJacobian i j x).det| *
      (fullAttachedEndGradient s f a b κ (sourceCollarPiece i j x) ⬝ᵥ
        (attachedCollarTensor s a (sourceCollarPiece i j x)*ᵥ
          physicalTestCovector φ (sourceCollarPiece i j x)))=
      |a| *angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
        (fullEndFlatCovector s f κ (a*(x 0-b)) (torusAngles (sourceFaceAngles i j x)) ⬝ᵥ
          (flatCylinderMatrix s*ᵥattachedFlatTestCovector φ a i j x)) := by
  rw [fullAttachedEndGradient_transport s hs f a b κ i j hx ht,
    attachedCollarTensor_open s a i j hx,
    ←attachedFlatTestCovector_transport φ ha i j (sourceCollarOpenBox_subset hx)]
  exact attachedFlatTensor_energy_density s ha i j (sourceCollarOpenBox_subset hx) _ _

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CylinderPointEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal

lemma deriv_ofReal_im_zero (f : ℝ → ℝ) (t : ℝ) :
    (deriv (fun x => (f x : ℂ)) t).im=0 := by
  by_cases h : DifferentiableAt ℝ (fun x => (f x:ℂ)) t
  · have hh := (Complex.imCLM.hasFDerivAt).comp_hasDerivAt t h.hasDerivAt
    have he := hh.deriv
    have heq : Complex.imCLM ∘ (fun x => (f x:ℂ)) = fun _ => (0:ℝ) := by
      funext x; rfl
    rw [heq,deriv_const] at he
    exact he.symm
  · rw [deriv_zero_of_not_differentiableAt h,Complex.zero_im]

lemma sourceAngularJet_im (f : (Fin 3 → ℝ) → ℝ) (a b : ℝ)
    (j : Fin 4) (z : ℝ × UnitAddTorus (Fin 2)) :
    (sourceAngularJet f a b j z).im=0 := by
  have hd (k : Fin 2) : (torusDirectionalDerivative
      (fun θ => sourceAngularTest f a b (z.1,θ)) k z.2).im=0 :=
    deriv_ofReal_im_zero _ _
  fin_cases j
  · rfl
  · rfl
  · change (torusDirectionalDerivative _ 0 z.2 / (2*Real.pi:ℂ)).im=0
    simp [Complex.div_im,hd]
  · change (torusDirectionalDerivative _ 1 z.2 / (2*Real.pi:ℂ)).im=0
    simp [Complex.div_im,hd]

lemma flatCylinderMatrix_mixed (s u v : Fin 3 → ℝ) :
    u ⬝ᵥ (flatCylinderMatrix s*ᵥv)=
      u 0*v 0+s 0*(u 1*v 1)+s 1*(u 1*v 2+u 2*v 1)+s 2*(u 2*v 2) := by
  simp [flatCylinderMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

attribute [local instance] OAI.ScalarConductivity.cylinderPointEnergyMeasureSpace
local instance cylinderPointEnergyIsProbabilityMeasure_r28d5ce_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
lemma cylinderSlopeJet_covector_ae (r R : ℝ) (k : Fin 3) :
    cylinderSlopeJet r R k.succ=ᵐ[(FiniteAxisMeasure R).prod volume]
      fun _ => ((r • Pi.single 0 (1:ℝ)) k : ℂ) := by
  fin_cases k
  · change (cylinderSlopeJet r R 1)=ᵐ[(FiniteAxisMeasure R).prod volume]
      (fun _ => (((r • Pi.single 0 (1:ℝ)) (0:Fin 3)):ℂ))
    simp only [Pi.smul_apply,Pi.single_apply,ite_true,smul_eq_mul,mul_one]
    rw [cylinderSlopeJet_derivative]
    have h1 := cylinderTensor_ae
      (smoothFiniteAxisLp (continuous_const : Continuous (fun _ : ℝ => (r:ℂ))) R) (mFourierLp 2 0)
    have h2 := (Measure.quasiMeasurePreserving_fst (μ:=FiniteAxisMeasure R)
      (ν:=(volume : Measure (UnitAddTorus (Fin 2))))).ae
      (smoothFiniteAxisLp_ae (continuous_const : Continuous (fun _ : ℝ => (r:ℂ))) R)
    have h3 := (Measure.quasiMeasurePreserving_snd (μ:=FiniteAxisMeasure R)
      (ν:=(volume : Measure (UnitAddTorus (Fin 2))))).ae (coeFn_mFourierLp 2 0)
    filter_upwards [h1,h2,h3] with z hz ht hθ
    change cylinderTensor _ _ z=_
    rw [hz,ht,hθ]
    simp [mFourier]
  · change (cylinderSlopeJet r R 2)=ᵐ[(FiniteAxisMeasure R).prod volume]
      (fun _ => (((r • Pi.single 0 (1:ℝ)) (1:Fin 3)):ℂ))
    simp only [Pi.smul_apply,Pi.single_apply,show (1:Fin 3)≠0 by decide,
      ite_false,smul_eq_mul,mul_zero,Complex.ofReal_zero]
    rw [(cylinderSlopeJet_angular r R).1]
    filter_upwards [Lp.coeFn_zero (ℂ) 2 ((FiniteAxisMeasure R).prod volume)] with z hz
    exact hz
  · change (cylinderSlopeJet r R 3)=ᵐ[(FiniteAxisMeasure R).prod volume]
      (fun _ => (((r • Pi.single 0 (1:ℝ)) (2:Fin 3)):ℂ))
    simp only [Pi.smul_apply,Pi.single_apply,show (2:Fin 3)≠0 by decide,
      ite_false,smul_eq_mul,mul_zero,Complex.ofReal_zero]
    rw [(cylinderSlopeJet_angular r R).2]
    filter_upwards [Lp.coeFn_zero (ℂ) 2 ((FiniteAxisMeasure R).prod volume)] with z hz
    exact hz

lemma cylinderEndJet_covector_ae (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (r R : ℝ) (hR : 0≤R) (f : spectralTraceGraph (torusRate s)) :
    ∀ᵐ z∂(FiniteAxisMeasure R).prod volume,
      (fun k : Fin 3 => (cylinderEndJet s hs r R hR f k.succ z).re)=
        fullEndFlatCovector s f r z.1 z.2 := by
  have h (k : Fin 3) : ∀ᵐ z∂(FiniteAxisMeasure R).prod volume,
      (cylinderEndJet s hs r R hR f k.succ z).re=fullEndFlatCovector s f r z.1 z.2 k := by
    filter_upwards [Lp.coeFn_add (endPoissonJet s hs R hR f k.succ)
      (cylinderSlopeJet r R k.succ),endPoissonJet_ae s hs R hR f k.succ,
      cylinderSlopeJet_covector_ae r R k] with z hz hp hr
    change ((endPoissonJet s hs R hR f k.succ+cylinderSlopeJet r R k.succ) z).re=_
    rw [hz]
    simp only [Pi.add_apply,hp,hr,Complex.add_re,Complex.ofReal_re,fullEndFlatCovector]
  filter_upwards [ae_all_iff.mpr h] with z hz
  exact funext hz

lemma flatCylinderEnergy_real_integral (s : Fin 3 → ℝ) {R : ℝ}
    (u v : FiniteCylinderJets R)
    (hv : ∀ k : Fin 3,∀ᵐ z∂(FiniteAxisMeasure R).prod volume,(v k.succ z).im=0) :
    Integrable (fun z => (fun k : Fin 3 => (u k.succ z).re) ⬝ᵥ
      (flatCylinderMatrix s*ᵥ(fun k : Fin 3 => (v k.succ z).re)))
        ((FiniteAxisMeasure R).prod volume) ∧
    (flatCylinderEnergy s u v).re=
      ∫ z,(fun k : Fin 3 => (u k.succ z).re) ⬝ᵥ
        (flatCylinderMatrix s*ᵥ(fun k : Fin 3 => (v k.succ z).re))
          ∂(FiniteAxisMeasure R).prod volume := by
  let P (i j : Fin 4) := fun z => inner ℂ (u i z) (v j z)
  have hP (i j : Fin 4) : Integrable (P i j) ((FiniteAxisMeasure R).prod volume) :=
    L2.integrable_inner (𝕜:=ℂ) _ _
  let F := fun z => P 1 1 z+(s 0:ℂ)*P 2 2 z+
    (s 1:ℂ)*(P 2 3 z+P 3 2 z)+(s 2:ℂ)*P 3 3 z
  have hF : Integrable F ((FiniteAxisMeasure R).prod volume) :=
    (((hP 1 1).add ((hP 2 2).const_mul (s 0:ℂ))).add
      (((hP 2 3).add (hP 3 2)).const_mul (s 1:ℂ))).add ((hP 3 3).const_mul (s 2:ℂ))
  have he : (fun z => (F z).re)=ᵐ[(FiniteAxisMeasure R).prod volume]
      (fun z => (fun k : Fin 3 => (u k.succ z).re) ⬝ᵥ
        (flatCylinderMatrix s*ᵥ(fun k : Fin 3 => (v k.succ z).re))) := by
    filter_upwards [hv 0,hv 1,hv 2] with z h1 h2 h3
    change (v 1 z).im=0 at h1
    change (v 2 z).im=0 at h2
    change (v 3 z).im=0 at h3
    rw [flatCylinderMatrix_mixed]
    simp [F,P,RCLike.inner_apply,Complex.mul_re,h1,h2,h3]
    ring
  refine ⟨hF.re.congr he,?_⟩
  rw [←integral_congr_ae he]
  change _ = ∫ z,RCLike.re (F z) ∂(FiniteAxisMeasure R).prod volume
  rw [integral_re hF]
  congr 1
  change flatCylinderEnergy s u v = ∫ z,F z ∂(FiniteAxisMeasure R).prod volume
  unfold F
  rw [integral_add (f:=fun z => P 1 1 z+(s 0:ℂ)*P 2 2 z+
      (s 1:ℂ)*(P 2 3 z+P 3 2 z)) (g:=fun z => (s 2:ℂ)*P 3 3 z)
      (((hP 1 1).add ((hP 2 2).const_mul (s 0:ℂ))).add
        (((hP 2 3).add (hP 3 2)).const_mul (s 1:ℂ))) ((hP 3 3).const_mul (s 2:ℂ)),
    integral_add (f:=fun z => P 1 1 z+(s 0:ℂ)*P 2 2 z)
      (g:=fun z => (s 1:ℂ)*(P 2 3 z+P 3 2 z))
      ((hP 1 1).add ((hP 2 2).const_mul (s 0:ℂ)))
      (((hP 2 3).add (hP 3 2)).const_mul (s 1:ℂ)),
    integral_add (f:=P 1 1) (g:=fun z => (s 0:ℂ)*P 2 2 z)
      (hP 1 1) ((hP 2 2).const_mul (s 0:ℂ)),integral_const_mul,
    integral_const_mul,integral_const_mul,integral_add (hP 2 3) (hP 3 2)]
  rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_EndPointEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.endPointEnergyMeasureSpaceUnitAddCircle
local instance endPointEnergyIsProbabilityMeasure_r28d5ce_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
lemma sourceEndSmoothDensity_cylinder (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) (κ a b R : ℝ) (hR : 0≤R)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    Integrable (sourceEndSmoothDensity s f κ a b φ) ((FiniteAxisMeasure R).prod volume) ∧
    (∫ z,sourceEndSmoothDensity s f κ a b φ z ∂(FiniteAxisMeasure R).prod volume)=
      (flatCylinderEnergy s (cylinderEndJet s hs κ R hR f)
        (sourceAngularLpJet hφ a b R)).re := by
  let u := cylinderEndJet s hs κ R hR f
  let v := sourceAngularLpJet hφ a b R
  have hv (k : Fin 3) : ∀ᵐ z∂(FiniteAxisMeasure R).prod volume,(v k.succ z).im=0 := by
    filter_upwards [sourceAngularLpJet_ae hφ a b R k.succ] with z hz
    change (sourceAngularLpJet hφ a b R k.succ z).im=0
    rw [hz]
    exact sourceAngularJet_im φ a b k.succ z
  obtain ⟨hi,he⟩ := flatCylinderEnergy_real_integral s u v hv
  have hve : ∀ᵐ z∂(FiniteAxisMeasure R).prod volume,
      (fun k : Fin 3 => (v k.succ z).re)=
        (fun k : Fin 3 => (sourceAngularJet φ a b k.succ z).re) := by
    filter_upwards [ae_all_iff.mpr (fun k : Fin 3 => sourceAngularLpJet_ae hφ a b R k.succ)] with z hz
    exact funext (fun k => congrArg Complex.re (hz k))
  have hd : (fun z => (fun k : Fin 3 => (u k.succ z).re) ⬝ᵥ
      (flatCylinderMatrix s*ᵥ(fun k : Fin 3 => (v k.succ z).re)))=ᵐ[(FiniteAxisMeasure R).prod volume]
        sourceEndSmoothDensity s f κ a b φ := by
    filter_upwards [cylinderEndJet_covector_ae s hs κ R hR f,hve] with z hu hv
    change (fun k : Fin 3 => (cylinderEndJet s hs κ R hR f k.succ z).re) ⬝ᵥ
      (flatCylinderMatrix s*ᵥ(fun k : Fin 3 => (v k.succ z).re))=_
    rw [hu,hv]
    rfl
  exact ⟨hi.congr hd,(integral_congr_ae hd).symm.trans he.symm⟩

lemma sourceEndSmoothDensity_green (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) (κ a b R : ℝ) (hR : 0<R)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    (∫ z,sourceEndSmoothDensity s f κ a b φ z ∂(FiniteAxisMeasure R).prod volume)=
      inner ℝ (spectralGraphWeight (torusRate s) f)
        (spectralGraphWeight (torusRate s) (smoothCollarTrace s b hφ))-
      κ*spectralGraphMean (torusRate s) (smoothCollarTrace s b hφ)+
      cylinderTerminalFlux s κ R f (smoothCollarTrace s (a*R+b) hφ) := by
  rw [(sourceEndSmoothDensity_cylinder s hs f κ a b R hR.le hφ).2]
  exact cylinderEndJet_real_green s hs κ hR f
    ⟨(_,(_,_)),sourceAngularLpJet_graph s hφ a b R⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularMeasureExact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma continuous_faceRayCircle (w : ℝ) (j : Fin 4) :
    Continuous (fun b : ℝ => ((faceRayAngle w j b:ℝ):UnitAddCircle)) :=
  (AddCircle.continuous_mk' 1).comp
    (continuous_iff_continuousAt.mpr fun b => (hasDerivAt_faceRayAngle w j b).continuousAt)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_FaceMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
attribute [local instance] OAI.ScalarConductivity.sourceFaceMeasureCircleMeasureSpace
local instance sourceFaceMeasureCircleIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma continuous_sourceFaceParameter (i j : Fin 4) : Continuous (sourceFaceParameter i j) := by
  unfold sourceFaceParameter
  simp_rw [sourceFaceAngles_torus]
  apply (continuous_apply 0).prodMk
  apply continuous_pi
  intro k
  fin_cases k
  · exact (continuous_faceRayCircle 1 i).comp (continuous_apply 1)
  · exact (continuous_faceRayCircle sourceRadialWidth j).comp (continuous_apply 2)

lemma continuous_sourceFaceWeight (i j : Fin 4) : Continuous (sourceFaceWeight i j) :=
  ((continuous_faceRayDensity 1 i).comp (continuous_apply 1)).mul
    ((continuous_faceRayDensity sourceRadialWidth j).comp (continuous_apply 2))

lemma sourceFaceWeight_pos (i j : Fin 4) (x : Fin 3 → ℝ) : 0 < sourceFaceWeight i j x :=
  mul_pos (faceRayDensity_pos' (by norm_num) i (x 1))
    (faceRayDensity_pos' (by norm_num [sourceRadialWidth,sourceHole]) j (x 2))

instance finite_sourceFaceMeasure (l r : ℝ) (i j : Fin 4) :
    IsFiniteMeasure (sourceFaceMeasure l r i j) := by
  have h : IntegrableOn (sourceFaceWeight i j) (sourceExtendedBox l r) volume :=
    (continuous_sourceFaceWeight i j).continuousOn.integrableOn_compact isCompact_Icc
  have := isFiniteMeasure_withDensity_ofReal h.hasFiniteIntegral
  unfold sourceFaceMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma integral_sourceFaceMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l r : ℝ) (i j : Fin 4) {F : ℝ × UnitAddTorus (Fin 2) → E}
    (hF : AEStronglyMeasurable F (sourceFaceMeasure l r i j)) :
    (∫ z,F z ∂sourceFaceMeasure l r i j)=
      ∫ x in sourceExtendedBox l r,sourceFaceWeight i j x • F (sourceFaceParameter i j x) := by
  rw [sourceFaceMeasure,integral_map (continuous_sourceFaceParameter i j).aemeasurable hF,
    integral_withDensity_eq_integral_toReal_smul
      (continuous_sourceFaceWeight i j).measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  rw [ENNReal.toReal_ofReal (sourceFaceWeight_pos i j x).le]

lemma integral_sourceFaceWeight_continuous {F : ℝ × UnitAddTorus (Fin 2) → ℝ}
    (hF : Continuous F) (i j : Fin 4) {l r : ℝ} (hlr : l ≤ r) :
    (∫ x in sourceExtendedBox l r,sourceFaceWeight i j x * F (sourceFaceParameter i j x))=
      ∫ t in l..r,∫ a in (-1:ℝ)..1,
        (∫ b in (-1:ℝ)..1,torusFaceTerm 1 sourceRadialWidth (fun θ => F (t,θ)) i j a b)*
          faceRayDensity 1 i a := by
  rw [integral_sourceExtendedBox (g:=fun x => sourceFaceWeight i j x * F (sourceFaceParameter i j x)) ((continuous_sourceFaceWeight i j).mul
    (hF.comp (continuous_sourceFaceParameter i j))) hlr]
  congr 1
  funext t
  congr 1
  funext a
  rw [←intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr
  intro b _
  simp only [sourceFaceWeight,sourceFaceParameter,sourceFaceAngles_torus,torusFaceTerm,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  ring

lemma continuous_sourceFaceIntegral {F : ℝ × UnitAddTorus (Fin 2) → ℝ}
    (hF : Continuous F) (i j : Fin 4) :
    Continuous (fun t => ∫ a in (-1:ℝ)..1,
      (∫ b in (-1:ℝ)..1,torusFaceTerm 1 sourceRadialWidth (fun θ => F (t,θ)) i j a b)*
        faceRayDensity 1 i a) := by
  apply continuous_parametric_unitInterval
  apply Continuous.mul
  · apply continuous_parametric_unitInterval
    unfold torusFaceTerm
    apply Continuous.mul
    · apply hF.comp
      apply continuous_fst.fst.prodMk
      apply continuous_pi
      intro k
      fin_cases k
      · exact (continuous_faceRayCircle 1 i).comp continuous_fst.snd
      · exact (continuous_faceRayCircle sourceRadialWidth j).comp continuous_snd
    · exact (continuous_faceRayDensity sourceRadialWidth j).comp continuous_snd
  · exact (continuous_faceRayDensity 1 i).comp continuous_snd

theorem sourceCylinderMeasure_eq_faces {l r : ℝ} (hlr : l ≤ r) :
    (volume.restrict (Ioc l r)).prod (volume : Measure (UnitAddTorus (Fin 2)))=
      ∑ i : Fin 4,∑ j : Fin 4,sourceFaceMeasure l r i j := by
  have : ((volume.restrict (Ioc l r)).prod (volume : Measure (UnitAddTorus (Fin 2)))).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro F
  have hi : Integrable (fun z => F z)
      ((volume.restrict (Ioc l r)).prod (volume : Measure (UnitAddTorus (Fin 2)))) := F.integrable
  rw [integral_prod _ hi,←intervalIntegral.integral_of_le hlr]
  rw [integral_finsetSum_measure (fun i _ =>
    integrable_finsetSum_measure.mpr (fun j _ => F.integrable))]
  simp_rw [integral_finsetSum_measure (fun j _ => F.integrable)]
  have hh (i j : Fin 4) : (∫ z,F z ∂sourceFaceMeasure l r i j)=
      ∫ t in l..r,∫ a in (-1:ℝ)..1,
        (∫ b in (-1:ℝ)..1,torusFaceTerm 1 sourceRadialWidth (fun θ => F (t,θ)) i j a b)*
          faceRayDensity 1 i a := by
    rw [integral_sourceFaceMeasure (F:=fun z => F z) l r i j F.continuous.aestronglyMeasurable]
    exact integral_sourceFaceWeight_continuous F.continuous i j hlr
  simp_rw [hh]
  have he (t : ℝ) := integral_unitTorus_faces (w₀:=1) (w₁:=sourceRadialWidth)
    (F:=fun θ => F (t,θ)) (by norm_num) (by norm_num [sourceRadialWidth,sourceHole])
    (F.continuous.comp (continuous_const.prodMk continuous_id) : Continuous (fun θ => F (t,θ)))
  simp only [volume_pi,unitCircle_volume_eq_haar] at he
  trans ∫ t in l..r,∑ i : Fin 4,∑ j : Fin 4,∫ a in (-1:ℝ)..1,
      (∫ b in (-1:ℝ)..1,torusFaceTerm 1 sourceRadialWidth (fun θ => F (t,θ)) i j a b)*
        faceRayDensity 1 i a
  · apply intervalIntegral.integral_congr
    intro t _
    exact he t
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (continuous_finsetSum _ (fun j _ => continuous_sourceFaceIntegral (F:=fun z => F z) F.continuous i j)).intervalIntegrable l r)]
  apply Finset.sum_congr rfl
  intro i _
  exact intervalIntegral.integral_finsetSum (fun j _ =>
    (continuous_sourceFaceIntegral (F:=fun z => F z) F.continuous i j).intervalIntegrable l r)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_FaceIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.sourceFaceIntegralCircleMeasureSpace
local instance sourceFaceIntegralCircleIsProbabilityMeasure_r28d5ce_1 :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
lemma sourceFaceMeasure_le_cylinder {l r : ℝ} (hlr : l ≤ r) (i j : Fin 4) :
    sourceFaceMeasure l r i j ≤
      (volume.restrict (Ioc l r)).prod (volume : Measure (UnitAddTorus (Fin 2))) := by
  rw [sourceCylinderMeasure_eq_faces hlr]
  exact le_trans (Finset.single_le_sum (fun _ _ => Measure.zero_le _) (Finset.mem_univ j))
    (Finset.single_le_sum (f := fun face => ∑ patch,sourceFaceMeasure l r face patch)
      (fun _ _ => Measure.zero_le _) (Finset.mem_univ i))

lemma integrable_sourceFacePullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × UnitAddTorus (Fin 2) → E} {l r : ℝ} (hlr : l ≤ r)
    (hF : Integrable F ((volume.restrict (Ioc l r)).prod volume)) (i j : Fin 4) :
    IntegrableOn (fun x => sourceFaceWeight i j x • F (sourceFaceParameter i j x))
      (sourceExtendedBox l r) volume := by
  have hf := hF.mono_measure (sourceFaceMeasure_le_cylinder hlr i j)
  have hg := (integrable_map_measure hf.aestronglyMeasurable
    (continuous_sourceFaceParameter i j).aemeasurable).mp hf
  have hh := (integrable_withDensity_iff_integrable_smul'
    (continuous_sourceFaceWeight i j).measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hg
  simpa only [IntegrableOn,Function.comp_apply,ENNReal.toReal_ofReal (sourceFaceWeight_pos i j _).le] using hh

theorem integral_sourceCylinder_faces {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × UnitAddTorus (Fin 2) → E} {l r : ℝ} (hlr : l ≤ r)
    (hF : Integrable F ((volume.restrict (Ioc l r)).prod volume)) :
    (∫ z,F z ∂(volume.restrict (Ioc l r)).prod volume)=
      ∑ i : Fin 4,∑ j : Fin 4,∫ x in sourceExtendedBox l r,
        sourceFaceWeight i j x • F (sourceFaceParameter i j x) := by
  have hf (i j : Fin 4) := hF.mono_measure (sourceFaceMeasure_le_cylinder hlr i j)
  rw [sourceCylinderMeasure_eq_faces hlr,integral_finsetSum_measure (fun i _ =>
    integrable_finsetSum_measure.mpr (fun j _ => hf i j))]
  simp_rw [integral_finsetSum_measure (fun j _ => hf _ j)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact integral_sourceFaceMeasure l r i j (hf i j).aestronglyMeasurable

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FullWeakEndEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma sourceCollarClosedPiece_measurable (l r : ℝ) (i j : Fin 4) :
    MeasurableSet (sourceCollarPiece i j '' sourceExtendedBox l r) :=
  (isCompact_Icc.image (sourceCollarPiece_contDiff i j).continuous).measurableSet

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FullEndClosedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma sourceExtendedBox_interior_axial {l r : ℝ} {x : Fin 3 → ℝ}
    (hx : x∈interior (sourceExtendedBox l r)) : x 0∈Ioo l r := by
  have hbox : sourceExtendedBox l r=
      (univ : Set (Fin 3)).pi (fun k => Icc (![l,-1,-1] k) (![r,1,1] k)) := by
    ext x
    simp only [sourceExtendedBox,mem_Icc,Set.mem_pi,mem_univ,true_implies,Pi.le_def]
    simp only [forall_and]
  rw [hbox,interior_pi_set (finite_univ)] at hx
  have ht := hx 0 (mem_univ 0)
  simpa only [interior_Icc,Matrix.cons_val_zero] using ht

lemma sourceExtendedBox_axial_strict_ae (l r : ℝ) :
    ∀ᵐ x∂volume.restrict (sourceExtendedBox l r),x 0∈Ioo l r := by
  have hB : volume (frontier (sourceExtendedBox l r))=0 :=
    (convex_Icc _ _).addHaar_frontier volume
  have hn : ∀ᵐ x : Fin 3 → ℝ,x∉frontier (sourceExtendedBox l r) := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hB
  filter_upwards [ae_restrict_of_ae hn,
    ae_restrict_mem (show MeasurableSet (sourceExtendedBox l r) from measurableSet_Icc)] with x hx hm
  apply sourceExtendedBox_interior_axial
  by_contra hi
  exact hx ⟨subset_closure hm,hi⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalFaceSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceExtendedBox_mono {l r l' r' : ℝ} (hl : l'≤l) (hr : r ≤ r') :
    sourceExtendedBox l r ⊆ sourceExtendedBox l' r' := by
  intro x hx
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  exact mem_sourceExtendedBox.mpr ⟨⟨hl.trans ht.1,ht.2.trans hr⟩,ha,hb⟩

lemma sourceCollarPieces_aedisjoint {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    Pairwise (fun k m : Fin 4 × Fin 4 => AEDisjoint volume
      (sourceCollarPiece k.1 k.2 '' sourceExtendedBox l r)
      (sourceCollarPiece m.1 m.2 '' sourceExtendedBox l r)) := by
  intro k m hkm
  have hn : ∀ᵐ y : Fin 3 → ℝ, y∉
      (sourceCollarPiece k.1 k.2 '' sourceExtendedBox l r) ∩
      (sourceCollarPiece m.1 m.2 '' sourceExtendedBox l r) := by
    filter_upwards [sourceCollar_open_charts_ae] with y hy hm
    obtain ⟨⟨z,hz,hzy⟩,w,hw,hwy⟩ := hm
    have hyb := sourceCollarClosedPiece_subset (l:=-(1:ℝ)/100) (r:=1/100)
      le_rfl le_rfl k.1 k.2 ⟨z,sourceExtendedBox_mono hl hr hz,hzy⟩
    obtain ⟨i,j,x,hx,hxy⟩ := hy hyb
    obtain ⟨hik,hjk⟩ := sourceCollarPiece_open_unique i j k.1 k.2 hx
      (sourceExtendedBox_mono hl hr hz) (hxy.trans hzy.symm)
    obtain ⟨him,hjm⟩ := sourceCollarPiece_open_unique i j m.1 m.2 hx
      (sourceExtendedBox_mono hl hr hw) (hxy.trans hwy.symm)
    exact hkm (Prod.ext (hik.symm.trans him) (hjk.symm.trans hjm))
  simpa only [AEDisjoint,ae_iff,not_not,Set.ofPred_mem_eq] using hn

theorem sourceClosedCollarBand_measure_faces {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    volume.restrict (sourceClosedCollarBand l r)=
      ∑ i : Fin 4,∑ j : Fin 4,
        volume.restrict (sourceCollarPiece i j '' sourceExtendedBox l r) := by
  rw [sourceClosedCollarBand_eq l r hl hr]
  have he : (⋃ i : Fin 4,⋃ j : Fin 4,sourceCollarPiece i j '' sourceExtendedBox l r)=
      ⋃ k : Fin 4 × Fin 4,sourceCollarPiece k.1 k.2 '' sourceExtendedBox l r := by
    ext x
    simp
  rw [he,Measure.restrict_iUnion_ae (sourceCollarPieces_aedisjoint hl hr)
    (fun k => (sourceCollarClosedPiece_measurable l r k.1 k.2).nullMeasurableSet),
    Measure.sum_fintype,Fintype.sum_prod_type]

lemma integral_sourceClosedCollarBand_faces {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) {F : (Fin 3 → ℝ) → ℝ}
    (hF : IntegrableOn F (sourceClosedCollarBand l r) volume) :
    (∫ y in sourceClosedCollarBand l r,F y)=
      ∑ i : Fin 4,∑ j : Fin 4,
        ∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,F y := by
  have hi (i j : Fin 4) := hF.mono_set (sourceCollarClosedPiece_subset hl hr i j)
  rw [sourceClosedCollarBand_measure_faces hl hr,integral_finsetSum_measure (fun i _ =>
    integrable_finsetSum_measure.mpr (fun j _ => hi i j))]
  simp_rw [integral_finsetSum_measure (fun j _ => hi _ j)]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalEndSmoothEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.physicalEndSmoothEnergyMeasureSpace
local instance physicalEndSmoothEnergyIsProbabilityMeasure_r28d5ce_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
theorem fullAttachedEnd_smooth_energy_pullback (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    {a b l r R : ℝ} (ha : a≠0) (hlr : l ≤ r) (hR : 0≤R)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    (ht : ∀ t∈Ioo l r,0<a*(t-b)) :
    IntegrableOn (fun y => fullAttachedEndGradient s f a b κ y ⬝ᵥ
      (attachedCollarTensor s a y*ᵥphysicalTestCovector φ y)) (sourceClosedCollarBand l r) volume ∧
    (∫ y in sourceClosedCollarBand l r,fullAttachedEndGradient s f a b κ y ⬝ᵥ
      (attachedCollarTensor s a y*ᵥphysicalTestCovector φ y))=
      |a| *angularArea*(∫ z,sourceEndSmoothDensity s f κ a⁻¹ b φ
        (affineEndCoordinates a b z) ∂(volume.restrict (Ioc l r)).prod volume) := by
  let F := sourceEndSmoothDensity s f κ a⁻¹ b φ
  let G := fun y => fullAttachedEndGradient s f a b κ y ⬝ᵥ
    (attachedCollarTensor s a y*ᵥphysicalTestCovector φ y)
  have hF := (sourceEndSmoothDensity_cylinder s hs f κ a⁻¹ b R hR hφ).1
  have hg := integrable_affineEndCoordinates ha hT hF
  have he (i j : Fin 4) :
      (fun x => |(sourceCollarDerivative i j x).det| • G (sourceCollarPiece i j x))=ᵐ[
        volume.restrict (sourceExtendedBox l r)]
      (fun x => (|a| *angularArea)*(sourceFaceWeight i j x •
        F (affineEndCoordinates a b (sourceFaceParameter i j x)))) := by
    filter_upwards [sourceExtendedBox_open_ae hl hr,sourceExtendedBox_axial_strict_ae l r]
      with x hx hm
    dsimp only [G]
    rw [smul_eq_mul,sourceCollarDerivative_det,←sourceCollarJacobian_det,
      fullAttachedEnd_test_energy s hs f κ φ ha i j hx (ht (x 0) hm)]
    have hj := sourceAngularJet_attachedCovector hφ ha b i j hx
    change _=(|a| *angularArea)*(sourceFaceWeight i j x *
      (fullEndFlatCovector s f κ (a*(x 0-b)) (torusAngles (sourceFaceAngles i j x)) ⬝ᵥ
        (flatCylinderMatrix s*ᵥ(fun k : Fin 3 => (sourceAngularJet φ a⁻¹ b k.succ
          (a*(x 0-b),torusAngles (sourceFaceAngles i j x))).re))))
    rw [hj]
    unfold sourceFaceWeight
    ring
  have hi (i j : Fin 4) : IntegrableOn G
      (sourceCollarPiece i j '' sourceExtendedBox l r) volume := by
    apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume measurableSet_Icc
      (fun x _ => (sourceCollarPiece_hasFDeriv i j x).hasFDerivWithinAt)
      (sourceExtendedBox_injOn i j hl hr) G).mpr
    exact ((integrable_sourceFacePullback hlr hg i j).const_mul (|a| *angularArea)).congr (he i j).symm
  have hG : IntegrableOn G (sourceClosedCollarBand l r) volume := by
    unfold IntegrableOn
    rw [sourceClosedCollarBand_measure_faces hl hr]
    exact integrable_finsetSum_measure.mpr (fun i _ =>
      integrable_finsetSum_measure.mpr fun j _ => hi i j)
  refine ⟨hG,?_⟩
  change (∫ y in sourceClosedCollarBand l r,G y)=_
  rw [integral_sourceClosedCollarBand_faces hl hr hG,
    integral_sourceCylinder_faces (F:=fun z => sourceEndSmoothDensity s f κ a⁻¹ b φ
      (affineEndCoordinates a b z)) hlr hg,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [sourceExtended_integral i j hl hr G,integral_congr_ae (he i j),integral_const_mul]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalEndSmoothGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal

local instance physicalEndSmoothGreenMeasureSpaceUnitAddCircle_r28d5ce_1 : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
lemma fullAttachedEnd_smooth_green_neg_oai (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    {a l r R : ℝ} (ha : a<0) (hlr : l < r) (hR : a*(l-r)=R)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    (∫ y in sourceClosedCollarBand l r,fullAttachedEndGradient s f a r κ y ⬝ᵥ
      (attachedCollarTensor s a y*ᵥphysicalTestCovector φ y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) f)
        (spectralGraphWeight (torusRate s) (smoothCollarTrace s r hφ))-
      κ*spectralGraphMean (torusRate s) (smoothCollarTrace s r hφ)+
      cylinderTerminalFlux s κ R f (smoothCollarTrace s l hφ)) := by
  have hRp : 0<R := hR ▸ mul_pos_of_neg_of_neg ha (sub_neg.mpr hlr)
  have hT : ∀ t∈Icc l r,affineEndTime a r t∈Icc 0 R := by
    intro t ht
    dsimp [affineEndTime]
    constructor
    · exact mul_nonneg_of_nonpos_of_nonpos ha.le (sub_nonpos.mpr ht.2)
    · rw [←hR]; exact mul_le_mul_of_nonpos_left (sub_le_sub_right ht.1 r) ha.le
  have he := fullAttachedEnd_smooth_energy_pullback s hs f κ hφ ha.ne hlr.le hRp.le hl hr hT
    (fun t ht => mul_pos_of_neg_of_neg ha (sub_neg.mpr ht.2))
  rw [he.2,mul_assoc,←mul_left_comm angularArea |a|,
    integral_affineEndCoordinates_neg ha hlr.le hT hR (by ring) hRp.le
      (sourceEndSmoothDensity_cylinder s hs f κ a⁻¹ r R hRp.le hφ).1,
    sourceEndSmoothDensity_green s hs f κ a⁻¹ r R hRp hφ]
  have hend : a⁻¹*R+r=l := by rw [←hR]; field_simp [ha.ne]; ring
  rw [hend]

end ScalarConductivity

end
end

end OAI
end

theorem solution : type_of% @OAI.ScalarConductivity.fullAttachedEnd_smooth_green_neg_oai := @OAI.ScalarConductivity.fullAttachedEnd_smooth_green_neg_oai
