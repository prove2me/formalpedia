-- Prove2me | solution 1 for OAI.ThreeTorus.eventually_colored_controlled_anchor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T12:04:55.667448+00:00
-- url     : https://prove2.me/submissions/2f247d19-4eec-4acb-b82d-7b0f7471b2b5

import Mathlib
import Definitions.Def_ThreeTorus
import Definitions.Def_OAIQ13Tt000
import Theorems.Thm_OAI_ThreeTorus_exact_neutral_circle_spectral_estimate
import Theorems.Thm_OAI_ThreeTorus_exact_neutral_passage

section
-- module Solutions.OAIQ13_TT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PositiveLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive Fourier laws, compact integral differentiation, affine densities, and prime-sieve signal laws. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ThreeTorus

/-- Compact-parameter differentiation, used by the exact passage near epsilon=0. -/
lemma hasFDerivAt_compact_integral
    {E : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E × ℝ → G} (hF : ContDiff ℝ 1 F) (a b : ℝ) (x : E) :
    HasFDerivAt (fun y => ∫ t in a..b, F (y,t))
      (∫ t in a..b, (fderiv ℝ F (x,t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
  let D : E × ℝ → E →L[ℝ] G := fun p =>
    (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hD : Continuous D := hF.continuous_fderiv (by norm_num) |>.clm_comp continuous_const
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn hD.continuousOn
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F := fun y t => F (y,t)) (F' := fun y t => D (y,t))
    (bound := fun _ => C) (Metric.closedBall_mem_nhds x (by norm_num : (0:ℝ)<1)) ?_ ?_ ?_ ?_
    intervalIntegrable_const ?_
  · exact Eventually.of_forall (fun y => (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    intro y hy
    exact hC (y,t) ⟨hy,uIoc_subset_uIcc ht⟩
  · exact Eventually.of_forall (fun t y _ => by
      simpa [D,Function.comp_def] using ((hF.differentiable one_ne_zero ((ContinuousLinearMap.inl ℝ E ℝ) y+(0,t))).hasFDerivAt).comp y
        ((ContinuousLinearMap.inl ℝ E ℝ).hasFDerivAt.add_const (0,t)))

/-- Smooth parameter integration over a fixed compact interval. -/
lemma contDiff_compact_integral
    {E : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (n : ℕ) {F : E × ℝ → G} (hF : ContDiff ℝ n F) (a b : ℝ) :
    ContDiff ℝ n (fun y => ∫ t in a..b, F (y,t)) := by
  induction n generalizing G with
  | zero =>
    apply contDiff_zero.mpr
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (show Continuous (Function.uncurry (fun y t => F (y,t))) from hF.continuous) a b
  | succ n ih =>
    let D : E × ℝ → E →L[ℝ] G := fun p =>
      (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hD : ContDiff ℝ n D := (hF.fderiv_right (by simp)).clm_comp contDiff_const
    have hder (x : E) := hasFDerivAt_compact_integral (hF.of_le (by exact_mod_cast Nat.succ_pos n)) a b x
    rw [show ((n+1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞)+1 by simp, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hder x).differentiableAt, ?_, ?_⟩
    · simp
    · have heq : fderiv ℝ (fun y => ∫ t in a..b, F (y,t)) =
          fun y => ∫ t in a..b, D (y,t) := by
        funext y
        exact (hder y).fderiv
      rw [heq]
      exact ih hD

lemma smooth_compact_integral
    {E : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E × ℝ → G} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (a b : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∫ t in a..b, F (y,t)) := by
  rw [contDiff_infty]
  intro n
  exact contDiff_compact_integral n (hF.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))) a b

/-! The positive Fourier law. The sinc and averaged
baseline below are exactly those of the manuscript, including the scale and
normalization. -/
open scoped FourierTransform Convolution

/-! Exact Fourier support, without assuming an interval inversion formula. -/

open scoped ComplexConjugate

end ThreeTorus

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Twists
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product torus, exact angular packets, all integer twist iterates, and measure-preserving passage charts. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace ThreeTorus

lemma continuous_packet {m : ℤ} {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) : Continuous (packet m A) :=
  (hA.comp continuous_snd).mul ((fourier m).continuous.comp continuous_fst)

end ThreeTorus

namespace ThreeTorus

lemma passage_conjugacy (H σ : UnitAddCircle → UnitAddCircle) (x : TripleTorus) :
    passageChart H (passageMap H σ ((passageChart H).symm x)) = passageTwist σ x := by
  simp only [passageChart, passageMap, passageTwist, circleThetaShear, circleCycle,
    Equiv.trans_apply, Equiv.symm_trans_apply]
  ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma measurePreserving_circleCycle :
    MeasurePreserving circleCycle tripleVolume tripleVolume := by
  exact (measurePreserving_prodAssoc AddCircle.haarAddCircle AddCircle.haarAddCircle
    AddCircle.haarAddCircle).comp Measure.measurePreserving_swap

lemma measurePreserving_fiberTranslate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {g : Ω → UnitAddCircle} (hg : Measurable g) :
    MeasurePreserving (fun p : Ω × UnitAddCircle => (p.1,p.2+g p.1))
      (μ.prod AddCircle.haarAddCircle) (μ.prod AddCircle.haarAddCircle) := by
  exact (MeasurePreserving.id μ).skew_product (measurable_snd.add (hg.comp measurable_fst))
    (Filter.Eventually.of_forall (fun x => (measurePreserving_add_right AddCircle.haarAddCircle (g x)).map_eq))

lemma measurePreserving_circleThetaShear {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H) :
    MeasurePreserving (circleThetaShear H) tripleVolume tripleVolume := by
  exact Measure.measurePreserving_swap.comp
    ((measurePreserving_fiberTranslate (AddCircle.haarAddCircle.prod AddCircle.haarAddCircle)
      (hH.comp measurable_fst)).comp Measure.measurePreserving_swap)

lemma measurePreserving_passageChart {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H) :
    MeasurePreserving (passageChart H) tripleVolume tripleVolume :=
  measurePreserving_circleCycle.comp (measurePreserving_circleThetaShear hH.neg)

lemma passageChart_inverse_measurable {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H) :
    Measurable (passageChart H).symm := by
  change Measurable (fun x : TripleTorus => (x.2.2-(-H x.1),x.1,x.2.1))
  exact (measurable_snd.snd.sub (hH.comp measurable_fst).neg).prodMk
    (measurable_fst.prodMk measurable_snd.fst)

lemma measurePreserving_passageChart_inverse {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H) :
    MeasurePreserving (passageChart H).symm tripleVolume tripleVolume := by
  let e : TripleTorus ≃ᵐ TripleTorus :=
    { toEquiv := passageChart H
      measurable_toFun := (measurePreserving_passageChart hH).measurable
      measurable_invFun := passageChart_inverse_measurable hH }
  exact MeasurePreserving.symm e (measurePreserving_passageChart hH)

lemma passage_as_conjugate (H σ : UnitAddCircle → UnitAddCircle) :
    (passageMap H σ : TripleTorus → TripleTorus) =
      (passageChart H).symm ∘ passageTwist σ ∘ passageChart H := by
  funext x
  have hh := passage_conjugacy H σ (passageChart H x)
  simpa only [Equiv.symm_apply_apply, Function.comp_apply] using
    congrArg (passageChart H).symm hh

lemma measurePreserving_passageMap {H σ : UnitAddCircle → UnitAddCircle}
    (hH : Measurable H) (hσ : Measurable σ) :
    MeasurePreserving (passageMap H σ) tripleVolume tripleVolume := by
  rw [passage_as_conjugate]
  exact (measurePreserving_passageChart_inverse hH).comp
    ((measurePreserving_circleThetaShear hσ).comp (measurePreserving_passageChart hH))

end ThreeTorus

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Geometry
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Torus coordinate equivalence, smooth passage geometry, and all-jet passage convergence. -/

section

/-! Torus coordinate equivalence and retained passage geometry. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ThreeTorus

lemma torusTriple_apply (x : Torus) : torusTriple x = (x 0,x 1,x 2) := rfl

lemma torusTriple_symm_apply (x : TripleTorus) : torusTriple.symm x = ![x.1,x.2.1,x.2.2] := by
  ext i
  fin_cases i <;> rfl

lemma torusPassage_apply (h s : UnitAddCircle → UnitAddCircle) (x : Torus) :
    torusPassage h s x = ![x 0+h (x 1+s (x 2))-h (x 1),x 1+s (x 2),x 2] := by
  rw [torusPassage,Equiv.trans_apply,Equiv.trans_apply]
  rw [show torusTriple.toEquiv x = (x 0,x 1,x 2) from rfl]
  exact torusTriple_symm_apply _

lemma torusPassage_symm_apply (h s : UnitAddCircle → UnitAddCircle) (x : Torus) :
    (torusPassage h s).symm x = ![x 0-h (x 1)+h (x 1-s (x 2)),x 1-s (x 2),x 2] := by
  change torusTriple.symm ((passageMap h s).symm (torusTriple x)) = _
  rw [torusTriple_apply,torusTriple_symm_apply]
  rfl

lemma measurePreserving_torusPassage {h s : UnitAddCircle → UnitAddCircle}
    (hh : Measurable h) (hs : Measurable s) : MeasurePreserving (torusPassage h s) μ μ := by
  exact (MeasurePreserving.symm torusTriple measurePreserving_torusTriple).comp
    ((measurePreserving_passageMap hh hs).comp measurePreserving_torusTriple)

lemma contDiff_passageLift {h s : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (passageLift h s) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact ((contDiff_apply ℝ ℝ 0).add (hh.comp ((contDiff_apply ℝ ℝ 1).add (hs.comp (contDiff_apply ℝ ℝ 2))))).sub
      (hh.comp (contDiff_apply ℝ ℝ 1))
  · exact (contDiff_apply ℝ ℝ 1).add (hs.comp (contDiff_apply ℝ ℝ 2))
  · exact contDiff_apply ℝ ℝ 2

lemma contDiff_passageInverseLift {h s : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (passageInverseLift h s) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact ((contDiff_apply ℝ ℝ 0).sub (hh.comp (contDiff_apply ℝ ℝ 1))).add
      (hh.comp ((contDiff_apply ℝ ℝ 1).sub (hs.comp (contDiff_apply ℝ ℝ 2))))
  · exact (contDiff_apply ℝ ℝ 1).sub (hs.comp (contDiff_apply ℝ ℝ 2))
  · exact contDiff_apply ℝ ℝ 2

lemma smooth_torusPassage {h s : UnitAddCircle → UnitAddCircle} {H S : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (hH : ∀ x : ℝ, h (x : UnitAddCircle) = (H x : UnitAddCircle))
    (hS : ∀ x : ℝ, s (x : UnitAddCircle) = (S x : UnitAddCircle)) :
    Smooth (torusPassage h s) := by
  intro x
  refine ⟨Set.univ,isOpen_univ,Set.mem_univ x,passageLift H S,
    (contDiff_passageLift hh hs).contDiffOn,?_⟩
  intro y _
  rw [torusPassage_apply]
  ext i
  fin_cases i <;> simp only [project,passageLift,hS,← AddCircle.coe_add,hH,← AddCircle.coe_sub] <;> rfl

lemma smooth_torusPassage_symm {h s : UnitAddCircle → UnitAddCircle} {H S : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (hH : ∀ x : ℝ, h (x : UnitAddCircle) = (H x : UnitAddCircle))
    (hS : ∀ x : ℝ, s (x : UnitAddCircle) = (S x : UnitAddCircle)) :
    Smooth (torusPassage h s).symm := by
  intro x
  refine ⟨Set.univ,isOpen_univ,Set.mem_univ x,passageInverseLift H S,
    (contDiff_passageInverseLift hh hs).contDiffOn,?_⟩
  intro y _
  rw [torusPassage_symm_apply]
  ext i
  fin_cases i <;> simp only [project,passageInverseLift,hS,← AddCircle.coe_sub,hH,← AddCircle.coe_add] <;> rfl

end ThreeTorus

noncomputable section
open MeasureTheory Set Function
open scoped Topology
namespace ThreeTorus

lemma continuous_periodic_lift {X : Type*} [TopologicalSpace X] {f : ℝ → X}
    (hf : Function.Periodic f 1) (hc : Continuous f) : Continuous hf.lift := by
  exact hc.quotient_lift _

lemma circlePrimitive_coe {v : ℝ → ℝ} (hv : Function.Periodic v 1)
    (hc : Continuous v) {k : ℤ} (hk : (∫ t in 0..1, v t) = k) (x : ℝ) :
    circlePrimitive hv hc hk (x:UnitAddCircle) = (↑(∫ t in 0..x, v t):UnitAddCircle) := rfl

lemma continuous_circlePrimitive {v : ℝ → ℝ} (hv : Function.Periodic v 1)
    (hc : Continuous v) {k : ℤ} (hk : (∫ t in 0..1, v t) = k) :
    Continuous (circlePrimitive hv hc hk) := by
  exact continuous_periodic_lift _ ((AddCircle.continuous_mk' 1).comp
    (intervalIntegral.differentiable_integral_of_continuous hc).continuous)

lemma circleSpeed_coe {s : ℝ → ℝ} (hs : Function.Periodic s 1) (x : ℝ) :
    circleSpeed hs (x:UnitAddCircle) = (s x:UnitAddCircle) := rfl

lemma continuous_circleSpeed {s : ℝ → ℝ} (hs : Function.Periodic s 1) (hc : Continuous s) :
    Continuous (circleSpeed hs) := by
  exact (AddCircle.continuous_mk' 1).comp (continuous_periodic_lift hs hc)

/-- Global C-infinity, inverse C-infinity, and exact Haar preservation for the
manuscript passage, without assuming any geometric conclusion. -/
lemma primitive_passage_properties {v s : ℝ → ℝ}
    (hv : Function.Periodic v 1) (hs : Function.Periodic s 1)
    (hvc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (hsc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s)
    {k : ℤ} (hk : (∫ t in 0..1, v t) = k) :
    let T := torusPassage (circlePrimitive hv hvc.continuous hk) (circleSpeed hs)
    Smooth T ∧ Smooth T.symm ∧ MeasurePreserving T μ μ := by
  exact ⟨smooth_torusPassage (contDiff_real_primitive hvc) hsc
      (circlePrimitive_coe hv hvc.continuous hk) (circleSpeed_coe hs),
    smooth_torusPassage_symm (contDiff_real_primitive hvc) hsc
      (circlePrimitive_coe hv hvc.continuous hk) (circleSpeed_coe hs),
    measurePreserving_torusPassage (continuous_circlePrimitive hv hvc.continuous hk).measurable
      (continuous_circleSpeed hs hsc.continuous).measurable⟩

end ThreeTorus

noncomputable section
open MeasureTheory Set Function
open scoped Topology
namespace ThreeTorus

/-- The bounded winding correction; no subsequence of passage integers is needed. -/
lemma passage_rounding (A : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ d : ℝ, ∃ k : ℤ, |d| ≤ (N:ℝ)⁻¹ ∧ (N:ℝ)*(A+d) = k := by
  let k : ℤ := ⌊(N:ℝ)*A⌋
  let d : ℝ := ((k:ℝ)-(N:ℝ)*A)/(N:ℝ)
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  refine ⟨d,k,?_,?_⟩
  · have hk1 : (k:ℝ) ≤ (N:ℝ)*A := Int.floor_le _
    have hk2 : (N:ℝ)*A-1 ≤ (k:ℝ) := (Int.sub_one_lt_floor _).le
    dsimp [d]
    rw [abs_div,abs_of_pos hn,abs_of_nonpos (sub_nonpos.mpr hk1),← one_div]
    exact div_le_div_of_nonneg_right (by linarith) hn.le
  · dsimp [d]
    field_simp
    ring

lemma passage_rounded_slope {v : ℝ → ℝ}
    (hv : Function.Periodic v 1) (hc : Continuous v) (N : ℕ) (d : ℝ) {k : ℤ}
    (hk : (N:ℝ)*((∫ t in 0..1, v t)+d) = k) :
    Function.Periodic (fun x => (N:ℝ)*(v x+d)) 1 ∧
    (∫ t in 0..1, (N:ℝ)*(v t+d)) = k := by
  constructor
  · intro x
    dsimp only
    rw [hv x]
  · rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hc.intervalIntegrable _ _) intervalIntegrable_const]
    simpa using hk

lemma passage_speed_smooth {J : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (N : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (N:ℝ)⁻¹+(N:ℝ)⁻¹^2*J x) := by fun_prop

end ThreeTorus

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ThreeTorus

lemma iteratedFDeriv_slice
    {P E G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : P × E → G} {n : ℕ} (hF : ContDiff ℝ n F) (p : P) (x : E) :
    iteratedFDeriv ℝ n (fun y => F (p,y)) x =
      (iteratedFDeriv ℝ n F (p,x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ P E) := by
  have hh : ContDiff ℝ n (fun q : P × E => F ((p,0)+q)) :=
    hF.comp (contDiff_const.add contDiff_id)
  have he := (ContinuousLinearMap.inr ℝ P E).iteratedFDeriv_comp_right hh x (le_refl (n:WithTop ℕ∞))
  simpa only [Function.comp_def,ContinuousLinearMap.inr_apply,
    Prod.mk_add_mk,add_zero,zero_add,iteratedFDeriv_comp_add_left] using he

lemma continuous_iteratedFDeriv_slice
    {P E G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : P × E → G} {n : ℕ} (hF : ContDiff ℝ n F) :
    Continuous (fun q : P × E => iteratedFDeriv ℝ n (fun y => F (q.1,y)) q.2) := by
  simp_rw [iteratedFDeriv_slice hF]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin n => ContinuousLinearMap.inr ℝ P E)).continuous.comp
      hF.continuous_iteratedFDeriv'

/-- Joint smoothness gives convergence in every C^k seminorm on compact sets. -/
lemma smooth_parameter_jets_tendsto
    {P E G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : P × E → G} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (p : P) {K : Set E} (hK : IsCompact K) (n : ℕ) :
    TendstoUniformlyOn (fun a x => iteratedFDeriv ℝ n (fun y => F (a,y)) x)
      (fun x => iteratedFDeriv ℝ n (fun y => F (p,y)) x) (𝓝 p) K := by
  have hc := continuous_iteratedFDeriv_slice (hF.of_le
    (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤)))
  have hu := ((isCompact_closedBall p 1).prod hK).uniformContinuousOn_of_continuous hc.continuousOn
  have ht := UniformContinuousOn.tendstoUniformlyOn
    (F := fun a x => iteratedFDeriv ℝ n (fun y => F (a,y)) x)
    hu (by simp : p ∈ Metric.closedBall p (1:ℝ))
  simpa only [nhdsWithin_eq_nhds.mpr (Metric.closedBall_mem_nhds p (by norm_num : (0:ℝ)<1))] using ht

end ThreeTorus

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ThreeTorus

lemma smooth_passageFamily {v J : ℝ → ℝ}
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (r : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × ℝ) × Cover => passageFamily v J r q.1 q.2) := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ((ℝ × ℝ) × Cover) × ℝ =>
        v (q.1.2 1+q.2*(r*q.1.1.1*(1+q.1.1.1*J (q.1.2 2))))+q.1.1.2) := by
    fun_prop
  have hi := smooth_compact_integral hc 0 1
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (ℝ × ℝ) × Cover =>
      q.2 0+r*(1+q.1.1*J (q.2 2))*(∫ t in (0:ℝ)..1,
        v (q.2 1+t*(r*q.1.1*(1+q.1.1*J (q.2 2))))+q.1.2))
    exact (by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (ℝ × ℝ) × Cover => q.2 0)).add
      ((by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (ℝ × ℝ) × Cover => r*(1+q.1.1*J (q.2 2)))).mul hi)
  · change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (ℝ × ℝ) × Cover =>
      q.2 1+r*q.1.1*(1+q.1.1*J (q.2 2)))
    fun_prop
  · change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (ℝ × ℝ) × Cover => q.2 2)
    fun_prop

lemma passageFamily_zero (v J : ℝ → ℝ) (r : ℝ) :
    passageFamily v J r (0,0) = fun x : Cover => ![x 0+r*v (x 1),x 1,x 2] := by
  funext x
  simp [passageFamily]

lemma passageFamily_increment {v J : ℝ → ℝ} (hv : Continuous v)
    {N : ℕ} (hN : 0 < N) (d r u a : ℝ) :
    (∫ t in 0..u+r*((N:ℝ)⁻¹+(N:ℝ)⁻¹^2*J a), (N:ℝ)*(v t+d))
      -(∫ t in 0..u, (N:ℝ)*(v t+d)) =
    r*(1+(N:ℝ)⁻¹*J a)*(∫ t in (0:ℝ)..1,
      v (u+t*(r*(N:ℝ)⁻¹*(1+(N:ℝ)⁻¹*J a)))+d) := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun t => (N:ℝ)*(v t+d)) volume a b :=
    fun a b => (continuous_const.mul (hv.add continuous_const)).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 u) (hi u _), add_sub_cancel_left]
  rw [intervalIntegral.integral_const_mul]
  have hs : r*((N:ℝ)⁻¹+(N:ℝ)⁻¹^2*J a) = r*(N:ℝ)⁻¹*(1+(N:ℝ)⁻¹*J a) := by ring
  rw [hs]
  have he := intervalIntegral.smul_integral_comp_add_mul (fun t => v t+d)
    (a := (0:ℝ)) (b := 1) (r*(N:ℝ)⁻¹*(1+(N:ℝ)⁻¹*J a)) u
  simp only [smul_eq_mul,mul_zero,add_zero,mul_one] at he
  rw [← he]
  have hf : (fun t => v (u+t*(r*(N:ℝ)⁻¹*(1+(N:ℝ)⁻¹*J a)))+d) =
      (fun t => v (u+r*(N:ℝ)⁻¹*(1+(N:ℝ)⁻¹*J a)*t)+d) := by
    funext t
    rw [mul_comm t]
  rw [hf]
  field_simp

/-- The passage and inverse are specializations of the same smooth family. -/
lemma passageLift_eq_family {v J : ℝ → ℝ} (hv : Continuous v)
    {N : ℕ} (hN : 0 < N) (d : ℝ) :
    passageLift (fun u => ∫ t in 0..u, (N:ℝ)*(v t+d))
      (fun a => (N:ℝ)⁻¹+(N:ℝ)⁻¹^2*J a) = passageFamily v J 1 ((N:ℝ)⁻¹,d) ∧
    passageInverseLift (fun u => ∫ t in 0..u, (N:ℝ)*(v t+d))
      (fun a => (N:ℝ)⁻¹+(N:ℝ)⁻¹^2*J a) = passageFamily v J (-1) ((N:ℝ)⁻¹,d) := by
  have h1 (u a : ℝ) := passageFamily_increment (J := J) hv hN d 1 u a
  have h2 (u a : ℝ) := passageFamily_increment (J := J) hv hN d (-1) u a
  constructor
  · funext x i
    fin_cases i
    · dsimp [passageLift,passageFamily]
      simp only [one_mul] at h1 ⊢
      linarith [h1 (x 1) (x 2)]
    · dsimp [passageLift,passageFamily]
      ring
    · rfl
  · funext x i
    fin_cases i
    · dsimp [passageInverseLift,passageFamily]
      simp only [neg_one_mul,← sub_eq_add_neg] at h2 ⊢
      linarith [h2 (x 1) (x 2)]
    · dsimp [passageInverseLift,passageFamily]
      ring
    · rfl

lemma passage_parameters_tendsto {d : ℕ → ℝ}
    (hd : ∀ N : ℕ, 0 < N → |d N| ≤ (N:ℝ)⁻¹) :
    Tendsto (fun N : ℕ => ((N:ℝ)⁻¹,d N)) atTop (𝓝 (0,0)) := by
  have hn : Tendsto (fun N : ℕ => (N:ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hnd : Tendsto d atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hn
    filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    exact hd N hN
  exact hn.prodMk_nhds hnd

/-- All spatial derivatives of each sign of the passage converge uniformly on
any fixed compact set. This is genuine C-infinity convergence, not C-zero. -/
lemma passage_Cinfty_limit {v J : ℝ → ℝ}
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    {d : ℕ → ℝ} (hd : ∀ N : ℕ, 0 < N → |d N| ≤ (N:ℝ)⁻¹)
    (r : ℝ) {K : Set Cover} (hK : IsCompact K) (n : ℕ) :
    TendstoUniformlyOn
      (fun (N : ℕ) x => iteratedFDeriv ℝ n (passageFamily v J r ((N:ℝ)⁻¹,d N)) x)
      (fun x => iteratedFDeriv ℝ n (fun y : Cover => ![y 0+r*v (y 1),y 1,y 2]) x)
      atTop K := by
  have ht := smooth_parameter_jets_tendsto (smooth_passageFamily hv hJ r) (0,0) hK n
  simp only [passageFamily_zero] at ht
  intro U hU
  exact (passage_parameters_tendsto hd).eventually (ht U hU)

end ThreeTorus
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Cutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth cylinder cutoffs, circle periodization, and regularity of covering lifts. -/

section

/-! Smooth compact supported cutoffs on the actual real-frequency/slow-circle
cylinder, used for the disjoint stationary images in the passage lemma. -/
noncomputable section
open Set Function Filter Topology
open scoped Topology Manifold
namespace ThreeTorus

/-- A compactly supported Euclidean cutoff, equal to one on a neighborhood
of the prescribed compact set, not merely on the set itself. -/
lemma compact_smooth_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ f : E → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ U ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      ∀ x ∈ K, f =ᶠ[𝓝 x] 1 := by
  obtain ⟨O,hO,hKO,hOc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨V,hV,hKV,hVU⟩ := hK.exists_isOpen_closure_subset
    ((hU.inter hO).mem_nhdsSet.mpr (subset_inter hKU hKO))
  have hcV : IsCompact (closure V) := hOc.of_isClosed_subset isClosed_closure
    (fun x hx => subset_closure (hVU hx).2)
  obtain ⟨W,hW,hKW,hWV⟩ := hK.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hKV)
  obtain ⟨f,hf,hfr,hfs,hf1⟩ := exists_contMDiff_support_eq_eq_one_iff
    (I := 𝓘(ℝ,E)) (n := (⊤ : ℕ∞)) hV isClosed_closure hWV
  refine ⟨f,hf.contDiff,?_,?_,?_,?_⟩
  · simpa only [HasCompactSupport, tsupport, hfs] using hcV
  · rw [tsupport, hfs]
    intro x hx
    exact (hVU hx).1
  · intro x
    exact hfr (mem_range_self x)
  · intro x hx
    filter_upwards [hW.mem_nhds (hKW hx)] with y hy
    exact (hf1 y).mp (subset_closure hy)

/-- Compact support away from the zero frequency leaves finitely many
nonzero angular indices at every positive integral scale. -/
lemma cylinder_cutoff_finite_indices {χ : ℝ × UnitAddCircle → ℝ}
    (hc : HasCompactSupport χ) (hzero : ∀ a, χ (0,a) = 0) (n : ℕ) (hn : 0 < n) :
    ∃ S : Finset ℤ, (0:ℤ) ∉ S ∧ ∀ j ∉ S, ∀ a, χ ((j:ℝ)/n,a) = 0 := by
  classical
  obtain ⟨R,hR⟩ := (hc.image continuous_fst).isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt ((n:ℝ)*R)
  refine ⟨(Finset.Icc (-(N:ℤ)) N).erase 0,Finset.notMem_erase _ _,?_⟩
  intro j hj a
  by_contra ha
  have hj0 : j ≠ 0 := by intro hz; subst j; simp [hzero] at ha
  have hb : |(j:ℝ)/(n:ℝ)| ≤ R :=
    hR _ (mem_image_of_mem Prod.fst (subset_tsupport χ ha))
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [abs_div,abs_of_pos hn'] at hb
  have hjN : |(j:ℝ)| < N := ((div_le_iff₀ hn').mp hb).trans_lt (by nlinarith)
  apply hj
  rw [Finset.mem_erase,Finset.mem_Icc]
  exact ⟨hj0,by exact_mod_cast (abs_le.mp hjN.le)⟩

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Jitter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cumulative distribution, smooth quantile inverse, and positive smooth neutral jitter laws. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators
open MeasureTheory Set Filter
open scoped Topology FourierTransform
open MeasureTheory Set Filter Asymptotics

/-! Approximation of a positive smooth law.
The cumulative distribution and its local smooth inverse are constructed from
the positive smooth density, not assumed as an additional hypothesis. -/
noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology
namespace ThreeTorus

lemma contDiff_periodize {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hc : HasCompactSupport f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (periodize f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R + |x| + 1)
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) N
  have hs : ∀ᶠ y in 𝓝 x, support (fun k : ℤ => f (y+k)) ⊆ (s : Set ℤ) := by
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
    intro k hk
    have hy' : |y| < |x| + 1 := by
      have := abs_add_le (y-x) x
      have hy'' : |y-x| < 1 := hy
      simpa only [sub_add_cancel] using this.trans_lt (by linarith : |y-x|+|x| < |x|+1)
    have hk' : |y+(k : ℝ)| ≤ R := by
      simpa only [Real.norm_eq_abs] using hR (y+k) (subset_tsupport f hk)
    have hz : |(k : ℝ)| < (N : ℝ) := calc
      |(k : ℝ)| = |(y+k)-y| := by congr 1; ring
      _ ≤ |y+k| + |y| := abs_sub _ _
      _ < ↑N := by linarith
    have hh : -(N : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ ↑N := (abs_le.mp hz.le)
    show k ∈ Finset.Icc (-(N : ℤ)) N
    rw [Finset.mem_Icc]
    exact_mod_cast hh
  have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∑ k ∈ s, f (y+k)) :=
    ContDiff.sum fun k _ => hf.comp (contDiff_id.add contDiff_const)
  apply hh.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hs] with y hy
  exact finsum_eq_sum_of_support_subset _ hy

lemma periodize_eq_on_unit {f : ℝ → ℝ} (hs : support f ⊆ Ioo (0 : ℝ) 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : periodize f x = f x := by
  unfold periodize
  convert finsum_eq_single (fun k : ℤ => f (x+k)) 0 ?_ using 1
  · simp
  · intro k hk
    by_contra hn
    have hh := hs (show x+(k : ℝ) ∈ support f from hn)
    have h1 : (-1 : ℝ) < (k : ℝ) := by linarith [hx.2, hh.1]
    have h2 : (k : ℝ) < (1 : ℝ) := by linarith [hx.1, hh.2]
    have h1' : (-1 : ℤ) < k := by exact_mod_cast h1
    have h2' : k < (1 : ℤ) := by exact_mod_cast h2
    omega

lemma periodize_eq_fract {f : ℝ → ℝ} (hs : support f ⊆ Ioo (0 : ℝ) 1) (x : ℝ) :
    periodize f x = f (Int.fract x) := by
  have hh := (periodize_periodic f).sub_zsmul_eq (x := x) ⌊x⌋
  have he : periodize f (Int.fract x) = periodize f x := by
    simpa only [Int.fract, zsmul_eq_mul, mul_one] using hh
  rw [← he]
  exact periodize_eq_on_unit hs ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

lemma lawPsi_smooth {δ : ℝ} (c : LawCutoffs δ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lawPsi c) :=
  contDiff_periodize c.ψ_smooth c.ψ_compact

lemma lawPsi_eq {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) : lawPsi c a = c.ψ a := by
  apply periodize_eq_on_unit _ ha
  intro x hx
  have hh := c.ψ_support (subset_tsupport _ hx)
  exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

lemma lawPsi_bounds {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (a : ℝ) :
    0 ≤ lawPsi c a ∧ lawPsi c a ≤ 1 := by
  have hs : support c.ψ ⊆ Ioo (0 : ℝ) 1 := fun x hx => by
    have hh := c.ψ_support (subset_tsupport _ hx)
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  rw [lawPsi, periodize_eq_fract hs]
  exact ⟨c.ψ_nonneg _, c.ψ_le_one _⟩

lemma integral_cutoff_lower {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8) :
    1-4*δ ≤ ∫ a in Ioo (0 : ℝ) 1, c.ψ a^2 := by
  have hs : HasCompactSupport (fun a : ℝ => c.ψ a^2) :=
    c.ψ_compact.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have hi : Integrable (fun a : ℝ => c.ψ a^2) :=
    (c.ψ_smooth.continuous.pow 2).integrable_of_hasCompactSupport hs
  calc
    1-4*δ = ∫ a in Icc (2*δ) (1-2*δ), (1 : ℝ) := by
      simp only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, mul_one,
        Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1-2*δ-2*δ)]
      ring
    _ = ∫ a in Icc (2*δ) (1-2*δ), c.ψ a^2 := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro a ha
      change 1 = c.ψ a^2
      rw [c.ψ_one a ha, one_pow]
    _ ≤ ∫ a in Ioo (0 : ℝ) 1, c.ψ a^2 := by
      apply setIntegral_mono_set hi.integrableOn (Eventually.of_forall fun _ => sq_nonneg _)
      exact Eventually.of_forall fun a ha => ⟨by linarith [ha.1], by linarith [ha.2]⟩

lemma missing_cutoff_mass {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8) :
    (∫ a in Ioo (0 : ℝ) 1, (1-c.ψ a^2)) ≤ 4*δ := by
  have hs : HasCompactSupport (fun a : ℝ => c.ψ a^2) :=
    c.ψ_compact.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have hψ : Integrable (fun a : ℝ => c.ψ a^2) :=
    (c.ψ_smooth.continuous.pow 2).integrable_of_hasCompactSupport hs
  have hunit : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo (0 : ℝ) 1) :=
    continuous_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [integral_sub hunit hψ.integrableOn]
  have he : (∫ a in Ioo (0 : ℝ) 1, (1 : ℝ)) = 1 := by simp
  rw [he]
  linarith [integral_cutoff_lower c hδ hδ']

end ThreeTorus

namespace ThreeTorus
open Set Function MeasureTheory
open scoped Topology

lemma neutralJitterReal_smooth {δ : ℝ} (c : LawCutoffs δ) (L β : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (neutralJitterReal c L β) :=
  contDiff_periodize (c.ξ_smooth.mul (contDiff_const.mul contDiff_id |>.add contDiff_const))
    c.ξ_compact.mul_right

lemma neutralJitterReal_affine {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (L β : ℝ)
    {a : ℝ} (ha : a ∈ Icc δ (1-δ)) : neutralJitterReal c L β a = L*a+β := by
  unfold neutralJitterReal
  rw [periodize_eq_on_unit (fun x hx => c.ξ_support (subset_tsupport _ (left_ne_zero_of_mul hx)))
    (show a ∈ Icc (0:ℝ) 1 from ⟨by linarith [ha.1],by linarith [ha.2]⟩),c.ξ_one a ha,one_mul]

lemma neutralJitterReal_deriv {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (L β : ℝ)
    {a : ℝ} (ha : a ∈ Ioo δ (1-δ)) : deriv (neutralJitterReal c L β) a = L := by
  have he : neutralJitterReal c L β =ᶠ[𝓝 a] (fun x => L*x+β) := by
    filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
    exact neutralJitterReal_affine c hδ L β ⟨hb.1.le,hb.2.le⟩
  rw [he.deriv_eq]
  simp

lemma neutralJitter_coe {δ : ℝ} (c : LawCutoffs δ) (L β a : ℝ) :
    neutralJitter c L β (a : UnitAddCircle) = neutralJitterReal c L β a := rfl

lemma continuous_neutralJitter {δ : ℝ} (c : LawCutoffs δ) (L β : ℝ) :
    Continuous (neutralJitter c L β) :=
by
  apply Continuous.quotient_lift
  exact (neutralJitterReal_smooth c L β).continuous

lemma neutralCircleCutoff_coe {δ : ℝ} (c : LawCutoffs δ) (a : ℝ) :
    neutralCircleCutoff c (a : UnitAddCircle) = lawPsi c a := rfl

lemma continuous_neutralCircleCutoff {δ : ℝ} (c : LawCutoffs δ) :
    Continuous (neutralCircleCutoff c) :=
by
  apply Continuous.quotient_lift
  exact (lawPsi_smooth c).continuous

lemma neutralCircleCutoff_bounds {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ)
    (a : UnitAddCircle) : 0 ≤ neutralCircleCutoff c a ∧ neutralCircleCutoff c a ≤ 1 := by
  induction a using Quotient.inductionOn with
  | h a => exact lawPsi_bounds c hδ a

lemma neutralCircleCutoff_error {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8) :
    (∫ a, (1-neutralCircleCutoff c a^2) ∂AddCircle.haarAddCircle) ≤ 4*δ := by
  have he := AddCircle.integral_preimage 1 0 (fun a => (1-neutralCircleCutoff c a^2))
  simp only [zero_add,AddCircle.volume_eq_smul_haarAddCircle,ENNReal.ofReal_one,one_smul] at he
  rw [← he]
  change (∫ a in Ioc (0:ℝ) 1, (1-lawPsi c a^2)) ≤ 4*δ
  have hi : (∫ a in Ioc (0:ℝ) 1, (1-lawPsi c a^2)) =
      ∫ a in Ioo (0:ℝ) 1, (1-c.ψ a^2) := by
    rw [integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro a ha
    dsimp only
    rw [lawPsi_eq c hδ ⟨ha.1.le,ha.2.le⟩]
  rw [hi]
  exact missing_cutoff_mass c hδ hδ'

end ThreeTorus

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Fourier passage coefficients, branch Jacobians, rounding removal, and integrated stationary mass. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

namespace ThreeTorus

lemma continuous_fourierCoeff_param {Ω : Type*} [TopologicalSpace Ω]
    [FirstCountableTopology Ω] [LocallyCompactSpace Ω]
    {f : Ω → UnitAddCircle → ℂ} (hf : Continuous f.uncurry) (j : ℤ) :
    Continuous (fun a => fourierCoeff (f a) j) := by
  have hh : Continuous (fun p : Ω × UnitAddCircle => fourier (-j) p.2*f p.1 p.2) :=
    ((fourier (-j)).continuous.comp continuous_snd).mul hf
  simpa only [fourierCoeff,smul_eq_mul,setIntegral_univ] using
    (continuous_parametric_integral_of_continuous (μ := AddCircle.haarAddCircle)
      (f := fun a θ => fourier (-j) θ*f a θ) hh isCompact_univ)

lemma continuous_passageFourierInput {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hH : Continuous H) (hA : Continuous A) :
    Continuous (passageFourierInput m H A).uncurry := by
  exact (hA.comp continuous_swap).mul ((fourier m).continuous.comp (hH.comp continuous_snd))

lemma continuous_exactPassageCoeff {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hH : Continuous H) (hA : Continuous A) (j : ℤ) :
    Continuous (exactPassageCoeff m H A j) :=
  continuous_fourierCoeff_param (continuous_passageFourierInput hH hA) j

end ThreeTorus

namespace ThreeTorus

open Function

lemma branchDensity_on {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hg : ∀ x ∈ I, g (J x) = x) {x : ℝ} (hx : x ∈ I) :
    branchDensity I J g D q (J x) = q x/|D x| := by
  simp only [branchDensity,indicator_of_mem (mem_image_of_mem J hx),hg x hx]

lemma contDiffAt_invFunOn_of_deriv_ne_zero {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hIo : IsOpen I) (hinj : InjOn J I) {x d : ℝ} (hx : x ∈ I)
    (hd : HasDerivAt J d x) (hd0 : d ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (invFunOn J I) (J x) := by
  let e := hJ.contDiffAt.toOpenPartialHomeomorph J (hd.hasFDerivAt_equiv hd0) (by simp)
  have he : (e : ℝ → ℝ) = J := rfl
  have hxs : x ∈ e.source := hJ.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hd.hasFDerivAt_equiv hd0) (by simp)
  have hyt : J x ∈ e.target := by simpa only [he] using e.map_source hxs
  have hix : e.symm (J x) = x := by simpa only [he] using e.left_inv hxs
  have hi : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) e.symm (J x) := by
    apply e.contDiffAt_symm_deriv hd0 hyt
    · simpa only [he,hix] using hd
    · simpa only [he,hix] using hJ.contDiffAt (x := x)
  have hnear : ∀ᶠ y in 𝓝 (J x), e.symm y ∈ I := by
    apply hi.continuousAt.eventually
    change I ∈ 𝓝 (e.symm (J x))
    rw [hix]
    exact hIo.mem_nhds hx
  apply hi.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hyt,hnear] with y hy hyI
  have hr : J (e.symm y) = y := by simpa only [he] using e.right_inv hy
  have hp := invFunOn_pos (show y ∈ J '' I from ⟨e.symm y,hyI,hr⟩)
  exact hinj hp.1 hyI (hp.2.trans hr.symm)

lemma isOpen_image_of_deriv_ne_zero {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hIo : IsOpen I) (hd : ∀ x ∈ I, deriv J x ≠ 0) : IsOpen (J '' I) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x,hx,rfl⟩
  have hdx := (hJ.differentiable (by simp) x).hasDerivAt
  let e := hJ.contDiffAt.toOpenPartialHomeomorph J (hdx.hasFDerivAt_equiv (hd x hx)) (by simp)
  have he : (e : ℝ → ℝ) = J := rfl
  have hxs : x ∈ e.source := hJ.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hdx.hasFDerivAt_equiv (hd x hx)) (by simp)
  have hyt : J x ∈ e.target := by simpa only [he] using e.map_source hxs
  have hix : e.symm (J x) = x := by simpa only [he] using e.left_inv hxs
  have hnear : ∀ᶠ y in 𝓝 (J x), e.symm y ∈ I := by
    apply (e.continuousAt_symm hyt).eventually
    change I ∈ 𝓝 (e.symm (J x))
    rw [hix]
    exact hIo.mem_nhds hx
  filter_upwards [e.open_target.mem_nhds hyt,hnear] with y hy hyI
  exact ⟨e.symm y,hyI,by simpa only [he] using e.right_inv hy⟩

lemma branchFamily_congr_branch {Ω : Type*} {C I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ}
    (hIC : I ⊆ C) (hinj : InjOn J C) (hs : support F ⊆ I ×ˢ univ) :
    branchFamily C J F = branchFamily I J F := by
  classical
  funext p
  have him : J '' I ⊆ J '' C := image_mono hIC
  by_cases hp : p.1 ∈ J '' C
  · have hc := invFunOn_pos hp
    by_cases hpi : p.1 ∈ J '' I
    · have hi := invFunOn_pos hpi
      have hinv : invFunOn J C p.1 = invFunOn J I p.1 :=
        hinj hc.1 (hIC hi.1) (hc.2.trans hi.2.symm)
      simp [branchFamily,hp,hpi,hinv]
    · have hz : F (invFunOn J C p.1,p.2) = 0 := by
        by_contra hn
        exact hpi ⟨_, (hs hn).1, hc.2⟩
      simp [branchFamily,hp,hpi,hz]
  · have hpi : p.1 ∉ J '' I := fun h => hp (him h)
    simp [branchFamily,hp,hpi]

open scoped NNReal

end ThreeTorus

namespace ThreeTorus
open Function
open scoped ComplexConjugate

lemma exactPassageCoeff_neg (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (j : ℤ) (a : UnitAddCircle) :
    exactPassageCoeff (-m) H (fun x => conj (A x)) j a =
      conj (exactPassageCoeff m H A (-j) a) := by
  unfold exactPassageCoeff fourierCoeff passageFourierInput
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with θ
  simp only [smul_eq_mul, neg_neg, map_mul, fourier_neg]

end ThreeTorus

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unfolded and folded retained densities, branch kernels, residue sampling, and spectral limits. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ThreeTorus

lemma circle_integral_lift (o : ℝ) (q : UnitAddCircle → ℝ) :
    (∫ x, circleDensityLift o q x) = ∫ a, q a ∂AddCircle.haarAddCircle := by
  rw [circleDensityLift,integral_indicator measurableSet_Ioc]
  have h := AddCircle.integral_preimage 1 o q
  simpa [AddCircle.volume_eq_smul_haarAddCircle] using h

lemma integrable_circleDensityLift {q : UnitAddCircle → ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (o : ℝ) :
    Integrable (circleDensityLift o q) := by
  have hmp : MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
      (volume.restrict (Ioc o (o+1))) AddCircle.haarAddCircle := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 o
  have hi : IntegrableOn (fun x : ℝ => q (x : UnitAddCircle)) (Ioc o (o+1)) :=
    (hmp.integrable_comp hq.aestronglyMeasurable).2 hq
  exact hi.integrable_indicator measurableSet_Ioc

/-- Lifting a circle density on one period commutes with every measurable
spectral pushforward. This includes the actual jitter, not just polynomial tests. -/
lemma circleDensityLift_pushforward {Y : Type*} [MeasurableSpace Y]
    {q : UnitAddCircle → ℝ} (hq : Integrable q AddCircle.haarAddCircle)
    {T : UnitAddCircle → Y} (hT : Measurable T) (o : ℝ) :
    ((volume : Measure ℝ).withDensityᵥ (circleDensityLift o q)).map
      (fun x : ℝ => T (x : UnitAddCircle)) =
    (AddCircle.haarAddCircle.withDensityᵥ q).map T := by
  have hTm : Measurable (fun x : ℝ => T (x : UnitAddCircle)) := hT.comp AddCircle.measurable_mk'
  ext s hs
  rw [VectorMeasure.map_apply _ hTm hs,VectorMeasure.map_apply _ hT hs,
    withDensityᵥ_apply (integrable_circleDensityLift hq o) (hTm hs),
    withDensityᵥ_apply hq (hT hs)]
  rw [← integral_indicator (hTm hs),← integral_indicator (hT hs)]
  rw [← circle_integral_lift o ((T ⁻¹' s).indicator q)]
  congr 1
  funext x
  by_cases hx : x ∈ Ioc o (o+1) <;> by_cases hxs : T (x : UnitAddCircle) ∈ s <;>
    simp [circleDensityLift,hx,hxs]

lemma circleDensityLift_eq {q : UnitAddCircle → ℝ} {q₀ : ℝ → ℝ} {o : ℝ}
    (he : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hs : Function.support q₀ ⊆ Ioc o (o+1)) : circleDensityLift o q = q₀ := by
  funext x
  by_cases hx : x ∈ Ioc o (o+1)
  · simp [circleDensityLift,hx,he x hx]
  · have hzero : q₀ x = 0 := by by_contra hn; exact hx (hs hn)
    simp [circleDensityLift,hx,hzero]

lemma integrable_branchDensity {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : IntegrableOn q I) : Integrable (branchDensity I J g D q) := by
  have he : IntegrableOn (branchDensity I J g D q) (J '' I) := by
    rw [integrableOn_image_iff_integrableOn_abs_deriv_smul hI hJ hinj]
    apply hq.congr (ae_restrict_of_forall_mem hI (fun x hx => ?_))
    rw [smul_eq_mul,branchDensity_on hg hx]
    field_simp [abs_ne_zero.mpr (hD x hx)]
  have hs : (J '' I).indicator (branchDensity I J g D q) = branchDensity I J g D q := by
    funext y
    by_cases hy : y ∈ J '' I
    · exact indicator_of_mem hy _
    · simp [hy,branchDensity]
  simpa only [hs] using he.integrable_indicator himage

/-- Exact pushforward of the old squared coefficient on a branch. The only
inverse assumptions are the ordinary left-inverse identities on that branch. -/
lemma branchDensity_pushforward {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I)) (hJm : Measurable J)
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : Integrable q) (hqs : Function.support q ⊆ I) :
    ((volume : Measure ℝ).withDensityᵥ q).map J =
      (volume : Measure ℝ).withDensityᵥ (branchDensity I J g D q) := by
  have hK := integrable_branchDensity hI himage hJ hinj hg hD hq.integrableOn
  ext s hs
  rw [VectorMeasure.map_apply _ hJm hs,withDensityᵥ_apply hq (hJm hs),withDensityᵥ_apply hK hs]
  rw [← integral_indicator (hJm hs),← integral_indicator hs]
  have hleft : (∫ x, (J ⁻¹' s).indicator q x) = ∫ x in I, (J ⁻¹' s).indicator q x := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hqx : q x = 0 := by
      by_contra hh
      exact hx (hqs hh)
    by_cases hxs : x ∈ J ⁻¹' s <;> simp [hxs,hqx]
  have hright : (∫ y, s.indicator (branchDensity I J g D q) y) =
      ∫ y in J '' I, s.indicator (branchDensity I J g D q) y := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    by_cases hys : y ∈ s <;> simp [hys,branchDensity,hy]
  rw [hleft,hright,integral_image_eq_integral_abs_deriv_smul hI hJ hinj]
  apply setIntegral_congr_fun hI
  intro x hx
  dsimp only
  rw [smul_eq_mul]
  by_cases hxs : J x ∈ s
  · rw [indicator_of_mem (show x ∈ J ⁻¹' s from hxs),indicator_of_mem hxs,branchDensity_on hg hx]
    field_simp [abs_ne_zero.mpr (hD x hx)]
  · rw [indicator_of_notMem (show x ∉ J ⁻¹' s from hxs),indicator_of_notMem hxs,mul_zero]

lemma density_map_congr_support {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {f : X → ℝ} (hf : Integrable f μ)
    {T₁ T₂ : X → Y} (h₁ : Measurable T₁) (h₂ : Measurable T₂)
    (he : ∀ x, f x ≠ 0 → T₁ x = T₂ x) :
    (μ.withDensityᵥ f).map T₁ = (μ.withDensityᵥ f).map T₂ := by
  classical
  ext s hs
  rw [VectorMeasure.map_apply _ h₁ hs,VectorMeasure.map_apply _ h₂ hs,
    withDensityᵥ_apply hf (h₁ hs),withDensityᵥ_apply hf (h₂ hs),
    ← integral_indicator (h₁ hs),← integral_indicator (h₂ hs)]
  congr 1
  funext x
  change (if T₁ x ∈ s then f x else 0) = (if T₂ x ∈ s then f x else 0)
  by_cases hx : f x = 0
  · simp [hx]
  · rw [he x hx]

/-- The branch-Jacobian formula on the actual circle. The global periodic
jitter need not be injective; only the good arc bearing the weight is used. -/
lemma circle_branch_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ g D : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : Function.support q₀ ⊆ Ioc o (o+1)) (hqs : Function.support q₀ ⊆ I)
    (hj : Measurable J) (hj₀ : Measurable J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hI : MeasurableSet I) (himage : MeasurableSet (J₀ '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J₀ (D x) I x) (hinj : InjOn J₀ I)
    (hg : ∀ x ∈ I, g (J₀ x) = x) (hD : ∀ x ∈ I, D x ≠ 0) :
    (AddCircle.haarAddCircle.withDensityᵥ q).map J =
      (volume : Measure ℝ).withDensityᵥ (branchDensity I J₀ g D q₀) := by
  have hlift := circleDensityLift_eq hq₀ hq₀s
  have hi : Integrable q₀ := by rw [← hlift]; exact integrable_circleDensityLift hq o
  rw [← circleDensityLift_pushforward hq hj o,hlift]
  rw [density_map_congr_support (T₁ := fun x : ℝ => J (x : UnitAddCircle)) hi (hj.comp AddCircle.measurable_mk') hj₀
    (fun x hx => hJe x (hqs hx))]
  exact branchDensity_pushforward hI himage hj₀ hJ hinj hg hD hi hqs

/-- Total variation contracts under the actual temporal-frequency pushforward.
The real L¹ normalization has no factor 1/2. -/
lemma l1_pushforward_contraction {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → ℝ} {g : Y → ℝ} {T : X → Y}
    (hf : Integrable f μ) (hg : Integrable g ν) (hT : Measurable T)
    (hmap : (μ.withDensityᵥ f).map T = ν.withDensityᵥ g) :
    (∫ y, |g y| ∂ν) ≤ ∫ x, |f x| ∂μ := by
  have hv := MeasureTheory.VectorMeasure.variation_map_le (μ := μ.withDensityᵥ f) (φ := T)
  rw [hmap,Measure.variation_withDensityᵥ hg,Measure.variation_withDensityᵥ hf] at hv
  have hh := hv univ
  rw [Measure.map_apply hT MeasurableSet.univ] at hh
  simp only [preimage_univ,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at hh
  have he (z : ℝ) : ‖z‖ₑ = ENNReal.ofReal |z| := Real.enorm_eq_ofReal_abs z
  simp_rw [he] at hh
  rw [← ofReal_integral_eq_lintegral_ofReal hg.abs (Filter.Eventually.of_forall (fun _ => abs_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hf.abs (Filter.Eventually.of_forall (fun _ => abs_nonneg _))] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun _ => abs_nonneg _))).mp hh

lemma l1_pushforward_difference {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f₁ f₂ : X → ℝ} {g₁ g₂ : Y → ℝ} {T : X → Y}
    (hf₁ : Integrable f₁ μ) (hf₂ : Integrable f₂ μ)
    (hg₁ : Integrable g₁ ν) (hg₂ : Integrable g₂ ν) (hT : Measurable T)
    (h₁ : (μ.withDensityᵥ f₁).map T = ν.withDensityᵥ g₁)
    (h₂ : (μ.withDensityᵥ f₂).map T = ν.withDensityᵥ g₂) :
    (∫ y, |g₁ y-g₂ y| ∂ν) ≤ ∫ x, |f₁ x-f₂ x| ∂μ := by
  apply l1_pushforward_contraction (hf₁.sub hf₂) (hg₁.sub hg₂) hT
  rw [withDensityᵥ_sub hf₁ hf₂,withDensityᵥ_sub hg₁ hg₂]
  have he := map_sub (MeasureTheory.VectorMeasure.mapGm T) (μ.withDensityᵥ f₁) (μ.withDensityᵥ f₂)
  change (μ.withDensityᵥ f₁-μ.withDensityᵥ f₂).map T =
    (μ.withDensityᵥ f₁).map T-(μ.withDensityᵥ f₂).map T at he
  rw [he,h₁,h₂]

/-- Exact Jacobian cancellation in the unfolded output frequency t=(j+y)/N. -/
lemma temporalFrequency_pushforward {q : ℝ → ℝ} (hq : Integrable q)
    {n : ℝ} (hn : 0 < n) (j : ℝ) :
    ((volume : Measure ℝ).withDensityᵥ (fun y => n⁻¹*q y)).map (fun y => (j+y)/n) =
      (volume : Measure ℝ).withDensityᵥ (fun t => q (n*t-j)) := by
  have hmap : Measurable (fun y : ℝ => (j+y)/n) := by fun_prop
  have hq' : Integrable (fun t => q (n*t-j)) := by
    simpa only [sub_eq_add_neg] using
      (integrable_comp_mul_left_iff (fun x => q (x+ -j)) hn.ne').2 (hq.comp_add_right (-j))
  ext s hs
  rw [VectorMeasure.map_apply _ hmap hs,withDensityᵥ_apply (hq.const_mul n⁻¹) (hmap hs),
    withDensityᵥ_apply hq' hs,integral_const_mul]
  let F : ℝ → ℝ := ((fun y : ℝ => (j+y)/n) ⁻¹' s).indicator q
  have he : (fun t => F (n*t-j)) = s.indicator (fun t => q (n*t-j)) := by
    funext t
    by_cases ht : t ∈ s <;> simp [F,ht,hn.ne']
  rw [← integral_indicator (hmap hs),← integral_indicator hs,← he]
  change n⁻¹*(∫ y, F y) = ∫ t, F (n*t-j)
  rw [Measure.integral_comp_mul_left (fun x => F (x-j)) n,integral_sub_right_eq_self]
  simp only [smul_eq_mul,abs_of_pos (inv_pos.mpr hn)]

/-- Pushforward through a fixed smooth jitter followed by the output affine frequency.
This is the exact (not weak or asymptotic) density appearing in the passage. -/
lemma temporalFrequency_pushforward_comp {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {W : X → ℝ} {q : ℝ → ℝ} {J : X → ℝ}
    (hW : Integrable W μ) (hq : Integrable q) (hJ : Measurable J)
    (hpush : (μ.withDensityᵥ W).map J = (volume : Measure ℝ).withDensityᵥ q)
    {n : ℝ} (hn : 0 < n) (j : ℝ) :
    (μ.withDensityᵥ (fun a => n⁻¹*W a)).map (fun a => (j+J a)/n) =
      (volume : Measure ℝ).withDensityᵥ (fun t => q (n*t-j)) := by
  have haf : Measurable (fun y : ℝ => (j+y)/n) := by fun_prop
  have hcomp (v : VectorMeasure X ℝ) :
      v.map (fun a => (j+J a)/n) = (v.map J).map (fun y : ℝ => (j+y)/n) := by
    ext s hs
    have hcompm : Measurable (fun a => (j+J a)/n) := haf.comp hJ
    rw [VectorMeasure.map_apply _ hcompm hs,
      VectorMeasure.map_apply _ haf hs,VectorMeasure.map_apply _ hJ (haf hs)]
    rfl
  rw [hcomp]
  have he : μ.withDensityᵥ (fun a => n⁻¹*W a) = n⁻¹ • μ.withDensityᵥ W := by
    ext s hs
    rw [withDensityᵥ_apply (hW.const_mul _) hs,smul_apply,withDensityᵥ_apply hW hs,
      integral_const_mul,smul_eq_mul]
  have heq : (volume : Measure ℝ).withDensityᵥ (fun y => n⁻¹*q y) =
      n⁻¹ • (volume : Measure ℝ).withDensityᵥ q := by
    ext s hs
    rw [withDensityᵥ_apply (hq.const_mul _) hs,smul_apply,withDensityᵥ_apply hq hs,
      integral_const_mul,smul_eq_mul]
  rw [he,VectorMeasure.map_smul,hpush,← heq]
  exact temporalFrequency_pushforward hq hn j

lemma scaledBranchKernel_eq {I : Set ℝ} (J g D q : ℝ → ℝ) {s : ℝ} (hs : s ≠ 0) (y : ℝ) :
    branchDensity I (fun x => s*J x) (fun y => g (y/s)) (fun x => s*D x) q y =
      scaledBranchKernel I J g D q s y := by
  classical
  have he : y ∈ (fun x => s*J x) '' I ↔ y/s ∈ J '' I := by
    constructor
    · rintro ⟨x,hx,hxy⟩
      exact ⟨x,hx,by rw [← hxy]; field_simp⟩
    · rintro ⟨x,hx,hxy⟩
      exact ⟨x,hx,by change s*J x = y; rw [hxy]; field_simp⟩
  by_cases hy : y/s ∈ J '' I
  · simp only [branchDensity,scaledBranchKernel,indicator_of_mem hy,
      indicator_of_mem (he.mpr hy),abs_mul]
    ring
  · simp only [branchDensity,scaledBranchKernel,indicator_of_notMem hy,
      indicator_of_notMem (fun h => hy (he.mp h)),mul_zero]

lemma integrable_scaledBranchKernel {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hq : Integrable (branchDensity I J g D q)) {s : ℝ} (hs : s ≠ 0) :
    Integrable (scaledBranchKernel I J g D q s) :=
  ((integrable_comp_div_iff _ hs).2 hq).const_mul _

/-- The exact branch kernel in the new temporal coordinate, on the torus.
Only the good arc need be injective, as in the geometric passage. -/
lemma circle_mode_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ g D : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : Function.support q₀ ⊆ Ioc o (o+1)) (hqs : Function.support q₀ ⊆ I)
    (hj : Measurable J) (hj₀ : Measurable J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hI : MeasurableSet I) (himage : MeasurableSet (J₀ '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J₀ (D x) I x) (hinj : InjOn J₀ I)
    (hg : ∀ x ∈ I, g (J₀ x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    {s n : ℝ} (hs : s ≠ 0) (hn : 0 < n) (j : ℝ) :
    (AddCircle.haarAddCircle.withDensityᵥ (fun a => n⁻¹*q a)).map
        (fun a => (j+s*J a)/n) =
      (volume : Measure ℝ).withDensityᵥ
        (fun t => scaledBranchKernel I J₀ g D q₀ s (n*t-j)) := by
  have hqi : Integrable q₀ := by
    rw [← circleDensityLift_eq hq₀ hq₀s]
    exact integrable_circleDensityLift hq o
  have hK := integrable_branchDensity hI himage hJ hinj hg hD hqi.integrableOn
  have hsim : MeasurableSet ((fun x => s*J₀ x) '' I) := by
    have he : (fun x => s*J₀ x) '' I = (fun y : ℝ => s*y) '' (J₀ '' I) := by
      rw [image_image]
    rw [he]
    exact (Homeomorph.mulLeft₀ s hs).measurableEmbedding.measurableSet_image.mpr himage
  have hp := circle_branch_pushforward (g := fun y => g (y/s)) hq hq₀ hq₀s hqs
    (measurable_const.mul hj) (measurable_const.mul hj₀)
    (fun x hx => congrArg (fun y => s*y) (hJe x hx)) hI hsim
    (fun x hx => (hJ x hx).const_mul s)
    (fun x hx y hy he => hinj hx hy (mul_left_cancel₀ hs he))
    (fun x hx => show g (s*J₀ x/s) = x by simpa [hs] using hg x hx)
    (fun x hx => mul_ne_zero hs (hD x hx))
  have he : branchDensity I (fun x => s*J₀ x) (fun y => g (y/s)) (fun x => s*D x) q₀ =
      scaledBranchKernel I J₀ g D q₀ s := funext (scaledBranchKernel_eq _ _ _ _ hs)
  change (AddCircle.haarAddCircle.withDensityᵥ q).map (fun a => s*J a) =
    (volume : Measure ℝ).withDensityᵥ
      (branchDensity I (fun x => s*J₀ x) (fun y => g (y/s)) (fun x => s*D x) q₀) at hp
  rw [he] at hp
  exact temporalFrequency_pushforward_comp hq (integrable_scaledBranchKernel hK hs)
    (measurable_const.mul hj) hp hn j

lemma integrable_unfoldedModeDensity {I : Set ℝ} {J g D q₀ : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : Integrable q₀) {n j : ℝ} (hn : 0 < n) (hj : j ≠ 0) :
    Integrable (unfoldedModeDensity I J g D q₀ n j) := by
  have hi := integrable_scaledBranchKernel
    (integrable_branchDensity hI himage hJ hinj hg hD (hq.const_mul n).integrableOn)
    (div_ne_zero hj hn.ne')
  change Integrable (fun t => scaledBranchKernel I J g D (fun a => n*q₀ a) (j/n) (n*t-j))
  simpa only [sub_eq_add_neg] using
    (integrable_comp_mul_left_iff (fun x =>
      scaledBranchKernel I J g D (fun a => n*q₀ a) (j/n) (x+ -j)) hn.ne').2
      (hi.comp_add_right (-j))

/-- Exact density of an actual circle mode before any stationary approximation. -/
lemma unfoldedModeDensity_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ g D : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : Function.support q₀ ⊆ Ioc o (o+1)) (hqs : Function.support q₀ ⊆ I)
    (hj : Measurable J) (hj₀ : Measurable J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hI : MeasurableSet I) (himage : MeasurableSet (J₀ '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J₀ (D x) I x) (hinj : InjOn J₀ I)
    (hg : ∀ x ∈ I, g (J₀ x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    {n j : ℝ} (hn : 0 < n) (hjn : j ≠ 0) :
    (AddCircle.haarAddCircle.withDensityᵥ q).map
        (fun a => (j+(j/n)*J a)/n) =
      (volume : Measure ℝ).withDensityᵥ (unfoldedModeDensity I J₀ g D q₀ n j) := by
  have hsupp (L : Set ℝ) (hh : Function.support q₀ ⊆ L) :
      Function.support (fun a => n*q₀ a) ⊆ L := by
    intro x hx
    apply hh
    intro hz
    exact hx (by simp only [hz,mul_zero])
  have hp := circle_mode_pushforward (q := fun a => n*q a) (q₀ := fun a => n*q₀ a)
    (s := j/n) (hq.const_mul n) (fun x hx => congrArg (fun y => n*y) (hq₀ x hx))
    (hsupp _ hq₀s) (hsupp _ hqs) hj hj₀ hJe hI himage hJ hinj hg hD
    (div_ne_zero hjn hn.ne') hn j
  change _ = (volume : Measure ℝ).withDensityᵥ
    (fun t => scaledBranchKernel I J₀ g D (fun a => n*q₀ a) (j/n) (n*t-j))
  simpa only [← mul_assoc,inv_mul_cancel₀ hn.ne',one_mul] using hp

end ThreeTorus

noncomputable section
open Set Function Filter
open scoped Topology NNReal
namespace ThreeTorus

lemma support_branchKernel_subset {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ} :
    support (branchKernel I J F) ⊆ (fun p : ℝ × ℝ => (J p.1,p.2)) '' tsupport F := by
  rintro ⟨s,a⟩ hh
  have hs : s ∈ J '' I := by
    by_contra hn
    exact hh (by simp [branchKernel,hn])
  have hp := invFunOn_pos hs
  refine ⟨(invFunOn J I s,a),subset_tsupport F ?_,?_⟩
  · intro hz
    exact hh (by simp [branchKernel,hs,hz])
  · simp only [hp.2]

lemma branchKernel_compact {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ}
    (hJ : Continuous J) (hc : HasCompactSupport F) : HasCompactSupport (branchKernel I J F) := by
  apply HasCompactSupport.intro (hc.image (by fun_prop : Continuous (fun p : ℝ × ℝ => (J p.1,p.2))))
  intro p hp
  by_contra hn
  exact hp (support_branchKernel_subset hn)

lemma branchKernel_smooth {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ I ×ˢ univ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (branchKernel I J F) := by
  classical
  let g := invFunOn J I
  let M := (fun p : ℝ × ℝ => (J p.1,p.2)) '' tsupport F
  have hM : IsCompact M := hc.image (by fun_prop)
  have hzero {p : ℝ × ℝ} (hp : p ∉ M) : branchKernel I J F p = 0 :=
    notMem_support.mp (fun hn => hp (support_branchKernel_subset hn))
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) := by
    exact hJ.deriv' 
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ M
  · rcases hp with ⟨⟨x,a⟩,hx,rfl⟩
    have hxI : x ∈ I := (hs hx).1
    have hy : J x ∈ J '' I := mem_image_of_mem J hxI
    have hgi := contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hxI
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hxI)
    have hge : g (J x) = x := by
      exact hinj (invFunOn_pos hy).1 hxI (invFunOn_pos hy).2
    have hin : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (g p.1,p.2)) (J x,a) :=
      (hgi.comp (J x,a) contDiffAt_fst).prodMk contDiffAt_snd
    have hDen : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => |deriv J (g p.1)|) (J x,a) := by
      have hh : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × ℝ => deriv J (g p.1)) (J x,a) :=
        hD.contDiffAt.comp (J x,a) (hgi.comp (J x,a) contDiffAt_fst)
      exact (contDiffAt_abs (by simpa only [hge] using hd x hxI)).comp (J x,a) hh
    have hquot : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => F (g p.1,p.2) / |deriv J (g p.1)|) (J x,a) := by
      apply (hF.contDiffAt.comp _ hin).div hDen
      simpa only [hge] using abs_ne_zero.mpr (hd x hxI)
    apply hquot.congr_of_eventuallyEq
    have hnear : ∀ᶠ p : ℝ × ℝ in 𝓝 (J x,a), p.1 ∈ J '' I :=
      continuous_fst.continuousAt.eventually ((isOpen_image_of_deriv_ne_zero hJ hIo hd).mem_nhds hy)
    filter_upwards [hnear] with p hp
    simp only [branchKernel,ite_eq_left hp,g]
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hM.isClosed.isOpen_compl.mem_nhds hp] with q hq
    exact hzero hq

end ThreeTorus
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma stationaryWeight_family_of_branch {Ω : Type*} {C I : Set ℝ}
    {J : ℝ → ℝ} {A : Ω → ℝ → ℂ}
    (hIC : I ⊆ C) (hi : InjOn J C) (hs : ∀ a, support (A a) ⊆ I) :
    (fun p : ℝ × Ω => stationaryWeight C J (A p.2) p.1) =
      branchFamily I J (fun p : ℝ × Ω => ‖A p.2 p.1‖^2) := by
  have he (C : Set ℝ) :
      (fun p : ℝ × Ω => stationaryWeight C J (A p.2) p.1) =
      branchFamily C J (fun p : ℝ × Ω => ‖A p.2 p.1‖^2) := by
    funext p
    simp only [stationaryWeight,branchDensity,branchFamily]
    split_ifs with h <;> simp [h]
  rw [he]
  apply branchFamily_congr_branch hIC hi
  intro p hp
  refine ⟨hs p.2 ?_,mem_univ _⟩
  intro hz
  apply hp
  simp [hz]

/-- Smoothness of the actual old-frequency Jacobian, with a compactly
supported real lift of the old amplitude (including the new good-arc cutoff).
Both positive and negative angular indices are allowed by the injective branch. -/
lemma stationaryWeight_smooth_lift {C I : Set ℝ} {J : ℝ → ℝ} {B : ℝ × ℝ → ℂ}
    (hIC : I ⊆ C) (hi : InjOn J C)
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B) (hc : HasCompactSupport B)
    (hs : tsupport B ⊆ I ×ˢ univ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => stationaryWeight C J (fun x => B (x,p.2)) p.1) ∧
    HasCompactSupport (fun p : ℝ × ℝ => stationaryWeight C J (fun x => B (x,p.2)) p.1) := by
  let F : ℝ × ℝ → ℝ := fun p => ‖B p‖^2
  have hFt : tsupport F ⊆ tsupport B := by
    apply closure_mono
    intro p hp hz
    exact hp (by simp [F,show B p = 0 from hz])
  have hFc : HasCompactSupport F := hc.of_isClosed_subset (isClosed_tsupport F) hFt
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := hB.norm_sq (𝕜 := ℂ)
  have hA (a : ℝ) : support (fun x => B (x,a)) ⊆ I := by
    intro x hx
    exact (hs (subset_tsupport B hx)).1
  have he := stationaryWeight_family_of_branch (A := fun a x => B (x,a)) hIC hi hA
  rw [he]
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (branchKernel I J F) ∧
    HasCompactSupport (branchKernel I J F)
  exact ⟨branchKernel_smooth hJ hIo (hi.mono hIC) hd hF hFc (hFt.trans hs),
    branchKernel_compact hJ.continuous hFc⟩

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma retainedCircleWeight_integrable {ψ : UnitAddCircle → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {c : ℕ → ℤ → UnitAddCircle → ℂ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry) (hc : ∀ n j, Continuous (c n j))
    (n : ℕ) (j : ℤ) :
    Integrable (retainedCircleWeight ψ χ c n j) AddCircle.haarAddCircle := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  exact ((hψ.pow 2).mul ((hχ.comp (continuous_const.prodMk continuous_id)).pow 2)).mul
    ((hc n j).norm.pow 2)

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma scaled_speed_good_branch {V : ℝ → ℝ} {m : ℤ} {l u R : ℝ}
    (hm : m ≠ 0) (hR : 0 < R)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hd : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x) :
    InjOn (fun x => (m:ℝ)*V x) (Icc (l-R) (u+R)) ∧
      ∀ x ∈ Ioo (l-R) (u+R), deriv (fun x => (m:ℝ)*V x) x ≠ 0 := by
  have hsub : Icc (l-R) (u+R) ⊆ Icc (l-2*R) (u+2*R) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hi : InjOn V (Icc (l-R) (u+R)) :=
    (strictMonoOn_of_deriv_pos (convex_Icc _ _) hV.continuous.continuousOn
      (fun x hx => hd x (hsub (interior_subset hx)))).injOn
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm
  refine ⟨?_,?_⟩
  · intro x hx y hy he
    exact hi hx hy (mul_left_cancel₀ hm' he)
  · intro x hx
    rw [deriv_const_mul _ (hV.differentiable (by simp) x)]
    exact mul_ne_zero hm' (hd x (hsub (Ioo_subset_Icc_self hx))).ne'

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma stationaryWeight_mul (C : Set ℝ) (J : ℝ → ℝ) (A : ℝ → ℂ) (c : ℂ) (s : ℝ) :
    stationaryWeight C J (fun x => c*A x) s = ‖c‖^2*stationaryWeight C J A s := by
  classical
  unfold stationaryWeight branchDensity
  simp only [Set.indicator_apply]
  split_ifs <;> simp [mul_pow,mul_div_assoc]

lemma stationaryCutoffLift_eq {C : Set ℝ} {J : ℝ → ℝ}
    {A : ℝ × ℝ → ℂ} {ψ : ℝ → ℝ} :
    stationaryCutoffLift C J A ψ = fun p : ℝ × ℝ =>
      stationaryWeight C J (fun x => (ψ p.1 : ℂ)*A (x,p.1)) p.2 := by
  funext p
  rw [stationaryWeight_mul]
  simp [stationaryCutoffLift,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma cutoff_amplitude_regular {K : Set ℝ} {A : ℝ × ℝ → ℂ} {ψ : ℝ → ℝ}
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hKA : ∀ p, A p ≠ 0 → p.1 ∈ K) (hK : IsCompact K)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hcψ : HasCompactSupport ψ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => (ψ p.2 : ℂ)*A p) ∧
      HasCompactSupport (fun p : ℝ × ℝ => (ψ p.2 : ℂ)*A p) ∧
      tsupport (fun p : ℝ × ℝ => (ψ p.2 : ℂ)*A p) ⊆ K ×ˢ tsupport ψ := by
  let B : ℝ × ℝ → ℂ := fun p => (ψ p.2 : ℂ)*A p
  have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B :=
    (Complex.ofRealCLM.contDiff.comp (hψ.comp contDiff_snd)).mul hA
  have hsB : tsupport B ⊆ K ×ˢ tsupport ψ := by
    apply closure_minimal _ (hK.isClosed.prod (isClosed_tsupport ψ))
    intro p hp
    have ha : A p ≠ 0 := fun hz => hp (by simp [B,hz])
    have hψn : ψ p.2 ≠ 0 := fun hz => hp (by simp [B,hz])
    exact ⟨hKA p ha,subset_tsupport ψ hψn⟩
  have hcB : HasCompactSupport B :=
    (hK.prod hcψ).of_isClosed_subset (isClosed_tsupport B) hsB
  exact ⟨hB,hcB,hsB⟩

lemma stationaryCutoffLift_regular {C I K : Set ℝ} {J : ℝ → ℝ}
    {A : ℝ × ℝ → ℂ} {ψ : ℝ → ℝ}
    (hIC : I ⊆ C) (hi : InjOn J C)
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hKA : ∀ p, A p ≠ 0 → p.1 ∈ K) (hK : IsCompact K) (hKI : K ⊆ I)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hcψ : HasCompactSupport ψ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (stationaryCutoffLift C J A ψ) ∧
      HasCompactSupport (stationaryCutoffLift C J A ψ) := by
  let B : ℝ × ℝ → ℂ := fun p => (ψ p.2 : ℂ)*A p
  obtain ⟨hB,hcB,hsB⟩ := cutoff_amplitude_regular hA hKA hK hψ hcψ
  have hsBI : tsupport B ⊆ I ×ˢ univ := fun p hp => ⟨hKI (hsB hp).1,mem_univ _⟩
  have h := stationaryWeight_smooth_lift (C := C) (I := I) (J := J) (B := B)
    hIC hi hJ hIo hd hB hcB hsBI
  let G : ℝ × ℝ → ℝ := fun p => stationaryWeight C J (fun x => B (x,p.2)) p.1
  have hswap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Prod.swap : ℝ × ℝ → ℝ × ℝ) :=
    contDiff_snd.prodMk contDiff_fst
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G ∘ Prod.swap) := h.1.comp hswap
  have hc : HasCompactSupport (G ∘ Prod.swap) :=
    h.2.comp_homeomorph (Homeomorph.prodComm ℝ ℝ)
  have he : stationaryCutoffLift C J A ψ = G ∘ Prod.swap := stationaryCutoffLift_eq
  rw [he]
  exact ⟨hs,hc⟩

lemma stationaryWeight_support_subset {C K : Set ℝ} {J : ℝ → ℝ} {A : ℝ → ℂ}
    (hA : support A ⊆ K) : support (stationaryWeight C J A) ⊆ J '' K := by
  classical
  intro s hs
  have hsC : s ∈ J '' C := by
    by_contra hn
    exact hs (by simp [stationaryWeight,branchDensity,hn])
  have hp := invFunOn_pos hsC
  refine ⟨invFunOn J C s,hA ?_,hp.2⟩
  intro hz
  exact hs (by simp [stationaryWeight,branchDensity,hsC,show A (invFunOn J C s) = 0 from hz])

lemma stationaryCutoffLift_support {C K : Set ℝ} {J : ℝ → ℝ}
    {A : ℝ × ℝ → ℂ} {ψ : ℝ → ℝ}
    (hJ : Continuous J) (hK : IsCompact K) (hKA : ∀ p, A p ≠ 0 → p.1 ∈ K) :
    tsupport (stationaryCutoffLift C J A ψ) ⊆ tsupport ψ ×ˢ (J '' K) := by
  apply closure_minimal _ ((isClosed_tsupport ψ).prod (hK.image hJ).isClosed)
  intro p hp
  have hψn : ψ p.1 ≠ 0 := fun hz => hp (by simp [stationaryCutoffLift,hz])
  have hWn : stationaryWeight C J (fun x => A (x,p.1)) p.2 ≠ 0 :=
    fun hz => hp (by simp [stationaryCutoffLift,hz])
  exact ⟨subset_tsupport ψ hψn,
    stationaryWeight_support_subset (fun x hx => hKA (x,p.1) hx) hWn⟩

lemma stationaryCutoffLift_zero_near_zero {C K : Set ℝ} {J : ℝ → ℝ}
    {A : ℝ × ℝ → ℂ} {ψ : ℝ → ℝ}
    (hJ : Continuous J) (hK : IsCompact K) (hKA : ∀ p, A p ≠ 0 → p.1 ∈ K)
    (h0 : 0 ∉ J '' K) :
    ∃ ε > 0, ∀ a s, |s| < ε → stationaryCutoffLift C J A ψ (a,s) = 0 := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp ((hK.image hJ).isClosed.isOpen_compl.mem_nhds h0)
  refine ⟨ε,hε,?_⟩
  intro a s hs
  by_contra hh
  have hh' := stationaryCutoffLift_support hJ hK hKA (subset_tsupport _ hh)
  exact hball (by simpa [Metric.mem_ball,Real.dist_eq] using hs) hh'.2

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

/-- The cutoff old-frequency Jacobian used in the Passage Lemma has all
required regularity, including the frequency gap. These conclusions are
derived from the actual smooth amplitude and compact cutoffs. -/
lemma exact_cutoff_weight_regular
    {V : ℝ → ℝ} {m : ℤ} {l u R : ℝ} {A₀ : UnitAddCircle → ℝ → ℂ} {ψ₀ : ℝ → ℝ}
    (hm : m ≠ 0) (hR : 0 < R)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (hAr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ a, support (A₀ a) ⊆ Icc l u)
    (hψ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hcψ₀ : HasCompactSupport ψ₀)
    (h0 : 0 ∉ (fun x => (m:ℝ)*V x) '' Icc l u) :
    let F := stationaryCutoffLift (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1) ψ₀
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧ HasCompactSupport F ∧
      ∃ ε > 0, ∀ a s, |s| < ε → F (a,s) = 0 := by
  dsimp only
  have hb := scaled_speed_good_branch hm hR hV hdV
  have hKI : Icc l u ⊆ Ioo (l-R) (u+R) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hKA : ∀ p : ℝ × ℝ, A₀ (p.2 : UnitAddCircle) p.1 ≠ 0 → p.1 ∈ Icc l u :=
    fun p hp => hsupp _ hp
  have h := stationaryCutoffLift_regular Ioo_subset_Icc_self hb.1 (contDiff_const.mul hV)
    isOpen_Ioo hb.2 hAr hKA isCompact_Icc hKI hψ₀ hcψ₀
  exact ⟨h.1,h.2,stationaryCutoffLift_zero_near_zero
    (continuous_const.mul hV.continuous) isCompact_Icc hKA h0⟩

end ThreeTorus

noncomputable section
open MeasureTheory Set Function
open scoped Topology ENNReal
namespace ThreeTorus

lemma measurable_periodizedReal {q : ℝ → ℝ} (hq : Measurable q) :
    Measurable (periodizedReal q) := by
  exact Measurable.tsum (fun k => hq.comp (measurable_id.add_const (k:ℝ)))

lemma measurable_foldCircleDensity {q : ℝ → ℝ} (hq : Measurable q) :
    Measurable (foldCircleDensity q) := by
  exact ((measurable_periodizedReal hq).comp measurable_subtype_coe).comp
    (AddCircle.measurableEquivIoc 1 0).measurable

lemma foldCircleDensity_coe {q : ℝ → ℝ} {x : ℝ} (hx : x ∈ Ioc 0 1) :
    foldCircleDensity q (x : UnitAddCircle) = periodizedReal q x := by
  exact AddCircle.liftIoc_coe_apply (by simpa using hx)

lemma integral_real_eq_lattice (q : ℝ → ℝ) (hq : Integrable q) :
    (∫ x, q x) = ∑' k : ℤ, ∫ x in Ioc (0:ℝ) 1, q (x+k) := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0:ℝ)<1) 0).integral_eq_tsum'' q hq
  rw [← intUnitEquiv.tsum_eq] at h
  have he (k : ℤ) (x : ℝ) : intUnitEquiv k +ᵥ x = x+(k:ℝ) := by
    change (k • (1:ℝ))+x = x+(k:ℝ)
    simp [add_comm]
  simpa only [he,zero_add] using h

lemma lintegral_real_eq_lattice (q : ℝ → ℝ≥0∞) :
    (∫⁻ x, q x) = ∑' k : ℤ, ∫⁻ x in Ioc (0:ℝ) 1, q (x+k) := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0:ℝ)<1) 0).lintegral_eq_tsum'' q
  rw [← intUnitEquiv.tsum_eq] at h
  have he (k : ℤ) (x : ℝ) : intUnitEquiv k +ᵥ x = x+(k:ℝ) := by
    change (k • (1:ℝ))+x = x+(k:ℝ)
    simp [add_comm]
  simpa only [he,zero_add] using h

lemma integrableOn_periodizedReal {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    IntegrableOn (periodizedReal q) (Ioc 0 1) := by
  refine ⟨(measurable_periodizedReal hm).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ x in Ioc (0:ℝ) 1, ‖periodizedReal q x‖ₑ) ≤
        ∫⁻ x in Ioc (0:ℝ) 1, ∑' k : ℤ, ‖q (x+k)‖ₑ :=
      lintegral_mono (fun x => enorm_tsum_le_tsum_enorm)
    _ = ∑' k : ℤ, ∫⁻ x in Ioc (0:ℝ) 1, ‖q (x+k)‖ₑ :=
      lintegral_tsum (fun k => (hm.comp (measurable_id.add_const (k:ℝ))).enorm.aemeasurable)
    _ = ∫⁻ x, ‖q x‖ₑ := (lintegral_real_eq_lattice (fun x => ‖q x‖ₑ)).symm
    _ < ∞ := hq.hasFiniteIntegral

lemma integral_periodizedReal {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    (∫ x in Ioc (0:ℝ) 1, periodizedReal q x) = ∫ x, q x := by
  change (∫ x in Ioc (0:ℝ) 1, ∑' k : ℤ, q (x+k)) = ∫ x, q x
  rw [integral_tsum]
  · exact (integral_real_eq_lattice q hq).symm
  · exact fun k => (hm.comp (measurable_id.add_const (k:ℝ))).aestronglyMeasurable
  · rw [← lintegral_real_eq_lattice (fun x => ‖q x‖ₑ)]
    exact hq.hasFiniteIntegral.ne

lemma integrable_foldCircleDensity {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    Integrable (foldCircleDensity q) AddCircle.haarAddCircle := by
  have hp : MeasurePreserving (fun x : ℝ => (x:UnitAddCircle))
      (volume.restrict (Ioc (0:ℝ) 1)) AddCircle.haarAddCircle := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 0
  apply (hp.integrable_comp (measurable_foldCircleDensity hm).aestronglyMeasurable).1
  exact (integrableOn_periodizedReal hm hq).congr
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => (foldCircleDensity_coe hx).symm))

lemma integral_foldCircleDensity {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    (∫ a, foldCircleDensity q a ∂AddCircle.haarAddCircle) = ∫ x, q x := by
  have he := AddCircle.integral_preimage 1 0 (foldCircleDensity q)
  simp only [zero_add,AddCircle.volume_eq_smul_haarAddCircle,ENNReal.ofReal_one,
    one_smul] at he
  rw [← he]
  exact (setIntegral_congr_fun measurableSet_Ioc (fun x hx => foldCircleDensity_coe hx)).trans
    (integral_periodizedReal hm hq)

lemma quotient_add_int (x : ℝ) (k : ℤ) : ((x+k : ℝ):UnitAddCircle) = (x:UnitAddCircle) := by
  have h : ((k:ℝ):UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).2 ⟨k,by simp⟩
  rw [AddCircle.coe_add,h,add_zero]

lemma foldCircleDensity_indicator (q : ℝ → ℝ) (s : Set UnitAddCircle) :
    foldCircleDensity (((fun x : ℝ => (x:UnitAddCircle)) ⁻¹' s).indicator q) =
      s.indicator (foldCircleDensity q) := by
  classical
  funext a
  let x : ℝ := (AddCircle.equivIoc 1 0 a).1
  have hx : x ∈ Ioc (0:ℝ) 1 := by simpa using (AddCircle.equivIoc 1 0 a).2
  have ha : (x:UnitAddCircle) = a := (AddCircle.equivIoc 1 0).symm_apply_apply a
  rw [← ha]
  by_cases hs : (x:UnitAddCircle) ∈ s
  · simp only [indicator_of_mem hs,foldCircleDensity_coe hx,periodizedReal]
    apply tsum_congr
    intro k
    exact indicator_of_mem (by simpa only [mem_preimage,quotient_add_int] using hs) q
  · simp only [indicator_of_notMem hs,foldCircleDensity_coe hx,periodizedReal]
    have hz (k : ℤ) : (((fun x : ℝ => (x:UnitAddCircle)) ⁻¹' s).indicator q) (x+k) = 0 :=
      indicator_of_notMem (by simpa only [mem_preimage,quotient_add_int] using hs) q
    simp only [hz,tsum_zero]

/-- Folding is exactly pushforward under the quotient, not a replacement kernel. -/
lemma foldCircleDensity_pushforward {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    ((volume : Measure ℝ).withDensityᵥ q).map (fun x : ℝ => (x:UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensityᵥ (foldCircleDensity q) := by
  ext s hs
  rw [VectorMeasure.map_apply _ AddCircle.measurable_mk' hs,
    withDensityᵥ_apply hq (AddCircle.measurable_mk' hs),
    withDensityᵥ_apply (integrable_foldCircleDensity hm hq) hs,
    ← integral_indicator (AddCircle.measurable_mk' hs),← integral_indicator hs]
  rw [← foldCircleDensity_indicator]
  exact (integral_foldCircleDensity (hm.indicator (AddCircle.measurable_mk' hs))
    (hq.indicator (AddCircle.measurable_mk' hs))).symm

lemma periodizedReal_add_int (q : ℝ → ℝ) (x : ℝ) (j : ℤ) :
    periodizedReal q (x+j) = periodizedReal q x := by
  have h := (Equiv.addLeft j).tsum_eq (fun k : ℤ => q (x+k))
  change (∑' k : ℤ, q (x+(j:ℝ)+(k:ℝ))) = ∑' k : ℤ, q (x+(k:ℝ))
  rw [← h]
  apply tsum_congr
  intro k
  congr 1
  change x+(j:ℝ)+(k:ℝ) = x+((j+k:ℤ):ℝ)
  simp only [Int.cast_add,add_assoc]

/-- The displayed lattice formula holds for every real representative. -/
lemma foldCircleDensity_coe_all (q : ℝ → ℝ) (x : ℝ) :
    foldCircleDensity q (x:UnitAddCircle) = ∑' k : ℤ, q (x+k) := by
  let y : ℝ := (AddCircle.equivIoc 1 0 (x:UnitAddCircle)).1
  have hy : y ∈ Ioc (0:ℝ) 1 := by simpa using (AddCircle.equivIoc 1 0 (x:UnitAddCircle)).2
  have hxy : (y:UnitAddCircle) = (x:UnitAddCircle) :=
    (AddCircle.equivIoc 1 0).symm_apply_apply (x:UnitAddCircle)
  have hz : ((y-x:ℝ):UnitAddCircle) = 0 := by rw [AddCircle.coe_sub,hxy,sub_self]
  obtain ⟨k,hk⟩ := (AddCircle.coe_eq_zero_iff 1).1 hz
  have he : y = x+(k:ℝ) := by simpa only [zsmul_eq_mul,mul_one] using eq_add_of_sub_eq' hk.symm
  rw [← hxy,foldCircleDensity_coe hy,he,periodizedReal_add_int]
  rfl

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma measurable_branchDensity_smooth {I : Set ℝ} {J q : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0) (hq : Measurable q) :
    Measurable (branchDensity I J (invFunOn J I) (deriv J) q) := by
  classical
  let S := J '' I
  let g := S.piecewise (invFunOn J I) (fun _ => 0)
  have hS : IsOpen S := isOpen_image_of_deriv_ne_zero hJ hIo hd
  have hgi : ContinuousOn (invFunOn J I) S := by
    rintro y ⟨x,hx,rfl⟩
    exact (contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hx
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hx)).continuousAt.continuousWithinAt
  have hg : Measurable g := hgi.measurable_piecewise continuous_const.continuousOn hS.measurableSet
  have he : branchDensity I J (invFunOn J I) (deriv J) q =
      S.indicator (fun y => q (g y)/|deriv J (g y)|) := by
    funext y
    by_cases hy : y ∈ S
    · change S.indicator (fun y => q (invFunOn J I y)/|deriv J (invFunOn J I y)|) y = _
      simp [g,hy]
    · change S.indicator (fun y => q (invFunOn J I y)/|deriv J (invFunOn J I y)|) y = _
      simp only [indicator_of_notMem hy]
  rw [he]
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) := hJ.deriv'
  exact ((hq.comp hg).div ((hD.continuous.measurable.comp hg).abs)).indicator hS.measurableSet

lemma measurable_circleDensityLift {q : UnitAddCircle → ℝ} (hq : Measurable q) (o : ℝ) :
    Measurable (circleDensityLift o q) :=
  (hq.comp AddCircle.measurable_mk').indicator measurableSet_Ioc

lemma measurable_unfoldedModeDensity {I : Set ℝ} {J q : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0) (hq : Measurable q) (n j : ℝ) :
    Measurable (unfoldedModeDensity I J (invFunOn J I) (deriv J) q n j) := by
  have hm := measurable_branchDensity_smooth hJ hIo hinj hd (hq.const_mul n)
  unfold unfoldedModeDensity scaledBranchKernel
  exact (hm.comp ((measurable_const.mul measurable_id).sub_const j |>.div_const (j/n))).const_mul |j/n|⁻¹

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma retained_unfolded_regular {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    {ψ : UnitAddCircle → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {c : ℕ → ℤ → UnitAddCircle → ℂ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry) (hc : ∀ n j, Continuous (c n j))
    (o : ℝ) {n : ℕ} (hn : 0 < n) {j : ℤ} (hj : j ≠ 0) :
    Measurable (unfoldedModeDensity I J (invFunOn J I) (deriv J)
      (circleDensityLift o (retainedCircleWeight ψ χ c n j)) n j) ∧
    Integrable (unfoldedModeDensity I J (invFunOn J I) (deriv J)
      (circleDensityLift o (retainedCircleWeight ψ χ c n j)) n j) := by
  have hq : Continuous (retainedCircleWeight ψ χ c n j) :=
    ((hψ.pow 2).mul ((hχ.comp (continuous_const.prodMk continuous_id)).pow 2)).mul
      ((hc n j).norm.pow 2)
  exact ⟨measurable_unfoldedModeDensity hJ hIo hinj hd
      (measurable_circleDensityLift hq.measurable o) n j,
    integrable_unfoldedModeDensity hIo.measurableSet
      (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet
      (fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt) hinj
      (fun _ hx => hinj.leftInvOn_invFunOn hx) hd
      (integrable_circleDensityLift (retainedCircleWeight_integrable hψ hχ hc n j) o)
      (by exact_mod_cast hn) (by exact_mod_cast hj)⟩

lemma vectorMeasure_map_comp {X Y Z E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [AddCommMonoid E] [TopologicalSpace E]
    (ν : VectorMeasure X E) {f : X → Y} {g : Y → Z} (hf : Measurable f) (hg : Measurable g) :
    (ν.map f).map g = ν.map (g ∘ f) := by
  ext s hs
  rw [VectorMeasure.map_apply _ hg hs,VectorMeasure.map_apply _ hf (hg hs),
    VectorMeasure.map_apply _ (hg.comp hf) hs]
  rfl

/-- The folded expression is the density of the actual mode spectral map
j(1+J/n)/n modulo one. Thus the circle limit is a spectral-density statement. -/
lemma foldedModeDensity_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (hqm : Measurable q₀)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : support q₀ ⊆ Ioc o (o+1)) (hqs : support q₀ ⊆ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    {n j : ℝ} (hn : 0 < n) (hjn : j ≠ 0) :
    (AddCircle.haarAddCircle.withDensityᵥ q).map
        (fun a => (((j+(j/n)*J a)/n : ℝ) : UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensityᵥ
        (foldCircleDensity (unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀ n j)) := by
  have hqi : Integrable q₀ := by
    rw [← circleDensityLift_eq hq₀ hq₀s]
    exact integrable_circleDensityLift hq o
  have hD : ∀ x ∈ I, HasDerivWithinAt J₀ (deriv J₀ x) I x :=
    fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt
  have hp := unfoldedModeDensity_pushforward hq hq₀ hq₀s hqs hj hJ.continuous.measurable hJe
    hIo.measurableSet (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet hD hinj
    (fun _ hx => hinj.leftInvOn_invFunOn hx) hd hn hjn
  have h := congrArg (fun ν : VectorMeasure ℝ ℝ => ν.map (fun t : ℝ => (t:UnitAddCircle))) hp
  have hf : Measurable (fun a => (j+(j/n)*J a)/n) :=
    (measurable_const.add (hj.const_mul _)).div_const n
  have hg : Measurable (fun t : ℝ => (t:UnitAddCircle)) := AddCircle.measurable_mk'
  rw [vectorMeasure_map_comp _ hf hg] at h
  rw [foldCircleDensity_pushforward
    (measurable_unfoldedModeDensity hJ hIo hinj hd hqm n j)
    (integrable_unfoldedModeDensity hIo.measurableSet
      (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet hD hinj
      (fun _ hx => hinj.leftInvOn_invFunOn hx) hd hqi hn hjn)] at h
  exact h

end ThreeTorus

end

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Transmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Law averaging and weighted errors, folded packet transmission, and concrete signal-circle comparison. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators
open MeasureTheory Set Filter
open scoped Topology FourierTransform
open MeasureTheory Set Filter Asymptotics
open MeasureTheory Set Filter Function

namespace ThreeTorus
open MeasureTheory Set Filter Function
open scoped Topology BigOperators FourierTransform

lemma stationaryWeight_modulus_independent {A : UnitAddCircle → ℝ → ℂ}
    (hA : ∀ a x, ‖A a x‖ = ‖A 0 x‖) (C : Set ℝ) (V : ℝ → ℝ) (a : UnitAddCircle) :
    stationaryWeight C V (A a) = stationaryWeight C V (A 0) := by
  unfold stationaryWeight
  congr 1
  funext x
  rw [hA a x]

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Filter Function
open scoped Topology BigOperators FourierTransform

lemma exactRetainedPacketDensity_integrable
    {I : Set ℝ} {J₀ : ℝ → ℝ} {ψ : UnitAddCircle → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {m : ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} {S : Finset ℤ} {n : ℕ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀) (hIo : IsOpen I)
    (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry)
    (hH : ∀ n, Continuous (H n)) (hA : Continuous A)
    (hn : 0 < n) (hS : ∀ j ∈ S, j ≠ 0) :
    Integrable (exactRetainedPacketDensity I J₀ ψ χ m H A S n) AddCircle.haarAddCircle := by
  have hreg (j : ℤ) (hj : j ∈ S) := retained_unfolded_regular hJ hIo hinj hd hψ hχ
    (fun n j => continuous_exactPassageCoeff (m := m) (hH n) hA j) 0 hn (hS j hj)
  exact integrable_foldCircleDensity
    (Finset.measurable_sum _ (fun j hj => (hreg j hj).1))
    (integrable_finsetSum _ (fun j hj => (hreg j hj).2))

lemma integral_abs_sub_triangle {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g h : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ x, |f x-h x| ∂μ) ≤ (∫ x, |f x-g x| ∂μ)+(∫ x, |g x-h x| ∂μ) := by
  calc
    _ ≤ ∫ x, |f x-g x|+|g x-h x| ∂μ :=
      integral_mono (hf.sub hh).abs ((hf.sub hg).abs.add (hg.sub hh).abs)
        (fun x => abs_sub_le _ _ _)
    _ = _ := integral_add (hf.sub hg).abs (hg.sub hh).abs

end ThreeTorus

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_NeutralSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Neutral lattice sampling, retained support, and stationary image separation. -/

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology NNReal

lemma compact_slice_integral_continuous {F : ℝ × ℝ → ℝ} {D : ℝ}
    (hF : Continuous F) (hFa : ∀ s a, D < |a| → F (s,a) = 0) :
    Continuous (fun s => ∫ a, F (s,a)) := by
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (k := Icc (-D) D) isCompact_Icc
  · exact hF.continuousOn
  · intro s a _ ha
    exact hFa s a (lt_of_not_ge (by simpa only [mem_Icc,← abs_le] using ha))

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology NNReal

lemma compact_rect_bounds {F : ℝ × ℝ → ℝ} (hc : HasCompactSupport F) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
      (∀ s a, A < |s| → F (s,a) = 0) ∧ (∀ s a, D < |a| → F (s,a) = 0) := by
  obtain ⟨R,hR⟩ := hc.isBounded.subset_closedBall (0 : ℝ × ℝ)
  refine ⟨max R 0,max R 0,le_max_right _ _,le_max_right _ _,?_,?_⟩
  · intro s a hs
    by_contra hn
    have hh := hR (subset_tsupport _ hn)
    rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def] at hh
    have hh' : |s| ≤ R := by simpa only [Real.norm_eq_abs] using (le_max_left ‖s‖ ‖a‖).trans hh
    exact (not_lt_of_ge (hh'.trans (le_max_left _ _))) hs
  · intro s a hs
    by_contra hn
    have hh := hR (subset_tsupport _ hn)
    rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def] at hh
    have hh' : |a| ≤ R := by simpa only [Real.norm_eq_abs] using (le_max_right ‖s‖ ‖a‖).trans hh
    exact (not_lt_of_ge (hh'.trans (le_max_left _ _))) hs

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology NNReal

lemma compact_slice_integral_regular {F : ℝ × ℝ → ℝ}
    (hF : Continuous F) (hcF : HasCompactSupport F) :
    Continuous (fun s => ∫ a, F (s,a)) ∧ Integrable (fun s => ∫ a, F (s,a)) := by
  obtain ⟨A,D,_,_,hFs,hFa⟩ := compact_rect_bounds hcF
  have hZ := compact_slice_integral_continuous hF hFa
  refine ⟨hZ,hZ.integrable_of_hasCompactSupport ?_⟩
  apply HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A))
  intro s hs
  have hab : A < |s| := lt_of_not_ge (by simpa only [mem_Icc,← abs_le] using hs)
  simp [hFs s _ hab]

end ThreeTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_RetainedPackets
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal retained passage vectors, spectral identities, regularity, old marginals, and quantitative cutoff losses. -/

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology

noncomputable section
open Set Function Filter
open scoped Topology
namespace ThreeTorus

/-- The second support separation in the manuscript uses cutoffs in frequency
alone, as opposed to the first passage's frequency/slow-coordinate cutoffs. -/
theorem finite_disjoint_frequency_cutoffs {ι : Type*} [Finite ι]
    (K U : ι → Set ℝ) (hK : ∀ i, IsCompact (K i)) (hU : ∀ i, IsOpen (U i))
    (hKU : ∀ i, K i ⊆ U i) (hdisj : Pairwise (Disjoint on K)) :
    ∃ χ : ι → ℝ → ℝ,
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ i) ∧ HasCompactSupport (χ i) ∧
        tsupport (χ i) ⊆ U i ∧ (∀ s, 0 ≤ χ i s ∧ χ i s ≤ 1) ∧
        ∀ s ∈ K i, χ i =ᶠ[𝓝 s] 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) := by
  have hd : Pairwise (fun i j => Disjoint (𝓝ˢ (K i)) (𝓝ˢ (K j))) :=
    fun i j hij => disjoint_nhdsSet_nhdsSet (hK i).isClosed (hK j).isClosed (hdisj hij)
  obtain ⟨O,hO,hOd⟩ := hd.exists_mem_filter_of_disjoint
  have hv i : K i ⊆ interior (O i) ∩ U i :=
    subset_inter (subset_interior_iff_mem_nhdsSet.mpr (hO i)) (hKU i)
  choose χ hχ using fun i => compact_smooth_cutoff (hK i)
    (isOpen_interior.inter (hU i)) (hv i)
  refine ⟨χ,fun i => ⟨(hχ i).1,(hχ i).2.1,(hχ i).2.2.1.trans inter_subset_right,
    (hχ i).2.2.2⟩,?_⟩
  intro i j hij
  exact (hOd hij).mono ((hχ i).2.2.1.trans (inter_subset_left.trans interior_subset))
    ((hχ j).2.2.1.trans (inter_subset_left.trans interior_subset))

lemma compactSupport_frequency_cylinder {χ : ℝ → ℝ} (hc : HasCompactSupport χ) :
    HasCompactSupport (fun p : ℝ × UnitAddCircle => χ p.1) := by
  apply (hc.prod isCompact_univ).of_isClosed_subset isClosed_closure
  apply closure_minimal _ ((isClosed_tsupport χ).prod isClosed_univ)
  intro p hp
  exact ⟨subset_tsupport χ hp,mem_univ _⟩

end ThreeTorus

noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology
namespace ThreeTorus
namespace CompactParameter

/-- Compact-parameter differentiation, used by the exact passage near epsilon=0. -/
lemma hasFDerivAt_compact_integral
    {E : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E × ℝ → G} (hF : ContDiff ℝ 1 F) (a b : ℝ) (x : E) :
    HasFDerivAt (fun y => ∫ t in a..b, F (y,t))
      (∫ t in a..b, (fderiv ℝ F (x,t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
  let D : E × ℝ → E →L[ℝ] G := fun p =>
    (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hD : Continuous D := hF.continuous_fderiv (by norm_num) |>.clm_comp continuous_const
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn hD.continuousOn
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F := fun y t => F (y,t)) (F' := fun y t => D (y,t))
    (bound := fun _ => C) (Metric.closedBall_mem_nhds x (by norm_num : (0:ℝ)<1)) ?_ ?_ ?_ ?_
    intervalIntegrable_const ?_
  · exact Eventually.of_forall (fun y => (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    intro y hy
    exact hC (y,t) ⟨hy,uIoc_subset_uIcc ht⟩
  · exact Eventually.of_forall (fun t y _ => by
      simpa [D,Function.comp_def] using ((hF.differentiable one_ne_zero ((ContinuousLinearMap.inl ℝ E ℝ) y+(0,t))).hasFDerivAt).comp y
        ((ContinuousLinearMap.inl ℝ E ℝ).hasFDerivAt.add_const (0,t)))

/-- Smooth parameter integration over a fixed compact interval. -/
lemma contDiff_compact_integral
    {E : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (n : ℕ) {F : E × ℝ → G} (hF : ContDiff ℝ n F) (a b : ℝ) :
    ContDiff ℝ n (fun y => ∫ t in a..b, F (y,t)) := by
  induction n generalizing G with
  | zero =>
    apply contDiff_zero.mpr
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (show Continuous (Function.uncurry (fun y t => F (y,t))) from hF.continuous) a b
  | succ n ih =>
    let D : E × ℝ → E →L[ℝ] G := fun p =>
      (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hD : ContDiff ℝ n D := (hF.fderiv_right (by simp)).clm_comp contDiff_const
    have hder (x : E) := hasFDerivAt_compact_integral (hF.of_le (by exact_mod_cast Nat.succ_pos n)) a b x
    rw [show ((n+1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞)+1 by simp, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hder x).differentiableAt, ?_, ?_⟩
    · simp
    · have heq : fderiv ℝ (fun y => ∫ t in a..b, F (y,t)) =
          fun y => ∫ t in a..b, D (y,t) := by
        funext y
        exact (hder y).fderiv
      rw [heq]
      exact ih hD

lemma smooth_compact_integral
    {E : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E × ℝ → G} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (a b : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∫ t in a..b, F (y,t)) := by
  rw [contDiff_infty]
  intro n
  exact contDiff_compact_integral n (hF.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))) a b

end CompactParameter

/-- Smoothness of a Fourier coefficient in an arbitrary finite-dimensional
parameter, obtained from a compact interval integral of the literal lift. -/
lemma smooth_fourierCoeff_param {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → UnitAddCircle → ℂ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : E × ℝ => f p.1 (p.2 : UnitAddCircle))) (j : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => fourierCoeff (f x) j) := by
  have hchar : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : E × ℝ => (fourier (-j) (p.2 : UnitAddCircle) : ℂ)) := by
    simp only [fourier_coe_apply, Complex.ofReal_one, div_one]
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_snd)).cexp
  have h := CompactParameter.smooth_compact_integral (hchar.mul hf) 0 1
  have he (x : E) : fourierCoeff (f x) j =
      ∫ t in (0:ℝ)..1, (fourier (-j) (t : UnitAddCircle) : ℂ) * f x t := by
    simpa only [one_div_one,one_smul,zero_add,smul_eq_mul] using
      fourierCoeff_eq_intervalIntegral (f x) j 0
  simpa only [he] using h

lemma smooth_fourier_lift (m : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => (fourier m (x : UnitAddCircle) : ℂ)) := by
  simp only [fourier_coe_apply,Complex.ofReal_one,div_one]
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

/-- Smoothness of the exact old-amplitude coefficients; no stationary-phase
approximation replaces these coefficients. -/
lemma smooth_exactPassageCoeff {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {Hl : ℝ → ℝ} {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hHl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Hl)
    (hH : ∀ t : ℝ, H (t : UnitAddCircle) = (Hl t : UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A (p.1,p.2))) (j : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun a : ℝ => exactPassageCoeff m H A j a) := by
  apply smooth_fourierCoeff_param
  change ContDiff ℝ _ (fun p : ℝ × ℝ => A (p.2,p.1)*fourier m (H p.2))
  simp_rw [hH]
  exact (hA.comp (contDiff_snd.prodMk contDiff_fst)).mul ((smooth_fourier_lift m).comp (hHl.comp contDiff_snd))

/-- The new amplitudes retained by the passage lie in the same smooth packet
class needed for its next use. -/
lemma smooth_retained_amplitude {m j : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {Hl : ℝ → ℝ} {A : UnitAddCircle × UnitAddCircle → ℂ}
    {χ : ℝ × UnitAddCircle → ℝ} {ψ : UnitAddCircle → ℝ} (s : ℝ)
    (hHl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Hl)
    (hH : ∀ t : ℝ, H (t : UnitAddCircle) = (Hl t : UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (hχ : CylinderSmooth χ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a : ℝ => ψ a)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ =>
      (χ (s,p.1):ℂ)*(ψ p.1:ℂ)*exactPassageCoeff m H A j p.1*fourier m (p.2:UnitAddCircle)) := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => χ (s,(p.1:UnitAddCircle))) :=
    hχ.comp (contDiff_const.prodMk contDiff_fst)
  exact (((Complex.ofRealCLM.contDiff.comp hc).mul (Complex.ofRealCLM.contDiff.comp (hψ.comp contDiff_fst))).mul
    ((smooth_exactPassageCoeff hHl hH hA j).comp contDiff_fst)).mul
      ((smooth_fourier_lift m).comp contDiff_snd)

end ThreeTorus

noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology ENNReal
namespace ThreeTorus

/-- A nonnegative integrable density identity proved with signed vector
measures is the identical ordinary measure identity. -/
lemma positive_density_map_of_vectorMeasure
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} {q : X → ℝ} {p : Y → ℝ}
    (hf : Measurable f) (hq : Integrable q μ) (hp : Integrable p ν)
    (hq0 : ∀ x, 0 ≤ q x) (hp0 : ∀ y, 0 ≤ p y)
    (he : (μ.withDensityᵥ q).map f = ν.withDensityᵥ p) :
    (μ.withDensity (fun x => ENNReal.ofReal (q x))).map f =
      ν.withDensity (fun y => ENNReal.ofReal (p y)) := by
  ext s hs
  rw [Measure.map_apply hf hs,withDensity_apply _ (hf hs),withDensity_apply _ hs]
  rw [← ofReal_integral_eq_lintegral_ofReal hq.integrableOn (Eventually.of_forall hq0),
    ← ofReal_integral_eq_lintegral_ofReal hp.integrableOn (Eventually.of_forall hp0)]
  congr 1
  have h := congrArg (fun v : VectorMeasure Y ℝ => v s) he
  simpa only [VectorMeasure.map_apply _ hf hs,withDensityᵥ_apply hq (hf hs),
    withDensityᵥ_apply hp hs] using h

lemma branchDensity_nonneg {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hq : ∀ t, 0 ≤ q t) (y : ℝ) : 0 ≤ branchDensity I J g D q y := by
  classical
  simp only [branchDensity,Set.indicator_apply]
  split_ifs
  · exact div_nonneg (hq _) (abs_nonneg _)
  · rfl

lemma unfoldedModeDensity_nonneg {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hq : ∀ t, 0 ≤ q t) {n : ℝ} (hn : 0 ≤ n) (j t : ℝ) :
    0 ≤ unfoldedModeDensity I J g D q n j t := by
  unfold unfoldedModeDensity scaledBranchKernel
  exact mul_nonneg (inv_nonneg.mpr (abs_nonneg _))
    (branchDensity_nonneg (fun a => mul_nonneg hn (hq a)) _)

lemma foldCircleDensity_nonneg {q : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t) (z : UnitAddCircle) :
    0 ≤ foldCircleDensity q z := by
  unfold foldCircleDensity periodizedReal
  exact tsum_nonneg (fun k => hq _)

lemma retainedAmplitude_norm_sq (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ)
    (p : UnitAddCircle × UnitAddCircle) :
    ‖retainedAmplitude ψ χ m H A n j p‖^2 =
      retainedCircleWeight ψ χ (fun n j => exactPassageCoeff m (H n) A j) n j p.1 := by
  simp only [retainedAmplitude,norm_mul,show ‖fourier m p.2‖ = 1 from Circle.norm_coe _,
    mul_one,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,retainedCircleWeight]

lemma retainedAmplitude_modulus (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) (a b : UnitAddCircle) :
    ‖retainedAmplitude ψ χ m H A n j (a,b)‖ =
      ‖retainedAmplitude ψ χ m H A n j (a,0)‖ := by
  simp only [retainedAmplitude,norm_mul,show ‖fourier m b‖ = 1 from Circle.norm_coe _,
    show ‖fourier m (0:UnitAddCircle)‖ = 1 from Circle.norm_coe _]

-- The same elementary identity used in the supplied whitening proof.
lemma map_withDensity_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {ζ : X → Y} {w : Y → ℝ≥0∞}
    (hζ : Measurable ζ) (hw : Measurable w) :
    (μ.withDensity (w ∘ ζ)).map ζ = (μ.map ζ).withDensity w := by
  ext s hs
  rw [Measure.map_apply hζ hs, withDensity_apply _ (hζ hs), withDensity_apply _ hs]
  rw [← lintegral_indicator (hζ hs), ← lintegral_indicator hs,
    lintegral_map (hw.indicator hs) hζ]
  apply lintegral_congr
  intro x
  rfl

/-- If a coefficient's modulus is independent of its spare coordinate, its
literal packet spectral measure is the single-coordinate weighted image. -/
lemma packetSpectralMeasure_of_modulus
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ) {j : ℤ}
    {B : UnitAddCircle × UnitAddCircle → ℂ} {q : UnitAddCircle → ℝ}
    (hq : Measurable q) (hB : ∀ p, ‖B p‖^2 = q p.1) :
    packetSpectralMeasure φ j B =
      (AddCircle.haarAddCircle.withDensity (fun a => ENNReal.ofReal (q a))).map
        (fun a => j • φ a) := by
  unfold packetSpectralMeasure
  have he : (fun p : UnitAddCircle × UnitAddCircle => ENNReal.ofReal (‖B p‖^2)) =
      (fun a => ENNReal.ofReal (q a)) ∘ Prod.fst := funext (fun p => congrArg _ (hB p))
  rw [he]
  change Measure.map ((fun a => j • φ a) ∘ Prod.fst) _ = _
  rw [← Measure.map_map (show Measurable (fun a => j • φ a) from hφ.const_smul j) measurable_fst,
    map_withDensity_comp slowVolume measurable_fst hq.ennreal_ofReal]
  simp only [slowVolume,Measure.map_fst_prod,measure_univ,one_smul]

lemma retainedCircleWeight_nonneg (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (c : ℕ → ℤ → UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) (a : UnitAddCircle) :
    0 ≤ retainedCircleWeight ψ χ c n j a := by unfold retainedCircleWeight; positivity

lemma circleDensityLift_nonneg {q : UnitAddCircle → ℝ} (hq : ∀ a, 0 ≤ q a)
    (o x : ℝ) : 0 ≤ circleDensityLift o q x := by
  classical
  simp only [circleDensityLift,Set.indicator_apply]
  split_ifs
  · exact hq _
  · rfl

/-- The folded branch is the ordinary (positive) spectral density, not just
an identity of signed integrals. -/
lemma positive_foldedModeDensity_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (hqm : Measurable q₀)
    (hq0 : ∀ a, 0 ≤ q a) (hq00 : ∀ x, 0 ≤ q₀ x)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : support q₀ ⊆ Ioc o (o+1)) (hqs : support q₀ ⊆ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    {n j : ℝ} (hn : 0 < n) (hjn : j ≠ 0) :
    (AddCircle.haarAddCircle.withDensity (fun a => ENNReal.ofReal (q a))).map
        (fun a => (((j+(j/n)*J a)/n : ℝ) : UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensity
        (fun z => ENNReal.ofReal
          (foldCircleDensity (unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀ n j) z)) := by
  have hqi : Integrable q₀ := by
    rw [← circleDensityLift_eq hq₀ hq₀s]
    exact integrable_circleDensityLift hq o
  have hD : ∀ x ∈ I, HasDerivWithinAt J₀ (deriv J₀ x) I x :=
    fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt
  have hmi := measurable_unfoldedModeDensity hJ hIo hinj hd hqm n j
  have hii := integrable_unfoldedModeDensity hIo.measurableSet
    (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet hD hinj
    (fun _ hx => hinj.leftInvOn_invFunOn hx) hd hqi hn hjn
  exact positive_density_map_of_vectorMeasure
    (AddCircle.measurable_mk'.comp ((measurable_const.add (hj.const_mul _)).div_const n))
    hq (integrable_foldCircleDensity hmi hii) hq0
    (foldCircleDensity_nonneg (unfoldedModeDensity_nonneg hq00 hn.le j))
    (foldedModeDensity_pushforward hq hqm hq₀ hq₀s hqs hj hJ hJe hIo hinj hd hn hjn)

lemma passage_speed_mode (J : UnitAddCircle → ℝ) (n : ℝ) (j : ℤ) (a : UnitAddCircle) :
    j • (((1+J a/n)/n : ℝ) : UnitAddCircle) =
      ((((j:ℝ)+((j:ℝ)/n)*J a)/n : ℝ) : UnitAddCircle) := by
  rw [← AddCircle.coe_zsmul]
  congr 1
  simp only [zsmul_eq_mul]
  ring

/-- Any coefficient with the actual retained modulus has the displayed
nonnegative folded density under the actual new twist. -/
lemma packetSpectralMeasure_new_speed {q : UnitAddCircle → ℝ} {q₀ J₀ : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    {B : UnitAddCircle × UnitAddCircle → ℂ}
    (hq : Integrable q AddCircle.haarAddCircle) (hqmeas : Measurable q) (hqm : Measurable q₀)
    (hB : ∀ p, ‖B p‖^2 = q p.1) (hq00 : ∀ x, 0 ≤ q₀ x)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : support q₀ ⊆ Ioc o (o+1)) (hqs : support q₀ ⊆ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    {n : ℝ} {j : ℤ} (hn : 0 < n) (hjn : j ≠ 0) :
    packetSpectralMeasure (fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)) j B =
      AddCircle.haarAddCircle.withDensity
        (fun z => ENNReal.ofReal
          (foldCircleDensity (unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀ n j) z)) := by
  have hσ : Measurable (fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp ((measurable_const.add (hj.div_const n)).div_const n)
  rw [packetSpectralMeasure_of_modulus hσ hqmeas hB]
  simp_rw [passage_speed_mode]
  exact positive_foldedModeDensity_pushforward hq hqm
    (fun a => (hB (a,0)) ▸ sq_nonneg _) hq00 hq₀ hq₀s hqs hj hJ hJe hIo hinj hd hn
    (by exact_mod_cast hjn)

/-- Density identity for the literal retained coefficient used by the passage.
The only support hypothesis is that the cutoff lies on the chosen good branch. -/
lemma retainedAmplitude_spectralDensity
    {ψ : UnitAddCircle → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {m : ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle} {A : UnitAddCircle × UnitAddCircle → ℂ}
    {J : UnitAddCircle → ℝ} {J₀ : ℝ → ℝ} {o : ℝ} {I : Set ℝ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry)
    (hH : ∀ n, Continuous (H n)) (hA : Continuous A)
    (hψs : ∀ x ∈ Ioc o (o+1), ψ (x:UnitAddCircle) ≠ 0 → x ∈ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x:UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    {n : ℕ} {j : ℤ} (hn : 0 < n) (hjn : j ≠ 0) :
    packetSpectralMeasure (fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)) j
      (retainedAmplitude ψ χ m H A n j) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal
        (foldCircleDensity (unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
          (circleDensityLift o (retainedCircleWeight ψ χ
            (fun n j => exactPassageCoeff m (H n) A j) n j)) n j) z)) := by
  let C n j := exactPassageCoeff m (H n) A j
  let q := retainedCircleWeight ψ χ C n j
  have hC n j : Continuous (C n j) := continuous_exactPassageCoeff (hH n) hA j
  have hq : Continuous q :=
    ((hψ.pow 2).mul ((hχ.comp (continuous_const.prodMk continuous_id)).pow 2)).mul
      ((hC n j).norm.pow 2)
  have hqs : support (circleDensityLift o q) ⊆ Ioc o (o+1) ∩ I := by
    intro x hx
    have hxI : x ∈ Ioc o (o+1) := by
      by_contra hh
      exact hx (by simp [circleDensityLift,hh])
    refine ⟨hxI,hψs x hxI ?_⟩
    intro hz
    exact hx (by simp [circleDensityLift,hxI,q,retainedCircleWeight,hz])
  exact packetSpectralMeasure_new_speed
    (retainedCircleWeight_integrable hψ hχ hC n j) hq.measurable
    (measurable_circleDensityLift hq.measurable o)
    (retainedAmplitude_norm_sq ψ χ m H A n j)
    (circleDensityLift_nonneg (retainedCircleWeight_nonneg ψ χ C n j) o)
    (fun _ hx => by simp only [circleDensityLift,indicator_of_mem hx]; rfl)
    (hqs.trans inter_subset_left) (hqs.trans inter_subset_right)
    hj hJ hJe hIo hinj hd (by exact_mod_cast hn) hjn

end ThreeTorus
end
end
end
end
end
end

section

/-! Exact spectral identity for the literal retained packet vector. This closes
 the interface between the previously proved coefficient-density estimates and
 the actual Koopman correlations, without an abstract density hypothesis. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma foldCircleDensity_add_ae {q r : ℝ → ℝ} (hq : Measurable q) (hr : Measurable r)
    (hqi : Integrable q) (hri : Integrable r) :
    foldCircleDensity (fun x => q x+r x) =ᵐ[AddCircle.haarAddCircle]
      fun z => foldCircleDensity q z+foldCircleDensity r z := by
  apply (integrable_foldCircleDensity (hq.add hr) (hqi.add hri)).ae_eq_of_withDensityᵥ_eq
    ((integrable_foldCircleDensity hq hqi).add (integrable_foldCircleDensity hr hri))
  rw [← foldCircleDensity_pushforward (hq.add hr) (hqi.add hri),
    withDensityᵥ_add hqi hri,
    withDensityᵥ_add (integrable_foldCircleDensity hq hqi) (integrable_foldCircleDensity hr hri)]
  have he := map_add (VectorMeasure.mapGm (fun x : ℝ => (x:UnitAddCircle)))
    (volume.withDensityᵥ q) (volume.withDensityᵥ r)
  change (volume.withDensityᵥ q+volume.withDensityᵥ r).map _ =
    (volume.withDensityᵥ q).map _+(volume.withDensityᵥ r).map _ at he
  rw [he,foldCircleDensity_pushforward hq hqi,foldCircleDensity_pushforward hr hri]

lemma foldCircleDensity_finsetSum_ae {ι : Type*} (S : Finset ι) (q : ι → ℝ → ℝ)
    (hq : ∀ i ∈ S, Measurable (q i)) (hqi : ∀ i ∈ S, Integrable (q i)) :
    foldCircleDensity (fun x => ∑ i ∈ S, q i x) =ᵐ[AddCircle.haarAddCircle]
      fun z => ∑ i ∈ S, foldCircleDensity (q i) z := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    filter_upwards [] with z
    simp [foldCircleDensity,periodizedReal,AddCircle.liftIoc,Set.domRestrict]
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    have hh := foldCircleDensity_add_ae (hq i (Finset.mem_insert_self i S))
      (Finset.measurable_sum S (fun j hj => hq j (Finset.mem_insert_of_mem hj)))
      (hqi i (Finset.mem_insert_self i S))
      (integrable_finsetSum S (fun j hj => hqi j (Finset.mem_insert_of_mem hj)))
    have ht := ih (fun j hj => hq j (Finset.mem_insert_of_mem hj))
      (fun j hj => hqi j (Finset.mem_insert_of_mem hj))
    filter_upwards [hh,ht] with z hz ht
    rw [hz,ht]

end ThreeTorus
end
end

section

/-! Smoothness at the edge of the good arc is essential: the actual retained
spectral densities must be valid smooth inputs to the next stage. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma support_branchDensity_subset {J q : ℝ → ℝ} {I : Set ℝ} :
    support (branchDensity I J (invFunOn J I) (deriv J) q) ⊆ J '' tsupport q := by
  intro y hy
  have hyI : y ∈ J '' I := by
    by_contra hh
    exact hy (by simp [branchDensity,hh])
  have hx := invFunOn_pos hyI
  refine ⟨invFunOn J I y,subset_tsupport q ?_,hx.2⟩
  intro hq
  exact hy (by simp [branchDensity,hyI,hq])

lemma branchDensity_compact {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : Continuous J) (hq : HasCompactSupport q) :
    HasCompactSupport (branchDensity I J (invFunOn J I) (deriv J) q) := by
  apply HasCompactSupport.intro (hq.image hJ)
  intro y hy
  exact notMem_support.mp (fun hh => hy (support_branchDensity_subset hh))

lemma branchDensity_smooth {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q) (hc : HasCompactSupport q)
    (hs : tsupport q ⊆ I) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (branchDensity I J (invFunOn J I) (deriv J) q) := by
  classical
  let g := invFunOn J I
  have hM : IsCompact (J '' tsupport q) := hc.image hJ.continuous
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) := hJ.deriv'
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ J '' tsupport q
  · obtain ⟨x,hx,rfl⟩ := hy
    have hxI := hs hx
    have hyI : J x ∈ J '' I := mem_image_of_mem J hxI
    have hg := contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hxI
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hxI)
    have hge : g (J x) = x := hinj (invFunOn_pos hyI).1 hxI (invFunOn_pos hyI).2
    have hden : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y => |deriv J (g y)|) (J x) :=
      (contDiffAt_abs (by simpa only [hge] using hd x hxI)).comp (J x)
        (hD.contDiffAt.comp (J x) hg)
    have hquot := (hq.contDiffAt.comp (J x) hg).div hden
      (by simpa only [hge] using abs_ne_zero.mpr (hd x hxI))
    apply hquot.congr_of_eventuallyEq
    filter_upwards [(isOpen_image_of_deriv_ne_zero hJ hIo hd).mem_nhds hyI] with z hz
    simp only [branchDensity,indicator_of_mem hz,g]
    rfl
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hM.isClosed.isOpen_compl.mem_nhds hy] with z hz
    exact notMem_support.mp (fun hh => hz (support_branchDensity_subset hh))

lemma unfoldedModeDensity_smooth {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q) (hc : HasCompactSupport q)
    (hs : tsupport q ⊆ I) (n j : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (unfoldedModeDensity I J (invFunOn J I) (deriv J) q n j) := by
  have hmul : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => n*q x) := contDiff_const.mul hq
  have hcs : HasCompactSupport (fun x => n*q x) := hc.mul_left
  have hs' : tsupport (fun x => n*q x) ⊆ I := tsupport_mul_subset_right.trans hs
  have hh := branchDensity_smooth hJ hIo hinj hd hmul hcs hs' 
  unfold unfoldedModeDensity scaledBranchKernel
  exact contDiff_const.mul (hh.comp ((contDiff_const.mul contDiff_id).sub contDiff_const |>.div_const _))

lemma unfoldedModeDensity_compact {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : Continuous J) (hc : HasCompactSupport q) {n j : ℝ} (hn : n ≠ 0) (hj : j ≠ 0) :
    HasCompactSupport (unfoldedModeDensity I J (invFunOn J I) (deriv J) q n j) := by
  have hh := branchDensity_compact (I := I) hJ (hc.mul_left (f := fun _ => n))
  let e : ℝ ≃ₜ ℝ := (Homeomorph.mulLeft₀ n hn).trans (Homeomorph.addRight (-j))
  let e' : ℝ ≃ₜ ℝ := e.trans (Homeomorph.mulRight₀ (n/j) (div_ne_zero hn hj))
  have he (t : ℝ) : e' t = (n*t-j)/(j/n) := by
    dsimp [e',e]
    field_simp
    ring
  have hc' := hh.comp_homeomorph e'
  have heq : unfoldedModeDensity I J (invFunOn J I) (deriv J) q n j =
      fun t => |j/n|⁻¹ * branchDensity I J (invFunOn J I) (deriv J) (fun x => n*q x) (e' t) := by
    funext t
    rw [he]
    rfl
  rw [heq]
  exact hc'.mul_left

lemma periodizedReal_eq_periodize {q : ℝ → ℝ} (hc : HasCompactSupport q) :
    periodizedReal q = periodize q := by
  funext x
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R+|x|+1)
  have hs : support (fun k : ℤ => q (x+k)) ⊆ (Finset.Icc (-(N:ℤ)) N : Set ℤ) := by
    intro k hk
    have hr := hR (x+k) (subset_tsupport q hk)
    have hh : |(k:ℝ)| < N := by
      have ha := abs_sub_le (x+(k:ℝ)) 0 x
      simp only [sub_zero,zero_sub,abs_neg,add_sub_cancel_left,Real.norm_eq_abs] at hr ha
      linarith
    have hab := abs_lt.mp hh
    simp only [Finset.mem_coe,Finset.mem_Icc]
    constructor
    · exact_mod_cast (by linarith : -(N:ℝ) ≤ (k:ℝ))
    · exact_mod_cast (by linarith : (k:ℝ) ≤ (N:ℝ))
  exact tsum_eq_finsum ((Finset.finite_toSet _).subset hs)

lemma foldCircleDensity_smooth_lift {q : ℝ → ℝ}
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q) (hc : HasCompactSupport q) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => foldCircleDensity q (x:UnitAddCircle)) := by
  have he : (fun x : ℝ => foldCircleDensity q (x:UnitAddCircle)) = periodize q := by
    funext x
    rw [foldCircleDensity_coe_all]
    exact congrFun (periodizedReal_eq_periodize hc) x
  rw [he]
  exact contDiff_periodize hq hc

lemma realRetainedWeight_support (ψ₀ : ℝ → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) :
    tsupport (realRetainedWeight ψ₀ χ m H A n j) ⊆ tsupport ψ₀ := by
  apply closure_mono
  intro x hx hz
  exact hx (by simp [realRetainedWeight,hz])

lemma realRetainedWeight_compact {ψ₀ : ℝ → ℝ} (hc : HasCompactSupport ψ₀)
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) :
    HasCompactSupport (realRetainedWeight ψ₀ χ m H A n j) :=
  hc.of_isClosed_subset isClosed_closure (realRetainedWeight_support ψ₀ χ m H A n j)

lemma realRetainedWeight_smooth {ψ₀ : ℝ → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {m : ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle} {Hl : ℕ → ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀)
    (hχ : CylinderSmooth χ.uncurry)
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hH : ∀ n (t : ℝ), H n (t:UnitAddCircle) = (Hl n t:UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (n : ℕ) (j : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (realRetainedWeight ψ₀ χ m H A n j) := by
  have hχ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => χ ((j:ℝ)/n) x) := hχ.comp (contDiff_const.prodMk contDiff_id)
  exact ((hψ.pow 2).mul (hχ'.pow 2)).mul
    ((smooth_exactPassageCoeff (hHl n) (hH n) hA j).norm_sq (𝕜 := ℂ))

lemma retainedWeight_lift_eq {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ)
    (he : ∀ x ∈ Ioc (0:ℝ) (0+1), ψ (x:UnitAddCircle) = ψ₀ x)
    (hs : tsupport ψ₀ ⊆ Ioc (0:ℝ) (0+1)) :
    circleDensityLift 0 (retainedCircleWeight ψ χ
      (fun n j => exactPassageCoeff m (H n) A j) n j) =
      realRetainedWeight ψ₀ χ m H A n j := by
  apply circleDensityLift_eq
  · intro x hx
    simp only [retainedCircleWeight,realRetainedWeight,he x hx]
  · exact (subset_tsupport _).trans ((realRetainedWeight_support ψ₀ χ m H A n j).trans hs)

/-- Actual retained densities are smooth at all branch edges, including their
zero set. This supplies the next passage's regularity; it is not an assumption
that the density is already smooth. -/
theorem exactRetainedPacketDensity_smooth_lift
    {I : Set ℝ} {J : ℝ → ℝ} {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {m : ℤ}
    {H : ℕ → UnitAddCircle → UnitAddCircle} {Hl : ℕ → ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ} {S : Finset ℤ} {n : ℕ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hc : HasCompactSupport ψ₀)
    (he : ∀ x ∈ Ioc (0:ℝ) (0+1), ψ (x:UnitAddCircle) = ψ₀ x)
    (hs : tsupport ψ₀ ⊆ Ioc (0:ℝ) (0+1) ∩ I)
    (hχ : CylinderSmooth χ.uncurry)
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hH : ∀ n (t : ℝ), H n (t:UnitAddCircle) = (Hl n t:UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (hn : 0 < n) (hS : ∀ j ∈ S, j ≠ 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => exactRetainedPacketDensity I J ψ χ m H A S n x) := by
  unfold exactRetainedPacketDensity
  simp_rw [retainedWeight_lift_eq χ m H A n _ he (hs.trans inter_subset_left)]
  apply foldCircleDensity_smooth_lift
  · apply ContDiff.sum
    intro j hj
    exact unfoldedModeDensity_smooth hJ hIo hinj hd
      (realRetainedWeight_smooth hψ hχ hHl hH hA n j)
      (realRetainedWeight_compact hc χ m H A n j)
      ((realRetainedWeight_support ψ₀ χ m H A n j).trans (hs.trans inter_subset_right)) n j
  · have hh (j : ℤ) (hj : j ∈ S) : HasCompactSupport
        (unfoldedModeDensity I J (invFunOn J I) (deriv J)
          (realRetainedWeight ψ₀ χ m H A n j) n j) :=
      unfoldedModeDensity_compact hJ.continuous
        (realRetainedWeight_compact hc χ m H A n j)
        (by exact_mod_cast hn.ne') (by exact_mod_cast hS j hj)
    convert HasCompactSupport.finset_sum hh using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext time; simp only [Finset.sum_apply])

end ThreeTorus
end
end

section

/-! Identification of the reference stationary marginal with the actual old
packet spectrum. In particular integer carrier speeds do not change it. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma positive_circle_branch_fold
    {q : UnitAddCircle → ℝ} {q₀ J₀ : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (hqm : Measurable q₀)
    (hq0 : ∀ a, 0 ≤ q a) (hq00 : ∀ x, 0 ≤ q₀ x)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x:UnitAddCircle) = q₀ x)
    (hq₀s : support q₀ ⊆ Ioc o (o+1)) (hqs : support q₀ ⊆ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x:UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0) :
    (AddCircle.haarAddCircle.withDensity (fun a => ENNReal.ofReal (q a))).map
        (fun a => (J a:UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal
        (foldCircleDensity (branchDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀) z)) := by
  let w := branchDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀
  have hqi : Integrable q₀ := by
    rw [← circleDensityLift_eq hq₀ hq₀s]
    exact integrable_circleDensityLift hq o
  have hD : ∀ x ∈ I, HasDerivWithinAt J₀ (deriv J₀ x) I x :=
    fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt
  have hIm := (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet
  have hwi : Integrable w := integrable_branchDensity hIo.measurableSet hIm hD hinj
    (fun _ hx => hinj.leftInvOn_invFunOn hx) hd hqi.integrableOn
  have hwm : Measurable w := measurable_branchDensity_smooth hJ hIo hinj hd hqm
  have hmap := circle_branch_pushforward hq hq₀ hq₀s hqs hj hJ.continuous.measurable hJe
    hIo.measurableSet hIm hD hinj (fun _ hx => hinj.leftInvOn_invFunOn hx) hd
  apply positive_density_map_of_vectorMeasure (AddCircle.measurable_mk'.comp hj) hq
    (integrable_foldCircleDensity hwm hwi) hq0
    (foldCircleDensity_nonneg (branchDensity_nonneg hq00))
  rw [← foldCircleDensity_pushforward hwm hwi,← hmap]
  exact (vectorMeasure_map_comp _ hj AddCircle.measurable_mk').symm

lemma stationaryWeight_change_branch {A : ℝ → ℂ} {J : ℝ → ℝ} {C I : Set ℝ}
    (hIC : I ⊆ C) (hi : InjOn J C) (hs : support A ⊆ I) :
    stationaryWeight C J A = stationaryWeight I J A := by
  have h := stationaryWeight_family_of_branch (Ω := Unit) hIC hi (fun _ => hs)
  funext s
  have hh := congrFun h (s,())
  exact hh

/-- The density of a literal old angular packet, not an abstract probability
model. The integer speed carrier vanishes on the temporal circle. -/
theorem oldPacket_spectralDensity_of_modulus
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : ℝ → ℂ}
    {v : UnitAddCircle → ℝ} {V : ℝ → ℝ} {m c : ℤ} {o : ℝ} {C I : Set ℝ}
    (hA : Continuous A) (hA₀ : Continuous A₀)
    (hmod : ∀ u a, ‖A (u,a)‖ = ‖A (u,0)‖)
    (hAe : ∀ x ∈ Ioc o (o+1), A ((x:UnitAddCircle),0) = A₀ x)
    (has : support A₀ ⊆ Ioc o (o+1)) (hAs : support A₀ ⊆ I)
    (hv : Measurable v) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVe : ∀ x ∈ I, v (x:UnitAddCircle) = V x)
    (hIo : IsOpen I) (hIC : I ⊆ C) (hinj : InjOn (fun x => (m:ℝ)*V x) C)
    (hd : ∀ x ∈ I, deriv (fun x => (m:ℝ)*V x) x ≠ 0) :
    packetSpectralMeasure (fun a => ((v a-c:ℝ):UnitAddCircle)) m A =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal
        (foldCircleDensity (stationaryWeight C (fun x => (m:ℝ)*V x) A₀) z)) := by
  have hqc : Continuous (fun u : UnitAddCircle => ‖A (u,0)‖^2) :=
    ((hA.comp (continuous_id.prodMk continuous_const)).norm.pow 2)
  have hps := packetSpectralMeasure_of_modulus
    (φ := fun a => (((v a-(c:ℝ)) : ℝ):UnitAddCircle)) (j := m) (B := A)
    (q := fun u => ‖A (u,0)‖^2)
    (AddCircle.measurable_mk'.comp (hv.sub measurable_const)) hqc.measurable
    (fun p => by rw [hmod])
  rw [hps]
  have hmode (a : UnitAddCircle) : m • ((v a-c:ℝ):UnitAddCircle) = ((m:ℝ)*v a:UnitAddCircle) := by
    rw [← AddCircle.coe_zsmul]
    simp only [zsmul_eq_mul]
    rw [mul_sub]
    have he : ((m:ℝ)*(c:ℝ):UnitAddCircle) = 0 := by
      rw [← Int.cast_mul]
      exact (AddCircle.coe_eq_zero_iff 1).mpr ⟨m*c,by simp⟩
    rw [AddCircle.coe_sub,he,sub_zero]
  simp_rw [hmode]
  rw [stationaryWeight_change_branch hIC hinj hAs]
  apply positive_circle_branch_fold (q₀ := fun x => ‖A₀ x‖^2)
    (hqc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hA₀.norm.pow 2).measurable) (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
    (fun x hx => by rw [hAe x hx])
    (by intro x hx; apply has; intro hz; apply hx; simp [hz])
    (by intro x hx; apply hAs; intro hz; apply hx; simp [hz])
    (hv.const_mul (m:ℝ)) (contDiff_const.mul hV) (fun x hx => by rw [hVe x hx])
    hIo (hinj.mono hIC) hd

end ThreeTorus
end
end

section

/-! Actual old densities for amplitudes depending on both slow coordinates. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators ENNReal
namespace ThreeTorus

lemma continuous_slowMarginal {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) :
    Continuous (fun u => ∫ a, ‖A (u,a)‖^2 ∂AddCircle.haarAddCircle) := by
  have hc : Continuous (uncurry (fun (u a : UnitAddCircle) => ‖A (u,a)‖^2)) := hA.norm.pow 2
  simpa only [setIntegral_univ] using
    continuous_parametric_integral_of_continuous (X := UnitAddCircle) (Y := UnitAddCircle)
      (μ := AddCircle.haarAddCircle) hc isCompact_univ

lemma branchDensity_integral {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (I : Set ℝ) (J g D : ℝ → ℝ) (q : ℝ × Ω → ℝ) (s : ℝ) :
    branchDensity I J g D (fun u => ∫ a, q (u,a) ∂ν) s =
      ∫ a, branchDensity I J g D (fun u => q (u,a)) s ∂ν := by
  classical
  unfold branchDensity
  by_cases hs : s ∈ J '' I
  · simp only [Set.indicator_of_mem hs,integral_div]
  · simp only [Set.indicator_of_notMem hs,integral_zero]

end ThreeTorus
end
end

section

/-! The unchanged old spectral marginal, as a signed pushforward, for applying
L¹ contraction to physical cutoffs. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators ENNReal
namespace ThreeTorus

lemma signed_circle_branch_fold
    {q : UnitAddCircle → ℝ} {q₀ J₀ : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (hqm : Measurable q₀)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x:UnitAddCircle) = q₀ x)
    (hq₀s : support q₀ ⊆ Ioc o (o+1)) (hqs : support q₀ ⊆ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x:UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0) :
    Integrable (foldCircleDensity (branchDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀))
      AddCircle.haarAddCircle ∧
    (AddCircle.haarAddCircle.withDensityᵥ q).map (fun a => (J a:UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensityᵥ
        (foldCircleDensity (branchDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀)) := by
  let w := branchDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀
  have hqi : Integrable q₀ := by
    rw [← circleDensityLift_eq hq₀ hq₀s]
    exact integrable_circleDensityLift hq o
  have hD : ∀ x ∈ I, HasDerivWithinAt J₀ (deriv J₀ x) I x :=
    fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt
  have hIm := (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet
  have hwi : Integrable w := integrable_branchDensity hIo.measurableSet hIm hD hinj
    (fun _ hx => hinj.leftInvOn_invFunOn hx) hd hqi.integrableOn
  have hwm : Measurable w := measurable_branchDensity_smooth hJ hIo hinj hd hqm
  have hmap := circle_branch_pushforward hq hq₀ hq₀s hqs hj hJ.continuous.measurable hJe
    hIo.measurableSet hIm hD hinj (fun _ hx => hinj.leftInvOn_invFunOn hx) hd
  refine ⟨integrable_foldCircleDensity hwm hwi,?_⟩
  rw [← foldCircleDensity_pushforward hwm hwi,← hmap]
  exact (vectorMeasure_map_comp _ hj AddCircle.measurable_mk').symm

theorem oldStationaryMarginal_map
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {v : UnitAddCircle → ℝ} {V : ℝ → ℝ} {m : ℤ} {o : ℝ} {C I : Set ℝ}
    (hA : Continuous A) (hA₀ : Continuous A₀.uncurry)
    (hAe : ∀ a x, x ∈ Ioc o (o+1) → A ((x:UnitAddCircle),a) = A₀ a x)
    (has : ∀ a, support (A₀ a) ⊆ Ioc o (o+1)) (hAs : ∀ a, support (A₀ a) ⊆ I)
    (hv : Measurable v) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVe : ∀ x ∈ I, v (x:UnitAddCircle) = V x)
    (hIo : IsOpen I) (hIC : I ⊆ C) (hinj : InjOn (fun x => (m:ℝ)*V x) C)
    (hd : ∀ x ∈ I, deriv (fun x => (m:ℝ)*V x) x ≠ 0) :
    let p := foldCircleDensity (fun s => ∫ a, stationaryWeight C (fun x => (m:ℝ)*V x)
      (A₀ a) s ∂AddCircle.haarAddCircle)
    Integrable p AddCircle.haarAddCircle ∧
      (AddCircle.haarAddCircle.withDensityᵥ (fun u => ∫ a, ‖A (u,a)‖^2
        ∂AddCircle.haarAddCircle)).map (fun u => (((m:ℝ)*v u : ℝ):UnitAddCircle)) =
          AddCircle.haarAddCircle.withDensityᵥ p := by
  dsimp only
  let q : UnitAddCircle → ℝ := fun u => ∫ a, ‖A (u,a)‖^2 ∂AddCircle.haarAddCircle
  let q₀ : ℝ → ℝ := fun x => ∫ a, ‖A₀ a x‖^2 ∂AddCircle.haarAddCircle
  have hqc : Continuous q := continuous_slowMarginal hA
  have hq₀c : Continuous q₀ := by
    have hc : Continuous (uncurry (fun (x : ℝ) (a : UnitAddCircle) => ‖A₀ a x‖^2)) :=
      (hA₀.comp continuous_swap).norm.pow 2
    simpa only [q₀,setIntegral_univ] using
      continuous_parametric_integral_of_continuous (X := ℝ) (Y := UnitAddCircle)
        (μ := AddCircle.haarAddCircle) hc isCompact_univ
  have hs (K : Set ℝ) (hK : ∀ a, support (A₀ a) ⊆ K) : support q₀ ⊆ K := by
    intro x hx
    by_contra hnot
    apply hx
    have hz (a : UnitAddCircle) : A₀ a x = 0 := by
      by_contra hn
      exact hnot (hK a hn)
    simp only [q₀,hz,norm_zero,zero_pow (by decide : 2 ≠ 0),integral_zero]
  have hb : branchDensity I (fun x => (m:ℝ)*V x)
      (invFunOn (fun x => (m:ℝ)*V x) I) (deriv (fun x => (m:ℝ)*V x)) q₀ =
      fun s => ∫ a, stationaryWeight C (fun x => (m:ℝ)*V x) (A₀ a) s
        ∂AddCircle.haarAddCircle := by
    funext s
    rw [show q₀ = fun x => ∫ a, ‖A₀ a x‖^2 ∂AddCircle.haarAddCircle from rfl,
      branchDensity_integral (q := fun p : ℝ × UnitAddCircle => ‖A₀ p.2 p.1‖^2)]
    apply integral_congr_ae
    filter_upwards [] with a
    exact congrFun (stationaryWeight_change_branch hIC hinj (hAs a)).symm s
  rw [← hb]
  exact signed_circle_branch_fold
    (hqc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    hq₀c.measurable
    (fun x hx => integral_congr_ae (ae_of_all _ (fun a => by dsimp only; rw [hAe a x hx])))
    (hs _ has) (hs _ hAs) (hv.const_mul (m:ℝ)) (contDiff_const.mul hV)
    (fun x hx => by rw [hVe x hx]) hIo (hinj.mono hIC) hd

end ThreeTorus
end
end

section

/-! The neutral passage's old cutoff reference differs from the actual old
packet density by at most its physical missing mass. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma cutoff_slowMarginal_l1
    {A : UnitAddCircle × UnitAddCircle → ℂ} {ψ : UnitAddCircle → ℝ}
    (hA : Continuous A) (hψc : Continuous ψ) (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1)
    {B : ℝ} (_hB : 0 ≤ B) (hAb : ∀ p, ‖A p‖^2 ≤ B) :
    (∫ u, |(∫ a, ‖A (u,a)‖^2 ∂AddCircle.haarAddCircle)-
      (∫ a, ‖(ψ a:ℂ)*A (u,a)‖^2 ∂AddCircle.haarAddCircle)| ∂AddCircle.haarAddCircle) ≤
      B*(∫ a, (1-ψ a^2) ∂AddCircle.haarAddCircle) := by
  let D := B*(∫ a, (1-ψ a^2) ∂AddCircle.haarAddCircle)
  have hd : ∀ u, |(∫ a, ‖A (u,a)‖^2 ∂AddCircle.haarAddCircle)-
      (∫ a, ‖(ψ a:ℂ)*A (u,a)‖^2 ∂AddCircle.haarAddCircle)| ≤ D := by
    intro u
    have ha : Continuous (fun a => ‖A (u,a)‖^2) :=
      (hA.comp (continuous_const.prodMk continuous_id)).norm.pow 2
    have hap : Continuous (fun a => ‖(ψ a:ℂ)*A (u,a)‖^2) :=
      ((Complex.continuous_ofReal.comp hψc).mul
        (hA.comp (continuous_const.prodMk continuous_id))).norm.pow 2
    have hc : Continuous (fun a => ‖A (u,a)‖^2-‖(ψ a:ℂ)*A (u,a)‖^2) := ha.sub hap
    have he (a : UnitAddCircle) : ‖A (u,a)‖^2-‖(ψ a:ℂ)*A (u,a)‖^2 =
        (1-ψ a^2)*‖A (u,a)‖^2 := by
      simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
      ring
    have hz (a : UnitAddCircle) : 0 ≤ ‖A (u,a)‖^2-‖(ψ a:ℂ)*A (u,a)‖^2 := by
      rw [he]
      exact mul_nonneg (by nlinarith [(hψ a).1,(hψ a).2]) (sq_nonneg _)
    rw [← integral_sub (ha.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hap.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      abs_of_nonneg (integral_nonneg hz)]
    have hbound : Continuous (fun a => B*(1-ψ a^2)) :=
      continuous_const.mul (continuous_const.sub (hψc.pow 2))
    calc
      _ ≤ ∫ a, B*(1-ψ a^2) ∂AddCircle.haarAddCircle := by
        apply integral_mono (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          (hbound.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        intro a
        dsimp only
        rw [he,mul_comm B]
        exact mul_le_mul_of_nonneg_left (hAb _) (by nlinarith [(hψ a).1,(hψ a).2])
      _ = D := by rw [integral_const_mul]
  calc
    _ ≤ ∫ _ : UnitAddCircle, D ∂AddCircle.haarAddCircle := by
      exact integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _)) (integrable_const D)
        (ae_of_all _ hd)
    _ = _ := by simp [D]

/-- The reference in the neutral Riemann estimate is genuinely the cutoff
old spectrum. Its loss is bounded independently of slope, residue modulus or
passage integer. -/
theorem oldStationaryMarginal_cutoff_l1
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {v : UnitAddCircle → ℝ} {V : ℝ → ℝ} {m : ℤ} {o : ℝ} {C I : Set ℝ}
    (hA : Continuous A) (hA₀ : Continuous A₀.uncurry)
    (hAe : ∀ a x, x ∈ Ioc o (o+1) → A ((x:UnitAddCircle),a) = A₀ a x)
    (has : ∀ a, support (A₀ a) ⊆ Ioc o (o+1)) (hAs : ∀ a, support (A₀ a) ⊆ I)
    (hv : Measurable v) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVe : ∀ x ∈ I, v (x:UnitAddCircle) = V x)
    (hIo : IsOpen I) (hIC : I ⊆ C) (hinj : InjOn (fun x => (m:ℝ)*V x) C)
    (hd : ∀ x ∈ I, deriv (fun x => (m:ℝ)*V x) x ≠ 0)
    {ψ : UnitAddCircle → ℝ} (hψc : Continuous ψ) (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (hAb : ∀ p, ‖A p‖^2 ≤ B) :
    let p := foldCircleDensity (fun s => ∫ a, stationaryWeight C (fun x => (m:ℝ)*V x)
      (A₀ a) s ∂AddCircle.haarAddCircle)
    let pψ := foldCircleDensity (fun s => ∫ a, stationaryWeight C (fun x => (m:ℝ)*V x)
      (fun x => (ψ a:ℂ)*A₀ a x) s ∂AddCircle.haarAddCircle)
    (∫ z, |pψ z-p z| ∂AddCircle.haarAddCircle) ≤
      B*(∫ a, (1-ψ a^2) ∂AddCircle.haarAddCircle) := by
  dsimp only
  let Aψ : UnitAddCircle × UnitAddCircle → ℂ := fun p => (ψ p.2:ℂ)*A p
  let A₀ψ : UnitAddCircle → ℝ → ℂ := fun a x => (ψ a:ℂ)*A₀ a x
  have hAψ : Continuous Aψ := ((Complex.continuous_ofReal.comp hψc).comp continuous_snd).mul hA
  have hA₀ψ : Continuous A₀ψ.uncurry :=
    ((Complex.continuous_ofReal.comp hψc).comp continuous_fst).mul hA₀
  have hs (K : Set ℝ) (hK : ∀ a, support (A₀ a) ⊆ K) : ∀ a, support (A₀ψ a) ⊆ K := by
    intro a x hx
    exact hK a (right_ne_zero_of_mul hx)
  have he : ∀ a x, x ∈ Ioc o (o+1) → Aψ ((x:UnitAddCircle),a) = A₀ψ a x := by
    intro a x hx
    dsimp only [Aψ,A₀ψ]
    rw [hAe a x hx]
  obtain ⟨hpi,hmap⟩ := oldStationaryMarginal_map hA hA₀ hAe has hAs hv hV hVe hIo hIC hinj hd
  obtain ⟨hψi,hψmap⟩ := oldStationaryMarginal_map hAψ hA₀ψ he (hs _ has) (hs _ hAs)
    hv hV hVe hIo hIC hinj hd
  have hq := continuous_slowMarginal hA
  have hqψ := continuous_slowMarginal hAψ
  have hb := l1_pushforward_difference
    (hqψ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hψi hpi
    (AddCircle.measurable_mk'.comp (hv.const_mul (m:ℝ))) hψmap hmap
  refine hb.trans ?_
  simp only [Aψ,abs_sub_comm]
  exact cutoff_slowMarginal_l1 hA hψc hψ hB hAb

end ThreeTorus
end
end

section

/-! Quantitative physical and spectral conclusions for the same actual packet.
This is the analytic (not yet geometric finite-stage) transmission boundary. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators FourierTransform
namespace ThreeTorus

lemma continuous_passageChart {H : UnitAddCircle → UnitAddCircle} (hH : Continuous H) :
    Continuous (passageChart H) := by
  change Continuous (fun x : TripleTorus => (x.2.1,x.2.2,x.1+(-H x.2.1)))
  exact continuous_snd.fst.prodMk (continuous_snd.snd.prodMk
    (continuous_fst.add (hH.comp continuous_snd.fst).neg))

end ThreeTorus
end
end

section

/-! Quantitative good-arc cutoff losses for genuine two-coordinate amplitudes.
This does not presume spare-coordinate independence. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma stationaryCutoffLift_marginal {A : UnitAddCircle → ℝ → ℂ}
    {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ} {o : ℝ}
    (heψ : ∀ x ∈ Ioc o (o+1), ψ₀ x = ψ (x:UnitAddCircle))
    (hsψ : support ψ₀ ⊆ Ioc o (o+1)) (C : Set ℝ) (J : ℝ → ℝ) (s : ℝ) :
    (∫ a : ℝ, stationaryCutoffLift C J
      (fun p : ℝ × ℝ => A (p.2:UnitAddCircle) p.1) ψ₀ (a,s)) =
      ∫ a, stationaryWeight C J (fun x => (ψ a:ℂ)*A a x) s ∂AddCircle.haarAddCircle := by
  let q : UnitAddCircle → ℝ := fun a => ψ a^2*stationaryWeight C J (A a) s
  have he : circleDensityLift o q = fun a => stationaryCutoffLift C J
      (fun p : ℝ × ℝ => A (p.2:UnitAddCircle) p.1) ψ₀ (a,s) := by
    apply circleDensityLift_eq
    · intro x hx
      simp only [q,stationaryCutoffLift,heψ x hx]
    · intro x hx
      apply hsψ
      intro hz
      exact hx (by simp [stationaryCutoffLift,hz])
  rw [← he,circle_integral_lift]
  apply integral_congr_ae
  filter_upwards [] with a
  rw [stationaryWeight_mul]
  simp [q,Complex.norm_real,Real.norm_eq_abs,sq_abs]

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageFamilies
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rounded common primitives, neutral and quantile families, exact indices, signal passages, and support tracking. -/

section

/-! The exact family of passage primitives used by the analytic estimates is
constructed from a periodic speed. The rounding is chosen before any jitter.
No smoothness or perturbation conclusion is assumed. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology
namespace ThreeTorus

lemma deriv_real_primitive {V : ℝ → ℝ} (hV : Continuous V) :
    deriv (fun x => ∫ t in 0..x, V t) = V := by
  funext x
  exact (intervalIntegral.integral_hasDerivAt_right (hV.intervalIntegrable 0 x)
    hV.aestronglyMeasurable.stronglyMeasurableAtFilter hV.continuousAt).deriv

/-- One integer-rounded primitive sequence works for every later choice of jitter.
In particular the estimates for a finite list can all use exactly this sequence. -/
theorem exists_rounded_primitive_family {V : ℝ → ℝ}
    (hp : Periodic V 1) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) :
    ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      (∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹) ∧ Tendsto Δ atTop (𝓝 0) ∧
      (∀ n, Continuous (H n)) ∧
      (∀ n (x : ℝ), H n (x:UnitAddCircle) =
        ((n:ℝ)*((∫ t in 0..x, V t)+Δ n*x):UnitAddCircle)) ∧
      ∀ J : ℝ → ℝ, ∀ hJp : Periodic J 1,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J →
        let σ := fun (n : ℕ) (a : UnitAddCircle) => (((1+hJp.lift a/(n:ℝ))/(n:ℝ):ℝ):UnitAddCircle)
        (∀ n, Smooth (torusPassage (H n) (σ n)) ∧
          Smooth (torusPassage (H n) (σ n)).symm ∧
          MeasurePreserving (torusPassage (H n) (σ n)) μ μ) ∧
        (∀ n, 0 < n → ∀ x : Cover,
          torusPassage (H n) (σ n) (project x) =
            project (passageFamily V J 1 ((n:ℝ)⁻¹,Δ n) x) ∧
          (torusPassage (H n) (σ n)).symm (project x) =
            project (passageFamily V J (-1) ((n:ℝ)⁻¹,Δ n) x)) ∧
        ∀ r : ℝ, ∀ K : Set Cover, IsCompact K → ∀ d : ℕ,
          TendstoUniformlyOn
            (fun (n : ℕ) x => iteratedFDeriv ℝ d (passageFamily V J r ((n:ℝ)⁻¹,Δ n)) x)
            (fun x => iteratedFDeriv ℝ d (fun y : Cover => ![y 0+r*V (y 1),y 1,y 2]) x)
            atTop K := by
  classical
  have hr : ∀ n : ℕ, ∃ d : ℝ, ∃ k : ℤ,
      (0 < n → |d| ≤ (n:ℝ)⁻¹) ∧ (n:ℝ)*((∫ t in 0..1, V t)+d) = k := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨d,k,hd,hk⟩ := passage_rounding (∫ t in 0..1, V t) hn
      exact ⟨d,k,fun _ => hd,hk⟩
    · have he : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      exact ⟨0,0,by simp⟩
  choose Δ k hΔ hk using hr
  have hsp (n : ℕ) : Periodic (fun x => (n:ℝ)*(V x+Δ n)) 1 :=
    (passage_rounded_slope hp hV.continuous n (Δ n) (hk n)).1
  have hsi (n : ℕ) : (∫ t in 0..1, (n:ℝ)*(V t+Δ n)) = k n :=
    (passage_rounded_slope hp hV.continuous n (Δ n) (hk n)).2
  have hsc (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (n:ℝ)*(V x+Δ n)) :=
    contDiff_const.mul (hV.add contDiff_const)
  let H n := circlePrimitive (hsp n) (hsc n).continuous (hsi n)
  have hHe (n : ℕ) (x : ℝ) : H n (x:UnitAddCircle) =
      ((n:ℝ)*((∫ t in 0..x, V t)+Δ n*x):UnitAddCircle) := by
    rw [show H n (x:UnitAddCircle) = (((∫ t in 0..x, (n:ℝ)*(V t+Δ n)):ℝ):UnitAddCircle) from rfl]
    congr 1
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hV.continuous.intervalIntegrable 0 x) intervalIntegrable_const]
    simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
    ring
  refine ⟨Δ,H,hΔ,(continuous_snd.tendsto (0,0)).comp (passage_parameters_tendsto hΔ),
    fun n => continuous_circlePrimitive (hsp n) (hsc n).continuous (hsi n),hHe,?_⟩
  intro J hJp hJ
  let σ := fun (n : ℕ) (a : UnitAddCircle) => (((1+hJp.lift a/(n:ℝ))/(n:ℝ):ℝ):UnitAddCircle)
  have htsp (n : ℕ) : Periodic (fun a => (n:ℝ)⁻¹+(n:ℝ)⁻¹^2*J a) 1 := by
    intro a
    dsimp only
    rw [hJp a]
  have hσ (n : ℕ) : σ n = circleSpeed (htsp n) := by
    funext a
    induction a using QuotientAddGroup.induction_on with
    | H a =>
      change (((1+J a/(n:ℝ))/(n:ℝ):ℝ):UnitAddCircle) =
        ((((n:ℝ)⁻¹+(n:ℝ)⁻¹^2*J a):ℝ):UnitAddCircle)
      congr 1
      simp only [div_eq_mul_inv]
      ring
  refine ⟨?_,?_,?_⟩
  · intro n
    change Smooth (torusPassage (H n) (σ n)) ∧
      Smooth (torusPassage (H n) (σ n)).symm ∧
      MeasurePreserving (torusPassage (H n) (σ n)) μ μ
    rw [hσ]
    exact primitive_passage_properties (hsp n) (htsp n) (hsc n) (passage_speed_smooth hJ n) (hsi n)
  · intro n hn x
    change torusPassage (H n) (σ n) (project x) =
        project (passageFamily V J 1 ((n:ℝ)⁻¹,Δ n) x) ∧
      (torusPassage (H n) (σ n)).symm (project x) =
        project (passageFamily V J (-1) ((n:ℝ)⁻¹,Δ n) x)
    rw [hσ]
    have Hlift (u : ℝ) : H n (u:UnitAddCircle) =
        (((∫ t in 0..u, (n:ℝ)*(V t+Δ n)):ℝ):UnitAddCircle) := rfl
    have hgraphs : torusPassage (H n) (circleSpeed (htsp n)) (project x) =
          project (passageLift (fun u => ∫ t in 0..u, (n:ℝ)*(V t+Δ n))
            (fun a => (n:ℝ)⁻¹+(n:ℝ)⁻¹^2*J a) x) ∧
        (torusPassage (H n) (circleSpeed (htsp n))).symm (project x) =
          project (passageInverseLift (fun u => ∫ t in 0..u, (n:ℝ)*(V t+Δ n))
            (fun a => (n:ℝ)⁻¹+(n:ℝ)⁻¹^2*J a) x) := by
      constructor
      · rw [torusPassage_apply]
        ext i
        fin_cases i <;> simp only [project,passageLift,circleSpeed_coe,
          ← AddCircle.coe_add,Hlift,← AddCircle.coe_sub] <;> rfl
      · rw [torusPassage_symm_apply]
        ext i
        fin_cases i <;> simp only [project,passageInverseLift,circleSpeed_coe,
          ← AddCircle.coe_add,Hlift,← AddCircle.coe_sub] <;> rfl
    rw [(passageLift_eq_family (J := J) hV.continuous hn (Δ n)).1,
      (passageLift_eq_family (J := J) hV.continuous hn (Δ n)).2] at hgraphs
    exact hgraphs
  · intro r K hK d
    exact passage_Cinfty_limit hV hJ hΔ r hK d

end ThreeTorus
end
end

section

/-! Removing the identically zero retained modes does not alter either the
physical vector or its literal temporal density. This bridges the asymptotic
finite-retention producer and the exact finite index separations. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma sum_eq_of_zero_off {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (f : α → M) (S T : Finset α)
    (hS : ∀ j, j ∉ S → f j = 0) (hT : ∀ j, j ∉ T → f j = 0) :
    ∑ j ∈ S, f j = ∑ j ∈ T, f j := by
  have eS : ∑ j ∈ S ∩ T, f j = ∑ j ∈ S, f j := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro j hj hn
    exact hT j (fun ht => hn (Finset.mem_inter.mpr ⟨hj,ht⟩))
  have eT : ∑ j ∈ S ∩ T, f j = ∑ j ∈ T, f j := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro j hj hn
    exact hS j (fun hs => hn (Finset.mem_inter.mpr ⟨hs,hj⟩))
  exact eS.symm.trans eT

lemma retainedPassage_eq_of_cover (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (S T : Finset ℤ)
    (χ : ℤ → UnitAddCircle → ℝ) (ψ : UnitAddCircle → ℝ)
    (hS : ∀ j, j ∉ S → ∀ a, χ j a = 0) (hT : ∀ j, j ∉ T → ∀ a, χ j a = 0) :
    retainedPassage m H A S χ ψ = retainedPassage m H A T χ ψ := by
  funext x
  apply sum_eq_of_zero_off
  · intro j hj
    simp [hS j hj]
  · intro j hj
    simp [hT j hj]

lemma exactRetainedPacketDensity_eq_of_cover
    (I : Set ℝ) (J₀ : ℝ → ℝ) (ψ : UnitAddCircle → ℝ)
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (S T : Finset ℤ) (n : ℕ)
    (hS : ∀ j, j ∉ S → ∀ a, χ ((j:ℝ)/n) a = 0)
    (hT : ∀ j, j ∉ T → ∀ a, χ ((j:ℝ)/n) a = 0) :
    exactRetainedPacketDensity I J₀ ψ χ m H A S n =
      exactRetainedPacketDensity I J₀ ψ χ m H A T n := by
  unfold exactRetainedPacketDensity
  congr 1
  funext t
  apply sum_eq_of_zero_off
  · intro j hj
    simp [unfoldedModeDensity,scaledBranchKernel,branchDensity,
      circleDensityLift,retainedCircleWeight,hS j hj]
  · intro j hj
    simp [unfoldedModeDensity,scaledBranchKernel,branchDensity,
      circleDensityLift,retainedCircleWeight,hT j hj]

/-- The exact finite sampling set, with no identically zero extra modes. -/
theorem cylinder_cutoff_exact_indices {ι : Type*}
    (χ : ι → ℝ → UnitAddCircle → ℝ)
    (hc : ∀ i, HasCompactSupport (χ i).uncurry) (hz : ∀ i a, χ i 0 a = 0) :
    ∃ S : ℕ → ι → Finset ℤ,
      (∀ n i j, j ∈ S n i → j ≠ 0) ∧
      ∀ n, 0 < n → ∀ i j, j ∈ S n i ↔ ∃ a, χ i ((j:ℝ)/n) a ≠ 0 := by
  classical
  have hex (n : ℕ) (i : ι) : ∃ S : Finset ℤ,
      (∀ j ∈ S, j ≠ 0) ∧
      (0 < n → ∀ j, j ∈ S ↔ ∃ a, χ i ((j:ℝ)/n) a ≠ 0) := by
    by_cases hn : 0 < n
    · obtain ⟨S,hS,hS'⟩ := cylinder_cutoff_finite_indices (hc i) (hz i) n hn
      refine ⟨S.filter (fun j => ∃ a, χ i ((j:ℝ)/n) a ≠ 0),?_,?_⟩
      · intro j hj hz
        subst j
        exact hS (Finset.mem_filter.mp hj).1
      · intro _ j
        constructor
        · exact fun hj => (Finset.mem_filter.mp hj).2
        · intro hj
          refine Finset.mem_filter.mpr ⟨?_,hj⟩
          by_contra hh
          obtain ⟨a,ha⟩ := hj
          exact ha (hS' j hh a)
    · exact ⟨∅,by simp,fun hh => (hn hh).elim⟩
  choose S hS hSe using hex
  exact ⟨S,hS,fun n hn i => hSe n i hn⟩

end ThreeTorus
end
end

section

/-! Closure of the literal output coefficient class under a passage.
The next passage uses these very coefficients, rather than new placeholders. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma retainedRealCore_smooth {ψ₀ : ℝ → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {m : ℤ} {H : UnitAddCircle → UnitAddCircle} {Hl : ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hχ : CylinderSmooth χ.uncurry)
    (hHl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Hl)
    (hH : ∀ t : ℝ, H (t:UnitAddCircle) = (Hl t:UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (s : ℝ) (j : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (retainedRealCore ψ₀ χ m H A s j) := by
  have hχ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => χ s (u:UnitAddCircle)) :=
    hχ.comp (contDiff_const.prodMk contDiff_id)
  exact ((Complex.ofRealCLM.contDiff.comp hψ).mul
    (Complex.ofRealCLM.contDiff.comp hχ')).mul (smooth_exactPassageCoeff hHl hH hA j)

lemma retainedRealAmplitude_support (ψ₀ : ℝ → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (s : ℝ) (j : ℤ) (b : UnitAddCircle) :
    support (retainedRealAmplitude ψ₀ χ m H A s j b) ⊆ support ψ₀ := by
  intro u hu hz
  exact hu (by simp [retainedRealAmplitude,retainedRealCore,hz])

/-- Every analytic lift condition required by the next stationary-phase
passage follows from the smooth real core and the spare character. -/
lemma retainedRealAmplitude_regular {C : ℝ → ℂ}
    (hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) C) (m : ℤ) :
    (∀ b : UnitAddCircle, ContDiff ℝ 2 (fun u : ℝ => C u*fourier m b)) ∧
    Continuous (fun p : UnitAddCircle × ℝ => C p.2*fourier m p.1) ∧
    Continuous (fun p : UnitAddCircle × ℝ => deriv (fun u : ℝ => C u*fourier m p.1) p.2) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => C p.1*fourier m (p.2:UnitAddCircle)) := by
  refine ⟨fun _ => (hC.mul contDiff_const).of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)),
    (hC.continuous.comp continuous_snd).mul ((fourier m).continuous.comp continuous_fst),?_,
    (hC.comp contDiff_fst).mul ((smooth_fourier_lift m).comp contDiff_snd)⟩
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv C) :=
    (contDiff_infty_iff_deriv.mp hC).2
  have he (p : UnitAddCircle × ℝ) : deriv (fun u : ℝ => C u*fourier m p.1) p.2 =
      deriv C p.2*fourier m p.1 := deriv_mul_const (hC.differentiable (by simp) p.2) _
  simp_rw [he]
  exact (hD.continuous.comp continuous_snd).mul ((fourier m).continuous.comp continuous_fst)

lemma retainedRealAmplitude_matches {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) {o : ℝ}
    (he : ∀ u ∈ Ioc o (o+1), ψ (u:UnitAddCircle) = ψ₀ u) :
    ∀ b u, u ∈ Ioc o (o+1) →
      retainedAmplitude ψ χ m H A n j ((u:UnitAddCircle),b) =
        retainedRealAmplitude ψ₀ χ m (H n) A ((j:ℝ)/n) j b u := by
  intro b u hu
  simp only [retainedAmplitude,retainedRealAmplitude,retainedRealCore,he u hu]

lemma retainedAmplitude_smooth_lift
    {ψ : UnitAddCircle → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {m : ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle} {Hl : ℕ → ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => ψ u))
    (hχ : CylinderSmooth χ.uncurry)
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hH : ∀ n (t : ℝ), H n (t:UnitAddCircle) = (Hl n t:UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (n : ℕ) (j : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => retainedAmplitude ψ χ m H A n j (p.1,p.2)) := by
  have hs := smooth_retained_amplitude (m := m) (j := j) ((j:ℝ)/n) (hHl n) (hH n) hA hχ hψ
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  dsimp [retainedAmplitude]
  ring

end ThreeTorus

namespace ThreeTorus
open Set

/-- The buffered real integration interval can always be fixed before the
next passage integer, even when all the coefficients are zero. -/
lemma compact_inside_buffered_interval {K : Set ℝ} {a b : ℝ}
    (hK : IsCompact K) (hab : a < b) (hKI : K ⊆ Ioo a b) :
    ∃ l u R : ℝ, a < l ∧ l < u ∧ u < b ∧ 0 < R ∧
      K ⊆ Ioc l u ∧ Icc (l-2*R) (u+2*R) ⊆ Ioo a b := by
  let K' := insert ((a+b)/2) K
  have hc : IsCompact K' := hK.insert _
  have hsub : K' ⊆ Ioo a b := by
    intro x hx
    rcases mem_insert_iff.mp hx with rfl | hx
    · constructor <;> linarith
    · exact hKI hx
  obtain ⟨x,hx,hmin⟩ := hc.exists_isMinOn (insert_nonempty _ _) continuous_id.continuousOn
  obtain ⟨y,hy,hmax⟩ := hc.exists_isMaxOn (insert_nonempty _ _) continuous_id.continuousOn
  have hx' := hsub hx
  have hy' := hsub hy
  have hxy : x ≤ y := hmin hy
  let l := (a+x)/2
  let u := (y+b)/2
  have hal : a < l := by dsimp [l]; linarith [hx'.1]
  have hlu : l < u := by dsimp [l,u]; linarith [hx'.1,hy'.2]
  have hub : u < b := by dsimp [u]; linarith [hy'.2]
  let R := min (l-a) (b-u)/4
  have hR : 0 < R := div_pos (lt_min (sub_pos.mpr hal) (sub_pos.mpr hub)) (by norm_num)
  have hR₁ : 4*R ≤ l-a := by dsimp [R]; linarith [min_le_left (l-a) (b-u)]
  have hR₂ : 4*R ≤ b-u := by dsimp [R]; linarith [min_le_right (l-a) (b-u)]
  refine ⟨l,u,R,hal,hlu,hub,hR,?_,?_⟩
  · intro z hz
    have hz' : z ∈ K' := mem_insert_of_mem _ hz
    have hminz := hmin hz'
    have hmaxz := hmax hz'
    constructor <;> dsimp [l,u] at * <;> linarith
  · intro z hz
    constructor <;> linarith [hz.1,hz.2]

end ThreeTorus
end
end

section

/-! A concrete closed class for finite passage iteration.  The constructor
below uses the literal retained amplitudes; it does not postulate a next
packet state or any of its analytic regularity. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma smooth_new_speed {J : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => (1+J u/n)/n) :=
  (contDiff_const.add (hJ.div_const _)).div_const _

lemma positive_deriv_new_speed {J : ℝ → ℝ} {n : ℕ} {x : ℝ}
    (hn : 0 < n) (hd : 0 < deriv J x) :
    0 < deriv (fun u => (1+J u/n)/n) x := by
  simpa only [deriv_div_const,deriv_const_add] using
    div_pos (div_pos hd (show (0:ℝ)<n by exact_mod_cast hn)) (show (0:ℝ)<n by exact_mod_cast hn)

/-- A neutral or quantile passage produces a valid input family for the next
passage, with all real lifts supported in one common compact good interval.
The jitter may be arbitrarily broad. The constructor works at EVERY positive
passage integer, independently of the spectral/physical approximation bounds. -/
theorem literal_output_packets {ι : Type*} [Fintype ι]
    (m : ι → ℤ) (A : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (H : ℕ → UnitAddCircle → UnitAddCircle) (Hl : ℕ → ℝ → ℝ)
    (χ : ι → ℝ → UnitAddCircle → ℝ) (S : ι → Finset ℤ)
    (hS : ∀ i j, j ∈ S i → j ≠ 0)
    (hAc : ∀ i, Continuous (A i))
    (hAs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A i (p.1,p.2)))
    (hχ : ∀ i, CylinderSmooth (χ i).uncurry) (hχc : ∀ i, Continuous (χ i).uncurry)
    (hHc : ∀ n, Continuous (H n))
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hHe : ∀ n (x : ℝ), H n (x:UnitAddCircle) = (Hl n x:UnitAddCircle))
    {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
    {J : ℝ → ℝ} (hpJ : Periodic J 1) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hdJ : ∀ x ∈ Ioo δ (1-δ), 0 < deriv J x) {n : ℕ} (hn : 0 < n) :
    ∃ F : PassagePackets (PassageOutputIndex S),
      (∀ i, F.m i = i.2.val) ∧
      (∀ i, F.A i = retainedAmplitude (neutralCircleCutoff c) (χ i.1) (m i.1) H (A i.1) n i.2.val) ∧
      (∀ i, F.A₀ i = retainedRealAmplitude c.ψ (χ i.1) (m i.1) (H n) (A i.1)
        ((i.2.val:ℝ)/n) i.2.val) ∧
      F.V = (fun x => (1+J x/n)/n) ∧ F.o = 0 ∧
      δ < F.l ∧ F.u < 1-δ ∧ F.SpareIndependent := by
  obtain ⟨l,u,R,hδl,hlu,huδ,hR,hKI,hbuffer⟩ := compact_inside_buffered_interval
    c.ψ_compact (by linarith : δ < 1-δ) c.ψ_support
  let ψ := neutralCircleCutoff c
  have hψs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => ψ x) := by
    simp only [ψ,neutralCircleCutoff_coe]
    exact contDiff_periodize c.ψ_smooth c.ψ_compact
  have hψe : ∀ x ∈ Ioc (0:ℝ) (0+1), ψ (x:UnitAddCircle) = c.ψ x := by
    intro x hx
    rw [show ψ (x:UnitAddCircle) = lawPsi c x from neutralCircleCutoff_coe c x]
    exact periodize_eq_on_unit ((subset_tsupport c.ψ).trans
      (c.ψ_support.trans (by intro z hz; constructor <;> linarith [hz.1,hz.2]))) ⟨hx.1.le,by simpa using hx.2⟩
  let A' (i : PassageOutputIndex S) := retainedAmplitude ψ (χ i.1) (m i.1) H (A i.1) n i.2.val
  let A₀' (i : PassageOutputIndex S) := retainedRealAmplitude c.ψ (χ i.1) (m i.1) (H n) (A i.1)
    ((i.2.val:ℝ)/n) i.2.val
  have hcore (i : PassageOutputIndex S) := retainedRealCore_smooth (m := m i.1) c.ψ_smooth (hχ i.1)
    (hHl n) (hHe n) (hAs i.1) ((i.2.val:ℝ)/n) i.2.val
  have hreg (i : PassageOutputIndex S) := retainedRealAmplitude_regular (hcore i) (m i.1)
  have hA' i : Continuous (A' i) := by
    dsimp [A',retainedAmplitude]
    exact (((Complex.continuous_ofReal.comp ((continuous_neutralCircleCutoff c).comp continuous_fst)).mul
      (Complex.continuous_ofReal.comp ((hχc i.1).comp (continuous_const.prodMk continuous_fst)))).mul
      ((continuous_exactPassageCoeff (hHc n) (hAc i.1) _).comp continuous_fst)).mul
      ((fourier (m i.1)).continuous.comp continuous_snd)
  let F : PassagePackets (PassageOutputIndex S) := {
    m := fun i => i.2.val
    nonzero := fun i => hS i.1 i.2.val i.2.property
    A := A'
    A₀ := A₀'
    o := 0
    l := l
    u := u
    R := R
    lo := hδ.le.trans hδl.le
    uo := by linarith
    lu := hlu.le
    Rpos := hR
    lift_matches := fun i => retainedRealAmplitude_matches (χ i.1) (m i.1) H (A i.1) n i.2.val hψe
    two := fun i => (hreg i).1
    continuous_lift := fun i => (hreg i).2.1
    continuous_deriv := fun i => (hreg i).2.2.1
    smooth_lift := fun i => (hreg i).2.2.2
    support_lift := fun i a => (retainedRealAmplitude_support _ _ _ _ _ _ _ a).trans
      ((subset_tsupport c.ψ).trans hKI)
    continuous_amplitude := hA'
    smooth_amplitude := fun i => retainedAmplitude_smooth_lift hψs (hχ i.1) hHl hHe (hAs i.1) n i.2.val
    V := fun x => (1+J x/n)/n
    periodic := fun x => by dsimp; rw [hpJ x]
    smooth_speed := smooth_new_speed hJ n
    positive_deriv := fun x hx => positive_deriv_new_speed hn (hdJ x (hbuffer hx)) }
  refine ⟨F,fun _ => rfl,fun _ => rfl,fun _ => rfl,rfl,rfl,hδl,huδ,?_,?_⟩
  · intro i a x
    dsimp [F,A₀',retainedRealAmplitude]
    simp only [norm_mul, Circle.norm_coe]
  · intro i v a
    exact retainedAmplitude_modulus ψ (χ i.1) (m i.1) H (A i.1) n i.2.val v a

lemma output_index_injective {ι : Type*} {S : ι → Finset ℤ}
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) :
    Injective (fun i : PassageOutputIndex S => i.2.val) := by
  intro i j he
  have hij : i.1 = j.1 := by
    by_contra h
    exact Finset.disjoint_left.mp (hd h) i.2.property (by simpa only [he] using j.2.property)
  cases i with
  | mk i k =>
    cases j with
    | mk j l =>
      dsimp at hij he
      subst j
      exact congrArg (Sigma.mk i) (Subtype.ext he)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter
open scoped Topology
namespace ThreeTorus

/-- The integral carrier can meet every additional lower bound, as required
when the signal strength and approximation tolerance are selected first. -/
theorem eventually_integral_speed_separation {ι X : Type*} [Finite ι]
    [TopologicalSpace X] [CompactSpace X] (m : ι → ℤ) (φ : X → ℝ)
    (hm : ∀ i, m i ≠ 0) (hφ : Continuous φ) :
    ∀ᶠ c : ℕ in Filter.atTop, 0 < c ∧
      (∀ i x, (m i : ℝ) * ((c:ℝ) + φ x) ≠ 0) ∧
      (∀ i j x y, (m i : ℝ) * ((c:ℝ) + φ x) =
        (m j : ℝ) * ((c:ℝ) + φ y) → m i = m j) := by
  obtain ⟨R,hR⟩ := (isCompact_range hφ).isBounded.exists_norm_le
  obtain ⟨D,hD⟩ := (Set.finite_range (fun i => (m i : ℝ))).isCompact.isBounded.exists_norm_le
  let B := max R 0
  let M := max D 0
  have hB : 0 ≤ B := le_max_right _ _
  have hM : 0 ≤ M := le_max_right _ _
  have hφB x : |φ x| ≤ B := (hR _ (mem_range_self x)).trans (le_max_left _ _)
  have hmM i : |(m i : ℝ)| ≤ M := (hD _ (mem_range_self i)).trans (le_max_left _ _)
  have hct := (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun c : ℕ => (c:ℝ))
    Filter.atTop Filter.atTop).eventually (Filter.eventually_gt_atTop (2*M*B+B+1))
  filter_upwards [hct] with c hc
  have hMB : 0 ≤ M*B := mul_nonneg hM hB
  have hcB : B < (c:ℝ) := by nlinarith
  have hcp : (0:ℝ) < c := hB.trans_lt hcB
  refine ⟨by exact_mod_cast hcp,?_,?_⟩
  · intro i x
    apply mul_ne_zero (by exact_mod_cast hm i)
    have ht := (abs_le.mp (hφB x)).1
    linarith
  · intro i j x y he
    by_contra hij
    have hd : 1 ≤ |((m i-m j : ℤ):ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hij)
    have he' : ((m i:ℝ)-(m j:ℝ))*(c:ℝ) = (m j:ℝ)*φ y-(m i:ℝ)*φ x := by
      nlinarith [he]
    have hh : |(m j:ℝ)*φ y-(m i:ℝ)*φ x| ≤ 2*M*B := calc
      _ ≤ |(m j:ℝ)*φ y|+|(m i:ℝ)*φ x| := abs_sub _ _
      _ = |(m j:ℝ)| *|φ y|+|(m i:ℝ)| *|φ x| := by rw [abs_mul,abs_mul]
      _ ≤ M*B+M*B := add_le_add
        (mul_le_mul (hmM j) (hφB y) (abs_nonneg _) hM)
        (mul_le_mul (hmM i) (hφB x) (abs_nonneg _) hM)
      _ = 2*M*B := by ring
    rw [← he',abs_mul,abs_of_pos hcp] at hh
    simp only [Int.cast_sub] at hd
    nlinarith

end ThreeTorus
end
end

section

/-! Exact support tracking for the literal passage cutoffs.  The cutoffs are
chosen before the passage integer.  Every retained point is linked to a point
of the old support, so temporal tracking is not inferred from weak convergence.
The integral carrier disappears on the actual temporal circle. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- Scalar cutoffs with an arbitrarily small stationary-image enlargement,
exactly disjoint angular ranges, and the required identity on the true weights. -/
theorem tracked_frequency_cutoffs {ι : Type*} [Finite ι]
    (m : ι → ℤ) (V : ℝ → ℝ) (K : ι → Set ℝ)
    (hV : Continuous V) (hK : ∀ i, IsCompact (K i))
    (h0 : ∀ i, 0 ∉ (fun x => (m i:ℝ)*V x) '' K i)
    (hsep : Pairwise (fun i j => Disjoint ((fun x => (m i:ℝ)*V x) '' K i)
      ((fun x => (m j:ℝ)*V x) '' K j)))
    {η : ℝ} (hη : 0 < η) :
    ∃ χ : ι → ℝ → ℝ,
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ i) ∧ HasCompactSupport (χ i) ∧
        χ i 0 = 0 ∧ (∀ s, 0 ≤ χ i s ∧ χ i s ≤ 1) ∧
        (∀ s ∈ (fun x => (m i:ℝ)*V x) '' K i, χ i =ᶠ[𝓝 s] 1) ∧
        (∀ s ∈ tsupport (χ i), ∃ x ∈ K i, |s-(m i:ℝ)*V x| < η) ∧
        ∀ (C : Set ℝ) (A : ℝ → ℂ), support A ⊆ K i →
          ∀ s, stationaryWeight C (fun x => (m i:ℝ)*V x) A s ≠ 0 → χ i s = 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) := by
  let E i := (fun x => (m i:ℝ)*V x) '' K i
  let O i := Metric.thickening η (E i) ∩ ({0}:Set ℝ)ᶜ
  have hE i : IsCompact (E i) := (hK i).image (continuous_const.mul hV)
  have hO i : IsOpen (O i) := Metric.isOpen_thickening.inter isOpen_compl_singleton
  have hEO i : E i ⊆ O i := fun s hs =>
    ⟨Metric.self_subset_thickening hη _ hs,fun he => h0 i (show 0 ∈ E i from he ▸ hs)⟩
  obtain ⟨χ,hχ,hd⟩ := finite_disjoint_frequency_cutoffs E O hE hO hEO hsep
  refine ⟨χ,fun i => ⟨(hχ i).1,(hχ i).2.1,?_,(hχ i).2.2.2.1,
    (hχ i).2.2.2.2,?_,?_⟩,hd⟩
  · by_contra hz
    exact ((hχ i).2.2.1 (subset_tsupport (χ i) hz)).2 rfl
  · intro s hs
    obtain ⟨z,⟨x,hx,rfl⟩,hz⟩ := Metric.mem_thickening_iff.mp (((hχ i).2.2.1 hs).1)
    exact ⟨x,hx,by simpa only [Real.dist_eq] using hz⟩
  · intro C A hA s hs
    exact ((hχ i).2.2.2.2 s (stationaryWeight_support_subset hA hs)).self_of_nhds

lemma circle_dist_le_real (x y : ℝ) :
    dist (x:UnitAddCircle) (y:UnitAddCircle) ≤ |x-y| := by
  rw [dist_eq_norm,← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PacketStates
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed finite packet states, canonical densities, residue reindexing, anchors, reflection, clipping, and state tracking. -/

section

/-! Concrete finite-packet input data and the support bookkeeping used by
iteration. Field regularity is inherited from literal amplitudes. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

lemma core_subset (i : ι) : F.core i ⊆ Icc F.l F.u :=
  closure_minimal ((F.support_lift i 0).trans Ioc_subset_Icc_self) isClosed_Icc

lemma core_compact (i : ι) : IsCompact (F.core i) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (F.core_subset i)

lemma support_subset_core (hmod : F.SpareIndependent) (i : ι) (a : UnitAddCircle) :
    support (F.A₀ i a) ⊆ F.core i := by
  intro x hx
  apply subset_tsupport _
  intro hz
  apply hx
  apply norm_eq_zero.mp
  rw [hmod.1 i a x,hz,norm_zero]

lemma amplitude_bound [Finite ι] : ∃ B : ℝ, 0 ≤ B ∧ ∀ i p, ‖F.A i p‖^2 ≤ B := by
  classical
  have hb i := (isCompact_range ((F.continuous_amplitude i).norm.pow 2)).isBounded.exists_norm_le
  choose B hB using hb
  obtain ⟨C,hC⟩ := (Set.finite_range B).isCompact.isBounded.exists_norm_le
  refine ⟨max C 0,le_max_right _ _,fun i p => ?_⟩
  have h₁ := hB i _ (mem_range_self p)
  have h₂ := hC _ (mem_range_self i)
  exact (le_abs_self _).trans (h₁.trans ((le_abs_self _).trans (h₂.trans (le_max_left _ _))))

lemma carrier_spare (c : ℤ) (hmod : F.SpareIndependent) :
    (F.carrier c).SpareIndependent := hmod

lemma carrier_circle (c : ℤ) (x : ℝ) :
    ((F.carrier c).V x:UnitAddCircle) = (F.V x:UnitAddCircle) := by
  change (((c:ℝ)+F.V x:ℝ):UnitAddCircle) = _
  rw [AddCircle.coe_add]
  have hc : ((c:ℝ):UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).mpr ⟨c,by simp⟩
  rw [hc,zero_add]

end PassagePackets
end ThreeTorus
end
end

section

/-! Canonical smooth density of a literal passage-state packet.  These are
computed from the actual amplitude and speed; no spectral property is a field. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma continuous_density_unique {p q : UnitAddCircle → ℝ}
    (hp : Continuous p) (hq : Continuous q) (hp0 : ∀ z, 0 ≤ p z) (hq0 : ∀ z, 0 ≤ q z)
    (he : AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (p z)) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (q z))) : p = q := by
  apply (Continuous.ae_eq_iff_eq AddCircle.haarAddCircle hp hq).mp
  have hh := (withDensity_eq_iff_of_sigmaFinite
    hp.measurable.ennreal_ofReal.aemeasurable hq.measurable.ennreal_ofReal.aemeasurable).mp he
  filter_upwards [hh] with z hz
  have hh := congrArg ENNReal.toReal hz
  simpa only [ENNReal.toReal_ofReal (hp0 z), ENNReal.toReal_ofReal (hq0 z)] using hh

lemma foldCircleDensity_finsetSum_eq {ι : Type*} (S : Finset ι) (q : ι → ℝ → ℝ)
    (hq : ∀ i ∈ S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (q i))
    (hc : ∀ i ∈ S, HasCompactSupport (q i)) :
    foldCircleDensity (fun x => ∑ i ∈ S, q i x) =
      fun z => ∑ i ∈ S, foldCircleDensity (q i) z := by
  have hqS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ∑ i ∈ S, q i x) := ContDiff.sum hq
  have hcS : HasCompactSupport (fun x => ∑ i ∈ S, q i x) := by
    convert HasCompactSupport.finset_sum hc using 1
    all_goals try with_reducible_and_instances rfl
    funext point
    simp only [Finset.sum_apply]
  apply (Continuous.ae_eq_iff_eq AddCircle.haarAddCircle
    (continuous_of_continuous_lift (foldCircleDensity_smooth_lift hqS hcS).continuous)
    (continuous_finsetSum _ (fun i hi => continuous_of_continuous_lift
      (foldCircleDensity_smooth_lift (hq i hi) (hc i hi)).continuous))).mp
  exact foldCircleDensity_finsetSum_ae S q
    (fun i hi => (hq i hi).continuous.measurable)
    (fun i hi => (hq i hi).continuous.integrable_of_hasCompactSupport (hc i hi))

namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

lemma weight_nonneg (i : ι) (s : ℝ) : 0 ≤ F.weight i s :=
  branchDensity_nonneg (fun _ => sq_nonneg _) s

lemma density_nonneg (i : ι) (z : UnitAddCircle) : 0 ≤ F.density i z :=
  foldCircleDensity_nonneg (F.weight_nonneg i) z

lemma smooth_zero_lift (i : ι) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F.A₀ i 0) := by
  simpa only [Function.comp_def, AddCircle.coe_zero] using
    (F.smooth_lift i).comp (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => (x,(0:ℝ))) from contDiff_id.prodMk contDiff_const)

lemma weight_regular (i : ι) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F.weight i) ∧ HasCompactSupport (F.weight i) := by
  let q := fun x => ‖F.A₀ i 0 x‖^2
  have hqs : tsupport q ⊆ F.core i := by
    apply closure_mono
    intro x hx hz
    exact hx (by simp [q,hz])
  have hqc : HasCompactSupport q := (F.core_compact i).of_isClosed_subset isClosed_closure hqs
  have hs : tsupport q ⊆ Ioo (F.l-F.R) (F.u+F.R) := by
    intro x hx
    have hh := F.core_subset i (hqs hx)
    constructor <;> linarith [F.Rpos,hh.1,hh.2]
  have has : support (F.A₀ i 0) ⊆ Ioo (F.l-F.R) (F.u+F.R) := by
    intro x hx
    have hh := F.support_lift i 0 hx
    constructor <;> linarith [F.Rpos,hh.1,hh.2]
  have hb := scaled_speed_good_branch (F.nonzero i) F.Rpos F.smooth_speed F.positive_deriv
  have he := stationaryWeight_change_branch Ioo_subset_Icc_self hb.1 has
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (stationaryWeight _ _ _) ∧ HasCompactSupport (stationaryWeight _ _ _)
  rw [he]
  exact ⟨branchDensity_smooth (contDiff_const.mul F.smooth_speed) isOpen_Ioo
    (hb.1.mono Ioo_subset_Icc_self) hb.2 ((F.smooth_zero_lift i).norm_sq (𝕜 := ℂ)) hqc hs,
    branchDensity_compact (continuous_const.mul F.smooth_speed.continuous) hqc⟩

lemma density_smooth (i : ι) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : ℝ => F.density i (x:UnitAddCircle)) :=
  foldCircleDensity_smooth_lift (F.weight_regular i).1 (F.weight_regular i).2

lemma density_continuous (i : ι) : Continuous (F.density i) :=
  continuous_of_continuous_lift (F.density_smooth i).continuous

lemma speed_continuous : Continuous F.periodic.lift := by
  apply Continuous.quotient_lift
  exact F.smooth_speed.continuous

/-- The canonical density is the spectral measure of the actual angular packet. -/
theorem density_spectral (hmod : F.SpareIndependent) (i : ι) :
    packetSpectralMeasure (fun u => (F.periodic.lift u:UnitAddCircle)) (F.m i) (F.A i) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (F.density i z)) := by
  have hb := scaled_speed_good_branch (F.nonzero i) F.Rpos F.smooth_speed F.positive_deriv
  have hs : support (F.A₀ i 0) ⊆ Ioo (F.l-F.R) (F.u+F.R) := by
    intro x hx
    have hh := F.support_lift i 0 hx
    constructor <;> linarith [F.Rpos,hh.1,hh.2]
  have he := oldPacket_spectralDensity_of_modulus (m := F.m i) (c := 0) (v := F.periodic.lift)
    (F.continuous_amplitude i) (F.smooth_zero_lift i).continuous (hmod.2 i)
    (F.lift_matches i 0) ((F.support_lift i 0).trans (by
      intro x hx; exact ⟨lt_of_le_of_lt F.lo hx.1, hx.2.trans F.uo⟩)) hs
    F.speed_continuous.measurable F.smooth_speed (fun _ _ => rfl)
    isOpen_Ioo Ioo_subset_Icc_self hb.1 hb.2
  simpa only [Int.cast_zero,sub_zero,density,weight] using he

lemma density_marginal (hmod : F.SpareIndependent) (i : ι) :
    foldCircleDensity (fun s => ∫ a, stationaryWeight (Icc (F.l-F.R) (F.u+F.R))
      (fun x => (F.m i:ℝ)*F.V x) (F.A₀ i a) s ∂AddCircle.haarAddCircle) = F.density i := by
  congr 1
  funext s
  simp [stationaryWeight_modulus_independent (hmod.1 i),weight]

lemma density_carrier (hmod : F.SpareIndependent) (c : ℤ) (i : ι) :
    (F.carrier c).density i = F.density i := by
  apply continuous_density_unique ((F.carrier c).density_continuous i) (F.density_continuous i)
    ((F.carrier c).density_nonneg i) (F.density_nonneg i)
  rw [← (F.carrier c).density_spectral (F.carrier_spare c hmod) i,← F.density_spectral hmod i]
  congr 1
  funext z
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective z
  exact F.carrier_circle c x

end PassagePackets
end ThreeTorus
end
end

section

/-! Exact identification of the canonical density of an iterated packet state
with the literal finite density already controlled by the passage estimates. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma exactRetainedPacketDensity_nonneg (I : Set ℝ) (J : ℝ → ℝ) (ψ : UnitAddCircle → ℝ)
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (S : Finset ℤ) (n : ℕ) (z : UnitAddCircle) :
    0 ≤ exactRetainedPacketDensity I J ψ χ m H A S n z := by
  apply foldCircleDensity_nonneg
  intro t
  apply Finset.sum_nonneg
  intro j _hj
  exact unfoldedModeDensity_nonneg
    (circleDensityLift_nonneg (retainedCircleWeight_nonneg ψ χ _ n j) 0) (Nat.cast_nonneg n) j t

lemma exactRetainedPacketDensity_singleton (I : Set ℝ) (J : ℝ → ℝ) (ψ : UnitAddCircle → ℝ)
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (j : ℤ) (n : ℕ) :
    exactRetainedPacketDensity I J ψ χ m H A {j} n =
      foldCircleDensity (unfoldedModeDensity I J (invFunOn J I) (deriv J)
        (circleDensityLift 0 (retainedCircleWeight ψ χ
          (fun n j => exactPassageCoeff m (H n) A j) n j)) n j) := by
  simp only [exactRetainedPacketDensity,Finset.sum_singleton]

lemma exactRetainedPacketDensity_sum_singletons
    {I : Set ℝ} {J : ℝ → ℝ} {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {m : ℤ}
    {H : ℕ → UnitAddCircle → UnitAddCircle} {Hl : ℕ → ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ} {S : Finset ℤ} {n : ℕ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hc : HasCompactSupport ψ₀)
    (he : ∀ x ∈ Ioc (0:ℝ) (0+1), ψ (x:UnitAddCircle) = ψ₀ x)
    (hs : tsupport ψ₀ ⊆ Ioc (0:ℝ) (0+1) ∩ I)
    (hχ : CylinderSmooth χ.uncurry)
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hH : ∀ n (t : ℝ), H n (t:UnitAddCircle) = (Hl n t:UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (hn : 0 < n) (hS : ∀ j ∈ S, j ≠ 0) :
    exactRetainedPacketDensity I J ψ χ m H A S n =
      fun z => ∑ j ∈ S, exactRetainedPacketDensity I J ψ χ m H A {j} n z := by
  unfold exactRetainedPacketDensity
  simp only [Finset.sum_singleton]
  simp_rw [retainedWeight_lift_eq χ m H A n _ he (hs.trans inter_subset_left)]
  apply foldCircleDensity_finsetSum_eq
  · intro j _hj
    exact unfoldedModeDensity_smooth hJ hIo hinj hd
      (realRetainedWeight_smooth hψ hχ hHl hH hA n j)
      (realRetainedWeight_compact hc χ m H A n j)
      ((realRetainedWeight_support ψ₀ χ m H A n j).trans (hs.trans inter_subset_right)) n j
  · intro j hj
    exact unfoldedModeDensity_compact hJ.continuous
      (realRetainedWeight_compact hc χ m H A n j)
      (by exact_mod_cast hn.ne') (by exact_mod_cast hS j hj)

lemma exactRetainedPacketDensity_filtered_singletons
    {I : Set ℝ} {J : ℝ → ℝ} {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {m : ℤ}
    {H : ℕ → UnitAddCircle → UnitAddCircle} {Hl : ℕ → ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ} {S : Finset ℤ} {n : ℕ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hc : HasCompactSupport ψ₀)
    (he : ∀ x ∈ Ioc (0:ℝ) (0+1), ψ (x:UnitAddCircle) = ψ₀ x)
    (hs : tsupport ψ₀ ⊆ Ioc (0:ℝ) (0+1) ∩ I)
    (hχ : CylinderSmooth χ.uncurry)
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hH : ∀ n (t : ℝ), H n (t:UnitAddCircle) = (Hl n t:UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (hn : 0 < n) (hS : ∀ j ∈ S, j ≠ 0) (E : ℤ → Prop) [DecidablePred E] :
    exactRetainedPacketDensity I J ψ χ m H A (S.filter E) n =
      fun z => ∑ j : ↥S, if E j.val then
        exactRetainedPacketDensity I J ψ χ m H A {j.val} n z else 0 := by
  rw [exactRetainedPacketDensity_sum_singletons hJ hIo hinj hd hψ hc he hs hχ hHl hH hA hn
    (fun j hj => hS j (Finset.mem_filter.mp hj).1)]
  funext z
  rw [Finset.sum_filter]
  exact (Finset.sum_coe_sort S (fun j => if E j then
    exactRetainedPacketDensity I J ψ χ m H A {j} n z else 0)).symm

/-- Pointwise, not just a.e., identity of a literal output packet's canonical
density. The hypotheses below are only smooth lifts and the displayed literal
coefficient/speed identities; no new spectral law is assumed. -/
theorem literal_packet_canonical_density {ι : Type*} (F : PassagePackets ι)
    (hmod : F.SpareIndependent) (i : ι)
    {I : Set ℝ} {J : UnitAddCircle → ℝ} {J₀ : ℝ → ℝ}
    {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {m j : ℤ} {n : ℕ} {H : ℕ → UnitAddCircle → UnitAddCircle} {Hl : ℕ → ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hm : F.m i = j) (hamp : F.A i = retainedAmplitude ψ χ m H A n j)
    (hspeed : ∀ a, (F.periodic.lift a:UnitAddCircle) = (((1+J a/n)/n:ℝ):UnitAddCircle))
    (hJc : Continuous J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x:UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    (hψc : Continuous ψ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀)
    (hc : HasCompactSupport ψ₀)
    (he : ∀ x ∈ Ioc (0:ℝ) (0+1), ψ (x:UnitAddCircle) = ψ₀ x)
    (hs : tsupport ψ₀ ⊆ Ioc (0:ℝ) (0+1) ∩ I)
    (hχc : Continuous χ.uncurry) (hχ : CylinderSmooth χ.uncurry)
    (hHc : ∀ n, Continuous (H n))
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hH : ∀ n (t : ℝ), H n (t:UnitAddCircle) = (Hl n t:UnitAddCircle))
    (hAc : Continuous A)
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (hn : 0 < n) :
    F.density i = exactRetainedPacketDensity I J₀ ψ χ m H A {j} n := by
  have hj : j ≠ 0 := hm ▸ F.nonzero i
  have hps := exactRetainedPacketDensity_smooth_lift (m := m) hJ hIo hinj hd hψ hc he hs hχ hHl hH hA hn
    (S := {j}) (fun k hk => by simpa only [Finset.mem_singleton.mp hk] using hj)
  apply continuous_density_unique (F.density_continuous i)
    (continuous_of_continuous_lift hps.continuous) (F.density_nonneg i)
    (exactRetainedPacketDensity_nonneg I J₀ ψ χ m H A {j} n)
  rw [← F.density_spectral hmod i,hm,hamp,show
    (fun a => (F.periodic.lift a:UnitAddCircle)) =
      (fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)) from funext hspeed,
    exactRetainedPacketDensity_singleton]
  exact retainedAmplitude_spectralDensity hψc hχc hHc hAc
    (fun x hx hp => (hs (subset_tsupport ψ₀ (by rwa [he x hx] at hp))).2)
    hJc.measurable hJ hJe hIo hinj hd hn hj

end ThreeTorus
end
end

section

/-! The residue slices are slices of the actual retained angular list, not
independently fabricated Fourier arrays. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma sum_residue_rename {M : Type*} [AddCommMonoid M]
    (f : ℤ → M) (S T : Finset ℤ) (Q h : ℤ) (hQ : Q ≠ 0)
    (hS : ∀ k, k ∉ S → f (h+k*Q) = 0) (hT : ∀ j, j ∉ T → f j = 0) :
    ∑ k ∈ S, f (h+k*Q) = ∑ j ∈ T.filter (fun j => j % Q = h % Q), f j := by
  classical
  let a : ℤ → ℤ := fun k => h+k*Q
  have hai : Injective a := fun x y he => mul_right_cancel₀ hQ (add_left_cancel he)
  let F : ℤ → M := fun j => if j % Q = h % Q then f j else 0
  have hFa k : F (a k) = f (a k) := by simp [F,a,Int.add_mul_emod_self_right]
  have hSa j (hj : j ∉ S.image a) : F j = 0 := by
    dsimp only [F]
    split_ifs with he
    · let k := j/Q-h/Q
      have hk : a k = j := by
        dsimp [a,k]
        have hh := Int.emod_add_ediv_mul h Q
        have hj' := Int.emod_add_ediv_mul j Q
        rw [he] at hj'
        nlinarith
      have hkS : k ∉ S := fun hks => hj (hk ▸ Finset.mem_image.mpr ⟨k,hks,rfl⟩)
      rw [← hk]
      exact hS k hkS
    · rfl
  have hTF j (hj : j ∉ T) : F j = 0 := by simp [F,hT j hj]
  calc
    ∑ k ∈ S, f (a k) = ∑ k ∈ S, F (a k) := by simp_rw [hFa]
    _ = ∑ j ∈ S.image a, F j := (Finset.sum_image hai.injOn).symm
    _ = ∑ j ∈ T, F j := sum_eq_of_zero_off F (S.image a) T hSa hTF
    _ = _ := (Finset.sum_filter _ f).symm

lemma exactRetainedPacketDensity_residue_rename
    (I : Set ℝ) (J₀ : ℝ → ℝ) (ψ : UnitAddCircle → ℝ)
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (S T : Finset ℤ) (n : ℕ)
    (Q h : ℤ) (hQ : Q ≠ 0)
    (hS : ∀ k, k ∉ S → ∀ a, χ (((h+k*Q:ℤ):ℝ)/n) a = 0)
    (hT : ∀ j, j ∉ T → ∀ a, χ ((j:ℝ)/n) a = 0) :
    foldCircleDensity (fun t => ∑ k ∈ S,
      unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
        (circleDensityLift 0 (retainedCircleWeight ψ χ
          (fun n j => exactPassageCoeff m (H n) A j) n (h+k*Q)))
        n ((h+k*Q:ℤ):ℝ) t) =
      exactRetainedPacketDensity I J₀ ψ χ m H A (T.filter (fun j => j % Q = h % Q)) n := by
  unfold exactRetainedPacketDensity
  congr 1
  funext t
  apply sum_residue_rename
    (fun j : ℤ => unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
      (circleDensityLift 0 (retainedCircleWeight ψ χ
        (fun n j => exactPassageCoeff m (H n) A j) n j)) n (j:ℝ) t) S T Q h hQ
  · intro k hk
    have hz := hS k hk
    simp only [Int.cast_add,Int.cast_mul] at hz
    simp [unfoldedModeDensity,scaledBranchKernel,branchDensity,
      circleDensityLift,retainedCircleWeight,hz]
  · intro j hj
    simp [unfoldedModeDensity,scaledBranchKernel,branchDensity,
      circleDensityLift,retainedCircleWeight,hT j hj]

end ThreeTorus
end
end

section

/-! Neutral refresh splits the literal next angular list, simultaneously for
all residues, with total error independent of the number of residue tests. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma foldCircleDensity_const_mul (w : ℝ → ℝ) (c : ℝ) :
    foldCircleDensity (fun s => c*w s) = fun z => c*foldCircleDensity w z := by
  funext z
  induction z using Quotient.inductionOn with | h x =>
    simp only [foldCircleDensity_coe_all,tsum_mul_left]

theorem exact_neutral_residue_refresh
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {Pr V : ℝ → ℝ} {m : ℤ} {Δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(Pr x+Δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hAr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ a, support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pr)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv Pr = V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (h0 : 0 ∉ (fun x => (m:ℝ)*V x) '' Icc l u)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hΔt : Tendsto Δ atTop (𝓝 0))
    {v : UnitAddCircle → ℝ} (hv : Measurable v) (hVe : ∀ x : ℝ, v (x:UnitAddCircle) = V x)
    {B : ℝ} (hB : 0 ≤ B) (hAb : ∀ p, ‖A p‖^2 ≤ B)
    {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
    {χ : ℝ → UnitAddCircle → ℝ}
    (hχc : Continuous χ.uncurry) (hcχ : HasCompactSupport χ.uncurry) (hzχ : ∀ a, χ 0 a = 0)
    (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s ≠ 0 → χ s a = 1)
    {Q : ℕ} (hQ : 0 < Q) :
    let pold := foldCircleDensity (fun s => ∫ a, stationaryWeight (Icc (l-R) (u+R))
      (fun x => (m:ℝ)*V x) (A₀ a) s ∂AddCircle.haarAddCircle)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L → ∀ β : ℝ,
      ∀ T : ℕ → Finset ℤ,
      (∀ n, 0 < n → ∀ j ∈ T n, j ≠ 0) →
      (∀ n, 0 < n → ∀ j ∉ T n, ∀ a, χ ((j:ℝ)/n) a = 0) →
      ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
        (∑ h : Fin Q, ∫ z,
          |exactRetainedPacketDensity (Ioo δ (1-δ)) (neutralJitterReal c L β)
            (neutralCircleCutoff c) χ m H A
            ((T n).filter (fun j => j % (Q:ℤ) = (h.val:ℤ) % (Q:ℤ))) n z-
            (Q:ℝ)⁻¹*pold z| ∂AddCircle.haarAddCircle) < C/L+4*δ*B+η := by
  classical
  dsimp only
  let ψ := neutralCircleCutoff c
  let W := fun s a => stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s
  let pold := foldCircleDensity (fun s => ∫ a, W s a ∂AddCircle.haarAddCircle)
  let pcut := foldCircleDensity (fun s => ∫ a, stationaryWeight (Icc (l-R) (u+R))
    (fun x => (m:ℝ)*V x) (fun x => (ψ a:ℂ)*A₀ a x) s ∂AddCircle.haarAddCircle)
  let F := stationaryCutoffLift (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
    (fun p : ℝ × ℝ => A₀ (p.2:UnitAddCircle) p.1) c.ψ
  have hψc := continuous_neutralCircleCutoff c
  have hψs : tsupport c.ψ ⊆ Ioc (0:ℝ) (0+1) ∩ Ioo δ (1-δ) := by
    intro x hx
    have hh := c.ψ_support hx
    exact ⟨⟨by linarith [hh.1],by linarith [hh.2]⟩,hh⟩
  have heψ : ∀ x ∈ Ioc (0:ℝ) (0+1), c.ψ x = ψ (x:UnitAddCircle) := by
    intro x hx
    exact (lawPsi_eq c hδ ⟨hx.1.le,by simpa using hx.2⟩).symm
  have hcut : (∫ z, |pcut z-pold z| ∂AddCircle.haarAddCircle) ≤ B*(4*δ) := by
    have hs₁ : ∀ a, support (A₀ a) ⊆ Ioc o (o+1) := by
      intro a x hx
      have hh := hsupp a hx
      exact ⟨lt_of_le_of_lt hlo hh.1,hh.2.trans huo⟩
    have hs₂ : ∀ a, support (A₀ a) ⊆ Ioo (l-R) (u+R) := by
      intro a x hx
      have hh := hsupp a hx
      exact ⟨by linarith [hh.1],by linarith [hh.2]⟩
    have hb := oldStationaryMarginal_cutoff_l1 hAcont hAc hA hs₁ hs₂ hv hV
      (fun x _ => hVe x) isOpen_Ioo Ioo_subset_Icc_self
      (scaled_speed_good_branch hm hR hV hdV).1 (scaled_speed_good_branch hm hR hV hdV).2
      hψc (neutralCircleCutoff_bounds c hδ) hB hAb
    exact hb.trans (mul_le_mul_of_nonneg_left (neutralCircleCutoff_error c hδ hδ') hB)
  have hmarg : (fun s => ∫ a, F (a,s)) = fun s => ∫ a,
      stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
        (fun x => (ψ a:ℂ)*A₀ a x) s ∂AddCircle.haarAddCircle := by
    funext s
    exact stationaryCutoffLift_marginal heψ
      (fun x hx => (hψs (subset_tsupport c.ψ hx)).1) _ _ s
  have hsp (h : Fin Q) := exact_neutral_circle_spectral_estimate hm hH hA hA₀ hAc hAd hAr
    hsupp hlo huo hlu hR hPr hV hPV hdV h0 hHc hAcont hΔt isOpen_Ioo
    c.ψ_smooth c.ψ_compact hψs heψ hψc hχc hcχ hzχ
    (neutralCircleCutoff_bounds c hδ) hχ hχW hQ (h.val:ℤ)
  choose C hC hrest using hsp
  refine ⟨∑ h, C h,Finset.sum_nonneg (fun h _ => hC h),?_⟩
  intro L hL β T hTN hTZ η hη
  have hJs := neutralJitterReal_smooth c L β
  have hJc := continuous_neutralJitter c L β
  have heJ : ∀ a ∈ Ioo δ (1-δ), neutralJitterReal c L β a = L*a+β :=
    fun a ha => neutralJitterReal_affine c hδ L β ⟨ha.1.le,ha.2.le⟩
  have hJinj : InjOn (neutralJitterReal c L β) (Ioo δ (1-δ)) := by
    intro a ha b hb hab
    rw [heJ a ha,heJ b hb] at hab
    nlinarith
  have hJd : ∀ a ∈ Ioo δ (1-δ), deriv (neutralJitterReal c L β) a ≠ 0 := by
    intro a ha
    rw [neutralJitterReal_deriv c hδ L β ha]
    exact hL.ne'
  choose S hSN hST ht using fun h => hrest h L hL β (neutralJitterReal c L β)
    (neutralJitter c L β) heJ hJs hJc.measurable (fun x _ => neutralJitter_coe c L β x)
  have hpcuti : Integrable pcut AddCircle.haarAddCircle := by
    have hreg := exact_cutoff_weight_regular hm hR hV hdV hAr
      (fun a => (hsupp a).trans Ioc_subset_Icc_self) c.ψ_smooth c.ψ_compact h0
    have hi := compact_slice_integral_regular
      ((hreg.1.comp (contDiff_snd.prodMk contDiff_fst)).continuous)
      (hreg.2.1.comp_homeomorph (Homeomorph.prodComm ℝ ℝ))
    dsimp only [pcut]
    rw [← hmarg]
    exact integrable_foldCircleDensity hi.1.measurable hi.2
  have hpoldi : Integrable pold AddCircle.haarAddCircle := by
    have hs₁ : ∀ a, support (A₀ a) ⊆ Ioc o (o+1) := fun a x hx =>
      ⟨lt_of_le_of_lt hlo (hsupp a hx).1,(hsupp a hx).2.trans huo⟩
    have hs₂ : ∀ a, support (A₀ a) ⊆ Ioo (l-R) (u+R) := by
      intro a x hx
      have hh := hsupp a hx
      exact ⟨by linarith [hh.1],by linarith [hh.2]⟩
    exact (oldStationaryMarginal_map hAcont hAc hA hs₁ hs₂ hv hV
      (fun x _ => hVe x) isOpen_Ioo Ioo_subset_Icc_self
      (scaled_speed_good_branch hm hR hV hdV).1 (scaled_speed_good_branch hm hR hV hdV).2).1
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hQz : (Q:ℤ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hqpos : 0 < (Q:ℝ)⁻¹ := inv_pos.mpr hQr
  have hsall := (Filter.eventually_all).mpr (fun h => ht h (η/Q) (div_pos hη hQr))
  filter_upwards [hsall,eventually_gt_atTop (0:ℕ)] with n hnsp hn
  have hp (h : Fin Q) := exactRetainedPacketDensity_integrable (m := m) hJs isOpen_Ioo hJinj hJd
    hψc hχc hHc hAcont hn
    (fun j (hj : j ∈ (T n).filter (fun j => j % (Q:ℤ) = (h.val:ℤ) % (Q:ℤ))) =>
      hTN n hn j (Finset.mem_filter.mp hj).1)
  have hps (h : Fin Q) :
      (∫ z, |exactRetainedPacketDensity (Ioo δ (1-δ)) (neutralJitterReal c L β)
        ψ χ m H A ((T n).filter (fun j => j % (Q:ℤ) = (h.val:ℤ) % (Q:ℤ))) n z-
        (Q:ℝ)⁻¹*pcut z| ∂AddCircle.haarAddCircle) < C h/L+η/Q := by
    have he := exactRetainedPacketDensity_residue_rename (Ioo δ (1-δ))
      (neutralJitterReal c L β) ψ χ m H A (S h n) (T n) n (Q:ℤ) (h.val:ℤ) hQz
      (hST h n hn) (hTZ n hn)
    have hh := hnsp h
    rw [he,foldCircleDensity_const_mul,hmarg] at hh
    exact hh
  have hcscale : (∫ z, |(Q:ℝ)⁻¹*pcut z-(Q:ℝ)⁻¹*pold z|
      ∂AddCircle.haarAddCircle) ≤ (Q:ℝ)⁻¹*(B*(4*δ)) := by
    simp_rw [← mul_sub,abs_mul,abs_of_pos hqpos]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hcut hqpos.le
  have hfinal (h : Fin Q) :
      (∫ z, |exactRetainedPacketDensity (Ioo δ (1-δ)) (neutralJitterReal c L β)
        ψ χ m H A ((T n).filter (fun j => j % (Q:ℤ) = (h.val:ℤ) % (Q:ℤ))) n z-
        (Q:ℝ)⁻¹*pold z| ∂AddCircle.haarAddCircle) < C h/L+(4*δ*B+η)/Q := by
    have hh := integral_abs_sub_triangle (hp h)
      (hpcuti.const_mul (Q:ℝ)⁻¹) (hpoldi.const_mul (Q:ℝ)⁻¹)
    have hs := hps h
    calc
      _ ≤ _ := hh
      _ < C h/L+η/Q+(Q:ℝ)⁻¹*(B*(4*δ)) := add_lt_add_of_lt_of_le hs hcscale
      _ = _ := by ring
  calc
    _ < ∑ h : Fin Q, (C h/L+(4*δ*B+η)/Q) := by
      apply Finset.sum_lt_sum
      · exact fun h _ => (hfinal h).le
      · exact ⟨⟨0,hQ⟩,Finset.mem_univ _,hfinal ⟨0,hQ⟩⟩
    _ = _ := by
      rw [Finset.sum_add_distrib,← Finset.sum_div]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp
      ring

end ThreeTorus
end
end

section

/-! The simultaneous neutral passage with an actual integer-rounded common
primitive. Its complete geometry and all spectral estimates are supplied by
one and the same sequence of smooth Haar-preserving maps. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

/-- The jitter, all packet lists and all cutoffs are fixed before the final
passage integer. No primitive, convergence, or spectral data are assumed. -/
theorem exists_simultaneous_neutral_residue_passage {ι : Type*} [Fintype ι]
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} {A₀ : ι → UnitAddCircle → ℝ → ℂ}
    {V : ℝ → ℝ} {m : ι → ℤ} {o l u R : ℝ}
    (hm : ∀ i, m i ≠ 0)
    (hA : ∀ i a x, x ∈ Ioc o (o+1) → A i ((x : UnitAddCircle),a) = A₀ i a x)
    (hA₀ : ∀ i a, ContDiff ℝ 2 (A₀ i a)) (hAc : ∀ i, Continuous (A₀ i).uncurry)
    (hAd : ∀ i, Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ i p.1) p.2))
    (hAr : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ i (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ i a, support (A₀ i a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hp : Periodic V 1) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (h0 : ∀ i, 0 ∉ (fun x => (m i:ℝ)*V x) '' Icc l u)
    (hAcont : ∀ i, Continuous (A i))
    (hAs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A i (p.1,p.2)))
    {B : ι → ℝ} (hB : ∀ i, 0 ≤ B i) (hAb : ∀ i p, ‖A i p‖^2 ≤ B i)
    {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
    {χ : ι → ℝ → UnitAddCircle → ℝ}
    (hχs : ∀ i, CylinderSmooth (χ i).uncurry)
    (hχc : ∀ i, Continuous (χ i).uncurry) (hcχ : ∀ i, HasCompactSupport (χ i).uncurry)
    (hzχ : ∀ i a, χ i 0 a = 0) (hχ : ∀ i s a, 0 ≤ χ i s a ∧ χ i s a ≤ 1)
    (hχW : ∀ i s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m i:ℝ)*V x)
      (A₀ i a) s ≠ 0 → χ i s a = 1)
    {Q : ℕ} (hQ : 0 < Q) :
    ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      (∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹) ∧ Tendsto Δ atTop (𝓝 0) ∧
      (∀ n, Continuous (H n)) ∧
      (∀ n (x : ℝ), H n (x:UnitAddCircle) =
        ((n:ℝ)*((∫ t in 0..x, V t)+Δ n*x):UnitAddCircle)) ∧
      ∃ C Cq : ι → ℝ, (∀ i, 0 ≤ C i) ∧ (∀ i, 0 ≤ Cq i) ∧ ∀ L : ℝ, 0 < L → ∀ β : ℝ,
        let ψ := neutralCircleCutoff c
        let J := neutralJitter c L β
        let J₀ := neutralJitterReal c L β
        let σ := fun (n : ℕ) a => (((1+J a/n)/n:ℝ):UnitAddCircle)
        (∀ n, Smooth (torusPassage (H n) (σ n)) ∧
          Smooth (torusPassage (H n) (σ n)).symm ∧
          MeasurePreserving (torusPassage (H n) (σ n)) μ μ) ∧
        (∀ n, 0 < n → ∀ x : Cover,
          torusPassage (H n) (σ n) (project x) =
            project (passageFamily V J₀ 1 ((n:ℝ)⁻¹,Δ n) x) ∧
          (torusPassage (H n) (σ n)).symm (project x) =
            project (passageFamily V J₀ (-1) ((n:ℝ)⁻¹,Δ n) x)) ∧
        (∀ r : ℝ, ∀ K : Set Cover, IsCompact K → ∀ d : ℕ,
          TendstoUniformlyOn
            (fun (n : ℕ) x => iteratedFDeriv ℝ d (passageFamily V J₀ r ((n:ℝ)⁻¹,Δ n)) x)
            (fun x => iteratedFDeriv ℝ d (fun y : Cover => ![y 0+r*V (y 1),y 1,y 2]) x)
            atTop K) ∧
        ∃ S : ℕ → ι → Finset ℤ,
          (∀ n, 0 < n → ∀ i j, j ∈ S n i → j ≠ 0) ∧
          (∀ n, 0 < n → ∀ i j, j ∉ S n i → ∀ a, χ i ((j:ℝ)/n) a = 0) ∧
          (∀ n, 0 < n → ∀ i j, j ∈ S n i ↔ ∃ a, χ i ((j:ℝ)/n) a ≠ 0) ∧
          ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
            0 < n ∧ ∀ i,
            let f := retainedPassage (m i) (H n) (A i) (S n i) (fun j => χ i ((j:ℝ)/n)) ψ
            let p := exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ (χ i) (m i) H (A i) (S n i) n
            let pold := foldCircleDensity (fun s => ∫ a, stationaryWeight (Icc (l-R) (u+R))
              (fun x => (m i:ℝ)*V x) (A₀ i a) s ∂AddCircle.haarAddCircle)
            (∫ x : TripleTorus, ‖packet (m i) (A i) x-f (passageChart (H n) x)‖^2 ∂tripleVolume) <
              8*δ*B i+η ∧
            (∫ z, |p z-pold z| ∂AddCircle.haarAddCircle) < C i/L+4*δ*B i+η ∧
            ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => p x) ∧
            (∀ k : ℤ, (∫ x : TripleTorus, starRingEnd ℂ (f x)*f (twistIter (σ n) k x) ∂tripleVolume) =
              ∫ z, (p z:ℂ)*fourier k z ∂AddCircle.haarAddCircle) ∧
            (∀ j u a, ‖retainedAmplitude ψ (χ i) (m i) H (A i) n j (u,a)‖ =
              ‖retainedAmplitude ψ (χ i) (m i) H (A i) n j (u,0)‖) ∧
            (∑ h : Fin Q, ∫ z,
              |exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ (χ i) (m i) H (A i)
                ((S n i).filter (fun j => j % (Q:ℤ) = (h.val:ℤ) % (Q:ℤ))) n z-
                (Q:ℝ)⁻¹*pold z| ∂AddCircle.haarAddCircle) < Cq i/L+4*δ*B i+η := by
  classical
  obtain ⟨Δ,H,hΔ,hΔt,hHc,hHe,hgeo⟩ := exists_rounded_primitive_family hp hV
  have hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ∫ t in 0..x, V t) :=
    contDiff_real_primitive hV
  have hPV : deriv (fun x => ∫ t in 0..x, V t) = V := deriv_real_primitive hV.continuous
  have hv : Continuous hp.lift := by
    apply Continuous.quotient_lift
    exact hV.continuous
  have heV (x : ℝ) : hp.lift (x:UnitAddCircle) = V x := rfl
  have hneutral i := exact_neutral_passage (hm i) hHe (hA i) (hA₀ i) (hAc i) (hAd i)
    (hAr i) (hsupp i) hlo huo hlu hR hPr hV hPV hdV (h0 i) hHc (hAcont i) hΔt (hAs i)
    hv.measurable heV (hB i) (hAb i) c hδ hδ' (hχs i) (hχc i) (hcχ i) (hzχ i) (hχ i) (hχW i)
  choose C hC hrest using hneutral
  have hresidue i := exact_neutral_residue_refresh (hm i) hHe (hA i) (hA₀ i) (hAc i) (hAd i)
    (hAr i) (hsupp i) hlo huo hlu hR hPr hV hPV hdV (h0 i) hHc (hAcont i) hΔt
    hv.measurable heV (hB i) (hAb i) c hδ hδ' (hχc i) (hcχ i) (hzχ i) (hχ i) (hχW i) hQ
  choose Cq hCq hres using hresidue
  refine ⟨Δ,H,hΔ,hΔt,hHc,hHe,C,Cq,hC,hCq,?_⟩
  intro L hL β
  dsimp only
  obtain ⟨hg,hgraph,hlimit⟩ := hgeo (neutralJitterReal c L β)
    (neutralJitterReal_periodic c L β) (neutralJitterReal_smooth c L β)
  refine ⟨hg,hgraph,hlimit,?_⟩
  choose S hSN hST hgood using fun i => hrest i L hL β
  obtain ⟨T,hTN,hTE⟩ := cylinder_cutoff_exact_indices χ hcχ hzχ
  have hTZ n (hn : 0 < n) i j (hj : j ∉ T n i) a : χ i ((j:ℝ)/n) a = 0 := by
    by_contra hh
    exact hj ((hTE n hn i j).mpr ⟨a,hh⟩)
  refine ⟨T,fun n _ i => hTN n i,hTZ,hTE,?_⟩
  intro η hη
  have hgall := (Filter.eventually_all).mpr (fun i => hgood i η hη)
  have hqall := (Filter.eventually_all).mpr (fun i => hres i L hL β (fun n => T n i)
    (fun n _ => hTN n i) (fun n hn => hTZ n hn i) η hη)
  filter_upwards [eventually_gt_atTop (0:ℕ),hgall,hqall] with n hn hall hq
  refine ⟨hn,fun i => ?_⟩
  have ef := retainedPassage_eq_of_cover (m i) (H n) (A i) (S i n) (T n i)
    (fun j => χ i ((j:ℝ)/n)) (neutralCircleCutoff c) (hST i n hn) (hTZ n hn i)
  have ep := exactRetainedPacketDensity_eq_of_cover (Ioo δ (1-δ))
    (neutralJitterReal c L β) (neutralCircleCutoff c) (χ i) (m i) H (A i)
    (S i n) (T n i) n (hST i n hn) (hTZ n hn i)
  have hh := hall i
  dsimp only at hh
  rw [ef,ep] at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hq i⟩

end ThreeTorus
end
end

section

/-! Conjugation symmetry survives the literal retained coefficients. Smooth
cutoffs can be made reflection-compatible by a product, without losing the
already constructed exact disjointness of their supports. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma retainedAmplitude_reflect (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) (p : UnitAddCircle × UnitAddCircle) :
    retainedAmplitude ψ (fun s a => χ (-s) a) (-m) H (fun x => conj (A x)) n j p =
      conj (retainedAmplitude ψ χ m H A n (-j) p) := by
  simp only [retainedAmplitude,exactPassageCoeff_neg,Int.cast_neg,neg_div,map_mul,
    Complex.conj_ofReal,fourier_neg]

end ThreeTorus
end
end

section

/-! Actual conjugation data, invariant cutoff choices, and canonical spectral
reflection. No symmetry of an approximate model is substituted for reality of
the packets. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

variable {F}

lemma Reflection.involutive {τ : ι → ι} (h : F.Reflection τ) (hi : Injective F.m) :
    Involutive τ := fun i => hi (by rw [h.index,h.index,neg_neg])

lemma Reflection.core {τ : ι → ι} (h : F.Reflection τ) (i : ι) :
    F.core (τ i) = F.core i := by
  unfold PassagePackets.core tsupport
  congr 1
  ext x
  simp only [mem_support,h.lift,map_ne_zero]

end PassagePackets

/-- Reflection-compatible, exactly disjoint cutoffs with the full tracking
and stationary identity used by the actual neutral and signal producers. -/
theorem tracked_symmetric_cutoffs_fixed_carrier {ι : Type*} [Finite ι]
    (F : PassagePackets ι) (hi : Injective F.m) (hmod : F.SpareIndependent)
    {τ : ι → ι} (hr : F.Reflection τ) {c : ℕ}
    (hc : 0 < c ∧ (∀ i x, (F.m i:ℝ)*((c:ℝ)+F.periodic.lift x) ≠ 0) ∧
      ∀ i j x y, (F.m i:ℝ)*((c:ℝ)+F.periodic.lift x) =
        (F.m j:ℝ)*((c:ℝ)+F.periodic.lift y) → F.m i = F.m j)
    {η : ℝ} (hη : 0 < η) :
    0 < c ∧ ∃ χ : ι → ℝ → ℝ,
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ i) ∧ HasCompactSupport (χ i) ∧
        χ i 0 = 0 ∧ (∀ s, 0 ≤ χ i s ∧ χ i s ≤ 1) ∧
        (∀ s ∈ tsupport (χ i), ∃ x ∈ F.core i, |s-(F.m i:ℝ)*((c:ℝ)+F.V x)| < η) ∧
        ∀ (C : Set ℝ) a s, stationaryWeight C
          (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) (F.A₀ i a) s ≠ 0 → χ i s = 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
      (∀ i s, χ (τ i) s = χ i (-s)) := by
  have hzero i : 0 ∉ (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) '' F.core i := by
    rintro ⟨x,_hx,he⟩
    exact hc.2.1 i (x:UnitAddCircle) he
  have hsep : Pairwise (fun i j => Disjoint
      ((fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) '' F.core i)
      ((fun x => (F.m j:ℝ)*((c:ℝ)+F.V x)) '' F.core j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro s ⟨x,_hx,rfl⟩ ⟨y,_hy,he⟩
    exact hij (hi (hc.2.2 i j (x:UnitAddCircle) (y:UnitAddCircle) he.symm))
  obtain ⟨χ,hχ,hd⟩ := tracked_frequency_cutoffs F.m (fun x => (c:ℝ)+F.V x) F.core
    (continuous_const.add F.smooth_speed.continuous) F.core_compact hzero hsep hη
  let ψ : ι → ℝ → ℝ := fun i s => χ i s*χ (τ i) (-s)
  have hsub i : tsupport (ψ i) ⊆ tsupport (χ i) := tsupport_mul_subset_left
  refine ⟨hc.1,ψ,fun i => ⟨(hχ i).1.mul ((hχ (τ i)).1.comp contDiff_neg),
    (hχ i).2.1.mul_right,?_,?_,?_,?_⟩,?_,?_⟩
  · simp only [ψ,(hχ i).2.2.1,zero_mul]
  · intro s
    exact ⟨mul_nonneg ((hχ i).2.2.2.1 s).1 ((hχ (τ i)).2.2.2.1 (-s)).1,
      (mul_le_mul ((hχ i).2.2.2.1 s).2 ((hχ (τ i)).2.2.2.1 (-s)).2
        ((hχ (τ i)).2.2.2.1 (-s)).1 zero_le_one).trans (by norm_num)⟩
  · intro s hs
    exact (hχ i).2.2.2.2.2.1 s (hsub i hs)
  · intro C a s hs
    have hsi := stationaryWeight_support_subset (F.support_subset_core hmod i a) hs
    obtain ⟨x,hx,hxs⟩ := hsi
    have hre : -s ∈ (fun x => (F.m (τ i):ℝ)*((c:ℝ)+F.V x)) '' F.core (τ i) := by
      refine ⟨x,(hr.core i).symm ▸ hx,?_⟩
      simp only [hr.index,Int.cast_neg,neg_mul,hxs]
    have hleft := (hχ i).2.2.2.2.2.2 C (F.A₀ i a) (F.support_subset_core hmod i a) s hs
    have hright := ((hχ (τ i)).2.2.2.2.1 (-s) hre).self_of_nhds
    change χ (τ i) (-s) = 1 at hright
    simp only [ψ,hleft,hright,one_mul]
  · intro i j hij
    exact (hd hij).mono (hsub i) (hsub j)
  · intro i s
    simp only [ψ,hr.involutive hi i,neg_neg,mul_comm]

end ThreeTorus
end
end

section

/-! Support tracking for the actual next packets. Canonical density support
is linked to a genuine old-amplitude point; the same point controls both
normalized angular indices and temporal frequencies. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma periodic_real_bound {J : ℝ → ℝ} (hs : Continuous J) (hp : Periodic J 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |J x| ≤ B := by
  have hc : Continuous hp.lift := by
    apply Continuous.quotient_lift
    exact hs
  obtain ⟨B,hB⟩ := (isCompact_range hc).isBounded.exists_norm_le
  exact ⟨max B 0,le_max_right _ _,fun x =>
    (hB _ (mem_range_self (x:UnitAddCircle))).trans (le_max_left _ _)⟩

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PhysicalJets
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite passage geometry families, physical charts, and all-jet bounds. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PassageGeometryFamily
variable {V : ℝ → ℝ} (g : PassageGeometryFamily V)

/-- Smoothness of the retained speed recovers smoothness of the actual jitter;
no additional regularity hypothesis on a passage is needed. -/
lemma smooth_jitter_of_output {ι : Type*} (G : PassagePackets ι) {n : ℕ}
    (hn : 0 < n) (hG : G.V = fun x => (1+g.J₀ x/n)/n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g.J₀ := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have he : g.J₀ = fun x => (n:ℝ)*((n:ℝ)*G.V x-1) := by
    funext x
    rw [hG]
    field_simp
    ring
  rw [he]
  exact contDiff_const.mul ((contDiff_const.mul G.smooth_speed).sub contDiff_const)

lemma correctedFamily_zero (r : ℝ) : g.correctedFamily r (0,0) =
    fun x : Cover => ![x 0+r*V (x 1),x 1,x 2] := by
  funext x
  rw [correctedFamily,passageFamily_zero]
  ext i
  fin_cases i <;> simp
  ring

lemma correctedFamily_smooth (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g.J₀) (r : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (ℝ × ℝ) × Cover => g.correctedFamily r p.1 p.2) :=
  (smooth_passageFamily (contDiff_const.add hV) hJ r).sub contDiff_const

/-- Every spatial jet still converges after an arbitrary fixed smooth change
of physical coordinates. Both signs of the map use this same theorem. -/
lemma physical_jets_tendsto (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g.J₀)
    {A B : Cover → Cover} (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    (r : ℝ) {K : Set Cover} (hK : IsCompact K) (d : ℕ) :
    TendstoUniformlyOn
      (fun (n : ℕ) x => iteratedFDeriv ℝ d
        (fun y => B (g.correctedFamily r ((n:ℝ)⁻¹,g.Δ n) (A y))) x)
      (fun x => iteratedFDeriv ℝ d
        (fun y => B ![A y 0+r*V (A y 1),A y 1,A y 2]) x) atTop K := by
  have hs := hB.comp ((g.correctedFamily_smooth hV hJ r).comp
    (contDiff_fst.prodMk (hA.comp contDiff_snd)))
  have ht := smooth_parameter_jets_tendsto hs (0,0) hK d
  have he (x : Cover) : g.correctedFamily r (0,0) (A x) =
      ![A x 0+r*V (A x 1),A x 1,A x 2] := congrFun (g.correctedFamily_zero r) (A x)
  change TendstoUniformlyOn
    (fun a x => iteratedFDeriv ℝ d (fun y => B (g.correctedFamily r a (A y))) x)
    (fun x => iteratedFDeriv ℝ d (fun y => B (g.correctedFamily r (0,0) (A y))) x)
    (𝓝 (0,0)) K at ht
  simp only [he] at ht
  exact fun U hU => (passage_parameters_tendsto g.delta_bound).eventually (ht U hU)

end PassageGeometryFamily
end ThreeTorus
end
end

section

/-! Global smooth cover charts with independently chosen deck representatives
for the two signs. This makes the corrected physical passage lift compatible
with further coordinate changes, rather than losing the integer carrier. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PassageGeometryFamily
variable {V : ℝ → ℝ} (g : PassageGeometryFamily V)

lemma chart_twist_chartInv (hV : Continuous V) {n : ℕ} (hn : 0 < n) (r : ℝ) (x : Cover) :
    coverChartInv (g.primitive n) (coverTwist (fun a => (1+g.J₀ a/n)/n) r
      (coverChart (g.primitive n) x)) =
      passageFamily (fun t => (g.c:ℝ)+V t) g.J₀ r ((n:ℝ)⁻¹,g.Δ n) x := by
  have hi := passageFamily_increment (v := fun t => (g.c:ℝ)+V t) (J := g.J₀) (continuous_const.add hV) hn (g.Δ n) r (x 1) (x 2)
  have he (a : ℝ) : (1+g.J₀ a/n)/n = (n:ℝ)⁻¹+(n:ℝ)⁻¹^2*g.J₀ a := by
    simp only [div_eq_mul_inv]
    ring
  have hs : r*((n:ℝ)⁻¹+(n:ℝ)⁻¹^2*g.J₀ (x 2)) =
      r*(n:ℝ)⁻¹*(1+(n:ℝ)⁻¹*g.J₀ (x 2)) := by ring
  ext i
  fin_cases i
  · dsimp [coverChartInv,coverChart,coverTwist,passageFamily,primitive]
    rw [he]
    linarith [hi]
  · dsimp [coverChartInv,coverChart,coverTwist,passageFamily]
    rw [he,hs]
  · rfl

end PassageGeometryFamily

namespace PhysicalFrame

lemma next_mapLift (F : PhysicalFrame) {V : ℝ → ℝ} (g : PassageGeometryFamily V)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) {n : ℕ} (hn : 0 < n) (k : ℤ) :
    (F.next g hV n).mapLift (fun a => (1+g.J₀ a/n)/n) k =
      fun x => F.backward k (g.correctedFamily (k:ℝ) ((n:ℝ)⁻¹,g.Δ n) (F.forward x)) := by
  funext x
  change F.backward k (coverDeck (-k*(g.c:ℤ))
    (coverChartInv (g.primitive n) (coverTwist _ (k:ℝ) (coverChart (g.primitive n) (F.forward x))))) = _
  rw [g.chart_twist_chartInv hV.continuous hn]
  congr 1
  ext i
  fin_cases i <;> simp [coverDeck,PassageGeometryFamily.correctedFamily,sub_eq_add_neg]

end PhysicalFrame
end ThreeTorus
end
end

section

/-! Finite summation and composition estimates in the original physical L².
These let the literal per-packet passages be assembled without replacing their
vectors by independent spectral models. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma physicalError_integrable {f g : TripleTorus → ℂ} (hf : Continuous f) (hg : Continuous g) :
    Integrable (fun x => ‖f x-g x‖^2) tripleVolume :=
  ((hf.sub hg).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma physicalError_sum {ι : Type*} [Fintype ι] {f g : ι → TripleTorus → ℂ}
    (hf : ∀ i, Continuous (f i)) (hg : ∀ i, Continuous (g i)) :
    physicalError (fun x => ∑ i, f i x) (fun x => ∑ i, g i x) ≤
      (Fintype.card ι:ℝ)*(∑ i, physicalError (f i) (g i)) := by
  have he x : (∑ i, f i x)-(∑ i, g i x) = ∑ i, (f i x-g i x) :=
    (Finset.sum_sub_distrib _ _).symm
  have hp x : ‖(∑ i, f i x)-(∑ i, g i x)‖^2 ≤
      (Fintype.card ι:ℝ)*(∑ i, ‖f i x-g i x‖^2) := by
    rw [he]
    calc
      _ ≤ (∑ i, ‖f i x-g i x‖)^2 := by
        gcongr
        exact norm_sum_le _ _
      _ ≤ _ := by simpa only [Finset.card_univ] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖f i x-g i x‖))
  unfold physicalError
  calc
    _ ≤ ∫ x, (Fintype.card ι:ℝ)*(∑ i, ‖f i x-g i x‖^2) ∂tripleVolume :=
      integral_mono
        (physicalError_integrable (continuous_finsetSum _ (fun i _ => hf i))
          (continuous_finsetSum _ (fun i _ => hg i)))
        ((integrable_finsetSum _ (fun i _ => physicalError_integrable (hf i) (hg i))).const_mul _) hp
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => physicalError_integrable (hf i) (hg i))]

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PredictionModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Block tests, diagonal predictions, centering, and stability of finite-color models. -/

section

/-! Quantitative passage from the fixed pre-block model to actual color
 densities, source 04:239--286 and 409--437. No geometric approximation oracle
 is introduced: these are deterministic L1 stability estimates. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma continuous_circle_integrable {f : UnitAddCircle → ℝ} (hf : Continuous f) :
    Integrable f phaseHaar :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_TrackedPackets
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refresh and residue estimates, physical aggregates, tracked producers, pair/color aggregates, and colored states. -/

section

/-! Physical vectors and spectral densities grouped by their actual source
packet. No spectral data is chosen independently of the literal amplitudes. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma continuous_outputDensity {ι : Type*} {S : ι → Finset ℤ}
    (G : PassagePackets (PassageOutputIndex S)) (i : ι) : Continuous (outputDensity G i) :=
  continuous_finsetSum _ (fun _ _ => G.density_continuous _)

lemma continuous_outputVector {ι : Type*} {S : ι → Finset ℤ}
    (G : PassagePackets (PassageOutputIndex S)) (i : ι) : Continuous (outputVector G i) := by
  apply continuous_finsetSum
  intro j _
  exact continuous_packet (G.continuous_amplitude ⟨i,j⟩)

lemma outputVector_eq_retained {ι : Type*} {S : ι → Finset ℤ}
    (F : PassagePackets ι) (G : PassagePackets (PassageOutputIndex S))
    (ψ : UnitAddCircle → ℝ) (χ : ι → ℝ → UnitAddCircle → ℝ)
    (H : ℕ → UnitAddCircle → UnitAddCircle) (n : ℕ)
    (hm : ∀ i, G.m i = i.2.val)
    (hA : ∀ i, G.A i = retainedAmplitude ψ (χ i.1) (F.m i.1) H (F.A i.1) n i.2.val)
    (i : ι) :
    outputVector G i = retainedPassage (F.m i) (H n) (F.A i) (S i)
      (fun j => χ i ((j:ℝ)/n)) ψ := by
  funext x
  unfold outputVector
  simp_rw [hm,hA]
  exact Finset.sum_coe_sort (S i) (fun j =>
    packet j (retainedAmplitude ψ (χ i) (F.m i) H (F.A i) n j) x)

/-- L1 error of a finite sum, with continuity discharging integrability. -/
lemma integral_abs_sum_sub_le {ι : Type*} [Fintype ι]
    {p q : ι → UnitAddCircle → ℝ} (hp : ∀ i, Continuous (p i)) (hq : ∀ i, Continuous (q i)) :
    (∫ z, |(∑ i, p i z)-(∑ i, q i z)| ∂phaseHaar) ≤
      ∑ i, ∫ z, |p i z-q i z| ∂phaseHaar := by
  have he z : (∑ i, p i z)-(∑ i, q i z) = ∑ i, (p i z-q i z) :=
    (Finset.sum_sub_distrib (s := Finset.univ) (fun i => p i z) (fun i => q i z)).symm
  simp_rw [he]
  have hint (i : ι) : Integrable (fun z => |p i z-q i z|) phaseHaar :=
    continuous_circle_integrable ((hp i).sub (hq i)).abs
  calc
    _ ≤ ∫ z, ∑ i, |p i z-q i z| ∂phaseHaar := integral_mono
      (continuous_circle_integrable (continuous_finsetSum _ (fun i _ => (hp i).sub (hq i))).abs)
      (integrable_finsetSum _ (fun i _ => hint i))
      (fun z => Finset.abs_sum_le_sum_abs _ _)
    _ = _ := integral_finsetSum _ (fun i _ => hint i)

end ThreeTorus
end
end

section

/-! Literal color sums in the concrete packet state. Colors are labels, not
new independent spectral data. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

variable {ι R : Type*} [Fintype ι] [DecidableEq R]

lemma colored_physical_bound {f g : ι → TripleTorus → ℂ}
    (hf : ∀ i, Continuous (f i)) (hg : ∀ i, Continuous (g i))
    (c : ι → R) (r : R) {e ε : ℝ} (he : 0 ≤ e)
    (h : ∀ i, physicalError (f i) (g i) ≤ e)
    (hε : (Fintype.card ι:ℝ)^2*e < ε) :
    physicalError (fun x => ∑ i, if c i = r then f i x else 0)
      (fun x => ∑ i, if c i = r then g i x else 0) < ε := by
  have hf' i : Continuous (fun x => if c i = r then f i x else 0) := by
    split_ifs <;> first | exact hf i | exact continuous_const
  have hg' i : Continuous (fun x => if c i = r then g i x else 0) := by
    split_ifs <;> first | exact hg i | exact continuous_const
  have hb i : physicalError (fun x => if c i = r then f i x else 0)
      (fun x => if c i = r then g i x else 0) ≤ e := by
    split_ifs <;> first | exact h i | simpa [physicalError] using he
  apply (physicalError_sum hf' hg').trans_lt
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i))
    (show (0:ℝ) ≤ Fintype.card ι from Nat.cast_nonneg _)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  apply hh.trans_lt
  simpa only [sq,mul_assoc] using hε

lemma colored_density_bound {p q : ι → UnitAddCircle → ℝ}
    (hp : ∀ i, Continuous (p i)) (hq : ∀ i, Continuous (q i))
    (c : ι → R) (r : R) (mass : ι → ℝ) {e γ ω : ℝ} (he : 0 ≤ e)
    (h : ∀ i, (∫ z, |p i z-q i z| ∂phaseHaar) ≤ γ*ω*mass i+e) :
    (∫ z, |(∑ i, if c i = r then p i z else 0)-(∑ i, if c i = r then q i z else 0)| ∂phaseHaar) ≤
      γ*ω*(∑ i, if c i = r then mass i else 0)+(Fintype.card ι:ℝ)*e := by
  have hp' i : Continuous (fun z => if c i = r then p i z else 0) := by
    split_ifs <;> first | exact hp i | exact continuous_const
  have hq' i : Continuous (fun z => if c i = r then q i z else 0) := by
    split_ifs <;> first | exact hq i | exact continuous_const
  apply (integral_abs_sum_sub_le hp' hq').trans
  calc
    _ ≤ ∑ i, (γ*ω*(if c i = r then mass i else 0)+e) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> first | exact h i | simpa using he
    _ = _ := by rw [Finset.sum_add_distrib,Finset.mul_sum]; simp

end ThreeTorus
end
end

section

/-! A finite colored state and a pair record containing the two ACTUAL
smooth volume-preserving passage families. The existence theorem is derived
from the concrete neutral/signal producers, not supplied as an oracle. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

attribute [instance] ColoredState.finite

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_ColorBlocks
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Block transfer, cofinal frequency trees, color-density products, finite iteration, and actual anchored blocks. -/

section

/-! Uniform open room for actual anchors, and their exact temporal deviation.
These bounds do not take a model density or a later passage as input. -/
noncomputable section
open Set Function Filter MeasureTheory Complex
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma anchor_temporal_deviation {j : ℤ} {n : ℕ} (hn : 0 < n) (J : ℝ)
    {D R : ℝ} (hj : |(j:ℝ)/(n:ℝ)| ≤ D) (hJ : |J| ≤ R) :
    dist ((j:ℝ)*((1+J/(n:ℝ))/(n:ℝ)):UnitAddCircle) ((j:ℝ)/(n:ℝ):UnitAddCircle) ≤ D*R/(n:ℝ) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  calc
    _ ≤ |(j:ℝ)*((1+J/(n:ℝ))/(n:ℝ))-(j:ℝ)/(n:ℝ)| := circle_dist_le_real _ _
    _ = |(j:ℝ)/(n:ℝ)| *|J|/(n:ℝ) := by
      have he : (j:ℝ)*((1+J/(n:ℝ))/(n:ℝ))-(j:ℝ)/(n:ℝ) = ((j:ℝ)/(n:ℝ))*J/(n:ℝ) := by ring
      rw [he,abs_div,abs_mul,abs_of_pos hnR]
    _ ≤ D*R/(n:ℝ) := div_le_div_of_nonneg_right
      (mul_le_mul hj hJ (abs_nonneg _) ((abs_nonneg _).trans hj)) hnR.le

/-- Coefficient substitution on EVERY new speed point (not only a nonzero
spectral-density set). This is what the next real packet passage needs. -/
theorem anchor_coefficient_budget {ι : Type*} [Fintype ι]
    {q : UnitAddCircle → ℂ} (hq : Continuous q)
    {d : ℝ → ℂ} (a : ι → ℂ) {D ω : ℝ} (hω : 0 < ω) :
    ∀ R : ℝ, ∀ᶠ n : ℕ in atTop, 0 < n ∧
      ∀ (j : ℤ) (i : ι) (J : ℝ), |(j:ℝ)/(n:ℝ)| ≤ D → |J| ≤ R →
        d ((j:ℝ)/(n:ℝ)) = a i-q ((j:ℝ)/(n:ℝ):UnitAddCircle) →
        ‖d ((j:ℝ)/(n:ℝ))-(a i-q ((j:ℝ)*((1+J/(n:ℝ))/(n:ℝ)):UnitAddCircle))‖ < ω := by
  obtain ⟨η,hη,hU⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hq) ω hω
  intro R
  have ht : ∀ᶠ n : ℕ in atTop, D*R/(n:ℝ) < η :=
    ((tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hη))
  filter_upwards [ht,eventually_gt_atTop (0:ℕ)] with n hn hnp
  refine ⟨hnp,?_⟩
  intro j i J hj hJ he
  rw [he]
  have hh := hU ((anchor_temporal_deviation hnp J hj hJ).trans_lt hn)
  rw [dist_eq_norm] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma colorVector_output {ι R : Type*} [Fintype ι] [DecidableEq R]
    {S : ι → Finset ℤ} (G : PassagePackets (PassageOutputIndex S))
    (c : ι → R) (r : R) (x : TripleTorus) :
    colorVector G (c ∘ Sigma.fst) r x =
      ∑ i, if c i = r then outputVector G i x else 0 := by
  unfold colorVector outputVector
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : c i = r
  · simp only [Function.comp_apply,h,ite_true]
  · simp only [Function.comp_apply,h,ite_false,Finset.sum_const_zero]

lemma colorDensity_output {ι R : Type*} [Fintype ι] [DecidableEq R]
    {S : ι → Finset ℤ} (G : PassagePackets (PassageOutputIndex S))
    (c : ι → R) (r : R) (z : UnitAddCircle) :
    colorDensity G (c ∘ Sigma.fst) r z =
      ∑ i, if c i = r then outputDensity G i z else 0 := by
  unfold colorDensity outputDensity
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : c i = r
  · simp only [Function.comp_apply,h,ite_true]
  · simp only [Function.comp_apply,h,ite_false,Finset.sum_const_zero]

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_SymmetricPackets
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reflected neutral and signal producers, symmetric colors, physical control, and grouped cutoffs. -/

section

/-! The actual retained family, including its real compactly supported lifts,
preserves conjugation, with the literal inherited parent on its finite indices. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma retainedRealAmplitude_reflect (ψ : ℝ → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (s : ℝ) (j : ℤ) (a : UnitAddCircle) (x : ℝ) :
    retainedRealAmplitude ψ (fun s a => χ (-s) a) (-m) H (fun p => conj (A p)) s j a x =
      conj (retainedRealAmplitude ψ χ m H A (-s) (-j) a x) := by
  simp only [retainedRealAmplitude,retainedRealCore,exactPassageCoeff_neg,
    map_mul,Complex.conj_ofReal,fourier_neg]

lemma literal_output_reflection {ι : Type*} (F : PassagePackets ι)
    {τ : ι → ι} (hr : F.Reflection τ)
    (ψ : UnitAddCircle → ℝ) (ψ₀ : ℝ → ℝ) (χ : ι → ℝ → UnitAddCircle → ℝ)
    (H : ℕ → UnitAddCircle → UnitAddCircle) (n : ℕ) (S : ι → Finset ℤ)
    (hs : ∀ i j, j ∈ S (τ i) ↔ -j ∈ S i)
    (hχ : ∀ i s a, χ (τ i) s a = χ i (-s) a)
    (G : PassagePackets (PassageOutputIndex S))
    (hGm : ∀ i, G.m i = i.2.val)
    (hGA : ∀ i, G.A i = retainedAmplitude ψ (χ i.1) (F.m i.1) H (F.A i.1) n i.2.val)
    (hGA₀ : ∀ i, G.A₀ i = retainedRealAmplitude ψ₀ (χ i.1) (F.m i.1) (H n) (F.A i.1)
      ((i.2.val:ℝ)/n) i.2.val) :
    ∃ τG : PassageOutputIndex S → PassageOutputIndex S,
      (∀ i, (τG i).1 = τ i.1) ∧ G.Reflection τG := by
  let τG := reflectedOutputIndex τ S hs
  have hχ' i : χ (τ i) = fun s a => χ i (-s) a := funext (fun s => funext (hχ i s))
  have hA i : F.A (τ i) = fun p => conj (F.A i p) := funext (hr.amplitude i)
  refine ⟨τG,fun _ => rfl,⟨?_,?_,?_⟩⟩
  · intro i
    simp only [hGm,τG,reflectedOutputIndex]
  · intro i p
    rw [hGA,hGA]
    change retainedAmplitude ψ (χ (τ i.1)) (F.m (τ i.1)) H (F.A (τ i.1)) n (-i.2.val) p = _
    rw [hχ',hr.index,hA,retainedAmplitude_reflect,neg_neg]
  · intro i a x
    rw [hGA₀,hGA₀]
    change retainedRealAmplitude ψ₀ (χ (τ i.1)) (F.m (τ i.1)) (H n) (F.A (τ i.1))
      (((-i.2.val:ℤ):ℝ)/n) (-i.2.val) a x = _
    rw [hχ',hr.index,hA,retainedRealAmplitude_reflect]
    simp only [Int.cast_neg,neg_div,neg_neg]

lemma scalar_exact_indices_reflect {ι : Type*} {τ : ι → ι}
    {χ : ι → ℝ → ℝ} (hχ : ∀ i s, χ (τ i) s = χ i (-s))
    {S : ι → Finset ℤ} {n : ℕ} (he : ∀ i j, j ∈ S i ↔ χ i ((j:ℝ)/n) ≠ 0) :
    ∀ i j, j ∈ S (τ i) ↔ -j ∈ S i := by
  intro i j
  rw [he,he,hχ]
  simp only [Int.cast_neg,neg_div]

end ThreeTorus
end
end

section

/-! Full actual neutral producer, with conjugation of both amplitudes and
compact real lifts, inherited parent indices, and arbitrary final good arc. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

theorem eventually_neutral_anchor_reflected_family {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) (hi : Injective F.m) (hmod : F.SpareIndependent)
    {τref : ι → ι} (hr : F.Reflection τref)
    :
    ∀ᶠ c : ℕ in atTop, ∀ Q : ℕ, 0 < Q → ∀ ε τ κ : ℝ, 0 < ε → 0 < τ → 0 < κ →
      0 < c ∧ ∃ δ : ℝ, ∃ cut : LawCutoffs δ, ∃ L : ℝ,
      ∃ χ : ι → ℝ → ℝ, ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ 0 < L ∧
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ i) ∧ HasCompactSupport (χ i) ∧
        χ i 0 = 0 ∧ (∀ s, 0 ≤ χ i s ∧ χ i s ≤ 1) ∧
        ∀ s ∈ tsupport (χ i), ∃ x ∈ F.core i,
          |s-(F.m i:ℝ)*((c:ℝ)+F.V x)| < τ) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
      (∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹) ∧ Tendsto Δ atTop (𝓝 0) ∧
      (∀ n, Continuous (H n)) ∧
      (∀ n (x : ℝ), H n (x:UnitAddCircle) =
        ((n:ℝ)*((∫ t in 0..x, (c:ℝ)+F.V t)+Δ n*x):UnitAddCircle)) ∧
      let ψ := neutralCircleCutoff cut
      let J := neutralJitter cut L 0
      let J₀ := neutralJitterReal cut L 0
      let σ := fun (n : ℕ) a => (((1+J a/n)/n:ℝ):UnitAddCircle)
      (∀ n, Smooth (torusPassage (H n) (σ n)) ∧ Smooth (torusPassage (H n) (σ n)).symm ∧
        MeasurePreserving (torusPassage (H n) (σ n)) μ μ) ∧
      (∀ n, 0 < n → ∀ x : Cover,
        torusPassage (H n) (σ n) (project x) =
          project (passageFamily (fun t => (c:ℝ)+F.V t) J₀ 1 ((n:ℝ)⁻¹,Δ n) x) ∧
        (torusPassage (H n) (σ n)).symm (project x) =
          project (passageFamily (fun t => (c:ℝ)+F.V t) J₀ (-1) ((n:ℝ)⁻¹,Δ n) x)) ∧
      (∀ r : ℝ, ∀ K : Set Cover, IsCompact K → ∀ d : ℕ,
        TendstoUniformlyOn
          (fun (n : ℕ) x => iteratedFDeriv ℝ d
            (passageFamily (fun t => (c:ℝ)+F.V t) J₀ r ((n:ℝ)⁻¹,Δ n)) x)
          (fun x => iteratedFDeriv ℝ d (fun y : Cover => ![y 0+r*((c:ℝ)+F.V (y 1)),y 1,y 2]) x)
          atTop K) ∧
      ∃ S : ℕ → ι → Finset ℤ,
        (∀ n, 0 < n → Pairwise (fun i j => Disjoint (S n i) (S n j))) ∧
        (∀ n, 0 < n → ∀ i j, j ∈ S n i ↔ χ i ((j:ℝ)/n) ≠ 0) ∧
        ∀ᶠ n : ℕ in atTop, 0 < n ∧
          (∀ i,
            let f := retainedPassage (F.m i) (H n) (F.A i) (S n i) (fun j _ => χ i ((j:ℝ)/n)) ψ
            let p := exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ (fun s _ => χ i s)
              (F.m i) H (F.A i) (S n i) n
            (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-f (passageChart (H n) x)‖^2
              ∂tripleVolume) < ε ∧
            (∫ z, |p z-F.density i z| ∂AddCircle.haarAddCircle) < ε ∧
            (∀ k : ℤ, (∫ x : TripleTorus, starRingEnd ℂ (f x)*f (twistIter (σ n) k x) ∂tripleVolume) =
              ∫ z, (p z:ℂ)*fourier k z ∂AddCircle.haarAddCircle) ∧
            (∑ h : Fin Q, ∫ z,
              |exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ (fun s _ => χ i s) (F.m i) H (F.A i)
                ((S n i).filter (fun j => j % (Q:ℤ) = (h.val:ℤ) % (Q:ℤ))) n z-
                  (Q:ℝ)⁻¹*F.density i z| ∂AddCircle.haarAddCircle) < ε) ∧
          ∃ G : PassagePackets (PassageOutputIndex (S n)),
            Injective G.m ∧ G.SpareIndependent ∧
            G.V = (fun x => (1+J₀ x/n)/n) ∧
            (∀ i, G.m i = i.2.val) ∧
            (∀ i, G.A i = retainedAmplitude ψ (fun s _ => χ i.1 s) (F.m i.1) H (F.A i.1) n i.2.val) ∧
            (∀ i, G.density i = exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ
              (fun s _ => χ i.1 s) (F.m i.1) H (F.A i.1) {i.2.val} n) ∧
            (∀ i (E : ℤ → Prop) [DecidablePred E],
              exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ
                (fun s _ => χ i s) (F.m i) H (F.A i) ((S n i).filter E) n =
              fun z => ∑ j : ↥(S n i), if E j.val then G.density ⟨i,j⟩ z else 0) ∧
            ∃ τG : PassageOutputIndex (S n) → PassageOutputIndex (S n),
              (∀ i, (τG i).1 = τref i.1) ∧ G.Reflection τG ∧ G.GoodArc δ := by
  classical
  filter_upwards [eventually_integral_speed_separation F.m F.periodic.lift F.nonzero F.speed_continuous] with c hsep
  intro Q hQ ε τ κ hε hτ hκ
  obtain ⟨B,hB,hAB⟩ := F.amplitude_bound
  have hden : 0 < 32*(B+1) := by positivity
  obtain ⟨δ,hδ,hδall⟩ := exists_between (lt_min
    (lt_min (by norm_num : (0:ℝ)<1/8) (div_pos hε hden)) hκ)
  have hδhi := hδall.trans_le (min_le_left _ _)
  have hδκ := hδall.trans_le (min_le_right _ _)
  have hδ' : δ < 1/8 := hδhi.trans_le (min_le_left _ _)
  have hδB : 8*δ*B < ε/4 := by
    have hh := (lt_div_iff₀ hden).mp (hδhi.trans_le (min_le_right _ _))
    nlinarith
  let cut := lawCutoffs δ hδ hδ'
  obtain ⟨hcp,χ,hχ,hdisj,hχsym⟩ := tracked_symmetric_cutoffs_fixed_carrier F hi hmod hr hsep hτ
  let Fc := F.carrier (c:ℤ)
  let X : ι → ℝ → UnitAddCircle → ℝ := fun i s _ => χ i s
  have hXs i : CylinderSmooth (X i).uncurry := by
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => χ i p.1)
    exact (hχ i).1.comp contDiff_fst
  have hXc i : Continuous (X i).uncurry := (hχ i).1.continuous.comp continuous_fst
  have hXcompact i : HasCompactSupport (X i).uncurry := compactSupport_frequency_cylinder (hχ i).2.1
  have hXzero i (a : UnitAddCircle) : X i 0 a = 0 := (hχ i).2.2.1
  have hXbound i s (a : UnitAddCircle) : 0 ≤ X i s a ∧ X i s a ≤ 1 := (hχ i).2.2.2.1 s
  have hXW i s a : stationaryWeight (Icc (Fc.l-Fc.R) (Fc.u+Fc.R))
      (fun x => (Fc.m i:ℝ)*Fc.V x) (Fc.A₀ i a) s ≠ 0 → X i s a = 1 := by
    simpa only [Fc,PassagePackets.carrier,Int.cast_natCast] using
      (hχ i).2.2.2.2.2 (Icc (F.l-F.R) (F.u+F.R)) a s
  have hzero i : 0 ∉ (fun x => (Fc.m i:ℝ)*Fc.V x) '' Icc Fc.l Fc.u := by
    rintro ⟨x,_hx,he⟩
    apply hsep.2.1 i (x:UnitAddCircle)
    change (F.m i:ℝ)*((c:ℝ)+F.V x) = 0
    simpa only [Fc,PassagePackets.carrier,Int.cast_natCast] using he
  obtain ⟨Δ,H,hΔ,hΔt,hHc,hHe,C,Cq,_hC,_hCq,hrest⟩ :=
    exists_simultaneous_neutral_residue_passage Fc.nonzero Fc.lift_matches Fc.two Fc.continuous_lift
      Fc.continuous_deriv Fc.smooth_lift Fc.support_lift Fc.lo Fc.uo Fc.lu Fc.Rpos
      Fc.periodic Fc.smooth_speed Fc.positive_deriv hzero Fc.continuous_amplitude Fc.smooth_amplitude
      (B := fun _ => B) (fun _ => hB) hAB cut hδ hδ' hXs hXc hXcompact hXzero hXbound hXW hQ
  have hsmall : 0 < ε/4 := by positivity
  have hCT i : ∀ᶠ L : ℝ in atTop, C i/L < ε/4 :=
    (tendsto_const_nhds.div_atTop tendsto_id).eventually (gt_mem_nhds hsmall)
  have hCqT i : ∀ᶠ L : ℝ in atTop, Cq i/L < ε/4 :=
    (tendsto_const_nhds.div_atTop tendsto_id).eventually (gt_mem_nhds hsmall)
  obtain ⟨L,hL,hCL,hCqL⟩ := ((eventually_gt_atTop (0:ℝ)).and
    (((Filter.eventually_all).mpr hCT).and ((Filter.eventually_all).mpr hCqT))).exists
  obtain ⟨hgeo,hgraph,hlimit,S,hSN,_hST,hTE,hgood⟩ := hrest L hL 0
  have hTE' n (hn : 0 < n) i j : j ∈ S n i ↔ χ i ((j:ℝ)/n) ≠ 0 := by
    simpa only [X,exists_const] using hTE n hn i j
  have hSd n (hn : 0 < n) : Pairwise (fun i j => Disjoint (S n i) (S n j)) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro k hki hkj
    exact Set.disjoint_left.mp (hdisj hij)
      (subset_tsupport _ ((hTE' n hn i k).mp hki)) (subset_tsupport _ ((hTE' n hn j k).mp hkj))
  refine ⟨hcp,δ,cut,L,χ,Δ,H,hδ,hδ',hδκ,hL,?_,hdisj,hΔ,hΔt,hHc,?_,?_,?_,?_,S,hSd,hTE',?_⟩
  · exact fun i => ⟨(hχ i).1,(hχ i).2.1,(hχ i).2.2.1,(hχ i).2.2.2.1,(hχ i).2.2.2.2.1⟩
  · simpa only [Fc,PassagePackets.carrier,Int.cast_natCast] using hHe
  · exact hgeo
  · simpa only [Fc,PassagePackets.carrier,Int.cast_natCast] using hgraph
  · simpa only [Fc,PassagePackets.carrier,Int.cast_natCast] using hlimit
  filter_upwards [hgood (ε/4) hsmall] with n hn
  have hn0 := hn.1
  refine ⟨hn0,?_,?_⟩
  · intro i
    have hh := hn.2 i
    dsimp only at hh ⊢
    have hPM := (Fc.density_marginal (F.carrier_spare (c:ℤ) hmod) i).trans
      (F.density_carrier hmod (c:ℤ) i)
    rw [hPM] at hh
    refine ⟨lt_trans hh.1 (by linarith), lt_trans hh.2.1 (by linarith [hCL i]),
      hh.2.2.2.1,lt_trans hh.2.2.2.2.2 (by linarith [hCqL i])⟩
  · let Hl (n : ℕ) (x : ℝ) := (n:ℝ)*((∫ t in 0..x, Fc.V t)+Δ n*x)
    have hHl n : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n) :=
      contDiff_const.mul ((contDiff_real_primitive Fc.smooth_speed).add (contDiff_const.mul contDiff_id))
    have hJs := neutralJitterReal_smooth cut L 0
    have hJd x (hx : x ∈ Ioo δ (1-δ)) : 0 < deriv (neutralJitterReal cut L 0) x := by
      rw [neutralJitterReal_deriv cut hδ L 0 hx]
      exact hL
    obtain ⟨G,hGm,hGA,hGA₀,hGV,hGo,hGl,hGu,hGmod⟩ := literal_output_packets
      F.m F.A H Hl X (S n) (hSN n hn0) F.continuous_amplitude F.smooth_amplitude
      hXs hXc hHc hHl hHe cut hδ hδ' (neutralJitterReal_periodic cut L 0) hJs hJd hn0
    have heψ : ∀ x ∈ Ioc (0:ℝ) (0+1), neutralCircleCutoff cut (x:UnitAddCircle) = cut.ψ x := by
      intro x hx
      rw [neutralCircleCutoff_coe]
      exact periodize_eq_on_unit ((subset_tsupport cut.ψ).trans
        (cut.ψ_support.trans (by intro z hz; constructor <;> linarith [hz.1,hz.2]))) ⟨hx.1.le,by simpa using hx.2⟩
    have hsψ : tsupport cut.ψ ⊆ Ioc (0:ℝ) (0+1) ∩ Ioo δ (1-δ) := by
      intro x hx
      have hh := cut.ψ_support hx
      exact ⟨⟨by linarith [hh.1],by linarith [hh.2]⟩,hh⟩
    have hJinj : InjOn (neutralJitterReal cut L 0) (Ioo δ (1-δ)) := by
      intro x hx y hy he
      rw [neutralJitterReal_affine cut hδ L 0 ⟨hx.1.le,hx.2.le⟩,
        neutralJitterReal_affine cut hδ L 0 ⟨hy.1.le,hy.2.le⟩] at he
      nlinarith
    have hGden (i : PassageOutputIndex (S n)) : G.density i =
        exactRetainedPacketDensity (Ioo δ (1-δ)) (neutralJitterReal cut L 0) (neutralCircleCutoff cut)
          (X i.1) (F.m i.1) H (F.A i.1) {i.2.val} n := by
      apply literal_packet_canonical_density G hGmod i (hGm i) (hGA i) ?_
        (continuous_neutralJitter cut L 0) hJs (fun _ _ => rfl) isOpen_Ioo hJinj
        (fun x hx => (hJd x hx).ne') (continuous_neutralCircleCutoff cut) cut.ψ_smooth cut.ψ_compact
        heψ hsψ (hXc i.1) (hXs i.1) hHc hHl hHe (F.continuous_amplitude i.1)
        (F.smooth_amplitude i.1) hn0
      intro a
      obtain ⟨x,rfl⟩ := Quotient.mk_surjective a
      change (G.V x:UnitAddCircle) = _
      rw [hGV]
      rfl
    refine ⟨G,?_,hGmod,hGV,hGm,hGA,hGden,?_,?_⟩
    · have he : G.m = fun i : PassageOutputIndex (S n) => i.2.val := funext hGm
      rw [he]
      exact output_index_injective (hSd n hn0)
    · intro i E inst
      simp_rw [hGden]
      exact exactRetainedPacketDensity_filtered_singletons hJs isOpen_Ioo hJinj
        (fun x hx => (hJd x hx).ne') cut.ψ_smooth cut.ψ_compact heψ hsψ (hXs i)
        hHl hHe (F.smooth_amplitude i) hn0 (hSN n hn0 i) E

    · obtain ⟨τG,hτG,hrG⟩ := literal_output_reflection F hr (neutralCircleCutoff cut) cut.ψ X H n (S n)
        (scalar_exact_indices_reflect hχsym (hTE' n hn0)) (fun i s _ => hχsym i s)
        G hGm hGA hGA₀
      refine ⟨τG,hτG,hrG,hGo,hGl,hGu,?_⟩
      intro x hx
      rw [hGV]
      exact positive_deriv_new_speed hn0 (hJd x hx)

end ThreeTorus
end
end

section

/-! Finite physical C-infinity restrictions, on both the map and inverse,
threaded through the actual refresh and transmission integer choices. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PhysicalJetData

lemma eventually_next (Q : PhysicalJetData) (F : PhysicalFrame) {V : ℝ → ℝ}
    (g : PassageGeometryFamily V) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g.J₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Q.Close ε F V (F.next g hV n) (fun a => (1+g.J₀ a/n)/n) := by
  have hj : ∀ᶠ n : ℕ in atTop, ∀ i : Fin Q.size, ∀ x ∈ Q.domain i,
      dist (iteratedFDeriv ℝ (Q.order i)
        (fun y => F.backward (Q.sign i) (g.correctedFamily (Q.sign i:ℝ)
          ((n:ℝ)⁻¹,g.Δ n) (F.forward y))) x)
        (iteratedFDeriv ℝ (Q.order i) (F.mapLift V (Q.sign i)) x) < ε := by
    apply eventually_all.2
    intro i
    simpa only [PhysicalFrame.mapLift,coverTwist,Function.comp_def,dist_comm] using
      (Metric.tendstoUniformlyOn_iff.1 (g.physical_jets_tendsto hV hJ F.forward_smooth
        (F.backward_smooth (Q.sign i)) (Q.sign i:ℝ) (Q.compact i) (Q.order i))) ε hε
  filter_upwards [hj,eventually_gt_atTop 0] with n hn hnp
  intro i x hx
  rw [F.next_mapLift g hV hnp]
  exact (hn i x hx).le

end PhysicalJetData

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_FiniteBlocks
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric anchored blocks, unconditional block production, physical mass, and estimator regularity. -/

section

/-! The correctly ordered anchor constructs the literal finite output state,
with coefficient matching valid on every next packet core. -/
noncomputable section
open Set Function Filter MeasureTheory Complex
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- Carrier first; signal, band and all block tolerances afterwards; anchor
integer last and still arbitrarily large. No modeled next densities occur. -/
theorem eventually_reflected_anchor_state {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) (hi : Injective F.m) (hmod : F.SpareIndependent)
    {τref : ι → ι} (hr : F.Reflection τref) :
    ∀ᶠ c : ℕ in atTop,
      ∀ (d : ℝ → ℂ) (q : UnitAddCircle → ℂ) (a : ι → ℂ), Continuous q →
      ∀ b D margin τ : ℝ, 0 < τ →
      (∀ i x, x ∈ F.core i → ∀ s,
        |s-(F.m i:ℝ)*((c:ℝ)+F.V x)| < τ →
        d s = a i-q (s:UnitAddCircle) ∧ b+margin ≤ |s| ∧ |s| ≤ D-margin) →
      ∀ ε ω κ : ℝ, 0 < ε → 0 < ω → 0 < κ →
      ∃ g : PassageGeometryFamily F.V, g.c = c ∧
      ∃ δ : ℝ, ∃ cut : LawCutoffs δ, ∃ L : ℝ,
        0 < δ ∧ δ < κ ∧ 0 < L ∧ g.J₀ = neutralJitterReal cut L 0 ∧
      ∃ S : ℕ → ι → Finset ℤ, ∀ᶠ n : ℕ in atTop, 0 < n ∧
        ∃ G : PassagePackets (PassageOutputIndex (S n)),
          Injective G.m ∧ G.SpareIndependent ∧
          G.V = (fun x => (1+g.J₀ x/n)/n) ∧ (∀ i, G.m i = i.2.val) ∧
          (∀ i,
            (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-
              outputVector G i (passageChart (g.H n) x)‖^2 ∂tripleVolume) < ε ∧
            (∫ z, |outputDensity G i z-F.density i z| ∂phaseHaar) < ε) ∧
          (∀ i, b+margin ≤ |(G.m i:ℝ)/n| ∧ |(G.m i:ℝ)/n| ≤ D-margin) ∧
          (∀ i y, ‖d ((G.m i:ℝ)/n)-
            (a i.1-q ((G.m i:ℝ)*G.V y:UnitAddCircle))‖ < ω) ∧
          ∃ τG : PassageOutputIndex (S n) → PassageOutputIndex (S n),
            (∀ i, (τG i).1 = τref i.1) ∧ G.Reflection τG ∧ G.GoodArc δ := by
  filter_upwards [eventually_neutral_anchor_reflected_family F hi hmod hr] with c hc
  intro d q a hq b D margin τ hτ hroom ε ω κ hε hω hκ
  obtain ⟨hcp,δ,cut,L,χ,Δ,H,hδ,_hδ',hδκ,hL,hχ,_hχd,hΔ,hΔt,hHc,hHe,
    hgeo,hgraph,hlimit,S,_hSd,hS,hgood⟩ := hc 1 (by norm_num) ε τ κ hε hτ hκ
  let g : PassageGeometryFamily F.V :=
    ⟨c,hcp,Δ,H,neutralJitter cut L 0,neutralJitterReal cut L 0,(fun _ => rfl),
      continuous_neutralJitter cut L 0,hΔ,hΔt,hHc,hHe,hgeo,hgraph,hlimit⟩
  obtain ⟨R,_hR,hRJ⟩ := periodic_real_bound (neutralJitterReal_smooth cut L 0).continuous
    (neutralJitterReal_periodic cut L 0)
  have hbudget := anchor_coefficient_budget (d := d) (D := D-margin) hq a hω R
  refine ⟨g,rfl,δ,cut,L,hδ,hδκ,hL,rfl,S,?_⟩
  filter_upwards [hgood,hbudget] with n hn hnω
  obtain ⟨hnp,haul,G,hGi,hGmod,hGV,hGm,hGA,_hGden,hgroup,hreflect⟩ := hn
  have hloc (i : PassageOutputIndex (S n)) :
      d ((G.m i:ℝ)/n) = a i.1-q (((G.m i:ℝ)/(n:ℝ)):UnitAddCircle) ∧
      b+margin ≤ |(G.m i:ℝ)/n| ∧ |(G.m i:ℝ)/n| ≤ D-margin := by
    obtain ⟨x,hx,hx'⟩ := (hχ i.1).2.2.2.2 _
      (subset_tsupport _ ((hS n hnp i.1 _).mp i.2.property))
    rw [hGm]
    exact hroom i.1 x hx _ hx'
  refine ⟨hnp,G,hGi,hGmod,hGV,hGm,?_,fun i => (hloc i).2,?_,hreflect⟩
  · intro i
    have hv := outputVector_eq_retained F G (neutralCircleCutoff cut) (fun i s _ => χ i s)
      H n hGm hGA i
    have hp : exactRetainedPacketDensity (Ioo δ (1-δ)) (neutralJitterReal cut L 0)
        (neutralCircleCutoff cut) (fun s _ => χ i s) (F.m i) H (F.A i) (S n i) n =
        outputDensity G i := by
      have hh := hgroup i (fun _ => True)
      change _ = fun z => ∑ j : ↥(S n i), G.density ⟨i,j⟩ z
      simpa only [Finset.filter_true,ite_true] using hh
    have hh := haul i
    dsimp only at hh
    rw [← hv,hp] at hh
    exact ⟨hh.1,hh.2.1⟩
  · intro i y
    rw [hGV]
    exact hnω.2 (G.m i) i.1 (neutralJitterReal cut L 0 y) (hloc i).2.2 (hRJ y) (hloc i).1

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_ControlledBlocks
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical signal and derivative control through actual repeated blocks, cyclic prediction, and tag selection. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- The carrier precedes the block signal and every block accuracy requirement.
The output retains the literal actual geometry and finite amplitudes. -/
theorem eventually_colored_controlled_anchor_oai {m : ℕ} (C : ColoredState (Fin m))
    {τR : Fin m → Fin m} (hrC : C.Reflection τR) :
    ∀ᶠ c : ℕ in atTop,
      ∀ (d : ℝ → ℂ) (q : UnitAddCircle → ℂ) (tags : Fin m → ℂ), Continuous q →
      ∀ b D margin τ : ℝ, 0 < τ →
      (∀ i x, x ∈ C.packets.core i → ∀ s,
        |s-(C.packets.m i:ℝ)*((c:ℝ)+C.packets.V x)| < τ →
        d s = tags (C.color i)-q (s:UnitAddCircle) ∧ b+margin ≤ |s| ∧ |s| ≤ D-margin) →
      ∀ (Q : PhysicalJetData) (F : PhysicalFrame) (ζ : ℝ), 0 < ζ →
      ∀ ε e ω κ : ℝ, 0 < ε → 0 < e → 0 < ω → 0 < κ →
      ∀ᶠ n : ℕ in atTop, ∃ s : ColoredAnchor C n,
        Q.Close ζ F C.packets.V (s.nextFrame F) s.final.V ∧
        s.geometry.c = c ∧
        (∃ δ : ℝ, ∃ cut : LawCutoffs δ, ∃ K : ℝ,
          0 < δ ∧ δ < κ ∧ 0 < K ∧ s.geometry.J₀ = neutralJitterReal cut K 0) ∧
        (∀ r, physicalError (C.vector r) (s.output.vector r ∘ s.chart) < ε) ∧
        colorL1Distance C.density s.output.density < e ∧
        s.output.InBand b D margin ∧
        s.output.Matches d (fun r z => tags r-q z) ω ∧
        s.output.Reflection τR ∧
        ∃ δ : ℝ, 0 < δ ∧ δ < κ ∧ s.final.GoodArc δ := by
  classical
  obtain ⟨τref,hr,hτref⟩ := hrC
  filter_upwards [eventually_reflected_anchor_state C.packets C.injective C.spare hr] with c hc
  intro d q tags hq b D margin τ hτ hroom Q F ζ hζ ε e ω κ hε he hω hκ
  let K : ℝ := Fintype.card C.Index
  have hK : 0 ≤ K := Nat.cast_nonneg _
  let e' : ℝ := min (ε/(K^2+1)) (e/((m:ℝ)*K+1))
  have he' : 0 < e' := lt_min (div_pos hε (by positivity)) (div_pos he (by positivity))
  have hphysicalBudget : K^2*e' < ε := by
    have he1 : e' ≤ ε/(K^2+1) := min_le_left _ _
    have hp := (le_div_iff₀ (show 0 < K^2+1 by positivity)).1 he1
    nlinarith
  have hdensityBudget : (m:ℝ)*K*e' < e := by
    have he1 : e' ≤ e/((m:ℝ)*K+1) := min_le_right _ _
    have hp := (le_div_iff₀ (show 0 < (m:ℝ)*K+1 by positivity)).1 he1
    nlinarith
  obtain ⟨g,hgc,δ,cut,L,hδ,hδκ,hL,hgJ,S,hready⟩ := hc d q (tags ∘ C.color) hq
    b D margin τ hτ hroom e' ω κ he' hω hκ
  obtain ⟨n₀,hn₀⟩ := hready.exists
  obtain ⟨hn₀p,G₀,_hG₀i,_hG₀mod,hG₀V,_hG₀m,_tail⟩ := hn₀
  have hgJs := g.smooth_jitter_of_output G₀ hn₀p hG₀V
  filter_upwards [hready,Q.eventually_next F g C.packets.smooth_speed hgJs hζ] with n hn hjet
  obtain ⟨hnp,G,hGi,hGmod,hGV,hGm,herror,hband,hmatch,τG,hτG,hrG,hgoodG⟩ := hn
  let s : ColoredAnchor C n := ⟨g,S n,hnp,G,hGi,hGmod,hGV,hGm⟩
  refine ⟨s,?_,hgc,⟨δ,cut,L,hδ,hδκ,hL,hgJ⟩,?_,?_,hband,?_,⟨τG,hrG,?_⟩,⟨δ,hδ,hδκ,hgoodG⟩⟩
  · change Q.Close ζ F C.packets.V (F.next g C.packets.smooth_speed n) G.V
    rw [hGV]
    exact hjet
  · intro r
    have hh := colored_physical_bound
      (fun i => continuous_packet (C.packets.continuous_amplitude i))
      (fun i => (continuous_outputVector G i).comp (continuous_passageChart (g.Hcontinuous n)))
      C.color r he'.le (fun i => (herror i).1.le) hphysicalBudget
    change physicalError (C.vector r) _ < ε at hh
    have heq : (s.output.vector r ∘ s.chart) =
        (fun x => ∑ i, if C.color i = r then outputVector G i (passageChart (g.H n) x) else 0) := by
      funext x
      exact colorVector_output G C.color r _
    rw [heq]
    exact hh
  · have hcolor r : (∫ z, |C.density r z-s.output.density r z| ∂phaseHaar) ≤ K*e' := by
      have hh := colored_density_bound
        (fun i => continuous_outputDensity G i) C.packets.density_continuous C.color r
        (fun _ => 0) (γ := 0) (ω := 0) he'.le (fun i => by simpa using (herror i).2.le)
      simp only [zero_mul,zero_add] at hh
      have heq : (fun z => ∑ i, if C.color i = r then outputDensity G i z else 0) =
          s.output.density r := by
        funext z
        exact (colorDensity_output G C.color r z).symm
      change (∫ z, |(fun z => ∑ i, if C.color i = r then outputDensity G i z else 0) z-
        C.density r z| ∂phaseHaar) ≤ K*e' at hh
      rw [heq] at hh
      simpa only [abs_sub_comm] using hh
    apply (Finset.sum_le_sum (s := Finset.univ) (fun r _ => hcolor r)).trans_lt
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using hdensityBudget
  · intro i y _hy
    exact (hmatch i y).le
  · intro i
    change C.color ((τG i).1) = τR (C.color i.1)
    exact (congrArg C.color (hτG i)).trans (hτref i.1)

end ThreeTorus
end
end

end OAI
end

theorem solution : type_of% @OAI.ThreeTorus.eventually_colored_controlled_anchor_oai := @OAI.ThreeTorus.eventually_colored_controlled_anchor_oai
