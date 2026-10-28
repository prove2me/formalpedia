-- Prove2me | solution 1 for OAI.ThreeTorus.exists_two_slow_insertions
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T12:16:36.996157+00:00
-- url     : https://prove2.me/submissions/239dc8fe-59dc-4b5e-8a29-62aeacbe8dd7

import Mathlib
import Definitions.Def_ThreeTorus
import Definitions.Def_OAIQ13Tt000
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

lemma lawPsi_smooth {δ : ℝ} (c : LawCutoffs δ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lawPsi c) :=
  contDiff_periodize c.ψ_smooth c.ψ_compact

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

lemma support_branchFamily_subset {Ω : Type*} [TopologicalSpace Ω]
    {I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ} :
    support (branchFamily I J F) ⊆ (fun p : ℝ × Ω => (J p.1,p.2)) '' tsupport F := by
  rintro ⟨s,a⟩ hh
  have hs : s ∈ J '' I := by
    by_contra hn
    exact hh (by simp [branchFamily,hn])
  have hp := invFunOn_pos hs
  refine ⟨(invFunOn J I s,a),subset_tsupport F ?_,?_⟩
  · intro hz
    exact hh (by simp [branchFamily,hs,hz])
  · simp only [hp.2]

lemma branchFamily_compact {Ω : Type*} [TopologicalSpace Ω] [T2Space Ω]
    {I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ}
    (hJ : Continuous J) (hc : HasCompactSupport F) : HasCompactSupport (branchFamily I J F) := by
  apply HasCompactSupport.intro (hc.image (by fun_prop : Continuous (fun p : ℝ × Ω => (J p.1,p.2))))
  intro p hp
  by_contra hn
  exact hp (support_branchFamily_subset hn)

lemma branchFamily_continuous {Ω : Type*} [TopologicalSpace Ω] [T2Space Ω]
    {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × Ω → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hF : Continuous F) (hc : HasCompactSupport F) (hs : tsupport F ⊆ I ×ˢ univ) :
    Continuous (branchFamily I J F) := by
  classical
  let g := invFunOn J I
  let M := (fun p : ℝ × Ω => (J p.1,p.2)) '' tsupport F
  have hM : IsCompact M := hc.image (by fun_prop)
  have hzero {p : ℝ × Ω} (hp : p ∉ M) : branchFamily I J F p = 0 :=
    notMem_support.mp (fun hn => hp (support_branchFamily_subset hn))
  have hD : Continuous (deriv J) := hJ.continuous_deriv (by simp)
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p ∈ M
  · rcases hp with ⟨⟨x,a⟩,hx,rfl⟩
    have hxI : x ∈ I := (hs hx).1
    have hy : J x ∈ J '' I := mem_image_of_mem J hxI
    have hgi := (contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hxI
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hxI)).continuousAt
    have hge : g (J x) = x := by
      exact hinj (invFunOn_pos hy).1 hxI (invFunOn_pos hy).2
    have hgi' : ContinuousAt (fun p : ℝ × Ω => g p.1) (J x,a) :=
      hgi.comp_of_eq continuousAt_fst rfl
    have hin : ContinuousAt (fun p : ℝ × Ω => (g p.1,p.2)) (J x,a) :=
      hgi'.prodMk continuousAt_snd
    have hDen : ContinuousAt (fun p : ℝ × Ω => |deriv J (g p.1)|) (J x,a) :=
      (hD.continuousAt.comp hgi').abs
    have hquot : ContinuousAt (fun p : ℝ × Ω => F (g p.1,p.2) / |deriv J (g p.1)|) (J x,a) := by
      apply (hF.continuousAt.comp hin).div hDen
      simpa only [hge] using abs_ne_zero.mpr (hd x hxI)
    apply hquot.congr_of_eventuallyEq
    have hnear : ∀ᶠ p : ℝ × Ω in 𝓝 (J x,a), p.1 ∈ J '' I :=
      continuous_fst.continuousAt.eventually ((isOpen_image_of_deriv_ne_zero hJ hIo hd).mem_nhds hy)
    filter_upwards [hnear] with p hp
    simp only [branchFamily,ite_eq_left hp,g]
  · apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hM.isClosed.isOpen_compl.mem_nhds hp] with q hq
    exact hzero hq

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

lemma stationaryWeight_signed_compact_continuous {J : ℝ → ℝ}
    {A : UnitAddCircle → ℝ → ℂ} {l u R : ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hA : Continuous A.uncurry) (hs : ∀ a, support (A a) ⊆ Icc l u)
    (hR : 0 < R) (hi : InjOn J (Icc (l-R) (u+R)))
    (hd : ∀ x ∈ Ioo (l-R) (u+R), deriv J x ≠ 0) :
    Continuous (fun p : ℝ × UnitAddCircle => stationaryWeight (Icc (l-R) (u+R)) J (A p.2) p.1) ∧
    HasCompactSupport (fun p : ℝ × UnitAddCircle => stationaryWeight (Icc (l-R) (u+R)) J (A p.2) p.1) := by
  let F : ℝ × UnitAddCircle → ℝ := fun p => ‖A p.2 p.1‖^2
  have hF : Continuous F := (hA.comp (continuous_snd.prodMk continuous_fst)).norm.pow 2
  have hFs : support F ⊆ Icc l u ×ˢ (univ : Set UnitAddCircle) := by
    intro p hp
    refine ⟨hs p.2 ?_,mem_univ _⟩
    intro hz
    exact hp (by simp [F,show A p.2 p.1 = 0 from hz])
  have hFt : tsupport F ⊆ Icc l u ×ˢ (univ : Set UnitAddCircle) :=
    closure_minimal hFs (isClosed_Icc.prod isClosed_univ)
  have hc : HasCompactSupport F :=
    (isCompact_Icc.prod isCompact_univ).of_isClosed_subset (isClosed_tsupport F) hFt
  have hsub : Icc l u ⊆ Ioo (l-R) (u+R) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  rw [stationaryWeight_family_of_branch Ioo_subset_Icc_self hi (fun a => (hs a).trans hsub)]
  exact ⟨branchFamily_continuous hJ isOpen_Ioo (hi.mono Ioo_subset_Icc_self) hd hF hc
    (fun p hp => ⟨hsub (hFt hp).1,mem_univ _⟩),branchFamily_compact hJ.continuous hc⟩

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

/-! The two exact support separations in the passage and stage construction.
No spectral or asymptotic separation is substituted for actual disjoint sets. -/
noncomputable section
open Set Function
open scoped Topology
namespace ThreeTorus

/-- One integral shift separates the speed ranges for all distinct integer
angular indices in a finite list. It also keeps every range away from zero. -/
theorem exists_integral_speed_separation {ι X : Type*} [Finite ι]
    [TopologicalSpace X] [CompactSpace X] (m : ι → ℤ) (φ : X → ℝ)
    (hm : ∀ i, m i ≠ 0) (hφ : Continuous φ) :
    ∃ c : ℕ, 0 < c ∧
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
  obtain ⟨c,hc⟩ := exists_nat_gt (2*M*B+B+1)
  have hMB : 0 ≤ M*B := mul_nonneg hM hB
  have hcB : B < (c:ℝ) := by nlinarith
  have hcp : (0:ℝ) < c := hB.trans_lt hcB
  refine ⟨c,by exact_mod_cast hcp,?_,?_⟩
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

lemma map_fst_withDensity_marginal
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {q : X × Y → ℝ≥0∞} (hq : Measurable q) :
    ((μ.prod ν).withDensity q).map Prod.fst =
      μ.withDensity (fun x => ∫⁻ y, q (x,y) ∂ν) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs,withDensity_apply _ (measurable_fst hs),
    withDensity_apply _ hs,← lintegral_indicator (measurable_fst hs),
    ← lintegral_indicator hs,lintegral_prod _ (hq.indicator (measurable_fst hs)).aemeasurable]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx]
    apply lintegral_congr
    intro y
    exact Set.indicator_of_mem (show (x,y) ∈ Prod.fst ⁻¹' s from hx) q
  · simp only [Set.indicator_of_notMem hx]
    have hz (y : Y) : ((Prod.fst ⁻¹' s).indicator q) (x,y) = 0 :=
      Set.indicator_of_notMem (show (x,y) ∉ Prod.fst ⁻¹' s from hx) q
    simp only [hz,lintegral_zero]

lemma continuous_slowMarginal {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) :
    Continuous (fun u => ∫ a, ‖A (u,a)‖^2 ∂AddCircle.haarAddCircle) := by
  have hc : Continuous (uncurry (fun (u a : UnitAddCircle) => ‖A (u,a)‖^2)) := hA.norm.pow 2
  simpa only [setIntegral_univ] using
    continuous_parametric_integral_of_continuous (X := UnitAddCircle) (Y := UnitAddCircle)
      (μ := AddCircle.haarAddCircle) hc isCompact_univ

lemma packetSpectralMeasure_marginal {φ : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} {m : ℤ}
    (hφ : Measurable φ) (hA : Continuous A) :
    packetSpectralMeasure φ m A =
      (AddCircle.haarAddCircle.withDensity (fun u => ENNReal.ofReal
        (∫ a, ‖A (u,a)‖^2 ∂AddCircle.haarAddCircle))).map (fun u => m • φ u) := by
  unfold packetSpectralMeasure slowVolume
  change Measure.map ((fun u => m • φ u) ∘ Prod.fst) _ = _
  rw [← Measure.map_map (show Measurable (fun u => m • φ u) from hφ.const_smul m) measurable_fst,
    map_fst_withDensity_marginal (q := fun p => ENNReal.ofReal (‖A p‖^2))
      (by simpa only [Pi.pow_apply] using (hA.norm.pow 2).measurable.ennreal_ofReal)]
  congr 2
  funext u
  exact (ofReal_integral_eq_lintegral_ofReal
    (((hA.comp (continuous_const.prodMk continuous_id)).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (ae_of_all _ (fun a => sq_nonneg _))).symm

lemma branchDensity_integral {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (I : Set ℝ) (J g D : ℝ → ℝ) (q : ℝ × Ω → ℝ) (s : ℝ) :
    branchDensity I J g D (fun u => ∫ a, q (u,a) ∂ν) s =
      ∫ a, branchDensity I J g D (fun u => q (u,a)) s ∂ν := by
  classical
  unfold branchDensity
  by_cases hs : s ∈ J '' I
  · simp only [Set.indicator_of_mem hs,integral_div]
  · simp only [Set.indicator_of_notMem hs,integral_zero]

/-- An arbitrary smooth/continuous old packet has the stationary marginal as
its temporal density. Spare-coordinate independence is not required. -/
theorem oldPacket_spectralDensity
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {v : UnitAddCircle → ℝ} {V : ℝ → ℝ} {m c : ℤ} {o : ℝ} {C I : Set ℝ}
    (hA : Continuous A) (hA₀ : Continuous A₀.uncurry)
    (hAe : ∀ a x, x ∈ Ioc o (o+1) → A ((x:UnitAddCircle),a) = A₀ a x)
    (has : ∀ a, support (A₀ a) ⊆ Ioc o (o+1)) (hAs : ∀ a, support (A₀ a) ⊆ I)
    (hv : Measurable v) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVe : ∀ x ∈ I, v (x:UnitAddCircle) = V x)
    (hIo : IsOpen I) (hIC : I ⊆ C) (hinj : InjOn (fun x => (m:ℝ)*V x) C)
    (hd : ∀ x ∈ I, deriv (fun x => (m:ℝ)*V x) x ≠ 0) :
    packetSpectralMeasure (fun a => ((v a-c:ℝ):UnitAddCircle)) m A =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal
        (foldCircleDensity (fun s => ∫ a, stationaryWeight C (fun x => (m:ℝ)*V x)
          (A₀ a) s ∂AddCircle.haarAddCircle) z)) := by
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
  have hmap := packetSpectralMeasure_marginal (m := m) (A := A)
    (φ := fun a => (((v a-(c:ℝ)) : ℝ):UnitAddCircle))
    (AddCircle.measurable_mk'.comp (hv.sub measurable_const)) hA
  rw [hmap]
  have hmode (a : UnitAddCircle) : m • ((v a-c:ℝ):UnitAddCircle) =
      (((m:ℝ)*v a:ℝ):UnitAddCircle) := by
    rw [← AddCircle.coe_zsmul]
    simp only [zsmul_eq_mul]
    rw [mul_sub]
    have he : ((m:ℝ)*(c:ℝ):UnitAddCircle) = 0 := by
      rw [← Int.cast_mul]
      exact (AddCircle.coe_eq_zero_iff 1).mpr ⟨m*c,by simp⟩
    rw [AddCircle.coe_sub,he,sub_zero]
  simp_rw [hmode]
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
  exact positive_circle_branch_fold
    (hqc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    hq₀c.measurable (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun x hx => integral_congr_ae (ae_of_all _ (fun a => by dsimp only; rw [hAe a x hx])))
    (hs _ has) (hs _ hAs) (hv.const_mul (m:ℝ)) (contDiff_const.mul hV)
    (fun x hx => by rw [hVe x hx]) hIo (hinj.mono hIC) hd

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

/-! The simultaneous neutral passage with an actual integer-rounded common
primitive. Its complete geometry and all spectral estimates are supplied by
one and the same sequence of smooth Haar-preserving maps. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

/-- The jitter, all packet lists and all cutoffs are fixed before the final
passage integer. No primitive, convergence, or spectral data are assumed. -/
theorem exists_simultaneous_neutral_passage {ι : Type*} [Fintype ι]
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
      (A₀ i a) s ≠ 0 → χ i s a = 1) :
    ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      (∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹) ∧ Tendsto Δ atTop (𝓝 0) ∧
      (∀ n, Continuous (H n)) ∧
      (∀ n (x : ℝ), H n (x:UnitAddCircle) =
        ((n:ℝ)*((∫ t in 0..x, V t)+Δ n*x):UnitAddCircle)) ∧
      ∃ C : ι → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ L : ℝ, 0 < L → ∀ β : ℝ,
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
              ‖retainedAmplitude ψ (χ i) (m i) H (A i) n j (u,0)‖) := by
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
  refine ⟨Δ,H,hΔ,hΔt,hHc,hHe,C,hC,?_⟩
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
  filter_upwards [eventually_gt_atTop (0:ℕ),hgall] with n hn hall
  refine ⟨hn,fun i => ?_⟩
  have ef := retainedPassage_eq_of_cover (m i) (H n) (A i) (S i n) (T n i)
    (fun j => χ i ((j:ℝ)/n)) (neutralCircleCutoff c) (hST i n hn) (hTZ n hn i)
  have ep := exactRetainedPacketDensity_eq_of_cover (Ioo δ (1-δ))
    (neutralJitterReal c L β) (neutralCircleCutoff c) (χ i) (m i) H (A i)
    (S i n) (T n i) n (hST i n hn) (hTZ n hn i)
  simpa only [ef,ep] using hall i

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

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PacketStates
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

lemma amplitude_bound [Finite ι] : ∃ B : ℝ, 0 ≤ B ∧ ∀ i p, ‖F.A i p‖^2 ≤ B := by
  classical
  have hb i := (isCompact_range ((F.continuous_amplitude i).norm.pow 2)).isBounded.exists_norm_le
  choose B hB using hb
  obtain ⟨C,hC⟩ := (Set.finite_range B).isCompact.isBounded.exists_norm_le
  refine ⟨max C 0,le_max_right _ _,fun i p => ?_⟩
  have h₁ := hB i _ (mem_range_self p)
  have h₂ := hC _ (mem_range_self i)
  exact (le_abs_self _).trans (h₁.trans ((le_abs_self _).trans (h₂.trans (le_max_left _ _))))

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

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

lemma marginalWeight_regular (i : ι) : Continuous (F.marginalWeight i) ∧
    HasCompactSupport (F.marginalWeight i) := by
  let w : ℝ × UnitAddCircle → ℝ := fun p => stationaryWeight (Icc (F.l-F.R) (F.u+F.R))
    (fun x => (F.m i:ℝ)*F.V x) (F.A₀ i p.2) p.1
  have hb := scaled_speed_good_branch (F.nonzero i) F.Rpos F.smooth_speed F.positive_deriv
  have hw := stationaryWeight_signed_compact_continuous (contDiff_const.mul F.smooth_speed)
    (F.continuous_lift i) (fun a => (F.support_lift i a).trans Ioc_subset_Icc_self) F.Rpos hb.1 hb.2
  have hc : Continuous (F.marginalWeight i) := by
    have hh : Continuous (uncurry (fun (s : ℝ) (a : UnitAddCircle) => w (s,a))) := hw.1
    change Continuous (fun s => ∫ a, w (s,a) ∂AddCircle.haarAddCircle)
    simpa only [setIntegral_univ] using
      continuous_parametric_integral_of_continuous (X := ℝ) (Y := UnitAddCircle)
        (μ := AddCircle.haarAddCircle) hh isCompact_univ
  refine ⟨hc, (hw.2.image continuous_fst).of_isClosed_subset (isClosed_tsupport _) ?_⟩
  apply closure_minimal ?_ (hw.2.image continuous_fst).isClosed
  intro s hs
  by_contra hn
  have hz (a : UnitAddCircle) : w (s,a) = 0 := by
    by_contra hh
    exact hn ⟨(s,a),subset_tsupport w hh,rfl⟩
  apply hs
  simp only [marginalWeight,show ∀ a, stationaryWeight (Icc (F.l-F.R) (F.u+F.R))
    (fun x => (F.m i:ℝ)*F.V x) (F.A₀ i a) s = 0 from hz,integral_zero]

lemma marginalDensity_nonneg (i : ι) (z : UnitAddCircle) : 0 ≤ F.marginalDensity i z :=
  foldCircleDensity_nonneg (fun s => integral_nonneg (fun _a => branchDensity_nonneg
    (fun _ => sq_nonneg _) s)) z

lemma marginalDensity_measurable (i : ι) : Measurable (F.marginalDensity i) :=
  measurable_foldCircleDensity (F.marginalWeight_regular i).1.measurable

lemma marginalDensity_integrable (i : ι) : Integrable (F.marginalDensity i) AddCircle.haarAddCircle :=
  integrable_foldCircleDensity (F.marginalWeight_regular i).1.measurable
    ((F.marginalWeight_regular i).1.integrable_of_hasCompactSupport (F.marginalWeight_regular i).2)

/-- The actual old packet spectrum, without spare independence. -/
theorem marginalDensity_spectral (i : ι) :
    packetSpectralMeasure (fun u => (F.periodic.lift u:UnitAddCircle)) (F.m i) (F.A i) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (F.marginalDensity i z)) := by
  have hb := scaled_speed_good_branch (F.nonzero i) F.Rpos F.smooth_speed F.positive_deriv
  have hs a : support (F.A₀ i a) ⊆ Ioo (F.l-F.R) (F.u+F.R) := by
    intro x hx
    have hh := F.support_lift i a hx
    constructor <;> linarith [F.Rpos,hh.1,hh.2]
  have he := oldPacket_spectralDensity (m := F.m i) (c := 0) (v := F.periodic.lift)
    (F.continuous_amplitude i) (F.continuous_lift i) (F.lift_matches i)
    (fun a => (F.support_lift i a).trans (by
      intro x hx; exact ⟨lt_of_le_of_lt F.lo hx.1,hx.2.trans F.uo⟩)) hs
    F.speed_continuous.measurable F.smooth_speed (fun _ _ => rfl) isOpen_Ioo Ioo_subset_Icc_self hb.1 hb.2
  change _ = AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal
    (foldCircleDensity (fun s => ∫ a, stationaryWeight (Icc (F.l-F.R) (F.u+F.R))
      (fun x => (F.m i:ℝ)*F.V x) (F.A₀ i a) s ∂AddCircle.haarAddCircle) z))
  simpa only [Int.cast_zero,sub_zero] using he

lemma marginalDensity_carrier (c : ℤ) (i : ι) :
    (F.carrier c).marginalDensity i =ᵐ[AddCircle.haarAddCircle] F.marginalDensity i := by
  have he : AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal ((F.carrier c).marginalDensity i z)) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (F.marginalDensity i z)) := by
    rw [← (F.carrier c).marginalDensity_spectral i,← F.marginalDensity_spectral i]
    congr 1
    funext z
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective z
    exact F.carrier_circle c x
  have h := (withDensity_eq_iff_of_sigmaFinite
    ((F.carrier c).marginalDensity_measurable i).ennreal_ofReal.aemeasurable
    (F.marginalDensity_measurable i).ennreal_ofReal.aemeasurable).mp he
  filter_upwards [h] with z hz
  have hh := congrArg ENNReal.toReal hz
  simpa only [ENNReal.toReal_ofReal ((F.carrier c).marginalDensity_nonneg i z),
    ENNReal.toReal_ofReal (F.marginalDensity_nonneg i z)] using hh

lemma marginalDensity_eq (hmod : F.SpareIndependent) (i : ι) :
    F.marginalDensity i = F.density i := F.density_marginal hmod i

end PassagePackets
end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PhysicalJets
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

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PacketAlgebra
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite packet algebra and physical L2 metric estimates. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace PassagePackets

variable {ι κ : Type*}

lemma reindex_reflection (F : PassagePackets ι) {r : κ → ι}
    {τ : ι → ι} {σ : κ → κ} (h : F.Reflection τ) (he : ∀ i, r (σ i)=τ (r i)) :
    (F.reindex r).Reflection σ := by
  constructor
  · intro i; change F.m (r (σ i)) = -F.m (r i); rw [he,h.index]
  · intro i p; change F.A (r (σ i)) p = conj (F.A (r i) p); rw [he,h.amplitude]
  · intro i a x; change F.A₀ (r (σ i)) a x = conj (F.A₀ (r i) a x); rw [he,h.lift]

lemma append_good (F : PassagePackets ι) (G : PassagePackets κ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hF : F.GoodArc δ) (hG : G.GoodArc δ) (hV : G.V=F.V) :
    (F.append G hδ hF hG hV).GoodArc δ :=
  ⟨rfl,lt_min hF.2.1 hG.2.1,max_lt hF.2.2.1 hG.2.2.1,hF.2.2.2⟩

end PassagePackets
end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma physicalDist_lt_iff (f g : TripleTorus → ℂ) {ε : ℝ} (hε : 0 < ε) :
    physicalDist f g < ε ↔ physicalError f g < ε^2 := Real.sqrt_lt' hε
lemma norm_toLp_sq {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 ν) : ‖hf.toLp f‖^2=∫ x, ‖f x‖^2 ∂ν := by
  calc
    _ = inner ℝ (hf.toLp f) (hf.toLp f) := (real_inner_self_eq_norm_sq _).symm
    _ = ∫ x, inner ℝ (hf.toLp f x) (hf.toLp f x) ∂ν := L2.inner_def _ _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx,real_inner_self_eq_norm_sq]
lemma physicalError_eq_norm {f g : TripleTorus → ℂ}
    (hf : MemLp f 2 tripleVolume) (hg : MemLp g 2 tripleVolume) :
    physicalError f g=‖hf.toLp f-hg.toLp g‖^2 := by
  rw [← hf.toLp_sub hg,norm_toLp_sq]
  rfl
lemma physicalDist_eq_norm {f g : TripleTorus → ℂ}
    (hf : MemLp f 2 tripleVolume) (hg : MemLp g 2 tripleVolume) :
    physicalDist f g=‖hf.toLp f-hg.toLp g‖ := by
  rw [physicalDist,physicalError_eq_norm hf hg,Real.sqrt_sq (norm_nonneg _)]
lemma physicalDist_triangle {f g h : TripleTorus → ℂ}
    (hf : MemLp f 2 tripleVolume) (hg : MemLp g 2 tripleVolume) (hh : MemLp h 2 tripleVolume) :
    physicalDist f h ≤ physicalDist f g+physicalDist g h := by
  rw [physicalDist_eq_norm hf hh,physicalDist_eq_norm hf hg,physicalDist_eq_norm hg hh]
  simpa only [dist_eq_norm] using dist_triangle (hf.toLp f) (hg.toLp g) (hh.toLp h)
lemma physicalDist_finsum {ι : Type*} [Fintype ι] {f g : ι → TripleTorus → ℂ}
    (hf : ∀ i, MemLp (f i) 2 tripleVolume) (hg : ∀ i, MemLp (g i) 2 tripleVolume) :
    physicalDist (fun x => ∑ i, f i x) (fun x => ∑ i, g i x) ≤ ∑ i, physicalDist (f i) (g i) := by
  classical
  have hsum (a : ι → TripleTorus → ℂ) (ha : ∀ i, MemLp (a i) 2 tripleVolume) :
      (memLp_finsetSum Finset.univ (fun i _ => ha i)).toLp (fun x => ∑ i, a i x) =
        ∑ i, (ha i).toLp (a i) := by
    apply Lp.ext
    filter_upwards [(memLp_finsetSum Finset.univ (fun i _ => ha i)).coeFn_toLp,
      Lp.coeFn_fun_finsetSum Finset.univ (fun i => (ha i).toLp (a i)),
      ae_all_iff.mpr (fun i => (ha i).coeFn_toLp)] with x hx hy hz
    rw [hx,hy]
    exact Finset.sum_congr rfl (fun i _ => (hz i).symm)
  rw [physicalDist_eq_norm (memLp_finsetSum Finset.univ (fun i _ => hf i))
    (memLp_finsetSum Finset.univ (fun i _ => hg i)),hsum f hf,hsum g hg,← Finset.sum_sub_distrib]
  simp_rw [physicalDist_eq_norm (hf _) (hg _)]
  exact norm_sum_le Finset.univ (fun i => (hf i).toLp (f i)-(hg i).toLp (g i))

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

lemma Close.trans {Q : PhysicalJetData} {ε η : ℝ} {F G H : PhysicalFrame}
    {V W U : ℝ → ℝ} (h : Q.Close ε F V G W) (h' : Q.Close η G W H U) :
    Q.Close (ε+η) F V H U := by
  intro i x hx
  exact (dist_triangle _ _ _).trans (by linarith [h i x hx,h' i x hx])

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

section

/-! Unconditional neutral passage for general spare-dependent amplitudes and
possibly repeated old modes. Cutoffs and old families are fixed before all
jitter and passage-integer selections. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- Generic actual neutral output. It intentionally does not assert
injectivity of the new modes: the first support separation does not give it. -/
theorem exists_general_neutral {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) {c : ℕ} (hc : 0 < c)
    (h0 : ∀ x : ℝ, (c:ℝ)+F.V x ≠ 0)
    (χ : ι → ℝ → UnitAddCircle → ℝ)
    (hχs : ∀ i, CylinderSmooth (χ i).uncurry)
    (hχc : ∀ i, HasCompactSupport (χ i).uncurry)
    (hχ0 : ∀ i a, χ i 0 a = 0)
    (hχb : ∀ i s a, 0 ≤ χ i s a ∧ χ i s a ≤ 1)
    (hχW : ∀ i (C : Set ℝ) a s, stationaryWeight C
      (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) (F.A₀ i a) s ≠ 0 → χ i s a = 1)
    {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ δ : ℝ, ∃ cut : LawCutoffs δ, ∃ L : ℝ, ∃ g : PassageGeometryFamily F.V,
      0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ 0 < L ∧ g.c = c ∧
      g.J = neutralJitter cut L 0 ∧ g.J₀ = neutralJitterReal cut L 0 ∧
      ∃ S : ℕ → ι → Finset ℤ,
        (∀ n, 0 < n → ∀ i j, j ∈ S n i ↔ ∃ a, χ i ((j:ℝ)/n) a ≠ 0) ∧
        ∀ᶠ n : ℕ in atTop, 0 < n ∧
          ∃ G : PassagePackets (PassageOutputIndex (S n)),
            G.SpareIndependent ∧ G.V = (fun x => (1+g.J₀ x/n)/n) ∧
            (∀ i, G.m i = i.2.val) ∧
            (∀ i, G.A i = retainedAmplitude (neutralCircleCutoff cut) (χ i.1)
              (F.m i.1) g.H (F.A i.1) n i.2.val) ∧
            (∀ i, G.A₀ i = retainedRealAmplitude cut.ψ (χ i.1) (F.m i.1) (g.H n)
              (F.A i.1) ((i.2.val:ℝ)/n) i.2.val) ∧
            G.GoodArc δ ∧
            ∀ i, (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-
              outputVector G i (passageChart (g.H n) x)‖^2 ∂tripleVolume) < ε ∧
              (∫ z, |outputDensity G i z-F.marginalDensity i z| ∂phaseHaar) < ε := by
  classical
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
  let Fc := F.carrier (c:ℤ)
  have hXc i : Continuous (χ i).uncurry := (hχs i).continuous
  have hXW i s a : stationaryWeight (Icc (Fc.l-Fc.R) (Fc.u+Fc.R))
      (fun x => (Fc.m i:ℝ)*Fc.V x) (Fc.A₀ i a) s ≠ 0 → χ i s a = 1 := by
    simpa only [Fc,PassagePackets.carrier,Int.cast_natCast] using
      hχW i (Icc (F.l-F.R) (F.u+F.R)) a s
  have hzero i : 0 ∉ (fun x => (Fc.m i:ℝ)*Fc.V x) '' Icc Fc.l Fc.u := by
    rintro ⟨x,_hx,he⟩
    have hh : (F.m i:ℝ)*((c:ℝ)+F.V x) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast F.nonzero i) (h0 x)
    exact hh (by simpa only [Fc,PassagePackets.carrier,Int.cast_natCast] using he)
  obtain ⟨Δ,H,hΔ,hΔt,hHc,hHe,C,_hC,hrest⟩ :=
    exists_simultaneous_neutral_passage Fc.nonzero Fc.lift_matches Fc.two Fc.continuous_lift
      Fc.continuous_deriv Fc.smooth_lift Fc.support_lift Fc.lo Fc.uo Fc.lu Fc.Rpos
      Fc.periodic Fc.smooth_speed Fc.positive_deriv hzero Fc.continuous_amplitude Fc.smooth_amplitude
      (B := fun _ => B) (fun _ => hB) hAB cut hδ hδ' hχs hXc hχc hχ0 hχb hXW
  have hsmall : 0 < ε/4 := by positivity
  have hCT i : ∀ᶠ L : ℝ in atTop, C i/L < ε/4 :=
    (tendsto_const_nhds.div_atTop tendsto_id).eventually (gt_mem_nhds hsmall)
  obtain ⟨L,hL,hCL⟩ := ((eventually_gt_atTop (0:ℝ)).and ((Filter.eventually_all).mpr hCT)).exists
  obtain ⟨hgeo,hgraph,hlimit,S,hSN,_hST,hTE,hgood⟩ := hrest L hL 0
  let g : PassageGeometryFamily F.V := {
    c := c, c_pos := hc, Δ := Δ, H := H,
    J := neutralJitter cut L 0, J₀ := neutralJitterReal cut L 0,
    Jmatch := fun _ => rfl, Jcontinuous := continuous_neutralJitter cut L 0,
    delta_bound := hΔ, delta_tendsto := hΔt, Hcontinuous := hHc,
    Hformula := by simpa only [Fc,PassagePackets.carrier,Int.cast_natCast] using hHe,
    geometry := hgeo,
    graph := by simpa only [Fc,PassagePackets.carrier,Int.cast_natCast] using hgraph,
    convergence := by simpa only [Fc,PassagePackets.carrier,Int.cast_natCast] using hlimit }
  refine ⟨δ,cut,L,g,hδ,hδ',hδκ,hL,rfl,rfl,rfl,S,hTE,?_⟩
  filter_upwards [hgood (ε/4) hsmall] with n hn
  have hn0 := hn.1
  let Hl (n : ℕ) (x : ℝ) := (n:ℝ)*((∫ t in 0..x, Fc.V t)+Δ n*x)
  have hHl n : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n) :=
    contDiff_const.mul ((contDiff_real_primitive Fc.smooth_speed).add (contDiff_const.mul contDiff_id))
  have hJs := neutralJitterReal_smooth cut L 0
  have hJd x (hx : x ∈ Ioo δ (1-δ)) : 0 < deriv (neutralJitterReal cut L 0) x := by
    rw [neutralJitterReal_deriv cut hδ L 0 hx]
    exact hL
  obtain ⟨G,hGm,hGA,hGA₀,hGV,hGo,hGl,hGu,hGmod⟩ := literal_output_packets
    F.m F.A H Hl χ (S n) (hSN n hn0) F.continuous_amplitude F.smooth_amplitude
    hχs hXc hHc hHl hHe cut hδ hδ' (neutralJitterReal_periodic cut L 0) hJs hJd hn0
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
        (χ i.1) (F.m i.1) H (F.A i.1) {i.2.val} n := by
    apply literal_packet_canonical_density G hGmod i (hGm i) (hGA i) ?_
      (continuous_neutralJitter cut L 0) hJs (fun _ _ => rfl) isOpen_Ioo hJinj
      (fun x hx => (hJd x hx).ne') (continuous_neutralCircleCutoff cut) cut.ψ_smooth cut.ψ_compact
      heψ hsψ (hXc i.1) (hχs i.1) hHc hHl hHe (F.continuous_amplitude i.1)
      (F.smooth_amplitude i.1) hn0
    intro a
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective a
    change (G.V x:UnitAddCircle) = _
    rw [hGV]
    rfl
  have hgroup i : exactRetainedPacketDensity (Ioo δ (1-δ)) (neutralJitterReal cut L 0)
      (neutralCircleCutoff cut) (χ i) (F.m i) H (F.A i) (S n i) n = outputDensity G i := by
    have hh := exactRetainedPacketDensity_filtered_singletons (m := F.m i) hJs isOpen_Ioo hJinj
      (fun x hx => (hJd x hx).ne') cut.ψ_smooth cut.ψ_compact heψ hsψ (hχs i)
      hHl hHe (F.smooth_amplitude i) hn0 (hSN n hn0 i) (fun _ => True)
    simp only [Finset.filter_true,ite_true] at hh
    rw [hh]
    unfold outputDensity
    simp_rw [hGden]
  refine ⟨hn0,G,hGmod,hGV,hGm,hGA,hGA₀,⟨hGo,hGl,hGu,?_⟩,?_⟩
  · intro x hx
    rw [hGV]
    exact positive_deriv_new_speed hn0 (hJd x hx)
  · intro i
    have hh := hn.2 i
    dsimp only at hh
    rw [show Fc.m = F.m from rfl,show Fc.A = F.A from rfl] at hh
    have hv := outputVector_eq_retained F G (neutralCircleCutoff cut) χ H n hGm hGA i
    have hde : (∫ z, |outputDensity G i z-Fc.marginalDensity i z| ∂phaseHaar) =
        ∫ z, |outputDensity G i z-F.marginalDensity i z| ∂phaseHaar := by
      apply integral_congr_ae
      filter_upwards [F.marginalDensity_carrier (c:ℤ) i] with z hz
      rw [hz]
    change _ ∧ (∫ z, |outputDensity G i z-F.marginalDensity i z| ∂phaseHaar) < ε
    rw [← hv] at hh
    refine ⟨hh.1.trans (by linarith),?_⟩
    have hds : (∫ z, |outputDensity G i z-Fc.marginalDensity i z| ∂phaseHaar) < C i/L+4*δ*B+ε/4 := by
      change (∫ z, |outputDensity G i z-foldCircleDensity (fun s => ∫ a,
        stationaryWeight (Icc (Fc.l-Fc.R) (Fc.u+Fc.R)) (fun x => (Fc.m i:ℝ)*Fc.V x)
          (Fc.A₀ i a) s ∂AddCircle.haarAddCircle) z| ∂phaseHaar) < _
      rw [← hgroup]
      exact hh.2.1
    rw [hde] at hds
    exact hds.trans (by linarith [hCL i])

end ThreeTorus
end
end

section

/-! Actual general neutral steps with arbitrary repeated indices, carrying the
literal coefficient formulas, physical charts and controlled cover jets. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace NeutralStep
variable {ι : Type*} {F : PassagePackets ι} (s : NeutralStep F)

lemma reflection {τ : ι → ι} (hr : F.Reflection τ) (hτ : Involutive τ)
    (hχ : ∀ i x a, s.χ (τ i) x a = s.χ i (-x) a) :
    ∃ τG : PassageOutputIndex s.S → PassageOutputIndex s.S,
      (∀ i, (τG i).1 = τ i.1) ∧ Involutive τG ∧ s.final.Reflection τG := by
  have hs (i : ι) (j : ℤ) : j ∈ s.S (τ i) ↔ -j ∈ s.S i := by
    rw [s.indices,s.indices]
    simp only [hχ,Int.cast_neg,neg_div]
  obtain ⟨τG,hparent,hrG⟩ := literal_output_reflection F hr (neutralCircleCutoff s.cut)
    s.cut.ψ s.χ s.geometry.H s.n s.S hs hχ s.final s.mode s.amplitude s.lift
  refine ⟨τG,hparent,?_,hrG⟩
  intro i
  have h₁ : (τG (τG i)).1 = i.1 := by rw [hparent,hparent,hτ]
  have h₂ : (τG (τG i)).2.val = i.2.val := by
    rw [← s.mode,hrG.index,hrG.index,neg_neg,s.mode]
  have hext (a b : PassageOutputIndex s.S) (hp : a.1 = b.1) (hm : a.2.val = b.2.val) : a = b := by
    rcases a with ⟨a,ja⟩
    rcases b with ⟨b,jb⟩
    dsimp only at hp hm
    subst b
    exact congrArg (Sigma.mk a) (Subtype.ext hm)
  exact hext _ _ h₁ h₂

end NeutralStep

/-- Finite physical restrictions are imposed only after the coefficients,
cutoffs, carrier, broad jitter and its rounding sequence have all been fixed. -/
theorem exists_controlled_neutral {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) {c : ℕ} (hc : 0 < c)
    (h0 : ∀ x : ℝ, (c:ℝ)+F.V x ≠ 0)
    (χ : ι → ℝ → UnitAddCircle → ℝ)
    (hχs : ∀ i, CylinderSmooth (χ i).uncurry)
    (hχc : ∀ i, HasCompactSupport (χ i).uncurry)
    (hχ0 : ∀ i a, χ i 0 a = 0)
    (hχb : ∀ i x a, 0 ≤ χ i x a ∧ χ i x a ≤ 1)
    (hχW : ∀ i (C : Set ℝ) a x, stationaryWeight C
      (fun t => (F.m i:ℝ)*((c:ℝ)+F.V t)) (F.A₀ i a) x ≠ 0 → χ i x a = 1)
    (Q : PhysicalJetData) (frame : PhysicalFrame)
    {ε κ ζ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∃ s : NeutralStep F, s.χ = χ ∧ s.geometry.c = c ∧ s.δ < κ ∧
      Q.Close ζ frame F.V (s.nextFrame frame) s.final.V ∧
      ∀ i, (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-
        outputVector s.final i (s.chart x)‖^2 ∂tripleVolume) < ε ∧
        (∫ z, |outputDensity s.final i z-F.marginalDensity i z| ∂phaseHaar) < ε := by
  classical
  obtain ⟨δ,cut,L,g,hδ,hδ',hδκ,hL,hgc,_hgJ,hgJ₀,S,hS,hgood⟩ :=
    exists_general_neutral F hc h0 χ hχs hχc hχ0 hχb hχW hε hκ
  have hJs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g.J₀ := by
    rw [hgJ₀]
    exact neutralJitterReal_smooth cut L 0
  obtain ⟨n,hn,hjet⟩ := (hgood.and (Q.eventually_next frame g F.smooth_speed hJs hζ)).exists
  obtain ⟨hnp,G,hGmod,hGV,hGm,hGA,hGA₀,hGgood,herr⟩ := hn
  let s : NeutralStep F := ⟨δ,cut,L,hδ,hδ',hL,g,hgJ₀,n,hnp,χ,S n,hS n hnp,
    G,hGmod,hGV,hGm,hGA,hGA₀,hGgood⟩
  refine ⟨s,rfl,hgc,hδκ,?_,herr⟩
  change Q.Close ζ frame F.V (frame.next g F.smooth_speed n) G.V
  rw [hGV]
  exact hjet

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- A repeated-mode neutral cutoff, independent of the spare coordinate.
Separation is in scalar frequency, not just on the cylinder. -/
theorem scalar_grouped_neutral_cutoffs {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) {τ : ι → ι} (hr : F.Reflection τ) :
    ∃ c : ℕ, 0 < c ∧ (∀ x : ℝ, (c:ℝ)+F.V x ≠ 0) ∧
      ∃ χ : ι → ℝ → ℝ,
        (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ i) ∧ HasCompactSupport (χ i) ∧
          χ i 0=0 ∧ (∀ s, 0 ≤ χ i s ∧ χ i s ≤ 1) ∧
          ∀ (C : Set ℝ) a s, stationaryWeight C
            (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) (F.A₀ i a) s ≠ 0 → χ i s=1) ∧
        (∀ i j, F.m i ≠ F.m j → Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
        (∀ i j, F.m i=F.m j → χ i=χ j) ∧
        ∀ i s, χ (τ i) s=χ i (-s) := by
  classical
  let m : Option ι → ℤ := fun i => i.elim 1 F.m
  have hm (i : Option ι) : m i ≠ 0 := by
    cases i with
    | none => norm_num [m]
    | some i => exact F.nonzero i
  obtain ⟨c,hc,hc0,hsep⟩ := exists_integral_speed_separation m F.periodic.lift hm F.speed_continuous
  let V : ℝ → ℝ := fun x => (c:ℝ)+F.V x
  have h0 (x : ℝ) : V x ≠ 0 := by simpa [m,V] using hc0 none (x:UnitAddCircle)
  have hV : Continuous V := continuous_const.add F.smooth_speed.continuous
  let M := ↥(range F.m)
  let : Finite M := (finite_range F.m).to_subtype
  let a (i : ι) : M := ⟨F.m i,mem_range_self i⟩
  let negM (k : M) : M := ⟨-k.val,by
    obtain ⟨i,hi⟩ := k.property
    exact ⟨τ i,by simp only [hr.index,hi]⟩⟩
  have hneg (i : ι) : a (τ i)=negM (a i) := Subtype.ext (hr.index i)
  have hnn (k : M) : negM (negM k)=k := Subtype.ext (neg_neg _)
  let E (k : M) := (fun x => (k.val:ℝ)*V x) '' Icc F.l F.u
  have hEc k : IsCompact (E k) := isCompact_Icc.image (continuous_const.mul hV)
  have hEd : Pairwise (Disjoint on E) := by
    intro k l hkl
    obtain ⟨i,hi⟩ := k.property
    obtain ⟨j,hj⟩ := l.property
    apply Set.disjoint_left.mpr
    rintro s ⟨x,_hx,hx⟩ ⟨y,_hy,hy⟩
    have he : (F.m i:ℝ)*((c:ℝ)+F.V x)=(F.m j:ℝ)*((c:ℝ)+F.V y) := by
      rw [hi,hj]; exact hx.trans hy.symm
    exact hkl (Subtype.ext (hi.symm.trans ((hsep (some i) (some j) (x:UnitAddCircle) (y:UnitAddCircle) he).trans hj)))
  have hEU k : E k ⊆ ({0}:Set ℝ)ᶜ := by
    rintro s ⟨x,_hx,rfl⟩ hs
    obtain ⟨i,hi⟩ := k.property
    exact mul_ne_zero (by rw [← hi]; exact_mod_cast F.nonzero i) (h0 x) hs
  obtain ⟨ξ,hξ,hξd⟩ := finite_disjoint_frequency_cutoffs E (fun _ => ({0}:Set ℝ)ᶜ)
    hEc (fun _ => isOpen_compl_singleton) hEU hEd
  let χ : ι → ℝ → ℝ := fun i s => ξ (a i) s*ξ (negM (a i)) (-s)
  have hsub i : tsupport (χ i) ⊆ tsupport (ξ (a i)) := tsupport_mul_subset_left
  have hre (k : M) {s : ℝ} (hs : s ∈ E k) : -s ∈ E (negM k) := by
    obtain ⟨x,hx,rfl⟩ := hs
    exact ⟨x,hx,by simp only [negM,Int.cast_neg,neg_mul]⟩
  refine ⟨c,hc,h0,χ,fun i => ⟨?_,?_,?_,?_,?_⟩,?_,?_,?_⟩
  · exact (hξ (a i)).1.mul ((hξ (negM (a i))).1.comp contDiff_id.neg)
  · exact (hξ (a i)).2.1.mul_right
  · by_contra hn
    exact (hξ (a i)).2.2.1 (hsub i (subset_tsupport (χ i) hn)) rfl
  · intro s
    exact ⟨mul_nonneg ((hξ (a i)).2.2.2.1 s).1 ((hξ (negM (a i))).2.2.2.1 (-s)).1,
      (mul_le_mul ((hξ (a i)).2.2.2.1 s).2 ((hξ (negM (a i))).2.2.2.1 (-s)).2
        ((hξ (negM (a i))).2.2.2.1 (-s)).1 zero_le_one).trans (by norm_num)⟩
  · intro C z s hs
    have he : s ∈ E (a i) := stationaryWeight_support_subset
      ((F.support_lift i z).trans Ioc_subset_Icc_self) hs
    have h1 := ((hξ (a i)).2.2.2.2 s he).self_of_nhds
    have h2 := ((hξ (negM (a i))).2.2.2.2 (-s) (hre _ he)).self_of_nhds
    change ξ (a i) s=1 at h1
    change ξ (negM (a i)) (-s)=1 at h2
    simp only [χ,h1,h2,one_mul]
  · intro i j hij
    exact (hξd (fun h => hij (congrArg Subtype.val h))).mono (hsub i) (hsub j)
  · intro i j hij
    have he : a i=a j := Subtype.ext hij
    simp only [χ,he]
  · intro i s
    simp only [χ,hneg,hnn,neg_neg,mul_comm]

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_FlatPackets
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Flat support, finite packet L2 estimates, neutral selection, density invariance, and finite spectral whitening. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

lemma physicalDist_add_le {f g h j : TripleTorus → ℂ}
    (hf : MemLp f 2 tripleVolume) (hg : MemLp g 2 tripleVolume)
    (hh : MemLp h 2 tripleVolume) (hj : MemLp j 2 tripleVolume) :
    physicalDist (fun x => f x+h x) (fun x => g x+j x) ≤ physicalDist f g+physicalDist h j := by
  change physicalDist (f+h) (g+j) ≤ _
  rw [physicalDist_eq_norm (hf.add hh) (hg.add hj),hf.toLp_add hh,hg.toLp_add hj]
  rw [show hf.toLp f+hh.toLp h-(hg.toLp g+hj.toLp j) =
    (hf.toLp f-hg.toLp g)+(hh.toLp h-hj.toLp j) by abel]
  simpa only [physicalDist_eq_norm hf hg,physicalDist_eq_norm hh hj] using
    norm_add_le (hf.toLp f-hg.toLp g) (hh.toLp h-hj.toLp j)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
namespace NeutralStep
variable {ι κ : Type*} {F : PassagePackets ι} (s : NeutralStep F)

lemma reindex_final_injective (r : κ → ι)
    (hd : Pairwise (fun i j : κ => Disjoint (s.S (r i)) (s.S (r j)))) :
    Injective (s.reindex r).final.m := by
  intro i j hij
  apply output_index_injective hd
  simpa only [(s.reindex r).mode] using hij

/-- Exact vector regrouping of the retained coefficients over their old roots. -/
lemma finitePacketVector_output [Fintype ι] :
    finitePacketVector s.final.m s.final.A = fun x => ∑ i, outputVector s.final i x := by
  funext x
  simp only [finitePacketVector,outputVector,Fintype.sum_sigma]

lemma physicalDist_total [Fintype ι] {ε : ℝ} (hε : 0 < ε)
    (he : ∀ i, physicalError (packet (F.m i) (F.A i))
      (outputVector s.final i ∘ s.chart) < (ε/(Fintype.card ι+1))^2) :
    physicalDist (finitePacketVector F.m F.A)
      (finitePacketVector s.final.m s.final.A ∘ s.chart) < ε := by
  have hFc i : MemLp (packet (F.m i) (F.A i)) 2 tripleVolume :=
    (continuous_packet (F.continuous_amplitude i)).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hGc i : MemLp (outputVector s.final i ∘ s.chart) 2 tripleVolume :=
    ((continuous_outputVector s.final i).comp (continuous_passageChart (s.geometry.Hcontinuous s.n))).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hc : (0:ℝ) < Fintype.card ι+1 := by positivity
  have he' i : physicalDist (packet (F.m i) (F.A i)) (outputVector s.final i ∘ s.chart) <
      ε/(Fintype.card ι+1) := (physicalDist_lt_iff _ _ (div_pos hε hc)).2 (he i)
  rw [s.finitePacketVector_output]
  calc
    _ ≤ ∑ i, physicalDist (packet (F.m i) (F.A i)) (outputVector s.final i ∘ s.chart) :=
      physicalDist_finsum hFc hGc
    _ ≤ ∑ _i : ι, ε/(Fintype.card ι+1) := Finset.sum_le_sum (fun i _ => (he' i).le)
    _ < ε := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← mul_div_assoc]
      apply (div_lt_iff₀ hc).2
      nlinarith

end NeutralStep
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- A simultaneous neutral passage with repeated modes. Distinct old modes
have disjoint scalar retained sets, and equal modes share the same cutoff. -/
theorem exists_grouped_neutral {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) (τ : ι → ι) (hτ : Involutive τ) (hr : F.Reflection τ)
    (Q : PhysicalJetData) (frame : PhysicalFrame)
    {ε κ ζ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∃ s : NeutralStep F, s.δ < κ ∧
      Q.Close ζ frame F.V (s.nextFrame frame) s.final.V ∧
      (∀ i j, F.m i ≠ F.m j → Disjoint (s.S i) (s.S j)) ∧
      (∀ i x a, s.χ (τ i) x a=s.χ i (-x) a) ∧
      (∃ σ, Involutive σ ∧ s.final.Reflection σ ∧ ∀ i, (σ i).1=τ i.1) ∧
      ∀ i, physicalError (packet (F.m i) (F.A i))
        (outputVector s.final i ∘ s.chart) < ε ∧
        (∫ z, |outputDensity s.final i z-F.marginalDensity i z| ∂phaseHaar) < ε := by
  obtain ⟨c,hc,h0,χ,hχ,hd,_he,hrχ⟩ := scalar_grouped_neutral_cutoffs F hr
  obtain ⟨s,hsχ,_hsc,hsδ,hjet,hs⟩ := exists_controlled_neutral F hc h0 (fun i x _ => χ i x)
    (fun i => (hχ i).1.comp contDiff_fst)
    (fun i => compactSupport_frequency_cylinder (hχ i).2.1)
    (fun i _ => (hχ i).2.2.1) (fun i x _ => (hχ i).2.2.2.1 x)
    (fun i => (hχ i).2.2.2.2) Q frame hε hκ hζ
  refine ⟨s,hsδ,hjet,?_,?_,?_,hs⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro k hki hkj
    obtain ⟨a,ha⟩ := (s.indices i k).mp hki
    obtain ⟨b,hb⟩ := (s.indices j k).mp hkj
    rw [hsχ] at ha hb
    exact Set.disjoint_left.mp (hd i j hij) (subset_tsupport _ ha) (subset_tsupport _ hb)
  · intro i x a
    simpa only [hsχ] using hrχ i x
  · obtain ⟨σ,hroot,hσ,hrσ⟩ := s.reflection hr hτ (by simpa only [hsχ] using fun i x _ => hrχ i x)
    exact ⟨σ,hσ,hrσ,hroot⟩

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped BigOperators
namespace ThreeTorus
namespace PassagePackets

lemma marginalDensity_congr {ι κ : Type*} {F : PassagePackets ι} {G : PassagePackets κ}
    {i : ι} {j : κ} (hm : F.m i=G.m j) (hA : F.A i=G.A j) (hV : F.V=G.V) :
    F.marginalDensity i =ᵐ[AddCircle.haarAddCircle] G.marginalDensity j := by
  have hv : F.periodic.lift=G.periodic.lift := by
    funext x
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective x
    exact congrFun hV x
  have he : AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (F.marginalDensity i z)) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (G.marginalDensity j z)) := by
    rw [← F.marginalDensity_spectral i,← G.marginalDensity_spectral j,hm,hA,hv]
  have h := (withDensity_eq_iff_of_sigmaFinite
    (F.marginalDensity_measurable i).ennreal_ofReal.aemeasurable
    (G.marginalDensity_measurable j).ennreal_ofReal.aemeasurable).mp he
  filter_upwards [h] with z hz
  have hh := congrArg ENNReal.toReal hz
  simpa only [ENNReal.toReal_ofReal (F.marginalDensity_nonneg i z),
    ENNReal.toReal_ofReal (G.marginalDensity_nonneg j z)] using hh

lemma append_marginalDensity_left {ι κ : Type*} (F : PassagePackets ι) (G : PassagePackets κ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hgF : F.GoodArc δ) (hgG : G.GoodArc δ) (hV : G.V=F.V) (i : ι) :
    (F.append G hδ hgF hgG hV).marginalDensity (Sum.inl i) =ᵐ[AddCircle.haarAddCircle] F.marginalDensity i :=
  marginalDensity_congr rfl rfl rfl

end PassagePackets
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
lemma integral_abs_sum_sub_le_of_integrable {ι : Type*} [Fintype ι]
    {p q : ι → UnitAddCircle → ℝ} (hp : ∀ i, Integrable (p i) phaseHaar)
    (hq : ∀ i, Integrable (q i) phaseHaar) :
    (∫ z, |(∑ i, p i z)-(∑ i, q i z)| ∂phaseHaar) ≤
      ∑ i, ∫ z, |p i z-q i z| ∂phaseHaar := by
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∫ z, ∑ i, |p i z-q i z| ∂phaseHaar := integral_mono
      ((integrable_finsetSum _ (fun i _ => (hp i).sub (hq i))).abs)
      (integrable_finsetSum _ (fun i _ => ((hp i).sub (hq i)).abs))
      (fun z => Finset.abs_sum_le_sum_abs _ _)
    _ = _ := integral_finsetSum _ (fun i _ => ((hp i).sub (hq i)).abs)

namespace NeutralStep
variable {ι : Type*} [Fintype ι] {F : PassagePackets ι} (s : NeutralStep F)

lemma density_total {ε : ℝ} (hε : 0 < ε)
    (he : ∀ i, (∫ z, |outputDensity s.final i z-F.marginalDensity i z| ∂phaseHaar) <
      ε/(Fintype.card ι+1)) :
    (∫ z, |(∑ j, s.final.marginalDensity j z)-(∑ i, F.marginalDensity i z)| ∂phaseHaar) < ε := by
  have heq (z : UnitAddCircle) : (∑ j, s.final.marginalDensity j z)=∑ i, outputDensity s.final i z := by
    simp only [s.final.marginalDensity_eq s.spare,outputDensity,Fintype.sum_sigma]
  simp_rw [heq]
  calc
    _ ≤ ∑ i, ∫ z, |outputDensity s.final i z-F.marginalDensity i z| ∂phaseHaar :=
      integral_abs_sum_sub_le_of_integrable
        (fun i => continuous_circle_integrable (continuous_outputDensity s.final i)) F.marginalDensity_integrable
    _ ≤ ∑ _i : ι, ε/(Fintype.card ι+1) := Finset.sum_le_sum (fun i _ => (he i).le)
    _ < ε := by
      have hc : (0:ℝ) < Fintype.card ι+1 := by positivity
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← mul_div_assoc]
      apply (div_lt_iff₀ hc).2
      nlinarith

end NeutralStep

/-- Simultaneous transport of two real lists with the SAME physical passage.
The first list retains injective angular indices; no cross-list orthogonality
or disjointness is assumed. -/
theorem exists_neutral_pair {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : PassagePackets ι) (H : PassagePackets κ) (hmi : Injective F.m)
    {δ : ℝ} (hδ : 0 ≤ δ) (hgF : F.GoodArc δ) (hgH : H.GoodArc δ) (hV : H.V=F.V)
    (τ : ι → ι) (σ : κ → κ) (hτ : Involutive τ) (hσ : Involutive σ)
    (hrF : F.Reflection τ) (hrH : H.Reflection σ)
    (Q : PhysicalJetData) (frame : PhysicalFrame)
    {ε η ζ : ℝ} (hε : 0 < ε) (hη : 0 < η) (hζ : 0 < ζ) :
    ∃ s : NeutralStep (F.append H hδ hgF hgH hV),
      s.δ < η ∧ Q.Close ζ frame F.V (s.nextFrame frame) s.final.V ∧
      Injective (s.reindex Sum.inl).final.m ∧
      (∃ τ', Involutive τ' ∧ (s.reindex Sum.inl).final.Reflection τ') ∧
      (∃ σ', Involutive σ' ∧ (s.reindex Sum.inr).final.Reflection σ') ∧
      physicalDist (finitePacketVector F.m F.A)
        (finitePacketVector (s.reindex Sum.inl).final.m (s.reindex Sum.inl).final.A ∘ s.chart) < ε ∧
      physicalDist (finitePacketVector H.m H.A)
        (finitePacketVector (s.reindex Sum.inr).final.m (s.reindex Sum.inr).final.A ∘ s.chart) < ε ∧
      (∫ z, |(∑ j, (s.reindex Sum.inl).final.marginalDensity j z)-
        (∑ i, F.marginalDensity i z)| ∂phaseHaar) < ε := by
  classical
  let U := F.append H hδ hgF hgH hV
  let r : ι ⊕ κ → ι ⊕ κ := Sum.map τ σ
  have hr : U.Reflection r := F.append_reflection H hδ hgF hgH hV hrF hrH
  have hri : Involutive r := by
    intro i; cases i with
    | inl i => exact congrArg Sum.inl (hτ i)
    | inr i => exact congrArg Sum.inr (hσ i)
  let a := ε/(Fintype.card ι+1)
  let b := ε/(Fintype.card κ+1)
  have ha : 0 < a := div_pos hε (by positivity)
  have hb : 0 < b := div_pos hε (by positivity)
  have he : 0 < min (min (a^2) (b^2)) a := lt_min (lt_min (sq_pos_of_pos ha) (sq_pos_of_pos hb)) ha
  obtain ⟨s,hsδ,hjet,hd,hχ,_hr,hs⟩ := exists_grouped_neutral U r hri hr Q frame he hη hζ
  refine ⟨s,hsδ,hjet,?_,?_,?_,?_,?_,?_⟩
  · apply s.reindex_final_injective
    intro i j hij
    exact hd (Sum.inl i) (Sum.inl j) (fun he => hij (hmi he))
  · have hh : (U.reindex Sum.inl).Reflection τ := U.reindex_reflection hr (fun _ => rfl)
    obtain ⟨τ',_,hi,hh'⟩ := (s.reindex Sum.inl).reflection hh hτ (fun i x a => hχ (Sum.inl i) x a)
    exact ⟨τ',hi,hh'⟩
  · have hh : (U.reindex Sum.inr).Reflection σ := U.reindex_reflection hr (fun _ => rfl)
    obtain ⟨σ',_,hi,hh'⟩ := (s.reindex Sum.inr).reflection hh hσ (fun i x a => hχ (Sum.inr i) x a)
    exact ⟨σ',hi,hh'⟩
  · exact (s.reindex Sum.inl).physicalDist_total hε (fun i =>
      ((hs (Sum.inl i)).1.trans_le ((min_le_left _ _).trans (min_le_left _ _))))
  · exact (s.reindex Sum.inr).physicalDist_total hε (fun i =>
      ((hs (Sum.inr i)).1.trans_le ((min_le_left _ _).trans (min_le_right _ _))))
  · have hh := (s.reindex Sum.inl).density_total hε (fun i =>
      ((hs (Sum.inl i)).2.trans_le (min_le_right _ _)))
    have heq : (fun z => ∑ i, (U.reindex Sum.inl).marginalDensity i z) =ᵐ[phaseHaar]
        (fun z => ∑ i, F.marginalDensity i z) := by
      filter_upwards [ae_all_iff.2 (fun i => F.append_marginalDensity_left H hδ hgF hgH hV i)] with z hz
      exact Finset.sum_congr rfl (fun i _ => hz i)
    rwa [integral_congr_ae (heq.mono (fun z hz => congrArg (fun t => |(∑ j, (s.reindex Sum.inl).final.marginalDensity j z)-t|) hz))] at hh

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Preparation
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real perturbation, smooth cylinder approximation, tensor preparation, real packet families, and two neutral separations. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace ThreeTorus

variable {d : Type*} [Fintype d]

lemma multiTrigPolynomial_apply (c : (d → ℤ) →₀ ℂ) (x : UnitAddTorus d) :
    multiTrigPolynomial c x = ∑ k ∈ c.support, c k * UnitAddTorus.mFourier k x := by
  simp [multiTrigPolynomial,Finsupp.sum]

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

attribute [instance] RealPacketFamily.finite
namespace RealPacketFamily
variable (F : RealPacketFamily)
lemma continuous_vector : Continuous F.vector :=
  continuous_finsetSum _ (fun i _ => continuous_packet (F.data.continuous_amplitude i))
lemma vector_memLp : MemLp F.vector 2 tripleVolume :=
  F.continuous_vector.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma density_integrable : Integrable F.density phaseHaar :=
  integrable_finsetSum _ (fun i _ => F.data.marginalDensity_integrable i)

lemma append_vector (G : RealPacketFamily) {δ : ℝ} (hδ : 0 ≤ δ)
    (hF : F.data.GoodArc δ) (hG : G.data.GoodArc δ) (hV : G.data.V=F.data.V) :
    (F.append G hδ hF hG hV).vector = fun x => F.vector x+G.vector x := by
  funext x
  change (∑ i : F.Index ⊕ G.Index, packet (Sum.elim F.data.m G.data.m i) (Sum.elim F.data.A G.data.A i) x) = _
  rw [Fintype.sum_sum_type]
  rfl

end RealPacketFamily
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

theorem exists_neutral_families (F H : RealPacketFamily) (hmi : Injective F.data.m)
    {δ : ℝ} (hδ : 0 ≤ δ) (hgF : F.data.GoodArc δ) (hgH : H.data.GoodArc δ) (hV : H.data.V=F.data.V)
    (Q : PhysicalJetData) (frame : PhysicalFrame)
    {ε η ζ : ℝ} (hε : 0 < ε) (hη : 0 < η) (hζ : 0 < ζ) :
    ∃ s : NeutralStep (F.data.append H.data hδ hgF hgH hV),
      ∃ F' H' : RealPacketFamily,
      F'.data.V=s.final.V ∧ H'.data.V=s.final.V ∧ F'.data.GoodArc s.δ ∧ H'.data.GoodArc s.δ ∧
      s.δ < η ∧ Q.Close ζ frame F.data.V (s.nextFrame frame) F'.data.V ∧ Injective F'.data.m ∧
      physicalDist F.vector (F'.vector ∘ s.chart) < ε ∧
      physicalDist H.vector (H'.vector ∘ s.chart) < ε ∧
      (∫ z, |F'.density z-F.density z| ∂phaseHaar) < ε := by
  obtain ⟨s,hsδ,hjet,hmi',⟨τ',hτ',hrF'⟩,⟨σ',hσ',hrH'⟩,hF',hH',hp⟩ :=
    exists_neutral_pair F.data H.data hmi hδ hgF hgH hV F.neg H.neg F.invol H.invol
      F.reflected H.reflected Q frame hε hη hζ
  let F' : RealPacketFamily := ⟨_,inferInstance,(s.reindex Sum.inl).final,τ',hτ',hrF'⟩
  let H' : RealPacketFamily := ⟨_,inferInstance,(s.reindex Sum.inr).final,σ',hσ',hrH'⟩
  exact ⟨s,F',H',rfl,rfl,(s.reindex Sum.inl).good,(s.reindex Sum.inr).good,hsδ,hjet,hmi',hF',hH',hp⟩

lemma physicalDist_continuous_comp (α : Equiv.Perm TripleTorus) (hc : Continuous α)
    (hm : MeasurePreserving α tripleVolume tripleVolume) (f g : TripleTorus → ℂ) :
    physicalDist (f ∘ α) (g ∘ α)=physicalDist f g := by
  unfold physicalDist physicalError
  exact congrArg Real.sqrt (hm.integral_comp (hc.measurableEmbedding α.injective) (fun x => ‖f x-g x‖^2))

lemma densityDist_triangle {p q r : UnitAddCircle → ℝ}
    (hp : Integrable p phaseHaar) (hq : Integrable q phaseHaar) (hr : Integrable r phaseHaar) :
    (∫ z, |p z-r z| ∂phaseHaar) ≤ (∫ z, |p z-q z| ∂phaseHaar)+(∫ z, |q z-r z| ∂phaseHaar) := by
  calc
    _ ≤ ∫ z, |p z-q z|+|q z-r z| ∂phaseHaar :=
      integral_mono (hp.sub hr).abs (((hp.sub hq).abs).add ((hq.sub hr).abs))
        (fun z => abs_sub_le (p z) (q z) (r z))
    _ = _ := integral_add (hp.sub hq).abs (hq.sub hr).abs
end ThreeTorus
end
end

section
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace ThreeTorus

lemma toTriple_apply (x : Torus) : toTriple x = (x 0,x 1,x 2) := rfl

lemma toTriple_symm_apply (x : TripleTorus) : toTriple.symm x = ![x.1,x.2.1,x.2.2] := by
  apply toTriple.injective
  simp only [MeasurableEquiv.apply_symm_apply,toTriple_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  rfl

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

lemma mFourier_toTriple (k : TensorIndex) (x : TripleTorus) :
    UnitAddTorus.mFourier k (toTriple.symm x) = tensorCharacter k x := by
  change (∏ i, fourier (k i) (toTriple.symm x i)) = _
  simp only [Fin.prod_univ_three,toTriple_symm_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,tensorCharacter]
  rfl

lemma tensorPolynomial_eq (c : TensorIndex →₀ ℂ) : tensorPolynomial c = multiTrigPolynomial c ∘ toTriple.symm := by
  funext x
  simp only [tensorPolynomial,multiTrigPolynomial_apply,Function.comp_apply,Finsupp.sum,mFourier_toTriple]

lemma continuous_toTriple_symm : Continuous toTriple.symm := by
  simp only [show (toTriple.symm : TripleTorus → Torus) = fun x => ![x.1,x.2.1,x.2.2] from funext toTriple_symm_apply]
  exact continuous_pi (fun i => by fin_cases i <;> fun_prop)

lemma tensorPolynomial_continuous (c : TensorIndex →₀ ℂ) : Continuous (tensorPolynomial c) := by
  rw [tensorPolynomial_eq]
  exact (multiTrigPolynomial c).continuous.comp continuous_toTriple_symm

lemma tensorLast_nonzero {c : TensorIndex →₀ ℂ} (hc : c 0=0) {k : TensorIndex}
    (hk : k ∈ (tensorLast c).support) : k 2 ≠ 0 := by
  classical
  have hh := Finsupp.mem_support_iff.1 hk
  simp only [tensorLast,Finsupp.filter_apply] at hh
  split_ifs at hh with h
  · intro hk2
    have he : k=0 := by ext i; fin_cases i <;> simp [h.1,h.2,hk2]
    exact hh (by simpa [he] using hc)
  · exact False.elim (hh rfl)

end ThreeTorus
end
end

section

/-! The two neutral passages of source05, on the same literal packet family.
The first separates cylinder supports and the second makes angular modes
injective. Physical and density estimates retain each original root label. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma scalar_cylinder_compact {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun p : ℝ × UnitAddCircle => f p.1) := by
  apply (hf.prod isCompact_univ).of_isClosed_subset (isClosed_tsupport _) 
  apply closure_minimal _ (hf.isClosed.prod isClosed_univ)
  intro p hp
  exact ⟨subset_tsupport f hp,mem_univ _⟩

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_TensorPackets
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Good-arc cutoffs, scalar and tensor packet constructors, fiber insertion, and initial dense tests. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace ThreeTorus

lemma sharp_cutoff_integral_bound {δ t : ℝ} (ht : 0 < t) (hδ : 0 ≤ δ)
    (hu : δ+t < 1/2) {b : ℝ → ℝ} (hbc : Continuous b) (_hbs : HasCompactSupport b)
    (hb : ∀ x, 0 ≤ b x ∧ b x ≤ 1)
    (hone : ∀ x ∈ Icc (δ+t) (1-δ-t), b x = 1) :
    (∫ x in Ioo (0:ℝ) 1, (1-b x)^2) ≤ 2*δ+2*t := by
  have hbint : IntegrableOn (fun x : ℝ => b x^2) (Ioo (0:ℝ) 1) :=
    (hbc.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hlower : 1-2*δ-2*t ≤ ∫ x in Ioo (0:ℝ) 1, b x^2 := by
    calc
      _ = ∫ x in Icc (δ+t) (1-δ-t), (1:ℝ) := by
        simp only [integral_const,Measure.restrict_apply_univ,smul_eq_mul,mul_one,
          Measure.real,Real.volume_Icc,ENNReal.toReal_ofReal (by linarith : 0 ≤ 1-δ-t-(δ+t))]
        ring
      _ = ∫ x in Icc (δ+t) (1-δ-t), b x^2 := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        dsimp only
        rw [hone x hx,one_pow]
      _ ≤ ∫ x in Ioo (0:ℝ) 1, b x^2 := by
        apply setIntegral_mono_set hbint (.of_forall fun _ => sq_nonneg _)
        exact .of_forall fun x hx => ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hi : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Ioo (0:ℝ) 1) :=
    continuous_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  calc
    _ ≤ ∫ x in Ioo (0:ℝ) 1, 1-b x^2 := by
      apply setIntegral_mono_on
        ((continuous_const.sub hbc).pow 2 |>.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
        (hi.sub hbint) measurableSet_Ioo
      intro x _
      change (1-b x)^2 ≤ 1-b x^2
      nlinarith [(hb x).1,(hb x).2]
    _ = 1-∫ x in Ioo (0:ℝ) 1, b x^2 := by rw [integral_sub hi hbint]; simp
    _ ≤ _ := by linarith

lemma circle_cutoff_squared_error {χ : ℝ → ℝ}
    (_hc : HasCompactSupport χ) (hs : support χ ⊆ Ioo (0:ℝ) 1)
    (_hb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    (∫ x, (1-(periodize_periodic χ).lift x)^2 ∂AddCircle.haarAddCircle) =
      ∫ x in Ioo (0:ℝ) 1, (1-χ x)^2 := by
  have he := AddCircle.integral_preimage 1 0
    (fun x : UnitAddCircle => (1-(periodize_periodic χ).lift x)^2)
  simp only [zero_add,AddCircle.volume_eq_smul_haarAddCircle,ENNReal.ofReal_one,one_smul] at he
  rw [← he,integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  change (1-periodize χ x)^2 = (1-χ x)^2
  rw [periodize_eq_on_unit hs ⟨hx.1.le,hx.2.le⟩]

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma cylinderTorusCutoff_scalar (χ : ℝ → ℝ) (p : UnitAddCircle × UnitAddCircle) :
    cylinderTorusCutoff (fun q => χ q.1) p = (periodize_periodic χ).lift p.1 := by
  rcases p with ⟨p,q⟩
  obtain ⟨x,hx⟩ := QuotientAddGroup.mk_surjective p
  subst p
  rfl

/-- A common scalar good-arc cutoff produces literal smooth input packets;
all data are fixed before any passage integer is chosen. -/
theorem exists_scalar_cutoff_packets {ι : Type*}
    (m : ι → ℤ) (hm : ∀ i, m i ≠ 0)
    (C : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (hCc : ∀ i, Continuous (C i))
    (hCs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => C i (p.1,p.2)))
    {χ : ℝ → ℝ} (hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχc : HasCompactSupport χ) {δ : ℝ} (hδ : 0 ≤ δ) (hd : δ < 1/2)
    (hχI : tsupport χ ⊆ Ioo δ (1-δ))
    (V : ℝ → ℝ) (hVp : Periodic V 1)
    (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVd : ∀ x ∈ Ioo δ (1-δ), 0 < deriv V x) :
    ∃ F : PassagePackets ι, F.m=m ∧ F.V=V ∧ F.GoodArc δ ∧
      (∀ i p, F.A i p = ((periodize_periodic χ).lift p.1:ℂ)*C i p) ∧
      ∀ i a x, F.A₀ i a x = (χ x:ℂ)*C i ((x:UnitAddCircle),a) := by
  obtain ⟨l,u,R,hdl,hlu,hud,hR,hKI,hbuffer⟩ := compact_inside_buffered_interval
    hχc (by linarith : δ < 1-δ) hχI
  have hs : CylinderSmooth (fun p : ℝ × UnitAddCircle => χ p.1) := hχs.comp contDiff_fst
  have hc : HasCompactSupport (fun p : ℝ × UnitAddCircle => χ p.1) := scalar_cylinder_compact hχc
  have hso : support (fun p : ℝ × UnitAddCircle => χ p.1) ⊆ Ioo (0:ℝ) (0+1) ×ˢ univ := by
    intro p hp
    have h := hχI (subset_tsupport χ hp)
    exact ⟨⟨hδ.trans_lt h.1,by linarith [h.2]⟩,mem_univ _⟩
  have hsi : support (fun p : ℝ × UnitAddCircle => χ p.1) ⊆ Ioc l u ×ˢ univ :=
    fun p hp => ⟨hKI (subset_tsupport χ hp),mem_univ _⟩
  let F := cutoffPackets m hm C hCc hCs (fun _ p => χ p.1) (fun _ => hs) (fun _ => hc)
    0 l u R (fun _ => hso) (fun _ => hsi) (hδ.trans hdl.le) (by linarith) hlu.le hR
    V hVp hVs (fun x hx => hVd x (hbuffer hx))
  refine ⟨F,rfl,rfl,⟨rfl,hdl,hud,hVd⟩,?_,fun _ _ _ => rfl⟩
  intro i p
  change (cylinderTorusCutoff (fun q => χ q.1) p:ℂ)*C i p = _
  rw [cylinderTorusCutoff_scalar]

lemma scalar_packets_reflection {ι : Type*} (F : PassagePackets ι)
    {τ : ι → ι} {m : ι → ℤ} {C : ι → UnitAddCircle × UnitAddCircle → ℂ}
    {χ : ℝ → ℝ} (hm : F.m=m) (hmi : ∀ i, m (τ i) = -m i)
    (hc : ∀ i p, C (τ i) p = conj (C i p))
    (hA : ∀ i p, F.A i p = ((periodize_periodic χ).lift p.1:ℂ)*C i p)
    (hA₀ : ∀ i a x, F.A₀ i a x = (χ x:ℂ)*C i ((x:UnitAddCircle),a)) :
    F.Reflection τ := by
  constructor
  · simpa only [hm] using hmi
  · intro i p; rw [hA,hA,hc]; simp only [map_mul,Complex.conj_ofReal]
  · intro i a x; rw [hA₀,hA₀,hc]; simp only [map_mul,Complex.conj_ofReal]

end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped BigOperators ComplexConjugate
namespace ThreeTorus

lemma tensor_filter_reflection {c : TensorIndex →₀ ℂ} (hc : ∀ k, c (-k)=conj (c k))
    (P : TensorIndex → Prop) [DecidablePred P] (hP : ∀ k, P (-k) ↔ P k) :
    ∀ k, (c.filter P) (-k)=conj ((c.filter P) k) := by
  intro k
  simp only [Finsupp.filter_apply,hP,hc,apply_ite,map_zero]
  split_ifs <;> rfl

lemma tensorMiddle_reflection {c : TensorIndex →₀ ℂ} (hc : ∀ k, c (-k)=conj (c k)) :
    ∀ k, tensorMiddle c (-k)=conj (tensorMiddle c k) :=
  tensor_filter_reflection hc _ (fun _ => by simp)
lemma tensorLast_reflection {c : TensorIndex →₀ ℂ} (hc : ∀ k, c (-k)=conj (c k)) :
    ∀ k, tensorLast c (-k)=conj (tensorLast c k) :=
  tensor_filter_reflection hc _ (fun _ => by simp)

lemma tensorSupportNeg_involutive {c : TensorIndex →₀ ℂ} (hc : ∀ k, c (-k)=conj (c k)) :
    Involutive (tensorSupportNeg hc) := fun _ => Subtype.ext (neg_neg _)

/-- Literal smooth packets of a finite tensor polynomial after a cyclic
coordinate change. The unused old coordinate is not silently discarded. -/
theorem exists_rotated_tensor_packets (c : TensorIndex →₀ ℂ)
    (hc : ∀ k, c (-k)=conj (c k)) (a b d : Fin 3)
    (hn : ∀ k ∈ c.support, k a ≠ 0)
    {χ : ℝ → ℝ} (hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχc : HasCompactSupport χ) {δ : ℝ} (hδ : 0 ≤ δ) (hd : δ < 1/2)
    (hχI : tsupport χ ⊆ Ioo δ (1-δ))
    (V : ℝ → ℝ) (hVp : Periodic V 1)
    (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVd : ∀ x ∈ Ioo δ (1-δ), 0 < deriv V x) :
    ∃ F : PassagePackets ↥c.support, F.V=V ∧ F.GoodArc δ ∧
      F.Reflection (tensorSupportNeg hc) ∧
      (∀ k, F.m k=k.val a) ∧
      ∀ x, finitePacketVector F.m F.A x = ((periodize_periodic χ).lift x.2.1:ℂ)*
        ∑ k ∈ c.support, c k*(fourier (k a) x.1*fourier (k b) x.2.1*fourier (k d) x.2.2) := by
  let C : ↥c.support → UnitAddCircle × UnitAddCircle → ℂ :=
    fun k ua => c k.val*fourier (k.val b) ua.1*fourier (k.val d) ua.2
  have hCc k : Continuous (C k) := by dsimp [C]; fun_prop
  have hCs k : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => C k (p.1,p.2)) :=
    (contDiff_const.mul ((smooth_fourier_lift (k.val b)).comp contDiff_fst)).mul
      ((smooth_fourier_lift (k.val d)).comp contDiff_snd)
  obtain ⟨F,hFm,hFV,hFg,hFA,hFA₀⟩ := exists_scalar_cutoff_packets
    (fun k : ↥c.support => k.val a) (fun k => hn k.val k.property) C hCc hCs
    hχs hχc hδ hd hχI V hVp hVs hVd
  have hCr k p : C (tensorSupportNeg hc k) p=conj (C k p) := by
    simp only [C,tensorSupportNeg,hc,Pi.neg_apply,fourier_neg,map_mul]
  have hFr := scalar_packets_reflection F hFm (fun _ => rfl) hCr hFA hFA₀
  refine ⟨F,hFV,hFg,hFr,fun _ => congrFun hFm _,?_⟩
  intro x
  simp only [finitePacketVector,packet,hFA,hFm,C]
  rw [Finset.mul_sum]
  change (∑ k ∈ c.support.attach, _) = _
  refine (Finset.sum_congr rfl (fun k _ => ?_)).trans
    (Finset.sum_attach c.support (fun k => ((periodize_periodic χ).lift x.2.1:ℂ)*
      (c k*(fourier (k a) x.1*fourier (k b) x.2.1*fourier (k d) x.2.2))))
  ring

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma neutralCircleCutoff_squared_error {δ : ℝ} (cut : LawCutoffs δ)
    (hδ : 0 < δ) (hd : δ < 1/8) :
    (∫ a, (1-neutralCircleCutoff cut a)^2 ∂phaseHaar) ≤ 4*δ := by
  have hs : support cut.ψ ⊆ Ioo (0:ℝ) 1 := fun x hx => by
    have hh := cut.ψ_support (subset_tsupport _ hx)
    exact ⟨hδ.trans hh.1,by linarith [hh.2]⟩
  change (∫ a, (1-(periodize_periodic cut.ψ).lift a)^2 ∂phaseHaar) ≤ _
  rw [circle_cutoff_squared_error cut.ψ_compact hs (fun x => ⟨cut.ψ_nonneg x,cut.ψ_le_one x⟩)]
  have hh := sharp_cutoff_integral_bound hδ hδ.le (by linarith : δ+δ < 1/2)
    cut.ψ_smooth.continuous cut.ψ_compact (fun x => ⟨cut.ψ_nonneg x,cut.ψ_le_one x⟩)
    (by simpa only [two_mul,sub_sub] using cut.ψ_one)
  linarith

lemma uniform_slow_cutoff_energy {f : TripleTorus → ℂ} (hf : Continuous f)
    {B : ℝ} (_hB : 0 ≤ B) (hb : ∀ x, ‖f x‖ ≤ B)
    {χ : UnitAddCircle → ℝ} (hχ : Continuous χ) :
    physicalError f (fun x => (χ x.2.1:ℂ)*f x) ≤
      B^2*(∫ u, (1-χ u)^2 ∂phaseHaar) := by
  have he (x : TripleTorus) : ‖f x-(χ x.2.1:ℂ)*f x‖^2 = (1-χ x.2.1)^2*‖f x‖^2 := by
    rw [show f x-(χ x.2.1:ℂ)*f x = ((1-χ x.2.1:ℝ):ℂ)*f x by push_cast; ring,
      norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  unfold physicalError
  simp_rw [he]
  calc
    _ ≤ ∫ x : TripleTorus, (1-χ x.2.1)^2*B^2 ∂tripleVolume := by
      apply integral_mono
        (((continuous_const.sub (hχ.comp (continuous_fst.comp continuous_snd))).pow 2).mul (hf.norm.pow 2)
          |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (((continuous_const.sub (hχ.comp (continuous_fst.comp continuous_snd))).pow 2).mul continuous_const
          |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      intro x
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb x) 2) (sq_nonneg _)
    _ = _ := by
      rw [integral_prod]
      · simp only [integral_const,probReal_univ,one_smul]
        rw [integral_prod]
        · simp only [integral_const,probReal_univ,one_smul]
          rw [integral_mul_const,mul_comm]
        · exact (((continuous_const.sub (hχ.comp continuous_fst)).pow 2).mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact (((continuous_const.sub (hχ.comp (continuous_fst.comp continuous_snd))).pow 2).mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma tensorMiddle_coords {c : TensorIndex →₀ ℂ} (H : UnitAddCircle → UnitAddCircle) (x : TripleTorus) :
    (∑ k ∈ (tensorMiddle c).support, tensorMiddle c k*(fourier (k 1) (passageChart H x).1 *
      fourier (k 2) (passageChart H x).2.1 * fourier (k 0) (passageChart H x).2.2)) =
      tensorPolynomial (tensorMiddle c) x := by
  classical
  unfold tensorPolynomial Finsupp.sum
  apply Finset.sum_congr rfl
  intro k hk
  have hh := Finsupp.mem_support_iff.mp hk
  have hk0 : k 0=0 := by
    simpa only [tensorMiddle,Finsupp.filter_apply] using
      (show k 0=0 from by
        by_contra hn
        exact hh (by simp [tensorMiddle,hn]))
  simp only [tensorCharacter,passageChart,circleThetaShear,circleCycle,Equiv.trans_apply,Equiv.coe_fn_mk,hk0,fourier_zero,one_mul,mul_one]

lemma tensorLast_coords {c : TensorIndex →₀ ℂ} (H J : UnitAddCircle → UnitAddCircle) (x : TripleTorus) :
    (∑ k ∈ (tensorLast c).support, tensorLast c k*(fourier (k 2) (passageChart J (passageChart H x)).1 *
      fourier (k 0) (passageChart J (passageChart H x)).2.1 *
      fourier (k 1) (passageChart J (passageChart H x)).2.2)) = tensorPolynomial (tensorLast c) x := by
  classical
  unfold tensorPolynomial Finsupp.sum
  apply Finset.sum_congr rfl
  intro k hk
  have hh := Finsupp.mem_support_iff.mp hk
  have hk01 : k 0=0 ∧ k 1=0 := by
    by_contra hn
    exact hh (by simp [tensorLast,hn])
  simp only [tensorCharacter,passageChart,circleThetaShear,circleCycle,Equiv.trans_apply,Equiv.coe_fn_mk,hk01.1,hk01.2,fourier_zero,one_mul,mul_one]

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma tensorBudget_nonneg (c : TensorIndex →₀ ℂ) : 0 ≤ tensorBudget c :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)
lemma rotatedTensor_continuous (c : TensorIndex →₀ ℂ) (a b d : Fin 3) :
    Continuous (rotatedTensor c a b d) := by
  unfold rotatedTensor
  apply continuous_finsetSum
  intro k _
  fun_prop
lemma rotatedTensor_norm_le (c : TensorIndex →₀ ℂ) (a b d : Fin 3) (x : TripleTorus) :
    ‖rotatedTensor c a b d x‖ ≤ tensorBudget c := by
  apply (norm_sum_le _ _).trans_eq
  simp only [norm_mul,fourier_apply,Circle.norm_coe,mul_one,tensorBudget]

lemma exists_tensor_cutoff_family (c : TensorIndex →₀ ℂ)
    (hc : ∀ k, c (-k)=conj (c k)) (a b d : Fin 3)
    (hn : ∀ k ∈ c.support, k a ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (hd : δ < 1/8) (cut : LawCutoffs δ)
    (V : ℝ → ℝ) (hp : Periodic V 1) (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hv : ∀ x ∈ Ioo δ (1-δ), 0 < deriv V x) :
    ∃ P : RealPacketFamily, P.data.V=V ∧ P.data.GoodArc δ ∧
      physicalError (rotatedTensor c a b d) P.vector ≤ 4*δ*(tensorBudget c)^2 := by
  obtain ⟨P,hPV,hPg,hPr,_hPm,hPv⟩ := exists_rotated_tensor_packets c hc a b d hn
    cut.ψ_smooth cut.ψ_compact hδ.le (by linarith : δ < 1/2) cut.ψ_support V hp hs hv
  let F : RealPacketFamily := ⟨↥c.support,inferInstance,P,tensorSupportNeg hc,
    tensorSupportNeg_involutive hc,hPr⟩
  refine ⟨F,hPV,hPg,?_⟩
  have he : F.vector = fun x => (neutralCircleCutoff cut x.2.1:ℂ)*rotatedTensor c a b d x := funext hPv
  rw [he]
  apply (uniform_slow_cutoff_energy (rotatedTensor_continuous c a b d)
    (tensorBudget_nonneg c) (rotatedTensor_norm_le c a b d) (continuous_neutralCircleCutoff cut)).trans
  have h := mul_le_mul_of_nonneg_left (neutralCircleCutoff_squared_error cut hδ hd)
    (sq_nonneg (tensorBudget c))
  nlinarith

lemma tensorMiddle_nonzero {c : TensorIndex →₀ ℂ} {k : TensorIndex}
    (hk : k ∈ (tensorMiddle c).support) : k 1 ≠ 0 := by
  classical
  have hh := Finsupp.mem_support_iff.mp hk
  intro hn
  exact hh (by simp [tensorMiddle,hn])

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma exists_cutoff_loss_budget (B : ℝ) {ε : ℝ} (he : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, δ < η → 4*δ*B^2 < ε^2 := by
  refine ⟨ε^2/(4*(B^2+1)),by positivity,?_⟩
  intro δ hd
  have hh := (lt_div_iff₀ (by positivity : 0 < 4*(B^2+1))).1 hd
  by_cases hδ : 0 ≤ δ
  · nlinarith [sq_nonneg B]
  · have : δ < 0 := lt_of_not_ge hδ
    have : 4*δ*B^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg B)
    exact this.trans_lt (sq_pos_of_pos he)

/-- Two literal neutral passages convert both retained slow Fourier components
into nonzero angular packets. The F list alone is kept orthogonal. All objects,
cutoffs and bounds are fixed before their respective passage integer choices. -/
theorem exists_two_slow_insertions_oai (F H : RealPacketFamily) (hmi : Injective F.data.m)
    {δ : ℝ} (hδ : 0 ≤ δ) (hgF : F.data.GoodArc δ) (hgH : H.data.GoodArc δ) (hV : H.data.V=F.data.V)
    (c : TensorIndex →₀ ℂ) (hc0 : c 0=0) (hcr : ∀ k, c (-k)=conj (c k))
    (Q : PhysicalJetData) (frame : PhysicalFrame)
    {ε κ ζ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∃ F' H' : RealPacketFamily, ∃ α : Equiv.Perm TripleTorus, ∃ frame' : PhysicalFrame,
      Continuous α ∧ MeasurePreserving α tripleVolume tripleVolume ∧
      frame'.chart=frame.chart.trans α ∧ H'.data.V=F'.data.V ∧ Injective F'.data.m ∧
      (∃ δ' : ℝ, 0 < δ' ∧ δ' < 1/8 ∧ δ' < κ ∧ F'.data.GoodArc δ' ∧ H'.data.GoodArc δ') ∧
      Q.Close ζ frame F.data.V frame' F'.data.V ∧
      physicalDist F.vector (F'.vector ∘ α) < ε ∧
      physicalDist (fun x => H.vector x+tensorPolynomial (tensorMiddle c) x+tensorPolynomial (tensorLast c) x)
        (H'.vector ∘ α) < ε ∧
      (∫ z, |F'.density z-F.density z| ∂phaseHaar) < ε := by
  classical
  let e := ε/4
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨η,hη,hηe⟩ := exists_cutoff_loss_budget (tensorBudget (tensorMiddle c)) he
  obtain ⟨s,F₁,H₁,hF₁V,hH₁V,hF₁g,hH₁g,hsδ,hsjet,hF₁i,hsF,hsH,hsp⟩ :=
    exists_neutral_families F H hmi hδ hgF hgH hV Q frame he hη (half_pos hζ)
  obtain ⟨P₁,hP₁V,hP₁g,hP₁e⟩ := exists_tensor_cutoff_family (tensorMiddle c)
    (tensorMiddle_reflection hcr) 1 2 0 (fun _ => tensorMiddle_nonzero)
    s.δpos s.δsmall s.cut s.final.V s.final.periodic s.final.smooth_speed s.good.2.2.2
  let K := H₁.append P₁ s.δpos.le hH₁g hP₁g (hP₁V.trans hH₁V.symm)
  have hKg : K.data.GoodArc s.δ := H₁.data.append_good P₁.data s.δpos.le hH₁g hP₁g (hP₁V.trans hH₁V.symm)
  have hKV : K.data.V=F₁.data.V := hH₁V.trans hF₁V.symm
  obtain ⟨η₂,hη₂,hη₂e⟩ := exists_cutoff_loss_budget (tensorBudget (tensorLast c)) he
  obtain ⟨t,F₂,H₂,hF₂V,hH₂V,hF₂g,hH₂g,htδ,htjet,hF₂i,htF,htH,htp⟩ :=
    exists_neutral_families F₁ K hF₁i s.δpos.le hF₁g hKg hKV Q (s.nextFrame frame)
      he (lt_min hκ hη₂) (half_pos hζ)
  obtain ⟨P₂,hP₂V,hP₂g,hP₂e⟩ := exists_tensor_cutoff_family (tensorLast c)
    (tensorLast_reflection hcr) 2 0 1 (fun _ => tensorLast_nonzero hc0)
    t.δpos t.δsmall t.cut t.final.V t.final.periodic t.final.smooth_speed t.good.2.2.2
  let H' := H₂.append P₂ t.δpos.le hH₂g hP₂g (hP₂V.trans hH₂V.symm)
  have hscont : Continuous s.chart := continuous_passageChart (s.geometry.Hcontinuous s.n)
  have htcont : Continuous t.chart := continuous_passageChart (t.geometry.Hcontinuous t.n)
  have hsmp : MeasurePreserving s.chart tripleVolume tripleVolume := measurePreserving_passageChart (s.geometry.Hcontinuous s.n).measurable
  have htmp : MeasurePreserving t.chart tripleVolume tripleVolume := measurePreserving_passageChart (t.geometry.Hcontinuous t.n).measurable
  refine ⟨F₂,H',s.chart.trans t.chart,t.nextFrame (s.nextFrame frame),htcont.comp hscont,htmp.comp hsmp,rfl,
    hH₂V.trans hF₂V.symm,hF₂i,⟨t.δ,t.δpos,t.δsmall,htδ.trans_le (min_le_left _ _),hF₂g,?_⟩,?_,?_,?_,?_⟩
  · exact H₂.data.append_good P₂.data t.δpos.le hH₂g hP₂g (hP₂V.trans hH₂V.symm)
  · have hh := hsjet.trans htjet
    convert hh using 1; simp [show ζ/2+ζ/2=ζ by ring]
  · have htF' : physicalDist (F₁.vector ∘ s.chart) (F₂.vector ∘ (s.chart.trans t.chart)) < e := by
      change physicalDist (F₁.vector ∘ s.chart) ((F₂.vector ∘ t.chart) ∘ s.chart) < e
      rwa [physicalDist_continuous_comp s.chart hscont hsmp]
    have hh := physicalDist_triangle F.vector_memLp (continuous_triple_memLp (F₁.continuous_vector.comp hscont))
      (continuous_triple_memLp (F₂.continuous_vector.comp (htcont.comp hscont)))
    exact (hh.trans_lt (add_lt_add hsF htF')).trans_le (by dsimp [e]; linarith)
  · have hm : (rotatedTensor (tensorMiddle c) 1 2 0 ∘ s.chart)=tensorPolynomial (tensorMiddle c) :=
      funext (tensorMiddle_coords (s.geometry.H s.n))
    have hl : (rotatedTensor (tensorLast c) 2 0 1 ∘ (s.chart.trans t.chart))=tensorPolynomial (tensorLast c) :=
      funext (tensorLast_coords (s.geometry.H s.n) (t.geometry.H t.n))
    have hP₁ : physicalDist (tensorPolynomial (tensorMiddle c)) (P₁.vector ∘ s.chart) < e := by
      rw [← hm,physicalDist_continuous_comp s.chart hscont hsmp]
      exact (physicalDist_lt_iff _ _ he).2 (hP₁e.trans_lt (hηe _ hsδ))
    have hP₂ : physicalDist (tensorPolynomial (tensorLast c)) (P₂.vector ∘ (s.chart.trans t.chart)) < e := by
      rw [← hl,physicalDist_continuous_comp (s.chart.trans t.chart) (htcont.comp hscont) (htmp.comp hsmp)]
      exact (physicalDist_lt_iff _ _ he).2 (hP₂e.trans_lt (hη₂e _ (htδ.trans_le (min_le_right _ _))))
    have hK : physicalDist (fun x => H.vector x+tensorPolynomial (tensorMiddle c) x) (K.vector ∘ s.chart) < e+e := by
      have hh := physicalDist_add_le H.vector_memLp (continuous_triple_memLp (H₁.continuous_vector.comp hscont))
        (continuous_triple_memLp (tensorPolynomial_continuous (tensorMiddle c))) (continuous_triple_memLp (P₁.continuous_vector.comp hscont))
      have hv := H₁.append_vector P₁ s.δpos.le hH₁g hP₁g (hP₁V.trans hH₁V.symm)
      change K.vector = _ at hv
      rw [hv]
      exact hh.trans_lt (add_lt_add hsH hP₁)
    have hT : physicalDist (K.vector ∘ s.chart) (H₂.vector ∘ (s.chart.trans t.chart)) < e := by
      change physicalDist (K.vector ∘ s.chart) ((H₂.vector ∘ t.chart) ∘ s.chart) < e
      rwa [physicalDist_continuous_comp s.chart hscont hsmp]
    have hKH : physicalDist (fun x => H.vector x+tensorPolynomial (tensorMiddle c) x)
        (H₂.vector ∘ (s.chart.trans t.chart)) < (e+e)+e :=
      (physicalDist_triangle (continuous_triple_memLp (H.continuous_vector.add (tensorPolynomial_continuous (tensorMiddle c))))
        (continuous_triple_memLp (K.continuous_vector.comp hscont))
        (continuous_triple_memLp (H₂.continuous_vector.comp (htcont.comp hscont)))).trans_lt (add_lt_add hK hT)
    have hh := physicalDist_add_le (continuous_triple_memLp (H.continuous_vector.add (tensorPolynomial_continuous (tensorMiddle c))))
      (continuous_triple_memLp (H₂.continuous_vector.comp (htcont.comp hscont)))
      (continuous_triple_memLp (tensorPolynomial_continuous (tensorLast c)))
      (continuous_triple_memLp (P₂.continuous_vector.comp (htcont.comp hscont)))
    have hv := H₂.append_vector P₂ t.δpos.le hH₂g hP₂g (hP₂V.trans hH₂V.symm)
    change H'.vector = _ at hv
    rw [hv]
    convert hh.trans_lt (add_lt_add hKH hP₂) using 1 <;> first | rfl | (simp only [e]; ring)
  · have hh := densityDist_triangle F₂.density_integrable F₁.density_integrable F.density_integrable
    have ht := hh.trans_lt (add_lt_add htp hsp)
    dsimp [e] at ht
    linarith
end ThreeTorus
end
end

end OAI
end

theorem solution : type_of% @OAI.ThreeTorus.exists_two_slow_insertions_oai := @OAI.ThreeTorus.exists_two_slow_insertions_oai
