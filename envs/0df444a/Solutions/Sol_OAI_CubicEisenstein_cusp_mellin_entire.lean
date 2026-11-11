-- Prove2me | solution 1 for OAI.CubicEisenstein.cusp_mellin_entire
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T03:56:11.022353+00:00
-- url     : https://prove2.me/submissions/21ae1d6a-9bbf-4306-b92e-32c2d36fcc49

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SourceBesselExpansion
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_InverseCuspCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ReflectedCuspMellin
import Theorems.Thm_OAI_CubicEisenstein_reflectedCuspProfile_mellin
import Theorems.Thm_OAI_CubicEisenstein_reflectedCuspProfile_mellinConvergent
import Theorems.Thm_OAI_CubicEisenstein_cusp_truncation_reflection_ae
import Theorems.Thm_OAI_CubicEisenstein_truncatedCuspProfile_mellin_entire


set_option autoImplicit false
open OAI
noncomputable section
open OAI.CubicEisenstein
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology
namespace OAI.CubicEisenstein
theorem _root_.solution (f g : ℝ→ℂ) (A : ℂ) (Q decayF decayG : ℝ)
    (hQ : 0<Q) (hdecayF : 0<decayF) (hdecayG : 0<decayG)
    (hf : ContinuousOn f (Set.Ioi 0)) (hg : ContinuousOn g (Set.Ioi 0))
    (hfbound : f =O[atTop] (fun v : ℝ=>Real.exp (-decayF*v)))
    (hgbound : g =O[atTop] (fun v : ℝ=>Real.exp (-decayG*v)))
    (hfg : ∀v : ℝ,0<v→f v=reflectedCuspProfile A Q g v) :
    (∀s : ℂ,MellinConvergent f s) ∧ Differentiable ℂ (mellin f) := by
  obtain ⟨hfc,hfd⟩ := truncatedCuspProfile_mellin_entire 1 decayF (by norm_num) hdecayF f hf hfbound
  obtain ⟨hgc,hgd⟩ := truncatedCuspProfile_mellin_entire (1/Q) decayG
    (by positivity) hdecayG g hg hgbound
  have hae := cusp_truncation_reflection_ae f g A Q hQ hfg
  have hresult (s : ℂ) : HasMellin f s
      (mellin (truncatedCuspProfile 1 f) s+
        A*(Q:ℂ)^(2-s)*mellin (truncatedCuspProfile (1/Q) g) (2-s)) := by
    have hr := reflectedCuspProfile_mellinConvergent
      (truncatedCuspProfile (1/Q) g) A s Q hQ (hgc (2-s))
    have hsum := hasMellin_add (hfc s) hr
    constructor
    · apply hsum.1.congr
      filter_upwards [hae] with v hv
      exact congrArg (fun z : ℂ=>(v:ℂ)^(s-1) • z) hv.symm
    · have he : mellin f s=mellin (fun v=>truncatedCuspProfile 1 f v+
          reflectedCuspProfile A Q (truncatedCuspProfile (1/Q) g) v) s := by
        unfold mellin
        apply integral_congr_ae
        filter_upwards [hae] with v hv
        rw [hv]
      rw [he,hsum.2,reflectedCuspProfile_mellin _ _ _ _ hQ]
  refine ⟨fun s=>(hresult s).1,?_⟩
  have he : mellin f=(fun s : ℂ=>mellin (truncatedCuspProfile 1 f) s+
      A*(Q:ℂ)^(2-s)*mellin (truncatedCuspProfile (1/Q) g) (2-s)) :=
    funext (fun s=>(hresult s).2)
  rw [he]
  let : NeZero (Q:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hQ.ne'⟩
  have hp := (differentiable_const_cpow_of_neZero (Q:ℂ)).comp
    ((differentiable_const (2:ℂ)).sub differentiable_id)
  exact hfd.add (((differentiable_const A).mul hp).mul
    (hgd.comp ((differentiable_const (2:ℂ)).sub differentiable_id)))
end OAI.CubicEisenstein
