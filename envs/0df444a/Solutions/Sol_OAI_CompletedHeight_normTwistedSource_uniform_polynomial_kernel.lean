-- Prove2me | solution 1 for OAI.CompletedHeight.normTwistedSource_uniform_polynomial_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:18:31.129216+00:00
-- url     : https://prove2.me/submissions/1bded6c8-84b5-4f13-99a8-9c3c1dd4db73

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_PolynomialHeight
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DensityBudgets
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RankMargins
import Theorems.Thm_OAI_CompletedHeight_uniformTwistedSchwartz_apply
import Theorems.Thm_OAI_CompletedHeight_normTwistedSource_uniform_degree
import Theorems.Thm_OAI_CompletedHeight_normTwistedSource_polynomial_kernel
import Theorems.Thm_OAI_CompletedHeight_normTwistedSource_support
import Theorems.Thm_OAI_CubicReflectionKernel_paperKernel_euler_source_uniform_weighted_bound


set_option autoImplicit false
open OAI
noncomputable section
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
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.CompletedHeight
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open CompletedGauss
namespace OAI.CompletedHeight
theorem _root_.solution (a b : ℝ) (ha : 0<a) :
    HasUniformPolynomialKernel (fun W : SupportedSmoothSource a b => normTwistedSource W.val) := by
  constructor
  · intro W t
    exact (normTwistedSource_polynomial_kernel W.val a b ha W.property.1 W.property.2).1 t
  · intro A K
    obtain ⟨s,D,hD,hkernel⟩ := CubicReflectionKernel.paperKernel_euler_source_uniform_weighted_bound a b ha A K
    obtain ⟨n,hn⟩ := normTwistedSource_uniform_degree a b ha s
    refine ⟨n,?_⟩
    intro W
    let S := vstarSchwartz W.val a b ha W.property.1 W.property.2
    have hS : Function.support (S : ℝ→ℂ)⊆Set.Icc a b := Vstar_support W.val a b W.property.1
    let G := uniformTwistedSchwartz S a b ha hS (S.smooth ⊤)
    obtain ⟨C,hC,hsource⟩ := hn S hS (S.smooth ⊤)
    have hlink (t : ℝ) : (G t : ℝ→ℂ)=Vstar (normTwistedSource W.val t) := by
      funext x
      rw [show G t x=uniformTwistedSchwartz S a b ha hS (S.smooth ⊤) t x from rfl,
        uniformTwistedSchwartz_apply]
      change FourierBridge.logPhase t (Real.log x)*((Real.sqrt x:ℂ)*W.val x)=
        (Real.sqrt x:ℂ)*(FourierBridge.logPhase t (Real.log x)*W.val x)
      ring
    have hGs (t : ℝ) : Function.support (G t : ℝ→ℂ)⊆Set.Icc a b := by
      intro x hx
      change G t x≠0 at hx
      rw [show G t x=uniformTwistedSchwartz S a b ha hS (S.smooth ⊤) t x from rfl,
        uniformTwistedSchwartz_apply] at hx
      exact hS (normTwistedSource_support S t hx)
    refine ⟨D*C,mul_pos hD hC,?_⟩
    intro t i hi x hx
    rw [←hlink t]
    exact (hkernel (G t) (hGs t) i hi x hx).trans
      ((mul_le_mul_of_nonneg_left (hsource t) hD.le).trans_eq (by ring))
end OAI.CompletedHeight
