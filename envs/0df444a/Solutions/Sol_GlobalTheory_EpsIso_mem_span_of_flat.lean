-- Prove2me | solution 1 for GlobalTheory.EpsIso.mem_span_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:21:34.414313+00:00
-- url     : https://prove2.me/submissions/c7e6d302-00da-4295-a06c-05b9c9a5729e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoOfIdModEpsThickening
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
namespace GlobalTheory.EpsIso
set_option maxHeartbeats 1000000 in
private theorem exists_eq_eps_mul_of_flat_of_eps_mul_eq_zero {K : Type} [Field K] {C : Type} [CommRing C] (a : DualNumber K →+* C)
    (ha : a.Flat) (c : C) (hc : a DualNumber.eps * c = 0) :
    ∃ d : C, c = a DualNumber.eps * d := by
  let _ : Algebra (DualNumber K) C := a.toAlgebra
  have _ : Module.Flat (DualNumber K) C := ha
  have hsum : ∑ _i : Unit, (DualNumber.eps : DualNumber K) • c = 0 := by
    rw [Fintype.sum_unique, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    exact hc
  obtain ⟨k, b, y, hy, hb⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := DualNumber K) (M := C)
    (f := fun _ : Unit => (DualNumber.eps : DualNumber K)) (x := fun _ => c) hsum
  have hkill : ∀ i, b () i = DualNumber.eps * TrivSqZeroExt.inl (b () i).snd := by
    intro i
    have h1 : DualNumber.eps * b () i = 0 := by
      have h0 := hb i
      rwa [Fintype.sum_unique] at h0
    have h2 : (b () i).fst = 0 := by
      have h3 := congrArg TrivSqZeroExt.snd h1
      rw [DualNumber.snd_mul, DualNumber.fst_eps, DualNumber.snd_eps, zero_mul, _root_.one_mul, zero_add,
        TrivSqZeroExt.snd_zero] at h3
      exact h3
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [TrivSqZeroExt.fst_mul, DualNumber.fst_eps, zero_mul, h2]
    · rw [DualNumber.snd_mul, DualNumber.fst_eps, DualNumber.snd_eps, zero_mul, zero_add, _root_.one_mul,
        TrivSqZeroExt.fst_inl]
  refine ⟨∑ i, a (TrivSqZeroExt.inl (b () i).snd) * y i, ?_⟩
  rw [show c = ∑ j, b () j • y j from hy (), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hki := hkill i
  rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  conv_lhs => rw [hki]
  rw [map_mul, _root_.mul_assoc]
end GlobalTheory.EpsIso
namespace GlobalTheory
end GlobalTheory
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.EpsIso
namespace GlobalTheory.EpsIso
theorem _root_.solution {K : Type} [Field K] {C : Type} [CommRing C] (a : DualNumber K →+* C)
    (ha : a.Flat) (c : C) (hc : a DualNumber.eps * c = 0) :
    c ∈ Ideal.span {a DualNumber.eps} := by
  rw [Ideal.mem_span_singleton]
  exact exists_eq_eps_mul_of_flat_of_eps_mul_eq_zero a ha c hc
end GlobalTheory.EpsIso
