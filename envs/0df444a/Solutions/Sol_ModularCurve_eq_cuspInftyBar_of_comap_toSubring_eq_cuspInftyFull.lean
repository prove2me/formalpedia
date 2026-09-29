-- Prove2me | solution 1 for ModularCurve.eq_cuspInftyBar_of_comap_toSubring_eq_cuspInftyFull
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/b611f70a-6d23-5784-bea0-3bbc82c91fc2

import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_JacJ1Iface
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eq_cuspInftyBar_of_comap_toSubring_eq_cuspInftyFull

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve AlgebraicCurve IsLocalRing CuspForm

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

namespace RPUAux

theorem valuationSubring_eq_of_le_of_ne_top {K : Type*} [Field K] (R S : ValuationSubring K)
    [IsPrincipalIdealRing R] (hR : R ≠ ⊤) (h : R ≤ S) (hS : S ≠ ⊤) : S = R := by
  have key := ValuationSubring.ofPrime_idealOfLE R S h
  haveI : (ValuationSubring.idealOfLE R S h).IsPrime := ValuationSubring.prime_idealOfLE R S h
  have congrP : ∀ (P Q : Ideal R) [P.IsPrime] [Q.IsPrime], P = Q → R.ofPrime P = R.ofPrime Q := by
    rintro P Q _ _ rfl; rfl
  by_cases hbot : ValuationSubring.idealOfLE R S h = ⊥
  · exfalso
    apply hS
    rw [← key, congrP _ ⊥ hbot, ValuationSubring.ofPrime_bot]
  ·
    have hmax : (ValuationSubring.idealOfLE R S h).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hbot
    have hPm : ValuationSubring.idealOfLE R S h = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hmax
    rw [← key, congrP _ _ hPm, ValuationSubring.ofPrime_top]

section Descent

variable (L : Type*) [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

theorem order_nonneg_of_forall_coeff_eq_zero {R : Type*} [Zero R] (x : LaurentSeries R)
    (h : ∀ n : ℤ, n < 0 → x.coeff n = 0) : 0 ≤ x.order := by
  by_cases hx : x = 0
  · simp [hx]
  · by_contra hlt
    push_neg at hlt
    exact hx (HahnSeries.coeff_order_eq_zero.mp (h _ hlt))

theorem mem_of_order_nonneg (S : Subring (laurentBaseChange L F₀))
    (hS1 : ∀ c : L, algebraMap L (laurentBaseChange L F₀) c ∈ S)
    (hS2 : ∀ f : F₀, 0 ≤ (f : LaurentSeries ℚ).order → baseChangeEquiv L F₀ ((1 : L) ⊗ₜ[ℚ] f) ∈ S)
    (z : laurentBaseChange L F₀) (hz : 0 ≤ (z : LaurentSeries L).order) : z ∈ S := by
  classical

  let b := Module.Free.chooseBasis ℚ L
  let e : L ⊗[ℚ] F₀ ≃ₗ[ℚ] (Module.Free.ChooseBasisIndex ℚ L →₀ F₀) :=
    (TensorProduct.congr b.repr (LinearEquiv.refl ℚ F₀)).trans (TensorProduct.finsuppScalarLeft ℚ F₀ _)
  have he : ∀ (i) (f : F₀), e.symm (Finsupp.single i f) = b i ⊗ₜ f := by
    intro i f
    simp only [e, LinearEquiv.trans_symm, LinearEquiv.trans_apply, TensorProduct.finsuppScalarLeft_symm_apply_single,
      TensorProduct.congr_symm_tmul, LinearEquiv.refl_symm, LinearEquiv.refl_apply, Module.Basis.repr_symm_single, one_smul]
  set x := (baseChangeEquiv L F₀).symm z with hx
  set g := e x with hg

  have hxsum : x = ∑ i ∈ g.support, b i ⊗ₜ[ℚ] g i := by
    calc x = e.symm g := by rw [hg, LinearEquiv.symm_apply_apply]
      _ = e.symm (∑ i ∈ g.support, Finsupp.single i (g i)) := by conv_lhs => rw [← Finsupp.sum_single g]
                                                                 rfl
      _ = ∑ i ∈ g.support, e.symm (Finsupp.single i (g i)) := map_sum _ _ _
      _ = _ := by simp only [he]

  have hzsum : z = ∑ i ∈ g.support, algebraMap L (laurentBaseChange L F₀) (b i) *
      baseChangeEquiv L F₀ ((1 : L) ⊗ₜ[ℚ] g i) := by
    calc z = baseChangeEquiv L F₀ x := by rw [hx, AlgEquiv.apply_symm_apply]
      _ = ∑ i ∈ g.support, baseChangeEquiv L F₀ (b i ⊗ₜ[ℚ] g i) := by rw [hxsum, map_sum]
      _ = _ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [baseChangeEquiv_tmul, baseChangeEquiv_one_tmul]

  have hcoeff : ∀ n : ℤ, (z : LaurentSeries L).coeff n = ∑ i ∈ g.support, ((g i : F₀) : LaurentSeries ℚ).coeff n • b i := by
    intro n
    have : ((z : laurentBaseChange L F₀) : LaurentSeries L) =
        ∑ i ∈ g.support, algebraMap L (LaurentSeries L) (b i) * coeffEmb L ((g i : F₀) : LaurentSeries ℚ) := by
      conv_lhs => rw [hzsum]
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MulMemClass.coe_mul, baseChangeEquiv_one_tmul]
      rfl
    rw [this, HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show algebraMap L (LaurentSeries L) (b i) = HahnSeries.ofPowerSeries ℤ L (PowerSeries.C (b i)) from rfl,
      HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, coeffEmb_coeff, smul_eq_mul,
      Algebra.smul_def, mul_comm]

  have hneg : ∀ i ∈ g.support, ∀ n : ℤ, n < 0 → ((g i : F₀) : LaurentSeries ℚ).coeff n = 0 := by
    intro i hi n hn
    have h0 : ∑ j ∈ g.support, ((g j : F₀) : LaurentSeries ℚ).coeff n • b j = 0 := by
      rw [← hcoeff]
      exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hn hz)
    exact linearIndependent_iff'.mp b.linearIndependent g.support (fun j => ((g j : F₀) : LaurentSeries ℚ).coeff n) h0 i hi

  rw [hzsum]
  refine Subring.sum_mem _ fun i hi => Subring.mul_mem _ (hS1 _) (hS2 _ ?_)
  exact order_nonneg_of_forall_coeff_eq_zero _ (hneg i hi)

end Descent

end RPUAux

theorem solution
    (N : ℕ) [NeZero N] (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hw : w.toValuationSubring.toSubring.comap
        ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
            (B := ↥(modularFunctionFieldFull N))).toRingHom) =
      (cuspInftyFull N).toValuationSubring.toSubring) :
    w = cuspInftyBar N := by
  classical
  apply Place.ext
  rw [cuspInftyBar_toValuationSubring]
  haveI : IsPrincipalIdealRing (qIntegersBar (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :=
    (cuspInftyBar N).isPrincipalIdealRing'
  refine RPUAux.valuationSubring_eq_of_le_of_ne_top _ _ (cuspInftyBar N).ne_top' ?_ w.ne_top'
  intro z hz
  rw [mem_qIntegersBar_iff] at hz
  exact RPUAux.mem_of_order_nonneg (AlgebraicClosure ℚ) (modularFunctionFieldFull N) w.toValuationSubring.toSubring
    (fun c => w.algebraMap_mem' c)
    (fun f hf => by
      have hmem : f ∈ (cuspInftyFull N).toValuationSubring.toSubring := by
        show f ∈ (cuspInftyFull N).toValuationSubring
        rw [cuspInftyFull_toValuationSubring, mem_qIntegersBar_iff]
        exact hf
      rw [← hw] at hmem
      exact hmem)
    z hz

#print axioms solution

end S_ModularCurve_eq_cuspInftyBar_of_comap_toSubring_eq_cuspInftyFull
end P2MW
export P2MW.S_ModularCurve_eq_cuspInftyBar_of_comap_toSubring_eq_cuspInftyFull (solution)
