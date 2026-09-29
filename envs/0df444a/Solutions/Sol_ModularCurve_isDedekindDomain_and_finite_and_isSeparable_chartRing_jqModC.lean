-- Prove2me | solution 1 for ModularCurve.isDedekindDomain_and_finite_and_isSeparable_chartRing_jqModC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/7fe7787d-3ab2-5b16-99ba-2f3683f36e3e

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_JacJ1_ChartAlgebra
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_isSeparable_and_finrank_adjoin_aeval_jqModC_modularFunctionFieldFullC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isDedekindDomain_and_finite_and_isSeparable_chartRing_jqModC
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

open Polynomial ModularCurve AlgebraicCurve
open scoped IntermediateField.algebraAdjoinAdjoin

namespace AVI

variable (K : Type) [Field K] {F : Type} [Field F] [Algebra K F] (jb : F) (ht : Transcendental K jb)

theorem gen_mem : jb ∈ CurveModel.chartRing K ({jb} : Set F) :=
  CurveModel.adjoin_le_chartRing K _ (Algebra.self_mem_adjoin_singleton K _)

@[reducible] def genB : ↥(CurveModel.chartRing K ({jb} : Set F)) := ⟨jb, gen_mem K jb⟩

@[reducible] noncomputable def algKX : Algebra K[X] ↥(CurveModel.chartRing K ({jb} : Set F)) :=
  (Polynomial.aeval (R := K) (genB K jb)).toRingHom.toAlgebra

noncomputable def toAdjoin : K[X] →ₐ[K] ↥(Algebra.adjoin K ({jb} : Set F)) :=
  (Polynomial.aeval jb).codRestrict (Algebra.adjoin K ({jb} : Set F)) (fun f => Polynomial.aeval_mem_adjoin_singleton K jb)

theorem toAdjoin_surjective : Function.Surjective (toAdjoin K jb) := by
  rintro ⟨x, hx⟩
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  obtain ⟨f, rfl⟩ := hx
  exact ⟨f, rfl⟩

include ht in
theorem toAdjoin_injective : Function.Injective (toAdjoin K jb) := by
  intro f g h
  apply (transcendental_iff_injective.mp ht)
  have := congrArg (fun x : ↥(Algebra.adjoin K ({jb} : Set F)) => (x : F)) h
  exact this

include ht in
theorem isPrincipalIdealRing_adjoin : IsPrincipalIdealRing ↥(Algebra.adjoin K ({jb} : Set F)) :=
  IsPrincipalIdealRing.of_surjective (toAdjoin K jb) (toAdjoin_surjective K jb)

include ht in
theorem isDedekindDomain_adjoin : IsDedekindDomain ↥(Algebra.adjoin K ({jb} : Set F)) := by
  haveI := isPrincipalIdealRing_adjoin K jb ht
  infer_instance

section Main

variable [FiniteDimensional ↥(IntermediateField.adjoin K ({jb} : Set F)) F]
  [Algebra.IsSeparable ↥(IntermediateField.adjoin K ({jb} : Set F)) F]

include ht in

theorem isDedekindDomain_chartRing : IsDedekindDomain ↥(CurveModel.chartRing K ({jb} : Set F)) := by
  haveI := isDedekindDomain_adjoin K jb ht
  exact IsIntegralClosure.isDedekindDomain ↥(Algebra.adjoin K ({jb} : Set F))
    ↥(IntermediateField.adjoin K ({jb} : Set F)) F _

include ht in
theorem finite_adjoin_chartRing : Module.Finite ↥(Algebra.adjoin K ({jb} : Set F)) ↥(CurveModel.chartRing K ({jb} : Set F)) := by
  haveI := isDedekindDomain_adjoin K jb ht
  exact IsIntegralClosure.finite ↥(Algebra.adjoin K ({jb} : Set F))
    ↥(IntermediateField.adjoin K ({jb} : Set F)) F _

include ht in
theorem isFractionRing_chartRing : IsFractionRing ↥(CurveModel.chartRing K ({jb} : Set F)) F := by
  haveI := isDedekindDomain_adjoin K jb ht
  exact IsIntegralClosure.isFractionRing_of_finite_extension ↥(Algebra.adjoin K ({jb} : Set F))
    ↥(IntermediateField.adjoin K ({jb} : Set F)) F _

end Main

section OverKX

variable [FiniteDimensional ↥(IntermediateField.adjoin K ({jb} : Set F)) F]
  [Algebra.IsSeparable ↥(IntermediateField.adjoin K ({jb} : Set F)) F]

theorem algebraMap_algKX_eq (f : K[X]) :
    letI := algKX K jb
    algebraMap K[X] ↥(CurveModel.chartRing K ({jb} : Set F)) f
      = algebraMap ↥(Algebra.adjoin K ({jb} : Set F)) ↥(CurveModel.chartRing K ({jb} : Set F)) (toAdjoin K jb f) := by
  letI := algKX K jb
  apply Subtype.ext
  show (CurveModel.chartRing K ({jb} : Set F)).val (Polynomial.aeval (R := K) (genB K jb) f) = Polynomial.aeval jb f
  rw [← Polynomial.aeval_algHom_apply]
  rfl

include ht in
theorem finite_KX_chartRing :
    letI := algKX K jb
    Module.Finite K[X] ↥(CurveModel.chartRing K ({jb} : Set F)) := by
  letI := algKX K jb
  letI : Algebra K[X] ↥(Algebra.adjoin K ({jb} : Set F)) := (toAdjoin K jb).toRingHom.toAlgebra
  haveI : IsScalarTower K[X] ↥(Algebra.adjoin K ({jb} : Set F)) ↥(CurveModel.chartRing K ({jb} : Set F)) :=
    IsScalarTower.of_algebraMap_eq fun f => algebraMap_algKX_eq K jb f
  haveI : Module.Finite K[X] ↥(Algebra.adjoin K ({jb} : Set F)) :=
    Module.Finite.of_surjective (Algebra.linearMap K[X] ↥(Algebra.adjoin K ({jb} : Set F))) (toAdjoin_surjective K jb)
  haveI := finite_adjoin_chartRing K jb ht
  exact Module.Finite.trans ↥(Algebra.adjoin K ({jb} : Set F)) _

include ht in
theorem algebraMap_algKX_injective :
    letI := algKX K jb
    Function.Injective (algebraMap K[X] ↥(CurveModel.chartRing K ({jb} : Set F))) := by
  letI := algKX K jb
  intro f g h
  apply toAdjoin_injective K jb ht
  rw [algebraMap_algKX_eq, algebraMap_algKX_eq] at h
  exact Subalgebra.inclusion_injective _ h

include ht in
theorem noZeroSMulDivisors_KX_chartRing :
    letI := algKX K jb
    NoZeroSMulDivisors K[X] ↥(CurveModel.chartRing K ({jb} : Set F)) := by
  letI := algKX K jb
  refine ⟨fun {c x} h => ?_⟩
  rw [Algebra.smul_def, mul_eq_zero] at h
  rcases h with h | h
  · left
    exact algebraMap_algKX_injective K jb ht (by rw [h, map_zero])
  · right; exact h

include ht in

theorem isSeparable_fractionRing :
    letI := algKX K jb
    ∀ [FaithfulSMul K[X] ↥(CurveModel.chartRing K ({jb} : Set F))],
      Algebra.IsSeparable (FractionRing K[X]) (FractionRing ↥(CurveModel.chartRing K ({jb} : Set F))) := by
  letI := algKX K jb
  intro _
  haveI := isFractionRing_chartRing K jb ht

  let e₁ : ↥(IntermediateField.adjoin K ({jb} : Set F)) ≃+* FractionRing K[X] :=
    (RatFunc.algEquivOfTranscendental jb ht).symm.toRingEquiv.trans
      (IsLocalization.algEquiv (nonZeroDivisors K[X]) (RatFunc K) (FractionRing K[X])).toRingEquiv
  let e₂ : F ≃+* FractionRing ↥(CurveModel.chartRing K ({jb} : Set F)) :=
    (IsLocalization.algEquiv (nonZeroDivisors ↥(CurveModel.chartRing K ({jb} : Set F))) F
      (FractionRing ↥(CurveModel.chartRing K ({jb} : Set F)))).toRingEquiv
  refine Algebra.IsSeparable.of_equiv_equiv e₁ e₂ ?_

  have key : ∀ f : K[X],
      (algebraMap (FractionRing K[X]) (FractionRing ↥(CurveModel.chartRing K ({jb} : Set F))))
          (e₁ (RatFunc.algEquivOfTranscendental jb ht (algebraMap K[X] (RatFunc K) f)))
        = e₂ (algebraMap ↥(IntermediateField.adjoin K ({jb} : Set F)) F
            (RatFunc.algEquivOfTranscendental jb ht (algebraMap K[X] (RatFunc K) f))) := by
    intro f

    have hl : e₁ (RatFunc.algEquivOfTranscendental jb ht (algebraMap K[X] (RatFunc K) f))
        = algebraMap K[X] (FractionRing K[X]) f := by
      show (IsLocalization.algEquiv (nonZeroDivisors K[X]) (RatFunc K) (FractionRing K[X]))
          ((RatFunc.algEquivOfTranscendental jb ht).symm (RatFunc.algEquivOfTranscendental jb ht (algebraMap K[X] (RatFunc K) f))) = _
      rw [AlgEquiv.symm_apply_apply, AlgEquiv.commutes]
    rw [hl, ← IsScalarTower.algebraMap_apply K[X] (FractionRing K[X]) (FractionRing ↥(CurveModel.chartRing K ({jb} : Set F))),
      IsScalarTower.algebraMap_apply K[X] ↥(CurveModel.chartRing K ({jb} : Set F)) (FractionRing ↥(CurveModel.chartRing K ({jb} : Set F)))]

    rw [RatFunc.algEquivOfTranscendental_algebraMap]
    have hr : algebraMap ↥(IntermediateField.adjoin K ({jb} : Set F)) F
        (Polynomial.aeval (IntermediateField.AdjoinSimple.gen K jb) f) = Polynomial.aeval jb f := by
      rw [← Polynomial.aeval_algebraMap_apply, IntermediateField.AdjoinSimple.algebraMap_gen]
    rw [hr]
    have hB : Polynomial.aeval jb f
        = algebraMap ↥(CurveModel.chartRing K ({jb} : Set F)) F (algebraMap K[X] ↥(CurveModel.chartRing K ({jb} : Set F)) f) := by
      rw [algebraMap_algKX_eq]; rfl
    rw [hB]
    exact (AlgEquiv.commutes _ _).symm

  have hcomp : ((algebraMap (FractionRing K[X]) (FractionRing ↥(CurveModel.chartRing K ({jb} : Set F)))).comp
        (e₁.toRingHom.comp (RatFunc.algEquivOfTranscendental jb ht).toAlgHom.toRingHom))
      = (e₂.toRingHom.comp (algebraMap ↥(IntermediateField.adjoin K ({jb} : Set F)) F)).comp
          (RatFunc.algEquivOfTranscendental jb ht).toAlgHom.toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors K[X])
    exact RingHom.ext fun f => key f
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := (RatFunc.algEquivOfTranscendental jb ht).surjective x
  exact RingHom.congr_fun hcomp y

end OverKX

end AVI

open scoped IntermediateField.algebraAdjoinAdjoin in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p ℓ : ℕ) [Fact p.Prime] [NeZero p] [Fact ℓ.Prime] (hℓ : ℓ ≠ p)
    (K : Type) [Field K] [CharP K ℓ] [IsAlgClosed K] :
    letI : Algebra K[X] ↥(CurveModel.chartRing K ({⟨jqModC K, jqModC_mem_full K p⟩} : Set ↥(modularFunctionFieldFullC K p))) :=
      (Polynomial.aeval (R := K)
        (⟨⟨jqModC K, jqModC_mem_full K p⟩,
          CurveModel.adjoin_le_chartRing K _ (Algebra.self_mem_adjoin_singleton K _)⟩ : ↥(CurveModel.chartRing K ({⟨jqModC K, jqModC_mem_full K p⟩} : Set ↥(modularFunctionFieldFullC K p))))).toRingHom.toAlgebra
    IsDedekindDomain ↥(CurveModel.chartRing K ({⟨jqModC K, jqModC_mem_full K p⟩} : Set ↥(modularFunctionFieldFullC K p))) ∧
    Module.Finite K[X] ↥(CurveModel.chartRing K ({⟨jqModC K, jqModC_mem_full K p⟩} : Set ↥(modularFunctionFieldFullC K p))) ∧
    NoZeroSMulDivisors K[X] ↥(CurveModel.chartRing K ({⟨jqModC K, jqModC_mem_full K p⟩} : Set ↥(modularFunctionFieldFullC K p))) ∧
    (∀ [FaithfulSMul K[X] ↥(CurveModel.chartRing K ({⟨jqModC K, jqModC_mem_full K p⟩} : Set ↥(modularFunctionFieldFullC K p)))],
      Algebra.IsSeparable (FractionRing K[X]) (FractionRing ↥(CurveModel.chartRing K ({⟨jqModC K, jqModC_mem_full K p⟩} : Set ↥(modularFunctionFieldFullC K p))))) := by

  have hp : p.Prime := Fact.out
  have hl : ℓ.Prime := Fact.out
  have hN : (p : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K ℓ p] at h
    exact hℓ ((Nat.prime_dvd_prime_iff_eq hl hp).mp h)
  have ht : Transcendental K (⟨jqModC K, jqModC_mem_full K p⟩ : ↥(modularFunctionFieldFullC K p)) := by
    intro halg
    apply transcendental_jqModC K
    exact (isAlgebraic_algHom_iff (modularFunctionFieldFullC K p).val Subtype.val_injective).mpr halg

  obtain ⟨hsep, hrk⟩ := isSeparable_and_finrank_adjoin_aeval_jqModC_modularFunctionFieldFullC K p hN X
    (by rw [derivative_X]; exact one_ne_zero)
  rw [Polynomial.aeval_X] at hsep hrk
  haveI := hsep
  haveI : FiniteDimensional ↥(IntermediateField.adjoin K ({(⟨jqModC K, jqModC_mem_full K p⟩ : ↥(modularFunctionFieldFullC K p))} :
      Set ↥(modularFunctionFieldFullC K p))) ↥(modularFunctionFieldFullC K p) := by
    apply Module.finite_of_finrank_pos
    rw [hrk, natDegree_X, one_mul]
    have h1 : 1 ∈ p.divisors.filter Squarefree := by
      rw [Finset.mem_filter]; exact ⟨Nat.one_mem_divisors.mpr hp.ne_zero, squarefree_one⟩
    have := Finset.single_le_sum (f := fun d => p / d) (fun _ _ => Nat.zero_le _) h1
    simp only [Nat.div_one] at this
    exact lt_of_lt_of_le hp.pos this
  exact ⟨AVI.isDedekindDomain_chartRing K _ ht, AVI.finite_KX_chartRing K _ ht, AVI.noZeroSMulDivisors_KX_chartRing K _ ht,
    by intro _; exact AVI.isSeparable_fractionRing K _ ht⟩

end S_ModularCurve_isDedekindDomain_and_finite_and_isSeparable_chartRing_jqModC
end P2MW
export P2MW.S_ModularCurve_isDedekindDomain_and_finite_and_isSeparable_chartRing_jqModC (solution)
