-- Prove2me | solution 1 for ModularCurve.HpoolLevelRing.finrank_rat_tensorProduct_quotient_span_aeval_jChartFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/86a6e6ae-3dc9-597c-9298-4beae09cd987

import Mathlib
import Definitions.Def_ModularCurve_HpoolLevelRing
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_tensor_chartAlg
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_IntermediateField_exists_algEquiv_adjoin_simple_ratFunc_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval_jChartFin
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

p2m_open "Polynomial ModularCurve~dedekindPsi_prime P2MW.S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval_jChartFin.ModularCurve ModularCurve.HpoolLevelRing P2MW.S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval_jChartFin.ModularCurve.HpoolLevelRing"
open scoped TensorProduct

namespace ModularCurve
p2m_export "ModularCurve" "dedekindPsi modularFunctionFieldFull IgusaScheme.jFull IgusaScheme modularFunctionFieldFullC modularFunctionFieldFullC_rat jqModC_mem_full jqModC finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi transcendental_jqModC"
namespace HpoolLevelRing
p2m_export "ModularCurve.HpoolLevelRing" "Afin levelRing"
namespace JChartFinRankAux
p2m_open "ModularCurve.HpoolLevelRing ModularCurve~dedekindPsi_prime"

open AlgebraicCurve.TwoChartIntegralModel

variable (p : ℕ) [Fact p.Prime] [NeZero p]

abbrev FF : Type := ↥(modularFunctionFieldFull p)

noncomputable abbrev jF : FF p := IgusaScheme.jFull p

abbrev Bq : Type := ↥(chartAlg ℚ (FF p) {jF p})

noncomputable abbrev jA : Afin p := jChartFin ℤ (FF p) (jF p)

noncomputable abbrev jB : Bq p := jChartFin ℚ (FF p) (jF p)

noncomputable abbrev Kj : IntermediateField ℚ (FF p) := IntermediateField.adjoin ℚ ({jF p} : Set (FF p))

noncomputable abbrev jK : ↥(Kj p) := ⟨jF p, IntermediateField.mem_adjoin_simple_self ℚ (jF p)⟩

theorem transcendental_jF : Transcendental ℚ (jF p) := by
  intro halg
  obtain ⟨f, hf, hev⟩ := halg
  refine ModularCurve.transcendental_jqModC ℚ ⟨f, hf, ?_⟩
  have h0 : (algebraMap (FF p) (LaurentSeries ℚ)) (Polynomial.aeval (jF p) f) = 0 := by
    rw [hev]; exact map_zero _
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂] at h0
  rw [Polynomial.aeval_def]
  convert h0 using 2 <;> first | rfl | exact Subsingleton.elim _ _

omit [Fact p.Prime] [NeZero p] in
theorem dedekindPsi_prime (hp : p.Prime) : dedekindPsi p = p + 1 := by
  unfold dedekindPsi
  rw [hp.divisors]
  have h1p : (1 : ℕ) ≠ p := hp.one_lt.ne
  rw [Finset.filter_true_of_mem (by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact squarefree_one
    · exact hp.prime.squarefree)]
  rw [Finset.sum_pair h1p, Nat.div_one, Nat.div_self hp.pos, add_comm]

omit [Fact p.Prime] in

theorem finrank_key (K : Type) [Field K] [CharZero K]
    (X : IntermediateField K (LaurentSeries K)) (hX : X = modularFunctionFieldFullC K p)
    (y : ↥X) (hy : (y : LaurentSeries K) = jqModC K) :
    Module.finrank ↥(IntermediateField.adjoin K ({y} : Set ↥X)) ↥X = dedekindPsi p := by
  subst hX
  obtain rfl : y = ⟨jqModC K, jqModC_mem_full K p⟩ := Subtype.ext hy
  exact finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K p (by exact_mod_cast (NeZero.ne p))

theorem finrank_Kj : Module.finrank ↥(Kj p) (FF p) = p + 1 := by
  rw [← dedekindPsi_prime p Fact.out]
  convert finrank_key p ℚ (modularFunctionFieldFull p) (modularFunctionFieldFullC_rat p).symm (jF p) rfl <;>
    exact Subsingleton.elim _ _

scoped instance finiteDimensional_Kj : FiniteDimensional ↥(Kj p) (FF p) :=
  Module.finite_of_finrank_pos (by rw [finrank_Kj]; omega)

example : Algebra.IsSeparable ↥(Kj p) (FF p) := inferInstance

@[reducible] noncomputable def algQXB : Algebra ℚ[X] (Bq p) := (Polynomial.aeval (jB p)).toRingHom.toAlgebra

@[reducible] noncomputable def algQXF : Algebra ℚ[X] (FF p) := (Polynomial.aeval (jF p)).toRingHom.toAlgebra

@[reducible] noncomputable def algQXK : Algebra ℚ[X] ↥(Kj p) := (Polynomial.aeval (jK p)).toRingHom.toAlgebra

attribute [local instance] algQXB algQXF algQXK

theorem algebraMap_QXB (f : ℚ[X]) : algebraMap ℚ[X] (Bq p) f = aeval (jB p) f := rfl
theorem algebraMap_QXF (f : ℚ[X]) : algebraMap ℚ[X] (FF p) f = aeval (jF p) f := rfl
theorem algebraMap_QXK (f : ℚ[X]) : algebraMap ℚ[X] ↥(Kj p) f = aeval (jK p) f := rfl

scoped instance tower_QXBF : IsScalarTower ℚ[X] (Bq p) (FF p) := by
  refine IsScalarTower.of_algebraMap_eq fun f => ?_
  rw [algebraMap_QXB, algebraMap_QXF]
  change aeval (jF p) f = (chartAlg ℚ (FF p) {jF p}).val (aeval (jB p) f)
  rw [← aeval_algHom_apply]
  rfl

scoped instance tower_QXKF : IsScalarTower ℚ[X] ↥(Kj p) (FF p) := by
  refine IsScalarTower.of_algebraMap_eq fun f => ?_
  rw [algebraMap_QXK, algebraMap_QXF]
  change aeval (jF p) f = (Kj p).val (aeval (jK p) f)
  rw [← aeval_algHom_apply]
  rfl

scoped instance tower_QQXB : IsScalarTower ℚ ℚ[X] (Bq p) :=
  IsScalarTower.of_algebraMap_eq fun q => by
    rw [algebraMap_QXB, Polynomial.algebraMap_apply, aeval_C]
    rfl

scoped instance tower_QQXK : IsScalarTower ℚ ℚ[X] ↥(Kj p) :=
  IsScalarTower.of_algebraMap_eq fun q => by
    rw [algebraMap_QXK, Polynomial.algebraMap_apply, aeval_C]
    rfl

scoped instance tower_QQXF : IsScalarTower ℚ ℚ[X] (FF p) :=
  IsScalarTower.of_algebraMap_eq fun q => by
    rw [algebraMap_QXF, Polynomial.algebraMap_apply, aeval_C]
    rfl

theorem algebraMap_QXF_injective : Function.Injective (algebraMap ℚ[X] (FF p)) :=
  transcendental_iff_injective.mp (transcendental_jF p)

theorem algebraMap_QXB_injective : Function.Injective (algebraMap ℚ[X] (Bq p)) := fun f g h => by
  apply algebraMap_QXF_injective p
  rw [IsScalarTower.algebraMap_apply ℚ[X] (Bq p) (FF p), h, ← IsScalarTower.algebraMap_apply]

theorem algebraMap_QXK_injective : Function.Injective (algebraMap ℚ[X] ↥(Kj p)) := fun f g h => by
  apply algebraMap_QXF_injective p
  rw [IsScalarTower.algebraMap_apply ℚ[X] ↥(Kj p) (FF p), h, ← IsScalarTower.algebraMap_apply]

scoped instance : Module.IsTorsionFree ℚ[X] (FF p) where
  isSMulRegular r hr := by
    intro x y hxy
    have hr0 : algebraMap ℚ[X] (FF p) r ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap_QXF_injective p)).mpr hr.ne_zero
    simp only [Algebra.smul_def] at hxy
    exact mul_left_cancel₀ hr0 hxy
scoped instance : Module.IsTorsionFree ℚ[X] (Bq p) where
  isSMulRegular r hr := by
    intro x y hxy
    have hr0 : algebraMap ℚ[X] (Bq p) r ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap_QXB_injective p)).mpr hr.ne_zero
    simp only [Algebra.smul_def] at hxy
    exact mul_left_cancel₀ hr0 hxy
scoped instance : FaithfulSMul ℚ[X] (Bq p) := (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap_QXB_injective p)

attribute [local instance 10000] RatFunc.instAlgebraOfPolynomial in

scoped instance isFractionRing_QXK : IsFractionRing ℚ[X] ↥(Kj p) := by
  obtain ⟨e, he⟩ := IntermediateField.exists_algEquiv_adjoin_simple_ratFunc_of_transcendental ℚ (FF p) (jF p)
    (transcendental_jF p)
  have halg : ∀ f : ℚ[X], algebraMap ℚ[X] (RatFunc ℚ) f = aeval RatFunc.X f := fun f => by
    have h1 := aeval_algHom_apply (IsScalarTower.toAlgHom ℚ ℚ[X] (RatFunc ℚ)) X f
    rw [aeval_X_left, AlgHom.coe_id, id_eq, IsScalarTower.coe_toAlgHom', RatFunc.algebraMap_X] at h1
    exact h1.symm
  have hcomm : ∀ f : ℚ[X], e.symm.toRingEquiv (algebraMap ℚ[X] (RatFunc ℚ) f) = algebraMap ℚ[X] ↥(Kj p) f := by
    intro f
    rw [algebraMap_QXK, halg, AlgEquiv.coe_ringEquiv, ← aeval_algHom_apply,
      ← he, AlgEquiv.symm_apply_apply]
  let e' : RatFunc ℚ ≃ₐ[ℚ[X]] ↥(Kj p) := AlgEquiv.ofRingEquiv (f := e.symm.toRingEquiv) hcomm
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors ℚ[X]) e'

noncomputable abbrev A0 : Subalgebra ℚ (FF p) := Algebra.adjoin ℚ ({jF p} : Set (FF p))

theorem aeval_mem_A0 (f : ℚ[X]) : aeval (jF p) f ∈ A0 p := by
  rw [A0, Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨f, rfl⟩

@[reducible] noncomputable def algQXA0 : Algebra ℚ[X] ↥(A0 p) :=
  ((Polynomial.aeval (jF p)).codRestrict (A0 p) (aeval_mem_A0 p)).toRingHom.toAlgebra

attribute [local instance] algQXA0

scoped instance tower_QXA0F : IsScalarTower ℚ[X] ↥(A0 p) (FF p) :=
  IsScalarTower.of_algebraMap_eq fun f => rfl

theorem algebraMap_QXA0_surjective : Function.Surjective (algebraMap ℚ[X] ↥(A0 p)) := by
  rintro ⟨a, ha⟩
  rw [A0, Algebra.adjoin_singleton_eq_range_aeval] at ha
  obtain ⟨f, rfl⟩ := ha
  exact ⟨f, rfl⟩

scoped instance : Algebra.IsIntegral ℚ[X] ↥(A0 p) :=
  ⟨fun a => by
    obtain ⟨f, rfl⟩ := algebraMap_QXA0_surjective p a
    exact isIntegral_algebraMap⟩

scoped instance isIntegralClosure_B : IsIntegralClosure (Bq p) ℚ[X] (FF p) where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff := fun {x} => by
    constructor
    · intro hx
      refine ⟨⟨x, (mem_chartAlg_iff ℚ (FF p)).mpr ?_⟩, rfl⟩
      exact hx.tower_top
    · rintro ⟨y, rfl⟩
      have hy : IsIntegral ↥(A0 p) (y : FF p) := (mem_chartAlg_iff ℚ (FF p)).mp y.2
      exact isIntegral_trans (y : FF p) hy

scoped instance : Module.Finite ℚ[X] (Bq p) := IsIntegralClosure.finite ℚ[X] ↥(Kj p) (FF p) (Bq p)
scoped instance : Module.Free ℚ[X] (Bq p) := inferInstance
scoped instance : IsDedekindDomain (Bq p) := IsIntegralClosure.isDedekindDomain ℚ[X] ↥(Kj p) (FF p) (Bq p)

theorem finrank_QXB : Module.finrank ℚ[X] (Bq p) = p + 1 := by
  rw [IsIntegralClosure.rank ℚ[X] ↥(Kj p) (FF p) (Bq p), finrank_Kj]

set_option maxHeartbeats 3200000 in
theorem finrank_quotient_B (g : ℚ[X]) (hg : g ≠ 0) :
    Module.finrank ℚ (Bq p ⧸ Ideal.span {algebraMap ℚ[X] (Bq p) g}) = (p + 1) * g.natDegree := by
  classical
  let b := Module.Free.chooseBasis ℚ[X] (Bq p)
  have h0 : algebraMap ℚ[X] (Bq p) g ≠ 0 := fun h =>
    hg (algebraMap_QXB_injective p (h.trans (map_zero _).symm))
  rw [finrank_quotient_span_eq_natDegree_norm b h0, Algebra.norm_algebraMap_of_basis b, natDegree_pow,
    ← Module.finrank_eq_card_basis b, finrank_QXB]

set_option maxHeartbeats 3200000 in
theorem R1 (g : ℤ[X]) (hg : g ≠ 0) :
    Module.finrank ℚ (ℚ ⊗[ℤ] Afin p ⧸
      Ideal.span {(1 : ℚ) ⊗ₜ[ℤ] Polynomial.aeval (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) g}) = (p + 1) * g.natDegree := by
  obtain ⟨e, he⟩ := AlgebraicCurve.TwoChartIntegralModel.exists_algEquiv_tensor_chartAlg ℤ ℚ (FF p)
    (nonZeroDivisors ℤ) ({jF p} : Set (FF p))
  have hex : e ((1 : ℚ) ⊗ₜ[ℤ] Polynomial.aeval (jA p) g) = algebraMap ℚ[X] (Bq p) (g.map (Int.castRingHom ℚ)) := by
    apply Subtype.ext
    rw [he, one_smul, algebraMap_QXB]
    change ((chartAlg ℤ (FF p) {jF p}).val (aeval (jA p) g) : FF p) =
      (chartAlg ℚ (FF p) {jF p}).val (aeval (jB p) (g.map (Int.castRingHom ℚ)))
    rw [← aeval_algHom_apply, ← aeval_algHom_apply, show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl,
      aeval_map_algebraMap]
    rfl
  have hI : Ideal.span {algebraMap ℚ[X] (Bq p) (g.map (Int.castRingHom ℚ))} =
      (Ideal.span {(1 : ℚ) ⊗ₜ[ℤ] Polynomial.aeval (jA p) g}).map (e : ℚ ⊗[ℤ] Afin p →+* Bq p) := by
    rw [Ideal.map_span, Set.image_singleton, RingHom.coe_coe, hex]
  rw [(Ideal.quotientEquivAlg _ _ e hI).toLinearEquiv.finrank_eq,
    finrank_quotient_B p _ ((Polynomial.map_ne_zero_iff (Int.castRingHom ℚ).injective_int).mpr hg),
    natDegree_map_eq_of_injective (Int.castRingHom ℚ).injective_int]

end ModularCurve.HpoolLevelRing.JChartFinRankAux
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval_jChartFin.ModularCurve P2MW.S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval_jChartFin.ModularCurve.HpoolLevelRing P2MW.S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval_jChartFin.ModularCurve.HpoolLevelRing.JChartFinRankAux"
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval_jChartFin.ModularCurve P2MW.S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval_jChartFin.ModularCurve.HpoolLevelRing"
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval_jChartFin.ModularCurve"

theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p] (g : ℤ[X]) (hg : g ≠ 0) :
    Module.finrank ℚ (ℚ ⊗[ℤ] Afin p ⧸
      Ideal.span {(1 : ℚ) ⊗ₜ[ℤ] Polynomial.aeval (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) g}) = (p + 1) * g.natDegree :=
  ModularCurve.HpoolLevelRing.JChartFinRankAux.R1 p g hg

end S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval_jChartFin
end P2MW
export P2MW.S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval_jChartFin (solution)
