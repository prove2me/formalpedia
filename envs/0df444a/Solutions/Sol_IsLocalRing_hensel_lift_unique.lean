-- Prove2me | solution 1 for IsLocalRing.hensel_lift_unique
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/1a71ef63-860f-5807-97b2-dd42b8950ba0

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific
import Definitions.Def_AlgebraicCurve_PlaceCompletion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_hensel_lift_unique

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open Polynomial IsLocalRing

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 6400000

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero MonoidWithZeroHom

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext heightOneSpectrum ramificationIndex ramificationIndex_pos restrict adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_adicCompletionComapIntegers_coe kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_completionTrace kw_ffgc_completionTraceF'"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

section Bridge

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

theorem kw_ffgc_ramificationIndex_eq_one_of_comap_surjective
    (hsurj : Function.Surjective (kw_ffgc_adicCompletionComap F W)) :
    W.ramificationIndex F = 1 := by
  have hrpos := W.ramificationIndex_pos (F := F)
  obtain ⟨y, hy⟩ :=
    W.heightOneSpectrum.valuedAdicCompletion_surjective F' (exp (-1 : ℤ))
  obtain ⟨x, rfl⟩ := hsurj y
  rw [kw_ffgc_valued_adicCompletionComap F W x, ← zpow_natCast] at hy
  have hx0 : Valued.v x ≠ 0 := by
    intro h0; rw [h0, zero_zpow _ (Nat.cast_ne_zero.mpr hrpos.ne')] at hy
    exact exp_ne_zero hy.symm
  apply_fun WithZero.log at hy
  rw [log_zpow, log_exp] at hy
  have hdvd : (W.ramificationIndex F : ℤ) ∣ (1 : ℤ) := dvd_neg.mp ⟨_, hy.symm⟩
  exact Nat.dvd_one.mp (by exact_mod_cast hdvd)

end Bridge

end AlgebraicCurve.Place

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 6400000

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero MonoidWithZeroHom

section HenselUniqueness

variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem kw_ffgc_hensel_lift_unique_port {f : Polynomial R} {a b : R}
    (ha : f.IsRoot a) (hb : f.IsRoot b) (hmem : b - a ∈ maximalIdeal R)
    (hunit : IsUnit (f.derivative.eval a)) : a = b := by
  obtain ⟨k, hk⟩ := f.binomExpansion a (b - a)
  rw [add_sub_cancel, hb, ha, zero_add, sq, ← mul_assoc, ← add_mul] at hk

  have hbracket : IsUnit (f.derivative.eval a + k * (b - a)) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem'
    refine (IsLocalRing.notMem_maximalIdeal.mpr hunit) ?_
    have : f.derivative.eval a
        = (f.derivative.eval a + k * (b - a)) - k * (b - a) := by ring
    rw [this]
    exact Ideal.sub_mem _ hmem' (Ideal.mul_mem_left _ k hmem)
  exact (sub_eq_zero.mp ((hbracket.mul_right_eq_zero).mp hk.symm)).symm

end HenselUniqueness

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext heightOneSpectrum ramificationIndex ramificationIndex_pos restrict adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_adicCompletionComapIntegers_coe kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_completionTrace kw_ffgc_completionTraceF'"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

section IntegerComap

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

theorem kw_ffgc_adicCompletionComapIntegers_mem_maximalIdeal
    {x : (W.restrict F).adicCompletionIntegers}
    (hx : x ∈ maximalIdeal (W.restrict F).adicCompletionIntegers) :
    kw_ffgc_adicCompletionComapIntegers F W x ∈ maximalIdeal W.adicCompletionIntegers := by
  have hrpos := W.ramificationIndex_pos (F := F)
  rw [show maximalIdeal (W.restrict F).adicCompletionIntegers
      = (W.restrict F).heightOneSpectrum.completionIdeal F from rfl,
    HeightOneSpectrum.mem_completionIdeal_iff] at hx
  rw [show maximalIdeal W.adicCompletionIntegers
      = W.heightOneSpectrum.completionIdeal F' from rfl,
    HeightOneSpectrum.mem_completionIdeal_iff, kw_ffgc_adicCompletionComapIntegers_coe,
    kw_ffgc_valued_adicCompletionComap]
  calc Valued.v (x : (W.restrict F).adicCompletion) ^ W.ramificationIndex F
      < 1 ^ W.ramificationIndex F := pow_lt_pow_left₀ hx zero_le' hrpos.ne'
    _ = 1 := one_pow _

scoped instance kw_ffgc_isLocalHom_adicCompletionComapIntegers :
    IsLocalHom (kw_ffgc_adicCompletionComapIntegers F W) where
  map_nonunit x hx := by
    by_contra hnu
    exact (IsLocalRing.notMem_maximalIdeal.mpr hx)
      (kw_ffgc_adicCompletionComapIntegers_mem_maximalIdeal F W
        ((IsLocalRing.mem_maximalIdeal x).mpr hnu))

end IntegerComap

section ClosedRange

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end ClosedRange

end AlgebraicCurve.Place
p2m_reactivate "P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve.Place"
p2m_reactivate "P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 6400000

noncomputable section

open Polynomial IsLocalRing IsDedekindDomain

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext heightOneSpectrum ramificationIndex ramificationIndex_pos restrict adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_adicCompletionComapIntegers_coe kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_completionTrace kw_ffgc_completionTraceF'"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

section CompletionAlgebra

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

scoped instance kw_ffgc_isIntegrallyClosed_adicCompletionIntegers :
    IsIntegrallyClosed (W.restrict F).adicCompletionIntegers :=
  Valuation.Integers.isIntegrallyClosed
    (HeightOneSpectrum.adicCompletionIntegers.integers
      (K := F) (v := (W.restrict F).heightOneSpectrum))

theorem kw_ffgc_adicCompletionComapIntegers_injective :
    Function.Injective (kw_ffgc_adicCompletionComapIntegers F W) := by
  intro a b hab
  exact Subtype.ext ((kw_ffgc_adicCompletionComap F W).injective
    (congrArg Subtype.val hab))

scoped instance kw_ffgc_isTorsionFree_adicCompletionComapIntegers :
    Module.IsTorsionFree (W.restrict F).adicCompletionIntegers W.adicCompletionIntegers :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (kw_ffgc_adicCompletionComapIntegers_injective F W)

end CompletionAlgebra
p2m_reactivate "P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve.Place"

section IrreducibleValuation

open WithZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

theorem kw_ffgc_valued_coe_irreducible_adicCompletionIntegers
    {π : V.adicCompletionIntegers} (hπ : Irreducible π) :
    Valued.v (π : V.adicCompletion) = exp (-1 : ℤ) := by

  have hπm : Valued.v (π : V.adicCompletion) < 1 := by
    have h := (IsLocalRing.mem_maximalIdeal π).mpr hπ.not_isUnit
    rwa [show maximalIdeal V.adicCompletionIntegers
        = V.heightOneSpectrum.completionIdeal F from rfl,
      HeightOneSpectrum.mem_completionIdeal_iff] at h
  have hπ0 : Valued.v (π : V.adicCompletion) ≠ 0 := by
    simp only [ne_eq, map_eq_zero]
    exact fun h => hπ.ne_zero (Subtype.ext h)

  obtain ⟨y, hy⟩ :=
    V.heightOneSpectrum.valuedAdicCompletion_surjective F (exp (-1 : ℤ))
  have hy1 : Valued.v y < 1 := by
    rw [hy, show (1 : ℤᵐ⁰) = exp (0 : ℤ) from (exp_zero).symm, exp_lt_exp]; omega
  have hyint : y ∈ V.adicCompletionIntegers := hy1.le
  have hym : (⟨y, hyint⟩ : V.adicCompletionIntegers)
      ∈ maximalIdeal V.adicCompletionIntegers := by
    rw [show maximalIdeal V.adicCompletionIntegers
        = V.heightOneSpectrum.completionIdeal F from rfl,
      HeightOneSpectrum.mem_completionIdeal_iff]; exact hy1
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hym
  obtain ⟨k, hk⟩ := hym
  have hle : exp (-1 : ℤ) ≤ Valued.v (π : V.adicCompletion) := by
    have hkv : Valued.v (k : V.adicCompletion) ≤ 1 := k.2
    calc exp (-1 : ℤ)
        = Valued.v y := hy.symm
      _ = Valued.v (π : V.adicCompletion) * Valued.v (k : V.adicCompletion) := by
          rw [show y = (π : V.adicCompletion) * (k : V.adicCompletion) from
            congrArg Subtype.val hk, map_mul]
      _ ≤ Valued.v (π : V.adicCompletion) * 1 := by gcongr
      _ = Valued.v (π : V.adicCompletion) := mul_one _

  have h1 : log (Valued.v (π : V.adicCompletion)) < 0 := by
    have h := (log_lt_log hπ0 (one_ne_zero)).mpr hπm
    rwa [log_one] at h
  have h2 : -1 ≤ log (Valued.v (π : V.adicCompletion)) := by
    have h := (log_le_log exp_ne_zero hπ0).mpr hle
    rwa [log_exp] at h
  rw [← exp_log hπ0, show log (Valued.v (π : V.adicCompletion)) = -1 from by omega]

end IrreducibleValuation
p2m_reactivate "P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve.Place"

section SpectralSetup

open scoped Valued NNReal WithZero

open WithZeroMulInt Valuation.IsRankOneDiscrete

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

theorem kw_ffgc_norm_adicCompletion_eq (x : V.adicCompletion) :
    letI := kw_ffgc_rankOne_adicCompletion V
    ‖x‖ = (WithZeroMulInt.toNNReal (two_ne_zero) (Valued.v x) : ℝ) := by
  letI := kw_ffgc_rankOne_adicCompletion V
  have h := valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
    (V.heightOneSpectrum.valuedAdicCompletion_surjective F) x
  simp only [Valued.toNormedField.norm_def, Valuation.RankOne.hom]
  rw [← h]; rfl

end SpectralSetup
p2m_reactivate "P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve.Place"

section AbsoluteValue

open scoped Valued NNReal WithZero

open WithZeroMulInt Valuation.IsRankOneDiscrete

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

theorem kw_ffgc_absoluteValue_extends (c : (W.restrict F).adicCompletion) :
    letI := kw_ffgc_rankOne_adicCompletion (W.restrict F)
    kw_ffgc_absoluteValue F W
      (algebraMap (W.restrict F).adicCompletion W.adicCompletion c) = ‖c‖ := by
  letI := kw_ffgc_rankOne_adicCompletion (W.restrict F)
  letI := kw_ffgc_rankOne_adicCompletion W
  have hr : (0 : ℝ) < (W.ramificationIndex F : ℝ) :=
    Nat.cast_pos.mpr (W.ramificationIndex_pos (F := F))
  show ‖algebraMap (W.restrict F).adicCompletion W.adicCompletion c‖
      ^ ((W.ramificationIndex F : ℝ))⁻¹ = ‖c‖
  rw [kw_ffgc_norm_adicCompletion_eq W, kw_ffgc_norm_adicCompletion_eq (W.restrict F),
    kw_ffgc_algebraMap_adicCompletionComap_eq, kw_ffgc_valued_adicCompletionComap,
    map_pow, NNReal.coe_pow, ← Real.rpow_natCast, ← Real.rpow_mul (NNReal.coe_nonneg _),
    mul_inv_cancel₀ hr.ne', Real.rpow_one]

end AbsoluteValue
p2m_reactivate "P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve.Place"

section IntegralClosure

open scoped Valued NNReal WithZero

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

theorem kw_ffgc_isIntegral_adicCompletionIntegers_of_algebraic
    [Algebra.IsAlgebraic (W.restrict F).adicCompletion W.adicCompletion]
    (x : W.adicCompletionIntegers) :
    IsIntegral (W.restrict F).adicCompletionIntegers x := by
  letI := kw_ffgc_rankOne_adicCompletion (W.restrict F)
  letI := kw_ffgc_rankOne_adicCompletion W
  letI : NontriviallyNormedField (W.restrict F).adicCompletion :=
    Valued.toNontriviallyNormedField (W.restrict F).adicCompletion ℤᵐ⁰
  haveI : IsUltrametricDist (W.restrict F).adicCompletion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (fun a b => Valuation.norm_add_le Valued.v a b)
  have hr : (0 : ℝ) < ((W.ramificationIndex F : ℝ))⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (W.ramificationIndex_pos (F := F)))

  have hxn : ‖(x : W.adicCompletion)‖ ≤ 1 :=
    (Valued.toNormedField.norm_le_one_iff).mpr x.2

  have hsn : spectralNorm (W.restrict F).adicCompletion W.adicCompletion
        (x : W.adicCompletion)
      = ‖(x : W.adicCompletion)‖ ^ ((W.ramificationIndex F : ℝ))⁻¹ :=
    (spectralNorm_unique_field_norm_ext (f := kw_ffgc_absoluteValue F W)
      (kw_ffgc_absoluteValue_extends F W) (x : W.adicCompletion)).symm

  have hspec : spectralValue (minpoly (W.restrict F).adicCompletion
      (x : W.adicCompletion)) ≤ 1 := by
    show spectralNorm (W.restrict F).adicCompletion W.adicCompletion
      (x : W.adicCompletion) ≤ 1
    rw [hsn]; exact Real.rpow_le_one (norm_nonneg _) hxn hr.le
  have hmon : (minpoly (W.restrict F).adicCompletion (x : W.adicCompletion)).Monic :=
    minpoly.monic (Algebra.IsAlgebraic.isAlgebraic
      (R := (W.restrict F).adicCompletion) (x : W.adicCompletion)).isIntegral

  have hlift : minpoly (W.restrict F).adicCompletion (x : W.adicCompletion)
      ∈ Polynomial.lifts (algebraMap (W.restrict F).adicCompletionIntegers
          (W.restrict F).adicCompletion) := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, ?_⟩, rfl⟩
    exact (Valued.toNormedField.norm_le_one_iff).mp
      ((spectralValue_le_one_iff hmon).mp hspec n)
  obtain ⟨P, hP, -, hPmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmon

  have hxintW : IsIntegral (W.restrict F).adicCompletionIntegers (x : W.adicCompletion) := by
    refine ⟨P, hPmon, ?_⟩
    rw [← Polynomial.aeval_def,
      ← Polynomial.aeval_map_algebraMap (W.restrict F).adicCompletion, hP, minpoly.aeval]
  exact (isIntegral_algHom_iff
    (IsScalarTower.toAlgHom (W.restrict F).adicCompletionIntegers
      W.adicCompletionIntegers W.adicCompletion)
    Subtype.val_injective).mp hxintW

theorem kw_ffgc_isIntegralClosure_adicCompletionIntegers
    [Algebra.IsAlgebraic (W.restrict F).adicCompletion W.adicCompletion] :
    IsIntegralClosure W.adicCompletionIntegers (W.restrict F).adicCompletionIntegers
      W.adicCompletion where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := by
    constructor
    · intro hx
      have hxW : IsIntegral W.adicCompletionIntegers x := hx.tower_top
      haveI : IsIntegrallyClosed W.adicCompletionIntegers :=
        Valuation.Integers.isIntegrallyClosed
          (HeightOneSpectrum.adicCompletionIntegers.integers
            (K := F') (v := W.heightOneSpectrum))
      exact IsIntegrallyClosed.isIntegral_iff.mp hxW
    · rintro ⟨y, rfl⟩
      exact (kw_ffgc_isIntegral_adicCompletionIntegers_of_algebraic F W y).map
        (IsScalarTower.toAlgHom (W.restrict F).adicCompletionIntegers
          W.adicCompletionIntegers W.adicCompletion)

end IntegralClosure
p2m_reactivate "P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve.Place"

section ClosedAdjoin

open scoped Valued NNReal WithZero

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

theorem kw_ffgc_isClosed_intermediateField_of_finiteDimensional
    (E : IntermediateField (W.restrict F).adicCompletion W.adicCompletion)
    [FiniteDimensional (W.restrict F).adicCompletion E] :
    IsClosed (E : Set W.adicCompletion) := by
  letI := kw_ffgc_rankOne_adicCompletion (W.restrict F)
  letI : NontriviallyNormedField (W.restrict F).adicCompletion :=
    Valued.toNontriviallyNormedField (W.restrict F).adicCompletion ℤᵐ⁰
  exact E.toSubalgebra.toSubmodule.closed_of_finiteDimensional

theorem kw_ffgc_adjoin_adicCompletion_eq_top_of_denseSubset {ζ : W.adicCompletion}
    (hint : IsIntegral (W.restrict F).adicCompletion ζ)
    (hsubset : ∀ x : F', algebraMap F' W.adicCompletion x
      ∈ IntermediateField.adjoin (W.restrict F).adicCompletion {ζ}) :
    Algebra.adjoin (W.restrict F).adicCompletion {ζ} = ⊤ := by
  set E := IntermediateField.adjoin (W.restrict F).adicCompletion {ζ}
  haveI : FiniteDimensional (W.restrict F).adicCompletion E :=
    IntermediateField.adjoin.finiteDimensional hint
  have hclosed : IsClosed (E : Set W.adicCompletion) :=
    kw_ffgc_isClosed_intermediateField_of_finiteDimensional F W E
  have hdense : DenseRange (algebraMap F' W.adicCompletion) :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F' W.heightOneSpectrum
  have huniv : Set.univ ⊆ (E : Set W.adicCompletion) := by
    rw [← hdense.closure_range, ← hclosed.closure_eq]
    exact closure_mono (Set.range_subset_iff.mpr hsubset)
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    ← top_le_iff]
  exact fun y _ => huniv (Set.mem_univ y)

end ClosedAdjoin
p2m_reactivate "P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve.Place"

section Bridge

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

scoped instance kw_ffgc_faithfulSMul_adicCompletionComapIntegers :
    FaithfulSMul (W.restrict F).adicCompletionIntegers W.adicCompletionIntegers :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (kw_ffgc_adicCompletionComapIntegers_injective F W)

end Bridge
p2m_reactivate "P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve.Place"

end AlgebraicCurve.Place
p2m_reactivate "P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve.Place"
p2m_reactivate "P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve.Place"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 6400000

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero

open scoped Valued WithZero

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext heightOneSpectrum ramificationIndex ramificationIndex_pos restrict adicCompletion adicCompletionIntegers kw_ffgc_adicCompletionComap kw_ffgc_valued_adicCompletionComap kw_ffgc_adicCompletionComapIntegers kw_ffgc_adicCompletionComapIntegers_coe kw_ffgc_algebraMap_adicCompletionComap_eq kw_ffgc_rankOne_adicCompletion kw_ffgc_absoluteValue kw_ffgc_completionLinearCombination kw_ffgc_denseRange_completionLinearCombination kw_ffgc_completionTrace kw_ffgc_completionTraceF'"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

section FiniteDimensional

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

theorem kw_ffgc_finrank_adicCompletion_le [FiniteDimensional F F'] :
    Module.finrank (W.restrict F).adicCompletion W.adicCompletion ≤ Module.finrank F F' := by
  letI := kw_ffgc_rankOne_adicCompletion (W.restrict F)
  letI : NontriviallyNormedField (W.restrict F).adicCompletion :=
    Valued.toNontriviallyNormedField (W.restrict F).adicCompletion ℤᵐ⁰
  let b := Module.finBasis F F'
  have hsurj : Function.Surjective (kw_ffgc_completionLinearCombination F W b) := by
    rw [← Set.range_eq_univ, ← LinearMap.coe_range,
      ← (LinearMap.range
          (kw_ffgc_completionLinearCombination F W b)).closed_of_finiteDimensional.closure_eq]
    exact (kw_ffgc_denseRange_completionLinearCombination F W b).closure_range
  calc Module.finrank (W.restrict F).adicCompletion W.adicCompletion
      ≤ Module.finrank (W.restrict F).adicCompletion
          (Fin (Module.finrank F F') → (W.restrict F).adicCompletion) :=
        LinearMap.finrank_le_finrank_of_surjective
          (f := kw_ffgc_completionLinearCombination F W b) hsurj
    _ = Module.finrank F F' := by rw [Module.finrank_pi, Fintype.card_fin]

end FiniteDimensional
p2m_reactivate "P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve.Place"

section CompletionTrace

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

theorem kw_ffgc_completionTraceF'_apply [FiniteDimensional F F'] (g : F') :
    kw_ffgc_completionTraceF' F W g
      = Algebra.trace (W.restrict F).adicCompletion W.adicCompletion
          (algebraMap F' W.adicCompletion g) := rfl

theorem kw_ffgc_completionTrace_mem_integers [FiniteDimensional F F']
    [Algebra.IsSeparable (W.restrict F).adicCompletion W.adicCompletion]
    (x : W.adicCompletion) (hx : x ∈ W.adicCompletionIntegers) :
    kw_ffgc_completionTrace F W x ∈ (W.restrict F).adicCompletionIntegers := by
  haveI : Algebra.IsAlgebraic (W.restrict F).adicCompletion W.adicCompletion :=
    Algebra.IsAlgebraic.of_finite _ _
  have hint : IsIntegral (W.restrict F).adicCompletionIntegers x :=
    ((kw_ffgc_isIntegralClosure_adicCompletionIntegers F W).isIntegral_iff (x := x)).mpr
      ⟨⟨x, hx⟩, rfl⟩
  have htr : IsIntegral (W.restrict F).adicCompletionIntegers
      (Algebra.trace (W.restrict F).adicCompletion W.adicCompletion x) :=
    Algebra.isIntegral_trace hint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff
    (R := (W.restrict F).adicCompletionIntegers) |>.mp htr
  exact hy ▸ y.2

end CompletionTrace
p2m_reactivate "P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve.Place"

end AlgebraicCurve.Place
p2m_reactivate "P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve.Place"
p2m_reactivate "P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve.Place"

open _root_.AlgebraicCurve _root_.P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve _root_.AlgebraicCurve.Place _root_.P2MW.S_IsLocalRing_hensel_lift_unique.AlgebraicCurve.Place IsLocalRing WithZero in
theorem solution {R : Type*} [CommRing R] [IsLocalRing R] {f : Polynomial R} {a b : R}
    (ha : f.IsRoot a) (hb : f.IsRoot b) (hmem : b - a ∈ IsLocalRing.maximalIdeal R)
    (hunit : IsUnit (f.derivative.eval a)) : a = b :=
  kw_ffgc_hensel_lift_unique_port (R := R) (f := f) (a := a) (b := b) (ha := ha) (hb := hb) (hmem := hmem) (hunit := hunit)

end
end
end
end
end S_IsLocalRing_hensel_lift_unique
end P2MW
export P2MW.S_IsLocalRing_hensel_lift_unique (solution)
