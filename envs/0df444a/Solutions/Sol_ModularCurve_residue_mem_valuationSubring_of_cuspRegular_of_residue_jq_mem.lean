-- Prove2me | solution 1 for ModularCurve.residue_mem_valuationSubring_of_cuspRegular_of_residue_jq_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/6170c9e0-456c-55fa-8faa-13a2a2d5cae4

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
import Theorems.Thm_ModularCurve_CompEq_finrank_adjoin_jBar_eq_dedekindPsi
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_residue_mem_valuationSubring_of_cuspRegular_of_residue_jq_mem
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open AlgebraicCurve ModularCurve IsLocalRing

namespace CuspRedReg

local notation "Qb" => AlgebraicClosure ℚ

section Divisors

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem degree_eq_sum_of_deg_eq_one (hdeg : ∀ v : Place K F, v.deg = 1) (D : Divisor K F) :
    Divisor.degree D = D.sum fun _ n => n := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun v _ => ?_
  simp [hdeg v]

theorem eq_of_le_of_degree_eq (hdeg : ∀ v : Place K F, v.deg = 1) {D D' : Divisor K F} (hle : D ≤ D')
    (hdegD : Divisor.degree D = Divisor.degree D') : D = D' := by
  classical
  have hG0 : 0 ≤ D' - D := sub_nonneg.mpr hle
  have hGdeg : Divisor.degree (D' - D) = 0 := by rw [map_sub, hdegD, sub_self]
  rw [degree_eq_sum_of_deg_eq_one hdeg, Finsupp.sum] at hGdeg
  have hall : ∀ v ∈ (D' - D).support, (D' - D) v = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun v _ => hG0 v).mp hGdeg
  have hG : D' - D = 0 := by
    ext v
    by_cases hv : v ∈ (D' - D).support
    · exact hall v hv
    · exact Finsupp.notMem_support_iff.mp hv
  exact (sub_eq_zero.mp hG).symm

end Divisors

section Bar

variable (N : ℕ) [NeZero N]

abbrev jF : ↥(modularFunctionFieldBar N) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩

theorem coeffEmb_jq_eq_jqModC (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L jq = jqModC L :=
  map_jqModC (algebraMap ℚ L)

theorem jF_ne_zero : jF N ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : ↥(modularFunctionFieldBar N) => (z : LaurentSeries Qb).coeff (-1)) h
  simp only [ZeroMemClass.coe_zero, HahnSeries.coeff_zero] at h1
  rw [coeffEmb_coeff, coeff_jq_neg_one, map_one] at h1
  exact one_ne_zero h1

theorem transcendental_jF : Transcendental Qb (jF N) := transcendental_coeffEmb_jq Qb N

scoped instance isCurveOver_bar : IsCurveOver Qb ↥(modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N

scoped instance hasPrincipalDivisors_bar : HasPrincipalDivisors Qb ↥(modularFunctionFieldBar N) :=
  IsCurveOver.hasPrincipalDivisors

scoped instance finiteDimensional_lSpace_zero_bar :
    FiniteDimensional Qb ↥(LSpace (0 : Divisor Qb ↥(modularFunctionFieldBar N))) := by
  have hC : ConstantsAreBase Qb ↥(modularFunctionFieldBar N) :=
    constantsAreBase_of_deg_eq_one (cuspInftyBar N) (deg_eq_one_modularFunctionFieldBar N _)
  rw [show LSpace (0 : Divisor Qb ↥(modularFunctionFieldBar N)) = _ from hC]
  infer_instance

scoped instance finiteDimensional_adjoin_jF :
    FiniteDimensional (IntermediateField.adjoin Qb ({jF N} : Set ↥(modularFunctionFieldBar N)))
      ↥(modularFunctionFieldBar N) :=
  finiteDimensional_adjoin_coeffEmb_jq_of_neZero N

theorem finrank_adjoin_jF :
    Module.finrank (IntermediateField.adjoin Qb ({jF N} : Set ↥(modularFunctionFieldBar N)))
      ↥(modularFunctionFieldBar N) = dedekindPsi N :=
  CompEq.finrank_adjoin_jBar_eq_dedekindPsi N

theorem degree_poleDivisor_jF (E₀ : Divisor Qb ↥(modularFunctionFieldBar N))
    (hE₀ : ∀ v, E₀ v = max 0 (-(v.ord (jF N)))) : Divisor.degree E₀ = dedekindPsi N := by
  rw [Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord (jF N) (transcendental_jF N) E₀ hE₀, finrank_adjoin_jF]

end Bar

section Red

theorem finrank_adjoin_transport {L : Type*} [Field L]
    {E E' : IntermediateField L (LaurentSeries L)} (h : E = E')
    {x : LaurentSeries L} (hx : x ∈ E) (hx' : x ∈ E') :
    Module.finrank (IntermediateField.adjoin L ({⟨x, hx⟩} : Set E)) E =
      Module.finrank (IntermediateField.adjoin L ({⟨x, hx'⟩} : Set E')) E' := by
  subst h; rfl

variable (κ : Type*) [Field κ] (N : ℕ) [NeZero N]

abbrev jC : ↥(modularFunctionFieldC κ N) := ⟨jqModC κ, jqModC_mem κ N⟩

theorem transcendental_jC : Transcendental κ (jC κ N) := fun h =>
  transcendental_jqModC κ
    ((isAlgebraic_algHom_iff (modularFunctionFieldC κ N).val Subtype.val_injective).mpr h)

theorem jC_ne_zero : jC κ N ≠ 0 := fun h => transcendental_jC κ N (h ▸ isAlgebraic_zero)

theorem finrank_adjoin_jC (q : ℕ) [Fact q.Prime] [CharP κ q] (hqN : ¬ q ∣ N) :
    Module.finrank (IntermediateField.adjoin κ ({jC κ N} : Set ↥(modularFunctionFieldC κ N)))
      ↥(modularFunctionFieldC κ N) = dedekindPsi N := by
  have hN : (N : κ) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff κ q] at h0
    exact hqN h0
  rw [finrank_adjoin_transport (modularFunctionFieldC_eq_modularFunctionFieldFullC κ q N hqN)
    (jqModC_mem κ N) (jqModC_mem_full κ N)]
  exact finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi κ N hN

end Red

end CuspRedReg
p2m_reactivate "P2MW.S_ModularCurve_residue_mem_valuationSubring_of_cuspRegular_of_residue_jq_mem.CuspRedReg"

end
p2m_reactivate "P2MW.S_ModularCurve_residue_mem_valuationSubring_of_cuspRegular_of_residue_jq_mem.CuspRedReg"

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups
open CuspRedReg

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (x : ↥(modularFunctionFieldBar M')) (hx : x ∈ R₀.integers)
    (hreg : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord x)
    (hj : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
    (v : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))
    (hv : (R₀.residue ⟨_, hj⟩ : modularFunctionFieldC (ResidueField A) M') ∈ v.toValuationSubring) :
    (R₀.residue ⟨x, hx⟩ : modularFunctionFieldC (ResidueField A) M') ∈ v.toValuationSubring := by
  classical

  by_cases hx0 : R₀.residue ⟨x, hx⟩ = 0
  · rw [hx0]; exact zero_mem _

  haveI hκ : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : PerfectField (ResidueField A) := IsAlgClosed.perfectField _
  haveI : CharP (ResidueField A) q := by
    have hq0 : ((q : ℕ) : ResidueField A) = 0 := by
      have hqm : (⟨(q : AlgebraicClosure ℚ), natCast_mem A q⟩ : A) ∈ maximalIdeal A := by
        rw [ValuationSubring.valuation_lt_one_iff]
        exact (A.mem_nonunits_iff).mp hA
      have : IsLocalRing.residue A ⟨(q : AlgebraicClosure ℚ), natCast_mem A q⟩ = 0 :=
        (IsLocalRing.residue_eq_zero_iff _).mpr hqm
      rw [← map_natCast (IsLocalRing.residue A) q]
      convert this using 2 <;> first | rfl | (apply Subtype.ext; simp) | (ext; simp)
    exact (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr hq0
  haveI : IsCurveOver (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') :=
    isCurveOver_modularFunctionFieldC_of_perfectField (ResidueField A) M'
  haveI : HasPrincipalDivisors (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') :=
    IsCurveOver.hasPrincipalDivisors
  have hdeg1 : ∀ w : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M'), w.deg = 1 :=
    IsCurveOver.deg_eq_one_of_isAlgClosed
  haveI : FiniteDimensional (ResidueField A)
      ↥(LSpace (0 : Divisor (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M'))) := by
    have hC : ConstantsAreBase (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') :=
      constantsAreBase_of_deg_eq_one (R₀.placeMap (cuspInftyBar M')) (hdeg1 _)
    rw [show LSpace (0 : Divisor (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')) = _ from hC]
    infer_instance

  have hjq : coeffMap A.subtype (jqModC A) = coeffEmb (AlgebraicClosure ℚ) jq :=
    (map_jqModC _).trans (coeffEmb_jq_eq_jqModC (AlgebraicClosure ℚ)).symm
  have hyj : coeffMap A.subtype (jqModC A) ∈ modularFunctionFieldBar M' := by
    rw [hjq]; exact (jF M').2
  have hjres : R₀.residue ⟨jF M', hj⟩ = jC (ResidueField A) M' := by
    obtain ⟨h, hres⟩ := hR₀ (jqModC A) hyj
    have heq : (⟨⟨coeffMap A.subtype (jqModC A), hyj⟩, h⟩ : R₀.integers) = ⟨jF M', hj⟩ :=
      Subtype.ext (Subtype.ext hjq)
    rw [← heq]
    apply Subtype.ext
    rw [hres]
    exact map_jqModC _
  haveI : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A)
        ({jC (ResidueField A) M'} : Set ↥(modularFunctionFieldC (ResidueField A) M')))
      ↥(modularFunctionFieldC (ResidueField A) M') :=
    Module.finite_of_finrank_pos (by
      rw [finrank_adjoin_jC (ResidueField A) M' q hqM']; exact dedekindPsi_pos M' (NeZero.ne M'))

  have hxF0 : x ≠ 0 := by
    intro h0; apply hx0
    have : (⟨x, hx⟩ : R₀.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  obtain ⟨Dx, hDx, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) x hxF0
  obtain ⟨Dj, hDj, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (jF M') (jF_ne_zero M')
  set E₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') :=
    Finsupp.mapRange (fun n : ℤ => max 0 (-n)) (by simp) Dj with hE₀def
  set Z₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') :=
    Finsupp.mapRange (fun n : ℤ => max 0 n) (by simp) Dj with hZ₀def
  have hE₀ : ∀ P, E₀ P = max 0 (-(P.ord (jF M'))) := fun P => by
    rw [hE₀def, Finsupp.mapRange_apply, hDj P]
  have hZ₀ : ∀ P, Z₀ P = max 0 (P.ord (jF M')) := fun P => by
    rw [hZ₀def, Finsupp.mapRange_apply, hDj P]
  have hDjZE : Dj = Z₀ - E₀ := by
    ext P
    rw [Finsupp.sub_apply, hZ₀, hE₀, hDj]
    omega

  obtain ⟨m, hm⟩ : ∃ m : ℕ, -((m : ℤ) • E₀) ≤ Dx := by
    refine ⟨Dx.support.sup fun P => (-(Dx P)).toNat, fun P => ?_⟩
    set m : ℕ := Dx.support.sup fun P => (-(Dx P)).toNat with hmdef
    have hbound : -(m : ℤ) ≤ Dx P := by
      by_cases hP : P ∈ Dx.support
      · have h1 : (-(Dx P)).toNat ≤ m := Finset.le_sup (f := fun P => (-(Dx P)).toNat) hP
        omega
      · rw [Finsupp.notMem_support_iff] at hP
        rw [hP]; omega
    rw [Finsupp.neg_apply, Finsupp.smul_apply, hE₀ P, smul_eq_mul]
    rcases le_or_gt 0 (P.ord (jF M')) with hjP | hjP
    · rw [max_eq_left (by omega), mul_zero, neg_zero, hDx P]
      exact hreg P hjP
    · rw [max_eq_right (by omega)]
      have h1 : (1 : ℤ) ≤ -(P.ord (jF M')) := by omega
      nlinarith [hbound, h1, (Nat.cast_nonneg m : (0 : ℤ) ≤ m)]

  set r := R₀.placeMap with hr
  have hxbar : ∀ Q, Finsupp.mapDomain r Dx Q = Q.ord (R₀.residue ⟨x, hx⟩) :=
    R₀.mapDomain_placeMap ⟨x, hx⟩ hx0 Dx hDx
  have hjbar0 : R₀.residue ⟨jF M', hj⟩ ≠ 0 := by
    rw [hjres]; exact jC_ne_zero (ResidueField A) M'
  have hjbar : ∀ Q, Finsupp.mapDomain r Dj Q = Q.ord (jC (ResidueField A) M') := by
    intro Q; rw [← hjres]; exact R₀.mapDomain_placeMap ⟨jF M', hj⟩ hjbar0 Dj hDj Q

  obtain ⟨Djb, hDjb, -⟩ := HasPrincipalDivisors.exists_divisor (K := ResidueField A)
    (jC (ResidueField A) M') (jC_ne_zero (ResidueField A) M')
  set Eb : Divisor (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') :=
    Finsupp.mapRange (fun n : ℤ => max 0 (-n)) (by simp) Djb with hEbdef
  have hEb : ∀ Q, Eb Q = max 0 (-(Q.ord (jC (ResidueField A) M'))) := fun Q => by
    rw [hEbdef, Finsupp.mapRange_apply, hDjb Q]
  have hkey : Finsupp.mapDomain r E₀ = Eb := by
    symm
    refine eq_of_le_of_degree_eq hdeg1 ?_ ?_
    ·
      intro Q
      have h1 : Finsupp.mapDomain r Z₀ Q - Finsupp.mapDomain r E₀ Q = Q.ord (jC (ResidueField A) M') := by
        rw [← Finsupp.sub_apply, ← Finsupp.mapDomain_sub, ← hDjZE]
        exact hjbar Q
      have h2 : 0 ≤ Finsupp.mapDomain r Z₀ Q := by
        have : (0 : Divisor (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')) ≤
            Finsupp.mapDomain r Z₀ :=
          Finsupp.mapDomain_nonneg fun P => by
            show (0 : ℤ) ≤ Z₀ P
            rw [hZ₀]; exact le_max_left _ _
        exact this Q
      have h3 : 0 ≤ Finsupp.mapDomain r E₀ Q := by
        have : (0 : Divisor (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')) ≤
            Finsupp.mapDomain r E₀ :=
          Finsupp.mapDomain_nonneg fun P => by
            show (0 : ℤ) ≤ E₀ P
            rw [hE₀]; exact le_max_left _ _
        exact this Q
      rw [hEb]
      exact max_le h3 (by omega)
    ·
      rw [R₀.degree_mapDomain, degree_poleDivisor_jF M' E₀ hE₀,
        Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord (jC (ResidueField A) M')
          (transcendental_jC (ResidueField A) M') Eb hEb,
        finrank_adjoin_jC (ResidueField A) M' q hqM']

  have hvj : 0 ≤ v.ord (jC (ResidueField A) M') := by
    rw [← hjres]
    exact (Place.mem_iff_ord_nonneg v hjbar0).mp hv
  have hEbv : Eb v = 0 := by rw [hEb, max_eq_left (by omega)]
  have hle : Finsupp.mapDomain r (-((m : ℤ) • E₀)) ≤ Finsupp.mapDomain r Dx := Finsupp.mapDomain_mono hm
  have hneg : Finsupp.mapDomain r (-((m : ℤ) • E₀)) = -((m : ℤ) • Finsupp.mapDomain r E₀) := by
    have := map_neg (Finsupp.mapDomain.addMonoidHom r) ((m : ℤ) • E₀)
    rw [map_zsmul] at this
    simpa using this
  have hord : 0 ≤ v.ord (R₀.residue ⟨x, hx⟩) := by
    rw [← hxbar v]
    refine le_trans ?_ (hle v)
    rw [hneg, Finsupp.neg_apply, Finsupp.smul_apply, hkey, hEbv, smul_zero, neg_zero]
  exact (Place.mem_iff_ord_nonneg v hx0).mpr hord

end S_ModularCurve_residue_mem_valuationSubring_of_cuspRegular_of_residue_jq_mem
end P2MW
export P2MW.S_ModularCurve_residue_mem_valuationSubring_of_cuspRegular_of_residue_jq_mem (solution)
