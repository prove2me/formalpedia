-- Prove2me | solution 1 for ModularCurve.FullLevel.sum_algebraMap_mul_apply_eq_zero_of_sum_smul_residue_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/c5481baa-605e-54eb-9b07-369ead97e5a1

import Theorems.Thm_ModularCurve_algebraMap_coeff_mem_of_mem_integers_of_cuspRegular
import Theorems.Thm_RingHom_exists_eq_sum_mul_of_forall_sum_mul_eq_zero_of_forall_mem_range
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_sum_algebraMap_mul_apply_eq_zero_of_sum_smul_residue_eq_zero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 12800000
open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups
attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open scoped Classical

namespace LinConsAux

theorem residue_mem_range_castHom {L : Type*} [Field L] [CharZero L] (A : ValuationSubring L) (q : ℕ) [Fact q.Prime]
    [CharP (ResidueField ↥A) q] (r : ℚ) (hr : algebraMap ℚ L r ∈ A) :
    IsLocalRing.residue ↥A ⟨algebraMap ℚ L r, hr⟩ ∈ Set.range (ZMod.castHom (dvd_refl q) (ResidueField ↥A)) := by
  set φ := ZMod.castHom (dvd_refl q) (ResidueField ↥A)
  have key : (⟨algebraMap ℚ L r, hr⟩ : ↥A) * ((r.den : ℕ) : ↥A) = ((r.num : ℤ) : ↥A) := by
    apply Subtype.ext
    show algebraMap ℚ L r * (((r.den : ℕ) : ↥A) : L) = (((r.num : ℤ) : ↥A) : L)
    rw [SubringClass.coe_natCast, SubringClass.coe_intCast, ← map_natCast (algebraMap ℚ L), ← map_intCast (algebraMap ℚ L),
      ← map_mul, Rat.mul_den_eq_num]
  have key2 : IsLocalRing.residue ↥A ⟨algebraMap ℚ L r, hr⟩ * ((r.den : ℕ) : ResidueField ↥A) =
      ((r.num : ℤ) : ResidueField ↥A) := by
    have h := congrArg (IsLocalRing.residue ↥A) key
    rwa [map_mul, map_natCast, map_intCast] at h
  by_cases h0 : ((r.den : ℕ) : ResidueField ↥A) = 0
  · exfalso
    have hqden : q ∣ r.den := (CharP.cast_eq_zero_iff (ResidueField ↥A) q _).mp h0
    have hnum0 : ((r.num : ℤ) : ResidueField ↥A) = 0 := by rw [← key2, h0, mul_zero]
    have hqnum : (q : ℤ) ∣ r.num := (CharP.intCast_eq_zero_iff (ResidueField ↥A) q _).mp hnum0
    have hqnum' : q ∣ r.num.natAbs := Int.natCast_dvd.mp hqnum
    have h1 : q ∣ Nat.gcd r.num.natAbs r.den := Nat.dvd_gcd hqnum' hqden
    rw [r.reduced] at h1
    exact (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h1)
  · refine ⟨((r.num : ℤ) : ZMod q) * (((r.den : ℕ) : ZMod q))⁻¹, ?_⟩
    rw [map_mul, map_inv₀, map_intCast, map_natCast]
    exact ((eq_mul_inv_iff_mul_eq₀ h0).mpr key2).symm

end LinConsAux

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)

    (𝒜 : Subring (LaurentSeries ℚ))
    (h𝒜 : ∀ gf : LaurentSeries ℚ, gf ∈ 𝒜 ↔
      ∃ (hgf : gf ∈ modularFunctionFieldFull M')
        (_ : (⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
        ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) :
            ↥(modularFunctionFieldBar M')))
    (hj𝒜 : jq ∈ 𝒜)
    (Ω : Type) [Field Ω] [Algebra (ResidueField A) Ω] (val : ↥𝒜 →+* Ω)
    (hval0 : ∀ (gf : LaurentSeries ℚ) (h : gf ∈ 𝒜) (hgf : gf ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') = 0 → val ⟨gf, h⟩ = 0)
    (hvalj : Transcendental (ResidueField A) (val ⟨jq, hj𝒜⟩)) :
    ∀ (n : ℕ) (gf : Fin n → LaurentSeries ℚ) (h : ∀ i, gf i ∈ 𝒜) (hgf : ∀ i, gf i ∈ modularFunctionFieldFull M')
      (hgi : ∀ i, (⟨coeffEmb (AlgebraicClosure ℚ) (gf i), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hgf i)⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
      (c : Fin n → ResidueField A),
      ∑ i, c i • (R₀.residue ⟨_, hgi i⟩ : modularFunctionFieldC (ResidueField A) M') = 0 →
      ∑ i, algebraMap (ResidueField A) Ω (c i) * val ⟨gf i, h i⟩ = 0 := by
  classical
  intro n gf h hgf hgi c hsum
  haveI hchar : CharP (ResidueField ↥A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA

  have hcusp : ∀ i, ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (gf i), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hgf i)⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) := by
    intro i
    obtain ⟨hgf', hgi', hc'⟩ := (h𝒜 (gf i)).mp (h i)
    exact hc'
  let φ : ZMod q →+* (ResidueField ↥A) := ZMod.castHom (dvd_refl q) (ResidueField ↥A)
  let T : Fin n → (modularFunctionFieldC (ResidueField ↥A) M') := fun i => R₀.residue ⟨_, hgi i⟩

  have hcoefT : ∀ (i : Fin n) (x : ℤ), ((T i : (modularFunctionFieldC (ResidueField ↥A) M')) : LaurentSeries (ResidueField ↥A)).coeff x ∈ Set.range φ := by
    intro i x
    have hint := ModularCurve.algebraMap_coeff_mem_of_mem_integers_of_cuspRegular q M' A hA R₀ hR₀ (gf i) (hgf i) (hgi i) (hcusp i)
    let y : LaurentSeries ↥A :=
      { coeff := fun k => ⟨(coeffEmb (AlgebraicClosure ℚ) (gf i)).coeff k, hint k⟩
        isPWO_support' := (coeffEmb (AlgebraicClosure ℚ) (gf i)).isPWO_support'.mono (by
          intro k hk
          simp only [Function.mem_support, ne_eq] at hk ⊢
          exact fun h0 => hk (Subtype.ext h0)) }
    have hy : coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (gf i) := by ext k; rfl
    have hyF : coeffMap A.subtype y ∈ modularFunctionFieldBar M' := by
      rw [hy]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hgf i)
    obtain ⟨h', hres⟩ := hR₀ y hyF
    have helt : (⟨coeffMap A.subtype y, hyF⟩ : ↥(modularFunctionFieldBar M')) = ⟨coeffEmb (AlgebraicClosure ℚ) (gf i), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hgf i)⟩ :=
      Subtype.ext hy
    have hti : ((T i : (modularFunctionFieldC (ResidueField ↥A) M')) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y := by
      rw [← hres]
      show ((R₀.residue ⟨_, hgi i⟩ : (modularFunctionFieldC (ResidueField ↥A) M')) : LaurentSeries (ResidueField ↥A)) = _
      congr 2
    rw [hti, coeffMap_coeff]
    exact LinConsAux.residue_mem_range_castHom A q ((gf i).coeff x) (hint x)
  have eC : ∀ r : (ResidueField ↥A), ((algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M') r : (modularFunctionFieldC (ResidueField ↥A) M')) : LaurentSeries (ResidueField ↥A)) = HahnSeries.C r := by
    intro r
    rw [SubalgebraClass.coe_algebraMap, algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]

  have hcoe : ∀ (r : Fin n → (ResidueField ↥A)) (x : ℤ),
      (((∑ l, r l • T l : (modularFunctionFieldC (ResidueField ↥A) M')) : (modularFunctionFieldC (ResidueField ↥A) M')) : LaurentSeries (ResidueField ↥A)).coeff x =
        ∑ l, r l * ((T l : (modularFunctionFieldC (ResidueField ↥A) M')) : LaurentSeries (ResidueField ↥A)).coeff x := by
    intro r x
    simp_rw [Algebra.smul_def]
    rw [IntermediateField.coe_sum, HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [IntermediateField.coe_mul, eC, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  have hc : ∀ x : ℤ, ∑ l, c l * ((T l : (modularFunctionFieldC (ResidueField ↥A) M')) : LaurentSeries (ResidueField ↥A)).coeff x = 0 := by
    intro x
    rw [← hcoe c x, hsum, ZeroMemClass.coe_zero, HahnSeries.coeff_zero]

  obtain ⟨m, d, v, hv, hcd⟩ := RingHom.exists_eq_sum_mul_of_forall_sum_mul_eq_zero_of_forall_mem_range φ
    (fun l x => ((T l : (modularFunctionFieldC (ResidueField ↥A) M')) : LaurentSeries (ResidueField ↥A)).coeff x) (fun l x => hcoefT l x) c hc
  have hφ : ∀ j' l, φ (v j' l) = (((v j' l).val : ℤ) : (ResidueField ↥A)) := by
    intro j' l
    show ZMod.cast (v j' l) = _
    rw [ZMod.cast_eq_val, Int.cast_natCast]

  have hrel : ∀ j', ∑ l, (((v j' l).val : ℤ) : (ResidueField ↥A)) • T l = 0 := by
    intro j'
    apply Subtype.ext
    ext x
    rw [hcoe, ZeroMemClass.coe_zero, HahnSeries.coeff_zero]
    have := hv j' x
    simp only [hφ] at this
    exact this

  have hkill : ∀ j', ∑ l, (((v j' l).val : ℤ) : Ω) * val ⟨gf l, h l⟩ = 0 := by
    intro j'
    let GA : ↥𝒜 := ∑ l, ((((v j' l).val : ℤ)) : ↥𝒜) * ⟨gf l, h l⟩
    have hGcoe : (GA : LaurentSeries ℚ) = ∑ l, ((((v j' l).val : ℤ)) : LaurentSeries ℚ) * gf l := by
      show ((∑ l, ((((v j' l).val : ℤ)) : ↥𝒜) * ⟨gf l, h l⟩ : ↥𝒜) : LaurentSeries ℚ) = _
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [MulMemClass.coe_mul, SubringClass.coe_intCast]
    have hGF : (GA : LaurentSeries ℚ) ∈ modularFunctionFieldFull M' := by
      rw [hGcoe]; exact sum_mem fun l _ => mul_mem (intCast_mem _ _) (hgf l)
    have eBar : (⟨coeffEmb (AlgebraicClosure ℚ) (GA : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hGF⟩ : ↥(modularFunctionFieldBar M')) =
        ∑ l, ((((v j' l).val : ℤ)) : ↥(modularFunctionFieldBar M')) * ⟨coeffEmb (AlgebraicClosure ℚ) (gf l), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hgf l)⟩ := by
      apply Subtype.ext
      show coeffEmb (AlgebraicClosure ℚ) (GA : LaurentSeries ℚ) = _
      rw [IntermediateField.coe_sum, hGcoe, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [IntermediateField.coe_mul, SubringClass.coe_intCast, map_mul, map_intCast]
    have hGi : (⟨coeffEmb (AlgebraicClosure ℚ) (GA : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hGF⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers := by
      rw [eBar]; exact sum_mem fun l _ => mul_mem (intCast_mem _ _) (hgi l)
    have hGres : (R₀.residue ⟨_, hGi⟩ : modularFunctionFieldC (ResidueField A) M') = 0 := by
      have e2 : (⟨_, hGi⟩ : ↥R₀.integers) = ∑ l, ((((v j' l).val : ℤ)) : ↥R₀.integers) * ⟨_, hgi l⟩ := by
        apply Subtype.ext
        show (⟨coeffEmb (AlgebraicClosure ℚ) (GA : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hGF⟩ : ↥(modularFunctionFieldBar M')) =
          ((∑ l, ((((v j' l).val : ℤ)) : ↥R₀.integers) * ⟨_, hgi l⟩ : ↥R₀.integers) : ↥(modularFunctionFieldBar M'))
        rw [eBar, AddSubmonoidClass.coe_finsetSum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [MulMemClass.coe_mul, SubringClass.coe_intCast]
      rw [e2, map_sum]
      simp_rw [map_mul, map_intCast]
      rw [← hrel j']
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Algebra.smul_def, map_intCast]
    have hv0 := hval0 (GA : LaurentSeries ℚ) GA.2 hGF hGi hGres
    have eGA : (⟨(GA : LaurentSeries ℚ), GA.2⟩ : ↥𝒜) = GA := Subtype.coe_eta _ _
    rw [eGA] at hv0
    have : val GA = ∑ l, (((v j' l).val : ℤ) : Ω) * val ⟨gf l, h l⟩ := by
      show val (∑ l, ((((v j' l).val : ℤ)) : ↥𝒜) * ⟨gf l, h l⟩) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, map_intCast]
    rw [← this, hv0]

  calc ∑ i, algebraMap (ResidueField ↥A) Ω (c i) * val ⟨gf i, h i⟩
      = ∑ l, (∑ j', algebraMap (ResidueField ↥A) Ω (d j') * (((v j' l).val : ℤ) : Ω)) * val ⟨gf l, h l⟩ := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hcd l, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun j' _ => ?_
        rw [map_mul, hφ, map_intCast]
    _ = ∑ j', algebraMap (ResidueField ↥A) Ω (d j') * ∑ l, (((v j' l).val : ℤ) : Ω) * val ⟨gf l, h l⟩ := by
        simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        rw [Finset.sum_comm]
    _ = 0 := by
        refine Finset.sum_eq_zero fun j' _ => ?_
        rw [hkill j', mul_zero]

end S_ModularCurve_FullLevel_sum_algebraMap_mul_apply_eq_zero_of_sum_smul_residue_eq_zero
end P2MW
export P2MW.S_ModularCurve_FullLevel_sum_algebraMap_mul_apply_eq_zero_of_sum_smul_residue_eq_zero (solution)
