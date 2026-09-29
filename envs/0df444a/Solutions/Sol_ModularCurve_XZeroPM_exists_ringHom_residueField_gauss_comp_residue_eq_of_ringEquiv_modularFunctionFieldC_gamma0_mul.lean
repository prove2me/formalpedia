-- Prove2me | solution 1 for ModularCurve.XZeroPM.exists_ringHom_residueField_gauss_comp_residue_eq_of_ringEquiv_modularFunctionFieldC_gamma0_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/382bde9f-cdad-5cf1-a475-4c6420889c46

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_XZeroPM_mem_ker_iff_coe_mem_nonunits_gaussValuationSubring_of_map_jChartFin_eq_jGeomGen_gamma0_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XZeroPM_exists_ringHom_residueField_gauss_comp_residue_eq_of_ringEquiv_modularFunctionFieldC_gamma0_mul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.Point.instFinite CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"
p2m_attr_erase "simp" "ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply"
p2m_attr_erase "simp" "CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₂] [IsScalarTower A L ↥K₂]
    (j₂ : ↥K₂) (hj₂ : ((j₂ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₂ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₂ : ValuationSubring ↥K₂)
    (hW₂ : ∀ f : ↥K₂, f ∈ W₂ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hSW₂ : ∀ b : ↥(chartAlgFin A (↥K₂) j₂), (b : ↥K₂) ∈ W₂)

    (bM : ↥(chartAlgFin A (↥K₂) j₂))
    (hbM : (((bM : ↥K₂) : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ M ModularCurve.jq))

    (ε₂ : IsLocalRing.ResidueField ↥W₂ ≃+* ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) M))
    (hε₂j : ε₂ (IsLocalRing.residue ↥W₂ ⟨(jChartFin A (↥K₂) j₂ : ↥K₂), hSW₂ _⟩) =
      ModularCurve.jGeomGen (IsLocalRing.ResidueField A) M)
    (hε₂jM : ε₂ (IsLocalRing.residue ↥W₂ ⟨(bM : ↥K₂), hSW₂ _⟩) = ModularCurve.jNGeomGen (IsLocalRing.ResidueField A) M)
    (hε₂A : ∀ a : A, ε₂ (IsLocalRing.residue ↥W₂ ⟨((algebraMap A ↥(chartAlgFin A (↥K₂) j₂) a : ↥(chartAlgFin A (↥K₂) j₂)) : ↥K₂), hSW₂ _⟩) =
      algebraMap (IsLocalRing.ResidueField A) ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) M) (IsLocalRing.residue A a))

    (𝔶₂ : Ideal ↥(chartAlgFin A (↥K₂) j₂))
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] [DecidableEq k]
    (halg : ∀ x : k, ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x)
    (w : AlgebraicCurve.Place k ↥(ModularCurve.modularFunctionFieldC k M))
    (hw : w ∈ ModularCurve.ssPlaces p M k)
    (ρ : ↥(chartAlgFin A (↥K₂) j₂) →+* ↥(ModularCurve.modularFunctionFieldC k M))
    (hρϖ : ρ (algebraMap A ↥(chartAlgFin A (↥K₂) j₂) ϖ) = 0)
    (hρj : ρ (jChartFin A (↥K₂) j₂) = ModularCurve.jGeomGen k M)
    (hρint : ∀ b, ρ b ∈ w.toValuationSubring)
    (hρcent : ∀ b, ρ b ∈ w.toValuationSubring.nonunits ↔ b ∈ 𝔶₂)
    (hρbir : ∀ f : ↥(ModularCurve.modularFunctionFieldC k M), ∃ a b : ↥(Algebra.adjoin k (Set.range ρ)),
        (b : ↥(ModularCurve.modularFunctionFieldC k M)) ≠ 0 ∧ f * b = a) :
    ∃ θt : IsLocalRing.ResidueField ↥W₂ →+* ↥(ModularCurve.modularFunctionFieldC k M),
      ∀ b : ↥(chartAlgFin A (↥K₂) j₂), θt (IsLocalRing.residue ↥W₂ ⟨(b : ↥K₂), hSW₂ b⟩) = ρ b := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  let ρ₂ : ↥(chartAlgFin A (↥K₂) j₂) →+* IsLocalRing.ResidueField ↥W₂ :=
    (IsLocalRing.residue ↥W₂).comp
      { toFun := fun b => ⟨(b : ↥K₂), hSW₂ b⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun _ _ => Subtype.ext rfl
        map_zero' := Subtype.ext rfl
        map_add' := fun _ _ => Subtype.ext rfl }
  have hρ₂ : ∀ b, ρ₂ b = IsLocalRing.residue ↥W₂ ⟨(b : ↥K₂), hSW₂ b⟩ := fun _ => rfl

  have hpin := ModularCurve.XZeroPM.mem_ker_iff_coe_mem_nonunits_gaussValuationSubring_of_map_jChartFin_eq_jGeomGen_gamma0_mul
      p M hM hpM L ζ hζ K₂ hK₂ A hAp hζA j₂ hj₂ ϖ hϖ W₂ hW₂ 𝔶₂ k w hw ρ hρϖ hρj hρint hρcent hρbir
  have hker : ∀ b, ρ b = 0 ↔ ρ₂ b = 0 := fun b => by
    rw [← RingHom.mem_ker, hpin b, hρ₂, IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]

  let f : ↥(chartAlgFin A (↥K₂) j₂) →+* ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) M) :=
    ε₂.toRingHom.comp ρ₂
  have hf : ∀ b, f b = ε₂ (ρ₂ b) := fun _ => rfl
  have hkerf : ∀ b, f b = 0 ↔ ρ b = 0 := fun b => by rw [hf, map_eq_zero_iff ε₂ ε₂.injective, hker]
  let fr : ↥(chartAlgFin A (↥K₂) j₂) →+* ↥f.range := f.rangeRestrict
  have hfr : Function.Surjective fr := RingHom.rangeRestrict_surjective f
  have hfrval : ∀ b, ((fr b : ↥f.range) : ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) M)) = f b := fun _ => rfl
  have hkerle : RingHom.ker fr ≤ RingHom.ker ρ := fun b hb => by
    rw [RingHom.mem_ker] at hb ⊢
    exact (hkerf b).mp (by rw [← hfrval, hb]; rfl)
  let g : ↥f.range →+* ↥(ModularCurve.modularFunctionFieldC k M) :=
    RingHom.liftOfRightInverse fr (Function.surjInv hfr) (Function.rightInverse_surjInv hfr) ⟨ρ, hkerle⟩
  have hg : ∀ b, g (fr b) = ρ b := fun b =>
    RingHom.liftOfRightInverse_comp_apply fr (Function.surjInv hfr) (Function.rightInverse_surjInv hfr) ⟨ρ, hkerle⟩ b
  have hginj : Function.Injective g := by
    intro x y hxy
    obtain ⟨bx, rfl⟩ := hfr x
    obtain ⟨by', rfl⟩ := hfr y
    rw [hg, hg, ← sub_eq_zero, ← map_sub, ← hkerf] at hxy
    rw [← sub_eq_zero, ← map_sub]
    exact Subtype.ext (by rw [hfrval]; exact hxy)

  let RgA : Subalgebra (IsLocalRing.ResidueField A) ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) M) :=
    { f.range.toSubsemiring with
      algebraMap_mem' := fun c => by
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
        exact ⟨algebraMap A _ a, hε₂A a⟩ }
  have hRgA : ∀ x, x ∈ RgA ↔ x ∈ f.range := fun _ => Iff.rfl
  let RgL : Subalgebra (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) :=
    RgA.map (ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) M).val
  have hgens : ({ModularCurve.jqModC (IsLocalRing.ResidueField A), ModularCurve.jqNModC (IsLocalRing.ResidueField A) M} :
      Set (LaurentSeries (IsLocalRing.ResidueField A))) ⊆ RgL := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Subalgebra.mem_map.mpr ⟨ModularCurve.jGeomGen _ M, (hRgA _).mpr ⟨_, hε₂j⟩, rfl⟩
    · exact Subalgebra.mem_map.mpr ⟨ModularCurve.jNGeomGen _ M, (hRgA _).mpr ⟨_, hε₂jM⟩, rfl⟩
  have hadj : Algebra.adjoin (IsLocalRing.ResidueField A)
      ({ModularCurve.jqModC (IsLocalRing.ResidueField A), ModularCurve.jqNModC (IsLocalRing.ResidueField A) M} :
        Set (LaurentSeries (IsLocalRing.ResidueField A))) ≤ RgL := Algebra.adjoin_le hgens
  have hmemR : ∀ r, r ∈ Algebra.adjoin (IsLocalRing.ResidueField A)
      ({ModularCurve.jqModC (IsLocalRing.ResidueField A), ModularCurve.jqNModC (IsLocalRing.ResidueField A) M} :
        Set (LaurentSeries (IsLocalRing.ResidueField A))) →
      ∃ x : ↥f.range, (((x : ↥f.range) : ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) M)) :
        LaurentSeries (IsLocalRing.ResidueField A)) = r := by
    intro r hr
    obtain ⟨y, hy, hyr⟩ := Subalgebra.mem_map.mp (hadj hr)
    exact ⟨⟨y, (hRgA y).mp hy⟩, hyr⟩
  haveI : IsFractionRing ↥f.range ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) M) := by
    refine IsFractionRing.of_field _ _ (fun z => ?_)
    have hz : (z : LaurentSeries (IsLocalRing.ResidueField A)) ∈
        IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({ModularCurve.jqModC (IsLocalRing.ResidueField A), ModularCurve.jqNModC (IsLocalRing.ResidueField A) M} :
            Set (LaurentSeries (IsLocalRing.ResidueField A))) := z.2
    obtain ⟨r, hr, s, hs, hzrs⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
    obtain ⟨x, hx⟩ := hmemR r hr
    obtain ⟨y, hy⟩ := hmemR s hs
    refine ⟨x, y, Subtype.ext ?_⟩
    rw [hzrs, ← hx, ← hy]
    rfl

  refine ⟨(IsFractionRing.lift hginj).comp ε₂.toRingHom, fun b => ?_⟩
  show IsFractionRing.lift hginj (ε₂ (IsLocalRing.residue ↥W₂ ⟨(b : ↥K₂), hSW₂ b⟩)) = ρ b
  rw [← hρ₂, ← hf, ← hfrval, show ((fr b : ↥f.range) : ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) M)) =
      algebraMap ↥f.range ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) M) (fr b) from rfl,
    IsFractionRing.lift_algebraMap, hg]

end S_ModularCurve_XZeroPM_exists_ringHom_residueField_gauss_comp_residue_eq_of_ringEquiv_modularFunctionFieldC_gamma0_mul
end P2MW
export P2MW.S_ModularCurve_XZeroPM_exists_ringHom_residueField_gauss_comp_residue_eq_of_ringEquiv_modularFunctionFieldC_gamma0_mul (solution)
