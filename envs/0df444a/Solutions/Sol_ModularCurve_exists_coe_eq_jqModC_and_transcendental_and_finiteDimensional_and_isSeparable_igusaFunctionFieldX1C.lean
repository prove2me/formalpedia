-- Prove2me | solution 1 for ModularCurve.exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_igusaFunctionFieldX1C
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/1254a201-42ed-5a2c-b495-68f48f219c59

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC
import Theorems.Thm_ModularCurve_isKummerGenerator_hasseRootFn_x1FunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_igusaFunctionFieldX1C
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec"
p2m_attr_erase "simp" "CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open scoped IntermediateField

namespace FinSepAux

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]

section Copy

variable {K₀ L₀ : IntermediateField k Ω} (hle : K₀ ≤ L₀)

def F : IntermediateField k ↥L₀ := K₀.comap L₀.val

theorem mem_F (x : ↥L₀) : x ∈ F (K₀ := K₀) (L₀ := L₀) ↔ (x : Ω) ∈ K₀ := Iff.rfl

def ιF : ↥K₀ →ₐ[k] ↥(F (K₀ := K₀) (L₀ := L₀)) where
  toFun x := ⟨IntermediateField.inclusion hle x, x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x y)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)
  commutes' c := Subtype.ext ((IntermediateField.inclusion hle).commutes c)

noncomputable def eF : ↥K₀ ≃ₐ[k] ↥(F (K₀ := K₀) (L₀ := L₀)) :=
  AlgEquiv.ofBijective (ιF hle)
    ⟨fun x y h => IntermediateField.inclusion_injective hle (congrArg Subtype.val h),
     fun y => ⟨⟨(y : ↥L₀), y.2⟩, Subtype.ext (Subtype.ext rfl)⟩⟩

theorem coe_eF (x : ↥K₀) : (eF hle x : ↥L₀) = IntermediateField.inclusion hle x := rfl

end Copy

theorem eq_top_of_generators_mem {K₀ L₀ : IntermediateField k Ω} {a : Ω}
    (hL : L₀ = IntermediateField.adjoin k ((K₀ : Set Ω) ∪ {a})) (hle : K₀ ≤ L₀) (haL : a ∈ L₀)
    (E : IntermediateField k ↥L₀)
    (hK : ∀ x : ↥L₀, (x : Ω) ∈ K₀ → x ∈ E) (ha : (⟨a, haL⟩ : ↥L₀) ∈ E) : E = ⊤ := by
  apply top_le_iff.1
  intro x _
  have hsub : L₀ ≤ IntermediateField.lift E := by
    refine hL.le.trans (IntermediateField.adjoin_le_iff.2 (Set.union_subset ?_ ?_))
    · intro y hy
      exact (IntermediateField.mem_lift ⟨y, hle hy⟩).2 (hK _ hy)
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (IntermediateField.mem_lift ⟨y, haL⟩).2 ha
  exact (IntermediateField.mem_lift x).1 (hsub x.2)

end FinSepAux

set_option maxHeartbeats 6400000 in
open ModularCurve FinSepAux in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (w : ModularCurve.IntegralWeightOneForm k M) :
    ∃ t : ↥(ModularCurve.igusaFunctionFieldX1C k M w),
      ((t : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) = ModularCurve.jqModC k ∧
      Transcendental k t ∧
      FiniteDimensional ↥k⟮t⟯ ↥(ModularCurve.igusaFunctionFieldX1C k M w) ∧
      Algebra.IsSeparable ↥k⟮t⟯ ↥(ModularCurve.igusaFunctionFieldX1C k M w)  := by
  classical

  obtain ⟨t₀, ht₀, htr₀, hfin₀, hsep₀⟩ :=
    ModularCurve.exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC p M hM hpM k
  have hK := ModularCurve.isKummerGenerator_hasseRootFn_x1FunctionFieldC p M hM hpM k w

  have hle : ModularCurve.x1FunctionFieldC k M ≤ ModularCurve.igusaFunctionFieldX1C k M w :=
    ModularCurve.x1FunctionFieldC_le_igusaFunctionFieldX1C k M w
  have haL : w.hasseRootFn ∈ ModularCurve.igusaFunctionFieldX1C k M w := ModularCurve.hasseRootFn_mem_igusaFunctionFieldX1C k M w
  let ι : ↥(ModularCurve.x1FunctionFieldC k M) →ₐ[k] ↥(ModularCurve.igusaFunctionFieldX1C k M w) := IntermediateField.inclusion hle
  have hι : Function.Injective ι := IntermediateField.inclusion_injective hle
  let t : ↥(ModularCurve.igusaFunctionFieldX1C k M w) := ι t₀
  refine ⟨t, ht₀, ?_, ?_⟩
  ·
    exact fun h => htr₀ ((isAlgebraic_algHom_iff ι hι).1 h)

  haveI := hfin₀
  haveI := hsep₀
  let Fc : IntermediateField k ↥(ModularCurve.igusaFunctionFieldX1C k M w) := F (K₀ := ModularCurve.x1FunctionFieldC k M) (L₀ := ModularCurve.igusaFunctionFieldX1C k M w)
  have htF : k⟮t⟯ ≤ Fc := IntermediateField.adjoin_simple_le_iff.2 (show ((t : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) ∈ ModularCurve.x1FunctionFieldC k M from t₀.2)
  let F' : IntermediateField ↥k⟮t⟯ ↥(ModularCurve.igusaFunctionFieldX1C k M w) := IntermediateField.extendScalars htF

  let e₂ : ↥(ModularCurve.x1FunctionFieldC k M) ≃+* ↥F' := (eF hle).toRingEquiv
  have hmap : IntermediateField.map ι k⟮t₀⟯ = k⟮t⟯ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
  let e₁ : ↥k⟮t₀⟯ ≃+* ↥k⟮t⟯ := ((IntermediateField.equivMap k⟮t₀⟯ ι).trans (IntermediateField.equivOfEq hmap)).toRingEquiv
  have he : (algebraMap ↥k⟮t⟯ ↥F').comp (e₁ : ↥k⟮t₀⟯ →+* ↥k⟮t⟯) = (e₂ : ↥(ModularCurve.x1FunctionFieldC k M) →+* ↥F').comp (algebraMap ↥k⟮t₀⟯ ↥(ModularCurve.x1FunctionFieldC k M)) := by
    apply RingHom.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    rfl
  haveI : Module.Finite ↥k⟮t⟯ ↥F' := Module.Finite.of_equiv_equiv e₁ e₂ he
  haveI : Algebra.IsSeparable ↥k⟮t⟯ ↥F' := Algebra.IsSeparable.of_equiv_equiv e₁ e₂ he

  let α : ↥(ModularCurve.igusaFunctionFieldX1C k M w) := ⟨w.hasseRootFn, haL⟩
  have memF' : ∀ z : ↥(ModularCurve.igusaFunctionFieldX1C k M w), z ∈ F' ↔ (z : LaurentSeries k) ∈ ModularCurve.x1FunctionFieldC k M := by
    intro z
    rw [IntermediateField.mem_extendScalars]
    exact mem_F z
  have hαpow : α ^ (p - 1) ∈ F' := by
    rw [memF', SubmonoidClass.coe_pow]
    exact hK.pow_mem
  have hα0 : α ≠ 0 := fun h => hK.ne_zero (congrArg Subtype.val h)
  have hn : ((p - 1 : ℕ) : ↥F') ≠ 0 := by
    intro h
    have h' : ((p - 1 : ℕ) : k) = 0 := by
      have := congrArg (fun x : ↥F' => ((x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k)) h
      have h1 : (((p - 1 : ℕ) : ↥F') : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) = ((p - 1 : ℕ) : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) := by norm_cast
      have h2 : ((((p - 1 : ℕ) : ↥(ModularCurve.igusaFunctionFieldX1C k M w))) : LaurentSeries k) = ((p - 1 : ℕ) : LaurentSeries k) := by norm_cast
      rw [h1, h2] at this
      have h3 : ((p - 1 : ℕ) : LaurentSeries k) = algebraMap k (LaurentSeries k) ((p - 1 : ℕ) : k) := by rw [map_natCast]
      rw [h3, show ((0 : ↥F') : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) = 0 from rfl, ZeroMemClass.coe_zero] at this
      exact (map_eq_zero_iff _ (algebraMap k (LaurentSeries k)).injective).1 this
    have hp1 : ((p - 1 : ℕ) : k) = -1 := by
      have : ((p - 1 : ℕ) : k) + 1 = 0 := by
        rw [show ((p - 1 : ℕ) : k) + 1 = ((p - 1 + 1 : ℕ) : k) by push_cast; ring,
          Nat.sub_add_cancel (Fact.out : p.Prime).one_lt.le, CharP.cast_eq_zero]
      exact eq_neg_of_add_eq_zero_left this
    rw [hp1] at h'
    exact one_ne_zero (neg_eq_zero.1 h')
  have hint : IsIntegral ↥F' α := by
    refine ⟨Polynomial.X ^ (p - 1) - Polynomial.C ⟨α ^ (p - 1), hαpow⟩, Polynomial.monic_X_pow_sub_C _ ?_, ?_⟩
    · exact Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt
    · simp [Polynomial.eval₂_sub, sub_eq_zero]
  have hsepα : IsSeparable ↥F' α := by
    refine (Polynomial.separable_X_pow_sub_C (⟨α ^ (p - 1), hαpow⟩ : ↥F') hn ?_).of_dvd (minpoly.dvd _ _ ?_)
    · exact fun h => pow_ne_zero _ hα0 (congrArg Subtype.val h)
    · simp [sub_eq_zero]
  haveI : IsScalarTower k ↥F' ↥(ModularCurve.igusaFunctionFieldX1C k M w) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have htop' : (F'⟮α⟯).restrictScalars k = ⊤ :=
    eq_top_of_generators_mem (K₀ := ModularCurve.x1FunctionFieldC k M) (a := w.hasseRootFn) rfl hle haL _
      (fun x hx => (F'⟮α⟯).algebraMap_mem ⟨x, (memF' x).2 hx⟩)
      (IntermediateField.mem_adjoin_simple_self _ α)
  have htop : F'⟮α⟯ = ⊤ := by
    apply IntermediateField.restrictScalars_injective k
    rw [htop', IntermediateField.restrictScalars_top]
  haveI : Module.Finite ↥F' ↥(ModularCurve.igusaFunctionFieldX1C k M w) := by
    haveI : FiniteDimensional ↥F' ↥F'⟮α⟯ := IntermediateField.adjoin.finiteDimensional hint
    rw [htop] at this
    exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := ↥F') (E := ↥(ModularCurve.igusaFunctionFieldX1C k M w))).toLinearEquiv
  haveI : Algebra.IsSeparable ↥F' ↥(ModularCurve.igusaFunctionFieldX1C k M w) := by
    haveI : Algebra.IsSeparable ↥F' ↥F'⟮α⟯ := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).2 hsepα
    rw [htop] at this
    exact Algebra.IsSeparable.of_algHom ↥F' _ (IntermediateField.topEquiv (F := ↥F') (E := ↥(ModularCurve.igusaFunctionFieldX1C k M w))).symm.toAlgHom
  exact ⟨Module.Finite.trans ↥F' ↥(ModularCurve.igusaFunctionFieldX1C k M w), Algebra.IsSeparable.trans ↥k⟮t⟯ ↥F' ↥(ModularCurve.igusaFunctionFieldX1C k M w)⟩

end S_ModularCurve_exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_igusaFunctionFieldX1C
end P2MW
export P2MW.S_ModularCurve_exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_igusaFunctionFieldX1C (solution)
