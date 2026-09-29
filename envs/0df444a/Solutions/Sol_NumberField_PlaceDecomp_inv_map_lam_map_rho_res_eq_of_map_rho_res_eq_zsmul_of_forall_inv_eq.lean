-- Prove2me | solution 1 for NumberField.PlaceDecomp.inv_map_lam_map_rho_res_eq_of_map_rho_res_eq_zsmul_of_forall_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/216a0681-6f5c-59b4-aa27-525339ccef82

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_NumberField_PlaceDecomp_natCard_decomp_eq_ramificationIdx_mul_inertiaDeg_mul_natCard_decomp
import Theorems.Thm_ExtCitation_LocalLevel_isLocalFundamentalClass_map_subtype
import Theorems.Thm_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass
import Theorems.Thm_ExtCitation_LocalLevel_finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq
import Theorems.Thm_IntermediateField_isSolvable_algEquiv_of_padic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_NumberField_PlaceDecomp_inv_map_lam_map_rho_res_eq_of_map_rho_res_eq_zsmul_of_forall_inv_eq
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology NumberField P2MW.S_NumberField_PlaceDecomp_inv_map_lam_map_rho_res_eq_of_map_rho_res_eq_zsmul_of_forall_inv_eq.NumberField IsDedekindDomain M4aHerbrand"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_inv_map_lam_map_rho_res_eq_of_map_rho_res_eq_zsmul_of_forall_inv_eq.NumberField.PlaceDecomp Pointwise"

set_option linter.unusedSectionVars false

namespace NumberField
p2m_export "NumberField" "place PlaceDecomp.decomp PlaceDecomp.actRingEquiv_apply PlaceDecomp.smul_def PlaceDecomp.coe_smul_units PlaceDecomp.natCard_decomp_eq_ramificationIdx_mul_inertiaDeg_mul_natCard_decomp"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp actRingEquiv_apply smul_def coe_smul_units natCard_decomp_eq_ramificationIdx_mul_inertiaDeg_mul_natCard_decomp"
namespace C7bBody
p2m_open "NumberField.PlaceDecomp NumberField"

theorem exists_isBase (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [MulSemiringAction G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) :
    ∃ (K : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] K), ExtCitation.LocalLevel.IsBase q L G K := by
  haveI : SMulCommClass G ℚ_[q] L := ⟨fun g c x => by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hG]⟩
  refine ⟨IntermediateField.lift (FixedPoints.intermediateField G : IntermediateField ℚ_[q] L), ?_, ?_⟩
  · exact FiniteDimensional.of_injective
      (IntermediateField.inclusion (IntermediateField.lift_le (FixedPoints.intermediateField G : IntermediateField ℚ_[q] L))).toLinearMap
      (fun a b h => (IntermediateField.inclusion
        (IntermediateField.lift_le (FixedPoints.intermediateField G : IntermediateField ℚ_[q] L))).toRingHom.injective h)
  · refine ⟨IntermediateField.lift_le _, fun x => ?_⟩
    rw [IntermediateField.mem_lift]
    exact Iff.rfl

section Solvable
open ExtCitation.LocalLevel

theorem isSolvable_layer (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀] (hK : IsBase q L G K₀) : Group.IsSolvable G := by
  classical
  haveI := Fintype.ofFinite G
  let E' : IntermediateField K₀ (PadicAlgCl q) := IntermediateField.extendScalars hK.le
  have memE : ∀ x : PadicAlgCl q, x ∈ E' ↔ x ∈ L := fun x => Iff.rfl
  let toL : E' → L := fun x => ⟨x.1, (memE x.1).1 x.2⟩
  let ofL : L → E' := fun y => ⟨y.1, (memE y.1).2 y.2⟩
  have hfix : ∀ (g : G) (r : K₀), g • toL (algebraMap K₀ E' r) = toL (algebraMap K₀ E' r) :=
    fun g r => (hK.mem_iff _).1 r.2 g

  let ψ₀ : G → (E' ≃ₐ[K₀] E') := fun g =>
    { toFun := fun x => ofL (g • toL x)
      invFun := fun x => ofL (g⁻¹ • toL x)
      left_inv := fun x => by
        change ofL (g⁻¹ • g • toL x) = x
        rw [← mul_smul, inv_mul_cancel, one_smul]
      right_inv := fun x => by
        change ofL (g • g⁻¹ • toL x) = x
        rw [← mul_smul, mul_inv_cancel, one_smul]
      map_mul' := fun x y => by
        change ofL (g • (toL x * toL y)) = ofL (g • toL x) * ofL (g • toL y)
        rw [smul_mul']
        rfl
      map_add' := fun x y => by
        change ofL (g • (toL x + toL y)) = ofL (g • toL x) + ofL (g • toL y)
        rw [smul_add]
        rfl
      commutes' := fun r => by
        change ofL (g • toL (algebraMap K₀ E' r)) = _
        rw [hfix] }
  have ψ₀_apply : ∀ (g : G) (x : E'), toL (ψ₀ g x) = g • toL x := fun g x => rfl
  let ψ : G →* (E' ≃ₐ[K₀] E') :=
    { toFun := ψ₀
      map_one' := by
        ext x
        change ((ofL ((1 : G) • toL x) : E') : PadicAlgCl q) = x
        rw [one_smul]
      map_mul' := fun g h => by
        ext x
        change ((ofL ((g * h) • toL x) : E') : PadicAlgCl q) = ((ofL (g • toL (ofL (h • toL x))) : E') : PadicAlgCl q)
        rw [mul_smul] }
  have hψ : Function.Injective ψ := by
    intro g h hgh
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro y
    have := congrArg (fun f : E' ≃ₐ[K₀] E' => toL (f (ofL y))) hgh
    exact this

  let eL : E' ≃ₗ[ℚ_[q]] L :=
    { toFun := toL, invFun := ofL, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  haveI : Module.Finite ℚ_[q] E' := Module.Finite.equiv eL.symm
  haveI : FiniteDimensional K₀ E' := Module.Finite.of_restrictScalars_finite ℚ_[q] K₀ E'
  have hdeg : Module.finrank K₀ E' = Fintype.card G := by
    have h1 := ExtCitation.LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq q L G hG K₀ hK.le hK.mem_iff
    have h2 := Module.finrank_mul_finrank ℚ_[q] K₀ E'
    rw [LinearEquiv.finrank_eq eL, h1, Nat.card_eq_fintype_card, mul_comm] at h2
    have hpos : 0 < Module.finrank ℚ_[q] K₀ := Module.finrank_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  have hcard : Fintype.card (E' ≃ₐ[K₀] E') = Module.finrank K₀ E' := by
    apply le_antisymm AlgEquiv.card_le
    rw [hdeg]
    exact Fintype.card_le_of_injective ψ hψ
  haveI : IsGalois K₀ E' := IsGalois.of_card_aut_eq_finrank K₀ E' (by rw [Nat.card_eq_fintype_card]; exact hcard)
  haveI := IntermediateField.isSolvable_algEquiv_of_padic q K₀ E'
  exact solvable_of_solvable_injective hψ

end Solvable

theorem coe_mapCocycles₂' {G H : Type} [Group G] [Group H] {A : Rep ℤ H} {B : Rep ℤ G}
    (f : G →* H) (φ : Rep.res f A ⟶ B) (x : cocycles₂ A) :
    ((mapCocycles₂ f φ x : cocycles₂ B) : G × G → B) = fun gh => φ.hom (x (f gh.1, f gh.2)) := by
  funext gh
  have := congrFun (mapCocycles₂_comp_i_apply f φ x) gh
  exact this

theorem val_mapCocycles₂ {G H : Type} [Group G] [Group H] {A : Rep ℤ H} {B : Rep ℤ G}
    (f : G →* H) (φ : Rep.res f A ⟶ B) (x : cocycles₂ A) :
    (mapCocycles₂ f φ x : cocycles₂ B).1 = fun gh => φ.hom (x (f gh.1, f gh.2)) :=
  coe_mapCocycles₂' f φ x

theorem isLocalFundamentalClass_map_mulEquiv (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q))
    (G G' : Type) [Group G] [Group G'] [MulSemiringAction G L] [MulDistribMulAction G (↥L)ˣ]
    [MulSemiringAction G' L] [MulDistribMulAction G' (↥L)ˣ]
    (ε : G' ≃* G) (hε : ∀ (g' : G') (x : L), g' • x = ε g' • x) (hεU : ∀ (g' : G') (v : (↥L)ˣ), g' • v = ε g' • v)
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ)) (hu : ExtCitation.LocalLevel.IsLocalFundamentalClass q L G K u)
    (ι₀ : Rep.res ε.toMonoidHom (Rep.ofMulDistribMulAction G (↥L)ˣ) ⟶ Rep.ofMulDistribMulAction G' (↥L)ˣ)
    (hι₀ : ∀ v, ι₀.hom v = v) :
    ExtCitation.LocalLevel.IsLocalFundamentalClass q L G' K ((groupCohomology.map ε.toMonoidHom ι₀ 2).hom u) := by
  intro M _ hLM Hg _ _ _ _ _ NL Nn _ _ e φ π d ι hι hfin hc

  let e₀ : G ≃* Hg ⧸ NL := ε.symm.trans e
  have d₀ : ExtCitation.LocalLevel.IsUnramOverlayerDatum q L G K M hLM Hg NL Nn e₀ φ π :=
    { smul_algebraMap := d.smul_algebraMap
      coe_smul_units := d.coe_smul_units
      mem_base_iff := d.mem_base_iff
      mem_layer_iff := d.mem_layer_iff
      coe_smul_eq := fun g h hh x => by
        have := d.coe_smul_eq (ε.symm g) h (by rw [hh]; rfl) x
        rwa [hε, MulEquiv.apply_symm_apply] at this
      card_quotient := d.card_quotient.trans (Nat.card_congr ε.toEquiv)
      mem_zpowers := d.mem_zpowers
      frobenius := d.frobenius
      smul_pi := d.smul_pi
      pi_mem := d.pi_mem
      norm_pi_lt := d.norm_pi_lt
      norm_le_norm_pi := d.norm_le_norm_pi }

  have hρε : ∀ (y : Hg) (v : Rep.ofMulDistribMulAction G (↥L)ˣ),
      (Rep.ofMulDistribMulAction G (↥L)ˣ).ρ (e₀.symm.toMonoidHom.comp (QuotientGroup.mk' NL) y) v =
        (Rep.ofMulDistribMulAction G' (↥L)ˣ).ρ (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL) y) v := by
    intro y v
    show Additive.ofMul ((ε (e.symm (QuotientGroup.mk' NL y))) • (Additive.toMul v : (↥L)ˣ)) =
      Additive.ofMul ((e.symm (QuotientGroup.mk' NL y)) • (Additive.toMul v : (↥L)ˣ))
    rw [hεU]
  let ιG : Rep.res (e₀.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (Rep.ofMulDistribMulAction G (↥L)ˣ) ⟶
      Rep.ofMulDistribMulAction Hg (↥M)ˣ :=
    Rep.ofHom ⟨ι.hom.toLinearMap, fun y => LinearMap.ext fun v => by
      show ι.hom ((Rep.ofMulDistribMulAction G (↥L)ˣ).ρ (e₀.symm.toMonoidHom.comp (QuotientGroup.mk' NL) y) v) =
        (Rep.ofMulDistribMulAction Hg (↥M)ˣ).ρ y (ι.hom v)
      rw [hρε]
      exact Rep.hom_comm_apply ι y v⟩
  have hιG : ∀ v, ιG.hom v = ι.hom v := fun _ => rfl
  have key := hu M hLM Hg NL Nn e₀ φ π d₀ ιG (fun v => hι v) hfin hc

  have hsame : (groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) ι 2).hom
      ((groupCohomology.map ε.toMonoidHom ι₀ 2).hom u) =
      (groupCohomology.map (e₀.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) ιG 2).hom u := by
    clear key hu
    induction u using groupCohomology.H2_induction_on with
    | _ z =>
      simp only [groupCohomology.H2π_comp_map_apply]
      congr 1
      apply Subtype.ext
      rw [val_mapCocycles₂, val_mapCocycles₂]
      funext gh
      rw [coe_mapCocycles₂', hιG]
      show ι.hom (ι₀.hom _) = ι.hom _
      rw [hι₀]
      rfl
  rw [hsame]
  exact key

end NumberField.PlaceDecomp.C7bBody

open NumberField.PlaceDecomp.C7bBody in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois ℚ F] [IsGalois E F]
    (r : (F ≃ₐ[E] F) →* (F ≃ₐ[ℚ] F)) (hr : ∀ (g : F ≃ₐ[E] F) (y : F), r g y = g y)
    (p : ℕ) [Fact p.Prime]
    (w : HeightOneSpectrum (𝓞 F)) (q : ℕ) [Fact q.Prime] (hw : ((q : ℕ) : 𝓞 F) ∈ w.asIdeal)
    (hpD : p ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ F w))

    (xℚ : groupCohomology.H2 (Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) Fˣ))
    (φ : Rep.res r (Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) Fˣ) ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ)
    (hφ : ∀ u : Fˣ, φ.hom (Additive.ofMul u) = Additive.ofMul u)
    (x : groupCohomology.H2 (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))
    (hx : x = (groupCohomology.map r φ 2).hom xℚ)
    (ρℚ : Rep.res (NumberField.PlaceDecomp.decomp ℚ F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) Fˣ) ⟶
        Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ F w) (w.adicCompletion F)ˣ)
    (hρℚ : ∀ u : Fˣ, ρℚ.hom (Additive.ofMul u) = Additive.ofMul (Units.map (algebraMap F (w.adicCompletion F)).toMonoidHom u))
    (ρ : Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hρ : ∀ u : Fˣ, ρ.hom (Additive.ofMul u) = Additive.ofMul (Units.map (algebraMap F (w.adicCompletion F)).toMonoidHom u))

    (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    [MulSemiringAction ↥(NumberField.PlaceDecomp.decomp ℚ F w) L'] [FaithfulSMul ↥(NumberField.PlaceDecomp.decomp ℚ F w) L']
    [MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ F w) (↥L')ˣ]
    (Φ' : w.adicCompletion F ≃+* L')
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ F w)) (y : ℚ_[q]), g • algebraMap ℚ_[q] L' y = algebraMap ℚ_[q] L' y)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ F w)) (y : w.adicCompletion F), Φ' (g • y) = g • Φ' y)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (_ : ExtCitation.LocalLevel.IsBase q L' ↥(NumberField.PlaceDecomp.decomp ℚ F w) K₀)
    (θ' : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ F w) (↥L')ˣ ⟶
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ F w) (w.adicCompletion F)ˣ)
    (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ'.hom (Additive.ofMul v)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ'.symm (v : L'))
    (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ F w) (↥L')ˣ))
    (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' ↥(NumberField.PlaceDecomp.decomp ℚ F w) K₀ u')
    (m : ℤ)
    (hm : (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ F w)) ρℚ 2).hom
          ((groupCohomology.map (NumberField.PlaceDecomp.decomp ℚ F w).subtype
            (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ℚ F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) Fˣ))) 2).hom xℚ) =
        m • ((Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ F w) / p) •
          (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ F w)) θ' 2).hom u'))

    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (lam : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (inv : ∀ H : Subgroup (F ≃ₐ[E] F),
      ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) →+
        AddCircle (1 : ℚ))
    (hloc : ∀ (L'' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L'']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L'']
        [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L'')ˣ]
        (Φ : w.adicCompletion F ≃+* L'')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ℚ_[q]),
          g • algebraMap ℚ_[q] L'' x = algebraMap ℚ_[q] L'' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (v : (↥L'')ˣ), ((g • v : (↥L'')ˣ) : L'') = g • (v : L''))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : w.adicCompletion F), Φ (g • x) = g • Φ x)
        (K₀'' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀'']
        (_ : ExtCitation.LocalLevel.IsBase q L'' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀'')
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L'')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ v : (↥L'')ˣ,
          ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (v : L''))
        (u'' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L'')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L'' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀'' u''),
        inv (NumberField.PlaceDecomp.decomp E F w)
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) lam 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u'')) =
          (((1 : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) : ℚ) : ℚ) : AddCircle (1 : ℚ))) :
    inv (NumberField.PlaceDecomp.decomp E F w)
        ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) lam 2).hom
          ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) ρ 2).hom
            ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype
              (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype
                (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))) 2).hom x))) =
      ((((Ideal.ramificationIdx' (Ideal.span {((q : ℕ) : ℤ)}) (Ideal.comap (algebraMap (𝓞 E) (𝓞 F)) w.asIdeal) *
            Ideal.inertiaDeg' (Ideal.span {((q : ℕ) : ℤ)}) (Ideal.comap (algebraMap (𝓞 E) (𝓞 F)) w.asIdeal) *
            ZMod.val (m : ZMod p) : ℕ) : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
  classical

  have hG1 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ F w)) (y : ℚ_[q]), g • algebraMap ℚ_[q] L' y = algebraMap ℚ_[q] L' y := by
    assumption
  have hG2 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L') := by
    assumption
  have hG3 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ F w)) (y : w.adicCompletion F), Φ' (g • y) = g • Φ' y := by
    assumption
  have hbaseG : ExtCitation.LocalLevel.IsBase q L' ↥(NumberField.PlaceDecomp.decomp ℚ F w) K₀ := by assumption
  have hθ'pin : ∀ v : (↥L')ˣ, ((Additive.toMul (θ'.hom (Additive.ofMul v)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ'.symm (v : L') := by
    assumption
  have hu'G : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' ↥(NumberField.PlaceDecomp.decomp ℚ F w) K₀ u' := by assumption

  have hreq : ∀ g : F ≃ₐ[E] F, ((r g : F ≃ₐ[ℚ] F) : F ≃+* F) = ((g : F ≃ₐ[E] F) : F ≃+* F) := fun g =>
    RingEquiv.ext (hr g)
  have hjmem : ∀ g : ↥(NumberField.PlaceDecomp.decomp E F w), r (g : F ≃ₐ[E] F) ∈ NumberField.PlaceDecomp.decomp ℚ F w := by
    intro g
    have hg := g.2
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    ext x
    rw [ValuationSubring.mem_smul_pointwise_iff_exists]
    conv_rhs => rw [← hg, ValuationSubring.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, (hr (g : F ≃ₐ[E] F) s).symm⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, hr (g : F ≃ₐ[E] F) s⟩
  let j : ↥(NumberField.PlaceDecomp.decomp E F w) →* ↥(NumberField.PlaceDecomp.decomp ℚ F w) :=
    { toFun := fun g => ⟨r g.1, hjmem g⟩
      map_one' := Subtype.ext (map_one r)
      map_mul' := fun a b => Subtype.ext (map_mul r a.1 b.1) }
  have hj : ∀ g : ↥(NumberField.PlaceDecomp.decomp E F w), ((j g : ↥(NumberField.PlaceDecomp.decomp ℚ F w)) : F ≃ₐ[ℚ] F) = r g.1 :=
    fun _ => rfl
  have hjinj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    apply AlgEquiv.ext
    intro y
    have := congrArg (fun s : ↥(NumberField.PlaceDecomp.decomp ℚ F w) => (s : F ≃ₐ[ℚ] F) y) h
    simpa [hj, hr] using this
  have hsmulF : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : w.adicCompletion F), (j g) • x = g • x := by
    intro g x
    rw [NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.smul_def]
    apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
    rw [NumberField.PlaceDecomp.actRingEquiv_apply, NumberField.PlaceDecomp.actRingEquiv_apply]
    have : ((((j g : ↥(NumberField.PlaceDecomp.decomp ℚ F w)) : F ≃ₐ[ℚ] F)) : F ≃+* F) = ((g : F ≃ₐ[E] F) : F ≃+* F) :=
      hreq g
    rw [this]
  have hsmulU : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : (w.adicCompletion F)ˣ), (j g) • x = g • x := by
    intro g x
    apply Units.ext
    rw [NumberField.PlaceDecomp.coe_smul_units, NumberField.PlaceDecomp.coe_smul_units, hsmulF]

  let ψ : Rep.res j (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ F w) (w.adicCompletion F)ˣ) ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ :=
    Rep.ofHom ⟨LinearMap.id, fun g => LinearMap.ext fun x => by
      show Additive.ofMul ((j g) • (Additive.toMul x : (w.adicCompletion F)ˣ)) =
        Additive.ofMul (g • (Additive.toMul x : (w.adicCompletion F)ˣ))
      rw [hsmulU]⟩
  have hψ : ∀ x, ψ.hom x = x := fun _ => rfl

  have hB : (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) ρ 2).hom
          ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype
            (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype
              (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))) 2).hom x) =
      (groupCohomology.map j ψ 2).hom
        ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ F w)) ρℚ 2).hom
          ((groupCohomology.map (NumberField.PlaceDecomp.decomp ℚ F w).subtype
            (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ℚ F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) Fˣ))) 2).hom xℚ)) := by
    subst hx
    induction xℚ using groupCohomology.H2_induction_on with
    | _ z =>
      simp only [groupCohomology.H2π_comp_map_apply]
      congr 1
      apply Subtype.ext
      rw [val_mapCocycles₂, val_mapCocycles₂]
      funext gh
      rw [coe_mapCocycles₂', coe_mapCocycles₂', coe_mapCocycles₂', coe_mapCocycles₂']

      show ρ.hom (φ.hom (z (r gh.1, r gh.2))) = ψ.hom (ρℚ.hom (z (r gh.1, r gh.2)))
      rw [hψ]
      generalize z (r gh.1, r gh.2) = t
      rw [show t = Additive.ofMul (Additive.toMul t) from rfl, hρℚ, hφ]
      exact hρ _

  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : Finite (F ≃ₐ[ℚ] F) := inferInstance
  haveI : Finite (F ≃ₐ[E] F) := inferInstance
  letI actH : MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E F w) L' := MulSemiringAction.compHom L' j
  letI actHU : MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L')ˣ := MulDistribMulAction.compHom (↥L')ˣ j
  have hsmulL : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : L'), g • y = (j g) • y := fun _ _ => rfl
  have hsmulLU : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : (↥L')ˣ), g • y = (j g) • y := fun _ _ => rfl
  haveI faithH : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E F w) L' :=
    ⟨fun {a b} h => hjinj (FaithfulSMul.eq_of_smul_eq_smul (α := L') fun y => by
      rw [← hsmulL, ← hsmulL]; exact h y)⟩
  have h1H : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : ℚ_[q]), g • algebraMap ℚ_[q] L' y = algebraMap ℚ_[q] L' y :=
    fun g y => by rw [hsmulL]; exact hG1 (j g) y
  have h2H : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L') :=
    fun g v => by rw [hsmulLU, hsmulL]; exact hG2 (j g) v
  have h3H : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : w.adicCompletion F), Φ' (g • y) = g • Φ' y :=
    fun g y => by rw [hsmulL, ← hsmulF]; exact hG3 (j g) y
  obtain ⟨K₀H, fdH, baseH⟩ := exists_isBase q L' (↥(NumberField.PlaceDecomp.decomp E F w)) h1H
  haveI := fdH

  let ΦM : (↥L')ˣ →* (w.adicCompletion F)ˣ := Units.map Φ'.symm.toRingHom.toMonoidHom
  have hΦM : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : (↥L')ˣ), ΦM (g • y) = g • ΦM y := by
    intro g y
    apply Units.ext
    show Φ'.symm ((g • y : (↥L')ˣ) : ↥L') = ((g • ΦM y : (w.adicCompletion F)ˣ) : w.adicCompletion F)
    rw [h2H g y, NumberField.PlaceDecomp.coe_smul_units]
    apply Φ'.injective
    rw [h3H g, RingEquiv.apply_symm_apply]
    congr 1
    exact (Φ'.apply_symm_apply _).symm
  let θH := M4aHerbrand.repHomOfMulEquivariant ΦM hΦM
  have hθH : ∀ y : (↥L')ˣ, ((Additive.toMul (θH.hom (Additive.ofMul y)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ'.symm (y : ↥L') :=
    fun y => rfl
  have hsolvH : Group.IsSolvable (↥(NumberField.PlaceDecomp.decomp E F w)) := isSolvable_layer q L' _ h1H K₀H baseH
  obtain ⟨uH, huH, huHuniq⟩ := ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F w)) h1H h2H hsolvH K₀H baseH

  have hinv := hloc L' Φ' h1H h2H h3H K₀H baseH θH hθH uH huH

  have hident : (groupCohomology.map j ψ 2).hom
      ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ F w)) θ' 2).hom u') =
      (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θH 2).hom uH := by

    let S : Subgroup ↥(NumberField.PlaceDecomp.decomp ℚ F w) := j.range
    let ε : ↥(NumberField.PlaceDecomp.decomp E F w) ≃* ↥S := MonoidHom.ofInjective hjinj
    have hεj : ∀ h : ↥(NumberField.PlaceDecomp.decomp E F w), ((ε h : ↥S) : ↥(NumberField.PlaceDecomp.decomp ℚ F w)) = j h :=
      fun _ => rfl
    have hεs : ∀ (h : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : L'), h • y = (ε h) • y := fun _ _ => rfl
    have hεU : ∀ (h : ↥(NumberField.PlaceDecomp.decomp E F w)) (v : (↥L')ˣ), h • v = (ε h) • v := fun _ _ => rfl
    have baseS : ExtCitation.LocalLevel.IsBase q L' ↥S K₀H := by
      refine ⟨baseH.le, fun y => (baseH.mem_iff y).trans ⟨fun h s => ?_, fun h t => ?_⟩⟩
      · obtain ⟨t, rfl⟩ := ε.surjective s
        rw [← hεs]; exact h t
      · rw [hεs]; exact h (ε t)
    have hsolvG : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp ℚ F w) :=
      isSolvable_layer q L' ↥(NumberField.PlaceDecomp.decomp ℚ F w) hG1 K₀ hbaseG
    have huS : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' ↥S K₀H
        ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ F w) (↥L')ˣ))) 2).hom u') :=
      ExtCitation.LocalLevel.isLocalFundamentalClass_map_subtype q L' ↥(NumberField.PlaceDecomp.decomp ℚ F w)
        hG1 hG2 hsolvG K₀ hbaseG u' hu'G S K₀H baseS

    let ι₀ : Rep.res ε.toMonoidHom (Rep.ofMulDistribMulAction ↥S (↥L')ˣ) ⟶
        Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L')ˣ :=
      Rep.ofHom ⟨LinearMap.id, fun h => LinearMap.ext fun v => rfl⟩
    have hι₀ : ∀ v, ι₀.hom v = v := fun _ => rfl
    have huE := isLocalFundamentalClass_map_mulEquiv q L' ↥S ↥(NumberField.PlaceDecomp.decomp E F w) ε hεs hεU K₀H _ huS ι₀ hι₀
    have heq := huHuniq _ huE

    have hθv : ∀ v : (↥L')ˣ, θ'.hom (Additive.ofMul v) = θH.hom (Additive.ofMul v) := by
      intro v
      have hU : Additive.toMul (θ'.hom (Additive.ofMul v)) = ΦM v := Units.ext (hθ'pin v)
      exact congrArg Additive.ofMul hU
    have hident' : ∀ y : groupCohomology.H2 (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ F w) (↥L')ˣ),
        (groupCohomology.map j ψ 2).hom ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ F w)) θ' 2).hom y) =
        (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θH 2).hom
          ((groupCohomology.map ε.toMonoidHom ι₀ 2).hom
            ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ F w) (↥L')ˣ))) 2).hom y)) := by
      intro y
      induction y using groupCohomology.H2_induction_on with
      | _ z =>
        erw [groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply,
          groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply]
        congr 1
        apply Subtype.ext
        rw [val_mapCocycles₂, val_mapCocycles₂]
        funext gh
        rw [coe_mapCocycles₂', coe_mapCocycles₂']
        erw [coe_mapCocycles₂']
        show ψ.hom (θ'.hom (z (j gh.1, j gh.2))) = θH.hom (ι₀.hom (z (j gh.1, j gh.2)))
        rw [hψ, hι₀]
        generalize z (j gh.1, j gh.2) = t
        exact hθv (Additive.toMul t)
    rw [hident' u', heq]

  rw [hB, hm, map_zsmul, map_nsmul, hident, map_zsmul, map_nsmul, map_zsmul, map_nsmul, hinv]

  have hcard := NumberField.PlaceDecomp.natCard_decomp_eq_ramificationIdx_mul_inertiaDeg_mul_natCard_decomp E F w q hw
  set eI := Ideal.ramificationIdx' (Ideal.span {((q : ℕ) : ℤ)}) (Ideal.comap (algebraMap (𝓞 E) (𝓞 F)) w.asIdeal) with heI
  set fI := Ideal.inertiaDeg' (Ideal.span {((q : ℕ) : ℤ)}) (Ideal.comap (algebraMap (𝓞 E) (𝓞 F)) w.asIdeal) with hfI
  set Gc := Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ F w) with hGc
  set Hc := Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) with hHc
  haveI : Fintype ↥(NumberField.PlaceDecomp.decomp E F w) := Fintype.ofFinite _
  have hH0 : (Hc : ℚ) ≠ 0 := by
    rw [hHc, Nat.cast_ne_zero, Nat.card_eq_fintype_card]
    exact Fintype.card_ne_zero
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨n, hn⟩ := hpD
  have hndiv : Gc / p = n := by rw [hn, Nat.mul_div_cancel_left _ (Fact.out : p.Prime).pos]
  rw [hndiv]

  have hnq : (n : ℚ) * p = (eI : ℚ) * fI * Hc := by
    have : p * n = eI * fI * Hc := by rw [← hn]; exact hcard
    exact_mod_cast (by rw [mul_comm] at this; exact this : n * p = eI * fI * Hc)

  have hv : (((m : ZMod p)).val : ℤ) = m % (p : ℤ) := ZMod.val_intCast m
  rw [← AddCircle.coe_nsmul, ← AddCircle.coe_zsmul, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  refine ⟨(eI : ℤ) * fI * (m / p), ?_⟩
  rw [zsmul_eq_mul, mul_one, nsmul_eq_mul, zsmul_eq_mul]
  push_cast
  rw [show (((m : ZMod p).val : ℕ) : ℚ) = ((m % (p : ℤ) : ℤ) : ℚ) by rw [← hv]; norm_cast]
  have hmod : ((m % (p : ℤ) : ℤ) : ℚ) = (m : ℚ) - (p : ℚ) * ((m / (p : ℤ) : ℤ) : ℚ) := by
    have := Int.emod_add_mul_ediv m p
    have h' : ((m % (p : ℤ) : ℤ) : ℚ) + (p : ℚ) * ((m / (p : ℤ) : ℤ) : ℚ) = (m : ℚ) := by exact_mod_cast this
    linarith
  rw [hmod]
  field_simp
  linear_combination (-(m : ℚ)) * hnq

end S_NumberField_PlaceDecomp_inv_map_lam_map_rho_res_eq_of_map_rho_res_eq_zsmul_of_forall_inv_eq
end P2MW
export P2MW.S_NumberField_PlaceDecomp_inv_map_lam_map_rho_res_eq_of_map_rho_res_eq_zsmul_of_forall_inv_eq (solution)
