-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_linearMap_pointDerivations_forall_isShiftBy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/effab67f-bcb1-5087-aa54-f5fff4c7cf58

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_MvFormalGroup_IsShiftBy
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_isTangentCoordsOfPairAt
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_deformation_isFormalCoordinates_liftsCoordinates
import Theorems.Thm_MvFormalGroup_Deformation_existsUnique_isShiftBy
import Theorems.Thm_GoodReductionJacobian_BareDeformation_isShiftBy_of_isShiftBy_of_isRegluingBy_of_exists_d_eq_sub
import Theorems.Thm_GoodReductionJacobian_BareDeformation_isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_linearMap_pointDerivations_forall_isShiftBy
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal PresheafOfModules.ExteriorPower.instModulePresheafAb"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq MvFormalGroup.Points.mk.injEq"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.sizeOf_spec MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero GoodReductionJacobian.prodInr_comp_prodFst GoodReductionJacobian.RelativeGroupLaw.prod_inv GoodReductionJacobian.prodInl_comp_prodSnd GoodReductionJacobian.prodInr_comp_prodSnd GoodReductionJacobian.prodInl_comp_prodFst GoodReductionJacobian.prodFstPt_prodPairPt GoodReductionJacobian.prodFst_coe GoodReductionJacobian.prodSndPt_prodPairPt GoodReductionJacobian.RelativeGroupLaw.prod_one GoodReductionJacobian.prodPairPt_coe GoodReductionJacobian.prodPairPt_prodFstPt_prodSndPt GoodReductionJacobian.prodFstPt_coe GoodReductionJacobian.RelativeGroupLaw.prod_mul GoodReductionJacobian.prodSndPt_coe GoodReductionJacobian.prodSnd_coe AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply"
p2m_attr_erase "simp" "IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj"

set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_exists_linearMap_pointDerivations_forall_isShiftBy.GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover"

open scoped Quaternion TensorProduct NumberField

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw.FormalCoordinates RelativeGroupLaw AbelianSchemePropertyBundle BareDeformation RelativeGroupLaw.baseChange BareDeformation.exists_isRegluingBy_isTangentCoordsOfPairAt BareDeformation.exists_deformation_isFormalCoordinates_liftsCoordinates BareDeformation.isShiftBy_of_isShiftBy_of_isRegluingBy_of_exists_d_eq_sub BareDeformation.isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul"
namespace P2mKSLinear
p2m_open "GoodReductionJacobian"

theorem exists_comp_eq_of_forall_eq {k : Type} [Field k] {S E W : Type}
    [AddCommMonoid S] [Module k S] [AddCommMonoid E] [Module k E] [AddCommMonoid W] [Module k W]
    (q : S →ₗ[k] E) (Λ : S →ₗ[k] W) (h : ∀ c c', q c = q c' → Λ c = Λ c') :
    ∃ g : E →ₗ[k] W, ∀ c, g (q c) = Λ c := by
  classical
  letI : AddCommGroup E := Module.addCommMonoidToAddCommGroup k
  letI : AddCommGroup W := Module.addCommMonoidToAddCommGroup k
  have hT : ∀ t : ↥(LinearMap.range q), ∃ c : S, q c = (t : E) := fun t => LinearMap.mem_range.mp t.2
  choose cf hcf using hT
  have fadd : ∀ t t' : ↥(LinearMap.range q), Λ (cf (t + t')) = Λ (cf t) + Λ (cf t') := by
    intro t t'
    rw [← Λ.map_add]
    apply h
    rw [q.map_add, hcf, hcf, hcf, Submodule.coe_add]
  have fsmul : ∀ (r : k) (t : ↥(LinearMap.range q)), Λ (cf (r • t)) = r • Λ (cf t) := by
    intro r t
    rw [← Λ.map_smul]
    apply h
    rw [q.map_smul, hcf, hcf, Submodule.coe_smul]
  let f : ↥(LinearMap.range q) →ₗ[k] W :=
    { toFun := fun t => Λ (cf t), map_add' := fadd, map_smul' := fsmul }
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  refine ⟨g, fun c => ?_⟩
  have hmem : q c ∈ LinearMap.range q := ⟨c, rfl⟩
  have h1 : g (q c) = f ⟨q c, hmem⟩ := by rw [← hg]; rfl
  rw [h1]
  show Λ (cf ⟨q c, hmem⟩) = Λ c
  exact h _ _ (hcf ⟨q c, hmem⟩)

end GoodReductionJacobian.P2mKSLinear

theorem solution
    {q : ℕ} [Fact q.Prime]
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [IsAlgClosed (ResidueField B)]
    [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    (hsmall : RingHom.ker (algebraMap B B₁) * maximalIdeal B = ⊥)
    (hq : IsNilpotent ((q : ℕ) : B))
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁) (hc₁ : L₁.IsCommutative)
    (h₁ : AbelianSchemePropertyBundle B₁ f₁)
    (F : MvFormalGroup 2 B) [F.IsComm]
    (θ₁ : RelativeGroupLaw.FormalCoordinates f₁ 2) (hθ₁ : L₁.IsFormalCoordinates (F.map (algebraMap B B₁)) θ₁)
    (hinf₁ : ∀ (C : Type) [CommRing C] [Algebra B₁ C] (m : ℕ) (P : SchemeHomOver (Scheme.specOver (𝒪 := B₁) C) f₁),
      nsmulPt L₁ (Scheme.specOver (𝒪 := B₁) C) (q ^ m) P = L₁.one (Scheme.specOver (𝒪 := B₁) C) →
        ∃ J : Ideal C, IsNilpotent J ∧ L₁.IsInfinitesimal J P)
    (hheight : ∀ (k : Type) [Field k] (ρ : B →+* k), Function.Surjective ρ →
      Module.finrank k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range ((F.map ρ).nthSeries q))) = q ^ 4)
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    [Module (ResidueField B)ᵐᵒᵖ V] [IsCentralScalar (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))

    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f]
    (𝒰 : D₀.A.OrderedAffineCover) (i₀ : 𝒰.ι) (e₀ : Spec (CommRingCat.of B) ⟶ ↑(𝒰.U i₀)) (he₀ : e₀ ≫ (𝒰.U i₀).ι = (D₀.L.one (𝟙 _)).1)

    (e₁ : Spec (CommRingCat.of (ResidueField B)) ⟶ (((𝒰.baseChange D₀.f (ResidueField B)).U i₀) : Scheme.{0}))
    (he₁ : e₁ ≫ ((𝒰.baseChange D₀.f (ResidueField B)).U i₀).ι = ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).one (𝟙 _)).1)
    (σ : ∀ s : 𝒰.Idx 1,
      letI := algebraOfHom D₀.f (𝒰.inter s)
      ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s)) ≃+* Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s))
    (hσ₁ : ∀ (s : 𝒰.Idx 1) (x : Γ(D₀.A, 𝒰.inter s)),
      letI := algebraOfHom D₀.f (𝒰.inter s)
      σ s ((1 : (ResidueField B)) ⊗ₜ[B] x) =
        ((pullback D₀.f (specMap B (ResidueField B))).presheaf.map (homOfLE (𝒰.baseChange_inter_le D₀.f (ResidueField B) s)).op).hom
          (((pullback.fst D₀.f (specMap B (ResidueField B))).app (𝒰.inter s)).hom x))
    (hσ₂ : ∀ (s : 𝒰.Idx 1) (a : (ResidueField B)),
      letI := algebraOfHom D₀.f (𝒰.inter s)
      letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).inter s)
      σ s (a ⊗ₜ[B] (1 : Γ(D₀.A, 𝒰.inter s))) = algebraMap (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s) a)
    (G₀ : MvFormalGroup.Deformation (F.map (algebraMap B B₁)) B) [G₀.F.IsComm]
    (θ₀ : RelativeGroupLaw.FormalCoordinates D₀.f 2) (hθ₀ : D₀.L.IsFormalCoordinates G₀.F θ₀) (hl₀ : D₀.LiftsCoordinates θ₁ θ₀) :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
    ∃ lam : ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) (((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom
          (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).HSucc (𝒰.baseChange D₀.f (ResidueField B)) 0)) →ₗ[(ResidueField B)]
        (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] MvFormalGroup.firstOrderDeformationSpace (F.map (IsLocalRing.residue B))),
      ∀ (c : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) (((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom
          (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)))
    (hc : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ
        ∈ LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))
        (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
        (hτ : ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ (𝒰.inter s).ι)
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
            σ s (cs a ξ) = (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ s)
        (D : BareDeformation f₁ L₁ B) (hD : D₀.IsRegluingBy 𝒰 τ D)
        (G : MvFormalGroup.Deformation (F.map (algebraMap B B₁)) B) [G.F.IsComm]
        (θ : RelativeGroupLaw.FormalCoordinates D.f 2) (hθ : D.L.IsFormalCoordinates G.F θ) (hl : D.LiftsCoordinates θ₁ θ)
        (u : ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) (((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom
          (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).HSucc (𝒰.baseChange D₀.f (ResidueField B)) 0)))
        (hu : ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
          ∃ z : LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) (0 + 1)),
            (z : (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) (0 + 1)) =
              c.1 a ξ ∧
            u.1 a ξ
              = Submodule.Quotient.mk z),
        MvFormalGroup.Deformation.IsShiftBy V ι F (lam u) G₀ G := by
  classical

  letI instU := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)

  let Cx := OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))
  let 𝒰k := 𝒰.baseChange D₀.f (ResidueField B)
  let Ci := Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))
  let ev : Ci →+* ResidueField B :=
    (((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom
  let M1 := Module.Dual (ResidueField B) V →ₗ[ResidueField B] Cx.cochain 𝒰k 1
  let HH := Module.Dual (ResidueField B) V →ₗ[ResidueField B] Cx.HSucc 𝒰k 0
  let PD1 := Algebra.PointDerivations (ResidueField B) Ci ev M1
  let PDH := Algebra.PointDerivations (ResidueField B) Ci ev HH
  let Wt := Module.Dual (ResidueField B) V →ₗ[ResidueField B] MvFormalGroup.firstOrderDeformationSpace (F.map (IsLocalRing.residue B))

  let S : Submodule (ResidueField B) ↥PD1 :=
    { carrier := {c | ∀ (a : Ci) (ξ : Module.Dual (ResidueField B) V),
        (c : Ci →ₗ[ResidueField B] M1) a ξ ∈ LinearMap.ker (Cx.d 𝒰k 1)}
      add_mem' := by
        intro c c' hc hc' a ξ
        simp only [Set.mem_setOf_eq] at hc hc' ⊢
        rw [Submodule.coe_add, LinearMap.add_apply, LinearMap.add_apply]
        exact Submodule.add_mem _ (hc a ξ) (hc' a ξ)
      zero_mem' := by
        intro a ξ
        simp only [Submodule.coe_zero, LinearMap.zero_apply]
        exact Submodule.zero_mem _
      smul_mem' := by
        intro r c hc a ξ
        simp only [Set.mem_setOf_eq] at hc ⊢
        rw [Submodule.coe_smul, LinearMap.smul_apply, LinearMap.smul_apply]
        exact Submodule.smul_mem _ r (hc a ξ) }

  have hRG : ∀ c : ↥S, ∃ (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s))) (D : BareDeformation f₁ L₁ B),
      D₀.IsRegluingBy 𝒰 τ D ∧
      ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        ∃ cs : Ci → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ (𝒰.inter s).ι)
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Ci) (ξ : Module.Dual (ResidueField B) V),
            σ s (cs a ξ) = ((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) a ξ s :=
    fun c => GoodReductionJacobian.BareDeformation.exists_isRegluingBy_isTangentCoordsOfPairAt B B₁ hπ hker hsmall hq f₁ L₁ hc₁ h₁ F θ₁ hθ₁
      hinf₁ hheight hI V ι hι hιI D₀ 𝒰 i₀ e₀ he₀ e₁ he₁ σ hσ₁ hσ₂ (c : ↥PD1) c.2
  choose τf Df hDf hτf using hRG
  have hFE : ∀ c : ↥S, ∃ (G : MvFormalGroup.Deformation (F.map (algebraMap B B₁)) B) (θ : RelativeGroupLaw.FormalCoordinates (Df c).f 2),
      G.F.IsComm ∧ (Df c).L.IsFormalCoordinates G.F θ ∧ (Df c).LiftsCoordinates θ₁ θ :=
    fun c => GoodReductionJacobian.BareDeformation.exists_deformation_isFormalCoordinates_liftsCoordinates B B₁ hπ hker
      (F.map (algebraMap B B₁)) θ₁ hθ₁ (Df c)
  choose Gf θf hGc hθf hlf using hFE
  have hGT : ∀ c : ↥S, ∃! w : Wt, MvFormalGroup.Deformation.IsShiftBy V ι F w G₀ (Gf c) := fun c =>
    haveI := hGc c
    MvFormalGroup.Deformation.existsUnique_isShiftBy hI V ι hι hιI F G₀ (Gf c)
  choose wf hwf hwu using fun c => (hGT c)

  have hcomb : ∀ (c c' : ↥S) (r : ResidueField B), wf (c + r • c') = wf c + r • wf c' := by
    intro c c' r
    haveI := hGc c; haveI := hGc c'; haveI := hGc (c + r • c')
    symm
    apply hwu (c + r • c')
    exact GoodReductionJacobian.BareDeformation.isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul
      B B₁ hπ hker hsmall hq f₁ L₁ hc₁ h₁ F θ₁ hθ₁ hinf₁ hheight hI V ι hι hιI D₀ 𝒰 i₀ e₀ he₀ e₁ he₁ σ hσ₁ hσ₂ G₀ θ₀ hθ₀ hl₀
      r (c : ↥PD1) c.2 (c' : ↥PD1) c'.2 (τf c) (τf c') (τf (c + r • c')) (Df c) (Df c') (Df (c + r • c'))
      (hDf c) (hDf c') (hDf (c + r • c')) (hτf c) (hτf c') (hτf (c + r • c'))
      (Gf c) (θf c) (hθf c) (hlf c) (Gf c') (θf c') (hθf c') (hlf c') (Gf (c + r • c')) (θf (c + r • c')) (hθf _) (hlf _)
      (wf c) (wf c') (hwf c) (hwf c')
  have hzero : wf 0 = 0 := by
    have h := hcomb 0 0 1
    have e0 : (0 : ↥S) + (1 : ResidueField B) • (0 : ↥S) = 0 := by rw [smul_zero, add_zero]
    rw [e0, one_smul] at h

    have h2 : wf 0 + wf 0 = wf 0 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  have hadd : ∀ c c' : ↥S, wf (c + c') = wf c + wf c' := by
    intro c c'
    have h := hcomb c c' 1
    rwa [one_smul, one_smul] at h
  have hsmul : ∀ (r : ResidueField B) (c : ↥S), wf (r • c) = r • wf c := by
    intro r c
    have h := hcomb 0 c r
    rwa [zero_add, hzero, zero_add] at h
  let ΛS : ↥S →ₗ[ResidueField B] Wt :=
    { toFun := wf
      map_add' := hadd
      map_smul' := fun r c => hsmul r c }
  have hΛS : ∀ c : ↥S, ΛS c = wf c := fun c => rfl

  let K1 : Submodule (ResidueField B) (Cx.cochain 𝒰k (0 + 1)) := LinearMap.ker (Cx.d 𝒰k (0 + 1))
  let N : Submodule (ResidueField B) ↥K1 := (LinearMap.range (Cx.d 𝒰k 0)).comap K1.subtype
  let mkN : ↥K1 →ₗ[ResidueField B] Cx.HSucc 𝒰k 0 := N.mkQ
  have mk_congr : ∀ (x y : Cx.cochain 𝒰k (0 + 1)) (hx : x ∈ K1) (hy : y ∈ K1), x = y → mkN ⟨x, hx⟩ = mkN ⟨y, hy⟩ := by
    intro x y hx hy h; cases h; rfl
  have mk_add : ∀ (x y : Cx.cochain 𝒰k (0 + 1)) (hx : x ∈ K1) (hy : y ∈ K1) (hxy : x + y ∈ K1),
      mkN ⟨x + y, hxy⟩ = mkN ⟨x, hx⟩ + mkN ⟨y, hy⟩ := by
    intro x y hx hy hxy
    rw [← mkN.map_add]
    exact congrArg mkN (Subtype.ext rfl)
  have mk_smul : ∀ (r : ResidueField B) (x : Cx.cochain 𝒰k (0 + 1)) (hx : x ∈ K1) (hrx : r • x ∈ K1),
      mkN ⟨r • x, hrx⟩ = r • mkN ⟨x, hx⟩ := by
    intro r x hx hrx
    rw [← mkN.map_smul]
    exact congrArg mkN (Subtype.ext rfl)

  have cval : ∀ (c : ↥S) (a : Ci) (ξ : Module.Dual (ResidueField B) V), ((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) a ξ ∈ K1 :=
    fun c a ξ => c.2 a ξ
  have cadd_a : ∀ (c : ↥S) (a₁ a₂ : Ci) (ξ : Module.Dual (ResidueField B) V),
      ((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) (a₁ + a₂) ξ =
        ((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) a₁ ξ + ((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) a₂ ξ := by
    intro c a₁ a₂ ξ; rw [((c : ↥PD1) : Ci →ₗ[ResidueField B] M1).map_add]; rfl
  have csmul_a : ∀ (c : ↥S) (r : ResidueField B) (a : Ci) (ξ : Module.Dual (ResidueField B) V),
      ((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) (r • a) ξ = r • ((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) a ξ := by
    intro c r a ξ; rw [((c : ↥PD1) : Ci →ₗ[ResidueField B] M1).map_smul]; rfl
  have cadd_ξ : ∀ (c : ↥S) (a : Ci) (ξ₁ ξ₂ : Module.Dual (ResidueField B) V),
      ((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) a (ξ₁ + ξ₂) =
        ((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) a ξ₁ + ((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) a ξ₂ :=
    fun c a ξ₁ ξ₂ => (((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) a).map_add ξ₁ ξ₂
  have csmul_ξ : ∀ (c : ↥S) (a : Ci) (r : ResidueField B) (ξ : Module.Dual (ResidueField B) V),
      ((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) a (r • ξ) = r • ((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) a ξ :=
    fun c a r ξ => (((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) a).map_smul r ξ
  have cleib : ∀ (c : ↥S) (a b : Ci) (ξ : Module.Dual (ResidueField B) V),
      ((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) (a * b) ξ =
        ev a • ((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) b ξ + ev b • ((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) a ξ := by
    intro c a b ξ
    have h := (Algebra.PointDerivations.mem_iff _).mp (c : ↥PD1).2 a b
    rw [h]; rfl

  have cScoe_add : ∀ (c c' : ↥S) (a : Ci) (ξ : Module.Dual (ResidueField B) V),
      (((c + c' : ↥S) : ↥PD1) : Ci →ₗ[ResidueField B] M1) a ξ =
        ((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) a ξ + ((c' : ↥PD1) : Ci →ₗ[ResidueField B] M1) a ξ := fun _ _ _ _ => rfl
  have cScoe_smul : ∀ (r : ResidueField B) (c : ↥S) (a : Ci) (ξ : Module.Dual (ResidueField B) V),
      (((r • c : ↥S) : ↥PD1) : Ci →ₗ[ResidueField B] M1) a ξ = r • ((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) a ξ :=
    fun _ _ _ _ => rfl
  have qlin : ∀ c : ↥S, ∃ Q : Ci →ₗ[ResidueField B] HH, ∀ (a : Ci) (ξ : Module.Dual (ResidueField B) V),
      Q a ξ = mkN ⟨((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) a ξ, cval c a ξ⟩ := by
    intro c
    refine ⟨LinearMap.mk₂ (ResidueField B)
      (fun (a : Ci) (ξ : Module.Dual (ResidueField B) V) => mkN ⟨((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) a ξ, cval c a ξ⟩)
      ?_ ?_ ?_ ?_, fun a ξ => rfl⟩
    · intro a₁ a₂ ξ
      exact (mk_congr _ _ _ (K1.add_mem (cval c a₁ ξ) (cval c a₂ ξ)) (cadd_a c a₁ a₂ ξ)).trans (mk_add _ _ _ _ _)
    · intro r a ξ
      exact (mk_congr _ _ _ (K1.smul_mem r (cval c a ξ)) (csmul_a c r a ξ)).trans (mk_smul _ _ _ _)
    · intro a ξ₁ ξ₂
      exact (mk_congr _ _ _ (K1.add_mem (cval c a ξ₁) (cval c a ξ₂)) (cadd_ξ c a ξ₁ ξ₂)).trans (mk_add _ _ _ _ _)
    · intro r a ξ
      exact (mk_congr _ _ _ (K1.smul_mem r (cval c a ξ)) (csmul_ξ c a r ξ)).trans (mk_smul _ _ _ _)
  choose qf hqf using qlin
  have hqext : ∀ (Q Q' : Ci →ₗ[ResidueField B] HH), (∀ (a : Ci) (ξ : Module.Dual (ResidueField B) V),
      Q a ξ = Q' a ξ) → Q = Q' := by
    intro Q Q' h
    apply LinearMap.ext; intro a; apply LinearMap.ext; intro ξ
    exact h a ξ
  have hqadd : ∀ c c' : ↥S, qf (c + c') = qf c + qf c' := by
    intro c c'
    apply hqext; intro a ξ
    rw [hqf, LinearMap.add_apply, LinearMap.add_apply, hqf, hqf]
    exact (mk_congr _ _ _ (K1.add_mem (cval c a ξ) (cval c' a ξ)) (cScoe_add c c' a ξ)).trans (mk_add _ _ _ _ _)
  have hqsmul : ∀ (r : ResidueField B) (c : ↥S), qf (r • c) = r • qf c := by
    intro r c
    apply hqext; intro a ξ
    rw [hqf, LinearMap.smul_apply, LinearMap.smul_apply, hqf]
    exact (mk_congr _ _ _ (K1.smul_mem r (cval c a ξ)) (cScoe_smul r c a ξ)).trans (mk_smul _ _ _ _)
  let qS : ↥S →ₗ[ResidueField B] (Ci →ₗ[ResidueField B] HH) := { toFun := qf, map_add' := hqadd, map_smul' := hqsmul }
  have hqS : ∀ c : ↥S, qS c = qf c := fun c => rfl

  have hWDq : ∀ c c' : ↥S, qf c = qf c' → wf c = wf c' := by
    intro c c' hcc
    have hcob : ∀ (a : Ci) (ξ : Module.Dual (ResidueField B) V),
        ∃ b : Cx.cochain 𝒰k 0, Cx.d 𝒰k 0 b =
          ((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) a ξ - ((c' : ↥PD1) : Ci →ₗ[ResidueField B] M1) a ξ := by
      intro a ξ
      have h12 : mkN ⟨((c : ↥PD1) : Ci →ₗ[ResidueField B] M1) a ξ, cval c a ξ⟩ =
          mkN ⟨((c' : ↥PD1) : Ci →ₗ[ResidueField B] M1) a ξ, cval c' a ξ⟩ := by
        rw [← hqf c a ξ, ← hqf c' a ξ, hcc]
      have hmem := (Submodule.Quotient.eq N).mp h12
      rw [Submodule.mem_comap, LinearMap.mem_range] at hmem
      obtain ⟨b, hb⟩ := hmem
      exact ⟨b, by rw [hb]; rfl⟩
    haveI := hGc c; haveI := hGc c'
    apply hwu c'
    exact GoodReductionJacobian.BareDeformation.isShiftBy_of_isShiftBy_of_isRegluingBy_of_exists_d_eq_sub
      B B₁ hπ hker hsmall hq f₁ L₁ hc₁ h₁ F θ₁ hθ₁ hinf₁ hheight hI V ι hι hιI D₀ 𝒰 i₀ e₀ he₀ e₁ he₁ σ hσ₁ hσ₂ G₀ θ₀ hθ₀ hl₀
      (c : ↥PD1) c.2 (c' : ↥PD1) c'.2 (τf c) (τf c') (Df c) (Df c') (hDf c) (hDf c') (hτf c) (hτf c') hcob
      (Gf c) (θf c) (hθf c) (hlf c) (Gf c') (θf c') (hθf c') (hlf c') (wf c) (hwf c)

  obtain ⟨g, hlam⟩ := GoodReductionJacobian.P2mKSLinear.exists_comp_eq_of_forall_eq qS ΛS
    (fun (c c' : ↥S) (hcc : qS c = qS c') =>
      (hΛS c).trans ((hWDq c c' (((hqS c).symm.trans hcc).trans (hqS c'))).trans (hΛS c').symm))

  have hlam' : ∀ c : ↥S, g (qf c) = wf c := fun c => (congrArg g (hqS c)).symm.trans ((hlam c).trans (hΛS c))
  refine ⟨g.comp PDH.subtype, ?_⟩
  intro c hc τ hτ D hD G instG θ hθ hl u hu
  let cS : ↥S := ⟨c, hc⟩
  have huq : ((u : ↥PDH) : Ci →ₗ[ResidueField B] HH) = qf cS := by
    apply hqext; intro a ξ
    rw [hqf]
    exact (hu a ξ).elim (fun z hz => hz.2.trans (congrArg mkN (Subtype.ext hz.1)))
  have hgl : (g.comp PDH.subtype) u = wf cS := by
    rw [LinearMap.comp_apply, Submodule.subtype_apply, huq, hlam']
  rw [hgl]
  haveI := hGc cS
  have hcob0 : ∀ (a : Ci) (ξ : Module.Dual (ResidueField B) V),
      ∃ b : Cx.cochain 𝒰k 0, Cx.d 𝒰k 0 b =
        ((cS : ↥PD1) : Ci →ₗ[ResidueField B] M1) a ξ - (c : Ci →ₗ[ResidueField B] M1) a ξ :=
    fun a ξ => ⟨0, by rw [map_zero]; exact (sub_self _).symm⟩
  exact GoodReductionJacobian.BareDeformation.isShiftBy_of_isShiftBy_of_isRegluingBy_of_exists_d_eq_sub
    B B₁ hπ hker hsmall hq f₁ L₁ hc₁ h₁ F θ₁ hθ₁ hinf₁ hheight hI V ι hι hιI D₀ 𝒰 i₀ e₀ he₀ e₁ he₁ σ hσ₁ hσ₂ G₀ θ₀ hθ₀ hl₀
    (cS : ↥PD1) cS.2 c hc (τf cS) τ (Df cS) D (hDf cS) hD (hτf cS) hτ hcob0
    (Gf cS) (θf cS) (hθf cS) (hlf cS) G θ hθ hl (wf cS) (hwf cS)

end S_GoodReductionJacobian_BareDeformation_exists_linearMap_pointDerivations_forall_isShiftBy
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_linearMap_pointDerivations_forall_isShiftBy (solution)
