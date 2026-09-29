-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.eq_schemeHomOverId_of_forall_schemeHomOverComp_eq_quotient_of_isDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/7919c6ba-b243-5948-ba92-592f8114698c

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_opens_forall_comp_eq_comp_of_forall_comp_eq_comp
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isClosed_setOf_forall_comp_eq_comp
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_of_one_comp_eq_one_comp_of_forall_comp_eq_comp_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_schemeHomOverId_of_forall_schemeHomOverComp_eq_quotient_of_isDomain
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

noncomputable section

namespace RigidConnT

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

def reidx {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    letI := L.pointGroup t; letI := L.pointGroup t'
    SchemeHomOver t f →* SchemeHomOver t' f :=
  letI := L.pointGroup t; letI := L.pointGroup t'
  MonoidHom.mk' (GoodReductionJacobian.schemeHomOverComp ψ hψ) (fun x y => L.mul_natural t t' ψ hψ x y)

theorem inv_natural {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t; letI := L.pointGroup t'
  exact (reidx L t t' ψ hψ).map_inv x

def tauPt (σ : SchemeHomOver f f) : SchemeHomOver f f := L.mul f σ (L.inv f (schemeHomOverId f))

def unitPt : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f := L.one (𝟙 _)

theorem fixed_iff {T : Scheme.{0}} (σ : SchemeHomOver f f) (x : T ⟶ A) :
    x ≫ σ.1 = x ↔ x ≫ (tauPt L σ).1 = x ≫ f ≫ (unitPt L).1 := by
  let t : T ⟶ Spec (CommRingCat.of R) := x ≫ f
  letI := L.pointGroup f; letI := L.pointGroup t
  have hx : x ≫ f = t := rfl

  have h1 : GoodReductionJacobian.schemeHomOverComp x hx (tauPt L σ) =
      L.mul t (GoodReductionJacobian.schemeHomOverComp x hx σ)
        (L.inv t (GoodReductionJacobian.schemeHomOverComp x hx (schemeHomOverId f))) := by
    rw [tauPt, L.mul_natural, inv_natural]

  have h2 : GoodReductionJacobian.schemeHomOverComp (x ≫ f) (Category.comp_id _) (unitPt L) = L.one t :=
    L.one_natural _ _ _ _
  have hid : GoodReductionJacobian.schemeHomOverComp x hx (schemeHomOverId f) = ⟨x, hx⟩ := by
    apply Subtype.ext; simp
  constructor
  · intro hσx
    have hσ' : GoodReductionJacobian.schemeHomOverComp x hx σ = ⟨x, hx⟩ := Subtype.ext (by simpa using hσx)
    have : GoodReductionJacobian.schemeHomOverComp x hx (tauPt L σ) = L.one t := by
      rw [h1, hσ', hid]; exact L.mul_inv_cancel t _
    have e1 := congrArg Subtype.val this
    have e2 := congrArg Subtype.val h2
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc] at e1 e2
    rw [e1, ← e2]
  · intro hτx
    have : GoodReductionJacobian.schemeHomOverComp x hx (tauPt L σ) = L.one t := by
      rw [← h2]; apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc]
      exact hτx
    rw [h1, hid] at this

    have hab : GoodReductionJacobian.schemeHomOverComp x hx σ = ⟨x, hx⟩ := by
      have := this
      change (GoodReductionJacobian.schemeHomOverComp x hx σ) * (⟨x, hx⟩ : SchemeHomOver t f)⁻¹ = 1 at this
      exact mul_inv_eq_one.mp this
    have := congrArg Subtype.val hab
    simpa using this

theorem one_comp_eq_of_hom (σ : SchemeHomOver f f)
    (hσ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) σ =
        L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ)) :
    (unitPt L).1 ≫ σ.1 = (unitPt L).1 := by
  letI := L.pointGroup (𝟙 (Spec (CommRingCat.of R)))
  have h := hσ (𝟙 _) 1 1
  change NeronModelInfra.schemeHomOverComp ((1 : SchemeHomOver (𝟙 _) f) * 1) σ =
    NeronModelInfra.schemeHomOverComp 1 σ * NeronModelInfra.schemeHomOverComp 1 σ at h
  rw [mul_one] at h
  have h' : NeronModelInfra.schemeHomOverComp (1 : SchemeHomOver (𝟙 _) f) σ = 1 :=
    mul_left_cancel (h.symm.trans (mul_one _).symm)
  exact congrArg Subtype.val h'

theorem main {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (hA : AbelianSchemePropertyBundle R f)
    (L : RelativeGroupLaw R f) (σ : SchemeHomOver f f)
    (hσ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) σ =
        L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))
    (𝔭 : Ideal R) [𝔭.IsMaximal]
    (hfix : ∀ (K : Type) [Field K] [IsAlgClosed K] (κ : R ⧸ 𝔭 →+* K)
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (κ.comp (Ideal.Quotient.mk 𝔭)))) f),
      NeronModelInfra.schemeHomOverComp x σ = x) :
    σ = NeronModelInfra.schemeHomOverId f := by
  classical
  haveI : IsProper f := hA.proper
  let τ : A ⟶ A := (tauPt L σ).1
  let e₁ : Spec (CommRingCat.of R) ⟶ A := (unitPt L).1
  have hτ : τ ≫ f = f := (tauPt L σ).2
  have he₁ : e₁ ≫ f = 𝟙 _ := (unitPt L).2
  have heσ : e₁ ≫ σ.1 = e₁ := one_comp_eq_of_hom L σ hσ
  have heτ : e₁ ≫ τ = e₁ := by
    have := (fixed_iff L σ e₁).mp heσ
    rw [this, ← Category.assoc, he₁, Category.id_comp]

  let Z : Set ↥(Spec (CommRingCat.of R)) := {s | ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ A),
    f.base (x.base (IsLocalRing.closedPoint K)) = s → x ≫ τ = x ≫ f ≫ e₁}
  have hZc : IsClosed Z :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.isClosed_setOf_forall_comp_eq_comp hA f τ hτ e₁ he₁
  have hZo : IsOpen Z := by
    rw [isOpen_iff_forall_mem_open]
    intro s hs
    obtain ⟨U, hsU, hU⟩ := GoodReductionJacobian.AbelianSchemePropertyBundle.exists_opens_forall_comp_eq_comp_of_forall_comp_eq_comp
      hA f τ hτ e₁ he₁ e₁ he₁ heτ s hs
    exact ⟨U, fun s' hs' K _ _ x hx => hU K x (hx ▸ hs'), U.isOpen, hsU⟩

  have h𝔭 : (⟨𝔭, inferInstance⟩ : PrimeSpectrum R) ∈ Z := by
    intro K _ _ x hx
    obtain ⟨φ, hφ⟩ : ∃ φ : R →+* K, x ≫ f = Spec.map (CommRingCat.ofHom φ) :=
      ⟨(Spec.preimage (x ≫ f)).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
    have hpt : (Spec.map (CommRingCat.ofHom φ)).base (IsLocalRing.closedPoint K) = ⟨𝔭, inferInstance⟩ := by
      rw [← hφ]; exact hx
    have hker : ∀ r ∈ 𝔭, φ r = 0 := by
      intro r hr
      have hr' : r ∈ ((Spec.map (CommRingCat.ofHom φ)).base (IsLocalRing.closedPoint K)).asIdeal := by
        rw [hpt]; exact hr
      change φ r ∈ IsLocalRing.maximalIdeal K at hr'
      rwa [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hr'
    let κ : R ⧸ 𝔭 →+* K := Ideal.Quotient.lift 𝔭 φ hker
    have hκ : κ.comp (Ideal.Quotient.mk 𝔭) = φ := Ideal.Quotient.lift_comp_mk 𝔭 φ hker
    have hxf : x ≫ f = Spec.map (CommRingCat.ofHom (κ.comp (Ideal.Quotient.mk 𝔭))) := by rw [hκ]; exact hφ
    have := congrArg Subtype.val (hfix K κ ⟨x, hxf⟩)
    simp only [NeronModelInfra.schemeHomOverComp_coe] at this
    exact (fixed_iff L σ x).mp this

  have hZ : Z = Set.univ := IsClopen.eq_univ ⟨hZc, hZo⟩ ⟨_, h𝔭⟩

  apply Subtype.ext
  rw [schemeHomOverId_coe]
  refine GoodReductionJacobian.AbelianSchemePropertyBundle.eq_of_one_comp_eq_one_comp_of_forall_comp_eq_comp_of_isAlgClosed
    hA L σ.1 (𝟙 A) σ.2 (Category.id_comp _) ?_ ?_
  · rw [Category.comp_id]; exact heσ
  · intro K _ _ x
    rw [Category.comp_id]
    have hmem : f.base (x.base (IsLocalRing.closedPoint K)) ∈ Z := by rw [hZ]; trivial
    exact (fixed_iff L σ x).mpr (hmem K x rfl)

end RigidConnT

end

theorem solution
    {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (hA : AbelianSchemePropertyBundle R f)
    (L : RelativeGroupLaw R f) (σ : SchemeHomOver f f)
    (hσ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) σ =
        L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))
    (𝔭 : Ideal R) [𝔭.IsMaximal]
    (hfix : ∀ (K : Type) [Field K] [IsAlgClosed K] (κ : R ⧸ 𝔭 →+* K)
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (κ.comp (Ideal.Quotient.mk 𝔭)))) f),
      NeronModelInfra.schemeHomOverComp x σ = x) :
    σ = NeronModelInfra.schemeHomOverId f :=
  RigidConnT.main hA L σ hσ 𝔭 hfix

#print axioms solution

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_schemeHomOverId_of_forall_schemeHomOverComp_eq_quotient_of_isDomain
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_schemeHomOverId_of_forall_schemeHomOverComp_eq_quotient_of_isDomain (solution)
