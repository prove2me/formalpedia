-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isAffine_or_exists_isClosedImmersion_lt_of_not_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/37088c1f-ac7e-5ba0-9fd7-341fa2cbc569

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_PartialAction
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_GoodReductionJacobian_PartialAction_exists_isClosedImmersion_range_ne_univ_of_act_ne
import Theorems.Thm_GoodReductionJacobian_PartialAction_exists_defined_act_eq_of_forall_act_eq
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_connectedSpace_lt_of_range_ne_univ
import Theorems.Thm_GoodReductionJacobian_PartialAction_isAffine_of_forall_exists_defined_act_eq
import Theorems.Thm_GoodReductionJacobian_PartialAction_exists_compatible_stable_defined_one_of_not_isProper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isAffine_or_exists_isClosedImmersion_lt_of_not_isProper
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (g : ℕ) [SmoothOfRelativeDimension g f]
    (hG : ¬ IsProper f) :
    IsAffine G ∨
    ∃ (H : Scheme.{u}) (i : H ⟶ G) (LH : RelativeGroupLaw k (i ≫ f)) (h : ℕ),
      IsClosedImmersion i ∧ ConnectedSpace H ∧ SmoothOfRelativeDimension h (i ≫ f) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (LH.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) ∧
      1 ≤ h ∧ h < g := by
  haveI : Smooth f := SmoothOfRelativeDimension.smooth g f
  obtain ⟨V, hVne, P, p, hPs, hPl, hPi, ι, hιo, hι, a, hc, hu, ha, W, hW, hst, hWg, P₀, hP₀, he⟩ :=
    GoodReductionJacobian.PartialAction.exists_compatible_stable_defined_one_of_not_isProper k f L g hG
  haveI := hVne; haveI := hPs; haveI := hPl; haveI := hPi; haveI := hιo
  by_cases hmov : ∃ (γ₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hγ₀ : a.Defined γ₀ P₀), a.act γ₀ P₀ hγ₀ ≠ P₀
  · obtain ⟨γ₀, hγ₀, hne⟩ := hmov
    obtain ⟨H, i, LH, hi, hhom, hrange, hdim⟩ :=
      GoodReductionJacobian.PartialAction.exists_isClosedImmersion_range_ne_univ_of_act_ne k f L g p a hu ha W hW hWg hst
        P₀ hP₀ he γ₀ hγ₀ hne
    haveI := hi
    exact Or.inr (GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_connectedSpace_lt_of_range_ne_univ
      k f L g i LH hhom hrange hdim)
  · push_neg at hmov
    refine Or.inl (GoodReductionJacobian.PartialAction.isAffine_of_forall_exists_defined_act_eq k f L p V ι hι a hc
      hu ha P₀ (fun t γ => ?_))
    exact GoodReductionJacobian.PartialAction.exists_defined_act_eq_of_forall_act_eq k f L p a ha P₀ he
      (fun γ hd => hmov γ hd) t γ

end S_GoodReductionJacobian_RelativeGroupLaw_isAffine_or_exists_isClosedImmersion_lt_of_not_isProper
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isAffine_or_exists_isClosedImmersion_lt_of_not_isProper (solution)
