-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_addEquiv_galois_map_toricPts_eq_map_finPts_eq_of_representsRelSubPic_of_abelianScheme
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/3e52fb61-72c9-54db-8ca0-86de1db2b197

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_CharacterLatticePairings
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_addEquiv_galois_map_toricPts_eq_map_finPts_eq_of_representsRelSubPic_of_ptsLaw_of_abelianScheme
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_relativeGroupLaw_mul_eq_mul_genPt_of_one_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_addEquiv_galois_map_toricPts_eq_map_finPts_eq_of_representsRelSubPic_of_abelianScheme
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice"

open scoped MatrixGroups

noncomputable section

namespace OTthin

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))

theorem hone_pic : ∀ {T : Scheme.{0}} (s : T ⟶ base p),
    ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).one s).1 = (O.L.one s).1 := by
  intro T s
  have h1 := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).one_natural (𝟙 _) s s (Category.comp_id s)
  have h2 := O.L.one_natural (𝟙 _) s s (Category.comp_id s)
  have e1 := congrArg Subtype.val h1
  have e2 := congrArg Subtype.val h2
  simp only [GoodReductionJacobian.schemeHomOverComp_coe] at e1 e2
  rw [← e1, ← e2, RepresentsRelSubPic.relativeGroupLaw_one]

theorem pts_picLaw : ∀ x y : JH M H, O.pts (x + y) =
    (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y) := by
  intro x y
  rw [O.pts_add]
  exact Subtype.ext (ModularCurve.JHNeronObjectAtP.relativeGroupLaw_mul_eq_mul_genPt_of_one_eq p M H hpM A hA Λ O
    (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD) (hone_pic p M H hpM hj 𝔛 A hA Λ O hD)
    (O.pts x) (O.pts y)).symm

end OTthin

end

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (Λ' : JHNeronObjectAtP.LevelData p M H hpM A) (O' : JHNeronObjectAtP p M H hpM A hA Λ')
    (hD' : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O'.G, O'.g, (O'.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O'.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hΛ' : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ'.f) :
    ∃ e : JH M H ≃+ JH M H,
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JH M H), e (σ • x) = σ • e x) ∧
      (∀ m : ℕ, 0 < m →
        (O'.toricPts m) = (O.toricPts m).map e.toAddMonoidHom ∧
        (O'.finPts m) = (O.finPts m).map e.toAddMonoidHom) :=
  ModularCurve.JHNeronObjectAtP.exists_addEquiv_galois_map_toricPts_eq_map_finPts_eq_of_representsRelSubPic_of_ptsLaw_of_abelianScheme
    p M H hpM hpM2 hj 𝔛 A hA Λ O hD (OTthin.pts_picLaw p M H hpM hj 𝔛 A hA Λ O hD) Λ' O' hD' hΛ' (OTthin.pts_picLaw p M H hpM hj 𝔛 A hA Λ' O' hD')

end S_ModularCurve_JHNeronObjectAtP_exists_addEquiv_galois_map_toricPts_eq_map_finPts_eq_of_representsRelSubPic_of_abelianScheme
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_addEquiv_galois_map_toricPts_eq_map_finPts_eq_of_representsRelSubPic_of_abelianScheme (solution)
