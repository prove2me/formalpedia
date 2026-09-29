-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/4958d09e-2b6e-5aad-bb95-41a7e7884bcc

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
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_eq_of_muBaseChange_residue_comp_eq
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_LevelData_exists_ringHom_comp_eq_algebraMap_and_sigmaA_eq_specMap
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_mul_eq_mul_of_one_eq_of_abelianSchemePropertyBundle
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_genericFibre
import Definitions.Def_JacJ1Iface
import Theorems.Thm_AlgebraicGeometry_SplitTorus_exists_addEquiv_eq_specMap_mapDomain_comp_of_range_eq
import Theorems.Thm_AlgebraicGeometry_SplitTorus_exists_schemeHomOverComp_eq_of_isClosedImmersion_torusStr_of_eq
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice"

open scoped MatrixGroups

noncomputable section

namespace TRL3

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring ℚ̄} {hA : A.LiesOverPrime p} [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A} (O : JHNeronObjectAtP p M H hpM A hA Λ)
  {Λ' : JHNeronObjectAtP.LevelData p M H hpM A} (O' : JHNeronObjectAtP p M H hpM A hA Λ')
  (ψ : SchemeHomOver O.g O'.g) (ψinv : SchemeHomOver O'.g O.g)
  (hψ₁ : ψ.1 ≫ ψinv.1 = 𝟙 _) (hψ₂ : ψinv.1 ≫ ψ.1 = 𝟙 _)
  (hψL : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g),
      NeronModelInfra.schemeHomOverComp (O.L.mul s x y) ψ =
        O'.L.mul s (NeronModelInfra.schemeHomOverComp x ψ) (NeronModelInfra.schemeHomOverComp y ψ))

theorem sigmaA_eq (Λ Λ' : JHNeronObjectAtP.LevelData p M H hpM A) : Λ'.σA = Λ.σA := by
  obtain ⟨ρ, hρ, hσ⟩ := JHNeronObjectAtP.LevelData.exists_ringHom_comp_eq_algebraMap_and_sigmaA_eq_specMap p M H hpM A Λ
  obtain ⟨ρ', hρ', hσ'⟩ := JHNeronObjectAtP.LevelData.exists_ringHom_comp_eq_algebraMap_and_sigmaA_eq_specMap p M H hpM A Λ'
  have : ρ' = ρ := RingHom.ext fun r => A.subtype_injective (by
    change (A.subtype.comp ρ') r = (A.subtype.comp ρ) r
    rw [hρ, hρ'])
  rw [hσ', hσ, this]

include hψ₁ hψ₂ hψL in
theorem inv_mul {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O'.g) :
    NeronModelInfra.schemeHomOverComp (O'.L.mul s x y) ψinv =
      O.L.mul s (NeronModelInfra.schemeHomOverComp x ψinv) (NeronModelInfra.schemeHomOverComp y ψinv) := by
  have hx : x = NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x ψinv) ψ :=
    Subtype.ext (by simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, hψ₂, Category.comp_id])
  have hy : y = NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp y ψinv) ψ :=
    Subtype.ext (by simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, hψ₂, Category.comp_id])
  conv_lhs => rw [hx, hy, ← hψL]
  apply Subtype.ext
  simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, hψ₁, Category.comp_id]

theorem mul_coe_congr {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of R)} (e : t = t')
    (x y : SchemeHomOver t f) (x' y' : SchemeHomOver t' f) (hx : x.1 = x'.1) (hy : y.1 = y'.1) :
    (L.mul t x y).1 = (L.mul t' x' y').1 := by
  subst e
  rw [Subtype.ext hx, Subtype.ext hy]

def transportσ (h : Λ'.σA = Λ.σA) : pullback O.g Λ'.σA ≅ pullback O.g Λ.σA := pullback.congrHom rfl h

@[scoped simp] theorem transportσ_hom_fst (h : Λ'.σA = Λ.σA) : (transportσ O h).hom ≫ pullback.fst O.g Λ.σA = pullback.fst O.g Λ'.σA := by
  simp only [transportσ, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]

@[scoped simp] theorem transportσ_hom_snd (h : Λ'.σA = Λ.σA) : (transportσ O h).hom ≫ pullback.snd O.g Λ.σA = pullback.snd O.g Λ'.σA := by
  simp only [transportσ, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]

def psiInvA : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ'.σA O'.g) (RelativeGroupLaw.baseChangeStr Λ.σA O.g) :=
  ⟨(fibreRestrictAlong Λ'.σA O.g O'.g ψinv).1 ≫ (transportσ O (sigmaA_eq Λ Λ')).hom, by
    change (_ ≫ _) ≫ pullback.snd O.g Λ.σA = pullback.snd O'.g Λ'.σA
    rw [Category.assoc, transportσ_hom_snd, fibreRestrictAlong_coe_comp_snd]⟩

theorem psiInvA_fst : (psiInvA O O' ψinv).1 ≫ pullback.fst O.g Λ.σA = pullback.fst O'.g Λ'.σA ≫ ψinv.1 := by
  change ((fibreRestrictAlong Λ'.σA O.g O'.g ψinv).1 ≫ _) ≫ _ = _
  rw [Category.assoc, transportσ_hom_fst, fibreRestrictAlong_coe_comp_fst]

theorem psiInvA_snd : (psiInvA O O' ψinv).1 ≫ pullback.snd O.g Λ.σA = pullback.snd O'.g Λ'.σA := (psiInvA O O' ψinv).2

include hψ₁ hψ₂ hψL in

theorem psiInvA_mul {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥A))
    (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ'.σA O'.g)) :
    NeronModelInfra.schemeHomOverComp ((O'.L.baseChange Λ'.σA).mul s x y) (psiInvA O O' ψinv) =
      (O.L.baseChange Λ.σA).mul s (NeronModelInfra.schemeHomOverComp x (psiInvA O O' ψinv))
        (NeronModelInfra.schemeHomOverComp y (psiInvA O O' ψinv)) := by

  apply Subtype.ext
  apply pullback.hom_ext
  ·
    have key := congrArg Subtype.val (inv_mul O O' ψ ψinv hψ₁ hψ₂ hψL (s ≫ Λ'.σA)
      (RelativeGroupLaw.baseChangePointToBase Λ'.σA x) (RelativeGroupLaw.baseChangePointToBase Λ'.σA y))
    rw [NeronModelInfra.schemeHomOverComp_coe, ← RelativeGroupLaw.baseChangePointToBase_mul,
      RelativeGroupLaw.baseChangePointToBase_coe] at key

    rw [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, psiInvA_fst, ← Category.assoc, key]

    rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
    refine mul_coe_congr O.L (by rw [sigmaA_eq Λ Λ']) _ _ _ _ ?_ ?_
    · simp only [NeronModelInfra.schemeHomOverComp_coe, RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc, psiInvA_fst]
    · simp only [NeronModelInfra.schemeHomOverComp_coe, RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc, psiInvA_fst]
  · rw [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, psiInvA_snd]
    rw [((O'.L.baseChange Λ'.σA).mul s x y).2]
    exact (((O.L.baseChange Λ.σA).mul s _ _).2).symm

section Reduce

variable {t t' : ℕ}

def reduceMod (M₀ : (Fin t' → ℤ) →+ (Fin t → ℤ)) (m : ℕ) : (Fin t' → ZMod m) →+ (Fin t → ZMod m) :=
  (Matrix.mulVecLin (Matrix.of fun (j : Fin t) (i : Fin t') => ((M₀ (Pi.single i 1) j : ℤ) : ZMod m))).toAddMonoidHom

abbrev castPi (n m : ℕ) : (Fin n → ℤ) →+ (Fin n → ZMod m) :=
  AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin n => ℤ) i)

@[scoped simp] theorem castPi_apply (n m : ℕ) (v : Fin n → ℤ) (i : Fin n) : castPi n m v i = ((v i : ℤ) : ZMod m) := rfl

theorem reduceMod_comp_castPi (M₀ : (Fin t' → ℤ) →+ (Fin t → ℤ)) (m : ℕ) :
    (reduceMod M₀ m).comp (castPi t' m) = (castPi t m).comp M₀ := by

  have key : ((reduceMod M₀ m).comp (castPi t' m)).toIntLinearMap = ((castPi t m).comp M₀).toIntLinearMap := by
    refine (Pi.basisFun ℤ (Fin t')).ext fun i => ?_
    ext j
    simp only [Pi.basisFun_apply, AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_comp, Function.comp_apply, castPi_apply,
      reduceMod, LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]

    rw [Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same, Int.cast_one, mul_one]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, Int.cast_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  exact AddMonoidHom.toIntLinearMap_injective key

end Reduce

section Lift

variable (m : ℕ) (hm : 0 < m) (Mbar : (Fin O'.toricRank → ZMod m) →+ (Fin O.toricRank → ZMod m))

abbrev specMbar : muScheme ↥A O.toricRank m ⟶ muScheme ↥A O'.toricRank m :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom ↥A Mbar))

theorem specMbar_comp_muStr : specMbar O O' m Mbar ≫ muStr ↥A O'.toricRank m = muStr ↥A O.toricRank m := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar).comp_algebraMap

def vLift : SchemeHomOver (muStr ↥A O.toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA O.g) :=
  ⟨specMbar O O' m Mbar ≫ (O'.toricLift m hm).1 ≫ (psiInvA O O' ψinv).1, by
    change (_ ≫ _ ≫ _) ≫ pullback.snd O.g Λ.σA = _
    rw [Category.assoc, Category.assoc, psiInvA_snd, (O'.toricLift m hm).2, specMbar_comp_muStr]⟩

theorem muPt_comp_specMbar (χ : muCoord ↥A O.toricRank m →ₐ[↥A] ℚ̄) :
    (muPt A O.toricRank m χ).1 ≫ specMbar O O' m Mbar =
      (muPt A O'.toricRank m (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar))).1 := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem comp_muPt_vLift (χ : muCoord ↥A O.toricRank m →ₐ[↥A] ℚ̄) :
    NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ) (vLift O O' ψinv m hm Mbar) =
      NeronModelInfra.schemeHomOverComp
        (NeronModelInfra.schemeHomOverComp (muPt A O'.toricRank m (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar)))
          (O'.toricLift m hm)) (psiInvA O O' ψinv) := by
  apply Subtype.ext
  simp only [NeronModelInfra.schemeHomOverComp_coe, vLift, ← Category.assoc, muPt_comp_specMbar]

include hψ₁ hψ₂ hψL in

theorem vLift_mul (χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] ℚ̄)) :
    NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m (χ * χ').ofConv) (vLift O O' ψinv m hm Mbar) =
      (O.L.baseChange Λ.σA).mul _
        (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ.ofConv) (vLift O O' ψinv m hm Mbar))
        (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ'.ofConv) (vLift O O' ψinv m hm Mbar)) := by
  rw [comp_muPt_vLift, comp_muPt_vLift, comp_muPt_vLift]

  have hconv : (χ * χ').ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar) =
      (WithConv.toConv (χ.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar)) *
        WithConv.toConv (χ'.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar))).ofConv :=
    AlgHom.convMul_comp_bialgHom_distrib χ χ' (AddMonoidAlgebra.mapDomainBialgHom ↥A Mbar)
  rw [hconv, O'.toricLift_mul m hm, psiInvA_mul O O' ψ ψinv hψ₁ hψ₂ hψL]

variable (Mx : (Fin O'.toricRank → ℤ) →+ (Fin O.toricRank → ℤ))

theorem muBaseChange_comp_specMbar :
    muBaseChange (IsLocalRing.residue ↥A) O.toricRank m ≫ specMbar O O' m Mbar =
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) Mbar)) ≫
        muBaseChange (IsLocalRing.residue ↥A) O'.toricRank m := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    AddMonoidAlgebra.mapRingHom_comp_mapDomainRingHom]

theorem specMbar_comp_muToTorus (hred : Mbar.comp (castPi O'.toricRank m) = (castPi O.toricRank m).comp Mx) :
    Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) Mbar)) ≫
        muToTorus (ResidueField ↥A) O'.toricRank m =
      muToTorus (ResidueField ↥A) O.toricRank m ≫
        Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) Mx)) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    ← AddMonoidAlgebra.mapDomainRingHom_comp, ← AddMonoidAlgebra.mapDomainRingHom_comp]
  exact congrArg (fun F => Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) F))) hred

include hψ₁ in

theorem special_eq (hred : Mbar.comp (castPi O'.toricRank m) = (castPi O.toricRank m).comp Mx)
    (hMx : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) Mx)) ≫ O'.torusFibre.1 ≫
        pullback.fst O'.g (resPt A ≫ Λ'.σA) =
      O.torusFibre.1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) ≫ ψ.1) :
    muBaseChange (IsLocalRing.residue ↥A) O.toricRank m ≫ (O.toricLift m hm).1 =
      muBaseChange (IsLocalRing.residue ↥A) O.toricRank m ≫ (vLift O O' ψinv m hm Mbar).1 := by
  apply pullback.hom_ext
  ·
    rw [Category.assoc, Category.assoc, O.toricLift_special m hm]
    change _ = muBaseChange (IsLocalRing.residue ↥A) O.toricRank m ≫
      (specMbar O O' m Mbar ≫ (O'.toricLift m hm).1 ≫ (psiInvA O O' ψinv).1) ≫ pullback.fst O.g Λ.σA
    simp only [Category.assoc]
    rw [psiInvA_fst, reassoc_of% (muBaseChange_comp_specMbar O O' m Mbar), reassoc_of% (O'.toricLift_special m hm),
      reassoc_of% (specMbar_comp_muToTorus O O' m Mbar Mx hred), reassoc_of% hMx, hψ₁, Category.comp_id]
  ·
    rw [Category.assoc, Category.assoc, (O.toricLift m hm).2, (vLift O O' ψinv m hm Mbar).2]

end Lift

include hψ₁ hψ₂ hψL in

theorem lift_transport (Mx : (Fin O'.toricRank → ℤ) →+ (Fin O.toricRank → ℤ))
    (hMx : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) Mx)) ≫ O'.torusFibre.1 ≫
        pullback.fst O'.g (resPt A ≫ Λ'.σA) =
      O.torusFibre.1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) ≫ ψ.1)
    (m : ℕ) (hm : 0 < m) :
    ∃ Mbar : (Fin O'.toricRank → ZMod m) →+ (Fin O.toricRank → ZMod m),
      Mbar.comp (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin O'.toricRank => ℤ) i)) =
        (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin O.toricRank => ℤ) i)).comp Mx ∧
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom ↥A Mbar)) ≫ (O'.toricLift m hm).1 ≫ pullback.fst O'.g Λ'.σA =
        (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA ≫ ψ.1 := by
  refine ⟨reduceMod Mx m, reduceMod_comp_castPi Mx m, ?_⟩
  have huv := ModularCurve.JHNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq p M H hpM A hA Λ O m hm
    (O.toricLift m hm) (vLift O O' ψinv m hm (reduceMod Mx m)) (O.toricLift_mul m hm)
    (vLift_mul O O' ψ ψinv hψ₁ hψ₂ hψL m hm (reduceMod Mx m))
    (special_eq O O' ψ ψinv hψ₁ m hm (reduceMod Mx m) Mx (reduceMod_comp_castPi Mx m) hMx)

  have h1 := congrArg (fun w : SchemeHomOver (muStr ↥A O.toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA O.g) =>
    w.1 ≫ pullback.fst O.g Λ.σA ≫ ψ.1) huv
  simp only [vLift, Category.assoc] at h1
  rw [h1, reassoc_of% (psiInvA_fst O O' ψinv), hψ₂, Category.comp_id]

end TRL3
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme.TRL3"

namespace TR

namespace LawEq

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)

abbrev ιQ : Spec (CommRingCat.of ℚ) ⟶ base p := Spec.map (CommRingCat.ofHom (algebraMap (baseRing p) ℚ))

theorem away_p : IsLocalization.Away (((p : ℕ) : baseRing p)) ℚ := by
  have hp : p.Prime := Fact.out
  refine
    { map_units := ?_
      surj := ?_
      exists_of_eq := ?_ }
  · rintro ⟨_, n, rfl⟩
    rw [map_pow]
    exact IsUnit.pow _ (isUnit_iff_ne_zero.mpr (by
      change ((((p : ℕ) : baseRing p) : ℚ)) ≠ 0
      exact_mod_cast hp.ne_zero))
  · intro q
    obtain ⟨e, d, hpd, hden⟩ := Nat.exists_eq_pow_mul_and_not_dvd q.den_nz p hp.ne_one
    have hd0 : d ≠ 0 := by rintro rfl; exact q.den_nz (by rw [hden, mul_zero])
    have hr : ((q.num : ℚ) / d).den.Coprime p := by
      have h1 : (((q.num : ℚ) / d).den : ℤ) ∣ (d : ℤ) := by
        have := Rat.den_dvd q.num d
        rwa [Rat.divInt_eq_div, Int.cast_natCast] at this
      have h2 : ((q.num : ℚ) / d).den ∣ d := by exact_mod_cast h1
      exact Nat.Coprime.of_dvd_left h2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd).symm
    refine ⟨⟨⟨(q.num : ℚ) / d, hr⟩, ⟨_, e, rfl⟩⟩, ?_⟩
    change q * ((((p : ℕ) : baseRing p) ^ e : baseRing p) : ℚ) = (q.num : ℚ) / d
    push_cast
    have hnum : (q.num : ℚ) = q * ((p : ℚ) ^ e * d) := by
      rw [← Rat.mul_den_eq_num, hden]; push_cast; ring
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
    rw [hnum]
    field_simp
  · intro x y h
    exact ⟨1, by simpa using Subtype.val_injective (by exact_mod_cast h : ((x : ℚ)) = y)⟩

scoped instance isOpenImmersion_ιQ : IsOpenImmersion (ιQ p) :=
  haveI := away_p p
  IsOpenImmersion.of_isLocalization (((p : ℕ) : baseRing p))

theorem isFractionRing_baseRing : IsFractionRing (baseRing p) ℚ := by
  refine
    { map_units := ?_
      surj := ?_
      exists_of_eq := ?_ }
  · rintro ⟨y, hy⟩
    rw [mem_nonZeroDivisors_iff_ne_zero] at hy
    refine isUnit_iff_ne_zero.mpr ?_
    change ((y : ℚ)) ≠ 0
    exact fun h => hy (Subtype.ext h)
  · intro z
    have hnum : ((z.num : ℚ)).den.Coprime p := by simp
    have hden : ((z.den : ℚ)).den.Coprime p := by simp
    have hden0 : (⟨(z.den : ℚ), hden⟩ : baseRing p) ∈ nonZeroDivisors (baseRing p) := by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      intro h
      have h' : ((z.den : ℚ)) = 0 := by simpa using congrArg Subtype.val h
      exact z.den_nz (by exact_mod_cast h')
    refine ⟨⟨⟨(z.num : ℚ), hnum⟩, ⟨⟨(z.den : ℚ), hden⟩, hden0⟩⟩, ?_⟩
    change z * (z.den : ℚ) = (z.num : ℚ)
    exact Rat.mul_den_eq_num z
  · intro x y h
    exact ⟨1, by simpa using Subtype.val_injective (by exact_mod_cast h : ((x : ℚ)) = y)⟩

theorem abelianBundle_genericFibre :
    AbelianSchemePropertyBundle ℚ (RelativeGroupLaw.baseChangeStr (ιQ p) O.g) := by
  haveI := O.smooth
  haveI := O.proper_generic
  refine ⟨inferInstance, ?_, ?_, ⟨O.L.baseChange (ιQ p)⟩⟩
  · exact O.proper_generic
  · intro s
    have hs : (RelativeGroupLaw.baseChangeStr (ιQ p) O.g).base ⁻¹' {s} = Set.univ := by
      ext z; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]; exact Subsingleton.elim _ _
    rw [hs]
    let η : base p := (ιQ p).base (IsLocalRing.closedPoint ℚ)
    have hrange : Set.range (ιQ p).base = {η} := by
      ext z; constructor
      · rintro ⟨w, rfl⟩; rw [Set.mem_singleton_iff, Subsingleton.elim w (IsLocalRing.closedPoint ℚ)]
      · rintro rfl; exact ⟨_, rfl⟩
    have hfst : Set.range (pullback.fst O.g (ιQ p)).base = O.g.base ⁻¹' {η} := by
      rw [Scheme.Pullback.range_fst, hrange]
    refine ⟨?_, ?_⟩
    · exact ⟨((O.L.baseChange (ιQ p)).one (𝟙 _)).1.base (IsLocalRing.closedPoint ℚ), trivial⟩
    · have hind := (pullback.fst O.g (ιQ p)).isOpenEmbedding.isInducing
      rw [← hind.isPreconnected_image, Set.image_univ, hfst]
      exact O.fibre_preconnected η

theorem one_baseChange_eq (L₂ : RelativeGroupLaw (baseRing p) O.g)
    (hone : ∀ {T : Scheme.{0}} (s : T ⟶ base p), (L₂.one s).1 = (O.L.one s).1) :
    ((L₂.baseChange (ιQ p)).one (𝟙 (Spec (CommRingCat.of ℚ)))).1 =
      ((O.L.baseChange (ιQ p)).one (𝟙 (Spec (CommRingCat.of ℚ)))).1 := by
  rw [RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe,
    RelativeGroupLaw.baseChangePointOfBase_coe]
  apply pullback.hom_ext
  · rw [pullback.lift_fst, pullback.lift_fst, hone]
  · rw [pullback.lift_snd, pullback.lift_snd]

theorem mul_eq_over (L₂ : RelativeGroupLaw (baseRing p) O.g)
    (hone : ∀ {T : Scheme.{0}} (s : T ⟶ base p), (L₂.one s).1 = (O.L.one s).1)
    {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of ℚ)) :
    ∀ a b : SchemeHomOver (s ≫ ιQ p) O.g, L₂.mul _ a b = O.L.mul _ a b := by
  intro a b
  have key := GoodReductionJacobian.RelativeGroupLaw.mul_eq_mul_of_one_eq_of_abelianSchemePropertyBundle ℚ
    (abelianBundle_genericFibre p M H hpM A hA Λ O) (L₂.baseChange (ιQ p)) (O.L.baseChange (ιQ p))
    (one_baseChange_eq p M H hpM A hA Λ O L₂ hone) s
    (RelativeGroupLaw.baseChangePointOfBase (ιQ p) a) (RelativeGroupLaw.baseChangePointOfBase (ιQ p) b)
  have := congrArg (RelativeGroupLaw.baseChangePointToBase (ιQ p)) key
  rwa [RelativeGroupLaw.baseChangePointToBase_mul, RelativeGroupLaw.baseChangePointToBase_mul,
    RelativeGroupLaw.baseChangePointToBase_ofBase, RelativeGroupLaw.baseChangePointToBase_ofBase] at this

theorem mul_eq_mul_of_eq {R : Type} [CommRing R] {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    (L Lc : RelativeGroupLaw R g) {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of R)}
    (h : s' = s) (hs : ∀ a b : SchemeHomOver s g, L.mul s a b = Lc.mul s a b) :
    ∀ a b : SchemeHomOver s' g, L.mul s' a b = Lc.mul s' a b := by
  subst h; exact hs

theorem mul_val_congr {R : Type} [CommRing R] {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R g) {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s')
    (a b : SchemeHomOver s g) (a' b' : SchemeHomOver s' g) (ha : a.1 = a'.1) (hb : b.1 = b'.1) :
    (L.mul s a b).1 = (L.mul s' a' b').1 := by
  subst h
  obtain rfl : a = a' := Subtype.ext ha
  obtain rfl : b = b' := Subtype.ext hb
  rfl

theorem mul_eq_all (L₂ : RelativeGroupLaw (baseRing p) O.g)
    (hone : ∀ {T : Scheme.{0}} (s : T ⟶ base p), (L₂.one s).1 = (O.L.one s).1)
    {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g) : L₂.mul s x y = O.L.mul s x y := by
  haveI := O.smooth
  haveI := O.separated
  haveI : IsFractionRing (baseRing p) ℚ := isFractionRing_baseRing p
  let φ : SchemeHomOver O.g O.g := ⟨𝟙 _, Category.id_comp _⟩
  have hpt : ∀ {S : Scheme.{0}} {s' : S ⟶ base p} (a : SchemeHomOver s' O.g)
      (ha : (a.1 ≫ φ.1) ≫ O.g = s'), (⟨a.1 ≫ φ.1, ha⟩ : SchemeHomOver s' O.g) = a :=
    fun a _ => Subtype.ext (Category.comp_id _)
  have key := GoodReductionJacobian.RelativeGroupLaw.comp_mul_eq_mul_comp_of_genericFibre (baseRing p) ℚ
    (f := O.g) (t := O.g) O.L L₂ φ ?_ s x y
  · rw [hpt, hpt] at key
    exact Subtype.ext ((Category.comp_id _).symm.trans key)
  · intro S s' a b
    rw [hpt, hpt]
    change (L₂.mul _ a b).1 ≫ 𝟙 _ = (O.L.mul _ a b).1
    rw [Category.comp_id]
    exact congrArg Subtype.val
      (mul_eq_mul_of_eq L₂ O.L (s := s' ≫ ιQ p) rfl (mul_eq_over p M H hpM A hA Λ O L₂ hone s') a b)

end LawEq
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme.TRL3 P2MW.S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme.TR.LawEq"

section Main

variable
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hpts_law : ∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y))
    (Λ' : JHNeronObjectAtP.LevelData p M H hpM A) (O' : JHNeronObjectAtP p M H hpM A hA Λ')
    (hD' : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O'.G, O'.g, (O'.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O'.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hΛ' : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ'.f)
    (hpts_law' : ∀ x y : JH M H,
        O'.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD').mul _ (O'.pts x) (O'.pts y))
    (ψ : SchemeHomOver O.g O'.g) (ψinv : SchemeHomOver O'.g O.g)
    (hψ₁ : ψ.1 ≫ ψinv.1 = 𝟙 _) (hψ₂ : ψinv.1 ≫ ψ.1 = 𝟙 _)

    (hψmul : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s x y) ψ =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD').mul s
          (NeronModelInfra.schemeHomOverComp x ψ) (NeronModelInfra.schemeHomOverComp y ψ))

omit [Fact (Nat.Prime p)] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
theorem sigmaA_eq : Λ.σA = Λ'.σA := by
  obtain ⟨χ, hχ⟩ := Spec.map_surjective Λ.σA
  obtain ⟨χ', hχ'⟩ := Spec.map_surjective Λ'.σA
  have h1 := Λ.hσA
  have h2 := Λ'.hσA
  rw [← hχ] at h1
  rw [← hχ'] at h2
  change Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map χ = Spec.map (CommRingCat.ofHom (algebraMap (baseRing p) (AlgebraicClosure ℚ))) at h1
  change Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map χ' = Spec.map (CommRingCat.ofHom (algebraMap (baseRing p) (AlgebraicClosure ℚ))) at h2
  rw [← Spec.map_comp] at h1 h2
  have e1 := Spec.map_injective h1
  have e2 := Spec.map_injective h2
  have hχχ' : χ = χ' := by
    ext x
    have := congrArg (fun f : CommRingCat.of (baseRing p) ⟶ CommRingCat.of (AlgebraicClosure ℚ) => f.hom x) (e1.trans e2.symm)
    simpa using this
  rw [← hχ, ← hχ', hχχ']

theorem sκ_eq : resPt A ≫ Λ.σA = resPt A ≫ Λ'.σA := by rw [sigmaA_eq p M H hpM A Λ Λ']

def psiκ : SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ'.σA) O'.g) :=
  ⟨pullback.lift (pullback.fst _ _ ≫ ψ.1) (pullback.snd _ _)
      (by rw [Category.assoc, ψ.2, pullback.condition, sκ_eq p M H hpM A Λ Λ']),
    pullback.lift_snd _ _ _⟩

@[scoped simp] theorem psiκ_fst : (psiκ p M H hpM A hA Λ O Λ' O' ψ).1 ≫ pullback.fst O'.g _ = pullback.fst O.g _ ≫ ψ.1 := pullback.lift_fst _ _ _
@[scoped simp] theorem psiκ_snd : (psiκ p M H hpM A hA Λ O Λ' O' ψ).1 ≫ pullback.snd O'.g _ = pullback.snd O.g _ := pullback.lift_snd _ _ _

def psiκInv : SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ'.σA) O'.g) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) :=
  ⟨pullback.lift (pullback.fst _ _ ≫ ψinv.1) (pullback.snd _ _)
      (by rw [Category.assoc, ψinv.2, pullback.condition, sκ_eq p M H hpM A Λ Λ']),
    pullback.lift_snd _ _ _⟩

include hψ₁ in
theorem psiκ_comp_inv : (psiκ p M H hpM A hA Λ O Λ' O' ψ).1 ≫ (psiκInv p M H hpM A hA Λ O Λ' O' ψinv).1 = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [psiκ, psiκInv, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
    rw [hψ₁, Category.comp_id]
  · simp only [psiκ, psiκInv, Category.assoc, pullback.lift_snd, Category.id_comp]

include hψ₂ in
theorem psiκInv_comp : (psiκInv p M H hpM A hA Λ O Λ' O' ψinv).1 ≫ (psiκ p M H hpM A hA Λ O Λ' O' ψ).1 = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [psiκ, psiκInv, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
    rw [hψ₂, Category.comp_id]
  · simp only [psiκ, psiκInv, Category.assoc, pullback.lift_snd, Category.id_comp]

include hψ₁ hψ₂ in
theorem isIso_psiκ : IsIso (psiκ p M H hpM A hA Λ O Λ' O' ψ).1 :=
  ⟨⟨(psiκInv p M H hpM A hA Λ O Λ' O' ψinv).1, psiκ_comp_inv p M H hpM A hA Λ O Λ' O' ψ ψinv hψ₁, psiκInv_comp p M H hpM A hA Λ O Λ' O' ψ ψinv hψ₂⟩⟩

def psiA : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.σA O.g) (RelativeGroupLaw.baseChangeStr Λ'.σA O'.g) :=
  ⟨pullback.lift (pullback.fst _ _ ≫ ψ.1) (pullback.snd _ _)
      (by rw [Category.assoc, ψ.2, pullback.condition, sigmaA_eq p M H hpM A Λ Λ']),
    pullback.lift_snd _ _ _⟩

@[scoped simp] theorem psiA_fst : (psiA p M H hpM A hA Λ O Λ' O' ψ).1 ≫ pullback.fst O'.g _ = pullback.fst O.g _ ≫ ψ.1 := pullback.lift_fst _ _ _
@[scoped simp] theorem psiA_snd : (psiA p M H hpM A hA Λ O Λ' O' ψ).1 ≫ pullback.snd O'.g _ = pullback.snd O.g _ := pullback.lift_snd _ _ _

theorem hone_pic : ∀ {T : Scheme.{0}} (s : T ⟶ base p),
    ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).one s).1 = (O.L.one s).1 := by
  intro T s
  have h1 := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).one_natural (𝟙 _) s s (Category.comp_id s)
  have h2 := O.L.one_natural (𝟙 _) s s (Category.comp_id s)
  have e1 := congrArg Subtype.val h1
  have e2 := congrArg Subtype.val h2
  simp only [GoodReductionJacobian.schemeHomOverComp_coe] at e1 e2
  rw [← e1, ← e2, RepresentsRelSubPic.relativeGroupLaw_one]

theorem law_eq_pic {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g) :
    (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s x y = O.L.mul s x y :=
  LawEq.mul_eq_all p M H hpM A hA Λ O _ (hone_pic p M H hpM hj 𝔛 A hA Λ O hD) s x y

include hD hD' hψmul in

theorem law_transfer {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g) :
    NeronModelInfra.schemeHomOverComp (O.L.mul s x y) ψ =
      O'.L.mul s (NeronModelInfra.schemeHomOverComp x ψ) (NeronModelInfra.schemeHomOverComp y ψ) := by
  rw [← law_eq_pic p M H hpM hj 𝔛 A hA Λ O hD s x y,
    ← law_eq_pic p M H hpM hj 𝔛 A hA Λ' O' hD' s (NeronModelInfra.schemeHomOverComp x ψ) (NeronModelInfra.schemeHomOverComp y ψ)]
  exact hψmul s x y

include hD hD' hψmul in

theorem law_transfer_baseChange {R' : Type} [CommRing R'] (ι ι' : Spec (CommRingCat.of R') ⟶ base p) (hι : ι = ι')
    (Ψ : SchemeHomOver (RelativeGroupLaw.baseChangeStr ι O.g) (RelativeGroupLaw.baseChangeStr ι' O'.g))
    (hΨ : Ψ.1 ≫ pullback.fst O'.g ι' = pullback.fst O.g ι ≫ ψ.1)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R'))
    (x y : SchemeHomOver t (RelativeGroupLaw.baseChangeStr ι O.g)) :
    NeronModelInfra.schemeHomOverComp ((O.L.baseChange ι).mul _ x y) Ψ =
      (O'.L.baseChange ι').mul _ (NeronModelInfra.schemeHomOverComp x Ψ) (NeronModelInfra.schemeHomOverComp y Ψ) := by
  apply (RelativeGroupLaw.baseChangePointEquiv ι' (f := O'.g) t).injective
  apply Subtype.ext
  change (RelativeGroupLaw.baseChangePointToBase ι' (NeronModelInfra.schemeHomOverComp ((O.L.baseChange ι).mul _ x y) Ψ)).1 =
    (RelativeGroupLaw.baseChangePointToBase ι' ((O'.L.baseChange ι').mul _
      (NeronModelInfra.schemeHomOverComp x Ψ) (NeronModelInfra.schemeHomOverComp y Ψ))).1
  rw [RelativeGroupLaw.baseChangePointToBase_mul, RelativeGroupLaw.baseChangePointToBase_coe,
    NeronModelInfra.schemeHomOverComp_coe, Category.assoc, hΨ, ← Category.assoc]
  have hL := congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_mul ι O.L t x y)
  rw [RelativeGroupLaw.baseChangePointToBase_coe] at hL
  rw [hL]
  have hT := congrArg Subtype.val
    (law_transfer p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' ψ hψmul (t ≫ ι)
      (RelativeGroupLaw.baseChangePointToBase ι x) (RelativeGroupLaw.baseChangePointToBase ι y))
  rw [NeronModelInfra.schemeHomOverComp_coe] at hT
  rw [hT]
  refine LawEq.mul_val_congr O'.L (by rw [hι]) _ _ _ _ ?_ ?_
  · simp only [NeronModelInfra.schemeHomOverComp_coe, RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc, hΨ]
  · simp only [NeronModelInfra.schemeHomOverComp_coe, RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc, hΨ]

include hD hD' hψmul in

theorem law_transfer_A :
    ∀ x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥A))) (RelativeGroupLaw.baseChangeStr Λ.σA O.g),
      NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.σA).mul _ x y) (psiA p M H hpM A hA Λ O Λ' O' ψ) =
        (O'.L.baseChange Λ'.σA).mul _
          (NeronModelInfra.schemeHomOverComp x (psiA p M H hpM A hA Λ O Λ' O' ψ))
          (NeronModelInfra.schemeHomOverComp y (psiA p M H hpM A hA Λ O Λ' O' ψ)) :=
  fun x y => law_transfer_baseChange p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' ψ hψmul Λ.σA Λ'.σA
    (sigmaA_eq p M H hpM A Λ Λ') (psiA p M H hpM A hA Λ O Λ' O' ψ) (psiA_fst p M H hpM A hA Λ O Λ' O' ψ) (𝟙 _) x y

def xT : SchemeHomOver (torusStr (ResidueField ↥A) O.toricRank) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ'.σA) O'.g) :=
  NeronModelInfra.schemeHomOverComp O.torusFibre (psiκ p M H hpM A hA Λ O Λ' O' ψ)

@[scoped simp] theorem xT_val : (xT p M H hpM A hA Λ O Λ' O' ψ).1 = O.torusFibre.1 ≫ (psiκ p M H hpM A hA Λ O Λ' O' ψ).1 := rfl

include hD hD' hψmul in

theorem law_transfer_κ :
    ∀ x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g),
      NeronModelInfra.schemeHomOverComp ((O.L.baseChange (resPt A ≫ Λ.σA)).mul _ x y) (psiκ p M H hpM A hA Λ O Λ' O' ψ) =
        (O'.L.baseChange (resPt A ≫ Λ'.σA)).mul _
          (NeronModelInfra.schemeHomOverComp x (psiκ p M H hpM A hA Λ O Λ' O' ψ))
          (NeronModelInfra.schemeHomOverComp y (psiκ p M H hpM A hA Λ O Λ' O' ψ)) :=
  fun x y => law_transfer_baseChange p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' ψ hψmul (resPt A ≫ Λ.σA) (resPt A ≫ Λ'.σA)
    (sκ_eq p M H hpM A Λ Λ') (psiκ p M H hpM A hA Λ O Λ' O' ψ) (psiκ_fst p M H hpM A hA Λ O Λ' O' ψ) (𝟙 _) x y

section units
variable {R : Type} [CommRing R] {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}

theorem eq_one_of_mul_self (L : RelativeGroupLaw R g) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver t g) (h : L.mul t e e = e) : e = L.one t := by
  calc e = L.mul t (L.one t) e := (L.one_mul t e).symm
    _ = L.mul t (L.mul t (L.inv t e) e) e := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t e) (L.mul t e e) := by rw [L.mul_assoc]
    _ = L.mul t (L.inv t e) e := by rw [h]
    _ = L.one t := L.inv_mul_cancel t e

end units
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme.TRL3 P2MW.S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme.TR.LawEq"

theorem torusFibre_one :
    NeronModelInfra.schemeHomOverComp (torusPt _ _ (1 : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)).ofConv) O.torusFibre =
      (O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by
  apply eq_one_of_mul_self
  have h := O.torusFibre_mul 1 1
  rw [mul_one] at h
  exact h.symm

include hj 𝔛 hD hD' hψmul in

theorem psiκ_one :
    NeronModelInfra.schemeHomOverComp ((O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)) (psiκ p M H hpM A hA Λ O Λ' O' ψ) =
      (O'.L.baseChange (resPt A ≫ Λ'.σA)).one (𝟙 _) := by
  apply eq_one_of_mul_self
  have h := law_transfer_κ p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' ψ hψmul ((O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)) ((O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _))
  rw [RelativeGroupLaw.one_mul] at h
  exact h.symm

theorem abqFibre'_one (i : Fin 2) :
    NeronModelInfra.schemeHomOverComp ((O'.L.baseChange (resPt A ≫ Λ'.σA)).one (𝟙 _)) (O'.abqFibre i) =
      (Λ'.L.baseChange (resPt A ≫ Λ'.σA)).one (𝟙 _) := by
  apply eq_one_of_mul_self
  have h := O'.abqFibre_mul i (𝟙 _) ((O'.L.baseChange (resPt A ≫ Λ'.σA)).one (𝟙 _)) ((O'.L.baseChange (resPt A ≫ Λ'.σA)).one (𝟙 _))
  rw [RelativeGroupLaw.one_mul] at h
  exact h.symm

theorem toricRank_eq : O.toricRank = O'.toricRank := by
  have h1 := O.toricRank_succ_eq_card
  have h2 := O'.toricRank_succ_eq_card
  have hss : O.ssFinset = O'.ssFinset := by
    ext s; rw [O.mem_ssFinset_iff, O'.mem_ssFinset_iff]
  rw [hss] at h1
  omega

include hΛ' in

theorem abelianBundle_Λ'κ :
    GoodReductionJacobian.AbelianSchemePropertyBundle (ResidueField ↥A) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ'.σA) Λ'.f) :=
  GoodReductionJacobian.AbelianSchemePropertyBundle.baseChange_of_field hΛ' (resPt A ≫ Λ'.σA)

def u0 : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ torusScheme (ResidueField ↥A) O.toricRank :=
  (torusPt _ _ (1 : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)).ofConv).1

theorem u0_torusStr : u0 p M H hpM A hA Λ O ≫ torusStr (ResidueField ↥A) O.toricRank = 𝟙 _ :=
  (torusPt _ _ (1 : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)).ofConv).2

include hj 𝔛 hD hD' hψmul in
include hΛ' in

theorem comp_xT_abqFibre' (i : Fin 2) :
    NeronModelInfra.schemeHomOverComp (xT p M H hpM A hA Λ O Λ' O' ψ) (O'.abqFibre i) =
      (Λ'.L.baseChange (resPt A ≫ Λ'.σA)).one (torusStr (ResidueField ↥A) O.toricRank) := by

  set φ : torusScheme (ResidueField ↥A) O.toricRank ⟶ _ := (xT p M H hpM A hA Λ O Λ' O' ψ).1 ≫ (O'.abqFibre i).1 with hφdef
  have hφ : φ ≫ RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ'.σA) Λ'.f = torusStr (ResidueField ↥A) O.toricRank := by
    rw [hφdef, Category.assoc, (O'.abqFibre i).2, (xT p M H hpM A hA Λ O Λ' O' ψ).2]
  obtain ⟨a, ha1, ha2⟩ := GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int
    (abelianBundle_Λ'κ p M H hpM A Λ' hΛ') O.toricRank φ hφ

  have hu : u0 p M H hpM A hA Λ O ≫ φ = ((Λ'.L.baseChange (resPt A ≫ Λ'.σA)).one (𝟙 _)).1 := by
    have e1 := congrArg Subtype.val (torusFibre_one p M H hpM A hA Λ O)
    have e2 := congrArg Subtype.val (psiκ_one p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' ψ hψmul)
    have e3 := congrArg Subtype.val (abqFibre'_one p M H hpM A hA Λ' O' i)
    simp only [NeronModelInfra.schemeHomOverComp_coe] at e1 e2 e3
    rw [hφdef, xT_val, ← Category.assoc, ← Category.assoc, show u0 p M H hpM A hA Λ O ≫ O.torusFibre.1 = _ from e1, e2, e3]
  have ha : a = ((Λ'.L.baseChange (resPt A ≫ Λ'.σA)).one (𝟙 _)).1 := by
    rw [← hu, ha2, ← Category.assoc, u0_torusStr, Category.id_comp]
  apply Subtype.ext
  rw [NeronModelInfra.schemeHomOverComp_coe]
  change φ = _
  rw [ha2, ha]
  have := congrArg Subtype.val ((Λ'.L.baseChange (resPt A ≫ Λ'.σA)).one_natural (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank)
    (torusStr (ResidueField ↥A) O.toricRank) (Category.comp_id _))
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
  exact this

include hj 𝔛 hD hD' hψmul in
include hΛ' in

theorem exists_y : ∃ y : SchemeHomOver (torusStr (ResidueField ↥A) O.toricRank) (torusStr (ResidueField ↥A) O'.toricRank),
    NeronModelInfra.schemeHomOverComp y O'.torusFibre = xT p M H hpM A hA Λ O Λ' O' ψ :=
  (O'.abqFibre_eq_one_iff (torusStr (ResidueField ↥A) O.toricRank) (xT p M H hpM A hA Λ O Λ' O' ψ)).mp
    (comp_xT_abqFibre' p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' hΛ' ψ hψmul)

include hψ₁ hψ₂ in
theorem isClosedImmersion_xT : IsClosedImmersion (xT p M H hpM A hA Λ O Λ' O' ψ).1 := by
  haveI := O.torusFibre_isClosedImmersion
  haveI := isIso_psiκ p M H hpM A hA Λ O Λ' O' ψ ψinv hψ₁ hψ₂
  rw [xT_val]
  infer_instance

include hψ₁ hψ₂ in
theorem isClosedImmersion_y (y : SchemeHomOver (torusStr (ResidueField ↥A) O.toricRank) (torusStr (ResidueField ↥A) O'.toricRank))
    (hy : NeronModelInfra.schemeHomOverComp y O'.torusFibre = xT p M H hpM A hA Λ O Λ' O' ψ) : IsClosedImmersion y.1 := by
  haveI := O'.torusFibre_isClosedImmersion
  haveI : IsClosedImmersion (y.1 ≫ O'.torusFibre.1) := by
    have := congrArg Subtype.val hy
    rw [NeronModelInfra.schemeHomOverComp_coe] at this
    rw [this]; exact isClosedImmersion_xT p M H hpM A hA Λ O Λ' O' ψ ψinv hψ₁ hψ₂
  exact IsClosedImmersion.of_comp y.1 O'.torusFibre.1

include hψ₁ hψ₂ in

theorem range_xT_eq (y : SchemeHomOver (torusStr (ResidueField ↥A) O.toricRank) (torusStr (ResidueField ↥A) O'.toricRank))
    (hy : NeronModelInfra.schemeHomOverComp y O'.torusFibre = xT p M H hpM A hA Λ O Λ' O' ψ) :
    Set.range (xT p M H hpM A hA Λ O Λ' O' ψ).1.base = Set.range O'.torusFibre.1.base := by
  have hyci := isClosedImmersion_y p M H hpM A hA Λ O Λ' O' ψ ψinv hψ₁ hψ₂ y hy

  have honto := AlgebraicGeometry.SplitTorus.exists_schemeHomOverComp_eq_of_isClosedImmersion_torusStr_of_eq (ResidueField ↥A)
    O'.toricRank O.toricRank (toricRank_eq p M H hpM A hA Λ O Λ' O') y hyci

  have hrange_y : Set.range y.1.base = Set.univ := by
    haveI : LocallyOfFiniteType (torusStr (ResidueField ↥A) O'.toricRank) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      change RingHom.FiniteType (algebraMap (ResidueField ↥A) (torusCoord (ResidueField ↥A) O'.toricRank))
      rw [RingHom.finiteType_algebraMap]
      infer_instance
    haveI : JacobsonSpace (torusScheme (ResidueField ↥A) O'.toricRank) :=
      LocallyOfFiniteType.jacobsonSpace (Y := Spec (CommRingCat.of (ResidueField ↥A))) (torusStr (ResidueField ↥A) O'.toricRank)
    have hcl : IsClosed (Set.range y.1.base) := y.1.isClosedEmbedding.isClosed_range
    have hsub : closedPoints (torusScheme (ResidueField ↥A) O'.toricRank) ⊆ Set.range y.1.base := by
      intro c hc
      obtain ⟨⟨z', hz'⟩, hz'c⟩ := (pointEquivClosedPoint (torusStr (ResidueField ↥A) O'.toricRank)).surjective ⟨c, hc⟩
      obtain ⟨z, hz⟩ := honto ⟨z', hz'⟩
      have := congrArg Subtype.val hz
      rw [NeronModelInfra.schemeHomOverComp_coe] at this
      refine ⟨z.1.base (IsLocalRing.closedPoint _), ?_⟩
      have hc' : z'.base (IsLocalRing.closedPoint _) = c := congrArg Subtype.val hz'c
      have this' : z.1 ≫ y.1 = z' := this
      rw [← hc', ← this', Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    apply Set.eq_univ_of_univ_subset
    rw [← closure_closedPoints (X := torusScheme (ResidueField ↥A) O'.toricRank)]
    exact closure_minimal hsub hcl
  have := congrArg Subtype.val hy
  rw [NeronModelInfra.schemeHomOverComp_coe] at this
  rw [← this, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange_y, Set.image_univ]

section core
variable {κ : Type} [Field κ] [IsAlgClosed κ] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of κ)) [IsSeparated f]
  (L : RelativeGroupLaw κ f)

theorem transport_core (t t' : ℕ) (h : t = t')
    (τ : SchemeHomOver (torusStr κ t') f) (τ' : SchemeHomOver (torusStr κ t) f)
    (hτ : IsClosedImmersion τ.1) (hτ' : IsClosedImmersion τ'.1)
    (hτmul : ∀ χ χ' : WithConv (torusCoord κ t' →ₐ[κ] κ),
      NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) τ =
        L.mul _ (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) τ) (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) τ))
    (hτ'mul : ∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ),
      NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) τ' =
        L.mul _ (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) τ') (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) τ'))
    (hrange : Set.range τ'.1.base = Set.range τ.1.base) :
    ∃ M₀ : (Fin t' → ℤ) →+ (Fin t → ℤ), Function.Bijective M₀ ∧
      τ'.1 = Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ M₀)) ≫ τ.1 := by
  subst h
  obtain ⟨Mx, hMx⟩ := AlgebraicGeometry.SplitTorus.exists_addEquiv_eq_specMap_mapDomain_comp_of_range_eq f L t τ τ' hτ hτ'
    hτmul hτ'mul hrange
  exact ⟨Mx.toAddMonoidHom, Mx.bijective, hMx⟩

end core
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme.TRL3 P2MW.S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme.TR.LawEq"

theorem schemeHomOverComp_assoc' {B T X Y Z : Scheme.{0}} {t : T ⟶ B} {f : X ⟶ B} {g : Y ⟶ B} {h : Z ⟶ B}
    (a : SchemeHomOver t f) (b : SchemeHomOver f g) (c : SchemeHomOver g h) :
    NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a b) c =
      NeronModelInfra.schemeHomOverComp a (NeronModelInfra.schemeHomOverComp b c) :=
  Subtype.ext (Category.assoc _ _ _)

include hj 𝔛 hD hD' hψmul in

theorem xT_mul : ∀ χ χ' : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A),
    NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) (xT p M H hpM A hA Λ O Λ' O' ψ) =
      (O'.L.baseChange (resPt A ≫ Λ'.σA)).mul _
        (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) (xT p M H hpM A hA Λ O Λ' O' ψ))
        (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) (xT p M H hpM A hA Λ O Λ' O' ψ)) := by
  intro χ χ'
  unfold xT
  rw [← schemeHomOverComp_assoc', ← schemeHomOverComp_assoc', ← schemeHomOverComp_assoc', O.torusFibre_mul,
    law_transfer_κ p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' ψ hψmul]

include hj 𝔛 hD hD' hψmul in
include hΛ' hψ₁ hψ₂ in

theorem torus_transport_bijective :
    ∃ M₀ : (Fin O'.toricRank → ℤ) →+ (Fin O.toricRank → ℤ), Function.Bijective M₀ ∧
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀)) ≫ O'.torusFibre.1 ≫
          pullback.fst O'.g (resPt A ≫ Λ'.σA) =
        O.torusFibre.1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) ≫ ψ.1 := by
  haveI : IsSeparated (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ'.σA) O'.g) := by
    haveI := O'.separated; dsimp only [RelativeGroupLaw.baseChangeStr]; infer_instance
  obtain ⟨y, hy⟩ := exists_y p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' hΛ' ψ hψmul
  obtain ⟨M₀, hbij, hM₀⟩ := transport_core (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ'.σA) O'.g) (O'.L.baseChange (resPt A ≫ Λ'.σA))
    O.toricRank O'.toricRank (toricRank_eq p M H hpM A hA Λ O Λ' O') O'.torusFibre (xT p M H hpM A hA Λ O Λ' O' ψ)
    O'.torusFibre_isClosedImmersion (isClosedImmersion_xT p M H hpM A hA Λ O Λ' O' ψ ψinv hψ₁ hψ₂)
    O'.torusFibre_mul (xT_mul p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' ψ hψmul) (range_xT_eq p M H hpM A hA Λ O Λ' O' ψ ψinv hψ₁ hψ₂ y hy)
  refine ⟨M₀, hbij, ?_⟩
  rw [← Category.assoc, ← hM₀, xT_val, Category.assoc, psiκ_fst]

include hΛ' hψ₁ hψ₂ in
include hΛ' hψ₁ hψ₂ in
include hj 𝔛 hD hD' hψmul in

theorem torus_transport_fst :
    ∃ M₀ : (Fin O'.toricRank → ℤ) →+ (Fin O.toricRank → ℤ),
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀)) ≫ O'.torusFibre.1 ≫
          pullback.fst O'.g (resPt A ≫ Λ'.σA) =
        O.torusFibre.1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) ≫ ψ.1 := by
  obtain ⟨M₀, -, h⟩ := torus_transport_bijective p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' hΛ' ψ ψinv hψ₁ hψ₂ hψmul
  exact ⟨M₀, h⟩

include hj 𝔛 hD hD' hψmul in
include hΛ' hψ₁ hψ₂ in

theorem torus_transport :
    ∃ Mx : (Fin O'.toricRank → ℤ) ≃+ (Fin O.toricRank → ℤ),
      O.torusFibre.1 ≫ (psiκ p M H hpM A hA Λ O Λ' O' ψ).1 =
        Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A)
          (Mx : (Fin O'.toricRank → ℤ) →+ (Fin O.toricRank → ℤ)))) ≫ O'.torusFibre.1 := by
  haveI : IsSeparated (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ'.σA) O'.g) := by
    haveI := O'.separated; dsimp only [RelativeGroupLaw.baseChangeStr]; infer_instance
  obtain ⟨y, hy⟩ := exists_y p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' hΛ' ψ hψmul
  obtain ⟨M₀, hbij, hM₀⟩ := transport_core (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ'.σA) O'.g) (O'.L.baseChange (resPt A ≫ Λ'.σA))
    O.toricRank O'.toricRank (toricRank_eq p M H hpM A hA Λ O Λ' O') O'.torusFibre (xT p M H hpM A hA Λ O Λ' O' ψ)
    O'.torusFibre_isClosedImmersion (isClosedImmersion_xT p M H hpM A hA Λ O Λ' O' ψ ψinv hψ₁ hψ₂)
    O'.torusFibre_mul (xT_mul p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' ψ hψmul) (range_xT_eq p M H hpM A hA Λ O Λ' O' ψ ψinv hψ₁ hψ₂ y hy)
  refine ⟨AddEquiv.ofBijective M₀ hbij, ?_⟩
  rw [← xT_val, hM₀]
  rfl

include hpM2 hj 𝔛 hD hpts_law hD' hΛ' hpts_law' ψinv hψ₁ hψ₂ hψmul in

private theorem _root_.TR.lift_transport (m : ℕ) (hm : 0 < m) :
    ∃ Mbar : (Fin O'.toricRank → ZMod m) →+ (Fin O.toricRank → ZMod m), Function.Bijective Mbar ∧
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom ↥A Mbar)) ≫ (O'.toricLift m hm).1 ≫ pullback.fst O'.g Λ'.σA =
        (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA ≫ ψ.1 := by
  obtain ⟨M₀, hbij, hM₀⟩ := torus_transport_bijective p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' hΛ' ψ ψinv hψ₁ hψ₂ hψmul
  obtain ⟨Mbar, hsq, h⟩ := TRL3.lift_transport O O' ψ ψinv hψ₁ hψ₂ (fun s x y => law_transfer p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' ψ hψmul s x y) M₀ hM₀ m hm
  refine ⟨Mbar, ?_, h⟩

  have hcast : ∀ n, Function.Surjective (TRL3.castPi n m) := by
    intro n w
    refine ⟨fun i => (w i).valMinAbs, ?_⟩
    ext i
    simp [TRL3.castPi, ZMod.coe_valMinAbs]
  have hsurj : Function.Surjective Mbar := by
    intro w
    obtain ⟨v, rfl⟩ := hcast _ w
    obtain ⟨u, rfl⟩ := hbij.2 v
    refine ⟨TRL3.castPi _ m u, ?_⟩
    have := congrArg (fun f : (Fin O'.toricRank → ℤ) →+ (Fin O.toricRank → ZMod m) => f u) hsq
    simpa using this
  haveI : NeZero m := ⟨hm.ne'⟩
  have hcard : Fintype.card (Fin O'.toricRank → ZMod m) = Fintype.card (Fin O.toricRank → ZMod m) := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, toricRank_eq p M H hpM A hA Λ O Λ' O']
  exact (Fintype.bijective_iff_surjective_and_card Mbar).mpr ⟨hsurj, hcard⟩

p2m_export "TR" "lift_transport"

def charEquiv {m : ℕ} (Mbar : (Fin O'.toricRank → ZMod m) →+ (Fin O.toricRank → ZMod m)) (hbij : Function.Bijective Mbar) :
    (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) ≃ (muCoord ↥A O'.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) where
  toFun χ := χ.comp (AddMonoidAlgebra.domCongr ↥A ↥A (AddEquiv.ofBijective Mbar hbij)).toAlgHom
  invFun χ' := χ'.comp (AddMonoidAlgebra.domCongr ↥A ↥A (AddEquiv.ofBijective Mbar hbij)).symm.toAlgHom
  left_inv χ := by ext; simp
  right_inv χ' := by
    have h2 : ∀ v, (AddEquiv.ofBijective Mbar hbij).symm (Mbar v) = v := fun v => (AddEquiv.symm_apply_eq _).mpr rfl
    ext i x
    simp [h2]

theorem charEquiv_toRingHom {m : ℕ} (Mbar : (Fin O'.toricRank → ZMod m) →+ (Fin O.toricRank → ZMod m)) (hbij : Function.Bijective Mbar)
    (χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) :
    (charEquiv p M H hpM A hA Λ O Λ' O' Mbar hbij χ).toRingHom = χ.toRingHom.comp (AddMonoidAlgebra.mapDomainRingHom ↥A Mbar) := by
  refine AddMonoidAlgebra.ringHom_ext (fun a => ?_) (fun v => ?_)
  · simp [charEquiv, AddMonoidAlgebra.mapDomainRingHom_apply]
  · simp [charEquiv, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.domCongr_single,
      AddMonoidAlgebra.mapDomain_single]

theorem pts_toricPoint_val (m : ℕ) (hm : 0 < m) (χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) :
    (O.pts (O.toricPoint m hm χ)).1 = (muPt A O.toricRank m χ).1 ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA := by
  simp only [JHNeronObjectAtP.toricPoint, Equiv.apply_symm_apply, genOfBaseChangePt, castOver,
    RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc]

theorem pts_toricPoint_val' (m : ℕ) (hm : 0 < m) (χ' : muCoord ↥A O'.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) :
    (O'.pts (O'.toricPoint m hm χ')).1 = (muPt A O'.toricRank m χ').1 ≫ (O'.toricLift m hm).1 ≫ pullback.fst O'.g Λ'.σA := by
  simp only [JHNeronObjectAtP.toricPoint, Equiv.apply_symm_apply, genOfBaseChangePt, castOver,
    RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc]

theorem muPt_charEquiv_val {m : ℕ} (Mbar : (Fin O'.toricRank → ZMod m) →+ (Fin O.toricRank → ZMod m)) (hbij : Function.Bijective Mbar)
    (χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) :
    (muPt A O'.toricRank m (charEquiv p M H hpM A hA Λ O Λ' O' Mbar hbij χ)).1 =
      (muPt A O.toricRank m χ).1 ≫ Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom ↥A Mbar)) := by
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← charEquiv_toRingHom]

include hpM2 hj 𝔛 hD hpts_law hD' hΛ' hpts_law' ψinv hψ₁ hψ₂ hψmul in

theorem toricLift_transport (m : ℕ) (hm : 0 < m) :
    ∃ a : (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) ≃ (muCoord ↥A O'.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
        (O'.pts (O'.toricPoint m hm (a χ))).1 = (O.pts (O.toricPoint m hm χ)).1 ≫ ψ.1 := by
  obtain ⟨Mbar, hbij, h⟩ := lift_transport p M H hpM hpM2 hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hΛ' hpts_law' ψ ψinv hψ₁ hψ₂ hψmul m hm
  refine ⟨charEquiv p M H hpM A hA Λ O Λ' O' Mbar hbij, fun χ => ?_⟩
  rw [pts_toricPoint_val', pts_toricPoint_val, muPt_charEquiv_val, Category.assoc, Category.assoc, Category.assoc, h]

end Main
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme.TRL3 P2MW.S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme.TR.LawEq"

end TR
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme.TRL3 P2MW.S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme.TR.LawEq P2MW.S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme.TR"

end
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme.TRL3 P2MW.S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme.TR.LawEq P2MW.S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme.TR"

open TR in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hpts_law : ∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y))
    (Λ' : JHNeronObjectAtP.LevelData p M H hpM A) (O' : JHNeronObjectAtP p M H hpM A hA Λ')
    (hD' : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O'.G, O'.g, (O'.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O'.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hΛ' : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ'.f)
    (hpts_law' : ∀ x y : JH M H,
        O'.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD').mul _ (O'.pts x) (O'.pts y))
    (ψ : SchemeHomOver O.g O'.g) (ψinv : SchemeHomOver O'.g O.g)
    (hψ₁ : ψ.1 ≫ ψinv.1 = 𝟙 _) (hψ₂ : ψinv.1 ≫ ψ.1 = 𝟙 _)

    (hψmul : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s x y) ψ =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD').mul s
          (NeronModelInfra.schemeHomOverComp x ψ) (NeronModelInfra.schemeHomOverComp y ψ)) :
    ∀ (m : ℕ) (hm : 0 < m),
      ∃ a : (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) ≃ (muCoord ↥A O'.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
        ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
          (O'.pts (O'.toricPoint m hm (a χ))).1 = (O.pts (O.toricPoint m hm χ)).1 ≫ ψ.1 := by
  intro m hm
  exact TR.toricLift_transport p M H hpM hpM2 hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hΛ' hpts_law' ψ ψinv hψ₁ hψ₂ hψmul m hm

end S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme (solution)
