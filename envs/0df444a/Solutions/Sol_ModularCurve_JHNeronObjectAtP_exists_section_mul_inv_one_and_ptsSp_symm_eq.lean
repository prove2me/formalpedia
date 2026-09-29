-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_section_mul_inv_one_and_ptsSp_symm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/9114cc00-3e8d-514f-8225-f10afb1072a0

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
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_ModularCurve_XHDiamondModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_section_mul_inv_one_and_ptsSp_symm_eq

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice"

open scoped MatrixGroups

namespace REDHOM

open ModularCurve ModularCurve.JHNeronObjectAtP ModularCurve.JZeroNeronObjectAtP GoodReductionJacobian in

theorem ofFibrePt_mul_toFibrePt
    {p : ℕ} {X : Scheme.{0}} {f : X ⟶ base p} (L : RelativeGroupLaw (baseRing p) f)
    {R' : Type} [CommRing R'] (r : Spec (CommRingCat.of R') ⟶ base p)
    (x y : NeronModelInfra.SchemeHomOver r f) :
    ofFibrePt ((L.baseChange r).mul _ (toFibrePt x) (toFibrePt y)) = L.mul r x y := by
  apply Subtype.ext
  show (RelativeGroupLaw.baseChangePointToBase r ((L.baseChange r).mul _ (toFibrePt x) (toFibrePt y))).1 = _
  rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointToBase_ofBase]

  have hx : RelativeGroupLaw.baseChangePointToBase r (toFibrePt x) = schemeHomOverComp (𝟙 _) rfl x := by
    unfold toFibrePt; rw [RelativeGroupLaw.baseChangePointToBase_ofBase]; exact Subtype.ext (Category.id_comp _).symm
  have hy : RelativeGroupLaw.baseChangePointToBase r (toFibrePt y) = schemeHomOverComp (𝟙 _) rfl y := by
    unfold toFibrePt; rw [RelativeGroupLaw.baseChangePointToBase_ofBase]; exact Subtype.ext (Category.id_comp _).symm
  rw [hx, hy, ← L.mul_natural r (𝟙 _ ≫ r) (𝟙 _) rfl x y, GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp]

end REDHOM

set_option maxHeartbeats 1600000 in
open ModularCurve ModularCurve.JHNeronObjectAtP in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ) :

    (∀ (x y : JH M H) (s t : NeronModelInfra.SchemeHomOver Λ.σA O.g),
      (O.pts x).1 = barPt A ≫ s.1 → (O.pts y).1 = barPt A ≫ t.1 →
        (O.pts (x + y)).1 = barPt A ≫ (O.L.mul Λ.σA s t).1 ∧
        O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (O.L.mul Λ.σA s t)) =
          O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s) +
            O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ t)) ∧

    (∀ (x : JH M H) (s : NeronModelInfra.SchemeHomOver Λ.σA O.g),
      (O.pts x).1 = barPt A ≫ s.1 →
        (O.pts (-x)).1 = barPt A ≫ (O.L.inv Λ.σA s).1 ∧
        O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (O.L.inv Λ.σA s)) =
          - O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s)) ∧

    ((O.pts 0).1 = barPt A ≫ (O.L.one Λ.σA).1 ∧
      O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (O.L.one Λ.σA)) = 0) ∧

    (∀ s : NeronModelInfra.SchemeHomOver Λ.σA O.g,
      O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s) = 0 ↔
        resPt A ≫ s.1 = (resPt A ≫ Λ.σA) ≫ (O.L.one (𝟙 (base p))).1) ∧

    (∀ s t : NeronModelInfra.SchemeHomOver Λ.σA O.g, barPt A ≫ s.1 = barPt A ≫ t.1 → s = t) := by

  letI instG : Group (NeronModelInfra.SchemeHomOver (genPt p) O.g) := O.L.pointGroup (genPt p)
  letI instA : Group (NeronModelInfra.SchemeHomOver Λ.σA O.g) := O.L.pointGroup Λ.σA
  letI instK : Group (NeronModelInfra.SchemeHomOver (resPt A ≫ Λ.σA) O.g) := O.L.pointGroup (resPt A ≫ Λ.σA)

  let γ : NeronModelInfra.SchemeHomOver Λ.σA O.g →* NeronModelInfra.SchemeHomOver (genPt p) O.g :=
    { toFun := fun s => GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA s
      map_one' := O.L.one_natural Λ.σA (genPt p) (barPt A) Λ.hσA
      map_mul' := fun s t => O.L.mul_natural Λ.σA (genPt p) (barPt A) Λ.hσA s t }
  let ρ : NeronModelInfra.SchemeHomOver Λ.σA O.g →* NeronModelInfra.SchemeHomOver (resPt A ≫ Λ.σA) O.g :=
    { toFun := fun s => GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s
      map_one' := O.L.one_natural Λ.σA (resPt A ≫ Λ.σA) (resPt A) rfl
      map_mul' := fun s t => O.L.mul_natural Λ.σA (resPt A ≫ Λ.σA) (resPt A) rfl s t }
  have hγ : ∀ s, (γ s).1 = barPt A ≫ s.1 := fun s => rfl
  have hρ : ∀ s, NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s = ρ s := fun s => rfl

  have hpts_mul : ∀ x y : JH M H, O.pts (x + y) = O.pts x * O.pts y := O.pts_add
  have hptsSp_mul : ∀ a b, O.ptsSp (a + b) = O.ptsSp a * O.ptsSp b := by
    intro a b; rw [O.ptsSp_add]; exact REDHOM.ofFibrePt_mul_toFibrePt O.L (resPt A ≫ Λ.σA) _ _
  have hpts0 : O.pts 0 = 1 := by
    have h : O.pts 0 = O.pts 0 * O.pts 0 := (congrArg O.pts (add_zero (0 : JH M H))).symm.trans (hpts_mul 0 0)
    exact mul_eq_left.mp h.symm
  have hptsSp0 : O.ptsSp 0 = 1 := by
    have h : O.ptsSp 0 = O.ptsSp 0 * O.ptsSp 0 := (congrArg O.ptsSp (add_zero (0 : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset))).symm.trans (hptsSp_mul 0 0)
    exact mul_eq_left.mp h.symm
  have hpts_neg : ∀ x : JH M H, O.pts (-x) = (O.pts x)⁻¹ := by
    intro x
    have h : O.pts x * O.pts (-x) = 1 := by rw [← hpts_mul, add_neg_cancel, hpts0]
    exact (eq_inv_of_mul_eq_one_right h)
  have hptsSp_neg : ∀ a : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset, O.ptsSp (-a) = (O.ptsSp a)⁻¹ := by
    intro a
    have h : O.ptsSp a * O.ptsSp (-a) = 1 := by rw [← hptsSp_mul, add_neg_cancel, hptsSp0]
    exact (eq_inv_of_mul_eq_one_right h)

  have hcar : ∀ (x : JH M H) (s : NeronModelInfra.SchemeHomOver Λ.σA O.g),
      (O.pts x).1 = barPt A ≫ s.1 ↔ γ s = O.pts x := by
    intro x s; constructor
    · intro h; exact Subtype.ext h.symm
    · intro h; exact (congrArg Subtype.val h).symm

  have hsymm_mul : ∀ a b : NeronModelInfra.SchemeHomOver (resPt A ≫ Λ.σA) O.g,
      O.ptsSp.symm (a * b) = O.ptsSp.symm a + O.ptsSp.symm b := by
    intro a b
    apply O.ptsSp.injective
    rw [hptsSp_mul, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hsymm_inv : ∀ a : NeronModelInfra.SchemeHomOver (resPt A ≫ Λ.σA) O.g,
      O.ptsSp.symm a⁻¹ = - O.ptsSp.symm a := by
    intro a
    apply O.ptsSp.injective
    rw [hptsSp_neg, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hsymm_one : O.ptsSp.symm 1 = 0 := by
    apply O.ptsSp.injective; rw [Equiv.apply_symm_apply, hptsSp0]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x y s t hs ht
    refine ⟨?_, ?_⟩
    · rw [hcar] at hs ht ⊢
      show γ (s * t) = _
      rw [map_mul, hs, ht, hpts_mul]
    · rw [hρ, hρ, hρ]
      show O.ptsSp.symm (ρ (s * t)) = _
      rw [map_mul, hsymm_mul]
  ·
    intro x s hs
    refine ⟨?_, ?_⟩
    · rw [hcar] at hs ⊢
      show γ s⁻¹ = _
      rw [map_inv, hs, hpts_neg]
    · rw [hρ, hρ]
      show O.ptsSp.symm (ρ s⁻¹) = _
      rw [map_inv, hsymm_inv]
  ·
    refine ⟨?_, ?_⟩
    · rw [hcar]
      show γ 1 = _
      rw [map_one, hpts0]
    · rw [hρ]
      show O.ptsSp.symm (ρ 1) = 0
      rw [map_one, hsymm_one]
  ·
    intro s
    rw [hρ]
    constructor
    · intro h
      have h1 : ρ s = 1 := by
        apply O.ptsSp.symm.injective; rw [h, hsymm_one]
      have h2 := congrArg Subtype.val h1

      have h3 : (O.L.one (resPt A ≫ Λ.σA)).1 = (resPt A ≫ Λ.σA) ≫ (O.L.one (𝟙 (base p))).1 := by
        rw [← O.L.one_natural (𝟙 (base p)) (resPt A ≫ Λ.σA) (resPt A ≫ Λ.σA) (Category.comp_id _)]
        rfl
      rw [← h3]
      exact h2
    · intro h
      have h3 : (O.L.one (resPt A ≫ Λ.σA)).1 = (resPt A ≫ Λ.σA) ≫ (O.L.one (𝟙 (base p))).1 := by
        rw [← O.L.one_natural (𝟙 (base p)) (resPt A ≫ Λ.σA) (resPt A ≫ Λ.σA) (Category.comp_id _)]
        rfl
      have h1 : ρ s = 1 := Subtype.ext (h.trans h3.symm)
      rw [h1]
      exact hsymm_one
  ·
    intro s t hst
    haveI : IsSeparated O.g := O.separated
    have hU := (IsSeparated.valuativeCriterion (f := O.g))

    have halg : CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ)) = CommRingCat.ofHom A.subtype := rfl
    have hst' : Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))) ≫ t.1 =
        Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))) ≫ s.1 := by
      rw [halg]; exact hst.symm
    let sq : ValuativeCommSq O.g :=
      { R := ↥A, K := AlgebraicClosure ℚ
        i₁ := Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))) ≫ s.1
        i₂ := Λ.σA
        commSq := ⟨by rw [Category.assoc, s.2]⟩ }
    have hsub : Subsingleton sq.commSq.LiftStruct := hU sq
    have h := hsub.elim ⟨s.1, rfl, s.2⟩ ⟨t.1, hst', t.2⟩
    exact Subtype.ext (congrArg CommSq.LiftStruct.l h)

end S_ModularCurve_JHNeronObjectAtP_exists_section_mul_inv_one_and_ptsSp_symm_eq
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_section_mul_inv_one_and_ptsSp_symm_eq (solution)
