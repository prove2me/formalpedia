-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.relativeGroupLaw_mul_eq_mul_genPt_of_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/e96cd436-f51a-5bf5-93e2-d54121e0df8a

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
import Definitions.Def_JacJ1Iface
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_mul_eq_mul_of_one_eq_of_abelianSchemePropertyBundle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_relativeGroupLaw_mul_eq_mul_genPt_of_one_eq
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice"

open scoped MatrixGroups

namespace RigidLawO

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)

noncomputable abbrev ιQ : Spec (CommRingCat.of ℚ) ⟶ base p := Spec.map (CommRingCat.ofHom (algebraMap (baseRing p) ℚ))

noncomputable abbrev sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))

theorem genPt_eq : genPt p = sbar ≫ ιQ p := by
  change Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

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

theorem abelianBundle_genericFibre :
    AbelianSchemePropertyBundle ℚ (RelativeGroupLaw.baseChangeStr (ιQ p) O.g) := by
  haveI := O.smooth
  haveI := O.proper_generic
  refine ⟨inferInstance, ?_, ?_, ⟨O.L.baseChange (ιQ p)⟩⟩
  ·
    exact O.proper_generic
  ·
    intro s
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

theorem mul_eq_over_sbar (L₂ : RelativeGroupLaw (baseRing p) O.g)
    (hone : ∀ {T : Scheme.{0}} (s : T ⟶ base p), (L₂.one s).1 = (O.L.one s).1) :
    ∀ a b : SchemeHomOver (sbar ≫ ιQ p) O.g, L₂.mul _ a b = O.L.mul _ a b := by
  intro a b
  have key := GoodReductionJacobian.RelativeGroupLaw.mul_eq_mul_of_one_eq_of_abelianSchemePropertyBundle ℚ
    (abelianBundle_genericFibre p M H hpM A hA Λ O) (L₂.baseChange (ιQ p)) (O.L.baseChange (ιQ p))
    (one_baseChange_eq p M H hpM A hA Λ O L₂ hone) sbar
    (RelativeGroupLaw.baseChangePointOfBase (ιQ p) a) (RelativeGroupLaw.baseChangePointOfBase (ιQ p) b)
  have := congrArg (RelativeGroupLaw.baseChangePointToBase (ιQ p)) key
  rwa [RelativeGroupLaw.baseChangePointToBase_mul, RelativeGroupLaw.baseChangePointToBase_mul,
    RelativeGroupLaw.baseChangePointToBase_ofBase, RelativeGroupLaw.baseChangePointToBase_ofBase] at this

theorem mul_eq_mul_of_eq {R : Type} [CommRing R] {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    (L Lc : RelativeGroupLaw R g) {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of R)}
    (h : s' = s) (hs : ∀ a b : SchemeHomOver s g, L.mul s a b = Lc.mul s a b) :
    ∀ a b : SchemeHomOver s' g, L.mul s' a b = Lc.mul s' a b := by
  subst h; exact hs

end RigidLawO
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_relativeGroupLaw_mul_eq_mul_genPt_of_one_eq.RigidLawO"

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (L₂ : RelativeGroupLaw (baseRing p) O.g)
    (hone : ∀ {T : Scheme.{0}} (s : T ⟶ base p), (L₂.one s).1 = (O.L.one s).1) :
    ∀ x y : SchemeHomOver (genPt p) O.g, (L₂.mul _ x y).1 = (O.L.mul _ x y).1  := by
  intro x y
  exact congrArg Subtype.val
    (RigidLawO.mul_eq_mul_of_eq L₂ O.L (RigidLawO.genPt_eq p) (RigidLawO.mul_eq_over_sbar p M H hpM A hA Λ O L₂ hone) x y)

end S_ModularCurve_JHNeronObjectAtP_relativeGroupLaw_mul_eq_mul_genPt_of_one_eq
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_relativeGroupLaw_mul_eq_mul_genPt_of_one_eq (solution)
