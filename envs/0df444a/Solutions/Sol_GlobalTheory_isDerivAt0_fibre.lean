-- Prove2me | solution 1 for GlobalTheory.isDerivAt0_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:24:19.303804+00:00
-- url     : https://prove2.me/submissions/5cc1266d-12da-4276-ac90-342f4352b394

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDerivAt0OfIsPullback
import Theorems.Thm_GlobalTheory_FibreDeriv_isDerivAt0_comp
import Theorems.Thm_GlobalTheory_FibreDeriv_isDerivAt0_of_isPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology
open GlobalTheory
open FibreDeriv
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X : Scheme.{0}) (G : Over X) (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (Y : Scheme.{0}) (φ : Y ⟶ G.left) (s : Y ⟶ Sp ℂ) (e₁ : (Fin g → ℂ) → (Sp ℂ ⟶ Y)), IsPullback φ s G.hom y → (∀ z, e₁ z ≫ φ = (e z).left ∧ e₁ z ≫ s = 𝟙 _) → IsHolTo Set.univ (fun z => (e z).left) → ((∀ w, ∃! v : epsPt y ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ ∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) → ((∀ w, ∃! v : Sp (DualNumber ℂ) ⟶ Y, v ≫ s = spMap (algebraMap ℂ (DualNumber ℂ)) ∧ IsDerivAt0 e₁ w v) ∧ ∀ v : Sp (DualNumber ℂ) ⟶ Y, v ≫ s = spMap (algebraMap ℂ (DualNumber ℂ)) → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e₁ 0 → ∃! w, IsDerivAt0 e₁ w v) := by
  intro X G y g e Y φ s e₁ H he hol hd
  have hee : (fun z => (e z).left) = fun z => e₁ z ≫ φ := funext fun z => (he z).1.symm
  have hs : ∀ z, e₁ z ≫ s = 𝟙 _ := fun z => (he z).2
  have key : ∀ (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ Y), v ≫ s = spMap (algebraMap ℂ (DualNumber ℂ)) →
      (IsDerivAt0 e₁ w v ↔ IsDerivAt0 (fun z => (e z).left) w (v ≫ φ)) := fun w v hv => by
    constructor
    · intro h
      have := isDerivAt0_comp h φ
      rw [← hee] at this
      exact this
    · intro h
      refine isDerivAt0_of_isPullback H hs ?_ hv ?_
      · rw [← hee]; exact hol
      · rw [← hee]; exact h
  have hw : ∀ v : Sp (DualNumber ℂ) ⟶ Y, v ≫ s = spMap (algebraMap ℂ (DualNumber ℂ)) →
      (v ≫ φ) ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y := fun v hv => by
    rw [Category.assoc, H.w, ← Category.assoc, hv]
  refine ⟨fun w => ?_, fun v hv h0 => ?_⟩
  · obtain ⟨u, hu, huniq⟩ := hd.1 w
    have huw : u.left ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y := Over.w u
    refine ⟨H.lift u.left _ huw, ⟨H.lift_snd _ _ _, (key w _ (H.lift_snd _ _ _)).2 ?_⟩, fun v hv => ?_⟩
    · rw [H.lift_fst]; exact hu
    · have h1 := huniq (Over.homMk (v ≫ φ) (hw v hv.1)) ((key w v hv.1).1 hv.2)
      refine H.hom_ext ?_ (by rw [H.lift_snd, hv.1])
      rw [H.lift_fst, ← h1]
      rfl
  · have h1 := hd.2 (Over.homMk (v ≫ φ) (hw v hv)) (by
      change _ ≫ v ≫ φ = _
      rw [← Category.assoc, h0, (he 0).1])
    simp only [key _ v hv]
    exact h1
end GlobalTheory
