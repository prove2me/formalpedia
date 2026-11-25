-- Prove2me | solution 1 for GlobalTheory.ExtensionRigidity.isMonHom_of_pointed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:28:08.36673+00:00
-- url     : https://prove2.me/submissions/b1f26dd2-ad8c-4680-8bae-be055257c2ef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsMonHomPointedSplitExtToAbelianVariety
import Theorems.Thm_GlobalTheory_ExtensionRigidity_hom_ext_of_rationalPoints
import Theorems.Thm_GlobalTheory_ExtensionRigidity_exists_factor
import Theorems.Thm_GlobalTheory_T_splitTorus_to_abelianVariety_const
import Theorems.Thm_GlobalTheory_UnitRigidity_isPullback_act
import Theorems.Thm_GlobalTheory_UnitRigidity_smooth_geometricallyConnected_of_isGt
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_GlobalTheory_rigidity_holds
import Theorems.Thm_GlobalTheory_splitTorus_properties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ExtensionRigidity
namespace GlobalTheory.ExtensionRigidity
theorem _root_.solution :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (E : SplitExt (Sp K)) (G : Over (Sp K)) [GrpObj G], E.IsGt G → ∀ (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ f : G ⟶ B, η[G] ≫ f = η[B] → IsMonHom f := by
  intro K _ _ E G _ hG B _ hB f hf
  have := (UnitRigidity.smooth_geometricallyConnected_of_isGt E G hG).1
  obtain ⟨D⟩ := hG
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_affine
  have := E.free
  have := E.finite
  have := hB.proper
  obtain ⟨-, -, -, -, h1, -⟩ := (splitTorus_properties (Sp K)).1 E.X
  have : Smooth (splitTorus (Sp K) E.X).hom :=
    SmoothOfRelativeDimension.smooth (Module.finrank ℤ E.X) _
  have : Smooth (splitTorus (Sp K) E.X ⊗ G).hom :=
    inferInstanceAs (Smooth (pullback.fst (splitTorus (Sp K) E.X).hom G.hom ≫
      (splitTorus (Sp K) E.X).hom))
  have hact : ((fst (splitTorus (Sp K) E.X) G ≫ D.i) * snd _ G) ≫ f = snd _ G ≫ f := by
    refine hom_ext_of_rationalPoints _ _ fun x => ?_
    obtain ⟨b, hb⟩ := GlobalTheory.T.splitTorus_to_abelianVariety_const K E.X B hB ((D.i * (toUnit _ ≫ x ≫ snd _ G)) ≫ f)
    have e : ∀ t : 𝟙_ (Over (Sp K)) ⟶ splitTorus (Sp K) E.X,
        ((t ≫ D.i) * (x ≫ snd _ G)) ≫ f = b := by
      intro t
      have := congrArg (t ≫ ·) hb
      simp only [← Category.assoc, MonObj.comp_mul] at this
      rw [toUnit_unique (t ≫ toUnit _) (𝟙 _), Category.id_comp, Category.id_comp] at this
      exact this
    have e1 := e 1
    rw [MonObj.one_comp, _root_.one_mul] at e1
    rw [← Category.assoc, MonObj.comp_mul, ← Category.assoc, e, ← Category.assoc, e1]
  obtain ⟨β, hβ⟩ := exists_factor D.q f fun W a c h => by
    have H := UnitRigidity.isPullback_act D.i D.q D.isKernel
    rw [← H.lift_fst a c h, Category.assoc, hact, ← Category.assoc, H.lift_snd]
  have : IsMonHom β := rigidity_holds _ _ _ E.isAbelian hB β (by
    rw [← IsMonHom.one_hom D.q, Category.assoc, hβ, hf])
  rw [← hβ]
  infer_instance
end GlobalTheory.ExtensionRigidity
