-- Prove2me | solution 1 for GlobalTheory.LieEtale.existsUnique_tangent_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:48.655831+00:00
-- url     : https://prove2.me/submissions/bb4f2249-b43c-435b-9fd2-67fea7d506b6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueTangentLift
import Theorems.Thm_GlobalTheory_LieEtale_existsUnique_dual_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LieEtale
variable {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S)
variable {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (τ : O →+* k)
namespace GlobalTheory.LieEtale
theorem _root_.solution {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ]
    [Etale ψ.left] (w : epsPt x ⟶ B) (hw : epsPtZero x ≫ w = 1) :
    ∃! v : epsPt x ⟶ A, epsPtZero x ≫ v = 1 ∧ v ≫ ψ = w := by
  obtain ⟨v, ⟨h₁, h₂⟩, hu⟩ := existsUnique_dual_lift ψ.left w.left (1 : Over.mk x ⟶ A).left
    (congrArg (·.left) ((MonObj.one_comp ψ).trans hw.symm))
  refine ⟨Over.homMk v ?_, ⟨Over.OverMorphism.ext h₁, Over.OverMorphism.ext h₂⟩,
    fun v' hv' => Over.OverMorphism.ext
      (hu _ ⟨congrArg (·.left) hv'.1, congrArg (·.left) hv'.2⟩)⟩
  rw [← Over.w ψ, ← Category.assoc]
  exact (congrArg (· ≫ B.hom) h₂).trans (Over.w w)
end GlobalTheory.LieEtale
