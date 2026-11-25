-- Prove2me | solution 1 for GlobalTheory.SegreCoord.exists_segre_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:11:55.057717+00:00
-- url     : https://prove2.me/submissions/cf336b10-af4f-4d4d-93b7-d691af2f6fc7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates
import Theorems.Thm_GlobalTheory_SegreCoord_projRep_box
import Theorems.Thm_GlobalTheory_SegreCoord_secCoord_box

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SegreCoord
variable {X : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec} {T T' : Type} [CommRing T] [CommRing T']
namespace GlobalTheory.SegreCoord
theorem _root_.solution : ∀ (R σ : Type) [CommRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)) (Z : Over (Sp R)) (M : LB Z.left) (th : σ → M.Sec), ProjRep I Z.hom M th → ∃ (I₂ : Ideal (MvPolynomial (σ × σ) R)) (M₂ : LB (Z ⊗ Z).left) (th₂ : σ × σ → M₂.Sec), ProjRep I₂ (Z ⊗ Z).hom M₂ th₂ ∧ ∀ (T : Type) [CommRing T] (x : Sp T ⟶ (Z ⊗ Z).left) (v₁ v₂ : σ → T), SecCoord M th (x ≫ (fst Z Z).left) v₁ → SecCoord M th (x ≫ (snd Z Z).left) v₂ → SecCoord M₂ th₂ x (fun i => v₁ i.1 * v₂ i.2) := by
  intro R σ _ _ I Z M th H
  have hP : IsPullback (fst Z Z).left (snd Z Z).left Z.hom Z.hom := IsPullback.of_hasPullback Z.hom Z.hom
  refine ⟨segreIdeal I, boxLB M (fst Z Z).left (snd Z Z).left, boxTh th (fst Z Z).left (snd Z Z).left, ?_,
    fun T _ x v₁ v₂ h₁ h₂ => secCoord_box H hP x v₁ v₂ h₁ h₂⟩
  rw [← Over.w (fst Z Z)]
  exact projRep_box H hP
end GlobalTheory.SegreCoord
