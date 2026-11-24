-- Prove2me | solution 1 for GlobalTheory.SS.exists_stalk_derivation_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:10:47.64163+00:00
-- url     : https://prove2.me/submissions/9963f622-50f5-4c83-8e31-cf116164dab3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStalkDerivationOfIsPullback
import Theorems.Thm_GlobalTheory_SS_StalkDer_germ_appLE
import Theorems.Thm_GlobalTheory_SS_StalkDer_exists_dual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS
open StalkDer
namespace GlobalTheory.SS
theorem _root_.solution : ∀ (K : Type) [Field K] (P X Y : Over (Sp K)) (p : P.left ⟶ X.left) (q : P.left ⟶ Y.left), IsPullback p q X.hom Y.hom → ∀ (D : VF X) (z : P.left), ∃ δ : P.left.presheaf.stalk z →+ P.left.presheaf.stalk z, (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧ (∀ (V : X.left.Opens) (W : P.left.Opens) (h : W ≤ p ⁻¹ᵁ V) (hz : z ∈ W) (u : Γ(X.left, V)), δ ((P.left.presheaf.germ W z hz).hom ((p.appLE V W h).hom u)) = (P.left.presheaf.germ W z hz).hom ((p.appLE V W h).hom (D.D V u))) ∧ ∀ (V : Y.left.Opens) (W : P.left.Opens) (h : W ≤ q ⁻¹ᵁ V) (hz : z ∈ W) (u : Γ(Y.left, V)), δ ((P.left.presheaf.germ W z hz).hom ((q.appLE V W h).hom u)) = 0 := by
  intro K _ P X Y p q H D z
  obtain ⟨Φ, h0, h1, h2⟩ := exists_dual p q H D (VF.zero Y) z
  refine ⟨⟨⟨fun x => (Φ x).snd, by simp⟩, fun a b => by simp⟩, fun a b => ?_,
    fun V W h hz u => ?_, fun V W h hz u => ?_⟩
  · show (Φ (a * b)).snd = a * (Φ b).snd + b * (Φ a).snd
    rw [map_mul, DualNumber.snd_mul, h0, h0]; ring
  · rw [germ_appLE, germ_appLE]
    exact congrArg TrivSqZeroExt.snd (h1 V (h hz) u)
  · rw [germ_appLE]
    exact (congrArg TrivSqZeroExt.snd (h2 V (h hz) u)).trans (map_zero (gm q z V (h hz)))
end GlobalTheory.SS
