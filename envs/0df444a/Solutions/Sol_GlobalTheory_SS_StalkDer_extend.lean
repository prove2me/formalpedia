-- Prove2me | solution 1 for GlobalTheory.SS.StalkDer.extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:41:10.747679+00:00
-- url     : https://prove2.me/submissions/45fa28c4-f826-4734-be54-17f59255c87f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStalkDerivationOfIsPullback
import Theorems.Thm_GlobalTheory_SS_StalkDer_gm_res
import Theorems.Thm_GlobalTheory_SS_StalkDer_gmDual_res

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.StalkDer
variable {K : Type} [Field K] {P : Scheme.{0}} {X : Over (Sp K)}
namespace GlobalTheory.SS.StalkDer
theorem _root_.solution (D : VF X) (f : P ⟶ X.left) (z : P)
    (Φ : P.presheaf.stalk z →+* DualNumber (P.presheaf.stalk z)) (V₀ : X.left.Opens)
    (hV₀ : IsAffineOpen V₀) (hz₀ : z ∈ f ⁻¹ᵁ V₀)
    (H : ∀ u, Φ (gm f z V₀ hz₀ u) = gmDual D f z V₀ hz₀ u)
    (V : X.left.Opens) (hz : z ∈ f ⁻¹ᵁ V) (u : Γ(X.left, V)) :
    Φ (gm f z V hz u) = gmDual D f z V hz u := by
  obtain ⟨r, hr, hzr⟩ := hV₀.exists_basicOpen_le (V := V) ⟨f z, hz⟩ hz₀
  have hzr' : z ∈ f ⁻¹ᵁ X.left.basicOpen r := hzr
  have := hV₀.isLocalization_basicOpen r
  have e : Φ.comp (gm f z _ hzr') = gmDual D f z _ hzr' := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    refine RingHom.ext fun a => ?_
    have h1 := gm_res f z V₀ _ (X.left.basicOpen_le r) hzr' a
    have h2 := gmDual_res D f z V₀ _ (X.left.basicOpen_le r) hzr' a
    exact ((congrArg Φ h1).trans (H a)).trans h2.symm
  rw [← gm_res f z V _ hr hzr', ← gmDual_res D f z V _ hr hzr']
  exact RingHom.congr_fun e _
end GlobalTheory.SS.StalkDer
