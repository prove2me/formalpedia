-- Prove2me | solution 1 for GlobalTheory.SS.LiftTorus.exists_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:14:56.922287+00:00
-- url     : https://prove2.me/submissions/82340392-27c0-4813-8835-c708013267c8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UniqueFactorizationMonoidAddMonoidAlgebraOfFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftOneParameterQuotientTorus
import Theorems.Thm_GlobalTheory_SS_LiftTorus_exists_retraction
import Theorems.Thm_GlobalTheory_TorsorUnit_IsTorsorOn_of_equiv
import Theorems.Thm_GlobalTheory_TorsorUnit_exists_coaction
import Theorems.Thm_GlobalTheory_TorsorUnit_exists_eq_pt
import Theorems.Thm_GlobalTheory_TorsorUnit_faithfullyFlat_appLE
import Theorems.Thm_GlobalTheory_TorsorUnit_isTorsorOn
import Theorems.Thm_GlobalTheory_TorsorUnit_le_pt_preimage
import Theorems.Thm_GlobalTheory_TorsorUnit_pt_appLE
import Theorems.Thm_GlobalTheory_TorsorUnit_pt_comp
import Theorems.Thm_P2M_GlobalTheory_pic_groupAlgebra_of_isIntegrallyClosed__4f9bdb8fe068


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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LiftTorus
open GlobalTheory.TorsorUnit
namespace GlobalTheory.SS.LiftTorus
theorem _root_.solution {S : Scheme.{0}} {X : Type} [AddCommGroup X] [Module.Free ℤ X] {G B : Over S}
    [GrpObj G] [GrpObj B] {q : G ⟶ B} {i : splitTorus S X ⟶ G} [IsMonHom q] [IsMonHom i]
    [Flat q.left] [Surjective q.left] [IsAffineHom q.left] [IsAffine B.left]
    [Subsingleton (CommRing.Pic Γ(B.left, ⊤))]
    (hi : IsPullback i (toUnit _) q η[B]) : ∃ s : B ⟶ G, s ≫ q = 𝟙 B := by
  have hV : IsAffineOpen (⊤ : B.left.Opens) := isAffineOpen_top _
  have hU : IsAffineOpen (q.left ⁻¹ᵁ ⊤) := hV.preimage q.left
  obtain ⟨ρ, hρ⟩ := exists_coaction hi hU
  have htor : ∀ (R : Type) [CommRing R], IsTorsorOn R (q.left.appLE ⊤ _ le_rfl).hom ρ :=
    fun R _ => (isTorsorOn hi hV hU hρ (Spec (.of R))).of_equiv
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  obtain ⟨σ, hσ⟩ := exists_retraction (faithfullyFlat_appLE q.left hV hU) htor
  have h1 : pt hU σ ≫ q.left = 𝟙 B.left := by
    rw [pt_comp hU hV q.left le_rfl, hσ]
    obtain ⟨θ, hθ⟩ := exists_eq_pt hV (𝟙 B.left) le_rfl
    have h2 := pt_appLE hV θ (le_pt_preimage hV θ)
    have h3 : ∀ (g : B.left ⟶ B.left) (e : ⊤ ≤ g ⁻¹ᵁ ⊤), g = 𝟙 _ →
        (g.appLE ⊤ ⊤ e).hom = RingHom.id _ := by
      rintro _ e rfl
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
      exact congrArg CommRingCat.Hom.hom ((Category.id_comp _).trans (B.left.presheaf.map_id _))
    rw [hθ, ← h2, h3 _ _ hθ.symm]
  refine ⟨Over.homMk (pt hU σ) ?_, Over.OverMorphism.ext h1⟩
  rw [← Over.w q, ← Category.assoc, h1, Category.id_comp]
end GlobalTheory.SS.LiftTorus
