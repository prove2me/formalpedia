-- Prove2me | solution 1 for GlobalTheory.quotient_isAbelianScheme_of_quotientScheme
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:42:22.565198+00:00
-- url     : https://prove2.me/submissions/0ef3cfc9-4218-44b1-9827-864e78a5b303

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuotientIsAbelianSchemeOfQuotientScheme
import Theorems.Thm_GlobalTheory_AbelianQuotient_exists_grpObj
import Theorems.Thm_GlobalTheory_AbelianQuotient_geometricallyReduced_of_comp
import Theorems.Thm_GlobalTheory_AbelianQuotient_geometricallyConnected_of_comp
import Theorems.Thm_GlobalTheory_AbelianQuotient_smooth_of_grpObj_of_flat
import Theorems.Thm_GlobalTheory_flat_of_comp_of_flat_of_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open AbelianQuotient
namespace GlobalTheory
theorem _root_.solution :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f →
      GeometricallyIntegral f) →
    (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Spec (CommRingCat.of R)))
      (H : Over (Spec (CommRingCat.of R))) [GrpObj H] (i : H ⟶ P.A), IsMonHom i → Mono i →
      IsFinite H.hom → Flat H.hom →
      ∃ (Q : Over (Spec (CommRingCat.of R))) (q : P.A ⟶ Q), IsFinite q.left ∧ Flat q.left ∧
        Surjective q.left ∧ IsSeparated Q.hom ∧ LocallyOfFiniteType Q.hom ∧
        IsPullback ((fst H P.A ≫ i) * snd H P.A) (snd H P.A) q q) →
    QuotientSt := by
  intro hint hquot R _ _ P H _ i hi hmono hfin hflat
  obtain ⟨Q, q, h1, h2, h3, h4, h5, hq⟩ := hquot R P H i hi hmono hfin hflat
  have := P.isAb.comm
  obtain ⟨inst, hcomm, hhom, hker⟩ := exists_grpObj i q hq
  refine ⟨Q, inst, ?_, q, hhom, h1, h2, h3, hker⟩
  have hw : q.left ≫ Q.hom = P.A.hom := Over.w q
  have := P.isAb.smooth
  have := P.isAb.proper
  have := P.isAb.geomConnected
  have := hint _ _ P.A.hom P.isAb.smooth P.isAb.geomConnected
  have : Flat (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyReduced (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyConnected (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have := flat_of_comp_of_flat_of_surjective q.left Q.hom
  have := UniversallyClosed.of_comp_surjective q.left Q.hom
  have := geometricallyReduced_of_comp q.left Q.hom
  have : LocallyOfFinitePresentation Q.hom := inferInstance
  exact ⟨hcomm, smooth_of_grpObj_of_flat Q, ⟨⟩, geometricallyConnected_of_comp q.left Q.hom⟩
end GlobalTheory
