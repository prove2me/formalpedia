-- Prove2me | solution 1 for GlobalTheory.unifPre_abelianPart_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:38:55.417919+00:00
-- url     : https://prove2.me/submissions/9118497a-d37b-4ba8-abc3-d6246fe8671f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnifPreAbelianPartIso
import Theorems.Thm_GlobalTheory_gtCoord_i_comp_q
import Theorems.Thm_GlobalTheory_flatQuotient_iso_of_same_kernel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
      ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R))))
        (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
        ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (e : ℕ),
          ∃ (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A),
            IsMonHom β.hom ∧ (U'.gt e).q ≫ β.hom = (U.gt e).q := by
  intro R _ _ _ I hR D D' A A' G _ _ _ U U' e
  obtain ⟨hN, -, -, hC⟩ := hR
  have hI : I ≠ ⊤ := by
    rintro rfl
    have : Subsingleton R := IsHausdorff.subsingleton hC.toIsHausdorff
    exact false_of_nontrivial_of_subsingleton R
  have := (U.gt e).q_affine
  have := (U'.gt e).q_affine
  exact flatQuotient_iso_of_same_kernel _ _ _ _ _ _ (U.gt e).q (U.gt e).i (U'.gt e).q (U'.gt e).i
    (U.gt e).q_hom (U.gt e).i_hom (U.gt e).q_flat (U.gt e).q_surj inferInstance (U.gt e).isKernel
    (U'.gt e).q_hom (U'.gt e).i_hom (U'.gt e).q_flat (U'.gt e).q_surj inferInstance
    (U'.gt e).isKernel (gtCoord_i_comp_q hI _ _) (gtCoord_i_comp_q hI _ _)
end GlobalTheory
