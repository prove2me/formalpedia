-- Prove2me | solution 1 for GlobalTheory.corr_of_generic_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:07:58.657799+00:00
-- url     : https://prove2.me/submissions/c90a5742-14d9-4f07-ba99-d0ffa0b4dd0d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CorrOfGenericOfIsSeparated
import Theorems.Thm_GlobalTheory_corr_of_corr_pullGen
import Theorems.Thm_GlobalTheory_ExtUnique_hom_ext_of_dominant
import Theorems.Thm_GlobalTheory_ExtUnique_spec_fractionRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution
    (V : Type u) [CommRing V] (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K]
    (G : Over (Spec (CommRingCat.of V))) [IsSeparated G.hom]
    (T : Over (Spec (CommRingCat.of V))) [Flat T.hom]
    (L : LB G.left) {I I' : Type u} [Fintype I] [Fintype I']
    (φ : I → (T.left ⟶ G.left)) (ε : I → ℤ) (φ' : I' → (T.left ⟶ G.left)) (ε' : I' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (H : LB.Gen.Corr L _ _ _ _
      (LB.pullGen L _ _ t (pullback.fst T.hom (Spec.map (CommRingCat.ofHom (algebraMap V K)))))
      (LB.pullGen L _ _ t' (pullback.fst T.hom (Spec.map (CommRingCat.ofHom (algebraMap V K)))))) :
    LB.Gen.Corr L _ _ _ _ t t' := by
  have := (ExtUnique.spec_fractionRing V K).2
  have : IsSchemeTheoreticallyDominant
      (pullback.fst T.hom (Spec.map (CommRingCat.ofHom (algebraMap V K)))) :=
    .of_isPullback (IsPullback.of_hasPullback _ _).flip
  refine corr_of_corr_pullGen L φ ε φ' ε' t t' _ (fun U => Scheme.Hom.app_injective _ U)
    (fun a b e => ?_) H
  exact ExtUnique.hom_ext_of_dominant (G.hom ≫ terminal.from _) (terminal.hom_ext _ _) _ e
end GlobalTheory
