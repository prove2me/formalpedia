-- Prove2me | solution 1 for GlobalTheory.T.splitTorus_extension_descends_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:42:18.548798+00:00
-- url     : https://prove2.me/submissions/69c8b54b-543b-48d6-b7c5-f981eac2a71f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusExtensionDescends
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusExtensionDescendsStatement
import Theorems.Thm_GlobalTheory_splitTorus_extension_descends


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
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (G B : Over (Sp K)) [GrpObj G] [GrpObj B] (G₀ B₀ : Over (Sp k)) [GrpObj G₀] [GrpObj B₀] (X : Type) [AddCommGroup X] (φG : G.left ⟶ G₀.left) (φ : B.left ⟶ B₀.left), IsGrpPullback G G₀ (spMap β) φG → IsGrpPullback B B₀ (spMap β) φ → ∀ (q : G ⟶ B) (i : splitTorus (Sp K) X ⟶ G) (q₀ : G₀ ⟶ B₀) (i₀ : splitTorus (Sp k) X ⟶ G₀), φG ≫ q₀.left = q.left ≫ φ → GlobalTheory.SplitTorus.bcMap (spMap β) X ≫ i₀.left = i.left ≫ φG → IsMonHom q → Flat q.left → Surjective q.left → QuasiCompact q.left → IsMonHom i → IsPullback i (toUnit _) q (η[B] : 𝟙_ _ ⟶ B) → IsMonHom q₀ ∧ Flat q₀.left ∧ Surjective q₀.left ∧ QuasiCompact q₀.left ∧ IsMonHom i₀ ∧ IsPullback i₀ (toUnit _) q₀ (η[B₀] : 𝟙_ _ ⟶ B₀) := by
  first | exact @GlobalTheory.splitTorus_extension_descends | exact GlobalTheory.splitTorus_extension_descends | (intros; apply GlobalTheory.splitTorus_extension_descends <;> assumption)
end _root_.GlobalTheory.T
