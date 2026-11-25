-- Prove2me | solution 1 for GlobalTheory.T.lineBundle_trivial_iso_descend_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:47:48.782588+00:00
-- url     : https://prove2.me/submissions/f04b65a4-2296-4cb4-8e2c-6cbf5b045f2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LineBundleTrivialIsoDescendField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LineBundleTrivialIsoDescendFieldStatement
import Theorems.Thm_GlobalTheory_lb_gen_iso_descend_field


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
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀), Smooth p₀ → IsProper p₀ → GeometricallyConnected p₀ → IsPullback φ p p₀ (spMap i) → (∀ M : LB X₀, M.IsLB → (∃ t : (M.pull φ).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen) ∧ ∀ M N : LB X₀, M.IsLB → N.IsLB → LBIso (M.pull φ) (N.pull φ) → LBIso M N := by
  first | exact @GlobalTheory.lb_gen_iso_descend_field | exact GlobalTheory.lb_gen_iso_descend_field | (intros; apply GlobalTheory.lb_gen_iso_descend_field <;> assumption)
end _root_.GlobalTheory.T
