-- Prove2me | solution 1 for GlobalTheory.KS.EpsBundle.overlap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:25:56.411483+00:00
-- url     : https://prove2.me/submissions/cf1744bc-619f-40fc-8c86-ace16f73574b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TrivialIffCoboundary
import Theorems.Thm_GlobalTheory_KS_EpsBundle_uniq

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.EpsBundle
namespace GlobalTheory.KS.EpsBundle
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (e : B) (he : e * e = 0)
    (H : ∀ F : B, ∃! ab : A × A, F = φ ab.1 + e * φ ab.2) {b b' c d d' c' k : A}
    (hb : b * b' = 1) (hd : d * d' = 1)
    (h : φ b + e * φ c = (1 + e * φ k) * (φ d + e * φ c')) : k = c * b' - c' * d' := by
  obtain ⟨h1, h2⟩ := uniq φ e H (a := b) (b := c) (a' := d) (b' := c' + k * d) (by
    simp only [map_mul, map_add]
    linear_combination h + (φ k * φ c') * he)
  subst h1
  have h3 : b' = d' := by linear_combination d' * hb - b' * hd + (0 : A)
  subst h3
  linear_combination (-b') * h2 - k * hb
end GlobalTheory.KS.EpsBundle
