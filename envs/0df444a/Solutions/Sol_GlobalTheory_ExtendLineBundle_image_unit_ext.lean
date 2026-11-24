-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.image_unit_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:51:44.556157+00:00
-- url     : https://prove2.me/submissions/b509cefc-2df5-4744-b69c-392ab268b2a8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Theorems.Thm_GlobalTheory_ExtendLineBundle_unit_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open GlobalTheory GlobalTheory.ExtendLineBundle
variable {X Y : Scheme.{0}} [IsIntegral X]
variable (j : Y ⟶ X) [IsOpenImmersion j]
namespace GlobalTheory.ExtendLineBundle
theorem _root_.solution {V : Y.Opens} {a b : Γ(Y, V)ˣ}
    (h : genericPoint X ∈ j ''ᵁ V → imageVal j V a = imageVal j V b) : a = b :=
  (imageUnit j V).injective (unit_ext h)
end GlobalTheory.ExtendLineBundle
