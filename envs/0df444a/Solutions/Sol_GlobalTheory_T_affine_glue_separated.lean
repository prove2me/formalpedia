-- Prove2me | solution 1 for GlobalTheory.T.affine_glue_separated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:23:56.876799+00:00
-- url     : https://prove2.me/submissions/a9007f19-f851-4e11-8cbe-f5e01d4de47a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineGlueSeparated
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecEquivResM
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineGlueSeparatedStatement
import Theorems.Thm_GlobalTheory_AffGlue_eq_zero_of_cover_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AffGlue
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {T : Scheme.{0}} (D : GlobalTheory.AffGlue.Data T) {V : T.Opens} (hV : IsAffineOpen V) {ι : Type} (W : ι → T.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V), V ≤ ⨆ i, W i → ∀ x : D.M V hV, (∀ i, D.ρ hV (hW i) (hWV i) x = 0) → x = 0 := by
  first | exact @GlobalTheory.AffGlue.eq_zero_of_cover_zero | exact GlobalTheory.AffGlue.eq_zero_of_cover_zero | (intros; apply GlobalTheory.AffGlue.eq_zero_of_cover_zero <;> assumption)
end _root_.GlobalTheory.T
