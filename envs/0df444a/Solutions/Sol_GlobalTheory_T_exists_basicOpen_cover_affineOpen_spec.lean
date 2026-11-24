-- Prove2me | solution 1 for GlobalTheory.T.exists_basicOpen_cover_affineOpen_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:12:32.774691+00:00
-- url     : https://prove2.me/submissions/1970dd0d-d32d-4e40-8f7d-0317cfa6572c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpenCoverAffineOpenSpec
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpenCoverAffineOpenSpecStatement
import Theorems.Thm_GlobalTheory_SecGlue_exists_basicOpen_cover_affine


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S : Type) [CommRing S] (Y : Scheme.{0}) (u : Sp S ⟶ Y),
    ∃ (n : ℕ) (s : Fin n → S) (W : Fin n → Y.Opens), Ideal.span (Set.range s) = ⊤ ∧
      (∀ i, IsAffineOpen (W i)) ∧ ∀ i, (spMap (algebraMap S (Localization.Away (s i))) ≫ u) ⁻¹ᵁ W i = ⊤ := by
  first | exact @GlobalTheory.SecGlue.exists_basicOpen_cover_affine | exact GlobalTheory.SecGlue.exists_basicOpen_cover_affine | (intros; apply GlobalTheory.SecGlue.exists_basicOpen_cover_affine <;> assumption)
end _root_.GlobalTheory.T
