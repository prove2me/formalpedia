-- Prove2me | solution 1 for GlobalTheory.T.exists_derivation_split_kaehlerD_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:34:02.833621+00:00
-- url     : https://prove2.me/submissions/b4b1db29-16f6-4693-8658-3d24308076ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDerivationSplitKaehlerDSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDerivationSplitKaehlerDSmoothStatement
import Theorems.Thm_GlobalTheory_bertini_derivation_split


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A], ∃ (n : ℕ) (δ : Fin n → Derivation k A A) (ω : Fin n → KaehlerDifferential k A), ∀ a : A, KaehlerDifferential.D k A a = ∑ l, δ l a • ω l := by
  first | exact @GlobalTheory.bertini_derivation_split | exact GlobalTheory.bertini_derivation_split | (intros; apply GlobalTheory.bertini_derivation_split <;> assumption)
end _root_.GlobalTheory.T
