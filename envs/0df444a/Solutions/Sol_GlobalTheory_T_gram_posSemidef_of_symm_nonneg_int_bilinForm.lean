-- Prove2me | solution 1 for GlobalTheory.T.gram_posSemidef_of_symm_nonneg_int_bilinForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:23:42.310177+00:00
-- url     : https://prove2.me/submissions/391f1445-eab7-42e9-9b77-bdfaad5dc2ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GramPosSemidefOfIntForm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GramPosSemidefOfIntFormStatement
import Theorems.Thm_GlobalTheory_gram_posSemidef_of_int_form


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
theorem _root_.solution : ∀ {X : Type} [AddCommGroup X] {r : ℕ} (b : LinearMap.BilinForm ℤ X), (∀ y z, b y z = b z y) → (∀ y, 0 ≤ b y y) → ∀ v : Fin r → X, (Matrix.of fun i j => (b (v i) (v j) : ℝ)).PosSemidef := by
  first | exact @GlobalTheory.gram_posSemidef_of_int_form | exact GlobalTheory.gram_posSemidef_of_int_form | (intros; apply GlobalTheory.gram_posSemidef_of_int_form <;> assumption)
end _root_.GlobalTheory.T
