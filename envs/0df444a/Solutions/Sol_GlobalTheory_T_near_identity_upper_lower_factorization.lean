-- Prove2me | solution 1 for GlobalTheory.T.near_identity_upper_lower_factorization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:19:36.028538+00:00
-- url     : https://prove2.me/submissions/2d80157c-d975-422d-83a8-fba577535edc

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_NearIdentityUpperLowerFactorization
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_NearIdentityUpperLowerFactorizationStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_IwahoriLU_iwahori_factorisation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ), 0 ≤ r → r < 1 → ∀ A : Matrix (Fin n) (Fin n) L, (∀ i j, ‖(A - 1) i j‖ ≤ r) → ∃ U W : Matrix (Fin n) (Fin n) L, (∀ i j, j < i → U i j = 0) ∧ (∀ i j, i < j → W i j = 0) ∧ (∀ i j, ‖(U - 1) i j‖ ≤ r) ∧ (∀ i j, ‖(W - 1) i j‖ ≤ r) ∧ A = U * W := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.IwahoriLU.iwahori_factorisation | exact GlobalTheory.CompanionTheory.CartGL.IwahoriLU.iwahori_factorisation | (intros; apply GlobalTheory.CompanionTheory.CartGL.IwahoriLU.iwahori_factorisation <;> assumption)
end _root_.GlobalTheory.T
