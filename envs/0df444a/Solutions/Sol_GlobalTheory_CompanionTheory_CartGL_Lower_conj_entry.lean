-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.Lower.conj_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:21:41.879708+00:00
-- url     : https://prove2.me/submissions/762d8dc1-31f9-455a-9fa5-c6eb7b4ee9c0

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DominantConjugationPreservesLowerCongruence
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_dPow_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL GlobalTheory.CompanionTheory.CartGL.Lower
namespace GlobalTheory.CompanionTheory.CartGL.Lower
theorem _root_.solution {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}
    (p : Lˣ) (a : Fin n → ℤ) (w : GL (Fin n) L) (i j : Fin n) :
    (((GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ * w * GlobalTheory.CompanionTheory.CartGL.dPow p a : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L) i j =
      ((p ^ (-a i) : Lˣ) : L) * (w : Matrix (Fin n) (Fin n) L) i j * ((p ^ a j : Lˣ) : L) := by
  have h : (((GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      diagonal fun i => ((p ^ (-a i) : Lˣ) : L) := rfl
  rw [Units.val_mul, Units.val_mul, h, GlobalTheory.CompanionTheory.CartGL.dPow_val, mul_diagonal, diagonal_mul]
end GlobalTheory.CompanionTheory.CartGL.Lower
