-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QuadraticUnit.isUnit_add_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:14:07.424699+00:00
-- url     : https://prove2.me/submissions/7e2df901-a7dd-4c4d-92d4-8b21cd7f98ca

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuadraticOrderPrincipal
import Theorems.Thm_GlobalTheory_CompanionTheory_QuadraticUnit_norm_isUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QuadraticUnit
open Polynomial IsLocalRing
namespace GlobalTheory.CompanionTheory.QuadraticUnit
theorem _root_.solution {R O : Type} [CommRing R] [HenselianLocalRing R] [CommRing O]
    (ι : R →+* O) (δ : O) (D : R) (hδ : δ * δ = ι D) (hD : IsUnit D)
    (h2 : IsUnit (2 : R)) (hns : ¬ ∃ e : R, D = e * e) (a b : R)
    (hab : IsUnit a ∨ IsUnit b) : IsUnit (ι a + ι b * δ) := by
  have hn := (norm_isUnit D hD h2 hns a b hab).map ι
  have he : (ι a + ι b * δ) * (ι a - ι b * δ) = ι (a * a - D * (b * b)) := by
    rw [map_sub, map_mul, map_mul, map_mul, ← hδ]
    ring
  rw [← he] at hn
  exact isUnit_of_mul_isUnit_left hn
end GlobalTheory.CompanionTheory.QuadraticUnit
