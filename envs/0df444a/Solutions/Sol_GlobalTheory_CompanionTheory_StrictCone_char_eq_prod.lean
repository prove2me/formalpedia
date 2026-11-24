-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.StrictCone.char_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:42:50.244136+00:00
-- url     : https://prove2.me/submissions/57378362-08d7-40bc-b8ad-9eb521574746

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativeCharacterOnCone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.StrictCone
namespace GlobalTheory.CompanionTheory.StrictCone
theorem _root_.solution {n : ℕ} (φ : (Fin n → ℤ) → ℂˣ) (h : ∀ g g', φ (g + g') = φ g * φ g') (x : Fin n → ℤ) :
    φ x = ∏ i, φ (Pi.single i 1) ^ x i := by
  let F : (Fin n → ℤ) →+ Additive ℂˣ :=
    AddMonoidHom.mk' (fun g => Additive.ofMul (φ g)) (fun g g' => by rw [h]; rfl)
  have hx : x = ∑ i, x i • (Pi.single i (1 : ℤ) : Fin n → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h2 : F x = ∑ i, x i • F (Pi.single i 1) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    simp only [map_zsmul]
  have h3 := congrArg Additive.toMul h2
  simpa [F, toMul_sum] using h3
end GlobalTheory.CompanionTheory.StrictCone
