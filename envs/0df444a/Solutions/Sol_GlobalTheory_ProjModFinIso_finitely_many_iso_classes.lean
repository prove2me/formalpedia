-- Prove2me | solution 1 for GlobalTheory.ProjModFinIso.finitely_many_iso_classes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:27:17.515947+00:00
-- url     : https://prove2.me/submissions/03ff4898-2f8a-4a49-b9dd-ea91e6bd97dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FinitelyManyIsoClassesProjectiveNumberField
import Theorems.Thm_GlobalTheory_ProjModFinIso_exists_finite_reps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.ProjModFinIso
variable {R : Type} [CommRing R] [IsDedekindDomain R]
namespace GlobalTheory.ProjModFinIso
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (q : ℕ),
    ∃ (n : ℕ) (Y : Fin n → ModuleCat.{0} (𝓞 E)), ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
      [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
      ∃ k, Nonempty (X ≃ₗ[𝓞 E] Y k) := by
  intro E _ _ q
  exact exists_finite_reps q
end GlobalTheory.ProjModFinIso
