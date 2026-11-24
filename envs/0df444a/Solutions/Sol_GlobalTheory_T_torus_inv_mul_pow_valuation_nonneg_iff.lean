-- Prove2me | solution 1 for GlobalTheory.T.torus_inv_mul_pow_valuation_nonneg_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:46:09.213533+00:00
-- url     : https://prove2.me/submissions/a9882cd7-bc1a-4289-8840-fa9b6245b52a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusInvMulPowValuationNonnegIff
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValsAtApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusInvMulPowValuationNonnegIffStatement
import Theorems.Thm_GlobalTheory_TorusInteg_torus_integral_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [CommGroup G] (τ : G →* G) (T : Subgroup G), (∀ t, t ∈ T ↔ t * τ t = 1) → ∀ (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ), (∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x))) → ∀ (r : ℕ) (e : Fin r → ι), (∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j)) → ∀ α : G, τ α = α → (∀ i, 0 < Multiplicative.toAdd (w i α)) → ∀ (t : T) (k : ℕ), (∀ i, 0 ≤ Multiplicative.toAdd (w i ((t : G)⁻¹ * α ^ k))) ↔ ∀ j, |Multiplicative.toAdd ((valsAt w e).comp T.subtype t) j| ≤ ((k * (Multiplicative.toAdd (w (e j) α)).toNat : ℕ) : ℤ) := by
  first | exact @GlobalTheory.TorusInteg.torus_integral_iff | exact GlobalTheory.TorusInteg.torus_integral_iff | (intros; apply GlobalTheory.TorusInteg.torus_integral_iff <;> assumption)
end _root_.GlobalTheory.T
