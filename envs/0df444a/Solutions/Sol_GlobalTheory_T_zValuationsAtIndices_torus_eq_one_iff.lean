-- Prove2me | solution 1 for GlobalTheory.T.zValuationsAtIndices_torus_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:48:20.775103+00:00
-- url     : https://prove2.me/submissions/cbad8b6b-5808-41b0-aba6-77b5e2c1314c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ZValuationsAtIndicesTorusEqOneIff
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValsAtApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ZValuationsAtIndicesTorusEqOneIffStatement
import Theorems.Thm_GlobalTheory_TorusKer_valsAt_torus_eq_one_iff


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
theorem _root_.solution : ∀ (G : Type) [CommGroup G] (τ : G →* G) (T : Subgroup G), (∀ t, t ∈ T ↔ t * τ t = 1) → ∀ (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ), (∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x))) → ∀ (r : ℕ) (e : Fin r → ι), (∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j)) → ∀ t : T, (valsAt w e).comp T.subtype t = 1 ↔ ∀ i, Multiplicative.toAdd (w i (t : G)) = 0 := by
  first | exact @GlobalTheory.TorusKer.valsAt_torus_eq_one_iff | exact GlobalTheory.TorusKer.valsAt_torus_eq_one_iff | (intros; apply GlobalTheory.TorusKer.valsAt_torus_eq_one_iff <;> assumption)
end _root_.GlobalTheory.T
