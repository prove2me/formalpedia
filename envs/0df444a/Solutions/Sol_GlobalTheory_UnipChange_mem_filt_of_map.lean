-- Prove2me | solution 1 for GlobalTheory.UnipChange.mem_filt_of_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:49:49.185805+00:00
-- url     : https://prove2.me/submissions/ace62eae-b331-4e7c-b911-3554e3ce1092

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitriangularMapInduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped Pointwise
open GlobalTheory GlobalTheory.UnipChange
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointRadical
variable {k : Type} [Field k] {r : ℕ} {b : Fin r → ℕ}
namespace GlobalTheory.UnipChange
theorem _root_.solution (L : lieRadical k b ≃ₗ[k] lieRadical k b)
    (hL : ∀ t (X : lieRadical k b), X.1 ∈ filt k b t → (L X).1 ∈ filt k b t)
    (t : ℕ) (X : lieRadical k b) (hX : (L X).1 ∈ filt k b t) : X.1 ∈ filt k b t := by
  set U := (filt k b t).comap (lieRadical k b).subtype with hU
  have h1 : U.map (L : lieRadical k b →ₗ[k] lieRadical k b) = U := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨Y, hY, rfl⟩
      exact hL t Y hY
    · exact LinearEquiv.finrank_map_eq L U
  have h2 : L X ∈ U := hX
  rw [← h1] at h2
  obtain ⟨Y, hY, e⟩ := h2
  have : Y = X := L.injective e
  exact this ▸ hY
end GlobalTheory.UnipChange
