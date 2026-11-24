-- Prove2me | solution 1 for GlobalTheory.Proof.ColumnMapShift.rowShift_X_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:38:42.250934+00:00
-- url     : https://prove2.me/submissions/a24f0c37-185c-4fc3-bd93-31abc0a6dacb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_UnitaryDetClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ColumnMapShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.ColumnMapShift
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
namespace GlobalTheory.Proof.ColumnMapShift
theorem _root_.solution (σ : T) (i i' : Fin (r σ)) (t : k) (τ : T) (j : Fin (r τ))
    (h : (⟨τ, j⟩ : Σ s, Fin (r s)) ≠ ⟨σ, i⟩) (b : Fin n) :
    rowShift r n k σ i i' t (X ⟨τ, j, b⟩) = X ⟨τ, j, b⟩ := by
  rw [rowShift, aeval_X, if_neg]
  rintro ⟨b', hb⟩
  apply h
  exact congrArg (fun ℓ : Letter T r n => (⟨ℓ.1, ℓ.2.1⟩ : Σ s, Fin (r s))) hb
end GlobalTheory.Proof.ColumnMapShift
