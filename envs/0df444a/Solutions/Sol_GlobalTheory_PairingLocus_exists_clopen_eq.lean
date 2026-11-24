-- Prove2me | solution 1 for GlobalTheory.PairingLocus.exists_clopen_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:37:37.895887+00:00
-- url     : https://prove2.me/submissions/15cfb6f4-48d8-4bf8-9204-eec9fe3460a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsClopenOfIsLocallyNoetherian
import Theorems.Thm_GlobalTheory_PairingLocus_exists_idempotent
import Theorems.Thm_GlobalTheory_PairingLocus_isClosed_basicOpen
import Theorems.Thm_GlobalTheory_PairingLocus_appTop_eq_one_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PairingLocus
namespace GlobalTheory.PairingLocus
theorem _root_.solution {X : Scheme.{0}} {n : ℕ} (hn : IsUnit (n : Γ(X, ⊤))) {c c₀ : Γ(X, ⊤)ˣ}
    (hc : c ^ n = 1) (hc₀ : c₀ ^ n = 1) :
    ∃ U : X.Opens, IsClosed (U : Set X) ∧ ∀ (Y : Scheme.{0}) (h : Y ⟶ X),
      Units.map h.appTop.hom.toMonoidHom c = Units.map h.appTop.hom.toMonoidHom c₀ ↔ Set.range h ⊆ U := by
  have hu : (c * c₀⁻¹).val ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, inv_pow, hc, hc₀, inv_one, _root_.mul_one, Units.val_one]
  obtain ⟨e, he, H⟩ := exists_idempotent hn hu
  refine ⟨X.basicOpen e, isClosed_basicOpen he, fun Y h => ?_⟩
  rw [← appTop_eq_one_iff he, ← H, ← mul_inv_eq_one, ← map_inv, ← map_mul, ← Units.val_eq_one]
  rfl
end GlobalTheory.PairingLocus
