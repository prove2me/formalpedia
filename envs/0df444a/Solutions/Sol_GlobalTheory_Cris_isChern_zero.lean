-- Prove2me | solution 1 for GlobalTheory.Cris.isChern_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:01:33.875276+00:00
-- url     : https://prove2.me/submissions/83c1a5ba-fbe9-4b39-bde0-ca1ca32f0a20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
import Theorems.Thm_GlobalTheory_Cris_dpExp_zero


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
open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.Cris
open CatCoh
variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}
variable (γ : DividedPowers I) (s : X ⟶ Sp R)
namespace GlobalTheory.Cris
theorem _root_.solution (L : LB X) (h : ∀ i j, L.g i j = 1) : IsChern γ s L 0 := by
  refine ⟨fun T ↦ T.property.choose, fun T ↦ T.property.choose_spec, fun _ _ _ ↦ 1, 0,
    fun T T' φ ↦ by rw [h, Units.val_one, map_one, map_one], fun T T' T'' φ ψ ↦ ⟨T''.obj.J.zero_mem, ?_⟩,
    by rw [map_zero, map_zero]⟩
  change dpExp T''.obj.δ 0 * 1 = _
  rw [dpExp_zero, map_one]
end GlobalTheory.Cris
