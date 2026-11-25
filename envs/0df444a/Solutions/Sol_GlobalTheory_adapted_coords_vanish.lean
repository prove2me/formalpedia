-- Prove2me | solution 1 for GlobalTheory.adapted_coords_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:17:48.989543+00:00
-- url     : https://prove2.me/submissions/e4edc0ff-ddc7-44b8-8481-70c95ee4875f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LaurentSeriesAdaptedBasisCoordsVanishBeyondFinra
import Theorems.Thm_GlobalTheory_inv_mulVec_coord_eq_zero_of_adapted_columns_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (F : Type) [Field F] (n : ℕ)
    (W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F))
    (g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ)
    (hg : ∀ j : Fin n, (j : ℕ) < Module.finrank (LaurentSeries F) W →
      (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) : LaurentSeries F)) ∈ W)
    (y : Fin n → PowerSeries F) (hy : (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W)
    (a : Fin n) (ha : Module.finrank (LaurentSeries F) W ≤ (a : ℕ)) :
    (((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec y) a = 0 :=
  inv_mulVec_coord_eq_zero_of_adapted_columns_injective (HahnSeries.ofPowerSeries ℤ F) HahnSeries.ofPowerSeries_injective n W g hg y hy a ha
end GlobalTheory
