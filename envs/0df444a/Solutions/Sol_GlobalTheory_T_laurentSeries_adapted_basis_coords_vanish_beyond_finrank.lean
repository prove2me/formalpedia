-- Prove2me | solution 1 for GlobalTheory.T.laurentSeries_adapted_basis_coords_vanish_beyond_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:03:33.147373+00:00
-- url     : https://prove2.me/submissions/4bde87a1-d7f1-429f-b2f9-49bfbc7ed020

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LaurentSeriesAdaptedBasisCoordsVanishBeyondFinra
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LaurentSeriesAdaptedBasisCoordsVanishBeyondFinraStatement
import Theorems.Thm_GlobalTheory_adapted_coords_vanish_stmt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] (n : ℕ) (W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ), (∀ j : Fin n, (j : ℕ) < Module.finrank (LaurentSeries F) W → (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) : LaurentSeries F)) ∈ W) → ∀ y : Fin n → PowerSeries F, (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W → ∀ a : Fin n, Module.finrank (LaurentSeries F) W ≤ (a : ℕ) → (((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec y) a = 0 := by
  first | exact @GlobalTheory.adapted_coords_vanish_stmt | exact GlobalTheory.adapted_coords_vanish_stmt | (intros; apply GlobalTheory.adapted_coords_vanish_stmt <;> assumption)
end _root_.GlobalTheory.T
