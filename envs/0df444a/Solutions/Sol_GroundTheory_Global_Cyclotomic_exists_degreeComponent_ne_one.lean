-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.exists_degreeComponent_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:37:31.459999+00:00
-- url     : https://prove2.me/submissions/229fd5e0-f268-4e2f-b13c-15cc9f2eac38

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition
import Theorems.Thm_GroundTheory_Global_Cyclotomic_redUnits_character
import Theorems.Thm_GroundTheory_Global_Cyclotomic_degreeComponent_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Filter Topology
open scoped GroundTheory.LocalField.Abstract Pointwise
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (q : Nat.Primes) (w : ℤ_[q]ˣ)
    (hw : padicUnitsLog q w ≠ 1) :
    ∃ N, 0 < N ∧ ∀ σ : Gal(ℚ̄/ℚ), (modCharacter ((q : ℕ) ^ N) σ : ZMod ((q : ℕ) ^ N)) =
      PadicInt.toZModPow N (w : ℤ_[q]) → degreeComponent q σ ≠ 1 := by
  obtain ⟨n, hn⟩ : ∃ n, PadicInt.toZModPow n (Multiplicative.toAdd (padicUnitsLog q w)) ≠ 0 := by
    by_contra! hcon
    apply hw
    have h0 : Multiplicative.toAdd (padicUnitsLog q w) = 0 :=
      PadicInt.ext_of_toZModPow.mp fun n => by rw [hcon n, map_zero]
    rw [← ofAdd_toAdd (padicUnitsLog q w), h0, ofAdd_zero]
  refine ⟨n + unitsLevel q, by have := unitsLevel_ne_zero q; omega, fun σ hσ h1 => hn ?_⟩
  have hred : redUnits q (n + unitsLevel q) (Units.map (toPadicInt q).toMonoidHom (character σ)) =
      redUnits q (n + unitsLevel q) w :=
    Units.ext (by rw [redUnits_character, hσ, coe_redUnits])
  rw [toZModPow_padicUnitsLog, ← hred, ← toZModPow_padicUnitsLog, ← degreeComponent_apply, h1,
    toAdd_one, map_zero]
end GroundTheory.Global.Cyclotomic
