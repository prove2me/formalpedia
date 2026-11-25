-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.modCharacter_eq_of_eqOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:28:15.18147+00:00
-- url     : https://prove2.me/submissions/dec4a615-6edc-42fc-888d-b75a99a23c4e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition

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
theorem _root_.solution {M : ℕ} [NeZero M] {σ τ : Gal(ℚ̄/ℚ)}
    (h : ∀ x ∈ rootsOfUnityField M, σ x = τ x) : modCharacter M σ = modCharacter M τ :=
  Units.ext (modCharacter_unique σ fun t ht => by
    rw [h t (subset_adjoin ℚ _ ht), modCharacter_spec τ ht])
end GroundTheory.Global.Cyclotomic
