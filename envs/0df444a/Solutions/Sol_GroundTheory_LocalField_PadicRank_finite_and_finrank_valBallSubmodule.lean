-- Prove2me | solution 1 for GroundTheory.LocalField.PadicRank.finite_and_finrank_valBallSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:33:03.50045+00:00
-- url     : https://prove2.me/submissions/590ae543-5a41-48c4-87d6-fb7e78a510c9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogLinear
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_PrincipalUnitsRank
import Theorems.Thm_GroundTheory_LocalField_PadicRank_finite_and_finrank_integer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
open GroundTheory.LocalField.PadicRank
variable (p : ℕ) [hp : Fact p.Prime]
variable [CharP 𝓀[K] p] [CharZero K]
attribute [local instance] algebraK algebraInteger
namespace GroundTheory.LocalField.PadicRank
theorem _root_.solution (m : ℤ) :
    Module.Finite ℤ_[p] (valBallSubmodule K p m) ∧ Module.finrank ℤ_[p] (valBallSubmodule K p m) =
      (letI := (CharZero.padicHom K p).toAlgebra; Module.finrank ℚ_[p] K) := by
  obtain ⟨h1, h2⟩ := finite_and_finrank_integer (K := K) p
  have e := (valBallSubmoduleEquiv K p m).symm.trans (valBallSubmoduleZeroEquiv K p)
  exact ⟨Module.Finite.equiv e.symm, e.finrank_eq.trans h2⟩
end GroundTheory.LocalField.PadicRank
