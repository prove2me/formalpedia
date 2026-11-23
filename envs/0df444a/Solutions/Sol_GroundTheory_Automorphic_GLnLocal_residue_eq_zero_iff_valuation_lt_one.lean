-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.residue_eq_zero_iff_valuation_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:38.16102+00:00
-- url     : https://prove2.me/submissions/f173b346-db8c-4035-a276-01463325f376

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset ValuativeRel
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution (x : 𝒪[F]) :
    IsLocalRing.residue 𝒪[F] x = 0 ↔ valuation F (x : F) < 1 := by
  rw [← not_iff_not, ← ne_eq, IsLocalRing.residue_ne_zero_iff_isUnit,
    (Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one, not_lt]
  exact ⟨fun h => h.ge, fun h => le_antisymm ((Valuation.mem_integer_iff _ _).mp x.2) h⟩
end GroundTheory.Automorphic.GLnLocal
