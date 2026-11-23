-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.residue_ne_zero_iff_valuation_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:59.057302+00:00
-- url     : https://prove2.me/submissions/7e490b3c-a8b5-419f-ba6e-2ea0f0b1f5b0

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
    IsLocalRing.residue 𝒪[F] x ≠ 0 ↔ valuation F (x : F) = 1 := by
  rw [IsLocalRing.residue_ne_zero_iff_isUnit,
    (Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one]
  exact Iff.rfl
end GroundTheory.Automorphic.GLnLocal
