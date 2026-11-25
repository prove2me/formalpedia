-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.residueReduction_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:49:49.412294+00:00
-- url     : https://prove2.me/submissions/c4811501-265b-43d1-b1c0-9662c77353c0

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
theorem _root_.solution (u : GL (Fin n) 𝒪[F]) (i j : Fin n) :
    (residueReduction F n u : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField 𝒪[F])) i j =
      IsLocalRing.residue 𝒪[F] (u i j) :=
  rfl
end GroundTheory.Automorphic.GLnLocal
