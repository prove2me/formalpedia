-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.isOpen_iwahori
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:10:41.331797+00:00
-- url     : https://prove2.me/submissions/7f0047a5-7a3e-4735-ba9b-5adadf05bea0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_congruenceSubgroup_one_le_iwahori

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
theorem _root_.solution : IsOpen (iwahori F n : Set (GL (Fin n) F)) :=
  Subgroup.isOpen_mono (congruenceSubgroup_one_le_iwahori F n) (isOpen_congruenceSubgroup F n 1)
end GroundTheory.Automorphic.GLnLocal
