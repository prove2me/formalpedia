-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.doubleCoset_affineWeylGL_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:23:29.23179+00:00
-- url     : https://prove2.me/submissions/06010cdb-3dbf-441e-ab6c-38a3c88d8fe4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_eq_of_affineWeylGL_mem_doubleCoset

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
theorem _root_.solution {w w' : ExtendedAffineWeyl n} {g : GL (Fin n) F}
    (hw : g ∈ doubleCoset (affineWeylGL F n w) (iwahori F n) (iwahori F n))
    (hw' : g ∈ doubleCoset (affineWeylGL F n w') (iwahori F n) (iwahori F n)) : w = w' := by
  have e : doubleCoset (affineWeylGL F n w) (iwahori F n) (iwahori F n) =
      doubleCoset (affineWeylGL F n w') (iwahori F n) (iwahori F n) :=
    (doubleCoset_eq_of_mem hw).symm.trans (doubleCoset_eq_of_mem hw')
  have hmem := mem_doubleCoset_self (iwahori F n) (iwahori F n) (affineWeylGL F n w')
  rw [← e] at hmem
  exact eq_of_affineWeylGL_mem_doubleCoset F n hmem
end GroundTheory.Automorphic.GLnLocal
