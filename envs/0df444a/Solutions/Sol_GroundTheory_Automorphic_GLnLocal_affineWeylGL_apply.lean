-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.affineWeylGL_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:46.25567+00:00
-- url     : https://prove2.me/submissions/88c4a205-e6f8-4bc0-8d34-ebbdad928e8a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_permGL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset ValuativeRel
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution (w : ExtendedAffineWeyl n) (i j : Fin n) :
    (affineWeylGL F n w : Matrix (Fin n) (Fin n) F) i j =
      if i = w.right j then ϖ ^ (w.left i).toAdd else 0 := by
  show ((diagPow F n w.left * permGL F w.right : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = _
  rw [Units.val_mul, diagPow_val, diagonal_mul, permGL_apply]
  split_ifs <;> simp
end GroundTheory.Automorphic.GLnLocal
