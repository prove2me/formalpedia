-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.rootElt_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:34.405782+00:00
-- url     : https://prove2.me/submissions/e0c26a7d-031d-4750-b9b3-ae387a7b1d75

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable (ψ₀ : AddChar F ℂ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {i j : Fin n} (h : i ≠ j) (a : F) (r c : Fin n) :
    ((rootElt i j a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) r c =
      (1 : Matrix (Fin n) (Fin n) F) r c + if i = r ∧ j = c then a else 0 := by
  rw [coe_rootElt h, Matrix.add_apply, Matrix.single_apply]
end GroundTheory.Automorphic.Whittaker
