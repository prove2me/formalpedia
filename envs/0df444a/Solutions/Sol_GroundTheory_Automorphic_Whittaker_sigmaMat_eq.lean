-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.sigmaMat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:07.795787+00:00
-- url     : https://prove2.me/submissions/f88de438-9048-4bfc-a3cd-2f5395fefb57

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Theorems.Thm_GroundTheory_Automorphic_mul_permGL_apply
import Theorems.Thm_GroundTheory_Automorphic_permGL_mul_apply


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
theorem _root_.solution (M : Matrix (Fin n) (Fin n) F) :
    sigmaMat M = ((permGL F (Fin.revPerm (n := n)) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Mᵀ *
      ((permGL F (Fin.revPerm (n := n)) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  ext i j
  rw [mul_permGL_apply, permGL_mul_apply, Matrix.transpose_apply, sigmaMat_apply]
  congr 1
end GroundTheory.Automorphic.Whittaker
