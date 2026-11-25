-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.sigma_mem_borel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:09.428914+00:00
-- url     : https://prove2.me/submissions/8dcad474-28bf-4181-82dd-839ad6cf0efd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Theorems.Thm_GroundTheory_Automorphic_mem_borel_iff


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
theorem _root_.solution {b : GL (Fin n) F} (hb : b ∈ borel n F) : sigma b ∈ borel n F := by
  rw [mem_borel_iff] at hb ⊢
  intro i j hij
  rw [sigma_apply]
  exact hb _ _ (Fin.rev_lt_rev.2 hij)
end GroundTheory.Automorphic.Whittaker
