-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.sigma_diagGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:46:32.301892+00:00
-- url     : https://prove2.me/submissions/e2981261-4d23-4aa1-a5e6-38083861413e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable (ψ₀ : AddChar F ℂ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (t : Fin n → Fˣ) :
    sigma (Iwasawa.diagGL F n t) = Iwasawa.diagGL F n (t ∘ Fin.rev) := by
  refine Units.ext ?_
  ext i j
  simp only [sigma_apply, Iwasawa.coe_diagGL, Matrix.diagonal_apply, Fin.rev_inj,
    Function.comp_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg (Ne.symm h), if_neg h]
end GroundTheory.Automorphic.Whittaker
