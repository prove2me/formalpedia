-- Prove2me | solution 1 for GroundTheory.Global.isFiniteSplit_pi_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:06:41.164993+00:00
-- url     : https://prove2.me/submissions/a102e764-8d43-48f3-9f07-096289c7e6c5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Theorems.Thm_GroundTheory_Global_finrank_eq_one_of_surjective_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField Module
open scoped TensorProduct
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
namespace GroundTheory.Global
theorem _root_.solution {ι : Type*} [Finite ι] {E : ι → Type*} [∀ i, Field (E i)]
    [∀ i, Algebra F (E i)] :
    Algebra.IsFiniteSplit F (∀ i, E i) ↔ ∀ i, finrank F (E i) = 1 := by
  constructor
  · intro h i
    obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun F (∀ i, E i)
    refine finrank_eq_one_of_surjective_pi ((Pi.evalAlgHom F E i).comp e.symm.toAlgHom) ?_
    exact (Function.surjective_eval i).comp e.symm.surjective
  · intro h
    exact .of_algEquiv (AlgEquiv.piCongrRight fun i ↦ algEquivOfFinrankEqOne (h i))
end GroundTheory.Global
