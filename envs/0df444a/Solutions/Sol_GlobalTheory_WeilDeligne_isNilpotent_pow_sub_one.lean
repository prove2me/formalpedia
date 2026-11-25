-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.isNilpotent_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:29:26.504792+00:00
-- url     : https://prove2.me/submissions/183bfe0b-9ee1-4c33-bd3f-b9c70fc45386

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPowEqPowOfWeilDegreeEqSmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_WeilGroupIsSemisimpleOfSemisimpleFrobStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFrobeniusSemisimplification

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne
namespace GlobalTheory.WeilDeligne
theorem _root_.solution {R : Type*} [Ring R] {u : R} (hu : IsNilpotent (u - 1)) (k : ℕ) :
    IsNilpotent (u ^ k - 1) := by
  rw [← mul_geom_sum]
  refine Commute.isNilpotent_mul_right ?_ hu
  exact Commute.sum_right _ _ _ fun i _ =>
    ((Commute.refl u).pow_right i).sub_left (Commute.one_left _)
end GlobalTheory.WeilDeligne
