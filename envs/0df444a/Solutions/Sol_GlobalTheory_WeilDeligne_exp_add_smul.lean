-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.exp_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:34:52.412729+00:00
-- url     : https://prove2.me/submissions/2866f5fe-0c01-43f9-9eb4-03d2da9cdc47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ToZModPowKummerEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFrobeniusSemisimplification
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNilpotentZpowSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAevalEqSmulOnEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_CharpolyEqOfIsNilpotentSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne
open IsNilpotent
variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]
namespace GlobalTheory.WeilDeligne
theorem _root_.solution {N : Matrix n n K} (hN : IsNilpotent N) (s t : K) :
    exp ((s + t) • N) = exp (s • N) * exp (t • N) := by
  rw [add_smul]
  exact exp_add_of_commute (((Commute.refl N).smul_left s).smul_right t) (hN.smul s) (hN.smul t)
end GlobalTheory.WeilDeligne
