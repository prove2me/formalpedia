-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.exp_smul_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:39:19.587857+00:00
-- url     : https://prove2.me/submissions/dc3d8848-3507-452c-ba1b-23fd45d2cce9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ToZModPowKummerEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFrobeniusSemisimplification
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNilpotentZpowSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAevalEqSmulOnEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_CharpolyEqOfIsNilpotentSub
import Theorems.Thm_GlobalTheory_WeilDeligne_semiconj_exp

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
theorem _root_.solution {N : Matrix n n K} (hN : IsNilpotent N) (s : K) :
    exp (s • N) * N = N * exp (s • N) :=
  (semiconj_exp (hN.smul s) (hN.smul s) ((Commute.refl N).smul_right s).eq).symm
end GlobalTheory.WeilDeligne
