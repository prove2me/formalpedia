-- Prove2me | solution 1 for GlobalTheory.UTr.aeval_mulMat_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:43:32.845507+00:00
-- url     : https://prove2.me/submissions/0a15b471-8bda-4a6f-bfb4-00f5ef34ed67

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.UTr
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'}
variable {s}
variable (P : Csr s)
variable {n : Type} [Fintype n] [DecidableEq n]
variable {J : Matrix n n B}
variable {P}
namespace GlobalTheory.UTr
theorem _root_.solution (i : Alg P ≃ₗ[B] (n → B)) : aeval (mulMat i (root P)) P.1 = 0 := by
  rw [aeval_algHom_apply, aeval_root, map_zero]
end GlobalTheory.UTr
