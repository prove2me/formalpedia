-- Prove2me | solution 1 for GlobalTheory.UTr.normU_mem_plus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:35:16.041246+00:00
-- url     : https://prove2.me/submissions/e305549e-4fdb-445b-8d07-27197a357e5a

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Theorems.Thm_GlobalTheory_UTr_conj_conj

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
open Polynomial Matrix
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'}
variable {s}
variable (P : _root_.GlobalTheory.UTr.Csr s)
namespace GlobalTheory.UTr
namespace _root_.GlobalTheory.UTr
theorem _root_.solution (hs : ∀ b, s (s b) = b)
    (z : (_root_.GlobalTheory.UTr.Alg P)ˣ) :
    _root_.GlobalTheory.UTr.normU P z ∈ _root_.GlobalTheory.UTr.plus P := by
  rw [_root_.GlobalTheory.UTr.mem_plus, _root_.GlobalTheory.UTr.val_normU,
    map_mul, _root_.GlobalTheory.UTr.conj_conj P hs, mul_comm]
end _root_.GlobalTheory.UTr
end GlobalTheory.UTr
