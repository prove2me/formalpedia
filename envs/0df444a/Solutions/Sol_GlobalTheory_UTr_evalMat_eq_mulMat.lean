-- Prove2me | solution 1 for GlobalTheory.UTr.evalMat_eq_mulMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:58:04.264804+00:00
-- url     : https://prove2.me/submissions/63193010-092b-4cae-82df-66a34de95a26

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Theorems.Thm_GlobalTheory_UTr_eq_evalMat

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
variable {x x' : Alg P}
namespace GlobalTheory.UTr
theorem _root_.solution {g : Matrix n n B} (hg : aeval g P.1 = 0) {i : Alg P ≃ₗ[B] (n → B)} (hi : mulMat i (root P) = g)
    (z : Alg P) : evalMat P g hg z = mulMat i z := (eq_evalMat hg (mulMat i) hi z).symm
end GlobalTheory.UTr
