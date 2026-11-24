-- Prove2me | solution 1 for GlobalTheory.UTr.eq_evalMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:43:33.743604+00:00
-- url     : https://prove2.me/submissions/0af82dac-3949-4973-b7c2-c30da9e831f1

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
variable {P}
namespace GlobalTheory.UTr
theorem _root_.solution {g : Matrix n n B} (hg : aeval g P.1 = 0) (f : Alg P →ₐ[B] Matrix n n B) (hf : f (root P) = g)
    (z : Alg P) : f z = evalMat P g hg z :=
  RingHom.congr_fun (Alg.ringHom_ext (f := f.toRingHom) (g := (evalMat P g hg).toRingHom)
    (fun b => (f.commutes b).trans ((evalMat P g hg).commutes b).symm) (hf.trans (evalMat_root P g hg).symm)) z
end GlobalTheory.UTr
