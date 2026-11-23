-- Prove2me | solution 1 for GlobalTheory.CuspGL.mangoldtConv_eq_of_dvd_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:15.337478+00:00
-- url     : https://prove2.me/submissions/6a40fc0d-1268-41c7-953b-57ee657fc742

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveEqPolynomialVonMangoldtConvolutionOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL
theorem _root_.solution {f g : F[X]} (hf : f.Monic) (hf' : Irreducible f) (hg : g.Monic)
    (hg' : Irreducible g) {n : ℕ} (h : g ∣ f ^ n) : g = f :=
  eq_of_monic_of_associated hg hf (hg'.associated_of_dvd hf' (hg'.prime.dvd_of_dvd_pow h))
end GlobalTheory.CuspGL
