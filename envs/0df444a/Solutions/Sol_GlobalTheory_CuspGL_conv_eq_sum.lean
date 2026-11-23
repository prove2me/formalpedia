-- Prove2me | solution 1 for GlobalTheory.CuspGL.conv_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:53.64949+00:00
-- url     : https://prove2.me/submissions/9d5e69e7-7f70-4b08-9c79-80c70156ea24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionFiniteCommAssocAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL
theorem _root_.solution (a b : F[X] → ℂ) (P : F[X]) :
    conv a b P = ∑ x ∈ (finite_monic_factorisations P).toFinset, a x.1 * b x.2 :=
  finsum_mem_eq_finite_toFinset_sum _ (finite_monic_factorisations P)
end GlobalTheory.CuspGL
