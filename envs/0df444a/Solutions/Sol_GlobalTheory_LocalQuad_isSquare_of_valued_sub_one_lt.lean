-- Prove2me | solution 1 for GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:08:33.588072+00:00
-- url     : https://prove2.me/submissions/8c1f51d3-accf-4b30-a199-e0241e5a738f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Theorems.Thm_GlobalTheory_LocalQuad_SquareTheorem_isSquare_of_norm_sub_one_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
open NumberField IsDedekindDomain
open scoped Matrix WithZero
namespace GlobalTheory.LocalQuad
namespace _root_.GlobalTheory.LocalQuad
theorem _root_.solution (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (h : Valued.v (x - 1) < Valued.v (4 : v.adicCompletion F)) : IsSquare x :=
  _root_.GlobalTheory.LocalQuad.SquareTheorem.isSquare_of_norm_sub_one_lt x (Valued.toNormedField.norm_lt_iff.2 h)
end _root_.GlobalTheory.LocalQuad
end GlobalTheory.LocalQuad
