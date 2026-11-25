-- Prove2me | solution 1 for GlobalTheory.UniformSerre.isHomogeneous_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:20:10.016544+00:00
-- url     : https://prove2.me/submissions/00fa1771-3597-4196-8c7f-dbe6789d5023

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomogeneousIdealOverReesAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormOfCompatibleFractionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformSerreSections
import Theorems.Thm_GlobalTheory_UniformSerre_liftFun_zero
import Theorems.Thm_GlobalTheory_UniformSerre_coeff_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.UniformSerre
variable {R : Type} [CommRing R] {I : Ideal R} {σ : Type}
namespace GlobalTheory.UniformSerre
theorem _root_.solution {e t : ℕ} {P : MvPolynomial σ R} (hP : P.IsHomogeneous t) :
    (lift I e P).IsHomogeneous t :=
  fun d hd => hP (fun h0 => hd (by rw [coeff_lift, h0, liftFun_zero]))
end GlobalTheory.UniformSerre
