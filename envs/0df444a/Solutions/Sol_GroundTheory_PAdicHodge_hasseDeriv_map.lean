-- Prove2me | solution 1 for GroundTheory.PAdicHodge.hasseDeriv_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:19.461775+00:00
-- url     : https://prove2.me/submissions/24ff6af8-d5b7-4f89-b1f2-c6be71fefc9b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace GroundTheory.PAdicHodge
theorem _root_.solution {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (q : ℕ)
    (P : R[X]) : hasseDeriv q (P.map f) = (hasseDeriv q P).map f := by
  ext n
  rw [hasseDeriv_coeff, coeff_map, coeff_map, hasseDeriv_coeff, map_mul, map_natCast]
end GroundTheory.PAdicHodge
