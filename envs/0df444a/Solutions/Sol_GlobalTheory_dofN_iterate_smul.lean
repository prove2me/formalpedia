-- Prove2me | solution 1 for GlobalTheory.dofN_iterate_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:45:44.01385+00:00
-- url     : https://prove2.me/submissions/faf93ce5-1c91-4fab-8fa0-c38318ce2afd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NablaValueCopiesBilinear
import Theorems.Thm_GlobalTheory_dofN_smul
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory
variable {R : Type} [CommRing R] {d n : ℕ}
namespace GlobalTheory
theorem _root_.solution (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (k : ℕ)
    (t : R) (f : PS R n d) :
    (DofN F b u)^[k] (t • f) = t • (DofN F b u)^[k] f := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, dofN_smul]
end GlobalTheory
