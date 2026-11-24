-- Prove2me | solution 1 for GlobalTheory.DI.PhiLead.gamma_iMulti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:09:31.653027+00:00
-- url     : https://prove2.me/submissions/4fd4a8a6-faa0-45c0-aebc-0885b56114dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechAntisymmetrizedCupProductLeadingTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI GlobalTheory.DI.PhiLead
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]
namespace GlobalTheory.DI.PhiLead
theorem _root_.solution (p : ℕ) (g : V →+ V) (γ : ExteriorAlgebra K V →+* ExteriorAlgebra K V)
    (hγ : IsGamma p g γ) (a : ℕ) (v : Fin a → V) :
    γ (ExteriorAlgebra.ιMulti K a v) = ExteriorAlgebra.ιMulti K a (fun k => g (v k)) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 1
  exact List.ofFn_inj.mpr (funext fun k => hγ.2 (v k))
end GlobalTheory.DI.PhiLead
