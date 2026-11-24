-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LKDens.ev_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:42:11.657844+00:00
-- url     : https://prove2.me/submissions/6ba72726-cc15-49e3-8b74-e48af2407caa

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_RhoSurj
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LKDens
open CompanionTheory.D.LK
open CompanionTheory.D.DSIC (KStab)
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.LKDens
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (L : Submodule ℂ V) (hL : KStab ε E L)
    (r : FreeAlgebra ℂ (Fin n × Fin n)) : ∀ s : L, ev E (psi ε r) s = (rho ε E L hL r s : V) := by
  induction r using FreeAlgebra.induction with
  | grade0 c => intro s; simp [Module.algebraMap_end_apply]
  | grade1 p =>
    intro s
    by_cases h : ε p.1 = ε p.2
    · simp [psi, rho, ev, h]
    · simp [psi, rho, ev, h]
  | mul a b ha hb => intro s; simp [map_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb => intro s; simp [map_add, ha, hb]
end GlobalTheory.CompanionTheory.LKDens
