-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LKWtProj.Ft_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:42:14.580102+00:00
-- url     : https://prove2.me/submissions/7b5bdca2-f41e-4ea2-8dbf-a82fa024369a

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_WtProj
import Theorems.Thm_GlobalTheory_CompanionTheory_LKWtProj_Ft_apply
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
open Finset
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LKWtProj
open CompanionTheory.D.LK
open CompanionTheory.D.DSIC (KRel KUnit KStab)
namespace GlobalTheory.CompanionTheory.LKWtProj
theorem _root_.solution {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ε₀ ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (hE : KRel ε E) (c d : Fin n) : Commute (Ft ε₀ E c) (Ft ε₀ E d) := by
  have h : E c c * E d d = E d d * E c c := by
    have := hE c c d d rfl rfl
    by_cases hcd : c = d
    · subst hcd; rfl
    · rw [if_neg hcd, if_neg (Ne.symm hcd), sub_zero, sub_eq_zero] at this
      exact this
  refine LinearMap.ext fun x => funext fun A => ?_
  have h' : E c c (E d d (x A)) = E d d (E c c (x A)) := LinearMap.congr_fun h (x A)
  simp only [Module.End.mul_apply, Ft_apply, map_add, map_smul, h', smul_add, smul_smul,
    mul_comm (wt (A.filter (cpt ε₀)) c : ℂ)]
  abel
end GlobalTheory.CompanionTheory.LKWtProj
