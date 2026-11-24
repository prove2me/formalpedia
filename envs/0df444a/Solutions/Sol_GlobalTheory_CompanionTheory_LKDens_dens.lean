-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LKDens.dens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:16:32.546956+00:00
-- url     : https://prove2.me/submissions/c6cc500b-b3eb-43e1-95d2-eb87492733d1

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_RhoSurj
import Theorems.Thm_GlobalTheory_CompanionTheory_LKDens_ev_psi
import Theorems.Thm_GlobalTheory_CompanionTheory_LKDens_rho_surj
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
theorem _root_.solution : CompanionTheory.D.LK.Dens := by
  intro n ε V _ _ E μ v L _ _ hv hvL _ hfd hL hirr _
  have hs := rho_surj ε E L hL hv hvL hirr
  let b := Module.finBasis ℂ L
  constructor
  · intro x hx
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ
      (show (⟨v, hvL⟩ : L) ≠ 0 from fun h => hv (congrArg Subtype.val h))
    obtain ⟨r, hr⟩ := hs (f.smulRight (⟨x, hx⟩ : L))
    refine ⟨psi ε r, ?_⟩
    have := ev_psi ε E L hL r ⟨v, hvL⟩
    rw [hr] at this
    simpa [hf] using this
  · intro φ hφ
    choose u hu using fun i => hφ (b i)
    choose r hr using fun i => hs ((b.coord i).smulRight (⟨v, hvL⟩ : L))
    refine ⟨∑ i, u i * psi ε (r i), fun s => ?_⟩
    have hu' : ∀ i, ev E (u i) v = φ (b i) := fun i => by simpa using hu i
    conv_rhs => rw [← b.sum_repr s]
    simp only [map_sum, map_mul, LinearMap.sum_apply, Module.End.mul_apply, ev_psi ε E L hL, hr, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hu']
end GlobalTheory.CompanionTheory.LKDens
