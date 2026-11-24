-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSUniq.cas_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:26:22.6585+00:00
-- url     : https://prove2.me/submissions/033bcbca-02b7-4d67-8972-009a8287bd74

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Closure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsDerivedOnOfIsKMod
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_LK_cyc_stab
import Theorems.Thm_CompanionTheory_D_LK_mem_cyc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_inner_sum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Matrix Finset WithLp
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSUniq
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight Cas)
open PI.UpqRep (lowK IsURepOn IsIrredOn UJset IsDS)
open CompanionTheory.D.DSIC (KUnit KStab)
open CompanionTheory.D.LK (Cyc LocFin IsMin IsKMod MultAlg KModExists OrthCyc mem_cyc cyc_stab ev)
open ReciprocityTheory.ChartRestriction.DS (genSub IsDerivedOn)
open ReciprocityTheory.ChartRestriction.DS.USum (sD sE sσ ofP toP lift)
variable {n : ℕ}
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
  {ε : Fin n → Bool}
namespace GlobalTheory.CompanionTheory.DSUniq
theorem _root_.solution (hU : IsUnitary ε E) (x y : V) : ⟪Cas E x, y⟫_ℂ = ⟪x, Cas E y⟫_ℂ := by
  have hs : ∀ a b : Fin n, ((Formalism.REAL.sgn ε a b : ℝ) : ℂ) * (Formalism.REAL.sgn ε b a : ℂ) = 1 := by
    intro a b
    by_cases h : ε a = ε b
    · simp [Formalism.REAL.sgn, h]
    · have h' : ¬ ε b = ε a := fun e => h e.symm
      simp [Formalism.REAL.sgn, h, h']
  have h1 : ∀ a b, ⟪(E a b * E b a) x, y⟫_ℂ = ⟪x, (E a b * E b a) y⟫_ℂ := by
    intro a b
    rw [Module.End.mul_apply, Module.End.mul_apply, hU a b, hU b a, ← mul_assoc, hs, one_mul]
  simp only [Cas, LinearMap.sum_apply, sum_inner, inner_sum, h1]
end GlobalTheory.CompanionTheory.DSUniq
