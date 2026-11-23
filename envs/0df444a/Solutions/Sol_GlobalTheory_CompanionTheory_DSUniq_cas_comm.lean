-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSUniq.cas_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:32.25096+00:00
-- url     : https://prove2.me/submissions/2c0e915a-bca0-43c1-844e-a6df5fec7c39

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Closure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsDerivedOnOfIsKMod
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_LK_cyc_stab
import Theorems.Thm_CompanionTheory_D_LK_mem_cyc
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
variable {V : Type} [AddCommGroup V] [Module ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
namespace GlobalTheory.CompanionTheory.DSUniq
theorem _root_.solution (ε : Fin n → Bool) (hgl : GlRel E) (a b : Fin n) (x : V) : E a b (Cas E x) = Cas E (E a b x) := by
  have key : E a b * Cas E - Cas E * E a b = 0 := by
    have h : ∀ c d, E a b * (E c d * E d c) - E c d * E d c * E a b =
        ((if b = c then E a d else 0) - (if d = a then E c b else 0)) * E d c +
        E c d * ((if b = d then E a c else 0) - (if c = a then E d b else 0)) := by
      intro c d
      rw [← hgl a b c d, ← hgl a b d c]
      noncomm_ring
    have A1 : ∑ c, ∑ d, (if b = c then E a d else 0) * E d c = ∑ d, E a d * E d b := by
      rw [Finset.sum_comm]
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have A2 : ∑ c, ∑ d, (if d = a then E c b else 0) * E d c = ∑ c, E c b * E a c := by
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have A3 : ∑ c, ∑ d, E c d * (if b = d then E a c else 0) = ∑ c, E c b * E a c := by
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have A4 : ∑ c, ∑ d, E c d * (if c = a then E d b else 0) = ∑ d, E a d * E d b := by
      rw [Finset.sum_comm]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    calc E a b * Cas E - Cas E * E a b
        = ∑ c, ∑ d, (E a b * (E c d * E d c) - E c d * E d c * E a b) := by
          simp only [Cas, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      _ = 0 := by
          simp only [h, sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, A1, A2, A3, A4]
          abel
  have := congrArg (fun T : Module.End ℂ V => T x) (sub_eq_zero.1 key)
  simpa only [Module.End.mul_apply] using this
end GlobalTheory.CompanionTheory.DSUniq
