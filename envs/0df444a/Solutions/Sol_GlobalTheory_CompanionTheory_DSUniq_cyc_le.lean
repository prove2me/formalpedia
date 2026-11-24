-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSUniq.cyc_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:26:23.95044+00:00
-- url     : https://prove2.me/submissions/0c454f2c-0928-48f1-93a7-357bf3e51cde

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
theorem _root_.solution {v : V} {T : Submodule ℂ V} (hT : ∀ a b, ∀ x ∈ T, E a b x ∈ T) (hv : v ∈ T) : Cyc E v ≤ T := by
  intro w hw
  obtain ⟨a, rfl⟩ := mem_cyc.1 hw
  clear hw
  suffices h : ∀ x ∈ T, ev E a x ∈ T from h v hv
  induction a using FreeAlgebra.induction
  next r =>
    intro x hx
    rw [AlgHom.commutes, Module.algebraMap_end_apply]
    exact T.smul_mem r hx
  next p =>
    intro x hx
    simp only [ev, FreeAlgebra.lift_ι_apply]
    exact hT p.1 p.2 x hx
  next a b ha hb =>
    intro x hx
    rw [map_mul, Module.End.mul_apply]
    exact ha _ (hb x hx)
  next a b ha hb =>
    intro x hx
    rw [map_add, LinearMap.add_apply]
    exact T.add_mem (ha x hx) (hb x hx)
end GlobalTheory.CompanionTheory.DSUniq
