-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSUniq.orth_spread
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:43:57.644432+00:00
-- url     : https://prove2.me/submissions/867dbdc5-42ed-47be-975d-bd23c93dac32

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Closure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsDerivedOnOfIsKMod
import Theorems.Thm_GlobalTheory_CompanionTheory_DSUniq_cyc_le
import Theorems.Thm_CompanionTheory_D_LK_cyc_stab
import Theorems.Thm_CompanionTheory_D_LK_mem_cyc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (hU : IsUnitary ε E) (J : Module.End ℂ V) (hJ : ∀ a b x, J (E a b x) = E a b (J x)) {v : V}
    (hv : ∀ m ∈ Cyc E v, ⟪m, J v⟫_ℂ = 0) : ∀ x ∈ Cyc E v, ∀ m ∈ Cyc E v, ⟪m, J x⟫_ℂ = 0 := by
  let S : Submodule ℂ V :=
    { carrier := {x | ∀ m ∈ Cyc E v, ⟪m, J x⟫_ℂ = 0}
      add_mem' := fun {x y} hx hy m hm => by
        rw [map_add, inner_add_right, hx m hm, hy m hm, add_zero]
      zero_mem' := fun m _ => by rw [map_zero, inner_zero_right]
      smul_mem' := fun c x hx m hm => by rw [map_smul, inner_smul_right, hx m hm, mul_zero] }
  have hS : Cyc E v ≤ S := by
    refine cyc_le (fun c d x hx m hm => ?_) hv
    show ⟪m, J (E c d x)⟫_ℂ = 0
    have h1 := hU d c m (J x)
    rw [hJ]
    have h2 : ⟪E d c m, J x⟫_ℂ = 0 := hx _ (cyc_stab d c hm)
    rw [h2] at h1
    have hs : ((Formalism.REAL.sgn ε d c : ℝ) : ℂ) ≠ 0 := by
      unfold Formalism.REAL.sgn; split_ifs <;> norm_num
    exact (mul_eq_zero.1 h1.symm).resolve_left hs
  intro x hx m hm
  exact hS hx m hm
end GlobalTheory.CompanionTheory.DSUniq
