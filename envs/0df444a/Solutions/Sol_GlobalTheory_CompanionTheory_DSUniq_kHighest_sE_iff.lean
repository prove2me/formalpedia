-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSUniq.kHighest_sE_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:32.966011+00:00
-- url     : https://prove2.me/submissions/f8246159-d10f-4cf9-9cc4-503c1dc1750f

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Closure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsDerivedOnOfIsKMod
import Theorems.Thm_GlobalTheory_CompanionTheory_DSUniq_toProd_prodMap
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_DSUniq_toProd_injective__e149abdd9e22
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
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {D : Submodule ℂ H} {D' : Submodule ℂ H'} {E : Fin n → Fin n → Module.End ℂ D}
  {E' : Fin n → Fin n → Module.End ℂ D'} {ε : Fin n → Bool}
namespace GlobalTheory.CompanionTheory.DSUniq
theorem _root_.solution {μ : Fin n → ℝ} {x : sD D D'} :
    KHighest ε (sE E E') μ x ↔ KHighest ε E μ (toP x).1 ∧ KHighest ε E' μ (toP x).2 := by
  have key : ∀ (x y : sD D D'), x = y ↔ (toP x).1 = (toP y).1 ∧ (toP x).2 = (toP y).2 := fun x y =>
    ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => toProd_injective₂ (Prod.ext h.1 h.2)⟩
  unfold Formalism.REAL.KHighest Formalism.REAL.IsWeight
  simp only [key, toProd_prodMap, map_smul, map_zero, Prod.smul_fst, Prod.smul_snd, Prod.fst_zero, Prod.snd_zero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun a => (h1 a).1, fun a b hab he => (h2 a b hab he).1⟩,
      ⟨fun a => (h1 a).2, fun a b hab he => (h2 a b hab he).2⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h1', h2'⟩⟩
    exact ⟨fun a => ⟨h1 a, h1' a⟩, fun a b hab he => ⟨h2 a b hab he, h2' a b hab he⟩⟩
end GlobalTheory.CompanionTheory.DSUniq
