-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSUniq.locFin_sE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:28:50.298821+00:00
-- url     : https://prove2.me/submissions/63e040a6-c3b0-4544-ac69-2278174f17f5

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Closure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsDerivedOnOfIsKMod
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_DSUniq_toProd_injective__e149abdd9e22
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
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {D : Submodule ℂ H} {D' : Submodule ℂ H'} {E : Fin n → Fin n → Module.End ℂ D}
  {E' : Fin n → Fin n → Module.End ℂ D'} {ε : Fin n → Bool}
namespace GlobalTheory.CompanionTheory.DSUniq
theorem _root_.solution (hF : LocFin ε E) (hF' : LocFin ε E') : LocFin ε (sE E E') := by
  intro x
  obtain ⟨S₁, hf₁, hk₁, hx₁⟩ := hF (toP x).1
  obtain ⟨S₂, hf₂, hk₂, hx₂⟩ := hF' (toP x).2
  refine ⟨(S₁.prod S₂).map ofP, ?_, ?_, ?_⟩
  · haveI : FiniteDimensional ℂ (S₁.prod S₂) := by
      first
        | infer_instance
        | (rw [← Submodule.range_subtype S₁, ← Submodule.range_subtype S₂, ← LinearMap.range_prodMap]
           infer_instance)
        | (rw [← Submodule.range_subtype S₁, ← Submodule.range_subtype S₂, ← LinearMap.range_prod_map]
           infer_instance)
    infer_instance
  · intro a b hab w hw
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hw
    refine Submodule.mem_map.2 ⟨(E a b p.1, E' a b p.2), ⟨hk₁ a b hab _ hp.1, hk₂ a b hab _ hp.2⟩, ?_⟩
    rfl
  · exact Submodule.mem_map.2 ⟨toP x, ⟨hx₁, hx₂⟩, toProd_injective₂ rfl⟩
end GlobalTheory.CompanionTheory.DSUniq
