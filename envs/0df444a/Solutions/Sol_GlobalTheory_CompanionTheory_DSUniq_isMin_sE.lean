-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSUniq.isMin_sE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:26:27.593145+00:00
-- url     : https://prove2.me/submissions/23f32c3f-bdc8-4b2a-81d1-29f7438ca12d

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Closure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsDerivedOnOfIsKMod
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_DSUniq_toProd_injective__e149abdd9e22
import Theorems.Thm_GlobalTheory_CompanionTheory_DSUniq_kHighest_sE_iff
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
theorem _root_.solution {lam : Fin n → ℝ} (hm : IsMin ε E lam) (hm' : IsMin ε E' lam) : IsMin ε (sE E E') lam := by
  intro μ x hx hk
  rw [kHighest_sE_iff] at hk
  by_cases h1 : (toP x).1 = 0
  · have h2 : (toP x).2 ≠ 0 := by
      intro h2
      apply hx
      apply toProd_injective₂
      rw [map_zero]
      exact Prod.ext h1 h2
    exact hm' μ _ h2 hk.2
  · exact hm μ _ h1 hk.1
end GlobalTheory.CompanionTheory.DSUniq
