-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSUniq.isDerivedOn_of_isKMod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:26:25.809803+00:00
-- url     : https://prove2.me/submissions/7da29be9-dc83-424a-83b0-abe3119ce2f5

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
namespace GlobalTheory.CompanionTheory.DSUniq
theorem _root_.solution {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hK : IsKMod ε σ D E) : IsDerivedOn ε σ D E := by
  refine ⟨hK.gl, ?_, ?_⟩
  · intro k hk v hv
    obtain ⟨S, hSf, hvS, hSK⟩ := (hK.mem v).1 hv
    exact (hK.mem _).2 ⟨S, hSf, hSK k hk v hvS, hSK⟩
  · intro X hX v
    have h := hK.real X hX v
    have e : ((ReciprocityTheory.ChartRestriction.DS.actM E X v : D) : H) = ∑ a, ∑ b, X a b • ((E a b v : D) : H) := by
      simp [ReciprocityTheory.ChartRestriction.DS.actM]
    rw [e]
    exact h
end GlobalTheory.CompanionTheory.DSUniq
