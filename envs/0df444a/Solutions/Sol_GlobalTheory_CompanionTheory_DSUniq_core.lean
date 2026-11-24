-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSUniq.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:10:37.89151+00:00
-- url     : https://prove2.me/submissions/66c1404e-6769-4af9-bc31-1b733688d048

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Closure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsDerivedOnOfIsKMod
import Theorems.Thm_GlobalTheory_CompanionTheory_DSUniq_self_mem_cyc
import Theorems.Thm_GlobalTheory_CompanionTheory_DSUniq_cas_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_DSUniq_orth_spread
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
theorem _root_.solution (hM : MultAlg) (hO : OrthCyc) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {E : Fin n → Fin n → Module.End ℂ V} {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : StrictAnti lam) (hgl : GlRel E)
    (hun : IsUnitary ε E) (hF : LocFin ε E) (hm : IsMin ε E lam) {y : V} (hy0 : y ≠ 0)
    (hyK : KHighest ε E (lowK ε lam) y) (J : Module.End ℂ V) (hJ : ∀ a b x, J (E a b x) = E a b (J x))
    (hy : ⟪y, J y⟫_ℂ = 0) : (∃ c : ℂ, Cas E y = c • y) ∧ ∀ x ∈ Cyc E y, ⟪x, J x⟫_ℂ = 0 := by
  have hKU : KUnit ε E := fun a b hab x y => by simp [hun a b, Formalism.REAL.sgn, hab]
  have hmult : ∀ w ∈ Cyc E y, KHighest ε E (lowK ε lam) w → ∃ c, w = c • y :=
    fun w hw hwK => hM n ε lam V E hlam hgl hKU hF hm y w hy0 hyK hwK hw
  have hyK' := hyK
  unfold Formalism.REAL.KHighest Formalism.REAL.IsWeight at hyK'
  have hCas : KHighest ε E (lowK ε lam) (Cas E y) := by
    unfold Formalism.REAL.KHighest Formalism.REAL.IsWeight
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · rw [cas_comm ε hgl, hyK'.1 a, map_smul]
    · rw [cas_comm ε hgl, hyK'.2 a b hab he, map_zero]
  have hCasMem : Cas E y ∈ Cyc E y := by
    simp only [Cas, LinearMap.sum_apply, Module.End.mul_apply]
    exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
      cyc_stab a b (cyc_stab b a (self_mem_cyc y))
  refine ⟨hmult _ hCasMem hCas, ?_⟩
  have hJK : KHighest ε E (lowK ε lam) (J y) := by
    unfold Formalism.REAL.KHighest Formalism.REAL.IsWeight
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · rw [← hJ, hyK'.1 a, map_smul]
    · rw [← hJ, hyK'.2 a b hab he, map_zero]
  have horth := hO n ε V E (lowK ε lam) y (J y) hgl hKU hF hmult hJK hy
  intro x hx
  exact orth_spread hun J hJ horth x hx x hx
end GlobalTheory.CompanionTheory.DSUniq
