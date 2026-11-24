-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LKWtProj.chain_mem_iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:57:16.349968+00:00
-- url     : https://prove2.me/submissions/f2fd9192-d669-4f83-b4ab-8eacf0136299

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_WtProj
import Theorems.Thm_GlobalTheory_CompanionTheory_LKWtProj_Ft_apply
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
open Finset
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LKWtProj
open CompanionTheory.D.LK
open CompanionTheory.D.DSIC (KRel KUnit KStab)
namespace GlobalTheory.CompanionTheory.LKWtProj
theorem _root_.solution {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c : Fin n) (h : ∀ v : V, v ∈ ⨆ μ : ℂ, (E c c).eigenspace μ)
    (t : Cn n V) : t ∈ ⨆ μ : ℂ, (Ft ε E c).eigenspace μ := by
  classical
  rw [← Finset.univ_sum_single t]
  refine Submodule.sum_mem _ fun A _ => ?_
  have hle : (⨆ μ : ℂ, (E c c).eigenspace μ).map (LinearMap.single ℂ (fun _ : Finset (Pos n) => V) A) ≤
      ⨆ μ : ℂ, (Ft ε E c).eigenspace μ := by
    rw [Submodule.map_iSup]
    refine iSup_le fun μ => le_trans ?_ (le_iSup _ (μ + (wt (A.filter (cpt ε)) c : ℂ)))
    rintro _ ⟨y, hy, rfl⟩
    have hy' := Module.End.mem_eigenspace_iff.1 hy
    rw [Module.End.mem_eigenspace_iff]
    funext B
    rw [Ft_apply]
    by_cases hB : B = A
    · subst hB
      simp [hy', add_smul]
    · simp [Pi.single_eq_of_ne hB]
  exact hle ⟨t A, h _, rfl⟩
end GlobalTheory.CompanionTheory.LKWtProj
