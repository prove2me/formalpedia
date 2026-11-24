-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LKWtProj.wtProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:20:11.136634+00:00
-- url     : https://prove2.me/submissions/b8aa2d29-3f2e-4266-bc20-42bf8f27e2fa

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_WtProj
import Theorems.Thm_GlobalTheory_CompanionTheory_LKWtProj_exists_proj
import Theorems.Thm_GlobalTheory_CompanionTheory_LKWtProj_mem_iSup_eigenspace
import Theorems.Thm_GlobalTheory_CompanionTheory_LKWtProj_Ft_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_LKWtProj_chain_mem_iSup
import Theorems.Thm_GlobalTheory_CompanionTheory_LKWtProj_Ft_commute
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
theorem _root_.solution : CompanionTheory.D.LK.WtProj := by
  intro n ε₀ ε V _ _ E hE hU hL D hD τ t ht
  have hdiag : ∀ c (x : Cn n V), x ∈ ⨆ μ : ℂ, (Ft ε₀ E c).eigenspace μ := fun c =>
    chain_mem_iSup ε₀ E c fun v => by
      obtain ⟨S, hS, hst, hv⟩ := hL v
      exact mem_iSup_eigenspace (E c c) (fun x y => hU c c rfl x y) S (hst c c rfl) v hv
  let W : Submodule ℂ (Cn n V) :=
    { carrier := {x | ∀ A, t A = 0 → x A = 0}
      add_mem' := fun {a b} ha hb A hA => by simp [ha A hA, hb A hA]
      zero_mem' := fun A _ => rfl
      smul_mem' := fun c a ha A hA => by simp [ha A hA] }
  have hW : ∀ c, ∀ x ∈ W, Ft ε₀ E c x ∈ W := fun c x hx A hA => by
    rw [Ft_apply, hx A hA]; simp
  have key : ∀ s : Finset (Fin n), ∃ t' : Cn n V, (∀ c ∈ s, Ft ε₀ E c t' = (τ c : ℂ) • t') ∧ D t' = D t ∧
      t' ∈ W := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨t, by simp, rfl, fun A hA => hA⟩
    | insert c s _ ih =>
      obtain ⟨u, hu1, hu2, hu3⟩ := ih
      obtain ⟨P, hP1, hP2, hP3, hP4⟩ := exists_proj (Ft ε₀ E c) (τ c) u (hdiag c u)
      refine ⟨P u, fun d hd => ?_, ?_, hP2 W (hW c) u hu3⟩
      · rcases Finset.mem_insert.1 hd with rfl | hd
        · exact hP4
        · have := LinearMap.congr_fun (hP1 _ (Ft_commute ε₀ ε E hE c d)).eq u
          simp only [Module.End.mul_apply] at this
          rw [← this, hu1 d hd, map_smul]
      · have := LinearMap.congr_fun (hP1 _ (hD c)).eq u
        simp only [Module.End.mul_apply] at this
        rw [← this, hu2, hP3 _ (ht c)]
  obtain ⟨t', h1, h2, h3⟩ := key univ
  exact ⟨t', fun c => h1 c (mem_univ c), h2, h3⟩
end GlobalTheory.CompanionTheory.LKWtProj
