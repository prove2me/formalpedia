-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Maschke.avg_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:26:54.314648+00:00
-- url     : https://prove2.me/submissions/b9a3b56a-d19c-4589-b652-ec04b60af6b9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_avg_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.Maschke
variable {Γ : Type} [Group Γ] [Fintype Γ]
variable {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]
namespace GlobalTheory.CompanionTheory.TyFin.Maschke
theorem _root_.solution (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W) (f : V →ₗ[ℂ] W) :
    avg ρ σ f ∈ Intw ρ σ := by
  intro h
  ext v
  simp only [LinearMap.comp_apply, avg_apply, map_smul, map_sum]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun g => ?_
  have e1 : ρ (h⁻¹ * g)⁻¹ v = ρ g⁻¹ (ρ h v) := by
    rw [mul_inv_rev, inv_inv, map_mul]; rfl
  have e2 : ∀ w, σ h (σ (h⁻¹ * g) w) = σ g w := fun w => by
    have h2 : σ (h * (h⁻¹ * g)) w = σ g w := by simp
    rw [map_mul σ h (h⁻¹ * g)] at h2
    exact h2
  simp only [Equiv.coe_mulLeft]
  rw [e1, e2]
end GlobalTheory.CompanionTheory.TyFin.Maschke
