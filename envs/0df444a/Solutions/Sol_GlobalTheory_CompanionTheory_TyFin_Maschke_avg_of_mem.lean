-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Maschke.avg_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:37.083337+00:00
-- url     : https://prove2.me/submissions/cbc39e86-a770-4cd9-b0a5-73266e55cdd9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_avg_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_mem_intw_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_rep_inv_apply

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
theorem _root_.solution {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {f : V →ₗ[ℂ] W}
    (hf : f ∈ Intw ρ σ) : avg ρ σ f = f := by
  ext v
  have hc : (Fintype.card Γ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h : ∀ g : Γ, σ g (f (ρ g⁻¹ v)) = f v := fun g => by
    rw [← mem_intw_apply hf, rep_inv_apply]
  simp only [avg_apply, h, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
end GlobalTheory.CompanionTheory.TyFin.Maschke
