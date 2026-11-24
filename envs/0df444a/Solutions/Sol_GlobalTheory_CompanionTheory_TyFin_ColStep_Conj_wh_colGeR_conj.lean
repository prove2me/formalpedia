-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.wh_colGeR_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:29:02.155242+00:00
-- url     : https://prove2.me/submissions/f168b602-67c7-4fc2-a2cf-d9b9c1a67e92

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerBlockEmbeddingConj
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Conj_conj_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Conj_patChar_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep GlobalTheory.CompanionTheory.TyFin.ColStep.Conj
variable {K : Type} [Field K]
namespace GlobalTheory.CompanionTheory.TyFin.ColStep.Conj
theorem _root_.solution : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ) (g : GL (Fin j) K) (h : GL (Fin d) K) (r : Fin j → K),
    j < d → (∀ x y, χ (x * y * x⁻¹) = χ y) →
    (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K) →
    ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) →
    wh (colGe d j) (colGeR K d j r) ψ₀ χ = wh (colGe d j) (colGeR K d j (Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K))) ψ₀ χ := by
  intro K _ _ _ d j ψ₀ χ g h r hj hχ h1 h2
  have hN : ∀ u : GL (Fin d) K, h * u * h⁻¹ ∈ patSet K (colGe d j) ↔ u ∈ patSet K (colGe d j) := by
    intro u
    refine ⟨fun hu => ?_, conj_mem hj.le g h h1 h2⟩
    have := conj_mem hj.le g⁻¹ h⁻¹ h2 (by rw [inv_inv, inv_inv]; exact h1) hu
    have e : h⁻¹ * (h * u * h⁻¹) * (h⁻¹)⁻¹ = u := by group
    rwa [e] at this
  unfold wh
  congr 1
  rw [← Equiv.sum_comp (MulAut.conj h).toEquiv]
  refine Finset.sum_congr rfl fun u _ => ?_
  have e : (MulAut.conj h).toEquiv u = h * u * h⁻¹ := rfl
  rw [e]
  by_cases hu : u ∈ patSet K (colGe d j)
  · rw [if_pos ((hN u).2 hu), if_pos hu, patChar_conj hj ψ₀ g h r h1 h2 u, hχ]
  · rw [if_neg (fun q => hu ((hN u).1 q)), if_neg hu]
end GlobalTheory.CompanionTheory.TyFin.ColStep.Conj
