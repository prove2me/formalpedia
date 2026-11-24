-- Prove2me | solution 1 for GlobalTheory.LatticePartition.exists_lattice_partition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:13:21.903809+00:00
-- url     : https://prove2.me/submissions/ad1f0620-3104-476c-a4f6-6b912a046575

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealCompactPartitionUnity
import Theorems.Thm_GlobalTheory_LatticePartition_bumpProd_contDiff
import Theorems.Thm_GlobalTheory_LatticePartition_bumpProd_compact
import Theorems.Thm_GlobalTheory_LatticePartition_hasSum_bumpProd
import Theorems.Thm_GlobalTheory_LatticePartition_summable_latPt
import Theorems.Thm_GlobalTheory_LatticePartition_finite_of_summable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff
noncomputable section
open GlobalTheory GlobalTheory.LatticePartition
namespace GlobalTheory.LatticePartition
theorem _root_.solution :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    ∃ ψ : SchwartzMap V ℂ, HasCompactSupport (ψ : V → ℂ) ∧ (∀ x, starRingEnd ℂ (ψ x) = ψ x) ∧
      ∃ v : (Fin (Module.finrank ℝ V) → ℤ) → V, (∀ x, HasSum (fun j => ψ (x - v j)) 1) ∧
        (∀ R : ℝ, {j | ‖v j‖ ≤ R}.Finite) ∧ ∃ M : ℕ, Summable (fun j => ((1 + ‖v j‖) ^ M)⁻¹) := by
  intro V _ _ _
  obtain ⟨M, hS⟩ := summable_latPt (Module.finBasis ℝ V)
  generalize (Module.finBasis ℝ V).equivFunL = e at hS
  have hc : HasCompactSupport (fun x => ((bumpProd e x : ℝ) : ℂ)) :=
    (bumpProd_compact e).comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hd : ContDiff ℝ ∞ (fun x => ((bumpProd e x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (bumpProd_contDiff e)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : SchwartzMap V ℂ, (ψ : V → ℂ) = fun x => ((bumpProd e x : ℝ) : ℂ) :=
    ⟨hc.toSchwartzMap hd, rfl⟩
  refine ⟨ψ, hψ ▸ hc, ?_, latPt e, ?_, ?_, M, hS⟩
  · intro x
    rw [hψ]
    exact Complex.conj_ofReal _
  · intro x
    rw [hψ]
    have h := Complex.hasSum_ofReal.2 (hasSum_bumpProd e x)
    rwa [Complex.ofReal_one] at h
  · exact finite_of_summable (fun j => ‖latPt e j‖) (fun _ => norm_nonneg _) M hS
end GlobalTheory.LatticePartition
