-- Prove2me | solution 1 for GlobalTheory.LatticePartition.summable_latPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:54:28.046828+00:00
-- url     : https://prove2.me/submissions/7a6dd7f0-c0bf-4333-af25-2b661a0a2e7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealCompactPartitionUnity
import Theorems.Thm_GlobalTheory_LatticePartition_summable_lattice

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
namespace GlobalTheory.LatticePartition
theorem _root_.solution [FiniteDimensional ℝ V] (b : Module.Basis (Fin n) ℝ V) :
    ∃ M : ℕ, Summable (fun j : Fin n → ℤ => ((1 + ‖latPt b.equivFunL j‖) ^ M)⁻¹) := by
  have hmem : ∀ j, latPt b.equivFunL j ∈ Submodule.span ℤ (Set.range b) := fun j => by
    have : latPt b.equivFunL j = ∑ i, (j i : ℝ) • b i := b.equivFun_symm_apply _
    rw [this]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hinj : Function.Injective fun j : Fin n → ℤ =>
      (⟨latPt b.equivFunL j, hmem j⟩ : Submodule.span ℤ (Set.range b)) := by
    intro j k hjk
    have h1 : latPt b.equivFunL j = latPt b.equivFunL k := congrArg Subtype.val hjk
    have h2 : (fun i => (j i : ℝ)) = fun i => (k i : ℝ) := b.equivFunL.symm.injective h1
    funext i
    exact_mod_cast congrFun h2 i
  have h := (summable_lattice (Submodule.span ℤ (Set.range b))).comp_injective hinj
  refine ⟨Module.finrank ℤ (Submodule.span ℤ (Set.range b)) + 1, h.congr fun j => ?_⟩
  simp only [Function.comp_apply, Submodule.coe_norm]
end GlobalTheory.LatticePartition
