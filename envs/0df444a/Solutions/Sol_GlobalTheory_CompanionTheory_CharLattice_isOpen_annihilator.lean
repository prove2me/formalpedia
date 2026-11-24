-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CharLattice.isOpen_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:22:52.01218+00:00
-- url     : https://prove2.me/submissions/a9bd83ba-4306-4095-83d9-52ef67577e2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CharacterAnnihilatorIntegerLattice
import Theorems.Thm_GlobalTheory_CharDualMat_exists_ball_trivial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CharLattice
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.CharLattice
theorem _root_.solution (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) (b : k) (hb : b ≠ 0) :
    IsOpen (annihilator ψ n b : Set (Fin n → k)) := by
  obtain ⟨γ, hγ0, hγ⟩ := GlobalTheory.CharDualMat.exists_ball_trivial ψ hψ
  apply AddSubgroup.isOpen_of_mem_nhds
  have hball : {z : k | valuation k z < γ} ∈ nhds (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem hγ0
  have hmul : {y : k | valuation k (b * y) < γ} ∈ nhds (0 : k) := by
    have h := (continuous_const.mul continuous_id : Continuous fun y : k => b * y).tendsto' 0 0 (mul_zero b)
    exact h hball
  have hU : (Set.univ.pi fun _ : Fin n => {y : k | valuation k (b * y) < γ}) ∈ nhds (0 : Fin n → k) :=
    set_pi_mem_nhds Set.finite_univ (fun j _ => hmul)
  refine Filter.mem_of_superset hU ?_
  intro x hx t ht
  apply hγ
  show valuation k (b * ∑ i, t i * x i) < γ
  rw [Finset.mul_sum]
  refine (valuation k).map_sum_lt hγ0 fun j _ => ?_
  have hxj : valuation k (b * x j) < γ := hx j (Set.mem_univ j)
  have htj : valuation k (t j) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (ht j)
  refine lt_of_le_of_lt ?_ hxj
  calc valuation k (b * (t j * x j)) = valuation k (t j) * valuation k (b * x j) := by
        rw [← map_mul]; ring_nf
    _ ≤ 1 * valuation k (b * x j) := mul_le_mul_left htj _
    _ = valuation k (b * x j) := one_mul _
end GlobalTheory.CompanionTheory.CharLattice
