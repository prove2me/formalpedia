-- Prove2me | solution 1 for GlobalTheory.UnitLogPartition.exists_nonneg_hasSum_lattice_translates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:03:06.597898+00:00
-- url     : https://prove2.me/submissions/0d313258-143f-44ad-a3ff-939aa65da2d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothHomogeneousHasSumUnitSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMeasurablePartitionOfUnityUnitLogTranslate
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_PeriodicPartition_locallyFinite_support_translate
import Theorems.Thm_GlobalTheory_exists_radius_lattice_translate_norm_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField MeasureTheory
open scoped ContDiff
noncomputable section
open GlobalTheory
open GlobalTheory.UnitLogPartition
open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
namespace GlobalTheory.UnitLogPartition
theorem _root_.solution (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ η : V → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ (∀ z, 0 ≤ η z) ∧
      ∀ y, HasSum (fun l : L => η (y + l)) 1 := by
  obtain ⟨R, hR, hcov⟩ := GlobalTheory.exists_radius_lattice_translate_norm_le V L
  let b : ContDiffBump (0 : V) := ⟨R, R + 1, hR, by linarith⟩
  have hφc : HasCompactSupport (b : V → ℝ) := b.hasCompactSupport
  have hφs : ContDiff ℝ ∞ (b : V → ℝ) := b.contDiff
  have hlf := GlobalTheory.PeriodicPartition.locallyFinite_support_translate L b hφc
  set S : V → ℝ := fun z => ∑ᶠ l : L, b (z + l) with hS
  have hSs : ContDiff ℝ ∞ S := by
    rw [← contMDiff_iff_contDiff]
    refine contMDiff_finsum (f := fun (l : L) (z : V) => b (z + l)) (fun l => ?_) hlf
    rw [contMDiff_iff_contDiff]
    exact hφs.comp (contDiff_id.add contDiff_const)
  have hSp : ∀ (l : L) z, S (z + l) = S z := by
    intro l z
    show ∑ᶠ m : L, b (z + l + m) = ∑ᶠ m : L, b (z + m)
    rw [← finsum_comp_equiv (Equiv.addLeft l) (f := fun m : L => b (z + m))]
    simp [add_assoc]
  have hSpos : ∀ z, 0 < S z := by
    intro z
    obtain ⟨l, hl⟩ := hcov z
    have h1 := single_le_finsum (f := fun l : L => b (z + l)) l (hlf.point_finite z)
      (fun l => b.nonneg)
    have h2 : b (z + l) = 1 := b.one_of_mem_closedBall (by simpa using hl)
    simp only [h2] at h1
    exact lt_of_lt_of_le one_pos h1
  refine ⟨fun z => b z / S z, hφs.div hSs fun z => (hSpos z).ne', ?_,
    fun z => div_nonneg b.nonneg (hSpos z).le, fun y => ?_⟩
  · simp only [div_eq_mul_inv]
    exact hφc.mul_right
  · simp only [hSp]
    have hfin : (Function.support fun l : L => b (y + l)).Finite := hlf.point_finite y
    have h1 : HasSum (fun l : L => b (y + l)) (S y) := by
      have hs : Summable (fun l : L => b (y + l)) := summable_of_finite_support hfin
      have := hs.hasSum
      rwa [tsum_eq_finsum hfin] at this
    have := h1.div_const (S y)
    rwa [div_self (hSpos y).ne'] at this
end GlobalTheory.UnitLogPartition
