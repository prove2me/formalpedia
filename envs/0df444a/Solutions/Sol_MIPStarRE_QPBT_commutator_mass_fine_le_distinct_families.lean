-- Prove2me | solution 1 for MIPStarRE.QPBT.commutator_mass_fine_le_distinct_families
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:49:11.351989+00:00
-- url     : https://prove2.me/submissions/f3dcd360-ba6d-4a01-ab86-ccd56fe79abb

-- Generated proof for MIPStarRE.QPBT.commutator_mass_fine_le_distinct_families.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Theorems.Thm_MIPStarRE_QPBT_abs_cross_move_gap_le_sqrt_distinct_families
import Theorems.Thm_MIPStarRE_QPBT_avgOver_pinched_collision_le_distinct_families
import Theorems.Thm_MIPStarRE_QPBT_commutator_mass_eq_expansion
import Theorems.Thm_MIPStarRE_QPBT_pinched_coarse_sub_fine_eq_distinct_families
import Theorems.Thm_MIPStarRE_QPBT_sum_norm_ordered_product_le_one

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-! # Ordered product masses and the assembly of the pasting estimate

This module records the mass estimates of step 3 of the proof of the adopted
statement of `lem:pasting`, the fine commutator mass of step 5, the assembly of
those estimates into the explicit bound on the defect of the pasted family, the
bound of one on the defect of an arbitrary pair of placed families, and the
scalar comparison of the assembled bound with the error function of the
theorem.  The proof of the adopted statement is recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.

## References

Blueprint `ch12_qpbt_games.tex:960-990`, paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus

theorem solution {X Y₁ Y₂ R₁ R₂ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
    [Fintype R₂] [DecidableEq R₂] [Fintype Γ₂] [DecidableEq Γ₂]
    [Fintype ι] [DecidableEq ι]
    (D : _root_.LIDT.MIPStarRE.LDT.Distribution ((X × Y₁) × Y₂)) (eval₂ : Γ₂ → Y₂ → R₂)
    (G₂ opposite : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Γ₂ ι) (P : (X × Y₁) → _root_.LIDT.MIPStarRE.Quantum.Measurement R₁ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (η K₀ m εc εf : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1) (hη : 0 ≤ η)
    (hG₂ : ∀ x, _root_.MIPStarRE.QPBT.Measurement.IsProjective (G₂ x))
    (hcoll : ∀ x y₁, 0 < (D.map Prod.fst).weight (x, y₁) →
      ∀ g g' : Γ₂, g ≠ g' →
        (∑ y₂ : Y₂, D.weight ((x, y₁), y₂) *
          if eval₂ g y₂ = eval₂ g' y₂ then 1 else 0) ≤
          η * (D.map Prod.fst).weight (x, y₁))
    (hK₀ : _root_.MIPStarRE.QPBT.opFamilyDistSq D (fun q (ab : R₁ × R₂) => _root_.MIPStarRE.QPBT.heteroKron 1
      ((P q.1).effect ab.1 * ((G₂ q.1.1).postprocess
          (fun g => eval₂ g q.2)).effect ab.2 -
        ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)).effect ab.2 *
          (P q.1).effect ab.1)) (fun _ _ => 0) ψ ≤ K₀)
    (hmass : 1 - m ≤ _root_.LIDT.MIPStarRE.LDT.avgOver D (fun q => ∑ ab : R₁ × R₂,
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q.1).effect ab.1 *
        ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)).effect ab.2)) ψ‖ ^ 2))
    (hglc : _root_.MIPStarRE.QPBT.opFamilyDistSq D
      (fun q b => _root_.MIPStarRE.QPBT.heteroKron 1 (((G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect b))
      (fun q b => _root_.MIPStarRE.QPBT.heteroKron (((opposite q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect b) 1) ψ ≤ εc)
    (hglf : _root_.MIPStarRE.QPBT.opFamilyDistSq D (fun q g => _root_.MIPStarRE.QPBT.heteroKron 1 ((G₂ q.1.1).effect g))
      (fun q g => _root_.MIPStarRE.QPBT.heteroKron ((opposite q.1.1).effect g) 1) ψ ≤ εf) :
    _root_.LIDT.MIPStarRE.LDT.avgOver D (fun q => ∑ a : R₁, ∑ g : Γ₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q.1).effect a * (G₂ q.1.1).effect g -
          (G₂ q.1.1).effect g * (P q.1).effect a)) ψ‖ ^ 2) ≤
      K₀ + m + 2 * η + 2 * Real.sqrt εf + 2 * Real.sqrt εc := by
  classical
  set Qm : ((X × Y₁) × Y₂) → _root_.LIDT.MIPStarRE.Quantum.Measurement R₂ ι :=
    fun q => (G₂ q.1.1).postprocess (fun g => eval₂ g q.2) with hQm
  have hQproj : ∀ q, _root_.MIPStarRE.QPBT.Measurement.IsProjective (Qm q) := by
    intro q
    exact _root_.MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective (G₂ q.1.1) (hG₂ q.1.1) _
  set F1 : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ a : R₁, ∑ g : Γ₂,
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q.1).effect a *
      (G₂ q.1.1).effect g)) ψ‖ ^ 2 with hF1d
  set C1 : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ a : R₁, ∑ b : R₂,
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q.1).effect a *
      (Qm q).effect b)) ψ‖ ^ 2 with hC1d
  set Sq : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ a : R₁,
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q.1).effect a * (P q.1).effect a)) with hSd
  set F3 : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ a : R₁, ∑ g : Γ₂,
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1 ((G₂ q.1.1).effect g * (P q.1).effect a *
      (G₂ q.1.1).effect g * (P q.1).effect a)) with hF3d
  set C3 : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ a : R₁, ∑ b : R₂,
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1 ((Qm q).effect b * (P q.1).effect a *
      (Qm q).effect b * (P q.1).effect a)) with hC3d
  set MF : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ g : Γ₂,
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((opposite q.1.1).effect g)
      (∑ a : R₁, (P q.1).effect a * (G₂ q.1.1).effect g * (P q.1).effect a))
    with hMFd
  set MC : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ b : R₂,
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (((opposite q.1.1).postprocess (fun g => eval₂ g q.2)).effect b)
      (∑ a : R₁, (P q.1).effect a * (Qm q).effect b * (P q.1).effect a))
    with hMCd
  set glf : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ g : Γ₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
    (_root_.MIPStarRE.QPBT.heteroKron 1 ((G₂ q.1.1).effect g) -
      _root_.MIPStarRE.QPBT.heteroKron ((opposite q.1.1).effect g) 1) ψ‖ ^ 2 with hglfd
  set glc : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ b : R₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
    (_root_.MIPStarRE.QPBT.heteroKron 1 ((Qm q).effect b) -
      _root_.MIPStarRE.QPBT.heteroKron (((opposite q.1.1).postprocess (fun g => eval₂ g q.2)).effect b) 1) ψ‖ ^ 2
    with hglcd
  set col : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ g : Γ₂, ∑ g' : Γ₂,
    if g = g' then 0 else if eval₂ g q.2 = eval₂ g' q.2 then
      ∑ a : R₁, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((opposite q.1.1).effect g')
        ((P q.1).effect a * (G₂ q.1.1).effect g * (P q.1).effect a))
    else 0 with hcold
  -- the two expansions of the commutator masses
  have hfine : ∀ q, (∑ a : R₁, ∑ g : Γ₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q.1).effect a * (G₂ q.1.1).effect g -
        (G₂ q.1.1).effect g * (P q.1).effect a)) ψ‖ ^ 2) =
      F1 q + Sq q - 2 * F3 q := fun q =>
    _root_.MIPStarRE.QPBT.commutator_mass_eq_expansion (P q.1) (G₂ q.1.1) ψ (hG₂ q.1.1)
  have hcoarse : ∀ q, (∑ a : R₁, ∑ b : R₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q.1).effect a * (Qm q).effect b -
        (Qm q).effect b * (P q.1).effect a)) ψ‖ ^ 2) =
      C1 q + Sq q - 2 * C3 q := fun q =>
    _root_.MIPStarRE.QPBT.commutator_mass_eq_expansion (P q.1) (Qm q) ψ (hQproj q)
  -- the two moves and the collision split
  have hmoveF : ∀ q, |F3 q - MF q| ≤ Real.sqrt (glf q) := fun q =>
    _root_.MIPStarRE.QPBT.abs_cross_move_gap_le_sqrt_distinct_families (P q.1) (G₂ q.1.1)
      (opposite q.1.1) ψ hψ
  have hmoveC : ∀ q, |C3 q - MC q| ≤ Real.sqrt (glc q) := fun q =>
    _root_.MIPStarRE.QPBT.abs_cross_move_gap_le_sqrt_distinct_families (P q.1) (Qm q)
      ((opposite q.1.1).postprocess (fun g => eval₂ g q.2)) ψ hψ
  have hsplit : ∀ q, MC q - MF q = col q := fun q =>
    _root_.MIPStarRE.QPBT.pinched_coarse_sub_fine_eq_distinct_families (P q.1) (G₂ q.1.1) (opposite q.1.1)
      (fun g => eval₂ g q.2) ψ
  have hF1le : ∀ q, F1 q ≤ 1 := fun q =>
    _root_.MIPStarRE.QPBT.sum_norm_ordered_product_le_one (P q.1) (G₂ q.1.1) ψ hψ
  -- averaging
  have hglfnn : ∀ q, 0 ≤ glf q := fun q => Finset.sum_nonneg fun g _ => sq_nonneg _
  have hglcnn : ∀ q, 0 ≤ glc q := fun q => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hJf : |avgOver D F3 - _root_.LIDT.MIPStarRE.LDT.avgOver D MF| ≤ Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver D glf) := by
    rw [← _root_.LIDT.MIPStarRE.LDT.avgOver_sub]
    exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise D _ glf
      hmoveF hglfnn (by rw [hD.weight_sum_eq_one])
  have hJc : |avgOver D C3 - _root_.LIDT.MIPStarRE.LDT.avgOver D MC| ≤ Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver D glc) := by
    rw [← _root_.LIDT.MIPStarRE.LDT.avgOver_sub]
    exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise D _ glc
      hmoveC hglcnn (by rw [hD.weight_sum_eq_one])
  have hcolavg : _root_.LIDT.MIPStarRE.LDT.avgOver D MC - _root_.LIDT.MIPStarRE.LDT.avgOver D MF ≤ η := by
    rw [← _root_.LIDT.MIPStarRE.LDT.avgOver_sub, _root_.LIDT.MIPStarRE.LDT.avgOver_congr D _ col hsplit]
    exact _root_.MIPStarRE.QPBT.avgOver_pinched_collision_le_distinct_families D eval₂ G₂ opposite P ψ η hD hψ hη hcoll
  have hF1avg : _root_.LIDT.MIPStarRE.LDT.avgOver D F1 ≤ 1 := by
    have := _root_.LIDT.MIPStarRE.LDT.avgOver_mono D F1 (fun _ => (1 : ℝ)) hF1le
    rwa [_root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability D hD] at this
  have hC1avg : 1 - m ≤ _root_.LIDT.MIPStarRE.LDT.avgOver D C1 := by
    refine le_trans hmass (le_of_eq (_root_.LIDT.MIPStarRE.LDT.avgOver_congr D _ C1 fun q => ?_))
    rw [hC1d, Fintype.sum_prod_type]
  have hK₀avg : _root_.LIDT.MIPStarRE.LDT.avgOver D C1 + _root_.LIDT.MIPStarRE.LDT.avgOver D Sq - 2 * _root_.LIDT.MIPStarRE.LDT.avgOver D C3 ≤ K₀ := by
    have hEq : _root_.LIDT.MIPStarRE.LDT.avgOver D (fun q => C1 q + Sq q - 2 * C3 q) =
        _root_.LIDT.MIPStarRE.LDT.avgOver D C1 + _root_.LIDT.MIPStarRE.LDT.avgOver D Sq - 2 * _root_.LIDT.MIPStarRE.LDT.avgOver D C3 := by
      rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sub, _root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul]
    rw [← hEq]
    refine le_trans (le_of_eq ?_) hK₀
    refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr D _ _ fun q => ?_
    rw [← hcoarse q, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      rw [sub_zero]
  have hglfavg : _root_.LIDT.MIPStarRE.LDT.avgOver D glf ≤ εf := hglf
  have hglcavg : _root_.LIDT.MIPStarRE.LDT.avgOver D glc ≤ εc := hglc
  have hsf : Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver D glf) ≤ Real.sqrt εf := Real.sqrt_le_sqrt hglfavg
  have hsc : Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver D glc) ≤ Real.sqrt εc := Real.sqrt_le_sqrt hglcavg
  have hgoal : _root_.LIDT.MIPStarRE.LDT.avgOver D (fun q => ∑ a : R₁, ∑ g : Γ₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q.1).effect a * (G₂ q.1.1).effect g -
        (G₂ q.1.1).effect g * (P q.1).effect a)) ψ‖ ^ 2) =
      _root_.LIDT.MIPStarRE.LDT.avgOver D F1 + _root_.LIDT.MIPStarRE.LDT.avgOver D Sq - 2 * _root_.LIDT.MIPStarRE.LDT.avgOver D F3 := by
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_congr D _ (fun q => F1 q + Sq q - 2 * F3 q) hfine,
      _root_.LIDT.MIPStarRE.LDT.avgOver_sub, _root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul]
  rw [hgoal]
  have h1 := abs_le.mp hJf
  have h2 := abs_le.mp hJc
  linarith [h1.1, h1.2, h2.1, h2.2, hcolavg, hF1avg, hC1avg, hK₀avg, hsf, hsc]
