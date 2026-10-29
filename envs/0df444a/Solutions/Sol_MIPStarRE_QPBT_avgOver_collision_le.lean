-- Prove2me | solution 1 for MIPStarRE.QPBT.avgOver_collision_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:42:40.250066+00:00
-- url     : https://prove2.me/submissions/a527586e-f975-40e3-a9f8-82e0242d604b

-- Generated proof for MIPStarRE.QPBT.avgOver_collision_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Theorems.Thm_LIDT_MIPStarRE_LDT_Distribution_IsProbability_weight_sum_univ_eq_one
import Theorems.Thm_LIDT_MIPStarRE_LDT_Distribution_map_totalWeight

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-! # Consistency and commutation of the pasting codeword families

This module records the cross consistency of the coarse second codeword family,
the commutator estimate for the two coarse families, the collision average of
the distinct second codewords, and the comparison of the fine second codeword
family with its coarse-graining.  These are the codeword-family steps of the
proof of `lem:pasting` recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.

## References

Blueprint `blueprint/src/chapter/ch12_qpbt_games.tex:960-1050`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus

theorem solution {X Y₁ Y₂ R₂ Γ₂ : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₂] [DecidableEq R₂]
    [Fintype Γ₂] [DecidableEq Γ₂]
    (D : _root_.LIDT.MIPStarRE.LDT.Distribution ((X × Y₁) × Y₂)) (eval₂ : Γ₂ → Y₂ → R₂)
    (c : (X × Y₁) → Γ₂ → Γ₂ → ℝ) (η : ℝ)
    (hD : D.IsProbability) (hη : 0 ≤ η)
    (hc : ∀ p g g', 0 ≤ c p g g')
    (hmass : ∀ p, (∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else c p g g') ≤ 1)
    (hcoll : ∀ x y₁, 0 < (D.map Prod.fst).weight (x, y₁) →
      ∀ g g' : Γ₂, g ≠ g' →
        (∑ y₂ : Y₂, D.weight ((x, y₁), y₂) *
          if eval₂ g y₂ = eval₂ g' y₂ then 1 else 0) ≤
          η * (D.map Prod.fst).weight (x, y₁)) :
    _root_.LIDT.MIPStarRE.LDT.avgOver D (fun q => ∑ g : Γ₂, ∑ g' : Γ₂,
      if g = g' then 0 else
        if eval₂ g q.2 = eval₂ g' q.2 then c q.1 g g' else 0) ≤ η := by
  classical
  set FF : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ g : Γ₂, ∑ g' : Γ₂,
    if g = g' then 0 else
      if eval₂ g q.2 = eval₂ g' q.2 then c q.1 g g' else 0 with hFF
  have hmarg : ∀ p : X × Y₁,
      (∑ y₂ : Y₂, D.weight (p, y₂)) = (D.map Prod.fst).weight p := by
    intro p
    have h1 : (D.map Prod.fst).weight p
        = ∑ a ∈ Finset.univ.filter (fun a : (X × Y₁) × Y₂ => a.1 = p),
            D.weight a := by
      rw [_root_.LIDT.MIPStarRE.LDT.Distribution.map_weight]
      refine Finset.sum_subset
        (Finset.filter_subset_filter _ (Finset.subset_univ _)) ?_
      intro a ha hna
      refine D.outsideSupport a fun hsupp => hna ?_
      exact Finset.mem_filter.mpr ⟨hsupp, (Finset.mem_filter.mp ha).2⟩
    rw [h1, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
    exact Finset.sum_congr rfl fun y₂ _ => by simp
  have hWnn : ∀ p : X × Y₁, 0 ≤ (D.map Prod.fst).weight p :=
    fun p => (D.map Prod.fst).nonnegative p
  have hWsum : (∑ p : X × Y₁, (D.map Prod.fst).weight p) = 1 := by
    refine _root_.LIDT.MIPStarRE.LDT.Distribution.IsProbability.weight_sum_univ_eq_one ?_
    unfold _root_.LIDT.MIPStarRE.LDT.Distribution.IsProbability
    rw [_root_.LIDT.MIPStarRE.LDT.Distribution.map_totalWeight]
    exact hD
  have hkey : ∀ (p : X × Y₁) (g g' : Γ₂),
      (∑ y₂ : Y₂, D.weight (p, y₂) *
        (if g = g' then 0 else
          if eval₂ g y₂ = eval₂ g' y₂ then c p g g' else 0)) ≤
        (if g = g' then 0 else c p g g') * (η * (D.map Prod.fst).weight p) := by
    rintro ⟨x, y₁⟩ g g'
    by_cases hgg : g = g'
    · simp [hgg]
    have hrw : ∀ y₂ : Y₂, D.weight ((x, y₁), y₂) *
        (if g = g' then 0 else
          if eval₂ g y₂ = eval₂ g' y₂ then c (x, y₁) g g' else 0) =
        c (x, y₁) g g' * (D.weight ((x, y₁), y₂) *
          (if eval₂ g y₂ = eval₂ g' y₂ then 1 else 0)) := by
      intro y₂
      rw [if_neg hgg]
      by_cases hcol : eval₂ g y₂ = eval₂ g' y₂
      · simp [hcol]
        ring
      · simp [hcol]
    rw [Finset.sum_congr rfl (fun y₂ _ => hrw y₂), ← Finset.mul_sum, if_neg hgg]
    rcases lt_or_eq_of_le (hWnn (x, y₁)) with hpos | hzero
    · exact mul_le_mul_of_nonneg_left (hcoll x y₁ hpos g g' hgg) (hc (x, y₁) g g')
    · have hz : ∀ y₂ : Y₂, D.weight ((x, y₁), y₂) = 0 := by
        intro y₂
        have hsum : (∑ z : Y₂, D.weight ((x, y₁), z)) = 0 := by
          rw [hmarg (x, y₁), ← hzero]
        exact le_antisymm
          ((Finset.single_le_sum (fun z _ => D.nonnegative ((x, y₁), z))
            (Finset.mem_univ y₂)).trans_eq hsum) (D.nonnegative _)
      rw [← hzero]
      simp [hz]
  calc _root_.LIDT.MIPStarRE.LDT.avgOver D FF
      = ∑ q : (X × Y₁) × Y₂, D.weight q * FF q :=
        (_root_.LIDT.MIPStarRE.LDT.Distribution.sum_univ_eq_sum_support D (fun q => D.weight q * FF q)
          (fun q hq => by rw [D.outsideSupport q hq, zero_mul])).symm
    _ = ∑ p : X × Y₁, ∑ y₂ : Y₂, D.weight (p, y₂) * FF (p, y₂) :=
        Fintype.sum_prod_type _
    _ = ∑ p : X × Y₁, ∑ g : Γ₂, ∑ g' : Γ₂, ∑ y₂ : Y₂,
          D.weight (p, y₂) *
            (if g = g' then 0 else
              if eval₂ g y₂ = eval₂ g' y₂ then c p g g' else 0) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        simp only [hFF, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun g _ => Finset.sum_comm
    _ ≤ ∑ p : X × Y₁, ∑ g : Γ₂, ∑ g' : Γ₂,
          (if g = g' then 0 else c p g g') *
            (η * (D.map Prod.fst).weight p) :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun g _ =>
          Finset.sum_le_sum fun g' _ => hkey p g g'
    _ = ∑ p : X × Y₁,
          (∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else c p g g') *
            (η * (D.map Prod.fst).weight p) := by
        simp only [← Finset.sum_mul]
    _ ≤ ∑ p : X × Y₁, 1 * (η * (D.map Prod.fst).weight p) :=
        Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_right (hmass p)
          (mul_nonneg hη (hWnn p))
    _ = η * ∑ p : X × Y₁, (D.map Prod.fst).weight p := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ = η := by rw [hWsum, mul_one]
