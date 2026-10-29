-- Prove2me | solution 1 for MIPStarRE.QPBT.pasting_error_of_marginal_consistency_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:04:38.151985+00:00
-- url     : https://prove2.me/submissions/8a42aa48-e8ce-46f1-9b2d-7e430da9c4fd

-- Generated proof for MIPStarRE.QPBT.pasting_error_of_marginal_consistency_explicit.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Defs
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Pasting_Heterogeneous
import Theorems.Thm_MIPStarRE_QPBT_coarse_commutator_bound_explicit
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_pasted_le_sqrt_one_sided
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_placed_le_one
import Theorems.Thm_MIPStarRE_QPBT_pasting_error_sqrt_le_rpow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.Pasting
end MIPStarRE.QPBT.Pasting

/-! # Pasting on independent local spaces

The two local spaces are realized in a common product space by adjoining fixed
basis vectors. Tensor placement supplies the corresponding
measurements, with projectivity and postprocessing preserved.

## References

Paper `lem:pasting`,
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`, and its use in
`lem:qld-xz-lines`, `14_analysis_of_the_pauli_basis_test.tex:882-963`.
The common-space realization is a formalization-only auxiliary; see issue
Dengnifer/MIPStarRE-QPBT-bak#495.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus



open MIPStarRE.QPBT.Pasting

variable {ιA ιB : Type*}
  [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]

theorem solution :
    ∀ {X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ι : Type*}
        [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
        [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
        [Fintype R₂] [DecidableEq R₂]
        [Fintype Γ₁] [DecidableEq Γ₁] [Fintype Γ₂] [DecidableEq Γ₂]
        [Fintype ι] [DecidableEq ι]
        (D : _root_.LIDT.MIPStarRE.LDT.Distribution ((X × Y₁) × Y₂))
        (eval₁ : Γ₁ → Y₁ → R₁) (eval₂ : Γ₂ → Y₂ → R₂)
        (G₁ : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Γ₁ ι) (G₂ : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Γ₂ ι)
        (A : ((X × Y₁) × Y₂) → _root_.LIDT.MIPStarRE.Quantum.Measurement (R₁ × R₂) ι)
        (ψ : EuclideanSpace ℂ (ι × ι)) (η δ : ℝ),
        D.IsProbability → ‖ψ‖ = 1 → 0 ≤ η → 0 ≤ δ →
        (∀ x, _root_.MIPStarRE.QPBT.Measurement.IsProjective (G₂ x)) →
        (∀ q, _root_.MIPStarRE.QPBT.Measurement.IsProjective (A q)) →
        _root_.MIPStarRE.QPBT.HasConditionalCollisionBound D eval₂ η →
        _root_.MIPStarRE.QPBT.consistencyDefect D
          (fun q a₁ => _root_.MIPStarRE.QPBT.heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
          (fun q a₁ => _root_.MIPStarRE.QPBT.heteroKron 1 (((G₁ q.1.1).postprocess
            (fun g => eval₁ g q.1.2)).effect a₁)) ψ ≤ δ →
        _root_.MIPStarRE.QPBT.consistencyDefect D
          (fun q a₂ => _root_.MIPStarRE.QPBT.heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
          (fun q a₂ => _root_.MIPStarRE.QPBT.heteroKron 1 (((G₂ q.1.1).postprocess
            (fun g => eval₂ g q.2)).effect a₂)) ψ ≤ δ →
        _root_.MIPStarRE.QPBT.consistencyDefect D (fun q a => _root_.MIPStarRE.QPBT.heteroKron ((A q).effect a) 1)
          (fun q a => _root_.MIPStarRE.QPBT.heteroKron 1 (∑ g₁ : Γ₁, ∑ g₂ : Γ₂,
            if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
              _root_.MIPStarRE.QPBT.pastedMeasurement (fun g => (G₁ q.1.1).effect g)
                (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0)) ψ ≤
          115 * (η ^ (1 / 4 : ℝ) + δ ^ (1 / 8 : ℝ)) := by
  classical
  intro X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ι _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    D eval₁ eval₂ G₁ G₂ A ψ η δ hD hψ hη hδ hG₂ hA hcoll h₁ h₂
  have hpm : ∀ q : (X × Y₁) × Y₂,
      (∀ g : Γ₁ × Γ₂, 0 ≤ _root_.MIPStarRE.QPBT.pastedMeasurement (fun g => (G₁ q.1.1).effect g)
          (fun g => (G₂ q.1.1).effect g) g.1 g.2) ∧
        (∑ g : Γ₁ × Γ₂, _root_.MIPStarRE.QPBT.pastedMeasurement (fun g => (G₁ q.1.1).effect g)
          (fun g => (G₂ q.1.1).effect g) g.1 g.2) = 1 :=
    fun q => _root_.MIPStarRE.QPBT.pastedMeasurement_isMeasurement (G₁ q.1.1) (G₂ q.1.1) (hG₂ q.1.1)
  set Bp : ((X × Y₁) × Y₂) → _root_.LIDT.MIPStarRE.Quantum.Measurement (R₁ × R₂) ι := fun q =>
    (_root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne
      (fun g : Γ₁ × Γ₂ => _root_.MIPStarRE.QPBT.pastedMeasurement (fun g => (G₁ q.1.1).effect g)
        (fun g => (G₂ q.1.1).effect g) g.1 g.2) (hpm q).1 (hpm q).2).postprocess
      (fun g => (eval₁ g.1 q.1.2, eval₂ g.2 q.2)) with hBpdef
  have heff : ∀ (q : (X × Y₁) × Y₂) (a : R₁ × R₂), (Bp q).effect a =
      ∑ g₁ : Γ₁, ∑ g₂ : Γ₂, if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
        _root_.MIPStarRE.QPBT.pastedMeasurement (fun g => (G₁ q.1.1).effect g)
          (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0 := by
    intro q a
    rw [hBpdef]
    simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne]
    rw [Finset.sum_filter, Fintype.sum_prod_type]
  have hle1 := _root_.MIPStarRE.QPBT.consistencyDefect_placed_le_one D A Bp ψ hD hψ
  have hfam : (fun (q : (X × Y₁) × Y₂) (a : R₁ × R₂) =>
        _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ((Bp q).effect a)) =
      fun (q : (X × Y₁) × Y₂) (a : R₁ × R₂) => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)
        (∑ g₁ : Γ₁, ∑ g₂ : Γ₂, if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
          _root_.MIPStarRE.QPBT.pastedMeasurement (fun g => (G₁ q.1.1).effect g)
            (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0) := by
    funext q a
    rw [heff q a]
  rw [hfam] at hle1
  rcases le_or_gt δ 1 with hδ1 | hδgt
  · rcases le_or_gt η 1 with hη1 | hηgt
    · refine le_trans (_root_.MIPStarRE.QPBT.consistencyDefect_pasted_le_sqrt_one_sided D eval₁ eval₂ G₁ G₂ A ψ
        η δ 32 hD hψ hη hG₂ hA hcoll h₁ h₂ hδ hδ1
        (_root_.MIPStarRE.QPBT.coarse_commutator_bound_explicit D eval₁ eval₂ G₁ G₂ A ψ δ hA h₁ h₂)) ?_
      have h := _root_.MIPStarRE.QPBT.pasting_error_sqrt_le_rpow 32 δ η (by norm_num) hδ hδ1 hη hη1
      have hcoeff : (3 * (32 : ℝ) + 19) = 115 := by norm_num
      rw [hcoeff] at h
      exact h
    · refine le_trans hle1 ?_
      have hb : (0:ℝ) ≤ δ ^ (1/8 : ℝ) := Real.rpow_nonneg hδ _
      have ha : (1:ℝ) ≤ η ^ (1/4 : ℝ) := by
        calc (1:ℝ) = (1:ℝ) ^ (1/4 : ℝ) := (Real.one_rpow _).symm
          _ ≤ η ^ (1/4 : ℝ) :=
            Real.rpow_le_rpow zero_le_one hηgt.le (by norm_num)
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 115 by norm_num) hb]
  · refine le_trans hle1 ?_
    have ha : (0:ℝ) ≤ η ^ (1/4 : ℝ) := Real.rpow_nonneg hη _
    have hb : (1:ℝ) ≤ δ ^ (1/8 : ℝ) := by
      calc (1:ℝ) = (1:ℝ) ^ (1/8 : ℝ) := (Real.one_rpow _).symm
        _ ≤ δ ^ (1/8 : ℝ) :=
          Real.rpow_le_rpow zero_le_one hδgt.le (by norm_num)
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 115 by norm_num) ha]
