-- Prove2me | solution 1 for MIPStarRE.QPBT.consistencyDefect_pasted_le_sqrt_one_sided
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:59:25.69184+00:00
-- url     : https://prove2.me/submissions/68fd56b1-e3e8-48ac-ad25-d3c6a3a894f4

-- Generated proof for MIPStarRE.QPBT.consistencyDefect_pasted_le_sqrt_one_sided.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Defs
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Pasting_SchmidtMirror
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Theorems.Thm_MIPStarRE_QPBT_commutator_mass_fine_le_distinct_families
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_codeword_fine_le_coarse_add_distinct_families
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_pasted_le_marginal_add_pinched
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_pinched_le_marginal_add_sqrt
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_schmidtMirror_le
import Theorems.Thm_MIPStarRE_QPBT_mass_ordered_product_ge
import Theorems.Thm_MIPStarRE_QPBT_opFamilyDistSq_le_two_mul_consistencyDefect

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/DistanceTheorems/Support.lean. -/
/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

























































































/-- Formalization-only auxiliary lemma for Proposition 4.29: state-dependent
operator-family distance is symmetric. -/
theorem opFamilyDistSq_symm {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ A B ψ = _root_.MIPStarRE.QPBT.opFamilyDistSq μ B A ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  simp only [_root_.MIPStarRE.QPBT.applyOperatorToState, map_sub, LinearMap.sub_apply]
  rw [norm_sub_rev]

end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/Sandwich/Pasting/SchmidtMirror.lean. -/
/-! # State-dependent Schmidt mirrors

This module constructs the opposite-register mirror used in the one-sided
pasting argument. The auxiliary construction uses the spectral theorem and
orthonormal completion, including zero Schmidt coefficients.

## References

`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`, `lem:pasting`;
`docs/paper-gaps/qpbt_pasting-product-error.tex`, issue Dengnifer/MIPStarRE-QPBT-bak#201. The
Schmidt-mirror
argument is a formalization auxiliary, not an additional paper hypothesis.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective











variable {ι : Type*} [Fintype ι] [DecidableEq ι]

























/-- Mirroring commutes with coarse-graining along any evaluation map. -/
theorem schmidtMirrorMeasurement_postprocess {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (ψ : EuclideanSpace ℂ (ι × ι))
    (measurement : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (evaluation : α → β) (answer : β) :
    ((_root_.MIPStarRE.QPBT.schmidtMirrorMeasurement ψ measurement).postprocess evaluation).effect answer =
      _root_.MIPStarRE.QPBT.schmidtMirror ψ ((measurement.postprocess evaluation).effect answer) := by
  change (∑ original ∈ Finset.univ.filter (fun original => evaluation original = answer),
      _root_.MIPStarRE.QPBT.schmidtMirror ψ (measurement.effect original)) =
    _root_.MIPStarRE.QPBT.schmidtMirror ψ (∑ original ∈ Finset.univ.filter
      (fun original => evaluation original = answer), measurement.effect original)
  rw [map_sum]



end MIPStarRE.QPBT

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

theorem solution {X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
    [Fintype R₂] [DecidableEq R₂] [Fintype Γ₁] [DecidableEq Γ₁]
    [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]
    (D : _root_.LIDT.MIPStarRE.LDT.Distribution ((X × Y₁) × Y₂))
    (eval₁ : Γ₁ → Y₁ → R₁) (eval₂ : Γ₂ → Y₂ → R₂)
    (G₁ : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Γ₁ ι) (G₂ : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Γ₂ ι)
    (A : ((X × Y₁) × Y₂) → _root_.LIDT.MIPStarRE.Quantum.Measurement (R₁ × R₂) ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (η δ C : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1) (hη : 0 ≤ η)
    (hG₂ : ∀ x, _root_.MIPStarRE.QPBT.Measurement.IsProjective (G₂ x))
    (hA : ∀ q, _root_.MIPStarRE.QPBT.Measurement.IsProjective (A q))
    (hcoll : ∀ x y₁, 0 < (D.map Prod.fst).weight (x, y₁) →
      ∀ g g' : Γ₂, g ≠ g' →
        (∑ y₂ : Y₂, D.weight ((x, y₁), y₂) *
          if eval₂ g y₂ = eval₂ g' y₂ then 1 else 0) ≤
          η * (D.map Prod.fst).weight (x, y₁))
    (h₁ : _root_.MIPStarRE.QPBT.consistencyDefect D
      (fun q a₁ => _root_.MIPStarRE.QPBT.heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
      (fun q a₁ => _root_.MIPStarRE.QPBT.heteroKron 1 (((G₁ q.1.1).postprocess
        (fun g => eval₁ g q.1.2)).effect a₁)) ψ ≤ δ)
    (h₂ : _root_.MIPStarRE.QPBT.consistencyDefect D
      (fun q a₂ => _root_.MIPStarRE.QPBT.heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
      (fun q a₂ => _root_.MIPStarRE.QPBT.heteroKron 1 (((G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect a₂)) ψ ≤ δ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hK₀ : _root_.MIPStarRE.QPBT.opFamilyDistSq D (fun q (ab : R₁ × R₂) => _root_.MIPStarRE.QPBT.heteroKron 1
      (((G₁ q.1.1).postprocess (fun g => eval₁ g q.1.2)).effect ab.1 *
          ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)).effect ab.2 -
        ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)).effect ab.2 *
          ((G₁ q.1.1).postprocess (fun g => eval₁ g q.1.2)).effect ab.1))
      (fun _ _ => 0) ψ ≤ C * δ) :
    _root_.MIPStarRE.QPBT.consistencyDefect D (fun q a => _root_.MIPStarRE.QPBT.heteroKron ((A q).effect a) 1)
        (fun q a => _root_.MIPStarRE.QPBT.heteroKron 1 (∑ g₁ : Γ₁, ∑ g₂ : Γ₂,
          if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
            _root_.MIPStarRE.QPBT.pastedMeasurement (fun g => (G₁ q.1.1).effect g)
              (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0)) ψ ≤
      2 * δ + Real.sqrt (C * δ +
        (2 * Real.sqrt (2 * δ) + 2 * δ + 2 * Real.sqrt (C * δ) + C * δ) + 2 * η +
        2 * Real.sqrt (2 * ((δ + 2 * Real.sqrt (2 * δ)) + η)) +
        2 * Real.sqrt (2 * (δ + 2 * Real.sqrt (2 * δ)))) := by
  classical
  set P : (X × Y₁) → _root_.LIDT.MIPStarRE.Quantum.Measurement R₁ ι :=
    fun p => (G₁ p.1).postprocess (fun g => eval₁ g p.2) with hPd
  set Ac : ((X × Y₁) × Y₂) → _root_.LIDT.MIPStarRE.Quantum.Measurement R₁ ι :=
    fun q => (A q).postprocess Prod.fst with hAcd
  have hAcproj : ∀ q, _root_.MIPStarRE.QPBT.Measurement.IsProjective (Ac q) := fun q =>
    _root_.MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective (A q) (hA q) Prod.fst
  have hQproj : ∀ q : (X × Y₁) × Y₂, _root_.MIPStarRE.QPBT.Measurement.IsProjective
      ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)) := fun q =>
    _root_.MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective (G₂ q.1.1) (hG₂ q.1.1) _
  let opposite : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Γ₂ ι := fun question =>
    _root_.MIPStarRE.QPBT.schmidtMirrorMeasurement ψ (G₂ question)
  have hbudget : 2 * δ ≤ δ + 2 * Real.sqrt (2 * δ) := by
    have hs := Real.sq_sqrt (show 0 ≤ 2 * δ by positivity)
    have hn := Real.sqrt_nonneg (2 * δ)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδ1)]
  have hεc : _root_.MIPStarRE.QPBT.consistencyDefect D
      (fun q answer => _root_.MIPStarRE.QPBT.heteroKron (((opposite q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect answer) 1)
      (fun q answer => _root_.MIPStarRE.QPBT.heteroKron 1 (((G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect answer)) ψ ≤ δ + 2 * Real.sqrt (2 * δ) := by
    have hmirror := _root_.MIPStarRE.QPBT.consistencyDefect_schmidtMirror_le D
      (fun q => (A q).postprocess Prod.snd)
      (fun q => (G₂ q.1.1).postprocess (fun g => eval₂ g q.2)) ψ hQproj
    simp only [_root_.MIPStarRE.QPBT.schmidtMirrorMeasurement, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne] at hmirror
    simp only [opposite, _root_.MIPStarRE.QPBT.schmidtMirrorMeasurement_postprocess]
    linarith [hmirror, h₂]
  have hεf : _root_.MIPStarRE.QPBT.consistencyDefect D
      (fun q g => _root_.MIPStarRE.QPBT.heteroKron ((opposite q.1.1).effect g) 1)
      (fun q g => _root_.MIPStarRE.QPBT.heteroKron 1 ((G₂ q.1.1).effect g)) ψ ≤
      (δ + 2 * Real.sqrt (2 * δ)) + η := by
    refine le_trans (_root_.MIPStarRE.QPBT.consistencyDefect_codeword_fine_le_coarse_add_distinct_families
      D eval₂ G₂ opposite ψ η
      hD hψ hη hcoll) ?_
    linarith [hεc]
  have hglf : _root_.MIPStarRE.QPBT.opFamilyDistSq D (fun q g => _root_.MIPStarRE.QPBT.heteroKron 1 ((G₂ q.1.1).effect g))
      (fun q g => _root_.MIPStarRE.QPBT.heteroKron ((opposite q.1.1).effect g) 1) ψ ≤
      2 * ((δ + 2 * Real.sqrt (2 * δ)) + η) := by
    rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_symm]
    refine le_trans (_root_.MIPStarRE.QPBT.opFamilyDistSq_le_two_mul_consistencyDefect D
      (fun q => _root_.MIPStarRE.QPBT.Measurement.leftPlacement (ιB := ι) (opposite q.1.1))
      (fun q => _root_.MIPStarRE.QPBT.Measurement.rightPlacement (ιA := ι) (G₂ q.1.1)) ψ) ?_
    simp only [_root_.MIPStarRE.QPBT.Measurement.leftPlacement_effect, _root_.MIPStarRE.QPBT.Measurement.rightPlacement_effect]
    linarith [hεf]
  have hglc : _root_.MIPStarRE.QPBT.opFamilyDistSq D
      (fun q b => _root_.MIPStarRE.QPBT.heteroKron 1 (((G₂ q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect b))
      (fun q b => _root_.MIPStarRE.QPBT.heteroKron (((opposite q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect b) 1) ψ ≤
      2 * (δ + 2 * Real.sqrt (2 * δ)) := by
    rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_symm]
    refine le_trans (_root_.MIPStarRE.QPBT.opFamilyDistSq_le_two_mul_consistencyDefect D
      (fun q => _root_.MIPStarRE.QPBT.Measurement.leftPlacement (ιB := ι)
        ((opposite q.1.1).postprocess (fun g => eval₂ g q.2)))
      (fun q => _root_.MIPStarRE.QPBT.Measurement.rightPlacement (ιA := ι)
        ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2))) ψ) ?_
    simp only [_root_.MIPStarRE.QPBT.Measurement.leftPlacement_effect, _root_.MIPStarRE.QPBT.Measurement.rightPlacement_effect]
    linarith [hεc]
  have hd : _root_.MIPStarRE.QPBT.opFamilyDistSq D (fun q a => _root_.MIPStarRE.QPBT.heteroKron ((Ac q).effect a) 1)
      (fun q a => _root_.MIPStarRE.QPBT.heteroKron 1 ((P q.1).effect a)) ψ ≤ 2 * δ := by
    refine le_trans (_root_.MIPStarRE.QPBT.opFamilyDistSq_le_two_mul_consistencyDefect D
      (fun q => _root_.MIPStarRE.QPBT.Measurement.leftPlacement (ιB := ι) (Ac q))
      (fun q => _root_.MIPStarRE.QPBT.Measurement.rightPlacement (ιA := ι) (P q.1)) ψ) ?_
    simp only [_root_.MIPStarRE.QPBT.Measurement.leftPlacement_effect, _root_.MIPStarRE.QPBT.Measurement.rightPlacement_effect]
    linarith [h₁]
  have hmass := _root_.MIPStarRE.QPBT.mass_ordered_product_ge D Ac (fun q => P q.1)
    (fun q => (G₂ q.1.1).postprocess (fun g => eval₂ g q.2)) ψ (2 * δ) (C * δ)
    hD hψ hAcproj hQproj hd hK₀
  have hKfine := _root_.MIPStarRE.QPBT.commutator_mass_fine_le_distinct_families D eval₂ G₂ opposite P ψ η (C * δ)
    (2 * Real.sqrt (2 * δ) + 2 * δ + 2 * Real.sqrt (C * δ) + C * δ)
    (2 * (δ + 2 * Real.sqrt (2 * δ)))
    (2 * ((δ + 2 * Real.sqrt (2 * δ)) + η))
    hD hψ hη hG₂ hcoll hK₀ (by linarith [hmass]) hglc hglf
  have hpinch := _root_.MIPStarRE.QPBT.consistencyDefect_pinched_le_marginal_add_sqrt D G₂
    (fun q => P q.1) Ac ψ (C * δ +
      (2 * Real.sqrt (2 * δ) + 2 * δ + 2 * Real.sqrt (C * δ) + C * δ) + 2 * η +
      2 * Real.sqrt (2 * ((δ + 2 * Real.sqrt (2 * δ)) + η)) +
      2 * Real.sqrt (2 * (δ + 2 * Real.sqrt (2 * δ))))
    hD hψ hAcproj hG₂ hKfine
  have hpaste := _root_.MIPStarRE.QPBT.consistencyDefect_pasted_le_marginal_add_pinched D eval₁ eval₂
    G₁ G₂ A ψ hψ hG₂
  linarith [hpaste, hpinch, h₁, h₂]
