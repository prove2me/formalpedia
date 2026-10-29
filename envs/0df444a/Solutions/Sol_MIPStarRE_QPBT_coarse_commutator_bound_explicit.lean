-- Prove2me | solution 1 for MIPStarRE.QPBT.coarse_commutator_bound_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:42:40.084536+00:00
-- url     : https://prove2.me/submissions/a6f2e819-090a-451d-8958-36454a17ffa5

-- Generated proof for MIPStarRE.QPBT.coarse_commutator_bound_explicit.
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
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Defs
import Theorems.Thm_MIPStarRE_QPBT_opFamilyDistSq_le_two_mul_consistencyDefect
import Theorems.Thm_MIPStarRE_QPBT_op_dist_sq_commutator_right_le_explicit

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
namespace MIPStarRE.QPBT.SandwichProduct
end MIPStarRE.QPBT.SandwichProduct

/- Source helpers from QPBT/Games/DistanceTheorems/TensorSupport.lean. -/
/-!
# Tensor-placement and marginal identities

This module collects tensor-placement, marginal, and finite-fiber identities
used in data processing and the commutator estimate.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-461`
- Blueprint `fact:triangle-for-simeq`, `fact:data-processing`, and
  `lem:commutation-analysis`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective



























/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: reindexing an operator family along an equivalence preserves its
distance. -/
theorem opFamilyDistSq_reindex {X α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (e : α ≃ β) (A B : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ A B ψ =
      _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x b => A x (e.symm b))
        (fun x b => B x (e.symm b)) ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq _root_.LIDT.MIPStarRE.LDT.avgOver
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  exact Fintype.sum_equiv e
    (fun a => ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ‖ ^ 2)
    (fun b => ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A x (e.symm b) - B x (e.symm b)) ψ‖ ^ 2)
    (by intro a; simp)

/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: pointwise equal operator families have equal state-dependent
distance. -/
theorem opFamilyDistSq_congr {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B A' B' : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι)
    (hA : ∀ x a, A x a = A' x a) (hB : ∀ x a, B x a = B' x a) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ A B ψ = _root_.MIPStarRE.QPBT.opFamilyDistSq μ A' B' ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq _root_.LIDT.MIPStarRE.LDT.avgOver
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [hA x a, hB x a]







end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/Sandwich/Defs.lean. -/
/-! # Definitions for sandwiched measurements

This module defines the palindromic operator products and the conditional
collision predicate used by the sandwich and pasting lemmas.

## References

Blueprint `lem:ld-sandwich` and `lem:pasting`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-525`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open DistanceCalculus












/-! ### Tensor placements of measurements

The operator families compared in `lem:pasting` are placed on one factor of a
bipartite space. The two constructions below present such a placed family as a
measurement, so that the consistency calculus applies to it verbatim. -/






















/-- Relabelling the outcome set preserves projectivity. Formalization support
for `lem:pasting`, blueprint `ch12_qpbt_games.tex:960-990`. -/
theorem Measurement.isProjective_congrAlphabet {α β ι : Type*} [Fintype α]
    [Fintype β] [Fintype ι] [DecidableEq ι] (e : β ≃ α) (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι)
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (_root_.MIPStarRE.QPBT.Measurement.congrAlphabet e M) :=
  fun b => hM (e b)

/-- Postprocessing a relabelled measurement is the postprocessing of the
original measurement along the transported map. Formalization support for
`lem:pasting`, blueprint `ch12_qpbt_games.tex:960-990`. -/
theorem Measurement.postprocess_congrAlphabet {α β γ ι : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    [Fintype ι] [DecidableEq ι] (e : β ≃ α) (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι)
    (f : β → γ) (c : γ) :
    ((_root_.MIPStarRE.QPBT.Measurement.congrAlphabet e M).postprocess f).effect c =
      (M.postprocess (fun a => f (e.symm a))).effect c := by
  classical
  simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, _root_.MIPStarRE.QPBT.Measurement.congrAlphabet_effect,
    Finset.sum_filter]
  rw [← Equiv.sum_comp e (fun a => if f (e.symm a) = c then M.effect a else 0)]
  simp

end MIPStarRE.QPBT

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

theorem solution :
    ∀ {X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ι : Type*}
        [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
        [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
        [Fintype R₂] [DecidableEq R₂] [Fintype Γ₁] [DecidableEq Γ₁]
        [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]
        (D : _root_.LIDT.MIPStarRE.LDT.Distribution ((X × Y₁) × Y₂))
        (eval₁ : Γ₁ → Y₁ → R₁) (eval₂ : Γ₂ → Y₂ → R₂)
        (G₁ : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Γ₁ ι) (G₂ : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Γ₂ ι)
        (A : ((X × Y₁) × Y₂) → _root_.LIDT.MIPStarRE.Quantum.Measurement (R₁ × R₂) ι)
        (ψ : EuclideanSpace ℂ (ι × ι)) (δ : ℝ),
        (∀ q, _root_.MIPStarRE.QPBT.Measurement.IsProjective (A q)) →
        _root_.MIPStarRE.QPBT.consistencyDefect D
          (fun q a₁ => _root_.MIPStarRE.QPBT.heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
          (fun q a₁ => _root_.MIPStarRE.QPBT.heteroKron 1 (((G₁ q.1.1).postprocess
            (fun g => eval₁ g q.1.2)).effect a₁)) ψ ≤ δ →
        _root_.MIPStarRE.QPBT.consistencyDefect D
          (fun q a₂ => _root_.MIPStarRE.QPBT.heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
          (fun q a₂ => _root_.MIPStarRE.QPBT.heteroKron 1 (((G₂ q.1.1).postprocess
            (fun g => eval₂ g q.2)).effect a₂)) ψ ≤ δ →
        _root_.MIPStarRE.QPBT.opFamilyDistSq D
          (fun q (a : R₁ × R₂) => _root_.MIPStarRE.QPBT.heteroKron 1
            (((G₁ q.1.1).postprocess (fun g => eval₁ g q.1.2)).effect a.1 *
                ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)).effect a.2 -
              ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)).effect a.2 *
                ((G₁ q.1.1).postprocess (fun g => eval₁ g q.1.2)).effect a.1))
          (fun _ _ => 0) ψ ≤ 32 * δ := by
  classical
  intro X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ι _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    D eval₁ eval₂ G₁ G₂ A ψ δ hA h₁ h₂
  set P : ((X × Y₁) × Y₂) → _root_.LIDT.MIPStarRE.Quantum.Measurement R₁ ι :=
    fun q => (G₁ q.1.1).postprocess (fun g => eval₁ g q.1.2) with hPdef
  set Q : ((X × Y₁) × Y₂) → _root_.LIDT.MIPStarRE.Quantum.Measurement R₂ ι :=
    fun q => (G₂ q.1.1).postprocess (fun g => eval₂ g q.2) with hQdef
  let f₁ : R₁ ≃ (Unit × R₁) :=
    ⟨fun a => ((), a), fun p => p.2, fun _ => rfl, by rintro ⟨⟨⟩, a⟩; rfl⟩
  let f₂ : R₂ ≃ (Unit × R₂) :=
    ⟨fun a => ((), a), fun p => p.2, fun _ => rfl, by rintro ⟨⟨⟩, a⟩; rfl⟩
  let eB : ((Unit × R₁) × R₂) ≃ (R₁ × R₂) :=
    ⟨fun p => (p.1.2, p.2), fun a => (((), a.1), a.2),
      by rintro ⟨⟨⟨⟩, a⟩, b⟩; rfl, fun _ => rfl⟩
  let AR : ((X × Y₁) × Y₂) → _root_.LIDT.MIPStarRE.Quantum.Measurement (Unit × R₁) ι :=
    fun q => _root_.MIPStarRE.QPBT.Measurement.congrAlphabet f₁.symm (P q)
  let DR : ((X × Y₁) × Y₂) → _root_.LIDT.MIPStarRE.Quantum.Measurement (Unit × R₂) ι :=
    fun q => _root_.MIPStarRE.QPBT.Measurement.congrAlphabet f₂.symm (Q q)
  let BJ : ((X × Y₁) × Y₂) → _root_.LIDT.MIPStarRE.Quantum.Measurement ((Unit × R₁) × R₂) ι :=
    fun q => _root_.MIPStarRE.QPBT.Measurement.congrAlphabet eB (A q)
  have hBJ : ∀ q, _root_.MIPStarRE.QPBT.Measurement.IsProjective (BJ q) :=
    fun q => _root_.MIPStarRE.QPBT.Measurement.isProjective_congrAlphabet eB (A q) (hA q)
  have hd₁ : _root_.MIPStarRE.QPBT.opFamilyDistSq D
      (fun q a₁ => _root_.MIPStarRE.QPBT.heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
      (fun q a₁ => _root_.MIPStarRE.QPBT.heteroKron 1 ((P q).effect a₁)) ψ ≤ 2 * δ := by
    refine le_trans (_root_.MIPStarRE.QPBT.opFamilyDistSq_le_two_mul_consistencyDefect D
      (fun q => _root_.MIPStarRE.QPBT.Measurement.leftPlacement ((A q).postprocess Prod.fst))
      (fun q => _root_.MIPStarRE.QPBT.Measurement.rightPlacement (P q)) ψ) ?_
    simp only [_root_.MIPStarRE.QPBT.Measurement.leftPlacement_effect,
      _root_.MIPStarRE.QPBT.Measurement.rightPlacement_effect]
    linarith [h₁]
  have hd₂ : _root_.MIPStarRE.QPBT.opFamilyDistSq D
      (fun q a₂ => _root_.MIPStarRE.QPBT.heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
      (fun q a₂ => _root_.MIPStarRE.QPBT.heteroKron 1 ((Q q).effect a₂)) ψ ≤ 2 * δ := by
    refine le_trans (_root_.MIPStarRE.QPBT.opFamilyDistSq_le_two_mul_consistencyDefect D
      (fun q => _root_.MIPStarRE.QPBT.Measurement.leftPlacement ((A q).postprocess Prod.snd))
      (fun q => _root_.MIPStarRE.QPBT.Measurement.rightPlacement (Q q)) ψ) ?_
    simp only [_root_.MIPStarRE.QPBT.Measurement.leftPlacement_effect,
      _root_.MIPStarRE.QPBT.Measurement.rightPlacement_effect]
    linarith [h₂]
  have hBA : _root_.MIPStarRE.QPBT.opFamilyDistSq D
      (fun q ab => _root_.MIPStarRE.QPBT.heteroKron
        (((BJ q).postprocess (fun abc => abc.1)).effect ab) 1)
      (fun q ab => _root_.MIPStarRE.QPBT.heteroKron 1 ((AR q).effect ab)) ψ ≤ 2 * δ := by
    refine le_trans (le_of_eq ?_) hd₁
    rw [_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_reindex D f₁
      (fun q a₁ => _root_.MIPStarRE.QPBT.heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
      (fun q a₁ => _root_.MIPStarRE.QPBT.heteroKron 1 ((P q).effect a₁)) ψ]
    refine _root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_congr D _ _ _ _ ψ (fun q ab => ?_) (fun q ab => rfl)
    congr 1
    rw [_root_.MIPStarRE.QPBT.Measurement.postprocess_congrAlphabet]
    simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
    refine Finset.sum_congr (Finset.filter_congr fun a _ => ?_) fun _ _ => rfl
    simp [eB, f₁, Prod.ext_iff]
  have hBD : _root_.MIPStarRE.QPBT.opFamilyDistSq D
      (fun q ac => _root_.MIPStarRE.QPBT.heteroKron
        (((BJ q).postprocess (fun abc => (abc.1.1, abc.2))).effect ac) 1)
      (fun q ac => _root_.MIPStarRE.QPBT.heteroKron 1 ((DR q).effect ac)) ψ ≤ 2 * δ := by
    refine le_trans (le_of_eq ?_) hd₂
    rw [_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_reindex D f₂
      (fun q a₂ => _root_.MIPStarRE.QPBT.heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
      (fun q a₂ => _root_.MIPStarRE.QPBT.heteroKron 1 ((Q q).effect a₂)) ψ]
    refine _root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_congr D _ _ _ _ ψ (fun q ac => ?_) (fun q ac => rfl)
    congr 1
    rw [_root_.MIPStarRE.QPBT.Measurement.postprocess_congrAlphabet]
    simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
    refine Finset.sum_congr (Finset.filter_congr fun a _ => ?_) fun _ _ => rfl
    simp [eB, f₂, Prod.ext_iff]
  have hconc := _root_.MIPStarRE.QPBT.op_dist_sq_commutator_right_le_explicit
    D AR BJ DR ψ (2 * δ) hBJ hBA hBD
  rw [_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_reindex D eB _ _ ψ] at hconc
  refine le_trans (le_of_eq ?_) (le_trans hconc (le_of_eq (by ring)))
  exact _root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_congr D _ _ _ _ ψ (fun q a => rfl) (fun q a => rfl)
