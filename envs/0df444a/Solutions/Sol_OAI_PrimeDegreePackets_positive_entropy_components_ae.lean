-- Prove2me | solution 1 for OAI.PrimeDegreePackets.positive_entropy_components_ae
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:46:13.849752+00:00
-- url     : https://prove2.me/submissions/5bffb44b-2f63-4709-8372-5a1f21175fd0

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke023
import Definitions.Def_OAIQ244Duke024

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketMoments
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace

open Filter Set Topology

open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
namespace PrimeDegreePackets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma matrixBall_isOpen (n : ℕ) (r : ℝ) : IsOpen (matrixBall n r) := by
  simp only [matrixBall, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_lt _ continuous_const
  exact ((continuous_apply j).comp ((continuous_apply i).comp Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous)).sub
    continuous_const |>.abs

lemma right_ball_isOpen {n : ℕ} (x : X n) (r : ℝ) :
    IsOpen ((fun h => rightAction x h) '' matrixBall n r) := by
  induction x using Quotient.inductionOn with
  | h g =>
    change IsOpen ((fun h => Quotient.mk _ (g*h)) '' matrixBall n r)
    rw [← Set.image_image]
    exact (quotient_covering n).isOpenMap _
      ((Homeomorph.mulLeft g).isOpenMap _ (matrixBall_isOpen n r))



open scoped Matrix
open Matrix

open TopologicalSpace
open scoped Topology

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealNorms
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix

open MeasureTheory Filter Set Module TopologicalSpace
namespace PrimeDegreePackets

lemma tube_entries {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    {b t : ℝ} {h : G n} (hh : h ∈ twoSidedTube ell hell b t) :
    (∀ i, |h.1 i i - 1| < b) ∧
      ∀ i j, i ≠ j → |h.1 i j| < b * Real.exp (-|(ell i - ell j) * t|) := by
  constructor
  · intro i
    have H := hh.2 i i
    simpa only [conjugation_entry,sub_self,zero_mul,Real.exp_zero,one_mul,
      Matrix.one_apply_eq] using H
  · intro i j hij
    have Hplus := hh.2 i j
    have Hminus := hh.1 i j
    have he := conjugation_entry ell hell h (-t) i j
    simp only [neg_neg] at he
    rw [he] at Hminus
    simp only [conjugation_entry,Matrix.one_apply_ne hij,sub_zero,abs_mul,
      abs_of_pos (Real.exp_pos _)] at Hplus Hminus
    by_cases hd : 0 ≤ (ell i - ell j) * t
    · rw [abs_of_nonneg hd]
      have H : |h.1 i j| < b / Real.exp ((ell i - ell j)*t) :=
        (lt_div_iff₀ (Real.exp_pos ((ell i - ell j)*t))).mpr (by
          simpa only [mul_comm] using Hplus)
      simpa only [Real.exp_neg,div_eq_mul_inv] using H
    · rw [abs_of_nonpos (le_of_not_ge hd),neg_neg]
      have H : |h.1 i j| < b / Real.exp ((ell i - ell j)*(-t)) :=
        (lt_div_iff₀ (Real.exp_pos ((ell i - ell j)*(-t)))).mpr (by
          simpa only [mul_comm] using Hminus)
      simpa only [mul_neg,Real.exp_neg,inv_inv,div_eq_mul_inv] using H

lemma tube_entries_uniform {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    {b t δ : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hδ : ∀ i j, i ≠ j → δ ≤ |ell i - ell j|)
    {h : G n} (hh : h ∈ twoSidedTube ell hell b t) :
    (∀ i, |h.1 i i - 1| < b) ∧
      ∀ i j, i ≠ j → |h.1 i j| < b * Real.exp (-δ*t) := by
  refine ⟨(tube_entries ell hell hh).1, ?_⟩
  intro i j hij
  apply ((tube_entries ell hell hh).2 i j hij).trans_le
  apply mul_le_mul_of_nonneg_left _ hb
  apply Real.exp_le_exp.mpr
  rw [abs_mul,abs_of_nonneg ht]
  nlinarith [mul_le_mul_of_nonneg_right (hδ i j hij) ht]

 

lemma exists_two_moved {α : Type*} (σ : Equiv.Perm α) (hσ : σ ≠ 1) :
    ∃ i j, i ≠ j ∧ σ i ≠ i ∧ σ j ≠ j := by
  obtain ⟨i,hi⟩ : ∃ i, σ i ≠ i := by
    by_contra! H
    apply hσ
    exact Equiv.ext H
  refine ⟨i,σ i,Ne.symm hi,hi,?_⟩
  intro he
  exact hi (σ.injective he)

 

lemma product_two_small {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) {r : ℝ} (hr : 0 ≤ r) (hf : ∀ i, |f i| ≤ 2)
    {i j : α} (hij : i ≠ j) (hi : |f i| ≤ r) (hj : |f j| ≤ r) :
    |∏ k, f k| ≤ r^2 * 2^(Fintype.card α) := by
  classical
  have hi' : i ∈ (Finset.univ : Finset α) := Finset.mem_univ i
  have hj' : j ∈ (Finset.univ.erase i : Finset α) := by simp [hij.symm]
  rw [←Finset.mul_prod_erase _ _ hi', ←Finset.mul_prod_erase _ _ hj',
    abs_mul,abs_mul]
  have HT : |∏ k ∈ (Finset.univ.erase i).erase j, f k| ≤
      2^((Finset.univ.erase i).erase j).card := by
    rw [Finset.abs_prod]
    simpa only [Finset.prod_const] using Finset.prod_le_prod
      (fun k _ => abs_nonneg (f k)) (fun k _ => hf k)
  have HC : ((Finset.univ.erase i).erase j).card ≤ Fintype.card α := by
    exact Finset.card_le_card (by simp)
  have HP : (2:ℝ)^((Finset.univ.erase i).erase j).card ≤ 2^(Fintype.card α) :=
    pow_le_pow_right₀ (by norm_num) HC
  calc
    _ ≤ r * (r * 2^((Finset.univ.erase i).erase j).card) :=
      mul_le_mul hi (mul_le_mul hj HT (abs_nonneg _) hr) (by positivity) hr
    _ ≤ r^2 * 2^(Fintype.card α) := by
      nlinarith [mul_le_mul_of_nonneg_left HP (sq_nonneg r)]

 

lemma determinant_diagonal_error {n : ℕ} {h : G n} {r : ℝ}
    (hr : 0 ≤ r)
    (hall : ∀ i j, |h.1 i j| ≤ 2)
    (hoff : ∀ i j, i ≠ j → |h.1 i j| ≤ r) :
    |(∏i, h.1 i i) - 1| ≤ (Nat.factorial n : ℝ) * 2^n * r^2 := by
  classical
  have Hterm (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) :
      |Equiv.Perm.sign σ * ∏i, h.1 (σ i) i| ≤ r^2 * 2^n := by
    obtain ⟨i,j,hij,hi,hj⟩ := exists_two_moved σ hσ
    rw [abs_mul]
    have hs : |(Equiv.Perm.sign σ : ℝ)| = 1 := by
      rw [←Int.cast_abs, Int.abs_eq_natAbs, Int.units_natAbs]
      norm_num
    rw [hs,one_mul]
    simpa using product_two_small (fun k => h.1 (σ k) k) hr
      (fun k => hall (σ k) k) hij (hoff _ _ hi) (hoff _ _ hj)
  have Hdet : (1:ℝ) = (∏ i, h.1 i i) +
      ∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin n)),
        Equiv.Perm.sign σ * ∏i, h.1 (σ i) i := by
    calc
      1 = Matrix.det h.1 := h.2.symm
      _ = _ := by
        rw [Matrix.det_apply']
        rw [←Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin n)))]
        simp
  have HE : (∏i, h.1 i i) - 1 =
      -(∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin n)),
        Equiv.Perm.sign σ * ∏i, h.1 (σ i) i) := by linarith
  rw [HE,abs_neg]
  calc
    _ ≤ ∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin n)),
        |Equiv.Perm.sign σ * ∏i, h.1 (σ i) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin n)), r^2 * 2^n := by
      exact Finset.sum_le_sum (fun σ hσ => Hterm σ (Finset.ne_of_mem_erase hσ))
    _ ≤ (Nat.factorial n : ℝ) * 2^n * r^2 := by
      rw [Finset.sum_const,nsmul_eq_mul]
      have HC : (Finset.univ.erase (1 : Equiv.Perm (Fin n))).card ≤ Nat.factorial n := by
        calc
          _ ≤ (Finset.univ : Finset (Equiv.Perm (Fin n))).card :=
            Finset.card_le_card (Finset.erase_subset _ _)
          _ = _ := by rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
      have HC' : ((Finset.univ.erase (1 : Equiv.Perm (Fin n))).card : ℝ) ≤ Nat.factorial n :=
        Nat.cast_le.mpr HC
      nlinarith [mul_le_mul_of_nonneg_right HC' (by positivity : 0 ≤ r^2 * (2:ℝ)^n)]

 

lemma diagonalFlow_neg_log_val {d : ℕ} (h : G (d+1))
    (hd : ∀ i, 0 < h.1 i i) :
    (diagonalFlow (fun i : Fin d => -Real.log (h.1 i.castSucc i.castSucc))).1 =
      Matrix.diagonal (Fin.snoc (α := fun _ => ℝ) (fun i : Fin d => (h.1 i.castSucc i.castSucc)⁻¹)
        (∏ i : Fin d, h.1 i.castSucc i.castSucc)) := by
  change Matrix.diagonal _ = Matrix.diagonal _
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, Finset.sum_neg_distrib,neg_neg,Real.exp_sum]
    exact Finset.prod_congr rfl (fun i _ => Real.exp_log (hd i.castSucc))
  · simp only [Fin.snoc_castSucc,Real.exp_neg,Real.exp_log (hd j.castSucc)]

lemma normalizing_scalars_le {d : ℕ} (h : G (d+1))
    (hd : ∀ i, (1:ℝ)/2 ≤ h.1 i i ∧ h.1 i i ≤ 2) (i : Fin (d+1)) :
    (0:ℝ) < Fin.snoc (α := fun _ => ℝ) (fun i : Fin d => (h.1 i.castSucc i.castSucc)⁻¹)
      (∏ i : Fin d, h.1 i.castSucc i.castSucc) i ∧
    Fin.snoc (α := fun _ => ℝ) (fun i : Fin d => (h.1 i.castSucc i.castSucc)⁻¹)
      (∏ i : Fin d, h.1 i.castSucc i.castSucc) i ≤ (2:ℝ) + 2^d := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    constructor
    · exact Finset.prod_pos (fun j _ => lt_of_lt_of_le (by norm_num) (hd j.castSucc).1)
    · have H : (∏j : Fin d, h.1 j.castSucc j.castSucc) ≤ (2:ℝ)^d := by
        simpa using Finset.prod_le_prod (s := Finset.univ)
          (fun (j : Fin d) _ => (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (hd j.castSucc).1).le)
          (fun (j : Fin d) _ => (hd j.castSucc).2)
      linarith
  · simp only [Fin.snoc_castSucc]
    have hp : 0 < h.1 j.castSucc j.castSucc := lt_of_lt_of_le (by norm_num) (hd j.castSucc).1
    refine ⟨inv_pos.mpr hp, ?_⟩
    have H : (h.1 j.castSucc j.castSucc)⁻¹ ≤ 2 := by
      exact (inv_le_comm₀ hp (by norm_num)).mpr (by simpa using (hd j.castSucc).1)
    linarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) d]

 

lemma normalized_matrix_entry_bound {d : ℕ} (h : G (d+1)) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hd : ∀ i, (1:ℝ)/2 ≤ h.1 i i ∧ h.1 i i ≤ 2)
    (hoff : ∀ i j, i ≠ j → |h.1 i j| ≤ r) (i j : Fin (d+1)) :
    |(diagonalFlow (fun i : Fin d => -Real.log (h.1 i.castSucc i.castSucc)) * h).1 i j -
      (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) i j| ≤
      (((d+1).factorial : ℝ)*2^(d+1) + 2 + 2^d) * r := by
  have hp : ∀ i, 0 < h.1 i i := fun i => lt_of_lt_of_le (by norm_num) (hd i).1
  have he : (diagonalFlow (fun i : Fin d => -Real.log (h.1 i.castSucc i.castSucc)) * h).1 =
      Matrix.diagonal (Fin.snoc (α := fun _ => ℝ) (fun i : Fin d => (h.1 i.castSucc i.castSucc)⁻¹)
        (∏ i : Fin d, h.1 i.castSucc i.castSucc)) * h.1 := by
    change (diagonalFlow _).1 * h.1 = _
    rw [diagonalFlow_neg_log_val h hp]
  rw [he,Matrix.diagonal_mul]
  by_cases hij : i = j
  · subst j
    rw [Matrix.one_apply_eq]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      have hall : ∀ i j, |h.1 i j| ≤ 2 := by
        intro i j
        by_cases he : i=j
        · subst j; rw [abs_of_pos (hp i)]; exact (hd i).2
        · exact (hoff i j he).trans (by linarith)
      have HD := determinant_diagonal_error hr hall hoff
      rw [Fin.prod_univ_castSucc] at HD
      have hrr : r^2 ≤ r := by nlinarith
      have HC : (0:ℝ) ≤ ((d+1).factorial : ℝ) * 2^(d+1) := by positivity
      have HE : ((d+1).factorial : ℝ) * 2^(d+1) * r^2 ≤
          (((d+1).factorial : ℝ)*2^(d+1) + 2 + 2^d)*r := by
        nlinarith [mul_le_mul_of_nonneg_left hrr HC,
          mul_nonneg hr (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) d)]
      exact HD.trans HE
    · simp only [Fin.snoc_castSucc,inv_mul_cancel₀ (hp j.castSucc).ne',sub_self,abs_zero]
      positivity
  · rw [Matrix.one_apply_ne hij,sub_zero,abs_mul,abs_of_pos (normalizing_scalars_le h hd i).1]
    have H := mul_le_mul (normalizing_scalars_le h hd i).2 (hoff i j hij)
      (abs_nonneg _) (by positivity : (0:ℝ) ≤ 2+2^d)
    have HC : (0:ℝ) ≤ ((d+1).factorial : ℝ) * 2^(d+1)*r := by positivity
    nlinarith

 

lemma diagonal_log_mem_compact_box {d : ℕ} (h : G (d+1))
    (hd : ∀ i, (1:ℝ)/2 ≤ h.1 i i ∧ h.1 i i ≤ 2) :
    (fun i : Fin d => Real.log (h.1 i.castSucc i.castSucc)) ∈
      Set.pi Set.univ (fun _ => Set.Icc (-Real.log 2) (Real.log 2)) := by
  intro i _
  have hp : 0 < h.1 i.castSucc i.castSucc := lt_of_lt_of_le (by norm_num) (hd i.castSucc).1
  constructor
  · have H := Real.log_le_log (by norm_num : (0:ℝ)<1/2) (hd i.castSucc).1
    simpa only [one_div,Real.log_inv] using H
  · exact Real.log_le_log hp (hd i.castSucc).2

 

theorem cube_grid_cover (d : ℕ) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ s : Finset (Fin d → ℝ),
      (∀ u ∈ s, ∀ i, |u i| ≤ R+1) ∧
      (s.card : ℝ) ≤ (2*R+2)^d / r^d ∧
      ∀ x : Fin d → ℝ, (∀ i, |x i| ≤ R) →
        ∃ u ∈ s, ∀ i, |x i-u i| < r := by
  classical
  let N : ℕ := ⌈2*R/r⌉₊
  let g (k : Fin d → Fin (N+1)) : Fin d → ℝ := fun i => -R + (k i : ℕ)*r
  let s : Finset (Fin d → ℝ) := Finset.univ.image g
  have hN : (N:ℝ) < 2*R/r+1 := by
    exact Nat.ceil_lt_add_one (div_nonneg (by positivity) hr.le)
  have hNr : (N:ℝ)*r < 2*R+r := by
    have := (mul_lt_mul_iff_left₀ hr).mpr hN
    field_simp at this
    nlinarith
  refine ⟨s, ?_, ?_, ?_⟩
  · intro u hu i
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hu
    dsimp [g]
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (k i).val) hr.le]
    · have hki : ((k i).val : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt_succ (k i).isLt)
      nlinarith [mul_le_mul_of_nonneg_right hki hr.le]
  · have hcard : s.card ≤ (N+1)^d := by
      calc
        _ ≤ (Finset.univ : Finset (Fin d → Fin (N+1))).card := Finset.card_image_le
        _ = _ := by simp
    have hN1 : ((N+1:ℕ):ℝ) ≤ (2*R+2)/r := by
      apply (le_div_iff₀ hr).mpr
      push_cast
      nlinarith
    calc
      (s.card:ℝ) ≤ (((N+1)^d:ℕ):ℝ) := Nat.cast_le.mpr hcard
      _ = (((N+1:ℕ):ℝ))^d := Nat.cast_pow _ _
      _ ≤ ((2*R+2)/r)^d := pow_le_pow_left₀ (Nat.cast_nonneg _) hN1 d
      _ = _ := div_pow _ _ _
  · intro x hx
    have hx0 (i : Fin d) : 0 ≤ (x i+R)/r := by
      apply div_nonneg _ hr.le
      have := (abs_le.mp (hx i)).1
      linarith
    let k (i : Fin d) : Fin (N+1) := ⟨⌊(x i+R)/r⌋₊, by
      apply Nat.lt_succ_of_le
      apply (Nat.floor_mono ?_).trans (Nat.floor_le_ceil _)
      apply div_le_div_of_nonneg_right _ hr.le
      have := (abs_le.mp (hx i)).2
      linarith⟩
    refine ⟨g k, Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩, ?_⟩
    intro i
    have hlo := Nat.floor_le (hx0 i)
    have hhi := Nat.lt_floor_add_one ((x i+R)/r)
    have Hlo : (⌊(x i+R)/r⌋₊ : ℝ)*r ≤ x i+R := (le_div_iff₀ hr).mp hlo
    have Hhi : x i+R < ((⌊(x i+R)/r⌋₊ : ℝ)+1)*r := (div_lt_iff₀ hr).mp hhi
    dsimp [g,k]
    rw [abs_of_nonneg (by linarith)]
    linarith

lemma exp_sub_one_abs_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - 1| ≤ 2 * |x| := by
  have H := Real.norm_exp_sub_one_sub_id_le (show ‖x‖ ≤ 1 by simpa using hx)
  simp only [Real.norm_eq_abs] at H
  have He := abs_le.mp H
  have Ha := abs_le.mp (le_refl |x|)
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg x]

lemma diagonalFlow_small_entries {d : ℕ} {u : Fin d → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hu : ∀ i, |u i| ≤ r / (d+1)) (i j : Fin (d+1)) :
    |(diagonalFlow u).1 i j - (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) i j| ≤ 2*r := by
  have hd : (0:ℝ) < d+1 := by positivity
  have hsmall (i : Fin d) : |u i| ≤ r := by
    exact (hu i).trans (div_le_self hr (by linarith [Nat.cast_nonneg (α := ℝ) d]))
  have hsum : |∑ i, u i| ≤ r := by
    calc
      _ ≤ ∑ i, |u i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, r/(d+1) := Finset.sum_le_sum (fun i _ => hu i)
      _ = (d:ℝ)*(r/(d+1)) := by simp
      _ ≤ r := by
        have H : (d:ℝ) ≤ d+1 := by linarith
        have := mul_le_mul_of_nonneg_right H (div_nonneg hr hd.le)
        rwa [mul_div_cancel₀ _ hd.ne'] at this
  change |(Matrix.diagonal _ : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) i j - _| ≤ _
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq,Matrix.one_apply_eq]
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp only [Fin.snoc_last]
      exact (exp_sub_one_abs_le (by simpa only [abs_neg] using hsum.trans hr1)).trans
        (by simpa only [abs_neg] using mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ)≤2))
    · simp only [Fin.snoc_castSucc]
      exact (exp_sub_one_abs_le ((hsmall k).trans hr1)).trans
        (mul_le_mul_of_nonneg_left (hsmall k) (by norm_num))
  · simp only [Matrix.diagonal_apply_ne _ hij,Matrix.one_apply_ne hij,sub_self,abs_zero]
    positivity

 

lemma matrix_product_entry_error {n : ℕ} {g h : G n} {a b : ℝ}
    (ha : 0 ≤ a)
    (hg : ∀ i j, |g.1 i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j| ≤ a)
    (hh : ∀ i j, |h.1 i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j| ≤ b)
    (i j : Fin n) :
    |(g*h).1 i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j| ≤ a+b+n*a*b := by
  let I : Matrix (Fin n) (Fin n) ℝ := 1
  have He : (g*h).1 - I = (g.1-I)*(h.1-I)+(g.1-I)+(h.1-I) := by
    change g.1*h.1-I = _
    simp only [I,mul_sub,sub_mul,Matrix.one_mul,Matrix.mul_one]
    abel
  have Hij := congrFun (congrFun He i) j
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.mul_apply] at Hij
  rw [Hij]
  calc
    _ ≤ |∑ k, (g.1 i k-I i k)*(h.1 k j-I k j)| + |g.1 i j-I i j| + |h.1 i j-I i j| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (∑ _k : Fin n, a*b)+a+b := by
      apply add_le_add (add_le_add ?_ (hg i j)) (hh i j)
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => by
        rw [abs_mul]
        exact mul_le_mul (hg i k) (hh k j) (abs_nonneg _) ha))
    _ = _ := by simp <;> ring

 

theorem near_diagonal_cover (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∃ s : Finset (Fin d → ℝ),
        (∀ u ∈ s, ∀ i, |u i| ≤ Real.log 2+1) ∧
        (s.card : ℝ) ≤ C / r^d ∧
        ∀ h : G (d+1),
          (∀ i, (1:ℝ)/2 ≤ h.1 i i ∧ h.1 i i ≤ 2) →
          (∀ i j, i ≠ j → |h.1 i j| ≤ r) →
          ∃ u ∈ s, h ∈ (fun k => diagonalFlow u * k) '' matrixBall (d+1) (C*r) := by
  classical
  let A : ℝ := ((d+1).factorial : ℝ)*2^(d+1) + 2 + 2^d
  let B : ℝ := 2+A+2*(d+1)*A
  let E : ℝ := ((2*Real.log 2+2)*(d+1))^d
  have hA : 0 ≤ A := by dsimp [A] <;> positivity
  have hB : 0 ≤ B := by dsimp [B] <;> positivity
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  refine ⟨B+E+1, by positivity, ?_⟩
  intro r hr hr1
  have hd : (0:ℝ) < d+1 := by positivity
  have hρ : 0 < r/(d+1) := div_pos hr hd
  have hρ1 : r/(d+1) ≤ 1 := (div_le_self hr.le (by linarith [Nat.cast_nonneg (α := ℝ) d])).trans hr1
  obtain ⟨s,hs,hcard,hcover⟩ := cube_grid_cover d
    (Real.log_nonneg (by norm_num : (1:ℝ)≤2)) hρ hρ1
  refine ⟨s,hs,?_,?_⟩
  · have hcard' : (s.card:ℝ) ≤ E/r^d := by
      convert hcard using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [E]
      rw [div_pow,mul_pow]
      field_simp
    exact hcard'.trans (div_le_div_of_nonneg_right (by linarith) (pow_nonneg hr.le d))
  · intro h hdiag hoff
    let x : Fin d → ℝ := fun i => Real.log (h.1 i.castSucc i.castSucc)
    have hx : ∀ i, |x i| ≤ Real.log 2 := by
      intro i
      exact abs_le.mpr (diagonal_log_mem_compact_box h hdiag i (Set.mem_univ _))
    obtain ⟨u,hu,hxu⟩ := hcover x hx
    have hw : ∀ i, |(x-u) i| ≤ r/(d+1) := fun i => (hxu i).le
    have HD := diagonalFlow_small_entries hr.le hr1 hw
    have HN : ∀ i j,
        |(diagonalFlow (-x) * h).1 i j - (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) i j| ≤ A*r :=
      normalized_matrix_entry_bound h hr.le hr1 hdiag hoff
    have Hmul := matrix_product_entry_error (show 0 ≤ 2*r by positivity)
      HD HN
    have He : diagonalFlow (x-u) * (diagonalFlow (-x) * h) = diagonalFlow (-u)*h := by
      rw [←mul_assoc,←diagonalFlow_add]
      congr 2
      abel
    have Herror (i j : Fin (d+1)) :
        |(diagonalFlow (-u)*h).1 i j - (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) i j| ≤ B*r := by
      have H := Hmul i j
      rw [He] at H
      apply H.trans
      have Hr : r*r ≤ r := by nlinarith
      have HC : 0 ≤ 2*(d+1)*A := by positivity
      have := mul_le_mul_of_nonneg_left Hr HC
      dsimp [B]
      push_cast
      nlinarith
    refine ⟨u,hu,diagonalFlow (-u)*h,?_,?_⟩
    · intro i j
      exact (Herror i j).trans_lt (by nlinarith)
    · change diagonalFlow u * (diagonalFlow (-u) * h) = h
      rw [←mul_assoc,←diagonalFlow_add,add_neg_cancel,diagonalFlow_zero,one_mul]

 

theorem tube_cover (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ell : Fin (d+1) → ℝ) (hell : ∑i, ell i = 0)
      (δ b t : ℝ), 0 ≤ δ → 0 ≤ b → b < 1/4 → 0 ≤ t →
      (∀ i j, i ≠ j → δ ≤ |ell i-ell j|) →
      ∃ s : Finset (Fin d → ℝ),
        (∀ u ∈ s, ∀ i, |u i| ≤ Real.log 2+1) ∧
        (s.card : ℝ) ≤ C / (Real.exp (-δ*t))^d ∧
        ∀ h ∈ twoSidedTube ell hell b t,
          ∃ u ∈ s, h ∈ (fun k => diagonalFlow u*k) ''
            matrixBall (d+1) (C*Real.exp (-δ*t)) := by
  obtain ⟨C,hC,H⟩ := near_diagonal_cover d
  refine ⟨C,hC,?_⟩
  intro ell hell δ b t hδ hb hb1 ht hgap
  have hr1 : Real.exp (-δ*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  obtain ⟨s,hs,hcard,hcover⟩ := H (Real.exp (-δ*t)) (Real.exp_pos _) hr1
  refine ⟨s,hs,hcard,?_⟩
  intro h hh
  obtain ⟨hdiag,hoff⟩ := tube_entries_uniform ell hell hb ht hgap hh
  apply hcover h
  · intro i
    have Hi := abs_lt.mp (hdiag i)
    constructor <;> linarith
  · intro i j hij
    exact (hoff i j hij).le.trans (mul_le_of_le_one_left (Real.exp_pos _).le (by linarith))



lemma diagonalLogBox_isCompact (d : ℕ) : IsCompact (diagonalLogBox d) := by
  simpa only [diagonalLogBox,abs_le,Set.mem_Icc] using
    (isCompact_pi_infinite (fun _i : Fin d =>
      show IsCompact (Set.Icc (-(Real.log 2+1)) (Real.log 2+1)) from isCompact_Icc))

lemma compact_diagonal_thickening {d : ℕ} {Ω : Set (X (d+1))} (hΩ : IsCompact Ω) :
    IsCompact ((fun p : X (d+1) × LogCoordinates d => rightAction p.1 (diagonalFlow p.2)) ''
      (Ω ×ˢ diagonalLogBox d)) := by
  refine (hΩ.prod (diagonalLogBox_isCompact d)).image ?_
  exact (continuous_rightAction_uncurry (d+1)).comp
    (continuous_fst.prodMk ((continuous_diagonalFlow d).comp continuous_snd))



lemma ordinaryBallBound_of_le {n : ℕ} {μ ξ : Measure (X n)}
    (hμ : OrdinaryBallBound n μ) {c : ℝ} (hc : 0 < c)
    (hξ : ξ ≤ ENNReal.ofReal c • μ) : OrdinaryBallBound n ξ := by
  intro Ω hΩ
  obtain ⟨C,r₀,hC,hr₀,H⟩ := hμ Ω hΩ
  refine ⟨c*C,r₀,mul_pos hc hC,hr₀,?_⟩
  intro x hx r hr hrr
  calc
    ξ _ ≤ (ENNReal.ofReal c • μ) _ := hξ _
    _ = ENNReal.ofReal c * μ _ := Measure.smul_apply _ _ _
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (C*r^n) := mul_le_mul_right (H x hx r hr hrr) _
    _ = ENNReal.ofReal ((c*C)*r^n) := by rw [← ENNReal.ofReal_mul hc.le]; congr 1; ring

 

theorem tube_mass_of_ordinary_balls {d : ℕ} {ξ : Measure (X (d+1))}
    (hξ : OrdinaryBallBound (d+1) ξ) (Ω : Set (X (d+1))) (hΩ : IsCompact Ω)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i = 0)
    {δ b : ℝ} (hδ : 0 < δ) (hb : 0 ≤ b) (hb1 : b < 1/4)
    (hgap : ∀ i j, i ≠ j → δ ≤ |ell i-ell j|) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t : ℝ in atTop,
      ∀ x ∈ Ω, ξ ((fun h => rightAction x h) '' twoSidedTube ell hell b t) ≤
        ENNReal.ofReal (K*Real.exp (-δ*t)) := by
  classical
  obtain ⟨C,hC,Hcover⟩ := tube_cover d
  let Ω' : Set (X (d+1)) :=
    (fun p : X (d+1) × LogCoordinates d => rightAction p.1 (diagonalFlow p.2)) ''
      (Ω ×ˢ diagonalLogBox d)
  obtain ⟨A,r₀,hA,hr₀,Hball⟩ := hξ Ω' (compact_diagonal_thickening hΩ)
  have hexp : Tendsto (fun t : ℝ => Real.exp (-δ*t)) atTop (𝓝 0) := by
    exact Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hδ)).mpr tendsto_id)
  have hsmall : ∀ᶠ t : ℝ in atTop, C*Real.exp (-δ*t) < r₀ := by
    have H : Tendsto (fun t : ℝ => C*Real.exp (-δ*t)) atTop (𝓝 (C*0)) :=
      tendsto_const_nhds.mul hexp
    simpa only [mul_zero] using H.eventually (eventually_lt_nhds (by simpa using hr₀))
  refine ⟨A*C^(d+2),by positivity,?_⟩
  filter_upwards [hsmall,eventually_ge_atTop (0:ℝ)] with t htr ht
  obtain ⟨s,hs,hcard,Hs⟩ := Hcover ell hell δ b t hδ.le hb hb1 ht hgap
  intro x hx
  let r : ℝ := Real.exp (-δ*t)
  have hr : 0 < r := Real.exp_pos _
  have Hsub : (fun h => rightAction x h) '' twoSidedTube ell hell b t ⊆
      ⋃ u ∈ s, (fun k => rightAction (rightAction x (diagonalFlow u)) k) ''
        matrixBall (d+1) (C*r) := by
    rintro z ⟨h,hh,rfl⟩
    obtain ⟨u,hu,k,hk,rfl⟩ := Hs h hh
    refine Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨hu,?_⟩⟩
    exact ⟨k,hk,rightAction_mul x _ _⟩
  have Hcenter (u : LogCoordinates d) (hu : u ∈ s) : rightAction x (diagonalFlow u) ∈ Ω' :=
    ⟨(x,u),⟨hx,hs u hu⟩,rfl⟩
  calc
    ξ _ ≤ ξ (⋃ u ∈ s, (fun k => rightAction (rightAction x (diagonalFlow u)) k) ''
        matrixBall (d+1) (C*r)) := measure_mono Hsub
    _ ≤ ∑ u ∈ s, ξ ((fun k => rightAction (rightAction x (diagonalFlow u)) k) ''
        matrixBall (d+1) (C*r)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _u ∈ s, ENNReal.ofReal (A*(C*r)^(d+1)) :=
      Finset.sum_le_sum (fun u hu => Hball _ (Hcenter u hu) _ (mul_pos hC hr) htr)
    _ = ENNReal.ofReal ((s.card:ℝ)*(A*(C*r)^(d+1))) := by
      rw [Finset.sum_const,nsmul_eq_mul]
      simp only [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((C/r^d)*(A*(C*r)^(d+1))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard (by positivity))
    _ = ENNReal.ofReal ((A*C^(d+2))*r) := by
      congr 1
      rw [mul_pow,pow_succ r,pow_succ C,show d+2=(d+1)+1 from rfl,pow_succ C]
      field_simp
      ring

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ShannonEntropy
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
namespace PrimeDegreePackets


lemma finiteShannon_nonneg {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (h1 : ∑ a, p a = 1) : 0 ≤ finiteShannon p := by
  classical
  apply Finset.sum_nonneg
  intro a _
  apply Real.negMulLog_nonneg (hp a)
  rw [← h1]
  exact Finset.single_le_sum (fun b _ => hp b) (Finset.mem_univ a)

lemma negMulLog_le_cross {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hzero : q = 0 → p = 0) :
    Real.negMulLog p ≤ -p * Real.log q + q-p := by
  by_cases hp0 : p = 0
  · simp [hp0,hq]
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hq' : 0 < q := lt_of_le_of_ne hq (fun h => hp0 (hzero h.symm))
  have H := mul_le_mul_of_nonneg_right
    (Real.self_sub_one_le_mul_log (div_nonneg hp hq)) hq
  rw [Real.log_div hp0 hq'.ne'] at H
  have heq : (p/q-1)*q = p-q := by field_simp
  have heq' : (p/q*(Real.log p-Real.log q))*q = p*(Real.log p-Real.log q) := by
    field_simp
  rw [heq,heq'] at H
  unfold Real.negMulLog
  linarith

 
theorem finiteShannon_le_cross {α : Type*} [Fintype α] {p q : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1)
    (hzero : ∀ a, q a = 0 → p a = 0) :
    finiteShannon p ≤ ∑ a, -p a * Real.log (q a) := by
  calc
    finiteShannon p ≤ ∑ a, (-p a * Real.log (q a) + q a-p a) :=
      Finset.sum_le_sum (fun a _ => negMulLog_le_cross (hp a) (hq a) (hzero a))
    _ = ∑ a, -p a * Real.log (q a) := by
      rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,hp1,hq1]
      ring

 
theorem finiteShannon_joint_le {α β : Type*} [Fintype α] [Fintype β]
    {p : α × β → ℝ} (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    finiteShannon p ≤ finiteShannon (fun a => ∑ b, p (a,b)) +
      finiteShannon (fun b => ∑ a, p (a,b)) := by
  classical
  let r : α → ℝ := fun a => ∑ b, p (a,b)
  let c : β → ℝ := fun b => ∑ a, p (a,b)
  have hr a : 0 ≤ r a := Finset.sum_nonneg fun _ _ => hp _
  have hc b : 0 ≤ c b := Finset.sum_nonneg fun _ _ => hp _
  have hr1 : ∑ a, r a = 1 := by simpa [r,Fintype.sum_prod_type] using hp1
  have hc1 : ∑ b, c b = 1 := by
    change (∑ b, ∑ a, p (a,b)) = 1
    rw [Finset.sum_comm]
    simpa only [r] using hr1
  have hpr a b : p (a,b) ≤ r a := Finset.single_le_sum
    (fun j _ => hp (a,j)) (Finset.mem_univ b)
  have hpc a b : p (a,b) ≤ c b := Finset.single_le_sum
    (fun i _ => hp (i,b)) (Finset.mem_univ a)
  have hq1 : ∑ z : α × β, r z.1 * c z.2 = 1 := by
    simp only [Fintype.sum_prod_type,← Finset.mul_sum,hc1,mul_one,hr1]
  have H := finiteShannon_le_cross hp (fun z => mul_nonneg (hr z.1) (hc z.2)) hp1 hq1
    (fun z hz => by
      rcases mul_eq_zero.mp hz with h | h
      · exact le_antisymm (h ▸ hpr z.1 z.2) (hp z)
      · exact le_antisymm (h ▸ hpc z.1 z.2) (hp z))
  refine H.trans_eq ?_
  have heq (a : α) (b : β) : -p (a,b)*Real.log (r a*c b) =
      -p (a,b)*Real.log (r a) + -p (a,b)*Real.log (c b) := by
    by_cases h : p (a,b) = 0
    · simp [h]
    have hpos := lt_of_le_of_ne (hp (a,b)) (Ne.symm h)
    rw [Real.log_mul (ne_of_gt (lt_of_lt_of_le hpos (hpr a b)))
      (ne_of_gt (lt_of_lt_of_le hpos (hpc a b))),mul_add]
  simp only [Fintype.sum_prod_type,heq,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun a b => -p (a,b)*Real.log (c b))]
  congr 1
  · simp only [finiteShannon,Real.negMulLog,r,← Finset.sum_mul,Finset.sum_neg_distrib]
  · simp only [finiteShannon,Real.negMulLog,c,← Finset.sum_mul,Finset.sum_neg_distrib]

 
theorem finiteShannon_le_log_card {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    finiteShannon p ≤ Real.log (Fintype.card α) := by
  classical
  have hn : 0 < Fintype.card α := by
    by_contra hn
    have : IsEmpty α := Fintype.card_eq_zero_iff.mp (by omega)
    simp at hp1
  have hn' : (Fintype.card α : ℝ) ≠ 0 := by positivity
  have H := finiteShannon_le_cross hp
    (q := fun _ => (Fintype.card α : ℝ)⁻¹) (fun _ => by positivity) hp1
    (by simp [hn']) (fun _ h => (inv_ne_zero hn' h).elim)
  refine H.trans_eq ?_
  rw [← Finset.sum_mul,Finset.sum_neg_distrib,hp1,Real.log_inv]
  ring


lemma observation_distribution_sum {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    ∑ a, μ.real {y | P y = a} = 1 := by
  have hd : Pairwise (fun a b => Disjoint {y | P y = a} {y | P y = b}) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro y hy hy'
    exact hab (hy.symm.trans hy')
  rw [← measureReal_iUnion_fintype hd hP]
  have heq : (⋃ a, {y | P y = a}) = Set.univ := by ext; simp
  rw [heq]; simp [Measure.real]

lemma observationEntropy_nonneg {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    0 ≤ observationEntropy μ P :=
  finiteShannon_nonneg (fun _ => measureReal_nonneg) (observation_distribution_sum μ P hP)

end PrimeDegreePackets

open scoped BigOperators Topology ENNReal
namespace PrimeDegreePackets

lemma observationEntropy_equiv {Y α β : Type*} [MeasurableSpace Y]
    [Fintype α] [Fintype β] (μ : Measure Y) (P : Y → α) (e : α ≃ β) :
    observationEntropy μ (fun y => e (P y)) = observationEntropy μ P := by
  classical
  unfold observationEntropy finiteShannon
  rw [← e.sum_comp]
  simp only [Equiv.apply_eq_iff_eq]

lemma observation_joint_row {Y α β : Type*} [MeasurableSpace Y]
    [Fintype β] (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a}) (hQ : ∀ b, MeasurableSet {y | Q y = b})
    (a : α) :
    ∑ b, μ.real {y | (P y,Q y) = (a,b)} = μ.real {y | P y = a} := by
  have hd : Pairwise (fun b c => Disjoint {y | (P y,Q y) = (a,b)}
      {y | (P y,Q y) = (a,c)}) := by
    intro b c hbc
    rw [Set.disjoint_left]
    intro y hy hz
    exact hbc ((congrArg Prod.snd hy).symm.trans (congrArg Prod.snd hz))
  have hm b : MeasurableSet {y | (P y,Q y) = (a,b)} := by
    simpa only [Prod.mk.injEq,Set.ofPred_and] using (hP a).inter (hQ b)
  rw [← measureReal_iUnion_fintype hd hm]
  congr 1
  ext y
  simp

 
theorem observationEntropy_joint_le {Y α β : Type*} [MeasurableSpace Y]
    [Fintype α] [Fintype β] (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a}) (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    observationEntropy μ (fun y => (P y,Q y)) ≤
      observationEntropy μ P + observationEntropy μ Q := by
  have hm (z : α × β) : MeasurableSet {y | (P y,Q y) = z} := by
    rcases z with ⟨a,b⟩
    simpa only [Prod.mk.injEq,Set.ofPred_and] using (hP a).inter (hQ b)
  have H := finiteShannon_joint_le (fun z =>
    measureReal_nonneg (μ := μ) (s := {y | (P y,Q y) = z}))
    (observation_distribution_sum μ (fun y => (P y,Q y)) hm)
  have hrow := observation_joint_row μ P Q hP hQ
  have hcol (b : β) : (∑ a, μ.real {y | (P y,Q y) = (a,b)}) = μ.real {y | Q y = b} := by
    convert observation_joint_row μ Q P hQ hP b using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext a
    congr 1
    ext y
    simp only [Prod.mk.injEq,and_comm]
  simpa only [hrow,hcol,observationEntropy] using H

lemma observationEntropy_comp_preserving {Y α : Type*} [MeasurableSpace Y]
    [Fintype α] (μ : Measure Y) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) {S : Y → Y} (hS : MeasurePreserving S μ μ) :
    observationEntropy μ (fun y => P (S y)) = observationEntropy μ P := by
  unfold observationEntropy finiteShannon
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  change (μ (S ⁻¹' {y | P y = a})).toReal = (μ {y | P y = a}).toReal
  rw [hS.measure_preimage (hP a).nullMeasurableSet]


lemma orbitName_measurable_fiber {Y α : Type*} [MeasurableSpace Y]
    {T : Y → Y} (hT : Measurable T) {P : Y → α}
    (hP : ∀ a, MeasurableSet {y | P y = a}) (N : ℕ) (a : Fin N → α) :
    MeasurableSet {y | orbitName T P N y = a} := by
  have heq : {y | orbitName T P N y = a} = ⋂ j : Fin N, {y | P (T^[j] y) = a j} := by
    ext y
    simp [orbitName,funext_iff]
  rw [heq]
  exact MeasurableSet.iInter fun j => (hP (a j)).preimage (hT.iterate j)

lemma orbitName_add {Y α : Type*} (T : Y → Y) (P : Y → α) (m n : ℕ) :
    orbitName T P (m+n) = fun y => (Fin.appendEquiv m n)
      (orbitName T P m y,orbitName T P n (T^[m] y)) := by
  funext y
  apply (Fin.appendEquiv m n).symm.injective
  ext i
  · simp [orbitName]
  · simp only [Fin.appendEquiv_symm_apply,orbitName,
      Equiv.symm_apply_apply,Fin.val_natAdd]
    rw [Function.iterate_add_apply,← Function.iterate_add_apply,
      ← Function.iterate_add_apply,Nat.add_comm]

 
theorem orbitEntropy_subadditive {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) :
    Subadditive (fun N => observationEntropy μ (orbitName T P N)) := by
  intro m n
  change observationEntropy μ (orbitName T P (m+n)) ≤
    observationEntropy μ (orbitName T P m) + observationEntropy μ (orbitName T P n)
  rw [orbitName_add,observationEntropy_equiv]
  have H := observationEntropy_joint_le μ (orbitName T P m)
    (fun y => orbitName T P n (T^[m] y))
    (orbitName_measurable_fiber hT.measurable hP m)
    (fun a => (orbitName_measurable_fiber hT.measurable hP n a).preimage
      (hT.measurable.iterate m))
  rw [observationEntropy_comp_preserving μ _
    (orbitName_measurable_fiber hT.measurable hP n) (hT.iterate m)] at H
  exact H



theorem tendsto_observationEntropyRate {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) :
    Tendsto (fun N : ℕ => observationEntropy μ (orbitName T P N)/(N:ℝ)) atTop
      (𝓝 (observationEntropyRate μ T P)) := by
  have h := orbitEntropy_subadditive μ hT P hP
  have hb : BddBelow (Set.range (fun N : ℕ => observationEntropy μ (orbitName T P N)/(N:ℝ))) := by
    refine ⟨0,?_⟩
    rintro _ ⟨N,rfl⟩
    exact div_nonneg (observationEntropy_nonneg μ _
      (orbitName_measurable_fiber hT.measurable hP N)) (Nat.cast_nonneg N)
  simpa only [Subadditive.lim,observationEntropyRate] using h.tendsto_lim hb



end PrimeDegreePackets


namespace PrimeDegreePackets

lemma negMulLog_lower_of_le_exp {r B : ℝ} (hr : 0 ≤ r) (hB : r ≤ Real.exp (-B)) :
    B*r ≤ Real.negMulLog r := by
  by_cases h0 : r = 0
  · simp [h0]
  have hr' : 0 < r := lt_of_le_of_ne hr (Ne.symm h0)
  have H : Real.log r ≤ -B := by
    simpa only [Real.log_exp] using Real.log_le_log hr' hB
  have H' := mul_le_mul_of_nonneg_left H hr
  unfold Real.negMulLog
  nlinarith

 

theorem finiteShannon_split_lower {α : Type*} [Fintype α] {p r : α → ℝ}
    (_hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (hr : ∀ a, 0 ≤ r a) (hrp : ∀ a, r a ≤ p a)
    (B : ℝ) (hB : ∀ a, r a ≤ Real.exp (-B)) :
    B*(∑ a, r a)-Real.log 2 ≤ finiteShannon p := by
  classical
  let q : α × Bool → ℝ := fun z => if z.2 then r z.1 else p z.1-r z.1
  have hq z : 0 ≤ q z := by
    rcases z with ⟨a,b⟩
    cases b <;> simp only [q,Bool.false_eq_true,↓reduceIte] <;> linarith [hr a,hrp a]
  have hrow a : ∑ b, q (a,b) = p a := by simp [q]
  have hq1 : ∑ z, q z = 1 := by simpa only [Fintype.sum_prod_type,hrow] using hp1
  have hqle z : q z ≤ 1 := by
    rw [← hq1]
    exact Finset.single_le_sum (fun z _ => hq z) (Finset.mem_univ z)
  have Hlow : B*(∑ a, r a) ≤ finiteShannon q := by
    rw [Finset.mul_sum]
    calc
      (∑ a, B*r a) ≤ ∑ a, Real.negMulLog (r a) :=
        Finset.sum_le_sum fun a _ => negMulLog_lower_of_le_exp (hr a) (hB a)
      _ ≤ ∑ a, (Real.negMulLog (p a-r a)+Real.negMulLog (r a)) := by
        apply Finset.sum_le_sum
        intro a _
        have H := Real.negMulLog_nonneg (hq (a,false)) (hqle (a,false))
        dsimp [q] at H
        linarith
      _ = finiteShannon q := by simp [finiteShannon,Fintype.sum_prod_type,q,add_comm]
  have Hjoint := finiteShannon_joint_le hq hq1
  simp only [hrow] at Hjoint
  have hcols : (∑ b, ∑ a, q (a,b)) = 1 := by
    rw [Finset.sum_comm]
    simpa only [hrow] using hp1
  have Hcol : finiteShannon (fun b => ∑ a, q (a,b)) ≤ Real.log 2 := by
    simpa using finiteShannon_le_log_card
      (fun b => Finset.sum_nonneg fun a _ => hq (a,b)) hcols
  linarith

lemma sum_good_observation_masses {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) {A : Set Y} (hA : MeasurableSet A) :
    (∑ a, μ.real (A ∩ {y | P y = a})) = μ.real A := by
  have hd : Pairwise (fun a b => Disjoint (A ∩ {y | P y = a}) (A ∩ {y | P y = b})) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro y hy hz
    exact hab (hy.2.symm.trans hz.2)
  rw [← measureReal_iUnion_fintype hd (fun a => hA.inter (hP a))]
  congr 1
  ext y
  simp

 

theorem observationEntropy_lower_of_good_atoms {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) {A : Set Y} (hA : MeasurableSet A)
    (B : ℝ) (hB : ∀ a, μ.real (A ∩ {y | P y = a}) ≤ Real.exp (-B)) :
    B*μ.real A-Real.log 2 ≤ observationEntropy μ P := by
  have H := finiteShannon_split_lower (p := fun a => μ.real {y | P y = a})
    (r := fun a => μ.real (A ∩ {y | P y = a}))
    (fun _ => measureReal_nonneg) (observation_distribution_sum μ P hP)
    (fun _ => measureReal_nonneg) (fun _ => measureReal_mono Set.inter_subset_right) B hB
  rw [sum_good_observation_masses μ P hP hA] at H
  exact H

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem observationEntropyRate_lower_of_good_atoms {Y α : Type*} [MeasurableSpace Y]
    [Fintype α] (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (A : ℕ → Set Y) (hA : ∀ N, MeasurableSet (A N))
    {c C w : ℝ} (hc : 0 ≤ c) (hC : 0 < C)
    (hw : ∀ᶠ N : ℕ in atTop, w ≤ μ.real (A N))
    (hsmall : ∀ᶠ N : ℕ in atTop, ∀ a : Fin N → α,
      μ.real (A N ∩ {y | orbitName T P N y = a}) ≤ C*Real.exp (-c*N)) :
    c*w ≤ observationEntropyRate μ T P := by
  let D : ℝ := |Real.log C| + Real.log 2
  have HN : ∀ᶠ N : ℕ in atTop,
      c*w-D/(N:ℝ) ≤ observationEntropy μ (orbitName T P N)/(N:ℝ) := by
    filter_upwards [hw,hsmall,eventually_ge_atTop (1:ℕ)] with N hwN hsN hN
    have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hexp : Real.exp (-(c*N-Real.log C)) = C*Real.exp (-c*N) := by
      rw [show -(c*(N:ℝ)-Real.log C)=Real.log C+(-c*N) by ring,Real.exp_add,
        Real.exp_log hC]
    have HL := observationEntropy_lower_of_good_atoms μ (orbitName T P N)
      (orbitName_measurable_fiber hT.measurable hP N) (hA N) (c*N-Real.log C)
      (fun a => (hsN a).trans_eq hexp.symm)
    have hmass0 : 0 ≤ μ.real (A N) := measureReal_nonneg
    have hmass1 : μ.real (A N) ≤ 1 := by
      have H := measureReal_mono (μ := μ) (Set.subset_univ (A N))
      simpa only [measureReal_def,measure_univ,ENNReal.toReal_one] using H
    have HH := mul_le_mul_of_nonneg_left hwN (mul_nonneg hc hn.le)
    have Hlog : Real.log C*μ.real (A N) ≤ |Real.log C| := by
      calc
        Real.log C*μ.real (A N) ≤ |Real.log C*μ.real (A N)| := le_abs_self _
        _ = |Real.log C| *μ.real (A N) := by rw [abs_mul,abs_of_nonneg hmass0]
        _ ≤ |Real.log C| := mul_le_of_le_one_right (abs_nonneg _) hmass1
    apply (le_div_iff₀ hn).mpr
    have Hcalc : (c*w-D/(N:ℝ))*(N:ℝ) = c*w*N-D := by field_simp
    rw [Hcalc]
    dsimp [D]
    nlinarith
  have hlimleft : Tendsto (fun N : ℕ => c*w-D/(N:ℝ)) atTop (𝓝 (c*w)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun N : ℕ => D/(N:ℝ)) atTop (𝓝 0))
  exact le_of_tendsto_of_tendsto hlimleft (tendsto_observationEntropyRate μ hT P hP) HN

 

theorem measureEntropy_lower_of_good_atoms {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (k : ℕ) (P : Y → Fin k)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (A : ℕ → Set Y) (hA : ∀ N, MeasurableSet (A N))
    {c C w : ℝ} (hc : 0 ≤ c) (hC : 0 < C)
    (hw : ∀ᶠ N : ℕ in atTop, w ≤ μ.real (A N))
    (hsmall : ∀ᶠ N : ℕ in atTop, ∀ a : Fin N → Fin k,
      μ.real (A N ∩ {y | orbitName T P N y = a}) ≤ C*Real.exp (-c*N)) :
    ENNReal.ofReal (c*w) ≤ measureEntropy μ T := by
  exact le_iSup_of_le k (le_iSup_of_le P (le_iSup_of_le hP
    (ENNReal.ofReal_le_ofReal
      (observationEntropyRate_lower_of_good_atoms μ hT P hP A hA hc hC hw hsmall))))

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_InverseEntropy
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal


namespace PrimeDegreePackets


lemma stepCover_of_image {Y : Type*} {T : Y → Y} {R : Y → Y → Prop} {M : ℕ}
    (h : StepCover T R M) (j : ℕ) (E : Set Y)
    (hE : RelationDiameter R (T^[j] '' E)) :
    ∃ F : Fin M → Set Y, E ⊆ ⋃ i, F i ∧ ∀ i, F i ⊆ E ∧
      RelationDiameter R (T^[j+1] '' F i) := by
  obtain ⟨F,hcov,hF⟩ := h _ hE
  refine ⟨fun i => E ∩ T^[j] ⁻¹' F i, ?_, ?_⟩
  · intro x hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hcov ⟨x,hx,rfl⟩)
    exact Set.mem_iUnion.mpr ⟨i,hx,hi⟩
  · intro i
    refine ⟨Set.inter_subset_left,?_⟩
    rintro x ⟨u,hu,rfl⟩ y ⟨v,hv,rfl⟩
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    exact (hF i).2 _ ⟨_,hu.2,rfl⟩ _ ⟨_,hv.2,rfl⟩



end PrimeDegreePackets

open scoped BigOperators Topology ENNReal Classical
namespace PrimeDegreePackets

lemma visitCount_cast {Y : Type*} (T : Y → Y) (B : Set Y) (N : ℕ) (x : Y) :
    (visitCount T B N x : ℝ) = ∑ j ∈ Finset.range N, B.indicator (fun _ => (1:ℝ)) (T^[j] x) := by
  classical
  rw [visitCount,Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hx : T^[j] x ∈ B <;> simp [hx]

lemma integrable_visitCount {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsFiniteMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {B : Set Y} (hB : MeasurableSet B) (N : ℕ) :
    Integrable (fun x => (visitCount T B N x : ℝ)) μ := by
  simp only [visitCount_cast]
  apply integrable_finsetSum
  intro j _
  exact (hT.iterate j).integrable_comp_of_integrable ((integrable_const (1:ℝ)).indicator hB)

lemma integral_visitCount {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsFiniteMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {B : Set Y} (hB : MeasurableSet B) (N : ℕ) :
    (∫ x, (visitCount T B N x : ℝ) ∂μ) = N*μ.real B := by
  simp only [visitCount_cast]
  rw [integral_finsetSum]
  · have hj (j : ℕ) : (∫ x, B.indicator (fun _ => (1:ℝ)) (T^[j] x) ∂μ) = μ.real B := by
      have H := integral_map (hT.iterate j).measurable.aemeasurable
        ((measurable_const.indicator hB).aestronglyMeasurable (μ := Measure.map T^[j] μ) :
          AEStronglyMeasurable (B.indicator (fun _ => (1:ℝ))) (Measure.map T^[j] μ))
      rw [(hT.iterate j).map_eq] at H
      rw [← H]
      simp [integral_indicator hB,measureReal_def]
    simp only [hj,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  · intro j _
    exact (hT.iterate j).integrable_comp_of_integrable ((integrable_const (1:ℝ)).indicator hB)

lemma measurable_visitCount {Y : Type*} [MeasurableSpace Y]
    {T : Y → Y} (hT : Measurable T) {B : Set Y} (hB : MeasurableSet B) (N : ℕ) :
    Measurable (fun x => (visitCount T B N x : ℝ)) := by
  simp only [visitCount_cast]
  exact Finset.measurable_sum _ fun j _ => (measurable_const.indicator hB).comp (hT.iterate j)

 

theorem measure_many_visits {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsFiniteMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {B : Set Y} (hB : MeasurableSet B) {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) :
    μ {x | ε*N < (visitCount T B N x : ℝ)} ≤ ENNReal.ofReal (μ.real B/ε) := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hi := (integrable_visitCount μ hT hB N).div_const (ε*N)
  have hnon : 0 ≤ᵐ[μ] fun x => (visitCount T B N x : ℝ)/(ε*N) :=
    ae_of_all _ fun x => div_nonneg (Nat.cast_nonneg _) (mul_pos hε hn).le
  have H := hi.measure_le_integral hnon (s := {x | ε*N < (visitCount T B N x : ℝ)})
    (fun x hx => (le_div_iff₀ (mul_pos hε hn)).mpr (by simpa only [one_mul] using hx.le))
  rw [integral_div,integral_visitCount μ hT hB N] at H
  convert H using 2
  all_goals try with_reducible_and_instances rfl
  field_simp

end PrimeDegreePackets

open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
namespace PrimeDegreePackets

lemma matrixBall_mono {n : ℕ} {r s : ℝ} (hrs : r ≤ s) :
    matrixBall n r ⊆ matrixBall n s := by
  intro g hg i j
  exact (hg i j).trans_le hrs

 

lemma inverse_entries_uniform (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ g ∈ matrixBall n 1, ∀ i j, |g⁻¹.1 i j| ≤ C := by
  let K : Set (Matrix (Fin n) (Fin n) ℝ) := {m | ∀ i j, |m i j| ≤ 2}
  have hK : IsCompact K := by
    simpa only [K,Set.matrix,Set.mem_Icc,abs_le] using
      (show IsCompact (Set.Icc (-2:ℝ) 2) from isCompact_Icc).matrix
  have hpre : IsCompact (Subtype.val ⁻¹' K : Set (G n)) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage hK
  have hc : Continuous (fun g : G n => g⁻¹.1) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous.comp continuous_inv
  obtain ⟨C,hC⟩ := hpre.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0+1,by positivity,?_⟩
  intro g hg i j
  have hgin : g.1 ∈ K := by
    intro i j
    have H := hg i j
    have H1 : |(1 : Matrix (Fin n) (Fin n) ℝ) i j| ≤ 1 := by
      by_cases hij : i = j <;> simp [Matrix.one_apply,hij]
    calc
      |g.1 i j| = |(g.1 i j-(1 : Matrix (Fin n) (Fin n) ℝ) i j)+
          (1 : Matrix (Fin n) (Fin n) ℝ) i j| := by congr 1; ring
      _ ≤ |g.1 i j-(1 : Matrix (Fin n) (Fin n) ℝ) i j| +
          |(1 : Matrix (Fin n) (Fin n) ℝ) i j| := abs_add_le _ _
      _ ≤ 2 := by linarith
  calc
    |g⁻¹.1 i j| = ‖g⁻¹.1 i j‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖g⁻¹.1 i‖ := norm_le_pi_norm _ _
    _ ≤ ‖g⁻¹.1‖ := norm_le_pi_norm _ _
    _ ≤ C := hC g hgin
    _ ≤ max C 0+1 := by linarith [le_max_left C 0]

 
lemma left_div_entry_bound {n : ℕ} (g h : G n) {C b : ℝ}
    (hC : 0 ≤ C)
    (hg : ∀ i j, |g⁻¹.1 i j| ≤ C)
    (hgh : ∀ i j, |h.1 i j-g.1 i j| ≤ b) :
    ∀ i j, |(g⁻¹*h).1 i j-(1 : Matrix (Fin n) (Fin n) ℝ) i j| ≤ n*C*b := by
  intro i j
  have heq : (g⁻¹*h).1 - (1 : Matrix (Fin n) (Fin n) ℝ) = g⁻¹.1*(h.1-g.1) := by
    rw [Matrix.mul_sub]
    simp only [← Matrix.SpecialLinearGroup.coe_mul,inv_mul_cancel,Matrix.SpecialLinearGroup.coe_one]
  change |((g⁻¹*h).1-(1 : Matrix (Fin n) (Fin n) ℝ)) i j| ≤ _
  rw [heq,Matrix.mul_apply]
  calc
    |∑ k, g⁻¹.1 i k*(h.1-g.1) k j| ≤ ∑ k, |g⁻¹.1 i k*(h.1-g.1) k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, C*b := Finset.sum_le_sum fun k _ => by
      rw [abs_mul]
      exact mul_le_mul (hg i k) (hgh k j) (abs_nonneg _) hC
    _ = n*C*b := by simp <;> ring

 

theorem small_matrix_ball_cover (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ r : ℝ, 0 < r → L*r ≤ 1 →
      ∃ F : Fin M → Set (G n), matrixBall n (L*r) ⊆ ⋃ i, F i ∧
        ∀ i, F i ⊆ matrixBall n (L*r) ∧
          RelationDiameter (fun g h : G n => g⁻¹*h ∈ matrixBall n r) (F i) := by
  classical
  obtain ⟨C,hC,HC⟩ := inverse_entries_uniform n
  let ε : ℝ := 1/(4*((n:ℝ)+1)*(C+1))
  have hden : 0 < 4*((n:ℝ)+1)*(C+1) := by positivity
  have hε : 0 < ε := by exact one_div_pos.mpr hden
  have hε1 : ε ≤ 1 := by
    apply (div_le_one hden).mpr
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hbudget : (n:ℝ)*C*ε ≤ 1/4 := by
    change (n:ℝ)*C*(1/(4*((n:ℝ)+1)*(C+1))) ≤ 1/4
    rw [mul_one_div]
    apply (div_le_iff₀ hden).mpr
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  let e : (Fin n × Fin n) ≃ Fin (Fintype.card (Fin n × Fin n)) := Fintype.equivFin _
  obtain ⟨s,_,_,hs⟩ := cube_grid_cover (Fintype.card (Fin n × Fin n)) hL hε hε1
  have hsne : s.Nonempty := by
    obtain ⟨u,hu,_⟩ := hs 0 (by simpa using fun _ => hL)
    exact ⟨u,hu⟩
  let : Nonempty s := hsne.to_subtype
  let f : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  refine ⟨Fintype.card s,Fintype.card_pos,?_⟩
  intro r hr hLr
  let q (g : G n) (t : Fin (Fintype.card (Fin n × Fin n))) : ℝ :=
    (g.1 (e.symm t).1 (e.symm t).2 - (1 : Matrix (Fin n) (Fin n) ℝ) (e.symm t).1 (e.symm t).2)/r
  let F (i : Fin (Fintype.card s)) : Set (G n) :=
    {g | g ∈ matrixBall n (L*r) ∧ ∀ t, |q g t-(f i).val t| < ε}
  refine ⟨F,?_,?_⟩
  · intro g hg
    have hq : ∀ t, |q g t| ≤ L := by
      intro t
      dsimp [q]
      rw [abs_div,abs_of_pos hr]
      exact (div_le_iff₀ hr).mpr (hg _ _).le
    obtain ⟨u,hu,hgu⟩ := hs (q g) hq
    exact Set.mem_iUnion.mpr ⟨f.symm ⟨u,hu⟩,hg,by simpa using hgu⟩
  · intro i
    refine ⟨fun _ hg => hg.1,?_⟩
    intro g hg h hh
    have hg1 := matrixBall_mono hLr hg.1
    have hdiff : ∀ j k, |h.1 j k-g.1 j k| ≤ 2*ε*r := by
      intro j k
      have H : |q h (e (j,k))-q g (e (j,k))| ≤ 2*ε := by
        calc
          _ = |(q h (e (j,k))-(f i).val (e (j,k))) +
              ((f i).val (e (j,k))-q g (e (j,k)))| := by congr 1; ring
          _ ≤ |q h (e (j,k))-(f i).val (e (j,k))| +
              |(f i).val (e (j,k))-q g (e (j,k))| := abs_add_le _ _
          _ ≤ 2*ε := by rw [abs_sub_comm ((f i).val _)]; linarith [hg.2 (e (j,k)),hh.2 (e (j,k))]
      have he : h.1 j k-g.1 j k = (q h (e (j,k))-q g (e (j,k)))*r := by
        simp only [q,Equiv.symm_apply_apply]
        field_simp
        ring
      rw [he,abs_mul,abs_of_pos hr]
      exact mul_le_mul_of_nonneg_right H hr.le
    have Hbound := left_div_entry_bound g h hC.le (HC g hg1) hdiff
    intro j k
    apply (Hbound j k).trans_lt
    nlinarith [mul_le_mul_of_nonneg_right hbudget hr.le]

end PrimeDegreePackets

open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
namespace PrimeDegreePackets

lemma one_mem_matrixBall (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (1 : G n) ∈ matrixBall n r := by
  intro i j
  simpa using hr

lemma matrixBall_nhds_basis {n : ℕ} {U : Set (G n)} (hU : U ∈ 𝓝 (1 : G n)) :
    ∃ r : ℝ, 0 < r ∧ matrixBall n r ⊆ U := by
  have hv : Topology.IsInducing (fun g : G n => g.1) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.isInducing
  rw [hv.nhds_eq_comap] at hU
  obtain ⟨V,hV,hVU⟩ := Filter.mem_comap.mp hU
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨r,hr,fun g hg => hVU (hsub ?_)⟩
  change dist g.1 (1 : G n).1 < r
  rw [dist_eq_norm]
  exact (Matrix.norm_lt_iff hr).mpr hg

 

lemma local_uniform_chart_injective {n : ℕ} (x : X n) :
    ∃ U : Set (X n), IsOpen U ∧ x ∈ U ∧ ∃ r : ℝ, 0 < r ∧
      ∀ y ∈ U, Set.InjOn (fun g => rightAction y g) (matrixBall n r) := by
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨V,hVo,hgV,hVi⟩ :=
      (quotient_covering n).isLocalHomeomorph.isLocallyInjective g
    have hpre : (fun u : G n => g*u) ⁻¹' V ∈ 𝓝 (1 : G n) := by
      apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
      simpa using hVo.mem_nhds hgV
    obtain ⟨W,hWo,h1W,hWW⟩ := exists_open_nhds_one_mul_subset hpre
    obtain ⟨r,hr,hrW⟩ := matrixBall_nhds_basis (hWo.mem_nhds h1W)
    refine ⟨(fun u => Quotient.mk _ (g*u)) '' W, ?_, ?_, r,hr,?_⟩
    · rw [← Set.image_image]
      exact (quotient_covering n).isOpenMap _ ((Homeomorph.mulLeft g).isOpenMap _ hWo)
    · exact ⟨1,h1W,by simp⟩
    · rintro y ⟨u,hu,rfl⟩ v hv w hw heq
      have hgv : g*(u*v) ∈ V := hWW (Set.mul_mem_mul hu (hrW hv))
      have hgw : g*(u*w) ∈ V := hWW (Set.mul_mem_mul hu (hrW hw))
      have He : g*(u*v) = g*(u*w) := hVi hgv hgw (by
        change Quotient.mk _ ((g*u)*v) = Quotient.mk _ ((g*u)*w) at heq
        simpa only [mul_assoc] using heq)
      exact mul_left_cancel (mul_left_cancel He)

 
theorem compact_uniform_chart_injective {n : ℕ} (K : Set (X n)) (hK : IsCompact K) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ K,
      Set.InjOn (fun g => rightAction x g) (matrixBall n r) := by
  choose U hUo hxU r hr hU using local_uniform_chart_injective (n := n)
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U hUo (by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x,hxU x⟩)
  let t : Finset ℝ := insert 1 (s.image r)
  have ht : t.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  refine ⟨t.min' ht,?_,?_⟩
  · have hm := Finset.min'_mem t ht
    rcases Finset.mem_insert.mp hm with hm | hm
    · rw [hm]; norm_num
    · obtain ⟨x,_,hxr⟩ := Finset.mem_image.mp hm
      rw [← hxr]
      exact hr x
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    apply (hU y x hxy).mono
    apply matrixBall_mono
    exact Finset.min'_le t (r y) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨y,hy,rfl⟩))

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ObservationCovers
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
namespace PrimeDegreePackets

 

lemma small_right_chart (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : X n,
      ∀ y ∈ (fun g => rightAction x g) '' matrixBall n δ,
      ∀ z ∈ (fun g => rightAction x g) '' matrixBall n δ,
      ∃ h ∈ matrixBall n r, rightAction y h = z := by
  obtain ⟨V,hV,_,hVi,hVV⟩ := exists_closed_nhds_one_inv_eq_mul_subset
    ((matrixBall_isOpen n r).mem_nhds (one_mem_matrixBall n hr))
  obtain ⟨δ,hδ,hδV⟩ := matrixBall_nhds_basis hV
  refine ⟨δ,hδ,?_⟩
  rintro x y ⟨u,hu,rfl⟩ z ⟨v,hv,rfl⟩
  refine ⟨u⁻¹*v,?_,?_⟩
  · apply hVV
    refine Set.mul_mem_mul ?_ (hδV hv)
    rw [← hVi]
    exact Set.inv_mem_inv.mpr (hδV hu)
  · simp only [rightAction_mul,mul_inv_cancel_left]

 

theorem compact_finite_observation {n : ℕ} (K : Set (X n)) (hK : IsCompact K)
    {r : ℝ} (hr : 0 < r) :
    ∃ k : ℕ, ∃ P : X n → (Fin k → Bool),
      (∀ a, MeasurableSet {x | P x = a}) ∧
      (∀ x, P x = (fun _ => false) ↔ x ∉ K) ∧
      ∀ a, a ≠ (fun _ => false) → ∀ x, P x = a → ∀ y, P y = a →
        x ∈ K ∧ y ∈ K ∧ ∃ h ∈ matrixBall n r, rightAction x h = y := by
  obtain ⟨δ,hδ,Hδ⟩ := small_right_chart n hr
  let U : X n → Set (X n) := fun x => (fun g => rightAction x g) '' matrixBall n δ
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U (fun x => right_ball_isOpen x δ) (by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x,1,one_mem_matrixBall n hδ,by simp [rightAction_one]⟩)
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm.trans
    (Equiv.refl s)
  let V : Fin (Fintype.card s) → Set (X n) := fun i => K ∩ U (e i)
  have hVm : ∀ i, MeasurableSet (V i) := fun i =>
    hK.isClosed.measurableSet.inter (right_ball_isOpen (e i).val δ).measurableSet
  have hVcov : K ⊆ ⋃ i, V i := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion.mpr ⟨e.symm ⟨y,hy⟩,hx,by simpa [V] using hxy⟩
  let P : X n → (Fin (Fintype.card s) → Bool) := fun x i => if x ∈ V i then true else false
  have hP : Measurable P := measurable_pi_iff.mpr fun i =>
    Measurable.ite (hVm i) measurable_const measurable_const
  have hbad (x : X n) : P x = (fun _ => false) ↔ x ∉ K := by
    constructor
    · intro hx hxK
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hVcov hxK)
      have H := congrFun hx i
      simp [P,hi] at H
    · intro hx
      funext i
      have H : x ∉ V i := fun h => hx h.1
      simp [P,H]
  refine ⟨Fintype.card s,P,fun a => hP (measurableSet_singleton a),hbad,?_⟩
  intro a ha x hx y hy
  have hxK : x ∈ K := by by_contra H; exact ha (hx.symm.trans ((hbad x).mpr H))
  have hyK : y ∈ K := by by_contra H; exact ha (hy.symm.trans ((hbad y).mpr H))
  refine ⟨hxK,hyK,?_⟩
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hVcov hxK)
  have Hxy := congrFun (hx.trans hy.symm) i
  have hiy : y ∈ V i := by
    by_contra H
    simp [P,hi,H] at Hxy
  exact Hδ (e i) x hi.2 y hiy.2

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem orbit_name_cover_of_reset {Y : Type*} {T : Y → Y} {R : Y → Y → Prop}
    {M : ℕ} (hM : 1 ≤ M) (hstep : StepCover T R M)
    (N : ℕ) (bad : ℕ → Prop) [DecidablePred bad]
    (E : Set Y) (hinit : RelationDiameter R E)
    (hreset : ∀ k < N, ¬bad (k+1) → ∀ F ⊆ E,
      RelationDiameter R (T^[k] '' F) → RelationDiameter R (T^[k+1] '' F)) :
    ∃ s : Finset (Set Y), E ⊆ ⋃ F ∈ s, F ∧
      s.card ≤ M^(((Finset.range (N+1)).filter fun j => bad j).card) ∧
      ∀ F ∈ s, F ⊆ E ∧ ∀ j ≤ N, RelationDiameter R (T^[j] '' F) := by
  classical
  have hM0 : 0 < M := hM
  have aux : ∀ k ≤ N, ∃ s : Finset (Set Y), E ⊆ ⋃ F ∈ s, F ∧
      s.card ≤ M^((Finset.range (k+1)).filter fun j => bad j).card ∧
      ∀ F ∈ s, F ⊆ E ∧ ∀ j ≤ k, RelationDiameter R (T^[j] '' F) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨{E},by simp,?_,?_⟩
      · simp only [Finset.card_singleton]
        exact Nat.one_le_pow _ _ hM0
      · intro F hF
        have hFE : F = E := by simpa using hF
        subst F
        refine ⟨Set.Subset.refl _,?_⟩
        intro j hj
        have hj0 : j = 0 := by omega
        subst j
        simp only [Function.iterate_zero,Set.image_id]
        exact hinit
    | succ k ih =>
      obtain ⟨s,hcov,hcard,hs⟩ := ih (by omega)
      by_cases hb : bad (k+1)
      · choose F hFc hFp using fun C : s => stepCover_of_image hstep k C.val
          ((hs C.val C.property).2 k le_rfl)
        let t : Finset (Set Y) := s.attach.biUnion fun C => Finset.univ.image (F C)
        refine ⟨t,?_,?_,?_⟩
        · intro x hx
          obtain ⟨C,hC,hxC⟩ := Set.mem_iUnion₂.mp (hcov hx)
          obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hFc ⟨C,hC⟩ hxC)
          exact Set.mem_iUnion₂.mpr ⟨F ⟨C,hC⟩ i,
            Finset.mem_biUnion.mpr ⟨⟨C,hC⟩,by simp,Finset.mem_image.mpr ⟨i,by simp,rfl⟩⟩,hi⟩
        · have ht : t.card ≤ s.card*M := by
            calc
              t.card ≤ ∑ C ∈ s.attach, (Finset.univ.image (F C)).card := Finset.card_biUnion_le
              _ ≤ ∑ _C ∈ s.attach, M := Finset.sum_le_sum fun C _ =>
                (Finset.card_image_le).trans_eq (by simp)
              _ = s.card*M := by simp
          calc
            t.card ≤ s.card*M := ht
            _ ≤ M^((Finset.range (k+1)).filter fun j => bad j).card *M :=
              Nat.mul_le_mul_right M hcard
            _ = _ := by
              rw [Finset.range_add_one (n := k+1),Finset.filter_insert]
              simp only [hb,ite_true, if_true]
              rw [Finset.card_insert_of_notMem, pow_succ]
              simp only [Finset.mem_filter,Finset.mem_range,lt_self_iff_false,false_and,not_false_eq_true]
        · intro C hC
          obtain ⟨D,hD,hCi⟩ := Finset.mem_biUnion.mp hC
          obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hCi
          refine ⟨(hFp D i).1.trans (hs D.val D.property).1,?_⟩
          intro j hj
          by_cases heq : j = k+1
          · subst j
            exact (hFp D i).2
          · have hd := (hs D.val D.property).2 j (by omega)
            intro x hx y hy
            exact hd x (Set.image_mono (hFp D i).1 hx) y (Set.image_mono (hFp D i).1 hy)
      · refine ⟨s,hcov,?_,?_⟩
        · simpa only [Finset.range_add_one (n := k+1),Finset.filter_insert,hb,ite_false, if_false] using hcard
        · intro C hC
          refine ⟨(hs C hC).1,?_⟩
          intro j hj
          by_cases heq : j = k+1
          · subst j
            exact hreset k (by omega) hb C (hs C hC).1 ((hs C hC).2 k le_rfl)
          · exact (hs C hC).2 j (by omega)
  exact aux N le_rfl

end PrimeDegreePackets

open scoped BigOperators Topology ENNReal Classical Matrix
namespace PrimeDegreePackets

 

lemma stepCover_of_matrix_expansion {n : ℕ} (D : G n ≃* G n) {L : ℝ}
    (hL : 0 ≤ L) (hexpand : ∀ r : ℝ, 0 < r → D '' matrixBall n r ⊆ matrixBall n (L*r)) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ r : ℝ, 0 < r → L*r ≤ 1 →
      StepCover D (fun g h => g⁻¹*h ∈ matrixBall n r) M := by
  obtain ⟨M,hM,HM⟩ := small_matrix_ball_cover n hL
  refine ⟨M,hM,?_⟩
  intro r hr hrL E hE
  by_cases hne : E.Nonempty
  · obtain ⟨g,hg⟩ := hne
    obtain ⟨F,hcov,hF⟩ := HM r hr hrL
    refine ⟨fun i => E ∩ (fun h => D (g⁻¹*h)) ⁻¹' F i,?_,?_⟩
    · intro h hh
      have Hin : D (g⁻¹*h) ∈ matrixBall n (L*r) := hexpand r hr ⟨_,hE g hg h hh,rfl⟩
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hcov Hin)
      exact Set.mem_iUnion.mpr ⟨i,hh,hi⟩
    · intro i
      refine ⟨Set.inter_subset_left,?_⟩
      rintro u ⟨h,hh,rfl⟩ v ⟨k,hk,rfl⟩
      have H := (hF i).2 _ hh.2 _ hk.2
      simpa only [map_mul,map_inv,_root_.mul_inv_rev,inv_inv,mul_assoc,mul_inv_cancel_left,
        inv_mul_cancel_left] using H
  · refine ⟨fun _ => ∅,?_,?_⟩
    · simp only [Set.not_nonempty_iff_eq_empty] at hne
      simp [hne]
    · intro i
      simp [RelationDiameter]



lemma diagonal_conjugation_expansion {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ r : ℝ, 0 < r →
      (MulAut.conj (diagonalOneParameter ell hell (-1))) '' matrixBall n r ⊆ matrixBall n (L*r) := by
  let L : ℝ := 1 + ∑ i : Fin n, ∑ j : Fin n, Real.exp (ell j-ell i)
  have hsum : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, Real.exp (ell j-ell i) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
  refine ⟨L,by dsimp [L] <;> linarith,?_⟩
  rintro r hr g ⟨h,hh,rfl⟩ i j
  have he : (MulAut.conj (diagonalOneParameter ell hell (-1)) h).1 i j =
      Real.exp (ell j-ell i)*h.1 i j := by
    change (diagonalOneParameter ell hell (-1)*h*(diagonalOneParameter ell hell (-1))⁻¹).1 i j = _
    rw [← diagonalOneParameter_neg]
    convert conjugation_entry ell hell h (-1) i j using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring
  have hLij : Real.exp (ell j-ell i) ≤ L := by
    have H : Real.exp (ell j-ell i) ≤ ∑ i : Fin n, ∑ j : Fin n, Real.exp (ell j-ell i) :=
      (Finset.single_le_sum (f := fun k : Fin n => Real.exp (ell k-ell i))
        (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun k : Fin n => ∑ l : Fin n, Real.exp (ell l-ell k))
          (fun _ _ => Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
          (Finset.mem_univ i))
    dsimp [L]
    linarith
  change |(MulAut.conj (diagonalOneParameter ell hell (-1)) h).1 i j -
    (1 : Matrix (Fin n) (Fin n) ℝ) i j| < L*r
  rw [he]
  by_cases hij : i = j
  · subst j
    simpa only [sub_self,Real.exp_zero,one_mul] using (hh i i).trans_le
      (le_mul_of_one_le_left hr.le (by dsimp [L] <;> linarith))
  · have Hh : |h.1 i j| < r := by simpa only [Matrix.one_apply_ne hij,sub_zero] using hh i j
    simp only [Matrix.one_apply_ne hij,sub_zero]
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    exact (mul_lt_mul_of_pos_left Hh (Real.exp_pos _)).trans_le
      (mul_le_mul_of_nonneg_right hLij hr.le)

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma rightAction_conjugation {n : ℕ} (a : G n) (x : X n) (g : G n) :
    rightAction (rightAction x g) a =
      rightAction (rightAction x a) (MulAut.conj a⁻¹ g) := by
  simp only [rightAction_mul,MulAut.conj_apply,inv_inv]
  congr 1
  group

lemma rightAction_iterate_conjugation {n : ℕ} (a : G n) (x : X n) (g : G n) (k : ℕ) :
    (fun y => rightAction y a)^[k] (rightAction x g) =
      rightAction ((fun y => rightAction y a)^[k] x) ((MulAut.conj a⁻¹)^[k] g) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih,rightAction_conjugation]
    simp only [Function.iterate_succ_apply']

 

theorem homogeneous_lifted_name_cover {n : ℕ} (a : G n) {L r ρ : ℝ} {M : ℕ}
    (hL : 1 ≤ L) (hr : 0 < r) (hρr : ρ ≤ r) (hM : 1 ≤ M)
    (hexpand : (MulAut.conj a⁻¹) '' matrixBall n r ⊆ matrixBall n (L*r))
    (hstep : StepCover (MulAut.conj a⁻¹) (fun g h => g⁻¹*h ∈ matrixBall n r) M)
    (K : Set (X n))
    (hinj : ∀ y ∈ K, Set.InjOn (fun g => rightAction y g) (matrixBall n (L*r)))
    {α : Type*} (P : X n → α) (bad : α → Prop) [DecidablePred bad]
    (hfine : ∀ b, ¬bad b → ∀ y, P y = b → ∀ z, P z = b →
      y ∈ K ∧ z ∈ K ∧ ∃ h ∈ matrixBall n ρ, rightAction y h = z)
    (x : X n) (N : ℕ) (name : ℕ → α) (E : Set (G n))
    (hinit : RelationDiameter (fun g h : G n => g⁻¹*h ∈ matrixBall n r) E)
    (hname : ∀ g ∈ E, ∀ j ≤ N,
      P ((fun y => rightAction y a)^[j] (rightAction x g)) = name j) :
    ∃ s : Finset (Set (G n)), E ⊆ ⋃ F ∈ s, F ∧
      s.card ≤ M^((Finset.range (N+1)).filter fun j => bad (name j)).card ∧
      ∀ F ∈ s, F ⊆ E ∧ ∀ j ≤ N,
        RelationDiameter (fun g h : G n => g⁻¹*h ∈ matrixBall n r)
          ((MulAut.conj a⁻¹)^[j] '' F) := by
  apply orbit_name_cover_of_reset hM hstep N (fun j => bad (name j)) E hinit
  intro k hk hgood F hFE hF
  rintro u ⟨g,hg,rfl⟩ v ⟨h,hh,rfl⟩
  let D := MulAut.conj a⁻¹
  let T := fun y : X n => rightAction y a
  let u := D^[k+1] g
  let v := D^[k+1] h
  have huv : u⁻¹*v ∈ matrixBall n (L*r) := by
    have H := hexpand ⟨(D^[k] g)⁻¹*(D^[k] h),
      hF _ ⟨g,hg,rfl⟩ _ ⟨h,hh,rfl⟩,rfl⟩
    change D ((D^[k] g)⁻¹*(D^[k] h)) ∈ matrixBall n (L*r) at H
    rw [map_mul,map_inv] at H
    simpa only [u,v,Function.iterate_succ_apply'] using H
  have hgname : P (rightAction (T^[k+1] x) u) = name (k+1) := by
    rw [← rightAction_iterate_conjugation]
    exact hname g (hFE hg) (k+1) (by omega)
  have hhname : P (rightAction (T^[k+1] x) v) = name (k+1) := by
    rw [← rightAction_iterate_conjugation]
    exact hname h (hFE hh) (k+1) (by omega)
  obtain ⟨hyK,_,w,hw,hyw⟩ := hfine (name (k+1)) hgood _ hgname _ hhname
  have hrL : r ≤ L*r := le_mul_of_one_le_left hr.le hL
  have hwL := matrixBall_mono (hρr.trans hrL) hw
  have heq : u⁻¹*v = w := hinj _ hyK huv hwL (by
    change rightAction (rightAction (T^[k+1] x) u) (u⁻¹*v) =
      rightAction (rightAction (T^[k+1] x) u) w
    rw [hyw]
    simp only [rightAction_mul,mul_inv_cancel_left])
  change u⁻¹*v ∈ matrixBall n r
  rw [heq]
  exact matrixBall_mono hρr hw

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma conjugation_iterate {H : Type*} [Group H] (a g : H) (j : ℕ) :
    (MulAut.conj a⁻¹)^[j] g = (a^j)⁻¹*g*a^j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',ih]
    simp only [MulAut.conj_apply,inv_inv,pow_succ,_root_.mul_inv_rev]
    group

 

lemma branch_midpoint_tube {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (x : X n) (g h : G n) (t : ℕ) {r : ℝ}
    (h0 : g⁻¹*h ∈ matrixBall n r)
    (h2 : ((MulAut.conj (diagonalOneParameter ell hell 1)⁻¹)^[2*t] g)⁻¹ *
      ((MulAut.conj (diagonalOneParameter ell hell 1)⁻¹)^[2*t] h) ∈ matrixBall n r) :
    ∃ w ∈ twoSidedTube ell hell r (t:ℝ),
      rightAction ((fun y => rightAction y (diagonalOneParameter ell hell 1))^[t]
        (rightAction x g)) w =
        (fun y => rightAction y (diagonalOneParameter ell hell 1))^[t] (rightAction x h) := by
  let a := diagonalOneParameter ell hell 1
  let b := a^t
  let w := b⁻¹*(g⁻¹*h)*b
  refine ⟨w,?_,?_⟩
  · constructor
    · rw [diagonalOneParameter_neg,diagonalOneParameter_nat]
      have Hp : a^(2*t) = b*b := by dsimp [b]; rw [two_mul,pow_add]
      have He : (a^t)⁻¹*w*a^t =
          ((MulAut.conj a⁻¹)^[2*t] g)⁻¹*((MulAut.conj a⁻¹)^[2*t] h) := by
        simp only [conjugation_iterate,Hp]
        dsimp [w,b,a]
        group
      rw [He]
      exact h2
    · rw [diagonalOneParameter_neg,diagonalOneParameter_nat]
      have He : (diagonalOneParameter ell hell 1)^t*w*((diagonalOneParameter ell hell 1)^t)⁻¹ = g⁻¹*h := by
        dsimp [w,b,a]
        group
      rw [He]
      exact h0
  · rw [rightAction_iterate,rightAction_iterate,rightAction_mul,rightAction_mul,rightAction_mul]
    congr 1
    dsimp [w,b,a]
    group

 

lemma rightAction_iterate_measure_preimage {n : ℕ} (μ : Measure (X n)) (a : G n)
    (hT : MeasurePreserving (fun x => rightAction x a) μ μ) (t : ℕ) (S : Set (X n)) :
    μ ((fun x => (fun y => rightAction y a)^[t] x) ⁻¹' S) = μ S := by
  apply (hT.iterate t).measure_preimage_emb
  have heq : (fun x => rightAction x a)^[t] = fun x => rightAction x (a^t) :=
    funext (rightAction_iterate a t)
  rw [heq]
  exact (rightActionHomeomorph (a^t)).isOpenEmbedding.measurableEmbedding

 

theorem lifted_branch_mass {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (μ : Measure (X n))
    (hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell 1)) μ μ)
    (K : Set (X n)) {r : ℝ} (t : ℕ) (B : ℝ≥0∞)
    (hTube : ∀ y ∈ K, μ ((fun w => rightAction y w) '' twoSidedTube ell hell r t) ≤ B)
    (x : X n) (F : Set (G n))
    (hmid : ∀ g ∈ F, (fun y => rightAction y (diagonalOneParameter ell hell 1))^[t]
      (rightAction x g) ∈ K)
    (h0 : RelationDiameter (fun g h : G n => g⁻¹*h ∈ matrixBall n r) F)
    (h2 : RelationDiameter (fun g h : G n => g⁻¹*h ∈ matrixBall n r)
      ((MulAut.conj (diagonalOneParameter ell hell 1)⁻¹)^[2*t] '' F)) :
    μ ((fun g => rightAction x g) '' F) ≤ B := by
  by_cases hne : F.Nonempty
  · obtain ⟨g,hg⟩ := hne
    let T := fun y => rightAction y (diagonalOneParameter ell hell 1)
    let y := T^[t] (rightAction x g)
    have hsub : (fun g => rightAction x g) '' F ⊆
        (T^[t]) ⁻¹' ((fun w => rightAction y w) '' twoSidedTube ell hell r t) := by
      rintro z ⟨h,hh,rfl⟩
      exact branch_midpoint_tube ell hell x g h t (h0 g hg h hh)
        (h2 _ ⟨g,hg,rfl⟩ _ ⟨h,hh,rfl⟩)
    calc
      μ _ ≤ μ ((T^[t]) ⁻¹' ((fun w => rightAction y w) '' twoSidedTube ell hell r t)) := measure_mono hsub
      _ = μ ((fun w => rightAction y w) '' twoSidedTube ell hell r t) :=
        rightAction_iterate_measure_preimage μ _ hT t _
      _ ≤ B := hTube y (hmid g hg)
  · simp only [Set.not_nonempty_iff_eq_empty] at hne
    simp [hne]

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_AtomMass
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
namespace PrimeDegreePackets

lemma small_matrixBall_pairwise (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧
      RelationDiameter (fun g h : G n => g⁻¹*h ∈ matrixBall n r) (matrixBall n ρ) := by
  obtain ⟨V,hV,_,hVi,hVV⟩ := exists_closed_nhds_one_inv_eq_mul_subset
    ((matrixBall_isOpen n r).mem_nhds (one_mem_matrixBall n hr))
  obtain ⟨ρ,hρ,hρV⟩ := matrixBall_nhds_basis hV
  refine ⟨min ρ r,lt_min hρ hr,min_le_right _ _,?_⟩
  intro g hg h hh
  apply hVV
  refine Set.mul_mem_mul ?_ (hρV (matrixBall_mono (min_le_left _ _) hh))
  rw [← hVi]
  exact Set.inv_mem_inv.mpr (hρV (matrixBall_mono (min_le_left _ _) hg))

 

theorem homogeneous_name_atom_mass {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (μ : Measure (X n))
    (hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell 1)) μ μ)
    {L r ρ : ℝ} {M : ℕ} (hL : 1 ≤ L) (hr : 0 < r) (hρr : ρ ≤ r) (hM : 1 ≤ M)
    (hdiam : RelationDiameter (fun g h : G n => g⁻¹*h ∈ matrixBall n r) (matrixBall n ρ))
    (hexpand : (MulAut.conj (diagonalOneParameter ell hell 1)⁻¹) '' matrixBall n r ⊆ matrixBall n (L*r))
    (hstep : StepCover (MulAut.conj (diagonalOneParameter ell hell 1)⁻¹)
      (fun g h => g⁻¹*h ∈ matrixBall n r) M)
    (K : Set (X n))
    (hinj : ∀ y ∈ K, Set.InjOn (fun g => rightAction y g) (matrixBall n (L*r)))
    {α : Type*} (P : X n → α) (bad : α → Prop) [DecidablePred bad]
    (hfine : ∀ b, ¬bad b → ∀ y, P y = b → ∀ z, P z = b →
      y ∈ K ∧ z ∈ K ∧ ∃ h ∈ matrixBall n ρ, rightAction y h = z)
    (t : ℕ) (name : ℕ → α) (hfirst : ¬bad (name 0))
    (A : Set (X n))
    (hname : ∀ y ∈ A, ∀ j ≤ 2*t,
      P ((fun x => rightAction x (diagonalOneParameter ell hell 1))^[j] y) = name j)
    (hmid : ∀ y ∈ A, (fun x => rightAction x (diagonalOneParameter ell hell 1))^[t] y ∈ K)
    (B : ℝ≥0∞)
    (hTube : ∀ y ∈ K, μ ((fun w => rightAction y w) '' twoSidedTube ell hell r t) ≤ B) :
    μ A ≤ (M^((Finset.range (2*t+1)).filter fun j => bad (name j)).card : ℕ)*B := by
  by_cases hne : A.Nonempty
  · obtain ⟨x,hx⟩ := hne
    let E : Set (G n) := {g | g ∈ matrixBall n ρ ∧ rightAction x g ∈ A}
    have hE : RelationDiameter (fun g h : G n => g⁻¹*h ∈ matrixBall n r) E :=
      fun g hg h hh => hdiam g hg.1 h hh.1
    have hNE : ∀ g ∈ E, ∀ j ≤ 2*t,
        P ((fun y => rightAction y (diagonalOneParameter ell hell 1))^[j] (rightAction x g)) = name j :=
      fun g hg j hj => hname _ hg.2 j hj
    obtain ⟨s,hcov,hcard,hs⟩ := homogeneous_lifted_name_cover
      (diagonalOneParameter ell hell 1) hL hr hρr hM hexpand hstep K hinj P bad hfine
      x (2*t) name E hE hNE
    have hAsub : A ⊆ ⋃ F ∈ s, (fun g => rightAction x g) '' F := by
      intro y hy
      have hxname : P x = name 0 := by simpa using hname x hx 0 (by omega)
      have hyname : P y = name 0 := by simpa using hname y hy 0 (by omega)
      obtain ⟨_,_,g,hg,hxy⟩ := hfine (name 0) hfirst x hxname y hyname
      have hgE : g ∈ E := ⟨hg,hxy ▸ hy⟩
      obtain ⟨F,hF,hgF⟩ := Set.mem_iUnion₂.mp (hcov hgE)
      exact Set.mem_iUnion₂.mpr ⟨F,hF,g,hgF,hxy⟩
    have hFB : ∀ F ∈ s, μ ((fun g => rightAction x g) '' F) ≤ B := by
      intro F hF
      apply lifted_branch_mass ell hell μ hT K t B hTube x F
      · intro g hg
        exact hmid _ ((hs F hF).1 hg).2
      · simpa only [Function.iterate_zero,Set.image_id] using (hs F hF).2 0 (by omega)
      · exact (hs F hF).2 (2*t) le_rfl
    calc
      μ A ≤ μ (⋃ F ∈ s, (fun g => rightAction x g) '' F) := measure_mono hAsub
      _ ≤ ∑ F ∈ s, μ ((fun g => rightAction x g) '' F) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _F ∈ s, B := Finset.sum_le_sum hFB
      _ = s.card*B := by simp [nsmul_eq_mul]
      _ ≤ _ := by gcongr
  · simp only [Set.not_nonempty_iff_eq_empty] at hne
    simp [hne]

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma entropyGoodSet_measurable {Y : Type*} [MeasurableSpace Y] {T : Y → Y}
    (hT : Measurable T) {K : Set Y} (hK : MeasurableSet K) (ε : ℝ) (N : ℕ) :
    MeasurableSet (entropyGoodSet T K ε N) :=
  (hK.inter (hK.preimage (hT.iterate _))).inter
    (measurableSet_le (measurable_visitCount hT hK.compl N) measurable_const)

 

theorem entropyGoodSet_mass {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {K : Set Y} (hK : MeasurableSet K) {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 0 < N) :
    1-(2+1/ε)*μ.real Kᶜ ≤ μ.real (entropyGoodSet T K ε N) := by
  let A := entropyGoodSet T K ε N
  have hA : MeasurableSet A := entropyGoodSet_measurable hT.measurable hK ε N
  have hsub : Aᶜ ⊆ Kᶜ ∪ (T^[(N-1)/2]) ⁻¹' Kᶜ ∪
      {x | ε*N < (visitCount T Kᶜ N x : ℝ)} := by
    intro x hx
    simp only [A,entropyGoodSet,Set.mem_compl_iff,Set.mem_inter_iff,
      Set.mem_preimage,Set.mem_ofPred_eq,not_and,not_le] at hx
    by_cases hxK : x ∈ K
    · by_cases hxT : T^[(N-1)/2] x ∈ K
      · exact Or.inr (hx ⟨hxK,hxT⟩)
      · exact Or.inl (Or.inr hxT)
    · exact Or.inl (Or.inl hxK)
  have hbad : μ.real {x | ε*N < (visitCount T Kᶜ N x : ℝ)} ≤ μ.real Kᶜ/ε := by
    have H := ENNReal.toReal_mono ENNReal.ofReal_ne_top (measure_many_visits μ hT hK.compl hN hε)
    calc
      μ.real {x | ε*N < (visitCount T Kᶜ N x : ℝ)} ≤
          (ENNReal.ofReal (μ.real Kᶜ/ε)).toReal := H
      _ = μ.real Kᶜ/ε := ENNReal.toReal_ofReal (div_nonneg measureReal_nonneg hε.le)
  have hpre : μ.real ((T^[(N-1)/2]) ⁻¹' Kᶜ) = μ.real Kᶜ :=
    congrArg ENNReal.toReal ((hT.iterate _).measure_preimage hK.compl.nullMeasurableSet)
  have H : μ.real Aᶜ ≤ 2*μ.real Kᶜ+μ.real Kᶜ/ε := by
    calc
      μ.real Aᶜ ≤ μ.real (Kᶜ ∪ (T^[(N-1)/2]) ⁻¹' Kᶜ ∪
          {x | ε*N < (visitCount T Kᶜ N x : ℝ)}) := measureReal_mono hsub
      _ ≤ μ.real (Kᶜ ∪ (T^[(N-1)/2]) ⁻¹' Kᶜ) +
          μ.real {x | ε*N < (visitCount T Kᶜ N x : ℝ)} := measureReal_union_le _ _
      _ ≤ (μ.real Kᶜ+μ.real ((T^[(N-1)/2]) ⁻¹' Kᶜ))+μ.real Kᶜ/ε :=
        add_le_add (measureReal_union_le _ _) hbad
      _ = _ := by rw [hpre]; ring
  rw [measureReal_compl hA,probReal_univ] at H
  dsimp [A] at H
  have He : (2+1/ε)*μ.real Kᶜ = 2*μ.real Kᶜ+μ.real Kᶜ/ε := by ring
  rw [He]
  linarith

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma tendsto_entropyMidpoint : Tendsto (fun N : ℕ => (N-1)/2) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (2*b+1)] with N hN
  omega

 

lemma branching_exp_bound {M b N : ℕ} (hM : 1 ≤ M) {ε δ C : ℝ}
    (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hb : (b:ℝ) ≤ ε*N) :
    (M^b : ℕ)*ENNReal.ofReal (C*Real.exp (-δ*((N-1)/2 : ℕ))) ≤
      ENNReal.ofReal ((C*Real.exp δ)*Real.exp (-(δ/2-ε*Real.log M)*N)) := by
  have hM0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hlog : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hmid : (N:ℝ) ≤ 2*((N-1)/2 : ℕ)+2 := by
    exact_mod_cast (show N ≤ 2*((N-1)/2)+2 by omega)
  have hexp : (M:ℝ)^b ≤ Real.exp (ε*N*Real.log M) := by
    calc
      (M:ℝ)^b = Real.exp ((b:ℝ)*Real.log M) := by rw [Real.exp_nat_mul,Real.exp_log hM0]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hb hlog)
  have hE : ε*N*Real.log M-δ*((N-1)/2 : ℕ) ≤ δ-(δ/2-ε*Real.log M)*N := by
    nlinarith
  have H : (M:ℝ)^b*(C*Real.exp (-δ*((N-1)/2 : ℕ))) ≤
      (C*Real.exp δ)*Real.exp (-(δ/2-ε*Real.log M)*N) := by
    calc
      _ ≤ Real.exp (ε*N*Real.log M)*(C*Real.exp (-δ*((N-1)/2 : ℕ))) :=
        mul_le_mul_of_nonneg_right hexp (mul_nonneg hC (Real.exp_pos _).le)
      _ = C*Real.exp (ε*N*Real.log M-δ*((N-1)/2 : ℕ)) := by
        rw [sub_eq_add_neg, Real.exp_add, neg_mul]
        ring
      _ ≤ C*Real.exp (δ-(δ/2-ε*Real.log M)*N) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE) hC
      _ = _ := by
        rw [sub_eq_add_neg, Real.exp_add, neg_mul]
        ring
  have heq : (M^b : ℕ)*ENNReal.ofReal (C*Real.exp (-δ*((N-1)/2 : ℕ))) =
      ENNReal.ofReal ((M:ℝ)^b*(C*Real.exp (-δ*((N-1)/2 : ℕ)))) := by
    conv_rhs => rw [ENNReal.ofReal_mul (pow_nonneg (Nat.cast_nonneg M) b),
      ENNReal.ofReal_pow (Nat.cast_nonneg M), ENNReal.ofReal_natCast]
    simp
  rw [heq]
  exact ENNReal.ofReal_le_ofReal H

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem good_name_atom_mass {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (μ : Measure (X n))
    (hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell 1)) μ μ)
    {L r ρ : ℝ} {M : ℕ} (hL : 1 ≤ L) (hr : 0 < r) (hρr : ρ ≤ r) (hM : 1 ≤ M)
    (hdiam : RelationDiameter (fun g h : G n => g⁻¹*h ∈ matrixBall n r) (matrixBall n ρ))
    (hexpand : (MulAut.conj (diagonalOneParameter ell hell 1)⁻¹) '' matrixBall n r ⊆ matrixBall n (L*r))
    (hstep : StepCover (MulAut.conj (diagonalOneParameter ell hell 1)⁻¹)
      (fun g h => g⁻¹*h ∈ matrixBall n r) M)
    (K : Set (X n))
    (hinj : ∀ y ∈ K, Set.InjOn (fun g => rightAction y g) (matrixBall n (L*r)))
    {α : Type*} (P : X n → α) (bad : α → Prop) [DecidablePred bad]
    (hbad : ∀ x, bad (P x) ↔ x ∉ K)
    (hfine : ∀ b, ¬bad b → ∀ y, P y = b → ∀ z, P z = b →
      y ∈ K ∧ z ∈ K ∧ ∃ h ∈ matrixBall n ρ, rightAction y h = z)
    {ε δ C : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C) {N : ℕ} (hN : 0 < N)
    (hTube : ∀ y ∈ K, μ ((fun w => rightAction y w) ''
      twoSidedTube ell hell r (((N-1)/2 : ℕ) : ℝ)) ≤ ENNReal.ofReal (C*Real.exp (-δ*((N-1)/2 : ℕ))))
    (a : Fin N → α) :
    μ (entropyGoodSet (fun x => rightAction x (diagonalOneParameter ell hell 1)) K ε N ∩
        {y | orbitName (fun x => rightAction x (diagonalOneParameter ell hell 1)) P N y = a}) ≤
      ENNReal.ofReal ((C*Real.exp δ)*Real.exp (-(δ/2-ε*Real.log M)*N)) := by
  let T : X n → X n := fun x => rightAction x (diagonalOneParameter ell hell 1)
  let A := entropyGoodSet T K ε N ∩ {y | orbitName T P N y = a}
  change μ A ≤ _
  by_cases hne : A.Nonempty
  · obtain ⟨x,hx⟩ := hne
    let name : ℕ → α := fun j => P (T^[j] x)
    have hnlen : 2*((N-1)/2)+1 ≤ N := by omega
    have hname : ∀ y ∈ A, ∀ j ≤ 2*((N-1)/2), P (T^[j] y) = name j := by
      intro y hy j hj
      have H := congrFun (hy.2.trans hx.2.symm) ⟨j,by omega⟩
      exact H
    have hfirst : ¬bad (name 0) := by
      simpa only [name,Function.iterate_zero,id_eq] using (not_congr (hbad x)).mpr (not_not.mpr hx.1.1.1)
    have hmid : ∀ y ∈ A, T^[(N-1)/2] y ∈ K := fun y hy => hy.1.1.2
    have hb : (((Finset.range (2*((N-1)/2)+1)).filter fun j => bad (name j)).card : ℝ) ≤ ε*N := by
      have hsub : (Finset.range (2*((N-1)/2)+1)).filter (fun j => bad (name j)) ⊆
          (Finset.range N).filter (fun j => T^[j] x ∈ Kᶜ) := by
        intro j hj
        obtain ⟨hj0,hj1⟩ := Finset.mem_filter.mp hj
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hj0; omega),?_⟩
        exact (hbad _).mp hj1
      have hc : (((Finset.range (2*((N-1)/2)+1)).filter fun j => bad (name j)).card : ℝ) ≤
          visitCount T Kᶜ N x := by
        have H := (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card hsub)
        convert H using 1 <;> first | (with_reducible_and_instances rfl) | (congr 2)
        unfold visitCount
        congr 1
        ext j
        simp only [Finset.mem_filter]

      exact hc.trans hx.1.2
    have H := homogeneous_name_atom_mass ell hell μ hT hL hr hρr hM hdiam hexpand hstep K hinj
      P bad hfine ((N-1)/2) name hfirst A hname hmid _ hTube
    exact H.trans (branching_exp_bound hM hδ hC hb)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    simp [hne]

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem entropy_lower_of_ordinary_balls {d : ℕ} (μ : Measure (X (d+1)))
    [IsProbabilityMeasure μ] (hball : OrdinaryBallBound (d+1) μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i = 0)
    (hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell 1)) μ μ)
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ i j, i ≠ j → δ ≤ |ell i-ell j|) :
    ENNReal.ofReal (δ/3) ≤ measureEntropy μ
      (fun x => rightAction x (diagonalOneParameter ell hell 1)) := by
  let T : X (d+1) → X (d+1) := fun x => rightAction x (diagonalOneParameter ell hell 1)
  obtain ⟨L,hL,hexpand0⟩ := diagonal_conjugation_expansion ell hell
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hexpand : ∀ r : ℝ, 0 < r →
      (MulAut.conj (diagonalOneParameter ell hell 1)⁻¹) '' matrixBall (d+1) r ⊆
        matrixBall (d+1) (L*r) := by
    simpa only [diagonalOneParameter_neg] using hexpand0
  obtain ⟨M,hM,hstep⟩ := stepCover_of_matrix_expansion
    (MulAut.conj (diagonalOneParameter ell hell 1)⁻¹) hLpos.le hexpand
  have hlog : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  let ε : ℝ := δ/(12*(1+Real.log M))
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hεlog : ε*Real.log M ≤ δ/12 := by
    have H : ε*(12*(1+Real.log M)) = δ := div_mul_cancel₀ _ (by positivity)
    nlinarith
  let η : ℝ := 1/(5*(2+1/ε))
  have hη : 0 < η := by positivity
  obtain ⟨K,_,hK,hKsmall⟩ := (MeasurableSet.univ : MeasurableSet (Set.univ : Set (X (d+1)))).exists_isCompact_sdiff_lt
    (measure_ne_top μ Set.univ) (show ENNReal.ofReal η ≠ 0 by exact ne_of_gt (ENNReal.ofReal_pos.mpr hη))
  have hKc : μ.real Kᶜ ≤ η := by
    have H : μ Kᶜ ≤ ENNReal.ofReal η := by simpa only [compl_eq_univ_sdiff] using hKsmall.le
    have H' := ENNReal.toReal_mono ENNReal.ofReal_ne_top H
    simpa only [measureReal_def,ENNReal.toReal_ofReal hη.le] using H'
  have hweight : 4/5 ≤ 1-(2+1/ε)*μ.real Kᶜ := by
    have H := mul_le_mul_of_nonneg_left hKc (show 0 ≤ 2+1/ε by positivity)
    have Hη : (2+1/ε)*η = 1/5 := by dsimp [η]; field_simp
    rw [Hη] at H
    linarith
  obtain ⟨r₀,hr₀,hinj₀⟩ := compact_uniform_chart_injective K hK
  let r : ℝ := min (r₀/L) (min (1/L) (1/8))
  have hr : 0 < r := lt_min (div_pos hr₀ hLpos) (lt_min (div_pos zero_lt_one hLpos) (by norm_num))
  have hLr0 : L*r ≤ r₀ := by
    have H := (le_div_iff₀ hLpos).mp (min_le_left (r₀/L) (min (1/L) (1/8)))
    simpa only [mul_comm] using H
  have hLr1 : L*r ≤ 1 := by
    have H := (le_div_iff₀ hLpos).mp ((min_le_right (r₀/L) (min (1/L) (1/8))).trans (min_le_left _ _))
    simpa only [mul_comm] using H
  have hrquarter : r < 1/4 := (le_trans (min_le_right _ _) (min_le_right _ _)).trans_lt (by norm_num)
  have hinj : ∀ x ∈ K, Set.InjOn (fun g => rightAction x g) (matrixBall (d+1) (L*r)) :=
    fun x hx => (hinj₀ x hx).mono (matrixBall_mono hLr0)
  obtain ⟨ρ,hρ,hρr,hdiam⟩ := small_matrixBall_pairwise (d+1) hr
  obtain ⟨k,P₀,hP₀,hbad₀,hfine₀⟩ := compact_finite_observation K hK hρ
  let e := Fintype.equivFin (Fin k → Bool)
  let P : X (d+1) → Fin (Fintype.card (Fin k → Bool)) := fun x => e (P₀ x)
  let bad : Fin (Fintype.card (Fin k → Bool)) → Prop := fun b => e.symm b = (fun _ => false)
  have hP : ∀ a, MeasurableSet {x | P x = a} := by
    intro a
    have H : {x | P x = a} = {x | P₀ x = e.symm a} := by
      ext x
      exact e.eq_symm_apply.symm
    rw [H]
    exact hP₀ _
  have hbad : ∀ x, bad (P x) ↔ x ∉ K := by simpa [bad,P] using hbad₀
  have hfine : ∀ b, ¬bad b → ∀ y, P y = b → ∀ z, P z = b →
      y ∈ K ∧ z ∈ K ∧ ∃ h ∈ matrixBall (d+1) ρ, rightAction y h = z := by
    intro b hb y hy z hz
    exact hfine₀ (e.symm b) hb y (by simpa [P] using congrArg e.symm hy)
      z (by simpa [P] using congrArg e.symm hz)
  obtain ⟨C,hC,hTube⟩ := tube_mass_of_ordinary_balls hball K hK ell hell hδ hr.le hrquarter hgap
  have htend : Tendsto (fun N : ℕ => ((N-1)/2 : ℕ)) atTop atTop := tendsto_entropyMidpoint
  have hTubeN := (tendsto_natCast_atTop_atTop.comp htend).eventually hTube
  let c : ℝ := δ/2-ε*Real.log M
  have hc : 0 ≤ c := by dsimp [c] <;> linarith
  have hsmall : ∀ᶠ N : ℕ in atTop, ∀ a : Fin N → Fin (Fintype.card (Fin k → Bool)),
      μ.real (entropyGoodSet T K ε N ∩ {y | orbitName T P N y = a}) ≤
        (C*Real.exp δ)*Real.exp (-c*N) := by
    filter_upwards [hTubeN,eventually_ge_atTop (1:ℕ)] with N hTN hN
    intro a
    have H := good_name_atom_mass (ε := ε) ell hell μ hT hL hr hρr hM hdiam (hexpand r hr)
      (hstep r hr hLr1) K hinj P bad hbad hfine hδ.le hC.le (show 0 < N by omega) hTN a
    have H' := ENNReal.toReal_mono ENNReal.ofReal_ne_top H
    change μ.real (entropyGoodSet T K ε N ∩ {y | orbitName T P N y = a}) ≤
      (ENNReal.ofReal ((C*Real.exp δ)*Real.exp (-c*N))).toReal at H'
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ (C*Real.exp δ)*Real.exp (-c*N) by positivity)] using H'
  have hw : ∀ᶠ N : ℕ in atTop, (4/5:ℝ) ≤ μ.real (entropyGoodSet T K ε N) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    exact hweight.trans (entropyGoodSet_mass μ hT hK.isClosed.measurableSet hε (by omega))
  have H := measureEntropy_lower_of_good_atoms μ hT _ P hP (entropyGoodSet T K ε)
    (fun N => entropyGoodSet_measurable hT.measurable hK.isClosed.measurableSet ε N)
    hc (show 0 < C*Real.exp δ by positivity) hw hsmall
  apply le_trans (b := ENNReal.ofReal (c*(4/5))) _ H
  apply ENNReal.ofReal_le_ofReal
  dsimp [c]
  linarith

end PrimeDegreePackets


namespace PrimeDegreePackets



theorem entropy_from_ordinary_balls_dominated {d : ℕ}
    (μ ξ : Measure (X (d+1))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ξ]
    (hball : OrdinaryBallBound (d+1) μ)
    (hAξ : ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) ξ = ξ)
    {c : ℝ} (hξ : ξ ≤ ENNReal.ofReal c • μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i = 0)
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ i j, i ≠ j → δ ≤ |ell i-ell j|) :
    ENNReal.ofReal (δ/3) ≤ measureEntropy ξ
      (fun x => rightAction x (diagonalOneParameter ell hell 1)) := by
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal c := by
    simpa only [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one] using hξ Set.univ
  have hc : 0 < c := ENNReal.ofReal_pos.mp (lt_of_lt_of_le zero_lt_one h1)
  have hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell 1)) ξ ξ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hAξ _
  exact entropy_lower_of_ordinary_balls ξ (ordinaryBallBound_of_le hball hc hξ)
    ell hell hT hδ hgap

end PrimeDegreePackets


namespace PrimeDegreePackets


lemma regularDiagonalWeights_separated (d : ℕ) (i j : Fin (d+1)) (hij : i ≠ j) :
    1 ≤ |regularDiagonalWeights d i - regularDiagonalWeights d j| := by
  have h : i.val ≠ j.val := fun H => hij (Fin.ext H)
  have H : regularDiagonalWeights d i - regularDiagonalWeights d j = (i.val:ℝ)-j.val := by
    unfold regularDiagonalWeights
    ring
  rw [H]
  rcases lt_or_gt_of_ne h with h | h
  · have H : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast (show i.val+1 ≤ j.val by omega)
    rw [abs_of_nonpos (by linarith : (i.val:ℝ)-j.val ≤ 0)]
    linarith
  · have H : (j.val:ℝ)+1 ≤ i.val := by exact_mod_cast (show j.val+1 ≤ i.val by omega)
    rw [abs_of_nonneg (by linarith : 0 ≤ (i.val:ℝ)-j.val)]
    linarith

 

theorem positive_entropy_every_dominated_invariant {d : ℕ}
    (μ ξ : Measure (X (d+1))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ξ]
    (hball : OrdinaryBallBound (d+1) μ)
    (hAξ : ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) ξ = ξ)
    {c : ℝ} (hξ : ξ ≤ ENNReal.ofReal c • μ) :
    0 < measureEntropy ξ (fun x => rightAction x
      (diagonalOneParameter (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 1)) := by
  have H := entropy_from_ordinary_balls_dominated μ ξ hball hAξ hξ
    (regularDiagonalWeights d) (regularDiagonalWeights_sum d)
    (δ := 1) zero_lt_one (regularDiagonalWeights_separated d)
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by norm_num : (0:ℝ)<1/3)) H

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_EntropyMixtures
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
namespace PrimeDegreePackets

lemma negMulLog_sum_le {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    Real.negMulLog (∑ i, p i) ≤ ∑ i, Real.negMulLog (p i) := by
  rw [Real.negMulLog, ← Finset.sum_neg_distrib, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  by_cases h0 : p i = 0
  · simp [h0]
  have hi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm h0)
  have hs : p i ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
  exact mul_le_mul_of_nonpos_left (Real.log_le_log hi hs) (neg_nonpos.mpr (hp i))

lemma finiteShannon_mixture_joint {ι α : Type*} [Fintype ι] [Fintype α]
    (w : ι → ℝ) (p : ι → α → ℝ) (hp1 : ∀ i, ∑ a, p i a = 1) :
    finiteShannon (fun z : ι × α => w z.1*p z.1 z.2) =
      finiteShannon w + ∑ i, w i*finiteShannon (p i) := by
  simp only [finiteShannon, Fintype.sum_prod_type, Real.negMulLog_mul,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hp1, one_mul]

lemma finiteShannon_mixture_bounds {ι α : Type*} [Fintype ι] [Fintype α]
    (w : ι → ℝ) (p : ι → α → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hp : ∀ i a, 0 ≤ p i a) (hp1 : ∀ i, ∑ a, p i a = 1) :
    (∑ i, w i*finiteShannon (p i)) ≤ finiteShannon (fun a => ∑ i, w i*p i a) ∧
    finiteShannon (fun a => ∑ i, w i*p i a) ≤
      finiteShannon w + ∑ i, w i*finiteShannon (p i) := by
  constructor
  · simp only [finiteShannon, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro a _
    exact Real.concaveOn_negMulLog.le_map_sum (fun i _ => hw i) hw1 (fun i _ => hp i a)
  · rw [← finiteShannon_mixture_joint w p hp1]
    simp only [finiteShannon, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun a _ => negMulLog_sum_le _ (fun i => mul_nonneg (hw i) (hp i a)))

lemma observationEntropy_finite_mixture_bounds {Y ι α : Type*} [MeasurableSpace Y]
    [Fintype ι] [Fintype α] (μ : Measure Y) [IsProbabilityMeasure μ]
    (ν : ι → Measure Y) [∀ i, IsProbabilityMeasure (ν i)] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hmix : μ = ∑ i, ENNReal.ofReal (w i) • ν i) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    (∑ i, w i*observationEntropy (ν i) P) ≤ observationEntropy μ P ∧
    observationEntropy μ P ≤ finiteShannon w + ∑ i, w i*observationEntropy (ν i) P := by
  have heq a : μ.real {y | P y = a} = ∑ i, w i*(ν i).real {y | P y = a} := by
    rw [hmix]
    simp only [measureReal_def, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw _)]
  simpa only [observationEntropy, heq] using finiteShannon_mixture_bounds w
    (fun i a => (ν i).real {y | P y = a}) hw hw1 (fun i a => measureReal_nonneg)
    (fun i => observation_distribution_sum (ν i) P hP)

 

theorem observationEntropyRate_finite_mixture {Y ι α : Type*} [MeasurableSpace Y]
    [Fintype ι] [Fintype α] (μ : Measure Y) [IsProbabilityMeasure μ]
    (ν : ι → Measure Y) [∀ i, IsProbabilityMeasure (ν i)] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hmix : μ = ∑ i, ENNReal.ofReal (w i) • ν i)
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (hTν : ∀ i, MeasurePreserving T (ν i) (ν i))
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) :
    observationEntropyRate μ T P = ∑ i, w i*observationEntropyRate (ν i) T P := by
  have hleft := tendsto_observationEntropyRate μ hT P hP
  have hright : Tendsto (fun N : ℕ => ∑ i, w i*(observationEntropy (ν i) (orbitName T P N)/(N:ℝ)))
      atTop (𝓝 (∑ i, w i*observationEntropyRate (ν i) T P)) :=
    tendsto_finsetSum _ (fun i _ => tendsto_const_nhds.mul (tendsto_observationEntropyRate (ν i) (hTν i) P hP))
  have hzero : Tendsto (fun N : ℕ => finiteShannon w / (N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlo : ∀ᶠ N : ℕ in atTop,
      (∑ i, w i*(observationEntropy (ν i) (orbitName T P N)/(N:ℝ))) ≤
        observationEntropy μ (orbitName T P N)/(N:ℝ) := by
    filter_upwards [] with N
    have H := (observationEntropy_finite_mixture_bounds μ ν w hw hw1 hmix
      (orbitName T P N) (orbitName_measurable_fiber hT.measurable hP N)).1
    simpa only [Finset.sum_div, mul_div_assoc] using div_le_div_of_nonneg_right H (Nat.cast_nonneg N)
  have hup : ∀ᶠ N : ℕ in atTop,
      observationEntropy μ (orbitName T P N)/(N:ℝ) ≤
        finiteShannon w/(N:ℝ)+(∑ i, w i*(observationEntropy (ν i) (orbitName T P N)/(N:ℝ))) := by
    filter_upwards [] with N
    have H := (observationEntropy_finite_mixture_bounds μ ν w hw hw1 hmix
      (orbitName T P N) (orbitName_measurable_fiber hT.measurable hP N)).2
    simpa only [add_div, Finset.sum_div, mul_div_assoc] using div_le_div_of_nonneg_right H (Nat.cast_nonneg N)
  apply le_antisymm
  · simpa only [zero_add] using le_of_tendsto_of_tendsto hleft (hzero.add hright) hup
  · exact le_of_tendsto_of_tendsto hright hleft hlo

end PrimeDegreePackets

open MeasureTheory ProbabilityTheory Filter Set
namespace PrimeDegreePackets

lemma kernel_comp_real {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    (τ : Measure Z) (κ : Kernel Z Y) [IsMarkovKernel κ]
    {S : Set Y} (hS : MeasurableSet S) :
    (κ ∘ₘ τ).real S = ∫ z, (κ z).real S ∂τ := by
  rw [measureReal_def, Measure.bind_apply hS κ.aemeasurable]
  exact (integral_toReal (κ.measurable_coe hS).aemeasurable
    (ae_of_all _ fun z => measure_lt_top (κ z) S)).symm

lemma kernel_mixture_preserving {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    (τ : Measure Z) (κ : Kernel Z Y) {T : Y → Y} (hT : Measurable T)
    (hκ : ∀ᵐ z ∂τ, MeasurePreserving T (κ z) (κ z)) :
    MeasurePreserving T (κ ∘ₘ τ) (κ ∘ₘ τ) := by
  refine ⟨hT,?_⟩
  rw [Measure.map_comp τ κ hT]
  apply Measure.comp_congr
  filter_upwards [hκ] with z hz
  simpa only [Kernel.map_apply _ hT] using hz.map_eq

variable {Z Y ι : Type*} [MeasurableSpace Z] [MeasurableSpace Y]



lemma kernelCell_preserving (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Kernel Z Y) (Q : Z → ι) (i : ι)
    {T : Y → Y} (hT : Measurable T)
    (hκ : ∀ᵐ z ∂τ, MeasurePreserving T (κ z) (κ z)) :
    MeasurePreserving T (kernelCell τ κ Q i) (kernelCell τ κ Q i) := by
  unfold kernelCell
  split_ifs
  · exact kernel_mixture_preserving τ κ hT hκ
  · exact kernel_mixture_preserving _ κ hT (cond_absolutelyContinuous.ae_le hκ)

lemma weighted_kernelCell (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Kernel Z Y) (Q : Z → ι) (i : ι) :
    ENNReal.ofReal (τ.real {z | Q z = i}) • kernelCell τ κ Q i =
      κ ∘ₘ τ.restrict {z | Q z = i} := by
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  unfold kernelCell
  split_ifs with h
  · rw [h, zero_smul, Measure.restrict_eq_zero.mpr h]
    simp
  · rw [ProbabilityTheory.cond, Measure.comp_smul, smul_smul, ENNReal.mul_inv_cancel h (measure_ne_top _ _), one_smul]

lemma kernel_finite_cells [Fintype ι] (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Kernel Z Y) (Q : Z → ι) (hQ : ∀ i, MeasurableSet {z | Q z = i}) :
    κ ∘ₘ τ = ∑ i, ENNReal.ofReal (τ.real {z | Q z = i}) • kernelCell τ κ Q i := by
  simp_rw [weighted_kernelCell]
  have hτ : τ = ∑ i, τ.restrict {z | Q z = i} := by
    have hd : Pairwise (fun i j => Disjoint {z | Q z = i} {z | Q z = j}) := by
      intro i j hij
      rw [Set.disjoint_left]
      intro z hz hz'
      exact hij (hz.symm.trans hz')
    have HU : (⋃ i, {z | Q z = i}) = (Set.univ : Set Z) := by ext; simp
    have H := τ.restrict_iUnion hd hQ
    rw [HU, Measure.restrict_univ] at H
    simpa only [Measure.sum_fintype] using H
  conv_lhs => rw [hτ]
  generalize (Finset.univ : Finset ι) = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Measure.comp_add, ih]

lemma kernelCell_real (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Kernel Z Y) [IsMarkovKernel κ] (Q : Z → ι) (i : ι)
    (h : τ {z | Q z = i} ≠ 0) {S : Set Y} (hS : MeasurableSet S) :
    (kernelCell τ κ Q i).real S =
      (τ.real {z | Q z = i})⁻¹ * ∫ z in {z | Q z = i}, (κ z).real S ∂τ := by
  rw [kernelCell, ite_eq_right h, kernel_comp_real _ _ hS, ProbabilityTheory.cond, integral_smul_measure]
  simp only [ENNReal.toReal_inv, smul_eq_mul, measureReal_def]

lemma measurable_kernel_real (κ : Kernel Z Y) {S : Set Y} (hS : MeasurableSet S) :
    Measurable (fun z => (κ z).real S) := (κ.measurable_coe hS).ennreal_toReal

lemma integrable_kernel_real (τ : Measure Z) [IsFiniteMeasure τ]
    (κ : Kernel Z Y) [IsMarkovKernel κ] {S : Set Y} (hS : MeasurableSet S) :
    Integrable (fun z => (κ z).real S) τ := by
  refine Integrable.mono' (integrable_const (1:ℝ)) (measurable_kernel_real κ hS).aestronglyMeasurable ?_
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one

end PrimeDegreePackets


namespace PrimeDegreePackets

 

lemma finite_measurable_small_fibers {Z V : Type*} [MeasurableSpace Z]
    [PseudoMetricSpace V] [MeasurableSpace V] [BorelSpace V]
    (p : Z → V) (hp : Measurable p) {K : Set V} (hK : IsCompact K)
    (hpK : ∀ z, p z ∈ K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, ∃ Q : Z → (Fin k → Bool),
      (∀ i, MeasurableSet {z | Q z = i}) ∧
      ∀ z z', Q z = Q z' → dist (p z) (p z') < δ := by
  let U : V → Set V := fun v => Metric.ball v (δ/2)
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U (fun _ => Metric.isOpen_ball) (by
    intro v _
    exact Set.mem_iUnion.mpr ⟨v, Metric.mem_ball_self (by positivity)⟩)
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let Q : Z → (Fin (Fintype.card s) → Bool) := fun z i => if p z ∈ U (e i) then true else false
  have hQ : Measurable Q := measurable_pi_iff.mpr fun i =>
    Measurable.ite (hp (Metric.isOpen_ball.measurableSet)) measurable_const measurable_const
  refine ⟨Fintype.card s,Q,fun i => hQ (measurableSet_singleton i),?_⟩
  intro z z' H
  obtain ⟨v,hv,hz⟩ := Set.mem_iUnion₂.mp (hs (hpK z))
  let i : Fin (Fintype.card s) := e.symm ⟨v,hv⟩
  have hzi : p z ∈ U (e i) := by simpa [i] using hz
  have hz'i : p z' ∈ U (e i) := by
    have H' := congrFun H i
    by_contra hn
    simp only [Q, ite_eq_left hzi, ite_eq_right hn] at H'
    contradiction
  have hz1 : dist (p z) (e i).val < δ/2 := hzi
  have hz2 : dist (p z') (e i).val < δ/2 := hz'i
  have Htri := dist_triangle (p z) (e i).val (p z')
  rw [dist_comm (e i).val (p z')] at Htri
  linarith

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma continuous_finiteShannon {α : Type*} [Fintype α] :
    Continuous (finiteShannon (α := α)) := by
  unfold finiteShannon
  exact continuous_finsetSum _ (fun a _ => Real.continuous_negMulLog.comp (continuous_apply a))

lemma measurable_kernel_entropy {Z Y α : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    [Fintype α] (κ : Kernel Z Y) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    Measurable (fun z => observationEntropy (κ z) P) := by
  exact continuous_finiteShannon.measurable.comp (measurable_pi_iff.mpr
    (fun a => measurable_kernel_real κ (hP a)))

lemma integrable_kernel_entropy {Z Y α : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    [Fintype α] (τ : Measure Z) [IsFiniteMeasure τ]
    (κ : Kernel Z Y) [IsMarkovKernel κ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    Integrable (fun z => observationEntropy (κ z) P) τ := by
  apply Integrable.mono' (integrable_const (Real.log (Fintype.card α)))
    (measurable_kernel_entropy κ P hP).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (observationEntropy_nonneg (κ z) P hP)]
    exact finiteShannon_le_log_card (fun a => measureReal_nonneg)
      (observation_distribution_sum (κ z) P hP)

lemma ae_nonnull_fiber {Z ι : Type*} [MeasurableSpace Z] [Fintype ι]
    (τ : Measure Z) (Q : Z → ι) :
    ∀ᵐ z ∂τ, τ {z' | Q z' = Q z} ≠ 0 := by
  have H (i : ι) : ∀ᵐ z ∂τ, Q z = i → τ {z' | Q z' = i} ≠ 0 := by
    by_cases hi : τ {z' | Q z' = i} = 0
    · apply ae_iff.mpr
      simp only [hi, ne_eq, not_true_eq_false, imp_false, not_not]
    · exact ae_of_all _ (fun _ _ => hi)
  filter_upwards [ae_all_iff.mpr H] with z hz
  exact hz (Q z) rfl

 

lemma kernelCell_real_close {Z Y ι : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    (τ : Measure Z) [IsProbabilityMeasure τ] (κ : Kernel Z Y) [IsMarkovKernel κ]
    (Q : Z → ι) (hQ : ∀ i, MeasurableSet {z | Q z = i})
    {S : Set Y} (hS : MeasurableSet S) {δ : ℝ}
    (hclose : ∀ z z', Q z = Q z' → |(κ z).real S - (κ z').real S| ≤ δ)
    (z : Z) (hz : τ {z' | Q z' = Q z} ≠ 0) :
    |(kernelCell τ κ Q (Q z)).real S - (κ z).real S| ≤ δ := by
  let A := {z' | Q z' = Q z}
  have hw : 0 < τ.real A := ENNReal.toReal_pos hz (measure_ne_top _ _)
  have hAreal : (τ.restrict A).real Set.univ = τ.real A := by simp [measureReal_def]
  rw [kernelCell_real τ κ Q (Q z) hz hS, abs_le]
  have hlo : (κ z).real S - δ ≤
      (τ.real A)⁻¹ * ∫ z' in A, (κ z').real S ∂τ := by
    have H : ∫ z' in A, (κ z).real S-δ ∂τ ≤ ∫ z' in A, (κ z').real S ∂τ :=
      setIntegral_mono_on (integrable_const _).integrableOn
        (integrable_kernel_real τ κ hS).integrableOn (hQ (Q z)) (by
          intro z' hz'
          have := (abs_le.mp (hclose z' z hz')).1
          linarith)
    rw [integral_const] at H
    simp only [hAreal, smul_eq_mul] at H
    have := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hw.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hw.ne', one_mul] using this
  have hup : (τ.real A)⁻¹ * ∫ z' in A, (κ z').real S ∂τ ≤ (κ z).real S+δ := by
    have H : ∫ z' in A, (κ z').real S ∂τ ≤ ∫ z' in A, (κ z).real S+δ ∂τ :=
      setIntegral_mono_on (integrable_kernel_real τ κ hS).integrableOn
        (integrable_const _).integrableOn (hQ (Q z)) (by
          intro z' hz'
          have := (abs_le.mp (hclose z' z hz')).2
          linarith)
    rw [integral_const] at H
    simp only [hAreal, smul_eq_mul] at H
    have := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hw.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hw.ne', one_mul] using this
  change -δ ≤ (τ.real A)⁻¹ * _ - _ ∧ _ ≤ δ
  constructor <;> linarith

 

theorem kernel_entropy_finite_approx {Z Y α : Type*} [MeasurableSpace Z]
    [MeasurableSpace Y] [Fintype α] (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Kernel Z Y) [IsMarkovKernel κ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∃ Q : Z → (Fin k → Bool),
      (∀ i, MeasurableSet {z | Q z = i}) ∧
      ∀ᵐ z ∂τ, observationEntropy (kernelCell τ κ Q (Q z)) P ≤
        observationEntropy (κ z) P + ε := by
  let K : Set (α → ℝ) := Set.Icc 0 1
  have hK : IsCompact K := isCompact_Icc
  have hU := hK.uniformContinuousOn_of_continuous continuous_finiteShannon.continuousOn
  obtain ⟨δ,hδ,Hδ⟩ := Metric.uniformContinuousOn_iff.mp hU ε hε
  let p : Z → α → ℝ := fun z a => (κ z).real {y | P y = a}
  have hpK z : p z ∈ K := ⟨fun a => measureReal_nonneg, fun a => measureReal_le_one⟩
  obtain ⟨k,Q,hQ,HQ⟩ := finite_measurable_small_fibers p
    (measurable_pi_iff.mpr (fun a => measurable_kernel_real κ (hP a))) hK hpK
    (show 0 < δ/2 by positivity)
  refine ⟨k,Q,hQ,?_⟩
  filter_upwards [ae_nonnull_fiber τ Q] with z hz
  let q : α → ℝ := fun a => (kernelCell τ κ Q (Q z)).real {y | P y = a}
  have hqK : q ∈ K := ⟨fun a => measureReal_nonneg, fun a => measureReal_le_one⟩
  have hdist : dist q (p z) < δ := by
    apply lt_of_le_of_lt ((dist_pi_le_iff (show 0 ≤ δ/2 by positivity)).mpr ?_) (show δ/2 < δ by linarith)
    intro a
    rw [Real.dist_eq]
    exact kernelCell_real_close τ κ Q hQ (hP a) (fun z z' H =>
      (Real.dist_eq _ _ ▸ (dist_le_pi_dist (p z) (p z') a)).trans (HQ z z' H).le) z hz
  have H := Hδ q hqK (p z) (hpK z) hdist
  rw [Real.dist_eq] at H
  change finiteShannon q ≤ finiteShannon (p z) + ε
  have := (abs_lt.mp H).2
  linarith

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma integrable_finite_values {Z ι : Type*} [MeasurableSpace Z] [Fintype ι]
    (τ : Measure Z) [IsFiniteMeasure τ] (Q : Z → ι)
    (hQ : ∀ i, MeasurableSet {z | Q z = i}) (c : ι → ℝ) :
    Integrable (fun z => c (Q z)) τ := by
  have H : (fun z => c (Q z)) = fun z =>
      ∑ i, {z | Q z = i}.indicator (fun _ => c i) z := by
    funext z
    simp [Set.indicator_apply]
  rw [H]
  exact integrable_finsetSum _ (fun i _ => (integrable_const (c i)).indicator (hQ i))

lemma integral_finite_values {Z ι : Type*} [MeasurableSpace Z] [Fintype ι]
    (τ : Measure Z) [IsFiniteMeasure τ] (Q : Z → ι)
    (hQ : ∀ i, MeasurableSet {z | Q z = i}) (c : ι → ℝ) :
    (∫ z, c (Q z) ∂τ) = ∑ i, τ.real {z | Q z = i} * c i := by
  have H : (fun z => c (Q z)) = fun z =>
      ∑ i, {z | Q z = i}.indicator (fun _ => c i) z := by
    funext z
    simp [Set.indicator_apply]
  rw [H,integral_finsetSum _ (fun i _ => (integrable_const (c i)).indicator (hQ i))]
  simp only [integral_indicator_const _ (hQ _), smul_eq_mul]

lemma observationEntropyRate_nonneg {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y} (hT : Measurable T)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) :
    0 ≤ observationEntropyRate μ T P := by
  unfold observationEntropyRate
  apply le_csInf
  · exact ⟨_,1,(show (1:ℕ) ≤ 1 from le_rfl),rfl⟩
  · rintro _ ⟨N,_,rfl⟩
    exact div_nonneg (observationEntropy_nonneg μ _ (orbitName_measurable_fiber hT hP N))
      (Nat.cast_nonneg _)

lemma observationEntropyRate_le_block {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y} (hT : Measurable T)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) {N : ℕ} (hN : 1 ≤ N) :
    observationEntropyRate μ T P ≤ observationEntropy μ (orbitName T P N)/(N:ℝ) := by
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro _ ⟨k,_,rfl⟩
    exact div_nonneg (observationEntropy_nonneg μ _ (orbitName_measurable_fiber hT hP k))
      (Nat.cast_nonneg _)
  · exact ⟨N,hN,rfl⟩

 

theorem kernel_entropyRate_le_block {Z Y α : Type*} [MeasurableSpace Z]
    [MeasurableSpace Y] [Fintype α] (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Kernel Z Y) [IsMarkovKernel κ] {T : Y → Y} (hT : Measurable T)
    (hκ : ∀ᵐ z ∂τ, MeasurePreserving T (κ z) (κ z))
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) {N : ℕ} (hN : 1 ≤ N) :
    observationEntropyRate (κ ∘ₘ τ) T P * (N:ℝ) ≤
      ∫ z, observationEntropy (κ z) (orbitName T P N) ∂τ := by
  have hNr : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  let R := orbitName T P N
  have hR := orbitName_measurable_fiber hT hP N
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨k,Q,hQ,HQ⟩ := kernel_entropy_finite_approx τ κ R hR hε
  let w := fun i => τ.real {z | Q z = i}
  let ν := kernelCell τ κ Q
  have hmix := kernel_finite_cells τ κ Q hQ
  have hrate := observationEntropyRate_finite_mixture (κ ∘ₘ τ) ν w
    (fun _ => measureReal_nonneg) (observation_distribution_sum τ Q hQ) hmix
    (kernel_mixture_preserving τ κ hT hκ) (fun i => kernelCell_preserving τ κ Q i hT hκ) P hP
  rw [hrate,Finset.sum_mul]
  have H : (∑ i, w i * observationEntropyRate (ν i) T P * (N:ℝ)) ≤
      ∑ i, w i * observationEntropy (ν i) R := by
    apply Finset.sum_le_sum
    intro i _
    have H := (le_div_iff₀ hNr).mp (observationEntropyRate_le_block (ν i) hT P hP hN)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left H
      (show 0 ≤ w i from measureReal_nonneg)
  apply H.trans
  rw [← integral_finite_values τ Q hQ (fun i => observationEntropy (ν i) R)]
  have H' := integral_mono_ae (integrable_finite_values τ Q hQ (fun i => observationEntropy (ν i) R))
    ((integrable_kernel_entropy τ κ R hR).add (integrable_const ε)) HQ
  change (∫ z, observationEntropy (ν (Q z)) R ∂τ) ≤
    ∫ z, observationEntropy (κ z) R + ε ∂τ at H'
  simpa only [integral_add (integrable_kernel_entropy τ κ R hR) (integrable_const ε),
    integral_const, probReal_univ, one_smul] using H'

lemma normalized_orbit_entropy_le {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y} (hT : Measurable T)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) (N : ℕ) :
    observationEntropy μ (orbitName T P N)/(N:ℝ) ≤ Real.log (Fintype.card α) := by
  by_cases hN : N = 0
  · subst N
    simpa only [Nat.cast_zero, _root_.div_zero] using Real.log_natCast_nonneg (Fintype.card α)
  · have H := finiteShannon_le_log_card (fun a =>
        show 0 ≤ μ.real {y | orbitName T P N y = a} from measureReal_nonneg)
        (observation_distribution_sum μ _ (orbitName_measurable_fiber hT hP N))
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow] at H
    exact (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hN)).mpr (by
      simpa only [observationEntropy, mul_comm] using H)

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_KernelEntropy
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
namespace PrimeDegreePackets

lemma kernel_cond_le {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    (τ : Measure Z) [IsProbabilityMeasure τ] (κ : Kernel Z Y)
    (S : Set Z) (hS : τ S ≠ 0) :
    κ ∘ₘ ProbabilityTheory.cond τ S ≤ ENNReal.ofReal ((τ.real S)⁻¹) • (κ ∘ₘ τ) := by
  have H : ENNReal.ofReal ((τ.real S)⁻¹) = (τ S)⁻¹ := by
    rw [measureReal_def, ← ENNReal.toReal_inv, ENNReal.ofReal_toReal]
    exact ENNReal.inv_ne_top.mpr hS
  rw [H, ProbabilityTheory.cond, Measure.comp_smul]
  apply Measure.le_iff.mpr
  intro A hA
  simp only [Measure.smul_apply, smul_eq_mul]
  apply _root_.mul_le_mul_right
  rw [Measure.bind_apply hA κ.aemeasurable, Measure.bind_apply hA κ.aemeasurable]
  exact lintegral_mono' Measure.restrict_le_self le_rfl



end PrimeDegreePackets


namespace PrimeDegreePackets

lemma measurable_kernel_entropyRate {Z Y α : Type*} [MeasurableSpace Z]
    [MeasurableSpace Y] [Fintype α] (κ : Kernel Z Y) {T : Y → Y} (hT : Measurable T)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) :
    Measurable (fun z => observationEntropyRate (κ z) T P) := by
  unfold observationEntropyRate
  exact Measurable.sInf (Set.to_countable _) (fun N _ =>
    (measurable_kernel_entropy κ _ (orbitName_measurable_fiber hT hP N)).div_const _)

 

lemma observationEntropyRate_kernel_zero {Z Y α : Type*} [MeasurableSpace Z]
    [MeasurableSpace Y] [Fintype α]
    (τ : Measure Z) [IsProbabilityMeasure τ] (κ : Kernel Z Y) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T)
    (hκ : ∀ᵐ z ∂τ, MeasurePreserving T (κ z) (κ z))
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a})
    (hzero : ∀ᵐ z ∂τ, observationEntropyRate (κ z) T P = 0) :
    observationEntropyRate (κ ∘ₘ τ) T P = 0 := by
  apply le_antisymm _ (observationEntropyRate_nonneg _ hT P hP)
  let F : ℕ → Z → ℝ := fun N z => observationEntropy (κ z) (orbitName T P N)/(N:ℝ)
  have hlim : Tendsto (fun N => ∫ z, F N z ∂τ) atTop (𝓝 0) := by
    have H := tendsto_integral_of_dominated_convergence
      (fun _ : Z => Real.log (Fintype.card α))
      (fun N => ((measurable_kernel_entropy κ _ (orbitName_measurable_fiber hT hP N)).div_const _).aestronglyMeasurable)
      (integrable_const _) (fun N => ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
          (observationEntropy_nonneg (κ z) _ (orbitName_measurable_fiber hT hP N)) (Nat.cast_nonneg N))]
        exact normalized_orbit_entropy_le (κ z) hT P hP N)
      (f := fun _ : Z => (0:ℝ)) (by
        filter_upwards [hκ,hzero] with z hz hz0
        simpa only [hz0] using tendsto_observationEntropyRate (κ z) hz P hP)
    simpa only [integral_zero] using H
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have H := kernel_entropyRate_le_block τ κ hT hκ P hP hN
  have hNr : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  change observationEntropyRate (κ ∘ₘ τ) T P ≤ ∫ z, observationEntropy (κ z) (orbitName T P N)/(N:ℝ) ∂τ
  rw [integral_div]
  exact (le_div_iff₀ hNr).mpr H

 

theorem positive_entropy_components_ae_oai {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Kernel Z (X (d+1))) [IsMarkovKernel κ]
    (hball : OrdinaryBallBound (d+1) (κ ∘ₘ τ))
    (hA : ∀ᵐ z ∂τ, ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) (κ z) = κ z) :
    ∀ᵐ z ∂τ, 0 < measureEntropy (κ z)
      (fun x => rightAction x (diagonalOneParameter (regularDiagonalWeights d)
        (regularDiagonalWeights_sum d) 1)) := by
  let T : X (d+1) → X (d+1) := fun x => rightAction x
    (diagonalOneParameter (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 1)
  have hT : Measurable T := (continuous_rightAction _).measurable
  let C : Set (Set Z) := {B | ∃ k : ℕ, ∃ P : X (d+1) → Fin k,
    (∀ a, MeasurableSet {y | P y = a}) ∧ B = {z | 0 < observationEntropyRate (κ z) T P}}
  have hCm (B : Set Z) (hB : B ∈ C) : MeasurableSet B := by
    obtain ⟨k,P,hP,rfl⟩ := hB
    exact measurableSet_lt measurable_const (measurable_kernel_entropyRate κ hT P hP)
  obtain ⟨D,hDC,hDcount,hDcover⟩ := Measure.exists_ae_subset_biUnion_countable τ hCm
  let U : Set Z := ⋃₀ D
  have hUm : MeasurableSet U := MeasurableSet.sUnion hDcount (fun B hB => hCm B (hDC hB))
  have hUpos (z : Z) (hz : z ∈ U) : 0 < measureEntropy (κ z) T := by
    obtain ⟨B,hBD,hzB⟩ := Set.mem_sUnion.mp hz
    obtain ⟨k,P,hP,rfl⟩ := hDC hBD
    exact (ENNReal.ofReal_pos.mpr hzB).trans_le
      (le_iSup_of_le k (le_iSup_of_le P (le_iSup_of_le hP le_rfl)))
  have hnull : τ Uᶜ = 0 := by
    by_contra hS
    let σ := ProbabilityTheory.cond τ Uᶜ
    have : IsProbabilityMeasure σ := cond_isProbabilityMeasure hS
    let ν := κ ∘ₘ σ
    have hA' : ∀ᵐ z ∂σ, ∀ u : LogCoordinates d,
        Measure.map (fun x => rightAction x (diagonalFlow u)) (κ z) = κ z :=
      cond_absolutelyContinuous.ae_le hA
    have hν : ∀ u : LogCoordinates d,
        Measure.map (fun x => rightAction x (diagonalFlow u)) ν = ν := by
      intro u
      exact (kernel_mixture_preserving σ κ (continuous_rightAction _).measurable
        (hA'.mono (fun z hz => ⟨(continuous_rightAction _).measurable,hz u⟩))).map_eq
    have hpos := positive_entropy_every_dominated_invariant (κ ∘ₘ τ) ν hball hν
      (kernel_cond_le τ κ Uᶜ hS)
    have hpres : ∀ᵐ z ∂σ, MeasurePreserving T (κ z) (κ z) := by
      filter_upwards [hA'] with z hz
      refine ⟨hT,?_⟩
      dsimp [T]
      rw [diagonalOneParameter_eq_diagonalFlow]
      exact hz _
    have hnotU : ∀ᵐ z ∂σ, z ∉ U := by
      exact Measure.smul_absolutelyContinuous.ae_le (ae_restrict_mem hUm.compl)
    have hzero : measureEntropy ν T = 0 := by
      apply le_antisymm _ bot_le
      apply iSup_le
      intro k
      apply iSup_le
      intro P
      apply iSup_le
      intro hP
      have hcover := hDcover {z | 0 < observationEntropyRate (κ z) T P} ⟨k,P,hP,rfl⟩
      have hz : ∀ᵐ z ∂σ, observationEntropyRate (κ z) T P = 0 := by
        filter_upwards [cond_absolutelyContinuous.ae_le hcover,hnotU] with z hz hn
        apply le_antisymm _ (observationEntropyRate_nonneg (κ z) hT P hP)
        exact le_of_not_gt (fun hp => hn (hz hp))
      rw [observationEntropyRate_kernel_zero σ κ hT hpres P hP hz,ENNReal.ofReal_zero]
      exact le_rfl
    exact (ne_of_gt hpos) hzero
  have hUae : ∀ᵐ z ∂τ, z ∈ U := by
    simpa only [Set.mem_compl_iff,not_not] using measure_eq_zero_iff_ae_notMem.mp hnull
  exact hUae.mono hUpos

end PrimeDegreePackets

open Set Filter
open scoped Topology

open scoped Classical

open scoped Topology ENNReal Classical
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PrimeDegreePackets.positive_entropy_components_ae_oai.{u_1} := @OAI.PrimeDegreePackets.positive_entropy_components_ae_oai.{u_1}
