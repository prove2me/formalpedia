-- Prove2me | solution 1 for NoLocalBroadcast.Broadcast.cc_locally_broadcastable
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T07:02:01.189923+00:00
-- url     : https://prove2.me/submissions/2f1894fe-cff8-4e71-ae75-06a670bf6bbe

import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_QAlgorithms_Defs_Search
import Definitions.Def_QAlgorithms_Defs_Adversary
import Definitions.Def_QAlgorithms_Defs_Polynomial
import Definitions.Def_QAlgorithms_Defs_CompressedOracle
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Defs_Walk
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_LinearSystems
import Definitions.Def_QAlgorithms_Defs_Stabilizer
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QAlgorithms_Defs_SDP
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_QAlgorithms_Defs_Learning
import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_NoLocalBroadcast_Broadcast_Model
import Init
import Mathlib



section
noncomputable section
namespace Queelius.LocalBroadcasting
open Finset

 theorem weighted_log_bound (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hs : 0 < x → 0 < y) : x * Real.log y - x * Real.log x ≤ y-x := by
  by_cases h0 : x=0
  · simp [h0,hy]
  · have hp : 0 < x := lt_of_le_of_ne hx (Ne.symm h0)
    have hq := hs hp
    calc
      _ = x * Real.log (y/x) := by rw [Real.log_div (ne_of_gt hq) h0]; ring
      _ ≤ x * (y/x-1) := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hq hp)) hx
      _ = y-x := by field_simp

 theorem finite_gibbs {ι : Type} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1)
    (hs : ∀ i, 0 < p i → 0 < q i) :
    ∑ i, p i * Real.log (q i) ≤ ∑ i, p i * Real.log (p i) := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => weighted_log_bound (p i) (q i) (hp i) (hq i) (hs i))
  simpa only [Finset.sum_sub_distrib,hp1,hq1,sub_self,sub_nonpos] using h

variable {a b : Type} [Fintype a] [Fintype b]

def rowProb (p : a × b → ℝ) (i : a) : ℝ := ∑ j, p (i,j)
def colProb (p : a × b → ℝ) (j : b) : ℝ := ∑ i, p (i,j)

 theorem row_nonnegative (p : a × b → ℝ) (hp : ∀ ij, 0 ≤ p ij) (i : a) : 0 ≤ rowProb p i :=
  Finset.sum_nonneg (fun j _ => hp (i,j))
 theorem col_nonnegative (p : a × b → ℝ) (hp : ∀ ij, 0 ≤ p ij) (j : b) : 0 ≤ colProb p j :=
  Finset.sum_nonneg (fun i _ => hp (i,j))
 theorem joint_le_row (p : a × b → ℝ) (hp : ∀ ij, 0 ≤ p ij) (i : a) (j : b) : p (i,j) ≤ rowProb p i :=
  Finset.single_le_sum (fun j _ => hp (i,j)) (Finset.mem_univ j)
 theorem joint_le_col (p : a × b → ℝ) (hp : ∀ ij, 0 ≤ p ij) (i : a) (j : b) : p (i,j) ≤ colProb p j :=
  Finset.single_le_sum (fun i _ => hp (i,j)) (Finset.mem_univ i)

 theorem marginal_product_sum (p : a × b → ℝ) (hp1 : ∑ ij, p ij = 1) :
    ∑ ij : a × b, rowProb p ij.1 * colProb p ij.2 = 1 := by
  have hr : ∑ i, rowProb p i = 1 := by simpa only [rowProb,Fintype.sum_prod_type] using hp1
  have hc : ∑ j, colProb p j = 1 := by
    simp only [colProb]
    rw [Finset.sum_comm]
    exact hr
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum,hc,mul_one]
  exact hr

 theorem log_marginal_decomposition (p : a × b → ℝ) (hp : ∀ ij, 0 ≤ p ij) :
    ∑ ij, p ij * Real.log (rowProb p ij.1 * colProb p ij.2) =
      (∑ i, rowProb p i * Real.log (rowProb p i)) +
      (∑ j, colProb p j * Real.log (colProb p j)) := by
  have hterm (ij : a × b) : p ij * Real.log (rowProb p ij.1 * colProb p ij.2) =
      p ij * Real.log (rowProb p ij.1) + p ij * Real.log (colProb p ij.2) := by
    by_cases h0 : p ij=0
    · simp [h0]
    · have hp' : 0 < p ij := lt_of_le_of_ne (hp ij) (Ne.symm h0)
      rw [Real.log_mul (ne_of_gt (hp'.trans_le (joint_le_row p hp ij.1 ij.2)))
        (ne_of_gt (hp'.trans_le (joint_le_col p hp ij.1 ij.2))),mul_add]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib,Fintype.sum_prod_type,Fintype.sum_prod_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [Prod.fst,Prod.snd]
    rw [← Finset.sum_mul]
    rfl
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Prod.fst,Prod.snd]
    rw [← Finset.sum_mul]
    rfl

 theorem classical_log_subadditivity (p : a × b → ℝ) (hp : ∀ ij, 0 ≤ p ij)
    (hp1 : ∑ ij, p ij = 1) :
    (∑ i, rowProb p i * Real.log (rowProb p i)) +
      (∑ j, colProb p j * Real.log (colProb p j)) ≤ ∑ ij, p ij * Real.log (p ij) := by
  rw [← log_marginal_decomposition p hp]
  apply finite_gibbs p (fun ij => rowProb p ij.1 * colProb p ij.2) hp
    (fun ij => mul_nonneg (row_nonnegative p hp _) (col_nonnegative p hp _)) hp1
    (marginal_product_sum p hp1)
  intro ij h
  exact mul_pos (h.trans_le (joint_le_row p hp ij.1 ij.2)) (h.trans_le (joint_le_col p hp ij.1 ij.2))

end Queelius.LocalBroadcasting

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem unitary_row_normSq (U : Matrix.unitaryGroup ι ℂ) (i : ι) :
    ∑ j, Complex.normSq ((U : Matrix ι ι ℂ) i j) = 1 := by
  have h := congrArg Complex.re (congrFun (congrFun U.property.2 i) i)
  simpa [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,
    Complex.mul_re,Complex.normSq_apply] using h

theorem unitary_col_normSq (U : Matrix.unitaryGroup ι ℂ) (j : ι) :
    ∑ i, Complex.normSq ((U : Matrix ι ι ℂ) i j) = 1 := by
  have h := congrArg Complex.re (congrFun (congrFun U.property.1 j) j)
  simpa [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,
    Complex.mul_re,Complex.normSq_apply,mul_comm] using h

theorem unitary_diagonal_mix (U : Matrix.unitaryGroup ι ℂ) (p : ι → ℝ) (i : ι) :
    (((U : Matrix ι ι ℂ) * Matrix.diagonal (fun j => (p j : ℂ)) * (U : Matrix ι ι ℂ)ᴴ) i i).re =
      ∑ j, Complex.normSq ((U : Matrix ι ι ℂ) i j) * p j := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Complex.star_def,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    map_zero,mul_zero,sub_zero,zero_mul,add_zero,Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
  ring

theorem doubly_stochastic_entropy {κ : Type} [Fintype κ]
    (W : ι → κ → ℝ) (p : κ → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hw : ∀ i j, 0 ≤ W i j) (hr : ∀ i, ∑ j, W i j = 1) (hc : ∀ j, ∑ i, W i j = 1) :
    ∑ j, Real.negMulLog (p j) ≤ ∑ i, Real.negMulLog (∑ j, W i j * p j) := by
  have hh (i : ι) : ∑ j, W i j * Real.negMulLog (p j) ≤
      Real.negMulLog (∑ j, W i j * p j) := by
    simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.le_map_sum
      (fun j _ => hw i j) (hr i) (fun j _ => hp j)
  calc
    _ = ∑ i, ∑ j, W i j * Real.negMulLog (p j) := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul,hc,one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => hh i)

end Queelius.LocalBroadcasting

end


section
noncomputable section
namespace Queelius.LocalBroadcasting
open Finset

 theorem weighted_log_strict (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hs : 0 < x → 0 < y) (hne : x ≠ y) : x * Real.log y - x * Real.log x < y-x := by
  by_cases h0 : x=0
  · subst x
    simpa only [zero_mul,sub_zero] using lt_of_le_of_ne hy hne
  · have hp : 0 < x := lt_of_le_of_ne hx (Ne.symm h0)
    have hq := hs hp
    have hn : y/x ≠ 1 := by intro h; apply hne; exact ((div_eq_one_iff_eq h0).mp h).symm
    calc
      _ = x * Real.log (y/x) := by rw [Real.log_div (ne_of_gt hq) h0]; ring
      _ < x * (y/x-1) := mul_lt_mul_of_pos_left (Real.log_lt_sub_one_of_pos (div_pos hq hp) hn) hp
      _ = y-x := by field_simp

 theorem finite_gibbs_equality {ι : Type} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1)
    (hs : ∀ i, 0 < p i → 0 < q i) :
    (∑ i, p i * Real.log (q i)) = (∑ i, p i * Real.log (p i)) ↔ p=q := by
  constructor
  · intro heq
    funext i
    by_contra hne
    have hsum := Finset.sum_lt_sum
      (s:=Finset.univ) (fun j _ => weighted_log_bound (p j) (q j) (hp j) (hq j) (hs j))
      ⟨i,Finset.mem_univ i,weighted_log_strict (p i) (q i) (hp i) (hq i) (hs i) hne⟩
    simpa only [Finset.sum_sub_distrib,hp1,hq1,heq,sub_self,lt_self_iff_false] using hsum
  · rintro rfl
    rfl

end Queelius.LocalBroadcasting

end


























section
noncomputable section
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker

namespace Queelius.LocalBroadcast
open NoLocalBroadcast.Broadcast QAlgorithms

def tensorVec {a b : Type} (u : EuclideanSpace ℂ a) (v : EuclideanSpace ℂ b) :
    EuclideanSpace ℂ (a × b) := WithLp.toLp 2 fun p => u p.1 * v p.2

theorem pure_tensor {a b : Type} (u : EuclideanSpace ℂ a) (v : EuclideanSpace ℂ b) :
    pureDensity (tensorVec u v) = pureDensity u ⊗ₖ pureDensity v := by
  ext p q
  simp [pureDensity, tensorVec, Matrix.kronecker_apply, map_mul]
  ring

theorem pure_psd {a : Type} [Fintype a] (u : EuclideanSpace ℂ a) : (pureDensity u).PosSemidef := by
  exact Matrix.posSemidef_vecMulVec_self_star (fun i => u i)

theorem pure_trace {a : Type} [Fintype a] (u : EuclideanSpace ℂ a) :
    (pureDensity u).trace = inner ℂ u u := by
  simp only [Matrix.trace, Matrix.diag, pureDensity, Matrix.of_apply, PiLp.inner_apply, RCLike.inner_apply]

theorem tensor_inner {a b : Type} [Fintype a] [Fintype b]
    (u u' : EuclideanSpace ℂ a) (v v' : EuclideanSpace ℂ b) :
    inner ℂ (tensorVec u v) (tensorVec u' v') = inner ℂ u u' * inner ℂ v v' := by
  simp only [PiLp.inner_apply, tensorVec, RCLike.inner_apply,
    map_mul, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  ring

def copiedPure {a b : Type} (u : EuclideanSpace ℂ a) (v : EuclideanSpace ℂ b) :
    Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ :=
  pureDensity (tensorVec (tensorVec u u) (tensorVec v v))

theorem traceCopies_copiedPure {a b : Type} [Fintype a] [Fintype b]
    (u : EuclideanSpace ℂ a) (v : EuclideanSpace ℂ b)
    (hu : inner ℂ u u = 1) (hv : inner ℂ v v = 1) :
    traceCopies (copiedPure u v) = pureDensity u ⊗ₖ pureDensity v := by
  ext p q
  have hu' : ∑ x, u x * conj (u x) = 1 := by
    simpa only [PiLp.inner_apply, RCLike.inner_apply] using hu
  have hv' : ∑ y, v y * conj (v y) = 1 := by
    simpa only [PiLp.inner_apply, RCLike.inner_apply] using hv
  change (∑ x, ∑ y, (u p.1 * u x * (v p.2 * v y)) *
    conj (u q.1 * u x * (v q.2 * v y))) = _
  simp only [map_mul]
  calc
    _ = (u p.1 * conj (u q.1) * (v p.2 * conj (v q.2))) *
        (∑ x, u x * conj (u x)) * (∑ y, v y * conj (v y)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = _ := by simp [hu', hv', Matrix.kronecker_apply, pureDensity]

theorem copiedPure_swap {a b : Type} (u : EuclideanSpace ℂ a) (v : EuclideanSpace ℂ b)
    (p q : (a × a) × (b × b)) :
    copiedPure u v ((p.1.2,p.1.1),(p.2.2,p.2.1)) ((q.1.2,q.1.1),(q.2.2,q.2.1)) =
      copiedPure u v p q := by
  simp [copiedPure, pureDensity, tensorVec, map_mul]
  ring

theorem traceOriginals_copiedPure {a b : Type} [Fintype a] [Fintype b]
    (u : EuclideanSpace ℂ a) (v : EuclideanSpace ℂ b)
    (hu : inner ℂ u u = 1) (hv : inner ℂ v v = 1) :
    traceOriginals (copiedPure u v) = pureDensity u ⊗ₖ pureDensity v := by
  rw [← traceCopies_copiedPure u v hu hv]
  ext p q
  change (∑ x, ∑ y, _) = ∑ x, ∑ y, _
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  exact copiedPure_swap u v ((p.1,x),(p.2,y)) ((q.1,x),(q.2,y))

theorem copiedPure_density {a b : Type} [Fintype a] [Fintype b]
    (u : EuclideanSpace ℂ a) (v : EuclideanSpace ℂ b)
    (hu : inner ℂ u u = 1) (hv : inner ℂ v v = 1) :
    IsDensityMatrix (copiedPure u v) := by
  refine ⟨pure_psd _, ?_⟩
  simp only [copiedPure, pure_trace, tensor_inner, hu, hv, mul_one]

theorem classical_broadcast_state {a b : Type} [Fintype a] [Fintype b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hcc : IsClassicalClassical ρ) :
    ∃ σ, IsBroadcastState ρ σ := by
  rcases hcc with ⟨k,l,e,f,p,he,hf,hp,hs,rfl⟩
  have he' (i) : inner ℂ (e i) (e i) = 1 := (orthonormal_iff_ite.mp he) i i |>.trans (if_pos rfl)
  have hf' (i) : inner ℂ (f i) (f i) = 1 := (orthonormal_iff_ite.mp hf) i i |>.trans (if_pos rfl)
  refine ⟨∑ ij, (p ij : ℂ) • copiedPure (e ij.1) (f ij.2), ⟨?_, ?_⟩, ?_, ?_⟩
  · apply Matrix.posSemidef_sum
    intro ij hij
    exact (copiedPure_density _ _ (he' _) (hf' _)).1.smul (by exact_mod_cast hp ij)
  · simp only [Matrix.trace_sum, Matrix.trace_smul,
      (copiedPure_density _ _ (he' _) (hf' _)).2, smul_eq_mul, mul_one]
    exact_mod_cast hs
  · ext a b
    simp only [traceCopies, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ij hij
    simp only [← Finset.mul_sum]
    exact congrArg (fun M : Matrix _ _ ℂ => (p ij : ℂ) * M a b)
      (traceCopies_copiedPure _ _ (he' _) (hf' _))
  · ext a b
    simp only [traceOriginals, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ij hij
    simp only [← Finset.mul_sum]
    exact congrArg (fun M : Matrix _ _ ℂ => (p ij : ℂ) * M a b)
      (traceOriginals_copiedPure _ _ (he' _) (hf' _))

end Queelius.LocalBroadcast

end

section
noncomputable section
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker
namespace Queelius.LocalBroadcast
open QAlgorithms NoLocalBroadcast.Broadcast

def discardRight {a b : Type} [DecidableEq a] [DecidableEq b] (k : b) :
    Matrix a (a × b) ℂ := fun i j => if i = j.1 ∧ k = j.2 then 1 else 0

def discardLeft {a b : Type} [DecidableEq a] [DecidableEq b] (k : a) :
    Matrix b (a × b) ℂ := fun i j => if k = j.1 ∧ i = j.2 then 1 else 0

theorem discardRight_normalized {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] : IsKrausFamily (@discardRight a b _ _) := by
  ext p q
  simp [IsKrausFamily, discardRight, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Prod.ext_iff, ite_and, apply_ite, eq_comm, Finset.sum_apply, Matrix.sum_apply]
  split_ifs <;> simp_all

theorem discardLeft_normalized {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] : IsKrausFamily (@discardLeft a b _ _) := by
  ext p q
  simp [IsKrausFamily, discardLeft, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Prod.ext_iff, ite_and, apply_ite, eq_comm, Finset.sum_apply, Matrix.sum_apply]
  split_ifs <;> simp_all

theorem discardRight_action {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (ρ : Matrix (a × b) (a × b) ℂ) :
    krausApply (@discardRight a b _ _) ρ = traceRight ρ := by
  ext i j
  simp [krausApply, discardRight, traceRight, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.sum_apply, Finset.sum_mul, ite_and, apply_ite, eq_comm]

theorem discardLeft_action {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (ρ : Matrix (a × b) (a × b) ℂ) :
    krausApply (@discardLeft a b _ _) ρ = traceLeft ρ := by
  ext i j
  simp [krausApply, discardLeft, traceLeft, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.sum_apply, Finset.sum_mul, ite_and, apply_ite, eq_comm]

end Queelius.LocalBroadcast

end

section
noncomputable section
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker
namespace Queelius.LocalBroadcast
open QAlgorithms NoLocalBroadcast.Broadcast

theorem kraus_density {a b ι : Type} [Fintype a] [DecidableEq a] [Fintype b]
    [Fintype ι] (K : ι → Matrix b a ℂ) (hK : IsKrausFamily K)
    (ρ : Matrix a a ℂ) (hρ : IsDensityMatrix ρ) : IsDensityMatrix (krausApply K ρ) := by
  constructor
  · exact Matrix.posSemidef_sum _ (fun i _ => hρ.1.mul_mul_conjTranspose_same (K i))
  · change (∑ i, K i * ρ * (K i)ᴴ).trace = 1
    calc
      _ = ∑ i, ((K i)ᴴ * K i * ρ).trace := by
        rw [Matrix.trace_sum]
        exact Finset.sum_congr rfl (fun i _ => Matrix.trace_mul_cycle _ _ _)
      _ = ((∑ i, (K i)ᴴ * K i) * ρ).trace := by
        rw [Matrix.sum_mul, Matrix.trace_sum]
      _ = 1 := by rw [hK, Matrix.one_mul, hρ.2]

theorem tensor_kraus_normalized {a b a' b' ι κ : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype a'] [Fintype b'] [Fintype ι] [Fintype κ]
    (K : ι → Matrix a' a ℂ) (L : κ → Matrix b' b ℂ)
    (hK : IsKrausFamily K) (hL : IsKrausFamily L) :
    IsKrausFamily (fun ij : ι × κ => K ij.1 ⊗ₖ L ij.2) := by
  unfold IsKrausFamily at *
  simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Fintype.sum_prod_type]
  have hs : (∑ i, ∑ j, ((K i)ᴴ * K i) ⊗ₖ ((L j)ᴴ * L j)) =
      (∑ i, (K i)ᴴ * K i) ⊗ₖ (∑ j, (L j)ᴴ * L j) := by
    ext p q
    simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hs, hK, hL, Matrix.one_kronecker_one]

theorem local_density {a b a' b' : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype a'] [Fintype b'] {m n : ℕ}
    (K : Fin m → Matrix a' a ℂ) (L : Fin n → Matrix b' b ℂ)
    (hK : IsKrausFamily K) (hL : IsKrausFamily L)
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (localApply K L ρ) :=
  kraus_density _ (tensor_kraus_normalized K L hK hL) ρ hρ

end Queelius.LocalBroadcast

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset
open scoped Kronecker

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def diagonalStarAlg : (ι → ℂ) →⋆ₐ[ℝ] Matrix ι ι ℂ :=
  { Matrix.diagonalAlgHom (n:=ι) (α:=ℂ) ℝ with
    map_star' := by intro x; exact (Matrix.diagonal_conjTranspose x).symm }

theorem cfc_real_diagonal (f : ℝ → ℝ) (hf : Continuous f) (p : ι → ℝ) :
    cfc f (Matrix.diagonal (fun i => (p i : ℂ))) =
      Matrix.diagonal (fun i => (f (p i) : ℂ)) := by
  cases isEmpty_or_nonempty ι with
  | inl hi =>
    ext i
    exact isEmptyElim i
  | inr hi =>
    letI : ContinuousFunctionalCalculus ℂ (ι → ℂ) IsStarNormal :=
      IsStarNormal.instContinuousFunctionalCalculus
    letI : ContinuousFunctionalCalculus ℝ (ι → ℂ) IsSelfAdjoint :=
      IsSelfAdjoint.instContinuousFunctionalCalculus
    have hsa : IsSelfAdjoint (fun i => (p i : ℂ)) := by
      ext i
      simp
    have hd : IsSelfAdjoint (diagonalStarAlg (fun i => (p i : ℂ))) := by
      exact Matrix.isHermitian_diagonal_of_self_adjoint _ hsa
    have hc : Continuous (diagonalStarAlg (ι:=ι)) := by
      change Continuous (Matrix.diagonal : (ι → ℂ) → Matrix ι ι ℂ)
      fun_prop
    have h := (diagonalStarAlg (ι:=ι)).map_cfc f (fun i => (p i : ℂ)) hf.continuousOn hc hsa hd
    rw [cfc_map_pi (S:=ℝ) f _ hf.continuousOn hsa (fun i => by change star (p i : ℂ) = _; simp)] at h
    have hs (i : ι) : cfc f (p i : ℂ) = (f (p i) : ℂ) :=
      cfc_algebraMap (R:=ℝ) (A:=ℂ) (p i) f
    simp only [hs] at h
    change Matrix.diagonal (fun i => (f (p i) : ℂ)) = cfc f (Matrix.diagonal (fun i => (p i : ℂ))) at h
    exact h.symm

theorem continuous_entropy_kernel : Continuous (fun x : ℝ => x * Real.logb 2 x) := by
  simpa only [Real.logb,mul_div_assoc] using Real.continuous_mul_log.div_const (Real.log 2)

theorem entropy_diagonal (p : ι → ℝ) :
    QAlgorithms.vnEntropy (Matrix.diagonal (fun i => (p i : ℂ))) =
      -(∑ i, p i * Real.logb 2 (p i)) := by
  rw [QAlgorithms.vnEntropy,cfc_real_diagonal _ continuous_entropy_kernel]
  simp

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem traceRight_diagonal (p : a × b → ℝ) :
    QAlgorithms.traceRight (Matrix.diagonal (fun ij => (p ij : ℂ))) =
      Matrix.diagonal (fun i => ((∑ j, p (i,j) : ℝ) : ℂ)) := by
  ext i j
  by_cases hij : i=j
  · subst j; simp [QAlgorithms.traceRight,Matrix.diagonal_apply]
  · simp [QAlgorithms.traceRight,Matrix.diagonal_apply,hij]

theorem traceLeft_diagonal (p : a × b → ℝ) :
    QAlgorithms.traceLeft (Matrix.diagonal (fun ij => (p ij : ℂ))) =
      Matrix.diagonal (fun j => ((∑ i, p (i,j) : ℝ) : ℂ)) := by
  ext i j
  by_cases hij : i=j
  · subst j; simp [QAlgorithms.traceLeft,Matrix.diagonal_apply]
  · simp [QAlgorithms.traceLeft,Matrix.diagonal_apply,hij]

theorem mutualInfo_diagonal (p : a × b → ℝ) :
    NoLocalBroadcast.Broadcast.mutualInfo (Matrix.diagonal (fun ij => (p ij : ℂ))) =
      -(∑ i, (∑ j, p (i,j)) * Real.logb 2 (∑ j, p (i,j)))
      -(∑ j, (∑ i, p (i,j)) * Real.logb 2 (∑ i, p (i,j)))
      +(∑ ij, p ij * Real.logb 2 (p ij)) := by
  rw [NoLocalBroadcast.Broadcast.mutualInfo,traceRight_diagonal,traceLeft_diagonal]
  simp only [entropy_diagonal]
  ring

end Queelius.LocalBroadcasting

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset
open scoped ComplexOrder Kronecker MatrixOrder
open QAlgorithms NoLocalBroadcast.Broadcast

 theorem trace_mul_psd {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A*B).trace := by
  obtain ⟨C,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have h := (hB.mul_mul_conjTranspose_same C).trace_nonneg
  rw [Matrix.trace_mul_cycle] at h
  simpa only [Matrix.star_eq_conjTranspose] using h

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable {m n : ℕ}

def jointMeasurement (ρ : Matrix (a × b) (a × b) ℂ)
    (M : Fin m → Matrix a a ℂ) (N : Fin n → Matrix b b ℂ) (ij : Fin m × Fin n) : ℝ :=
  ((M ij.1 ⊗ₖ N ij.2) * ρ).trace.re

 theorem jointMeasurement_nonnegative (ρ : Matrix (a × b) (a × b) ℂ)
    (M : Fin m → Matrix a a ℂ) (N : Fin n → Matrix b b ℂ)
    (hM : IsPOVM M) (hN : IsPOVM N) (hρ : IsDensityMatrix ρ) (ij : Fin m × Fin n) :
    0 ≤ jointMeasurement ρ M N ij :=
  (Complex.nonneg_iff.mp (trace_mul_psd _ _ ((hM.1 ij.1).kronecker (hN.1 ij.2)) hρ.1)).1

 theorem jointMeasurement_real (ρ : Matrix (a × b) (a × b) ℂ)
    (M : Fin m → Matrix a a ℂ) (N : Fin n → Matrix b b ℂ)
    (hM : IsPOVM M) (hN : IsPOVM N) (hρ : IsDensityMatrix ρ) (ij : Fin m × Fin n) :
    (jointMeasurement ρ M N ij : ℂ) = ((M ij.1 ⊗ₖ N ij.2) * ρ).trace := by
  have hi := (Complex.nonneg_iff.mp (trace_mul_psd _ _ ((hM.1 ij.1).kronecker (hN.1 ij.2)) hρ.1)).2
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using hi

 theorem tensor_povm_sum (M : Fin m → Matrix a a ℂ) (N : Fin n → Matrix b b ℂ)
    (hM : IsPOVM M) (hN : IsPOVM N) :
    (∑ ij : Fin m × Fin n, M ij.1 ⊗ₖ N ij.2) = 1 := by
  have hs : (∑ ij : Fin m × Fin n, M ij.1 ⊗ₖ N ij.2) = (∑ i, M i) ⊗ₖ (∑ j, N j) := by
    ext p q
    simp only [Fintype.sum_prod_type,Matrix.sum_apply,Matrix.kroneckerMap_apply,Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_comm
  rw [hs,hM.2,hN.2,Matrix.one_kronecker_one]

 theorem jointMeasurement_sum (ρ : Matrix (a × b) (a × b) ℂ)
    (M : Fin m → Matrix a a ℂ) (N : Fin n → Matrix b b ℂ)
    (hM : IsPOVM M) (hN : IsPOVM N) (hρ : IsDensityMatrix ρ) :
    ∑ ij, jointMeasurement ρ M N ij = 1 := by
  simp only [jointMeasurement,← Complex.re_sum,← Matrix.trace_sum,← Matrix.sum_mul,
    tensor_povm_sum M N hM hN,one_mul,hρ.2,Complex.one_re]

 theorem ccState_diagonal_law (ρ : Matrix (a × b) (a × b) ℂ)
    (M : Fin m → Matrix a a ℂ) (N : Fin n → Matrix b b ℂ)
    (hM : IsPOVM M) (hN : IsPOVM N) (hρ : IsDensityMatrix ρ) :
    ccState ρ M N = Matrix.diagonal (fun ij => (jointMeasurement ρ M N ij : ℂ)) := by
  unfold ccState
  congr 1
  funext ij
  exact (jointMeasurement_real ρ M N hM hN hρ ij).symm

end Queelius.LocalBroadcasting

end

section
noncomputable section
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker

namespace Queelius.LocalBroadcast
open QAlgorithms

def ketBra {a b : Type} (u : EuclideanSpace ℂ a) (v : EuclideanSpace ℂ b) :
    Matrix a b ℂ := Matrix.of fun i j => u i * conj (v j)

theorem ketBra_adjoint {a b : Type} (u : EuclideanSpace ℂ a) (v : EuclideanSpace ℂ b) :
    (ketBra u v)ᴴ = ketBra v u := by
  ext i j
  simp [ketBra, Matrix.conjTranspose_apply, map_mul, mul_comm]

theorem ketBra_mul {a b c : Type} [Fintype b]
    (u : EuclideanSpace ℂ a) (v x : EuclideanSpace ℂ b) (y : EuclideanSpace ℂ c) :
    ketBra u v * ketBra x y = (inner ℂ v x) • ketBra u y := by
  ext i j
  simp only [ketBra, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    PiLp.inner_apply, RCLike.inner_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem basis_pure_sum {a ι : Type} [Fintype a] [DecidableEq a] [Fintype ι]
    (e : OrthonormalBasis ι ℂ (EuclideanSpace ℂ a)) :
    ∑ i, pureDensity (e i) = 1 := by
  ext x y
  have h := congrArg (fun v : EuclideanSpace ℂ a => v x)
    (e.sum_repr' (EuclideanSpace.single y 1))
  simpa [pureDensity, Matrix.sum_apply, PiLp.inner_apply, RCLike.inner_apply, Matrix.one_apply,
    PiLp.single_apply, mul_comm, eq_comm] using h

def copyKraus {a ι : Type} [Fintype a] [Fintype ι]
    (e : OrthonormalBasis ι ℂ (EuclideanSpace ℂ a)) (i : ι) : Matrix (a × a) a ℂ :=
  ketBra (tensorVec (e i) (e i)) (e i)

theorem basis_unit {a ι : Type} [Fintype a] [Fintype ι]
    (e : OrthonormalBasis ι ℂ (EuclideanSpace ℂ a)) (i : ι) : inner ℂ (e i) (e i) = 1 := by
  classical
  exact (orthonormal_iff_ite.mp e.orthonormal) i i |>.trans (if_pos rfl)

theorem copyKraus_normalized {a ι : Type} [Fintype a] [DecidableEq a] [Fintype ι]
    (e : OrthonormalBasis ι ℂ (EuclideanSpace ℂ a)) : IsKrausFamily (copyKraus e) := by
  unfold IsKrausFamily copyKraus
  simp only [ketBra_adjoint, ketBra_mul, tensor_inner, basis_unit, mul_one, one_smul]
  exact basis_pure_sum e

theorem copyKraus_on_basis {a ι : Type} [Fintype a] [DecidableEq ι] [Fintype ι]
    (e : OrthonormalBasis ι ℂ (EuclideanSpace ℂ a)) (i j : ι) :
    copyKraus e i * pureDensity (e j) * (copyKraus e i)ᴴ =
      if i = j then pureDensity (tensorVec (e j) (e j)) else 0 := by
  change ketBra _ _ * ketBra _ _ * (ketBra _ _)ᴴ = _
  rw [ketBra_adjoint, ketBra_mul, Matrix.smul_mul, ketBra_mul]
  simp only [orthonormal_iff_ite.mp e.orthonormal]
  by_cases h : i = j
  · subst j
    simp [ketBra, pureDensity]
  · simp [h, Ne.symm h]

theorem copyChannel_on_basis {a ι : Type} [Fintype a] [Fintype ι]
    (e : OrthonormalBasis ι ℂ (EuclideanSpace ℂ a)) (j : ι) :
    krausApply (copyKraus e) (pureDensity (e j)) = pureDensity (tensorVec (e j) (e j)) := by
  classical
  simp [krausApply, copyKraus_on_basis]

end Queelius.LocalBroadcast

end

section
noncomputable section
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker
namespace Queelius.LocalBroadcast
open QAlgorithms NoLocalBroadcast.Broadcast

theorem reindex_normalized {a b ι κ : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [Fintype ι] [Fintype κ] (K : ι → Matrix b a ℂ)
    (hK : IsKrausFamily K) (e : κ ≃ ι) : IsKrausFamily (fun j => K (e j)) :=
  (e.sum_comp (fun i => (K i)ᴴ * K i)).trans hK

theorem double_discardRight {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (σ : Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ) :
    krausApply (fun ij : a × b =>
      (@discardRight a a _ _ ij.1) ⊗ₖ (@discardRight b b _ _ ij.2)) σ = traceCopies σ := by
  ext p q
  simp [krausApply, discardRight, traceCopies, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.sum_apply, Finset.sum_mul, ite_and, apply_ite, eq_comm]

theorem double_discardLeft {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (σ : Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ) :
    krausApply (fun ij : a × b =>
      (@discardLeft a a _ _ ij.1) ⊗ₖ (@discardLeft b b _ _ ij.2)) σ = traceOriginals σ := by
  ext p q
  simp [krausApply, discardLeft, traceOriginals, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.sum_apply, Finset.sum_mul, ite_and, apply_ite, eq_comm]

theorem traceCopies_channels {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] :
    ∃ (m n : ℕ) (K : Fin m → Matrix a (a × a) ℂ) (L : Fin n → Matrix b (b × b) ℂ),
      IsKrausFamily K ∧ IsKrausFamily L ∧
      ∀ σ, localApply K L σ = traceCopies σ := by
  let ea : Fin (Fintype.card a) ≃ a := (Fintype.equivFin a).symm
  let eb : Fin (Fintype.card b) ≃ b := (Fintype.equivFin b).symm
  refine ⟨Fintype.card a, Fintype.card b, fun i => discardRight (ea i),
    fun j => discardRight (eb j), reindex_normalized _ discardRight_normalized ea,
    reindex_normalized _ discardRight_normalized eb, ?_⟩
  intro σ
  exact ((ea.prodCongr eb).sum_comp (fun ij =>
    (discardRight ij.1 ⊗ₖ discardRight ij.2) * σ *
    (discardRight ij.1 ⊗ₖ discardRight ij.2)ᴴ)).trans (double_discardRight σ)

theorem traceOriginals_channels {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] :
    ∃ (m n : ℕ) (K : Fin m → Matrix a (a × a) ℂ) (L : Fin n → Matrix b (b × b) ℂ),
      IsKrausFamily K ∧ IsKrausFamily L ∧
      ∀ σ, localApply K L σ = traceOriginals σ := by
  let ea : Fin (Fintype.card a) ≃ a := (Fintype.equivFin a).symm
  let eb : Fin (Fintype.card b) ≃ b := (Fintype.equivFin b).symm
  refine ⟨Fintype.card a, Fintype.card b, fun i => discardLeft (ea i),
    fun j => discardLeft (eb j), reindex_normalized _ discardLeft_normalized ea,
    reindex_normalized _ discardLeft_normalized eb, ?_⟩
  intro σ
  exact ((ea.prodCongr eb).sum_comp (fun ij =>
    (discardLeft ij.1 ⊗ₖ discardLeft ij.2) * σ *
    (discardLeft ij.1 ⊗ₖ discardLeft ij.2)ᴴ)).trans (double_discardLeft σ)

theorem traceCopies_density {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (σ : Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ)
    (hσ : IsDensityMatrix σ) : IsDensityMatrix (traceCopies σ) := by
  obtain ⟨m,n,K,L,hK,hL,he⟩ := @traceCopies_channels a b _ _ _ _
  rw [← he]
  exact local_density K L hK hL σ hσ

theorem traceOriginals_density {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (σ : Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ)
    (hσ : IsDensityMatrix σ) : IsDensityMatrix (traceOriginals σ) := by
  obtain ⟨m,n,K,L,hK,hL,he⟩ := @traceOriginals_channels a b _ _ _ _
  rw [← he]
  exact local_density K L hK hL σ hσ

theorem broadcast_source_density {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ)
    (σ : Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ)
    (hσ : IsBroadcastState ρ σ) : IsDensityMatrix ρ :=
  hσ.2.1 ▸ traceCopies_density σ hσ.1

end Queelius.LocalBroadcast

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset NoLocalBroadcast.Broadcast

 theorem mutualInfo_diagonal_nonnegative {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (p : a × b → ℝ)
    (hp : ∀ ij, 0 ≤ p ij) (hp1 : ∑ ij, p ij = 1) :
    0 ≤ mutualInfo (Matrix.diagonal (fun ij => (p ij : ℂ))) := by
  rw [mutualInfo_diagonal]
  simp only [Real.logb,← mul_div_assoc,← Finset.sum_div]
  have h := classical_log_subadditivity p hp hp1
  have hpos := div_nonneg (sub_nonneg.mpr h) (le_of_lt (Real.log_pos (by norm_num : (1:ℝ)<2)))
  dsimp only [rowProb,colProb] at hpos
  simp only [sub_div,add_div] at hpos
  linarith only [hpos]

end Queelius.LocalBroadcasting

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset
open Unitary
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem cfc_unitary_conjugation (U : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ)
    (hX : IsSelfAdjoint X) (f : ℝ → ℝ) (hf : Continuous f) :
    cfc f ((U : Matrix ι ι ℂ) * X * (U : Matrix ι ι ℂ)ᴴ) =
      (U : Matrix ι ι ℂ) * cfc f X * (U : Matrix ι ι ℂ)ᴴ := by
  let φ : Matrix ι ι ℂ →⋆ₐ[ℝ] Matrix ι ι ℂ :=
    (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℂ) U).toStarAlgHom
  have hc : Continuous φ := by
    change Continuous (fun X : Matrix ι ι ℂ => (U : Matrix ι ι ℂ)*X*star (U : Matrix ι ι ℂ))
    fun_prop
  have hφ : IsSelfAdjoint (φ X) := by
    change star (φ X) = φ X
    rw [← map_star,hX.star_eq]
  have hh := φ.map_cfc f X hf.continuousOn hc hX hφ
  change (U : Matrix ι ι ℂ) * cfc f X * star (U : Matrix ι ι ℂ) =
    cfc f ((U : Matrix ι ι ℂ)*X*star (U : Matrix ι ι ℂ)) at hh
  simpa only [Matrix.star_eq_conjTranspose] using hh.symm

theorem trace_unitary_conjugation (U : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ) :
    Matrix.trace ((U : Matrix ι ι ℂ) * X * (U : Matrix ι ι ℂ)ᴴ) = Matrix.trace X := by
  rw [Matrix.trace_mul_comm,← Matrix.mul_assoc,← Matrix.star_eq_conjTranspose,
    Matrix.UnitaryGroup.star_mul_self,Matrix.one_mul]

theorem entropy_unitary_conjugation (U : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ)
    (hX : IsSelfAdjoint X) :
    QAlgorithms.vnEntropy ((U : Matrix ι ι ℂ)*X*(U : Matrix ι ι ℂ)ᴴ) = QAlgorithms.vnEntropy X := by
  unfold QAlgorithms.vnEntropy
  rw [cfc_unitary_conjugation U X hX _ continuous_entropy_kernel,trace_unitary_conjugation]

theorem entropy_spectral (X : Matrix ι ι ℂ) (hX : X.IsHermitian) :
    QAlgorithms.vnEntropy X = -(∑ i, hX.eigenvalues i * Real.logb 2 (hX.eigenvalues i)) := by
  conv_lhs => rw [hX.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply,Unitary.coe_star,Matrix.star_eq_conjTranspose]
  rw [entropy_unitary_conjugation _ _ (by
    exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp))]
  exact entropy_diagonal _

end Queelius.LocalBroadcasting

end

section
noncomputable section
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker

namespace Queelius.LocalBroadcast
open QAlgorithms NoLocalBroadcast.Broadcast

theorem family_copy_channel {a ι : Type} [Fintype a] [DecidableEq a]
    (e : ι → EuclideanSpace ℂ a) (he : Orthonormal ℂ e) :
    ∃ (m : ℕ) (K : Fin m → Matrix (a × a) a ℂ), IsKrausFamily K ∧
      ∀ i, krausApply K (pureDensity (e i)) = pureDensity (tensorVec (e i) (e i)) := by
  classical
  obtain ⟨u,b,hu,hb⟩ := he.toSubtypeRange.exists_orthonormalBasis_extension
  let r : Fin (Fintype.card u) ≃ u := (Fintype.equivFin u).symm
  refine ⟨Fintype.card u, fun j => copyKraus b (r j), ?_, ?_⟩
  · unfold IsKrausFamily
    exact (r.sum_comp (fun i => (copyKraus b i)ᴴ * copyKraus b i)).trans
      (copyKraus_normalized b)
  · intro i
    let j : u := ⟨e i,hu (Set.mem_range_self i)⟩
    have hj : b j = e i := congrFun hb j
    rw [← hj]
    unfold krausApply
    exact (r.sum_comp (fun i => copyKraus b i * pureDensity (b j) * (copyKraus b i)ᴴ)).trans
      (copyChannel_on_basis b j)

theorem kraus_sum {a b ι κ : Type} [Fintype a] [Fintype ι] [Fintype κ]
    (K : ι → Matrix b a ℂ) (ρ : κ → Matrix a a ℂ) :
    krausApply K (∑ i, ρ i) = ∑ i, krausApply K (ρ i) := by
  simp only [krausApply, Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_comm

theorem kraus_smul {a b ι : Type} [Fintype a] [Fintype ι]
    (K : ι → Matrix b a ℂ) (ρ : Matrix a a ℂ) (c : ℂ) :
    krausApply K (c • ρ) = c • krausApply K ρ := by
  simp only [krausApply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

theorem local_product {a b a' b' : Type} [Fintype a] [Fintype b] {m n : ℕ}
    (K : Fin m → Matrix a' a ℂ) (L : Fin n → Matrix b' b ℂ)
    (ρ : Matrix a a ℂ) (σ : Matrix b b ℂ) :
    localApply K L (ρ ⊗ₖ σ) = krausApply K ρ ⊗ₖ krausApply L σ := by
  simp only [localApply, krausApply, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Fintype.sum_prod_type]
  ext p q
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]

theorem cc_locally_broadcastable {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hcc : IsClassicalClassical ρ) :
    IsLocallyBroadcastable ρ := by
  classical
  rcases hcc with ⟨k,l,e,f,p,he,hf,hp,hs,rfl⟩
  obtain ⟨m,K,hK,hKe⟩ := family_copy_channel e he
  obtain ⟨n,L,hL,hLf⟩ := family_copy_channel f hf
  have he' (i) : inner ℂ (e i) (e i) = 1 :=
    (orthonormal_iff_ite.mp he) i i |>.trans (if_pos rfl)
  have hf' (i) : inner ℂ (f i) (f i) = 1 :=
    (orthonormal_iff_ite.mp hf) i i |>.trans (if_pos rfl)
  have hout : localApply K L (∑ ij, (p ij : ℂ) • (pureDensity (e ij.1) ⊗ₖ pureDensity (f ij.2))) =
      ∑ ij, (p ij : ℂ) • copiedPure (e ij.1) (f ij.2) := by
    change krausApply _ _ = _
    rw [kraus_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [kraus_smul]
    congr 1
    change localApply K L _ = _
    rw [local_product,hKe,hLf]
    exact (pure_tensor _ _).symm
  refine ⟨m,n,K,L,hK,hL,?_⟩
  rw [hout]
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · apply Matrix.posSemidef_sum
    intro ij hij
    exact (copiedPure_density _ _ (he' _) (hf' _)).1.smul (by exact_mod_cast hp ij)
  · simp only [Matrix.trace_sum, Matrix.trace_smul,
      (copiedPure_density _ _ (he' _) (hf' _)).2, smul_eq_mul, mul_one]
    exact_mod_cast hs
  · ext x y
    simp only [traceCopies, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    conv_lhs => arg 2; ext x'; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ij hij
    simp only [← Finset.mul_sum]
    exact congrArg (fun M : Matrix _ _ ℂ => (p ij : ℂ) * M x y)
      (traceCopies_copiedPure _ _ (he' _) (hf' _))
  · ext x y
    simp only [traceOriginals, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    conv_lhs => arg 2; ext x'; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ij hij
    simp only [← Finset.mul_sum]
    exact congrArg (fun M : Matrix _ _ ℂ => (p ij : ℂ) * M x y)
      (traceOriginals_copiedPure _ _ (he' _) (hf' _))

end Queelius.LocalBroadcast

open NoLocalBroadcast.Broadcast in
theorem solution {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hcc : IsClassicalClassical ρ) :
    IsLocallyBroadcastable ρ := Queelius.LocalBroadcast.cc_locally_broadcastable ρ hcc

end

section
noncomputable section
open Matrix
open scoped Kronecker
namespace Queelius.LocalBroadcast
open QAlgorithms NoLocalBroadcast.Broadcast

/-- Open information-theoretic premise: the mutual-information part of Observation 1(i). -/
def MutualInfoDataProcessing : Prop :=
  ∀ {a b a' b' : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b'] {m n : ℕ},
    ∀ (K : Fin m → Matrix a' a ℂ) (L : Fin n → Matrix b' b ℂ),
      IsKrausFamily K → IsKrausFamily L →
      ∀ ρ, IsDensityMatrix ρ → mutualInfo (localApply K L ρ) ≤ mutualInfo ρ

/-- Open information-theoretic premise: precisely the local recovery conclusion of Lemma 2. -/
def LocalInfoRecovery : Prop :=
  ∀ {a b a' b' : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b'] {m n : ℕ},
    ∀ (K : Fin m → Matrix a' a ℂ) (L : Fin n → Matrix b' b ℂ),
      IsKrausFamily K → IsKrausFamily L →
      ∀ ρ, IsDensityMatrix ρ → mutualInfo (localApply K L ρ) = mutualInfo ρ →
      ∃ (m' n' : ℕ) (K' : Fin m' → Matrix a a' ℂ) (L' : Fin n' → Matrix b b' ℂ),
        IsKrausFamily K' ∧ IsKrausFamily L' ∧ localApply K' L' (localApply K L ρ) = ρ

theorem broadcast_recovery (hrec : LocalInfoRecovery)
    {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (ρ : Matrix (a × b) (a × b) ℂ)
    (σ : Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ)
    (hσ : IsBroadcastState ρ σ) (hI : mutualInfo σ = mutualInfo ρ) :
    ∃ (m n : ℕ) (K : Fin m → Matrix (a × a) a ℂ) (L : Fin n → Matrix (b × b) b ℂ),
      IsKrausFamily K ∧ IsKrausFamily L ∧ localApply K L ρ = σ := by
  obtain ⟨m,n,K,L,hK,hL,htrace⟩ := @traceCopies_channels a b _ _ _ _
  have he : localApply K L σ = ρ := (htrace σ).trans hσ.2.1
  obtain ⟨m',n',K',L',hK',hL',hr⟩ := hrec K L hK hL σ hσ.1 (by rw [he,hI])
  exact ⟨m',n',K',L',hK',hL',by simpa only [he] using hr⟩

theorem broadcast_information (hmono : MutualInfoDataProcessing)
    {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b] {m n : ℕ}
    (K : Fin m → Matrix (a × a) a ℂ) (L : Fin n → Matrix (b × b) b ℂ)
    (hK : IsKrausFamily K) (hL : IsKrausFamily L)
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : IsDensityMatrix ρ)
    (hb : IsBroadcastState ρ (localApply K L ρ)) :
    mutualInfo (localApply K L ρ) = mutualInfo ρ := by
  apply le_antisymm (hmono K L hK hL ρ hρ)
  obtain ⟨m',n',K',L',hK',hL',htrace⟩ := @traceCopies_channels a b _ _ _ _
  have h := hmono K' L' hK' hL' (localApply K L ρ) hb.1
  simpa only [htrace, hb.2.1] using h

/-- Conditional reduction only: both information principles remain open obligations. -/
theorem theorem2_of_information (hmono : MutualInfoDataProcessing) (hrec : LocalInfoRecovery)
    {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : IsDensityMatrix ρ) :
    (IsLocallyBroadcastable ρ ↔
      ∃ σ : Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ,
        IsBroadcastState ρ σ ∧ mutualInfo σ = mutualInfo ρ) ∧
    (∀ σ : Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ,
      IsBroadcastState ρ σ → mutualInfo σ = mutualInfo ρ →
      ∃ (m n : ℕ) (K : Fin m → Matrix (a × a) a ℂ) (L : Fin n → Matrix (b × b) b ℂ),
        IsKrausFamily K ∧ IsKrausFamily L ∧ localApply K L ρ = σ) := by
  refine ⟨⟨?_,?_⟩,fun σ hσ hI => broadcast_recovery hrec ρ σ hσ hI⟩
  · rintro ⟨m,n,K,L,hK,hL,hb⟩
    exact ⟨localApply K L ρ,hb,broadcast_information hmono K L hK hL ρ hρ hb⟩
  · rintro ⟨σ,hσ,hI⟩
    obtain ⟨m,n,K,L,hK,hL,he⟩ := broadcast_recovery hrec ρ σ hσ hI
    exact ⟨m,n,K,L,hK,hL,by simpa only [he] using hσ⟩

end Queelius.LocalBroadcast

end

section
noncomputable section
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker
namespace Queelius.LocalBroadcast.Controls
open QAlgorithms NoLocalBroadcast.Broadcast

theorem rectangular_channel :
    IsKrausFamily (@discardRight (Fin 2) (Fin 3) _ _) := discardRight_normalized

theorem retained_coherence :
    krausApply (@discardRight (Fin 2) (Fin 3) _ _)
      (Matrix.single (0,2) (1,2) (1 : ℂ)) = Matrix.single 0 1 1 := by
  rw [discardRight_action]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [traceRight, Matrix.single, Fin.sum_univ_succ]
  all_goals norm_num [eq_comm]
  all_goals decide

theorem discarded_coherence :
    krausApply (@discardRight (Fin 2) (Fin 3) _ _)
      (Matrix.single (0,2) (1,1) (1 : ℂ)) = 0 := by
  rw [discardRight_action]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [traceRight, Matrix.single, Fin.sum_univ_succ]
  all_goals norm_num [eq_comm]
  all_goals decide

def bellVector : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 fun ij => if ij.1 = ij.2 then 1 else 0

def bellState : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1/2 : ℂ) • pureDensity bellVector

theorem bell_density : IsDensityMatrix bellState := by
  constructor
  · exact (pure_psd bellVector).smul (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 1/2)
  · norm_num [bellState,pureDensity,bellVector,Matrix.trace,Matrix.diag,
      Fintype.sum_prod_type,Fin.sum_univ_two]

theorem bell_marginals : traceRight bellState = (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    traceLeft bellState = (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [traceRight,traceLeft,bellState,bellVector,pureDensity,Fin.sum_univ_two,Matrix.one_apply]

def orderingWitness : Matrix ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))
    ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℂ :=
  Matrix.single ((0,1),(1,0)) ((1,1),(0,0)) 1

theorem first_copy_order : traceCopies orderingWitness = Matrix.single (0,1) (1,0) 1 := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [traceCopies,orderingWitness,Matrix.single,Fin.sum_univ_two]
  all_goals norm_num [eq_comm]
  all_goals decide

theorem second_copy_order : traceOriginals orderingWitness = 0 := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [traceOriginals,orderingWitness,Matrix.single,Fin.sum_univ_two]

end Queelius.LocalBroadcast.Controls

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset NoLocalBroadcast.Broadcast
open scoped Kronecker

 theorem mutualInfo_diagonal_gibbs {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (p : a × b → ℝ) (hp : ∀ ij, 0 ≤ p ij) :
    mutualInfo (Matrix.diagonal (fun ij => (p ij : ℂ))) =
      ((∑ ij, p ij * Real.log (p ij)) -
        (∑ ij, p ij * Real.log (rowProb p ij.1 * colProb p ij.2))) / Real.log 2 := by
  rw [mutualInfo_diagonal,log_marginal_decomposition p hp]
  simp only [Real.logb,← mul_div_assoc,← Finset.sum_div,rowProb,colProb]
  ring

 theorem mutualInfo_diagonal_zero_iff {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (p : a × b → ℝ)
    (hp : ∀ ij, 0 ≤ p ij) (hp1 : ∑ ij, p ij = 1) :
    mutualInfo (Matrix.diagonal (fun ij => (p ij : ℂ))) = 0 ↔
      ∀ ij, p ij = rowProb p ij.1 * colProb p ij.2 := by
  let q : a × b → ℝ := fun ij => rowProb p ij.1 * colProb p ij.2
  have hq : ∀ ij, 0 ≤ q ij := fun ij => mul_nonneg (row_nonnegative p hp _) (col_nonnegative p hp _)
  have hq1 : ∑ ij, q ij = 1 := marginal_product_sum p hp1
  have hs : ∀ ij, 0 < p ij → 0 < q ij := by
    intro ij h
    exact mul_pos (h.trans_le (joint_le_row p hp ij.1 ij.2)) (h.trans_le (joint_le_col p hp ij.1 ij.2))
  have hn : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1:ℝ)<2))
  rw [mutualInfo_diagonal_gibbs p hp,div_eq_zero_iff]
  simp only [hn,or_false,sub_eq_zero]
  change (∑ ij, p ij * Real.log (p ij)) = (∑ ij, p ij * Real.log (q ij)) ↔ _
  rw [eq_comm,finite_gibbs_equality p q hp hq hp1 hq1 hs]
  exact funext_iff

 theorem diagonal_factorized_iff_zero {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (p : a × b → ℝ)
    (hp : ∀ ij, 0 ≤ p ij) (hp1 : ∑ ij, p ij = 1) :
    mutualInfo (Matrix.diagonal (fun ij => (p ij : ℂ))) = 0 ↔
      Matrix.diagonal (fun ij => (p ij : ℂ)) =
        QAlgorithms.traceRight (Matrix.diagonal (fun ij => (p ij : ℂ))) ⊗ₖ
        QAlgorithms.traceLeft (Matrix.diagonal (fun ij => (p ij : ℂ))) := by
  rw [mutualInfo_diagonal_zero_iff p hp hp1,traceRight_diagonal,traceLeft_diagonal,
    Matrix.diagonal_kronecker_diagonal,Matrix.diagonal_injective.eq_iff,funext_iff]
  simp only [← Complex.ofReal_mul,Complex.ofReal_inj,rowProb,colProb]

end Queelius.LocalBroadcasting

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset QAlgorithms NoLocalBroadcast.Broadcast
open scoped ComplexOrder

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

 theorem ccState_nonnegative {m n : ℕ} (ρ : Matrix (a × b) (a × b) ℂ)
    (M : Fin m → Matrix a a ℂ) (N : Fin n → Matrix b b ℂ)
    (hM : IsPOVM M) (hN : IsPOVM N) (hρ : IsDensityMatrix ρ) :
    0 ≤ mutualInfo (ccState ρ M N) := by
  rw [ccState_diagonal_law ρ M N hM hN hρ]
  exact mutualInfo_diagonal_nonnegative _ (jointMeasurement_nonnegative ρ M N hM hN hρ)
    (jointMeasurement_sum ρ M N hM hN hρ)

 theorem icc_nonnegative_general [Nonempty a] [Nonempty b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : IsDensityMatrix ρ) : 0 ≤ I_CC ρ := by
  let S : Set ℝ := {x | ∃ (n n' : ℕ) (M : Fin n → Matrix a a ℂ) (N : Fin n' → Matrix b b ℂ),
    IsPOVM M ∧ IsPOVM N ∧ x = mutualInfo (ccState ρ M N)}
  change 0 ≤ sSup S
  by_cases hb : BddAbove S
  · have hM : IsPOVM (fun _ : Fin 1 => (1 : Matrix a a ℂ)) := ⟨fun _ => .one, by simp⟩
    have hN : IsPOVM (fun _ : Fin 1 => (1 : Matrix b b ℂ)) := ⟨fun _ => .one, by simp⟩
    have hx : mutualInfo (ccState ρ (fun _ : Fin 1 => (1 : Matrix a a ℂ))
        (fun _ : Fin 1 => (1 : Matrix b b ℂ))) ∈ S := ⟨1,1,_,_,hM,hN,rfl⟩
    exact (ccState_nonnegative ρ _ _ hM hN hρ).trans (le_csSup hb hx)
  · rw [csSup_of_not_bddAbove hb]
    simp

end Queelius.LocalBroadcasting

namespace Queelius.LocalBroadcasting
 theorem icc_nonnegative {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    0 ≤ NoLocalBroadcast.Broadcast.I_CC ρ := icc_nonnegative_general ρ hρ
end Queelius.LocalBroadcasting

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem shannon_nonnegative (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    0 ≤ -(∑ i, p i * Real.logb 2 (p i)) := by
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro i hi
  have hle : p i ≤ 1 := by
    rw [← hp1]
    exact Finset.single_le_sum (fun j hj => hp j) hi
  apply mul_nonpos_of_nonneg_of_nonpos (hp i)
  exact div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos (hp i) hle) (le_of_lt (Real.log_pos (by norm_num : (1:ℝ)<2)))

theorem shannon_le_log_card (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    -(∑ i, p i * Real.logb 2 (p i)) ≤ Real.logb 2 (Fintype.card ι) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hq1 : ∑ _ : ι, (1 : ℝ)/(Fintype.card ι) = 1 := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    field_simp
  have hg := finite_gibbs p (fun _ => (1 : ℝ)/Fintype.card ι) hp
    (fun _ => le_of_lt (one_div_pos.mpr hn)) hp1 hq1 (fun _ _ => one_div_pos.mpr hn)
  have hlog : Real.log ((1 : ℝ)/Fintype.card ι) = -Real.log (Fintype.card ι) := by
    simp [Real.log_div,ne_of_gt hn]
  simp only [hlog,← Finset.sum_mul,hp1,one_mul] at hg
  have hd := div_le_div_of_nonneg_right hg (le_of_lt (Real.log_pos (by norm_num : (1:ℝ)<2)))
  simp only [Real.logb,← mul_div_assoc,← Finset.sum_div]
  rw [neg_div] at hd
  linarith

theorem density_eigenvalues_sum (ρ : Matrix ι ι ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    ∑ i, hρ.1.isHermitian.eigenvalues i = 1 := by
  have ht := hρ.1.isHermitian.trace_eq_sum_eigenvalues
  have hr := congrArg Complex.re (ht.symm.trans hρ.2)
  simpa using hr

theorem entropy_nonnegative (ρ : Matrix ι ι ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    0 ≤ QAlgorithms.vnEntropy ρ := by
  rw [entropy_spectral ρ hρ.1.isHermitian]
  exact shannon_nonnegative _ (hρ.1.eigenvalues_nonneg) (density_eigenvalues_sum ρ hρ)

theorem entropy_le_log_dimension (ρ : Matrix ι ι ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    QAlgorithms.vnEntropy ρ ≤ Real.logb 2 (Fintype.card ι) := by
  rw [entropy_spectral ρ hρ.1.isHermitian]
  exact shannon_le_log_card _ (hρ.1.eigenvalues_nonneg) (density_eigenvalues_sum ρ hρ)

end Queelius.LocalBroadcasting

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset
open scoped Matrix.Norms.L2Operator
variable {ι b : Type} [Fintype ι] [DecidableEq ι] [Fintype b] [DecidableEq b]

def blockDiagonalStarAlg : (ι → Matrix b b ℂ) →⋆ₐ[ℝ] Matrix (b × ι) (b × ι) ℂ :=
  { Matrix.blockDiagonalRingHom b ι ℂ with
    commutes' := by
      intro r
      simp only [Algebra.algebraMap_eq_smul_one]
      change Matrix.blockDiagonal (r • (1 : ι → Matrix b b ℂ)) = r • (1 : Matrix (b × ι) (b × ι) ℂ)
      rw [Matrix.blockDiagonal_smul,Matrix.blockDiagonal_one]
    map_star' := by
      intro X
      exact (Matrix.blockDiagonal_conjTranspose X).symm }

theorem cfc_blockDiagonal [Nonempty ι] [Nonempty b]
    (X : ι → Matrix b b ℂ) (hX : ∀ i, (X i).IsHermitian)
    (f : ℝ → ℝ) (hf : Continuous f) :
    cfc f (Matrix.blockDiagonal X) = Matrix.blockDiagonal (fun i => cfc f (X i)) := by
  letI : ContinuousFunctionalCalculus ℂ (ι → Matrix b b ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : ContinuousFunctionalCalculus ℝ (ι → Matrix b b ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  have hs : IsSelfAdjoint X := by
    change star X = X
    funext i
    exact (hX i).eq
  have hb : IsSelfAdjoint (blockDiagonalStarAlg X) := by
    change star (blockDiagonalStarAlg X) = blockDiagonalStarAlg X
    rw [← map_star,hs.star_eq]
  have hc : Continuous (blockDiagonalStarAlg (ι := ι) (b := b)) := by
    change Continuous (Matrix.blockDiagonal : (ι → Matrix b b ℂ) → Matrix (b × ι) (b × ι) ℂ)
    apply continuous_pi
    intro p
    apply continuous_pi
    intro q
    by_cases h : p.2=q.2 <;> simp only [Matrix.blockDiagonal_apply,h,ite_true,ite_false] <;> fun_prop
  have hh := (blockDiagonalStarAlg (ι := ι) (b := b)).map_cfc f X hf.continuousOn hc hs hb
  rw [cfc_map_pi (S := ℝ) f X hf.continuousOn hs hX] at hh
  exact hh.symm

theorem trace_blockDiagonal (X : ι → Matrix b b ℂ) :
    (Matrix.blockDiagonal X).trace = ∑ i, (X i).trace := by
  simp only [Matrix.trace,Matrix.diag,Matrix.blockDiagonal,Matrix.of_apply,ite_true,Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem entropy_blockDiagonal [Nonempty ι] [Nonempty b]
    (X : ι → Matrix b b ℂ) (hX : ∀ i, (X i).IsHermitian) :
    QAlgorithms.vnEntropy (Matrix.blockDiagonal X) = ∑ i, QAlgorithms.vnEntropy (X i) := by
  unfold QAlgorithms.vnEntropy
  rw [cfc_blockDiagonal X hX _ continuous_entropy_kernel,trace_blockDiagonal]
  simp

end Queelius.LocalBroadcasting

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]

def reindexStarAlg (e : ι ≃ κ) : Matrix ι ι ℂ →⋆ₐ[ℝ] Matrix κ κ ℂ :=
  { (Matrix.reindexAlgEquiv ℝ ℂ e).toAlgHom with
    map_star' := by intro X; exact (Matrix.conjTranspose_reindex e e X).symm }

theorem cfc_reindex (e : ι ≃ κ) (X : Matrix ι ι ℂ) (hX : X.IsHermitian)
    (f : ℝ → ℝ) (hf : Continuous f) :
    cfc f (Matrix.reindex e e X) = Matrix.reindex e e (cfc f X) := by
  have hc : Continuous (reindexStarAlg e) := by
    change Continuous (fun X => Matrix.reindex e e X)
    fun_prop
  have hh : IsSelfAdjoint (reindexStarAlg e X) := by
    change star (reindexStarAlg e X) = reindexStarAlg e X
    rw [← map_star,Matrix.star_eq_conjTranspose,hX.eq]
  exact ((reindexStarAlg e).map_cfc f X hf.continuousOn hc hX hh).symm

theorem trace_reindex (e : ι ≃ κ) (X : Matrix ι ι ℂ) :
    (Matrix.reindex e e X).trace = X.trace := by
  exact e.symm.sum_comp (fun i => X i i)

theorem entropy_reindex (e : ι ≃ κ) (X : Matrix ι ι ℂ) (hX : X.IsHermitian) :
    QAlgorithms.vnEntropy (Matrix.reindex e e X) = QAlgorithms.vnEntropy X := by
  unfold QAlgorithms.vnEntropy
  rw [cfc_reindex e X hX _ continuous_entropy_kernel,trace_reindex]

end Queelius.LocalBroadcasting

end

section
noncomputable section
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker

namespace Queelius.LocalBroadcast.Controls
open QAlgorithms NoLocalBroadcast.Broadcast

def bits : OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)) :=
  EuclideanSpace.basisFun (Fin 2) ℂ

def correlated : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ∑ ij : Fin 2 × Fin 2, (if ij.1 = ij.2 then (1 / 2 : ℂ) else 0) •
    (pureDensity (bits ij.1) ⊗ₖ pureDensity (bits ij.2))

theorem correlated_classical : IsClassicalClassical correlated := by
  refine ⟨2,2,bits,bits,(fun ij => if ij.1 = ij.2 then (1/2:ℝ) else 0),
    bits.orthonormal,bits.orthonormal,?_,?_,?_⟩
  · intro ij
    dsimp
    split_ifs <;> norm_num
  · simp [Fintype.sum_prod_type,Fin.sum_univ_two]
  · unfold correlated
    apply Finset.sum_congr rfl
    intro ij hij
    congr 1
    split_ifs with h <;> simp [h]

theorem correlated_broadcastable : IsLocallyBroadcastable correlated :=
  Queelius.LocalBroadcast.cc_locally_broadcastable correlated correlated_classical

theorem correlated_entries :
    correlated (0,0) (0,0) = 1/2 ∧ correlated (1,1) (1,1) = 1/2 ∧
    correlated (0,1) (0,1) = 0 ∧ correlated (1,0) (1,0) = 0 := by
  norm_num [correlated,Fintype.sum_prod_type,Fin.sum_univ_two,Matrix.sum_apply,
    Matrix.smul_apply,Matrix.kronecker_apply,pureDensity,bits,
    EuclideanSpace.basisFun_apply,PiLp.single_apply]

theorem correlated_not_product :
    ¬ ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, correlated = A ⊗ₖ B := by
  rintro ⟨A,B,h⟩
  have h00 := congrArg (fun M : Matrix _ _ ℂ => M (0,0) (0,0)) h
  have h11 := congrArg (fun M : Matrix _ _ ℂ => M (1,1) (1,1)) h
  have h01 := congrArg (fun M : Matrix _ _ ℂ => M (0,1) (0,1)) h
  have h10 := congrArg (fun M : Matrix _ _ ℂ => M (1,0) (1,0)) h
  have hc := correlated_entries
  simp only [Matrix.kronecker_apply,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2] at h00 h11 h01 h10
  have hh : (A 0 0 * B 0 0) * (A 1 1 * B 1 1) =
      (A 0 0 * B 1 1) * (A 1 1 * B 0 0) := by ring
  rw [← h00,← h11,← h01,← h10] at hh
  norm_num at hh

theorem incomplete_family_naive_channel_fails :
    ¬ IsKrausFamily (fun _ : Fin 1 => copyKraus bits 0) := by
  intro h
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) h
  norm_num [copyKraus,ketBra,tensorVec,bits,EuclideanSpace.basisFun_apply,
    PiLp.single_apply,Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fintype.sum_prod_type,Fin.sum_univ_two,Matrix.one_apply] at hh

theorem incomplete_family_extendable :
    ∃ (m : ℕ) (K : Fin m → Matrix (Fin 2 × Fin 2) (Fin 2) ℂ), IsKrausFamily K ∧
      krausApply K (pureDensity (bits 0)) = pureDensity (tensorVec (bits 0) (bits 0)) := by
  have he : Orthonormal ℂ (fun _ : Fin 1 => bits 0) := by
    rw [orthonormal_iff_ite]
    intro i j
    have h : i=j := Subsingleton.elim _ _
    simp [h,basis_unit]
  obtain ⟨m,K,hK,h⟩ := family_copy_channel (fun _ : Fin 1 => bits 0) he
  exact ⟨m,K,hK,h 0⟩

end Queelius.LocalBroadcast.Controls

end

section
noncomputable section
namespace Queelius.LocalBroadcasting.Controls
open Matrix Finset NoLocalBroadcast.Broadcast QAlgorithms
open scoped Kronecker

def correlated : Fin 2 × Fin 2 → ℝ := fun ij => if ij.1=ij.2 then 1/2 else 0

theorem correlated_normalized : (∀ ij, 0 ≤ correlated ij) ∧ ∑ ij, correlated ij = 1 := by
  constructor
  · intro ij; unfold correlated; split_ifs <;> norm_num
  · norm_num [correlated,Fintype.sum_prod_type,Fin.sum_univ_two]

theorem half_log : Real.logb 2 (1/2) = -1 := by
  rw [Real.logb_div (by norm_num) (by norm_num)]
  norm_num [Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]

theorem quarter_log : Real.logb 2 (1/4) = -2 := by
  have h : (1/4 : ℝ) = (1/2)^2 := by norm_num
  rw [h,Real.logb_pow,half_log]
  norm_num

theorem correlated_one_bit : mutualInfo (Matrix.diagonal (fun ij => (correlated ij : ℂ))) = 1 := by
  rw [mutualInfo_diagonal]
  norm_num [correlated,Fintype.sum_prod_type,Fin.sum_univ_two,half_log]

theorem independent_zero : mutualInfo (Matrix.diagonal (fun _ : Fin 2 × Fin 2 => (1/4 : ℂ))) = 0 := by
  have h : (fun _ : Fin 2 × Fin 2 => (1/4 : ℂ)) = fun _ => ((1/4 : ℝ) : ℂ) := by ext; norm_num
  rw [h,mutualInfo_diagonal]
  norm_num [Fintype.sum_prod_type,Fin.sum_univ_two,half_log,quarter_log]

theorem zero_support_deterministic :
    mutualInfo (Matrix.diagonal (fun ij : Fin 2 × Fin 2 => ((if ij=(0,0) then 1 else 0 : ℝ) : ℂ))) = 0 := by
  rw [mutualInfo_diagonal]
  have hc : (Finset.univ.filter (fun x : Fin 2 => x=0)).card = 1 := by decide
  norm_num [Fintype.sum_prod_type,Fin.sum_univ_two,hc]

end Queelius.LocalBroadcasting.Controls

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset
open scoped ComplexOrder Kronecker
variable {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]

def tensorUnitary (U : Matrix.unitaryGroup a ℂ) (V : Matrix.unitaryGroup b ℂ) :
    Matrix.unitaryGroup (a × b) ℂ :=
  ⟨(U : Matrix a a ℂ) ⊗ₖ (V : Matrix b b ℂ), Matrix.kronecker_mem_unitary U.prop V.prop⟩

theorem tensor_unitary_conjugation (U : Matrix.unitaryGroup a ℂ) (V : Matrix.unitaryGroup b ℂ)
    (A : Matrix a a ℂ) (B : Matrix b b ℂ) :
    ((U : Matrix a a ℂ)*A*(U : Matrix a a ℂ)ᴴ) ⊗ₖ
      ((V : Matrix b b ℂ)*B*(V : Matrix b b ℂ)ᴴ) =
      (tensorUnitary U V : Matrix (a × b) (a × b) ℂ) * (A ⊗ₖ B) *
        (tensorUnitary U V : Matrix (a × b) (a × b) ℂ)ᴴ := by
  simp only [tensorUnitary,Matrix.conjTranspose_kronecker,Matrix.mul_kronecker_mul]

theorem shannon_product (p : a → ℝ) (q : b → ℝ)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ j, q j = 1) :
    -(∑ ij : a × b, p ij.1*q ij.2*Real.logb 2 (p ij.1*q ij.2)) =
      -(∑ i, p i*Real.logb 2 (p i)) -(∑ j, q j*Real.logb 2 (q j)) := by
  have hterm (i : a) (j : b) : p i*q j*Real.logb 2 (p i*q j) =
      (p i*Real.logb 2 (p i))*q j + p i*(q j*Real.logb 2 (q j)) := by
    by_cases h0 : p i=0
    · simp [h0]
    by_cases h1 : q j=0
    · simp [h1]
    rw [Real.logb_mul h0 h1]
    ring
  simp_rw [Fintype.sum_prod_type,hterm,Finset.sum_add_distrib,
    ← Finset.mul_sum,hq1,mul_one,← Finset.sum_mul,hp1,one_mul]
  ring

theorem entropy_tensor_density (A : Matrix a a ℂ) (B : Matrix b b ℂ)
    (hA : QAlgorithms.IsDensityMatrix A) (hB : QAlgorithms.IsDensityMatrix B) :
    QAlgorithms.vnEntropy (A ⊗ₖ B) = QAlgorithms.vnEntropy A + QAlgorithms.vnEntropy B := by
  have hspec : A ⊗ₖ B =
      (tensorUnitary hA.1.isHermitian.eigenvectorUnitary hB.1.isHermitian.eigenvectorUnitary :
        Matrix (a × b) (a × b) ℂ) *
      Matrix.diagonal (fun ij => ((hA.1.isHermitian.eigenvalues ij.1 *
        hB.1.isHermitian.eigenvalues ij.2 : ℝ) : ℂ)) *
      (tensorUnitary hA.1.isHermitian.eigenvectorUnitary hB.1.isHermitian.eigenvectorUnitary :
        Matrix (a × b) (a × b) ℂ)ᴴ := by
    conv_lhs => rw [hA.1.isHermitian.spectral_theorem,hB.1.isHermitian.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply,Unitary.coe_star,Matrix.star_eq_conjTranspose]
    rw [tensor_unitary_conjugation,Matrix.diagonal_kronecker_diagonal]
    simp only [Function.comp_apply,RCLike.ofReal_eq_complex_ofReal,Complex.ofReal_mul]
  rw [hspec,entropy_unitary_conjugation _ _ (by
    exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext ij; simp)),entropy_diagonal,
    shannon_product _ _ (density_eigenvalues_sum A hA) (density_eigenvalues_sum B hB),
    entropy_spectral A hA.1.isHermitian,entropy_spectral B hB.1.isHermitian]
  ring

end Queelius.LocalBroadcasting

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem shannon_negMulLog (p : ι → ℝ) :
    -(∑ i, p i * Real.logb 2 (p i)) =
      (∑ i, Real.negMulLog (p i)) / Real.log 2 := by
  simp only [Real.logb,Real.negMulLog,← mul_div_assoc,← Finset.sum_div,
    neg_mul,Finset.sum_neg_distrib,neg_div]

theorem hermitian_diagonal_spectral_mix (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (i : ι) :
    (X i i).re = ∑ j, Complex.normSq ((hX.eigenvectorUnitary : Matrix ι ι ℂ) i j) * hX.eigenvalues j := by
  nth_rw 1 [hX.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply,Unitary.coe_star,Matrix.star_eq_conjTranspose]
  exact unitary_diagonal_mix _ _ _

theorem entropy_le_diagonal_shannon (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) :
    QAlgorithms.vnEntropy ρ ≤ -(∑ i, (ρ i i).re * Real.logb 2 (ρ i i).re) := by
  rw [entropy_spectral ρ hρ.isHermitian,shannon_negMulLog,shannon_negMulLog]
  apply div_le_div_of_nonneg_right _ (le_of_lt (Real.log_pos (by norm_num : (1:ℝ)<2)))
  have h := doubly_stochastic_entropy
    (fun i j => Complex.normSq ((hρ.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) i j))
    hρ.isHermitian.eigenvalues hρ.eigenvalues_nonneg
    (fun i j => Complex.normSq_nonneg _) (unitary_row_normSq _) (unitary_col_normSq _)
  simpa only [← hermitian_diagonal_spectral_mix ρ hρ.isHermitian] using h

end Queelius.LocalBroadcasting

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem entropy_real_smul (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (c : ℝ) :
    QAlgorithms.vnEntropy ((c : ℂ) • X) =
      c * QAlgorithms.vnEntropy X - (c * Real.logb 2 c) * X.trace.re := by
  let U := hX.eigenvectorUnitary
  have hs : (c : ℂ) • X = (U : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i => ((c*hX.eigenvalues i : ℝ) : ℂ)) * (U : Matrix ι ι ℂ)ᴴ := by
    have hd : Matrix.diagonal (fun i => ((c*hX.eigenvalues i : ℝ) : ℂ)) =
        (c : ℂ) • Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) := by
      rw [← Matrix.diagonal_smul]
      congr 1
      funext i
      simp
    rw [hd,Matrix.mul_smul,Matrix.smul_mul]
    have h := congrArg (fun M : Matrix ι ι ℂ => (c : ℂ) • M) hX.spectral_theorem
    simpa only [Unitary.conjStarAlgAut_apply,Unitary.coe_star,Matrix.star_eq_conjTranspose,
      Function.comp_def,RCLike.ofReal_eq_complex_ofReal,U] using h
  rw [hs,entropy_unitary_conjugation U _ (by
    exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)),entropy_diagonal]
  have hterm (i : ι) : c*hX.eigenvalues i*Real.logb 2 (c*hX.eigenvalues i) =
      c*(hX.eigenvalues i*Real.logb 2 (hX.eigenvalues i)) +
        (c*Real.logb 2 c)*hX.eigenvalues i := by
    by_cases hc : c=0
    · simp [hc]
    by_cases hi : hX.eigenvalues i=0
    · simp [hi]
    rw [Real.logb_mul hc hi]
    ring
  have ht : ∑ i, hX.eigenvalues i = X.trace.re := by
    simpa using congrArg Complex.re hX.trace_eq_sum_eigenvalues.symm
  simp_rw [hterm,Finset.sum_add_distrib,← Finset.mul_sum,ht]
  rw [entropy_spectral X hX]
  ring

theorem entropy_scaled_density (X : Matrix ι ι ℂ) (hX : QAlgorithms.IsDensityMatrix X) (c : ℝ) :
    QAlgorithms.vnEntropy ((c : ℂ) • X) = c*QAlgorithms.vnEntropy X - c*Real.logb 2 c := by
  rw [entropy_real_smul X hX.1.isHermitian c,hX.2]
  simp

end Queelius.LocalBroadcasting

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset QAlgorithms NoLocalBroadcast.Broadcast
open scoped ComplexOrder Kronecker
variable {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]

theorem traceRight_tensor (A : Matrix a a ℂ) (B : Matrix b b ℂ) :
    traceRight (A ⊗ₖ B) = B.trace • A := by
  ext i j
  simp [traceRight,Matrix.kronecker,Matrix.trace,Finset.mul_sum,mul_comm]

theorem traceLeft_tensor (A : Matrix a a ℂ) (B : Matrix b b ℂ) :
    traceLeft (A ⊗ₖ B) = A.trace • B := by
  ext i j
  simp [traceLeft,Matrix.kronecker,Matrix.trace,Finset.sum_mul]

theorem tensor_density (A : Matrix a a ℂ) (B : Matrix b b ℂ)
    (hA : IsDensityMatrix A) (hB : IsDensityMatrix B) : IsDensityMatrix (A ⊗ₖ B) :=
  ⟨hA.1.kronecker hB.1, by rw [Matrix.trace_kronecker,hA.2,hB.2,mul_one]⟩

theorem traceRight_density (ρ : Matrix (a × b) (a × b) ℂ) (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (traceRight ρ) := by
  rw [← Queelius.LocalBroadcast.discardRight_action]
  exact Queelius.LocalBroadcast.kraus_density _ Queelius.LocalBroadcast.discardRight_normalized ρ hρ

theorem traceLeft_density (ρ : Matrix (a × b) (a × b) ℂ) (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (traceLeft ρ) := by
  rw [← Queelius.LocalBroadcast.discardLeft_action]
  exact Queelius.LocalBroadcast.kraus_density _ Queelius.LocalBroadcast.discardLeft_normalized ρ hρ

theorem mutualInfo_product_zero (A : Matrix a a ℂ) (B : Matrix b b ℂ)
    (hA : IsDensityMatrix A) (hB : IsDensityMatrix B) : mutualInfo (A ⊗ₖ B) = 0 := by
  rw [mutualInfo,traceRight_tensor,traceLeft_tensor,hA.2,hB.2,one_smul,one_smul,
    entropy_tensor_density A B hA hB]
  ring

theorem mutualInfo_zero_of_factorized (ρ : Matrix (a × b) (a × b) ℂ) (hρ : IsDensityMatrix ρ) :
    ρ = traceRight ρ ⊗ₖ traceLeft ρ → mutualInfo ρ = 0 := by
  intro h
  have he := mutualInfo_product_zero (traceRight ρ) (traceLeft ρ)
    (traceRight_density ρ hρ) (traceLeft_density ρ hρ)
  rwa [← h] at he

theorem mutualInfo_le_dimension_sum (ρ : Matrix (a × b) (a × b) ℂ) (hρ : IsDensityMatrix ρ) :
    mutualInfo ρ ≤ Real.logb 2 (Fintype.card a) + Real.logb 2 (Fintype.card b) := by
  have ha := entropy_le_log_dimension _ (traceRight_density ρ hρ)
  have hb := entropy_le_log_dimension _ (traceLeft_density ρ hρ)
  have hz := entropy_nonnegative ρ hρ
  unfold mutualInfo
  linarith

end Queelius.LocalBroadcasting

end

section
noncomputable section
namespace Queelius.LocalBroadcasting.Controls
open Matrix Finset QAlgorithms NoLocalBroadcast.Broadcast
open scoped ComplexOrder Kronecker

def rationalRotation : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨!![(3:ℂ)/5, -4/5; 4/5, 3/5], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply,map_ofNat,Matrix.vecMul,dotProduct]⟩

def coherentState : Matrix (Fin 2) (Fin 2) ℂ := !![9/25,12/25;12/25,16/25]

theorem coherent_conjugation : coherentState =
    (rationalRotation : Matrix (Fin 2) (Fin 2) ℂ) *
    Matrix.diagonal (fun i : Fin 2 => ((if i=0 then 1 else 0 : ℝ) : ℂ)) *
    (rationalRotation : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coherentState,rationalRotation,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.diagonal_apply,Matrix.conjTranspose_apply,map_ofNat,Matrix.vecMul,dotProduct]

theorem coherent_density : IsDensityMatrix coherentState := by
  constructor
  · rw [coherent_conjugation]
    exact (Matrix.PosSemidef.diagonal (fun i => by split_ifs <;> norm_num)).mul_mul_conjTranspose_same _
  · norm_num [coherentState,Matrix.trace,Matrix.diag,Fin.sum_univ_two]

theorem coherent_zero_entropy : vnEntropy coherentState = 0 := by
  rw [coherent_conjugation,entropy_unitary_conjugation _ _ (by
    exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)),entropy_diagonal]
  norm_num [Fin.sum_univ_two]

theorem coherent_off_diagonal : coherentState 0 1 ≠ 0 := by
  norm_num [coherentState]

theorem maximally_mixed_one_bit :
    vnEntropy (Matrix.diagonal (fun _ : Fin 2 => ((1/2 : ℝ) : ℂ))) = 1 := by
  rw [entropy_diagonal]
  norm_num [Fin.sum_univ_two,half_log]

theorem product_additivity_control :
    vnEntropy ((Matrix.diagonal (fun _ : Fin 2 => ((1/2 : ℝ) : ℂ))) ⊗ₖ coherentState) = 1 := by
  rw [entropy_tensor_density _ _ ⟨Matrix.PosSemidef.diagonal (by intro; norm_num [Complex.nonneg_iff]), by
    norm_num [Matrix.trace,Matrix.diag,Fin.sum_univ_two]⟩ coherent_density,
    maximally_mixed_one_bit,coherent_zero_entropy,add_zero]

theorem normalization_guard_control :
    vnEntropy (Matrix.diagonal (fun _ : Fin 1 => ((2:ℝ):ℂ))) = -2 := by
  rw [entropy_diagonal]
  norm_num [Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]

end Queelius.LocalBroadcasting.Controls

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset
open scoped Kronecker
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem unitary_cross_columns (V : Matrix.unitaryGroup b ℂ) (p q : b) :
    ∑ j, (V : Matrix b b ℂ) j p * star ((V : Matrix b b ℂ) j q) = if p=q then 1 else 0 := by
  have h := congrFun (congrFun V.property.1 q) p
  simpa [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,
    Matrix.one_apply,mul_comm,eq_comm] using h

theorem traceRight_local_unitary (U : Matrix.unitaryGroup a ℂ) (V : Matrix.unitaryGroup b ℂ)
    (ρ : Matrix (a × b) (a × b) ℂ) :
    QAlgorithms.traceRight ((tensorUnitary U V : Matrix (a × b) (a × b) ℂ) * ρ *
      (tensorUnitary U V : Matrix (a × b) (a × b) ℂ)ᴴ) =
    (U : Matrix a a ℂ) * QAlgorithms.traceRight ρ * (U : Matrix a a ℂ)ᴴ := by
  ext i k
  simp only [QAlgorithms.traceRight,tensorUnitary,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.kronecker_apply,Matrix.kroneckerMap_apply,Matrix.of_apply,Finset.sum_mul]
  have cross (p q : a × b) :
      (∑ j : b, (U : Matrix a a ℂ) i p.1 * (V : Matrix b b ℂ) j p.2 * ρ p q *
        star ((U : Matrix a a ℂ) k q.1 * (V : Matrix b b ℂ) j q.2)) =
      ((U : Matrix a a ℂ) i p.1 * ρ p q * star ((U : Matrix a a ℂ) k q.1)) *
        (if p.2=q.2 then 1 else 0) := by
    calc
      _ = ((U : Matrix a a ℂ) i p.1 * ρ p q * star ((U : Matrix a a ℂ) k q.1)) *
          (∑ j : b, (V : Matrix b b ℂ) j p.2 * star ((V : Matrix b b ℂ) j q.2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [star_mul]
        ring
      _ = _ := by rw [unitary_cross_columns]

  calc
    _ = ∑ q : a × b, ∑ p : a × b,
        ((U : Matrix a a ℂ) i p.1 * ρ p q * star ((U : Matrix a a ℂ) k q.1)) *
          (if p.2=q.2 then 1 else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun p _ => cross p q)
    _ = _ := by
      simp only [Fintype.sum_prod_type]
      simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      simp only [Finset.sum_mul,Finset.mul_sum]
      congr 1
      funext q
      rw [Finset.sum_comm]

theorem traceLeft_local_unitary (U : Matrix.unitaryGroup a ℂ) (V : Matrix.unitaryGroup b ℂ)
    (ρ : Matrix (a × b) (a × b) ℂ) :
    QAlgorithms.traceLeft ((tensorUnitary U V : Matrix (a × b) (a × b) ℂ) * ρ *
      (tensorUnitary U V : Matrix (a × b) (a × b) ℂ)ᴴ) =
    (V : Matrix b b ℂ) * QAlgorithms.traceLeft ρ * (V : Matrix b b ℂ)ᴴ := by
  ext i k
  simp only [QAlgorithms.traceLeft,tensorUnitary,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.kronecker_apply,Matrix.kroneckerMap_apply,Matrix.of_apply,Finset.sum_mul]
  have cross (p q : a × b) :
      (∑ j : a, (V : Matrix b b ℂ) i p.2 * (U : Matrix a a ℂ) j p.1 * ρ p q *
        star ((V : Matrix b b ℂ) k q.2 * (U : Matrix a a ℂ) j q.1)) =
      ((V : Matrix b b ℂ) i p.2 * ρ p q * star ((V : Matrix b b ℂ) k q.2)) *
        (if p.1=q.1 then 1 else 0) := by
    calc
      _ = ((V : Matrix b b ℂ) i p.2 * ρ p q * star ((V : Matrix b b ℂ) k q.2)) *
          (∑ j : a, (U : Matrix a a ℂ) j p.1 * star ((U : Matrix a a ℂ) j q.1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [star_mul]
        ring
      _ = _ := by rw [unitary_cross_columns]

  calc
    _ = ∑ q : a × b, ∑ p : a × b,
        ((V : Matrix b b ℂ) i p.2 * ρ p q * star ((V : Matrix b b ℂ) k q.2)) *
          (if p.1=q.1 then 1 else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      convert cross p q using 1 <;> congr 1 <;> ext j <;> ring
    _ = _ := by
      simp only [Fintype.sum_prod_type,mul_ite,mul_one,mul_zero]
      simp_rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun x : a => fun y : b =>
        if x = _ then _ else (0:ℂ))]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_comm]

end Queelius.LocalBroadcasting

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset QAlgorithms NoLocalBroadcast.Broadcast
open scoped ComplexOrder Kronecker
variable {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]

theorem density_diagonal_probability {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : Matrix ι ι ℂ) (hρ : IsDensityMatrix ρ) :
    (∀ i, 0 ≤ (ρ i i).re) ∧ ∑ i, (ρ i i).re = 1 := by
  constructor
  · intro i
    exact (Complex.nonneg_iff.mp hρ.1.diag_nonneg).1
  · have h := congrArg Complex.re hρ.2
    simpa [Matrix.trace,Matrix.diag] using h

theorem density_unitary_conjugation {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (U : Matrix.unitaryGroup ι ℂ) (ρ : Matrix ι ι ℂ) (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix ((U : Matrix ι ι ℂ) * ρ * (U : Matrix ι ι ℂ)ᴴ) :=
  ⟨hρ.1.mul_mul_conjTranspose_same _, (trace_unitary_conjugation U ρ).trans hρ.2⟩

theorem entropy_subadditive_diagonal_marginals (ρ : Matrix (a × b) (a × b) ℂ)
    (hρ : IsDensityMatrix ρ) (p : a → ℝ) (q : b → ℝ)
    (ha : traceRight ρ = Matrix.diagonal (fun i => (p i : ℂ)))
    (hb : traceLeft ρ = Matrix.diagonal (fun j => (q j : ℂ))) :
    vnEntropy ρ ≤ vnEntropy (traceRight ρ) + vnEntropy (traceLeft ρ) := by
  obtain ⟨hp,hp1⟩ := density_diagonal_probability ρ hρ
  have hc := mutualInfo_diagonal_nonnegative (fun ij => (ρ ij ij).re) hp hp1
  rw [mutualInfo_diagonal] at hc
  have ha' (i : a) : ∑ j, (ρ (i,j) (i,j)).re = p i := by
    have h := congrArg Complex.re (congrFun (congrFun ha i) i)
    simpa [traceRight] using h
  have hb' (j : b) : ∑ i, (ρ (i,j) (i,j)).re = q j := by
    have h := congrArg Complex.re (congrFun (congrFun hb j) j)
    simpa [traceLeft] using h
  simp only [ha',hb'] at hc
  have hs := entropy_le_diagonal_shannon ρ hρ.1
  rw [ha,hb,entropy_diagonal,entropy_diagonal]
  linarith

theorem entropy_subadditive (ρ : Matrix (a × b) (a × b) ℂ) (hρ : IsDensityMatrix ρ) :
    vnEntropy ρ ≤ vnEntropy (traceRight ρ) + vnEntropy (traceLeft ρ) := by
  let hA := (traceRight_density ρ hρ).1.isHermitian
  let hB := (traceLeft_density ρ hρ).1.isHermitian
  let U := star hA.eigenvectorUnitary
  let V := star hB.eigenvectorUnitary
  let W := tensorUnitary U V
  let σ := (W : Matrix (a × b) (a × b) ℂ) * ρ * (W : Matrix (a × b) (a × b) ℂ)ᴴ
  have hσ : IsDensityMatrix σ := density_unitary_conjugation W ρ hρ
  have ha : traceRight σ = Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
    rw [show σ = _ from rfl,traceRight_local_unitary]
    simpa only [U,Unitary.conjStarAlgAut_apply,Function.comp_def,RCLike.ofReal_eq_complex_ofReal,
      Matrix.star_eq_conjTranspose] using hA.conjStarAlgAut_star_eigenvectorUnitary
  have hb : traceLeft σ = Matrix.diagonal (fun j => (hB.eigenvalues j : ℂ)) := by
    rw [show σ = _ from rfl,traceLeft_local_unitary]
    simpa only [V,Unitary.conjStarAlgAut_apply,Function.comp_def,RCLike.ofReal_eq_complex_ofReal,
      Matrix.star_eq_conjTranspose] using hB.conjStarAlgAut_star_eigenvectorUnitary
  have hs := entropy_subadditive_diagonal_marginals σ hσ hA.eigenvalues hB.eigenvalues ha hb
  rw [show σ = _ from rfl,entropy_unitary_conjugation W ρ hρ.1.isHermitian,
    traceRight_local_unitary,traceLeft_local_unitary,
    entropy_unitary_conjugation U _ hA,entropy_unitary_conjugation V _ hB] at hs
  exact hs

theorem mutualInfo_nonnegative (ρ : Matrix (a × b) (a × b) ℂ) (hρ : IsDensityMatrix ρ) :
    0 ≤ mutualInfo ρ := sub_nonneg.mpr (entropy_subadditive ρ hρ)

end Queelius.LocalBroadcasting

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset QAlgorithms
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem doubly_stochastic_entropy_equality {κ : Type} [Fintype κ]
    (W : ι → κ → ℝ) (p : κ → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hw : ∀ i j, 0 ≤ W i j) (hr : ∀ i, ∑ j, W i j = 1) (hc : ∀ j, ∑ i, W i j = 1)
    (he : ∑ j, Real.negMulLog (p j) = ∑ i, Real.negMulLog (∑ j, W i j * p j)) :
    ∀ i j, W i j ≠ 0 → p j = ∑ k, W i k * p k := by
  have hh (i : ι) : ∑ j, W i j * Real.negMulLog (p j) ≤
      Real.negMulLog (∑ j, W i j * p j) := by
    simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.le_map_sum
      (fun j _ => hw i j) (hr i) (fun j _ => hp j)
  have ht : (∑ i, ∑ j, W i j * Real.negMulLog (p j)) =
      ∑ i, Real.negMulLog (∑ j, W i j * p j) := by
    rw [Finset.sum_comm]
    simpa only [← Finset.sum_mul,hc,one_mul] using he
  have hi := (Finset.sum_eq_sum_iff_of_le (fun i _ => hh i)).mp ht
  intro i j hj
  have hji := (Real.strictConcaveOn_negMulLog.map_sum_eq_iff'
    (fun k _ => hw i k) (hr i) (fun k _ => hp k))
  simp only [smul_eq_mul] at hji
  exact (hji.mp (hi i (Finset.mem_univ i)).symm) j (Finset.mem_univ j) hj

theorem entropy_diagonal_equality (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef)
    (he : vnEntropy ρ = -(∑ i, (ρ i i).re * Real.logb 2 (ρ i i).re)) :
    ρ = Matrix.diagonal (fun i => ((ρ i i).re : ℂ)) := by
  let hH := hρ.isHermitian
  let U := hH.eigenvectorUnitary
  let p := hH.eigenvalues
  have hs (i : ι) : (ρ i i).re = ∑ j, Complex.normSq ((U : Matrix ι ι ℂ) i j) * p j :=
    hermitian_diagonal_spectral_mix ρ hH i
  rw [entropy_spectral ρ hH,shannon_negMulLog,shannon_negMulLog] at he
  have he' : ∑ j, Real.negMulLog (p j) =
      ∑ i, Real.negMulLog (∑ j, Complex.normSq ((U : Matrix ι ι ℂ) i j) * p j) := by
    rw [← div_left_inj' (ne_of_gt (Real.log_pos (by norm_num : (1:ℝ)<2)))]
    simpa only [← hs] using he
  have hi := doubly_stochastic_entropy_equality
    (fun i j => Complex.normSq ((U : Matrix ι ι ℂ) i j)) p hρ.eigenvalues_nonneg
    (fun i j => Complex.normSq_nonneg _) (unitary_row_normSq U) (unitary_col_normSq U) he'
  have hu (i j : ι) : (U : Matrix ι ι ℂ) i j * (p j : ℂ) =
      ((ρ i i).re : ℂ) * (U : Matrix ι ι ℂ) i j := by
    by_cases hz : (U : Matrix ι ι ℂ) i j = 0
    · simp [hz]
    · have hj := hi i j (fun h => hz (Complex.normSq_eq_zero.mp h))
      rw [← hs] at hj
      rw [hj,mul_comm]
  have hmat : (U : Matrix ι ι ℂ) * Matrix.diagonal (fun j => (p j : ℂ)) =
      Matrix.diagonal (fun i => ((ρ i i).re : ℂ)) * (U : Matrix ι ι ℂ) := by
    ext i j
    simpa only [Matrix.mul_diagonal,Matrix.diagonal_mul] using hu i j
  calc
    ρ = (U : Matrix ι ι ℂ) * Matrix.diagonal (fun j => (p j : ℂ)) * (U : Matrix ι ι ℂ)ᴴ := by
      simpa only [U,p,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
        Function.comp_def,RCLike.ofReal_eq_complex_ofReal] using hH.spectral_theorem
    _ = _ := by rw [hmat,Matrix.mul_assoc,← Matrix.star_eq_conjTranspose,
      U.property.2,Matrix.mul_one]

end Queelius.LocalBroadcasting

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset QAlgorithms NoLocalBroadcast.Broadcast
open scoped ComplexOrder Kronecker
variable {ι b : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype b] [DecidableEq b] [Nonempty b]

def cqBlock (X : ι → Matrix b b ℂ) : Matrix (ι × b) (ι × b) ℂ :=
  Matrix.reindex (Equiv.prodComm b ι) (Equiv.prodComm b ι) (Matrix.blockDiagonal X)

theorem cqBlock_apply (X : ι → Matrix b b ℂ) (p q : ι × b) :
    cqBlock X p q = if p.1=q.1 then X p.1 p.2 q.2 else 0 := rfl

theorem cqBlock_hermitian (X : ι → Matrix b b ℂ) (hX : ∀ i, (X i).IsHermitian) :
    (cqBlock X).IsHermitian := by
  change (cqBlock X)ᴴ = cqBlock X
  ext p q
  by_cases h : p.1=q.1
  · simp only [Matrix.conjTranspose_apply,cqBlock_apply,h,ite_true,eq_comm]
    exact (congrFun (congrFun (hX q.1).eq p.2) q.2).symm
  · simp [Matrix.conjTranspose_apply,cqBlock_apply,h,Ne.symm h]

theorem entropy_cqBlock (X : ι → Matrix b b ℂ) (hX : ∀ i, (X i).IsHermitian) :
    vnEntropy (cqBlock X) = ∑ i, vnEntropy (X i) := by
  unfold cqBlock
  rw [entropy_reindex _ _ (by
    change (Matrix.blockDiagonal X)ᴴ = Matrix.blockDiagonal X
    rw [Matrix.blockDiagonal_conjTranspose]
    congr 1
    funext i
    exact (hX i).eq), entropy_blockDiagonal X hX]

theorem traceRight_cqBlock (X : ι → Matrix b b ℂ) :
    traceRight (cqBlock X) = Matrix.diagonal (fun i => (X i).trace) := by
  ext i j
  by_cases h : i=j <;> simp [traceRight,cqBlock_apply,Matrix.diagonal_apply,h,Matrix.trace,Matrix.diag]

theorem traceLeft_cqBlock (X : ι → Matrix b b ℂ) : traceLeft (cqBlock X) = ∑ i, X i := by
  ext i j
  simp [traceLeft,cqBlock_apply,Matrix.sum_apply]

theorem entropy_cq_ensemble (p : ι → ℝ) (σ : ι → Matrix b b ℂ)
    (hσ : ∀ i, IsDensityMatrix (σ i)) :
    vnEntropy (cqBlock (fun i => (p i : ℂ) • σ i)) =
      -(∑ i, p i * Real.logb 2 (p i)) + ∑ i, p i * vnEntropy (σ i) := by
  rw [entropy_cqBlock _ (fun i => (hσ i).1.isHermitian.smul (show IsSelfAdjoint (p i : ℂ) from by change star (p i : ℂ) = (p i : ℂ); simp))]
  simp_rw [entropy_scaled_density _ (hσ _),Finset.sum_sub_distrib]
  ring

theorem mutualInfo_cq_ensemble (p : ι → ℝ) (σ : ι → Matrix b b ℂ)
    (hσ : ∀ i, IsDensityMatrix (σ i)) :
    mutualInfo (cqBlock (fun i => (p i : ℂ) • σ i)) =
      vnEntropy (∑ i, (p i : ℂ) • σ i) - ∑ i, p i * vnEntropy (σ i) := by
  rw [mutualInfo,traceRight_cqBlock,traceLeft_cqBlock,entropy_cq_ensemble p σ hσ]
  have ht : (fun i => ((p i : ℂ) • σ i).trace) = fun i => (p i : ℂ) := by
    funext i
    simp [Matrix.trace_smul,(hσ i).2]
  rw [ht,entropy_diagonal]
  ring

theorem cq_ensemble_information_bound (p : ι → ℝ) (σ : ι → Matrix b b ℂ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1) (hσ : ∀ i, IsDensityMatrix (σ i)) :
    mutualInfo (cqBlock (fun i => (p i : ℂ) • σ i)) ≤ Real.logb 2 (Fintype.card b) := by
  have hmix : IsDensityMatrix (∑ i, (p i : ℂ) • σ i) := by
    constructor
    · exact Matrix.posSemidef_sum _ (fun i _ => (hσ i).1.smul (by exact_mod_cast hp i))
    · simp only [Matrix.trace_sum,Matrix.trace_smul]
      simp_rw [fun i => (hσ i).2,smul_eq_mul,mul_one]
      exact_mod_cast hp1
  rw [mutualInfo_cq_ensemble p σ hσ]
  have hbound := entropy_le_log_dimension _ hmix
  have hnonneg : 0 ≤ ∑ i, p i * vnEntropy (σ i) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (entropy_nonnegative _ (hσ i)))
  linarith

end Queelius.LocalBroadcasting

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset QAlgorithms NoLocalBroadcast.Broadcast
open scoped ComplexOrder Kronecker
variable {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]

theorem factorized_of_zero_diagonal_marginals (ρ : Matrix (a × b) (a × b) ℂ)
    (hρ : IsDensityMatrix ρ) (p : a → ℝ) (q : b → ℝ)
    (ha : traceRight ρ = Matrix.diagonal (fun i => (p i : ℂ)))
    (hb : traceLeft ρ = Matrix.diagonal (fun j => (q j : ℂ))) (hz : mutualInfo ρ = 0) :
    ρ = traceRight ρ ⊗ₖ traceLeft ρ := by
  obtain ⟨hp,hp1⟩ := density_diagonal_probability ρ hρ
  have hc := mutualInfo_diagonal_nonnegative (fun ij => (ρ ij ij).re) hp hp1
  rw [mutualInfo_diagonal] at hc
  have ha' (i : a) : ∑ j, (ρ (i,j) (i,j)).re = p i := by
    have h := congrArg Complex.re (congrFun (congrFun ha i) i)
    simpa [traceRight] using h
  have hb' (j : b) : ∑ i, (ρ (i,j) (i,j)).re = q j := by
    have h := congrArg Complex.re (congrFun (congrFun hb j) j)
    simpa [traceLeft] using h
  simp only [ha',hb'] at hc
  have hs := entropy_le_diagonal_shannon ρ hρ.1
  have hz' := hz
  rw [mutualInfo,ha,hb,entropy_diagonal,entropy_diagonal] at hz'
  have he : vnEntropy ρ = -(∑ ij, (ρ ij ij).re * Real.logb 2 (ρ ij ij).re) := by linarith
  have hd := entropy_diagonal_equality ρ hρ.1 he
  have hciff := diagonal_factorized_iff_zero (fun ij => (ρ ij ij).re) hp hp1
  rw [← hd] at hciff
  exact hciff.mp hz

theorem mutualInfo_local_unitary (U : Matrix.unitaryGroup a ℂ) (V : Matrix.unitaryGroup b ℂ)
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : IsDensityMatrix ρ) :
    mutualInfo ((tensorUnitary U V : Matrix (a × b) (a × b) ℂ) * ρ *
      (tensorUnitary U V : Matrix (a × b) (a × b) ℂ)ᴴ) = mutualInfo ρ := by
  rw [mutualInfo,mutualInfo,traceRight_local_unitary,traceLeft_local_unitary,
    entropy_unitary_conjugation U _ (traceRight_density ρ hρ).1.isHermitian,
    entropy_unitary_conjugation V _ (traceLeft_density ρ hρ).1.isHermitian,
    entropy_unitary_conjugation _ ρ hρ.1.isHermitian]

theorem factorized_of_mutualInfo_zero (ρ : Matrix (a × b) (a × b) ℂ)
    (hρ : IsDensityMatrix ρ) (hz : mutualInfo ρ = 0) :
    ρ = traceRight ρ ⊗ₖ traceLeft ρ := by
  let hA := (traceRight_density ρ hρ).1.isHermitian
  let hB := (traceLeft_density ρ hρ).1.isHermitian
  let U := star hA.eigenvectorUnitary
  let V := star hB.eigenvectorUnitary
  let W := tensorUnitary U V
  let σ := (W : Matrix (a × b) (a × b) ℂ) * ρ * (W : Matrix (a × b) (a × b) ℂ)ᴴ
  have hσ : IsDensityMatrix σ := density_unitary_conjugation W ρ hρ
  have ha : traceRight σ = Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
    rw [show σ = _ from rfl,traceRight_local_unitary]
    simpa only [U,Unitary.conjStarAlgAut_apply,Function.comp_def,RCLike.ofReal_eq_complex_ofReal,
      Matrix.star_eq_conjTranspose] using hA.conjStarAlgAut_star_eigenvectorUnitary
  have hb : traceLeft σ = Matrix.diagonal (fun j => (hB.eigenvalues j : ℂ)) := by
    rw [show σ = _ from rfl,traceLeft_local_unitary]
    simpa only [V,Unitary.conjStarAlgAut_apply,Function.comp_def,RCLike.ofReal_eq_complex_ofReal,
      Matrix.star_eq_conjTranspose] using hB.conjStarAlgAut_star_eigenvectorUnitary
  have hzσ : mutualInfo σ = 0 := (mutualInfo_local_unitary U V ρ hρ).trans hz
  have hf := factorized_of_zero_diagonal_marginals σ hσ _ _ ha hb hzσ
  apply (Unitary.conjStarAlgAut ℂ (Matrix (a × b) (a × b) ℂ) W).injective
  change σ = (W : Matrix (a × b) (a × b) ℂ) * (traceRight ρ ⊗ₖ traceLeft ρ) *
    (W : Matrix (a × b) (a × b) ℂ)ᴴ
  rw [← tensor_unitary_conjugation U V]
  exact hf.trans (by rw [show σ = _ from rfl,traceRight_local_unitary,traceLeft_local_unitary])

theorem mutualInfo_zero_iff_factorized (ρ : Matrix (a × b) (a × b) ℂ)
    (hρ : IsDensityMatrix ρ) :
    mutualInfo ρ = 0 ↔ ρ = traceRight ρ ⊗ₖ traceLeft ρ :=
  ⟨factorized_of_mutualInfo_zero ρ hρ,mutualInfo_zero_of_factorized ρ hρ⟩

end Queelius.LocalBroadcasting

end

section
noncomputable section
namespace Queelius.LocalBroadcasting.Controls
open Matrix Finset QAlgorithms NoLocalBroadcast.Broadcast
open scoped ComplexOrder Kronecker

theorem coherent_diagonal_entropy_strict :
    vnEntropy coherentState <
      -(∑ i : Fin 2, (coherentState i i).re * Real.logb 2 (coherentState i i).re) := by
  apply lt_of_le_of_ne (entropy_le_diagonal_shannon coherentState coherent_density.1)
  intro he
  have hd := entropy_diagonal_equality coherentState coherent_density.1 he
  have h01 := congrFun (congrFun hd 0) 1
  norm_num [coherentState,Matrix.diagonal_apply] at h01

theorem coherent_product_subadditivity_equality :
    vnEntropy (coherentState ⊗ₖ coherentState) =
      vnEntropy (traceRight (coherentState ⊗ₖ coherentState)) +
      vnEntropy (traceLeft (coherentState ⊗ₖ coherentState)) := by
  rw [traceRight_tensor,traceLeft_tensor,coherent_density.2,one_smul,
    entropy_tensor_density _ _ coherent_density coherent_density]

theorem correlated_subadditivity_strict :
    vnEntropy (Matrix.diagonal (fun ij => (correlated ij : ℂ))) <
      vnEntropy (traceRight (Matrix.diagonal (fun ij => (correlated ij : ℂ)))) +
      vnEntropy (traceLeft (Matrix.diagonal (fun ij => (correlated ij : ℂ)))) := by
  have h := correlated_one_bit
  unfold mutualInfo at h
  linarith

end Queelius.LocalBroadcasting.Controls

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset QAlgorithms NoLocalBroadcast.Broadcast
open scoped ComplexOrder Kronecker
variable {ι b : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype b] [DecidableEq b] [Nonempty b]

theorem cqBlock_eq_sum (X : ι → Matrix b b ℂ) :
    cqBlock X = ∑ i, Matrix.diagonal (fun j => if j=i then (1:ℂ) else 0) ⊗ₖ X i := by
  ext p q
  by_cases h : p.1=q.1
  · simp [cqBlock_apply,Matrix.sum_apply,Matrix.kroneckerMap_apply,Matrix.diagonal_apply,h]
  · simp [cqBlock_apply,Matrix.sum_apply,Matrix.kroneckerMap_apply,Matrix.diagonal_apply,h]

theorem cqBlock_posSemidef (X : ι → Matrix b b ℂ) (hX : ∀ i, (X i).PosSemidef) :
    (cqBlock X).PosSemidef := by
  rw [cqBlock_eq_sum]
  exact Matrix.posSemidef_sum _ (fun i _ =>
    (Matrix.PosSemidef.diagonal (fun j => by split_ifs <;> norm_num)).kronecker (hX i))

theorem cq_ensemble_density (p : ι → ℝ) (σ : ι → Matrix b b ℂ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1) (hσ : ∀ i, IsDensityMatrix (σ i)) :
    IsDensityMatrix (cqBlock (fun i => (p i : ℂ) • σ i)) := by
  constructor
  · exact cqBlock_posSemidef _ (fun i => (hσ i).1.smul (by exact_mod_cast hp i))
  · unfold cqBlock
    rw [trace_reindex,trace_blockDiagonal]
    simp_rw [Matrix.trace_smul,fun i => (hσ i).2,smul_eq_mul,mul_one]
    exact_mod_cast hp1

theorem entropy_concave_ensemble (p : ι → ℝ) (σ : ι → Matrix b b ℂ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1) (hσ : ∀ i, IsDensityMatrix (σ i)) :
    ∑ i, p i * vnEntropy (σ i) ≤ vnEntropy (∑ i, (p i : ℂ) • σ i) := by
  have h := mutualInfo_nonnegative _ (cq_ensemble_density p σ hp hp1 hσ)
  rw [mutualInfo_cq_ensemble p σ hσ] at h
  linarith

end Queelius.LocalBroadcasting

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset QAlgorithms NoLocalBroadcast.Broadcast
open scoped ComplexOrder Kronecker MatrixOrder
variable {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]

theorem traceLeft_left_cyclic (A : Matrix a a ℂ) (X : Matrix (a×b) (a×b) ℂ) :
    traceLeft ((A ⊗ₖ (1 : Matrix b b ℂ)) * X) =
      traceLeft (X * (A ⊗ₖ (1 : Matrix b b ℂ))) := by
  ext i j
  simp only [traceLeft,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.kroneckerMap_apply,
    Matrix.one_apply,Matrix.of_apply,ite_mul,mul_ite,one_mul,mul_one,zero_mul,mul_zero]
  simp only [Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem traceLeft_posSemidef (X : Matrix (a×b) (a×b) ℂ) (hX : X.PosSemidef) :
    (traceLeft X).PosSemidef := by
  rw [← Queelius.LocalBroadcast.discardLeft_action]
  exact Matrix.posSemidef_sum _ (fun i _ => hX.mul_mul_conjTranspose_same _)

theorem conditional_block_posSemidef (A : Matrix a a ℂ) (X : Matrix (a×b) (a×b) ℂ)
    (hA : A.PosSemidef) (hX : X.PosSemidef) :
    (traceLeft ((A ⊗ₖ (1 : Matrix b b ℂ)) * X)).PosSemidef := by
  obtain ⟨C,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have h := traceLeft_posSemidef
    ((C ⊗ₖ (1 : Matrix b b ℂ)) * X * (C ⊗ₖ (1 : Matrix b b ℂ))ᴴ)
    (hX.mul_mul_conjTranspose_same _)
  rw [Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one] at h
  rw [← traceLeft_left_cyclic Cᴴ ((C ⊗ₖ (1 : Matrix b b ℂ))*X)] at h
  simpa only [← Matrix.mul_assoc,← Matrix.mul_kronecker_mul,one_mul,
    Matrix.star_eq_conjTranspose] using h

theorem cqState_as_blocks {n : ℕ} (ρ : Matrix (a×b) (a×b) ℂ)
    (M : Fin n → Matrix a a ℂ) :
    cqState ρ M = cqBlock (fun i => traceLeft ((M i ⊗ₖ (1 : Matrix b b ℂ))*ρ)) := by
  rfl

theorem conditional_blocks_sum {n : ℕ} (ρ : Matrix (a×b) (a×b) ℂ)
    (M : Fin n → Matrix a a ℂ) (hM : IsPOVM M) :
    (∑ i, traceLeft ((M i ⊗ₖ (1 : Matrix b b ℂ))*ρ)) = traceLeft ρ := by
  have hm : (∑ i, M i ⊗ₖ (1 : Matrix b b ℂ)) = 1 := by
    have hs : (∑ i, M i ⊗ₖ (1 : Matrix b b ℂ)) = (∑ i, M i) ⊗ₖ (1 : Matrix b b ℂ) := by
      ext p q
      simp [Matrix.sum_apply,Matrix.kroneckerMap_apply,Finset.sum_mul]
    rw [hs,hM.2,Matrix.one_kronecker_one]
  have ht : (∑ i, traceLeft ((M i ⊗ₖ (1 : Matrix b b ℂ))*ρ)) =
      traceLeft ((∑ i, M i ⊗ₖ (1 : Matrix b b ℂ))*ρ) := by
    ext x y
    simp only [traceLeft,Matrix.sum_apply,Matrix.sum_mul]
    exact Finset.sum_comm
  rw [ht,hm,one_mul]

end Queelius.LocalBroadcasting

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset QAlgorithms NoLocalBroadcast.Broadcast
open scoped ComplexOrder Kronecker
variable {ι b : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype b] [DecidableEq b] [Nonempty b]

theorem positive_blocks_normalize (X : ι → Matrix b b ℂ) (hX : ∀ i, (X i).PosSemidef)
    (ht : (∑ i, X i).trace = 1) (τ : Matrix b b ℂ) (hτ : IsDensityMatrix τ) :
    ∃ (p : ι → ℝ) (σ : ι → Matrix b b ℂ),
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i=1) ∧ (∀ i, IsDensityMatrix (σ i)) ∧
      (∀ i, X i = (p i : ℂ) • σ i) := by
  let p : ι → ℝ := fun i => (X i).trace.re
  have hp (i : ι) : 0 ≤ p i := (Complex.nonneg_iff.mp (hX i).trace_nonneg).1
  have hreal (i : ι) : (p i : ℂ) = (X i).trace := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp (hX i).trace_nonneg).2
  have hp1 : ∑ i, p i=1 := by
    have h := congrArg Complex.re ht
    simpa [p,Matrix.trace_sum] using h
  let σ : ι → Matrix b b ℂ := fun i => if p i=0 then τ else ((p i)⁻¹ : ℂ) • X i
  refine ⟨p,σ,hp,hp1,?_,?_⟩
  · intro i
    by_cases hz : p i=0
    · simpa [σ,hz] using hτ
    · have hc : (p i : ℂ) ≠ 0 := by exact_mod_cast hz
      constructor
      · simp only [σ,hz,ite_false]
        exact (hX i).smul (by exact_mod_cast inv_nonneg.mpr (hp i))
      · simp only [σ,hz,ite_false,Matrix.trace_smul,smul_eq_mul]
        rw [← hreal]
        exact inv_mul_cancel₀ hc
  · intro i
    by_cases hz : p i=0
    · have hx : X i=0 := (hX i).trace_eq_zero_iff.mp (by rw [← hreal,hz]; rfl)
      simp [σ,hz,hx]
    · have hc : (p i : ℂ) ≠ 0 := by exact_mod_cast hz
      simp [σ,hz,smul_smul,hc]

theorem positive_blocks_information_bound (X : ι → Matrix b b ℂ)
    (hX : ∀ i, (X i).PosSemidef) (ht : (∑ i, X i).trace = 1)
    (τ : Matrix b b ℂ) (hτ : IsDensityMatrix τ) :
    0 ≤ mutualInfo (cqBlock X) ∧ mutualInfo (cqBlock X) ≤ Real.logb 2 (Fintype.card b) := by
  obtain ⟨p,σ,hp,hp1,hσ,he⟩ := positive_blocks_normalize X hX ht τ hτ
  have hx : X = fun i => (p i : ℂ) • σ i := funext he
  rw [hx]
  exact ⟨mutualInfo_nonnegative _ (cq_ensemble_density p σ hp hp1 hσ),
    cq_ensemble_information_bound p σ hp hp1 hσ⟩

end Queelius.LocalBroadcasting

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset QAlgorithms NoLocalBroadcast.Broadcast
open scoped ComplexOrder Kronecker
variable {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]

theorem povm_outcome_positive {n : ℕ} (M : Fin n → Matrix a a ℂ) (hM : IsPOVM M) : 0<n := by
  by_contra hn
  have hz : n=0 := by omega
  subst n
  have h := congrFun (congrFun hM.2 (Classical.arbitrary a)) (Classical.arbitrary a)
  simp at h

theorem cqState_information_bound {n : ℕ} (ρ : Matrix (a×b) (a×b) ℂ)
    (hρ : IsDensityMatrix ρ) (M : Fin n → Matrix a a ℂ) (hM : IsPOVM M) :
    0 ≤ mutualInfo (cqState ρ M) ∧
      mutualInfo (cqState ρ M) ≤ Real.logb 2 (Fintype.card b) := by
  have hn : 0<n := povm_outcome_positive M hM
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [cqState_as_blocks]
  exact positive_blocks_information_bound _
    (fun i => conditional_block_posSemidef _ ρ (hM.1 i) hρ.1)
    (by rw [conditional_blocks_sum ρ M hM]; exact (traceLeft_density ρ hρ).2)
    (traceLeft ρ) (traceLeft_density ρ hρ)

theorem icq_boundedAbove (ρ : Matrix (a×b) (a×b) ℂ) (hρ : IsDensityMatrix ρ) :
    BddAbove {x | ∃ (n : ℕ) (M : Fin n → Matrix a a ℂ), IsPOVM M ∧
      x = mutualInfo (cqState ρ M)} := by
  refine ⟨Real.logb 2 (Fintype.card b),?_⟩
  rintro x ⟨n,M,hM,rfl⟩
  exact (cqState_information_bound ρ hρ M hM).2

theorem icq_information_bound (ρ : Matrix (a×b) (a×b) ℂ) (hρ : IsDensityMatrix ρ) :
    0 ≤ I_CQ ρ ∧ I_CQ ρ ≤ Real.logb 2 (Fintype.card b) := by
  let S : Set ℝ := {x | ∃ (n : ℕ) (M : Fin n → Matrix a a ℂ), IsPOVM M ∧
    x = mutualInfo (cqState ρ M)}
  have hM : IsPOVM (fun _ : Fin 1 => (1 : Matrix a a ℂ)) := ⟨fun _ => .one, by simp⟩
  have hx : mutualInfo (cqState ρ (fun _ : Fin 1 => (1 : Matrix a a ℂ))) ∈ S :=
    ⟨1,_,hM,rfl⟩
  change 0 ≤ sSup S ∧ sSup S ≤ _
  constructor
  · exact (cqState_information_bound ρ hρ _ hM).1.trans (le_csSup (icq_boundedAbove ρ hρ) hx)
  · apply csSup_le ⟨_,hx⟩
    rintro x ⟨n,M,h,rfl⟩
    exact (cqState_information_bound ρ hρ M h).2

end Queelius.LocalBroadcasting

end

section
noncomputable section
namespace Queelius.LocalBroadcasting.Controls
open Matrix Finset QAlgorithms NoLocalBroadcast.Broadcast
open scoped ComplexOrder Kronecker

def basisZero : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (fun i => if i=0 then 1 else 0)

theorem basisZero_density : IsDensityMatrix basisZero := by
  constructor
  · exact Matrix.PosSemidef.diagonal (fun i => by split_ifs <;> norm_num)
  · norm_num [basisZero,Matrix.trace,Matrix.diag,Fin.sum_univ_two]

theorem basisZero_entropy : vnEntropy basisZero=0 := by
  have he : basisZero = Matrix.diagonal (fun i : Fin 2 => ((if i=0 then 1 else 0 : ℝ):ℂ)) := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [basisZero,Matrix.diagonal_apply]
  rw [he,entropy_diagonal]
  norm_num [Fin.sum_univ_two]

def noncommutingEnsemble (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  if i=0 then basisZero else coherentState

theorem noncommutingEnsemble_density (i : Fin 2) : IsDensityMatrix (noncommutingEnsemble i) := by
  unfold noncommutingEnsemble
  split_ifs
  · exact basisZero_density
  · exact coherent_density

theorem ensemble_not_commuting : basisZero * coherentState ≠ coherentState * basisZero := by
  intro h
  have he := congrFun (congrFun h 0) 1
  norm_num [basisZero,coherentState,Matrix.mul_apply,Fin.sum_univ_two,Matrix.diagonal_apply] at he

theorem zero_weight_ignored :
    mutualInfo (cqBlock (fun i : Fin 2 => ((if i=0 then 1 else 0 : ℝ):ℂ) •
      noncommutingEnsemble i)) = 0 := by
  rw [mutualInfo_cq_ensemble _ _ noncommutingEnsemble_density]
  norm_num [Fin.sum_univ_two,noncommutingEnsemble,basisZero_entropy]

theorem noncommuting_holevo_identity :
    mutualInfo (cqBlock (fun i : Fin 2 => ((1/2:ℝ):ℂ) • noncommutingEnsemble i)) =
      vnEntropy (((1/2:ℂ) • basisZero) + ((1/2:ℂ) • coherentState)) := by
  rw [mutualInfo_cq_ensemble _ _ noncommutingEnsemble_density]
  norm_num [Fin.sum_univ_two,noncommutingEnsemble,basisZero_entropy,coherent_zero_entropy]

theorem noncommuting_information_positive :
    0 < mutualInfo (cqBlock (fun i : Fin 2 => ((1/2:ℝ):ℂ) • noncommutingEnsemble i)) := by
  let X := cqBlock (fun i : Fin 2 => ((1/2:ℝ):ℂ) • noncommutingEnsemble i)
  have hd : IsDensityMatrix X := cq_ensemble_density _ _ (by intro; norm_num)
    (by norm_num [Fin.sum_univ_two]) noncommutingEnsemble_density
  have hn := mutualInfo_nonnegative X hd
  have hne : mutualInfo X ≠ 0 := by
    intro hz
    have hf := factorized_of_mutualInfo_zero X hd hz
    have he := congrFun (congrFun hf (0,0)) (0,0)
    change X (0,0) (0,0) = (traceRight X ⊗ₖ traceLeft X) (0,0) (0,0) at he
    norm_num [X,cqBlock_apply,traceRight_cqBlock,traceLeft_cqBlock,Matrix.kroneckerMap_apply,
      Matrix.trace,Matrix.diag,Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_two,
      noncommutingEnsemble,basisZero,coherentState,Matrix.diagonal_apply] at he
  exact lt_of_le_of_ne hn (Ne.symm hne)

end Queelius.LocalBroadcasting.Controls

end

section
noncomputable section
namespace Queelius.LocalBroadcasting
open Matrix Finset QAlgorithms NoLocalBroadcast.Broadcast
open scoped ComplexOrder Kronecker
variable {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]

theorem cqState_product_information_zero {n : ℕ} (A : Matrix a a ℂ) (B : Matrix b b ℂ)
    (hA : IsDensityMatrix A) (hB : IsDensityMatrix B)
    (M : Fin n → Matrix a a ℂ) (hM : IsPOVM M) :
    mutualInfo (cqState (A ⊗ₖ B) M) = 0 := by
  letI : NeZero n := ⟨Nat.ne_of_gt (povm_outcome_positive M hM)⟩
  have hd : IsDensityMatrix (Matrix.diagonal (fun i => (M i*A).trace)) := by
    constructor
    · exact Matrix.PosSemidef.diagonal (fun i => trace_mul_psd _ _ (hM.1 i) hA.1)
    · rw [Matrix.trace_diagonal,← Matrix.trace_sum,← Matrix.sum_mul,hM.2,one_mul,hA.2]
  have he : cqState (A ⊗ₖ B) M = Matrix.diagonal (fun i => (M i*A).trace) ⊗ₖ B := by
    ext p q
    simp only [cqState,← Matrix.mul_kronecker_mul,one_mul,traceLeft_tensor,Matrix.of_apply,
      Matrix.smul_apply,smul_eq_mul,Matrix.kroneckerMap_apply,Matrix.diagonal_apply]
    split_ifs <;> simp_all
  rw [he]
  exact mutualInfo_product_zero _ B hd hB

theorem icq_product_zero (A : Matrix a a ℂ) (B : Matrix b b ℂ)
    (hA : IsDensityMatrix A) (hB : IsDensityMatrix B) : I_CQ (A ⊗ₖ B) = 0 := by
  apply le_antisymm
  · unfold I_CQ
    apply csSup_le
    · exact ⟨_,1,(fun _ : Fin 1 => (1 : Matrix a a ℂ)),⟨fun _ => .one,by simp⟩,rfl⟩
    · rintro x ⟨n,M,hM,rfl⟩
      exact le_of_eq (cqState_product_information_zero A B hA hB M hM)
  · exact (icq_information_bound _ (tensor_density A B hA hB)).1

theorem icq_zero_of_factorized (ρ : Matrix (a×b) (a×b) ℂ) (hρ : IsDensityMatrix ρ)
    (hf : ρ = traceRight ρ ⊗ₖ traceLeft ρ) : I_CQ ρ = 0 := by
  have h := icq_product_zero _ _ (traceRight_density ρ hρ) (traceLeft_density ρ hρ)
  rwa [← hf] at h

end Queelius.LocalBroadcasting

end
