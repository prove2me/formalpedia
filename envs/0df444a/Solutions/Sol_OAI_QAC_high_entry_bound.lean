-- Prove2me | solution 1 for OAI.QAC.high_entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:30:31.546029+00:00
-- url     : https://prove2.me/submissions/cec04d9d-f6e4-4b50-8a01-698e555d6413

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Computational.lean:L104-L121
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.high_entry_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_DepthZero
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Localization
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Toffoli
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Physical
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Computational
import Theorems.Thm_OAI_QAC_Count_high_mul_pattern
import Theorems.Thm_OAI_QAC_Count_pattern_mul
import Theorems.Thm_OAI_QAC_rankOne_projection

-- ---- from OAI.InformationTheory.QuantumCircuit.ProductProjection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma tensorMatrix_mul {N : ℕ} (a b : Fin N → QubitOperator) :
    tensorMatrix a * tensorMatrix b = tensorMatrix (fun i => a i * b i) := by
  classical
  ext x y
  simp only [Matrix.mul_apply, tensorMatrix]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i z => a i (x i) z * b i z (y i))).symm

lemma tensorMatrix_projection {N : ℕ} (a : Fin N → QubitOperator)
    (ha : ∀ i, IsStarProjection (a i)) : IsStarProjection (tensorMatrix a) := by
  rw [isStarProjection_iff']
  constructor
  · rw [tensorMatrix_mul]
    congr 1
    funext i
    exact (ha i).isIdempotentElem.eq
  · rw [tensorMatrix_star]
    congr 1
    funext i
    exact (ha i).isSelfAdjoint.star_eq

lemma Count.zero_projection {N : ℕ} (M : Count N) : IsStarProjection M.zero := by
  apply tensorMatrix_projection
  intro i
  split_ifs with hi
  · exact rankOne_projection (M.normalized i hi)
  · exact IsStarProjection.one _

lemma Count.pattern_projection {N : ℕ} (M : Count N) (F : Finset (Fin N)) :
    IsStarProjection (M.pattern F) := by
  apply tensorMatrix_projection
  intro i
  split_ifs with hi hF
  · exact (rankOne_projection (M.normalized i hi)).one_sub
  · exact rankOne_projection (M.normalized i hi)
  · exact IsStarProjection.one _

lemma projection_sum {A ι : Type*} [Ring A] [StarRing A] (s : Finset ι) (p : ι → A)
    (hp : ∀ i ∈ s, IsStarProjection (p i))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → p i * p j = 0) :
    IsStarProjection (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    apply (hp i (Finset.mem_insert_self _ _)).add
    · apply ih
      · exact fun j hj => hp j (Finset.mem_insert_of_mem hj)
      · exact fun j hj k hk h => horth j (Finset.mem_insert_of_mem hj)
          k (Finset.mem_insert_of_mem hk) h
    · rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      apply horth i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
      intro h
      exact hi (h ▸ hj)

lemma Count.high_eq_sum_filter {N : ℕ} (M : Count N) (r : ℝ) :
    M.high r = ∑ F ∈ M.support.powerset.filter (fun F => r ≤ (F.card : ℝ)), M.pattern F := by
  classical
  simp only [Count.high, Finset.sum_filter]

lemma Count.high_projection {N : ℕ} (M : Count N) (r : ℝ) : IsStarProjection (M.high r) := by
  classical
  rw [M.high_eq_sum_filter]
  apply projection_sum
  · exact fun F _ => M.pattern_projection F
  · intro F hF G hG hFG
    rw [M.pattern_mul (Finset.mem_powerset.mp (Finset.mem_filter.mp hF).1)
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hG).1), ite_eq_right hFG]

section SpectralAlgebra

variable {A ι : Type*} [CStarAlgebra A]

variable [PartialOrder A] [StarOrderedRing A]

end SpectralAlgebra

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Toffoli ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma rankOne_basis (b : Bit) (x y : Bit) :
    rankOne (basisVector b) x y = if x=b ∧ y=b then 1 else 0 := by
  classical
  simp only [rankOne,basisVector]
  split_ifs <;> simp_all

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Computational ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma matrix_entry_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (i j : ι) :
    ‖A i j‖ ≤ ‖A‖ := by
  classical
  let v : EuclideanSpace ℂ ι := WithLp.toLp 2 (Pi.single j 1)
  have h := A.l2_opNorm_mulVec v
  have he := PiLp.norm_apply_le ((EuclideanSpace.equiv ι ℂ).symm (A *ᵥ v)) i
  have hv : ‖v‖=1 := by simp [v]
  rw [hv,mul_one] at h
  apply le_trans _ h
  simpa [v,Matrix.mulVec,dotProduct,Pi.single_apply] using he

lemma tensorMatrix_diagonal {N : ℕ} (f : Fin N → Bit → ℂ) :
    tensorMatrix (fun i => Matrix.diagonal (f i)) = Matrix.diagonal (fun x => ∏ i, f i (x i)) := by
  classical
  ext x y
  simp only [tensorMatrix,Matrix.diagonal_apply]
  by_cases hxy : x=y
  · subst y; simp
  · simp only [ite_eq_right hxy]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hxy
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma rankOne_basis_diagonal (b : Bit) :
    rankOne (basisVector b) = Matrix.diagonal (fun x => if x=b then 1 else 0) := by
  ext x y
  rw [rankOne_basis,Matrix.diagonal_apply]
  split_ifs <;> simp_all

lemma one_sub_rankOne_basis (b : Bit) :
    1-rankOne (basisVector b) = rankOne (basisVector (1-b)) := by
  ext x y
  simp only [Matrix.sub_apply,Matrix.one_apply,rankOne_basis]
  fin_cases b <;> fin_cases x <;> fin_cases y <;> norm_num

lemma computationalCount_zero {N : ℕ} (z : Word N) : (computationalCount z).zero=basisProjection z := by
  classical
  simp only [Count.zero,computationalCount,Finset.mem_univ,ite_true,rankOne_basis_diagonal]
  rw [tensorMatrix_diagonal]
  congr 1
  funext x
  rw [Fintype.prod_boole]
  simp only [funext_iff]
  split_ifs <;> rfl

lemma computationalCount_pattern {N : ℕ} (z : Word N) (F : Finset (Fin N)) :
    (computationalCount z).pattern F = basisProjection (flipWord F z) := by
  classical
  rw [← computationalCount_zero]
  simp only [Count.pattern,Count.zero,computationalCount,Finset.mem_univ,ite_true]
  congr 1
  funext i
  by_cases hi : i∈F
  · simp only [ite_eq_left hi,flipWord]
    exact one_sub_rankOne_basis (z i)
  · simp [hi,flipWord]

lemma basisProjection_mul_entry {N : ℕ} (z : Word N) (A : Operator N) (y : Word N) :
    (basisProjection z*A) z y = A z y := by
  classical
  simp [basisProjection,Matrix.diagonal_mul]

lemma mul_basisProjection_entry {N : ℕ} (z : Word N) (A : Operator N) (y : Word N) :
    (A*basisProjection z) y z = A y z := by
  classical
  simp [basisProjection,Matrix.mul_diagonal]

lemma high_entry_bound {N : ℕ} (B : Operator N) (z : Word N) (F : Finset (Fin N))
    {r : ℝ} (hr : r ≤ (F.card:ℝ)) :
    ‖B (flipWord F z) z‖ ≤ ‖(computationalCount z).high r*B*(computationalCount z).zero‖ := by
  let y := flipWord F z
  have habs := (computationalCount z).high_mul_pattern F (Finset.subset_univ F) r
  rw [ite_eq_left hr,computationalCount_pattern] at habs
  have hleft : basisProjection y*(computationalCount z).high r = basisProjection y := by
    have h := congrArg star habs
    rw [star_mul, ((computationalCount z).high_projection r).isSelfAdjoint.star_eq] at h
    change star (basisProjection y)*(computationalCount z).high r = star (basisProjection y) at h
    simpa only [← computationalCount_zero,
      (computationalCount y).zero_projection.isSelfAdjoint.star_eq,
      ((computationalCount z).high_projection r).isSelfAdjoint.star_eq] using h
  have heq : ((computationalCount z).high r*B*basisProjection z) y z = B y z := by
    rw [← basisProjection_mul_entry y ((computationalCount z).high r*B*basisProjection z) z]
    rw [← mul_assoc,← mul_assoc,hleft,mul_basisProjection_entry,basisProjection_mul_entry]
  rw [computationalCount_zero]
  exact heq ▸ matrix_entry_norm_le ((computationalCount z).high r*B*basisProjection z) y z

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

theorem solution {N : ℕ} (B : Operator N) (z : Word N) (F : Finset (Fin N))
    {r : ℝ} (hr : r ≤ (F.card:ℝ)) :
    ‖B (flipWord F z) z‖ ≤ ‖(computationalCount z).high r*B*(computationalCount z).zero‖ := by
  first
    | exact OAI.QAC.high_entry_bound B z F hr
    | exact OAI.QAC.high_entry_bound
    | (apply OAI.QAC.high_entry_bound <;> assumption)
    | (intros; apply OAI.QAC.high_entry_bound <;> assumption)
