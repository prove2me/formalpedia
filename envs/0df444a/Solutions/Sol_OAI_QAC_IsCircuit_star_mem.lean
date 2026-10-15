-- Prove2me | solution 1 for OAI.QAC.IsCircuit.star_mem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:59:14.307928+00:00
-- url     : https://prove2.me/submissions/d4f20905-0c01-4d8b-9f5c-abacc9385410

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Circuit.lean:L164-L177
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.IsCircuit.star_mem. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Theorems.Thm_OAI_QAC_rankOne_projection

-- ---- from OAI.InformationTheory.QuantumCircuit.ProductProjection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

section SpectralAlgebra

variable {A ι : Type*} [CStarAlgebra A]

variable [PartialOrder A] [StarOrderedRing A]

end SpectralAlgebra

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Circuit ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma localMatrix_mul {N : ℕ} (L K : LocalLayer N) :
    localMatrix L * localMatrix K = localMatrix (fun i => L i * K i) := by
  exact tensorMatrix_mul _ _

lemma localMatrix_star {N : ℕ} (L : LocalLayer N) :
    star (localMatrix L) = localMatrix (fun i => star (L i)) := by
  exact tensorMatrix_star _

lemma IsCircuit.mul_local {N d : ℕ} {U : Operator N} (hU : IsCircuit d U)
    (L : LocalLayer N) : IsCircuit d (U * localMatrix L) := by
  cases d with
  | zero =>
    obtain ⟨K, rfl⟩ := hU
    exact ⟨fun i => K i * L i, localMatrix_mul K L⟩
  | succ d =>
    obtain ⟨V, R, K, hV, rfl⟩ := hU
    exact ⟨V, R, (fun i => K i * L i), hV, by rw [mul_assoc, localMatrix_mul]⟩

lemma IsCircuit.mul {N d e : ℕ} {U V : Operator N}
    (hU : IsCircuit d U) (hV : IsCircuit e V) : IsCircuit (d + e) (U * V) := by
  induction e generalizing V with
  | zero =>
    obtain ⟨L, rfl⟩ := hV
    exact hU.mul_local L
  | succ e ih =>
    obtain ⟨W, R, L, hW, rfl⟩ := hV
    exact ⟨U * W, R, L, ih hW, by simp only [mul_assoc]⟩

lemma star_list_prod_reverse {A B : Type*} [Ring B] [StarRing B]
    (f : A → B) (hf : ∀ a, star (f a) = f a) (l : List A) :
    star (l.map f).prod = (l.reverse.map f).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.reverse_cons, List.map_append, List.prod_append, star_mul, hf, ih]

lemma reflectionMatrix_star {N : ℕ} (R : ReflectionLayer N) :
    star (reflectionMatrix R) = reflectionMatrix R.reverse := by
  apply star_list_prod_reverse
  intro M
  simp only [star_sub, star_one, star_smul, star_ofNat, M.zero_projection.isSelfAdjoint.star_eq]

lemma IsCircuit.star_mem {N d : ℕ} {U : Operator N} (hU : IsCircuit d U) :
    IsCircuit d (star U) := by
  induction d generalizing U with
  | zero =>
    obtain ⟨L, rfl⟩ := hU
    exact ⟨fun i => star (L i), localMatrix_star L⟩
  | succ d ih =>
    obtain ⟨V, R, L, hV, rfl⟩ := hU
    have hL : IsCircuit 0 (star (localMatrix L)) := ⟨_, localMatrix_star L⟩
    have hLR : IsCircuit 1 (star (localMatrix L) * reflectionMatrix R.reverse) := by
      refine ⟨_, R.reverse, (fun _ => 1), hL, ?_⟩
      simp [localMatrix]
    have h := hLR.mul (ih hV)
    simpa only [star_mul, reflectionMatrix_star, Nat.add_comm 1, mul_assoc] using h

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

theorem solution {N d : ℕ} {U : Operator N} (hU : IsCircuit d U) :
    IsCircuit d (star U) := by
  first
    | exact OAI.QAC.IsCircuit.star_mem hU
    | exact OAI.QAC.IsCircuit.star_mem
    | (apply OAI.QAC.IsCircuit.star_mem <;> assumption)
    | (intros; apply OAI.QAC.IsCircuit.star_mem <;> assumption)
