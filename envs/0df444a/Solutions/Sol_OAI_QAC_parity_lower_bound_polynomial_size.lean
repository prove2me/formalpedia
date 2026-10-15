-- Prove2me | solution 1 for OAI.QAC.parity_lower_bound_polynomial_size
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:43:43.736062+00:00
-- url     : https://prove2.me/submissions/2aeb72b3-4ec3-4903-b305-1f8bd05e95d7

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Main.lean:L11-L39
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.QAC.parity_lower_bound_polynomial_size.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_QAC_parity_lower_bound_polynomial_size) verbatim and is proved by it.
import Mathlib
import Definitions.Def_RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Model
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_DepthZero__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Localization__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Toffoli__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Physical__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Computational__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Ancilla__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ParityTrace__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Measurement__RegularParity

-- ---- from OAI.InformationTheory.QuantumCircuit.ProductProjection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
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

lemma tensorMatrix_zero_of_zero {N : ℕ} (a : Fin N → QubitOperator)
    (i : Fin N) (hi : a i = 0) : tensorMatrix a = 0 := by
  classical
  ext x y
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hi]

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

lemma tensorMatrix_unitary {N : ℕ} (a : Fin N → QubitOperator)
    (ha : ∀ i, a i ∈ unitary QubitOperator) : tensorMatrix a ∈ unitary (Operator N) := by
  rw [Unitary.mem_iff]
  simp only [tensorMatrix_star, tensorMatrix_mul]
  constructor <;> convert tensorMatrix_one (N := N) using 1 <;>
    congr 1 <;> funext i
  · exact (Unitary.mem_iff.mp (ha i)).1
  · exact (Unitary.mem_iff.mp (ha i)).2

lemma rankOne_projection {v : Bit → ℂ} (hv : ∑ b, Complex.normSq (v b) = 1) :
    IsStarProjection (rankOne v) := by
  rw [isStarProjection_iff']
  refine ⟨?_, rankOne_star v⟩
  ext x y
  simp only [Matrix.mul_apply, rankOne]
  calc
    _ = v x * (∑ z, star (v z) * v z) * star (v y) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      congr 1
      funext z
      ring
    _ = _ := by rw [normalized_complex hv]; ring

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

lemma Count.pattern_mul {N : ℕ} (M : Count N) {F G : Finset (Fin N)}
    (hF : F ⊆ M.support) (hG : G ⊆ M.support) :
    M.pattern F * M.pattern G = if F = G then M.pattern F else 0 := by
  classical
  by_cases hFG : F = G
  · subst G
    rw [ite_eq_left rfl, (M.pattern_projection F).isIdempotentElem.eq]
  rw [ite_eq_right hFG, Count.pattern, Count.pattern, tensorMatrix_mul]
  obtain ⟨i, hi⟩ : ∃ i, (i ∈ F ∧ i ∉ G) ∨ (i ∈ G ∧ i ∉ F) := by
    by_contra h
    push Not at h
    apply hFG
    ext i
    specialize h i
    aesop
  apply tensorMatrix_zero_of_zero _ i
  rcases hi with ⟨hiF, hiG⟩ | ⟨hiG, hiF⟩
  · simp only [ite_eq_left (hF hiF), ite_eq_left hiF, ite_eq_right hiG]
    exact (rankOne_projection (M.normalized i (hF hiF))).one_sub_mul_self
  · simp only [ite_eq_left (hG hiG), ite_eq_left hiG, ite_eq_right hiF]
    exact (rankOne_projection (M.normalized i (hG hiG))).mul_one_sub_self

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

lemma Count.high_eq_zero {N : ℕ} (M : Count N) {r : ℝ} (hr : (N : ℝ) < r) : M.high r = 0 := by
  classical
  unfold Count.high
  apply Finset.sum_eq_zero
  intro F hF
  rw [ite_eq_right]
  have hFN : F.card ≤ N := by simpa using Finset.card_le_univ F
  have hFR : (F.card : ℝ) ≤ N := by exact_mod_cast hFN
  linarith

section SpectralAlgebra

variable {A ι : Type*} [CStarAlgebra A]

lemma orthogonal_sum_mul (s : Finset ι) (p : ι → A)
    (hp : ∀ i ∈ s, IsStarProjection (p i))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → p i * p j = 0) (c d : ι → ℝ) :
    (∑ i ∈ s, c i • p i) * (∑ i ∈ s, d i • p i) = ∑ i ∈ s, (c i * d i) • p i := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · rw [smul_mul_smul_comm, (hp i hi).isIdempotentElem.eq]
  · intro j hj hji
    rw [smul_mul_smul_comm, horth i hi j hj (Ne.symm hji), smul_zero]
  · intro h
    exact (h hi).elim

lemma orthogonal_sum_star (s : Finset ι) (p : ι → A)
    (hp : ∀ i ∈ s, IsStarProjection (p i)) (c : ι → ℝ) :
    star (∑ i ∈ s, c i • p i) = ∑ i ∈ s, c i • p i := by
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [star_smul, star_trivial, (hp i hi).isSelfAdjoint.star_eq]

variable [PartialOrder A] [StarOrderedRing A]

lemma orthogonal_sum_norm_le (s : Finset ι) (p : ι → A)
    (hp : ∀ i ∈ s, IsStarProjection (p i))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → p i * p j = 0)
    (hsum : ∑ i ∈ s, p i = 1) (c : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ i ∈ s, |c i| ≤ C) : ‖∑ i ∈ s, c i • p i‖ ≤ C := by
  have hsq : star (∑ i ∈ s, c i • p i) * (∑ i ∈ s, c i • p i) =
      ∑ i ∈ s, (c i)^2 • p i := by
    rw [orthogonal_sum_star s p hp c, orthogonal_sum_mul s p hp horth]
    simp only [pow_two]
  have hle : (∑ i ∈ s, (c i)^2 • p i) ≤ algebraMap ℝ A (C^2) := by
    calc
      _ ≤ ∑ i ∈ s, C^2 • p i := by
        apply Finset.sum_le_sum
        intro i hi
        apply smul_le_smul_of_nonneg_right _ (hp i hi).nonneg
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).2 (hc i hi)
      _ = _ := by rw [← Finset.smul_sum, hsum, Algebra.algebraMap_eq_smul_one]
  have hnorm := (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg C)
    (star_mul_self_nonneg (∑ i ∈ s, c i • p i))).2 (hsq ▸ hle)
  rw [CStarRing.norm_star_mul_self] at hnorm
  nlinarith only [hnorm, norm_nonneg (∑ i ∈ s, c i • p i), hC]

end SpectralAlgebra

open scoped MatrixOrder in
lemma Count.spectral_norm_le {N : ℕ} (M : Count N) (f : ℕ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ k ≤ N, |f k| ≤ C) :
    ‖∑ F ∈ M.support.powerset, f F.card • M.pattern F‖ ≤ C := by
  refine orthogonal_sum_norm_le M.support.powerset M.pattern
    (fun F _ => M.pattern_projection F) ?_ M.sum_pattern _ hC ?_
  · intro F hF G hG hFG
    rw [M.pattern_mul (Finset.mem_powerset.mp hF) (Finset.mem_powerset.mp hG), ite_eq_right hFG]
  · intro F _
    apply hf
    simpa using Finset.card_le_univ F

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

lemma rankOne_mulVec (U : QubitOperator) (v : Bit → ℂ) :
    rankOne (U *ᵥ v) = U * rankOne v * star U := by
  change Matrix.vecMulVec (U *ᵥ v) (star (U *ᵥ v)) =
    U * Matrix.vecMulVec v (star v) * star U
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]
  rfl

lemma rankOne_orthogonalVector {v : Bit → ℂ} (hv : ∑ b, Complex.normSq (v b) = 1) :
    rankOne (orthogonalVector v) = 1 - rankOne v := by
  have h := normalized_complex hv
  simp only [Fin.sum_univ_two, Complex.star_def] at h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rankOne, orthogonalVector]
  · linear_combination h
  · ring
  · ring
  · linear_combination h

lemma Count.rotate_zero {N : ℕ} (M : Count N) (L : LocalLayer N) :
    (M.rotate L).zero = localMatrix L * M.zero * star (localMatrix L) := by
  classical
  dsimp only [Count.zero, Count.rotate, localMatrix]
  rw [tensorMatrix_star, tensorMatrix_mul, tensorMatrix_mul]
  congr 1
  funext i
  by_cases hi : i ∈ M.support
  · simp only [ite_eq_left hi]
    exact rankOne_mulVec _ _
  · simp only [ite_eq_right hi, mul_one, Unitary.mul_star_self_of_mem (L i).property]

lemma Count.flip_zero {N : ℕ} (M : Count N) (F : Finset (Fin N)) :
    (M.flip F).zero = M.pattern F := by
  classical
  dsimp only [Count.zero, Count.flip, Count.pattern]
  congr 1
  funext i
  split_ifs with hi hF
  · exact rankOne_orthogonalVector (M.normalized i hi)
  · rfl
  · rfl

lemma localMatrix_unitary {N : ℕ} (L : LocalLayer N) : localMatrix L ∈ unitary (Operator N) :=
  tensorMatrix_unitary _ (fun i => (L i).property)

lemma localMatrix_mul {N : ℕ} (L K : LocalLayer N) :
    localMatrix L * localMatrix K = localMatrix (fun i => L i * K i) := by
  exact tensorMatrix_mul _ _

lemma localMatrix_star {N : ℕ} (L : LocalLayer N) :
    star (localMatrix L) = localMatrix (fun i => star (L i)) := by
  exact tensorMatrix_star _

lemma reflection_unitary {N : ℕ} (M : Count N) :
    (1 : Operator N) - (2 : ℂ) • M.zero ∈ unitary (Operator N) := by
  have h := M.zero_projection.two_mul_sub_one_mem_unitary
  have hneg : -(2 * M.zero - 1) ∈ unitary (Operator N) := by
    simpa only [Unitary.mem_iff, star_neg, neg_mul_neg] using h
  simpa only [two_smul, two_mul, neg_sub] using hneg

lemma reflectionMatrix_unitary {N : ℕ} (R : ReflectionLayer N) :
    reflectionMatrix R ∈ unitary (Operator N) := by
  apply (unitary (Operator N)).list_prod_mem
  intro U hU
  obtain ⟨M, _, rfl⟩ := List.mem_map.mp hU
  exact reflection_unitary M

lemma IsCircuit.mem_unitary {N d : ℕ} {U : Operator N} (hU : IsCircuit d U) :
    U ∈ unitary (Operator N) := by
  induction d generalizing U with
  | zero => obtain ⟨L, rfl⟩ := hU; exact localMatrix_unitary L
  | succ d ih =>
    obtain ⟨V, R, L, hV, rfl⟩ := hU
    exact (unitary (Operator N)).mul_mem
      ((unitary (Operator N)).mul_mem (ih hV) (reflectionMatrix_unitary R)) (localMatrix_unitary L)

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

-- ---- from OAI.InformationTheory.QuantumCircuit.Count ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma tensorMatrix_smul {N : ℕ} (c : Fin N → ℝ) (a : Fin N → QubitOperator) :
    tensorMatrix (fun i => c i • a i) = (∏ i, c i) • tensorMatrix a := by
  ext x y
  simp only [tensorMatrix, Matrix.smul_apply, Complex.real_smul, Finset.prod_mul_distrib,
    Complex.ofReal_prod]

open scoped MatrixOrder in
lemma tensorMatrix_nonneg {N : ℕ} (a : Fin N → QubitOperator) (ha : ∀ i, 0 ≤ a i) :
    0 ≤ tensorMatrix a := by
  choose b hb using fun i => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (ha i)
  have h : tensorMatrix a = star (tensorMatrix b) * tensorMatrix b := by
    rw [tensorMatrix_star, tensorMatrix_mul]
    congr 1
    funext i
    exact hb i
  rw [h]
  exact star_mul_self_nonneg _

open scoped MatrixOrder in
lemma tensorMatrix_le_one {N : ℕ} (a : Fin N → QubitOperator)
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) : tensorMatrix a ≤ 1 := by
  classical
  have hsum := tensorMatrix_sum_patterns (Finset.univ : Finset (Fin N))
    (fun i => 1 - a i) a (fun _ => 1)
  simp only [Finset.mem_univ, ite_true, sub_add_cancel, tensorMatrix_one] at hsum
  rw [← hsum]
  have hmem : (∅ : Finset (Fin N)) ∈ Finset.univ.powerset := Finset.mem_powerset.mpr (Finset.empty_subset _)
  have h := Finset.single_le_sum (fun F (_ : F ∈ (Finset.univ : Finset (Fin N)).powerset) =>
    tensorMatrix_nonneg (fun i => if i ∈ F then 1 - a i else a i)
      (fun i => by split_ifs; exact sub_nonneg.mpr (ha1 i); exact ha i)) hmem
  simpa only [Finset.notMem_empty, ite_false] using h

lemma Count.join_zero {N : ℕ} (A B : Count N) (h : Disjoint A.support B.support) :
    (A.join B).zero = A.zero * B.zero := by
  classical
  dsimp only [Count.zero, Count.join]
  rw [tensorMatrix_mul]
  congr 1
  funext i
  by_cases hA : i ∈ A.support
  · have hB : i ∉ B.support := Finset.disjoint_left.mp h hA
    simp [hA, hB]
  · by_cases hB : i ∈ B.support <;> simp [hA, hB]

lemma Count.disjoint_commute {N : ℕ} (A B : Count N) (h : Disjoint A.support B.support) :
    Commute A.zero B.zero := by
  classical
  show A.zero * B.zero = B.zero * A.zero
  dsimp only [Count.zero]
  rw [tensorMatrix_mul, tensorMatrix_mul]
  congr 1
  funext i
  by_cases hA : i ∈ A.support
  · have hB : i ∉ B.support := Finset.disjoint_left.mp h hA
    simp [hA, hB]
  · simp [hA]

lemma Count.restrict_zero_mul {N : ℕ} (M : Count N) (S T : Finset (Fin N)) :
    (M.restrict S).zero * (M.restrict T).zero = (M.restrict (S ∪ T)).zero := by
  classical
  dsimp only [Count.zero, Count.restrict]
  rw [tensorMatrix_mul]
  congr 1
  funext i
  by_cases hi : i ∈ M.support
  · by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
      simp [hi, hS, hT, (rankOne_projection (M.normalized i hi)).isIdempotentElem.eq]
  · simp [hi]

lemma Count.restrict_support_card {N : ℕ} (M : Count N) (S : Finset (Fin N)) :
    (M.restrict S).support.card ≤ S.card := Finset.card_le_card Finset.inter_subset_right

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Spectral ----
-- Lean 4.34 name of List.sum_le_card_nsmul (same statement) in Mathlib 0df444a.
private abbrev List.sum_le_length_nsmul := @List.sum_le_card_nsmul

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma Count.flip_pattern {N : ℕ} (M : Count N) (F G : Finset (Fin N)) :
    (M.flip F).pattern G = M.pattern (F ∆ G) := by
  classical
  dsimp only [Count.pattern, Count.flip]
  congr 1
  funext i
  by_cases hi : i ∈ M.support
  · have hv := rankOne_orthogonalVector (M.normalized i hi)
    by_cases hF : i ∈ F <;> by_cases hG : i ∈ G <;>
      simp [hi, hF, hG, Finset.mem_symmDiff, hv]
  · simp [hi]

lemma Count.high_mul_pattern {N : ℕ} (M : Count N) (F : Finset (Fin N))
    (hF : F ⊆ M.support) (r : ℝ) :
    M.high r * M.pattern F = if r ≤ (F.card : ℝ) then M.pattern F else 0 := by
  classical
  rw [Count.high, Finset.sum_mul, Finset.sum_eq_single F]
  · split_ifs with h
    · exact (M.pattern_projection F).isIdempotentElem.eq
    · exact zero_mul _
  · intro G hG hGF
    split_ifs
    · rw [M.pattern_mul (Finset.mem_powerset.mp hG) hF, ite_eq_right hGF]
    · exact zero_mul _
  · intro h
    exact (h (Finset.mem_powerset.mpr hF)).elim

lemma symmDiff_subset_of_subset {α : Type*} [DecidableEq α] {F G S : Finset α}
    (hF : F ⊆ S) (hG : G ⊆ S) : F ∆ G ⊆ S :=
  Finset.symmDiff_subset_union.trans (Finset.union_subset hF hG)

lemma card_le_add_symmDiff {α : Type*} [DecidableEq α] (F G : Finset α) :
    G.card ≤ F.card + (F ∆ G).card := by
  have h : G ⊆ F ∪ (F ∆ G) := by
    intro i hi
    by_cases hF : i ∈ F
    · exact Finset.mem_union_left _ hF
    · exact Finset.mem_union_right _ (Finset.mem_symmDiff.mpr (Or.inr ⟨hi,hF⟩))
  exact (Finset.card_le_card h).trans (Finset.card_union_le _ _)

lemma Count.high_flip_absorb {N : ℕ} (M : Count N) (F : Finset (Fin N))
    (hF : F ⊆ M.support) {r q : ℝ} (hrq : q + F.card ≤ r) :
    (M.flip F).high q * M.high r = M.high r := by
  classical
  rw [M.high_eq_sum_filter r, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro G hG
  have hrG : r ≤ (G.card : ℝ) := (Finset.mem_filter.mp hG).2
  have hGs : G ⊆ M.support := Finset.mem_powerset.mp (Finset.mem_filter.mp hG).1
  have hFGs : F ∆ G ⊆ (M.flip F).support := symmDiff_subset_of_subset hF hGs
  have heq : M.pattern G = (M.flip F).pattern (F ∆ G) := by
    rw [M.flip_pattern, symmDiff_symmDiff_cancel_left]
  rw [heq, (M.flip F).high_mul_pattern _ hFGs, ite_eq_left]
  have hc : (G.card : ℝ) ≤ F.card + (F ∆ G).card := by exact_mod_cast card_le_add_symmDiff F G
  linarith

lemma Count.low_projection {N : ℕ} (M : Count N) (r : ℝ) : IsStarProjection (M.low r) :=
  (M.high_projection r).one_sub

lemma Count.low_eq_sum {N : ℕ} (M : Count N) (r : ℝ) :
    M.low r = ∑ F ∈ M.support.powerset.filter (fun F => (F.card : ℝ) < r), M.pattern F := by
  classical
  rw [Count.low, ← M.sum_pattern]
  unfold Count.high
  rw [← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro F _
  by_cases h : r ≤ (F.card : ℝ)
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

lemma norm_mul_le_right {A : Type*} [NormedRing A] (x y : A) (hx : ‖x‖ ≤ 1) :
    ‖x*y‖ ≤ ‖y‖ := (norm_mul_le _ _).trans (by nlinarith only [hx, norm_nonneg y])

lemma norm_mul_le_left {A : Type*} [NormedRing A] (x y : A) (hy : ‖y‖ ≤ 1) :
    ‖x*y‖ ≤ ‖x‖ := (norm_mul_le _ _).trans (by nlinarith only [hy, norm_nonneg x])

lemma Count.high_flip_norm {N : ℕ} (M : Count N) (F : Finset (Fin N))
    (hF : F ⊆ M.support) {r q : ℝ} (hrq : q + F.card ≤ r) (B : Operator N) :
    ‖M.high r * B * M.pattern F‖ ≤ ‖(M.flip F).high q * B * (M.flip F).zero‖ := by
  have habs := congrArg star (M.high_flip_absorb F hF hrq)
  simp only [star_mul, (M.high_projection r).isSelfAdjoint.star_eq,
    ((M.flip F).high_projection q).isSelfAdjoint.star_eq] at habs
  rw [M.flip_zero]
  calc
    _ = ‖M.high r * ((M.flip F).high q * B * M.pattern F)‖ := by rw [← mul_assoc, ← mul_assoc, habs]
    _ ≤ _ := norm_mul_le_right _ _ (IsStarProjection.norm_le _ (M.high_projection r))

lemma Count.generator_mul_pattern {N : ℕ} (M : Count N) (i : Fin N) (hi : i ∈ M.support)
    (F : Finset (Fin N)) :
    tensorMatrix (fun j => if j = i then 1-rankOne (M.vector i) else 1) * M.pattern F =
      if i ∈ F then M.pattern F else 0 := by
  classical
  rw [Count.pattern, tensorMatrix_mul]
  by_cases hiF : i ∈ F
  · rw [ite_eq_left hiF]
    congr 1
    funext j
    by_cases hji : j = i
    · subst j
      simp only [ite_eq_left hi, ite_eq_left hiF]
      exact (rankOne_projection (M.normalized i hi)).one_sub.isIdempotentElem.eq
    · simp only [ite_eq_right hji, one_mul]
  · rw [ite_eq_right hiF]
    apply tensorMatrix_zero_of_zero _ i
    simp only [ite_eq_left hi, ite_eq_right hiF]
    exact (rankOne_projection (M.normalized i hi)).one_sub_mul_self

lemma Count.operator_mul_pattern {N : ℕ} (M : Count N) (F : Finset (Fin N)) (hF : F ⊆ M.support) :
    M.operator * M.pattern F = (F.card : ℝ) • M.pattern F := by
  classical
  rw [Count.operator, Finset.sum_mul]
  calc
    _ = ∑ i ∈ M.support, if i ∈ F then M.pattern F else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact M.generator_mul_pattern i hi F
    _ = _ := by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hF, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]

lemma Count.operator_spectral {N : ℕ} (M : Count N) :
    M.operator = M.spectral (fun k => k) := by
  classical
  calc
    _ = M.operator * (∑ F ∈ M.support.powerset, M.pattern F) := by rw [M.sum_pattern,mul_one]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F hF
      exact M.operator_mul_pattern F (Finset.mem_powerset.mp hF)

lemma Count.spectral_mul {N : ℕ} (M : Count N) (f g : ℕ → ℝ) :
    M.spectral f * M.spectral g = M.spectral (fun k => f k * g k) := by
  classical
  exact orthogonal_sum_mul _ _ (fun F _ => M.pattern_projection F)
    (fun F hF G hG hFG => by
      rw [M.pattern_mul (Finset.mem_powerset.mp hF) (Finset.mem_powerset.mp hG),ite_eq_right hFG]) _ _

lemma Count.operator_pow_spectral {N : ℕ} (M : Count N) (k : ℕ) :
    M.operator^k = M.spectral (fun j => (j:ℝ)^k) := by
  induction k with
  | zero => simp [Count.spectral]
  | succ k ih => rw [pow_succ,ih,M.operator_spectral,M.spectral_mul]; simp only [pow_succ]

lemma Count.operator_norm_le {N : ℕ} (M : Count N) : ‖M.operator‖ ≤ N := by
  rw [M.operator_spectral]
  exact M.spectral_norm_le _ (by positivity) (fun k hk => by simpa using (show (k:ℝ) ≤ N by exact_mod_cast hk))

lemma Count.polynomial_eq_sum {N : ℕ} (M : Count N) (p : Polynomial ℝ) :
    M.polynomial p = ∑ k ∈ p.support, p.coeff k • M.operator^k := by
  classical
  unfold Count.polynomial Count.spectral
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.smul_sum]
  change p.coeff k • M.spectral (fun j => (j:ℝ)^k) = _
  rw [← M.operator_pow_spectral]

lemma Count.generator_eq_restrict {N : ℕ} (M : Count N) (i : Fin N) (hi : i ∈ M.support) :
    tensorMatrix (fun j => if j = i then 1-rankOne (M.vector i) else 1) =
      ((M.flip M.support).restrict {i}).zero := by
  classical
  dsimp only [Count.zero, Count.restrict, Count.flip]
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Finset.mem_inter, Finset.mem_singleton, hi, true_and, ite_true]
    exact (rankOne_orthogonalVector (M.normalized i hi)).symm
  · simp [hji]

lemma selectionSets_card {ι : Type*} [DecidableEq ι] (S : Finset ι) (k : ℕ) :
    ∀ F ∈ selectionSets S k, F.card ≤ k := by
  induction k with
  | zero => intro F hF; simpa [selectionSets] using hF
  | succ k ih =>
    intro F hF
    obtain ⟨i, _, hFi⟩ := List.mem_flatMap.mp hF
    obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hFi
    exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (ih G hG) 1)

lemma selectionSets_length {ι : Type*} [DecidableEq ι] (S : Finset ι) (k : ℕ) :
    (selectionSets S k).length = S.card^k := by
  induction k with
  | zero => simp [selectionSets]
  | succ k ih => simp [selectionSets, List.length_flatMap, ih, pow_succ, mul_comm]

lemma list_sum_flatMap {ι κ A : Type*} [AddMonoid A] (l : List ι) (f : ι → List κ) (g : κ → A) :
    ((l.flatMap f).map g).sum = (l.map (fun i => ((f i).map g).sum)).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

lemma Count.selectionSets_sum {N : ℕ} (M : Count N) (S : Finset (Fin N)) (k : ℕ) :
    ((selectionSets S k).map (fun F => (M.restrict F).zero)).sum =
      (∑ i ∈ S, (M.restrict {i}).zero)^k := by
  classical
  induction k with
  | zero => simp [selectionSets,Count.zero,Count.restrict]
  | succ k ih =>
    rw [selectionSets, list_sum_flatMap]
    simp only [List.map_map]
    dsimp only [Function.comp_def]
    have hi : ∀ i, ((selectionSets S k).map (fun F => (M.restrict (insert i F)).zero)).sum =
        (M.restrict {i}).zero * ((selectionSets S k).map (fun F => (M.restrict F).zero)).sum := by
      intro i
      simp_rw [← Finset.singleton_union, ← M.restrict_zero_mul]
      exact List.sum_map_mul_left _ _ _
    simp_rw [hi,ih]
    rw [List.sum_map_mul_right, ← List.sum_toFinset _ S.nodup_toList, Finset.toList_toFinset, pow_succ']

lemma Count.operator_monomials {N : ℕ} (M : Count N) (k : ℕ) :
    M.operator^k = ((selectionSets M.support k).map
      (fun F => ((M.flip M.support).restrict F).zero)).sum := by
  rw [(M.flip M.support).selectionSets_sum]
  congr 1
  unfold Count.operator
  apply Finset.sum_congr rfl
  intro i hi
  exact M.generator_eq_restrict i hi

lemma list_norm_sum_le {A : Type*} [SeminormedAddCommGroup A] (l : List A) :
    ‖l.sum‖ ≤ (l.map norm).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.sum_cons,List.map_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

lemma list_norm_sum_le_const {ι A : Type*} [SeminormedAddCommGroup A]
    (l : List ι) (f : ι → A) (C : ℝ) (hf : ∀ i ∈ l, ‖f i‖ ≤ C) :
    ‖(l.map f).sum‖ ≤ l.length * C := by
  apply (list_norm_sum_le _).trans
  rw [List.map_map]
  have h := List.sum_le_length_nsmul (l.map (norm ∘ f)) C (by
    intro c hc
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
    exact hf i hi)
  simpa only [List.length_map, nsmul_eq_mul] using h

lemma Count.zero_spectral {N : ℕ} (M : Count N) :
    M.zero = M.spectral (fun k => if k = 0 then 1 else 0) := by
  classical
  unfold Count.spectral
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro F _ hF
    simp only [Finset.card_eq_zero, ite_eq_right hF, zero_smul]
  · simp

lemma Count.low_spectral {N : ℕ} (M : Count N) (r : ℝ) :
    M.low r = M.spectral (fun k => if (k:ℝ) < r then 1 else 0) := by
  classical
  rw [M.low_eq_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro F _
  split_ifs with h <;> simp only [h, ite_true, ite_false, one_smul, zero_smul]

lemma Count.spectral_sub {N : ℕ} (M : Count N) (f g : ℕ → ℝ) :
    M.spectral f - M.spectral g = M.spectral (fun k => f k - g k) := by
  simp only [Count.spectral, sub_smul, Finset.sum_sub_distrib]

lemma Count.polynomial_error_low {N : ℕ} (M : Count N) (p : Polynomial ℝ)
    {r δ : ℝ} (hδ : 0 ≤ δ) (hp0 : p.eval 0 = 1)
    (hp : ∀ k : ℕ, 1 ≤ k → (k:ℝ) < r → |p.eval (k:ℝ)| ≤ δ) :
    ‖(M.zero - M.polynomial p) * M.low r‖ ≤ δ := by
  rw [M.zero_spectral, Count.polynomial, M.spectral_sub, M.low_spectral, M.spectral_mul]
  apply M.spectral_norm_le (fun k => ((if k = 0 then 1 else 0) - p.eval (k:ℝ)) *
    (if (k:ℝ) < r then 1 else 0)) hδ
  intro k _
  by_cases hk : k = 0
  · subst k; simpa [hp0] using hδ
  · by_cases hkr : (k:ℝ) < r
    · simpa [hk,hkr] using hp k (by omega) hkr
    · simpa [hkr] using hδ

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Transition ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

section NormAlgebra
variable {A : Type*} [CStarAlgebra A]

lemma norm_unitary_conjugate {U : A} (hU : U ∈ unitary A) (B : A) :
    ‖U * B * star U‖ = ‖B‖ := by
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hU), CStarRing.norm_mem_unitary_mul _ hU]

lemma conjugate_projection {U B : A} (hU : U ∈ unitary A) (hB : IsStarProjection B) :
    IsStarProjection (U * B * star U) := by
  rw [isStarProjection_iff']
  constructor
  · calc
      _ = U * (B * B) * star U := by
        simp only [mul_assoc, ← mul_assoc (star U) U, Unitary.star_mul_self_of_mem hU, one_mul]
      _ = _ := by rw [hB.isIdempotentElem.eq]
  · simp only [star_mul, star_star, hB.isSelfAdjoint.star_eq, mul_assoc]

lemma projection_transition_square (H P Q X : A)
    (hH : IsStarProjection H) (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    ‖H * Q * P‖^2 ≤ ‖H * X * P‖ + ‖(Q-X) * P * Q‖ := by
  have hid : (H*Q*P) * star (H*Q*P) = H*Q*P*Q*H := by
    simp only [star_mul, hH.isSelfAdjoint.star_eq, hP.isSelfAdjoint.star_eq,
      hQ.isSelfAdjoint.star_eq]
    calc
      _ = H * Q * (P*P) * Q * H := by simp only [mul_assoc]
      _ = _ := by rw [hP.isIdempotentElem.eq]
  have heq : H*Q*P*Q*H = (H*X*P)*Q*H + H*((Q-X)*P*Q)*H := by noncomm_ring
  calc
    ‖H*Q*P‖^2 = ‖(H*Q*P) * star (H*Q*P)‖ := by rw [CStarRing.norm_self_mul_star]; ring
    _ = ‖(H*X*P)*Q*H + H*((Q-X)*P*Q)*H‖ := by rw [hid,heq]
    _ ≤ ‖(H*X*P)*Q*H‖ + ‖H*((Q-X)*P*Q)*H‖ := norm_add_le _ _
    _ ≤ _ := by
      apply add_le_add
      · exact (norm_mul_le_left _ _ (IsStarProjection.norm_le _ hH)).trans
          (norm_mul_le_left _ _ (IsStarProjection.norm_le _ hQ))
      · exact (norm_mul_le_left _ _ (IsStarProjection.norm_le _ hH)).trans
          (norm_mul_le_right _ _ (IsStarProjection.norm_le _ hH))

lemma norm_split_bound (E W P Q : A) (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) :
    ‖E*P*Q‖ ≤ ‖E*(1-W)‖ + ‖E‖*‖W*P*Q‖ := by
  have heq : E*P*Q = E*(1-W)*P*Q + E*(W*P*Q) := by noncomm_ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_mul_le_left _ _ hQ).trans (norm_mul_le_left _ _ hP)) (norm_mul_le _ _))
end NormAlgebra

lemma sum_powers_bound (N K : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.range K, N^k ≤ (N+1)^K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hpow : N^K ≤ (N+1)^K := Nat.pow_le_pow_left (by omega) _
    have hmul : (N+1)^K ≤ (N+1)^K*N := by
      simpa only [mul_one] using Nat.mul_le_mul_left ((N+1)^K) hN
    nlinarith only [ih, hpow, hmul]

lemma low_patterns_card {N : ℕ} (S : Finset (Fin N)) {r : ℝ} (hN : 1 ≤ N) :
    (S.powerset.filter (fun F => (F.card:ℝ) < r)).card ≤ (N+1)^(⌈r⌉₊+1) := by
  classical
  have hsub : S.powerset.filter (fun F => (F.card:ℝ) < r) ⊆
      (Finset.range (⌈r⌉₊+1)).biUnion (fun k => S.powersetCard k) := by
    intro F hF
    obtain ⟨hFS, hFr⟩ := Finset.mem_filter.mp hF
    refine Finset.mem_biUnion.mpr ⟨F.card, ?_, Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hFS,rfl⟩⟩
    rw [Finset.mem_range]
    have h : (F.card:ℝ) ≤ ⌈r⌉₊ := hFr.le.trans (Nat.le_ceil r)
    have : F.card ≤ ⌈r⌉₊ := by exact_mod_cast h
    omega
  calc
    _ ≤ ((Finset.range (⌈r⌉₊+1)).biUnion (fun k => S.powersetCard k)).card := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range (⌈r⌉₊+1), (S.powersetCard k).card := Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (⌈r⌉₊+1), N^k := by
      apply Finset.sum_le_sum
      intro k _
      rw [Finset.card_powersetCard]
      exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by simpa using Finset.card_le_univ S) _)
    _ ≤ _ := sum_powers_bound N _ hN

lemma list_disjoint_hits_length {ι κ : Type*} [DecidableEq κ]
    (f : ι → Finset κ) (l : List ι) (hl : l.Pairwise (fun a b => Disjoint (f a) (f b)))
    (S : Finset κ) (hS : ∀ a ∈ l, (f a ∩ S).Nonempty) : l.length ≤ S.card := by
  induction l generalizing S with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.pairwise_cons.mp hl
    obtain ⟨i,hi⟩ := hS a (List.mem_cons_self ..)
    obtain ⟨hia,hiS⟩ := Finset.mem_inter.mp hi
    have hh : ∀ b ∈ l, (f b ∩ S.erase i).Nonempty := by
      intro b hb
      obtain ⟨j,hj⟩ := hS b (List.mem_cons_of_mem _ hb)
      obtain ⟨hjb,hjS⟩ := Finset.mem_inter.mp hj
      have hji : j ≠ i := by
        intro h
        subst j
        exact Finset.disjoint_left.mp (ha b hb) hia hjb
      exact ⟨j,Finset.mem_inter.mpr ⟨hjb,Finset.mem_erase.mpr ⟨hji,hjS⟩⟩⟩
    have h := ih hl (S.erase i) hh
    simp only [List.length_cons]
    have hc := Finset.card_erase_add_one hiS
    omega

/-- Scalar list estimates retain multiplicities, including the ordered monomials. -/
lemma norm_list_smul_sum {ι A : Type*} [SeminormedAddCommGroup A] [NormedSpace ℝ A]
    (l : List ι) (c : ι → ℝ) (f : ι → A) (δ : ℝ) (hf : ∀ i ∈ l, ‖f i‖ ≤ δ) :
    ‖(l.map (fun i => c i • f i)).sum‖ ≤ (l.map (fun i => |c i|)).sum * δ := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons,List.sum_cons,add_mul]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hf i (List.mem_cons_self ..)) (abs_nonneg _)
    · exact ih (fun j hj => hf j (List.mem_cons_of_mem _ hj))

lemma Count.low_propagation_bound {N : ℕ} (M : Count N) (B : Operator N)
    {r q R δ : ℝ} (hN : 1 ≤ N) (hδ : 0 ≤ δ) (hrq : q + r ≤ R)
    (hB : ∀ K : Count N, ‖K.high q * B * K.zero‖ ≤ δ) :
    ‖M.high R * B * M.low r‖ ≤ (N+1:ℝ)^(⌈r⌉₊+1) * δ := by
  classical
  rw [M.low_eq_sum, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ F ∈ M.support.powerset.filter (fun F => (F.card:ℝ) < r), δ := by
      apply Finset.sum_le_sum
      intro F hF
      obtain ⟨hFs, hFr⟩ := Finset.mem_filter.mp hF
      exact (M.high_flip_norm F (Finset.mem_powerset.mp hFs)
        (by linarith) B).trans (hB (M.flip F))
    _ = ((M.support.powerset.filter (fun F => (F.card:ℝ) < r)).card:ℝ)*δ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast low_patterns_card M.support (r:=r) hN) hδ

lemma norm_mul_le_one {A : Type*} [NormedRing A] {x y : A}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x*y‖ ≤ 1 :=
  (norm_mul_le_left _ _ hy).trans hx

section ThreeFactors
variable {A : Type*} [CStarAlgebra A]

lemma three_factor_transition (H P H₁ H₂ B₁ B₂ B₃ : A) {δ : ℝ}
    (hH : ‖H‖ ≤ 1) (hP : ‖P‖ ≤ 1)
    (hE₁ : ‖1-H₁‖ ≤ 1)
    (hB₁ : ‖B₁‖ ≤ 1) (hB₂ : ‖B₂‖ ≤ 1) (hB₃ : ‖B₃‖ ≤ 1)
    (h₁ : ‖H₁*B₃*P‖ ≤ δ) (h₂ : ‖H₂*B₂*(1-H₁)‖ ≤ δ)
    (h₃ : ‖H*B₁*(1-H₂)‖ ≤ δ) : ‖H*B₁*B₂*B₃*P‖ ≤ 3*δ := by
  have heq : H*B₁*B₂*B₃*P = (H*B₁*B₂)*(H₁*B₃*P) +
      (H*B₁)*(H₂*B₂*(1-H₁))*(B₃*P) +
      (H*B₁*(1-H₂))*(B₂*(1-H₁)*B₃*P) := by noncomm_ring
  have ht₁ : ‖(H*B₁*B₂)*(H₁*B₃*P)‖ ≤ δ :=
    (norm_mul_le_right _ _ (norm_mul_le_one (norm_mul_le_one hH hB₁) hB₂)).trans h₁
  have ht₂ : ‖(H*B₁)*(H₂*B₂*(1-H₁))*(B₃*P)‖ ≤ δ :=
    ((norm_mul_le_left _ _ (norm_mul_le_one hB₃ hP)).trans
      (norm_mul_le_right _ _ (norm_mul_le_one hH hB₁))).trans h₂
  have ht₃ : ‖(H*B₁*(1-H₂))*(B₂*(1-H₁)*B₃*P)‖ ≤ δ :=
    (norm_mul_le_left _ _ (norm_mul_le_one (norm_mul_le_one
      (norm_mul_le_one hB₂ hE₁) hB₃) hP)).trans h₃
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
    (by linarith only [ht₁,ht₂,ht₃]))
end ThreeFactors

section Conjugation
variable {A : Type*} [CStarAlgebra A]

lemma conjugate_comp (U V B : A) : conjugate (U*V) B = conjugate U (conjugate V B) := by
  simp only [conjugate,star_mul,mul_assoc]

lemma conjugate_mul {U : A} (hU : U ∈ unitary A) (B C : A) :
    conjugate U (B*C) = conjugate U B * conjugate U C := by
  simp only [conjugate,mul_assoc,← mul_assoc (star U) U,Unitary.star_mul_self_of_mem hU,one_mul]

lemma conjugate_sub (U B C : A) : conjugate U (B-C) = conjugate U B - conjugate U C := by
  simp only [conjugate,mul_sub,sub_mul]

lemma conjugate_one {U : A} (hU : U ∈ unitary A) : conjugate U 1 = 1 := by
  simp only [conjugate,mul_one,Unitary.mul_star_self_of_mem hU]

lemma conjugate_smul (U B : A) (r : ℝ) : conjugate U (r • B) = r • conjugate U B := by
  simp only [conjugate,mul_smul_comm,smul_mul_assoc]

lemma conjugate_list_sum {ι : Type*} (U : A) (l : List ι) (f : ι → A) :
    conjugate U (l.map f).sum = (l.map (fun i => conjugate U (f i))).sum := by
  simp only [conjugate,← List.sum_map_mul_left,← List.sum_map_mul_right]

lemma conjugate_fixed {U B : A} (hU : U ∈ unitary A) (h : Commute U B) :
    conjugate U B = B := by
  rw [conjugate,h.eq,mul_assoc,Unitary.mul_star_self_of_mem hU,mul_one]

lemma list_conjugate_filter {ι : Type*} (f : ι → A) (l : List ι) (p : ι → Bool) (B : A)
    (hl : l.Pairwise (fun a b => Commute (f a) (f b)))
    (hu : ∀ a ∈ l, f a ∈ unitary A)
    (hd : ∀ a ∈ l, p a = false → Commute (f a) B) :
    conjugate (l.map f).prod B = conjugate ((l.filter p).map f).prod B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.pairwise_cons.mp hl
    have hu' : ∀ b ∈ l, f b ∈ unitary A := fun b hb => hu b (List.mem_cons_of_mem _ hb)
    have hd' : ∀ b ∈ l, p b = false → Commute (f b) B := fun b hb => hd b (List.mem_cons_of_mem _ hb)
    have hc : Commute (f a) (l.map f).prod := by
      apply Commute.list_prod_right
      intro x hx
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
      exact ha b hb
    cases hpa : p a with
    | false =>
      simp only [List.map_cons,List.prod_cons,List.filter_cons,hpa,Bool.false_eq_true,ite_false]
      rw [hc.eq,conjugate_comp,conjugate_fixed (hu a (List.mem_cons_self ..))
        (hd a (List.mem_cons_self ..) hpa)]
      exact ih hl hu' hd'
    | true =>
      simp only [List.map_cons,List.prod_cons,List.filter_cons,hpa,ite_true,List.map_cons,List.prod_cons]
      rw [conjugate_comp,conjugate_comp,ih hl hu' hd']
end Conjugation

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Reflection ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma reflectionMatrix_eq {N : ℕ} (R : ReflectionLayer N) : reflectionMatrix R = reflectList R.gates := by
  unfold reflectionMatrix reflectList
  congr 1

lemma reflect_unitary {N : ℕ} (D : Count N) : reflect D ∈ unitary (Operator N) := by
  simpa only [reflect,two_smul] using reflection_unitary D

lemma reflect_disjoint_commute {N : ℕ} (A B : Count N) (h : Disjoint A.support B.support) :
    Commute (reflect A) (reflect B) := by
  exact (Commute.one_left _).sub_left
    (((Commute.one_right _).sub_right ((A.disjoint_commute B h).smul_right (2:ℝ))).smul_left (2:ℝ))

lemma reflect_disjoint_zero_commute {N : ℕ} (A B : Count N) (h : Disjoint A.support B.support) :
    Commute (reflect A) B.zero :=
  (Commute.one_left _).sub_left ((A.disjoint_commute B h).smul_left (2:ℝ))

lemma ReflectionLayer.active_length {N : ℕ} (R : ReflectionLayer N) (A : Count N) :
    (R.active A).gates.length ≤ A.support.card := by
  apply list_disjoint_hits_length Count.support _ (R.active A).disjoint
  intro D hD
  have h := (List.mem_filter.mp hD).2
  simp only [decide_eq_true_eq] at h
  exact Finset.not_disjoint_iff_nonempty_inter.mp h

lemma ReflectionLayer.active_conjugate {N : ℕ} (R : ReflectionLayer N) (A : Count N) :
    conjugate (reflectionMatrix R) A.zero = conjugate (reflectionMatrix (R.active A)) A.zero := by
  rw [reflectionMatrix_eq,reflectionMatrix_eq]
  apply list_conjugate_filter
  · exact R.disjoint.imp (fun h => reflect_disjoint_commute _ _ h)
  · intro D _; exact reflect_unitary D
  · intro D _ hD
    apply reflect_disjoint_zero_commute
    simpa using hD

lemma reflectionTerms_support {N : ℕ} (l : List (Count N)) :
    ∀ p ∈ reflectionTerms l, ∀ i ∈ p.2.support, ∃ A ∈ l, i ∈ A.support := by
  induction l with
  | nil => simp [reflectionTerms,Count.empty]
  | cons A l ih =>
    intro p hp i hi
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨B,hB,hiB⟩ := ih p hp i hi
      exact ⟨B,List.mem_cons_of_mem _ hB,hiB⟩
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      rcases Finset.mem_union.mp hi with hi | hi
      · exact ⟨A,List.mem_cons_self ..,hi⟩
      · obtain ⟨B,hB,hiB⟩ := ih q hq i hi
        exact ⟨B,List.mem_cons_of_mem _ hB,hiB⟩

lemma reflectionTerms_disjoint {N : ℕ} (A : Count N) (l : List (Count N))
    (h : ∀ B ∈ l, Disjoint A.support B.support) (p : ℝ × Count N) (hp : p ∈ reflectionTerms l) :
    Disjoint A.support p.2.support := by
  apply Finset.disjoint_left.mpr
  intro i hiA hip
  obtain ⟨B,hB,hiB⟩ := reflectionTerms_support l p hp i hip
  exact Finset.disjoint_left.mp (h B hB) hiA hiB

lemma reflectionTerms_sum {N : ℕ} (l : List (Count N))
    (hl : l.Pairwise (fun A B => Disjoint A.support B.support)) :
    ((reflectionTerms l).map (fun p => p.1 • p.2.zero)).sum = reflectList l := by
  induction l with
  | nil => simp [reflectionTerms,reflectList]
  | cons A l ih =>
    obtain ⟨ha,hl⟩ := List.pairwise_cons.mp hl
    rw [reflectionTerms,List.map_append,List.sum_append,List.map_map]
    have heq : ((reflectionTerms l).map (fun p => (-2*p.1) • (A.join p.2).zero)) =
        (reflectionTerms l).map (fun p => ((-2:ℝ) • A.zero) * (p.1 • p.2.zero)) := by
      apply List.map_congr_left
      intro p hp
      rw [A.join_zero p.2 (reflectionTerms_disjoint A l ha p hp),smul_mul_smul_comm]
    change ((reflectionTerms l).map (fun p => p.1 • p.2.zero)).sum +
      ((reflectionTerms l).map (fun p => (-2*p.1) • (A.join p.2).zero)).sum = _
    rw [heq,List.sum_map_mul_left,ih hl]
    simp only [reflectList,List.map_cons,List.prod_cons,reflect,sub_mul,one_mul,neg_smul,neg_mul]
    abel

lemma reflectionTerms_weight {N : ℕ} (l : List (Count N)) :
    ((reflectionTerms l).map (fun p => |p.1|)).sum = (3:ℝ)^l.length := by
  induction l with
  | nil => simp [reflectionTerms]
  | cons A l ih =>
    simp only [reflectionTerms,List.map_append,List.sum_append,List.map_map,List.length_cons,pow_succ]
    change ((reflectionTerms l).map (fun p => |p.1|)).sum +
      ((reflectionTerms l).map (fun p => |(-2:ℝ)*p.1|)).sum = _
    simp_rw [abs_mul]
    norm_num only [abs_neg]
    rw [List.sum_map_mul_left,ih]
    ring

lemma star_list_sum {A ι : Type*} [AddMonoid A] [StarAddMonoid A] (l : List ι) (f : ι → A) :
    star (l.map f).sum = (l.map (fun i => star (f i))).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

lemma reflectList_selfAdjoint {N : ℕ} (l : List (Count N))
    (hl : l.Pairwise (fun A B => Disjoint A.support B.support)) :
    star (reflectList l) = reflectList l := by
  rw [← reflectionTerms_sum l hl,star_list_sum]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [star_smul,star_trivial,p.2.zero_projection.isSelfAdjoint.star_eq]

section BilinearBudget
variable {A : Type*} [CStarAlgebra A]

lemma list_sum_sandwich {ι : Type*} (l : List ι) (c : ι → ℝ) (f : ι → A) (L R : A) :
    L * (l.map (fun i => c i • f i)).sum * R =
      (l.map (fun i => c i • (L*f i*R))).sum := by
  simp only [← List.sum_map_mul_left,← List.sum_map_mul_right,mul_smul_comm,smul_mul_assoc]

lemma bilinear_list_bound {ι : Type*} (l : List ι) (c : ι → ℝ) (f : ι → A)
    (H B P : A) (δ : ℝ)
    (h : ∀ i ∈ l, ∀ j ∈ l, ‖H*f i*B*f j*P‖ ≤ δ) :
    ‖H * (l.map (fun i => c i • f i)).sum * B *
      (l.map (fun i => c i • f i)).sum * P‖ ≤ (l.map (fun i => |c i|)).sum^2 * δ := by
  let T := (l.map (fun i => c i • f i)).sum
  let C := (l.map (fun i => |c i|)).sum
  have hj : ∀ i ∈ l, ‖H*f i*B*T*P‖ ≤ C*δ := by
    intro i hi
    rw [show H*f i*B*T*P = (H*f i*B)*T*P by rfl, list_sum_sandwich]
    exact norm_list_smul_sum l c _ δ (h i hi)
  have heq : H*T*B*T*P = (l.map (fun i => c i • (H*f i*B*T*P))).sum := by
    calc
      _ = H*T*(B*T*P) := by simp only [mul_assoc]
      _ = _ := by rw [list_sum_sandwich]; simp only [mul_assoc]
  change ‖H*T*B*T*P‖ ≤ C^2*δ
  rw [heq]
  exact (norm_list_smul_sum l c _ (C*δ) hj).trans_eq (by ring)
end BilinearBudget

lemma reflection_conjugate_expansion {N : ℕ} (l : List (Count N))
    (hl : l.Pairwise (fun A B => Disjoint A.support B.support)) (V : Operator N) :
    conjugate V (reflectList l) =
      ((reflectionTerms l).map (fun p => p.1 • conjugate V p.2.zero)).sum := by
  rw [← reflectionTerms_sum l hl,conjugate_list_sum]
  simp only [conjugate_smul]

lemma reflection_transition_bound {N : ℕ} (R : ReflectionLayer N) (V H P : Operator N)
    (A : Count N) (hV : V ∈ unitary (Operator N)) (δ : ℝ)
    (h : ∀ X Y : Count N, ‖H*conjugate V X.zero*conjugate V A.zero*conjugate V Y.zero*P‖ ≤ δ) :
    ‖H*conjugate V (conjugate (reflectionMatrix R) A.zero)*P‖ ≤ (9:ℝ)^R.gates.length*δ := by
  rw [reflectionMatrix_eq]
  unfold conjugate at *
  have heq : H*(V*(reflectList R.gates*A.zero*star (reflectList R.gates))*star V)*P =
      H*conjugate V (reflectList R.gates)*conjugate V A.zero*conjugate V (reflectList R.gates)*P := by
    change H*conjugate V (reflectList R.gates*A.zero*star (reflectList R.gates))*P = _
    rw [reflectList_selfAdjoint _ R.disjoint,conjugate_mul hV,conjugate_mul hV]
    simp only [mul_assoc]
  rw [heq,reflection_conjugate_expansion _ R.disjoint V]
  apply (bilinear_list_bound (reflectionTerms R.gates) Prod.fst
    (fun p => conjugate V p.2.zero) H (conjugate V A.zero) P δ (fun i _ j _ => h i.2 j.2)).trans_eq
  rw [reflectionTerms_weight]
  congr 1
  rw [pow_two,← mul_pow]
  norm_num

lemma small_support_layer_bound {N : ℕ} (V : Operator N) (hV : V ∈ unitary (Operator N))
    (R : ReflectionLayer N) (L : LocalLayer N) (M A : Count N) {r r₁ r₂ δ : ℝ} (hδ : 0 ≤ δ)
    (h₁ : ∀ D : Count N, ‖M.high r₁*conjugate V D.zero*M.zero‖ ≤ δ)
    (h₂ : ∀ D : Count N, ‖M.high r₂*conjugate V D.zero*M.low r₁‖ ≤ δ)
    (h₃ : ∀ D : Count N, ‖M.high r*conjugate V D.zero*M.low r₂‖ ≤ δ) :
    ‖M.high r*conjugate (V*reflectionMatrix R*localMatrix L) A.zero*M.zero‖ ≤
      (9:ℝ)^A.support.card*(3*δ) := by
  have hc : ∀ D : Count N, ‖conjugate V D.zero‖ ≤ 1 := fun D =>
    IsStarProjection.norm_le _ (conjugate_projection hV D.zero_projection)
  have htriple : ∀ X Y Z : Count N,
      ‖M.high r*conjugate V X.zero*conjugate V Y.zero*conjugate V Z.zero*M.zero‖ ≤ 3*δ := by
    intro X Y Z
    exact three_factor_transition _ _ (M.high r₁) (M.high r₂) _ _ _
      (IsStarProjection.norm_le _ (M.high_projection r)) (IsStarProjection.norm_le _ M.zero_projection)
      (IsStarProjection.norm_le _ (M.low_projection r₁)) (hc X) (hc Y) (hc Z) (h₁ Z) (h₂ Y) (h₃ X)
  have hbound := reflection_transition_bound (R.active (A.rotate L)) V (M.high r) M.zero
    (A.rotate L) hV (3*δ) (fun X Y => htriple X (A.rotate L) Y)
  have hlen : (R.active (A.rotate L)).gates.length ≤ A.support.card := R.active_length (A.rotate L)
  calc
    _ = ‖M.high r*conjugate V (conjugate (reflectionMatrix (R.active (A.rotate L))) (A.rotate L).zero)*M.zero‖ := by
      rw [conjugate_comp,conjugate_comp,
        show conjugate (localMatrix L) A.zero = (A.rotate L).zero from (A.rotate_zero L).symm,
        R.active_conjugate]
    _ ≤ (9:ℝ)^(R.active (A.rotate L)).gates.length*(3*δ) := hbound
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hlen) (by positivity)

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Polynomial ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Filter Asymptotics

namespace QAC

lemma weight_nonneg {R : ℝ} (hR : 0 ≤ R) (p : ℝ[X]) : 0 ≤ weight R p := by
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (pow_nonneg hR _)

lemma weight_add_le {R : ℝ} (hR : 0 ≤ R) (p q : ℝ[X]) :
    weight R (p + q) ≤ weight R p + weight R q := by
  let s := p.support ∪ q.support
  have hf : ∀ i : ℕ, |(0 : ℝ)| * R ^ i = 0 := by simp
  have hp : p.support ⊆ s := Finset.subset_union_left
  have hq : q.support ⊆ s := Finset.subset_union_right
  unfold weight
  rw [sum_eq_of_subset _ hf (support_add.trans (Finset.Subset.refl s)),
    sum_eq_of_subset _ hf hp, sum_eq_of_subset _ hf hq, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    rw [coeff_add, ← add_mul]
    exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (pow_nonneg hR _)

lemma weight_sub_le {R : ℝ} (hR : 0 ≤ R) (p q : ℝ[X]) :
    weight R (p - q) ≤ weight R p + weight R q := by
  simpa only [sub_eq_add_neg, weight_neg] using weight_add_le hR p (-q)

lemma weight_sum_le {ι : Type*} {R : ℝ} (hR : 0 ≤ R) (s : Finset ι) (p : ι → ℝ[X]) :
    weight R (∑ i ∈ s, p i) ≤ ∑ i ∈ s, weight R (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (weight_add_le hR (p i) (∑ j ∈ s, p j)).trans (add_le_add_right ih _)

lemma weight_mul_le {R : ℝ} (hR : 0 ≤ R) (p q : ℝ[X]) :
    weight R (p * q) ≤ weight R p * weight R q := by
  rw [mul_eq_sum_sum]
  apply (weight_sum_le hR _ _).trans
  calc
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support,
        weight R (monomial (i + j) (p.coeff i * q.coeff j)) :=
      Finset.sum_le_sum fun i _ => weight_sum_le hR _ _
    _ = weight R p * weight R q := by
      simp_rw [weight_monomial, abs_mul, pow_add]
      unfold weight Polynomial.sum
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

lemma weight_prod_le {ι : Type*} {R : ℝ} (hR : 0 ≤ R) (s : Finset ι) (p : ι → ℝ[X]) :
    weight R (∏ i ∈ s, p i) ≤ ∏ i ∈ s, weight R (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (weight_mul_le hR _ _).trans
      (mul_le_mul_of_nonneg_left ih (weight_nonneg hR _))

lemma weight_chebyshev {R : ℝ} (hR : 0 ≤ R) (z : ℝ[X]) (k : ℕ) :
    weight R ((Polynomial.Chebyshev.T ℝ k).comp z) ≤ (2 * weight R z + 1) ^ k := by
  let b := weight R z
  let A := 2 * b + 1
  have hb : 0 ≤ b := weight_nonneg hR z
  have hA : 1 ≤ A := by dsimp [A]; linarith
  change weight R ((Polynomial.Chebyshev.T ℝ k).comp z) ≤ A ^ k
  induction k using Nat.twoStepInduction with
  | zero => simp [Polynomial.Chebyshev.T_zero]
  | one => simpa [Polynomial.Chebyshev.T_one, A, b] using (show b ≤ A by dsimp [A]; linarith)
  | more k hk hk1 =>
    have heq : Polynomial.Chebyshev.T ℝ (↑(k + 2)) =
        2 * X * Polynomial.Chebyshev.T ℝ (↑(k + 1)) - Polynomial.Chebyshev.T ℝ k := by
      simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using Polynomial.Chebyshev.T_add_two ℝ (k : ℤ)
    rw [heq, sub_comp, mul_comp, mul_comp, X_comp]
    have htwo : weight R ((2 : ℝ[X]).comp z) = 2 := by
      rw [show (2 : ℝ[X]) = C 2 by exact (map_ofNat C 2).symm, C_comp, weight_C]
      norm_num
    calc
      _ ≤ weight R (((2 : ℝ[X]).comp z) * z * (Polynomial.Chebyshev.T ℝ (↑(k + 1))).comp z) +
          weight R ((Polynomial.Chebyshev.T ℝ (↑k)).comp z) := weight_sub_le hR _ _
      _ ≤ (2 * b) * A ^ (k + 1) + A ^ k := by
        apply add_le_add _ hk
        apply (weight_mul_le hR _ _).trans
        apply mul_le_mul _ hk1 (weight_nonneg hR _) (by positivity)
        simpa only [htwo] using weight_mul_le hR ((2 : ℝ[X]).comp z) z
      _ ≤ A ^ (k + 2) := by
        rw [pow_succ, pow_succ, pow_succ]
        have h : 2 * b * A + 1 ≤ A * A := by dsimp [A]; nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h (pow_nonneg (le_trans zero_le_one hA) k)]

lemma chebyshev_abs_le_one (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(Polynomial.Chebyshev.T ℝ k).eval x| ≤ 1 := by
  rw [← Real.cos_arccos hx.1 hx.2, Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

/-- An elementary hyperbolic lower bound for the Chebyshev denominator. -/
lemma chebyshev_denominator (k : ℕ) {m r : ℝ} (hr : 0 < r) (hm : r < m) :
    1 ≤ (Polynomial.Chebyshev.T ℝ k).eval ((m + r) / (m - r)) ∧
    Real.exp ((k : ℝ) * Real.sqrt (r / m)) / 2 ≤
      (Polynomial.Chebyshev.T ℝ k).eval ((m + r) / (m - r)) := by
  let q := Real.sqrt (r / m)
  have hm0 : 0 < m := lt_trans hr hm
  have hq0 : 0 < q := Real.sqrt_pos.2 (div_pos hr hm0)
  have hq1 : q < 1 := by
    dsimp [q]
    apply (Real.sqrt_lt' (by norm_num)).2
    simpa using (div_lt_one hm0).2 hm
  have hq2 : q ^ 2 = r / m := Real.sq_sqrt (le_of_lt (div_pos hr hm0))
  let h := (1 + q) / (1 - q)
  have hh0 : 0 < h := div_pos (by linarith) (by linarith)
  have hlog : q ≤ Real.log h := by
    dsimp [h]
    rw [Real.log_div (by linarith) (by linarith)]
    have hp := Real.log_nonneg (show 1 ≤ 1 + q by linarith)
    have hn := Real.log_le_sub_one_of_pos (show 0 < 1 - q by linarith)
    linarith
  have harg : (m + r) / (m - r) = Real.cosh (Real.log h) := by
    rw [Real.cosh_eq, Real.exp_log hh0, Real.exp_neg, Real.exp_log hh0]
    dsimp [h]
    have hqm : m * q ^ 2 = r := by nlinarith [((eq_div_iff (ne_of_gt hm0)).1 hq2)]
    have hmr : m - r ≠ 0 := by linarith
    have hqm1 : 1 - q ≠ 0 := by linarith
    have hqp1 : 1 + q ≠ 0 := by linarith
    field_simp [hmr, hqm1, hqp1]
    nlinarith
  rw [harg, Polynomial.Chebyshev.T_real_cosh]
  constructor
  · exact Real.one_le_cosh _
  · have he : Real.exp ((k : ℝ) * q) ≤ Real.exp ((k : ℤ) * Real.log h) := by
      apply Real.exp_le_exp.2
      norm_cast
      exact mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k)
    rw [Real.cosh_eq]
    exact (div_le_div_of_nonneg_right he (by norm_num)).trans
      (by have := Real.exp_pos (-((k : ℤ) * Real.log h)); linarith)

lemma rootPoly_eval_nat {r x : ℕ} (hx0 : 1 ≤ x) (hxr : x ≤ r) :
    (rootPoly r).eval (x : ℝ) = 0 := by
  have hx : x - 1 ∈ Finset.range r := Finset.mem_range.2 (by omega)
  have hx1 : x - 1 + 1 = x := by omega
  simp only [rootPoly, Polynomial.eval_prod, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  apply Finset.prod_eq_zero hx
  have hxne : (x : ℝ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  have he : ((x - 1 : ℕ) : ℝ) + 1 = x := by exact_mod_cast hx1
  rw [he, inv_mul_cancel₀ hxne, sub_self]

lemma rootPoly_weight {R : ℝ} (hR : 0 ≤ R) (r : ℕ) :
    weight R (rootPoly r) ≤ (1 + R) ^ r := by
  unfold rootPoly
  apply (weight_prod_le hR _ _).trans
  calc
    _ ≤ ∏ _j ∈ Finset.range r, (1 + R) := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact weight_nonneg hR _
      · intro j hj
        apply (weight_sub_le hR _ _).trans
        simp only [weight_one]
        apply add_le_add_right
        apply (weight_mul_le hR _ _).trans
        rw [weight_C, weight_X, abs_of_nonneg (by positivity)]
        exact mul_le_of_le_one_left hR (inv_le_one_of_one_le₀ (by norm_num))
    _ = (1 + R) ^ r := by simp

lemma rootPoly_abs_eval {m x : ℝ} (hm : 1 ≤ m) (hx0 : 0 ≤ x) (hxm : x ≤ m) (r : ℕ) :
    |(rootPoly r).eval x| ≤ m ^ r := by
  simp only [rootPoly, eval_prod, eval_sub, eval_one, eval_mul, eval_C, eval_X,
    Finset.abs_prod]
  calc
    _ ≤ ∏ _j ∈ Finset.range r, m := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro j hj
      have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by norm_num
      have hj0 : 0 < (j : ℝ) + 1 := by positivity
      have hv0 : 0 ≤ ((j : ℝ) + 1)⁻¹ * x := by positivity
      have hv : ((j : ℝ) + 1)⁻¹ * x ≤ m :=
        (mul_le_of_le_one_left hx0 (inv_le_one_of_one_le₀ hj1)).trans hxm
      exact abs_le.2 ⟨by linarith, by linarith⟩
    _ = m ^ r := by simp

lemma rootPoly_degree (r : ℕ) : (rootPoly r).natDegree ≤ r := by
  apply (natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _j ∈ Finset.range r, 1 := by
      apply Finset.sum_le_sum
      intro j hj
      apply (natDegree_sub_le _ _).trans
      apply max_le (by simp)
      exact (natDegree_C_mul_le _ _).trans (by simp)
    _ = r := by simp

lemma scalePoly_eval (r m x : ℝ) :
    (scalePoly r m).eval x = (m + r - 2 * x) / (m - r) := by
  simp only [scalePoly, eval_sub, eval_C, eval_mul, eval_X]
  ring

lemma scalePoly_zero (r m : ℝ) :
    (scalePoly r m).eval 0 = (m + r) / (m - r) := by rw [scalePoly_eval]; ring

lemma scalePoly_interval {r m x : ℝ} (hrm : r < m) (hrx : r ≤ x) (hxm : x ≤ m) :
    (scalePoly r m).eval x ∈ Set.Icc (-1) 1 := by
  rw [scalePoly_eval]
  constructor
  · apply (le_div_iff₀ (sub_pos.2 hrm)).2
    linarith
  · apply (div_le_one (sub_pos.2 hrm)).2
    linarith

lemma scalePoly_degree (r m : ℝ) : (scalePoly r m).natDegree ≤ 1 := by
  apply (natDegree_sub_le _ _).trans
  simp only [natDegree_C, Nat.zero_max]
  exact (natDegree_C_mul_le _ _).trans (by simp)

lemma scalePoly_weight {R r m : ℝ} (hR : 0 ≤ R) (hr : 1 ≤ r) (hm : 2 * r ≤ m) :
    weight R (scalePoly r m) ≤ 3 + 2 * R := by
  have hmr : 1 ≤ m - r := by linarith
  have hmr0 : 0 < m - r := by linarith
  have hconst0 : 0 ≤ (m + r) / (m - r) := div_nonneg (by linarith) hmr0.le
  have hconst : (m + r) / (m - r) ≤ 3 := by
    apply (div_le_iff₀ hmr0).2
    linarith
  have hlin0 : 0 ≤ 2 / (m - r) := by positivity
  have hlin : 2 / (m - r) ≤ 2 := by
    apply (div_le_iff₀ hmr0).2
    linarith
  apply (weight_sub_le hR _ _).trans
  apply (add_le_add_right (weight_mul_le hR _ _) _).trans
  simp only [weight_C, weight_X, abs_of_nonneg hconst0, abs_of_nonneg hlin0]
  exact add_le_add hconst (mul_le_mul_of_nonneg_right hlin hR)

/-- Finite degree, coefficient, normalization, and decay bounds for the approximating polynomial. -/
lemma approxPoly_bounds {r m k : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (hr : 1 ≤ r) (hm : 2 * r ≤ m)
    (hk : 4 * (r : ℝ) * Real.log m ≤ (k : ℝ) * Real.sqrt ((r : ℝ) / m)) :
    (approxPoly r m k).natDegree ≤ r + k ∧
    weight R (approxPoly r m k) ≤ (1 + R) ^ r * (7 + 4 * R) ^ k ∧
    (approxPoly r m k).eval 0 = 1 ∧
    ∀ x : ℕ, 1 ≤ x → x ≤ m →
      |(approxPoly r m k).eval (x : ℝ)| ≤ 2 * Real.exp (-(3 * (r : ℝ) * Real.log m)) := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hmR : 2 * (r : ℝ) ≤ m := by exact_mod_cast hm
  have hrm : (r : ℝ) < m := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hden := chebyshev_denominator k (lt_of_lt_of_le zero_lt_one hrR) hrm
  let den := (Polynomial.Chebyshev.T ℝ k).eval (((m : ℝ) + r) / (m - r))
  have hd1 : 1 ≤ den := hden.1
  have hd0 : 0 < den := lt_of_lt_of_le zero_lt_one hd1
  have hdb : Real.exp (4 * (r : ℝ) * Real.log m) / 2 ≤ den :=
    (div_le_div_of_nonneg_right (Real.exp_le_exp.2 hk) (by norm_num)).trans hden.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply natDegree_mul_le.trans
    apply add_le_add
    · exact (natDegree_C_mul_le _ _).trans (rootPoly_degree r)
    · apply natDegree_comp_le.trans
      simpa only [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast, mul_one] using
        Nat.mul_le_mul_left k (scalePoly_degree r m)
  · apply (weight_mul_le hR _ _).trans
    apply mul_le_mul _ _ (weight_nonneg hR _) (by positivity)
    · apply (weight_mul_le hR _ _).trans
      rw [weight_C, abs_of_pos (inv_pos.2 hd0)]
      exact (mul_le_of_le_one_left (weight_nonneg hR _) (inv_le_one_of_one_le₀ hd1)).trans
        (rootPoly_weight hR r)
    · apply (weight_chebyshev hR _ k).trans
      apply pow_le_pow_left₀ (by have := weight_nonneg hR (scalePoly r m); linarith)
      have := scalePoly_weight hR hrR hmR
      linarith
  · simp only [approxPoly, eval_mul, eval_C, rootPoly_eval_zero, mul_one,
      eval_comp, scalePoly_zero]
    exact inv_mul_cancel₀ (ne_of_gt hd0)
  · intro x hx0 hxm
    by_cases hxr : x ≤ r
    · simp only [approxPoly, eval_mul, rootPoly_eval_nat hx0 hxr, mul_zero, zero_mul,
        abs_zero]
      positivity
    have hrx : (r : ℝ) ≤ x := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hxr))
    have hxmR : (x : ℝ) ≤ m := by exact_mod_cast hxm
    have hroot := rootPoly_abs_eval (show (1 : ℝ) ≤ m by linarith)
      (Nat.cast_nonneg x) hxmR r
    have hcheb := chebyshev_abs_le_one k (scalePoly_interval hrm hrx hxmR)
    have heq : (approxPoly r m k).eval (x : ℝ) =
        den⁻¹ * (rootPoly r).eval (x : ℝ) *
          (Polynomial.Chebyshev.T ℝ k).eval ((scalePoly r m).eval (x : ℝ)) := by
      simp only [approxPoly, eval_mul, eval_C, eval_comp, den]
    rw [heq, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hd0)]
    apply (mul_le_mul (mul_le_mul_of_nonneg_left hroot (le_of_lt (inv_pos.2 hd0)))
      hcheb (abs_nonneg _) (by positivity)).trans
    rw [mul_one, inv_mul_eq_div]
    apply (div_le_iff₀ hd0).2
    have epos : 0 ≤ 2 * Real.exp (-(3 * (r : ℝ) * Real.log m)) := by positivity
    apply (le_trans ?_ (mul_le_mul_of_nonneg_left hdb epos))
    rw [show 2 * Real.exp (-(3 * (r : ℝ) * Real.log m)) *
        (Real.exp (4 * (r : ℝ) * Real.log m) / 2) =
        Real.exp ((r : ℝ) * Real.log m) by
      rw [show 2 * Real.exp (-(3 * (r : ℝ) * Real.log m)) *
          (Real.exp (4 * (r : ℝ) * Real.log m) / 2) =
          Real.exp (-(3 * (r : ℝ) * Real.log m)) *
            Real.exp (4 * (r : ℝ) * Real.log m) by ring,
        ← Real.exp_add]
      congr 1
      ring]
    rw [Real.exp_nat_mul, Real.exp_log hm0]

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Backward ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma conjugate_finset_sum {A ι : Type*} [CStarAlgebra A] (U : A) (s : Finset ι) (f : ι → A) :
    conjugate U (∑ i ∈ s, f i) = ∑ i ∈ s, conjugate U (f i) := by
  simp only [conjugate,Finset.mul_sum,Finset.sum_mul]

lemma Count.polynomial_norm_le {N : ℕ} (D : Count N) (p : Polynomial ℝ) :
    ‖D.polynomial p‖ ≤ weight N p := by
  classical
  rw [D.polynomial_eq_sum]
  apply (norm_sum_le _ _).trans
  change (∑ k ∈ p.support, ‖p.coeff k • D.operator^k‖) ≤ ∑ k ∈ p.support, |p.coeff k| *(N:ℝ)^k
  apply Finset.sum_le_sum
  intro k _
  rw [norm_smul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) D.operator_norm_le _)

lemma Count.monomial_transition {N : ℕ} (D M : Count N) (U : Operator N) (r μ δ : ℝ)
    (hδ : 0 ≤ δ) (k : ℕ) (hk : (k:ℝ) ≤ μ)
    (hA : ∀ A : Count N, (A.support.card:ℝ) ≤ μ →
      ‖M.high r*conjugate U A.zero*M.zero‖ ≤ δ) :
    ‖M.high r*conjugate U (D.operator^k)*M.zero‖ ≤ (N:ℝ)^k*δ := by
  rw [D.operator_monomials,conjugate_list_sum,← List.sum_map_mul_left,← List.sum_map_mul_right]
  have h := list_norm_sum_le_const (selectionSets D.support k)
    (fun F => M.high r*conjugate U ((D.flip D.support).restrict F).zero*M.zero) δ (by
      intro F hF
      apply hA
      have hc := ((D.flip D.support).restrict_support_card F).trans (selectionSets_card _ _ F hF)
      exact (show (((D.flip D.support).restrict F).support.card:ℝ) ≤ k by exact_mod_cast hc).trans hk)
  apply h.trans
  rw [selectionSets_length]
  apply mul_le_mul_of_nonneg_right _ hδ
  exact_mod_cast Nat.pow_le_pow_left (show D.support.card ≤ N by simpa using Finset.card_le_univ D.support) k

lemma Count.polynomial_transition {N : ℕ} (D M : Count N) (U : Operator N)
    (p : Polynomial ℝ) (r μ δ : ℝ) (hδ : 0 ≤ δ) (hp : (p.natDegree:ℝ) ≤ μ)
    (hA : ∀ A : Count N, (A.support.card:ℝ) ≤ μ →
      ‖M.high r*conjugate U A.zero*M.zero‖ ≤ δ) :
    ‖M.high r*conjugate U (D.polynomial p)*M.zero‖ ≤ weight N p*δ := by
  classical
  rw [D.polynomial_eq_sum,conjugate_finset_sum,Finset.mul_sum,Finset.sum_mul]
  simp only [conjugate_smul,mul_smul_comm,smul_mul_assoc]
  apply (norm_sum_le _ _).trans
  change (∑ k ∈ p.support, ‖p.coeff k • (M.high r*conjugate U (D.operator^k)*M.zero)‖) ≤
    (∑ k ∈ p.support, |p.coeff k| *(N:ℝ)^k)*δ
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  rw [norm_smul,Real.norm_eq_abs]
  rw [mul_assoc (|p.coeff k|) ((N:ℝ)^k)]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply D.monomial_transition M U r μ δ hδ k _ hA
  exact (show (k:ℝ) ≤ p.natDegree by exact_mod_cast Polynomial.le_natDegree_of_mem_supp k hk).trans hp

lemma Count.backward_finite {N : ℕ} (M D : Count N) (U : Operator N) (hU : U ∈ unitary (Operator N))
    (p : Polynomial ℝ) (r b A B E T : ℝ)
    (hx : ‖M.high r*conjugate U (D.polynomial p)*M.zero‖ ≤ A)
    (hp : ‖D.polynomial p‖ ≤ B)
    (he : ‖(D.zero-D.polynomial p)*D.low b‖ ≤ E)
    (ht : ‖D.high b*star U*M.zero*U*D.zero‖ ≤ T) :
    ‖M.high r*conjugate U D.zero*M.zero‖^2 ≤ A+E+(1+B)*T := by
  let Q := conjugate U D.zero
  let X := conjugate U (D.polynomial p)
  let W := conjugate U (D.high b)
  have hQ : IsStarProjection Q := conjugate_projection hU D.zero_projection
  have hQn : ‖Q‖ ≤ 1 := IsStarProjection.norm_le _ hQ
  have hXn : ‖X‖ ≤ B := by
    change ‖U*D.polynomial p*star U‖ ≤ B
    rw [norm_unitary_conjugate hU]
    exact hp
  have hn : ‖Q-X‖ ≤ 1+B := (norm_sub_le _ _).trans (add_le_add hQn hXn)
  have hlow : ‖(Q-X)*(1-W)‖ ≤ E := by
    have heq : (Q-X)*(1-W) = conjugate U ((D.zero-D.polynomial p)*D.low b) := by
      change (conjugate U D.zero-conjugate U (D.polynomial p))*(1-conjugate U (D.high b)) = _
      simp only [Count.low,conjugate_mul hU,conjugate_sub,conjugate_one hU]
    rw [heq]
    change ‖U*((D.zero-D.polynomial p)*D.low b)*star U‖ ≤ E
    rw [norm_unitary_conjugate hU]
    exact he
  have htail : ‖W*M.zero*Q‖ ≤ T := by
    have heq : W*M.zero*Q = conjugate U (D.high b*star U*M.zero*U*D.zero) := by
      dsimp only [W,Q,conjugate]
      simp only [mul_assoc]
    rw [heq]
    change ‖U*(D.high b*star U*M.zero*U*D.zero)*star U‖ ≤ T
    rw [norm_unitary_conjugate hU]
    exact ht
  have herr : ‖(Q-X)*M.zero*Q‖ ≤ E+(1+B)*T := by
    apply (norm_split_bound (Q-X) W M.zero Q (IsStarProjection.norm_le _ M.zero_projection) hQn).trans
    exact add_le_add hlow (mul_le_mul hn htail (norm_nonneg _) ((norm_nonneg _).trans hn))
  have hsquare := projection_transition_square (M.high r) M.zero Q X
    (M.high_projection r) M.zero_projection hQ
  exact hsquare.trans ((add_le_add hx herr).trans_eq (by ring))

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Asymptotics ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Filter Asymptotics

namespace QAC

/-- Strict exponent gaps absorb every fixed multiplicative constant. -/
lemma eventually_power_le {s t : ℝ} (hst : s < t) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ s ≤ (N : ℝ) ^ t := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (t - s)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.2 hst)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop C, eventually_ge_atTop 1] with N hN h1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    C * (N : ℝ) ^ s ≤ (N : ℝ) ^ (t - s) * (N : ℝ) ^ s :=
      mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ t := by rw [← Real.rpow_add hN0]; congr 1; ring

/-- The same strict gap absorbs a logarithm, with no change to the exponent. -/
lemma eventually_power_log_le {s t : ℝ} (hst : s < t) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ s * Real.log N ≤ (N : ℝ) ^ t := by
  have h := ((isLittleO_log_rpow_atTop (sub_pos.2 hst)).const_mul_left C).bound
    (c := 1) zero_lt_one
  have hn := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [hn, eventually_ge_atTop 1] with N hN h1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbound : C * Real.log N ≤ (N : ℝ) ^ (t - s) := by
    have hN' : |C * Real.log N| ≤ (N : ℝ) ^ (t - s) := by
      simpa only [Real.norm_eq_abs, one_mul,
        abs_of_nonneg (Real.rpow_nonneg hN0.le (t - s))] using hN
    exact (le_abs_self _).trans hN'
  calc
    C * (N : ℝ) ^ s * Real.log N = (C * Real.log N) * (N : ℝ) ^ s := by ring
    _ ≤ (N : ℝ) ^ (t - s) * (N : ℝ) ^ s :=
      mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ t := by rw [← Real.rpow_add hN0]; congr 1; ring

lemma ceil_rpow_bounds {N : ℕ} {a : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a) :
    (N : ℝ) ^ a ≤ (⌈(N : ℝ) ^ a⌉₊ : ℝ) ∧
    (⌈(N : ℝ) ^ a⌉₊ : ℝ) ≤ 2 * (N : ℝ) ^ a := by
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp1 : 1 ≤ (N : ℝ) ^ a := Real.one_le_rpow h1 ha
  constructor
  · exact Nat.le_ceil _
  · have h := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg N) a)
    linarith

lemma ceil_rpow_log {N : ℕ} {b : ℝ} (hN : 2 ≤ N) (hb : 0 ≤ b) :
    Real.log (⌈(N : ℝ) ^ b⌉₊ : ℝ) ≤ (b + 1) * Real.log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hbounds := ceil_rpow_bounds (show 1 ≤ N by omega) hb
  have hceil0 : (0 : ℝ) < ⌈(N : ℝ) ^ b⌉₊ :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hbounds.1
  calc
    _ ≤ Real.log (2 * (N : ℝ) ^ b) := Real.log_le_log hceil0 hbounds.2
    _ = Real.log 2 + b * Real.log N := by
      rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hN0 _)),
        Real.log_rpow hN0]
    _ ≤ (b + 1) * Real.log N := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2
      nlinarith

lemma approx_weight_exp {N r k : ℕ} {v u : ℝ} (hN : 6 ≤ N)
    (hsum : (r : ℝ) + k ≤ 4 * (N : ℝ) ^ v)
    (hcostN : 8 * (N : ℝ) ^ v * Real.log N ≤ (N : ℝ) ^ u) :
    (1 + (N : ℝ)) ^ r * (7 + 4 * (N : ℝ)) ^ k ≤ Real.exp ((N : ℝ) ^ u) := by
  have hN6R : (6 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlog1 : Real.log (1 + (N : ℝ)) ≤ 2 * Real.log N := by
    have h := Real.log_le_log (by positivity : 0 < 1 + (N : ℝ))
      (show 1 + (N : ℝ) ≤ (N : ℝ) ^ 2 by nlinarith only [hN6R])
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hlog2 : Real.log (7 + 4 * (N : ℝ)) ≤ 2 * Real.log N := by
    have h := Real.log_le_log (by positivity : 0 < 7 + 4 * (N : ℝ))
      (show 7 + 4 * (N : ℝ) ≤ (N : ℝ) ^ 2 by nlinarith only [hN6R])
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hcost : (r : ℝ) * Real.log (1 + (N : ℝ)) +
      (k : ℝ) * Real.log (7 + 4 * (N : ℝ)) ≤ (N : ℝ) ^ u := by
    calc
      _ ≤ (r : ℝ) * (2 * Real.log N) + (k : ℝ) * (2 * Real.log N) :=
        add_le_add (mul_le_mul_of_nonneg_left hlog1 (Nat.cast_nonneg r))
          (mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg k))
      _ ≤ 8 * (N : ℝ) ^ v * Real.log N := by
        nlinarith only [mul_le_mul_of_nonneg_right hsum hlogN]
      _ ≤ _ := hcostN
  calc
    _ = Real.exp ((r : ℝ) * Real.log (1 + (N : ℝ)) +
        (k : ℝ) * Real.log (7 + 4 * (N : ℝ))) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log (by positivity), Real.exp_log (by positivity)]
    _ ≤ _ := Real.exp_le_exp.2 hcost

lemma approx_decay_exp {r : ℕ} {m z : ℝ} (hr : 1 ≤ r) (hm : 1 ≤ Real.log m)
    (hz : z ≤ r) : 2 * Real.exp (-(3 * (r : ℝ) * Real.log m)) ≤ Real.exp (-z) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  calc
    _ ≤ Real.exp 1 * Real.exp (-(3 * (r : ℝ) * Real.log m)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      have := Real.add_one_le_exp 1
      norm_num at this ⊢
      exact this
    _ = Real.exp (1 - 3 * (r : ℝ) * Real.log m) := by rw [← Real.exp_add]; congr 1
    _ ≤ _ := by
      apply Real.exp_le_exp.2
      nlinarith only [mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg r), hz, hr1]

lemma ceil_approx_condition {N : ℕ} {a b v : ℝ} (hN : 2 ≤ N)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hv : 0 ≤ v)
    (hkN : (8 * (b + 1)) * (N : ℝ) ^ ((a + b) / 2) * Real.log N ≤ (N : ℝ) ^ v) :
    4 * (⌈(N : ℝ) ^ a⌉₊ : ℝ) * Real.log (⌈(N : ℝ) ^ b⌉₊ : ℝ) ≤
      (⌈(N : ℝ) ^ v⌉₊ : ℝ) *
        Real.sqrt ((⌈(N : ℝ) ^ a⌉₊ : ℝ) / (⌈(N : ℝ) ^ b⌉₊ : ℝ)) := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let r := ⌈(N : ℝ) ^ a⌉₊
  let m := ⌈(N : ℝ) ^ b⌉₊
  let k := ⌈(N : ℝ) ^ v⌉₊
  have hrap := ceil_rpow_bounds hN1 ha
  have hmbp := ceil_rpow_bounds hN1 hb
  have hkvp := ceil_rpow_bounds hN1 hv
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hmbp.1
  have hlogm := ceil_rpow_log hN hb
  have hsquare : ((N : ℝ) ^ ((a + b) / 2)) ^ 2 = (N : ℝ) ^ a * (N : ℝ) ^ b := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    congr 1
    ring
  have hsqrt : Real.sqrt ((r : ℝ) * m) ≤ 2 * (N : ℝ) ^ ((a + b) / 2) := by
    apply (Real.sqrt_le_left (by positivity)).2
    have hmul := mul_le_mul hrap.2 hmbp.2 (Nat.cast_nonneg m)
      (by positivity : 0 ≤ 2 * (N : ℝ) ^ a)
    rw [mul_pow, hsquare]
    nlinarith only [hmul]
  have hksqrt : 4 * Real.sqrt ((r : ℝ) * m) * Real.log m ≤ (k : ℝ) := by
    calc
      _ ≤ 4 * (2 * (N : ℝ) ^ ((a + b) / 2)) * ((b + 1) * Real.log N) := by
        apply mul_le_mul _ hlogm (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hsqrt (by norm_num)
      _ = (8 * (b + 1)) * (N : ℝ) ^ ((a + b) / 2) * Real.log N := by ring
      _ ≤ (N : ℝ) ^ v := hkN
      _ ≤ (k : ℝ) := hkvp.1
  have hsqrtmul : Real.sqrt ((r : ℝ) * m) * Real.sqrt ((r : ℝ) / m) = r := by
    rw [← Real.sqrt_mul (by positivity), show (r : ℝ) * m * ((r : ℝ) / m) = (r : ℝ)^2 by
      field_simp, Real.sqrt_sq (Nat.cast_nonneg r)]
  calc
    _ = (4 * Real.sqrt ((r : ℝ) * m) * Real.log m) * Real.sqrt ((r : ℝ) / m) := by
      calc
        _ = 4 * Real.log m * (Real.sqrt ((r : ℝ) * m) * Real.sqrt ((r : ℝ) / m)) := by
          rw [hsqrtmul]; ring
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hksqrt (Real.sqrt_nonneg _)

/-- Polynomial approximation uniform in `N`, including `b > 1`. -/
theorem polynomial_approximation {a b u : ℝ} (ha : 0 < a) (hab : a < b)
    (hu : (a + b) / 2 < u) :
    ∀ᶠ N : ℕ in atTop, ∃ p : ℝ[X],
      (p.natDegree : ℝ) ≤ (N : ℝ) ^ u ∧ weight N p ≤ Real.exp ((N : ℝ) ^ u) ∧
      p.eval 0 = 1 ∧ ∀ x : ℕ, 1 ≤ x → x ≤ ⌈(N : ℝ) ^ b⌉₊ →
        |p.eval (x : ℝ)| ≤ Real.exp (-((N : ℝ) ^ a)) := by
  let g := (a + b) / 2
  let v := (g + u) / 2
  have hgu : g < u := hu
  have hag : a < g := by dsimp [g]; linarith
  have hgv : g < v := by dsimp [v]; linarith only [hgu]
  have hvu : v < u := by dsimp [v]; linarith only [hgu]
  have hav : a < v := lt_trans hag hgv
  have hb : 0 < b := lt_trans ha hab
  have hv : 0 < v := lt_trans ha hav
  have hexp : ∀ᶠ N : ℕ in atTop, Real.exp 1 ≤ (N : ℝ) ^ b :=
    ((tendsto_rpow_atTop hb).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop 6, eventually_power_le hab 4,
    eventually_power_le hvu 4, eventually_power_log_le hvu 8,
    eventually_power_log_le hgv (8 * (b + 1)), hexp] with N hN habN hdegN hcostN hkN hexpN
  have hN1 : 1 ≤ N := by omega
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  let r := ⌈(N : ℝ) ^ a⌉₊
  let m := ⌈(N : ℝ) ^ b⌉₊
  let k := ⌈(N : ℝ) ^ v⌉₊
  have hrap := ceil_rpow_bounds hN1 ha.le
  have hmbp := ceil_rpow_bounds hN1 hb.le
  have hkvp := ceil_rpow_bounds hN1 hv.le
  have hr1 : (1 : ℝ) ≤ r := (Real.one_le_rpow hN1R ha.le).trans hrap.1
  have hr : 1 ≤ r := by exact_mod_cast hr1
  have hm : 2 * r ≤ m := by
    have h : 2 * (r : ℝ) ≤ m := by nlinarith only [hrap.2, hmbp.1, habN]
    exact_mod_cast h
  have hlogm1 : 1 ≤ Real.log (m : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 1) (hexpN.trans hmbp.1)
    simpa only [Real.log_exp] using h
  have hk := ceil_approx_condition (show 2 ≤ N by omega) ha.le hb.le hv.le hkN
  obtain ⟨hdeg, hweight, hzero, hdecay⟩ := approxPoly_bounds (Nat.cast_nonneg N) hr hm hk
  have havN : (N : ℝ) ^ a ≤ (N : ℝ) ^ v :=
    Real.rpow_le_rpow_of_exponent_le hN1R hav.le
  have hsum : (r : ℝ) + k ≤ 4 * (N : ℝ) ^ v := by
    nlinarith only [hrap.2, hkvp.2, havN]
  refine ⟨approxPoly r m k, ?_, ?_, hzero, ?_⟩
  · exact (by exact_mod_cast hdeg : ((approxPoly r m k).natDegree : ℝ) ≤ (r : ℝ) + k).trans
      (hsum.trans hdegN)
  · exact hweight.trans (approx_weight_exp hN hsum hcostN)
  · intro x hx0 hxm
    exact (hdecay x hx0 hxm).trans (approx_decay_exp hr hlogm1 hrap.1)

lemma eventually_two_powers_le {a b t : ℝ} (ha : a < t) (hb : b < t) :
    ∀ᶠ N : ℕ in atTop, (N:ℝ)^a + (N:ℝ)^b ≤ (N:ℝ)^t := by
  filter_upwards [eventually_power_le ha 2,eventually_power_le hb 2] with N haN hbN
  linarith

/-- Every fixed coefficient and prefactor is absorbed by the strict power gaps. -/
lemma eventually_exp_power_gap {s u v : ℝ} (hs : s < v) (hu : u < v) (hv : 0 < v)
    (C ε D K : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, C * Real.exp (K*(N:ℝ)^u - (N:ℝ)^v) ≤
      ε * Real.exp (-(D*(N:ℝ)^s)) := by
  filter_upwards [eventually_power_le hv (3*Real.log (C/ε)),
    eventually_power_le hu (3*K),eventually_power_le hs (3*D)] with N h0 h1 h2
  simp only [Real.rpow_zero,mul_one] at h0
  calc
    _ = ε * Real.exp (Real.log (C/ε) + K*(N:ℝ)^u - (N:ℝ)^v) := by
      rw [show Real.log (C/ε) + K*(N:ℝ)^u - (N:ℝ)^v =
        Real.log (C/ε) + (K*(N:ℝ)^u - (N:ℝ)^v) by ring, Real.exp_add,
        Real.exp_log (div_pos hC hε)]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [h0,h1,h2])) hε.le

lemma ceil_power_log_bound {N : ℕ} {a : ℝ} (hN : 2 ≤ N) (ha : 0 ≤ a) :
    ((⌈(N:ℝ)^a⌉₊:ℝ)+1)*Real.log (N+1) ≤ 6*(N:ℝ)^a*Real.log N := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN2 : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hp : 1 ≤ (N:ℝ)^a := Real.one_le_rpow hN1 ha
  have hc := (ceil_rpow_bounds (show 1 ≤ N by omega) ha).2
  have hl : Real.log (N+1) ≤ 2*Real.log N := by
    calc
      _ ≤ Real.log ((N:ℝ)^2) := Real.log_le_log (by positivity) (by nlinarith only [hN2])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hlog : 0 ≤ Real.log (N+1) := Real.log_nonneg (by linarith only [hN1])
  calc
    _ ≤ (3*(N:ℝ)^a)*Real.log (N+1) := mul_le_mul_of_nonneg_right (by linarith) hlog
    _ ≤ (3*(N:ℝ)^a)*(2*Real.log N) := mul_le_mul_of_nonneg_left hl (by positivity)
    _ = _ := by ring

lemma eventually_pattern_cost {a s v : ℝ} (ha : 0 ≤ a) (hav : a < v) (hsv : s < v) :
    ∀ᶠ N : ℕ in atTop,
      (N+1:ℝ)^(⌈(N:ℝ)^a⌉₊+1) * Real.exp (-((N:ℝ)^v)) ≤ Real.exp (-((N:ℝ)^s)) := by
  filter_upwards [eventually_power_log_le hav 12,eventually_power_le hsv 2,
    eventually_ge_atTop 2] with N hcost htarget hN
  have hc := ceil_power_log_bound hN ha
  have hp : (N+1:ℝ)^(⌈(N:ℝ)^a⌉₊+1) =
      Real.exp (((⌈(N:ℝ)^a⌉₊:ℝ)+1)*Real.log (N+1)) := by
    rw [show (⌈(N:ℝ)^a⌉₊:ℝ)+1 = ((⌈(N:ℝ)^a⌉₊+1:ℕ):ℝ) by push_cast; rfl,
      Real.exp_nat_mul,Real.exp_log (by positivity)]
  rw [hp,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith only [hc,hcost,htarget]

lemma eventually_backward_cost {s a u w t : ℝ} (hs : 0 ≤ s) (hsa : s < a)
    (hau : a < u) (huw : u < w) (hwt : w < t) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp ((N:ℝ)^u-(N:ℝ)^w) + Real.exp (-((N:ℝ)^a)) +
        (1+Real.exp ((N:ℝ)^u))*Real.exp (-((N:ℝ)^t)) ≤ Real.exp (-2*(N:ℝ)^s) := by
  have ha : 0 < a := lt_of_le_of_lt hs hsa
  have hsu := hsa.trans hau
  have hsw := hsu.trans huw
  have hst := hsw.trans hwt
  filter_upwards [eventually_exp_power_gap hsw huw (ha.trans (hau.trans huw)) 1 (1/3) 2 1
      zero_lt_one (by norm_num),
    eventually_exp_power_gap hsa ha ha 1 (1/3) 2 0 zero_lt_one (by norm_num),
    eventually_exp_power_gap hst (huw.trans hwt) (lt_of_le_of_lt hs hst) 2 (1/3) 2 1
      (by norm_num) (by norm_num)] with N h1 h2 h3
  simp only [one_mul,zero_mul,zero_sub] at h1 h2 h3
  have hnon : 1 ≤ Real.exp ((N:ℝ)^u) := Real.one_le_exp (by positivity)
  have hlast : (1+Real.exp ((N:ℝ)^u))*Real.exp (-((N:ℝ)^t)) ≤
      2*Real.exp ((N:ℝ)^u-(N:ℝ)^t) := by
    rw [Real.exp_sub,div_eq_mul_inv,← Real.exp_neg]
    nlinarith only [hnon,Real.exp_pos (-((N:ℝ)^t))]
  have hlast' := hlast.trans h3
  have heq : -(2*(N:ℝ)^s) = -2*(N:ℝ)^s := by ring
  rw [heq] at h1 h2 hlast'
  linarith only [h1,h2,hlast']

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.ScaleInduction ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

namespace QAC

/-- Finite scale bootstrap, stated for the uniform bound relation.  This is a
pure real-arithmetic induction and contains no operator-theoretic assumption. -/
theorem finite_scale_induction (B : ℝ → ℝ → Prop)
    (large : ∀ s t, 0 ≤ s → s < t → 1 < t → B s t)
    (backstep : ∀ s t a b u w, 0 ≤ s → s < a → a < u → u < w → w < t → t < b →
      (a + b) / 2 < u → B t b → B s t) :
    ∀ s t, 0 ≤ s → s < t → B s t := by
  intro s t hs hst
  by_cases ht : 1 < t
  · exact large s t hs hst ht
  have ht1 : t ≤ 1 := le_of_not_gt ht
  let g := t - s
  have hg : 0 < g := sub_pos.2 hst
  have hg1 : g ≤ 1 := by dsimp [g]; linarith
  let K := ⌈2 / g⌉₊
  let η := g ^ 2 / 100
  have hη : 0 < η := by dsimp [η]; positivity
  have hKlow : 2 / g ≤ (K : ℝ) := Nat.le_ceil _
  have hKhigh : (K : ℝ) < 2 / g + 1 := Nat.ceil_lt_add_one (by positivity)
  have hKg : (K : ℝ) * g ≥ 2 := (div_le_iff₀ hg).1 hKlow
  have hKg' : (K : ℝ) * g < 2 + g := by
    have := (lt_div_iff₀ hg).1 (show (K : ℝ) < (2 + g) / g by
      convert hKhigh using 1
      field_simp)
    exact this
  have hKη : 3 * (K : ℝ) * η < g / 2 := by
    dsimp [η]
    nlinarith only [hg, hg1, hKg', mul_lt_mul_of_pos_right hKg' hg]
  let T : ℕ → ℝ := fun i => t + (i : ℝ) * g - 3 * η * i * (i + 1) / 2
  let S : ℕ → ℝ := fun i => T i - (g - 3 * i * η)
  have hT0 : T 0 = t := by simp [T]
  have hS0 : S 0 = s := by simp [S, T, g]
  have hTS : ∀ i, S (i + 1) = T i := by
    intro i
    dsimp [S, T]
    push_cast
    ring
  have hgap : ∀ i ≤ K, g / 2 < T i - S i := by
    intro i hi
    have hi' : (i : ℝ) ≤ K := by exact_mod_cast hi
    dsimp [S]
    nlinarith only [hKη, mul_le_mul_of_nonneg_right hi' hη.le]
  have hTstep : ∀ i, T (i + 1) = 2 * T i - S i - 3 * η := by
    intro i
    dsimp [S, T]
    push_cast
    ring
  have hSnonneg : ∀ i ≤ K, 0 ≤ S i := by
    intro i
    induction i with
    | zero => intro _; simpa only [hS0] using hs
    | succ i ih =>
      intro hi
      have hiK : i ≤ K := by omega
      rw [hTS]
      have := hgap i hiK
      have := ih hiK
      linarith
  have hstep : ∀ i < K, T i + g / 2 < T (i + 1) := by
    intro i hi
    have h := hgap (i + 1) (by omega)
    rw [hTS] at h
    linarith
  have hTbound : ∀ i ≤ K, t + i * (g / 2) ≤ T i := by
    intro i
    induction i with
    | zero => intro _; simp [hT0]
    | succ i ih =>
      intro hi
      have h := hstep i (by omega)
      have h' := ih (by omega)
      push_cast
      linarith
  have hTK : 1 < T K := by
    have h := hTbound K le_rfl
    have ht0 : 0 < t := lt_of_le_of_lt hs hst
    nlinarith only [h, hKg, ht0]
  have hηgap : ∀ i ≤ K, 3 * η < T i - S i := by
    intro i hi
    have h := hgap i hi
    dsimp [η]
    nlinarith only [h, hg, hg1, mul_le_mul_of_nonneg_left hg1 hg.le]
  have hB : ∀ i ≤ K, B (S i) (T i) := by
    intro i hi
    induction hi using Nat.decreasingInduction with
    | self =>
      exact large (S K) (T K) (hSnonneg K le_rfl)
        (by have := hgap K le_rfl; linarith) hTK
    | of_succ i hi ih =>
      have hiK : i ≤ K := by omega
      have h := hηgap i hiK
      have htstep := hTstep i
      have hnext : B (T i) (T (i + 1)) := by simpa only [hTS] using ih
      apply backstep (S i) (T i) (S i + η / 2) (T (i + 1))
        (T i - η) (T i - η / 2) (hSnonneg i hiK)
      · linarith
      · linarith
      · linarith
      · linarith
      · linarith
      · linarith
      · exact hnext
  simpa only [hS0, hT0] using hB 0 (Nat.zero_le K)

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.DepthZero ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma rankOne_sandwich (v w : Bit → ℂ) :
    rankOne v * rankOne w * rankOne v =
      Complex.normSq (star w ⬝ᵥ v) • rankOne v := by
  ext i j
  simp only [rankOne, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
    Complex.real_smul, ← Complex.mul_conj, dotProduct, Pi.star_apply,
    Fin.sum_univ_two, map_add, map_mul, Complex.conj_conj, Complex.star_def]
  ring

open scoped MatrixOrder in
lemma rankOne_markov_le (v w : Bit → ℂ)
    (hv : ∑ b, Complex.normSq (v b) = 1)
    (hw : ∑ b, Complex.normSq (w b) = 1) :
    rankOne v * rankOne w * ((2:ℝ) • (1 - rankOne v) + rankOne v) * rankOne w * rankOne v ≤ 1 := by
  let P := rankOne v
  let Q := rankOne w
  let c : ℝ := Complex.normSq (star w ⬝ᵥ v)
  have hP := rankOne_projection hv
  have hQ := rankOne_projection hw
  have hPQ : P * Q * P = c • P := rankOne_sandwich v w
  have hid : P * Q * ((2:ℝ) • (1 - P) + P) * Q * P = (2*c-c^2) • P := by
    have h1 : P * Q * Q * P = c • P := by rw [mul_assoc P Q Q, hQ.isIdempotentElem.eq, hPQ]
    have h2 : P * Q * P * Q * P = c^2 • P := by
      rw [hPQ, smul_mul_assoc, smul_mul_assoc, hPQ, smul_smul, pow_two]
    calc
      _ = (2:ℝ) • (P * Q * Q * P) - P * Q * P * Q * P := by
        simp only [two_smul, mul_add, add_mul, mul_sub, sub_mul, mul_one]
        abel
      _ = _ := by rw [h1, h2, smul_smul, ← sub_smul]
  change P * Q * ((2:ℝ) • (1 - P) + P) * Q * P ≤ 1
  rw [hid]
  apply sub_nonneg.mp
  have heq : 1 - (2*c-c^2) • P = (1-P) + (1-c)^2 • P := by
    have hc : (1-c)^2 = 1-(2*c-c^2) := by ring
    simp only [hc, sub_smul, one_smul]
    abel
  rw [heq]
  exact add_nonneg hP.one_sub.nonneg (smul_nonneg (sq_nonneg _) hP.nonneg)

lemma tensorMatrix_pattern_scale {N : ℕ} (M : Count N) (F : Finset (Fin N))
    (hF : F ⊆ M.support) (z : ℝ) :
    tensorMatrix (fun i => if i ∈ M.support then
      (if i ∈ F then z • (1 - rankOne (M.vector i)) else rankOne (M.vector i)) else 1) =
      z ^ F.card • M.pattern F := by
  classical
  have heq : (fun i => if i ∈ M.support then
      (if i ∈ F then z • (1 - rankOne (M.vector i)) else rankOne (M.vector i)) else 1) =
      (fun i => (if i ∈ F then z else 1) •
        (if i ∈ M.support then (if i ∈ F then 1 - rankOne (M.vector i) else rankOne (M.vector i)) else 1)) := by
    funext i
    by_cases hiF : i ∈ F
    · simp [hiF, hF hiF]
    · simp [hiF]
  rw [heq, tensorMatrix_smul]
  congr 1
  simp

/-- The generating function of the mismatch spectral partition. -/
lemma Count.spectral_power_tensor {N : ℕ} (M : Count N) (z : ℝ) :
    (∑ F ∈ M.support.powerset, z ^ F.card • M.pattern F) =
      tensorMatrix (fun i => if i ∈ M.support then
        z • (1 - rankOne (M.vector i)) + rankOne (M.vector i) else 1) := by
  classical
  rw [← tensorMatrix_sum_patterns M.support]
  apply Finset.sum_congr rfl
  intro F hF
  exact (tensorMatrix_pattern_scale M F (Finset.mem_powerset.mp hF) z).symm

open scoped MatrixOrder in
lemma Count.high_le_generating {N : ℕ} (M : Count N) (r : ℝ) :
    M.high r ≤ (2 : ℝ) ^ (-r) •
      (∑ F ∈ M.support.powerset, (2 : ℝ)^F.card • M.pattern F) := by
  classical
  rw [Finset.smul_sum]
  unfold Count.high
  apply Finset.sum_le_sum
  intro F _
  rw [smul_smul]
  by_cases hr : r ≤ F.card
  · rw [ite_eq_left hr]
    nth_rw 1 [← one_smul ℝ (M.pattern F)]
    apply smul_le_smul_of_nonneg_right _ (M.pattern_projection F).nonneg
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    exact Real.one_le_rpow (by norm_num) (by linarith)
  · rw [ite_eq_right hr]
    exact smul_nonneg (by positivity) (M.pattern_projection F).nonneg

lemma Count.site_projection {N : ℕ} (M : Count N) (i : Fin N) : IsStarProjection (M.site i) := by
  classical
  dsimp [Count.site]
  split_ifs with hi
  · exact rankOne_projection (M.normalized i hi)
  · exact IsStarProjection.one _

open scoped MatrixOrder in
lemma projection_markov_nonneg {A : Type*} [Ring A] [StarRing A] [PartialOrder A]
    [StarOrderedRing A] [Algebra ℝ A] [IsOrderedModule ℝ A]
    (P Q : A) (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    0 ≤ P * Q * ((2:ℝ) • (1-P)+P) * Q * P := by
  have hn : 0 ≤ (2:ℝ) • (1-P)+P :=
    add_nonneg (smul_nonneg (by norm_num) hP.one_sub.nonneg) hP.nonneg
  simpa only [star_mul, hQ.isSelfAdjoint.star_eq, hP.isSelfAdjoint.star_eq, mul_assoc] using
    star_right_conjugate_nonneg hn (P*Q)

lemma projection_markov_self {A : Type*} [Ring A] [Module ℝ A] [SMulCommClass ℝ A A]
    {P : A} (hP : IsIdempotentElem P) : P * ((2:ℝ) • (1-P)+P) * P = P := by
  have hc : P * (1-P) = 0 := by rw [mul_sub,mul_one,hP.eq,sub_self]
  simp only [mul_add, mul_smul_comm, hc, smul_zero, zero_add, hP.eq]

open scoped MatrixOrder in
lemma Count.markov_site_le {N : ℕ} (M D : Count N) (i : Fin N) :
    M.site i * D.site i * ((2:ℝ) • (1-M.site i)+M.site i) * D.site i * M.site i ≤ 1 := by
  classical
  by_cases hM : i ∈ M.support
  · by_cases hD : i ∈ D.support
    · simp only [Count.site, ite_eq_left hM, ite_eq_left hD]
      exact rankOne_markov_le _ _ (M.normalized i hM) (D.normalized i hD)
    · simp only [Count.site, ite_eq_left hM, ite_eq_right hD, mul_one]
      rw [projection_markov_self (rankOne_projection (M.normalized i hM)).isIdempotentElem]
      exact (rankOne_projection (M.normalized i hM)).le_one
  · have heq : M.site i = 1 := ite_eq_right hM
    rw [heq]
    simp only [sub_self, smul_zero, zero_add, one_mul, mul_one,
      (D.site_projection i).isIdempotentElem.eq]
    exact (D.site_projection i).le_one

lemma Count.generating_eq_sites {N : ℕ} (M : Count N) :
    (∑ F ∈ M.support.powerset, (2 : ℝ)^F.card • M.pattern F) =
      tensorMatrix (fun i => (2:ℝ) • (1-M.site i)+M.site i) := by
  classical
  rw [M.spectral_power_tensor]
  congr 1
  funext i
  by_cases hi : i ∈ M.support <;> simp [Count.site,hi]

open scoped MatrixOrder in
lemma Count.markov_sandwich_le {N : ℕ} (M D : Count N) :
    M.zero * D.zero * (∑ F ∈ M.support.powerset, (2 : ℝ)^F.card • M.pattern F) *
      D.zero * M.zero ≤ 1 := by
  rw [M.generating_eq_sites]
  change tensorMatrix M.site * tensorMatrix D.site *
    tensorMatrix (fun i => (2:ℝ) • (1-M.site i)+M.site i) *
    tensorMatrix D.site * tensorMatrix M.site ≤ 1
  simp only [tensorMatrix_mul]
  exact tensorMatrix_le_one _
    (fun i => projection_markov_nonneg _ _ (M.site_projection i) (D.site_projection i))
    (fun i => M.markov_site_le D i)

open scoped MatrixOrder in
lemma Count.depth_zero_square {N : ℕ} (M D : Count N) (r : ℝ) :
    ‖M.high r * D.zero * M.zero‖^2 ≤ (2 : ℝ)^(-r) := by
  let A := M.high r * D.zero * M.zero
  have heq : star A * A = M.zero * D.zero * M.high r * D.zero * M.zero := by
    dsimp [A]
    simp only [star_mul, M.zero_projection.isSelfAdjoint.star_eq,
      D.zero_projection.isSelfAdjoint.star_eq, (M.high_projection r).isSelfAdjoint.star_eq]
    simp only [mul_assoc]
    rw [← mul_assoc (M.high r) (M.high r), (M.high_projection r).isIdempotentElem.eq]
  have h := star_right_conjugate_le_conjugate (M.high_le_generating r) (M.zero * D.zero)
  simp only [star_mul, M.zero_projection.isSelfAdjoint.star_eq,
    D.zero_projection.isSelfAdjoint.star_eq, mul_smul_comm, smul_mul_assoc] at h
  have hbound : star A * A ≤ (2 : ℝ)^(-r) • (1 : Operator N) := by
    rw [heq]
    exact le_trans (by simpa only [mul_assoc] using h)
      (smul_le_smul_of_nonneg_left (M.markov_sandwich_le D) (by positivity))
  have hn := (CStarAlgebra.norm_le_iff_le_algebraMap (star A * A) (by positivity : 0 ≤ (2:ℝ)^(-r)) (star_mul_self_nonneg A)).2
    (by simpa only [Algebra.algebraMap_eq_smul_one] using hbound)
  simpa only [CStarRing.norm_star_mul_self, pow_two] using hn

lemma Count.depth_zero_bound {N : ℕ} (M D : Count N) (r : ℝ) :
    ‖M.high r * D.zero * M.zero‖ ≤ Real.exp (-(Real.log 2 / 2) * r) := by
  have hsq := M.depth_zero_square D r
  have heq : Real.exp (-(Real.log 2 / 2) * r)^2 = (2:ℝ)^(-r) := by
    rw [pow_two, ← Real.exp_add, Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  rw [← heq] at hsq
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp hsq

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Localization ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

namespace QAC

lemma uniform_zero {s t : ℝ} (hst : s < t) : UniformLocalization 0 s t := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_power_le hst (2/Real.log 2)] with N hN
  intro U hU M D
  obtain ⟨L,rfl⟩ := hU
  have hb := M.depth_zero_bound (D.rotate L) ((N:ℝ)^t)
  rw [D.rotate_zero L] at hb
  apply hb.trans
  apply Real.exp_le_exp.mpr
  have h := (div_le_iff₀ hlog).mp (show 2*(N:ℝ)^s/Real.log 2 ≤ (N:ℝ)^t by
    simpa only [div_mul_eq_mul_div] using hN)
  nlinarith only [h]

lemma uniform_large (d : ℕ) {s t : ℝ} (ht : 1 < t) : UniformLocalization d s t := by
  filter_upwards [eventually_power_le ht 2,Filter.eventually_ge_atTop 1] with N hN hN1
  intro U _ M D
  have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlimit : (N:ℝ) < (N:ℝ)^t := by rw [Real.rpow_one] at hN; linarith only [hN,hNpos]
  rw [M.high_eq_zero hlimit,zero_mul,zero_mul,norm_zero]
  exact (Real.exp_pos _).le

lemma uniform_low_propagation {d : ℕ}
    (ih : ∀ s t : ℝ, 0 ≤ s → s < t → UniformLocalization d s t)
    {a s t : ℝ} (ha : 0 ≤ a) (_hs : 0 ≤ s) (hat : a < t) (hst : s < t) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ U : Operator N, IsCircuit d U → ∀ M D : Count N,
      ‖M.high ((N:ℝ)^t)*conjugate U D.zero*M.low ((N:ℝ)^a)‖ ≤ Real.exp (-((N:ℝ)^s)) := by
  obtain ⟨v,hv,hvt⟩ := exists_between (max_lt hat hst)
  have hav : a < v := (le_max_left _ _).trans_lt hv
  have hsv : s < v := (le_max_right _ _).trans_lt hv
  obtain ⟨q,hvq,hqt⟩ := exists_between hvt
  filter_upwards [ih v q (ha.trans hav.le) hvq,
    eventually_two_powers_le hqt hat,eventually_pattern_cost ha hav hsv,
    Filter.eventually_ge_atTop 1] with N hN hp hc hN1
  intro U hU M D
  exact (M.low_propagation_bound (conjugate U D.zero) hN1 (Real.exp_pos _).le hp
    (fun K => hN U hU K D)).trans hc

lemma uniform_small_support {d : ℕ}
    (ih : ∀ s t : ℝ, 0 ≤ s → s < t → UniformLocalization d s t)
    {u w t : ℝ} (hu : 0 ≤ u) (_hw : 0 ≤ w) (hut : u < t) (hwt : w < t) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ U : Operator N, IsCircuit (d+1) U → ∀ M A : Count N,
      (A.support.card:ℝ) ≤ (N:ℝ)^u →
      ‖M.high ((N:ℝ)^t)*conjugate U A.zero*M.zero‖ ≤ Real.exp (-((N:ℝ)^w)) := by
  obtain ⟨v,hv,hvt⟩ := exists_between (max_lt hut hwt)
  have huv : u < v := (le_max_left _ _).trans_lt hv
  have hwv : w < v := (le_max_right _ _).trans_lt hv
  have hv0 : 0 < v := lt_of_le_of_lt hu huv
  obtain ⟨r₁,hvr₁,hr₁t⟩ := exists_between hvt
  obtain ⟨r₂,hr₁r₂,hr₂t⟩ := exists_between hr₁t
  filter_upwards [ih v r₁ hv0.le hvr₁,
    uniform_low_propagation ih (hv0.le.trans hvr₁.le) hv0.le hr₁r₂ (hvr₁.trans hr₁r₂),
    uniform_low_propagation ih (hv0.le.trans (hvr₁.trans hr₁r₂).le) hv0.le hr₂t hvt,
    eventually_exp_power_gap hwv huv hv0 3 1 1 (Real.log 9) (by norm_num) zero_lt_one] with N h₁ h₂ h₃ hc
  intro U hU M A hA
  obtain ⟨V,R,L,hV,rfl⟩ := hU
  have hb := small_support_layer_bound V hV.mem_unitary R L M A (Real.exp_pos _).le
    (fun D => h₁ V hV M D) (fun D => h₂ V hV M D) (fun D => h₃ V hV M D)
  have hcost : (9:ℝ)^A.support.card ≤ Real.exp (Real.log 9*(N:ℝ)^u) := by
    calc
      _ = Real.exp (Real.log 9*(A.support.card:ℝ)) := by
        rw [mul_comm,Real.exp_nat_mul,Real.exp_log (by norm_num)]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hA (Real.log_nonneg (by norm_num)))
  apply hb.trans
  calc
    _ ≤ Real.exp (Real.log 9*(N:ℝ)^u)*(3*Real.exp (-((N:ℝ)^v))) :=
      mul_le_mul_of_nonneg_right hcost (by positivity)
    _ = 3*Real.exp (Real.log 9*(N:ℝ)^u-(N:ℝ)^v) := by rw [sub_eq_add_neg,Real.exp_add]; ring
    _ ≤ _ := by simpa only [one_mul] using hc

lemma uniform_backward {d : ℕ}
    (ih : ∀ s t : ℝ, 0 ≤ s → s < t → UniformLocalization d s t)
    {s t a b u w : ℝ} (hs : 0 ≤ s) (hsa : s < a) (hau : a < u)
    (huw : u < w) (hwt : w < t) (htb : t < b) (hdegree : (a+b)/2 < u)
    (hnext : UniformLocalization (d+1) t b) : UniformLocalization (d+1) s t := by
  have ha : 0 < a := lt_of_le_of_lt hs hsa
  have hab : a < b := hau.trans (huw.trans (hwt.trans htb))
  filter_upwards [polynomial_approximation ha hab hdegree,
    uniform_small_support ih (ha.trans hau).le (ha.trans (hau.trans huw)).le (huw.trans hwt) hwt,
    hnext,eventually_backward_cost hs hsa hau huw hwt] with N hp hsmall htail hcost
  intro U hU M D
  obtain ⟨p,hdeg,hweight,hzero,hp⟩ := hp
  have hx := D.polynomial_transition M U p ((N:ℝ)^t) ((N:ℝ)^u) (Real.exp (-((N:ℝ)^w)))
    (Real.exp_pos _).le hdeg (fun A hA => hsmall U hU M A hA)
  have hx' : ‖M.high ((N:ℝ)^t)*conjugate U (D.polynomial p)*M.zero‖ ≤
      Real.exp ((N:ℝ)^u-(N:ℝ)^w) := by
    apply hx.trans
    calc
      _ ≤ Real.exp ((N:ℝ)^u)*Real.exp (-((N:ℝ)^w)) :=
        mul_le_mul_of_nonneg_right hweight (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  have herr := D.polynomial_error_low p (Real.exp_pos _).le hzero (fun k hk hkb =>
    hp k hk (by exact_mod_cast hkb.le.trans (Nat.le_ceil ((N:ℝ)^b))))
  have hinv := htail (star U) hU.star_mem D M
  simp only [conjugate,star_star,mul_assoc] at hinv
  have hsq := M.backward_finite D U hU.mem_unitary p ((N:ℝ)^t) ((N:ℝ)^b)
    (Real.exp ((N:ℝ)^u-(N:ℝ)^w)) (Real.exp ((N:ℝ)^u))
    (Real.exp (-((N:ℝ)^a))) (Real.exp (-((N:ℝ)^t))) hx'
    ((D.polynomial_norm_le p).trans hweight) herr (by simpa only [mul_assoc] using hinv)
  have hsq' := hsq.trans hcost
  have heq : Real.exp (-2*(N:ℝ)^s) = (Real.exp (-((N:ℝ)^s)))^2 := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [heq] at hsq'
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp hsq'

/-- Uniform localization, proved by depth and finite scale induction. -/
theorem uniform_localization : ∀ d s t, 0 ≤ s → s < t → UniformLocalization d s t := by
  intro d
  induction d with
  | zero => intro s t _ hst; exact uniform_zero hst
  | succ d ih =>
    apply finite_scale_induction (UniformLocalization (d+1))
    · intro s t _ _ ht; exact uniform_large (d+1) ht
    · intro s t a b u w hs hsa hau huw hwt htb hdegree hnext
      exact uniform_backward ih hs hsa hau huw hwt htb hdegree hnext

/-- Uniform product-projection localization in the Euclidean operator norm. -/
theorem localization : LocalizationStatement := by
  intro d s t hs hst
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp (uniform_localization d s t hs hst)
  refine ⟨N₀,?_⟩
  intro N hN U hU M D
  simpa only [conjugate,mul_assoc] using hN₀ N hN U hU M D

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

lemma rankOne_minus (x y : Bit) :
    rankOne minusVector x y = if x=y then (1/2:ℂ) else -(1/2:ℂ) := by
  have hh : (halfScale:ℂ)^2 = 1/2 := by rw [← Complex.ofReal_pow,halfScale_sq]; norm_num
  fin_cases x <;> fin_cases y <;> simp [rankOne,minusVector,← pow_two,hh]

lemma toffoliCount_entry {N : ℕ} (c : Finset (Fin N)) (t : Fin N) (ht : t ∉ c)
    (x y : Word N) :
    (toffoliCount c t).zero x y =
      if (∀ i, i ≠ t → x i=y i) ∧ (∀ i ∈ c, y i=1) then
        rankOne minusVector (x t) (y t) else 0 := by
  classical
  let a : Fin N → QubitOperator := fun i =>
    if i ∈ insert t c then rankOne (if i=t then minusVector else basisVector 1) else 1
  change (∏ i, a i (x i) (y i)) = _
  have hat : a t (x t) (y t) = rankOne minusVector (x t) (y t) := by simp [a]
  have hf : ∀ i, i ≠ t → a i (x i) (y i) =
      if x i=y i ∧ (i ∈ c → y i=1) then 1 else 0 := by
    intro i hi
    by_cases hic : i ∈ c
    · simp only [a,Finset.mem_insert,hic,or_true,ite_true,ite_eq_right hi,rankOne_basis,true_implies]
      congr 1
      apply propext
      constructor
      · rintro ⟨hx,hy⟩; exact ⟨hx.trans hy.symm,hy⟩
      · rintro ⟨hxy,hy⟩; exact ⟨hxy.trans hy,hy⟩
    · simp [a,hi,hic,Matrix.one_apply]
  split_ifs with h
  · rw [Finset.prod_eq_single t]
    · exact hat
    · intro i _ hit
      rw [hf i hit,ite_eq_left ⟨h.1 i hit,h.2 i⟩]
    · simp
  · obtain h | h := not_and_or.mp h
    · push Not at h
      obtain ⟨i,hit,hxy⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hf i hit]; simp [hxy])
    · push Not at h
      obtain ⟨i,hic,hy⟩ := h
      have hit : i ≠ t := fun h => ht (h ▸ hic)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hf i hit]; simp [hic,hy])

lemma toffoli_reflection {N : ℕ} (c : Finset (Fin N)) (t : Fin N) (ht : t ∉ c) :
    Gate.matrix (.toffoli c t ht) = reflect (toffoliCount c t) := by
  classical
  ext x y
  change (if x=Gate.toffoliWord c t y then (1:ℂ) else 0) =
    (if x=y then 1 else 0) - 2*(toffoliCount c t).zero x y
  rw [toffoliCount_entry c t ht]
  by_cases hctrl : ∀ i ∈ c, y i=1
  · have hw : Gate.toffoliWord c t y = Function.update y t (1-y t) := by
      exact ite_eq_left hctrl
    rw [hw]
    by_cases hrest : ∀ i, i ≠ t → x i=y i
    · have hxy : x=y ↔ x t=y t := by
        constructor
        · intro h; exact congrFun h t
        · intro h; funext i; by_cases hi : i=t
          · simpa [hi] using h
          · exact hrest i hi
      have hxu : x=Function.update y t (1-y t) ↔ x t=1-y t := by
        constructor
        · intro h; simpa using congrFun h t
        · intro h; funext i; by_cases hi : i=t
          · simpa [hi] using h
          · simpa [Function.update_of_ne hi] using hrest i hi
      have hboth : (∀ i, i ≠ t → x i=y i) ∧ (∀ i ∈ c, y i=1) := ⟨hrest,hctrl⟩
      rw [ite_eq_left hboth,rankOne_minus]
      simp only [hxy,hxu]
      generalize x t = a, y t = b
      fin_cases a <;> fin_cases b <;> norm_num
    · have hxy : x ≠ y := by intro h; apply hrest; intro i _; exact congrFun h i
      have hxu : x ≠ Function.update y t (1-y t) := by
        intro h; apply hrest; intro i hi
        simpa [Function.update_of_ne hi] using congrFun h i
      simp [hrest,hxy,hxu]
  · have hw : Gate.toffoliWord c t y = y := by exact ite_eq_right hctrl
    rw [hw]
    simp [hctrl]

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Physical ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

namespace QAC

lemma local_gate_matrix {N : ℕ} (q : Fin N) (u : Matrix.unitaryGroup Bit ℂ) :
    Gate.matrix (.local q u) = localMatrix (singleLocal q u) := by
  classical
  change tensorMatrix (fun i => if i=q then (u:QubitOperator) else 1) =
    tensorMatrix (fun i => ((singleLocal q u i):QubitOperator))
  congr 1
  funext i
  unfold singleLocal
  split_ifs <;> rfl

lemma reflectList_rotate {N : ℕ} (l : List (Count N)) (L : LocalLayer N) :
    reflectList (l.map (fun A => A.rotate L)) = conjugate (localMatrix L) (reflectList l) := by
  induction l with
  | nil => simp [reflectList,conjugate_one (localMatrix_unitary L)]
  | cons A l ih =>
    simp only [List.map_cons,reflectList,List.prod_cons,List.map_map] at ih ⊢
    rw [conjugate_mul (localMatrix_unitary L),← ih]
    congr 1
    simp only [reflect,conjugate_sub,conjugate_one (localMatrix_unitary L),conjugate_smul]
    rw [A.rotate_zero L]
    rfl

lemma reflectList_rotate_commute {N : ℕ} (l : List (Count N)) (L : LocalLayer N) :
    localMatrix L*reflectList l = reflectList (l.map (fun A => A.rotate L))*localMatrix L := by
  rw [reflectList_rotate,conjugate]
  simp only [mul_assoc,Unitary.star_mul_self_of_mem (localMatrix_unitary L),mul_one]

lemma normalCounts_support {N : ℕ} (l : List (Gate N)) :
    ∀ A ∈ normalCounts l, ∃ g ∈ l, A.support=g.support := by
  induction l with
  | nil => simp [normalCounts]
  | cons g l ih =>
    cases g with
    | «local» q u =>
      intro A hA
      obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hA
      obtain ⟨g,hg,hBg⟩ := ih B hB
      exact ⟨g,List.mem_cons_of_mem _ hg,hBg⟩
    | toffoli c t ht =>
      intro A hA
      rcases List.mem_cons.mp hA with rfl | hA
      · exact ⟨.toffoli c t ht,List.mem_cons_self ..,rfl⟩
      · obtain ⟨g,hg,hAg⟩ := ih A hA
        exact ⟨g,List.mem_cons_of_mem _ hg,hAg⟩

lemma normalCounts_disjoint {N : ℕ} (l : List (Gate N))
    (hl : l.Pairwise (fun A B => Disjoint A.support B.support)) :
    (normalCounts l).Pairwise (fun A B => Disjoint A.support B.support) := by
  induction l with
  | nil => simp [normalCounts]
  | cons g l ih =>
    have hparts := List.pairwise_cons.mp hl
    clear hl
    cases g with
    | «local» q u =>
      exact (ih hparts.2).map (fun A : Count N => A.rotate (singleLocal q u)) (fun _ _ h => h)
    | toffoli c t ht =>
      apply List.pairwise_cons.mpr
      refine ⟨?_,ih hparts.2⟩
      intro A hA
      obtain ⟨g,hg',hAg⟩ := normalCounts_support l A hA
      change Disjoint (Gate.support (.toffoli c t ht)) A.support
      rw [hAg]
      exact hparts.1 g hg'

lemma gateList_normal {N : ℕ} (l : List (Gate N)) :
    (l.map Gate.matrix).prod = reflectList (normalCounts l)*localMatrix (normalLocal l) := by
  induction l with
  | nil => simp [normalCounts,normalLocal,reflectList,localMatrix]
  | cons g l ih =>
    cases g with
    | «local» q u =>
      simp only [List.map_cons,List.prod_cons,normalCounts,normalLocal]
      rw [local_gate_matrix,ih,← mul_assoc,reflectList_rotate_commute,mul_assoc,localMatrix_mul]
    | toffoli c t ht =>
      simp only [List.map_cons,List.prod_cons,normalCounts,normalLocal]
      rw [toffoli_reflection,ih]
      simp only [reflectList,List.map_cons,List.prod_cons,mul_assoc]

lemma physicalLayer_isCircuit {N : ℕ} (P : PhysicalLayer N) :
    IsCircuit 1 (physicalLayerMatrix P) := by
  let R : ReflectionLayer N := ⟨normalCounts P.gates,normalCounts_disjoint _ P.disjoint⟩
  refine ⟨1,R,normalLocal P.gates,?_,?_⟩
  · exact ⟨fun _ => 1,by simp [localMatrix]⟩
  · rw [one_mul,reflectionMatrix_eq]
    exact gateList_normal P.gates

lemma physicalCircuit_isCircuit {N : ℕ} (l : List (PhysicalLayer N)) :
    IsCircuit l.length (physicalCircuitMatrix l) := by
  induction l with
  | nil => exact ⟨fun _ => 1,by simp [physicalCircuitMatrix,localMatrix]⟩
  | cons L l ih =>
    have h := ih.mul (physicalLayer_isCircuit L)
    simpa only [physicalCircuitMatrix,List.map_cons,List.reverse_cons,List.prod_append,
      List.prod_singleton,List.length_cons] using h

lemma IsCircuit.succ {N d : ℕ} {U : Operator N} (hU : IsCircuit d U) : IsCircuit (d+1) U := by
  refine ⟨U,⟨[],by simp⟩,fun _ => 1,hU,?_⟩
  simp [reflectionMatrix,localMatrix]

lemma IsCircuit.mono {N d e : ℕ} {U : Operator N} (hU : IsCircuit d U) (hde : d ≤ e) :
    IsCircuit e U := by
  induction hde with
  | refl => exact hU
  | step h ih => exact ih.succ

lemma IsCircuit.local_mul {N d : ℕ} {U : Operator N} (hU : IsCircuit d U) (L : LocalLayer N) :
    IsCircuit d (localMatrix L*U) := by
  have hL : IsCircuit 0 (localMatrix L) := ⟨L,rfl⟩
  simpa only [Nat.zero_add] using hL.mul hU

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Computational ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

lemma flipWord_involutive {N : ℕ} (F : Finset (Fin N)) : Function.Involutive (flipWord F) := by
  intro z
  funext i
  simp only [flipWord]
  split_ifs
  · generalize z i = b
    fin_cases b <;> decide
  · rfl

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

lemma inputSet_card {n N : ℕ} (hnN : n ≤ N) : (inputSet n N).card=n := by
  rw [inputSet,Fin.card_filter_val_lt,min_eq_right hnN]

lemma bitH_X_H : bitH*bitX*bitH=bitZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bitH,bitX,bitZ,bitSign,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals first | linear_combination 2*halfScale_complex_sq | linear_combination -2*halfScale_complex_sq

lemma inputHadamard_star (n N : ℕ) : star (localMatrix (inputHadamard n N)) =
    localMatrix (inputHadamard n N) := by
  rw [localMatrix_star]
  congr 1
  funext i
  apply Subtype.ext
  by_cases hi : i.val<n
  · simp only [inputHadamard,ite_eq_left hi,Unitary.coe_star,hadamardGate]
    exact bitH_star
  · simp [inputHadamard,hi]

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Ancilla ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma restrict_inputWord {n N : ℕ} (hnN : n ≤ N) (x : Word n) :
    restrictWord hnN (inputWord x)=x := by
  funext i
  simp [restrictWord,inputWord,i.isLt]

lemma inputWord_injective {n N : ℕ} (hnN : n ≤ N) :
    Function.Injective (@inputWord n N) :=
  Function.LeftInverse.injective (restrict_inputWord hnN)

lemma inputWord_valid {n N : ℕ} (x : Word n) : ancillaValid n (@inputWord n N x) := by
  intro i hi
  simp [inputWord,not_lt.mpr hi]

lemma input_restrictWord {n N : ℕ} (hnN : n ≤ N) (z : Word N) (hz : ancillaValid n z) :
    inputWord (restrictWord hnN z)=z := by
  funext i
  by_cases hi : i.val<n
  · simp [inputWord,hi,restrictWord]
  · simp [inputWord,hi,hz i (not_lt.mp hi)]

lemma sum_ancillaValid {n N : ℕ} (hnN : n ≤ N) {α : Type*} [AddCommMonoid α]
    (f : Word N → α) :
    (∑ z : Word N, if ancillaValid n z then f z else 0) = ∑ x : Word n, f (inputWord x) := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun x _ => inputWord x)
  · intro x _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact inputWord_valid x
  · intro x _ y _ hxy
    exact inputWord_injective hnN hxy
  · intro z hz
    refine ⟨restrictWord hnN z,Finset.mem_univ _,?_⟩
    exact input_restrictWord hnN z (Finset.mem_filter.mp hz).2
  · intro x _
    rfl

lemma ancillaProjection_diagonal (n N : ℕ) :
    ancillaProjection n N = Matrix.diagonal (fun z => if ancillaValid n z then 1 else 0) := by
  classical
  have hloc : (fun i : Fin N => if i.val<n then (1 : QubitOperator) else rankOne (basisVector 0)) =
      fun i => Matrix.diagonal (fun b => if n ≤ i.val → b=0 then (1:ℂ) else 0) := by
    funext i
    by_cases hi : i.val<n
    · simp [hi,not_le.mpr hi,Matrix.diagonal_one]
    · simp [hi,not_lt.mp hi,rankOne_basis_diagonal]
  rw [ancillaProjection,hloc,tensorMatrix_diagonal]
  congr 1
  funext z
  by_cases hz : ancillaValid n z
  · rw [ite_eq_left hz]
    apply Finset.prod_eq_one
    intro i _
    exact ite_eq_left (hz i)
  · rw [ite_eq_right hz]
    obtain ⟨i,hi⟩ := not_forall.mp hz
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma inputHadamard_ancilla_flip (n N : ℕ) :
    localMatrix (inputHadamard n N)*(inputFlip n N*ancillaProjection n N)*
      localMatrix (inputHadamard n N) = inputPhase n N*ancillaProjection n N := by
  unfold localMatrix inputFlip inputPhase ancillaProjection
  simp only [tensorMatrix_mul]
  congr 1
  funext i
  by_cases hi : i.val<n
  · simpa only [inputHadamard,ite_eq_left hi,hadamardGate,mul_one] using bitH_X_H
  · simp [inputHadamard,hi]

lemma bitX_entry (a b : Bit) : bitX a b = if a=1-b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> norm_num [bitX]

lemma inputFlip_entry (n N : ℕ) (x y : Word N) :
    inputFlip n N x y = if x=flipWord (inputSet n N) y then 1 else 0 := by
  classical
  have hloc (i : Fin N) : (if i.val<n then bitX else (1:QubitOperator)) (x i) (y i) =
      if x i=flipWord (inputSet n N) y i then 1 else 0 := by
    by_cases hi : i.val<n
    · simp [hi,bitX_entry,flipWord,inputSet]
    · simp [hi,Matrix.one_apply,flipWord,inputSet]
  simp only [inputFlip,tensorMatrix,hloc]
  rw [Fintype.prod_boole]
  simp only [← funext_iff]

lemma ancillaValid_flip {n N : ℕ} (z : Word N) :
    ancillaValid n (flipWord (inputSet n N) z) ↔ ancillaValid n z := by
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro hi
  simp [flipWord,inputSet,not_lt.mpr hi]

lemma inputFlip_mul_ancilla_entry {n N : ℕ} (B : Operator N) (z : Word N) :
    (inputFlip n N*ancillaProjection n N*B) z z =
      if ancillaValid n z then B (flipWord (inputSet n N) z) z else 0 := by
  classical
  rw [ancillaProjection_diagonal]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,inputFlip_entry]
  have hf (y : Word N) : z=flipWord (inputSet n N) y ↔ y=flipWord (inputSet n N) z := by
    constructor
    · intro h; rw [h,flipWord_involutive]
    · intro h; rw [h,flipWord_involutive]
  simp only [hf,ite_mul,zero_mul]
  simp [ancillaValid_flip]

lemma trace_flip_ancilla {n N : ℕ} (hnN : n ≤ N) (B : Operator N) :
    Matrix.trace (inputFlip n N*ancillaProjection n N*B) =
      ∑ x : Word n, B (flipWord (inputSet n N) (inputWord x)) (inputWord x) := by
  simp only [Matrix.trace,Matrix.diag_apply,inputFlip_mul_ancilla_entry]
  exact sum_ancillaValid hnN _

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.ParityTrace ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma bitSign_add (a b : Bit) : bitSign (a+b)=bitSign a*bitSign b := by
  fin_cases a <;> fin_cases b <;> norm_num [bitSign,Fin.add_def,Fin.ext_iff]

lemma bitSign_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Bit) :
    bitSign (∑ i ∈ s, f i)=∏ i ∈ s, bitSign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bitSign]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,Finset.prod_insert hi,bitSign_add,ih]

lemma bitSign_parity {n : ℕ} (x : Word n) : bitSign (parity x)=∏ i, bitSign (x i) :=
  bitSign_finset_sum _ _

lemma sum_bitSign_parity {n : ℕ} (hn : 0<n) : (∑ x : Word n, bitSign (parity x))=0 := by
  simp only [bitSign_parity]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (b : Bit) => bitSign b)]
  exact Finset.prod_eq_zero (Finset.mem_univ (⟨0,hn⟩ : Fin n)) (by norm_num [Fin.sum_univ_two,bitSign])

lemma inputPhase_diagonal (n N : ℕ) :
    inputPhase n N = Matrix.diagonal (fun z => (inputSign n z:ℂ)) := by
  have hloc : (fun i : Fin N => if i.val<n then bitZ else (1:QubitOperator)) =
      fun i => Matrix.diagonal (fun b => ((if i.val<n then bitSign b else 1:ℝ):ℂ)) := by
    funext i
    split_ifs <;> simp [bitZ,Matrix.diagonal_one]
  rw [inputPhase,hloc,tensorMatrix_diagonal]
  congr 1
  funext z
  simp only [inputSign,Complex.ofReal_prod]

lemma inputSign_inputWord {n N : ℕ} (hnN : n ≤ N) (x : Word n) :
    inputSign n (@inputWord n N x)=bitSign (parity x) := by
  classical
  rw [inputSign,bitSign_parity,← Finset.prod_filter]
  symm
  apply Finset.prod_bij (fun i _ => Fin.castLE hnN i)
  · intro i _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Fin.val_castLE]
    exact i.isLt
  · intro i _ j _ hij
    exact Fin.ext (congrArg (fun k : Fin N => k.val) hij)
  · intro i hi
    refine ⟨⟨i.val,(Finset.mem_filter.mp hi).2⟩,Finset.mem_univ _,?_⟩
    rfl
  · intro i _
    simp [inputWord,i.isLt]

lemma trace_phase_ancilla {n N : ℕ} (hnN : n ≤ N) (B : Operator N) :
    Matrix.trace (inputPhase n N*ancillaProjection n N*B) =
      ∑ x : Word n, (bitSign (parity x):ℂ)*B (inputWord x) (inputWord x) := by
  classical
  rw [inputPhase_diagonal,ancillaProjection_diagonal,Matrix.diagonal_mul_diagonal]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.diagonal_mul]
  simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
  rw [sum_ancillaValid hnN]
  simp only [inputSign_inputWord hnN]

/-- Character orthogonality as a finite-dimensional cyclic trace identity. -/
lemma parity_trace_identity {n N : ℕ} (hnN : n ≤ N) (B : Operator N) :
    (∑ x : Word n, (localMatrix (inputHadamard n N)*B*localMatrix (inputHadamard n N))
      (flipWord (inputSet n N) (inputWord x)) (inputWord x)) =
    ∑ x : Word n, (bitSign (parity x):ℂ)*B (inputWord x) (inputWord x) := by
  rw [← trace_flip_ancilla hnN]
  let H := localMatrix (inputHadamard n N)
  let T := inputFlip n N*ancillaProjection n N
  change Matrix.trace (T*(H*B*H)) = _
  calc
    Matrix.trace (T*(H*B*H)) = Matrix.trace ((T*(H*B))*H) :=
      congrArg Matrix.trace (mul_assoc T (H*B) H).symm
    _ = Matrix.trace (H*T*(H*B)) := Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace ((H*T*H)*B) := by rw [mul_assoc (H*T) H B]
    _ = Matrix.trace (inputPhase n N*ancillaProjection n N*B) := by
      rw [show H*T*H=inputPhase n N*ancillaProjection n N from inputHadamard_ancilla_flip n N]
    _ = _ := trace_phase_ancilla hnN B

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Measurement ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma outputZeroCount_diagonal {N : ℕ} (out : Fin N) :
    (outputZeroCount out).zero = Matrix.diagonal (fun z => if z out=0 then 1 else 0) := by
  classical
  have hloc : (fun i : Fin N => if i=out then rankOne (basisVector 0) else (1:QubitOperator)) =
      fun i => Matrix.diagonal (fun b => if i=out → b=0 then (1:ℂ) else 0) := by
    funext i
    by_cases hi : i=out
    · simp [hi,rankOne_basis_diagonal]
    · simp [hi,Matrix.diagonal_one]
  simp only [Count.zero,outputZeroCount,Finset.mem_singleton]
  rw [hloc,tensorMatrix_diagonal]
  congr 1
  funext z
  rw [Fintype.prod_boole]
  simp

lemma born_zero_diagonal {N : ℕ} (W : Operator N) (out : Fin N) (z : Word N) :
    (star W*(outputZeroCount out).zero*W) z z = (outputProbability W out 0 z:ℂ) := by
  classical
  rw [outputZeroCount_diagonal,Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.star_apply,outputProbability,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y out=0
  · simp only [ite_eq_left hy,mul_one,Complex.star_def,← Complex.normSq_eq_conj_mul_self]
  · simp [hy]

lemma total_born_probability {N : ℕ} (W : Operator N) (hW : W ∈ unitary (Operator N))
    (z : Word N) : (∑ y, Complex.normSq (W y z))=1 := by
  apply Complex.ofReal_injective
  have h := congrArg (fun A : Operator N => A z z) (Unitary.star_mul_self_of_mem hW)
  simpa only [Matrix.mul_apply,Matrix.star_apply,Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self,← Complex.ofReal_sum,Matrix.one_apply_eq,Complex.ofReal_one] using h

lemma outputProbability_complement {N : ℕ} (W : Operator N) (hW : W ∈ unitary (Operator N))
    (out : Fin N) (z : Word N) :
    outputProbability W out 0 z+outputProbability W out 1 z=1 := by
  rw [outputProbability,outputProbability,← Finset.sum_add_distrib,← total_born_probability W hW z]
  apply Finset.sum_congr rfl
  intro y _
  generalize y out=b
  fin_cases b <;> simp

lemma success_character_lower {n N : ℕ} (W : Operator N) (hW : W ∈ unitary (Operator N))
    (out : Fin N) (x : Word n) {ε : ℝ} (hsuccess : 1/2+ε ≤ successProbability W out x) :
    ε+bitSign (parity x)/2 ≤
      ((bitSign (parity x):ℂ)*(star W*(outputZeroCount out).zero*W) (inputWord x) (inputWord x)).re := by
  rw [born_zero_diagonal,← Complex.ofReal_mul,Complex.ofReal_re]
  have htotal := outputProbability_complement W hW out (inputWord x)
  change 1/2+ε ≤ outputProbability W out (parity x) (inputWord x) at hsuccess
  generalize hp : parity x=b at hsuccess ⊢
  fin_cases b
  · norm_num [bitSign] at *
    linarith only [hsuccess]
  · norm_num [bitSign] at *
    linarith only [hsuccess,htotal]

/-- The finite Fourier step, with all final garbage summed out by the Born rule. -/
lemma parity_advantage_from_entries {n N : ℕ} (hn : 0<n) (hnN : n ≤ N)
    (W : Operator N) (hW : W ∈ unitary (Operator N)) (out : Fin N) {ε δ : ℝ}
    (hsuccess : ∀ x : Word n, 1/2+ε ≤ successProbability W out x)
    (hentry : ∀ x : Word n,
      ‖(localMatrix (inputHadamard n N)*(star W*(outputZeroCount out).zero*W)*
        localMatrix (inputHadamard n N)) (flipWord (inputSet n N) (inputWord x)) (inputWord x)‖ ≤ δ) :
    ε ≤ δ := by
  let B := star W*(outputZeroCount out).zero*W
  let H := localMatrix (inputHadamard n N)
  have hlow := Finset.sum_le_sum (fun (x : Word n) (_ : x∈Finset.univ) =>
    success_character_lower W hW out x (hsuccess x))
  have hzero := sum_bitSign_parity hn
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ← Finset.sum_div,hzero,zero_div,add_zero] at hlow
  have hupp := Finset.sum_le_sum (fun (x : Word n) (_ : x∈Finset.univ) =>
    (Complex.re_le_norm ((H*B*H) (flipWord (inputSet n N) (inputWord x)) (inputWord x))).trans (hentry x))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hupp
  have heq := congrArg Complex.re (parity_trace_identity hnN B)
  have hsumre (f : Word n → ℂ) : (∑ x, f x).re = ∑ x, (f x).re :=
    map_sum Complex.reAddGroupHom f Finset.univ
  rw [hsumre,hsumre] at heq
  change (∑ x : Word n, ((H*B*H) (flipWord (inputSet n N) (inputWord x)) (inputWord x)).re) =
    ∑ x : Word n, ((bitSign (parity x):ℂ)*B (inputWord x) (inputWord x)).re at heq
  rw [heq] at hupp
  have hc : 0 < (Fintype.card (Word n):ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  exact (mul_le_mul_iff_right₀ hc).mp (hlow.trans hupp)

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Parity ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

namespace QAC

lemma eventually_exp_neg_power_lt {s ε : ℝ} (hs : 0<s) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, Real.exp (-(N:ℝ)^s)<ε := by
  filter_upwards [eventually_power_le hs (-Real.log ε+1)] with N hN
  rw [Real.rpow_zero,mul_one] at hN
  rw [← Real.exp_log hε]
  exact Real.exp_lt_exp.mpr (by linarith only [hN])

lemma polynomial_qubit_threshold {n N : ℕ} {c t : ℝ} (hn : 1≤n)
    (ht : 0≤t) (hct : c*t≤1) (hN : (N:ℝ)≤(n:ℝ)^c) : (N:ℝ)^t≤(n:ℝ) := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  calc
    (N:ℝ)^t ≤ ((n:ℝ)^c)^t := Real.rpow_le_rpow (Nat.cast_nonneg N) hN ht
    _ = (n:ℝ)^(c*t) := (Real.rpow_mul (Nat.cast_nonneg n) c t).symm
    _ ≤ (n:ℝ)^1 := Real.rpow_le_rpow_of_exponent_le hn1 hct
    _ = (n:ℝ) := Real.rpow_one _

lemma hadamard_high_entry_bound {n N : ℕ} (hnN : n≤N) (W : Operator N)
    (out : Fin N) (x : Word n) {r : ℝ} (hr : r≤(n:ℝ)) :
    ‖(localMatrix (inputHadamard n N)*(star W*(outputZeroCount out).zero*W)*
      localMatrix (inputHadamard n N))
      (flipWord (inputSet n N) (inputWord x)) (inputWord x)‖ ≤
    ‖(computationalCount (inputWord x)).high r*(localMatrix (inputHadamard n N)*star W)*
      (outputZeroCount out).zero*star (localMatrix (inputHadamard n N)*star W)*
      (computationalCount (inputWord x)).zero‖ := by
  have hcard : r≤((inputSet n N).card:ℝ) := by simpa only [inputSet_card hnN] using hr
  have hh := high_entry_bound
    (localMatrix (inputHadamard n N)*(star W*(outputZeroCount out).zero*W)*
      localMatrix (inputHadamard n N)) (inputWord x) (inputSet n N) hcard
  simpa only [star_mul,star_star,inputHadamard_star,mul_assoc] using hh

/-- The measured-output parity lower bound, allowing arbitrary final garbage and
all polynomially many initially zero ancillas. No cleanliness assumption is used. -/
theorem parity_lower_bound : ParityStatement := by
  intro d c ε hc hε _
  have hcpos : 0<c := lt_of_lt_of_le zero_lt_one hc
  let t : ℝ := 1/(2*c)
  let s : ℝ := t/2
  have ht : 0<t := by dsimp [t]; positivity
  have hs : 0<s := by dsimp [s]; positivity
  have hst : s<t := by dsimp [s]; linarith only [ht]
  have hct : c*t≤1 := by
    have hceq : c*t=1/2 := by dsimp [t]; field_simp
    rw [hceq]
    norm_num
  obtain ⟨N₀,hN₀⟩ := localization d s t hs.le hst
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.mp (eventually_exp_neg_power_lt hs hε)
  refine ⟨max 1 (max N₀ N₁),?_⟩
  intro n hn N hnN hsize layers hdepth out hsuccess
  have hn1 : 1≤n := (le_max_left 1 (max N₀ N₁)).trans hn
  have hn0 : 0<n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hNN₀ : N₀≤N := (le_trans (le_max_left N₀ N₁) (le_max_right 1 (max N₀ N₁))).trans (hn.trans hnN)
  have hNN₁ : N₁≤N := (le_trans (le_max_right N₀ N₁) (le_max_right 1 (max N₀ N₁))).trans (hn.trans hnN)
  let W := physicalCircuitMatrix layers
  let H := localMatrix (inputHadamard n N)
  have hW : IsCircuit d W := (physicalCircuit_isCircuit layers).mono hdepth
  have hU : IsCircuit d (H*star W) := hW.star_mem.local_mul (inputHadamard n N)
  have hthreshold : (N:ℝ)^t≤(n:ℝ) := polynomial_qubit_threshold hn1 ht.le hct hsize
  have hentry (x : Word n) :
      ‖(H*(star W*(outputZeroCount out).zero*W)*H)
        (flipWord (inputSet n N) (inputWord x)) (inputWord x)‖ ≤ Real.exp (-(N:ℝ)^s) := by
    exact (hadamard_high_entry_bound hnN W out x hthreshold).trans
      (hN₀ N hNN₀ (H*star W) hU (computationalCount (inputWord x)) (outputZeroCount out))
  have hadv := parity_advantage_from_entries hn0 hnN W hW.mem_unitary out hsuccess hentry
  exact (not_le_of_gt (hN₁ N hNN₁)) hadv

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Main ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

namespace QAC

/-- Measured-output parity for a polynomial qubit bound with a fixed multiplicative constant. -/
theorem parity_lower_bound_polynomial_size (d k C : ℕ)
    (_hd : 0 < d) (_hk : 0 < k) (_hC : 0 < C) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ N : ℕ, n ≤ N → N ≤ C * (n + 1) ^ k →
      ∀ layers : List (PhysicalLayer N), layers.length ≤ d →
        ∀ out : Fin N, ∃ x : Word n,
          successProbability (physicalCircuitMatrix layers) out x < (2 : ℝ) / 3 := by
  classical
  obtain ⟨n₀, h₀⟩ := parity_lower_bound d ((k + 1 : ℕ) : ℝ) (1 / 6)
    (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)) (by norm_num) (by norm_num)
  refine ⟨max n₀ (max 1 (C * 2 ^ k)), ?_⟩
  intro n hn N hnN hN layers hdepth out
  rcases max_le_iff.mp hn with ⟨hn₀, hnrest⟩
  rcases max_le_iff.mp hnrest with ⟨hn1, hCn⟩
  have hpoly : N ≤ n ^ (k + 1) := by
    calc
      N ≤ C * (n + 1) ^ k := hN
      _ ≤ C * (2 * n) ^ k :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) k)
      _ = (C * 2 ^ k) * n ^ k := by rw [mul_pow, Nat.mul_assoc]
      _ ≤ n * n ^ k := Nat.mul_le_mul_right (n ^ k) hCn
      _ = n ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]
  have hsize : (N : ℝ) ≤ (n : ℝ) ^ ((k + 1 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hpoly
  have hnot := h₀ n hn₀ N hnN hsize layers hdepth out
  push Not at hnot
  norm_num at hnot
  exact hnot

end QAC

end

end OAI

-- ---- mission target ----
open OAI OAI.QAC
open scoped BigOperators
open scoped BigOperators Topology
open Polynomial Filter Asymptotics

theorem solution (d k C : ℕ)
    (_hd : 0 < d) (_hk : 0 < k) (_hC : 0 < C) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ N : ℕ, n ≤ N → N ≤ C * (n + 1) ^ k →
      ∀ layers : List (PhysicalLayer N), layers.length ≤ d →
        ∀ out : Fin N, ∃ x : Word n,
          successProbability (physicalCircuitMatrix layers) out x < (2 : ℝ) / 3 := by
  first
    | exact OAI.QAC.parity_lower_bound_polynomial_size d k C _hd _hk _hC
    | exact OAI.QAC.parity_lower_bound_polynomial_size
    | (apply OAI.QAC.parity_lower_bound_polynomial_size <;> assumption)
    | (intros; apply OAI.QAC.parity_lower_bound_polynomial_size <;> assumption)
