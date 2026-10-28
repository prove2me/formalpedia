-- Prove2me | solution 1 for OAI.CriticalSK.fixedBulkDeficit_bounds_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:03:32.66302+00:00
-- url     : https://prove2.me/submissions/5a60aef9-54ea-49aa-9885-bfb90421c972

import Mathlib
import Definitions.Def_OAIQ074C000

section
-- module Solutions.OAIQ074_CM.Compat
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_GaussianMatrices
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace
open Module
namespace CriticalSK


section

open scoped NNReal

section Upper

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

@[simp] lemma upperRead_upperWrite (a : UpperEntry ι → ℝ) :
    upperRead (upperWrite a) = a := by
  funext p
  exact dite_eq_left p.2

end Upper

open scoped BigOperators

end

open scoped BigOperators

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_PathEnergy
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

namespace CriticalSK

lemma path_energy_identity (n : ℕ) (c u : ℕ → ℝ) (hc : c n = 0) :
    2 * (∑ i ∈ Finset.range (n + 1), u i ^ 2) -
      2 * (∑ i ∈ Finset.range n, c i * u i * u (i + 1)) =
    (∑ i ∈ Finset.range n, c i * (u (i + 1) - u i) ^ 2) +
      ∑ i ∈ Finset.range (n + 1),
        (2 - c i - if i = 0 then 0 else c (i - 1)) * u i ^ 2 := by
  have hl : (∑ i ∈ Finset.range (n + 1),
      (if i = 0 then (0 : ℝ) else c (i - 1)) * u i ^ 2) =
      ∑ i ∈ Finset.range n, c i * u (i + 1) ^ 2 := by
    rw [Finset.sum_range_succ']
    simp
  have hr : (∑ i ∈ Finset.range (n + 1), c i * u i ^ 2) =
      ∑ i ∈ Finset.range n, c i * u i ^ 2 := by
    rw [Finset.sum_range_succ, hc, zero_mul, add_zero]
  have hg : (∑ i ∈ Finset.range n, c i * (u (i + 1) - u i) ^ 2) =
      (∑ i ∈ Finset.range n, c i * u i ^ 2) +
      (∑ i ∈ Finset.range n, c i * u (i + 1) ^ 2) -
      2 * ∑ i ∈ Finset.range n, c i * u i * u (i + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hl, hr, hg]
  ring

lemma edgeCoeff_last (n : ℕ) : edgeCoeff n n = 0 := by
  simp [edgeCoeff, show (n + 1 : ℝ) ≠ 0 by positivity]

lemma edgeCoeff_upper (n i : ℕ) (hi : i ≤ n) :
    edgeCoeff n i ≤ 1 - (i + 1 : ℝ) / (2 * (n + 1)) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hit : (i + 1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ hi
  have ht : 0 ≤ (i + 1 : ℝ) / (n + 1) := by positivity
  have ht1 : (i + 1 : ℝ) / (n + 1) ≤ 1 := (div_le_one hn).mpr hit
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 - (i + 1 : ℝ) / (n + 1))
  have hd : (i + 1 : ℝ) / (2 * (n + 1)) = ((i + 1 : ℝ) / (n + 1)) / 2 := by rw [div_div]; ring
  dsimp [edgeCoeff]
  rw [hd]
  nlinarith [Real.sqrt_nonneg (1 - (i + 1 : ℝ) / (n + 1)),
    sq_nonneg ((i + 1 : ℝ) / (n + 1))]

lemma edgeCoeff_le_one (n i : ℕ) (hi : i ≤ n) : edgeCoeff n i ≤ 1 :=
  (edgeCoeff_upper n i hi).trans (sub_le_self _ (by positivity))

lemma edge_deficit (n i : ℕ) (hi : i ≤ n) :
    (i + 1 : ℝ) / (2 * (n + 1)) ≤
      2 - edgeCoeff n i - if i = 0 then 0 else edgeCoeff n (i - 1) := by
  have h := edgeCoeff_upper n i hi
  split_ifs with hi0
  · linarith
  · have hprev := edgeCoeff_le_one n (i - 1) (by omega)
    linarith

lemma pathEnergy_expansion (n : ℕ) (u : ℕ → ℝ) :
    pathEnergy n u =
      (∑ i ∈ Finset.range n, edgeCoeff n i * (u (i + 1) - u i) ^ 2) +
      ∑ i ∈ Finset.range (n + 1),
        (2 - edgeCoeff n i - if i = 0 then 0 else edgeCoeff n (i - 1)) * u i ^ 2 :=
  path_energy_identity n (edgeCoeff n) u (edgeCoeff_last n)

lemma pathEnergy_controls (n : ℕ) (u : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, edgeCoeff n i * (u (i + 1) - u i) ^ 2) +
      (∑ i ∈ Finset.range (n + 1), (i + 1 : ℝ) / (2 * (n + 1)) * u i ^ 2) ≤
      pathEnergy n u := by
  rw [pathEnergy_expansion]
  gcongr with i hi
  exact edge_deficit n i (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))

lemma pathEnergy_nonneg (n : ℕ) (u : ℕ → ℝ) : 0 ≤ pathEnergy n u :=
  (by
    unfold edgeCoeff
    positivity : 0 ≤
    (∑ i ∈ Finset.range n, edgeCoeff n i * (u (i + 1) - u i) ^ 2) +
      (∑ i ∈ Finset.range (n + 1), (i + 1 : ℝ) / (2 * (n + 1)) * u i ^ 2)).trans
        (pathEnergy_controls n u)

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_PathSpectra
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial
open scoped BigOperators Topology
open Filter
namespace CriticalSK

lemma scaledHermite_succ (a : ℝ) (k : ℕ) :
    scaledHermite a (k + 1) = X * scaledHermite a k - C a * derivative (scaledHermite a k) := rfl

lemma derivative_scaledHermite_succ (a : ℝ) (k : ℕ) :
    derivative (scaledHermite a (k + 1)) = C (k + 1 : ℝ) * scaledHermite a k := by
  induction k with
  | zero => simp [scaledHermite]
  | succ k ih =>
    rw [scaledHermite_succ a (k + 1), derivative_sub, derivative_mul, derivative_X,
      one_mul, ih, derivative_mul, derivative_C, zero_mul, zero_add]
    rw [derivative_mul, derivative_C, zero_mul, zero_add]
    rw [scaledHermite_succ a k]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

lemma scaledHermite_three_term (a : ℝ) (k : ℕ) :
    scaledHermite a (k + 2) = X * scaledHermite a (k + 1) -
      C (a * (k + 1)) * scaledHermite a k := by
  rw [show k + 2 = (k + 1) + 1 by omega, scaledHermite_succ,
    derivative_scaledHermite_succ, map_mul, mul_assoc]

lemma scaledHermite_differential (a : ℝ) (k : ℕ) :
    C a * derivative (derivative (scaledHermite a k)) -
      X * derivative (scaledHermite a k) + C (k : ℝ) * scaledHermite a k = 0 := by
  have h := derivative_scaledHermite_succ a k
  rw [scaledHermite_succ, derivative_sub, derivative_mul, derivative_X,
    one_mul, derivative_mul, derivative_C, zero_mul, zero_add] at h
  simp only [map_add, map_one] at h
  linear_combination -h

lemma det_tridiagonal_step {R : Type*} [CommRing R] (k : ℕ)
    (A : Matrix (Fin (k + 2)) (Fin (k + 2)) R)
    (hrow : ∀ j : Fin k, A 0 j.succ.succ = 0)
    (hcol : ∀ i : Fin k, A i.succ.succ 0 = 0) :
    A.det = A 0 0 * (A.submatrix Fin.succ Fin.succ).det -
      A 0 1 * A 1 0 * (A.submatrix (Fin.succ ∘ Fin.succ) (Fin.succ ∘ Fin.succ)).det := by
  have hminor : (A.submatrix Fin.succ (1 : Fin (k + 2)).succAbove).det =
      A 1 0 * (A.submatrix (Fin.succ ∘ Fin.succ) (Fin.succ ∘ Fin.succ)).det := by
    rw [det_succ_column_zero, Fin.sum_univ_succ]
    simp only [Matrix.submatrix_apply, Fin.val_zero, pow_zero, one_mul,
      Fin.succ_zero_eq_one, Fin.one_succAbove_zero, hcol, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero, submatrix_submatrix, Fin.succAbove_zero]
    congr 2
  rw [det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Fin.val_succ,
    Fin.succ_zero_eq_one, hminor, hrow, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, Fin.val_one, pow_one, neg_one_mul]
  ring

lemma jacobi_diagonal (a : ℝ) (k : ℕ) (i : Fin k) : jacobi a k i i = 0 := by
  simp [jacobi]

lemma jacobi_tail (a : ℝ) (k : ℕ) :
    (jacobi a (k + 1)).submatrix Fin.succ Fin.succ = jacobi a k := by
  ext i j
  simp only [Matrix.submatrix_apply, jacobi, Fin.val_succ, Nat.add_right_cancel_iff,
    Nat.cast_add, Nat.cast_one]
  split_ifs <;> congr 1 <;> ring

lemma jacobi_row_zero (a : ℝ) (k : ℕ) (j : Fin k) : jacobi a (k + 2) 0 j.succ.succ = 0 := by
  simp [jacobi]

lemma jacobi_col_zero (a : ℝ) (k : ℕ) (i : Fin k) : jacobi a (k + 2) i.succ.succ 0 = 0 := by
  simp [jacobi]

lemma jacobi_first_super (a : ℝ) (k : ℕ) :
    jacobi a (k + 2) 0 1 = Real.sqrt (a * (k + 1)) := by
  simp [jacobi]
  congr 1
  ring

lemma jacobi_first_sub (a : ℝ) (k : ℕ) :
    jacobi a (k + 2) 1 0 = Real.sqrt (a * (k + 1)) := by
  simp [jacobi]
  congr 1
  ring

lemma charmatrix_jacobi_tail (a : ℝ) (k : ℕ) :
    ((jacobi a (k + 1)).charmatrix).submatrix Fin.succ Fin.succ =
      (jacobi a k).charmatrix := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [jacobi_diagonal]
  · simp [hij, charmatrix_apply_ne, ← jacobi_tail a k]

lemma jacobi_charpoly_step {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    (jacobi a (k + 2)).charpoly = X * (jacobi a (k + 1)).charpoly -
      C (a * (k + 1)) * (jacobi a k).charpoly := by
  have hr (j : Fin k) : (jacobi a (k + 2)).charmatrix 0 j.succ.succ = 0 := by
    rw [charmatrix_apply_ne _ _ _ (by simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_succ]; omega), jacobi_row_zero]
    simp
  have hc (i : Fin k) : (jacobi a (k + 2)).charmatrix i.succ.succ 0 = 0 := by
    rw [charmatrix_apply_ne _ _ _ (by simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_succ]; omega), jacobi_col_zero]
    simp
  unfold Matrix.charpoly
  rw [det_tridiagonal_step k _ hr hc, charmatrix_apply_eq, jacobi_diagonal,
    map_zero, sub_zero, charmatrix_jacobi_tail,
    charmatrix_apply_ne _ _ _ (by simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_one]; omega : (0 : Fin (k + 2)) ≠ 1),
    charmatrix_apply_ne _ _ _ (by simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_one]; omega : (1 : Fin (k + 2)) ≠ 0),
    jacobi_first_super, jacobi_first_sub, neg_mul_neg, ← map_mul,
    ← sq, Real.sq_sqrt (by positivity)]
  congr 2
  rw [← submatrix_submatrix, charmatrix_jacobi_tail, charmatrix_jacobi_tail]

lemma jacobi_charpoly {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    (jacobi a k).charpoly = scaledHermite a k := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one =>
    have hz : jacobi a 1 = 0 := by ext i j; fin_cases i; fin_cases j; simp [jacobi]
    simp [hz, scaledHermite]
  | more k h0 h1 => rw [jacobi_charpoly_step ha, h0, h1, scaledHermite_three_term]

lemma finset_sum_indicator_le_one {ι : Type*} [Fintype ι] (p : ι → Prop)
    [DecidablePred p] (hp : ∀ i j, p i → p j → i = j) :
    (∑ i, if p i then (1 : ℝ) else 0) ≤ 1 := by
  classical
  by_cases hex : ∃ i, p i
  · obtain ⟨i, hi⟩ := hex
    have heq : ∀ j, p j ↔ j = i := fun j => ⟨fun hj => hp j i hj hi, fun h => h ▸ hi⟩
    simp_rw [heq]
    simp
  · simp [not_exists.mp hex]

lemma jacobi_row_norm_bound (n : ℕ) (i : Fin n) :
    ∑ j : Fin n, ‖jacobi (n : ℝ)⁻¹ n i j‖ ≤ 2 := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hentry (k : Fin n) : Real.sqrt ((n : ℝ)⁻¹ * ((n : ℝ) - 1 - k.val)) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    have hk : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    apply (inv_mul_le_iff₀ hn).mpr
    linarith
  have hpoint (j : Fin n) : ‖jacobi (n : ℝ)⁻¹ n i j‖ ≤
      (if i.val + 1 = j.val then 1 else 0) + (if j.val + 1 = i.val then 1 else 0) := by
    unfold jacobi
    split_ifs <;> simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      norm_zero] <;> linarith [hentry i, hentry j]
  have h₁ := finset_sum_indicator_le_one (fun j : Fin n => i.val + 1 = j.val)
    (fun j k hj hk => Fin.ext (by omega))
  have h₂ := finset_sum_indicator_le_one (fun j : Fin n => j.val + 1 = i.val)
    (fun j k hj hk => Fin.ext (by omega))
  have hb := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hpoint j)
  rw [Finset.sum_add_distrib] at hb
  linarith

lemma jacobi_eigenvalue_bound (n : ℕ) (i : Fin n) :
    |(jacobi_hermitian (n : ℝ)⁻¹ n).eigenvalues i| ≤ 2 := by
  let hA := jacobi_hermitian (n : ℝ)⁻¹ n
  have he : Module.End.HasEigenvalue (Matrix.toLin' (jacobi (n : ℝ)⁻¹ n))
      (hA.eigenvalues i) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨Module.End.mem_eigenspace_iff.mpr (hA.mulVec_eigenvectorBasis i), ?_⟩
    intro h
    apply hA.eigenvectorBasis.orthonormal.ne_zero i
    ext j
    exact congrFun h j
  obtain ⟨j, hj⟩ := eigenvalue_mem_ball he
  rw [Metric.mem_closedBall, jacobi_diagonal, dist_zero_right, Real.norm_eq_abs] at hj
  exact hj.trans ((Finset.sum_le_univ_sum_of_nonneg (fun _ => norm_nonneg _)).trans
    (jacobi_row_norm_bound n j))

section

lemma semicircle_discriminant_pos {s : ℝ} (hs : 0 < s) : 0 < s * (4 + s) := by positivity

lemma semicircleResolvent_le_one {s : ℝ} (hs : 0 ≤ s) : semicircleResolvent s ≤ 1 := by
  have hn := Real.sqrt_nonneg (s * (4 + s))
  have hsq := Real.sq_sqrt (show 0 ≤ s * (4 + s) by positivity)
  unfold semicircleResolvent
  nlinarith

lemma semicircleResolvent_deficit {s : ℝ} (hs : 0 ≤ s) :
    1 - semicircleResolvent s ≤ Real.sqrt s := by
  have hn := Real.sqrt_nonneg (s * (4 + s))
  have hsq := Real.sq_sqrt (show 0 ≤ s * (4 + s) by positivity)
  have hb := Real.sqrt_nonneg s
  have hb2 := Real.sq_sqrt hs
  unfold semicircleResolvent
  nlinarith [mul_nonneg hs hb]

lemma semicircleResolvent_difference {s : ℝ} (hs : 0 ≤ s) :
    semicircleResolvent (s / 2) - semicircleResolvent s ≤ Real.sqrt s := by
  have := semicircleResolvent_le_one (show 0 ≤ s / 2 by positivity)
  have := semicircleResolvent_deficit hs
  linarith

lemma semicircle_discriminant_lower {s : ℝ} (hs : 0 ≤ s) :
    2 * Real.sqrt s ≤ Real.sqrt (s * (4 + s)) := by
  have hn := Real.sqrt_nonneg (s * (4 + s))
  have hsq := Real.sq_sqrt (show 0 ≤ s * (4 + s) by positivity)
  have hb := Real.sqrt_nonneg s
  have hb2 := Real.sq_sqrt hs
  nlinarith

variable {ι : Type*} [Fintype ι] [Nonempty ι] (e : ι → ℝ) (he : ∀ i, 0 ≤ e i)

include he

lemma empiricalResolventSquare_pos {s : ℝ} (hs : 0 < s) : 0 < empiricalResolventSquare e s := by
  unfold empiricalResolventSquare
  apply mul_pos (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  exact Finset.sum_pos (fun i _ => sq_pos_of_pos (inv_pos.mpr
    (add_pos_of_pos_of_nonneg hs (he i)))) Finset.univ_nonempty

lemma empiricalResolvent_le_inv {s : ℝ} (hs : 0 < s) : empiricalResolvent e s ≤ s⁻¹ := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  calc
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, s⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn.le)
      apply Finset.sum_le_sum
      intro i _
      exact (inv_le_inv₀ (add_pos_of_pos_of_nonneg hs (he i)) hs).mpr (le_add_of_nonneg_right (he i))
    _ = s⁻¹ := by simp [hn.ne']

omit [Nonempty ι] in
lemma empiricalResolvent_continuousOn : ContinuousOn (empiricalResolvent e) (Set.Ioi 0) := by
  apply ContinuousOn.const_mul
  apply continuousOn_finsetSum
  intro i _
  apply ContinuousOn.inv₀ (continuousOn_id.add continuousOn_const)
  intro s hs
  exact ne_of_gt (add_pos_of_pos_of_nonneg hs (he i))

omit [Nonempty ι] in
lemma empiricalResolvent_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt (empiricalResolvent e) (-empiricalResolventSquare e s) s := by
  have h (i : ι) : HasDerivAt (fun u : ℝ => (u + e i)⁻¹) (-(s + e i)⁻¹ ^ 2) s := by
    convert! ((hasDerivAt_id s).add_const (e i)).inv (ne_of_gt
      (add_pos_of_pos_of_nonneg hs (he i))) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [neg_div, one_div, inv_pow, id_eq]
  convert! (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => h i)).const_mul
    (Fintype.card ι : ℝ)⁻¹ using 1
  all_goals try with_reducible_and_instances rfl
  simp only [empiricalResolventSquare, Finset.sum_neg_distrib, mul_neg]

lemma empiricalResolvent_square_difference {s : ℝ} (hs : 0 < s) :
    empiricalResolventSquare e s ≤ 2 / s *
      (empiricalResolvent e (s / 2) - empiricalResolvent e s) := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hpoint (i : ι) : (s + e i)⁻¹ ^ 2 ≤ 2 / s * ((s / 2 + e i)⁻¹ - (s + e i)⁻¹) := by
    have hi : 0 < s + e i := by linarith [he i]
    have hi2 : 0 < s / 2 + e i := by linarith [he i]
    have hval : 2 / s * ((s / 2 + e i)⁻¹ - (s + e i)⁻¹) =
        ((s / 2 + e i) * (s + e i))⁻¹ := by
        rw [inv_sub_inv hi2.ne' hi.ne',
          show s + e i - (s / 2 + e i) = s / 2 by ring, ← mul_div_assoc,
          show 2 / s * (s / 2) = 1 by field_simp, one_div]
    rw [hval, inv_pow]
    apply (inv_le_inv₀ (sq_pos_of_pos hi) (mul_pos hi2 hi)).mpr
    nlinarith
  unfold empiricalResolventSquare empiricalResolvent
  calc
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i, 2 / s * ((s / 2 + e i)⁻¹ - (s + e i)⁻¹) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hpoint i)) (inv_nonneg.mpr hn.le)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_sub_distrib]; ring

lemma empiricalResolvent_lt_midpoint
    (hR : ∀ s : ℝ, 0 < s →
      (empiricalResolvent e s) ^ 2 - (2 + s) * empiricalResolvent e s + 1 =
        empiricalResolventSquare e s / Fintype.card ι)
    {s : ℝ} (hs : 0 < s) : empiricalResolvent e s < (2 + s) / 2 := by
  by_contra hbad
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  let f : ℝ → ℝ := fun u => (2 + u) / 2 - empiricalResolvent e u
  have hfs : f s ≤ 0 := by dsimp [f]; linarith
  have hft : 0 ≤ f (s + 2) := by
    have hb := empiricalResolvent_le_inv e he (show 0 < s + 2 by linarith)
    have hinv : (s + 2)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr (by linarith)
    dsimp [f]
    linarith
  have hc : ContinuousOn f (Set.Icc s (s + 2)) := by
    apply ContinuousOn.sub
    · exact (continuous_const.add continuous_id).continuousOn.div_const 2
    · exact (empiricalResolvent_continuousOn e he).mono (fun u hu => lt_of_lt_of_le hs hu.1)
  obtain ⟨u, hu, hzero⟩ := intermediate_value_Icc (show s ≤ s + 2 by linarith) hc ⟨hfs, hft⟩
  have hu0 : 0 < u := lt_of_lt_of_le hs hu.1
  have hid := hR u hu0
  have ht : 0 < empiricalResolventSquare e u / Fintype.card ι :=
    div_pos (empiricalResolventSquare_pos e he hu0) hn
  dsimp [f] at hzero
  nlinarith

lemma empiricalResolvent_lt_semicircle
    (hR : ∀ s : ℝ, 0 < s →
      (empiricalResolvent e s) ^ 2 - (2 + s) * empiricalResolvent e s + 1 =
        empiricalResolventSquare e s / Fintype.card ι)
    {s : ℝ} (hs : 0 < s) : empiricalResolvent e s < semicircleResolvent s := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hmid := empiricalResolvent_lt_midpoint e he hR hs
  have hid := hR s hs
  have ht : 0 < empiricalResolventSquare e s / Fintype.card ι :=
    div_pos (empiricalResolventSquare_pos e he hs) hn
  have hsq := Real.sq_sqrt (semicircle_discriminant_pos hs).le
  have hpos := Real.sqrt_nonneg (s * (4 + s))
  unfold semicircleResolvent
  nlinarith

lemma empiricalResolvent_root_difference
    (hR : ∀ s : ℝ, 0 < s →
      (empiricalResolvent e s) ^ 2 - (2 + s) * empiricalResolvent e s + 1 =
        empiricalResolventSquare e s / Fintype.card ι)
    {s : ℝ} (hs : 0 < s) :
    0 ≤ semicircleResolvent s - empiricalResolvent e s ∧
      semicircleResolvent s - empiricalResolvent e s ≤
        empiricalResolventSquare e s /
          ((Fintype.card ι : ℝ) * Real.sqrt (s * (4 + s))) := by
  have hd := (empiricalResolvent_lt_semicircle e he hR hs).le
  refine ⟨sub_nonneg.mpr hd, ?_⟩
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hpos : 0 < Real.sqrt (s * (4 + s)) := Real.sqrt_pos.mpr (semicircle_discriminant_pos hs)
  have hsq := Real.sq_sqrt (semicircle_discriminant_pos hs).le
  have hid := hR s hs
  apply (le_div_iff₀ (mul_pos hn hpos)).mpr
  have hid' := (eq_div_iff hn.ne').mp hid
  unfold semicircleResolvent at *
  nlinarith [sq_nonneg ((2 + s - Real.sqrt (s * (4 + s))) / 2 - empiricalResolvent e s)]

lemma empiricalResolventSquare_bound
    (hR : ∀ s : ℝ, 0 < s →
      (empiricalResolvent e s) ^ 2 - (2 + s) * empiricalResolvent e s + 1 =
        empiricalResolventSquare e s / Fintype.card ι)
    {s : ℝ} (hs : 0 < s)
    (hscale : 4 ≤ (Fintype.card ι : ℝ) * s * Real.sqrt (s * (4 + s))) :
    empiricalResolventSquare e s ≤ 4 / Real.sqrt s := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hsp := Real.sqrt_pos.mpr hs
  have hsq := Real.sq_sqrt hs.le
  have hdisc := Real.sqrt_pos.mpr (semicircle_discriminant_pos hs)
  have hd := empiricalResolvent_root_difference e he hR hs
  have hhalf := (empiricalResolvent_lt_semicircle e he hR (show 0 < s / 2 by positivity)).le
  have hdiff := semicircleResolvent_difference hs.le
  have hb := empiricalResolvent_square_difference e he hs
  have hT := (empiricalResolventSquare_pos e he hs).le
  have hd' : 2 * (semicircleResolvent s - empiricalResolvent e s) ≤
      s * empiricalResolventSquare e s / 2 := by
    have hden : 0 < (Fintype.card ι : ℝ) * Real.sqrt (s * (4 + s)) := mul_pos hn hdisc
    have hmul := (le_div_iff₀ hden).mp hd.2
    have hscl : 4 ≤ s * ((Fintype.card ι : ℝ) * Real.sqrt (s * (4 + s))) := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hscl hd.1
    have hm2 := mul_le_mul_of_nonneg_left hmul hs.le
    nlinarith
  have hb' : s * empiricalResolventSquare e s ≤
      2 * (empiricalResolvent e (s / 2) - empiricalResolvent e s) := by
    have := (mul_le_mul_of_nonneg_left hb hs.le)
    field_simp at this
    nlinarith
  apply (le_div_iff₀ hsp).mpr
  have hmain : s * empiricalResolventSquare e s ≤ 4 * Real.sqrt s := by linarith
  have := mul_le_mul_of_nonneg_right hmain hsp.le
  nlinarith

lemma empiricalResolvent_error_bound
    (hR : ∀ s : ℝ, 0 < s →
      (empiricalResolvent e s) ^ 2 - (2 + s) * empiricalResolvent e s + 1 =
        empiricalResolventSquare e s / Fintype.card ι)
    {s : ℝ} (hs : 0 < s)
    (hscale : 4 ≤ (Fintype.card ι : ℝ) * s * Real.sqrt (s * (4 + s))) :
    0 ≤ semicircleResolvent s - empiricalResolvent e s ∧
      semicircleResolvent s - empiricalResolvent e s ≤ 2 / ((Fintype.card ι : ℝ) * s) := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hsp := Real.sqrt_pos.mpr hs
  have hsq := Real.sq_sqrt hs.le
  have hdisc := Real.sqrt_pos.mpr (semicircle_discriminant_pos hs)
  have hd := empiricalResolvent_root_difference e he hR hs
  refine ⟨hd.1, ?_⟩
  have hT := empiricalResolventSquare_bound e he hR hs hscale
  have hlow := semicircle_discriminant_lower hs.le
  have hd' := (le_div_iff₀ (mul_pos hn hdisc)).mp hd.2
  have hT' := (le_div_iff₀ hsp).mp hT
  have hm := mul_le_mul_of_nonneg_right hd' hsp.le
  have hlow' := mul_le_mul_of_nonneg_left hlow (mul_nonneg hd.1 hn.le)
  have hlow'' := mul_le_mul_of_nonneg_right hlow' hsp.le
  apply (le_div_iff₀ (mul_pos hn hs)).mpr
  nlinarith

end

open Matrix Polynomial Filter

lemma jacobiGaps_nonneg (n : ℕ) (i : Fin n) : 0 ≤ jacobiGaps n i := by
  have := (abs_le.mp (jacobi_eigenvalue_bound n i)).2
  exact sub_nonneg.mpr this

lemma hermitian_charpoly_derivative_ratio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) {z : ℝ} (hz : A.charpoly.eval z ≠ 0) :
    A.charpoly.derivative.eval z / A.charpoly.eval z = ∑ i, (z - hA.eigenvalues i)⁻¹ := by
  rw [hA.splits_charpoly.eval_derivative_div_eval_of_ne_zero hz,
    hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  simp [one_div]

lemma jacobi_charpoly_nonzero {n : ℕ} {s : ℝ} (hs : 0 < s) :
    (jacobi (n : ℝ)⁻¹ n).charpoly.eval (2 + s) ≠ 0 := by
  rw [(jacobi_hermitian (n : ℝ)⁻¹ n).charpoly_eq, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  simp only [eval_sub, eval_X, eval_C, RCLike.ofReal_real_eq_id, id_eq]
  have := jacobiGaps_nonneg n i
  dsimp [jacobiGaps] at this
  linarith

lemma jacobi_logarithmic_ratio {n : ℕ} {s : ℝ} (hs : 0 < s) :
    (jacobi (n : ℝ)⁻¹ n).charpoly.derivative.eval (2 + s) /
      (jacobi (n : ℝ)⁻¹ n).charpoly.eval (2 + s) =
        (n : ℝ) * empiricalResolvent (jacobiGaps n) s := by
  by_cases hn : n = 0
  · subst n
    simp [empiricalResolvent]
  · rw [hermitian_charpoly_derivative_ratio _ (jacobi_hermitian (n : ℝ)⁻¹ n)
      (jacobi_charpoly_nonzero hs)]
    simp only [empiricalResolvent, Fintype.card_fin, ← mul_assoc,
      mul_inv_cancel₀ (show (n : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hn), one_mul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp [jacobiGaps]
    ring

lemma jacobi_riccati {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) :
    (empiricalResolvent (jacobiGaps n) s) ^ 2 -
      (2 + s) * empiricalResolvent (jacobiGaps n) s + 1 =
        empiricalResolventSquare (jacobiGaps n) s / n := by
  let : NeZero n := ⟨hn.ne'⟩
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let p := (jacobi (n : ℝ)⁻¹ n).charpoly
  have hp : p.eval (2 + s) ≠ 0 := jacobi_charpoly_nonzero hs
  have hpd : HasDerivAt (fun u : ℝ => p.eval (2 + u)) (p.derivative.eval (2 + s)) s := by
    convert! (p.hasDerivAt (2 + s)).comp s ((hasDerivAt_id s).const_add 2) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [mul_one]
  have hpdd : HasDerivAt (fun u : ℝ => p.derivative.eval (2 + u))
      (p.derivative.derivative.eval (2 + s)) s := by
    convert! (p.derivative.hasDerivAt (2 + s)).comp s ((hasDerivAt_id s).const_add 2) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [mul_one]
  have hratio : HasDerivAt (fun u : ℝ => (n : ℝ)⁻¹ *
      (p.derivative.eval (2 + u) / p.eval (2 + u)))
      ((n : ℝ)⁻¹ * ((p.derivative.derivative.eval (2 + s) * p.eval (2 + s) -
        p.derivative.eval (2 + s) * p.derivative.eval (2 + s)) / p.eval (2 + s)^2)) s := by
    convert! (hpdd.div hpd hp).const_mul (n : ℝ)⁻¹ using 1
    all_goals try with_reducible_and_instances rfl
  have hlocal : (fun u : ℝ => (n : ℝ)⁻¹ *
      (p.derivative.eval (2 + u) / p.eval (2 + u))) =ᶠ[𝓝 s]
        empiricalResolvent (jacobiGaps n) := by
    filter_upwards [Ioi_mem_nhds hs] with u hu
    rw [jacobi_logarithmic_ratio hu, ← mul_assoc, inv_mul_cancel₀ hnR.ne', one_mul]
  have hder := (hratio.congr_of_eventuallyEq hlocal.symm).unique
    (empiricalResolvent_hasDerivAt (jacobiGaps n) (jacobiGaps_nonneg n) hs)
  have hode := congrArg (Polynomial.eval (2 + s)) (scaledHermite_differential (n : ℝ)⁻¹ n)
  rw [← jacobi_charpoly (inv_nonneg.mpr hnR.le) n] at hode
  rw [eval_zero] at hode
  change (C (n : ℝ)⁻¹ * p.derivative.derivative - X * p.derivative + C (n : ℝ) * p).eval (2 + s) = 0 at hode
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X] at hode
  have hv := jacobi_logarithmic_ratio (n := n) hs
  change p.derivative.eval (2 + s) / p.eval (2 + s) =
    (n : ℝ) * empiricalResolvent (jacobiGaps n) s at hv
  change (n : ℝ)⁻¹ * ((p.derivative.derivative.eval (2 + s) * p.eval (2 + s) -
        p.derivative.eval (2 + s) * p.derivative.eval (2 + s)) / p.eval (2 + s)^2) =
      -empiricalResolventSquare (jacobiGaps n) s at hder
  field_simp [hnR.ne', hp] at hode hv hder ⊢
  rw [hv] at hode hder
  have hh : (n : ℝ) * p.eval (2 + s) ^ 2 *
      ((n : ℝ) * (empiricalResolvent (jacobiGaps n) s *
        (empiricalResolvent (jacobiGaps n) s - (2 + s)) + 1) -
        empiricalResolventSquare (jacobiGaps n) s) = 0 := by
    linear_combination p.eval (2 + s) * hode - hder
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left
    (mul_ne_zero hnR.ne' (pow_ne_zero 2 hp)))

lemma jacobi_resolvent_estimates {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s)
    (hscale : 2 ≤ (n : ℝ) * s * Real.sqrt s) :
    empiricalResolventSquare (jacobiGaps n) s ≤ 4 / Real.sqrt s ∧
      0 ≤ semicircleResolvent s - empiricalResolvent (jacobiGaps n) s ∧
      semicircleResolvent s - empiricalResolvent (jacobiGaps n) s ≤ 2 / (n * s) := by
  let : NeZero n := ⟨hn.ne'⟩
  have hR : ∀ u : ℝ, 0 < u →
      (empiricalResolvent (jacobiGaps n) u) ^ 2 -
        (2 + u) * empiricalResolvent (jacobiGaps n) u + 1 =
          empiricalResolventSquare (jacobiGaps n) u / Fintype.card (Fin n) := by
    intro u hu
    simpa using (jacobi_riccati hn hu)
  have hscale' : 4 ≤ (Fintype.card (Fin n) : ℝ) * s * Real.sqrt (s * (4 + s)) := by
    have := mul_le_mul_of_nonneg_left (semicircle_discriminant_lower hs.le)
      (show 0 ≤ (n : ℝ) * s by positivity)
    simp only [Fintype.card_fin]
    nlinarith
  exact ⟨empiricalResolventSquare_bound _ (jacobiGaps_nonneg n) hR hs hscale',
    by simpa using empiricalResolvent_error_bound _ (jacobiGaps_nonneg n) hR hs hscale'⟩

lemma jacobi_edgeCoeff (n : ℕ) (i j : Fin (n+1)) :
    jacobi (n+1 : ℝ)⁻¹ (n+1) i j =
      (if i.val+1=j.val then edgeCoeff n i.val else 0) +
      (if j.val+1=i.val then edgeCoeff n j.val else 0) := by
  have hs (k : Fin (n+1)) :
      Real.sqrt ((n+1 : ℝ)⁻¹ * ((n+1 : ℝ)-1-k.val)) = edgeCoeff n k.val := by
    unfold edgeCoeff
    congr 1
    field_simp
    ring
  simp only [jacobi, Nat.cast_add, Nat.cast_one, hs]
  split_ifs with h h' h' <;> try rfl
  · omega
  · simp
  · simp
  · simp

lemma directed_neighbor_sum (n : ℕ) (u : ℕ → ℝ) :
    (∑ i : Fin (n+1), ∑ j : Fin (n+1),
      (if i.val+1=j.val then edgeCoeff n i.val else 0) * u i.val * u j.val) =
      ∑ i ∈ Finset.range n, edgeCoeff n i * u i * u (i+1) := by
  rw [Fin.sum_univ_castSucc]
  have hl : (∑ j : Fin (n+1),
      (if (Fin.last n).val+1=j.val then edgeCoeff n (Fin.last n).val else 0) *
        u (Fin.last n).val * u j.val) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [ite_eq_right (by have := j.isLt; simp only [Fin.val_last]; omega), zero_mul, zero_mul]
  rw [hl, add_zero, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i.succ]
  · simp
  · intro j _ hj
    rw [ite_eq_right (fun h => hj (Fin.ext (by simpa using h.symm))), zero_mul, zero_mul]
  · simp

lemma pathOperator_inner (n : ℕ) (u : ℕ → ℝ) :
    inner ℝ (WithLp.toLp 2 (fun i : Fin (n+1) => u i.val))
      (pathOperator n (WithLp.toLp 2 (fun i : Fin (n+1) => u i.val))) =
      2 * ∑ i ∈ Finset.range n, edgeCoeff n i * u i * u (i+1) := by
  simp only [pathOperator, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct,
    Pi.star_apply, star_trivial, dotProduct, Matrix.mulVec,
    jacobi_edgeCoeff, add_mul, Finset.sum_add_distrib]
  have hlo : (∑ i : Fin (n+1), (∑ j : Fin (n+1),
      (if i.val+1=j.val then edgeCoeff n i.val else 0) * u j.val) * u i.val) =
      ∑ i ∈ Finset.range n, edgeCoeff n i * u i * u (i+1) := by
    convert directed_neighbor_sum n u using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intros
    ring
  have hhi : (∑ i : Fin (n+1), (∑ j : Fin (n+1),
      (if j.val+1=i.val then edgeCoeff n j.val else 0) * u j.val) * u i.val) =
      ∑ i ∈ Finset.range n, edgeCoeff n i * u i * u (i+1) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact directed_neighbor_sum n u
  rw [hlo, hhi]
  ring

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_Powers
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

namespace CriticalSK

lemma edgeError_relative {A B C s t e : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hs : 0 < s) (hst : s ≤ t) (he : 0 ≤ e) :
    edgeError A B C s e ≤ (A * s ^ (-5 / 8 : ℝ) + B / s + C) * (t + e) := by
  have hes : 0 < e + s := by linarith
  have ht : 0 < t + e := by linarith
  have hp : (e + s) ^ (3 / 8 : ℝ) = (e + s) * (e + s) ^ (-5 / 8 : ℝ) := by
    nth_rw 2 [← Real.rpow_one (e + s)]
    rw [← Real.rpow_add hes]
    norm_num
  have hp' : (e + s) ^ (3 / 8 : ℝ) ≤ s ^ (-5 / 8 : ℝ) * (t + e) := by
    rw [hp]
    calc
      _ ≤ (e + s) * s ^ (-5 / 8 : ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hs (by linarith) (by norm_num)) hes.le
      _ ≤ _ := by
        have : 0 ≤ s ^ (-5 / 8 : ℝ) := by positivity
        nlinarith
  have hb : B ≤ (B / s) * (t + e) := by
    have : B / s * s = B := div_mul_cancel₀ B hs.ne'
    have : 0 ≤ B / s := div_nonneg hB hs.le
    nlinarith [div_mul_cancel₀ B hs.ne']
  have hc : C * e ≤ C * (t + e) := by nlinarith [hs.trans_le hst]
  dsimp [edgeError]
  nlinarith [mul_le_mul_of_nonneg_left hp' hA]

open Set MeasureTheory Filter

open Set Filter MeasureTheory

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_Resolvent
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

namespace CriticalSK


lemma extendPath_restrict (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    (WithLp.toLp 2 (fun i : Fin (n+1) => extendPath n x i.val)) = x := by
  ext i
  simp only [extendPath,dite_eq_left i.isLt]

lemma extendPath_mass (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    (∑ i ∈ Finset.range (n+1), extendPath n x i^2) = ‖x‖^2 := by
  rw [← Fin.sum_univ_eq_sum_range,EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp only [extendPath,dite_eq_left i.isLt]

lemma pathOperator_energy (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    inner ℝ x (pathOperator n x) = 2*‖x‖^2-pathEnergy n (extendPath n x) := by
  have h := pathOperator_inner n (extendPath n x)
  rw [extendPath_restrict] at h
  rw [h,pathEnergy,extendPath_mass]
  ring

lemma pathOperator_inner_le_two (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) (hx : ‖x‖=1) :
    inner ℝ x (pathOperator n x) ≤ 2 := by
  rw [pathOperator_energy,hx]
  have := pathEnergy_nonneg n (extendPath n x)
  linarith

lemma pathOperator_eigenvalue_le_two (n : ℕ) (i : Fin (n+1)) :
    (pathOperator_symmetric n).eigenvalues (by simp) i ≤ 2 := by
  let h := pathOperator_symmetric n
  have hh := pathOperator_inner_le_two n (h.eigenvectorBasis (by simp) i) ((h.eigenvectorBasis (by simp)).norm_eq_one i)
  rw [h.apply_eigenvectorBasis] at hh
  simpa only [inner_smul_right,real_inner_self_eq_norm_sq,
    (h.eigenvectorBasis (by simp)).norm_eq_one i,one_pow,mul_one,
    RCLike.ofReal_real_eq_id,id_eq] using hh

open MeasureTheory Set

lemma weighted_resolvent_integrable {s e : ℝ} (hs : 0 < s) (he : 0 ≤ e) :
    IntegrableOn (fun t : ℝ => t^(-5/8:ℝ)/(t+e)^2) (Ioi s) := by
  apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (-21/8:ℝ) < -1) hs).mono'
  · exact ((measurable_id.pow_const _).div ((measurable_id.add_const e).pow_const 2)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := hs.trans ht
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    calc
      t^(-5/8:ℝ)/(t+e)^2 ≤ t^(-5/8:ℝ)/t^2 := by gcongr; linarith
      _ = t^(-21/8:ℝ) := by
        rw [← Real.rpow_two,← Real.rpow_sub ht0]
        norm_num

lemma fractional_power_integral_bound {s e : ℝ} (hs : 0 < s) (he : 0 ≤ e) :
    (s+e)^(-13/8:ℝ) ≤ (13/2:ℝ)*(∫ t : ℝ in Ioi s, t^(-5/8:ℝ)/(t+e)^2) := by
  have hx : 0 < s+e := by positivity
  have hlo : (∫ t : ℝ in Ioi (s+e), (1/4:ℝ)*t^(-21/8:ℝ)) ≤
      ∫ t : ℝ in Ioi (s+e), t^(-5/8:ℝ)/(t+e)^2 := by
    apply integral_mono_ae ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-21/8:ℝ)< -1) hx).const_mul _) (weighted_resolvent_integrable hx he)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := hx.trans ht
    have het : e ≤ t := by change s+e < t at ht; linarith
    calc
      (1/4:ℝ)*t^(-21/8:ℝ) = t^(-5/8:ℝ)/(2*t)^2 := by
        have hp : t^(-21/8:ℝ) = t^(-5/8:ℝ)/t^2 := by
          rw [← Real.rpow_two,← Real.rpow_sub ht0]; norm_num
        rw [hp]; ring
      _ ≤ _ := by gcongr; linarith
  have hmono : (∫ t : ℝ in Ioi (s+e), t^(-5/8:ℝ)/(t+e)^2) ≤
      ∫ t : ℝ in Ioi s, t^(-5/8:ℝ)/(t+e)^2 := by
    apply integral_mono_measure (Measure.restrict_mono_set _ (Ioi_subset_Ioi (by linarith))) _
      (weighted_resolvent_integrable hs he)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact div_nonneg (Real.rpow_nonneg (hs.trans ht).le _) (sq_nonneg _)
  rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num : (-21/8:ℝ)< -1) hx] at hlo
  norm_num at hlo
  linarith

lemma fractional_trace_bound {ι : Type*} [Fintype ι] (e : ι → ℝ) (he : ∀ i, 0 ≤ e i)
    {s C : ℝ} (hs : 0 < s)
    (htrace : ∀ t : ℝ, s ≤ t → (∑ i, (t+e i)⁻¹^2) ≤ C / Real.sqrt t) :
    (∑ i, (s+e i)^(-13/8:ℝ)) ≤ 52*C*s^(-1/8:ℝ) := by
  have hint (i : ι) := weighted_resolvent_integrable hs (he i)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => fractional_power_integral_bound hs (he i))
  simp only [← Finset.mul_sum] at hsum
  rw [← integral_finsetSum _ (fun i _ => hint i)] at hsum
  have hi := integrable_finsetSum Finset.univ (fun i _ => hint i)
  have hupper : (∫ t : ℝ in Ioi s, ∑ i, t^(-5/8:ℝ)/(t+e i)^2) ≤
      ∫ t : ℝ in Ioi s, C*t^(-9/8:ℝ) := by
    apply integral_mono_ae hi ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-9/8:ℝ)< -1) hs).const_mul C)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := hs.trans ht
    calc
      (∑ i, t^(-5/8:ℝ)/(t+e i)^2) = t^(-5/8:ℝ)*(∑ i, (t+e i)⁻¹^2) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; simp only [inv_pow,div_eq_mul_inv]
      _ ≤ t^(-5/8:ℝ)*(C/Real.sqrt t) := mul_le_mul_of_nonneg_left (htrace t ht.le) (by positivity)
      _ = C*t^(-9/8:ℝ) := by
        rw [Real.sqrt_eq_rpow]
        have hp : t^(-5/8:ℝ)/t^(1/2:ℝ) = t^(-9/8:ℝ) := by rw [← Real.rpow_sub ht0]; norm_num
        calc
          _ = C*(t^(-5/8:ℝ)/t^(1/2:ℝ)) := by ring
          _ = _ := by rw [hp]
  rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num : (-9/8:ℝ)< -1) hs] at hupper
  norm_num at hupper
  nlinarith



open MeasureTheory Set

lemma inverse_perturbation_bound {x d E : ℝ} (hx : 0 < x) (hclose : |d-x| ≤ E)
    (hsmall : E ≤ x/2) : 0 < d ∧ |d⁻¹-x⁻¹| ≤ 2*E/x^2 ∧ d⁻¹^2 ≤ 4*x⁻¹^2 := by
  have hd : 0 < d := by have := (abs_le.mp hclose).1; linarith
  have hdx : x/2 ≤ d := by have := (abs_le.mp hclose).1; linarith
  have he : 0 ≤ E := (abs_nonneg _).trans hclose
  refine ⟨hd,?_,?_⟩
  · have hid : d⁻¹-x⁻¹ = (x-d)/(d*x) := by field_simp
    rw [hid,abs_div,abs_of_pos (mul_pos hd hx),abs_sub_comm]
    calc
      |d-x|/(d*x) ≤ E/(d*x) := by gcongr
      _ ≤ E/((x/2)*x) := div_le_div_of_nonneg_left he (by positivity)
        (mul_le_mul_of_nonneg_right hdx hx.le)
      _ = 2*E/x^2 := by field_simp
  · have hinv : d⁻¹ ≤ 2*x⁻¹ := by
      have hh := one_div_le_one_div_of_le (by positivity : 0 < x/2) hdx
      have heq : (x/2)⁻¹ = 2*x⁻¹ := by field_simp
      simpa only [one_div,heq] using hh
    calc
      d⁻¹^2 ≤ (2*x⁻¹)^2 := pow_le_pow_left₀ (inv_nonneg.mpr hd.le) hinv 2
      _ = _ := by ring

lemma resolvent_trace_transfer {ι : Type*} [Fintype ι] (e lam : ι → ℝ)
    {A B C s₀ s D : ℝ} (he : ∀ i, 0 ≤ e i) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s)
    (hclose : ∀ i, |lam i-(2-e i)| ≤ edgeError A B C s₀ (e i))
    (hsmall : A*s₀^(-5/8:ℝ)+B/s₀+C ≤ 1/2)
    (htrace : ∀ t : ℝ, s ≤ t → (∑ i, (t+e i)⁻¹^2) ≤ D / Real.sqrt t) :
    (∀ i, 0 < 2+s-lam i) ∧
    (∑ i, (2+s-lam i)⁻¹^2) ≤ 4*D/Real.sqrt s ∧
    |(∑ i, (2+s-lam i)⁻¹)-(∑ i, (s+e i)⁻¹)| ≤
      104*A*D*s^(-1/8:ℝ)+2*B*(D/Real.sqrt s)+2*C*(∑ i, (s+e i)⁻¹) := by
  have hspos : 0 < s := hs₀.trans_le hs
  have hrel (i : ι) : edgeError A B C s₀ (e i) ≤ (s+e i)/2 := by
    have hh := edgeError_relative hA hB hC hs₀ hs (he i)
    have hei := he i
    exact hh.trans ((mul_le_mul_of_nonneg_right hsmall (by positivity)).trans_eq (by ring))
  have hc (i : ι) : |(2+s-lam i)-(s+e i)| ≤ edgeError A B C s₀ (e i) := by
    convert hclose i using 1
    all_goals try with_reducible_and_instances rfl
    rw [show 2+s-lam i-(s+e i) = -(lam i-(2-e i)) by ring,abs_neg]
  have hh (i : ι) := inverse_perturbation_bound (add_pos_of_pos_of_nonneg hspos (he i)) (hc i) (hrel i)
  refine ⟨fun i => (hh i).1,?_,?_⟩
  · calc
      _ ≤ ∑ i, 4*(s+e i)⁻¹^2 := Finset.sum_le_sum (fun i _ => (hh i).2.2)
      _ = 4*∑ i, (s+e i)⁻¹^2 := by rw [Finset.mul_sum]
      _ ≤ _ := by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (htrace s le_rfl) (by norm_num : (0:ℝ) ≤ 4)
  · have hpoint (i : ι) : 2*edgeError A B C s₀ (e i)/(s+e i)^2 ≤
        2*A*(s+e i)^(-13/8:ℝ)+2*B*(s+e i)⁻¹^2+2*C*(s+e i)⁻¹ := by
      have hei := he i
      have hx : 0 < s+e i := by positivity
      have hexp : (e i+s₀)^(3/8:ℝ) ≤ (s+e i)^(3/8:ℝ) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      have hp : (s+e i)^(3/8:ℝ)/(s+e i)^2 = (s+e i)^(-13/8:ℝ) := by
        rw [← Real.rpow_two,← Real.rpow_sub hx]; norm_num
      have hCe : C*e i ≤ C*(s+e i) := by gcongr; linarith
      calc
        _ ≤ 2*(A*(s+e i)^(3/8:ℝ)+B+C*(s+e i))/(s+e i)^2 := by
          unfold edgeError; gcongr
        _ = _ := by rw [show 2*(A*(s+e i)^(3/8:ℝ)+B+C*(s+e i))/(s+e i)^2 =
            2*A*((s+e i)^(3/8:ℝ)/(s+e i)^2)+2*B*(s+e i)⁻¹^2+2*C*(s+e i)⁻¹ by field_simp,hp]
    calc
      _ = |∑ i, ((2+s-lam i)⁻¹-(s+e i)⁻¹)| := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ i, |(2+s-lam i)⁻¹-(s+e i)⁻¹| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (2*A*(s+e i)^(-13/8:ℝ)+2*B*(s+e i)⁻¹^2+2*C*(s+e i)⁻¹) :=
        Finset.sum_le_sum (fun i _ => (hh i).2.1.trans (hpoint i))
      _ = 2*A*(∑ i, (s+e i)^(-13/8:ℝ))+2*B*(∑ i, (s+e i)⁻¹^2)+2*C*(∑ i, (s+e i)⁻¹) := by
        simp only [Finset.sum_add_distrib,Finset.mul_sum]
      _ ≤ _ := by
        have hf := fractional_trace_bound e he hspos htrace
        have ht := htrace s le_rfl
        nlinarith [mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 2*A),
          mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2*B)]


lemma formA_nonneg (n : ℕ) {h : ℝ} (hh : 0 ≤ h) : 0 ≤ formA n h := by unfold formA; positivity

lemma formB_nonneg (n : ℕ) : 0 ≤ formB n := by unfold formB; positivity

lemma formC_nonneg (n : ℕ) : 0 ≤ formC n := by unfold formC; positivity

lemma orderedJacobiGaps_nonneg (n : ℕ) (i : Fin (n+1)) : 0 ≤ orderedJacobiGaps n i :=
  sub_nonneg.mpr (pathOperator_eigenvalue_le_two n i)

lemma symmetric_eigenvalue_sum_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    {m n : ℕ} (hm : Module.finrank ℝ E = m) (hn : Module.finrank ℝ E = n) (f : ℝ → ℝ) :
    (∑ i, f (hT.eigenvalues hm i)) = ∑ i, f (hT.eigenvalues hn i) := by
  subst m
  subst n
  rfl

lemma sum_orderedJacobiGaps (n : ℕ) (f : ℝ → ℝ) :
    (∑ i, f (orderedJacobiGaps n i)) = ∑ i, f (jacobiGaps (n+1) i) := by
  let e : Fin (Fintype.card (Fin (n+1))) ≃ Fin (n+1) :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have hh := Equiv.sum_comp e (fun i => f (jacobiGaps (n+1) i))
  simp only [jacobiGaps,Matrix.IsHermitian.eigenvalues,e,Equiv.symm_apply_apply] at hh
  calc
    _ = ∑ i, f (2-(jacobi_hermitian (n+1:ℝ)⁻¹ (n+1)).eigenvalues₀ i) :=
      symmetric_eigenvalue_sum_congr (pathOperator_symmetric n) (by simp) finrank_euclideanSpace (fun x => f (2-x))
    _ = _ := by
      simpa only [jacobiGaps,Matrix.IsHermitian.eigenvalues,Nat.cast_add,Nat.cast_one] using hh

lemma orderedJacobi_trace (n : ℕ) {s : ℝ} (hs : 0 < s)
    (hscale : 2 ≤ (n+1:ℝ)*s*Real.sqrt s) :
    (∑ i, (s+orderedJacobiGaps n i)⁻¹^2) ≤ 4*(n+1:ℝ)/Real.sqrt s ∧
    |(∑ i, (s+orderedJacobiGaps n i)⁻¹)/(n+1)-semicircleResolvent s| ≤ 2/((n+1:ℝ)*s) ∧
    (∑ i, (s+orderedJacobiGaps n i)⁻¹) ≤ n+1 := by
  have ht := jacobi_resolvent_estimates (Nat.succ_pos n) hs (by simpa using hscale)
  have hn : (0:ℝ) < n+1 := by positivity
  have hR := semicircleResolvent_le_one hs.le
  rw [sum_orderedJacobiGaps n (fun e => (s+e)⁻¹^2),
    sum_orderedJacobiGaps n (fun e => (s+e)⁻¹)]
  simp only [empiricalResolventSquare,empiricalResolvent,Fintype.card_fin,Nat.cast_succ] at ht
  refine ⟨?_,?_,?_⟩
  · calc
      _ = (n+1:ℝ)*((n+1:ℝ)⁻¹*(∑ i, (s+jacobiGaps (n+1) i)⁻¹^2)) := by field_simp
      _ ≤ (n+1:ℝ)*(4/Real.sqrt s) := mul_le_mul_of_nonneg_left ht.1 hn.le
      _ = _ := by ring
  · rw [div_eq_mul_inv,mul_comm,abs_sub_comm,abs_of_nonneg ht.2.1]
    exact ht.2.2
  · have hsum : (n+1:ℝ)⁻¹*(∑ i, (s+jacobiGaps (n+1) i)⁻¹) ≤ 1 := by linarith [ht.2.1]
    have hmul := mul_le_mul_of_nonneg_left hsum hn.le
    simpa only [← mul_assoc,mul_inv_cancel₀ hn.ne',one_mul,mul_one] using hmul

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_EdgeAsymptotics
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

open scoped BigOperators NNReal

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open Module

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

namespace CriticalSK


open scoped Topology

lemma spectralGood_resolvent (n : ℕ) {lam : Fin (n+1) → ℝ} {h s₀ s : ℝ}
    (hh : 0 ≤ h) (hs₀ : 0 < s₀) (hs : s₀ ≤ s)
    (hsmall : formA n h*s₀^(-5/8:ℝ)+formB n/s₀+formC n ≤ 1/2)
    (hspace : 2 ≤ (n+1:ℝ)*s₀*Real.sqrt s₀)
    (hlam : lam ∈ spectralGood n h s₀) :
    (∀ i, 0 < 2+s-lam i) ∧
    (∑ i, (2+s-lam i)⁻¹^2)/(n+1) ≤ 16/Real.sqrt s ∧
    |(∑ i, (2+s-lam i)⁻¹)/(n+1)-semicircleResolvent s| ≤
      416*formA n h*s^(-1/8:ℝ)+8*formB n/Real.sqrt s+2*formC n+2/((n+1:ℝ)*s) := by
  have hn : (0:ℝ) < n+1 := by positivity
  have hspos : 0 < s := hs₀.trans_le hs
  have hA := formA_nonneg n hh
  have hB := formB_nonneg n
  have hC := formC_nonneg n
  have hsc (t : ℝ) (hst : s ≤ t) : 2 ≤ (n+1:ℝ)*t*Real.sqrt t := by
    have htpos : 0 < t := hspos.trans_le hst
    exact hspace.trans (mul_le_mul (mul_le_mul_of_nonneg_left (hs.trans hst) hn.le)
      (Real.sqrt_le_sqrt (hs.trans hst)) (Real.sqrt_nonneg _) (by positivity))
  have hc := resolvent_trace_transfer (orderedJacobiGaps n) (lam)
    (orderedJacobiGaps_nonneg n) hA hB hC hs₀ hs
    hlam hsmall
    (fun t hst => (orderedJacobi_trace n (hspos.trans_le hst) (hsc t hst)).1)
  have hd := orderedJacobi_trace n hspos (hsc s le_rfl)
  refine ⟨hc.1,?_,?_⟩
  · apply (div_le_iff₀ hn).mpr
    convert hc.2.1 using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | ring
  · have hdif : |(∑ i, (2+s-lam i)⁻¹)/(n+1)-
        (∑ i, (s+orderedJacobiGaps n i)⁻¹)/(n+1)| ≤
        416*formA n h*s^(-1/8:ℝ)+8*formB n/Real.sqrt s+2*formC n := by
      rw [← sub_div,abs_div,abs_of_pos hn]
      apply (div_le_iff₀ hn).mpr
      calc
        _ ≤ _ := hc.2.2
        _ ≤ 104*formA n h*(4*(n+1))*s^(-1/8:ℝ)+2*formB n*(4*(n+1)/Real.sqrt s)+2*formC n*(n+1) := by gcongr; exact hd.2.2
        _ = _ := by ring
    exact (abs_sub_le _ _ _).trans (add_le_add hdif hd.2.1)

lemma traceCost_antitone (n : ℕ) {h s t : ℝ} (hh : 0 ≤ h) (hs : 0 < s) (hst : s ≤ t) :
    traceCost n h t ≤ traceCost n h s := by
  have ht : 0 < t := hs.trans_le hst
  have hA := formA_nonneg n hh
  have hB := formB_nonneg n
  have hC := formC_nonneg n
  have hr := Real.sqrt_le_sqrt hst
  have hsp := Real.sqrt_pos.mpr hs
  unfold traceCost
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hs hst (by norm_num)) (by positivity)
      · exact div_le_div_of_nonneg_left (by positivity) hs hst
    · exact div_le_div_of_nonneg_left (by positivity) hsp hr
  · apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hst (by positivity)) hr hsp.le (by positivity)

lemma traceError_eq_cost (n : ℕ) (h : ℝ) {s : ℝ} (hs : 0 < s) :
    416*formA n h*s^(-1/8:ℝ)+8*formB n/Real.sqrt s+2*formC n+2/((n+1:ℝ)*s) =
      traceCost n h s * Real.sqrt s := by
  have hp : s^(-1/8:ℝ) = s^(-5/8:ℝ)*Real.sqrt s := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_add hs]
    norm_num
  have hsqrt := Real.sqrt_pos.mpr hs
  have hN : (0:ℝ) < n+1 := by positivity
  rw [hp,traceCost]
  field_simp
  linear_combination -(8*formB n*(n+1))*(Real.sq_sqrt hs.le)

lemma spectralGood_relative_trace (n : ℕ) {lam : Fin (n+1) → ℝ} {h s₀ s η : ℝ}
    (hh : 0 ≤ h) (hs₀ : 0 < s₀) (hs : s₀ ≤ s)
    (hsmall : formA n h*s₀^(-5/8:ℝ)+formB n/s₀+formC n ≤ 1/2)
    (hspace : 2 ≤ (n+1:ℝ)*s₀*Real.sqrt s₀)
    (hlam : lam ∈ spectralGood n h s₀) (hcost : traceCost n h s₀ ≤ η) :
    |(∑ i, (2+s-lam i)⁻¹)/(n+1)-semicircleResolvent s| ≤ η*Real.sqrt s := by
  have ht := spectralGood_resolvent n hh hs₀ hs hsmall hspace hlam
  apply ht.2.2.trans
  rw [traceError_eq_cost n h (hs₀.trans_le hs)]
  exact mul_le_mul_of_nonneg_right ((traceCost_antitone n hh hs₀ hs).trans hcost) (Real.sqrt_nonneg _)

lemma traceCost_small (n : ℕ) {h s η : ℝ} (hh : 0 ≤ h) (hs : 0 < s) (hs1 : s ≤ 1)
    (hcost : traceCost n h s ≤ η) :
    formA n h*s^(-5/8:ℝ)+formB n/s+formC n ≤ η := by
  have hA := formA_nonneg n hh
  have hB := formB_nonneg n
  have hC := formC_nonneg n
  have hp : 0 ≤ formA n h*s^(-5/8:ℝ) := by positivity
  have hq : 0 ≤ formB n/s := by positivity
  have hroot : Real.sqrt s ≤ 1 := by simpa using Real.sqrt_le_sqrt hs1
  have hcle : formC n ≤ 2*formC n/Real.sqrt s := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hs)]
    nlinarith [mul_le_mul_of_nonneg_left hroot hC]
  have htail : 0 ≤ 2/((n+1:ℝ)*s*Real.sqrt s) := by positivity
  unfold traceCost at hcost
  have h8 : 8*formB n/s = 8*(formB n/s) := by ring
  rw [h8] at hcost
  nlinarith

open scoped Topology

lemma spectralGood_relative_error (n : ℕ) {lam : Fin (n+1) → ℝ} {h s η : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hs1 : s ≤ 1) (hcost : traceCost n h s ≤ η)
    (hlam : lam ∈ spectralGood n h s) (i : Fin (n+1)) :
    |lam i-(2-orderedJacobiGaps n i)| ≤ η*(s+orderedJacobiGaps n i) := by
  have he := edgeError_relative (formA_nonneg n hh) (formB_nonneg n) (formC_nonneg n)
    hs le_rfl (orderedJacobiGaps_nonneg n i)
  exact (hlam i).trans (he.trans (mul_le_mul_of_nonneg_right (traceCost_small n hh hs hs1 hcost)
    (by linarith [orderedJacobiGaps_nonneg n i])))

lemma spectralGood_top_upper (n : ℕ) {lam : Fin (n+1) → ℝ} {h s η : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hs1 : s ≤ 1) (hη : η ≤ 1)
    (hcost : traceCost n h s ≤ η) (hlam : lam ∈ spectralGood n h s) :
    ∀ i, lam i ≤ 2+η*s := by
  intro i
  have he := (abs_le.mp (spectralGood_relative_error n hh hs hs1 hcost hlam i)).2
  nlinarith [orderedJacobiGaps_nonneg n i]

lemma semicircleResolvent_deficit_lower {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.sqrt s/2 ≤ 1-semicircleResolvent s := by
  have hsroot : s ≤ Real.sqrt s := by
    nlinarith [Real.sq_sqrt hs,Real.sqrt_nonneg s,Real.sqrt_le_sqrt hs1]
  have hc := semicircle_discriminant_lower hs
  unfold semicircleResolvent
  linarith

lemma sum_pair_tail_real {n : ℕ} (v : Fin (n+2) → ℝ) :
    (∑ i, v i) = v 0+v 1+∑ i : Fin n, v i.succ.succ := by
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.succ_zero_eq_one]
  ring

lemma fixedEdgeVariance_coe {ι : Type*} {lam : ι → ℝ} {s : ℝ}
    (hgap : ∀ i, 0 < 2+s-lam i) (i : ι) :
    (fixedEdgeVariance lam s i:ℝ) = (2+s-lam i)⁻¹ :=
  max_eq_right (inv_nonneg.mpr (hgap i).le)

lemma bulk_fixedTilt_bounds {n : ℕ} (v : Fin (n+2) → ℝ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hv : ∀ i, 0 ≤ v i)
    (htrace : |(∑ i, v i)/(n+2)-semicircleResolvent s| ≤ (1/100)*Real.sqrt s)
    (hsq : (∑ i, v i^2) ≤ 16*(n+2)/Real.sqrt s)
    (hmax : ∀ i, v i ≤ 2/s)
    (hspace : 32768 ≤ (n+2:ℝ)*s*Real.sqrt s) :
    let d : ℝ := (n+2)-(∑ i : Fin n, v i.succ.succ)
    (n+2:ℝ)*Real.sqrt s/4 ≤ d ∧ d ≤ 3*(n+2:ℝ)*Real.sqrt s ∧
      128*(∑ i : Fin n, (v i.succ.succ)^2) ≤ d^2 := by
  have hN : (0:ℝ) < n+2 := by positivity
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have ht := abs_le.mp htrace
  have hlowR := semicircleResolvent_deficit_lower hs.le hs1
  have huppR := semicircleResolvent_deficit hs.le
  have hfull_upper : (∑ i, v i) ≤ (n+2)-(n+2)*Real.sqrt s/4 := by
    have hh : (∑ i, v i)/(n+2) ≤ 1-Real.sqrt s/4 := by linarith
    have hm := (div_le_iff₀ hN).mp hh
    nlinarith
  have hfull_lower : (n+2)-(∑ i, v i) ≤ 2*(n+2)*Real.sqrt s := by
    have hh : 1-2*Real.sqrt s ≤ (∑ i, v i)/(n+2) := by linarith
    have hm := (le_div_iff₀ hN).mp hh
    nlinarith
  have hpair_le : v 0+v 1 ≤ (n+2)*Real.sqrt s := by
    have hh : 4/s ≤ (n+2)*Real.sqrt s := by
      rw [div_le_iff₀ hs]
      nlinarith
    have h0 := hmax 0
    have h1 := hmax 1
    ring_nf at h0 h1 hh ⊢
    linarith
  have hsplit := sum_pair_tail_real v
  dsimp only
  have hd : (n+2:ℝ)*Real.sqrt s/4 ≤ (n+2)-(∑ i : Fin n, v i.succ.succ) := by
    linarith [hv 0,hv 1]
  refine ⟨hd,by linarith,?_⟩
  have htail : (∑ i : Fin n, (v i.succ.succ)^2) ≤ (∑ i, v i^2) := by
    rw [sum_pair_tail_real (fun i => v i^2)]
    linarith [sq_nonneg (v 0),sq_nonneg (v 1)]
  have hid : ((n+2:ℝ)*Real.sqrt s/4)^2*Real.sqrt s =
      ((n+2:ℝ)/16)*((n+2:ℝ)*s*Real.sqrt s) := by
    rw [div_pow,mul_pow,Real.sq_sqrt hs.le]
    ring
  have hmid : 2048*(n+2:ℝ)/Real.sqrt s ≤ ((n+2:ℝ)*Real.sqrt s/4)^2 := by
    rw [div_le_iff₀ hr,hid]
    have hh := mul_le_mul_of_nonneg_left hspace (div_nonneg hN.le (by norm_num : (0:ℝ) ≤ 16))
    linarith
  calc
    _ ≤ 128*(16*(n+2:ℝ)/Real.sqrt s) := mul_le_mul_of_nonneg_left (htail.trans hsq) (by norm_num)
    _ = 2048*(n+2:ℝ)/Real.sqrt s := by ring
    _ ≤ ((n+2:ℝ)*Real.sqrt s/4)^2 := hmid
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hd 2

lemma fixedEdgeVariance_upper {ι : Type*} {lam : ι → ℝ} {s : ℝ} (hs : 0 < s)
    (hgap : ∀ i, s/2 ≤ 2+s-lam i) (i : ι) :
    (fixedEdgeVariance lam s i:ℝ) ≤ 2/s := by
  have hp (j : ι) : 0 < 2+s-lam j := lt_of_lt_of_le (by positivity) (hgap j)
  rw [fixedEdgeVariance_coe hp]
  have hh := (inv_le_inv₀ (hp i) (by positivity : (0:ℝ) < s/2)).2 (hgap i)
  simpa only [inv_div,inv_one,one_div] using hh

lemma spectralGood_fixed_variance {n : ℕ} {lam : Fin (n+2) → ℝ} {h s : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hs1 : s ≤ 1)
    (hcost : traceCost (n+1) h s ≤ 1/100) (hlam : lam ∈ spectralGood (n+1) h s)
    (hspace : 32768 ≤ (n+2:ℝ)*s*Real.sqrt s) :
    (∀ i, 0 < 2+s-lam i) ∧
    (∀ i, (fixedEdgeVariance lam s i:ℝ) ≤ 2/s) ∧
    |(∑ i, (fixedEdgeVariance lam s i:ℝ))/(n+2)-semicircleResolvent s| ≤ (1/100)*Real.sqrt s ∧
    (∑ i, (fixedEdgeVariance lam s i:ℝ)^2) ≤ 16*(n+2)/Real.sqrt s := by
  have hup := spectralGood_top_upper (n+1) hh hs hs1 (by norm_num : (1/100:ℝ) ≤ 1) hcost hlam
  have hgap (i) : s/2 ≤ 2+s-lam i := by linarith [hup i]
  have hpos (i) : 0 < 2+s-lam i := lt_of_lt_of_le (by positivity) (hgap i)
  have hsmall : formA (n+1) h*s^(-5/8:ℝ)+formB (n+1)/s+formC (n+1) ≤ 1/2 :=
    (traceCost_small (n+1) hh hs hs1 hcost).trans (by norm_num)
  have hspace' : 2 ≤ (n+1+1:ℝ)*s*Real.sqrt s := by linarith
  have hN : (0:ℝ) < n+2 := by positivity
  have ht := spectralGood_relative_trace (n+1) hh hs le_rfl hsmall
    (by simpa only [Nat.cast_add,Nat.cast_one] using hspace') hlam hcost
  have hq := (spectralGood_resolvent (n+1) hh hs le_rfl hsmall
    (by simpa only [Nat.cast_add,Nat.cast_one] using hspace') hlam).2.1
  simp only [Nat.cast_add,Nat.cast_one,show (n:ℝ)+1+1=n+2 by ring] at ht hq
  refine ⟨hpos,fixedEdgeVariance_upper hs hgap,?_,?_⟩
  · simpa only [fixedEdgeVariance_coe hpos] using ht
  · simp only [fixedEdgeVariance_coe hpos]
    have he := (div_le_iff₀ hN).mp hq
    convert he using 1 <;> first | rfl | ring

lemma spectralGood_fixed_bulk {n : ℕ} {lam : Fin (n+2) → ℝ} {h s : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hs1 : s ≤ 1)
    (hcost : traceCost (n+1) h s ≤ 1/100) (hlam : lam ∈ spectralGood (n+1) h s)
    (hspace : 32768 ≤ (n+2:ℝ)*s*Real.sqrt s) :
    let d : ℝ := (n+2)-(∑ i : Fin n, (fixedEdgeVariance lam s i.succ.succ:ℝ))
    (n+2:ℝ)*Real.sqrt s/4 ≤ d ∧ d ≤ 3*(n+2:ℝ)*Real.sqrt s ∧
      128*(∑ i : Fin n, (fixedEdgeVariance lam s i.succ.succ:ℝ)^2) ≤ d^2 := by
  have hi := spectralGood_fixed_variance hh hs hs1 hcost hlam hspace
  exact bulk_fixedTilt_bounds (fun i => (fixedEdgeVariance lam s i:ℝ)) hs hs1
    (fun i => NNReal.coe_nonneg _) hi.2.2.1 hi.2.2.2 hi.2.1 hspace

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_PartitionBounds
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

open scoped BigOperators NNReal

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open Module

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal BigOperators

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set Real

namespace CriticalSK

lemma fixedBulkDeficit_bounds_s2_oai {n : ℕ} {lam : Fin (n+2) → ℝ} {h s : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hs1 : s ≤ 1)
    (hcost : traceCost (n+1) h s ≤ 1/100) (hlam : lam ∈ spectralGood (n+1) h s)
    (hspace : 32768 ≤ (n+2:ℝ)*s*Real.sqrt s) :
    0 < fixedBulkDeficit lam s ∧ fixedBulkDeficit lam s/(1/(2*s)) ≤ 6*((n+2:ℝ)*s*Real.sqrt s) ∧
    128*(∑ i : Fin n, (fixedEdgeVariance lam s i.succ.succ:ℝ)^2) ≤ (fixedBulkDeficit lam s)^2 := by
  have hi := spectralGood_fixed_bulk hh hs hs1 hcost hlam hspace
  change _ ≤ fixedBulkDeficit lam s ∧ fixedBulkDeficit lam s ≤ _ ∧ _ at hi
  refine ⟨lt_of_lt_of_le (by positivity) hi.1,?_,hi.2.2⟩
  have ht := mul_le_mul_of_nonneg_right hi.2.1 (by positivity : 0 ≤ 2*s)
  simpa only [div_div_eq_mul_div,div_one] using ht.trans_eq (show 3*(n+2:ℝ)*Real.sqrt s*(2*s) = 6*((n+2:ℝ)*s*Real.sqrt s) by ring)

end CriticalSK

end

end OAI
end

theorem solution : type_of% @OAI.CriticalSK.fixedBulkDeficit_bounds_s2_oai := @OAI.CriticalSK.fixedBulkDeficit_bounds_s2_oai
