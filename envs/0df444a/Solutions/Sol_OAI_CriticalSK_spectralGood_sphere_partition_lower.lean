-- Prove2me | solution 1 for OAI.CriticalSK.spectralGood_sphere_partition_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:34:32.781752+00:00
-- url     : https://prove2.me/submissions/a1d7e7be-1c35-4e6b-9a7f-4c20ebd4b9b3

import Mathlib
import Definitions.Def_OAIQWCSK000

section
-- module Solutions.OAIQW_CriticalSK.Compat
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
namespace OAI.CriticalSK
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434


end OAI.CriticalSK
end

section
-- module Solutions.OAIQW_CriticalSK.GaussianMatrices
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
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
-- module Solutions.OAIQW_CriticalSK.PathEnergy
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
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
-- module Solutions.OAIQW_CriticalSK.PathSpectra
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
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
    simp only [neg_div, one_div, inv_pow, id_eq]
  convert! (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => h i)).const_mul
    (Fintype.card ι : ℝ)⁻¹ using 1
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
    simp only [mul_one]
  have hpdd : HasDerivAt (fun u : ℝ => p.derivative.eval (2 + u))
      (p.derivative.derivative.eval (2 + s)) s := by
    convert! (p.derivative.hasDerivAt (2 + s)).comp s ((hasDerivAt_id s).const_add 2) using 1
    simp only [mul_one]
  have hratio : HasDerivAt (fun u : ℝ => (n : ℝ)⁻¹ *
      (p.derivative.eval (2 + u) / p.eval (2 + u)))
      ((n : ℝ)⁻¹ * ((p.derivative.derivative.eval (2 + s) * p.eval (2 + s) -
        p.derivative.eval (2 + s) * p.derivative.eval (2 + s)) / p.eval (2 + s)^2)) s := by
    convert! (hpdd.div hpd hp).const_mul (n : ℝ)⁻¹ using 1
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
-- module Solutions.OAIQW_CriticalSK.Powers
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
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
-- module Solutions.OAIQW_CriticalSK.GaussianMoments
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
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

namespace CriticalSK

lemma gaussian_square_density (t x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (t * x ^ 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * x ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma gaussian_square_integral (t : ℝ) (ht : t < 1 / 2) :
    (∫ x : ℝ, Real.exp (t * x ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul, gaussian_square_density]
  rw [integral_const_mul, integral_gaussian]
  have ha : 0 < 1 / 2 - t := by linarith
  have hb : 0 < 1 - 2 * t := by linarith
  apply (mul_left_inj' (Real.sqrt_ne_zero'.mpr hb)).mp
  rw [inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hb)]
  have he : Real.sqrt (Real.pi / (1 / 2 - t)) * Real.sqrt (1 - 2 * t) =
      Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_mul (by positivity), show Real.pi / (1 / 2 - t) * (1 - 2 * t) =
      2 * Real.pi by field_simp]
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / (1 / 2 - t)) *
        Real.sqrt (1 - 2 * t) = (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (2 * Real.pi) := by
          rw [mul_assoc, he]
    _ = 1 := inv_mul_cancel₀ (by positivity)

lemma gaussian_square_integrable (t : ℝ) (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (t * x ^ 2)) (gaussianReal 0 1) := by
  apply mgf_pos_iff.mp
  change 0 < ∫ x : ℝ, Real.exp (t * x ^ 2) ∂gaussianReal 0 1
  rw [gaussian_square_integral t ht]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))

open Set Filter MeasureTheory ProbabilityTheory

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.Resolvent
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
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
-- module Solutions.OAIQW_CriticalSK.EdgeAsymptotics
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
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

lemma fixedEdgeVariance_pos {ι : Type*} {lam : ι → ℝ} {s : ℝ}
    (hgap : ∀ i, 0 < 2+s-lam i) (i : ι) : fixedEdgeVariance lam s i ≠ 0 := by
  rw [← NNReal.coe_ne_zero,fixedEdgeVariance_coe hgap]
  exact inv_ne_zero (hgap i).ne'

lemma fixedEdgeVariance_inverse {ι : Type*} {lam : ι → ℝ} {s : ℝ}
    (hgap : ∀ i, 0 < 2+s-lam i) (i : ι) :
    (fixedEdgeVariance lam s i:ℝ)⁻¹ = 2+s-lam i := by
  rw [fixedEdgeVariance_coe hgap,inv_inv]

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

lemma fixedEdgeVariance_lower {ι : Type*} {lam : ι → ℝ} {s : ℝ} (hs : 0 < s)
    (hgap : ∀ i, 0 < 2+s-lam i) (i : ι) (hi : |lam i-2| ≤ s/4) :
    1/(2*s) ≤ (fixedEdgeVariance lam s i:ℝ) := by
  rw [fixedEdgeVariance_coe hgap,one_div]
  exact (inv_le_inv₀ (by positivity : (0:ℝ) < 2*s) (hgap i)).2 (by
    have hh := (abs_le.mp hi).1; linarith)

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
    convert he using 1 <;> first | rfl | ring1

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
-- module Solutions.OAIQW_CriticalSK.SphereGeometry
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

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped BigOperators ENNReal Topology
open Set MeasureTheory
open scoped BigOperators ENNReal
open MeasureTheory
namespace CriticalSK


section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable [Nonempty ι]

omit [DecidableEq ι] in
lemma sphereArea_pos : 0 < sphereArea (ι := ι) := by
  exact ENNReal.toReal_pos ((measure_univ_pos.mpr (Measure.toSphere_ne_zero _)).ne')
    (measure_ne_top _ _)

end


section

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma integral_polar (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → ℝ) :
    (∫ x, f x ∂μ) = ∫ p : sphere (0 : E) 1 × Ioi (0 : ℝ),
      f (p.2.val • p.1.val) ∂μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E - 1)) := by
  calc
    _ = ∫ x : ({(0)}ᶜ : Set E), f x.val ∂(μ.comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl f,
        restrict_compl_singleton]
    _ = _ := by
      simpa only [Function.comp_def, Homeomorph.symm_apply_apply, homeomorphUnitSphereProd_symm_apply_coe] using
        μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
          (Homeomorph.measurableEmbedding _) (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) =>
            f ((homeomorphUnitSphereProd E).symm p).val)

lemma radial_map_preserving (μ : Measure E) [μ.IsAddHaarMeasure] :
    MeasurePreserving (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => p.2.val • p.1.val)
      (μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E - 1))) μ := by
  have hs : MeasurePreserving (Subtype.val : ({(0)}ᶜ : Set E) → E)
      (μ.comap Subtype.val) μ := by
    simpa only [restrict_compl_singleton] using
      (measurePreserving_subtype_coe (μa := μ) (measurableSet_singleton (0 : E)).compl)
  exact hs.comp (MeasurePreserving.symm (homeomorphUnitSphereProd E).toMeasurableEquiv
    μ.measurePreserving_homeomorphUnitSphereProd)

end

end

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.SphereSaddle
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

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real

open Finset Real Filter

open scoped Topology

open MeasureTheory Filter Set Real

open scoped ENNReal NNReal BigOperators

open scoped NNReal ENNReal BigOperators
open scoped NNReal ENNReal
open ProbabilityTheory
namespace CriticalSK



section

variable {ι : Type*} [Fintype ι]

lemma gaussianPiPDF_nonneg (v : ι → ℝ≥0) (x : ι → ℝ) : 0 ≤ gaussianPiPDF v x := by
  exact Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)

lemma gaussianPiPDF_integrable (v : ι → ℝ≥0) : Integrable (gaussianPiPDF v) :=
  Integrable.fintype_prod (fun i => integrable_gaussianPDFReal 0 (v i))

lemma gaussianPi_density (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    Measure.pi (fun i => gaussianReal 0 (v i)) =
      volume.withDensity (fun x => ENNReal.ofReal (gaussianPiPDF v x)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal (gaussianPiPDF_integrable v).integrableOn
      (Filter.Eventually.of_forall (gaussianPiPDF_nonneg v))]
  change ENNReal.ofReal (∫ x, gaussianPiPDF v x
      ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict (Set.univ.pi s)) = _
  rw [Measure.restrict_pi_pi]
  simp only [gaussianPiPDF]
  rw [integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro i _
    rw [gaussianReal_of_var_ne_zero _ (hv i), withDensity_apply _ (hs i)]
    exact ofReal_integral_eq_lintegral_ofReal
      (integrable_gaussianPDFReal 0 (v i)).integrableOn
      (Filter.Eventually.of_forall (gaussianPDFReal_nonneg 0 (v i)))
  · intro i _
    exact integral_nonneg (gaussianPDFReal_nonneg 0 (v i))

lemma gaussianPiPDF_continuous (v : ι → ℝ≥0) : Continuous (gaussianPiPDF v) := by
  unfold gaussianPiPDF gaussianPDFReal
  fun_prop

lemma map_density_of_preserving {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {T : X → Y} (hT : MeasurePreserving T μ ν)
    (w : Y → ℝ≥0∞) (hw : Measurable w) :
    (μ.withDensity (fun x => w (T x))).map T = ν.withDensity w := by
  ext A hA
  rw [Measure.map_apply hT.measurable hA, withDensity_apply _ (hT.measurable hA),
    withDensity_apply _ hA]
  exact hT.setLIntegral_comp_preimage hA hw

lemma density_toLp (w : (ι → ℝ) → ℝ≥0∞) (hw : Measurable w) :
    ((volume : Measure (ι → ℝ)).withDensity w).map (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) = volume.withDensity
      (fun x : EuclideanSpace ℝ ι => w (WithLp.ofLp x)) := by
  have hm : Measurable (fun x : EuclideanSpace ℝ ι => w (WithLp.ofLp x)) :=
    hw.comp (WithLp.measurable_ofLp 2 _)
  simpa only [WithLp.ofLp_toLp] using
    map_density_of_preserving (PiLp.volume_preserving_toLp ι)
      (fun x : EuclideanSpace ℝ ι => w (WithLp.ofLp x)) hm

lemma diagonalGaussian_density (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    diagonalGaussian v = volume.withDensity
      (fun x : EuclideanSpace ℝ ι => ENNReal.ofReal (gaussianPiPDF v (WithLp.ofLp x))) := by
  change (Measure.pi (fun i => gaussianReal 0 (v i))).map (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) = _
  rw [gaussianPi_density v hv]
  exact density_toLp _ (gaussianPiPDF_continuous v).measurable.ennreal_ofReal

lemma euclideanGaussianPDF_continuous (v : ι → ℝ≥0) :
    Continuous (fun x : EuclideanSpace ℝ ι => gaussianPiPDF v x) :=
  (gaussianPiPDF_continuous v).comp (PiLp.continuous_ofLp 2 _)

lemma euclideanGaussianPDF_integrable (v : ι → ℝ≥0) :
    Integrable (fun x : EuclideanSpace ℝ ι => gaussianPiPDF v x) := by
  exact (PiLp.volume_preserving_ofLp ι).integrable_comp
    (gaussianPiPDF_integrable v).aestronglyMeasurable |>.mpr (gaussianPiPDF_integrable v)

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma integral_polar_iterated (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ}
    (hf : Integrable f μ) :
    (∫ x, f x ∂μ) = ∫ r : Ioi (0 : ℝ), ∫ u : sphere (0 : E) 1,
      f (r.val • u.val) ∂μ.toSphere ∂volumeIoiPow (Module.finrank ℝ E - 1) := by
  rw [integral_polar μ f]
  exact integral_prod_symm _
    ((radial_map_preserving μ).integrable_comp hf.aestronglyMeasurable |>.mpr hf)

omit [Nontrivial E] in
lemma angular_integral_continuous (μ : Measure E) [μ.IsAddHaarMeasure]
    [ProperSpace E] {f : E → ℝ} (hf : Continuous f) (A : Set (sphere (0 : E) 1)) :
    Continuous (fun r : ℝ => ∫ u : sphere (0 : E) 1, f (r • u.val) ∂μ.toSphere.restrict A) := by
  have h : Continuous (Function.uncurry (fun r : ℝ => fun u : sphere (0 : E) 1 =>
      f (r • u.val))) := hf.comp (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous (μ := μ.toSphere.restrict A) h
      (isCompact_univ : IsCompact (Set.univ : Set (sphere (0 : E) 1))))

lemma integral_polar_real (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ}
    (hf : Integrable f μ) :
    (∫ x, f x ∂μ) = ∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ E - 1) *
      ∫ u : sphere (0 : E) 1, f (r • u.val) ∂μ.toSphere := by
  rw [integral_polar_iterated μ hf, Measure.volumeIoiPow,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rw [integral_subtype_comap measurableSet_Ioi
    (fun r : ℝ => (ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1))).toReal •
      ∫ u : sphere (0 : E) 1, f (r • u.val) ∂μ.toSphere)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
  rfl

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma normShell_measurable (a b : ℝ) : MeasurableSet (normShell (E := E) a b) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma normShell_radial (a b : ℝ) (r : Ioi (0 : ℝ)) (u : sphere (0 : E) 1) :
    r.val • u.val ∈ normShell a b ↔ r.val ∈ Ioc a b := by
  have hu : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  simp only [normShell, Set.mem_ofPred_eq, norm_smul, Real.norm_eq_abs, abs_of_pos r.property.out,
    hu, mul_one, Set.mem_Ioc]

lemma normShell_integral (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ}
    (hf : Integrable f μ) {a b : ℝ} (ha : 0 ≤ a) :
    (∫ x in normShell a b, f x ∂μ) = ∫ r in Ioc a b,
      r ^ (Module.finrank ℝ E - 1) * ∫ u : sphere (0 : E) 1, f (r • u.val) ∂μ.toSphere := by
  rw [← integral_indicator (normShell_measurable a b),
    integral_polar_real μ (hf.indicator (normShell_measurable a b))]
  calc
    _ = ∫ r in Ioi (0 : ℝ), (Ioc a b).indicator
        (fun r => r ^ (Module.finrank ℝ E - 1) *
          ∫ u : sphere (0 : E) 1, f (r • u.val) ∂μ.toSphere) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hh (u : sphere (0 : E) 1) := normShell_radial a b ⟨r, hr⟩ u
      by_cases hab : r ∈ Ioc a b
      · simp only [Set.indicator_of_mem hab]
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun u => Set.indicator_of_mem ((hh u).mpr hab) f)
      · simp only [Set.indicator_of_notMem hab]
        have hz : (∫ u : sphere (0 : E) 1,
            (normShell a b).indicator f (r • u.val) ∂μ.toSphere) = 0 := by
          apply integral_eq_zero_of_ae
          exact Filter.Eventually.of_forall (fun u => Set.indicator_of_notMem
            (fun h => hab ((hh u).mp h)) f)
        rw [hz, mul_zero]
    _ = _ := by
      rw [setIntegral_indicator measurableSet_Ioc]
      have hsub : Ioc a b ⊆ Ioi (0 : ℝ) := fun _ h => lt_of_le_of_lt ha h.1
      rw [Set.inter_eq_right.mpr hsub]

omit [Nontrivial E] in
lemma radialDensity_continuous (μ : Measure E) [μ.IsAddHaarMeasure] [ProperSpace E]
    {f : E → ℝ} (hf : Continuous f) : Continuous (radialDensity μ f) := by
  have h := angular_integral_continuous μ hf Set.univ
  simp only [Measure.restrict_univ] at h
  exact (continuous_id.pow _).mul h

lemma normShell_density (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ}
    (hf : Integrable f μ) (hfn : ∀ x, 0 ≤ f x) {a b : ℝ} (ha : 0 ≤ a) :
    μ.withDensity (fun x => ENNReal.ofReal (f x)) (normShell a b) =
      ENNReal.ofReal (∫ r in Ioc a b, radialDensity μ f r) := by
  rw [withDensity_apply _ (normShell_measurable a b),
    ← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (Filter.Eventually.of_forall hfn),
    normShell_integral μ hf ha]
  rfl

lemma normShell_density_real (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ}
    (hf : Integrable f μ) (hfn : ∀ x, 0 ≤ f x) {a b : ℝ} (ha : 0 ≤ a) :
    (μ.withDensity (fun x => ENNReal.ofReal (f x)) (normShell a b)).toReal =
      ∫ r in Ioc a b, radialDensity μ f r := by
  rw [normShell_density μ hf hfn ha, ENNReal.toReal_ofReal]
  apply setIntegral_nonneg measurableSet_Ioc
  intro r hr
  exact mul_nonneg (pow_nonneg (le_trans ha hr.1.le) _) (integral_nonneg (fun u => hfn _))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma squareNormShell_measurable (s δ : ℝ) : MeasurableSet (squareNormShell (E := E) s δ) :=
  (measurableSet_lt measurable_const (measurable_norm.pow_const 2)).inter
    (measurableSet_le (measurable_norm.pow_const 2) measurable_const)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma squareNormShell_eq {s δ : ℝ} (hs : 0 ≤ s) (hδ : 0 ≤ δ) :
    squareNormShell (E := E) s δ = normShell (Real.sqrt s) (Real.sqrt (s+δ)) := by
  ext x
  have h1 := Real.sq_sqrt hs
  have h2 := Real.sq_sqrt (by linarith : 0 ≤ s+δ)
  have h3 := Real.sqrt_nonneg s
  have h4 := Real.sqrt_nonneg (s+δ)
  have h5 := norm_nonneg x
  change (s < ‖x‖^2 ∧ ‖x‖^2 ≤ s+δ) ↔ (Real.sqrt s < ‖x‖ ∧ ‖x‖ ≤ Real.sqrt (s+δ))
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]

lemma squareNormShell_density_limit (μ : Measure E) [μ.IsAddHaarMeasure] [ProperSpace E]
    {f : E → ℝ} (hf : Integrable f μ) (hfc : Continuous f) (hfn : ∀ x, 0 ≤ f x)
    {s : ℝ} (hs : 0 < s) :
    Filter.Tendsto (fun δ : ℝ =>
      (μ.withDensity (fun x => ENNReal.ofReal (f x)) (squareNormShell s δ)).toReal / δ)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (radialDensity μ f (Real.sqrt s) / (2 * Real.sqrt s))) := by
  have hq := radialDensity_continuous μ hfc
  have hd : HasDerivAt (fun t : ℝ => ∫ r in Real.sqrt s..t, radialDensity μ f r)
      (radialDensity μ f (Real.sqrt s)) (Real.sqrt s) :=
    intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
      hq.stronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt
  have hd' := hd.comp s (Real.hasDerivAt_sqrt hs.ne')
  have hh := hd'.tendsto_slope_zero_right
  simp only [Function.comp_def, mul_one_div] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : 0 < δ := hδ.out
  rw [squareNormShell_eq hs.le hδ0.le,
    normShell_density_real μ hf hfn (Real.sqrt_nonneg _), intervalIntegral.integral_same,
    sub_zero, smul_eq_mul, intervalIntegral.integral_of_le (Real.sqrt_le_sqrt (by linarith))]
  exact mul_comm _ _

end

section

lemma splitPair_preserving (n : ℕ) (μ : Fin (n+2) → Measure ℝ) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (splitPair n) (Measure.pi μ)
      (((μ 0).prod (μ 1)).prod (Measure.pi (fun i => μ i.succ.succ))) := by
  have h1 := measurePreserving_piFinSuccAbove μ 0
  have h2 := (MeasurePreserving.id (μ 0)).prod
    (measurePreserving_piFinSuccAbove (fun i : Fin (n+1) => μ i.succ) 0)
  have h3 := (measurePreserving_prodAssoc (μ 0) (μ 1)
    (Measure.pi fun i : Fin n => μ i.succ.succ)).symm
  exact h3.comp (h2.comp h1)

lemma splitPair_square_sum (n : ℕ) (x : Fin (n+2) → ℝ) :
    (∑ i, x i^2) = x 0^2 + x 1^2 + ∑ i : Fin n, x i.succ.succ^2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.succ_zero_eq_one]
  ring

section

lemma squareDisk_measurable (s : ℝ) : MeasurableSet (squareDisk s) := by
  exact measurableSet_le (by fun_prop) measurable_const

lemma squareAnnulus_measurable (s δ : ℝ) : MeasurableSet (squareAnnulus s δ) := by
  exact (measurableSet_lt measurable_const
    (show Measurable (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) by fun_prop)).inter
    (measurableSet_le (show Measurable (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) by fun_prop) measurable_const)

lemma squareDisk_complex {s : ℝ} (hs : 0 ≤ s) :
    Complex.measurableEquivRealProd ⁻¹' squareDisk s =
      Metric.closedBall (0 : ℂ) (Real.sqrt s) := by
  ext z
  simp only [Set.mem_preimage, squareDisk, Set.mem_ofPred_eq,
    Complex.measurableEquivRealProd_apply, Metric.mem_closedBall, dist_zero_right]
  rw [show z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 by rw [Complex.sq_norm, Complex.normSq_apply]; ring]
  exact (Real.le_sqrt (norm_nonneg _) hs).symm

lemma volume_squareDisk {s : ℝ} (hs : 0 ≤ s) :
    volume (squareDisk s) = ENNReal.ofReal (Real.pi * s) := by
  rw [← Complex.volume_preserving_equiv_real_prod.measure_preimage
    (squareDisk_measurable s).nullMeasurableSet, squareDisk_complex hs, Complex.volume_closedBall,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hs]
  rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, ← ENNReal.ofReal_mul hs, mul_comm]

lemma squareAnnulus_sdiff (s δ : ℝ) :
    squareAnnulus s δ = squareDisk (s+δ) \ squareDisk s := by
  ext p
  simp [squareAnnulus, squareDisk, and_comm]

lemma volume_squareAnnulus {s δ : ℝ} (hs : 0 ≤ s) (hδ : 0 ≤ δ) :
    volume (squareAnnulus s δ) = ENNReal.ofReal (Real.pi * δ) := by
  rw [squareAnnulus_sdiff, measure_sdiff (by
    intro p hp
    change p.1 ^ 2 + p.2 ^ 2 ≤ s at hp
    change p.1 ^ 2 + p.2 ^ 2 ≤ s+δ
    linarith) (squareDisk_measurable s).nullMeasurableSet (by
      rw [volume_squareDisk hs]
      exact ENNReal.ofReal_ne_top)]
  rw [volume_squareDisk (by linarith), volume_squareDisk hs,
    ← ENNReal.ofReal_sub _ (by positivity)]
  congr 1
  ring

lemma gaussianPairPrefactor_nonneg (a b : ℝ≥0) : 0 ≤ gaussianPairPrefactor a b := by
  unfold gaussianPairPrefactor
  positivity

lemma gaussianPair_density (a b : ℝ≥0) (x y : ℝ) :
    gaussianPDFReal 0 a x * gaussianPDFReal 0 b y =
      gaussianPairPrefactor a b * Real.exp (-(x^2/(2*a) + y^2/(2*b))) := by
  simp only [gaussianPDFReal, sub_zero, gaussianPairPrefactor, mul_inv, neg_div]
  rw [show (Real.sqrt (2*Real.pi*a))⁻¹ * Real.exp (-(x^2/(2*a))) *
      ((Real.sqrt (2*Real.pi*b))⁻¹ * Real.exp (-(y^2/(2*b)))) =
      ((Real.sqrt (2*Real.pi*a))⁻¹ * (Real.sqrt (2*Real.pi*b))⁻¹) *
      (Real.exp (-(x^2/(2*a))) * Real.exp (-(y^2/(2*b)))) by ring,
    ← Real.exp_add, ← neg_add]

lemma gaussianPair_density_upper (a b : ℝ≥0) (x y : ℝ) :
    gaussianPDFReal 0 a x * gaussianPDFReal 0 b y ≤ gaussianPairPrefactor a b := by
  rw [gaussianPair_density]
  have h : Real.exp (-(x^2/(2*a) + y^2/(2*b))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left h (gaussianPairPrefactor_nonneg a b)

lemma gaussianPair_density_lower {a b : ℝ≥0} {m R x y : ℝ}
    (hm : 0 < m) (hma : m ≤ a) (hmb : m ≤ b) (hR : x^2+y^2 ≤ R) :
    gaussianPairPrefactor a b * Real.exp (-R/(2*m)) ≤
      gaussianPDFReal 0 a x * gaussianPDFReal 0 b y := by
  rw [gaussianPair_density]
  apply mul_le_mul_of_nonneg_left _ (gaussianPairPrefactor_nonneg a b)
  apply Real.exp_le_exp.mpr
  have hxa : x^2/(2*a) ≤ x^2/(2*m) :=
    div_le_div_of_nonneg_left (sq_nonneg x) (by positivity) (by linarith)
  have hyb : y^2/(2*b) ≤ y^2/(2*m) :=
    div_le_div_of_nonneg_left (sq_nonneg y) (by positivity) (by linarith)
  have hsum : x^2/(2*a) + y^2/(2*b) ≤ R/(2*m) := by
    calc
      _ ≤ x^2/(2*m) + y^2/(2*m) := add_le_add hxa hyb
      _ = (x^2+y^2)/(2*m) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hR (by positivity)
  rw [neg_div]
  exact neg_le_neg hsum

lemma gaussianPair_apply {a b : ℝ≥0} (ha : a ≠ 0) (hb : b ≠ 0) (s : Set (ℝ × ℝ)) :
    ((gaussianReal 0 a).prod (gaussianReal 0 b)) s =
      ∫⁻ p in s, ENNReal.ofReal (gaussianPDFReal 0 a p.1 * gaussianPDFReal 0 b p.2) := by
  rw [gaussianReal_of_var_ne_zero _ ha, gaussianReal_of_var_ne_zero _ hb,
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _),
    withDensity_apply' _ s]
  apply lintegral_congr
  intro p
  exact (ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)).symm

lemma gaussianPair_annulus_lower {a b : ℝ≥0} {m s δ : ℝ}
    (hm : 0 < m) (hma : m ≤ a) (hmb : m ≤ b) (hs : 0 ≤ s) (hδ : 0 ≤ δ) :
    ENNReal.ofReal (Real.pi * δ * gaussianPairPrefactor a b * Real.exp (-(s+δ)/(2*m))) ≤
      ((gaussianReal 0 a).prod (gaussianReal 0 b)) (squareAnnulus s δ) := by
  have ha : a ≠ 0 := by intro h; simp only [h, NNReal.coe_zero] at hma; linarith
  have hb : b ≠ 0 := by intro h; simp only [h, NNReal.coe_zero] at hmb; linarith
  rw [gaussianPair_apply ha hb]
  calc
    _ = ∫⁻ _p in squareAnnulus s δ,
        ENNReal.ofReal (gaussianPairPrefactor a b * Real.exp (-(s+δ)/(2*m))) := by
      rw [lintegral_const, Measure.restrict_apply_univ, volume_squareAnnulus hs hδ,
        ← ENNReal.ofReal_mul (mul_nonneg (gaussianPairPrefactor_nonneg _ _)
          (Real.exp_pos _).le)]
      congr 1
      ring
    _ ≤ _ := by
      apply lintegral_mono_ae
      apply (ae_restrict_iff' (squareAnnulus_measurable s δ)).mpr
      exact ae_of_all _ (fun p hp => ENNReal.ofReal_le_ofReal
        (gaussianPair_density_lower hm hma hmb hp.2))

lemma volume_squareAnnulus_le {s δ : ℝ} (hδ : 0 ≤ δ) :
    volume (squareAnnulus s δ) ≤ ENNReal.ofReal (Real.pi * δ) := by
  by_cases hs : 0 ≤ s
  · exact le_of_eq (volume_squareAnnulus hs hδ)
  · have hsn : s < 0 := lt_of_not_ge hs
    by_cases ht : 0 ≤ s+δ
    · have hsub : squareAnnulus s δ ⊆ squareDisk (s+δ) := fun _ h => h.2
      calc
        _ ≤ volume (squareDisk (s+δ)) := measure_mono hsub
        _ = ENNReal.ofReal (Real.pi*(s+δ)) := volume_squareDisk ht
        _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le)
    · have hset : squareAnnulus s δ = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have hh := add_nonneg (sq_nonneg p.1) (sq_nonneg p.2)
        exact ht (le_trans hh hp.2)
      rw [hset, measure_empty]
      exact bot_le

lemma gaussianPair_annulus_upper_all {a b : ℝ≥0} (ha : a ≠ 0) (hb : b ≠ 0)
    (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((gaussianReal 0 a).prod (gaussianReal 0 b)) (squareAnnulus s δ) ≤
      ENNReal.ofReal (Real.pi * δ * gaussianPairPrefactor a b) := by
  rw [gaussianPair_apply ha hb]
  calc
    _ ≤ ∫⁻ _p in squareAnnulus s δ, ENNReal.ofReal (gaussianPairPrefactor a b) := by
      exact lintegral_mono (fun p => ENNReal.ofReal_le_ofReal (gaussianPair_density_upper a b p.1 p.2))
    _ ≤ ENNReal.ofReal (gaussianPairPrefactor a b) * ENNReal.ofReal (Real.pi * δ) := by
      rw [lintegral_const, Measure.restrict_apply_univ]
      exact mul_le_mul_of_nonneg_left (volume_squareAnnulus_le hδ) bot_le
    _ = _ := by
      rw [← ENNReal.ofReal_mul (gaussianPairPrefactor_nonneg _ _), mul_comm]

variable {Ω : Type*} [MeasurableSpace Ω]

lemma sumSquareShell_measurable {Z : Ω → ℝ} (hZ : Measurable Z) (s δ : ℝ) :
    MeasurableSet (sumSquareShell Z s δ) := by
  have h : Measurable (fun p : (ℝ × ℝ) × Ω => p.1.1^2 + p.1.2^2 + Z p.2) := by fun_prop
  exact (measurableSet_lt measurable_const h).inter (measurableSet_le h measurable_const)

lemma sumSquareShell_apply (μ : Measure (ℝ × ℝ)) (ν : Measure Ω) [SFinite μ] [SFinite ν]
    {Z : Ω → ℝ} (hZ : Measurable Z) (s δ : ℝ) :
    (μ.prod ν) (sumSquareShell Z s δ) = ∫⁻ ω, μ (squareAnnulus (s-Z ω) δ) ∂ν := by
  rw [Measure.prod_apply_symm (sumSquareShell_measurable hZ s δ)]
  apply lintegral_congr
  intro ω
  congr 1
  ext p
  simp only [Set.mem_preimage, sumSquareShell, squareAnnulus, Set.mem_ofPred_eq]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

lemma gaussianPair_bulk_upper {ν : Measure Ω} [IsProbabilityMeasure ν]
    {Z : Ω → ℝ} (hZ : Measurable Z) {a b : ℝ≥0} (ha : a ≠ 0) (hb : b ≠ 0)
    (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (((gaussianReal 0 a).prod (gaussianReal 0 b)).prod ν) (sumSquareShell Z s δ) ≤
      ENNReal.ofReal (Real.pi * δ * gaussianPairPrefactor a b) := by
  rw [sumSquareShell_apply _ _ hZ]
  calc
    _ ≤ ∫⁻ _ : Ω, ENNReal.ofReal (Real.pi * δ * gaussianPairPrefactor a b) ∂ν :=
      lintegral_mono (fun ω => gaussianPair_annulus_upper_all ha hb (s-Z ω) hδ)
    _ = _ := by simp

lemma gaussianPair_bulk_lower {ν : Measure Ω} [IsProbabilityMeasure ν]
    {Z : Ω → ℝ} (hZ : Measurable Z) {a b : ℝ≥0} {m s R δ : ℝ}
    (hm : 0 < m) (hma : m ≤ a) (hmb : m ≤ b) (hδ : 0 ≤ δ) :
    ENNReal.ofReal (Real.pi * δ * gaussianPairPrefactor a b * Real.exp (-(R+δ)/(2*m))) *
      ν {ω | s-R ≤ Z ω ∧ Z ω ≤ s} ≤
      (((gaussianReal 0 a).prod (gaussianReal 0 b)).prod ν) (sumSquareShell Z s δ) := by
  rw [sumSquareShell_apply _ _ hZ]
  let A := {ω | s-R ≤ Z ω ∧ Z ω ≤ s}
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_const hZ).inter (measurableSet_le hZ measurable_const)
  calc
    _ = ∫⁻ _ω in A, ENNReal.ofReal
        (Real.pi * δ * gaussianPairPrefactor a b * Real.exp (-(R+δ)/(2*m))) ∂ν := by
      rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ∫⁻ ω in A, ((gaussianReal 0 a).prod (gaussianReal 0 b))
        (squareAnnulus (s-Z ω) δ) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with ω hω
      apply le_trans _ (gaussianPair_annulus_lower hm hma hmb (sub_nonneg.mpr hω.2) hδ)
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg Real.pi_pos.le hδ) (gaussianPairPrefactor_nonneg _ _))
      apply Real.exp_le_exp.mpr
      apply (div_le_div_iff_of_pos_right (by positivity : 0 < 2*m)).mpr
      linarith [hω.1]
    _ ≤ _ := setLIntegral_le_lintegral _ _

end

section

lemma fourth_power_le_exp (x : ℝ) : x ^ 4 ≤ 32 * Real.exp (x^2/4) := by
  have h := Real.pow_div_factorial_le_exp (x^2/4) (by positivity) 2
  norm_num at h
  nlinarith

lemma gaussian_fourth_integrable : Integrable (fun x : ℝ => x^4) (gaussianReal 0 1) := by
  apply ((gaussian_square_integrable (1/4) (by norm_num)).const_mul 32).mono' (by fun_prop)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ x^4)]
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using fourth_power_le_exp x

lemma gaussian_fourth_bound : (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) ≤ 64 := by
  calc
    _ ≤ ∫ x : ℝ, 32 * Real.exp ((1/4) * x^2) ∂gaussianReal 0 1 :=
      integral_mono gaussian_fourth_integrable
        ((gaussian_square_integrable (1/4) (by norm_num)).const_mul 32)
        (fun x => by simpa only [div_eq_mul_inv, one_mul, mul_comm] using fourth_power_le_exp x)
    _ = 32 * (Real.sqrt (1/2))⁻¹ := by
      rw [integral_const_mul, gaussian_square_integral _ (by norm_num)]
      norm_num
    _ ≤ 64 := by
      have hs : (1/2 : ℝ) ≤ Real.sqrt (1/2) := by
        apply Real.le_sqrt (by norm_num) (by norm_num) |>.mpr
        norm_num
      have hh : (Real.sqrt (1/2))⁻¹ ≤ 2 := by
        calc
          _ ≤ (1/2 : ℝ)⁻¹ := (inv_le_inv₀ (by positivity) (by norm_num)).mpr hs
          _ = 2 := by norm_num
      linarith

lemma gaussian_as_scaled (v : ℝ≥0) : gaussianReal 0 v =
    (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v * x) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.coe_injective
    simp [Real.sq_sqrt v.coe_nonneg]

lemma gaussian_fourth_integrable_var (v : ℝ≥0) :
    Integrable (fun x : ℝ => x^4) (gaussianReal 0 v) := by
  rw [gaussian_as_scaled]
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  simpa only [Function.comp_def, mul_pow] using gaussian_fourth_integrable.const_mul ((Real.sqrt v)^4)

lemma gaussian_fourth_bound_var (v : ℝ≥0) :
    (∫ x : ℝ, x^4 ∂gaussianReal 0 v) ≤ 64 * (v:ℝ)^2 := by
  rw [gaussian_as_scaled, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul]
  have hs : (Real.sqrt (v:ℝ))^4 = (v:ℝ)^2 := by
    rw [show (4:ℕ)=2*2 by rfl, pow_mul, Real.sq_sqrt v.coe_nonneg]
  rw [hs]
  exact (mul_le_mul_of_nonneg_left gaussian_fourth_bound (sq_nonneg (v:ℝ))).trans_eq (mul_comm _ _)

lemma gaussian_square_memLp (v : ℝ≥0) :
    MemLp (fun x : ℝ => x^2) 2 (gaussianReal 0 v) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [← pow_mul] using gaussian_fourth_integrable_var v

lemma gaussian_square_mean (v : ℝ≥0) :
    (∫ x : ℝ, x^2 ∂gaussianReal 0 v) = v := by
  have h := variance_eq_sub (μ := gaussianReal 0 v) (X := id) (memLp_id_gaussianReal 2)
  simpa only [variance_id_gaussianReal, id_eq, Pi.pow_apply, integral_id_gaussianReal,
    zero_pow (by norm_num : 2 ≠ 0), sub_zero] using h.symm

lemma gaussian_square_variance (v : ℝ≥0) :
    Var[(fun x : ℝ => x^2); gaussianReal 0 v] ≤ 64 * (v:ℝ)^2 := by
  rw [variance_eq_sub (gaussian_square_memLp v), gaussian_square_mean]
  have h : (∫ x : ℝ, (x^2)^2 ∂gaussianReal 0 v) ≤ 64 * (v:ℝ)^2 := by
    simpa only [← pow_mul] using gaussian_fourth_bound_var v
  simpa only [Pi.pow_apply] using (sub_le_self _ (sq_nonneg (v:ℝ))).trans h

variable {ι : Type*} [Fintype ι]

lemma piSquareSum_memLp (v : ι → ℝ≥0) :
    MemLp (piSquareSum (ι := ι)) 2 (Measure.pi (fun i => gaussianReal 0 (v i))) := by
  exact memLp_finsetSum _ (fun i _ => (gaussian_square_memLp (v i)).comp_measurePreserving
    (measurePreserving_eval _ i))

lemma piSquareSum_mean (v : ι → ℝ≥0) :
    (∫ x, piSquareSum x ∂Measure.pi (fun i => gaussianReal 0 (v i))) = ∑ i, (v i : ℝ) := by
  unfold piSquareSum
  rw [integral_finsetSum Finset.univ (f := fun (i : ι) (x : ι → ℝ) => x i ^ 2)
    (fun i _ => integrable_comp_eval (μ := fun i => gaussianReal 0 (v i)) (i := i)
      ((gaussian_square_memLp (v i)).integrable (by norm_num)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_comp_eval (μ := fun i => gaussianReal 0 (v i)) (i := i) (f := fun x : ℝ => x^2) (by fun_prop)]
  exact gaussian_square_mean (v i)

lemma piSquareSum_variance (v : ι → ℝ≥0) :
    Var[piSquareSum (ι := ι); Measure.pi (fun i => gaussianReal 0 (v i))] ≤
      64 * ∑ i, (v i : ℝ)^2 := by
  have he : piSquareSum (ι := ι) = ∑ i, (fun x : ι → ℝ => x i^2) := by
    funext x
    simp only [piSquareSum, Finset.sum_apply]
  rw [he, variance_sum_pi (X := fun (_ : ι) (x : ℝ) => x^2)
    (fun i => gaussian_square_memLp (v i)), Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => gaussian_square_variance (v i))

lemma piSquareSum_tail (v : ι → ℝ≥0) {d : ℝ} (hd : 0 < d) :
    (Measure.pi (fun i => gaussianReal 0 (v i))) {x | d ≤ |piSquareSum x - ∑ i, (v i : ℝ)|} ≤
      ENNReal.ofReal (64 * (∑ i, (v i : ℝ)^2) / d^2) := by
  have ht := meas_ge_le_variance_div_sq (piSquareSum_memLp v) hd
  rw [piSquareSum_mean] at ht
  refine ht.trans (ENNReal.ofReal_le_ofReal ?_)
  exact div_le_div_of_nonneg_right (piSquareSum_variance v) (sq_nonneg d)

lemma piSquareSum_bulk_mass (v : ι → ℝ≥0) {s d : ℝ} (hd : 0 < d)
    (hmean : (∑ i, (v i : ℝ)) = s-d)
    (hvar : 128 * (∑ i, (v i : ℝ)^2) ≤ d^2) :
    (1/2 : ℝ≥0∞) ≤ (Measure.pi (fun i => gaussianReal 0 (v i)))
      {x | s-2*d ≤ piSquareSum x ∧ piSquareSum x ≤ s} := by
  let μ := Measure.pi (fun i => gaussianReal 0 (v i))
  let A := {x : ι → ℝ | s-2*d ≤ piSquareSum x ∧ piSquareSum x ≤ s}
  have hA : MeasurableSet A := by
    have hS : Measurable (piSquareSum (ι := ι)) := by unfold piSquareSum; fun_prop
    exact (measurableSet_le measurable_const hS).inter (measurableSet_le hS measurable_const)
  have hsub : Aᶜ ⊆ {x : ι → ℝ | d ≤ |piSquareSum x - ∑ i, (v i : ℝ)|} := by
    intro x hx
    change ¬ (s-2*d ≤ piSquareSum x ∧ piSquareSum x ≤ s) at hx
    rw [Set.mem_ofPred_eq, hmean, le_abs]
    push Not at hx
    by_cases hh : s-2*d ≤ piSquareSum x
    · left; linarith [hx hh]
    · right; linarith
  have ht : μ Aᶜ ≤ (1/2:ℝ≥0∞) := by
    apply (measure_mono hsub).trans ((piSquareSum_tail v hd).trans _)
    rw [show (1/2 : ℝ≥0∞) = ENNReal.ofReal (1/2) by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num]
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    linarith
  have hsum : μ A + μ Aᶜ = 1 := by
    rw [measure_add_measure_compl hA, measure_univ]
  have hfin : μ A ≠ ∞ := measure_ne_top _ _
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add hfin (measure_ne_top _ _), ENNReal.toReal_one] at hreal
  have ht' := ENNReal.toReal_mono (by norm_num : (1/2:ℝ≥0∞) ≠ ∞) ht
  norm_num at ht'
  apply (ENNReal.toReal_le_toReal (by norm_num) hfin).mp
  norm_num
  linarith

end

section

open Set Filter

variable {n : ℕ}

lemma diagonalGaussian_shell_split (v : Fin (n+2) → ℝ≥0) (s δ : ℝ) :
    diagonalGaussian v (squareNormShell s δ) =
      (((gaussianReal 0 (v 0)).prod (gaussianReal 0 (v 1))).prod
        (Measure.pi fun i : Fin n => gaussianReal 0 (v i.succ.succ)))
      (sumSquareShell piSquareSum s δ) := by
  rw [diagonalGaussian, Measure.map_apply (WithLp.measurable_toLp 2 _)
    (squareNormShell_measurable s δ)]
  rw [← (splitPair_preserving n (fun i => gaussianReal 0 (v i))).measure_preimage
    (sumSquareShell_measurable (by unfold piSquareSum; fun_prop) s δ).nullMeasurableSet]
  congr 1
  ext x
  simp only [Set.mem_preimage, squareNormShell, sumSquareShell, Set.mem_ofPred_eq,
    EuclideanSpace.real_norm_sq_eq, splitPair, piSquareSum]
  rw [splitPair_square_sum]

lemma diagonalGaussian_shell_upper (v : Fin (n+2) → ℝ≥0)
    (h0 : v 0 ≠ 0) (h1 : v 1 ≠ 0) (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    diagonalGaussian v (squareNormShell s δ) ≤
      ENNReal.ofReal (Real.pi * δ * gaussianPairPrefactor (v 0) (v 1)) := by
  rw [diagonalGaussian_shell_split]
  exact gaussianPair_bulk_upper (by unfold piSquareSum; fun_prop) h0 h1 s hδ

lemma diagonalGaussian_shell_lower (v : Fin (n+2) → ℝ≥0) {m s d δ : ℝ}
    (hm : 0 < m) (hm0 : m ≤ v 0) (hm1 : m ≤ v 1) (hδ : 0 ≤ δ) (hd : 0 < d)
    (hmean : (∑ i : Fin n, (v i.succ.succ : ℝ)) = s-d)
    (hvar : 128 * (∑ i : Fin n, (v i.succ.succ : ℝ)^2) ≤ d^2) :
    ENNReal.ofReal (Real.pi * δ * gaussianPairPrefactor (v 0) (v 1) *
      Real.exp (-(2*d+δ)/(2*m)) / 2) ≤ diagonalGaussian v (squareNormShell s δ) := by
  rw [diagonalGaussian_shell_split]
  have hl := gaussianPair_bulk_lower
    (ν := Measure.pi fun i : Fin n => gaussianReal 0 (v i.succ.succ))
    (Z := piSquareSum) (by unfold piSquareSum; fun_prop) (s := s) (R := 2*d)
    hm hm0 hm1 hδ
  have hp := piSquareSum_bulk_mass (fun i : Fin n => v i.succ.succ) hd hmean hvar
  apply le_trans _ hl
  calc
    _ = ENNReal.ofReal (Real.pi * δ * gaussianPairPrefactor (v 0) (v 1) *
      Real.exp (-(2*d+δ)/(2*m))) * (1/2 : ℝ≥0∞) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, div_eq_mul_inv]
        congr 1
        norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hp bot_le

lemma diagonalSquareDensity_limit {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun δ : ℝ => (diagonalGaussian v (squareNormShell s δ)).toReal / δ)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (diagonalSquareDensity v s)) := by
  rw [diagonalGaussian_density v hv]
  exact squareNormShell_density_limit volume (euclideanGaussianPDF_integrable v)
    (euclideanGaussianPDF_continuous v) (fun x => gaussianPiPDF_nonneg v x) hs

lemma diagonalSquareDensity_upper (v : Fin (n+2) → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    {s : ℝ} (hs : 0 < s) :
    diagonalSquareDensity v s ≤ Real.pi * gaussianPairPrefactor (v 0) (v 1) := by
  apply le_of_tendsto (diagonalSquareDensity_limit v hv hs)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : 0 < δ := hδ.out
  have h := ENNReal.toReal_mono (ENNReal.ofReal_ne_top)
    (diagonalGaussian_shell_upper v (hv 0) (hv 1) s hδ0.le)
  have hp := gaussianPairPrefactor_nonneg (v 0) (v 1)
  rw [ENNReal.toReal_ofReal (by positivity)] at h
  apply (div_le_iff₀ hδ0).mpr
  nlinarith

lemma diagonalSquareDensity_lower (v : Fin (n+2) → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    {m s d : ℝ} (hs : 0 < s) (hm : 0 < m) (hm0 : m ≤ v 0) (hm1 : m ≤ v 1)
    (hd : 0 < d) (hmean : (∑ i : Fin n, (v i.succ.succ : ℝ)) = s-d)
    (hvar : 128 * (∑ i : Fin n, (v i.succ.succ : ℝ)^2) ≤ d^2) :
    Real.pi * gaussianPairPrefactor (v 0) (v 1) * Real.exp (-d/m) / 2 ≤
      diagonalSquareDensity v s := by
  have hc : Continuous (fun δ : ℝ => Real.pi * gaussianPairPrefactor (v 0) (v 1) *
      Real.exp (-(2*d+δ)/(2*m)) / 2) := by fun_prop
  have ht := (hc.continuousAt (x := 0)).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have ht' : Tendsto (fun δ : ℝ => Real.pi * gaussianPairPrefactor (v 0) (v 1) *
      Real.exp (-(2*d+δ)/(2*m)) / 2) (nhdsWithin 0 (Ioi 0))
      (𝓝 (Real.pi * gaussianPairPrefactor (v 0) (v 1) * Real.exp (-d/m) / 2)) := by
    have he : -(2*d+(0:ℝ))/(2*m) = -d/m := by ring
    simpa only [he] using ht
  apply le_of_tendsto_of_tendsto ht' (diagonalSquareDensity_limit v hv hs)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : 0 < δ := hδ.out
  have h := ENNReal.toReal_mono (measure_ne_top _ _)
    (diagonalGaussian_shell_lower v hm hm0 hm1 hδ0.le hd hmean hvar)
  have hp := gaussianPairPrefactor_nonneg (v 0) (v 1)
  rw [ENNReal.toReal_ofReal (by positivity)] at h
  apply (le_div_iff₀ hδ0).mpr
  nlinarith

end

open Set Filter

end

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma sphereAverage_one : sphereAverage (fun _ : unitSphere ι => (1:ℝ)) = 1 := by
  unfold sphereAverage sphereArea
  simp only [integral_const, smul_eq_mul, mul_one]
  exact div_self (ne_of_gt (sphereArea_pos (ι := ι)))

omit [Nonempty ι] in
lemma gaussianPiPDF_exp (v : ι → ℝ≥0) (x : ι → ℝ) :
    gaussianPiPDF v x = gaussianPiPrefactor v * Real.exp (-∑ i, x i ^ 2 / (2*v i)) := by
  simp only [gaussianPiPDF, gaussianPDFReal, sub_zero, Finset.prod_mul_distrib,
    gaussianPiPrefactor, ← Real.exp_sum, ← Finset.sum_neg_distrib, neg_div]

omit [Nonempty ι] in
lemma gaussianPiPrefactor_pos {v : ι → ℝ≥0} (hv : ∀ i, v i ≠ 0) :
    0 < gaussianPiPrefactor v := by
  apply Finset.prod_pos
  intro i _
  have hvi : 0 < (v i : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (hv i))
  positivity

omit [Nonempty ι] in
lemma unitSphere_sum_sq (u : unitSphere ι) : ∑ i, u.val i ^ 2 = 1 := by
  have hn : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  simpa only [hn, one_pow] using (EuclideanSpace.real_norm_sq_eq u.val).symm

omit [Nonempty ι] in
lemma sphereGaussianPDF {lam : ι → ℝ} {v : ι → ℝ≥0} {z a : ℝ}
    (hq : ∀ i, (v i : ℝ)⁻¹ = z - a * lam i) (r : ℝ) (u : unitSphere ι) :
    gaussianPiPDF v (WithLp.ofLp (r • u.val)) = gaussianPiPrefactor v * Real.exp (-z*r^2/2) *
      Real.exp (a/2 * diagonalEnergy lam (r • u.val)) := by
  rw [gaussianPiPDF_exp, mul_assoc, ← Real.exp_add]
  congr 2
  have hsum : ∑ i, (r • u.val) i ^ 2 / (2 * v i) =
      z*r^2/2 - a/2 * diagonalEnergy lam (r • u.val) := by
    simp only [diagonalEnergy, PiLp.smul_apply, smul_eq_mul]
    calc
      _ = ∑ i, (z*r^2/2 * u.val i^2 - a/2 * (lam i*(r*u.val i)^2)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [div_eq_mul_inv, mul_inv, hq i]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, unitSphere_sum_sq, mul_one,
          ← Finset.mul_sum]
  rw [hsum]
  ring

lemma radialDensity_spherePartition {lam : ι → ℝ} {v : ι → ℝ≥0} {z a : ℝ}
    (hq : ∀ i, (v i : ℝ)⁻¹ = z - a * lam i) (r : ℝ) :
    radialDensity volume (fun x : EuclideanSpace ℝ ι => gaussianPiPDF v x) r =
      r ^ (Fintype.card ι - 1) * gaussianPiPrefactor v * Real.exp (-z*r^2/2) *
      sphereArea (ι := ι) * spherePartition lam a r := by
  unfold radialDensity spherePartition sphereAverage
  simp only [finrank_euclideanSpace]
  simp_rw [sphereGaussianPDF hq]
  rw [integral_const_mul]
  have ha := ne_of_gt (sphereArea_pos (ι := ι))
  field_simp

lemma spherePartition_zero (lam : ι → ℝ) (r : ℝ) : spherePartition lam 0 r = 1 := by
  simpa only [spherePartition, zero_div, zero_mul, Real.exp_zero] using sphereAverage_one (ι := ι)

lemma radialDensity_standard (r : ℝ) :
    radialDensity volume (fun x : EuclideanSpace ℝ ι => gaussianPiPDF (fun _ => 1) x) r =
      r ^ (Fintype.card ι - 1) * gaussianPiPrefactor (fun _ : ι => 1) * Real.exp (-r^2/2) *
      sphereArea (ι := ι) := by
  have h := radialDensity_spherePartition (lam := fun _ : ι => (0:ℝ))
    (v := fun _ => 1) (z := 1) (a := 0) (by norm_num) r
  simpa only [spherePartition_zero, mul_one, neg_mul, one_mul] using h

lemma spherical_radial_ratio {lam : ι → ℝ} {v : ι → ℝ≥0} {z a r : ℝ}
    (hq : ∀ i, (v i : ℝ)⁻¹ = z - a * lam i) (hr : 0 < r) :
    radialDensity volume (fun x : EuclideanSpace ℝ ι => gaussianPiPDF v x) r /
      radialDensity volume (fun x : EuclideanSpace ℝ ι => gaussianPiPDF (fun _ => 1) x) r =
      gaussianPiPrefactor v / gaussianPiPrefactor (fun _ : ι => 1) *
        Real.exp (-(z-1)*r^2/2) * spherePartition lam a r := by
  rw [radialDensity_spherePartition hq, radialDensity_standard]
  have hE : Real.exp (-(z-1)*r^2/2) = Real.exp (-z*r^2/2) / Real.exp (-r^2/2) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hE]
  have h1 := ne_of_gt (gaussianPiPrefactor_pos (v := fun _ : ι => 1) (by simp))
  have h2 := ne_of_gt (sphereArea_pos (ι := ι))
  have h3 := ne_of_gt (pow_pos hr (Fintype.card ι - 1))
  have h4 := ne_of_gt (Real.exp_pos (-r^2/2))
  field_simp

end

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.PartitionBounds
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

section

lemma log_le_square_half {x : ℝ} (hx : 0 < x) : Real.log x ≤ (x^2-1)/2 := by
  have hh := Real.log_le_sub_one_of_pos (sq_pos_of_pos hx)
  rw [Real.log_pow] at hh
  norm_num at hh
  linarith

lemma gaussian_radial_shape_bound (p : ℕ) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hp : (p:ℝ) ≤ R) :
    r^p * Real.exp (-r^2/2) ≤
      Real.exp ((R-p)/2) * (Real.sqrt R)^p * Real.exp (-R/2) := by
  have hs := Real.sqrt_pos.mpr hR
  have hs2 := Real.sq_sqrt hR.le
  let x := r / Real.sqrt R
  have hx : 0 < x := div_pos hr hs
  have hxid : Real.sqrt R*x = r := by dsimp [x]; field_simp
  have hx2 : R*x^2 = r^2 := by nlinarith [sq_nonneg (Real.sqrt R*x-r)]
  have hlog := mul_le_mul_of_nonneg_left (log_le_square_half hx) (Nat.cast_nonneg p : (0:ℝ) ≤ p)
  have hn : 0 ≤ (R-p)*x^2 := mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg x)
  have he : (p:ℝ)*Real.log x-r^2/2 ≤ (R-p)/2-R/2 := by nlinarith
  have he' := Real.exp_le_exp.mpr he
  rw [Real.exp_sub,Real.exp_nat_mul,Real.exp_log hx,Real.exp_sub] at he'
  have he'' : x^p * Real.exp (-r^2/2) ≤ Real.exp ((R-p)/2)*Real.exp (-R/2) := by
    rw [show -r^2/2 = -(r^2/2) by ring, show -R/2 = -(R/2) by ring, Real.exp_neg, Real.exp_neg]
    simpa only [div_eq_mul_inv] using he'
  calc
    r^p * Real.exp (-r^2/2) = (Real.sqrt R)^p*(x^p*Real.exp (-r^2/2)) := by
      rw [← mul_assoc,← mul_pow,hxid]
    _ ≤ (Real.sqrt R)^p*(Real.exp ((R-p)/2)*Real.exp (-R/2)) :=
      mul_le_mul_of_nonneg_left he'' (pow_nonneg hs.le _)
    _ = _ := by ring

open Set Filter

variable {ι : Type*} [Fintype ι]

lemma diagonalGaussian_normSq_integrable (v : ι → ℝ≥0) :
    Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖^2) (diagonalGaussian v) := by
  unfold diagonalGaussian
  apply (integrable_map_measure (by fun_prop) (WithLp.measurable_toLp 2 _).aemeasurable).mpr
  have hi := (piSquareSum_memLp v).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  unfold piSquareSum at hi
  simpa only [Function.comp_def,EuclideanSpace.real_norm_sq_eq] using hi

lemma diagonalGaussian_normSq_mean (v : ι → ℝ≥0) :
    (∫ x : EuclideanSpace ℝ ι, ‖x‖^2 ∂diagonalGaussian v) = ∑ i, (v i : ℝ) := by
  rw [diagonalGaussian,integral_map (WithLp.measurable_toLp 2 _).aemeasurable (by fun_prop)]
  simpa only [EuclideanSpace.real_norm_sq_eq,piSquareSum] using piSquareSum_mean v

lemma diagonalGaussian_singleton_zero [Nonempty ι] (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    diagonalGaussian v ({0} : Set (EuclideanSpace ℝ ι)) = 0 := by
  rw [diagonalGaussian_density v hv]
  exact withDensity_absolutelyContinuous _ _ (measure_singleton 0)

lemma diagonalGaussian_standard_shell_half [Nonempty ι] :
    (1:ℝ)/2 ≤ (diagonalGaussian (fun _ : ι => 1) (normShell 0 (Real.sqrt (2*Fintype.card ι)))).toReal := by
  let μ := diagonalGaussian (fun _ : ι => 1)
  let A : Set (EuclideanSpace ℝ ι) := normShell 0 (Real.sqrt (2*Fintype.card ι))
  have hN : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have htail := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (Eventually.of_forall (fun x : EuclideanSpace ℝ ι => sq_nonneg ‖x‖))
    (diagonalGaussian_normSq_integrable (fun _ => 1)) (2*Fintype.card ι)
  rw [diagonalGaussian_normSq_mean] at htail
  simp only [NNReal.coe_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at htail
  have hcomp : Aᶜ ⊆ ({0} : Set (EuclideanSpace ℝ ι)) ∪ {x | 2*(Fintype.card ι : ℝ) ≤ ‖x‖^2} := by
    intro x hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      change 2*(Fintype.card ι : ℝ) ≤ ‖x‖^2
      have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hh : Real.sqrt (2*Fintype.card ι) < ‖x‖ := by
        by_contra h
        exact hx ⟨hn,le_of_not_gt h⟩
      have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2*Fintype.card ι by positivity)
      have hspos := Real.sqrt_nonneg (2*(Fintype.card ι : ℝ))
      nlinarith
  have hcomp' : μ Aᶜ ≤ μ {x | 2*(Fintype.card ι : ℝ) ≤ ‖x‖^2} := by
    apply (measure_mono hcomp).trans
    apply (measure_union_le _ _).trans
    rw [show μ ({0} : Set (EuclideanSpace ℝ ι)) = 0 from diagonalGaussian_singleton_zero _ (by simp),zero_add]
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hcomp'
  have hsum : (μ A).toReal+(μ Aᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      measure_add_measure_compl (normShell_measurable _ _),measure_univ,ENNReal.toReal_one]
  change 1/2 ≤ (μ A).toReal
  change 2*(Fintype.card ι : ℝ)*(μ {x | 2*(Fintype.card ι : ℝ) ≤ ‖x‖^2}).toReal ≤ Fintype.card ι at htail
  nlinarith

variable (n : ℕ)

lemma diagonalSquareDensity_standard_formula :
    diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2) =
      (Real.sqrt (n+2))^n * gaussianPiPrefactor (fun _ : Fin (n+2) => 1) *
        Real.exp (-(n+2)/2) * sphereArea (ι := Fin (n+2)) / 2 := by
  rw [diagonalSquareDensity,radialDensity_standard]
  simp only [Fintype.card_fin,show n+2-1=n+1 by omega,pow_succ,
    Real.sq_sqrt (show (0:ℝ) ≤ n+2 by positivity)]
  field_simp

lemma standard_radial_density_upper {r : ℝ} (hr : 0 ≤ r) :
    radialDensity volume (fun x : EuclideanSpace ℝ (Fin (n+2)) => gaussianPiPDF (fun _ => 1) x) r ≤
      2*r*Real.exp 1*diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2) := by
  rw [radialDensity_standard,diagonalSquareDensity_standard_formula]
  simp only [Fintype.card_fin,show n+2-1=n+1 by omega,pow_succ]
  rcases hr.eq_or_lt with h | h
  · simp [← h]
  · have hp := gaussian_radial_shape_bound n (by positivity : (0:ℝ) < n+2) h (by linarith : (n:ℝ) ≤ n+2)
    rw [show ((n:ℝ)+2-n)/2=1 by ring] at hp
    have hmul := mul_le_mul_of_nonneg_right hp
      (show 0 ≤ r*gaussianPiPrefactor (fun _ : Fin (n+2) => 1)*sphereArea (ι := Fin (n+2)) by
        exact mul_nonneg (mul_nonneg h.le (gaussianPiPrefactor_pos (by simp)).le) sphereArea_pos.le)
    convert hmul using 1 <;> first | rfl | ring_nf

lemma diagonalSquareDensity_standard_lower :
    1/(4*Real.exp 1*(n+2)) ≤ diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2) := by
  let R := Real.sqrt (2*((n:ℝ)+2))
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R^2 = 2*((n:ℝ)+2) := Real.sq_sqrt (by positivity)
  have hmass := diagonalGaussian_standard_shell_half (ι := Fin (n+2))
  simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat] at hmass
  rw [diagonalGaussian_density _ (by simp),normShell_density_real volume
    (euclideanGaussianPDF_integrable _) (fun x => gaussianPiPDF_nonneg _ x.ofLp) (le_refl 0)] at hmass
  have hi := setIntegral_mono_on (μ := (volume : Measure ℝ)) (s := Ioc 0 R)
    ((radialDensity_continuous volume (euclideanGaussianPDF_continuous (fun _ : Fin (n+2) => 1))).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((show Continuous (fun r : ℝ => 2*r*Real.exp 1*diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2)) by fun_prop).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    measurableSet_Ioc (fun r hr => standard_radial_density_upper n hr.1.le)
  have he : (∫ r in Ioc 0 R, 2*r*Real.exp 1*diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2)) =
      2*((n:ℝ)+2)*Real.exp 1*diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2) := by
    rw [← intervalIntegral.integral_of_le hR,intervalIntegral.integral_mul_const,
      intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul,integral_id]
    rw [hR2]
    ring
  rw [he] at hi
  have hh : 1/2 ≤ 2*((n:ℝ)+2)*Real.exp 1*diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2) :=
    hmass.trans hi
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

end

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma saddleRadius_spec (lam : ι → ℝ) {a : ℝ} (ha : 0 < a) :
    spectralTop lam < saddleRadius lam a ∧ spectralStieltjes lam (saddleRadius lam a) = a := by
  simpa only [saddleRadius,dite_eq_left ha] using (spectralStieltjes_exists lam ha).choose_spec

lemma saddleZ_pos_gap (lam : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    a*spectralTop lam < saddleZ lam a := by
  rcases ha.eq_or_lt with h | h
  · simp [← h,saddleZ]
  · simp only [saddleZ,ite_eq_right h.ne']
    exact mul_lt_mul_of_pos_left (saddleRadius_spec lam h).1 h

lemma saddleZ_gap_pos (lam : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) (i : ι) :
    0 < saddleZ lam a-a*lam i := by
  have h := mul_le_mul_of_nonneg_left (le_spectralTop lam i) ha
  linarith [saddleZ_pos_gap lam ha]

lemma saddleZ_reciprocal_sum (lam : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    ∑ i, (saddleZ lam a-a*lam i)⁻¹ = Fintype.card ι := by
  rcases ha.eq_or_lt with h | h
  · simp [← h,saddleZ]
  · have heq := (saddleRadius_spec lam h).2
    unfold spectralStieltjes at heq
    have hs : ∑ i, (saddleRadius lam a-lam i)⁻¹ = (Fintype.card ι : ℝ)*a := by
      have hN : (Fintype.card ι : ℝ) ≠ 0 := cardinal_pos_real.ne'
      exact (inv_mul_eq_iff_eq_mul₀ hN).mp heq
    simp only [saddleZ,ite_eq_right h.ne',← mul_sub,_root_.mul_inv_rev]
    rw [← Finset.sum_mul, hs]
    field_simp

lemma saddleObjective_min (lam : ι → ℝ) {a z : ℝ} (ha : 0 ≤ a)
    (hz : a*spectralTop lam < z) :
    saddleObjective lam a (saddleZ lam a) ≤ saddleObjective lam a z := by
  have hzpos (i : ι) : 0 < z-a*lam i := by
    have h := mul_le_mul_of_nonneg_left (le_spectralTop lam i) ha
    linarith
  have hl (i : ι) : Real.log (z-a*lam i)-Real.log (saddleZ lam a-a*lam i) ≤
      (z-saddleZ lam a)*(saddleZ lam a-a*lam i)⁻¹ := by
    rw [← Real.log_div (hzpos i).ne' (saddleZ_gap_pos lam ha i).ne']
    have hh := Real.log_le_sub_one_of_pos (div_pos (hzpos i) (saddleZ_gap_pos lam ha i))
    convert hh using 1
    field_simp [(saddleZ_gap_pos lam ha i).ne']
    ring
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hl i)
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,saddleZ_reciprocal_sum lam ha] at hs
  have hN : (0:ℝ) < Fintype.card ι := cardinal_pos_real
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ (2*(Fintype.card ι : ℝ))⁻¹ by positivity)
  unfold saddleObjective
  have he : (2*(Fintype.card ι : ℝ))⁻¹ * ((z-saddleZ lam a)*(Fintype.card ι : ℝ)) =
      (z-saddleZ lam a)/2 := by field_simp
  rw [he] at hm
  linarith

lemma sphericalVariational_eq (lam : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    sphericalVariational lam a = saddleObjective lam a (saddleZ lam a) := by
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨saddleZ lam a,saddleZ_pos_gap lam ha,rfl⟩
  · rintro _ ⟨z,hz,rfl⟩
    exact saddleObjective_min lam ha hz

end

section

open Set

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
lemma gaussianPiPrefactor_log {v : ι → ℝ≥0} (hv : ∀ i, v i ≠ 0) :
    Real.log (gaussianPiPrefactor v) = -(∑ i, Real.log (2*Real.pi*(v i:ℝ)))/2 := by
  unfold gaussianPiPrefactor
  rw [Real.log_prod (fun i _ => inv_ne_zero (Real.sqrt_ne_zero'.mpr (by
    have hi : 0 < (v i : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (hv i))
    positivity)))]
  have hs (i : ι) : Real.log (Real.sqrt (2*Real.pi*(v i:ℝ))) = Real.log (2*Real.pi*(v i:ℝ))/2 :=
    Real.log_sqrt (by positivity)
  simp_rw [Real.log_inv,hs]
  simp only [Finset.sum_neg_distrib,← Finset.sum_div,neg_div]

omit [Nonempty ι] in
lemma gaussianPiPrefactor_log_ratio {v : ι → ℝ≥0} (hv : ∀ i, v i ≠ 0) :
    Real.log (gaussianPiPrefactor v / gaussianPiPrefactor (fun _ : ι => 1)) =
      (∑ i, Real.log ((v i : ℝ)⁻¹))/2 := by
  rw [Real.log_div (gaussianPiPrefactor_pos hv).ne'
    (gaussianPiPrefactor_pos (v := fun _ : ι => 1) (by simp)).ne',
    gaussianPiPrefactor_log hv,gaussianPiPrefactor_log (v := fun _ : ι => 1) (by simp)]
  have hlog (i : ι) : Real.log (2*Real.pi*(v i:ℝ)) = Real.log (2*Real.pi)+Real.log (v i) :=
    Real.log_mul (by positivity) (NNReal.coe_ne_zero.mpr (hv i))
  simp_rw [hlog,NNReal.coe_one,mul_one,Real.log_inv]
  rw [Finset.sum_add_distrib,Finset.sum_neg_distrib]
  ring

lemma spherical_gaussian_identity {lam : ι → ℝ} {v : ι → ℝ≥0} {z a : ℝ}
    (hv : ∀ i, v i ≠ 0) (hq : ∀ i, (v i : ℝ)⁻¹ = z-a*lam i) :
    spherePartition lam a (Real.sqrt (Fintype.card ι)) =
      Real.exp ((Fintype.card ι : ℝ)*saddleObjective lam a z) *
        (diagonalSquareDensity v (Fintype.card ι) /
          diagonalSquareDensity (fun _ : ι => 1) (Fintype.card ι)) := by
  have hN : (0:ℝ) < Fintype.card ι := cardinal_pos_real
  have hs := Real.sqrt_pos.mpr hN
  have hr := spherical_radial_ratio hq hs
  have hp := gaussianPiPrefactor_log_ratio hv
  simp_rw [hq] at hp
  have he : gaussianPiPrefactor v / gaussianPiPrefactor (fun _ : ι => 1) *
      Real.exp (-(z-1)*(Real.sqrt (Fintype.card ι))^2/2) =
      Real.exp (-((Fintype.card ι : ℝ)*saddleObjective lam a z)) := by
    rw [← Real.exp_log (div_pos (gaussianPiPrefactor_pos hv) (gaussianPiPrefactor_pos (by simp))),
      ← Real.exp_add,hp,Real.sq_sqrt hN.le]
    congr 1
    unfold saddleObjective
    field_simp
    ring
  rw [he] at hr
  have hd : diagonalSquareDensity v (Fintype.card ι) /
      diagonalSquareDensity (fun _ : ι => 1) (Fintype.card ι) =
      radialDensity volume (fun x : EuclideanSpace ℝ ι => gaussianPiPDF v x) (Real.sqrt (Fintype.card ι)) /
        radialDensity volume (fun x : EuclideanSpace ℝ ι => gaussianPiPDF (fun _ => 1) x) (Real.sqrt (Fintype.card ι)) := by
    unfold diagonalSquareDensity
    rw [div_div_div_cancel_right₀ (mul_ne_zero two_ne_zero hs.ne')]
  rw [hd,hr,Real.exp_neg]
  field_simp

end

section

open Set

variable {n : ℕ}

lemma diagonalSquareDensity_standard_upper :
    diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2) ≤ 1/2 := by
  have hh := diagonalSquareDensity_upper (fun _ : Fin (n+2) => 1) (by simp)
    (by positivity : (0:ℝ) < n+2)
  have he : Real.pi*gaussianPairPrefactor 1 1 = 1/2 := by
    unfold gaussianPairPrefactor
    norm_num only [NNReal.coe_one,mul_one]
    rw [← sq,Real.sq_sqrt (by positivity)]
    field_simp
  rwa [he] at hh

lemma spherePartition_fixed_lower (lam : Fin (n+2) → ℝ) (v : Fin (n+2) → ℝ≥0)
    {z m d : ℝ} (hv : ∀ i, v i ≠ 0) (hq : ∀ i, (v i:ℝ)⁻¹ = z-lam i)
    (hm : 0 < m) (hm0 : m ≤ v 0) (hm1 : m ≤ v 1) (hd : 0 < d)
    (hmean : (∑ i : Fin n, (v i.succ.succ : ℝ)) = (n+2)-d)
    (hvar : 128*(∑ i : Fin n, (v i.succ.succ : ℝ)^2) ≤ d^2) :
    Real.pi*gaussianPairPrefactor (v 0) (v 1)*Real.exp (-d/m) *
      Real.exp ((n+2)*sphericalVariational lam 1) ≤ spherePartition lam 1 (Real.sqrt (n+2)) := by
  let K := Real.pi*gaussianPairPrefactor (v 0) (v 1)*Real.exp (-d/m)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg Real.pi_pos.le (gaussianPairPrefactor_nonneg _ _)) (Real.exp_pos _).le
  have hlo := diagonalSquareDensity_lower v hv (by positivity : (0:ℝ) < n+2) hm hm0 hm1 hd hmean hvar
  have hstd := diagonalSquareDensity_standard_upper (n := n)
  have hstdpos : 0 < diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2) :=
    lt_of_lt_of_le (by positivity) (diagonalSquareDensity_standard_lower n)
  have hratio : K ≤ diagonalSquareDensity v (n+2) /
      diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2) := by
    apply (le_div_iff₀ hstdpos).mpr
    have hh := mul_le_mul_of_nonneg_left hstd hK
    dsimp only [K] at hh ⊢
    linarith
  have hq' : ∀ i, (v i:ℝ)⁻¹ = z-1*lam i := by simpa only [one_mul] using hq
  have hid := spherical_gaussian_identity hv hq'
  simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat] at hid
  rw [hid]
  have hz : (1:ℝ)*spectralTop lam < z := by
    obtain ⟨i,hi⟩ := spectralTop_attained lam
    have hp : 0 < (v i : ℝ)⁻¹ := inv_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (hv i)))
    rw [hq i,hi] at hp
    linarith
  have hB := saddleObjective_min lam (by norm_num : (0:ℝ) ≤ 1) hz
  rw [← sphericalVariational_eq lam (by norm_num : (0:ℝ) ≤ 1)] at hB
  have hE := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hB (by positivity : (0:ℝ) ≤ n+2))
  have hh := mul_le_mul hratio hE (Real.exp_pos _).le (hK.trans hratio)
  simpa only [K, _root_.mul_comm] using hh

end

lemma gaussianPairPrefactor_lower {a b : ℝ≥0} {c : ℝ} (hc : 0 < c)
    (ha : a ≠ 0) (hb : b ≠ 0) (hac : (a:ℝ) ≤ c) (hbc : (b:ℝ) ≤ c) :
    1/(2*c) ≤ Real.pi*gaussianPairPrefactor a b := by
  have hs : 0 < Real.sqrt (2*Real.pi*a)*Real.sqrt (2*Real.pi*b) := by
    have hapos := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ha)
    have hbpos := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hb)
    positivity
  have ht : Real.sqrt (2*Real.pi*a)*Real.sqrt (2*Real.pi*b) ≤ 2*Real.pi*c := by
    have h1 := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hac (by positivity : 0 ≤ 2*Real.pi))
    have h2 := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hbc (by positivity : 0 ≤ 2*Real.pi))
    have hp := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    simpa only [← sq,Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi*c)] using hp
  have h := mul_le_mul_of_nonneg_left (inv_anti₀ hs ht) Real.pi_pos.le
  unfold gaussianPairPrefactor
  convert h using 1 <;> first | rfl | (field_simp; ring1) | field_simp

lemma fixedBulkDeficit_bounds {n : ℕ} {lam : Fin (n+2) → ℝ} {h s : ℝ}
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

lemma spectralGood_sphere_partition_lower_oai {n : ℕ} {lam : Fin (n+2) → ℝ} {h s : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hs1 : s ≤ 1)
    (hcost : traceCost (n+1) h s ≤ 1/100) (hlam : lam ∈ spectralGood (n+1) h s)
    (hspace : 32768 ≤ (n+2:ℝ)*s*Real.sqrt s)
    (h0 : |lam 0-2| ≤ s/4) (h1 : |lam 1-2| ≤ s/4) :
    (s/4)*Real.exp (-6*((n+2:ℝ)*s*Real.sqrt s))*
      Real.exp ((n+2)*sphericalVariational lam 1) ≤ spherePartition lam 1 (Real.sqrt (n+2)) := by
  have hv := spectralGood_fixed_variance hh hs hs1 hcost hlam hspace
  have hd := fixedBulkDeficit_bounds hh hs hs1 hcost hlam hspace
  have hz (j) : fixedEdgeVariance lam s j ≠ 0 := fixedEdgeVariance_pos hv.1 j
  have hb := spherePartition_fixed_lower (n := n) lam (fixedEdgeVariance lam s) hz
    (fixedEdgeVariance_inverse hv.1) (by positivity : 0 < (1:ℝ)/(2*s))
    (fixedEdgeVariance_lower hs hv.1 0 h0) (fixedEdgeVariance_lower hs hv.1 1 h1) hd.1
    (by unfold fixedBulkDeficit; ring) hd.2.2
  apply le_trans _ hb
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have hc : s/4 ≤ Real.pi*gaussianPairPrefactor (fixedEdgeVariance lam s 0) (fixedEdgeVariance lam s 1) := by
    have hp := gaussianPairPrefactor_lower (by positivity : 0 < 2/s) (hz 0) (hz 1) (hv.2.1 0) (hv.2.1 1)
    convert hp using 1
    field_simp
    ring
  apply mul_le_mul hc _ (Real.exp_pos _).le ((by positivity : (0:ℝ) ≤ s/4).trans hc)
  apply Real.exp_le_exp.mpr
  linarith [hd.2.1]

end CriticalSK

end

end OAI
end

theorem solution : type_of% @OAI.CriticalSK.spectralGood_sphere_partition_lower_oai := @OAI.CriticalSK.spectralGood_sphere_partition_lower_oai
