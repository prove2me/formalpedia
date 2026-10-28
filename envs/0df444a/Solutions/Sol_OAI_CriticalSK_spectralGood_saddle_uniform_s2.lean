-- Prove2me | solution 1 for OAI.CriticalSK.spectralGood_saddle_uniform_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:08:52.317339+00:00
-- url     : https://prove2.me/submissions/040ce751-5f68-4a72-93cb-7054f4e64d00

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
-- module Solutions.OAIQ074_CM.CriticalSK_MinMax
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma basisSpan_finrank {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (s : Finset (Fin n)) :
    finrank ℝ (basisSpan b s) = s.card := by
  have hli : LinearIndependent ℝ (fun i : s => b i) :=
    b.orthonormal.linearIndependent.comp (fun i : s => (i : Fin n)) Subtype.val_injective
  rw [basisSpan, finrank_span_eq_card hli, Fintype.card_coe]

omit [FiniteDimensional ℝ E] in
lemma basisSpan_repr_zero {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (s : Finset (Fin n)) {x : E} (hx : x ∈ basisSpan b s)
    (i : Fin n) (hi : i ∉ s) : b.repr x i = 0 := by
  have hmem : x ∈ Submodule.span ℝ (b.toBasis '' (s : Set (Fin n))) := by
    convert hx using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext y
    simp [Set.mem_range, Set.mem_image]
  have hs := b.toBasis.repr_support_subset_of_mem_span _ hmem
  have hz : b.toBasis.repr x i = 0 := by
    by_contra hz
    exact hi (hs (Finsupp.mem_support_iff.mpr hz))
  simpa only [b.coe_toBasis_repr_apply] using hz

omit [FiniteDimensional ℝ E] in
lemma basis_sum_squares {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (x : E) :
    ∑ i, (b.repr x i) ^ 2 = ‖x‖ ^ 2 := by
  simp only [b.repr_apply_apply]
  exact b.sum_sq_inner_right x

omit [FiniteDimensional ℝ E] in
lemma basisQuadratic_le {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    (s : Finset (Fin n)) {x : E} (hx : x ∈ basisSpan b s) (hunit : ‖x‖ = 1)
    {r : ℝ} (hr : ∀ i ∈ s, a i ≤ r) : basisQuadratic b a x ≤ r := by
  calc
    _ ≤ ∑ i, r * (b.repr x i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ s
      · exact mul_le_mul_of_nonneg_right (hr i hi) (sq_nonneg _)
      · simp [basisSpan_repr_zero b s hx i hi]
    _ = r := by rw [← Finset.mul_sum, basis_sum_squares, hunit]; ring

lemma eigenbasisQuadratic_eq {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    {n : ℕ} (hn : finrank ℝ E = n) (x : E) :
    basisQuadratic (hT.eigenvectorBasis hn) (hT.eigenvalues hn) x = inner ℝ x (T x) := by
  rw [basisQuadratic, ← (hT.eigenvectorBasis hn).sum_inner_mul_inner x (T x)]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm ((hT.eigenvectorBasis hn) i) x, ← (hT.eigenvectorBasis hn).repr_apply_apply,
    ← (hT.eigenvectorBasis hn).repr_apply_apply, hT.eigenvectorBasis_apply_self_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  ring

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

lemma edgeCoeff_nonneg (n i : ℕ) : 0 ≤ edgeCoeff n i := Real.sqrt_nonneg _

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

lemma pathEnergy_le_four_mass (n : ℕ) (u : ℕ → ℝ) :
    pathEnergy n u ≤ 4 * ∑ i ∈ Finset.range (n + 1), u i ^ 2 := by
  have hm1 : (∑ i ∈ Finset.range n, u i ^ 2) ≤ ∑ i ∈ Finset.range (n + 1), u i ^ 2 := by
    rw [Finset.sum_range_succ]
    linarith [sq_nonneg (u n)]
  have hm2 : (∑ i ∈ Finset.range n, u (i + 1) ^ 2) ≤ ∑ i ∈ Finset.range (n + 1), u i ^ 2 := by
    rw [Finset.sum_range_succ']
    linarith [sq_nonneg (u 0)]
  have he : -2 * (∑ i ∈ Finset.range n, edgeCoeff n i * u i * u (i + 1)) ≤
      (∑ i ∈ Finset.range n, u i ^ 2) + (∑ i ∈ Finset.range n, u (i + 1) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have hci := edgeCoeff_le_one n i (Nat.le_of_lt (Finset.mem_range.mp hi))
    have hcn := edgeCoeff_nonneg n i
    have hprod : -2 * u i * u (i + 1) ≤ u i ^ 2 + u (i + 1) ^ 2 := by
      nlinarith [sq_nonneg (u i + u (i + 1))]
    have hmul := mul_le_mul_of_nonneg_left hprod hcn
    have hmass := mul_le_mul_of_nonneg_right hci
      (add_nonneg (sq_nonneg (u i)) (sq_nonneg (u (i + 1))))
    nlinarith
  unfold pathEnergy
  linarith

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

lemma edgeTent_zero_left {m b i : ℕ} (hi : i ≤ b) : edgeTent m b i = 0 := by
  simp [edgeTent, Nat.sub_eq_zero_of_le hi]

lemma edgeTent_zero_right {m b i : ℕ} (hi : b + 4*m ≤ i) : edgeTent m b i = 0 := by
  have h : 4*m ≤ i-b := by omega
  simp [edgeTent, Nat.sub_eq_zero_of_le h]

lemma edgeTent_plateau {m b i : ℕ} (hlo : b+m ≤ i) (hhi : i ≤ b+3*m) :
    edgeTent m b i = m := by
  have h1 : m ≤ i-b := by omega
  have h2 : m ≤ 4*m-(i-b) := by omega
  simp [edgeTent, min_eq_right h1, min_eq_left h2]

lemma edgeTent_lipschitz (m b i : ℕ) : |edgeTent m b (i+1) - edgeTent m b i| ≤ 1 := by
  unfold edgeTent
  rw [abs_le]
  have h1 : min (min (i+1-b) m) (4*m-(i+1-b)) ≤ min (min (i-b) m) (4*m-(i-b)) + 1 := by omega
  have h2 : min (min (i-b) m) (4*m-(i-b)) ≤ min (min (i+1-b) m) (4*m-(i+1-b)) + 1 := by omega
  have hh1 : ((min (min (i+1-b) m) (4*m-(i+1-b)) : ℕ) : ℝ) ≤ ((min (min (i-b) m) (4*m-(i-b)) : ℕ) : ℝ) + 1 := by exact_mod_cast h1
  have hh2 : ((min (min (i-b) m) (4*m-(i-b)) : ℕ) : ℝ) ≤ ((min (min (i+1-b) m) (4*m-(i+1-b)) : ℕ) : ℝ) + 1 := by exact_mod_cast h2
  constructor <;> linarith

lemma edgeTent_gradient_support {m b i : ℕ} (hi : i ∉ Finset.Ico b (b+4*m)) :
    edgeTent m b (i+1) - edgeTent m b i = 0 := by
  simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hi
  rcases hi with hi | hi
  · rw [edgeTent_zero_left (by omega), edgeTent_zero_left (by omega), sub_self]
  · rw [edgeTent_zero_right (by omega), edgeTent_zero_right hi, sub_self]

lemma edgeTent_gradient (m b n : ℕ) :
    (∑ i ∈ Finset.range n, (edgeTent m b (i+1) - edgeTent m b i)^2) ≤ 4 * m := by
  have hpoint (i : ℕ) : (edgeTent m b (i+1) - edgeTent m b i)^2 ≤
      if i ∈ Finset.Ico b (b+4*m) then (1 : ℝ) else 0 := by
    split_ifs with hi
    · have h := edgeTent_lipschitz m b i
      nlinarith [sq_abs (edgeTent m b (i+1) - edgeTent m b i), abs_nonneg (edgeTent m b (i+1) - edgeTent m b i)]
    · rw [edgeTent_gradient_support hi]; norm_num
  calc
    _ ≤ ∑ i ∈ Finset.range n, if i ∈ Finset.Ico b (b+4*m) then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ ≤ ∑ i ∈ Finset.Ico b (b+4*m), (1 : ℝ) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi; exact (Finset.mem_filter.mp hi).2
      · intros; positivity
    _ = 4*m := by simp

lemma edgeTent_mass {m b n : ℕ} (hfit : b+2*m ≤ n+1) :
    (m : ℝ)^3 ≤ ∑ i ∈ Finset.range (n+1), edgeTent m b i ^ 2 := by
  calc
    (m : ℝ)^3 = ∑ i ∈ Finset.Ico (b+m) (b+2*m), (m : ℝ)^2 := by
      have h : b+2*m-(b+m) = m := by omega
      simp only [Finset.sum_const, Nat.card_Ico, h, nsmul_eq_mul]
      ring
    _ = ∑ i ∈ Finset.Ico (b+m) (b+2*m), edgeTent m b i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [edgeTent_plateau (Finset.mem_Ico.mp hi).1 (by have := (Finset.mem_Ico.mp hi).2; omega)]
    _ ≤ ∑ i ∈ Finset.range (n+1), edgeTent m b i ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp only [Finset.mem_range]
        have := (Finset.mem_Ico.mp hi).2
        omega
      · intros; positivity

lemma edgeCoeff_lower (n i : ℕ) (hi : i ≤ n) :
    1 - (i+1 : ℝ)/(n+1) ≤ edgeCoeff n i := by
  have hn : (0 : ℝ) < n+1 := by positivity
  have ht : (i+1 : ℝ) ≤ n+1 := by exact_mod_cast Nat.succ_le_succ hi
  have h0 : 0 ≤ 1 - (i+1 : ℝ)/(n+1) := sub_nonneg.mpr ((div_le_one hn).mpr ht)
  have h1 : 1 - (i+1 : ℝ)/(n+1) ≤ 1 := sub_le_self _ (by positivity)
  dsimp [edgeCoeff]
  have hs := Real.sq_sqrt h0
  nlinarith [Real.sqrt_nonneg (1 - (i+1 : ℝ)/(n+1)), mul_nonneg h0 (sub_nonneg.mpr h1)]

lemma edge_potential_upper {n i : ℕ} (hi : i ≤ n) (hi0 : i ≠ 0) :
    2 - edgeCoeff n i - edgeCoeff n (i-1) ≤ 2*(i+1 : ℝ)/(n+1) := by
  have h1 := edgeCoeff_lower n i hi
  have h2 := edgeCoeff_lower n (i-1) (by omega)
  have h3 : (i-1+1 : ℕ) = i := by omega
  have h4 : ((i-1 : ℕ) : ℝ) + 1 = i := by exact_mod_cast h3
  have h5 : (i : ℝ)/(n+1) ≤ (i+1 : ℝ)/(n+1) := by gcongr; linarith
  rw [h4] at h2
  rw [mul_div_assoc]
  linarith

lemma edgeTent_energy {m b n : ℕ} (_hfit : b+4*m ≤ n) :
    pathEnergy n (edgeTent m b) ≤ 4*m + (2*(b+4*m+1 : ℝ)/(n+1)) *
      (∑ i ∈ Finset.range (n+1), edgeTent m b i ^ 2) := by
  rw [pathEnergy_expansion]
  apply add_le_add
  · calc
      _ ≤ ∑ i ∈ Finset.range n, (edgeTent m b (i+1)-edgeTent m b i)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_of_le_one_left (sq_nonneg _) (edgeCoeff_le_one n i (by have := Finset.mem_range.mp hi; omega))
      _ ≤ 4*m := edgeTent_gradient m b n
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    by_cases hi0 : i = 0
    · subst i; rw [edgeTent_zero_left (by omega)]; simp
    · simp only [ite_eq_right hi0]
      by_cases hit : b+4*m ≤ i
      · rw [edgeTent_zero_right hit]; simp
      · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        apply (edge_potential_upper (by have := Finset.mem_range.mp hi; omega) hi0).trans
        gcongr
        exact_mod_cast (show i ≤ b+4*m by omega)

lemma edgeTent_mul_zero {m b d i : ℕ} (hgap : b+4*m ≤ d) :
    edgeTent m b i * edgeTent m d i = 0 := by
  by_cases h : i ≤ d
  · rw [edgeTent_zero_left h, mul_zero]
  · rw [edgeTent_zero_right (by omega), zero_mul]

lemma edgeTent_adj_mul_zero {m b d i : ℕ} (hgap : b+4*m ≤ d) :
    edgeTent m b i * edgeTent m d (i+1) = 0 := by
  by_cases h : i+1 ≤ d
  · rw [edgeTent_zero_left h, mul_zero]
  · rw [edgeTent_zero_right (by omega), zero_mul]

lemma edgeTent_adj_mul_zero' {m b d i : ℕ} (hgap : b+4*m ≤ d) :
    edgeTent m d i * edgeTent m b (i+1) = 0 := by
  by_cases h : i ≤ d
  · rw [edgeTent_zero_left h, zero_mul]
  · rw [edgeTent_zero_right (m := m) (b := b) (i := i+1) (by omega), mul_zero]

lemma separated_tents {m k l i : ℕ} (hkl : k ≠ l) :
    edgeTent m (4*m*k) i * edgeTent m (4*m*l) i = 0 := by
  rcases lt_or_gt_of_ne hkl with h | h
  · apply edgeTent_mul_zero
    nlinarith
  · rw [mul_comm]
    apply edgeTent_mul_zero
    nlinarith

lemma separated_tents_adj {m k l i : ℕ} (hkl : k ≠ l) :
    edgeTent m (4*m*k) i * edgeTent m (4*m*l) (i+1) = 0 := by
  rcases lt_or_gt_of_ne hkl with h | h
  · apply edgeTent_adj_mul_zero
    nlinarith
  · apply edgeTent_adj_mul_zero'
    nlinarith

lemma sum_mul_diagonal {ι : Type*} [Fintype ι] (u v c : ι → ℝ)
    (huv : ∀ i j, i ≠ j → u i * v j = 0) :
    (∑ i, c i * u i) * (∑ i, c i * v i) = ∑ i, c i ^ 2 * u i * v i := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · ring
  · intro j _ hji
    calc
      _ = (c i * c j) * (u i * v j) := by ring
      _ = 0 := by rw [huv i j hji.symm, mul_zero]
  · simp

lemma tentCombination_sq {r : ℕ} (m : ℕ) (c : Fin r → ℝ) (i : ℕ) :
    tentCombination m c i ^ 2 = ∑ k, c k ^ 2 * edgeTent m (4*m*k.val) i ^ 2 := by
  rw [sq, tentCombination, sum_mul_diagonal]
  · apply Finset.sum_congr rfl
    intros
    ring
  · intro k l hkl
    exact separated_tents (fun h => hkl (Fin.ext h))

lemma tentCombination_adj {r : ℕ} (m : ℕ) (c : Fin r → ℝ) (i : ℕ) :
    tentCombination m c i * tentCombination m c (i+1) =
      ∑ k, c k ^ 2 * edgeTent m (4*m*k.val) i * edgeTent m (4*m*k.val) (i+1) := by
  exact sum_mul_diagonal _ _ _ (fun k l hkl => separated_tents_adj (fun h => hkl (Fin.ext h)))

lemma tentCombination_mass {r : ℕ} (m n : ℕ) (c : Fin r → ℝ) :
    (∑ i ∈ Finset.range (n+1), tentCombination m c i ^ 2) =
      ∑ k, c k ^ 2 * ∑ i ∈ Finset.range (n+1), edgeTent m (4*m*k.val) i ^ 2 := by
  simp only [tentCombination_sq, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma tentCombination_energy {r : ℕ} (m n : ℕ) (c : Fin r → ℝ) :
    pathEnergy n (tentCombination m c) =
      ∑ k, c k ^ 2 * pathEnergy n (edgeTent m (4*m*k.val)) := by
  simp only [pathEnergy, tentCombination_sq, tentCombination_adj,
    mul_assoc, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (s := Finset.range (n+1)), Finset.sum_comm (s := Finset.range n)]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro k _
  · apply Finset.sum_congr rfl
    intros
    ring
  · apply Finset.sum_congr rfl
    intros
    ring

lemma edgeTent_rayleigh {m b n : ℕ} (hm : 0 < m) (hfit : b+4*m ≤ n) :
    pathEnergy n (edgeTent m b) ≤
      (4/(m : ℝ)^2 + 2*(b+4*m+1 : ℝ)/(n+1)) *
        ∑ i ∈ Finset.range (n+1), edgeTent m b i ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmass := edgeTent_mass (m := m) (b := b) (n := n) (by omega)
  have h := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 4/(m : ℝ)^2 by positivity)
  have he : 4/(m : ℝ)^2 * (m : ℝ)^3 = 4*m := by field_simp
  rw [he] at h
  have henergy := edgeTent_energy hfit
  nlinarith

lemma tentCombination_rayleigh {m n r : ℕ} (hm : 0 < m) (hfit : 4*m*r ≤ n)
    (c : Fin r → ℝ) :
    pathEnergy n (tentCombination m c) ≤
      (4/(m : ℝ)^2 + 2*(4*m*r+1 : ℝ)/(n+1)) *
        ∑ i ∈ Finset.range (n+1), tentCombination m c i ^ 2 := by
  rw [tentCombination_mass, tentCombination_energy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hk : 4*m*k.val+4*m ≤ 4*m*r := by nlinarith [k.isLt]
  have h := edgeTent_rayleigh hm (hk.trans hfit)
  have h' : 4/(m : ℝ)^2 + 2*(4*m*k.val+4*m+1 : ℝ)/(n+1) ≤
      4/(m : ℝ)^2 + 2*(4*m*r+1 : ℝ)/(n+1) := by
    gcongr
    exact_mod_cast (by nlinarith [k.isLt] : 4*m*k.val+4*m ≤ 4*m*r)
  push_cast at h
  have hmass : 0 ≤ ∑ i ∈ Finset.range (n+1), edgeTent m (4*m*k.val) i ^ 2 := by positivity
  have hbound := h.trans (mul_le_mul_of_nonneg_right h' hmass)
  have hscaled := mul_le_mul_of_nonneg_left hbound (sq_nonneg (c k))
  convert hscaled using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma tentCombination_probe {m r : ℕ} (c : Fin r → ℝ) (k : Fin r) :
    tentCombination m c (4*m*k.val+m) = c k * m := by
  classical
  rw [tentCombination, Finset.sum_eq_single k]
  · rw [edgeTent_plateau (by omega) (by omega)]
  · intro l _ hlk
    by_cases hm : m = 0
    · subst m
      simp [edgeTent]
    have h := separated_tents (m := m) (i := 4*m*k.val+m)
      (show l.val ≠ k.val from fun h => hlk (Fin.ext h))
    rw [edgeTent_plateau (m := m) (b := 4*m*k.val) (i := 4*m*k.val+m) (by omega) (by omega)] at h
    have hz : edgeTent m (4*m*l.val) (4*m*k.val+m) = 0 :=
      (mul_eq_zero.mp h).resolve_right (by exact_mod_cast hm)
    rw [hz, mul_zero]
  · simp

lemma tentMap_injective {m n r : ℕ} (hm : 0 < m) (hfit : 4*m*r ≤ n) :
    Function.Injective (tentMap m n r) := by
  intro c d h
  funext k
  have hidx : 4*m*k.val+m < n+1 := by nlinarith [k.isLt]
  have he := congrArg (fun u : EuclideanSpace ℝ (Fin (n+1)) =>
    u ⟨4*m*k.val+m, hidx⟩) h
  change tentCombination m c (4*m*k.val+m) = tentCombination m d (4*m*k.val+m) at he
  rw [tentCombination_probe, tentCombination_probe] at he
  exact mul_right_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hm)) he

lemma tentMap_rank {m n r : ℕ} (hm : 0 < m) (hfit : 4*m*r ≤ n) :
    finrank ℝ (LinearMap.range (tentMap m n r)) = r := by
  rw [← LinearEquiv.finrank_eq (LinearEquiv.ofInjective _ (tentMap_injective hm hfit))]
  simp

lemma tentMap_mass (m n r : ℕ) (c : Fin r → ℝ) :
    (∑ i ∈ Finset.range (n+1), tentCombination m c i ^ 2) = ‖tentMap m n r c‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [tentMap, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply,
    Real.norm_eq_abs, sq_abs]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

lemma eigenvalue_lower_of_subspace {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {n : ℕ} (hn : finrank ℝ E = n)
    (S : Submodule ℝ E) (i : Fin n) {a : ℝ}
    (hdim : i.val < finrank ℝ S)
    (hquad : ∀ x : E, x ∈ S → ‖x‖ = 1 → a ≤ inner ℝ x (T x)) :
    a ≤ hT.eigenvalues hn i := by
  let b := hT.eigenvectorBasis hn
  let U := basisSpan b (Finset.Ici i)
  have hnot : ¬ Disjoint S U := by
    intro hd
    have h := Submodule.finrank_add_finrank_le_of_disjoint hd
    rw [show U = basisSpan b (Finset.Ici i) from rfl, basisSpan_finrank,
      Fin.card_Ici, hn] at h
    omega
  rw [Submodule.disjoint_def] at hnot
  push Not at hnot
  obtain ⟨x, hxS, hxU, hx⟩ := hnot
  let y := ‖x‖⁻¹ • x
  have hy : ‖y‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)
  have hlow := hquad y (S.smul_mem _ hxS) hy
  have hupp := basisQuadratic_le b (hT.eigenvalues hn) (Finset.Ici i)
    (U.smul_mem ‖x‖⁻¹ hxU) hy (fun j hj => hT.eigenvalues_antitone hn (Finset.mem_Ici.mp hj))
  rw [eigenbasisQuadratic_eq] at hupp
  exact hlow.trans hupp

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

lemma pathOperator_tent_rayleigh {m n r : ℕ} (hm : 0 < m) (hfit : 4*m*r ≤ n)
    (c : Fin r → ℝ) :
    (2-(4/(m : ℝ)^2 + 2*(4*m*r+1 : ℝ)/(n+1))) * ‖tentMap m n r c‖^2 ≤
      inner ℝ (tentMap m n r c) (pathOperator n (tentMap m n r c)) := by
  have h := tentCombination_rayleigh hm hfit c
  rw [pathEnergy, tentMap_mass] at h
  change _ ≤ inner ℝ (WithLp.toLp 2 (fun i : Fin (n+1) => tentCombination m c i.val))
    (pathOperator n (WithLp.toLp 2 (fun i : Fin (n+1) => tentCombination m c i.val)))
  rw [pathOperator_inner]
  nlinarith

lemma pathOperator_eigenvalue_lower {m n r : ℕ} (hm : 0 < m) (hfit : 4*m*r ≤ n)
    (i : Fin (n+1)) (hi : i.val < r) :
    2-(4/(m : ℝ)^2 + 2*(4*m*r+1 : ℝ)/(n+1)) ≤
      (pathOperator_symmetric n).eigenvalues (by simp) i := by
  apply eigenvalue_lower_of_subspace (pathOperator_symmetric n) (by simp)
    (LinearMap.range (tentMap m n r)) i
  · rw [tentMap_rank hm hfit]
    exact hi
  · rintro x ⟨c, rfl⟩ hx
    have h := pathOperator_tent_rayleigh hm hfit c
    simpa only [hx, one_pow, mul_one] using h

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
-- module Solutions.OAIQ074_CM.CriticalSK_TriNoise
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
open Finset Real
open scoped BigOperators ENNReal Topology
open Set MeasureTheory
open scoped BigOperators ENNReal
open MeasureTheory
open Finset Real Filter
open scoped Topology
namespace CriticalSK

section

lemma dyadic_cube_scale (N : ℕ) (hN : 0 < N) :
    (N : ℝ) ≤ ((2 : ℝ)^(Nat.clog 8 N)) ^ 3 ∧
    ((2 : ℝ)^(Nat.clog 8 N)) ^ 3 ≤ 8 * N := by
  have he : ((2 : ℝ)^Nat.clog 8 N) ^ 3 = (8 : ℝ)^Nat.clog 8 N := by
    rw [← pow_mul, mul_comm (Nat.clog 8 N) 3, pow_mul]
    norm_num
  rw [he]
  constructor
  · exact_mod_cast Nat.le_pow_clog (by decide : 1 < 8) N
  · by_cases hn : N = 1
    · subst N
      norm_num [Nat.clog_one_right]
    · have hn' : 1 < N := by omega
      have hi := Nat.pow_pred_clog_lt_self (by decide : 1 < 8) hn'
      have hj := Nat.clog_pos (by decide : 1 < 8) hn'
      have hid : Nat.clog 8 N = (Nat.clog 8 N).pred + 1 := by
        simpa only [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hj).symm
      rw [hid, pow_succ]
      have hi' : (8 : ℝ)^(Nat.clog 8 N).pred < N := by exact_mod_cast hi
      linarith

end

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

lemma edgeLength_pos (n : ℕ) : 0 < edgeLength n := by unfold edgeLength; positivity

lemma edgeLength_cast_pos (n : ℕ) : (0:ℝ) < edgeLength n := by exact_mod_cast edgeLength_pos n

lemma edgeLength_cube (n : ℕ) : (n+1:ℝ) ≤ (edgeLength n:ℝ)^3 ∧
    (edgeLength n:ℝ)^3 ≤ 8*(n+1:ℝ) := by
  simpa only [edgeLength,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] using
    dyadic_cube_scale (n+1) (Nat.succ_pos n)

lemma naturalEdgeScale_pos (n : ℕ) {L : ℝ} (hL : 0 < L) : 0 < naturalEdgeScale n L := by
  exact div_pos hL (sq_pos_of_pos (edgeLength_cast_pos n))

lemma formA_edgeLength (n : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    formA n h ≤ formConstant*(h+1)*(edgeLength n:ℝ)^(-5/4:ℝ) := by
  let D : ℝ := edgeLength n
  have hD : 0 < D := edgeLength_cast_pos n
  have hN : (0:ℝ) < n+1 := by positivity
  have hroot : Real.sqrt (32*(entryVariance n:ℝ)) ≤
      Real.sqrt (512*(48*Real.exp 1+4))*D^(-3/2:ℝ) := by
    have hfrac : 32*(entryVariance n:ℝ) ≤ (512*(48*Real.exp 1+4))/D^3 := by
      change 32*(2*(48*Real.exp 1+4)/(n+1)) ≤ _
      apply (le_div_iff₀ (pow_pos hD 3)).mpr
      calc
        _ = (64*(48*Real.exp 1+4))*D^3/(n+1) := by ring
        _ ≤ (64*(48*Real.exp 1+4))*(8*(n+1))/(n+1) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (edgeLength_cube n).2 (by positivity)) hN.le
        _ = 512*(48*Real.exp 1+4) := by field_simp; ring
    calc
      _ ≤ Real.sqrt ((512*(48*Real.exp 1+4))/D^3) := Real.sqrt_le_sqrt hfrac
      _ = _ := by
        rw [Real.sqrt_div (by positivity)]
        have hd : Real.sqrt (D^3) = D^(3/2:ℝ) := by
          rw [Real.sqrt_eq_rpow,← Real.rpow_natCast,← Real.rpow_mul hD.le]
          norm_num
        rw [hd,div_eq_mul_inv,← Real.rpow_neg hD.le]
        congr 2; norm_num
  calc
    _ = 41472*Real.sqrt (32*(entryVariance n:ℝ))*(h+1)*D^(1/4:ℝ) := by
      simp only [formA,D,edgeLength,Nat.cast_pow,Nat.cast_ofNat]
    _ ≤ 41472*(Real.sqrt (512*(48*Real.exp 1+4))*D^(-3/2:ℝ))*(h+1)*D^(1/4:ℝ) := by
      gcongr
    _ = formConstant*(h+1)*D^(-5/4:ℝ) := by
      rw [formConstant,show (-5/4:ℝ)=(-3/2:ℝ)+(1/4:ℝ) by norm_num,Real.rpow_add hD]
      ring

lemma formA_natural_scale (n : ℕ) {h L : ℝ} (hh : 0 ≤ h) (hL : 0 < L) :
    formA n h*(naturalEdgeScale n L)^(-5/8:ℝ) ≤ formConstant*(h+1)*L^(-5/8:ℝ) := by
  have hD := edgeLength_cast_pos n
  calc
    _ ≤ (formConstant*(h+1)*(edgeLength n:ℝ)^(-5/4:ℝ))*(naturalEdgeScale n L)^(-5/8:ℝ) := by
      exact mul_le_mul_of_nonneg_right (formA_edgeLength n hh)
        (Real.rpow_nonneg (naturalEdgeScale_pos n hL).le _)
    _ = _ := by
      rw [naturalEdgeScale,Real.div_rpow hL.le (sq_nonneg _),← Real.rpow_natCast,
        ← Real.rpow_mul hD.le]
      norm_num
      field_simp [Real.rpow_ne_zero hD.le hD.ne']

lemma orderedJacobiGaps_top_bound {n m : ℕ} (hm : 0 < m) (hfit : 12*m ≤ n)
    (i : Fin (n+1)) (hi : i.val < 3) :
    orderedJacobiGaps n i ≤ 4/(m:ℝ)^2+2*(12*m+1:ℝ)/(n+1) := by
  have hh := pathOperator_eigenvalue_lower hm (r := 3) (by omega) i hi
  unfold orderedJacobiGaps
  norm_num only [Nat.cast_ofNat] at hh
  rw [show (4:ℝ)*m*3 = 12*m by ring] at hh
  linarith

lemma edgeLength_tendsto : Tendsto (fun n : ℕ => (edgeLength n:ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hn : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  filter_upwards [hn.eventually_ge_atTop ((max b 0)^3)] with n hn'
  by_contra! hb
  have hp := pow_lt_pow_left₀ (hb.trans_le (le_max_left b 0))
    (edgeLength_cast_pos n).le (by norm_num : 3 ≠ 0)
  linarith [(edgeLength_cube n).1]

lemma edgeLength_sq_div_bound (n : ℕ) :
    (edgeLength n:ℝ)^2/(n+1) ≤ 8/(edgeLength n:ℝ) := by
  have hD := edgeLength_cast_pos n
  have hN : (0:ℝ) < n+1 := by positivity
  rw [div_le_div_iff₀ hN hD]
  nlinarith [(edgeLength_cube n).2]

lemma edgeLength_sq_div_tendsto :
    Tendsto (fun n : ℕ => (edgeLength n:ℝ)^2/(n+1)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => by positivity) edgeLength_sq_div_bound
  exact edgeLength_tendsto.const_div_atTop 8

lemma edgeLength_div_sqrt_tendsto :
    Tendsto (fun n : ℕ => (edgeLength n:ℝ)/Real.sqrt (n+1)) atTop (𝓝 0) := by
  have hh := edgeLength_sq_div_tendsto.sqrt
  simpa only [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq (edgeLength_cast_pos _).le,Real.sqrt_zero] using hh

lemma naturalEdgeScale_tendsto (L : ℝ) :
    Tendsto (fun n => naturalEdgeScale n L) atTop (𝓝 0) := by
  exact ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp edgeLength_tendsto).const_div_atTop L

lemma formB_natural_scale_tendsto (L : ℝ) :
    Tendsto (fun n => formB n / naturalEdgeScale n L) atTop (𝓝 0) := by
  have hh := (edgeLength_sq_div_tendsto.const_mul 8).div_const L
  simpa only [mul_zero,zero_div] using hh.congr (fun n => by
    dsimp only [formB,naturalEdgeScale]
    ring_nf; simp only [inv_inv]; ring)

lemma formC_natural_scale_tendsto {L : ℝ} (hL : 0 < L) :
    Tendsto (fun n => formC n / Real.sqrt (naturalEdgeScale n L)) atTop (𝓝 0) := by
  have hh := (edgeLength_div_sqrt_tendsto.const_mul 16).div_const (Real.sqrt L)
  simpa only [mul_zero,zero_div] using hh.congr (fun n => by
    dsimp only [formC,naturalEdgeScale]
    rw [Real.sqrt_div hL.le,Real.sqrt_sq (edgeLength_cast_pos n).le]
    simp only [div_eq_mul_inv,_root_.mul_inv_rev,inv_inv]; ring)

lemma naturalEdgeScale_space (n : ℕ) {L : ℝ} (hL : 0 < L) :
    L*Real.sqrt L/8 ≤ (n+1:ℝ)*naturalEdgeScale n L*Real.sqrt (naturalEdgeScale n L) ∧
    (n+1:ℝ)*naturalEdgeScale n L*Real.sqrt (naturalEdgeScale n L) ≤ L*Real.sqrt L := by
  have hD := edgeLength_cast_pos n
  have he : (n+1:ℝ)*naturalEdgeScale n L*Real.sqrt (naturalEdgeScale n L) =
      (L*Real.sqrt L)*((n+1:ℝ)/(edgeLength n:ℝ)^3) := by
    rw [naturalEdgeScale,Real.sqrt_div hL.le,Real.sqrt_sq hD.le]
    ring
  have hfrac : (1/8:ℝ) ≤ (n+1:ℝ)/(edgeLength n:ℝ)^3 := by
    rw [le_div_iff₀ (pow_pos hD 3)]
    linarith [(edgeLength_cube n).2]
  have hfrac' : (n+1:ℝ)/(edgeLength n:ℝ)^3 ≤ 1 := by
    rw [div_le_one (pow_pos hD 3)]
    exact (edgeLength_cube n).1
  rw [he]
  constructor
  · simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hfrac (by positivity : 0 ≤ L*Real.sqrt L)
  · simpa using mul_le_mul_of_nonneg_left hfrac' (by positivity : 0 ≤ L*Real.sqrt L)

lemma formB_tendsto : Tendsto formB atTop (𝓝 0) := by
  exact (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ)))).const_div_atTop 8

lemma formC_tendsto : Tendsto formC atTop (𝓝 0) := by
  exact (Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ))))).const_div_atTop 16

lemma formA_tendsto {h : ℝ} (hh : 0 ≤ h) : Tendsto (fun n => formA n h) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => formA_nonneg n hh) (fun n => formA_edgeLength n hh)
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 5/4)).comp edgeLength_tendsto
  simpa only [mul_zero,neg_div,Function.comp_def] using ht.const_mul (formConstant*(h+1))

lemma edgeLength_tents_eventually : ∀ᶠ n : ℕ in atTop, 12*edgeLength n ≤ n := by
  have ht := edgeLength_sq_div_tendsto.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/24))
  filter_upwards [ht,eventually_ge_atTop 1] with n hn hn1
  have hD1 : (1:ℝ) ≤ edgeLength n := by exact_mod_cast edgeLength_pos n
  have hN : (0:ℝ) < n+1 := by positivity
  have h' := (div_lt_iff₀ hN).mp hn
  have hn1' : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hr : (12:ℝ)*edgeLength n ≤ n := by nlinarith
  exact_mod_cast hr

lemma orderedJacobiGaps_natural_top {n : ℕ} (hfit : 12*edgeLength n ≤ n)
    (i : Fin (n+1)) (hi : i.val < 3) :
    orderedJacobiGaps n i ≤ 212/(edgeLength n:ℝ)^2 := by
  have hD := edgeLength_cast_pos n
  have hD1 : (1:ℝ) ≤ edgeLength n := by exact_mod_cast edgeLength_pos n
  have hN : (0:ℝ) < n+1 := by positivity
  apply (orderedJacobiGaps_top_bound (edgeLength_pos n) hfit i hi).trans
  have hcube := (edgeLength_cube n).2
  have hmain : 2*(12*(edgeLength n:ℝ)+1)*(edgeLength n:ℝ)^2 ≤ 208*(n+1) := by
    nlinarith [mul_nonneg (sq_nonneg (edgeLength n:ℝ)) (sub_nonneg.mpr hD1)]
  apply (le_div_iff₀ (sq_pos_of_pos hD)).mpr
  have hx := (div_le_iff₀ hN).mpr hmain
  calc
    _ = 4+2*(12*(edgeLength n:ℝ)+1)*(edgeLength n:ℝ)^2/(n+1) := by field_simp
    _ ≤ _ := by linarith



lemma orderedJacobiGaps_le_four (n : ℕ) (i : Fin (n+1)) : orderedJacobiGaps n i ≤ 4 := by
  let h := pathOperator_symmetric n
  let x := h.eigenvectorBasis (by simp) i
  have hx : ‖x‖=1 := (h.eigenvectorBasis (by simp)).norm_eq_one i
  have hh := pathEnergy_le_four_mass n (extendPath n x)
  rw [extendPath_mass,hx] at hh
  have he := pathOperator_energy n x
  have heig : inner ℝ x (pathOperator n x) = h.eigenvalues (by simp) i := by
    dsimp only [x]
    rw [h.apply_eigenvectorBasis,inner_smul_right,real_inner_self_eq_norm_sq]
    simp only [(h.eigenvectorBasis (by simp)).norm_eq_one i,one_pow,mul_one,RCLike.ofReal_real_eq_id,id_eq]
  rw [heig,hx] at he
  unfold orderedJacobiGaps
  linarith

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

lemma traceCost_nonneg (n : ℕ) {h s : ℝ} (hh : 0 ≤ h) (hs : 0 < s) : 0 ≤ traceCost n h s := by
  have := formA_nonneg n hh
  have := formB_nonneg n
  have := formC_nonneg n
  unfold traceCost; positivity

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

lemma traceCost_natural_le (n : ℕ) {h L : ℝ} (hh : 0 ≤ h) (hL : 0 < L) :
    traceCost n h (naturalEdgeScale n L) ≤ edgeFixedCost h L+
      8*(formB n/naturalEdgeScale n L)+2*(formC n/Real.sqrt (naturalEdgeScale n L)) := by
  have hspace := (naturalEdgeScale_space n hL).1
  have hbot : 0 < L*Real.sqrt L/8 := by positivity
  have htail := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2) hbot hspace
  have hA := mul_le_mul_of_nonneg_left (formA_natural_scale n hh hL) (by norm_num : (0:ℝ) ≤ 416)
  rw [show 2/(L*Real.sqrt L/8) = 16/(L*Real.sqrt L) by ring] at htail
  unfold traceCost edgeFixedCost
  ring_nf at hA htail ⊢
  linarith

lemma traceCost_natural_eventually {h L η : ℝ} (hh : 0 ≤ h) (hL : 0 < L)
    (hcost : edgeFixedCost h L < η) :
    ∀ᶠ n : ℕ in atTop, traceCost n h (naturalEdgeScale n L) ≤ η := by
  have ht := ((formB_natural_scale_tendsto L).const_mul 8).add
    ((formC_natural_scale_tendsto hL).const_mul 2)
  have ht' : Tendsto (fun n => 8*(formB n/naturalEdgeScale n L)+
      2*(formC n/Real.sqrt (naturalEdgeScale n L))) atTop (𝓝 0) := by simpa using ht
  filter_upwards [ht'.eventually (gt_mem_nhds (sub_pos.mpr hcost))] with n hn
  linarith [traceCost_natural_le n hh hL]

lemma spectralGood_relative_error (n : ℕ) {lam : Fin (n+1) → ℝ} {h s η : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hs1 : s ≤ 1) (hcost : traceCost n h s ≤ η)
    (hlam : lam ∈ spectralGood n h s) (i : Fin (n+1)) :
    |lam i-(2-orderedJacobiGaps n i)| ≤ η*(s+orderedJacobiGaps n i) := by
  have he := edgeError_relative (formA_nonneg n hh) (formB_nonneg n) (formC_nonneg n)
    hs le_rfl (orderedJacobiGaps_nonneg n i)
  exact (hlam i).trans (he.trans (mul_le_mul_of_nonneg_right (traceCost_small n hh hs hs1 hcost)
    (by linarith [orderedJacobiGaps_nonneg n i])))

lemma spectralGood_bounded (n : ℕ) {lam : Fin (n+1) → ℝ} {h s η : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hs1 : s ≤ 1) (hη : η ≤ 1/5)
    (hcost : traceCost n h s ≤ η) (hlam : lam ∈ spectralGood n h s) :
    ∀ i, |lam i| ≤ 3 := by
  have hη0 := (traceCost_nonneg n hh hs).trans hcost
  intro i
  have he := spectralGood_relative_error n hh hs hs1 hcost hlam i
  have h0 := orderedJacobiGaps_nonneg n i
  have h4 := orderedJacobiGaps_le_four n i
  have hE : η*(s+orderedJacobiGaps n i) ≤ 1 := by nlinarith
  have h := abs_le.mp (he.trans hE)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma spectralGood_top_upper (n : ℕ) {lam : Fin (n+1) → ℝ} {h s η : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hs1 : s ≤ 1) (hη : η ≤ 1)
    (hcost : traceCost n h s ≤ η) (hlam : lam ∈ spectralGood n h s) :
    ∀ i, lam i ≤ 2+η*s := by
  intro i
  have he := (abs_le.mp (spectralGood_relative_error n hh hs hs1 hcost hlam i)).2
  nlinarith [orderedJacobiGaps_nonneg n i]

lemma spectralGood_top_close {n : ℕ} {lam : Fin (n+1) → ℝ} {h L : ℝ}
    (hh : 0 ≤ h) (hL : 1696 ≤ L) (hs1 : naturalEdgeScale n L ≤ 1)
    (hfit : 12*edgeLength n ≤ n) (hcost : traceCost n h (naturalEdgeScale n L) ≤ 1/100)
    (hlam : lam ∈ spectralGood n h (naturalEdgeScale n L))
    (i : Fin (n+1)) (hi : i.val < 3) :
    |lam i-2| ≤ naturalEdgeScale n L/4 := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hs := naturalEdgeScale_pos n hLp
  have hg : orderedJacobiGaps n i ≤ naturalEdgeScale n L/8 := by
    apply (orderedJacobiGaps_natural_top hfit i hi).trans
    calc
      _ ≤ (L/8)/(edgeLength n:ℝ)^2 :=
        div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
      _ = _ := by unfold naturalEdgeScale; ring
  have he := abs_le.mp (spectralGood_relative_error n hh hs hs1 hcost hlam i)
  have hg0 := orderedJacobiGaps_nonneg n i
  exact abs_le.mpr ⟨by linarith,by linarith⟩


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

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma spectralStieltjes_pos (lam : ι → ℝ) {r : ℝ} (hr : spectralTop lam < r) :
    0 < spectralStieltjes lam r := by
  unfold spectralStieltjes
  apply mul_pos (inv_pos.mpr cardinal_pos_real)
  apply Finset.sum_pos (fun i _ => inv_pos.mpr (by linarith [le_spectralTop lam i])) Finset.univ_nonempty

lemma spectralStieltjes_strictAnti (lam : ι → ℝ) : StrictAntiOn (spectralStieltjes lam) (Ioi (spectralTop lam)) := by
  intro r hr s _ hrs
  change spectralTop lam < r at hr
  unfold spectralStieltjes
  apply mul_lt_mul_of_pos_left _ (inv_pos.mpr cardinal_pos_real)
  apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
  intro i _
  exact inv_strictAnti₀ (by linarith [le_spectralTop lam i] : 0 < r-lam i) (by linarith)

lemma spectralStieltjesSlope_neg (lam : ι → ℝ) {r : ℝ} (hr : spectralTop lam < r) :
    spectralStieltjesSlope lam r < 0 := by
  unfold spectralStieltjesSlope
  apply mul_neg_of_neg_of_pos (neg_neg_of_pos (inv_pos.mpr cardinal_pos_real))
  exact Finset.sum_pos (fun i _ => sq_pos_of_pos (inv_pos.mpr (by linarith [le_spectralTop lam i]))) Finset.univ_nonempty

lemma saddleRadius_spec (lam : ι → ℝ) {a : ℝ} (ha : 0 < a) :
    spectralTop lam < saddleRadius lam a ∧ spectralStieltjes lam (saddleRadius lam a) = a := by
  simpa only [saddleRadius,dite_eq_left ha] using (spectralStieltjes_exists lam ha).choose_spec

lemma saddleRadius_unique (lam : ι → ℝ) {a r : ℝ} (hr : spectralTop lam < r)
    (heq : spectralStieltjes lam r = a) : saddleRadius lam a = r := by
  have ha : 0 < a := heq ▸ spectralStieltjes_pos lam hr
  exact (spectralStieltjes_strictAnti lam).injOn (saddleRadius_spec lam ha).1 hr
    ((saddleRadius_spec lam ha).2.trans heq.symm)

lemma saddleRadius_hasStrictDerivAt (lam : ι → ℝ) {a : ℝ} (ha : 0 < a) :
    HasStrictDerivAt (saddleRadius lam) (spectralStieltjesSlope lam (saddleRadius lam a))⁻¹ a := by
  obtain ⟨hr,heq⟩ := saddleRadius_spec lam ha
  have hd := spectralStieltjes_hasStrictDerivAt lam hr
  have hg : ∀ᶠ r in 𝓝 (saddleRadius lam a), saddleRadius lam (spectralStieltjes lam r) = r := by
    filter_upwards [eventually_gt_nhds hr] with r hr
    exact saddleRadius_unique lam hr rfl
  have h := hd.to_local_left_inverse (spectralStieltjesSlope_neg lam hr).ne hg
  rwa [heq] at h

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
    all_goals try with_reducible_and_instances rfl
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

lemma sphericalVariational_radius_expr (lam : ι → ℝ) {a : ℝ} (ha : 0 < a) :
    sphericalVariational lam a = (a*saddleRadius lam a-1)/2-Real.log a/2 -
      (2*(Fintype.card ι : ℝ))⁻¹ * ∑ i, Real.log (saddleRadius lam a-lam i) := by
  rw [sphericalVariational_eq lam ha.le]
  simp only [saddleObjective,saddleZ,ite_eq_right ha.ne',← mul_sub]
  have hr := (saddleRadius_spec lam ha).1
  have he (i : ι) := Real.log_mul ha.ne' (ne_of_gt (show 0 < saddleRadius lam a-lam i by linarith [le_spectralTop lam i]))
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hN : (Fintype.card ι : ℝ) ≠ 0 := cardinal_pos_real.ne'
  field_simp
  ring

lemma sphericalVariational_hasDerivAt (lam : ι → ℝ) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (sphericalVariational lam) ((saddleRadius lam a-a⁻¹)/2) a := by
  let r := saddleRadius lam
  let d := (spectralStieltjesSlope lam (r a))⁻¹
  have hr : HasDerivAt r d a := (saddleRadius_hasStrictDerivAt lam ha).hasDerivAt
  have hpos (i : ι) : 0 < r a-lam i := by
    have hs := (saddleRadius_spec lam ha).1
    dsimp [r]
    linarith [le_spectralTop lam i]
  have hlog (i : ι) := (hr.sub_const (lam i)).log (hpos i).ne'
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun i _ => hlog i)
  have hd := (((hasDerivAt_id a).mul hr).sub_const 1).div_const 2
  have hd := (hd.sub ((hasDerivAt_log ha.ne').div_const 2)).sub
    (hsum.const_mul (2*(Fintype.card ι : ℝ))⁻¹)
  have heq : ∀ᶠ b in 𝓝 a, sphericalVariational lam b =
      (b*r b-1)/2-Real.log b/2 - (2*(Fintype.card ι : ℝ))⁻¹*∑ i, Real.log (r b-lam i) := by
    filter_upwards [eventually_gt_nhds ha] with b hb
    exact sphericalVariational_radius_expr lam hb
  simp only [Pi.mul_apply, Finset.sum_apply, id_eq] at hd
  have hres := hd.congr_of_eventuallyEq heq
  have hs := (saddleRadius_spec lam ha).2
  unfold spectralStieltjes at hs
  have hN : (Fintype.card ι : ℝ) ≠ 0 := cardinal_pos_real.ne'
  have hs' : ∑ i, (r a-lam i)⁻¹ = (Fintype.card ι : ℝ)*a :=
    (inv_mul_eq_iff_eq_mul₀ hN).mp hs
  convert! hres using 1
  all_goals try with_reducible_and_instances rfl
  simp only [div_eq_mul_inv,← Finset.mul_sum,hs']
  field_simp
  ring

lemma saddleZ_weighted_identity (lam : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (saddleZ lam a-1)*(Fintype.card ι : ℝ) =
      a*∑ i, lam i*(saddleZ lam a-a*lam i)⁻¹ := by
  have h (i : ι) : saddleZ lam a*(saddleZ lam a-a*lam i)⁻¹ -
      a*(lam i*(saddleZ lam a-a*lam i)⁻¹) = 1 := by
    rw [← mul_assoc,← sub_mul,mul_inv_cancel₀ (saddleZ_gap_pos lam ha i).ne']
  have hs := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h i)
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,
    saddleZ_reciprocal_sum lam ha,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hs
  linarith

lemma sphericalVariational_slope_bound (lam : ι → ℝ) {a C : ℝ} (ha : 0 < a)
    (hlam : ∀ i, |lam i| ≤ C) : |(saddleRadius lam a-a⁻¹)/2| ≤ C/2 := by
  have hN : (0:ℝ) < Fintype.card ι := cardinal_pos_real
  have hw := saddleZ_weighted_identity lam ha.le
  have hb : |∑ i, lam i*(saddleZ lam a-a*lam i)⁻¹| ≤ C*(Fintype.card ι : ℝ) := by
    calc
      _ ≤ ∑ i, |lam i*(saddleZ lam a-a*lam i)⁻¹| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, C*(saddleZ lam a-a*lam i)⁻¹ := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul,abs_of_pos (inv_pos.mpr (saddleZ_gap_pos lam ha.le i))]
        exact mul_le_mul_of_nonneg_right (hlam i) (inv_pos.mpr (saddleZ_gap_pos lam ha.le i)).le
      _ = _ := by rw [← Finset.mul_sum,saddleZ_reciprocal_sum lam ha.le]
  have hwb := congrArg abs hw
  rw [abs_mul,abs_of_pos hN,abs_mul,abs_of_pos ha] at hwb
  have hzbound : |saddleZ lam a-1| ≤ a*C := by nlinarith
  have heq : (saddleRadius lam a-a⁻¹)/2 = (saddleZ lam a-1)/(2*a) := by
    simp only [saddleZ,ite_eq_right ha.ne']
    field_simp
  rw [heq,abs_div,abs_of_pos (by positivity : 0 < 2*a)]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

end

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_SaddleLimit
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

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma saddleRadius_le_iff (lam : ι → ℝ) {a r : ℝ} (ha : 0 < a) (hr : spectralTop lam < r) :
    saddleRadius lam a ≤ r ↔ spectralStieltjes lam r ≤ a := by
  have hs := saddleRadius_spec lam ha
  constructor
  · intro h
    rw [← hs.2]
    exact (spectralStieltjes_strictAnti lam).antitoneOn hs.1 hr h
  · intro h
    by_contra hc
    have he := spectralStieltjes_strictAnti lam hr hs.1 (lt_of_not_ge hc)
    rw [hs.2] at he
    exact (not_lt_of_ge h) he

lemma le_saddleRadius_iff (lam : ι → ℝ) {a r : ℝ} (ha : 0 < a) (hr : spectralTop lam < r) :
    r ≤ saddleRadius lam a ↔ a ≤ spectralStieltjes lam r := by
  have hs := saddleRadius_spec lam ha
  constructor
  · intro h
    rw [← hs.2]
    exact (spectralStieltjes_strictAnti lam).antitoneOn hr hs.1 h
  · intro h
    by_contra hc
    have he := spectralStieltjes_strictAnti lam hs.1 hr (lt_of_not_ge hc)
    rw [hs.2] at he
    exact (not_lt_of_ge h) he

lemma semicircleResolvent_gt_from_inverse {s x : ℝ} (hs : 0 < s) (hx : x ≤ 1)
    (h : s*x < (1-x)^2) : x < semicircleResolvent s := by
  have hsq := Real.sq_sqrt (show 0 ≤ s*(4+s) by positivity)
  have hp : 0 < 2+s-2*x := by linarith
  have hr : Real.sqrt (s*(4+s)) < 2+s-2*x := by nlinarith
  unfold semicircleResolvent
  linarith

end

section

lemma semicircleResolvent_lt_from_inverse {s x : ℝ} (hs : 0 < s) (hx : x ≤ 1)
    (h : (1-x)^2 < s*x) : semicircleResolvent s < x := by
  have hsq := Real.sq_sqrt (show 0 ≤ s*(4+s) by positivity)
  have hn := Real.sqrt_nonneg (s*(4+s))
  have hp : 0 < 2+s-2*x := by linarith
  have hr : 2+s-2*x < Real.sqrt (s*(4+s)) := by nlinarith
  unfold semicircleResolvent
  linarith

lemma subcritical_radius_gap {a : ℝ} (ha : 0 < a) (ha1 : a < 1) : 2 < a+a⁻¹ := by
  have hsq : 0 < (1-a)^2 := sq_pos_of_pos (by linarith)
  have heq : (a+a⁻¹-2)*a = (1-a)^2 := by field_simp; ring
  nlinarith

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]

lemma saddleRadius_subcritical_tendsto (lam : (n : ℕ) → ι n → ℝ)
    (htop : Tendsto (fun n => spectralTop (lam n)) atTop (𝓝 2))
    (hres : ∀ s > 0, Tendsto (fun n => spectralStieltjes (lam n) (2+s)) atTop (𝓝 (semicircleResolvent s)))
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun n => saddleRadius (lam n) a) atTop (𝓝 (a+a⁻¹)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := min (ε/2) ((a+a⁻¹-2)/2)
  have hδ : 0 < δ := lt_min (by positivity) (by linarith [subcritical_radius_gap ha ha1])
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδr : δ ≤ (a+a⁻¹-2)/2 := min_le_right _ _
  have hminus : 0 < a+a⁻¹-2-δ := by linarith
  have hplus : 0 < a+a⁻¹-2+δ := by linarith
  have he : (a+a⁻¹-2)*a = (1-a)^2 := by field_simp; ring
  have hRm : a < semicircleResolvent (a+a⁻¹-2-δ) :=
    semicircleResolvent_gt_from_inverse hminus ha1.le (by nlinarith)
  have hRp : semicircleResolvent (a+a⁻¹-2+δ) < a :=
    semicircleResolvent_lt_from_inverse hplus ha1.le (by nlinarith)
  have hm := (hres _ hminus).eventually (lt_mem_nhds hRm)
  have hp := (hres _ hplus).eventually (gt_mem_nhds hRp)
  have ht := htop.eventually (gt_mem_nhds (show (2:ℝ) < a+a⁻¹-δ by linarith))
  filter_upwards [hm,hp,ht] with n hnm hnp hnt
  have hshadowMinus : 2+(a+a⁻¹-2-δ) = a+a⁻¹-δ := by ring
  have hshadowPlus : 2+(a+a⁻¹-2+δ) = a+a⁻¹+δ := by ring
  rw [hshadowMinus] at hnm
  rw [hshadowPlus] at hnp
  have hlow := (le_saddleRadius_iff (lam n) ha hnt).mpr hnm.le
  have hupp := (saddleRadius_le_iff (lam n) ha (by linarith : spectralTop (lam n) < a+a⁻¹+δ)).mpr hnp.le
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith

lemma sphericalVariational_deriv_tendsto (lam : (n : ℕ) → ι n → ℝ)
    (htop : Tendsto (fun n => spectralTop (lam n)) atTop (𝓝 2))
    (hres : ∀ s > 0, Tendsto (fun n => spectralStieltjes (lam n) (2+s)) atTop (𝓝 (semicircleResolvent s)))
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun n => deriv (sphericalVariational (lam n)) a) atTop (𝓝 (a/2)) := by
  have h := ((saddleRadius_subcritical_tendsto lam htop hres ha ha1).sub_const a⁻¹).div_const 2
  simpa only [add_sub_cancel_right, (sphericalVariational_hasDerivAt _ ha).deriv] using h

lemma saddleSubcriticalError_tendsto (lam : (n : ℕ) → ι n → ℝ)
    (hbound : ∀ᶠ n in atTop, ∀ i, |lam n i| ≤ 3)
    (htop : Tendsto (fun n => spectralTop (lam n)) atTop (𝓝 2))
    (hres : ∀ s > 0, Tendsto (fun n => spectralStieltjes (lam n) (2+s)) atTop (𝓝 (semicircleResolvent s))) :
    Tendsto (fun n => saddleSubcriticalError (lam n)) atTop (𝓝 0) := by
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun a => |deriv (sphericalVariational (lam n)) a-a/2|)
      (volume.restrict (Ioo (0:ℝ) 1)) :=
    ((measurable_deriv _).sub (measurable_id.div_const 2)).abs.aestronglyMeasurable
  have hdom : ∀ᶠ n in atTop, ∀ᵐ a ∂volume.restrict (Ioo (0:ℝ) 1),
      ‖|deriv (sphericalVariational (lam n)) a-a/2|‖ ≤ 2 := by
    filter_upwards [hbound] with n hn
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
    rw [norm_eq_abs,abs_abs,(sphericalVariational_hasDerivAt _ ha.1).deriv]
    calc
      _ ≤ |(saddleRadius (lam n) a-a⁻¹)/2|+|a/2| := abs_sub _ _
      _ ≤ 3/2+a/2 := by
        rw [abs_of_pos (div_pos ha.1 (by norm_num) : 0 < a/2)]
        exact add_le_add (sphericalVariational_slope_bound _ ha.1 hn) (le_refl _)
      _ ≤ 2 := by linarith [ha.2]
  have hlim : ∀ᵐ a ∂volume.restrict (Ioo (0:ℝ) 1),
      Tendsto (fun n => |deriv (sphericalVariational (lam n)) a-a/2|) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
    simpa using ((sphericalVariational_deriv_tendsto lam htop hres ha.1 ha.2).sub_const (a/2)).abs
  have hint : Integrable (fun _ : ℝ => (2:ℝ)) (volume.restrict (Ioo (0:ℝ) 1)) := by
    exact (continuousOn_const.integrableOn_Icc (μ := volume) (a := (0:ℝ)) (b := 1)).mono_set Ioo_subset_Icc_self
  have hh := tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => (2:ℝ))
    (Eventually.of_forall hmeas) hdom hint hlim
  simpa only [saddleSubcriticalError,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo,integral_zero] using hh

end

open Set Filter

lemma spectralGood_reference (n : ℕ) {h s : ℝ} (hh : 0 ≤ h) (hs : 0 ≤ s) :
    (fun i => 2-orderedJacobiGaps n i) ∈ spectralGood n h s := by
  intro i
  simp only [sub_self,abs_zero]
  unfold edgeError
  exact add_nonneg (add_nonneg (mul_nonneg (formA_nonneg n hh) (Real.rpow_nonneg (add_nonneg (orderedJacobiGaps_nonneg n i) hs) _))
    (formB_nonneg n)) (mul_nonneg (formC_nonneg n) (orderedJacobiGaps_nonneg n i))

lemma spectralGood_natural_controls {h L : ℝ} (hh : 0 ≤ h) (hL : 1696 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) :
    ∀ᶠ n : ℕ in atTop, ∀ lam ∈ spectralGood n h (naturalEdgeScale n L),
      (∀ i, |lam i| ≤ 3) ∧ |spectralTop lam-2| ≤ naturalEdgeScale n L := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hc := traceCost_natural_eventually hh hLp hcost
  have hs := (naturalEdgeScale_tendsto L).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [hc,hs,edgeLength_tents_eventually] with n hn hns hnfit
  intro lam hlam
  have hp := naturalEdgeScale_pos n hLp
  refine ⟨spectralGood_bounded n hh hp hns.le (by norm_num : (1/100:ℝ) ≤ 1/5) hn hlam,?_⟩
  have hlow := (abs_le.mp (spectralGood_top_close hh hL hns.le hnfit hn hlam 0 (by simp))).1
  have hlu := le_spectralTop lam 0
  obtain ⟨i,hi⟩ := spectralTop_attained lam
  have hu := spectralGood_top_upper n hh hp hns.le (by norm_num : (1/100:ℝ) ≤ 1) hn hlam i
  rw [hi] at hu
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma spectralGood_natural_top_tendsto {h L : ℝ} (hh : 0 ≤ h) (hL : 1696 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) (lam : (n : ℕ) → Fin (n+1) → ℝ)
    (hgood : ∀ᶠ n in atTop, lam n ∈ spectralGood n h (naturalEdgeScale n L)) :
    Tendsto (fun n => spectralTop (lam n)) atTop (𝓝 2) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [spectralGood_natural_controls hh hL hcost,hgood,
    (naturalEdgeScale_tendsto L).eventually (gt_mem_nhds hε)] with n hn hng hne
  rw [Real.dist_eq]
  exact (hn (lam n) hng).2.trans_lt hne

lemma traceError_fixed_tendsto {h s : ℝ} (hh : 0 ≤ h) (hs : 0 < s) :
    Tendsto (fun n : ℕ => 416*formA n h*s^(-1/8:ℝ)+8*formB n/Real.sqrt s+
      2*formC n+2/((n+1:ℝ)*s)) atTop (𝓝 0) := by
  have hA := ((formA_tendsto hh).const_mul 416).mul_const (s^(-1/8:ℝ))
  have hB := (formB_tendsto.const_mul 8).div_const (Real.sqrt s)
  have hC := formC_tendsto.const_mul 2
  have hN : Tendsto (fun n : ℕ => ((n:ℝ)+1)*s) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ)))).atTop_mul_const hs
  simpa only [mul_zero,zero_mul,zero_div,zero_add] using ((hA.add hB).add hC).add (hN.const_div_atTop (2:ℝ))

lemma spectralGood_natural_resolvent_tendsto {h L : ℝ} (hh : 0 ≤ h) (hL : 1696 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) (hspace : 16 ≤ L*Real.sqrt L)
    (lam : (n : ℕ) → Fin (n+1) → ℝ)
    (hgood : ∀ᶠ n in atTop, lam n ∈ spectralGood n h (naturalEdgeScale n L))
    (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n => spectralStieltjes (lam n) (2+s)) atTop (𝓝 (semicircleResolvent s)) := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [traceCost_natural_eventually hh hLp hcost,hgood,
    (naturalEdgeScale_tendsto L).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    (naturalEdgeScale_tendsto L).eventually (gt_mem_nhds hs),
    (traceError_fixed_tendsto hh hs).eventually (gt_mem_nhds hε)] with n hnc hng hn1 hns hne
  have hp := naturalEdgeScale_pos n hLp
  have hsmall := (traceCost_small n hh hp hn1.le hnc).trans (by norm_num : (1/100:ℝ) ≤ 1/2)
  have hsc : 2 ≤ (n+1:ℝ)*naturalEdgeScale n L*Real.sqrt (naturalEdgeScale n L) := by
    have hx := (naturalEdgeScale_space n hLp).1
    linarith
  have ht := (spectralGood_resolvent n hh hp hns.le hsmall hsc hng).2.2
  rw [Real.dist_eq]
  apply lt_of_le_of_lt _ hne
  simpa only [spectralStieltjes,Fintype.card_fin,Nat.cast_add,Nat.cast_one,div_eq_mul_inv,mul_comm] using ht

lemma spectralGood_natural_saddle_tendsto {h L : ℝ} (hh : 0 ≤ h) (hL : 1696 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) (hspace : 16 ≤ L*Real.sqrt L)
    (lam : (n : ℕ) → Fin (n+1) → ℝ)
    (hgood : ∀ᶠ n in atTop, lam n ∈ spectralGood n h (naturalEdgeScale n L)) :
    Tendsto (fun n => saddleSubcriticalError (lam n)) atTop (𝓝 0) := by
  apply saddleSubcriticalError_tendsto lam
  · filter_upwards [spectralGood_natural_controls hh hL hcost,hgood] with n hn hng
    exact (hn (lam n) hng).1
  · exact spectralGood_natural_top_tendsto hh hL hcost lam hgood
  · exact spectralGood_natural_resolvent_tendsto hh hL hcost hspace lam hgood

lemma spectralGood_saddle_uniform_s2_oai {h L : ℝ} (hh : 0 ≤ h) (hL : 1696 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) (hspace : 16 ≤ L*Real.sqrt L)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ lam ∈ spectralGood n h (naturalEdgeScale n L),
      saddleSubcriticalError lam+naturalEdgeScale n L/2 < ε := by
  classical
  let bad (n : ℕ) (lam : Fin (n+1) → ℝ) : Prop :=
    lam ∈ spectralGood n h (naturalEdgeScale n L) ∧ ε ≤ saddleSubcriticalError lam+naturalEdgeScale n L/2
  let lam (n : ℕ) : Fin (n+1) → ℝ :=
    if hb : ∃ x, bad n x then Classical.choose hb else fun i => 2-orderedJacobiGaps n i
  have hg (n) : lam n ∈ spectralGood n h (naturalEdgeScale n L) := by
    dsimp only [lam]
    split
    · exact (Classical.choose_spec ‹∃ x, bad n x›).1
    · exact spectralGood_reference n hh (naturalEdgeScale_pos n (lt_of_lt_of_le (by norm_num) hL)).le
  have hlim := (spectralGood_natural_saddle_tendsto hh hL hcost hspace lam (Eventually.of_forall hg)).add
    ((naturalEdgeScale_tendsto L).div_const 2)
  have hlim' : Tendsto (fun n => saddleSubcriticalError (lam n)+naturalEdgeScale n L/2) atTop (𝓝 0) := by
    simpa only [zero_div,add_zero] using hlim
  filter_upwards [hlim'.eventually (gt_mem_nhds hε)] with n hn
  intro x hx
  by_contra hnot
  have hex : ∃ y, bad n y := ⟨x,hx,le_of_not_gt hnot⟩
  have hh := (Classical.choose_spec hex).2
  have he : lam n = Classical.choose hex := dite_eq_left hex
  rw [he] at hn
  exact (not_lt_of_ge hh) hn

end CriticalSK

end

end OAI
end

theorem solution : type_of% @OAI.CriticalSK.spectralGood_saddle_uniform_s2_oai := @OAI.CriticalSK.spectralGood_saddle_uniform_s2_oai
