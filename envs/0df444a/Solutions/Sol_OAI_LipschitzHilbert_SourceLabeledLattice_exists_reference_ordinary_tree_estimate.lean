-- Prove2me | solution 1 for OAI.LipschitzHilbert.SourceLabeledLattice.exists_reference_ordinary_tree_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:30:59.449101+00:00
-- url     : https://prove2.me/submissions/a9ca9aa3-e7b1-4a91-87db-7a72042c443e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_SourceLabeledLattice_exists_masked_frozen_tree_estimate

section
-- module Solutions.OAIQ090_LH.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
/-- Mathlib d13f23b's `Finset.sum_le_sum_of_injOn`; ours has no such lemma (LipschitzHilbert, oaiq-090). -/
theorem sum_le_sum_of_injOn {ι κ M : Type*} [DecidableEq κ] [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M} (e : ι → κ)
    (he : Set.InjOn e s) (hest : s.image e ⊆ t) (hf : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ j ∈ t, j ∉ s.image e → 0 ≤ g j) : ∑ i ∈ s, f i ≤ ∑ j ∈ t, g j := by
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s, g (e i) := Finset.sum_le_sum hf
    _ = ∑ j ∈ s.image e, g j := (Finset.sum_image he).symm
    _ ≤ ∑ j ∈ t, g j := Finset.sum_le_sum_of_subset_of_nonneg hest hg
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_GeometricScaleWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform row and column bounds for the actual geometric scale kernel. -/

open scoped BigOperators

noncomputable section

namespace LipschitzHilbert

theorem sum_half_powers_le_two (N : ℕ) :
    (∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) ≤ 2 := by
  have heq : (∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) =
      2 * (1 - (1 / 2 : ℝ) ^ N) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [heq]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_BoxPolynomialWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial localization lower bound on a reference interval, with
the horizontal box offset retained explicitly. -/

noncomputable section
open Set

namespace LipschitzHilbert

theorem box_polynomial_base (u r k x : ℝ) (hr : 0 < r) (hx : |x - u| ≤ r) :
    (1 + |k|) ^ 2 / 8 ≤ 1 + (x - (u + r * k)) ^ 2 / r ^ 2 := by
  let v := (x - (u + r * k)) / r
  have hunit : |(x - u) / r| ≤ 1 := by
    rw [abs_div, abs_of_pos hr, div_le_one hr]
    exact hx
  have heq : k = (x - u) / r - v := by
    dsimp [v]
    field_simp
    ring
  have hk : |k| ≤ 1 + |v| := by
    rw [heq]
    exact (abs_sub _ _).trans (add_le_add hunit le_rfl)
  have hk2 := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |k|)
    (add_le_add (le_rfl : (1 : ℝ) ≤ 1) hk) 2
  have habs : |v| ^ 2 = v ^ 2 := sq_abs v
  have hs := sq_nonneg (|v| - 2)
  have hv : 1 + (x - (u + r * k)) ^ 2 / r ^ 2 = 1 + v ^ 2 := by
    dsimp [v]
    rw [div_pow]
  rw [hv]
  nlinarith

theorem box_polynomial_weight (u r k x : ℝ) (q : ℕ)
    (hr : 0 < r) (hx : |x - u| ≤ r) :
    ((1 + |k|) ^ 2 / 8) ^ q ≤ polynomialWeight (u + r * k) r q x := by
  exact pow_le_pow_left₀ (by positivity) (box_polynomial_base u r k x hr hx) q

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MultiplierError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The angular multiplier error is bounded by the actual annulus-plus-
small-angle-ratio source from the manuscript. -/

noncomputable section

namespace LipschitzHilbert

theorem multiplierError_bound (b : ℝ → ℂ) (t d c R M L u : ℝ)
    (hd : 0 < d) (_hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hb : ∀ s, ‖b s‖ ≤ M)
    (hnear : |u-t| ≤ c*d → ‖b u-b t‖ ≤ L * (|u-t|/d))
    (hfar : R*d < |u-t| → b u = 0) :
    ‖multiplierError b t d u‖ ≤ (2*M+L) * errorSourceProfile c R d |u-t| := by
  have hA : 0 ≤ 2*M+L := by positivity
  have hprofile := errorSourceProfile_nonneg c R d |u-t| hd (abs_nonneg _)
  by_cases hn : |u-t| ≤ c*d
  · have hsel : |u-t| ≤ d := hn.trans (by nlinarith)
    have hratio : 0 ≤ |u-t|/d := div_nonneg (abs_nonneg _) hd.le
    have hp : |u-t|/d ≤ errorSourceProfile c R d |u-t| := by
      unfold errorSourceProfile
      rw [ite_eq_left hn]
      split_ifs <;> linarith
    calc
      _ = ‖b u-b t‖ := by rw [multiplierError, ite_eq_left hsel]
      _ ≤ L * (|u-t|/d) := hnear hn
      _ ≤ (2*M+L) * (|u-t|/d) := mul_le_mul_of_nonneg_right (by linarith) hratio
      _ ≤ _ := mul_le_mul_of_nonneg_left hp hA
  · by_cases hf : |u-t| ≤ R*d
    · have hp : errorSourceProfile c R d |u-t| = 1 := by
        unfold errorSourceProfile
        rw [ite_eq_left ⟨(lt_of_not_ge hn).le,hf⟩, ite_eq_right hn, add_zero]
      rw [hp,mul_one]
      unfold multiplierError
      split_ifs
      · exact (norm_sub_le _ _).trans (by linarith [hb u,hb t])
      · simpa only [sub_zero] using (hb u).trans (by linarith)
    · have hfar' : R*d < |u-t| := lt_of_not_ge hf
      have hsel : ¬ |u-t| ≤ d := by nlinarith
      rw [multiplierError, hfar hfar', ite_eq_right hsel, sub_self, norm_zero]
      exact mul_nonneg hA hprofile

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PolynomialEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial growth about a box is absorbed by a slower packet envelope.
The integrated envelope has the packet length as its only scale factor. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert

theorem polynomial_base_le (x s a l r : ℝ) (hl : 0 < l) (hr : 0 < r)
    (hlr : l ≤ r) (hsa : |s - a| ≤ r) :
    1 + (x - a) ^ 2 / r ^ 2 ≤ 4 * (1 + ((x - s) / l) ^ 2) := by
  have hu : |(x - s) / r| ≤ |(x - s) / l| := by
    rw [abs_div, abs_div, abs_of_pos hr, abs_of_pos hl]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hl hlr
  have hv : |(s - a) / r| ≤ 1 := by
    rw [abs_div, abs_of_pos hr, div_le_one hr]
    exact hsa
  have hu2 := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hu
  have hv2 := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr hv
  simp only [sq_abs, one_pow] at hu2 hv2
  have heq : (x - a) / r = (x - s) / r + (s - a) / r := by ring
  rw [← div_pow, heq]
  nlinarith [sq_nonneg ((x - s) / r - (s - a) / r), sq_nonneg ((x - s) / l)]

theorem polynomialWeight_sq_mul_envelope (x s a l r : ℝ) (q n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r) (hsa : |s - a| ≤ r) :
    polynomialWeight a r q x ^ 2 * lineEnvelope s l (n + 2 * q) x ≤
      16 ^ q * lineEnvelope s l n x := by
  let B := 1 + ((x - s) / l) ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hbase := polynomial_base_le x s a l r hl hr hlr hsa
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + (x - a) ^ 2 / r ^ 2)
    hbase (2 * q)
  have hweight : polynomialWeight a r q x ^ 2 = (1 + (x - a) ^ 2 / r ^ 2) ^ (2 * q) := by
    simp only [polynomialWeight, ← pow_mul, Nat.mul_comm q 2]
  rw [hweight]
  calc
    _ ≤ (4 * B) ^ (2 * q) * (B ^ (n + 2 * q))⁻¹ :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = 16 ^ q * lineEnvelope s l n x := by
      change (4 * B) ^ (2 * q) * (B ^ (n + 2 * q))⁻¹ = 16 ^ q * (B ^ n)⁻¹
      rw [mul_pow, pow_add, mul_inv_rev, ← mul_assoc]
      have hz : B ^ (2 * q) ≠ 0 := pow_ne_zero _ hB.ne'
      have hc : (4 : ℝ) ^ (2 * q) = 16 ^ q := by rw [pow_mul]; norm_num
      rw [mul_assoc ((4 : ℝ) ^ (2 * q)), mul_inv_cancel₀ hz, mul_one, hc]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlicedIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! From almost-everywhere line estimates to planar estimates, including
the area-preserving coordinates of a fixed reference slope. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem integral_slopeShear (s : ℝ) (f : ℝ × ℝ → ℝ) :
    (∫ z, f (slopeShear s z) ∂volume.prod volume) = ∫ z, f z ∂volume.prod volume :=
  (slopeShear_measurePreserving s).integral_comp (slopeShear s).measurableEmbedding f

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineTiling
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countably many actual finite line meshes cover a reference line. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert

theorem tiledLineGrid_root (origin H : ℝ) (hH : 0 < H) (G N : ℕ) (hG : 0 < G)
    (k : ℤ) :
    (tiledLineGrid origin H hH G N hG k).root =
      Ico (origin + k * H) (origin + (k + 1 : ℤ) * H) := by
  unfold FiniteLineGrid.root tiledLineGrid
  congr 1
  push_cast
  ring

theorem tiledLineGrid_pairwise_disjoint (origin H : ℝ) (hH : 0 < H) (G N : ℕ)
    (hG : 0 < G) :
    Pairwise fun i j => Disjoint (tiledLineGrid origin H hH G N hG i).root
      (tiledLineGrid origin H hH G N hG j).root := by
  intro i j hij
  simp only [tiledLineGrid_root]
  apply Set.disjoint_left.mpr
  intro x hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hc : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
    push_cast at hi hj
    have hm := mul_le_mul_of_nonneg_right hc hH.le
    linarith [hi.2, hj.1]
  · have hc : (j : ℝ) + 1 ≤ i := by exact_mod_cast (show j + 1 ≤ i by omega)
    push_cast at hi hj
    have hm := mul_le_mul_of_nonneg_right hc hH.le
    linarith [hj.2, hi.1]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineLatticeEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform finite lattice overlap bound from the actual line integral of
the rational envelope. No cardinality factor or implicit lattice assumption
is used. -/

noncomputable section

open Set MeasureTheory Function
open scoped BigOperators

namespace LipschitzHilbert

theorem lineEnvelope_cell_comparison (x k y : ℝ) (hy : y ∈ Ico k (k + 1)) :
    lineEnvelope x 1 1 k ≤ 4 * lineEnvelope x 1 1 y := by
  have hdelta : (y - k) ^ 2 ≤ 1 := by
    have ha : |y - k| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr ha
    simpa only [sq_abs, one_pow] using hs
  have hb : 1 + (y - x) ^ 2 ≤ 4 * (1 + (k - x) ^ 2) := by
    nlinarith [sq_nonneg ((k - x) - (y - k)), sq_nonneg (k - x)]
  simp only [lineEnvelope, div_one, pow_one]
  rw [← one_div, ← div_eq_mul_inv]
  exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hb)

theorem lineEnvelope_le_cell_integral (x k : ℝ) :
    lineEnvelope x 1 1 k ≤ 4 * ∫ y in Ico k (k + 1), lineEnvelope x 1 1 y := by
  have hint : IntegrableOn (lineEnvelope x 1 1) (Ico k (k + 1)) :=
    (integrable_lineEnvelope_one x 1 (by norm_num)).integrableOn
  have hfinite : volume (Ico k (k + 1)) ≠ ⊤ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  have h := setIntegral_mono_on (integrableOn_const hfinite : IntegrableOn
      (fun _ : ℝ => lineEnvelope x 1 1 k) (Ico k (k + 1)) volume)
    (hint.const_mul 4) measurableSet_Ico (fun y hy => lineEnvelope_cell_comparison x k y hy)
  rw [integral_const_mul] at h
  simpa [setIntegral_const, Real.volume_Ico, measureReal_def] using h

theorem finite_line_lattice_overlap (x : ℝ) (s : Finset ℤ) :
    (∑ k ∈ s, lineEnvelope x 1 1 k) ≤ 4 * Real.pi := by
  classical
  have hint := integrable_lineEnvelope_one x 1 (by norm_num)
  have hd : (s : Set ℤ).Pairwise (Disjoint on fun k : ℤ => Ico (k : ℝ) (k + 1)) := by
    intro i _ j _ hij
    have h := tiledLineGrid_pairwise_disjoint 0 1 (by norm_num) 2 0 (by norm_num) hij
    simpa only [tiledLineGrid_root, Int.cast_add, Int.cast_one, mul_one, zero_add] using h
  have hsum := integral_biUnion_finset s (fun _ _ => measurableSet_Ico) hd
    (fun _ _ => hint.integrableOn)
  calc
    _ ≤ ∑ k ∈ s, 4 * ∫ y in Ico (k : ℝ) (k + 1), lineEnvelope x 1 1 y :=
      Finset.sum_le_sum (fun k _ => lineEnvelope_le_cell_integral x k)
    _ = 4 * ∫ y in ⋃ k ∈ s, Ico (k : ℝ) (k + 1), lineEnvelope x 1 1 y := by
      rw [← Finset.mul_sum, hsum]
    _ ≤ 4 * ∫ y, lineEnvelope x 1 1 y := by
      exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hint
        (Filter.Eventually.of_forall (lineEnvelope_nonneg x 1 1))) (by norm_num)
    _ = 4 * Real.pi := by rw [integral_lineEnvelope_one x 1 (by norm_num), mul_one]

theorem lineEnvelope_lattice_rescale (a l x : ℝ) (hl : l ≠ 0) (k : ℤ) (n : ℕ) :
    lineEnvelope (a + l * k) l n x = lineEnvelope ((x - a) / l) 1 n k := by
  unfold lineEnvelope
  congr 3
  simp only [div_one]
  have h : (x - (a + l * k)) / l = -((k : ℝ) - (x - a) / l) := by
    field_simp
    ring
  rw [h, neg_sq]

theorem finite_plane_lattice_overlap (x y : ℝ) (s : Finset (ℤ × ℤ)) :
    (∑ p ∈ s, lineEnvelope x 1 1 p.1 * lineEnvelope y 1 1 p.2) ≤
      (4 * Real.pi) ^ 2 := by
  classical
  have hsub : s ⊆ (s.image Prod.fst) ×ˢ (s.image Prod.snd) := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,
      Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩
  calc
    _ ≤ ∑ p ∈ (s.image Prod.fst) ×ˢ (s.image Prod.snd),
        lineEnvelope x 1 1 p.1 * lineEnvelope y 1 1 p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
        mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
    _ = (∑ i ∈ s.image Prod.fst, lineEnvelope x 1 1 i) *
        ∑ j ∈ s.image Prod.snd, lineEnvelope y 1 1 j := by
      rw [Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ ≤ (4 * Real.pi) * (4 * Real.pi) :=
      mul_le_mul (finite_line_lattice_overlap x _) (finite_line_lattice_overlap y _)
        (Finset.sum_nonneg (fun j _ => lineEnvelope_nonneg _ _ _ _)) (by positivity)
    _ = _ := (pow_two _).symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TileLatticeEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform overlap for actual rectangular tile-center lattices, allowing
arbitrary horizontal and vertical scales and finite subfamilies. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem finite_scaled_plane_lattice_overlap (a b l W x y : ℝ)
    (hl : l ≠ 0) (hW : W ≠ 0) (s : Finset (ℤ × ℤ)) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (∑ p ∈ s, lineEnvelope (a + l * p.1) l m x *
      lineEnvelope (b + W * p.2) W n y) ≤ (4 * Real.pi) ^ 2 := by
  calc
    _ ≤ ∑ p ∈ s, lineEnvelope ((x - a) / l) 1 1 p.1 *
        lineEnvelope ((y - b) / W) 1 1 p.2 := by
      apply Finset.sum_le_sum
      intro p _
      rw [lineEnvelope_lattice_rescale a l x hl p.1 m,
        lineEnvelope_lattice_rescale b W y hW p.2 n]
      exact mul_le_mul (lineEnvelope_antitone _ _ _ hm) (lineEnvelope_antitone _ _ _ hn)
        (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
    _ ≤ _ := finite_plane_lattice_overlap _ _ s

theorem injective_tile_lattice_overlap {ι : Type*} [Fintype ι]
    (index : ι → ℤ × ℤ) (hinj : Function.Injective index)
    (a b l W x y : ℝ) (hl : l ≠ 0) (hW : W ≠ 0)
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (∑ i, lineEnvelope (a + l * (index i).1) l m x *
      lineEnvelope (b + W * (index i).2) W n y) ≤ (4 * Real.pi) ^ 2 := by
  classical
  have h := finite_scaled_plane_lattice_overlap a b l W x y hl hW
    (Finset.univ.image index) hm hn
  rw [Finset.sum_image (fun _ _ _ _ heq => hinj heq)] at h
  exact h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual decaying top weights and their motion along a reference line. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

namespace SlopeBox

theorem radius_nonnegative (T : SlopeBox) (z : ℝ × ℝ) : 0 ≤ T.radius z :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeightIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability and exact area scaling for the actual decaying top weights. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

theorem planeDivide_apply (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (z : ℝ × ℝ) :
    planeDivide a b ha hb z = (z.1 / a, z.2 / b) := by
  rfl

theorem map_planeDivide (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Measure.map (planeDivide a b ha hb) (volume.prod volume) =
      (ENNReal.ofReal |a| * ENNReal.ofReal |b|) • (volume.prod volume) := by
  have hmap (c : ℝ) (hc : c ≠ 0) :
      Measure.map (fun x : ℝ => x * c⁻¹) volume = ENNReal.ofReal |c| • volume := by
    simpa only [smul_eq_mul, Module.finrank_self, pow_one, inv_inv, mul_comm] using
      (Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) (inv_ne_zero hc))
  change Measure.map (Prod.map (fun x => x * a⁻¹) (fun y => y * b⁻¹)) _ = _
  rw [← Measure.map_prod_map volume volume (by fun_prop) (by fun_prop), hmap a ha, hmap b hb,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]

theorem integrable_planeDivide (f : ℝ × ℝ → ℝ)
    (hf : Integrable f (volume.prod volume)) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Integrable (fun z => f (planeDivide a b ha hb z)) (volume.prod volume) := by
  apply (integrable_map_equiv (planeDivide a b ha hb) f).mp
  rw [map_planeDivide]
  exact hf.smul_measure (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

theorem integral_planeDivide (f : ℝ × ℝ → ℝ) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∫ z, f (planeDivide a b ha hb z) ∂volume.prod volume) =
      (|a| * |b|) * ∫ z, f z ∂volume.prod volume := by
  rw [← integral_map_equiv (planeDivide a b ha hb), map_planeDivide, integral_smul_measure]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]

theorem topProfile_nonnegative (D : ℝ) (z : ℝ × ℝ) : 0 ≤ topProfile D z :=
  Real.rpow_nonneg (by positivity) _

theorem topProfile_continuous (D : ℝ) : Continuous (topProfile D) := by
  unfold topProfile
  apply Continuous.rpow_const (by fun_prop)
  intro z
  left
  positivity

/-- The fixed normalized profile is integrable once its decay exponent exceeds
its two-dimensional domain. -/
theorem topProfile_integrable {D : ℝ} (hD : 2 < D) :
    Integrable (topProfile D) (volume.prod volume) := by
  have hd : (Module.finrank ℝ (ℝ × ℝ) : ℝ) < D := by simpa using hD
  have h := integrable_one_add_norm (μ := (volume.prod volume)) hd
  apply h.mono' (topProfile_continuous D).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (topProfile_nonnegative D z)]
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
  simp only [Prod.norm_def, Real.norm_eq_abs]
  have hmax : max |z.1| |z.2| ≤ |z.1| + |z.2| :=
    max_le (by linarith [abs_nonneg z.2]) (by linarith [abs_nonneg z.1])
  linarith

namespace SlopeBox

theorem normalizedCoordinates_eq (T : SlopeBox) (K : ℝ) (hK : 0 < K) (z : ℝ × ℝ) :
    T.normalizedCoordinates K hK z = (T.horizontal z / K, T.transverse z / K) := by
  ext <;> simp [normalizedCoordinates, planeDivide_apply, slopeShear, horizontal, transverse]
  <;> ring

theorem weight_eq_topProfile (T : SlopeBox) (K D : ℝ) (hK : 0 < K) (z : ℝ × ℝ) :
    T.weight K D z = 2 ^ D * topProfile D (T.normalizedCoordinates K hK z) := by
  rw [normalizedCoordinates_eq]
  simp only [weight, topProfile, radius, abs_div, abs_of_pos hK, add_div]

/-- The actual top weight is integrable, uniformly over positions and slopes. -/
theorem weight_integrable (T : SlopeBox) {K D : ℝ} (hK : 0 < K) (hD : 2 < D) :
    Integrable (T.weight K D) (volume.prod volume) := by
  have hf := integrable_planeDivide (topProfile D) (topProfile_integrable hD)
    (K * T.length) (K * T.width)
    (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne')
  have hs := (slopeShear_measurePreserving (-T.slope)).integrable_comp_of_integrable hf
  have ht := hs.comp_sub_right (T.x, T.y)
  have heq : T.weight K D = fun z => 2 ^ D *
      ((fun z => topProfile D (planeDivide (K * T.length) (K * T.width)
        (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne') z)) ∘
        slopeShear (-T.slope)) (z - (T.x, T.y)) := by
    funext z
    exact T.weight_eq_topProfile K D hK z
  rw [heq]
  exact ht.const_mul _

/-- Exact area scaling: all dependence on the box and the dilation is
`K² * length * width`, while the remaining integral is a fixed constant. -/
theorem integral_weight (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) :
    (∫ z, T.weight K D z ∂volume.prod volume) =
      (2 ^ D * ∫ z, topProfile D z ∂volume.prod volume) *
        K ^ 2 * T.length * T.width := by
  have heq : T.weight K D = fun z => 2 ^ D *
      ((fun z => topProfile D (planeDivide (K * T.length) (K * T.width)
        (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne') z)) ∘
        slopeShear (-T.slope)) (z - (T.x, T.y)) := by
    funext z
    exact T.weight_eq_topProfile K D hK z
  rw [heq, integral_const_mul, integral_sub_right_eq_self]
  simp only [Function.comp_apply]
  rw [integral_slopeShear (-T.slope) (fun z => topProfile D
    (planeDivide (K * T.length) (K * T.width)
      (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne') z)),
    integral_planeDivide, abs_of_pos (mul_pos hK T.length_pos),
    abs_of_pos (mul_pos hK T.width_pos)]
  ring

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_DyadicLineGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nested alternating one-third grids in the line-counting argument. -/

noncomputable section

open Set

namespace LipschitzHilbert.DyadicLineGrid

theorem cell_length (q k j : ℤ) : MeasureTheory.volume.real (cell q k j) = scale k := by
  rw [cell, Real.volume_real_Ico_of_le]
  · unfold left
    push_cast
    ring
  · unfold left
    have hs := scale_pos k
    push_cast
    nlinarith

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWhitneyIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Horizontal Whitney cells for the ordinary tree estimate. An allowed
cell has no tile of shorter length whose center meets its triple. A
maximal allowed cell obtains its concrete witness from its parent. -/
noncomputable section
open Set
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid
attribute [local instance] Classical.propDecidable

theorem center_parent_bound (k j : ℤ) :
    |center k j-center (k+1) (parent 0 k j)| ≤ scale k/2 := by
  have hlo : 2*(j/2) ≤ j := by omega
  have hhi : j ≤ 2*(j/2)+1 := by omega
  have hlo' : (2:ℝ)*(j/2:ℤ) ≤ j := by exact_mod_cast hlo
  have hhi' : (j:ℝ) ≤ 2*(j/2:ℤ)+1 := by exact_mod_cast hhi
  have hs := scale_pos k
  have hl := mul_le_mul_of_nonneg_left hlo' hs.le
  have hh := mul_le_mul_of_nonneg_left hhi' hs.le
  simp only [center,left,parent,shift,Int.mul_zero,Int.cast_zero,zero_div,add_zero,scale_succ]
  apply abs_le.mpr
  constructor <;> nlinarith only [hl,hh,hs]

theorem allowed_of_parent {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
    (k j : ℤ) (h : Allowed tiles x ell (k+1) (parent 0 k j)) :
    Allowed tiles x ell k j := by
  intro i hi hlen
  have hs := scale_pos k
  have hlen' : ell i ≤ scale (k+1) := by rw [scale_succ]; linarith only [hlen,hs]
  have hp := h i hi hlen'
  have hd := center_parent_bound k j
  have ht := abs_sub_le (x i) (center k j) (center (k+1) (parent 0 k j))
  rw [scale_succ] at hp
  linarith only [hp,hd,ht,hs]

theorem parent_witness {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
    {k j : ℤ} (h : Whitney tiles x ell k j) :
    ∃ i ∈ tiles, ell i ≤ 2*scale k ∧
      ∀ z ∈ cell 0 k j, |x i-z| ≤ 4*scale k := by
  have hn := h.2
  simp only [Allowed,not_forall,not_lt] at hn
  obtain ⟨i,hi,hlen,hnear⟩ := hn
  refine ⟨i,hi,by simpa only [scale_succ] using hlen,?_⟩
  intro z hz
  have hd := point_center_bound (k+1) (parent 0 k j) (cell_subset_parent 0 k j hz)
  rw [scale_succ] at hd hnear
  have ht := abs_sub_le (x i) (center (k+1) (parent 0 k j)) z
  rw [abs_sub_comm (center (k+1) (parent 0 k j)) z] at ht
  linarith only [ht,hd,hnear]

/-- The index of a point at the next scale is exactly its parent index. -/
theorem parent_index (k : ℤ) (z : ℝ) :
    parent 0 k (index 0 k z) = index 0 (k+1) z :=
  (index_eq_of_mem (cell_subset_parent 0 k (index 0 k z)
    (mem_index_cell 0 k z))).symm

/-- Being allowed passes from a larger cell to every smaller cell it meets. -/
theorem allowed_at_point_mono {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
    {k l : ℤ} (hkl : k ≤ l) (z : ℝ)
    (h : Allowed tiles x ell l (index 0 l z)) :
    Allowed tiles x ell k (index 0 k z) := by
  obtain ⟨n,rfl⟩ := Int.le.dest hkl
  induction n with
  | zero => simpa only [Nat.cast_zero,add_zero] using h
  | succ n ih =>
    apply ih (by omega)
    apply allowed_of_parent tiles x ell (k+n) (index 0 (k+n) z)
    simpa only [parent_index,Nat.cast_add,Nat.cast_one,add_assoc] using h

/-- Distinct maximal allowed cells are disjoint at all scales. -/
theorem whitney_disjoint {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
    {k l i j : ℤ} (hi : Whitney tiles x ell k i)
    (hj : Whitney tiles x ell l j) (hne : (k,i) ≠ (l,j)) :
    Disjoint (cell 0 k i) (cell 0 l j) := by
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  have hei := index_eq_of_mem hzi
  have hej := index_eq_of_mem hzj
  rcases lt_trichotomy k l with hkl | hkl | hlk
  · apply hi.2
    have hp := cell_subset_parent 0 k i hzi
    have he := index_eq_of_mem hp
    rw [← he]
    apply allowed_at_point_mono tiles x ell (by omega : k+1 ≤ l) z
    simpa only [hej] using hj.1
  · subst l
    exact hne (by simp [hei.symm.trans hej])
  · apply hj.2
    have hp := cell_subset_parent 0 l j hzj
    have he := index_eq_of_mem hp
    rw [← he]
    apply allowed_at_point_mono tiles x ell (by omega : l+1 ≤ k) z
    simpa only [hei] using hi.1

end LipschitzHilbert.SourceWhitney

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SourceWhitneyPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative packing of the actual Whitney intervals used in the
ordinary tree estimate. Bounds are on arbitrary finite subfamilies and
therefore also support subsequent monotone summation. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid

/-- A parent witness locates the entire Whitney cell near the horizontal top. -/
theorem cell_subset_top_enlargement {ι : Type*} (tiles : Finset ι)
    (x ell : ι → ℝ) {c L : ℝ}
    (hcenters : ∀ i ∈ tiles, |x i-c| ≤ L/2) {k j : ℤ}
    (h : Whitney tiles x ell k j) :
    cell 0 k j ⊆ Icc (c-(4*scale k+L/2)) (c+(4*scale k+L/2)) := by
  obtain ⟨i,hi,_,hw⟩ := parent_witness tiles x ell h
  intro z hz
  have hbound : |z-c| ≤ 4*scale k+L/2 := by
    have ht := abs_sub_le z (x i) c
    rw [abs_sub_comm z (x i)] at ht
    linarith only [ht,hw z hz,hcenters i hi]
  exact ⟨by linarith [(abs_le.mp hbound).1],by linarith [(abs_le.mp hbound).2]⟩

/-- A finite subfamily with lengths at most `r` has total length at most
`8r+L`, where the tile centers lie in an interval of length `L`. -/
theorem finite_length_budget {ι : Type*} (tiles : Finset ι)
    (x ell : ι → ℝ) {c L r : ℝ} (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hcenters : ∀ i ∈ tiles, |x i-c| ≤ L/2)
    (S : Finset (ℤ×ℤ))
    (hW : ∀ p ∈ S, Whitney tiles x ell p.1 p.2)
    (hscale : ∀ p ∈ S, scale p.1 ≤ r) :
    ∑ p ∈ S, scale p.1 ≤ 8*r+L := by
  have hsub (p) (hp : p ∈ S) :
      cell 0 p.1 p.2 ⊆ Icc (c-(4*r+L/2)) (c+(4*r+L/2)) := by
    intro z hz
    have hc := cell_subset_top_enlargement tiles x ell hcenters (hW p hp) hz
    have hs := hscale p hp
    exact ⟨by linarith [hc.1],by linarith [hc.2]⟩
  have hdisj : Set.PairwiseDisjoint (S : Set (ℤ×ℤ)) (fun p => cell 0 p.1 p.2) := by
    intro p hp q hq hpq
    exact whitney_disjoint tiles x ell (hW p hp) (hW q hq) (by simpa using hpq)
  calc
    ∑ p ∈ S, scale p.1 = ∑ p ∈ S, volume.real (cell 0 p.1 p.2) := by
      simp only [cell_length]
    _ = volume.real (⋃ p ∈ S, cell 0 p.1 p.2) :=
      (measureReal_biUnion_finset hdisj (fun p _ => cell_measurable 0 p.1 p.2)
        (fun _ _ => measure_Ico_lt_top.ne)).symm
    _ ≤ volume.real (Icc (c-(4*r+L/2)) (c+(4*r+L/2))) := by
      apply measureReal_mono _ measure_Icc_lt_top.ne
      intro z hz
      obtain ⟨p,hp,hz⟩ := mem_iUnion₂.mp hz
      exact hsub p hp hz
    _ = 8*r+L := by
      rw [Real.volume_real_Icc_of_le (by linarith)]
      ring

/-- The small Whitney cells have a summable total length controlled by
the top length. -/
theorem small_length_budget {ι : Type*} (tiles : Finset ι)
    (x ell : ι → ℝ) {c L : ℝ} (hL : 0 ≤ L)
    (hcenters : ∀ i ∈ tiles, |x i-c| ≤ L/2)
    (S : Finset (ℤ×ℤ))
    (hW : ∀ p ∈ S, Whitney tiles x ell p.1 p.2)
    (hscale : ∀ p ∈ S, scale p.1 ≤ L) :
    ∑ p ∈ S, scale p.1 ≤ 9*L := by
  have h := finite_length_budget tiles x ell hL hL hcenters S hW hscale
  linarith only [h]

end LipschitzHilbert.SourceWhitney

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SourceShortTreeOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short-tree summation uses actual distance to the Whitney strip,
actual sheared center lattices, and a finite dyadic length sum. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid

theorem stripDistance_nonneg (c r s : ℝ) : 0 ≤ stripDistance c r s := le_max_left _ _

theorem center_distance_le (c r s : ℝ) : |s-c| ≤ stripDistance c r s+r/2 := by
  have h := le_max_right 0 (|s-c|-r/2)
  change |s-c|-r/2 ≤ stripDistance c r s at h
  linarith only [h]

theorem stripDistance_le_point (s : ℝ) (k j : ℤ) {z : ℝ} (hz : z∈cell 0 k j) :
    stripDistance (center k j) (scale k) s ≤ |z-s| := by
  apply max_le (abs_nonneg _)
  have ht := abs_sub_le s z (center k j)
  have hc := point_center_bound k j hz
  rw [abs_sub_comm s z] at ht
  linarith only [ht,hc]

theorem stripDistance_large {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
    {k j : ℤ} (h : Allowed tiles x ell k j) {i : ι} (hi : i∈tiles)
    (hlen : ell i ≤ scale k) : scale k < stripDistance (center k j) (scale k) (x i) := by
  have ha := h i hi hlen
  have hd := center_distance_le (center k j) (scale k) (x i)
  linarith only [ha,hd]

/-- An interval-distance kernel is controlled by a center kernel once the
center distance is at most twice that distance plus one packet length. -/
theorem inverse_quadratic_le_center {s c ell d : ℝ} (hell : 0<ell) (hd : 0≤d)
    (hc : |s-c|≤2*d+ell) :
    (1+(d/ell)^2)⁻¹ ≤ 8*lineEnvelope s ell 1 c := by
  have hu : |s-c|/ell ≤ 2*(d/ell)+1 := by
    apply (div_le_iff₀ hell).mpr
    calc
      _ ≤ 2*d+ell := hc
      _ = (2*(d/ell)+1)*ell := by field_simp
  have hu0 : 0≤|s-c|/ell := div_nonneg (abs_nonneg _) hell.le
  have hv : 0≤d/ell := div_nonneg hd hell.le
  have hs := pow_le_pow_left₀ hu0 hu 2
  have hbase : 1+((c-s)/ell)^2 ≤ 8*(1+(d/ell)^2) := by
    have he : ((c-s)/ell)^2=(|s-c|/ell)^2 := by
      rw [div_pow,div_pow,sq_abs,sub_sq_comm]
    rw [he]
    nlinarith only [hs,sq_nonneg (2*(d/ell)-1)]
  simp only [lineEnvelope,pow_one]
  rw [←one_div,←div_eq_mul_inv]
  exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hbase)

theorem strip_kernel_le_center {s c ell r : ℝ} (hell : 0<ell)
    (hrel : ell ≤ r → r ≤ stripDistance c r s) :
    (1+(stripDistance c r s/ell)^2)⁻¹^2 ≤ 8*lineEnvelope s ell 1 c := by
  let d := stripDistance c r s
  have hd : 0≤d := stripDistance_nonneg c r s
  have hc : |s-c|≤2*d+ell := by
    have ht := center_distance_le c r s
    change |s-c|≤d+r/2 at ht
    by_cases he : ell ≤ r
    · have h := hrel he
      change r≤d at h
      linarith only [ht,h,hell,hd]
    · have h : r≤ell := le_of_lt (lt_of_not_ge he)
      linarith only [ht,h,hd,hell]
  have hq := inverse_quadratic_le_center hell hd hc
  have h1 : (1+(d/ell)^2)⁻¹≤1 :=
    (inv_le_one₀ (by positivity)).2 (by nlinarith [sq_nonneg (d/ell)])
  have h0 : 0≤(1+(d/ell)^2)⁻¹ := by positivity
  calc
    _ = (1+(d/ell)^2)⁻¹*(1+(d/ell)^2)⁻¹ := pow_two _
    _ ≤ (1+(d/ell)^2)⁻¹*1 := mul_le_mul_of_nonneg_left h1 h0
    _ ≤ _ := by simpa only [mul_one] using hq

theorem strip_kernel_le_center_decay {s c ell r : ℝ} (hell : 0<ell) (hr : 0 < r)
    (hfar : r ≤ stripDistance c r s) :
    (1+(stripDistance c r s/ell)^2)⁻¹^2 ≤
      8*lineEnvelope s ell 1 c*(ell/r)^2 := by
  let d := stripDistance c r s
  have hd : 0≤d := stripDistance_nonneg c r s
  have hc : |s-c|≤2*d+ell := by
    have ht := center_distance_le c r s
    change |s-c|≤d+r/2 at ht
    change r≤d at hfar
    linarith only [ht,hfar,hell,hd]
  have hq := inverse_quadratic_le_center hell hd hc
  have hrat : r/ell≤d/ell := div_le_div_of_nonneg_right hfar hell.le
  have hs := pow_le_pow_left₀ (div_nonneg hr.le hell.le) hrat 2
  have hinv := inv_anti₀ (pow_pos (div_pos hr hell) 2)
    (show (r/ell)^2≤1+(d/ell)^2 by linarith only [hs])
  have hinv' : (1+(d/ell)^2)⁻¹≤(ell/r)^2 := by
    rw [←inv_pow,inv_div] at hinv
    exact hinv
  calc
    _ = (1+(d/ell)^2)⁻¹*(1+(d/ell)^2)⁻¹ := pow_two _
    _ ≤ (8*lineEnvelope s ell 1 c)*(ell/r)^2 :=
      mul_le_mul hq hinv' (by positivity)
        (mul_nonneg (by norm_num) (lineEnvelope_nonneg _ _ _ _))

/-- A sheared lattice with centers in a strip has uniformly bounded
horizontal envelope sum, without a tile-cardinality factor. -/
theorem sheared_strip_overlap (a b ell W delta c y : ℝ)
    (hell : 0<ell) (hW : 0<W) (S : Finset (ℤ×ℤ))
    (hstrip : ∀ p∈S, |b+delta*ell*p.1+W*p.2-y|≤W) :
    (∑ p∈S, lineEnvelope (a+ell*p.1) ell 1 c) ≤ 18*(4*Real.pi)^2 := by
  classical
  have hfactor (p) (hp : p∈S) :
      1≤2*lineEnvelope (b+delta*ell*p.1+W*p.2) W 1 y := by
    have ht : |(y-(b+delta*ell*p.1+W*p.2))/W|≤1 := by
      rw [abs_div,abs_of_pos hW]
      exact (div_le_one hW).mpr (by simpa only [abs_sub_comm] using hstrip p hp)
    have hs := pow_le_pow_left₀ (abs_nonneg _) ht 2
    simp only [sq_abs,one_pow] at hs
    simp only [lineEnvelope,pow_one]
    rw [←div_eq_mul_inv]
    exact (le_div_iff₀ (by positivity)).mpr (by linarith only [hs])
  calc
    _ ≤ ∑ p∈S, 2*(lineEnvelope (a+ell*p.1) ell 1 c *
        lineEnvelope (b+delta*ell*p.1+W*p.2) W 1 y) := by
      apply Finset.sum_le_sum
      intro p hp
      have h := mul_le_mul_of_nonneg_left (hfactor p hp) (lineEnvelope_nonneg (a+ell*p.1) ell 1 c)
      nlinarith only [h]
    _ ≤ ∑ p∈S, 18*(lineEnvelope (ell*(snappedLatticeSite a b ell W delta p).1) ell 1 c *
        lineEnvelope (W*(snappedLatticeSite a b ell W delta p).2) W 1 y) := by
      apply Finset.sum_le_sum
      intro p _
      have h := snappedLatticeSite_envelope a b ell W delta c y hell hW p 1 1
      norm_num only [pow_one] at h
      nlinarith only [h]
    _ = 18*∑ p∈S.image (snappedLatticeSite a b ell W delta),
        lineEnvelope (ell*p.1) ell 1 c * lineEnvelope (W*p.2) W 1 y := by
      rw [Finset.mul_sum,Finset.sum_image (fun _ _ _ _ he => snappedLatticeSite_injective a b ell W delta he)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by
      simpa only [zero_add] using finite_scaled_plane_lattice_overlap 0 0 ell W c y
        hell.ne' hW.ne' (S.image (snappedLatticeSite a b ell W delta))
        (by decide : 1≤1) (by decide : 1≤1)) (by norm_num)

end LipschitzHilbert.SourceWhitney

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityScaledForest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The angular grid has physical scale w/topLength. Keeping that scale
explicit allows arbitrary vertical band width and dyadic source lengths. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

theorem scaledAngularCell_measurable (unit : ℝ) (q k j : ℤ) :
    MeasurableSet (scaledAngularCell unit q k j) :=
  measurableSet_Ico.preimage (measurable_id.div_const unit)

theorem scaledAngularCell_subset {unit : ℝ} {q k l i j : ℤ} (hlk : l ≤ k)
    (hinter : (scaledAngularCell unit q k i ∩ scaledAngularCell unit q l j).Nonempty) :
    scaledAngularCell unit q l j ⊆ scaledAngularCell unit q k i := by
  obtain ⟨s,hs,ht⟩ := hinter
  have hnested := DyadicLineGrid.cell_subset_of_intersect hlk ⟨s/unit,ht,hs⟩
  intro t ht
  exact hnested ht

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The density kernel has a quantitative tail outside a dilated slope
box. This turns a weighted density test into the unweighted witness used
by the finite keeper construction. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace LipschitzHilbert
namespace SlopeBox

theorem densityKernel_nonneg (T : SlopeBox) (D : ℝ) (z : ℝ×ℝ) :
    0 ≤ T.densityKernel D z := Real.rpow_nonneg (by linarith [T.radius_nonnegative z]) _

theorem densityKernel_eq_weight (T : SlopeBox) (D : ℝ) (z : ℝ×ℝ) :
    T.densityKernel D z = ((2:ℝ)^D)⁻¹*T.weight 1 D z := by
  have htwo : (2:ℝ)^D ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) D).ne'
  simp only [densityKernel,weight,div_one,←mul_assoc,inv_mul_cancel₀ htwo,one_mul]

theorem densityKernel_integrable (T : SlopeBox) {D : ℝ} (hD : 2 < D) :
    Integrable (T.densityKernel D) (volume.prod volume) := by
  have h := (T.weight_integrable (by norm_num : (0:ℝ)<1) hD).const_mul (((2:ℝ)^D)⁻¹)
  exact h.congr (Eventually.of_forall (fun z => (T.densityKernel_eq_weight D z).symm))

theorem integral_densityKernel (T : SlopeBox) (D : ℝ) :
    (∫ z, T.densityKernel D z ∂volume.prod volume) =
      (∫ z, topProfile D z ∂volume.prod volume)*T.area := by
  simp_rw [T.densityKernel_eq_weight D]
  rw [integral_const_mul,T.integral_weight (by norm_num : (0:ℝ)<1) D]
  have htwo : (2:ℝ)^D ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) D).ne'
  simp only [one_pow,mul_one,SlopeBox.area]
  field_simp [htwo]

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityPowerForest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At the manuscript's polynomial density threshold, the selected actual
witnesses obey the polynomial radius, precision and area hypotheses used
by concentration. The threshold is fixed before all finite data. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

theorem density_dyadic_length_order {w : ℝ} (hw : 0 < w) {i j : ℤ}
    (h : w/DyadicLineGrid.scale i ≤ w/DyadicLineGrid.scale j) : j ≤ i := by
  have hmul := (div_le_div_iff₀ (DyadicLineGrid.scale_pos i) (DyadicLineGrid.scale_pos j)).mp h
  have hscale : DyadicLineGrid.scale j ≤ DyadicLineGrid.scale i :=
    (mul_le_mul_iff_right₀ hw).mp (by simpa only [mul_comm] using hmul)
  exact (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp hscale

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary density is the supremum of the manuscript's actual
weighted box tests. Exceeding a threshold supplies a concrete test, which
can then be fed to the finite keeper construction. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem densityAverage_le (T : SlopeBox) (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ)
    (omega : Set ℝ) : densityAverage T E u omega ≤ ∫ z, topProfile 203 z ∂volume.prod volume := by
  unfold densityAverage
  apply (div_le_iff₀ T.area_pos).mpr
  have h := setIntegral_le_integral (s := E ∩ u ⁻¹' omega)
    (T.densityKernel_integrable (by norm_num : (2:ℝ)<203))
    (Filter.Eventually.of_forall (fun z => T.densityKernel_nonneg 203 z))
  exact h.trans_eq (T.integral_densityKernel 203)

namespace OrdinaryDensityTile

theorem densityValues_bddAbove (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) :
    BddAbove (tile.densityValues ell0 w W tau q E u) := by
  refine ⟨∫ z, topProfile 203 z ∂volume.prod volume,?_⟩
  intro x hx
  rcases hx with rfl | ⟨test,rfl⟩
  · exact integral_nonneg (topProfile_nonnegative 203)
  · exact densityAverage_le test.top E u _

end OrdinaryDensityTile
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PlanarSliceFourierAngular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript uses angular frequencies in `exp(iηy)`, whereas
mathlib's Fourier transform uses `exp(-2πi xξ)`. These definitions and
identities keep the conversion explicit. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

theorem planarAngularFourier_eq_integral (f : ℝ × ℝ → ℂ) (frequency : ℝ × ℝ) :
    planarAngularFourier f frequency = ∫ z : ℝ × ℝ,
      Complex.exp (-(Complex.I * (z.1 * frequency.1 + z.2 * frequency.2))) * f z
        ∂volume.prod volume := by
  unfold planarAngularFourier planarFourier
  simp only [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLatticeScaleEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-length energy estimate for the original physical source
packets. The profile and lattice assumptions already present in the
source family discharge every envelope and overlap hypothesis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem physicalPlanarPacket_profile_envelope (f : SchwartzMap (ℝ×ℝ) ℂ)
    (n : ℕ) (a b l W theta frequency : ℝ) (hl : l ≠ 0) (hW : W ≠ 0) (z : ℝ×ℝ) :
    ‖physicalPlanarPacket f a b l W theta frequency hl hW z‖ ≤
      planarProfileConstant f n *
        (lineEnvelope a l n z.1 * lineEnvelope (b-theta*a) W n (z.2-theta*z.1)) := by
  rw [physicalPlanarPacket_apply,norm_mul]
  have hphase : ‖Complex.exp ((frequency*((z.2-b)-theta*(z.1-a)):ℝ)*Complex.I)‖ = 1 := by
    simp [Complex.norm_exp]
  rw [hphase,one_mul]
  have h := planar_profile_base_envelope f n 0
    ((z.1-a)/l,((z.2-b)-theta*(z.1-a))/W)
  have hy : ((z.2-b)-theta*(z.1-a))/W =
      ((z.2-theta*z.1)-(b-theta*a))/W := by ring
  simpa only [planarVerticalJet,ite_true, if_true,lineEnvelope,sub_zero,div_one,hy] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeDensityTerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single short-tree term is controlled by its actual density test.
Extra packet decay retains the distance to the horizontal strip. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

private theorem taxicab_quadratic_le (x y : ℝ) :
    1+|x|+|y| ≤ 3*((1+x^2)*(1+y^2)) := by
  have hx : |x|≤1+x^2 := by nlinarith [sq_nonneg (|x|-1),sq_abs x]
  have hy : |y|≤1+y^2 := by nlinarith [sq_nonneg (|y|-1),sq_abs y]
  have ha : 1≤1+x^2 := le_add_of_nonneg_right (sq_nonneg x)
  have hb : 1≤1+y^2 := le_add_of_nonneg_right (sq_nonneg y)
  nlinarith [mul_le_mul_of_nonneg_right ha (show 0≤1+y^2 by positivity),
    mul_le_mul_of_nonneg_left hb (show 0≤1+x^2 by positivity)]

/-- The physical product envelope dominates the density kernel, while
leaving any prescribed number of horizontal decay powers. -/
theorem packet_envelope_density_decay (T : SlopeBox) (D r : ℕ) (z : ℝ×ℝ) :
    lineEnvelope T.x T.length (D+r) z.1 *
      lineEnvelope (T.y-T.slope*T.x) T.width (D+r) (z.2-T.slope*z.1) ≤
      3^D*T.densityKernel D z*lineEnvelope T.x T.length r z.1 := by
  let x := T.horizontal z
  let y := T.transverse z
  let A := 1+x^2
  let B := 1+y^2
  let R := 1+|x|+|y|
  have hA : 1≤A := le_add_of_nonneg_right (sq_nonneg x)
  have hB : 1≤B := le_add_of_nonneg_right (sq_nonneg y)
  have hR : 0<R := by dsimp [R]; positivity
  have hA0 : 0<A := zero_lt_one.trans_le hA
  have hB0 : 0<B := zero_lt_one.trans_le hB
  have hpow : R^D≤3^D*(A^D*B^D) := by
    simpa only [mul_pow,mul_assoc] using
      pow_le_pow_left₀ hR.le (taxicab_quadratic_le x y) D
  have hratio : (A^D*B^D)⁻¹≤3^D*(R^D)⁻¹ := by
    have hdiv : 1/(A^D*B^D)≤3^D/(R^D) := by
      rw [div_le_div_iff₀ (mul_pos (pow_pos hA0 D) (pow_pos hB0 D)) (pow_pos hR D)]
      simpa only [one_mul] using hpow
    simpa only [one_div,div_eq_mul_inv,one_mul] using hdiv
  have hBr : (B^r)⁻¹≤1 := (inv_le_one₀ (pow_pos hB0 r)).2 (one_le_pow₀ hB)
  have heX : lineEnvelope T.x T.length (D+r) z.1=(A^(D+r))⁻¹ := rfl
  have heY : lineEnvelope (T.y-T.slope*T.x) T.width (D+r) (z.2-T.slope*z.1)=
      (B^(D+r))⁻¹ := by
    dsimp [lineEnvelope,B,y,SlopeBox.transverse]
    congr 3
    ring
  have heD : T.densityKernel D z=(R^D)⁻¹ := by
    change (1+(|x|+|y|))^(-(D:ℝ))=(R^D)⁻¹
    rw [←add_assoc,Real.rpow_neg hR.le,Real.rpow_natCast]
  rw [heX,heY,heD]
  change (A^(D+r))⁻¹*(B^(D+r))⁻¹≤3^D*(R^D)⁻¹*(A^r)⁻¹
  calc
    _ = (A^D*B^D)⁻¹*(A^r)⁻¹*(B^r)⁻¹ := by
      rw [pow_add,pow_add,mul_inv_rev,mul_inv_rev,mul_inv_rev]
      ring
    _ ≤ (3^D*(R^D)⁻¹)*(A^r)⁻¹*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hratio (inv_nonneg.mpr (pow_nonneg hA0.le r)))
        hBr (inv_nonneg.mpr (pow_nonneg hB0.le r))
        (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity))
    _ = _ := mul_one _

theorem horizontal_envelope_le_distance (T : SlopeBox) (r : ℕ) {d : ℝ}
    (hd : 0≤d) (z : ℝ×ℝ) (hsep : d≤|z.1-T.x|) :
    lineEnvelope T.x T.length r z.1 ≤ (1+(d/T.length)^2)⁻¹^r := by
  have hrat : d/T.length≤|(z.1-T.x)/T.length| := by
    rw [abs_div,abs_of_pos T.length_pos]
    exact div_le_div_of_nonneg_right hsep T.length_pos.le
  have hs : (d/T.length)^2≤((z.1-T.x)/T.length)^2 := by
    have hh := pow_le_pow_left₀ (div_nonneg hd T.length_pos.le) hrat 2
    simpa only [sq_abs] using hh
  have hp : (1+(d/T.length)^2)^r≤(1+((z.1-T.x)/T.length)^2)^r :=
    pow_le_pow_left₀ (by positivity) (by linarith) r
  have hh := inv_anti₀ (show 0<(1+(d/T.length)^2)^r by positivity) hp
  simpa only [lineEnvelope,inv_pow] using hh

namespace OrdinaryDensityTile

/-- Every admissible test is bounded by the literal density supremum. -/
theorem test_integral_le_density (tile : OrdinaryDensityTile)
    (ell0 w W tau : ℝ) (grid : ℤ) (E : Set (ℝ×ℝ)) (v : ℝ×ℝ → ℝ)
    (test : OrdinaryDensityTest ell0 w W tau grid tile) :
    (∫ z in E ∩ v ⁻¹' scaledAngularCell (w/ell0) grid test.level test.cell,
      test.top.densityKernel 203 z ∂volume.prod volume) ≤
        tile.density ell0 w W tau grid E v*test.top.area := by
  have h := le_csSup (tile.densityValues_bddAbove ell0 w W tau grid E v)
    (show densityAverage test.top E v (scaledAngularCell (w/ell0) grid test.level test.cell) ∈
      tile.densityValues ell0 w W tau grid E v from Or.inr ⟨test,rfl⟩)
  exact (div_le_iff₀ test.top.area_pos).mp h

end OrdinaryDensityTile

/-- One literal physical packet term. Its selector may be complex and
coordinate-dependent; only its original support and norm bound are used. -/
theorem density_test_short_packet_term {κ : Type} [Fintype κ]
    (ell0 w W tau : ℝ) (grid : ℤ) (tile : OrdinaryDensityTile)
    (test : OrdinaryDensityTest ell0 w W tau grid tile)
    (r n : ℕ) (horder : 203+r≤n) (C M sigma eta d : ℝ)
    (hC : 0≤C) (hM : 0≤M) (hsigma : 0 ≤ sigma) (hd : 0≤d)
    (profile : κ → SchwartzMap (ℝ×ℝ) ℂ) (frequency : κ → ℝ)
    (hprofile : ∀ k, planarProfileConstant (profile k) n≤C)
    (c : EuclideanSpace ℂ κ) (hc : ‖c‖ ≤ sigma)
    (selector : κ → ℝ → ℂ) (hselector : ∀ k, Measurable (selector k))
    (hbound : ∀ k s, ‖selector k s‖≤M)
    (hsupport : ∀ k s, selector k s≠0 →
      s∈scaledAngularCell (w/ell0) grid test.level test.cell)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v) (E : Set (ℝ×ℝ))
    (hE : MeasurableSet E) (I : Set ℝ) (hI : MeasurableSet I)
    (hsep : ∀ x∈I, d≤|x-test.top.x|)
    (hdensity : tile.density ell0 w W tau grid E v≤eta) :
    let F := fun z : ℝ×ℝ => WithLp.toLp 2 (fun k => c k*selector k (v z)*
      physicalPlanarPacket (profile k) test.top.x test.top.y test.top.length test.top.width
        test.top.slope (frequency k) test.top.length_pos.ne' test.top.width_pos.ne' z)
    IntegrableOn (fun z => ‖F z‖) (E∩Prod.fst ⁻¹' I) (volume.prod volume) ∧
    (∫ z in E∩Prod.fst ⁻¹' I, ‖F z‖ ∂volume.prod volume) ≤
      (3:ℝ)^203*C*M*sigma*((1+(d/test.top.length)^2)⁻¹^r)*eta*test.top.area := by
  let T := test.top
  let F := fun z : ℝ×ℝ => WithLp.toLp 2 (fun k => c k*selector k (v z)*
    physicalPlanarPacket (profile k) T.x T.y T.length T.width T.slope (frequency k)
      T.length_pos.ne' T.width_pos.ne' z)
  let omega := scaledAngularCell (w/ell0) grid test.level test.cell
  let A := E∩Prod.fst ⁻¹' I
  let tail := (1+(d/T.length)^2)⁻¹^r
  let B := (3:ℝ)^203*C*M*sigma*tail
  have htail : 0≤tail := by dsimp [tail]; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  have homega : MeasurableSet (v ⁻¹' omega) :=
    (scaledAngularCell_measurable _ _ _ _).preimage hv
  have hA : MeasurableSet A := hE.inter (hI.preimage measurable_fst)
  have hF : Measurable (fun z => ‖F z‖) := by
    apply Measurable.norm
    apply (WithLp.measurable_toLp 2 _).comp
    apply measurable_pi_iff.mpr
    intro k
    exact
      (measurable_const.mul ((hselector k).comp hv)).mul
        (physicalPlanarPacket (profile k) T.x T.y T.length T.width T.slope
          (frequency k) T.length_pos.ne' T.width_pos.ne').continuous.measurable
  have hpacket (k : κ) (z : ℝ×ℝ) (hz : z∈A) :
      ‖physicalPlanarPacket (profile k) T.x T.y T.length T.width T.slope
        (frequency k) T.length_pos.ne' T.width_pos.ne' z‖ ≤
      (3:ℝ)^203*C*tail*T.densityKernel 203 z := by
    have hp := physicalPlanarPacket_profile_envelope (profile k) n T.x T.y T.length
      T.width T.slope (frequency k) T.length_pos.ne' T.width_pos.ne' z
    have he := packet_envelope_density_decay T 203 r z
    have hx := horizontal_envelope_le_distance T r hd z (hsep z.1 hz.2)
    calc
      _ ≤ C*(lineEnvelope T.x T.length (203+r) z.1 *
          lineEnvelope (T.y-T.slope*T.x) T.width (203+r) (z.2-T.slope*z.1)) :=
        hp.trans (mul_le_mul (hprofile k)
          (mul_le_mul (lineEnvelope_antitone _ _ _ horder) (lineEnvelope_antitone _ _ _ horder)
            (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
          (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)) hC)
      _ ≤ C*((3:ℝ)^203*T.densityKernel 203 z*lineEnvelope T.x T.length r z.1) :=
        mul_le_mul_of_nonneg_left he hC
      _ ≤ C*((3:ℝ)^203*T.densityKernel 203 z*tail) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx
          (mul_nonneg (by positivity) (T.densityKernel_nonneg 203 z))) hC
      _ = _ := by ring
  have hpoint (z : ℝ×ℝ) (hz : z∈A) :
      ‖F z‖≤B*(v ⁻¹' omega).indicator (T.densityKernel 203) z := by
    by_cases hvz : v z∈omega
    · rw [Set.indicator_of_mem (show z∈v ⁻¹' omega from hvz)]
      let ker : ℝ := (3:ℝ)^203*C*tail*T.densityKernel 203 z
      have hker : 0≤ker :=
        mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hC) htail)
          (T.densityKernel_nonneg 203 z)
      let wave := fun k => selector k (v z)*
        physicalPlanarPacket (profile k) T.x T.y T.length T.width T.slope
          (frequency k) T.length_pos.ne' T.width_pos.ne' z
      have hwave (k : κ) : ‖wave k‖≤M*ker := by
        dsimp only [wave]
        rw [norm_mul]
        exact mul_le_mul (hbound k (v z)) (hpacket k z hz) (norm_nonneg _) hM
      have hp := diagonal_packet_norm c wave (mul_nonneg hM hker) hwave
      calc
        _ = ‖WithLp.toLp 2 (fun k => c k*(selector k (v z)*
            physicalPlanarPacket (profile k) T.x T.y T.length T.width T.slope
              (frequency k) T.length_pos.ne' T.width_pos.ne' z))‖ := by
          dsimp only [F]
          congr 1
          ext k
          simp only [mul_assoc]
        _ ≤ M*((3:ℝ)^203*C*tail*T.densityKernel 203 z)*sigma :=
          hp.trans (mul_le_mul_of_nonneg_left hc (mul_nonneg hM hker))
        _ = _ := by dsimp [B]; ring
    · have hs (k) : selector k (v z)=0 := by
        by_contra hn
        exact hvz (hsupport k (v z) hn)
      have hzero : F z=0 := by
        ext k
        simp only [F,hs,mul_zero,zero_mul,WithLp.ofLp_zero,Pi.zero_apply]
      rw [hzero,norm_zero,Set.indicator_of_notMem (show z∉v ⁻¹' omega from hvz),mul_zero]
  have hmajor : Integrable (fun z => B*(v ⁻¹' omega).indicator (T.densityKernel 203) z)
      (volume.prod volume) :=
    ((T.densityKernel_integrable (by norm_num : (2:ℝ)<203)).indicator homega).const_mul B
  have hfi : IntegrableOn (fun z => ‖F z‖) A (volume.prod volume) :=
    hmajor.integrableOn.mono' hF.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem hA] with z hz
      simpa only [Real.norm_eq_abs,abs_norm] using hpoint z hz)
  refine ⟨hfi,?_⟩
  calc
    _ ≤ ∫ z in A, B*(v ⁻¹' omega).indicator (T.densityKernel 203) z ∂volume.prod volume :=
      setIntegral_mono_on hfi hmajor.integrableOn hA hpoint
    _ = B*∫ z in A∩v ⁻¹' omega, T.densityKernel 203 z ∂volume.prod volume := by
      rw [integral_const_mul,setIntegral_indicator homega]
    _ ≤ B*∫ z in E∩v ⁻¹' omega, T.densityKernel 203 z ∂volume.prod volume := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply setIntegral_mono_set (T.densityKernel_integrable (by norm_num : (2:ℝ)<203)).integrableOn
        (Filter.Eventually.of_forall (fun z => T.densityKernel_nonneg 203 z))
      exact Filter.Eventually.of_forall (fun z hz => ⟨hz.1.1,hz.2⟩)
    _ ≤ B*(eta*T.area) := mul_le_mul_of_nonneg_left
      ((tile.test_integral_le_density ell0 w W tau grid E v test).trans
        (mul_le_mul_of_nonneg_right hdensity T.area_pos.le)) hB
    _ = _ := by dsimp [B,T,tail]; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeCellDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The density factor for a long-tree cell. A literal admissible test
controls the measure of its angularly restricted cell, with polynomial
loss in the transverse cell index. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem one_le_densityKernel_mul (T : SlopeBox) {R : ℝ}
    {z : ℝ×ℝ} (hz : T.radius z≤R) :
    1≤(1+R)^203*T.densityKernel 203 z := by
  have hr : 0<1+T.radius z := by linarith [T.radius_nonnegative z]
  have hp := pow_le_pow_left₀ hr.le (show 1+T.radius z≤1+R by linarith only [hz]) 203
  have h := mul_le_mul_of_nonneg_right hp
    (inv_nonneg.mpr (pow_nonneg hr.le 203))
  rw [mul_inv_cancel₀ (pow_ne_zero _ hr.ne')] at h
  have heq : T.densityKernel 203 z=((1+T.radius z)^(203:ℕ))⁻¹ := by
    change (1+T.radius z)^(-((203:ℕ):ℝ))=((1+T.radius z)^(203:ℕ))⁻¹
    rw [Real.rpow_neg hr.le,Real.rpow_natCast]
  rw [heq]
  exact h

/-- A density test gives the mass bound on any measurable cell on which
its normalized radius is bounded. The constant function is integrable on
the restricted cell as a consequence, without an extra finiteness premise. -/
theorem density_test_cell_mass (ell0 w W tau : ℝ) (grid : ℤ)
    (tile : OrdinaryDensityTile) (test : OrdinaryDensityTest ell0 w W tau grid tile)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (S : Set (ℝ×ℝ)) (hS : MeasurableSet S) (R eta : ℝ) (hR : 0≤R)
    (hradius : ∀ z∈S, test.top.radius z≤R)
    (hdensity : tile.density ell0 w W tau grid E u≤eta) :
    let A := E∩u ⁻¹' scaledAngularCell (w/ell0) grid test.level test.cell∩S
    IntegrableOn (fun _ : ℝ×ℝ => (1:ℝ)) A (volume.prod volume) ∧
    (volume.prod volume).real A≤(1+R)^203*eta*test.top.area := by
  let A := E∩u ⁻¹' scaledAngularCell (w/ell0) grid test.level test.cell∩S
  have hA : MeasurableSet A := (hE.inter
    ((scaledAngularCell_measurable _ _ _ _).preimage hu)).inter hS
  have hB : 0≤(1+R)^203 := pow_nonneg (by linarith only [hR]) _
  have hkernel := test.top.densityKernel_integrable (by norm_num : (2:ℝ)<203)
  have hmajor : IntegrableOn (fun z => (1+R)^203*test.top.densityKernel 203 z) A
      (volume.prod volume) := (hkernel.const_mul _).integrableOn
  have hpoint (z : ℝ×ℝ) (hz : z∈A) : 1≤(1+R)^203*test.top.densityKernel 203 z :=
    one_le_densityKernel_mul test.top (hradius z hz.2)
  have hone : IntegrableOn (fun _ : ℝ×ℝ => (1:ℝ)) A (volume.prod volume) :=
    hmajor.mono' measurable_const.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem hA] with z hz
      simpa only [norm_one] using hpoint z hz)
  refine ⟨hone,?_⟩
  calc
    _ = ∫ _z in A, (1:ℝ) ∂volume.prod volume := by simp only [setIntegral_const,smul_eq_mul,mul_one]; rfl
    _ ≤ ∫ z in A, (1+R)^203*test.top.densityKernel 203 z ∂volume.prod volume :=
      setIntegral_mono_on hone hmajor hA hpoint
    _ = (1+R)^203*∫ z in A, test.top.densityKernel 203 z ∂volume.prod volume := integral_const_mul _ _
    _ ≤ (1+R)^203*∫ z in E∩u ⁻¹' scaledAngularCell (w/ell0) grid test.level test.cell,
        test.top.densityKernel 203 z ∂volume.prod volume := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply setIntegral_mono_set hkernel.integrableOn
        (Filter.Eventually.of_forall (fun z => test.top.densityKernel_nonneg 203 z))
      exact Filter.Eventually.of_forall (fun _ hz => hz.1)
    _ ≤ (1+R)^203*(eta*test.top.area) := mul_le_mul_of_nonneg_left
      ((tile.test_integral_le_density ell0 w W tau grid E u test).trans
        (mul_le_mul_of_nonneg_right hdensity test.top.area_pos.le)) hB
    _ = _ := by ring

namespace SourceWhitney
open DyadicLineGrid

theorem treeCell_measurable (slope y W : ℝ) (k j n : ℤ) :
    MeasurableSet (treeCell slope y W k j n) := by
  exact ((cell_measurable 0 k j).preimage measurable_fst).inter
    (isClosed_le (((continuous_snd.sub (continuous_const.mul continuous_fst)).sub
      continuous_const).sub continuous_const |>.abs) continuous_const).measurableSet

/-- A test centered on the horizontal cell has bounded radius on each
transverse translate. -/
theorem treeCell_radius_bound (T : SlopeBox) (slope y : ℝ) (k j n : ℤ)
    (hx : T.x=center k j) (hy : T.y=y+slope*T.x) (ht : T.slope=slope)
    (hlength : scale k≤T.length) {z : ℝ×ℝ} (hz : z∈treeCell slope y T.width k j n) :
    T.radius z≤1+|(n:ℝ)| := by
  have hX : |T.horizontal z|≤(1/2:ℝ) := by
    have hp := point_center_bound k j hz.1
    rw [←hx] at hp
    rw [SlopeBox.horizontal,abs_div,abs_of_pos T.length_pos]
    apply (div_le_iff₀ T.length_pos).mpr
    linarith only [hp,hlength]
  have hY : |T.transverse z|≤|(n:ℝ)|+1/2 := by
    have hraw : |(z.2-slope*z.1)-y|≤T.width/2+|(n:ℝ)| * T.width := by
      calc
        _ ≤ |(z.2-slope*z.1)-y-(n:ℝ)*T.width|+|(n:ℝ)*T.width| := by simpa only [sub_zero] using abs_sub_le ((z.2-slope*z.1)-y) ((n:ℝ)*T.width) 0
        _ ≤ T.width/2+|(n:ℝ)| * T.width := by
          rw [abs_mul,abs_of_pos T.width_pos]
          linarith only [hz.2]
    rw [SlopeBox.transverse,hy,ht]
    have he : (z.2-(y+slope*T.x))-slope*(z.1-T.x)=(z.2-slope*z.1)-y := by ring
    rw [he,abs_div,abs_of_pos T.width_pos]
    apply (div_le_iff₀ T.width_pos).mpr
    nlinarith only [hraw]
  unfold SlopeBox.radius
  linarith only [hX,hY]

end SourceWhitney
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A disjoint half-open partition underneath the manuscript's closed
transverse cells. Boundary points are retained exactly once. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators ENNReal
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid

theorem transverseCell_measurable (b W : ℝ) (n : ℤ) :
    MeasurableSet (transverseCell b W n) := measurableSet_Ico

theorem transverseCell_bound (b W : ℝ) (n : ℤ) {y : ℝ}
    (hy : y∈transverseCell b W n) : |y-b-(n:ℝ)*W|≤W/2 := by
  exact abs_le.mpr ⟨by linarith [hy.1],by linarith [hy.2]⟩

theorem transverseCell_disjoint (b W : ℝ) (hW : 0<W) :
    Pairwise (Disjoint on transverseCell b W) := by
  have haux (n m : ℤ) (hlt : n < m) :
      Disjoint (transverseCell b W n) (transverseCell b W m) := by
    have hstep : (n:ℝ)+1 ≤ m := by exact_mod_cast (show n+1 ≤ m by omega)
    have hmul := mul_le_mul_of_nonneg_right hstep hW.le
    apply Set.disjoint_left.mpr
    intro y hyn hym
    have hny := hyn.2
    have hmy := hym.1
    linarith
  intro n m hnm
  rcases lt_or_gt_of_ne hnm with hlt | hlt
  · exact haux n m hlt
  · exact (haux m n hlt).symm

theorem mem_transverseCell_floor (b W y : ℝ) (hW : 0<W) :
    y∈transverseCell b W ⌊(y-b)/W+1/2⌋ := by
  have hl := Int.floor_le ((y-b)/W+1/2)
  have hu := Int.lt_floor_add_one ((y-b)/W+1/2)
  have hl' := mul_le_mul_of_nonneg_right hl hW.le
  have hu' := mul_lt_mul_of_pos_right hu hW
  have hc : ((y-b)/W+1/2)*W=y-b+W/2 := by field_simp
  rw [hc] at hl' hu'
  constructor <;> linarith

theorem partitionCell_measurable (b W : ℝ) (p : (ℤ×ℤ)×ℤ) :
    MeasurableSet (partitionCell b W p) :=
  (cell_measurable 0 p.1.1 p.1.2).prod (transverseCell_measurable b W p.2)

theorem partitionCell_finite (b W : ℝ) (p : (ℤ×ℤ)×ℤ) :
    (volume.prod volume) (partitionCell b W p)≠∞ := by
  rw [partitionCell,Measure.prod_prod]
  exact ENNReal.mul_ne_top measure_Ico_lt_top.ne measure_Ico_lt_top.ne

theorem partitionCell_subset_treeCell (b W : ℝ) (p : (ℤ×ℤ)×ℤ) :
    partitionCell b W p⊆treeCell 0 b W p.1.1 p.1.2 p.2 := by
  intro z hz
  refine ⟨hz.1,?_⟩
  simpa only [zero_mul,sub_zero] using transverseCell_bound b W p.2 hz.2

end LipschitzHilbert.SourceWhitney

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SourceTransverseTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The remaining transverse tail in the long-tree density estimate:
412 powers in squared energy absorb twice the density loss 203, leaving
the summable sixth power. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

/-- The transverse tail left by the fixed manuscript exponents is summable. -/
theorem summable_transverse_sixth :
    Summable (fun n : ℤ => ((1+|(n:ℝ)|)^6)⁻¹) := by
  have hs : Summable (fun n : ℕ => (((n:ℝ)+1)^6)⁻¹) := by
    have h := (summable_nat_add_iff (f:=fun n : ℕ => ((n:ℝ)^6)⁻¹) 1).mpr
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1<(6:ℕ)))
    simpa only [Nat.cast_add,Nat.cast_one] using h
  have ha (n : ℕ) : |(n:ℝ)|=(n:ℝ) := abs_of_nonneg n.cast_nonneg
  apply Summable.of_nat_of_neg
  · simpa only [Int.cast_natCast,ha,add_comm] using hs
  · simpa only [Int.cast_neg,Int.cast_natCast,abs_neg,ha,add_comm] using hs

theorem finite_transverse_tail (s : Finset ℤ) :
    ∑ n∈s, ((1+|(n:ℝ)|)^6)⁻¹≤transverseTailConstant :=
  summable_transverse_sixth.sum_le_tsum s (fun _ _ => by positivity)

namespace SourceWhitney
open DyadicLineGrid

/-- For any finite family of small Whitney intervals, the entire
transverse tail has a uniform volume budget. -/
theorem finite_whitney_transverse_budget {ι : Type*} (tiles : Finset ι)
    (x ell : ι → ℝ) (c L W : ℝ) (hL : 0≤L) (hW : 0≤W)
    (hcenters : ∀ i∈tiles, |x i-c|≤L/2)
    (S : Finset (ℤ×ℤ)) (T : Finset ℤ)
    (hWhitney : ∀ p∈S, Whitney tiles x ell p.1 p.2)
    (hscale : ∀ p∈S, scale p.1≤L) :
    (∑ p∈S×ˢT, (scale p.1.1*W)/(1+|(p.2:ℝ)|)^6)≤
      9*L*W*transverseTailConstant := by
  have hS := small_length_budget tiles x ell hL hcenters S hWhitney hscale
  have hT := finite_transverse_tail T
  calc
    _ = (∑ p∈S, scale p.1)*W*(∑ n∈T, ((1+|(n:ℝ)|)^6)⁻¹) := by
      rw [Finset.sum_product,Finset.sum_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [div_eq_mul_inv]
    _ ≤ (9*L)*W*transverseTailConstant := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hS hW) hT
        (Finset.sum_nonneg (fun _ _ => by positivity))
        (mul_nonneg (mul_nonneg (by norm_num) hL) hW)
    _ = _ := by ring

end SourceWhitney
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledRawEnvelope
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Carrier-free raw bounds for the original labeled lattices, before
any bound on the total number of labels is imposed. -/

noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem raw_eq_physical_slice (i : Fin 3) (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) (y t : ℝ) :
    P.raw i j l u k y = planarSchwartzSlice
      (planarCovariantJet (P.physicalPacket t j l u k) (P.frequency k) P.scale i) y t := by
  have h := physicalPlanarPacket_jet_slice (P.profile j l u k) (P.actualX j l u)
    (P.actualZ j l u+t*P.actualX j l u) (P.length j) P.width
    (t+P.rowSlope j l) (P.frequency k) P.scale y t (P.length_pos j).ne' P.width_pos.ne' i
  have hc : P.actualZ j l u+t*P.actualX j l u-t*P.actualX j l u = P.actualZ j l u := by ring
  have hd : t-(t+P.rowSlope j l) = -P.rowSlope j l := by ring
  simpa only [hc,hd,raw,physicalPacket] using h.symm

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCellPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial weights on the actual transverse cells of a tree.
The exponent is kept symbolic so the fixed high order need not expand. -/
noncomputable section
namespace LipschitzHilbert

theorem transverse_cell_polynomial_lower (b W n y : ℝ) (q : ℕ)
    (hW : 0<W) (hy : |y-b-n*W|≤W/2) :
    ((1+|n|)^2/32)^q≤polynomialWeight b (2*W) q y := by
  have hy' : |y-(b+n*W)|≤2*W := by
    have he : y-(b+n*W)=y-b-n*W := by ring
    rw [he]
    linarith
  have h := box_polynomial_weight (b+n*W) (2*W) (-n/2) y q (by positivity) hy'
  have hc : b+n*W+(2*W)*(-n/2)=b := by ring
  rw [hc] at h
  apply le_trans _ h
  apply pow_le_pow_left₀ (by positivity)
  rw [abs_div,abs_neg]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
  nlinarith [abs_nonneg n]

theorem transverse_cell_polynomial_weight (b W n y : ℝ) (q : ℕ)
    (hW : 0<W) (hy : |y-b-n*W|≤W/2) :
    (1+|n|)^(2*q)≤32^q*polynomialWeight b (2*W) q y := by
  have h := transverse_cell_polynomial_lower b W n y q hW hy
  rw [div_pow,←pow_mul] at h
  simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0<(32:ℝ)^q)).mp h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceFrozenCellIntegral
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual frozen long sums are measurable, have finite cell suprema,
and integrate against the original common angular-support mask. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

/-- A bounded measurable function on a finite cell integrates over its
mask with the exact mass of the intersection. -/
theorem masked_cell_norm_integral {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (C A : Set X) (hC : MeasurableSet C) (hA : MeasurableSet A)
    (hfin : μ C≠∞) (f : X → E) (hf : AEStronglyMeasurable f μ)
    (M : ℝ) (hbound : ∀ z∈C, ‖f z‖≤M) :
    IntegrableOn (A.indicator f) C μ ∧
      (∫ z in C, ‖A.indicator f z‖ ∂μ)≤M*μ.real (C∩A) := by
  have : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.mpr hfin
  have hpoint (z : X) (hz : z∈C) :
      ‖A.indicator f z‖≤A.indicator (fun _ => M) z := by
    by_cases ha : z∈A
    · simp only [indicator_of_mem ha]
      exact hbound z hz
    · simp only [indicator_of_notMem ha,norm_zero,le_refl]
  have hi : IntegrableOn (A.indicator f) C μ := by
    apply ((integrable_const M).indicator hA).mono' ((hf.indicator hA).restrict)
    filter_upwards [ae_restrict_mem hC] with z hz
    exact hpoint z hz
  refine ⟨hi,?_⟩
  have hle := integral_mono_ae hi.norm ((integrable_const M).indicator hA)
    (by filter_upwards [ae_restrict_mem hC] with z hz; exact hpoint z hz)
  apply hle.trans_eq
  rw [integral_indicator hA,integral_const]
  simp only [measureReal_def,smul_eq_mul,Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter,Measure.restrict_apply hA]
  rw [Set.inter_comm,mul_comm]

namespace SourceLabeledLattice
open SourceWhitney DyadicLineGrid
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

theorem frozenLongValue_measurable (t r w : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) :
    Measurable (fun z => P.frozenLongValue t r w (u z) c z) := by
  unfold frozenLongValue
  apply Finset.measurable_sum
  intro j _
  by_cases hj : 32*r<P.length j
  · simp only [hj,true_and]
    have hset : MeasurableSet {z | |u z-t|≤w/P.length j} :=
      measurableSet_le (show Measurable (fun z => |u z-t|) by fun_prop) measurable_const
    have hc := (planarSynthesisSchwartz
      (fun a : Σ l : P.labels j, Item j l => c j a.1 a.2)
      (fun a k => P.physicalPacket t j a.1 a.2 k)).continuous.measurable
    have hc' : Measurable (fun z => planarFixedSynthesis
        (fun a : Σ l : P.labels j, Item j l => c j a.1 a.2)
        (fun a k => P.physicalPacket t j a.1 a.2 k) z) := by
      convert hc using 1
      all_goals try with_reducible_and_instances rfl
      funext z
      exact (planarSynthesisSchwartz_apply _ _ z).symm
    exact Measurable.ite hset hc' measurable_const
  · simp only [hj,false_and,ite_false, if_false]
    exact measurable_const

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourcePacketDensity
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary density attached to literal source packets. A keeper in the
packet's original angular cell automatically meets the reference-cone
condition used by the phase-averaging argument. -/
noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem densityTile_length (P : SourceLabeledLattice N κ Label Item) (oldSlope : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (q : P.PacketIndex) :
    P.topLength/DyadicLineGrid.scale (P.densityTile oldSlope cell q).level = P.length q.1 := by
  simp only [densityTile,DyadicLineGrid.scale,zpow_natCast,SourceLabeledLattice.length]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWhitneyDensityTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual parent witness furnishes an admissible density test at a
length between sixteen and thirty-two Whitney lengths. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid

theorem center_mem_cell (k j : ℤ) : center k j∈cell 0 k j := by
  have hs := scale_pos k
  have hr : left 0 k (j+1)=left 0 k j+scale k := by
    simp only [left,Int.cast_add,Int.cast_one]
    ring
  change left 0 k j ≤ center k j ∧ center k j<left 0 k (j+1)
  rw [hr]
  unfold center
  constructor <;> linarith only [hs]

/-- No compatibility of the horizontal grid origin with the packet
length is assumed: the test length is selected in the source scale grid. -/
theorem exists_comparable_test_length (ell0 r : ℝ) (hell0 : 0<ell0) (hr : 0 < r) :
    ∃ level : ℤ, 16*r≤ell0/scale level ∧ ell0/scale level<32*r := by
  obtain ⟨level,hlo,hhi⟩ := exists_mem_Ico_zpow
    (show 0<ell0/(16*r) by positivity) (by norm_num : (1:ℝ)<2)
  change scale level≤ell0/(16*r) at hlo
  change ell0/(16*r) < scale (level+1) at hhi
  have hlo' := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<16) hr)).mp hlo
  have hhi' := (div_lt_iff₀ (mul_pos (by norm_num : (0:ℝ)<16) hr)).mp hhi
  rw [scale_succ] at hhi'
  refine ⟨level,(le_div_iff₀ (scale_pos level)).mpr ?_,(div_lt_iff₀ (scale_pos level)).mpr ?_⟩
  · nlinarith only [hlo']
  · nlinarith only [hhi']

/-- A Whitney interval admitting a tile longer than thirty-two interval
lengths has an actual density test containing its parent witness. -/
theorem exists_whitney_density_test {ι : Type*} (tiles : Finset ι)
    (tile : ι → OrdinaryDensityTile) (ell0 w W tau slope y : ℝ) (grid k j : ℤ)
    (hell0 : 0<ell0) (hW : 0<W)
    (hWhitney : Whitney tiles (fun i => (tile i).center.1)
      (fun i => ell0/scale (tile i).level) k j)
    (hshort : ∀ i∈tiles, ell0/scale (tile i).level≤tau)
    (hcenter : ∀ i∈tiles, |(tile i).center.2-y-slope*(tile i).center.1|≤W/2)
    (hslope : ∀ i∈tiles, slope∈scaledAngularCell (w/ell0) grid (tile i).level (tile i).cell)
    (hlong : ∃ i∈tiles, 32*scale k<ell0/scale (tile i).level) :
    ∃ i∈tiles, ∃ test : OrdinaryDensityTest ell0 w W tau grid (tile i),
      test.top.x=center k j ∧ test.top.y=y+slope*center k j ∧
      test.top.slope=slope ∧ 16*scale k≤test.top.length ∧ test.top.length<32*scale k := by
  obtain ⟨i,hi,hlen,hnear⟩ := parent_witness tiles _ _ hWhitney
  obtain ⟨level,hlo,hhi⟩ := exists_comparable_test_length ell0 (scale k) hell0 (scale_pos k)
  let len := ell0/scale level
  change 16*scale k≤len at hlo
  change len<32*scale k at hhi
  have hlen0 : 0<len := div_pos hell0 (scale_pos level)
  have htau : len≤tau := by
    obtain ⟨s,hs,hslen⟩ := hlong
    exact hhi.le.trans (hslen.le.trans (hshort s hs))
  let T : SlopeBox := ⟨center k j,y+slope*center k j,slope,len,W,hlen0,hW⟩
  have hcenter_mem : (tile i).center∈densitySpatialBox T (1/2) := by
    have hx := hnear (center k j) (center_mem_cell k j)
    have hy := hcenter i hi
    change |(tile i).center.1-center k j|≤(1/2)*len ∧
      |((tile i).center.2-(y+slope*center k j))-slope*((tile i).center.1-center k j)|≤(1/2)*W
    constructor
    · linarith only [hx,hlo,scale_pos k]
    · have he : ((tile i).center.2-(y+slope*center k j))-slope*((tile i).center.1-center k j)=
          (tile i).center.2-y-slope*(tile i).center.1 := by ring
      rw [he]
      linarith only [hy]
  let test : OrdinaryDensityTest ell0 w W tau grid (tile i) := {
    top := T
    level := level
    cell := index grid level (slope/(w/ell0))
    length_eq := rfl
    width_eq := rfl
    length_le := htau
    tile_length_le := by change ell0/scale (tile i).level≤len; linarith only [hlen,hlo,scale_pos k]
    center_mem := hcenter_mem
    slope_mem_tile := hslope i hi
    slope_mem_self := mem_index_cell grid level (slope/(w/ell0)) }
  exact ⟨i,hi,test,rfl,rfl,rfl,hlo,hhi⟩

/-- The test selected from the parent witness gives the manuscript's
polynomial cell-density bound, simultaneously at every transverse index. -/
theorem exists_whitney_cell_density {ι : Type*} (tiles : Finset ι)
    (tile : ι → OrdinaryDensityTile) (ell0 w W tau slope y : ℝ) (grid k j : ℤ)
    (hell0 : 0<ell0) (hW : 0<W)
    (hWhitney : Whitney tiles (fun i => (tile i).center.1)
      (fun i => ell0/scale (tile i).level) k j)
    (hshort : ∀ i∈tiles, ell0/scale (tile i).level≤tau)
    (hcenter : ∀ i∈tiles, |(tile i).center.2-y-slope*(tile i).center.1|≤W/2)
    (hslope : ∀ i∈tiles, slope∈scaledAngularCell (w/ell0) grid (tile i).level (tile i).cell)
    (hlong : ∃ i∈tiles, 32*scale k<ell0/scale (tile i).level)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (eta : ℝ) (heta : 0≤eta)
    (hdensity : ∀ i∈tiles, (tile i).density ell0 w W tau grid E u≤eta) :
    ∃ i∈tiles, ∃ test : OrdinaryDensityTest ell0 w W tau grid (tile i),
      test.top.x=center k j ∧ test.top.y=y+slope*center k j ∧
      test.top.slope=slope ∧ 16*scale k≤test.top.length ∧ test.top.length<32*scale k ∧
      ∀ n : ℤ,
        let A := E∩u ⁻¹' scaledAngularCell (w/ell0) grid test.level test.cell∩treeCell slope y W k j n
        IntegrableOn (fun _ : ℝ×ℝ => (1:ℝ)) A (volume.prod volume) ∧
        (volume.prod volume).real A≤32*(2:ℝ)^203*eta*(1+|(n:ℝ)|)^203*scale k*W := by
  obtain ⟨i,hi,test,hx,hy,ht,hlo,hhi⟩ := exists_whitney_density_test tiles tile ell0 w W tau slope y
    grid k j hell0 hW hWhitney hshort hcenter hslope hlong
  refine ⟨i,hi,test,hx,hy,ht,hlo,hhi,?_⟩
  intro n
  have hR : 0≤1+|(n:ℝ)| := by positivity
  have hrad : ∀ z∈treeCell slope y W k j n, test.top.radius z≤1+|(n:ℝ)| := by
    intro z hz
    apply treeCell_radius_bound test.top slope y k j n hx
      (by simpa only [hx] using hy) ht (by linarith only [hlo,scale_pos k])
    simpa only [test.width_eq] using hz
  have hm := density_test_cell_mass ell0 w W tau grid (tile i) test E hE u hu
    (treeCell slope y W k j n) (treeCell_measurable slope y W k j n)
    (1+|(n:ℝ)|) eta hR hrad (hdensity i hi)
  refine ⟨hm.1,hm.2.trans ?_⟩
  have hpow : (1+(1+|(n:ℝ)|))^203≤(2:ℝ)^203*(1+|(n:ℝ)|)^203 := by
    rw [←mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    linarith only [abs_nonneg (n:ℝ)]
  have hpow0 : 0≤(2:ℝ)^203*(1+|(n:ℝ)|)^203 := by positivity
  calc
    (1+(1+|(n:ℝ)|))^203*eta*test.top.area ≤
        ((2:ℝ)^203*(1+|(n:ℝ)|)^203)*eta*test.top.area :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow heta) test.top.area_pos.le
    _ ≤ ((2:ℝ)^203*(1+|(n:ℝ)|)^203)*eta*((32*scale k)*W) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hpow0 heta)
      rw [SlopeBox.area,test.width_eq]
      exact mul_le_mul_of_nonneg_right hhi.le hW.le
    _ = _ := by ring

end LipschitzHilbert.SourceWhitney

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLongTreeSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original long-packet angular supports lie in the cell of the actual
Whitney density test. This is the common indicator kept on the frozen
main term and the selector error. -/
noncomputable section
open Set
namespace LipschitzHilbert

namespace OrdinaryDensityTest

theorem contains_longer_angular_cell {ell0 w W tau : ℝ} {grid : ℤ}
    {witness : OrdinaryDensityTile} (test : OrdinaryDensityTest ell0 w W tau grid witness)
    (hell0 : 0<ell0) (tile : OrdinaryDensityTile)
    (hlen : test.top.length≤ell0/DyadicLineGrid.scale tile.level)
    (hslope : test.top.slope∈scaledAngularCell (w/ell0) grid tile.level tile.cell) :
    scaledAngularCell (w/ell0) grid tile.level tile.cell ⊆
      scaledAngularCell (w/ell0) grid test.level test.cell := by
  have hlevel : tile.level≤test.level := density_dyadic_length_order hell0
    (by simpa only [test.length_eq] using hlen)
  exact scaledAngularCell_subset hlevel ⟨test.top.slope,test.slope_mem_self,hslope⟩

end OrdinaryDensityTest

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourcePacketLongCell
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Long-tree cell density for literal source packets. The test and its
common angular cell are obtained from the actual Whitney parent witness. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- The original long selectors all live in one angular cell whose mass
on every transverse strip has the density bound from the manuscript. -/
theorem source_whitney_cell_density (P : SourceLabeledLattice N κ Label Item)
    (oldSlope y : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid k j : ℤ) (w tau : ℝ)
    (htime : P.topLength≤tau)
    (hWhitney : Whitney (Finset.univ : Finset P.PacketIndex)
      (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1) k j)
    (hY : ∀ q : P.PacketIndex, |P.actualZ q.1 q.2.1 q.2.2-y|≤P.width/2)
    (hreference : ∀ q : P.PacketIndex, oldSlope∈
      scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (hlong : ∃ q : P.PacketIndex, 32*DyadicLineGrid.scale k<P.length q.1)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (eta : ℝ) (heta : 0≤eta)
    (hdensity : ∀ q, P.ordinaryDensity oldSlope cell grid w tau E u q≤eta) :
    ∃ q : P.PacketIndex, ∃ test : OrdinaryDensityTest P.topLength w P.width tau grid (P.densityTile oldSlope cell q),
      test.top.x=center k j ∧ test.top.y=y+oldSlope*center k j ∧ test.top.slope=oldSlope ∧
      16*DyadicLineGrid.scale k≤test.top.length ∧ test.top.length<32*DyadicLineGrid.scale k ∧
      (∀ r : P.PacketIndex, 32*DyadicLineGrid.scale k<P.length r.1 →
        scaledAngularCell (w/P.topLength) grid r.1.val (cell r.1 r.2.1) ⊆
          scaledAngularCell (w/P.topLength) grid test.level test.cell) ∧
      (∀ n : ℤ,
        let A := E∩u ⁻¹' scaledAngularCell (w/P.topLength) grid test.level test.cell∩
          treeCell oldSlope y P.width k j n
        IntegrableOn (fun _ : ℝ×ℝ => (1:ℝ)) A (volume.prod volume) ∧
        (volume.prod volume).real A≤32*(2:ℝ)^203*eta*(1+|(n:ℝ)|)^203*DyadicLineGrid.scale k*P.width) := by
  have hgeom : Whitney (Finset.univ : Finset P.PacketIndex)
      (fun q => (P.densityTile oldSlope cell q).center.1)
      (fun q => P.topLength/DyadicLineGrid.scale (P.densityTile oldSlope cell q).level) k j := by
    simpa only [densityTile,DyadicLineGrid.scale,zpow_natCast,SourceLabeledLattice.length] using hWhitney
  have hshort (q : P.PacketIndex) (_hq : q∈(Finset.univ : Finset P.PacketIndex)) :
      P.topLength/DyadicLineGrid.scale (P.densityTile oldSlope cell q).level≤tau := by
    rw [P.densityTile_length]
    exact (div_le_self P.topLength_pos.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))).trans htime
  have hcenter (q : P.PacketIndex) (_hq : q∈(Finset.univ : Finset P.PacketIndex)) :
      |(P.densityTile oldSlope cell q).center.2-y-oldSlope*(P.densityTile oldSlope cell q).center.1|≤P.width/2 := by
    have h := hY q
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    dsimp [densityTile]
    ring
  have hangle (q : P.PacketIndex) (_hq : q∈(Finset.univ : Finset P.PacketIndex)) :
      oldSlope∈scaledAngularCell (w/P.topLength) grid
        (P.densityTile oldSlope cell q).level (P.densityTile oldSlope cell q).cell := hreference q
  have hlong' : ∃ q∈(Finset.univ : Finset P.PacketIndex), 32*DyadicLineGrid.scale k<
      P.topLength/DyadicLineGrid.scale (P.densityTile oldSlope cell q).level := by
    obtain ⟨q,hq⟩ := hlong
    exact ⟨q,Finset.mem_univ q,by simpa only [P.densityTile_length] using hq⟩
  obtain ⟨q,_hq,test,hx,hy,ht,hlo,hhi,hmass⟩ := exists_whitney_cell_density
    (Finset.univ : Finset P.PacketIndex) (P.densityTile oldSlope cell)
    P.topLength w P.width tau oldSlope y grid k j P.topLength_pos P.width_pos
    hgeom hshort hcenter hangle hlong' E hE u hu eta heta (fun q _ => hdensity q)
  refine ⟨q,test,hx,hy,ht,hlo,hhi,?_,hmass⟩
  intro r hr
  have hlen : test.top.length≤P.topLength/DyadicLineGrid.scale (P.densityTile oldSlope cell r).level := by
    rw [P.densityTile_length]
    exact hhi.le.trans hr.le
  exact test.contains_longer_angular_cell P.topLength_pos (P.densityTile oldSlope cell r)
    hlen (by simpa only [ht,densityTile] using hreference r)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourcePacketOwnDensity
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Own-box density tests for the literal source packets, and the resulting
short-packet bound on every horizontal Whitney strip. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- A literal source packet restricted to a Whitney strip. Its decay
factor is precisely the one summed in `SourceShortTreeSum`. -/
theorem own_packet_whitney_density_bound
    (oldSlope : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (w tau : ℝ)
    (q : P.PacketIndex) (hlen : P.length q.1≤tau)
    (hslope : oldSlope+P.rowSlope q.1 q.2.1 ∈
      scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (horder : 205≤2*P.order) (M sigma eta : ℝ) (hM : 0≤M) (hsigma : 0 ≤ sigma)
    (coefficient : EuclideanSpace ℂ κ) (hcoefficient : ‖coefficient‖ ≤ sigma)
    (selector : κ → ℝ → ℂ) (hselector : ∀ a, Measurable (selector a))
    (hbound : ∀ a s, ‖selector a s‖≤M)
    (hsupport : ∀ a s, selector a s≠0 →
      s∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (E : Set (ℝ×ℝ)) (hE : MeasurableSet E)
    (hdensity : P.ordinaryDensity oldSlope cell grid w tau E u q≤eta) (k j : ℤ) :
    let F := fun z : ℝ×ℝ => WithLp.toLp 2 (fun a => coefficient a*selector a (u z)*
      P.physicalPacket oldSlope q.1 q.2.1 q.2.2 a z)
    IntegrableOn (fun z => ‖F z‖) (E∩Prod.fst ⁻¹' DyadicLineGrid.cell 0 k j) (volume.prod volume) ∧
    (∫ z in E∩Prod.fst ⁻¹' DyadicLineGrid.cell 0 k j, ‖F z‖ ∂volume.prod volume) ≤
      (3:ℝ)^203*P.profileBound*M*sigma*eta*(P.length q.1)*P.width*
        (1+(SourceWhitney.stripDistance (SourceWhitney.center k j) (DyadicLineGrid.scale k)
          (P.actualX q.1 q.2.1 q.2.2)/(P.length q.1))^2)⁻¹^2 := by
  let test := P.ownDensityTest oldSlope cell grid w tau q hlen hslope
  have h := density_test_short_packet_term P.topLength w P.width tau grid
    (P.densityTile oldSlope cell q) test 2 (2*P.order) horder
    P.profileBound M sigma eta
    (SourceWhitney.stripDistance (SourceWhitney.center k j) (DyadicLineGrid.scale k)
      (P.actualX q.1 q.2.1 q.2.2))
    P.profileBound_pos.le hM hsigma (SourceWhitney.stripDistance_nonneg _ _ _)
    (P.profile q.1 q.2.1 q.2.2) P.frequency (P.profile_bound q.1 q.2.1 q.2.2)
    coefficient hcoefficient selector hselector hbound hsupport u hu E hE
    (DyadicLineGrid.cell 0 k j) (DyadicLineGrid.cell_measurable 0 k j)
    (fun x hx => SourceWhitney.stripDistance_le_point (P.actualX q.1 q.2.1 q.2.2) k j hx)
    hdensity
  refine ⟨h.1,?_⟩
  exact h.2.trans_eq (by simp only [test,ownDensityTest,ownBox,SlopeBox.area]; ring)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourcePacketShear
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing to a reference direction is an exact shear of the original
packets. The Fourier wedge and vertical bin are transported exactly. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert

theorem planarAngularFourier_slopeShear (f : ℝ×ℝ → ℂ) (t xi eta : ℝ) :
    planarAngularFourier (fun z => f (slopeShear t z)) (xi,eta)=
      planarAngularFourier f (xi-t*eta,eta) := by
  rw [planarAngularFourier_eq_integral,planarAngularFourier_eq_integral]
  have h := (slopeShear_measurePreserving t).integral_comp (slopeShear t).measurableEmbedding
    (fun z : ℝ×ℝ => Complex.exp (-(Complex.I*(z.1*(xi-t*eta,eta).1+
      z.2*(xi-t*eta,eta).2)))*f z)
  refine Eq.trans ?_ h
  apply integral_congr_ae
  filter_upwards [] with z
  congr 2
  change -(Complex.I*((z.1:ℂ)*(xi:ℂ)+(z.2:ℂ)*(eta:ℂ)))=
    -(Complex.I*((z.1:ℂ)*((xi-t*eta:ℝ):ℂ)+((z.2+t*z.1:ℝ):ℂ)*(eta:ℂ)))
  push_cast
  ring

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem physicalPacket_slopeShear (t : ℝ) (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) (z : ℝ×ℝ) :
    P.physicalPacket t j l u k (slopeShear t z)=P.physicalPacket 0 j l u k z := by
  simp only [physicalPacket,physicalPlanarPacket_apply,zero_mul,add_zero,zero_add]
  change Complex.exp (((P.frequency k*
      ((z.2+t*z.1-(P.actualZ j l u+t*P.actualX j l u))-
        (t+P.rowSlope j l)*(z.1-P.actualX j l u))):ℝ)*Complex.I)*
    P.profile j l u k ((z.1-P.actualX j l u)/P.length j,
      ((z.2+t*z.1-(P.actualZ j l u+t*P.actualX j l u))-
        (t+P.rowSlope j l)*(z.1-P.actualX j l u))/P.width)=_
  have he : (z.2+t*z.1-(P.actualZ j l u+t*P.actualX j l u))-
      (t+P.rowSlope j l)*(z.1-P.actualX j l u)=
      (z.2-P.actualZ j l u)-P.rowSlope j l*(z.1-P.actualX j l u) := by ring
  rw [he]

theorem physicalPacket_shear_fourier (t : ℝ) (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) (xi eta : ℝ) :
    planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)=
      planarAngularFourier (P.physicalPacket t j l u k) (xi-t*eta,eta) := by
  have he : (P.physicalPacket 0 j l u k : ℝ×ℝ → ℂ)=
      fun z => P.physicalPacket t j l u k (slopeShear t z) := by
    funext z
    exact (P.physicalPacket_slopeShear t j l u k z).symm
  rw [he,planarAngularFourier_slopeShear]

theorem reference_packet_spectrum (t w cStar cEta CEta : ℝ)
    (hspectrum : ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket t j l u k) (xi,eta)≠0 →
      |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta) :
    ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
      |xi+P.rowSlope j l*eta| ≤ cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta := by
  intro j l u k xi eta hn
  rw [P.physicalPacket_shear_fourier t] at hn
  have h := hspectrum j l u k (xi-t*eta) eta hn
  have he : xi-t*eta+(t+P.rowSlope j l)*eta=xi+P.rowSlope j l*eta := by ring
  simpa only [he] using h

theorem reference_packet_bin (t Cv : ℝ)
    (hbin : ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket t j l u k) (xi,eta)≠0 →
      |eta-P.frequency k|≤Cv/P.width) :
    ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
      |eta-P.frequency k|≤Cv/P.width := by
  intro j l u k xi eta hn
  rw [P.physicalPacket_shear_fourier t] at hn
  exact hbin j l u k (xi-t*eta) eta hn

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShortDyadicBudget
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short-tree estimates are summed over dyadic lengths with constants
independent of the number of retained scales. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney

/-- Any finite selection of dyadic lengths below `R` has sum at most `2R`. -/
theorem finite_dyadic_length_sum (L R : ℝ) (hR : 0≤R)
    (S : Finset ℕ) (hbound : ∀ j∈S, L/(2:ℝ)^j≤R) :
    (∑ j∈S, L/(2:ℝ)^j) ≤ 2*R := by
  classical
  by_cases hs : S.Nonempty
  · let m := S.min' hs
    have hm : m∈S := S.min'_mem hs
    have hmin (j) (hj : j∈S) : m≤j := S.min'_le j hj
    have hpow (j) (hj : j∈S) :
        L/(2:ℝ)^j = (L/(2:ℝ)^m)*(1/2:ℝ)^(j-m) := by
      have hp : (2:ℝ)^j = 2^m*2^(j-m) := by
        rw [←pow_add,Nat.add_sub_of_le (hmin j hj)]
      rw [hp,one_div_pow]
      ring
    have hinj : Set.InjOn (fun j : ℕ => j-m) (S:Set ℕ) := by
      intro j hj k hk heq
      change j-m=k-m at heq
      have hj' := hmin j hj
      have hk' := hmin k hk
      omega
    have hmap : S.image (fun j => j-m) ⊆ Finset.range (S.max' hs+1) := by
      intro n hn
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hn
      have hj' := S.le_max' j hj
      simp only [Finset.mem_range]
      omega
    have hsum := OAI.sum_le_sum_of_injOn (fun j : ℕ => j-m) hinj hmap
      (s:=S) (t:=Finset.range (S.max' hs+1))
      (f:=fun j => L/(2:ℝ)^j) (g:=fun n => R*(1/2:ℝ)^n)
      (fun j hj => by
        rw [hpow j hj]
        exact mul_le_mul_of_nonneg_right (hbound m hm) (by positivity))
      (fun _ _ _ => mul_nonneg hR (by positivity))
    calc
      _ ≤ ∑ n∈Finset.range (S.max' hs+1), R*(1/2:ℝ)^n := hsum
      _ = R*∑ n∈Finset.range (S.max' hs+1), (1/2:ℝ)^n := (Finset.mul_sum _ _ _).symm
      _ ≤ R*2 := mul_le_mul_of_nonneg_left (sum_half_powers_le_two _) hR
      _ = _ := mul_comm _ _
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs,Finset.sum_empty]
    positivity

/-- The far-strip gain survives summation of every selected length. -/
theorem finite_dyadic_decay_sum (L R r : ℝ) (hL : 0<L) (hR : 0≤R) (hr : 0 < r)
    (S : Finset ℕ) (hbound : ∀ j∈S, L/(2:ℝ)^j≤R) :
    (∑ j∈S, (L/(2:ℝ)^j)*((L/(2:ℝ)^j)/r)^2) ≤ 2*R*(R/r)^2 := by
  have hratio (j) (hj : j∈S) : ((L/(2:ℝ)^j)/r)^2≤(R/r)^2 :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right (hbound j hj) hr.le) 2
  calc
    _ ≤ ∑ j∈S, (L/(2:ℝ)^j)*(R/r)^2 :=
      Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hratio j hj) (by positivity))
    _ = (∑ j∈S, L/(2:ℝ)^j)*(R/r)^2 := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (finite_dyadic_length_sum L R hR S hbound) (sq_nonneg _)

/-- The same short-length sum in the finite scale indexing used by packets. -/
theorem fin_short_dyadic_length_sum (N : ℕ) (L R : ℝ) (hR : 0≤R) :
    (∑ j : Fin N, if L/(2:ℝ)^j.val≤R then L/(2:ℝ)^j.val else 0) ≤ 2*R := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if L/(2:ℝ)^j≤R then L/(2:ℝ)^j else 0) N,
    ←Finset.sum_filter]
  exact finite_dyadic_length_sum L R hR
    ((Finset.range N).filter (fun j => L/(2:ℝ)^j≤R))
    (fun _ hj => (Finset.mem_filter.mp hj).2)

/-- All packet lengths together retain a quadratic far-strip gain. -/
theorem fin_dyadic_decay_sum (N : ℕ) (L r : ℝ) (hL : 0<L) (hr : 0 < r) :
    (∑ j : Fin N, (L/(2:ℝ)^j.val)*((L/(2:ℝ)^j.val)/r)^2) ≤ 2*L*(L/r)^2 := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (L/(2:ℝ)^j)*((L/(2:ℝ)^j)/r)^2) N]
  apply finite_dyadic_decay_sum L L r hL hL.le hr
  intro j _
  exact div_le_self hL.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))

/-- The squared ratios from a fixed length to larger dyadic lengths have
a uniformly bounded sum, also when the dyadic levels are negative. -/
theorem finite_large_scale_square_sum (L : ℝ) (hL : 0<L)
    (S : Finset ℤ) (hscale : ∀ k∈S, L≤DyadicLineGrid.scale k) :
    (∑ k∈S, (L/DyadicLineGrid.scale k)^2) ≤ 2 := by
  classical
  by_cases hs : S.Nonempty
  · let m := S.min' hs
    have hm : m∈S := S.min'_mem hs
    have hmin (k) (hk : k∈S) : m≤k := S.min'_le k hk
    have hp (k) (hk : k∈S) :
        DyadicLineGrid.scale k = DyadicLineGrid.scale m*(2:ℝ)^((k-m).toNat) := by
      unfold DyadicLineGrid.scale
      rw [←zpow_natCast,←zpow_add₀ (by norm_num : (2:ℝ)≠0)]
      congr 1
      have hk' := hmin k hk
      rw [Int.toNat_of_nonneg (by omega)]
      ring
    have hc : 0≤L/DyadicLineGrid.scale m := div_nonneg hL.le (DyadicLineGrid.scale_pos m).le
    have hc1 : L/DyadicLineGrid.scale m≤1 :=
      (div_le_one (DyadicLineGrid.scale_pos m)).mpr (hscale m hm)
    have hpoint (k) (hk : k∈S) :
        (L/DyadicLineGrid.scale k)^2≤(1/2:ℝ)^((k-m).toNat) := by
      have he : L/DyadicLineGrid.scale k =
          (L/DyadicLineGrid.scale m)*(1/2:ℝ)^((k-m).toNat) := by
        rw [hp k hk,one_div_pow]
        ring
      rw [he]
      have ht0 : 0≤(1/2:ℝ)^((k-m).toNat) := by positivity
      have ht1 : (1/2:ℝ)^((k-m).toNat)≤1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hmul := mul_le_mul_of_nonneg_right hc1 ht0
      have hmul0 : 0≤(L/DyadicLineGrid.scale m)*(1/2:ℝ)^((k-m).toNat) := mul_nonneg hc ht0
      have hsq := pow_le_pow_left₀ hmul0 (by simpa only [one_mul] using hmul) 2
      nlinarith only [hsq,ht0,ht1]
    have hinj : Set.InjOn (fun k : ℤ => (k-m).toNat) (S:Set ℤ) := by
      intro j hj k hk heq
      change (j-m).toNat=(k-m).toNat at heq
      have hj' := hmin j hj
      have hk' := hmin k hk
      omega
    have hmap : S.image (fun k => (k-m).toNat) ⊆ Finset.range ((S.max' hs-m).toNat+1) := by
      intro n hn
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
      have hk' := S.le_max' k hk
      have hk'' := hmin k hk
      simp only [Finset.mem_range]
      omega
    exact (OAI.sum_le_sum_of_injOn (fun k : ℤ => (k-m).toNat) hinj hmap
      (s:=S) (t:=Finset.range ((S.max' hs-m).toNat+1))
      (f:=fun k => (L/DyadicLineGrid.scale k)^2) (g:=fun n => (1/2:ℝ)^n)
      hpoint (fun _ _ _ => by positivity)).trans (sum_half_powers_le_two _)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs,Finset.sum_empty]
    norm_num

end LipschitzHilbert.SourceWhitney

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShortTreeSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summation of the short-tree density tails over the actual center
lattice and all retained dyadic scales. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney

/-- A single length, with the actual sheared lattice and strip cutoff. -/
theorem sheared_strip_kernel_sum (a b ell W delta c y r : ℝ)
    (hell : 0<ell) (hW : 0<W) (S : Finset (ℤ×ℤ))
    (hstrip : ∀ p∈S, |b+delta*ell*p.1+W*p.2-y|≤W)
    (hsep : ∀ p∈S, ell ≤ r → r ≤ stripDistance c r (a+ell*p.1)) :
    (∑ p∈S, (1+(stripDistance c r (a+ell*p.1)/ell)^2)⁻¹^2) ≤
      144*(4*Real.pi)^2 := by
  calc
    _ ≤ ∑ p∈S, 8*lineEnvelope (a+ell*p.1) ell 1 c :=
      Finset.sum_le_sum (fun p hp => strip_kernel_le_center hell (hsep p hp))
    _ = 8*∑ p∈S, lineEnvelope (a+ell*p.1) ell 1 c := (Finset.mul_sum _ _ _).symm
    _ ≤ 8*(18*(4*Real.pi)^2) := mul_le_mul_of_nonneg_left
      (sheared_strip_overlap a b ell W delta c y hell hW S hstrip) (by norm_num)
    _ = _ := by ring

/-- A single short length retains the squared length-to-distance gain. -/
theorem sheared_strip_kernel_decay_sum (a b ell W delta c y r : ℝ)
    (hell : 0<ell) (hW : 0<W) (hr : 0 < r) (S : Finset (ℤ×ℤ))
    (hstrip : ∀ p∈S, |b+delta*ell*p.1+W*p.2-y|≤W)
    (hsep : ∀ p∈S, r ≤ stripDistance c r (a+ell*p.1)) :
    (∑ p∈S, (1+(stripDistance c r (a+ell*p.1)/ell)^2)⁻¹^2) ≤
      144*(4*Real.pi)^2*(ell/r)^2 := by
  calc
    _ ≤ ∑ p∈S, 8*lineEnvelope (a+ell*p.1) ell 1 c*(ell/r)^2 :=
      Finset.sum_le_sum (fun p hp => strip_kernel_le_center_decay hell hr (hsep p hp))
    _ = 8*(∑ p∈S, lineEnvelope (a+ell*p.1) ell 1 c)*(ell/r)^2 := by
      rw [←Finset.sum_mul,←Finset.mul_sum]
    _ ≤ 8*(18*(4*Real.pi)^2)*(ell/r)^2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (sheared_strip_overlap a b ell W delta c y hell hW S hstrip) (by norm_num)) (sq_nonneg _)
    _ = _ := by ring

end LipschitzHilbert.SourceWhitney

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourcePacketShortSum
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short-tree lattice sums for the literal labeled source family.
The Whitney separation is derived from the actual packet centers. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney DyadicLineGrid
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem label_short_kernel_sum (y : ℝ) (k m : ℤ) (hallowed : P.whitneyAllowed k m)
    (hcenter : ∀ j l u, |P.actualZ j l u-y|≤P.width) (j : Fin N) (l : P.labels j) :
    (∑ u : Item j l, P.shortKernel k m ⟨j,l,u⟩) ≤ 144*(4*Real.pi)^2 := by
  classical
  let S := Finset.univ.image (P.site j l)
  have hstrip : ∀ p∈S, |P.originZ j l+P.rowSlope j l*P.length j*p.1+P.width*p.2-y|≤P.width := by
    intro p hp
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hp
    exact hcenter j l u
  have hsep : ∀ p∈S, P.length j≤DyadicLineGrid.scale k →
      DyadicLineGrid.scale k ≤ stripDistance (center k m) (DyadicLineGrid.scale k) (P.originX j l+P.length j*p.1) := by
    intro p hp hlen
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hp
    exact (stripDistance_large _ _ _ hallowed (Finset.mem_univ ⟨j,l,u⟩) hlen).le
  have h := sheared_strip_kernel_sum (P.originX j l) (P.originZ j l) (P.length j)
    P.width (P.rowSlope j l) (center k m) y (DyadicLineGrid.scale k) (P.length_pos j) P.width_pos S hstrip hsep
  rw [Finset.sum_image (fun _ _ _ _ he => P.site_injective j l he)] at h
  exact h

theorem label_short_kernel_decay_sum (y : ℝ) (k m : ℤ) (hallowed : P.whitneyAllowed k m)
    (hcenter : ∀ j l u, |P.actualZ j l u-y|≤P.width)
    (j : Fin N) (l : P.labels j) (hlen : P.length j≤DyadicLineGrid.scale k) :
    (∑ u : Item j l, P.shortKernel k m ⟨j,l,u⟩) ≤
      144*(4*Real.pi)^2*(P.length j/DyadicLineGrid.scale k)^2 := by
  classical
  let S := Finset.univ.image (P.site j l)
  have hstrip : ∀ p∈S, |P.originZ j l+P.rowSlope j l*P.length j*p.1+P.width*p.2-y|≤P.width := by
    intro p hp
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hp
    exact hcenter j l u
  have hsep : ∀ p∈S, DyadicLineGrid.scale k ≤ stripDistance (center k m) (DyadicLineGrid.scale k) (P.originX j l+P.length j*p.1) := by
    intro p hp
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hp
    exact (stripDistance_large _ _ _ hallowed (Finset.mem_univ ⟨j,l,u⟩) hlen).le
  have h := sheared_strip_kernel_decay_sum (P.originX j l) (P.originZ j l) (P.length j)
    P.width (P.rowSlope j l) (center k m) y (DyadicLineGrid.scale k) (P.length_pos j) P.width_pos (scale_pos k) S hstrip hsep
  rw [Finset.sum_image (fun _ _ _ _ he => P.site_injective j l he)] at h
  exact h

theorem row_short_kernel_sum (B : ℕ) (hcard : ∀ j, (P.labels j).card≤B)
    (y : ℝ) (k m : ℤ) (hallowed : P.whitneyAllowed k m)
    (hcenter : ∀ j l u, |P.actualZ j l u-y|≤P.width) (j : Fin N) :
    (∑ l : P.labels j, ∑ u : Item j l, P.shortKernel k m ⟨j,l,u⟩) ≤
      144*(4*Real.pi)^2*B := by
  calc
    _ ≤ ∑ _l : P.labels j, 144*(4*Real.pi)^2 :=
      Finset.sum_le_sum (fun l _ => P.label_short_kernel_sum y k m hallowed hcenter j l)
    _ = (P.labels j).card*(144*(4*Real.pi)^2) := by simp
    _ ≤ (B:ℝ)*(144*(4*Real.pi)^2) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast hcard j) (by positivity)
    _ = _ := mul_comm _ _

/-- The short-tail majorant summed over every packet with length at most
`R`. Labels cost only their fixed per-scale multiplicity. -/
theorem packet_short_mass_sum (B : ℕ) (hcard : ∀ j, (P.labels j).card≤B)
    (y R : ℝ) (hR : 0≤R) (k m : ℤ) (hallowed : P.whitneyAllowed k m)
    (hcenter : ∀ j l u, |P.actualZ j l u-y|≤P.width) :
    (∑ q : P.PacketIndex, if P.length q.1≤R then
      P.length q.1*P.width*P.shortKernel k m q else 0) ≤
      288*(4*Real.pi)^2*B*P.width*R := by
  classical
  have hwidth := P.width_pos
  have hrow (j : Fin N) :
      (∑ l : P.labels j, ∑ u : Item j l, if P.length j≤R then
        P.length j*P.width*P.shortKernel k m ⟨j,l,u⟩ else 0) ≤
      (144*(4*Real.pi)^2*B*P.width)*(if P.length j≤R then P.length j else 0) := by
    by_cases hlen : P.length j≤R
    · simp only [ite_eq_left hlen]
      simp_rw [←Finset.mul_sum]
      have h := mul_le_mul_of_nonneg_left (P.row_short_kernel_sum B hcard y k m hallowed hcenter j)
        (mul_nonneg (P.length_pos j).le P.width_pos.le)
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      ring
    · simp only [ite_eq_right hlen,Finset.sum_const_zero,mul_zero,le_refl]
  calc
    _ = ∑ j : Fin N, ∑ l : P.labels j, ∑ u : Item j l, if P.length j≤R then
      P.length j*P.width*P.shortKernel k m ⟨j,l,u⟩ else 0 := by simp only [Fintype.sum_sigma]
    _ ≤ ∑ j : Fin N, (144*(4*Real.pi)^2*B*P.width)*(if P.length j≤R then P.length j else 0) :=
      Finset.sum_le_sum (fun j _ => hrow j)
    _ = (144*(4*Real.pi)^2*B*P.width)*∑ j : Fin N, if P.length j≤R then P.length j else 0 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (144*(4*Real.pi)^2*B*P.width)*(2*R) := mul_le_mul_of_nonneg_left
      (fin_short_dyadic_length_sum N P.topLength R hR) (by positivity)
    _ = _ := by ring

/-- The far-strip majorant over the entire packet family retains decay
in the ratio of top length to Whitney length. -/
theorem packet_short_mass_decay_sum (B : ℕ) (hcard : ∀ j, (P.labels j).card≤B)
    (y : ℝ) (k m : ℤ) (hallowed : P.whitneyAllowed k m)
    (hcenter : ∀ j l u, |P.actualZ j l u-y|≤P.width) (hlarge : P.topLength≤DyadicLineGrid.scale k) :
    (∑ q : P.PacketIndex, P.length q.1*P.width*P.shortKernel k m q) ≤
      288*(4*Real.pi)^2*B*P.width*P.topLength*(P.topLength/DyadicLineGrid.scale k)^2 := by
  classical
  have hwidth := P.width_pos
  have hlen (j : Fin N) : P.length j≤DyadicLineGrid.scale k :=
    (div_le_self P.topLength_pos.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))).trans hlarge
  have hrow (j : Fin N) :
      (∑ l : P.labels j, ∑ u : Item j l, P.shortKernel k m ⟨j,l,u⟩) ≤
        144*(4*Real.pi)^2*B*(P.length j/DyadicLineGrid.scale k)^2 := by
    calc
      _ ≤ ∑ _l : P.labels j, 144*(4*Real.pi)^2*(P.length j/DyadicLineGrid.scale k)^2 :=
        Finset.sum_le_sum (fun l _ => P.label_short_kernel_decay_sum y k m hallowed hcenter j l (hlen j))
      _ = (P.labels j).card*(144*(4*Real.pi)^2*(P.length j/DyadicLineGrid.scale k)^2) := by simp
      _ ≤ (B:ℝ)*(144*(4*Real.pi)^2*(P.length j/DyadicLineGrid.scale k)^2) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard j) (by positivity)
      _ = _ := by ring
  calc
    _ = ∑ j : Fin N, P.length j*P.width*(∑ l : P.labels j, ∑ u : Item j l, P.shortKernel k m ⟨j,l,u⟩) := by
      simp only [Fintype.sum_sigma,Finset.mul_sum]
    _ ≤ ∑ j : Fin N, (144*(4*Real.pi)^2*B*P.width)*(P.length j*(P.length j/DyadicLineGrid.scale k)^2) := by
      apply Finset.sum_le_sum
      intro j _
      have h := mul_le_mul_of_nonneg_left (hrow j) (mul_nonneg (P.length_pos j).le P.width_pos.le)
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      ring
    _ = (144*(4*Real.pi)^2*B*P.width)*∑ j : Fin N, P.length j*(P.length j/DyadicLineGrid.scale k)^2 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (144*(4*Real.pi)^2*B*P.width)*(2*P.topLength*(P.topLength/DyadicLineGrid.scale k)^2) :=
      mul_le_mul_of_nonneg_left (fin_dyadic_decay_sum N P.topLength (DyadicLineGrid.scale k) P.topLength_pos (scale_pos k))
        (by positivity)
    _ = _ := by ring

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWhitneyGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Glue stripwise estimates over the actual countable Whitney partition.
Finite-subfamily bounds imply integrability and the same global bound. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid
variable {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)

variable (hne : tiles.Nonempty) (hpos : ∀ i∈tiles, 0<ell i)

theorem indexAt_mem (z : ℝ) :
    z∈cell 0 (indexAt tiles x ell hne hpos z).val.1 (indexAt tiles x ell hne hpos z).val.2 :=
  Classical.choose_spec (exists_cellIndex tiles x ell hne hpos z)

theorem indexAt_eq_of_mem (i : CellIndex tiles x ell) {z : ℝ}
    (hz : z∈cell 0 i.val.1 i.val.2) : indexAt tiles x ell hne hpos z=i := by
  apply Subtype.ext
  by_contra hne'
  exact Set.disjoint_left.mp
    (whitney_disjoint tiles x ell (indexAt tiles x ell hne hpos z).property i.property hne')
    (indexAt_mem tiles x ell hne hpos z) hz

theorem strip_measurable {E : Set (ℝ×ℝ)} (hE : MeasurableSet E) (i : CellIndex tiles x ell) :
    MeasurableSet (strip tiles x ell E i) :=
  hE.inter ((cell_measurable 0 i.val.1 i.val.2).preimage measurable_fst)

theorem strip_disjoint (E : Set (ℝ×ℝ)) :
    Pairwise (fun i j : CellIndex tiles x ell => Disjoint (strip tiles x ell E i) (strip tiles x ell E j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  have hne' : i.val≠j.val := fun h => hij (Subtype.ext h)
  exact Set.disjoint_left.mp (whitney_disjoint tiles x ell i.property j.property hne') hzi.2 hzj.2

include hne hpos in
theorem strip_iUnion (E : Set (ℝ×ℝ)) : ⋃ i : CellIndex tiles x ell, strip tiles x ell E i = E := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact hi.1
  · intro z hz
    exact mem_iUnion.mpr ⟨indexAt tiles x ell hne hpos z.1,hz,indexAt_mem tiles x ell hne hpos z.1⟩

variable {V : Type*}

theorem paste_eq (F : CellIndex tiles x ell → ℝ×ℝ → V)
    (i : CellIndex tiles x ell) {z : ℝ×ℝ} {E : Set (ℝ×ℝ)} (hz : z∈strip tiles x ell E i) :
    paste tiles x ell hne hpos F z=F i z := by
  unfold paste
  rw [indexAt_eq_of_mem tiles x ell hne hpos i hz.2]

variable [NormedAddCommGroup V]

/-- Uniform bounds for finite collections of local norm integrals give
integrability and the identical estimate on the full Whitney partition. -/
theorem paste_integrable_bound (E : Set (ℝ×ℝ)) (hE : MeasurableSet E)
    (F : CellIndex tiles x ell → ℝ×ℝ → V)
    (hF : ∀ i, IntegrableOn (F i) (strip tiles x ell E i) (volume.prod volume))
    (C : ℝ) (hbound : ∀ S : Finset (CellIndex tiles x ell),
      (∑ i∈S, ∫ z in strip tiles x ell E i, ‖F i z‖ ∂volume.prod volume) ≤ C) :
    IntegrableOn (paste tiles x ell hne hpos F) E (volume.prod volume) ∧
    (∫ z in E, ‖paste tiles x ell hne hpos F z‖ ∂volume.prod volume) ≤ C := by
  let G := paste tiles x ell hne hpos F
  have heq (i : CellIndex tiles x ell) (z : ℝ×ℝ) (hz : z∈strip tiles x ell E i) : G z=F i z :=
    paste_eq tiles x ell hne hpos F i hz
  have hlocal (i : CellIndex tiles x ell) : IntegrableOn G (strip tiles x ell E i) (volume.prod volume) := by
    exact (hF i).congr_fun (fun z hz => (heq i z hz).symm) (strip_measurable tiles x ell hE i)
  have hint (i : CellIndex tiles x ell) :
      (∫ z in strip tiles x ell E i, ‖G z‖ ∂volume.prod volume) =
      (∫ z in strip tiles x ell E i, ‖F i z‖ ∂volume.prod volume) :=
    setIntegral_congr_fun (strip_measurable tiles x ell hE i) (fun z hz => congrArg norm (heq i z hz))
  have hsum : Summable (fun i : CellIndex tiles x ell =>
      ∫ z in strip tiles x ell E i, ‖G z‖ ∂volume.prod volume) := by
    apply summable_of_sum_le (fun i => integral_nonneg (fun z => norm_nonneg (G z)))
    intro S
    simpa only [hint] using hbound S
  have hglobal := integrableOn_iUnion_of_summable_integral_norm hlocal hsum
  rw [strip_iUnion tiles x ell hne hpos E] at hglobal
  refine ⟨hglobal,?_⟩
  have hglobalnorm : IntegrableOn (fun z => ‖G z‖) E (volume.prod volume) := hglobal.norm
  have hpartition := integral_iUnion (μ:=volume.prod volume)
    (f:=fun z => ‖G z‖) (strip_measurable tiles x ell hE) (strip_disjoint tiles x ell E)
    (by simpa only [strip_iUnion tiles x ell hne hpos E] using hglobalnorm)
  rw [strip_iUnion tiles x ell hne hpos E] at hpartition
  rw [hpartition]
  apply Real.tsum_le_of_sum_le (fun i => integral_nonneg (fun z => norm_nonneg (G z)))
  intro S
  simpa only [hint] using hbound S

end LipschitzHilbert.SourceWhitney

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLongCellMask
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual parent-witness density test supplies the common mask and
mass bounds on the disjoint cells used in long-tree integration. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem long_cell_scale_le_top (i : P.DensityWhitneyCell) (hi : P.HasLongPacket i) :
    DyadicLineGrid.scale i.val.1≤P.topLength := by
  obtain ⟨q,hq⟩ := hi
  have hl : P.length q.1≤P.topLength :=
    div_le_self P.topLength_pos.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  linarith [DyadicLineGrid.scale_pos i.val.1]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeCellGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable gluing on the actual horizontal Whitney cells and
half-open transverse cells. A finite rectangle bound suffices. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid
variable {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
variable (hne : tiles.Nonempty) (hpos : ∀ i∈tiles, 0<ell i)

theorem productCell_measurable (b W : ℝ) (i : ProductCellIndex tiles x ell) :
    MeasurableSet (productCell tiles x ell b W i) := partitionCell_measurable b W _

theorem productCell_disjoint (b W : ℝ) (hW : 0<W) :
    Pairwise (fun i j : ProductCellIndex tiles x ell =>
      Disjoint (productCell tiles x ell b W i) (productCell tiles x ell b W j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  by_cases he : i.1=j.1
  · have hn : i.2≠j.2 := by
      intro hn
      exact hij (Prod.ext he hn)
    exact Set.disjoint_left.mp (transverseCell_disjoint b W hW hn) hzi.2 hzj.2
  · have hv : i.1.val≠j.1.val := fun h => he (Subtype.ext h)
    exact Set.disjoint_left.mp
      (whitney_disjoint tiles x ell i.1.property j.1.property hv) hzi.1 hzj.1

include hne hpos in
theorem productCell_iUnion (b W : ℝ) (hW : 0<W) :
    (⋃ i : ProductCellIndex tiles x ell, productCell tiles x ell b W i)=univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨i,hi⟩ := exists_cellIndex tiles x ell hne hpos z.1
  exact mem_iUnion.mpr ⟨(i,⌊(z.2-b)/W+1/2⌋),hi,mem_transverseCell_floor b W z.2 hW⟩

variable {V : Type*} [NormedAddCommGroup V]

/-- Any finite collection is dominated by its finite rectangle of
horizontal and transverse indices. -/
theorem product_finite_bound
    (F : ProductCellIndex tiles x ell → ℝ) (hF : ∀ i, 0≤F i) (C : ℝ)
    (hrect : ∀ (S : Finset (CellIndex tiles x ell)) (T : Finset ℤ),
      (∑ i∈S×ˢT, F i)≤C) (A : Finset (ProductCellIndex tiles x ell)) :
    (∑ i∈A, F i)≤C := by
  classical
  apply le_trans _ (hrect (A.image Prod.fst) (A.image Prod.snd))
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hi,Finset.mem_image_of_mem _ hi⟩
  · intro i _ _
    exact hF i

/-- Integrability of the pasted function follows from the proved local
integrals and their uniform finite-rectangle bound. -/
theorem product_paste_integrable_bound (b W : ℝ) (hW : 0<W)
    (F : CellIndex tiles x ell → ℝ×ℝ → V)
    (hF : ∀ i : ProductCellIndex tiles x ell,
      IntegrableOn (F i.1) (productCell tiles x ell b W i) (volume.prod volume))
    (C : ℝ) (hrect : ∀ (S : Finset (CellIndex tiles x ell)) (T : Finset ℤ),
      (∑ i∈S×ˢT, ∫ z in productCell tiles x ell b W i, ‖F i.1 z‖ ∂volume.prod volume)≤C) :
    Integrable (paste tiles x ell hne hpos F) (volume.prod volume) ∧
      (∫ z, ‖paste tiles x ell hne hpos F z‖ ∂volume.prod volume)≤C := by
  let G := paste tiles x ell hne hpos F
  have heq (i : ProductCellIndex tiles x ell) {z : ℝ×ℝ}
      (hz : z∈productCell tiles x ell b W i) : G z=F i.1 z := by
    dsimp [G,paste]
    rw [indexAt_eq_of_mem tiles x ell hne hpos i.1 hz.1]
  have hlocal (i : ProductCellIndex tiles x ell) :
      IntegrableOn G (productCell tiles x ell b W i) (volume.prod volume) :=
    (hF i).congr_fun (fun z hz => (heq i hz).symm) (productCell_measurable tiles x ell b W i)
  have hint (i : ProductCellIndex tiles x ell) :
      (∫ z in productCell tiles x ell b W i, ‖G z‖ ∂volume.prod volume)=
        ∫ z in productCell tiles x ell b W i, ‖F i.1 z‖ ∂volume.prod volume :=
    setIntegral_congr_fun (productCell_measurable tiles x ell b W i)
      (fun _ hz => congrArg norm (heq i hz))
  have hbound (A : Finset (ProductCellIndex tiles x ell)) :
      (∑ i∈A, ∫ z in productCell tiles x ell b W i, ‖G z‖ ∂volume.prod volume)≤C := by
    simpa only [hint] using product_finite_bound tiles x ell
      (fun i => ∫ z in productCell tiles x ell b W i, ‖F i.1 z‖ ∂volume.prod volume)
      (fun _ => integral_nonneg (fun _ => norm_nonneg _)) C hrect A
  have hs : Summable (fun i : ProductCellIndex tiles x ell =>
      ∫ z in productCell tiles x ell b W i, ‖G z‖ ∂volume.prod volume) :=
    summable_of_sum_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hbound
  have hi := integrableOn_iUnion_of_summable_integral_norm hlocal hs
  rw [productCell_iUnion tiles x ell hne hpos b W hW,integrableOn_univ] at hi
  refine ⟨hi,?_⟩
  have hpart := integral_iUnion (μ:=volume.prod volume) (f:=fun z => ‖G z‖)
    (productCell_measurable tiles x ell b W) (productCell_disjoint tiles x ell b W hW)
    hi.norm.integrableOn
  rw [productCell_iUnion tiles x ell hne hpos b W hW,setIntegral_univ] at hpart
  rw [hpart]
  exact Real.tsum_le_of_sum_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hbound

end LipschitzHilbert.SourceWhitney

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWhitneySummation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summation of the local short-tree bounds over the Whitney partition:
total small-cell length and the large-cell geometric tail. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid

/-- Summing the far-strip decay over the large Whitney intervals costs
only an absolute factor, including all possible integer scales. -/
theorem large_whitney_ratio_sum {ι : Type*} (tiles : Finset ι)
    (x ell : ι → ℝ) {c L : ℝ} (hL : 0<L)
    (hcenters : ∀ i∈tiles, |x i-c|≤L/2) (S : Finset (ℤ×ℤ))
    (hW : ∀ p∈S, Whitney tiles x ell p.1 p.2)
    (hlarge : ∀ p∈S, L ≤ scale p.1) :
    (∑ p∈S, (L/scale p.1)^2) ≤ 18 := by
  classical
  let K := S.image Prod.fst
  have hmaps : ∀ p∈S, p.1∈K := fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hK (k) (hk : k∈K) : L ≤ scale k := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hk
    exact hlarge p hp
  have hrow (k) (hk : k∈K) :
      (∑ p∈S.filter (fun p => p.1=k), (L/scale p.1)^2) ≤ 9*(L/scale k)^2 := by
    let T := S.filter (fun p => p.1=k)
    have htW : ∀ p∈T, Whitney tiles x ell p.1 p.2 :=
      fun p hp => hW p (Finset.mem_filter.mp hp).1
    have htlevel : ∀ p∈T, p.1=k := fun _ hp => (Finset.mem_filter.mp hp).2
    have hsum : (∑ p∈T, scale p.1) = (T.card:ℝ)*scale k := by
      calc
        _ = ∑ _p∈T, scale k := Finset.sum_congr rfl (fun p hp => by rw [htlevel p hp])
        _ = _ := by simp
    have hbudget := finite_length_budget tiles x ell hL.le (scale_pos k).le hcenters T htW
      (fun p hp => le_of_eq (congrArg scale (htlevel p hp)))
    rw [hsum] at hbudget
    have hcard : (T.card:ℝ)≤9 := (mul_le_mul_iff_left₀ (scale_pos k)).mp (by
      nlinarith only [hbudget,hK k hk])
    calc
      _ = (T.card:ℝ)*(L/scale k)^2 := by
        calc
          _ = ∑ _p∈T, (L/scale k)^2 :=
            Finset.sum_congr rfl (fun p hp => by rw [htlevel p hp])
          _ = _ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
  calc
    _ = ∑ k∈K, ∑ p∈S.filter (fun p => p.1=k), (L/scale p.1)^2 :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ k∈K, 9*(L/scale k)^2 := Finset.sum_le_sum hrow
    _ = 9*∑ k∈K, (L/scale k)^2 := (Finset.mul_sum _ _ _).symm
    _ ≤ 9*2 := mul_le_mul_of_nonneg_left (finite_large_scale_square_sum L hL K hK) (by norm_num)
    _ = _ := by norm_num

/-- The small-cell contribution and large-cell tail together have total
weight at most `27L`. -/
theorem short_whitney_weight_sum {ι : Type*} (tiles : Finset ι)
    (x ell : ι → ℝ) {c L : ℝ} (hL : 0<L)
    (hcenters : ∀ i∈tiles, |x i-c|≤L/2) (S : Finset (ℤ×ℤ))
    (hW : ∀ p∈S, Whitney tiles x ell p.1 p.2) :
    (∑ p∈S, shortWhitneyWeight L (scale p.1)) ≤ 27*L := by
  classical
  let small := S.filter (fun p => scale p.1≤L)
  let large := S.filter (fun p => ¬scale p.1≤L)
  have hs := small_length_budget tiles x ell hL.le hcenters small
    (fun p hp => hW p (Finset.mem_filter.mp hp).1)
    (fun _ hp => (Finset.mem_filter.mp hp).2)
  have hl := large_whitney_ratio_sum tiles x ell hL hcenters large
    (fun p hp => hW p (Finset.mem_filter.mp hp).1)
    (fun p hp => le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hp).2))
  have heq : (∑ p∈S, shortWhitneyWeight L (scale p.1)) =
      (∑ p∈small, scale p.1)+L*(∑ p∈large, (L/scale p.1)^2) := by
    simp only [shortWhitneyWeight,Finset.sum_ite,small,large,Finset.mul_sum]
  rw [heq]
  nlinarith only [hs,hl,hL]

/-- Local strip estimates with the manuscript's two decay regimes sum to
the required top-area bound. -/
theorem sum_short_strip_bounds {ι : Type*} (tiles : Finset ι)
    (x ell : ι → ℝ) {c L W A : ℝ} (hL : 0<L) (hW : 0≤W) (hA : 0≤A)
    (hcenters : ∀ i∈tiles, |x i-c|≤L/2) (S : Finset (ℤ×ℤ))
    (hWhitney : ∀ p∈S, Whitney tiles x ell p.1 p.2) (mass : ℤ×ℤ → ℝ)
    (hsmall : ∀ p∈S, scale p.1≤L → mass p≤A*W*scale p.1)
    (hlarge : ∀ p∈S, L < scale p.1 → mass p≤A*W*L*(L/scale p.1)^2) :
    (∑ p∈S, mass p) ≤ 27*A*L*W := by
  have hpoint (p) (hp : p∈S) : mass p≤(A*W)*shortWhitneyWeight L (scale p.1) := by
    by_cases h : scale p.1≤L
    · simpa only [shortWhitneyWeight,ite_eq_left h] using hsmall p hp h
    · have hb := hlarge p hp (lt_of_not_ge h)
      simpa only [shortWhitneyWeight,ite_eq_right h,mul_assoc] using hb
  calc
    _ ≤ ∑ p∈S, (A*W)*shortWhitneyWeight L (scale p.1) := Finset.sum_le_sum hpoint
    _ = (A*W)*∑ p∈S, shortWhitneyWeight L (scale p.1) := (Finset.mul_sum _ _ _).symm
    _ ≤ (A*W)*(27*L) := mul_le_mul_of_nonneg_left
      (short_whitney_weight_sum tiles x ell hL hcenters S hWhitney) (mul_nonneg hA hW)
    _ = _ := by ring

end LipschitzHilbert.SourceWhitney

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShortTreeIntegral
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete finite-strip short-tree estimate for the original packet
integrals. All density tests, lattice sums and Whitney budgets are actual. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney DyadicLineGrid
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- Sum of absolute short-packet integrals over any finite family of
actual Whitney strips is bounded by size times density times top area.
The explicit constant depends only on the fixed packet seminorm, label
multiplicity, selector bound, and short/long splitting constant. -/
theorem short_tree_finite_strip_bound (P : SourceLabeledLattice N κ Label Item)
    (B : ℕ) (hcard : ∀ j, (P.labels j).card≤B)
    (oldSlope : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (w tau : ℝ)
    (htime : P.topLength≤tau)
    (hslope : ∀ j l, oldSlope+P.rowSlope j l ∈
      scaledAngularCell (w/P.topLength) grid j.val (cell j l))
    (horder : 205≤2*P.order) (M sigma eta : ℝ)
    (hM : 0≤M) (hsigma : 0 ≤ sigma) (heta : 0≤eta)
    (coefficient : P.PacketIndex → EuclideanSpace ℂ κ)
    (hcoefficient : ∀ q, ‖coefficient q‖ ≤ sigma)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hselector : ∀ j l a, Measurable (selector j l a))
    (hbound : ∀ j l a s, ‖selector j l a s‖≤M)
    (hsupport : ∀ j l a s, selector j l a s≠0 →
      s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l))
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (E : Set (ℝ×ℝ)) (hE : MeasurableSet E)
    (hdensity : ∀ q, P.ordinaryDensity oldSlope cell grid w tau E u q≤eta)
    (x y CW : ℝ) (hCW : 1≤CW)
    (hX : ∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-x|≤P.topLength/2)
    (hY : ∀ j l v, |P.actualZ j l v-y|≤P.width)
    (S : Finset (ℤ×ℤ))
    (hWhitney : ∀ p∈S, Whitney (Finset.univ : Finset P.PacketIndex)
      (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1) p.1 p.2) :
    (∑ p∈S, ∑ q : P.PacketIndex, if P.length q.1≤CW*DyadicLineGrid.scale p.1 then
      (∫ z in E∩Prod.fst ⁻¹' DyadicLineGrid.cell 0 p.1 p.2,
        ‖ordinaryPacketValue P oldSlope coefficient selector u q z‖ ∂volume.prod volume) else 0) ≤
      (27*288*(4*Real.pi)^2*(B:ℝ)*CW*(3:ℝ)^203*P.profileBound*M)*
        sigma*eta*P.topLength*P.width := by
  classical
  have hwidth := P.width_pos
  have hprofile := P.profileBound_pos
  have htop := P.topLength_pos
  let C := (3:ℝ)^203*P.profileBound*M*sigma*eta
  let A := C*(288*(4*Real.pi)^2*B)*CW
  let mass := fun p : ℤ×ℤ => ∑ q : P.PacketIndex,
    if P.length q.1≤CW*DyadicLineGrid.scale p.1 then
      (∫ z in E∩Prod.fst ⁻¹' DyadicLineGrid.cell 0 p.1 p.2,
        ‖ordinaryPacketValue P oldSlope coefficient selector u q z‖ ∂volume.prod volume) else 0
  have hC : 0≤C := by dsimp [C]; positivity
  have hCW0 : 0≤CW := zero_le_one.trans hCW
  have hnum : 0≤288*(4*Real.pi)^2*(B:ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Nat.cast_nonneg _)
  have hA : 0≤A := mul_nonneg (mul_nonneg hC hnum) hCW0
  have hlength (j : Fin N) : P.length j≤P.topLength :=
    div_le_self P.topLength_pos.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have hterm (p : ℤ×ℤ) (q : P.PacketIndex) :
      (∫ z in E∩Prod.fst ⁻¹' DyadicLineGrid.cell 0 p.1 p.2,
        ‖ordinaryPacketValue P oldSlope coefficient selector u q z‖ ∂volume.prod volume) ≤
      C*(P.length q.1*P.width*P.shortKernel p.1 p.2 q) := by
    have h := P.own_packet_whitney_density_bound oldSlope cell grid w tau q
      ((hlength q.1).trans htime) (hslope q.1 q.2.1) horder M sigma eta hM hsigma
      (coefficient q) (hcoefficient q) (selector q.1 q.2.1)
      (hselector q.1 q.2.1) (hbound q.1 q.2.1) (hsupport q.1 q.2.1)
      u hu E hE (hdensity q) p.1 p.2
    exact h.2.trans_eq (by dsimp [C,shortKernel]; ring)
  have hmass (p : ℤ×ℤ) : mass p≤C*(∑ q : P.PacketIndex,
      if P.length q.1≤CW*DyadicLineGrid.scale p.1 then P.length q.1*P.width*P.shortKernel p.1 p.2 q else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q _
    by_cases h : P.length q.1≤CW*DyadicLineGrid.scale p.1
    · simpa only [ite_eq_left h] using hterm p q
    · simp only [ite_eq_right h,mul_zero,le_refl]
  have hsmall (p : ℤ×ℤ) (hp : p∈S) (_hsize : DyadicLineGrid.scale p.1≤P.topLength) :
      mass p≤A*P.width*DyadicLineGrid.scale p.1 := by
    have h := P.packet_short_mass_sum B hcard y (CW*DyadicLineGrid.scale p.1)
      (mul_nonneg hCW0 (scale_pos p.1).le)
      p.1 p.2 (hWhitney p hp).1 hY
    exact (hmass p).trans ((mul_le_mul_of_nonneg_left h hC).trans_eq (by dsimp [A]; ring))
  have hlarge (p : ℤ×ℤ) (hp : p∈S) (hsize : P.topLength<DyadicLineGrid.scale p.1) :
      mass p≤A*P.width*P.topLength*(P.topLength/DyadicLineGrid.scale p.1)^2 := by
    have hdrop : (∑ q : P.PacketIndex,
        if P.length q.1≤CW*DyadicLineGrid.scale p.1 then P.length q.1*P.width*P.shortKernel p.1 p.2 q else 0) ≤
        ∑ q : P.PacketIndex, P.length q.1*P.width*P.shortKernel p.1 p.2 q := by
      apply Finset.sum_le_sum
      intro q _
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (mul_nonneg (P.length_pos q.1).le P.width_pos.le)
          (by dsimp [shortKernel]; positivity)
    have ht := P.packet_short_mass_decay_sum B hcard y p.1 p.2 (hWhitney p hp).1 hY hsize.le
    have hbase : mass p≤C*(288*(4*Real.pi)^2*B*P.width*P.topLength*(P.topLength/DyadicLineGrid.scale p.1)^2) :=
      (hmass p).trans (mul_le_mul_of_nonneg_left (hdrop.trans ht) hC)
    have hcw := mul_le_mul_of_nonneg_left hCW
      (mul_nonneg hC (mul_nonneg (mul_nonneg (mul_nonneg hnum hwidth.le) htop.le) (sq_nonneg (P.topLength/DyadicLineGrid.scale p.1))))
    exact hbase.trans (by simpa only [mul_one] using hcw) |>.trans_eq (by dsimp [A]; ring)
  have h := sum_short_strip_bounds (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)
    P.topLength_pos P.width_pos.le hA (fun q _ => hX q) S hWhitney mass hsmall hlarge
  exact h.trans_eq (by dsimp [A,C]; ring)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShortTreeGlobal
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original short-tree sum on the full Whitney partition, with
integrability and a uniform size-density-area bound. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney DyadicLineGrid
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem ordinaryPacketValue_measurable (P : SourceLabeledLattice N κ Label Item)
    (oldSlope : ℝ) (coefficient : P.PacketIndex → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hselector : ∀ j l a, Measurable (selector j l a))
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (q : P.PacketIndex) :
    Measurable (P.ordinaryPacketValue oldSlope coefficient selector u q) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_iff.mpr
  intro a
  exact (measurable_const.mul ((hselector q.1 q.2.1 a).comp hu)).mul
    (P.physicalPacket oldSlope q.1 q.2.1 q.2.2 a).continuous.measurable

private theorem finite_cutoff_integral {Q V : Type*} [Fintype Q] [NormedAddCommGroup V]
    (E : Set (ℝ×ℝ)) (F : Q → ℝ×ℝ → V) (keep : Q → Prop) [DecidablePred keep]
    (hF : ∀ q, IntegrableOn (F q) E (volume.prod volume)) :
    IntegrableOn (fun z => ∑ q, if keep q then F q z else 0) E (volume.prod volume) ∧
    (∫ z in E, ‖∑ q, if keep q then F q z else 0‖ ∂volume.prod volume) ≤
      ∑ q, if keep q then (∫ z in E, ‖F q z‖ ∂volume.prod volume) else 0 := by
  have hi (q : Q) : IntegrableOn (fun z => if keep q then F q z else 0) E (volume.prod volume) := by
    by_cases h : keep q
    · simpa only [ite_eq_left h] using hF q
    · simp only [ite_eq_right h]
      exact integrableOn_zero
  have hs := integrable_finsetSum Finset.univ (fun q _ => hi q)
  refine ⟨hs,?_⟩
  calc
    _ ≤ ∫ z in E, ∑ q, ‖if keep q then F q z else 0‖ ∂volume.prod volume :=
      integral_mono hs.norm (integrable_finsetSum Finset.univ (fun q _ => (hi q).norm))
        (fun z => norm_sum_le _ _)
    _ = ∑ q, ∫ z in E, ‖if keep q then F q z else 0‖ ∂volume.prod volume :=
      integral_finsetSum _ (fun q _ => (hi q).norm)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      by_cases h : keep q <;> simp only [h,ite_true, if_true,ite_false, if_false,norm_zero,integral_zero]

/-- The original short-tree sum is integrable on the full Whitney partition. -/
theorem short_tree_integrable_bound (P : SourceLabeledLattice N κ Label Item)
    (hne : Nonempty P.PacketIndex) (B : ℕ) (hcard : ∀ j, (P.labels j).card≤B)
    (oldSlope : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (w tau : ℝ)
    (htime : P.topLength≤tau)
    (hslope : ∀ j l, oldSlope+P.rowSlope j l ∈
      scaledAngularCell (w/P.topLength) grid j.val (cell j l))
    (horder : 205≤2*P.order) (M sigma eta : ℝ)
    (hM : 0≤M) (hsigma : 0 ≤ sigma) (heta : 0≤eta)
    (coefficient : P.PacketIndex → EuclideanSpace ℂ κ)
    (hcoefficient : ∀ q, ‖coefficient q‖ ≤ sigma)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hselector : ∀ j l a, Measurable (selector j l a))
    (hbound : ∀ j l a s, ‖selector j l a s‖≤M)
    (hsupport : ∀ j l a s, selector j l a s≠0 →
      s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l))
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (E : Set (ℝ×ℝ)) (hE : MeasurableSet E)
    (hdensity : ∀ q, P.ordinaryDensity oldSlope cell grid w tau E u q≤eta)
    (x y CW : ℝ) (hCW : 1≤CW)
    (hX : ∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-x|≤P.topLength/2)
    (hY : ∀ j l v, |P.actualZ j l v-y|≤P.width)
 :
    IntegrableOn (P.shortTreeValue hne oldSlope CW coefficient selector u) E (volume.prod volume) ∧
    (∫ z in E, ‖P.shortTreeValue hne oldSlope CW coefficient selector u z‖ ∂volume.prod volume) ≤
      (27*288*(4*Real.pi)^2*(B:ℝ)*CW*(3:ℝ)^203*P.profileBound*M)*
        sigma*eta*P.topLength*P.width := by
  classical
  let tiles := (Finset.univ : Finset P.PacketIndex)
  let X := fun q : P.PacketIndex => P.actualX q.1 q.2.1 q.2.2
  let ell := fun q : P.PacketIndex => P.length q.1
  let F := P.shortLocalValue oldSlope CW coefficient selector u
  have hlen (j : Fin N) : P.length j≤tau :=
    (div_le_self P.topLength_pos.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))).trans htime
  have hpiece (i : P.WhitneyCell) (q : P.PacketIndex) :
      IntegrableOn (P.ordinaryPacketValue oldSlope coefficient selector u q)
        (strip tiles X ell E i) (volume.prod volume) := by
    have h := P.own_packet_whitney_density_bound oldSlope cell grid w tau q
      (hlen q.1) (hslope q.1 q.2.1) horder M sigma eta hM hsigma
      (coefficient q) (hcoefficient q) (selector q.1 q.2.1)
      (hselector q.1 q.2.1) (hbound q.1 q.2.1) (hsupport q.1 q.2.1)
      u hu E hE (hdensity q) i.val.1 i.val.2
    exact (integrable_norm_iff
      (P.ordinaryPacketValue_measurable oldSlope coefficient selector hselector u hu q).aestronglyMeasurable).mp h.1
  have hlocal (i : P.WhitneyCell) :
      IntegrableOn (F i) (strip tiles X ell E i) (volume.prod volume) ∧
      (∫ z in strip tiles X ell E i, ‖F i z‖ ∂volume.prod volume) ≤
        ∑ q : P.PacketIndex, if P.length q.1≤CW*DyadicLineGrid.scale i.val.1 then
          (∫ z in strip tiles X ell E i,
            ‖P.ordinaryPacketValue oldSlope coefficient selector u q z‖ ∂volume.prod volume) else 0 :=
    finite_cutoff_integral (strip tiles X ell E i)
      (P.ordinaryPacketValue oldSlope coefficient selector u)
      (fun q => P.length q.1≤CW*DyadicLineGrid.scale i.val.1) (hpiece i)
  apply paste_integrable_bound tiles X ell (P.packet_univ_nonempty hne)
    (fun q _ => P.length_pos q.1) E hE F (fun i => (hlocal i).1)
  intro S
  have hs := P.short_tree_finite_strip_bound B hcard oldSlope cell grid w tau htime hslope
    horder M sigma eta hM hsigma heta coefficient hcoefficient selector hselector hbound hsupport
    u hu E hE hdensity x y CW hCW hX hY (S.image Subtype.val)
    (by intro p hp; obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp; exact i.property)
  rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)] at hs
  apply le_trans (Finset.sum_le_sum (fun i _ => (hlocal i).2))
  exact hs

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeErrorIntegral
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating the ordinary-tree error over the actual density masks.
Order 53 leaves at least six decay powers after the density loss 203. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
open SourceWhitney

private theorem error_cell_integral {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (b W D eta : ℝ) (hW : 0<W) (hD : 0≤D)
    (p : (ℤ×ℤ)×ℤ) (A : Set (ℝ×ℝ)) (hA : MeasurableSet A)
    (F : ℝ×ℝ → V) (hF : AEStronglyMeasurable F (volume.prod volume))
    (hbound : ∀ z, polynomialWeight b (2*W) 53 z.2^2*‖F z‖≤D)
    (hmass : (volume.prod volume).real (partitionCell b W p∩A)≤
      32*(2:ℝ)^203*eta*(1+|(p.2:ℝ)|)^203*DyadicLineGrid.scale p.1.1*W) :
    IntegrableOn (A.indicator F) (partitionCell b W p) (volume.prod volume) ∧
    (∫ z in partitionCell b W p, ‖A.indicator F z‖ ∂volume.prod volume)≤
      (32^106*D*(32*(2:ℝ)^203*eta))*
        ((DyadicLineGrid.scale p.1.1*W)/(1+|(p.2:ℝ)|)^6) := by
  let w := 1+|(p.2:ℝ)|
  have hw1 : 1≤w := by dsimp [w]; linarith [abs_nonneg (p.2:ℝ)]
  have hw : 0<w := lt_of_lt_of_le (by norm_num) hw1
  have hpt (z : ℝ×ℝ) (hz : z∈partitionCell b W p) :
      ‖F z‖≤32^106*D/w^209 := by
    have hp := transverse_cell_polynomial_weight b W (p.2:ℝ) z.2 53 hW
      (transverseCell_bound b W p.2 hz.2)
    have hs := pow_le_pow_left₀ (by positivity : 0≤(1+|(p.2:ℝ)|)^(2*53)) hp 2
    simp only [mul_pow,←pow_mul] at hs
    change w^212≤32^106*polynomialWeight b (2*W) 53 z.2^2 at hs
    have hl : w^209≤32^106*polynomialWeight b (2*W) 53 z.2^2 :=
      (pow_le_pow_right₀ hw1 (by omega : 209≤212)).trans hs
    apply (le_div_iff₀ (pow_pos hw 209)).mpr
    calc
      _ ≤ (32^106*polynomialWeight b (2*W) 53 z.2^2)*‖F z‖ := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hl (norm_nonneg (F z))
      _ = 32^106*(polynomialWeight b (2*W) 53 z.2^2*‖F z‖) := by rw [mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbound z) (pow_nonneg (by norm_num) 106)
  have h := masked_cell_norm_integral (volume.prod volume) (partitionCell b W p) A
    (partitionCell_measurable b W p) hA (partitionCell_finite b W p) F hF
    (32^106*D/w^209) hpt
  refine ⟨h.1,h.2.trans ?_⟩
  apply (mul_le_mul_of_nonneg_left hmass
    (div_nonneg (mul_nonneg (pow_nonneg (by norm_num) 106) hD) (pow_nonneg hw.le 209))).trans_eq
  change (32^106*D/w^209)*(32*2^203*eta*w^203*DyadicLineGrid.scale p.1.1*W)=_
  have he : w^209=w^203*w^6 := by rw [←pow_add]
  rw [he]
  field_simp
  ring

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- A pointwise transverse error estimate integrates with the actual
cell masks at a cost independent of the number of scales and cells. -/
theorem tree_error_integrable_bound (hne : Nonempty P.PacketIndex)
    (F : P.DensityWhitneyCell → ℝ×ℝ → EuclideanSpace ℂ κ)
    (hF : ∀ i, AEStronglyMeasurable (F i) (volume.prod volume))
    (a b D eta : ℝ) (hD : 0≤D) (heta : 0≤eta)
    (hcenter : ∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2)
    (hbound : ∀ i z, polynomialWeight b (2*P.width) 53 z.2^2*‖F i z‖≤D)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (Omega : P.DensityWhitneyCell → Set ℝ) (hOmega : ∀ i, MeasurableSet (Omega i))
    (hEmpty : ∀ i, ¬P.HasLongPacket i → Omega i=∅)
    (hmass : ∀ i n, (volume.prod volume).real
      (partitionCell b P.width (i.val,n)∩(E∩u ⁻¹' Omega i))≤
      32*(2:ℝ)^203*eta*(1+|(n:ℝ)|)^203*DyadicLineGrid.scale i.val.1*P.width) :
    let G := paste (Finset.univ : Finset P.PacketIndex)
      (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)
      (by obtain ⟨q⟩ := hne; exact ⟨q,Finset.mem_univ q⟩)
      (fun q _ => P.length_pos q.1)
      (fun i => (E∩u ⁻¹' Omega i).indicator (F i))
    Integrable G (volume.prod volume) ∧ (∫ z, ‖G z‖ ∂volume.prod volume)≤
      (32^106*D*(32*(2:ℝ)^203*eta))*(9*P.topLength*P.width*transverseTailConstant) := by
  classical
  let mask := fun i => E∩u ⁻¹' Omega i
  let J := fun (i : P.DensityWhitneyCell) (n : ℤ) =>
    ∫ z in partitionCell b P.width (i.val,n), ‖(mask i).indicator (F i) z‖ ∂volume.prod volume
  let C := 32^106*D*(32*(2:ℝ)^203*eta)
  have hC : 0≤C := mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) 106) hD)
    (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) 203)) heta)
  have hlocal (i : P.DensityWhitneyCell) (n : ℤ) := error_cell_integral b P.width D eta
    P.width_pos hD (i.val,n) (mask i) (hE.inter ((hOmega i).preimage hu))
    (F i) (hF i) (hbound i) (hmass i n)
  apply product_paste_integrable_bound (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)
    (by obtain ⟨q⟩ := hne; exact ⟨q,Finset.mem_univ q⟩)
    (fun q _ => P.length_pos q.1) b P.width P.width_pos
    (fun i => (mask i).indicator (F i)) (fun i => (hlocal i.1 i.2).1)
  intro S T
  let SL := S.filter P.HasLongPacket
  have hzero (i : P.DensityWhitneyCell) (hi : ¬P.HasLongPacket i) (n : ℤ) : J i n=0 := by
    dsimp only [J,mask]
    rw [hEmpty i hi,preimage_empty,inter_empty]
    simp only [indicator_empty,norm_zero,integral_zero]
  have heq : (∑ p∈S×ˢT, J p.1 p.2)=(∑ p∈SL×ˢT, J p.1 p.2) := by
    simp only [Finset.sum_product,SL,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : P.HasLongPacket i
    · simp only [hi,ite_true, if_true]
    · simp only [hi,ite_false, if_false]
      exact Finset.sum_eq_zero (fun n _ => hzero i hi n)
  change (∑ p∈S×ˢT, J p.1 p.2)≤_
  rw [heq]
  have hbudget := finite_whitney_transverse_budget (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)
    a P.topLength P.width P.topLength_pos.le P.width_pos.le (fun q _ => hcenter q)
    (SL.image Subtype.val) T
    (by intro p hp; obtain ⟨i,_hi,rfl⟩ := Finset.mem_image.mp hp; exact i.property)
    (by intro p hp; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
        exact P.long_cell_scale_le_top i (Finset.mem_filter.mp hi).2)
  rw [Finset.sum_product,Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)] at hbudget
  calc
    _ ≤ ∑ p∈SL×ˢT, C*((DyadicLineGrid.scale p.1.val.1*P.width)/(1+|(p.2:ℝ)|)^6) :=
      Finset.sum_le_sum (fun p _ => (hlocal p.1 p.2).2)
    _ = C*∑ i∈SL, ∑ n∈T, (DyadicLineGrid.scale i.val.1*P.width)/(1+|(n:ℝ)|)^6 := by
      rw [Finset.sum_product,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hbudget hC

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeSelectorError
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary-tree freezing error is a summable dyadic error, with
its original angular indicator retained on both terms. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem rawSelectorTreeValue_sub (i : Fin 3)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (beta gamma : ∀ j, P.labels j → κ → ℂ) (y x : ℝ) :
    P.rawSelectorTreeValue i c beta y x - P.rawSelectorTreeValue i c gamma y x =
      P.rawSelectorTreeValue i c (fun j l k => beta j l k-gamma j l k) y x := by
  ext k
  simp only [rawSelectorTreeValue,WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_sub,
    Pi.sub_apply,Finset.sum_sub_distrib,mul_sub,sub_mul]

private theorem tree_raw_envelope (i : Fin 3) (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) (y x : ℝ) :
    ‖P.raw i j l u k y x‖ ≤ P.absoluteConstant *
      (lineEnvelope (P.length j*(P.snappedSite j l u).1) (P.length j) P.order x *
       lineEnvelope (P.width*(P.snappedSite j l u).2) P.width P.order y) := by
  have hs := snappedLatticeSite_envelope (P.originX j l) (P.originZ j l) (P.length j)
    P.width (P.rowSlope j l) x y (P.length_pos j) P.width_pos (P.site j l u) P.order P.order
  have hp : (3:ℝ)^P.order*3^P.order = 3^(2*P.order) := by
    rw [←pow_add]; congr 1; omega
  have hA : 0≤(2^P.order*P.profileBound)*P.ratioBound^2 := by
    have := P.profileBound_pos
    positivity
  have h := mul_le_mul_of_nonneg_left hs hA
  rw [hp] at h
  exact (P.raw_absolute_envelope i j l u k y x).trans (by
    simpa only [absoluteConstant,actualX,actualZ,snappedSite,mul_assoc] using h)

private theorem tree_transverse_overlap (q : ℕ) (horder : 1+2*q≤P.order)
    (b : ℝ) (hcenter : ∀ j l u, |P.actualZ j l u-b|≤P.width)
    (j : Fin N) (l : P.labels j) (y x : ℝ) :
    polynomialWeight b (2*P.width) q y^2 *
      (∑ u : Item j l,
        lineEnvelope (P.length j*(P.snappedSite j l u).1) (P.length j) P.order x *
        lineEnvelope (P.width*(P.snappedSite j l u).2) P.width P.order y) ≤
      16^q*(4*Real.pi)^2 := by
  have hY (u : Item j l) : |P.width*(P.snappedSite j l u).2-b|≤2*P.width := by
    have he := snappedLatticeSite_vertical (P.originX j l) (P.originZ j l) (P.length j)
      P.width (P.rowSlope j l) P.width_pos (P.site j l u)
    change |P.actualZ j l u-P.width*(P.snappedSite j l u).2|≤P.width at he
    calc
      _ ≤ |P.width*(P.snappedSite j l u).2-P.actualZ j l u|+|P.actualZ j l u-b| := abs_sub_le _ _ _
      _ ≤ P.width+P.width := add_le_add (by simpa only [abs_sub_comm] using he) (hcenter j l u)
      _ = _ := by ring
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ u : Item j l, 16^q *
        (lineEnvelope (P.length j*(P.snappedSite j l u).1) (P.length j) 1 x *
         lineEnvelope (P.width*(P.snappedSite j l u).2) P.width 1 y) := by
      apply Finset.sum_le_sum
      intro u _
      have hx := lineEnvelope_antitone (P.length j*(P.snappedSite j l u).1)
        (P.length j) x (by omega : 1≤P.order)
      have hy := (mul_le_mul_of_nonneg_left
        (lineEnvelope_antitone (P.width*(P.snappedSite j l u).2) P.width y horder)
        (sq_nonneg (polynomialWeight b (2*P.width) q y))).trans
        (polynomialWeight_sq_mul_envelope y (P.width*(P.snappedSite j l u).2)
          b P.width (2*P.width) q 1 P.width_pos (by linarith [P.width_pos])
          (by linarith [P.width_pos]) (hY u))
      calc
        _ = lineEnvelope (P.length j*(P.snappedSite j l u).1) (P.length j) P.order x *
            (polynomialWeight b (2*P.width) q y^2 *
             lineEnvelope (P.width*(P.snappedSite j l u).2) P.width P.order y) := by ring
        _ ≤ lineEnvelope (P.length j*(P.snappedSite j l u).1) (P.length j) 1 x *
            (16^q*lineEnvelope (P.width*(P.snappedSite j l u).2) P.width 1 y) :=
          mul_le_mul hx hy (mul_nonneg (sq_nonneg _) (lineEnvelope_nonneg _ _ _ _))
            (lineEnvelope_nonneg _ _ _ _)
        _ = _ := by ring
    _ = 16^q * ∑ u : Item j l,
        lineEnvelope (P.length j*(P.snappedSite j l u).1) (P.length j) 1 x *
        lineEnvelope (P.width*(P.snappedSite j l u).2) P.width 1 y := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by
      simpa only [zero_add] using injective_tile_lattice_overlap (P.snappedSite j l)
        (P.snappedSite_injective j l) 0 0 (P.length j) P.width x y
        (P.length_pos j).ne' P.width_pos.ne' (by decide : 1≤1) (by decide : 1≤1)) (by positivity)

/-- The source-angle error at a fixed point has summable dyadic size.
The multiplier hypotheses concern the original selectors, not the error. -/
theorem raw_tree_selector_error (q K B : ℕ) (horder : 1+2*q≤P.order)
    (hcard : ∀ j, (P.labels j).card≤B) (w b t radius Cb M Lip sigma : ℝ)
    (hw : 0<w) (hM : 0≤M) (hLip : 0≤Lip) (hsigma : 0 ≤ sigma)
    (hwide : 1 ≤ radius+Cb) (hK : radius+Cb≤(2:ℝ)^K)
    (hcenter : ∀ j l u, |P.actualZ j l u-b|≤P.width)
    (hslope : ∀ j l, |P.rowSlope j l|≤Cb*(w/P.length j))
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (hc : ∀ j l u, ‖c j l u‖ ≤ sigma)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hbound : ∀ j l k s, ‖selector j l k s‖≤M)
    (hsupport : ∀ j l k s, selector j l k s≠0 →
      |s-(t+P.rowSlope j l)| ≤ radius*(w/P.length j))
    (hnear : ∀ j l k s, |s-t|≤w/P.length j →
      ‖selector j l k s-selector j l k t‖≤Lip*(|s-t|/(w/P.length j)))
    (i : Fin 3) (s y x : ℝ) :
    polynomialWeight b (2*P.width) q y^2 *
      ‖P.rawSelectorTreeValue i c
        (fun j l k => multiplierError (selector j l k) t (w/P.length j) s) y x‖ ≤
      (B:ℝ)*P.absoluteConstant*sigma*(2*M+Lip)*16^q*(4*Real.pi)^2*((K+1:ℕ)+4) := by
  classical
  have hC := P.absoluteConstant_pos
  let e := fun j : Fin N => errorSourceProfile 1 (radius+Cb) (w/P.length j) |s-t|
  have he0 (j : Fin N) : 0≤e j := errorSourceProfile_nonneg _ _ _ _
    (div_pos hw (P.length_pos j)) (abs_nonneg _)
  have heSum : (∑ j, e j)≤(K+1:ℕ)+4 := by
    have hd (j : Fin N) : w/P.length j=(w/P.topLength)*(2:ℝ)^j.val := by
      dsimp only [length]
      field_simp [P.topLength_pos.ne']
    simp_rw [e,hd]
    simpa using sum_errorSourceProfile N K (w/P.topLength) 1 (radius+Cb) |s-t|
      (div_pos hw P.topLength_pos) (by norm_num) (abs_nonneg _) (by simpa using hK)
  have herror (j : Fin N) (l : P.labels j) (k : κ) :
      ‖multiplierError (selector j l k) t (w/P.length j) s‖≤(2*M+Lip)*e j := by
    apply multiplierError_bound _ _ _ 1 (radius+Cb) M Lip s
      (div_pos hw (P.length_pos j)) (by norm_num) (by norm_num) hwide hM hLip
      (hbound j l k) (by simpa only [one_mul] using hnear j l k s)
    intro hfar
    by_contra hn
    have hsup := hsupport j l k s hn
    have ht : |s-t|≤|s-(t+P.rowSlope j l)|+|P.rowSlope j l| := by
      have hh := abs_sub_le s (t+P.rowSlope j l) t
      simpa only [add_sub_cancel_left] using hh
    have hh := ht.trans (add_le_add hsup (hslope j l))
    nlinarith
  let env := fun j (l : P.labels j) (u : Item j l) =>
    lineEnvelope (P.length j*(P.snappedSite j l u).1) (P.length j) P.order x *
    lineEnvelope (P.width*(P.snappedSite j l u).2) P.width P.order y
  have henv0 (j) (l : P.labels j) (u : Item j l) : 0≤env j l u :=
    mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  have hterm (j) (l : P.labels j) (u : Item j l) :
      ‖WithLp.toLp 2 (fun k => c j l u k *
        multiplierError (selector j l k) t (w/P.length j) s * P.raw i j l u k y x)‖ ≤
      P.absoluteConstant*sigma*(2*M+Lip)*e j*env j l u := by
    have hej := he0 j
    have henvj := henv0 j l u
    have hh := diagonal_packet_norm (c j l u)
      (fun k => multiplierError (selector j l k) t (w/P.length j) s * P.raw i j l u k y x)
      (show 0≤((2*M+Lip)*e j)*(P.absoluteConstant*env j l u) by positivity)
      (fun k => by
        rw [norm_mul]
        exact mul_le_mul (herror j l k) (P.tree_raw_envelope i j l u k y x)
          (norm_nonneg _) (mul_nonneg (by linarith) (he0 j)))
    have hh' := hh.trans (mul_le_mul_of_nonneg_left (hc j l u)
      (show 0≤((2*M+Lip)*e j)*(P.absoluteConstant*env j l u) by positivity))
    calc
      _ = ‖WithLp.toLp 2 (fun k => c j l u k *
          (multiplierError (selector j l k) t (w/P.length j) s * P.raw i j l u k y x))‖ := by
        congr 1
        ext k
        simp only [mul_assoc]
      _ ≤ _ := hh'
      _ = _ := by ring
  have hlabel (j) (l : P.labels j) :
      polynomialWeight b (2*P.width) q y^2 *
        (∑ u : Item j l, ‖WithLp.toLp 2 (fun k => c j l u k *
          multiplierError (selector j l k) t (w/P.length j) s * P.raw i j l u k y x)‖) ≤
      P.absoluteConstant*sigma*(2*M+Lip)*e j*(16^q*(4*Real.pi)^2) := by
    have hej := he0 j
    calc
      _ ≤ polynomialWeight b (2*P.width) q y^2 *
          (∑ u : Item j l, P.absoluteConstant*sigma*(2*M+Lip)*e j*env j l u) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ => hterm j l u) (sq_nonneg _)
      _ = (P.absoluteConstant*sigma*(2*M+Lip)*e j)*
          (polynomialWeight b (2*P.width) q y^2*∑ u : Item j l, env j l u) := by
        rw [←Finset.mul_sum]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (P.tree_transverse_overlap q horder b hcenter j l y x)
        (by positivity)
  have hscale (j) : polynomialWeight b (2*P.width) q y^2 *
      (∑ l : P.labels j, ∑ u : Item j l, ‖WithLp.toLp 2 (fun k => c j l u k *
        multiplierError (selector j l k) t (w/P.length j) s * P.raw i j l u k y x)‖) ≤
      (B:ℝ)*P.absoluteConstant*sigma*(2*M+Lip)*e j*(16^q*(4*Real.pi)^2) := by
    rw [Finset.mul_sum]
    apply (Finset.sum_le_sum fun l _ => hlabel j l).trans
    simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
    have hb : (Fintype.card (P.labels j):ℝ)≤B := by
      simpa only [Fintype.card_coe] using (Nat.cast_le.mpr (hcard j) : ((P.labels j).card:ℝ)≤B)
    have hej := he0 j
    have hh := mul_le_mul_of_nonneg_right hb
      (show 0≤P.absoluteConstant*sigma*(2*M+Lip)*e j*(16^q*(4*Real.pi)^2) by positivity)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  calc
    _ ≤ polynomialWeight b (2*P.width) q y^2 *
        (∑ j, ∑ l : P.labels j, ∑ u : Item j l, ‖WithLp.toLp 2 (fun k => c j l u k *
          multiplierError (selector j l k) t (w/P.length j) s * P.raw i j l u k y x)‖) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => norm_sum_le _ _))
    _ ≤ ∑ j, (B:ℝ)*P.absoluteConstant*sigma*(2*M+Lip)*e j*(16^q*(4*Real.pi)^2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => hscale j
    _ = ((B:ℝ)*P.absoluteConstant*sigma*(2*M+Lip)*16^q*(4*Real.pi)^2) * ∑ j, e j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left heSum (by positivity)

theorem physicalTreeSelectorValue_eq_raw (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (beta : ∀ j, P.labels j → κ → ℂ) (z : ℝ×ℝ) :
    P.physicalTreeSelectorValue t c beta z =
      P.rawSelectorTreeValue 0 c beta (z.2-t*z.1) z.1 := by
  have hraw (j) (l : P.labels j) (u : Item j l) (k : κ) :
      P.raw 0 j l u k (z.2-t*z.1) z.1=P.physicalPacket t j l u k z := by
    have hh := congrArg (fun f : SchwartzMap ℝ ℂ => f z.1)
      (P.raw_eq_physical_slice 0 j l u k (z.2-t*z.1) t)
    change _ = P.physicalPacket t j l u k (z.1,z.2-t*z.1+t*z.1) at hh
    simpa only [sub_add_cancel] using hh
  simp only [physicalTreeSelectorValue,rawSelectorTreeValue,hraw]

/-- Both the original sum and its frozen replacement keep the same
angular indicator. No support assertion about the frozen sum is used. -/
theorem physical_tree_freezing_error (q K B : ℕ) (horder : 1+2*q≤P.order)
    (hcard : ∀ j, (P.labels j).card≤B) (w b t radius Cb M Lip sigma : ℝ)
    (hw : 0<w) (hM : 0≤M) (hLip : 0≤Lip) (hsigma : 0 ≤ sigma)
    (hwide : 1 ≤ radius+Cb) (hK : radius+Cb≤(2:ℝ)^K)
    (hcenter : ∀ j l u, |P.actualZ j l u-b|≤P.width)
    (hslope : ∀ j l, |P.rowSlope j l|≤Cb*(w/P.length j))
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (hc : ∀ j l u, ‖c j l u‖ ≤ sigma)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hbound : ∀ j l k s, ‖selector j l k s‖≤M)
    (hsupport : ∀ j l k s, selector j l k s≠0 →
      |s-(t+P.rowSlope j l)| ≤ radius*(w/P.length j))
    (hnear : ∀ j l k s, |s-t|≤w/P.length j →
      ‖selector j l k s-selector j l k t‖≤Lip*(|s-t|/(w/P.length j)))
    (S : Set ℝ) (s : ℝ) (z : ℝ×ℝ) :
    polynomialWeight b (2*P.width) q (z.2-t*z.1)^2 *
      ‖(if s∈S then P.physicalTreeSelectorValue t c (fun j l k => selector j l k s) z else 0) -
        (if s∈S then P.physicalTreeSelectorValue t c
          (fun j l k => if |s-t|≤w/P.length j then selector j l k t else 0) z else 0)‖ ≤
      if s∈S then (B:ℝ)*P.absoluteConstant*sigma*(2*M+Lip)*16^q*(4*Real.pi)^2*((K+1:ℕ)+4)
      else 0 := by
  classical
  by_cases hS : s∈S
  · simp only [hS,ite_true, if_true,physicalTreeSelectorValue_eq_raw,rawSelectorTreeValue_sub]
    exact P.raw_tree_selector_error q K B horder hcard w b t radius Cb M Lip sigma
      hw hM hLip hsigma hwide hK hcenter hslope c hc selector hbound hsupport hnear
      0 s (z.2-t*z.1) z.1
  · simp only [hS,ite_false, if_false,sub_self,norm_zero,mul_zero,le_refl]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLongTreeSplit
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original long sum, its frozen coefficients, and the literal
selector error. No support property is imposed on the frozen sum. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

theorem longCoefficient_norm_le (r : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (sigma : ℝ) (hsigma : 0 ≤ sigma) (hc : ∀ j l v, ‖c j l v‖ ≤ sigma)
    (j : Fin N) (l : P.labels j) (v : Item j l) :
    ‖P.longCoefficient r c j l v‖ ≤ sigma := by
  by_cases hj : 32*r<P.length j
  · simpa only [longCoefficient,ite_eq_left hj] using hc j l v
  · simpa only [longCoefficient,ite_eq_right hj,norm_zero] using hsigma

theorem physicalTreeSelectorValue_measurable
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (beta : ∀ j, P.labels j → κ → (ℝ×ℝ) → ℂ)
    (hbeta : ∀ j l k, Measurable (beta j l k)) :
    Measurable (fun z => P.physicalTreeSelectorValue 0 c (fun j l k => beta j l k z) z) := by
  unfold physicalTreeSelectorValue
  apply Finset.measurable_sum
  intro j _
  apply Finset.measurable_sum
  intro l _
  apply Finset.measurable_sum
  intro v _
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_iff.mpr
  intro k
  exact (measurable_const.mul (hbeta j l k)).mul
    (P.physicalPacket 0 j l v k).continuous.measurable

/-- Coordinate multipliers of norm at most one do not enlarge the
coefficient size used by the frozen tree estimate. -/
theorem frozenSelectorCoefficient_norm_le
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, ‖selector j l k 0‖≤1)
    (j : Fin N) (l : P.labels j) (v : Item j l) :
    ‖P.frozenSelectorCoefficient c selector j l v‖≤‖c j l v‖ := by
  simpa only [frozenSelectorCoefficient,one_mul] using
    diagonal_packet_norm (c j l v) (fun k => selector j l k 0) (by norm_num : (0:ℝ)≤1) (hb j l)

theorem physicalTreeSelectorValue_eq_sum
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    P.physicalTreeSelectorValue 0 c (fun j l k => selector j l k (u z)) z=
      ∑ q : P.PacketIndex, P.ordinaryPacketValue 0
        (fun q => c q.1 q.2.1 q.2.2) selector u q z := by
  simp only [physicalTreeSelectorValue,ordinaryPacketValue,Fintype.sum_sigma]

theorem longOriginalLocal_eq_sum
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (i : P.DensityWhitneyCell) (z : ℝ×ℝ) :
    P.longOriginalLocal c selector u i z=
      ∑ q : P.PacketIndex, if 32*DyadicLineGrid.scale i.val.1<P.length q.1 then
        P.ordinaryPacketValue 0 (fun q => c q.1 q.2.1 q.2.2) selector u q z else 0 := by
  rw [longOriginalLocal,P.physicalTreeSelectorValue_eq_sum]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : 32*DyadicLineGrid.scale i.val.1<P.length q.1
  · simp only [ordinaryPacketValue,longCoefficient,ite_eq_left hq]
  · simp only [ordinaryPacketValue,longCoefficient,ite_eq_right hq,
      WithLp.ofLp_zero,Pi.zero_apply,zero_mul]
    rfl

theorem ordinaryTreeLocal_split
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (i : P.DensityWhitneyCell) (z : ℝ×ℝ) :
    P.physicalTreeSelectorValue 0 c (fun j l k => selector j l k (u z)) z=
      P.shortLocalValue 0 32 (fun q => c q.1 q.2.1 q.2.2) selector u i z+
        P.longOriginalLocal c selector u i z := by
  rw [P.physicalTreeSelectorValue_eq_sum,P.longOriginalLocal_eq_sum,shortLocalValue,
    ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : P.length q.1≤32*DyadicLineGrid.scale i.val.1
  · simp only [ite_eq_left hq,ite_eq_right (not_lt.mpr hq),add_zero]
  · simp only [ite_eq_right hq,ite_eq_left (lt_of_not_ge hq),zero_add]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceAngularTreeSplit
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact short/frozen/error identity with an independent angular
cutoff, and the corresponding integrated selector error. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable


theorem frozenLongValue_eq_selector_at_width (w r s : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (z : ℝ×ℝ) :
    P.frozenLongValue 0 r w s (P.frozenSelectorCoefficient c selector) z=
      P.physicalTreeSelectorValue 0 (P.longCoefficient r c)
        (fun j l k => if |s-0|≤w/P.length j then selector j l k 0 else 0) z := by
  ext k
  simp only [frozenLongValue,physicalTreeSelectorValue,WithLp.ofLp_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : 32*r<P.length j <;> by_cases hs : |s-0|≤w/P.length j <;>
    simp only [hj,hs,and_true,and_false,ite_true, if_true,ite_false, if_false,planarFixedSynthesis,
      WithLp.ofLp_toLp,Fintype.sum_sigma,longCoefficient,frozenSelectorCoefficient,
      WithLp.ofLp_zero,Pi.zero_apply,mul_zero,zero_mul,Finset.sum_const_zero]


theorem longErrorLocalAtWidth_measurable (w : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hselector : ∀ j l k, Measurable (selector j l k))
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (i : P.DensityWhitneyCell) :
    Measurable (P.longErrorLocalAtWidth w c selector u i) := by
  exact (P.physicalTreeSelectorValue_measurable
    (P.longCoefficient (DyadicLineGrid.scale i.val.1) c)
    (fun j l k z => selector j l k (u z)) (fun j l k => (hselector j l k).comp hu)).sub
    (P.frozenLongValue_measurable 0 (DyadicLineGrid.scale i.val.1) w
      (P.frozenSelectorCoefficient c selector) u hu)

/-- The dyadic selector-error estimate applies to the exact long
restriction without paying for the number of scales. -/
theorem longErrorLocalAtWidth_bound (w : ℝ) (hw : 0<w) (K B : ℕ) (horder : 107≤P.order)
    (hcard : ∀ j, (P.labels j).card≤B) (b radius Cb M Lip sigma : ℝ)
    (hM : 0≤M) (hLip : 0≤Lip) (hsigma : 0 ≤ sigma)
    (hwide : 1 ≤ radius+Cb) (hK : radius+Cb≤(2:ℝ)^K)
    (hcenter : ∀ j l v, |P.actualZ j l v-b|≤P.width)
    (hslope : ∀ j l, |P.rowSlope j l|≤Cb*(w/P.length j))
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (hc : ∀ j l v, ‖c j l v‖ ≤ sigma)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hbound : ∀ j l k s, ‖selector j l k s‖≤M)
    (hsupport : ∀ j l k s, selector j l k s≠0 →
      |s-P.rowSlope j l| ≤ radius*(w/P.length j))
    (hnear : ∀ j l k s, |s|≤w/P.length j →
      ‖selector j l k s-selector j l k 0‖≤Lip*(|s|/(w/P.length j)))
    (u : ℝ×ℝ → ℝ) (i : P.DensityWhitneyCell) (z : ℝ×ℝ) :
    polynomialWeight b (2*P.width) 53 z.2^2*‖P.longErrorLocalAtWidth w c selector u i z‖≤
      (B:ℝ)*P.absoluteConstant*sigma*(2*M+Lip)*16^53*(4*Real.pi)^2*((K+1:ℕ)+4) := by
  have h := P.physical_tree_freezing_error 53 K B horder hcard w b 0 radius Cb M Lip sigma
    hw hM hLip hsigma hwide hK hcenter hslope
    (P.longCoefficient (DyadicLineGrid.scale i.val.1) c)
    (P.longCoefficient_norm_le _ c sigma hsigma hc) selector hbound
    (by simpa only [zero_add] using hsupport) (by simpa only [sub_zero] using hnear)
    Set.univ (u z) z
  simpa only [longErrorLocalAtWidth,longOriginalLocal,P.frozenLongValue_eq_selector_at_width,
    Set.mem_univ,ite_true, if_true,zero_mul,sub_zero] using h


theorem angular_long_error_integrable_bound (w : ℝ) (hw : 0<w) (hne : Nonempty P.PacketIndex)
    (K B : ℕ) (horder : 107≤P.order) (hcard : ∀ j, (P.labels j).card≤B)
    (a b radius Cb M Lip sigma eta : ℝ)
    (hM : 0≤M) (hLip : 0≤Lip) (hsigma : 0 ≤ sigma) (heta : 0≤eta)
    (hwide : 1 ≤ radius+Cb) (hK : radius+Cb≤(2:ℝ)^K)
    (hX : ∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2)
    (hY : ∀ j l v, |P.actualZ j l v-b|≤P.width)
    (hslope : ∀ j l, |P.rowSlope j l|≤Cb*(w/P.length j))
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (hc : ∀ j l v, ‖c j l v‖ ≤ sigma)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hselector : ∀ j l k, Measurable (selector j l k))
    (hbound : ∀ j l k s, ‖selector j l k s‖≤M)
    (hsupport : ∀ j l k s, selector j l k s≠0 →
      |s-P.rowSlope j l| ≤ radius*(w/P.length j))
    (hnear : ∀ j l k s, |s|≤w/P.length j →
      ‖selector j l k s-selector j l k 0‖≤Lip*(|s|/(w/P.length j)))
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (Omega : P.DensityWhitneyCell → Set ℝ) (hOmega : ∀ i, MeasurableSet (Omega i))
    (hEmpty : ∀ i, ¬P.HasLongPacket i → Omega i=∅)
    (hmass : ∀ i n, (volume.prod volume).real
      (partitionCell b P.width (i.val,n)∩(E∩u ⁻¹' Omega i))≤
      32*(2:ℝ)^203*eta*(1+|(n:ℝ)|)^203*DyadicLineGrid.scale i.val.1*P.width) :
    Integrable (P.longErrorTreeValueAtWidth w hne c selector E u Omega) (volume.prod volume) ∧
    (∫ z, ‖P.longErrorTreeValueAtWidth w hne c selector E u Omega z‖ ∂volume.prod volume)≤
      (32^106*((B:ℝ)*P.absoluteConstant*sigma*(2*M+Lip)*16^53*(4*Real.pi)^2*((K+1:ℕ)+4))*
        (32*(2:ℝ)^203*eta))*(9*P.topLength*P.width*transverseTailConstant) := by
  have hD : 0≤(B:ℝ)*P.absoluteConstant*sigma*(2*M+Lip)*16^53*(4*Real.pi)^2*((K+1:ℕ)+4) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg B) P.absoluteConstant_pos.le) hsigma)
      (by linarith)) (pow_nonneg (by norm_num) 53)) (sq_nonneg _)) (by positivity)
  exact P.tree_error_integrable_bound hne (P.longErrorLocalAtWidth w c selector u)
    (fun i => (P.longErrorLocalAtWidth_measurable w c selector hselector u hu i).aestronglyMeasurable)
    a b _ eta hD heta hX
    (P.longErrorLocalAtWidth_bound w hw K B horder hcard b radius Cb M Lip sigma
      hM hLip hsigma hwide hK hY hslope c hc selector hbound hsupport hnear u)
    E hE u hu Omega hOmega hEmpty hmass


end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMaskedTreeSplit
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact short/frozen/error identity with an independent angular
cutoff, and the corresponding integrated selector error. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

theorem longOriginalLocal_mask_of_support
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (Omega : P.DensityWhitneyCell → Set ℝ)
    (hsupport : ∀ i (q : P.PacketIndex), 32*DyadicLineGrid.scale i.val.1<P.length q.1 →
      ∀ k s, selector q.1 q.2.1 k s≠0 → s∈Omega i)
    (E : Set (ℝ×ℝ)) (i : P.DensityWhitneyCell) (z : ℝ×ℝ) :
    E.indicator (P.longOriginalLocal c selector u i) z=
      (E∩u ⁻¹' Omega i).indicator (P.longOriginalLocal c selector u i) z := by
  classical
  by_cases hz : z∈E
  · by_cases hu : u z∈Omega i
    · simp only [indicator_of_mem hz,indicator_of_mem (show z∈E∩u ⁻¹' Omega i from ⟨hz,hu⟩)]
    · rw [indicator_of_mem hz,indicator_of_notMem (show z∉E∩u ⁻¹' Omega i from fun h => hu h.2)]
      rw [P.longOriginalLocal_eq_sum]
      apply Finset.sum_eq_zero
      intro q _
      by_cases hq : 32*DyadicLineGrid.scale i.val.1<P.length q.1
      · simp only [ite_eq_left hq]
        have hb (k : κ) : selector q.1 q.2.1 k (u z)=0 := by
          by_contra hk
          exact hu (hsupport i q hq k (u z) hk)
        simp only [ordinaryPacketValue,hb,mul_zero,zero_mul]
        rfl
      · exact ite_eq_right hq
  · rw [indicator_of_notMem hz,indicator_of_notMem (show z∉E∩u ⁻¹' Omega i from fun h => hz h.1)]


theorem masked_ordinary_tree_split_identity (w : ℝ) (hne : Nonempty P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (Omega : P.DensityWhitneyCell → Set ℝ)
    (hsupport : ∀ i (q : P.PacketIndex), 32*DyadicLineGrid.scale i.val.1<P.length q.1 →
      ∀ k s, selector q.1 q.2.1 k s≠0 → s∈Omega i)
    (E : Set (ℝ×ℝ)) :
    E.indicator (fun z => P.physicalTreeSelectorValue 0 c (fun j l k => selector j l k (u z)) z)=
      fun z => E.indicator
        (P.shortTreeValue hne 0 32 (fun q => c q.1 q.2.1 q.2.2) selector u) z+
        P.frozenTreeValueAtWidth w hne (P.frozenSelectorCoefficient c selector) E u Omega z+
        P.longErrorTreeValueAtWidth w hne c selector E u Omega z := by
  classical
  funext z
  let i : P.DensityWhitneyCell := indexAt (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)
    (P.packet_univ_nonempty hne) (fun q _ => P.length_pos q.1) z.1
  have hs := P.ordinaryTreeLocal_split c selector u i z
  have hm := P.longOriginalLocal_mask_of_support c selector u Omega hsupport E i z
  simp only [Set.indicator_apply,shortTreeValue,frozenTreeValueAtWidth,frozenWhitneyLocalAtWidth,
    longErrorTreeValueAtWidth,paste]
  change (if z∈E then P.physicalTreeSelectorValue 0 c (fun j l k => selector j l k (u z)) z else 0)=
    (if z∈E then P.shortLocalValue 0 32 (fun q => c q.1 q.2.1 q.2.2) selector u i z else 0)+
    (if z∈E∩u ⁻¹' Omega i then P.frozenLongValue 0 (DyadicLineGrid.scale i.val.1) w
      (u z) (P.frozenSelectorCoefficient c selector) z else 0)+
    (if z∈E∩u ⁻¹' Omega i then P.longErrorLocalAtWidth w c selector u i z else 0)
  by_cases hz : z∈E
  · by_cases hu : u z∈Omega i
    · have ha : z∈E∩u ⁻¹' Omega i := ⟨hz,hu⟩
      simp only [ite_eq_left hz,ite_eq_left ha,longErrorLocalAtWidth]
      rw [hs]
      abel
    · have ha : z∉E∩u ⁻¹' Omega i := fun h => hu h.2
      simp only [indicator_of_mem hz,indicator_of_notMem ha] at hm
      simp only [ite_eq_left hz,ite_eq_right ha,add_zero]
      rw [hs,hm,add_zero]
  · have ha : z∉E∩u ⁻¹' Omega i := fun h => hz h.1
    simp only [ite_eq_right hz,ite_eq_right ha,zero_add]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceCoordinates
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Change of coordinates for actual tree sums and their integrals. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem integrableOn_slopeShear_iff {V : Type*} [NormedAddCommGroup V]
    (t : ℝ) (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (f : ℝ×ℝ → V) :
    IntegrableOn (fun z => f (slopeShear t z)) ((slopeShear t) ⁻¹' E) (volume.prod volume) ↔
      IntegrableOn f E (volume.prod volume) := by
  classical
  rw [←integrable_indicator_iff (hE.preimage (slopeShear t).measurable),
    ←integrable_indicator_iff hE]
  have he : ((slopeShear t) ⁻¹' E).indicator (fun z => f (slopeShear t z))=
      (E.indicator f) ∘ (slopeShear t) := by
    funext z
    simp only [Set.indicator_apply,mem_preimage,Function.comp_apply]
  rw [he]
  exact (slopeShear_measurePreserving t).integrable_comp_emb (slopeShear t).measurableEmbedding

theorem integralOn_slopeShear {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (t : ℝ) (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (f : ℝ×ℝ → V) :
    (∫ z in (slopeShear t) ⁻¹' E, f (slopeShear t z) ∂volume.prod volume)=
      ∫ z in E, f z ∂volume.prod volume := by
  classical
  rw [←integral_indicator (hE.preimage (slopeShear t).measurable),←integral_indicator hE]
  have he : ((slopeShear t) ⁻¹' E).indicator (fun z => f (slopeShear t z))=
      (E.indicator f) ∘ (slopeShear t) := by
    funext z
    simp only [Set.indicator_apply,mem_preimage,Function.comp_apply]
  rw [he]
  exact (slopeShear_measurePreserving t).integral_comp (slopeShear t).measurableEmbedding _

theorem treeCell_slopeShear (t b W : ℝ) (k j n : ℤ) :
    (slopeShear t) ⁻¹' SourceWhitney.treeCell t b W k j n=
      SourceWhitney.treeCell 0 b W k j n := by
  ext z
  simp only [mem_preimage,SourceWhitney.treeCell,mem_ofPred_eq]
  change (z.1∈DyadicLineGrid.cell 0 k j ∧
    |(z.2+t*z.1-t*z.1)-b-(n:ℝ)*W|≤W/2) ↔ _
  simp only [add_sub_cancel_right,zero_mul,sub_zero]

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem ordinaryPacketValue_slopeShear (t : ℝ)
    (c : P.PacketIndex → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (q : P.PacketIndex) (z : ℝ×ℝ) :
    P.ordinaryPacketValue 0 c (fun j l k s => selector j l k (s+t))
      (fun z => u (slopeShear t z)-t) q z=
      P.ordinaryPacketValue t c selector u q (slopeShear t z) := by
  simp only [ordinaryPacketValue,sub_add_cancel,P.physicalPacket_slopeShear]

theorem shortTreeValue_slopeShear (hne : Nonempty P.PacketIndex) (t CW : ℝ)
    (c : P.PacketIndex → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    P.shortTreeValue hne 0 CW c (fun j l k s => selector j l k (s+t))
      (fun z => u (slopeShear t z)-t) z=
      P.shortTreeValue hne t CW c selector u (slopeShear t z) := by
  classical
  have hf : (slopeShear t z).1=z.1 := rfl
  simp only [shortTreeValue,SourceWhitney.paste,shortLocalValue,hf]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs
  · exact P.ordinaryPacketValue_slopeShear t c selector u q z
  · rfl


theorem physicalTreeSelectorValue_slopeShear (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    P.physicalTreeSelectorValue 0 c
      (fun j l k => selector j l k ((u (slopeShear t z)-t)+t)) z=
      P.physicalTreeSelectorValue t c (fun j l k => selector j l k (u (slopeShear t z)))
        (slopeShear t z) := by
  ext k
  simp only [physicalTreeSelectorValue,Finset.sum_apply,
    WithLp.ofLp_sum,sub_add_cancel,P.physicalPacket_slopeShear]

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceMasks
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference-direction masks obtained from the original angular grid.
Only the direction variable is translated; no dyadic cell is reassigned. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem exists_reference_long_cell_mask
    (t b w : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid k j : ℤ) (tau : ℝ)
    (htime : P.topLength≤tau)
    (hWhitney : Whitney (Finset.univ : Finset P.PacketIndex)
      (fun a => P.actualX a.1 a.2.1 a.2.2) (fun a => P.length a.1) k j)
    (hY : ∀ a : P.PacketIndex, |P.actualZ a.1 a.2.1 a.2.2-b|≤P.width/2)
    (hreference : ∀ a : P.PacketIndex, t∈
      scaledAngularCell (w/P.topLength) grid a.1.val (cell a.1 a.2.1))
    (hlong : ∃ a : P.PacketIndex, 32*DyadicLineGrid.scale k<P.length a.1)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (eta : ℝ) (heta : 0≤eta)
    (hdensity : ∀ a, P.ordinaryDensity t cell grid w tau E u a≤eta) :
    ∃ Omega : Set ℝ, MeasurableSet Omega ∧
      (∀ a : P.PacketIndex, 32*DyadicLineGrid.scale k<P.length a.1 →
        (fun s : ℝ => s+t) ⁻¹' scaledAngularCell (w/P.topLength) grid a.1.val (cell a.1 a.2.1)⊆Omega) ∧
      (∀ n : ℤ, (volume.prod volume).real
        (partitionCell b P.width ((k,j),n)∩((slopeShear t) ⁻¹' E∩
          (fun z => u (slopeShear t z)-t) ⁻¹' Omega))≤
        32*(2:ℝ)^203*eta*(1+|(n:ℝ)|)^203*DyadicLineGrid.scale k*P.width) := by
  obtain ⟨a,test,_hx,_hy,_ht,_hl,_hu,hcontains,hmass⟩ :=
    P.source_whitney_cell_density t b cell grid k j w tau htime hWhitney hY
      hreference hlong E hE u hu eta heta hdensity
  let Omega := scaledAngularCell (w/P.topLength) grid test.level test.cell
  let O := (fun s : ℝ => s+t) ⁻¹' Omega
  refine ⟨O,(scaledAngularCell_measurable _ _ _ _).preimage (measurable_id.add_const t),?_,?_⟩
  · intro q hq s hs
    exact hcontains q hq hs
  · intro n
    have hm := hmass n
    dsimp only at hm
    let A := E∩u ⁻¹' Omega∩treeCell t b P.width k j n
    have hfin : (volume.prod volume) A≠∞ := by
      have h := (integrableOn_const_iff (C:=(1:ℝ))).mp hm.1
      simpa only [enorm_one,one_ne_zero,false_or,lt_top_iff_ne_top] using h
    have hfin' : (volume.prod volume) ((slopeShear t) ⁻¹' A)≠∞ := by
      rw [(slopeShear_measurePreserving t).measure_preimage_equiv]
      exact hfin
    apply (measureReal_mono (s₂ := (slopeShear t) ⁻¹' A) ?_ hfin').trans
    · have he : (volume.prod volume).real ((slopeShear t) ⁻¹' A)=
          (volume.prod volume).real A := by
        exact congrArg ENNReal.toReal ((slopeShear_measurePreserving t).measure_preimage_equiv A)
      rw [he]
      exact hm.2
    · intro z hz
      refine ⟨⟨hz.2.1,?_⟩,?_⟩
      · have hs := hz.2.2
        change u (slopeShear t z)-t+t∈Omega at hs
        change u (slopeShear t z)∈Omega
        simpa only [sub_add_cancel] using hs
      · have hcell := partitionCell_subset_treeCell b P.width ((k,j),n) hz.1
        exact (Set.ext_iff.mp (treeCell_slopeShear t b P.width k j n) z).mpr hcell



/-- Choose the density masks on the entire actual Whitney partition.
Cells without long packets receive the empty mask. -/
theorem exists_reference_whitney_masks
    (t b w : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (tau : ℝ)
    (htime : P.topLength≤tau)
    (hY : ∀ a : P.PacketIndex, |P.actualZ a.1 a.2.1 a.2.2-b|≤P.width/2)
    (hreference : ∀ a : P.PacketIndex, t∈
      scaledAngularCell (w/P.topLength) grid a.1.val (cell a.1 a.2.1))
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (eta : ℝ) (heta : 0≤eta)
    (hdensity : ∀ a, P.ordinaryDensity t cell grid w tau E u a≤eta) :
    ∃ Omega : P.DensityWhitneyCell → Set ℝ,
      (∀ i, MeasurableSet (Omega i)) ∧
      (∀ i, ¬P.HasLongPacket i → Omega i=∅) ∧
      (∀ i (a : P.PacketIndex), 32*DyadicLineGrid.scale i.val.1<P.length a.1 →
        (fun s : ℝ => s+t) ⁻¹' scaledAngularCell (w/P.topLength) grid a.1.val (cell a.1 a.2.1)⊆Omega i) ∧
      (∀ i n, (volume.prod volume).real
        (partitionCell b P.width (i.val,n)∩((slopeShear t) ⁻¹' E∩
          (fun z => u (slopeShear t z)-t) ⁻¹' Omega i))≤
        32*(2:ℝ)^203*eta*(1+|(n:ℝ)|)^203*DyadicLineGrid.scale i.val.1*P.width) := by
  classical
  let Long := {i : P.DensityWhitneyCell // P.HasLongPacket i}
  have hex (i : Long) := P.exists_reference_long_cell_mask t b w cell grid i.val.val.1 i.val.val.2 tau
    htime i.val.property hY hreference i.property E hE u hu eta heta hdensity
  choose O hO hcontains hmass using hex
  let Omega := fun i : P.DensityWhitneyCell => if hi : P.HasLongPacket i then O ⟨i,hi⟩ else ∅
  refine ⟨Omega,?_,?_,?_,?_⟩
  · intro i
    by_cases hi : P.HasLongPacket i
    · simpa only [Omega,dite_eq_left hi] using hO ⟨i,hi⟩
    · simp only [Omega,dite_eq_right hi,MeasurableSet.empty]
  · intro i hi
    exact dite_eq_right hi
  · intro i a ha
    have hi : P.HasLongPacket i := ⟨a,ha⟩
    simpa only [Omega,dite_eq_left hi] using hcontains ⟨i,hi⟩ a ha
  · intro i n
    by_cases hi : P.HasLongPacket i
    · simpa only [Omega,dite_eq_left hi] using hmass ⟨i,hi⟩ n
    · have hzero : Omega i=∅ := dite_eq_right hi
      rw [hzero,preimage_empty,inter_empty,inter_empty,measureReal_empty]
      exact mul_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) 203)) heta) (by positivity)) (DyadicLineGrid.scale_pos _).le)
        P.width_pos.le


end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceOrdinaryTree
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary trees in arbitrary reference coordinates. Original angular
cells and density tests are kept through the measure-preserving shear. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice

theorem exists_reference_ordinary_tree_estimate_oai (hL : LepingleInput)
    (cStar cEta CEta cb Cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 ≤ cb) (hCb : 0≤Cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (B K : ℕ),
      (∀ j, (P.labels j).card≤B) → 207≤P.order →
    ∀ (_hne : Nonempty P.PacketIndex)
      (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (t a b w tau radius Lip eta sigma : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ),
      0<w → P.topLength≤tau → 0≤Lip → 0≤eta → 0 ≤ sigma →
      1 ≤ radius+Cb → radius+Cb≤(2:ℝ)^K →
      (∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2) →
      (∀ q : P.PacketIndex, |P.actualZ q.1 q.2.1 q.2.2-b|≤P.width/2) →
      (∀ q : P.PacketIndex, t∈scaledAngularCell (w/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ j l, t+P.rowSlope j l∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket t j l v k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope j l)*η| ≤ cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j (l : P.labels j), |P.rowSlope j l|≤Cb*w/P.length j) →
      (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket t j l v k) (ξ,η)≠0 →
        |η-P.frequency k|≤Cv/P.width) →
      (∀ j l v, ‖c j l v‖ ≤ sigma) →
      P.angularSeparatedTreeEnergy cb w c ≤ sigma^2*(P.topLength*P.width) →
    ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (selector j l k)) →
      (∀ j l k s, ‖selector j l k s‖≤1) →
      (∀ j l k, selector j l k t≠0 → cb*w/P.length j≤|P.rowSlope j l|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 →
        |s-(t+P.rowSlope j l)| ≤ radius*(w/P.length j)) →
      (∀ j l k s, |s-t|≤w/P.length j →
        ‖selector j l k s-selector j l k t‖≤Lip*(|s-t|/(w/P.length j))) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∀ q, P.ordinaryDensity t cell grid w tau E u q≤eta) →
      let F := fun z => P.physicalTreeSelectorValue t c (fun j l k => selector j l k (u z)) z
      IntegrableOn F E (volume.prod volume) ∧
        (∫ z in E, ‖F z‖ ∂volume.prod volume)≤
          P.ordinaryTreeConstant C B K Lip*sigma*eta*P.topLength*P.width := by
  obtain ⟨C,hC,hfrozen⟩ := exists_masked_frozen_tree_estimate hL
    cStar cEta CEta cb Cb Cv hcStar hcEta hCEta hCv hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P B K hcard horder hne c t a b w tau radius Lip eta sigma cell grid
    hw htime hLip heta hsigma hwide hK hX hY href hangle hspectrum hslope hbin hc hsize
    selector hsel hselbound hselaway hselsupport hselradius hselnear E hE u hu hdensity
  let E0 := (slopeShear t) ⁻¹' E
  let u0 := fun z => u (slopeShear t z)-t
  let sel := fun j l k s => selector j l k (s+t)
  have hE0 : MeasurableSet E0 := hE.preimage (slopeShear t).measurable
  have hu0 : Measurable u0 := (hu.comp (slopeShear t).measurable).sub_const t
  have hsel0 : ∀ j l k, Measurable (sel j l k) := fun j l k =>
    (hsel j l k).comp (measurable_id.add_const t)
  let d := P.frozenSelectorCoefficient c sel
  have hd (j : Fin N) (l : P.labels j) (v : Item j l) : ‖d j l v‖≤‖c j l v‖ :=
    P.frozenSelectorCoefficient_norm_le c sel (fun j l k => by
      simpa only [sel,zero_add] using hselbound j l k t) j l v
  have hlowerD (j : Fin N) (l : P.labels j) (v : Item j l) (hv : d j l v≠0) :
      cb*w/P.length j≤|P.rowSlope j l| := by
    by_contra hl
    apply hv
    ext k
    have hb : sel j l k 0=0 := by
      by_contra hk
      exact hl (hselaway j l k (by simpa only [sel,zero_add] using hk))
    simp only [d,frozenSelectorCoefficient,WithLp.ofLp_toLp,hb,mul_zero,
      WithLp.ofLp_zero,Pi.zero_apply]
  have hsizeD : (∑ j, ∑ l : P.labels j, ∑ v : Item j l, ‖d j l v‖^2*P.length j*P.width)≤
      sigma^2*(P.topLength*P.width) := by
    apply le_trans _ hsize
    unfold angularSeparatedTreeEnergy
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro l _
    apply Finset.sum_le_sum
    intro v _
    by_cases hsep : cb*w/P.length j≤|P.rowSlope j l|
    · rw [ite_eq_left hsep]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hd j l v) 2)
          (P.length_pos j).le) P.width_pos.le
    · have hz : d j l v=0 := by
        by_contra hn
        exact hsep (hlowerD j l v hn)
      simp only [ite_eq_right hsep,hz,norm_zero,zero_pow (by decide : 2≠0),zero_mul,le_refl]
  obtain ⟨Omega,hOm,hEmpty,hcontains,hmass⟩ := P.exists_reference_whitney_masks t b w
    cell grid tau htime hY href E hE u hu eta heta hdensity
  have hspectrum0 := P.reference_packet_spectrum t w cStar cEta CEta hspectrum
  have hbin0 := P.reference_packet_bin t Cv hbin
  have hsizeD' := hsizeD
  have hfrozen := hfrozen N κ Label Item P B hcard horder hne d a b w eta sigma
    hw heta hsigma hX hY hspectrum0 hslope hbin0 hlowerD hsizeD' E0 hE0 u0 hu0
    Omega hOm hEmpty hmass
  have hFI := hfrozen.1
  have hFB := hfrozen.2
  have hY' (j : Fin N) (l : P.labels j) (v : Item j l) : |P.actualZ j l v-b|≤P.width :=
    (hY ⟨j,⟨l,v⟩⟩).trans (by linarith [P.width_pos])
  have hshort := P.short_tree_integrable_bound hne B hcard t cell grid w tau htime
    hangle (by omega) 1 sigma eta (by norm_num) hsigma heta
    (fun q => c q.1 q.2.1 q.2.2) (fun q => hc q.1 q.2.1 q.2.2)
    selector hsel hselbound hselsupport u hu E hE hdensity a b 32 (by norm_num) hX hY'
  let S0 := P.shortTreeValue hne 0 32 (fun q => c q.1 q.2.1 q.2.2) sel u0
  let St := P.shortTreeValue hne t 32 (fun q => c q.1 q.2.1 q.2.2) selector u
  have hSeq : S0=(fun z => St (slopeShear t z)) := by
    funext z
    exact P.shortTreeValue_slopeShear hne t 32 (fun q => c q.1 q.2.1 q.2.2) selector u z
  have hSI0 : IntegrableOn S0 E0 (volume.prod volume) := by
    rw [hSeq]
    exact (integrableOn_slopeShear_iff t E hE St).mpr hshort.1
  have hSbound : (∫ z in E0, ‖S0 z‖ ∂volume.prod volume)=
      ∫ z in E, ‖St z‖ ∂volume.prod volume := by
    rw [hSeq]
    exact integralOn_slopeShear t E hE (fun z => ‖St z‖)
  have hselradius0 : ∀ j l k s, sel j l k s≠0 →
      |s-P.rowSlope j l| ≤ radius*(w/P.length j) := by
    intro j l k s hs
    have he : s+t-(t+P.rowSlope j l)=s-P.rowSlope j l := by ring
    simpa only [he] using hselradius j l k (s+t) hs
  have hselnear0 : ∀ j l k s, |s|≤w/P.length j →
      ‖sel j l k s-sel j l k 0‖≤Lip*(|s|/(w/P.length j)) := by
    intro j l k s hs
    simpa only [sel,add_sub_cancel_right,zero_add] using hselnear j l k (s+t)
      (by simpa only [add_sub_cancel_right] using hs)
  have herr := P.angular_long_error_integrable_bound w hw hne K B (by omega) hcard a b radius Cb 1 Lip sigma eta
    (by norm_num) hLip hsigma heta hwide hK hX hY'
    (by simpa only [mul_div_assoc] using hslope)
    c hc sel hsel0 (fun j l k s => hselbound j l k (s+t)) hselradius0 hselnear0 E0 hE0 u0 hu0 Omega hOm hEmpty hmass
  let S := E0.indicator S0
  let F := P.frozenTreeValueAtWidth w hne d E0 u0 Omega
  let R := P.longErrorTreeValueAtWidth w hne c sel E0 u0 Omega
  let V := fun z => P.physicalTreeSelectorValue 0 c (fun j l k => sel j l k (u0 z)) z
  let Vt := fun z => P.physicalTreeSelectorValue t c (fun j l k => selector j l k (u z)) z
  have hVeq : V=(fun z => Vt (slopeShear t z)) := by
    funext z
    exact P.physicalTreeSelectorValue_slopeShear t c selector u z
  have hSI : Integrable S (volume.prod volume) := (integrable_indicator_iff hE0).mpr hSI0
  have hident : E0.indicator V = fun z => S z+F z+R z :=
    P.masked_ordinary_tree_split_identity w hne c sel u0 Omega
      (fun i q hq k s hs => hcontains i q hq (hselsupport q.1 q.2.1 k (s+t) hs)) E0
  have hVI : Integrable (E0.indicator V) (volume.prod volume) := by
    rw [hident]
    exact (hSI.add hFI).add herr.1
  have hnormS : (∫ z, ‖S z‖ ∂volume.prod volume)=
      ∫ z in E, ‖St z‖
        ∂volume.prod volume := by
    simp only [S,norm_indicator_eq_indicator_norm]
    exact (integral_indicator hE0).trans hSbound
  have hSB : (∫ z, ‖S z‖ ∂volume.prod volume)≤
      (27*288*(4*Real.pi)^2*(B:ℝ)*32*3^203*P.profileBound*1)*sigma*eta*P.topLength*P.width := by
    rw [hnormS]
    exact hshort.2
  have hVtI : IntegrableOn Vt E (volume.prod volume) := by
    apply (integrableOn_slopeShear_iff t E hE Vt).mp
    rw [←hVeq]
    exact (integrable_indicator_iff hE0).mp hVI
  refine ⟨hVtI,?_⟩
  have hnormV : (∫ z, ‖E0.indicator V z‖ ∂volume.prod volume)=
      ∫ z in E, ‖Vt z‖ ∂volume.prod volume := by
    simp only [norm_indicator_eq_indicator_norm]
    apply (integral_indicator hE0).trans
    rw [hVeq]
    exact integralOn_slopeShear t E hE (fun z => ‖Vt z‖)
  rw [←hnormV,hident]
  calc
    _ ≤ ∫ z, ‖S z‖+‖F z‖+‖R z‖ ∂volume.prod volume := by
      apply integral_mono ((hSI.add hFI).add herr.1).norm ((hSI.norm.add hFI.norm).add herr.1.norm)
      intro z
      change ‖S z+F z+R z‖≤‖S z‖+‖F z‖+‖R z‖
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (∫ z, ‖S z‖ ∂volume.prod volume)+(∫ z, ‖F z‖ ∂volume.prod volume)+
        (∫ z, ‖R z‖ ∂volume.prod volume) := by
      have hiSF : Integrable (fun z => ‖S z‖+‖F z‖) (volume.prod volume) := hSI.norm.add hFI.norm
      have hiR : Integrable (fun z => ‖R z‖) (volume.prod volume) := herr.1.norm
      have hiS : Integrable (fun z => ‖S z‖) (volume.prod volume) := hSI.norm
      have hiF : Integrable (fun z => ‖F z‖) (volume.prod volume) := hFI.norm
      rw [integral_add hiSF hiR,integral_add hiS hiF]
    _ ≤ _ := add_le_add (add_le_add hSB hFB) herr.2
    _ = _ := by
      simp only [ordinaryTreeConstant,add_mul,mul_one]
      simp only [mul_assoc,mul_comm,mul_left_comm]


end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.SourceLabeledLattice.exists_reference_ordinary_tree_estimate_oai := @OAI.LipschitzHilbert.SourceLabeledLattice.exists_reference_ordinary_tree_estimate_oai
