-- Prove2me | solution 1 for OAI.LipschitzHilbert.PacketLatticeData.eventually_physical_parent_full_residual_square
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T19:56:39.662993+00:00
-- url     : https://prove2.me/submissions/5fa17d8c-f1cf-409d-97f4-f96025021bb8

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TwoPointEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two-point decay estimate behind the positive error convolution.
Only fixed exponents six and three are needed. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem envelope_triangle_base (s l x y : ℝ) :
    1 + ((x-y)/l)^2 ≤ 2 * (1+((x-s)/l)^2) * (1+((y-s)/l)^2) := by
  have heq : (x-y)/l = (x-s)/l - (y-s)/l := by ring
  rw [heq]
  nlinarith [sq_nonneg ((x-s)/l + (y-s)/l),
    sq_nonneg (((x-s)/l)*((y-s)/l))]

theorem envelope_three_product (s l x y : ℝ) :
    lineEnvelope s l 3 x * lineEnvelope s l 3 y ≤ 8 * lineEnvelope y l 3 x := by
  let A := 1+((x-s)/l)^2
  let B := 1+((y-s)/l)^2
  let D := 1+((x-y)/l)^2
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have h := pow_le_pow_left₀ hD.le (envelope_triangle_base s l x y) 3
  change (A^3)⁻¹ * (B^3)⁻¹ ≤ 8 * (D^3)⁻¹
  rw [← mul_inv, ← one_div, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (mul_pos (pow_pos hA 3) (pow_pos hB 3)) (pow_pos hD 3)).mpr
  simpa only [mul_pow, show (2:ℝ)^3=8 by norm_num, one_mul, mul_assoc] using h

theorem envelope_six_product (s l x y : ℝ) :
    lineEnvelope s l 6 x * lineEnvelope s l 6 y ≤
      8 * lineEnvelope y l 3 x * lineEnvelope s l 3 x := by
  have hsmall : lineEnvelope s l 3 y ≤ 1 := by
    simpa only [lineEnvelope, pow_zero, inv_one] using
      lineEnvelope_antitone s l y (by decide : 0 ≤ 3)
  have hpow (z : ℝ) : lineEnvelope s l 6 z = lineEnvelope s l 3 z ^ 2 := by
    unfold lineEnvelope
    rw [show (6:ℕ) = 3*2 from rfl, pow_mul, inv_pow]
  have heq : lineEnvelope s l 6 x * lineEnvelope s l 6 y =
      (lineEnvelope s l 3 x * lineEnvelope s l 3 y) *
        (lineEnvelope s l 3 x * lineEnvelope s l 3 y) := by
    rw [hpow x, hpow y]
    ring
  rw [heq]
  have h1 := envelope_three_product s l x y
  have h2 : lineEnvelope s l 3 x * lineEnvelope s l 3 y ≤ lineEnvelope s l 3 x := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsmall (lineEnvelope_nonneg _ _ _ _)
  calc
    _ ≤ (8 * lineEnvelope y l 3 x) * lineEnvelope s l 3 x :=
      mul_le_mul h1 h2 (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
        (mul_nonneg (by norm_num) (lineEnvelope_nonneg _ _ _ _))
    _ = _ := by ring

theorem two_point_tile_envelope {ι : Type*} [Fintype ι]
    (site : ι → ℤ × ℤ) (hinj : Function.Injective site)
    (a b l W x y x' y' : ℝ) (hl : 0 < l) (hW : 0 < W) :
    (∑ i, (lineEnvelope (a+l*(site i).1) l 6 x * lineEnvelope (b+W*(site i).2) W 6 y) *
      (lineEnvelope (a+l*(site i).1) l 6 x' * lineEnvelope (b+W*(site i).2) W 6 y')) ≤
    (64 * (4 * Real.pi)^2) * lineEnvelope x' l 3 x * lineEnvelope y' W 3 y := by
  have hterm (i : ι) :
      (lineEnvelope (a+l*(site i).1) l 6 x * lineEnvelope (b+W*(site i).2) W 6 y) *
      (lineEnvelope (a+l*(site i).1) l 6 x' * lineEnvelope (b+W*(site i).2) W 6 y') ≤
      (64 * lineEnvelope x' l 3 x * lineEnvelope y' W 3 y) *
      (lineEnvelope (a+l*(site i).1) l 3 x * lineEnvelope (b+W*(site i).2) W 3 y) := by
    have hx := envelope_six_product (a+l*(site i).1) l x x'
    have hy := envelope_six_product (b+W*(site i).2) W y y'
    have h := mul_le_mul hx hy
      (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
      (mul_nonneg (mul_nonneg (by norm_num) (lineEnvelope_nonneg _ _ _ _)) (lineEnvelope_nonneg _ _ _ _))
    first | (convert h using 1 <;> ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))
  calc
    _ ≤ ∑ i, (64 * lineEnvelope x' l 3 x * lineEnvelope y' W 3 y) *
        (lineEnvelope (a+l*(site i).1) l 3 x * lineEnvelope (b+W*(site i).2) W 3 y) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = (64 * lineEnvelope x' l 3 x * lineEnvelope y' W 3 y) *
        ∑ i, lineEnvelope (a+l*(site i).1) l 3 x * lineEnvelope (b+W*(site i).2) W 3 y :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (64 * lineEnvelope x' l 3 x * lineEnvelope y' W 3 y) * (4*Real.pi)^2 :=
      mul_le_mul_of_nonneg_left (injective_tile_lattice_overlap site hinj a b l W x y
        hl.ne' hW.ne' (by decide : 1 ≤ 3) (by decide : 1 ≤ 3))
        (mul_nonneg (mul_nonneg (by norm_num) (lineEnvelope_nonneg _ _ _ _))
          (lineEnvelope_nonneg _ _ _ _))
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlanarPositiveConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive planar kernel in coordinates (x,Y), and its exact
factorization into the two line convolutions used for concentration. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert

theorem planarPositiveConvolution_integrable (l W : ℝ) (f : ℝ × ℝ → ℝ)
    (hf : Measurable f) (hl : 0 < l) (hW : 0 < W) {C : ℝ}
    (hbound : ∀ z, ‖f z‖ ≤ C) (x y : ℝ) :
    Integrable (fun z : ℝ × ℝ => (lineKernel l (x-z.1) * lineKernel W (y-z.2)) * f z) := by
  have hx : Integrable (fun s => lineKernel l (x-s)) := by
    simp_rw [lineKernel_sub_comm l x]
    exact lineKernel_integrable l x hl
  have hy : Integrable (fun s => lineKernel W (y-s)) := by
    simp_rw [lineKernel_sub_comm W y]
    exact lineKernel_integrable W y hW
  exact (hx.mul_prod hy).mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_TileEnvelopeKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-point lattice overlap after normalization by tile area. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem tileEnvelope_nonneg (a b l W : ℝ) (n : ℕ) (z : ℝ × ℝ) :
    0 ≤ tileEnvelope a b l W n z :=
  mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)

theorem tileEnvelope_integrable (a b l W : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (hl : 0 < l) (hW : 0 < W) : Integrable (tileEnvelope a b l W n) :=
  (integrable_lineEnvelope a l hl hn).mul_prod (integrable_lineEnvelope b W hW hn)

theorem two_point_tile_kernel {ι : Type*} [Fintype ι]
    (site : ι → ℤ × ℤ) (hinj : Function.Injective site)
    (a b l W : ℝ) (hl : 0 < l) (hW : 0 < W) (z z' : ℝ × ℝ) :
    (∑ i, tileEnvelope (a+l*(site i).1) (b+W*(site i).2) l W 6 z *
      tileEnvelope (a+l*(site i).1) (b+W*(site i).2) l W 6 z') / (l*W) ≤
    (64 * (4*Real.pi)^2) * (lineKernel l (z.1-z'.1) * lineKernel W (z.2-z'.2)) := by
  have h := div_le_div_of_nonneg_right
    (two_point_tile_envelope site hinj a b l W z.1 z.2 z'.1 z'.2 hl hW)
    (mul_nonneg hl.le hW.le)
  convert h using 1
  all_goals first | rfl | (rw [lineKernel_shift, lineKernel_shift]; ring)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LatticeCoefficientConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual analyzing coefficients controlled by a common scalar source
satisfy the fixed-scale positive convolution estimate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace LipschitzHilbert

theorem lattice_coefficient_convolution {ι κ : Type*} [Fintype ι] [Fintype κ]
    (site : ι → ℤ × ℤ) (hinj : Function.Injective site) (a b l W : ℝ)
    (hl : 0 < l) (hW : 0 < W) (f : ℝ × ℝ → ℝ) (hf : Measurable f)
    (hf0 : ∀ z, 0 ≤ f z) {M : ℝ} (hfb : ∀ z, ‖f z‖ ≤ M)
    (wave : ι → κ → ℝ × ℝ → ℂ) (hw : ∀ i k, Measurable (wave i k))
    (hwf : ∀ i k z, ‖wave i k z‖ ≤
      tileEnvelope (a+l*(site i).1) (b+W*(site i).2) l W 6 z * f z)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (z : ℝ × ℝ) :
    (∑ i, ‖analyzingCoefficient volume (fun _ : ι => l*W) wave g i‖ *
      tileEnvelope (a+l*(site i).1) (b+W*(site i).2) l W 6 z) ≤
      (64 * (4*Real.pi)^2) * planarPositiveConvolution l W f z.1 z.2 := by
  let E := fun i => tileEnvelope (a+l*(site i).1) (b+W*(site i).2) l W 6
  have hEi (i : ι) : Integrable (fun p => E i p * f p) :=
    (tileEnvelope_integrable _ _ _ _ (by decide : 1 ≤ 6) hl hW).mul_bdd
      hf.aestronglyMeasurable (Filter.Eventually.of_forall hfb)
  have hEn (i : ι) (p : ℝ × ℝ) : 0 ≤ E i p := tileEnvelope_nonneg _ _ _ _ _ _
  have hint (i : ι) (k : κ) : Integrable (fun p => g p k * conj (wave i k p)) := by
    have hgm : Measurable (fun p => g p k) :=
      (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
    apply (hEi i).mono' (hgm.mul (continuous_star.measurable.comp (hw i k))).aestronglyMeasurable
    filter_upwards [] with p
    dsimp only [Pi.mul_apply, Function.comp_apply]
    rw [norm_mul, norm_star]
    have hgk := (PiLp.norm_apply_le (g p) k).trans (hg1 p)
    exact (mul_le_mul_of_nonneg_right hgk (norm_nonneg _)).trans
      (by simpa only [one_mul] using hwf i k p)
  have ha (i : ι) : ‖analyzingCoefficient volume (fun _ : ι => l*W) wave g i‖ ≤
      (l*W)⁻¹ * ∫ p, E i p * f p :=
    analyzingCoefficient_norm_le volume (fun _ : ι => l*W) wave g i (fun p => E i p * f p)
      (mul_pos hl hW) (hEi i) (fun p => mul_nonneg (hEn i p) (hf0 p))
      (hint i) hg1 (hwf i)
  have hsumI : Integrable (fun p => ∑ i, (E i z * E i p / (l*W)) * f p) := by
    apply integrable_finsetSum
    intro i _
    convert (hEi i).const_mul (E i z / (l*W)) using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    ring
  have hkerI := planarPositiveConvolution_integrable l W f hf hl hW hfb z.1 z.2
  calc
    _ ≤ ∑ i, ((l*W)⁻¹ * ∫ p, E i p * f p) * E i z :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (ha i) (hEn i z))
    _ = ∫ p, ∑ i, (E i z * E i p / (l*W)) * f p := by
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro i _
        have heq : (fun p => (E i z * E i p / (l*W)) * f p) =
            (fun p => (E i z / (l*W)) * (E i p * f p)) := by funext p; ring
        rw [heq, integral_const_mul]
        ring
      · intro i _
        convert (hEi i).const_mul (E i z / (l*W)) using 1
        all_goals try with_reducible_and_instances rfl
        funext p
        ring
    _ ≤ ∫ p, (64*(4*Real.pi)^2) *
        ((lineKernel l (z.1-p.1) * lineKernel W (z.2-p.2)) * f p) := by
      apply integral_mono hsumI (hkerI.const_mul _)
      intro p
      have h := mul_le_mul_of_nonneg_right
        (two_point_tile_kernel site hinj a b l W hl hW z p) (hf0 p)
      convert h using 1
      · simp only [Finset.sum_mul, Finset.sum_div]
        rfl
      · ring
    _ = _ := integral_const_mul _ _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CoefficientDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual coefficient decomposes exactly into its frozen main part
and the angular error whose positive majorant was proved above. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace LipschitzHilbert

theorem analyzingCoefficient_sub {Ω σ κ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (area : σ → ℝ) (f h : σ → κ → Ω → ℂ)
    (g : Ω → EuclideanSpace ℂ κ)
    (hf : ∀ i k, Integrable (fun z => g z k * conj (f i k z)) μ)
    (hh : ∀ i k, Integrable (fun z => g z k * conj (h i k z)) μ) (i : σ) :
    analyzingCoefficient μ area (fun i k z => f i k z-h i k z) g i =
      analyzingCoefficient μ area f g i - analyzingCoefficient μ area h g i := by
  ext k
  change ((area i)⁻¹ : ℂ) * (∫ z, g z k * conj (f i k z-h i k z) ∂μ) =
    ((area i)⁻¹ : ℂ) * (∫ z, g z k * conj (f i k z) ∂μ) -
      ((area i)⁻¹ : ℂ) * (∫ z, g z k * conj (h i k z) ∂μ)
  simp only [map_sub, mul_sub]
  rw [integral_sub (hf i k) (hh i k)]
  ring

theorem angularErrorWave_eq_sub {ι κ : Type*} (b : ι → κ → ℝ → ℂ)
    (ψ : ι → κ → ℝ × ℝ → ℂ) (u : ℝ × ℝ → ℝ) (t d : ℝ)
    (i : ι) (k : κ) (z : ℝ × ℝ) :
    angularErrorWave b ψ u t d i k z =
      b i k (u z) * ψ i k z - (if |u z-t| ≤ d then b i k t * ψ i k z else 0) := by
  unfold angularErrorWave multiplierError
  split_ifs <;> ring

theorem angularCoefficient_decomposition {ι κ : Type*}
    (area : ι → ℝ) (b : ι → κ → ℝ → ℂ) (ψ : ι → κ → ℝ × ℝ → ℂ)
    (u : ℝ × ℝ → ℝ) (t d : ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ)
    (hOriginal : ∀ i k, Integrable (fun z => g z k * conj (b i k (u z) * ψ i k z)))
    (hMain : ∀ i k, Integrable (fun z => g z k *
      conj (if |u z-t| ≤ d then b i k t * ψ i k z else 0))) (i : ι) :
    analyzingCoefficient volume area (fun i k z => b i k (u z)*ψ i k z) g i =
      analyzingCoefficient volume area (fun i k z =>
        if |u z-t| ≤ d then b i k t*ψ i k z else 0) g i +
      analyzingCoefficient volume area (angularErrorWave b ψ u t d) g i := by
  have heq : angularErrorWave b ψ u t d = (fun i k z =>
      b i k (u z)*ψ i k z - (if |u z-t| ≤ d then b i k t*ψ i k z else 0)) := by
    funext i k z
    exact angularErrorWave_eq_sub b ψ u t d i k z
  rw [heq, analyzingCoefficient_sub volume area _ _ g hOriginal hMain]
  abel

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rounded dyadic parameters in the manuscript. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert.SourceParameters

theorem log_step_bounds {L : ℝ} (hL : 0 ≤ L) :
    L ^ (7 / 10 : ℝ) ≤ Real.log (step L) ∧
      Real.log (step L) ≤ L ^ (7 / 10 : ℝ) + 2 * Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr : 0 ≤ L ^ (7 / 10 : ℝ) / (2 * Real.log 2) := by positivity
  have hlo := Nat.le_ceil (L ^ (7 / 10 : ℝ) / (2 * Real.log 2))
  have hhi := (Nat.ceil_lt_add_one hr).le
  rw [step, Real.log_pow, stepExponent, Nat.cast_mul, Nat.cast_ofNat]
  constructor
  · have h := mul_le_mul_of_nonneg_right hlo (show 0 ≤ 2 * Real.log 2 by positivity)
    have heq : L ^ (7 / 10 : ℝ) / (2 * Real.log 2) * (2 * Real.log 2) =
        L ^ (7 / 10 : ℝ) := div_mul_cancel₀ _ (by positivity)
    rw [heq] at h
    nlinarith
  · have h := mul_le_mul_of_nonneg_right hhi (show 0 ≤ 2 * Real.log 2 by positivity)
    have heq : (L ^ (7 / 10 : ℝ) / (2 * Real.log 2) + 1) * (2 * Real.log 2) =
        L ^ (7 / 10 : ℝ) + 2 * Real.log 2 := by
      rw [add_mul, div_mul_cancel₀ _ (by positivity), one_mul]
    rw [heq] at h
    nlinarith

theorem log_branching_le {L : ℝ} (hL : 0 ≤ L) :
    Real.log (branching L) ≤
      (Real.log L ^ 2 + 1) * (L ^ (7 / 10 : ℝ) + 2 * Real.log 2) := by
  rw [branching, Real.log_pow]
  have hK : (blockCount L : ℝ) ≤ Real.log L ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (sq_nonneg (Real.log L))).le
  exact mul_le_mul hK (log_step_bounds hL).2
    (Real.log_nonneg (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))) (by positivity)

/-- The actual rounded dyadic branching satisfies the scale separation
`B^100 ≤ exp(L^0.9)` eventually, with no real-valued stand-in for `B`. -/
theorem eventually_branching_separation :
    ∀ᶠ L : ℝ in atTop, branching L ^ 100 ≤ Real.exp (L ^ (9 / 10 : ℝ)) := by
  have hlog := isLittleO_log_rpow_rpow_atTop (r := 2) (s := 1 / 5) (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)).eventually_ge_atTop (2 * Real.log 2),
    hlog.bound (by norm_num : (0 : ℝ) < 1 / 400)] with L hL hlogL hpow hsmall
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hp7 : 0 ≤ L ^ (7 / 10 : ℝ) := Real.rpow_nonneg hL0.le _
  have hp2 : 0 ≤ L ^ (1 / 5 : ℝ) := Real.rpow_nonneg hL0.le _
  have hlogsq : 1 ≤ Real.log L ^ 2 := by nlinarith
  rw [Real.rpow_two] at hsmall
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log L)),
    abs_of_nonneg hp2] at hsmall
  have hcrude : Real.log (branching L) ≤ 4 * L ^ (7 / 10 : ℝ) * Real.log L ^ 2 := by
    apply (log_branching_le hL0.le).trans
    nlinarith [mul_le_mul (show Real.log L ^ 2 + 1 ≤ 2 * Real.log L ^ 2 by linarith)
      (show L ^ (7 / 10 : ℝ) + 2 * Real.log 2 ≤ 2 * L ^ (7 / 10 : ℝ) by linarith)
      (by positivity : 0 ≤ L ^ (7 / 10 : ℝ) + 2 * Real.log 2)
      (by positivity : 0 ≤ 2 * Real.log L ^ 2)]
  have hpower : L ^ (7 / 10 : ℝ) * L ^ (1 / 5 : ℝ) = L ^ (9 / 10 : ℝ) := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hbound : 100 * Real.log (branching L) ≤ L ^ (9 / 10 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hsmall (mul_nonneg (by norm_num : (0 : ℝ) ≤ 400) hp7)
    nlinarith
  calc
    branching L ^ 100 = Real.exp (100 * Real.log (branching L)) := by
      have heq : Real.log (branching L ^ (100 : ℕ)) = (100 : ℝ) * Real.log (branching L) := by
        simpa only [Nat.cast_ofNat] using (Real.log_pow (branching L) 100)
      rw [← heq, Real.exp_log (pow_pos (branching_pos L) _)]
    _ ≤ Real.exp (L ^ (9 / 10 : ℝ)) := Real.exp_le_exp.mpr hbound

end LipschitzHilbert.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ErrorSourceBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construction of the line error data from the manuscript's actual
two-coordinate direction profile and common vertical averaging kernel. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem source_branching_eq_two_pow (L : ℝ) :
    SourceParameters.branching L =
      (2 : ℝ)^(SourceParameters.stepExponent L * SourceParameters.blockCount L) := by
  simp only [SourceParameters.branching, SourceParameters.step, pow_mul]

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

theorem weight_pos (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) (z : ℝ × ℝ) :
    0 < T.weight K D z := by
  unfold weight
  have hr := T.radius_nonnegative z
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) D)
    (Real.rpow_pos_of_pos (by positivity) _)

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translated nested angular grids and their actual eligible-top masses. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

namespace AngularGrid

theorem index_parent (g : AngularGrid) (level : ℕ) (slope : ℝ) :
    g.index (level + 1) slope / (g.branching : ℤ) = g.index level slope := by
  have hG : g.branching ≠ 0 := by have h := g.branching_ge_two; omega
  simpa only [index, pow_succ, mul_assoc] using
    (Int.mul_natCast_floor_div_cancel hG
      (((slope - g.origin) / g.rootWidth) * (g.branching : ℝ) ^ level))

variable {ι X : Type*}

theorem cellTops_subset_parent (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    (level : ℕ) (child : ℤ) :
    g.cellTops tops slope precision cutoff (level + 1) child ⊆
      g.cellTops tops slope precision cutoff level (child / (g.branching : ℤ)) := by
  intro i hi
  obtain ⟨hit, hindex, heligible⟩ := (g.mem_cellTops _ _ _ _ _ _ _).1 hi
  apply (g.mem_cellTops _ _ _ _ _ _ _).2
  refine ⟨hit, ?_, g.eligible_parent (hp i hit) level heligible⟩
  rw [← g.index_parent level (slope i), hindex]

theorem mass_pos_of_member (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 < weight i x)
    (level : ℕ) (cell : ℤ) (x : X) {i : ι}
    (hi : i ∈ g.cellTops tops slope precision cutoff level cell) :
    0 < g.mass tops slope precision cutoff weight level cell x := by
  classical
  exact (hw i x).trans_le (Finset.single_le_sum (fun j _ => (hw j x).le) hi)

/-- An eligible top supplies a strictly positive summand on its own path. -/
theorem path_mass_pos (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 < weight i x)
    (level : ℕ) (top : ι) (htop : top ∈ tops) (heligible : g.eligible cutoff (precision top) level)
    (x : X) : 0 < g.mass tops slope precision cutoff weight level (g.index level (slope top)) x :=
  g.mass_pos_of_member tops slope precision cutoff weight hw level _ x
    ((g.mem_cellTops _ _ _ _ _ _ _).2 ⟨htop, rfl, heligible⟩)

/-- Child mass is at most parent mass, with the eligibility restriction
already built into both finite sums. -/
theorem mass_le_parent (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    (hw : ∀ i x, 0 ≤ weight i x) (level : ℕ) (child : ℤ) (x : X) :
    g.mass tops slope precision cutoff weight (level + 1) child x ≤
      g.mass tops slope precision cutoff weight level (child / (g.branching : ℤ)) x := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (g.cellTops_subset_parent tops slope precision cutoff hp level child) (fun i _ _ => hw i x)

end AngularGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric separation in the actual translated angular grid. -/

noncomputable section

namespace LipschitzHilbert.AngularGrid

/-- The floor assignment is exactly the half-open translated interval. -/
theorem slope_mem_cell (g : AngularGrid) (level : ℕ) (slope : ℝ) :
    g.left level (g.index level slope) ≤ slope ∧
      slope < g.left level (g.index level slope) + g.width level := by
  let a := ((slope - g.origin) / g.rootWidth) * (g.branching : ℝ) ^ level
  have hlow := Int.floor_le a
  have hhigh := Int.lt_floor_add_one a
  have heq : g.width level * a = slope - g.origin := by
    unfold width a
    have hG : (g.branching : ℝ) ≠ 0 := by
      exact_mod_cast (show g.branching ≠ 0 by have h := g.branching_ge_two; omega)
    field_simp [g.rootWidth_pos.ne', pow_ne_zero level hG]
  have hlow' := mul_le_mul_of_nonneg_left hlow (g.width_pos level).le
  have hhigh' := mul_lt_mul_of_pos_left hhigh (g.width_pos level)
  rw [heq] at hlow' hhigh'
  change g.origin + g.width level * (⌊a⌋ : ℝ) ≤ slope ∧
    slope < g.origin + g.width level * (⌊a⌋ : ℝ) + g.width level
  constructor <;> nlinarith

theorem same_cell_diameter (g : AngularGrid) (level : ℕ) {s t : ℝ}
    (hcell : g.index level s = g.index level t) : |s - t| ≤ g.width level := by
  obtain ⟨hs0, hs1⟩ := g.slope_mem_cell level s
  obtain ⟨ht0, ht1⟩ := g.slope_mem_cell level t
  rw [hcell] at hs0 hs1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem eligible_iff_precision_le (g : AngularGrid) (cutoff precision : ℝ) (level : ℕ) :
    g.eligible cutoff precision level ↔ precision ≤ cutoff / (g.branching : ℝ) ^ level := by
  have hG : (0 : ℝ) < g.branching := by
    exact_mod_cast (show 0 < g.branching by have h := g.branching_ge_two; omega)
  exact (le_div_iff₀ (pow_pos hG level)).symm

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary masses formed from actual top sets in a common angular ancestor. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.AngularGrid

variable {ι X : Type*}

attribute [local instance] Classical.propDecidable

theorem index_eq_of_add (g : AngularGrid) (base steps : ℕ) {s t : ℝ}
    (h : g.index (base + steps) s = g.index (base + steps) t) :
    g.index base s = g.index base t := by
  induction steps with
  | zero => simpa using h
  | succ steps ih =>
    apply ih
    rw [← g.index_parent (base + steps) s, ← g.index_parent (base + steps) t]
    simpa only [Nat.add_succ] using congrArg (fun a : ℤ => a / g.branching) h

theorem index_eq_of_le (g : AngularGrid) {base level : ℕ} (hle : base ≤ level)
    {s t : ℝ} (h : g.index level s = g.index level t) :
    g.index base s = g.index base t := by
  obtain ⟨steps, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact g.index_eq_of_add base steps h

/-- Tops in a descendant cell remain eligible and lie in its actual ancestor. -/
theorem cellTops_subset_ancestor (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    {base level : ℕ} (hle : base ≤ level) (s : ℝ) :
    g.cellTops tops slope precision cutoff level (g.index level s) ⊆
      g.cellTops tops slope precision cutoff base (g.index base s) := by
  intro i hi
  obtain ⟨hit, hindex, he⟩ := (g.mem_cellTops _ _ _ _ _ _ _).1 hi
  exact (g.mem_cellTops _ _ _ _ _ _ _).2
    ⟨hit, g.index_eq_of_le hle hindex, g.eligible_of_le (hp i hit) hle he⟩

theorem parent_subset_boundary (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (base level : ℕ) (gap s : ℝ) :
    g.cellTops tops slope precision cutoff level (g.index level s) ⊆
      g.boundaryTops tops slope precision cutoff base level gap s := by
  classical
  exact Finset.subset_union_left

theorem boundary_subset_ancestor (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    {base level : ℕ} (hle : base ≤ level) (gap s : ℝ) :
    g.boundaryTops tops slope precision cutoff base level gap s ⊆
      g.cellTops tops slope precision cutoff base (g.index base s) := by
  classical
  apply Finset.union_subset
  · exact g.cellTops_subset_ancestor tops slope precision cutoff hp hle s
  · exact Finset.filter_subset _ _

/-- The immediate child, parent, boundary and block ancestor have ordered masses. -/
theorem boundary_mass_bounds (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 ≤ weight i x)
    {base level : ℕ} (hle : base ≤ level) (gap s : ℝ) (x : X) :
    g.mass tops slope precision cutoff weight (level + 1) (g.index (level + 1) s) x ≤
        g.mass tops slope precision cutoff weight level (g.index level s) x ∧
    g.mass tops slope precision cutoff weight level (g.index level s) x ≤
        g.boundaryMass tops slope precision cutoff weight base level gap s x ∧
    g.boundaryMass tops slope precision cutoff weight base level gap s x ≤
        g.mass tops slope precision cutoff weight base (g.index base s) x := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · have h := g.mass_le_parent tops slope precision cutoff weight hp hw level
      (g.index (level + 1) s) x
    simpa only [g.index_parent] using h
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (g.parent_subset_boundary tops slope precision cutoff base level gap s)
      (fun i _ _ => hw i x)
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (g.boundary_subset_ancestor tops slope precision cutoff hp hle gap s)
      (fun i _ _ => hw i x)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularAnalyticWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic transition weights for the shared angular packet family.
The exact modulus is the child-to-boundary mass ratio raised to the
real part of the corresponding complex parameter. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

theorem analyticTransition_norm (mass boundary : ℕ → ℤ → ℝ) (phase : ℕ → ℂ)
    (level : ℕ) (cell : ℤ) (hm : 0 < mass (level + 1) cell) (hb : 0 < boundary level cell) :
    ‖analyticTransition mass boundary phase level cell‖ =
      (mass (level + 1) cell / boundary level cell) ^ (phase level).re := by
  rw [analyticTransition, Complex.norm_exp, Real.rpow_def_of_pos (div_pos hm hb)]
  congr 1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

theorem analyticTransition_norm_le_one (mass boundary : ℕ → ℤ → ℝ) (phase : ℕ → ℂ)
    (level : ℕ) (cell : ℤ) (hm : 0 < mass (level + 1) cell) (hb : 0 < boundary level cell)
    (hle : mass (level + 1) cell ≤ boundary level cell) (hphase : 0 ≤ (phase level).re) :
    ‖analyticTransition mass boundary phase level cell‖ ≤ 1 := by
  rw [analyticTransition_norm mass boundary phase level cell hm hb]
  exact Real.rpow_le_one (div_nonneg hm.le hb.le) ((div_le_one hb).mpr hle) hphase

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShiftedBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual shifted block endpoints of §8. The first block is allowed
to be shorter. Every transition has one phase tag, and each completed
block contains its distinguished phase exactly at the last transition. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert.ShiftedBlocks

variable {K : ℕ}

theorem endpoint_first_bounds (σ : Fin K) : 1 ≤ endpoint σ 1 ∧ endpoint σ 1 ≤ K := by
  simp only [endpoint_succ, Nat.zero_mul, Nat.add_zero]
  have hs := σ.isLt
  omega

theorem endpoint_step (σ : Fin K) (j : ℕ) :
    endpoint σ (j + 2) = endpoint σ (j + 1) + K := by
  simp only [show j + 2 = (j + 1) + 1 by omega, endpoint_succ, Nat.add_mul, Nat.one_mul]
  omega

theorem endpoint_width_le (σ : Fin K) (j : ℕ) :
    endpoint σ (j + 1) ≤ endpoint σ j + K := by
  cases j with
  | zero => simpa using (endpoint_first_bounds σ).2
  | succ j => exact le_of_eq (endpoint_step σ j)

end LipschitzHilbert.ShiftedBlocks

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopMaskApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript mask at its actual scale. Inside the prescribed
near region its error is at most a fixed constant times L^(1-A). -/

noncomputable section

namespace LipschitzHilbert

theorem topSincMask_nonneg (L A x y : ℝ) : 0 ≤ topSincMask L A x y :=
  sincProductMask_nonneg _ _ _

theorem topSincMask_le_one (L A x y : ℝ) : topSincMask L A x y ≤ 1 :=
  sincProductMask_le_one _ _ _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSlopeLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The slope-label multiplicity assumption in §2 of the manuscript
gives a uniform number of labels active at a fixed source direction.
This includes vector-valued selectors: taking the union over all bin
components does not increase the count.  The last lemmas split the
active labels at every scale into a fixed finite set of lattice slots. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.SourceSlopeLabels

attribute [local instance] Classical.propDecidable

variable {ι : Type*}

theorem window_card_le (labels : Finset ι) (slope : ι → ℝ)
    {t d radius : ℝ} {M K : ℕ} (hd : 0 < d)
    (hlocal : LocalMultiplicity labels slope d M) (hK : radius ≤ K) :
    (window labels slope t d radius).card ≤ (2 * K + 1) * M := by
  classical
  let active := window labels slope t d radius
  let bin : ι → ℤ := fun i => ⌊(slope i - t) / d⌋
  let bins : Finset ℤ := Finset.Icc (-(K : ℤ)) K
  have hmaps : (active : Set ι).MapsTo bin bins := by
    intro i hi
    have hwin : |slope i - t| ≤ radius * d := (Finset.mem_filter.mp hi).2
    have habs : |slope i - t| ≤ (K : ℝ) * d :=
      hwin.trans (mul_le_mul_of_nonneg_right hK hd.le)
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    have hlow : -(K : ℝ) ≤ (slope i - t) / d := by
      apply (le_div_iff₀ hd).mpr
      linarith
    have hupp : (slope i - t) / d < (K : ℝ) + 1 := by
      apply (div_lt_iff₀ hd).mpr
      nlinarith
    exact Finset.mem_Icc.mpr ⟨Int.le_floor.mpr (by simpa using hlow),
      Int.floor_le_iff.mpr (by simpa using hupp)⟩
  have hfiber (b : ℤ) : (active.filter (fun i => bin i = b)).card ≤ M := by
    apply (Finset.card_le_card (show active.filter (fun i => bin i = b) ⊆
      labels.filter (fun i => t + (b : ℝ) * d ≤ slope i ∧
        slope i < (t + (b : ℝ) * d) + d) from ?_)).trans
      (hlocal (t + (b : ℝ) * d))
    intro i hi
    obtain ⟨hia, hib⟩ := Finset.mem_filter.mp hi
    have hil : i ∈ labels := (Finset.mem_filter.mp hia).1
    have h0 := Int.floor_le ((slope i - t) / d)
    have h1 := Int.lt_floor_add_one ((slope i - t) / d)
    change ⌊(slope i - t) / d⌋ = b at hib
    rw [hib] at h0 h1
    have h0' := (le_div_iff₀ hd).mp h0
    have h1' := (div_lt_iff₀ hd).mp h1
    exact Finset.mem_filter.mpr ⟨hil, by constructor <;> nlinarith⟩
  have hcount : bins.card = 2 * K + 1 := by
    have hcount' : (bins.card : ℤ) = 2 * (K : ℤ) + 1 := by
      dsimp [bins]
      rw [Int.card_Icc_of_le (a := -(K : ℤ)) (b := (K : ℤ)) (by omega)]
      omega
    exact_mod_cast hcount'
  calc
    active.card = ∑ b ∈ bins, (active.filter (fun i => bin i = b)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _b ∈ bins, M := Finset.sum_le_sum fun b _ => hfiber b
    _ = (2 * K + 1) * M := by simp [hcount]

theorem active_card_le (labels : Finset ι) (slope : ι → ℝ)
    {κ : Type*} (selector : ι → κ → ℝ → ℂ)
    {t d radius : ℝ} {M K : ℕ} (hd : 0 < d)
    (hlocal : LocalMultiplicity labels slope d M) (hK : radius ≤ K)
    (hsupport : ∀ i ∈ labels, ∀ k, selector i k t ≠ 0 →
      |t - slope i| ≤ radius * d) :
    (active labels selector t).card ≤ (2 * K + 1) * M := by
  classical
  apply (Finset.card_le_card (show active labels selector t ⊆
    window labels slope t d radius from ?_)).trans
    (window_card_le labels slope hd hlocal hK)
  intro i hi
  obtain ⟨hil, k, hk⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hil, by simpa only [abs_sub_comm] using hsupport i hil k hk⟩

end LipschitzHilbert.SourceSlopeLabels

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketLatticeData
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite packet family before choosing a reference direction.
There is no small-shear condition on its slopes. That condition is proved
only for the labels retained in a short reference cone. -/
noncomputable section
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

variable (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone * w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F / w)

local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

theorem referenceFamily_actualZ (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).actualZ j l u = P.actualZ j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u +
      (oldSlope - newSlope) * P.actualX j
        (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := by
  dsimp [SourceLabeledLattice.actualZ, actualZ, actualX, referenceFamily,
    SourceLabeledLattice.length, length]
  ring

theorem referenceFamily_physicalPacket (j : Fin N) (l : (Q).labels j)
    (u : Item j l) (k : κ) :
    (Q).physicalPacket newSlope j l u k = P.physicalPacket oldSlope j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u k := by
  let l₀ := P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l
  have hx := P.referenceFamily_actualX oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency j l u
  have hz := P.referenceFamily_actualZ oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency j l u
  unfold SourceLabeledLattice.physicalPacket physicalPacket
  rw [hx, hz]
  have hc : P.actualZ j l₀ u + (oldSlope - newSlope) * P.actualX j l₀ u +
      newSlope * P.actualX j l₀ u = P.actualZ j l₀ u + oldSlope * P.actualX j l₀ u := by ring
  have hs : newSlope + (P.rowSlope j l₀ + (oldSlope - newSlope)) =
      oldSlope + P.rowSlope j l₀ := by ring
  change physicalPlanarPacket (P.profile j l₀ u k) _ _ (P.length j) P.width
    (newSlope + (P.rowSlope j l₀ + (oldSlope - newSlope))) (P.frequency k) _ _ = _
  rw [hc, hs]

end PacketLatticeData
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSingleScaleEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The single-scale estimate in §5, `conc:original-positive`.
The lattice estimate is summed at the source point before integrating.
Only pointwise overlap of the label multipliers appears, so the estimate
has no factor counting the available labels. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem planarPositiveConvolution_sum {Λ : Type*} [Fintype Λ]
    (f : Λ → ℝ×ℝ → ℝ) (hf : ∀ b, Measurable (f b))
    {l W B : ℝ} (hl : 0 < l) (hW : 0 < W)
    (hbound : ∀ b z, ‖f b z‖ ≤ B) (x y : ℝ) :
    planarPositiveConvolution l W (fun z => ∑ b, f b z) x y =
      ∑ b, planarPositiveConvolution l W (f b) x y := by
  unfold planarPositiveConvolution
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ (fun b _ =>
    planarPositiveConvolution_integrable l W (f b) (hf b) hl hW (hbound b) x y)

theorem planarPositiveConvolution_le {l W B : ℝ} (hl : 0 < l) (hW : 0 < W)
    (hB : 0 ≤ B) (f : ℝ×ℝ → ℝ) (hf : Measurable f)
    (hf0 : ∀ z, 0 ≤ f z) (hbound : ∀ z, f z ≤ B) (x y : ℝ) :
    planarPositiveConvolution l W f x y ≤ B*Real.pi^2 := by
  have hb (z : ℝ×ℝ) : ‖f z‖ ≤ B := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hf0 z)]
    exact hbound z
  have hx : Integrable (fun s => lineKernel l (x-s)) := by
    simp_rw [lineKernel_sub_comm l x]
    exact lineKernel_integrable l x hl
  have hy : Integrable (fun s => lineKernel W (y-s)) := by
    simp_rw [lineKernel_sub_comm W y]
    exact lineKernel_integrable W y hW
  have hkernel : (∫ z : ℝ×ℝ, lineKernel l (x-z.1)*lineKernel W (y-z.2)) ≤ Real.pi^2 := by
    rw [Measure.volume_eq_prod,integral_prod_mul (fun s : ℝ => lineKernel l (x-s))
      (fun s : ℝ => lineKernel W (y-s))]
    have hxle : (∫ s, lineKernel l (x-s)) ≤ Real.pi := by
      simpa only [lineKernel_sub_comm l x] using integral_lineKernel_le l x hl
    have hyle : (∫ s, lineKernel W (y-s)) ≤ Real.pi := by
      simpa only [lineKernel_sub_comm W y] using integral_lineKernel_le W y hW
    have hyn : 0 ≤ ∫ s, lineKernel W (y-s) := integral_nonneg (fun _ => lineKernel_nonneg _ _ hW)
    simpa only [pow_two] using mul_le_mul hxle hyle hyn Real.pi_pos.le
  calc
    _ ≤ ∫ z : ℝ×ℝ, (lineKernel l (x-z.1)*lineKernel W (y-z.2))*B := by
      apply integral_mono (planarPositiveConvolution_integrable l W f hf hl hW hb x y)
        ((hx.mul_prod hy).mul_const B)
      intro z
      exact mul_le_mul_of_nonneg_left (hbound z)
        (mul_nonneg (lineKernel_nonneg _ _ hl) (lineKernel_nonneg _ _ hW))
    _ = B*(∫ z : ℝ×ℝ, lineKernel l (x-z.1)*lineKernel W (y-z.2)) := by
      rw [integral_mul_const,mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hkernel hB

theorem sum_planarPositiveConvolution_le {Λ : Type*} [Fintype Λ]
    (f : Λ → ℝ×ℝ → ℝ) (hf : ∀ b, Measurable (f b))
    (hf0 : ∀ b z, 0 ≤ f b z) {l W B : ℝ}
    (hl : 0 < l) (hW : 0 < W) (hB : 0 ≤ B)
    (hoverlap : ∀ z, ∑ b, f b z ≤ B) (x y : ℝ) :
    (∑ b, planarPositiveConvolution l W (f b) x y) ≤ B*Real.pi^2 := by
  have hb (b : Λ) (z : ℝ×ℝ) : ‖f b z‖ ≤ B := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hf0 b z)]
    exact (Finset.single_le_sum (fun c _ => hf0 c z) (Finset.mem_univ b)).trans (hoverlap z)
  rw [← planarPositiveConvolution_sum f hf hl hW hb x y]
  exact planarPositiveConvolution_le hl hW hB _
    (Finset.measurable_sum _ (fun b _ => hf b))
    (fun z => Finset.sum_nonneg (fun b _ => hf0 b z)) hoverlap x y

/-- Each label may have its own translated lattice. They share the
physical scale, transverse width, source test, and pointwise overlap
budget. All analyzing coefficients are the actual integral coefficients. -/
theorem source_single_scale_envelope {Λ κ : Type*} [Fintype Λ] [Fintype κ]
    (ι : Λ → Type*) [∀ b, Fintype (ι b)]
    (site : ∀ b, ι b → ℤ×ℤ) (hinj : ∀ b, Function.Injective (site b))
    (originX originY : Λ → ℝ) {l W B : ℝ} (hl : 0 < l) (hW : 0 < W) (hB : 0 ≤ B)
    (source : Λ → ℝ×ℝ → ℝ) (hmeas : ∀ b, Measurable (source b))
    (hnonneg : ∀ b z, 0 ≤ source b z) (hoverlap : ∀ z, ∑ b, source b z ≤ B)
    (wave : ∀ b, ι b → κ → ℝ×ℝ → ℂ) (hwave : ∀ b i k, Measurable (wave b i k))
    (hbound : ∀ b i k z, ‖wave b i k z‖ ≤
      tileEnvelope (originX b+l*(site b i).1) (originY b+W*(site b i).2) l W 6 z*source b z)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (z : ℝ×ℝ) :
    (∑ b, ∑ i, ‖analyzingCoefficient volume (fun _ : ι b => l*W) (wave b) g i‖*
      tileEnvelope (originX b+l*(site b i).1) (originY b+W*(site b i).2) l W 6 z) ≤
        (64*(4*Real.pi)^2)*(B*Real.pi^2) := by
  have hb (b : Λ) (p : ℝ×ℝ) : ‖source b p‖ ≤ B := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hnonneg b p)]
    exact (Finset.single_le_sum (fun c _ => hnonneg c p) (Finset.mem_univ b)).trans (hoverlap p)
  calc
    _ ≤ ∑ b, (64*(4*Real.pi)^2)*planarPositiveConvolution l W (source b) z.1 z.2 := by
      apply Finset.sum_le_sum
      intro b _
      exact lattice_coefficient_convolution (site b) (hinj b) (originX b) (originY b) l W
        hl hW (source b) (hmeas b) (hnonneg b) (hb b) (wave b) (hwave b) (hbound b) g hg hg1 z
    _ = (64*(4*Real.pi)^2)*∑ b, planarPositiveConvolution l W (source b) z.1 z.2 :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_planarPositiveConvolution_le source hmeas hnonneg hl hW hB hoverlap z.1 z.2)
      (by positivity)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSelectorEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source selector support and local slope-label multiplicity
instantiate the pointwise overlap budget in the single-scale estimate.
The bound is uniform in the number of labels and Hilbert coordinates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem source_selector_single_scale {Λ κ : Type*} [Fintype Λ] [Fintype κ]
    (ι : Λ → Type*) [∀ b, Fintype (ι b)]
    (site : ∀ b, ι b → ℤ×ℤ) (hinj : ∀ b, Function.Injective (site b))
    (originX originY slope : Λ → ℝ) {l W d radius C M : ℝ} {K H : ℕ}
    (hl : 0 < l) (hW : 0 < W) (hd : 0 < d) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ slope d H)
    (hK : radius ≤ K)
    (selector : Λ → κ → ℝ → ℂ) (hselector : ∀ b k, Measurable (selector b k))
    (hselectorBound : ∀ b k s, ‖selector b k s‖ ≤ M)
    (hsupport : ∀ b k s, selector b k s ≠ 0 → |s-slope b| ≤ radius*d)
    (direction : ℝ×ℝ → ℝ) (hdirection : Measurable direction)
    (wave : ∀ b, ι b → κ → ℝ×ℝ → ℂ) (hwave : ∀ b i k, Measurable (wave b i k))
    (hwaveBound : ∀ b i k z, ‖wave b i k z‖ ≤
      C*tileEnvelope (originX b+l*(site b i).1) (originY b+W*(site b i).2) l W 6 z)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (z : ℝ×ℝ) :
    (∑ b, ∑ i, ‖analyzingCoefficient volume (fun _ : ι b => l*W)
      (fun i k p => selector b k (direction p)*wave b i k p) g i‖*
      tileEnvelope (originX b+l*(site b i).1) (originY b+W*(site b i).2) l W 6 z) ≤
        (64*(4*Real.pi)^2)*((C*M*((2*K+1)*H:ℕ))*Real.pi^2) := by
  let active := fun (b : Λ) (p : ℝ×ℝ) => ∃ k, selector b k (direction p) ≠ 0
  let source := fun (b : Λ) (p : ℝ×ℝ) => if active b p then C*M else 0
  have hsourceMeas (b : Λ) : Measurable (source b) := by
    have ha : MeasurableSet {p : ℝ×ℝ | active b p} := by
      have heq : {p : ℝ×ℝ | active b p} = ⋃ k : κ, {p | selector b k (direction p) ≠ 0} := by
        ext p
        simp only [Set.mem_ofPred_eq,Set.mem_iUnion,active]
      rw [heq]
      exact MeasurableSet.iUnion fun k =>
        (measurableSet_eq_fun ((hselector b k).comp hdirection) measurable_const).compl
    exact Measurable.ite ha measurable_const measurable_const
  have hsource0 (b : Λ) (p : ℝ×ℝ) : 0 ≤ source b p := by
    dsimp [source]
    split_ifs <;> positivity
  have hoverlap (p : ℝ×ℝ) : ∑ b, source b p ≤ C*M*((2*K+1)*H:ℕ) := by
    have hcard := SourceSlopeLabels.active_card_le Finset.univ slope selector
      (t := direction p) hd hlocal hK (fun b _ k => hsupport b k (direction p))
    have heq : (∑ b, source b p) =
        C*M*((SourceSlopeLabels.active Finset.univ selector (direction p)).card:ℝ) := by
      dsimp [source,SourceSlopeLabels.active]
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]
      congr 2
      congr 1
      ext b
      simp only [Finset.mem_filter,active]
    rw [heq]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (mul_nonneg hC hM)
  apply source_single_scale_envelope ι site hinj originX originY hl hW (by positivity)
    source hsourceMeas hsource0 hoverlap _ _ _ g hg hg1 z
  · intro b i k
    exact ((hselector b k).comp hdirection).mul (hwave b i k)
  · intro b i k p
    by_cases ha : active b p
    · have hm := mul_le_mul (hselectorBound b k (direction p)) (hwaveBound b i k p)
        (norm_nonneg _) hM
      rw [norm_mul]
      convert hm using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [source]
      rw [ite_eq_left ha]
      ring
    · have hz : selector b k (direction p) = 0 := by
        by_contra hk
        exact ha ⟨k,hk⟩
      simp only [hz,zero_mul,norm_zero,source,ite_eq_right ha,mul_zero,le_refl]

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledCoefficientSplit
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original labeled physical coefficient splits into its centered
frozen selector and angular error, without changing synthesis packets. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem physical_multiplier_analyzing_integrable (t : ℝ) (m : ℝ×ℝ → ℂ)
    (hm : Measurable m) (hm1 : ∀ z, ‖m z‖ ≤ 1)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (l : P.labels j) (u : Item j l) (k : κ) :
    Integrable (fun z => g z k*conj (m z*P.physicalPacket t j l u k z))
      (volume.prod volume) := by
  have hgm : Measurable (fun z => g z k) :=
    (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
  apply (P.physicalPacket t j l u k).integrable.norm.mono'
    (hgm.mul (continuous_star.measurable.comp
      (hm.mul (P.physicalPacket t j l u k).continuous.measurable))).aestronglyMeasurable
  filter_upwards [] with z
  change ‖g z k*conj (m z*P.physicalPacket t j l u k z)‖ ≤ ‖P.physicalPacket t j l u k z‖
  rw [norm_mul,Complex.norm_conj,norm_mul]
  have hgk : ‖g z k‖ ≤ 1 := (PiLp.norm_apply_le (g z) k).trans (hg1 z)
  calc
    _ ≤ 1*(1*‖P.physicalPacket t j l u k z‖) := mul_le_mul hgk
      (mul_le_mul_of_nonneg_right (hm1 z) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = _ := by ring

theorem physicalMultiplierCoefficient_split (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (l : P.labels j) (u : Item j l) :
    P.physicalMultiplierCoefficient t b v g j l u =
      P.physicalFrozenCenteredCoefficient t a b v g j l u+
        P.physicalAngularErrorCoefficient t a b v g j l u := by
  apply angularCoefficient_decomposition (fun _ : Item j l => P.length j*P.width)
    (fun _ k => b j l k) (fun u k => P.physicalPacket t j l u k) v t (a*(2:ℝ)^j.val) g
  · intro u k
    exact P.physical_multiplier_analyzing_integrable t (fun z => b j l k (v z))
      ((hb j l k).comp hv) (fun z => hb1 j l k (v z)) g hg hg1 j l u k
  · intro u k
    have hdist : Measurable (fun z => |v z-t|) := by
      simpa only [Real.norm_eq_abs] using (hv.sub_const t).norm
    have hm : Measurable (fun z : ℝ×ℝ =>
        if |v z-t| ≤ a*(2:ℝ)^j.val then b j l k t else 0) :=
      Measurable.ite (measurableSet_le hdist measurable_const)
        measurable_const measurable_const
    have hm1 (z : ℝ×ℝ) :
        ‖if |v z-t| ≤ a*(2:ℝ)^j.val then b j l k t else 0‖ ≤ 1 := by
      split_ifs
      · exact hb1 j l k t
      · simp only [norm_zero,zero_le_one]
    have h := P.physical_multiplier_analyzing_integrable t _ hm hm1 g hg hg1 j l u k
    simpa only [Measure.volume_eq_prod,ite_mul,zero_mul] using h

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCoefficient
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analyzing coefficients for unrestricted packet lattices and their
exact transport to the local reference lattice. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

variable (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0<w) (hcone : 0 ≤ cone) (hF : 0≤F) (hwide : cone*w≤P.width)
  (hfrequency : ∀ k, |P.frequency k|≤F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

theorem referenceFamily_multiplier_coefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).physicalMultiplierCoefficient newSlope
      (P.referenceSelector oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency b)
      v g j l u =
    P.physicalMultiplierCoefficient oldSlope b v g j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := by
  ext k
  simp only [SourceLabeledLattice.physicalMultiplierCoefficient,physicalMultiplierCoefficient,
    analyzingCoefficient,WithLp.ofLp_toLp]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  have hp := congrArg (fun f : SchwartzMap (ℝ×ℝ) ℂ => f z)
    (P.referenceFamily_physicalPacket oldSlope newSlope referenceLength cone w F
      hw hcone hF hwide hfrequency j l u k)
  dsimp only [referenceSelector]
  rw [hp]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledSynthesisEnvelope
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise norms of actual vector packets are controlled by the
same positive main and error envelopes used in the reference tails. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem positiveEnvelope_nonneg (j : Fin N) (l : P.labels j) (u : Item j l) (y x : ℝ) :
    0 ≤ P.positiveEnvelope j l u y x :=
  mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)

theorem tileEnvelope_le_positive (j : Fin N) (l : P.labels j) (u : Item j l) (y x : ℝ) :
    tileEnvelope (P.length j*(P.snappedSite j l u).1)
      (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 (x,y) ≤
        P.positiveEnvelope j l u y x :=
  mul_le_mul (lineEnvelope_antitone _ _ _ (by decide : 3 ≤ 6))
    (lineEnvelope_antitone _ _ _ (by decide : 2 ≤ 6))
    (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)

theorem raw_packet_value_norm (horder : 6 ≤ P.order) (i : Fin 3) (j : Fin N)
    (l : P.labels j) (u : Item j l) (c : EuclideanSpace ℂ κ) (y x : ℝ) :
    ‖P.rawPacketValue i j l u c y x‖ ≤
      P.absoluteConstant*(‖c‖*tileEnvelope (P.length j*(P.snappedSite j l u).1)
        (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 (x,y)) := by
  have h := diagonal_packet_norm c (fun k => P.raw i j l u k y x)
    (mul_nonneg P.absoluteConstant_pos.le (tileEnvelope_nonneg _ _ _ _ _ _))
    (fun k => P.raw_absolute_tileEnvelope horder i j l u k (x,y))
  exact h.trans_eq (by ring)

theorem raw_packet_value_split (horder : 6 ≤ P.order) (i : Fin 3) (j : Fin N)
    (l : P.labels j) (u : Item j l) (c main error : EuclideanSpace ℂ κ)
    (hsplit : c = main+error) (y x : ℝ) :
    ‖P.rawPacketValue i j l u c y x‖ ≤
      P.absoluteConstant*(‖error‖*tileEnvelope
        (P.length j*(P.snappedSite j l u).1) (P.width*(P.snappedSite j l u).2)
        (P.length j) P.width 6 (x,y)+‖main‖*P.positiveEnvelope j l u y x) := by
  apply (P.raw_packet_value_norm horder i j l u c y x).trans
  apply mul_le_mul_of_nonneg_left _ P.absoluteConstant_pos.le
  have hc : ‖c‖ ≤ ‖main‖+‖error‖ :=
    hsplit ▸ norm_add_le _ _
  calc
    _ ≤ (‖main‖+‖error‖)*tileEnvelope _ _ _ _ 6 (x,y) :=
      mul_le_mul_of_nonneg_right hc (tileEnvelope_nonneg _ _ _ _ _ _)
    _ ≤ _ := by
      have he := mul_le_mul_of_nonneg_left (P.tileEnvelope_le_positive j l u y x)
        (norm_nonneg main)
      nlinarith

/-- Every path-dependent packet subset is bounded by the one fixed
positive reference family. -/
theorem sum_raw_packet_values_split (horder : 6 ≤ P.order) (i : Fin 3) (j : Fin N)
    (c main error : ∀ l : P.labels j, Item j l → EuclideanSpace ℂ κ)
    (hsplit : ∀ l u, c l u = main l u+error l u)
    (Q : Finset (Σ l : P.labels j, Item j l)) (y x : ℝ) :
    (∑ q ∈ Q, ‖P.rawPacketValue i j q.1 q.2 (c q.1 q.2) y x‖) ≤
      P.absoluteConstant*((∑ l : P.labels j, ∑ u : Item j l,
        ‖error l u‖*tileEnvelope (P.length j*(P.snappedSite j l u).1)
          (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 (x,y))+
        ∑ l : P.labels j, ∑ u : Item j l, ‖main l u‖*P.positiveEnvelope j l u y x) := by
  classical
  calc
    _ ≤ ∑ q : (Σ l : P.labels j, Item j l), ‖P.rawPacketValue i j q.1 q.2 (c q.1 q.2) y x‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Q) (fun _ _ _ => norm_nonneg _)
    _ ≤ ∑ q : (Σ l : P.labels j, Item j l), P.absoluteConstant*(‖error q.1 q.2‖*tileEnvelope
        (P.length j*(P.snappedSite j q.1 q.2).1) (P.width*(P.snappedSite j q.1 q.2).2)
        (P.length j) P.width 6 (x,y)+‖main q.1 q.2‖*P.positiveEnvelope j q.1 q.2 y x) :=
      by
        apply Finset.sum_le_sum
        intro q _
        have h := P.raw_packet_value_split horder i j q.1 q.2
          (c q.1 q.2) (main q.1 q.2) (error q.1 q.2) (hsplit q.1 q.2) y x
        exact h
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_add_distrib]; simp only [Fintype.sum_sigma]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledPositiveSplit
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual source coefficient supplies the positive per-length
main/error bound for every residual subset, with original synthesis waves. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem physicalErrorScale_nonneg (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (y x : ℝ) :
    0 ≤ P.physicalErrorScale t a b v g j y x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (norm_nonneg _) (tileEnvelope_nonneg _ _ _ _ _ _)

theorem physicalMainScale_nonneg (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (y x : ℝ) :
    0 ≤ P.physicalMainScale t a b v g j y x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (norm_nonneg _) (P.positiveEnvelope_nonneg _ _ _ _ _)

theorem sum_physicalErrorScale (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (y x : ℝ) :
    (∑ j, P.physicalErrorScale t a b v g j y x) =
      P.physicalAngularError t a b v g (x,y+t*x) := by
  unfold physicalErrorScale physicalAngularError
  congr 1
  funext j
  have hy : y+t*x-t*x = y := by ring
  simp only [hy]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_ResidualBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Square summation of disjoint residual blocks

The finite deterministic estimates in §10 `res:block-square`: error
envelopes are summed in ℓ¹, main envelopes in ℓ², and each block contains
only a bounded number of lengths. Multiplicities of packets at one
length are already included in the corresponding envelope.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem sum_disjoint_blocks_le (I : ι → Finset κ)
    (hI : Pairwise (fun i j => Disjoint (I i) (I j)))
    (e : κ → ℝ) (he : ∀ k, 0 ≤ e k) :
    (∑ i, ∑ k ∈ I i, e k) ≤ ∑ k, e k := by
  classical
  have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) I :=
    fun i _ j _ hij => hI hij
  rw [← Finset.sum_biUnion hd]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun k _ _ => he k)

theorem error_blocks_square_sum_le (I : ι → Finset κ)
    (hI : Pairwise (fun i j => Disjoint (I i) (I j)))
    (e : κ → ℝ) (he : ∀ k, 0 ≤ e k) :
    (∑ i, (∑ k ∈ I i, e k) ^ 2) ≤ (∑ k, e k) ^ 2 := by
  have hs := sum_disjoint_blocks_le I hI e he
  have hsmall : 0 ≤ ∑ i, ∑ k ∈ I i, e k :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => he k
  have hlarge : 0 ≤ ∑ k, e k := Finset.sum_nonneg fun k _ => he k
  refine (Finset.sum_sq_le_sq_sum_of_nonneg
    (fun i _ => Finset.sum_nonneg fun k _ => he k)).trans ?_
  nlinarith

theorem main_blocks_square_sum_le (I : ι → Finset κ)
    (hI : Pairwise (fun i j => Disjoint (I i) (I j)))
    (a : κ → ℝ) {L : ℝ} (hL : 0 ≤ L) (hcard : ∀ i, ((I i).card : ℝ) ≤ L) :
    (∑ i, (∑ k ∈ I i, a k) ^ 2) ≤ L * ∑ k, (a k) ^ 2 := by
  have hblock (i : ι) : (∑ k ∈ I i, a k) ^ 2 ≤ L * ∑ k ∈ I i, (a k) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (I i) (fun _ => (1 : ℝ)) a
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hcard i) (Finset.sum_nonneg fun k _ => sq_nonneg (a k)))
  calc
    _ ≤ ∑ i, L * ∑ k ∈ I i, (a k) ^ 2 := Finset.sum_le_sum fun i _ => hblock i
    _ = L * ∑ i, ∑ k ∈ I i, (a k) ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ L * ∑ k, (a k) ^ 2 := mul_le_mul_of_nonneg_left
      (sum_disjoint_blocks_le I hI (fun k => (a k) ^ 2) (fun k => sq_nonneg (a k))) hL

/-- A residual block is controlled by its error and main envelopes and
a final-block remainder. Their full square sum has no depth factor. -/
theorem residual_blocks_square_sum_le {E : Type*} [NormedAddCommGroup E]
    (I : ι → Finset κ) (hI : Pairwise (fun i j => Disjoint (I i) (I j)))
    (e a : κ → ℝ) (he : ∀ k, 0 ≤ e k) (ha : ∀ k, 0 ≤ a k)
    (B : ι → E) (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i)
    {C L R : ℝ} (_hC : 0 ≤ C) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hcard : ∀ i, ((I i).card : ℝ) ≤ L) (hremainder : ∑ i, r i ≤ R)
    (hbound : ∀ i, ‖B i‖ ≤ C * ((∑ k ∈ I i, e k) + ∑ k ∈ I i, a k) + r i) :
    (∑ i, ‖B i‖ ^ 2) ≤
      3 * C ^ 2 * ((∑ k, e k) ^ 2 + L * ∑ k, (a k) ^ 2) + 3 * R ^ 2 := by
  have hpoint (i : ι) : ‖B i‖ ^ 2 ≤
      3 * C ^ 2 * ((∑ k ∈ I i, e k) ^ 2 + (∑ k ∈ I i, a k) ^ 2) + 3 * (r i) ^ 2 := by
    have he0 : 0 ≤ ∑ k ∈ I i, e k := Finset.sum_nonneg fun k _ => he k
    have ha0 : 0 ≤ ∑ k ∈ I i, a k := Finset.sum_nonneg fun k _ => ha k
    have hb0 := norm_nonneg (B i)
    have hb := hbound i
    have hs : ‖B i‖ ^ 2 ≤ (C * ((∑ k ∈ I i, e k) + ∑ k ∈ I i, a k) + r i) ^ 2 := by
      nlinarith [mul_nonneg _hC (add_nonneg he0 ha0), hr i]
    nlinarith [sq_nonneg (C * (∑ k ∈ I i, e k) - C * (∑ k ∈ I i, a k)),
      sq_nonneg (C * (∑ k ∈ I i, e k) - r i),
      sq_nonneg (C * (∑ k ∈ I i, a k) - r i)]
  have heBound := error_blocks_square_sum_le I hI e he
  have haBound := main_blocks_square_sum_le I hI a hL hcard
  have hrBound : (∑ i, (r i) ^ 2) ≤ R ^ 2 := by
    refine (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hr i)).trans ?_
    have hr0 : 0 ≤ ∑ i, r i := Finset.sum_nonneg fun i _ => hr i
    nlinarith
  calc
    _ ≤ ∑ i, (3 * C ^ 2 * ((∑ k ∈ I i, e k) ^ 2 + (∑ k ∈ I i, a k) ^ 2) + 3 * (r i) ^ 2) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = 3 * C ^ 2 * ((∑ i, (∑ k ∈ I i, e k) ^ 2) +
        ∑ i, (∑ k ∈ I i, a k) ^ 2) + 3 * ∑ i, (r i) ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add heBound haBound) (by positivity))
      (mul_le_mul_of_nonneg_left hrBound (by norm_num))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual last eligible angular level exists for every positive
precision. Packet stopping precedes the stopping of its assigned top. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

theorem eligible_iff_le_lastEligible (g : AngularGrid) (cutoff precision : ℝ)
    (hp : 0 < precision) (hstart : g.eligible cutoff precision 0) (n : ℕ) :
    g.eligible cutoff precision n ↔ n ≤ g.lastEligible cutoff precision hp := by
  let h := g.exists_ineligible cutoff precision hp
  have hfirst : 0 < Nat.find h := by
    by_contra hn
    have hz : Nat.find h = 0 := by omega
    apply Nat.find_spec h
    simpa only [hz] using hstart
  constructor
  · intro hn
    by_contra hle
    have hfind : Nat.find h ≤ n := by
      change ¬n ≤ Nat.find h - 1 at hle
      omega
    exact Nat.find_spec h (g.eligible_of_le hp.le hfind hn)
  · intro hn
    have hlt : n < Nat.find h := by
      change n ≤ Nat.find h - 1 at hn
      omega
    exact Classical.not_not.mp (Nat.find_min h hlt)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularSourceWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary masses and logarithmic variation along actual eligible top
paths. Every boundary uses the start of the block whose last transition
is the current level, in the shared family of all shifted groupings. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {ι X : Type*}

attribute [local instance] Classical.propDecidable

theorem index_center (g : AngularGrid) (level : ℕ) (cell : ℤ) :
    g.index level (g.center level cell) = cell := by
  have hG : (g.branching : ℝ) ≠ 0 := by
    exact_mod_cast (show g.branching ≠ 0 by have := g.branching_ge_two; omega)
  have heq : ((g.center level cell - g.origin) / g.rootWidth) *
      (g.branching : ℝ)^level = (cell : ℝ) + 1/2 := by
    unfold center left width
    field_simp [g.rootWidth_pos.ne', pow_ne_zero level hG]
    ring
  unfold index
  rw [heq]
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num

theorem boundaryTops_eq_of_cell (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) {base level : ℕ} (hle : base ≤ level)
    (gap : ℝ) {s t : ℝ} (hc : g.index (level+1) s = g.index (level+1) t) :
    g.boundaryTops tops slope precision cutoff base level gap s =
      g.boundaryTops tops slope precision cutoff base level gap t := by
  have hp := g.index_eq_of_le (Nat.le_succ level) hc
  have ha := g.index_eq_of_le (hle.trans (Nat.le_succ level)) hc
  simp only [boundaryTops, outsideNearTops, hp, ha, hc]

theorem boundaryMass_eq_of_cell (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    {base level : ℕ} (hle : base ≤ level) (gap : ℝ) {s t : ℝ}
    (hc : g.index (level+1) s = g.index (level+1) t) (x : X) :
    g.boundaryMass tops slope precision cutoff weight base level gap s x =
      g.boundaryMass tops slope precision cutoff weight base level gap t x := by
  unfold boundaryMass
  rw [g.boundaryTops_eq_of_cell tops slope precision cutoff hle gap hc]

theorem sourceBoundaryMass_path (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (level : ℕ) (s : ℝ) (x : X) :
    g.sourceBoundaryMass tops slope precision cutoff weight K gap level
        (g.index (level+1) s) x =
      g.boundaryMass tops slope precision cutoff weight (level+1-K) level (gap level) s x := by
  apply g.boundaryMass_eq_of_cell tops slope precision cutoff weight (by omega)
  exact g.index_center (level+1) _

theorem sourceBoundaryMass_bounds (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 ≤ weight i x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (level : ℕ) (s : ℝ) (x : X) :
    g.mass tops slope precision cutoff weight (level+1) (g.index (level+1) s) x ≤
      g.sourceBoundaryMass tops slope precision cutoff weight K gap level (g.index (level+1) s) x ∧
    g.sourceBoundaryMass tops slope precision cutoff weight K gap level (g.index (level+1) s) x ≤
      g.mass tops slope precision cutoff weight (level+1-K) (g.index (level+1-K) s) x := by
  rw [g.sourceBoundaryMass_path tops slope precision cutoff weight hK gap]
  have h := g.boundary_mass_bounds tops slope precision cutoff weight hp hw
    (by omega : level+1-K ≤ level) (gap level) s x
  exact ⟨h.1.trans h.2.1, h.2.2⟩

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularSourceAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The shared source amplitude uses the packet's stopping mass and the
actual boundary mass at each transition. The assigned top supplies the
positive mass required by every logarithm along the packet's path. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

attribute [local instance] Classical.propDecidable

theorem sourceTransition_norm_le_one (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 < weight i x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (x : X) (level : ℕ) (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) (level+1)) (hz : 0 ≤ (phase level).re) :
    ‖g.sourceTransition tops slope precision cutoff weight K gap phase x level
      (g.index (level+1) (slope top))‖ ≤ 1 := by
  have hn := g.path_mass_pos tops slope precision cutoff weight hw (level+1) top htop he x
  have hb := (g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
    (fun i x => (hw i x).le) hK gap level (slope top) x).1
  exact analyticTransition_norm_le_one _ _ phase level _ hn (hn.trans_le hb) hb hz

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceResidualPropagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact propagation of source residual packets. The same angular
transition product occurs at every shift. A packet continuing in the
path child therefore acquires a coefficient depending only on its stop
level; Abel summation applies to one fixed raw packet prefix. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace AngularGrid
variable {σ ι X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Stop intervals belonging to different blocks are disjoint. -/
theorem block_of_stop_unique (level : ℕ → ℕ) (hlevel : StrictMono level)
    {i j k : ℕ} (hi : level i ≤ k ∧ k < level (i+1))
    (hj : level j ≤ k ∧ k < level (j+1)) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have h := hlevel.monotone (show i+1 ≤ j by omega)
    omega
  · have h := hlevel.monotone (show j+1 ≤ i by omega)
    omega

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShiftedScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual shifted angular blocks meet the source scale conditions.
The first block is included with its original shorter length. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid

/-- The ratio of actual angular widths is exactly the iterated step. -/
theorem source_width_ratio (g : AngularGrid) (L : ℝ) {lower upper : ℕ}
    (hle : lower ≤ upper) (hbranch : (g.branching:ℝ) = SourceParameters.step L) :
    g.width lower = SourceParameters.step L^(upper-lower)*g.width upper := by
  have hp : SourceParameters.step L^upper =
      SourceParameters.step L^lower*SourceParameters.step L^(upper-lower) := by
    rw [← pow_add,Nat.add_sub_of_le hle]
  unfold width
  rw [hbranch,hp]
  field_simp [(SourceParameters.step_pos L).ne']

/-- Every source block has width ratio between G and B, with exactly the
same conclusion for the initial block. -/
theorem source_shifted_width_bounds (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hK : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L)) (j : ℕ) :
    SourceParameters.step L*g.width (ShiftedBlocks.endpoint σ (j+1)) ≤
        g.width (ShiftedBlocks.endpoint σ j) ∧
      g.width (ShiftedBlocks.endpoint σ j) ≤
        SourceParameters.branching L*g.width (ShiftedBlocks.endpoint σ (j+1)) := by
  have hle := (ShiftedBlocks.endpoint_strictMono hK σ) (Nat.lt_succ_self j)
  change ShiftedBlocks.endpoint σ j < ShiftedBlocks.endpoint σ (j+1) at hle
  have hlen := ShiftedBlocks.endpoint_width_le σ j
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  rw [g.source_width_ratio L hle.le hbranch]
  constructor
  · apply mul_le_mul_of_nonneg_right _ (g.width_pos _).le
    calc
      SourceParameters.step L = SourceParameters.step L^1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hG (by omega)
  · apply mul_le_mul_of_nonneg_right _ (g.width_pos _).le
    exact pow_le_pow_right₀ hG (by omega)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTerminalScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The least ineligible shifted endpoint provides a finite terminal
generation without enlarging the source root line window past its top.
This includes exactly one final block after the last eligible endpoint. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem eligible_before_firstIneligibleShiftedBlock {K : ℕ}
    (g : AngularGrid) (cutoff precision : ℝ) (hp : 0 < precision) (hK : 0 < K)
    (σ : Fin K) {j : ℕ} (hj : j < g.firstIneligibleShiftedBlock cutoff precision hp hK σ) :
    g.eligible cutoff precision (ShiftedBlocks.endpoint σ j) := by
  exact Classical.not_not.mp
    (Nat.find_min (g.exists_shifted_terminal cutoff precision hp hK σ) hj)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceResidualGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed residual packet collection uses only endpoints at which
the reference top is still eligible. Its packets are shorter than that
top and lie in the reference angular cone. These are the geometric
hypotheses of the existing reference-line variation estimate. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem not_eligible_above_lastEligible (g : AngularGrid)
    (cutoff precision : ℝ) (hp : 0 < precision)
    (hzero : g.eligible cutoff precision 0) {k : ℕ}
    (hk : g.lastEligible cutoff precision hp < k) :
    ¬g.eligible cutoff precision k := by
  intro he
  exact (not_le.mpr hk) ((g.eligible_iff_le_lastEligible cutoff precision hp hzero k).mp he)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceResidualBlockGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual residual blocks contain disjoint bands of packet lengths.
Their cardinality is bounded by the logarithm of the source block width
ratio, rather than by the total number of packet scales. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem dyadic_precision_band_card {N : ℕ} (I : Finset (Fin N))
    {c A : ℝ} (hc : 0 < c) (_hA : 0 < A) (R : ℕ)
    (hband : ∀ j ∈ I, A < c*(2:ℝ)^j.val ∧ c*(2:ℝ)^j.val ≤ (2:ℝ)^R*A) :
    I.card ≤ R := by
  by_cases hI : I.Nonempty
  · let i := I.min' hI
    have hi : i ∈ I := I.min'_mem hI
    have hspan (j : Fin N) (hj : j ∈ I) : j.val < i.val+R := by
      by_contra hn
      have hpow : (2:ℝ)^(i.val+R) ≤ (2:ℝ)^j.val :=
        pow_le_pow_right₀ (by norm_num) (not_lt.mp hn)
      have hlower := mul_lt_mul_of_pos_left (hband i hi).1 (by positivity : (0:ℝ)<2^R)
      have hupper := (mul_le_mul_of_nonneg_left hpow hc.le).trans (hband j hj).2
      rw [pow_add] at hupper
      nlinarith
    let idx := fun j : Fin N => j.val
    have hinj : Set.InjOn idx I := fun _ _ _ _ h => Fin.ext h
    have hsubset : I.image idx ⊆ Finset.Ico i.val (i.val+R) := by
      intro k hk
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_Ico.mpr ⟨I.min'_le j hj,hspan j hj⟩
    calc
      I.card = (I.image idx).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Ico i.val (i.val+R)).card := Finset.card_le_card hsubset
      _ = R := by simp
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hI,Finset.card_empty]
    exact Nat.zero_le _

theorem residualLengthSet_disjoint {N : ℕ} (stop : Fin N → ℕ)
    (level : ℕ → ℕ) (hlevel : StrictMono level) :
    Pairwise (fun i j => Disjoint (residualLengthSet stop (level i) (level (i+1)))
      (residualLengthSet stop (level j) (level (j+1)))) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro k hki hkj
  have hi := (Finset.mem_filter.mp hki).2
  have hj := (Finset.mem_filter.mp hkj).2
  exact hij (AngularGrid.block_of_stop_unique level hlevel hi hj)

namespace AngularGrid

theorem source_residual_precision_window (g : AngularGrid) {w B length : ℝ}
    (hw : 0 < w) (_hB : 0 < B) (hlen : 0 < length)
    (hzero : g.eligible (g.rootWidth/B^2) (w/length) 0)
    {lower upper : ℕ}
    (hstop : lower ≤ g.lastEligible (g.rootWidth/B^2) (w/length) (div_pos hw hlen) ∧
      g.lastEligible (g.rootWidth/B^2) (w/length) (div_pos hw hlen) < upper) :
    g.width upper/B^2 < w/length ∧ w/length ≤ g.width lower/B^2 := by
  have hlow := (g.eligible_iff_le_lastEligible _ _ (div_pos hw hlen) hzero lower).mpr hstop.1
  have hhigh := g.not_eligible_above_lastEligible _ _ (div_pos hw hlen) hzero hstop.2
  have heq (k : ℕ) : (g.rootWidth/B^2)/(g.branching:ℝ)^k = g.width k/B^2 := by
    unfold width
    ring
  constructor
  · rw [← heq upper]
    exact not_le.mp (fun h => hhigh ((g.eligible_iff_precision_le _ _ _).mpr h))
  · rw [← heq lower]
    exact (g.eligible_iff_precision_le _ _ _).mp hlow

/-- The full residual only belongs to the parent cell. Its cone is wider
by one block ratio than the continuing residual's cone. -/
theorem source_parent_residual_cone (g : AngularGrid)
    {w B length C packetSlope assignedSlope referenceSlope : ℝ}
    (hw : 0 < w) (hB : 0 < B) (hlen : 0 < length)
    (hzero : g.eligible (g.rootWidth/B^2) (w/length) 0)
    {lower upper : ℕ}
    (hstop : lower ≤ g.lastEligible (g.rootWidth/B^2) (w/length) (div_pos hw hlen) ∧
      g.lastEligible (g.rootWidth/B^2) (w/length) (div_pos hw hlen) < upper)
    (hwidth : g.width lower ≤ B*g.width upper)
    (hcell : g.index lower assignedSlope = g.index lower referenceSlope)
    (hangle : |packetSlope-assignedSlope| ≤ C*(w/length)) :
    |packetSlope-referenceSlope| ≤ (C+B^3)*(w/length) := by
  have hp := (g.source_residual_precision_window hw hB hlen hzero hstop).1
  have hu : g.width upper < B^2*(w/length) := by
    have h := (div_lt_iff₀ (sq_pos_of_pos hB)).mp hp
    simpa only [mul_comm] using h
  have hl : g.width lower ≤ B^3*(w/length) := by
    calc
      _ ≤ B*g.width upper := hwidth
      _ ≤ B*(B^2*(w/length)) := mul_le_mul_of_nonneg_left hu.le hB.le
      _ = _ := by ring
  calc
    _ ≤ |packetSlope-assignedSlope|+|assignedSlope-referenceSlope| := abs_sub_le _ _ _
    _ ≤ C*(w/length)+g.width lower := add_le_add hangle (g.same_cell_diameter lower hcell)
    _ ≤ C*(w/length)+B^3*(w/length) := add_le_add le_rfl hl
    _ = _ := by ring

/-- A residual block has at most log₂(block ratio) dyadic lengths. The
strict lower precision cutoff also handles a zero-width empty band. -/
theorem source_residual_length_card {N : ℕ} (g : AngularGrid)
    {w B baseLength : ℝ} (hw : 0 < w) (hB : 0 < B) (hlen : 0 < baseLength)
    (lower upper R : ℕ) (hwidth : g.width lower ≤ (2:ℝ)^R*g.width upper)
    (hzero : ∀ j : Fin N, g.eligible (g.rootWidth/B^2) (w/(baseLength/(2:ℝ)^j.val)) 0) :
    let stop := fun j : Fin N => g.lastEligible (g.rootWidth/B^2)
      (w/(baseLength/(2:ℝ)^j.val)) (by positivity)
    (residualLengthSet stop lower upper).card ≤ R := by
  dsimp only
  apply dyadic_precision_band_card _ (div_pos hw hlen)
    (div_pos (g.width_pos upper) (sq_pos_of_pos hB)) R
  intro j hj
  have hjs := (Finset.mem_filter.mp hj).2
  have h := g.source_residual_precision_window hw hB
    (show 0 < baseLength/(2:ℝ)^j.val by positivity) (hzero j) hjs
  have heq : w/(baseLength/(2:ℝ)^j.val) = (w/baseLength)*(2:ℝ)^j.val := by
    field_simp
  rw [heq] at h
  refine ⟨h.1,h.2.trans ?_⟩
  calc
    _ ≤ ((2:ℝ)^R*g.width upper)/B^2 :=
      div_le_div_of_nonneg_right hwidth (sq_nonneg B)
    _ = _ := by ring

theorem source_shifted_residual_length_card {N : ℕ} (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hK : 0 < SourceParameters.blockCount L) (shift : Fin (SourceParameters.blockCount L))
    {w baseLength : ℝ} (hw : 0 < w) (hlen : 0 < baseLength)
    (hzero : ∀ j : Fin N, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
      (w/(baseLength/(2:ℝ)^j.val)) 0) (block : ℕ) :
    let stop := fun j : Fin N => g.lastEligible (g.rootWidth/(SourceParameters.branching L)^2)
      (w/(baseLength/(2:ℝ)^j.val)) (by positivity)
    (residualLengthSet stop (ShiftedBlocks.endpoint shift block)
      (ShiftedBlocks.endpoint shift (block+1))).card ≤
        SourceParameters.stepExponent L*SourceParameters.blockCount L := by
  apply g.source_residual_length_card hw (SourceParameters.branching_pos L) hlen _ _ _ ?_ hzero
  have h := (g.source_shifted_width_bounds L hbranch hK shift block).2
  simpa only [SourceParameters.branching,SourceParameters.step,pow_mul] using h

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceResidualSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual residual coefficient is bounded by its assigned top's
mask times a negative power of that top's weight. Grouping the resulting
absolute packet envelopes by the disjoint source length bands gives the
marked residual square estimate without any angular-depth factor. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem packet_length_group_norm_bound {σ E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {N : ℕ} (Q : Finset σ) (lengthIndex : σ → Fin N)
    (I : Finset (Fin N)) (multiplier : σ → ℂ) (value : σ → E)
    (envelope : Fin N → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hsupport : ∀ q ∈ Q, lengthIndex q ∈ I)
    (hmult : ∀ q ∈ Q, ‖multiplier q‖ ≤ C)
    (henvelope : ∀ k ∈ I, (∑ q ∈ Q.filter (fun q => lengthIndex q = k), ‖value q‖) ≤ envelope k) :
    ‖∑ q ∈ Q, multiplier q • value q‖ ≤ C*∑ k ∈ I, envelope k := by
  calc
    _ ≤ ∑ q ∈ Q, ‖multiplier q • value q‖ := norm_sum_le _ _
    _ = ∑ q ∈ Q, ‖multiplier q‖*‖value q‖ := by simp only [norm_smul]
    _ ≤ ∑ q ∈ Q, C*‖value q‖ := Finset.sum_le_sum (fun q hq =>
      mul_le_mul_of_nonneg_right (hmult q hq) (norm_nonneg _))
    _ = C*∑ q ∈ Q, ‖value q‖ := (Finset.mul_sum ..).symm
    _ = C*∑ k ∈ I, ∑ q ∈ Q.filter (fun q => lengthIndex q = k), ‖value q‖ := by
      rw [Finset.sum_fiberwise_of_maps_to hsupport]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum henvelope) hC

namespace AngularGrid
variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem source_packet_residual_coefficient_bound (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (hz : ∀ k, 0 ≤ (phase k).re) (a : ℝ) (ha : 0 ≤ a) (x : X)
    (mask : ι → ℂ) (C : ℝ)
    (hmask : ∀ t ∈ tops, weight t x^(-a)*‖mask t‖ ≤ C)
    (top : ι) (htop : top ∈ tops) (stop : ℕ)
    (he : g.eligible cutoff (precision top) stop) (lower : ℕ) :
    ‖g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight K gap phase x)
        lower stop (slope top)*
      ((g.mass tops slope precision cutoff weight stop (g.index stop (slope top)) x^(-a):ℝ):ℂ)*mask top‖ ≤ C := by
  have hprod : ‖g.packetPathProduct
      (g.sourceTransition tops slope precision cutoff weight K gap phase x)
      lower stop (slope top)‖ ≤ 1 := by
    rw [packetPathProduct,norm_prod]
    apply Finset.prod_le_one
    · intro k _
      exact norm_nonneg _
    · intro k hk
      exact g.sourceTransition_norm_le_one tops slope precision cutoff weight hp hw hK gap phase
        x k top htop (g.eligible_of_le (hp top htop)
          (Nat.succ_le_of_lt (Finset.mem_Ico.mp hk).2) he) (hz k)
  have hmember : top ∈ g.cellTops tops slope precision cutoff stop (g.index stop (slope top)) :=
    (g.mem_cellTops _ _ _ _ _ _ _).mpr ⟨htop,rfl,he⟩
  have hm : weight top x ≤ g.mass tops slope precision cutoff weight stop (g.index stop (slope top)) x :=
    Finset.single_le_sum (fun t _ => (hw t x).le) hmember
  have hrpow := Real.rpow_le_rpow_of_nonpos (hw top x) hm (neg_nonpos.mpr ha)
  have hnonneg : 0 ≤ g.mass tops slope precision cutoff weight stop (g.index stop (slope top)) x^(-a) :=
    Real.rpow_nonneg ((hw top x).le.trans hm) _
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnonneg]
  calc
    _ ≤ (1*(g.mass tops slope precision cutoff weight stop (g.index stop (slope top)) x^(-a)))*‖mask top‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprod hnonneg) (norm_nonneg _)
    _ ≤ weight top x^(-a)*‖mask top‖ := by
      rw [one_mul]
      exact mul_le_mul_of_nonneg_right hrpow (norm_nonneg _)
    _ ≤ C := hmask top htop

/-- Exact assigned-top coefficients and a per-length absolute envelope
control the complete residual of an actual source node. -/
theorem source_packet_residual_norm_bound {N : ℕ} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (hz : ∀ k, 0 ≤ (phase k).re) (a : ℝ) (ha : 0 ≤ a) (x : X)
    (packets : Finset σ) (assigned : σ → ι) (lengthIndex : σ → Fin N)
    (stop : Fin N → ℕ) (mask : ι → ℂ) (value : σ → E)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (he : ∀ q ∈ packets, g.eligible cutoff (precision (assigned q)) (stop (lengthIndex q)))
    (C : ℝ) (hC : 0 ≤ C) (hmask : ∀ t ∈ tops, weight t x^(-a)*‖mask t‖ ≤ C)
    (lower upper : ℕ) (pathSlope : ℝ) (envelope : Fin N → ℝ)
    (henvelope : ∀ k ∈ residualLengthSet stop lower upper,
      (∑ q ∈ ((g.packetSet packets (fun q => slope (assigned q))
          (fun q => stop (lengthIndex q)) lower (g.index lower pathSlope)).filter
            (fun q => stop (lengthIndex q) < upper)).filter (fun q => lengthIndex q = k),
        ‖value q‖) ≤ envelope k) :
    ‖g.packetResidual packets (fun q => slope (assigned q)) (fun q => stop (lengthIndex q))
      (g.sourcePacketBase tops slope precision cutoff weight assigned (fun q => stop (lengthIndex q))
        (fun q => mask (assigned q) • value q) a x)
      (g.sourceTransition tops slope precision cutoff weight K gap phase x)
      lower upper (g.index lower pathSlope)‖ ≤ C*∑ k ∈ residualLengthSet stop lower upper, envelope k := by
  unfold packetResidual
  simp only [sourcePacketBase,smul_smul]
  apply packet_length_group_norm_bound _ lengthIndex (residualLengthSet stop lower upper) _ value
    envelope hC
  · intro q hq
    obtain ⟨hq,hupper⟩ := Finset.mem_filter.mp hq
    have hstop := (Finset.mem_filter.mp hq).2.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hstop,hupper⟩
  · intro q hq
    have hqp := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    have h := g.source_packet_residual_coefficient_bound tops slope precision cutoff weight hp hw hK
      gap phase hz a ha x mask C hmask (assigned q) (hassigned q hqp) (stop (lengthIndex q))
      (he q hqp) lower
    simpa only [mul_assoc] using h
  · exact henvelope

/-- The block square estimate now has the actual source residuals on
the left. All overlap and length-cardinality costs are proved above;
the remaining inputs are the positive per-length reference envelopes. -/
theorem source_packet_residual_square_sum {N : ℕ} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (hz : ∀ k, 0 ≤ (phase k).re) (a : ℝ) (ha : 0 ≤ a) (x : X)
    (packets : Finset σ) (assigned : σ → ι) (lengthIndex : σ → Fin N)
    (stop : Fin N → ℕ) (mask : ι → ℂ) (value : σ → E)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (he : ∀ q ∈ packets, g.eligible cutoff (precision (assigned q)) (stop (lengthIndex q)))
    (C : ℝ) (hC : 0 ≤ C) (hmask : ∀ t ∈ tops, weight t x^(-a)*‖mask t‖ ≤ C)
    (level : ℕ → ℕ) (hlevel : StrictMono level) (count : ℕ) (pathSlope : ℝ)
    (error main : Fin N → ℝ) (herror : ∀ k, 0 ≤ error k) (hmain : ∀ k, 0 ≤ main k)
    (R : ℝ) (hR : 0 ≤ R)
    (hcard : ∀ j < count, ((residualLengthSet stop (level j) (level (j+1))).card:ℝ) ≤ R)
    (henvelope : ∀ j < count, ∀ k ∈ residualLengthSet stop (level j) (level (j+1)),
      (∑ q ∈ ((g.packetSet packets (fun q => slope (assigned q))
          (fun q => stop (lengthIndex q)) (level j) (g.index (level j) pathSlope)).filter
            (fun q => stop (lengthIndex q) < level (j+1))).filter (fun q => lengthIndex q = k),
        ‖value q‖) ≤ error k+main k) :
    (∑ j : Fin count, ‖g.packetResidual packets (fun q => slope (assigned q))
      (fun q => stop (lengthIndex q))
      (g.sourcePacketBase tops slope precision cutoff weight assigned (fun q => stop (lengthIndex q))
        (fun q => mask (assigned q) • value q) a x)
      (g.sourceTransition tops slope precision cutoff weight K gap phase x)
      (level j.val) (level (j.val+1)) (g.index (level j.val) pathSlope)‖^2) ≤
        3*C^2*((∑ k, error k)^2+R*∑ k, (main k)^2) := by
  have hd := residualLengthSet_disjoint stop level hlevel
  have h := residual_blocks_square_sum_le
    (fun j : Fin count => residualLengthSet stop (level j.val) (level (j.val+1)))
    (fun i j hij => hd (Fin.val_injective.ne hij)) error main herror hmain
    (fun j : Fin count => g.packetResidual packets (fun q => slope (assigned q))
      (fun q => stop (lengthIndex q))
      (g.sourcePacketBase tops slope precision cutoff weight assigned (fun q => stop (lengthIndex q))
        (fun q => mask (assigned q) • value q) a x)
      (g.sourceTransition tops slope precision cutoff weight K gap phase x)
      (level j.val) (level (j.val+1)) (g.index (level j.val) pathSlope))
    (fun _ => 0) (C := C) (L := R) (R := 0) (fun _ => le_rfl) hC hR le_rfl
    (fun j => hcard j.val j.isLt) (by simp) ?_
  · simpa only [zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] using h
  · intro j
    have hj := g.source_packet_residual_norm_bound tops slope precision cutoff weight hp hw hK gap
      phase hz a ha x packets assigned lengthIndex stop mask value hassigned he C hC hmask
      (level j.val) (level (j.val+1)) pathSlope (fun k => error k+main k)
      (henvelope j.val j.isLt)
    simpa only [Finset.sum_add_distrib,add_zero] using hj

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceResidualPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial good-path thresholds control the actual residual square
with an exponent fixed before the path and the mass cutoff are chosen. -/

noncomputable section
namespace LipschitzHilbert

theorem residual_square_polynomial_bound {L C A E S R c q p r : ℝ}
    (hL : 6 ≤ L) (hC : 0 ≤ C) (hA : 0 ≤ A) (hE : 0 ≤ E) (hS : 0 ≤ S)
    (hR : 0 ≤ R) (hr : 0 ≤ r)
    (hCb : C ≤ L^c) (hAb : A ≤ L^q) (hEb : E ≤ L^p) (hSb : S ≤ L^p)
    (hRb : R ≤ L^r) :
    3*C^2*A^2*(E^2+R*S^2) ≤ (L^(c+q+p+r+1))^2 := by
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hR1 : 1 ≤ L^r := Real.one_le_rpow hL1 hr
  have hEsq := pow_le_pow_left₀ hE hEb 2
  have hSsq := pow_le_pow_left₀ hS hSb 2
  have hCq := pow_le_pow_left₀ hC hCb 2
  have hAq := pow_le_pow_left₀ hA hAb 2
  have hES : E^2+R*S^2 ≤ 2*L^r*(L^p)^2 := by
    have hmul := mul_le_mul hRb hSsq (sq_nonneg S) (Real.rpow_nonneg hL0.le r)
    have hOne := mul_le_mul_of_nonneg_right hR1 (sq_nonneg (L^p))
    nlinarith
  calc
    _ ≤ 3*(L^c)^2*(L^q)^2*(2*L^r*(L^p)^2) := by
      exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hCq (by norm_num)) hAq
        (sq_nonneg A) (by positivity)) hES (by positivity) (by positivity)
    _ = 6*L^(2*c+2*q+r+2*p) := by
      rw [← Real.rpow_mul_natCast hL0.le,← Real.rpow_mul_natCast hL0.le,
        ← Real.rpow_mul_natCast hL0.le]
      push_cast
      rw [Real.rpow_add hL0,Real.rpow_add hL0,Real.rpow_add hL0]
      ring_nf
    _ ≤ L*L^(2*c+2*q+r+2*p) :=
      mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hL0.le _)
    _ = L^(2*c+2*q+r+2*p+1) := by
      calc
        _ = L^(2*c+2*q+r+2*p)*L^(1:ℝ) := by rw [Real.rpow_one]; ring
        _ = _ := (Real.rpow_add hL0 _ _).symm
    _ ≤ L^(2*(c+q+p+r+1)) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    _ = _ := by rw [← Real.rpow_mul_natCast hL0.le]; push_cast; congr 1; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledResidualThreshold
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On the actual good-reference event, the residual-square expression
has a single fixed polynomial bound. The error and main quantities are
the original physical packet sums, not abstract envelope assumptions. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem physical_residual_expression_polynomial (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (y x : ℝ)
    {L C R c q p r : ℝ} (hL : 6 ≤ L) (hC : 0 ≤ C) (hR : 0 ≤ R) (hr : 0 ≤ r)
    (hCb : C ≤ L^c) (hAb : P.absoluteConstant ≤ L^q)
    (hError : P.physicalAngularError t a b v g (x,y+t*x) ≤ L^p)
    (hMain : P.physicalMainSquare t a b v g y x ≤ L^p) (hRb : R ≤ L^r) :
    3*C^2*((∑ k, P.absoluteConstant*P.physicalErrorScale t a b v g k y x)^2+
      R*∑ k, (P.absoluteConstant*P.physicalMainScale t a b v g k y x)^2) ≤
        (L^(c+q+p+r+1))^2 := by
  let E := P.physicalAngularError t a b v g (x,y+t*x)
  let S := P.physicalMainSquare t a b v g y x
  have hE : 0 ≤ E := by
    change 0 ≤ P.physicalAngularError t a b v g (x,y+t*x)
    rw [← P.sum_physicalErrorScale t a b v g y x]
    exact Finset.sum_nonneg (fun k _ => P.physicalErrorScale_nonneg t a b v g k y x)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hsumE : (∑ k, P.absoluteConstant*P.physicalErrorScale t a b v g k y x) =
      P.absoluteConstant*E := by
    rw [← Finset.mul_sum,P.sum_physicalErrorScale]
  have hsumS : (∑ k, (P.absoluteConstant*P.physicalMainScale t a b v g k y x)^2) =
      P.absoluteConstant^2*S^2 := by
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
    congr 1
    exact (Real.sq_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg
      (P.physicalMainScale t a b v g k y x)))).symm
  rw [hsumE,hsumS]
  calc
    _ = 3*C^2*P.absoluteConstant^2*(E^2+R*S^2) := by ring
    _ ≤ _ := residual_square_polynomial_bound hL hC P.absoluteConstant_pos.le hE hS hR hr
      hCb hAb hError hMain hRb

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledCrossResidual
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cross-profile residual squares: analyze against the original packets,
synthesize the alternate packets, and keep the same original main/error
reference quantities. No alternate analyzing coefficient is substituted. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

/-- Change only synthesis profiles; the analyzing coefficient and both
positive reference quantities remain those of the original family. -/
theorem actual_cross_packet_subset_envelope (horder : 6 ≤ P.order) (i : Fin 3) (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (Q : Finset (Σ l : P.labels j, Item j l)) (y x : ℝ) :
    (∑ q ∈ Q, ‖(P.withProfile alt hAlt).rawPacketValue i j q.1 q.2
      (P.physicalMultiplierCoefficient t b v g j q.1 q.2) y x‖) ≤
        P.absoluteConstant*(P.physicalErrorScale t a b v g j y x+
          P.physicalMainScale t a b v g j y x) := by
  exact (P.withProfile alt hAlt).sum_raw_packet_values_split horder i j
    (P.physicalMultiplierCoefficient t b v g j)
    (P.physicalFrozenCenteredCoefficient t a b v g j)
    (P.physicalAngularErrorCoefficient t a b v g j)
    (fun l u => P.physicalMultiplierCoefficient_split t a b hb hb1 v hv g hg hg1 j l u) Q y x

theorem physicalCrossPacketValue_length_envelope (horder : 6 ≤ P.order) (i : Fin 3) (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (Q : Finset P.PacketIndex) (j : Fin N) (z : ℝ×ℝ) :
    (∑ q ∈ Q.filter (fun q => q.1 = j), ‖P.physicalCrossPacketValue alt hAlt t b v g i z q‖) ≤
      P.absoluteConstant*(P.physicalErrorScale t a b v g j (z.2-t*z.1) z.1+
        P.physicalMainScale t a b v g j (z.2-t*z.1) z.1) := by
  classical
  calc
    _ ≤ ∑ q ∈ Finset.univ.filter (fun q : P.PacketIndex => q.1 = j),
        ‖P.physicalCrossPacketValue alt hAlt t b v g i z q‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset_filter _ (Finset.subset_univ Q)) (fun _ _ _ => norm_nonneg _)
    _ = ∑ u : (Σ l : P.labels j, Item j l),
        ‖P.physicalCrossPacketValue alt hAlt t b v g i z ⟨j,u⟩‖ := by
      rw [Finset.sum_filter,Fintype.sum_sigma,Finset.sum_eq_single j]
      · simp only [ite_true, if_true]
      · intro k _ hkj
        simp only [hkj,ite_false, if_false,Finset.sum_const_zero]
      · simp
    _ ≤ _ := P.actual_cross_packet_subset_envelope alt hAlt horder i t a b hb hb1 v hv g hg hg1
      j Finset.univ (z.2-t*z.1) z.1

/-- The actual source residual square now follows from the original
coefficient split and packet geometry; no residual-envelope premise remains. -/
theorem physical_cross_packet_residual_square_sum {τ : Type*}
    (horder : 6 ≤ P.order) (i : Fin 3) (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (hf : Measurable f) (hf1 : ∀ z, ‖f z‖ ≤ 1)
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → ℝ×ℝ → ℝ)
    (hp : ∀ T ∈ tops, 0 ≤ precision T) (hw : ∀ T z, 0 < weight T z)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (hz : ∀ k, 0 ≤ (phase k).re) (alpha : ℝ) (ha : 0 ≤ alpha) (z : ℝ×ℝ)
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (stop : Fin N → ℕ) (mask : τ → ℂ)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (he : ∀ q ∈ packets, grid.eligible cutoff (precision (assigned q)) (stop q.1))
    (C : ℝ) (hC : 0 ≤ C) (hmask : ∀ T ∈ tops, weight T z^(-alpha)*‖mask T‖ ≤ C)
    (level : ℕ → ℕ) (hlevel : StrictMono level) (count : ℕ) (pathSlope : ℝ)
    (R : ℝ) (hR : 0 ≤ R)
    (hcard : ∀ j < count,
      ((residualLengthSet stop (level j) (level (j+1))).card:ℝ) ≤ R) :
    let value := P.physicalCrossPacketValue alt hAlt t b v f i z
    (∑ j : Fin count, ‖grid.packetResidual packets (fun q => slope (assigned q))
      (fun q => stop q.1)
      (grid.sourcePacketBase tops slope precision cutoff weight assigned (fun q => stop q.1)
        (fun q => mask (assigned q) • value q) alpha z)
      (grid.sourceTransition tops slope precision cutoff weight K gap phase z)
      (level j.val) (level (j.val+1)) (grid.index (level j.val) pathSlope)‖^2) ≤
        3*C^2*((∑ k, P.absoluteConstant*P.physicalErrorScale t a b v f k (z.2-t*z.1) z.1)^2+
          R*∑ k, (P.absoluteConstant*P.physicalMainScale t a b v f k (z.2-t*z.1) z.1)^2) := by
  classical
  dsimp only
  apply grid.source_packet_residual_square_sum tops slope precision cutoff weight hp hw hK gap
    phase hz alpha ha z packets assigned (fun q : P.PacketIndex => q.1) stop mask
    (P.physicalCrossPacketValue alt hAlt t b v f i z) hassigned he C hC hmask level hlevel count pathSlope
    (fun k => P.absoluteConstant*P.physicalErrorScale t a b v f k (z.2-t*z.1) z.1)
    (fun k => P.absoluteConstant*P.physicalMainScale t a b v f k (z.2-t*z.1) z.1)
    (fun k => mul_nonneg P.absoluteConstant_pos.le (P.physicalErrorScale_nonneg t a b v f k _ _))
    (fun k => mul_nonneg P.absoluteConstant_pos.le (P.physicalMainScale_nonneg t a b v f k _ _))
    R hR hcard
  intro j _ k _
  have h := P.physicalCrossPacketValue_length_envelope alt hAlt horder i t a b hb hb1 v hv f hf hf1
    ((grid.packetSet packets (fun q => slope (assigned q)) (fun q => stop q.1)
      (level j) (grid.index (level j) pathSlope)).filter (fun q => stop q.1 < level (j+1))) k z
  simpa only [mul_add] using h

theorem physical_cross_packet_residual_square_polynomial {τ : Type*}
    (horder : 6 ≤ P.order) (i : Fin 3) (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (hf : Measurable f) (hf1 : ∀ z, ‖f z‖ ≤ 1)
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → ℝ×ℝ → ℝ)
    (hp : ∀ T ∈ tops, 0 ≤ precision T) (hw : ∀ T z, 0 < weight T z)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (hz : ∀ k, 0 ≤ (phase k).re) (alpha : ℝ) (ha : 0 ≤ alpha) (z : ℝ×ℝ)
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (stop : Fin N → ℕ) (mask : τ → ℂ)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (he : ∀ q ∈ packets, grid.eligible cutoff (precision (assigned q)) (stop q.1))
    (C : ℝ) (hC : 0 ≤ C) (hmask : ∀ T ∈ tops, weight T z^(-alpha)*‖mask T‖ ≤ C)
    (level : ℕ → ℕ) (hlevel : StrictMono level) (count : ℕ) (pathSlope : ℝ)
    (R : ℝ) (hR : 0 ≤ R)
    (hcard : ∀ j < count,
      ((residualLengthSet stop (level j) (level (j+1))).card:ℝ) ≤ R)
    (L c q p r : ℝ) (hL : 6 ≤ L) (hr : 0 ≤ r)
    (hCb : C ≤ L^c) (hAb : P.absoluteConstant ≤ L^q) (hRb : R ≤ L^r)
    (hError : P.physicalAngularError t a b v f z ≤ L^p)
    (hMain : P.physicalMainSquare t a b v f (z.2-t*z.1) z.1 ≤ L^p) :
    let value := P.physicalCrossPacketValue alt hAlt t b v f i z
    (∑ j : Fin count, ‖grid.packetResidual packets (fun q => slope (assigned q))
      (fun q => stop q.1)
      (grid.sourcePacketBase tops slope precision cutoff weight assigned (fun q => stop q.1)
        (fun q => mask (assigned q) • value q) alpha z)
      (grid.sourceTransition tops slope precision cutoff weight K gap phase z)
      (level j.val) (level (j.val+1)) (grid.index (level j.val) pathSlope)‖^2) ≤
        (L^(c+q+p+r+1))^2 := by
  dsimp only
  have h := P.physical_cross_packet_residual_square_sum alt hAlt horder i t a b hb hb1 v hv f hf hf1
    grid tops slope precision cutoff weight hp hw hK gap phase hz alpha ha z packets assigned
    stop mask hassigned he C hC hmask level hlevel count pathSlope R hR hcard
  apply h.trans
  have hpoint : (z.1,z.2-t*z.1+t*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  exact P.physical_residual_expression_polynomial t a b v f (z.2-t*z.1) z.1
    hL hC hR hr hCb hAb (by simpa only [hpoint] using hError) hMain hRb


end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledCrossIdentity
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The residual-square and unary-variation estimates use exactly the
same original analyzing coefficients and alternate physical synthesis.
The mask is applied to the synthesized vector, with no coefficient change. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)

theorem physicalCrossPacketValue_zero (y x : ℝ) (q : P.PacketIndex) :
    P.physicalCrossPacketValue alt hAlt t b v g 0 (x,y+t*x) q =
      WithLp.toLp 2 (fun k => P.physicalMultiplierCoefficient t b v g q.1 q.2.1 q.2.2 k*
        (P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k (x,y+t*x)) := by
  ext k
  have hw := congrArg (fun f : SchwartzMap ℝ ℂ => f x)
    ((P.withProfile alt hAlt).raw_eq_physical_slice 0 q.1 q.2.1 q.2.2 k y t)
  change (P.withProfile alt hAlt).raw 0 q.1 q.2.1 q.2.2 k y x =
    (P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k (x,y+t*x) at hw
  have hy : (y+t*x)-t*x = y := by ring
  simp only [physicalCrossPacketValue,rawPacketValue,WithLp.ofLp_toLp,hy,hw]

theorem physicalMaskedValue_eq_cross
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y x : ℝ) (q : P.PacketIndex) :
    P.physicalMaskedValue alt hAlt t b v g T L A (x,y+t*x) q =
      (T q.1 q.2.1 q.2.2).mask L A (x,y+t*x) •
        P.physicalCrossPacketValue alt hAlt t b v g 0 (x,y+t*x) q := by
  rw [P.physicalCrossPacketValue_zero alt hAlt t b v g]
  ext k
  simp only [physicalMaskedValue,WithLp.ofLp_toLp,PiLp.smul_apply,Complex.real_smul]
  ring

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceCross
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local reference restriction preserves the actual two-profile packet
operator, including its masked analyzing coefficient. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0<w) (hcone : 0 ≤ cone) (hF : 0≤F) (hwide : cone*w≤P.width)
  (hfrequency : ∀ k, |P.frequency k|≤F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

theorem referenceAlt_physicalPacket
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (j : Fin N) (l : (Q).labels j) (a : Item j l) (k : κ) :
    ((Q).withProfile
      (P.referenceAlt oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt)
      (P.referenceAlt_bound oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt hAlt)).physicalPacket
        newSlope j l a k =
    (P.withProfile alt hAlt).physicalPacket oldSlope j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) a k := by
  exact (P.withProfile alt hAlt).referenceFamily_physicalPacket
    oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency j l a k

theorem referenceFamily_crossPacketValue
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (Q).labels j) (a : Item j l) (z : ℝ×ℝ) :
    (Q).physicalCrossPacketValue
      (P.referenceAlt oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt)
      (P.referenceAlt_bound oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt hAlt)
      newSlope
      (P.referenceSelector oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency b)
      v g 0 z ⟨j,l,a⟩ =
    P.crossPacketValue alt hAlt oldSlope b v g z
      ⟨j,P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l,a⟩ := by
  have he := (Q).physicalCrossPacketValue_zero
    (P.referenceAlt oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt)
    (P.referenceAlt_bound oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt hAlt)
    newSlope
    (P.referenceSelector oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency b)
    v g (z.2-newSlope*z.1) z.1 ⟨j,l,a⟩
  have hz : (z.1,z.2-newSlope*z.1+newSlope*z.1)=z := by
    ext
    · rfl
    · dsimp only
      ring
  rw [hz] at he
  rw [he]
  apply WithLp.ofLp_injective
  funext k
  change (Q).physicalMultiplierCoefficient newSlope
    (P.referenceSelector oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency b)
      v g j l a k *
    ((Q).withProfile
      (P.referenceAlt oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt)
      (P.referenceAlt_bound oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt hAlt)).physicalPacket
        newSlope j l a k z = _
  rw [P.referenceFamily_multiplier_coefficient oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency b v g j l a,
    P.referenceAlt_physicalPacket oldSlope newSlope referenceLength cone w F
      hw hcone hF hwide hfrequency alt hAlt j l a k]
  rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceConditions
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frozen main coefficients vanish outside the fixed selector cone.
Restricting the main reference family to that cone is an exact identity;
its carrier bound therefore does not inherit the wide error cone. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

/-- A finite source sum supported on the reference labels equals the
sum in the literal restricted family. -/
theorem sum_referenceLabels_of_zero {E : Type*} [AddCommMonoid E]
    (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N)
    (f : ∀ l : P.labels j, Item j l → E)
    (hzero : ∀ l, ¬P.referenceCondition oldSlope newSlope referenceLength cone w j l →
      ∀ u, f l u = 0) :
    (∑ l : P.referenceLabels oldSlope newSlope referenceLength cone w j,
      ∑ u : Item j l, f (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u) =
      ∑ l : P.labels j, ∑ u : Item j l, f l u := by
  have hrestrict := Equiv.sum_comp (P.referenceLabelsEquiv oldSlope newSlope referenceLength cone w j)
    (fun l => ∑ u : Item j l.val, f l.val u)
  have hz : (∑ l : {l : P.labels j //
      ¬P.referenceCondition oldSlope newSlope referenceLength cone w j l},
      ∑ u : Item j l.val, f l.val u) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    exact Finset.sum_eq_zero (fun u _ => hzero l.val l.property u)
  have hsum := Fintype.sum_subtype_add_sum_subtype
    (P.referenceCondition oldSlope newSlope referenceLength cone w j)
    (fun l : P.labels j => ∑ u : Item j l, f l u)
  rw [hz,add_zero] at hsum
  exact hrestrict.trans hsum

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceProperties
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical selector centers are invariant under recentering.
Restricting to the reference cone can only decrease their local count. -/

noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => P.referenceOriginalLabel oldSlope newSlope R cone w

theorem referenceFamily_physical_center (j : Fin N) (l : (Q).labels j) :
    newSlope+(Q).rowSlope j l = oldSlope+P.rowSlope j (orig j l) := by
  change newSlope+(P.rowSlope j (orig j l)+(oldSlope-newSlope)) = _
  ring

theorem referenceFamily_localMultiplicity (j : Fin N) (d : ℝ) (M : ℕ)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) d M) :
    SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : (Q).labels j => newSlope+(Q).rowSlope j l) d M := by
  intro a
  apply (Finset.card_le_card_of_injOn (orig j) ?_ ?_).trans (hlocal a)
  · intro l hl
    obtain ⟨_,hlo,hhi⟩ := Finset.mem_filter.mp hl
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_⟩
    · change a ≤ newSlope+(P.rowSlope j (orig j l)+(oldSlope-newSlope)) at hlo
      change a ≤ oldSlope+P.rowSlope j (orig j l)
      linarith
    · change newSlope+(P.rowSlope j (orig j l)+(oldSlope-newSlope)) < a+d at hhi
      change oldSlope+P.rowSlope j (orig j l) < a+d
      linarith
  · intro l _ m _ heq
    apply Subtype.ext
    exact congrArg (fun u : P.labels j => u.val) heq

theorem referenceFamily_physicalMultiplierCoefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).physicalMultiplierCoefficient newSlope (fun j l => b j (orig j l)) v f j l u =
      P.physicalMultiplierCoefficient oldSlope b v f j (orig j l) u :=
  P.referenceFamily_multiplier_coefficient oldSlope newSlope R cone w F hw hcone hF hwide hfrequency b v f j l u

theorem referenceFamily_alternate_physicalPacket
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) (k : κ) :
    ((Q).withProfile (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))).physicalPacket
      newSlope j l u k = (P.withProfile alt hAlt).physicalPacket oldSlope j (orig j l) u k :=
  (P.withProfile alt hAlt).referenceFamily_physicalPacket oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency j l u k

/-- A selected set supported in the reference cone has the identical
sum after the literal label restriction, including empty item fibers. -/
theorem sum_referenceFamily_selected {E : Type*} [AddCommMonoid E]
    (S : Finset P.PacketIndex) (f : P.PacketIndex → E)
    (hS : ∀ u ∈ S, P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1) :
    (∑ u ∈ (Finset.univ : Finset (Q).PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S),
      f ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩) = ∑ u ∈ S, f u := by
  have hs : (Finset.univ.filter fun u : P.PacketIndex => u ∈ S) = S := by
    ext u
    simp
  conv_rhs => rw [← hs,Finset.sum_filter]
  simp only [Finset.sum_filter,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  exact P.sum_referenceLabels_of_zero oldSlope newSlope R cone w j
    (fun l u => if (⟨j,⟨l,u⟩⟩ : P.PacketIndex) ∈ S then f ⟨j,⟨l,u⟩⟩ else 0)
    (by
      intro l hl u
      rw [ite_eq_right]
      exact fun hu => hl (hS ⟨j,⟨l,u⟩⟩ hu))

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceLabeledPacketRestriction
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Any fixed residual packet subset is itself a lattice family, with
unchanged geometry, analyzing integrals and alternate synthesis waves.
Restricting the item fibers preserves the lattice constants exactly. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- Exact scalar/vector sums over the selected packet family. -/
theorem sum_restrictPackets {E : Type*} [AddCommMonoid E] (Q : Finset P.PacketIndex)
    (f : P.PacketIndex → E) :
    (∑ q : (P.restrictPackets Q).PacketIndex, f ⟨q.1,⟨q.2.1,q.2.2.val⟩⟩) =
      ∑ q ∈ Q, f q := by
  have h := Equiv.sum_comp (P.restrictedPacketEquiv Q) (fun q : Q => f q.val)
  exact h.trans (Finset.sum_subtype Q (p := fun q => q ∈ Q) (by simp) f).symm

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedSum
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact synthesis and separated-energy identities for the selected
reference lattice, with its cost expressed only in the original fixed
profile bounds. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem referenceEnvelopeConstant_pos :
    0<P.referenceEnvelopeConstant := by
  have hp := P.profileBound_pos
  have hr : 0<P.ratioBound := zero_lt_one.trans_le P.ratioBound_ge_one
  unfold referenceEnvelopeConstant
  positivity

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePhysicalSingleScale
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single length of original physical packets has a uniform positive
summation bound. Selector overlap is counted before convolution. The
analyzing coefficients remain those of the original profiles, while the
synthesis profiles may be any profiles with the same seminorm bound. -/

noncomputable section
open MeasureTheory
open Filter
open scoped BigOperators ComplexConjugate Topology
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- The shear changes coordinates, not the original analyzing coefficient. -/
theorem physicalMultiplierCoefficient_shear (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j) (u : Item j l) :
    analyzingCoefficient volume (fun _ : Item j l => P.length j*P.width)
      (fun u k z => b j l k (v (slopeShear t z))*P.raw 0 j l u k z.2 z.1)
      (fun z => g (slopeShear t z)) u =
        P.physicalMultiplierCoefficient t b v g j l u := by
  ext k
  simp only [analyzingCoefficient,physicalMultiplierCoefficient,WithLp.ofLp_toLp]
  change ((↑(P.length j*P.width):ℂ)⁻¹)*
    (∫ z, g (slopeShear t z) k*conj
      (b j l k (v (slopeShear t z))*P.raw 0 j l u k z.2 z.1)
        ∂volume.prod volume) = _
  have hw (z : ℝ×ℝ) : P.raw 0 j l u k z.2 z.1 =
      P.physicalPacket t j l u k (slopeShear t z) := by
    exact congrArg (fun f : SchwartzMap ℝ ℂ => f z.1)
      (P.raw_eq_physical_slice 0 j l u k z.2 t)
  simp_rw [hw]
  congr 1
  exact (slopeShear_measurePreserving t).integral_comp (slopeShear t).measurableEmbedding
    (fun z => g z k*conj (b j l k (v z)*P.physicalPacket t j l u k z))

/-- The positive coefficient sum has no factor for the total number of
labels. Only the selector's local multiplicity enters. -/
theorem physical_single_scale_coefficients (horder : 6 ≤ P.order)
    (j : Fin N) (t d radius M : ℝ) (K H : ℕ)
    (hd : 0 < d) (hM : 0 ≤ M) (hK : radius ≤ K)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => t+P.rowSlope j l) d H)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ l k, Measurable (b j l k))
    (hbM : ∀ l k s, ‖b j l k s‖ ≤ M)
    (hsupport : ∀ l k s, b j l k s ≠ 0 →
      |s-(t+P.rowSlope j l)| ≤ radius*d)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (y x : ℝ) :
    (∑ l : P.labels j, ∑ u : Item j l,
      ‖P.physicalMultiplierCoefficient t b v g j l u‖*
        tileEnvelope (P.length j*(P.snappedSite j l u).1)
          (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 (x,y)) ≤
      (64*(4*Real.pi)^2)*((P.absoluteConstant*M*((2*K+1)*H:ℕ))*Real.pi^2) := by
  have h := source_selector_single_scale (fun l : P.labels j => Item j l)
    (P.snappedSite j) (P.snappedSite_injective j) (fun _ => 0) (fun _ => 0)
    (fun l => t+P.rowSlope j l) (P.length_pos j) P.width_pos hd
    P.absoluteConstant_pos.le hM hlocal hK (b j) hb hbM hsupport
    (fun z => v (slopeShear t z)) (hv.comp (slopeShear t).measurable)
    (fun l u k z => P.raw 0 j l u k z.2 z.1)
    (fun l u k => P.raw_swapped_joint_measurable 0 j l u k)
    (by
      intro l u k z
      simpa only [zero_add] using P.raw_absolute_tileEnvelope horder 0 j l u k z)
    (fun z => g (slopeShear t z)) (hg.comp (slopeShear t).measurable)
    (fun z => hg1 (slopeShear t z)) (x,y)
  simpa only [zero_add,physicalMultiplierCoefficient_shear] using h

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

/-- Any selected packets at the given length, with alternate synthesis
and any of the three covariant jets, obey the same positive bound. -/
theorem physical_single_scale_raw_synthesis (horder : 6 ≤ P.order)
    (i : Fin 3) (j : Fin N) (t d radius M : ℝ) (K H : ℕ)
    (hd : 0 < d) (hM : 0 ≤ M) (hK : radius ≤ K)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => t+P.rowSlope j l) d H)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ l k, Measurable (b j l k))
    (hbM : ∀ l k s, ‖b j l k s‖ ≤ M)
    (hsupport : ∀ l k s, b j l k s ≠ 0 →
      |s-(t+P.rowSlope j l)| ≤ radius*d)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (Q : Finset (Σ l : P.labels j, Item j l)) (y x : ℝ) :
    (∑ q ∈ Q, ‖(P.withProfile alt hAlt).rawPacketValue i j q.1 q.2
      (P.physicalMultiplierCoefficient t b v g j q.1 q.2) y x‖) ≤
      P.absoluteConstant*((64*(4*Real.pi)^2)*
        ((P.absoluteConstant*M*((2*K+1)*H:ℕ))*Real.pi^2)) := by
  classical
  calc
    _ ≤ ∑ q : (Σ l : P.labels j, Item j l),
        ‖(P.withProfile alt hAlt).rawPacketValue i j q.1 q.2
          (P.physicalMultiplierCoefficient t b v g j q.1 q.2) y x‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Q)
        (fun _ _ _ => norm_nonneg _)
    _ ≤ ∑ q : (Σ l : P.labels j, Item j l),
        P.absoluteConstant*(‖P.physicalMultiplierCoefficient t b v g j q.1 q.2‖*
          tileEnvelope (P.length j*(P.snappedSite j q.1 q.2).1)
            (P.width*(P.snappedSite j q.1 q.2).2) (P.length j) P.width 6 (x,y)) := by
      apply Finset.sum_le_sum
      intro q _
      exact (P.withProfile alt hAlt).raw_packet_value_norm horder i j q.1 q.2
        (P.physicalMultiplierCoefficient t b v g j q.1 q.2) y x
    _ = P.absoluteConstant*(∑ l : P.labels j, ∑ u : Item j l,
        ‖P.physicalMultiplierCoefficient t b v g j l u‖*
          tileEnvelope (P.length j*(P.snappedSite j l u).1)
            (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 (x,y)) := by
      rw [← Finset.mul_sum,Fintype.sum_sigma]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (P.physical_single_scale_coefficients horder j t d radius M K H hd hM hK hlocal
        b hb hbM hsupport v hv g hg hg1 y x) P.absoluteConstant_pos.le

/-- The same bound in the original physical coordinates, restricted to
any finite packet set at one length. -/
theorem physical_single_scale_cross_packets (horder : 6 ≤ P.order)
    (i : Fin 3) (j : Fin N) (t d radius M : ℝ) (K H : ℕ)
    (hd : 0 < d) (hM : 0 ≤ M) (hK : radius ≤ K)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => t+P.rowSlope j l) d H)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ l k, Measurable (b j l k))
    (hbM : ∀ l k s, ‖b j l k s‖ ≤ M)
    (hsupport : ∀ l k s, b j l k s ≠ 0 →
      |s-(t+P.rowSlope j l)| ≤ radius*d)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (Q : Finset P.PacketIndex) (z : ℝ×ℝ) :
    (∑ q ∈ Q.filter (fun q => q.1 = j),
      ‖P.physicalCrossPacketValue alt hAlt t b v g i z q‖) ≤
      P.absoluteConstant*((64*(4*Real.pi)^2)*
        ((P.absoluteConstant*M*((2*K+1)*H:ℕ))*Real.pi^2)) := by
  classical
  calc
    _ ≤ ∑ q ∈ Finset.univ.filter (fun q : P.PacketIndex => q.1 = j),
        ‖P.physicalCrossPacketValue alt hAlt t b v g i z q‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset_filter _ (Finset.subset_univ Q)) (fun _ _ _ => norm_nonneg _)
    _ = ∑ u : (Σ l : P.labels j, Item j l),
        ‖P.physicalCrossPacketValue alt hAlt t b v g i z ⟨j,u⟩‖ := by
      rw [Finset.sum_filter,Fintype.sum_sigma,Finset.sum_eq_single j]
      · simp only [ite_true, if_true]
      · intro k _ hkj
        simp only [hkj,ite_false, if_false,Finset.sum_const_zero]
      · simp
    _ ≤ _ := P.physical_single_scale_raw_synthesis alt hAlt horder i j t d radius M K H
      hd hM hK hlocal b hb hbM hsupport v hv g hg hg1 Finset.univ (z.2-t*z.1) z.1

/-- The fixed selector constants cost only one additional polynomial
power, uniformly before choosing the packet family. -/
theorem eventually_single_scale_budget (q M : ℝ) (hM : 0 ≤ M) (K H : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ C : ℝ, 0 ≤ C → C ≤ L^q →
      C*((64*(4*Real.pi)^2)*((C*M*((2*K+1)*H:ℕ))*Real.pi^2)) ≤ L^(2*q+1) := by
  let A : ℝ := (64*(4*Real.pi)^2)*M*((2*K+1)*H:ℕ)*Real.pi^2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  filter_upwards [eventually_ge_atTop (max 1 A)] with L hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hAL : A ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  intro C hC hCb
  calc
    _ = A*C^2 := by dsimp [A]; ring
    _ ≤ A*(L^q)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hC hCb 2) hA
    _ ≤ L*(L^q)^2 := mul_le_mul_of_nonneg_right hAL (sq_nonneg _)
    _ = L^(2*q+1) := by
      rw [← Real.rpow_mul_natCast hL0.le]
      push_cast
      rw [Real.rpow_add hL0,Real.rpow_one]
      rw [mul_comm q 2]
      ring

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataConeSingleScale
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute single-scale summation is local in angle.  The original
packet family need not have small shear: only the packets being summed
must belong to the displayed reference cone. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem cone_single_scale_cross_packets
    (horder : 6 ≤ P.order)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t s R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
    (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (j : Fin N) (d radius M : ℝ) (K H : ℕ)
    (hd : 0 < d) (hM : 0 ≤ M) (hK : radius ≤ K)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => t+P.rowSlope j l) d H)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ l k, Measurable (b j l k))
    (hbM : ∀ l k x, ‖b j l k x‖ ≤ M)
    (hsupport : ∀ l k x, b j l k x ≠ 0 → |x-(t+P.rowSlope j l)| ≤ radius*d)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (S : Finset P.PacketIndex)
    (hS : ∀ u ∈ S, P.referenceCondition t s R cone w u.1 u.2.1)
    (z : ℝ×ℝ) :
    (∑ u ∈ S.filter (fun u => u.1 = j), ‖P.crossPacketValue alt hAlt t b v g z u‖) ≤
      P.referenceEnvelopeConstant*((64*(4*Real.pi)^2)*
        ((P.referenceEnvelopeConstant*M*((2*K+1)*H:ℕ))*Real.pi^2)) := by
  let Q := P.referenceFamily t s R cone w F hw hcone hF hwide hfrequency
  let orig := P.referenceOriginalLabel t s R cone w
  let selected := (Finset.univ : Finset Q.PacketIndex).filter
    (fun u => (⟨u.1,orig u.1 u.2.1,u.2.2⟩ : P.PacketIndex) ∈ S)
  have hsum := P.sum_referenceFamily_selected t s R cone w F hw hcone hF hwide hfrequency
    (S.filter (fun u => u.1 = j)) (fun u => ‖P.crossPacketValue alt hAlt t b v g z u‖)
    (fun u hu => hS u (Finset.mem_filter.mp hu).1)
  have hfilter : selected.filter (fun u => u.1 = j) =
      (Finset.univ : Finset Q.PacketIndex).filter (fun u =>
        (⟨u.1,orig u.1 u.2.1,u.2.2⟩ : P.PacketIndex) ∈ S.filter (fun u => u.1 = j)) := by
    ext u
    simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hsum, ← hfilter]
  have heq (u : Q.PacketIndex) := P.referenceFamily_crossPacketValue t s R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v g u.1 u.2.1 u.2.2 z
  simp_rw [← heq]
  exact Q.physical_single_scale_cross_packets
    (P.referenceAlt t s R cone w F hw hcone hF hwide hfrequency alt)
    (P.referenceAlt_bound t s R cone w F hw hcone hF hwide hfrequency alt hAlt)
    horder 0 j s d radius M K H hd hM hK
    (P.referenceFamily_localMultiplicity t s R cone w F hw hcone hF hwide hfrequency j d H hlocal)
    (P.referenceSelector t s R cone w F hw hcone hF hwide hfrequency b)
    (fun l k => hb (orig j l) k) (fun l k x => hbM (orig j l) k x)
    (by
      intro l k x hx
      rw [P.referenceFamily_physical_center t s R cone w F hw hcone hF hwide hfrequency]
      exact hsupport (orig j l) k x hx)
    v hv g hg hg1 selected z

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMaskTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source sinc mask is exponentially small outside the prescribed
polynomial enlargement of its top. The estimate includes points on either
coordinate axis and uses the actual even exponent `2 * ceil L`. -/

noncomputable section
namespace LipschitzHilbert

theorem abs_sinc_le_reciprocal_of_large {L x : ℝ} (hL : 0 < L)
    (hx : L ≤ |x|) : |Real.sinc x| ≤ 1/L := by
  have hx0 : x ≠ 0 := abs_pos.mp (hL.trans_le hx)
  rw [Real.sinc_of_ne_zero hx0,abs_div]
  calc
    _ ≤ 1/|x| := div_le_div_of_nonneg_right (Real.abs_sin_le_one x) (abs_nonneg x)
    _ ≤ 1/L := one_div_le_one_div_of_le hL hx

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceResidualMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mask in §4 is dominated by the actual hierarchy weight with
dilation `L^(A+2)`. Consequently the negative weight power in every
residual coefficient costs at most one, uniformly in the spatial point. -/

noncomputable section
namespace LipschitzHilbert

theorem topSincMask_abs_le_one (L A x y : ℝ) : |topSincMask L A x y| ≤ 1 := by
  simpa only [abs_of_nonneg (topSincMask_nonneg L A x y)] using
    topSincMask_le_one L A x y

theorem topSincMask_radial_power {L A x y : ℝ} (hL : 2 ≤ L)
    (hfar : L^(A+2) ≤ |x|+|y|) :
    |topSincMask L A x y| ≤ (L^(A+2)/(|x|+|y|))^(2*⌈L⌉₊) := by
  have hL0 : 0 < L := by linarith
  have hs : 0 < L^A := Real.rpow_pos_of_pos hL0 _
  have hK : 0 < L^(A+2) := Real.rpow_pos_of_pos hL0 _
  have hr : 0 < |x|+|y| := hK.trans_le hfar
  have hscale : 2*L^A ≤ L^(A+2) := by
    rw [Real.rpow_add hL0,Real.rpow_two]
    nlinarith [sq_nonneg (L-2)]
  have hcoord : (|x|+|y|)/2 ≤ |x| ∨ (|x|+|y|)/2 ≤ |y| := by
    by_contra h
    push Not at h
    linarith
  have hh : 0 < (|x|+|y|)/(2*L^A) := by positivity
  have hproduct : |Real.sinc (x/L^A)*Real.sinc (y/L^A)| ≤
      L^(A+2)/(|x|+|y|) := by
    have hratio : 1/((|x|+|y|)/(2*L^A)) = (2*L^A)/(|x|+|y|) := by
      field_simp
    have hsmall : |Real.sinc (x/L^A)*Real.sinc (y/L^A)| ≤
        1/((|x|+|y|)/(2*L^A)) := by
      rw [abs_mul]
      rcases hcoord with hx | hy
      · have hxx : (|x|+|y|)/(2*L^A) ≤ |x/L^A| := by
          rw [abs_div,abs_of_pos hs]
          apply (le_div_iff₀ hs).mpr
          calc
            _ = (|x|+|y|)/2 := by field_simp
            _ ≤ _ := hx
        simpa only [mul_one] using mul_le_mul
          (abs_sinc_le_reciprocal_of_large hh hxx) (Real.abs_sinc_le_one (y/L^A))
          (abs_nonneg _) (by positivity : 0 ≤ 1/((|x|+|y|)/(2*L^A)))
      · have hyy : (|x|+|y|)/(2*L^A) ≤ |y/L^A| := by
          rw [abs_div,abs_of_pos hs]
          apply (le_div_iff₀ hs).mpr
          calc
            _ = (|x|+|y|)/2 := by field_simp
            _ ≤ _ := hy
        simpa only [one_mul] using mul_le_mul
          (Real.abs_sinc_le_one (x/L^A)) (abs_sinc_le_reciprocal_of_large hh hyy)
          (abs_nonneg _) zero_le_one
    rw [hratio] at hsmall
    exact hsmall.trans (div_le_div_of_nonneg_right hscale hr.le)
  simpa only [topSincMask,sincProductMask,abs_pow] using
    pow_le_pow_left₀ (abs_nonneg _) hproduct (2*⌈L⌉₊)

theorem topSincMask_le_topShape {L A D x y : ℝ} (hL : 2 ≤ L)
    (hD : 0 ≤ D) (hdegree : D ≤ ((2*⌈L⌉₊:ℕ):ℝ)) :
    |topSincMask L A x y| ≤ topShape (L^(A+2)) D x y := by
  have hL0 : 0 < L := by linarith
  have hK : 0 < L^(A+2) := Real.rpow_pos_of_pos hL0 _
  have hr : 0 ≤ |x|+|y| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hb : 0 < 1+(|x|+|y|)/L^(A+2) := by positivity
  have hshape : topShape (L^(A+2)) D x y =
      (2/(1+(|x|+|y|)/L^(A+2)))^D := by
    unfold topShape
    rw [Real.rpow_neg hb.le,Real.div_rpow (by norm_num : (0:ℝ) ≤ 2) hb.le]
    rfl
  by_cases hfar : L^(A+2) ≤ |x|+|y|
  · have hr0 : 0 < |x|+|y| := hK.trans_le hfar
    have hratio : 0 < L^(A+2)/(|x|+|y|) := div_pos hK hr0
    have hratio1 : L^(A+2)/(|x|+|y|) ≤ 1 := (div_le_one hr0).mpr hfar
    have hbase : L^(A+2)/(|x|+|y|) ≤ 2/(1+(|x|+|y|)/L^(A+2)) := by
      apply (div_le_div_iff₀ hr0 hb).mpr
      have hcancel : L^(A+2)*(1+(|x|+|y|)/L^(A+2)) = L^(A+2)+(|x|+|y|) := by
        field_simp
      rw [hcancel]
      linarith
    calc
      _ ≤ (L^(A+2)/(|x|+|y|))^(2*⌈L⌉₊) := topSincMask_radial_power hL hfar
      _ = (L^(A+2)/(|x|+|y|))^((2*⌈L⌉₊:ℕ):ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (L^(A+2)/(|x|+|y|))^D :=
        Real.rpow_le_rpow_of_exponent_ge hratio hratio1 hdegree
      _ ≤ (2/(1+(|x|+|y|)/L^(A+2)))^D := Real.rpow_le_rpow hratio.le hbase hD
      _ = _ := hshape.symm
  · have hbase : 1 ≤ 2/(1+(|x|+|y|)/L^(A+2)) := by
      apply (le_div_iff₀ hb).mpr
      have h := (div_le_one hK).mpr (not_le.mp hfar).le
      linarith
    exact (topSincMask_abs_le_one L A x y).trans
      (hshape ▸ Real.one_le_rpow hbase hD)

theorem negative_weight_power_mul_le_one {w q a : ℝ} (hw : 0 < w)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hqw : q ≤ w) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    w^(-a)*q ≤ 1 := by
  by_cases hw1 : w ≤ 1
  · have hp : w^(-a) ≤ w^(-1:ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hw hw1 (by linarith)
    calc
      _ ≤ w^(-1:ℝ)*w := mul_le_mul hp hqw hq (Real.rpow_nonneg hw.le _)
      _ = 1 := by rw [Real.rpow_neg_one,inv_mul_cancel₀ hw.ne']
  · have hp : w^(-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
      (not_le.mp hw1).le (neg_nonpos.mpr ha)
    exact (mul_le_mul hp hq1 hq zero_le_one).trans_eq (mul_one 1)

theorem SlopeBox.residual_mask_weight_bound (T : SlopeBox) {L A D a : ℝ}
    (hL : 2 ≤ L) (hD : 0 ≤ D) (hdegree : D ≤ ((2*⌈L⌉₊:ℕ):ℝ))
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (z : ℝ×ℝ) :
    (T.weight (L^(A+2)) D z)^(-a)*|T.mask L A z| ≤ 1 := by
  have hL0 : 0 < L := by linarith
  apply negative_weight_power_mul_le_one (T.weight_pos (Real.rpow_pos_of_pos hL0 _) D z)
    (abs_nonneg _) (topSincMask_abs_le_one L A (T.horizontal z) (T.transverse z))
    _ ha ha1
  exact topSincMask_le_topShape hL hD hdegree

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceMasked
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact masked amplitudes and residuals survive the local reference change. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (oldSlope newSlope R cone w F : ℝ) (hw : 0<w) (hcone : 0 ≤ cone) (hF : 0≤F)
  (hwide : cone*w≤P.width) (hfrequency : ∀ k, |P.frequency k|≤F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => P.referenceOriginalLabel oldSlope newSlope R cone w

theorem referenceFamily_physicalMaskedValue
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (z : ℝ×ℝ)
    (u : (Q).PacketIndex) :
    (Q).physicalMaskedValue (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))
      newSlope (fun j l => b j (orig j l)) v f (fun j l => T j (orig j l)) L A z u =
    P.physicalMaskedValue alt hAlt oldSlope b v f T L A z ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ := by
  ext k
  simp only [physicalMaskedValue,SourceLabeledLattice.physicalMaskedValue,WithLp.ofLp_toLp]
  rw [P.referenceFamily_physicalMultiplierCoefficient oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency]
  rw [P.referenceFamily_alternate_physicalPacket oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency]

theorem referenceFamily_packetResidual_selected {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (S : Finset P.PacketIndex)
    (hS : ∀ u ∈ S, P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1)
    (grid : AngularGrid) (slope : P.PacketIndex → ℝ) (stop : P.PacketIndex → ℕ)
    (base : P.PacketIndex → E) (transition : ℕ → ℤ → ℂ) (lower upper : ℕ) (cell : ℤ) :
    grid.packetResidual ((Finset.univ : Finset (Q).PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S))
      (fun u => slope ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩)
      (fun u => stop ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩)
      (fun u => base ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩) transition lower upper cell =
      grid.packetResidual S slope stop base transition lower upper cell := by
  have h := P.sum_referenceFamily_selected oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency S
    (fun u => if grid.index lower (slope u) = cell ∧ lower ≤ stop u then
      if stop u < upper then
        grid.packetPathProduct transition lower (stop u) (slope u) • base u else 0
      else 0) hS
  simpa only [AngularGrid.packetResidual,AngularGrid.packetSet,Finset.sum_filter] using h

/-- The physical residual identity includes the exact stopping mass and
each original top mask, after recentering at the reference direction. -/
theorem referenceFamily_physicalSourceResidual_selected {τ : Type*}
    (S : Finset P.PacketIndex)
    (hS : ∀ u ∈ S, P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → (ℝ×ℝ) → ℝ) (assigned : P.PacketIndex → τ)
    (stop : Fin N → ℕ) (T : τ → SlopeBox) (L A alpha : ℝ) (z : ℝ×ℝ)
    (transition : ℕ → ℤ → ℂ) (lower upper : ℕ) (cell : ℤ) :
    grid.packetResidual ((Finset.univ : Finset (Q).PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S))
      (fun u => slope (assigned ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩)) (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cutoff weight
        (fun u => assigned ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩) (fun u => stop u.1)
        ((Q).physicalMaskedValue (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))
          newSlope (fun j l => b j (orig j l)) v f
          (fun j l u => T (assigned ⟨j,⟨orig j l,u⟩⟩)) L A z) alpha z)
      transition lower upper cell =
    grid.packetResidual S (fun u => slope (assigned u)) (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cutoff weight assigned (fun u => stop u.1)
        (P.physicalMaskedValue alt hAlt oldSlope b v f
          (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z) alpha z)
      transition lower upper cell := by
  let value := P.physicalMaskedValue alt hAlt oldSlope b v f
    (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
  have hvalue (u : (Q).PacketIndex) :
      (Q).physicalMaskedValue (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))
        newSlope (fun j l => b j (orig j l)) v f
        (fun j l u => T (assigned ⟨j,⟨orig j l,u⟩⟩)) L A z u =
      value ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ :=
    P.referenceFamily_physicalMaskedValue oldSlope newSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z u
  have hbase :
      grid.sourcePacketBase tops slope precision cutoff weight
        (fun u : (Q).PacketIndex => assigned ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩) (fun u => stop u.1)
        ((Q).physicalMaskedValue (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))
          newSlope (fun j l => b j (orig j l)) v f
          (fun j l u => T (assigned ⟨j,⟨orig j l,u⟩⟩)) L A z) alpha z =
      fun u => grid.sourcePacketBase tops slope precision cutoff weight assigned
        (fun u => stop u.1) value alpha z ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ := by
    funext u
    dsimp only [AngularGrid.sourcePacketBase]
    rw [hvalue]
  rw [hbase]
  exact P.referenceFamily_packetResidual_selected (E := EuclideanSpace ℂ κ) oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency S hS grid (fun u => slope (assigned u)) (fun u => stop u.1)
    (grid.sourcePacketBase tops slope precision cutoff weight assigned (fun u => stop u.1)
      value alpha z) transition lower upper cell

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceResidualSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact short/long splitting of the source residual. A packet at
least as long as the reference top cannot stop before an eligible
reference endpoint. The long part is therefore confined to the last
block and its square costs only its one terminal envelope. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace AngularGrid
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem packetResidual_filter_split (g : AngularGrid) (packets : Finset σ)
    (slope : σ → ℝ) (stop : σ → ℕ) (base : σ → E) (transition : ℕ → ℤ → ℂ)
    (keep : σ → Prop) (lower upper : ℕ) (cell : ℤ) :
    g.packetResidual packets slope stop base transition lower upper cell =
      g.packetResidual (packets.filter keep) slope stop base transition lower upper cell+
        g.packetResidual (packets.filter fun q => ¬keep q) slope stop base transition lower upper cell := by
  simp only [packetResidual,packetSet,Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : keep q <;> simp [hq]

theorem residual_packet_length_lt (g : AngularGrid)
    {w B packetLength referenceLength : ℝ} (hw : 0 < w) (_hB : 0 < B)
    (hp : 0 < packetLength) (hR : 0 < referenceLength)
    (hzero : g.eligible (g.rootWidth/B^2) (w/packetLength) 0)
    {upper : ℕ}
    (hstop : g.lastEligible (g.rootWidth/B^2) (w/packetLength) (div_pos hw hp) < upper)
    (hreference : g.eligible (g.rootWidth/B^2) (w/referenceLength) upper) :
    packetLength < referenceLength := by
  have hnot := g.not_eligible_above_lastEligible (g.rootWidth/B^2) (w/packetLength)
    (div_pos hw hp) hzero hstop
  have hpacket : (g.rootWidth/B^2)/(g.branching:ℝ)^upper < w/packetLength :=
    not_le.mp (fun h => hnot ((g.eligible_iff_precision_le _ _ _).mpr h))
  have href := (g.eligible_iff_precision_le _ _ _).mp hreference
  have hprec : w/referenceLength < w/packetLength := href.trans_lt hpacket
  by_contra hn
  exact (not_le.mpr hprec) (div_le_div_of_nonneg_left hw.le hR (not_lt.mp hn))

/-- The physical long-packet residual vanishes at every block whose
upper endpoint is still eligible for the distinguished reference top. -/
theorem long_packet_residual_eq_zero (g : AngularGrid) (packets : Finset σ)
    (slope length : σ → ℝ) (hlen : ∀ q, 0 < length q)
    {w B referenceLength : ℝ} (hw : 0 < w) (hB : 0 < B) (hR : 0 < referenceLength)
    (hzero : ∀ q ∈ packets, g.eligible (g.rootWidth/B^2) (w/length q) 0)
    (base : σ → E) (transition : ℕ → ℤ → ℂ) (lower upper : ℕ) (cell : ℤ)
    (hreference : g.eligible (g.rootWidth/B^2) (w/referenceLength) upper) :
    g.packetResidual (packets.filter fun q => ¬length q ≤ referenceLength) slope
      (fun q => g.lastEligible (g.rootWidth/B^2) (w/length q) (div_pos hw (hlen q)))
      base transition lower upper cell = 0 := by
  unfold packetResidual
  apply Finset.sum_eq_zero
  intro q hq
  obtain ⟨hq,hstop⟩ := Finset.mem_filter.mp hq
  obtain ⟨hq,_,_⟩ := Finset.mem_filter.mp hq
  obtain ⟨hqp,hlong⟩ := Finset.mem_filter.mp hq
  exact (hlong (g.residual_packet_length_lt hw hB (hlen q) hR (hzero q hqp)
    hstop hreference).le).elim

theorem source_shifted_long_residual_support {K : ℕ} (g : AngularGrid)
    (packets : Finset σ) (slope length : σ → ℝ) (hlen : ∀ q, 0 < length q)
    {w B referenceLength : ℝ} (hw : 0 < w) (hB : 0 < B) (hR : 0 < referenceLength)
    (hK : 0 < K) (shift : Fin K)
    (hzero : ∀ q ∈ packets, g.eligible (g.rootWidth/B^2) (w/length q) 0)
    (base : σ → E) (transition : ℕ → ℤ → ℂ) (pathSlope : ℝ) :
    let count := g.firstIneligibleShiftedBlock (g.rootWidth/B^2) (w/referenceLength)
      (div_pos hw hR) hK shift
    ∀ j : Fin count, j.val+1 < count →
      g.packetResidual (packets.filter fun q => ¬length q ≤ referenceLength) slope
        (fun q => g.lastEligible (g.rootWidth/B^2) (w/length q) (div_pos hw (hlen q)))
        base transition (ShiftedBlocks.endpoint shift j.val) (ShiftedBlocks.endpoint shift (j.val+1))
        (g.index (ShiftedBlocks.endpoint shift j.val) pathSlope) = 0 := by
  dsimp only
  intro j hj
  exact g.long_packet_residual_eq_zero packets slope length hlen hw hB hR hzero base transition
    _ _ _ (g.eligible_before_firstIneligibleShiftedBlock _ _ _ hK shift hj)

end AngularGrid

/-- Adding a term supported at the last block has no depth loss. -/
theorem terminal_perturbation_square_sum {E : Type*} [NormedAddCommGroup E]
    {count : ℕ} (hc : 0 < count) (full short long : Fin count → E)
    (hsplit : ∀ j, full j = short j+long j)
    (hsupport : ∀ j : Fin count, j.val+1 < count → long j = 0)
    {P R : ℝ} (hshort : (∑ j, ‖short j‖^2) ≤ P)
    (hR : 0 ≤ R) (hterminal : ‖long ⟨count-1,by omega⟩‖ ≤ R) :
    (∑ j, ‖full j‖^2) ≤ 2*P+2*R^2 := by
  have hlong : (∑ j, ‖long j‖^2) ≤ R^2 := by
    rw [Finset.sum_eq_single (⟨count-1,by omega⟩ : Fin count)]
    · nlinarith [norm_nonneg (long ⟨count-1,by omega⟩)]
    · intro j _ hj
      have hj' : j.val+1 < count := by
        have hneq : j.val ≠ count-1 := fun h => hj (Fin.ext h)
        omega
      rw [hsupport j hj',norm_zero,zero_pow (by decide : 2 ≠ 0)]
    · simp
  calc
    _ ≤ ∑ j, (2*‖short j‖^2+2*‖long j‖^2) := by
      apply Finset.sum_le_sum
      intro j _
      have ht : ‖full j‖ ≤ ‖short j‖+‖long j‖ := hsplit j ▸ norm_add_le _ _
      nlinarith [norm_nonneg (full j),norm_nonneg (short j),norm_nonneg (long j),
        sq_nonneg (‖short j‖-‖long j‖)]
    _ = 2*(∑ j, ‖short j‖^2)+2*(∑ j, ‖long j‖^2) := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    _ ≤ _ := by linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceResidualEnvelopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed reference packet collection from §§8 and 10 contains
every short residual packet. Positive per-length reference envelopes
therefore dominate the actual block envelopes by subset summation. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace AngularGrid

theorem short_residual_subset_reference {σ : Type*} (g : AngularGrid)
    (packets : Finset σ) (assignedSlope length angle : σ → ℝ)
    (hlen : ∀ q, 0 < length q) {w B referenceLength C referenceSlope : ℝ}
    (hw : 0 < w) (hB : 0 < B)
    (hzero : ∀ q ∈ packets, g.eligible (g.rootWidth/B^2) (w/length q) 0)
    (hangle : ∀ q ∈ packets, |angle q-assignedSlope q| ≤ C*(w/length q))
    (lower upper : ℕ) (hwidth : g.width lower ≤ B*g.width upper) :
    (g.packetSet (packets.filter fun q => length q ≤ referenceLength) assignedSlope
      (fun q => g.lastEligible (g.rootWidth/B^2) (w/length q) (div_pos hw (hlen q)))
      lower (g.index lower referenceSlope)).filter
        (fun q => g.lastEligible (g.rootWidth/B^2) (w/length q) (div_pos hw (hlen q)) < upper) ⊆
      sourceReferencePackets packets length angle referenceLength referenceSlope (C+B^3) w := by
  intro q hq
  obtain ⟨hq,hupper⟩ := Finset.mem_filter.mp hq
  obtain ⟨hq,hcell,hlower⟩ := Finset.mem_filter.mp hq
  obtain ⟨hqp,hshort⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨hqp,hshort,
    g.source_parent_residual_cone hw hB (hlen q) (hzero q hqp) ⟨hlower,hupper⟩ hwidth
      hcell (hangle q hqp)⟩

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceParentResidualReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A square estimate uses the parent residual cone. Its exact packet
restriction can be recentered at the path slope; no equality with the
original reference slope is required. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
namespace AngularGrid
attribute [local instance] Classical.propDecidable

theorem packetResidual_eq_of_support_subset {σ E : Type*} [AddCommMonoid E] [Module ℂ E]
    (g : AngularGrid) (small big : Finset σ) (slope : σ → ℝ) (stop : σ → ℕ)
    (base : σ → E) (transition : ℕ → ℤ → ℂ) (lower upper : ℕ) (cell : ℤ)
    (hsub : small ⊆ big)
    (hsupport : ((g.packetSet big slope stop lower cell).filter
      (fun q => stop q < upper)) ⊆ small) :
    g.packetResidual small slope stop base transition lower upper cell =
      g.packetResidual big slope stop base transition lower upper cell := by
  unfold packetResidual
  apply Finset.sum_congr
  · ext q
    simp only [packetSet,Finset.mem_filter]
    constructor
    · rintro ⟨⟨hq,hcell,hlo⟩,hhi⟩
      exact ⟨⟨hsub hq,hcell,hlo⟩,hhi⟩
    · rintro ⟨⟨hq,hcell,hlo⟩,hhi⟩
      exact ⟨⟨hsupport (Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hq,hcell,hlo⟩,hhi⟩),hcell,hlo⟩,hhi⟩
  · intro q _
    rfl

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataParentResidualReference
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
namespace PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- Every actual short residual is unchanged after restriction to the
fixed parent cone. This includes the terminal block. -/
theorem short_parent_residual_eq {τ E : Type*} [AddCommMonoid E] [Module ℂ E]
    (P : PacketLatticeData N κ Label Item) (grid : AngularGrid)
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (slope : τ → ℝ)
    (t R C B w : ℝ) (hw : 0 < w) (hB : 0 < B)
    (hzero : ∀ j, grid.eligible (grid.rootWidth/B^2) (w/P.length j) 0)
    (hangle : ∀ q ∈ packets,
      |t+P.rowSlope q.1 q.2.1-slope (assigned q)| ≤ C*(w/P.length q.1))
    (base : P.PacketIndex → E) (transition : ℕ → ℤ → ℂ)
    (lower upper : ℕ) (pathSlope : ℝ)
    (hwidth : grid.width lower ≤ B*grid.width upper) :
    let stop := fun q : P.PacketIndex => grid.lastEligible (grid.rootWidth/B^2)
      (w/P.length q.1) (div_pos hw (P.length_pos q.1))
    let short := packets.filter (fun q => P.length q.1 ≤ R)
    let selected := sourceReferencePackets packets (fun q => P.length q.1)
      (fun q => t+P.rowSlope q.1 q.2.1) R pathSlope (C+B^3) w
    grid.packetResidual selected (fun q => slope (assigned q)) stop base transition
      lower upper (grid.index lower pathSlope) =
    grid.packetResidual short (fun q => slope (assigned q)) stop base transition
      lower upper (grid.index lower pathSlope) := by
  dsimp only
  apply grid.packetResidual_eq_of_support_subset
  · intro q hq
    obtain ⟨hqp,hshort,_⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨hqp,hshort⟩
  · exact grid.short_residual_subset_reference packets (fun q => slope (assigned q))
      (fun q => P.length q.1) (fun q => t+P.rowSlope q.1 q.2.1)
      (fun q => P.length_pos q.1) hw hB (fun q _ => hzero q.1) hangle lower upper hwidth

end PacketLatticeData
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceRestrictedPacketAmplitude
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The angular sums of a literal packet restriction are the original
selected sums. Stopping levels, top assignments, hierarchy masses and
analyzing coefficients are unchanged. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- The residual is transported exactly, including both stopping filters. -/
theorem restrictPackets_packetResidual {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (Q : Finset P.PacketIndex) (grid : AngularGrid) (slope : P.PacketIndex → ℝ)
    (stop : P.PacketIndex → ℕ) (base : P.PacketIndex → E)
    (transition : ℕ → ℤ → ℂ) (lower upper : ℕ) (cell : ℤ) :
    grid.packetResidual (Finset.univ : Finset (P.restrictPackets Q).PacketIndex)
      (fun u => slope ⟨u.1,⟨u.2.1,u.2.2.val⟩⟩)
      (fun u => stop ⟨u.1,⟨u.2.1,u.2.2.val⟩⟩)
      (fun u => base ⟨u.1,⟨u.2.1,u.2.2.val⟩⟩) transition lower upper cell =
      grid.packetResidual Q slope stop base transition lower upper cell := by
  unfold AngularGrid.packetResidual AngularGrid.packetSet
  simp only [Finset.sum_filter]
  exact P.sum_restrictPackets Q (fun u =>
    if grid.index lower (slope u) = cell ∧ lower ≤ stop u then
      if stop u < upper then
        grid.packetPathProduct transition lower (stop u) (slope u) • base u else 0
    else 0)

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

/-- Physical residual transport preserves the original analyzing integral
and the same hierarchy mass at every packet's stopping level. -/
theorem restrictPackets_physicalSourceResidual {τ : Type*}
    (Q : Finset P.PacketIndex) (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → (ℝ×ℝ) → ℝ) (assigned : P.PacketIndex → τ)
    (stop : Fin N → ℕ) (T : τ → SlopeBox) (L A alpha : ℝ) (z : ℝ×ℝ)
    (transition : ℕ → ℤ → ℂ) (lower upper : ℕ) (cell : ℤ) :
    grid.packetResidual (Finset.univ : Finset (P.restrictPackets Q).PacketIndex)
      (fun u => slope (assigned ⟨u.1,⟨u.2.1,u.2.2.val⟩⟩)) (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cutoff weight
        (fun u => assigned ⟨u.1,⟨u.2.1,u.2.2.val⟩⟩) (fun u => stop u.1)
        ((P.restrictPackets Q).physicalMaskedValue (P.restrictedAlternate alt Q)
          (P.restrictedAlternate_bound alt hAlt Q) t b v f
          (fun j l u => T (assigned ⟨j,⟨l,u.val⟩⟩)) L A z) alpha z)
      transition lower upper cell =
    grid.packetResidual Q (fun u => slope (assigned u)) (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cutoff weight assigned (fun u => stop u.1)
        (P.physicalMaskedValue alt hAlt t b v f
          (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z) alpha z)
      transition lower upper cell := by
  let value := P.physicalMaskedValue alt hAlt t b v f
    (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
  have hvalue (u : (P.restrictPackets Q).PacketIndex) :
      (P.restrictPackets Q).physicalMaskedValue (P.restrictedAlternate alt Q)
        (P.restrictedAlternate_bound alt hAlt Q) t b v f
        (fun j l u => T (assigned ⟨j,⟨l,u.val⟩⟩)) L A z u =
      value ⟨u.1,⟨u.2.1,u.2.2.val⟩⟩ := rfl
  have hbase :
      grid.sourcePacketBase tops slope precision cutoff weight
        (fun u : (P.restrictPackets Q).PacketIndex => assigned ⟨u.1,⟨u.2.1,u.2.2.val⟩⟩)
        (fun u => stop u.1)
        ((P.restrictPackets Q).physicalMaskedValue (P.restrictedAlternate alt Q)
          (P.restrictedAlternate_bound alt hAlt Q) t b v f
          (fun j l u => T (assigned ⟨j,⟨l,u.val⟩⟩)) L A z) alpha z =
      fun u => grid.sourcePacketBase tops slope precision cutoff weight assigned
        (fun u => stop u.1) value alpha z ⟨u.1,⟨u.2.1,u.2.2.val⟩⟩ := by
    funext u
    dsimp only [AngularGrid.sourcePacketBase]
    rw [hvalue]
  rw [hbase]
  exact P.restrictPackets_packetResidual Q grid (fun u => slope (assigned u))
    (fun u => stop u.1)
    (grid.sourcePacketBase tops slope precision cutoff weight assigned (fun u => stop u.1)
      value alpha z) transition lower upper cell

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledGoodEvents
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable reference events for the original error, positive main
square and full masked variation. All three thresholds are fixed before
the angular path or mass cutoff is selected. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A e s r : ℝ)

theorem physicalReferenceBad_compl_bounds (z : ℝ×ℝ)
    (hz : z ∉ P.physicalReferenceBad alt hAlt t a b v g T L A e s r) :
    P.physicalAngularError t a b v g z < L^e ∧
    P.physicalMainSquareOnPlane t a b v g z < L^s ∧
    P.physicalMaskedVariation alt hAlt t b v g T L A (z.2-t*z.1) z.1 < L^r := by
  have h (i : Fin 3) : z ∉ P.physicalReferenceEvent alt hAlt t a b v g T L A e s r i :=
    fun hi => hz (mem_iUnion.mpr ⟨i,hi⟩)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [physicalReferenceEvent,ite_true, if_true,Set.mem_ofPred_eq] at h0
  simp only [physicalReferenceEvent,show (1 : Fin 3) ≠ 0 by decide,ite_false, if_false,ite_true, if_true,
    Set.mem_ofPred_eq] at h1
  simp only [physicalReferenceEvent,show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide,ite_false, if_false,Set.mem_ofPred_eq] at h2
  exact ⟨lt_of_not_ge h0,lt_of_not_ge h1,lt_of_not_ge h2⟩

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePhysicalResidualSquare
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original masked physical residual blocks inherit the square
bound from the original analyzing/alternate-synthesis decomposition. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

/-- Actual top masks and original physical packets satisfy the marked
residual square estimate; the analyzing coefficient is unchanged. -/
theorem physical_masked_packet_residual_square_polynomial {τ : Type*}
    (horder : 6 ≤ P.order) (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (hf : Measurable f) (hf1 : ∀ z, ‖f z‖ ≤ 1)
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → ℝ×ℝ → ℝ)
    (hp : ∀ T ∈ tops, 0 ≤ precision T) (hw : ∀ T z, 0 < weight T z)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (hz : ∀ k, 0 ≤ (phase k).re) (alpha : ℝ) (ha : 0 ≤ alpha) (z : ℝ×ℝ)
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (stop : Fin N → ℕ) (T : τ → SlopeBox) (L A : ℝ)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (he : ∀ q ∈ packets, grid.eligible cutoff (precision (assigned q)) (stop q.1))
    (C : ℝ) (hC : 0 ≤ C) (hmask : ∀ top ∈ tops, weight top z^(-alpha)*‖((T top).mask L A z:ℂ)‖ ≤ C)
    (level : ℕ → ℕ) (hlevel : StrictMono level) (count : ℕ) (pathSlope : ℝ)
    (R : ℝ) (hR : 0 ≤ R)
    (hcard : ∀ j < count,
      ((residualLengthSet stop (level j) (level (j+1))).card:ℝ) ≤ R)
    (c q p r : ℝ) (hL : 6 ≤ L) (hr : 0 ≤ r)
    (hCb : C ≤ L^c) (hAb : P.absoluteConstant ≤ L^q) (hRb : R ≤ L^r)
    (hError : P.physicalAngularError t a b v f z ≤ L^p)
    (hMain : P.physicalMainSquare t a b v f (z.2-t*z.1) z.1 ≤ L^p) :
    let value := P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
    (∑ j : Fin count, ‖grid.packetResidual packets (fun q => slope (assigned q))
      (fun q => stop q.1)
      (grid.sourcePacketBase tops slope precision cutoff weight assigned (fun q => stop q.1)
        value alpha z)
      (grid.sourceTransition tops slope precision cutoff weight K gap phase z)
      (level j.val) (level (j.val+1)) (grid.index (level j.val) pathSlope)‖^2) ≤
        (L^(c+q+p+r+1))^2 := by
  let mask := fun top => ((T top).mask L A z:ℂ)
  have hvalue : P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z =
      fun q => mask (assigned q) • P.physicalCrossPacketValue alt hAlt t b v f 0 z q := by
    funext q
    rcases q with ⟨j,⟨l,u⟩⟩
    have hpoint : (z.1,z.2-t*z.1+t*z.1) = z := by
      apply Prod.ext
      · rfl
      · dsimp
        ring
    have h := P.physicalMaskedValue_eq_cross alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A (z.2-t*z.1) z.1 ⟨j,⟨l,u⟩⟩
    rw [hpoint] at h
    rw [h]
    ext k
    simp only [mask,PiLp.smul_apply,Complex.real_smul,smul_eq_mul]
  dsimp only
  rw [hvalue]
  exact P.physical_cross_packet_residual_square_polynomial alt hAlt horder 0 t a
    b hb hb1 v hv f hf hf1 grid tops slope precision cutoff weight hp hw hK gap phase hz
    alpha ha z packets assigned stop mask hassigned he C hC hmask level hlevel count
    pathSlope R hR hcard L c q p r hL hr hCb hAb hRb hError hMain

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePhysicalGoodResidual
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At a good physical reference point the original top-masked residual
blocks have a polynomial square bound, with the mask normalization
proved from the actual hierarchy weights. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

/-- The actual good reference event discharges the error/main envelopes;
the exponent is fixed independently of the later mass cutoff. -/
theorem physical_good_reference_residual_square {τ : Type*}
    (horder : 6 ≤ P.order) (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k u, ‖b j l k u‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (hf : Measurable f) (hf1 : ∀ z, ‖f z‖ ≤ 1)
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (T : τ → SlopeBox) (L A D q r s : ℝ)
    (hL : 6 ≤ L) (hD : 0 ≤ D) (hdegree : D ≤ ((2*⌈L⌉₊:ℕ):ℝ))
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hAb : P.absoluteConstant ≤ L^q)
    (hp : ∀ top ∈ tops, 0 ≤ precision top)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (hz : ∀ k, 0 ≤ (phase k).re) (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (z : ℝ×ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (stop : Fin N → ℕ) (hassigned : ∀ u ∈ packets, assigned u ∈ tops)
    (he : ∀ u ∈ packets, grid.eligible cutoff (precision (assigned u)) (stop u.1))
    (level : ℕ → ℕ) (hlevel : StrictMono level) (count : ℕ) (pathSlope R : ℝ)
    (hR : 0 ≤ R) (hRb : R ≤ L^r)
    (hcard : ∀ j < count,
      ((residualLengthSet stop (level j) (level (j+1))).card:ℝ) ≤ R)
    (hgood : z ∉ P.physicalReferenceBad alt hAlt t a b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A (q+8) (2*q+9) s) :
    let weight := fun top z => (T top).weight (L^(A+2)) D z
    let value := P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
    (∑ j : Fin count, ‖grid.packetResidual packets (fun u => slope (assigned u))
      (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cutoff weight assigned (fun u => stop u.1)
        value alpha z)
      (grid.sourceTransition tops slope precision cutoff weight K gap phase z)
      (level j.val) (level (j.val+1)) (grid.index (level j.val) pathSlope)‖^2) ≤
        (L^(3*q+r+10))^2 := by
  let weight := fun top z => (T top).weight (L^(A+2)) D z
  have hL0 : 0 < L := by linarith
  have hw (top : τ) (z : ℝ×ℝ) : 0 < weight top z :=
    (T top).weight_pos (Real.rpow_pos_of_pos hL0 _) D z
  have hm (top : τ) (_htop : top ∈ tops) :
      weight top z^(-alpha)*‖((T top).mask L A z:ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using
      (T top).residual_mask_weight_bound (by linarith) hD hdegree ha ha1 z
  have hbounds := P.physicalReferenceBad_compl_bounds alt hAlt t a b v f
    (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A (q+8) (2*q+9) s z hgood
  have hError : P.physicalAngularError t a b v f z ≤ L^(2*q+9) :=
    hbounds.1.le.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
  have hMain : P.physicalMainSquare t a b v f (z.2-t*z.1) z.1 ≤ L^(2*q+9) :=
    hbounds.2.1.le
  have h := P.physical_masked_packet_residual_square_polynomial alt hAlt horder t a
    b hb hb1 v hv f hf hf1 grid tops slope precision cutoff weight hp hw hK gap phase hz
    alpha ha z packets assigned stop T L A hassigned he 1 zero_le_one hm level hlevel count
    pathSlope R hR hcard 0 q (2*q+9) r hL hr (by simp) hAb hRb hError hMain
  simpa only [zero_add,show q+(2*q+9)+r+1 = 3*q+r+10 by ring] using h

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceResidualBlockBudget
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's rounded block parameters bound the number of
residual lengths polynomially, uniformly over the packet family. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

/-- The actual integer exponent of the source branching is at most L²
for large L; no bound depends on the number of packet scales. -/
theorem eventually_source_block_length_budget :
    ∀ᶠ L : ℝ in atTop,
      ((SourceParameters.stepExponent L*SourceParameters.blockCount L:ℕ):ℝ) ≤ L^(2:ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [SourceParameters.eventually_branching_separation,
    eventually_ge_atTop (max 1 (1/(100*Real.log 2)))] with L hsep hlarge
  have hL : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hc : 1 ≤ L*(100*Real.log 2) :=
    (div_le_iff₀ (by positivity : 0 < 100*Real.log 2)).mp ((le_max_right _ _).trans hlarge)
  have hlogB : Real.log (SourceParameters.branching L) =
      ((SourceParameters.stepExponent L*SourceParameters.blockCount L:ℕ):ℝ)*Real.log 2 := by
    rw [source_branching_eq_two_pow,Real.log_pow]
  have hlog := Real.log_le_log (pow_pos (SourceParameters.branching_pos L) 100) hsep
  rw [Real.log_pow,Real.log_exp,hlogB] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hp : L^(9/10:ℝ) ≤ L := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL
      (by norm_num : (9/10:ℝ) ≤ 1)
  have hm := mul_le_mul_of_nonneg_left hc hL0.le
  rw [Real.rpow_two]
  apply (mul_le_mul_iff_right₀ (by positivity : 0 < 100*Real.log 2)).mp
  nlinarith

namespace SourceLabeledLattice

/-- Every shifted residual block of an actual dyadic packet family has
at most L² lengths for sufficiently large L. -/
theorem eventually_shifted_residual_length_budget :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (grid : AngularGrid),
      (grid.branching:ℝ) = SourceParameters.step L →
    ∀ (_hK : 0 < SourceParameters.blockCount L) (shift : Fin (SourceParameters.blockCount L))
      (w : ℝ) (hw : 0 < w),
      (∀ j : Fin N, grid.eligible (grid.rootWidth/(SourceParameters.branching L)^2)
        (w/P.length j) 0) →
    ∀ block : ℕ,
      let stop := fun j : Fin N => grid.lastEligible
        (grid.rootWidth/(SourceParameters.branching L)^2) (w/P.length j)
        (div_pos hw (P.length_pos j))
      ((residualLengthSet stop (ShiftedBlocks.endpoint shift block)
        (ShiftedBlocks.endpoint shift (block+1))).card:ℝ) ≤ L^(2:ℝ) := by
  filter_upwards [eventually_source_block_length_budget] with L hbudget
  intro N κ Label Item _ _ P grid hbranch hK shift w hw hzero block
  have hcard := grid.source_shifted_residual_length_card L hbranch hK shift hw
    P.topLength_pos hzero block
  have hc : ((residualLengthSet
      (fun j : Fin N => grid.lastEligible (grid.rootWidth/(SourceParameters.branching L)^2)
        (w/P.length j) (div_pos hw (P.length_pos j)))
      (ShiftedBlocks.endpoint shift block) (ShiftedBlocks.endpoint shift (block+1))).card:ℝ) ≤
      ((SourceParameters.stepExponent L*SourceParameters.blockCount L:ℕ):ℝ) := by
    dsimp only [SourceLabeledLattice.length]
    exact_mod_cast hcard
  exact hc.trans hbudget

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePhysicalShiftedResidual
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual shifted angular blocks satisfy the good-reference
residual square estimate with a fixed polynomial exponent. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.SourceLabeledLattice

/-- Source dyadic stopping and the good event discharge the block count,
mask normalization and positive reference envelopes simultaneously. -/
theorem eventually_physical_shifted_good_reference_residual_square
    (q D : ℝ) (hq : 0 ≤ q) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), 6 ≤ P.order → P.absoluteConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k u, ‖b j l k u‖ ≤ 1) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (τ : Type*) (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
      (T : τ → SlopeBox) (A s : ℝ) (w : ℝ) (hw : 0 < w),
      (grid.branching:ℝ) = SourceParameters.step L →
    ∀ (_hK : 0 < SourceParameters.blockCount L) (shift : Fin (SourceParameters.blockCount L)),
      (∀ j : Fin N, grid.eligible (grid.rootWidth/(SourceParameters.branching L)^2)
        (w/P.length j) 0) → (∀ top ∈ tops, 0 ≤ precision top) →
    let cut := grid.rootWidth/(SourceParameters.branching L)^2
    let stop := fun j : Fin N => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let weight := fun top z => (T top).weight (L^(A+2)) D z
    ∀ (phase : ℕ → ℂ), (∀ k, 0 ≤ (phase k).re) →
    ∀ (alpha : ℝ), 0 ≤ alpha → alpha ≤ 1 →
    ∀ (z : ℝ×ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
      (∀ u ∈ packets, assigned u ∈ tops) →
      (∀ u ∈ packets, grid.eligible cut (precision (assigned u)) (stop u.1)) →
    ∀ (count : ℕ) (pathSlope : ℝ),
      z ∉ P.physicalReferenceBad alt hAlt t a b v f
        (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A (q+8) (2*q+9) s →
    let value := P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
    (∑ j : Fin count, ‖grid.packetResidual packets (fun u => slope (assigned u))
      (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cut weight assigned (fun u => stop u.1) value alpha z)
      (grid.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
        (grid.sourceBoundaryGap L) phase z)
      (ShiftedBlocks.endpoint shift j.val) (ShiftedBlocks.endpoint shift (j.val+1))
      (grid.index (ShiftedBlocks.endpoint shift j.val) pathSlope)‖^2) ≤
        (L^(3*q+12))^2 := by
  filter_upwards [eventually_shifted_residual_length_budget,
    eventually_ge_atTop (max 6 D)] with L hbudget hlarge
  have hL : 6 ≤ L := (le_max_left _ _).trans hlarge
  have hdegree : D ≤ ((2*⌈L⌉₊:ℕ):ℝ) := by
    have hceil : L ≤ (⌈L⌉₊:ℝ) := Nat.le_ceil L
    have hDL : D ≤ L := (le_max_right _ _).trans hlarge
    push_cast
    linarith
  intro N κ Label Item _ _ P horder hP alt hAlt t a b hb hb1 v hv f hf hf1
    τ grid tops slope precision T A s w hw hbranch hK shift hzero hp
  dsimp only
  intro phase hz alpha ha ha1 z packets assigned hassigned he count pathSlope hgood
  let cut := grid.rootWidth/(SourceParameters.branching L)^2
  let stop := fun j : Fin N => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
  have hcard (j : ℕ) (_hj : j < count) :
      ((residualLengthSet stop (ShiftedBlocks.endpoint shift j)
        (ShiftedBlocks.endpoint shift (j+1))).card:ℝ) ≤ L^(2:ℝ) :=
    hbudget N κ Label Item P grid hbranch hK shift w hw hzero j
  have h := P.physical_good_reference_residual_square alt hAlt horder t a b hb hb1 v hv
    f hf hf1 grid tops slope precision cut T L A D q 2 s hL hD hdegree hq (by norm_num) hP hp
    hK (grid.sourceBoundaryGap L) phase hz alpha ha ha1 z packets assigned stop hassigned he
    (ShiftedBlocks.endpoint shift) (ShiftedBlocks.endpoint_strictMono hK shift)
    count pathSlope (L^(2:ℝ)) (Real.rpow_nonneg (by linarith) _) le_rfl hcard hgood
  simpa only [show 3*q+2+10 = 3*q+12 by ring] using h

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSelectedResidualSquare
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A good event for the selected physical reference family controls
the original selected packet residuals, with the same hierarchy masses. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.SourceLabeledLattice

theorem eventually_selected_physical_shifted_residual_square
    (q D : ℝ) (hq : 0 ≤ q) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), 6 ≤ P.order → P.absoluteConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k u, ‖b j l k u‖ ≤ 1) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (τ : Type*) (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
      (T : τ → SlopeBox) (A s : ℝ) (w : ℝ) (hw : 0 < w),
      (grid.branching:ℝ) = SourceParameters.step L →
    ∀ (_hK : 0 < SourceParameters.blockCount L) (shift : Fin (SourceParameters.blockCount L)),
      (∀ j : Fin N, grid.eligible (grid.rootWidth/(SourceParameters.branching L)^2)
        (w/P.length j) 0) → (∀ top ∈ tops, 0 ≤ precision top) →
    let cut := grid.rootWidth/(SourceParameters.branching L)^2
    let stop := fun j : Fin N => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let weight := fun top z => (T top).weight (L^(A+2)) D z
    ∀ (phase : ℕ → ℂ), (∀ k, 0 ≤ (phase k).re) →
    ∀ (alpha : ℝ), 0 ≤ alpha → alpha ≤ 1 →
    ∀ (z : ℝ×ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
      (∀ u ∈ packets, assigned u ∈ tops) →
      (∀ u ∈ packets, grid.eligible cut (precision (assigned u)) (stop u.1)) →
    ∀ (count : ℕ) (pathSlope : ℝ),
      z ∉ (P.restrictPackets packets).physicalReferenceBad
        (P.restrictedAlternate alt packets) (P.restrictedAlternate_bound alt hAlt packets)
        t a b v f (fun j l u => T (assigned ⟨j,⟨l,u.val⟩⟩)) L A (q+8) (2*q+9) s →
    let value := P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
    (∑ j : Fin count, ‖grid.packetResidual packets (fun u => slope (assigned u))
      (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cut weight assigned (fun u => stop u.1) value alpha z)
      (grid.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
        (grid.sourceBoundaryGap L) phase z)
      (ShiftedBlocks.endpoint shift j.val) (ShiftedBlocks.endpoint shift (j.val+1))
      (grid.index (ShiftedBlocks.endpoint shift j.val) pathSlope)‖^2) ≤
        (L^(3*q+12))^2 := by
  filter_upwards [eventually_physical_shifted_good_reference_residual_square q D hq hD]
    with L hbound
  intro N κ Label Item _ _ P horder hP alt hAlt t a b hb hb1 v hv f hf hf1
    τ grid tops slope precision T A s w hw hbranch hK shift hzero hp
  dsimp only
  intro phase hz alpha ha ha1 z packets assigned hassigned he count pathSlope hgood
  let Q := P.restrictPackets packets
  let own : Q.PacketIndex → τ := fun u => assigned ⟨u.1,⟨u.2.1,u.2.2.val⟩⟩
  have hown (u : Q.PacketIndex) (_hu : u ∈ Finset.univ) : own u ∈ tops :=
    hassigned _ (P.restrictedPacketEquiv packets u).property
  have helig (u : Q.PacketIndex) (_hu : u ∈ Finset.univ) :
      grid.eligible (grid.rootWidth/(SourceParameters.branching L)^2)
        (precision (own u))
        (grid.lastEligible (grid.rootWidth/(SourceParameters.branching L)^2)
          (w/Q.length u.1) (div_pos hw (Q.length_pos u.1))) :=
    he _ (P.restrictedPacketEquiv packets u).property
  have hs := hbound N κ Label (P.RestrictedPacketItem packets) Q horder hP
    (P.restrictedAlternate alt packets) (P.restrictedAlternate_bound alt hAlt packets)
    t a b hb hb1 v hv f hf hf1 τ grid tops slope precision T A s w hw hbranch hK shift
    hzero hp phase hz alpha ha ha1 z Finset.univ own hown helig count pathSlope hgood
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun u : EuclideanSpace ℂ κ => ‖u‖^2)
  exact (P.restrictPackets_physicalSourceResidual alt hAlt packets t b v f grid tops slope
    precision (grid.rootWidth/(SourceParameters.branching L)^2)
    (fun top z => (T top).weight (L^(A+2)) D z) assigned
    (fun i => grid.lastEligible (grid.rootWidth/(SourceParameters.branching L)^2)
      (w/P.length i) (div_pos hw (P.length_pos i))) T L A alpha z
    (grid.sourceTransition tops slope precision (grid.rootWidth/(SourceParameters.branching L)^2)
      (fun top z => (T top).weight (L^(A+2)) D z) (SourceParameters.blockCount L)
      (grid.sourceBoundaryGap L) phase z)
    (ShiftedBlocks.endpoint shift j.val) (ShiftedBlocks.endpoint shift (j.val+1))
    (grid.index (ShiftedBlocks.endpoint shift j.val) pathSlope)).symm

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataParentResidualSquare
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square-reference event is taken on the literal parent cone and
in the path-top reference direction. Its good event controls the original
short residuals without an equality of reference slopes. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_physical_parent_short_square (q D : ℝ) (hq : 0 ≤ q) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item), 6 ≤ P.order → P.referenceEnvelopeConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t pathSlope R C F w a : ℝ) (hw : 0 < w)
      (hcone : 0 ≤ C+(SourceParameters.branching L)^3) (hF : 0 ≤ F)
      (hwide : (C+(SourceParameters.branching L)^3)*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (τ : Type*) (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
      (T : τ → SlopeBox) (A s : ℝ),
      (grid.branching:ℝ) = SourceParameters.step L →
    ∀ (_hK : 0 < SourceParameters.blockCount L) (shift : Fin (SourceParameters.blockCount L)),
      (∀ j : Fin N, grid.eligible (grid.rootWidth/(SourceParameters.branching L)^2)
        (w/P.length j) 0) → (∀ top ∈ tops, 0 ≤ precision top) →
    let cut := grid.rootWidth/(SourceParameters.branching L)^2
    let stop := fun j : Fin N => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let weight := fun top z => (T top).weight (L^(A+2)) D z
    ∀ (phase : ℕ → ℂ), (∀ k, 0 ≤ (phase k).re) →
    ∀ (alpha : ℝ), 0 ≤ alpha → alpha ≤ 1 →
    ∀ (z : ℝ×ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
      (∀ u ∈ packets, assigned u ∈ tops) →
      (∀ u ∈ packets, grid.eligible cut (precision (assigned u)) (stop u.1)) →
      (∀ u ∈ packets, |t+P.rowSlope u.1 u.2.1-slope (assigned u)| ≤ C*(w/P.length u.1)) →
    let cone := C+(SourceParameters.branching L)^3
    let S := sourceReferencePackets packets (fun u => P.length u.1)
      (fun u => t+P.rowSlope u.1 u.2.1) R pathSlope cone w
    let Q := P.referenceFamily t pathSlope R cone w F hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel t pathSlope R cone w
    let selected := (Finset.univ : Finset Q.PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S)
    z ∉ (Q.restrictPackets selected).physicalReferenceBad
      (Q.restrictedAlternate (fun j l => alt j (orig j l)) selected)
      (Q.restrictedAlternate_bound (fun j l => alt j (orig j l))
        (fun j l => hAlt j (orig j l)) selected)
      pathSlope a (fun j l => b j (orig j l)) v f
      (fun j l u => T (assigned ⟨j,⟨orig j l,u.val⟩⟩)) L A (q+8) (2*q+9) s →
    ∀ count : ℕ,
    let value := P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
    (∑ j : Fin count, ‖grid.packetResidual (packets.filter (fun u => P.length u.1 ≤ R))
      (fun u => slope (assigned u)) (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cut weight assigned (fun u => stop u.1) value alpha z)
      (grid.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
        (grid.sourceBoundaryGap L) phase z)
      (ShiftedBlocks.endpoint shift j.val) (ShiftedBlocks.endpoint shift (j.val+1))
      (grid.index (ShiftedBlocks.endpoint shift j.val) pathSlope)‖^2) ≤ (L^(3*q+12))^2 := by
  filter_upwards [SourceLabeledLattice.eventually_selected_physical_shifted_residual_square q D hq hD] with L hbound
  intro N κ Label Item _ _ P horder hP alt hAlt t pathSlope R C F w a hw hcone hF
    hwide hfrequency b hb hb1 v hv f hf hf1 τ grid tops slope precision T A s hbranch hK shift
    hzero hp cut stop weight phase hz alpha ha ha1 z packets assigned hassigned he hangle
    cone S Q orig selected hgood count value
  let own := fun u : Q.PacketIndex => assigned ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩
  let altQ := fun j (l : Q.labels j) => alt j (orig j l)
  have hAltQ := fun j (l : Q.labels j) => hAlt j (orig j l)
  have hS (u : P.PacketIndex) (hu : u ∈ S) :
      P.referenceCondition t pathSlope R cone w u.1 u.2.1 := by
    obtain ⟨_,hlen,hangle⟩ := Finset.mem_filter.mp hu
    exact ⟨hlen,by simpa only [mul_div_assoc] using hangle⟩
  have hmap (u : Q.PacketIndex) (hu : u ∈ selected) :
      (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ packets :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hu).2).1
  have hs := hbound N κ Label Item Q horder hP altQ hAltQ pathSlope a
    (fun j l => b j (orig j l)) (fun j l => hb j (orig j l)) (fun j l => hb1 j (orig j l))
    v hv f hf hf1 τ grid tops slope precision T A s w hw hbranch hK shift
    hzero hp phase hz alpha ha ha1 z selected own
    (fun u hu => hassigned _ (hmap u hu)) (fun u hu => he _ (hmap u hu)) count pathSlope hgood
  have heq (j : Fin count) :
      grid.packetResidual selected (fun u => slope (own u)) (fun u => stop u.1)
        (grid.sourcePacketBase tops slope precision cut weight own (fun u => stop u.1)
          (Q.physicalMaskedValue altQ hAltQ pathSlope (fun j l => b j (orig j l)) v f
            (fun j l u => T (own ⟨j,⟨l,u⟩⟩)) L A z) alpha z)
        (grid.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
          (grid.sourceBoundaryGap L) phase z)
        (ShiftedBlocks.endpoint shift j.val) (ShiftedBlocks.endpoint shift (j.val+1))
        (grid.index (ShiftedBlocks.endpoint shift j.val) pathSlope) =
      grid.packetResidual (packets.filter (fun u => P.length u.1 ≤ R))
        (fun u => slope (assigned u)) (fun u => stop u.1)
        (grid.sourcePacketBase tops slope precision cut weight assigned (fun u => stop u.1) value alpha z)
        (grid.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
          (grid.sourceBoundaryGap L) phase z)
        (ShiftedBlocks.endpoint shift j.val) (ShiftedBlocks.endpoint shift (j.val+1))
        (grid.index (ShiftedBlocks.endpoint shift j.val) pathSlope) := by
    rw [P.referenceFamily_physicalSourceResidual_selected t pathSlope R cone w F
      hw hcone hF hwide hfrequency S hS alt hAlt b v f grid tops slope precision cut weight
      assigned stop T L A alpha z]
    exact P.short_parent_residual_eq grid packets assigned slope t R C
      (SourceParameters.branching L) w hw (SourceParameters.branching_pos L) hzero hangle
      _ _ _ _ pathSlope (grid.source_shifted_width_bounds L hbranch hK shift j.val).2
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun x : EuclideanSpace ℂ κ => ‖x‖^2) (heq j).symm

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataPhysicalResidualNorm
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A residual sees only the parent angular cell. Its cone, rather than
the slopes of the whole packet family, supplies the single-scale bound. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

theorem physicalMaskedValue_eq_complex_cross (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (T : ∀ j (l : P.labels j), Item j l → SlopeBox)
    (L A : ℝ) (z : ℝ×ℝ) :
    P.physicalMaskedValue alt hAlt t b v f T L A z =
      fun u => ((T u.1 u.2.1 u.2.2).mask L A z:ℂ) •
        P.crossPacketValue alt hAlt t b v f z u := by
  funext u
  ext k
  simp only [physicalMaskedValue, crossPacketValue, PiLp.smul_apply,
    PiLp.toLp_apply, smul_eq_mul]
  ring

theorem physical_parent_residual_norm {τ : Type*}
    (horder : 6 ≤ P.order) (t : ℝ) (d radius : Fin N → ℝ) (M : ℝ) (K H : ℕ)
    (hd : ∀ j, 0 < d j) (hM : 0 ≤ M) (hradius : ∀ j, radius j ≤ K)
    (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => t+P.rowSlope j l) (d j) H)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, Measurable (b j l k))
    (hbM : ∀ j l k s, ‖b j l k s‖ ≤ M)
    (hsupport : ∀ j l k s, b j l k s ≠ 0 → |s-(t+P.rowSlope j l)| ≤ radius j*d j)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (hf : Measurable f) (hf1 : ∀ z, ‖f z‖ ≤ 1)
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (T : τ → SlopeBox) (L A D w B C F : ℝ)
    (hw : 0 < w) (hB : 0 < B) (hcone : 0 ≤ C+B^3) (hF : 0 ≤ F)
    (hwide : (C+B^3)*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (hL : 2 ≤ L) (hD : 0 ≤ D) (hdegree : D ≤ ((2*⌈L⌉₊:ℕ):ℝ))
    (hp : ∀ top ∈ tops, 0 ≤ precision top)
    {Kb : ℕ} (hKb : 0 < Kb) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (hz : ∀ k, 0 ≤ (phase k).re) (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (z : ℝ×ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (hzero : ∀ j, grid.eligible (grid.rootWidth/B^2) (w/P.length j) 0)
    (hassigned : ∀ u ∈ packets, assigned u ∈ tops)
    (he : ∀ u ∈ packets, grid.eligible (grid.rootWidth/B^2) (precision (assigned u))
      (grid.lastEligible (grid.rootWidth/B^2) (w/P.length u.1) (div_pos hw (P.length_pos u.1))))
    (hangle : ∀ u ∈ packets,
      |t+P.rowSlope u.1 u.2.1-slope (assigned u)| ≤ C*(w/P.length u.1))
    (lower upper : ℕ) (pathSlope : ℝ) (hwidth : grid.width lower ≤ B*grid.width upper) :
    let cut := grid.rootWidth/B^2
    let stop := fun j => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let weight := fun top z => (T top).weight (L^(A+2)) D z
    let value := P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
    ‖grid.packetResidual packets (fun u => slope (assigned u)) (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cut weight assigned (fun u => stop u.1)
        value alpha z)
      (grid.sourceTransition tops slope precision cut weight Kb gap phase z)
      lower upper (grid.index lower pathSlope)‖ ≤
    ((residualLengthSet stop lower upper).card:ℝ)*
      (P.referenceEnvelopeConstant*((64*(4*Real.pi)^2)*
        ((P.referenceEnvelopeConstant*M*((2*K+1)*H:ℕ))*Real.pi^2))) := by
  let cut := grid.rootWidth/B^2
  let stop := fun j => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
  let weight := fun top z => (T top).weight (L^(A+2)) D z
  let bound := P.referenceEnvelopeConstant*((64*(4*Real.pi)^2)*
    ((P.referenceEnvelopeConstant*M*((2*K+1)*H:ℕ))*Real.pi^2))
  let mask := fun top => ((T top).mask L A z:ℂ)
  let S := (grid.packetSet packets (fun u => slope (assigned u)) (fun u => stop u.1)
    lower (grid.index lower pathSlope)).filter (fun u => stop u.1 < upper)
  have hS (u : P.PacketIndex) (hu : u ∈ S) :
      P.referenceCondition t pathSlope P.topLength (C+B^3) w u.1 u.2.1 := by
    obtain ⟨hu,hupper⟩ := Finset.mem_filter.mp hu
    obtain ⟨hup,hcell,hlower⟩ := Finset.mem_filter.mp hu
    constructor
    · exact div_le_self P.topLength_pos.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
    · simpa only [mul_div_assoc] using grid.source_parent_residual_cone hw hB
        (P.length_pos u.1) (hzero u.1) ⟨hlower,hupper⟩ hwidth hcell (hangle u hup)
  have hweight (top : τ) (x : ℝ×ℝ) : 0 < weight top x :=
    (T top).weight_pos (Real.rpow_pos_of_pos (by linarith) _) D x
  have hm (top : τ) (_htop : top ∈ tops) : weight top z^(-alpha)*‖mask top‖ ≤ 1 := by
    simpa only [mask,Complex.norm_real,Real.norm_eq_abs] using
      (T top).residual_mask_weight_bound hL hD hdegree ha ha1 z
  dsimp only
  rw [P.physicalMaskedValue_eq_complex_cross alt hAlt]
  have h := grid.source_packet_residual_norm_bound tops slope precision cut weight hp hweight
    hKb gap phase hz alpha ha z packets assigned (fun u : P.PacketIndex => u.1) stop mask
    (P.crossPacketValue alt hAlt t b v f z) hassigned he 1 zero_le_one hm
    lower upper pathSlope (fun _ => bound) (by
      intro j _
      exact P.cone_single_scale_cross_packets horder alt hAlt t pathSlope P.topLength
        (C+B^3) w F hw hcone hF hwide hfrequency j (d j) (radius j) M K H
        (hd j) hM (hradius j) (hlocal j) b (hb j) (hbM j) (hsupport j)
        v hv f hf hf1 S hS z)
  simpa only [one_mul,Finset.sum_const,nsmul_eq_mul,bound] using h

omit P alt hAlt in
/-- Source stopping and the rounded block length absorb every constant
in the physical single-block estimate before a family is chosen. -/
theorem eventually_physical_parent_shifted_residual_norm
    (q D M : ℝ) (hD : 0 ≤ D) (hM : 0 ≤ M) (K H : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item), 6 ≤ P.order → P.referenceEnvelopeConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t : ℝ) (d radius : Fin N → ℝ), (∀ j, 0 < d j) → (∀ j, radius j ≤ K) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => t+P.rowSlope j l) (d j) H) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ M) →
      (∀ j l k s, b j l k s ≠ 0 → |s-(t+P.rowSlope j l)| ≤ radius j*d j) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (τ : Type*) (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
      (T : τ → SlopeBox) (A w C F : ℝ) (hw : 0 < w)
      (_hcone : 0 ≤ C+(SourceParameters.branching L)^3) (_hF : 0 ≤ F)
      (_hwide : (C+(SourceParameters.branching L)^3)*w ≤ P.width)
      (_hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (grid.branching:ℝ) = SourceParameters.step L →
    ∀ (_hKb : 0 < SourceParameters.blockCount L) (shift : Fin (SourceParameters.blockCount L)),
      (∀ j : Fin N, grid.eligible (grid.rootWidth/(SourceParameters.branching L)^2)
        (w/P.length j) 0) → (∀ top ∈ tops, 0 ≤ precision top) →
    let cut := grid.rootWidth/(SourceParameters.branching L)^2
    let stop := fun j : Fin N => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let weight := fun top z => (T top).weight (L^(A+2)) D z
    ∀ (phase : ℕ → ℂ), (∀ k, 0 ≤ (phase k).re) →
    ∀ (alpha : ℝ), 0 ≤ alpha → alpha ≤ 1 →
    ∀ (z : ℝ×ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
      (∀ u ∈ packets, assigned u ∈ tops) →
      (∀ u ∈ packets, grid.eligible cut (precision (assigned u)) (stop u.1)) →
      (∀ u ∈ packets, |t+P.rowSlope u.1 u.2.1-slope (assigned u)| ≤ C*(w/P.length u.1)) →
    ∀ (j : ℕ) (pathSlope : ℝ),
    let value := P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
    ‖grid.packetResidual packets (fun u => slope (assigned u)) (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cut weight assigned (fun u => stop u.1) value alpha z)
      (grid.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
        (grid.sourceBoundaryGap L) phase z)
      (ShiftedBlocks.endpoint shift j) (ShiftedBlocks.endpoint shift (j+1))
      (grid.index (ShiftedBlocks.endpoint shift j) pathSlope)‖ ≤ L^(2*q+3) := by
  filter_upwards [SourceLabeledLattice.eventually_single_scale_budget q M hM K H,
    eventually_source_block_length_budget,eventually_ge_atTop (max 2 D)]
    with L hconstant hbudget hlarge
  have hL : 2 ≤ L := (le_max_left _ _).trans hlarge
  have hL0 : 0 < L := by linarith
  have hdegree : D ≤ ((2*⌈L⌉₊:ℕ):ℝ) := by
    have hceil : L ≤ (⌈L⌉₊:ℝ) := Nat.le_ceil L
    have hDL : D ≤ L := (le_max_right _ _).trans hlarge
    push_cast
    linarith
  intro N κ Label Item _ _ P horder hP alt hAlt t d radius hd hradius hlocal
    b hb hbM hsupp v hv f hf hf1 τ grid tops slope precision T A w C F hw hcone hF hwide hfrequency hbranch hKb shift hzero hp
  dsimp only
  intro phase hz alpha ha ha1 z packets assigned hassigned he hangle j pathSlope
  have h := P.physical_parent_residual_norm alt hAlt horder t d radius M K H hd hM hradius
    hlocal b hb hbM hsupp v hv f hf hf1 grid tops slope precision T L A D w
    (SourceParameters.branching L) C F hw (SourceParameters.branching_pos L)
    hcone hF hwide hfrequency hL hD hdegree hp hKb (grid.sourceBoundaryGap L)
    phase hz alpha ha ha1 z packets assigned hzero hassigned he hangle
    (ShiftedBlocks.endpoint shift j) (ShiftedBlocks.endpoint shift (j+1)) pathSlope
    (grid.source_shifted_width_bounds L hbranch hKb shift j).2
  refine h.trans ?_
  have hcNat := grid.source_shifted_residual_length_card L hbranch hKb shift hw
    P.topLength_pos hzero j
  have hc : ((residualLengthSet (fun i : Fin N => grid.lastEligible
      (grid.rootWidth/(SourceParameters.branching L)^2) (w/P.length i)
      (div_pos hw (P.length_pos i))) (ShiftedBlocks.endpoint shift j)
      (ShiftedBlocks.endpoint shift (j+1))).card:ℝ) ≤ L^(2:ℝ) :=
    (Nat.cast_le.mpr hcNat).trans hbudget
  have hbnd := hconstant P.referenceEnvelopeConstant P.referenceEnvelopeConstant_pos.le hP
  have habs := P.referenceEnvelopeConstant_pos
  calc
    _ ≤ L^(2:ℝ)*L^(2*q+1) := mul_le_mul hc hbnd (by positivity)
      (Real.rpow_nonneg hL0.le _)
    _ = L^(2*q+3) := by rw [← Real.rpow_add hL0]; congr 1; ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataParentFullResidual
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A parent-cone reference event controls the original short residuals.
The remaining long packets occur only in the terminal block and retain
the original single-scale selector estimate. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_physical_parent_full_residual_square_oai
    (q D : ℝ) (hq : 0 ≤ q) (hD : 0 ≤ D) (K H : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item), 6 ≤ P.order → P.referenceEnvelopeConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t a : ℝ) (d radius : Fin N → ℝ), (∀ j, 0 < d j) → (∀ j, radius j ≤ K) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => t+P.rowSlope j l) (d j) H) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 → |s-(t+P.rowSlope j l)| ≤ radius j*d j) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (τ : Type*) (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
      (T : τ → SlopeBox) (A s w R C F pathSlope : ℝ) (hw : 0 < w) (hR : 0 < R)
      (hcone : 0 ≤ C+(SourceParameters.branching L)^3) (hF : 0 ≤ F)
      (hwide : (C+(SourceParameters.branching L)^3)*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (grid.branching:ℝ) = SourceParameters.step L →
    ∀ (hKb : 0 < SourceParameters.blockCount L) (shift : Fin (SourceParameters.blockCount L)),
      (∀ j : Fin N, grid.eligible (grid.rootWidth/(SourceParameters.branching L)^2)
        (w/P.length j) 0) → (∀ top ∈ tops, 0 ≤ precision top) →
    let cut := grid.rootWidth/(SourceParameters.branching L)^2
    let stop := fun j : Fin N => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let weight := fun top z => (T top).weight (L^(A+2)) D z
    let count := grid.firstIneligibleShiftedBlock cut (w/R) (div_pos hw hR) hKb shift
    ∀ (phase : ℕ → ℂ), (∀ k, 0 ≤ (phase k).re) →
    ∀ (alpha : ℝ), 0 ≤ alpha → alpha ≤ 1 →
    ∀ (z : ℝ×ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
      (∀ u ∈ packets, assigned u ∈ tops) →
      (∀ u ∈ packets, grid.eligible cut (precision (assigned u)) (stop u.1)) →
      (∀ u ∈ packets, |t+P.rowSlope u.1 u.2.1-slope (assigned u)| ≤ C*(w/P.length u.1)) →
    let cone := C+(SourceParameters.branching L)^3
    let S := sourceReferencePackets packets (fun u => P.length u.1)
      (fun u => t+P.rowSlope u.1 u.2.1) R pathSlope cone w
    let Q := P.referenceFamily t pathSlope R cone w F hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel t pathSlope R cone w
    let selected := (Finset.univ : Finset Q.PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S)
    z ∉ (Q.restrictPackets selected).physicalReferenceBad
      (Q.restrictedAlternate (fun j l => alt j (orig j l)) selected)
      (Q.restrictedAlternate_bound (fun j l => alt j (orig j l))
        (fun j l => hAlt j (orig j l)) selected)
      pathSlope a (fun j l => b j (orig j l)) v f
      (fun j l u => T (assigned ⟨j,⟨orig j l,u.val⟩⟩)) L A (q+8) (2*q+9) s →
    let value := P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
    (∑ j : Fin count, ‖grid.packetResidual packets (fun u => slope (assigned u))
      (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cut weight assigned (fun u => stop u.1) value alpha z)
      (grid.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
        (grid.sourceBoundaryGap L) phase z)
      (ShiftedBlocks.endpoint shift j.val) (ShiftedBlocks.endpoint shift (j.val+1))
      (grid.index (ShiftedBlocks.endpoint shift j.val) pathSlope)‖^2) ≤
        (L^(3*q+13))^2 := by
  filter_upwards [eventually_physical_parent_short_square q D hq hD,
    eventually_physical_parent_shifted_residual_norm q D 1 hD zero_le_one K H,
    eventually_ge_atTop (2:ℝ)] with L hshortBound hlongBound hL
  intro N κ Label Item _ _ P horder hP alt hAlt t a d radius hd hradius hlocal
    b hb hb1 hsupp v hv f hf hf1 τ grid tops slope precision T A s w R C F pathSlope hw hR hcone hF hwide hfrequency
    hbranch hKb shift hzero hp
  dsimp only
  intro phase hz alpha ha ha1 z packets assigned hassigned he hangle hgood
  let cut := grid.rootWidth/(SourceParameters.branching L)^2
  let stop := fun j : Fin N => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
  let weight := fun top z => (T top).weight (L^(A+2)) D z
  let count := grid.firstIneligibleShiftedBlock cut (w/R) (div_pos hw hR) hKb shift
  let short := packets.filter (fun u => P.length u.1 ≤ R)
  let long := packets.filter (fun u => ¬P.length u.1 ≤ R)
  let value := P.physicalMaskedValue alt hAlt t b v f
    (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
  let base := grid.sourcePacketBase tops slope precision cut weight assigned
    (fun u => stop u.1) value alpha z
  let trans := grid.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
    (grid.sourceBoundaryGap L) phase z
  let residual (Q : Finset P.PacketIndex) (j : Fin count) :=
    grid.packetResidual Q (fun u => slope (assigned u)) (fun u => stop u.1) base trans
      (ShiftedBlocks.endpoint shift j.val) (ShiftedBlocks.endpoint shift (j.val+1))
      (grid.index (ShiftedBlocks.endpoint shift j.val) pathSlope)
  have hshort : (∑ j : Fin count, ‖residual short j‖^2) ≤ (L^(3*q+12))^2 :=
    hshortBound N κ Label Item P horder hP alt hAlt t pathSlope R C F w a hw
      hcone hF hwide hfrequency b hb hb1 v hv f hf hf1 τ grid tops slope precision T A s
      hbranch hKb shift hzero hp phase hz alpha ha ha1 z packets assigned hassigned he
      hangle hgood count
  have hsupport (j : Fin count) (hj : j.val+1 < count) : residual long j = 0 :=
    grid.source_shifted_long_residual_support packets (fun u => slope (assigned u))
      (fun u : P.PacketIndex => P.length u.1) (fun u => P.length_pos u.1)
      hw (SourceParameters.branching_pos L) hR hKb shift
      (fun u _ => hzero u.1) base trans pathSlope j hj
  have hterminal (j : Fin count) : ‖residual long j‖ ≤ L^(2*q+3) :=
    hlongBound N κ Label Item P horder hP alt hAlt t d radius hd hradius hlocal b hb hb1
      hsupp v hv f hf hf1 τ grid tops slope precision T A w C F hw hcone hF hwide hfrequency hbranch hKb shift hzero hp
      phase hz alpha ha ha1 z long assigned
      (fun u hu => hassigned u (Finset.mem_filter.mp hu).1)
      (fun u hu => he u (Finset.mem_filter.mp hu).1)
      (fun u hu => hangle u (Finset.mem_filter.mp hu).1) j.val pathSlope
  have hsplit (j : Fin count) : residual packets j = residual short j+residual long j :=
    grid.packetResidual_filter_split packets (fun u => slope (assigned u)) (fun u => stop u.1)
      base trans (fun u => P.length u.1 ≤ R) _ _ _
  change (∑ j : Fin count, ‖residual packets j‖^2) ≤ _
  by_cases hc : 0 < count
  · have hfull := terminal_perturbation_square_sum hc (residual packets) (residual short)
      (residual long) hsplit hsupport hshort (Real.rpow_nonneg (by linarith) _) (hterminal _)
    refine hfull.trans ?_
    have hsmall : L^(2*q+3) ≤ L^(3*q+12) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hsmallSq := pow_le_pow_left₀ (Real.rpow_nonneg (by linarith) _) hsmall 2
    have hpos : 0 ≤ L^(3*q+12) := Real.rpow_nonneg (by linarith) _
    have hscale : 2*L^(3*q+12) ≤ L^(3*q+12)*L := by nlinarith
    have hscaleSq := pow_le_pow_left₀ (by positivity : 0 ≤ 2*L^(3*q+12)) hscale 2
    have hpow : L^(3*q+13) = L^(3*q+12)*L := by
      rw [show 3*q+13 = (3*q+12)+1 by ring,Real.rpow_add (by linarith),Real.rpow_one]
    rw [hpow]
    nlinarith
  · have hzcount : count = 0 := by omega
    have hsum : (∑ j : Fin count, ‖residual packets j‖^2) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have := j.isLt
      omega
    rw [hsum]
    positivity

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.LipschitzHilbert.PacketLatticeData.eventually_physical_parent_full_residual_square_oai.{u_1} := @OAI.LipschitzHilbert.PacketLatticeData.eventually_physical_parent_full_residual_square_oai.{u_1}
