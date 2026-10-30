-- Prove2me | solution 1 for OAI.LipschitzHilbert.PacketLatticeData.exists_ordinary_capped_removal_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:18:24.972904+00:00
-- url     : https://prove2.me/submissions/c21d29d8-88cb-47e0-acfa-9329fd1a8ad7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_PacketLatticeData_exists_tree_far_gram_bound
import Theorems.Thm_OAI_LipschitzHilbert_SourceLabeledLattice_exists_reference_ordinary_tree_estimate

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteEnergySchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite weighted energy summation for the smooth/dyadic comparison. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem weighted_sum_norm_square {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (v : ι → E) (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    ‖∑ j, v j‖ ^ 2 ≤ (∑ j, w j) * ∑ j, ‖v j‖ ^ 2 / w j := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (f := w) (g := fun j => ‖v j‖ ^ 2 / w j) (r := fun j => ‖v j‖)
    (fun j _ => (hw j).le) (fun j _ => div_nonneg (sq_nonneg _) (hw j).le)
    (fun j _ => by rw [mul_div_cancel₀ _ (hw j).ne'])
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans hcs

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_EnvelopeSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Cauchy--Schwarz for actual packet synthesis, followed by
polynomially weighted whole-line energy bounds. -/

noncomputable section
open MeasureTheory
open FourierTransform
open scoped BigOperators
open scoped FourierTransform

namespace LipschitzHilbert

theorem envelope_synthesis_square {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ι → ℂ) (f : ι → E) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    {C D : ℝ} (hD : 0 ≤ D) (hover : ∑ i, w i ≤ D)
    (henv : ∀ i, ‖f i‖ ≤ C * w i) :
    ‖∑ i, c i • f i‖ ^ 2 ≤ D * C ^ 2 * ∑ i, ‖c i‖ ^ 2 * w i := by
  have hterm (i : ι) : ‖c i • f i‖ ^ 2 / w i ≤ C ^ 2 * (‖c i‖ ^ 2 * w i) := by
    rw [norm_smul, mul_pow]
    apply (div_le_iff₀ (hw i)).mpr
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (henv i) 2
    have h := mul_le_mul_of_nonneg_left hsq (sq_nonneg ‖c i‖)
    nlinarith
  calc
    _ ≤ (∑ i, w i) * ∑ i, ‖c i • f i‖ ^ 2 / w i :=
      weighted_sum_norm_square _ w hw
    _ ≤ D * ∑ i, ‖c i • f i‖ ^ 2 / w i :=
      mul_le_mul_of_nonneg_right hover (Finset.sum_nonneg (fun i _ =>
        div_nonneg (sq_nonneg _) (hw i).le))
    _ ≤ D * ∑ i, C ^ 2 * (‖c i‖ ^ 2 * w i) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hterm i)) hD
    _ = _ := by rw [← Finset.mul_sum, mul_assoc]

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_WeightedPacketEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomially localized packet synthesis energy with arbitrary dual
coefficients. No local coefficient budget is assumed here. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem weighted_component_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (rho : ι → ℝ) :
    (∑ k, ∑ i, ‖c i k‖ ^ 2 * rho i) = ∑ i, ‖c i‖ ^ 2 * rho i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_mul, ← EuclideanSpace.norm_sq_eq]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PlanarFixedScaleEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-length synthesis estimate in section 3. A single translated
box lattice has bounded overlap. Summing squared bin components gives a
constant independent of the number of packets and frequency bins. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem planarFixedSynthesis_memLp {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ) :
    MemLp (planarFixedSynthesis c f) 2 (volume.prod volume) := by
  apply memLp_piLp_iff.mpr
  intro k
  exact memLp_finsetSum _ (fun i _ => ((f i k).memLp 2 (volume.prod volume)).const_mul (c i k))

theorem planarFixedSynthesis_pointwise {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (z : ℝ×ℝ) (weight : ι → ℝ) (hw : ∀ i, 0 < weight i)
    {C D : ℝ} (hD : 0 ≤ D) (hover : ∑ i, weight i ≤ D)
    (henv : ∀ i k, ‖f i k z‖ ≤ C*weight i) :
    ‖planarFixedSynthesis c f z‖^2 ≤ D*C^2*∑ i, ‖c i‖^2*weight i := by
  rw [EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ k, D*C^2*∑ i, ‖c i k‖^2*weight i := by
      apply Finset.sum_le_sum
      intro k _
      exact envelope_synthesis_square (fun i => c i k) (fun i => f i k z)
        weight hw hD hover (fun i => henv i k)
    _ = _ := by
      rw [← Finset.mul_sum,weighted_component_energy]

theorem planar_envelope_integrable (x y l W slope : ℝ) (hl : 0 < l) (hW : 0 < W) :
    Integrable (fun z : ℝ×ℝ =>
      lineEnvelope x l 1 z.1*lineEnvelope y W 1 (z.2-slope*z.1)) (volume.prod volume) := by
  have hprod := (integrable_lineEnvelope_one x l hl).mul_prod
    (integrable_lineEnvelope_one y W hW)
  simpa [slopeShear,Function.comp_def,sub_eq_add_neg] using
    (slopeShear_measurePreserving (-slope)).integrable_comp_of_integrable hprod

theorem integral_planar_envelope (x y l W slope : ℝ) (hl : 0 < l) (hW : 0 < W) :
    (∫ z : ℝ×ℝ, lineEnvelope x l 1 z.1*lineEnvelope y W 1 (z.2-slope*z.1)
      ∂volume.prod volume) = Real.pi^2*l*W := by
  have heq : (fun z : ℝ×ℝ =>
      lineEnvelope x l 1 z.1*lineEnvelope y W 1 (z.2-slope*z.1)) =
      (fun z : ℝ×ℝ => lineEnvelope x l 1 z.1*lineEnvelope y W 1 z.2) ∘
        slopeShear (-slope) := by
    funext z
    simp [slopeShear,sub_eq_add_neg]
  rw [heq]
  change (∫ z, (fun p : ℝ×ℝ => lineEnvelope x l 1 p.1*lineEnvelope y W 1 p.2)
    (slopeShear (-slope) z) ∂volume.prod volume) = _
  rw [integral_slopeShear (-slope)
    (fun p : ℝ×ℝ => lineEnvelope x l 1 p.1*lineEnvelope y W 1 p.2),integral_prod_mul,
    integral_lineEnvelope_one x l hl,integral_lineEnvelope_one y W hW]
  ring

theorem planar_fixed_scale_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (site : ι → ℤ×ℤ) (hinj : Function.Injective site)
    (a b l W slope C : ℝ) (hl : 0 < l) (hW : 0 < W)
    (henv : ∀ i k z, ‖f i k z‖ ≤ C*
      (lineEnvelope (a+l*(site i).1) l 1 z.1*
        lineEnvelope (b+W*(site i).2) W 1 (z.2-slope*z.1))) :
    (∫ z, ‖planarFixedSynthesis c f z‖^2 ∂volume.prod volume) ≤
      ((4*Real.pi)^2*C^2*Real.pi^2)*∑ i, ‖c i‖^2*l*W := by
  let weight := fun (i : ι) (z : ℝ×ℝ) =>
    lineEnvelope (a+l*(site i).1) l 1 z.1*
      lineEnvelope (b+W*(site i).2) W 1 (z.2-slope*z.1)
  have hi (i : ι) : Integrable (fun z => ‖c i‖^2*weight i z) (volume.prod volume) :=
    (planar_envelope_integrable _ _ l W slope hl hW).const_mul _
  have hp (z : ℝ×ℝ) : ‖planarFixedSynthesis c f z‖^2 ≤
      (4*Real.pi)^2*C^2*∑ i, ‖c i‖^2*weight i z := by
    apply planarFixedSynthesis_pointwise c f z (fun i => weight i z)
    · intro i
      dsimp [weight,lineEnvelope]
      positivity
    · positivity
    · exact injective_tile_lattice_overlap site hinj a b l W z.1
        (z.2-slope*z.1) hl.ne' hW.ne' (by decide) (by decide)
    · exact fun i k => henv i k z
  calc
    _ ≤ ∫ z, (4*Real.pi)^2*C^2*∑ i, ‖c i‖^2*weight i z ∂volume.prod volume :=
      integral_mono ((planarFixedSynthesis_memLp c f).integrable_norm_pow (by decide))
        ((integrable_finsetSum _ (fun i _ => hi i)).const_mul _) hp
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => hi i)]
      simp_rw [integral_const_mul]
      simp only [weight,integral_planar_envelope _ _ l W slope hl hW]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_AnalyzingCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Hilbert duality for coefficients defined by actual analyzing
integrals. The self-pairing uses the same selected synthesizing packets. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace LipschitzHilbert
variable {Ω σ κ : Type*} [MeasurableSpace Ω] [Fintype σ] [Fintype κ]

omit [Fintype σ] [Fintype κ] in
theorem analyzingCoefficient_mul_area (μ : Measure Ω) (area : σ → ℝ)
    (wave : σ → κ → Ω → ℂ) (g : Ω → EuclideanSpace ℂ κ)
    (ha : ∀ i, area i ≠ 0) (i : σ) (k : κ) :
    (area i : ℂ) * analyzingCoefficient μ area wave g i k =
      ∫ z, g z k * conj (wave i k z) ∂μ := by
  change (area i : ℂ) * (((area i)⁻¹ : ℂ) * _) = _
  rw [← mul_assoc, mul_inv_cancel₀ (show (area i : ℂ) ≠ 0 by exact_mod_cast ha i), one_mul]

theorem analyzingCoefficient_self_pairing (μ : Measure Ω) (area : σ → ℝ)
    (wave : σ → κ → Ω → ℂ) (g : Ω → EuclideanSpace ℂ κ)
    (ha : ∀ i, area i ≠ 0)
    (hint : ∀ i k, Integrable (fun z => g z k * conj (wave i k z)) μ) :
    ((∑ i, area i * ‖analyzingCoefficient μ area wave g i‖^2 : ℝ) : ℂ) =
      ∫ z, inner ℂ (diagonalSynthesis wave (analyzingCoefficient μ area wave g) z) (g z) ∂μ := by
  let a := analyzingCoefficient μ area wave g
  have hterm (i : σ) : ((area i * ‖a i‖^2 : ℝ) : ℂ) =
      ∑ k, conj (a i k) * ∫ z, g z k * conj (wave i k z) ∂μ := by
    have hnorm : (‖a i‖ : ℂ)^2 = inner ℂ (a i) (a i) :=
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (a i)).symm
    rw [Complex.ofReal_mul, Complex.ofReal_pow, hnorm]
    simp only [PiLp.inner_apply, RCLike.inner_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← analyzingCoefficient_mul_area μ area wave g ha i k]
    ring
  have hInt (i : σ) (k : κ) :
      Integrable (fun z => conj (a i k) * (g z k * conj (wave i k z))) μ :=
    (hint i k).const_mul _
  calc
    _ = ∑ i, ∑ k, conj (a i k) * ∫ z, g z k * conj (wave i k z) ∂μ := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = ∫ z, ∑ i, ∑ k, conj (a i k) * (g z k * conj (wave i k z)) ∂μ := by
      simp_rw [← integral_const_mul]
      rw [integral_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum _ (fun k _ => hInt i k))]
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum Finset.univ (fun k _ => hInt i k)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [diagonalSynthesis, PiLp.inner_apply, RCLike.inner_apply,
        map_sum, map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SeparatedPlanarSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Combining the box-lattice synthesis bound with separated annuli.
This is the nonmaximal, unweighted separated synthesis estimate of §3,
including the dimension-independent sum over frequency bins. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem planarFourier_finsetSum {ι : Type*} (s : Finset ι)
    (f : ι → SchwartzMap (ℝ×ℝ) ℂ) (frequency : ℝ×ℝ) :
    planarFourier (∑ i ∈ s, f i : SchwartzMap (ℝ×ℝ) ℂ) frequency =
      ∑ i ∈ s, planarFourier (f i) frequency := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [planarFourier]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi,planarFourier_add,ih,Finset.sum_insert hi]

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

end LipschitzHilbert.SourceSlopeLabels

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityKeepers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Decreasing-length selection of the actual spatial and angular density
tests. Keeper witnesses are disjoint even when their spatial boxes overlap. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

theorem densityConflict_symm {ι : Type*} (T : ι → SlopeBox) (omega : ι → Set ℝ)
    (K : ℝ) {i j : ι} (h : densityConflict T omega K i j) :
    densityConflict T omega K j i := by
  simpa only [densityConflict,inter_comm] using h

theorem densityTest_disjoint_of_not_conflict {ι : Type*}
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (T : ι → SlopeBox)
    (omega : ι → Set ℝ) (K : ℝ) {i j : ι}
    (h : ¬densityConflict T omega K i j) :
    Disjoint (densityTest E u (T i) (omega i) K)
      (densityTest E u (T j) (omega j) K) := by
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  exact h ⟨⟨z,hzi.1.2,hzj.1.2⟩,⟨u z,hzi.2,hzj.2⟩⟩

theorem exists_density_keepers {ι : Type*} (candidates : Finset ι)
    (T : ι → SlopeBox) (omega : ι → Set ℝ) (K : ℝ) (hK : 0 ≤ K)
    (homega : ∀ i ∈ candidates, (omega i).Nonempty) :
    ∃ keepers : Finset ι, keepers ⊆ candidates ∧
      (∀ i ∈ keepers, ∀ j ∈ keepers, i ≠ j → ¬densityConflict T omega K i j) ∧
      (∀ i ∈ candidates, ∃ j ∈ keepers,
        (T i).length ≤ (T j).length ∧ densityConflict T omega K i j) := by
  classical
  induction candidates using Finset.strongInductionOn with
  | _ candidates ih =>
    by_cases hnonempty : candidates.Nonempty
    · obtain ⟨top,htop,hmax⟩ := candidates.exists_max_image (fun i => (T i).length) hnonempty
      have hself : densityConflict T omega K top top := by
        obtain ⟨s,hs⟩ := homega top htop
        refine ⟨⟨((T top).x,(T top).y),?_,?_⟩,⟨s,hs,hs⟩⟩ <;>
          simp only [densitySpatialBox,mem_ofPred_eq,sub_self,mul_zero,abs_zero]
        · exact ⟨mul_nonneg hK (T top).length_pos.le,mul_nonneg hK (T top).width_pos.le⟩
        · exact ⟨mul_nonneg hK (T top).length_pos.le,mul_nonneg hK (T top).width_pos.le⟩
      let rest := candidates.filter fun i => ¬densityConflict T omega K top i
      have hrest : rest ⊂ candidates := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.filter_subset _ _,?_⟩
        intro heq
        have : top ∈ rest := heq.symm ▸ htop
        exact (Finset.mem_filter.mp this).2 hself
      obtain ⟨keepers,hsub,hdisj,hcover⟩ := ih rest hrest
        (fun i hi => homega i (Finset.mem_filter.mp hi).1)
      refine ⟨insert top keepers,?_,?_,?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact htop
        · exact (Finset.mem_filter.mp (hsub hi)).1
      · intro i hi j hj hij
        rcases Finset.mem_insert.mp hi with hieq | hi'
        · subst i
          rcases Finset.mem_insert.mp hj with hjeq | hj'
          · exact (hij hjeq.symm).elim
          · exact (Finset.mem_filter.mp (hsub hj')).2
        · rcases Finset.mem_insert.mp hj with hjeq | hj'
          · subst j
            intro hconflict
            exact (Finset.mem_filter.mp (hsub hi')).2 (densityConflict_symm T omega K hconflict)
          · exact hdisj i hi' j hj' hij
      · intro i hi
        by_cases hc : densityConflict T omega K top i
        · exact ⟨top,Finset.mem_insert_self _ _,hmax i hi,densityConflict_symm T omega K hc⟩
        · obtain ⟨j,hj,hlen,hconflict⟩ := hcover i (Finset.mem_filter.mpr ⟨hi,hc⟩)
          exact ⟨j,Finset.mem_insert_of_mem hj,hlen,hconflict⟩
    · refine ⟨∅,Finset.empty_subset _,?_,?_⟩
      · simp
      · intro i hi
        exact (hnonempty ⟨i,hi⟩).elim

theorem density_keeper_area_budget {ι : Type*} (keepers : Finset ι)
    (T : ι → SlopeBox) (omega : ι → Set ℝ) (K eta : ℝ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (heta : 0 < eta)
    (hE : (volume.prod volume) E ≠ ∞)
    (hdisj : ∀ i ∈ keepers, ∀ j ∈ keepers, i ≠ j → ¬densityConflict T omega K i j)
    (hmeas : ∀ i ∈ keepers, MeasurableSet (densityTest E u (T i) (omega i) K))
    (hmass : ∀ i ∈ keepers, eta*(T i).area ≤
      (volume.prod volume).real (densityTest E u (T i) (omega i) K)) :
    ∑ i ∈ keepers, (T i).area ≤ (volume.prod volume).real E / eta := by
  have hsub (i : ι) : densityTest E u (T i) (omega i) K ⊆ E := fun _ hz => hz.1.1
  have hfinite (i : ι) : (volume.prod volume) (densityTest E u (T i) (omega i) K) ≠ ∞ :=
    measure_ne_top_of_subset (hsub i) hE
  have hpair : Set.PairwiseDisjoint (keepers : Set ι)
      (fun i => densityTest E u (T i) (omega i) K) := by
    intro i hi j hj hij
    exact densityTest_disjoint_of_not_conflict E u T omega K (hdisj i hi j hj hij)
  have hsum : (∑ i ∈ keepers, (volume.prod volume).real (densityTest E u (T i) (omega i) K)) ≤
      (volume.prod volume).real E := by
    rw [← measureReal_biUnion_finset hpair hmeas (fun i _ => hfinite i)]
    apply measureReal_mono _ hE
    intro z hz
    obtain ⟨i,hi,hz⟩ := mem_iUnion₂.mp hz
    exact hsub i hz
  apply (le_div_iff₀ heta).mpr
  calc
    (∑ i ∈ keepers, (T i).area)*eta = ∑ i ∈ keepers, eta*(T i).area := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i ∈ keepers, (volume.prod volume).real (densityTest E u (T i) (omega i) K) :=
      Finset.sum_le_sum hmass
    _ ≤ _ := hsum

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual geometry behind the density keeper assignment: intersecting
angular cells give slope control, and intersecting slope boxes then give
the required spatial enlargement. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem densitySpatialBox_measurable (T : SlopeBox) (K : ℝ) :
    MeasurableSet (densitySpatialBox T K) := by
  change MeasurableSet ({z : ℝ×ℝ | |z.1-T.x| ≤ K*T.length} ∩
    {z : ℝ×ℝ | |(z.2-T.y)-T.slope*(z.1-T.x)| ≤ K*T.width})
  exact (isClosed_le ((continuous_fst.sub continuous_const).abs) continuous_const).measurableSet.inter
    (isClosed_le (((continuous_snd.sub continuous_const).sub
      (continuous_const.mul (continuous_fst.sub continuous_const))).abs) continuous_const).measurableSet

theorem densityTest_measurable {E : Set (ℝ×ℝ)} {u : ℝ×ℝ → ℝ}
    {omega : Set ℝ} (hE : MeasurableSet E) (hu : Measurable u)
    (homega : MeasurableSet omega) (T : SlopeBox) (K : ℝ) :
    MeasurableSet (densityTest E u T omega K) :=
  (hE.inter (densitySpatialBox_measurable T K)).inter (hu homega)

theorem density_center_in_keeper (T S : SlopeBox) {K C : ℝ}
    (hK : 0 ≤ K) (hlen : T.length ≤ S.length) (hwidth : T.width = S.width)
    (hslope : |T.slope-S.slope| * T.length ≤ C*S.width)
    {z : ℝ×ℝ} (hT : z ∈ densitySpatialBox T K) (hS : z ∈ densitySpatialBox S K) :
    |T.x-S.x| ≤ 2*K*S.length ∧
      |(T.y-S.y)-S.slope*(T.x-S.x)| ≤ (2+C)*K*S.width := by
  have hx : |T.x-S.x| ≤ 2*K*S.length := by
    calc
      _ = |(z.1-S.x)-(z.1-T.x)| := by congr 1; ring
      _ ≤ |z.1-S.x|+|z.1-T.x| := abs_sub _ _
      _ ≤ K*S.length+K*T.length := add_le_add hS.1 hT.1
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hlen hK]
  refine ⟨hx,?_⟩
  have hp : |T.slope-S.slope| * |z.1-T.x| ≤ C*K*S.width := by
    calc
      _ ≤ |T.slope-S.slope| * (K*T.length) :=
        mul_le_mul_of_nonneg_left hT.1 (abs_nonneg _)
      _ = K*(|T.slope-S.slope| * T.length) := by ring
      _ ≤ K*(C*S.width) := mul_le_mul_of_nonneg_left hslope hK
      _ = _ := by ring
  calc
    _ = |((z.2-S.y)-S.slope*(z.1-S.x)) -
        ((z.2-T.y)-T.slope*(z.1-T.x)) - (T.slope-S.slope)*(z.1-T.x)| := by
      congr 1
      ring
    _ ≤ |(z.2-S.y)-S.slope*(z.1-S.x)|+
        |(z.2-T.y)-T.slope*(z.1-T.x)|+|(T.slope-S.slope)*(z.1-T.x)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ K*S.width+K*T.width+C*K*S.width := by
      rw [abs_mul]
      exact add_le_add (add_le_add hS.2 hT.2) hp
    _ = _ := by rw [hwidth]; ring

theorem density_box_subset_keeper (T S : SlopeBox) {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hlen : T.length ≤ S.length)
    (hwidth : T.width = S.width)
    (hslope : |T.slope-S.slope| * T.length ≤ C*S.width)
    (hinter : (densitySpatialBox T K ∩ densitySpatialBox S K).Nonempty) :
    densitySpatialBox T K ⊆ densitySpatialBox S ((3+2*C)*K) := by
  obtain ⟨q,hqT,hqS⟩ := hinter
  obtain ⟨hcx,hcy⟩ := density_center_in_keeper T S hK hlen hwidth hslope hqT hqS
  intro z hz
  have hx : |z.1-S.x| ≤ 3*K*S.length := by
    calc
      _ = |(z.1-T.x)+(T.x-S.x)| := by congr 1; ring
      _ ≤ |z.1-T.x|+|T.x-S.x| := abs_add_le _ _
      _ ≤ K*T.length+2*K*S.length := add_le_add hz.1 hcx
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hlen hK]
  have hp : |T.slope-S.slope| * |z.1-T.x| ≤ C*K*S.width := by
    calc
      _ ≤ |T.slope-S.slope| * (K*T.length) :=
        mul_le_mul_of_nonneg_left hz.1 (abs_nonneg _)
      _ = K*(|T.slope-S.slope| * T.length) := by ring
      _ ≤ K*(C*S.width) := mul_le_mul_of_nonneg_left hslope hK
      _ = _ := by ring
  constructor
  · exact hx.trans (by nlinarith [mul_nonneg (mul_nonneg hC hK) S.length_pos.le])
  · calc
      _ = |((z.2-T.y)-T.slope*(z.1-T.x)) +
          ((T.y-S.y)-S.slope*(T.x-S.x)) + (T.slope-S.slope)*(z.1-T.x)| := by
        congr 1
        ring
      _ ≤ |(z.2-T.y)-T.slope*(z.1-T.x)|+
          |(T.y-S.y)-S.slope*(T.x-S.x)|+|(T.slope-S.slope)*(z.1-T.x)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ K*T.width+(2+C)*K*S.width+C*K*S.width := by
        rw [abs_mul]
        exact add_le_add (add_le_add hz.2 hcy) hp
      _ = _ := by rw [hwidth]; ring

theorem density_angular_cell_slope {q k l i j : ℤ} {s t : ℝ}
    (hlk : l ≤ k) (hinter : (DyadicLineGrid.cell q k i ∩ DyadicLineGrid.cell q l j).Nonempty)
    (hs : s ∈ DyadicLineGrid.cell q k i) (ht : t ∈ DyadicLineGrid.cell q l j) :
    |s-t| ≤ DyadicLineGrid.scale k := by
  have ht' := DyadicLineGrid.cell_subset_of_intersect hlk
    (by simpa only [inter_comm] using hinter) ht
  have hnext : DyadicLineGrid.left q k (i+1) =
      DyadicLineGrid.left q k i+DyadicLineGrid.scale k := by
    unfold DyadicLineGrid.left
    push_cast
    ring
  change DyadicLineGrid.left q k i ≤ s ∧ s < DyadicLineGrid.left q k (i+1) at hs
  change DyadicLineGrid.left q k i ≤ t ∧ t < DyadicLineGrid.left q k (i+1) at ht'
  rw [hnext] at hs ht'
  exact abs_le.mpr ⟨by linarith [hs.1,ht'.2],by linarith [hs.2,ht'.1]⟩

end LipschitzHilbert

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

theorem scaledAngularCell_nonempty {unit : ℝ} (hunit : 0 < unit) (q k j : ℤ) :
    (scaledAngularCell unit q k j).Nonempty := by
  obtain ⟨s,hs⟩ := DyadicLineGrid.cell_nonempty q k j
  refine ⟨s*unit,?_⟩
  simpa only [scaledAngularCell,mem_ofPred_eq,mul_div_cancel_right₀ _ hunit.ne'] using hs

theorem scaledAngularCell_subset {unit : ℝ} {q k l i j : ℤ} (hlk : l ≤ k)
    (hinter : (scaledAngularCell unit q k i ∩ scaledAngularCell unit q l j).Nonempty) :
    scaledAngularCell unit q l j ⊆ scaledAngularCell unit q k i := by
  obtain ⟨s,hs,ht⟩ := hinter
  have hnested := DyadicLineGrid.cell_subset_of_intersect hlk ⟨s/unit,ht,hs⟩
  intro t ht
  exact hnested ht

theorem scaledAngularCell_slope {unit : ℝ} (hunit : 0 < unit) {q k l i j : ℤ} {s t : ℝ}
    (hlk : l ≤ k)
    (hinter : (scaledAngularCell unit q k i ∩ scaledAngularCell unit q l j).Nonempty)
    (hs : s ∈ scaledAngularCell unit q k i) (ht : t ∈ scaledAngularCell unit q l j) :
    |s-t| ≤ unit*DyadicLineGrid.scale k := by
  obtain ⟨v,hv,hv'⟩ := hinter
  have h := density_angular_cell_slope hlk ⟨v/unit,hv,hv'⟩ hs ht
  rw [←sub_div,abs_div,abs_of_pos hunit] at h
  simpa only [mul_comm] using (div_le_iff₀ hunit).mp h

theorem exists_scaled_dyadic_density_forest {ι : Type*} (candidates : Finset ι)
    (T : ι → SlopeBox) (level cell : ι → ℤ) (q : ℤ) (unit K C eta : ℝ)
    (hunit : 0 < unit) (hK : 0 ≤ K) (hC : 0 ≤ C) (heta : 0 < eta)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (hE : MeasurableSet E)
    (hEfinite : (volume.prod volume) E ≠ ∞) (hu : Measurable u)
    (horder : ∀ i ∈ candidates, ∀ j ∈ candidates,
      (T i).length ≤ (T j).length → level j ≤ level i)
    (hwidth : ∀ i ∈ candidates, ∀ j ∈ candidates, (T i).width = (T j).width)
    (hslope : ∀ i ∈ candidates,
      (T i).slope ∈ scaledAngularCell unit q (level i) (cell i))
    (hangular : ∀ i ∈ candidates,
      (unit*DyadicLineGrid.scale (level i))*(T i).length ≤ C*(T i).width)
    (hmass : ∀ i ∈ candidates, eta*(T i).area ≤
      (volume.prod volume).real
        (densityTest E u (T i) (scaledAngularCell unit q (level i) (cell i)) K)) :
    ∃ keepers : Finset ι, keepers ⊆ candidates ∧
      (∀ i ∈ keepers, MeasurableSet
        (densityTest E u (T i) (scaledAngularCell unit q (level i) (cell i)) K)) ∧
      Set.PairwiseDisjoint (keepers : Set ι)
        (fun i => densityTest E u (T i) (scaledAngularCell unit q (level i) (cell i)) K) ∧
      (∑ i ∈ keepers, (T i).area) ≤ (volume.prod volume).real E/eta ∧
      (∀ i ∈ keepers, ∀ z ∈ densityTest E u (T i)
          (scaledAngularCell unit q (level i) (cell i)) K,
        z ∈ E ∧ |u z-(T i).slope| ≤ unit*DyadicLineGrid.scale (level i)) ∧
      (∀ i ∈ candidates, ∃ j ∈ keepers,
        (T i).length ≤ (T j).length ∧
        scaledAngularCell unit q (level j) (cell j) ⊆
          scaledAngularCell unit q (level i) (cell i) ∧
        densitySpatialBox (T i) K ⊆ densitySpatialBox (T j) ((3+2*C)*K)) := by
  let omega := fun i => scaledAngularCell unit q (level i) (cell i)
  obtain ⟨keepers,hsub,hdisj,hcover⟩ := exists_density_keepers candidates T omega K hK
    (fun i _ => scaledAngularCell_nonempty hunit q (level i) (cell i))
  have hm (i : ι) : MeasurableSet (densityTest E u (T i) (omega i) K) :=
    densityTest_measurable hE hu (scaledAngularCell_measurable unit q (level i) (cell i)) (T i) K
  refine ⟨keepers,hsub,fun i _ => hm i,?_,?_,?_,?_⟩
  · intro i hi j hj hij
    exact densityTest_disjoint_of_not_conflict E u T omega K (hdisj i hi j hj hij)
  · exact density_keeper_area_budget keepers T omega K eta E u heta hEfinite hdisj
      (fun i _ => hm i) (fun i hi => hmass i (hsub hi))
  · intro i hi z hz
    refine ⟨hz.1.1,?_⟩
    exact scaledAngularCell_slope hunit (le_refl (level i))
      ⟨(T i).slope,hslope i (hsub hi),hslope i (hsub hi)⟩ hz.2 (hslope i (hsub hi))
  · intro i hi
    obtain ⟨j,hj,hlen,hconflict⟩ := hcover i hi
    have hjc := hsub hj
    have hlevels := horder i hi j hjc hlen
    have hnested : omega j ⊆ omega i := scaledAngularCell_subset hlevels hconflict.2
    have hs : |(T i).slope-(T j).slope| * (T i).length ≤ C*(T j).width := by
      calc
        _ ≤ (unit*DyadicLineGrid.scale (level i))*(T i).length :=
          mul_le_mul_of_nonneg_right
            (scaledAngularCell_slope hunit hlevels hconflict.2 (hslope i hi) (hslope j hjc))
            (T i).length_pos.le
        _ ≤ C*(T i).width := hangular i hi
        _ = _ := by rw [hwidth i hi j hjc]
    exact ⟨j,hj,hlen,hnested,density_box_subset_keeper (T i) (T j) hK hC hlen
      (hwidth i hi j hjc) hs hconflict.1⟩

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

theorem densityKernel_le_one (T : SlopeBox) {D : ℝ} (hD : 0 ≤ D) (z : ℝ×ℝ) :
    T.densityKernel D z ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith [T.radius_nonnegative z]) (neg_nonpos.mpr hD)

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

theorem densitySpatialBox_iff (T : SlopeBox) (K : ℝ) (z : ℝ×ℝ) :
    z ∈ densitySpatialBox T K ↔ |T.horizontal z| ≤ K ∧ |T.transverse z| ≤ K := by
  simp only [densitySpatialBox,mem_ofPred_eq,SlopeBox.horizontal,SlopeBox.transverse,
    abs_div,abs_of_pos T.length_pos,abs_of_pos T.width_pos,
    div_le_iff₀ T.length_pos,div_le_iff₀ T.width_pos]

theorem densitySpatialBox_radius_lt (T : SlopeBox) (K : ℝ) {z : ℝ×ℝ}
    (hz : z ∉ densitySpatialBox T K) : K < T.radius z := by
  by_contra h
  have hr : T.radius z ≤ K := le_of_not_gt h
  apply hz
  rw [densitySpatialBox_iff]
  constructor
  · exact (le_add_of_nonneg_right (abs_nonneg _)).trans hr
  · exact (le_add_of_nonneg_left (abs_nonneg _)).trans hr

theorem densityKernel_tail (T : SlopeBox) {K D : ℝ} (hK : 1 ≤ K) (hD : 3 ≤ D) :
    (∫ z in (densitySpatialBox T K)ᶜ, T.densityKernel D z ∂volume.prod volume) ≤
      K^(3-D)*(∫ z, topProfile 3 z ∂volume.prod volume)*T.area := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hker := T.densityKernel_integrable (by linarith : 2 < D)
  have hthree := T.densityKernel_integrable (by norm_num : (2:ℝ)<3)
  have hpoint (z : ℝ×ℝ) (hz : z ∈ (densitySpatialBox T K)ᶜ) :
      T.densityKernel D z ≤ K^(3-D)*T.densityKernel 3 z := by
    have hr : K ≤ 1+T.radius z := by linarith [densitySpatialBox_radius_lt T K hz]
    have hb : 0 < 1+T.radius z := by linarith [T.radius_nonnegative z]
    have hp := Real.rpow_le_rpow_of_nonpos hKpos hr (by linarith : 3-D ≤ 0)
    calc
      _ = (1+T.radius z)^(3-D)*T.densityKernel 3 z := by
        unfold SlopeBox.densityKernel
        rw [← Real.rpow_add hb]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (T.densityKernel_nonneg 3 z)
  calc
    _ ≤ ∫ z in (densitySpatialBox T K)ᶜ, K^(3-D)*T.densityKernel 3 z ∂volume.prod volume :=
      setIntegral_mono_on hker.integrableOn (hthree.const_mul _).integrableOn
        (densitySpatialBox_measurable T K).compl hpoint
    _ ≤ ∫ z, K^(3-D)*T.densityKernel 3 z ∂volume.prod volume :=
      setIntegral_le_integral (hthree.const_mul _) (Eventually.of_forall
        (fun z => mul_nonneg (Real.rpow_nonneg hKpos.le _) (T.densityKernel_nonneg 3 z)))
    _ = _ := by rw [integral_const_mul,T.integral_densityKernel 3]; ring

theorem density_witness_mass (T : SlopeBox) {K D eta : ℝ}
    (hK : 1 ≤ K) (hD : 3 ≤ D) (_heta : 0 ≤ eta)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (omega : Set ℝ)
    (hE : MeasurableSet E) (hEfinite : (volume.prod volume) E ≠ ∞)
    (hu : Measurable u) (homega : MeasurableSet omega)
    (htail : K^(3-D)*(∫ z, topProfile 3 z ∂volume.prod volume) ≤ eta/2)
    (hdensity : eta*T.area ≤ ∫ z in E ∩ u ⁻¹' omega,
      T.densityKernel D z ∂volume.prod volume) :
    (eta/2)*T.area ≤ (volume.prod volume).real (densityTest E u T omega K) := by
  let A := E ∩ u ⁻¹' omega
  have hA : MeasurableSet A := hE.inter (hu homega)
  have hker := T.densityKernel_integrable (by linarith : 2 < D)
  have hbox := densitySpatialBox_measurable T K
  have hsplit := integral_inter_add_sdiff hbox (hker.integrableOn :
    IntegrableOn (T.densityKernel D) A (volume.prod volume))
  have htest : A ∩ densitySpatialBox T K = densityTest E u T omega K := by
    ext z
    exact and_right_comm
  have htestFinite : (volume.prod volume) (A ∩ densitySpatialBox T K) ≠ ∞ :=
    measure_ne_top_of_subset (fun _ hz => hz.1.1) hEfinite
  have hinside : (∫ z in A ∩ densitySpatialBox T K, T.densityKernel D z ∂volume.prod volume) ≤
      (volume.prod volume).real (A ∩ densitySpatialBox T K) := by
    have h := setIntegral_mono_on hker.integrableOn
      (integrableOn_const htestFinite : IntegrableOn (fun _ : ℝ×ℝ => (1:ℝ))
        (A ∩ densitySpatialBox T K) (volume.prod volume)) (hA.inter hbox)
      (fun z _ => T.densityKernel_le_one (by linarith : 0 ≤ D) z)
    simpa only [setIntegral_const,smul_eq_mul,mul_one] using h
  have houtside : (∫ z in A\densitySpatialBox T K, T.densityKernel D z ∂volume.prod volume) ≤
      (eta/2)*T.area := by
    have hmono := setIntegral_mono_set
      (hker.integrableOn : IntegrableOn (T.densityKernel D) (densitySpatialBox T K)ᶜ (volume.prod volume))
      (Eventually.of_forall (fun z => T.densityKernel_nonneg D z))
      (Eventually.of_forall (fun z (hz : z ∈ A\densitySpatialBox T K) => hz.2))
    exact hmono.trans ((densityKernel_tail T hK hD).trans
      (mul_le_mul_of_nonneg_right htail (by exact mul_nonneg T.length_pos.le T.width_pos.le)))
  rw [htest] at hinside
  rw [htest] at hsplit
  linarith

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

theorem densityValues_nonempty (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) :
    (tile.densityValues ell0 w W tau q E u).Nonempty := ⟨0,Or.inl rfl⟩

theorem densityValues_bddAbove (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) :
    BddAbove (tile.densityValues ell0 w W tau q E u) := by
  refine ⟨∫ z, topProfile 203 z ∂volume.prod volume,?_⟩
  intro x hx
  rcases hx with rfl | ⟨test,rfl⟩
  · exact integral_nonneg (topProfile_nonnegative 203)
  · exact densityAverage_le test.top E u _

theorem exists_test_of_lt_density (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) {eta : ℝ} (heta : 0 ≤ eta)
    (h : eta < tile.density ell0 w W tau q E u) :
    ∃ test : OrdinaryDensityTest ell0 w W tau q tile,
      eta*test.top.area < ∫ z in E ∩
        u ⁻¹' scaledAngularCell (w/ell0) q test.level test.cell,
        test.top.densityKernel 203 z ∂volume.prod volume := by
  obtain ⟨x,hx,hlt⟩ := (lt_csSup_iff
    (tile.densityValues_bddAbove ell0 w W tau q E u)
    (tile.densityValues_nonempty ell0 w W tau q E u)).mp h
  rcases hx with rfl | ⟨test,rfl⟩
  · exact (not_lt_of_ge heta hlt).elim
  · exact ⟨test,(lt_div_iff₀ test.top.area_pos).mp hlt⟩

end OrdinaryDensityTile
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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSignedSizeTest
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The signed size tests used in ordinary tree selection. Failing tests
have a packet witness and admit the manuscript's near-extremal direction. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
attribute [local instance] Classical.propDecidable Classical.decEq

theorem sizeTestEnergy_mono (negative : Bool) (w cb : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    {R S : Finset P.PacketIndex} (hRS : R⊆S) (T : SlopeBox) :
    P.sizeTestEnergy negative w cb cell grid c R T≤P.sizeTestEnergy negative w cb cell grid c S T := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ hRS)
  intro q _ _
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (P.length_pos q.1).le) P.width_pos.le

theorem sizeTestFails_mono (negative : Bool) (w cb tau sigma : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    {R S : Finset P.PacketIndex} (hRS : R⊆S) (T : SlopeBox)
    (hfail : P.sizeTestFails negative w cb tau sigma cell grid c R T) :
    P.sizeTestFails negative w cb tau sigma cell grid c S T :=
  ⟨hfail.1,hfail.2.1,hfail.2.2.trans_le (P.sizeTestEnergy_mono negative w cb cell grid c hRS T)⟩

theorem failing_size_test_nonempty (negative : Bool) (w cb tau sigma : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (R : Finset P.PacketIndex) (T : SlopeBox)
    (hfail : P.sizeTestFails negative w cb tau sigma cell grid c R T) :
    (P.sizeTestPackets negative w cb cell grid R T).Nonempty := by
  by_contra hn
  have he : P.sizeTestPackets negative w cb cell grid R T=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have h := hfail.2.2
  simp only [sizeTestEnergy,he,Finset.sum_empty] at h
  have ha : 0 ≤ sigma^2*T.area/2 := div_nonneg (mul_nonneg (sq_nonneg _) T.area_pos.le) (by norm_num)
  linarith

theorem size_test_direction_lower (negative : Bool) (w cb : ℝ) (hw : 0≤w) (hcb : 0 ≤ cb)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (R : Finset P.PacketIndex)
    (T : SlopeBox) (q : P.PacketIndex) (hq : q∈P.sizeTestPackets negative w cb cell grid R T)
    (L : ℝ) (hL : L ≤ sizeDirection negative (P.rowSlope q.1 q.2.1)) :
    L ≤ sizeDirection negative T.slope := by
  have hd := (Finset.mem_filter.mp hq).2.2.2.2
  have hn : 0 ≤ cb*w/P.length q.1 :=
    div_nonneg (mul_nonneg hcb hw) (P.length_pos q.1).le
  cases negative <;> simp only [sizeDirection,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at * <;> linarith

/-- Near-infimum selection is valid even though test directions vary
continuously. The finite packet family supplies the lower bound. -/
theorem exists_near_first_size_test (negative : Bool) (w cb tau sigma epsilon : ℝ)
    (hw : 0≤w) (hcb : 0 ≤ cb) (hepsilon : 0<epsilon)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (R : Finset P.PacketIndex)
    (hex : ∃ T, P.sizeTestFails negative w cb tau sigma cell grid c R T) :
    ∃ T, P.sizeTestFails negative w cb tau sigma cell grid c R T ∧
      ∀ U, P.sizeTestFails negative w cb tau sigma cell grid c R U →
        sizeDirection negative T.slope < sizeDirection negative U.slope+epsilon := by
  obtain ⟨T0,hT0⟩ := hex
  obtain ⟨q0,_hq0⟩ := P.failing_size_test_nonempty negative w cb tau sigma cell grid c R T0 hT0
  have hne : (Finset.univ : Finset P.PacketIndex).Nonempty := ⟨q0,Finset.mem_univ _⟩
  obtain ⟨q,_hq,hmin⟩ := Finset.exists_min_image (Finset.univ : Finset P.PacketIndex)
    (fun q => sizeDirection negative (P.rowSlope q.1 q.2.1)) hne
  let S : Set ℝ := {x | ∃ T, P.sizeTestFails negative w cb tau sigma cell grid c R T ∧
    sizeDirection negative T.slope=x}
  have hSne : S.Nonempty := ⟨sizeDirection negative T0.slope,T0,hT0,rfl⟩
  have hbelow : BddBelow S := by
    refine ⟨sizeDirection negative (P.rowSlope q.1 q.2.1),?_⟩
    rintro x ⟨T,hT,rfl⟩
    obtain ⟨p,hp⟩ := P.failing_size_test_nonempty negative w cb tau sigma cell grid c R T hT
    exact P.size_test_direction_lower negative w cb hw hcb cell grid R T p hp _
      (hmin p (Finset.mem_univ _))
  obtain ⟨x,hx,hclose⟩ := exists_lt_of_csInf_lt hSne
    (lt_add_of_pos_right (sInf S) hepsilon)
  obtain ⟨T,hT,rfl⟩ := hx
  refine ⟨T,hT,?_⟩
  intro U hU
  exact hclose.trans_le (add_le_add (csInf_le hbelow ⟨U,hU,rfl⟩) le_rfl)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSizeStopping
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite signed size-selection loop. Test directions are
chosen near the extremum; all tiles in the enlarged top are deleted. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
attribute [local instance] Classical.propDecidable Classical.decEq

theorem sizeTestPackets_subset_delete (negative : Bool) (w cb A : ℝ) (hA : 1/2≤A)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (R : Finset P.PacketIndex) (T : SlopeBox) :
    P.sizeTestPackets negative w cb cell grid R T⊆P.sizeDeletePackets w A cell grid R T := by
  intro q hq
  obtain ⟨hR,hlen,hpos,hang,_hsign⟩ := Finset.mem_filter.mp hq
  apply Finset.mem_filter.mpr
  refine ⟨hR,hlen,?_,hang⟩
  exact ⟨hpos.1.trans (mul_le_mul_of_nonneg_right hA T.length_pos.le),
    hpos.2.trans (mul_le_mul_of_nonneg_right hA T.width_pos.le)⟩

theorem exists_size_stopping_run (negative : Bool) (w cb tau sigma epsilon A : ℝ)
    (hw : 0≤w) (hcb : 0 ≤ cb) (hepsilon : 0<epsilon) (hA : 1/2≤A)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (initial : Finset P.PacketIndex) :
    ∃ tops remaining, P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c
      initial tops remaining := by
  induction initial using Finset.strongInductionOn with
  | _ R ih =>
    by_cases hex : ∃ T, P.sizeTestFails negative w cb tau sigma cell grid c R T
    · obtain ⟨T,hT,hfirst⟩ := P.exists_near_first_size_test negative w cb tau sigma epsilon
        hw hcb hepsilon cell grid c R hex
      obtain ⟨q,hq⟩ := P.failing_size_test_nonempty negative w cb tau sigma cell grid c R T hT
      have hqD := P.sizeTestPackets_subset_delete negative w cb A hA cell grid R T hq
      have hqR : q∈R := (Finset.mem_filter.mp hq).1
      have hstrict : R\P.sizeDeletePackets w A cell grid R T⊂R := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.sdiff_subset,?_⟩
        intro heq
        have hmem : q∈R\P.sizeDeletePackets w A cell grid R T := heq.symm ▸ hqR
        exact (Finset.mem_sdiff.mp hmem).2 hqD
      obtain ⟨tops,remaining,hrun⟩ := ih _ hstrict
      exact ⟨T::tops,remaining,SizeStoppingRun.step R T tops remaining hT hfirst hrun⟩
    · exact ⟨[],R,SizeStoppingRun.stop R (not_exists.mp hex)⟩

namespace SizeStoppingRun
variable {P} {negative : Bool} {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem remaining_subset
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining) :
    remaining⊆initial := by
  induction h with
  | stop => exact Finset.Subset.refl _
  | step R T tops remaining _ _ _ ih => exact ih.trans Finset.sdiff_subset

theorem terminal_good
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining) :
    ∀ T, ¬P.sizeTestFails negative w cb tau sigma cell grid c remaining T := by
  induction h with
  | stop R hg => exact hg
  | step _ _ _ _ _ _ _ ih => exact ih

end SizeStoppingRun
end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_PacketDataSizeSelectionEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint recorded tests and the exact energy bookkeeping for the
finite signed size-selection run. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
attribute [local instance] Classical.propDecidable Classical.decEq

theorem recordedSizeTests_subset (negative : Bool) (w cb A : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (R : Finset P.PacketIndex) (tops : List SlopeBox) :
    ∀ Q∈P.recordedSizeTests negative w cb A cell grid R tops, Q⊆R := by
  induction tops generalizing R with
  | nil => simp only [recordedSizeTests,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | cons T tops ih =>
    intro Q hQ
    rcases List.mem_cons.mp hQ with rfl | hQ
    · exact Finset.filter_subset _ _
    · exact (ih _ Q hQ).trans Finset.sdiff_subset

namespace SizeStoppingRun
variable {P} {negative : Bool} {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem top_area_energy
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining) :
    sigma^2/2*(tops.map SlopeBox.area).sum≤
      ((P.recordedSizeTests negative w cb A cell grid initial tops).map (P.packetEnergySum c)).sum := by
  induction h with
  | stop => simp only [List.map_nil,List.sum_nil,mul_zero,le_refl,recordedSizeTests]
  | step R T tops remaining hT _ _ ih =>
    change sigma^2/2*(T.area+(tops.map SlopeBox.area).sum)≤
      P.sizeTestEnergy negative w cb cell grid c R T+
        ((P.recordedSizeTests negative w cb A cell grid
          (R\P.sizeDeletePackets w A cell grid R T) tops).map (P.packetEnergySum c)).sum
    have ht : sigma^2/2*T.area≤P.sizeTestEnergy negative w cb cell grid c R T := by
      have hh := hT.2.2.le
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      ring
    rw [mul_add]
    exact add_le_add ht ih

end SizeStoppingRun
end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_PacketDataSizeSelectionOrder
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The near-extremal selection rule orders every later failing test.
Monotonicity uses the actual decreasing packet sets, not a separate order assumption. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData.SizeStoppingRun
open PacketLatticeData
attribute [local instance] Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable {P : PacketLatticeData N κ Label Item} {negative : Bool}
  {w cb tau sigma epsilon A : ℝ} {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem selected_failing
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining) :
    ∀ T∈tops, P.sizeTestFails negative w cb tau sigma cell grid c initial T := by
  induction h with
  | stop => simp
  | step R T tops remaining hT _ _ ih =>
    intro U hU
    rcases List.mem_cons.mp hU with rfl | hU
    · exact hT
    · exact P.sizeTestFails_mono negative w cb tau sigma cell grid c Finset.sdiff_subset U (ih U hU)

end LipschitzHilbert.PacketLatticeData.SizeStoppingRun

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_PacketDataSelectionRecords
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Paired tops and their actual recorded test packets. Chronological
nondeletion is a conclusion of the finite stopping run. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
attribute [local instance] Classical.propDecidable Classical.decEq

theorem sizeSelectionRecords_packets (negative : Bool) (w cb A : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (R : Finset P.PacketIndex) (tops : List SlopeBox) :
    (P.sizeSelectionRecords negative w cb A cell grid R tops).map Prod.snd =
      P.recordedSizeTests negative w cb A cell grid R tops := by
  induction tops generalizing R with
  | nil => rfl
  | cons T tops ih => simp only [sizeSelectionRecords,List.map_cons,recordedSizeTests,ih]

theorem sizeSelectionRecords_tops (negative : Bool) (w cb A : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (R : Finset P.PacketIndex) (tops : List SlopeBox) :
    (P.sizeSelectionRecords negative w cb A cell grid R tops).map Prod.fst=tops := by
  induction tops generalizing R with
  | nil => rfl
  | cons T tops ih => simp only [sizeSelectionRecords,List.map_cons,ih]

theorem sizeSelectionRecords_subset (negative : Bool) (w cb A : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (R : Finset P.PacketIndex) (tops : List SlopeBox)
    (p : SlopeBox × Finset P.PacketIndex)
    (hp : p ∈ P.sizeSelectionRecords negative w cb A cell grid R tops) : p.2⊆R := by
  apply P.recordedSizeTests_subset negative w cb A cell grid R tops p.2
  rw [←P.sizeSelectionRecords_packets negative w cb A cell grid R tops]
  exact List.mem_map.mpr ⟨p,hp,rfl⟩

namespace SizeStoppingRun
variable {P} {negative : Bool} {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem records_geometry
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining) :
    ∀ p ∈ P.sizeSelectionRecords negative w cb A cell grid initial tops,
      p.1.width=P.width ∧ p.1.length≤tau ∧
      ∀ q∈p.2, P.length q.1≤p.1.length ∧
        (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox p.1 (1/2) ∧
        p.1.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1) ∧
        cb*w/P.length q.1 ≤ sizeDirection negative (p.1.slope-P.rowSlope q.1 q.2.1) := by
  induction h with
  | stop => simp only [sizeSelectionRecords,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | step R T tops remaining hT _ _ ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · refine ⟨hT.1,hT.2.1,?_⟩
      intro q hq
      exact (Finset.mem_filter.mp hq).2
    · exact ih p hp

/-- A later recorded packet lies outside every earlier enlarged deletion
box whenever its scale and angular cell make it eligible for deletion. -/
theorem records_order
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining) :
    (P.sizeSelectionRecords negative w cb A cell grid initial tops).Pairwise
      (fun p p' => sizeDirection negative p.1.slope < sizeDirection negative p'.1.slope+epsilon ∧
        ∀ q∈p'.2, ¬(P.length q.1≤p.1.length ∧
          (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox p.1 A ∧
          p.1.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))) := by
  induction h with
  | stop => exact List.Pairwise.nil
  | step R T tops remaining _ hfirst htail ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih⟩
    intro p hp
    have hpTop : p.1∈tops := by
      rw [←P.sizeSelectionRecords_tops negative w cb A cell grid
        (R\P.sizeDeletePackets w A cell grid R T) tops]
      exact List.mem_map.mpr ⟨p,hp,rfl⟩
    refine ⟨hfirst p.1 (P.sizeTestFails_mono negative w cb tau sigma cell grid c
      Finset.sdiff_subset p.1 (htail.selected_failing p.1 hpTop)),?_⟩
    intro q hq heligible
    have hsub := P.sizeSelectionRecords_subset negative w cb A cell grid
      (R\P.sizeDeletePackets w A cell grid R T) tops p hp hq
    exact (Finset.mem_sdiff.mp hsub).2
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hsub).1,heligible⟩)

end SizeStoppingRun
end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SourceSelectionBoxGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial part of the selected-tree packing argument. Boxes are compared
in a common direction before passing to the selecting top's coordinates. -/
noncomputable section
open Set
namespace LipschitzHilbert

theorem common_direction_center_bounds (x y x' y' t ell r W K : ℝ)
    (hell : ell ≤ r) (hK : 0 ≤ K) (z : ℝ×ℝ)
    (hx : |z.1-x| ≤ K*ell) (hy : |(z.2-y)-t*(z.1-x)| ≤ K*W)
    (hx' : |z.1-x'| ≤ K*r) (hy' : |(z.2-y')-t*(z.1-x')| ≤ K*W) :
    |x-x'| ≤ 2*K*r ∧ |(y-y')-t*(x-x')| ≤ 2*K*W := by
  constructor
  · calc
      _ = |(z.1-x')-(z.1-x)| := by congr 1; ring
      _ ≤ |z.1-x'|+|z.1-x| := abs_sub _ _
      _ ≤ K*r+K*ell := add_le_add hx' hx
      _ ≤ 2*K*r := by nlinarith only [mul_le_mul_of_nonneg_left hell hK]
  · calc
      _ = |((z.2-y')-t*(z.1-x'))-((z.2-y)-t*(z.1-x))| := by congr 1; ring
      _ ≤ |(z.2-y')-t*(z.1-x')|+|(z.2-y)-t*(z.1-x)| := abs_sub _ _
      _ ≤ K*W+K*W := add_le_add hy' hy
      _ = _ := by ring

theorem center_in_enlarged_selecting_top (T : SlopeBox)
    (x y x' y' t r W K C A : ℝ)
    (hW : 0 < W) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hlen : r ≤ T.length) (hwidth : T.width=W)
    (hcenter : (x',y') ∈ densitySpatialBox T (1/2))
    (hx : |x-x'| ≤ 2*K*r)
    (hy : |(y-y')-t*(x-x')| ≤ 2*K*W)
    (hangle : |T.slope-t| * r ≤ C*W)
    (hA : 2*K*(1+C)+1/2 ≤ A) :
    (x,y) ∈ densitySpatialBox T A := by
  have hA' : 2*K+1/2 ≤ A := by nlinarith only [hA,mul_nonneg hK hC]
  refine ⟨?_,?_⟩
  · calc
      _ ≤ |x-x'|+|x'-T.x| := abs_sub_le _ _ _
      _ ≤ 2*K*r+(1/2)*T.length := add_le_add hx hcenter.1
      _ ≤ (2*K+1/2)*T.length := by
        nlinarith only [mul_le_mul_of_nonneg_left hlen (mul_nonneg (by norm_num : (0:ℝ)≤2) hK)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hA' T.length_pos.le
  · have hchange : |(T.slope-t)*(x-x')| ≤ 2*K*C*W := by
      rw [abs_mul]
      calc
        _ ≤ |T.slope-t| * (2*K*r) := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
        _ = 2*K*(|T.slope-t| * r) := by ring
        _ ≤ 2*K*(C*W) := mul_le_mul_of_nonneg_left hangle (mul_nonneg (by norm_num) hK)
        _ = _ := by ring
    calc
      _ = |((y-y')-t*(x-x'))-((T.slope-t)*(x-x'))+
          ((y'-T.y)-T.slope*(x'-T.x))| := by congr 1; ring
      _ ≤ |(y-y')-t*(x-x')|+|(T.slope-t)*(x-x')|+
          |(y'-T.y)-T.slope*(x'-T.x)| := (abs_add_le _ _).trans
        (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ 2*K*W+2*K*C*W+(1/2)*W :=
        add_le_add (add_le_add hy hchange) (by simpa only [hwidth] using hcenter.2)
      _ = (2*K*(1+C)+1/2)*W := by ring
      _ ≤ A*T.width := by rw [hwidth]; exact mul_le_mul_of_nonneg_right hA hW.le

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePlanarPlancherel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product-coordinate Plancherel and the common-frequency witness
needed for the actual planar packet Gram matrix. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert

/-- Plancherel for the manuscript's product-coordinate Fourier transform. -/
theorem planar_integral_inner_fourier (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    (∫ z, inner ℂ (planarFourier f z) (planarFourier g z) ∂volume.prod volume)=
      ∫ z, inner ℂ (f z) (g z) ∂volume.prod volume := by
  calc
    _ = ∫ x : HilbertPlane, inner ℂ (𝓕 (liftPlanar f) x) (𝓕 (liftPlanar g) x) := by
      rw [integral_hilbertPlane]
      simp only [fourier_liftPlanar]
    _ = ∫ x : HilbertPlane, inner ℂ (liftPlanar f x) (liftPlanar g x) :=
      SchwartzMap.integral_inner_fourier_fourier (liftPlanar f) (liftPlanar g)
    _ = _ := by
      rw [integral_hilbertPlane]
      rfl

theorem planar_inner_eq_zero_of_disjoint (f g : SchwartzMap (ℝ×ℝ) ℂ)
    (hdisjoint : ∀ z, planarFourier f z=0 ∨ planarFourier g z=0) :
    (∫ z, inner ℂ (f z) (g z) ∂volume.prod volume)=0 := by
  rw [←planar_integral_inner_fourier f g]
  have hz (z : ℝ×ℝ) : inner ℂ (planarFourier f z) (planarFourier g z)=0 := by
    rcases hdisjoint z with hf | hg
    · rw [hf,inner_zero_left]
    · rw [hg,inner_zero_right]
  simp only [hz,integral_zero]

/-- Nonzero interaction gives an actual common angular frequency;
no support-overlap premise is added to the packet estimate. -/
theorem exists_common_angular_frequency (f g : SchwartzMap (ℝ×ℝ) ℂ)
    (hinner : (∫ z, inner ℂ (f z) (g z) ∂volume.prod volume)≠0) :
    ∃ ξ η, planarAngularFourier f (ξ,η)≠0 ∧ planarAngularFourier g (ξ,η)≠0 := by
  have hex : ∃ z, planarFourier f z≠0 ∧ planarFourier g z≠0 := by
    by_contra h
    apply hinner
    apply planar_inner_eq_zero_of_disjoint f g
    intro z
    by_cases hf : planarFourier f z=0
    · exact Or.inl hf
    · exact Or.inr (by by_contra hg; exact h ⟨z,hf,hg⟩)
  obtain ⟨z,hf,hg⟩ := hex
  refine ⟨(2*Real.pi)*z.1,(2*Real.pi)*z.2,?_,?_⟩
  · simpa only [planarAngularFourier,mul_div_cancel_left₀ _ (by positivity : (2:ℝ)*Real.pi≠0)] using hf
  · simpa only [planarAngularFourier,mul_div_cancel_left₀ _ (by positivity : (2:ℝ)*Real.pi≠0)] using hg

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceGramGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual nonzero Gram interactions force the angular proximity used
in the selected-tree Bessel argument. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert

private theorem common_wedge_distance (xi eta theta phi ell r w cStar cEta : ℝ)
    (hell : 0<ell) (hr : 0 < r) (hw : 0<w) (hcEta : 0 < cEta)
    (he : cEta≤w*eta) (hs : |xi+theta*eta| ≤ cStar/ell)
    (ht : |xi+phi*eta| ≤ cStar/r) :
    |theta-phi|≤(cStar/cEta)*(w/ell+w/r) := by
  have heta : 0<eta := by nlinarith
  have hdiff : |(theta-phi)*eta| ≤ cStar/ell+cStar/r := by
    calc
      _ = |(xi+theta*eta)-(xi+phi*eta)| := by congr 1; ring
      _ ≤ |xi+theta*eta|+|xi+phi*eta| := abs_sub _ _
      _ ≤ _ := add_le_add hs ht
  have hscaled : |theta-phi| * cEta≤w*(cStar/ell+cStar/r) := by
    calc
      _ ≤ |theta-phi| * (w*eta) := mul_le_mul_of_nonneg_left he (abs_nonneg _)
      _ = w*|(theta-phi)*eta| := by rw [abs_mul,abs_of_pos heta]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiff hw.le
  have h := (le_div_iff₀ hcEta).mpr hscaled
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

theorem planar_packet_gram_angle (f g : SchwartzMap (ℝ×ℝ) ℂ)
    (theta phi ell r w cStar cEta CEta : ℝ)
    (hell : 0<ell) (hr : 0 < r) (hw : 0<w) (hcEta : 0 < cEta)
    (hf : ∀ xi eta, planarAngularFourier f (xi,eta)≠0 →
      |xi+theta*eta| ≤ cStar/ell ∧ cEta≤w*eta ∧ w*eta≤CEta)
    (hg : ∀ xi eta, planarAngularFourier g (xi,eta)≠0 →
      |xi+phi*eta| ≤ cStar/r ∧ cEta≤w*eta ∧ w*eta≤CEta)
    (hinner : (∫ z, inner ℂ (f z) (g z) ∂volume.prod volume)≠0) :
    |theta-phi|≤(cStar/cEta)*(w/ell+w/r) := by
  obtain ⟨xi,eta,hfi,hgi⟩ := exists_common_angular_frequency f g hinner
  exact common_wedge_distance xi eta theta phi ell r w cStar cEta hell hr hw hcEta
    (hf xi eta hfi).2.1 (hf xi eta hfi).1 (hg xi eta hgi).1

/-- A sufficiently longer interacting packet lies close to the longer
tree's direction in units of the shorter packet's angular scale. -/
theorem gram_short_direction (f g : SchwartzMap (ℝ×ℝ) ℂ)
    (theta phi t ell r w cStar cEta CEta cOne COmega CZero : ℝ)
    (hell : 0<ell) (hr : 0 < r) (hw : 0<w) (hcStar : 0 ≤ cStar)
    (hcEta : 0 < cEta) (hCOmega : 0≤COmega) (hCZero : 0<CZero)
    (hlong : CZero*ell ≤ r)
    (hconstants : (cStar/cEta)*(1+1/CZero)+COmega/CZero ≤ cOne/4)
    (htop : |phi-t|≤COmega*(w/r))
    (hf : ∀ xi eta, planarAngularFourier f (xi,eta)≠0 →
      |xi+theta*eta| ≤ cStar/ell ∧ cEta≤w*eta ∧ w*eta≤CEta)
    (hg : ∀ xi eta, planarAngularFourier g (xi,eta)≠0 →
      |xi+phi*eta| ≤ cStar/r ∧ cEta≤w*eta ∧ w*eta≤CEta)
    (hinner : (∫ z, inner ℂ (f z) (g z) ∂volume.prod volume)≠0) :
    |theta-t|≤(cOne/4)*(w/ell) := by
  have hgram := planar_packet_gram_angle f g theta phi ell r w cStar cEta CEta
    hell hr hw hcEta hf hg hinner
  have hscale : w/r≤(1/CZero)*(w/ell) := by
    apply (div_le_iff₀ hr).mpr
    have h := mul_le_mul_of_nonneg_left hlong (div_nonneg hw.le (mul_pos hCZero hell).le)
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)
  have hc : 0 ≤ cStar/cEta := div_nonneg hcStar hcEta.le
  calc
    _ ≤ |theta-phi|+|phi-t| := abs_sub_le _ _ _
    _ ≤ (cStar/cEta)*(w/ell+w/r)+COmega*(w/r) := add_le_add hgram htop
    _ ≤ (cStar/cEta)*(w/ell+(1/CZero)*(w/ell))+COmega*((1/CZero)*(w/ell)) :=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hscale) hc)
        (mul_le_mul_of_nonneg_left hscale hCOmega)
    _ = ((cStar/cEta)*(1+1/CZero)+COmega/CZero)*(w/ell) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hconstants (div_nonneg hw.le hell.le)

/-- The near-extremal direction rule rules out the wrong temporal order
once these two geometric slope estimates hold. -/
theorem selected_direction_order_contradiction
    (theta t selected other d cOne epsilon : ℝ)
    (hd : 0<d) (hcOne : 0 < cOne)
    (hnear : |theta-t| ≤ cOne*d/4)
    (hselected : theta+cOne*d ≤ selected)
    (hother : |other-t| ≤ cOne*d/4)
    (hepsilon : epsilon ≤ cOne*d/4)
    (hfirst : selected<other+epsilon) : False := by
  have h1 := (abs_le.mp hnear).1
  have h2 := (abs_le.mp hother).2
  have hpos : 0 < cOne*d := mul_pos hcOne hd
  nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_PacketDataDirectionLatticeCount
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The number of actual spatial lattice boxes through a point is bounded
at one scale and label, uniformly in the comparison direction. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert

private theorem envelope_lower_near_p0 (a x r K : ℝ) (hr : 0 < r)
    (hx : |x-a|≤K*r) : 1≤(1+K^2)*lineEnvelope a r 1 x := by
  have ht : |(x-a)/r|≤K := by
    rw [abs_div,abs_of_pos hr]
    exact (div_le_iff₀ hr).mpr hx
  have hs := pow_le_pow_left₀ (abs_nonneg _) ht 2
  rw [sq_abs] at hs
  simp only [lineEnvelope,pow_one]
  rw [←div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity)).mpr (by linarith)

namespace PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem direction_lattice_count (j : Fin N) (l : P.labels j)
    (S : Finset (Item j l)) (t K D : ℝ) (hK : 0≤K)
    (hangle : |t-P.rowSlope j l| * P.length j≤D*P.width)
    (z : ℝ×ℝ)
    (hbox : ∀ u∈S, z∈densitySpatialBox (P.directionBox t ⟨j,⟨l,u⟩⟩) K) :
    (S.card:ℝ)≤((1+K^2)*(1+(K*(1+D))^2))*(4*Real.pi)^2 := by
  classical
  let theta := P.rowSlope j l
  let y := z.2-theta*z.1
  let b := P.originZ j l-theta*P.originX j l
  let Ex := fun u => lineEnvelope (P.actualX j l u) (P.length j) 1 z.1
  let Ey := fun u => lineEnvelope (b+P.width*(P.site j l u).2) P.width 1 y
  let A := (1+K^2)*(1+(K*(1+D))^2)
  have hA : 0≤A := mul_nonneg (by positivity) (by positivity)
  have hy (u : Item j l) (hu : u∈S) :
      |y-(b+P.width*(P.site j l u).2)|≤(K*(1+D))*P.width := by
    have hz := hbox u hu
    have hx : |z.1-P.actualX j l u|≤K*P.length j := hz.1
    have he : y-(b+P.width*(P.site j l u).2)=
        ((z.2-P.actualZ j l u)-t*(z.1-P.actualX j l u))+
        (t-theta)*(z.1-P.actualX j l u) := by
      dsimp [y,b,theta,actualX,actualZ]
      ring
    rw [he]
    calc
      _ ≤ |(z.2-P.actualZ j l u)-t*(z.1-P.actualX j l u)|+
          |(t-theta)*(z.1-P.actualX j l u)| := abs_add_le _ _
      _ ≤ K*P.width+|t-theta| * (K*P.length j) :=
        add_le_add hz.2 (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg _))
      _ = K*P.width+K*(|t-theta| * P.length j) := by ring
      _ ≤ K*P.width+K*(D*P.width) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hangle hK)
      _ = _ := by ring
  have hpoint (u : Item j l) (hu : u∈S) : 1≤A*(Ex u*Ey u) := by
    have hx := envelope_lower_near_p0 (P.actualX j l u) z.1 (P.length j) K
      (P.length_pos j) (hbox u hu).1
    have ht := envelope_lower_near_p0 (b+P.width*(P.site j l u).2) y P.width (K*(1+D))
      P.width_pos (hy u hu)
    have hh := mul_le_mul hx ht (by norm_num : (0:ℝ)≤1) (le_trans (by norm_num) hx)
    calc
      (1:ℝ) = 1*1 := by norm_num
      _ ≤ ((1+K^2)*Ex u)*((1+(K*(1+D))^2)*Ey u) := hh
      _ = A*(Ex u*Ey u) := by dsimp only [A]; ring
  have hsum : (∑ u∈S, Ex u*Ey u)≤(4*Real.pi)^2 := by
    have hh := finite_scaled_plane_lattice_overlap (P.originX j l) b (P.length j) P.width z.1 y
      (P.length_pos j).ne' P.width_pos.ne' (S.image (P.site j l))
      (by decide : 1≤1) (by decide : 1≤1)
    rw [Finset.sum_image (fun _ _ _ _ he => P.site_injective j l he)] at hh
    exact hh
  calc
    _ = ∑ _u∈S, (1:ℝ) := by simp
    _ ≤ ∑ u∈S, A*(Ex u*Ey u) := Finset.sum_le_sum hpoint
    _ = A*∑ u∈S, Ex u*Ey u := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hA

end PacketLatticeData
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_PacketDataDirectionLabelCount
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local angular multiplicity supplies the per-scale packing constant.
There is no dependence on the total number of available labels. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem direction_label_count (j : Fin N)
    (items : ∀ l : P.labels j, Finset (Item j l))
    (t w K R : ℝ) (hw : 0<w) (hwW : w≤P.width) (hK : 0≤K) (hR : 0≤R)
    (M Q : ℕ) (hQ : R≤Q)
    (hmultiplicity : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (P.rowSlope j) (w/P.length j) M)
    (hnear : ∀ l, (items l).Nonempty → |P.rowSlope j l-t|≤R*(w/P.length j))
    (z : ℝ×ℝ)
    (hbox : ∀ l u, u∈items l → z∈densitySpatialBox (P.directionBox t ⟨j,⟨l,u⟩⟩) K) :
    (∑ l : P.labels j, ((items l).card:ℝ))≤
      (((2*Q+1)*M:ℕ):ℝ)*(((1+K^2)*(1+(K*(1+R))^2))*(4*Real.pi)^2) := by
  classical
  let active := SourceSlopeLabels.window Finset.univ (P.rowSlope j) t (w/P.length j) R
  let C := ((1+K^2)*(1+(K*(1+R))^2))*(4*Real.pi)^2
  have hC : 0≤C := by dsimp [C]; positivity
  have hcard : active.card≤(2*Q+1)*M :=
    SourceSlopeLabels.window_card_le Finset.univ (P.rowSlope j)
      (div_pos hw (P.length_pos j)) hmultiplicity hQ
  have hsum : (∑ l : P.labels j, ((items l).card:ℝ))=
      ∑ l∈active, ((items l).card:ℝ) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ active)
    intro l _ hl
    have he : items l=∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hn
      exact hl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnear l hn⟩)
    simp only [he,Finset.card_empty,Nat.cast_zero]
  rw [hsum]
  have hlocal (l : P.labels j) (hl : l∈active) : ((items l).card:ℝ)≤C := by
    apply P.direction_lattice_count j l (items l) t K R hK ?_ z (hbox l)
    have hn := (Finset.mem_filter.mp hl).2
    have hb : |t-P.rowSlope j l| * P.length j≤R*w := by
      calc
        _ ≤ (R*(w/P.length j))*P.length j :=
          mul_le_mul_of_nonneg_right (by simpa only [abs_sub_comm] using hn) (P.length_pos j).le
        _ = _ := by field_simp [(P.length_pos j).ne']
    exact hb.trans (mul_le_mul_of_nonneg_left hwW hR)
  calc
    _ ≤ ∑ _l∈active, C := Finset.sum_le_sum hlocal
    _ = (active.card:ℝ)*C := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hC

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceGramMargin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed angular margin of an actual packet transfers to every
direction sufficiently close to its slope, using a common Fourier witness. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

private theorem frequency_slope_distance (xi eta theta ell w cStar cEta : ℝ)
    (hell : 0<ell) (hw : 0<w) (hcEta : 0 < cEta)
    (he : cEta≤w*eta) (hs : |xi+theta*eta| ≤ cStar/ell) :
    |theta-(-xi/eta)|≤(cStar/cEta)*(w/ell) := by
  have heta : 0<eta := by nlinarith
  have hid : |theta-(-xi/eta)| * eta=|xi+theta*eta| := by
    calc
      _ = |(theta-(-xi/eta))*eta| := by rw [abs_mul,abs_of_pos heta]
      _ = _ := by congr 1; field_simp; ring
  have hbound : |theta-(-xi/eta)| * cEta≤w*(cStar/ell) := by
    calc
      _ ≤ |theta-(-xi/eta)| * (w*eta) := mul_le_mul_of_nonneg_left he (abs_nonneg _)
      _ = w*|xi+theta*eta| := by rw [←hid]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs hw.le
  have h := (le_div_iff₀ hcEta).mpr hbound
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

/-- This uses the manuscript's support margin, not an assumed angular
membership for the direction that will be used in deletion. -/
theorem gram_margin_direction_mem (f g : SchwartzMap (ℝ×ℝ) ℂ)
    (theta ell w cStar cEta margin u : ℝ) (omega : Set ℝ)
    (hell : 0<ell) (hw : 0<w) (hcEta : 0 < cEta)
    (hf : ∀ xi eta, planarAngularFourier f (xi,eta)≠0 →
      |xi+theta*eta| ≤ cStar/ell ∧ cEta≤w*eta)
    (hmargin : ∀ xi eta, planarAngularFourier f (xi,eta)≠0 →
      Icc (-xi/eta-margin*(w/ell)) (-xi/eta+margin*(w/ell))⊆omega)
    (hu : |u-theta|≤(margin-cStar/cEta)*(w/ell))
    (hinner : (∫ z, inner ℂ (f z) (g z) ∂volume.prod volume)≠0) : u∈omega := by
  obtain ⟨xi,eta,hfi,_⟩ := exists_common_angular_frequency f g hinner
  have hd := frequency_slope_distance xi eta theta ell w cStar cEta hell hw hcEta
    (hf xi eta hfi).2 (hf xi eta hfi).1
  have hu' : |u-(-xi/eta)| ≤ margin*(w/ell) := by
    calc
      _ ≤ |u-theta|+|theta-(-xi/eta)| := abs_sub_le _ _ _
      _ ≤ (margin-cStar/cEta)*(w/ell)+(cStar/cEta)*(w/ell) := add_le_add hu hd
      _ = _ := by ring
  apply hmargin xi eta hfi
  obtain ⟨hl,hr⟩ := abs_le.mp hu'
  constructor <;> linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceSelectionAngularGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact angular cell widths and the scale comparison used to discharge
the direction hypotheses in selected-box separation. -/
noncomputable section
open Set
namespace LipschitzHilbert

theorem angular_scale_ratio (w ell r CZero : ℝ) (hw : 0≤w)
    (hell : 0<ell) (hr : 0 < r) (hCZero : 0<CZero) (hlen : CZero*ell ≤ r) :
    w/r≤(1/CZero)*(w/ell) := by
  apply (div_le_iff₀ hr).mpr
  have h := mul_le_mul_of_nonneg_left hlen (div_nonneg hw (mul_pos hCZero hell).le)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SourceScalePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separated-scale disjointness limits all boxes through a point to one
fixed window of scales. This converts per-scale lattice counts into the
uniform packing estimate used in the Bessel argument. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem scale_window_packing {ι X : Type*} (S : Finset ι)
    (level : ι → ℕ) (box : ι → Set X) (gap : ℕ) (B : ℝ)
    (hdisjoint : ∀ i∈S, ∀ j∈S, level i+gap≤level j → Disjoint (box i) (box j))
    (hscale : ∀ z k, ((S.filter fun i => level i=k ∧ z∈box i).card:ℝ)≤B)
    (z : X) : ((S.filter fun i => z∈box i).card:ℝ)≤gap*B := by
  classical
  let active := S.filter fun i => z∈box i
  by_cases hne : active.Nonempty
  · obtain ⟨i,hi,hmin⟩ := active.exists_min_image level hne
    let bins := Finset.Ico (level i) (level i+gap)
    have hmaps : (active:Set ι).MapsTo level bins := by
      intro j hj
      refine Finset.mem_Ico.mpr ⟨hmin j hj,?_⟩
      by_contra hn
      have hle : level i+gap≤level j := le_of_not_gt hn
      have hid := Finset.mem_filter.mp hi
      have hjd := Finset.mem_filter.mp hj
      exact Set.disjoint_left.mp (hdisjoint i hid.1 j hjd.1 hle) hid.2 hjd.2
    have hfiber (k : ℕ) : ((active.filter fun j => level j=k).card:ℝ)≤B := by
      apply (Nat.cast_le.mpr (Finset.card_le_card ?_)).trans (hscale z k)
      intro j hj
      obtain ⟨hj,hk⟩ := Finset.mem_filter.mp hj
      obtain ⟨hjS,hjz⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨hjS,hk,hjz⟩
    have hcount : bins.card=gap := by simp [bins]
    change (active.card:ℝ)≤_
    rw [Finset.card_eq_sum_card_fiberwise hmaps,Nat.cast_sum]
    calc
      _ ≤ ∑ k∈bins, B := Finset.sum_le_sum (fun k _ => hfiber k)
      _ = _ := by simp only [Finset.sum_const,hcount,nsmul_eq_mul]
  · have hzero : active=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hB : 0≤B := by
      have h := hscale z 0
      exact (Nat.cast_nonneg _).trans h
    change (active.card:ℝ)≤_
    rw [hzero,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hB

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataScaleGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem length_antitone (P : PacketLatticeData N κ Label Item) : Antitone P.length := by
  intro i j hij
  unfold length
  exact div_le_div_of_nonneg_left P.topLength_pos.le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hij)


theorem length_scale_gap (i j : Fin N) (gap : ℕ) (hgap : i.val+gap≤j.val) :
    (2:ℝ)^gap*P.length j≤P.length i := by
  have he : (2:ℝ)^(i.val+gap)≤(2:ℝ)^j.val :=
    pow_le_pow_right₀ (by norm_num) hgap
  rw [pow_add] at he
  unfold length
  apply (le_div_iff₀ (pow_pos (by norm_num) _)).mpr
  calc
    _ = (P.topLength*((2:ℝ)^i.val*2^gap))/2^j.val := by ring
    _ ≤ P.topLength := (div_le_iff₀ (pow_pos (by norm_num) _)).mpr
      (mul_le_mul_of_nonneg_left he P.topLength_pos.le)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataPacketScaleCount
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindex the actual packets at one scale into their original labels
and spatial sites, then apply the uniform lattice count. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

private theorem filter_card_sum {α : Type*} [Fintype α] (S : Finset α) (p : α → Prop) [DecidablePred p] :
    ((S.filter p).card:ℝ)=∑ i : α, if i∈S ∧ p i then (1:ℝ) else 0 := by
  rw [←Finset.sum_filter]
  have he : Finset.univ.filter (fun i => i∈S ∧ p i)=S.filter p := by ext; simp
  rw [he]
  simp

theorem scale_card_eq_labels (S : Finset P.PacketIndex) (j : Fin N)
    (keep : P.PacketIndex → Prop) :
    ((S.filter fun q => q.1=j ∧ keep q).card:ℝ)=
      ∑ l : P.labels j, ((Finset.univ.filter fun u : Item j l =>
        (⟨j,⟨l,u⟩⟩:P.PacketIndex)∈S ∧ keep ⟨j,⟨l,u⟩⟩).card:ℝ) := by
  refine (filter_card_sum S (fun q : P.PacketIndex => q.1=j ∧ keep q)).trans ?_
  simp only [Fintype.sum_sigma]
  rw [Finset.sum_eq_single j]
  · apply Finset.sum_congr rfl
    intro l _
    symm
    convert filter_card_sum Finset.univ (fun u : Item j l =>
      (⟨j,⟨l,u⟩⟩:P.PacketIndex)∈S ∧ keep ⟨j,⟨l,u⟩⟩) using 1 <;> first | (with_reducible_and_instances rfl) | (simp)
  · intro i _ hij
    apply Finset.sum_eq_zero
    intro l _
    apply Finset.sum_eq_zero
    intro u _
    simp [hij]
  · simp

theorem direction_packets_count (S : Finset P.PacketIndex)
    (t w K R : ℝ) (hw : 0<w) (hwW : w≤P.width) (hK : 0≤K) (hR : 0≤R)
    (M Q : ℕ) (hQ : R≤Q)
    (hmultiplicity : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (P.rowSlope j) (w/P.length j) M)
    (hnear : ∀ q∈S, |P.rowSlope q.1 q.2.1-t|≤R*(w/P.length q.1))
    (z : ℝ×ℝ) (k : ℕ) :
    ((S.filter fun q => q.1.val=k ∧ z∈densitySpatialBox (P.directionBox t q) K).card:ℝ)≤
      (((2*Q+1)*M:ℕ):ℝ)*(((1+K^2)*(1+(K*(1+R))^2))*(4*Real.pi)^2) := by
  by_cases hk : k<N
  · let j : Fin N := ⟨k,hk⟩
    have heq : (S.filter fun q => q.1.val=k ∧ z∈densitySpatialBox (P.directionBox t q) K)=
        S.filter fun q => q.1=j ∧ z∈densitySpatialBox (P.directionBox t q) K := by
      ext q
      simp only [Finset.mem_filter]
      have hj : q.1.val=k ↔ q.1=j := ⟨fun he => Fin.ext he,fun he => congrArg Fin.val he⟩
      rw [hj]
    rw [heq,P.scale_card_eq_labels]
    apply P.direction_label_count j _ t w K R hw hwW hK hR M Q hQ (hmultiplicity j)
    · intro l hl
      obtain ⟨u,hu⟩ := hl
      exact hnear ⟨j,⟨l,u⟩⟩ (Finset.mem_filter.mp hu).2.1
    · intro l u hu
      exact (Finset.mem_filter.mp hu).2.2
  · have heq : (S.filter fun q => q.1.val=k ∧ z∈densitySpatialBox (P.directionBox t q) K)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      have hqk := (Finset.mem_filter.mp hq).2.1
      exact hk (hqk ▸ q.1.isLt)
    rw [heq,Finset.card_empty,Nat.cast_zero]
    positivity

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PacketDataSelectionAngularGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace LipschitzHilbert

namespace PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem angular_cell_distance (w : ℝ) (hw : 0<w) (grid : ℤ)
    (j : Fin N) (k : ℤ) (s t : ℝ)
    (hs : s∈scaledAngularCell (w/P.topLength) grid j.val k)
    (ht : t∈scaledAngularCell (w/P.topLength) grid j.val k) :
    |s-t|≤w/P.length j := by
  have h := scaledAngularCell_slope (div_pos hw P.topLength_pos)
    (le_refl (j.val:ℤ)) ⟨s,hs,hs⟩ hs ht
  have he : (w/P.topLength)*DyadicLineGrid.scale j.val=w/P.length j := by
    unfold length DyadicLineGrid.scale
    rw [zpow_natCast]
    field_simp [P.topLength_pos.ne']
  rwa [he] at h

end PacketLatticeData
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSignedBoxSeparation
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric separation argument for either sign of the actual
size-selection run. Negating the direction order preserves the required
absolute slope distances; physical boxes keep their original coordinates. -/
noncomputable section
open Set
namespace LipschitzHilbert

private theorem signed_chronology_p0 {α : Type*} {R : α → α → Prop} {xs : List α}
    (h : xs.Pairwise R) {a b : α} (ha : a∈xs) (hb : b∈xs) :
    a=b ∨ R a b ∨ R b a := by
  induction xs with
  | nil => simp only [List.not_mem_nil] at ha
  | cons x xs ih =>
    obtain ⟨hx,ht⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with rfl | hax
    · rcases List.mem_cons.mp hb with rfl | hbx
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (hx _ hbx))
    · rcases List.mem_cons.mp hb with rfl | hbx
      · exact Or.inr (Or.inr (hx _ hax))
      · exact ih ht hax hbx

namespace PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

 theorem sizeDirection_sub (negative : Bool) (x y : ℝ) :
    sizeDirection negative (x-y)=sizeDirection negative x-sizeDirection negative y := by
  cases negative
  · rfl
  · simp only [sizeDirection,ite_true, if_true]
    ring

 theorem abs_sizeDirection_sub (negative : Bool) (x y : ℝ) :
    |sizeDirection negative x-sizeDirection negative y|=|x-y| := by
  cases negative
  · rfl
  · simp only [sizeDirection,ite_true, if_true]
    rw [show -x - -y=-(x-y) by ring,abs_neg]

namespace SizeStoppingRun
variable {P : PacketLatticeData N κ Label Item} {negative : Bool}
  {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem selected_boxes_disjoint_signed
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hw : 0<w) (hcb : 0 < cb) (t K C : ℝ) (hK : 0≤K) (hC : 0≤C)
    (hA : 2*K*(1+C)+1/2≤A)
    (p p' : SlopeBox × Finset P.PacketIndex)
    (hp : p∈P.sizeSelectionRecords negative w cb A cell grid initial tops)
    (hp' : p'∈P.sizeSelectionRecords negative w cb A cell grid initial tops)
    (q q' : P.PacketIndex) (hq : q∈p.2) (hq' : q'∈p'.2)
    (hlen : P.length q.1≤P.length q'.1)
    (hnear : |P.rowSlope q.1 q.2.1-t| ≤ cb*(w/P.length q.1)/4)
    (htopnear : |p'.1.slope-t| ≤ cb*(w/P.length q.1)/4)
    (htopscaled : |p'.1.slope-t| * P.length q'.1≤C*P.width)
    (hepsilon : epsilon ≤ cb*(w/P.length q.1)/4)
    (hmargin : p'.1.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) :
    Disjoint (densitySpatialBox (P.directionBox t q) K)
      (densitySpatialBox (P.directionBox t q') K) := by
  have hgeom := h.records_geometry p hp
  have hgeom' := h.records_geometry p' hp'
  have hqgeom := hgeom.2.2 q hq
  have hqgeom' := hgeom'.2.2 q' hq'
  have hsep : sizeDirection negative (P.rowSlope q.1 q.2.1)+cb*(w/P.length q.1)≤
      sizeDirection negative p.1.slope := by
    have hs := hqgeom.2.2.2
    rw [sizeDirection_sub,mul_div_assoc] at hs
    linarith
  have hn : |sizeDirection negative (P.rowSlope q.1 q.2.1)-sizeDirection negative t|≤
      cb*(w/P.length q.1)/4 := by simpa only [abs_sizeDirection_sub] using hnear
  have htn : |sizeDirection negative p'.1.slope-sizeDirection negative t|≤
      cb*(w/P.length q.1)/4 := by simpa only [abs_sizeDirection_sub] using htopnear
  apply Set.disjoint_left.mpr
  intro z hz hz'
  rcases signed_chronology_p0 h.records_order hp hp' with heq | horder | horder
  · rw [heq] at hsep
    have hleft := (abs_le.mp hn).1
    have hright := (abs_le.mp htn).2
    have hpos := mul_pos hcb (div_pos hw (P.length_pos q.1))
    linarith
  · have ho := horder.1
    exact selected_direction_order_contradiction _ _ _ _ _ _ _
      (div_pos hw (P.length_pos q.1)) hcb hn hsep htn hepsilon ho
  · have hcenters := common_direction_center_bounds
      (P.actualX q.1 q.2.1 q.2.2) (P.actualZ q.1 q.2.1 q.2.2)
      (P.actualX q'.1 q'.2.1 q'.2.2) (P.actualZ q'.1 q'.2.1 q'.2.2)
      t (P.length q.1) (P.length q'.1) P.width K hlen hK z
      hz.1 hz.2 hz'.1 hz'.2
    have hcenter := center_in_enlarged_selecting_top p'.1
      (P.actualX q.1 q.2.1 q.2.2) (P.actualZ q.1 q.2.1 q.2.2)
      (P.actualX q'.1 q'.2.1 q'.2.2) (P.actualZ q'.1 q'.2.1 q'.2.2)
      t (P.length q'.1) P.width K C A P.width_pos hK hC
      hqgeom'.1 hgeom'.1 hqgeom'.2.1 hcenters.1 hcenters.2 htopscaled hA
    exact horder.2 q hq ⟨hlen.trans hqgeom'.1,hcenter,hmargin⟩


end SizeStoppingRun
end PacketLatticeData
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PacketDataSignedAngularGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular margins discharge the direction hypotheses of signed
selected-box separation, for both passes of the stopping procedure. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketLatticeData.SizeStoppingRun
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable {P : PacketLatticeData N κ Label Item} {negative : Bool}
  {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem selected_top_direction_bound_signed
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hw : 0<w) (t : ℝ) (p : SlopeBox × Finset P.PacketIndex)
    (hp : p∈P.sizeSelectionRecords negative w cb A cell grid initial tops)
    (q : P.PacketIndex) (hq : q∈p.2)
    (hrow : P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (hnear : |P.rowSlope q.1 q.2.1-t| ≤ cb*(w/P.length q.1)/4) :
    |p.1.slope-t|≤(1+cb/4)*(w/P.length q.1) := by
  have hgeom := (h.records_geometry p hp).2.2 q hq
  have hd := P.angular_cell_distance w hw grid q.1 (cell q.1 q.2.1)
    p.1.slope (P.rowSlope q.1 q.2.1) hgeom.2.2.1 hrow
  calc
    _ ≤ |p.1.slope-P.rowSlope q.1 q.2.1|+|P.rowSlope q.1 q.2.1-t| := abs_sub_le _ _ _
    _ ≤ w/P.length q.1+cb*(w/P.length q.1)/4 := add_le_add hd hnear
    _ = _ := by ring

/-- The geometric separation now needs only the packet-cell margins and
the two packet slope bounds; it does not assume the later top's direction. -/
theorem selected_boxes_disjoint_of_margin_signed
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hw : 0<w) (hwW : w≤P.width) (hcb : 0 < cb)
    (t K CZero : ℝ) (hK : 0≤K) (hCZero : 0<CZero)
    (hconstants : (1+cb/4)/CZero ≤ cb/4)
    (hA : 2*K*(1+(1+cb/4))+1/2≤A)
    (p p' : SlopeBox × Finset P.PacketIndex)
    (hp : p∈P.sizeSelectionRecords negative w cb A cell grid initial tops)
    (hp' : p'∈P.sizeSelectionRecords negative w cb A cell grid initial tops)
    (q q' : P.PacketIndex) (hq : q∈p.2) (hq' : q'∈p'.2)
    (hlen : P.length q.1≤P.length q'.1)
    (hfar : CZero*P.length q.1≤P.length q'.1)
    (hnear : |P.rowSlope q.1 q.2.1-t| ≤ cb*(w/P.length q.1)/4)
    (hnear' : |P.rowSlope q'.1 q'.2.1-t| ≤ cb*(w/P.length q'.1)/4)
    (hrow' : P.rowSlope q'.1 q'.2.1∈scaledAngularCell (w/P.topLength) grid q'.1.val (cell q'.1 q'.2.1))
    (hepsilon : epsilon ≤ cb*(w/P.length q.1)/4)
    (hmargin : Icc (P.rowSlope q.1 q.2.1-cb*(w/P.length q.1)/2)
      (P.rowSlope q.1 q.2.1+cb*(w/P.length q.1)/2)⊆
        scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) :
    Disjoint (densitySpatialBox (P.directionBox t q) K)
      (densitySpatialBox (P.directionBox t q') K) := by
  have ht := h.selected_top_direction_bound_signed hw t p' hp' q' hq' hrow' hnear'
  have hpos : 0≤1+cb/4 := by linarith
  have hs := angular_scale_ratio w (P.length q.1) (P.length q'.1) CZero hw.le
    (P.length_pos q.1) (P.length_pos q'.1) hCZero hfar
  have htnear : |p'.1.slope-t| ≤ cb*(w/P.length q.1)/4 := by
    calc
      _ ≤ (1+cb/4)*((1/CZero)*(w/P.length q.1)) :=
        ht.trans (mul_le_mul_of_nonneg_left hs hpos)
      _ = ((1+cb/4)/CZero)*(w/P.length q.1) := by ring
      _ ≤ (cb/4)*(w/P.length q.1) :=
        mul_le_mul_of_nonneg_right hconstants (div_nonneg hw.le (P.length_pos q.1).le)
      _ = _ := by ring
  have htscaled : |p'.1.slope-t| * P.length q'.1≤(1+cb/4)*P.width := by
    calc
      _ ≤ ((1+cb/4)*(w/P.length q'.1))*P.length q'.1 :=
        mul_le_mul_of_nonneg_right ht (P.length_pos q'.1).le
      _ = (1+cb/4)*w := by field_simp [(P.length_pos q'.1).ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hwW hpos
  have htcell : p'.1.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1) := by
    apply hmargin
    have hd : |p'.1.slope-P.rowSlope q.1 q.2.1| ≤ cb*(w/P.length q.1)/2 := by
      calc
        _ ≤ |p'.1.slope-t|+|t-P.rowSlope q.1 q.2.1| := abs_sub_le _ _ _
        _ ≤ cb*(w/P.length q.1)/4+cb*(w/P.length q.1)/4 :=
          add_le_add htnear (by simpa only [abs_sub_comm] using hnear)
        _ = _ := by ring
    obtain ⟨hl,hr⟩ := abs_le.mp hd
    constructor <;> linarith
  exact h.selected_boxes_disjoint_signed hw hcb t K (1+cb/4) hK hpos hA p p' hp hp' q q' hq hq'
    hlen hnear htnear htscaled hepsilon htcell


end LipschitzHilbert.PacketLatticeData.SizeStoppingRun

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_PacketDataSignedPacketPacking
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded overlap for actual selected packets with slopes close to a
fixed longer tree. Both temporal order and spatial lattice counts have
been proved; no overlap premise is assumed. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketLatticeData.SizeStoppingRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable {P : PacketLatticeData N κ Label Item} {negative : Bool}
  {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem selected_packet_box_packing_signed
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hw : 0<w) (hwW : w≤P.width) (hcb : 0 < cb)
    (t K CZero : ℝ) (hK : 0≤K) (hCZero : 0<CZero)
    (hconstants : (1+cb/4)/CZero ≤ cb/4)
    (hA : 2*K*(1+(1+cb/4))+1/2≤A)
    (gap M Q : ℕ) (hgap : CZero≤(2:ℝ)^gap) (hQ : cb/4≤Q)
    (S : Finset P.PacketIndex)
    (hselected : ∀ q∈S, ∃ p∈P.sizeSelectionRecords negative w cb A cell grid initial tops, q∈p.2)
    (hmultiplicity : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (P.rowSlope j) (w/P.length j) M)
    (hnear : ∀ q∈S, |P.rowSlope q.1 q.2.1-t| ≤ cb*(w/P.length q.1)/4)
    (hrow : ∀ q∈S, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (hepsilon : ∀ q∈S, epsilon ≤ cb*(w/P.length q.1)/4)
    (hmargin : ∀ q∈S, Icc (P.rowSlope q.1 q.2.1-cb*(w/P.length q.1)/2)
      (P.rowSlope q.1 q.2.1+cb*(w/P.length q.1)/2)⊆
        scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (z : ℝ×ℝ) :
    ((S.filter fun q => z∈densitySpatialBox (P.directionBox t q) K).card:ℝ)≤
      gap*((((2*Q+1)*M:ℕ):ℝ)*(((1+K^2)*(1+(K*(1+cb/4))^2))*(4*Real.pi)^2)) := by
  apply scale_window_packing S (fun q => q.1.val)
    (fun q => densitySpatialBox (P.directionBox t q) K) gap _ ?_ ?_ z
  · intro i hi j hj hij
    obtain ⟨p,hp,hpi⟩ := hselected i hi
    obtain ⟨p',hp',hpj⟩ := hselected j hj
    have hlen : P.length j.1≤P.length i.1 := P.length_antitone (by omega)
    have hfar : CZero*P.length j.1≤P.length i.1 :=
      (mul_le_mul_of_nonneg_right hgap (P.length_pos j.1).le).trans (P.length_scale_gap i.1 j.1 gap hij)
    exact (h.selected_boxes_disjoint_of_margin_signed hw hwW hcb t K CZero hK hCZero hconstants hA
      p' p hp' hp j i hpj hpi hlen hfar (hnear j hj) (hnear i hi) (hrow i hi)
      (hepsilon j hj) (hmargin j hj)).symm
  · intro v k
    apply P.direction_packets_count S t w K (cb/4) hw hwW hK (by linarith) M Q hQ hmultiplicity
    intro q hq
    convert hnear q hq using 1 <;> first | rfl | ring

end LipschitzHilbert.PacketLatticeData.SizeStoppingRun

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataInteractionGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short family used in the selected-tree argument is defined by
actual nonzero Gram interactions. Its angular geometry follows from the
packet spectra, rather than being a separate analytic premise. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem interactingShortPackets_subset (S T : Finset P.PacketIndex) (gap : ℕ) :
    P.interactingShortPackets S T gap⊆S := Finset.filter_subset _ _

theorem interacting_short_length (S T : Finset P.PacketIndex) (gap : ℕ) (L : ℝ)
    (hT : ∀ q∈T, P.length q.1≤L) (s : P.PacketIndex)
    (hs : s∈P.interactingShortPackets S T gap) : P.length s.1≤L := by
  obtain ⟨_,q,hq,hgap,_⟩ := Finset.mem_filter.mp hs
  exact (P.length_antitone (show q.1 ≤ s.1 by change q.1.val ≤ s.1.val; omega)).trans (hT q hq)

theorem interacting_short_direction (S T : Finset P.PacketIndex) (gap : ℕ)
    (t w cStar cEta CEta cb : ℝ) (hw : 0<w) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hconstants : (cStar/cEta)*(1+1/(2:ℝ)^gap)+1/(2:ℝ)^gap ≤ cb/4)
    (hT : ∀ q∈T, |P.rowSlope q.1 q.2.1-t|≤w/P.length q.1)
    (hspectrum : ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
      |xi+P.rowSlope j l*eta| ≤ cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta)
    (s : P.PacketIndex) (hs : s∈P.interactingShortPackets S T gap) :
    |P.rowSlope s.1 s.2.1-t| ≤ cb*(w/P.length s.1)/4 := by
  obtain ⟨_,q,hq,hgap,k,hinner⟩ := Finset.mem_filter.mp hs
  have h := gram_short_direction
    (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (P.physicalPacket 0 q.1 q.2.1 q.2.2 k)
    (P.rowSlope s.1 s.2.1) (P.rowSlope q.1 q.2.1) t (P.length s.1) (P.length q.1)
    w cStar cEta CEta cb 1 ((2:ℝ)^gap) (P.length_pos s.1) (P.length_pos q.1)
    hw hcStar hcEta (by norm_num) (by positivity) (P.length_scale_gap q.1 s.1 gap hgap)
    (by simpa only [one_div] using hconstants) (by simpa only [one_mul] using hT q hq)
    (hspectrum s.1 s.2.1 s.2.2 k) (hspectrum q.1 q.2.1 q.2.2 k) hinner
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem interacting_short_margin (S T : Finset P.PacketIndex) (gap : ℕ)
    (w cStar cEta margin cb : ℝ) (hw : 0<w) (hcEta : 0 < cEta)
    (hconstants : cb/2 ≤ margin-cStar/cEta)
    (cell : P.PacketIndex → Set ℝ)
    (hspectrum : ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
      |xi+P.rowSlope j l*eta| ≤ cStar/P.length j ∧ cEta≤w*eta)
    (hmargin : ∀ s∈S, ∀ k xi eta,
      planarAngularFourier (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (xi,eta)≠0 →
        Icc (-xi/eta-margin*(w/P.length s.1)) (-xi/eta+margin*(w/P.length s.1))⊆cell s)
    (s : P.PacketIndex) (hs : s∈P.interactingShortPackets S T gap) :
    Icc (P.rowSlope s.1 s.2.1-cb*(w/P.length s.1)/2)
      (P.rowSlope s.1 s.2.1+cb*(w/P.length s.1)/2)⊆cell s := by
  obtain ⟨hsS,q,_,_,k,hinner⟩ := Finset.mem_filter.mp hs
  intro u hu
  have huabs : |u-P.rowSlope s.1 s.2.1|≤(cb/2)*(w/P.length s.1) := by
    apply abs_le.mpr
    constructor <;> linarith [hu.1,hu.2]
  exact gram_margin_direction_mem
    (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (P.physicalPacket 0 q.1 q.2.1 q.2.2 k)
    (P.rowSlope s.1 s.2.1) (P.length s.1) w cStar cEta margin u (cell s)
    (P.length_pos s.1) hw hcEta (hspectrum s.1 s.2.1 s.2.2 k)
    (hmargin s hsS k) (huabs.trans (mul_le_mul_of_nonneg_right hconstants
      (div_nonneg hw.le (P.length_pos s.1).le))) hinner

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedPackets
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The union of the actual recorded separated tests. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem mem_selectedPackets (negative : Bool) (w cb A : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (initial : Finset P.PacketIndex) (tops : List SlopeBox) (q : P.PacketIndex) :
    q∈P.selectedPackets negative w cb A cell grid initial tops ↔
      ∃ p∈P.sizeSelectionRecords negative w cb A cell grid initial tops, q∈p.2 := by
  simp only [selectedPackets,Finset.mem_biUnion,List.mem_toFinset]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_PacketDataSignedInteractionPacking
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Gram-interacting short packets from one selected top obey
the packing estimate needed by the far-tree bound. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketLatticeData.SizeStoppingRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable {P : PacketLatticeData N κ Label Item} {negative : Bool}
  {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem selected_interacting_box_packing_signed
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hw : 0<w) (hwW : w≤P.width) (hcb : 0 < cb)
    (cStar cEta CEta margin : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (farGap packGap M Q : ℕ)
    (hfar : (cStar/cEta)*(1+1/(2:ℝ)^farGap)+1/(2:ℝ)^farGap ≤ cb/4)
    (hpack : (1+cb/4)/(2:ℝ)^packGap ≤ cb/4)
    (hmarginSize : cb/2 ≤ margin-cStar/cEta)
    (hA : 2*(1+(1+cb/4))+1/2≤A) (hQ : cb/4≤Q)
    (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M)
    (hrow : ∀ q∈P.selectedPackets negative w cb A cell grid initial tops,
      P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (hepsilon : ∀ q∈P.selectedPackets negative w cb A cell grid initial tops,
      epsilon ≤ cb*(w/P.length q.1)/4)
    (hspectrum : ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
      |xi+P.rowSlope j l*eta| ≤ cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta)
    (hmargin : ∀ s∈P.selectedPackets negative w cb A cell grid initial tops, ∀ k xi eta,
      planarAngularFourier (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (xi,eta)≠0 →
      Icc (-xi/eta-margin*(w/P.length s.1)) (-xi/eta+margin*(w/P.length s.1))⊆
        scaledAngularCell (w/P.topLength) grid s.1.val (cell s.1 s.2.1))
    (p : SlopeBox × Finset P.PacketIndex)
    (hp : p∈P.sizeSelectionRecords negative w cb A cell grid initial tops) :
    let S := P.interactingShortPackets (P.selectedPackets negative w cb A cell grid initial tops) p.2 farGap
    ∀ z : ℝ×ℝ, ((S.filter fun q => |z.1-P.actualX q.1 q.2.1 q.2.2|≤P.length q.1 ∧
      |(z.2-P.actualZ q.1 q.2.1 q.2.2)-p.1.slope*(z.1-P.actualX q.1 q.2.1 q.2.2)|≤P.width).card:ℝ)≤
        selectedEnvelopePackingConstant cb packGap M Q := by
  let all := P.selectedPackets negative w cb A cell grid initial tops
  let S := P.interactingShortPackets all p.2 farGap
  have hsub : S⊆all := P.interactingShortPackets_subset all p.2 farGap
  have hT (q : P.PacketIndex) (hq : q∈p.2) : |P.rowSlope q.1 q.2.1-p.1.slope|≤w/P.length q.1 := by
    have hs : q∈all := (P.mem_selectedPackets negative w cb A cell grid initial tops q).mpr ⟨p,hp,hq⟩
    exact P.angular_cell_distance w hw grid q.1 (cell q.1 q.2.1) _ _ (hrow q hs)
      ((h.records_geometry p hp).2.2 q hq).2.2.1
  have hnear := P.interacting_short_direction all p.2 farGap p.1.slope w cStar cEta CEta cb
    hw hcStar hcEta hfar hT hspectrum
  have hmargin' := P.interacting_short_margin all p.2 farGap w cStar cEta margin cb hw hcEta hmarginSize
    (fun q => scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (fun j l u k xi eta hh => ⟨(hspectrum j l u k xi eta hh).1,(hspectrum j l u k xi eta hh).2.1⟩)
    hmargin
  have hpacking := h.selected_packet_box_packing_signed hw hwW hcb p.1.slope 1 ((2:ℝ)^packGap)
    (by norm_num) (by positivity) hpack (by simpa only [one_mul,mul_one] using hA)
    packGap M Q le_rfl hQ S
    (fun q hq => (P.mem_selectedPackets negative w cb A cell grid initial tops q).mp (hsub hq))
    hlocal hnear (fun q hq => hrow q (hsub hq)) (fun q hq => hepsilon q (hsub hq)) hmargin'
  dsimp only
  intro z
  simpa only [densitySpatialBox,directionBox,mem_ofPred_eq,one_mul,selectedEnvelopePackingConstant] using hpacking z

end LipschitzHilbert.PacketLatticeData.SizeStoppingRun

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedPrefix
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distant longer packets in a fixed selected tree form an actual
initial scale segment, so their norm is bounded by its interval maximum. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem onPackets_energy_sum (S : Finset P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    (∑ j, ∑ l : P.labels j, ∑ u, ‖P.onPackets S c j l u‖^2*P.length j*P.width)=
      ∑ q∈S, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width := by
  have he (q : P.PacketIndex) :
      ‖P.onPackets S c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width=
        if q∈S then ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0 := by
    by_cases hq : q∈S <;> simp [onPackets,hq]
  calc
    _ = ∑ q : P.PacketIndex, ‖P.onPackets S c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width := by
      simp only [Fintype.sum_sigma]
    _ = ∑ q : P.PacketIndex, if q∈S then ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0 := by
      simp only [he]
    _ = _ := by
      rw [←Finset.sum_filter]
      congr 1
      ext q
      simp

theorem packetVector_onPackets (S : Finset P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (q : P.PacketIndex) (z : ℝ×ℝ) :
    P.packetVector (P.onPackets S c) q z=if q∈S then P.packetVector c q z else 0 := by
  by_cases hq : q∈S
  · simp only [packetVector,onPackets,hq,ite_true, if_true]
  · simp only [packetVector,onPackets,hq,ite_false, if_false,WithLp.ofLp_zero,Pi.zero_apply,zero_mul]
    rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedReference
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A selected tree from an unrestricted packet lattice has a genuine
bounded reference lattice. Only the selected packets are present, and
their original physical waves are preserved. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item) (S : Finset P.PacketIndex)

variable (t Cb w F : ℝ) (hw : 0<w) (hCb : 0≤Cb) (hF : 0≤F)
  (hwide : Cb*w≤P.width) (hfrequency : ∀ k, |P.frequency k|≤F/w)
  (hnear : ∀ q∈S, |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1)

local notation "Q" => P.selectedReference S t Cb w F hw hCb hF hwide hfrequency hnear

theorem selectedReference_actualZ (j : Fin N) (l : (Q).labels j)
    (u : P.SelectedItem S j l) :
    (Q).actualZ j l u=P.actualZ j (P.selectedOriginalLabel S j l) u.val-
      t*P.actualX j (P.selectedOriginalLabel S j l) u.val := by
  dsimp [SourceLabeledLattice.actualZ,SourceLabeledLattice.actualX,actualX,actualZ,
    selectedReference,SourceLabeledLattice.length,length]
  ring

theorem selectedReference_physicalPacket (j : Fin N) (l : (Q).labels j)
    (u : P.SelectedItem S j l) (k : κ) :
    (Q).physicalPacket t j l u k=P.physicalPacket 0 j (P.selectedOriginalLabel S j l) u.val k := by
  have hx := P.selectedReference_actualX S t Cb w F hw hCb hF hwide hfrequency hnear j l u
  have hz := P.selectedReference_actualZ S t Cb w F hw hCb hF hwide hfrequency hnear j l u
  unfold SourceLabeledLattice.physicalPacket physicalPacket
  rw [hx,hz]
  change physicalPlanarPacket (P.profile j (P.selectedOriginalLabel S j l) u.val k)
    (P.actualX j (P.selectedOriginalLabel S j l) u.val)
    (P.actualZ j (P.selectedOriginalLabel S j l) u.val-
      t*P.actualX j (P.selectedOriginalLabel S j l) u.val+
      t*P.actualX j (P.selectedOriginalLabel S j l) u.val)
    (P.length j) P.width (t+(P.rowSlope j (P.selectedOriginalLabel S j l)-t))
    (P.frequency k) (P.length_pos j).ne' P.width_pos.ne' = _
  have hs : t+(P.rowSlope j (P.selectedOriginalLabel S j l)-t)=
      P.rowSlope j (P.selectedOriginalLabel S j l) := by ring
  rw [sub_add_cancel,hs]
  simp only [zero_mul,add_zero,zero_add]


theorem selectedReference_sum {E : Type*} [AddCommMonoid E] (f : P.PacketIndex → E) :
    (∑ r : (Q).PacketIndex,
      f (P.selectedReferenceEquiv S t Cb w F hw hCb hF hwide hfrequency hnear r).val) =
        ∑ q∈S, f q := by
  have h := Equiv.sum_comp
    (P.selectedReferenceEquiv S t Cb w F hw hCb hF hwide hfrequency hnear)
    (fun q : S => f q.val)
  exact h.trans (Finset.sum_subtype S (p := fun q => q∈S) (by simp) f).symm

theorem selectedReference_card (M R : ℕ) (hR : Cb≤R)
    (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (P.rowSlope j) (w/P.length j) M) (j : Fin N) :
    ((Q).labels j).card≤(2*R+1)*M := by
  let W := SourceSlopeLabels.window Finset.univ (P.rowSlope j) t (w/P.length j) Cb
  let embed : P.selectedLabels S j ↪ W :=
    { toFun := fun l => ⟨P.selectedOriginalLabel S j l,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,by
          simpa only [mul_div_assoc] using P.selectedLabel_near S t Cb w hnear j l⟩⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : W => z.val.val) hab }
  have hcount : (P.selectedLabels S j).card≤W.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective embed embed.injective
  exact hcount.trans (SourceSlopeLabels.window_card_le Finset.univ (P.rowSlope j)
    (div_pos hw (P.length_pos j)) (hlocal j) hR)

end LipschitzHilbert.PacketLatticeData

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

theorem transverseTailConstant_nonneg : 0≤transverseTailConstant :=
  tsum_nonneg (fun _ => by positivity)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceHighDensityForest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High ordinary density supplies concrete tests and then a finite
popular forest. Every tile receives a keeper whose direction belongs to
the tile's original dyadic interval. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

theorem densitySpatialBox_mono (T : SlopeBox) {K K' : ℝ} (h : K ≤ K') :
    densitySpatialBox T K ⊆ densitySpatialBox T K' := by
  intro z hz
  exact ⟨hz.1.trans (mul_le_mul_of_nonneg_right h T.length_pos.le),
    hz.2.trans (mul_le_mul_of_nonneg_right h T.width_pos.le)⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected reference family retains the original density tests
and spectra. No bound on the unselected slopes is involved. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item) (S : Finset P.PacketIndex)
  (t Cb w F : ℝ) (hw : 0<w) (hCb : 0≤Cb) (hF : 0≤F)
  (hwide : Cb*w≤P.width) (hfrequency : ∀ k, |P.frequency k|≤F/w)
  (hnear : ∀ q∈S, |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1)
local notation "Q" => P.selectedReference S t Cb w F hw hCb hF hwide hfrequency hnear

theorem selectedReference_densityTile (cell : ∀ j, P.labels j → ℤ)
    (j : Fin N) (l : (Q).labels j) (u : P.SelectedItem S j l) :
    (Q).densityTile t (P.selectedCells S t Cb w F hw hCb hF hwide hfrequency hnear cell) ⟨j,l,u⟩ =
      P.densityTile 0 cell ⟨j,P.selectedOriginalLabel S j l,u.val⟩ := by
  have hx := P.selectedReference_actualX S t Cb w F hw hCb hF hwide hfrequency hnear j l u
  have hz := P.selectedReference_actualZ S t Cb w F hw hCb hF hwide hfrequency hnear j l u
  unfold SourceLabeledLattice.densityTile densityTile
  rw [hx,hz]
  congr 1
  apply Prod.ext
  · rfl
  · dsimp only
    ring

theorem selectedReference_density (cell : ∀ j, P.labels j → ℤ)
    (grid : ℤ) (tau : ℝ) (E : Set (ℝ×ℝ)) (v : ℝ×ℝ → ℝ)
    (j : Fin N) (l : (Q).labels j) (u : P.SelectedItem S j l) :
    (Q).ordinaryDensity t (P.selectedCells S t Cb w F hw hCb hF hwide hfrequency hnear cell)
        grid w tau E v ⟨j,l,u⟩ =
      P.ordinaryDensity 0 cell grid w tau E v ⟨j,P.selectedOriginalLabel S j l,u.val⟩ := by
  unfold SourceLabeledLattice.ordinaryDensity ordinaryDensity
  rw [P.selectedReference_densityTile S t Cb w F hw hCb hF hwide hfrequency hnear cell j l u]
  rfl

theorem selectedReference_slope (j : Fin N) (l : (Q).labels j) :
    t+(Q).rowSlope j l=P.rowSlope j (P.selectedOriginalLabel S j l) := by
  change t+(P.rowSlope j (P.selectedOriginalLabel S j l)-t)=_
  ring

theorem selectedReference_spectrum_at (cStar cEta CEta : ℝ)
    (j : Fin N) (l : (Q).labels j) (u : P.SelectedItem S j l) (k : κ) (xi eta : ℝ)
    (hspectrum : planarAngularFourier
      (P.physicalPacket 0 j (P.selectedOriginalLabel S j l) u.val k) (xi,eta)≠0 →
        |xi+P.rowSlope j (P.selectedOriginalLabel S j l)*eta| ≤ cStar/P.length j ∧
          cEta≤w*eta ∧ w*eta≤CEta)
    (h : planarAngularFourier ((Q).physicalPacket t j l u k) (xi,eta)≠0) :
    |xi+(t+(Q).rowSlope j l)*eta| ≤ cStar/(Q).length j ∧ cEta≤w*eta ∧ w*eta≤CEta := by
  have hpacket := P.selectedReference_physicalPacket S t Cb w F hw hCb hF hwide hfrequency hnear j l u k
  have hf := congrArg (fun f : SchwartzMap (ℝ×ℝ) ℂ => planarAngularFourier f (xi,eta)) hpacket
  rw [hf] at h
  rw [P.selectedReference_slope S t Cb w F hw hCb hF hwide hfrequency hnear j l]
  exact hspectrum h

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedSum
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
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

variable (S : Finset P.PacketIndex) (t Cb w F : ℝ) (hw : 0<w) (hCb : 0≤Cb) (hF : 0≤F)
  (hwide : Cb*w≤P.width) (hfrequency : ∀ k, |P.frequency k|≤F/w)
  (hnear : ∀ q∈S, |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1)
local notation "Q" => P.selectedReference S t Cb w F hw hCb hF hwide hfrequency hnear

theorem selectedReference_synthesis
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (beta : ∀ j, P.labels j → κ → ℂ) (z : ℝ×ℝ) :
    (Q).physicalTreeSelectorValue t
      (P.selectedCoefficients S t Cb w F hw hCb hF hwide hfrequency hnear c)
      (P.selectedMultipliers S t Cb w F hw hCb hF hwide hfrequency hnear beta) z =
    ∑ q∈S, WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*beta q.1 q.2.1 k*
      P.physicalPacket 0 q.1 q.2.1 q.2.2 k z) := by
  let value := fun q : P.PacketIndex => WithLp.toLp 2
    (fun k => c q.1 q.2.1 q.2.2 k*beta q.1 q.2.1 k*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
  have hval (r : (Q).PacketIndex) :
      WithLp.toLp 2 (fun k =>
        P.selectedCoefficients S t Cb w F hw hCb hF hwide hfrequency hnear c r.1 r.2.1 r.2.2 k*
        P.selectedMultipliers S t Cb w F hw hCb hF hwide hfrequency hnear beta r.1 r.2.1 k*
        (Q).physicalPacket t r.1 r.2.1 r.2.2 k z) =
      value (P.selectedReferenceEquiv S t Cb w F hw hCb hF hwide hfrequency hnear r).val := by
    rcases r with ⟨j,l,u⟩
    apply WithLp.ofLp_injective
    funext k
    simp only [selectedCoefficients,selectedMultipliers,value,selectedReferenceEquiv]
    rw [P.selectedReference_physicalPacket S t Cb w F hw hCb hF hwide hfrequency hnear j l u k]
    rfl
  calc
    _ = ∑ r : (Q).PacketIndex, WithLp.toLp 2 (fun k =>
        P.selectedCoefficients S t Cb w F hw hCb hF hwide hfrequency hnear c r.1 r.2.1 r.2.2 k*
        P.selectedMultipliers S t Cb w F hw hCb hF hwide hfrequency hnear beta r.1 r.2.1 k*
        (Q).physicalPacket t r.1 r.2.1 r.2.2 k z) := by
      simp only [SourceLabeledLattice.physicalTreeSelectorValue,Fintype.sum_sigma]
    _ = ∑ r : (Q).PacketIndex,
        value (P.selectedReferenceEquiv S t Cb w F hw hCb hF hwide hfrequency hnear r).val :=
      Finset.sum_congr rfl (fun r _ => hval r)
    _ = _ := P.selectedReference_sum S t Cb w F hw hCb hF hwide hfrequency hnear value

theorem selectedReference_separated_energy
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (cb : ℝ) :
    (Q).angularSeparatedTreeEnergy cb w
      (P.selectedCoefficients S t Cb w F hw hCb hF hwide hfrequency hnear c) =
    ∑ q∈S, if cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t| then
      ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0 := by
  have h := P.selectedReference_sum S t Cb w F hw hCb hF hwide hfrequency hnear
    (fun q => if cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t| then
      ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0)
  simp only [Fintype.sum_sigma] at h
  exact h

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSignedTopGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometry of each actual recorded test, in its own top coordinates. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketLatticeData.SizeStoppingRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable {P : PacketLatticeData N κ Label Item} {negative : Bool}
  {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem recorded_packet_geometry_signed
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hw : 0<w)
    (hrow : ∀ q∈P.selectedPackets negative w cb A cell grid initial tops,
      P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (p : SlopeBox × Finset P.PacketIndex)
    (hp : p∈P.sizeSelectionRecords negative w cb A cell grid initial tops)
    (q : P.PacketIndex) (hq : q∈p.2) :
    P.length q.1≤p.1.length ∧
      |P.actualX q.1 q.2.1 q.2.2-p.1.x|≤p.1.length ∧
      |(P.actualZ q.1 q.2.1 q.2.2-p.1.y)-p.1.slope*(P.actualX q.1 q.2.1 q.2.2-p.1.x)|≤P.width ∧
      cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-p.1.slope| ∧
      |P.rowSlope q.1 q.2.1-p.1.slope|≤w/P.length q.1 := by
  have hg := (h.records_geometry p hp).2.2 q hq
  have hwidth := (h.records_geometry p hp).1
  have hs : q∈P.selectedPackets negative w cb A cell grid initial tops :=
    (P.mem_selectedPackets negative w cb A cell grid initial tops q).mpr ⟨p,hp,hq⟩
  have hbox := hg.2.1
  change |P.actualX q.1 q.2.1 q.2.2-p.1.x|≤(1/2)*p.1.length ∧
    |(P.actualZ q.1 q.2.1 q.2.2-p.1.y)-p.1.slope*(P.actualX q.1 q.2.1 q.2.2-p.1.x)|≤
      (1/2)*p.1.width at hbox
  rw [hwidth] at hbox
  have hlower := hg.2.2.2
  have habs : sizeDirection negative (p.1.slope-P.rowSlope q.1 q.2.1)≤
      |p.1.slope-P.rowSlope q.1 q.2.1| := by
    cases negative
    · exact le_abs_self _
    · exact neg_le_abs _
  refine ⟨hg.1,?_,?_,?_,?_⟩
  · exact hbox.1.trans (by linarith [p.1.length_pos])
  · exact hbox.2.trans (by linarith [P.width_pos])
  · rw [abs_sub_comm]
    exact hlower.trans habs
  · exact P.angular_cell_distance w hw grid q.1 (cell q.1 q.2.1) _ _ (hrow q hs) hg.2.2.1

end LipschitzHilbert.PacketLatticeData.SizeStoppingRun

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataPacketGram
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinatewise Gram identities relate the Hilbert-valued coefficient
packets to the original scalar Fourier geometry. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem packetVector_inner_integrable
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (s q : P.PacketIndex) :
    Integrable (fun z => inner ℂ (P.packetVector c s z) (P.packetVector c q z))
      (volume.prod volume) := by
  have hf := P.packetVector_memLp c s
  have hg := P.packetVector_memLp c q
  exact (hf.norm.integrable_mul hg.norm).mono'
    (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => norm_inner_le_norm (𝕜 := ℂ) _ _)

theorem packetVector_gram_eq
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (s q : P.PacketIndex) :
    (∫ z, inner ℂ (P.packetVector c s z) (P.packetVector c q z) ∂volume.prod volume)=
      ∑ k, (star (c s.1 s.2.1 s.2.2 k)*c q.1 q.2.1 q.2.2 k)*
        ∫ z, inner ℂ (P.physicalPacket 0 s.1 s.2.1 s.2.2 k z)
          (P.physicalPacket 0 q.1 q.2.1 q.2.2 k z) ∂volume.prod volume := by
  have he (z : ℝ×ℝ) : inner ℂ (P.packetVector c s z) (P.packetVector c q z)=
      ∑ k, (star (c s.1 s.2.1 s.2.2 k)*c q.1 q.2.1 q.2.2 k)*
        inner ℂ (P.physicalPacket 0 s.1 s.2.1 s.2.2 k z)
          (P.physicalPacket 0 q.1 q.2.1 q.2.2 k z) := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro k _
    change inner ℂ (c s.1 s.2.1 s.2.2 k • P.physicalPacket 0 s.1 s.2.1 s.2.2 k z)
      (c q.1 q.2.1 q.2.2 k • P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)=_
    rw [inner_smul_left,inner_smul_right]
    simp only [starRingEnd_apply]
    ring
  have hi (k : κ) : Integrable (fun z => inner ℂ
      (P.physicalPacket 0 s.1 s.2.1 s.2.2 k z)
      (P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)) (volume.prod volume) := by
    have hf := (P.physicalPacket 0 s.1 s.2.1 s.2.2 k).memLp 2 (volume.prod volume)
    have hg := (P.physicalPacket 0 q.1 q.2.1 q.2.2 k).memLp 2 (volume.prod volume)
    exact (hf.norm.integrable_mul hg.norm).mono'
      (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => norm_inner_le_norm (𝕜 := ℂ) _ _)
  simp_rw [he]
  rw [integral_finsetSum _ (fun k _ => (hi k).const_mul _)]
  simp only [integral_const_mul]

theorem packetVector_gram_eq_zero
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (s q : P.PacketIndex)
    (hzero : ∀ k, (∫ z, inner ℂ (P.physicalPacket 0 s.1 s.2.1 s.2.2 k z)
      (P.physicalPacket 0 q.1 q.2.1 q.2.2 k z) ∂volume.prod volume)=0) :
    (∫ z, inner ℂ (P.packetVector c s z) (P.packetVector c q z) ∂volume.prod volume)=0 := by
  rw [P.packetVector_gram_eq]
  simp only [hzero,mul_zero,Finset.sum_const_zero]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataTrimInteractions
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing noninteracting short packets is an exact equality for the
actual vector-valued far Gram sum. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
attribute [local instance] Classical.propDecidable

theorem far_pairing_restrict_to_interacting
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (S T : Finset P.PacketIndex) (gap : ℕ) :
    (∑ s∈S, ∫ z, inner ℂ (P.packetVector c s z) (P.longPacketSum c T gap s.1 z)
      ∂volume.prod volume)=
    ∑ s∈P.interactingShortPackets S T gap, ∫ z,
      inner ℂ (P.packetVector c s z) (P.longPacketSum c T gap s.1 z) ∂volume.prod volume := by
  symm
  apply Finset.sum_subset (P.interactingShortPackets_subset S T gap)
  intro s hs hout
  have hz (q : P.PacketIndex) (hq : q∈T.filter (fun q => q.1.val+gap ≤ s.1.val)) :
      (∫ z, inner ℂ (P.packetVector c s z) (P.packetVector c q z) ∂volume.prod volume)=0 := by
    obtain ⟨hqT,hgap⟩ := Finset.mem_filter.mp hq
    apply P.packetVector_gram_eq_zero c s q
    intro k
    by_contra hnonzero
    exact hout (Finset.mem_filter.mpr ⟨hs,q,hqT,hgap,k,hnonzero⟩)
  simp only [longPacketSum,inner_sum]
  rw [integral_finsetSum _ (fun q _ => P.packetVector_inner_integrable c s q)]
  exact Finset.sum_eq_zero (fun q hq => hz q hq)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSelectedTopGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometry of each actual recorded test, in its own top coordinates. -/
noncomputable section
open Set

namespace LipschitzHilbert

theorem short_direction_shear_bound (theta t cb w ell W : ℝ)
    (hell : 0<ell) (hW : 0<W) (hw : 0≤w) (hwW : w≤W) (hcb : cb≤4)
    (hnear : |theta-t| ≤ cb*(w/ell)/4) : |(theta-t)*ell/W|≤1 := by
  rw [abs_div,abs_mul,abs_of_pos hell,abs_of_pos hW]
  apply (div_le_one hW).mpr
  have hscaled := mul_le_mul_of_nonneg_right hnear hell.le
  have he : (cb*(w/ell)/4)*ell=cb*w/4 := by field_simp
  rw [he] at hscaled
  have hc := mul_le_mul_of_nonneg_right hcb hw
  have hb : cb*w/4≤W := by linarith
  exact hscaled.trans hb

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_PacketDataSignedSelectedFarBound
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The far contribution belonging to one actual recorded signed
selection top. The required short-packet packing follows from a combination
of selection order and the original Fourier margins. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_signed_selected_far_gram_bound (hL : LepingleInput)
    (cStar cEta CEta cb : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hcb : 0 < cb) (hcb4 : cb≤4) (hspectral : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (negative : Bool) (M Q farGap packGap : ℕ),
      ∀ (w tau sigma beta epsilon A margin F : ℝ), 0<w → w≤P.width → 0≤F →
      (∀ k, |P.frequency k|≤F/w) →
      (cStar/cEta)*(1+1/(2:ℝ)^farGap)+1/(2:ℝ)^farGap ≤ cb/4 →
      (1+cb/4)/(2:ℝ)^packGap ≤ cb/4 → cb/2 ≤ margin-cStar/cEta →
      2*(1+(1+cb/4))+1/2≤A → cb/4≤Q →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
    ∀ (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (initial remaining : Finset P.PacketIndex) (tops : List SlopeBox),
      P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining →
      (∀ q∈P.selectedPackets negative w cb A cell grid initial tops, ‖c q.1 q.2.1 q.2.2‖≤beta) →
      (∀ q∈P.selectedPackets negative w cb A cell grid initial tops,
        P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈P.selectedPackets negative w cb A cell grid initial tops, epsilon ≤ cb*(w/P.length q.1)/4) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
        |xi+P.rowSlope j l*eta| ≤ cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta) →
      (∀ s∈P.selectedPackets negative w cb A cell grid initial tops, ∀ k xi eta,
        planarAngularFourier (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (xi,eta)≠0 →
        Icc (-xi/eta-margin*(w/P.length s.1)) (-xi/eta+margin*(w/P.length s.1))⊆
          scaledAngularCell (w/P.topLength) grid s.1.val (cell s.1 s.2.1)) →
    ∀ p∈P.sizeSelectionRecords negative w cb A cell grid initial tops,
      ‖∑ s∈P.selectedPackets negative w cb A cell grid initial tops,
        ∫ z, inner ℂ (P.packetVector c s z) (P.longPacketSum c p.2 farGap s.1 z)
          ∂volume.prod volume‖^2≤
        (4*P.profileBound*beta)^2*256*
          (82944*SizeStoppingRun.selectedEnvelopePackingConstant cb packGap M Q)^2*
          1296*Real.pi^2*p.1.length*P.width*
            (((3*M:ℕ):ℝ)*C*P.referenceEnvelopeConstant^2*
              ∑ q∈p.2, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width) := by
  obtain ⟨C,hC,hFar⟩ := exists_tree_far_gram_bound hL cStar cEta CEta cb 1
    hcStar hcEta hCEta hcb.le (by norm_num) hspectral
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P negative M Q farGap packGap w tau sigma beta epsilon A margin F
    hw hwW hF hfreq hfar hpack hmarginSize hA hQ hlocal cell grid c initial remaining tops
    hrun hcoeff hrow hepsilon hspectrum hmargin p hp
  let all := P.selectedPackets negative w cb A cell grid initial tops
  let I := P.interactingShortPackets all p.2 farGap
  have hsub : I⊆all := P.interactingShortPackets_subset all p.2 farGap
  have hgeom := hrun.recorded_packet_geometry_signed hw hrow p hp
  have hTnear (q : P.PacketIndex) (hq : q∈p.2) : |P.rowSlope q.1 q.2.1-p.1.slope|≤w/P.length q.1 :=
    (hgeom q hq).2.2.2.2
  have hnear := P.interacting_short_direction all p.2 farGap p.1.slope w cStar cEta CEta cb
    hw hcStar hcEta hfar hTnear hspectrum
  have hIlen := P.interacting_short_length all p.2 farGap p.1.length (fun q hq => (hgeom q hq).1)
  have hIpack := hrun.selected_interacting_box_packing_signed hw hwW hcb cStar cEta CEta margin
    hcStar hcEta farGap packGap M Q hfar hpack hmarginSize hA hQ hlocal hrow hepsilon hspectrum hmargin p hp
  rw [P.far_pairing_restrict_to_interacting]
  have hb := hFar N κ Label Item P M 1 (by norm_num) p.1.slope w p.1.x p.1.y p.1.length F beta
    (SizeStoppingRun.selectedEnvelopePackingConstant cb packGap M Q) hw p.1.length_pos hF
    (by simpa only [one_mul] using hwW) hfreq hlocal c I p.2 farGap
    (fun q hq => (hgeom q hq).1) (fun q hq => (hgeom q hq).2.1)
    (fun q hq => (hgeom q hq).2.2.1) hspectrum
    (fun q hq => by simpa only [one_mul] using (hgeom q hq).2.2.2)
    (fun s hs => hcoeff s (hsub hs))
    (fun s hs => short_direction_shear_bound _ _ cb w _ P.width (P.length_pos s.1) P.width_pos
      hw.le hwW hcb4 (hnear s hs)) hIlen hIpack
  simpa only [show (2*1+1:ℕ)=3 by decide] using hb

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSizeTest
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual unsigned size tests for unrestricted packet families. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem unsignedSizeTestEnergy_mono (w cb : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    {R S : Finset P.PacketIndex} (hRS : R⊆S) (T : SlopeBox) :
    P.unsignedSizeTestEnergy w cb cell grid c R T≤P.unsignedSizeTestEnergy w cb cell grid c S T := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hRS
  intro q _ _
  split_ifs
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) (P.length_pos q.1).le) P.width_pos.le
  · exact le_rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_PacketDataTwoSidedSelection
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive followed by negative selection leaves every separated
size test below its threshold. Both runs retain their original geometry. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
attribute [local instance] Classical.propDecidable Classical.decEq

private theorem signed_indicator_bound (common : Prop) (a d e : ℝ) (he : 0≤e) :
    (if common ∧ a≤|d| then e else 0)≤
      (if common ∧ a≤d then e else 0)+(if common ∧ a≤-d then e else 0) := by
  by_cases hc : common
  · simp only [hc,true_and]
    by_cases hd : 0≤d
    · rw [abs_of_nonneg hd]
      split_ifs <;> linarith
    · rw [abs_of_nonpos (le_of_not_ge hd)]
      split_ifs <;> linarith
  · simp only [hc,false_and,ite_false, if_false,add_zero,le_refl]

theorem unsignedSizeTestEnergy_le (w cb : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (R : Finset P.PacketIndex) (T : SlopeBox) :
    P.unsignedSizeTestEnergy w cb cell grid c R T≤
      P.sizeTestEnergy false w cb cell grid c R T+P.sizeTestEnergy true w cb cell grid c R T := by
  simp only [unsignedSizeTestEnergy,sizeTestEnergy,sizeTestPackets,Finset.sum_filter,
    sizeDirection,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q _
  simpa only [and_assoc] using signed_indicator_bound
    (P.length q.1≤T.length ∧
      (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T (1/2) ∧
      T.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (cb*w/P.length q.1) (T.slope-P.rowSlope q.1 q.2.1)
    (‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width)
    (mul_nonneg (mul_nonneg (sq_nonneg _) (P.length_pos q.1).le) P.width_pos.le)

theorem exists_two_sided_size_selection (w cb tau sigma epsilon A : ℝ)
    (hw : 0≤w) (hcb : 0 ≤ cb) (hepsilon : 0<epsilon) (hA : 1/2≤A)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (initial : Finset P.PacketIndex) :
    ∃ positive middle negative remaining,
      P.SizeStoppingRun false w cb tau sigma epsilon A cell grid c initial positive middle ∧
      P.SizeStoppingRun true w cb tau sigma epsilon A cell grid c middle negative remaining ∧
      remaining⊆initial ∧
      ∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c remaining T ≤ sigma^2*T.area := by
  obtain ⟨positive,middle,hpos⟩ := P.exists_size_stopping_run false w cb tau sigma epsilon A
    hw hcb hepsilon hA cell grid c initial
  obtain ⟨negative,remaining,hneg⟩ := P.exists_size_stopping_run true w cb tau sigma epsilon A
    hw hcb hepsilon hA cell grid c middle
  refine ⟨positive,middle,negative,remaining,hpos,hneg,
    hneg.remaining_subset.trans hpos.remaining_subset,?_⟩
  intro T hwidth hlen
  have hp : P.sizeTestEnergy false w cb cell grid c remaining T ≤ sigma^2*T.area/2 := by
    apply le_of_not_gt
    intro hbad
    exact hpos.terminal_good T (P.sizeTestFails_mono false w cb tau sigma cell grid c
      hneg.remaining_subset T ⟨hwidth,hlen,hbad⟩)
  have hn : P.sizeTestEnergy true w cb cell grid c remaining T ≤ sigma^2*T.area/2 := by
    apply le_of_not_gt
    intro hbad
    exact hneg.terminal_good T ⟨hwidth,hlen,hbad⟩
  exact (P.unsignedSizeTestEnergy_le w cb cell grid c remaining T).trans (by linarith)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SourceFarLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The stopping lower-energy bound makes a quadratic per-top far
estimate summable linearly in the selected energy. -/
noncomputable section
namespace LipschitzHilbert

theorem quadratic_far_bound_linear {x E sigma A K : ℝ}
    (hE : 0≤E) (hK : 0≤K)
    (hfar : x^2≤K*(sigma^2*A)*E) (hstop : sigma^2*A≤2*E) :
    x≤Real.sqrt (2*K)*E := by
  have hb := hfar.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstop hK) hE)
  have hr : 0≤Real.sqrt (2*K)*E := mul_nonneg (Real.sqrt_nonneg _) hE
  have hs : (Real.sqrt (2*K)*E)^2=2*K*E^2 := by
    rw [mul_pow,Real.sq_sqrt (mul_nonneg (by norm_num) hK)]
  nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative witness radius for the ordinary density selection. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert

theorem densityRadiusConstant_ge_one : 1 ≤ densityRadiusConstant := le_max_left _ _

theorem densityRadius_ge_one (eta : ℝ) : 1 ≤ densityRadius eta := by
  have h := densityRadiusConstant_ge_one
  have hm : (1:ℝ) ≤ max 1 (eta^(-(1/100:ℝ))) := le_max_left _ _
  dsimp only [densityRadius]
  nlinarith

theorem densityRadius_tail {eta : ℝ} (heta : 0<eta) :
    (densityRadius eta)^(3-(203:ℝ))*(∫ z, topProfile 3 z ∂volume.prod volume) ≤ eta/2 := by
  let C := ∫ z, topProfile 3 z ∂volume.prod volume
  let A := densityRadiusConstant
  let x := max 1 (eta^(-(1/100:ℝ)))
  have hC : 0≤C := integral_nonneg (topProfile_nonnegative 3)
  have hA : 1≤A := densityRadiusConstant_ge_one
  have hAp : 0<A := zero_lt_one.trans_le hA
  have hCA : 2*C≤A := le_max_right _ _
  have hx : 1≤x := le_max_left _ _
  have hxp : 0<x := zero_lt_one.trans_le hx
  have hhalf : A^(-(200:ℝ))*C≤1/2 := by
    calc
      _ ≤ A^(-(1:ℝ))*C := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hA (by norm_num)) hC
      _ = C/A := by rw [Real.rpow_neg_one]; ring
      _ ≤ 1/2 := (div_le_iff₀ hAp).mpr (by linarith)
  have hxsmall : x^(-(200:ℝ))≤eta := by
    by_cases he : eta≤1
    · have hbase : eta^(-(1/100:ℝ))≤x := le_max_right _ _
      have hp := Real.rpow_le_rpow_of_nonpos
        (Real.rpow_pos_of_pos heta (-(1/100:ℝ))) hbase (by norm_num : -(200:ℝ)≤0)
      have hid : (eta^(-(1/100:ℝ)))^(-(200:ℝ))=eta^2 := by
        rw [←Real.rpow_mul heta.le]
        norm_num
      rw [hid] at hp
      exact hp.trans (by nlinarith)
    · exact (Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)).trans (le_of_not_ge he)
  change (A*x)^(3-(203:ℝ))*C≤eta/2
  norm_num only [show (3-(203:ℝ))= -200 by norm_num]
  rw [Real.mul_rpow hAp.le hxp.le]
  calc
    A^(-(200:ℝ))*x^(-(200:ℝ))*C = (A^(-(200:ℝ))*C)*x^(-(200:ℝ)) := by ring
    _ ≤ (1/2)*x^(-(200:ℝ)) :=
      mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg hxp.le _)
    _ ≤ (1/2)*eta := mul_le_mul_of_nonneg_left hxsmall (by norm_num)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSharpDensityForest
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary density selection with the actual spatial radius retained.
The area budget costs eta⁻¹; the assigned centers lie in five times the
witness dilation, without the coarser concentration-scale enlargement. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

theorem exists_density_forest_at_radius {ι : Type*} (candidates : Finset ι)
    (T : ι → SlopeBox) (level cell : ι → ℤ) (q : ℤ) (ell0 w W K eta : ℝ)
    (hell0 : 0 < ell0) (hw : 0 < w) (hW : w ≤ W) (hK : 1 ≤ K) (heta : 0 < eta)
    (hlength : ∀ i ∈ candidates, (T i).length = ell0/DyadicLineGrid.scale (level i))
    (hwidth : ∀ i ∈ candidates, (T i).width = W)
    (hslope : ∀ i ∈ candidates,
      (T i).slope ∈ scaledAngularCell (w/ell0) q (level i) (cell i))
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (hE : MeasurableSet E)
    (hEfin : (volume.prod volume) E ≠ ∞) (hu : Measurable u)
    (htail : K^(3-(203:ℝ))*(∫ z, topProfile 3 z ∂volume.prod volume) ≤ eta/2)
    (hdensity : ∀ i ∈ candidates, eta*(T i).area ≤ ∫ z in E ∩
      u ⁻¹' scaledAngularCell (w/ell0) q (level i) (cell i),
      (T i).densityKernel 203 z ∂volume.prod volume) :
    let witness := fun i => densityTest E u (T i)
      (scaledAngularCell (w/ell0) q (level i) (cell i)) K
    ∃ keepers : Finset ι, keepers ⊆ candidates ∧
      (∀ i ∈ keepers, MeasurableSet (witness i)) ∧
      Set.PairwiseDisjoint (keepers : Set ι) witness ∧
      (∑ i ∈ keepers, (T i).area) ≤ 2*(volume.prod volume).real E/eta ∧
      (∀ i ∈ keepers, (eta/2)*(T i).area ≤ (volume.prod volume).real (witness i)) ∧
      (∀ i ∈ keepers, ∀ z ∈ witness i,
        z ∈ E ∧ z ∈ densitySpatialBox (T i) K ∧ |u z-(T i).slope| ≤ w/(T i).length) ∧
      (∀ i ∈ candidates, ∃ j ∈ keepers, (T i).length ≤ (T j).length ∧
        scaledAngularCell (w/ell0) q (level j) (cell j) ⊆
          scaledAngularCell (w/ell0) q (level i) (cell i) ∧
        densitySpatialBox (T i) K ⊆ densitySpatialBox (T j) (5*K)) := by
  intro witness
  have hmass (i : ι) (hi : i ∈ candidates) :
      (eta/2)*(T i).area ≤ (volume.prod volume).real (witness i) :=
    density_witness_mass (T i) hK (by norm_num) heta.le E u
      (scaledAngularCell (w/ell0) q (level i) (cell i)) hE hEfin hu
      (scaledAngularCell_measurable (w/ell0) q (level i) (cell i)) htail (hdensity i hi)
  have horder (i : ι) (hi : i ∈ candidates) (j : ι) (hj : j ∈ candidates)
      (hij : (T i).length ≤ (T j).length) : level j ≤ level i :=
    density_dyadic_length_order hell0 (by simpa only [hlength i hi,hlength j hj] using hij)
  have hang (i : ι) (hi : i ∈ candidates) :
      ((w/ell0)*DyadicLineGrid.scale (level i))*(T i).length ≤ 1*(T i).width := by
    rw [hlength i hi,hwidth i hi,one_mul]
    have heq : ((w/ell0)*DyadicLineGrid.scale (level i))*
        (ell0/DyadicLineGrid.scale (level i)) = w := by
      field_simp [hell0.ne',(DyadicLineGrid.scale_pos (level i)).ne']
    rwa [heq]
  obtain ⟨keepers,hsub,hmeas,hdisj,harea,hinside,hcover⟩ := exists_scaled_dyadic_density_forest
    candidates T level cell q (w/ell0) K 1 (eta/2) (div_pos hw hell0)
    (zero_le_one.trans hK) (by norm_num) (half_pos heta) E u hE hEfin hu horder
    (fun i hi j hj => (hwidth i hi).trans (hwidth j hj).symm) hslope hang hmass
  refine ⟨keepers,hsub,hmeas,hdisj,?_,fun i hi => hmass i (hsub hi),?_,?_⟩
  · exact harea.trans_eq (by ring)
  · intro i hi z hz
    refine ⟨(hinside i hi z hz).1,hz.1.2,?_⟩
    convert (hinside i hi z hz).2 using 1
    all_goals try with_reducible_and_instances rfl
    rw [hlength i (hsub hi)]
    field_simp [hell0.ne',(DyadicLineGrid.scale_pos (level i)).ne']
  · simpa only [show (3+2*(1:ℝ))=5 by norm_num] using hcover

theorem exists_sharp_high_density_forest {ι : Type*} (tiles : Finset ι)
    (tile : ι → OrdinaryDensityTile) (ell0 w W tau K eta : ℝ) (q : ℤ)
    (hell0 : 0 < ell0) (hw : 0 < w) (hW : w ≤ W) (hK : 1 ≤ K) (heta : 0 < eta)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (hE : MeasurableSet E)
    (hEfin : (volume.prod volume) E ≠ ∞) (hu : Measurable u)
    (htail : K^(3-(203:ℝ))*(∫ z, topProfile 3 z ∂volume.prod volume) ≤ eta/2)
    (hdensity : ∀ i ∈ tiles, eta < (tile i).density ell0 w W tau q E u) :
    ∃ (test : ∀ i : tiles, OrdinaryDensityTest ell0 w W tau q (tile i))
      (keepers : Finset tiles) (assigned : tiles → keepers),
      let witness := fun i : tiles => densityTest E u (test i).top
        (scaledAngularCell (w/ell0) q (test i).level (test i).cell) K
      (∀ i ∈ keepers, MeasurableSet (witness i)) ∧
      Set.PairwiseDisjoint (keepers : Set tiles) witness ∧
      (∑ i ∈ keepers, (test i).top.area) ≤ 2*(volume.prod volume).real E/eta ∧
      (∀ i ∈ keepers, (eta/2)*(test i).top.area ≤ (volume.prod volume).real (witness i)) ∧
      (∀ i ∈ keepers, ∀ z ∈ witness i,
        z ∈ E ∧ z ∈ densitySpatialBox (test i).top K ∧
        |u z-(test i).top.slope| ≤ w/(test i).top.length) ∧
      (∀ i : tiles,
        ell0/DyadicLineGrid.scale (tile i).level ≤ (test (assigned i).val).top.length ∧
        (tile i).center ∈ densitySpatialBox (test (assigned i).val).top (5*K) ∧
        (test (assigned i).val).top.slope ∈
          scaledAngularCell (w/ell0) q (tile i).level (tile i).cell) := by
  classical
  have htest (i : tiles) : ∃ test : OrdinaryDensityTest ell0 w W tau q (tile i),
      eta*test.top.area < ∫ z in E ∩
        u ⁻¹' scaledAngularCell (w/ell0) q test.level test.cell,
        test.top.densityKernel 203 z ∂volume.prod volume :=
    (tile i).exists_test_of_lt_density ell0 w W tau q E u heta.le (hdensity i i.property)
  let test := fun i : tiles => Classical.choose (htest i)
  have hchosen (i : tiles) := Classical.choose_spec (htest i)
  obtain ⟨keepers,hsub,hmeas,hdisj,harea,hmass,hinside,hcover⟩ := exists_density_forest_at_radius
    Finset.univ (fun i => (test i).top) (fun i => (test i).level) (fun i => (test i).cell)
    q ell0 w W K eta hell0 hw hW hK heta (fun i _ => (test i).length_eq)
    (fun i _ => (test i).width_eq) (fun i _ => (test i).slope_mem_self)
    E u hE hEfin hu htail (fun i _ => (hchosen i).le)
  let assigned : tiles → keepers := fun i =>
    ⟨Classical.choose (hcover i (Finset.mem_univ i)),
      (Classical.choose_spec (hcover i (Finset.mem_univ i))).1⟩
  refine ⟨test,keepers,assigned,hmeas,hdisj,harea,hmass,hinside,?_⟩
  intro i
  have hassigned := (Classical.choose_spec (hcover i (Finset.mem_univ i))).2
  change (test i).top.length ≤ (test (assigned i).val).top.length ∧
      scaledAngularCell (w/ell0) q (test (assigned i).val).level (test (assigned i).val).cell ⊆
        scaledAngularCell (w/ell0) q (test i).level (test i).cell ∧
      densitySpatialBox (test i).top K ⊆
        densitySpatialBox (test (assigned i).val).top (5*K) at hassigned
  have hcenter := densitySpatialBox_mono (test i).top
    ((by norm_num : (1/2:ℝ)≤1).trans hK) (test i).center_mem
  have hlevels : (test i).level ≤ (tile i).level := density_dyadic_length_order hell0
    (by simpa only [(test i).length_eq] using (test i).tile_length_le)
  have hnested : scaledAngularCell (w/ell0) q (test i).level (test i).cell ⊆
      scaledAngularCell (w/ell0) q (tile i).level (tile i).cell :=
    scaledAngularCell_subset hlevels
      ⟨(test i).top.slope,(test i).slope_mem_tile,(test i).slope_mem_self⟩
  exact ⟨(test i).tile_length_le.trans hassigned.1,hassigned.2.2 hcenter,
    hnested (hassigned.2.1 (test (assigned i).val).slope_mem_self)⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataOrdinaryDensityForest
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary density selection, retaining its sharp witness radius
and original angular cells. Empty packet sets require no dummy keeper. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem densityTile_length (P : PacketLatticeData N κ Label Item) (oldSlope : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (q : P.PacketIndex) :
    P.topLength/DyadicLineGrid.scale (P.densityTile oldSlope cell q).level = P.length q.1 := by
  simp only [densityTile,DyadicLineGrid.scale,zpow_natCast,PacketLatticeData.length]

theorem exists_ordinary_density_forest (P : PacketLatticeData N κ Label Item)
    (packets : Finset P.PacketIndex) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (w tau eta : ℝ) (hw : 0<w) (hW : w≤P.width) (heta : 0<eta)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (hE : MeasurableSet E)
    (hEfin : (volume.prod volume) E≠∞) (hu : Measurable u)
    (hdensity : ∀ q∈packets, eta<P.ordinaryDensity 0 cell grid w tau E u q) :
    Nonempty (OrdinaryDensityForest P packets cell grid w tau eta E u) := by
  classical
  obtain ⟨test,keepers,assigned,hmeas,hdisj,harea,hmass,hinside,hassign⟩ :=
    exists_sharp_high_density_forest packets (P.densityTile 0 cell)
      P.topLength w P.width tau (densityRadius eta) eta grid P.topLength_pos hw hW
      (densityRadius_ge_one eta) heta E u hE hEfin hu (densityRadius_tail heta) hdensity
  refine ⟨{
    keepers := keepers
    top := fun i => (test i.val).top
    assigned := assigned
    witness := fun i => densityTest E u (test i.val).top
      (scaledAngularCell (w/P.topLength) grid (test i.val).level (test i.val).cell)
      (densityRadius eta)
    measurable := fun i => hmeas i.val i.property
    disjoint := ?_
    inside := fun i z hz => hinside i.val i.property z hz
    mass := fun i => hmass i.val i.property
    width := fun i => (test i.val).width_eq
    short := fun i => (test i.val).length_le
    area := ?_
    length_le := ?_
    center := ?_
    direction := fun q => (hassign q).2.2 }⟩
  · intro i j hij
    exact hdisj i.property j.property (fun h => hij (Subtype.ext h))
  · rw [Finset.sum_coe_sort keepers (fun j => (test j).top.area)]
    exact harea
  · intro q
    simpa only [P.densityTile_length] using (hassign q).1
  · intro q
    simpa only [densityTile,zero_mul,add_zero] using (hassign q).2.1

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSizeOnePacket
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal one-packet separated test controls each coefficient.
The top direction is chosen inside its actual half-open angular cell. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert

private theorem interval_far_point_p0 (a d theta : ℝ) (hd : 0<d) :
    ∃ s∈Ico a (a+d), d/4≤|s-theta| := by
  by_cases h : d/4≤|a-theta|
  · exact ⟨a,⟨le_rfl,by linarith⟩,h⟩
  · have hh := abs_lt.mp (lt_of_not_ge h)
    refine ⟨a+d/2,⟨by linarith,by linarith⟩,?_⟩
    exact (by linarith [hh.1] : d/4≤a+d/2-theta).trans (le_abs_self _)

namespace PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_one_packet_size_direction (w cb : ℝ) (hw : 0<w) (hcb : cb≤1/4)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (q : P.PacketIndex) :
    ∃ t∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1),
      cb*w/P.length q.1≤|t-P.rowSlope q.1 q.2.1| := by
  let u := w/P.topLength
  let k : ℤ := q.1.val
  let j := cell q.1 q.2.1
  let a := u*DyadicLineGrid.left grid k j
  let d := u*DyadicLineGrid.scale k
  have hu : 0<u := div_pos hw P.topLength_pos
  have hd : 0<d := mul_pos hu (DyadicLineGrid.scale_pos k)
  have hnext : DyadicLineGrid.left grid k (j+1)=
      DyadicLineGrid.left grid k j+DyadicLineGrid.scale k := by
    unfold DyadicLineGrid.left
    push_cast
    ring
  have hcell : Ico a (a+d)⊆scaledAngularCell u grid k j := by
    intro t ht
    change DyadicLineGrid.left grid k j≤t/u ∧ t/u<DyadicLineGrid.left grid k (j+1)
    constructor
    · apply (le_div_iff₀ hu).mpr
      simpa only [a,mul_comm] using ht.1
    · apply (div_lt_iff₀ hu).mpr
      rw [hnext]
      simpa only [a,d,add_mul,mul_add,mul_comm] using ht.2
  have hdEq : d=w/P.length q.1 := by
    dsimp only [d,u,k,length,DyadicLineGrid.scale]
    rw [zpow_natCast]
    field_simp [P.topLength_pos.ne']
  obtain ⟨t,ht,hfar⟩ := interval_far_point_p0 a d (P.rowSlope q.1 q.2.1) hd
  refine ⟨t,hcell ht,?_⟩
  calc
    cb*w/P.length q.1 = cb*d := by rw [hdEq,mul_div_assoc]
    _ ≤ d/4 := by nlinarith
    _ ≤ _ := hfar

theorem coefficient_le_of_size_tests
    (w cb tau sigma : ℝ) (hw : 0<w) (hcb : cb≤1/4) (hsigma : 0 ≤ sigma)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (R : Finset P.PacketIndex)
    (hsize : ∀ T : SlopeBox, T.width=P.width → T.length≤tau →
      P.unsignedSizeTestEnergy w cb cell grid c R T ≤ sigma^2*T.area)
    (q : P.PacketIndex) (hq : q∈R) (hlen : P.length q.1≤tau) :
    ‖c q.1 q.2.1 q.2.2‖ ≤ sigma := by
  obtain ⟨t,ht,hsep⟩ := P.exists_one_packet_size_direction w cb hw hcb cell grid q
  let T : SlopeBox := ⟨P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2,t,
    P.length q.1,P.width,P.length_pos q.1,P.width_pos⟩
  have hsp : (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T (1/2) := by
    change |P.actualX q.1 q.2.1 q.2.2-P.actualX q.1 q.2.1 q.2.2|≤1/2*P.length q.1 ∧
      |(P.actualZ q.1 q.2.1 q.2.2-P.actualZ q.1 q.2.1 q.2.2)-
        t*(P.actualX q.1 q.2.1 q.2.2-P.actualX q.1 q.2.1 q.2.2)|≤1/2*P.width
    simp only [sub_self,mul_zero,abs_zero]
    exact ⟨mul_nonneg (by norm_num) (P.length_pos q.1).le,
      mul_nonneg (by norm_num) P.width_pos.le⟩
  have hguard : P.length q.1≤T.length ∧
      (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T (1/2) ∧
      T.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1) ∧
      cb*w/P.length q.1≤|T.slope-P.rowSlope q.1 q.2.1| := ⟨le_rfl,hsp,ht,hsep⟩
  have henergy : ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width≤
      P.unsignedSizeTestEnergy w cb cell grid c R T := by
    have h := Finset.single_le_sum (s:=R) (f:=fun p : P.PacketIndex =>
      if P.length p.1≤T.length ∧
        (P.actualX p.1 p.2.1 p.2.2,P.actualZ p.1 p.2.1 p.2.2)∈densitySpatialBox T (1/2) ∧
        T.slope∈scaledAngularCell (w/P.topLength) grid p.1.val (cell p.1 p.2.1) ∧
        cb*w/P.length p.1≤|T.slope-P.rowSlope p.1 p.2.1| then
        ‖c p.1 p.2.1 p.2.2‖^2*P.length p.1*P.width else 0)
      (fun p _ => by
        split_ifs
        · exact mul_nonneg (mul_nonneg (sq_nonneg _) (P.length_pos p.1).le) P.width_pos.le
        · exact le_rfl) hq
    dsimp only [unsignedSizeTestEnergy]
    simpa only [ite_eq_left hguard] using h
  have he := henergy.trans (hsize T rfl hlen)
  change ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width ≤ sigma^2*(P.length q.1*P.width) at he
  have hsq : ‖c q.1 q.2.1 q.2.2‖^2 ≤ sigma^2 := by
    apply (mul_le_mul_iff_left₀ (mul_pos (P.length_pos q.1) P.width_pos)).mp
    simpa only [mul_assoc,mul_comm,mul_left_comm] using he
  nlinarith [norm_nonneg (c q.1 q.2.1 q.2.2)]

end PacketLatticeData
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataScaleRestriction
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Drop a finite initial scale segment without changing any physical
packet in the remaining dyadic family. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem drop_length (first : Fin N) (j : Fin (N-first.val)) :
    P.length first/(2:ℝ)^j.val=P.length (dropIndex first j) := by
  unfold length dropIndex
  rw [pow_add,div_div]

@[simp] theorem dropScales_length (first : Fin N) (j : Fin (N-first.val)) :
    (P.dropScales first).length j=P.length (dropIndex first j) := P.drop_length first j

@[simp] theorem dropScales_physicalPacket (first : Fin N) (t : ℝ)
    (j : Fin (N-first.val)) (l : (P.dropScales first).labels j)
    (u : Item (dropIndex first j) l) (k : κ) :
    (P.dropScales first).physicalPacket t j l u k=P.physicalPacket t (dropIndex first j) l u k := by
  unfold physicalPacket actualX actualZ
  simp only [dropScales_length]
  rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityRebase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted density tests are invariant under a dyadic change of
starting scale. Their physical boxes and integrals are unchanged. -/
noncomputable section
open Set
namespace LipschitzHilbert
open DyadicLineGrid

/-- Each original test has exactly the same weighted average after rebasing. -/
theorem density_rebase_test_value {ell0 w W tau : ℝ} {q : ℤ} {tile : OrdinaryDensityTile}
    (test : OrdinaryDensityTest ell0 w W tau q tile)
    (h : ℤ) (hell0 : 0<ell0) (hw : 0<w)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) :
    densityAverage (test.rebase h hell0 hw).top E u
      (scaledAngularCell (w/(ell0/scale h)) ((h.negOnePow : ℤ)*q)
        (test.rebase h hell0 hw).level (test.rebase h hell0 hw).cell)=
    densityAverage test.top E u (scaledAngularCell (w/ell0) q test.level test.cell) := by
  simp only [OrdinaryDensityTest.rebase,density_rebase_cell ell0 w hell0 hw]

theorem density_restore_test_value {ell0 w W tau : ℝ} {q : ℤ} {tile : OrdinaryDensityTile}
    (h : ℤ) (hell0 : 0<ell0) (hw : 0<w)
    (test : OrdinaryDensityTest (ell0/scale h) w W tau ((h.negOnePow : ℤ)*q) (tile.rebase h))
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) :
    densityAverage (test.restore h hell0 hw).top E u
      (scaledAngularCell (w/ell0) q (test.restore h hell0 hw).level (test.restore h hell0 hw).cell)=
    densityAverage test.top E u (scaledAngularCell (w/(ell0/scale h))
      ((h.negOnePow : ℤ)*q) test.level test.cell) := by
  have he := density_rebase_cell ell0 w hell0 hw q h (test.level+h) test.cell
  rw [add_sub_cancel_right] at he
  simp only [OrdinaryDensityTest.restore,←he]

/-- All weighted box tests, including tests above the initial scale,
correspond in both directions, hence the density is exactly preserved. -/
theorem OrdinaryDensityTile.density_rebase (tile : OrdinaryDensityTile)
    (ell0 w W tau : ℝ) (h : ℤ) (q : ℤ) (hell0 : 0<ell0) (hw : 0<w)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) :
    (tile.rebase h).density (ell0/scale h) w W tau ((h.negOnePow : ℤ)*q) E u=
      tile.density ell0 w W tau q E u := by
  unfold OrdinaryDensityTile.density
  congr 1
  ext x
  constructor
  · intro hx
    rcases hx with rfl | ⟨test,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨test.restore h hell0 hw,density_restore_test_value h hell0 hw test E u⟩
  · intro hx
    rcases hx with rfl | ⟨test,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨test.rebase h hell0 hw,density_rebase_test_value test h hell0 hw E u⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDropDensity
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic scale restriction preserves every actual packet density.
The alternating angular grid is rebased with its required sign. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

@[simp] theorem dropScales_actualX (first : Fin N) (j : Fin (N-first.val))
    (l : (P.dropScales first).labels j) (u : Item (dropIndex first j) l) :
    (P.dropScales first).actualX j l u=P.actualX (dropIndex first j) l u := by
  simp only [actualX,dropScales_length]
  rfl

@[simp] theorem dropScales_actualZ (first : Fin N) (j : Fin (N-first.val))
    (l : (P.dropScales first).labels j) (u : Item (dropIndex first j) l) :
    (P.dropScales first).actualZ j l u=P.actualZ (dropIndex first j) l u := by
  simp only [actualZ,dropScales_length]
  rfl

theorem dropScales_densityTile (first : Fin N) (t : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (j : Fin (N-first.val))
    (l : (P.dropScales first).labels j) (u : Item (dropIndex first j) l) :
    (P.dropScales first).densityTile t (fun j l => cell (dropIndex first j) l) ⟨j,⟨l,u⟩⟩=
      (P.densityTile t cell ⟨dropIndex first j,⟨l,u⟩⟩).rebase first.val := by
  simp only [densityTile,OrdinaryDensityTile.rebase,dropScales_actualX,dropScales_actualZ]
  congr 1
  simp only [dropIndex,Nat.cast_add]
  omega

theorem dropScales_ordinaryDensity (first : Fin N) (t w tau : ℝ) (hw : 0<w)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (E : Set (ℝ×ℝ)) (v : ℝ×ℝ → ℝ) (j : Fin (N-first.val))
    (l : (P.dropScales first).labels j) (u : Item (dropIndex first j) l) :
    (P.dropScales first).ordinaryDensity t (fun j l => cell (dropIndex first j) l)
      (((first.val:ℤ).negOnePow : ℤ)*grid) w tau E v ⟨j,⟨l,u⟩⟩=
      P.ordinaryDensity t cell grid w tau E v ⟨dropIndex first j,⟨l,u⟩⟩ := by
  unfold ordinaryDensity
  rw [P.dropScales_densityTile]
  have he : (P.dropScales first).topLength=P.topLength/DyadicLineGrid.scale first.val := by
    simp only [dropScales,length,DyadicLineGrid.scale,zpow_natCast]
  change ((P.densityTile t cell ⟨dropIndex first j,⟨l,u⟩⟩).rebase first.val).density
    (P.dropScales first).topLength w P.width tau _ E v = _
  rw [he]
  exact OrdinaryDensityTile.density_rebase _ P.topLength w P.width tau first.val grid
    P.topLength_pos hw E v

theorem dropScales_angularCell (first : Fin N) (w : ℝ) (hw : 0<w)
    (q : ℤ) (j : Fin (N-first.val)) (cell : ℤ) :
    scaledAngularCell (w/(P.dropScales first).topLength)
      (((first.val:ℤ).negOnePow : ℤ)*q) j.val cell=
    scaledAngularCell (w/P.topLength) q (dropIndex first j).val cell := by
  have he : w/(P.dropScales first).topLength=(w/P.topLength)*DyadicLineGrid.scale first.val := by
    change w/(P.topLength/(2:ℝ)^first.val)=(w/P.topLength)*DyadicLineGrid.scale first.val
    simp only [DyadicLineGrid.scale,zpow_natCast]
    field_simp
  rw [he,scaledAngularCell_rebase _ (div_pos hw P.topLength_pos)]
  simp only [dropIndex,Nat.cast_add]


end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataScaleRestrictionSums
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dropping an initial scale segment is an exact reindexing of finite
packet sums. Original coefficients and physical packets are retained. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
attribute [local instance] Classical.propDecidable

theorem dropIndex_injective (first : Fin N) : Function.Injective (dropIndex first) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  change first.val+i.val=first.val+j.val at h
  omega

theorem dropIndex_surjective_tail (first j : Fin N) (hj : first.val≤j.val) :
    ∃ i : Fin (N-first.val), dropIndex first i=j := by
  refine ⟨⟨j.val-first.val,by have := j.isLt; omega⟩,?_⟩
  apply Fin.ext
  change first.val+(j.val-first.val)=j.val
  omega

theorem sum_dropIndex {E : Type*} [AddCommMonoid E] (first : Fin N) (f : Fin N → E) :
    (∑ j : Fin (N-first.val), f (dropIndex first j))=
      ∑ j∈Finset.univ.filter (fun j : Fin N => first.val≤j.val), f j := by
  apply Finset.sum_bij (fun j _ => dropIndex first j)
  · intro j _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by dsimp [dropIndex]; omega⟩
  · intro i _ j _ hij
    exact dropIndex_injective first hij
  · intro j hj
    obtain ⟨i,hi⟩ := dropIndex_surjective_tail first j (Finset.mem_filter.mp hj).2
    exact ⟨i,Finset.mem_univ _,hi⟩
  · intro j _
    rfl

theorem sum_dropScales {E : Type*} [AddCommMonoid E] (first : Fin N)
    (f : ∀ j (l : P.labels j), Item j l → E) :
    (∑ j : Fin (N-first.val), ∑ l : (P.dropScales first).labels j,
      ∑ u : Item (dropIndex first j) l, f (dropIndex first j) l u)=
    ∑ j∈Finset.univ.filter (fun j : Fin N => first.val≤j.val),
      ∑ l : P.labels j, ∑ u : Item j l, f j l u :=
  sum_dropIndex first (fun j => ∑ l : P.labels j, ∑ u : Item j l, f j l u)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDropPackets
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite packet subsets after dropping an initial scale segment. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
attribute [local instance] Classical.propDecidable

theorem sum_dropPackets {E : Type*} [AddCommMonoid E]
    (first : Fin N) (Q : Finset P.PacketIndex)
    (hQ : ∀ q∈Q, first.val≤q.1.val) (f : P.PacketIndex → E) :
    (∑ q∈P.dropPackets first Q, f (P.dropPacket first q))=∑ q∈Q, f q := by
  classical
  have h := P.sum_dropScales first (fun j l u =>
    if (⟨j,⟨l,u⟩⟩ : P.PacketIndex)∈Q then f ⟨j,⟨l,u⟩⟩ else 0)
  calc
    _ = ∑ j∈Finset.univ.filter (fun j : Fin N => first.val≤j.val),
        ∑ l : P.labels j, ∑ u : Item j l,
          if (⟨j,⟨l,u⟩⟩ : P.PacketIndex)∈Q then f ⟨j,⟨l,u⟩⟩ else 0 := by
      rw [dropPackets,Finset.sum_filter]
      simp only [Fintype.sum_sigma,dropPacket]
      exact h
    _ = ∑ j : Fin N, ∑ l : P.labels j, ∑ u : Item j l,
        if (⟨j,⟨l,u⟩⟩ : P.PacketIndex)∈Q then f ⟨j,⟨l,u⟩⟩ else 0 := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hn
      apply Finset.sum_eq_zero
      intro l _
      apply Finset.sum_eq_zero
      intro u _
      apply ite_eq_right
      intro hmem
      exact hn (Finset.mem_filter.mpr ⟨hj,hQ ⟨j,⟨l,u⟩⟩ hmem⟩)
    _ = ∑ q : P.PacketIndex, if q∈Q then f q else 0 := by simp only [Fintype.sum_sigma]
    _ = _ := by rw [←Finset.sum_filter]; simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDropSize
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dropping scales preserves every remaining unsigned size test. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem dropPackets_tail (first : Fin N) (Q : Finset P.PacketIndex) :
    P.dropPackets first (Q.filter (fun q => first.val≤q.1.val))=P.dropPackets first Q := by
  ext q
  simp only [mem_dropPackets,Finset.mem_filter]
  have h : first.val≤(P.dropPacket first q).1.val := by
    change first.val≤first.val+q.1.val
    omega
  exact and_iff_left h

theorem dropScales_unsignedSizeTestEnergy (first : Fin N) (Q : Finset P.PacketIndex)
    (w cb : ℝ) (hw : 0<w) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (T : SlopeBox) :
    (P.dropScales first).unsignedSizeTestEnergy w cb (fun j l => cell (dropIndex first j) l)
      (((first.val:ℤ).negOnePow : ℤ)*grid) (fun j l v => c (dropIndex first j) l v)
      (P.dropPackets first Q) T=
    P.unsignedSizeTestEnergy w cb cell grid c (Q.filter (fun q => first.val≤q.1.val)) T := by
  let f := fun q : P.PacketIndex =>
    if P.length q.1≤T.length ∧
      (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T (1/2) ∧
      T.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1) ∧
      cb*w/P.length q.1≤|T.slope-P.rowSlope q.1 q.2.1| then
      ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0
  have hsum := P.sum_dropPackets first (Q.filter (fun q => first.val≤q.1.val))
    (fun q hq => (Finset.mem_filter.mp hq).2) f
  rw [P.dropPackets_tail] at hsum
  unfold unsignedSizeTestEnergy
  refine Eq.trans ?_ hsum
  apply Finset.sum_congr rfl
  rintro ⟨j,l,v⟩ _
  simp only [dropScales_length,dropScales_actualX,dropScales_actualZ,P.dropScales_angularCell first w hw]
  rfl

theorem dropScales_unsignedSizeTestEnergy_le (first : Fin N) (Q : Finset P.PacketIndex)
    (w cb : ℝ) (hw : 0<w) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (T : SlopeBox) :
    (P.dropScales first).unsignedSizeTestEnergy w cb (fun j l => cell (dropIndex first j) l)
      (((first.val:ℤ).negOnePow : ℤ)*grid) (fun j l v => c (dropIndex first j) l v)
      (P.dropPackets first Q) T≤P.unsignedSizeTestEnergy w cb cell grid c Q T := by
  rw [P.dropScales_unsignedSizeTestEnergy first Q w cb hw cell grid c T]
  exact P.unsignedSizeTestEnergy_mono w cb cell grid c (Finset.filter_subset _ _) T

theorem dropPackets_nonempty (first : Fin N) (Q : Finset P.PacketIndex)
    (hne : Q.Nonempty) (hQ : ∀ q∈Q, first.val≤q.1.val) :
    (P.dropPackets first Q).Nonempty := by
  obtain ⟨⟨j,l,v⟩,hq⟩ := hne
  obtain ⟨i,hi⟩ := dropIndex_surjective_tail first j (hQ ⟨j,⟨l,v⟩⟩ hq)
  subst j
  exact ⟨⟨i,⟨l,v⟩⟩,P.mem_dropPackets first Q _ |>.mpr hq⟩

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDropTreeTransport
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite selected-tree sums after a change of starting scale. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem dropPackets_mono (first : Fin N) {Q R : Finset P.PacketIndex} (h : Q⊆R) :
    P.dropPackets first Q⊆P.dropPackets first R := by
  intro q hq
  exact (P.mem_dropPackets first R q).mpr (h ((P.mem_dropPackets first Q q).mp hq))

theorem dropPackets_selector_value (first : Fin N) (Q : Finset P.PacketIndex)
    (hQ : ∀ q∈Q, first.val≤q.1.val) (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (beta : ∀ j, P.labels j → κ → ℂ) (z : ℝ×ℝ) :
    (∑ q∈P.dropPackets first Q, WithLp.toLp 2 (fun k =>
      c (dropIndex first q.1) q.2.1 q.2.2 k*beta (dropIndex first q.1) q.2.1 k*
      (P.dropScales first).physicalPacket t q.1 q.2.1 q.2.2 k z))=
    ∑ q∈Q, WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*beta q.1 q.2.1 k*
      P.physicalPacket t q.1 q.2.1 q.2.2 k z) := by
  have h := P.sum_dropPackets first Q hQ (fun q => WithLp.toLp 2 (fun k =>
    c q.1 q.2.1 q.2.2 k*beta q.1 q.2.1 k*P.physicalPacket t q.1 q.2.1 q.2.2 k z))
  simpa only [dropPacket,P.dropScales_physicalPacket] using h

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataEnclosingScale
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replace an arbitrary selected top length by a comparable existing
dyadic scale while retaining every packet below that top. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem exists_enclosing_scale (L : ℝ) (hLtop : L≤P.topLength)
    (hwitness : ∃ j, P.length j≤L) :
    ∃ first : Fin N, P.length first≤L ∧ L<2*P.length first ∧
      ∀ j, P.length j≤L → first≤j := by
  classical
  let S := Finset.univ.filter (fun j : Fin N => P.length j≤L)
  have hS : S.Nonempty := by
    obtain ⟨j,hj⟩ := hwitness
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  let first := S.min' hS
  have hfirst : P.length first≤L := (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
  have hmin (j : Fin N) (hj : P.length j≤L) : first≤j :=
    Finset.min'_le S j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)
  refine ⟨first,hfirst,?_,hmin⟩
  by_cases hz : first.val=0
  · have he : P.length first=P.topLength := by simp only [length,hz,pow_zero,div_one]
    rw [he]
    linarith [P.topLength_pos]
  · let prev : Fin N := ⟨first.val-1,by have := first.isLt; omega⟩
    have hp : ¬P.length prev≤L := by
      intro hp
      have hh := hmin prev hp
      change first.val≤first.val-1 at hh
      omega
    have he : P.length prev=2*P.length first := by
      have hi : first.val=prev.val+1 := by dsimp [prev]; omega
      unfold length
      rw [hi,pow_succ]
      field_simp
    rw [←he]
    exact lt_of_not_ge hp

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedTree
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary tree estimates for selected packets of an unrestricted slope
family. The only published input is scalar Lépingle variation. Small shear
is proved for the selected reference family, not assumed globally. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData

theorem exists_recentered_selected_tree_estimate (hL : LepingleInput)
    (cStar cEta CEta cb Cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 ≤ cb) (hCb : 0≤Cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (M R K : ℕ),
      Cb≤R → 207≤P.order → ∀ (Q : Finset P.PacketIndex), Q.Nonempty →
      ∀ (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (t a b w tau radius Lip eta sigma : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ),
      0<w → ∀ (F : ℝ), 0≤F → Cb*w≤P.width →
      (∀ k, |P.frequency k|≤F/w) → P.topLength≤tau → 0≤Lip → 0≤eta → 0 ≤ sigma →
      1 ≤ radius+Cb → radius+Cb≤(2:ℝ)^K →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => P.rowSlope j l) (w/P.length j) M) →
      (∀ q∈Q, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2) →
      (∀ q∈Q, |P.actualZ q.1 q.2.1 q.2.2-t*P.actualX q.1 q.2.1 q.2.2-b|≤P.width/2) →
      (∀ q∈Q, t∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈Q, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈Q, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |ξ+P.rowSlope q.1 q.2.1*η| ≤ cStar/P.length q.1 ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ q∈Q, |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1) →
      (∀ q∈Q, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |η-P.frequency k|≤Cv/P.width) →
      (∀ q∈Q, ‖c q.1 q.2.1 q.2.2‖ ≤ sigma) →
      (∑ q∈Q, if cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t| then
        ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0) ≤ sigma^2*(P.topLength*P.width) →
    ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (selector j l k)) →
      (∀ j l k s, ‖selector j l k s‖≤1) →
      (∀ q∈Q, ∀ k, selector q.1 q.2.1 k t≠0 → cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 → |s-P.rowSlope j l| ≤ radius*(w/P.length j)) →
      (∀ j l k s, |s-t|≤w/P.length j →
        ‖selector j l k s-selector j l k t‖≤Lip*(|s-t|/(w/P.length j))) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∀ q∈Q, P.ordinaryDensity 0 cell grid w tau E u q≤eta) →
      let F := fun z => ∑ q∈Q, WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
        selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
      IntegrableOn F E (volume.prod volume) ∧
        (∫ z in E, ‖F z‖ ∂volume.prod volume)≤
          P.referenceTreeConstant C ((2*R+1)*M) K Lip*sigma*eta*P.topLength*P.width := by
  obtain ⟨C,hC,hTree⟩ := SourceLabeledLattice.exists_reference_ordinary_tree_estimate hL
    cStar cEta CEta cb Cb Cv hcStar hcEta hCEta hCv hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M R K hR horder S hS c t a b w tau radius Lip eta sigma cell grid
    hw F hF hwideW hfreq htime hLip heta hsigma hwide hK hlocal hX hY href hangle hspectrum hslope hbin hc hsize
    selector hsel hselbound hselaway hselsupport hselradius hselnear E hE u hu hdensity
  let T := P.selectedReference S t Cb w F hw hCb hF hwideW hfreq hslope
  let d := P.selectedCoefficients S t Cb w F hw hCb hF hwideW hfreq hslope c
  let beta := fun j (l : T.labels j) k s => selector j (P.selectedOriginalLabel S j l) k s
  let cells := P.selectedCells S t Cb w F hw hCb hF hwideW hfreq hslope cell
  have hmem (j : Fin N) (l : T.labels j) (v : P.SelectedItem S j l) :
      (⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ : P.PacketIndex)∈S :=
    P.selectedItem_mem S j l v
  have hne : Nonempty T.PacketIndex := by
    obtain ⟨q,hq⟩ := hS
    exact ⟨(P.selectedReferenceEquiv S t Cb w F hw hCb hF hwideW hfreq hslope).symm ⟨q,hq⟩⟩
  have hcard (j : Fin N) : (T.labels j).card≤(2*R+1)*M :=
    P.selectedReference_card S t Cb w F hw hCb hF hwideW hfreq hslope M R hR hlocal j
  have hTX (q : T.PacketIndex) : |T.actualX q.1 q.2.1 q.2.2-a|≤T.topLength/2 := by
    rcases q with ⟨j,l,v⟩
    exact hX ⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ (hmem j l v)
  have hTY (q : T.PacketIndex) : |T.actualZ q.1 q.2.1 q.2.2-b|≤T.width/2 := by
    rcases q with ⟨j,l,v⟩
    change |(P.selectedReference S t Cb w F hw hCb hF hwideW hfreq hslope).actualZ j l v-b|≤P.width/2
    rw [P.selectedReference_actualZ S t Cb w F hw hCb hF hwideW hfreq hslope j l v]
    exact hY ⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ (hmem j l v)
  have hTref (q : T.PacketIndex) : t∈scaledAngularCell (w/T.topLength)
      grid q.1.val (cells q.1 q.2.1) := by
    rcases q with ⟨j,l,v⟩
    exact href ⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ (hmem j l v)
  have hTangle (j : Fin N) (l : T.labels j) : t+T.rowSlope j l∈
      scaledAngularCell (w/T.topLength) grid j.val (cells j l) := by
    obtain ⟨v,hv⟩ := P.selectedLabel_has_packet S j l
    rw [P.selectedReference_slope S t Cb w F hw hCb hF hwideW hfreq hslope j l]
    exact hangle ⟨j,⟨P.selectedOriginalLabel S j l,v⟩⟩ hv
  have hTspectrum (j : Fin N) (l : T.labels j) (v : P.SelectedItem S j l)
      (k : κ) (xi eta : ℝ) (h : planarAngularFourier (T.physicalPacket t j l v k) (xi,eta)≠0) :
      |xi+(t+T.rowSlope j l)*eta| ≤ cStar/T.length j ∧ cEta≤w*eta ∧ w*eta≤CEta :=
    P.selectedReference_spectrum_at S t Cb w F hw hCb hF hwideW hfreq hslope cStar cEta CEta
      j l v k xi eta (hspectrum ⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ (hmem j l v) k xi eta) h
  have hTslope (j : Fin N) (l : T.labels j) : |T.rowSlope j l|≤Cb*w/T.length j :=
    P.selectedLabel_near S t Cb w hslope j l
  have hTbin (j : Fin N) (l : T.labels j) (v : P.SelectedItem S j l)
      (k : κ) (xi eta : ℝ) (h : planarAngularFourier (T.physicalPacket t j l v k) (xi,eta)≠0) :
      |eta-T.frequency k|≤Cv/T.width := by
    change planarAngularFourier
      ((P.selectedReference S t Cb w F hw hCb hF hwideW hfreq hslope).physicalPacket t j l v k) (xi,eta)≠0 at h
    rw [P.selectedReference_physicalPacket S t Cb w F hw hCb hF hwideW hfreq hslope j l v k] at h
    exact hbin ⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ (hmem j l v) k xi eta h
  have hTc (j : Fin N) (l : T.labels j) (v : P.SelectedItem S j l) : ‖d j l v‖ ≤ sigma :=
    hc ⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ (hmem j l v)
  have hTsize : T.angularSeparatedTreeEnergy cb w d ≤ sigma^2*(T.topLength*T.width) :=
    (P.selectedReference_separated_energy S t Cb w F hw hCb hF hwideW hfreq hslope c cb).le.trans hsize
  have haway (j : Fin N) (l : T.labels j) (k : κ) :
      beta j l k t≠0 → cb*w/T.length j≤|T.rowSlope j l| := by
    obtain ⟨v,hv⟩ := P.selectedLabel_has_packet S j l
    exact hselaway ⟨j,⟨P.selectedOriginalLabel S j l,v⟩⟩ hv k
  have hradius (j : Fin N) (l : T.labels j) (k : κ) (s : ℝ) (hs : beta j l k s≠0) :
      |s-(t+T.rowSlope j l)| ≤ radius*(w/T.length j) := by
    rw [P.selectedReference_slope S t Cb w F hw hCb hF hwideW hfreq hslope j l]
    exact hselradius j (P.selectedOriginalLabel S j l) k s hs
  have hD (q : T.PacketIndex) : T.ordinaryDensity t cells grid w tau E u q≤eta := by
    rcases q with ⟨j,l,v⟩
    change (P.selectedReference S t Cb w F hw hCb hF hwideW hfreq hslope).ordinaryDensity t
      (P.selectedCells S t Cb w F hw hCb hF hwideW hfreq hslope cell) grid w tau E u ⟨j,l,v⟩≤eta
    rw [P.selectedReference_density S t Cb w F hw hCb hF hwideW hfreq hslope cell grid tau E u j l v]
    exact hdensity ⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ (hmem j l v)
  have h := hTree N κ Label (P.SelectedItem S) T ((2*R+1)*M) K hcard horder hne
    d t a b w tau radius Lip eta sigma cells grid hw htime hLip heta hsigma hwide hK
    hTX hTY hTref hTangle hTspectrum hTslope hTbin hTc hTsize beta
    (fun j l k => hsel j (P.selectedOriginalLabel S j l) k)
    (fun j l k s => hselbound j (P.selectedOriginalLabel S j l) k s) haway
    (fun j l k s => hselsupport j (P.selectedOriginalLabel S j l) k s) hradius
    (fun j l k s => hselnear j (P.selectedOriginalLabel S j l) k s)
    E hE u hu hD
  dsimp only at h ⊢
  have heval (z : ℝ×ℝ) : T.physicalTreeSelectorValue t d
      (fun j l k => beta j l k (u z)) z=
      ∑ q∈S, WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
        selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z) :=
    P.selectedReference_synthesis S t Cb w F hw hCb hF hwideW hfreq hslope c
      (fun j l k => selector j l k (u z)) z
  have hconst : T.ordinaryTreeConstant C ((2*R+1)*M) K Lip=
      P.referenceTreeConstant C ((2*R+1)*M) K Lip := rfl
  simp only [heval,hconst] at h
  exact h

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataTreeSize
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual unsigned size test supplies the separated energy of
a spatial piece in arbitrary reference coordinates. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem reference_separated_energy_eq_sizeTest
    (Q : Finset P.PacketIndex) (t w cb : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (T : SlopeBox)
    (ht : T.slope=t)
    (hlen : ∀ q∈Q, P.length q.1≤T.length)
    (hcenter : ∀ q∈Q, (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T (1/2))
    (hangle : ∀ q∈Q, t∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) :
    (∑ q∈Q, if cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t| then
      ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0)=
      P.unsignedSizeTestEnergy w cb cell grid c Q T := by
  unfold unsignedSizeTestEnergy
  apply Finset.sum_congr rfl
  intro q hq
  simp only [hlen q hq,hcenter q hq,ht,abs_sub_comm,hangle q hq,true_and]

theorem reference_selected_size_bound
    (Q R : Finset P.PacketIndex) (hQR : Q⊆R) (t w cb tau sigma : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (T : SlopeBox)
    (ht : T.slope=t) (hwidth : T.width=P.width) (htime : T.length≤tau)
    (hlen : ∀ q∈Q, P.length q.1≤T.length)
    (hcenter : ∀ q∈Q, (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T (1/2))
    (hangle : ∀ q∈Q, t∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (hsize : ∀ U : SlopeBox, U.width=P.width → U.length≤tau →
      P.unsignedSizeTestEnergy w cb cell grid c R U ≤ sigma^2*U.area) :
    (∑ q∈Q, if cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t| then
      ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0) ≤ sigma^2*T.area := by
  rw [P.reference_separated_energy_eq_sizeTest Q t w cb cell grid c T ht hlen hcenter hangle]
  exact (P.unsignedSizeTestEnergy_mono w cb cell grid c hQR T).trans (hsize T hwidth htime)

/-- Global size control supplies precisely the separated energy bound
needed on each centered spatial piece. -/
theorem reference_piece_size_bound
    (Q R : Finset P.PacketIndex) (hQR : Q⊆R) (t a b w cb tau sigma : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (htime : P.topLength≤tau)
    (hX : ∀ q∈Q, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2)
    (hY : ∀ q∈Q, |P.actualZ q.1 q.2.1 q.2.2-t*P.actualX q.1 q.2.1 q.2.2-b|≤P.width/2)
    (hangle : ∀ q∈Q, t∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (hsize : ∀ U : SlopeBox, U.width=P.width → U.length≤tau →
      P.unsignedSizeTestEnergy w cb cell grid c R U ≤ sigma^2*U.area) :
    (∑ q∈Q, if cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t| then
      ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0) ≤ sigma^2*(P.topLength*P.width) := by
  apply P.reference_selected_size_bound Q R hQR t w cb tau sigma cell grid c
    (P.referenceTreeTop t a b) rfl rfl htime _ _ hangle hsize
  · intro q _
    exact div_le_self P.topLength_pos.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  · intro q hq
    change |P.actualX q.1 q.2.1 q.2.2-a|≤(1/2:ℝ)*P.topLength ∧
      |(P.actualZ q.1 q.2.1 q.2.2-(b+t*a))-t*(P.actualX q.1 q.2.1 q.2.2-a)|≤(1/2:ℝ)*P.width
    constructor
    · linarith [hX q hq]
    · have he : (P.actualZ q.1 q.2.1 q.2.2-(b+t*a))-t*(P.actualX q.1 q.2.1 q.2.2-a)=
          P.actualZ q.1 q.2.1 q.2.2-t*P.actualX q.1 q.2.1 q.2.2-b := by ring
      rw [he]
      linarith [hY q hq]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSpatialSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded rectangle splits into uniformly many half-open cells.
Each cell has the exact center bounds used by the ordinary tree estimate. -/
noncomputable section
open Set
namespace LipschitzHilbert

theorem spatialCell_center_bound (a L x : ℝ) (hL : 0<L) :
    |x-spatialCellCenter a L (spatialCellIndex a L x)|≤L/2 := by
  have hlo := (le_div_iff₀ hL).mp (Int.floor_le ((x-a)/L))
  have hhi := (div_lt_iff₀ hL).mp (Int.lt_floor_add_one ((x-a)/L))
  unfold spatialCellCenter spatialCellIndex
  rw [abs_le]
  constructor <;> linarith

theorem spatialCell_index_bound (a L x : ℝ) (hL : 0<L) (K : ℕ)
    (hx : |x-a|≤(K:ℝ)*L) :
    spatialCellIndex a L x∈Finset.Icc (-(K:ℤ)) K := by
  have hlo : -(K:ℝ)≤(x-a)/L := (le_div_iff₀ hL).mpr (by linarith [(abs_le.mp hx).1])
  have hhi : (x-a)/L≤(K:ℝ) := (div_le_iff₀ hL).mpr (abs_le.mp hx).2
  apply Finset.mem_Icc.mpr
  constructor
  · apply Int.le_floor.mpr
    simpa only [Int.cast_neg,Int.cast_natCast] using hlo
  · have h := (Int.floor_le ((x-a)/L)).trans hhi
    exact_mod_cast h

/-- Cells covering an enlarged top are bounded independently of packet count. -/
theorem spatialCell_count (K : ℕ) :
    ((Finset.Icc (-(K:ℤ)) K) ×ˢ (Finset.Icc (-(K:ℤ)) K)).card=(2*K+1)^2 := by
  rw [Finset.card_product]
  have hc : (Finset.Icc (-(K:ℤ)) K).card=2*K+1 := by
    rw [Int.card_Icc]
    omega
  rw [hc]
  ring

theorem spatialPacketCell_mem {ι : Type*} (x y : ι → ℝ) (a b L W : ℝ)
    (hL : 0<L) (hW : 0<W) (K : ℕ) (q : ι)
    (hx : |x q-a|≤(K:ℝ)*L) (hy : |y q-b|≤(K:ℝ)*W) :
    spatialPacketCell x y a b L W q∈
      (Finset.Icc (-(K:ℤ)) K) ×ˢ (Finset.Icc (-(K:ℤ)) K) :=
  Finset.mem_product.mpr ⟨spatialCell_index_bound a L (x q) hL K hx,
    spatialCell_index_bound b W (y q) hW K hy⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSpatialTreePieces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite splitting of a selected tree into spatial pieces with
the center bounds required by the ordinary tree theorem. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

variable {ι : Type*}

theorem spatialTreePiece_centers (S : Finset ι) (x y : ι → ℝ) (a b L W : ℝ)
    (hL : 0<L) (hW : 0<W) (p : ℤ×ℤ) (q : ι)
    (hq : q∈spatialTreePiece S x y a b L W p) :
    |x q-spatialCellCenter a L p.1|≤L/2 ∧ |y q-spatialCellCenter b W p.2|≤W/2 := by
  have he := (Finset.mem_filter.mp hq).2
  rw [←he]
  exact ⟨spatialCell_center_bound a L (x q) hL,spatialCell_center_bound b W (y q) hW⟩

theorem sum_spatialTreePieces {E : Type*} [AddCommMonoid E]
    (S : Finset ι) (x y : ι → ℝ) (a b L W : ℝ) (hL : 0<L) (hW : 0<W) (K : ℕ)
    (hx : ∀ q∈S, |x q-a|≤(K:ℝ)*L) (hy : ∀ q∈S, |y q-b|≤(K:ℝ)*W)
    (f : ι → E) :
    (∑ p∈(Finset.Icc (-(K:ℤ)) K) ×ˢ (Finset.Icc (-(K:ℤ)) K),
      ∑ q∈spatialTreePiece S x y a b L W p, f q)=∑ q∈S, f q := by
  exact Finset.sum_fiberwise_of_maps_to
    (fun q hq => spatialPacketCell_mem x y a b L W hL hW K q (hx q hq) (hy q hq)) f

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSpatialTree
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary tree estimate for an actual selected packet set. Local
angular multiplicity supplies the row count; empty ambient rows disappear. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData

theorem exists_spatial_selected_tree_estimate (hL : LepingleInput)
    (cStar cEta CEta cb Cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 ≤ cb) (hCb : 0≤Cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (M R K D : ℕ),
      Cb≤R → 207≤P.order → ∀ (Q A : Finset P.PacketIndex), Q⊆A →
      ∀ (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (t a b w tau radius Lip eta sigma : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ),
      0<w → ∀ (F : ℝ), 0≤F → Cb*w≤P.width →
      (∀ k, |P.frequency k|≤F/w) → P.topLength≤tau → 0≤Lip → 0≤eta → 0 ≤ sigma →
      1 ≤ radius+Cb → radius+Cb≤(2:ℝ)^K →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => P.rowSlope j l) (w/P.length j) M) →
      (∀ q∈Q, |P.actualX q.1 q.2.1 q.2.2-a|≤(D:ℝ)*P.topLength) →
      (∀ q∈Q, |P.actualZ q.1 q.2.1 q.2.2-t*P.actualX q.1 q.2.1 q.2.2-b|≤(D:ℝ)*P.width) →
      (∀ q∈Q, t∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈Q, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈Q, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |ξ+P.rowSlope q.1 q.2.1*η| ≤ cStar/P.length q.1 ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ q∈Q, |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1) →
      (∀ q∈Q, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |η-P.frequency k|≤Cv/P.width) →
      (∀ q∈Q, ‖c q.1 q.2.1 q.2.2‖ ≤ sigma) →
      (∀ U : SlopeBox, U.width=P.width → U.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c A U ≤ sigma^2*U.area) →
    ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (selector j l k)) →
      (∀ j l k s, ‖selector j l k s‖≤1) →
      (∀ q∈Q, ∀ k, selector q.1 q.2.1 k t≠0 → cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 → |s-P.rowSlope j l| ≤ radius*(w/P.length j)) →
      (∀ j l k s, |s-t|≤w/P.length j →
        ‖selector j l k s-selector j l k t‖≤Lip*(|s-t|/(w/P.length j))) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∀ q∈Q, P.ordinaryDensity 0 cell grid w tau E u q≤eta) →
      let F := fun z => ∑ q∈Q, WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
        selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
      IntegrableOn F E (volume.prod volume) ∧
        (∫ z in E, ‖F z‖ ∂volume.prod volume)≤
          (((2*D+1)^2:ℕ):ℝ)*(P.referenceTreeConstant C ((2*R+1)*M) K Lip*
            sigma*eta*P.topLength*P.width) := by
  obtain ⟨C,hC,hTree⟩ := exists_recentered_selected_tree_estimate hL
    cStar cEta CEta cb Cb Cv hcStar hcEta hCEta hCv hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M R K D hR horder Q A hQA c t a b w tau radius Lip eta sigma cell grid
    hw F hF hwideW hfreq htime hLip heta hsigma hwide hK hlocal hX hY href hangle hspectrum hslope hbin hc hsize
    selector hsel hselbound hselaway hselsupport hselradius hselnear E hE u hu hdensity
  classical
  let X := fun q : P.PacketIndex => P.actualX q.1 q.2.1 q.2.2
  let Y := fun q : P.PacketIndex => P.actualZ q.1 q.2.1 q.2.2-t*P.actualX q.1 q.2.1 q.2.2
  let cells := (Finset.Icc (-(D:ℤ)) D) ×ˢ (Finset.Icc (-(D:ℤ)) D)
  let part := fun p => spatialTreePiece Q X Y a b P.topLength P.width p
  let V := fun (q : P.PacketIndex) (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
    selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
  let B := P.referenceTreeConstant C ((2*R+1)*M) K Lip*sigma*eta*P.topLength*P.width
  have hCtree : 0≤P.referenceTreeConstant C ((2*R+1)*M) K Lip := by
    have ht := transverseTailConstant_nonneg
    have hp := P.profileBound_pos
    dsimp [referenceTreeConstant,referenceEnvelopeConstant]
    positivity
  have hB : 0≤B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCtree hsigma) heta)
      P.topLength_pos.le) P.width_pos.le
  have hp (p : ℤ×ℤ) :
      IntegrableOn (fun z => ∑ q∈part p, V q z) E (volume.prod volume) ∧
      (∫ z in E, ‖∑ q∈part p, V q z‖ ∂volume.prod volume)≤B := by
    have hsub : part p⊆Q := Finset.filter_subset _ _
    by_cases hn : (part p).Nonempty
    · have hcenter := fun q hq => spatialTreePiece_centers Q X Y a b P.topLength P.width
        P.topLength_pos P.width_pos p q hq
      have henergy := P.reference_piece_size_bound (part p) A (hsub.trans hQA)
        t (spatialCellCenter a P.topLength p.1) (spatialCellCenter b P.width p.2)
        w cb tau sigma cell grid c htime (fun q hq => (hcenter q hq).1)
        (fun q hq => (hcenter q hq).2) (fun q hq => href q (hsub hq)) hsize
      exact hTree N κ Label Item P M R K hR horder (part p) hn c t
        (spatialCellCenter a P.topLength p.1) (spatialCellCenter b P.width p.2)
        w tau radius Lip eta sigma cell grid hw F hF hwideW hfreq htime hLip heta hsigma
        hwide hK hlocal (fun q hq => (hcenter q hq).1) (fun q hq => (hcenter q hq).2)
        (fun q hq => href q (hsub hq)) (fun q hq => hangle q (hsub hq))
        (fun q hq => hspectrum q (hsub hq)) (fun q hq => hslope q (hsub hq))
        (fun q hq => hbin q (hsub hq)) (fun q hq => hc q (hsub hq)) henergy
        selector hsel hselbound (fun q hq => hselaway q (hsub hq)) hselsupport hselradius
        hselnear E hE u hu (fun q hq => hdensity q (hsub hq))
    · have he : part p=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      simp only [he,Finset.sum_empty,norm_zero,integral_zero]
      exact ⟨integrableOn_zero,hB⟩
  have heval (z : ℝ×ℝ) : (∑ p∈cells, ∑ q∈part p, V q z)=∑ q∈Q, V q z :=
    sum_spatialTreePieces Q X Y a b P.topLength P.width P.topLength_pos P.width_pos D hX hY (fun q => V q z)
  have hI := integrable_finsetSum cells (fun p _ => (hp p).1)
  refine ⟨?_,?_⟩
  · change IntegrableOn (fun z => ∑ q∈Q, V q z) E (volume.prod volume)
    have he : (fun z => ∑ p∈cells, ∑ q∈part p, V q z)=(fun z => ∑ q∈Q, V q z) := funext heval
    rw [he] at hI
    exact hI
  · calc
      _ = ∫ z in E, ‖∑ p∈cells, ∑ q∈part p, V q z‖ ∂volume.prod volume := by
        change (∫ z in E, ‖∑ q∈Q, V q z‖ ∂volume.prod volume)=_
        simp only [heval]
      _ ≤ ∫ z in E, ∑ p∈cells, ‖∑ q∈part p, V q z‖ ∂volume.prod volume :=
        integral_mono hI.norm (integrable_finsetSum cells (fun p _ => (hp p).1.norm))
          (fun z => norm_sum_le _ _)
      _ = ∑ p∈cells, ∫ z in E, ‖∑ q∈part p, V q z‖ ∂volume.prod volume :=
        integral_finsetSum _ (fun p _ => (hp p).1.norm)
      _ ≤ ∑ _p∈cells, B := Finset.sum_le_sum (fun p _ => (hp p).2)
      _ = _ := by
        rw [Finset.sum_const,nsmul_eq_mul]
        rw [show cells.card=(2*D+1)^2 from spatialCell_count D]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataRootedTree
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary tree estimate for an actual selected packet set. Local
angular multiplicity supplies the row count; empty ambient rows disappear. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData

theorem exists_rooted_selected_tree_estimate (hL : LepingleInput)
    (cStar cEta CEta cb Cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 ≤ cb) (hCb : 0≤Cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (M R K D : ℕ),
      Cb≤R → 207≤P.order → ∀ (Q A : Finset P.PacketIndex), Q⊆A → Q.Nonempty →
      ∀ (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (L t a b w tau radius Lip eta sigma : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ),
      0<w → ∀ (F : ℝ), 0≤F → Cb*w≤P.width →
      (∀ k, |P.frequency k|≤F/w) → L≤P.topLength → L≤tau →
      (∀ q∈Q, P.length q.1≤L) → 0≤Lip → 0≤eta → 0 ≤ sigma →
      1 ≤ radius+Cb → radius+Cb≤(2:ℝ)^K →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => P.rowSlope j l) (w/P.length j) M) →
      (∀ q∈Q, |P.actualX q.1 q.2.1 q.2.2-a|≤(D:ℝ)*L) →
      (∀ q∈Q, |P.actualZ q.1 q.2.1 q.2.2-t*P.actualX q.1 q.2.1 q.2.2-b|≤(D:ℝ)*P.width) →
      (∀ q∈Q, t∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈Q, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈Q, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |ξ+P.rowSlope q.1 q.2.1*η| ≤ cStar/P.length q.1 ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ q∈Q, |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1) →
      (∀ q∈Q, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |η-P.frequency k|≤Cv/P.width) →
      (∀ q∈Q, ‖c q.1 q.2.1 q.2.2‖ ≤ sigma) →
      (∀ U : SlopeBox, U.width=P.width → U.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c A U ≤ sigma^2*U.area) →
    ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (selector j l k)) →
      (∀ j l k s, ‖selector j l k s‖≤1) →
      (∀ q∈Q, ∀ k, selector q.1 q.2.1 k t≠0 → cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 → |s-P.rowSlope j l| ≤ radius*(w/P.length j)) →
      (∀ j l k s, |s-t|≤w/P.length j →
        ‖selector j l k s-selector j l k t‖≤Lip*(|s-t|/(w/P.length j))) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∀ q∈Q, P.ordinaryDensity 0 cell grid w tau E u q≤eta) →
      let F := fun z => ∑ q∈Q, WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
        selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
      IntegrableOn F E (volume.prod volume) ∧
        (∫ z in E, ‖F z‖ ∂volume.prod volume)≤
          (((4*D+1)^2:ℕ):ℝ)*(P.referenceTreeConstant C ((2*R+1)*M) K Lip*
            sigma*eta*L*P.width) := by
  obtain ⟨C,hC,hTree⟩ := exists_spatial_selected_tree_estimate hL
    cStar cEta CEta cb Cb Cv hcStar hcEta hCEta hCv hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M R K D hR horder Q A hQA hQ c L t a b w tau radius Lip eta sigma cell grid
    hw F hF hwideW hfreq hLtop htime hlength hLip heta hsigma hwide hK hlocal hX hY href hangle hspectrum hslope hbin hc hsize
    selector hsel hselbound hselaway hselsupport hselradius hselnear E hE u hu hdensity
  classical
  obtain ⟨q0,hq0⟩ := hQ
  obtain ⟨first,hfirst,hcomp,hmin⟩ := P.exists_enclosing_scale L hLtop ⟨q0.1,hlength q0 hq0⟩
  let S := P.dropScales first
  let Qs := P.dropPackets first Q
  let As := P.dropPackets first A
  let d := fun j l v => c (dropIndex first j) l v
  let beta := fun j l k s => selector (dropIndex first j) l k s
  let cells := fun j l => cell (dropIndex first j) l
  let grid' := (((first.val:ℤ).negOnePow : ℤ)*grid)
  have hlevel (q : P.PacketIndex) (hq : q∈Q) : first.val≤q.1.val := hmin q.1 (hlength q hq)
  have hQs : Qs.Nonempty := P.dropPackets_nonempty first Q ⟨q0,hq0⟩ hlevel
  have hsub : Qs⊆As := P.dropPackets_mono first hQA
  have hmem (q : S.PacketIndex) (hq : q∈Qs) : P.dropPacket first q∈Q :=
    (P.mem_dropPackets first Q q).mp hq
  have hlocalS (j : Fin (N-first.val)) : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : S.labels j => S.rowSlope j l) (w/S.length j) M := by
    change SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels (dropIndex first j) => P.rowSlope (dropIndex first j) l)
      (w/(P.dropScales first).length j) M
    rw [P.dropScales_length]
    exact hlocal (dropIndex first j)
  have hXS (q : S.PacketIndex) (hq : q∈Qs) :
      |S.actualX q.1 q.2.1 q.2.2-a|≤(2*D:ℕ)*S.topLength := by
    have hh := hX (P.dropPacket first q) (hmem q hq)
    have he : S.actualX q.1 q.2.1 q.2.2=P.actualX (P.dropPacket first q).1
        (P.dropPacket first q).2.1 (P.dropPacket first q).2.2 := P.dropScales_actualX first q.1 q.2.1 q.2.2
    rw [he]
    apply hh.trans
    change (D:ℝ)*L≤(2*D:ℕ)*P.length first
    push_cast
    nlinarith [(Nat.cast_nonneg D : (0:ℝ)≤D)]
  have hYS (q : S.PacketIndex) (hq : q∈Qs) :
      |S.actualZ q.1 q.2.1 q.2.2-t*S.actualX q.1 q.2.1 q.2.2-b|≤(2*D:ℕ)*S.width := by
    have hh := hY (P.dropPacket first q) (hmem q hq)
    have hx : S.actualX q.1 q.2.1 q.2.2=P.actualX (P.dropPacket first q).1
        (P.dropPacket first q).2.1 (P.dropPacket first q).2.2 := P.dropScales_actualX first q.1 q.2.1 q.2.2
    have hy : S.actualZ q.1 q.2.1 q.2.2=P.actualZ (P.dropPacket first q).1
        (P.dropPacket first q).2.1 (P.dropPacket first q).2.2 := P.dropScales_actualZ first q.1 q.2.1 q.2.2
    rw [hx,hy]
    apply hh.trans
    change (D:ℝ)*P.width≤(2*D:ℕ)*P.width
    apply mul_le_mul_of_nonneg_right _ P.width_pos.le
    push_cast
    linarith [(Nat.cast_nonneg D : (0:ℝ)≤D)]
  have hRef (q : S.PacketIndex) (hq : q∈Qs) :
      t∈scaledAngularCell (w/S.topLength) grid' q.1.val (cells q.1 q.2.1) := by
    rw [P.dropScales_angularCell first w hw]
    exact href (P.dropPacket first q) (hmem q hq)
  have hAngle (q : S.PacketIndex) (hq : q∈Qs) :
      S.rowSlope q.1 q.2.1∈scaledAngularCell (w/S.topLength) grid' q.1.val (cells q.1 q.2.1) := by
    rw [P.dropScales_angularCell first w hw]
    exact hangle (P.dropPacket first q) (hmem q hq)
  have hSpec (q : S.PacketIndex) (hq : q∈Qs) (k : κ) (xi eta : ℝ)
      (hn : planarAngularFourier (S.physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,eta)≠0) :
      |xi+S.rowSlope q.1 q.2.1*eta| ≤ cStar/S.length q.1 ∧ cEta≤w*eta ∧ w*eta≤CEta := by
    rw [P.dropScales_physicalPacket] at hn
    change |xi+P.rowSlope (dropIndex first q.1) q.2.1*eta|≤
      cStar/(P.dropScales first).length q.1 ∧ cEta≤w*eta ∧ w*eta≤CEta
    rw [P.dropScales_length]
    exact hspectrum (P.dropPacket first q) (hmem q hq) k xi eta hn
  have hBin (q : S.PacketIndex) (hq : q∈Qs) (k : κ) (xi eta : ℝ)
      (hn : planarAngularFourier (S.physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,eta)≠0) :
      |eta-S.frequency k|≤Cv/S.width := by
    rw [P.dropScales_physicalPacket] at hn
    exact hbin (P.dropPacket first q) (hmem q hq) k xi eta hn
  have hSize (U : SlopeBox) (hU : U.width=S.width) (hUt : U.length≤tau) :
      S.unsignedSizeTestEnergy w cb cells grid' d As U ≤ sigma^2*U.area :=
    (P.dropScales_unsignedSizeTestEnergy_le first A w cb hw cell grid c U).trans (hsize U hU hUt)
  have hDensity (q : S.PacketIndex) (hq : q∈Qs) : S.ordinaryDensity 0 cells grid' w tau E u q≤eta := by
    rcases q with ⟨j,l,v⟩
    exact (P.dropScales_ordinaryDensity first 0 w tau hw cell grid E u j l v).le.trans
      (hdensity ⟨dropIndex first j,⟨l,v⟩⟩ (hmem ⟨j,⟨l,v⟩⟩ hq))
  have hSlope (q : S.PacketIndex) (hq : q∈Qs) : |S.rowSlope q.1 q.2.1-t|≤Cb*w/S.length q.1 := by
    change |P.rowSlope (dropIndex first q.1) q.2.1-t|≤Cb*w/(P.dropScales first).length q.1
    rw [P.dropScales_length]
    exact hslope (P.dropPacket first q) (hmem q hq)
  have hAway (q : S.PacketIndex) (hq : q∈Qs) (k : κ) (hk : beta q.1 q.2.1 k t≠0) :
      cb*w/S.length q.1≤|S.rowSlope q.1 q.2.1-t| := by
    change cb*w/(P.dropScales first).length q.1≤|P.rowSlope (dropIndex first q.1) q.2.1-t|
    rw [P.dropScales_length]
    exact hselaway (P.dropPacket first q) (hmem q hq) k hk
  have hRadius (j : Fin (N-first.val)) (l : S.labels j) (k : κ) (s : ℝ) (hs : beta j l k s≠0) :
      |s-S.rowSlope j l| ≤ radius*(w/S.length j) := by
    change |s-P.rowSlope (dropIndex first j) l| ≤ radius*(w/(P.dropScales first).length j)
    rw [P.dropScales_length]
    exact hselradius (dropIndex first j) l k s hs
  have hNear (j : Fin (N-first.val)) (l : S.labels j) (k : κ) (s : ℝ)
      (hs : |s-t|≤w/S.length j) :
      ‖beta j l k s-beta j l k t‖≤Lip*(|s-t|/(w/S.length j)) := by
    have he : S.length j=P.length (dropIndex first j) := P.dropScales_length first j
    rw [he] at hs ⊢
    exact hselnear (dropIndex first j) l k s hs
  have h := hTree (N-first.val) κ (fun j => Label (dropIndex first j))
    (fun j l => Item (dropIndex first j) l) S M R K (2*D) hR horder Qs As hsub d t a b
    w tau radius Lip eta sigma cells grid' hw F hF hwideW hfreq (hfirst.trans htime) hLip heta hsigma
    hwide hK hlocalS hXS hYS hRef hAngle hSpec hSlope
    hBin (fun q hq => hc (P.dropPacket first q) (hmem q hq)) hSize beta
    (fun j l k => hsel (dropIndex first j) l k)
    (fun j l k s => hselbound (dropIndex first j) l k s) hAway
    (fun j l k s hs => by
      rw [P.dropScales_angularCell first w hw]
      exact hselsupport (dropIndex first j) l k s hs)
    hRadius hNear E hE u hu hDensity
  have heval (z : ℝ×ℝ) := P.dropPackets_selector_value first Q hlevel 0 c
    (fun j l k => selector j l k (u z)) z
  dsimp only [S,Qs,d,beta] at h
  dsimp only
  change IntegrableOn _ E _ ∧ _ at h
  simp only [heval,P.dropScales_treeConstant] at h
  refine ⟨h.1,h.2.trans ?_⟩
  have hCt : 0≤P.referenceTreeConstant C ((2*R+1)*M) K Lip := by
    have ht := transverseTailConstant_nonneg
    have hp := P.profileBound_pos
    dsimp [referenceTreeConstant,referenceEnvelopeConstant]
    positivity
  have hwP := P.width_pos
  have hfac : 0≤(((4*D+1)^2:ℕ):ℝ)*
      (P.referenceTreeConstant C ((2*R+1)*M) K Lip*sigma*eta*P.width) := by positivity
  have hecount : 2*(2*D)+1=4*D+1 := by omega
  rw [hecount]
  change (((4*D+1)^2:ℕ):ℝ)*(P.referenceTreeConstant C ((2*R+1)*M) K Lip*
    sigma*eta*P.length first*P.width)≤_
  calc
    _ = ((((4*D+1)^2:ℕ):ℝ)*(P.referenceTreeConstant C ((2*R+1)*M) K Lip*
        sigma*eta*P.width))*P.length first := by ring
    _ ≤ ((((4*D+1)^2:ℕ):ℝ)*(P.referenceTreeConstant C ((2*R+1)*M) K Lip*
        sigma*eta*P.width))*L := mul_le_mul_of_nonneg_left hfirst hfac
    _ = _ := by ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataTopReferenceGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A selected top supplies the exact reference-cone and center bounds
for the ordinary tree estimate. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem selected_top_cone (w : ℝ) (hw : 0<w)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (q : P.PacketIndex) (T : SlopeBox)
    (_hlen : P.length q.1≤T.length)
    (hrow : P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (htop : T.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) :
    |P.rowSlope q.1 q.2.1-T.slope|≤w/P.length q.1 := by
  have hs := scaledAngularCell_slope (div_pos hw P.topLength_pos)
    (le_refl (q.1.val:ℤ)) ⟨P.rowSlope q.1 q.2.1,hrow,hrow⟩ hrow htop
  have heq : (w/P.topLength)*DyadicLineGrid.scale (q.1.val:ℤ) = w/P.length q.1 := by
    simp only [DyadicLineGrid.scale,zpow_natCast,PacketLatticeData.length]
    field_simp [P.topLength_pos.ne',ne_of_gt (pow_pos (by norm_num : (0:ℝ)<2) q.1.val)]
  rw [heq] at hs
  exact hs

theorem selected_top_centers (T : SlopeBox) (A : ℝ) (q : P.PacketIndex)
    (hwidth : T.width=P.width)
    (hcenter : (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T A) :
    |P.actualX q.1 q.2.1 q.2.2-T.x|≤A*T.length ∧
    |P.actualZ q.1 q.2.1 q.2.2-T.slope*P.actualX q.1 q.2.1 q.2.2-
      (T.y-T.slope*T.x)|≤A*P.width := by
  change |P.actualX q.1 q.2.1 q.2.2-T.x|≤A*T.length ∧
    |(P.actualZ q.1 q.2.1 q.2.2-T.y)-T.slope*(P.actualX q.1 q.2.1 q.2.2-T.x)|≤A*T.width at hcenter
  refine ⟨hcenter.1,?_⟩
  rw [hwidth] at hcenter
  convert hcenter.2 using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataTopEstimate
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary tree estimate for an actual selected packet set. Local
angular multiplicity supplies the row count; empty ambient rows disappear. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData

theorem exists_selected_top_estimate (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 ≤ cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (M R K D : ℕ),
      (1:ℝ)≤R → 207≤P.order → ∀ (Q A : Finset P.PacketIndex), Q⊆A → Q.Nonempty →
      ∀ (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (T : SlopeBox) (dilation w tau radius Lip eta sigma : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ),
      T.width=P.width → dilation≤D → 0<w → ∀ (F : ℝ), 0≤F → w≤P.width →
      (∀ k, |P.frequency k|≤F/w) → T.length≤P.topLength → T.length≤tau →
      (∀ q∈Q, P.length q.1≤T.length) → 0≤Lip → 0≤eta → 0 ≤ sigma →
      1 ≤ radius+1 → radius+1≤(2:ℝ)^K →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => P.rowSlope j l) (w/P.length j) M) →
      (∀ q∈Q, (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T dilation) →
      (∀ q∈Q, T.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈Q, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈Q, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |ξ+P.rowSlope q.1 q.2.1*η| ≤ cStar/P.length q.1 ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ q∈Q, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |η-P.frequency k|≤Cv/P.width) →
      (∀ q∈Q, ‖c q.1 q.2.1 q.2.2‖ ≤ sigma) →
      (∀ U : SlopeBox, U.width=P.width → U.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c A U ≤ sigma^2*U.area) →
    ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (selector j l k)) →
      (∀ j l k s, ‖selector j l k s‖≤1) →
      (∀ q∈Q, ∀ k, selector q.1 q.2.1 k T.slope≠0 → cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-T.slope|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 → |s-P.rowSlope j l| ≤ radius*(w/P.length j)) →
      (∀ j l k s, |s-T.slope|≤w/P.length j →
        ‖selector j l k s-selector j l k T.slope‖≤Lip*(|s-T.slope|/(w/P.length j))) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∀ q∈Q, P.ordinaryDensity 0 cell grid w tau E u q≤eta) →
      let F := fun z => ∑ q∈Q, WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
        selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
      IntegrableOn F E (volume.prod volume) ∧
        (∫ z in E, ‖F z‖ ∂volume.prod volume)≤
          (((4*D+1)^2:ℕ):ℝ)*(P.referenceTreeConstant C ((2*R+1)*M) K Lip*
            sigma*eta*T.area) := by
  obtain ⟨C,hC,hTree⟩ := exists_rooted_selected_tree_estimate hL
    cStar cEta CEta cb 1 Cv hcStar hcEta hCEta hCv hcb (by norm_num) hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M R K D hR horder Q A hQA hQ c T dilation w tau radius Lip eta sigma cell grid
    hwidth hdilation hw F hF hwideW hfreq hLtop htime hlength hLip heta hsigma hwide hK hlocal hcenter href hangle hspectrum hbin hc hsize
    selector hsel hselbound hselaway hselsupport hselradius hselnear E hE u hu hdensity
  have hX (q : P.PacketIndex) (hq : q∈Q) :
      |P.actualX q.1 q.2.1 q.2.2-T.x|≤(D:ℝ)*T.length :=
    (P.selected_top_centers T dilation q hwidth (hcenter q hq)).1.trans
      (mul_le_mul_of_nonneg_right hdilation T.length_pos.le)
  have hY (q : P.PacketIndex) (hq : q∈Q) :
      |P.actualZ q.1 q.2.1 q.2.2-T.slope*P.actualX q.1 q.2.1 q.2.2-
        (T.y-T.slope*T.x)|≤(D:ℝ)*P.width :=
    (P.selected_top_centers T dilation q hwidth (hcenter q hq)).2.trans
      (mul_le_mul_of_nonneg_right hdilation P.width_pos.le)
  have hcone (q : P.PacketIndex) (hq : q∈Q) :
      |P.rowSlope q.1 q.2.1-T.slope|≤1*w/P.length q.1 := by
    simpa only [one_mul] using P.selected_top_cone w hw cell grid q T (hlength q hq)
      (hangle q hq) (href q hq)
  have h := hTree N κ Label Item P M R K D hR horder Q A hQA hQ c
    T.length T.slope T.x (T.y-T.slope*T.x) w tau radius Lip eta sigma cell grid hw F hF
    (by simpa only [one_mul] using hwideW) hfreq hLtop htime hlength hLip heta hsigma
    hwide hK hlocal hX hY href hangle hspectrum hcone hbin hc hsize
    selector hsel hselbound hselaway hselsupport hselradius hselnear E hE u hu hdensity
  refine ⟨h.1,h.2.trans_eq ?_⟩
  rw [SlopeBox.area,hwidth]
  ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceAssignedPacketSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact grouping by an assignment defined only on the selected packets. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem assignedPacketSet_subset {ι J : Type*} (S : Finset ι) (assigned : S → J) (j : J) :
    assignedPacketSet S assigned j ⊆ S := Finset.filter_subset _ _

theorem mem_assignedPacketSet {ι J : Type*} (S : Finset ι) (assigned : S → J)
    (j : J) (q : ι) (hq : q∈assignedPacketSet S assigned j) :
    ∃ hqS : q∈S, assigned ⟨q,hqS⟩=j := (Finset.mem_filter.mp hq).2

theorem sum_assignedPacketSets {ι J V : Type*} [Fintype J] [AddCommMonoid V]
    (S : Finset ι) (assigned : S → J) (F : ι → V) :
    (∑ j, ∑ q∈assignedPacketSet S assigned j, F q)=∑ q∈S, F q := by
  classical
  simp only [assignedPacketSet,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  have hpred (j : J) : (∃ h : q∈S, assigned ⟨q,h⟩=j) ↔ assigned ⟨q,hq⟩=j := by
    constructor
    · rintro ⟨h,he⟩
      exact he
    · intro he
      exact ⟨hq,he⟩
  simp only [hpred]
  simp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDensityForestIntegral
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrate all trees in the actual sharp density forest. Coefficients
are controlled by the original size tests, and the forest area is supplied
by disjoint witnesses rather than by an additional analytic assumption. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData

theorem exists_density_forest_integral (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 ≤ cb) (hcbQuarter : cb≤1/4)
    (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (M R K D : ℕ),
      (1:ℝ)≤R → 207≤P.order →
    ∀ (packets initial : Finset P.PacketIndex), packets⊆initial →
    ∀ (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (w tau eta density sigma radius Lip F : ℝ)
      (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ)
      (forest : OrdinaryDensityForest P packets cell grid w tau eta E u),
      5*densityRadius eta≤D → 0<w → w≤P.width → 0≤F →
      (∀ k, |P.frequency k|≤F/w) → tau≤P.topLength →
      0≤Lip → 0≤density → 0 ≤ sigma → 1 ≤ radius+1 → radius+1≤(2:ℝ)^K →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => P.rowSlope j l) (w/P.length j) M) →
      (∀ q∈packets, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈packets, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |ξ+P.rowSlope q.1 q.2.1*η| ≤ cStar/P.length q.1 ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ q∈packets, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |η-P.frequency k|≤Cv/P.width) →
      (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c initial T ≤ sigma^2*T.area) →
    ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (selector j l k)) →
      (∀ j l k s, ‖selector j l k s‖≤1) →
      (∀ i, ∀ q∈assignedPacketSet packets forest.assigned i, ∀ k,
        selector q.1 q.2.1 k (forest.top i).slope≠0 →
          cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-(forest.top i).slope|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 → |s-P.rowSlope j l| ≤ radius*(w/P.length j)) →
      (∀ i, ∀ j l k s, |s-(forest.top i).slope|≤w/P.length j →
        ‖selector j l k s-selector j l k (forest.top i).slope‖≤
          Lip*(|s-(forest.top i).slope|/(w/P.length j))) →
      MeasurableSet E → Measurable u →
      (∀ q∈packets, P.ordinaryDensity 0 cell grid w tau E u q≤density) →
      let V := fun q (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
        selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
      IntegrableOn (fun z => ∑ q∈packets, V q z) E (volume.prod volume) ∧
        (∫ z in E, ‖∑ q∈packets, V q z‖ ∂volume.prod volume)≤
          ((((4*D+1)^2:ℕ):ℝ)*P.referenceTreeConstant C ((2*R+1)*M) K Lip*sigma*density)*
            (2*(volume.prod volume).real E/eta) := by
  obtain ⟨C,hC,hTree⟩ := exists_selected_top_estimate hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M R K D hR horder packets initial hsub c cell grid
    w tau eta density sigma radius Lip F E u forest hD hw hW hF hfreq htime
    hLip hdensity hsigma hwide hK hlocal hrow hspectrum hbin hsize
    selector hsel hbound haway hsupport hradius hnear hE hu hden
  classical
  let part := assignedPacketSet packets forest.assigned
  let V := fun (q : P.PacketIndex) (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
    selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
  let B := (((4*D+1)^2:ℕ):ℝ)*P.referenceTreeConstant C ((2*R+1)*M) K Lip*sigma*density
  have hCtree : 0≤P.referenceTreeConstant C ((2*R+1)*M) K Lip := by
    have ht := transverseTailConstant_nonneg
    have hp := P.profileBound_pos
    dsimp [referenceTreeConstant,referenceEnvelopeConstant]
    positivity
  have hB : 0≤B := by dsimp only [B]; positivity
  have hpart (i : forest.keepers) :
      IntegrableOn (fun z => ∑ q∈part i, V q z) E (volume.prod volume) ∧
      (∫ z in E, ‖∑ q∈part i, V q z‖ ∂volume.prod volume)≤B*(forest.top i).area := by
    have hsubset : part i⊆packets := assignedPacketSet_subset _ _ _
    have hgeom (q : P.PacketIndex) (hq : q∈part i) :
        P.length q.1≤(forest.top i).length ∧
        (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈
          densitySpatialBox (forest.top i) (5*densityRadius eta) ∧
        (forest.top i).slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1) := by
      obtain ⟨hqp,ha⟩ := mem_assignedPacketSet packets forest.assigned i q hq
      simpa only [ha] using
        And.intro (forest.length_le ⟨q,hqp⟩) (And.intro (forest.center ⟨q,hqp⟩) (forest.direction ⟨q,hqp⟩))
    by_cases hn : (part i).Nonempty
    · have h := hTree N κ Label Item P M R K D hR horder (part i) initial
        (hsubset.trans hsub) hn c (forest.top i) (5*densityRadius eta)
        w tau radius Lip density sigma cell grid (forest.width i) hD hw F hF hW hfreq
        ((forest.short i).trans htime) (forest.short i) (fun q hq => (hgeom q hq).1)
        hLip hdensity hsigma hwide hK hlocal
        (fun q hq => (hgeom q hq).2.1) (fun q hq => (hgeom q hq).2.2)
        (fun q hq => hrow q (hsubset hq)) (fun q hq => hspectrum q (hsubset hq))
        (fun q hq => hbin q (hsubset hq))
        (fun q hq => P.coefficient_le_of_size_tests w cb tau sigma hw hcbQuarter hsigma
          cell grid c initial hsize q (hsub (hsubset hq)) ((hgeom q hq).1.trans (forest.short i)))
        hsize selector hsel hbound (haway i) hsupport hradius (hnear i) E hE u hu
        (fun q hq => hden q (hsubset hq))
      refine ⟨h.1,h.2.trans_eq ?_⟩
      dsimp only [B]
      ring
    · have he : part i=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      simp only [he,Finset.sum_empty,norm_zero,integral_zero]
      exact ⟨integrableOn_zero,mul_nonneg hB (forest.top i).area_pos.le⟩
  have heval (z : ℝ×ℝ) : (∑ i : forest.keepers, ∑ q∈part i, V q z)=∑ q∈packets, V q z :=
    sum_assignedPacketSets packets forest.assigned (fun q => V q z)
  have hI := integrable_finsetSum Finset.univ (fun i _ => (hpart i).1)
  have hefun : (fun z => ∑ i : forest.keepers, ∑ q∈part i, V q z)=
      fun z => ∑ q∈packets, V q z := funext heval
  refine ⟨?_,?_⟩
  · change IntegrableOn (fun z => ∑ q∈packets, V q z) E (volume.prod volume)
    rw [hefun] at hI
    exact hI
  · change (∫ z in E, ‖∑ q∈packets, V q z‖ ∂volume.prod volume)≤B*(2*(volume.prod volume).real E/eta)
    calc
      _ = ∫ z in E, ‖∑ i : forest.keepers, ∑ q∈part i, V q z‖ ∂volume.prod volume := by
        simp only [heval]
      _ ≤ ∫ z in E, ∑ i : forest.keepers, ‖∑ q∈part i, V q z‖ ∂volume.prod volume :=
        integral_mono hI.norm (integrable_finsetSum Finset.univ (fun i _ => (hpart i).1.norm))
          (fun z => norm_sum_le _ _)
      _ = ∑ i : forest.keepers, ∫ z in E, ‖∑ q∈part i, V q z‖ ∂volume.prod volume :=
        integral_finsetSum _ (fun i _ => (hpart i).1.norm)
      _ ≤ ∑ i : forest.keepers, B*(forest.top i).area :=
        Finset.sum_le_sum (fun i _ => (hpart i).2)
      _ = B*∑ i : forest.keepers, (forest.top i).area := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left forest.area hB

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensitySpatialCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The number of translated ordinary trees in a density keeper has the
small power loss needed for summing the dyadic density thresholds. -/
noncomputable section
namespace LipschitzHilbert

theorem densitySpatialCount_covers (eta : ℝ) :
    5*densityRadius eta≤(densitySpatialCount eta : ℝ) := Nat.le_ceil _

theorem densityRadius_sq_le {eta : ℝ} (heta : 0<eta) :
    (densityRadius eta)^2 ≤ densityRadiusConstant^2*(1+eta^(-(1/20:ℝ))) := by
  let x := eta^(-(1/100:ℝ))
  have hx : 0<x := Real.rpow_pos_of_pos heta _
  have hxsq : x^2=eta^(-(1/50:ℝ)) := by
    dsimp only [x]
    rw [←Real.rpow_natCast,←Real.rpow_mul heta.le]
    norm_num
  have hm : (max 1 x)^2≤1+eta^(-(1/20:ℝ)) := by
    by_cases he : eta≤1
    · have hxone : 1≤x := Real.one_le_rpow_of_pos_of_le_one_of_nonpos heta he (by norm_num)
      rw [max_eq_right hxone,hxsq]
      have h := Real.rpow_le_rpow_of_exponent_ge heta he (by norm_num : -(1/20:ℝ)≤ -(1/50:ℝ))
      linarith
    · have hxone : x≤1 := Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge he) (by norm_num)
      rw [max_eq_left hxone,one_pow]
      linarith [Real.rpow_nonneg heta.le (-(1/20:ℝ))]
  dsimp only [densityRadius]
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left hm (sq_nonneg _)

theorem densitySpatialCost_le {eta : ℝ} (heta : 0<eta) :
    ((((4*densitySpatialCount eta+1)^2 : ℕ) : ℝ)) ≤
      (625*densityRadiusConstant^2)*(1+eta^(-(1/20:ℝ))) := by
  have hK := densityRadius_ge_one eta
  have hceil : (densitySpatialCount eta : ℝ)≤5*densityRadius eta+1 :=
    (Nat.ceil_lt_add_one (by linarith : 0≤5*densityRadius eta)).le
  have hlin : 4*(densitySpatialCount eta : ℝ)+1≤25*densityRadius eta := by linarith
  have hsquare : (4*(densitySpatialCount eta : ℝ)+1)^2≤625*(densityRadius eta)^2 := by
    nlinarith [sq_nonneg (25*densityRadius eta-(4*(densitySpatialCount eta : ℝ)+1))]
  push_cast
  calc
    _ ≤ 625*(densityRadius eta)^2 := hsquare
    _ ≤ 625*(densityRadiusConstant^2*(1+eta^(-(1/20:ℝ)))) :=
      mul_le_mul_of_nonneg_left (densityRadius_sq_le heta) (by norm_num)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDensityRemovalIntegral
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual high-density removal step, with the manuscript's small
power loss and an exact remainder of density at most the new threshold. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_density_removal_integral (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 ≤ cb) (hcbQuarter : cb≤1/4)
    (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (M R K : ℕ),
      (1:ℝ)≤R → 207≤P.order →
    ∀ (initial : Finset P.PacketIndex)
      (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (w tau eta density sigma radius Lip F : ℝ),
      0<eta → 0<w → w≤P.width → 0≤F →
      (∀ k, |P.frequency k|≤F/w) → tau≤P.topLength →
      0≤Lip → 0≤density → 0 ≤ sigma → 1 ≤ radius+1 → radius+1≤(2:ℝ)^K →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => P.rowSlope j l) (w/P.length j) M) →
      (∀ q∈initial, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈initial, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |ξ+P.rowSlope q.1 q.2.1*η| ≤ cStar/P.length q.1 ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ q∈initial, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |η-P.frequency k|≤Cv/P.width) →
      (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c initial T ≤ sigma^2*T.area) →
    ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (selector j l k)) →
      (∀ j l k s, ‖selector j l k s‖≤1) →
      (∀ j l k s, selector j l k s≠0 → cb*w/P.length j≤|P.rowSlope j l-s|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 → |s-P.rowSlope j l| ≤ radius*(w/P.length j)) →
      (∀ j l k s t, |s-t|≤w/P.length j →
        ‖selector j l k s-selector j l k t‖≤Lip*(|s-t|/(w/P.length j))) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → (volume.prod volume) E≠∞ →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∀ q∈initial, P.ordinaryDensity 0 cell grid w tau E u q≤density) →
      let removed := initial.filter (fun q => eta<P.ordinaryDensity 0 cell grid w tau E u q)
      let remaining := initial\removed
      let V := fun q (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
        selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
      remaining⊆initial ∧
      (∀ q∈remaining, P.ordinaryDensity 0 cell grid w tau E u q≤eta) ∧
      IntegrableOn (fun z => (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)) E (volume.prod volume) ∧
      (∫ z in E, ‖(∑ q∈initial, V q z)-(∑ q∈remaining, V q z)‖ ∂volume.prod volume)≤
        (625*densityRadiusConstant^2)*P.referenceTreeConstant C ((2*R+1)*M) K Lip*
          sigma*density*(1+eta^(-(1/20:ℝ)))*(2*(volume.prod volume).real E/eta) := by
  obtain ⟨C,hC,hIntegral⟩ := exists_density_forest_integral hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M R K hR horder initial c cell grid w tau eta density sigma
    radius Lip F heta hw hW hF hfreq htime hLip hdensity hsigma hwide hK hlocal
    hrow hspectrum hbin hsize selector hsel hbound haway hsupport hradius hnear E hE hEfin u hu hden
    removed remaining V
  classical
  have hsub : removed⊆initial := Finset.filter_subset _ _
  have hlarge (q : P.PacketIndex) (hq : q∈removed) :
      eta<P.ordinaryDensity 0 cell grid w tau E u q := (Finset.mem_filter.mp hq).2
  obtain ⟨forest⟩ := P.exists_ordinary_density_forest removed cell grid w tau eta hw hW heta E u hE hEfin hu hlarge
  have h := hIntegral N κ Label Item P M R K (densitySpatialCount eta) hR horder
    removed initial hsub c cell grid w tau eta density sigma radius Lip F E u forest
    (densitySpatialCount_covers eta) hw hW hF hfreq htime hLip hdensity hsigma hwide hK hlocal
    (fun q hq => hrow q (hsub hq)) (fun q hq => hspectrum q (hsub hq))
    (fun q hq => hbin q (hsub hq)) hsize selector hsel hbound
    (fun i q _ k hn => haway q.1 q.2.1 k (forest.top i).slope hn) hsupport hradius
    (fun i j l k s hs => hnear j l k s (forest.top i).slope hs) hE hu
    (fun q hq => hden q (hsub hq))
  have heval (z : ℝ×ℝ) : (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)=∑ q∈removed, V q z := by
    have hs := Finset.sum_sdiff hsub (f:=fun q => V q z)
    change (∑ q∈initial, V q z)-(∑ q∈initial\removed, V q z)=_
    rw [←hs]
    abel
  refine ⟨Finset.sdiff_subset,?_,?_,?_⟩
  · intro q hq
    have hq' := Finset.mem_sdiff.mp hq
    by_contra hn
    exact hq'.2 (Finset.mem_filter.mpr ⟨hq'.1,lt_of_not_ge hn⟩)
  · have hefun := funext heval
    rw [hefun]
    exact h.1
  · simp only [heval]
    apply h.2.trans
    have hTree : 0≤P.referenceTreeConstant C ((2*R+1)*M) K Lip := by
      have ht := transverseTailConstant_nonneg
      have ha := P.referenceEnvelopeConstant_pos
      have hp := P.profileBound_pos
      dsimp [referenceTreeConstant]
      positivity
    have hBudget : 0≤2*(volume.prod volume).real E/eta :=
      div_nonneg (mul_nonneg (by norm_num) measureReal_nonneg) heta.le
    have hcount := mul_le_mul_of_nonneg_right (densitySpatialCost_le heta)
      (mul_nonneg (mul_nonneg (mul_nonneg hTree hsigma) hdensity) hBudget)
    first | (convert hcount using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hcount.trans (le_of_eq (by ring)))

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDeletionForest
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full trees removed by the size-selection loop, including the
nonseparated packets deleted with each recorded top. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem sizeDeletionRecords_tops (w A : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (R : Finset P.PacketIndex) (tops : List SlopeBox) :
    (P.sizeDeletionRecords w A cell grid R tops).map Prod.fst=tops := by
  induction tops generalizing R with
  | nil => rfl
  | cons T tops ih => simp only [sizeDeletionRecords,List.map_cons,ih]

theorem sizeDeletionRecords_subset (w A : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (R : Finset P.PacketIndex) (tops : List SlopeBox) :
    ∀ p∈P.sizeDeletionRecords w A cell grid R tops, p.2⊆R := by
  induction tops generalizing R with
  | nil => simp only [sizeDeletionRecords,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | cons T tops ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Finset.filter_subset _ _
    · exact (ih _ p hp).trans Finset.sdiff_subset

namespace SizeStoppingRun
variable {P} {negative : Bool} {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem deletion_forest_nonempty
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hA : 1/2≤A) :
    ∀ p∈P.sizeDeletionRecords w A cell grid initial tops, p.2.Nonempty := by
  induction h with
  | stop => simp only [sizeDeletionRecords,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | step R T tops remaining hT _ _ ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · obtain ⟨q,hq⟩ := P.failing_size_test_nonempty negative w cb tau sigma cell grid c R T hT
      exact ⟨q,P.sizeTestPackets_subset_delete negative w cb A hA cell grid R T hq⟩
    · exact ih p hp

theorem deletion_forest_geometry
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining) :
    ∀ p∈P.sizeDeletionRecords w A cell grid initial tops,
      p.1.width=P.width ∧ p.1.length≤tau ∧ ∀ q∈p.2,
        P.length q.1≤p.1.length ∧
        (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox p.1 A ∧
        p.1.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1) := by
  induction h with
  | stop => simp only [sizeDeletionRecords,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | step R T tops remaining hT _ _ ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · refine ⟨hT.1,hT.2.1,?_⟩
      intro q hq
      exact (Finset.mem_filter.mp hq).2
    · exact ih p hp

theorem deletion_forest_sum {E : Type*} [AddCommMonoid E]
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (f : P.PacketIndex → E) :
    (∑ q∈initial, f q)=
      ((P.sizeDeletionRecords w A cell grid initial tops).map (fun p => ∑ q∈p.2, f q)).sum+
        ∑ q∈remaining, f q := by
  induction h with
  | stop => simp only [sizeDeletionRecords,List.map_nil,List.sum_nil,zero_add]
  | step R T tops remaining _ _ _ ih =>
    have hd : P.sizeDeletePackets w A cell grid R T⊆R := Finset.filter_subset _ _
    have he := Finset.sum_sdiff (f := f) hd
    change (∑ q∈R, f q)=(∑ q∈P.sizeDeletePackets w A cell grid R T, f q)+
      ((P.sizeDeletionRecords w A cell grid (R\P.sizeDeletePackets w A cell grid R T) tops).map
        (fun p => ∑ q∈p.2, f q)).sum+(∑ q∈remaining, f q)
    rw [←he,ih]
    ac_rfl

theorem deletion_forest_area :
    ((P.sizeDeletionRecords w A cell grid initial tops).map (fun p => p.1.area)).sum=
      (tops.map SlopeBox.area).sum := by
  calc
    _ = (((P.sizeDeletionRecords w A cell grid initial tops).map Prod.fst).map SlopeBox.area).sum := by
      rw [List.map_map]
      rfl
    _ = _ := by rw [P.sizeDeletionRecords_tops]

end SizeStoppingRun

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeForestIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integration of the actual finite forest sums. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem tree_list_integral_bound {ι V : Type*} [NormedAddCommGroup V]
    (r : List ι) (F : ι → ℝ×ℝ → V) (B : ι → ℝ) (E : Set (ℝ×ℝ))
    (h : ∀ i∈r, IntegrableOn (F i) E (volume.prod volume) ∧
      (∫ z in E, ‖F i z‖ ∂volume.prod volume)≤B i) :
    IntegrableOn (fun z => (r.map (fun i => F i z)).sum) E (volume.prod volume) ∧
      (∫ z in E, ‖(r.map (fun i => F i z)).sum‖ ∂volume.prod volume)≤(r.map B).sum := by
  induction r with
  | nil =>
    simp only [List.map_nil,List.sum_nil,norm_zero,integral_zero,le_refl,and_true]
    exact integrableOn_zero
  | cons a r ih =>
    have ha := h a (List.mem_cons_self)
    have hr := ih (fun i hi => h i (List.mem_cons_of_mem a hi))
    simp only [List.map_cons,List.sum_cons]
    refine ⟨ha.1.add hr.1,?_⟩
    calc
      _ ≤ ∫ z in E, ‖F a z‖+‖(r.map (fun i => F i z)).sum‖ ∂volume.prod volume :=
        integral_mono (ha.1.add hr.1).norm (ha.1.norm.add hr.1.norm) (fun z => norm_add_le _ _)
      _ = (∫ z in E, ‖F a z‖ ∂volume.prod volume)+
          (∫ z in E, ‖(r.map (fun i => F i z)).sum‖ ∂volume.prod volume) :=
        integral_add ha.1.norm hr.1.norm
      _ ≤ _ := add_le_add ha.2 hr.2

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDeletionTreeEstimate
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the actual tree estimate to every full deletion tree in one
signed stopping run, and sum with its recorded top-area budget. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData

theorem exists_deletion_forest_integral (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 ≤ cb) (hcbquarter : cb≤1/4) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (M R K D : ℕ),
      (1:ℝ)≤R → 207≤P.order →
    ∀ (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (w tau radius Lip eta sigma F dilation threshold epsilon : ℝ)
      (negative : Bool) (initial remaining : Finset P.PacketIndex) (tops : List SlopeBox),
      P.SizeStoppingRun negative w cb tau threshold epsilon dilation cell grid c initial tops remaining →
      1/2≤dilation → dilation≤D → 0<w → 0≤F → w≤P.width →
      (∀ k, |P.frequency k|≤F/w) → tau≤P.topLength →
      0≤Lip → 0≤eta → 0 ≤ sigma → 1 ≤ radius+1 → radius+1≤(2:ℝ)^K →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => P.rowSlope j l) (w/P.length j) M) →
      (∀ q∈initial, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈initial, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |ξ+P.rowSlope q.1 q.2.1*η| ≤ cStar/P.length q.1 ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ q∈initial, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |η-P.frequency k|≤Cv/P.width) →
      (∀ U : SlopeBox, U.width=P.width → U.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c initial U ≤ sigma^2*U.area) →
    ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (selector j l k)) →
      (∀ j l k s, ‖selector j l k s‖≤1) →
      (∀ p∈P.sizeDeletionRecords w dilation cell grid initial tops, ∀ q∈p.2, ∀ k,
        selector q.1 q.2.1 k p.1.slope≠0 → cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-p.1.slope|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 → |s-P.rowSlope j l| ≤ radius*(w/P.length j)) →
      (∀ p∈P.sizeDeletionRecords w dilation cell grid initial tops, ∀ j l k s,
        |s-p.1.slope|≤w/P.length j →
        ‖selector j l k s-selector j l k p.1.slope‖≤Lip*(|s-p.1.slope|/(w/P.length j))) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∀ q∈initial, P.ordinaryDensity 0 cell grid w tau E u q≤eta) →
      let V := fun q (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
        selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
      let H := fun z => (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)
      IntegrableOn H E (volume.prod volume) ∧
        (∫ z in E, ‖H z‖ ∂volume.prod volume)≤
          (((4*D+1)^2:ℕ):ℝ)*P.referenceTreeConstant C ((2*R+1)*M) K Lip*
            sigma*eta*(tops.map SlopeBox.area).sum := by
  obtain ⟨C,hC,hTree⟩ := exists_selected_top_estimate hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M R K D hR horder c cell grid w tau radius Lip eta sigma F
    dilation threshold epsilon negative initial remaining tops hRun hDil hD hw hF hwW hfreq htime
    hLip heta hsigma hwide hK hlocal hrow hspectrum hbin hsize selector hsel hselbound haway
    hsupport hradius hnear E hE u hu hdensity
  let forest := P.sizeDeletionRecords w dilation cell grid initial tops
  let V := fun (q : P.PacketIndex) (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
    selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
  let B := (((4*D+1)^2:ℕ):ℝ)*P.referenceTreeConstant C ((2*R+1)*M) K Lip*sigma*eta
  have hp (p : SlopeBox × Finset P.PacketIndex) (hp : p∈forest) :
      IntegrableOn (fun z => ∑ q∈p.2, V q z) E (volume.prod volume) ∧
      (∫ z in E, ‖∑ q∈p.2, V q z‖ ∂volume.prod volume)≤B*p.1.area := by
    have hsub := P.sizeDeletionRecords_subset w dilation cell grid initial tops p hp
    obtain ⟨hwidth,hpt,hgeom⟩ := hRun.deletion_forest_geometry p hp
    have hn := hRun.deletion_forest_nonempty hDil p hp
    have h := hTree N κ Label Item P M R K D hR horder p.2 initial hsub hn c p.1
      dilation w tau radius Lip eta sigma cell grid hwidth hD hw F hF hwW hfreq
      (hpt.trans htime) hpt (fun q hq => (hgeom q hq).1) hLip heta hsigma hwide hK hlocal
      (fun q hq => (hgeom q hq).2.1) (fun q hq => (hgeom q hq).2.2)
      (fun q hq => hrow q (hsub hq)) (fun q hq => hspectrum q (hsub hq))
      (fun q hq => hbin q (hsub hq))
      (fun q hq => P.coefficient_le_of_size_tests w cb tau sigma hw hcbquarter hsigma
        cell grid c initial hsize q (hsub hq) ((hgeom q hq).1.trans hpt)) hsize
      selector hsel hselbound (haway p hp) hsupport hradius (hnear p hp)
      E hE u hu (fun q hq => hdensity q (hsub hq))
    refine ⟨h.1,h.2.trans_eq ?_⟩
    dsimp only [B]
    ring
  have hforest := tree_list_integral_bound forest (fun p z => ∑ q∈p.2, V q z)
    (fun p => B*p.1.area) E hp
  have heval (z : ℝ×ℝ) : (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)=
      (forest.map (fun p => ∑ q∈p.2, V q z)).sum := by
    have h := hRun.deletion_forest_sum (fun q => V q z)
    rw [h]
    abel
  dsimp only
  have hefun : (fun z => (∑ q∈initial, V q z)-(∑ q∈remaining, V q z))=
      fun z => (forest.map (fun p => ∑ q∈p.2, V q z)).sum := funext heval
  change IntegrableOn (fun z => (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)) E _ ∧
    (∫ z in E, ‖(∑ q∈initial, V q z)-(∑ q∈remaining, V q z)‖ ∂volume.prod volume)≤
      B*(tops.map SlopeBox.area).sum
  rw [hefun]
  simp only [heval]
  refine ⟨hforest.1,hforest.2.trans_eq ?_⟩
  rw [List.sum_map_mul_left]
  have harea : (forest.map (fun p => p.1.area)).sum=(tops.map SlopeBox.area).sum :=
    SizeStoppingRun.deletion_forest_area
  rw [harea]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataTwoSidedRemovedIntegral
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the actual tree estimate to every full deletion tree in one
signed stopping run, and sum with its recorded top-area budget. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData

theorem exists_two_sided_removed_integral (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 ≤ cb) (hcbquarter : cb≤1/4) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (M R K D : ℕ),
      (1:ℝ)≤R → 207≤P.order →
    ∀ (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (w tau radius Lip eta sigma F dilation threshold epsilon : ℝ)
      (initial middle remaining : Finset P.PacketIndex) (positive negative : List SlopeBox),
      P.SizeStoppingRun false w cb tau threshold epsilon dilation cell grid c initial positive middle →
      P.SizeStoppingRun true w cb tau threshold epsilon dilation cell grid c middle negative remaining →
      1/2≤dilation → dilation≤D → 0<w → 0≤F → w≤P.width →
      (∀ k, |P.frequency k|≤F/w) → tau≤P.topLength →
      0≤Lip → 0≤eta → 0 ≤ sigma → 1 ≤ radius+1 → radius+1≤(2:ℝ)^K →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => P.rowSlope j l) (w/P.length j) M) →
      (∀ q∈initial, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈initial, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |ξ+P.rowSlope q.1 q.2.1*η| ≤ cStar/P.length q.1 ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ q∈initial, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
        |η-P.frequency k|≤Cv/P.width) →
      (∀ U : SlopeBox, U.width=P.width → U.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c initial U ≤ sigma^2*U.area) →
    ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (selector j l k)) →
      (∀ j l k s, ‖selector j l k s‖≤1) →
      (∀ p∈(P.sizeDeletionRecords w dilation cell grid initial positive ++
        P.sizeDeletionRecords w dilation cell grid middle negative), ∀ q∈p.2, ∀ k,
        selector q.1 q.2.1 k p.1.slope≠0 → cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-p.1.slope|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 → |s-P.rowSlope j l| ≤ radius*(w/P.length j)) →
      (∀ p∈(P.sizeDeletionRecords w dilation cell grid initial positive ++
        P.sizeDeletionRecords w dilation cell grid middle negative), ∀ j l k s,
        |s-p.1.slope|≤w/P.length j →
        ‖selector j l k s-selector j l k p.1.slope‖≤Lip*(|s-p.1.slope|/(w/P.length j))) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∀ q∈initial, P.ordinaryDensity 0 cell grid w tau E u q≤eta) →
      let V := fun q (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
        selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
      let H := fun z => (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)
      IntegrableOn H E (volume.prod volume) ∧
        (∫ z in E, ‖H z‖ ∂volume.prod volume)≤
          (((4*D+1)^2:ℕ):ℝ)*P.referenceTreeConstant C ((2*R+1)*M) K Lip*
            sigma*eta*((positive.map SlopeBox.area).sum+(negative.map SlopeBox.area).sum) := by
  obtain ⟨C,hC,hForest⟩ := exists_deletion_forest_integral hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbquarter hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M R K D hR horder c cell grid w tau radius Lip eta sigma F
    dilation threshold epsilon initial middle remaining positive negative hpos hneg hDil hD hw hF hwW hfreq htime
    hLip heta hsigma hwide hK hlocal hrow hspectrum hbin hsize selector hsel hselbound haway
    hsupport hradius hnear E hE u hu hdensity
  have hmid := hpos.remaining_subset
  have hp := hForest N κ Label Item P M R K D hR horder c cell grid
    w tau radius Lip eta sigma F dilation threshold epsilon false initial middle positive hpos
    hDil hD hw hF hwW hfreq htime hLip heta hsigma hwide hK hlocal hrow hspectrum hbin hsize
    selector hsel hselbound (fun p hp => haway p (List.mem_append_left _ hp)) hsupport hradius
    (fun p hp => hnear p (List.mem_append_left _ hp)) E hE u hu hdensity
  have hn := hForest N κ Label Item P M R K D hR horder c cell grid
    w tau radius Lip eta sigma F dilation threshold epsilon true middle remaining negative hneg
    hDil hD hw hF hwW hfreq htime hLip heta hsigma hwide hK hlocal
    (fun q hq => hrow q (hmid hq)) (fun q hq => hspectrum q (hmid hq))
    (fun q hq => hbin q (hmid hq))
    (fun U hw ht => (P.unsignedSizeTestEnergy_mono w cb cell grid c hmid U).trans (hsize U hw ht))
    selector hsel hselbound (fun p hp => haway p (List.mem_append_right _ hp)) hsupport hradius
    (fun p hp => hnear p (List.mem_append_right _ hp)) E hE u hu
    (fun q hq => hdensity q (hmid hq))
  let V := fun (q : P.PacketIndex) (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
    selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
  let A := fun z => (∑ q∈initial, V q z)-(∑ q∈middle, V q z)
  let B := fun z => (∑ q∈middle, V q z)-(∑ q∈remaining, V q z)
  have hAI : IntegrableOn A E (volume.prod volume) := hp.1
  have hBI : IntegrableOn B E (volume.prod volume) := hn.1
  have heq : (fun z => (∑ q∈initial, V q z)-(∑ q∈remaining, V q z))=
      fun z => A z+B z := by
    funext z
    dsimp [A,B]
    abel
  have heval (z : ℝ×ℝ) : (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)=A z+B z := congrFun heq z
  dsimp only
  change IntegrableOn (fun z => (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)) E _ ∧
    (∫ z in E, ‖(∑ q∈initial, V q z)-(∑ q∈remaining, V q z)‖ ∂volume.prod volume)≤_
  rw [heq]
  simp only [heval]
  refine ⟨hAI.add hBI,?_⟩
  calc
    _ ≤ ∫ z in E, ‖A z‖+‖B z‖ ∂volume.prod volume :=
      integral_mono (hAI.add hBI).norm (hAI.norm.add hBI.norm) (fun z => norm_add_le _ _)
    _ = (∫ z in E, ‖A z‖ ∂volume.prod volume)+(∫ z in E, ‖B z‖ ∂volume.prod volume) :=
      integral_add hAI.norm hBI.norm
    _ ≤ _ := add_le_add hp.2 hn.2
    _ = _ := by ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedRecordSums
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint selected records give exact sums over the selected union. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem sizeSelectionRecords_disjoint (negative : Bool) (w cb A : ℝ) (hA : 1/2≤A)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (R : Finset P.PacketIndex) (tops : List SlopeBox) :
    (P.sizeSelectionRecords negative w cb A cell grid R tops).Pairwise
      (fun p q => Disjoint p.2 q.2) := by
  induction tops generalizing R with
  | nil => exact List.Pairwise.nil
  | cons T tops ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih _⟩
    intro p hp
    have hsub := P.sizeSelectionRecords_subset negative w cb A cell grid
      (R\P.sizeDeletePackets w A cell grid R T) tops p hp
    apply Finset.disjoint_left.mpr
    intro q hq hqp
    exact (Finset.mem_sdiff.mp (hsub hqp)).2
      (P.sizeTestPackets_subset_delete negative w cb A hA cell grid R T hq)

theorem selectedPackets_sum {E : Type*} [AddCommMonoid E]
    (negative : Bool) (w cb A : ℝ) (hA : 1/2≤A)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (R : Finset P.PacketIndex) (tops : List SlopeBox) (f : P.PacketIndex → E) :
    (∑ q∈P.selectedPackets negative w cb A cell grid R tops, f q)=
      ∑ p∈(P.sizeSelectionRecords negative w cb A cell grid R tops).toFinset, ∑ q∈p.2, f q := by
  let : Std.Symm (fun p q : SlopeBox × Finset P.PacketIndex => Disjoint p.2 q.2) :=
    ⟨fun _ _ h => h.symm⟩
  apply Finset.sum_biUnion
  intro p hp q hq hpq
  exact (P.sizeSelectionRecords_disjoint negative w cb A hA cell grid R tops).forall
    (List.mem_toFinset.mp hp) (List.mem_toFinset.mp hq) hpq

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataRecordedEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The strict stopping test gives a lower energy bound for every
recorded top. This is the bound needed to sum its far-Gram estimate. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable {P : PacketLatticeData N κ Label Item}
  {negative : Bool} {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

namespace SizeStoppingRun

theorem recorded_energy_lower
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining) :
    ∀ p∈P.sizeSelectionRecords negative w cb A cell grid initial tops,
      sigma^2*p.1.area≤2*P.packetEnergySum c p.2 := by
  induction h with
  | stop => simp only [sizeSelectionRecords,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | step R T tops remaining hT _ _ ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · have ht := hT.2.2.le
      change sigma^2*T.area/2≤P.packetEnergySum c _ at ht
      linarith
    · exact ih p hp

theorem recorded_nonempty
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining) :
    ∀ p∈P.sizeSelectionRecords negative w cb A cell grid initial tops, p.2.Nonempty := by
  induction h with
  | stop => simp only [sizeSelectionRecords,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | step R T tops remaining hT _ _ ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact P.failing_size_test_nonempty negative w cb tau sigma cell grid c R T hT
    · exact ih p hp

theorem records_nodup
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hA : 1/2≤A) :
    (P.sizeSelectionRecords negative w cb A cell grid initial tops).Nodup := by
  change (P.sizeSelectionRecords negative w cb A cell grid initial tops).Pairwise (· ≠ ·)
  apply (P.sizeSelectionRecords_disjoint negative w cb A hA cell grid initial tops).imp_of_mem
  intro p q hp _ hd hpq
  subst q
  obtain ⟨r,hr⟩ := h.recorded_nonempty p hp
  exact Finset.disjoint_left.mp hd hr hr

theorem selected_energy_eq_records
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hA : 1/2≤A) :
    P.packetEnergySum c (P.selectedPackets negative w cb A cell grid initial tops)=
      ((P.recordedSizeTests negative w cb A cell grid initial tops).map (P.packetEnergySum c)).sum := by
  unfold packetEnergySum
  rw [P.selectedPackets_sum negative w cb A hA cell grid initial tops]
  rw [List.sum_toFinset _ (h.records_nodup hA)]
  rw [←P.sizeSelectionRecords_packets negative w cb A cell grid initial tops,List.map_map]
  rfl

end SizeStoppingRun
end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceGramSchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary Schur estimate for a sparse Gram matrix. It is used
for neighboring labels and comparable scales of actual packet sums. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem symmetric_matrix_energy {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (G : ι → ι → ℝ) (C : ℝ)
    (hG : ∀ i j, 0≤G i j) (hsym : ∀ i j, G i j=G j i)
    (hrow : ∀ i, ∑ j, G i j≤C) :
    (∑ i, ∑ j, G i j*a i*a j)≤C*∑ i, (a i)^2 := by
  have hp (i j : ι) : G i j*a i*a j≤(G i j*(a i)^2+G i j*(a j)^2)/2 := by
    have h := mul_nonneg (hG i j) (sq_nonneg (a i-a j))
    nlinarith only [h]
  have hcol (j : ι) : (∑ i, G i j)≤C := by simpa only [hsym] using hrow j
  calc
    _ ≤ ∑ i, ∑ j, (G i j*(a i)^2+G i j*(a j)^2)/2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hp i j))
    _ = ((∑ i, (∑ j, G i j)*(a i)^2)+(∑ j, (∑ i, G i j)*(a j)^2))/2 := by
      simp only [←Finset.sum_div,Finset.sum_add_distrib,Finset.sum_mul]
      rw [Finset.sum_comm (f := fun i j => G i j*(a j)^2)]
    _ ≤ ((∑ i, C*(a i)^2)+(∑ j, C*(a j)^2))/2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact add_le_add (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)))
        (Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)))
    _ = _ := by rw [←Finset.mul_sum]; ring

theorem sparse_gram_energy {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : ι → E) (near : ι → ι → Prop) (C : ℝ)
    (hsym : ∀ i j, near i j ↔ near j i)
    (hrow : ∀ i, ((Finset.univ.filter fun j => near i j).card:ℝ)≤C)
    (hortho : ∀ i j, ¬near i j → inner ℂ (v i) (v j)=0) :
    ‖∑ i, v i‖^2≤C*∑ i, ‖v i‖^2 := by
  let G := fun i j => if near i j then (1:ℝ) else 0
  have hG : ∀ i j, 0≤G i j := by intro i j; dsimp [G]; split_ifs <;> norm_num
  have hsymG : ∀ i j, G i j=G j i := by intro i j; simp only [G,hsym i j]
  have hrowG : ∀ i, ∑ j, G i j≤C := by
    intro i
    simpa only [G,Finset.sum_boole] using hrow i
  have hentry (i j : ι) : (inner ℂ (v i) (v j)).re≤G i j*‖v i‖*‖v j‖ := by
    by_cases hn : near i j
    · simpa only [G,ite_eq_left hn,one_mul] using (Complex.re_le_norm (inner ℂ (v i) (v j))).trans (norm_inner_le_norm (𝕜 := ℂ) (v i) (v j))
    · simp only [hortho i j hn,Complex.zero_re,G,ite_eq_right hn,zero_mul,le_refl]
  calc
    _ = ∑ i, ∑ j, (inner ℂ (v i) (v j)).re := by
      rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ E]
      simp only [sum_inner,inner_sum,map_sum]
      exact Finset.sum_comm
    _ ≤ ∑ i, ∑ j, G i j*‖v i‖*‖v j‖ :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hentry i j))
    _ ≤ _ := symmetric_matrix_energy (fun i => ‖v i‖) G C hG hsymG hrowG

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePlanarGramSchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the finite Gram-matrix estimate to actual planar Schwartz
functions and their product-Lebesgue square integrals. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem planar_toL2_norm_sq (f : SchwartzMap (ℝ×ℝ) ℂ) :
    ‖f.toLp 2 (volume.prod volume)‖^2=∫ z, ‖f z‖^2 ∂volume.prod volume := by
  have h := SchwartzMap.inner_toL2_toL2_eq f f (volume.prod volume)
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at h
  change ((‖f.toLp 2 (volume.prod volume)‖^2 : ℝ) : ℂ) =
    ∫ x, ((‖f x‖^2 : ℝ) : ℂ) ∂volume.prod volume at h
  rw [integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

theorem planar_sparse_gram_energy {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap (ℝ×ℝ) ℂ) (near : ι → ι → Prop) (C : ℝ)
    (hsym : ∀ i j, near i j ↔ near j i)
    (hrow : ∀ i, ((Finset.univ.filter fun j => near i j).card:ℝ)≤C)
    (hortho : ∀ i j, ¬near i j →
      (∫ z, inner ℂ (f i z) (f j z) ∂volume.prod volume)=0) :
    (∫ z, ‖∑ i, f i z‖^2 ∂volume.prod volume)≤
      C*∑ i, ∫ z, ‖f i z‖^2 ∂volume.prod volume := by
  have h := sparse_gram_energy (fun i => (f i).toLp 2 (volume.prod volume)) near C hsym hrow
    (fun i j hij => (SchwartzMap.inner_toL2_toL2_eq (f i) (f j) (volume.prod volume)).trans (hortho i j hij))
  have heq : (∑ i, (f i).toLp 2 (volume.prod volume))=
      (∑ i, f i).toLp 2 (volume.prod volume) := by
    exact (map_sum (SchwartzMap.toLpCLM ℂ ℂ 2 (volume.prod volume)) f Finset.univ).symm
  rw [heq,planar_toL2_norm_sq] at h
  simpa only [sum_apply,planar_toL2_norm_sq] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLocalLabelEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Equal-length label synthesis uses local angular multiplicity rather
than the total number of labels. Nonneighboring label sums are orthogonal
by their actual Fourier wedges. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem equal_length_label_energy {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap (ℝ×ℝ) ℂ) (theta : ι → ℝ)
    (ell w cStar cEta CEta : ℝ) (hell : 0<ell) (hw : 0<w) (hcEta : 0 < cEta)
    (M Q : ℕ) (hQ : 2*cStar/cEta≤Q)
    (hmultiplicity : SourceSlopeLabels.LocalMultiplicity Finset.univ theta (w/ell) M)
    (hspectrum : ∀ i xi eta, planarAngularFourier (f i) (xi,eta)≠0 →
      |xi+theta i*eta| ≤ cStar/ell ∧ cEta≤w*eta ∧ w*eta≤CEta) :
    (∫ z, ‖∑ i, f i z‖^2 ∂volume.prod volume)≤
      (((2*Q+1)*M:ℕ):ℝ)*∑ i, ∫ z, ‖f i z‖^2 ∂volume.prod volume := by
  let near := fun i j => |theta i-theta j|≤(2*cStar/cEta)*(w/ell)
  apply planar_sparse_gram_energy f near _ ?_ ?_ ?_
  · intro i j
    dsimp [near]
    rw [abs_sub_comm]
  · intro i
    have hcount := SourceSlopeLabels.window_card_le Finset.univ theta
      (t := theta i) (radius := 2*cStar/cEta) (div_pos hw hell) hmultiplicity hQ
    apply Nat.cast_le.mpr
    convert hcount using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext j
    simp only [SourceSlopeLabels.window,Finset.mem_filter,Finset.mem_univ,true_and,near]
    rw [abs_sub_comm]
  · intro i j hfar
    by_contra hn
    have hangle := planar_packet_gram_angle (f i) (f j) (theta i) (theta j)
      ell ell w cStar cEta CEta hell hell hw hcEta (hspectrum i) (hspectrum j) hn
    apply hfar
    dsimp [near]
    convert hangle using 1
    all_goals try with_reducible_and_instances rfl
    ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLocalLabelVectorEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local angular multiplicity controls vector-valued label sums with
no dependence on the number of frequency coordinates. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem equal_length_label_vector_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ) (theta : ι → ℝ)
    (ell w cStar cEta CEta : ℝ) (hell : 0<ell) (hw : 0<w) (hcEta : 0 < cEta)
    (M Q : ℕ) (hQ : 2*cStar/cEta≤Q)
    (hmultiplicity : SourceSlopeLabels.LocalMultiplicity Finset.univ theta (w/ell) M)
    (hspectrum : ∀ i k xi eta, planarAngularFourier (f i k) (xi,eta)≠0 →
      |xi+theta i*eta| ≤ cStar/ell ∧ cEta≤w*eta ∧ w*eta≤CEta) :
    (∫ z, ‖∑ i, (WithLp.toLp 2 (fun k => f i k z) : EuclideanSpace ℂ κ)‖^2
      ∂volume.prod volume)≤
      (((2*Q+1)*M:ℕ):ℝ)*∑ i,
        ∫ z, ‖(WithLp.toLp 2 (fun k => f i k z) : EuclideanSpace ℂ κ)‖^2
          ∂volume.prod volume := by
  have hi (i : ι) (k : κ) : Integrable (fun z => ‖f i k z‖^2) (volume.prod volume) :=
    ((f i k).memLp 2 (volume.prod volume)).integrable_norm_pow (by decide)
  have hs (k : κ) : Integrable (fun z => ‖∑ i, f i k z‖^2) (volume.prod volume) := by
    have h := ((∑ i, f i k : SchwartzMap (ℝ×ℝ) ℂ).memLp 2
      (volume.prod volume)).integrable_norm_pow (by decide : 2 ≠ 0)
    simpa only [sum_apply] using h
  simp only [EuclideanSpace.norm_sq_eq,WithLp.ofLp_sum,Finset.sum_apply]
  rw [integral_finsetSum _ (fun k _ => hs k)]
  calc
    _ ≤ ∑ k, (((2*Q+1)*M:ℕ):ℝ)*∑ i,
        ∫ z, ‖f i k z‖^2 ∂volume.prod volume := by
      apply Finset.sum_le_sum
      intro k _
      exact equal_length_label_energy (fun i => f i k) theta ell w cStar cEta CEta
        hell hw hcEta M Q hQ hmultiplicity (fun i => hspectrum i k)
    _ = _ := by
      rw [←Finset.mul_sum,Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum _ (fun k _ => hi i k)).symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabelScaleEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At one spatial scale, first sum sites on each genuine lattice and
then use local angular multiplicity to sum the labels. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem planar_label_scale_energy {Λ κ : Type*} [Fintype Λ] [Fintype κ]
    {ι : Λ → Type*} [∀ l, Fintype (ι l)]
    (c : ∀ l, ι l → EuclideanSpace ℂ κ)
    (f : ∀ l, ι l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (site : ∀ l, ι l → ℤ×ℤ) (hinj : ∀ l, Function.Injective (site l))
    (a b theta : Λ → ℝ) (ell W C w cStar cEta CEta : ℝ)
    (hell : 0<ell) (hW : 0<W) (hw : 0<w) (hcEta : 0 < cEta)
    (M Q : ℕ) (hQ : 2*cStar/cEta≤Q)
    (hmultiplicity : SourceSlopeLabels.LocalMultiplicity Finset.univ theta (w/ell) M)
    (hspectrum : ∀ l u k xi eta, planarAngularFourier (f l u k) (xi,eta)≠0 →
      |xi+theta l*eta| ≤ cStar/ell ∧ cEta≤w*eta ∧ w*eta≤CEta)
    (henv : ∀ l u k z, ‖f l u k z‖≤C*
      (lineEnvelope (a l+ell*(site l u).1) ell 1 z.1*
        lineEnvelope (b l+W*(site l u).2) W 1 (z.2-theta l*z.1))) :
    (∫ z, ‖∑ l, planarFixedSynthesis (c l) (f l) z‖^2 ∂volume.prod volume)≤
      (((2*Q+1)*M:ℕ):ℝ)*((4*Real.pi)^2*C^2*Real.pi^2)*
        ∑ l, ∑ u, ‖c l u‖^2*ell*W := by
  let F := fun l k => (∑ u, c l u k • f l u k : SchwartzMap (ℝ×ℝ) ℂ)
  have hF (l : Λ) (z : ℝ×ℝ) :
      (WithLp.toLp 2 (fun k => F l k z) : EuclideanSpace ℂ κ)=
        planarFixedSynthesis (c l) (f l) z := by
    ext k
    simp only [F,planarFixedSynthesis,WithLp.ofLp_toLp,sum_apply,smul_apply,smul_eq_mul]
  have hspec (l : Λ) (k : κ) (xi eta : ℝ)
      (hne : planarAngularFourier (F l k) (xi,eta)≠0) :
      |xi+theta l*eta| ≤ cStar/ell ∧ cEta≤w*eta ∧ w*eta≤CEta := by
    by_contra hout
    have hz (u : ι l) : planarAngularFourier (f l u k) (xi,eta)=0 := by
      by_contra hnonzero
      exact hout (hspectrum l u k xi eta hnonzero)
    apply hne
    dsimp only [F,planarAngularFourier]
    rw [planarFourier_finsetSum]
    simp only [planarFourier_smul]
    change (∑ u, c l u k*planarAngularFourier (f l u k) (xi,eta))=0
    simp only [hz,mul_zero,Finset.sum_const_zero]
  have h := equal_length_label_vector_energy F theta ell w cStar cEta CEta
    hell hw hcEta M Q hQ hmultiplicity hspec
  simp only [hF] at h
  calc
    _ ≤ (((2*Q+1)*M:ℕ):ℝ)*∑ l,
        ∫ z, ‖planarFixedSynthesis (c l) (f l) z‖^2 ∂volume.prod volume := h
    _ ≤ (((2*Q+1)*M:ℕ):ℝ)*∑ l,
        ((4*Real.pi)^2*C^2*Real.pi^2)*∑ u, ‖c l u‖^2*ell*W := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum fun l _ => planar_fixed_scale_energy (c l) (f l)
        (site l) (hinj l) (a l) (b l) ell W (theta l) C hell hW (henv l)
    _ = _ := by rw [←Finset.mul_sum]; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataLabelScaleEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual source family has a fixed-scale synthesis bound using
only local angular multiplicity, uniformly in its total label count. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem physicalPacket_label_envelope (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) (z : ℝ×ℝ) :
    ‖P.physicalPacket 0 j l u k z‖≤P.profileBound*
      (lineEnvelope (P.originX j l+P.length j*(P.site j l u).1) (P.length j) 1 z.1*
        lineEnvelope (P.originZ j l-P.rowSlope j l*P.originX j l+P.width*(P.site j l u).2)
          P.width 1 (z.2-P.rowSlope j l*z.1)) := by
  have h := physicalPlanarPacket_profile_envelope (P.profile j l u k) (2*P.order)
    (P.actualX j l u) (P.actualZ j l u) (P.length j) P.width
    (P.rowSlope j l) (P.frequency k) (P.length_pos j).ne' P.width_pos.ne' z
  have horder : 1≤2*P.order := by have := P.order_ge_three; omega
  have hcenter : P.actualZ j l u-P.rowSlope j l*P.actualX j l u=
      P.originZ j l-P.rowSlope j l*P.originX j l+P.width*(P.site j l u).2 := by
    simp only [actualX,actualZ]
    ring
  rw [hcenter] at h
  apply (show ‖P.physicalPacket 0 j l u k z‖≤_ from by
    simpa only [physicalPacket,zero_mul,add_zero,zero_add] using h).trans
  exact mul_le_mul (P.profile_bound j l u k)
    (mul_le_mul (lineEnvelope_antitone _ _ _ horder) (lineEnvelope_antitone _ _ _ horder)
      (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
    (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
    P.profileBound_pos.le

theorem physicalPacket_local_label_scale_energy (j : Fin N)
    (c : ∀ l : P.labels j, Item j l → EuclideanSpace ℂ κ)
    (w cStar cEta CEta : ℝ) (hw : 0<w) (hcEta : 0 < cEta)
    (M Q : ℕ) (hQ : 2*cStar/cEta≤Q)
    (hmultiplicity : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (P.rowSlope j) (w/P.length j) M)
    (hspectrum : ∀ l u k xi eta,
      planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
        |xi+P.rowSlope j l*eta| ≤ cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta) :
    (∫ z, ‖∑ l : P.labels j, planarFixedSynthesis (c l) (P.physicalPacket 0 j l) z‖^2
      ∂volume.prod volume)≤
      (((2*Q+1)*M:ℕ):ℝ)*((4*Real.pi)^2*P.profileBound^2*Real.pi^2)*
        ∑ l : P.labels j, ∑ u, ‖c l u‖^2*P.length j*P.width := by
  exact planar_label_scale_energy c (P.physicalPacket 0 j) (P.site j) (P.site_injective j)
    (P.originX j) (fun l => P.originZ j l-P.rowSlope j l*P.originX j l)
    (P.rowSlope j) (P.length j) P.width P.profileBound w cStar cEta CEta
    (P.length_pos j) P.width_pos hw hcEta M Q hQ hmultiplicity hspectrum
    (P.physicalPacket_label_envelope j)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceRestrictedGram
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Schur control of the comparable-scale part of a Gram expansion.
The other scale pairs are left for the selected-tree geometric estimate. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem restricted_gram_energy {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : ι → E) (near : ι → ι → Prop) [DecidableRel near] (C : ℝ)
    (hsym : ∀ i j, near i j ↔ near j i)
    (hrow : ∀ i, ((Finset.univ.filter fun j => near i j).card:ℝ)≤C) :
    (∑ i, ∑ j, if near i j then (inner ℂ (v i) (v j)).re else 0)≤
      C*∑ i, ‖v i‖^2 := by
  let G := fun i j => if near i j then (1:ℝ) else 0
  have hG : ∀ i j, 0≤G i j := by intro i j; dsimp [G]; split_ifs <;> norm_num
  have hsymG : ∀ i j, G i j=G j i := by intro i j; simp only [G,hsym i j]
  have hrowG : ∀ i, ∑ j, G i j≤C := by
    intro i
    simpa only [G,Finset.sum_boole] using hrow i
  calc
    _ ≤ ∑ i, ∑ j, G i j*‖v i‖*‖v j‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases h : near i j
      · simpa only [h,ite_true, if_true,G,one_mul] using
          (Complex.re_le_norm (inner ℂ (v i) (v j))).trans (norm_inner_le_norm (𝕜 := ℂ) (v i) (v j))
      · simp only [h,ite_false, if_false,G,zero_mul,le_refl]
    _ ≤ _ := symmetric_matrix_energy (fun i => ‖v i‖) G C hG hsymG hrowG

/-- A bounded interval of integer scale indices has uniformly bounded
cardinality, including scales at either endpoint of a finite family. -/
theorem finite_scale_neighbor_count {N : ℕ} (i : Fin N) (gap : ℕ) :
    (Finset.univ.filter (fun j : Fin N => |(i.val:ℤ)-(j.val:ℤ)|≤(gap:ℤ))).card≤
      2*gap+1 := by
  let e : Fin N ↪ ℤ := ⟨fun j => j.val,fun a b h => Fin.ext (Int.ofNat_inj.mp h)⟩
  let S := Finset.univ.filter (fun j : Fin N => |(i.val:ℤ)-(j.val:ℤ)|≤(gap:ℤ))
  have hs : S.map e ⊆ Finset.Icc ((i.val:ℤ)-gap) ((i.val:ℤ)+gap) := by
    intro z hz
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hz
    have hj' := (abs_le.mp (Finset.mem_filter.mp hj).2)
    apply Finset.mem_Icc.mpr
    change (i.val:ℤ)-gap ≤ j.val ∧ (j.val:ℤ) ≤ i.val+gap
    omega
  have hcard := Finset.card_le_card hs
  have hlen : (Finset.Icc ((i.val:ℤ)-gap) ((i.val:ℤ)+gap)).card=2*gap+1 := by
    have h := Int.card_Icc_of_le (a := (i.val:ℤ)-gap) (b := (i.val:ℤ)+gap) (by omega)
    omega
  simpa only [Finset.card_map,hlen,S] using hcard

theorem comparable_scale_gram_energy {N : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v : Fin N → E) (gap : ℕ) :
    (∑ i, ∑ j, if |(i.val:ℤ)-(j.val:ℤ)|≤(gap:ℤ)
      then (inner ℂ (v i) (v j)).re else 0)≤
      ((2*gap+1:ℕ):ℝ)*∑ i, ‖v i‖^2 := by
  apply restricted_gram_energy v (fun i j => |(i.val:ℤ)-(j.val:ℤ)|≤(gap:ℤ)) _
  · intro i j
    rw [abs_sub_comm]
  · intro i
    exact_mod_cast finite_scale_neighbor_count i gap

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceFiberGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact grouping of a finite Gram matrix by scale. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem sum_level_fibers {ι J A : Type*} [Fintype J] [DecidableEq J] [AddCommMonoid A]
    (S : Finset ι) (level : ι → J) (f : J → ι → A) :
    (∑ j, ∑ i∈S.filter (fun i => level i=j), f j i)=∑ i∈S, f (level i) i := by
  calc
    _ = ∑ j, ∑ i∈S.filter (fun i => level i=j), f (level i) i := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise S level (fun i => f (level i) i)

theorem gram_group_by_level {ι J E : Type*} [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Finset ι) (level : ι → J) (v : ι → E)
    (near : J → J → Prop) [DecidableRel near] :
    (∑ a, ∑ b, if near a b then
      (inner ℂ (∑ i∈S.filter (fun i => level i=a), v i)
        (∑ j∈S.filter (fun j => level j=b), v j)).re else 0)=
      ∑ i∈S, ∑ j∈S, if near (level i) (level j) then (inner ℂ (v i) (v j)).re else 0 := by
  have he (a b : J) : (if near a b then
      (inner ℂ (∑ i∈S.filter (fun i => level i=a), v i)
        (∑ j∈S.filter (fun j => level j=b), v j)).re else 0)=
      ∑ i∈S.filter (fun i => level i=a), ∑ j∈S.filter (fun j => level j=b),
        if near a b then (inner ℂ (v i) (v j)).re else 0 := by
    by_cases h : near a b
    · simp only [h,ite_true, if_true]
      change RCLike.re (inner ℂ _ _)=_
      simp only [sum_inner,inner_sum,map_sum]
      exact Finset.sum_comm
    · simp only [h,ite_false, if_false,Finset.sum_const_zero]
  simp_rw [he]
  calc
    _ = ∑ a, ∑ i∈S.filter (fun i => level i=a),
        ∑ b, ∑ j∈S.filter (fun j => level j=b),
          if near a b then (inner ℂ (v i) (v j)).re else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ a, ∑ i∈S.filter (fun i => level i=a),
        ∑ j∈S, if near a (level j) then (inner ℂ (v i) (v j)).re else 0 := by
      simp_rw [sum_level_fibers]
    _ = _ := sum_level_fibers S level _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceL2Gram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact L2 Gram identities for the finite physical packet sums. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem memLp_inner_integral (mu : Measure X) (f g : X → E)
    (hf : MemLp f 2 mu) (hg : MemLp g 2 mu) :
    inner ℂ (hf.toLp f) (hg.toLp g)=∫ x, inner ℂ (f x) (g x) ∂mu := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hfx hgx
  rw [hfx,hgx]

theorem memLp_toL2_norm_sq (mu : Measure X) (f : X → E) (hf : MemLp f 2 mu) :
    ‖hf.toLp f‖^2=∫ x, ‖f x‖^2 ∂mu := by
  have h := memLp_inner_integral mu f f hf hf
  simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow] at h
  change ((‖hf.toLp f‖^2 : ℝ) : ℂ)=(∫ x, ((‖f x‖^2 : ℝ) : ℂ) ∂mu) at h
  rw [integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceL2Sums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite sums commute with the map from square-integrable functions
into L2. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

omit [InnerProductSpace ℂ E] in
theorem finite_sum_toL2 (mu : Measure X) {ι : Type*} (S : Finset ι)
    (f : ι → X → E) (hf : ∀ i, MemLp (f i) 2 mu) :
    (memLp_finsetSum S (fun i _ => hf i)).toLp (fun x => ∑ i∈S, f i x)=
      ∑ i∈S, (hf i).toLp (f i) := by
  apply Lp.ext
  apply (MemLp.coeFn_toLp _).trans
  symm
  apply (Lp.coeFn_fun_finsetSum S (fun i => (hf i).toLp (f i))).trans
  filter_upwards [eventuallyEq_sum (s := S) (fun i _ => (hf i).coeFn_toLp)] with x hx
  simpa only [Finset.sum_apply] using hx

theorem finite_L2_sum_norm_sq (mu : Measure X) {ι : Type*} (S : Finset ι)
    (f : ι → X → E) (hf : ∀ i, MemLp (f i) 2 mu) :
    ‖∑ i∈S, (hf i).toLp (f i)‖^2=∫ x, ‖∑ i∈S, f i x‖^2 ∂mu := by
  rw [←finite_sum_toL2 mu S f hf]
  exact memLp_toL2_norm_sq mu _ _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedScale
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparable-scale Gram control for an arbitrary selected packet
set, using its actual masked coefficients. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem packet_scale_sum_eq (S : Finset P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (j : Fin N) (z : ℝ×ℝ) :
    (∑ q∈S.filter (fun q => q.1=j), P.packetVector c q z)=
      ∑ l : P.labels j, planarFixedSynthesis (P.onPackets S c j l) (P.physicalPacket 0 j l) z := by
  have he : (∑ q∈S.filter (fun q => q.1=j), P.packetVector c q z)=
      ∑ q : P.PacketIndex, if q.1=j then P.packetVector (P.onPackets S c) q z else 0 := by
    simp_rw [P.packetVector_onPackets]
    calc
      _ = ∑ q : P.PacketIndex, if q∈S.filter (fun q => q.1=j) then P.packetVector c q z else 0 := by
        symm
        rw [←Finset.sum_filter]
        congr 1
        ext q
        simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q _
        by_cases hs : q∈S <;> by_cases hj : q.1=j <;> simp only [Finset.mem_filter,hs,hj,
          and_true,and_false,ite_true, if_true,ite_false, if_false]
  rw [he]
  have hh (i : Fin N) :
      (∑ l : P.labels i, ∑ u, if i=j then
        P.packetVector (P.onPackets S c) ⟨i,⟨l,u⟩⟩ z else 0)=
      if i=j then ∑ l : P.labels i, ∑ u,
        P.packetVector (P.onPackets S c) ⟨i,⟨l,u⟩⟩ z else 0 := by
    by_cases hij : i=j <;> simp only [hij,ite_true, if_true,ite_false, if_false,Finset.sum_const_zero]
  simp only [Fintype.sum_sigma,hh,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
  ext k
  simp only [WithLp.ofLp_sum,Finset.sum_apply,packetVector,planarFixedSynthesis]

theorem packetL2_inner (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (q r : P.PacketIndex) : inner ℂ (P.packetL2 c q) (P.packetL2 c r)=
      ∫ z, inner ℂ (P.packetVector c q z) (P.packetVector c r z) ∂volume.prod volume :=
  memLp_inner_integral _ _ _ _ _

theorem selected_comparable_gram_energy
    (S : Finset P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (gap : ℕ) (w cStar cEta CEta : ℝ) (hw : 0<w) (hcEta : 0 < cEta)
    (M Q : ℕ) (hQ : 2*cStar/cEta≤Q)
    (hmultiplicity : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (P.rowSlope j) (w/P.length j) M)
    (hspectrum : ∀ j l u k xi eta,
      planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
        |xi+P.rowSlope j l*eta| ≤ cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta) :
    (∑ q∈S, ∑ r∈S, if |(q.1.val:ℤ)-(r.1.val:ℤ)|≤(gap:ℤ) then
      (∫ z, inner ℂ (P.packetVector c q z) (P.packetVector c r z)
        ∂volume.prod volume).re else 0)≤
      ((2*gap+1:ℕ):ℝ)*(((2*Q+1)*M:ℕ):ℝ)*
        ((4*Real.pi)^2*P.profileBound^2*Real.pi^2)*
          ∑ q∈S, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width := by
  let V := fun j : Fin N => ∑ q∈S.filter (fun q => q.1=j), P.packetL2 c q
  have hnear := gram_group_by_level S (fun q => q.1) (P.packetL2 c)
    (fun i j => |(i.val:ℤ)-(j.val:ℤ)|≤(gap:ℤ))
  have hn := comparable_scale_gram_energy V gap
  dsimp only [V] at hn
  rw [hnear] at hn
  simp_rw [P.packetL2_inner] at hn
  have henergy (j : Fin N) : ‖V j‖^2≤
      (((2*Q+1)*M:ℕ):ℝ)*((4*Real.pi)^2*P.profileBound^2*Real.pi^2)*
        ∑ l : P.labels j, ∑ u, ‖P.onPackets S c j l u‖^2*P.length j*P.width := by
    dsimp [V,packetL2]
    rw [finite_L2_sum_norm_sq]
    simp_rw [P.packet_scale_sum_eq S c j]
    exact P.physicalPacket_local_label_scale_energy j (P.onPackets S c j)
      w cStar cEta CEta hw hcEta M Q hQ (hmultiplicity j) (hspectrum j)
  apply hn.trans
  calc
    _ ≤ ((2*gap+1:ℕ):ℝ)*∑ j,
        (((2*Q+1)*M:ℕ):ℝ)*((4*Real.pi)^2*P.profileBound^2*Real.pi^2)*
          ∑ l : P.labels j, ∑ u, ‖P.onPackets S c j l u‖^2*P.length j*P.width :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => henergy j) (Nat.cast_nonneg _)
    _ = _ := by rw [←Finset.mul_sum,P.onPackets_energy_sum]; ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceScaleGramSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite split of a symmetric Gram matrix into comparable
scales and the two orientations of distant scales. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

private theorem scale_dichotomy (a b gap : ℕ) :
    |(a:ℤ)-(b:ℤ)|≤(gap:ℤ) ∨ a+gap+1≤b ∨ b+gap+1≤a := by
  by_cases hab : a≤b
  · have hh : (a:ℤ)-(b:ℤ)≤0 := by omega
    rw [abs_of_nonpos hh]
    omega
  · have hh : 0≤(a:ℤ)-(b:ℤ) := by omega
    rw [abs_of_nonneg hh]
    omega

private theorem scale_entry_split (a b gap : ℕ) (v : ℝ) :
    v=(if |(a:ℤ)-(b:ℤ)|≤(gap:ℤ) then v else 0)+
      (if a+gap+1≤b then v else 0)+(if b+gap+1≤a then v else 0) := by
  by_cases hn : |(a:ℤ)-(b:ℤ)|≤(gap:ℤ)
  · have habs := abs_le.mp hn
    have h1 : ¬a+gap+1≤b := by omega
    have h2 : ¬b+gap+1≤a := by omega
    simp only [hn,h1,h2,ite_true, if_true,ite_false, if_false,add_zero]
  · rcases (scale_dichotomy a b gap).resolve_left hn with hab | hba
    · have hnot : ¬b+gap+1≤a := by omega
      simp only [hn,hab,hnot,ite_false, if_false,ite_true, if_true,zero_add,add_zero]
    · have hnot : ¬a+gap+1≤b := by omega
      simp only [hn,hba,hnot,ite_false, if_false,ite_true, if_true,zero_add]

theorem scale_gram_split {ι : Type*} (S : Finset ι) (level : ι → ℕ)
    (G : ι → ι → ℝ) (hsym : ∀ i j, G i j=G j i) (gap : ℕ) :
    (∑ i∈S, ∑ j∈S, G i j)=
      (∑ i∈S, ∑ j∈S, if |(level i:ℤ)-(level j:ℤ)|≤(gap:ℤ) then G i j else 0)+
        2*(∑ i∈S, ∑ j∈S, if level j+gap+1≤level i then G i j else 0) := by
  have he : (∑ i∈S, ∑ j∈S, G i j)=
      (∑ i∈S, ∑ j∈S, if |(level i:ℤ)-(level j:ℤ)|≤(gap:ℤ) then G i j else 0)+
      (∑ i∈S, ∑ j∈S, if level i+gap+1≤level j then G i j else 0)+
      (∑ i∈S, ∑ j∈S, if level j+gap+1≤level i then G i j else 0) := by
    simp only [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact scale_entry_split (level i) (level j) gap (G i j)
  have hswap : (∑ i∈S, ∑ j∈S, if level i+gap+1≤level j then G i j else 0)=
      ∑ i∈S, ∑ j∈S, if level j+gap+1≤level i then G i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym]
  rw [he,hswap]
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedGram
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact far-Gram grouping over the actual selected records, followed
by the global near/far energy assembly. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem farPairing_eq_gram
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (S T : Finset P.PacketIndex) (gap : ℕ) :
    P.farPairing c S T gap=∑ s∈S, ∑ q∈T, if q.1.val+gap ≤ s.1.val then
      inner ℂ (P.packetL2 c s) (P.packetL2 c q) else 0 := by
  unfold farPairing
  apply Finset.sum_congr rfl
  intro s _
  simp only [longPacketSum,inner_sum]
  rw [integral_finsetSum _ (fun q _ => P.packetVector_inner_integrable c s q)]
  simp only [Finset.sum_filter,P.packetL2_inner]

theorem selected_far_gram_sum (negative : Bool) (w cb A : ℝ) (hA : 1/2≤A)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (initial : Finset P.PacketIndex) (tops : List SlopeBox) (gap : ℕ) :
    let S := P.selectedPackets negative w cb A cell grid initial tops
    (∑ s∈S, ∑ q∈S, if q.1.val+gap ≤ s.1.val then
      inner ℂ (P.packetL2 c s) (P.packetL2 c q) else 0)=
      ∑ p∈(P.sizeSelectionRecords negative w cb A cell grid initial tops).toFinset,
        P.farPairing c S p.2 gap := by
  dsimp only
  calc
    _ = ∑ s∈P.selectedPackets negative w cb A cell grid initial tops,
        ∑ p∈(P.sizeSelectionRecords negative w cb A cell grid initial tops).toFinset,
          ∑ q∈p.2, if q.1.val+gap ≤ s.1.val then
            inner ℂ (P.packetL2 c s) (P.packetL2 c q) else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      exact P.selectedPackets_sum negative w cb A hA cell grid initial tops _
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [P.farPairing_eq_gram]

/-- The exact near/far assembly for a selected set. Its two estimates
follow from local multiplicity and the per-record far theorem. -/
theorem selected_gram_energy
    (negative : Bool) (w cb A : ℝ) (hA : 1/2≤A)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (initial : Finset P.PacketIndex) (tops : List SlopeBox) (gap : ℕ)
    (Cnear Cfar : ℝ)
    (hnear : let S := P.selectedPackets negative w cb A cell grid initial tops
      (∑ s∈S, ∑ q∈S, if |(s.1.val:ℤ)-(q.1.val:ℤ)|≤(gap:ℤ) then
        (inner ℂ (P.packetL2 c s) (P.packetL2 c q)).re else 0)≤Cnear*P.packetEnergySum c S)
    (hfar : ∀ p∈P.sizeSelectionRecords negative w cb A cell grid initial tops,
      ‖P.farPairing c (P.selectedPackets negative w cb A cell grid initial tops) p.2 (gap+1)‖≤
        Cfar*P.packetEnergySum c p.2) :
    let S := P.selectedPackets negative w cb A cell grid initial tops
    (∫ z, ‖∑ q∈S, P.packetVector c q z‖^2 ∂volume.prod volume)≤
      (Cnear+2*Cfar)*P.packetEnergySum c S := by
  dsimp only at hnear ⊢
  let S := P.selectedPackets negative w cb A cell grid initial tops
  let R := (P.sizeSelectionRecords negative w cb A cell grid initial tops).toFinset
  let G := fun s q => (inner ℂ (P.packetL2 c s) (P.packetL2 c q)).re
  have hsym (s q : P.PacketIndex) : G s q=G q s := by
    change RCLike.re (inner ℂ (P.packetL2 c s) (P.packetL2 c q))=
      RCLike.re (inner ℂ (P.packetL2 c q) (P.packetL2 c s))
    exact inner_re_symm _ _
  have hsplit := scale_gram_split S (fun q => q.1.val) G hsym gap
  have hnorm : (∫ z, ‖∑ q∈S, P.packetVector c q z‖^2 ∂volume.prod volume)=
      ∑ s∈S, ∑ q∈S, G s q := by
    rw [←finite_L2_sum_norm_sq _ S _ (P.packetVector_memLp c)]
    change ‖∑ q∈S, P.packetL2 c q‖^2=
      ∑ s∈S, ∑ q∈S, RCLike.re (inner ℂ (P.packetL2 c s) (P.packetL2 c q))
    rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ]
    simp only [sum_inner,inner_sum,map_sum]
    exact Finset.sum_comm
  have hreal : (∑ s∈S, ∑ q∈S, if q.1.val+gap+1 ≤ s.1.val then G s q else 0)=
      ∑ p∈R, (P.farPairing c S p.2 (gap+1)).re := by
    change (∑ s∈S, ∑ q∈S, if q.1.val+gap+1 ≤ s.1.val then
      (RCLike.re : ℂ → ℝ) (inner ℂ (P.packetL2 c s) (P.packetL2 c q)) else 0)=
      ∑ p∈R, (RCLike.re : ℂ → ℝ) (P.farPairing c S p.2 (gap+1))
    have he := P.selected_far_gram_sum negative w cb A hA cell grid c initial tops (gap+1)
    have hr := congrArg Complex.re he
    change (RCLike.re : ℂ → ℝ) _ = (RCLike.re : ℂ → ℝ) _ at hr
    simpa only [R,S,G,map_sum,apply_ite,map_zero,Nat.add_assoc] using hr
  have hb : (∑ p∈R, (P.farPairing c S p.2 (gap+1)).re)≤Cfar*P.packetEnergySum c S := by
    calc
      _ ≤ ∑ p∈R, Cfar*P.packetEnergySum c p.2 := by
        apply Finset.sum_le_sum
        intro p hp
        exact (Complex.re_le_norm _).trans (hfar p (List.mem_toFinset.mp hp))
      _ = _ := by
        rw [←Finset.mul_sum]
        congr 1
        exact (P.selectedPackets_sum negative w cb A hA cell grid initial tops _).symm
  rw [hnorm,hsplit,hreal]
  nlinarith

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSelectedDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual analyzing coefficients and L2 duality for a selected packet
set. Only the synthesis estimate for those same coefficients is needed. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert

 theorem l2_self_pairing_energy_le {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (mu : Measure X) (F g : X → E) (S A : ℝ) (hS : 0≤S) (hA : 0≤A)
    (hF : MemLp F 2 mu) (hg : MemLp g 2 mu)
    (hp : (S : ℂ)=∫ x, inner ℂ (F x) (g x) ∂mu)
    (hbound : (∫ x, ‖F x‖^2 ∂mu)≤A*S) :
    S≤A*∫ x, ‖g x‖^2 ∂mu := by
  have hcs : S≤‖hF.toLp F‖*‖hg.toLp g‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) (hF.toLp F) (hg.toLp g)
    rw [memLp_inner_integral mu F g hF hg,←hp,Complex.norm_real,Real.norm_of_nonneg hS] at h
    exact h
  have hsq := pow_le_pow_left₀ hS hcs 2
  rw [mul_pow,memLp_toL2_norm_sq mu F hF,memLp_toL2_norm_sq mu g hg] at hsq
  have hnonneg : 0≤∫ x, ‖g x‖^2 ∂mu := integral_nonneg fun _ => sq_nonneg _
  have hm := mul_le_mul_of_nonneg_right hbound hnonneg
  by_cases hz : S=0
  · rw [hz]
    exact mul_nonneg hA hnonneg
  · have hs : 0<S := lt_of_le_of_ne hS (Ne.symm hz)
    apply le_of_mul_le_mul_left (a := S) _ hs
    nlinarith

 theorem finite_analyzing_self_pairing {X I K : Type*} [MeasurableSpace X]
    [Fintype K] (mu : Measure X) (area : I → ℝ) (wave : I → K → X → ℂ)
    (g : X → EuclideanSpace ℂ K) (S : Finset I)
    (ha : ∀ i∈S, area i≠0)
    (hint : ∀ i∈S, ∀ k, Integrable (fun x => g x k*conj (wave i k x)) mu) :
    ((∑ i∈S, area i*‖analyzingCoefficient mu area wave g i‖^2 : ℝ) : ℂ)=
      ∫ x, inner ℂ
        (∑ i∈S, WithLp.toLp 2 (fun k => analyzingCoefficient mu area wave g i k*wave i k x))
        (g x) ∂mu := by
  classical
  have hp := analyzingCoefficient_self_pairing mu (fun i : S => area i)
    (fun i : S => wave i) g (fun i => ha i i.property) (fun i k => hint i i.property k)
  change ((∑ i : S, area i*‖analyzingCoefficient mu area wave g i‖^2 : ℝ) : ℂ)=_ at hp
  have he : (∑ i : S, area i*‖analyzingCoefficient mu area wave g i‖^2)=
      ∑ i∈S, area i*‖analyzingCoefficient mu area wave g i‖^2 :=
    Finset.sum_coe_sort S (fun i : I => area i*‖analyzingCoefficient mu area wave g i‖^2)
  rw [he] at hp
  rw [hp]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  ext k
  simp only [diagonalSynthesis,WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_toLp,
    ]
  change (∑ i : S, analyzingCoefficient mu area wave g i k*wave i k x)=_
  exact Finset.sum_coe_sort S (fun i : I => analyzingCoefficient mu area wave g i k*wave i k x)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedDuality
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert

namespace PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

 theorem selected_ordinary_coefficient_energy (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hg : MemLp g 2 (volume.prod volume)) (S : Finset P.PacketIndex)
    (A : ℝ) (hA : 0≤A)
    (hbound : (∫ z, ‖∑ q∈S, P.packetVector (P.ordinaryCoefficient g) q z‖^2
      ∂volume.prod volume)≤A*P.packetEnergySum (P.ordinaryCoefficient g) S) :
    P.packetEnergySum (P.ordinaryCoefficient g) S≤A*∫ z, ‖g z‖^2 ∂volume.prod volume := by
  have he : P.packetEnergySum (P.ordinaryCoefficient g) S=
      ∑ q∈S, (P.length q.1*P.width)*‖P.ordinaryCoefficient g q.1 q.2.1 q.2.2‖^2 := by
    apply Finset.sum_congr rfl
    intro q _
    ring
  apply l2_self_pairing_energy_le (volume.prod volume) _ g _ A _ hA
    (memLp_finsetSum S (fun q _ => P.packetVector_memLp (P.ordinaryCoefficient g) q)) hg _ hbound
  · exact Finset.sum_nonneg fun q _ =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (P.length_pos q.1).le) P.width_pos.le
  · rw [he]
    apply finite_analyzing_self_pairing
    · intro q _
      exact (mul_pos (P.length_pos q.1) P.width_pos).ne'
    · intro q _ k
      have hgk : MemLp (fun z => g z k) 2 (volume.prod volume) := (memLp_piLp_iff.mp hg) k
      exact hgk.integrable_mul ((P.physicalPacket 0 q.1 q.2.1 q.2.2 k).memLp 2
        (volume.prod volume)).star

end PacketLatticeData
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedArea
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Charge the actual selected top areas to the L2 norm of the test
function, using the proved selected synthesis estimate. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData.SizeStoppingRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable {P : PacketLatticeData N κ Label Item} {negative : Bool}
  {w cb tau sigma epsilon A : ℝ} {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem selected_top_area_bound
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : MemLp g 2 (volume.prod volume))
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid
      (P.ordinaryCoefficient g) initial tops remaining)
    (hA : 1/2≤A) (hsigma : 0 < sigma) (C : ℝ) (hC : 0≤C)
    (hbound : let S := P.selectedPackets negative w cb A cell grid initial tops
      (∫ z, ‖∑ q∈S, P.packetVector (P.ordinaryCoefficient g) q z‖^2 ∂volume.prod volume)≤
        C*P.packetEnergySum (P.ordinaryCoefficient g) S) :
    (tops.map SlopeBox.area).sum≤(2*C/sigma^2)*∫ z, ‖g z‖^2 ∂volume.prod volume := by
  have he := P.selected_ordinary_coefficient_energy g hg
    (P.selectedPackets negative w cb A cell grid initial tops) C hC hbound
  have ht := h.top_area_energy
  rw [←h.selected_energy_eq_records hA] at ht
  have hle : sigma^2/2*(tops.map SlopeBox.area).sum≤C*∫ z, ‖g z‖^2 ∂volume.prod volume :=
    ht.trans he
  have hs : 0 < sigma^2/2 := div_pos (sq_pos_of_pos hsigma) (by norm_num)
  calc
    _ ≤ (C*∫ z, ‖g z‖^2 ∂volume.prod volume)/(sigma^2/2) :=
      (le_div_iff₀ hs).mpr (by simpa only [mul_comm] using hle)
    _ = _ := by field_simp

end LipschitzHilbert.PacketLatticeData.SizeStoppingRun

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedCoefficientBound
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial unsigned size bound controls each coefficient recorded
by either signed pass. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData.SizeStoppingRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable {P : PacketLatticeData N κ Label Item} {negative : Bool}
  {w cb tau sigma epsilon A : ℝ} {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem selected_coefficient_bound
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hw : 0<w) (hcb : cb≤1/4) (D : ℝ) (hD : 0≤D) (hsigma : 0 ≤ sigma)
    (hsize : ∀ T : SlopeBox, T.width=P.width → T.length≤tau →
      P.unsignedSizeTestEnergy w cb cell grid c initial T≤(D*sigma)^2*T.area) :
    ∀ q∈P.selectedPackets negative w cb A cell grid initial tops,
      ‖c q.1 q.2.1 q.2.2‖≤D*sigma := by
  intro q hq
  obtain ⟨p,hp,hqp⟩ := (P.mem_selectedPackets negative w cb A cell grid initial tops q).mp hq
  have hgeom := h.records_geometry p hp
  exact P.coefficient_le_of_size_tests w cb tau (D*sigma) hw hcb (mul_nonneg hD hsigma)
    cell grid c initial hsize q
    (P.sizeSelectionRecords_subset negative w cb A cell grid initial tops p hp hqp)
    (((hgeom.2.2 q hqp).1).trans hgeom.2.1)

end LipschitzHilbert.PacketLatticeData.SizeStoppingRun

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedQuadratic
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear summation of the per-top quadratic estimate, using the
actual stopping threshold for each recorded top. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable {P : PacketLatticeData N κ Label Item}
  {negative : Bool} {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

namespace SizeStoppingRun

theorem selected_far_linear
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (gap : ℕ) (K : ℝ) (hK : 0≤K)
    (hquad : ∀ p∈P.sizeSelectionRecords negative w cb A cell grid initial tops,
      ‖P.farPairing c (P.selectedPackets negative w cb A cell grid initial tops) p.2 gap‖^2≤
        K*sigma^2*p.1.length*P.width*P.packetEnergySum c p.2) :
    ∀ p∈P.sizeSelectionRecords negative w cb A cell grid initial tops,
      ‖P.farPairing c (P.selectedPackets negative w cb A cell grid initial tops) p.2 gap‖≤
        Real.sqrt (2*K)*P.packetEnergySum c p.2 := by
  intro p hp
  have he : 0≤P.packetEnergySum c p.2 :=
    Finset.sum_nonneg fun q _ => mul_nonneg (mul_nonneg (sq_nonneg _) (P.length_pos q.1).le) P.width_pos.le
  have hwidth := (h.records_geometry p hp).1
  apply quadratic_far_bound_linear he hK (sigma := sigma) (A := p.1.area)
  · have hq := hquad p hp
    simpa only [SlopeBox.area,hwidth,mul_assoc] using hq
  · exact h.recorded_energy_lower p hp

theorem selected_gram_energy_of_quadratic
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hA : 1/2≤A) (gap : ℕ) (Cnear K : ℝ) (hK : 0≤K)
    (hnear : let S := P.selectedPackets negative w cb A cell grid initial tops
      (∑ s∈S, ∑ q∈S, if |(s.1.val:ℤ)-(q.1.val:ℤ)|≤(gap:ℤ) then
        (inner ℂ (P.packetL2 c s) (P.packetL2 c q)).re else 0)≤Cnear*P.packetEnergySum c S)
    (hquad : ∀ p∈P.sizeSelectionRecords negative w cb A cell grid initial tops,
      ‖P.farPairing c (P.selectedPackets negative w cb A cell grid initial tops) p.2 (gap+1)‖^2≤
        K*sigma^2*p.1.length*P.width*P.packetEnergySum c p.2) :
    let S := P.selectedPackets negative w cb A cell grid initial tops
    (∫ z, ‖∑ q∈S, P.packetVector c q z‖^2 ∂volume.prod volume)≤
      (Cnear+2*Real.sqrt (2*K))*P.packetEnergySum c S :=
  P.selected_gram_energy negative w cb A hA cell grid c initial tops gap Cnear
    (Real.sqrt (2*K)) hnear (h.selected_far_linear (gap+1) K hK hquad)

end SizeStoppingRun
end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSignedSelectedSynthesis
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected packet synthesis estimate for either sign of the
actual stopping run, with the same constants in both passes. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_signed_selected_synthesis_bound (hL : LepingleInput)
    (cStar cEta CEta cb : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hcb : 0 < cb) (hcb4 : cb≤4) (hspectral : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (negative : Bool) (M Q gap packGap : ℕ),
      ∀ (w tau sigma D epsilon A margin F : ℝ), 0<w → w≤P.width → 0≤F →
      (∀ k, |P.frequency k|≤F/w) →
      (cStar/cEta)*(1+1/(2:ℝ)^(gap+1))+1/(2:ℝ)^(gap+1) ≤ cb/4 →
      (1+cb/4)/(2:ℝ)^packGap ≤ cb/4 → cb/2 ≤ margin-cStar/cEta →
      2*(1+(1+cb/4))+1/2≤A → cb/4≤Q → 2*cStar/cEta≤Q →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
    ∀ (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (initial remaining : Finset P.PacketIndex) (tops : List SlopeBox),
      P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining →
      (∀ q∈P.selectedPackets negative w cb A cell grid initial tops, ‖c q.1 q.2.1 q.2.2‖≤D*sigma) →
      (∀ q∈P.selectedPackets negative w cb A cell grid initial tops,
        P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈P.selectedPackets negative w cb A cell grid initial tops, epsilon ≤ cb*(w/P.length q.1)/4) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
        |xi+P.rowSlope j l*eta| ≤ cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta) →
      (∀ s∈P.selectedPackets negative w cb A cell grid initial tops, ∀ k xi eta,
        planarAngularFourier (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (xi,eta)≠0 →
        Icc (-xi/eta-margin*(w/P.length s.1)) (-xi/eta+margin*(w/P.length s.1))⊆
          scaledAngularCell (w/P.topLength) grid s.1.val (cell s.1 s.2.1)) →
    let S := P.selectedPackets negative w cb A cell grid initial tops
    let K := selectedFarConstant P cb D C packGap M Q
    (∫ z, ‖∑ q∈S, P.packetVector c q z‖^2 ∂volume.prod volume)≤
      (selectedNearConstant P gap M Q+2*Real.sqrt (2*K))*
        ∑ q∈S, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width := by
  obtain ⟨C,hC,hFar⟩ := exists_signed_selected_far_gram_bound hL cStar cEta CEta cb
    hcStar hcEta hCEta hcb hcb4 hspectral
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P negative M Q gap packGap w tau sigma D epsilon A margin F
    hw hwW hF hfreq hgap hpack hmarginSize hA hQ hQnear hlocal cell grid c initial remaining tops
    hrun hcoeff hrow hepsilon hspectrum hmargin
  dsimp only
  have hAhalf : 1/2≤A := by linarith
  apply hrun.selected_gram_energy_of_quadratic hAhalf gap
    (selectedNearConstant P gap M Q) (selectedFarConstant P cb D C packGap M Q)
  · unfold selectedFarConstant
    positivity
  · dsimp only
    simp_rw [P.packetL2_inner]
    exact P.selected_comparable_gram_energy _ c gap w cStar cEta CEta hw hcEta M Q
      hQnear hlocal hspectrum
  · intro p hp
    have hf := hFar N κ Label Item P negative M Q (gap+1) packGap w tau sigma (D*sigma)
      epsilon A margin F hw hwW hF hfreq hgap hpack hmarginSize hA hQ hlocal cell grid c
      initial remaining tops hrun hcoeff hrow hepsilon hspectrum hmargin p hp
    change ‖P.farPairing c _ p.2 (gap+1)‖^2≤_ at hf
    apply hf.trans_eq
    unfold selectedFarConstant packetEnergySum
    ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSignedSelectedArea
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected top-area estimate for both passes, with ordinary
coefficients defined by their actual integrals. The initial size bound
supplies coefficient control; no selected-energy bound is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_signed_selected_area_bound (hL : LepingleInput)
    (cStar cEta CEta cb : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hcb : 0 < cb) (hcb4 : cb≤4) (hspectral : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (negative : Bool) (M Q gap packGap : ℕ),
      ∀ (w tau sigma D epsilon A margin F : ℝ), 0 < sigma → 0≤D → cb≤1/4 →
      0<w → w≤P.width → 0≤F →
      (∀ k, |P.frequency k|≤F/w) →
      (cStar/cEta)*(1+1/(2:ℝ)^(gap+1))+1/(2:ℝ)^(gap+1) ≤ cb/4 →
      (1+cb/4)/(2:ℝ)^packGap ≤ cb/4 → cb/2 ≤ margin-cStar/cEta →
      2*(1+(1+cb/4))+1/2≤A → cb/4≤Q → 2*cStar/cEta≤Q →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
    ∀ (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : MemLp g 2 (volume.prod volume))
      (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (_hc : c=P.ordinaryCoefficient g)
      (initial remaining : Finset P.PacketIndex) (tops : List SlopeBox),
      P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining →
      (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c initial T≤(D*sigma)^2*T.area) →
      (∀ q∈P.selectedPackets negative w cb A cell grid initial tops,
        P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈P.selectedPackets negative w cb A cell grid initial tops, epsilon ≤ cb*(w/P.length q.1)/4) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
        |xi+P.rowSlope j l*eta| ≤ cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta) →
      (∀ s∈P.selectedPackets negative w cb A cell grid initial tops, ∀ k xi eta,
        planarAngularFourier (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (xi,eta)≠0 →
        Icc (-xi/eta-margin*(w/P.length s.1)) (-xi/eta+margin*(w/P.length s.1))⊆
          scaledAngularCell (w/P.topLength) grid s.1.val (cell s.1 s.2.1)) →
    (tops.map SlopeBox.area).sum≤
      (2*(selectedNearConstant P gap M Q+
        2*Real.sqrt (2*selectedFarConstant P cb D C packGap M Q))/sigma^2)*
          ∫ z, ‖g z‖^2 ∂volume.prod volume := by
  obtain ⟨C,hC,hSyn⟩ := exists_signed_selected_synthesis_bound hL cStar cEta CEta cb
    hcStar hcEta hCEta hcb hcb4 hspectral
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P negative M Q gap packGap w tau sigma D epsilon A margin F
    hsigma hD hcbquarter hw hwW hF hfreq hgap hpack hmarginSize hA hQ hQnear hlocal cell grid
    g hg c hc initial remaining tops hrun hsize hrow hepsilon hspectrum hmargin
  subst c
  have hcoeff := hrun.selected_coefficient_bound hw hcbquarter D hD hsigma.le hsize
  have hs := hSyn N κ Label Item P negative M Q gap packGap w tau sigma D epsilon A margin F
    hw hwW hF hfreq hgap hpack hmarginSize hA hQ hQnear hlocal cell grid
    (P.ordinaryCoefficient g) initial remaining tops hrun hcoeff hrow hepsilon hspectrum hmargin
  have hAhalf : 1/2≤A := by linarith
  apply hrun.selected_top_area_bound g hg hAhalf hsigma
    (selectedNearConstant P gap M Q+2*Real.sqrt (2*selectedFarConstant P cb D C packGap M Q))
  · unfold selectedNearConstant
    positivity
  · exact hs

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataTwoSidedSizeArea
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary two-sided size-selection lemma with an L2 top-area
bound, derived from the actual packet geometry and scalar variation input. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_two_sided_size_selection_with_area (hL : LepingleInput)
    (cStar cEta CEta cb : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hcb : 0 < cb) (hcb4 : cb≤4) (hspectral : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (M Q gap packGap : ℕ),
      ∀ (w tau sigma D epsilon A margin F : ℝ), 0 < sigma → 0≤D → cb≤1/4 → 0<epsilon →
      0<w → w≤P.width → 0≤F →
      (∀ k, |P.frequency k|≤F/w) →
      (cStar/cEta)*(1+1/(2:ℝ)^(gap+1))+1/(2:ℝ)^(gap+1) ≤ cb/4 →
      (1+cb/4)/(2:ℝ)^packGap ≤ cb/4 → cb/2 ≤ margin-cStar/cEta →
      2*(1+(1+cb/4))+1/2≤A → cb/4≤Q → 2*cStar/cEta≤Q →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
    ∀ (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : MemLp g 2 (volume.prod volume))
      (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (_hc : c=P.ordinaryCoefficient g)
      (initial : Finset P.PacketIndex),
      (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c initial T≤(D*sigma)^2*T.area) →
      (∀ q∈initial,
        P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈initial, epsilon ≤ cb*(w/P.length q.1)/4) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
        |xi+P.rowSlope j l*eta| ≤ cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta) →
      (∀ s∈initial, ∀ k xi eta,
        planarAngularFourier (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (xi,eta)≠0 →
        Icc (-xi/eta-margin*(w/P.length s.1)) (-xi/eta+margin*(w/P.length s.1))⊆
          scaledAngularCell (w/P.topLength) grid s.1.val (cell s.1 s.2.1)) →
    ∃ positive middle negative remaining,
      P.SizeStoppingRun false w cb tau sigma epsilon A cell grid c initial positive middle ∧
      P.SizeStoppingRun true w cb tau sigma epsilon A cell grid c middle negative remaining ∧
      remaining⊆initial ∧
      (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c remaining T ≤ sigma^2*T.area) ∧
      (positive.map SlopeBox.area).sum+(negative.map SlopeBox.area).sum≤
        (4*(selectedNearConstant P gap M Q+
          2*Real.sqrt (2*selectedFarConstant P cb D C packGap M Q))/sigma^2)*
            ∫ z, ‖g z‖^2 ∂volume.prod volume := by
  obtain ⟨C,hC,hArea⟩ := exists_signed_selected_area_bound hL cStar cEta CEta cb
    hcStar hcEta hCEta hcb hcb4 hspectral
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M Q gap packGap w tau sigma D epsilon A margin F
    hsigma hD hcbquarter hepsilonPos hw hwW hF hfreq hgap hpack hmarginSize hA hQ hQnear hlocal
    cell grid g hg c hc initial hsize hrow hepsilon hspectrum hmargin
  subst c
  have hAhalf : 1/2≤A := by linarith
  obtain ⟨positive,middle,negative,remaining,hpos,hneg,hrsub,hgood⟩ :=
    P.exists_two_sided_size_selection w cb tau sigma epsilon A hw.le hcb.le hepsilonPos hAhalf
      cell grid (P.ordinaryCoefficient g) initial
  have hsubset (sign : Bool) (R : Finset P.PacketIndex) (ts : List SlopeBox) (hR : R⊆initial) :
      P.selectedPackets sign w cb A cell grid R ts⊆initial := by
    intro q hq
    obtain ⟨p,hp,hqp⟩ := (P.mem_selectedPackets sign w cb A cell grid R ts q).mp hq
    exact hR (P.sizeSelectionRecords_subset sign w cb A cell grid R ts p hp hqp)
  have happly (sign : Bool) (R rem : Finset P.PacketIndex) (ts : List SlopeBox)
      (hrun : P.SizeStoppingRun sign w cb tau sigma epsilon A cell grid (P.ordinaryCoefficient g) R ts rem)
      (hR : R⊆initial) :
      (ts.map SlopeBox.area).sum≤
        (2*(selectedNearConstant P gap M Q+
          2*Real.sqrt (2*selectedFarConstant P cb D C packGap M Q))/sigma^2)*
            ∫ z, ‖g z‖^2 ∂volume.prod volume := by
    apply hArea N κ Label Item P sign M Q gap packGap w tau sigma D epsilon A margin F
      hsigma hD hcbquarter hw hwW hF hfreq hgap hpack hmarginSize hA hQ hQnear hlocal
      cell grid g hg (P.ordinaryCoefficient g) rfl R rem ts hrun
    · intro T hwidth hlen
      exact (P.unsignedSizeTestEnergy_mono w cb cell grid (P.ordinaryCoefficient g) hR T).trans
        (hsize T hwidth hlen)
    · intro q hq
      exact hrow q (hsubset sign R ts hR hq)
    · intro q hq
      exact hepsilon q (hsubset sign R ts hR hq)
    · exact hspectrum
    · intro q hq
      exact hmargin q (hsubset sign R ts hR hq)
  refine ⟨positive,middle,negative,remaining,hpos,hneg,hrsub,hgood,?_⟩
  have hp := happly false initial middle positive hpos (fun _ h => h)
  have hn := happly true middle remaining negative hneg hpos.remaining_subset
  convert add_le_add hp hn using 1
  all_goals try with_reducible_and_instances rfl
  ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCappedRemovalStep
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same density/size removal admits an independent bounded-input
size cap. The selection threshold and its area budget remain unchanged. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_ordinary_capped_removal_step_oai (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 < cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar < cEta*cb) :
    ∃ CD CS CT : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (M Q gap packGap R K D0 : ℕ),
    ∀ (w tau sigma D epsilon A margin F radius Lip eta density cap : ℝ),
      0 < sigma → 0≤D → 0 ≤ cap → 0<epsilon → 0<eta → 0≤density → 0≤Lip →
      0<w → w≤P.width → 0≤F → (∀ k, |P.frequency k|≤F/w) →
      (cStar/cEta)*(1+1/(2:ℝ)^(gap+1))+1/(2:ℝ)^(gap+1) ≤ cb/4 →
      (1+cb/4)/(2:ℝ)^packGap ≤ cb/4 → cb/2 ≤ margin-cStar/cEta →
      2*(1+(1+cb/4))+1/2≤A → cb/4≤Q → 2*cStar/cEta≤Q →
      (1:ℝ)≤R → 207≤P.order → A≤D0 → tau≤P.topLength →
      1 ≤ radius+1 → radius+1≤(2:ℝ)^K →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
    ∀ (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ), MemLp g 2 (volume.prod volume) →
    ∀ (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ), c=P.ordinaryCoefficient g →
    ∀ (initial : Finset P.PacketIndex),
      (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c initial T≤(D*sigma)^2*T.area) →
      (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c initial T ≤ cap^2*T.area) →
      (∀ q∈initial, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈initial, epsilon ≤ cb*(w/P.length q.1)/4) →
      (∀ j l a k xi et, planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et| ≤ cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta) →
      (∀ s∈initial, ∀ k xi et,
        planarAngularFourier (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (xi,et)≠0 →
        Icc (-xi/et-margin*(w/P.length s.1)) (-xi/et+margin*(w/P.length s.1))⊆
          scaledAngularCell (w/P.topLength) grid s.1.val (cell s.1 s.2.1)) →
      (∀ q∈initial, ∀ k xi et,
        planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        |et-P.frequency k|≤Cv/P.width) →
    ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (selector j l k)) →
      (∀ j l k s, ‖selector j l k s‖≤1) →
      (∀ j l k s, selector j l k s≠0 → cb*w/P.length j≤|P.rowSlope j l-s|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 → |s-P.rowSlope j l| ≤ radius*(w/P.length j)) →
      (∀ j l k s t, |s-t|≤w/P.length j →
        ‖selector j l k s-selector j l k t‖≤Lip*(|s-t|/(w/P.length j))) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → (volume.prod volume) E≠∞ →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∀ q∈initial, P.ordinaryDensity 0 cell grid w tau E u q≤density) →
    ∃ remaining : Finset P.PacketIndex, remaining⊆initial ∧
      (∀ q∈remaining, P.ordinaryDensity 0 cell grid w tau E u q≤eta) ∧
      (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c remaining T ≤ sigma^2*T.area) ∧
      let V := fun q (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
        selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
      IntegrableOn (fun z => (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)) E (volume.prod volume) ∧
      (∫ z in E, ‖(∑ q∈initial, V q z)-(∑ q∈remaining, V q z)‖ ∂volume.prod volume)≤
        (625*densityRadiusConstant^2)*P.referenceTreeConstant CD ((2*R+1)*M) K Lip*
          cap*density*(1+eta^(-(1/20:ℝ)))*(2*(volume.prod volume).real E/eta) +
        (((4*D0+1)^2:ℕ):ℝ)*P.referenceTreeConstant CT ((2*R+1)*M) K Lip*cap*density*
          ((4*(selectedNearConstant P gap M Q+
            2*Real.sqrt (2*selectedFarConstant P cb D CS packGap M Q))/sigma^2)*
              ∫ z, ‖g z‖^2 ∂volume.prod volume) := by
  obtain ⟨CD,hCD,hDensity⟩ := exists_density_removal_integral hL cStar cEta CEta cb Cv
    hcStar hcEta hCEta hCv hcb.le hcbQuarter hspectral
  obtain ⟨CS,hCS,hSelect⟩ := exists_two_sided_size_selection_with_area hL
    cStar cEta CEta cb hcStar hcEta hCEta hcb (by linarith) hspectral
  obtain ⟨CT,hCT,hIntegral⟩ := exists_two_sided_removed_integral hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb.le hcbQuarter hspectral
  refine ⟨CD,CS,CT,hCD,hCS,hCT,?_⟩
  intro N κ Label Item _ _ P M Q gap packGap R K D0 w tau sigma D epsilon A margin F
    radius Lip eta density cap hsigma hD hcap hepsilon heta hdensity hLip hw hW hF hfreq
    hgap hpack hmargin hA hQ hQnear hR horder hD0 htime hwide hK hlocal
    cell grid g hg c hc initial hsize hsizeCap hrow heps hspectrum hmarginSpec hbin
    selector hsel hbound haway hsupport hradius hnear E hE hEfin u hu hden
  let removed := initial.filter (fun q => eta<P.ordinaryDensity 0 cell grid w tau E u q)
  let middle := initial\removed
  have hDensityStep := hDensity N κ Label Item P M R K hR horder initial c cell grid
    w tau eta density cap radius Lip F heta hw hW hF hfreq htime hLip hdensity
    hcap hwide hK hlocal hrow
    (fun q _ k xi et hn => hspectrum q.1 q.2.1 q.2.2 k xi et hn) hbin hsizeCap
    selector hsel hbound haway hsupport hradius hnear E hE hEfin u hu hden
  change middle⊆initial ∧
    (∀ q∈middle, P.ordinaryDensity 0 cell grid w tau E u q≤eta) ∧ _ at hDensityStep
  have hm : middle⊆initial := hDensityStep.1
  have hmSize (T : SlopeBox) (hwT : T.width=P.width) (htT : T.length≤tau) :
      P.unsignedSizeTestEnergy w cb cell grid c middle T≤(D*sigma)^2*T.area :=
    (P.unsignedSizeTestEnergy_mono w cb cell grid c hm T).trans (hsize T hwT htT)
  have hmCap (T : SlopeBox) (hwT : T.width=P.width) (htT : T.length≤tau) :
      P.unsignedSizeTestEnergy w cb cell grid c middle T ≤ cap^2*T.area :=
    (P.unsignedSizeTestEnergy_mono w cb cell grid c hm T).trans (hsizeCap T hwT htT)
  obtain ⟨positive,intermediate,negative,remaining,hpos,hneg,hr,hsmall,harea⟩ :=
    hSelect N κ Label Item P M Q gap packGap w tau sigma D epsilon A margin F
      hsigma hD hcbQuarter hepsilon hw hW hF hfreq hgap hpack hmargin hA hQ hQnear hlocal
      cell grid g hg c hc middle hmSize (fun q hq => hrow q (hm hq))
      (fun q hq => heps q (hm hq)) hspectrum (fun q hq => hmarginSpec q (hm hq))
  have hRemoved := hIntegral N κ Label Item P M R K D0 hR horder c cell grid w tau radius Lip density
    cap F A sigma epsilon middle intermediate remaining positive negative hpos hneg
    (by linarith) hD0 hw hF hW hfreq htime hLip hdensity hcap hwide hK hlocal
    (fun q hq => hrow q (hm hq)) (fun q _ k xi et hn => hspectrum q.1 q.2.1 q.2.2 k xi et hn)
    (fun q hq => hbin q (hm hq)) hmCap selector hsel hbound
    (fun p _ q _ k hn => haway q.1 q.2.1 k p.1.slope hn) hsupport hradius
    (fun p _ j l k s hs => hnear j l k s p.1.slope hs) E hE u hu
    (fun q hq => hden q (hm hq))
  have hTree : 0≤P.referenceTreeConstant CT ((2*R+1)*M) K Lip := by
    have ht := transverseTailConstant_nonneg
    have ha := P.referenceEnvelopeConstant_pos
    have hp := P.profileBound_pos
    dsimp [referenceTreeConstant]
    positivity
  have hSizeBound := hRemoved.2.trans
    (mul_le_mul_of_nonneg_left harea (by positivity :
      0≤((((4*D0+1)^2:ℕ):ℝ)*P.referenceTreeConstant CT ((2*R+1)*M) K Lip*cap*density)))
  let V := fun (q : P.PacketIndex) (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
    selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
  have heq (z : ℝ×ℝ) : (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)=
      ((∑ q∈initial, V q z)-(∑ q∈middle, V q z))+
      ((∑ q∈middle, V q z)-(∑ q∈remaining, V q z)) := by abel
  have hI := (hDensityStep.2.2.1.add hRemoved.1).congr
    (Filter.Eventually.of_forall fun z => (heq z).symm)
  refine ⟨remaining,hr.trans hm,fun q hq => hDensityStep.2.1 q (hr hq),hsmall,hI,?_⟩
  calc
    _ ≤ ∫ z in E, ‖(∑ q∈initial, V q z)-(∑ q∈middle, V q z)‖+
        ‖(∑ q∈middle, V q z)-(∑ q∈remaining, V q z)‖ ∂volume.prod volume :=
      integral_mono hI.norm (hDensityStep.2.2.1.norm.add hRemoved.1.norm)
        (fun z => by rw [heq]; exact norm_add_le _ _)
    _ = (∫ z in E, ‖(∑ q∈initial, V q z)-(∑ q∈middle, V q z)‖ ∂volume.prod volume)+
        (∫ z in E, ‖(∑ q∈middle, V q z)-(∑ q∈remaining, V q z)‖ ∂volume.prod volume) :=
      integral_add hDensityStep.2.2.1.norm hRemoved.1.norm
    _ ≤ _ := add_le_add hDensityStep.2.2.2 hSizeBound

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.PacketLatticeData.exists_ordinary_capped_removal_step_oai := @OAI.LipschitzHilbert.PacketLatticeData.exists_ordinary_capped_removal_step_oai
