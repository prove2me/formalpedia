-- Prove2me | solution 1 for OAI.LipschitzHilbert.PacketRepresentation.lineConjugation_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:04:19.601697+00:00
-- url     : https://prove2.me/submissions/6bffb429-b69c-4646-a9b4-12a1f6b5c638

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_PacketRepresentation_comparableCommutatorSum_energy
import Theorems.Thm_OAI_LipschitzHilbert_PacketRepresentation_lineSamplingGenerator_commutator_bound

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
end OAICompat434

end OAI
end

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

theorem weighted_integral_sum_square {Ω ι E : Type*} [MeasurableSpace Ω]
    [Fintype ι] [NormedAddCommGroup E] (μ : Measure Ω)
    (F : ι → Ω → E) (hF : ∀ j, MemLp (F j) 2 μ)
    (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    (∫ x, ‖∑ j, F j x‖ ^ 2 ∂μ) ≤
      (∑ j, w j) * ∑ j, (∫ x, ‖F j x‖ ^ 2 ∂μ) / w j := by
  have hsum : MemLp (fun x => ∑ j, F j x) 2 μ := by
    simpa only [Finset.sum_apply] using memLp_finsetSum Finset.univ (fun j _ => hF j)
  have hint (j : ι) : Integrable (fun x => ‖F j x‖ ^ 2 / w j) μ :=
    ((hF j).integrable_norm_pow (by decide : 2 ≠ 0)).div_const _
  calc
    _ ≤ ∫ x, (∑ j, w j) * ∑ j, ‖F j x‖ ^ 2 / w j ∂μ :=
      integral_mono (hsum.integrable_norm_pow (by decide : 2 ≠ 0))
        ((integrable_finsetSum _ (fun j _ => hint j)).const_mul _)
        (fun x => weighted_sum_norm_square (fun j => F j x) w hw)
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => hint j)]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact integral_div _ _

theorem finite_energy_schur {Ω ι κ E : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] [NormedAddCommGroup E]
    (μ : Measure Ω) (F : ι → κ → Ω → E)
    (hF : ∀ i j, MemLp (F i j) 2 μ) (a : ι → κ → ℝ)
    (ha : ∀ i j, 0 < a i j) (b : κ → ℝ) (hb : ∀ j, 0 ≤ b j)
    {R C : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ i, ∑ j, a i j ≤ R) (hcol : ∀ j, ∑ i, a i j ≤ C)
    (hbound : ∀ i j, (∫ x, ‖F i j x‖ ^ 2 ∂μ) ≤ a i j ^ 2 * b j) :
    (∑ i, ∫ x, ‖∑ j, F i j x‖ ^ 2 ∂μ) ≤ R * C * ∑ j, b j := by
  have hcell (i : ι) (j : κ) :
      (∫ x, ‖F i j x‖ ^ 2 ∂μ) / a i j ≤ a i j * b j := by
    apply (div_le_iff₀ (ha i j)).mpr
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hbound i j
  have hrowbound (i : ι) : (∫ x, ‖∑ j, F i j x‖ ^ 2 ∂μ) ≤
      R * ∑ j, a i j * b j := by
    calc
      _ ≤ (∑ j, a i j) * ∑ j, (∫ x, ‖F i j x‖ ^ 2 ∂μ) / a i j :=
        weighted_integral_sum_square μ (F i) (hF i) (a i) (ha i)
      _ ≤ (∑ j, a i j) * ∑ j, a i j * b j :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hcell i j))
          (Finset.sum_nonneg (fun j _ => (ha i j).le))
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i)
        (Finset.sum_nonneg (fun j _ => mul_nonneg (ha i j).le (hb j)))
  calc
    _ ≤ ∑ i, R * ∑ j, a i j * b j := Finset.sum_le_sum (fun i _ => hrowbound i)
    _ = R * ∑ j, (∑ i, a i j) * b j := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ R * ∑ j, C * b j := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcol j) (hb j))) hR
    _ = _ := by rw [← Finset.mul_sum, mul_assoc]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteTimeKernelMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first absolute moment of the retained time kernel is bounded
by twice the largest scale, independently of the number of scales. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem schwartz_first_absolute_moment_integrable (k : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ => |t| *‖k t‖) := by
  simpa only [pow_one,Real.norm_eq_abs] using k.integrable_pow_mul volume 1

theorem scaledTimeKernel_moment1_pointwise (k : ℝ → ℂ) (l t : ℝ) (hl : 0<l) :
    |t| *‖scaledTimeKernel k l t‖=|t/l| *‖k (t/l)‖ := by
  simp only [scaledTimeKernel,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg hl.le,abs_div,abs_of_pos hl]
  ring

theorem scaledTimeKernel_moment1 (k : SchwartzMap ℝ ℂ) (l : ℝ) (hl : 0<l) :
    (∫ t, |t| *‖scaledTimeKernel k l t‖)=l*(∫ t, |t| *‖k t‖) := by
  simp_rw [scaledTimeKernel_moment1_pointwise k l _ hl]
  rw [Measure.integral_comp_div (fun t => |t| *‖k t‖) l,abs_of_pos hl,smul_eq_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularCutoffConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit real annular cutoffs and the low-pass difference underlying
the geometric frequency partition. All supports stay inside fixed bands. -/
noncomputable section
open MeasureTheory Function Set
namespace LipschitzHilbert.PacketRepresentation

theorem reassemblyLow_one (s : ℝ) (hs : |s|≤1) : reassemblyLow s=1 := by
  have hd : s∈Metric.closedBall (0:ℝ) reassemblyLowBump.rIn := by
    simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,reassemblyLowBump] using hs
  simp only [reassemblyLow_apply,reassemblyLowBump.one_of_mem_closedBall hd,Complex.ofReal_one]

theorem reassemblyLow_zero (s : ℝ) (hs : 13/12≤|s|) : reassemblyLow s=0 := by
  have hd : reassemblyLowBump.rOut≤dist s 0 := by
    simpa only [Real.dist_eq,sub_zero,reassemblyLowBump] using hs
  simp only [reassemblyLow_apply,reassemblyLowBump.zero_of_le_dist hd,Complex.ofReal_zero]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularSquareBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric annular cutoffs have a uniform finite square sum. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem reassemblyLow_norm (s : ℝ) : ‖reassemblyLow s‖≤1 := by
  rw [reassemblyLow_apply,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg reassemblyLowBump.nonneg]
  exact reassemblyLowBump.le_one

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicSmoothCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine binary low-pass difference for the dyadic commutator
proof, with its scale-independent Fourier square bound. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem dyadicDifference_small (x : ℝ) (hx : |x|≤1) : dyadicDifference x=0 := by
  have hh : |x/2|≤1 := by rw [abs_div]; norm_num; linarith
  simp only [dyadicDifference_apply,reassemblyLow_one x hx,reassemblyLow_one _ hh,sub_self]

theorem dyadicDifference_large (x : ℝ) (hx : 13/6≤|x|) : dyadicDifference x=0 := by
  have hh : 13/12≤|x/2| := by rw [abs_div]; norm_num; linarith
  simp only [dyadicDifference_apply,reassemblyLow_zero x (by linarith),
    reassemblyLow_zero _ hh,sub_self]

theorem dyadicDifference_norm (x : ℝ) : ‖dyadicDifference x‖≤2 := by
  rw [dyadicDifference_apply]
  exact (norm_sub_le _ _).trans (by linarith [reassemblyLow_norm (x/2),reassemblyLow_norm x])

theorem dyadicDifference_separated (j k : ℤ) (x : ℝ) (hjk : j+2≤k) :
    dyadicDifference ((2:ℝ)^j*x)=0 ∨ dyadicDifference ((2:ℝ)^k*x)=0 := by
  by_contra hn
  have hj : dyadicDifference ((2:ℝ)^j*x)≠0 := fun h => hn (Or.inl h)
  have hk : dyadicDifference ((2:ℝ)^k*x)≠0 := fun h => hn (Or.inr h)
  have hjlo : 1 < |(2:ℝ)^j*x| := lt_of_not_ge (fun h => hj (dyadicDifference_small _ h))
  have hkhi : |(2:ℝ)^k*x|<13/6 := lt_of_not_ge (fun h => hk (dyadicDifference_large _ h))
  have hp : (2:ℝ)^j*4≤(2:ℝ)^k := by
    calc
      _ = (2:ℝ)^(j+2) := by rw [zpow_add₀ (by norm_num)]; norm_num
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) hjk
  have hm := mul_le_mul_of_nonneg_right hp (abs_nonneg x)
  have ha (n : ℤ) : |(2:ℝ)^n*x|=(2:ℝ)^n*|x| := by
    rw [abs_mul,abs_of_pos (zpow_pos (by norm_num) _)]
  rw [ha j] at hjlo
  rw [ha k] at hkhi
  nlinarith only [hm,hjlo,hkhi]

theorem dyadicDifference_nonzero_count (I : Finset ℤ) (x : ℝ) :
    (I.filter (fun n => dyadicDifference ((2:ℝ)^n*x)≠0)).card≤3 := by
  classical
  let A := I.filter (fun n => dyadicDifference ((2:ℝ)^n*x)≠0)
  change A.card≤3
  by_cases hne : A.Nonempty
  · obtain ⟨j,hj⟩ := hne
    have hjnz := (Finset.mem_filter.mp hj).2
    have hsub : A⊆Finset.Icc (j-1) (j+1) := by
      intro k hk
      have hknz := (Finset.mem_filter.mp hk).2
      apply Finset.mem_Icc.mpr
      constructor
      · by_contra hn
        exact (dyadicDifference_separated k j x (by omega)).elim hknz hjnz
      · by_contra hn
        exact (dyadicDifference_separated j k x (by omega)).elim hjnz hknz
    apply (Finset.card_le_card hsub).trans
    rw [Int.card_Icc]
    omega
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty]
    omega

theorem dyadicDifference_square_sum (I : Finset ℤ) (x : ℝ) :
    (∑ n∈I, ‖dyadicDifference ((2:ℝ)^n*x)‖^2)≤12 := by
  classical
  let A := I.filter (fun n => dyadicDifference ((2:ℝ)^n*x)≠0)
  have he : (∑ n∈I, ‖dyadicDifference ((2:ℝ)^n*x)‖^2)=
      ∑ n∈A, ‖dyadicDifference ((2:ℝ)^n*x)‖^2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnA
    have hz : dyadicDifference ((2:ℝ)^n*x)=0 := by
      by_contra h
      exact hnA (Finset.mem_filter.mpr ⟨hn,h⟩)
    simp only [hz,norm_zero,zero_pow (by decide : 2≠0)]
  rw [he]
  calc
    _ ≤ ∑ _n∈A, (4:ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      simpa only [show (2:ℝ)^2=4 by norm_num] using
        pow_le_pow_left₀ (norm_nonneg _) (dyadicDifference_norm ((2:ℝ)^n*x)) 2
    _ = (A.card:ℝ)*4 := by simp
    _ ≤ 12 := by
      have hc : (A.card:ℝ)≤3 := by exact_mod_cast dyadicDifference_nonzero_count I x
      linarith

end LipschitzHilbert.PacketRepresentation

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineFrequencyProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smooth frequency projections on the line and their finite
square-function bound. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProjection_fourier (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (f : SchwartzMap ℝ ℂ) (eta : ℝ) :
    (𝓕 (lineSchwartzProjection q W hW f)) eta=q (W*eta)*(𝓕 f) eta := by
  simp only [lineSchwartzProjection,FourierTransform.fourier_fourierInv_eq]
  rw [SchwartzMap.smulLeftCLM_apply_apply (dilatedSlopeWindow q W hW).hasTemperateGrowth,
    dilatedSlopeWindow_apply,smul_eq_mul]

theorem lineSchwartzProjection_energy (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (M : ℝ) (hM : ∀ eta, ‖q eta‖≤M) (f : SchwartzMap ℝ ℂ) :
    (∫ x, ‖lineSchwartzProjection q W hW f x‖^2)≤M^2*∫ x, ‖f x‖^2 := by
  rw [←SchwartzMap.integral_norm_sq_fourier (lineSchwartzProjection q W hW f),
    ←SchwartzMap.integral_norm_sq_fourier f,←integral_const_mul]
  apply integral_mono
  · exact ((𝓕 (lineSchwartzProjection q W hW f) : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  · exact (((𝓕 f : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)).const_mul _
  · intro x
    change ‖(𝓕 (lineSchwartzProjection q W hW f)) x‖^2≤M^2*‖(𝓕 f) x‖^2
    rw [lineSchwartzProjection_fourier,norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hM (W*x)) 2) (sq_nonneg _)

theorem lineSchwartzProjection_frame {ι : Type*} (I : Finset ι)
    (q : ι → SchwartzMap ℝ ℂ) (W : ι → ℝ) (hW : ∀ i, W i≠0)
    (M : ℝ) (hM : ∀ eta, (∑ i∈I, ‖q i (W i*eta)‖^2)≤M)
    (f : SchwartzMap ℝ ℂ) :
    (∑ i∈I, ∫ x, ‖lineSchwartzProjection (q i) (W i) (hW i) f x‖^2)≤
      M*∫ x, ‖f x‖^2 := by
  have hi (i : ι) : Integrable (fun eta =>
      ‖(𝓕 (lineSchwartzProjection (q i) (W i) (hW i) f)) eta‖^2) :=
    ((𝓕 (lineSchwartzProjection (q i) (W i) (hW i) f) : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  have hf : Integrable (fun eta => ‖(𝓕 f) eta‖^2) :=
    ((𝓕 f : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  calc
    _ = ∑ i∈I, ∫ eta, ‖(𝓕 (lineSchwartzProjection (q i) (W i) (hW i) f)) eta‖^2 :=
      Finset.sum_congr rfl (fun i _ => (SchwartzMap.integral_norm_sq_fourier _).symm)
    _ = ∫ eta, ∑ i∈I, ‖(𝓕 (lineSchwartzProjection (q i) (W i) (hW i) f)) eta‖^2 :=
      (integral_finsetSum I (fun i _ => hi i)).symm
    _ ≤ M*∫ eta, ‖(𝓕 f) eta‖^2 := by
      rw [←integral_const_mul]
      apply integral_mono (integrable_finsetSum I (fun i _ => hi i)) (hf.const_mul M)
      intro eta
      change (∑ i∈I, ‖(𝓕 (lineSchwartzProjection (q i) (W i) (hW i) f)) eta‖^2)≤_
      simp only [lineSchwartzProjection_fourier,norm_mul,mul_pow]
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hM eta) (sq_nonneg _)
    _ = _ := by rw [SchwartzMap.integral_norm_sq_fourier]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineProjectionKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The line Fourier projection is the actual convolution with its
inverse-Fourier kernel. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProjection_eq_convolution (q : SchwartzMap ℝ ℂ)
    (W : ℝ) (hW : W≠0) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    lineSchwartzProjection q W hW f x=lineConvolution (lineProjectionKernel q W hW) f x := by
  have he : lineSchwartzProjection q W hW f=
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (lineProjectionKernel q W hW) f := by
    apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
    ext eta
    change (𝓕 (lineSchwartzProjection q W hW f)) eta=
      (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (lineProjectionKernel q W hW) f)) eta
    rw [lineSchwartzProjection_fourier,SchwartzMap.fourier_convolution]
    simp only [SchwartzMap.pairing_apply_apply,lineProjectionKernel,
      FourierTransform.fourier_fourierInv_eq,dilatedSlopeWindow_apply,ContinuousLinearMap.mul_apply']
  rw [he,SchwartzMap.convolution_apply,convolution_def]
  rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineKernelScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual line projection kernel has the expected physical scale,
including its exact first absolute moment. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineProjectionKernel_moment1 (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) :
    (∫ t, |t| *‖lineProjectionKernel q W hW.ne' t‖)=
      W*(∫ t, |t| *‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖) := by
  have he (t : ℝ) : lineProjectionKernel q W hW.ne' t=
      scaledTimeKernel (𝓕⁻ q : SchwartzMap ℝ ℂ) W t := by
    rw [lineProjectionKernel_eq_scaled]
    exact scaledSchwartzKernel_apply q W hW t
  simp_rw [he]
  exact scaledTimeKernel_moment1 (𝓕⁻ q) W hW

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineKernelCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact kernel mass, cancellation, and uniform Lipschitz approximation
for the actual line projections. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineProjectionKernel_integral (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0) :
    (∫ t, lineProjectionKernel q W hW t)=q 0 := by
  have he : (𝓕 (lineProjectionKernel q W hW) : SchwartzMap ℝ ℂ) 0=q 0 := by
    simp only [lineProjectionKernel,FourierTransform.fourier_fourierInv_eq,dilatedSlopeWindow_apply,mul_zero]
  rw [SchwartzMap.fourier_coe,Real.fourier_eq] at he
  simpa only [inner_zero_right,neg_zero,Real.fourierChar.map_zero_eq_one,one_smul] using he

theorem lineConvolution_centered_bound (K : SchwartzMap ℝ ℂ) (b : ℝ → ℂ)
    (hbm : Measurable b) (B : ℝ) (hb : ∀ x, ‖b x‖≤B) (L : ℝ)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) (x : ℝ) :
    ‖lineConvolution K b x-(∫ t, K t)*b x‖≤L*(∫ t, |t| *‖K t‖) := by
  have h1 := lineConvolution_integrand_of_bounded K b K.integrable hbm B hb x
  have he : lineConvolution K b x-(∫ t, K t)*b x=
      ∫ t, K t*(b (x-t)-b x) := by
    simp_rw [mul_sub]
    rw [integral_sub h1 (K.integrable.mul_const (b x)),integral_mul_const]
    rfl
  rw [he]
  have hn := norm_integral_le_of_norm_le
    ((schwartz_first_absolute_moment_integrable K).const_mul L)
    (Filter.Eventually.of_forall (fun t => show ‖K t*(b (x-t)-b x)‖≤L*(|t| *‖K t‖) from by
      rw [norm_mul]
      have hh := hLip (x-t) x
      simp only [sub_sub_cancel_left,abs_neg] at hh
      calc
        _ ≤ ‖K t‖*(L*|t|) := mul_le_mul_of_nonneg_left hh (norm_nonneg _)
        _ = _ := by ring))
  simpa only [integral_const_mul] using hn

theorem lineProjection_centered_bound (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W)
    (b : ℝ → ℂ) (hbm : Measurable b) (B : ℝ) (hb : ∀ x, ‖b x‖≤B)
    (L : ℝ) (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) (x : ℝ) :
    ‖lineConvolution (lineProjectionKernel q W hW.ne') b x-q 0*b x‖≤
      L*W*(∫ t, |t| *‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖) := by
  have hh := lineConvolution_centered_bound (lineProjectionKernel q W hW.ne') b hbm B hb L hLip x
  rw [lineProjectionKernel_integral,lineProjectionKernel_moment1 q W hW] at hh
  simpa only [mul_assoc] using hh

theorem dyadicProjection_lipschitz_bound (W : ℝ) (hW : 0<W)
    (b : ℝ → ℂ) (hbm : Measurable b) (B : ℝ) (hb : ∀ x, ‖b x‖≤B)
    (L : ℝ) (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) (x : ℝ) :
    ‖lineConvolution (lineProjectionKernel dyadicDifference W hW.ne') b x‖≤
      L*W*(∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖) := by
  have hh := lineProjection_centered_bound dyadicDifference W hW b hbm B hb L hLip x
  simpa only [dyadicDifference_small 0 (by norm_num),zero_mul,sub_zero] using hh

theorem lowpassProjection_lipschitz_approximation (W : ℝ) (hW : 0<W)
    (b : ℝ → ℂ) (hbm : Measurable b) (B : ℝ) (hb : ∀ x, ‖b x‖≤B)
    (L : ℝ) (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) (x : ℝ) :
    ‖lineConvolution (lineProjectionKernel reassemblyLow W hW.ne') b x-b x‖≤
      L*W*(∫ t, |t| *‖(𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ) t‖) := by
  have hh := lineProjection_centered_bound reassemblyLow W hW b hbm B hb L hLip x
  simpa only [reassemblyLow_one 0 (by norm_num),one_mul] using hh

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SignedAnnularSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All signed finite annular multipliers have the same Mihlin bounds.
The proof uses only the fixed support annulus and its finite overlap. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

theorem iteratedDeriv_tsupport_subset (q : ℝ → ℂ) (r : ℕ) :
    tsupport (iteratedDeriv r q) ⊆ tsupport q := by
  induction r with
  | zero => simp only [iteratedDeriv_zero,subset_refl]
  | succ r ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FourierKernelFirstMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative first absolute moment from the zeroth and third
L1 derivatives of a Schwartz multiplier. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem schwartzDerivative_apply (r : ℕ) (q : SchwartzMap ℝ ℂ) :
    (schwartzDerivative r q : ℝ → ℂ)=iteratedDeriv r q := by
  induction r with
  | zero => rfl
  | succ r ih =>
    funext x
    change deriv (schwartzDerivative r q) x=iteratedDeriv (r+1) q x
    rw [ih,iteratedDeriv_succ]

theorem fourier_schwartzDerivative (r : ℕ) (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    (𝓕 (schwartzDerivative r q)) x=
      ((2*Real.pi*Complex.I*(x:ℂ))^r)*(𝓕 q) x := by
  induction r with
  | zero => simp only [schwartzDerivative,pow_zero,one_mul]
  | succ r ih =>
    have hd := congrFun (Real.fourier_deriv (schwartzDerivative r q).integrable
      (schwartzDerivative r q).differentiable
      (SchwartzMap.derivCLM ℂ ℂ (schwartzDerivative r q)).integrable) x
    change (𝓕 (SchwartzMap.derivCLM ℂ ℂ (schwartzDerivative r q))) x=
      (2*Real.pi*Complex.I*(x:ℂ))* (𝓕 (schwartzDerivative r q)) x at hd
    rw [schwartzDerivative,hd,ih]
    ring

theorem schwartz_fourier_norm_le_l1 (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖(𝓕 q) x‖≤∫ y, ‖q y‖ := by
  change ‖𝓕 (q : ℝ → ℂ) x‖≤_
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem schwartz_fourier_weighted_norm (r : ℕ) (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    (2*Real.pi)^r*|x|^r*‖(𝓕 q) x‖≤∫ y, ‖schwartzDerivative r q y‖ := by
  have hb := schwartz_fourier_norm_le_l1 (schwartzDerivative r q) x
  rw [fourier_schwartzDerivative,norm_mul,norm_pow] at hb
  have hn : ‖2*Real.pi*Complex.I*(x:ℂ)‖=2*Real.pi*|x| := by
    simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]
  rw [hn,mul_pow] at hb
  exact hb

theorem firstMoment_bound_of_decay (K : ℝ → ℂ) (hK : Measurable K)
    (B C : ℝ) (hB : 0≤B) (hC : 0≤C)
    (hzero : ∀ x, ‖K x‖≤B) (hthree : ∀ x, |x|^3*‖K x‖≤C) :
    Integrable (fun x => |x| *‖K x‖) ∧
      (∫ x, |x| *‖K x‖)≤2*(B+C)*Real.pi := by
  have hdom (x : ℝ) : |x| *‖K x‖≤2*(B+C)*(1+x^2)⁻¹ := by
    have hp : 0<1+x^2 := by positivity
    rw [←div_eq_mul_inv,le_div_iff₀ hp]
    have hx2 : x^2=|x|^2 := (sq_abs x).symm
    rw [hx2]
    by_cases hx : |x|≤1
    · have ha : |x| *‖K x‖≤B :=
        (mul_le_mul_of_nonneg_right hx (norm_nonneg _)).trans (by simpa using hzero x)
      have hs : |x|^2≤1 := by nlinarith [abs_nonneg x]
      calc
        _ ≤ B*(1+|x|^2) := mul_le_mul_of_nonneg_right ha (by positivity)
        _ ≤ 2*B := by nlinarith
        _ ≤ _ := by linarith
    · have hx' : 1≤|x| := le_of_not_ge hx
      have hcube : |x|≤|x|^3 := by nlinarith [sq_nonneg (|x|-1)]
      have ha : |x| *‖K x‖≤C :=
        (mul_le_mul_of_nonneg_right hcube (norm_nonneg _)).trans (hthree x)
      nlinarith only [ha,hthree x,hB]
  have hint : Integrable (fun x : ℝ => 2*(B+C)*(1+x^2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (2*(B+C))
  have hmeas : AEStronglyMeasurable (fun x => |x| *‖K x‖) :=
    (show Measurable (fun x : ℝ => |x| *‖K x‖) from
      continuous_abs.measurable.mul hK.norm).aestronglyMeasurable
  have hi : Integrable (fun x => |x| *‖K x‖) := hint.mono' hmeas
    (Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (abs_nonneg x) (norm_nonneg _))] using hdom x))
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ x : ℝ, 2*(B+C)*(1+x^2)⁻¹ := integral_mono hi hint hdom
    _ = _ := by rw [integral_const_mul,integral_univ_inv_one_add_sq]

theorem schwartz_fourier_firstMoment_bound (q : SchwartzMap ℝ ℂ) :
    (∫ x, |x| *‖(𝓕 q) x‖)≤
      2*((∫ y, ‖q y‖)+(∫ y, ‖schwartzDerivative 3 q y‖)/(2*Real.pi)^3)*Real.pi := by
  have hp : 0<(2*Real.pi)^3 := by positivity
  apply (firstMoment_bound_of_decay (𝓕 q : SchwartzMap ℝ ℂ) (𝓕 q : SchwartzMap ℝ ℂ).continuous.measurable
    (∫ y, ‖q y‖) ((∫ y, ‖schwartzDerivative 3 q y‖)/(2*Real.pi)^3)
    (integral_nonneg (fun _ => norm_nonneg _)) (by positivity)
    (schwartz_fourier_norm_le_l1 q) (fun x => ?_)).2
  apply (le_div_iff₀ hp).2
  have h := schwartz_fourier_weighted_norm 3 q x
  nlinarith only [h]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LocalizedMihlinProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform derivative bounds for a rescaled multiplier after restriction
to a fixed annulus. These are the bounds needed for its kernel moment. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem annularDerivativeBudget_nonneg (rho : SchwartzMap ℝ ℂ) (r : ℕ) :
    0≤annularDerivativeBudget rho r :=
  Finset.sum_nonneg (fun _ _ => by positivity)

theorem dilated_mihlin_derivative_bound (m : SchwartzMap ℝ ℂ) (W A : ℝ)
    (hW : 0<W) (r : ℕ)
    (hm : ∀ y, |y|^r*‖iteratedDeriv r m y‖≤A)
    (x : ℝ) (hx : 1/2≤|x|) :
    ‖iteratedDeriv r (dilatedSlopeWindow m W hW.ne') x‖≤2^r*A := by
  have he : (dilatedSlopeWindow m W hW.ne' : ℝ → ℂ)=fun y => m (W*y) := rfl
  rw [he,iteratedDeriv_comp_const_smul (m.smooth r),norm_smul,
    Real.norm_eq_abs,abs_of_pos (pow_pos hW r)]
  have habs : |W*x|=W*|x| := by rw [abs_mul,abs_of_pos hW]
  have hp : 1≤(2*|x|)^r := one_le_pow₀ (show (1:ℝ)≤2*|x| by linarith)
  calc
    _ ≤ (2*|x|)^r*(W^r*‖iteratedDeriv r m (W*x)‖) :=
      le_mul_of_one_le_left (by positivity) hp
    _ = 2^r*(|W*x|^r*‖iteratedDeriv r m (W*x)‖) := by rw [habs,mul_pow,mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hm (W*x)) (by positivity)

theorem localizedMihlinProfile_derivative_bound (m rho : SchwartzMap ℝ ℂ)
    (W A : ℝ) (hW : 0<W) (hA : 0≤A) (r : ℕ)
    (hm : ∀ j ≤ r, ∀ y, |y|^j*‖iteratedDeriv j m y‖≤A)
    (hrho : tsupport rho ⊆ {x : ℝ | 1/2≤|x|}) (x : ℝ) :
    ‖iteratedDeriv r (localizedMihlinProfile m rho W hW.ne') x‖≤
      A*annularDerivativeBudget rho r := by
  let g := dilatedSlopeWindow m W hW.ne'
  have he : (localizedMihlinProfile m rho W hW.ne' : ℝ → ℂ)=
      (g : ℝ → ℂ)*rho := by
        funext y
        exact localizedMihlinProfile_apply m rho W hW.ne' y
  rw [he,iteratedDeriv_mul (g.smooth r).contDiffAt (rho.smooth r).contDiffAt]
  apply (norm_sum_le _ _).trans
  unfold annularDerivativeBudget
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjr : j ≤ r := by have := Finset.mem_range.mp hj; omega
  by_cases hz : iteratedDeriv (r-j) rho x=0
  · simp only [hz,mul_zero,norm_zero]
    positivity
  · have hx := hrho (iteratedDeriv_tsupport_subset _ (r-j) (subset_closure hz))
    have hg := dilated_mihlin_derivative_bound m W A hW j (hm j hjr) x hx
    have hb : ‖iteratedDeriv (r-j) rho x‖≤SchwartzMap.seminorm ℝ 0 (r-j) rho := by
      simpa only [pow_zero,one_mul] using rho.le_seminorm' ℝ 0 (r-j) x
    rw [norm_mul,norm_mul,Complex.norm_natCast]
    calc
      _ ≤ (r.choose j:ℝ)*(2^j*A)*SchwartzMap.seminorm ℝ 0 (r-j) rho :=
        mul_le_mul (mul_le_mul_of_nonneg_left hg (by positivity)) hb
          (norm_nonneg _) (by positivity)
      _ = _ := by ring

theorem schwartz_l1_bound_of_support (q : SchwartzMap ℝ ℂ) (B : ℝ) (_hB : 0≤B)
    (hq : tsupport q ⊆ Icc (-2:ℝ) 2) (hb : ∀ x, ‖q x‖≤B) :
    (∫ x, ‖q x‖)≤4*B := by
  have hz : ∀ x, x∉Icc (-2:ℝ) 2 → ‖q x‖=0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hq h)),norm_zero]
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  calc
    _ ≤ ∫ _x in Icc (-2:ℝ) 2, B := integral_mono q.integrable.norm.integrableOn
      (integrableOn_const measure_Icc_lt_top.ne) (fun x => hb x)
    _ = _ := by
      rw [setIntegral_const,Real.volume_real_Icc_of_le (by norm_num),smul_eq_mul]
      norm_num

theorem schwartzDerivative_l1_bound_of_support (q : SchwartzMap ℝ ℂ) (r : ℕ)
    (B : ℝ) (hB : 0≤B) (hq : tsupport q ⊆ Icc (-2:ℝ) 2)
    (hb : ∀ x, ‖iteratedDeriv r q x‖≤B) :
    (∫ x, ‖schwartzDerivative r q x‖)≤4*B := by
  apply schwartz_l1_bound_of_support _ B hB
  · rw [schwartzDerivative_apply]
    exact (iteratedDeriv_tsupport_subset q r).trans hq
  · simpa only [schwartzDerivative_apply] using hb

theorem localizedMihlinProfile_tsupport (m rho : SchwartzMap ℝ ℂ)
    (W : ℝ) (hW : W≠0) :
    tsupport (localizedMihlinProfile m rho W hW) ⊆ tsupport rho := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  apply subset_closure
  intro hz
  exact hx (by rw [localizedMihlinProfile_apply,hz,mul_zero])

theorem localizedMihlinProfile_l1 (m rho : SchwartzMap ℝ ℂ)
    (W A : ℝ) (hW : 0<W) (hA : 0≤A) (r : ℕ)
    (hm : ∀ j ≤ r, ∀ y, |y|^j*‖iteratedDeriv j m y‖≤A)
    (hrho : tsupport rho ⊆ {x : ℝ | 1/2≤|x|})
    (hsupp : tsupport rho ⊆ Icc (-2:ℝ) 2) :
    (∫ x, ‖schwartzDerivative r (localizedMihlinProfile m rho W hW.ne') x‖)≤
      4*(A*annularDerivativeBudget rho r) := by
  apply schwartzDerivative_l1_bound_of_support
  · exact mul_nonneg hA (annularDerivativeBudget_nonneg rho r)
  · exact (localizedMihlinProfile_tsupport m rho W hW.ne').trans hsupp
  · exact localizedMihlinProfile_derivative_bound m rho W A hW hA r hm hrho

theorem localizedKernelFirstMomentConstant_nonneg (rho : SchwartzMap ℝ ℂ) :
    0≤localizedKernelFirstMomentConstant rho := by
  unfold localizedKernelFirstMomentConstant
  have h0 := annularDerivativeBudget_nonneg rho 0
  have h3 := annularDerivativeBudget_nonneg rho 3
  positivity

theorem localizedMihlinProfile_fourier_firstMoment (m rho : SchwartzMap ℝ ℂ)
    (W A : ℝ) (hW : 0<W) (hA : 0≤A)
    (hm : ∀ j≤3, ∀ y, |y|^j*‖iteratedDeriv j m y‖≤A)
    (hrho : tsupport rho ⊆ {x : ℝ | 1/2≤|x|})
    (hsupp : tsupport rho ⊆ Icc (-2:ℝ) 2) :
    (∫ x, |x| *‖(𝓕 (localizedMihlinProfile m rho W hW.ne')) x‖)≤
      A*localizedKernelFirstMomentConstant rho := by
  let q := localizedMihlinProfile m rho W hW.ne'
  have h0 := localizedMihlinProfile_l1 m rho W A hW hA 0
    (fun j hj => hm j (by omega)) hrho hsupp
  have h3 := localizedMihlinProfile_l1 m rho W A hW hA 3 hm hrho hsupp
  have h := schwartz_fourier_firstMoment_bound q
  change (∫ x, ‖q x‖)≤_ at h0
  apply h.trans
  have hp : 0<(2*Real.pi)^3 := by positivity
  have hd := div_le_div_of_nonneg_right h3 hp.le
  have hm' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add h0 hd)
    (by norm_num : (0:ℝ)≤2)) Real.pi_pos.le
  unfold localizedKernelFirstMomentConstant
  convert hm' using 1 <;> first | rfl | ring

theorem schwartz_fourierInv_firstMoment_eq (q : SchwartzMap ℝ ℂ) :
    (∫ x, |x| *‖(𝓕⁻ q) x‖)=(∫ x, |x| *‖(𝓕 q) x‖) := by
  have he : (fun x : ℝ => |x| *‖(𝓕⁻ q) x‖)=
      fun x => |-x| *‖(𝓕 q) (-x)‖ := by
    funext x
    rw [abs_neg]
    rfl
  rw [he]
  calc
    _ = ∫ x : ℝ, |(-1:ℝ)*x| *‖(𝓕 q) ((-1:ℝ)*x)‖ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [show (-1:ℝ)*x= -x by ring]
    _ = _ := by
      simpa only [inv_neg,inv_one,abs_neg,abs_one,one_smul] using
        Measure.integral_comp_mul_left (fun x : ℝ => |x| *‖(𝓕 q) x‖) (-1)

theorem localizedMihlinProfile_kernel_firstMoment (m rho : SchwartzMap ℝ ℂ)
    (W A : ℝ) (hW : 0<W) (hA : 0≤A)
    (hm : ∀ j≤3, ∀ y, |y|^j*‖iteratedDeriv j m y‖≤A)
    (hrho : tsupport rho ⊆ {x : ℝ | 1/2≤|x|})
    (hsupp : tsupport rho ⊆ Icc (-2:ℝ) 2) :
    (∫ x, |x| *‖(𝓕⁻ (localizedMihlinProfile m rho W hW.ne')) x‖)≤
      A*localizedKernelFirstMomentConstant rho := by
  rw [schwartz_fourierInv_firstMoment_eq]
  exact localizedMihlinProfile_fourier_firstMoment m rho W A hW hA hm hrho hsupp

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineCommutatorEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The L2 kernel commutator estimate for multiplication by a bounded
Lipschitz function. The cost is its Lipschitz bound times the first moment. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem lineMoment_dominated_energy (K : SchwartzMap ℝ ℂ) (h : SchwartzMap ℝ ℂ)
    (F : ℝ → ℂ) (hFm : Measurable F) (L : ℝ)
    (hdom : ∀ x, ‖F x‖≤L*(∫ t, |t| *‖K t‖*‖h (x-t)‖)) :
    MemLp F 2 volume ∧ (∫ x, ‖F x‖^2)≤
      L^2*(∫ t, |t| *‖K t‖)^2*(∫ x, ‖h x‖^2) := by
  let a := fun t => ((|t| *‖K t‖:ℝ):ℂ)
  let v := fun x => ((‖h x‖:ℝ):ℂ)
  have ha (t : ℝ) : ‖a t‖=|t| *‖K t‖ := by
    simp only [a,Complex.norm_real,Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
  have hv (x : ℝ) : ‖v x‖=‖h x‖ := by
    simp only [v,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
  have hai : Integrable a := (schwartz_first_absolute_moment_integrable K).ofReal
  have ham : Measurable a := by dsimp [a]; fun_prop
  have hvm : Measurable v := by dsimp [v]; fun_prop
  have hvlp : MemLp v 2 volume := (h.memLp 2 volume).norm.ofReal
  have hc := lineConvolution_energy_bound a hai ham v hvm hvlp
  have he (x : ℝ) : ‖lineConvolution a v x‖=∫ t, |t| *‖K t‖*‖h (x-t)‖ := by
    have hh : lineConvolution a v x=((∫ t, |t| *‖K t‖*‖h (x-t)‖:ℝ):ℂ) := by
      unfold lineConvolution
      simp only [a,v,←Complex.ofReal_mul]
      exact integral_ofReal
    rw [hh,Complex.norm_real,Real.norm_of_nonneg]
    exact integral_nonneg (fun _ => by positivity)
  have hp (x : ℝ) : ‖F x‖^2≤L^2*‖lineConvolution a v x‖^2 := by
    rw [←mul_pow,he]
    exact pow_le_pow_left₀ (norm_nonneg _) (hdom x) 2
  have hi : Integrable (fun x => ‖F x‖^2) :=
    ((hc.1.integrable_norm_pow (by decide : 2≠0)).const_mul (L^2)).mono'
      (hFm.norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hp x)
  refine ⟨(memLp_two_iff_integrable_sq_norm hFm.aestronglyMeasurable).mpr hi,?_⟩
  calc
    _ ≤ ∫ x, L^2*‖lineConvolution a v x‖^2 :=
      integral_mono hi ((hc.1.integrable_norm_pow (by decide : 2≠0)).const_mul _) hp
    _ = L^2*(∫ x, ‖lineConvolution a v x‖^2) := integral_const_mul _ _
    _ ≤ L^2*((∫ t, ‖a t‖)^2*(∫ x, ‖v x‖^2)) :=
      mul_le_mul_of_nonneg_left hc.2 (sq_nonneg L)
    _ = _ := by simp only [ha,hv]; ring

theorem lineMultiplicationCommutator_formula (K h : SchwartzMap ℝ ℂ)
    (b : ℝ → ℂ) (hbm : Measurable b) (B : ℝ) (hB : 0≤B) (hb : ∀ x, ‖b x‖≤B) (x : ℝ) :
    lineMultiplicationCommutator K b h x=
      ∫ t, K t*(b x-b (x-t))*h (x-t) := by
  have hh := lineConvolution_integrand_of_bounded K h K.integrable h.continuous.measurable
    (SchwartzMap.seminorm ℝ 0 0 h) (fun x => h.norm_le_seminorm ℝ x) x
  have hbh := lineConvolution_integrand_of_bounded K (fun y => b y*h y) K.integrable
    (hbm.mul h.continuous.measurable) (B*SchwartzMap.seminorm ℝ 0 0 h)
    (fun y => by rw [norm_mul]; exact mul_le_mul (hb y) (h.norm_le_seminorm ℝ y) (norm_nonneg _) hB) x
  unfold lineMultiplicationCommutator lineConvolution
  rw [←integral_const_mul,←integral_sub (hh.const_mul (b x)) hbh]
  apply integral_congr_ae
  filter_upwards [] with t
  ring

theorem lineMultiplicationCommutator_energy (K h : SchwartzMap ℝ ℂ)
    (b : ℝ → ℂ) (hbm : Measurable b) (B : ℝ) (hB : 0≤B) (hb : ∀ x, ‖b x‖≤B)
    (L : ℝ) (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    MemLp (lineMultiplicationCommutator K b h) 2 volume ∧
    (∫ x, ‖lineMultiplicationCommutator K b h x‖^2)≤
      L^2*(∫ t, |t| *‖K t‖)^2*(∫ x, ‖h x‖^2) := by
  have hm : Measurable (lineMultiplicationCommutator K b h) :=
    (hbm.mul (lineConvolution_measurable K K.continuous.measurable h h.continuous.measurable)).sub
      (lineConvolution_measurable K K.continuous.measurable (fun y => b y*h y)
        (hbm.mul h.continuous.measurable))
  apply lineMoment_dominated_energy K h _ hm L
  intro x
  rw [lineMultiplicationCommutator_formula K h b hbm B hB hb]
  have hi : Integrable (fun t => |t| *‖K t‖*‖h (x-t)‖) := by
    apply ((schwartz_first_absolute_moment_integrable K).mul_const (SchwartzMap.seminorm ℝ 0 0 h)).mono'
      (by apply Measurable.aestronglyMeasurable; fun_prop)
    filter_upwards [] with t
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (h.norm_le_seminorm ℝ _) (by positivity)
  have hh := norm_integral_le_of_norm_le (hi.const_mul L)
    (Filter.Eventually.of_forall (fun t => show ‖K t*(b x-b (x-t))*h (x-t)‖≤L*(|t| *‖K t‖*‖h (x-t)‖) from by
      rw [norm_mul,norm_mul]
      have hl := hLip x (x-t)
      rw [sub_sub_cancel] at hl
      calc
        _ ≤ ‖K t‖*(L*|t|)*‖h (x-t)‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl (norm_nonneg _)) (norm_nonneg _)
        _ = _ := by ring))
  simpa only [integral_const_mul] using hh

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicCommutatorCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed enlarged annulus for the low/high part of the commutator.
Its support fits the already proved localized Mihlin kernel estimates. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketRepresentation

theorem dyadicCommutatorCutoff_one (x : ℝ) (hx : 13/24≤|x| ∧ |x|≤3/2) :
    dyadicCommutatorCutoff x=1 := by
  have hsmall : |(2/3)*x|≤1 := by rw [abs_mul]; norm_num; linarith [hx.2]
  have hlarge : 13/12≤|2*x| := by rw [abs_mul]; norm_num; linarith [hx.1]
  rw [dyadicCommutatorCutoff_apply,reassemblyLow_one _ hsmall,reassemblyLow_zero _ hlarge,sub_zero]

theorem dyadicCommutatorCutoff_small (x : ℝ) (hx : |x|≤1/2) :
    dyadicCommutatorCutoff x=0 := by
  have h1 : |(2/3)*x|≤1 := by rw [abs_mul]; norm_num; linarith
  have h2 : |2*x|≤1 := by rw [abs_mul]; norm_num; linarith
  rw [dyadicCommutatorCutoff_apply,reassemblyLow_one _ h1,reassemblyLow_one _ h2,sub_self]

theorem dyadicCommutatorCutoff_large (x : ℝ) (hx : 13/8≤|x|) :
    dyadicCommutatorCutoff x=0 := by
  have h1 : 13/12≤|(2/3)*x| := by rw [abs_mul]; norm_num; linarith
  have h2 : 13/12≤|2*x| := by rw [abs_mul]; norm_num; linarith
  rw [dyadicCommutatorCutoff_apply,reassemblyLow_zero _ h1,reassemblyLow_zero _ h2,sub_self]

theorem dyadicCommutatorCutoff_tsupport :
    tsupport dyadicCommutatorCutoff ⊆ {x : ℝ | 1/2≤|x| ∧ |x|≤13/8} := by
  apply closure_minimal _ ((isClosed_le continuous_const continuous_abs).inter
    (isClosed_le continuous_abs continuous_const))
  intro x hx
  exact ⟨(lt_of_not_ge (fun h => hx (dyadicCommutatorCutoff_small x h))).le,
    (lt_of_not_ge (fun h => hx (dyadicCommutatorCutoff_large x h))).le⟩

theorem dyadicCommutatorCutoff_away_zero :
    tsupport dyadicCommutatorCutoff ⊆ {x : ℝ | 1/2≤|x|} :=
  fun _ hx => (dyadicCommutatorCutoff_tsupport hx).1

theorem dyadicCommutatorCutoff_bounded_support :
    tsupport dyadicCommutatorCutoff ⊆ Icc (-2:ℝ) 2 := by
  intro x hx
  have h := (dyadicCommutatorCutoff_tsupport hx).2
  exact abs_le.mp (by linarith : |x|≤2)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineProductSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Fourier spectrum of an actual Schwartz product, including the
ball and annulus bounds needed in the dyadic commutator decomposition. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem schwartz_fourier_twice (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    (𝓕 (𝓕 f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ) x=f (-x) := by
  have he : (𝓕⁻ (𝓕 f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ)=f := FourierTransform.fourierInv_fourier_eq f
  have hh := congrArg (fun g : SchwartzMap ℝ ℂ => g (-x)) he
  change (𝓕 (𝓕 f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ) (-(-x))=f (-x) at hh
  simpa only [neg_neg] using hh

theorem lineSchwartzProduct_fourier (f g : SchwartzMap ℝ ℂ) :
    (𝓕 (lineSchwartzProduct f g) : SchwartzMap ℝ ℂ)=
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 g) := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).symm.injective
  change 𝓕⁻ (𝓕 (lineSchwartzProduct f g) : SchwartzMap ℝ ℂ)=
    𝓕⁻ (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 g))
  rw [FourierTransform.fourierInv_fourier_eq]
  ext x
  change lineSchwartzProduct f g x=
    (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 g)) : SchwartzMap ℝ ℂ) (-x)
  rw [SchwartzMap.fourier_convolution]
  simp only [SchwartzMap.pairing_apply_apply,ContinuousLinearMap.mul_apply',schwartz_fourier_twice,
    neg_neg,lineSchwartzProduct_apply]

theorem lineSchwartzProduct_fourier_zero (f g : SchwartzMap ℝ ℂ) (eta : ℝ)
    (h : ∀ t, (𝓕 f : SchwartzMap ℝ ℂ) t=0 ∨ (𝓕 g : SchwartzMap ℝ ℂ) (eta-t)=0) :
    (𝓕 (lineSchwartzProduct f g) : SchwartzMap ℝ ℂ) eta=0 := by
  rw [lineSchwartzProduct_fourier,SchwartzMap.convolution_apply,convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards [] with t
  change (𝓕 f : SchwartzMap ℝ ℂ) t*(𝓕 g : SchwartzMap ℝ ℂ) (eta-t)=0
  exact (h t).elim (fun hf => by rw [hf,zero_mul]) (fun hg => by rw [hg,mul_zero])

theorem lineSchwartzProduct_band (f g : SchwartzMap ℝ ℂ) (A B : ℝ)
    (hf : ∀ eta, (𝓕 f : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤A)
    (hg : ∀ eta, (𝓕 g : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤B) :
    ∀ eta, (𝓕 (lineSchwartzProduct f g) : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤A+B := by
  intro eta heta
  by_contra hn
  apply heta
  apply lineSchwartzProduct_fourier_zero
  intro t
  by_cases ht : (𝓕 f : SchwartzMap ℝ ℂ) t=0
  · exact Or.inl ht
  · right
    by_contra hs
    have htri : |eta|≤|t|+|eta-t| := by simpa only [add_sub_cancel] using abs_add_le t (eta-t)
    exact hn (htri.trans (add_le_add (hf t ht) (hg (eta-t) hs)))

theorem lineSchwartzProduct_annular_lower (f g : SchwartzMap ℝ ℂ) (A B : ℝ)
    (hf : ∀ eta, (𝓕 f : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤A)
    (hg : ∀ eta, (𝓕 g : SchwartzMap ℝ ℂ) eta≠0 → B≤|eta|) :
    ∀ eta, (𝓕 (lineSchwartzProduct f g) : SchwartzMap ℝ ℂ) eta≠0 → B-A≤|eta| := by
  intro eta heta
  by_contra hn
  apply heta
  apply lineSchwartzProduct_fourier_zero
  intro t
  by_cases ht : (𝓕 f : SchwartzMap ℝ ℂ) t=0
  · exact Or.inl ht
  · right
    by_contra hs
    have htri : |eta-t|≤|eta|+|t| := abs_sub eta t
    have h1 := hf t ht
    have h2 := hg (eta-t) hs
    linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineDyadicSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual spectral separation of the low/high dyadic interaction,
and its exact localization by the fixed commutator cutoff. -/
noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem dyadicProjection_frequency (W : ℝ) (hW : 0<W) (f : SchwartzMap ℝ ℂ)
    (eta : ℝ) (heta : (𝓕 (lineSchwartzProjection dyadicDifference W hW.ne' f)) eta≠0) :
    1/W≤|eta| ∧ |eta|≤(13/6)/W := by
  have hn : dyadicDifference (W*eta)≠0 := by
    intro hz
    exact heta (by rw [lineSchwartzProjection_fourier,hz,zero_mul])
  have hlo : 1 < |W*eta| := lt_of_not_ge (fun hh => hn (dyadicDifference_small _ hh))
  have hhi : |W*eta|<13/6 := lt_of_not_ge (fun hh => hn (dyadicDifference_large _ hh))
  rw [abs_mul,abs_of_pos hW] at hlo hhi
  exact ⟨(div_le_iff₀ hW).mpr (by linarith), (le_div_iff₀ hW).mpr (by linarith)⟩

theorem lowpassProjection_frequency (W : ℝ) (hW : 0<W) (f : SchwartzMap ℝ ℂ)
    (eta : ℝ) (heta : (𝓕 (lineSchwartzProjection reassemblyLow W hW.ne' f)) eta≠0) :
    |eta|≤(13/12)/W := by
  have hn : reassemblyLow (W*eta)≠0 := by
    intro hz
    exact heta (by rw [lineSchwartzProjection_fourier,hz,zero_mul])
  have hh : |W*eta|<13/12 := lt_of_not_ge (fun hh => hn (reassemblyLow_zero _ hh))
  rw [abs_mul,abs_of_pos hW] at hh
  exact (le_div_iff₀ hW).mpr (by linarith)

theorem lowHighProduct_frequency (W : ℝ) (hW : 0<W) (b h : SchwartzMap ℝ ℂ) :
    let B := lineSchwartzProjection reassemblyLow (16*W) (by positivity) b
    let H := lineSchwartzProjection dyadicDifference W hW.ne' h
    ∀ eta, (𝓕 (lineSchwartzProduct B H)) eta≠0 → (11/12)/W≤|eta| ∧ |eta|≤(9/4)/W := by
  intro B H eta heta
  have hb := lowpassProjection_frequency (16*W) (by positivity) b
  have hh := dyadicProjection_frequency W hW h
  have hlo := lineSchwartzProduct_annular_lower B H ((13/12)/(16*W)) (1/W) hb
    (fun x hx => (hh x hx).1) eta heta
  have hhi := lineSchwartzProduct_band B H ((13/12)/(16*W)) ((13/6)/W) hb
    (fun x hx => (hh x hx).2) eta heta
  have he1 : 1/W-(13/12)/(16*W)=(179/192)/W := by field_simp [hW.ne']; ring
  have he2 : (13/12)/(16*W)+(13/6)/W=(143/64)/W := by field_simp [hW.ne']; ring
  rw [he1] at hlo
  rw [he2] at hhi
  exact ⟨(div_le_div_of_nonneg_right (by norm_num : (11/12:ℝ)≤179/192) hW.le).trans hlo,
    hhi.trans (div_le_div_of_nonneg_right (by norm_num : (143/64:ℝ)≤9/4) hW.le)⟩

theorem dyadicCommutatorCutoff_absorb (W : ℝ) (hW : 0<W) (f : SchwartzMap ℝ ℂ)
    (hband : ∀ eta, (𝓕 f) eta≠0 → (11/12)/W≤|eta| ∧ |eta|≤(9/4)/W) :
    lineSchwartzProjection dyadicCommutatorCutoff ((2/3)*W) (by positivity) f=f := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
  ext eta
  change (𝓕 (lineSchwartzProjection dyadicCommutatorCutoff ((2/3)*W) _ f)) eta=(𝓕 f) eta
  rw [lineSchwartzProjection_fourier]
  by_cases hz : (𝓕 f) eta=0
  · rw [hz,mul_zero]
  · have h := hband eta hz
    have hlo : 11/12≤W*|eta| := (div_le_iff₀ hW).mp h.1 |>.trans_eq (by ring)
    have hhi : W*|eta|≤9/4 := by have hh := (le_div_iff₀ hW).mp h.2; nlinarith only [hh]
    have habs : |((2/3)*W)*eta|=(2/3)*(W*|eta|) := by
      rw [abs_mul,abs_of_pos (by positivity : (0:ℝ)<(2/3)*W)]
      ring
    have hp : dyadicCommutatorCutoff (((2/3)*W)*eta)=1 := by
      apply dyadicCommutatorCutoff_one
      rw [habs]
      exact ⟨by linarith,by linarith⟩
    rw [hp,one_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineProjectionDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation commutes with the actual smooth line projections,
and a compact Fourier band gives the required Bernstein energy bound. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProjection_derivative (q : SchwartzMap ℝ ℂ)
    (W : ℝ) (hW : W≠0) (f : SchwartzMap ℝ ℂ) :
    schwartzDerivative 1 (lineSchwartzProjection q W hW f)=
      lineSchwartzProjection q W hW (schwartzDerivative 1 f) := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
  ext eta
  change (𝓕 (schwartzDerivative 1 (lineSchwartzProjection q W hW f))) eta=
    (𝓕 (lineSchwartzProjection q W hW (schwartzDerivative 1 f))) eta
  rw [fourier_schwartzDerivative,lineSchwartzProjection_fourier,
    lineSchwartzProjection_fourier,fourier_schwartzDerivative]
  ring

theorem line_bernstein_energy (f : SchwartzMap ℝ ℂ) (R : ℝ)
    (hband : ∀ eta, (𝓕 f : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤R) :
    (∫ x, ‖schwartzDerivative 1 f x‖^2)≤(2*Real.pi*R)^2*(∫ x, ‖f x‖^2) := by
  have hi (g : SchwartzMap ℝ ℂ) : Integrable (fun eta => ‖(𝓕 g : SchwartzMap ℝ ℂ) eta‖^2) :=
    ((𝓕 g : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  have hp (eta : ℝ) : ‖(𝓕 (schwartzDerivative 1 f) : SchwartzMap ℝ ℂ) eta‖^2≤
      (2*Real.pi*R)^2*‖(𝓕 f : SchwartzMap ℝ ℂ) eta‖^2 := by
    rw [fourier_schwartzDerivative 1 f eta,pow_one,norm_mul]
    by_cases hf : (𝓕 f : SchwartzMap ℝ ℂ) eta=0
    · simp only [hf,norm_zero,mul_zero,zero_pow (by decide : 2≠0),le_refl]
    · have hc : ‖(2*Real.pi*Complex.I*(eta:ℂ))‖=2*Real.pi*|eta| := by
        simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]
      rw [hc,mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left (hband eta hf) (by positivity)) 2
  calc
    _ = ∫ eta, ‖(𝓕 (schwartzDerivative 1 f) : SchwartzMap ℝ ℂ) eta‖^2 := (SchwartzMap.integral_norm_sq_fourier (schwartzDerivative 1 f)).symm
    _ ≤ ∫ eta, (2*Real.pi*R)^2*‖(𝓕 f : SchwartzMap ℝ ℂ) eta‖^2 := integral_mono (hi _) ((hi f).const_mul _) hp
    _ = _ := by rw [integral_const_mul,SchwartzMap.integral_norm_sq_fourier f]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineLocalizedMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact localized line multipliers and the scale-cancelling first-moment
bound used in the low/high commutator estimate. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem localizedLineProjection_eq (m f : SchwartzMap ℝ ℂ) (V : ℝ) (hV : 0<V)
    (hcut : ∀ eta, dyadicCommutatorCutoff (V*eta)*(𝓕 f) eta=(𝓕 f) eta) :
    lineSchwartzProjection (localizedLineSymbol m V hV) V hV.ne' f=
      lineSchwartzProjection m 1 (by norm_num) f := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
  ext eta
  change (𝓕 (lineSchwartzProjection (localizedLineSymbol m V hV) V hV.ne' f)) eta=
    (𝓕 (lineSchwartzProjection m 1 (by norm_num) f)) eta
  rw [lineSchwartzProjection_fourier,lineSchwartzProjection_fourier]
  simp only [localizedLineSymbol,localizedMihlinProfile_apply,one_mul]
  have he : V⁻¹*(V*eta)=eta := by field_simp
  rw [he,mul_assoc,hcut]

theorem localizedLineKernel_firstMoment (m : SchwartzMap ℝ ℂ) (V A : ℝ) (hV : 0<V) (hA : 0≤A)
    (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A) :
    (∫ t, |t| *‖lineProjectionKernel (localizedLineSymbol m V hV) V hV.ne' t‖)≤
      V*A*localizedKernelFirstMomentConstant dyadicCommutatorCutoff := by
  rw [lineProjectionKernel_moment1 _ V hV]
  have hh := localizedMihlinProfile_kernel_firstMoment m dyadicCommutatorCutoff V⁻¹ A
    (inv_pos.mpr hV) hA hm dyadicCommutatorCutoff_away_zero dyadicCommutatorCutoff_bounded_support
  exact (mul_le_mul_of_nonneg_left hh hV.le).trans_eq (by ring)

theorem localizedLineCommutator_derivative_energy (m h : SchwartzMap ℝ ℂ)
    (V A : ℝ) (hV : 0<V) (hA : 0≤A)
    (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (b : ℝ → ℂ) (hbm : Measurable b) (B : ℝ) (hB : 0≤B) (hb : ∀ x, ‖b x‖≤B)
    (L R : ℝ) (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|)
    (hband : ∀ eta, (𝓕 h) eta≠0 → |eta|≤R) :
    let K := lineProjectionKernel (localizedLineSymbol m V hV) V hV.ne'
    MemLp (lineMultiplicationCommutator K b (schwartzDerivative 1 h)) 2 volume ∧
      (∫ x, ‖lineMultiplicationCommutator K b (schwartzDerivative 1 h) x‖^2)≤
        (L*A*localizedKernelFirstMomentConstant dyadicCommutatorCutoff*V*(2*Real.pi*R))^2*
          (∫ x, ‖h x‖^2) := by
  intro K
  have hc := lineMultiplicationCommutator_energy K (schwartzDerivative 1 h) b hbm B hB hb L hLip
  have hmom := localizedLineKernel_firstMoment m V A hV hA hm
  have hpos := localizedKernelFirstMomentConstant_nonneg dyadicCommutatorCutoff
  have hs := pow_le_pow_left₀ (integral_nonneg (fun _ => by positivity)) hmom 2
  have hbnd := line_bernstein_energy h R hband
  refine ⟨hc.1,?_⟩
  calc
    _ ≤ L^2*(∫ t, |t| *‖K t‖)^2*(∫ x, ‖schwartzDerivative 1 h x‖^2) := hc.2
    _ ≤ L^2*(V*A*localizedKernelFirstMomentConstant dyadicCommutatorCutoff)^2*
        ((2*Real.pi*R)^2*(∫ x, ‖h x‖^2)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hs (sq_nonneg L)) hbnd
        (integral_nonneg (fun _ => sq_nonneg _)) (by positivity)
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineKernelDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed zeroth and second decay bounds for the scaled line kernel. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineProjectionKernel_norm (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) (t : ℝ) :
    ‖lineProjectionKernel q W hW.ne' t‖=W⁻¹*‖(𝓕⁻ q : SchwartzMap ℝ ℂ) (t/W)‖ := by
  rw [lineProjectionKernel_eq_scaled q W hW,scaledSchwartzKernel_apply q W hW]
  simp only [scaledTimeKernel,norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hW.le]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineProjectionLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth line projection preserves a Lipschitz bound uniformly in its
scale, up to the fixed kernel L1 norm. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineProjectionKernel_l1 (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) :
    (∫ t, ‖lineProjectionKernel q W hW.ne' t‖)=∫ t, ‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖ := by
  simp_rw [lineProjectionKernel_norm q W hW]
  rw [integral_const_mul,Measure.integral_comp_div (fun t => ‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖) W,
    abs_of_pos hW,smul_eq_mul,←mul_assoc,inv_mul_cancel₀ hW.ne',one_mul]

theorem lineConvolution_lipschitz (K : SchwartzMap ℝ ℂ) (b : ℝ → ℂ)
    (hbm : Measurable b) (B : ℝ) (hb : ∀ x, ‖b x‖≤B) (L : ℝ)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) (x y : ℝ) :
    ‖lineConvolution K b x-lineConvolution K b y‖≤
      (L*(∫ t, ‖K t‖))*|x-y| := by
  have h1 := lineConvolution_integrand_of_bounded K b K.integrable hbm B hb x
  have h2 := lineConvolution_integrand_of_bounded K b K.integrable hbm B hb y
  have he : lineConvolution K b x-lineConvolution K b y=
      ∫ t, K t*(b (x-t)-b (y-t)) := by
    simp_rw [mul_sub]
    rw [integral_sub h1 h2]
    rfl
  rw [he]
  have hh := norm_integral_le_of_norm_le (μ:=volume) (K.integrable.norm.const_mul (L*|x-y|))
    (Filter.Eventually.of_forall (fun t => show ‖K t*(b (x-t)-b (y-t))‖≤L*|x-y| *‖K t‖ from by
      rw [norm_mul]
      have hl := hLip (x-t) (y-t)
      rw [sub_sub_sub_cancel_right] at hl
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hl (norm_nonneg (K t))))
  rw [integral_const_mul] at hh
  convert hh using 1 <;> first | rfl | ring

theorem lineProjection_lipschitz (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W)
    (b : ℝ → ℂ) (hbm : Measurable b) (B : ℝ) (hb : ∀ x, ‖b x‖≤B) (L : ℝ)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) (x y : ℝ) :
    ‖lineConvolution (lineProjectionKernel q W hW.ne') b x-
      lineConvolution (lineProjectionKernel q W hW.ne') b y‖≤
      (L*(∫ t, ‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖))*|x-y| := by
  have hh := lineConvolution_lipschitz (lineProjectionKernel q W hW.ne') b hbm B hb L hLip x y
  rw [lineProjectionKernel_l1 q W hW] at hh
  exact hh

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineLowHighCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual low/high contribution of the multiplier commutator.
Both localization identities follow from the proved Fourier bands. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzCommutator_localized (m b h : SchwartzMap ℝ ℂ) (V : ℝ) (hV : 0<V)
    (hcutH : ∀ eta, dyadicCommutatorCutoff (V*eta)*(𝓕 h) eta=(𝓕 h) eta)
    (hcutBH : ∀ eta, dyadicCommutatorCutoff (V*eta)*(𝓕 (lineSchwartzProduct b h)) eta=
      (𝓕 (lineSchwartzProduct b h)) eta) :
    (lineSchwartzCommutator m b h : ℝ → ℂ)=
      lineMultiplicationCommutator (lineProjectionKernel (localizedLineSymbol m V hV) V hV.ne') b h := by
  funext x
  simp only [lineSchwartzCommutator,sub_apply,lineSchwartzProduct_apply,lineMultiplicationCommutator]
  rw [←localizedLineProjection_eq m h V hV hcutH,
    ←localizedLineProjection_eq m (lineSchwartzProduct b h) V hV hcutBH,
    lineSchwartzProjection_eq_convolution,lineSchwartzProjection_eq_convolution]
  rfl

theorem lowHighCommutator_localized (m b h : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) :
    let B := lineSchwartzProjection reassemblyLow (16*W) (by positivity) b
    let H := lineSchwartzProjection dyadicDifference W hW.ne' h
    (lineSchwartzCommutator m B (schwartzDerivative 1 H) : ℝ → ℂ)=
      lineMultiplicationCommutator
        (lineProjectionKernel (localizedLineSymbol m ((2/3)*W) (by positivity)) ((2/3)*W) (by positivity))
        B (schwartzDerivative 1 H) := by
  intro B H
  have hD : schwartzDerivative 1 H=lineSchwartzProjection dyadicDifference W hW.ne' (schwartzDerivative 1 h) :=
    lineSchwartzProjection_derivative dyadicDifference W hW.ne' h
  have hband : ∀ eta, (𝓕 (schwartzDerivative 1 H)) eta≠0 →
      (11/12)/W≤|eta| ∧ |eta|≤(9/4)/W := by
    intro eta heta
    rw [hD] at heta
    have hh := dyadicProjection_frequency W hW (schwartzDerivative 1 h) eta heta
    exact ⟨(div_le_div_of_nonneg_right (by norm_num : (11/12:ℝ)≤1) hW.le).trans hh.1,
      hh.2.trans (div_le_div_of_nonneg_right (by norm_num : (13/6:ℝ)≤9/4) hW.le)⟩
  have hbandB : ∀ eta, (𝓕 (lineSchwartzProduct B (schwartzDerivative 1 H))) eta≠0 →
      (11/12)/W≤|eta| ∧ |eta|≤(9/4)/W := by
    rw [hD]
    exact lowHighProduct_frequency W hW b (schwartzDerivative 1 h)
  have hcut (f : SchwartzMap ℝ ℂ)
      (hf : ∀ eta, (𝓕 f) eta≠0 → (11/12)/W≤|eta| ∧ |eta|≤(9/4)/W) (eta : ℝ) :
      dyadicCommutatorCutoff (((2/3)*W)*eta)*(𝓕 f) eta=(𝓕 f) eta := by
    have he := congrArg (fun g : SchwartzMap ℝ ℂ => (𝓕 g) eta)
      (dyadicCommutatorCutoff_absorb W hW f hf)
    simpa only [lineSchwartzProjection_fourier] using he
  exact lineSchwartzCommutator_localized m B (schwartzDerivative 1 H) ((2/3)*W) (by positivity)
    (hcut _ hband) (hcut _ hbandB)

theorem lowHighCommutator_energy (m b h : SchwartzMap ℝ ℂ) (W A L : ℝ)
    (hW : 0<W) (hA : 0≤A)
    (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    let B := lineSchwartzProjection reassemblyLow (16*W) (by positivity) b
    let H := lineSchwartzProjection dyadicDifference W hW.ne' h
    (∫ x, ‖lineSchwartzCommutator m B (schwartzDerivative 1 H) x‖^2)≤
      (L*(∫ t, ‖(𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ) t‖)*A*
        localizedKernelFirstMomentConstant dyadicCommutatorCutoff*(26*Real.pi/9))^2*
      (∫ x, ‖H x‖^2) := by
  intro B H
  let Lb := L*(∫ t, ‖(𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ) t‖)
  have hBLip (x y : ℝ) : ‖B x-B y‖≤Lb*|x-y| := by
    dsimp [B]
    rw [lineSchwartzProjection_eq_convolution,lineSchwartzProjection_eq_convolution]
    exact lineProjection_lipschitz reassemblyLow (16*W) (by positivity) b b.continuous.measurable
      (SchwartzMap.seminorm ℝ 0 0 b) (fun z => b.norm_le_seminorm ℝ z) L hLip x y
  have hR (eta : ℝ) (heta : (𝓕 H) eta≠0) : |eta|≤(13/6)/W :=
    (dyadicProjection_frequency W hW h eta heta).2
  have he := lowHighCommutator_localized m b h W hW
  have hc := localizedLineCommutator_derivative_energy m H ((2/3)*W) A (by positivity) hA hm
    B B.continuous.measurable (SchwartzMap.seminorm ℝ 0 0 B) (apply_nonneg _ _)
    (fun z => B.norm_le_seminorm ℝ z) Lb ((13/6)/W) hBLip hR
  change (∫ x, ‖lineSchwartzCommutator m B (schwartzDerivative 1 H) x‖^2)≤_
  rw [show (fun x => ‖lineSchwartzCommutator m B (schwartzDerivative 1 H) x‖^2)=
    (fun x => ‖lineMultiplicationCommutator
      (lineProjectionKernel (localizedLineSymbol m ((2/3)*W) (by positivity)) ((2/3)*W) (by positivity))
      B (schwartzDerivative 1 H) x‖^2) from by rw [he]]
  apply hc.2.trans_eq
  congr 2
  dsimp [Lb]
  field_simp [hW.ne']
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineLowHighSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The low/high commutator output stays in a fixed annulus. -/
noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProjection_comm (q p : SchwartzMap ℝ ℂ)
    (W V : ℝ) (hW : W≠0) (hV : V≠0) (f : SchwartzMap ℝ ℂ) :
    lineSchwartzProjection q W hW (lineSchwartzProjection p V hV f)=
      lineSchwartzProjection p V hV (lineSchwartzProjection q W hW f) := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
  ext eta
  change (𝓕 (lineSchwartzProjection q W hW (lineSchwartzProjection p V hV f))) eta=
    (𝓕 (lineSchwartzProjection p V hV (lineSchwartzProjection q W hW f))) eta
  simp only [lineSchwartzProjection_fourier]
  ring

theorem lowHighCommutator_frequency (m b h : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) :
    let B := lineSchwartzProjection reassemblyLow (16*W) (by positivity) b
    let H := lineSchwartzProjection dyadicDifference W hW.ne' h
    ∀ eta, (𝓕 (lineSchwartzCommutator m B (schwartzDerivative 1 H))) eta≠0 →
      (11/12)/W≤|eta| ∧ |eta|≤(9/4)/W := by
  intro B H eta heta
  have hD : schwartzDerivative 1 H=lineSchwartzProjection dyadicDifference W hW.ne' (schwartzDerivative 1 h) :=
    lineSchwartzProjection_derivative dyadicDifference W hW.ne' h
  have hcomm : lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 H)=
      lineSchwartzProjection dyadicDifference W hW.ne'
        (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 h)) := by
    rw [hD]
    exact lineSchwartzProjection_comm m dyadicDifference 1 W (by norm_num) hW.ne' _
  have hfirst : ∀ eta, (𝓕 (lineSchwartzProduct B
      (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 H)))) eta≠0 →
      (11/12)/W≤|eta| ∧ |eta|≤(9/4)/W := by
    rw [hcomm]
    exact lowHighProduct_frequency W hW b (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 h))
  have hsecond : ∀ eta, (𝓕 (lineSchwartzProduct B (schwartzDerivative 1 H))) eta≠0 →
      (11/12)/W≤|eta| ∧ |eta|≤(9/4)/W := by
    rw [hD]
    exact lowHighProduct_frequency W hW b (schwartzDerivative 1 h)
  have he : (𝓕 (lineSchwartzCommutator m B (schwartzDerivative 1 H))) eta=
      (𝓕 (lineSchwartzProduct B (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 H)))) eta-
      m eta*(𝓕 (lineSchwartzProduct B (schwartzDerivative 1 H))) eta := by
    change (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ)
      (lineSchwartzProduct B (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 H))-
        lineSchwartzProjection m 1 (by norm_num) (lineSchwartzProduct B (schwartzDerivative 1 H)))) eta=_
    rw [map_sub,sub_apply,FourierTransform.fourierCLM_apply,FourierTransform.fourierCLM_apply,
      lineSchwartzProjection_fourier,one_mul]
  by_cases hf : (𝓕 (lineSchwartzProduct B
      (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 H)))) eta=0
  · apply hsecond eta
    intro hs
    apply heta
    rw [he,hf,hs,mul_zero,sub_zero]
  · exact hfirst eta hf

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineHighLowEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cancellation of the high coefficient and Bernstein for the low input
give the actual high/low commutator its geometric scale factor. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProduct_energy (b h : SchwartzMap ℝ ℂ) (B : ℝ)
    (hb : ∀ x, ‖b x‖≤B) :
    (∫ x, ‖lineSchwartzProduct b h x‖^2)≤B^2*(∫ x, ‖h x‖^2) := by
  rw [←integral_const_mul]
  apply integral_mono
    ((lineSchwartzProduct b h).memLp 2 volume |>.integrable_norm_pow (by decide : 2≠0))
    ((h.memLp 2 volume |>.integrable_norm_pow (by decide : 2≠0)).const_mul _)
  intro x
  simp only [lineSchwartzProduct_apply,norm_mul,mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb x) 2) (sq_nonneg _)

theorem lineSchwartzCommutator_bounded_energy (m b h : SchwartzMap ℝ ℂ) (A B : ℝ)
    (hm : ∀ eta, ‖m eta‖≤A) (hb : ∀ x, ‖b x‖≤B) :
    (∫ x, ‖lineSchwartzCommutator m b h x‖^2)≤4*A^2*B^2*(∫ x, ‖h x‖^2) := by
  let U := lineSchwartzProduct b (lineSchwartzProjection m 1 (by norm_num) h)
  let V := lineSchwartzProjection m 1 (by norm_num) (lineSchwartzProduct b h)
  have hi (f : SchwartzMap ℝ ℂ) : Integrable (fun x => ‖f x‖^2) :=
    (f.memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  have hp (x : ℝ) : ‖U x-V x‖^2≤2*‖U x‖^2+2*‖V x‖^2 := by
    have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (U x) (V x)) 2
    nlinarith [sq_nonneg (‖U x‖-‖V x‖)]
  have hu := (lineSchwartzProduct_energy b _ B hb).trans
    (mul_le_mul_of_nonneg_left (lineSchwartzProjection_energy m 1 (by norm_num) A hm h) (sq_nonneg B))
  have hv := (lineSchwartzProjection_energy m 1 (by norm_num) A hm _).trans
    (mul_le_mul_of_nonneg_left (lineSchwartzProduct_energy b h B hb) (sq_nonneg A))
  calc
    _ ≤ ∫ x, 2*‖U x‖^2+2*‖V x‖^2 :=
      integral_mono (hi _) (((hi U).const_mul 2).add ((hi V).const_mul 2)) hp
    _ = 2*(∫ x, ‖U x‖^2)+2*(∫ x, ‖V x‖^2) := by
      rw [integral_add ((hi U).const_mul 2) ((hi V).const_mul 2),integral_const_mul,integral_const_mul]
    _ ≤ _ := by dsimp [U,V] at *; nlinarith [hu,hv]

theorem highLowCommutator_energy (m b h : SchwartzMap ℝ ℂ) (W V A L : ℝ)
    (hW : 0<W) (hV : 0<V) (hm : ∀ eta, ‖m eta‖≤A)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    let B := lineSchwartzProjection dyadicDifference W hW.ne' b
    let H := lineSchwartzProjection dyadicDifference V hV.ne' h
    (∫ x, ‖lineSchwartzCommutator m B (schwartzDerivative 1 H) x‖^2)≤
      (A*L*(∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖)*
        (26*Real.pi/3)*(W/V))^2*(∫ x, ‖H x‖^2) := by
  intro B H
  let M := ∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖
  have hb (x : ℝ) : ‖B x‖≤L*W*M := by
    dsimp [B]
    rw [lineSchwartzProjection_eq_convolution]
    exact dyadicProjection_lipschitz_bound W hW b b.continuous.measurable
      (SchwartzMap.seminorm ℝ 0 0 b) (fun z => b.norm_le_seminorm ℝ z) L hLip x
  have hc := lineSchwartzCommutator_bounded_energy m B (schwartzDerivative 1 H) A (L*W*M) hm hb
  have hd := line_bernstein_energy H ((13/6)/V)
    (fun eta heta => (dyadicProjection_frequency V hV h eta heta).2)
  calc
    _ ≤ 4*A^2*(L*W*M)^2*(∫ x, ‖schwartzDerivative 1 H x‖^2) := hc
    _ ≤ 4*A^2*(L*W*M)^2*((2*Real.pi*((13/6)/V))^2*(∫ x, ‖H x‖^2)) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by dsimp [M]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineHighLowSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A gap of five binary scales puts every high/low output in the
same fixed annulus as the high coefficient. -/
noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProduct_comm (f g : SchwartzMap ℝ ℂ) :
    lineSchwartzProduct f g=lineSchwartzProduct g f := by
  ext x
  simp only [lineSchwartzProduct_apply,mul_comm]

theorem lineSchwartzProjection_frequency_of_nonzero (q f : SchwartzMap ℝ ℂ)
    (W : ℝ) (hW : W≠0) (eta : ℝ)
    (heta : (𝓕 (lineSchwartzProjection q W hW f) : SchwartzMap ℝ ℂ) eta≠0) :
    (𝓕 f : SchwartzMap ℝ ℂ) eta≠0 := by
  intro hz
  exact heta (by rw [lineSchwartzProjection_fourier,hz,mul_zero])

theorem schwartzDerivative_frequency_of_nonzero (f : SchwartzMap ℝ ℂ) (eta : ℝ)
    (heta : (𝓕 (schwartzDerivative 1 f) : SchwartzMap ℝ ℂ) eta≠0) :
    (𝓕 f : SchwartzMap ℝ ℂ) eta≠0 := by
  intro hz
  exact heta (by rw [fourier_schwartzDerivative,hz,mul_zero])

theorem highLowProduct_frequency (B H : SchwartzMap ℝ ℂ) (W V : ℝ)
    (hW : 0<W) (hgap : 32*W≤V)
    (hB : ∀ eta, (𝓕 B : SchwartzMap ℝ ℂ) eta≠0 → 1/W≤|eta| ∧ |eta|≤(13/6)/W)
    (hH : ∀ eta, (𝓕 H : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤(13/6)/V) :
    ∀ eta, (𝓕 (lineSchwartzProduct B H) : SchwartzMap ℝ ℂ) eta≠0 →
      (11/12)/W≤|eta| ∧ |eta|≤(9/4)/W := by
  have hV : 0<V := lt_of_lt_of_le (by positivity) hgap
  have hR : (13/6)/V≤(1/12)/W := by
    apply (div_le_div_iff₀ hV hW).mpr
    nlinarith
  intro eta heta
  have hhi := lineSchwartzProduct_band B H ((13/6)/W) ((13/6)/V)
    (fun x hx => (hB x hx).2) hH eta heta
  have hlo := lineSchwartzProduct_annular_lower H B ((13/6)/V) (1/W)
    hH (fun x hx => (hB x hx).1) eta (by rwa [lineSchwartzProduct_comm H B])
  constructor
  · have he : (11/12)/W=1/W-(1/12)/W := by ring
    rw [he]; linarith
  · have he : (9/4)/W=(13/6)/W+(1/12)/W := by ring
    rw [he]; linarith

theorem highLowCommutator_frequency (m b h : SchwartzMap ℝ ℂ) (W V : ℝ)
    (hW : 0<W) (hV : 0<V) (hgap : 32*W≤V) :
    let B := lineSchwartzProjection dyadicDifference W hW.ne' b
    let H := lineSchwartzProjection dyadicDifference V hV.ne' h
    ∀ eta, (𝓕 (lineSchwartzCommutator m B (schwartzDerivative 1 H)) : SchwartzMap ℝ ℂ) eta≠0 →
      (11/12)/W≤|eta| ∧ |eta|≤(9/4)/W := by
  intro B H eta heta
  have hb := dyadicProjection_frequency W hW b
  have hh : ∀ x, (𝓕 (schwartzDerivative 1 H) : SchwartzMap ℝ ℂ) x≠0 → |x|≤(13/6)/V := by
    intro x hx
    exact (dyadicProjection_frequency V hV h x (schwartzDerivative_frequency_of_nonzero H x hx)).2
  have ht : ∀ x, (𝓕 (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 H)) : SchwartzMap ℝ ℂ) x≠0 → |x|≤(13/6)/V := by
    intro x hx
    exact hh x (lineSchwartzProjection_frequency_of_nonzero m _ 1 (by norm_num) x hx)
  have hfirst := highLowProduct_frequency B (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 H)) W V hW hgap hb ht
  have hsecond := highLowProduct_frequency B (schwartzDerivative 1 H) W V hW hgap hb hh
  have he : (𝓕 (lineSchwartzCommutator m B (schwartzDerivative 1 H)) : SchwartzMap ℝ ℂ) eta=
      (𝓕 (lineSchwartzProduct B (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 H))) : SchwartzMap ℝ ℂ) eta-
        m eta*(𝓕 (lineSchwartzProduct B (schwartzDerivative 1 H)) : SchwartzMap ℝ ℂ) eta := by
    change (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ)
      (lineSchwartzProduct B (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 H))-
        lineSchwartzProjection m 1 (by norm_num) (lineSchwartzProduct B (schwartzDerivative 1 H)))) eta=_
    rw [map_sub,sub_apply,FourierTransform.fourierCLM_apply,FourierTransform.fourierCLM_apply,
      lineSchwartzProjection_fourier,one_mul]
  by_cases hf : (𝓕 (lineSchwartzProduct B (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 H))) : SchwartzMap ℝ ℂ) eta=0
  · apply hsecond eta
    intro hs
    exact heta (by rw [he,hf,hs,mul_zero,sub_zero])
  · exact hfirst eta hf

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_IntGeometricSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric bound used on the two sides of a dyadic crossover. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem int_geometric_summable {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1) :
    Summable (fun k : ℤ => r^k.natAbs) := by
  have h := summable_geometric_of_abs_lt_one (r:=r) (by simpa only [abs_of_nonneg hr] using hr1)
  apply Summable.of_nat_of_neg
  · simpa only [Int.natAbs_natCast] using h
  · simpa only [Int.natAbs_neg,Int.natAbs_natCast] using h

theorem int_geometric_tsum_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1) :
    (∑' k : ℤ, r^k.natAbs)≤2/(1-r) := by
  have h := summable_geometric_of_abs_lt_one (r:=r) (by simpa only [abs_of_nonneg hr] using hr1)
  have hnat : Summable (fun n : ℕ => r^(n:ℤ).natAbs) := by simpa only [Int.natAbs_natCast] using h
  have hneg : Summable (fun n : ℕ => r^(-n:ℤ).natAbs) := by
    simpa only [Int.natAbs_neg,Int.natAbs_natCast] using h
  have heq : (∑' k : ℤ, r^k.natAbs)=(∑' n : ℕ, r^n)+(∑' n : ℕ, r^n)-1 := by
    simpa only [Int.natAbs_neg,Int.natAbs_natCast,Int.natAbs_zero,pow_zero] using
      (hnat.tsum_of_nat_of_neg (f:=fun k : ℤ => r^k.natAbs) hneg)
  rw [heq,tsum_geometric_of_abs_lt_one (r:=r)
    (by simpa only [abs_of_nonneg hr] using hr1),div_eq_mul_inv]
  linarith

theorem int_geometric_shift_sum_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1)
    (S : Finset ℤ) (a : ℤ) :
    (∑ k∈S, r^(k-a).natAbs)≤2/(1-r) := by
  classical
  have he : (∑ k∈S.image (fun k => k-a), r^k.natAbs)=∑ k∈S, r^(k-a).natAbs :=
    Finset.sum_image (g:=fun k : ℤ => k-a) (fun i _ j _ hij => by
      change i-a=j-a at hij
      omega)
  rw [←he]
  exact ((int_geometric_summable hr hr1).sum_le_tsum _ (fun k _ => pow_nonneg hr k.natAbs)).trans
    (int_geometric_tsum_le hr hr1)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineGeometricSchur
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual binary scale ratio is a summable row-and-column kernel. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem lineScaleWeight_pos (i j : ℤ) : 0<lineScaleWeight i j := by
  unfold lineScaleWeight
  positivity

theorem lineScaleWeight_ratio (i j : ℤ) (hij : i≤j) :
    DyadicLineGrid.scale i/DyadicLineGrid.scale j=lineScaleWeight i j := by
  have hn : ((j-i).natAbs:ℤ)=j-i := by omega
  unfold lineScaleWeight DyadicLineGrid.scale
  rw [←zpow_natCast,show (1/2:ℝ)=(2:ℝ)⁻¹ by norm_num,inv_zpow,←zpow_neg,hn,neg_sub,
    zpow_sub₀ (by norm_num : (2:ℝ)≠0)]

theorem lineScaleWeight_row (J : Finset ℤ) (i : ℤ) :
    (∑ j∈J, lineScaleWeight i j)≤4 := by
  simpa only [lineScaleWeight,show (2:ℝ)/(1-1/2)=4 by norm_num] using
    (int_geometric_shift_sum_le (r:=(1/2:ℝ)) (by norm_num) (by norm_num) J i)

theorem lineScaleWeight_col (I : Finset ℤ) (j : ℤ) :
    (∑ i∈I, lineScaleWeight i j)≤4 := by
  have he (i : ℤ) : lineScaleWeight i j=lineScaleWeight j i := by
    unfold lineScaleWeight
    rw [←Int.natAbs_neg,neg_sub]
  simpa only [he] using lineScaleWeight_row I j

theorem line_geometric_energy_schur {E : Type*} [NormedAddCommGroup E]
    (I J : Finset ℤ) (F : ℤ → ℤ → ℝ → E)
    (hF : ∀ i∈I, ∀ j∈J, MemLp (F i j) 2 volume)
    (b : ℤ → ℝ) (hb : ∀ j∈J, 0≤b j)
    (hbound : ∀ i∈I, ∀ j∈J, (∫ x, ‖F i j x‖^2)≤(lineScaleWeight i j)^2*b j) :
    (∑ i∈I, ∫ x, ‖∑ j∈J, F i j x‖^2)≤16*∑ j∈J, b j := by
  classical
  have hh := finite_energy_schur (volume : Measure ℝ)
    (fun (i : I) (j : J) => F i.val j.val)
    (fun i j => hF i.val i.property j.val j.property)
    (fun (i : I) (j : J) => lineScaleWeight i.val j.val)
    (fun i j => lineScaleWeight_pos i.val j.val)
    (fun j : J => b j.val) (fun j => hb j.val j.property)
    (R:=4) (C:=4) (by norm_num)
    (fun i => by
      rw [Finset.sum_coe_sort J (fun j => lineScaleWeight i.val j)]
      exact lineScaleWeight_row J i.val)
    (fun j => by
      rw [Finset.sum_coe_sort I (fun i => lineScaleWeight i j.val)]
      exact lineScaleWeight_col I j.val)
    (fun i j => hbound i.val i.property j.val j.property)
  change (∑ i : I, ∫ x, ‖∑ j : J, F i.val j.val x‖^2)≤
    4*4*(∑ j : J, b j.val) at hh
  have he (i : ℤ) : (∫ x, ‖∑ j : J, F i j.val x‖^2)=
      ∫ x, ‖∑ j∈J, F i j x‖^2 := by
    congr 1
    funext x
    rw [Finset.sum_coe_sort J (fun j => F i j x)]
  simp_rw [he] at hh
  rw [Finset.sum_coe_sort I (fun i => ∫ x, ‖∑ j∈J, F i j x‖^2),
    Finset.sum_coe_sort J b] at hh
  norm_num at hh
  exact hh

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicResolutionSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact telescoping and strong pointwise resolution for the binary
low-pass differences used in the commutator decomposition. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

theorem dyadicDifference_telescope (M : ℕ) (x : ℝ) :
    (∑ n∈Finset.range M, dyadicDifference ((2:ℝ)^n*x))=
      reassemblyLow (x/2)-reassemblyLow (((2:ℝ)^M*x)/2) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ,ih,dyadicDifference_apply,pow_succ]
    have he : (2^M*2*x)/2=(2:ℝ)^M*x := by ring
    rw [he]
    ring

theorem dyadicResolutionSymbol_eq (N : ℕ) (x : ℝ) :
    dyadicResolutionSymbol N x=
      reassemblyLow ((1/2:ℝ)^(N+1)*x)-reassemblyLow ((2:ℝ)^N*x) := by
  unfold dyadicResolutionSymbol
  have he (n : ℕ) : dyadicResolutionScale N n*x=(2:ℝ)^n*((1/2:ℝ)^N*x) := by
    unfold dyadicResolutionScale
    ring
  simp_rw [he]
  rw [dyadicDifference_telescope]
  have hfirst : ((1/2:ℝ)^N*x)/2=(1/2:ℝ)^(N+1)*x := by rw [pow_succ]; ring
  have hcancel : (2:ℝ)^N*(1/2:ℝ)^N=1 := by rw [←mul_pow]; norm_num
  have hlast : ((2:ℝ)^(2*N+1)*((1/2:ℝ)^N*x))/2=(2:ℝ)^N*x := by
    rw [show 2*N+1=N+N+1 by omega,pow_succ,pow_add]
    calc
      _ = ((2:ℝ)^N*(1/2:ℝ)^N)*(2:ℝ)^N*x := by ring
      _ = _ := by rw [hcancel,one_mul]
  rw [hfirst,hlast]

theorem dyadicResolutionSymbol_norm (N : ℕ) (x : ℝ) :
    ‖dyadicResolutionSymbol N x‖≤2 := by
  rw [dyadicResolutionSymbol_eq]
  have h1 := reassemblyLow_norm ((1/2:ℝ)^(N+1)*x)
  have h2 := reassemblyLow_norm ((2:ℝ)^N*x)
  exact (norm_sub_le _ _).trans (by linarith only [h1,h2])

theorem dyadicResolutionSymbol_tendsto (x : ℝ) (hx : x≠0) :
    Tendsto (fun N : ℕ => dyadicResolutionSymbol N x) atTop (𝓝 1) := by
  have hsmall : Tendsto (fun N : ℕ => reassemblyLow ((1/2:ℝ)^(N+1)*x)) atTop (𝓝 1) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
      (by norm_num : (1/2:ℝ)<1)).mul_const ((1/2:ℝ)*x)
    have hh := reassemblyLow.continuous.continuousAt.tendsto.comp hp
    simpa only [Function.comp_def,zero_mul,pow_succ,mul_assoc,reassemblyLow_one 0 (by norm_num)] using hh
  have hlarge : ∀ᶠ N : ℕ in atTop, reassemblyLow ((2:ℝ)^N*x)=0 := by
    have hp := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).atTop_mul_const
      (show 0 < |x| from abs_pos.mpr hx)
    filter_upwards [hp.eventually (eventually_ge_atTop (13/12:ℝ))] with N hN
    apply reassemblyLow_zero
    simpa only [abs_mul,abs_of_pos (pow_pos (by norm_num : (0:ℝ)<2) N)] using hN
  have hz : Tendsto (fun N : ℕ => reassemblyLow ((2:ℝ)^N*x)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (hlarge.mono fun _ h => h.symm)
  simpa only [dyadicResolutionSymbol_eq,sub_zero] using hsmall.sub hz

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicLineResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong L2 resolution by the genuine binary smooth differences. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators FourierTransform Topology ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem dyadicSchwartzSum_fourier (N : ℕ) (f : SchwartzMap ℝ ℂ) (eta : ℝ) :
    (𝓕 (dyadicSchwartzSum N f) : SchwartzMap ℝ ℂ) eta=
      dyadicResolutionSymbol N eta*(𝓕 f) eta := by
  simp only [dyadicSchwartzSum,FourierTransform.fourier_sum,sum_apply,lineSchwartzProjection_fourier,dyadicResolutionSymbol]
  exact (Finset.sum_mul _ _ _).symm

theorem dyadicSchwartzSum_sub_fourier (N : ℕ) (f : SchwartzMap ℝ ℂ) (eta : ℝ) :
    (𝓕 (dyadicSchwartzSum N f-f) : SchwartzMap ℝ ℂ) eta=
      (dyadicResolutionSymbol N eta-1)*(𝓕 f) eta := by
  change (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ) (dyadicSchwartzSum N f-f)) eta=_
  rw [map_sub,sub_apply,FourierTransform.fourierCLM_apply,FourierTransform.fourierCLM_apply,dyadicSchwartzSum_fourier]
  ring

theorem dyadicSchwartzSum_energy_tendsto (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun N : ℕ => ∫ x, ‖dyadicSchwartzSum N f x-f x‖^2) atTop (𝓝 0) := by
  have hi : Integrable (fun eta => (9:ℝ)*‖(𝓕 f : SchwartzMap ℝ ℂ) eta‖^2) :=
    (((𝓕 f : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)).const_mul 9
  have hh := tendsto_integral_of_dominated_convergence
    (fun eta => (9:ℝ)*‖(𝓕 f : SchwartzMap ℝ ℂ) eta‖^2)
    (F:=fun N eta => ‖(𝓕 (dyadicSchwartzSum N f-f) : SchwartzMap ℝ ℂ) eta‖^2)
    (f:=fun _ => (0:ℝ))
    (fun N => ((𝓕 (dyadicSchwartzSum N f-f) : SchwartzMap ℝ ℂ).continuous.measurable.norm.pow_const 2).aestronglyMeasurable)
    hi
    (fun N => Filter.Eventually.of_forall fun eta => by
      rw [Real.norm_of_nonneg (sq_nonneg _),dyadicSchwartzSum_sub_fourier,norm_mul,mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have htri := norm_sub_le (dyadicResolutionSymbol N eta) 1
      have hs := dyadicResolutionSymbol_norm N eta
      simp only [norm_one] at htri
      have hn : ‖dyadicResolutionSymbol N eta-1‖≤3 := by linarith
      exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (by norm_num))
    (by
      filter_upwards [volume.ae_ne (0:ℝ)] with eta heta
      have hlim := (((dyadicResolutionSymbol_tendsto eta heta).sub_const 1).mul_const ((𝓕 f) eta)).norm.pow 2
      simpa only [dyadicSchwartzSum_sub_fourier,sub_self,zero_mul,norm_zero,zero_pow (by decide : 2≠0)] using hlim)
  simpa only [SchwartzMap.integral_norm_sq_fourier,sub_apply,integral_zero] using hh

theorem dyadicSchwartzSum_Lp_tendsto (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun N : ℕ => (dyadicSchwartzSum N f).toLp 2 volume) atTop (𝓝 (f.toLp 2 volume)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun N : ℕ => dyadicSchwartzSum N f)
    (fun N => (dyadicSchwartzSum N f).memLp 2 volume) f (f.memLp 2 volume)).mpr
  have he (N : ℕ) : eLpNorm ((dyadicSchwartzSum N f : ℝ → ℂ)-(f : ℝ → ℂ)) 2 volume=
      ENNReal.ofReal (Real.sqrt (∫ x, ‖dyadicSchwartzSum N f x-f x‖^2)) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      (((dyadicSchwartzSum N f).memLp 2 volume).sub (f.memLp 2 volume))]
    norm_num [Real.sqrt_eq_rpow]
  simp_rw [he]
  have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_sqrt.continuousAt.tendsto.comp (dyadicSchwartzSum_energy_tendsto f))
  simpa only [Function.comp_def,Real.sqrt_zero,ENNReal.ofReal_zero] using hh

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineAnnularSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed annular Fourier overlap controls sums of the actual line
Schwartz functions appearing in the commutator proof. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem line_annular_nonzero_count (I : Finset ℤ) (f : ℤ → SchwartzMap ℝ ℂ)
    (hband : ∀ k∈I, ∀ eta, (𝓕 (f k) : SchwartzMap ℝ ℂ) eta≠0 →
      11/12≤(2:ℝ)^k*|eta| ∧ (2:ℝ)^k*|eta|≤9/4) (eta : ℝ) :
    (I.filter (fun k => (𝓕 (f k) : SchwartzMap ℝ ℂ) eta≠0)).card≤3 := by
  classical
  let A := I.filter (fun k => (𝓕 (f k) : SchwartzMap ℝ ℂ) eta≠0)
  change A.card≤3
  have hsep (j : ℤ) (hj : j∈A) (k : ℤ) (hk : k∈A) (hjk : j+2≤k) : False := by
    have hjb := hband j (Finset.mem_filter.mp hj).1 eta (Finset.mem_filter.mp hj).2
    have hkb := hband k (Finset.mem_filter.mp hk).1 eta (Finset.mem_filter.mp hk).2
    have hp : (2:ℝ)^j*4≤(2:ℝ)^k := by
      calc
        _ = (2:ℝ)^(j+2) := by rw [zpow_add₀ (by norm_num)]; norm_num
        _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) hjk
    have hh := mul_le_mul_of_nonneg_right hp (abs_nonneg eta)
    nlinarith only [hh,hjb.1,hkb.2]
  by_cases hne : A.Nonempty
  · obtain ⟨j,hj⟩ := hne
    have hsub : A⊆Finset.Icc (j-1) (j+1) := by
      intro k hk
      apply Finset.mem_Icc.mpr
      constructor
      · by_contra hn
        exact hsep k hk j hj (by omega)
      · by_contra hn
        exact hsep j hj k hk (by omega)
    apply (Finset.card_le_card hsub).trans
    rw [Int.card_Icc]
    omega
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty]
    omega

theorem line_annular_pointwise_square (I : Finset ℤ) (f : ℤ → SchwartzMap ℝ ℂ)
    (hband : ∀ k∈I, ∀ eta, (𝓕 (f k) : SchwartzMap ℝ ℂ) eta≠0 →
      11/12≤(2:ℝ)^k*|eta| ∧ (2:ℝ)^k*|eta|≤9/4) (eta : ℝ) :
    ‖∑ k∈I, (𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2≤3*∑ k∈I, ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2 := by
  classical
  let A := I.filter (fun k => (𝓕 (f k) : SchwartzMap ℝ ℂ) eta≠0)
  have he : (∑ k∈I, (𝓕 (f k) : SchwartzMap ℝ ℂ) eta)=∑ k∈A, (𝓕 (f k) : SchwartzMap ℝ ℂ) eta := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hkA
    by_contra h
    exact hkA (Finset.mem_filter.mpr ⟨hk,h⟩)
  have hs : (∑ k∈A, ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2)=∑ k∈I, ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hkA
    have hz : (𝓕 (f k) : SchwartzMap ℝ ℂ) eta=0 := by
      by_contra h
      exact hkA (Finset.mem_filter.mpr ⟨hk,h⟩)
    simp only [hz,norm_zero,zero_pow (by decide : 2≠0)]
  have hc : (A.card:ℝ)≤3 := by exact_mod_cast line_annular_nonzero_count I f hband eta
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul A
    (f:=fun _ => (1:ℝ)) (g:=fun k => ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2) (r:=fun k => ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖)
    (fun _ _ => zero_le_one) (fun _ _ => sq_nonneg _) (fun _ _ => by simp)
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at hcs
  rw [he]
  calc
    _ ≤ (∑ k∈A, ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (A.card:ℝ)*(∑ k∈A, ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2) := hcs
    _ ≤ 3*(∑ k∈A, ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2) :=
      mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by rw [hs]

theorem line_annular_sum_energy (I : Finset ℤ) (f : ℤ → SchwartzMap ℝ ℂ)
    (hband : ∀ k∈I, ∀ eta, (𝓕 (f k) : SchwartzMap ℝ ℂ) eta≠0 →
      11/12≤(2:ℝ)^k*|eta| ∧ (2:ℝ)^k*|eta|≤9/4) :
    (∫ x, ‖(∑ k∈I, f k) x‖^2)≤3*∑ k∈I, ∫ x, ‖f k x‖^2 := by
  have hi (k : ℤ) : Integrable (fun eta => ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2) :=
    ((𝓕 (f k) : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  calc
    _ = ∫ eta, ‖(𝓕 (∑ k∈I, f k) : SchwartzMap ℝ ℂ) eta‖^2 :=
      (SchwartzMap.integral_norm_sq_fourier _).symm
    _ ≤ ∫ eta, 3*∑ k∈I, ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2 := by
      apply integral_mono
        (((𝓕 (∑ k∈I, f k) : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0))
        ((integrable_finsetSum _ (fun k _ => hi k)).const_mul 3)
      intro eta
      simpa only [FourierTransform.fourier_sum,sum_apply] using line_annular_pointwise_square I f hband eta
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum _ (fun k _ => hi k)]
      simp_rw [SchwartzMap.integral_norm_sq_fourier]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineDyadicReconstructionEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite dyadic square bounds control the whole Schwartz function,
using the already proved strong binary resolution. -/
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem dyadicResolutionScale_eq_scale (N n : ℕ) :
    dyadicResolutionScale N n=scale ((n:ℤ)-(N:ℤ)) := by
  simp only [dyadicResolutionScale,scale,zpow_sub₀ (by norm_num : (2:ℝ)≠0),zpow_natCast]
  rw [one_div,inv_pow]
  ring

theorem dyadicSchwartzSum_eq_window (N : ℕ) (f : SchwartzMap ℝ ℂ) :
    dyadicSchwartzSum N f=∑ k∈dyadicResolutionWindow N,
      lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' f := by
  classical
  unfold dyadicSchwartzSum dyadicResolutionWindow
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n _
    simp only [dyadicResolutionScale_eq_scale]
  · intro i _ j _ hij
    change (i:ℤ)-(N:ℤ)=(j:ℤ)-(N:ℤ) at hij
    omega

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicProjectionCarleson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth Carleson condition for the actual binary line projections,
first on intervals and then on the nested dyadic line cells. -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem dyadicCarlesonConstant_pos : 0<dyadicCarlesonConstant := by
  unfold dyadicCarlesonConstant
  positivity

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SmoothCarlesonSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Duality turns the proved smooth Carleson analysis bound into the
actual finite paraproduct synthesis bound. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem smoothCarlesonDualConstant_nonneg : 0 ≤ smoothCarlesonDualConstant := by
  unfold smoothCarlesonDualConstant
  exact mul_nonneg (mul_nonneg (by norm_num) dyadicCarlesonConstant_pos.le) (sq_nonneg _)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ComparableCommutatorSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full comparable-frequency contribution, with its two product
terms estimated by actual smooth Carleson synthesis. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem schwartzDerivative_lipschitz_bound (b : SchwartzMap ℝ ℂ) (L : ℝ)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) : 0≤L ∧ ∀ x, ‖schwartzDerivative 1 b x‖≤L := by
  have hL : 0≤L := by
    have hh := hLip 1 0
    norm_num at hh
    exact (norm_nonneg _).trans hh
  refine ⟨hL,fun x => ?_⟩
  change ‖deriv b x‖≤L
  exact norm_deriv_le_of_lip' hL (Filter.Eventually.of_forall fun y => by
    simpa only [Real.norm_eq_abs] using hLip y x)

theorem lineSchwartz_three_energy (f g h : SchwartzMap ℝ ℂ) :
    (∫ x, ‖(f-g+h) x‖^2)≤3*((∫ x, ‖f x‖^2)+(∫ x, ‖g x‖^2)+(∫ x, ‖h x‖^2)) := by
  have hi (p : SchwartzMap ℝ ℂ) : Integrable (fun x => ‖p x‖^2) :=
    (p.memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  calc
    _ ≤ ∫ x, 3*(‖f x‖^2+‖g x‖^2+‖h x‖^2) := by
      apply integral_mono (hi _) (((hi f).add (hi g)).add (hi h) |>.const_mul 3)
      intro x
      simp only [add_apply,sub_apply]
      change ‖f x-g x+h x‖^2≤3*(‖f x‖^2+‖g x‖^2+‖h x‖^2)
      have ht : ‖f x-g x+h x‖≤‖f x‖+‖g x‖+‖h x‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (le_refl _))
      have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
      nlinarith [sq_nonneg (‖f x‖-‖g x‖),sq_nonneg (‖f x‖-‖h x‖),sq_nonneg (‖g x‖-‖h x‖)]
    _ = _ := by
      rw [integral_const_mul,
        integral_add (f:=fun x => ‖f x‖^2+‖g x‖^2) (g:=fun x => ‖h x‖^2) ((hi f).add (hi g)) (hi h),
        integral_add (hi f) (hi g)]

theorem lineSchwartzProjection_sum {ι : Type*} (I : Finset ι)
    (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0) (f : ι → SchwartzMap ℝ ℂ) :
    lineSchwartzProjection q W hW (∑ i∈I, f i)=∑ i∈I, lineSchwartzProjection q W hW (f i) :=
  map_sum (lineSchwartzProjectionLM q W hW) f I

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineCommutatorLinearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite linearity identities for the actual Schwartz commutator. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProduct_sum_right {ι : Type*} (I : Finset ι)
    (b : SchwartzMap ℝ ℂ) (h : ι → SchwartzMap ℝ ℂ) :
    lineSchwartzProduct b (∑ i∈I, h i)=∑ i∈I, lineSchwartzProduct b (h i) := by
  ext x
  simp only [lineSchwartzProduct_apply,sum_apply,Finset.mul_sum]

theorem lineSchwartzProduct_sum_left {ι : Type*} (I : Finset ι)
    (b : ι → SchwartzMap ℝ ℂ) (h : SchwartzMap ℝ ℂ) :
    lineSchwartzProduct (∑ i∈I, b i) h=∑ i∈I, lineSchwartzProduct (b i) h := by
  ext x
  simp only [lineSchwartzProduct_apply,sum_apply,Finset.sum_mul]

theorem lineSchwartzCommutator_sum_right {ι : Type*} (I : Finset ι)
    (m b : SchwartzMap ℝ ℂ) (h : ι → SchwartzMap ℝ ℂ) :
    lineSchwartzCommutator m b (∑ i∈I, h i)=∑ i∈I, lineSchwartzCommutator m b (h i) := by
  simp only [lineSchwartzCommutator,lineSchwartzProjection_sum,lineSchwartzProduct_sum_right,
    Finset.sum_sub_distrib]

theorem lineSchwartzCommutator_sum_left {ι : Type*} (I : Finset ι)
    (m : SchwartzMap ℝ ℂ) (b : ι → SchwartzMap ℝ ℂ) (h : SchwartzMap ℝ ℂ) :
    lineSchwartzCommutator m (∑ i∈I, b i) h=∑ i∈I, lineSchwartzCommutator m (b i) h := by
  simp only [lineSchwartzCommutator,lineSchwartzProduct_sum_left,lineSchwartzProjection_sum,
    Finset.sum_sub_distrib]

theorem lineSchwartzCommutator_add_left (m b c h : SchwartzMap ℝ ℂ) :
    lineSchwartzCommutator m (b+c) h=
      lineSchwartzCommutator m b h+lineSchwartzCommutator m c h := by
  have hprod (f g p : SchwartzMap ℝ ℂ) : lineSchwartzProduct (f+g) p=
      lineSchwartzProduct f p+lineSchwartzProduct g p := by
    ext x
    simp only [lineSchwartzProduct_apply,add_apply,add_mul]
  have hproj (f g : SchwartzMap ℝ ℂ) : lineSchwartzProjection m 1 (by norm_num) (f+g)=
      lineSchwartzProjection m 1 (by norm_num) f+lineSchwartzProjection m 1 (by norm_num) g :=
    map_add (lineSchwartzProjectionLM m 1 (by norm_num)) f g
  simp only [lineSchwartzCommutator,hprod,hproj]
  abel

theorem lineSchwartzCommutator_zero_left (m h : SchwartzMap ℝ ℂ) :
    lineSchwartzCommutator m 0 h=0 := by
  ext x
  have hp : lineSchwartzProduct (0 : SchwartzMap ℝ ℂ) h=0 := by ext y; simp
  have hT : lineSchwartzProjection m 1 (by norm_num) (0 : SchwartzMap ℝ ℂ)=0 :=
    map_zero (lineSchwartzProjectionLM m 1 (by norm_num))
  simp only [lineSchwartzCommutator,lineSchwartzProduct_apply,zero_apply,zero_mul,hp,hT,sub_zero]

theorem lineSchwartzCommutator_sub_left (m b c h : SchwartzMap ℝ ℂ) :
    lineSchwartzCommutator m (b-c) h=
      lineSchwartzCommutator m b h-lineSchwartzCommutator m c h := by
  have hprod (f g p : SchwartzMap ℝ ℂ) : lineSchwartzProduct (f-g) p=
      lineSchwartzProduct f p-lineSchwartzProduct g p := by
    ext x
    simp only [lineSchwartzProduct_apply,sub_apply,sub_mul]
  have hproj (f g : SchwartzMap ℝ ℂ) : lineSchwartzProjection m 1 (by norm_num) (f-g)=
      lineSchwartzProjection m 1 (by norm_num) f-lineSchwartzProjection m 1 (by norm_num) g :=
    map_sub (lineSchwartzProjectionLM m 1 (by norm_num)) f g
  simp only [lineSchwartzCommutator,hprod,hproj]
  abel

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineDyadicTelescoping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact inhomogeneous coefficient reconstruction: the low-frequency
part is retained, and the finite high-frequency tail telescopes. -/
noncomputable section
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem lineDyadic_eq_lowpass_sub (f : SchwartzMap ℝ ℂ) (k : ℤ) :
    lineDyadic f (k+1)=lineLowpass f k-lineLowpass f (k+1) := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
  ext eta
  change (𝓕 (lineDyadic f (k+1)) : SchwartzMap ℝ ℂ) eta=
    (𝓕 (lineLowpass f k-lineLowpass f (k+1)) : SchwartzMap ℝ ℂ) eta
  change (𝓕 (lineDyadic f (k+1)) : SchwartzMap ℝ ℂ) eta=
    (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ) (lineLowpass f k-lineLowpass f (k+1))) eta
  rw [map_sub,sub_apply,FourierTransform.fourierCLM_apply,FourierTransform.fourierCLM_apply]
  simp only [lineDyadic,lineLowpass,lineSchwartzProjection_fourier,dyadicDifference_apply]
  rw [scale_succ]
  have he : (2*scale k*eta)/2=scale k*eta := by ring
  rw [he]
  ring

theorem lineLowpass_telescope (f : SchwartzMap ℝ ℂ) (l u : ℤ) (hlu : l≤u) :
    lineLowpass f l=lineLowpass f u+∑ k∈Finset.Icc (l+1) u, lineDyadic f k := by
  classical
  induction u, hlu using Int.leInduction with
  | base => simp
  | succ u hlu ih =>
    have he : Finset.Icc (l+1) (u+1)=insert (u+1) (Finset.Icc (l+1) u) := by
      ext k
      simp only [Finset.mem_Icc,Finset.mem_insert]
      omega
    rw [he,Finset.sum_insert (by simp),lineDyadic_eq_lowpass_sub]
    rw [ih]
    abel

theorem lineLowpass_telescope_filtered (f : SchwartzMap ℝ ℂ) (l u v : ℤ)
    (hlu : l≤u) (huv : u≤v) :
    lineLowpass f l=lineLowpass f u+
      ∑ k∈Finset.Icc (l+1) v, if k≤u then lineDyadic f k else 0 := by
  classical
  rw [←Finset.sum_filter]
  have he : (Finset.Icc (l+1) v).filter (fun k => k≤u)=Finset.Icc (l+1) u := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_Icc]
    omega
  rw [he]
  exact lineLowpass_telescope f l u hlu

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineHighLowSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete finite high/low sum: geometric Schur summation inside
each high-frequency output annulus, then finite Fourier overlap. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem dyadic_scale_five_gap (i j : ℤ) (hij : i+5≤j) : 32*scale i ≤ scale j := by
  have hh : (2:ℝ)^(i+5)≤(2:ℝ)^j := zpow_le_zpow_right₀ (by norm_num) hij
  simpa only [zpow_add₀ (by norm_num : (2:ℝ)≠0),show (2:ℝ)^(5:ℤ)=32 by norm_num,
    scale,mul_comm] using hh

theorem highLowPiece_frequency (m b h : SchwartzMap ℝ ℂ) (i j : ℤ) :
    ∀ eta, (𝓕 (highLowPiece m b h i j) : SchwartzMap ℝ ℂ) eta≠0 →
      (11/12)/scale i≤|eta| ∧ |eta|≤(9/4)/scale i := by
  classical
  intro eta heta
  by_cases hij : i+5≤j
  · simp only [highLowPiece,ite_eq_left hij] at heta
    exact highLowCommutator_frequency m b h (scale i) (scale j) (scale_pos i) (scale_pos j)
      (dyadic_scale_five_gap i j hij) eta heta
  · simp only [highLowPiece,ite_eq_right hij,FourierTransform.fourier_zero,zero_apply,ne_eq,not_true_eq_false] at heta

theorem highLowRow_frequency (J : Finset ℤ) (m b h : SchwartzMap ℝ ℂ) (i : ℤ) :
    ∀ eta, (𝓕 (highLowRow J m b h i) : SchwartzMap ℝ ℂ) eta≠0 →
      (11/12)/scale i≤|eta| ∧ |eta|≤(9/4)/scale i := by
  intro eta heta
  by_contra hn
  apply heta
  simp only [highLowRow,FourierTransform.fourier_sum,sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_contra hj
  exact hn (highLowPiece_frequency m b h i j eta hj)

theorem highLowSum_energy (I J : Finset ℤ) (m b h : SchwartzMap ℝ ℂ) (A L : ℝ)
    (hm : ∀ eta, ‖m eta‖≤A) (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    (∫ x, ‖(∑ i∈I, highLowRow J m b h i) x‖^2)≤
      576*(A*L*(∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖)*
        (26*Real.pi/3))^2*(∫ x, ‖h x‖^2) := by
  classical
  let C := A*L*(∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖)*(26*Real.pi/3)
  let H := fun j => lineSchwartzProjection dyadicDifference (scale j) (scale_pos j).ne' h
  have hpiece (i j : ℤ) : (∫ x, ‖highLowPiece m b h i j x‖^2)≤
      (lineScaleWeight i j)^2*(C^2*(∫ x, ‖H j x‖^2)) := by
    by_cases hij : i+5≤j
    · have hc := highLowCommutator_energy m b h (scale i) (scale j) A L (scale_pos i) (scale_pos j) hm hLip
      simp only [highLowPiece,ite_eq_left hij]
      apply hc.trans_eq
      rw [lineScaleWeight_ratio i j (by omega)]
      dsimp [C,H]
      ring
    · simp only [highLowPiece,ite_eq_right hij,zero_apply,norm_zero,zero_pow (by decide : 2≠0),integral_zero]
      positivity
  have hschur := line_geometric_energy_schur I J
    (fun i j x => highLowPiece m b h i j x)
    (fun i _ j _ => (highLowPiece m b h i j).memLp 2 volume)
    (fun j => C^2*(∫ x, ‖H j x‖^2)) (fun j _ => by positivity)
    (fun i _ j _ => hpiece i j)
  have hrows : (∑ i∈I, ∫ x, ‖highLowRow J m b h i x‖^2)≤
      16*C^2*(∑ j∈J, ∫ x, ‖H j x‖^2) := by
    simpa only [highLowRow,sum_apply,←Finset.mul_sum,mul_assoc] using hschur
  have hframe : (∑ j∈J, ∫ x, ‖H j x‖^2)≤12*(∫ x, ‖h x‖^2) :=
    lineSchwartzProjection_frame J (fun _ => dyadicDifference) scale (fun j => (scale_pos j).ne')
      12 (fun eta => dyadicDifference_square_sum J eta) h
  have hoverlap := line_annular_sum_energy I (highLowRow J m b h) (by
    intro i _ eta heta
    have hf := highLowRow_frequency J m b h i eta heta
    have hlo := (div_le_iff₀ (scale_pos i)).mp hf.1
    have hhi := (le_div_iff₀ (scale_pos i)).mp hf.2
    exact ⟨by simpa only [scale,mul_comm] using hlo,by simpa only [scale,mul_comm] using hhi⟩)
  calc
    _ ≤ 3*(∑ i∈I, ∫ x, ‖highLowRow J m b h i x‖^2) := hoverlap
    _ ≤ 3*(16*C^2*(∑ j∈J, ∫ x, ‖H j x‖^2)) :=
      mul_le_mul_of_nonneg_left hrows (by norm_num)
    _ ≤ 3*(16*C^2*(12*(∫ x, ‖h x‖^2))) := by
      gcongr
    _ = _ := by dsimp [C]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineLowHighSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete low/high commutator sum has a bound independent of
both the number and the location of the retained dyadic frequencies. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem lowHighSum_energy (I : Finset ℤ) (m b h : SchwartzMap ℝ ℂ) (A L : ℝ) (hA : 0≤A)
    (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    (∫ x, ‖(∑ k∈I, lowHighPiece m b h k) x‖^2)≤
      36*(L*(∫ t, ‖(𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ) t‖)*A*
        localizedKernelFirstMomentConstant dyadicCommutatorCutoff*(26*Real.pi/9))^2*
        (∫ x, ‖h x‖^2) := by
  let C := L*(∫ t, ‖(𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ) t‖)*A*
    localizedKernelFirstMomentConstant dyadicCommutatorCutoff*(26*Real.pi/9)
  let H := fun k => lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' h
  have hpiece (k : ℤ) : (∫ x, ‖lowHighPiece m b h k x‖^2)≤C^2*(∫ x, ‖H k x‖^2) :=
    lowHighCommutator_energy m b h (scale k) A L (scale_pos k) hA hm hLip
  have hsum := line_annular_sum_energy I (lowHighPiece m b h) (by
    intro k _ eta heta
    have hb := lowHighCommutator_frequency m b h (scale k) (scale_pos k) eta heta
    have hlo := (div_le_iff₀ (scale_pos k)).mp hb.1
    have hhi := (le_div_iff₀ (scale_pos k)).mp hb.2
    exact ⟨by simpa only [scale,mul_comm] using hlo,by simpa only [scale,mul_comm] using hhi⟩)
  have hframe : (∑ k∈I, ∫ x, ‖H k x‖^2)≤12*(∫ x, ‖h x‖^2) :=
    lineSchwartzProjection_frame I (fun _ => dyadicDifference) scale (fun k => (scale_pos k).ne')
      12 (fun eta => dyadicDifference_square_sum I eta) h
  calc
    _ ≤ 3*∑ k∈I, ∫ x, ‖lowHighPiece m b h k x‖^2 := hsum
    _ ≤ 3*∑ k∈I, C^2*(∫ x, ‖H k x‖^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hpiece k) (by norm_num)
    _ = 3*C^2*(∑ k∈I, ∫ x, ‖H k x‖^2) := by rw [←Finset.mul_sum]; ring
    _ ≤ 3*C^2*(12*(∫ x, ‖h x‖^2)) := mul_le_mul_of_nonneg_left hframe (by positivity)
    _ = _ := by dsimp [C]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_DyadicNearbyInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nine nearby dyadic input frequencies form an actual Schwartz
family with uniform spectral and square-energy bounds. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem nearbyInputPiece_frequency (h : SchwartzMap ℝ ℂ) (i j : ℤ) (eta : ℝ)
    (heta : (𝓕 (nearbyInputPiece h i j) : SchwartzMap ℝ ℂ) eta≠0) : |eta|≤64/scale i := by
  classical
  by_cases hij : i-4≤j ∧ j≤ i+4
  · simp only [nearbyInputPiece,ite_eq_left hij] at heta
    have hh := (dyadicProjection_frequency (scale j) (scale_pos j) h eta heta).2
    have hr : scale i/scale j≤16 := by
      rw [scale,scale,←zpow_sub₀ (by norm_num : (2:ℝ)≠0)]
      have hz := zpow_le_zpow_right₀ (show (1:ℝ)≤2 by norm_num) (show i-j≤4 by omega)
      norm_num at hz
      exact hz
    have hm := mul_le_mul_of_nonneg_left hh (scale_pos i).le
    have he : scale i*((13/6)/scale j)=(13/6)*(scale i/scale j) := by ring
    rw [he] at hm
    apply (le_div_iff₀ (scale_pos i)).mpr
    nlinarith
  · simp only [nearbyInputPiece,ite_eq_right hij,FourierTransform.fourier_zero,zero_apply,ne_eq,not_true_eq_false] at heta

theorem nearbyInput_frequency (J : Finset ℤ) (h : SchwartzMap ℝ ℂ) (i : ℤ) (eta : ℝ)
    (heta : (𝓕 (nearbyInput J h i) : SchwartzMap ℝ ℂ) eta≠0) : |eta|≤64/scale i := by
  by_contra hn
  apply heta
  simp only [nearbyInput,FourierTransform.fourier_sum,sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_contra hj
  exact hn (nearbyInputPiece_frequency h i j eta hj)

theorem nearbyInput_energy (I J : Finset ℤ) (h : SchwartzMap ℝ ℂ) :
    (∑ i∈I, ∫ x, ‖nearbyInput J h i x‖^2)≤49152*(∫ x, ‖h x‖^2) := by
  classical
  let H := fun j => lineSchwartzProjection dyadicDifference (scale j) (scale_pos j).ne' h
  have hp (i j : ℤ) : (∫ x, ‖nearbyInputPiece h i j x‖^2)≤
      (lineScaleWeight i j)^2*(256*(∫ x, ‖H j x‖^2)) := by
    by_cases hij : i-4≤j ∧ j≤ i+4
    · have hn : (j-i).natAbs≤4 := by omega
      have hw : (1/16:ℝ)≤lineScaleWeight i j := by
        have hh := pow_le_pow_of_le_one (show (0:ℝ)≤1/2 by norm_num)
          (show (1/2:ℝ)≤1 by norm_num) hn
        norm_num only [show (1/2:ℝ)^4=1/16 by norm_num] at hh
        exact hh
      have hsq := pow_le_pow_left₀ (show (0:ℝ)≤1/16 by norm_num) hw 2
      have hcoef : 1≤(lineScaleWeight i j)^2*256 := by norm_num at hsq; linarith
      simp only [nearbyInputPiece,ite_eq_left hij]
      calc
        _ = 1*(∫ x, ‖H j x‖^2) := by rw [one_mul]
        _ ≤ ((lineScaleWeight i j)^2*256)*(∫ x, ‖H j x‖^2) :=
          mul_le_mul_of_nonneg_right hcoef (integral_nonneg fun _ => sq_nonneg _)
        _ = _ := by ring
    · simp only [nearbyInputPiece,ite_eq_right hij,zero_apply,norm_zero,zero_pow (by decide : 2≠0),integral_zero]
      positivity
  have hs := line_geometric_energy_schur I J (fun i j x => nearbyInputPiece h i j x)
    (fun i _ j _ => (nearbyInputPiece h i j).memLp 2 volume)
    (fun j => 256*(∫ x, ‖H j x‖^2)) (fun j _ => by positivity) (fun i _ j _ => hp i j)
  have hf := lineSchwartzProjection_frame J (fun _ => dyadicDifference) scale (fun j => (scale_pos j).ne')
    12 (fun eta => dyadicDifference_square_sum J eta) h
  change (∑ j∈J, ∫ x, ‖H j x‖^2)≤_ at hf
  have he : (∑ i∈I, ∫ x, ‖nearbyInput J h i x‖^2)≤16*256*(∑ j∈J, ∫ x, ‖H j x‖^2) := by
    simpa only [nearbyInput,sum_apply,←Finset.mul_sum,mul_assoc] using hs
  exact he.trans (by nlinarith [hf])

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SmoothedCommutatorDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact decomposition of a smoothed coefficient against finitely many
input bands into the three already bounded commutator interactions. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem lineSchwartzCommutator_zero_right (m b : SchwartzMap ℝ ℂ) :
    lineSchwartzCommutator m b 0=0 := by
  have hh := lineSchwartzCommutator_sum_right (∅ : Finset Unit) m b (fun _ => 0)
  simpa only [Finset.sum_empty] using hh

theorem schwartzDerivative_sum {ι : Type*} (I : Finset ι) (f : ι → SchwartzMap ℝ ℂ) :
    schwartzDerivative 1 (∑ i∈I, f i)=∑ i∈I, schwartzDerivative 1 (f i) :=
  map_sum (SchwartzMap.derivCLM ℂ ℂ) f I

theorem schwartzDerivative_zero : schwartzDerivative 1 (0 : SchwartzMap ℝ ℂ)=0 :=
  map_zero (SchwartzMap.derivCLM ℂ ℂ)

theorem scale_add_four (j : ℤ) : scale (j+4)=16*scale j := by
  simp only [scale,zpow_add₀ (by norm_num : (2:ℝ)≠0)]
  norm_num
  ring

theorem lineCommutator_nearbyInput (J : Finset ℤ) (m b h : SchwartzMap ℝ ℂ) (i : ℤ) :
    lineSchwartzCommutator m (lineDyadic b i) (schwartzDerivative 1 (nearbyInput J h i))=
      ∑ j∈J, if i-4≤j ∧ j≤ i+4 then
        lineSchwartzCommutator m (lineDyadic b i) (schwartzDerivative 1 (lineDyadic h j)) else 0 := by
  classical
  rw [nearbyInput,schwartzDerivative_sum,lineSchwartzCommutator_sum_right]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i-4≤j ∧ j≤ i+4
  · simp only [nearbyInputPiece,ite_eq_left hij,lineDyadic]
  · simp only [nearbyInputPiece,ite_eq_right hij,schwartzDerivative_zero,lineSchwartzCommutator_zero_right]

theorem split_dyadic_interaction {E : Type*} [AddCommMonoid E] (i j : ℤ) (x : E) :
    (if i≤j+4 then x else 0)=
      (if i+5≤j then x else 0)+(if i-4≤j ∧ j≤ i+4 then x else 0) := by
  by_cases hlow : i+5≤j
  · have h1 : i≤j+4 := by omega
    have h2 : ¬(i-4≤j ∧ j≤ i+4) := by omega
    simp only [ite_eq_left h1,ite_eq_left hlow,ite_eq_right h2,add_zero]
  · by_cases hnear : i-4≤j ∧ j≤ i+4
    · have h1 : i≤j+4 := by omega
      simp only [ite_eq_left h1,ite_eq_right hlow,ite_eq_left hnear,zero_add]
    · have h1 : ¬i≤j+4 := by omega
      simp only [ite_eq_right h1,ite_eq_right hlow,ite_eq_right hnear,add_zero]

theorem smoothedCommutator_decomposition (J : Finset ℤ) (m b h : SchwartzMap ℝ ℂ)
    (l v : ℤ) (hl : ∀ j∈J, l≤j+4) (hv : ∀ j∈J, j+4≤v) :
    lineSchwartzCommutator m (lineLowpass b l) (schwartzDerivative 1 (∑ j∈J, lineDyadic h j))=
      (∑ j∈J, lowHighPiece m b h j)+
      (∑ i∈Finset.Icc (l+1) v, highLowRow J m b h i)+
      (∑ i∈Finset.Icc (l+1) v, lineSchwartzCommutator m (lineDyadic b i)
        (schwartzDerivative 1 (nearbyInput J h i))) := by
  classical
  let I := Finset.Icc (l+1) v
  let F := fun i j => lineSchwartzCommutator m (lineDyadic b i) (schwartzDerivative 1 (lineDyadic h j))
  have hj (j : ℤ) (hj : j∈J) :
      lineSchwartzCommutator m (lineLowpass b l) (schwartzDerivative 1 (lineDyadic h j))=
        lowHighPiece m b h j+∑ i∈I, if i≤j+4 then F i j else 0 := by
    rw [lineLowpass_telescope_filtered b l (j+4) v (hl j hj) (hv j hj),
      lineSchwartzCommutator_add_left,lineSchwartzCommutator_sum_left]
    have he : lineSchwartzCommutator m (lineLowpass b (j+4))
        (schwartzDerivative 1 (lineDyadic h j))=lowHighPiece m b h j := by
      simp only [lineLowpass,lineDyadic,lowHighPiece,scale_add_four]
    rw [he]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hij : i≤j+4
    · simp only [ite_eq_left hij]
      rfl
    · simp only [ite_eq_right hij,lineSchwartzCommutator_zero_left]
  rw [schwartzDerivative_sum,lineSchwartzCommutator_sum_right]
  calc
    _ = ∑ j∈J, (lowHighPiece m b h j+∑ i∈I, if i≤j+4 then F i j else 0) :=
      Finset.sum_congr rfl hj
    _ = (∑ j∈J, lowHighPiece m b h j)+(∑ i∈I, ∑ j∈J, if i≤j+4 then F i j else 0) := by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
    _ = (∑ j∈J, lowHighPiece m b h j)+(∑ i∈I, (highLowRow J m b h i+
        lineSchwartzCommutator m (lineDyadic b i) (schwartzDerivative 1 (nearbyInput J h i)))) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [split_dyadic_interaction]
      rw [Finset.sum_add_distrib,lineCommutator_nearbyInput]
      rfl
    _ = _ := by rw [Finset.sum_add_distrib]; exact (add_assoc _ _ _).symm

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SmoothedCommutatorEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The assembled finite commutator bound has one constant, independent
of the coefficient smoothing and the number of input frequency bands. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem comparableCommutatorConstant_nonneg : 0 ≤ comparableCommutatorConstant := by
  unfold comparableCommutatorConstant
  have h := smoothCarlesonDualConstant_nonneg
  positivity

theorem lineCommutatorEnergyConstant_nonneg : 0≤lineCommutatorEnergyConstant := by
  unfold lineCommutatorEnergyConstant lineLowHighEnergyConstant lineHighLowEnergyConstant
  have h := comparableCommutatorConstant_nonneg
  positivity

theorem lineSchwartz_three_add_energy (f g h : SchwartzMap ℝ ℂ) :
    (∫ x, ‖(f+g+h) x‖^2)≤3*((∫ x, ‖f x‖^2)+(∫ x, ‖g x‖^2)+(∫ x, ‖h x‖^2)) := by
  simpa only [sub_neg_eq_add,neg_apply,norm_neg] using lineSchwartz_three_energy f (-g) h

theorem smoothedCommutator_energy (J : Finset ℤ) (m b h : SchwartzMap ℝ ℂ)
    (A L : ℝ) (hA : 0≤A)
    (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|)
    (l v : ℤ) (hl : ∀ j∈J, l≤j+4) (hv : ∀ j∈J, j+4≤v) :
    (∫ x, ‖lineSchwartzCommutator m (lineLowpass b l)
      (schwartzDerivative 1 (∑ j∈J, lineDyadic h j)) x‖^2)≤
        lineCommutatorEnergyConstant*A^2*L^2*(∫ x, ‖h x‖^2) := by
  let I := Finset.Icc (l+1) v
  let F := ∑ j∈J, lowHighPiece m b h j
  let G := ∑ i∈I, highLowRow J m b h i
  let H := ∑ i∈I, lineSchwartzCommutator m (lineDyadic b i)
    (schwartzDerivative 1 (nearbyInput J h i))
  have hm0 (eta : ℝ) : ‖m eta‖≤A := by
    simpa only [pow_zero,one_mul,iteratedDeriv_zero] using hm 0 (by norm_num) eta
  have hF : (∫ x, ‖F x‖^2)≤lineLowHighEnergyConstant*A^2*L^2*(∫ x, ‖h x‖^2) := by
    apply (lowHighSum_energy J m b h A L hA hm hLip).trans_eq
    unfold lineLowHighEnergyConstant
    ring
  have hG : (∫ x, ‖G x‖^2)≤lineHighLowEnergyConstant*A^2*L^2*(∫ x, ‖h x‖^2) := by
    apply (highLowSum_energy I J m b h A L hm0 hLip).trans_eq
    unfold lineHighLowEnergyConstant
    ring
  have hH : (∫ x, ‖H x‖^2)≤(49152*comparableCommutatorConstant)*A^2*L^2*(∫ x, ‖h x‖^2) := by
    have hc := comparableCommutatorSum_energy I m b (nearbyInput J h) A L hm0 hLip
      (fun i _ eta heta => nearbyInput_frequency J h i eta heta)
    have hnear := nearbyInput_energy I J h
    calc
      _ ≤ comparableCommutatorConstant*A^2*L^2*(∑ i∈I, ∫ x, ‖nearbyInput J h i x‖^2) := hc
      _ ≤ comparableCommutatorConstant*A^2*L^2*(49152*(∫ x, ‖h x‖^2)) :=
        mul_le_mul_of_nonneg_left hnear (by have := comparableCommutatorConstant_nonneg; positivity)
      _ = _ := by ring
  rw [smoothedCommutator_decomposition J m b h l v hl hv]
  calc
    _ ≤ 3*((∫ x, ‖F x‖^2)+(∫ x, ‖G x‖^2)+(∫ x, ‖H x‖^2)) := lineSchwartz_three_add_energy F G H
    _ ≤ 3*(lineLowHighEnergyConstant*A^2*L^2*(∫ x, ‖h x‖^2)+
        lineHighLowEnergyConstant*A^2*L^2*(∫ x, ‖h x‖^2)+
        (49152*comparableCommutatorConstant)*A^2*L^2*(∫ x, ‖h x‖^2)) := by gcongr
    _ = _ := by unfold lineCommutatorEnergyConstant; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineBoundedCommutatorL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! For a fixed bounded Schwartz coefficient the undifferentiated
commutator is an actual bounded L2 map. This identifies the limits of
the differentiated frequency approximations. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lineProductLM_apply (b f : SchwartzMap ℝ ℂ) :
    lineProductLM b f=lineSchwartzProduct b f := by
  ext x
  simp only [lineProductLM,ContinuousLinearMap.coe_coe,
    SchwartzMap.smulLeftCLM_apply_apply b.hasTemperateGrowth,smul_eq_mul,lineSchwartzProduct_apply]

theorem lineCommutatorLM_apply (m b f : SchwartzMap ℝ ℂ) :
    lineCommutatorLM m b f=lineSchwartzCommutator m b f := by
  simp only [lineCommutatorLM,LinearMap.sub_apply,LinearMap.comp_apply,lineProductLM_apply,
    lineSchwartzCommutator]
  rfl

theorem lineCommutatorToL2_bound (m b f : SchwartzMap ℝ ℂ) (A B : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hm : ∀ eta, ‖m eta‖≤A) (hb : ∀ x, ‖b x‖≤B) :
    ‖lineCommutatorToL2 m b f‖≤(2*A*B)*‖f.toLp 2 volume‖ := by
  have hh := lineSchwartzCommutator_bounded_energy m b f A B hm hb
  have ho := memLp_toL2_norm_sq volume _ ((lineSchwartzCommutator m b f).memLp 2 volume)
  have hf := memLp_toL2_norm_sq volume f (f.memLp 2 volume)
  change ‖(lineSchwartzCommutator m b f).toLp 2 volume‖^2=_ at ho
  change ‖f.toLp 2 volume‖^2=_ at hf
  rw [←ho,←hf] at hh
  have he : lineCommutatorToL2 m b f=(lineSchwartzCommutator m b f).toLp 2 volume := by
    change (lineCommutatorLM m b f).toLp 2 volume=_
    rw [lineCommutatorLM_apply]
  rw [he]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith only [hh]

theorem lineCommutatorL2_onSchwartz (m b f : SchwartzMap ℝ ℂ) :
    lineCommutatorL2 m b (f.toLp 2 volume)=(lineSchwartzCommutator m b f).toLp 2 volume := by
  have he : lineCommutatorL2 m b (f.toLp 2 volume)=lineCommutatorToL2 m b f := by
    apply LinearMap.extendOfNorm_eq
    · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
    · refine ⟨2*(SchwartzMap.seminorm ℝ 0 0 m)*(SchwartzMap.seminorm ℝ 0 0 b),fun g => ?_⟩
      exact lineCommutatorToL2_bound m b g _ _ (apply_nonneg _ _) (apply_nonneg _ _)
        (fun eta => m.norm_le_seminorm ℝ eta) (fun x => b.norm_le_seminorm ℝ x)
  rw [he]
  change (lineCommutatorLM m b f).toLp 2 volume=_
  rw [lineCommutatorLM_apply]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineCommutatorCoefficientLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform Lipschitz approximation of the coefficient identifies the
limit of the actual smoothed commutators in L2. -/
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform Topology
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem scale_neg_nat_tendsto :
    Tendsto (fun N : ℕ => scale (-(N:ℤ))) atTop (𝓝 (0:ℝ)) := by
  have hh := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)
  simpa only [scale,zpow_neg,zpow_natCast,one_div,inv_pow] using hh

theorem lineCommutator_lowpass_tendsto (m b f : SchwartzMap ℝ ℂ) (L : ℝ)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    Tendsto (fun N : ℕ => (lineSchwartzCommutator m (lineLowpass b (-(N:ℤ))) f).toLp 2 volume)
      atTop (𝓝 ((lineSchwartzCommutator m b f).toLp 2 volume)) := by
  let A := SchwartzMap.seminorm ℝ 0 0 m
  let M := ∫ t, |t| *‖(𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ) t‖
  let delta := fun N : ℕ => L*scale (-(N:ℤ))*M
  let F := fun N : ℕ => lineSchwartzCommutator m (lineLowpass b (-(N:ℤ))) f
  let G := lineSchwartzCommutator m b f
  have hd : Tendsto delta atTop (𝓝 0) := by
    have hh := (scale_neg_nat_tendsto.const_mul L).mul_const M
    simpa only [mul_zero,zero_mul] using hh
  have hb (N : ℕ) (x : ℝ) : ‖(lineLowpass b (-(N:ℤ))-b) x‖≤delta N := by
    simp only [lineLowpass,sub_apply,lineSchwartzProjection_eq_convolution]
    exact lowpassProjection_lipschitz_approximation (scale (-(N:ℤ))) (scale_pos _)
      b b.continuous.measurable (SchwartzMap.seminorm ℝ 0 0 b) (fun y => b.norm_le_seminorm ℝ y) L hLip x
  have hn (N : ℕ) : ‖(F N).toLp 2 volume-G.toLp 2 volume‖^2≤
      4*A^2*(delta N)^2*(∫ x, ‖f x‖^2) := by
    have hc := lineSchwartzCommutator_bounded_energy m (lineLowpass b (-(N:ℤ))-b) f A (delta N)
      (fun eta => m.norm_le_seminorm ℝ eta) (hb N)
    have he : (F N).toLp 2 volume-G.toLp 2 volume=
        (lineSchwartzCommutator m (lineLowpass b (-(N:ℤ))-b) f).toLp 2 volume := by
      rw [lineSchwartzCommutator_sub_left]
      exact (map_sub (SchwartzMap.toLpCLM ℂ ℂ 2 volume) (F N) G).symm
    rw [he]
    have hs := memLp_toL2_norm_sq volume _
      ((lineSchwartzCommutator m (lineLowpass b (-(N:ℤ))-b) f).memLp 2 volume)
    exact hs.trans_le hc
  have hupper : Tendsto (fun N : ℕ => 4*A^2*(delta N)^2*(∫ x, ‖f x‖^2)) atTop (𝓝 0) := by
    have hh := ((hd.pow 2).const_mul (4*A^2)).mul_const (∫ x, ‖f x‖^2)
    simpa only [zero_pow (by decide : 2≠0),mul_zero,zero_mul] using hh
  have hsquare := squeeze_zero (fun N => sq_nonneg ‖(F N).toLp 2 volume-G.toLp 2 volume‖) hn hupper
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  simp only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero,Function.comp_def] at hnorm
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineBandedCommutatorEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing coefficient smoothing gives the uniform commutator bound
for every finite collection of actual input frequency bands. -/
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

theorem lineBandedCommutator_energy (J : Finset ℤ) (m b h : SchwartzMap ℝ ℂ)
    (A L : ℝ) (hA : 0≤A)
    (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    (∫ x, ‖lineSchwartzCommutator m b (schwartzDerivative 1 (∑ j∈J, lineDyadic h j)) x‖^2)≤
      lineCommutatorEnergyConstant*A^2*L^2*(∫ x, ‖h x‖^2) := by
  classical
  by_cases hJ : J.Nonempty
  · let v := J.max' hJ+4
    let N₀ := (-J.min' hJ-4).toNat
    let f := schwartzDerivative 1 (∑ j∈J, lineDyadic h j)
    have hlimit := (lineCommutator_lowpass_tendsto m b f L hLip).norm.pow 2
    have hnorm (g : SchwartzMap ℝ ℂ) : ‖g.toLp 2 volume‖^2=∫ x, ‖g x‖^2 :=
      memLp_toL2_norm_sq volume g (g.memLp 2 volume)
    have hevent : ∀ᶠ N : ℕ in atTop,
        ‖(lineSchwartzCommutator m (lineLowpass b (-(N:ℤ))) f).toLp 2 volume‖^2≤
          lineCommutatorEnergyConstant*A^2*L^2*(∫ x, ‖h x‖^2) := by
      filter_upwards [eventually_ge_atTop N₀] with N hN
      have hlo (j : ℤ) (hj : j∈J) : -(N:ℤ)≤j+4 := by
        have hmin := Finset.min'_le J j hj
        dsimp [N₀] at hN
        omega
      have hhi (j : ℤ) (hj : j∈J) : j+4≤v := by
        have hmax := Finset.le_max' J j hj
        dsimp [v]
        omega
      simpa only [hnorm] using smoothedCommutator_energy J m b h A L hA hm hLip (-(N:ℤ)) v hlo hhi
    simpa only [hnorm] using le_of_tendsto hlimit hevent
  · have he : J=∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    subst J
    simp only [Finset.sum_empty,schwartzDerivative_zero,lineSchwartzCommutator_zero_right,
      zero_apply,norm_zero,zero_pow (by decide : 2≠0),integral_zero]
    have hc := lineCommutatorEnergyConstant_nonneg
    positivity

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSchwartzCommutatorEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Lipschitz multiplier commutator estimate on Schwartz
functions, after both coefficient and input cutoffs have been removed. -/
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

theorem dyadicSchwartzSum_derivative (N : ℕ) (h : SchwartzMap ℝ ℂ) :
    schwartzDerivative 1 (dyadicSchwartzSum N h)=
      dyadicSchwartzSum N (schwartzDerivative 1 h) := by
  simp only [dyadicSchwartzSum,schwartzDerivative_sum,lineSchwartzProjection_derivative]

theorem lineSchwartz_lipschitz_commutator_energy (m b h : SchwartzMap ℝ ℂ)
    (A L : ℝ) (hA : 0≤A)
    (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    (∫ x, ‖lineSchwartzCommutator m b (schwartzDerivative 1 h) x‖^2)≤
      lineCommutatorEnergyConstant*A^2*L^2*(∫ x, ‖h x‖^2) := by
  have hlimit := (lineCommutatorL2 m b).continuous.tendsto
    ((schwartzDerivative 1 h).toLp 2 volume) |>.comp (dyadicSchwartzSum_Lp_tendsto (schwartzDerivative 1 h))
  simp only [Function.comp_def,lineCommutatorL2_onSchwartz,←dyadicSchwartzSum_derivative] at hlimit
  have hnorm (g : SchwartzMap ℝ ℂ) : ‖g.toLp 2 volume‖^2=∫ x, ‖g x‖^2 :=
    memLp_toL2_norm_sq volume g (g.memLp 2 volume)
  have hevent : ∀ᶠ N : ℕ in atTop,
      ‖(lineSchwartzCommutator m b (schwartzDerivative 1 (dyadicSchwartzSum N h))).toLp 2 volume‖^2≤
        lineCommutatorEnergyConstant*A^2*L^2*(∫ x, ‖h x‖^2) := by
    apply Filter.Eventually.of_forall
    intro N
    rw [hnorm,dyadicSchwartzSum_eq_window]
    exact lineBandedCommutator_energy (dyadicResolutionWindow N) m b h A L hA hm hLip
  simpa only [hnorm] using le_of_tendsto (hlimit.norm.pow 2) hevent

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineDerivativeCommutatorL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The differentiated Lipschitz commutator has its actual bounded L2
extension, with the uniform constant proved by dyadic decomposition. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lineCommutatorNormConstant_nonneg : 0≤lineCommutatorNormConstant := Real.sqrt_nonneg _

theorem lineCommutatorNormConstant_sq : lineCommutatorNormConstant^2=lineCommutatorEnergyConstant :=
  Real.sq_sqrt lineCommutatorEnergyConstant_nonneg

theorem lineDerivativeCommutatorToL2_apply (m b h : SchwartzMap ℝ ℂ) :
    lineDerivativeCommutatorToL2 m b h=(lineSchwartzCommutator m b (schwartzDerivative 1 h)).toLp 2 volume := by
  change (lineCommutatorLM m b (schwartzDerivative 1 h)).toLp 2 volume=_
  rw [lineCommutatorLM_apply]

theorem lineDerivativeCommutatorToL2_bound (m b h : SchwartzMap ℝ ℂ)
    (A L : ℝ) (hA : 0≤A)
    (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    ‖lineDerivativeCommutatorToL2 m b h‖≤lineCommutatorNormConstant*A*L*‖h.toLp 2 volume‖ := by
  have hL := (schwartzDerivative_lipschitz_bound b L hLip).1
  have hc := lineSchwartz_lipschitz_commutator_energy m b h A L hA hm hLip
  have hn (f : SchwartzMap ℝ ℂ) : ‖f.toLp 2 volume‖^2=∫ x, ‖f x‖^2 :=
    memLp_toL2_norm_sq volume f (f.memLp 2 volume)
  rw [lineDerivativeCommutatorToL2_apply]
  apply (sq_le_sq₀ (norm_nonneg _) (by have := lineCommutatorNormConstant_nonneg; positivity)).mp
  rw [mul_pow,mul_pow,mul_pow,lineCommutatorNormConstant_sq,hn,hn]
  exact hc

theorem lineDerivativeCommutatorL2_onSchwartz (m b h : SchwartzMap ℝ ℂ)
    (A L : ℝ) (hA : 0≤A)
    (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    lineDerivativeCommutatorL2 m b (h.toLp 2 volume)=
      (lineSchwartzCommutator m b (schwartzDerivative 1 h)).toLp 2 volume := by
  rw [←lineDerivativeCommutatorToL2_apply]
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · exact ⟨lineCommutatorNormConstant*A*L,fun g =>
      lineDerivativeCommutatorToL2_bound m b g A L hA hm hLip⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSamplingEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual one-dimensional composition operators with uniform L2
bounds from the inverse Lipschitz estimate. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lineCompositionToL2_bound (phi : ℝ → ℝ) (hm : Measurable phi) (ha : AntilipschitzWith 2 phi)
    (f : SchwartzMap ℝ ℂ) : ‖lineCompositionToL2 phi hm ha f‖≤2*‖f.toLp 2 volume‖ := by
  have hc := line_memLp_comp phi hm ha f f.continuous.measurable (f.memLp 2 volume)
  have hn := memLp_toL2_norm_sq volume _ hc.1
  have hf := memLp_toL2_norm_sq volume f (f.memLp 2 volume)
  change ‖lineCompositionToL2 phi hm ha f‖^2=_ at hn
  change ‖f.toLp 2 volume‖^2=_ at hf
  have hh : ‖lineCompositionToL2 phi hm ha f‖^2≤2*‖f.toLp 2 volume‖^2 := by
    rw [hn,hf]
    exact hc.2
  nlinarith [norm_nonneg (lineCompositionToL2 phi hm ha f),norm_nonneg (f.toLp 2 volume)]

theorem lineCompositionL2_onSchwartz (phi : ℝ → ℝ) (hm : Measurable phi)
    (ha : AntilipschitzWith 2 phi) (f : SchwartzMap ℝ ℂ) :
    lineCompositionL2 phi hm ha (f.toLp 2 volume)=lineCompositionToL2 phi hm ha f := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · exact ⟨2,lineCompositionToL2_bound phi hm ha⟩

theorem lineCompositionL2_bound (phi : ℝ → ℝ) (hm : Measurable phi) (ha : AntilipschitzWith 2 phi) :
    ‖lineCompositionL2 phi hm ha‖≤2 := by
  apply LinearMap.opNorm_extendOfNorm_le
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · norm_num
  · exact lineCompositionToL2_bound phi hm ha

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSamplingGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual conjugation generator for a compact smooth direction.
Its Lipschitz bound is uniform in the short time parameter. -/
noncomputable section
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

theorem lineSamplingGenerator_lipschitz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) :
    LipschitzWith 2 (lineSamplingGenerator u hu B hB hb t ht) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (-u ((lineSamplingHomeomorph u hu B hB hb t ht).symm x))
    (-u ((lineSamplingHomeomorph u hu B hB hb t ht).symm y))≤(2:ℝ)*dist x y
  rw [dist_neg_neg]
  simpa only [one_mul,Function.comp_def,NNReal.coe_ofNat] using
    (hu.comp (lineSamplingHomeomorph_symm_lipschitz u hu B hB hb t ht)).dist_le_mul x y

theorem lineSamplingGeneratorSchwartz_apply (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) (y : ℝ) :
    lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht y=
      (lineSamplingGenerator u hu B hB hb t ht y : ℂ) := rfl

theorem lineSamplingGeneratorSchwartz_lipschitz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) (x y : ℝ) :
    ‖lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht x-
      lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht y‖≤2*|x-y| := by
  have hh := (lineSamplingGenerator_lipschitz u hu B hB hb t ht).dist_le_mul x y
  simpa only [lineSamplingGeneratorSchwartz_apply,←Complex.ofReal_sub,Complex.norm_real,
    Real.dist_eq,Real.norm_eq_abs,NNReal.coe_ofNat] using hh

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSamplingSchwartz
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual forward and inverse sampling operators on Schwartz functions. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

theorem lineCompositionL2_schwartz (phi : ℝ → ℝ) (hg : phi.HasTemperateGrowth)
    (ha : AntilipschitzWith 2 phi) (f : SchwartzMap ℝ ℂ) :
    lineCompositionL2 phi hg.1.continuous.measurable ha (f.toLp 2 volume)=
      (SchwartzMap.compCLMOfAntilipschitz ℂ hg ha f).toLp 2 volume := by
  rw [lineCompositionL2_onSchwartz]
  rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineSamplingL2Path
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded L2 sampling paths and their agreement with the Schwartz paths. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

variable (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
  (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
  (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)

theorem lineSamplingL2Path_onSchwartz (s : ℝ) (f : SchwartzMap ℝ ℂ) :
    lineSamplingL2Path u hu s (f.toLp 2 volume)=
      (lineSamplingPath u hu hc hcompact s f).toLp 2 volume := by
  by_cases hs : |s|≤1/2
  · simp only [lineSamplingL2Path,lineSamplingPath,dite_eq_left hs]
    exact lineCompositionL2_schwartz _ (lineSampling_temperate u hc hcompact s) _ f
  · simp only [lineSamplingL2Path,lineSamplingPath,dite_eq_right hs,ContinuousLinearMap.id_apply]

theorem lineSamplingInverseL2Path_onSchwartz (s : ℝ) (f : SchwartzMap ℝ ℂ) :
    lineSamplingInverseL2Path u hu B hB hb s (f.toLp 2 volume)=
      (lineSamplingInversePath u hu hc hcompact B hB hb s f).toLp 2 volume := by
  by_cases hs : |s|≤1/2
  · simp only [lineSamplingInverseL2Path,lineSamplingInversePath,dite_eq_left hs]
    exact lineCompositionL2_schwartz _ (lineSamplingInverse_temperate u hu hc hcompact B hB hb s hs) _ f
  · simp only [lineSamplingInverseL2Path,lineSamplingInversePath,dite_eq_right hs,ContinuousLinearMap.id_apply]

theorem lineSamplingL2Path_bound (s : ℝ) : ‖lineSamplingL2Path u hu s‖≤2 := by
  by_cases hs : |s|≤1/2
  · simp only [lineSamplingL2Path,dite_eq_left hs]
    exact lineCompositionL2_bound _ _ _
  · simp only [lineSamplingL2Path,dite_eq_right hs]
    exact (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure ℝ))‖≤1).trans (by norm_num)

theorem lineSamplingInverseL2Path_bound (s : ℝ) : ‖lineSamplingInverseL2Path u hu B hB hb s‖≤2 := by
  by_cases hs : |s|≤1/2
  · simp only [lineSamplingInverseL2Path,dite_eq_left hs]
    exact lineCompositionL2_bound _ _ _
  · simp only [lineSamplingInverseL2Path,dite_eq_right hs]
    exact (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure ℝ))‖≤1).trans (by norm_num)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineConjugationBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating the strong conjugation derivative with a uniform bound. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

variable (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
  (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
  (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)

theorem lineConjugation_derivative_bound_oai (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (t : ℝ) (ht : |t|≤1/2) (f : SchwartzMap ℝ ℂ) :
    ‖(lineSamplingSchwartz u hu hc hcompact t ht
        (lineSchwartzCommutator m (lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht)
          (schwartzDerivative 1 (lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht f)))).toLp 2 volume‖≤
      8*lineCommutatorNormConstant*A*‖f.toLp 2 volume‖ := by
  let I := lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht f
  let b := lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht
  let D := lineDerivativeCommutatorL2 m b
  have hD : ‖D‖≤2*lineCommutatorNormConstant*A :=
    lineSamplingGenerator_commutator_bound m A hA hm u hu hc hcompact B hB hb t ht
  have hI : ‖I.toLp 2 volume‖≤2*‖f.toLp 2 volume‖ := by
    have hh := (lineSamplingInverseL2Path u hu B hB hb t).le_opNorm (f.toLp 2 volume)
    have hi := lineSamplingInverseL2Path_bound u hu B hB hb t
    rw [lineSamplingInverseL2Path_onSchwartz u hu hc hcompact B hB hb] at hh
    simpa only [lineSamplingInversePath,dite_eq_left ht,I] using
      hh.trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
  have hDc : D (I.toLp 2 volume)=(lineSchwartzCommutator m b (schwartzDerivative 1 I)).toLp 2 volume :=
    lineDerivativeCommutatorL2_onSchwartz m b I A 2 hA hm
      (lineSamplingGeneratorSchwartz_lipschitz u hu hc hcompact B hB hb t ht)
  have hC : lineSamplingL2Path u hu t (D (I.toLp 2 volume))=
      (lineSamplingSchwartz u hu hc hcompact t ht
        (lineSchwartzCommutator m b (schwartzDerivative 1 I))).toLp 2 volume := by
    rw [hDc,lineSamplingL2Path_onSchwartz u hu hc hcompact]
    simp only [lineSamplingPath,dite_eq_left ht]
  change ‖(lineSamplingSchwartz u hu hc hcompact t ht
    (lineSchwartzCommutator m b (schwartzDerivative 1 I))).toLp 2 volume‖≤_
  rw [←hC]
  calc
    _ ≤ 2*‖D (I.toLp 2 volume)‖ :=
      ((lineSamplingL2Path u hu t).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (lineSamplingL2Path_bound u hu t) (norm_nonneg _))
    _ ≤ 2*((2*lineCommutatorNormConstant*A)*‖I.toLp 2 volume‖) :=
      mul_le_mul_of_nonneg_left ((D.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hD (norm_nonneg _))) (by norm_num)
    _ ≤ 2*((2*lineCommutatorNormConstant*A)*(2*‖f.toLp 2 volume‖)) := by
      gcongr
      exact mul_nonneg (mul_nonneg (by norm_num) lineCommutatorNormConstant_nonneg) hA
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.PacketRepresentation.lineConjugation_derivative_bound_oai := @OAI.LipschitzHilbert.PacketRepresentation.lineConjugation_derivative_bound_oai
