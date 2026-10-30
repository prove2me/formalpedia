-- Prove2me | solution 1 for OAI.LipschitzHilbert.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:09:46.024476+00:00
-- url     : https://prove2.me/submissions/c360e143-4d9a-4129-b1ce-341e1808da68

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_LipschitzHilbert
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_laceyLiInput_proved
import Theorems.Thm_OAI_LipschitzHilbert_main_of_three_published_inputs

section
-- module Solutions.OAIQ090_LH.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CubicDualityEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar exponent calculation in the three-halves dual estimate. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem cubic_duality_estimate (F J E : ℝ) (hF : 0≤F) (hJ : 0≤J) (hE : 0≤E)
    (h : J≤F^(2/3:ℝ)*(E*J)^(1/3:ℝ)) : J≤(E+1)^(3/2:ℝ)*F := by
  have hcube := pow_le_pow_left₀ hJ h 3
  have hFp : (F^(2/3:ℝ))^3=F^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hF]
    norm_num
  have hEJp : ((E*J)^(1/3:ℝ))^3=E*J := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (mul_nonneg hE hJ)]
    norm_num
  rw [mul_pow,hFp,hEJp] at hcube
  by_cases hz : J=0
  · rw [hz]
    positivity
  have hJp : 0<J := lt_of_le_of_ne hJ (Ne.symm hz)
  have hs : J^2≤E*F^2 := by
    by_contra hn
    have hp : 0<J*(J^2-E*F^2) := mul_pos hJp (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith [hcube]
  have hcoef : E≤(E+1)^3 := by nlinarith [sq_nonneg E,pow_nonneg hE 3]
  have hpower : ((E+1)^(3/2:ℝ)*F)^2=(E+1)^3*F^2 := by
    rw [mul_pow,←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0≤E+1)]
    norm_num
  apply (sq_le_sq₀ hJ (by positivity : 0≤(E+1)^(3/2:ℝ)*F)).mp
  rw [hpower]
  exact hs.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg F))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cubic variation and its dimension-free Euclidean comparison. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem finiteCubicVariation_nonneg {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) : 0 ≤ finiteCubicVariation F N := by
  classical
  apply Finset.le_sup'_of_le (f := fun p : Fin (N + 1) → Fin (N + 1) =>
    if Monotone p then ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
    (Finset.mem_univ (fun _ => 0))
  simp

theorem partition_le_finiteCubicVariation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) (p : Fin (N + 1) → Fin (N + 1)) (hp : Monotone p) :
    (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3) ≤
      finiteCubicVariation F N := by
  classical
  simpa only [finiteCubicVariation, ite_eq_left hp] using
    (Finset.le_sup' (fun p : Fin (N + 1) → Fin (N + 1) =>
      if Monotone p then ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
      (Finset.mem_univ p))

theorem scalar_finiteCubicVariation {Ω : Type*} (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    ENNReal.ofReal (finiteCubicVariation (fun n => F n x) N) = variationCube F N x := by
  classical
  have heq (p : Fin (N + 1) → Fin (N + 1)) :
      ENNReal.ofReal (if Monotone p then
        ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0) =
      if Monotone p then
        ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ₑ ^ 3 else 0 := by
    split_ifs
    · rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    · exact ENNReal.ofReal_zero
  apply le_antisymm
  · obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun p : Fin (N + 1) → Fin (N + 1) => if Monotone p then
        ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0)
    change ENNReal.ofReal (Finset.univ.sup' _ _) ≤ _
    rw [hp, heq]
    change (if Monotone p then ∑ i : Fin N,
      ‖F (p i.succ) x - F (p i.castSucc) x‖ₑ ^ 3 else 0) ≤
      Finset.univ.sup _
    exact Finset.le_sup (f := fun q : Fin (N + 1) → Fin (N + 1) =>
      if Monotone q then ∑ i : Fin N,
        ‖F (q i.succ) x - F (q i.castSucc) x‖ₑ ^ 3 else 0) (Finset.mem_univ p)
  · apply Finset.sup_le
    intro p _
    rw [← heq]
    apply ENNReal.ofReal_le_ofReal
    exact Finset.le_sup' (fun p : Fin (N + 1) → Fin (N + 1) =>
      if Monotone p then ∑ i : Fin N,
        ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0) (Finset.mem_univ p)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TimeErrorEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A normalized integrable envelope for the two endpoint errors in a
sharp time truncation. Its integral is independent of its radius. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem timeErrorEnvelope_nonneg (r t : ℝ) (hr : 0 < r) : 0≤timeErrorEnvelope r t := by
  unfold timeErrorEnvelope
  positivity

theorem timeErrorEnvelope_eq (r t : ℝ) (hr : 0 < r) :
    timeErrorEnvelope r t=r⁻¹*lineEnvelope 0 r 1 t := by
  unfold timeErrorEnvelope lineEnvelope
  simp only [sub_zero,pow_one]
  have hden : r^2+t^2≠0 := ne_of_gt (by positivity)
  have hden' : 1+(t/r)^2≠0 := ne_of_gt (by positivity)
  field_simp

theorem timeErrorEnvelope_integrable (r : ℝ) (hr : 0 < r) :
    Integrable (timeErrorEnvelope r) := by
  have h := (integrable_lineEnvelope_one 0 r hr).const_mul r⁻¹
  simpa only [←timeErrorEnvelope_eq r _ hr] using h

theorem timeErrorEnvelope_integral (r : ℝ) (hr : 0 < r) :
    (∫ t, timeErrorEnvelope r t)=Real.pi := by
  simp_rw [timeErrorEnvelope_eq r _ hr]
  rw [integral_const_mul,integral_lineEnvelope_one 0 r hr]
  field_simp

theorem timeErrorEnvelope_small (r t : ℝ) (hr : 0 < r) (ht : |t| ≤ r) :
    r⁻¹≤2*timeErrorEnvelope r t := by
  have ht2 : t^2 ≤ r^2 := by nlinarith [sq_abs t,pow_le_pow_left₀ (abs_nonneg t) ht 2]
  have hd : 0 < r^2+t^2 := by positivity
  unfold timeErrorEnvelope
  rw [←mul_div_assoc]
  apply (le_div_iff₀ hd).2
  rw [inv_mul_eq_div]
  apply (div_le_iff₀ hr).2
  nlinarith

theorem timeErrorEnvelope_large (r t : ℝ) (hr : 0 < r) (ht : r≤|t|) :
    r/t^2≤2*timeErrorEnvelope r t := by
  have ht2 : r^2≤t^2 := by nlinarith [sq_abs t,pow_le_pow_left₀ hr.le ht 2]
  have hd : 0 < r^2+t^2 := by positivity
  have htpos : 0<t^2 := lt_of_lt_of_le (sq_pos_of_pos hr) ht2
  unfold timeErrorEnvelope
  rw [←mul_div_assoc]
  apply (div_le_div_iff₀ htpos hd).2
  nlinarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteTimeKernelMoment
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
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

theorem finiteTimeKernel_measurable (k : SchwartzMap ℝ ℂ) (N : ℕ) (topLength : ℝ) :
    Measurable (finiteTimeKernel k N topLength) := by
  unfold finiteTimeKernel scaledTimeKernel
  fun_prop

theorem finiteTimeKernel_integrable (k : SchwartzMap ℝ ℂ) (N : ℕ) (topLength : ℝ)
    (htop : 0<topLength) : Integrable (finiteTimeKernel k N topLength) := by
  exact integrable_finsetSum _ (fun j _ => scaledTimeKernel_integrable k k.integrable _
    (ne_of_gt (div_pos htop (pow_pos (by norm_num) j.val))))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicKernelTelescoping
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact telescoping identity behind the finite Hilbert time-kernel
decomposition. The cutoff profile will be constructed independently. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem finiteTimeKernel_telescope (k : SchwartzMap ℝ ℂ) (a : ℝ → ℂ)
    (hprofile : ∀ s : ℝ, (s : ℂ)*k s=a s-a (s/2))
    (N : ℕ) (topLength : ℝ) (htop : 0<topLength) (t : ℝ) :
    (t : ℂ)*finiteTimeKernel k N topLength t=
      a ((2:ℝ)^N*t/(2*topLength))-a (t/(2*topLength)) := by
  have hterm (j : Fin N) : (t : ℂ)*scaledTimeKernel k (topLength/(2:ℝ)^j.val) t=
      a ((2:ℝ)^(j.val+1)*t/(2*topLength))-a ((2:ℝ)^j.val*t/(2*topLength)) := by
    have hl : 0<topLength/(2:ℝ)^j.val := div_pos htop (pow_pos (by norm_num) _)
    have heq : (t : ℂ)*scaledTimeKernel k (topLength/(2:ℝ)^j.val) t=
        ((t/(topLength/(2:ℝ)^j.val) : ℝ) : ℂ)*k (t/(topLength/(2:ℝ)^j.val)) := by
      unfold scaledTimeKernel
      push_cast
      ring
    rw [heq,hprofile]
    have harg : t/(topLength/(2:ℝ)^j.val)=(2:ℝ)^(j.val+1)*t/(2*topLength) := by
      rw [pow_succ]
      field_simp
    have hhalf : (t/(topLength/(2:ℝ)^j.val))/2=(2:ℝ)^j.val*t/(2*topLength) := by
      field_simp
    rw [harg]
    congr 1
    rw [←harg,hhalf]
  unfold finiteTimeKernel
  rw [Finset.mul_sum]
  simp_rw [hterm]
  change (∑ j : Fin N, (fun n : ℕ =>
    a ((2:ℝ)^(n+1)*t/(2*topLength))-a ((2:ℝ)^n*t/(2*topLength))) j.val)=_
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ =>
    a ((2:ℝ)^(n+1)*t/(2*topLength))-a ((2:ℝ)^n*t/(2*topLength))) N]
  simpa only [pow_zero,one_mul] using
    Finset.sum_range_sub (fun n : ℕ => a ((2:ℝ)^n*t/(2*topLength))) N

theorem finiteTimeKernel_eq_profileDifference (k : SchwartzMap ℝ ℂ) (a : ℝ → ℂ)
    (hprofile : ∀ s : ℝ, (s : ℂ)*k s=a s-a (s/2))
    (N : ℕ) (topLength : ℝ) (htop : 0<topLength) (t : ℝ) (ht : t≠0) :
    finiteTimeKernel k N topLength t=
      profileKernelDifference a (2*topLength/(2:ℝ)^N) (2*topLength) t := by
  have h := finiteTimeKernel_telescope k a hprofile N topLength htop t
  have harg : t/(2*topLength/(2:ℝ)^N)=(2:ℝ)^N*t/(2*topLength) := by field_simp
  unfold profileKernelDifference
  rw [harg]
  apply (eq_div_iff (by exact_mod_cast ht : (t:ℂ)≠0)).2
  simpa only [mul_comm] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SharpKernelComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two endpoint envelopes control sharp truncation versus a telescoped
kernel. The profile conditions are local construction obligations. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem profile_far_bound (a : ℝ → ℂ) (D : ℝ)
    (hfar : ∀ s, |s| *‖a s‖≤D) (r t : ℝ) (hr : 0 < r) (ht : t≠0) :
    ‖a (t/r)‖≤D*r/|t| := by
  have hf : ‖a (t/r)‖*|t|/r≤D := by
    simpa only [abs_div,abs_of_pos hr,div_mul_eq_mul_div,mul_comm] using hfar (t/r)
  apply (le_div_iff₀ (abs_pos.mpr ht)).2
  exact (div_le_iff₀ hr).1 hf

theorem sharpKernelComparison_pointwise (a : ℝ → ℂ) (D : ℝ) (hD : 0≤D)
    (hnear : ∀ s, ‖a s+1‖≤D*|s|) (hfar : ∀ s, |s| *‖a s‖≤D)
    (r R : ℝ) (hr : 0 < r) (hrR : r≤R) (t : ℝ) :
    ‖sharpTimeKernel r R t-profileKernelDifference a r R t‖≤
      4*D*(timeErrorEnvelope r t+timeErrorEnvelope R t) := by
  have hR : 0<R := hr.trans_le hrR
  have hqr := timeErrorEnvelope_nonneg r t hr
  have hqR := timeErrorEnvelope_nonneg R t hR
  by_cases ht0 : t=0
  · subst t
    have hs : ¬(r < |(0:ℝ)| ∧ |(0:ℝ)| < R) := by simp [not_lt_of_ge hr.le]
    simp only [sharpTimeKernel,ite_eq_right hs,profileKernelDifference,
      Complex.ofReal_zero,div_zero,sub_zero,norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤4) hD) (add_nonneg hqr hqR)
  have ht : 0 < |t| := abs_pos.mpr ht0
  have hnear_r : ‖a (t/r)+1‖≤D*(|t|/r) := by
    simpa only [abs_div,abs_of_pos hr] using hnear (t/r)
  have hnear_R : ‖a (t/R)+1‖≤D*(|t|/R) := by
    simpa only [abs_div,abs_of_pos hR] using hnear (t/R)
  have hfar_r := profile_far_bound a D hfar r t hr ht0
  have hfar_R := profile_far_bound a D hfar R t hR ht0
  by_cases hlo : |t| ≤ r
  · have hs : ¬(r < |t| ∧ |t| < R) := by intro h; linarith [h.1]
    have hnum : ‖a (t/r)-a (t/R)‖≤2*D*|t|/r := by
      have hn := norm_sub_le (a (t/r)+1) (a (t/R)+1)
      have hdiff : (a (t/r)+1)-(a (t/R)+1)=a (t/r)-a (t/R) := by ring
      rw [hdiff] at hn
      have hdiv := div_le_div_of_nonneg_left ht.le hr hrR
      calc
        _ ≤ D*(|t|/r)+D*(|t|/r) := hn.trans
          (add_le_add hnear_r (hnear_R.trans (mul_le_mul_of_nonneg_left hdiv hD)))
        _ = _ := by ring
    calc
      _ = ‖a (t/r)-a (t/R)‖/|t| := by
        simp only [sharpTimeKernel,ite_eq_right hs,profileKernelDifference,zero_sub,norm_neg,
          norm_div,Complex.norm_real,Real.norm_eq_abs]
      _ ≤ (2*D*|t|/r)/|t| := div_le_div_of_nonneg_right hnum ht.le
      _ = 2*D*r⁻¹ := by field_simp
      _ ≤ 4*D*timeErrorEnvelope r t := by
        have h := mul_le_mul_of_nonneg_left (timeErrorEnvelope_small r t hr hlo) (mul_nonneg (by norm_num : (0:ℝ)≤2) hD)
        nlinarith only [h]
      _ ≤ _ := by nlinarith only [mul_nonneg hD hqR]
  · have htr : r < |t| := lt_of_not_ge hlo
    by_cases hhi : |t| < R
    · have hnum : ‖1-a (t/r)+a (t/R)‖≤D*r/|t|+D*(|t|/R) := by
        have heq : (1:ℂ)-a (t/r)+a (t/R)=(-a (t/r))+(a (t/R)+1) := by ring
        rw [heq]
        exact (norm_add_le _ _).trans (add_le_add (by simpa only [norm_neg] using hfar_r) hnear_R)
      have hform : sharpTimeKernel r R t-profileKernelDifference a r R t=
          ((1:ℂ)-a (t/r)+a (t/R))/(t : ℂ) := by
        have hs : r < |t| ∧ |t| < R := ⟨htr,hhi⟩
        simp only [sharpTimeKernel,ite_eq_left hs,profileKernelDifference]
        field_simp
        ring
      calc
        _ = ‖1-a (t/r)+a (t/R)‖/|t| := by rw [hform,norm_div,Complex.norm_real,Real.norm_eq_abs]
        _ ≤ (D*r/|t|+D*(|t|/R))/|t| := div_le_div_of_nonneg_right hnum ht.le
        _ = D*(r/t^2)+D*R⁻¹ := by rw [←sq_abs t]; field_simp
        _ ≤ 2*D*timeErrorEnvelope r t+2*D*timeErrorEnvelope R t := by
          have hrb := mul_le_mul_of_nonneg_left (timeErrorEnvelope_large r t hr htr.le) hD
          have hRb := mul_le_mul_of_nonneg_left (timeErrorEnvelope_small R t hR hhi.le) hD
          nlinarith only [hrb,hRb]
        _ ≤ _ := by nlinarith only [mul_nonneg hD hqr,mul_nonneg hD hqR]
    · have hs : ¬(r < |t| ∧ |t| < R) := by intro h; exact hhi h.2
      have hnum : ‖a (t/r)-a (t/R)‖≤2*D*R/|t| := by
        have h := (norm_sub_le _ _).trans (add_le_add hfar_r hfar_R)
        have hmon := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrR hD) ht.le
        calc
          _ ≤ D*R/|t|+D*R/|t| := h.trans (add_le_add hmon (le_refl _))
          _ = _ := by ring
      calc
        _ = ‖a (t/r)-a (t/R)‖/|t| := by
          simp only [sharpTimeKernel,ite_eq_right hs,profileKernelDifference,zero_sub,norm_neg,
            norm_div,Complex.norm_real,Real.norm_eq_abs]
        _ ≤ (2*D*R/|t|)/|t| := div_le_div_of_nonneg_right hnum ht.le
        _ = 2*D*(R/t^2) := by rw [←sq_abs t]; field_simp
        _ ≤ 4*D*timeErrorEnvelope R t := by
          have h := mul_le_mul_of_nonneg_left
            (timeErrorEnvelope_large R t hR (le_of_not_gt hhi)) (mul_nonneg (by norm_num : (0:ℝ)≤2) hD)
          nlinarith only [h]
        _ ≤ _ := by nlinarith only [mul_nonneg hD hqr]

end LipschitzHilbert.PacketRepresentation

namespace LipschitzHilbert.PacketRepresentation

theorem sharpKernelComparison_integral (a : ℝ → ℂ) (ha : Measurable a)
    (D : ℝ) (hD : 0≤D) (hnear : ∀ s, ‖a s+1‖≤D*|s|)
    (hfar : ∀ s, |s| *‖a s‖≤D) (r R : ℝ) (hr : 0 < r) (hrR : r≤R) :
    Integrable (fun t => sharpTimeKernel r R t-profileKernelDifference a r R t) ∧
      (∫ t, ‖sharpTimeKernel r R t-profileKernelDifference a r R t‖)≤8*Real.pi*D := by
  have hR := hr.trans_le hrR
  have hi := ((timeErrorEnvelope_integrable r hr).add
    (timeErrorEnvelope_integrable R hR)).const_mul (4*D)
  have hm : Measurable (fun t => sharpTimeKernel r R t-profileKernelDifference a r R t) := by
    apply (sharpTimeKernel_measurable r R).sub
    unfold profileKernelDifference
    exact ((ha.comp (by fun_prop)).sub (ha.comp (by fun_prop))).div (by fun_prop)
  have hb (t : ℝ) := sharpKernelComparison_pointwise a D hD hnear hfar r R hr hrR t
  have he := hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine ⟨he,?_⟩
  calc
    _ ≤ ∫ t, 4*D*(timeErrorEnvelope r t+timeErrorEnvelope R t) :=
      integral_mono he.norm hi hb
    _ = 8*Real.pi*D := by
      rw [integral_const_mul,integral_add (timeErrorEnvelope_integrable r hr)
        (timeErrorEnvelope_integrable R hR),timeErrorEnvelope_integral r hr,
        timeErrorEnvelope_integral R hR]
      ring

theorem finiteTimeKernel_sharp_integral (k : SchwartzMap ℝ ℂ) (a : ℝ → ℂ)
    (ha : Measurable a) (hprofile : ∀ s : ℝ, (s : ℂ)*k s=a s-a (s/2))
    (D : ℝ) (hD : 0≤D) (hnear : ∀ s, ‖a s+1‖≤D*|s|)
    (hfar : ∀ s, |s| *‖a s‖≤D) (N : ℕ) (topLength : ℝ) (htop : 0<topLength) :
    Integrable (fun t => sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
      finiteTimeKernel k N topLength t) ∧
    (∫ t, ‖sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
      finiteTimeKernel k N topLength t‖)≤8*Real.pi*D := by
  have hr : 0<2*topLength/(2:ℝ)^N := by positivity
  have hrR : 2*topLength/(2:ℝ)^N≤2*topLength := by
    apply div_le_self (by positivity)
    exact one_le_pow₀ (by norm_num)
  have heq : (fun t => sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
      finiteTimeKernel k N topLength t) =ᵐ[volume]
      (fun t => sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        profileKernelDifference a (2*topLength/(2:ℝ)^N) (2*topLength) t) := by
    filter_upwards [volume.ae_ne (0:ℝ)] with t ht
    rw [finiteTimeKernel_eq_profileDifference k a hprofile N topLength htop t ht]
  obtain ⟨hi,hbound⟩ := sharpKernelComparison_integral a ha D hD hnear hfar _ _ hr hrR
  refine ⟨hi.congr heq.symm,?_⟩
  calc
    _ = ∫ t, ‖sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        profileKernelDifference a (2*topLength/(2:ℝ)^N) (2*topLength) t‖ :=
      integral_congr_ae (heq.mono fun _ h => congrArg norm h)
    _ ≤ _ := hbound

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ReflectedBandProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Negative vertical bands are conjugates of positive vertical bands. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_conj (epsilon R t : ℝ) :
    conj (sharpTimeKernel epsilon R t)=sharpTimeKernel epsilon R t := by
  unfold sharpTimeKernel
  split_ifs <;> simp

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

theorem lineConvolution_sub_of_bounded (K f g : ℝ → ℂ)
    (hK : Integrable K) (hfm : Measurable f) (hgm : Measurable g)
    (Bf Bg : ℝ) (hf : ∀ x, ‖f x‖≤Bf) (hg : ∀ x, ‖g x‖≤Bg) :
    lineConvolution K (f-g)=lineConvolution K f-lineConvolution K g := by
  funext x
  unfold lineConvolution
  simp only [Pi.sub_apply,mul_sub]
  exact integral_sub (lineConvolution_integrand_of_bounded K f hK hfm Bf hf x)
    (lineConvolution_integrand_of_bounded K g hK hgm Bg hg x)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineConvolutionFourth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fourth-power Young bound for an integrable line kernel and a
Schwartz input, with its exact L1 kernel constant. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_fourth_joint_integrable (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : SchwartzMap ℝ ℂ) :
    Integrable (fun p : ℝ×ℝ => ‖K p.1‖*‖f (p.2-p.1)‖^4) (volume.prod volume) := by
  have hm : Measurable (fun p : ℝ×ℝ => ‖K p.1‖*‖f (p.2-p.1)‖^4) := by fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun t =>
      ((lineTranslation_measurePreserving t).integrable_comp_of_integrable
        ((f.memLp 4 volume).integrable_norm_pow (by decide))).const_mul ‖K t‖
  · have heq (t : ℝ) : (∫ z, ‖‖K t‖*‖f (z-t)‖^4‖)=‖K t‖*(∫ z, ‖f z‖^4) := by
      simp only [norm_mul,Real.norm_of_nonneg (norm_nonneg (K t)),
        norm_pow,norm_norm]
      rw [integral_const_mul,integral_sub_right_eq_self (fun z => ‖f z‖^4) t]
    simp_rw [heq]
    exact hK.norm.mul_const _

theorem lineConvolution_fourth_pointwise (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖lineConvolution K f x‖^4≤(∫ t, ‖K t‖)^3*(∫ t, ‖K t‖*‖f (x-t)‖^4) := by
  have hi (n : ℕ) : Integrable (fun t => ‖K t‖*‖f (x-t)‖^n) := by
    apply (hK.norm.mul_const ((SchwartzMap.seminorm ℝ 0 0 f)^n)).mono'
      (by fun_prop)
    filter_upwards [] with t
    rw [Real.norm_of_nonneg (by positivity : 0≤‖K t‖*‖f (x-t)‖^n)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (SchwartzMap.norm_le_seminorm ℝ f (x-t)) n)
      (norm_nonneg _)
  have hfirst := lineConvolution_pointwise_energy K hK hKm f f.continuous.measurable x (hi 2)
  have hfourth : Integrable (fun t => ‖K t‖*(‖f (x-t)‖^2)^2) := by
    simpa only [←pow_mul] using hi 4
  have hsecond := (weighted_integral_cauchySchwarz volume (fun t => ‖K t‖)
    (fun t => ‖f (x-t)‖^2) hKm.norm (by fun_prop) (fun _ => norm_nonneg _)
    (fun _ => sq_nonneg _) hK.norm hfourth).2
  have hs := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
  calc
    ‖lineConvolution K f x‖^4 = (‖lineConvolution K f x‖^2)^2 := by ring
    _ ≤ ((∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (x-t)‖^2))^2 := hs
    _ = (∫ t, ‖K t‖)^2*(∫ t, ‖K t‖*‖f (x-t)‖^2)^2 := mul_pow _ _ _
    _ ≤ (∫ t, ‖K t‖)^2*((∫ t, ‖K t‖)*(∫ t, ‖K t‖*(‖f (x-t)‖^2)^2)) :=
      mul_le_mul_of_nonneg_left hsecond (sq_nonneg _)
    _ = _ := by simp only [←pow_mul]; ring

theorem lineConvolution_fourth_bound (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : SchwartzMap ℝ ℂ) :
    Integrable (fun x => ‖lineConvolution K f x‖^4) ∧
      (∫ x, ‖lineConvolution K f x‖^4)≤(∫ t, ‖K t‖)^4*(∫ x, ‖f x‖^4) := by
  have hj := lineConvolution_fourth_joint_integrable K hK hKm f
  have hm := lineConvolution_measurable K hKm f f.continuous.measurable
  have hd : Integrable (fun x => (∫ t, ‖K t‖)^3*(∫ t, ‖K t‖*‖f (x-t)‖^4)) :=
    hj.integral_prod_right.const_mul _
  have hi : Integrable (fun x => ‖lineConvolution K f x‖^4) := by
    apply hd.mono' (by fun_prop)
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (by positivity : 0≤‖lineConvolution K f x‖^4)]
    exact lineConvolution_fourth_pointwise K hK hKm f x
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ x, (∫ t, ‖K t‖)^3*(∫ t, ‖K t‖*‖f (x-t)‖^4) :=
      integral_mono hi hd (lineConvolution_fourth_pointwise K hK hKm f)
    _ = _ := by
      rw [integral_const_mul]
      rw [integral_integral_swap (f:=fun (x t : ℝ) => ‖K t‖*‖f (x-t)‖^4) hj.swap]
      simp_rw [integral_const_mul,integral_sub_right_eq_self (fun x => ‖f x‖^4)]
      rw [integral_mul_const]
      ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineConvolutionL4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The line convolution fourth-power estimate for measurable L4 inputs. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem memLp_fourth_iff (f : ℝ → ℂ) (hfm : AEStronglyMeasurable f volume) :
    MemLp f 4 volume ↔ Integrable (fun x => ‖f x‖^4) := by
  simpa using (integrable_norm_rpow_iff (p:=4) hfm (by norm_num) (by norm_num)).symm

theorem memLp_toL4_norm_pow (f : ℝ → ℂ) (hf : MemLp f 4 volume) :
    ‖hf.toLp f‖^4=∫ x, ‖f x‖^4 := by
  rw [Lp.norm_toLp,toReal_eLpNorm hf.aestronglyMeasurable,lpNorm_eq_integral_norm_rpow_toReal
    (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  rw [←Real.rpow_natCast,←Real.rpow_mul (integral_nonneg fun _ => by positivity)]
  norm_num

theorem lineConvolution_fourth_joint (K f : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (hfm : Measurable f) (hf : MemLp f 4 volume) :
    Integrable (fun p : ℝ×ℝ => ‖K p.1‖*‖f (p.2-p.1)‖^4) (volume.prod volume) := by
  have hm : Measurable (fun p : ℝ×ℝ => ‖K p.1‖*‖f (p.2-p.1)‖^4) := by fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun t =>
      ((lineTranslation_measurePreserving t).integrable_comp_of_integrable
        (hf.integrable_norm_pow (by decide : 4≠0))).const_mul ‖K t‖
  · have heq (t : ℝ) : (∫ z, ‖‖K t‖*‖f (z-t)‖^4‖)=‖K t‖*(∫ z, ‖f z‖^4) := by
      simp only [norm_mul,Real.norm_of_nonneg (norm_nonneg (K t)),norm_pow,norm_norm]
      rw [integral_const_mul,integral_sub_right_eq_self (fun z => ‖f z‖^4) t]
    simp_rw [heq]
    exact hK.norm.mul_const _

theorem lineConvolution_fourth_at (K f : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (hfm : Measurable f) (x : ℝ)
    (hi : Integrable (fun t => ‖K t‖*‖f (x-t)‖^4)) :
    ‖lineConvolution K f x‖^4≤(∫ t, ‖K t‖)^3*(∫ t, ‖K t‖*‖f (x-t)‖^4) := by
  have hfourth : Integrable (fun t => ‖K t‖*(‖f (x-t)‖^2)^2) := by
    simpa only [←pow_mul] using hi
  have hsecond := weighted_integral_cauchySchwarz volume (fun t => ‖K t‖)
    (fun t => ‖f (x-t)‖^2) hKm.norm (by fun_prop) (fun _ => norm_nonneg _)
    (fun _ => sq_nonneg _) hK.norm hfourth
  have hfirst := lineConvolution_pointwise_energy K hK hKm f hfm x hsecond.1
  have hs := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
  calc
    ‖lineConvolution K f x‖^4 = (‖lineConvolution K f x‖^2)^2 := by ring
    _ ≤ ((∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (x-t)‖^2))^2 := hs
    _ = (∫ t, ‖K t‖)^2*(∫ t, ‖K t‖*‖f (x-t)‖^2)^2 := mul_pow _ _ _
    _ ≤ (∫ t, ‖K t‖)^2*((∫ t, ‖K t‖)*(∫ t, ‖K t‖*(‖f (x-t)‖^2)^2)) :=
      mul_le_mul_of_nonneg_left hsecond.2 (sq_nonneg _)
    _ = _ := by simp only [←pow_mul]; ring

theorem lineConvolution_L4_bound (K f : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (hfm : Measurable f) (hf : MemLp f 4 volume) :
    MemLp (lineConvolution K f) 4 volume ∧
      (∫ x, ‖lineConvolution K f x‖^4)≤(∫ t, ‖K t‖)^4*(∫ x, ‖f x‖^4) := by
  have hj := lineConvolution_fourth_joint K f hK hKm hfm hf
  have hm := lineConvolution_measurable K hKm f hfm
  have hd : Integrable (fun x => (∫ t, ‖K t‖)^3*(∫ t, ‖K t‖*‖f (x-t)‖^4)) :=
    hj.integral_prod_right.const_mul _
  have hp : ∀ᵐ x ∂volume, ‖lineConvolution K f x‖^4≤
      (∫ t, ‖K t‖)^3*(∫ t, ‖K t‖*‖f (x-t)‖^4) := by
    filter_upwards [hj.prod_left_ae] with x hx
    exact lineConvolution_fourth_at K f hK hKm hfm x hx
  have hi : Integrable (fun x => ‖lineConvolution K f x‖^4) := by
    apply hd.mono' (by fun_prop)
    filter_upwards [hp] with x hx
    rwa [Real.norm_of_nonneg (by positivity : 0≤‖lineConvolution K f x‖^4)]
  refine ⟨(memLp_fourth_iff _ hm.aestronglyMeasurable).2 hi,?_⟩
  calc
    _ ≤ ∫ x, (∫ t, ‖K t‖)^3*(∫ t, ‖K t‖*‖f (x-t)‖^4) := integral_mono_ae hi hd hp
    _ = _ := by
      rw [integral_const_mul]
      rw [integral_integral_swap (f:=fun (x t : ℝ) => ‖K t‖*‖f (x-t)‖^4) hj.swap]
      simp_rw [integral_const_mul,integral_sub_right_eq_self (fun x => ‖f x‖^4)]
      rw [integral_mul_const]
      ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HalfPowerDualTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit dual test for exponent three-halves, with its second,
fourth and third moments. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem halfPowerDualTest_measurable (g : ℝ → ℂ) (hg : Measurable g) :
    Measurable (halfPowerDualTest g) := by unfold halfPowerDualTest; fun_prop

theorem halfPowerDualTest_norm (g : ℝ → ℂ) (x : ℝ) :
    ‖halfPowerDualTest g x‖=‖g x‖^(1/2:ℝ) := by
  by_cases hz : g x=0
  · simp [halfPowerDualTest,hz]
  have hp : 0<‖g x‖ := norm_pos_iff.mpr hz
  rw [halfPowerDualTest,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg hp.le _)]
  conv_lhs => rhs; rw [←Real.rpow_one ‖g x‖]
  rw [←Real.rpow_add hp]
  norm_num

theorem halfPowerDualTest_norm_sq (g : ℝ → ℂ) (x : ℝ) :
    ‖halfPowerDualTest g x‖^2=‖g x‖ := by
  rw [halfPowerDualTest_norm,←Real.rpow_natCast,←Real.rpow_mul (norm_nonneg _)]
  norm_num

theorem halfPowerDualTest_norm_fourth (g : ℝ → ℂ) (x : ℝ) :
    ‖halfPowerDualTest g x‖^4=‖g x‖^2 := by
  rw [show (4:ℕ)=2*2 by decide,pow_mul,halfPowerDualTest_norm_sq]

theorem halfPowerDualTest_norm_cube (g : ℝ → ℂ) (x : ℝ) :
    ‖halfPowerDualTest g x‖^3=‖g x‖^(3/2:ℝ) := by
  rw [halfPowerDualTest_norm,←Real.rpow_natCast,←Real.rpow_mul (norm_nonneg _)]
  norm_num

theorem halfPowerDualTest_pair (g : ℝ → ℂ) (x : ℝ) :
    g x*conj (halfPowerDualTest g x)=((‖g x‖^(3/2:ℝ):ℝ):ℂ) := by
  by_cases hz : g x=0
  · simp [halfPowerDualTest,hz]
  have hp : 0<‖g x‖ := norm_pos_iff.mpr hz
  simp only [halfPowerDualTest,map_mul,Complex.conj_ofReal]
  calc
    _ = ((‖g x‖^(-(1/2):ℝ):ℝ):ℂ)*(g x*conj (g x)) := by ring
    _ = ((‖g x‖^(-(1/2):ℝ):ℝ):ℂ)*(‖g x‖:ℂ)^2 := by rw [Complex.mul_conj']
    _ = ((‖g x‖^(3/2:ℝ):ℝ):ℂ) := by
      rw [←Complex.ofReal_pow,←Complex.ofReal_mul,←Real.rpow_natCast,←Real.rpow_add hp]
      norm_num

theorem halfPowerDualTest_memLp (g : ℝ → ℂ) (hgm : Measurable g)
    (hg1 : Integrable g) (hg2 : MemLp g 2 volume) :
    MemLp (halfPowerDualTest g) 2 volume ∧ MemLp (halfPowerDualTest g) 4 volume := by
  have hm := halfPowerDualTest_measurable g hgm
  constructor
  · apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
    simpa only [halfPowerDualTest_norm_sq] using hg1.norm
  · apply (memLp_fourth_iff _ hm.aestronglyMeasurable).2
    simpa only [halfPowerDualTest_norm_fourth] using hg2.integrable_norm_pow (by decide : 2≠0)

theorem halfPowerDualTest_bound (g : ℝ → ℂ) (B : ℝ) (hB : ∀ x, ‖g x‖≤B) :
    ∀ x, ‖halfPowerDualTest g x‖≤B+1 := by
  have hBp : 0≤B := (norm_nonneg _).trans (hB 0)
  intro x
  have hs : ‖halfPowerDualTest g x‖^2≤B := by rw [halfPowerDualTest_norm_sq]; exact hB x
  nlinarith [norm_nonneg (halfPowerDualTest g x),sq_nonneg B]

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

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HardyPairL4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An elementary fourth-power bound for the difference of positive and
negative frequency Schwartz functions. The proof uses only Plancherel,
frequency support of products, and a scalar quadratic inequality. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProduct_positive (a b : SchwartzMap ℝ ℂ)
    (ha : ∀ eta, eta≤0 → (𝓕 a : SchwartzMap ℝ ℂ) eta=0)
    (hb : ∀ eta, eta≤0 → (𝓕 b : SchwartzMap ℝ ℂ) eta=0) :
    ∀ eta, eta≤0 → (𝓕 (lineSchwartzProduct a b) : SchwartzMap ℝ ℂ) eta=0 := by
  intro eta he
  apply lineSchwartzProduct_fourier_zero
  intro t
  by_cases ht : t≤0
  · exact Or.inl (ha t ht)
  · exact Or.inr (hb (eta-t) (by linarith))

theorem lineSchwartzProduct_negative (a b : SchwartzMap ℝ ℂ)
    (ha : ∀ eta, 0≤eta → (𝓕 a : SchwartzMap ℝ ℂ) eta=0)
    (hb : ∀ eta, 0≤eta → (𝓕 b : SchwartzMap ℝ ℂ) eta=0) :
    ∀ eta, 0≤eta → (𝓕 (lineSchwartzProduct a b) : SchwartzMap ℝ ℂ) eta=0 := by
  intro eta he
  apply lineSchwartzProduct_fourier_zero
  intro t
  by_cases ht : 0≤t
  · exact Or.inl (ha t ht)
  · exact Or.inr (hb (eta-t) (by linarith))

theorem schwartz_disjoint_energy_add_sub (a b : SchwartzMap ℝ ℂ)
    (h : ∀ eta, (𝓕 a : SchwartzMap ℝ ℂ) eta=0 ∨ (𝓕 b : SchwartzMap ℝ ℂ) eta=0) :
    (∫ x, ‖(a+b) x‖^2)=(∫ x, ‖(a-b) x‖^2) := by
  rw [←SchwartzMap.integral_norm_sq_fourier (a+b),
    ←SchwartzMap.integral_norm_sq_fourier (a-b)]
  apply integral_congr_ae
  filter_upwards [] with eta
  simp only [sub_eq_add_neg,FourierTransform.fourier_add,FourierTransform.fourier_neg,
    add_apply,neg_apply]
  rcases h eta with ha | hb
  · rw [ha,zero_add,zero_add,norm_neg]
  · rw [hb,add_zero,neg_zero,add_zero]

theorem hardyPair_fourth_power (a b : SchwartzMap ℝ ℂ)
    (ha : ∀ eta, eta≤0 → (𝓕 a : SchwartzMap ℝ ℂ) eta=0)
    (hb : ∀ eta, 0≤eta → (𝓕 b : SchwartzMap ℝ ℂ) eta=0) :
    (∫ x, ‖(a-b) x‖^4)≤68*(∫ x, ‖(a+b) x‖^4) := by
  let f := a+b
  let g := a-b
  let H := lineSchwartzProduct a a+lineSchwartzProduct b b
  let Q := lineSchwartzProduct a a-lineSchwartzProduct b b
  have horth : (∫ x, ‖H x‖^2)=(∫ x, ‖Q x‖^2) := by
    apply schwartz_disjoint_energy_add_sub
    intro eta
    by_cases he : eta≤0
    · exact Or.inl (lineSchwartzProduct_positive a a ha ha eta he)
    · exact Or.inr (lineSchwartzProduct_negative b b hb hb eta (by linarith))
  have hidentity (x : ℝ) : g x*g x=2*H x-f x*f x := by
    simp only [f,g,H,add_apply,sub_apply,lineSchwartzProduct_apply]
    ring
  have hQ (x : ℝ) : Q x=f x*g x := by
    simp only [Q,f,g,add_apply,sub_apply,lineSchwartzProduct_apply]
    ring
  have hpoint (x : ℝ) : ‖g x‖^4≤8*‖H x‖^2+2*‖f x‖^4 := by
    have hn := norm_sub_le (2*H x) (f x*f x)
    rw [←hidentity,norm_mul,norm_mul,norm_mul] at hn
    norm_num at hn
    have hs := sq_nonneg (2*‖H x‖-‖f x‖^2)
    nlinarith [sq_nonneg (‖g x‖^2-(2*‖H x‖+‖f x‖^2))]
  have hQpoint (x : ℝ) : ‖Q x‖^2≤(1/16:ℝ)*‖g x‖^4+4*‖f x‖^4 := by
    rw [hQ,norm_mul,mul_pow]
    nlinarith [sq_nonneg (‖g x‖^2/4-2*‖f x‖^2)]
  have hf : Integrable (fun x => ‖f x‖^4) :=
    (f.memLp 4 volume).integrable_norm_pow (by decide)
  have hg : Integrable (fun x => ‖g x‖^4) :=
    (g.memLp 4 volume).integrable_norm_pow (by decide)
  have hH : Integrable (fun x => ‖H x‖^2) :=
    (H.memLp 2 volume).integrable_norm_pow (by decide)
  have hQi : Integrable (fun x => ‖Q x‖^2) :=
    (Q.memLp 2 volume).integrable_norm_pow (by decide)
  have hi := integral_mono hg ((hH.const_mul 8).add (hf.const_mul 2)) hpoint
  have hqi := integral_mono hQi ((hg.const_mul (1/16)).add (hf.const_mul 4)) hQpoint
  simp only [Pi.add_apply] at hi hqi
  rw [integral_add (hH.const_mul 8) (hf.const_mul 2),integral_const_mul,integral_const_mul,
    horth] at hi
  rw [integral_add (hg.const_mul (1/16)) (hf.const_mul 4),integral_const_mul,
    integral_const_mul] at hqi
  change (∫ x, ‖g x‖^4)≤68*(∫ x, ‖f x‖^4)
  linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_HilbertCutoffProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed smooth annular Hilbert multiplier and its cutoff derivative.
All profiles are constructed, rather than supplied as analytic inputs. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertSmoothSign_pos (x : ℝ) (hx : 1/2≤x) : hilbertSmoothSign x=1 := by
  simp [hilbertSmoothSign,Real.smoothTransition.one_of_one_le (show 1≤2*x+1 by linarith),
    Real.smoothTransition.zero_of_nonpos (show 1-2*x≤0 by linarith)]

theorem hilbertSmoothSign_neg (x : ℝ) (hx : x≤-(1/2)) : hilbertSmoothSign x= -1 := by
  simp [hilbertSmoothSign,Real.smoothTransition.zero_of_nonpos (show 2*x+1≤0 by linarith),
    Real.smoothTransition.one_of_one_le (show 1≤1-2*x by linarith)]

theorem hilbertSmoothSign_range (x : ℝ) : -1≤hilbertSmoothSign x ∧ hilbertSmoothSign x≤1 := by
  unfold hilbertSmoothSign
  constructor <;> linarith [Real.smoothTransition.nonneg (2*x+1),
    Real.smoothTransition.le_one (2*x+1),Real.smoothTransition.nonneg (1-2*x),
    Real.smoothTransition.le_one (1-2*x)]

theorem hilbertSmoothSign_deriv_zero (x : ℝ) (hx : 1/2≤|x|) :
    deriv hilbertSmoothSign x=0 := by
  rcases le_abs.mp hx with hx | hx
  · apply IsLocalMax.deriv_eq_zero
    apply Filter.Eventually.of_forall
    intro y
    rw [hilbertSmoothSign_pos x hx]
    exact (hilbertSmoothSign_range y).2
  · apply IsLocalMin.deriv_eq_zero
    apply Filter.Eventually.of_forall
    intro y
    rw [hilbertSmoothSign_neg x (by linarith)]
    exact (hilbertSmoothSign_range y).1

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_HilbertCutoffDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiating the actual annular multiplier gives a dyadic difference
of a single compactly supported smooth profile. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertSign_deriv_plateau (x : ℝ) : deriv hilbertSmoothSign x*
    (verticalBinPlateauReal x-verticalBinPlateauReal (2*x))=0 := by
  by_cases hx : |x|≤1/2
  · have hx1 : |x|≤1 := by linarith
    have hx2 : |2*x|≤1 := by rw [abs_mul]; norm_num; linarith
    rw [verticalBinPlateauReal_one x hx1,verticalBinPlateauReal_one (2*x) hx2]
    ring
  · rw [hilbertSmoothSign_deriv_zero x (le_of_lt (lt_of_not_ge hx)),zero_mul]

theorem hilbertSign_dilation_deriv (x : ℝ) :
    hilbertSmoothSign x*deriv verticalBinPlateauReal (2*x)=
      hilbertSmoothSign (2*x)*deriv verticalBinPlateauReal (2*x) := by
  by_cases hx : |x|≤1/2
  · have hx2 : |2*x|≤1 := by rw [abs_mul]; norm_num; linarith
    rw [verticalBinPlateauReal_deriv_zero (2*x) (Or.inl hx2)]
    ring
  · have hxabs : 1/2≤|x| := le_of_lt (lt_of_not_ge hx)
    rcases le_abs.mp hxabs with hp | hn
    · rw [hilbertSmoothSign_pos x hp,hilbertSmoothSign_pos (2*x) (by linarith)]
    · rw [hilbertSmoothSign_neg x (by linarith),hilbertSmoothSign_neg (2*x) (by linarith)]

theorem hilbertAnnularSymbol_hasDerivAt (x : ℝ) :
    HasDerivAt hilbertAnnularSymbol
      (-(Real.pi:ℂ)*Complex.I*(hilbertCutoffDerivative x-2*hilbertCutoffDerivative (2*x))) x := by
  have hs := ((contDiff_infty_iff_deriv.mp hilbertSmoothSign_smooth).1 x).hasDerivAt
  have hc (s : ℝ) := ((contDiff_infty_iff_deriv.mp verticalBinPlateauReal_smooth).1 s).hasDerivAt
  have hc2 := (hc (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hd := (hs.mul ((hc x).sub hc2)).ofReal_comp.const_mul (-(Real.pi:ℂ)*Complex.I)
  refine hd.congr_deriv ?_
  · symm
    change -(Real.pi:ℂ)*Complex.I*
      (↑(hilbertSmoothSign x*deriv verticalBinPlateauReal x)-
        2*↑(hilbertSmoothSign (2*x)*deriv verticalBinPlateauReal (2*x))) = _
    simp only [Pi.sub_apply,Function.comp_apply]
    rw [hilbertSign_deriv_plateau,zero_add]
    have heq : hilbertSmoothSign x*(deriv verticalBinPlateauReal x-
        deriv verticalBinPlateauReal (2*x)*(2*1))=
        hilbertSmoothSign x*deriv verticalBinPlateauReal x-
          2*(hilbertSmoothSign (2*x)*deriv verticalBinPlateauReal (2*x)) := by
      rw [←hilbertSign_dilation_deriv]
      ring
    rw [heq]
    push_cast
    ring

theorem hilbertAnnularSymbol_deriv (x : ℝ) :
    deriv hilbertAnnularSymbol x=
      -(Real.pi:ℂ)*Complex.I*(hilbertCutoffDerivative x-2*hilbertCutoffDerivative (2*x)) :=
  (hilbertAnnularSymbol_hasDerivAt x).deriv

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_HilbertCutoffNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact derivative profile has integral minus two, fixing the
normalization of the physical telescoping profile at the origin. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertCutoffDerivative_nonneg_arg (x : ℝ) (hx : 0≤x) :
    hilbertCutoffDerivative x=((deriv verticalBinPlateauReal x : ℝ) : ℂ) := by
  change ((hilbertSmoothSign x*deriv verticalBinPlateauReal x : ℝ) : ℂ)=_
  by_cases h : 1/2≤x
  · rw [hilbertSmoothSign_pos x h,one_mul]
  · have ha : |x|≤1 := by rw [abs_of_nonneg hx]; linarith
    rw [verticalBinPlateauReal_deriv_zero x (Or.inl ha),mul_zero,Complex.ofReal_zero]

theorem hilbertCutoffDerivative_nonpos_arg (x : ℝ) (hx : x≤0) :
    hilbertCutoffDerivative x= -((deriv verticalBinPlateauReal x : ℝ) : ℂ) := by
  change ((hilbertSmoothSign x*deriv verticalBinPlateauReal x : ℝ) : ℂ)=_
  by_cases h : x≤-(1/2)
  · rw [hilbertSmoothSign_neg x h,neg_one_mul,Complex.ofReal_neg]
  · have ha : |x|≤1 := by rw [abs_of_nonpos hx]; linarith
    rw [verticalBinPlateauReal_deriv_zero x (Or.inl ha),mul_zero,Complex.ofReal_zero,neg_zero]

theorem hilbertCutoffDerivative_integral : (∫ x, hilbertCutoffDerivative x)=(-2:ℂ) := by
  have hc : Continuous (fun x => ((deriv verticalBinPlateauReal x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (contDiff_infty_iff_deriv.mp verticalBinPlateauReal_smooth).2.continuous
  have hd (x : ℝ) : HasDerivAt verticalBinPlateau ((deriv verticalBinPlateauReal x : ℝ) : ℂ) x := by
    exact ((contDiff_infty_iff_deriv.mp verticalBinPlateauReal_smooth).1 x).hasDerivAt.ofReal_comp
  have hpos : (∫ x in (0:ℝ)..3, hilbertCutoffDerivative x)=(-1:ℂ) := by
    calc
      _ = ∫ x in (0:ℝ)..3, ((deriv verticalBinPlateauReal x : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num : (0:ℝ)≤3)] at hx
        exact hilbertCutoffDerivative_nonneg_arg x hx.1
      _ = verticalBinPlateau 3-verticalBinPlateau 0 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable _ _)
      _ = -1 := by
        have h3 : verticalBinPlateau (3:ℝ)=0 := by
          change (verticalBinPlateauReal 3:ℂ)=0
          rw [verticalBinPlateauReal_zero 3 (Or.inr (by norm_num)),Complex.ofReal_zero]
        rw [h3,verticalBinPlateau_one 0 (by norm_num),zero_sub]
  have hneg : (∫ x in (-3:ℝ)..0, hilbertCutoffDerivative x)=(-1:ℂ) := by
    calc
      _ = ∫ x in (-3:ℝ)..0, -((deriv verticalBinPlateauReal x : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num : (-3:ℝ)≤0)] at hx
        exact hilbertCutoffDerivative_nonpos_arg x hx.2
      _ = -(verticalBinPlateau 0-verticalBinPlateau (-3)) := by
        rw [intervalIntegral.integral_neg]
        congr 1
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable _ _)
      _ = -1 := by
        have h3 : verticalBinPlateau (-3:ℝ)=0 := by
          change (verticalBinPlateauReal (-3):ℂ)=0
          rw [verticalBinPlateauReal_zero (-3) (Or.inl (by norm_num)),Complex.ofReal_zero]
        rw [h3,verticalBinPlateau_one 0 (by norm_num),sub_zero]
  have hsupport : Function.support hilbertCutoffDerivative ⊆ Ioc (-3:ℝ) 3 := by
    intro x hx
    have ha : |x|<2 := by
      by_contra hn
      have hz := verticalBinPlateauReal_deriv_zero x (Or.inr (le_of_not_gt hn))
      apply hx
      change ((hilbertSmoothSign x*deriv verticalBinPlateauReal x : ℝ) : ℂ)=0
      rw [hz,mul_zero,Complex.ofReal_zero]
    have hb := abs_lt.mp ha
    constructor <;> linarith
  rw [←intervalIntegral.integral_eq_integral_of_support_subset hsupport,
    ←intervalIntegral.integral_add_adjacent_intervals
      (hilbertCutoffDerivative.continuous.intervalIntegrable (-3) 0)
      (hilbertCutoffDerivative.continuous.intervalIntegrable 0 3),hneg,hpos]
  norm_num

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SchwartzProfileBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The endpoint assumptions in the sharp truncation comparison follow
from Schwartz regularity and the single normalization value at zero. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem schwartzProfile_bounds (a : SchwartzMap ℝ ℂ) (ha : a 0= -1) :
    ∃ D : ℝ, 0≤D ∧ (∀ s, ‖a s+1‖≤D*|s|) ∧ (∀ s, |s| *‖a s‖≤D) := by
  let D := SchwartzMap.seminorm ℝ 0 1 a+SchwartzMap.seminorm ℝ 1 0 a
  have h0 : 0≤SchwartzMap.seminorm ℝ 0 1 a := apply_nonneg _ _
  have h1 : 0≤SchwartzMap.seminorm ℝ 1 0 a := apply_nonneg _ _
  have hd (x : ℝ) : ‖deriv a x‖≤SchwartzMap.seminorm ℝ 0 1 a := by
    simpa only [pow_zero,one_mul,iteratedDeriv_one] using a.le_seminorm' ℝ 0 1 x
  refine ⟨D,add_nonneg h0 h1,?_,?_⟩
  · intro s
    have h := convex_univ.norm_image_sub_le_of_norm_deriv_le
      (fun x (_ : x∈(Set.univ : Set ℝ)) => a.differentiableAt)
      (fun x (_ : x∈(Set.univ : Set ℝ)) => hd x) (Set.mem_univ (0:ℝ)) (Set.mem_univ s)
    rw [ha,sub_neg_eq_add,sub_zero,Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right h1) (abs_nonneg s))
  · intro s
    have h := a.norm_pow_mul_le_seminorm ℝ 1 s
    simp only [pow_one,Real.norm_eq_abs] at h
    exact h.trans (le_add_of_nonneg_left h0)

theorem schwartzFiniteTimeKernel_sharp_integral (k a : SchwartzMap ℝ ℂ)
    (ha : a 0= -1) (hprofile : ∀ s : ℝ, (s : ℂ)*k s=a s-a (s/2)) :
    ∃ B : ℝ, 0≤B ∧ ∀ (N : ℕ) (topLength : ℝ), 0<topLength →
      Integrable (fun t => sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        finiteTimeKernel k N topLength t) ∧
      (∫ t, ‖sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        finiteTimeKernel k N topLength t‖)≤B := by
  obtain ⟨D,hD,hnear,hfar⟩ := schwartzProfile_bounds a ha
  refine ⟨8*Real.pi*D,by positivity,?_⟩
  intro N topLength htop
  exact finiteTimeKernel_sharp_integral k a a.continuous.measurable hprofile
    D hD hnear hfar N topLength htop

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HilbertTimeProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual annular inverse Fourier kernel telescopes to a normalized
Schwartz profile. This gives a uniform sharp truncation comparison. -/
noncomputable section
open MeasureTheory FourierTransform LineDeriv
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertTimeProfile_zero : hilbertTimeProfile 0= -1 := by
  change (1/2:ℂ)*(𝓕⁻ hilbertCutoffDerivative : SchwartzMap ℝ ℂ) 0= -1
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq]
  simp only [inner_zero_right,Real.fourierChar.map_zero_eq_one,one_smul]
  rw [hilbertCutoffDerivative_integral]
  norm_num

theorem schwartzDilation_fourierInv (f : SchwartzMap ℝ ℂ) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    (𝓕⁻ (schwartzDilation f r hr.ne') : SchwartzMap ℝ ℂ) t=
      (r⁻¹:ℂ)*(𝓕⁻ f : SchwartzMap ℝ ℂ) (t/r) := by
  simp only [SchwartzMap.fourierInv_coe,Real.fourierInv_eq_fourier_neg]
  rw [←SchwartzMap.fourier_coe,schwartzDilation_fourier]
  rw [abs_of_pos (inv_pos.mpr hr),Complex.real_smul,neg_div]
  simp only [Complex.ofReal_inv,SchwartzMap.fourier_coe]

theorem schwartz_fourierInv_deriv (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    (𝓕⁻ (SchwartzMap.derivCLM ℂ ℂ f) : SchwartzMap ℝ ℂ) t=
      -(2*Real.pi*Complex.I)*(t:ℂ)*(𝓕⁻ f : SchwartzMap ℝ ℂ) t := by
  have heq : SchwartzMap.derivCLM ℂ ℂ f=∂_{(1:ℝ)} f := by
    ext x
    rw [SchwartzMap.derivCLM_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv,
      fderiv_apply_one_eq_deriv]
  rw [heq,SchwartzMap.fourierInv_lineDerivOp_eq]
  simp only [smul_apply,Real.inner_apply,mul_one,smul_eq_mul]
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (show (fun x : ℝ => x).HasTemperateGrowth from by fun_prop)]
  simp only [Complex.real_smul]
  ring

theorem hilbertTimeKernel_profile (t : ℝ) :
    (t:ℂ)*hilbertTimeKernel t=hilbertTimeProfile t-hilbertTimeProfile (t/2) := by
  have hd : SchwartzMap.derivCLM ℂ ℂ hilbertAnnularSymbol=
      (-(Real.pi:ℂ)*Complex.I) • (hilbertCutoffDerivative-
        (2:ℂ) • schwartzDilation hilbertCutoffDerivative 2 (by norm_num)) := by
    ext x
    simp only [SchwartzMap.derivCLM_apply,smul_apply,sub_apply,smul_eq_mul,
      schwartzDilation_apply]
    exact hilbertAnnularSymbol_deriv x
  have h := schwartz_fourierInv_deriv hilbertAnnularSymbol t
  rw [hd] at h
  simp only [sub_eq_add_neg,fourierInv_add,fourierInv_neg,fourierInv_smul,
    smul_apply,add_apply,neg_apply,smul_eq_mul] at h
  rw [schwartzDilation_fourierInv hilbertCutoffDerivative 2 (by norm_num) t] at h
  change (t:ℂ)*(𝓕⁻ hilbertAnnularSymbol : SchwartzMap ℝ ℂ) t=
    (1/2:ℂ)*(𝓕⁻ hilbertCutoffDerivative : SchwartzMap ℝ ℂ) t-
      (1/2:ℂ)*(𝓕⁻ hilbertCutoffDerivative : SchwartzMap ℝ ℂ) (t/2)
  have hp : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  apply (mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (by norm_num : (-2:ℂ)≠0) hp) Complex.I_ne_zero))
  calc
    _ = -(2*Real.pi*Complex.I)*(t:ℂ)*(𝓕⁻ hilbertAnnularSymbol : SchwartzMap ℝ ℂ) t := by ring
    _ = _ := h.symm
    _ = _ := by push_cast; ring

theorem hilbertTimeKernel_sharp_integral :
    ∃ B : ℝ, 0≤B ∧ ∀ (N : ℕ) (topLength : ℝ), 0<topLength →
      Integrable (fun t => sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        finiteTimeKernel hilbertTimeKernel N topLength t) ∧
      (∫ t, ‖sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        finiteTimeKernel hilbertTimeKernel N topLength t‖)≤B :=
  schwartzFiniteTimeKernel_sharp_integral hilbertTimeKernel hilbertTimeProfile
    hilbertTimeProfile_zero hilbertTimeKernel_profile

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TimeEndpointComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A factor-two change of the inner time endpoint costs a fixed L1
constant. Every positive inner endpoint has such a dyadic representative. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_close_lower (r s R t : ℝ) (hr : 0 < r)
    (hrs : r ≤ s) (hsr : s≤2*r) :
    ‖sharpTimeKernel r R t-sharpTimeKernel s R t‖≤3*timeErrorEnvelope r t := by
  have hq := timeErrorEnvelope_nonneg r t hr
  by_cases hs : s< |t|
  · have hr' : r< |t| := hrs.trans_lt hs
    simp only [sharpTimeKernel,hr',hs,true_and,sub_self,norm_zero]
    positivity
  · by_cases hr' : r< |t|
    · by_cases hR : |t|<R
      · have ht : 0< |t| := hr.trans hr'
        have ht2 : |t|≤2*r := (le_of_not_gt hs).trans hsr
        have hd : 0 < r^2+t^2 := by positivity
        have hpoly : r^2+t^2≤3*r*|t| := by
          nlinarith [sq_abs t,mul_nonneg (sub_nonneg.mpr hr'.le) (sub_nonneg.mpr ht2)]
        have hcond1 : r< |t| ∧ |t|<R := ⟨hr',hR⟩
        have hcond2 : ¬(s< |t| ∧ |t|<R) := fun h => hs h.1
        simp only [sharpTimeKernel,ite_eq_left hcond1,ite_eq_right hcond2,sub_zero,
          norm_inv,Complex.norm_real,Real.norm_eq_abs,timeErrorEnvelope]
        rw [←mul_div_assoc,inv_eq_one_div]
        apply (div_le_div_iff₀ ht hd).2
        nlinarith only [hpoly]
      · have hcond1 : ¬(r< |t| ∧ |t|<R) := fun h => hR h.2
        have hcond2 : ¬(s< |t| ∧ |t|<R) := fun h => hR h.2
        simp only [sharpTimeKernel,ite_eq_right hcond1,ite_eq_right hcond2,sub_self,norm_zero]
        positivity
    · have hcond1 : ¬(r< |t| ∧ |t|<R) := fun h => hr' h.1
      have hcond2 : ¬(s< |t| ∧ |t|<R) := fun h => hs h.1
      simp only [sharpTimeKernel,ite_eq_right hcond1,ite_eq_right hcond2,sub_self,norm_zero]
      positivity

theorem sharpTimeKernel_close_lower_integral (r s R : ℝ) (hr : 0 < r)
    (hrs : r ≤ s) (hsr : s≤2*r) :
    Integrable (fun t => sharpTimeKernel r R t-sharpTimeKernel s R t) ∧
      (∫ t, ‖sharpTimeKernel r R t-sharpTimeKernel s R t‖)≤3*Real.pi := by
  have hm := (sharpTimeKernel_measurable r R).sub (sharpTimeKernel_measurable s R)
  have hi := (timeErrorEnvelope_integrable r hr).const_mul 3
  have hb (t) := sharpTimeKernel_close_lower r s R t hr hrs hsr
  have he := hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine ⟨he,?_⟩
  calc
    _ ≤ ∫ t, 3*timeErrorEnvelope r t := integral_mono he.norm hi hb
    _ = 3*Real.pi := by rw [integral_const_mul,timeErrorEnvelope_integral r hr]

theorem exists_dyadic_time_endpoint (epsilon R : ℝ) (he : 0<epsilon) (heR : epsilon≤R) :
    ∃ N : ℕ, epsilon≤R/(2:ℝ)^N ∧ R/(2:ℝ)^N<2*epsilon := by
  have hR : 0<R := he.trans_le heR
  obtain ⟨N,hlo,hhi⟩ := exists_nat_pow_near ((le_div_iff₀ he).2 (by simpa using heR))
    (by norm_num : (1:ℝ)<2)
  refine ⟨N,?_,?_⟩
  · apply (le_div_iff₀ (pow_pos (by norm_num) N)).2
    simpa only [mul_comm] using (le_div_iff₀ he).1 hlo
  · apply (div_lt_iff₀ (pow_pos (by norm_num) N)).2
    have h := (div_lt_iff₀ he).1 hhi
    rw [pow_succ] at h
    nlinarith only [h]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HilbertArbitraryEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Hilbert decomposition applies to every positive inner
truncation, with a nearby dyadic endpoint and a uniform error. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertTimeKernel_arbitrary_endpoint :
    ∃ B : ℝ, 0≤B ∧ ∀ epsilon R : ℝ, 0<epsilon → epsilon≤R →
      ∃ N : ℕ, epsilon≤R/(2:ℝ)^N ∧ R/(2:ℝ)^N<2*epsilon ∧
        Integrable (fun t => sharpTimeKernel epsilon R t-
          finiteTimeKernel hilbertTimeKernel N (R/2) t) ∧
        (∫ t, ‖sharpTimeKernel epsilon R t-
          finiteTimeKernel hilbertTimeKernel N (R/2) t‖)≤B := by
  obtain ⟨B,hB,hkernel⟩ := hilbertTimeKernel_sharp_integral
  refine ⟨3*Real.pi+B,by positivity,?_⟩
  intro epsilon R he heR
  have hR : 0<R := he.trans_le heR
  obtain ⟨N,hlo,hhi⟩ := exists_dyadic_time_endpoint epsilon R he heR
  refine ⟨N,hlo,hhi,?_⟩
  have hc := sharpTimeKernel_close_lower_integral epsilon (R/(2:ℝ)^N) R he hlo hhi.le
  have hk := hkernel N (R/2) (by positivity)
  rw [show 2*(R/2)=R by ring] at hk
  let A := fun t => sharpTimeKernel epsilon R t-sharpTimeKernel (R/(2:ℝ)^N) R t
  let C := fun t => sharpTimeKernel (R/(2:ℝ)^N) R t-
    finiteTimeKernel hilbertTimeKernel N (R/2) t
  have hi : Integrable (fun t => sharpTimeKernel epsilon R t-
      finiteTimeKernel hilbertTimeKernel N (R/2) t) := by
    apply (hc.1.add hk.1).congr
    filter_upwards [] with t
    dsimp
    ring
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ t, ‖A t‖+‖C t‖ := by
      apply integral_mono hi.norm (hc.1.norm.add hk.1.norm)
      intro t
      have heq : sharpTimeKernel epsilon R t-finiteTimeKernel hilbertTimeKernel N (R/2) t=
          A t+C t := by dsimp [A,C]; ring
      change ‖sharpTimeKernel epsilon R t-finiteTimeKernel hilbertTimeKernel N (R/2) t‖≤
        ‖A t‖+‖C t‖
      rw [heq]
      exact norm_add_le _ _
    _ = (∫ t, ‖A t‖)+(∫ t, ‖C t‖) := integral_add hc.1.norm hk.1.norm
    _ ≤ 3*Real.pi+B := add_le_add hc.2 hk.2

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_HilbertFiniteSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth finite Hilbert multiplier has a uniform bound obtained
from an exact telescoping identity, independently of the scale count. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertFrequencySign_pos_mul (a x : ℝ) (ha : 0<a) :
    hilbertFrequencySign (a*x)=hilbertFrequencySign x := by
  unfold hilbertFrequencySign
  by_cases hx : 0≤x
  · rw [ite_eq_left hx,ite_eq_left (mul_nonneg ha.le hx)]
  · rw [ite_eq_right hx,ite_eq_right (not_le.mpr (mul_neg_of_pos_of_neg ha (lt_of_not_ge hx)))]

theorem hilbertAnnularSymbol_sign (x : ℝ) :
    hilbertAnnularSymbol x=-(Real.pi:ℂ)*Complex.I*
      (hilbertFrequencySign x*(verticalBinPlateau x-verticalBinPlateau (2*x))) := by
  change -(Real.pi:ℂ)*Complex.I*↑(hilbertSmoothSign x*
    (verticalBinPlateauReal x-verticalBinPlateauReal (2*x)))=_
  by_cases hs : |x|≤1/2
  · have h1 : |x|≤1 := by linarith
    have h2 : |2*x|≤1 := by rw [abs_mul]; norm_num; linarith
    rw [verticalBinPlateauReal_one x h1,verticalBinPlateauReal_one (2*x) h2,
      verticalBinPlateau_one x h1,verticalBinPlateau_one (2*x) h2]
    simp
  · have hne : x≠0 := by intro hz; subst x; norm_num at hs
    by_cases hp : 0<x
    · have hx : 1/2≤x := by rw [abs_of_pos hp] at hs; linarith
      rw [hilbertSmoothSign_pos x hx,hilbertFrequencySign,ite_eq_left hp.le]
      simp only [one_mul,Complex.ofReal_sub]
      rfl
    · have hx : x≤-(1/2) := by rw [abs_of_nonpos (le_of_not_gt hp)] at hs; linarith
      rw [hilbertSmoothSign_neg x hx,hilbertFrequencySign,ite_eq_right (by linarith)]
      simp only [neg_one_mul,Complex.ofReal_neg,Complex.ofReal_sub]
      rfl

theorem hilbertFiniteSymbol_apply (N : ℕ) (L : ℝ) (hL : 0<L) (eta : ℝ) :
    hilbertFiniteSymbol N L hL eta=-(Real.pi:ℂ)*Complex.I*hilbertFrequencySign eta*
      (verticalBinPlateau ((2*L)/(2:ℝ)^N*eta)-verticalBinPlateau ((2*L)*eta)) := by
  have hterm (j : ℕ) : hilbertAnnularSymbol (L/(2:ℝ)^j*eta)=
      (-(Real.pi:ℂ)*Complex.I*hilbertFrequencySign eta)*
      (verticalBinPlateau ((2*L)/(2:ℝ)^(j+1)*eta)-verticalBinPlateau ((2*L)/(2:ℝ)^j*eta)) := by
    rw [hilbertAnnularSymbol_sign]
    have hp : 0<L/(2:ℝ)^j := div_pos hL (pow_pos (by norm_num) j)
    have hsign : hilbertFrequencySign (L/(2:ℝ)^j*eta)=hilbertFrequencySign eta :=
      hilbertFrequencySign_pos_mul _ _ hp
    have h1 : L/(2:ℝ)^j*eta=(2*L)/(2:ℝ)^(j+1)*eta := by rw [pow_succ]; field_simp
    have h2 : 2*(L/(2:ℝ)^j*eta)=(2*L)/(2:ℝ)^j*eta := by ring
    rw [hsign,h1]
    rw [←h1,h2]
    ring
  simp only [hilbertFiniteSymbol,sum_apply,dilatedSlopeWindow_apply,hterm]
  rw [←Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    verticalBinPlateau ((2*L)/(2:ℝ)^(j+1)*eta)-verticalBinPlateau ((2*L)/(2:ℝ)^j*eta)) N]
  rw [Finset.sum_range_sub (fun j : ℕ =>
    verticalBinPlateau ((2*L)/(2:ℝ)^j*eta))]
  simp only [pow_zero,div_one]

theorem hilbertFiniteSymbol_norm (N : ℕ) (L : ℝ) (hL : 0<L) (eta : ℝ) :
    ‖hilbertFiniteSymbol N L hL eta‖≤Real.pi := by
  rw [hilbertFiniteSymbol_apply]
  have hdiff : ‖verticalBinPlateau ((2*L)/(2:ℝ)^N*eta)-verticalBinPlateau ((2*L)*eta)‖≤1 := by
    change ‖((verticalBinPlateauReal ((2*L)/(2:ℝ)^N*eta):ℂ)-
      (verticalBinPlateauReal ((2*L)*eta):ℂ))‖≤1
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    have h1 := verticalBinPlateauReal_range ((2*L)/(2:ℝ)^N*eta)
    have h2 := verticalBinPlateauReal_range ((2*L)*eta)
    exact abs_le.mpr ⟨by linarith [h1.1,h2.2],by linarith [h1.2,h2.1]⟩
  have hsign : ‖hilbertFrequencySign eta‖≤1 := by
    unfold hilbertFrequencySign
    split_ifs <;> norm_num
  simp only [norm_mul,norm_neg,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_I,mul_one]
  exact (mul_le_mul_of_nonneg_left hdiff (mul_nonneg Real.pi_pos.le (norm_nonneg _))).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsign Real.pi_pos.le)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HilbertFiniteL2
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform L2 bounds for the actual finite smooth Hilbert convolutions. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem lineProjectionKernel_unit (q : SchwartzMap ℝ ℂ) :
    lineProjectionKernel q 1 (by norm_num)=𝓕⁻ q := by
  unfold lineProjectionKernel
  congr 1
  ext x
  simp only [dilatedSlopeWindow_apply,one_mul]

theorem hilbertFinite_kernel (N : ℕ) (L : ℝ) (hL : 0<L) (x : ℝ) :
    lineProjectionKernel (hilbertFiniteSymbol N L hL) 1 (by norm_num) x=
      finiteTimeKernel hilbertTimeKernel N L x := by
  have he : lineProjectionKernel (hilbertFiniteSymbol N L hL) 1 (by norm_num)=
      ∑ j : Fin N, lineProjectionKernel hilbertAnnularSymbol (L/(2:ℝ)^j.val)
        (ne_of_gt (div_pos hL (pow_pos (by norm_num) j.val))) := by
    rw [lineProjectionKernel_unit,hilbertFiniteSymbol,FourierTransform.fourierInv_sum]
    rfl
  rw [he]
  simp only [sum_apply,finiteTimeKernel]
  apply Finset.sum_congr rfl
  intro j _
  rw [lineProjectionKernel_eq_scaled _ _ (div_pos hL (pow_pos (by norm_num) j.val)),
    scaledSchwartzKernel_apply]
  rfl

theorem hilbertFinite_L2 (N : ℕ) (L : ℝ) (hL : 0<L) (f : SchwartzMap ℝ ℂ) :
    MemLp (lineConvolution (finiteTimeKernel hilbertTimeKernel N L) f) 2 volume ∧
      (∫ x, ‖lineConvolution (finiteTimeKernel hilbertTimeKernel N L) f x‖^2)≤
        Real.pi^2*(∫ x, ‖f x‖^2) := by
  have he : lineConvolution (finiteTimeKernel hilbertTimeKernel N L) f=
      lineSchwartzProjection (hilbertFiniteSymbol N L hL) 1 (by norm_num) f := by
    funext x
    rw [lineSchwartzProjection_eq_convolution]
    simp only [lineConvolution,hilbertFinite_kernel]
  rw [he]
  exact ⟨(lineSchwartzProjection _ _ _ f).memLp 2 volume,
    lineSchwartzProjection_energy _ 1 (by norm_num) Real.pi (hilbertFiniteSymbol_norm N L hL) f⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HilbertSignFourth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fourth-power bound for the sign multiplier on Schwartz functions. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertSign_fourth_power (f g : SchwartzMap ℝ ℂ)
    (hzero : (𝓕 f : SchwartzMap ℝ ℂ) 0=0)
    (hfg : ∀ eta, (𝓕 g : SchwartzMap ℝ ℂ) eta=
      hilbertFrequencySign eta*(𝓕 f : SchwartzMap ℝ ℂ) eta) :
    (∫ x, ‖g x‖^4)≤68*(∫ x, ‖f x‖^4) := by
  let a : SchwartzMap ℝ ℂ := (1/2:ℂ) • (f+g)
  let b : SchwartzMap ℝ ℂ := (1/2:ℂ) • (f-g)
  have ha : ∀ eta, eta≤0 → (𝓕 a : SchwartzMap ℝ ℂ) eta=0 := by
    intro eta he
    change (𝓕 ((1/2:ℂ) • (f+g)) : SchwartzMap ℝ ℂ) eta=0
    simp only [FourierTransform.fourier_smul,FourierTransform.fourier_add,smul_apply,
      add_apply,smul_eq_mul,hfg]
    rcases he.eq_or_lt with hz | hn
    · subst eta
      rw [hzero,mul_zero,add_zero,mul_zero]
    · rw [hilbertFrequencySign,ite_eq_right (by linarith)]
      ring
  have hb : ∀ eta, 0≤eta → (𝓕 b : SchwartzMap ℝ ℂ) eta=0 := by
    intro eta he
    change (𝓕 ((1/2:ℂ) • (f-g)) : SchwartzMap ℝ ℂ) eta=0
    simp only [sub_eq_add_neg,FourierTransform.fourier_smul,FourierTransform.fourier_add,
      FourierTransform.fourier_neg,smul_apply,add_apply,neg_apply,smul_eq_mul,hfg]
    rw [hilbertFrequencySign,ite_eq_left he]
    ring
  have hab : a+b=f := by
    ext x
    simp only [a,b,add_apply,sub_apply,smul_apply,smul_eq_mul]
    ring
  have hdiff : a-b=g := by
    ext x
    simp only [a,b,add_apply,sub_apply,smul_apply,smul_eq_mul]
    ring
  have hh := hardyPair_fourth_power a b ha hb
  rwa [hab,hdiff] at hh

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

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineProjectionFourth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform fourth-power estimates for one or two scaled smooth cutoffs. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem norm_add_fourth_le (x y : ℂ) : ‖x+y‖^4≤8*(‖x‖^4+‖y‖^4) := by
  calc
    _ ≤ (‖x‖+‖y‖)^4 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 4
    _ ≤ _ := by simpa only [show (4:ℕ)-1=3 from rfl,show (2:ℝ)^3=8 by norm_num] using
      add_pow_le (norm_nonneg x) (norm_nonneg y) 4

theorem norm_sub_fourth_le (x y : ℂ) : ‖x-y‖^4≤8*(‖x‖^4+‖y‖^4) := by
  simpa only [sub_eq_add_neg,norm_neg] using norm_add_fourth_le x (-y)

theorem lineSchwartzProjection_fourth (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W)
    (f : SchwartzMap ℝ ℂ) :
    (∫ x, ‖lineSchwartzProjection q W hW.ne' f x‖^4)≤
      (∫ t, ‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖)^4*(∫ x, ‖f x‖^4) := by
  have hh := (lineConvolution_fourth_bound (lineProjectionKernel q W hW.ne')
    (lineProjectionKernel q W hW.ne').integrable
    (lineProjectionKernel q W hW.ne').continuous.measurable f).2
  simp_rw [←lineSchwartzProjection_eq_convolution q W hW.ne' f] at hh
  rwa [lineProjectionKernel_l1 q W hW] at hh

theorem lineSchwartzProjection_difference_fourth (q : SchwartzMap ℝ ℂ)
    (A B : ℝ) (hA : 0<A) (hB : 0<B) (f : SchwartzMap ℝ ℂ) :
    (∫ x, ‖(lineSchwartzProjection q A hA.ne' f-
      lineSchwartzProjection q B hB.ne' f) x‖^4)≤
      16*(∫ t, ‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖)^4*(∫ x, ‖f x‖^4) := by
  let u := lineSchwartzProjection q A hA.ne' f
  let v := lineSchwartzProjection q B hB.ne' f
  have hu : Integrable (fun x => ‖u x‖^4) := (u.memLp 4 volume).integrable_norm_pow (by decide)
  have hv : Integrable (fun x => ‖v x‖^4) := (v.memLp 4 volume).integrable_norm_pow (by decide)
  have hd : Integrable (fun x => ‖(u-v) x‖^4) := ((u-v).memLp 4 volume).integrable_norm_pow (by decide)
  have hh := integral_mono hd ((hu.add hv).const_mul 8) (fun x => norm_sub_fourth_le (u x) (v x))
  simp only [Pi.add_apply] at hh
  rw [integral_const_mul,integral_add hu hv] at hh
  have ha := lineSchwartzProjection_fourth q A hA f
  have hb := lineSchwartzProjection_fourth q B hB f
  change (∫ x, ‖(u-v) x‖^4)≤_
  change (∫ x, ‖u x‖^4)≤_ at ha
  change (∫ x, ‖v x‖^4)≤_ at hb
  linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HilbertFiniteFourth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform fourth-power bounds for the finite smooth Hilbert kernel. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertFinite_fourth (N : ℕ) (L : ℝ) (hL : 0<L) (f : SchwartzMap ℝ ℂ) :
    (∫ x, ‖lineConvolution (finiteTimeKernel hilbertTimeKernel N L) f x‖^4)≤
      (68*16*Real.pi^4*(∫ t, ‖(𝓕⁻ verticalBinPlateau : SchwartzMap ℝ ℂ) t‖)^4)*
        (∫ x, ‖f x‖^4) := by
  let A := (2*L)/(2:ℝ)^N
  let B := 2*L
  have hA : 0<A := div_pos (mul_pos (by norm_num) hL) (pow_pos (by norm_num) N)
  have hB : 0<B := mul_pos (by norm_num) hL
  let u := lineSchwartzProjection verticalBinPlateau A hA.ne' f-
    lineSchwartzProjection verticalBinPlateau B hB.ne' f
  let H := lineSchwartzProjection (hilbertFiniteSymbol N L hL) 1 (by norm_num) f
  let k : ℂ := -(Real.pi:ℂ)*Complex.I
  have hk : k≠0 := mul_ne_zero (neg_ne_zero.mpr (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  let v := k⁻¹ • H
  have hu (eta : ℝ) : (𝓕 u : SchwartzMap ℝ ℂ) eta=
      (verticalBinPlateau (A*eta)-verticalBinPlateau (B*eta))*(𝓕 f : SchwartzMap ℝ ℂ) eta := by
    change (𝓕 (lineSchwartzProjection verticalBinPlateau A hA.ne' f-
      lineSchwartzProjection verticalBinPlateau B hB.ne' f) : SchwartzMap ℝ ℂ) eta=_
    simp only [sub_eq_add_neg,FourierTransform.fourier_add,FourierTransform.fourier_neg,
      add_apply,neg_apply,lineSchwartzProjection_fourier]
    ring
  have huzero : (𝓕 u : SchwartzMap ℝ ℂ) 0=0 := by rw [hu]; simp
  have hv (eta : ℝ) : (𝓕 v : SchwartzMap ℝ ℂ) eta=
      hilbertFrequencySign eta*(𝓕 u : SchwartzMap ℝ ℂ) eta := by
    change (𝓕 (k⁻¹ • H) : SchwartzMap ℝ ℂ) eta=_
    rw [FourierTransform.fourier_smul,smul_apply]
    change k⁻¹*(𝓕 H : SchwartzMap ℝ ℂ) eta=_
    rw [lineSchwartzProjection_fourier,one_mul,hilbertFiniteSymbol_apply,hu]
    change k⁻¹*(k*hilbertFrequencySign eta*
      (verticalBinPlateau (A*eta)-verticalBinPlateau (B*eta))*(𝓕 f : SchwartzMap ℝ ℂ) eta)=_
    calc
      _ = (k⁻¹*k)*(hilbertFrequencySign eta*
        ((verticalBinPlateau (A*eta)-verticalBinPlateau (B*eta))*(𝓕 f : SchwartzMap ℝ ℂ) eta)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hk,one_mul]
  have hv4 := hilbertSign_fourth_power u v huzero hv
  have hu4 := lineSchwartzProjection_difference_fourth verticalBinPlateau A B hA hB f
  have hH : H=k • v := by dsimp [v]; rw [smul_smul,mul_inv_cancel₀ hk,one_smul]
  have hkn : ‖k‖=Real.pi := by
    simp only [k,norm_mul,norm_neg,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,
      Complex.norm_I,mul_one]
  have heq (x : ℝ) : lineConvolution (finiteTimeKernel hilbertTimeKernel N L) f x=H x := by
    dsimp [H]
    rw [lineSchwartzProjection_eq_convolution]
    simp only [lineConvolution,hilbertFinite_kernel]
  simp_rw [heq,hH,smul_apply,norm_smul,hkn,mul_pow]
  rw [integral_const_mul]
  change (∫ x, ‖u x‖^4)≤_ at hu4
  have hp : 0≤Real.pi^4 := pow_nonneg Real.pi_pos.le 4
  calc
    _ ≤ Real.pi^4*(68*(∫ x, ‖u x‖^4)) := mul_le_mul_of_nonneg_left hv4 hp
    _ ≤ Real.pi^4*(68*(16*(∫ t, ‖(𝓕⁻ verticalBinPlateau : SchwartzMap ℝ ℂ) t‖)^4*
        (∫ x, ‖f x‖^4))) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hu4 (by norm_num)) hp
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SharpHilbertFourth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform fourth-power estimate for the actual sharp truncations. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem sharpHilbert_uniform_fourth : ∃ D : ℝ, 0≤D ∧
    ∀ r R : ℝ, 0 < r → r≤R → ∀ f : SchwartzMap ℝ ℂ,
      Integrable (fun x => ‖oneDimensionalTruncatedHilbert r R f x‖^4) ∧
      (∫ x, ‖oneDimensionalTruncatedHilbert r R f x‖^4)≤D*(∫ x, ‖f x‖^4) := by
  obtain ⟨B,hB,hkernel⟩ := hilbertTimeKernel_arbitrary_endpoint
  let D := 68*16*Real.pi^4*(∫ t, ‖(𝓕⁻ verticalBinPlateau : SchwartzMap ℝ ℂ) t‖)^4
  have hD : 0≤D := by dsimp [D]; positivity
  refine ⟨8*(B^4+D),by positivity,?_⟩
  intro r R hr hrR f
  have hhalf : 0<R/2 := by linarith
  obtain ⟨N,_,_,hEi,hEb⟩ := hkernel r R hr hrR
  let K := sharpTimeKernel r R
  let J := finiteTimeKernel hilbertTimeKernel N (R/2)
  let E := fun t => K t-J t
  have hKi : Integrable K := sharpTimeKernel_integrable r R hr (hr.trans_le hrR)
  have hJi : Integrable J := finiteTimeKernel_integrable _ N (R/2) hhalf
  have hEm : Measurable E := (sharpTimeKernel_measurable r R).sub
    (finiteTimeKernel_measurable _ N (R/2))
  have he := lineConvolution_fourth_bound E hEi hEm f
  have hj := lineConvolution_fourth_bound J hJi (finiteTimeKernel_measurable _ _ _) f
  have heBound : (∫ x, ‖lineConvolution E f x‖^4)≤B^4*(∫ x, ‖f x‖^4) :=
    he.2.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (integral_nonneg fun _ => norm_nonneg _) hEb 4)
      (integral_nonneg fun _ => by positivity))
  have hjBound : (∫ x, ‖lineConvolution J f x‖^4)≤D*(∫ x, ‖f x‖^4) :=
    hilbertFinite_fourth N (R/2) hhalf f
  have heq (x : ℝ) : oneDimensionalTruncatedHilbert r R f x=
      lineConvolution E f x+lineConvolution J f x := by
    have hsub : lineConvolution E f x=lineConvolution K f x-lineConvolution J f x := by
      change (∫ t, (K t-J t)*f (x-t))=_
      simp_rw [sub_mul]
      exact integral_sub
        (lineConvolution_integrand_of_bounded K f hKi f.continuous.measurable
          (SchwartzMap.seminorm ℝ 0 0 f) (fun y => SchwartzMap.norm_le_seminorm ℝ f y) x)
        (lineConvolution_integrand_of_bounded J f hJi f.continuous.measurable
          (SchwartzMap.seminorm ℝ 0 0 f) (fun y => SchwartzMap.norm_le_seminorm ℝ f y) x)
    change lineConvolution K f x=_
    rw [hsub,sub_add_cancel]
  have hm : Measurable (oneDimensionalTruncatedHilbert r R f) :=
    lineConvolution_measurable K (sharpTimeKernel_measurable r R) f f.continuous.measurable
  have hd := (he.1.add hj.1).const_mul 8
  have hp (x : ℝ) : ‖oneDimensionalTruncatedHilbert r R f x‖^4≤
      8*(‖lineConvolution E f x‖^4+‖lineConvolution J f x‖^4) := by
    rw [heq]
    exact norm_add_fourth_le _ _
  have hi : Integrable (fun x => ‖oneDimensionalTruncatedHilbert r R f x‖^4) := by
    apply hd.mono' (hm.norm.pow_const 4).aestronglyMeasurable
    filter_upwards [] with x
    simpa only [Pi.add_apply,Real.norm_of_nonneg (by positivity : 0≤‖oneDimensionalTruncatedHilbert r R f x‖^4)] using hp x
  refine ⟨hi,?_⟩
  have hh := integral_mono hi hd hp
  simp only [Pi.add_apply] at hh
  rw [integral_const_mul,integral_add he.1 hj.1] at hh
  linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SharpHilbertL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform L2 estimate for all finite sharp one-dimensional Hilbert
truncations. This is a proved foundation for the remaining Lp input. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

private theorem energy_eLpNorm_bound (g : ℝ → ℂ) (hg : MemLp g 2 volume)
    (f : SchwartzMap ℝ ℂ) (C : ℝ) (hC : 0≤C)
    (he : (∫ x, ‖g x‖^2)≤C^2*(∫ x, ‖f x‖^2)) :
    eLpNorm g 2 volume≤ENNReal.ofReal (C*‖f.toLp 2 volume‖) := by
  have hout := memLp_toL2_norm_sq volume g hg
  have hin := memLp_toL2_norm_sq volume f (f.memLp 2 volume)
  change ‖f.toLp 2 volume‖^2=_ at hin
  rw [←hout,←hin] at he
  have hn : ‖hg.toLp g‖≤C*‖f.toLp 2 volume‖ :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
      (by simpa only [mul_pow] using he)
  rw [←Lp.enorm_toLp hg,←ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hn

theorem sharpHilbert_uniform_L2 : ∃ C : ℝ, 0<C ∧
    ∀ r R : ℝ, 0 < r → r≤R → ∀ f : SchwartzMap ℝ ℂ,
      MemLp (oneDimensionalTruncatedHilbert r R f) 2 volume ∧
      eLpNorm (oneDimensionalTruncatedHilbert r R f) 2 volume≤
        ENNReal.ofReal (C*‖f.toLp 2 volume‖) := by
  obtain ⟨B,hB,hkernel⟩ := hilbertTimeKernel_arbitrary_endpoint
  refine ⟨B+Real.pi,by linarith [Real.pi_pos],?_⟩
  intro r R hr hrR f
  have hR : 0<R := hr.trans_le hrR
  have hhalf : 0<R/2 := by positivity
  obtain ⟨N,_,_,hEi,hEb⟩ := hkernel r R hr hrR
  let K := sharpTimeKernel r R
  let J := finiteTimeKernel hilbertTimeKernel N (R/2)
  let E := fun t => K t-J t
  have hKi : Integrable K := sharpTimeKernel_integrable r R hr (hr.trans_le hrR)
  have hJi : Integrable J := finiteTimeKernel_integrable _ N (R/2) hhalf
  have hEm : Measurable E := (sharpTimeKernel_measurable r R).sub
    (finiteTimeKernel_measurable _ N (R/2))
  have herror := lineConvolution_energy_bound E hEi hEm f f.continuous.measurable (f.memLp 2 volume)
  have hEb' : (∫ t, ‖E t‖)^2≤B^2 := pow_le_pow_left₀
    (integral_nonneg fun _ => norm_nonneg _) hEb 2
  have herrorBound := energy_eLpNorm_bound (lineConvolution E f) herror.1 f B hB
    (herror.2.trans (mul_le_mul_of_nonneg_right hEb' (integral_nonneg fun _ => sq_nonneg _)))
  have hsmooth := hilbertFinite_L2 N (R/2) hhalf f
  have hsmoothBound := energy_eLpNorm_bound (lineConvolution J f) hsmooth.1 f Real.pi
    Real.pi_pos.le hsmooth.2
  have heq : oneDimensionalTruncatedHilbert r R f=lineConvolution E f+lineConvolution J f := by
    funext x
    have hsub : lineConvolution E f x=lineConvolution K f x-lineConvolution J f x := by
      change (∫ t, (K t-J t)*f (x-t))=_
      simp_rw [sub_mul]
      exact integral_sub
        (lineConvolution_integrand_of_bounded K f hKi f.continuous.measurable
          (SchwartzMap.seminorm ℝ 0 0 f) (fun y => SchwartzMap.norm_le_seminorm ℝ f y) x)
        (lineConvolution_integrand_of_bounded J f hJi f.continuous.measurable
          (SchwartzMap.seminorm ℝ 0 0 f) (fun y => SchwartzMap.norm_le_seminorm ℝ f y) x)
    change lineConvolution K f x=_
    rw [Pi.add_apply,hsub,sub_add_cancel]
  rw [heq]
  refine ⟨herror.1.add hsmooth.1,?_⟩
  calc
    _ ≤ eLpNorm (lineConvolution E f) 2 volume+eLpNorm (lineConvolution J f) 2 volume :=
      eLpNorm_add_le herror.1.aestronglyMeasurable hsmooth.1.aestronglyMeasurable (by norm_num)
    _ ≤ ENNReal.ofReal (B*‖f.toLp 2 volume‖)+ENNReal.ofReal (Real.pi*‖f.toLp 2 volume‖) :=
      add_le_add herrorBound hsmoothBound
    _ = _ := by
      rw [←ENNReal.ofReal_add (mul_nonneg hB (norm_nonneg _))
        (mul_nonneg Real.pi_pos.le (norm_nonneg _))]
      congr 1
      ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LayerEnergyMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two layer integrals needed to interpolate the second and fourth
moments to the third moment. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem highLayerEnergy_integral (f : ℝ → ℂ) (hf : Measurable f) :
    (∫⁻ t in Ioi 0, highLayerEnergy f t)=∫⁻ x, ENNReal.ofReal (‖f x‖^3) := by
  unfold highLayerEnergy
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr
    intro x
    have he : (fun t : ℝ => if t≤‖f x‖ then ENNReal.ofReal (‖f x‖^2) else 0)=
        (Iic ‖f x‖).indicator (fun _ => ENNReal.ofReal (‖f x‖^2)) := by
      funext t
      simp only [Set.indicator,mem_Iic]
    rw [he,lintegral_indicator measurableSet_Iic,lintegral_const]
    simp only [Measure.restrict_apply MeasurableSet.univ,univ_inter]
    rw [Measure.restrict_apply measurableSet_Iic]
    have hset : Iic ‖f x‖∩Ioi (0:ℝ)=Ioc 0 ‖f x‖ := by ext t; simp only [mem_inter_iff,mem_Iic,mem_Ioi,mem_Ioc]; tauto
    rw [hset,Real.volume_Ioc,sub_zero,←ENNReal.ofReal_mul (by positivity)]
    congr 1
  · exact ((hf.comp measurable_snd).norm.pow_const 2).ennreal_ofReal.ite
      (measurableSet_le measurable_fst (hf.comp measurable_snd).norm) measurable_const |>.aemeasurable

theorem lowLayer_scalar_integral (a : ℝ) (ha : 0≤a) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t^(-2:ℝ))*
      (if a<t then ENNReal.ofReal (a^4) else 0))=ENNReal.ofReal (a^3) := by
  by_cases hz : a=0
  · subst a
    simp
  have hap : 0<a := lt_of_le_of_ne ha (Ne.symm hz)
  have he : (fun t : ℝ => ENNReal.ofReal (t^(-2:ℝ))*
      (if a<t then ENNReal.ofReal (a^4) else 0))=
      (Ioi a).indicator (fun t => ENNReal.ofReal (t^(-2:ℝ))*ENNReal.ofReal (a^4)) := by
    funext t
    by_cases ht : a<t <;> simp [ht]
  rw [he,lintegral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  rw [inter_eq_left.mpr (Ioi_subset_Ioi ha)]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  have hint : IntegrableOn (fun t : ℝ => t^(-2:ℝ)) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hap
  have hnonneg : 0≤ᵐ[volume.restrict (Ioi a)] (fun t : ℝ => t^(-2:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hap.trans ht).le _
  rw [←ofReal_integral_eq_lintegral_ofReal hint hnonneg,
    integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hap]
  norm_num
  rw [←ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  exact Real.rpow_neg_one a ▸ inv_mul_cancel₀ hz

theorem lowLayerEnergy_integral (f : ℝ → ℂ) (hf : Measurable f) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t^(-2:ℝ))*lowLayerEnergy f t)=
      ∫⁻ x, ENNReal.ofReal (‖f x‖^3) := by
  unfold lowLayerEnergy
  simp_rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_lintegral_swap]
  · exact lintegral_congr fun x => lowLayer_scalar_integral ‖f x‖ (norm_nonneg _)
  · have hm : Measurable (fun p : ℝ×ℝ => if ‖f p.2‖<p.1 then ENNReal.ofReal (‖f p.2‖^4) else 0) :=
      ((hf.comp measurable_snd).norm.pow_const 4).ennreal_ofReal.ite
        (measurableSet_lt (hf.comp measurable_snd).norm measurable_fst) measurable_const
    exact ((measurable_fst.pow_const (-2:ℝ)).ennreal_ofReal.mul hm).aemeasurable

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BoundedConvolutionL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer of a Schwartz L2 convolution bound to bounded measurable
L2 inputs, using density and the actual convolution difference. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation
local instance instTwoAtLeastOne : Fact (1≤(2:ℝ≥0∞)) := ⟨by norm_num⟩

theorem toL2_norm_le_of_integral (f g : ℝ → ℂ)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (C : ℝ) (hC : 0≤C)
    (h : (∫ x, ‖g x‖^2)≤C^2*(∫ x, ‖f x‖^2)) :
    ‖hg.toLp g‖≤C*‖hf.toLp f‖ := by
  rw [←memLp_toL2_norm_sq volume g hg,←memLp_toL2_norm_sq volume f hf] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg (hg.toLp g)) (mul_nonneg hC (norm_nonneg (hf.toLp f)))
    (by decide : (2:ℕ)≠0)).mp (by simpa only [mul_pow] using h)

theorem boundedConvolution_L2_difference (K f g : ℝ → ℂ)
    (hK : Integrable K) (hKm : Measurable K) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hcf : MemLp (lineConvolution K f) 2 volume) (hcg : MemLp (lineConvolution K g) 2 volume)
    (Bf Bg : ℝ) (hfb : ∀ x, ‖f x‖≤Bf) (hgb : ∀ x, ‖g x‖≤Bg) :
    ‖hcf.toLp (lineConvolution K f)-hcg.toLp (lineConvolution K g)‖≤
      (∫ t, ‖K t‖)*‖hf.toLp f-hg.toLp g‖ := by
  have he := (lineConvolution_energy_bound K hK hKm (f-g) (hfm.sub hgm) (hf.sub hg)).2
  rw [lineConvolution_sub_of_bounded K f g hK hfm hgm Bf Bg hfb hgb] at he
  have hn := toL2_norm_le_of_integral (f-g) (lineConvolution K f-lineConvolution K g)
    (hf.sub hg) (hcf.sub hcg) _ (integral_nonneg fun _ => norm_nonneg _) he
  rwa [hf.toLp_sub hg,hcf.toLp_sub hcg] at hn

theorem boundedConvolution_L2_of_schwartz (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (C : ℝ) (hC : 0≤C)
    (hsch : ∀ g : SchwartzMap ℝ ℂ,
      (∫ x, ‖lineConvolution K g x‖^2)≤C^2*(∫ x, ‖g x‖^2))
    (f : ℝ → ℂ) (hfm : Measurable f) (hf : MemLp f 2 volume)
    (B : ℝ) (hfb : ∀ x, ‖f x‖≤B) :
    (∫ x, ‖lineConvolution K f x‖^2)≤C^2*(∫ x, ‖f x‖^2) := by
  let L := ∫ t, ‖K t‖
  have hL : 0≤L := integral_nonneg fun _ => norm_nonneg _
  let hcf := (lineConvolution_energy_bound K hK hKm f hfm hf).1
  let xf := hf.toLp f
  let yf := hcf.toLp (lineConvolution K f)
  have hd : DenseRange (fun g : SchwartzMap ℝ ℂ => g.toLp 2 volume) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  have hnorm : ‖yf‖≤C*‖xf‖ := by
    by_contra hn
    have hgap : 0<‖yf‖-C*‖xf‖ := by linarith
    let eps := (‖yf‖-C*‖xf‖)/(2*(C+L+1))
    have heps : 0<eps := div_pos hgap (by positivity)
    obtain ⟨g,hg⟩ := hd.exists_dist_lt xf heps
    let hcg := (lineConvolution_energy_bound K hK hKm g g.continuous.measurable (g.memLp 2 volume)).1
    let yg := hcg.toLp (lineConvolution K g)
    have hgBound : ‖yg‖≤C*‖g.toLp 2 volume‖ :=
      toL2_norm_le_of_integral g _ (g.memLp 2 volume) hcg C hC (hsch g)
    have hdiff : ‖yf-yg‖≤L*‖xf-g.toLp 2 volume‖ :=
      boundedConvolution_L2_difference K f g hK hKm hfm g.continuous.measurable
        hf (g.memLp 2 volume) hcf hcg B (SchwartzMap.seminorm ℝ 0 0 g)
        hfb (fun x => SchwartzMap.norm_le_seminorm ℝ g x)
    have htri : ‖yf‖≤‖yf-yg‖+‖yg‖ := by
      simpa only [sub_add_cancel] using norm_add_le (yf-yg) yg
    have hgin : ‖g.toLp 2 volume‖≤‖xf‖+‖xf-g.toLp 2 volume‖ := by
      have hh := norm_add_le (g.toLp 2 volume-xf) xf
      rw [sub_add_cancel,norm_sub_rev] at hh
      linarith
    have htot : ‖yf‖≤C*‖xf‖+(C+L)*‖xf-g.toLp 2 volume‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hgin hC]
    have hdist : ‖xf-g.toLp 2 volume‖<eps := by simpa only [dist_eq_norm] using hg
    have hsmall : (C+L)*‖xf-g.toLp 2 volume‖<(C+L+1)*eps := by
      calc
        _ ≤ (C+L)*eps := mul_le_mul_of_nonneg_left hdist.le (add_nonneg hC hL)
        _ < _ := by nlinarith
    have heq : (C+L+1)*eps=(‖yf‖-C*‖xf‖)/2 := by
      dsimp [eps]
      field_simp [show C+L+1≠0 by positivity]
    rw [heq] at hsmall
    linarith
  have hp := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [mul_pow,memLp_toL2_norm_sq volume f hf,memLp_toL2_norm_sq volume _ hcf] at hp
  exact hp

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BoundedConvolutionL4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer of a Schwartz L4 convolution bound to bounded measurable
L4 inputs, using density and the actual convolution difference. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation
local instance instFourAtLeastOne : Fact (1≤(4:ℝ≥0∞)) := ⟨by norm_num⟩

theorem toL4_norm_le_of_integral (f g : ℝ → ℂ)
    (hf : MemLp f 4 volume) (hg : MemLp g 4 volume) (C : ℝ) (hC : 0≤C)
    (h : (∫ x, ‖g x‖^4)≤C^4*(∫ x, ‖f x‖^4)) :
    ‖hg.toLp g‖≤C*‖hf.toLp f‖ := by
  rw [←memLp_toL4_norm_pow g hg,←memLp_toL4_norm_pow f hf] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg (hg.toLp g)) (mul_nonneg hC (norm_nonneg (hf.toLp f)))
    (by decide : (4:ℕ)≠0)).mp (by simpa only [mul_pow] using h)

theorem lineConvolution_L4_difference (K f g : ℝ → ℂ)
    (hK : Integrable K) (hKm : Measurable K) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 4 volume) (hg : MemLp g 4 volume)
    (hcf : MemLp (lineConvolution K f) 4 volume) (hcg : MemLp (lineConvolution K g) 4 volume)
    (Bf Bg : ℝ) (hfb : ∀ x, ‖f x‖≤Bf) (hgb : ∀ x, ‖g x‖≤Bg) :
    ‖hcf.toLp (lineConvolution K f)-hcg.toLp (lineConvolution K g)‖≤
      (∫ t, ‖K t‖)*‖hf.toLp f-hg.toLp g‖ := by
  have he := (lineConvolution_L4_bound K (f-g) hK hKm (hfm.sub hgm) (hf.sub hg)).2
  rw [lineConvolution_sub_of_bounded K f g hK hfm hgm Bf Bg hfb hgb] at he
  have hn := toL4_norm_le_of_integral (f-g) (lineConvolution K f-lineConvolution K g)
    (hf.sub hg) (hcf.sub hcg) _ (integral_nonneg fun _ => norm_nonneg _) he
  rwa [hf.toLp_sub hg,hcf.toLp_sub hcg] at hn

theorem boundedConvolution_L4_of_schwartz (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (C : ℝ) (hC : 0≤C)
    (hsch : ∀ g : SchwartzMap ℝ ℂ,
      (∫ x, ‖lineConvolution K g x‖^4)≤C^4*(∫ x, ‖g x‖^4))
    (f : ℝ → ℂ) (hfm : Measurable f) (hf : MemLp f 4 volume)
    (B : ℝ) (hfb : ∀ x, ‖f x‖≤B) :
    (∫ x, ‖lineConvolution K f x‖^4)≤C^4*(∫ x, ‖f x‖^4) := by
  let L := ∫ t, ‖K t‖
  have hL : 0≤L := integral_nonneg fun _ => norm_nonneg _
  let hcf := (lineConvolution_L4_bound K f hK hKm hfm hf).1
  let xf := hf.toLp f
  let yf := hcf.toLp (lineConvolution K f)
  have hd : DenseRange (fun g : SchwartzMap ℝ ℂ => g.toLp 4 volume) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (4:ℝ≥0∞)≠⊤)
  have hnorm : ‖yf‖≤C*‖xf‖ := by
    by_contra hn
    have hgap : 0<‖yf‖-C*‖xf‖ := by linarith
    let eps := (‖yf‖-C*‖xf‖)/(2*(C+L+1))
    have heps : 0<eps := div_pos hgap (by positivity)
    obtain ⟨g,hg⟩ := hd.exists_dist_lt xf heps
    let hcg := (lineConvolution_L4_bound K g hK hKm g.continuous.measurable (g.memLp 4 volume)).1
    let yg := hcg.toLp (lineConvolution K g)
    have hgBound : ‖yg‖≤C*‖g.toLp 4 volume‖ :=
      toL4_norm_le_of_integral g _ (g.memLp 4 volume) hcg C hC (hsch g)
    have hdiff : ‖yf-yg‖≤L*‖xf-g.toLp 4 volume‖ :=
      lineConvolution_L4_difference K f g hK hKm hfm g.continuous.measurable
        hf (g.memLp 4 volume) hcf hcg B (SchwartzMap.seminorm ℝ 0 0 g)
        hfb (fun x => SchwartzMap.norm_le_seminorm ℝ g x)
    have htri : ‖yf‖≤‖yf-yg‖+‖yg‖ := by
      simpa only [sub_add_cancel] using norm_add_le (yf-yg) yg
    have hgin : ‖g.toLp 4 volume‖≤‖xf‖+‖xf-g.toLp 4 volume‖ := by
      have hh := norm_add_le (g.toLp 4 volume-xf) xf
      rw [sub_add_cancel,norm_sub_rev] at hh
      linarith
    have htot : ‖yf‖≤C*‖xf‖+(C+L)*‖xf-g.toLp 4 volume‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hgin hC]
    have hdist : ‖xf-g.toLp 4 volume‖<eps := by simpa only [dist_eq_norm] using hg
    have hsmall : (C+L)*‖xf-g.toLp 4 volume‖<(C+L+1)*eps := by
      calc
        _ ≤ (C+L)*eps := mul_le_mul_of_nonneg_left hdist.le (add_nonneg hC hL)
        _ < _ := by nlinarith
    have heq : (C+L+1)*eps=(‖yf‖-C*‖xf‖)/2 := by
      dsimp [eps]
      field_simp [show C+L+1≠0 by positivity]
    rw [heq] at hsmall
    linarith
  have hp := pow_le_pow_left₀ (norm_nonneg _) hnorm 4
  rw [mul_pow,memLp_toL4_norm_pow f hf,memLp_toL4_norm_pow _ hcf] at hp
  exact hp

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ConvolutionPowerTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Markov estimates and the actual large/small amplitude splitting used
for interpolation of line convolutions. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem normPower_tail (g : ℝ → ℂ) (hgm : Measurable g) (n : ℕ)
    (t : ℝ) (ht : 0<t) :
    volume {x | t≤‖g x‖}≤ENNReal.ofReal (t⁻¹)^n*(∫⁻ x, ENNReal.ofReal (‖g x‖^n)) := by
  have hinc : {x | t≤‖g x‖}⊆{x | ENNReal.ofReal (t^n)≤ENNReal.ofReal (‖g x‖^n)} := by
    intro x hx
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ht.le hx n)
  have hpos : ENNReal.ofReal (t^n)≠0 := by positivity
  have hh := meas_ge_le_lintegral_div (μ:=volume)
    ((hgm.norm.pow_const n).ennreal_ofReal.aemeasurable) hpos ENNReal.ofReal_ne_top
  calc
    _ ≤ volume {x | ENNReal.ofReal (t^n)≤ENNReal.ofReal (‖g x‖^n)} := measure_mono hinc
    _ ≤ (∫⁻ x, ENNReal.ofReal (‖g x‖^n))/ENNReal.ofReal (t^n) := hh
    _ = _ := by
      rw [ENNReal.ofReal_pow ht.le,div_eq_mul_inv,ENNReal.inv_pow,
        ←ENNReal.ofReal_inv_of_pos ht,mul_comm]

theorem highAmplitude_measurable (f : ℝ → ℂ) (hf : Measurable f) (t : ℝ) :
    Measurable (highAmplitude f t) := hf.indicator (measurableSet_le measurable_const hf.norm)

theorem lowAmplitude_measurable (f : ℝ → ℂ) (hf : Measurable f) (t : ℝ) :
    Measurable (lowAmplitude f t) := hf.indicator (measurableSet_lt hf.norm measurable_const)

theorem amplitude_sum (f : ℝ → ℂ) (t x : ℝ) : highAmplitude f t x+lowAmplitude f t x=f x := by
  classical
  unfold highAmplitude lowAmplitude
  by_cases hx : t≤‖f x‖ <;> simp [hx,not_lt.mpr,lt_of_not_ge]

theorem amplitude_bound (f : ℝ → ℂ) (t x : ℝ) :
    ‖highAmplitude f t x‖≤‖f x‖ ∧ ‖lowAmplitude f t x‖≤‖f x‖ := by
  classical
  unfold highAmplitude lowAmplitude
  constructor <;> exact norm_indicator_le_norm_self f x

theorem convolution_amplitude_sum (K f : ℝ → ℂ) (hK : Integrable K)
    (hf : Measurable f) (B : ℝ) (hB : ∀ x, ‖f x‖≤B) (t x : ℝ) :
    lineConvolution K f x=lineConvolution K (highAmplitude f t) x+
      lineConvolution K (lowAmplitude f t) x := by
  have hh := lineConvolution_integrand_of_bounded K (highAmplitude f t) hK
    (highAmplitude_measurable f hf t) B (fun x => (amplitude_bound f t x).1.trans (hB x)) x
  have hl := lineConvolution_integrand_of_bounded K (lowAmplitude f t) hK
    (lowAmplitude_measurable f hf t) B (fun x => (amplitude_bound f t x).2.trans (hB x)) x
  rw [lineConvolution,lineConvolution,lineConvolution,←integral_add hh hl]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [←mul_add,amplitude_sum]

theorem highAmplitude_power (f : ℝ → ℂ) (t : ℝ) :
    (∫⁻ x, ENNReal.ofReal (‖highAmplitude f t x‖^2))=highLayerEnergy f t := by
  classical
  apply lintegral_congr
  intro x
  unfold highAmplitude
  by_cases hx : t≤‖f x‖ <;> simp [hx]

theorem lowAmplitude_power (f : ℝ → ℂ) (t : ℝ) :
    (∫⁻ x, ENNReal.ofReal (‖lowAmplitude f t x‖^4))=lowLayerEnergy f t := by
  classical
  apply lintegral_congr
  intro x
  unfold lowAmplitude
  by_cases hx : ‖f x‖<t <;> simp [hx]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ConvolutionLayerTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distribution estimate for interpolation between uniform second
and fourth convolution moments. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem normPower_lintegral_le_of_integral (f g : ℝ → ℂ) (n : ℕ)
    (hf : Integrable (fun x => ‖f x‖^n)) (hg : Integrable (fun x => ‖g x‖^n))
    (A : ℝ) (hA : 0≤A) (h : (∫ x, ‖g x‖^n)≤A*(∫ x, ‖f x‖^n)) :
    (∫⁻ x, ENNReal.ofReal (‖g x‖^n))≤ENNReal.ofReal A*(∫⁻ x, ENNReal.ofReal (‖f x‖^n)) := by
  rw [←ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall fun x => by positivity),
    ←ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall fun x => by positivity),
    ←ENNReal.ofReal_mul hA]
  exact ENNReal.ofReal_le_ofReal h

theorem convolution_layer_tail (K f : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (hf : Measurable f) (hf2 : MemLp f 2 volume) (hf4 : MemLp f 4 volume)
    (M : ℝ) (hM : ∀ x, ‖f x‖≤M) (A C : ℝ) (hA : 0≤A) (hC : 0≤C)
    (h2 : ∀ g : SchwartzMap ℝ ℂ, (∫ x, ‖lineConvolution K g x‖^2)≤A^2*(∫ x, ‖g x‖^2))
    (h4 : ∀ g : SchwartzMap ℝ ℂ, (∫ x, ‖lineConvolution K g x‖^4)≤C^4*(∫ x, ‖g x‖^4))
    (t : ℝ) (ht : 0<t) :
    ENNReal.ofReal (t^2)*volume {x | t≤‖lineConvolution K f x‖}≤
      ENNReal.ofReal (4*A^2)*highLayerEnergy f t+
      ENNReal.ofReal (16*C^4)*(ENNReal.ofReal (t^(-2:ℝ))*lowLayerEnergy f t) := by
  let fh := highAmplitude f t
  let fl := lowAmplitude f t
  have hhm : Measurable fh := highAmplitude_measurable f hf t
  have hlm : Measurable fl := lowAmplitude_measurable f hf t
  have hh2 : MemLp fh 2 volume := hf2.indicator (measurableSet_le measurable_const hf.norm)
  have hl4 : MemLp fl 4 volume := hf4.indicator (measurableSet_lt hf.norm measurable_const)
  have hhb (x : ℝ) : ‖fh x‖≤M := (amplitude_bound f t x).1.trans (hM x)
  have hlb (x : ℝ) : ‖fl x‖≤M := (amplitude_bound f t x).2.trans (hM x)
  have hhOut := (lineConvolution_energy_bound K hK hKm fh hhm hh2).1
  have hlOut := (lineConvolution_L4_bound K fl hK hKm hlm hl4).1
  have eh := normPower_lintegral_le_of_integral fh (lineConvolution K fh) 2
    (hh2.integrable_norm_pow (by decide)) (hhOut.integrable_norm_pow (by decide))
    (A^2) (sq_nonneg A) (boundedConvolution_L2_of_schwartz K hK hKm A hA h2 fh hhm hh2 M hhb)
  have el := normPower_lintegral_le_of_integral fl (lineConvolution K fl) 4
    (hl4.integrable_norm_pow (by decide)) (hlOut.integrable_norm_pow (by decide))
    (C^4) (by positivity) (boundedConvolution_L4_of_schwartz K hK hKm C hC h4 fl hlm hl4 M hlb)
  rw [highAmplitude_power] at eh
  rw [lowAmplitude_power] at el
  have hhTail := (normPower_tail (lineConvolution K fh) (lineConvolution_measurable K hKm fh hhm)
    2 (t/2) (by positivity)).trans (mul_le_mul_right eh _)
  have hlTail := (normPower_tail (lineConvolution K fl) (lineConvolution_measurable K hKm fl hlm)
    4 (t/2) (by positivity)).trans (mul_le_mul_right el _)
  have hset : {x | t≤‖lineConvolution K f x‖}⊆
      {x | t/2≤‖lineConvolution K fh x‖}∪{x | t/2≤‖lineConvolution K fl x‖} := by
    intro x hx
    change t≤‖lineConvolution K f x‖ at hx
    rw [convolution_amplitude_sum K f hK hf M hM t x] at hx
    by_contra hn
    simp only [mem_union,mem_ofPred_eq,not_or,not_le] at hn
    have htri := norm_add_le (lineConvolution K fh x) (lineConvolution K fl x)
    linarith
  have htail := (measure_mono hset).trans (measure_union_le (μ:=volume) _ _)
  have hc2 : ENNReal.ofReal (t^2)*(ENNReal.ofReal ((t/2)⁻¹)^2*ENNReal.ofReal (A^2))=
      ENNReal.ofReal (4*A^2) := by
    rw [←ENNReal.ofReal_pow (by positivity),←ENNReal.ofReal_mul (by positivity),
      ←ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp; ring
  have hc4 : ENNReal.ofReal (t^2)*(ENNReal.ofReal ((t/2)⁻¹)^4*ENNReal.ofReal (C^4))=
      ENNReal.ofReal (16*C^4)*ENNReal.ofReal (t^(-2:ℝ)) := by
    rw [←ENNReal.ofReal_pow (by positivity),←ENNReal.ofReal_mul (by positivity),
      ←ENNReal.ofReal_mul (by positivity),←ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.rpow_neg ht.le,Real.rpow_two]
    field_simp; ring
  calc
    _ ≤ ENNReal.ofReal (t^2)*(volume {x | t/2≤‖lineConvolution K fh x‖}+
        volume {x | t/2≤‖lineConvolution K fl x‖}) := mul_le_mul_right htail _
    _ ≤ ENNReal.ofReal (t^2)*
        ((ENNReal.ofReal ((t/2)⁻¹)^2*ENNReal.ofReal (A^2))*highLayerEnergy f t+
        (ENNReal.ofReal ((t/2)⁻¹)^4*ENNReal.ofReal (C^4))*lowLayerEnergy f t) := by
      exact mul_le_mul_right (add_le_add (by simpa only [mul_assoc] using hhTail)
        (by simpa only [mul_assoc] using hlTail)) _
    _ = (ENNReal.ofReal (t^2)*(ENNReal.ofReal ((t/2)⁻¹)^2*ENNReal.ofReal (A^2)))*highLayerEnergy f t+
        (ENNReal.ofReal (t^2)*(ENNReal.ofReal ((t/2)⁻¹)^4*ENNReal.ofReal (C^4)))*lowLayerEnergy f t := by ring
    _ = _ := by rw [hc2,hc4,mul_assoc]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ConvolutionThird
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real interpolation at exponent three for bounded measurable inputs.
The proof integrates the two amplitude-dependent Markov bounds. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem highLayerEnergy_measurable (f : ℝ → ℂ) (hf : Measurable f) :
    Measurable (highLayerEnergy f) := by
  have hm : Measurable (fun p : ℝ×ℝ => if p.1≤‖f p.2‖ then ENNReal.ofReal (‖f p.2‖^2) else 0) :=
    ((hf.comp measurable_snd).norm.pow_const 2).ennreal_ofReal.ite
      (measurableSet_le measurable_fst (hf.comp measurable_snd).norm) measurable_const
  exact hm.lintegral_prod_right'

theorem lowLayerEnergy_measurable (f : ℝ → ℂ) (hf : Measurable f) :
    Measurable (lowLayerEnergy f) := by
  have hm : Measurable (fun p : ℝ×ℝ => if ‖f p.2‖<p.1 then ENNReal.ofReal (‖f p.2‖^4) else 0) :=
    ((hf.comp measurable_snd).norm.pow_const 4).ennreal_ofReal.ite
      (measurableSet_lt (hf.comp measurable_snd).norm measurable_fst) measurable_const
  exact hm.lintegral_prod_right'

theorem convolution_third_lintegral (K f : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (hf : Measurable f) (hf2 : MemLp f 2 volume) (hf4 : MemLp f 4 volume)
    (M : ℝ) (hM : ∀ x, ‖f x‖≤M) (A C : ℝ) (hA : 0≤A) (hC : 0≤C)
    (h2 : ∀ g : SchwartzMap ℝ ℂ, (∫ x, ‖lineConvolution K g x‖^2)≤A^2*(∫ x, ‖g x‖^2))
    (h4 : ∀ g : SchwartzMap ℝ ℂ, (∫ x, ‖lineConvolution K g x‖^4)≤C^4*(∫ x, ‖g x‖^4)) :
    (∫⁻ x, ENNReal.ofReal (‖lineConvolution K f x‖^3))≤
      ENNReal.ofReal (3*(4*A^2+16*C^4))*(∫⁻ x, ENNReal.ofReal (‖f x‖^3)) := by
  have hm := lineConvolution_measurable K hKm f hf
  have hlc : (∫⁻ x, ENNReal.ofReal (‖lineConvolution K f x‖^3))=
      ENNReal.ofReal 3*(∫⁻ t in Ioi 0,
        ENNReal.ofReal (t^2)*volume {x | t≤‖lineConvolution K f x‖}) := by
    have hh := lintegral_rpow_eq_lintegral_meas_le_mul volume
        (Filter.Eventually.of_forall fun x => norm_nonneg (lineConvolution K f x))
        hm.norm.aemeasurable (by norm_num : 0<(3:ℝ))
    simp only [show (3:ℝ)-1=2 by norm_num,Real.rpow_ofNat] at hh
    rw [hh]
    congr 1
    apply lintegral_congr
    intro t
    rw [mul_comm]
  have hhigh := highLayerEnergy_measurable f hf
  have hlow := lowLayerEnergy_measurable f hf
  have hdom := lintegral_mono_ae (μ:=volume.restrict (Ioi (0:ℝ))) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact convolution_layer_tail K f hK hKm hf hf2 hf4 M hM A C hA hC h2 h4 t ht)
  rw [hlc]
  calc
    _ ≤ ENNReal.ofReal 3*(∫⁻ t in Ioi 0,
        ENNReal.ofReal (4*A^2)*highLayerEnergy f t+
        ENNReal.ofReal (16*C^4)*(ENNReal.ofReal (t^(-2:ℝ))*lowLayerEnergy f t)) :=
      mul_le_mul_right hdom _
    _ = ENNReal.ofReal 3*(ENNReal.ofReal (4*A^2)*(∫⁻ x, ENNReal.ofReal (‖f x‖^3))+
        ENNReal.ofReal (16*C^4)*(∫⁻ x, ENNReal.ofReal (‖f x‖^3))) := by
      rw [lintegral_add_left (hhigh.const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        highLayerEnergy_integral f hf,lowLayerEnergy_integral f hf]
    _ = _ := by
      rw [←add_mul,←mul_assoc,←ENNReal.ofReal_add (by positivity) (by positivity),
        ←ENNReal.ofReal_mul (by norm_num)]

theorem memLp_two_four_integrable_cube (f : ℝ → ℂ) (hf : Measurable f)
    (hf2 : MemLp f 2 volume) (hf4 : MemLp f 4 volume) :
    Integrable (fun x => ‖f x‖^3) := by
  apply ((hf2.integrable_norm_pow (by decide : 2≠0)).add
    (hf4.integrable_norm_pow (by decide : 4≠0))).mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (by positivity : 0≤‖f x‖^3)]
  change ‖f x‖^3≤‖f x‖^2+‖f x‖^4
  nlinarith [sq_nonneg (‖f x‖-1),sq_nonneg (‖f x‖*(‖f x‖-1))]

theorem convolution_third_bound (K f : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (hf : Measurable f) (hf2 : MemLp f 2 volume) (hf4 : MemLp f 4 volume)
    (M : ℝ) (hM : ∀ x, ‖f x‖≤M) (A C : ℝ) (hA : 0≤A) (hC : 0≤C)
    (h2 : ∀ g : SchwartzMap ℝ ℂ, (∫ x, ‖lineConvolution K g x‖^2)≤A^2*(∫ x, ‖g x‖^2))
    (h4 : ∀ g : SchwartzMap ℝ ℂ, (∫ x, ‖lineConvolution K g x‖^4)≤C^4*(∫ x, ‖g x‖^4)) :
    Integrable (fun x => ‖lineConvolution K f x‖^3) ∧
      (∫ x, ‖lineConvolution K f x‖^3)≤(3*(4*A^2+16*C^4))*(∫ x, ‖f x‖^3) := by
  have hlin := convolution_third_lintegral K f hK hKm hf hf2 hf4 M hM A C hA hC h2 h4
  have hfi := memLp_two_four_integrable_cube f hf hf2 hf4
  have hfinite := (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => show 0≤‖f x‖^3 by positivity)).mp hfi.2
  have hfinal : (∫⁻ x, ENNReal.ofReal (‖lineConvolution K f x‖^3))<⊤ :=
    hlin.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinite)
  have hi : Integrable (fun x => ‖lineConvolution K f x‖^3) := by
    refine ⟨(lineConvolution_measurable K hKm f hf).norm.pow_const 3 |>.aestronglyMeasurable,?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => by positivity)).mpr hfinal
  refine ⟨hi,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity),
    ←ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall fun x => by positivity),
    ←ENNReal.ofReal_mul (by positivity)] at hlin
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hlin

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SharpHilbertThird
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The third-moment bound, including bounded measurable inputs needed
as explicit dual test functions. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem sharpHilbert_two_four_constants : ∃ A C : ℝ, 0<A ∧ 0<C ∧
    ∀ r R : ℝ, 0 < r → r≤R → ∀ f : SchwartzMap ℝ ℂ,
      (∫ x, ‖oneDimensionalTruncatedHilbert r R f x‖^2)≤A^2*(∫ x, ‖f x‖^2) ∧
      (∫ x, ‖oneDimensionalTruncatedHilbert r R f x‖^4)≤C^4*(∫ x, ‖f x‖^4) := by
  obtain ⟨A,hA,hTwo⟩ := sharpHilbert_uniform_L2
  obtain ⟨D,hD,hFour⟩ := sharpHilbert_uniform_fourth
  have hDle : D≤(D+1)^4 := by
    nlinarith [sq_nonneg D,pow_nonneg hD 3,pow_nonneg hD 4]
  refine ⟨A,D+1,hA,by positivity,?_⟩
  intro r R hr hrR f
  have h2 := hTwo r R hr hrR f
  have hn := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2.2
  rw [←Lp.norm_toLp _ h2.1,ENNReal.toReal_ofReal (mul_nonneg hA.le (norm_nonneg _))] at hn
  have hp := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [mul_pow,memLp_toL2_norm_sq volume _ h2.1] at hp
  have hfe : ‖f.toLp 2 volume‖^2=∫ x, ‖f x‖^2 := memLp_toL2_norm_sq volume f (f.memLp 2 volume)
  rw [hfe] at hp
  exact ⟨hp,(hFour r R hr hrR f).2.trans
    (mul_le_mul_of_nonneg_right hDle (integral_nonneg fun x => by positivity))⟩

theorem sharpHilbert_uniform_third_bounded : ∃ E : ℝ, 0≤E ∧
    ∀ r R : ℝ, 0 < r → r≤R → ∀ f : ℝ → ℂ, Measurable f →
      MemLp f 2 volume → MemLp f 4 volume →
      ∀ M : ℝ, (∀ x, ‖f x‖≤M) →
      Integrable (fun x => ‖oneDimensionalTruncatedHilbert r R f x‖^3) ∧
      (∫ x, ‖oneDimensionalTruncatedHilbert r R f x‖^3)≤E*(∫ x, ‖f x‖^3) := by
  obtain ⟨A,C,hA,hC,hb⟩ := sharpHilbert_two_four_constants
  refine ⟨3*(4*A^2+16*C^4),by positivity,?_⟩
  intro r R hr hrR f hfm hf2 hf4 M hM
  exact convolution_third_bound (sharpTimeKernel r R) f
    (sharpTimeKernel_integrable r R hr (hr.trans_le hrR)) (sharpTimeKernel_measurable r R)
    hfm hf2 hf4 M hM A C hA.le hC.le
    (fun g => (hb r R hr hrR g).1) (fun g => (hb r R hr hrR g).2)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineConvolutionPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual convolution duality for an integrable input and a bounded test. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_pairing (K f g : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (hf : Integrable f) (hfm : Measurable f)
    (hgm : Measurable g) (B : ℝ) (hgb : ∀ x, ‖g x‖≤B) :
    (∫ x, lineConvolution K f x*g x)=(∫ x, f x*reverseLineConvolution K g x) := by
  have hbase : Integrable (fun p : ℝ×ℝ => K p.2*f (p.1-p.2)) :=
    hK.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hf
  have hJ : Integrable (fun p : ℝ×ℝ => (K p.2*f (p.1-p.2))*g p.1) := by
    apply (hbase.norm.mul_const B).mono' (by fun_prop)
    filter_upwards [] with p
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hgb _) (norm_nonneg _)
  have hbase' : Integrable (fun p : ℝ×ℝ => ‖f p.1‖*‖K p.2‖) := hf.norm.mul_prod hK.norm
  have hJ' : Integrable (fun p : ℝ×ℝ => (K p.2*f p.1)*g (p.1+p.2)) := by
    apply (hbase'.mul_const B).mono' (by fun_prop)
    filter_upwards [] with p
    simp only [norm_mul]
    calc
      _ ≤ (‖K p.2‖*‖f p.1‖)*B := mul_le_mul_of_nonneg_left (hgb _) (by positivity)
      _ = _ := by ring
  calc
    _ = ∫ x, ∫ t, (K t*f (x-t))*g x := by simp_rw [lineConvolution,integral_mul_const]
    _ = ∫ t, ∫ x, (K t*f (x-t))*g x := integral_integral_swap hJ
    _ = ∫ t, ∫ y, (K t*f y)*g (y+t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self (fun x : ℝ => (K t*f (x-t))*g x) t).symm
    _ = ∫ y, ∫ t, (K t*f y)*g (y+t) := (integral_integral_swap hJ').symm
    _ = _ := by
      have he (y t : ℝ) : (K t*f y)*g (y+t)=f y*(K t*g (y+t)) := by ring
      simp_rw [he,integral_const_mul]
      rfl

theorem reverseLineConvolution_conj (K g : ℝ → ℂ)
    (hodd : ∀ t, K (-t)= -K t) (hreal : ∀ t, conj (K t)=K t) (x : ℝ) :
    reverseLineConvolution K (fun y => conj (g y)) x= -conj (lineConvolution K g x) := by
  unfold reverseLineConvolution lineConvolution
  rw [←integral_neg_eq_self (fun t : ℝ => K t*conj (g (x+t)))]
  simp only [hodd,neg_mul,←sub_eq_add_neg]
  rw [integral_neg,←integral_conj]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [map_mul,hreal]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ConvolutionBasicL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability and a uniform pointwise bound for convolution of an
integrable kernel with a Schwartz function. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_integrable (K f : ℝ → ℂ) (hK : Integrable K) (hf : Integrable f) :
    Integrable (lineConvolution K f) := by
  have hj : Integrable (fun p : ℝ×ℝ => K p.2*f (p.1-p.2)) :=
    hK.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hf
  exact hj.integral_prod_left

theorem lineConvolution_bound_basic (K f : ℝ → ℂ) (hK : Integrable K)
    (B : ℝ) (hB : ∀ x, ‖f x‖≤B) (x : ℝ) :
    ‖lineConvolution K f x‖≤(∫ t, ‖K t‖)*B := by
  have hh := norm_integral_le_of_norm_le (hK.norm.mul_const B)
    (Filter.Eventually.of_forall fun t => show ‖K t*f (x-t)‖≤‖K t‖*B from by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _))
  rw [integral_mul_const] at hh
  exact hh

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SharpHilbertThreeHalves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform three-halves estimates by the explicit dual test and the
proved third-moment bound. -/
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_odd (r R t : ℝ) : sharpTimeKernel r R (-t)= -sharpTimeKernel r R t := by
  unfold sharpTimeKernel
  simp only [abs_neg]
  split_ifs <;> simp

theorem sharpHilbert_uniform_three_halves : ∃ C : ℝ, 0<C ∧
    ∀ r R : ℝ, 0 < r → r≤R → ∀ f : SchwartzMap ℝ ℂ,
      Integrable (fun x => ‖oneDimensionalTruncatedHilbert r R f x‖^(3/2:ℝ)) ∧
      (∫ x, ‖oneDimensionalTruncatedHilbert r R f x‖^(3/2:ℝ))≤
        C^(3/2:ℝ)*(∫ x, ‖f x‖^(3/2:ℝ)) := by
  obtain ⟨E,hE,hThird⟩ := sharpHilbert_uniform_third_bounded
  obtain ⟨A,hA,hTwo⟩ := sharpHilbert_uniform_L2
  refine ⟨E+1,by positivity,?_⟩
  intro r R hr hrR f
  let K := sharpTimeKernel r R
  have hKi : Integrable K := sharpTimeKernel_integrable r R hr (hr.trans_le hrR)
  have hKm : Measurable K := sharpTimeKernel_measurable r R
  let g := oneDimensionalTruncatedHilbert r R f
  have hgm : Measurable g := lineConvolution_measurable K hKm f f.continuous.measurable
  have hg1 : Integrable g := lineConvolution_integrable K f hKi f.integrable
  have hg2 : MemLp g 2 volume := (hTwo r R hr hrR f).1
  let B := (∫ t, ‖K t‖)*SchwartzMap.seminorm ℝ 0 0 f
  have hgb (x : ℝ) : ‖g x‖≤B := lineConvolution_bound_basic K f hKi
    (SchwartzMap.seminorm ℝ 0 0 f) (fun y => SchwartzMap.norm_le_seminorm ℝ f y) x
  let h := halfPowerDualTest g
  have hhm : Measurable h := halfPowerDualTest_measurable g hgm
  have hhp := halfPowerDualTest_memLp g hgm hg1 hg2
  have hhb (x : ℝ) : ‖h x‖≤B+1 := halfPowerDualTest_bound g B hgb x
  have hh3 : Integrable (fun x => ‖h x‖^3) := memLp_two_four_integrable_cube h hhm hhp.1 hhp.2
  have hgi : Integrable (fun x => ‖g x‖^(3/2:ℝ)) := by
    simpa only [h,halfPowerDualTest_norm_cube] using hh3
  let J := ∫ x, ‖g x‖^(3/2:ℝ)
  let F := ∫ x, ‖f x‖^(3/2:ℝ)
  have hJ : 0≤J := integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hF : 0≤F := integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  let v := oneDimensionalTruncatedHilbert r R h
  have hvm : Measurable v := lineConvolution_measurable K hKm h hhm
  have hvBound := hThird r R hr hrR h hhm hhp.1 hhp.2 (B+1) hhb
  have hv3 : MemLp v (ENNReal.ofReal (3:ℝ)) volume := by
    have hh : MemLp v 3 volume := (integrable_norm_rpow_iff hvm.aestronglyMeasurable
      (by norm_num : (3:ℝ≥0∞)≠0) (by norm_num)).mp (by simpa using hvBound.1)
    simpa using hh
  have hvEnergy : (∫ x, ‖v x‖^3)≤E*J := by
    simpa only [h,halfPowerDualTest_norm_cube] using hvBound.2
  have hpair := lineConvolution_pairing K f (fun x => conj (h x)) hKi hKm
    f.integrable f.continuous.measurable (by fun_prop) (B+1)
    (fun x => by simpa only [Complex.norm_conj] using hhb x)
  have hleft : (∫ x, g x*conj (h x))=(J:ℂ) := by
    simp only [h,halfPowerDualTest_pair,integral_complex_ofReal]
    rfl
  have hright : (∫ x, f x*reverseLineConvolution K (fun y => conj (h y)) x)=
      -(∫ x, f x*conj (v x)) := by
    simp_rw [reverseLineConvolution_conj K h (sharpTimeKernel_odd r R)
      (sharpTimeKernel_conj r R),mul_neg,integral_neg]
    rfl
  have hidentity : (J:ℂ)= -(∫ x, f x*conj (v x)) := hleft.symm.trans (hpair.trans hright)
  have hnorm : J=‖∫ x, f x*conj (v x)‖ := by
    have hh := congrArg norm hidentity
    simpa only [Complex.norm_real,Real.norm_of_nonneg hJ,norm_neg] using hh
  have hhold := integral_mul_norm_le_Lp_mul_Lq (p:=3/2) (q:=3)
    (Real.holderConjugate_iff.mpr ⟨by norm_num,by norm_num⟩)
    (f.memLp (ENNReal.ofReal (3/2:ℝ)) volume) hv3
  have hi : J≤F^(2/3:ℝ)*(∫ x, ‖v x‖^3)^(1/3:ℝ) := by
    calc
      J = ‖∫ x, f x*conj (v x)‖ := hnorm
      _ ≤ ∫ x, ‖f x*conj (v x)‖ := norm_integral_le_integral_norm _
      _ = ∫ x, ‖f x‖*‖v x‖ := by simp only [norm_mul,Complex.norm_conj]
      _ ≤ _ := by simpa only [show (1/(3/2):ℝ)=2/3 by norm_num,Real.rpow_ofNat] using hhold
  refine ⟨hgi,?_⟩
  exact cubic_duality_estimate F J E hF hJ hE (hi.trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (integral_nonneg fun x => by positivity) hvEnergy (by norm_num))
      (Real.rpow_nonneg hF _)))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HorizontalHilbertProof
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The classical one-dimensional input required by the manuscript is
proved at the two required exponents. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert
open PacketRepresentation

theorem horizontalHilbertInput_proved : HorizontalHilbertInput := by
  obtain ⟨C,hC,hthree⟩ := sharpHilbert_uniform_three_halves
  obtain ⟨D,hD,hfour⟩ := sharpHilbert_uniform_fourth
  let B := C+D+1
  have hB : 0<B := by dsimp [B]; positivity
  have hCB : C≤B := by dsimp [B]; linarith
  have hDpow : D≤B^4 := by
    have hsmall : D≤(D+1)^4 := by nlinarith [sq_nonneg D,pow_nonneg hD 3,pow_nonneg hD 4]
    exact hsmall.trans (pow_le_pow_left₀ (by positivity) (by dsimp [B]; linarith) 4)
  refine ⟨B,hB,?_⟩
  intro p hp r R hr hrR f
  rcases hp with rfl | rfl
  · obtain ⟨hi,he⟩ := hthree r R hr hrR f
    refine ⟨hi,he.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hC.le hCB (by norm_num))
      (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _)
  · obtain ⟨hi,he⟩ := hfour r R hr hrR f
    simp only [Real.rpow_ofNat]
    refine ⟨hi,he.trans ?_⟩
    exact mul_le_mul_of_nonneg_right hDpow (integral_nonneg fun x => by positivity)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LepingleIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lépingle for disjoint intervals selected separately at each point. -/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace LipschitzHilbert

/-- Freezing a scalar martingale at a deterministic horizon preserves
the original filtration and the terminal value. -/
theorem martingale_freeze {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m} {F : ℕ → Ω → ℝ} (hF : Martingale F ℱ μ) (N : ℕ) :
    Martingale (fun n => F (min n N)) ℱ μ := by
  constructor
  · intro n
    exact (hF.stronglyMeasurable (min n N)).mono (ℱ.mono (min_le_left n N))
  · intro i j hij
    change μ[F (min j N) | ℱ i] =ᵐ[μ] F (min i N)
    by_cases hi : N ≤ i
    · have hj : N ≤ j := hi.trans hij
      simp only [min_eq_right hi, min_eq_right hj]
      exact Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable (ℱ.le i)
        ((hF.stronglyMeasurable N).mono (ℱ.mono hi)) (hF.integrable N))
    · have hiN : i ≤ N := (lt_of_not_ge hi).le
      rw [min_eq_left hiN]
      exact hF.condExp_ae_eq (le_min hij hiN)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MartingaleMaximalL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Doob's scalar finite-horizon L2 estimate, with its exact factor four,
for the dyadic averages used in the axis-parallel rectangle count. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert

theorem finiteMaxSignal_nonneg {Ω : Type*} (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    0 ≤ finiteMaxSignal F N x := by
  exact (abs_nonneg (F 0 x)).trans (Finset.le_sup' (fun i => |F i x|) (by simp))

theorem finiteMaxSignal_measurable {Ω : Type*} [MeasurableSpace Ω]
    (F : ℕ → Ω → ℝ) (N : ℕ) (hF : ∀ i ≤ N, Measurable (F i)) :
    Measurable (finiteMaxSignal F N) :=
  Finset.measurable_range_sup'' (fun i hi => by
    simpa only [Real.norm_eq_abs] using (hF i hi).norm)

theorem finiteMaxSignal_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : ℕ → Ω → ℝ) (N : ℕ) (hF : ∀ i, MemLp (F i) 2 μ) :
    MemLp (finiteMaxSignal F N) 2 μ := by
  induction N with
  | zero =>
    have heq : finiteMaxSignal F 0 = fun x => |F 0 x| := by
      funext x
      simp [finiteMaxSignal]
    rw [heq]
    simpa only [Real.norm_eq_abs] using (hF 0).norm
  | succ N ih =>
    have heq : finiteMaxSignal F (N+1) = (fun x => |F (N+1) x|) ⊔ finiteMaxSignal F N := by
      funext x
      have hh := Finset.sup'_insert (s := Finset.range (N+1)) (H := Finset.nonempty_range_add_one)
        (b := N+1) (f := fun i => |F i x|)
      simpa only [← Finset.range_add_one, finiteMaxSignal, Pi.sup_apply] using hh
    rw [heq]
    have hn : MemLp (fun x => |F (N+1) x|) 2 μ := by
      simpa only [Real.norm_eq_abs] using (hF (N+1)).norm
    exact hn.sup ih

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_StoppedMartingaleEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact quadratic energy for increasing bounded stopping times.
This supplies the jump-count energy in the scalar variation argument. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem conditionalExpectation_square_difference (m' : MeasurableSpace Ω) (hm : m' ≤ m)
    (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hgm : AEStronglyMeasurable[m'] g μ) (hcond : μ[f|m']=ᵐ[μ] g) :
    (∫ x, (f x-g x)^2 ∂μ)=(∫ x, f x^2 ∂μ)-(∫ x, g x^2 ∂μ) := by
  have hprod : Integrable (g*f) μ := hg.integrable_mul hf
  have hinner : (∫ x, g x*f x ∂μ)=∫ x, g x^2 ∂μ := by
    change (∫ x, (g*f) x ∂μ)=_
    rw [←integral_condExp hm (f:=g*f)]
    apply integral_congr_ae
    filter_upwards [condExp_mul_of_aestronglyMeasurable_left hgm hprod
      (hf.integrable (by norm_num)),hcond] with x hx hcx
    rw [hx]
    change g x*(μ[f|m']) x=g x^2
    rw [hcx]
    ring
  have he (x : Ω) : (f x-g x)^2=(f x^2+g x^2)-2*(g x*f x) := by ring
  simp_rw [he]
  change (∫ x, ((fun x => f x^2)+(fun x => g x^2)) x-2*(g*f) x ∂μ)=_
  rw [integral_sub (hf.integrable_sq.add hg.integrable_sq) (hprod.const_mul 2)]
  simp only [Pi.add_apply,Pi.mul_apply]
  rw [integral_add hf.integrable_sq hg.integrable_sq,integral_const_mul,hinner]
  ring

theorem stopped_martingale_square_difference {ℱ : Filtration ℕ m} {F : ℕ → Ω → ℝ}
    (hF : Martingale F ℱ μ) (hF2 : ∀ n, MemLp (F n) 2 μ)
    (σ τ : Ω → WithTop ℕ) (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ≤τ) (N : ℕ) (hτN : ∀ x, τ x≤N) :
    (∫ x, (stoppedValue F τ x-stoppedValue F σ x)^2 ∂μ)=
      (∫ x, (stoppedValue F τ x)^2 ∂μ)-(∫ x, (stoppedValue F σ x)^2 ∂μ) := by
  have hσN (x : Ω) : σ x≤N := (hστ x).trans (hτN x)
  have hσ2 := memLp_stoppedValue hσ hF2 hσN
  have hτ2 := memLp_stoppedValue hτ hF2 hτN
  have hσcond := hF.stoppedValue_ae_eq_condExp_of_le_const hσ hσN
  have hσm : AEStronglyMeasurable[hσ.measurableSpace] (stoppedValue F σ) μ :=
    stronglyMeasurable_condExp.aestronglyMeasurable.congr hσcond.symm
  exact conditionalExpectation_square_difference hσ.measurableSpace hσ.measurableSpace_le
    (stoppedValue F τ) (stoppedValue F σ) hτ2 hσ2 hσm
    (hF.stoppedValue_ae_eq_condExp_of_le hτ hσ hστ hτN).symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_StoppedMartingaleChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic energy and jump counts along any finite increasing chain
of bounded stopping times. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ m} {F : ℕ → Ω → ℝ}

theorem stopped_martingale_chain_identity (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (τ : ℕ → Ω → WithTop ℕ)
    (hτ : ∀ i, IsStoppingTime ℱ (τ i)) (hmono : ∀ i, τ i≤τ (i+1))
    (N J : ℕ) (hbound : ∀ i x, τ i x≤N) :
    (∑ i∈Finset.range J, ∫ x, (stoppedValue F (τ (i+1)) x-stoppedValue F (τ i) x)^2 ∂μ)=
      (∫ x, (stoppedValue F (τ J) x)^2 ∂μ)-(∫ x, (stoppedValue F (τ 0) x)^2 ∂μ) := by
  simp_rw [stopped_martingale_square_difference hF hF2 _ _ (hτ _) (hτ _) (hmono _) N (hbound _)]
  exact Finset.sum_range_sub (fun i => ∫ x, (stoppedValue F (τ i) x)^2 ∂μ) J

theorem stopped_martingale_terminal_energy (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (τ : Ω → WithTop ℕ)
    (hτ : IsStoppingTime ℱ τ) (N : ℕ) (hbound : ∀ x, τ x≤N) :
    (∫ x, (stoppedValue F τ x)^2 ∂μ)≤∫ x, F N x^2 ∂μ := by
  have hh := stopped_martingale_square_difference hF hF2 τ (fun _ => (N:WithTop ℕ))
    hτ (isStoppingTime_const ℱ N) hbound N (fun _ => le_rfl)
  change (∫ x, (F N x-stoppedValue F τ x)^2 ∂μ)=
    (∫ x, F N x^2 ∂μ)-(∫ x, (stoppedValue F τ x)^2 ∂μ) at hh
  have hnonneg : 0≤∫ x, (F N x-stoppedValue F τ x)^2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  linarith

theorem stopped_martingale_chain_energy (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (τ : ℕ → Ω → WithTop ℕ)
    (hτ : ∀ i, IsStoppingTime ℱ (τ i)) (hmono : ∀ i, τ i≤τ (i+1))
    (N J : ℕ) (hbound : ∀ i x, τ i x≤N) :
    (∑ i∈Finset.range J, ∫ x, (stoppedValue F (τ (i+1)) x-stoppedValue F (τ i) x)^2 ∂μ)≤
      ∫ x, F N x^2 ∂μ := by
  rw [stopped_martingale_chain_identity hF hF2 τ hτ hmono N J hbound]
  exact (sub_le_self _ (integral_nonneg fun x => sq_nonneg _)).trans
    (stopped_martingale_terminal_energy hF hF2 (τ J) (hτ J) N (hbound J))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RelativeMartingaleExits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative exits for the finite scalar specialization of Zorin-Kranich,
Bernoulli 26 (2020), Definition 2.1. The running radius is measured from
the initial value; the terminal time is one step beyond the path in use. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert

variable {Ω : Type*}

theorem runningOscillation_nonneg (F : ℕ → Ω → ℝ) (n : ℕ) (x : Ω) :
    0 ≤ runningOscillation F n x := finiteMaxSignal_nonneg _ _ _

theorem le_runningOscillation (F : ℕ → Ω → ℝ) {k n : ℕ} (h : k≤n) (x : Ω) :
    ‖F k x-F 0 x‖ ≤ runningOscillation F n x := by
  simpa only [runningOscillation,finiteMaxSignal,Real.norm_eq_abs] using
    (Finset.le_sup' (fun i => |F i x-F 0 x|) (show k∈Finset.range (n+1) by simp; omega))

theorem runningOscillation_le (F : ℕ → Ω → ℝ) (n : ℕ) (x : Ω) (A : ℝ)
    (h : ∀ k≤n, ‖F k x-F 0 x‖≤A) : runningOscillation F n x≤A := by
  unfold runningOscillation finiteMaxSignal
  apply Finset.sup'_le _
  intro k hk
  exact (Real.norm_eq_abs _).symm.trans_le (h k (by simpa using hk))

theorem runningOscillation_mono (F : ℕ → Ω → ℝ) {k n : ℕ} (h : k≤n) (x : Ω) :
    runningOscillation F k x ≤ runningOscillation F n x :=
  runningOscillation_le F k x _ (fun _ hi => le_runningOscillation F (hi.trans h) x)

theorem runningOscillation_adapted [m : MeasurableSpace Ω] {ℱ : Filtration ℕ m}
    (F : ℕ → Ω → ℝ) (hF : StronglyAdapted ℱ F) : Adapted ℱ (runningOscillation F) := by
  intro n
  change @Measurable Ω ℝ (ℱ n) _ (finiteMaxSignal (fun k y => F k y-F 0 y) n)
  apply @finiteMaxSignal_measurable Ω (ℱ n) (fun k y => F k y-F 0 y) n
  intro i hi
  exact (((hF i).mono (ℱ.mono hi)).sub ((hF 0).mono (ℱ.mono (Nat.zero_le n)))).measurable

theorem relativeNextExit_le (F : ℕ → Ω → ℝ) (a : ℝ) (H : ℕ) (σ : Ω → ℕ) (x : Ω) :
    relativeNextExit F a H σ x≤H := hittingBtwn_le x

theorem relativeNextExit_isStopping [m : MeasurableSpace Ω] {ℱ : Filtration ℕ m}
    (F : ℕ → Ω → ℝ) (hF : StronglyAdapted ℱ F) (a : ℝ) (H : ℕ) (σ : Ω → ℕ)
    (hσ : IsStoppingTime ℱ (fun x => (σ x:WithTop ℕ))) :
    IsStoppingTime ℱ (fun x => (relativeNextExit F a H σ x:WithTop ℕ)) := by
  apply Adapted.isStoppingTime_hittingBtwn (s:=Ioi 0) _ measurableSet_Ioi
  intro n
  have hs := hF.isStronglyProgressive_of_discrete.stronglyAdapted_stoppedProcess hσ n
  exact (((hF n).sub hs).norm.measurable).sub ((runningOscillation_adapted F hF n).const_mul a)

theorem relativeNextExit_ge (F : ℕ → Ω → ℝ) (a : ℝ) (ha : 0≤a)
    (H : ℕ) (σ : Ω → ℕ) (hσ : ∀ x, σ x≤H) (x : Ω) :
    σ x ≤ relativeNextExit F a H σ x := by
  by_contra hn
  have hlt : relativeNextExit F a H σ x<σ x := lt_of_not_ge hn
  have hh := hittingBtwn_mem_set_of_hittingBtwn_lt (hlt.trans_le (hσ x))
  have he : stoppedProcess F (fun y => (σ y:WithTop ℕ))
      (relativeNextExit F a H σ x) x=F (relativeNextExit F a H σ x) x := by
    unfold stoppedProcess
    rw [min_eq_left (by change (relativeNextExit F a H σ x:WithTop ℕ)≤(σ x:WithTop ℕ); exact_mod_cast hlt.le)]
    rfl
  change 0<‖F (relativeNextExit F a H σ x) x-
    stoppedProcess F (fun y => (σ y:WithTop ℕ)) (relativeNextExit F a H σ x) x‖-
      a*runningOscillation F (relativeNextExit F a H σ x) x at hh
  rw [he,sub_self,norm_zero] at hh
  have := mul_nonneg ha (runningOscillation_nonneg F (relativeNextExit F a H σ x) x)
  linarith

theorem relativeNextExit_before (F : ℕ → Ω → ℝ) (a : ℝ) (H : ℕ)
    (σ : Ω → ℕ) (x : Ω) (k : ℕ) (hσk : σ x≤k)
    (hk : k < relativeNextExit F a H σ x) :
    ‖F k x-F (σ x) x‖≤a*runningOscillation F k x := by
  have hh := notMem_of_lt_hittingBtwn (u:=fun n x =>
    ‖F n x-stoppedProcess F (fun y => (σ y:WithTop ℕ)) n x‖-
      a*runningOscillation F n x) (s:=Ioi 0) hk (Nat.zero_le k)
  have he : stoppedProcess F (fun y => (σ y:WithTop ℕ)) k x=F (σ x) x := by
    unfold stoppedProcess
    rw [min_eq_right (by change (σ x:WithTop ℕ)≤(k:WithTop ℕ); exact_mod_cast hσk)]
    rfl
  change ¬0<‖F k x-stoppedProcess F (fun y => (σ y:WithTop ℕ)) k x‖-
    a*runningOscillation F k x at hh
  rw [he] at hh
  linarith

theorem relativeNextExit_jump (F : ℕ → Ω → ℝ) (a : ℝ) (ha : 0≤a)
    (H : ℕ) (σ : Ω → ℕ) (hσ : ∀ x, σ x≤H) (x : Ω)
    (hlt : relativeNextExit F a H σ x<H) :
    a*runningOscillation F (relativeNextExit F a H σ x) x<
      ‖F (relativeNextExit F a H σ x) x-F (σ x) x‖ := by
  have hh := hittingBtwn_mem_set_of_hittingBtwn_lt hlt
  have hle := relativeNextExit_ge F a ha H σ hσ x
  have he : stoppedProcess F (fun y => (σ y:WithTop ℕ))
      (relativeNextExit F a H σ x) x=F (σ x) x := by
    unfold stoppedProcess
    rw [min_eq_right (by change (σ x:WithTop ℕ)≤(relativeNextExit F a H σ x:WithTop ℕ); exact_mod_cast hle)]
    rfl
  change 0<‖F (relativeNextExit F a H σ x) x-
    stoppedProcess F (fun y => (σ y:WithTop ℕ)) (relativeNextExit F a H σ x) x‖-
      a*runningOscillation F (relativeNextExit F a H σ x) x at hh
  rw [he] at hh
  linarith

theorem relativeExitTimes_le (F : ℕ → Ω → ℝ) (a : ℝ) (H i : ℕ) (x : Ω) :
    relativeExitTimes F a H i x≤H := by
  cases i with
  | zero => exact Nat.zero_le _
  | succ i => exact relativeNextExit_le F a H _ x

theorem relativeExitTimes_isStopping [m : MeasurableSpace Ω] {ℱ : Filtration ℕ m}
    (F : ℕ → Ω → ℝ) (hF : StronglyAdapted ℱ F) (a : ℝ) (H i : ℕ) :
    IsStoppingTime ℱ (fun x => (relativeExitTimes F a H i x:WithTop ℕ)) := by
  induction i with
  | zero => exact isStoppingTime_const ℱ 0
  | succ i ih => exact relativeNextExit_isStopping F hF a H _ ih

theorem relativeExitTimes_mono (F : ℕ → Ω → ℝ) (a : ℝ) (ha : 0≤a)
    (H : ℕ) (x : Ω) : Monotone (fun i => relativeExitTimes F a H i x) := by
  apply monotone_nat_of_le_succ
  intro i
  exact relativeNextExit_ge F a ha H _ (relativeExitTimes_le F a H i) x

theorem relativeExitTimes_min_le (F : ℕ → Ω → ℝ) (a : ℝ) (ha : 0≤a)
    (H i : ℕ) (x : Ω) : min i H ≤ relativeExitTimes F a H i x := by
  induction i with
  | zero => simp [relativeExitTimes]
  | succ i ih =>
    have hb := relativeExitTimes_le F a H (i+1) x
    by_cases hlt : relativeExitTimes F a H (i+1) x<H
    · have hj := relativeNextExit_jump F a ha H
        (relativeExitTimes F a H i) (relativeExitTimes_le F a H i) x hlt
      have hm : relativeExitTimes F a H i x ≤ relativeExitTimes F a H (i+1) x :=
        relativeExitTimes_mono F a ha H x (Nat.le_succ i)
      have hn : relativeExitTimes F a H i x≠relativeExitTimes F a H (i+1) x := by
        intro he
        change a*runningOscillation F (relativeExitTimes F a H (i+1) x) x<
          ‖F (relativeExitTimes F a H (i+1) x) x-F (relativeExitTimes F a H i x) x‖ at hj
        rw [he,sub_self,norm_zero] at hj
        have := mul_nonneg ha (runningOscillation_nonneg F (relativeExitTimes F a H (i+1) x) x)
        linarith
      omega
    · omega

theorem relativeExitTimes_terminal (F : ℕ → Ω → ℝ) (a : ℝ) (ha : 0≤a)
    (H : ℕ) (x : Ω) : relativeExitTimes F a H H x=H := by
  exact Nat.le_antisymm (relativeExitTimes_le F a H H x)
    (by simpa using relativeExitTimes_min_le F a ha H H x)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RelativeExitIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every sufficiently large interval crosses a relative exit whose jump
controls that interval. This is the finite, initial-value-radius version
of Zorin-Kranich, Bernoulli 26 (2020), Lemma 2.2. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert
variable {Ω : Type*}

theorem relativeExitTimes_last (F : ℕ → Ω → ℝ) (a : ℝ) (ha : 0≤a)
    (H b : ℕ) (hb : b<H) (x : Ω) :
    ∃ i<H, relativeExitTimes F a H i x≤b ∧ b < relativeExitTimes F a H (i+1) x := by
  have hex : ∃ i, b < relativeExitTimes F a H i x :=
    ⟨H,by simpa only [relativeExitTimes_terminal F a ha H x] using hb⟩
  have hq := Nat.find_spec hex
  have hqpos : 0<Nat.find hex := by
    apply (Nat.find_pos hex).2
    simp [relativeExitTimes]
  have hqH : Nat.find hex≤H := Nat.find_min' hex (by
    simpa only [relativeExitTimes_terminal F a ha H x] using hb)
  refine ⟨Nat.find hex-1, by omega, ?_, ?_⟩
  · exact le_of_not_gt (Nat.find_min hex (by omega))
  · simpa only [Nat.sub_add_cancel hqpos] using hq

theorem runningOscillation_at_last_exit (F : ℕ → Ω → ℝ) (a : ℝ)
    (ha : 0≤a) (ha2 : a≤1/2) (H b i : ℕ) (x : Ω)
    (_hleft : relativeExitTimes F a H i x≤b)
    (hright : b < relativeExitTimes F a H (i+1) x) :
    runningOscillation F b x≤2*runningOscillation F (relativeExitTimes F a H i x) x := by
  have hmax : runningOscillation F b x≤
      runningOscillation F (relativeExitTimes F a H i x) x+a*runningOscillation F b x := by
    apply runningOscillation_le
    intro k hk
    by_cases hki : k ≤ relativeExitTimes F a H i x
    · exact (le_runningOscillation F hki x).trans
        (le_add_of_nonneg_right (mul_nonneg ha (runningOscillation_nonneg F b x)))
    · have hik : relativeExitTimes F a H i x≤k := (lt_of_not_ge hki).le
      have hsmall := relativeNextExit_before F a H (relativeExitTimes F a H i) x k hik
        (hk.trans_lt hright)
      have hmono := mul_le_mul_of_nonneg_left (runningOscillation_mono F hk x) ha
      calc
        ‖F k x-F 0 x‖ ≤ ‖F k x-F (relativeExitTimes F a H i x) x‖+
            ‖F (relativeExitTimes F a H i x) x-F 0 x‖ := by simpa only [dist_eq_norm] using dist_triangle (F k x) (F (relativeExitTimes F a H i x) x) (F 0 x)
        _ ≤ a*runningOscillation F b x+runningOscillation F (relativeExitTimes F a H i x) x :=
          add_le_add (hsmall.trans hmono) (le_runningOscillation F le_rfl x)
        _ = _ := add_comm _ _
  have hprod := mul_le_mul_of_nonneg_right ha2 (runningOscillation_nonneg F b x)
  linarith

theorem relative_interval_crosses_exit (F : ℕ → Ω → ℝ) (a : ℝ)
    (ha : 0≤a) (ha2 : a≤1/2) (H l b : ℕ) (hb : b<H) (hlb : l≤b) (x : Ω)
    (hlarge : 2*a*runningOscillation F b x<‖F b x-F l x‖)
    (hupper : ‖F b x-F l x‖≤8*a*runningOscillation F b x) :
    ∃ j<H, l < relativeExitTimes F a H (j+1) x ∧
      relativeExitTimes F a H (j+1) x≤b ∧
      ‖F b x-F l x‖≤16*‖F (relativeExitTimes F a H (j+1) x) x-
        F (relativeExitTimes F a H j x) x‖ := by
  obtain ⟨i,hiH,his,hit⟩ := relativeExitTimes_last F a ha H b hb x
  have hli : l < relativeExitTimes F a H i x := by
    by_contra hn
    have hil : relativeExitTimes F a H i x≤l := le_of_not_gt hn
    have hs1 := relativeNextExit_before F a H (relativeExitTimes F a H i) x l hil
      (hlb.trans_lt hit)
    have hs2 := relativeNextExit_before F a H (relativeExitTimes F a H i) x b his hit
    have hrad := mul_le_mul_of_nonneg_left (runningOscillation_mono F hlb x) ha
    have htri : ‖F b x-F l x‖≤‖F b x-F (relativeExitTimes F a H i x) x‖+
        ‖F l x-F (relativeExitTimes F a H i x) x‖ := by
      simpa only [norm_sub_rev (F (relativeExitTimes F a H i x) x) (F l x)] using
        (show ‖F b x-F l x‖≤‖F b x-F (relativeExitTimes F a H i x) x‖+
          ‖F (relativeExitTimes F a H i x) x-F l x‖ by
          simpa only [dist_eq_norm] using dist_triangle (F b x) (F (relativeExitTimes F a H i x) x) (F l x))
    nlinarith
  have hipos : 0 < i := by
    by_contra hn
    have : i=0 := by omega
    simp [this,relativeExitTimes] at hli
  let j := i-1
  have hji : j+1=i := by dsimp [j]; omega
  have hjH : j<H := by dsimp [j]; omega
  have hjump := relativeNextExit_jump F a ha H (relativeExitTimes F a H j)
    (relativeExitTimes_le F a H j) x (by
      change relativeExitTimes F a H (j+1) x<H
      rw [hji]
      exact his.trans_lt hb)
  change a*runningOscillation F (relativeExitTimes F a H (j+1) x) x<
    ‖F (relativeExitTimes F a H (j+1) x) x-F (relativeExitTimes F a H j x) x‖ at hjump
  have hrad := runningOscillation_at_last_exit F a ha ha2 H b i x his hit
  rw [←hji] at hrad
  refine ⟨j,hjH,by simpa only [hji] using hli,by simpa only [hji] using his,?_⟩
  have hm := mul_le_mul_of_nonneg_left hrad ha
  nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RelativeExitScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic selection of the relative exit scale for each nonzero interval. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert

theorem relativeExitScale_pos (m : ℕ) : 0 < relativeExitScale m := by
  unfold relativeExitScale
  positivity

theorem relativeExitScale_le (m : ℕ) : relativeExitScale m≤1/4 := by
  unfold relativeExitScale
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num) (n:=m))
    (by norm_num)).trans_eq (mul_one _)

theorem relativeExitScale_succ (m : ℕ) : relativeExitScale m=2*relativeExitScale (m+1) := by
  unfold relativeExitScale
  rw [pow_succ]
  ring

theorem exists_relativeExitScale {d R : ℝ} (hd : 0<d) (hR : 0≤R) (hdR : d≤2*R) :
    ∃ m : ℕ, 2*relativeExitScale m*R<d ∧ d≤8*relativeExitScale m*R := by
  have hRpos : 0<R := by linarith
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (show 0<2*d/R by positivity) (show (1:ℝ)/2<1 by norm_num)
  have hex : ∃ m, 2*relativeExitScale m*R<d := by
    refine ⟨n,?_⟩
    have ht : (1/2:ℝ)^n*R<2*d := (lt_div_iff₀ hRpos).mp hn
    unfold relativeExitScale
    nlinarith
  refine ⟨Nat.find hex,Nat.find_spec hex,?_⟩
  cases h : Nat.find hex with
  | zero => norm_num [relativeExitScale]; exact hdR
  | succ m =>
    have hn := Nat.find_min hex (show m<Nat.find hex by omega)
    have hs := relativeExitScale_succ m
    have hp := relativeExitScale_pos (m+1)
    nlinarith

variable {Ω : Type*}

theorem relative_interval_scale (F : ℕ → Ω → ℝ) (H l b : ℕ) (hb : b<H)
    (hlb : l≤b) (x : Ω) (hd : 0<‖F b x-F l x‖) :
    ∃ m j : ℕ, j<H ∧ l < relativeExitTimes F (relativeExitScale m) H (j+1) x ∧
      relativeExitTimes F (relativeExitScale m) H (j+1) x≤b ∧
      ‖F b x-F l x‖^3≤2048*relativeExitScale m*runningOscillation F b x*
        ‖F (relativeExitTimes F (relativeExitScale m) H (j+1) x) x-
          F (relativeExitTimes F (relativeExitScale m) H j x) x‖^2 := by
  have hdiam : ‖F b x-F l x‖≤2*runningOscillation F b x := by
    have h1 := le_runningOscillation F (le_refl b) x
    have h2 := le_runningOscillation F hlb x
    have ht : ‖F b x-F l x‖≤‖F b x-F 0 x‖+‖F l x-F 0 x‖ := by
      simpa only [norm_sub_rev (F 0 x) (F l x)] using (show ‖F b x-F l x‖≤‖F b x-F 0 x‖+‖F 0 x-F l x‖ by
        simpa only [dist_eq_norm] using dist_triangle (F b x) (F 0 x) (F l x))
    linarith
  obtain ⟨m,hm1,hm2⟩ := exists_relativeExitScale hd (runningOscillation_nonneg F b x) hdiam
  obtain ⟨j,hj,hl,hb',hjump⟩ := relative_interval_crosses_exit F (relativeExitScale m)
    (relativeExitScale_pos m).le ((relativeExitScale_le m).trans (by norm_num)) H l b hb hlb x hm1 hm2
  refine ⟨m,j,hj,hl,hb',?_⟩
  have hsq : ‖F b x-F l x‖^2≤256*
      ‖F (relativeExitTimes F (relativeExitScale m) H (j+1) x) x-
        F (relativeExitTimes F (relativeExitScale m) H j x) x‖^2 := by
    have hp := norm_nonneg (F b x-F l x)
    have hq := norm_nonneg (F (relativeExitTimes F (relativeExitScale m) H (j+1) x) x-
      F (relativeExitTimes F (relativeExitScale m) H j x) x)
    nlinarith
  calc
    _ = ‖F b x-F l x‖*‖F b x-F l x‖^2 := by ring
    _ ≤ (8*relativeExitScale m*runningOscillation F b x)*
        (256*‖F (relativeExitTimes F (relativeExitScale m) H (j+1) x) x-
          F (relativeExitTimes F (relativeExitScale m) H j x) x‖^2) :=
      mul_le_mul hm2 hsq (sq_nonneg _) (by
        have := relativeExitScale_pos m
        have := runningOscillation_nonneg F b x
        positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RelativeExitEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable quadratic energies of the relative sampled martingales. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert
variable {Ω : Type*}

theorem relativeExitEnergy_nonneg (F : ℕ → Ω → ℝ) (a : ℝ) (H : ℕ) (x : Ω) :
    0 ≤ relativeExitEnergy F a H x := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem relativeExitEnergy_bound (F : ℕ → Ω → ℝ) (a : ℝ) (H : ℕ) (x : Ω) :
    relativeExitEnergy F a H x≤4*(H:ℝ)*(runningOscillation F H x)^2 := by
  have hb (j : Fin H) : ‖F (relativeExitTimes F a H (j.val+1) x) x-
      F (relativeExitTimes F a H j.val x) x‖≤2*runningOscillation F H x := by
    have h1 := le_runningOscillation F (relativeExitTimes_le F a H (j.val+1) x) x
    have h2 := le_runningOscillation F (relativeExitTimes_le F a H j.val x) x
    have ht := dist_triangle (F (relativeExitTimes F a H (j.val+1) x) x) (F 0 x)
      (F (relativeExitTimes F a H j.val x) x)
    simp only [dist_eq_norm] at ht
    rw [norm_sub_rev (F 0 x)] at ht
    linarith
  calc
    _ ≤ ∑ _j : Fin H, 4*(runningOscillation F H x)^2 := by
      apply Finset.sum_le_sum
      intro j _
      have h := hb j
      have hn := norm_nonneg (F (relativeExitTimes F a H (j.val+1) x) x-
        F (relativeExitTimes F a H j.val x) x)
      nlinarith
    _ = _ := by simp; ring

theorem relativeExitScale_summable : Summable relativeExitScale :=
  summable_geometric_two.mul_left (1/4)

theorem relativeExitScale_tsum : ∑' m, relativeExitScale m=1/2 := by
  change (∑' m, (1/4:ℝ)*(1/2)^m)=1/2
  rw [tsum_mul_left,tsum_geometric_two]
  norm_num

theorem relativeExitEnergy_summable (F : ℕ → Ω → ℝ) (H : ℕ) (x : Ω) :
    Summable (fun m => relativeExitScale m*relativeExitEnergy F (relativeExitScale m) H x) := by
  apply Summable.of_nonneg_of_le
    (fun m => mul_nonneg (relativeExitScale_pos m).le (relativeExitEnergy_nonneg F _ H x))
    (fun m => mul_le_mul_of_nonneg_left (relativeExitEnergy_bound F _ H x) (relativeExitScale_pos m).le)
  exact relativeExitScale_summable.mul_right _

theorem weightedRelativeExitEnergy_nonneg (F : ℕ → Ω → ℝ) (H : ℕ) (x : Ω) :
    0≤weightedRelativeExitEnergy F H x :=
  tsum_nonneg fun m => mul_nonneg (relativeExitScale_pos m).le (relativeExitEnergy_nonneg F _ H x)

theorem weightedRelativeExitEnergy_bound (F : ℕ → Ω → ℝ) (H : ℕ) (x : Ω) :
    weightedRelativeExitEnergy F H x≤2*(H:ℝ)*(runningOscillation F H x)^2 := by
  calc
    _ ≤ ∑' m, relativeExitScale m*(4*(H:ℝ)*(runningOscillation F H x)^2) :=
      Summable.tsum_le_tsum
        (fun m => mul_le_mul_of_nonneg_left (relativeExitEnergy_bound F _ H x) (relativeExitScale_pos m).le)
        (relativeExitEnergy_summable F H x) (relativeExitScale_summable.mul_right _)
    _ = _ := by rw [tsum_mul_right,relativeExitScale_tsum]; ring

section Measure
variable [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ m} {F : ℕ → Ω → ℝ}

theorem relativeExitEnergy_measurable (hF : StronglyAdapted ℱ F) (a : ℝ) (H : ℕ) :
    Measurable (relativeExitEnergy F a H) := by
  have hs (j : ℕ) : Measurable (fun x => F (relativeExitTimes F a H j x) x) := by
    have ht := stronglyMeasurable_stoppedValue_of_le hF.isStronglyProgressive_of_discrete
      (relativeExitTimes_isStopping F hF a H j) (fun x => by
        change (relativeExitTimes F a H j x:WithTop ℕ)≤(H:WithTop ℕ)
        exact_mod_cast relativeExitTimes_le F a H j x)
    exact (ht.mono (ℱ.le H)).measurable
  exact Finset.measurable_sum _ (fun j _ => ((hs (j.val+1)).sub (hs j.val)).norm.pow_const 2)

omit [IsFiniteMeasure μ] in
theorem relativeExitEnergy_integrable (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (a : ℝ) (H : ℕ) :
    Integrable (relativeExitEnergy F a H) μ := by
  have hs (j : ℕ) : MemLp (fun x => F (relativeExitTimes F a H j x) x) 2 μ :=
    memLp_stoppedValue (relativeExitTimes_isStopping F hF.1 a H j) hF2 (fun x => by
      change (relativeExitTimes F a H j x:WithTop ℕ)≤(H:WithTop ℕ)
      exact_mod_cast relativeExitTimes_le F a H j x)
  apply integrable_finsetSum
  intro j _
  have hi := ((hs (j.val+1)).sub (hs j.val)).integrable_sq
  convert hi using 1 <;> first | (with_reducible_and_instances rfl) | (ext x; simp [Real.norm_eq_abs,sq_abs,Pi.sub_apply])

theorem relativeExitEnergy_integral_le (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (a : ℝ) (ha : 0≤a) (H : ℕ) :
    (∫ x, relativeExitEnergy F a H x ∂μ)≤∫ x, F H x^2 ∂μ := by
  let τ := fun j x => (relativeExitTimes F a H j x:WithTop ℕ)
  have ht (j : ℕ) : IsStoppingTime ℱ (τ j) := relativeExitTimes_isStopping F hF.1 a H j
  have hm (j : ℕ) : τ j≤τ (j+1) := fun x => by
    change (relativeExitTimes F a H j x:WithTop ℕ)≤(relativeExitTimes F a H (j+1) x:WithTop ℕ)
    exact_mod_cast relativeExitTimes_mono F a ha H x (Nat.le_succ j)
  have hb (j : ℕ) (x : Ω) : τ j x≤H := by
    change (relativeExitTimes F a H j x:WithTop ℕ)≤(H:WithTop ℕ)
    exact_mod_cast relativeExitTimes_le F a H j x
  have he := stopped_martingale_chain_energy hF hF2 τ ht hm H H hb
  have hs (j : Fin H) : Integrable (fun x =>
      ‖F (relativeExitTimes F a H (j.val+1) x) x-F (relativeExitTimes F a H j.val x) x‖^2) μ := by
    have hi :=
      ((memLp_stoppedValue (ht (j.val+1)) hF2 (hb (j.val+1))).sub
        (memLp_stoppedValue (ht j.val) hF2 (hb j.val))).integrable_sq
    change Integrable (fun x => (F (relativeExitTimes F a H (j.val+1) x) x-
      F (relativeExitTimes F a H j.val x) x)^2) μ at hi
    simpa only [Real.norm_eq_abs,sq_abs] using hi
  change (∫ x, ∑ j : Fin H, ‖F (relativeExitTimes F a H (j.val+1) x) x-
    F (relativeExitTimes F a H j.val x) x‖^2 ∂μ)≤_
  rw [integral_finsetSum _ (fun j _ => hs j)]
  change (∑ i∈Finset.range H, ∫ x, (F (relativeExitTimes F a H (i+1) x) x-
    F (relativeExitTimes F a H i x) x)^2 ∂μ)≤_ at he
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∫ x, (F (relativeExitTimes F a H (i+1) x) x-
    F (relativeExitTimes F a H i x) x)^2 ∂μ) H] at he
  simpa only [Real.norm_eq_abs,sq_abs] using he


theorem weightedRelativeExitEnergy_measurable (hF : StronglyAdapted ℱ F) (H : ℕ) :
    Measurable (weightedRelativeExitEnergy F H) :=
  Measurable.tsum (fun k => (relativeExitEnergy_measurable hF (relativeExitScale k) H).const_mul _)

omit [IsFiniteMeasure μ] in
theorem weightedRelativeExitEnergy_integrable (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (H : ℕ) :
    Integrable (weightedRelativeExitEnergy F H) μ := by
  have hr : MemLp (runningOscillation F H) 2 μ :=
    finiteMaxSignal_memLp μ _ H (fun n => (hF2 n).sub (hF2 0))
  apply (hr.integrable_sq.const_mul (2*(H:ℝ))).mono'
    (weightedRelativeExitEnergy_measurable hF.1 H).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (weightedRelativeExitEnergy_nonneg F H x)]
  exact weightedRelativeExitEnergy_bound F H x

theorem weightedRelativeExitEnergy_integral_le (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (H : ℕ) :
    (∫ x, weightedRelativeExitEnergy F H x ∂μ)≤(1/2)*(∫ x, F H x^2 ∂μ) := by
  let G := fun k x => relativeExitScale k*relativeExitEnergy F (relativeExitScale k) H x
  have hg (k : ℕ) : Integrable (G k) μ :=
    (relativeExitEnergy_integrable hF hF2 (relativeExitScale k) H).const_mul _
  have hgn (k : ℕ) (x : Ω) : 0≤G k x :=
    mul_nonneg (relativeExitScale_pos k).le (relativeExitEnergy_nonneg F _ H x)
  have hle (k : ℕ) : (∫ x, G k x ∂μ) ≤ relativeExitScale k*(∫ x, F H x^2 ∂μ) := by
    rw [show (∫ x, G k x ∂μ)=relativeExitScale k*(∫ x, relativeExitEnergy F (relativeExitScale k) H x ∂μ)
      from integral_const_mul _ _]
    exact mul_le_mul_of_nonneg_left (relativeExitEnergy_integral_le hF hF2 _ (relativeExitScale_pos k).le H)
      (relativeExitScale_pos k).le
  have hs : Summable (fun k => ∫ x, G k x ∂μ) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg (hgn k)) hle
      (relativeExitScale_summable.mul_right _)
  have hsn : Summable (fun k => ∫ x, ‖G k x‖ ∂μ) := by
    simpa only [Real.norm_of_nonneg (hgn _ _)] using hs
  change (∫ x, ∑' k, G k x ∂μ)≤_
  rw [← integral_tsum_of_summable_integral_norm hg hsn]
  calc
    _ ≤ ∑' k, relativeExitScale k*(∫ x, F H x^2 ∂μ) :=
      Summable.tsum_le_tsum hle hs (relativeExitScale_summable.mul_right _)
    _ = _ := by rw [tsum_mul_right,relativeExitScale_tsum]

end Measure
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RelativePartitionVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite partitions are dominated by the summed quadratic relative-exit energies. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert
variable {Ω : Type*}

theorem relative_partition_cube_bound (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω)
    (p : Fin (N+1) → Fin (N+1)) (hp : Monotone p) :
    (∑ i : Fin N, ‖F (p i.succ) x-F (p i.castSucc) x‖^3) ≤
      2048*runningOscillation F N x*weightedRelativeExitEnergy F (N+1) x := by
  classical
  let d := fun i : Fin N => ‖F (p i.succ) x-F (p i.castSucc) x‖
  let s : Finset (Fin N) := Finset.univ.filter (fun i => 0<d i)
  have he (i : Fin N) (hi : i∈s) : ∃ q : ℕ × Fin (N+1),
      (p i.castSucc).val < relativeExitTimes F (relativeExitScale q.1) (N+1) (q.2.val+1) x ∧
      relativeExitTimes F (relativeExitScale q.1) (N+1) (q.2.val+1) x ≤ (p i.succ).val ∧
      d i^3 ≤ 2048*runningOscillation F N x*(relativeExitScale q.1*
        ‖F (relativeExitTimes F (relativeExitScale q.1) (N+1) (q.2.val+1) x) x-
          F (relativeExitTimes F (relativeExitScale q.1) (N+1) q.2.val x) x‖^2) := by
    have hd : 0<d i := (Finset.mem_filter.mp hi).2
    obtain ⟨m,j,hj,hl,hb,hv⟩ := relative_interval_scale F (N+1) (p i.castSucc) (p i.succ)
      (p i.succ).isLt (hp (show i.castSucc  ≤  i.succ by change i.val ≤ i.val+1; omega)) x hd
    refine ⟨(m,⟨j,hj⟩),hl,hb,?_⟩
    have hrad := runningOscillation_mono F (Nat.le_of_lt_succ (p i.succ).isLt) x
    have hs := relativeExitScale_pos m
    have hn := sq_nonneg ‖F (relativeExitTimes F (relativeExitScale m) (N+1) (j+1) x) x-
      F (relativeExitTimes F (relativeExitScale m) (N+1) j x) x‖
    calc
      _  ≤  _ := hv
      _ = (2048*relativeExitScale m*
          ‖F (relativeExitTimes F (relativeExitScale m) (N+1) (j+1) x) x-
            F (relativeExitTimes F (relativeExitScale m) (N+1) j x) x‖^2)*
              runningOscillation F (p i.succ) x := by ring
      _  ≤  (2048*relativeExitScale m*
          ‖F (relativeExitTimes F (relativeExitScale m) (N+1) (j+1) x) x-
            F (relativeExitTimes F (relativeExitScale m) (N+1) j x) x‖^2)*
              runningOscillation F N x := mul_le_mul_of_nonneg_left hrad (by positivity)
      _ = _ := by ring
  let q : Fin N → ℕ × Fin (N+1) := fun i => if hi : i∈s then Classical.choose (he i hi) else (0,0)
  have hq (i : Fin N) (hi : i∈s) := Classical.choose_spec (he i hi)
  have hqp (i : Fin N) (hi : i∈s) :
      (p i.castSucc).val < relativeExitTimes F (relativeExitScale (q i).1) (N+1) ((q i).2.val+1) x ∧
      relativeExitTimes F (relativeExitScale (q i).1) (N+1) ((q i).2.val+1) x ≤ (p i.succ).val ∧
      d i^3 ≤ 2048*runningOscillation F N x*(relativeExitScale (q i).1*
        ‖F (relativeExitTimes F (relativeExitScale (q i).1) (N+1) ((q i).2.val+1) x) x-
          F (relativeExitTimes F (relativeExitScale (q i).1) (N+1) (q i).2.val x) x‖^2) := by
    simpa only [q,dite_eq_left hi] using hq i hi
  have horder (i k : Fin N) (hik : i<k) : (p i.succ).val ≤ (p k.castSucc).val :=
    hp (show i.succ ≤ k.castSucc by change i.val+1 ≤ k.val; exact hik)
  have hqinj : Set.InjOn q s := by
    intro i hi k hk heq
    rcases lt_trichotomy i k with hik | hik | hki
    · have h1 := (hqp i hi).2.1
      have h2 := (hqp k hk).1
      rw [←heq] at h2
      have h3 := horder i k hik
      omega
    · exact hik
    · have h1 := (hqp k hk).2.1
      have h2 := (hqp i hi).1
      rw [heq] at h2
      have h3 := horder k i hki
      omega
  let M := s.sup (fun i => (q i).1)+1
  let w := fun z : ℕ × Fin (N+1) => relativeExitScale z.1*
    ‖F (relativeExitTimes F (relativeExitScale z.1) (N+1) (z.2.val+1) x) x-
      F (relativeExitTimes F (relativeExitScale z.1) (N+1) z.2.val x) x‖^2
  have hsum : (∑ i∈s,d i^3) ≤
      ∑ z∈(Finset.range M).product Finset.univ, 2048*runningOscillation F N x*w z := by
    apply OAI.sum_le_sum_of_injOn q hqinj
    · intro z hz
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
      rw [Finset.product_eq_sprod]
      simp only [Finset.mem_product,Finset.mem_range,Finset.mem_univ,and_true]
      exact Nat.lt_succ_of_le (Finset.le_sup (f:=fun i => (q i).1) hi)
    · exact fun i hi => (hqp i hi).2.2
    · intro z _ _
      exact mul_nonneg (mul_nonneg (by norm_num) (runningOscillation_nonneg F N x))
        (mul_nonneg (relativeExitScale_pos z.1).le (sq_nonneg _))
  have hsumeq : (∑ i∈s, d i^3)=∑ i : Fin N,d i^3 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hd : ¬0<d i := by simpa only [s,Finset.mem_filter,Finset.mem_univ,true_and] using hi
    have hdn : 0 ≤ d i := norm_nonneg _
    have : d i=0 := le_antisymm (le_of_not_gt hd) hdn
    simp only [this,zero_pow (by decide : 3≠0)]
  rw [hsumeq] at hsum
  calc
    _  ≤  _ := hsum
    _ = 2048*runningOscillation F N x*
        (∑ m∈Finset.range M, relativeExitScale m*relativeExitEnergy F (relativeExitScale m) (N+1) x) := by
      rw [Finset.product_eq_sprod,Finset.sum_product]
      simp only [w,relativeExitEnergy,←Finset.mul_sum]
    _  ≤  _ := mul_le_mul_of_nonneg_left
      ((relativeExitEnergy_summable F (N+1) x).sum_le_tsum (Finset.range M)
        (fun m _ => mul_nonneg (relativeExitScale_pos m).le (relativeExitEnergy_nonneg F _ _ x)))
      (mul_nonneg (by norm_num) (runningOscillation_nonneg F N x))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RealFiniteVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real-valued finite variation and cancellation of the running radius
in the pathwise relative-exit estimate. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert
variable {Ω : Type*}

theorem realVariationCube_nonneg (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    0 ≤ realVariationCube F N x := finiteCubicVariation_nonneg _ _

theorem partition_le_realVariationCube (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω)
    (p : Fin (N+1) → Fin (N+1)) (hp : Monotone p) :
    (∑ i : Fin N, ‖F (p i.succ) x-F (p i.castSucc) x‖^3) ≤ realVariationCube F N x :=
  partition_le_finiteCubicVariation (E:=ℝ) (fun n => F n x) N p hp

theorem realVariationCube_relative_bound (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    realVariationCube F N x≤2048*runningOscillation F N x*weightedRelativeExitEnergy F (N+1) x := by
  classical
  unfold realVariationCube finiteCubicVariation
  apply Finset.sup'_le _
  intro p _
  split_ifs with hp
  · exact relative_partition_cube_bound F N x p hp
  · exact mul_nonneg (mul_nonneg (by norm_num) (runningOscillation_nonneg F N x))
      (weightedRelativeExitEnergy_nonneg F (N+1) x)

theorem initial_jump_le_realVariationCube (F : ℕ → Ω → ℝ) (N k : ℕ) (hk : k≤N) (x : Ω) :
    ‖F k x-F 0 x‖^3 ≤ realVariationCube F N x := by
  classical
  by_cases hN : N=0
  · have hk0 : k=0 := by omega
    simpa [hk0] using realVariationCube_nonneg F N x
  have hNpos : 0<N := Nat.pos_of_ne_zero hN
  let p : Fin (N+1) → Fin (N+1) := fun i => if i.val=0 then 0 else ⟨k,Nat.lt_succ_of_le hk⟩
  have hp : Monotone p := by
    intro i j hij
    dsimp [p]
    split_ifs with hi hj
    · exact le_rfl
    · exact Fin.zero_le _
    · have : j.val≠0 := by intro hj; have := hij; change i.val≤j.val at this; omega
      contradiction
    · exact le_rfl
  have hterm : (∑ i : Fin N, ‖F (p i.succ) x-F (p i.castSucc) x‖^3)≥‖F k x-F 0 x‖^3 := by
    have h := Finset.single_le_sum (f:=fun i : Fin N => ‖F (p i.succ) x-F (p i.castSucc) x‖^3)
      (fun i _ => pow_nonneg (norm_nonneg _) _) (Finset.mem_univ (⟨0,hNpos⟩:Fin N))
    simpa [p] using h
  exact hterm.trans (partition_le_realVariationCube F N x p hp)

theorem runningOscillation_cube_le (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    runningOscillation F N x^3 ≤ realVariationCube F N x := by
  obtain ⟨k,hk,he⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
    (fun i => |F i x-F 0 x|)
  change (Finset.range (N+1)).sup' Finset.nonempty_range_add_one (fun i => |F i x-F 0 x|)^3≤_
  rw [he]
  simpa only [Real.norm_eq_abs] using initial_jump_le_realVariationCube F N k (by simpa using hk) x

theorem cubic_radius_cancel (V R W : ℝ) (hV : 0≤V) (hR : 0≤R) (hW : 0≤W)
    (h1 : V≤2048*R*W) (h2 : R^3≤V) : V^(2/3:ℝ)≤2048*W := by
  let v := V^(1/3:ℝ)
  have hv : 0≤v := Real.rpow_nonneg hV _
  have hv3 : v^3=V := by
    dsimp [v]
    rw [←Real.rpow_natCast,←Real.rpow_mul hV]
    norm_num
  have hv2 : v^2=V^(2/3:ℝ) := by
    dsimp [v]
    rw [←Real.rpow_natCast,←Real.rpow_mul hV]
    norm_num
  have hRv : R≤v := by
    by_contra hn
    have hlt : v<R := lt_of_not_ge hn
    have hc : v^3<R^3 := (pow_lt_pow_iff_left₀ hv hR (by decide : (3:ℕ)≠0)).2 hlt
    linarith
  by_cases hv0 : v=0
  · rw [←hv2,hv0]
    norm_num
    exact hW
  have hvp : 0<v := lt_of_le_of_ne hv (Ne.symm hv0)
  have h3 := mul_le_mul_of_nonneg_right hRv (mul_nonneg (by norm_num : (0:ℝ)≤2048) hW)
  rw [←hv2]
  by_contra hn
  have hbad := mul_pos hvp (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith

theorem realVariationCube_two_thirds_bound (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    realVariationCube F N x^(2/3:ℝ)≤2048*weightedRelativeExitEnergy F (N+1) x :=
  cubic_radius_cancel _ _ _ (realVariationCube_nonneg F N x) (runningOscillation_nonneg F N x)
    (weightedRelativeExitEnergy_nonneg F (N+1) x) (realVariationCube_relative_bound F N x)
    (runningOscillation_cube_le F N x)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LepingleProof
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite, scalar, unweighted p=2, r=3 specialization of
Zorin-Kranich, Bernoulli 26 (2020), Theorem 1.1. The proof uses the
relative stopping-time construction of Section 2 and quadratic energy;
no weighted inequality or further published premise is needed. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal
namespace LipschitzHilbert
variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ m} {F : ℕ → Ω → ℝ}

omit m in
theorem variationCube_relative_energy (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    variationCube F N x^(2/3:ℝ)≤
      ENNReal.ofReal (2048*weightedRelativeExitEnergy F (N+1) x) := by
  rw [←scalar_finiteCubicVariation]
  rw [ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (realVariationCube_two_thirds_bound F N x)

omit m in
theorem variationCube_freeze (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    variationCube (fun n => F (min n N)) N x=variationCube F N x := by
  classical
  unfold variationCube
  congr 1
  funext p
  split_ifs
  · apply Finset.sum_congr rfl
    intro i _
    dsimp only
    rw [min_eq_left (Nat.le_of_lt_succ (p i.succ).isLt),
      min_eq_left (Nat.le_of_lt_succ (p i.castSucc).isLt)]
  · rfl

theorem martingale_variation_L2 (hF : Martingale F ℱ μ) (hF2 : ∀ n, MemLp (F n) 2 μ)
    (N : ℕ) :
    (∫⁻ x, variationCube F N x^(2/3:ℝ) ∂μ)≤(1024:ℝ≥0∞)*squareIntegral μ (F N) := by
  let G := fun n => F (min n N)
  have hG : Martingale G ℱ μ := martingale_freeze hF N
  have hG2 : ∀ n, MemLp (G n) 2 μ := fun n => hF2 (min n N)
  have hW := weightedRelativeExitEnergy_integrable hG hG2 (N+1)
  have hWn := weightedRelativeExitEnergy_nonneg G (N+1)
  have hWi := weightedRelativeExitEnergy_integral_le hG hG2 (N+1)
  have heW := ofReal_integral_eq_lintegral_ofReal hW (Filter.Eventually.of_forall hWn)
  have heF := ofReal_integral_eq_lintegral_ofReal (hF2 N).integrable_sq
    (Filter.Eventually.of_forall (fun x => sq_nonneg (F N x)))
  have heFn : (∫⁻ x, ENNReal.ofReal (F N x^2) ∂μ)=squareIntegral μ (F N) := by
    apply lintegral_congr
    intro x
    rw [←sq_abs,←Real.norm_eq_abs,ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm]
  calc
    _ = ∫⁻ x, variationCube G N x^(2/3:ℝ) ∂μ := by
      apply lintegral_congr
      intro x
      rw [variationCube_freeze]
    _ ≤ ∫⁻ x, ENNReal.ofReal (2048*weightedRelativeExitEnergy G (N+1) x) ∂μ :=
      lintegral_mono (variationCube_relative_energy G N)
    _ = ENNReal.ofReal (2048*(∫ x, weightedRelativeExitEnergy G (N+1) x ∂μ)) := by
      simp_rw [ENNReal.ofReal_mul (show (0:ℝ)≤2048 by norm_num)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←heW]
    _ ≤ ENNReal.ofReal (1024*(∫ x, F N x^2 ∂μ)) := by
      apply ENNReal.ofReal_le_ofReal
      have hh : (∫ x, weightedRelativeExitEnergy G (N+1) x ∂μ)≤(1/2)*(∫ x, F N x^2 ∂μ) := by
        simpa only [G,min_eq_right (Nat.le_succ N)] using hWi
      linarith
    _ = (1024:ℝ≥0∞)*squareIntegral μ (F N) := by
      rw [ENNReal.ofReal_mul (by norm_num),heF,heFn]
      norm_num

/-- The published input is discharged without adding assumptions. -/
theorem lepingleInput_proved : LepingleInput := by
  refine ⟨32,by norm_num,?_⟩
  intro Ω m μ hμ ℱ F hF hF2 N
  let : IsProbabilityMeasure μ := hμ
  convert martingale_variation_L2 hF hF2 N using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_TwoInputMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform short directional Hilbert transform estimates conditional on
Lacey–Li and martingale variation bounds, using frequency reassembly and
classical one-dimensional Hilbert estimates. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert

theorem main_of_two_published_inputs (hVariation : LepingleInput) (hLL : LaceyLiInput) :
    ∃ a : ℝ, a∈Ioo 0 (1/2) ∧ ∃ C : ℝ≥0, 0<C ∧ ShortHilbertConclusion a C :=
  main_of_three_published_inputs hVariation hLL horizontalHilbertInput_proved

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_OneInputMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform short directional Hilbert transform estimates conditional on the
finite-rectangle Lacey–Li bound, using martingale variation and the classical
one-dimensional Hilbert transform. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert

theorem main_of_laceyLi_input (hLL : LaceyLiInput) :
    ∃ a : ℝ, a∈Ioo 0 (1/2) ∧ ∃ C : ℝ≥0, 0<C ∧ ShortHilbertConclusion a C :=
  main_of_two_published_inputs lepingleInput_proved hLL

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The main results of “A uniform Hilbert transform estimate for Lipschitz
directions” (25 September 2026). The estimates hold uniformly for Lipschitz
unit vector fields depending on both coordinates, at the reciprocal-Lipschitz
truncation scale. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert

/-- Uniform hard truncations, the actual symmetric principal value,
weak-(2,2), and bounded L2 extensions at an absolute short scale. -/
theorem main_oai :
    ∃ a : ℝ, a∈Ioo 0 (1/2) ∧ ∃ C : ℝ≥0, 0<C ∧ ShortHilbertConclusion a C :=
  main_of_laceyLi_input laceyLiInput_proved

end LipschitzHilbert

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.main_oai := @OAI.LipschitzHilbert.main_oai
