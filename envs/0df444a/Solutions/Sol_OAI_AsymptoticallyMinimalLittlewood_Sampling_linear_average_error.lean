-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Sampling.linear_average_error
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:50:29.910818+00:00
-- url     : https://prove2.me/submissions/67dd0978-24ef-4def-bb6a-e6357c3f0489

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/SamplingEnergy.lean:L73-L138
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Sampling.linear_average_error. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
import Definitions.Def_OAI_Analysis_Littlewood_SamplingTail
import Definitions.Def_OAI_Analysis_Littlewood_SamplingEnergy
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_polynomial_decay
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_latticeWeight_summable
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_poisson_tail_bound

-- ---- from OAI.Analysis.Littlewood.QuadraticTail ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
namespace OAI

universe uI uZ

namespace AsymptoticallyMinimalLittlewood
namespace QuadraticTail
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff

lemma phase_smooth (t u : ℝ) : ContDiff ℝ ∞ (phase t u) := by
  have hc : ContDiff ℝ ∞ (fun x : ℝ ↦ 2*Real.pi*(t*x^2/2-u*x)) := by fun_prop
  exact ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ Complex.I)).mul
    (Complex.ofRealCLM.contDiff.comp hc)).cexp

end
end QuadraticTail
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- from OAI.Analysis.Littlewood.SamplingTail ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open MeasureTheory FourierTransform Filter Topology Complex
open scoped BigOperators FourierTransform SchwartzMap ContDiff
open QuadraticTail

lemma latticeWeight_pos (w : ℤ) : 0 < latticeWeight w := by
  dsimp [latticeWeight]
  positivity

lemma sampledChirp_compact {g : ℝ → ℂ} (hg : HasCompactSupport g)
    {N : ℝ} (hN : N≠0) (β b : ℝ) : HasCompactSupport (sampledChirp g N β b) := by
  have h := hg.comp_homeomorph (Homeomorph.mulRight₀ N⁻¹ (inv_ne_zero hN))
  exact (show HasCompactSupport (fun x : ℝ ↦ g (x/N)) from by
    simpa only [Function.comp_def,Homeomorph.coe_mulRight₀,div_eq_mul_inv] using h).mul_right

lemma sampledChirp_smooth {g : ℝ → ℂ} (hgs : ContDiff ℝ ∞ g)
    (N β b : ℝ) : ContDiff ℝ ∞ (sampledChirp g N β b) := by
  exact (hgs.comp (by fun_prop)).mul (phase_smooth _ _)

lemma sampledChirp_fourier (g : ℝ → ℂ) {N : ℝ} (hN : 0<N) (β b u : ℝ) :
    𝓕 (sampledChirp g N β b) u =
      (N : ℂ)*(∫ x : ℝ, g x*phase (N*β) (N*(u-b)) x) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he : (fun x : ℝ ↦ Complex.exp ((-2*Real.pi*x*u : ℝ)*Complex.I) • sampledChirp g N β b x)=
      (fun x : ℝ ↦ (g x*phase (N*β) (N*(u-b)) x)) ∘ (fun x : ℝ ↦ x/N) := by
    funext x
    dsimp only [sampledChirp,Function.comp_def,phase,smul_eq_mul]
    rw [mul_left_comm,← Complex.exp_add]
    congr 2
    push_cast
    field_simp [hN.ne', Complex.ofReal_ne_zero.mpr hN.ne']
    ring
  rw [he]
  change (∫ x : ℝ, (g (x*N⁻¹)*phase (N*β) (N*(u-b)) (x*N⁻¹))) = _
  rw [Measure.integral_comp_inv_mul_right
    (fun x : ℝ ↦ g x*phase (N*β) (N*(u-b)) x) N,abs_of_pos hN,Complex.real_smul]

lemma poisson_chirp {g : ℝ → ℂ} (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {N : ℝ} (hN : 0<N) (β b : ℝ) :
    (∑' k : ℤ, g ((k : ℝ)/N)*phase (β/N) (-b) k)=
      (N : ℂ)*∑' l : ℤ, ∫ x : ℝ, g x*phase (N*β) (N*((l : ℝ)-b)) x := by
  let f := (sampledChirp_compact hg hN.ne' β b).toSchwartzMap (sampledChirp_smooth hgs N β b)
  have h := f.tsum_eq_tsum_fourier 0
  simp only [zero_add,AddCircle.coe_zero,fourier_eval_zero, mul_one] at h
  change (∑' k : ℤ, sampledChirp g N β b k)=_ at h
  change (∑' k : ℤ, sampledChirp g N β b k)=_
  rw [h,← tsum_mul_left]
  apply tsum_congr
  intro l
  change 𝓕 (sampledChirp g N β b) (l : ℝ)=_
  exact sampledChirp_fourier g hN β b l

lemma int_abs_large_of_not_mem {R : ℕ} {l : ℤ}
    (hl : l∉Finset.Icc (-(R : ℤ)) R) : (R : ℝ)≤|(l : ℝ)| := by
  simp only [Finset.mem_Icc,not_and_or] at hl
  rcases hl with hl | hl
  · have hh : (l : ℝ) < -(R : ℝ) := by exact_mod_cast (lt_of_not_ge hl)
    have hab := neg_le_abs (l : ℝ)
    linarith
  · have hh : (R : ℝ)<l := by exact_mod_cast (lt_of_not_ge hl)
    exact hh.le.trans (le_abs_self _)

end
end AsymptoticallyMinimalLittlewood.Sampling

end OAI

-- ---- from OAI.Analysis.Littlewood.SamplingEnergy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail

/-- The linear (equal-curvature) case of the same off-diagonal calculation. -/
theorem linear_integral_decay {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {b : ℝ} {l : ℤ} (hl : (l : ℝ)≠b) :
    ∃ C : ℝ, 0≤C ∧ ∀ N : ℝ, 0<N →
      N^2*‖∫ x : ℝ, g x*phase 0 (N*((l : ℝ)-b)) x‖≤C := by
  obtain ⟨C,hC,h⟩ := polynomial_decay 2 |(l : ℝ)-b| 0
    (abs_pos.mpr (sub_ne_zero.mpr hl)) le_rfl g hg hgs 0
  refine ⟨C,hC,?_⟩
  intro N hN
  have he := h 0 (N*((l : ℝ)-b)) N hN (by simp) (by
    intro x hx
    simp only [zero_mul,zero_sub,abs_neg,abs_mul,abs_of_pos hN]
    exact le_of_eq (mul_comm _ _))
  simpa only [Nat.zero_add,osc,amp,pow_zero,div_one] using he

/-- Averaged Poisson summation after removing a finite resonant set. This
single estimate handles both the diagonal Riemann sum and equal-curvature
cross terms without any uniformity in the packing data. -/
theorem linear_average_error {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {A : ℝ} (hA : 0≤A)
    (hsupp : tsupport g⊆Set.Icc (-A) A) (b : ℝ) (S : Finset ℤ)
    (hres : ∀ l∉S, (l : ℝ)≠b) :
    ∃ C : ℝ, 0≤C ∧ ∀ N : ℝ, 0<N →
      ‖(1/(N : ℂ))*(∑' k : ℤ, g ((k : ℝ)/N)*phase 0 (-b) k)-
        ∑ l∈S, ∫ x : ℝ, g x*phase 0 (N*((l : ℝ)-b)) x‖≤C/N^2 := by
  classical
  obtain ⟨R,hR⟩ := exists_nat_gt (2*|b|+1)
  let J : Finset ℤ := Finset.Icc (-(R : ℤ)) R
  obtain ⟨C₀,hC₀,ht⟩ := poisson_tail_bound hg hgs (β := 0) hA (abs_nonneg b) hsupp
    (by simpa using hR.le)
  have hex (l : ℤ) : ∃ C : ℝ, 0≤C ∧ ∀ N : ℝ, 0<N → l∉S →
      N^2*‖∫ x : ℝ, g x*phase 0 (N*((l : ℝ)-b)) x‖≤C := by
    by_cases hl : l∈S
    · exact ⟨0,le_rfl,fun _ _ hn ↦ False.elim (hn hl)⟩
    · obtain ⟨C,hC,h⟩ := linear_integral_decay hg hgs (hres l hl)
      exact ⟨C,hC,fun N hN _ ↦ h N hN⟩
  choose c hc hdec using hex
  let w (l : ℤ) : ℝ := (if l∈J then c l else 0)+C₀*latticeWeight l
  have hw0 (l : ℤ) : 0≤w l := by
    dsimp [w]
    exact add_nonneg (by split_ifs; exact hc l; exact le_rfl)
      (mul_nonneg hC₀ (latticeWeight_pos l).le)
  have hw : Summable w := (summable_of_ne_finset_zero (s := J) (by
    intro l hl; simp [hl])).add (latticeWeight_summable.mul_left C₀)
  refine ⟨∑' l, w l,tsum_nonneg hw0,?_⟩
  intro N hN
  let I (l : ℤ) : ℂ := ∫ x : ℝ, g x*phase 0 (N*((l : ℝ)-b)) x
  let E (l : ℤ) : ℂ := if l∈S then 0 else I l
  have he (l : ℤ) : ‖E l‖≤w l/N^2 := by
    by_cases hs : l∈S
    · simp only [E,ite_eq_left hs,norm_zero]; exact div_nonneg (hw0 l) (sq_nonneg N)
    · simp only [E,ite_eq_right hs]
      rw [le_div_iff₀ (sq_pos_of_pos hN)]
      rw [mul_comm]
      by_cases hl : l∈J
      · exact (hdec l N hN hs).trans (by dsimp [w]; rw [ite_eq_left hl]; exact le_add_of_nonneg_right (mul_nonneg hC₀ (latticeWeight_pos l).le))
      · have hh := ht N b hN le_rfl l (int_abs_large_of_not_mem hl)
        simpa only [mul_zero,w,ite_eq_right hl,zero_add,I] using hh
  have hE : Summable E := (hw.div_const (N^2)).of_norm_bounded he
  have hIS : Summable (fun l ↦ if l∈S then I l else 0) :=
    summable_of_ne_finset_zero (s := S) (by intro l hl; simp [hl])
  have hI : Summable I := by
    convert hE.add hIS using 1
    funext l
    dsimp [E]
    split_ifs <;> simp
  have hsum : (∑' l, I l)-(∑ l∈S, I l)=∑' l, E l := by
    have ht : (∑' l, if l∈S then I l else 0)=∑ l∈S, I l := by
      rw [tsum_eq_sum (s := S) (by intro l hl; simp [hl])]
      exact Finset.sum_congr rfl (fun l hl ↦ ite_eq_left hl)
    rw [← ht]
    rw [← hI.tsum_sub hIS]
    apply tsum_congr
    intro l
    dsimp [E]; split_ifs <;> simp
  rw [show (∑' k : ℤ, g ((k : ℝ)/N)*phase 0 (-b) k)=
      (N : ℂ)*∑' l, I l by simpa only [mul_zero,zero_div,I] using poisson_chirp hg hgs hN 0 b]
  rw [← mul_assoc,one_div_mul_cancel (Complex.ofReal_ne_zero.mpr hN.ne'),one_mul,hsum]
  apply (norm_tsum_le_tsum_norm hE.norm).trans
  rw [← tsum_div_const]
  exact Summable.tsum_le_tsum he hE.norm (hw.div_const (N^2))

end
end AsymptoticallyMinimalLittlewood.Sampling

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Sampling
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.linear_average_error := @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.linear_average_error
