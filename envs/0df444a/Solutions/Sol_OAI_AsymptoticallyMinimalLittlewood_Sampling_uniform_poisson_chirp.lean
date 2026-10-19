-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Sampling.uniform_poisson_chirp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:46:45.551197+00:00
-- url     : https://prove2.me/submissions/529afa56-496d-4ab1-8b7c-24bbe3d9b18a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/SamplingTail.lean:L181-L249
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Sampling.uniform_poisson_chirp. The node keeps its source
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
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_latticeWeight_summable
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_poisson_tail_bound
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_uniform_quadratic_integration

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
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

lemma normalized_integral_error {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {β : ℝ} (hβ : β≠0) :
    ∃ C : ℝ, 0≤C ∧ ∀ N b : ℝ, 0<N → ∀ l : ℤ,
      ‖(Real.sqrt N : ℂ)*(∫ x : ℝ, g x*phase (N*β) (N*((l : ℝ)-b)) x)-
        stationaryWave g N β b l‖ ≤ C/N := by
  let C₀ := Real.pi/|β| *(∫ ξ : ℝ, ξ^2*‖(𝓕⁻ (hg.toSchwartzMap hgs) : 𝓢(ℝ,ℂ)) ξ‖)
  have hC0 : 0≤C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀/Real.sqrt |β|,by positivity,?_⟩
  intro N b hN l
  obtain ⟨E,hE,hEq⟩ := uniform_quadratic_integration g hg hgs hβ hN (N*((l : ℝ)-b))
  have hsN : (Real.sqrt N : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hN).ne'
  have hsβ : (Real.sqrt |β| : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (abs_pos.mpr hβ)).ne'
  have hephase : (N*((l : ℝ)-b))^2/(2*N*β)=N*((l : ℝ)-b)^2/(2*β) := by field_simp
  have hestat : N*((l : ℝ)-b)/(N*β)=((l : ℝ)-b)/β := by field_simp
  have hint : (∫ x : ℝ, g x*phase (N*β) (N*((l : ℝ)-b)) x)=
      (realPhase (2*Real.pi*(Real.sign β/8-N*((l : ℝ)-b)^2/(2*β)))/
        ((Real.sqrt N : ℂ)*(Real.sqrt |β| : ℂ)))*(g (((l : ℝ)-b)/β)+E) := by
    simpa only [phase,realPhase,hephase,hestat,Real.sqrt_mul hN.le,Complex.ofReal_mul] using hEq
  rw [hint]
  have he : (Real.sqrt N : ℂ)*
      ((realPhase (2*Real.pi*(Real.sign β/8-N*((l : ℝ)-b)^2/(2*β)))/
        ((Real.sqrt N : ℂ)*(Real.sqrt |β| : ℂ)))*(g (((l : ℝ)-b)/β)+E))-
        stationaryWave g N β b l =
      realPhase (2*Real.pi*(Real.sign β/8-N*((l : ℝ)-b)^2/(2*β)))/
        (Real.sqrt |β| : ℂ)*E := by unfold stationaryWave; field_simp ; ring
  rw [he,norm_mul,norm_div,norm_realPhase,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ 1/Real.sqrt |β| *(C₀/N) := mul_le_mul_of_nonneg_left hE (by positivity)
    _ = (C₀/Real.sqrt |β|)/N := by ring

lemma stationaryWave_zero {g : ℝ → ℂ} {A B β L : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hsupp : tsupport g⊆Set.Icc (-A) A) (hβ : β≠0) (hL : 2*(|β| *A+B)+1≤L)
    {b : ℝ} (hb : |b|≤B) {l : ℤ} (hl : L≤|(l : ℝ)|) (N : ℝ) :
    stationaryWave g N β b l=0 := by
  have hβ0 := abs_pos.mpr hβ
  have hg : g (((l : ℝ)-b)/β)=0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hx := abs_le.mpr (hsupp hm)
    rw [abs_div] at hx
    have hx' := (div_le_iff₀ hβ0).mp hx
    have ht : |(l : ℝ)|≤|(l : ℝ)-b|+|b| := by simpa using abs_add_le ((l : ℝ)-b) b
    nlinarith [mul_nonneg (abs_nonneg β) hA]
  simp [stationaryWave,hg]

lemma int_abs_large_of_not_mem {R : ℕ} {l : ℤ}
    (hl : l∉Finset.Icc (-(R : ℤ)) R) : (R : ℝ)≤|(l : ℝ)| := by
  simp only [Finset.mem_Icc,not_and_or] at hl
  rcases hl with hl | hl
  · have hh : (l : ℝ) < -(R : ℝ) := by exact_mod_cast (lt_of_not_ge hl)
    have hab := neg_le_abs (l : ℝ)
    linarith
  · have hh : (R : ℝ)<l := by exact_mod_cast (lt_of_not_ge hl)
    exact hh.le.trans (le_abs_self _)

/-- The exact fixed-data sampling estimate, centered at zero; a nonzero center
is obtained by shifting the linear frequency and a unit scalar phase. -/
theorem uniform_poisson_chirp {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {A B β : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hsupp : tsupport g⊆Set.Icc (-A) A) (hβ : β≠0) :
    ∃ J : Finset ℤ, ∃ C : ℝ, 0≤C ∧ ∀ N b : ℝ, 1≤N → |b|≤B →
      (∀ l∉J, stationaryWave g N β b l=0) ∧
      ‖(1/(Real.sqrt N : ℂ))*(∑' k : ℤ, g ((k : ℝ)/N)*phase (β/N) (-b) k)-
        ∑ l∈J, stationaryWave g N β b l‖≤C/N := by
  classical
  obtain ⟨R,hR⟩ := exists_nat_gt (2*(|β| * A+B)+1)
  let J : Finset ℤ := Finset.Icc (-(R : ℤ)) R
  obtain ⟨C₀,hC₀,herr⟩ := normalized_integral_error hg hgs hβ
  obtain ⟨C₁,hC₁,htail⟩ := poisson_tail_bound hg hgs hA hB hsupp hR.le
  let w : ℤ → ℝ := fun l ↦ (if l∈J then C₀ else 0)+C₁*latticeWeight l
  have hw0 (l : ℤ) : 0≤w l := add_nonneg (by split_ifs <;> positivity) (mul_nonneg hC₁ (latticeWeight_pos l).le)
  have hw : Summable w := by
    apply Summable.add
    · exact summable_of_ne_finset_zero (s := J) (by intro l hl; simp [hl])
    · exact latticeWeight_summable.mul_left C₁
  refine ⟨J,∑' l, w l,tsum_nonneg hw0,?_⟩
  intro N b hN hb
  have hN0 : 0<N := lt_of_lt_of_le zero_lt_one hN
  have hsN0 : 0<Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsN : Real.sqrt N≤N := Real.sqrt_le_self_iff.mpr (Or.inr hN)
  have hzero (l : ℤ) (hl : l∉J) : stationaryWave g N β b l=0 :=
    stationaryWave_zero hA hB hsupp hβ hR.le hb (int_abs_large_of_not_mem hl) N
  refine ⟨hzero,?_⟩
  let I (l : ℤ) : ℂ := (Real.sqrt N : ℂ)*(∫ x : ℝ, g x*phase (N*β) (N*((l : ℝ)-b)) x)
  let W := stationaryWave g N β b
  have hW : Summable W := summable_of_ne_finset_zero (s := J) hzero
  have heBound (l : ℤ) : ‖I l-W l‖≤w l/N := by
    by_cases hl : l∈J
    · have h := herr N b hN0 l
      have hw' : C₀≤w l := by dsimp [w]; rw [ite_eq_left hl]; exact le_add_of_nonneg_right (mul_nonneg hC₁ (latticeWeight_pos l).le)
      exact h.trans (div_le_div_of_nonneg_right hw' hN0.le)
    · have ht := htail N b hN0 hb l (int_abs_large_of_not_mem hl)
      have heq : ‖I l-W l‖=Real.sqrt N*‖∫ x : ℝ, g x*phase (N*β) (N*((l : ℝ)-b)) x‖ := by
        dsimp [I,W]; rw [hzero l hl,sub_zero,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hsN0]
      rw [heq]
      dsimp [w]
      rw [ite_eq_right hl,zero_add,le_div_iff₀ hN0]
      have hnorm := norm_nonneg (∫ x : ℝ, g x*phase (N*β) (N*((l : ℝ)-b)) x)
      nlinarith only [ht,mul_nonneg (sub_nonneg.mpr hsN) hnorm,mul_nonneg hN0.le (mul_nonneg (sub_nonneg.mpr hsN) hnorm)]
  have he : Summable (fun l ↦ I l-W l) :=
    (hw.div_const N).of_norm_bounded heBound
  have hI : Summable I := by
    convert he.add hW using 1
    funext l
    ring
  have hsum := norm_tsum_le_tsum_norm he.norm
  have hnorm : ‖∑' l, (I l-W l)‖≤(∑' l, w l)/N := by
    apply hsum.trans
    rw [← tsum_div_const]
    exact Summable.tsum_le_tsum heBound he.norm (hw.div_const N)
  rw [hI.tsum_sub hW] at hnorm
  have hWsum : (∑' l, W l)=∑ l∈J, W l := tsum_eq_sum hzero
  rw [hWsum] at hnorm
  have hIsum : (∑' l, I l)=(1/(Real.sqrt N : ℂ))*
      (∑' k : ℤ, g ((k : ℝ)/N)*phase (β/N) (-b) k) := by
    rw [poisson_chirp hg hgs hN0 β b]
    change (∑' l, (Real.sqrt N : ℂ)*_) = _
    rw [tsum_mul_left]
    have hsq : (Real.sqrt N : ℂ)^2=(N : ℂ) := by exact_mod_cast Real.sq_sqrt hN0.le
    have hfac : (1/(Real.sqrt N : ℂ))*(N : ℂ)=(Real.sqrt N : ℂ) := by
      rw [← hsq]
      field_simp [Complex.ofReal_ne_zero.mpr hsN0.ne']
    rw [← mul_assoc,hfac]
  simpa only [hIsum,W] using hnorm

end
end AsymptoticallyMinimalLittlewood.Sampling

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Sampling
open MeasureTheory FourierTransform Filter Topology Complex
open scoped BigOperators FourierTransform SchwartzMap ContDiff
open QuadraticTail


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.uniform_poisson_chirp := @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.uniform_poisson_chirp
