-- Prove2me | solution 1 for GraphonGames.Stability.lemma_3_7_best_response_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T08:43:20.689117+00:00
-- url     : https://prove2.me/submissions/14733c9c-95c9-488b-ba79-b5307358f5bf

/-
Complete best-response sensitivity and L2 bound from the actual Assumption4.
Original mathematics: Carmona, Cooney, Graves and Laurière, Stochastic Graphon Games I,
arXiv:1911.10664v1, Lemma3.7; their source credits Parise and Ozdaglar [26].
Platform definitions/statements: mikedeng1; review: Shuze Chen.
Alexander Richard Towell (queelius) directed this formalization; OpenAI Codex substantially
assisted proof development, verification and documentation using Lean/Mathlib.
No claim of mathematical novelty or independent human review is made.
-/
import Mathlib
import Definitions.Def_GraphonGames_Stability_Setting
open MeasureTheory
open scoped ENNReal
namespace BestResponseResearch
open GraphonGames.Existence
variable {J : ℝ → ℝ → ℝ} {ℓc ℓJ : ℝ} (h4 : Asm4 J ℓc ℓJ)
include h4
lemma strongly_convex (z : ℝ) : StrongConvexOn Set.univ ℓc (fun a => J a z) := by
  refine ⟨convex_univ, ?_⟩
  intro a ha b hb u v hu hv huv
  have hv' : v = 1-u := by linarith
  have h := h4.2.2.2.1 a b z u hu (by linarith)
  simp only [smul_eq_mul, Real.norm_eq_abs]
  rw [hv']
  convert h using 1 <;> ring
lemma differentiable (z : ℝ) : Differentiable ℝ (fun a => J a z) :=
  (h4.2.2.1 z).differentiable (by norm_num)
lemma convex (z : ℝ) : ConvexOn ℝ Set.univ (fun a => J a z) :=
  ((strongly_convex h4 z).strictConvexOn h4.1).convexOn
lemma derivative_growth (z a b : ℝ) (hab : a ≤ b) :
    ℓc*(b-a) ≤ deriv (fun x => J x z) b - deriv (fun x => J x z) a := by
  let g : ℝ → ℝ := fun x => J x z - ℓc/2*x^2
  have hg : ConvexOn ℝ Set.univ g := by
    simpa only [Real.norm_eq_abs, sq_abs] using strongConvexOn_iff_convex.mp (strongly_convex h4 z)
  have hd (x : ℝ) : HasDerivAt g (deriv (fun x => J x z) x - ℓc*x) x := by
    have hq : HasDerivAt (fun y : ℝ => ℓc/2*y^2) (ℓc*x) x := by
      convert ((hasDerivAt_id x).pow 2).const_mul (ℓc/2) using 1 <;> norm_num <;> first | rfl | ring
    exact ((differentiable h4 z x).hasDerivAt).sub hq
  have hm := hg.monotoneOn_deriv (fun x _ => (hd x).differentiableAt)
  have hh := hm (Set.mem_univ a) (Set.mem_univ b) hab
  rw [(hd a).deriv, (hd b).deriv] at hh
  linarith
lemma exists_minimizer (z : ℝ) : ∃ a, ∀ b, J a z ≤ J b z := by
  let d := deriv (fun a => J a z) 0
  let R := (|d|+1)/ℓc
  have hc := h4.1
  have hR : 0 < R := div_pos (by positivity) hc
  have hRc : ℓc*R = |d|+1 := by dsimp [R]; field_simp
  have hlo := derivative_growth h4 z (-R) 0 (by linarith)
  have hhi := derivative_growth h4 z 0 R hR.le
  have hl : deriv (fun a => J a z) (-R) ≤ 0 := by
    have hab := le_abs_self d
    change d - deriv (fun a => J a z) (-R) ≥ ℓc * (0- -R) at hlo
    nlinarith
  have hu : 0 ≤ deriv (fun a => J a z) R := by
    have hab := neg_abs_le d
    change ℓc*(R-0) ≤ deriv (fun a => J a z) R-d at hhi
    nlinarith
  obtain ⟨a, _, ha⟩ := intermediate_value_Icc (show -R ≤ R by linarith)
    ((h4.2.2.1 z).continuous_deriv (by norm_num)).continuousOn (show (0:ℝ) ∈ Set.Icc _ _ from ⟨hl,hu⟩)
  refine ⟨a, fun b => ?_⟩
  rcases lt_trichotomy a b with hab | rfl | hba
  · have h := (convex h4 z).deriv_le_slope (Set.mem_univ a) (Set.mem_univ b) hab (differentiable h4 z a)
    rw [ha, slope_def_field] at h
    have hh := (le_div_iff₀ (sub_pos.mpr hab)).mp h
    linarith
  · rfl
  · have h := (convex h4 z).slope_le_deriv (Set.mem_univ b) (Set.mem_univ a) hba (differentiable h4 z a)
    rw [ha, slope_def_field] at h
    have hh := (div_le_iff₀ (sub_pos.mpr hba)).mp h
    linarith
noncomputable def response (J : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  Classical.epsilon (fun a => ∀ b, J a z ≤ J b z)
lemma response_min (z b : ℝ) : J (response J z) z ≤ J b z :=
  Classical.epsilon_spec (exists_minimizer h4 z) b
lemma response_deriv (z : ℝ) : deriv (fun a => J a z) (response J z) = 0 := by
  have hm : IsMinOn (fun a => J a z) Set.univ (response J z) := fun b _ => response_min h4 z b
  exact (hm.isLocalMin (by simp)).deriv_eq_zero
lemma response_bound (z z' : ℝ) : |response J z-response J z'| ≤ (ℓJ/ℓc)*|z-z'| := by
  have hc := h4.1
  have hder := h4.2.2.2.2 (response J z') z z'
  rw [response_deriv h4 z'] at hder
  rw [zero_sub, abs_neg, abs_sub_comm z' z] at hder
  rcases le_total (response J z) (response J z') with h | h
  · have hg := derivative_growth h4 z (response J z) (response J z') h
    rw [response_deriv h4 z, sub_zero] at hg
    have hb := (le_abs_self (deriv (fun a => J a z) (response J z'))).trans hder
    rw [abs_of_nonpos (sub_nonpos.mpr h)]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    nlinarith [hg.trans hb]
  · have hg := derivative_growth h4 z (response J z') (response J z) h
    rw [response_deriv h4 z, zero_sub] at hg
    have hb := (neg_le_abs (deriv (fun a => J a z) (response J z'))).trans hder
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hh := hg.trans hb
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    nlinarith
lemma response_unique (z a : ℝ) (ha : ∀ b, J a z ≤ J b z) : a = response J z := by
  exact ((strongly_convex h4 z).strictConvexOn h4.1).eq_of_isMinOn
    (fun b _ => ha b) (fun b _ => response_min h4 z b) (Set.mem_univ a) (Set.mem_univ _)
lemma response_lipschitz : LipschitzWith ⟨ℓJ/ℓc, div_nonneg h4.2.1 h4.1.le⟩ (response J) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |response J x-response J y| ≤ (ℓJ/ℓc)*|x-y|
  exact response_bound h4 x y
lemma profile_memLp (z : unitInterval → ℝ) (hz : MemLp z 2 volume) :
    MemLp (GraphonGames.Stability.bestResponse J z) 2 volume := by
  have hg : LipschitzWith ⟨ℓJ/ℓc, div_nonneg h4.2.1 h4.1.le⟩ (fun x => response J x-response J 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using (response_lipschitz h4).dist_le_mul x y
  have hm := hg.comp_memLp (by simp) hz
  have hc : MemLp (fun _ : unitInterval => response J 0) 2 volume := memLp_const _
  convert hm.add hc using 1
  ext x
  simp [Function.comp_def, GraphonGames.Stability.bestResponse, response]
end BestResponseResearch
open GraphonGames.Stability

theorem solution
    (J : ℝ → ℝ → ℝ) (ℓc ℓJ : ℝ) (h4 : GraphonGames.Existence.Asm4 J ℓc ℓJ)
    (z1 z2 : I → ℝ) (hz1 : MemLp z1 2 volume)
    (hz2 : MemLp z2 2 volume) :
    eLpNorm (bestResponse J z1 - bestResponse J z2) 2 volume ≤
      ENNReal.ofReal (ℓJ / ℓc) * eLpNorm (z1 - z2) 2 volume := by
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
  apply Filter.Eventually.of_forall
  intro x
  simpa only [Pi.sub_apply, Real.norm_eq_abs, bestResponse, BestResponseResearch.response]
    using BestResponseResearch.response_bound h4 (z1 x) (z2 x)
#print axioms solution
