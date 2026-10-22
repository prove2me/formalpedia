-- Prove2me | solution 1 for NonconvexAG.StochComposite.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T09:54:16.814121+00:00
-- url     : https://prove2.me/submissions/11f73cdf-5dc9-41a5-9db6-b9fda0b3eed0

/-
Nonexpansiveness of the gradient mapping from the actual convex proximal minimizer property.
Mathematical source: Saeed Ghadimi and Guanghui Lan, arXiv:1310.3787v1, Lemma 4.
Their source credits Proposition 1 of S. Ghadimi, G. Lan and H. Zhang (2013), reference [13].
Platform definitions/statements: mikedeng1; statement review: Shuze Chen.
Alexander Richard Towell (queelius): research direction and contribution stewardship.
OpenAI Codex: substantial formalization, verification and documentation assistance.
Lean/Mathlib contributors: convexity, Euclidean geometry, limits and algebraic tactics.
No claim of new mathematics or independent human review is made.
-/
import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_StochComposite_ProxMap
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace Topology
open Filter GhadimiLan.RSG NonconvexAG.StochComposite

namespace ProxResearch
lemma variational {n : ℕ} (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P)
    (x y u : E n) (c : ℝ) (hc : 0 < c) (hu : u ∈ K) :
    0 ≤ c * (inner ℝ y (u-P x y c) + X u-X (P x y c)) +
      inner ℝ (P x y c-x) (u-P x y c) := by
  let p := P x y c
  let d := u-p
  let A := c*(inner ℝ y d + X u-X p)+inner ℝ (p-x) d
  let B := ‖d‖^2
  have hp : p ∈ K := (hP x y c hc).1
  have hseg (t : ℝ) (ht : 0 < t) (ht1 : t < 1) : 0 ≤ 2*A+t*B := by
    have hm := (hP x y c hc).2 ((1-t) • p+t • u)
      (hX.1 hp hu (by linarith : 0 ≤ 1-t) ht.le (by ring))
    have hv := hX.2 hp hu (by linarith : 0 ≤ 1-t) ht.le (by ring : (1-t)+t=1)
    have he : (1-t) • p+t • u = p+t • d := by dsimp [d]; module
    have he' : p+t • d-x = (p-x)+t • d := by abel
    rw [he] at hm hv
    simp only [smul_eq_mul] at hv
    rw [he', norm_add_sq_real, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, real_inner_smul_right, inner_add_right, real_inner_smul_right] at hm
    have hq : 0 ≤ t*(2*A+t*B) := by
      dsimp [A,B]
      field_simp [hc.ne'] at hm
      nlinarith
    exact nonneg_of_mul_nonneg_right hq ht
  have htend : Tendsto (fun t : ℝ => 2*A+t*B) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (2*A)) := by
    have hh : ContinuousAt (fun t : ℝ => 2*A+t*B) 0 := by fun_prop
    simpa using hh.mono_left nhdsWithin_le_nhds
  have hh : 0 ≤ 2*A := ge_of_tendsto htend (by
    filter_upwards [self_mem_nhdsWithin, (nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1)))] with t ht ht1
    exact hseg t ht ht1)
  change 0 ≤ A
  linarith


lemma prox_lipschitz {n : ℕ} (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P)
    (x y1 y2 : E n) (c : ℝ) (hc : 0 < c) :
    ‖P x y1 c-P x y2 c‖ ≤ c*‖y1-y2‖ := by
  let p1 := P x y1 c
  let p2 := P x y2 c
  have h1 := variational K X hX P hP x y1 p2 c hc (hP x y2 c hc).1
  have h2 := variational K X hX P hP x y2 p1 c hc (hP x y1 c hc).1
  change 0 ≤ c*(inner ℝ y1 (p2-p1)+X p2-X p1)+inner ℝ (p1-x) (p2-p1) at h1
  change 0 ≤ c*(inner ℝ y2 (p1-p2)+X p1-X p2)+inner ℝ (p2-x) (p1-p2) at h2
  have hf : ‖p1-p2‖^2 ≤ c*inner ℝ (y2-y1) (p1-p2) := by
    rw [norm_sub_sq_real]
    simp only [inner_sub_left,inner_sub_right,real_inner_self_eq_norm_sq] at h1 h2 ⊢
    nlinarith [real_inner_comm p1 p2]
  have hcs := real_inner_le_norm (y2-y1) (p1-p2)
  rw [norm_sub_rev y2 y1] at hcs
  have hsq : ‖p1-p2‖^2 ≤ c*‖y1-y2‖*‖p1-p2‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hcs hc.le]
  by_cases he : ‖p1-p2‖=0
  · rw [show P x y1 c-P x y2 c = p1-p2 from rfl,he]; positivity
  · have hp : 0 < ‖p1-p2‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm he)
    change ‖p1-p2‖ ≤ c*‖y1-y2‖
    nlinarith

end ProxResearch

theorem solution {n : ℕ} (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P) :
    ∀ x y1 y2 : E n, ∀ c : ℝ, 0 < c →
      ‖gradMap P x y1 c-gradMap P x y2 c‖ ≤ ‖y1-y2‖ := by
  intro x y1 y2 c hc
  have h := ProxResearch.prox_lipschitz K X hX P hP x y1 y2 c hc
  have he : (x-P x y1 c)-(x-P x y2 c) = -(P x y1 c-P x y2 c) := by abel
  rw [gradMap,gradMap,← smul_sub,he,norm_smul,norm_neg,
    Real.norm_of_nonneg (by positivity : 0 ≤ 1/c)]
  rw [one_div,← div_eq_inv_mul]
  exact (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using h)
#print axioms ProxResearch.variational
#print axioms ProxResearch.prox_lipschitz
#print axioms solution

