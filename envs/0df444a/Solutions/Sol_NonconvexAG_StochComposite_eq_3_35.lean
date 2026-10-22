-- Prove2me | solution 1 for NonconvexAG.StochComposite.eq_3_35
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T15:37:18.021532+00:00
-- url     : https://prove2.me/submissions/6e3a2f71-e483-4f82-82d8-fec4eed892d7

/-
Complete expected stochastic proximal estimate (3.35), Ghadimi-Lan arXiv1310.3787v1 p23.
Mathematics: Saeed Ghadimi and Guanghui Lan. In this pinned version, the proximal
principle is credited to Ghadimi-Lan2012, reference[11]; retained older source comments
mentioning Ghadimi-Lan-Zhang[13] are superseded by this explicit source correction.
Complete accepted queelius pathwise and batch/error proofs retained inline, including
vebis's Equation3.34 and Equation2.47 bodies and all prior mathematical credit.
New proof supplies proximal-value continuity/integrability, actual-iterate integrability,
conditional noise cancellation and the exact expected coefficient, without adding hypotheses.
Alexander Richard Towell: direction and stewardship. OpenAI Codex: substantial proof
construction, assembly, checking and documentation. mikedeng1: platform model/repairs;
Shuze Chen: statement confirmation only. Lean/Mathlib contributors: proof infrastructure.
No mathematical novelty or independent human-review claim.
-/
/-
Bounded pathwise RSAG objective estimate, Ghadimi-Lan arXiv1310.3787v1 p23 first display.
Original mathematics: Saeed Ghadimi and Guanghui Lan.
Complete accepted queelius summed and iterate-bound bodies retained below;
the summed body retains vebis's complete Equation3.34 and Equation2.47 proofs.
New formal step: exact Gamma weight identity and weighted curvature estimate.
Prior platform model and initial-norm repair: mikedeng1; statement confirmation: Shuze Chen.
Alexander Richard Towell: research direction and stewardship.
OpenAI Codex: substantial formalization, assembly, verification and documentation.
Lean/Mathlib contributors: finite sums/products, norms, order and proof infrastructure.
No mathematical novelty or independent human-review claim.
-/
/-
Full pathwise weighted objective inequality, Ghadimi-Lan arXiv1310.3787v1 p22 last display.
Mathematical source: Saeed Ghadimi and Guanghui Lan.
Accepted one-step body: queelius submissionca92b8f3-f5c9-41bb-aec6-4143cdc033f4,
including credited complete vebis Equation3.34 and Equation2.47 proof bodies.
New assembly proves the actual Gamma recurrence, positive weights, distance-weight
monotonicity and complete finite telescoping without assuming the desired sum bound.
Alexander Richard Towell: direction. OpenAI Codex: substantial formalization/checking.
Platform formulations: mikedeng1; statement confirmation: Shuze Chen.
Lean/Mathlib infrastructure and all predecessor credit are retained below.
No mathematical novelty or independent human-review claim.
-/
/-
Pathwise stochastic composite objective estimate after (3.34), Ghadimi-Lan arXiv1310.3787v1 p22.
Original mathematics: Saeed Ghadimi and Guanghui Lan; predecessor proximal principle
credited in v1 to Ghadimi-Lan (2012), reference [11].
Two complete accepted proof bodies by vebis are retained under namespaces below:
Equation3.34, submission0038a9fc-3e52-42fe-a175-4242f50bdd5f;
Equation2.47, submissionb4efd53f-b120-4fd3-9901-b7e005ac01fd.
Platform model and statements: mikedeng1; prior statement confirmation: Shuze Chen.
Alexander Richard Towell (queelius): research direction and stewardship.
OpenAI Codex: substantial assembly, new noise estimate, formalization and verification.
Lean/Mathlib contributors: analysis, convexity, inner products and checking infrastructure.
No mathematical novelty or independent human proof review is claimed.
-/
import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_StochComposite_ProxMap
import Definitions.Def_NonconvexAG_StochComposite_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace PriorVebis334

open GhadimiLan.RSG (E)
open ConvexOptAlg.SmoothGD
open NonconvexAG.StochComposite

section YProx
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma yprox_var (K : Set V) (X : V → ℝ) (hX : ConvexOn ℝ K X) (x y p : V) (c : ℝ) (hc : 0 < c)
    (hpK : p ∈ K)
    (hmin : ∀ u ∈ K, inner ℝ y p + ‖p - x‖ ^ 2 / (2 * c) + X p ≤
      inner ℝ y u + ‖u - x‖ ^ 2 / (2 * c) + X u)
    (u : V) (hu : u ∈ K) :
    0 ≤ inner ℝ y (u - p) + (1 / c) * inner ℝ (p - x) (u - p) + X u - X p := by
  set A := inner ℝ y (u - p) + (1 / c) * inner ℝ (p - x) (u - p) + X u - X p with hA
  set B := ‖u - p‖ ^ 2 / (2 * c) with hB
  have hB0 : 0 ≤ B := by positivity
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ A + t * B := by
    intro t ht ht1
    have hut : (1 - t) • p + t • u ∈ K := hX.1 hpK hu (by linarith) ht.le (by ring)
    have h1 := hmin _ hut
    have h2 : X ((1 - t) • p + t • u) ≤ (1 - t) • X p + t • X u :=
      hX.2 hpK hu (by linarith) ht.le (by ring)
    have e1 : (1 - t) • p + t • u - x = (p - x) + t • (u - p) := by module
    have e2 : inner ℝ y ((1 - t) • p + t • u) = inner ℝ y p + t * inner ℝ y (u - p) := by
      have : (1 - t) • p + t • u = p + t • (u - p) := by module
      rw [this, inner_add_right, inner_smul_right]
    have e3 : ‖(p - x) + t • (u - p)‖ ^ 2 = ‖p - x‖ ^ 2 + 2 * t * inner ℝ (p - x) (u - p) + t ^ 2 * ‖u - p‖ ^ 2 := by
      rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    rw [e1, e3, e2] at h1
    simp only [smul_eq_mul] at h2
    have h3 : 0 ≤ t * A + t ^ 2 * B := by
      rw [hA, hB]
      have : t * (1 / c * inner ℝ (p - x) (u - p)) = 2 * t * inner ℝ (p - x) (u - p) / (2 * c) := by
        field_simp
      have h4 : t ^ 2 * ‖u - p‖ ^ 2 / (2 * c) = t ^ 2 * (‖u - p‖ ^ 2 / (2 * c)) := by ring
      have h5 : (‖p - x‖ ^ 2 + 2 * t * inner ℝ (p - x) (u - p) + t ^ 2 * ‖u - p‖ ^ 2) / (2 * c)
          = ‖p - x‖ ^ 2 / (2 * c) + 2 * t * inner ℝ (p - x) (u - p) / (2 * c) + t ^ 2 * ‖u - p‖ ^ 2 / (2 * c) := by
        ring
      rw [h5] at h1
      nlinarith [h1, h2, this, h4]
    have h6 : 0 ≤ t * (A + t * B) := by nlinarith [h3]
    exact (mul_nonneg_iff_of_pos_left ht).mp h6
  by_contra hneg
  push_neg at hneg
  have hpos : 0 < min 1 (-A / (B + 1)) := lt_min one_pos (div_pos (by linarith) (by linarith))
  have := key _ hpos (min_le_left _ _)
  have h7 : min 1 (-A / (B + 1)) * (B + 1) ≤ -A := by
    have := min_le_right 1 (-A / (B + 1))
    calc min 1 (-A / (B + 1)) * (B + 1) ≤ (-A / (B + 1)) * (B + 1) :=
          mul_le_mul_of_nonneg_right this (by linarith)
      _ = -A := by field_simp
  nlinarith

/-- three-point inequality for a prox step -/
lemma yprox_three (K : Set V) (X : V → ℝ) (hX : ConvexOn ℝ K X) (x y p : V) (c : ℝ) (hc : 0 < c)
    (hpK : p ∈ K)
    (hmin : ∀ u ∈ K, inner ℝ y p + ‖p - x‖ ^ 2 / (2 * c) + X p ≤
      inner ℝ y u + ‖u - x‖ ^ 2 / (2 * c) + X u)
    (u : V) (hu : u ∈ K) :
    inner ℝ y (p - u) + X p ≤
      X u + 1 / (2 * c) * (‖x - u‖ ^ 2 - ‖p - u‖ ^ 2 - ‖p - x‖ ^ 2) := by
  have h := yprox_var K X hX x y p c hc hpK hmin u hu
  have e : 2 * inner ℝ (p - x) (u - p) = ‖u - x‖ ^ 2 - ‖p - x‖ ^ 2 - ‖u - p‖ ^ 2 := by
    have : u - x = (p - x) + (u - p) := by abel
    rw [this, norm_add_sq_real]; ring
  have e2 : inner ℝ y (p - u) = - inner ℝ y (u - p) := by
    rw [← inner_neg_right]; congr 1; abel
  have e3 : 1 / c * inner ℝ (p - x) (u - p) = 1 / (2 * c) * (2 * inner ℝ (p - x) (u - p)) := by
    field_simp
  rw [e3, e] at h
  have n1 : ‖x - u‖ = ‖u - x‖ := norm_sub_rev _ _
  have n2 : ‖p - u‖ = ‖u - p‖ := norm_sub_rev _ _
  rw [n1, n2, e2]
  nlinarith [h]

end YProx

section YProx2
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma yprox_comb (K : Set V) (X : V → ℝ) (hX : ConvexOn ℝ K X)
    (g xp xagp xk xag xmd x : V) (α β lam : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ : 0 < β) (hlam : 0 < lam) (hαl : α * lam ≤ β)
    (hxmd : xmd = (1 - α) • xagp + α • xp)
    (hagp : α = 1 ∨ xagp ∈ K) (hxk : xk ∈ K) (hx : x ∈ K)
    (h1 : ∀ u ∈ K, inner ℝ g (xk - u) + X xk ≤
      X u + 1 / (2 * lam) * (‖xp - u‖ ^ 2 - ‖xk - u‖ ^ 2 - ‖xk - xp‖ ^ 2))
    (h2 : ∀ u ∈ K, inner ℝ g (xag - u) + X xag ≤
      X u + 1 / (2 * β) * (‖xmd - u‖ ^ 2 - ‖xag - u‖ ^ 2 - ‖xag - xmd‖ ^ 2)) :
    inner ℝ g (xag - α • x - (1 - α) • xagp) + X xag ≤
      (1 - α) * X xagp + α * X x + α / (2 * lam) * (‖xp - x‖ ^ 2 - ‖xk - x‖ ^ 2) -
        1 / (2 * β) * ‖xag - xmd‖ ^ 2 := by
  set u : V := (1 - α) • xagp + α • xk with hu
  have huK : u ∈ K ∧ X u ≤ (1 - α) * X xagp + α * X xk := by
    rcases hagp with h | h
    · have : u = xk := by rw [hu, h]; simp
      rw [this, h]; simp [hxk]
    · refine ⟨hX.1 h hxk (by linarith) hα0 (by ring), ?_⟩
      have := hX.2 h hxk (by linarith) hα0 (by ring : (1 - α) + α = 1)
      simpa [smul_eq_mul] using this
  have A := h2 u huK.1
  have B := h1 x hx
  have hn : ‖xmd - u‖ ^ 2 = α ^ 2 * ‖xp - xk‖ ^ 2 := by
    have : xmd - u = α • (xp - xk) := by rw [hxmd, hu]; module
    rw [this, norm_smul, mul_pow, Real.norm_of_nonneg hα0]
  have hin : inner ℝ g (xag - α • x - (1 - α) • xagp) =
      inner ℝ g (xag - u) + α * inner ℝ g (xk - x) := by
    have : xag - α • x - (1 - α) • xagp = (xag - u) + α • (xk - x) := by rw [hu]; module
    rw [this, inner_add_right, inner_smul_right]
  have hc : α ^ 2 / (2 * β) ≤ α / (2 * lam) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hα0 hα0, mul_nonneg hα0 (sub_nonneg.mpr hαl)]
  have hc2 := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖xp - xk‖)
  have hB := mul_le_mul_of_nonneg_left B hα0
  have hnn : 0 ≤ 1 / (2 * β) * ‖xag - u‖ ^ 2 := by positivity
  have hsw : ‖xk - xp‖ = ‖xp - xk‖ := norm_sub_rev _ _
  rw [hn] at A
  rw [hsw] at hB
  rw [hin]
  have e1 : 1 / (2 * β) * (α ^ 2 * ‖xp - xk‖ ^ 2 - ‖xag - u‖ ^ 2 - ‖xag - xmd‖ ^ 2)
      = α ^ 2 / (2 * β) * ‖xp - xk‖ ^ 2 - 1 / (2 * β) * ‖xag - u‖ ^ 2
        - 1 / (2 * β) * ‖xag - xmd‖ ^ 2 := by ring
  have e2 : α * (1 / (2 * lam) * (‖xp - x‖ ^ 2 - ‖xk - x‖ ^ 2 - ‖xp - xk‖ ^ 2))
      = α / (2 * lam) * (‖xp - x‖ ^ 2 - ‖xk - x‖ ^ 2) - α / (2 * lam) * ‖xp - xk‖ ^ 2 := by ring
  rw [e1] at A
  nlinarith [A, hB, hc2, hnn, huK.2, e2]

end YProx2

theorem prior_eq_3_34 {n : ℕ} (gΨ : E n → E n) (K : Set (E n)) (X : E n → ℝ)
    (hX : ConvexOn ℝ K X) (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P)
    {Ξ : Type*} (G : E n → Ξ → E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n)
    {Ω : Type*} (ξ : ℕ → Ω → Ξ) :
    let xk : ℕ → Ω → E n := xSeq G P α β lam m x0 ξ
    let xag : ℕ → Ω → E n := xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → E n := xmdSeq G P α β lam m x0 ξ
    let δ : ℕ → Ω → E n := deltaBar G gΨ P α β lam m x0 ξ
    ∀ ω : Ω, ∀ k, 1 ≤ k → α k * lam k ≤ β k → ∀ x ∈ K,
      inner ℝ (gΨ (xmd k ω) + δ k ω) (xag k ω - α k • x - (1 - α k) • xag (k - 1) ω) +
          X (xag k ω) ≤
        (1 - α k) * X (xag (k - 1) ω) + α k * X x +
          α k / (2 * lam k) * (‖xk (k - 1) ω - x‖ ^ 2 - ‖xk k ω - x‖ ^ 2) -
          1 / (2 * β k) * ‖xag k ω - xmd k ω‖ ^ 2 := by
  intro xk xag xmd δ ω k hk hab x hx
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hlam : 0 < lam (j + 1) := hstep.2.2.2.1 (j + 1) (by omega)
  have hβ : 0 < β (j + 1) := hstep.2.2.1 (j + 1) (by omega)
  have hg : gΨ (xmd (j + 1) ω) + δ (j + 1) ω =
      sampleAvg G m (j + 1) (xmd (j + 1) ω) (fun i => ξ i ω) := by
    show gΨ (xmd (j + 1) ω) + (Gbar G P α β lam m x0 ξ (j + 1) ω - gΨ (xmd (j + 1) ω)) = _
    rw [add_sub_cancel]; rfl
  set g := gΨ (xmd (j + 1) ω) + δ (j + 1) ω with hgdef
  have e1 : xk (j + 1) ω = P (xk j ω) g (lam (j + 1)) := by rw [hg]; rfl
  have e2 : xag (j + 1) ω = P (xmd (j + 1) ω) g (β (j + 1)) := by rw [hg]; rfl
  have e3 : xk (j + 1 - 1) ω = xk j ω := rfl
  have e4 : xag (j + 1 - 1) ω = xag j ω := rfl
  have e5 : xmd (j + 1) ω = (1 - α (j + 1)) • xag j ω + α (j + 1) • xk j ω := rfl
  have hα : 0 ≤ α (j + 1) ∧ α (j + 1) ≤ 1 := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; rw [hstep.1]; norm_num
    · have := hstep.2.1 (j + 1) (by omega); exact ⟨this.1.le, this.2.le⟩
  have hagp : α (j + 1) = 1 ∨ xag j ω ∈ K := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; left; exact hstep.1
    · right
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hgi : gΨ (xmd (i + 1) ω) + δ (i + 1) ω =
          sampleAvg G m (i + 1) (xmd (i + 1) ω) (fun i => ξ i ω) := by
        show gΨ (xmd (i + 1) ω) + (Gbar G P α β lam m x0 ξ (i + 1) ω - gΨ (xmd (i + 1) ω)) = _
        rw [add_sub_cancel]; rfl
      have e6 : xag (i + 1) ω = P (xmd (i + 1) ω) (gΨ (xmd (i + 1) ω) + δ (i + 1) ω) (β (i + 1)) := by
        rw [hgi]; rfl
      rw [e6]
      exact (hP _ _ _ (hstep.2.2.1 (i + 1) (by omega))).1
  have hxkK : xk (j + 1) ω ∈ K := by rw [e1]; exact (hP _ _ _ hlam).1
  rw [e3, e4]
  exact yprox_comb K X hX g (xk j ω) (xag j ω) (xk (j + 1) ω) (xag (j + 1) ω) (xmd (j + 1) ω) x
    (α (j + 1)) (β (j + 1)) (lam (j + 1)) hα.1 hα.2 hβ hlam hab e5 hagp hxkK hx
    (fun u hu => by
      have := yprox_three K X hX (xk j ω) g (xk (j + 1) ω) (lam (j + 1)) hlam
        (by rw [e1]; exact (hP _ _ _ hlam).1) (by rw [e1]; exact (hP _ _ _ hlam).2) u hu
      exact this)
    (fun u hu => by
      have := yprox_three K X hX (xmd (j + 1) ω) g (xag (j + 1) ω) (β (j + 1)) hβ
        (by rw [e2]; exact (hP _ _ _ hβ).1) (by rw [e2]; exact (hP _ _ _ hβ).2) u hu
      exact this)

end PriorVebis334

namespace PriorVebis247
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

open ConvexOptAlg.SmoothGD

abbrev EE (n : ℕ) := EuclideanSpace ℝ (Fin n)

lemma nac_hasDerivAt_line {n : ℕ} (Ψ : EE n → ℝ) (g : EE n → EE n) (L : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g L) (x d : EE n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Ψ (x + s • d)) (inner ℝ (g (x + t • d)) d) t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have h2 := (hΨ.2.1 (x + t • d)).hasFDerivAt
  have := h2.comp_hasDerivAt t h1
  simp only [InnerProductSpace.toDual_apply_apply] at this
  exact this


lemma nac_descent {n : ℕ} (Ψ : EE n → ℝ) (g : EE n → EE n) (L : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g L) (x y : EE n) :
    Ψ y ≤ Ψ x + inner ℝ (g x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  set d := y - x with hd
  set ψ : ℝ → ℝ := fun t => Ψ (x + t • d) - t * inner ℝ (g x) d - L / 2 * t ^ 2 * ‖d‖ ^ 2 with hψ
  have hder : ∀ t, HasDerivAt ψ
      (inner ℝ (g (x + t • d)) d - inner ℝ (g x) d - L * t * ‖d‖ ^ 2) t := by
    intro t
    have h1 := nac_hasDerivAt_line Ψ g L hΨ x d t
    have h2 : HasDerivAt (fun s : ℝ => s * inner ℝ (g x) d) (inner ℝ (g x) d) t := by
      simpa using (hasDerivAt_id t).mul_const (inner ℝ (g x) d)
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖d‖ ^ 2) (L * t * ‖d‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖d‖ ^ 2)
      exact this.congr_deriv (by rw [show (2:ℕ) - 1 = 1 from rfl]; push_cast; ring)
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact (fun t _ => (hder t).continuousAt.continuousWithinAt)
    · exact (fun t _ => (hder t).differentiableAt.differentiableWithinAt)
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hder t).deriv]
      have h1 : inner ℝ (g (x + t • d)) d - inner ℝ (g x) d = inner ℝ (g (x + t • d) - g x) d := by
        rw [inner_sub_left]
      have h2 : inner ℝ (g (x + t • d) - g x) d ≤ ‖g (x + t • d) - g x‖ * ‖d‖ :=
        real_inner_le_norm _ _
      have h3 : ‖g (x + t • d) - g x‖ ≤ L * ‖t • d‖ := by
        have := hΨ.2.2 (x + t • d) x
        simpa using this
      have h4 : ‖t • d‖ = t * ‖d‖ := by
        rw [norm_smul, Real.norm_of_nonneg ht.1.le]
      have h5 : ‖g (x + t • d) - g x‖ * ‖d‖ ≤ L * (t * ‖d‖) * ‖d‖ := by
        rw [h4] at h3
        exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      nlinarith
  have := hanti (Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩) (Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩)
    zero_le_one
  simp only [hψ] at this
  have hxd : x + d = y := by simp [hd]
  simp at this
  rw [hxd] at this
  linarith

lemma nac_grad_ineq {n : ℕ} (Ψ : EE n → ℝ) (g : EE n → EE n) (L : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g L) (hconv : ConvexOn ℝ Set.univ Ψ)
    (w z : EE n) : Ψ w + inner ℝ (g w) (z - w) ≤ Ψ z := by
  set d := z - w with hd
  have hφ : ConvexOn ℝ Set.univ (fun t : ℝ => Ψ (w + t • d)) := by
    refine ⟨convex_univ, fun a _ b _ s t hs ht hst => ?_⟩
    have h := hconv.2 (Set.mem_univ (w + a • d)) (Set.mem_univ (w + b • d)) hs ht hst
    obtain rfl : t = 1 - s := by linarith
    have : w + (s * a + (1 - s) * b) • d = s • (w + a • d) + (1 - s) • (w + b • d) := by
      module
    simp only [smul_eq_mul] at h ⊢
    rw [this]; exact h
  have h0 := nac_hasDerivAt_line Ψ g L hΨ w d 0
  simp only [zero_smul, add_zero] at h0
  have := hφ.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one h0
  rw [slope_def_field] at this
  simp at this
  have hy : w + d = z := by simp [hd]
  rw [hy] at this
  linarith

lemma nac_lower {n : ℕ} (Ψ : EuclideanSpace ℝ (Fin n) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (L : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g L) (x y : EuclideanSpace ℝ (Fin n)) :
    Ψ x + inner ℝ (g x) (y - x) - L / 2 * ‖y - x‖ ^ 2 ≤ Ψ y := by
  set d := y - x with hd
  set ψ : ℝ → ℝ := fun t => Ψ (x + t • d) - t * inner ℝ (g x) d + L / 2 * t ^ 2 * ‖d‖ ^ 2 with hψ
  have hder : ∀ t, HasDerivAt ψ
      (inner ℝ (g (x + t • d)) d - inner ℝ (g x) d + L * t * ‖d‖ ^ 2) t := by
    intro t
    have h1 := nac_hasDerivAt_line Ψ g L hΨ x d t
    have h2 : HasDerivAt (fun s : ℝ => s * inner ℝ (g x) d) (inner ℝ (g x) d) t := by
      simpa using (hasDerivAt_id t).mul_const (inner ℝ (g x) d)
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖d‖ ^ 2) (L * t * ‖d‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖d‖ ^ 2)
      exact this.congr_deriv (by rw [show (2:ℕ) - 1 = 1 from rfl]; push_cast; ring)
    exact (h1.sub h2).add h3
  have hmono : MonotoneOn ψ (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact (fun t _ => (hder t).continuousAt.continuousWithinAt)
    · exact (fun t _ => (hder t).differentiableAt.differentiableWithinAt)
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hder t).deriv]
      have h1 : inner ℝ (g (x + t • d)) d - inner ℝ (g x) d = inner ℝ (g (x + t • d) - g x) d := by
        rw [inner_sub_left]
      have h2 : -(‖g (x + t • d) - g x‖ * ‖d‖) ≤ inner ℝ (g (x + t • d) - g x) d := by
        have := abs_real_inner_le_norm (g (x + t • d) - g x) d
        exact (abs_le.mp this).1
      have h3 : ‖g (x + t • d) - g x‖ ≤ L * ‖t • d‖ := by
        have := hΨ.2.2 (x + t • d) x
        simpa using this
      have h4 : ‖t • d‖ = t * ‖d‖ := by
        rw [norm_smul, Real.norm_of_nonneg ht.1.le]
      have h5 : ‖g (x + t • d) - g x‖ * ‖d‖ ≤ L * (t * ‖d‖) * ‖d‖ := by
        rw [h4] at h3
        exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      nlinarith
  have := hmono (Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩) (Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩)
    zero_le_one
  simp only [hψ] at this
  have hxd : x + d = y := by simp [hd]
  simp at this
  rw [hxd] at this
  linarith

lemma nac_main {n : ℕ} (f h : EuclideanSpace ℝ (Fin n) → ℝ) (gf gh : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h) :
    ∀ x y : EuclideanSpace ℝ (Fin n),
      -(Lf / 2) * ‖y - x‖ ^ 2 ≤ (f y + h y) - (f x + h x) - inner ℝ (gf x + gh x) (y - x) ∧
        (f y + h y) - (f x + h x) - inner ℝ (gf x + gh x) (y - x) ≤
          (Lf + Lh) / 2 * ‖y - x‖ ^ 2 := by
  intro x y
  have h1 := nac_lower f gf Lf hf x y
  have h2 := nac_descent f gf Lf hf x y
  have h3 := nac_descent h gh Lh hh x y
  have h4 := nac_grad_ineq h gh Lh hh hhc x y
  rw [inner_add_left]
  constructor <;> nlinarith


lemma nac_47 {n : ℕ} (f h : EE n → ℝ) (gf gh : EE n → EE n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (xag xp x : EE n) :
    (f ((1 - α) • xag + α • xp) + h ((1 - α) • xag + α • xp))
        - ((1 - α) * (f xag + h xag) + α * (f x + h x)) ≤
      inner ℝ (gf ((1 - α) • xag + α • xp) + gh ((1 - α) • xag + α • xp))
          (((1 - α) • xag + α • xp) - α • x - (1 - α) • xag) +
        Lf * α / 2 * ‖((1 - α) • xag + α • xp) - x‖ ^ 2 +
        Lf * α ^ 2 * (1 - α) / 2 * ‖xag - xp‖ ^ 2 := by
  set md := (1 - α) • xag + α • xp with hmd
  have A := (nac_main f h gf gh Lf Lh hf hh hhc md xag).1
  have B := (nac_main f h gf gh Lf Lh hf hh hhc md x).1
  have hn : ‖xag - md‖ ^ 2 = α ^ 2 * ‖xag - xp‖ ^ 2 := by
    have : xag - md = α • (xag - xp) := by rw [hmd]; module
    rw [this, norm_smul, mul_pow, Real.norm_of_nonneg hα0]
  have hv : md - α • x - (1 - α) • xag = -((1 - α) • (xag - md) + α • (x - md)) := by
    rw [hmd]; module
  rw [hv, inner_neg_right, inner_add_right, inner_smul_right, inner_smul_right]
  have h1 := mul_le_mul_of_nonneg_left A (sub_nonneg.mpr hα1)
  have h2 := mul_le_mul_of_nonneg_left B hα0
  rw [hn] at h1
  rw [norm_sub_rev x md] at h2
  nlinarith [h1, h2]

theorem prior_eq_2_47 {n : ℕ} (f h : GhadimiLan.RSG.E n → ℝ) (gf gh : GhadimiLan.RSG.E n → GhadimiLan.RSG.E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (Ψ : GhadimiLan.RSG.E n → ℝ) (gΨ : GhadimiLan.RSG.E n → GhadimiLan.RSG.E n) (LΨ : ℝ) (hΨ : Ψ = fun x => f x + h x)
    (hgΨ : gΨ = fun x => gf x + gh x) (hLΨ : LΨ = Lf + Lh)
    (P : GhadimiLan.RSG.E n → GhadimiLan.RSG.E n → ℝ → GhadimiLan.RSG.E n) {Ξ : Type*} (G : GhadimiLan.RSG.E n → Ξ → GhadimiLan.RSG.E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : NonconvexAG.StochComposite.RSAGStepsizes α β lam m) (x0 : GhadimiLan.RSG.E n)
    {Ω : Type*} (ξ : ℕ → Ω → Ξ) :
    let xk : ℕ → Ω → GhadimiLan.RSG.E n := NonconvexAG.StochComposite.xSeq G P α β lam m x0 ξ
    let xag : ℕ → Ω → GhadimiLan.RSG.E n := NonconvexAG.StochComposite.xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → GhadimiLan.RSG.E n := NonconvexAG.StochComposite.xmdSeq G P α β lam m x0 ξ
    ∀ ω : Ω, ∀ k, 1 ≤ k → ∀ x : GhadimiLan.RSG.E n,
      Ψ (xmd k ω) - ((1 - α k) * Ψ (xag (k - 1) ω) + α k * Ψ x) ≤
        inner ℝ (gΨ (xmd k ω)) (xmd k ω - α k • x - (1 - α k) • xag (k - 1) ω) +
          Lf * α k / 2 * ‖xmd k ω - x‖ ^ 2 +
          Lf * α k ^ 2 * (1 - α k) / 2 * ‖xag (k - 1) ω - xk (k - 1) ω‖ ^ 2 := by
  intro xk xag xmd ω k hk x
  subst hΨ hgΨ
  have hα0 : 0 ≤ α k := by
    rcases Nat.eq_or_lt_of_le hk with h' | h'
    · subst h'; rw [hstep.1]; norm_num
    · exact (hstep.2.1 k (by omega)).1.le
  have hα1 : α k ≤ 1 := by
    rcases Nat.eq_or_lt_of_le hk with h' | h'
    · subst h'; rw [hstep.1]
    · exact (hstep.2.1 k (by omega)).2.le
  have := nac_47 f h gf gh Lf Lh hf hh hhc (α k) hα0 hα1 (xag (k - 1) ω) (xk (k - 1) ω) x
  exact this

end PriorVebis247

namespace ProxYoungResearch

lemma noise_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (b L : ℝ) (hb : 0 < b) (hL : L * b < 1) (d u : V) :
    -inner ℝ d u ≤ (1 / b - L) / 4 * ‖u‖ ^ 2 + b * ‖d‖ ^ 2 / (1 - L * b) := by
  have ht : 0 < 1 / b - L := sub_pos.mpr ((lt_div_iff₀ hb).mpr hL)
  have hq : 0 < 1 - L * b := by linarith
  have hcs : -inner ℝ d u ≤ ‖d‖ * ‖u‖ := by
    have hh := (abs_le.mp (abs_real_inner_le_norm d u)).1
    linarith
  have hh : (-inner ℝ d u) * (1 / b - L) ≤
      (1 / b - L) ^ 2 / 4 * ‖u‖ ^ 2 + ‖d‖ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hcs ht.le
    nlinarith only [hmul, sq_nonneg ((1 / b - L) * ‖u‖ - 2 * ‖d‖)]
  calc
    -inner ℝ d u ≤ ((1 / b - L) ^ 2 / 4 * ‖u‖ ^ 2 + ‖d‖ ^ 2) / (1 / b - L) :=
      (le_div_iff₀ ht).mpr hh
    _ = (1 / b - L) / 4 * ‖u‖ ^ 2 + b * ‖d‖ ^ 2 / (1 - L * b) := by
      field_simp

end ProxYoungResearch

open GhadimiLan.RSG (E)
open ConvexOptAlg.SmoothGD NonconvexAG.StochComposite

theorem prior_young {n : ℕ} (f h : E n → ℝ) (gf gh : E n → E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (Ψ : E n → ℝ) (gΨ : E n → E n) (LΨ : ℝ) (hΨ : Ψ = fun x => f x + h x)
    (hgΨ : gΨ = fun x => gf x + gh x) (hLΨ : LΨ = Lf + Lh)
    (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P) {Ξ : Type*} (G : E n → Ξ → E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n)
    {Ω : Type*} (ξ : ℕ → Ω → Ξ) :
    let Φ : E n → ℝ := fun x => Ψ x + X x
    let xk : ℕ → Ω → E n := xSeq G P α β lam m x0 ξ
    let xag : ℕ → Ω → E n := xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → E n := xmdSeq G P α β lam m x0 ξ
    let δ : ℕ → Ω → E n := deltaBar G gΨ P α β lam m x0 ξ
    ∀ ω : Ω, ∀ k, 1 ≤ k → α k * lam k ≤ β k → LΨ * β k < 1 → ∀ x ∈ K,
      Φ (xag k ω) ≤ (1 - α k) * Φ (xag (k - 1) ω) + α k * Φ x +
          inner ℝ (δ k ω) (α k • (x - xk (k - 1) ω)) -
          1 / 4 * (1 / β k - LΨ) * ‖xag k ω - xmd k ω‖ ^ 2 +
          β k * ‖δ k ω‖ ^ 2 / (1 - LΨ * β k) +
          α k / (2 * lam k) * (‖xk (k - 1) ω - x‖ ^ 2 - ‖xk k ω - x‖ ^ 2) +
          Lf * α k / 2 * ‖xmd k ω - x‖ ^ 2 +
          Lf * α k ^ 2 * (1 - α k) / 2 * ‖xag (k - 1) ω - xk (k - 1) ω‖ ^ 2 := by
  intro Φ xk xag xmd δ ω k hk hab hLb x hx
  have hp := PriorVebis334.prior_eq_3_34 gΨ K X hX P hP G α β lam m hstep x0 ξ ω k hk hab x hx
  have hc := PriorVebis247.prior_eq_2_47 f h gf gh Lf Lh hf hh hhc Ψ gΨ LΨ hΨ hgΨ hLΨ
    P G α β lam m hstep x0 ξ ω k hk x
  change inner ℝ (gΨ (xmd k ω) + δ k ω)
      (xag k ω - α k • x - (1 - α k) • xag (k - 1) ω) + X (xag k ω) ≤ _ at hp
  change Ψ (xmd k ω) - ((1 - α k) * Ψ (xag (k - 1) ω) + α k * Ψ x) ≤ _ at hc
  have hd : Ψ (xag k ω) ≤ Ψ (xmd k ω) +
      inner ℝ (gΨ (xmd k ω)) (xag k ω - xmd k ω) + LΨ / 2 * ‖xag k ω - xmd k ω‖ ^ 2 := by
    have hh := (PriorVebis247.nac_main f h gf gh Lf Lh hf hh hhc (xmd k ω) (xag k ω)).2
    rw [hΨ, hgΨ, hLΨ]
    dsimp only
    linarith only [hh]
  have hy := ProxYoungResearch.noise_bound (β k) LΨ (hstep.2.2.1 k hk) hLb
    (δ k ω) (xag k ω - xmd k ω)
  have hmd : xmd k ω = (1 - α k) • xag (k - 1) ω + α k • xk (k - 1) ω := rfl
  have hn : inner ℝ (δ k ω) (xmd k ω) =
      (1 - α k) * inner ℝ (δ k ω) (xag (k - 1) ω) +
      α k * inner ℝ (δ k ω) (xk (k - 1) ω) := by
    rw [hmd, inner_add_right, inner_smul_right, inner_smul_right]
  dsimp only [Φ, xk, xag, xmd, δ] at hp hc hd hy hn ⊢
  simp only [inner_add_left, inner_sub_right, inner_smul_right] at hp hc hd hy ⊢
  norm_num [div_eq_mul_inv, mul_inv_rev] at hp hc hd hy ⊢
  nlinarith only [hp, hc, hd, hy, hn]

#print axioms ProxYoungResearch.noise_bound
#print axioms prior_young

namespace ProxSumResearch
lemma telescope (U D R : ℕ → ℝ) (C : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (hbase : U 1 + D 1 ≤ C + R 1)
    (hs : ∀ k ∈ Finset.Icc 1 N, 2 ≤ k → U k + D k ≤ U (k - 1) + R k) :
    U N + ∑ k ∈ Finset.Icc 1 N, D k ≤ C + ∑ k ∈ Finset.Icc 1 N, R k := by
  have hall : ∀ j, 1 ≤ j → j ≤ N →
      U j + ∑ k ∈ Finset.Icc 1 j, D k ≤ C + ∑ k ∈ Finset.Icc 1 j, R k := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; simpa using hbase
    | succ j hj ih =>
      intro hjN
      have hi := ih (by omega)
      have hh := hs (j + 1) (Finset.mem_Icc.mpr ⟨by omega, hjN⟩) (by omega)
      simp only [Nat.add_sub_cancel] at hh
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      linarith only [hi, hh]
  exact hall N hN le_rfl
end ProxSumResearch


open GhadimiLan.RSG (E)
open ConvexOptAlg.SmoothGD

/-- §3.2, last display of p. 22: the summed inequality along Algorithm 4, for every realization
`ω`, every `N ≥ 1` and every `x` in the domain `K` of `𝒳`, when (2.9)
(`αₖλₖ ≤ βₖ`, `L_Ψ βₖ < 1`) and (2.10) hold for `k = 1, …, N`. -/
theorem prior_summed {n : ℕ} (f h : E n → ℝ) (gf gh : E n → E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (Ψ : E n → ℝ) (gΨ : E n → E n) (LΨ : ℝ) (hΨ : Ψ = fun x => f x + h x)
    (hgΨ : gΨ = fun x => gf x + gh x) (hLΨ : LΨ = Lf + Lh)
    (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P) {Ξ : Type*} (G : E n → Ξ → E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n)
    {Ω : Type*} (ξ : ℕ → Ω → Ξ)
    (N : ℕ) (hN : 1 ≤ N) (h29 : ∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ β k ∧ LΨ * β k < 1)
    (h210 : ∀ k ∈ Finset.Icc 1 N, 2 ≤ k →
      α k / (lam k * NonconvexAG.Smooth.Gamma α k) ≤ α (k - 1) / (lam (k - 1) * NonconvexAG.Smooth.Gamma α (k - 1))) :
    let Φ : E n → ℝ := fun x => Ψ x + X x
    let xk : ℕ → Ω → E n := xSeq G P α β lam m x0 ξ
    let xag : ℕ → Ω → E n := xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → E n := xmdSeq G P α β lam m x0 ξ
    let δ : ℕ → Ω → E n := deltaBar G gΨ P α β lam m x0 ξ
    ∀ ω : Ω, ∀ x ∈ K,
      (Φ (xag N ω) - Φ x) / NonconvexAG.Smooth.Gamma α N +
          ∑ k ∈ Finset.Icc 1 N,
            (1 - LΨ * β k) / (4 * β k * NonconvexAG.Smooth.Gamma α k) * ‖xag k ω - xmd k ω‖ ^ 2 ≤
        ‖x0 - x‖ ^ 2 / (2 * lam 1) +
          ∑ k ∈ Finset.Icc 1 N, α k / NonconvexAG.Smooth.Gamma α k * inner ℝ (δ k ω) (x - xk (k - 1) ω) +
          Lf / 2 * ∑ k ∈ Finset.Icc 1 N, α k / NonconvexAG.Smooth.Gamma α k *
            (‖xmd k ω - x‖ ^ 2 + α k * (1 - α k) * ‖xag (k - 1) ω - xk (k - 1) ω‖ ^ 2) +
          ∑ k ∈ Finset.Icc 1 N, β k * ‖δ k ω‖ ^ 2 / (NonconvexAG.Smooth.Gamma α k * (1 - LΨ * β k)) := by
  intro Φ xk xag xmd δ ω x hx
  let γ := NonconvexAG.Smooth.Gamma α
  have hg (k : ℕ) : 0 < γ k := by
    apply Finset.prod_pos
    intro i hi
    have hh := (hstep.2.1 i (Finset.mem_Icc.mp hi).1).2
    linarith
  have hg1 : γ 1 = 1 := by simp [γ, NonconvexAG.Smooth.Gamma]
  have hgstep (k : ℕ) (hk : 2 ≤ k) : γ k = (1 - α k) * γ (k - 1) := by
    have he : k = (k - 1) + 1 := by omega
    conv_lhs => rw [he]
    dsimp [γ, NonconvexAG.Smooth.Gamma]
    rw [Finset.prod_Icc_succ_top (by omega)]
    rw [← he]
    ring
  let a := fun k => (α k / (2 * lam k)) / γ k
  let U := fun k => (Φ (xag k ω) - Φ x) / γ k + a k * ‖xk k ω - x‖ ^ 2
  let D := fun k => (1 / 4 * (1 / β k - LΨ) * ‖xag k ω - xmd k ω‖ ^ 2) / γ k
  let R := fun k => (inner ℝ (δ k ω) (α k • (x - xk (k - 1) ω)) +
    Lf * α k / 2 * ‖xmd k ω - x‖ ^ 2 +
    Lf * α k ^ 2 * (1 - α k) / 2 * ‖xag (k - 1) ω - xk (k - 1) ω‖ ^ 2 +
    β k * ‖δ k ω‖ ^ 2 / (1 - LΨ * β k)) / γ k
  have step (k : ℕ) (hk : k ∈ Finset.Icc 1 N) : U k + D k ≤
      ((1 - α k) * (Φ (xag (k - 1) ω) - Φ x)) / γ k +
      a k * ‖xk (k - 1) ω - x‖ ^ 2 + R k := by
    have h := prior_young f h gf gh Lf Lh hf hh hhc Ψ gΨ LΨ hΨ hgΨ hLΨ
      K X hX P hP G α β lam m hstep x0 ξ ω k (Finset.mem_Icc.mp hk).1
      (h29 k hk).1 (h29 k hk).2 x hx
    have hd := div_le_div_of_nonneg_right h (hg k).le
    dsimp only [Φ, xk, xag, xmd, δ, U, D, R, a] at hd ⊢
    norm_num [div_eq_mul_inv, mul_inv_rev] at hd ⊢
    nlinarith only [hd]
  have hbase : U 1 + D 1 ≤ ‖x0 - x‖ ^ 2 / (2 * lam 1) + R 1 := by
    have hs := step 1 (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)
    have he : a 1 * ‖xk 0 ω - x‖ ^ 2 = ‖x0 - x‖ ^ 2 / (2 * lam 1) := by
      simp [a, hg1, hstep.1, xk, xSeq, rsagPath, div_eq_mul_inv, mul_comm]
    rw [hstep.1] at hs
    simpa only [sub_self, zero_mul, zero_div, zero_add, Nat.sub_self, he] using hs
  have hrec : ∀ k ∈ Finset.Icc 1 N, 2 ≤ k → U k + D k ≤ U (k - 1) + R k := by
    intro k hk hk2
    have hm : a k ≤ a (k - 1) := by
      have hh := mul_le_mul_of_nonneg_left (h210 k hk hk2) (show (0:ℝ) ≤ 1/2 by norm_num)
      dsimp [a, γ]
      norm_num [div_eq_mul_inv, mul_inv_rev] at hh ⊢
      nlinarith only [hh]
    have he : ((1 - α k) * (Φ (xag (k - 1) ω) - Φ x)) / γ k =
        (Φ (xag (k - 1) ω) - Φ x) / γ (k - 1) := by
      rw [hgstep k hk2]
      have ha : 1 - α k ≠ 0 := ne_of_gt (sub_pos.mpr (hstep.2.1 k hk2).2)
      field_simp
    have hm' := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖xk (k - 1) ω - x‖)
    have hs := step k hk
    rw [he] at hs
    dsimp only [U]
    linarith only [hs, hm']
  have ht := ProxSumResearch.telescope U D R (‖x0 - x‖ ^ 2 / (2 * lam 1)) N hN hbase hrec
  have hd : ∑ k ∈ Finset.Icc 1 N, D k = ∑ k ∈ Finset.Icc 1 N,
      (1 - LΨ * β k) / (4 * β k * γ k) * ‖xag k ω - xmd k ω‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    have hb := hstep.2.2.1 k (Finset.mem_Icc.mp hk).1
    dsimp [D]
    field_simp
    <;> ring
  have hr : ∑ k ∈ Finset.Icc 1 N, R k =
      (∑ k ∈ Finset.Icc 1 N, α k / γ k * inner ℝ (δ k ω) (x - xk (k - 1) ω)) +
      Lf / 2 * (∑ k ∈ Finset.Icc 1 N, α k / γ k *
        (‖xmd k ω - x‖ ^ 2 + α k * (1 - α k) * ‖xag (k - 1) ω - xk (k - 1) ω‖ ^ 2)) +
      ∑ k ∈ Finset.Icc 1 N, β k * ‖δ k ω‖ ^ 2 / (γ k * (1 - LΨ * β k)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [R]
    simp only [inner_smul_right, div_eq_mul_inv, mul_inv_rev]
    ring
  have ha : 0 ≤ α N := by
    rcases Nat.eq_or_lt_of_le hN with he | he
    · subst N; rw [hstep.1]; norm_num
    · exact (hstep.2.1 N (by omega)).1.le
  have haN : 0 ≤ a N := by
    dsimp [a]
    exact div_nonneg (div_nonneg ha (by have := hstep.2.2.2.1 N hN; positivity)) (hg N).le
  have hn := mul_nonneg haN (sq_nonneg ‖xk N ω - x‖)
  rw [hd, hr] at ht
  dsimp only [U] at ht
  change (Φ (xag N ω) - Φ x) / γ N + _ ≤ _
  linarith only [ht, hn]



#print axioms prior_summed

-- The complete accepted iterate-bound declaration and body, with imports consolidated.
theorem prior_bound {n : ℕ} (P : E n → E n → ℝ → E n) (M : ℝ) (hA2 : Assumption2 P M)
    {Ξ : Type*} (G : E n → Ξ → E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n)
    (hx0 : ‖x0‖ ≤ M) {Ω : Type*} (ξ : ℕ → Ω → Ξ) :
    let xk : ℕ → Ω → E n := xSeq G P α β lam m x0 ξ
    let xag : ℕ → Ω → E n := xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → E n := xmdSeq G P α β lam m x0 ξ
    ∀ ω : Ω, ∀ k, 1 ≤ k → ∀ xstar : E n,
      ‖xmd k ω - xstar‖ ^ 2 + α k * (1 - α k) * ‖xag (k - 1) ω - xk (k - 1) ω‖ ^ 2 ≤
        2 * (‖xstar‖ ^ 2 + 2 * M ^ 2) := by
  intro xk xag xmd ω k hk xstar
  have hM : 0 ≤ M := (norm_nonneg x0).trans hx0
  have hb (j : ℕ) : ‖xk j ω‖ ≤ M ∧ ‖xag j ω‖ ≤ M := by
    cases j with
    | zero => simpa [xk, xag, xSeq, xagSeq, rsagPath] using And.intro hx0 hx0
    | succ j =>
      change ‖P _ _ (lam (j + 1))‖ ≤ M ∧ ‖P _ _ (β (j + 1))‖ ≤ M
      exact ⟨hA2 _ _ _ (hstep.2.2.2.1 (j + 1) (by omega)),
        hA2 _ _ _ (hstep.2.2.1 (j + 1) (by omega))⟩
  have ha0 : 0 ≤ α k := by
    rcases Nat.eq_or_lt_of_le hk with he | he
    · subst k; rw [hstep.1]; norm_num
    · exact (hstep.2.1 k (by omega)).1.le
  have ha1 : α k ≤ 1 := by
    rcases Nat.eq_or_lt_of_le hk with he | he
    · subst k; rw [hstep.1]
    · exact (hstep.2.1 k (by omega)).2.le
  have hc0 : 0 ≤ 1 - α k := by linarith
  have hmd : ‖xmd k ω‖ ≤ M := by
    change ‖(1 - α k) • xag (k - 1) ω + α k • xk (k - 1) ω‖ ≤ M
    calc
      _ ≤ ‖(1 - α k) • xag (k - 1) ω‖ + ‖α k • xk (k - 1) ω‖ := norm_add_le _ _
      _ = (1 - α k) * ‖xag (k - 1) ω‖ + α k * ‖xk (k - 1) ω‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hc0, Real.norm_of_nonneg ha0]
      _ ≤ (1 - α k) * M + α k * M := add_le_add
        (mul_le_mul_of_nonneg_left (hb (k - 1)).2 hc0)
        (mul_le_mul_of_nonneg_left (hb (k - 1)).1 ha0)
      _ = M := by ring
  have hmdsq : ‖xmd k ω‖ ^ 2 ≤ M ^ 2 := by
    nlinarith only [mul_self_le_mul_self (norm_nonneg (xmd k ω)) hmd]
  have hdist : ‖xmd k ω - xstar‖ ^ 2 ≤ 2 * M ^ 2 + 2 * ‖xstar‖ ^ 2 := by
    have hs := mul_self_le_mul_self (norm_nonneg (xmd k ω - xstar)) (norm_sub_le (xmd k ω) xstar)
    nlinarith only [hs, hmdsq, sq_nonneg (‖xmd k ω‖ - ‖xstar‖)]
  have hdiff : ‖xag (k - 1) ω - xk (k - 1) ω‖ ≤ 2 * M := by
    have hh := norm_sub_le (xag (k - 1) ω) (xk (k - 1) ω)
    linarith only [hh, (hb (k - 1)).1, (hb (k - 1)).2]
  have hdiffsq : ‖xag (k - 1) ω - xk (k - 1) ω‖ ^ 2 ≤ 4 * M ^ 2 := by
    nlinarith only [mul_self_le_mul_self (norm_nonneg (xag (k - 1) ω - xk (k - 1) ω)) hdiff]
  have hc : α k * (1 - α k) ≤ (1:ℝ) / 4 := by nlinarith only [sq_nonneg (α k - 1/2)]
  have hcross : α k * (1 - α k) * ‖xag (k - 1) ω - xk (k - 1) ω‖ ^ 2 ≤ M ^ 2 := by
    calc
      _ ≤ α k * (1 - α k) * (4 * M ^ 2) :=
        mul_le_mul_of_nonneg_left hdiffsq (mul_nonneg ha0 hc0)
      _ ≤ (1/4:ℝ) * (4 * M ^ 2) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = M ^ 2 := by ring
  nlinarith only [hdist, hcross, sq_nonneg M]



#print axioms prior_bound

open NonconvexAG.StochComposite

open GhadimiLan.RSG (E)
open ConvexOptAlg.SmoothGD

/-- §3.2, first display of p. 23: the summed inequality at `x = x*`, with the `L_f`-terms bounded
by (2.16) and (2.52), along Algorithm 4, for every realization `ω`, every `N ≥ 1` and every
point `x*` of the domain `K` of `𝒳`, under Assumption 2, `‖x₀‖ ≤ M`, and (2.9), (2.10) for
`k = 1, …, N`. -/
theorem prior_xstar {n : ℕ} (f h : E n → ℝ) (gf gh : E n → E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (Ψ : E n → ℝ) (gΨ : E n → E n) (LΨ : ℝ) (hΨ : Ψ = fun x => f x + h x)
    (hgΨ : gΨ = fun x => gf x + gh x) (hLΨ : LΨ = Lf + Lh)
    (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P) {Ξ : Type*} (G : E n → Ξ → E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n)
    (M : ℝ) (hA2 : Assumption2 P M) (hx0 : ‖x0‖ ≤ M)
    {Ω : Type*} (ξ : ℕ → Ω → Ξ)
    (N : ℕ) (hN : 1 ≤ N) (h29 : ∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ β k ∧ LΨ * β k < 1)
    (h210 : ∀ k ∈ Finset.Icc 1 N, 2 ≤ k →
      α k / (lam k * NonconvexAG.Smooth.Gamma α k) ≤ α (k - 1) / (lam (k - 1) * NonconvexAG.Smooth.Gamma α (k - 1))) :
    let Φ : E n → ℝ := fun x => Ψ x + X x
    let xk : ℕ → Ω → E n := xSeq G P α β lam m x0 ξ
    let xag : ℕ → Ω → E n := xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → E n := xmdSeq G P α β lam m x0 ξ
    let δ : ℕ → Ω → E n := deltaBar G gΨ P α β lam m x0 ξ
    ∀ ω : Ω, ∀ xstar ∈ K,
      (Φ (xag N ω) - Φ xstar) / NonconvexAG.Smooth.Gamma α N +
          ∑ k ∈ Finset.Icc 1 N,
            (1 - LΨ * β k) / (4 * β k * NonconvexAG.Smooth.Gamma α k) * ‖xag k ω - xmd k ω‖ ^ 2 ≤
        ‖x0 - xstar‖ ^ 2 / (2 * lam 1) +
          ∑ k ∈ Finset.Icc 1 N, α k / NonconvexAG.Smooth.Gamma α k * inner ℝ (δ k ω) (xstar - xk (k - 1) ω) +
          Lf / NonconvexAG.Smooth.Gamma α N * (‖xstar‖ ^ 2 + 2 * M ^ 2) +
          ∑ k ∈ Finset.Icc 1 N, β k * ‖δ k ω‖ ^ 2 / (NonconvexAG.Smooth.Gamma α k * (1 - LΨ * β k)) := by
  intro Φ xk xag xmd δ ω xstar hx
  let γ := NonconvexAG.Smooth.Gamma α
  have hg (k : ℕ) : 0 < γ k := by
    apply Finset.prod_pos
    intro i hi
    have hh := (hstep.2.1 i (Finset.mem_Icc.mp hi).1).2
    linarith
  have hg1 : γ 1 = 1 := by simp [γ, NonconvexAG.Smooth.Gamma]
  have hgstep (k : ℕ) (hk : 2 ≤ k) : γ k = (1 - α k) * γ (k - 1) := by
    have he : k = (k - 1) + 1 := by omega
    conv_lhs => rw [he]
    dsimp [γ, NonconvexAG.Smooth.Gamma]
    rw [Finset.prod_Icc_succ_top (by omega)]
    rw [← he]
    ring
  have hsum : ∀ N : ℕ, 1 ≤ N → ∑ k ∈ Finset.Icc 1 N, α k / γ k = 1 / γ N := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => simp [hg1, hstep.1]
    | succ j hj ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j+1), ih, hgstep (j+1) (by omega)]
      have he : j+1-1=j := by omega
      rw [he]
      have hne := ne_of_gt (hg j)
      have ha := ne_of_gt (sub_pos.mpr (hstep.2.1 (j+1) (by omega)).2)
      field_simp
      <;> ring
  have ha (k : ℕ) (hk : 1 ≤ k) : 0 ≤ α k := by
    rcases Nat.eq_or_lt_of_le hk with he | he
    · subst k; rw [hstep.1]; norm_num
    · exact (hstep.2.1 k (by omega)).1.le
  have hb : (∑ k ∈ Finset.Icc 1 N, α k / γ k *
      (‖xmd k ω - xstar‖ ^ 2 + α k * (1 - α k) *
      ‖xag (k - 1) ω - xk (k - 1) ω‖ ^ 2)) ≤
      2 * (‖xstar‖ ^ 2 + 2 * M ^ 2) / γ N := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 N, α k / γ k * (2 * (‖xstar‖ ^ 2 + 2 * M ^ 2)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left
          (prior_bound P M hA2 G α β lam m hstep x0 hx0 ξ ω k (Finset.mem_Icc.mp hk).1 xstar)
          (div_nonneg (ha k (Finset.mem_Icc.mp hk).1) (hg k).le)
      _ = _ := by rw [← Finset.sum_mul, hsum N hN]; ring
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ Lf / 2 by exact div_nonneg hf.1 (by norm_num))
  have hs := prior_summed f h gf gh Lf Lh hf hh hhc Ψ gΨ LΨ hΨ hgΨ hLΨ
    K X hX P hP G α β lam m hstep x0 ξ N hN h29 h210 ω xstar hx
  change (Φ (xag N ω) - Φ xstar) / γ N + _ ≤ _ at hs ⊢
  dsimp only [Φ, xk, xag, xmd, δ, γ] at hb' hs ⊢
  simp only [div_eq_mul_inv] at hb' hs ⊢
  nlinarith only [hs, hb']




#print axioms prior_xstar

open scoped Topology
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

theorem prior_gradient_mapping {n : ℕ} (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
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
#print axioms prior_gradient_mapping


set_option maxHeartbeats 800000
namespace BatchResearch
lemma prox_joint_lipschitz {n : ℕ} (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P)
    (x1 y1 x2 y2 : E n) (c : ℝ) (hc : 0 < c) :
    ‖P x1 y1 c-P x2 y2 c‖ ≤ ‖x1-x2‖+c*‖y1-y2‖ := by
  let p1 := P x1 y1 c
  let p2 := P x2 y2 c
  have h1 := ProxResearch.variational K X hX P hP x1 y1 p2 c hc (hP x2 y2 c hc).1
  have h2 := ProxResearch.variational K X hX P hP x2 y2 p1 c hc (hP x1 y1 c hc).1
  change 0 ≤ c*(inner ℝ y1 (p2-p1)+X p2-X p1)+inner ℝ (p1-x1) (p2-p1) at h1
  change 0 ≤ c*(inner ℝ y2 (p1-p2)+X p1-X p2)+inner ℝ (p2-x2) (p1-p2) at h2
  have hf : ‖p1-p2‖^2 ≤ inner ℝ (x1-x2) (p1-p2)+c*inner ℝ (y2-y1) (p1-p2) := by
    rw [norm_sub_sq_real]
    simp only [inner_sub_left,inner_sub_right,real_inner_self_eq_norm_sq] at h1 h2 ⊢
    nlinarith [real_inner_comm p1 p2]
  have hx := real_inner_le_norm (x1-x2) (p1-p2)
  have hy := real_inner_le_norm (y2-y1) (p1-p2)
  rw [norm_sub_rev y2 y1] at hy
  by_cases he : ‖p1-p2‖=0
  · change ‖p1-p2‖ ≤ _
    rw [he]; positivity
  · have hp : 0 < ‖p1-p2‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm he)
    change ‖p1-p2‖ ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hy hc.le]

lemma prox_measurable {n : ℕ} (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P) (c : ℝ) (hc : 0 < c) :
    Measurable (fun p : E n × E n => P p.1 p.2 c) := by
  have hl : LipschitzWith ⟨1+c,by positivity⟩ (fun p : E n × E n => P p.1 p.2 c) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [dist_eq_norm]
    have h := prox_joint_lipschitz K X hX P hP p.1 p.2 q.1 q.2 c hc
    have hx : ‖p.1-q.1‖ ≤ dist p q := le_max_left _ _
    have hy : ‖p.2-q.2‖ ≤ dist p q := le_max_right _ _
    change ‖P p.1 p.2 c-P q.1 q.2 c‖ ≤ (1+c)*dist p q
    nlinarith [mul_le_mul_of_nonneg_left hy hc.le]
  exact hl.continuous.measurable

lemma batchEnd_mono (m : ℕ → ℕ) : Monotone (batchEnd m) := by
  intro k l h
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl h) (fun _ _ _ => Nat.zero_le _)

lemma batchEnd_succ (m : ℕ → ℕ) (k : ℕ) : batchEnd m (k+1) = batchEnd m k+m (k+1) := by
  unfold batchEnd
  exact Finset.sum_Icc_succ_top (f := m) (a := 1) (b := k) (by omega)

lemma batchOf_index (m : ℕ → ℕ) (k i : ℕ) (hk : 1 ≤ k) (hi : i ∈ Finset.Icc 1 (m k)) :
    batchOf m (batchEnd m (k-1)+i) = k := by
  obtain ⟨hi0,hi1⟩ := Finset.mem_Icc.mp hi
  have he : batchEnd m k = batchEnd m (k-1)+m k := by
    have hk1 : k-1+1=k := by omega
    simpa only [hk1] using batchEnd_succ m (k-1)
  apply IsLeast.csInf_eq
  refine ⟨?_,?_⟩
  · change batchEnd m (k-1)+i ≤ batchEnd m k
    omega
  · intro l hl
    change batchEnd m (k-1)+i ≤ batchEnd m l at hl
    by_contra hh
    have hlk : l ≤ k-1 := by omega
    have hm := batchEnd_mono m hlk
    omega

lemma path_measurable {n : ℕ} (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P)
    {Ω Ξ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    (ℱ : Filtration ℕ mΩ) (ξ : ℕ → Ω → Ξ)
    (hadapt : ∀ s,1 ≤ s → Measurable[ℱ s] (ξ s))
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n) :
    ∀ k, Measurable[ℱ (batchEnd m k)] (fun ω => rsagPath G P α β lam m x0 (fun j => ξ j ω) k) := by
  intro k
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hle := ℱ.mono (batchEnd_mono m (show k ≤ k+1 by omega))
    have hp := ih.mono hle le_rfl
    have hmd : Measurable[ℱ (batchEnd m (k+1))] (fun ω =>
        (1-α (k+1)) • (rsagPath G P α β lam m x0 (fun j => ξ j ω) k).2 +
        α (k+1) • (rsagPath G P α β lam m x0 (fun j => ξ j ω) k).1) :=
      (hp.snd.const_smul (1-α (k+1))).add (hp.fst.const_smul (α (k+1)))
    have hg : Measurable[ℱ (batchEnd m (k+1))] (fun ω =>
        sampleAvg G m (k+1)
          ((1-α (k+1)) • (rsagPath G P α β lam m x0 (fun j => ξ j ω) k).2 +
           α (k+1) • (rsagPath G P α β lam m x0 (fun j => ξ j ω) k).1) (fun j => ξ j ω)) := by
      unfold sampleAvg
      simp only [Nat.add_sub_cancel]
      apply Measurable.const_smul (c := ((m (k+1):ℝ)⁻¹))
      apply Finset.measurable_sum
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      have hs : batchEnd m k+i ≤ batchEnd m (k+1) := by rw [batchEnd_succ]; omega
      have hx := (hadapt (batchEnd m k+i) (by omega)).mono (ℱ.mono hs) le_rfl
      exact hG.comp (hmd.prodMk hx)
    exact ((prox_measurable K X hX P hP _ (hstep.2.2.2.1 _ (by omega))).comp (hp.fst.prodMk hg)).prodMk
      ((prox_measurable K X hX P hP _ (hstep.2.2.1 _ (by omega))).comp (hmd.prodMk hg))

#print axioms prox_joint_lipschitz
#print axioms batchOf_index
#print axioms path_measurable
end BatchResearch

namespace MartingaleVariance
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]
omit [CompleteSpace E] in
lemma inner_integrable {μ : Measure Ω} {f g : Ω → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun ω => ⟪f ω,g ω⟫_ℝ) μ := by
  exact (hf.norm.integrable_mul hg.norm).mono' (hf.1.inner hg.1)
    (Filter.Eventually.of_forall fun ω => norm_inner_le_norm (f ω) (g ω))
lemma orthogonal (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (f g : Ω → E) (hf : StronglyMeasurable[m] f) (hf2 : MemLp f 2 μ)
    (hg2 : MemLp g 2 μ) (hg : Integrable g μ)
    (hz : μ[g|m] =ᵐ[μ] fun _ => 0) : (∫ ω, ⟪f ω,g ω⟫_ℝ ∂μ) = 0 := by
  let : MeasurableSpace Ω := mΩ
  have h := condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) hf (inner_integrable hf2 hg2) hg
  change μ[fun ω => ⟪f ω,g ω⟫_ℝ|m] =ᵐ[μ] fun ω => ⟪f ω, μ[g|m] ω⟫_ℝ at h
  have he : μ[fun ω => ⟪f ω,g ω⟫_ℝ|m] =ᵐ[μ] fun _ => (0 : ℝ) := by
    filter_upwards [h,hz] with ω hω hzω
    simpa only [hzω,inner_zero_right] using hω
  rw [← integral_condExp hm, integral_congr_ae he]
  simp
end MartingaleVariance


namespace BatchResearch
lemma batch_moments {n : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (O : ℕ → Ω → E n) (H : Ω → E n) (S N : ℕ) (hN : 1 ≤ N) (σ : ℝ)
    (hH : StronglyMeasurable[ℱ S] H)
    (hO : ∀ i ∈ Finset.Icc 1 N, StronglyMeasurable[ℱ (S+i)] (O i))
    (hiO : ∀ i ∈ Finset.Icc 1 N, Integrable (O i) μ)
    (hu : ∀ i ∈ Finset.Icc 1 N, μ[O i | ℱ (S+i-1)] =ᵐ[μ] H)
    (hiV : ∀ i ∈ Finset.Icc 1 N, Integrable (fun ω => ‖O i ω-H ω‖^2) μ)
    (hV : ∀ i ∈ Finset.Icc 1 N, (∫ ω, ‖O i ω-H ω‖^2 ∂μ) ≤ σ^2) :
    Integrable (fun ω => (N:ℝ)⁻¹ • ∑ i ∈ Finset.Icc 1 N, O i ω) μ ∧
    μ[(fun ω => (N:ℝ)⁻¹ • ∑ i ∈ Finset.Icc 1 N, O i ω) | ℱ S] =ᵐ[μ] H ∧
    Integrable (fun ω => ‖(N:ℝ)⁻¹ • ∑ i ∈ Finset.Icc 1 N, O i ω-H ω‖^2) μ ∧
    (∫ ω, ‖(N:ℝ)⁻¹ • ∑ i ∈ Finset.Icc 1 N, O i ω-H ω‖^2 ∂μ) ≤ σ^2/(N:ℝ) := by
  classical
  let T := Finset.Icc 1 N
  have h1 : 1 ∈ T := by simp [T,hN]
  have hiH : Integrable H μ := integrable_condExp.congr (hu 1 h1)
  let D : ℕ → Ω → E n := fun i ω => O i ω-H ω
  have hD (i) (hi : i ∈ T) : MemLp (D i) 2 μ :=
    (memLp_two_iff_integrable_sq_norm ((hiO i hi).sub hiH).1).2 (hiV i hi)
  have hz (i) (hi : i ∈ T) : μ[D i | ℱ (S+i-1)] =ᵐ[μ] fun _ => 0 := by
    have hii := (Finset.mem_Icc.mp hi).1
    have hHH := hH.mono (ℱ.mono (show S ≤ S+i-1 by omega))
    have h := condExp_sub (hiO i hi) hiH (ℱ (S+i-1))
    rw [condExp_of_stronglyMeasurable (ℱ.le _) hHH hiH] at h
    filter_upwards [h,hu i hi] with ω hω huω
    change μ[D i | ℱ (S+i-1)] ω = 0
    simpa only [Pi.sub_apply,Pi.sub_def,D,huω,sub_self] using hω
  have hort (i) (hi : i ∈ T) (j) (hj : j ∈ T) (hij : i<j) :
      (∫ ω, inner ℝ (D i ω) (D j ω) ∂μ)=0 := by
    have hh : StronglyMeasurable[ℱ (S+j-1)] (D i) :=
      ((hO i hi).mono (ℱ.mono (by omega))).sub (hH.mono (ℱ.mono (by omega)))
    exact MartingaleVariance.orthogonal μ (ℱ.le _) _ _ hh (hD i hi) (hD j hj)
      ((hiO j hj).sub hiH) (hz j hj)
  have hpair (i) (hi : i ∈ T) (j) (hj : j ∈ T) :=
    MartingaleVariance.inner_integrable (hD i hi) (hD j hj)
  have hsum := memLp_finsetSum T (fun i hi => hD i hi)
  have hsumI : Integrable (fun ω => ‖∑ i ∈ T,D i ω‖^2) μ :=
    hsum.integrable_norm_pow (by decide)
  have hexact : (∫ ω, ‖∑ i ∈ T,D i ω‖^2 ∂μ) = ∑ i ∈ T, ∫ ω, ‖D i ω‖^2 ∂μ := by
    simp_rw [← real_inner_self_eq_norm_sq,sum_inner,inner_sum]
    rw [integral_finsetSum T (fun i hi => integrable_finsetSum T (fun j hj => hpair i hi j hj))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum T (fun j hj => hpair i hi j hj),Finset.sum_eq_single i]
    · intro j hj hji
      rcases lt_or_gt_of_ne hji with h|h
      · convert hort j hj i hi h using 1
        simp only [real_inner_comm]
      · exact hort i hi j hj h
    · intro h
      exact (h hi).elim
  have hvsum : (∫ ω, ‖∑ i ∈ T,D i ω‖^2 ∂μ) ≤ (N:ℝ)*σ^2 := by
    rw [hexact]
    have h := Finset.sum_le_sum (fun i hi => hV i hi)
    simpa [T] using h
  have hnR : (N:ℝ) ≠ 0 := by exact_mod_cast (show N≠0 by omega)
  have herr (ω) : (N:ℝ)⁻¹ • ∑ i ∈ T,O i ω-H ω = (N:ℝ)⁻¹ • ∑ i ∈ T,D i ω := by
    simp only [D,Finset.sum_sub_distrib,smul_sub,Finset.sum_const]
    rw [← Nat.cast_smul_eq_nsmul ℝ]
    simp [T,smul_smul,hnR]
  have hnorm (ω) : ‖(N:ℝ)⁻¹ • ∑ i ∈ T,O i ω-H ω‖^2 = (N:ℝ)⁻¹^2*‖∑ i ∈ T,D i ω‖^2 := by
    rw [herr,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  refine ⟨(integrable_finsetSum T (fun i hi => hiO i hi)).smul ((N:ℝ)⁻¹),?_,?_,?_⟩
  · have hmean (i) (hi : i ∈ T) : μ[O i|ℱ S] =ᵐ[μ] H := by
      have hii := (Finset.mem_Icc.mp hi).1
      have ht := (condExp_condExp_of_le (μ := μ) (f := O i)
        (ℱ.mono (show S ≤ S+i-1 by omega)) (ℱ.le (S+i-1))).symm
      exact ht.trans ((condExp_congr_ae (hu i hi)).trans (by rw [condExp_of_stronglyMeasurable (ℱ.le S) hH hiH]))
    have hs := condExp_finsetSum (s := T) (fun i hi => hiO i hi) (ℱ S)
    have hh : μ[(∑ i ∈ T,O i)|ℱ S] =ᵐ[μ] ∑ i ∈ T,H := by
      apply hs.trans
      have hall := (Filter.eventually_all_finset T).mpr hmean
      filter_upwards [hall] with ω hω
      simp only [Finset.sum_apply]
      exact Finset.sum_congr rfl (fun i hi => hω i hi)
    have hc := condExp_smul (μ := μ) ((N:ℝ)⁻¹) (∑ i ∈ T,O i) (ℱ S)
    have h := hc.trans (hh.const_smul _)
    simp only [Finset.sum_const,← Nat.cast_smul_eq_nsmul ℝ,smul_smul] at h
    simpa [T,Finset.sum_fn,Pi.smul_def,hnR] using h
  · change Integrable (fun ω => ‖(N:ℝ)⁻¹ • ∑ i ∈ T,O i ω-H ω‖^2) μ
    simp_rw [hnorm]
    exact hsumI.const_mul ((N:ℝ)⁻¹^2)
  · change (∫ ω, ‖(N:ℝ)⁻¹ • ∑ i ∈ T,O i ω-H ω‖^2 ∂μ) ≤ _
    simp_rw [hnorm]
    rw [integral_const_mul]
    have hh := mul_le_mul_of_nonneg_left hvsum (sq_nonneg (N:ℝ)⁻¹)
    convert hh using 1 <;> try rfl
    field_simp [hnR]
    <;> ring

#print axioms batch_moments
end BatchResearch

open ConvexOptAlg.SmoothGD

theorem prior_batch_moments {n : ℕ} (f h : E n → ℝ) (gf gh : E n → E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (Ψ : E n → ℝ) (gΨ : E n → E n) (LΨ : ℝ) (hΨ : Ψ = fun x => f x + h x)
    (hgΨ : gΨ = fun x => gf x + gh x) (hLΨ : LΨ = Lf + Lh)
    (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n)
    (hA1 : GhadimiLan.RSG.AssumptionA1 μ ℱ gΨ G ξ (querySeq G P α β lam m x0 ξ) σ) :
    let xk : ℕ → Ω → E n := xSeq G P α β lam m x0 ξ
    let xag : ℕ → Ω → E n := xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → E n := xmdSeq G P α β lam m x0 ξ
    let Gb : ℕ → Ω → E n := Gbar G P α β lam m x0 ξ
    let δ : ℕ → Ω → E n := deltaBar G gΨ P α β lam m x0 ξ
    ∀ k, 1 ≤ k →
      Integrable (Gb k) μ ∧
      μ[Gb k | ℱ (batchEnd m (k - 1))] =ᵐ[μ] (fun ω => gΨ (xmd k ω)) ∧
      Integrable (fun ω => ‖δ k ω‖ ^ 2) μ ∧
      ∫ ω, ‖δ k ω‖ ^ 2 ∂μ ≤ σ ^ 2 / (m k : ℝ) := by
  dsimp only
  intro k hk
  let S := batchEnd m (k-1)
  let H : Ω → E n := fun ω => gΨ (xmdSeq G P α β lam m x0 ξ k ω)
  let O : ℕ → Ω → E n := fun i ω => G (xmdSeq G P α β lam m x0 ξ k ω) (ξ (S+i) ω)
  have hm : 1 ≤ m k := hstep.2.2.2.2 k hk
  have hp := BatchResearch.path_measurable K X hX P hP G hG ℱ ξ hA1.adapted α β lam m hstep x0 (k-1)
  have hmd : Measurable[ℱ S] (xmdSeq G P α β lam m x0 ξ k) :=
    (hp.snd.const_smul (1-α k)).add (hp.fst.const_smul (α k))
  have hgf : LipschitzWith ⟨Lf,hf.1⟩ gf := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖gf x-gf y‖ ≤ Lf*‖x-y‖
    exact hf.2.2 x y
  have hgh : LipschitzWith ⟨Lh,hh.1⟩ gh := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖gh x-gh y‖ ≤ Lh*‖x-y‖
    exact hh.2.2 x y
  have hgrad : Measurable gΨ := by
    rw [hgΨ]
    exact hgf.continuous.measurable.add hgh.continuous.measurable
  have hH : StronglyMeasurable[ℱ S] H := (hgrad.comp hmd).stronglyMeasurable
  have hidx (i : ℕ) (hi : i ∈ Finset.Icc 1 (m k)) :
      querySeq G P α β lam m x0 ξ (S+i) = xmdSeq G P α β lam m x0 ξ k := by
    funext ω
    simp only [querySeq,S,BatchResearch.batchOf_index m k i hk hi]
  have hO (i : ℕ) (hi : i ∈ Finset.Icc 1 (m k)) : StronglyMeasurable[ℱ (S+i)] (O i) := by
    have hi0 := (Finset.mem_Icc.mp hi).1
    exact (hG.comp ((hmd.mono (ℱ.mono (Nat.le_add_right S i)) le_rfl).prodMk
      (hA1.adapted (S+i) (by omega)))).stronglyMeasurable
  have hiO (i : ℕ) (hi : i ∈ Finset.Icc 1 (m k)) : Integrable (O i) μ := by
    have hi0 := (Finset.mem_Icc.mp hi).1
    have h := hA1.integrable_oracle (S+i) (by omega)
    simpa only [hidx i hi] using h
  have hu (i : ℕ) (hi : i ∈ Finset.Icc 1 (m k)) : μ[O i | ℱ (S+i-1)] =ᵐ[μ] H := by
    have hi0 := (Finset.mem_Icc.mp hi).1
    have h := hA1.unbiased (S+i) (by omega)
    simpa only [hidx i hi] using h
  have hiV (i : ℕ) (hi : i ∈ Finset.Icc 1 (m k)) : Integrable (fun ω => ‖O i ω-H ω‖^2) μ := by
    have hi0 := (Finset.mem_Icc.mp hi).1
    have h := hA1.integrable_sq_error (S+i) (by omega)
    simpa only [hidx i hi] using h
  have hV (i : ℕ) (hi : i ∈ Finset.Icc 1 (m k)) : (∫ ω, ‖O i ω-H ω‖^2 ∂μ) ≤ σ^2 := by
    have hi0 := (Finset.mem_Icc.mp hi).1
    have h := hA1.variance_bound (S+i) (by omega)
    simpa only [hidx i hi] using h
  have hres := BatchResearch.batch_moments μ ℱ O H S (m k) hm σ hH hO hiO hu hiV hV
  convert hres using 1 <;> rfl

#print axioms prior_batch_moments

set_option autoImplicit false

open GhadimiLan.RSG (E)
open ConvexOptAlg.SmoothGD

/-- (3.29), p. 21, for Algorithm 4: under Assumption 1 (conditional form, along the query points),
for every `k ≥ 1`, `‖𝒢(x^md_k, ∇Ψ(x^md_k), βₖ) − 𝒢(x^md_k, Ḡₖ, βₖ)‖²` is integrable and
`E‖𝒢(x^md_k, ∇Ψ(x^md_k), βₖ) − 𝒢(x^md_k, Ḡₖ, βₖ)‖² ≤ E‖Ḡₖ − ∇Ψ(x^md_k)‖² ≤ σ²/mₖ`. -/
theorem prior_error {n : ℕ} (f h : E n → ℝ) (gf gh : E n → E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (Ψ : E n → ℝ) (gΨ : E n → E n) (LΨ : ℝ) (hΨ : Ψ = fun x => f x + h x)
    (hgΨ : gΨ = fun x => gf x + gh x) (hLΨ : LΨ = Lf + Lh)
    (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n)
    (hA1 : GhadimiLan.RSG.AssumptionA1 μ ℱ gΨ G ξ (querySeq G P α β lam m x0 ξ) σ) :
    let xk : ℕ → Ω → E n := xSeq G P α β lam m x0 ξ
    let xag : ℕ → Ω → E n := xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → E n := xmdSeq G P α β lam m x0 ξ
    let Gb : ℕ → Ω → E n := Gbar G P α β lam m x0 ξ
    let δ : ℕ → Ω → E n := deltaBar G gΨ P α β lam m x0 ξ
    ∀ k, 1 ≤ k →
      Integrable (fun ω => ‖gradMap P (xmd k ω) (gΨ (xmd k ω)) (β k) -
        gradMap P (xmd k ω) (Gb k ω) (β k)‖ ^ 2) μ ∧
      ∫ ω, ‖gradMap P (xmd k ω) (gΨ (xmd k ω)) (β k) -
          gradMap P (xmd k ω) (Gb k ω) (β k)‖ ^ 2 ∂μ ≤ ∫ ω, ‖δ k ω‖ ^ 2 ∂μ ∧
      ∫ ω, ‖δ k ω‖ ^ 2 ∂μ ≤ σ ^ 2 / (m k : ℝ) := by
  dsimp only
  intro k hk
  have hc := hstep.2.2.1 k hk
  have hmom := prior_batch_moments f h gf gh Lf Lh hf hh hhc Ψ gΨ LΨ hΨ hgΨ hLΨ
    K X hX P hP G hG μ ℱ ξ σ α β lam m hstep x0 hA1 k hk
  have hp := BatchResearch.path_measurable K X hX P hP G hG ℱ ξ hA1.adapted α β lam m hstep x0 (k-1)
  have hmdF : Measurable[ℱ (batchEnd m (k-1))] (xmdSeq G P α β lam m x0 ξ k) :=
    (hp.snd.const_smul (1-α k)).add (hp.fst.const_smul (α k))
  have hmd := hmdF.mono (ℱ.le _) le_rfl
  have hgf : LipschitzWith ⟨Lf,hf.1⟩ gf := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖gf x-gf y‖ ≤ Lf*‖x-y‖
    exact hf.2.2 x y
  have hgh : LipschitzWith ⟨Lh,hh.1⟩ gh := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖gh x-gh y‖ ≤ Lh*‖x-y‖
    exact hh.2.2 x y
  have hgrad : Measurable gΨ := by
    rw [hgΨ]
    exact hgf.continuous.measurable.add hgh.continuous.measurable
  have hpg := BatchResearch.prox_measurable K X hX P hP (β k) hc
  have hexa : AEStronglyMeasurable (fun ω =>
      gradMap P (xmdSeq G P α β lam m x0 ξ k ω)
        (gΨ (xmdSeq G P α β lam m x0 ξ k ω)) (β k)) μ := by
    exact (hmd.aestronglyMeasurable.sub
      (hpg.comp (hmd.prodMk (hgrad.comp hmd))).aestronglyMeasurable).const_smul (1/(β k))
  have hstoch : AEStronglyMeasurable (fun ω =>
      gradMap P (xmdSeq G P α β lam m x0 ξ k ω)
        (Gbar G P α β lam m x0 ξ k ω) (β k)) μ := by
    exact (hmd.aestronglyMeasurable.sub
      (hpg.comp_aemeasurable (hmd.aemeasurable.prodMk hmom.1.aemeasurable)).aestronglyMeasurable).const_smul (1/(β k))
  have hb (ω : Ω) :
      ‖gradMap P (xmdSeq G P α β lam m x0 ξ k ω)
          (gΨ (xmdSeq G P α β lam m x0 ξ k ω)) (β k) -
        gradMap P (xmdSeq G P α β lam m x0 ξ k ω)
          (Gbar G P α β lam m x0 ξ k ω) (β k)‖^2 ≤
      ‖deltaBar G gΨ P α β lam m x0 ξ k ω‖^2 := by
    have he := prior_gradient_mapping K X hX P hP
      (xmdSeq G P α β lam m x0 ξ k ω) (gΨ (xmdSeq G P α β lam m x0 ξ k ω))
      (Gbar G P α β lam m x0 ξ k ω) (β k) hc
    rw [norm_sub_rev (gΨ (xmdSeq G P α β lam m x0 ξ k ω)) (Gbar G P α β lam m x0 ξ k ω)] at he
    exact pow_le_pow_left₀ (norm_nonneg _) he 2
  have hi : Integrable (fun ω =>
      ‖gradMap P (xmdSeq G P α β lam m x0 ξ k ω)
          (gΨ (xmdSeq G P α β lam m x0 ξ k ω)) (β k) -
        gradMap P (xmdSeq G P α β lam m x0 ξ k ω)
          (Gbar G P α β lam m x0 ξ k ω) (β k)‖^2) μ := by
    apply hmom.2.2.1.mono' ((hexa.sub hstoch).norm.pow 2)
    filter_upwards [] with ω
    simpa only [Pi.pow_apply,Pi.sub_apply,Real.norm_eq_abs,abs_pow,abs_norm] using hb ω
  exact ⟨hi,integral_mono_ae hi hmom.2.2.1 (Filter.Eventually.of_forall hb),hmom.2.2.2⟩




#print axioms prior_error

namespace ProxValueResearch
open GhadimiLan.RSG (E)
open NonconvexAG.StochComposite
lemma prox_continuous {n : ℕ} (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P) (c : ℝ) (hc : 0 < c) :
    Continuous (fun p : E n × E n => P p.1 p.2 c) := by
  have hl : LipschitzWith ⟨1+c,by positivity⟩ (fun p : E n × E n => P p.1 p.2 c) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [dist_eq_norm]
    have h := BatchResearch.prox_joint_lipschitz K X hX P hP p.1 p.2 q.1 q.2 c hc
    have hx : ‖p.1-q.1‖ ≤ dist p q := le_max_left _ _
    have hy : ‖p.2-q.2‖ ≤ dist p q := le_max_right _ _
    change ‖P p.1 p.2 c-P q.1 q.2 c‖ ≤ (1+c)*dist p q
    nlinarith [mul_le_mul_of_nonneg_left hy hc.le]
  exact hl.continuous
lemma prox_value_continuous {n : ℕ} (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P) (c : ℝ) (hc : 0 < c) :
    Continuous (fun p : E n × E n => X (P p.1 p.2 c)) := by
  have hp := prox_continuous K X hX P hP c hc
  rw [continuous_iff_continuousAt]
  intro a
  let z := P a.1 a.2 c
  let lo := fun p : E n × E n => inner ℝ a.2 z + ‖z-a.1‖^2/(2*c)+X z -
    inner ℝ a.2 (P p.1 p.2 c) - ‖P p.1 p.2 c-a.1‖^2/(2*c)
  let hi := fun p : E n × E n => inner ℝ p.2 z + ‖z-p.1‖^2/(2*c)+X z -
    inner ℝ p.2 (P p.1 p.2 c) - ‖P p.1 p.2 c-p.1‖^2/(2*c)
  have hl : Continuous lo := by dsimp [lo]; fun_prop
  have hu : Continuous hi := by dsimp [hi]; fun_prop
  have hla : lo a = X z := by dsimp [lo,z]; ring
  have hua : hi a = X z := by dsimp [hi,z]; ring
  have hlow (p : E n × E n) : lo p ≤ X (P p.1 p.2 c) := by
    have h := (hP a.1 a.2 c hc).2 (P p.1 p.2 c) (hP p.1 p.2 c hc).1
    dsimp [lo,z]; linarith
  have hupp (p : E n × E n) : X (P p.1 p.2 c) ≤ hi p := by
    have h := (hP p.1 p.2 c hc).2 z (hP a.1 a.2 c hc).1
    dsimp [hi]; linarith
  have hl' := hl.tendsto a
  have hu' := hu.tendsto a
  rw [hla] at hl'
  rw [hua] at hu'
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl' hu' hlow hupp
end ProxValueResearch
#print axioms ProxValueResearch.prox_value_continuous

namespace ProxValueResearch
open GhadimiLan.RSG (E)
open NonconvexAG.StochComposite
lemma prox_value_integrable {n : ℕ} (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P)
    (M c : ℝ) (hA2 : Assumption2 P M) (hc : 0 < c)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x g : Ω → E n) (hx : Measurable x) (hg : Integrable g μ)
    (hxb : ∀ ω, ‖x ω‖ ≤ M) : Integrable (fun ω => X (P (x ω) (g ω) c)) μ := by
  let z := P 0 0 1
  have hz : ‖z‖ ≤ M := hA2 0 0 1 (by norm_num)
  have hM : 0 ≤ M := (norm_nonneg z).trans hz
  have hmeas : AEStronglyMeasurable (fun ω => X (P (x ω) (g ω) c)) μ :=
    ((prox_value_continuous K X hX P hP c hc).measurable.comp_aemeasurable
      (hx.aemeasurable.prodMk hg.aemeasurable)).aestronglyMeasurable
  let B := fun ω => |X z| + M^2/2 + 2*M*‖g ω‖ + 2*M^2/c
  have hB : Integrable B μ := by
    exact ((integrable_const _).add (hg.norm.const_mul (2*M))).add (integrable_const _)
  apply hB.mono' hmeas
  filter_upwards [] with ω
  let u := P (x ω) (g ω) c
  have hu : ‖u‖ ≤ M := hA2 _ _ c hc
  have hu2 : ‖u‖^2 ≤ M^2 := pow_le_pow_left₀ (norm_nonneg u) hu 2
  have hl := (hP 0 0 1 (by norm_num)).2 u (hP (x ω) (g ω) c hc).1
  have hl' : X z - M^2/2 ≤ X u := by
    simp only [inner_zero_left, sub_zero, zero_add, mul_one] at hl
    change ‖z‖^2/2+X z ≤ ‖u‖^2/2+X u at hl
    nlinarith only [hl,hu2,sq_nonneg ‖z‖]
  have hzu : ‖z-u‖ ≤ 2*M := (norm_sub_le z u).trans (by linarith only [hz,hu])
  have hzx : ‖z-x ω‖ ≤ 2*M := (norm_sub_le z (x ω)).trans (by linarith only [hz,hxb ω])
  have hzx2 : ‖z-x ω‖^2 ≤ 4*M^2 := by
    nlinarith only [pow_le_pow_left₀ (norm_nonneg (z-x ω)) hzx 2]
  have hi : inner ℝ (g ω) (z-u) ≤ 2*M*‖g ω‖ := by
    calc
      _ ≤ ‖g ω‖*‖z-u‖ := real_inner_le_norm _ _
      _ ≤ ‖g ω‖*(2*M) := mul_le_mul_of_nonneg_left hzu (norm_nonneg _)
      _ = _ := by ring
  have hr := (hP (x ω) (g ω) c hc).2 z (hP 0 0 1 (by norm_num)).1
  have hnorm : ‖z-x ω‖^2/(2*c) ≤ 2*M^2/c := by
    apply (div_le_iff₀ (by positivity : 0 < 2*c)).2
    field_simp
    nlinarith only [hzx2]
  have hp0 : 0 ≤ ‖u-x ω‖^2/(2*c) := by positivity
  have hu' : X u ≤ X z + 2*M*‖g ω‖ + 2*M^2/c := by
    change inner ℝ (g ω) u + ‖u-x ω‖^2/(2*c)+X u ≤
      inner ℝ (g ω) z + ‖z-x ω‖^2/(2*c)+X z at hr
    rw [inner_sub_right] at hi
    linarith only [hr,hi,hnorm,hp0]
  change |X u| ≤ B ω
  apply abs_le.mpr
  have hp : 0 ≤ 2*M*‖g ω‖ := by positivity
  have hq : 0 ≤ 2*M^2/c := by positivity
  dsimp only [B]
  constructor
  · linarith only [hl',neg_abs_le (X z),sq_nonneg M,hp,hq]
  · linarith only [hu',le_abs_self (X z),sq_nonneg M]
end ProxValueResearch
#print axioms ProxValueResearch.prox_value_integrable

namespace ProxValueResearch
open GhadimiLan.RSG (E)
open NonconvexAG.StochComposite
lemma bounded_continuous_memLp {n : ℕ} {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : Ω → E n) (hx : Measurable x) (M : ℝ) (hb : ∀ ω, ‖x ω‖ ≤ M)
    (f : E n → F) (hf : Continuous f) (p : ENNReal) : MemLp (fun ω => f (x ω)) p μ := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:E n) M).exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound (hf.measurable.comp hx).aestronglyMeasurable C
  filter_upwards [] with ω
  exact hC _ (by simpa only [Metric.mem_closedBall,dist_zero_right] using hb ω)
end ProxValueResearch

open NonconvexAG.StochComposite

open GhadimiLan.RSG (E)
open ConvexOptAlg.SmoothGD

/-- (3.35), p. 23 (outer ends of the chain, with `Φ(x*)` for the printed `Φ(x)` on the left), for
Algorithm 4: under Assumptions 1 (conditional form, along the query points) and 2, `‖x₀‖ ≤ M`,
and (2.9), (2.10) for `k = 1, …, N` (`N ≥ 1`), for every point `x*` of the domain `K` of `𝒳`
the quantities `Φ(x^ag_N) − Φ(x*)` and `‖𝒢(x^md_k, ∇Ψ(x^md_k), βₖ)‖²` (`k = 1, …, N`) are
integrable and
`E[Φ(x^ag_N) − Φ(x*)]/Γ_N + Σ_{k=1}^N (βₖ(1 − L_Ψβₖ)/(8Γₖ)) E‖𝒢(x^md_k, ∇Ψ(x^md_k), βₖ)‖²
  ≤ ‖x₀ − x*‖²/(2λ₁) + (L_f/Γ_N)(‖x*‖² + 2M²) + σ² Σ_{k=1}^N βₖ(4 + (1 − L_Ψβₖ)²)/(4Γₖ(1 − L_Ψβₖ)mₖ)`. -/
theorem solution {n : ℕ} (f h : E n → ℝ) (gf gh : E n → E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (Ψ : E n → ℝ) (gΨ : E n → E n) (LΨ : ℝ) (hΨ : Ψ = fun x => f x + h x)
    (hgΨ : gΨ = fun x => gf x + gh x) (hLΨ : LΨ = Lf + Lh)
    (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n)
    (hA1 : GhadimiLan.RSG.AssumptionA1 μ ℱ gΨ G ξ (querySeq G P α β lam m x0 ξ) σ)
    (M : ℝ) (hA2 : Assumption2 P M) (hx0 : ‖x0‖ ≤ M)
    (N : ℕ) (hN : 1 ≤ N) (h29 : ∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ β k ∧ LΨ * β k < 1)
    (h210 : ∀ k ∈ Finset.Icc 1 N, 2 ≤ k →
      α k / (lam k * NonconvexAG.Smooth.Gamma α k) ≤ α (k - 1) / (lam (k - 1) * NonconvexAG.Smooth.Gamma α (k - 1)))
    (xstar : E n) (hxstar : xstar ∈ K) :
    let Φ : E n → ℝ := fun x => Ψ x + X x
    let xag : ℕ → Ω → E n := xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → E n := xmdSeq G P α β lam m x0 ξ
    Integrable (fun ω => Φ (xag N ω) - Φ xstar) μ ∧
    (∀ k ∈ Finset.Icc 1 N,
      Integrable (fun ω => ‖gradMap P (xmd k ω) (gΨ (xmd k ω)) (β k)‖ ^ 2) μ) ∧
    (∫ ω, (Φ (xag N ω) - Φ xstar) ∂μ) / NonconvexAG.Smooth.Gamma α N +
        ∑ k ∈ Finset.Icc 1 N, β k * (1 - LΨ * β k) / (8 * NonconvexAG.Smooth.Gamma α k) *
          ∫ ω, ‖gradMap P (xmd k ω) (gΨ (xmd k ω)) (β k)‖ ^ 2 ∂μ ≤
      ‖x0 - xstar‖ ^ 2 / (2 * lam 1) + Lf / NonconvexAG.Smooth.Gamma α N * (‖xstar‖ ^ 2 + 2 * M ^ 2) +
        σ ^ 2 * ∑ k ∈ Finset.Icc 1 N,
          β k * (4 + (1 - LΨ * β k) ^ 2) / (4 * NonconvexAG.Smooth.Gamma α k * (1 - LΨ * β k) * (m k : ℝ)) := by
  intro Φ xag xmd
  let xk := xSeq G P α β lam m x0 ξ
  let Gb := Gbar G P α β lam m x0 ξ
  let δ := deltaBar G gΨ P α β lam m x0 ξ
  let γ := NonconvexAG.Smooth.Gamma α
  have hM : 0 ≤ M := (norm_nonneg x0).trans hx0
  have hp := BatchResearch.path_measurable K X hX P hP G hG ℱ ξ hA1.adapted α β lam m hstep x0
  have hb (j : ℕ) (ω : Ω) : ‖xk j ω‖ ≤ M ∧ ‖xag j ω‖ ≤ M := by
    cases j with
    | zero => simpa [xk,xag,xSeq,xagSeq,rsagPath] using And.intro hx0 hx0
    | succ j =>
      change ‖P _ _ (lam (j+1))‖ ≤ M ∧ ‖P _ _ (β (j+1))‖ ≤ M
      exact ⟨hA2 _ _ _ (hstep.2.2.2.1 _ (by omega)),hA2 _ _ _ (hstep.2.2.1 _ (by omega))⟩
  have hmdF (k : ℕ) : Measurable[ℱ (batchEnd m (k-1))] (xmd k) :=
    ((hp (k-1)).snd.const_smul (1-α k)).add ((hp (k-1)).fst.const_smul (α k))
  have hmd (k : ℕ) : Measurable (xmd k) := (hmdF k).mono (ℱ.le _) le_rfl
  have hmdB (k : ℕ) (hk : 1 ≤ k) (ω : Ω) : ‖xmd k ω‖ ≤ M := by
    have ha : 0 ≤ α k ∧ α k ≤ 1 := by
      rcases Nat.eq_or_lt_of_le hk with he | he
      · subst k; rw [hstep.1]; norm_num
      · exact ⟨(hstep.2.1 k (by omega)).1.le,(hstep.2.1 k (by omega)).2.le⟩
    change ‖(1-α k) • xag (k-1) ω + α k • xk (k-1) ω‖ ≤ M
    have hn := norm_add_le ((1-α k) • xag (k-1) ω) (α k • xk (k-1) ω)
    rw [norm_smul,norm_smul,Real.norm_of_nonneg (by linarith : 0 ≤ 1-α k),Real.norm_of_nonneg ha.1] at hn
    nlinarith [mul_le_mul_of_nonneg_left (hb (k-1) ω).2 (by linarith : 0 ≤ 1-α k),
      mul_le_mul_of_nonneg_left (hb (k-1) ω).1 ha.1]
  have hgf : LipschitzWith ⟨Lf,hf.1⟩ gf := by
    apply LipschitzWith.of_dist_le_mul; intro x y; exact hf.2.2 x y
  have hgh : LipschitzWith ⟨Lh,hh.1⟩ gh := by
    apply LipschitzWith.of_dist_le_mul; intro x y; exact hh.2.2 x y
  have hgrad : Continuous gΨ := by rw [hgΨ]; exact hgf.continuous.add hgh.continuous
  have hψ : Continuous Ψ := by
    rw [hΨ]
    exact (continuous_iff_continuousAt.mpr fun x => (hf.2.1 x).continuousAt).add
      (continuous_iff_continuousAt.mpr fun x => (hh.2.1 x).continuousAt)
  have hmom (k : ℕ) (hk : 1 ≤ k) := prior_batch_moments f h gf gh Lf Lh hf hh hhc Ψ gΨ LΨ hΨ hgΨ hLΨ
    K X hX P hP G hG μ ℱ ξ σ α β lam m hstep x0 hA1 k hk
  have hiφ : Integrable (fun ω => Φ (xag N ω)-Φ xstar) μ := by
    have hy : Measurable (xag N) := ((hp N).snd.mono (ℱ.le _) le_rfl)
    have hiψ := (ProxValueResearch.bounded_continuous_memLp μ (xag N) hy M (fun ω => (hb N ω).2) Ψ hψ 1).integrable (by norm_num)
    have hiX := ProxValueResearch.prox_value_integrable K X hX P hP M (β N) hA2 (hstep.2.2.1 N hN)
      μ (xmd N) (Gb N) (hmd N) (hmom N hN).1 (hmdB N hN)
    have hrec (ω : Ω) : xag N ω = P (xmd N ω) (Gb N ω) (β N) := by
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
      rfl
    have hiX' : Integrable (fun ω => X (xag N ω)) μ := by simpa only [hrec] using hiX
    exact (hiψ.add hiX').sub (integrable_const _)
  have himap (k : ℕ) (hk : 1 ≤ k) : Integrable (fun ω => ‖gradMap P (xmd k ω) (gΨ (xmd k ω)) (β k)‖^2) μ := by
    have hpc := ProxValueResearch.prox_continuous K X hX P hP (β k) (hstep.2.2.1 k hk)
    have hc : Continuous (fun z => ‖gradMap P z (gΨ z) (β k)‖^2) := by
      dsimp [gradMap]
      fun_prop
    exact (ProxValueResearch.bounded_continuous_memLp μ (xmd k) (hmd k) M (hmdB k hk) _ hc 1).integrable (by norm_num)
  have hnoise (k : ℕ) (hk : 1 ≤ k) : Integrable (fun ω => inner ℝ (δ k ω) (xstar-xk (k-1) ω)) μ ∧
      (∫ ω, inner ℝ (δ k ω) (xstar-xk (k-1) ω) ∂μ)=0 := by
    have hm := hmom k hk
    have hiH := (ProxValueResearch.bounded_continuous_memLp μ (xmd k) (hmd k) M (hmdB k hk) gΨ hgrad 1).integrable (by norm_num)
    have hid : Integrable (δ k) μ := hm.1.sub hiH
    have hd2 : MemLp (δ k) 2 μ := (memLp_two_iff_integrable_sq_norm hid.1).2 hm.2.2.1
    have hxF : StronglyMeasurable[ℱ (batchEnd m (k-1))] (fun ω => xstar-xk (k-1) ω) :=
      (measurable_const.sub (hp (k-1)).fst).stronglyMeasurable
    have hx2 : MemLp (fun ω => xstar-xk (k-1) ω) 2 μ := by
      apply MemLp.of_bound (hxF.mono (ℱ.le _)).aestronglyMeasurable (‖xstar‖+M)
      filter_upwards [] with ω
      exact (norm_sub_le _ _).trans (by linarith only [(hb (k-1) ω).1])
    have hz : μ[δ k | ℱ (batchEnd m (k-1))] =ᵐ[μ] fun _ => 0 := by
      have he := condExp_sub hm.1 hiH (m := ℱ (batchEnd m (k-1)))
      have hH : StronglyMeasurable[ℱ (batchEnd m (k-1))] (fun ω => gΨ (xmd k ω)) :=
        (hgrad.measurable.comp (hmdF k)).stronglyMeasurable
      rw [condExp_of_stronglyMeasurable (ℱ.le _) hH hiH] at he
      filter_upwards [he,hm.2.1] with ω hω hω'
      change μ[Gb k-(fun ω => gΨ (xmd k ω))|ℱ (batchEnd m (k-1))] ω=0
      simpa only [Pi.sub_apply,hω',xmd,Gb,sub_self] using hω
    have hi := MartingaleVariance.inner_integrable hx2 hd2
    have hz' := MartingaleVariance.orthogonal μ (ℱ.le _) _ _ hxF hx2 hd2 hid hz
    simpa only [real_inner_comm] using And.intro hi hz'
  have hg (k : ℕ) : 0 < γ k := by
    apply Finset.prod_pos
    intro i hi
    have hh := (hstep.2.1 i (Finset.mem_Icc.mp hi).1).2
    linarith
  let Q := fun k ω => ‖gradMap P (xmd k ω) (gΨ (xmd k ω)) (β k)‖^2
  let D := fun k ω => ‖xag k ω-xmd k ω‖^2
  let V := fun k ω => ‖δ k ω‖^2
  let T := fun k => 1-LΨ*β k
  let c := fun k => β k*T k/(8*γ k)
  let d := fun k => T k/(4*β k*γ k)
  let e := fun k => β k*T k/(4*γ k)
  let b := fun k => β k/(γ k*T k)+e k
  let A := fun ω => Φ (xag N ω)-Φ xstar
  let B := ‖x0-xstar‖^2/(2*lam 1)+Lf/γ N*(‖xstar‖^2+2*M^2)
  let Z := fun k ω => α k/γ k*inner ℝ (δ k ω) (xstar-xk (k-1) ω)
  have hZ (k : ℕ) (hk : k ∈ Finset.Icc 1 N) : Integrable (Z k) μ :=
    (hnoise k (Finset.mem_Icc.mp hk).1).1.const_mul _
  have hV (k : ℕ) (hk : k ∈ Finset.Icc 1 N) : Integrable (V k) μ :=
    (hmom k (Finset.mem_Icc.mp hk).1).2.2.1
  have hT (k : ℕ) (hk : k ∈ Finset.Icc 1 N) : 0 < T k := sub_pos.mpr (h29 k hk).2
  have hpos (k : ℕ) (hk : k ∈ Finset.Icc 1 N) : 0 ≤ b k := by
    have hβ := hstep.2.2.1 k (Finset.mem_Icc.mp hk).1
    have ht := hT k hk
    have hγ := hg k
    dsimp [b,e]; positivity
  have hmap (k : ℕ) (hk : k ∈ Finset.Icc 1 N) (ω : Ω) : c k*Q k ω ≤ d k*D k ω+e k*V k ω := by
    have hk1 := (Finset.mem_Icc.mp hk).1
    have hc := hstep.2.2.1 k hk1
    let u := gradMap P (xmd k ω) (gΨ (xmd k ω)) (β k)
    let v := gradMap P (xmd k ω) (Gb k ω) (β k)
    have hr (ω : Ω) : xag k ω=P (xmd k ω) (Gb k ω) (β k) := by
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rfl
    have hv : ‖v‖^2 = (1/β k)^2*D k ω := by
      dsimp [v,gradMap,D]
      rw [← hr, norm_smul,Real.norm_of_nonneg (by positivity),mul_pow,norm_sub_rev]
    have hd : ‖u-v‖^2 ≤ V k ω := by
      have hh := prior_gradient_mapping K X hX P hP (xmd k ω) (gΨ (xmd k ω)) (Gb k ω) (β k) hc
      rw [norm_sub_rev (gΨ (xmd k ω)) (Gb k ω)] at hh
      exact pow_le_pow_left₀ (norm_nonneg _) hh 2
    have hn : ‖u‖ ≤ ‖u-v‖+‖v‖ := by simpa only [sub_add_cancel] using norm_add_le (u-v) v
    have hq : Q k ω ≤ 2*((1/β k)^2*D k ω+V k ω) := by
      have hs := pow_le_pow_left₀ (norm_nonneg u) hn 2
      change ‖u‖^2 ≤ _
      nlinarith only [hs,hd,hv,sq_nonneg (‖u-v‖-‖v‖)]
    have hck : 0 ≤ c k := by dsimp [c]; exact div_nonneg (mul_nonneg hc.le (hT k hk).le) (mul_nonneg (by norm_num) (hg k).le)
    have hm := mul_le_mul_of_nonneg_left hq hck
    have he : c k*(2*((1/β k)^2*D k ω+V k ω)) = d k*D k ω+e k*V k ω := by
      dsimp [c,d,e]
      field_simp
      <;> ring
    exact hm.trans_eq he
  have hpath (ω : Ω) : A ω/γ N + ∑ k ∈ Finset.Icc 1 N,c k*Q k ω ≤
      B+∑ k ∈ Finset.Icc 1 N,Z k ω+∑ k ∈ Finset.Icc 1 N,b k*V k ω := by
    have hs := prior_xstar f h gf gh Lf Lh hf hh hhc Ψ gΨ LΨ hΨ hgΨ hLΨ
      K X hX P hP G α β lam m hstep x0 M hA2 hx0 ξ N hN h29 h210 ω xstar hxstar
    have hm := Finset.sum_le_sum (fun k hk => hmap k hk ω)
    have he : (∑ k ∈ Finset.Icc 1 N,b k*V k ω)=
        (∑ k ∈ Finset.Icc 1 N,β k*V k ω/(γ k*T k))+
        ∑ k ∈ Finset.Icc 1 N,e k*V k ω := by
      rw [← Finset.sum_add_distrib];apply Finset.sum_congr rfl;intro k hk;dsimp [b];ring
    rw [Finset.sum_add_distrib] at hm
    rw [he]
    dsimp only [A,B,Z,Q,D,V,T,c,d,e,xag,xmd,xk,δ,γ] at hs hm ⊢
    linarith only [hs,hm]
  have hleft : Integrable (fun ω => A ω/γ N+∑ k ∈ Finset.Icc 1 N,c k*Q k ω) μ :=
    (hiφ.div_const _).add (integrable_finset_sum _ fun k hk => (himap k (Finset.mem_Icc.mp hk).1).const_mul _)
  have hright : Integrable (fun ω => B+∑ k ∈ Finset.Icc 1 N,Z k ω+∑ k ∈ Finset.Icc 1 N,b k*V k ω) μ :=
    ((integrable_const _).add (integrable_finset_sum _ hZ)).add
      (integrable_finset_sum _ fun k hk => (hV k hk).const_mul _)
  have hexp := integral_mono hleft hright hpath
  have hzsum : (∫ ω,∑ k ∈ Finset.Icc 1 N,Z k ω ∂μ)=0 := by
    rw [integral_finset_sum _ hZ]
    apply Finset.sum_eq_zero
    intro k hk
    change (∫ ω,α k/γ k*inner ℝ (δ k ω) (xstar-xk (k-1) ω) ∂μ)=0
    rw [integral_const_mul,(hnoise k (Finset.mem_Icc.mp hk).1).2,mul_zero]
  have hQi : Integrable (fun ω => ∑ k ∈ Finset.Icc 1 N,c k*Q k ω) μ :=
    integrable_finsetSum _ fun k hk => (himap k (Finset.mem_Icc.mp hk).1).const_mul (c k)
  have hZi : Integrable (fun ω => ∑ k ∈ Finset.Icc 1 N,Z k ω) μ := integrable_finsetSum _ hZ
  have hWi : Integrable (fun ω => ∑ k ∈ Finset.Icc 1 N,b k*V k ω) μ :=
    integrable_finsetSum _ fun k hk => (hV k hk).const_mul (b k)
  have hBZ : Integrable (fun ω => B+(∑ k ∈ Finset.Icc 1 N,Z k ω)) μ := (integrable_const B).add hZi
  rw [integral_add (hiφ.div_const _) hQi, integral_div,
    integral_finsetSum _ (fun k hk => (himap k (Finset.mem_Icc.mp hk).1).const_mul (c k)),
    integral_add hBZ hWi,
    integral_add (integrable_const B) hZi,hzsum,add_zero,integral_const,probReal_univ,one_smul,
    integral_finsetSum _ (fun k hk => (hV k hk).const_mul (b k))] at hexp
  simp only [integral_const_mul] at hexp
  have hvar : (∑ k ∈ Finset.Icc 1 N,b k*∫ ω,V k ω ∂μ) ≤
      σ^2*∑ k ∈ Finset.Icc 1 N,β k*(4+T k^2)/(4*γ k*T k*(m k:ℝ)) := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 N,b k*(σ^2/(m k:ℝ)) :=
        Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hmom k (Finset.mem_Icc.mp hk).1).2.2.2 (hpos k hk)
      _ = _ := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k hk
        have ht := ne_of_gt (hT k hk)
        have hγ := ne_of_gt (hg k)
        dsimp [b,e]
        field_simp
        <;> ring
  refine ⟨hiφ,fun k hk => himap k (Finset.mem_Icc.mp hk).1,?_⟩
  change (∫ ω,A ω ∂μ)/γ N+∑ k ∈ Finset.Icc 1 N,c k*(∫ ω,Q k ω ∂μ) ≤
    B+σ^2*∑ k ∈ Finset.Icc 1 N,β k*(4+T k^2)/(4*γ k*T k*(m k:ℝ))
  linarith only [hexp,hvar]




#print axioms solution
