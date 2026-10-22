-- Prove2me | solution 1 for NonconvexAG.StochComposite.eq_xstar
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T15:28:31.49179+00:00
-- url     : https://prove2.me/submissions/8cd2348d-d799-47cc-bd31-4656e2ded5dc

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
theorem solution {n : ℕ} (f h : E n → ℝ) (gf gh : E n → E n) (Lf Lh : ℝ)
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




#print axioms solution
