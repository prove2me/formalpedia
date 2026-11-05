-- Prove2me | solution 1 for NemirovskiProx.proposition_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T17:23:36.614609+00:00
-- url     : https://prove2.me/submissions/202dfcb9-f1f5-4bfe-ba72-fa13bacead1b

import Mathlib
import Definitions.Def_NemirovskiProx_dualNorm
import Definitions.Def_NemirovskiProx_IsLipMonotoneOn
import Definitions.Def_NemirovskiProx_IsDistGen
import Definitions.Def_NemirovskiProx_IsProxPointOn
import Definitions.Def_NemirovskiProx_stepGap
import Definitions.Def_NemirovskiProx_IsRelaxedCPMRun
import Definitions.Def_NemirovskiProx_Theta
import Definitions.Def_NemirovskiProx_viError
import Definitions.Def_NemirovskiProx_ergodicAvg
import Definitions.Def_NemirovskiProx_prodSet
import Definitions.Def_NemirovskiProx_saddleOp
import Definitions.Def_NemirovskiProx_IsSmoothConvexConcave
import Definitions.Def_NemirovskiProx_saddleGap
import Definitions.Def_NemirovskiProx_legendre
import Definitions.Def_NemirovskiProx_Hfun

open scoped InnerProductSpace

set_option autoImplicit false

namespace NemirovskiProx

/-- A definite seminorm on a finite-dimensional inner product space dominates a multiple of the norm. -/
lemma np_N_lower {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {N : Seminorm ℝ E} (hN : ∀ x, N x = 0 → x = 0) : ∃ m : ℝ, 0 < m ∧ ∀ x, m * ‖x‖ ≤ N x := by
  classical
  let b := stdOrthonormalBasis ℝ E
  set C : ℝ := ∑ i, N (b i) with hC
  have hup : ∀ x, N x ≤ C * ‖x‖ := by
    intro x
    have hx : x = ∑ i, ⟪b i, x⟫_ℝ • b i := (b.sum_repr' x).symm
    calc N x = N (∑ i, ⟪b i, x⟫_ℝ • b i) := by rw [← hx]
      _ ≤ ∑ i, N (⟪b i, x⟫_ℝ • b i) :=
          Finset.le_sum_of_subadditive (fun y => N y) (map_zero N).le (fun y y' => map_add_le_add N y y') _ _
      _ = ∑ i, |⟪b i, x⟫_ℝ| * N (b i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul_eq_mul, Real.norm_eq_abs]
      _ ≤ ∑ i, ‖x‖ * N (b i) := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine mul_le_mul_of_nonneg_right ?_ (apply_nonneg N _)
          calc |⟪b i, x⟫_ℝ| ≤ ‖b i‖ * ‖x‖ := abs_real_inner_le_norm _ _
            _ = ‖x‖ := by rw [b.orthonormal.1 i, one_mul]
      _ = C * ‖x‖ := by rw [hC, Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
  have hcont : Continuous fun x => N x := by
    have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => apply_nonneg N _
    refine (LipschitzWith.of_dist_le_mul (K := ⟨C, hC0⟩) fun x y => ?_).continuous
    rw [Real.dist_eq, dist_eq_norm]
    calc |N x - N y| ≤ N (x - y) := abs_sub_map_le_sub N x y
      _ ≤ C * ‖x - y‖ := hup _
  by_cases hS : (Metric.sphere (0 : E) 1).Nonempty
  · obtain ⟨x0, hx0, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hS hcont.continuousOn
    have hx0n : x0 ≠ 0 := by
      intro h; rw [h] at hx0; simp at hx0
    have hm : 0 < N x0 := lt_of_le_of_ne (apply_nonneg N _) (fun h => hx0n (hN _ h.symm))
    refine ⟨N x0, hm, fun x => ?_⟩
    by_cases hx : x = 0
    · simp [hx]
    · have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnx.ne']
      have h1 := hmin hy
      simp only [Set.mem_setOf_eq, map_smul_eq_mul, norm_inv, norm_norm] at h1
      calc N x0 * ‖x‖ ≤ ‖x‖⁻¹ * N x * ‖x‖ := mul_le_mul_of_nonneg_right h1 hnx.le
        _ = N x := by field_simp
  · refine ⟨1, one_pos, fun x => ?_⟩
    by_cases hx : x = 0
    · simp [hx]
    · exfalso; apply hS
      refine ⟨‖x‖⁻¹ • x, ?_⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_pos_iff.mpr hx).ne']

lemma np_dual_bdd {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {N : Seminorm ℝ E} (hN : ∀ x, N x = 0 → x = 0) (ξ : E) :
    BddAbove ((fun z => ⟪ξ, z⟫_ℝ) '' {z | N z ≤ 1}) := by
  obtain ⟨m, hm, hmN⟩ := np_N_lower hN
  refine ⟨‖ξ‖ * m⁻¹, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hz' : ‖z‖ ≤ m⁻¹ := by
    have hz1 : N z ≤ 1 := hz
    have h1 : m * ‖z‖ ≤ 1 := le_trans (hmN z) hz1
    have := (le_inv_mul_iff₀ hm).mpr (by simpa using h1 : m * ‖z‖ ≤ 1)
    simpa using this
  calc ⟪ξ, z⟫_ℝ ≤ ‖ξ‖ * ‖z‖ := real_inner_le_norm _ _
    _ ≤ ‖ξ‖ * m⁻¹ := mul_le_mul_of_nonneg_left hz' (norm_nonneg _)

lemma np_dual_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {N : Seminorm ℝ E} (hN : ∀ x, N x = 0 → x = 0) (ξ : E) : 0 ≤ dualNorm N ξ := by
  unfold dualNorm
  refine le_csSup_of_le (np_dual_bdd hN ξ) ⟨0, by simp, rfl⟩ ?_
  simp

lemma np_inner_le_dual {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {N : Seminorm ℝ E} (hN : ∀ x, N x = 0 → x = 0) (ξ x : E) : ⟪ξ, x⟫_ℝ ≤ dualNorm N ξ * N x := by
  by_cases hx : N x = 0
  · rw [hN x hx]; simp
  · have hpos : 0 < N x := lt_of_le_of_ne (apply_nonneg N _) (Ne.symm hx)
    have hmem : (N x)⁻¹ • x ∈ {z | N z ≤ 1} := by
      simp only [Set.mem_setOf_eq, map_smul_eq_mul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos]
      rw [inv_mul_cancel₀ hpos.ne']
    have h1 : ⟪ξ, (N x)⁻¹ • x⟫_ℝ ≤ dualNorm N ξ := le_csSup (np_dual_bdd hN ξ) ⟨_, hmem, rfl⟩
    rw [real_inner_smul_right] at h1
    have h2 := mul_le_mul_of_nonneg_right h1 hpos.le
    rw [inv_mul_eq_div, div_mul_cancel₀ _ hpos.ne'] at h2
    exact h2

lemma np_hasFDeriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Z : Set E} {N : Seminorm ℝ E} {α : ℝ} {ω : E → ℝ} {ω' : E → E} (hω : IsDistGen Z N α ω ω')
    {z : E} (hz : z ∈ Z) :
    HasFDerivWithinAt ω (InnerProductSpace.toDual ℝ E (ω' z) : E →L[ℝ] ℝ) Z z :=
  hω.2.1 z hz

lemma np_omega_cont {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Z : Set E} {N : Seminorm ℝ E} {α : ℝ} {ω : E → ℝ} {ω' : E → E} (hω : IsDistGen Z N α ω ω') :
    ContinuousOn ω Z := fun z hz => (np_hasFDeriv hω hz).continuousWithinAt

/-- Strong convexity: lower bound of the Bregman distance. -/
lemma np_bregman_lb {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Z : Set E} (hZc : Convex ℝ Z) {N : Seminorm ℝ E} {α : ℝ} {ω : E → ℝ} {ω' : E → E}
    (hω : IsDistGen Z N α ω ω') {x y : E} (hx : x ∈ Z) (hy : y ∈ Z) :
    α / 2 * N (y - x) ^ 2 ≤ ω y - ω x - ⟪ω' x, y - x⟫_ℝ := by
  set d := y - x with hd
  let p : ℝ → E := fun s => x + s • d
  have hmaps : Set.MapsTo p (Set.Icc 0 1) Z := fun s hs => hZc.add_smul_sub_mem hx hy hs
  let g : ℝ → ℝ := fun s => ω (p s) - ω x - s * ⟪ω' x, d⟫_ℝ - α / 2 * s ^ 2 * N d ^ 2
  have hderiv : ∀ s ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt g
      (⟪ω' (p s), d⟫_ℝ - ⟪ω' x, d⟫_ℝ - α * s * N d ^ 2) (Set.Icc 0 1) s := by
    intro s hs
    have hp : HasDerivWithinAt p d (Set.Icc 0 1) s := by
      have := ((hasDerivAt_id s).smul_const d).const_add x
      simpa [p] using this.hasDerivWithinAt
    have h1 : HasDerivWithinAt (ω ∘ p) ⟪ω' (p s), d⟫_ℝ (Set.Icc 0 1) s := by
      have := (np_hasFDeriv hω (hmaps hs)).comp_hasDerivWithinAt s hp hmaps
      simpa [InnerProductSpace.toDual_apply_apply] using this
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪ω' x, d⟫_ℝ) ⟪ω' x, d⟫_ℝ s := by
      simpa using (hasDerivAt_id s).mul_const ⟪ω' x, d⟫_ℝ
    have h3 : HasDerivAt (fun s : ℝ => α / 2 * s ^ 2 * N d ^ 2) (α * s * N d ^ 2) s := by
      have := ((hasDerivAt_pow 2 s).const_mul (α / 2)).mul_const (N d ^ 2)
      convert this using 1 <;> first | rfl | (push_cast; ring)
    exact ((h1.sub_const (ω x)).sub h2.hasDerivWithinAt).sub h3.hasDerivWithinAt
  have hmono : MonotoneOn g (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
    · intro s hs; exact (hderiv s hs).continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs ⊢
      exact (hderiv s (Set.Ioo_subset_Icc_self hs)).mono Set.Ioo_subset_Icc_self
    · intro s hs
      rw [interior_Icc] at hs
      have hps : p s ∈ Z := hmaps (Set.Ioo_subset_Icc_self hs)
      have key := hω.2.2.2 (p s) hps x hx
      have hsub : p s - x = s • d := by simp [p]
      rw [hsub, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hs.1, real_inner_smul_right,
        inner_sub_left] at key
      have hsp : 0 < s := hs.1
      have : α * s * N d ^ 2 ≤ ⟪ω' (p s), d⟫_ℝ - ⟪ω' x, d⟫_ℝ := by
        have h' : s * (α * s * N d ^ 2) ≤ s * (⟪ω' (p s), d⟫_ℝ - ⟪ω' x, d⟫_ℝ) := by nlinarith
        exact le_of_mul_le_mul_left h' hsp
      linarith
  have h01 := hmono (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_le_one
  simp only [g, p] at h01
  simp at h01
  have hxd : x + d = y := by rw [hd]; abel
  rw [hxd] at h01
  linarith

/-- First-order optimality for a prox point over `U ⊆ Z`. -/
lemma np_prox_foc {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Z : Set E} {N : Seminorm ℝ E} {α : ℝ} {ω : E → ℝ} {ω' : E → E}
    (hω : IsDistGen Z N α ω ω') {U : Set E} (hUc : Convex ℝ U) (hUZ : U ⊆ Z) {z ξ p : E}
    (hp : IsProxPointOn U ω ω' z ξ p) {v : E} (hv : v ∈ U) :
    0 ≤ ⟪ω' p + (ξ - ω' z), v - p⟫_ℝ := by
  let ℓ : E →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E (ξ - ω' z)
  have hf : HasFDerivWithinAt (fun y => ω y + ℓ y)
      ((InnerProductSpace.toDual ℝ E (ω' p) : E →L[ℝ] ℝ) + ℓ) U p :=
    ((np_hasFDeriv hω (hUZ hp.1)).mono hUZ).add ℓ.hasFDerivWithinAt
  have hmin : IsLocalMinOn (fun y => ω y + ℓ y) U p := by
    refine IsMinOn.localize (fun y hy => ?_)
    show ω p + ℓ p ≤ ω y + ℓ y
    have := hp.2 y hy
    rw [real_inner_comm (ξ - ω' z) p, real_inner_comm (ξ - ω' z) y] at this
    simpa only [ℓ, InnerProductSpace.toDual_apply_apply] using this
  have := hmin.hasFDerivWithinAt_nonneg hf
    (sub_mem_posTangentConeAt_of_segment_subset (hUc.segment_subset hp.1 hv))
  have e : ((InnerProductSpace.toDual ℝ E (ω' p) : E →L[ℝ] ℝ) + ℓ) (v - p) =
      ⟪ω' p + (ξ - ω' z), v - p⟫_ℝ := by
    simp only [ContinuousLinearMap.add_apply, ℓ, InnerProductSpace.toDual_apply_apply,
      inner_add_left]
  rw [← e]; exact this

lemma np_legendre_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Z : Set E} (hZc : Convex ℝ Z) {N : Seminorm ℝ E} {α : ℝ} {ω : E → ℝ} {ω' : E → E}
    (hω : IsDistGen Z N α ω ω') {y : E} (hy : y ∈ Z) :
    legendre Z ω (ω' y) = ⟪ω' y, y⟫_ℝ - ω y := by
  unfold legendre
  refine IsGreatest.csSup_eq ⟨⟨y, hy, rfl⟩, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  have h := np_bregman_lb hZc hω hy hv
  have hα : 0 ≤ α / 2 * N (v - y) ^ 2 := mul_nonneg (by linarith [hω.1]) (sq_nonneg _)
  rw [inner_sub_right] at h
  simp only
  linarith

lemma np_Hfun_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Z : Set E} (hZc : Convex ℝ Z) {N : Seminorm ℝ E} {α : ℝ} {ω : E → ℝ} {ω' : E → E}
    (hω : IsDistGen Z N α ω ω') (u : E) {y : E} (hy : y ∈ Z) :
    Hfun Z ω ω' u y = ⟪ω' y, y - u⟫_ℝ - ω y := by
  unfold Hfun
  rw [np_legendre_eq hZc hω hy, inner_sub_right]
  ring

lemma np_run_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Z : Set E} {F : E → E} {ω : E → ℝ} {ω' : E → E} {γs εs : ℕ → ℝ} {z w : ℕ → E} {n : ℕ}
    (hrun : IsRelaxedCPMRun Z F ω ω' γs εs z w n) : ∀ t ≤ n, z t ∈ Z := by
  intro t ht
  cases t with
  | zero => exact hrun.1
  | succ k => exact (hrun.2 k (by omega)).2.2.2.1.1

lemma np_one_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Z : Set E} (hZc : Convex ℝ Z) {N : Seminorm ℝ E} {α : ℝ} {ω : E → ℝ} {ω' : E → E}
    (hω : IsDistGen Z N α ω ω') {F : E → E} {γs εs : ℕ → ℝ} {z w : ℕ → E} {n : ℕ}
    (hrun : IsRelaxedCPMRun Z F ω ω' γs εs z w n) {t : ℕ} (ht : t < n) {u : E} (hu : u ∈ Z) :
    γs (t + 1) * ⟪F (w (t + 1)), w (t + 1) - u⟫_ℝ ≤
      Hfun Z ω ω' u (z t) - Hfun Z ω ω' u (z (t + 1)) + εs (t + 1) := by
  obtain ⟨_, _, _, hprox, hgap⟩ := hrun.2 t ht
  have hzt : z t ∈ Z := np_run_mem hrun t ht.le
  have hB := np_prox_foc hω hZc subset_rfl hprox hu
  rw [np_Hfun_eq hZc hω u hzt, np_Hfun_eq hZc hω u hprox.1]
  unfold stepGap at hgap
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left, inner_sub_right] at hB hgap ⊢
  linarith

lemma np_summed {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Z : Set E} (hZc : Convex ℝ Z) {N : Seminorm ℝ E} {α : ℝ} {ω : E → ℝ} {ω' : E → E}
    (hω : IsDistGen Z N α ω ω') {F : E → E} {γs εs : ℕ → ℝ} {z w : ℕ → E} {n : ℕ}
    (hrun : IsRelaxedCPMRun Z F ω ω' γs εs z w n) {u : E} (hu : u ∈ Z) :
    ∀ m ≤ n, ∑ t ∈ Finset.Icc 1 m, γs t * ⟪F (w t), w t - u⟫_ℝ ≤
      Hfun Z ω ω' u (z 0) - Hfun Z ω ω' u (z m) + ∑ t ∈ Finset.Icc 1 m, εs t := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := np_one_step hZc hω hrun (t := k) (by omega) hu
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    linarith

lemma np_theta_ge {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Z : Set E} (hZk : IsCompact Z) {N : Seminorm ℝ E} {α : ℝ} {ω : E → ℝ} {ω' : E → E}
    (hω : IsDistGen Z N α ω ω') (z0 : E) {u : E} (hu : u ∈ Z) :
    ω u - ⟪ω' z0, u - z0⟫_ℝ - ω z0 ≤ Theta Z ω ω' z0 := by
  unfold Theta
  have hc : ContinuousOn (fun v => ω v - ω z0 - ⟪ω' z0, v - z0⟫_ℝ) Z :=
    ((np_omega_cont hω).sub continuousOn_const).sub
      (continuous_const.inner (continuous_id.sub continuous_const)).continuousOn
  have := le_csSup (hZk.bddAbove_image hc) ⟨u, hu, rfl⟩
  simp only at this
  linarith

/-- (2.16), end to end: `Σ γ_t ⟨F(w_t), w_t − u⟩ ≤ Θ(z₀) + Σ ε_t`. -/
lemma np_sum_le_theta {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Z : Set E} (hZc : Convex ℝ Z) (hZk : IsCompact Z) {N : Seminorm ℝ E} {α : ℝ} {ω : E → ℝ}
    {ω' : E → E} (hω : IsDistGen Z N α ω ω') {F : E → E} {γs εs : ℕ → ℝ} {z w : ℕ → E} {n : ℕ}
    (hrun : IsRelaxedCPMRun Z F ω ω' γs εs z w n) {u : E} (hu : u ∈ Z) :
    ∑ t ∈ Finset.Icc 1 n, γs t * ⟪F (w t), w t - u⟫_ℝ ≤
      Theta Z ω ω' (z 0) + ∑ t ∈ Finset.Icc 1 n, εs t := by
  have h1 := np_summed hZc hω hrun hu n le_rfl
  have hz0 : z 0 ∈ Z := hrun.1
  have hzn : z n ∈ Z := np_run_mem hrun n le_rfl
  have h3 := np_bregman_lb hZc hω hzn hu
  have hα : 0 ≤ α / 2 * N (u - z n) ^ 2 := mul_nonneg (by linarith [hω.1]) (sq_nonneg _)
  have h5 := np_theta_ge hZk hω (z 0) hu
  rw [np_Hfun_eq hZc hω u hz0, np_Hfun_eq hZc hω u hzn] at h1
  set A := ∑ t ∈ Finset.Icc 1 n, γs t * ⟪F (w t), w t - u⟫_ℝ with hA
  simp only [inner_sub_right] at h1 h3 h5
  linarith

/-- The relaxed-CPM sum with `F u` in place of `F w_t` (monotonicity of `F`). -/
lemma np_sum_Fu_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Z : Set E} (hZc : Convex ℝ Z) (hZk : IsCompact Z) {N : Seminorm ℝ E} {α : ℝ} {ω : E → ℝ}
    {ω' : E → E} (hω : IsDistGen Z N α ω ω') {L : ℝ} {F : E → E} (hF : IsLipMonotoneOn Z N L F)
    {γs εs : ℕ → ℝ} {z w : ℕ → E} {n : ℕ}
    (hrun : IsRelaxedCPMRun Z F ω ω' γs εs z w n) {u : E} (hu : u ∈ Z) :
    ∑ t ∈ Finset.Icc 1 n, γs t * ⟪F u, w t - u⟫_ℝ ≤
      Theta Z ω ω' (z 0) + ∑ t ∈ Finset.Icc 1 n, εs t := by
  refine le_trans (Finset.sum_le_sum fun t ht => ?_) (np_sum_le_theta hZc hZk hω hrun hu)
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ht
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  obtain ⟨_, hγ, hwZ, _, _⟩ := hrun.2 k (by omega)
  have hm := hF.2 (w (k + 1)) hwZ u hu
  rw [inner_sub_left] at hm
  exact mul_le_mul_of_nonneg_left (by linarith) hγ.le

lemma np_gamma_sum_pos {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Z : Set E} {F : E → E} {ω : E → ℝ} {ω' : E → E} {γs εs : ℕ → ℝ} {z w : ℕ → E} {n : ℕ}
    (hn : 1 ≤ n) (hrun : IsRelaxedCPMRun Z F ω ω' γs εs z w n) :
    0 < ∑ t ∈ Finset.Icc 1 n, γs t := by
  refine Finset.sum_pos (fun t ht => ?_) ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hn⟩⟩
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ht
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  exact (hrun.2 k (by omega)).2.1

/-- Proposition 2.2 (ii), (2.13). -/
lemma np_vi_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Z : Set E} (hZc : Convex ℝ Z) (hZk : IsCompact Z) {N : Seminorm ℝ E} {α : ℝ} {ω : E → ℝ}
    {ω' : E → E} (hω : IsDistGen Z N α ω ω') {L : ℝ} {F : E → E} (hF : IsLipMonotoneOn Z N L F)
    {γs εs : ℕ → ℝ} {z w : ℕ → E} {n : ℕ} (hn : 1 ≤ n)
    (hrun : IsRelaxedCPMRun Z F ω ω' γs εs z w n) :
    viError Z F (ergodicAvg γs w n) ≤
      (Theta Z ω ω' (z 0) + ∑ t ∈ Finset.Icc 1 n, εs t) / ∑ t ∈ Finset.Icc 1 n, γs t := by
  have hS := np_gamma_sum_pos hn hrun
  unfold viError ergodicAvg
  refine csSup_le ⟨_, z 0, hrun.1, rfl⟩ ?_
  rintro _ ⟨u, hu, rfl⟩
  have key := np_sum_Fu_le hZc hZk hω hF hrun hu
  set S := ∑ t ∈ Finset.Icc 1 n, γs t with hSdef
  have h1 : ⟪F u, ∑ t ∈ Finset.Icc 1 n, γs t • w t⟫_ℝ =
      ∑ t ∈ Finset.Icc 1 n, γs t * ⟪F u, w t⟫_ℝ := by
    rw [inner_sum]; simp only [real_inner_smul_right]
  have h2 : ∑ t ∈ Finset.Icc 1 n, γs t * ⟪F u, w t - u⟫_ℝ =
      ∑ t ∈ Finset.Icc 1 n, γs t * ⟪F u, w t⟫_ℝ - S * ⟪F u, u⟫_ℝ := by
    simp only [inner_sub_right, mul_sub, Finset.sum_sub_distrib, hSdef, Finset.sum_mul]
  simp only
  rw [inner_sub_right, real_inner_smul_right, h1, le_div_iff₀ hS]
  have h3 : (S⁻¹ * ∑ t ∈ Finset.Icc 1 n, γs t * ⟪F u, w t⟫_ℝ - ⟪F u, u⟫_ℝ) * S =
      ∑ t ∈ Finset.Icc 1 n, γs t * ⟪F u, w t⟫_ℝ - S * ⟪F u, u⟫_ℝ := by
    field_simp
  rw [h3]
  linarith
/-- Gradient inequality for a convex function with a gradient within its convex domain. -/
lemma np_grad_convex {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    {X : Set G} {g : G → ℝ} (hg : ConvexOn ℝ X g) {a b g' : G} (ha : a ∈ X) (hb : b ∈ X)
    (hd : HasGradientWithinAt g g' X a) : g a + ⟪g', b - a⟫_ℝ ≤ g b := by
  let ℓ : ℝ →ᵃ[ℝ] G := AffineMap.lineMap a b
  have hℓ : ∀ s : ℝ, ℓ s = s • (b - a) + a := fun s => AffineMap.lineMap_apply_module' a b s
  have hc : ConvexOn ℝ (ℓ ⁻¹' X) (g ∘ ℓ) := hg.comp_affineMap ℓ
  have h0 : (0:ℝ) ∈ ℓ ⁻¹' X := by
    simp only [Set.mem_preimage, hℓ, zero_smul, zero_add]; exact ha
  have h1 : (1:ℝ) ∈ ℓ ⁻¹' X := by
    simp only [Set.mem_preimage, hℓ, one_smul, sub_add_cancel]; exact hb
  have hp : HasDerivWithinAt (⇑ℓ) (b - a) (ℓ ⁻¹' X) 0 := by
    have : HasDerivAt (fun s : ℝ => s • (b - a) + a) (b - a) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const (b - a)).add_const a
    have e : (⇑ℓ) = fun s : ℝ => s • (b - a) + a := funext hℓ
    rw [e]; exact this.hasDerivWithinAt
  have hd' : HasFDerivWithinAt g (InnerProductSpace.toDual ℝ G g' : G →L[ℝ] ℝ) X (ℓ 0) := by
    rw [hℓ, zero_smul, zero_add]; exact hd
  have hcomp := hd'.comp_hasDerivWithinAt (0:ℝ) hp (Set.mapsTo_preimage ℓ X)
  rw [InnerProductSpace.toDual_apply_apply] at hcomp
  have hs := hc.le_slope_of_hasDerivWithinAt h0 h1 zero_lt_one hcomp
  rw [slope_def_field] at hs
  simp only [Function.comp_apply, hℓ, zero_smul, zero_add, one_smul, sub_add_cancel, sub_zero,
    div_one] at hs
  linarith

lemma np_grad_concave {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    {X : Set G} {g : G → ℝ} (hg : ConcaveOn ℝ X g) {a b g' : G} (ha : a ∈ X) (hb : b ∈ X)
    (hd : HasGradientWithinAt g g' X a) : g b ≤ g a + ⟪g', b - a⟫_ℝ := by
  have hd' : HasGradientWithinAt (-g) (-g') X a := by
    have h := HasFDerivWithinAt.neg (hd : HasFDerivWithinAt g (InnerProductSpace.toDual ℝ G g' : G →L[ℝ] ℝ) X a)
    rw [← map_neg] at h
    exact h
  have := np_grad_convex hg.neg ha hb hd'
  simp only [Pi.neg_apply, inner_neg_left] at this
  linarith

lemma np_prodSet_convex {Ex Ey : Type*} [NormedAddCommGroup Ex] [InnerProductSpace ℝ Ex]
    [NormedAddCommGroup Ey] [InnerProductSpace ℝ Ey] {X : Set Ex} {Y : Set Ey}
    (hX : Convex ℝ X) (hY : Convex ℝ Y) : Convex ℝ (prodSet X Y) := by
  intro p hp q hq a b ha hb hab
  obtain ⟨hp1, hp2⟩ : (WithLp.ofLp p).1 ∈ X ∧ (WithLp.ofLp p).2 ∈ Y := hp
  obtain ⟨hq1, hq2⟩ : (WithLp.ofLp q).1 ∈ X ∧ (WithLp.ofLp q).2 ∈ Y := hq
  show (WithLp.ofLp (a • p + b • q)).1 ∈ X ∧ (WithLp.ofLp (a • p + b • q)).2 ∈ Y
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd]
  exact ⟨hX hp1 hq1 ha hb hab, hY hp2 hq2 ha hb hab⟩

lemma np_prodSet_compact {Ex Ey : Type*} [NormedAddCommGroup Ex] [InnerProductSpace ℝ Ex]
    [NormedAddCommGroup Ey] [InnerProductSpace ℝ Ey] {X : Set Ex} {Y : Set Ey}
    (hX : IsCompact X) (hY : IsCompact Y) : IsCompact (prodSet X Y) := by
  have e : prodSet X Y = WithLp.toLp 2 '' (X ×ˢ Y) := by
    ext r; constructor
    · intro hp; exact ⟨WithLp.ofLp r, hp, rfl⟩
    · rintro ⟨q, hq, rfl⟩; exact hq
  rw [e]; exact (hX.prod hY).image (WithLp.prod_continuous_toLp 2 Ex Ey)

/-- The key estimate behind (2.14): `f(x^N, y) − f(x, y^N) ≤ (Θ(z₀) + Σ ε_t)/(Σ γ_t)`. -/
lemma np_saddle_key {Ex Ey : Type*} [NormedAddCommGroup Ex] [InnerProductSpace ℝ Ex]
    [FiniteDimensional ℝ Ex] [NormedAddCommGroup Ey] [InnerProductSpace ℝ Ey]
    [FiniteDimensional ℝ Ey] {X : Set Ex} {Y : Set Ey} {f : Ex × Ey → ℝ} {fx : Ex × Ey → Ex}
    {fy : Ex × Ey → Ey} {N : Seminorm ℝ (WithLp 2 (Ex × Ey))} {α : ℝ}
    {ω : WithLp 2 (Ex × Ey) → ℝ} {ω' : WithLp 2 (Ex × Ey) → WithLp 2 (Ex × Ey)}
    (hXc : Convex ℝ X) (hXk : IsCompact X) (hYc : Convex ℝ Y) (hYk : IsCompact Y)
    (hf : IsSmoothConvexConcave X Y f fx fy) (hω : IsDistGen (prodSet X Y) N α ω ω')
    {γs εs : ℕ → ℝ} {z w : ℕ → WithLp 2 (Ex × Ey)} {n : ℕ} (hn : 1 ≤ n)
    (hrun : IsRelaxedCPMRun (prodSet X Y) (saddleOp fx fy) ω ω' γs εs z w n)
    {x : Ex} {y : Ey} (hx : x ∈ X) (hy : y ∈ Y) :
    f ((WithLp.ofLp (ergodicAvg γs w n)).1, y) - f (x, (WithLp.ofLp (ergodicAvg γs w n)).2) ≤
      (Theta (prodSet X Y) ω ω' (z 0) + ∑ t ∈ Finset.Icc 1 n, εs t) /
        ∑ t ∈ Finset.Icc 1 n, γs t := by
  have hSpos := np_gamma_sum_pos hn hrun
  set S := ∑ t ∈ Finset.Icc 1 n, γs t with hS
  have hγ : ∀ t ∈ Finset.Icc 1 n, 0 < γs t := by
    intro t ht
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ht
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
    exact (hrun.2 k (by omega)).2.1
  have hwZ : ∀ t ∈ Finset.Icc 1 n, (WithLp.ofLp (w t)).1 ∈ X ∧ (WithLp.ofLp (w t)).2 ∈ Y := by
    intro t ht
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ht
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
    exact (hrun.2 k (by omega)).2.2.1
  have hl0 : ∀ t ∈ Finset.Icc 1 n, 0 ≤ S⁻¹ * γs t := fun t ht =>
    mul_nonneg (inv_nonneg.mpr hSpos.le) (hγ t ht).le
  have hl1 : ∑ t ∈ Finset.Icc 1 n, S⁻¹ * γs t = 1 := by
    rw [← Finset.mul_sum]; exact inv_mul_cancel₀ hSpos.ne'
  have hxbar : (WithLp.ofLp (ergodicAvg γs w n)).1 =
      ∑ t ∈ Finset.Icc 1 n, (S⁻¹ * γs t) • (WithLp.ofLp (w t)).1 := by
    unfold ergodicAvg
    simp only [WithLp.ofLp_smul, WithLp.ofLp_sum, Prod.smul_fst, Prod.fst_sum, Finset.smul_sum,
      smul_smul]
    rfl
  have hybar : (WithLp.ofLp (ergodicAvg γs w n)).2 =
      ∑ t ∈ Finset.Icc 1 n, (S⁻¹ * γs t) • (WithLp.ofLp (w t)).2 := by
    unfold ergodicAvg
    simp only [WithLp.ofLp_smul, WithLp.ofLp_sum, Prod.smul_snd, Prod.snd_sum, Finset.smul_sum,
      smul_smul]
    rfl
  have hJ1 : f ((WithLp.ofLp (ergodicAvg γs w n)).1, y) ≤
      ∑ t ∈ Finset.Icc 1 n, (S⁻¹ * γs t) • f ((WithLp.ofLp (w t)).1, y) := by
    rw [hxbar]
    exact (hf.2.2.2.2.1 y hy).map_sum_le hl0 hl1 (fun t ht => (hwZ t ht).1)
  have hJ2 : ∑ t ∈ Finset.Icc 1 n, (S⁻¹ * γs t) • f (x, (WithLp.ofLp (w t)).2) ≤
      f (x, (WithLp.ofLp (ergodicAvg γs w n)).2) := by
    rw [hybar]
    exact (hf.2.2.2.2.2 x hx).le_map_sum hl0 hl1 (fun t ht => (hwZ t ht).2)
  have hterm : ∀ t ∈ Finset.Icc 1 n,
      f ((WithLp.ofLp (w t)).1, y) - f (x, (WithLp.ofLp (w t)).2) ≤
        ⟪saddleOp fx fy (w t), w t - WithLp.toLp 2 (x, y)⟫_ℝ := by
    intro t ht
    obtain ⟨hxt, hyt⟩ := hwZ t ht
    have g1 := np_grad_convex (g := fun x' => f (x', (WithLp.ofLp (w t)).2))
      (hf.2.2.2.2.1 _ hyt) hxt hx (hf.1 _ hxt _ hyt)
    have g2 := np_grad_concave (g := fun y' => f ((WithLp.ofLp (w t)).1, y'))
      (hf.2.2.2.2.2 _ hxt) hyt hy (hf.2.1 _ hxt _ hyt)
    simp only [Prod.mk.eta, inner_sub_right] at g1 g2
    simp only [saddleOp, WithLp.prod_inner_apply, WithLp.ofLp_toLp, WithLp.ofLp_sub, Prod.fst_sub,
      Prod.snd_sub, inner_neg_left, inner_sub_right]
    linarith
  have hsum := np_sum_le_theta (np_prodSet_convex hXc hYc) (np_prodSet_compact hXk hYk) hω hrun
    (u := WithLp.toLp 2 (x, y)) ⟨hx, hy⟩
  have h3 : ∑ t ∈ Finset.Icc 1 n, (S⁻¹ * γs t) • f ((WithLp.ofLp (w t)).1, y) -
      ∑ t ∈ Finset.Icc 1 n, (S⁻¹ * γs t) • f (x, (WithLp.ofLp (w t)).2) ≤
      S⁻¹ * ∑ t ∈ Finset.Icc 1 n,
        γs t * ⟪saddleOp fx fy (w t), w t - WithLp.toLp 2 (x, y)⟫_ℝ := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun t ht => ?_
    simp only [smul_eq_mul]
    have := mul_le_mul_of_nonneg_left (hterm t ht) (hl0 t ht)
    calc S⁻¹ * γs t * f ((WithLp.ofLp (w t)).1, y) - S⁻¹ * γs t * f (x, (WithLp.ofLp (w t)).2)
        = S⁻¹ * γs t * (f ((WithLp.ofLp (w t)).1, y) - f (x, (WithLp.ofLp (w t)).2)) := by ring
      _ ≤ S⁻¹ * γs t * ⟪saddleOp fx fy (w t), w t - WithLp.toLp 2 (x, y)⟫_ℝ := this
      _ = S⁻¹ * (γs t * ⟪saddleOp fx fy (w t), w t - WithLp.toLp 2 (x, y)⟫_ℝ) := by ring
  have h4 := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hSpos.le)
  rw [div_eq_inv_mul]
  linarith

/-- Proposition 2.2, (2.14). -/
lemma np_saddle_bound {Ex Ey : Type*} [NormedAddCommGroup Ex] [InnerProductSpace ℝ Ex]
    [FiniteDimensional ℝ Ex] [NormedAddCommGroup Ey] [InnerProductSpace ℝ Ey]
    [FiniteDimensional ℝ Ey] {X : Set Ex} {Y : Set Ey} {f : Ex × Ey → ℝ} {fx : Ex × Ey → Ex}
    {fy : Ex × Ey → Ey} {N : Seminorm ℝ (WithLp 2 (Ex × Ey))} {α : ℝ}
    {ω : WithLp 2 (Ex × Ey) → ℝ} {ω' : WithLp 2 (Ex × Ey) → WithLp 2 (Ex × Ey)}
    (hXc : Convex ℝ X) (hXk : IsCompact X) (hYc : Convex ℝ Y) (hYk : IsCompact Y)
    (hf : IsSmoothConvexConcave X Y f fx fy) (hω : IsDistGen (prodSet X Y) N α ω ω')
    {γs εs : ℕ → ℝ} {z w : ℕ → WithLp 2 (Ex × Ey)} {n : ℕ} (hn : 1 ≤ n)
    (hrun : IsRelaxedCPMRun (prodSet X Y) (saddleOp fx fy) ω ω' γs εs z w n) :
    saddleGap X Y f (WithLp.ofLp (ergodicAvg γs w n)).1 (WithLp.ofLp (ergodicAvg γs w n)).2 ≤
      (Theta (prodSet X Y) ω ω' (z 0) + ∑ t ∈ Finset.Icc 1 n, εs t) /
        ∑ t ∈ Finset.Icc 1 n, γs t := by
  obtain ⟨hz0x, hz0y⟩ : (WithLp.ofLp (z 0)).1 ∈ X ∧ (WithLp.ofLp (z 0)).2 ∈ Y := hrun.1
  have hXne : X.Nonempty := ⟨_, hz0x⟩
  have hYne : Y.Nonempty := ⟨_, hz0y⟩
  have key : ∀ x ∈ X, ∀ y ∈ Y,
      f ((WithLp.ofLp (ergodicAvg γs w n)).1, y) - f (x, (WithLp.ofLp (ergodicAvg γs w n)).2) ≤
        (Theta (prodSet X Y) ω ω' (z 0) + ∑ t ∈ Finset.Icc 1 n, εs t) /
          ∑ t ∈ Finset.Icc 1 n, γs t :=
    fun x hx y hy => np_saddle_key hXc hXk hYc hYk hf hω hn hrun hx hy
  have hcx : ∀ y ∈ Y, ContinuousOn (fun x' => f (x', y)) X := fun y hy x hx =>
    HasFDerivWithinAt.continuousWithinAt (hf.1 x hx y hy)
  have hcy : ∀ x ∈ X, ContinuousOn (fun y' => f (x, y')) Y := fun x hx y hy =>
    HasFDerivWithinAt.continuousWithinAt (hf.2.1 x hx y hy)
  have hA : sSup ((fun y' => f ((WithLp.ofLp (ergodicAvg γs w n)).1, y')) '' Y) ≤
      sInf ((fun x' => f (x', (WithLp.ofLp (ergodicAvg γs w n)).2)) '' X) +
        (Theta (prodSet X Y) ω ω' (z 0) + ∑ t ∈ Finset.Icc 1 n, εs t) /
          ∑ t ∈ Finset.Icc 1 n, γs t := by
    refine csSup_le (hYne.image _) ?_
    rintro _ ⟨y, hy, rfl⟩
    have : f ((WithLp.ofLp (ergodicAvg γs w n)).1, y) -
        (Theta (prodSet X Y) ω ω' (z 0) + ∑ t ∈ Finset.Icc 1 n, εs t) /
          ∑ t ∈ Finset.Icc 1 n, γs t ≤
        sInf ((fun x' => f (x', (WithLp.ofLp (ergodicAvg γs w n)).2)) '' X) := by
      refine le_csInf (hXne.image _) ?_
      rintro _ ⟨x, hx, rfl⟩
      have := key x hx y hy
      dsimp only
      linarith
    dsimp only
    linarith
  have hC : sSup ((fun y' => sInf ((fun x' => f (x', y')) '' X)) '' Y) ≤
      sInf ((fun x' => sSup ((fun y' => f (x', y')) '' Y)) '' X) := by
    refine csSup_le (hYne.image _) ?_
    rintro _ ⟨y, hy, rfl⟩
    refine le_csInf (hXne.image _) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact le_trans (csInf_le (hXk.bddBelow_image (hcx y hy)) ⟨x, hx, rfl⟩)
      (le_csSup (hYk.bddAbove_image (hcy x hx)) ⟨y, hy, rfl⟩)
  unfold saddleGap
  linarith

end NemirovskiProx

universe u

open NemirovskiProx InnerProductSpace in
theorem solution :
    (∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      (Z : Set E) (N : Seminorm ℝ E) (α L : ℝ) (ω : E → ℝ) (ω' : E → E) (F : E → E),
      Convex ℝ Z → IsCompact Z → (∀ x, N x = 0 → x = 0) →
      IsDistGen Z N α ω ω' → IsLipMonotoneOn Z N L F →
      ∀ (γs εs : ℕ → ℝ) (z w : ℕ → E) (n : ℕ),
        (IsRelaxedCPMRun Z F ω ω' γs εs z w n →
          IsProxPointOn Z ω ω' (z n) (F (z n)) (z n) →
          ∀ u ∈ Z, 0 ≤ ⟪F (z n), u - z n⟫_ℝ) ∧
        (1 ≤ n → IsRelaxedCPMRun Z F ω ω' γs εs z w n →
          viError Z F (ergodicAvg γs w n) ≤
            (Theta Z ω ω' (z 0) + ∑ t ∈ Finset.Icc 1 n, εs t) / ∑ t ∈ Finset.Icc 1 n, γs t)) ∧
    (∀ {Ex Ey : Type u} [NormedAddCommGroup Ex] [InnerProductSpace ℝ Ex] [FiniteDimensional ℝ Ex]
      [NormedAddCommGroup Ey] [InnerProductSpace ℝ Ey] [FiniteDimensional ℝ Ey]
      (X : Set Ex) (Y : Set Ey) (f : Ex × Ey → ℝ) (fx : Ex × Ey → Ex) (fy : Ex × Ey → Ey)
      (N : Seminorm ℝ (WithLp 2 (Ex × Ey))) (α L : ℝ) (ω : WithLp 2 (Ex × Ey) → ℝ)
      (ω' : WithLp 2 (Ex × Ey) → WithLp 2 (Ex × Ey)),
      Convex ℝ X → IsCompact X → Convex ℝ Y → IsCompact Y →
      IsSmoothConvexConcave X Y f fx fy → (∀ x, N x = 0 → x = 0) →
      IsDistGen (prodSet X Y) N α ω ω' → IsLipMonotoneOn (prodSet X Y) N L (saddleOp fx fy) →
      ∀ (γs εs : ℕ → ℝ) (z w : ℕ → WithLp 2 (Ex × Ey)) (n : ℕ), 1 ≤ n →
        IsRelaxedCPMRun (prodSet X Y) (saddleOp fx fy) ω ω' γs εs z w n →
        saddleGap X Y f (WithLp.ofLp (ergodicAvg γs w n)).1 (WithLp.ofLp (ergodicAvg γs w n)).2 ≤
          (Theta (prodSet X Y) ω ω' (z 0) + ∑ t ∈ Finset.Icc 1 n, εs t) /
            ∑ t ∈ Finset.Icc 1 n, γs t) := by
  refine ⟨?_, ?_⟩
  · intro E _ _ _ Z N α L ω ω' F hZc hZk hN hω hF γs εs z w n
    refine ⟨fun hrun hfix u hu => ?_, fun hn hrun => np_vi_bound hZc hZk hω hF hn hrun⟩
    have := np_prox_foc hω hZc subset_rfl hfix hu
    rwa [show ω' (z n) + (F (z n) - ω' (z n)) = F (z n) by abel] at this
  · intro Ex Ey _ _ _ _ _ _ X Y f fx fy N α L ω ω' hXc hXk hYc hYk hf hN hω hF γs εs z w n hn hrun
    exact np_saddle_bound hXc hXk hYc hYk hf hω hn hrun
