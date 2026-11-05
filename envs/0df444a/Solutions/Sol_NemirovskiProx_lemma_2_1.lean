-- Prove2me | solution 1 for NemirovskiProx.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T17:36:34.694149+00:00
-- url     : https://prove2.me/submissions/aa3c8784-5841-47c5-b925-7cb8bae643f1

import Mathlib
import Definitions.Def_NemirovskiProx_dualNorm
import Definitions.Def_NemirovskiProx_IsDistGen
import Definitions.Def_NemirovskiProx_IsProxPointOn
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

/-- Lemma 3.1 (3.7.a)-(3.7.d). -/
theorem np_lemma_3_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Z : Set E} (hZc : Convex ℝ Z) (hZk : IsCompact Z)
    {N : Seminorm ℝ E} (hN : ∀ x, N x = 0 → x = 0)
    {α : ℝ} {ω : E → ℝ} {ω' : E → E} (hω : IsDistGen Z N α ω ω')
    {U : Set E} (hU : U.Nonempty) (hUc : Convex ℝ U) (hUcl : IsClosed U) (hUZ : U ⊆ Z)
    {z : E} (hz : z ∈ Z) (ξ η : E) {γ : ℝ} (hγ : 0 < γ) {w zp : E}
    (hw : IsProxPointOn U ω ω' z (γ • ξ) w) (hzp : IsProxPointOn U ω ω' z (γ • η) zp) :
    N (w - zp) ≤ α⁻¹ * γ * dualNorm N (ξ - η) ∧
      (∀ u ∈ U, ⟪γ • η, w - u⟫_ℝ ≤ Hfun Z ω ω' u z - Hfun Z ω ω' u zp +
          (⟪γ • η, w - zp⟫_ℝ + (ω z + ⟪ω' z, zp - z⟫_ℝ - ω zp))) ∧
      ⟪γ • η, w - zp⟫_ℝ + (ω z + ⟪ω' z, zp - z⟫_ℝ - ω zp) ≤
        ⟪γ • (η - ξ), w - zp⟫_ℝ + (ω z + ⟪ω' z, w - z⟫_ℝ + ⟪ω' w, zp - w⟫_ℝ - ω zp) ∧
      ⟪γ • (η - ξ), w - zp⟫_ℝ + (ω z + ⟪ω' z, w - z⟫_ℝ + ⟪ω' w, zp - w⟫_ℝ - ω zp) ≤
        α⁻¹ * γ ^ 2 * dualNorm N (ξ - η) ^ 2 - α / 2 * (N (w - z) ^ 2 + N (w - zp) ^ 2) := by
  have hα : 0 < α := hω.1
  have hwZ : w ∈ Z := hUZ hw.1
  have hzpZ : zp ∈ Z := hUZ hzp.1
  set D := dualNorm N (ξ - η) with hD
  have hD0 : 0 ≤ D := np_dual_nonneg hN _
  -- optimality conditions
  have hA : ∀ v ∈ U, 0 ≤ ⟪ω' w + (γ • ξ - ω' z), v - w⟫_ℝ := fun v hv =>
    np_prox_foc hω hUc hUZ hw hv
  have hB : ∀ v ∈ U, 0 ≤ ⟪ω' zp + (γ • η - ω' z), v - zp⟫_ℝ := fun v hv =>
    np_prox_foc hω hUc hUZ hzp hv
  have hA1 := hA zp hzp.1
  have hB1 := hB w hw.1
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left, inner_sub_right] at hA1 hB1
  -- strong monotonicity at w, zp
  have hmon := hω.2.2.2 w hwZ zp hzpZ
  simp only [inner_sub_left, inner_sub_right] at hmon
  -- dual bound
  have hdual := np_inner_le_dual hN (ξ - η) (zp - w)
  simp only [inner_sub_left, inner_sub_right] at hdual
  have hNsym : N (zp - w) = N (w - zp) := by rw [← map_neg_eq_map, neg_sub]
  rw [hNsym] at hdual
  -- (a)
  have ha : N (w - zp) ≤ α⁻¹ * γ * D := by
    have key : α * N (w - zp) ^ 2 ≤ γ * D * N (w - zp) := by
      have : α * N (w - zp) ^ 2 ≤ γ * (D * N (w - zp)) := by nlinarith
      linarith [mul_assoc γ D (N (w - zp))]
    have hn0 : 0 ≤ N (w - zp) := apply_nonneg N _
    rcases hn0.eq_or_lt with h0 | hpos
    · rw [← h0]; exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hα.le) hγ.le) hD0
    · have : α * N (w - zp) ≤ γ * D := by
        have h2 : N (w - zp) * (α * N (w - zp)) ≤ N (w - zp) * (γ * D) := by nlinarith
        exact le_of_mul_le_mul_left h2 hpos
      rw [mul_assoc, le_inv_mul_iff₀ hα]
      exact this
  refine ⟨ha, ?_, ?_, ?_⟩
  · -- (b)
    intro u hu
    have hBu := hB u hu
    rw [np_Hfun_eq hZc hω u hz, np_Hfun_eq hZc hω u hzpZ]
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left, inner_sub_right] at hBu ⊢
    linarith
  · -- (c)
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left, inner_sub_right] at ⊢
    linarith
  · -- (d)
    have hb1 := np_bregman_lb hZc hω hz hwZ
    have hb2 := np_bregman_lb hZc hω hwZ hzpZ
    have hNsym2 : N (zp - w) = N (w - zp) := hNsym
    have hNsym3 : N (w - z) = N (w - z) := rfl
    rw [hNsym2] at hb2
    have hdual' : γ * (⟪ξ, zp⟫_ℝ - ⟪η, zp⟫_ℝ - (⟪ξ, w⟫_ℝ - ⟪η, w⟫_ℝ)) ≤ γ * (D * N (w - zp)) :=
      mul_le_mul_of_nonneg_left hdual hγ.le
    have hsq : γ * (D * N (w - zp)) ≤ α⁻¹ * γ ^ 2 * D ^ 2 := by
      have := mul_le_mul_of_nonneg_left ha (mul_nonneg hγ.le hD0)
      calc γ * (D * N (w - zp)) = γ * D * N (w - zp) := by ring
        _ ≤ γ * D * (α⁻¹ * γ * D) := this
        _ = α⁻¹ * γ ^ 2 * D ^ 2 := by ring
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left, inner_sub_right] at hb1 hb2 ⊢
    linarith


end NemirovskiProx

open NemirovskiProx InnerProductSpace in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Z : Set E} (hZc : Convex ℝ Z) (hZk : IsCompact Z)
    {N : Seminorm ℝ E} (hN : ∀ x, N x = 0 → x = 0)
    {α : ℝ} {ω : E → ℝ} {ω' : E → E} (hω : IsDistGen Z N α ω ω') {z : E} (hz : z ∈ Z) :
    (∀ ξ η p q : E, IsProxPointOn Z ω ω' z ξ p → IsProxPointOn Z ω ω' z η q →
        N (p - q) ≤ α⁻¹ * dualNorm N (ξ - η)) ∧
      (∀ ξ p : E, IsProxPointOn Z ω ω' z ξ p →
        (∀ u ∈ Z, Hfun Z ω ω' u p - Hfun Z ω ω' u z ≤
            ⟪ξ, u - p⟫_ℝ + (ω z + ⟪ω' z, p - z⟫_ℝ - ω p)) ∧
          ω z + ⟪ω' z, p - z⟫_ℝ - ω p ≤ 0) := by
  refine ⟨fun ξ η p q hp hq => ?_, fun ξ p hp => ⟨fun u hu => ?_, ?_⟩⟩
  · have hp' : IsProxPointOn Z ω ω' z ((1:ℝ) • ξ) p := by rwa [one_smul]
    have hq' : IsProxPointOn Z ω ω' z ((1:ℝ) • η) q := by rwa [one_smul]
    have := (np_lemma_3_1 hZc hZk hN hω ⟨z, hz⟩ hZc hZk.isClosed subset_rfl hz ξ η one_pos hp' hq').1
    simpa using this
  · have hB := np_prox_foc hω hZc subset_rfl hp hu
    rw [np_Hfun_eq hZc hω u hp.1, np_Hfun_eq hZc hω u hz]
    simp only [inner_add_left, inner_sub_left, inner_sub_right] at hB ⊢
    linarith
  · have h := np_bregman_lb hZc hω hz hp.1
    have hα : 0 ≤ α / 2 * N (p - z) ^ 2 := mul_nonneg (by linarith [hω.1]) (sq_nonneg _)
    linarith
