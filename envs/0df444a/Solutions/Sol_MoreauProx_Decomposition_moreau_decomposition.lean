-- Prove2me | solution 1 for MoreauProx.Decomposition.moreau_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T03:05:07.942071+00:00
-- url     : https://prove2.me/submissions/a29ce914-3aed-42e3-9ca3-176f9073ac44

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_ConvexDuality

set_option autoImplicit false

/-- If `0 ≤ K + t * M` for all `t ∈ (0, 1]` with `M ≥ 0`, then `0 ≤ K`. -/
theorem mdp_nonneg_of_forall {K M : ℝ} (hM : 0 ≤ M)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ K + t * M) : 0 ≤ K := by
  by_contra hK'
  have hK : K < 0 := not_le.mp hK'
  set s : ℝ := -K / (2 * (M + 1)) with hs
  have hM1 : 0 < 2 * (M + 1) := by linarith
  have hs0 : 0 < s := div_pos (neg_pos.mpr hK) hM1
  have hsM : s * (2 * (M + 1)) = -K := by
    rw [hs]; field_simp
  set t : ℝ := min 1 s with ht
  have ht0 : 0 < t := lt_min one_pos hs0
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ s := min_le_right _ _
  have h1 := h t ht0 ht1
  have h2 : t * M ≤ s * M := mul_le_mul_of_nonneg_right ht2 hM
  nlinarith

/-- A sum of two extended reals equal to a real forces both summands to be real. -/
theorem mdp_add_eq_coe {p q : EReal} {r : ℝ} (h : p + q = (r : EReal)) :
    ∃ a b : ℝ, p = (a : EReal) ∧ q = (b : EReal) ∧ a + b = r := by
  induction p using EReal.rec with
  | bot => simp at h
  | top =>
    induction q using EReal.rec with
    | bot => simp at h
    | top => simp at h
    | coe b => simp at h
  | coe a =>
    induction q using EReal.rec with
    | bot => simp at h
    | top => simp at h
    | coe b => exact ⟨a, b, rfl, rfl, by exact_mod_cast h⟩

open MoreauProx.Decomposition in open scoped InnerProductSpace in
/-- Fenchel–Young, easy direction. -/
theorem mdp_fy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (u y : H) :
    ((⟪u, y⟫_ℝ : ℝ) : EReal) - f u ≤ conj f y :=
  le_iSup (fun x => ((⟪x, y⟫_ℝ : ℝ) : EReal) - f x) u

open MoreauProx.Decomposition in
/-- A proximal point of a `Γ₀` function has a finite value. -/
theorem mdp_prox_finite {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : GammaZero f) (z x : H) (hp : IsProx f z x) :
    ∃ a : ℝ, f x = (a : EReal) := by
  obtain ⟨x0, hx0⟩ := hf.exists_ne_top
  have h := hp x0
  unfold proxObjective at h
  have hne : f x ≠ ⊤ := by
    intro htop
    rw [htop, EReal.coe_add_top] at h
    have hc := (EReal.coe_toReal hx0 (hf.ne_bot x0)).symm
    rw [hc, ← EReal.coe_add, top_le_iff] at h
    exact EReal.coe_ne_top _ h
  exact ⟨(f x).toReal, (EReal.coe_toReal hne (hf.ne_bot x)).symm⟩

open MoreauProx.Decomposition in open scoped InnerProductSpace in
/-- Variational inequality from minimality of the proximal objective and convexity. -/
theorem mdp_varineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : GammaZero f) (z x : H) (a : ℝ) (hfx : f x = (a : EReal))
    (hp : IsProx f z x) (u : H) (c : ℝ) (hfu : f u = (c : EReal)) :
    ⟪u - x, z - x⟫_ℝ ≤ c - a := by
  have key : 0 ≤ (c - a - ⟪u - x, z - x⟫_ℝ) := by
    refine mdp_nonneg_of_forall (M := ‖u - x‖ ^ 2 / 2) (by positivity) ?_
    intro t ht0 ht1
    have hxe : (x, a) ∈ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)} := by
      simp only [Set.mem_ofPred_eq, hfx, le_refl]
    have hue : (u, c) ∈ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)} := by
      simp only [Set.mem_ofPred_eq, hfu, le_refl]
    have hconv := hf.convex_epigraph hxe hue (a := 1 - t) (b := t) (by linarith) ht0.le
      (by ring)
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hconv
    have hpr := hp ((1 - t) • x + t • u)
    unfold proxObjective at hpr
    rw [hfx] at hpr
    have h2 := hpr.trans (add_le_add le_rfl hconv)
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h2
    have heq : (1 - t) • x + t • u - z = t • (u - x) - (z - x) := by
      simp only [sub_smul, one_smul, smul_sub]; abel
    rw [heq, norm_sub_rev x z, norm_sub_sq_real (t • (u - x)) (z - x), norm_smul,
      real_inner_smul_left] at h2
    have hn : (‖t‖ * ‖u - x‖) ^ 2 = t ^ 2 * ‖u - x‖ ^ 2 := by
      rw [mul_pow, Real.norm_eq_abs, sq_abs]
    rw [hn] at h2
    by_contra hneg'
    have hneg := not_le.mp hneg'
    have : t * (c - a - ⟪u - x, z - x⟫_ℝ + t * (‖u - x‖ ^ 2 / 2)) < 0 :=
      mul_neg_of_pos_of_neg ht0 hneg
    nlinarith
  linarith

open MoreauProx.Decomposition in open scoped InnerProductSpace in
/-- The conjugate at `z - x` is bounded by the Fenchel–Young value. -/
theorem mdp_conj_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : GammaZero f) (z x : H) (a : ℝ) (hfx : f x = (a : EReal))
    (hp : IsProx f z x) :
    conj f (z - x) ≤ ((⟪x, z - x⟫_ℝ - a : ℝ) : EReal) := by
  unfold conj
  refine iSup_le fun u => ?_
  have hne := hf.ne_bot u
  induction hfu : f u using EReal.rec with
  | bot => exact absurd hfu hne
  | top => simp
  | coe c =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    have := mdp_varineq f hf z x a hfx hp u c hfu
    rw [inner_sub_left] at this
    linarith

open MoreauProx.Decomposition in open scoped InnerProductSpace in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f g : H → EReal) (hf : GammaZero f) (hg : g = conj f) (x y z : H) :
    (z = x + y ∧ f x + g y = ((⟪x, y⟫_ℝ : ℝ) : EReal)) ↔ (IsProx f z x ∧ IsProx g z y) := by
  subst hg
  constructor
  · rintro ⟨rfl, hsum⟩
    obtain ⟨a, b, hfx, hgy, hab⟩ := mdp_add_eq_coe hsum
    refine ⟨fun u => ?_, fun v => ?_⟩
    · unfold proxObjective
      rw [hfx]
      have hne := hf.ne_bot u
      induction hfu : f u using EReal.rec with
      | bot => exact absurd hfu hne
      | top => simp
      | coe c =>
        have hfy := mdp_fy f u y
        rw [hfu, hgy, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hfy
        rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
        have e1 : x - (x + y) = -y := by abel
        have e2 : u - (x + y) = (u - x) - y := by abel
        rw [e1, e2, norm_neg, norm_sub_sq_real]
        have e3 : ⟪u, y⟫_ℝ = ⟪u - x, y⟫_ℝ + ⟪x, y⟫_ℝ := by rw [inner_sub_left]; ring
        nlinarith [sq_nonneg ‖u - x‖]
    · unfold proxObjective
      rw [hgy]
      have hfy := mdp_fy f x v
      rw [hfx, ← EReal.coe_sub] at hfy
      refine le_trans ?_ (add_le_add le_rfl hfy)
      rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have e1 : y - (x + y) = -x := by abel
      have e2 : v - (x + y) = (v - y) - x := by abel
      rw [e1, e2, norm_neg, norm_sub_sq_real]
      have e3 : ⟪x, v⟫_ℝ = ⟪v - y, x⟫_ℝ + ⟪x, y⟫_ℝ := by
        rw [inner_sub_left, real_inner_comm x v, real_inner_comm x y]; ring
      nlinarith [sq_nonneg ‖v - y‖]
  · rintro ⟨hpx, hpy⟩
    obtain ⟨a, hfx⟩ := mdp_prox_finite f hf z x hpx
    have hgw := mdp_conj_le f hf z x a hfx hpx
    have hgw' := mdp_fy f x (z - x)
    rw [hfx, ← EReal.coe_sub] at hgw'
    have hgweq : conj f (z - x) = ((⟪x, z - x⟫_ℝ - a : ℝ) : EReal) := le_antisymm hgw hgw'
    have hgy := mdp_fy f x y
    rw [hfx, ← EReal.coe_sub] at hgy
    have h1 := hpy (z - x)
    unfold proxObjective at h1
    rw [hgweq] at h1
    have h2 := (add_le_add le_rfl hgy).trans h1
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h2
    have e1 : z - x - z = -x := by abel
    have e2 : y - z = (y - (z - x)) - x := by abel
    rw [e1, e2, norm_neg, norm_sub_sq_real] at h2
    have e3 : ⟪x, y⟫_ℝ = ⟪y - (z - x), x⟫_ℝ + ⟪x, z - x⟫_ℝ := by
      rw [inner_sub_left, real_inner_comm x y, real_inner_comm x (z - x)]; ring
    have h3 : ‖y - (z - x)‖ ^ 2 ≤ 0 := by nlinarith
    have h4 : ‖y - (z - x)‖ = 0 := by
      have := sq_nonneg ‖y - (z - x)‖
      have h5 : ‖y - (z - x)‖ ^ 2 = 0 := le_antisymm h3 this
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h5
    have hyw : y = z - x := sub_eq_zero.mp (norm_eq_zero.mp h4)
    refine ⟨by rw [hyw]; abel, ?_⟩
    rw [hyw, hgweq, hfx, ← EReal.coe_add]
    congr 1
    ring
