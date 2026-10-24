-- Prove2me | solution 1 for KellyStochasticNetworks.FlowStability.generator_control
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T07:11:12.160621+00:00
-- url     : https://prove2.me/submissions/67e38b5b-f66b-4ac4-bc48-f63b9fd661e2

import Mathlib
import Definitions.Def_KellyStochasticNetworks_FlowStability_Process
import Theorems.Thm_KellyStochasticNetworks_FlowStability_supporting_utility

namespace X5GC

/-- Tangent-line bounds for `t ↦ t^p`, `p ≥ 1`, between `x` and `x+1`. -/
lemma pow_succ_sub_le {p x : ℝ} (hp : 1 ≤ p) (hx : 0 ≤ x) :
    (x + 1) ^ p - x ^ p ≤ p * (x + 1) ^ (p - 1) := by
  have h1 : (0:ℝ) < x + 1 := by linarith
  have hs : (-1:ℝ) ≤ -1 / (x + 1) := by
    rw [neg_div, neg_le_neg_iff, div_le_one h1]; linarith
  have hb := one_add_mul_self_le_rpow_one_add hs hp
  have he : 1 + -1 / (x + 1) = x / (x + 1) := by field_simp; ring
  rw [he, Real.div_rpow hx h1.le] at hb
  have hpos : 0 < (x + 1) ^ p := Real.rpow_pos_of_pos h1 p
  have hsub : (x + 1) ^ (p - 1) = (x + 1) ^ p / (x + 1) := Real.rpow_sub_one h1.ne' p
  rw [le_div_iff₀ hpos] at hb
  rw [hsub]
  have : (1 + p * (-1 / (x + 1))) * (x + 1) ^ p = (x + 1) ^ p - p * ((x + 1) ^ p / (x + 1)) := by
    field_simp; ring
  linarith

lemma pow_succ_sub_ge {p x : ℝ} (hp : 1 ≤ p) (hx : 0 ≤ x) :
    p * x ^ (p - 1) ≤ (x + 1) ^ p - x ^ p := by
  rcases hx.lt_or_eq with hx | hx
  · have hs : (-1:ℝ) ≤ 1 / x := by
      have : 0 ≤ 1 / x := by positivity
      linarith
    have hb := one_add_mul_self_le_rpow_one_add hs hp
    have he : 1 + 1 / x = (x + 1) / x := by field_simp
    rw [he, Real.div_rpow (by linarith) hx.le] at hb
    have hpos : 0 < x ^ p := Real.rpow_pos_of_pos hx p
    rw [le_div_iff₀ hpos] at hb
    have hsub : x ^ (p - 1) = x ^ p / x := Real.rpow_sub_one hx.ne' p
    rw [hsub]
    have : (1 + p * (1 / x)) * x ^ p = x ^ p + p * (x ^ p / x) := by field_simp
    linarith
  · subst hx
    rcases (show (0:ℝ) ≤ p - 1 by linarith).lt_or_eq with h | h
    · rw [Real.zero_rpow h.ne', Real.zero_rpow (by linarith)]; simp
    · have hp1 : p = 1 := by linarith
      subst hp1; simp

lemma g_nonneg {α x : ℝ} (hα : 0 < α) (hx : 0 ≤ x) : 0 ≤ (x + 1) ^ α - x ^ α := by
  have := Real.rpow_le_rpow hx (show x ≤ x + 1 by linarith) hα.le
  linarith

/-- `(x+1)^α - x^α = o(x^α)`, uniformly in the form needed. -/
lemma g_le {α : ℝ} (hα : 0 < α) {η : ℝ} (hη : 0 < η) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ x : ℝ, 0 ≤ x → (x + 1) ^ α - x ^ α ≤ η * x ^ α + b := by
  rcases le_or_gt α 1 with h1 | h1
  · refine ⟨1, zero_le_one, fun x hx => ?_⟩
    have := Real.rpow_add_le_add_rpow hx zero_le_one hα.le h1
    rw [Real.one_rpow] at this
    have : 0 ≤ η * x ^ α := mul_nonneg hη.le (Real.rpow_nonneg hx _)
    linarith
  · -- δ chosen so that α 2^(α-1) δ ≤ η
    set K : ℝ := α * (2:ℝ) ^ (α - 1) with hK
    have hKpos : 0 < K := mul_pos hα (Real.rpow_pos_of_pos (by norm_num) _)
    set T : ℝ := max 1 (K / η) with hT
    refine ⟨α * (T + 1) ^ (α - 1), by positivity, fun x hx => ?_⟩
    have hstep := pow_succ_sub_le (p := α) h1.le hx
    have hα1 : 0 ≤ α - 1 := by linarith
    rcases le_or_gt x T with hxT | hxT
    · have : (x + 1) ^ (α - 1) ≤ (T + 1) ^ (α - 1) :=
        Real.rpow_le_rpow (by linarith) (by linarith) hα1
      have : 0 ≤ η * x ^ α := mul_nonneg hη.le (Real.rpow_nonneg hx _)
      nlinarith
    · have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hxT.le
      have hxpos : 0 < x := by linarith
      have h2 : (x + 1) ^ (α - 1) ≤ (2 * x) ^ (α - 1) :=
        Real.rpow_le_rpow (by linarith) (by linarith) hα1
      rw [Real.mul_rpow (by norm_num) hxpos.le, Real.rpow_sub_one hxpos.ne'] at h2
      have hKx : K / η ≤ x := le_trans (le_max_right _ _) hxT.le
      have hKx' : K ≤ η * x := by rwa [div_le_iff₀ hη, mul_comm] at hKx
      have hxa : 0 ≤ x ^ α := Real.rpow_nonneg hx _
      have : α * (x + 1) ^ (α - 1) ≤ K * (x ^ α / x) := by
        rw [hK, mul_assoc]; exact mul_le_mul_of_nonneg_left h2 hα.le
      have : K * (x ^ α / x) ≤ η * x ^ α := by
        rw [mul_div_assoc', div_le_iff₀ hxpos]; nlinarith
      have : 0 ≤ α * (T + 1) ^ (α - 1) := by
        have : 0 ≤ T + 1 := by have := le_max_left 1 (K / η); linarith
        positivity
      linarith

/-- A positive lower bound for a finite positive family. -/
lemma exists_pos_le {ι : Type*} [Fintype ι] (a : ι → ℝ) (h : ∀ i, 0 < a i) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ i, κ ≤ a i := by
  have hs : 0 ≤ ∑ i, (a i)⁻¹ := Finset.sum_nonneg (fun i _ => (inv_pos.2 (h i)).le)
  refine ⟨(1 + ∑ i, (a i)⁻¹)⁻¹, by positivity, fun i => ?_⟩
  have hi := h i
  have : (a i)⁻¹ ≤ 1 + ∑ j, (a j)⁻¹ := by
    have := Finset.single_le_sum (f := fun j => (a j)⁻¹) (fun j _ => (inv_pos.2 (h j)).le)
      (Finset.mem_univ i)
    linarith
  calc (1 + ∑ j, (a j)⁻¹)⁻¹ ≤ ((a i)⁻¹)⁻¹ :=
        inv_anti₀ (inv_pos.2 hi) this
    _ = a i := inv_inv _

end X5GC


namespace X5GC
open KellyStochasticNetworks KellyStochasticNetworks.FlowStability

variable {J R : ℕ} (D : Network J R)

noncomputable def cc (r : Fin R) : ℝ := D.w r / D.mu r * offeredLoad D r ^ (-D.alpha)

lemma rho_pos (r : Fin R) : 0 < offeredLoad D r :=
  div_pos (D.arrival_pos r) (D.service_pos r)

lemma cc_pos (r : Fin R) : 0 < cc D r :=
  mul_pos (div_pos (D.weight_pos r) (D.service_pos r)) (Real.rpow_pos_of_pos (rho_pos D r) _)

lemma lyap_update (n : State R) (r : Fin R) (v : ℕ) :
    lyapunov D (Function.update n r v) - lyapunov D n =
      cc D r * ((v : ℝ) ^ (D.alpha + 1) / (D.alpha + 1) -
        (n r : ℝ) ^ (D.alpha + 1) / (D.alpha + 1)) := by
  unfold lyapunov
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
  have : ∑ x ∈ Finset.univ.erase r, D.w x / D.mu x * offeredLoad D x ^ (-D.alpha) *
      (((Function.update n r v x : ℕ) : ℝ) ^ (D.alpha + 1) / (D.alpha + 1)) =
      ∑ x ∈ Finset.univ.erase r, D.w x / D.mu x * offeredLoad D x ^ (-D.alpha) *
      ((n x : ℝ) ^ (D.alpha + 1) / (D.alpha + 1)) := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [this, Function.update_self]; unfold cc; ring

lemma fd_term (n : State R) (X : Fin R → ℝ) (r : Fin R) :
    D.w r * offeredLoad D r ^ (-D.alpha) * (n r : ℝ) ^ D.alpha * (offeredLoad D r - X r) =
      cc D r * D.nu r * (n r : ℝ) ^ D.alpha - cc D r * D.mu r * X r * (n r : ℝ) ^ D.alpha := by
  unfold cc offeredLoad
  have hm := (D.service_pos r).ne'
  set P := (D.nu r / D.mu r) ^ (-D.alpha)
  field_simp

/-- Per-route bound of the generator against the first-order drift. -/
lemma route_bound (n : State R) (X : Fin R → ℝ) (r : Fin R) (Xb : ℝ)
    (hX0 : 0 ≤ X r) (hXb : X r ≤ Xb) (hXz : n r = 0 → X r = 0)
    {η' b' : ℝ} (hb' : 0 ≤ b') (hη' : 0 < η')
    (hg : ∀ x : ℝ, 0 ≤ x → (x + 1) ^ D.alpha - x ^ D.alpha ≤ η' * x ^ D.alpha + b') :
    D.nu r * (lyapunov D (birth n r) - lyapunov D n) +
      (if 0 < n r then D.mu r * X r * (lyapunov D (death n r) - lyapunov D n) else 0) ≤
    D.w r * offeredLoad D r ^ (-D.alpha) * (n r : ℝ) ^ D.alpha * (offeredLoad D r - X r) +
      (cc D r * D.nu r + cc D r * D.mu r * Xb) * (η' * (n r : ℝ) ^ D.alpha + b') := by
  have hα := D.alpha_pos
  have hc := cc_pos D r
  have hν := D.nu r
  have hνp := D.arrival_pos r
  have hμp := D.service_pos r
  rw [fd_term]
  set a : ℝ := D.alpha
  set x : ℝ := (n r : ℝ) with hx
  have hx0 : 0 ≤ x := Nat.cast_nonneg _
  have hxa : 0 ≤ x ^ a := Real.rpow_nonneg hx0 _
  have hE : 0 ≤ η' * x ^ a + b' := by positivity
  -- birth
  have hbirth : lyapunov D (birth n r) - lyapunov D n ≤ cc D r * (x ^ a + (η' * x ^ a + b')) := by
    unfold birth; rw [lyap_update]
    push_cast
    have h1 := pow_succ_sub_le (p := a + 1) (by linarith) hx0
    rw [add_sub_cancel_right] at h1
    have h2 := hg x hx0
    have : ((x + 1) ^ (a + 1) / (a + 1) - x ^ (a + 1) / (a + 1)) ≤ (x + 1) ^ a := by
      rw [← sub_div, div_le_iff₀ (by linarith)]; linarith
    have : (x + 1) ^ a ≤ x ^ a + (η' * x ^ a + b') := by linarith
    exact mul_le_mul_of_nonneg_left (by linarith) hc.le
  have hB : D.nu r * (lyapunov D (birth n r) - lyapunov D n) ≤
      cc D r * D.nu r * x ^ a + cc D r * D.nu r * (η' * x ^ a + b') := by
    have := mul_le_mul_of_nonneg_left hbirth hνp.le
    linarith
  -- death
  have hD : (if 0 < n r then D.mu r * X r * (lyapunov D (death n r) - lyapunov D n) else 0) ≤
      - (cc D r * D.mu r * X r * x ^ a) + cc D r * D.mu r * Xb * (η' * x ^ a + b') := by
    split_ifs with hn
    · unfold death; rw [lyap_update]
      have hy : (((n r - 1 : ℕ) : ℝ)) = x - 1 := by rw [hx]; push_cast [Nat.one_le_iff_ne_zero.2 hn.ne']; ring
      rw [hy]
      have hx1 : 0 ≤ x - 1 := by
        have : (1:ℝ) ≤ x := by rw [hx]; exact_mod_cast hn
        linarith
      have h1 := pow_succ_sub_ge (p := a + 1) (by linarith) hx1
      rw [add_sub_cancel_right, sub_add_cancel] at h1
      have h2 := hg (x - 1) hx1
      rw [sub_add_cancel] at h2
      have hmono : (x - 1) ^ a ≤ x ^ a := Real.rpow_le_rpow hx1 (by linarith) hα.le
      have h3 : (x - 1) ^ (a + 1) / (a + 1) - x ^ (a + 1) / (a + 1) ≤ -(x - 1) ^ a := by
        rw [← sub_div, div_le_iff₀ (by linarith)]; linarith
      have hgx : 0 ≤ x ^ a - (x - 1) ^ a := by linarith
      have hg2 : x ^ a - (x - 1) ^ a ≤ η' * x ^ a + b' := by
        have : η' * (x - 1) ^ a ≤ η' * x ^ a := mul_le_mul_of_nonneg_left hmono hη'.le
        linarith
      have hcm : 0 ≤ cc D r * D.mu r * X r := by positivity
      have k1 := mul_le_mul_of_nonneg_left h3 hcm
      have k2 : cc D r * D.mu r * X r * (x ^ a - (x - 1) ^ a) ≤
          cc D r * D.mu r * Xb * (x ^ a - (x - 1) ^ a) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXb (by positivity)) hgx
      have k3 : cc D r * D.mu r * Xb * (x ^ a - (x - 1) ^ a) ≤
          cc D r * D.mu r * Xb * (η' * x ^ a + b') :=
        mul_le_mul_of_nonneg_left hg2 (by have : 0 ≤ Xb := le_trans hX0 hXb; positivity)
      have : D.mu r * X r * (cc D r * ((x - 1) ^ (a + 1) / (a + 1) - x ^ (a + 1) / (a + 1))) =
        cc D r * D.mu r * X r * ((x - 1) ^ (a + 1) / (a + 1) - x ^ (a + 1) / (a + 1)) := by ring
      rw [this]
      nlinarith
    · have hn0 : n r = 0 := by omega
      rw [hXz hn0]
      have : 0 ≤ Xb := le_trans hX0 hXb
      have : 0 ≤ cc D r * D.mu r * Xb * (η' * x ^ a + b') := by positivity
      linarith
  linarith

end X5GC


namespace X5GC
open KellyStochasticNetworks KellyStochasticNetworks.FlowStability

variable {J R : ℕ} (D : Network J R)

noncomputable def Xb : ℝ := ∑ j, D.C j

lemma A_nonneg (j : Fin J) (r : Fin R) : 0 ≤ D.A j r := by
  rcases D.incidence j r with h | h <;> rw [h]; norm_num

lemma X_facts {X : State R → Fin R → ℝ} (hX : IsAlphaFair D X) (n : State R) (r : Fin R) :
    0 ≤ X n r ∧ X n r ≤ Xb D ∧ (n r = 0 → X n r = 0) := by
  obtain ⟨⟨⟨h0, hC⟩, hz, -⟩, -⟩ := hX n
  refine ⟨h0 r, ?_, hz r⟩
  obtain ⟨j, hj⟩ := D.route_nonempty r
  have h1 : X n r ≤ linkFlow D.A (X n) j := by
    unfold linkFlow
    have := Finset.single_le_sum (f := fun r' => D.A j r' * X n r')
      (fun r' _ => mul_nonneg (A_nonneg D j r') (h0 r')) (Finset.mem_univ r)
    simp only [hj, one_mul] at this; exact this
  have h2 : D.C j ≤ Xb D := Finset.single_le_sum (f := fun j => D.C j)
    (fun j _ => (D.capacity_pos j).le) (Finset.mem_univ j)
  linarith [hC j]

theorem part1 (X : State R → Fin R → ℝ) (hX : IsAlphaFair D X) :
    ∀ eta : ℝ, 0 < eta → ∃ b : ℝ, 0 ≤ b ∧ ∀ n : State R,
      generator D X (lyapunov D) n ≤ firstOrderDrift D X n +
        eta * (∑ r, (n r : ℝ) ^ D.alpha) + b := by
  intro η hη
  set co : Fin R → ℝ := fun r => cc D r * D.nu r + cc D r * D.mu r * Xb D with hco
  have hXb : 0 ≤ Xb D := Finset.sum_nonneg (fun j _ => (D.capacity_pos j).le)
  have hco0 : ∀ r, 0 ≤ co r := fun r => by
    have := cc_pos D r; have := D.arrival_pos r; have := D.service_pos r
    simp only [hco]; positivity
  set K := ∑ r, co r
  have hK : 0 ≤ K := Finset.sum_nonneg (fun r _ => hco0 r)
  set η' := η / (1 + K)
  have hη' : 0 < η' := div_pos hη (by linarith)
  obtain ⟨b', hb', hg⟩ := g_le D.alpha_pos hη'
  refine ⟨K * b', mul_nonneg hK hb', fun n => ?_⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun r _ =>
    route_bound D n (X n) r (Xb D) (X_facts D hX n r).1 (X_facts D hX n r).2.1
      (X_facts D hX n r).2.2 hb' hη' hg)
  unfold generator firstOrderDrift
  refine le_trans hsum ?_
  rw [Finset.sum_add_distrib]
  have : ∑ r, co r * (η' * (n r : ℝ) ^ D.alpha + b') ≤
      η * ∑ r, (n r : ℝ) ^ D.alpha + K * b' := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun r _ => ?_)
    have hcoK : co r ≤ K := Finset.single_le_sum (f := co) (fun r _ => hco0 r)
      (Finset.mem_univ r)
    have h1 : co r * η' ≤ η := by
      calc co r * η' ≤ (1 + K) * η' := mul_le_mul_of_nonneg_right (by linarith) hη'.le
        _ = η := by simp only [η']; field_simp
    have h2 := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (Nat.cast_nonneg (n r)) D.alpha)
    have : co r * (η' * (n r : ℝ) ^ D.alpha + b') =
      co r * η' * (n r : ℝ) ^ D.alpha + co r * b' := by ring
    rw [this]; linarith
  linarith

/-- First-order drift under subcriticality, via (8.5). -/
lemma drift_neg (hsub : Subcritical D) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (X : State R → Fin R → ℝ), IsAlphaFair D X → ∀ n : State R,
      firstOrderDrift D X n ≤
        -(ε * ∑ r, D.w r * offeredLoad D r ^ (-D.alpha) * offeredLoad D r * (n r : ℝ) ^ D.alpha) := by
  set lf := fun j => linkFlow D.A (offeredLoad D) j
  have hlf0 : ∀ j, 0 ≤ lf j := fun j => Finset.sum_nonneg (fun r _ =>
    mul_nonneg (A_nonneg D j r) (rho_pos D r).le)
  obtain ⟨ε, hε, hεle⟩ := exists_pos_le (fun j => (D.C j - lf j) / (lf j + 1))
    (fun j => div_pos (by have := hsub j; simp only [lf]; linarith) (by linarith [hlf0 j]))
  refine ⟨ε, hε, fun X hX n => ?_⟩
  have hα := D.alpha_pos
  set U : Fin R → ℝ := fun r => if 0 < n r then (1 + ε) * offeredLoad D r else 0 with hU
  have hUfeas : U ∈ networkFeasible D.A D.C := by
    refine ⟨fun r => ?_, fun j => ?_⟩
    · simp only [hU]; split_ifs
      · have := rho_pos D r; positivity
      · exact le_rfl
    · have h1 : linkFlow D.A U j ≤ (1 + ε) * lf j := by
        simp only [lf, linkFlow, Finset.mul_sum]
        refine Finset.sum_le_sum (fun r _ => ?_)
        have hA := A_nonneg D j r
        simp only [hU]; split_ifs
        · nlinarith
        · have := rho_pos D r; nlinarith [mul_nonneg hA (mul_nonneg (by linarith : (0:ℝ) ≤ 1 + ε) this.le)]
      have h2 := hεle j
      have h3 : ε * lf j ≤ D.C j - lf j := by
        have hl := hlf0 j
        have : ε * (lf j + 1) ≤ D.C j - lf j := by
          rwa [le_div_iff₀ (by linarith)] at h2
        nlinarith
      linarith
  have hUpos : ∀ r, 0 < n r → 0 < U r := fun r hr => by
    simp only [hU, if_pos hr]; have := rho_pos D r; positivity
  have hS := supporting_utility D X hX n U hUfeas hUpos
  have hS0 := le_trans hS.1 hS.2
  rw [Finset.sum_filter] at hS0
  -- termwise identity
  have hterm : ∀ r, D.w r * offeredLoad D r ^ (-D.alpha) * (n r : ℝ) ^ D.alpha *
      (offeredLoad D r - X n r) =
      (1 + ε) ^ D.alpha * (if 0 < n r then D.w r * (n r : ℝ) ^ D.alpha * U r ^ (-D.alpha) *
        (U r - X n r) else 0) -
      ε * (D.w r * offeredLoad D r ^ (-D.alpha) * offeredLoad D r * (n r : ℝ) ^ D.alpha) := by
    intro r
    split_ifs with hn
    · simp only [hU, if_pos hn]
      have hρ := rho_pos D r
      rw [Real.mul_rpow (by linarith) hρ.le]
      have he : (1 + ε) ^ D.alpha * (1 + ε) ^ (-D.alpha) = 1 := by
        rw [Real.rpow_neg (by linarith), mul_inv_cancel₀ (Real.rpow_pos_of_pos (by linarith) _).ne']
      linear_combination (-1 : ℝ) * (D.w r * (n r : ℝ) ^ D.alpha * offeredLoad D r ^ (-D.alpha) *
        ((1 + ε) * offeredLoad D r - X n r)) * he
    · have : n r = 0 := by omega
      rw [this]; push_cast; rw [Real.zero_rpow hα.ne']; ring
  unfold firstOrderDrift
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have : (1 + ε) ^ D.alpha * ∑ r, (if 0 < n r then D.w r * (n r : ℝ) ^ D.alpha *
      U r ^ (-D.alpha) * (U r - X n r) else 0) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by linarith) _) hS0
  linarith

theorem part2 (X : State R → Fin R → ℝ) (hX : IsAlphaFair D X) :
    Subcritical D → ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ K : ℕ, ∃ b : ℝ,
      ∀ n : State R, generator D X (lyapunov D) n ≤
        if (∑ r, n r) ≤ K then b - epsilon else -epsilon := by
  intro hsub
  have hα := D.alpha_pos
  obtain ⟨ε, hε, hdrift⟩ := drift_neg D hsub
  obtain ⟨κ, hκ, hκle⟩ := exists_pos_le
    (fun r => ε * (D.w r * offeredLoad D r ^ (-D.alpha) * offeredLoad D r))
    (fun r => by
      have := rho_pos D r; have := D.weight_pos r
      have := Real.rpow_pos_of_pos (rho_pos D r) (-D.alpha); positivity)
  obtain ⟨b, hb, hgen⟩ := part1 D X hX (κ / 2) (by linarith)
  have key : ∀ n : State R, generator D X (lyapunov D) n ≤
      -(κ / 2) * ∑ r, (n r : ℝ) ^ D.alpha + b := by
    intro n
    have h1 := hgen n
    have h2 := hdrift X hX n
    have h3 : κ * ∑ r, (n r : ℝ) ^ D.alpha ≤
        ε * ∑ r, D.w r * offeredLoad D r ^ (-D.alpha) * offeredLoad D r * (n r : ℝ) ^ D.alpha := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum (fun r _ => ?_)
      have := mul_le_mul_of_nonneg_right (hκle r) (Real.rpow_nonneg (Nat.cast_nonneg (n r)) D.alpha)
      linarith
    linarith
  set T : ℝ := 2 * (b + 1) / κ
  have hT : 0 ≤ T := by positivity
  set M : ℕ := ⌈T ^ D.alpha⁻¹⌉₊
  refine ⟨1, one_pos, R * M, b + 1, fun n => ?_⟩
  have hS0 : 0 ≤ ∑ r, (n r : ℝ) ^ D.alpha :=
    Finset.sum_nonneg (fun r _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  split_ifs with hK
  · have := key n; nlinarith
  · push_neg at hK
    obtain ⟨r, hr⟩ : ∃ r, M < n r := by
      by_contra hcon
      push_neg at hcon
      have : ∑ r, n r ≤ ∑ _r : Fin R, M := Finset.sum_le_sum (fun r _ => hcon r)
      simp at this; omega
    have hr' : T ^ D.alpha⁻¹ ≤ (n r : ℝ) := by
      calc T ^ D.alpha⁻¹ ≤ (M : ℝ) := Nat.le_ceil _
        _ ≤ n r := by exact_mod_cast hr.le
    have h1 : T ≤ (n r : ℝ) ^ D.alpha := by
      calc T = (T ^ D.alpha⁻¹) ^ D.alpha := (Real.rpow_inv_rpow hT hα.ne').symm
        _ ≤ (n r : ℝ) ^ D.alpha := Real.rpow_le_rpow (Real.rpow_nonneg hT _) hr' hα.le
    have h2 : (n r : ℝ) ^ D.alpha ≤ ∑ r, (n r : ℝ) ^ D.alpha :=
      Finset.single_le_sum (f := fun r => (n r : ℝ) ^ D.alpha)
        (fun r _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) (Finset.mem_univ r)
    have hkT : κ / 2 * T = b + 1 := by simp only [T]; field_simp
    have := key n
    have : κ / 2 * T ≤ κ / 2 * ∑ r, (n r : ℝ) ^ D.alpha :=
      mul_le_mul_of_nonneg_left (le_trans h1 h2) (by linarith)
    linarith

end X5GC


open KellyStochasticNetworks KellyStochasticNetworks.FlowStability in
theorem solution {J R : ℕ} (D : Network J R)
    (X : State R → Fin R → ℝ) (hX : IsAlphaFair D X) :
    (∀ eta : ℝ, 0 < eta → ∃ b : ℝ, 0 ≤ b ∧ ∀ n : State R,
      generator D X (lyapunov D) n ≤ firstOrderDrift D X n +
        eta * (∑ r, (n r : ℝ) ^ D.alpha) + b) ∧
    (Subcritical D → ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ K : ℕ, ∃ b : ℝ,
      ∀ n : State R, generator D X (lyapunov D) n ≤
        if (∑ r, n r) ≤ K then b - epsilon else -epsilon) :=
  ⟨X5GC.part1 D X hX, X5GC.part2 D X hX⟩

