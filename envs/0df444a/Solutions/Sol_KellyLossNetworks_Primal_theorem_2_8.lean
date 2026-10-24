-- Prove2me | solution 1 for KellyLossNetworks.Primal.theorem_2_8
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T07:23:47.094081+00:00
-- url     : https://prove2.me/submissions/0af0d9c2-cf60-490a-be74-30b9b0f30150

import Mathlib
import Definitions.Def_KellyLossNetworks_Primal_Problem

namespace X5KL
open KellyLossNetworks.Primal KellyStochasticNetworks

variable {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ) (C : Fin J → ℕ)

/-- Route "price" `(Aᵀ y)_r`. -/
noncomputable def ar (y : Fin J → ℝ) (r : Fin R) : ℝ := ∑ j, y j * (A j r : ℝ)

/-- Karush–Kuhn–Tucker conditions for the dual variable `y`. -/
def KKT (y : Fin J → ℝ) : Prop :=
  (∀ j, 0 ≤ y j) ∧ (∀ j, (∑ r, (A j r : ℝ) * primalPoint A ν y r) ≤ (C j : ℝ)) ∧
    (∀ j, 0 < y j → (∑ r, (A j r : ℝ) * primalPoint A ν y r) = (C j : ℝ))

lemma pp_eq (y : Fin J → ℝ) (r : Fin R) : primalPoint A ν y r = ν r * Real.exp (-ar A y r) := rfl

lemma pp_pos (hν : ∀ r, 0 < ν r) (y : Fin J → ℝ) (r : Fin R) : 0 < primalPoint A ν y r :=
  mul_pos (hν r) (Real.exp_pos _)

/-- Per-route bound: `u (log ν - a) - u log u + u ≤ ν e^{-a}` with equality iff `u = ν e^{-a}`. -/
lemma psi_le {v a u : ℝ} (hv : 0 < v) (hu : 0 ≤ u) :
    u * Real.log v - u * Real.log u + u - u * a ≤ v * Real.exp (-a) := by
  rcases hu.lt_or_eq with hu | hu
  · set m := v * Real.exp (-a)
    have hm : 0 < m := mul_pos hv (Real.exp_pos _)
    have hlog : Real.log m = Real.log v - a := by
      simp only [m]; rw [Real.log_mul hv.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
    have h := Real.log_le_sub_one_of_pos (div_pos hm hu)
    rw [Real.log_div hm.ne' hu.ne', hlog] at h
    have : u * (Real.log v - a - Real.log u) ≤ u * (m / u - 1) := mul_le_mul_of_nonneg_left h hu.le
    have e : u * (m / u - 1) = m - u := by field_simp
    linarith
  · subst hu; simp; exact (mul_pos hv (Real.exp_pos _)).le

lemma psi_eq {v a u : ℝ} (hv : 0 < v) (hu : 0 ≤ u)
    (h : v * Real.exp (-a) ≤ u * Real.log v - u * Real.log u + u - u * a) :
    u = v * Real.exp (-a) := by
  set m := v * Real.exp (-a)
  have hm : 0 < m := mul_pos hv (Real.exp_pos _)
  rcases hu.lt_or_eq with hu | hu
  · by_contra hne
    have hlog : Real.log m = Real.log v - a := by
      simp only [m]; rw [Real.log_mul hv.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
    have h1 : m / u ≠ 1 := by
      intro h1; apply hne; field_simp at h1; linarith
    have h2 := Real.log_lt_sub_one_of_pos (div_pos hm hu) h1
    rw [Real.log_div hm.ne' hu.ne', hlog] at h2
    have : u * (Real.log v - a - Real.log u) < u * (m / u - 1) := mul_lt_mul_of_pos_left h2 hu
    have e : u * (m / u - 1) = m - u := by field_simp
    linarith
  · subst hu; simp at h; linarith

lemma primal_le_dual (hν : ∀ r, 0 < ν r) {y : Fin J → ℝ} (hy : ∀ j, 0 ≤ y j)
    {x : Fin R → ℝ} (hx : x ∈ primalFeasible A C) :
    primalObjective ν x ≤ dualObjective A ν C y := by
  obtain ⟨hx0, hxC⟩ := hx
  have h1 : 0 ≤ ∑ j, y j * ((C j : ℝ) - ∑ r, (A j r : ℝ) * x r) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hy j) (by linarith [hxC j]))
  have h2 : primalObjective ν x + ∑ j, y j * ((C j : ℝ) - ∑ r, (A j r : ℝ) * x r) =
      ∑ r, (x r * Real.log (ν r) - x r * Real.log (x r) + x r - x r * ar A y r) +
        ∑ j, y j * (C j : ℝ) := by
    unfold primalObjective ar
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun j r => y j * ((A j r : ℝ) * x r))]
    have : ∀ r, ∑ j, x r * (y j * (A j r : ℝ)) = ∑ j, y j * ((A j r : ℝ) * x r) :=
      fun r => Finset.sum_congr rfl (fun j _ => by ring)
    simp only [this]; ring
  have h3 : ∑ r, (x r * Real.log (ν r) - x r * Real.log (x r) + x r - x r * ar A y r) ≤
      ∑ r, ν r * Real.exp (-ar A y r) :=
    Finset.sum_le_sum (fun r _ => psi_le (hν r) (hx0 r))
  unfold dualObjective
  have : ∑ r, ν r * Real.exp (-∑ j, y j * (A j r : ℝ)) = ∑ r, ν r * Real.exp (-ar A y r) := rfl
  linarith

lemma kkt_feasible {y : Fin J → ℝ} (hν : ∀ r, 0 < ν r) (hy : KKT A ν C y) :
    primalPoint A ν y ∈ primalFeasible A C :=
  ⟨fun r => (pp_pos A ν hν y r).le, hy.2.1⟩

lemma kkt_value {y : Fin J → ℝ} (hν : ∀ r, 0 < ν r) (hy : KKT A ν C y) :
    primalObjective ν (primalPoint A ν y) = dualObjective A ν C y := by
  have hcs : ∀ j, y j * ((C j : ℝ) - ∑ r, (A j r : ℝ) * primalPoint A ν y r) = 0 := by
    intro j
    rcases (hy.1 j).lt_or_eq with h | h
    · rw [hy.2.2 j h]; ring
    · rw [← h]; ring
  have hlog : ∀ r, Real.log (primalPoint A ν y r) = Real.log (ν r) - ar A y r := by
    intro r; rw [pp_eq, Real.log_mul (hν r).ne' (Real.exp_pos _).ne', Real.log_exp]; ring
  have h2 : ∑ j, y j * (C j : ℝ) = ∑ r, primalPoint A ν y r * ar A y r := by
    have : ∑ j, y j * (C j : ℝ) = ∑ j, y j * ∑ r, (A j r : ℝ) * primalPoint A ν y r :=
      Finset.sum_congr rfl (fun j _ => by linarith [hcs j])
    rw [this]; unfold ar
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun j _ => by ring))
  unfold primalObjective dualObjective
  simp only [hlog]
  rw [h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [pp_eq]; unfold ar; ring

lemma kkt_isMax {y : Fin J → ℝ} (hν : ∀ r, 0 < ν r) (hy : KKT A ν C y) :
    IsMaxOn (primalObjective ν) (primalFeasible A C) (primalPoint A ν y) := by
  intro x hx
  rw [Set.mem_setOf_eq, kkt_value A ν C hν hy]
  exact primal_le_dual A ν C hν hy.1 hx

lemma kkt_unique {y : Fin J → ℝ} (hν : ∀ r, 0 < ν r) (hy : KKT A ν C y)
    {x : Fin R → ℝ} (hx : x ∈ primalFeasible A C)
    (hge : dualObjective A ν C y ≤ primalObjective ν x) : x = primalPoint A ν y := by
  obtain ⟨hx0, hxC⟩ := hx
  have h1 : 0 ≤ ∑ j, y j * ((C j : ℝ) - ∑ r, (A j r : ℝ) * x r) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hy.1 j) (by linarith [hxC j]))
  have h2 : primalObjective ν x + ∑ j, y j * ((C j : ℝ) - ∑ r, (A j r : ℝ) * x r) =
      ∑ r, (x r * Real.log (ν r) - x r * Real.log (x r) + x r - x r * ar A y r) +
        ∑ j, y j * (C j : ℝ) := by
    unfold primalObjective ar
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun j r => y j * ((A j r : ℝ) * x r))]
    have : ∀ r, ∑ j, x r * (y j * (A j r : ℝ)) = ∑ j, y j * ((A j r : ℝ) * x r) :=
      fun r => Finset.sum_congr rfl (fun j _ => by ring)
    simp only [this]; ring
  have hD : dualObjective A ν C y = ∑ r, ν r * Real.exp (-ar A y r) + ∑ j, y j * (C j : ℝ) := rfl
  set f := fun r => x r * Real.log (ν r) - x r * Real.log (x r) + x r - x r * ar A y r
  set g := fun r => ν r * Real.exp (-ar A y r)
  have hfg : ∀ r ∈ Finset.univ, f r ≤ g r := fun r _ => psi_le (hν r) (hx0 r)
  have hsum : ∑ r, g r ≤ ∑ r, f r := by linarith
  have heq : ∀ r ∈ Finset.univ, f r = g r := by
    by_contra hne
    push_neg at hne
    obtain ⟨r, hr, hne⟩ := hne
    have hlt : ∑ r, f r < ∑ r, g r :=
      Finset.sum_lt_sum hfg ⟨r, hr, lt_of_le_of_ne (hfg r hr) hne⟩
    linarith
  funext r
  exact psi_eq (hν r) (hx0 r) (le_of_eq (heq r (Finset.mem_univ r)).symm)

end X5KL


namespace X5KL
open KellyLossNetworks.Primal KellyStochasticNetworks Filter Topology

variable {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ) (C : Fin J → ℕ)

lemma dual_eq (y : Fin J → ℝ) :
    dualObjective A ν C y = ∑ r, ν r * Real.exp (-ar A y r) + ∑ j, y j * (C j : ℝ) := rfl

/-- KKT points minimize the dual over the nonnegative orthant. -/
lemma kkt_dualOpt {y : Fin J → ℝ} (hν : ∀ r, 0 < ν r) (hy : KKT A ν C y) :
    IsDualOpt A ν C y := by
  refine ⟨hy.1, fun z hz => ?_⟩
  set x := primalPoint A ν y
  have hexp : ∀ r, ν r * Real.exp (-ar A y r) * (ar A y r - ar A z r + 1) ≤
      ν r * Real.exp (-ar A z r) := by
    intro r
    have h := Real.add_one_le_exp (ar A y r - ar A z r)
    have : Real.exp (-ar A z r) = Real.exp (-ar A y r) * Real.exp (ar A y r - ar A z r) := by
      rw [← Real.exp_add]; ring_nf
    rw [this, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left h (mul_pos (hν r) (Real.exp_pos _)).le
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun r _ => hexp r)
  have hlin : ∑ r, ν r * Real.exp (-ar A y r) * (ar A y r - ar A z r + 1) =
      ∑ r, ν r * Real.exp (-ar A y r) +
        ∑ j, (y j - z j) * ∑ r, (A j r : ℝ) * x r := by
    simp only [x, pp_eq, mul_add, mul_one, Finset.sum_add_distrib, ar, mul_sub,
      Finset.sum_sub_distrib, Finset.mul_sum, sub_mul, Finset.sum_mul]
    rw [Finset.sum_comm (f := fun j r => y j * ((A j r : ℝ) * (ν r * Real.exp (-∑ j, y j * (A j r : ℝ)))))]
    rw [Finset.sum_comm (f := fun j r => z j * ((A j r : ℝ) * (ν r * Real.exp (-∑ j, y j * (A j r : ℝ)))))]
    have e1 : ∀ r j, ν r * Real.exp (-∑ j, y j * (A j r : ℝ)) * (y j * (A j r : ℝ)) =
        y j * ((A j r : ℝ) * (ν r * Real.exp (-∑ j, y j * (A j r : ℝ)))) := fun r j => by ring
    have e2 : ∀ r j, ν r * Real.exp (-∑ j, y j * (A j r : ℝ)) * (z j * (A j r : ℝ)) =
        z j * ((A j r : ℝ) * (ν r * Real.exp (-∑ j, y j * (A j r : ℝ)))) := fun r j => by ring
    simp only [e1, e2]; ring
  have hcs : ∀ j, 0 ≤ (z j - y j) * ((C j : ℝ) - ∑ r, (A j r : ℝ) * x r) := by
    intro j
    rcases (hy.1 j).lt_or_eq with h | h
    · rw [hy.2.2 j h]; simp
    · rw [← h, sub_zero]; exact mul_nonneg (hz j) (by linarith [hy.2.1 j])
  have hcs' := Finset.sum_nonneg (s := Finset.univ) (fun j _ => hcs j)
  rw [dual_eq, dual_eq]
  have : ∑ j, (z j - y j) * ((C j : ℝ) - ∑ r, (A j r : ℝ) * x r) =
      ∑ j, z j * (C j : ℝ) - ∑ j, y j * (C j : ℝ) + ∑ j, (y j - z j) * ∑ r, (A j r : ℝ) * x r := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  linarith

/-- The one-dimensional dual section in direction `e_j`. -/
lemma dual_dir (y : Fin J → ℝ) (j : Fin J) (t : ℝ) :
    dualObjective A ν C (y + t • Pi.single j 1) =
      (∑ r, ν r * Real.exp (-ar A y r) * Real.exp (-(t * (A j r : ℝ))) + t * (C j : ℝ)) +
        ∑ i, y i * (C i : ℝ) := by
  have har : ∀ r, ar A (y + t • Pi.single j 1) r = ar A y r + t * (A j r : ℝ) := by
    intro r; unfold ar
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  rw [dual_eq]
  simp only [har, neg_add, Real.exp_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, mul_assoc]
  have hs : ∑ x, t * ((Pi.single j (1:ℝ) : Fin J → ℝ) x * (C x : ℝ)) = t * (C j : ℝ) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  rw [hs]; ring

lemma dual_dir_deriv (y : Fin J → ℝ) (j : Fin J) :
    HasDerivAt (fun t => ∑ r, ν r * Real.exp (-ar A y r) * Real.exp (-(t * (A j r : ℝ))) +
      t * (C j : ℝ)) ((C j : ℝ) - ∑ r, (A j r : ℝ) * primalPoint A ν y r) 0 := by
  have h : ∀ r, HasDerivAt (fun t => ν r * Real.exp (-ar A y r) * Real.exp (-(t * (A j r : ℝ))))
      (ν r * Real.exp (-ar A y r) * (Real.exp (-((0:ℝ) * (A j r : ℝ))) * (-(A j r : ℝ)))) 0 := by
    intro r
    apply HasDerivAt.const_mul
    have := ((hasDerivAt_id (0:ℝ)).mul_const (A j r : ℝ)).neg.exp
    simpa using this
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun r _ => h r)
  have hc := hasDerivAt_mul_const (x := (0:ℝ)) (C j : ℝ)
  refine (hs.add hc).congr_deriv ?_
  rw [sub_eq_add_neg, add_comm (C j : ℝ), ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun r _ => by simp only [pp_eq, ar, zero_mul, neg_zero, Real.exp_zero]; ring)

/-- Dual optimality implies the KKT conditions. -/
lemma dualOpt_kkt {y : Fin J → ℝ} (hy : IsDualOpt A ν C y) : KKT A ν C y := by
  obtain ⟨hy0, hmin⟩ := hy
  have key : ∀ j, ∀ t, 0 ≤ y j + t →
      (∑ r, ν r * Real.exp (-ar A y r) * Real.exp (-((0:ℝ) * (A j r : ℝ))) + 0 * (C j : ℝ)) ≤
      ∑ r, ν r * Real.exp (-ar A y r) * Real.exp (-(t * (A j r : ℝ))) + t * (C j : ℝ) := by
    intro j t ht
    have hz : ∀ i, 0 ≤ ((y + t • Pi.single j (1:ℝ)) : Fin J → ℝ) i := by
      intro i
      by_cases hi : i = j
      · subst hi; simp; linarith
      · simp [Pi.single_apply, hi, hy0 i]
    have h1 := hmin _ hz
    have h0 := dual_dir A ν C y j 0
    simp only [zero_smul, add_zero] at h0
    rw [dual_dir, h0] at h1
    linarith
  have hge : ∀ j, 0 ≤ (C j : ℝ) - ∑ r, (A j r : ℝ) * primalPoint A ν y r := by
    intro j
    have hd := (dual_dir_deriv A ν C y j).tendsto_slope_zero_right
    apply ge_of_tendsto hd
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have := key j t (by linarith [hy0 j])
    simp only [zero_add, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 ht.le) (by linarith)
  refine ⟨hy0, fun j => by linarith [hge j], fun j hj => ?_⟩
  have hd := (dual_dir_deriv A ν C y j).tendsto_slope_zero_left
  have hle : (C j : ℝ) - ∑ r, (A j r : ℝ) * primalPoint A ν y r ≤ 0 := by
    apply le_of_tendsto hd
    have : Set.Ioo (-y j) 0 ∈ 𝓝[<] (0:ℝ) := Ioo_mem_nhdsLT (by linarith)
    filter_upwards [this] with t ht
    have := key j t (by linarith [ht.1])
    simp only [zero_add, smul_eq_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.2 ht.2.le) (by linarith)
  linarith [hge j]

/-- Existence of a dual optimum (coercivity on the orthant). -/
lemma exists_dualOpt (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j) : ∃ y, IsDualOpt A ν C y := by
  set M := dualObjective A ν C 0
  set K : Set (Fin J → ℝ) := Set.pi Set.univ (fun _ => Set.Icc 0 (max M 0))
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hKne : K.Nonempty := ⟨0, fun j _ => ⟨le_rfl, le_max_right _ _⟩⟩
  have hcont : Continuous (dualObjective A ν C) := by
    unfold dualObjective; fun_prop
  obtain ⟨y, hyK, hymin⟩ := hK.exists_isMinOn hKne hcont.continuousOn
  have hy0 : ∀ j, 0 ≤ y j := fun j => (hyK j (Set.mem_univ j)).1
  refine ⟨y, hy0, fun z hz => ?_⟩
  by_cases hzK : z ∈ K
  · exact hymin hzK
  · -- some coordinate exceeds `M`, so the dual value exceeds `M`
    have hyM : dualObjective A ν C y ≤ M :=
      hymin (show (0 : Fin J → ℝ) ∈ K from fun j _ => ⟨le_rfl, le_max_right _ _⟩)
    simp only [K, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, not_forall] at hzK
    obtain ⟨j, hj⟩ := hzK
    have hzj : max M 0 < z j := by
      by_contra h; push_neg at h; exact hj ⟨hz j, h⟩
    have h1 : z j * (C j : ℝ) ≤ ∑ i, z i * (C i : ℝ) :=
      Finset.single_le_sum (f := fun i => z i * (C i : ℝ))
        (fun i _ => mul_nonneg (hz i) (Nat.cast_nonneg _)) (Finset.mem_univ j)
    have h2 : z j ≤ z j * (C j : ℝ) := by
      have : (1:ℝ) ≤ C j := by exact_mod_cast hC j
      nlinarith [hz j]
    have h3 : 0 ≤ ∑ r, ν r * Real.exp (-ar A z r) :=
      Finset.sum_nonneg (fun r _ => (mul_pos (hν r) (Real.exp_pos _)).le)
    have := le_max_left M 0
    have := dual_eq A ν C z
    linarith

end X5KL


namespace X5KL
open KellyLossNetworks.Primal KellyStochasticNetworks

variable {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ) (C : Fin J → ℕ)

lemma prod_eq (y : Fin J → ℝ) (r : Fin R) :
    ∏ i, (1 - blockingFromDual y i) ^ (A i r) = Real.exp (-ar A y r) := by
  unfold blockingFromDual ar
  simp only [sub_sub_cancel, ← Real.exp_nat_mul, ← Real.exp_sum]
  congr 1
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma flow_eq (y : Fin J → ℝ) (j : Fin J) :
    (∑ r, (A j r : ℝ) * ν r * ∏ i, (1 - blockingFromDual y i) ^ (A i r)) =
      ∑ r, (A j r : ℝ) * primalPoint A ν y r := by
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [prod_eq, pp_eq]; ring

lemma kkt_condB {y : Fin J → ℝ} (hy : KKT A ν C y) : ConditionsOnB A ν C (blockingFromDual y) := by
  refine ⟨fun j => ⟨?_, ?_⟩, fun j => ⟨fun hB => ?_, fun _ => ?_⟩⟩
  · unfold blockingFromDual
    have : Real.exp (-y j) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [hy.1 j])
    linarith
  · unfold blockingFromDual; linarith [Real.exp_pos (-y j)]
  · rw [flow_eq]
    apply hy.2.2 j
    rcases (hy.1 j).lt_or_eq with h | h
    · exact h
    · exfalso; unfold blockingFromDual at hB; rw [← h] at hB; simp at hB
  · rw [flow_eq]; exact hy.2.1 j

lemma condB_inv {B : Fin J → ℝ} (hB : ConditionsOnB A ν C B) :
    blockingFromDual (dualFromBlocking B) = B := by
  funext j
  have h1 : 0 < 1 - B j := by linarith [(hB.1 j).2]
  unfold blockingFromDual dualFromBlocking
  rw [neg_neg, Real.exp_log h1]; ring

lemma condB_kkt {B : Fin J → ℝ} (hB : ConditionsOnB A ν C B) : KKT A ν C (dualFromBlocking B) := by
  have hinv := condB_inv A ν C hB
  have hfl : ∀ j, (∑ r, (A j r : ℝ) * ν r * ∏ i, (1 - B i) ^ (A i r)) =
      ∑ r, (A j r : ℝ) * primalPoint A ν (dualFromBlocking B) r := by
    intro j; rw [← flow_eq, hinv]
  refine ⟨fun j => ?_, fun j => ?_, fun j hj => ?_⟩
  · unfold dualFromBlocking
    have h1 : 0 < 1 - B j := by linarith [(hB.1 j).2]
    have h2 : 1 - B j ≤ 1 := by linarith [(hB.1 j).1]
    linarith [Real.log_nonpos h1.le h2]
  · rw [← hfl]
    rcases (hB.1 j).1.lt_or_eq with h | h
    · exact le_of_eq ((hB.2 j).1 h)
    · exact (hB.2 j).2 h.symm
  · rw [← hfl]
    apply (hB.2 j).1
    rcases (hB.1 j).1.lt_or_eq with h | h
    · exact h
    · exfalso; unfold dualFromBlocking at hj; rw [← h] at hj; simp at hj

lemma dual_inv (y : Fin J → ℝ) : dualFromBlocking (blockingFromDual y) = y := by
  funext j; unfold dualFromBlocking blockingFromDual
  rw [sub_sub_cancel, Real.log_exp, neg_neg]

lemma ar_inj (hrank : (Matrix.of fun j r => (A j r : ℝ)).rank = J) {y z : Fin J → ℝ}
    (h : ∀ r, ar A y r = ar A z r) : y = z := by
  set M : Matrix (Fin J) (Fin R) ℝ := Matrix.of fun j r => (A j r : ℝ)
  have hT : M.transpose.rank = J := by rw [Matrix.rank_transpose]; exact hrank
  have hker : LinearMap.ker M.transpose.mulVecLin = ⊥ := by
    have h1 := LinearMap.finrank_range_add_finrank_ker M.transpose.mulVecLin
    rw [← Matrix.rank, hT, Module.finrank_fin_fun] at h1
    exact Submodule.finrank_eq_zero.1 (by omega)
  have hmem : y - z ∈ LinearMap.ker M.transpose.mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext r
    have := h r
    unfold ar at this
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, M, Matrix.of_apply, Pi.sub_apply,
      Pi.zero_apply, mul_sub, Finset.sum_sub_distrib]
    have e1 : ∑ x, (A x r : ℝ) * y x = ∑ j, y j * (A j r : ℝ) :=
      Finset.sum_congr rfl (fun j _ => by ring)
    have e2 : ∑ x, (A x r : ℝ) * z x = ∑ j, z j * (A j r : ℝ) :=
      Finset.sum_congr rfl (fun j _ => by ring)
    rw [e1, e2, this, sub_self]
  rw [hker, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hmem

theorem main (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j) :
    (∃! x : Fin R → ℝ,
      x ∈ primalFeasible A C ∧
      IsMaxOn (primalObjective ν) (primalFeasible A C) x) ∧
    (∀ B : Fin J → ℝ, ConditionsOnB A ν C B →
      ∀ x : Fin R → ℝ,
        (x ∈ primalFeasible A C ∧
          IsMaxOn (primalObjective ν) (primalFeasible A C) x) →
        ∀ r, x r = ν r * ∏ j, (1 - B j) ^ (A j r)) ∧
    (∃ B : Fin J → ℝ, ConditionsOnB A ν C B) ∧
    ((Matrix.of fun j r => (A j r : ℝ)).rank = J →
      ∃! B : Fin J → ℝ, ConditionsOnB A ν C B) ∧
    (∀ B : Fin J → ℝ, ConditionsOnB A ν C B →
      IsDualOpt A ν C (dualFromBlocking B)) ∧
    (∀ y : Fin J → ℝ, IsDualOpt A ν C y →
      ConditionsOnB A ν C (blockingFromDual y)) ∧
    (∀ B : Fin J → ℝ, ConditionsOnB A ν C B →
      blockingFromDual (dualFromBlocking B) = B) ∧
    (∀ y : Fin J → ℝ, IsDualOpt A ν C y →
      dualFromBlocking (blockingFromDual y) = y) := by
  obtain ⟨y0, hy0⟩ := exists_dualOpt A ν C hν hC
  have hk0 := dualOpt_kkt A ν C hy0
  -- any maximizer equals the KKT point of any KKT `y`
  have maxEq : ∀ y, KKT A ν C y → ∀ x, (x ∈ primalFeasible A C ∧
      IsMaxOn (primalObjective ν) (primalFeasible A C) x) → x = primalPoint A ν y := by
    intro y hy x ⟨hxF, hxM⟩
    apply kkt_unique A ν C hν hy hxF
    rw [← kkt_value A ν C hν hy]
    exact hxM (kkt_feasible A ν C hν hy)
  refine ⟨⟨primalPoint A ν y0, ⟨kkt_feasible A ν C hν hk0, kkt_isMax A ν C hν hk0⟩,
      fun x hx => maxEq y0 hk0 x hx⟩, ?_, ⟨_, kkt_condB A ν C hk0⟩, ?_,
    fun B hB => kkt_dualOpt A ν C hν (condB_kkt A ν C hB),
    fun y hy => kkt_condB A ν C (dualOpt_kkt A ν C hy),
    fun B hB => condB_inv A ν C hB, fun y _ => dual_inv y⟩
  · intro B hB x hx r
    have hk := condB_kkt A ν C hB
    rw [maxEq _ hk x hx, pp_eq, ← prod_eq, condB_inv A ν C hB]
  · intro hrank
    refine ⟨_, kkt_condB A ν C hk0, fun B hB => ?_⟩
    have hk := condB_kkt A ν C hB
    have hx := maxEq _ hk (primalPoint A ν y0)
      ⟨kkt_feasible A ν C hν hk0, kkt_isMax A ν C hν hk0⟩
    have har : ∀ r, ar A (dualFromBlocking B) r = ar A y0 r := by
      intro r
      have := congrFun hx r
      rw [pp_eq, pp_eq] at this
      have h2 := mul_left_cancel₀ (hν r).ne' this
      have := Real.exp_injective h2
      linarith
    have := ar_inj A hrank har
    rw [← condB_inv A ν C hB, this]

end X5KL


open KellyLossNetworks.Primal in
theorem solution {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r)
    (hC : ∀ j, 1 ≤ C j) :
    (∃! x : Fin R → ℝ,
      x ∈ primalFeasible A C ∧
      IsMaxOn (primalObjective ν) (primalFeasible A C) x) ∧
    (∀ B : Fin J → ℝ, ConditionsOnB A ν C B →
      ∀ x : Fin R → ℝ,
        (x ∈ primalFeasible A C ∧
          IsMaxOn (primalObjective ν) (primalFeasible A C) x) →
        ∀ r, x r = ν r * ∏ j, (1 - B j) ^ (A j r)) ∧
    (∃ B : Fin J → ℝ, ConditionsOnB A ν C B) ∧
    ((Matrix.of fun j r => (A j r : ℝ)).rank = J →
      ∃! B : Fin J → ℝ, ConditionsOnB A ν C B) ∧
    (∀ B : Fin J → ℝ, ConditionsOnB A ν C B →
      IsDualOpt A ν C (dualFromBlocking B)) ∧
    (∀ y : Fin J → ℝ, IsDualOpt A ν C y →
      ConditionsOnB A ν C (blockingFromDual y)) ∧
    (∀ B : Fin J → ℝ, ConditionsOnB A ν C B →
      blockingFromDual (dualFromBlocking B) = B) ∧
    (∀ y : Fin J → ℝ, IsDualOpt A ν C y →
      dualFromBlocking (blockingFromDual y) = y) :=
  X5KL.main A ν C hν hC
