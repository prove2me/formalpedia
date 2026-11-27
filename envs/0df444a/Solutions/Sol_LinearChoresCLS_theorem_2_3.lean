-- Prove2me | solution 1 for LinearChoresCLS.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T00:24:56.349434+00:00
-- url     : https://prove2.me/submissions/32bd99ab-8898-4683-b828-81f772f9f5fc

import Mathlib
import Definitions.Def_LinearChoresCLS_Psi
import Definitions.Def_LinearChoresCLS_RightDeriv

set_option autoImplicit false
open Finset Filter Topology

namespace LinearChoresCLS.T23

variable {M : Type*} [Fintype M] [Nonempty M]

/-- For a finite family of affine functions `r_j + h s_j`, the maximum equals
`max r + h · max_{j ∈ argmax r} s_j` for all small `h > 0`. -/
theorem sup_affine_eventually (r s : M → ℝ) :
    ∃ (J : Finset M) (hJ : J.Nonempty), (∀ j, j ∈ J ↔ r j = univ.sup' univ_nonempty r) ∧
      ∀ᶠ h in 𝓝[>] (0 : ℝ), univ.sup' univ_nonempty (fun j => r j + h * s j) =
        univ.sup' univ_nonempty r + h * J.sup' hJ s := by
  classical
  set μ := univ.sup' univ_nonempty r with hμ
  let J : Finset M := univ.filter (fun j => r j = μ)
  obtain ⟨j0, -, hj0⟩ := Finset.exists_mem_eq_sup' (univ_nonempty (α := M)) r
  have hJ : J.Nonempty := ⟨j0, by simp [J, hj0, hμ]⟩
  refine ⟨J, hJ, fun j => by simp [J], ?_⟩
  set τ := J.sup' hJ s with hτ
  obtain ⟨j1, hj1J, hj1⟩ := Finset.exists_mem_eq_sup' hJ s
  have hj1r : r j1 = μ := by simpa [J] using hj1J
  -- every index is eventually dominated
  have hdom : ∀ j, ∀ᶠ h in 𝓝[>] (0 : ℝ), r j + h * s j ≤ μ + h * τ := by
    intro j
    by_cases hj : j ∈ J
    · have hrj : r j = μ := by simpa [J] using hj
      have hs : s j ≤ τ := Finset.le_sup' s hj
      filter_upwards [self_mem_nhdsWithin] with h hh
      rw [hrj]; nlinarith [hh.out]
    · have hrj : r j < μ := lt_of_le_of_ne (Finset.le_sup' r (mem_univ j)) (by simpa [J] using hj)
      have hc : Tendsto (fun h : ℝ => μ + h * τ - (r j + h * s j)) (𝓝[>] 0) (𝓝 (μ - r j)) := by
        have : Continuous (fun h : ℝ => μ + h * τ - (r j + h * s j)) := by continuity
        have h2 := this.tendsto 0
        simp only [zero_mul, add_zero] at h2
        exact h2.mono_left nhdsWithin_le_nhds
      filter_upwards [hc.eventually (lt_mem_nhds (sub_pos.2 hrj))] with h hh
      linarith
  filter_upwards [(Filter.eventually_all.2 hdom), self_mem_nhdsWithin] with h hh hpos
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun j _ => hh j)
  · have := Finset.le_sup' (fun j => r j + h * s j) (mem_univ j1)
    rw [hj1r, ← hj1] at this
    exact this

end LinearChoresCLS.T23

namespace LinearChoresCLS.T23
open Finset Filter Topology

variable {N M : Type*} [Fintype N] [Fintype M] [Nonempty M]

noncomputable def Jset (F : ChoresMarket N M) (p : M → ℝ) (a : N) : Finset M := by
  classical exact univ.filter (fun j => p j / F.disutil a j = F.mu a p)

theorem Jset_nonempty (F : ChoresMarket N M) (p : M → ℝ) (a : N) : (Jset F p a).Nonempty := by
  classical
  obtain ⟨j0, -, hj0⟩ := Finset.exists_mem_eq_sup' (univ_nonempty (α := M))
    (fun j => p j / F.disutil a j)
  exact ⟨j0, by simp [Jset, ChoresMarket.mu, hj0]⟩

theorem mem_Jset (F : ChoresMarket N M) (p : M → ℝ) (a : N) (j : M) :
    j ∈ Jset F p a ↔ p j / F.disutil a j = F.mu a p := by
  classical simp [Jset]

noncomputable def tau (F : ChoresMarket N M) (p v : M → ℝ) (a : N) : ℝ :=
  (Jset F p a).sup' (Jset_nonempty F p a) (fun j => v j / F.disutil a j)

noncomputable def Dval (F : ChoresMarket N M) (p v : M → ℝ) : ℝ :=
  -∑ a, F.earn a * (tau F p v a / F.mu a p)

theorem mu_eventually (F : ChoresMarket N M) (p v : M → ℝ) (a : N) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), F.mu a (p + h • v) = F.mu a p + h * tau F p v a := by
  obtain ⟨J, hJ, hmem, hev⟩ := sup_affine_eventually (fun j => p j / F.disutil a j)
    (fun j => v j / F.disutil a j)
  have hJeq : J = Jset F p a := by
    ext j; rw [hmem, mem_Jset]; rfl
  subst hJeq
  filter_upwards [hev] with h hh
  unfold ChoresMarket.mu tau
  rw [← hh]
  congr 1; funext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem mu_pos (F : ChoresMarket N M) (hF : F.Valid) (p : M → ℝ) (hp : ∀ j, 0 < p j) (a : N) :
    0 < F.mu a p := by
  obtain ⟨j0⟩ := (inferInstance : Nonempty M)
  unfold ChoresMarket.mu
  exact lt_of_lt_of_le (div_pos (hp j0) (hF.1 a j0))
    (Finset.le_sup' (fun j => p j / F.disutil a j) (mem_univ j0))

theorem psi_rightDeriv (F : ChoresMarket N M) (hF : F.Valid) (p : M → ℝ) (hp : ∀ j, 0 < p j)
    (v : M → ℝ) : HasRightDerivAt0 (fun h => F.Psi (p + h • v)) (Dval F p v) := by
  set φ : ℝ → ℝ := fun h => -∑ a, F.earn a * Real.log (F.mu a p + h * tau F p v a) with hφ
  have hderiv : HasDerivAt φ (Dval F p v) 0 := by
    have : ∀ a, HasDerivAt (fun h : ℝ => F.earn a * Real.log (F.mu a p + h * tau F p v a))
        (F.earn a * (tau F p v a / F.mu a p)) 0 := by
      intro a
      have h1 : HasDerivAt (fun h : ℝ => F.mu a p + h * tau F p v a) (tau F p v a) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (tau F p v a)).const_add (F.mu a p)
      have h2 := (h1.log (by simpa using (mu_pos F hF p hp a).ne')).const_mul (F.earn a)
      simpa using h2
    have hs := HasDerivAt.fun_sum (u := univ) (fun a _ => this a)
    have := hs.fun_neg
    simpa [hφ, Dval] using this
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hderiv).mono_left
    (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))
  unfold HasRightDerivAt0
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), F.Psi (p + h • v) = φ h := by
    filter_upwards [Filter.eventually_all.2 (fun a => mu_eventually F p v a)] with h hh
    simp only [ChoresMarket.Psi, hφ, hh]
  have h0 : F.Psi (p + (0 : ℝ) • v) = φ 0 := by simp [ChoresMarket.Psi, hφ]
  refine hslope.congr' ?_
  filter_upwards [hev] with h hh
  simp only [slope_def_field, smul_eq_mul, hh, h0]
  ring

end LinearChoresCLS.T23

namespace LinearChoresCLS.T23
open Finset Filter Topology
variable {N M : Type*} [Fintype N] [Fintype M]

/-- The demand-set criterion for linear chores at nonnegative prices. -/
theorem mem_demandSet_iff (F : ChoresMarket N M) (hF : F.Valid) (p : M → ℝ) (hp : ∀ j, 0 ≤ p j)
    (a : N) (y : M → ℝ) :
    y ∈ F.demandSet p a ↔ (∀ j, 0 ≤ y j) ∧ F.earn a ≤ ∑ j, p j * y j ∧
      ∀ j, 0 < p j → p j * ∑ l, F.disutil a l * y l ≤ F.earn a * F.disutil a j := by
  obtain ⟨hd, hB, _⟩ := hF
  constructor
  · rintro ⟨hy, hfeas, hopt⟩
    refine ⟨hy, hfeas, fun j hj => ?_⟩
    classical
    let y' : M → ℝ := fun l => if l = j then F.earn a / p j else 0
    have hy' : ∀ l, 0 ≤ y' l := by
      intro l; simp only [y']; split_ifs
      · exact div_nonneg (hB a).le hj.le
      · exact le_rfl
    have hpy' : ∑ l, p l * y' l = F.earn a := by
      simp only [y', mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      field_simp
    have hdy' : ∑ l, F.disutil a l * y' l = F.disutil a j * (F.earn a / p j) := by
      simp only [y', mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have := hopt y' hy' hpy'.ge
    rw [hdy'] at this
    have := mul_le_mul_of_nonneg_left this hj.le
    calc p j * ∑ l, F.disutil a l * y l ≤ p j * (F.disutil a j * (F.earn a / p j)) := this
      _ = F.earn a * F.disutil a j := by field_simp
  · rintro ⟨hy, hfeas, hcond⟩
    refine ⟨hy, hfeas, fun y' hy' hfeas' => ?_⟩
    set D := ∑ l, F.disutil a l * y l with hD
    have hD0 : 0 ≤ D := Finset.sum_nonneg (fun l _ => mul_nonneg (hd a l).le (hy l))
    have hBpos := hB a
    -- termwise: D * p_j * y'_j ≤ B * d_j * y'_j
    have hterm : ∀ j, D * (p j * y' j) ≤ F.earn a * (F.disutil a j * y' j) := by
      intro j
      rcases (hp j).lt_or_eq with hj | hj
      · have := hcond j hj
        have := mul_le_mul_of_nonneg_right this (hy' j)
        nlinarith
      · rw [← hj]; simp only [zero_mul, mul_zero]
        exact mul_nonneg hBpos.le (mul_nonneg (hd a j).le (hy' j))
    have hsum : D * ∑ j, p j * y' j ≤ F.earn a * ∑ j, F.disutil a j * y' j := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_le_sum (fun j _ => hterm j)
    have h1 : D * F.earn a ≤ D * ∑ j, p j * y' j := mul_le_mul_of_nonneg_left hfeas' hD0
    have h2 : D * F.earn a ≤ F.earn a * ∑ j, F.disutil a j * y' j := h1.trans hsum
    rw [mul_comm] at h2
    exact le_of_mul_le_mul_left h2 hBpos


variable [Nonempty M]

theorem spend_eq (F : ChoresMarket N M) (hF : F.Valid) (p : M → ℝ) (hp : ∀ j, 0 < p j) (a : N)
    (y : M → ℝ) (hy : y ∈ F.demandSet p a) : ∑ j, p j * y j = F.earn a := by
  obtain ⟨hy0, hfeas, hopt⟩ := hy
  by_contra hne
  have hlt : F.earn a < ∑ j, p j * y j := lt_of_le_of_ne hfeas (Ne.symm hne)
  have hB := hF.2.1 a
  set Sp := ∑ j, p j * y j
  have hSp : 0 < Sp := lt_trans hB hlt
  set t := F.earn a / Sp
  have ht0 : 0 < t := div_pos hB hSp
  have ht1 : t < 1 := (div_lt_one hSp).2 hlt
  have hfeas' : F.earn a ≤ ∑ j, p j * (t * y j) := by
    have : ∑ j, p j * (t * y j) = t * Sp := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [this]; simp only [t]; field_simp; exact le_rfl
  have h := hopt (fun j => t * y j) (fun j => mul_nonneg ht0.le (hy0 j)) hfeas'
  have hD : 0 < ∑ j, F.disutil a j * y j := by
    by_contra hD
    push Not at hD
    have hz : ∀ j, F.disutil a j * y j = 0 := by
      have hnn : ∀ j ∈ univ, 0 ≤ F.disutil a j * y j := fun j _ => mul_nonneg (hF.1 a j).le (hy0 j)
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm hD (Finset.sum_nonneg hnn))
      exact fun j => this j (mem_univ j)
    have hy' : ∀ j, y j = 0 := fun j => by
      rcases mul_eq_zero.1 (hz j) with h | h
      · exact absurd h (hF.1 a j).ne'
      · exact h
    have : Sp = 0 := by simp [Sp, hy']
    linarith
  have : ∑ j, F.disutil a j * (t * y j) = t * ∑ j, F.disutil a j * y j := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => by ring)
  rw [this] at h
  nlinarith

theorem support_J (F : ChoresMarket N M) (hF : F.Valid) (p : M → ℝ) (hp : ∀ j, 0 < p j) (a : N)
    (y : M → ℝ) (hy : y ∈ F.demandSet p a) (j : M) (hj : 0 < y j) : j ∈ Jset F p a := by
  have hspend := spend_eq F hF p hp a y hy
  obtain ⟨hy0, _, hcrit⟩ := (mem_demandSet_iff F hF p (fun j => (hp j).le) a y).1 hy
  have hμ := mu_pos F hF p hp a
  obtain ⟨j0, hj0J⟩ := Jset_nonempty F p a
  have hj0 := (mem_Jset F p a j0).1 hj0J
  have hd := hF.1
  -- Σ d y ≤ B / μ
  have h1 : (∑ l, F.disutil a l * y l) * F.mu a p ≤ F.earn a := by
    have := hcrit j0 (hp j0)
    have e : F.disutil a j0 = p j0 / F.mu a p := by
      have := (hp j0).ne'; have := (hd a j0).ne'
      rw [← hj0]; field_simp
    rw [e] at this
    have hp0 := hp j0
    field_simp at this
    nlinarith [this]
  -- each term: p_l y_l ≤ μ d_l y_l
  have hterm : ∀ l, p l * y l ≤ F.mu a p * (F.disutil a l * y l) := by
    intro l
    have hr : p l / F.disutil a l ≤ F.mu a p :=
      Finset.le_sup' (fun j => p j / F.disutil a j) (mem_univ l)
    have := mul_le_mul_of_nonneg_right ((div_le_iff₀ (hd a l)).1 hr) (hy0 l)
    nlinarith [this]
  -- equality forces equality termwise
  have hsum : ∑ l, (F.mu a p * (F.disutil a l * y l) - p l * y l) = 0 := by
    have hle : ∑ l, (F.mu a p * (F.disutil a l * y l) - p l * y l) ≤ 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hspend]; nlinarith [h1]
    exact le_antisymm hle (Finset.sum_nonneg (fun l _ => sub_nonneg.2 (hterm l)))
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => sub_nonneg.2 (hterm l))).1 hsum j
    (mem_univ j)
  rw [mem_Jset]
  have : p j * y j = F.mu a p * (F.disutil a j * y j) := by linarith
  have hyj := hj.ne'
  have hdj := (hd a j).ne'
  field_simp
  have := mul_right_cancel₀ hyj (by linarith : p j * y j = (F.mu a p * F.disutil a j) * y j)
  linarith

theorem one_imp_two (F : ChoresMarket N M) (hF : F.Valid) (p : M → ℝ) (hp : ∀ j, 0 < p j)
    (z : N → M → ℝ) (hz : F.IsCE p z) (v : M → ℝ) (hv : ∑ j, F.supply j * v j = 0) :
    Dval F p v ≤ 0 := by
  obtain ⟨_, hz0, hdem, hclear⟩ := hz
  have hagent : ∀ a, ∑ j, z a j * v j ≤ F.earn a * (tau F p v a / F.mu a p) := by
    intro a
    have hμ := mu_pos F hF p hp a
    have hspend := spend_eq F hF p hp a (z a) (hdem a)
    have : ∀ j, z a j * v j ≤ z a j * p j * (tau F p v a / F.mu a p) := by
      intro j
      rcases (hz0 a j).lt_or_eq with hpos | hzero
      · have hJ := support_J F hF p hp a (z a) (hdem a) j hpos
        have hle : v j / F.disutil a j ≤ tau F p v a :=
          Finset.le_sup' (fun j => v j / F.disutil a j) hJ
        have hr := (mem_Jset F p a j).1 hJ
        have hd := hF.1 a j
        have e : F.disutil a j = p j / F.mu a p := by
          have := (hp j).ne'; have := hd.ne'
          rw [← hr]; field_simp
        rw [e, div_div_eq_mul_div] at hle
        have hpj := hp j
        have : v j ≤ p j * (tau F p v a / F.mu a p) := by
          rw [mul_div_assoc'] ; rw [le_div_iff₀ hμ]; rw [div_le_iff₀ hpj] at hle; linarith
        nlinarith
      · rw [← hzero]; simp
    calc ∑ j, z a j * v j ≤ ∑ j, z a j * p j * (tau F p v a / F.mu a p) :=
          Finset.sum_le_sum (fun j _ => this j)
      _ = (∑ j, p j * z a j) * (tau F p v a / F.mu a p) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun j _ => by ring)
      _ = F.earn a * (tau F p v a / F.mu a p) := by rw [hspend]
  have htot : ∑ a, ∑ j, z a j * v j = 0 := by
    rw [Finset.sum_comm]
    rw [← hv]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_mul, hclear j]
  unfold Dval
  have := Finset.sum_le_sum (fun a (_ : a ∈ univ) => hagent a)
  linarith

end LinearChoresCLS.T23

namespace LinearChoresCLS.T23
open Finset Filter Topology

variable {N M : Type*} [Fintype N] [Fintype M] [Nonempty M]

/-- The flow set: nonnegative payments on best chores, exhausting each budget. -/
def Xset (F : ChoresMarket N M) (p : M → ℝ) : Set (N → M → ℝ) :=
  {x | (∀ a j, 0 ≤ x a j) ∧ (∀ a j, j ∉ Jset F p a → x a j = 0) ∧ (∀ a, ∑ j, x a j = F.earn a)}

noncomputable def colL : (N → M → ℝ) →ₗ[ℝ] (M → ℝ) where
  toFun x := fun j => ∑ a, x a j
  map_add' x y := by funext j; simp [Finset.sum_add_distrib]
  map_smul' c x := by funext j; simp [Finset.mul_sum]

theorem Xset_convex (F : ChoresMarket N M) (p : M → ℝ) : Convex ℝ (Xset F p) := by
  intro x hx y hy s t hs ht hst
  obtain ⟨hx0, hxJ, hxB⟩ := hx
  obtain ⟨hy0, hyJ, hyB⟩ := hy
  refine ⟨fun a j => ?_, fun a j hj => ?_, fun a => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hs (hx0 a j)) (mul_nonneg ht (hy0 a j))
  · simp [hxJ a j hj, hyJ a j hj]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hxB a, hyB a]
    rw [← add_mul, hst, one_mul]

theorem Xset_compact (F : ChoresMarket N M) (p : M → ℝ) : IsCompact (Xset F p) := by
  have hbox : IsCompact (Set.univ.pi (fun a : N => Set.univ.pi (fun _ : M => Set.Icc (0 : ℝ) (F.earn a)))) :=
    isCompact_univ_pi (fun a => isCompact_univ_pi (fun _ => isCompact_Icc))
  refine hbox.of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {x : N → M → ℝ | ∀ a j, 0 ≤ x a j} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter (fun a => isClosed_iInter (fun j =>
        isClosed_le continuous_const ((continuous_apply j).comp (continuous_apply a))))
    have h2 : IsClosed {x : N → M → ℝ | ∀ a j, j ∉ Jset F p a → x a j = 0} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter (fun a => isClosed_iInter (fun j => isClosed_iInter (fun _ =>
        isClosed_eq ((continuous_apply j).comp (continuous_apply a)) continuous_const)))
    have h3 : IsClosed {x : N → M → ℝ | ∀ a, ∑ j, x a j = F.earn a} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter (fun a => isClosed_eq (continuous_finset_sum _ (fun j _ =>
        (continuous_apply j).comp (continuous_apply a))) continuous_const)
    have : Xset F p = {x : N → M → ℝ | ∀ a j, 0 ≤ x a j} ∩
        {x : N → M → ℝ | ∀ a j, j ∉ Jset F p a → x a j = 0} ∩
        {x : N → M → ℝ | ∀ a, ∑ j, x a j = F.earn a} := by
      ext x; simp [Xset, and_assoc]
    rw [this]; exact (h1.inter h2).inter h3
  · rintro x ⟨hx0, _, hxB⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro a j
    refine ⟨hx0 a j, ?_⟩
    rw [← hxB a]
    exact Finset.single_le_sum (fun l _ => hx0 a l) (mem_univ j)

theorem dual_repr [DecidableEq M] (f : StrongDual ℝ (M → ℝ)) (y : M → ℝ) :
    f y = ∑ j, y j * f (Pi.single j 1) := by
  conv_lhs => rw [show y = ∑ j, y j • (Pi.single j (1 : ℝ) : M → ℝ) by
    funext i; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  simp [map_smul]

end LinearChoresCLS.T23

namespace LinearChoresCLS.T23
open Finset Filter Topology

variable {N M : Type*} [Fintype N] [Fintype M] [Nonempty M]

theorem target_mem (F : ChoresMarket N M) (hF : F.Valid) (p : M → ℝ) (hp : ∀ j, 0 < p j)
    (hbal : ∑ j, F.supply j * p j = ∑ a, F.earn a)
    (hfoc : ∀ v : M → ℝ, ∑ j, F.supply j * v j = 0 → Dval F p v ≤ 0) :
    (fun j => F.supply j * p j) ∈ (colL : (N → M → ℝ) →ₗ[ℝ] (M → ℝ)) '' Xset F p := by
  classical
  by_contra hnot
  have hK : IsCompact ((colL : (N → M → ℝ) →ₗ[ℝ] (M → ℝ)) '' Xset F p) :=
    (Xset_compact F p).image (LinearMap.continuous_of_finiteDimensional _)
  have hKc : Convex ℝ ((colL : (N → M → ℝ) →ₗ[ℝ] (M → ℝ)) '' Xset F p) :=
    (Xset_convex F p).linear_image _
  obtain ⟨f, u, u', hfK, huu, hft⟩ := geometric_hahn_banach_compact_closed hKc hK
    (convex_singleton (fun j => F.supply j * p j)) isClosed_singleton
    (Set.disjoint_singleton_right.2 hnot)
  set w : M → ℝ := fun j => f (Pi.single j 1) with hw
  -- best chore for w in each J_a
  have hbest : ∀ a, ∃ j ∈ Jset F p a, w j = (Jset F p a).sup' (Jset_nonempty F p a) w :=
    fun a => by
      obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_sup' (Jset_nonempty F p a) w
      exact ⟨j, hj, he.symm⟩
  choose jstar hjJ hjmax using hbest
  set W : N → ℝ := fun a => (Jset F p a).sup' (Jset_nonempty F p a) w with hW
  -- the concentrated flow
  set xs : N → M → ℝ := fun a j => if j = jstar a then F.earn a else 0 with hxs
  have hxs_mem : xs ∈ Xset F p := by
    refine ⟨fun a j => ?_, fun a j hj => ?_, fun a => ?_⟩
    · simp only [hxs]; split_ifs
      · exact (hF.2.1 a).le
      · exact le_rfl
    · simp only [hxs]; split_ifs with h
      · exact absurd (h ▸ hjJ a) hj
      · rfl
    · simp [hxs]
  have h1 : f (colL xs) < u := hfK _ ⟨xs, hxs_mem, rfl⟩
  have h2 : u' < f (fun j => F.supply j * p j) := hft _ rfl
  have hval1 : f (colL xs) = ∑ a, F.earn a * W a := by
    rw [dual_repr]
    simp only [colL, LinearMap.coe_mk, AddHom.coe_mk, hxs]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have := hjmax a
    simp only [hw] at this
    rw [this]
  have hval2 : f (fun j => F.supply j * p j) = ∑ j, F.supply j * p j * w j := by
    rw [dual_repr]
  -- the bad direction
  have hSpos : 0 < ∑ j, F.supply j * p j := by
    obtain ⟨j0⟩ := (inferInstance : Nonempty M)
    exact lt_of_lt_of_le (mul_pos (hF.2.2 j0) (hp j0))
      (Finset.single_le_sum (fun j _ => (mul_pos (hF.2.2 j) (hp j)).le) (mem_univ j0))
  set c := (∑ j, F.supply j * p j * w j) / ∑ j, F.supply j * p j with hc
  set v : M → ℝ := fun j => p j * (w j - c) with hv
  have hvbal : ∑ j, F.supply j * v j = 0 := by
    simp only [hv]
    have : ∑ j, F.supply j * (p j * (w j - c)) =
        ∑ j, F.supply j * p j * w j - c * ∑ j, F.supply j * p j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [this, hc, div_mul_cancel₀ _ hSpos.ne']; ring
  have hD := hfoc v hvbal
  -- lower bound on Dval
  have htau : ∀ a, tau F p v a / F.mu a p ≤ W a - c := by
    intro a
    have hμ := mu_pos F hF p hp a
    rw [div_le_iff₀ hμ]
    unfold tau
    refine Finset.sup'_le _ _ (fun j hj => ?_)
    have hr := (mem_Jset F p a j).1 hj
    have hd := hF.1 a j
    have hwj : w j ≤ W a := Finset.le_sup' w hj
    have e : v j / F.disutil a j = F.mu a p * (w j - c) := by
      simp only [hv]; rw [← hr]; field_simp
    rw [e]; nlinarith
  have hlow : -(∑ a, F.earn a * (W a - c)) ≤ Dval F p v := by
    unfold Dval
    have := Finset.sum_le_sum (fun a (_ : a ∈ univ) =>
      mul_le_mul_of_nonneg_left (htau a) (hF.2.1 a).le)
    linarith
  have hcalc : ∑ a, F.earn a * (W a - c) = ∑ a, F.earn a * W a - ∑ j, F.supply j * p j * w j := by
    have : ∑ a, F.earn a * (W a - c) = ∑ a, F.earn a * W a - c * ∑ a, F.earn a := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun a _ => by ring)
    rw [this, ← hbal, hc, div_mul_cancel₀ _ hSpos.ne']
  rw [hcalc] at hlow
  rw [hval1] at h1; rw [hval2] at h2
  linarith

end LinearChoresCLS.T23

namespace LinearChoresCLS.T23
open Finset Filter Topology

theorem thm23 {N M : Type*} [Fintype N] [Fintype M] [Nonempty M]
    (F : ChoresMarket N M) (hF : F.Valid) (pstar : M → ℝ) (hp : pstar ∈ F.priceDomain) :
    (∃ z : N → M → ℝ, F.IsCE pstar z) ↔
      ∀ v : M → ℝ, ∑ j, F.supply j * v j = 0 →
        ∃ D : ℝ, HasRightDerivAt0 (fun h => F.Psi (pstar + h • v)) D ∧ D ≤ 0 := by
  obtain ⟨hpos, hbal⟩ := hp
  constructor
  · rintro ⟨z, hz⟩ v hv
    exact ⟨Dval F pstar v, psi_rightDeriv F hF pstar hpos v, one_imp_two F hF pstar hpos z hz v hv⟩
  · intro h
    have hfoc : ∀ v : M → ℝ, ∑ j, F.supply j * v j = 0 → Dval F pstar v ≤ 0 := by
      intro v hv
      obtain ⟨D, hD, hle⟩ := h v hv
      have := tendsto_nhds_unique hD (psi_rightDeriv F hF pstar hpos v)
      rw [← this]; exact hle
    obtain ⟨x, ⟨hx0, hxJ, hxB⟩, hcol⟩ := target_mem F hF pstar hpos hbal hfoc
    refine ⟨fun a j => x a j / pstar j, fun j => (hpos j).le,
      fun a j => div_nonneg (hx0 a j) (hpos j).le, fun a => ?_, fun j => ?_⟩
    · rw [mem_demandSet_iff F hF pstar (fun j => (hpos j).le)]
      have hspend : ∑ j, pstar j * (x a j / pstar j) = F.earn a := by
        rw [← hxB a]; refine Finset.sum_congr rfl (fun j _ => ?_)
        field_simp [(hpos j).ne']
      have hμ := mu_pos F hF pstar hpos a
      have hdis : ∑ l, F.disutil a l * (x a l / pstar l) = F.earn a / F.mu a pstar := by
        rw [← hxB a, Finset.sum_div]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        by_cases hl : l ∈ Jset F pstar a
        · have hr := (mem_Jset F pstar a l).1 hl
          have hd := (hF.1 a l).ne'
          have hpl := (hpos l).ne'
          rw [← hr]; field_simp
        · rw [hxJ a l hl]; simp
      refine ⟨fun j => div_nonneg (hx0 a j) (hpos j).le, hspend.ge, fun j hj => ?_⟩
      rw [hdis]
      have hr : pstar j / F.disutil a j ≤ F.mu a pstar :=
        Finset.le_sup' (fun j => pstar j / F.disutil a j) (mem_univ j)
      have hd := hF.1 a j
      have hB := hF.2.1 a
      rw [div_le_iff₀ hd] at hr
      rw [mul_div_assoc', div_le_iff₀ hμ]
      nlinarith
    · have := congrFun hcol j
      simp only [colL, LinearMap.coe_mk, AddHom.coe_mk] at this
      rw [← Finset.sum_div, this]
      field_simp [(hpos j).ne']

end LinearChoresCLS.T23

open LinearChoresCLS Finset

theorem solution {N M : Type*} [Fintype N] [Fintype M] [Nonempty M]
    (F : ChoresMarket N M) (hF : F.Valid) (pstar : M → ℝ) (hp : pstar ∈ F.priceDomain) :
    (∃ z : N → M → ℝ, F.IsCE pstar z) ↔
      ∀ v : M → ℝ, ∑ j, F.supply j * v j = 0 →
        ∃ D : ℝ, HasRightDerivAt0 (fun h => F.Psi (pstar + h • v)) D ∧ D ≤ 0 :=
  LinearChoresCLS.T23.thm23 F hF pstar hp
