-- Prove2me | solution 1 for LinearChoresCLS.chores_short_rational_ce
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T00:43:03.012167+00:00
-- url     : https://prove2.me/submissions/3a8ed2af-fca2-4785-847e-11ce4b8c1228

import Mathlib
import Definitions.Def_LinearChoresCLS_Psi
import Definitions.Def_LinearChoresCLS_RightDeriv
import Definitions.Def_LinearChoresCLS_ChoresSearch
import Theorems.Thm_MIQPInNP_SmallSol_theorem_3
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity

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


open Finset Filter Topology

namespace LinearChoresCLS.T23

variable {N M : Type*} [Fintype N] [Fintype M] [Nonempty M]

def Pbar (F : ChoresMarket N M) : Set (M → ℝ) :=
  {p | (∀ j, 0 ≤ p j) ∧ ∑ j, F.supply j * p j = ∑ a, F.earn a}

theorem Pbar_compact (F : ChoresMarket N M) (hF : F.Valid) : IsCompact (Pbar F) := by
  have hbox : IsCompact (Set.univ.pi (fun j : M => Set.Icc (0 : ℝ) ((∑ a, F.earn a) / F.supply j))) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  refine hbox.of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {p : M → ℝ | ∀ j, 0 ≤ p j} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter (fun j => isClosed_le continuous_const (continuous_apply j))
    have h2 : IsClosed {p : M → ℝ | ∑ j, F.supply j * p j = ∑ a, F.earn a} :=
      isClosed_eq (continuous_finset_sum _ (fun j _ => continuous_const.mul (continuous_apply j)))
        continuous_const
    exact h1.inter h2
  · rintro p ⟨hp0, hsum⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro j
    refine ⟨hp0 j, ?_⟩
    rw [le_div_iff₀ (hF.2.2 j), ← hsum, mul_comm]
    exact Finset.single_le_sum (fun l _ => mul_nonneg (hF.2.2 l).le (hp0 l)) (mem_univ j)

theorem mu_pos_of_Pbar [Nonempty N] (F : ChoresMarket N M) (hF : F.Valid) (p : M → ℝ)
    (hp : p ∈ Pbar F) (a : N) : 0 < F.mu a p := by
  obtain ⟨hp0, hsum⟩ := hp
  have hBt : 0 < ∑ a, F.earn a := by
    obtain ⟨a0⟩ := (inferInstance : Nonempty N)
    exact lt_of_lt_of_le (hF.2.1 a0) (Finset.single_le_sum (fun a _ => (hF.2.1 a).le) (mem_univ a0))
  obtain ⟨j, hj⟩ : ∃ j, 0 < p j := by
    by_contra h
    push Not at h
    have : ∑ j, F.supply j * p j = 0 :=
      Finset.sum_eq_zero (fun j _ => by rw [le_antisymm (h j) (hp0 j), mul_zero])
    linarith
  exact lt_of_lt_of_le (div_pos hj (hF.1 a j))
    (Finset.le_sup' (fun j => p j / F.disutil a j) (mem_univ j))

theorem mu_continuous (F : ChoresMarket N M) (a : N) : Continuous (fun p : M → ℝ => F.mu a p) := by
  unfold ChoresMarket.mu
  exact Continuous.finset_sup'_apply _ (fun j _ => (continuous_apply j).div_const _)

theorem psi_continuousOn [Nonempty N] (F : ChoresMarket N M) (hF : F.Valid) :
    ContinuousOn F.Psi (Pbar F) := by
  unfold ChoresMarket.Psi
  refine ContinuousOn.neg (continuousOn_finset_sum _ (fun a _ => ?_))
  exact continuousOn_const.mul ((mu_continuous F a).continuousOn.log
    (fun p hp => (mu_pos_of_Pbar F hF p hp a).ne'))

end LinearChoresCLS.T23

namespace LinearChoresCLS.T23
open Finset Filter Topology

variable {N M : Type*} [Fintype N] [Fintype M] [Nonempty M] [Nonempty N]

theorem Pbar_nonempty (F : ChoresMarket N M) (hF : F.Valid) : (Pbar F).Nonempty := by
  classical
  refine ⟨fun j => (∑ a, F.earn a) / (Fintype.card M * F.supply j), fun j => ?_, ?_⟩
  · exact div_nonneg (Finset.sum_nonneg (fun a _ => (hF.2.1 a).le))
      (mul_nonneg (Nat.cast_nonneg _) (hF.2.2 j).le)
  · have hc : (Fintype.card M : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have : ∀ j, F.supply j * ((∑ a, F.earn a) / (Fintype.card M * F.supply j)) =
        (∑ a, F.earn a) / Fintype.card M := by
      intro j; have := (hF.2.2 j).ne'; field_simp
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp

/-- The maximizer of `Ψ` on the closed price simplex has strictly positive prices. -/
theorem max_interior (F : ChoresMarket N M) (hF : F.Valid) (p : M → ℝ) (hp : p ∈ Pbar F)
    (hmax : ∀ q ∈ Pbar F, F.Psi q ≤ F.Psi p) : ∀ j, 0 < p j := by
  classical
  intro j0
  rcases (hp.1 j0).lt_or_eq with h | h
  · exact h
  exfalso
  set Bt := ∑ a, F.earn a with hBt
  have hBpos : 0 < Bt := by
    obtain ⟨a0⟩ := (inferInstance : Nonempty N)
    exact lt_of_lt_of_le (hF.2.1 a0) (Finset.single_le_sum (fun a _ => (hF.2.1 a).le) (mem_univ a0))
  set e : M → ℝ := fun l => if l = j0 then Bt / F.supply j0 else 0 with he
  set q : ℝ → M → ℝ := fun δ => (1 - δ) • p + δ • e with hq
  -- for small δ, every μ_a scales by (1 - δ)
  have hμ : ∀ a, ∀ᶠ δ in 𝓝[>] (0 : ℝ), F.mu a (q δ) = (1 - δ) * F.mu a p := by
    intro a
    have hμa := mu_pos_of_Pbar F hF p hp a
    obtain ⟨l1, -, hl1⟩ := Finset.exists_mem_eq_sup' (univ_nonempty (α := M))
      (fun j => p j / F.disutil a j)
    have hc : Tendsto (fun δ : ℝ => (1 - δ) * F.mu a p - δ * (Bt / F.supply j0) / F.disutil a j0)
        (𝓝[>] 0) (𝓝 (F.mu a p)) := by
      have : Continuous (fun δ : ℝ => (1 - δ) * F.mu a p - δ * (Bt / F.supply j0) / F.disutil a j0) := by
        continuity
      have h2 := this.tendsto 0
      simp only [sub_zero, one_mul, zero_mul, zero_div] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    filter_upwards [hc.eventually (lt_mem_nhds (half_lt_self hμa)), self_mem_nhdsWithin]
      with δ hδ hδpos
    have hδ1 : δ < 1 := by
      by_contra hge; push Not at hge
      have : (1 - δ) * F.mu a p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hμa.le
      have : 0 ≤ δ * (Bt / F.supply j0) / F.disutil a j0 :=
        div_nonneg (mul_nonneg (le_of_lt hδpos) (div_nonneg hBpos.le (hF.2.2 j0).le)) (hF.1 a j0).le
      linarith
    unfold ChoresMarket.mu
    apply le_antisymm
    · refine Finset.sup'_le _ _ (fun l _ => ?_)
      simp only [hq, he, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hl : l = j0
      · subst hl
        rw [← h]; simp only [mul_zero, zero_add, if_true]
        have : δ * (Bt / F.supply l) / F.disutil a l ≤ (1 - δ) * F.mu a p := by linarith
        unfold ChoresMarket.mu at this; exact this
      · simp only [hl, if_false, mul_zero, add_zero]
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun j => p j / F.disutil a j) (mem_univ l))
          (by linarith)
    · have hl1ne : l1 ≠ j0 := by
        intro heq; rw [heq, ← h, zero_div] at hl1
        unfold ChoresMarket.mu at hμa; linarith
      have := Finset.le_sup' (fun l => ((1 - δ) • p + δ • e) l / F.disutil a l) (mem_univ l1)
      simp only [he, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hl1ne, if_false, mul_zero,
        add_zero] at this
      rw [mul_div_assoc, ← hl1] at this
      exact this
  have hlt1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1 :=
    (eventually_lt_nhds one_pos).filter_mono nhdsWithin_le_nhds
  obtain ⟨δ, ⟨hδall, hδpos⟩, hδ1⟩ :=
    (((Filter.eventually_all.2 hμ).and self_mem_nhdsWithin).and hlt1).exists
  have hqP : q δ ∈ Pbar F := by
    refine ⟨fun l => ?_, ?_⟩
    · simp only [hq, he, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine add_nonneg (mul_nonneg (by linarith) (hp.1 l)) (mul_nonneg hδpos.le ?_)
      split_ifs
      · exact div_nonneg hBpos.le (hF.2.2 j0).le
      · exact le_rfl
    · simp only [hq, he, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add]
      rw [Finset.sum_add_distrib]
      have e1 : ∑ x, F.supply x * ((1 - δ) * p x) = (1 - δ) * Bt := by
        rw [hBt, ← hp.2, Finset.mul_sum]; refine Finset.sum_congr rfl (fun l _ => by ring)
      have e2 : ∑ x, F.supply x * (δ * if x = j0 then Bt / F.supply j0 else 0) = δ * Bt := by
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        have := (hF.2.2 j0).ne'; field_simp
      rw [e1, e2]; ring
  have hle := hmax (q δ) hqP
  have hPsi : F.Psi (q δ) = F.Psi p - Bt * Real.log (1 - δ) := by
    unfold ChoresMarket.Psi
    have : ∀ a, F.earn a * Real.log (F.mu a (q δ)) =
        F.earn a * Real.log (1 - δ) + F.earn a * Real.log (F.mu a p) := by
      intro a
      rw [hδall a, Real.log_mul (by linarith) (mu_pos_of_Pbar F hF p hp a).ne']; ring
    simp only [this, Finset.sum_add_distrib, ← Finset.sum_mul, hBt]; ring
  have hlog : Real.log (1 - δ) < 0 := Real.log_neg (by linarith) (by linarith [hδpos])
  rw [hPsi] at hle
  nlinarith

end LinearChoresCLS.T23

namespace LinearChoresCLS.T23
open Finset Filter Topology

variable {N M : Type*} [Fintype N] [Fintype M] [Nonempty M] [Nonempty N]

theorem exists_CE (F : ChoresMarket N M) (hF : F.Valid) :
    ∃ p : M → ℝ, ∃ z : N → M → ℝ, F.IsCE p z ∧ ∀ j, 0 < p j := by
  obtain ⟨p, hp, hmax⟩ := (Pbar_compact F hF).exists_isMaxOn (Pbar_nonempty F hF)
    (psi_continuousOn F hF)
  have hmax' : ∀ q ∈ Pbar F, F.Psi q ≤ F.Psi p := fun q hq => hmax hq
  have hpos := max_interior F hF p hp hmax'
  have hdom : p ∈ F.priceDomain := ⟨hpos, hp.2⟩
  obtain ⟨z, hz⟩ := (thm23 F hF p hdom).2 (fun v hv => by
    refine ⟨Dval F p v, psi_rightDeriv F hF p hpos v, ?_⟩
    have hT := psi_rightDeriv F hF p hpos v
    unfold HasRightDerivAt0 at hT
    refine le_of_tendsto hT ?_
    -- p + h v stays in Pbar for small h > 0
    have hev : ∀ j, ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 ≤ p j + h * v j := by
      intro j
      have hc : Tendsto (fun h : ℝ => p j + h * v j) (𝓝[>] 0) (𝓝 (p j)) := by
        have : Continuous (fun h : ℝ => p j + h * v j) := by continuity
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      exact (hc.eventually (lt_mem_nhds (hpos j))).mono (fun h hh => hh.le)
    filter_upwards [Filter.eventually_all.2 hev, self_mem_nhdsWithin] with h hh hpos'
    have hin : p + h • v ∈ Pbar F := by
      refine ⟨fun j => by simpa using hh j, ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
      have : ∑ j, F.supply j * (h * v j) = h * ∑ j, F.supply j * v j := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => by ring)
      rw [this, hv, mul_zero, add_zero, hp.2]
    have hle := hmax' _ hin
    have h0 : p + (0 : ℝ) • v = p := by simp
    rw [smul_eq_mul, h0]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (le_of_lt hpos')) (by linarith))
  exact ⟨p, z, hz, hpos⟩

end LinearChoresCLS.T23


open Finset

namespace LinearChoresCLS.RatCE

variable {nA nC : ℕ}

/-- LP variables: prices `p_j`, ratios `μ_a`, money flows `x_{aj}`. -/
abbrev V (nA nC : ℕ) := Fin nC ⊕ Fin nA ⊕ (Fin nA × Fin nC)
/-- LP rows. -/
abbrev R (nA nC : ℕ) := (Fin nA × Fin nC × Fin 4) ⊕ (Fin nA × Fin 2) ⊕ (Fin nC × Fin 2) ⊕ Fin nC ⊕ Fin nA

open Classical in
/-- Row coefficients of the LP `A y ≤ b` attached to an edge set `E`. -/
noncomputable def Arow (F : RatChoresMarket nA nC) (E : Fin nA → Fin nC → Prop) :
    R nA nC → V nA nC → ℚ
  -- k = 0: p_j - d_{aj} μ_a ≤ 0
  | .inl (a, j, 0), .inl j' => if j' = j then 1 else 0
  | .inl (a, j, 0), .inr (.inl a') => if a' = a then -F.disutil a j else 0
  -- k = 1: on E, d_{aj} μ_a - p_j ≤ 0
  | .inl (a, j, 1), .inl j' => if E a j ∧ j' = j then -1 else 0
  | .inl (a, j, 1), .inr (.inl a') => if E a j ∧ a' = a then F.disutil a j else 0
  -- k = 2: -x_{aj} ≤ 0
  | .inl (a, j, 2), .inr (.inr (a', j')) => if a' = a ∧ j' = j then -1 else 0
  -- k = 3: off E, x_{aj} ≤ 0
  | .inl (a, j, 3), .inr (.inr (a', j')) => if ¬ E a j ∧ a' = a ∧ j' = j then 1 else 0
  -- budget rows: ± ∑_j x_{aj}
  | .inr (.inl (a, 0)), .inr (.inr (a', _)) => if a' = a then 1 else 0
  | .inr (.inl (a, 1)), .inr (.inr (a', _)) => if a' = a then -1 else 0
  -- clearing rows: ± (∑_a x_{aj} - S_j p_j)
  | .inr (.inr (.inl (j, 0))), .inr (.inr (_, j')) => if j' = j then 1 else 0
  | .inr (.inr (.inl (j, 0))), .inl j' => if j' = j then -F.supply j else 0
  | .inr (.inr (.inl (j, 1))), .inr (.inr (_, j')) => if j' = j then -1 else 0
  | .inr (.inr (.inl (j, 1))), .inl j' => if j' = j then F.supply j else 0
  -- nonnegativity of prices and ratios
  | .inr (.inr (.inr (.inl j))), .inl j' => if j' = j then -1 else 0
  | .inr (.inr (.inr (.inr a))), .inr (.inl a') => if a' = a then -1 else 0
  | _, _ => 0

noncomputable def bRow (F : RatChoresMarket nA nC) : R nA nC → ℚ
  | .inr (.inl (a, 0)) => F.earn a
  | .inr (.inl (a, 1)) => -F.earn a
  | _ => 0

/-- The LP inequalities for a real point `(p, μ, x)`. -/
def Feasible (F : RatChoresMarket nA nC) (E : Fin nA → Fin nC → Prop) (y : V nA nC → ℝ) : Prop :=
  ∀ r, ∑ v, (Arow F E r v : ℝ) * y v ≤ (bRow F r : ℝ)

end LinearChoresCLS.RatCE

namespace LinearChoresCLS.RatCE
open Finset
variable {nA nC : ℕ}

section rows
variable (F : RatChoresMarket nA nC) (E : Fin nA → Fin nC → Prop) (y : V nA nC → ℝ)

open Classical

theorem row0 (a : Fin nA) (j : Fin nC) :
    ∑ v, (Arow F E (.inl (a, j, 0)) v : ℝ) * y v =
      y (Sum.inl j) - (F.disutil a j : ℝ) * y (Sum.inr (Sum.inl a)) := by
  simp [Arow, Fintype.sum_sum_type, apply_ite (Rat.cast : ℚ → ℝ), ite_mul]; ring

theorem row1 (a : Fin nA) (j : Fin nC) :
    ∑ v, (Arow F E (.inl (a, j, 1)) v : ℝ) * y v =
      if E a j then (F.disutil a j : ℝ) * y (Sum.inr (Sum.inl a)) - y (Sum.inl j) else 0 := by
  by_cases h : E a j <;> simp [Arow, Fintype.sum_sum_type, h, apply_ite (Rat.cast : ℚ → ℝ), ite_mul]
  ring

theorem row2 (a : Fin nA) (j : Fin nC) :
    ∑ v, (Arow F E (.inl (a, j, 2)) v : ℝ) * y v = -y (Sum.inr (Sum.inr (a, j))) := by
  simp [Arow, Fintype.sum_sum_type, Fintype.sum_prod_type, apply_ite (Rat.cast : ℚ → ℝ), ite_mul,
    ite_and, Finset.sum_ite_irrel]

theorem row3 (a : Fin nA) (j : Fin nC) :
    ∑ v, (Arow F E (.inl (a, j, 3)) v : ℝ) * y v =
      if E a j then 0 else y (Sum.inr (Sum.inr (a, j))) := by
  by_cases h : E a j <;> simp [Arow, Fintype.sum_sum_type, Fintype.sum_prod_type, h,
    apply_ite (Rat.cast : ℚ → ℝ), ite_mul, ite_and, Finset.sum_ite_irrel]

theorem rowB0 (a : Fin nA) :
    ∑ v, (Arow F E (.inr (.inl (a, 0))) v : ℝ) * y v = ∑ j, y (Sum.inr (Sum.inr (a, j))) := by
  simp [Arow, Fintype.sum_sum_type, Fintype.sum_prod_type, apply_ite (Rat.cast : ℚ → ℝ), ite_mul]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]; simp

theorem rowB1 (a : Fin nA) :
    ∑ v, (Arow F E (.inr (.inl (a, 1))) v : ℝ) * y v = -∑ j, y (Sum.inr (Sum.inr (a, j))) := by
  simp [Arow, Fintype.sum_sum_type, Fintype.sum_prod_type, apply_ite (Rat.cast : ℚ → ℝ), ite_mul]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]; simp

theorem rowC0 (j : Fin nC) :
    ∑ v, (Arow F E (.inr (.inr (.inl (j, 0)))) v : ℝ) * y v =
      ∑ a, y (Sum.inr (Sum.inr (a, j))) - (F.supply j : ℝ) * y (Sum.inl j) := by
  simp [Arow, Fintype.sum_sum_type, Fintype.sum_prod_type, apply_ite (Rat.cast : ℚ → ℝ), ite_mul]
  ring

theorem rowC1 (j : Fin nC) :
    ∑ v, (Arow F E (.inr (.inr (.inl (j, 1)))) v : ℝ) * y v =
      (F.supply j : ℝ) * y (Sum.inl j) - ∑ a, y (Sum.inr (Sum.inr (a, j))) := by
  simp [Arow, Fintype.sum_sum_type, Fintype.sum_prod_type, apply_ite (Rat.cast : ℚ → ℝ), ite_mul]
  ring

theorem rowP (j : Fin nC) :
    ∑ v, (Arow F E (.inr (.inr (.inr (.inl j)))) v : ℝ) * y v = -y (Sum.inl j) := by
  simp [Arow, Fintype.sum_sum_type, apply_ite (Rat.cast : ℚ → ℝ), ite_mul]

theorem rowU (a : Fin nA) :
    ∑ v, (Arow F E (.inr (.inr (.inr (.inr a)))) v : ℝ) * y v = -y (Sum.inr (Sum.inl a)) := by
  simp [Arow, Fintype.sum_sum_type, apply_ite (Rat.cast : ℚ → ℝ), ite_mul]

end rows

end LinearChoresCLS.RatCE

namespace LinearChoresCLS.RatCE
open Finset Classical
variable {nA nC : ℕ}

theorem ce_of_feasible [Nonempty (Fin nC)] (F : RatChoresMarket nA nC) (hF : F.toReal.Valid)
    (E : Fin nA → Fin nC → Prop) (hE : ∀ j, ∃ a, E a j) (y : V nA nC → ℝ) (hy : Feasible F E y) :
    (∀ j, 0 < y (Sum.inl j)) ∧
      F.toReal.IsCE (fun j => y (Sum.inl j))
        (fun a j => y (Sum.inr (Sum.inr (a, j))) / y (Sum.inl j)) := by
  have hd : ∀ a j, (0 : ℝ) < F.disutil a j := hF.1
  have hBp : ∀ a, (0 : ℝ) < F.earn a := hF.2.1
  have hSp : ∀ j, (0 : ℝ) < F.supply j := hF.2.2
  set P : Fin nC → ℝ := fun j => y (Sum.inl j)
  set U : Fin nA → ℝ := fun a => y (Sum.inr (Sum.inl a))
  set X : Fin nA → Fin nC → ℝ := fun a j => y (Sum.inr (Sum.inr (a, j)))
  have h0 : ∀ a j, P j ≤ (F.disutil a j : ℝ) * U a := fun a j => by
    have := hy (.inl (a, j, 0)); rw [row0] at this; simp [bRow] at this; linarith
  have h1 : ∀ a j, E a j → (F.disutil a j : ℝ) * U a ≤ P j := fun a j hE => by
    have := hy (.inl (a, j, 1)); rw [row1] at this; simp [bRow, hE] at this; linarith
  have h2 : ∀ a j, 0 ≤ X a j := fun a j => by
    have := hy (.inl (a, j, 2)); rw [row2] at this; simp [bRow] at this; linarith
  have h3 : ∀ a j, ¬ E a j → X a j ≤ 0 := fun a j hE => by
    have := hy (.inl (a, j, 3)); rw [row3] at this; simp [bRow, hE] at this; linarith
  have hB : ∀ a, ∑ j, X a j = F.earn a := fun a => by
    have e0 := hy (.inr (.inl (a, 0))); rw [rowB0] at e0
    have e1 := hy (.inr (.inl (a, 1))); rw [rowB1] at e1
    simp only [bRow, Rat.cast_neg] at e0 e1; linarith
  have hC : ∀ j, ∑ a, X a j = (F.supply j : ℝ) * P j := fun j => by
    have e0 := hy (.inr (.inr (.inl (j, 0)))); rw [rowC0] at e0
    have e1 := hy (.inr (.inr (.inl (j, 1)))); rw [rowC1] at e1
    simp only [bRow, Rat.cast_zero] at e0 e1; linarith
  have hP : ∀ j, 0 ≤ P j := fun j => by
    have := hy (.inr (.inr (.inr (.inl j)))); rw [rowP] at this; simp [bRow] at this; linarith
  have hU : ∀ a, 0 ≤ U a := fun a => by
    have := hy (.inr (.inr (.inr (.inr a)))); rw [rowU] at this; simp [bRow] at this; linarith
  -- every agent has positive ratio
  have hUpos : ∀ a, 0 < U a := by
    intro a
    obtain ⟨l, hl⟩ : ∃ l, 0 < X a l := by
      by_contra hno; push Not at hno
      have : ∑ j, X a j ≤ 0 := Finset.sum_nonpos (fun j _ => hno j)
      linarith [hB a, hBp a]
    have hEl : E a l := by by_contra hn; linarith [h3 a l hn]
    have hPl : 0 < P l := by
      have hsum := hC l
      have : X a l ≤ ∑ a', X a' l := Finset.single_le_sum (fun a' _ => h2 a' l) (mem_univ a)
      have := hSp l
      nlinarith
    have := h1 a l hEl
    have := hd a l
    by_contra hU0; push Not at hU0
    nlinarith [h0 a l]
  have hPpos : ∀ j, 0 < P j := by
    intro j
    obtain ⟨a, haj⟩ := hE j
    have := h1 a j haj
    have := mul_pos (hd a j) (hUpos a)
    linarith
  refine ⟨hPpos, fun j => (hPpos j).le, fun a j => div_nonneg (h2 a j) (hPpos j).le, fun a => ?_,
    fun j => ?_⟩
  · rw [T23.mem_demandSet_iff F.toReal hF _ (fun j => (hPpos j).le)]
    have hspend : ∑ j, P j * (X a j / P j) = F.earn a := by
      rw [← hB a]; refine Finset.sum_congr rfl (fun j _ => ?_)
      field_simp [(hPpos j).ne']
    have hdis : ∑ l, (F.disutil a l : ℝ) * (X a l / P l) = F.earn a / U a := by
      rw [← hB a, Finset.sum_div]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      by_cases hl : E a l
      · have heq : P l = (F.disutil a l : ℝ) * U a := le_antisymm (h0 a l) (h1 a l hl)
        rw [heq]; field_simp [(hd a l).ne', (hUpos a).ne']
      · have : X a l = 0 := le_antisymm (h3 a l hl) (h2 a l)
        simp [this]
    refine ⟨fun j => div_nonneg (h2 a j) (hPpos j).le, ?_, fun j _ => ?_⟩
    · show (F.earn a : ℝ) ≤ ∑ j, P j * (X a j / P j)
      rw [hspend]
    · show P j * ∑ l, (F.disutil a l : ℝ) * (X a l / P l) ≤ (F.earn a : ℝ) * F.disutil a j
      rw [hdis, mul_div_assoc', div_le_iff₀ (hUpos a)]
      nlinarith [h0 a j, hBp a]
  · show ∑ a, X a j / P j = (F.supply j : ℝ)
    rw [← Finset.sum_div, hC j]; field_simp [(hPpos j).ne']

end LinearChoresCLS.RatCE

namespace LinearChoresCLS.RatCE
open Finset Classical
variable {nA nC : ℕ}

theorem feasible_of_ce [Nonempty (Fin nC)] (F : RatChoresMarket nA nC) (hF : F.toReal.Valid)
    (p : Fin nC → ℝ) (z : Fin nA → Fin nC → ℝ) (hce : F.toReal.IsCE p z) (hp : ∀ j, 0 < p j) :
    (∀ j, ∃ a, j ∈ T23.Jset F.toReal p a) ∧
      Feasible F (fun a j => j ∈ T23.Jset F.toReal p a)
        (fun v => match v with
          | Sum.inl j => p j
          | Sum.inr (Sum.inl a) => F.toReal.mu a p
          | Sum.inr (Sum.inr (a, j)) => p j * z a j) := by
  obtain ⟨_, hz0, hdem, hclear⟩ := hce
  have hd : ∀ a j, (0 : ℝ) < F.disutil a j := hF.1
  have hsupp : ∀ a j, 0 < z a j → j ∈ T23.Jset F.toReal p a := fun a j h =>
    T23.support_J F.toReal hF p hp a (z a) (hdem a) j h
  refine ⟨fun j => ?_, ?_⟩
  · obtain ⟨a, ha⟩ : ∃ a, 0 < z a j := by
      by_contra hno; push Not at hno
      have : ∑ a, z a j ≤ 0 := Finset.sum_nonpos (fun a _ => hno a)
      have := hclear j
      have := hF.2.2 j
      simp only [RatChoresMarket.toReal] at *
      linarith
    exact ⟨a, hsupp a j ha⟩
  set y : V nA nC → ℝ := fun v => match v with
    | Sum.inl j => p j
    | Sum.inr (Sum.inl a) => F.toReal.mu a p
    | Sum.inr (Sum.inr (a, j)) => p j * z a j with hy
  set E : Fin nA → Fin nC → Prop := fun a j => j ∈ T23.Jset F.toReal p a with hE
  have r0 : ∀ a j, ∑ v, (Arow F E (.inl (a, j, 0)) v : ℝ) * y v ≤ (bRow F (.inl (a, j, 0)) : ℝ) := by
    intro a j
    rw [row0]; simp only [bRow, Rat.cast_zero]
    have hle : p j / F.toReal.disutil a j ≤ F.toReal.mu a p :=
      Finset.le_sup' (fun j => p j / F.toReal.disutil a j) (mem_univ j)
    have hle' : p j ≤ (F.disutil a j : ℝ) * F.toReal.mu a p := by
      have := (div_le_iff₀ (hd a j)).1 hle; linarith
    simp only [hy]; linarith
  have r1 : ∀ a j, ∑ v, (Arow F E (.inl (a, j, 1)) v : ℝ) * y v ≤ (bRow F (.inl (a, j, 1)) : ℝ) := by
    intro a j
    rw [row1]; simp only [bRow, Rat.cast_zero]
    split_ifs with hE'
    · have hr := (T23.mem_Jset F.toReal p a j).1 hE'
      have : (F.disutil a j : ℝ) * F.toReal.mu a p = p j := by
        rw [← hr]
        show (F.disutil a j : ℝ) * (p j / (F.disutil a j : ℝ)) = p j
        field_simp [(hd a j).ne']
      simp only [hy]; linarith
    · exact le_rfl
  have r2 : ∀ a j, ∑ v, (Arow F E (.inl (a, j, 2)) v : ℝ) * y v ≤ (bRow F (.inl (a, j, 2)) : ℝ) := by
    intro a j
    rw [row2]; simp only [bRow, Rat.cast_zero, hy]
    exact neg_nonpos.2 (mul_nonneg (hp j).le (hz0 a j))
  have r3 : ∀ a j, ∑ v, (Arow F E (.inl (a, j, 3)) v : ℝ) * y v ≤ (bRow F (.inl (a, j, 3)) : ℝ) := by
    intro a j
    rw [row3]; simp only [bRow, Rat.cast_zero]
    split_ifs with hE'
    · exact le_rfl
    · have : z a j = 0 := by
        rcases (hz0 a j).lt_or_eq with h | h
        · exact absurd (hsupp a j h) hE'
        · exact h.symm
      simp [hy, this]
  have rB : ∀ a, (∑ v, (Arow F E (.inr (.inl (a, 0))) v : ℝ) * y v ≤ (bRow F (.inr (.inl (a, 0))) : ℝ)) ∧
      (∑ v, (Arow F E (.inr (.inl (a, 1))) v : ℝ) * y v ≤ (bRow F (.inr (.inl (a, 1))) : ℝ)) := by
    intro a
    have hs := T23.spend_eq F.toReal hF p hp a (z a) (hdem a)
    have hsum : ∑ j, y (Sum.inr (Sum.inr (a, j))) = F.earn a := by simp only [hy]; exact hs
    refine ⟨?_, ?_⟩
    · rw [rowB0, hsum]; simp [bRow]
    · rw [rowB1, hsum]; simp [bRow]
  have rC : ∀ j, (∑ v, (Arow F E (.inr (.inr (.inl (j, 0)))) v : ℝ) * y v ≤
        (bRow F (.inr (.inr (.inl (j, 0)))) : ℝ)) ∧
      (∑ v, (Arow F E (.inr (.inr (.inl (j, 1)))) v : ℝ) * y v ≤
        (bRow F (.inr (.inr (.inl (j, 1)))) : ℝ)) := by
    intro j
    have hc := hclear j
    have e : ∑ a, y (Sum.inr (Sum.inr (a, j))) = (F.supply j : ℝ) * y (Sum.inl j) := by
      simp only [hy]
      rw [← Finset.mul_sum, hc]; simp [RatChoresMarket.toReal, mul_comm]
    refine ⟨?_, ?_⟩
    · rw [rowC0, e]; simp [bRow]
    · rw [rowC1, e]; simp [bRow]
  intro r
  rcases r with ⟨a, j, k⟩ | ⟨a, k⟩ | ⟨j, k⟩ | j | a
  · fin_cases k
    · exact r0 a j
    · exact r1 a j
    · exact r2 a j
    · exact r3 a j
  · fin_cases k
    · exact (rB a).1
    · exact (rB a).2
  · fin_cases k
    · exact (rC j).1
    · exact (rC j).2
  · rw [rowP]; simp only [bRow, Rat.cast_zero, hy]; exact neg_nonpos.2 (hp j).le
  · rw [rowU]; simp only [bRow, Rat.cast_zero, hy]
    exact neg_nonpos.2 (T23.mu_pos F.toReal hF p hp a).le

end LinearChoresCLS.RatCE


open Finset Classical

namespace LinearChoresCLS.RatCE
open MIQPInNP.SmallSol
variable {nA nC : ℕ}

noncomputable def eV (nA nC : ℕ) : V nA nC ≃ Fin (Fintype.card (V nA nC)) := Fintype.equivFin _
noncomputable def eR (nA nC : ℕ) : R nA nC ≃ Fin (Fintype.card (R nA nC)) := Fintype.equivFin _

noncomputable def Amat (F : RatChoresMarket nA nC) (E : Fin nA → Fin nC → Prop) :
    Matrix (Fin (Fintype.card (R nA nC))) (Fin (Fintype.card (V nA nC))) ℚ :=
  fun i k => Arow F E ((eR nA nC).symm i) ((eV nA nC).symm k)

noncomputable def bvec (F : RatChoresMarket nA nC) : Fin (Fintype.card (R nA nC)) → ℚ :=
  fun i => bRow F ((eR nA nC).symm i)

theorem mem_polyhedron_iff (F : RatChoresMarket nA nC) (E : Fin nA → Fin nC → Prop)
    (y : Fin (Fintype.card (V nA nC)) → ℝ) :
    y ∈ polyhedron (Amat F E) (bvec F) ↔ Feasible F E (fun v => y (eV nA nC v)) := by
  unfold polyhedron Feasible Amat bvec
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h r
    have := h (eR nA nC r)
    simp only [Equiv.symm_apply_apply] at this
    have e := (eV nA nC).symm.sum_comp (fun v => (Arow F E r v : ℝ) * y (eV nA nC v))
    simp only [Equiv.apply_symm_apply] at e
    rw [← e]; exact this
  · intro h i
    have := h ((eR nA nC).symm i)
    have e := (eV nA nC).symm.sum_comp
      (fun v => (Arow F E ((eR nA nC).symm i) v : ℝ) * y (eV nA nC v))
    simp only [Equiv.apply_symm_apply] at e
    rw [e]; exact this

theorem small_rat_point :
    ∃ g : Polynomial ℕ, ∀ (nA nC : ℕ) (F : RatChoresMarket nA nC) (E : Fin nA → Fin nC → Prop)
      (y : V nA nC → ℝ), Feasible F E y →
      ∃ yh : Fin (Fintype.card (V nA nC)) → ℚ, Feasible F E (fun v => (yh (eV nA nC v) : ℝ)) ∧
        vecSize yh ≤ g.eval (instSize 0 0 0 (Amat F E) (bvec F)) := by
  obtain ⟨g, hg, -⟩ := MIQPInNP.SmallSol.theorem_3
  refine ⟨g, fun nA nC F E y hy => ?_⟩
  have hne : (feasSet 0 (0 : Matrix (Fin (Fintype.card (V nA nC))) (Fin (Fintype.card (V nA nC))) ℚ)
      0 0 (Amat F E) (bvec F)).Nonempty := by
    refine ⟨fun k => y ((eV nA nC).symm k), ?_, ?_, ?_⟩
    · simp [quadVal, quadForm]
    · rw [mem_polyhedron_iff]; simpa using hy
    · intro i hi; exact absurd hi (Nat.not_lt_zero _)
  obtain ⟨yh, ⟨_, hmem, _⟩, hsize⟩ := hg _ _ _ _ _ _ _ hne
  exact ⟨yh, (mem_polyhedron_iff F E _).1 hmem, hsize⟩

end LinearChoresCLS.RatCE


open Finset

namespace LinearChoresCLS.RatCE
open MIQPInNP.SmallSol

theorem size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

theorem bitSize_neg (q : ℚ) : bitSize (-q) = bitSize q := by
  simp [bitSize]

theorem bitSize_zero : bitSize 0 = 2 := by simp [bitSize]
theorem bitSize_one : bitSize 1 = 3 := by simp [bitSize]

theorem two_le_bitSize (q : ℚ) : 2 ≤ bitSize q := by
  unfold bitSize
  have : 1 ≤ Nat.size q.den := by
    rw [Nat.one_le_iff_ne_zero, Ne, Nat.size_eq_zero]; exact q.den_ne_zero
  omega

theorem bitSize_div_le (x y : ℚ) : bitSize (x / y) ≤ bitSize x + bitSize y := by
  by_cases hy : y = 0
  · subst hy; simp only [div_zero, bitSize_zero]; have := two_le_bitSize x; omega
  have hyn : y.num ≠ 0 := Rat.num_ne_zero.2 hy
  have hrep : x / y = Rat.divInt (x.num * y.den) (x.den * y.num) := by
    rw [Rat.divInt_eq_div]; push_cast
    conv_lhs => rw [← Rat.num_div_den x, ← Rat.num_div_den y]
    have : (y.num : ℚ) ≠ 0 := by exact_mod_cast hyn
    have : (y.den : ℚ) ≠ 0 := by exact_mod_cast y.den_ne_zero
    have : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
    field_simp
  have hden0 : (x.den : ℤ) * y.num ≠ 0 := mul_ne_zero (by exact_mod_cast x.den_ne_zero) hyn
  have hnum := Rat.num_dvd (x.num * y.den) hden0
  have hden := Rat.den_dvd (x.num * y.den) (x.den * y.num)
  rw [← hrep] at hnum hden
  -- numerators
  have h1 : (x / y).num.natAbs ≤ x.num.natAbs * y.den := by
    by_cases hx : x.num * y.den = 0
    · have : x = 0 := by
        rcases mul_eq_zero.1 hx with h | h
        · exact Rat.num_eq_zero.1 h
        · exact absurd h (by exact_mod_cast y.den_ne_zero)
      subst this; simp
    · have := Int.natAbs_le_of_dvd_ne_zero hnum hx
      simpa [Int.natAbs_mul] using this
  have h2 : (x / y).den ≤ x.den * y.num.natAbs := by
    have := Int.natAbs_le_of_dvd_ne_zero hden hden0
    simpa [Int.natAbs_mul] using this
  unfold bitSize
  have e1 := Nat.size_le_size h1
  have e2 := Nat.size_le_size h2
  have e3 := size_mul_le x.num.natAbs y.den
  have e4 := size_mul_le x.den y.num.natAbs
  omega

/-- Length of the LinearNash code of a natural. -/
theorem len_lnNat (n : ℕ) : (NetworkEquilibriumCLS.LinearNash.encNat n).length = 2 * Nat.size n + 1 := by
  simp [NetworkEquilibriumCLS.LinearNash.encNat, Nat.size_eq_bits_len]; omega

theorem len_lnRat (q : ℚ) : (NetworkEquilibriumCLS.LinearNash.encRat q).length = 2 * bitSize q + 1 := by
  simp [NetworkEquilibriumCLS.LinearNash.encRat, NetworkEquilibriumCLS.LinearNash.encInt, len_lnNat,
    bitSize]; omega

theorem size_le_self' (n : ℕ) : Nat.size n ≤ n := by
  rw [Nat.size_le]; exact Nat.lt_two_pow_self

end LinearChoresCLS.RatCE

namespace LinearChoresCLS.RatCE
open MIQPInNP.SmallSol Classical
variable {nA nC : ℕ}

theorem Arow_bitSize (F : RatChoresMarket nA nC) (E : Fin nA → Fin nC → Prop) (T : ℕ)
    (hd : ∀ a j, bitSize (F.disutil a j) ≤ T) (hS : ∀ j, bitSize (F.supply j) ≤ T)
    (r : R nA nC) (v : V nA nC) : bitSize (Arow F E r v) ≤ T + 3 := by
  have h0 : bitSize 0 ≤ T + 3 := by rw [bitSize_zero]; omega
  have h1 : bitSize 1 ≤ T + 3 := by rw [bitSize_one]; omega
  have hm1 : bitSize (-1) ≤ T + 3 := by rw [bitSize_neg, bitSize_one]; omega
  rcases r with ⟨a, j, k⟩ | ⟨a, k⟩ | ⟨j, k⟩ | j | a <;> rcases v with j' | a' | ⟨a', j'⟩ <;>
    (try fin_cases k) <;> simp only [Arow, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    (try split_ifs) <;>
    first
    | exact h0 | exact h1 | exact hm1
    | (rw [bitSize_neg]; have := hd a j; omega)
    | (have := hd a j; omega)
    | (rw [bitSize_neg]; have := hS j; omega)
    | (have := hS j; omega)

end LinearChoresCLS.RatCE

namespace LinearChoresCLS.RatCE
open MIQPInNP.SmallSol Classical
variable {nA nC : ℕ}

theorem bRow_bitSize (F : RatChoresMarket nA nC) (T : ℕ) (hB : ∀ a, bitSize (F.earn a) ≤ T)
    (r : R nA nC) : bitSize (bRow F r) ≤ T + 3 := by
  have h0 : bitSize 0 ≤ T + 3 := by rw [bitSize_zero]; omega
  rcases r with ⟨a, j, k⟩ | ⟨a, k⟩ | ⟨j, k⟩ | j | a <;> (try fin_cases k) <;>
    simp only [bRow, Fin.isValue, Fin.zero_eta, Fin.mk_one] <;>
    first | exact h0 | (have := hB a; omega) | (rw [bitSize_neg]; have := hB a; omega)

theorem instSize_le (F : RatChoresMarket nA nC) (E : Fin nA → Fin nC → Prop) (T : ℕ)
    (hd : ∀ a j, bitSize (F.disutil a j) ≤ T) (hS : ∀ j, bitSize (F.supply j) ≤ T)
    (hB : ∀ a, bitSize (F.earn a) ≤ T) :
    instSize 0 0 0 (Amat F E) (bvec F) ≤
      3 * Fintype.card (V nA nC) ^ 2 + 3 * Fintype.card (V nA nC) + 2 +
      Fintype.card (R nA nC) * Fintype.card (V nA nC) * (T + 4) + Fintype.card (R nA nC) * (T + 4) := by
  set nV := Fintype.card (V nA nC)
  set nR := Fintype.card (R nA nC)
  unfold instSize matSize vecSize
  simp only [Matrix.zero_apply, Pi.zero_apply, bitSize_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  have hA : ∑ i, ∑ k, bitSize (Amat F E i k) ≤ nR * nV * (T + 3) := by
    calc ∑ i, ∑ k, bitSize (Amat F E i k) ≤ ∑ _i : Fin nR, ∑ _k : Fin nV, (T + 3) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ =>
            Arow_bitSize F E T hd hS _ _))
      _ = nR * nV * (T + 3) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
  have hb : ∑ i, bitSize (bvec F i) ≤ nR * (T + 3) := by
    calc ∑ i, bitSize (bvec F i) ≤ ∑ _i : Fin nR, (T + 3) :=
          Finset.sum_le_sum (fun i _ => bRow_bitSize F T hB _)
      _ = nR * (T + 3) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  nlinarith [hA, hb]

theorem card_V : Fintype.card (V nA nC) = nC + (nA + nA * nC) := by
  simp [V, Fintype.card_sum, Fintype.card_prod]

theorem card_R : Fintype.card (R nA nC) = nA * nC * 4 + (nA * 2 + (nC * 2 + (nC + nA))) := by
  simp [R, Fintype.card_sum, Fintype.card_prod]; ring

end LinearChoresCLS.RatCE


open Finset

namespace LinearChoresCLS.RatCE
open MIQPInNP.SmallSol

theorem poly_eval_mono (g : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : g.eval x ≤ g.eval y := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i))

theorem le_vecSize {n : ℕ} (v : Fin n → ℚ) (i : Fin n) : bitSize (v i) ≤ vecSize v := by
  unfold vecSize
  have := Finset.single_le_sum (f := fun i => bitSize (v i)) (fun _ _ => Nat.zero_le _) (mem_univ i)
  omega

/-- Instance-size budget of the LP for a market with `nA` agents, `nC` chores and data of bit
size at most `T`. -/
def IB (nA nC T : ℕ) : ℕ :=
  3 * (nC + (nA + nA * nC)) ^ 2 + 3 * (nC + (nA + nA * nC)) + 2 +
    (nA * nC * 4 + (nA * 2 + (nC * 2 + (nC + nA)))) * (nC + (nA + nA * nC)) * (T + 4) +
    (nA * nC * 4 + (nA * 2 + (nC * 2 + (nC + nA)))) * (T + 4)

theorem rat_ce_sized :
    ∃ g : Polynomial ℕ, ∀ (nA nC : ℕ), 0 < nA → 0 < nC → ∀ (F : RatChoresMarket nA nC),
      F.toReal.Valid → ∀ T : ℕ, (∀ a j, bitSize (F.disutil a j) ≤ T) → (∀ j, bitSize (F.supply j) ≤ T) →
      (∀ a, bitSize (F.earn a) ≤ T) →
      ∃ (p : Fin nC → ℚ) (z : Fin nA → Fin nC → ℚ),
        F.toReal.IsCE (fun j => (p j : ℝ)) (fun a j => (z a j : ℝ)) ∧
        (∀ j, bitSize (p j) ≤ g.eval (IB nA nC T)) ∧
        (∀ a j, bitSize (z a j) ≤ 2 * g.eval (IB nA nC T)) := by
  obtain ⟨g, hg⟩ := small_rat_point
  refine ⟨g, fun nA nC hA hC F hF T hd hS hB => ?_⟩
  haveI : Nonempty (Fin nA) := ⟨⟨0, hA⟩⟩
  haveI : Nonempty (Fin nC) := ⟨⟨0, hC⟩⟩
  obtain ⟨p, z, hce, hp⟩ := T23.exists_CE F.toReal hF
  obtain ⟨hcov, hfeas⟩ := feasible_of_ce F hF p z hce hp
  obtain ⟨yh, hyf, hsz⟩ := hg nA nC F _ _ hfeas
  obtain ⟨_, hce'⟩ := ce_of_feasible F hF _ hcov _ hyf
  have hIB : g.eval (instSize 0 0 0 (Amat F (fun a j => j ∈ T23.Jset F.toReal p a)) (bvec F)) ≤
      g.eval (IB nA nC T) := by
    apply poly_eval_mono
    have := instSize_le F (fun a j => j ∈ T23.Jset F.toReal p a) T hd hS hB
    have hV : Fintype.card (V nA nC) = nC + (nA + nA * nC) := card_V
    have hR : Fintype.card (R nA nC) = nA * nC * 4 + (nA * 2 + (nC * 2 + (nC + nA))) := card_R
    refine this.trans (le_of_eq ?_)
    unfold IB; rw [hV, hR]
  refine ⟨fun j => yh (eV nA nC (Sum.inl j)),
    fun a j => yh (eV nA nC (Sum.inr (Sum.inr (a, j)))) / yh (eV nA nC (Sum.inl j)), ?_, ?_, ?_⟩
  · convert hce' using 2
    push_cast; rfl
  · intro j
    exact (le_vecSize yh _).trans (hsz.trans hIB)
  · intro a j
    have h1 := (le_vecSize yh (eV nA nC (Sum.inr (Sum.inr (a, j))))).trans (hsz.trans hIB)
    have h2 := (le_vecSize yh (eV nA nC (Sum.inl j))).trans (hsz.trans hIB)
    exact (bitSize_div_le _ _).trans (by omega)

end LinearChoresCLS.RatCE


open Finset

namespace LinearChoresCLS.RatCE
open MIQPInNP.SmallSol NetworkEquilibriumCLS.LinearNash

theorem poly_bound (h : Polynomial ℕ) : ∃ k : ℕ, ∀ s : ℕ, h.eval s ≤ (s + 1) ^ k + k := by
  refine ⟨h.natDegree + h.eval 1, fun s => ?_⟩
  have h1 : h.eval s ≤ h.eval 1 * (s + 1) ^ h.natDegree := by
    rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_le_sum (fun i hi => ?_)
    simp only [one_pow, mul_one]
    have hi' : i ≤ h.natDegree := by simpa [Nat.lt_succ_iff] using hi
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (Nat.le_succ s) i).trans
      (Nat.pow_le_pow_right (Nat.succ_pos s) hi'))
  have h2 : h.eval 1 ≤ (s + 1) ^ h.eval 1 + h.eval 1 := Nat.le_add_left _ _
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; simp at h1 ⊢; omega
  · have h3 : h.eval 1 ≤ (s + 1) ^ h.eval 1 :=
      (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left (by omega) _)
    calc h.eval s ≤ h.eval 1 * (s + 1) ^ h.natDegree := h1
      _ ≤ (s + 1) ^ h.eval 1 * (s + 1) ^ h.natDegree := Nat.mul_le_mul_right _ h3
      _ = (s + 1) ^ (h.natDegree + h.eval 1) := by rw [← pow_add, Nat.add_comm (h.eval 1)]
      _ ≤ _ := Nat.le_add_right _ _

theorem len_flatMap_ge {α : Type} (f : α → List Bool) (l : List α) (x : α) (hx : x ∈ l) :
    (f x).length ≤ (l.flatMap f).length := by
  rw [List.length_flatMap]
  exact List.le_sum_of_mem (List.mem_map.2 ⟨x, hx, rfl⟩)

theorem len_lnList {α : Type} (f : α → List Bool) (l : List α) :
    (encList f l).length = 2 * Nat.size l.length + 1 + (l.map (fun x => (f x).length)).sum := by
  simp [encList, len_lnNat, List.length_flatMap]

end LinearChoresCLS.RatCE

namespace LinearChoresCLS.RatCE
open MIQPInNP.SmallSol NetworkEquilibriumCLS.LinearNash Polynomial

theorem IB_mono {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    IB a b c ≤ IB a' b' c' := by
  unfold IB; gcongr

noncomputable def IBpoly : Polynomial ℕ :=
  3 * (X + (X + X * X)) ^ 2 + 3 * (X + (X + X * X)) + 2 +
    (X * X * 4 + (X * 2 + (X * 2 + (X + X)))) * (X + (X + X * X)) * (X + 4) +
    (X * X * 4 + (X * 2 + (X * 2 + (X + X)))) * (X + 4)

theorem IBpoly_eval (s : ℕ) : IBpoly.eval s = IB s s s := by
  simp [IBpoly, IB]

theorem len_encVector_le {n : ℕ} (v : Fin n → ℚ) (K : ℕ) (hK : ∀ j, bitSize (v j) ≤ K) :
    (encVector v).length ≤ 2 * n + 1 + n * (2 * K + 1) := by
  unfold encVector
  rw [len_lnList]
  simp only [List.length_ofFn, List.map_ofFn, List.sum_ofFn, Function.comp_def, len_lnRat]
  have h1 := size_le_self' n
  have h2 : ∑ j, (2 * bitSize (v j) + 1) ≤ ∑ _j : Fin n, (2 * K + 1) :=
    Finset.sum_le_sum (fun j _ => by have := hK j; omega)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  omega

theorem len_encCE_le {nA nC : ℕ} (p : Fin nC → ℚ) (z : Fin nA → Fin nC → ℚ) (K : ℕ)
    (hp : ∀ j, bitSize (p j) ≤ K) (hz : ∀ a j, bitSize (z a j) ≤ 2 * K) :
    (encCE p z).length ≤ 2 * nC + 1 + nC * (2 * K + 1) +
      (2 * nA + 1 + nA * (2 * nC + 1 + nC * (2 * (2 * K) + 1))) := by
  unfold encCE
  rw [List.length_append, len_lnList]
  have hv := len_encVector_le p K hp
  have hrow : ∀ a, (encVector (z a)).length ≤ 2 * nC + 1 + nC * (2 * (2 * K) + 1) :=
    fun a => len_encVector_le (z a) (2 * K) (hz a)
  simp only [List.length_ofFn, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  have h1 := size_le_self' nA
  have h2 : ∑ a, (encVector (z a)).length ≤ ∑ _a : Fin nA, (2 * nC + 1 + nC * (2 * (2 * K) + 1)) :=
    Finset.sum_le_sum (fun a _ => hrow a)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  omega

theorem data_le {nA nC : ℕ} (F : RatChoresMarket nA nC) :
    (∀ a j, bitSize (F.disutil a j) ≤ (encChores F).length) ∧
    (∀ j, bitSize (F.supply j) ≤ (encChores F).length) ∧
    (∀ a, bitSize (F.earn a) ≤ (encChores F).length) ∧
    nC ≤ (encChores F).length ∧ nA ≤ (encChores F).length := by
  have hlen : ∀ q : ℚ, bitSize q ≤ (encRat q).length := fun q => by rw [len_lnRat]; omega
  have hpart : (encList (encList encRat) (List.ofFn fun a => List.ofFn (F.disutil a))).length ≤
        (encChores F).length ∧ (encVector F.earn).length ≤ (encChores F).length ∧
      (encVector F.supply).length ≤ (encChores F).length := by
    unfold encChores; simp only [List.length_append]; omega
  have hvec : ∀ {n : ℕ} (v : Fin n → ℚ) (j : Fin n), bitSize (v j) ≤ (encVector v).length := by
    intro n v j
    unfold encVector encList
    simp only [List.length_append]
    have := len_flatMap_ge encRat (List.ofFn v) (v j) (List.mem_ofFn.2 ⟨j, rfl⟩)
    have := hlen (v j); omega
  have hvecn : ∀ {n : ℕ} (v : Fin n → ℚ), n ≤ (encVector v).length := by
    intro n v
    unfold encVector
    rw [len_lnList]
    simp only [List.length_ofFn, List.map_ofFn, List.sum_ofFn, Function.comp_def, len_lnRat]
    have : ∑ _j : Fin n, 1 ≤ ∑ j, (2 * bitSize (v j) + 1) := Finset.sum_le_sum (fun j _ => by omega)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
    omega
  refine ⟨fun a j => ?_, fun j => (hvec F.supply j).trans hpart.2.2,
    fun a => (hvec F.earn a).trans hpart.2.1, (hvecn F.supply).trans hpart.2.2,
    (hvecn F.earn).trans hpart.2.1⟩
  refine le_trans ?_ hpart.1
  have hc : (List.flatMap (encList encRat) (List.ofFn fun a => List.ofFn (F.disutil a))).length ≤
      (encList (encList encRat) (List.ofFn fun a => List.ofFn (F.disutil a))).length := by
    show _ ≤ (encNat _ ++ _).length
    simp
  have h1 := len_flatMap_ge (encList encRat) (List.ofFn fun a => List.ofFn (F.disutil a))
    (List.ofFn (F.disutil a)) (List.mem_ofFn.2 ⟨a, rfl⟩)
  have h2 := hvec (F.disutil a) j
  unfold encVector at h2
  omega

theorem short_rational_ce : ∃ k : ℕ, TotalSearch (bounded choresCESearch k) := by
  obtain ⟨g, hg⟩ := rat_ce_sized
  set h : Polynomial ℕ := 10 * (X + 1) ^ 2 * (g.comp IBpoly + 1) with hh
  obtain ⟨k, hk⟩ := poly_bound h
  refine ⟨k, fun x hx => ?_⟩
  obtain ⟨nA, nC, hA, hC, F, hF, rfl⟩ := hx
  set s := (encChores F).length with hs
  obtain ⟨hd, hS, hB, hnC, hnA⟩ := data_le F
  obtain ⟨p, z, hce, hp, hz⟩ := hg nA nC hA hC F hF s hd hS hB
  set K := g.eval (IB nA nC s) with hK
  have hK' : K ≤ g.eval (IB s s s) := poly_eval_mono g (IB_mono hnA hnC le_rfl)
  refine ⟨encCE p z, ⟨nA, nC, hA, hC, F, hF, rfl, p, z, rfl, hce⟩, ?_⟩
  have hl := len_encCE_le p z K hp hz
  have heval : h.eval s = 10 * (s + 1) ^ 2 * (g.eval (IB s s s) + 1) := by
    simp [hh, Polynomial.eval_comp, IBpoly_eval]
  have hbound : (encCE p z).length ≤ h.eval s := by
    rw [heval]
    set K2 := g.eval (IB s s s)
    have e1 : nC * (2 * K + 1) ≤ (s + 1) * (2 * K2 + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e2 : nA * (2 * nC + 1 + nC * (2 * (2 * K) + 1)) ≤
        (s + 1) * (2 * (s + 1) + 1 + (s + 1) * (4 * K2 + 1)) :=
      Nat.mul_le_mul (by omega) (Nat.add_le_add (by omega) (Nat.mul_le_mul (by omega) (by omega)))
    nlinarith [e1, e2]
  exact hbound.trans (hk s)

end LinearChoresCLS.RatCE

open NetworkEquilibriumCLS.LinearNash in
theorem solution : ∃ k : ℕ, TotalSearch (bounded LinearChoresCLS.choresCESearch k) :=
  LinearChoresCLS.RatCE.short_rational_ce
