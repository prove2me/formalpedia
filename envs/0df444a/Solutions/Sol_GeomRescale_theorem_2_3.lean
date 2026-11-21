-- Prove2me | solution 1 for GeomRescale.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:07:12.725312+00:00
-- url     : https://prove2.me/submissions/592222f6-41d3-4c31-8481-c50a282871d1

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_GeomRescale_norm2
import Definitions.Def_GeomRescale_IsMinNormPoint

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

namespace Aux_GeomRescale_theorem_2_3
open GeomRescale

def pref {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => (σ v : ℕ) < i)

def IsSortedBy {n : ℕ} (w : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ u v : Fin n, σ u < σ v → w u ≤ w v

theorem mem_before {n : ℕ} (σ : Equiv.Perm (Fin n)) (u v : Fin n) :
    u ∈ before σ v ↔ σ u < σ v := by
  simp [before]

theorem univ_lower {n : ℕ} (σ : Equiv.Perm (Fin n)) : IsLowerIdeal σ Finset.univ :=
  fun _ _ w _ => Finset.mem_univ w

theorem dimret {n : ℕ} {f : Finset (Fin n) → ℝ} (hsub : Submodular f) {A B : Finset (Fin n)}
    (hAB : A ⊆ B) {v : Fin n} (hv : v ∉ B) :
    f (insert v B) - f B ≤ f (insert v A) - f A := by
  have h := hsub (insert v A) B
  have h1 : insert v A ∪ B = insert v B := by
    ext x
    have := @hAB x
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto
  have h2 : insert v A ∩ B = A := by
    ext x
    have := @hAB x
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨h | h, h'⟩
      · subst h
        exact absurd h' hv
      · exact h
    · intro h
      exact ⟨Or.inr h, this h⟩
  rw [h1, h2] at h
  linarith

theorem xsum_insert {n : ℕ} (x : Fin n → ℝ) {a : Fin n} {s : Finset (Fin n)} (ha : a ∉ s) :
    xsum x (insert a s) = x a + xsum x s := by
  unfold xsum
  rw [Finset.sum_insert ha]

theorem greedy_le {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f)
    (σ : Equiv.Perm (Fin n)) (U : Finset (Fin n)) :
    xsum (greedy f σ) U ≤ f U - f ∅ := by
  induction U using Finset.induction_on_max_value (fun v => σ v) with
  | empty => simp [xsum]
  | insert a s ha hmax ih =>
    have hs : s ⊆ before σ a := by
      intro x hx
      rw [mem_before]
      rcases lt_or_eq_of_le (hmax x hx) with h | h
      · exact h
      · exact absurd (by rw [← σ.injective h]; exact hx) ha
    have hnot : a ∉ before σ a := by
      rw [mem_before]
      exact lt_irrefl _
    have h1 := dimret hsub hs hnot
    rw [xsum_insert _ ha]
    have h3 : greedy f σ a = f (insert a (before σ a)) - f (before σ a) := rfl
    linarith

theorem greedy_eq {n : ℕ} (f : Finset (Fin n) → ℝ) (σ : Equiv.Perm (Fin n))
    (U : Finset (Fin n)) (hU : IsLowerIdeal σ U) : xsum (greedy f σ) U = f U - f ∅ := by
  induction U using Finset.induction_on_max_value (fun v => σ v) with
  | empty => simp [xsum]
  | insert a s ha hmax ih =>
    have hb : before σ a = s := by
      ext x
      rw [mem_before]
      constructor
      · intro h
        have hx := hU a (Finset.mem_insert_self a s) x h
        rcases Finset.mem_insert.mp hx with hx | hx
        · subst hx
          exact absurd h (lt_irrefl _)
        · exact hx
      · intro hx
        rcases lt_or_eq_of_le (hmax x hx) with h | h
        · exact h
        · exact absurd (by rw [← σ.injective h]; exact hx) ha
    have hs : IsLowerIdeal σ s := by
      intro u hu w hw
      have := hU u (Finset.mem_insert_of_mem hu) w hw
      rcases Finset.mem_insert.mp this with h | h
      · subst h
        exact absurd (lt_of_lt_of_le hw (hmax u hu)) (lt_irrefl _)
      · exact h
    rw [xsum_insert _ ha, ih hs]
    show f (insert a (before σ a)) - f (before σ a) + (f s - f ∅) = f (insert a s) - f ∅
    rw [hb]
    ring

theorem greedy_mem {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (σ : Equiv.Perm (Fin n)) : greedy f σ ∈ baseB f := by
  simp only [baseB, Set.mem_setOf_eq]
  refine ⟨fun U => ?_, ?_⟩
  · have := greedy_le f hsub σ U
    linarith
  · have := greedy_eq f σ Finset.univ (univ_lower σ)
    linarith

theorem mem_pref {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : ℕ) (v : Fin n) :
    v ∈ pref σ i ↔ (σ v : ℕ) < i := by
  simp [pref]

theorem pref_zero {n : ℕ} (σ : Equiv.Perm (Fin n)) : pref σ 0 = ∅ := by
  ext v
  simp [pref]

theorem pref_succ {n : ℕ} (σ : Equiv.Perm (Fin n)) {k : ℕ} (hk : k < n) :
    pref σ (k + 1) = insert (σ.symm ⟨k, hk⟩) (pref σ k) := by
  ext v
  rw [Finset.mem_insert, mem_pref, mem_pref]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
    · exact Or.inr h
    · left
      rw [Equiv.eq_symm_apply]
      exact Fin.ext h
  · rintro (h | h)
    · subst h
      simp
    · omega

theorem not_mem_pref {n : ℕ} (σ : Equiv.Perm (Fin n)) {k : ℕ} (hk : k < n) :
    σ.symm ⟨k, hk⟩ ∉ pref σ k := by
  rw [mem_pref]
  simp

theorem pref_le {n : ℕ} (σ : Equiv.Perm (Fin n)) {k : ℕ} (hk : n ≤ k) :
    pref σ k = Finset.univ := by
  ext v
  simp only [mem_pref, Finset.mem_univ, iff_true]
  exact lt_of_lt_of_le (σ v).isLt hk

theorem pref_lower {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) : IsLowerIdeal σ (pref σ k) := by
  intro u hu w hw
  rw [mem_pref] at hu ⊢
  exact lt_trans (Fin.lt_iff_val_lt_val.mp hw) hu

theorem abel (a b : ℕ → ℝ) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), b j * a j =
      ∑ j ∈ Finset.range k, (∑ i ∈ Finset.range (j + 1), a i) * (b j - b (j + 1)) +
        (∑ i ∈ Finset.range (k + 1), a i) * b k := by
  induction k with
  | zero =>
    simp only [zero_add, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    ring
  | succ k ih =>
    rw [Finset.sum_range_succ (fun j => b j * a j) (k + 1), ih]
    simp only [Finset.sum_range_succ]
    ring

noncomputable def seq {N : ℕ} (x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (j : ℕ) : ℝ :=
  if h : j < N then x (σ.symm ⟨j, h⟩) else 0

theorem seq_of_lt {N : ℕ} (x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) {j : ℕ} (h : j < N) :
    seq x σ j = x (σ.symm ⟨j, h⟩) := by
  rw [seq, dif_pos h]

theorem xsum_pref {N : ℕ} (x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    ∀ k, k ≤ N → xsum x (pref σ k) = ∑ j ∈ Finset.range k, seq x σ j
  | 0, _ => by simp [pref_zero, xsum]
  | k + 1, hk => by
    have hk' : k < N := hk
    rw [pref_succ σ hk', Finset.sum_range_succ, ← xsum_pref x σ k (le_of_lt hk'),
      xsum_insert _ (not_mem_pref σ hk'), seq_of_lt x σ hk']
    ring

theorem dot_eq {N : ℕ} (w x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    w ⬝ᵥ x = ∑ j ∈ Finset.range N, seq w σ j * seq x σ j := by
  have h1 : ∑ v, w v * x v = ∑ i, w (σ.symm i) * x (σ.symm i) :=
    (Equiv.sum_comp σ.symm (fun v => w v * x v)).symm
  unfold dotProduct
  rw [h1, ← Fin.sum_univ_eq_sum_range (fun j => seq w σ j * seq x σ j)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [seq_of_lt w σ i.isLt, seq_of_lt x σ i.isLt]

theorem key_abel {m : ℕ} (w x : Fin (m + 1) → ℝ) (σ : Equiv.Perm (Fin (m + 1))) :
    w ⬝ᵥ x = ∑ j ∈ Finset.range m, xsum x (pref σ (j + 1)) * (seq w σ j - seq w σ (j + 1)) +
      xsum x Finset.univ * seq w σ m := by
  rw [dot_eq w x σ, abel]
  congr 1
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    rw [xsum_pref x σ (j + 1) (by omega)]
  · rw [← pref_le σ (le_refl (m + 1)), xsum_pref x σ (m + 1) (le_refl _)]

theorem sorted_step {m : ℕ} (w : Fin (m + 1) → ℝ) (σ : Equiv.Perm (Fin (m + 1)))
    (hσ : IsSortedBy w σ) {j : ℕ} (hj : j < m) : seq w σ j ≤ seq w σ (j + 1) := by
  rw [seq_of_lt w σ (show j < m + 1 by omega), seq_of_lt w σ (show j + 1 < m + 1 by omega)]
  apply hσ
  simp [Fin.lt_iff_val_lt_val]

theorem greedy_min_aux {m : ℕ} (f : Finset (Fin (m + 1)) → ℝ) (hsub : Submodular f)
    (hf0 : f ∅ = 0) (w : Fin (m + 1) → ℝ) (σ : Equiv.Perm (Fin (m + 1)))
    (hσ : IsSortedBy w σ) :
    greedy f σ ∈ baseB f ∧
      (∀ x ∈ baseB f, w ⬝ᵥ greedy f σ ≤ w ⬝ᵥ x) ∧
      w ⬝ᵥ greedy f σ =
        ∑ j ∈ Finset.range m, f (pref σ (j + 1)) * (seq w σ j - seq w σ (j + 1)) +
          f Finset.univ * seq w σ m := by
  have hg : ∀ k, xsum (greedy f σ) (pref σ k) = f (pref σ k) := by
    intro k
    rw [greedy_eq f σ _ (pref_lower σ k), hf0, sub_zero]
  have hgu : xsum (greedy f σ) Finset.univ = f Finset.univ := by
    rw [greedy_eq f σ _ (univ_lower σ), hf0, sub_zero]
  have hform : w ⬝ᵥ greedy f σ =
      ∑ j ∈ Finset.range m, f (pref σ (j + 1)) * (seq w σ j - seq w σ (j + 1)) +
        f Finset.univ * seq w σ m := by
    rw [key_abel w (greedy f σ) σ, hgu]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hg]
  refine ⟨greedy_mem f hsub hf0 σ, ?_, hform⟩
  intro x hx
  simp only [baseB, Set.mem_setOf_eq] at hx
  rw [hform, key_abel w x σ, hx.2]
  have : ∑ j ∈ Finset.range m, f (pref σ (j + 1)) * (seq w σ j - seq w σ (j + 1)) ≤
      ∑ j ∈ Finset.range m, xsum x (pref σ (j + 1)) * (seq w σ j - seq w σ (j + 1)) := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have h1 := sorted_step w σ hσ hj
    exact mul_le_mul_of_nonpos_right (hx.1 _) (by linarith)
  linarith

theorem exists_lower {n : ℕ} (S : Finset (Fin n)) :
    ∃ σ : Equiv.Perm (Fin n), IsLowerIdeal σ S := by
  let w : Fin n → ℝ := fun v => if v ∈ S then (0 : ℝ) else 1
  refine ⟨(Tuple.sort w).symm, fun u hu x hx => ?_⟩
  have hm := Tuple.monotone_sort w (le_of_lt hx)
  have h : w x ≤ w u := by simpa using hm
  simp only [w, hu, if_true] at h
  by_contra hx'
  simp only [hx', if_false] at h
  linarith

theorem xsum_single {n : ℕ} (x : Fin n → ℝ) (v : Fin n) : xsum x {v} = x v := by
  simp [xsum]

theorem xsum_erase {n : ℕ} (x : Fin n → ℝ) (v : Fin n) :
    xsum x (Finset.univ.erase v) = xsum x Finset.univ - x v := by
  unfold xsum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
  ring

noncomputable def abnd {n : ℕ} (f : Finset (Fin n) → ℝ) (v : Fin n) : ℝ :=
  max |f {v}| |f Finset.univ - f (Finset.univ.erase v)|

theorem abs_le_abnd {n : ℕ} (f : Finset (Fin n) → ℝ) {z : Fin n → ℝ} (hz : z ∈ baseB f)
    (v : Fin n) : |z v| ≤ abnd f v := by
  simp only [baseB, Set.mem_setOf_eq] at hz
  have h1 := hz.1 {v}
  have h2 := hz.1 (Finset.univ.erase v)
  rw [xsum_single] at h1
  rw [xsum_erase, hz.2] at h2
  unfold abnd
  rw [abs_le]
  constructor
  · have := neg_abs_le (f Finset.univ - f (Finset.univ.erase v))
    have := le_max_right |f {v}| |f Finset.univ - f (Finset.univ.erase v)|
    linarith
  · have := le_abs_self (f {v})
    have := le_max_left |f {v}| |f Finset.univ - f (Finset.univ.erase v)|
    linarith

theorem baseB_closed {n : ℕ} (f : Finset (Fin n) → ℝ) : IsClosed (baseB f) := by
  have hc : ∀ U : Finset (Fin n), Continuous (fun x : Fin n → ℝ => xsum x U) := by
    intro U
    unfold xsum
    exact continuous_finset_sum _ (fun v _ => continuous_apply v)
  have : baseB f = (⋂ U : Finset (Fin n), {x | xsum x U ≤ f U}) ∩
      {x | xsum x Finset.univ = f Finset.univ} := by
    ext x
    simp [baseB]
  rw [this]
  refine IsClosed.inter (isClosed_iInter (fun U => ?_)) ?_
  · exact isClosed_le (hc U) continuous_const
  · exact isClosed_eq (hc _) continuous_const

theorem baseB_sub_Icc {n : ℕ} (f : Finset (Fin n) → ℝ) :
    baseB f ⊆ Set.Icc (-abnd f) (abnd f) := by
  intro z hz
  constructor
  · intro v
    have := abs_le_abnd f hz v
    have := neg_abs_le (z v)
    simp only [Pi.neg_apply]
    linarith
  · intro v
    have := abs_le_abnd f hz v
    have := le_abs_self (z v)
    linarith

theorem baseB_compact {n : ℕ} (f : Finset (Fin n) → ℝ) : IsCompact (baseB f) :=
  IsCompact.of_isClosed_subset isCompact_Icc (baseB_closed f) (baseB_sub_Icc f)

theorem baseB_nonempty {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0) :
    (baseB f).Nonempty :=
  ⟨greedy f (Equiv.refl _), greedy_mem f hsub hf0 _⟩

theorem greatest_of_cont {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (g : (Fin n → ℝ) → ℝ) (hg : Continuous g) :
    IsGreatest (g '' baseB f) (sSup (g '' baseB f)) :=
  IsCompact.isGreatest_sSup ((baseB_compact f).image hg) ((baseB_nonempty f hsub hf0).image g)

theorem le_sSup_img {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (g : (Fin n → ℝ) → ℝ) (hg : Continuous g) {z : Fin n → ℝ} (hz : z ∈ baseB f) :
    g z ≤ sSup (g '' baseB f) :=
  (greatest_of_cont f hsub hf0 g hg).2 ⟨z, hz, rfl⟩

theorem sSup_img_le {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (g : (Fin n → ℝ) → ℝ) (hg : Continuous g) {c : ℝ} (hc : ∀ z ∈ baseB f, g z ≤ c) :
    sSup (g '' baseB f) ≤ c := by
  obtain ⟨⟨z, hz, hz'⟩, _⟩ := greatest_of_cont f hsub hf0 g hg
  rw [← hz']
  exact hc z hz

theorem exists_sorted {n : ℕ} (w : Fin n → ℝ) : ∃ σ : Equiv.Perm (Fin n), IsSortedBy w σ := by
  refine ⟨(Tuple.sort w).symm, fun u v h => ?_⟩
  have hm := Tuple.monotone_sort w (le_of_lt h)
  simpa using hm

theorem norm2_cont {n : ℕ} : Continuous (fun z : Fin n → ℝ => norm2 z) := by
  unfold norm2
  exact Real.continuous_sqrt.comp
    (continuous_finset_sum _ (fun v _ => (continuous_apply v).pow 2))

theorem norm2_nonneg {n : ℕ} (z : Fin n → ℝ) : 0 ≤ norm2 z := Real.sqrt_nonneg _

theorem norm2_sq {n : ℕ} (z : Fin n → ℝ) : norm2 z ^ 2 = ∑ v, z v ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun v _ => sq_nonneg (z v)))

theorem baseB_convex {n : ℕ} (f : Finset (Fin n) → ℝ) {x y : Fin n → ℝ} (hx : x ∈ baseB f)
    (hy : y ∈ baseB f) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (fun v => x v + t * (y v - x v)) ∈ baseB f := by
  simp only [baseB, Set.mem_setOf_eq] at hx hy ⊢
  have hlin : ∀ U, xsum (fun v => x v + t * (y v - x v)) U =
      (1 - t) * xsum x U + t * xsum y U := by
    intro U
    unfold xsum
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => by ring)
  refine ⟨fun U => ?_, ?_⟩
  · rw [hlin]
    have h1 := mul_le_mul_of_nonneg_left (hx.1 U) (show 0 ≤ 1 - t by linarith)
    have h2 := mul_le_mul_of_nonneg_left (hy.1 U) ht0
    linarith
  · rw [hlin, hx.2, hy.2]
    ring

theorem first_order {n : ℕ} (f : Finset (Fin n) → ℝ) {z : Fin n → ℝ} (hz : IsMinNormPoint f z)
    {x : Fin n → ℝ} (hx : x ∈ baseB f) :
    ∑ v, z v * z v ≤ ∑ v, z v * x v := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨a, ha⟩ : ∃ a, a = ∑ v, z v * (x v - z v) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = ∑ v, (x v - z v) ^ 2 := ⟨_, rfl⟩
  have ha' : a < 0 := by
    have : a = ∑ v, z v * x v - ∑ v, z v * z v := by
      rw [ha, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    linarith
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact Finset.sum_nonneg (fun v _ => sq_nonneg _)
  obtain ⟨t, ht⟩ : ∃ t, t = min 1 (-a / (c + 1)) := ⟨_, rfl⟩
  have ht0 : 0 < t := by
    rw [ht]
    exact lt_min one_pos (div_pos (by linarith) (by linarith))
  have ht1 : t ≤ 1 := by
    rw [ht]
    exact min_le_left _ _
  have htc : t * c < -a := by
    have h1 : t ≤ -a / (c + 1) := by
      rw [ht]
      exact min_le_right _ _
    have h2 : t * c ≤ (-a / (c + 1)) * c := mul_le_mul_of_nonneg_right h1 hc0
    have h3 : (-a / (c + 1)) * c < -a := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  have hy := baseB_convex f hz.1 hx ht0.le ht1
  have hmin := hz.2 _ hy
  rw [norm2_sq, norm2_sq] at hmin
  have hexp : ∑ v, (z v + t * (x v - z v)) ^ 2 = ∑ v, z v ^ 2 + 2 * t * a + t ^ 2 * c := by
    rw [ha, hc, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => by ring)
  rw [hexp] at hmin
  have h4 : 2 * a + t * c < 0 := by linarith
  nlinarith [mul_neg_of_pos_of_neg ht0 h4]

theorem exists_min {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0) :
    ∃ z, IsMinNormPoint f z := by
  obtain ⟨z, hz, hmin⟩ := (baseB_compact f).exists_isMinOn (baseB_nonempty f hsub hf0)
    norm2_cont.continuousOn
  refine ⟨z, hz, fun x hx => ?_⟩
  have h : norm2 z ≤ norm2 x := isMinOn_iff.mp hmin x hx
  have := pow_le_pow_left₀ (norm2_nonneg z) h 2
  linarith

theorem unique_min {n : ℕ} (f : Finset (Fin n) → ℝ) {z1 z2 : Fin n → ℝ}
    (h1 : IsMinNormPoint f z1) (h2 : IsMinNormPoint f z2) : z1 = z2 := by
  have hm := baseB_convex f h1.1 h2.1 (t := 1 / 2) (by norm_num) (by norm_num)
  have a1 := h1.2 _ hm
  have a3 := h2.2 _ h1.1
  rw [norm2_sq, norm2_sq] at a1 a3
  have key : ∀ v, (z1 v - z2 v) ^ 2 =
      2 * z1 v ^ 2 + 2 * z2 v ^ 2 - 4 * (z1 v + 1 / 2 * (z2 v - z1 v)) ^ 2 := by
    intro v
    ring
  have hd : ∑ v, (z1 v - z2 v) ^ 2 ≤ 0 := by
    rw [Finset.sum_congr rfl (fun v _ => key v), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    linarith
  have hd0 := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => sq_nonneg (z1 v - z2 v))).mp
    (le_antisymm hd (Finset.sum_nonneg (fun v _ => sq_nonneg _)))
  funext v
  have h3 := hd0 v (Finset.mem_univ v)
  have h4 : z1 v - z2 v = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp h3
  linarith

theorem card_pref {n : ℕ} (σ : Equiv.Perm (Fin n)) : ∀ k, k ≤ n → (pref σ k).card = k
  | 0, _ => by simp [pref_zero]
  | k + 1, hk => by
    rw [pref_succ σ hk, Finset.card_insert_of_notMem (not_mem_pref σ hk),
      card_pref σ k (by omega)]

theorem lower_eq_pref {n : ℕ} (σ : Equiv.Perm (Fin n)) (U : Finset (Fin n))
    (hU : IsLowerIdeal σ U) : U = pref σ U.card := by
  ext v
  rw [mem_pref]
  constructor
  · intro hv
    have hsub : pref σ ((σ v : ℕ) + 1) ⊆ U := by
      intro u hu
      rw [mem_pref] at hu
      rcases Nat.lt_succ_iff_lt_or_eq.mp hu with h | h
      · exact hU v hv u (Fin.lt_iff_val_lt_val.mpr h)
      · have : u = v := σ.injective (Fin.ext h)
        rw [this]
        exact hv
    have := Finset.card_le_card hsub
    rw [card_pref σ ((σ v : ℕ) + 1) (Nat.succ_le_of_lt (σ v).isLt)] at this
    omega
  · intro hv
    by_contra hvU
    have hsub : U ⊆ pref σ (σ v) := by
      intro u hu
      rw [mem_pref]
      rcases lt_trichotomy (σ u) (σ v) with h | h | h
      · exact h
      · exact absurd (by rw [← σ.injective h]; exact hu) hvU
      · exact absurd (hU u hu v h) hvU
    have := Finset.card_le_card hsub
    rw [card_pref σ (σ v : ℕ) (le_of_lt (σ v).isLt)] at this
    omega

theorem tight {m : ℕ} (f : Finset (Fin (m + 1)) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    {z : Fin (m + 1) → ℝ} (hz : IsMinNormPoint f z) :
    xsum z (Finset.univ.filter (fun v => z v < 0)) =
      f (Finset.univ.filter (fun v => z v < 0)) := by
  obtain ⟨σ, hσ⟩ := exists_sorted z
  have hSl : IsLowerIdeal σ (Finset.univ.filter (fun v => z v < 0)) := by
    intro u hu w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact lt_of_le_of_lt (hσ w u hw) hu
  have hSk := lower_eq_pref σ _ hSl
  have hcard : (Finset.univ.filter (fun v => z v < 0)).card ≤ m + 1 := by
    have := Finset.card_le_univ (Finset.univ.filter (fun v => z v < 0))
    simpa using this
  obtain ⟨k, hk⟩ : ∃ k, k = (Finset.univ.filter (fun v => z v < 0)).card := ⟨_, rfl⟩
  rw [← hk] at hSk hcard
  rw [hSk]
  have hzB := hz.1
  simp only [baseB, Set.mem_setOf_eq] at hzB
  have hg := greedy_mem f hsub hf0 σ
  have hfo := first_order f hz hg
  have e1 := key_abel z z σ
  have e2 := key_abel z (greedy f σ) σ
  have hgp : ∀ j, xsum (greedy f σ) (pref σ j) = f (pref σ j) := fun j => by
    rw [greedy_eq f σ _ (pref_lower σ j), hf0, sub_zero]
  have hgu : xsum (greedy f σ) Finset.univ = f Finset.univ := by
    rw [greedy_eq f σ _ (univ_lower σ), hf0, sub_zero]
  have hdz : z ⬝ᵥ z = ∑ v, z v * z v := rfl
  have hdg : z ⬝ᵥ greedy f σ = ∑ v, z v * greedy f σ v := rfl
  have hD : ∀ j ∈ Finset.range m, 0 ≤ (xsum z (pref σ (j + 1)) - f (pref σ (j + 1))) *
      (seq z σ j - seq z σ (j + 1)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have h1 := sorted_step z σ hσ hj
    have h2 := hzB.1 (pref σ (j + 1))
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hsum : ∑ j ∈ Finset.range m, (xsum z (pref σ (j + 1)) - f (pref σ (j + 1))) *
      (seq z σ j - seq z σ (j + 1)) = z ⬝ᵥ z - z ⬝ᵥ greedy f σ := by
    rw [e1, e2, hgu, hzB.2]
    rw [show ∀ a b c : ℝ, a + c - (b + c) = a - b from fun a b c => by ring,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hgp]
    ring
  have hle : ∑ j ∈ Finset.range m, (xsum z (pref σ (j + 1)) - f (pref σ (j + 1))) *
      (seq z σ j - seq z σ (j + 1)) ≤ 0 := by
    rw [hsum, hdz, hdg]
    linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hD).mp (le_antisymm hle (Finset.sum_nonneg hD))
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0, pref_zero, hf0]
    simp [xsum]
  rcases Nat.lt_or_ge k (m + 1) with hlt | hge
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hj : j < m := by omega
    have h0 := hzero j (Finset.mem_range.mpr hj)
    have hneg : seq z σ j < 0 := by
      rw [seq_of_lt z σ (show j < m + 1 by omega)]
      have hmem : σ.symm ⟨j, by omega⟩ ∈ pref σ (j + 1) := by
        rw [mem_pref]
        simp
      rw [← hSk] at hmem
      simpa using hmem
    have hnn : 0 ≤ seq z σ (j + 1) := by
      rw [seq_of_lt z σ (show j + 1 < m + 1 by omega)]
      have hmem : σ.symm ⟨j + 1, by omega⟩ ∉ pref σ (j + 1) := not_mem_pref σ (by omega)
      rw [← hSk] at hmem
      simpa using hmem
    rcases mul_eq_zero.mp h0 with h | h
    · linarith
    · linarith
  · have hk' : k = m + 1 := by omega
    rw [hk', pref_le σ (le_refl _)]
    exact hzB.2

theorem tight_all {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    {z : Fin n → ℝ} (hz : IsMinNormPoint f z) :
    xsum z (Finset.univ.filter (fun v => z v < 0)) =
      f (Finset.univ.filter (fun v => z v < 0)) := by
  rcases n with _ | m
  · have h : Finset.univ.filter (fun v : Fin 0 => z v < 0) = ∅ := by
      ext v
      exact v.elim0
    rw [h, hf0]
    simp [xsum]
  · exact tight f hsub hf0 hz

theorem l1_le_sqrt {n : ℕ} (z : Fin n → ℝ) : ∑ v, |z v| ≤ √(n : ℝ) * norm2 z := by
  unfold norm2
  rw [← Real.sqrt_mul (Nat.cast_nonneg n)]
  apply Real.le_sqrt_of_sq_le
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun v => |z v|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sq_abs] at h
  exact h

theorem abs_min_le (a : ℝ) : |min 0 a| ≤ |a| := by
  rcases le_or_gt 0 a with h | h
  · rw [min_eq_left h, abs_zero]
    exact abs_nonneg a
  · rw [min_eq_right h.le]

end Aux_GeomRescale_theorem_2_3

open GeomRescale Aux_GeomRescale_theorem_2_3 in
theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0) :
    (∃! z, IsMinNormPoint f z) ∧
      ∀ z, IsMinNormPoint f z →
        let Sstar : Finset (Fin n) := Finset.univ.filter (fun v => z v < 0)
        (∀ T, f Sstar ≤ f T) ∧
          (∀ T, (∀ U, f T ≤ f U) → Sstar ⊆ T) ∧
          f Sstar = ∑ v, min 0 (z v) ∧
          |f Sstar| ≤ √(n : ℝ) * norm2 z := by
  refine ⟨?_, ?_⟩
  · obtain ⟨z, hz⟩ := exists_min f hsub hf0
    exact ⟨z, hz, fun y hy => unique_min f hy hz⟩
  intro z hz
  have htight := tight_all f hsub hf0 hz
  have hms : xsum z (Finset.univ.filter (fun v => z v < 0)) = ∑ v, min 0 (z v) := by
    show ∑ v ∈ Finset.univ.filter (fun v => z v < 0), z v = _
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    split_ifs with h
    · exact (min_eq_right h.le).symm
    · exact (min_eq_left (not_lt.mp h)).symm
  have hlow : ∀ T : Finset (Fin n), ∑ v, min 0 (z v) ≤ ∑ v ∈ T, min 0 (z v) := by
    intro T
    have hsd : ∑ v ∈ Finset.univ \ T, min 0 (z v) + ∑ v ∈ T, min 0 (z v) =
        ∑ v, min 0 (z v) := Finset.sum_sdiff (Finset.subset_univ T)
    have : ∑ v ∈ Finset.univ \ T, min 0 (z v) ≤ 0 :=
      Finset.sum_nonpos (fun v _ => min_le_left _ _)
    linarith
  have hT : ∀ T : Finset (Fin n), ∑ v ∈ T, min 0 (z v) ≤ xsum z T := fun T =>
    Finset.sum_le_sum (fun v _ => min_le_right _ _)
  have hzB := hz.1
  simp only [baseB, Set.mem_setOf_eq] at hzB
  intro Sstar
  refine ⟨fun T => ?_, fun T hTmin => ?_, ?_, ?_⟩
  · have h1 := hzB.1 T
    have h2 := hlow T
    have h3 := hT T
    show f (Finset.univ.filter (fun v => z v < 0)) ≤ f T
    linarith
  · intro v hv
    by_contra hvT
    have h1 := hTmin (Finset.univ.filter (fun v => z v < 0))
    have h2 := hzB.1 T
    have h3 := hT T
    have hsd : ∑ v ∈ Finset.univ \ T, min 0 (z v) + ∑ v ∈ T, min 0 (z v) =
        ∑ v, min 0 (z v) := Finset.sum_sdiff (Finset.subset_univ T)
    have h4 : ∑ v ∈ Finset.univ \ T, min 0 (z v) = 0 := by
      have : ∑ v ∈ Finset.univ \ T, min 0 (z v) ≤ 0 :=
        Finset.sum_nonpos (fun v _ => min_le_left _ _)
      linarith
    have h5 := (Finset.sum_eq_zero_iff_of_nonpos (fun v _ => min_le_left 0 (z v))).mp h4 v
      (by simp [hvT])
    have hv' : z v < 0 := by
      have hv2 : v ∈ Finset.univ.filter (fun v => z v < 0) := hv
      simpa using hv2
    rw [min_eq_right hv'.le] at h5
    linarith
  · show f (Finset.univ.filter (fun v => z v < 0)) = ∑ v, min 0 (z v)
    rw [← htight, hms]
  · show |f (Finset.univ.filter (fun v => z v < 0))| ≤ √(n : ℝ) * norm2 z
    rw [← htight, hms]
    calc |∑ v, min 0 (z v)| ≤ ∑ v, |min 0 (z v)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ v, |z v| := Finset.sum_le_sum (fun v _ => abs_min_le (z v))
      _ ≤ √(n : ℝ) * norm2 z := l1_le_sqrt z

