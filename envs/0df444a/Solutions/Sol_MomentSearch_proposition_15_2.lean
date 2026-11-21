-- Prove2me | solution 2 for MomentSearch.proposition_15
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T00:48:33.701178+00:00
-- url     : https://prove2.me/submissions/7d21e8ef-8645-4775-8933-014c32798f07

import Mathlib
import Definitions.Def_MomentSearch_moment
import Theorems.Thm_MomentSearch_proposition_10

open MomentSearch

set_option maxHeartbeats 800000 in
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      (∀ n k : ℕ, 3 ≤ n → 1 ≤ k → (k : ℝ) ≤ ((n : ℝ) - 1) / 2 →
        ∀ m m₀ : Fin n,
          ((n : ℝ) - 1) / 4 ≤ ((m : ℕ) : ℝ) → ((m : ℕ) : ℝ) ≤ 3 * ((n : ℝ) - 1) / 4 →
          ((n : ℝ) - 1) / 4 ≤ ((m₀ : ℕ) : ℝ) → ((m₀ : ℕ) : ℝ) ≤ 3 * ((n : ℝ) - 1) / 4 →
          ∃ p p' : Fin n → ℝ, ∃ γ : ℝ,
            p ∈ stdSimplex ℝ (Fin n) ∧ p' ∈ stdSimplex ℝ (Fin n) ∧
            γ ≤ C * ((k : ℝ) / ((n : ℝ) - 1)) * |((m : ℕ) : ℝ) - ((m₀ : ℕ) : ℝ)| ∧
            1 - γ ≤ p m ∧ 1 - γ ≤ p' m₀ ∧
            ∀ i : ℕ, i ≤ k → moment p i = moment p' i) ∧
      (∀ n k : ℕ, 3 ≤ n → 1 ≤ k → (k : ℝ) ≤ ((n : ℝ) - 1) / 2 →
        ∀ (R : ℕ) (m : ℕ → Fin n),
          (∀ r : ℕ, r ≤ R → ((n : ℝ) - 1) / 4 ≤ ((m r : ℕ) : ℝ) ∧
            ((m r : ℕ) : ℝ) ≤ 3 * ((n : ℝ) - 1) / 4) →
          ∃ p : ℕ → Fin n → ℝ, ∃ γ : ℝ,
            (∀ r : ℕ, r ≤ R → p r ∈ stdSimplex ℝ (Fin n)) ∧
            (∀ r : ℕ, r ≤ R → ∀ i : ℕ, i ≤ k → moment (p r) i = moment (p 0) i) ∧
            γ ≤ C * ((k : ℝ) / ((n : ℝ) - 1)) *
              ∑ s ∈ Finset.Icc 1 R, |((m s : ℕ) : ℝ) - ((m 0 : ℕ) : ℝ)| ∧
            ∀ r : ℕ, r ≤ R → 1 - γ ≤ p r (m r)) := by
  classical
  obtain ⟨C,hC,pair⟩ := MomentSearch.proposition_10
  refine ⟨2*C,by positivity,?_,?_⟩
  · intro n k hn hk hkn m b hm1 hm2 hb1 hb2
    obtain ⟨p,q,γ,hp,hq,hγ,hpm,hqb,hmatch⟩ := pair n k hn hk hkn m b hm1 hm2 hb1 hb2
    refine ⟨p,q,γ,hp,hq,hγ.trans ?_,hpm,hqb,hmatch⟩
    have hnon : 0 ≤ ((k:ℝ)/((n:ℝ)-1)) * |((m:ℕ):ℝ)-((b:ℕ):ℝ)| := by
      have hn' : (3:ℝ) ≤ n := by exact_mod_cast hn
      exact mul_nonneg (div_nonneg (by positivity) (by linarith)) (abs_nonneg _)
    nlinarith [mul_nonneg hC.le hnon]
  intro n k hn hk hkn R m hm
  let M := fun s : ℕ => if s ≤ R then m s else m 0
  have center (s : ℕ) : ((n:ℝ)-1)/4 ≤ ((M s:ℕ):ℝ) ∧
      ((M s:ℕ):ℝ) ≤ 3*((n:ℝ)-1)/4 := by
    by_cases h : s ≤ R
    · simpa [M,h] using hm s h
    · simpa [M,h] using hm 0 (Nat.zero_le _)
  have ex (s : ℕ) := pair n k hn hk hkn (M s) (m 0)
    (center s).1 (center s).2 (hm 0 (Nat.zero_le _)).1 (hm 0 (Nat.zero_le _)).2
  choose p q γ hp hq hγ hpm hqm hmatch using ex
  let δ := fun x t : Fin n => if t=x then (1:ℝ) else 0
  have pnon (s : ℕ) (t : Fin n) : 0 ≤ p s t := (hp s).1 t
  have qnon (s : ℕ) (t : Fin n) : 0 ≤ q s t := (hq s).1 t
  have pone (s : ℕ) (t : Fin n) : p s t ≤ 1 := (hp s).2 ▸
    Finset.single_le_sum (fun u _ => pnon s u) (Finset.mem_univ t)
  have qone (s : ℕ) (t : Fin n) : q s t ≤ 1 := (hq s).2 ▸
    Finset.single_le_sum (fun u _ => qnon s u) (Finset.mem_univ t)
  let L := fun s t => (if t=m 0 then 0 else q s t) + (1-p s (M s))*δ (M s) t
  let D := fun s t => (if t=M s then 0 else p s t) + (1-q s (m 0))*δ (m 0) t
  have δnon (x t : Fin n) : 0 ≤ δ x t := by dsimp [δ]; split <;> norm_num
  have Lnon (s : ℕ) (t : Fin n) : 0 ≤ L s t := by
    dsimp [L]; apply add_nonneg (by split <;> simp [qnon])
    exact mul_nonneg (sub_nonneg.mpr (pone s _)) (δnon _ _)
  have Dnon (s : ℕ) (t : Fin n) : 0 ≤ D s t := by
    dsimp [D]; apply add_nonneg (by split <;> simp [pnon])
    exact mul_nonneg (sub_nonneg.mpr (qone s _)) (δnon _ _)
  have Lform (s : ℕ) (t : Fin n) :
      L s t = q s t - q s (m 0) * δ (m 0) t + (1-p s (M s))*δ (M s) t := by
    by_cases h : t=m 0
    · subst t; simp [L,δ]
    · simp [L,δ,h]
  have Dform (s : ℕ) (t : Fin n) :
      D s t = p s t - p s (M s) * δ (M s) t + (1-q s (m 0))*δ (m 0) t := by
    by_cases h : t=M s
    · subst t; simp [D,δ]
    · simp [D,δ,h]
  have Lmass (s : ℕ) : (∑ t, L s t) = 2-p s (M s)-q s (m 0) := by
    simp_rw [Lform,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
    have sm (x : Fin n) : ∑ t, δ x t = 1 := by simp [δ]
    rw [(hq s).2,sm,sm]
    ring
  have swap (s : ℕ) (i : ℕ) (hi : i ≤ k) :
      moment (δ (M s)) i + moment (D s) i = moment (δ (m 0)) i + moment (L s) i := by
    have identity (t : Fin n) :
        (δ (M s) t + D s t) - (δ (m 0) t + L s t) = p s t-q s t := by
      rw [Lform,Dform]; ring
    have e := congrArg (fun f : Fin n → ℝ => moment f i) (funext identity)
    simp only [moment,add_mul,sub_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib] at e
    have v := hmatch s i hi
    unfold moment at v ⊢
    linarith
  let S := Finset.Icc 1 R
  let B := fun t : Fin n => ∑ s ∈ S, L s t
  let b := ∑ t, B t
  have bnon : 0 ≤ b := Finset.sum_nonneg (fun t _ => Finset.sum_nonneg (fun s _ => Lnon s t))
  let Z := 1+b
  have hz : 0 < Z := by dsimp [Z]; linarith
  let P := fun r t => δ (m r) t + if r ∈ S then D r t + ∑ s ∈ S.erase r, L s t else B t
  have inside (r : ℕ) (hr : r ∈ S) : M r = m r := by
    simp [M,(Finset.mem_Icc.mp hr).2]
  have balance (r i : ℕ) (hr : r ≤ R) (hi : i ≤ k) :
      moment (P r) i = moment (P 0) i := by
    by_cases h : r ∈ S
    · let H := fun t : Fin n => ∑ s ∈ S.erase r, L s t
      have er (t : Fin n) : L r t + H t = B t := by
        simpa [H,B,add_comm] using Finset.sum_erase_add _ (fun s => L s t) h
      have E0 : P 0 = fun t => δ (m 0) t + (L r t + H t) := by
        funext t
        have hzS : 0 ∉ S := by simp [S]
        simp only [P,if_neg hzS,er]
      have Er : P r = fun t => δ (M r) t + (D r t + H t) := by
        funext t
        simp [P,h,H,inside _ h]
      rw [E0,Er]
      simp only [moment,add_mul,Finset.sum_add_distrib]
      have q := swap r i hi
      unfold moment at q
      linarith
    · have zr : r = 0 := by
        have hr' : ¬ (1 ≤ r ∧ r ≤ R) := by simpa [S] using h
        omega
      subst r; rfl
  let out := fun r t => P r t / Z
  have hpsum : ∀ r ≤ R, ∑ t, P r t = Z := by
    intro r hr
    have eq := balance r 0 hr (Nat.zero_le _)
    simp only [moment,pow_zero,mul_one] at eq
    rw [eq]
    have hzS : 0 ∉ S := by simp [S]
    have sm : (∑ t, δ (m 0) t) = 1 := by simp [δ]
    simp [P,if_neg hzS,Finset.sum_add_distrib,sm,Z,b]
  refine ⟨out,b,?_,?_,?_,?_⟩
  · intro r hr
    constructor
    · intro t
      apply div_nonneg _ hz.le
      dsimp [P]
      apply add_nonneg (δnon _ _)
      split
      · exact add_nonneg (Dnon _ _) (Finset.sum_nonneg (fun s _ => Lnon s t))
      · exact Finset.sum_nonneg (fun s _ => Lnon s t)
    · dsimp [out]; rw [← Finset.sum_div,hpsum r hr,div_self hz.ne']
  · intro r hr i hi
    simpa only [moment,out,div_mul_eq_mul_div,← Finset.sum_div] using
      congrArg (fun v : ℝ => v / Z) (balance r i hr hi)
  · dsimp [b,B]
    rw [Finset.sum_comm]
    calc
      (∑ s ∈ S, ∑ t, L s t) ≤ ∑ s ∈ S, 2*(C*((k:ℝ)/((n:ℝ)-1)) *
          |((m s:ℕ):ℝ)-((m 0:ℕ):ℝ)|) := by
        apply Finset.sum_le_sum
        intro s hs
        rw [Lmass]
        have e := hγ s
        rw [inside _ hs] at e
        linarith [hpm s,hqm s]
      _ = _ := by simp_rw [mul_assoc,← Finset.mul_sum]; rfl
  · intro r _hr
    have hP : 1 ≤ P r (m r) := by
      dsimp [P,δ]
      rw [if_pos rfl]
      by_cases hrS : r ∈ S
      · rw [if_pos hrS]
        exact le_add_of_nonneg_right (add_nonneg (Dnon _ _) (Finset.sum_nonneg (fun s _ => Lnon s _)))
      · rw [if_neg hrS]
        exact le_add_of_nonneg_right (Finset.sum_nonneg (fun s _ => Lnon s _))
    apply le_trans _ (div_le_div_of_nonneg_right hP hz.le)
    apply (le_div_iff₀ hz).mpr
    dsimp [Z]
    nlinarith [sq_nonneg b]
