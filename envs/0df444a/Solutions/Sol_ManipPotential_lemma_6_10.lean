-- Prove2me | solution 1 for ManipPotential.lemma_6_10
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:42:24.687588+00:00
-- url     : https://prove2.me/submissions/7bf6ef7f-5d3c-4c67-b81f-b6272fc5c34e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_IsCommonJunction
import Definitions.Def_ManipPotential_cycL
import Definitions.Def_ManipPotential_supp
import Definitions.Def_ManipPotential_kappa
import Theorems.Thm_ManipPotential_lemma_6_3
import Theorems.Thm_ManipPotential_lemma_6_10_uniform_threshold

open ManipPotential

private lemma ell_injective_610 {m : ℕ} [NeZero m] :
    Function.Injective (@ell m _) := by
  intro a b h
  have h0 := congrArg (fun r : Ranking m => r 0) h
  simpa [ell, Ranking] using h0

private lemma cycL_apply_self_real {m : ℕ} [NeZero m] (x : Fin m → ℝ) (i : Fin m) :
    cycL x (ell i) = x i := by
  classical
  simp only [cycL, Finset.sum_apply, Pi.smul_apply, unitVec, Pi.single_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hbi
    have h : ell i ≠ ell b := fun h => hbi (ell_injective_610 h.symm)
    simp [h]
  · simp

private lemma cycL_apply_of_not_mem_range_real {m : ℕ} [NeZero m] (x : Fin m → ℝ)
    (r : Ranking m) (hr : r ∉ Set.range (@ell m _)) : cycL x r = 0 := by
  classical
  simp only [cycL, Finset.sum_apply, Pi.smul_apply, unitVec, Pi.single_apply,
    smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  have h : r ≠ ell i := fun h => hr ⟨i, h.symm⟩
  simp [h]

private lemma cycL_sub_real {m : ℕ} [NeZero m] (x y : Fin m → ℝ) :
    cycL (x - y) = cycL x - cycL y := by
  simp only [cycL, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

private lemma cast_cycL {m : ℕ} [NeZero m] (x : Fin m → ℚ) :
    (fun r => ((cycL x r : ℚ) : ℝ)) = cycL (fun j => (x j : ℝ)) := by
  classical
  funext r
  simp only [cycL, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Rat.cast_sum,
    Rat.cast_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : r = ell i
  · simp [unitVec, Pi.single_apply, h]
  · simp [unitVec, Pi.single_apply, h]

private lemma norm_cycL_sub_le {m : ℕ} [NeZero m] (x y : Fin m → ℝ) {d : ℝ}
    (hd : 0 ≤ d) (h : ∀ j, |x j - y j| ≤ d) :
    ‖cycL (x - y)‖ ≤ (m : ℝ) * d := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne m))
  have hdm : d ≤ (m : ℝ) * d := by nlinarith
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg m) hd)]
  intro r
  by_cases hr : r ∈ Set.range (@ell m _)
  · obtain ⟨i, rfl⟩ := hr
    rw [cycL_apply_self_real]
    exact (by simpa only [Pi.sub_apply, Real.norm_eq_abs] using (h i).trans hdm)
  · rw [cycL_apply_of_not_mem_range_real _ _ hr]
    simp only [norm_zero]
    exact mul_nonneg (Nat.cast_nonneg m) hd

theorem solution {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) (P : Ranking m → ℝ) (hP : IsCommonJunction g P) (ε : ℝ) (hε : 0 < ε)
    (hεP : ε < (1 / 2) * Finset.univ.inf' Finset.univ_nonempty P)
    (v : Fin m → ℝ) (hv : 0 ≤ v) (hS : (supp v).Nonempty) (hS' : supp v ≠ Finset.univ)
    (hvκ : kappa m K * ε < ∑ j, v j) (Q : Ranking m → ℚ)
    (hQ : ‖(fun r => (Q r : ℝ)) - (P - (fun _ => ε) + cycL v)‖ < ε / 4) :
    g Q ∈ supp v := by
  classical
  let D : ℝ := ‖(fun r => (Q r : ℝ)) - (P - (fun _ => ε) + cycL v)‖
  let A : ℝ := (∑ j, v j) - kappa m K * ε
  let B : ℝ := ε / 4 - D
  have hA : 0 < A := by dsimp [A]; linarith
  have hB : 0 < B := by dsimp [B, D]; linarith
  let d : ℝ := min (A / ((m : ℝ) + 1)) (B / ((m : ℝ) + 1)) / 2
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hdA : d < A / ((m : ℝ) + 1) := by
    have hp : 0 < A / ((m : ℝ) + 1) := by positivity
    have hm₀ : 0 < B / ((m : ℝ) + 1) := by positivity
    dsimp [d]
    exact lt_of_lt_of_le (half_lt_self (lt_min hp hm₀)) (min_le_left _ _)
  have hdB : d < B / ((m : ℝ) + 1) := by
    have hp : 0 < A / ((m : ℝ) + 1) := by positivity
    have hm₀ : 0 < B / ((m : ℝ) + 1) := by positivity
    dsimp [d]
    exact lt_of_lt_of_le (half_lt_self (lt_min hp hm₀)) (min_le_right _ _)
  have hmdA : (m : ℝ) * d < A := by
    have h := (lt_div_iff₀ (show 0 < (m : ℝ) + 1 by positivity)).mp hdA
    nlinarith
  have hmdB : (m : ℝ) * d < B := by
    have h := (lt_div_iff₀ (show 0 < (m : ℝ) + 1 by positivity)).mp hdB
    nlinarith
  have hex : ∀ j, ∃ q : ℚ,
      (v j = 0 → q = 0) ∧
      (0 < v j → 0 < (q : ℝ) ∧ v j - d < (q : ℝ) ∧ (q : ℝ) < v j + d) := by
    intro j
    by_cases hj : 0 < v j
    · have hab : max (v j - d) (v j / 2) < v j + d := by
        apply max_lt <;> linarith
      obtain ⟨q, hlq, hqu⟩ := exists_rat_btwn hab
      refine ⟨q, ?_, ?_⟩
      · intro hz
        linarith
      · intro _
        have hlow : v j - d < (q : ℝ) := lt_of_le_of_lt (le_max_left _ _) hlq
        have hhalf : v j / 2 < (q : ℝ) := lt_of_le_of_lt (le_max_right _ _) hlq
        exact ⟨by linarith, hlow, hqu⟩
    · have hj0 : v j = 0 := le_antisymm (le_of_not_gt hj) (hv j)
      exact ⟨0, fun _ => rfl, fun h => (hj h).elim⟩
  choose q hq0 hqpos using hex
  let w : Fin m → ℝ := fun j => (q j : ℝ)
  have hqw : ∀ j, |v j - w j| < d := by
    intro j
    by_cases hj : 0 < v j
    · obtain ⟨hqjp, hjl, hju⟩ := hqpos j hj
      rw [abs_lt]
      constructor <;> dsimp [w] <;> linarith
    · have hj0 : v j = 0 := le_antisymm (le_of_not_gt hj) (hv j)
      have hqz : q j = 0 := hq0 j hj0
      simp [hj0, hqz, w, hd]
  have hsumw : kappa m K * ε < ∑ j, w j := by
    have hlt : (∑ j, (v j - d)) < ∑ j, w j := by
      apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      intro j _
      have h := hqw j
      rw [abs_lt] at h
      linarith [h.1]
    have hlt' : (∑ j, v j) - (m : ℝ) * d < ∑ j, w j := by
      simpa [Finset.sum_sub_distrib] using hlt
    dsimp [A] at hmdA
    dsimp [w]
    linarith
  have hsupport : supp q = supp v := by
    ext j
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hqj
      by_contra hvj
      have hvj0 : v j = 0 := le_antisymm (le_of_not_gt hvj) (hv j)
      have hqz : q j = 0 := hq0 j hvj0
      rw [hqz] at hqj
      exact (lt_irrefl 0 hqj)
    · intro hvj
      have h := (hqpos j hvj).1
      exact_mod_cast h
  have hnorm : ‖cycL (v - w)‖ ≤ (m : ℝ) * d := by
    apply norm_cycL_sub_le _ _ hd.le
    intro j
    exact (hqw j).le
  have hQw : ‖(fun r => (Q r : ℝ)) - (P - (fun _ => ε) + cycL w)‖ < ε / 4 := by
    have hdecomp :
        (fun r => (Q r : ℝ)) - (P - (fun _ => ε) + cycL w) =
          ((fun r => (Q r : ℝ)) - (P - (fun _ => ε) + cycL v)) + cycL (v - w) := by
      rw [cycL_sub_real]
      abel
    rw [hdecomp]
    have htri := norm_add_le
      ((fun r => (Q r : ℝ)) - (P - (fun _ => ε) + cycL v)) (cycL (v - w))
    dsimp [B, D] at hmdB
    change D < ε / 4 at hQ
    linarith
  let Z : Ranking m → ℚ := Q - cycL q
  have hcastZ : (fun r => (Z r : ℝ)) =
      (fun r => (Q r : ℝ)) - cycL w := by
    rw [← cast_cycL]
    funext r
    simp [Z, w]
  have hZP : ‖(fun r => (Z r : ℝ)) - (P - (fun _ => ε))‖ < ε / 4 := by
    rw [hcastZ]
    convert hQw using 1 <;> abel
  have hZ : ∀ r, 0 < Z r := by
    intro r
    have hPr : 2 * ε < P r := by
      have hinf : Finset.univ.inf' Finset.univ_nonempty P ≤ P r :=
        Finset.inf'_le (fun r => P r) (Finset.mem_univ r)
      linarith
    have hn := norm_le_pi_norm
      ((fun r => (Z r : ℝ)) - (P - (fun _ => ε))) r
    have habs : |(Z r : ℝ) - (P r - ε)| < ε / 4 := by
      have h : |(Z r : ℝ) - (P r - ε)| ≤
          ‖(fun r => (Z r : ℝ)) - (P - (fun _ => ε))‖ := by
        simpa only [Pi.sub_apply, Real.norm_eq_abs] using hn
      linarith
    rw [abs_lt] at habs
    have hz : 0 < (Z r : ℝ) := by linarith [habs.1]
    exact_mod_cast hz
  obtain ⟨u₀, hu₀, hu₀bound, hwin⟩ :=
    lemma_6_10_uniform_threshold hm K g hg P hP ε hε hεP Z hZ hZP
  have hqnonneg : 0 ≤ q := by
    intro j
    have h : 0 ≤ (q j : ℝ) := by
      by_cases hj : 0 < v j
      · exact (hqpos j hj).1.le
      · have hj0 : v j = 0 := le_antisymm (le_of_not_gt hj) (hv j)
        simp [hq0 j hj0]
    exact_mod_cast h
  have hqne : q ≠ 0 := by
    intro hqz
    obtain ⟨j, hj⟩ := hS
    have hj' : j ∈ supp q := by rwa [hsupport]
    have hp : 0 < q j := by simpa [supp] using hj'
    rw [hqz] at hp
    simp at hp
  have hlam : (1 : ℝ) ≤ (K : ℝ) + 1 := by norm_num
  have hcard1 : 1 ≤ (supp q).card := Finset.card_pos.mpr (hsupport ▸ hS)
  have hcardm : (supp q).card ≤ m := by
    simpa using Finset.card_le_card (Finset.subset_univ (supp q))
  have hpow : ((K : ℝ) + 1) ^ (supp q).card ≤ ((K : ℝ) + 1) ^ m := by
    exact pow_le_pow_right₀ hlam hcardm
  have hmul : ((K : ℝ) + 1) ^ ((supp q).card - 1) * (u₀ : ℝ) < ∑ j, w j := by
    have hfac : 0 < ((K : ℝ) + 1) ^ ((supp q).card - 1) := by positivity
    have hpoweq : ((K : ℝ) + 1) ^ ((supp q).card - 1) * ((K : ℝ) + 1) =
        ((K : ℝ) + 1) ^ (supp q).card := by
      rw [← pow_succ]
      congr 1
      omega
    calc
      ((K : ℝ) + 1) ^ ((supp q).card - 1) * (u₀ : ℝ) <
          ((K : ℝ) + 1) ^ ((supp q).card - 1) *
            (2 * ((K : ℝ) + 1) * (m.factorial : ℝ) * ε) := by
              exact mul_lt_mul_of_pos_left hu₀bound hfac
      _ = 2 * (m.factorial : ℝ) *
          (((K : ℝ) + 1) ^ ((supp q).card - 1) * ((K : ℝ) + 1)) * ε := by ring
      _ = 2 * (m.factorial : ℝ) * ((K : ℝ) + 1) ^ (supp q).card * ε := by rw [hpoweq]
      _ ≤ 2 * (m.factorial : ℝ) * ((K : ℝ) + 1) ^ m * ε := by
        have hc : 0 ≤ 2 * (m.factorial : ℝ) * ε := by positivity
        nlinarith
      _ = kappa m K * ε := by simp only [kappa]
      _ < ∑ j, w j := hsumw
  have hmulq : ((K : ℚ) + 1) ^ ((supp q).card - 1) * u₀ < ∑ j, q j := by
    change ((K : ℝ) + 1) ^ ((supp q).card - 1) * (u₀ : ℝ) < ∑ j, (q j : ℝ) at hmul
    exact_mod_cast hmul
  have hres := (lemma_6_3 hm K g hg Z (fun r => (hZ r).le) u₀ hu₀).1
    hwin q hqnonneg hqne hmulq
  have hZQ : Z + cycL q = Q := by dsimp [Z]; abel
  rw [hZQ, hsupport] at hres
  exact hres
