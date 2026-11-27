-- Prove2me | solution 1 for ManipPotential.proposition_6_11_uniqueness_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T22:59:37.133944+00:00
-- url     : https://prove2.me/submissions/4d68b025-cb49-4a9e-8b56-1d8390d2f1ee

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_IsCommonJunction
import Definitions.Def_ManipPotential_ExtRanking
import Definitions.Def_ManipPotential_cycTotal
import Definitions.Def_ManipPotential_kappa
import Theorems.Thm_ManipPotential_lemma_6_10

open ManipPotential

private lemma ell_inj {m : ℕ} [NeZero m] {i j : Fin m} (h : ell i = ell j) : i = j := by
  have := congrArg (fun e : Ranking m => e 0) h
  simpa [ell, Equiv.subLeft_apply] using this

private lemma cycL_ell {m : ℕ} [NeZero m] (v : Fin m → ℝ) (j : Fin m) :
    cycL v (ell j) = v j := by
  unfold cycL unitVec
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have : ell j ≠ ell i := fun h => hij (ell_inj h).symm
    simp [this]
  · simp

private lemma cycL_ext {m : ℕ} [NeZero m] (v : Fin m → ℝ) (r : Ranking m)
    (hr : ∀ j, ell j ≠ r) : cycL v r = 0 := by
  unfold cycL unitVec
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have : r ≠ ell i := fun h => hr i h.symm
  simp [this]

theorem solution {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ)
    (g : (Ranking m → ℚ) → Fin m) (hg : GAxioms K g) :
    ∃ L : NNReal, ∀ P P' : Ranking m → ℝ,
      IsCommonJunction g P → IsCommonJunction g P' →
      (∀ r, 1 < P r) → (∀ r, 1 < P' r) →
      (∀ s : ExtRanking m, P s.1 < 1 + 1 / 32) →
      (∀ s : ExtRanking m, P' s.1 < 1 + 1 / 32) →
      dist P P' ≤ (L : ℝ) *
        max (‖fun s : ExtRanking m => P s.1 - P' s.1‖) |cycTotal P - cycTotal P'| := by
  classical
  set κ := kappa m K with hκdef
  have hκ : 0 < κ := by rw [hκdef]; unfold kappa; positivity
  refine ⟨⟨1 + 8 * κ, by positivity⟩, ?_⟩
  intro P P' hP hP' h1 h1' hy hy'
  show dist P P' ≤ (1 + 8 * κ) * _
  set R := ‖fun s : ExtRanking m => P s.1 - P' s.1‖ with hR
  set D := |cycTotal P - cycTotal P'| with hD
  have hR0 : 0 ≤ R := norm_nonneg _
  have hRs : ∀ s : ExtRanking m, |P s.1 - P' s.1| ≤ R := fun s => by
    have := norm_le_pi_norm (fun s : ExtRanking m => P s.1 - P' s.1) s
    simpa [Real.norm_eq_abs] using this
  have hR8 : R < 1 / 8 := by
    have : R < 1 / 32 := by
      rw [hR, pi_norm_lt_iff (by norm_num)]
      intro s
      rw [Real.norm_eq_abs, abs_sub_lt_iff]
      constructor <;> linarith [hy s, hy' s, h1 s.1, h1' s.1]
    linarith
  set h : Fin m → ℝ := fun j => P' (ell j) - P (ell j) with hh
  set hp : Fin m → ℝ := fun j => max (h j) 0 with hhp
  set hn : Fin m → ℝ := fun j => max (-h j) 0 with hhn
  have hεP : ∀ (P0 : Ranking m → ℝ), (∀ r, 1 < P0 r) → ∀ ε : ℝ, ε < 1 / 2 →
      ε < (1 / 2) * Finset.univ.inf' Finset.univ_nonempty P0 := by
    intro P0 hP0 ε hε
    have : 1 < Finset.univ.inf' Finset.univ_nonempty P0 := by
      rw [Finset.lt_inf'_iff]; intro r _; exact hP0 r
    linarith
  have key : min (∑ j, hp j) (∑ j, hn j) ≤ κ * (4 * R) := by
    by_contra hcon
    push_neg at hcon
    set M := min (∑ j, hp j) (∑ j, hn j) with hMdef
    have hM1 : 4 * R < M / κ := by rw [lt_div_iff₀ hκ]; linarith
    have hm1 : 4 * R < min (M / κ) (1 / 2) := lt_min hM1 (by linarith)
    set ε := (4 * R + min (M / κ) (1 / 2)) / 2 with hεdef
    have hε1 : 4 * R < ε := by rw [hεdef]; linarith
    have hε2 : ε < min (M / κ) (1 / 2) := by rw [hεdef]; linarith
    have hε3 : ε < 1 / 2 := lt_of_lt_of_le hε2 (min_le_right _ _)
    have hε4 : κ * ε < M := by
      have := lt_of_lt_of_le hε2 (min_le_left _ _)
      rw [lt_div_iff₀ hκ] at this; linarith
    have hεpos : 0 < ε := by linarith
    have hκε : 0 < κ * ε := mul_pos hκ hεpos
    set Z : Ranking m → ℝ := fun r => max (P r) (P' r) - ε with hZ
    have hδ : 0 < ε / 4 - R := by linarith
    obtain ⟨Q, hQ⟩ : ∃ Q : Ranking m → ℚ, ‖(fun r => (Q r : ℝ)) - Z‖ < ε / 4 - R := by
      have : ∀ r, ∃ q : ℚ, Z r - (ε / 4 - R) / 2 < q ∧ (q : ℝ) < Z r + (ε / 4 - R) / 2 :=
        fun r => exists_rat_btwn (by linarith)
      choose q hq using this
      refine ⟨q, ?_⟩
      have : ‖(fun r => (q r : ℝ)) - Z‖ ≤ (ε / 4 - R) / 2 := by
        rw [pi_norm_le_iff_of_nonneg (by linarith)]
        intro r
        rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
        constructor <;> linarith [(hq r).1, (hq r).2]
      linarith
    -- distances from Z
    have hZp : ‖Z - (P - (fun _ => ε) + cycL hp)‖ ≤ R := by
      rw [pi_norm_le_iff_of_nonneg hR0]
      intro r
      rw [Real.norm_eq_abs]
      by_cases hr : ∃ j, ell j = r
      · obtain ⟨j, rfl⟩ := hr
        simp only [Pi.sub_apply, Pi.add_apply, hZ, cycL_ell, hhp, hh]
        rcases le_total (P (ell j)) (P' (ell j)) with hle | hle
        · rw [max_eq_right hle, max_eq_left (by linarith)]; simp [hR0]
        · rw [max_eq_left hle, max_eq_right (by linarith)]; simp [hR0]
      · push_neg at hr
        simp only [Pi.sub_apply, Pi.add_apply, hZ, cycL_ext _ r hr]
        have := hRs ⟨r, hr⟩
        simp only at this
        rcases le_total (P r) (P' r) with hle | hle
        · rw [max_eq_right hle]; rw [abs_le] at this ⊢; constructor <;> linarith
        · rw [max_eq_left hle]; simp [hR0]
    have hZn : ‖Z - (P' - (fun _ => ε) + cycL hn)‖ ≤ R := by
      rw [pi_norm_le_iff_of_nonneg hR0]
      intro r
      rw [Real.norm_eq_abs]
      by_cases hr : ∃ j, ell j = r
      · obtain ⟨j, rfl⟩ := hr
        simp only [Pi.sub_apply, Pi.add_apply, hZ, cycL_ell, hhn, hh]
        rcases le_total (P (ell j)) (P' (ell j)) with hle | hle
        · rw [max_eq_right hle, max_eq_right (by linarith)]; simp [hR0]
        · rw [max_eq_left hle, max_eq_left (by linarith)]; simp [hR0]
      · push_neg at hr
        simp only [Pi.sub_apply, Pi.add_apply, hZ, cycL_ext _ r hr]
        have := hRs ⟨r, hr⟩
        simp only at this
        rcases le_total (P r) (P' r) with hle | hle
        · rw [max_eq_right hle]; simp [hR0]
        · rw [max_eq_left hle]; rw [abs_le] at this ⊢; constructor <;> linarith
    have tri : ∀ A B C : Ranking m → ℝ, ‖A - C‖ ≤ ‖A - B‖ + ‖B - C‖ := fun A B C => by
      calc ‖A - C‖ = ‖(A - B) + (B - C)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have hQp : ‖(fun r => (Q r : ℝ)) - (P - (fun _ => ε) + cycL hp)‖ < ε / 4 := by
      have := tri (fun r => (Q r : ℝ)) Z (P - (fun _ => ε) + cycL hp); linarith
    have hQn : ‖(fun r => (Q r : ℝ)) - (P' - (fun _ => ε) + cycL hn)‖ < ε / 4 := by
      have := tri (fun r => (Q r : ℝ)) Z (P' - (fun _ => ε) + cycL hn); linarith
    -- supports
    have hpne : ∃ j, 0 < hp j := by
      by_contra H; push_neg at H
      have : ∑ j, hp j ≤ 0 := Finset.sum_nonpos (fun j _ => H j)
      have : M ≤ ∑ j, hp j := min_le_left _ _
      linarith
    have hnne : ∃ j, 0 < hn j := by
      by_contra H; push_neg at H
      have : ∑ j, hn j ≤ 0 := Finset.sum_nonpos (fun j _ => H j)
      have : M ≤ ∑ j, hn j := min_le_right _ _
      linarith
    have memsupp : ∀ (v : Fin m → ℝ) j, j ∈ supp v ↔ 0 < v j := fun v j => by simp [supp]
    have hpos_iff : ∀ j, 0 < hp j ↔ 0 < h j := fun j => by
      simp only [hhp, lt_max_iff, lt_irrefl, or_false]
    have hneg_iff : ∀ j, 0 < hn j ↔ h j < 0 := fun j => by
      simp only [hhn, lt_max_iff, lt_irrefl, or_false, neg_pos]
    obtain ⟨jp, hjp⟩ := hpne
    obtain ⟨jn, hjn⟩ := hnne
    have A := lemma_6_10 hm K g hg P hP ε hεpos (hεP P h1 ε hε3) hp
      (fun j => le_max_right _ _) ⟨jp, (memsupp _ _).2 hjp⟩
      (by
        intro heq
        have : jn ∈ supp hp := heq ▸ Finset.mem_univ jn
        rw [memsupp, hpos_iff] at this
        rw [hneg_iff] at hjn
        linarith)
      (by linarith [show M ≤ ∑ j, hp j from min_le_left _ _]) Q hQp
    have B := lemma_6_10 hm K g hg P' hP' ε hεpos (hεP P' h1' ε hε3) hn
      (fun j => le_max_right _ _) ⟨jn, (memsupp _ _).2 hjn⟩
      (by
        intro heq
        have : jp ∈ supp hn := heq ▸ Finset.mem_univ jp
        rw [memsupp, hneg_iff] at this
        rw [hpos_iff] at hjp
        linarith)
      (by linarith [show M ≤ ∑ j, hn j from min_le_right _ _]) Q hQn
    rw [memsupp, hpos_iff] at A
    rw [memsupp, hneg_iff] at B
    linarith
  -- ℓ¹ bound on the cyclic part
  have habs : ∀ j, |h j| = hp j + hn j := fun j => by
    simp only [hhp, hhn]
    rcases le_total 0 (h j) with hle | hle
    · rw [abs_of_nonneg hle, max_eq_left hle, max_eq_right (by linarith)]; ring
    · rw [abs_of_nonpos hle, max_eq_right hle, max_eq_left (by linarith)]; ring
  have hsum : ∑ j, h j = ∑ j, hp j - ∑ j, hn j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _
    simp only [hhp, hhn]
    rcases le_total 0 (h j) with hle | hle
    · rw [max_eq_left hle, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hle, max_eq_left (by linarith)]; ring
  have hsumD : |∑ j, h j| = D := by
    rw [hD, abs_sub_comm]
    simp only [hh, cycTotal, Finset.sum_sub_distrib]
  have hl1 : ∑ j, |h j| ≤ D + 8 * κ * R := by
    rw [Finset.sum_congr rfl (fun j _ => habs j), Finset.sum_add_distrib, ← hsumD, hsum]
    set a := ∑ j, hp j
    set b := ∑ j, hn j
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab] at key
      rw [abs_of_nonpos (by linarith)]; linarith
    · rw [min_eq_right hab] at key
      rw [abs_of_nonneg (by linarith)]; linarith
  have hmaxR := le_max_left R D
  have hmaxD := le_max_right R D
  have hmax0 : 0 ≤ max R D := le_trans hR0 hmaxR
  have hk8 : 8 * κ * R ≤ 8 * κ * max R D := by
    apply mul_le_mul_of_nonneg_left hmaxR; positivity
  rw [dist_pi_le_iff (by positivity)]
  intro r
  rw [Real.dist_eq]
  by_cases hr : ∃ j, ell j = r
  · obtain ⟨j, rfl⟩ := hr
    have h1j : |h j| ≤ ∑ j, |h j| :=
      Finset.single_le_sum (f := fun j => |h j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    have : |P (ell j) - P' (ell j)| = |h j| := by rw [hh, abs_sub_comm]
    rw [this]
    nlinarith
  · push_neg at hr
    have := hRs ⟨r, hr⟩
    simp only at this
    have : 0 ≤ 8 * κ * max R D := by positivity
    nlinarith
