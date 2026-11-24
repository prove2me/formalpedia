-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KmCover.double_coset_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:32:19.788564+00:00
-- url     : https://prove2.me/submissions/561f4a00-a4e4-4cce-a841-ec78154cd16b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SolveUnitriangular
import Theorems.Thm_GlobalTheory_CompanionTheory_KmCover_mul_congr_one
import Theorems.Thm_GlobalTheory_CompanionTheory_KmCover_solve_unitriangular
import Theorems.Thm_GlobalTheory_CompanionTheory_KmCover_exists_reps
import Theorems.Thm_GlobalTheory_CompanionTheory_KmCover_map_mul_diagonal
import Theorems.Thm_GlobalTheory_CompanionTheory_IwahoriUDL_iwahori_udl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KmCover
open Matrix
namespace GlobalTheory.CompanionTheory.KmCover
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) (ϖ : R) (m : ℕ), Irreducible ϖ → 1 ≤ m →
    ∀ [Finite (IsLocalRing.ResidueField R)] (lam : Fin n → ℤ), Antitone lam →
    ∃ s : Finset (Matrix (Fin n) (Fin n) K),
      s.card ≤ Nat.card (IsLocalRing.ResidueField R) ^
        (∑ i : Fin n, ∑ j : Fin n, if i < j then (lam i - lam j).toNat else 0) ∧
      ∀ (A1 A2 : Matrix (Fin n) (Fin n) R),
        (∀ i j, A1 i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) →
        (∀ i j, A2 i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) →
        ∃ g ∈ s, ∃ B : Matrix (Fin n) (Fin n) R,
          (∀ i j, B i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) ∧
          A1.map (algebraMap R K) * Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (lam i)) *
            A2.map (algebraMap R K) = g * B.map (algebraMap R K) := by
  intro R K _ _ _ _ _ _ n ϖ m hϖ hm _ lam hlam
  classical
  choose reps hcard hrep using fun k => exists_reps R hϖ k
  set a := algebraMap R K with ha
  set J : Ideal R := Ideal.span {ϖ ^ m} with hJ
  have hπ : a ϖ ≠ 0 := by
    intro h
    have h0 : ϖ = 0 := (IsFractionRing.injective R K) (by rw [map_zero]; exact h)
    exact hϖ.ne_zero h0

  have hpow : ∀ i j : Fin n, j ≤ i → a ϖ ^ lam i * a ϖ ^ (lam j - lam i).toNat = a ϖ ^ lam j := by
    intro i j h
    have h0 : 0 ≤ lam j - lam i := sub_nonneg.mpr (hlam h)
    rw [← zpow_natCast, Int.toNat_of_nonneg h0, ← zpow_add₀ hπ]
    congr 1
    ring
  let Tf : Fin n → Fin n → Finset R := fun i j =>
    if i < j then (reps (lam i - lam j).toNat).image (fun x => ϖ ^ m * x)
    else {(1 : Matrix (Fin n) (Fin n) R) i j}
  let S : Finset (Fin n → Fin n → R) :=
    Fintype.piFinset fun i => Fintype.piFinset fun j => Tf i j
  let D : Matrix (Fin n) (Fin n) K := Matrix.diagonal (fun i => a ϖ ^ (lam i))
  let f : (Fin n → Fin n → R) → Matrix (Fin n) (Fin n) K :=
    fun r => (Matrix.of r).map a * D
  have hT : ∀ i j, (Tf i j).card ≤ Nat.card (IsLocalRing.ResidueField R) ^
      (if i < j then (lam i - lam j).toNat else 0) := by
    intro i j
    by_cases h : i < j
    · simp only [Tf, if_pos h]
      exact Finset.card_image_le.trans (hcard _)
    · simp [Tf, if_neg h]
  refine ⟨S.image f, ?_, ?_⟩
  · calc (S.image f).card ≤ S.card := Finset.card_image_le
      _ = ∏ i, ∏ j, (Tf i j).card := by simp [S, Fintype.card_piFinset]
      _ ≤ ∏ i : Fin n, ∏ j : Fin n, Nat.card (IsLocalRing.ResidueField R) ^
            (if i < j then (lam i - lam j).toNat else 0) :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ =>
            Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun j _ => hT i j
      _ = _ := by simp only [Finset.prod_pow_eq_pow_sum]
  · intro A1 A2 h1 h2
    obtain ⟨u, d, l, hu, hd, hl, hul, hud, hdo, hlu, hld, hA⟩ :=
      GlobalTheory.CompanionTheory.IwahoriUDL.iwahori_udl R n ϖ m hϖ hm A1 h1
    have hdec : ∀ i j : Fin n, i < j → ∀ c ∈ J, ∃ t v : R,
        t ∈ (fun x => ϖ ^ m * x) '' (reps (lam i - lam j).toNat : Set R) ∧
        v ∈ (Ideal.span {ϖ ^ (m + (lam i - lam j).toNat)} : Set R) ∧
        t ∈ J ∧ v ∈ J ∧ c = t + v := by
      intro i j _ c hc
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hc
      obtain ⟨t, ht, hy⟩ := hrep (lam i - lam j).toNat y
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hy
      refine ⟨ϖ ^ m * t, ϖ ^ (m + (lam i - lam j).toNat) * z, ⟨t, ht, rfl⟩, ?_, ?_, ?_, ?_⟩
      · exact Ideal.mem_span_singleton.mpr (Dvd.intro _ rfl)
      · exact Ideal.mem_span_singleton.mpr (Dvd.intro _ rfl)
      · exact Ideal.mem_span_singleton.mpr ⟨ϖ ^ (lam i - lam j).toNat * z, by ring⟩
      · rw [pow_add]
        linear_combination ϖ ^ m * hz
    obtain ⟨r, w, hrl, hrd, hrT, hwl, hwd, hwV, huw⟩ := solve_unitriangular J
      (fun i j => (fun x => ϖ ^ m * x) '' (reps (lam i - lam j).toNat : Set R))
      (fun i j => (Ideal.span {ϖ ^ (m + (lam i - lam j).toNat)} : Set R))
      hdec u hu hul hud

    have hw' : ∀ i j, ∃ y : R, y - (1 : Matrix (Fin n) (Fin n) R) i j ∈ J ∧
        a (w i j) * a ϖ ^ lam j = a ϖ ^ lam i * a y := by
      intro i j
      rcases lt_trichotomy i j with h | h | h
      · obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp (hwV i j h)
        refine ⟨ϖ ^ m * z, ?_, ?_⟩
        · rw [Matrix.one_apply_ne (ne_of_lt h), sub_zero]
          exact Ideal.mem_span_singleton.mpr (Dvd.intro _ rfl)
        · have h0 : 0 ≤ lam i - lam j := sub_nonneg.mpr (hlam h.le)
          have e : a ϖ ^ lam j * a ϖ ^ (lam i - lam j).toNat = a ϖ ^ lam i := by
            rw [← zpow_natCast, Int.toNat_of_nonneg h0, ← zpow_add₀ hπ]
            congr 1
            ring
          rw [hz, pow_add, ← e]
          simp only [map_mul, map_pow]
          ring
      · subst h
        refine ⟨1, by simp [J.zero_mem], ?_⟩
        rw [hwd]
        simp [mul_comm]
      · refine ⟨0, ?_, ?_⟩
        · rw [Matrix.one_apply_ne (ne_of_gt h)]
          simp
        · rw [hwl i j h]
          simp
    have hl' : ∀ i j, ∃ y : R, y - (1 : Matrix (Fin n) (Fin n) R) i j ∈ J ∧
        a (l i j) * a ϖ ^ lam j = a ϖ ^ lam i * a y := by
      intro i j
      rcases lt_trichotomy i j with h | h | h
      · refine ⟨0, ?_, ?_⟩
        · rw [Matrix.one_apply_ne (ne_of_lt h)]
          simp
        · rw [hlu i j h]
          simp
      · subst h
        refine ⟨1, by simp [J.zero_mem], ?_⟩
        rw [hld]
        simp [mul_comm]
      · refine ⟨l i j * ϖ ^ (lam j - lam i).toNat, ?_, ?_⟩
        · rw [Matrix.one_apply_ne (ne_of_gt h), sub_zero]
          have := hl i j
          rw [Matrix.one_apply_ne (ne_of_gt h), sub_zero] at this
          exact J.mul_mem_right _ this
        · rw [← hpow i j h.le]
          simp only [map_mul, map_pow]
          ring
    choose w' hw'1 hw'2 using hw'
    choose l' hl'1 hl'2 using hl'
    have ew : (w.map a) * D = D * (Matrix.of w').map a :=
      map_mul_diagonal a _ w (Matrix.of w') hw'2
    have el : (l.map a) * D = D * (Matrix.of l').map a :=
      map_mul_diagonal a _ l (Matrix.of l') hl'2
    have ed : (d.map a) * D = D * d.map a := by
      refine map_mul_diagonal a _ d d fun i j => ?_
      by_cases h : i = j
      · subst h
        exact mul_comm _ _
      · rw [hdo i j h]
        simp
    refine ⟨f r, Finset.mem_image_of_mem f ?_, Matrix.of w' * d * Matrix.of l' * A2, ?_, ?_⟩
    · refine Fintype.mem_piFinset.mpr fun i => Fintype.mem_piFinset.mpr fun j => ?_
      by_cases h : i < j
      · simp only [Tf, if_pos h]
        obtain ⟨t, ht, e⟩ := hrT i j h
        exact Finset.mem_image.mpr ⟨t, ht, e⟩
      · simp only [Tf, if_neg h, Finset.mem_singleton]
        rcases lt_or_eq_of_le (not_lt.mp h) with h' | h'
        · rw [hrl i j h', Matrix.one_apply_ne (ne_of_gt h')]
        · subst h'
          rw [hrd, Matrix.one_apply_eq]
    · exact mul_congr_one (mul_congr_one (mul_congr_one hw'1 hd) hl'1) h2
    · show A1.map a * D * A2.map a = (Matrix.of r).map a * D * _
      have er : (Matrix.of r) = r := rfl
      rw [er, hA, huw]
      simp only [Matrix.map_mul]
      calc r.map a * w.map a * d.map a * l.map a * D * A2.map a
          = r.map a * w.map a * d.map a * (l.map a * D) * A2.map a := by
            simp only [Matrix.mul_assoc]
        _ = r.map a * w.map a * (d.map a * D) * (Matrix.of l').map a * A2.map a := by
            rw [el]
            simp only [Matrix.mul_assoc]
        _ = r.map a * (w.map a * D) * d.map a * (Matrix.of l').map a * A2.map a := by
            rw [ed]
            simp only [Matrix.mul_assoc]
        _ = r.map a * D * ((Matrix.of w').map a * d.map a * (Matrix.of l').map a * A2.map a) := by
            rw [ew]
            simp only [Matrix.mul_assoc]
end GlobalTheory.CompanionTheory.KmCover
