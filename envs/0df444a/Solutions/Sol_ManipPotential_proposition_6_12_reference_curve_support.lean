-- Prove2me | solution 1 for ManipPotential.proposition_6_12_reference_curve_support
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:55:07.808962+00:00
-- url     : https://prove2.me/submissions/7d068fcb-95de-4e05-afa6-2bf56642d67e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_IsCommonJunction
import Definitions.Def_ManipPotential_referenceCurve
import Definitions.Def_ManipPotential_cycL
import Theorems.Thm_ManipPotential_lemma_6_10

open ManipPotential

namespace ManipPotential

private theorem cycL_single {m : ℕ} [NeZero m] (k : Fin m) (a : ℝ) :
    cycL (Pi.single k a) = a • unitVec (ell k) := by
  classical
  ext r
  simp only [cycL, Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single k]
  · simp [unitVec, Pi.single_apply]
  · intro b _ hbk
    simp [hbk]
  · simp

private theorem cycL_add' {m : ℕ} [NeZero m] (x y : Fin m → ℝ) :
    cycL (x + y) = cycL x + cycL y := by
  classical
  ext r
  simp [cycL, add_smul, Finset.sum_add_distrib]

end ManipPotential

/-- Lemma 6.10 applied along the reference curve: nearby rational profiles elect only `i` or `j`,
with the indicated endpoints. -/
theorem solution {m : ℕ} [NeZero m]
    (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m) (hg : GAxioms K g)
    (G : ((ExtRanking m → ℝ) × ℝ) → (Ranking m → ℝ))
    (z₀ v : ((ExtRanking m → ℝ) × ℝ)) (i j : Fin m) (hij : i ≠ j)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hε : ρ / (4 * kappa m K) < 1 / 2) (t : ℝ) (ht : t ∈ Set.Icc 0 1)
    (Q : Ranking m → ℚ)
    (hP : IsCommonJunction g (G (z₀ + (t * ρ) • v)))
    (hPpos : ∀ r, 1 < G (z₀ + (t * ρ) • v) r)
    (hQ : ‖(fun r => (Q r : ℝ)) - referenceCurve K G z₀ v i j ρ t‖ <
      (ρ / (4 * kappa m K)) / 4) :
    (g Q = i ∨ g Q = j) ∧ (t = 0 → g Q = i) ∧ (t = 1 → g Q = j) := by
  classical
  let P : Ranking m → ℝ := G (z₀ + (t * ρ) • v)
  let ε : ℝ := ρ / (4 * kappa m K)
  let x : Fin m → ℝ := Pi.single i (ρ * (1 - t)) + Pi.single j (ρ * t)
  have hκ : 0 < kappa m K := by
    unfold kappa
    positivity
  have hεpos : 0 < ε := by dsimp [ε]; positivity
  have hx0 : 0 ≤ x := by
    intro k
    have ha : 0 ≤ ρ * (1 - t) := mul_nonneg hρ.le (sub_nonneg.mpr ht.2)
    have hb : 0 ≤ ρ * t := mul_nonneg hρ.le ht.1
    dsimp [x]
    by_cases hki : k = i
    · subst k
      simp only [Pi.single_eq_same]
      exact add_nonneg ha (by by_cases h : i = j <;> simp [h, hb])
    · by_cases hkj : k = j
      · subst k
        simp [hki, hb]
      · simp [hki, hkj]
  have hxsum : ∑ k, x k = ρ := by
    classical
    simp [x, Finset.sum_add_distrib]
    ring
  have hsub : supp x ⊆ {i, j} := by
    intro k hk
    have hkpos : 0 < x k := by simpa [supp] using hk
    by_contra hnot
    have hki : k ≠ i := fun h => hnot (by simp [h])
    have hkj : k ≠ j := fun h => hnot (by simp [h])
    simp [x, hki, hkj] at hkpos
  have hnonempty : (supp x).Nonempty := by
    by_cases ht1 : t = 1
    · refine ⟨j, ?_⟩
      subst t
      simp [supp, x, hρ]
    · have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
      refine ⟨i, ?_⟩
      have ha : 0 < ρ * (1 - t) := mul_pos hρ (sub_pos.mpr htlt)
      simp [supp, x, hij, ha]
  have hproper : supp x ≠ Finset.univ := by
    intro hs
    have hpair : ({i, j} : Finset (Fin m)) = Finset.univ := by
      apply Finset.Subset.antisymm (Finset.subset_univ _)
      intro k hk
      have hkx : k ∈ supp x := hs.symm ▸ hk
      exact hsub hkx
    have hcard : ({i, j} : Finset (Fin m)).card ≤ 2 := by
      calc
        ({i, j} : Finset (Fin m)).card ≤ ({j} : Finset (Fin m)).card + 1 :=
          Finset.card_insert_le i {j}
        _ = 2 := by simp
    rw [hpair, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  have hmass : kappa m K * ε < ∑ k, x k := by
    rw [hxsum]
    have heq : kappa m K * ε = ρ / 4 := by
      dsimp [ε]
      field_simp
    rw [heq]
    linarith
  have hPinf : 1 < Finset.univ.inf' Finset.univ_nonempty P := by
    rw [Finset.lt_inf'_iff]
    intro r _
    exact hPpos r
  have hεP : ε < (1 / 2 : ℝ) * Finset.univ.inf' Finset.univ_nonempty P := by
    dsimp [ε] at hε ⊢
    linarith
  have hcyc : cycL x = ρ • ((1 - t) • unitVec (ell i) + t • unitVec (ell j)) := by
    dsimp [x]
    rw [cycL_add', cycL_single, cycL_single]
    module
  have hcurve : P - (fun _ => ε) + cycL x = referenceCurve K G z₀ v i j ρ t := by
    rw [hcyc]
    rfl
  have hclose : ‖(fun r => (Q r : ℝ)) - (P - (fun _ => ε) + cycL x)‖ < ε / 4 := by
    rw [hcurve]
    exact hQ
  have hmain : g Q ∈ supp x :=
    ManipPotential.lemma_6_10 hm K g hg P hP ε hεpos hεP x
      hx0 hnonempty hproper hmass Q hclose
  have hwinner : g Q = i ∨ g Q = j := by
    have hgmem := hsub hmain
    simpa using hgmem
  refine ⟨hwinner, ?_, ?_⟩
  · intro ht0
    subst t
    by_contra hne
    have hz : x (g Q) = 0 := by
      simp [x, hne]
    have hgpos : 0 < x (g Q) := by simpa [supp] using hmain
    exact (ne_of_gt hgpos) hz
  · intro ht1
    subst t
    by_contra hne
    have hz : x (g Q) = 0 := by
      simp [x, hne]
    have hgpos : 0 < x (g Q) := by simpa [supp] using hmain
    exact (ne_of_gt hgpos) hz
