-- Prove2me | solution 1 for KangKurtz.SecondScale.gammaTheta_ge
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:42:48.877958+00:00
-- url     : https://prove2.me/submissions/0a313ef7-74c4-4456-8e8e-c3b330b2d721

import Mathlib
import Definitions.Def_KangKurtz_SecondScale_Setting
set_option autoImplicit false
open KangKurtz.SecondScale

lemma ss_sup'_congr {ι : Type*} (S T : Finset ι) (f : ι → ℝ) (hST : S = T)
    (h1 : S.Nonempty) (h2 : T.Nonempty) : S.sup' h1 f = T.sup' h2 f := by
  subst hST; rfl

lemma ss_partA {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ)
    (α : Fin s → ℝ) (β : Fin r → ℝ) (θ : Fin s → ℝ) (hθ : ∀ i, 0 ≤ θ i) :
    (⨅ i ∈ KangKurtz.SecondScale.support θ, gammaSp ν ν' α β i) ≤
      KangKurtz.SCC.gammaTheta ν ν' α β θ := by
  unfold KangKurtz.SCC.gammaTheta
  dsimp only
  split_ifs with hS
  · obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' hS (KangKurtz.SCC.rho ν α β)
    have hdot : KangKurtz.SCC.dot ν ν' θ k ≠ 0 := by
      intro h0
      simp only [Finset.mem_union, KangKurtz.SCC.GammaPlus, KangKurtz.SCC.GammaMinus,
        Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rcases hk with h | h <;> linarith
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdot
    have hθi : 0 < θ i := by
      rcases (hθ i).lt_or_eq with h | h
      · exact h
      · exfalso; apply hi; rw [← h]; ring
    have hζ : KangKurtz.SCC.zeta ν ν' k i ≠ 0 := by
      intro h; apply hi; rw [h]; ring
    have hisupp : i ∈ KangKurtz.SecondScale.support θ := by
      simp [KangKurtz.SecondScale.support, hθi]
    have hne : ν k i ≠ ν' k i := by
      intro h; apply hζ; simp [KangKurtz.SCC.zeta, h]
    have hkΓ : k ∈ GammaSpPlus ν ν' i ∪ GammaSpMinus ν ν' i := by
      simp only [Finset.mem_union, GammaSpPlus, GammaSpMinus, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hΓne : (GammaSpPlus ν ν' i ∪ GammaSpMinus ν ν' i).Nonempty := ⟨k, hkΓ⟩
    refine (iInf₂_le i hisupp).trans ?_
    unfold gammaSp
    rw [dif_pos hΓne]
    rw [EReal.coe_le_coe_iff]
    have h1 : KangKurtz.SCC.rho ν α β k ≤
        (GammaSpPlus ν ν' i ∪ GammaSpMinus ν ν' i).sup' hΓne (KangKurtz.SCC.rho ν α β) :=
      Finset.le_sup' (KangKurtz.SCC.rho ν α β) hkΓ
    have h2 : α i ≤ KangKurtz.SCC.alphaTheta α θ := by
      unfold KangKurtz.SCC.alphaTheta
      dsimp only
      have hne' : (Finset.univ.filter (fun j => 0 < θ j)).Nonempty := ⟨i, by simp [hθi]⟩
      rw [dif_pos hne']
      exact Finset.le_sup' α (by simp [hθi])
    rw [← hkeq] at h1
    linarith
  · exact le_top

lemma ss_partB {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ)
    (α : Fin s → ℝ) (β : Fin r → ℝ) (i : Fin s) :
    KangKurtz.SCC.gammaTheta ν ν' α β (Pi.single i 1) = gammaSp ν ν' α β i := by
  have hdot : ∀ k, KangKurtz.SCC.dot ν ν' (Pi.single i (1:ℝ)) k = KangKurtz.SCC.zeta ν ν' k i := by
    intro k
    simp [KangKurtz.SCC.dot, Pi.single_apply]
  have hS : KangKurtz.SCC.GammaPlus ν ν' (Pi.single i (1:ℝ)) ∪
      KangKurtz.SCC.GammaMinus ν ν' (Pi.single i (1:ℝ)) =
      GammaSpPlus ν ν' i ∪ GammaSpMinus ν ν' i := by
    ext k
    simp only [Finset.mem_union, KangKurtz.SCC.GammaPlus, KangKurtz.SCC.GammaMinus,
      GammaSpPlus, GammaSpMinus, Finset.mem_filter, Finset.mem_univ, true_and, hdot,
      KangKurtz.SCC.zeta, sub_pos, sub_neg, Nat.cast_lt]
  have hα : KangKurtz.SCC.alphaTheta α (Pi.single i (1:ℝ)) = α i := by
    unfold KangKurtz.SCC.alphaTheta
    dsimp only
    have : (Finset.univ.filter (fun j => 0 < (Pi.single i (1:ℝ) : Fin s → ℝ) j)) = {i} := by
      ext j
      by_cases h : j = i <;> simp [Pi.single_apply, h]
    rw [dif_pos (by rw [this]; exact Finset.singleton_nonempty i)]
    simp_rw [this]
    simp
  unfold KangKurtz.SCC.gammaTheta gammaSp
  dsimp only
  by_cases hne : (GammaSpPlus ν ν' i ∪ GammaSpMinus ν ν' i).Nonempty
  · have hne' : (KangKurtz.SCC.GammaPlus ν ν' (Pi.single i (1:ℝ)) ∪
      KangKurtz.SCC.GammaMinus ν ν' (Pi.single i (1:ℝ))).Nonempty := by rw [hS]; exact hne
    rw [dif_pos hne', dif_pos hne, hα]
    congr 2
    exact ss_sup'_congr _ _ _ hS _ _ |> fun h => by rw [h]
  · have hne' : ¬ (KangKurtz.SCC.GammaPlus ν ν' (Pi.single i (1:ℝ)) ∪
      KangKurtz.SCC.GammaMinus ν ν' (Pi.single i (1:ℝ))).Nonempty := by rw [hS]; exact hne
    rw [dif_neg hne', dif_neg hne]

theorem solution {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ)
    (α : Fin s → ℝ) (hα : ∀ i, 0 ≤ α i) (β : Fin r → ℝ)
    (θ : Fin s → ℝ) (hθ : ∀ i, 0 ≤ θ i) :
    (⨅ i ∈ KangKurtz.SecondScale.support θ, gammaSp ν ν' α β i) ≤ KangKurtz.SCC.gammaTheta ν ν' α β θ ∧
    r1 ν ν' α β =
      ⨅ η ∈ {η : Fin s → ℝ | ∀ i, 0 ≤ η i}, KangKurtz.SCC.gammaTheta ν ν' α β η := by
  refine ⟨ss_partA ν ν' α β θ hθ, ?_⟩
  apply le_antisymm
  · refine le_iInf₂ fun η hη => ?_
    refine le_trans ?_ (ss_partA ν ν' α β η hη)
    exact le_iInf₂ fun i _ => iInf_le _ i
  · refine le_iInf fun i => ?_
    have hmem : (Pi.single i (1:ℝ) : Fin s → ℝ) ∈ {η : Fin s → ℝ | ∀ j, 0 ≤ η j} := by
      intro j
      by_cases h : j = i <;> simp [Pi.single_apply, h]
    refine (iInf₂_le _ hmem).trans ?_
    rw [ss_partB]
