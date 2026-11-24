-- Prove2me | solution 2 for HypercliqueAC0.FixedDepth.Supplement.lemma_8_1
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:11:05.224644+00:00
-- url     : https://prove2.me/submissions/f8850e69-47af-4876-b136-dd8081c6a5d4

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Supplement_TwoListOV

set_option autoImplicit false
noncomputable section

open HypercliqueAC0.FixedDepth.Supplement
open scoped BigOperators

/-- A family of at most `n₂` sets is listed (with padding by `univ`) by `Fin n₂`. -/
private lemma exists_enum (d n₂ : ℕ) (T : Finset (Finset (Fin d))) (hT : T.card ≤ n₂) :
    ∃ g : Fin n₂ → Finset (Fin d),
      (∀ j, g j ∈ T ∨ g j = Finset.univ) ∧ ∀ w ∈ T, ∃ j, g j = w := by
  classical
  refine ⟨fun j => if h : (j : ℕ) < T.card then (T.equivFin.symm ⟨j, h⟩).1 else Finset.univ,
    ?_, ?_⟩
  · intro j
    dsimp only
    split_ifs with h
    · exact Or.inl (T.equivFin.symm _).2
    · exact Or.inr rfl
  · intro w hw
    have hlt : ((T.equivFin ⟨w, hw⟩ : Fin T.card) : ℕ) < n₂ :=
      lt_of_lt_of_le (T.equivFin ⟨w, hw⟩).2 hT
    refine ⟨⟨_, hlt⟩, ?_⟩
    simp only [Fin.is_lt, dif_pos, Fin.eta, Equiv.symm_apply_apply]

theorem solution (d : ℕ) (hd : 2 ≤ d) (n₁ n₂ : ℕ) (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂)
    (i : Fin n₁) :
    ∑ s ∈ Finset.range (min n₂ (Nat.choose d (d / 2)) + 1), Nat.choose (Nat.choose d (d / 2)) s ≤
      (subfunctionsOnFirstVector (twoListOV n₁ n₂ d) i).card := by
  classical
  set Mid : Finset (Finset (Fin d)) := (Finset.univ : Finset (Fin d)).powersetCard (d / 2)
    with hMid
  have hmemMid : ∀ w, w ∈ Mid ↔ w.card = d / 2 := by
    intro w
    simp [hMid, Finset.mem_powersetCard]
  have hcardMid : Mid.card = d.choose (d / 2) := by
    simp [hMid, Finset.card_powersetCard]
  set S := Mid.powerset.filter (fun T => T.card ≤ n₂) with hSdef
  have hS : S.card =
      ∑ s ∈ Finset.range (min n₂ (d.choose (d / 2)) + 1), (d.choose (d / 2)).choose s := by
    rw [hSdef, Finset.card_filter,
      Finset.sum_powerset_apply_card (fun m => if m ≤ n₂ then 1 else 0), hcardMid]
    simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext s
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hkey : ∀ T ∈ S, ∃ φ ∈ subfunctionsOnFirstVector (twoListOV n₁ n₂ d) i,
      ∀ w ∈ Mid, φ (fun q => decide (q ∉ w)) = decide (w ∈ T) := by
    intro T hT
    rw [hSdef, Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hTM, hTc⟩ := hT
    obtain ⟨g, hg1, hg2⟩ := exists_enum d n₂ T hTc
    let y : TwoListVar n₁ n₂ d → Bool :=
      Sum.elim (fun _ => true) (fun p => decide (p.2 ∈ g p.1))
    refine ⟨fun z => twoListOV n₁ n₂ d (setFirstVector i y z), ?_, ?_⟩
    · unfold subfunctionsOnFirstVector
      exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩
    · intro w hw
      have hwc := (hmemMid w).mp hw
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      unfold twoListOV
      rw [decide_eq_true_iff]
      constructor
      · rintro ⟨i', j, hq⟩
        have hgne : (g j).Nonempty := by
          rcases hg1 j with h | h
          · rw [← Finset.card_pos, (hmemMid _).mp (hTM h)]
            omega
          · rw [h]
            exact Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩
        obtain ⟨q0, hq0⟩ := hgne
        by_cases hi' : i' = i
        · subst hi'
          have hsub : g j ⊆ w := by
            intro q hq'
            have := hq q
            simp [setFirstVector, y] at this
            tauto
          rcases hg1 j with h | h
          · have : g j = w := Finset.eq_of_subset_of_card_le hsub
              (by rw [hwc, (hmemMid _).mp (hTM h)])
            exact this ▸ h
          · exfalso
            rw [h] at hsub
            have := Finset.card_le_card hsub
            rw [Finset.card_univ, Fintype.card_fin, hwc] at this
            omega
        · exfalso
          have := hq q0
          simp [setFirstVector, hi', y] at this
          exact this hq0
      · intro hwT
        obtain ⟨j, hj⟩ := hg2 w hwT
        refine ⟨i, j, fun q => ?_⟩
        simp [setFirstVector, y, hj]
        tauto
  choose! Φ hΦmem hΦprop using hkey
  rw [← hS]
  apply Finset.card_le_card_of_injOn Φ
  · intro T hT
    exact hΦmem T hT
  · intro T₁ hT₁ T₂ hT₂ he
    have hsub : ∀ T ∈ S, T ⊆ Mid := by
      intro T hT
      rw [hSdef, Finset.mem_filter, Finset.mem_powerset] at hT
      exact hT.1
    ext w
    by_cases hw : w ∈ Mid
    · have h1 := hΦprop T₁ hT₁ w hw
      rw [he, hΦprop T₂ hT₂ w hw] at h1
      exact (decide_eq_decide.mp h1).symm
    · exact iff_of_false (fun h => hw (hsub T₁ hT₁ h)) (fun h => hw (hsub T₂ hT₂ h))
