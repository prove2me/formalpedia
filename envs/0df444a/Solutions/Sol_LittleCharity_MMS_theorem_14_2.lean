-- Prove2me | solution 2 for LittleCharity.MMS.theorem_14
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:54:02.463993+00:00
-- url     : https://prove2.me/submissions/b16ec72e-d973-48dd-a141-064277ebaf18

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting

set_option autoImplicit false
open LittleCharity.MMS

theorem lcm_add_mono {n m : ℕ} {v : Fin n → Finset (Fin m) → ℝ} (hadd : IsAdditive v) (i : Fin n)
    {A B : Finset (Fin m)} (h : A ⊆ B) : v i A ≤ v i B := by
  rw [hadd.1 i A, hadd.1 i B]
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun g _ _ => hadd.2 i {g})

theorem lcm_mms_step {m : ℕ} (w : Finset (Fin m) → ℝ) (hw : ∀ A B, A ⊆ B → w A ≤ w B)
    (k : ℕ) (hk : 1 ≤ k) (S S' : Finset (Fin m)) (hS : S' ⊆ S) (hc : (S \ S').card ≤ 1) :
    mms w (k + 1) S ≤ mms w k S' := by
  classical
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  unfold mms
  apply ciSup_le
  intro f
  obtain ⟨a, ha⟩ : ∃ a : Fin (k' + 1 + 1), ∀ x ∈ S \ S', f x = a := by
    by_cases h : (S \ S').Nonempty
    · obtain ⟨x0, hx0⟩ := h
      refine ⟨f x0, fun x hx => ?_⟩
      rw [Finset.card_le_one.mp hc x hx x0 hx0]
    · exact ⟨0, fun x hx => absurd ⟨x, hx⟩ h⟩
  let f' : Fin m → Fin (k' + 1) := fun x =>
    if h : f x = a then 0 else Classical.choose (Fin.exists_succAbove_eq h)
  have hf' : ∀ x, f x ≠ a → a.succAbove (f' x) = f x := by
    intro x hx
    simp only [f', dif_neg hx]
    exact Classical.choose_spec (Fin.exists_succAbove_eq hx)
  refine le_trans ?_ (le_ciSup (f := fun g : Fin m → Fin (k' + 1) =>
    ⨅ j : Fin (k' + 1), w (S'.filter (fun x => g x = j))) (Set.finite_range _).bddAbove f')
  refine le_ciInf (fun j => ?_)
  refine le_trans (ciInf_le (Set.finite_range _).bddBelow (a.succAbove j)) (hw _ _ ?_)
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  obtain ⟨hxS, hxf⟩ := hx
  have hxa : f x ≠ a := by rw [hxf]; exact Fin.succAbove_ne a j
  have hxS' : x ∈ S' := by
    by_contra hn
    exact hxa (ha x (Finset.mem_sdiff.mpr ⟨hxS, hn⟩))
  refine ⟨hxS', ?_⟩
  apply Fin.succAbove_right_injective (p := a)
  rw [hf' x hxa, hxf]

theorem lcm_mms_remove {m : ℕ} (w : Finset (Fin m) → ℝ) (hw : ∀ A B, A ⊆ B → w A ≤ w B) :
    ∀ (d k : ℕ), 1 ≤ k → ∀ S S' : Finset (Fin m), S' ⊆ S → (S \ S').card ≤ d →
      mms w (k + d) S ≤ mms w k S' := by
  classical
  intro d
  induction d with
  | zero =>
    intro k hk S S' hS hc
    have h0 : S \ S' = ∅ := Finset.card_eq_zero.mp (by omega)
    have : S = S' := by
      apply Finset.Subset.antisymm _ hS
      intro x hx
      by_contra hn
      have : x ∈ S \ S' := Finset.mem_sdiff.mpr ⟨hx, hn⟩
      rw [h0] at this; simp at this
    subst this
    simp
  | succ d ih =>
    intro k hk S S' hS hc
    by_cases hne : (S \ S').Nonempty
    · obtain ⟨g, hg⟩ := hne
      rw [Finset.mem_sdiff] at hg
      have hS1 : S' ⊆ S.erase g := by
        intro x hx
        rw [Finset.mem_erase]
        exact ⟨fun h => hg.2 (h ▸ hx), hS hx⟩
      have hc1 : ((S.erase g) \ S').card ≤ d := by
        have : (S.erase g) \ S' = (S \ S').erase g := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_erase]; tauto
        rw [this, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr hg)]
        omega
      have h1 := ih k hk (S.erase g) S' hS1 hc1
      have h2 := lcm_mms_step w hw (k + d) (by omega) S (S.erase g) (Finset.erase_subset _ _) (by
        calc (S \ S.erase g).card ≤ ({g} : Finset (Fin m)).card := by
              apply Finset.card_le_card
              intro x hx
              simp only [Finset.mem_sdiff, Finset.mem_erase] at hx
              simp only [Finset.mem_singleton]
              by_contra hne; exact hx.2 ⟨hne, hx.1⟩
          _ = 1 := Finset.card_singleton g)
      exact le_trans h2 h1
    · have h0 : S \ S' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have : S = S' := by
        apply Finset.Subset.antisymm _ hS
        intro x hx
        by_contra hn
        have : x ∈ S \ S' := Finset.mem_sdiff.mpr ⟨hx, hn⟩
        rw [h0] at this; simp at this
      subst this
      have h1 := ih k hk S S (Finset.Subset.refl _) (by simp)
      have h2 := lcm_mms_step w hw (k + d) (by omega) S S (Finset.Subset.refl _) (by simp)
      exact le_trans h2 h1


theorem lcm_efx_half {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (X : Fin n → Finset (Fin m)) (hEFX : IsEFX v X) (i j : Fin n)
    (hj : 2 ≤ (X j).card) : v i (X j) ≤ 2 * v i (X i) := by
  classical
  have hc : (2 : ℝ) ≤ ((X j).card : ℝ) := by exact_mod_cast hj
  have hcpos : (0 : ℝ) < ((X j).card : ℝ) := by linarith
  have hg : ∀ g ∈ X j, v i (X j) - v i {g} ≤ v i (X i) := by
    intro g hg
    have h1 := hEFX i j g hg
    have h2 : v i ((X j).erase g) = v i (X j) - v i {g} := by
      rw [hadd.1 i ((X j).erase g), hadd.1 i (X j), Finset.sum_erase_eq_sub hg]
    linarith
  have hsum : ((X j).card : ℝ) * v i (X j) - v i (X j) ≤ ((X j).card : ℝ) * v i (X i) := by
    have h3 : ∑ g ∈ X j, (v i (X j) - v i {g}) ≤ ∑ _g ∈ X j, v i (X i) :=
      Finset.sum_le_sum hg
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
      ← hadd.1 i (X j)] at h3
    exact h3
  have hV : 0 ≤ v i (X j) := hadd.2 i _
  have hW : 0 ≤ v i (X i) := hadd.2 i _
  -- (c-1) V ≤ c W  and c ≥ 2  ⇒  V ≤ 2 W
  nlinarith

theorem lcm_union_le {n m : ℕ} {v : Fin n → Finset (Fin m) → ℝ} (hadd : IsAdditive v) (i : Fin n)
    (A B : Finset (Fin m)) : v i (A ∪ B) ≤ v i A + v i B := by
  classical
  have h := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := fun g => v i {g})
  have h0 : 0 ≤ ∑ g ∈ A ∩ B, v i {g} := Finset.sum_nonneg (fun g _ => hadd.2 i {g})
  rw [hadd.1 i (A ∪ B), hadd.1 i A, hadd.1 i B]
  linarith

theorem lcm_biUnion_le {n m : ℕ} {v : Fin n → Finset (Fin m) → ℝ} (hadd : IsAdditive v) (i : Fin n)
    (X : Fin n → Finset (Fin m)) (T : Finset (Fin n)) :
    v i (T.biUnion X) ≤ ∑ j ∈ T, v i (X j) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.biUnion_empty, Finset.sum_empty]
    rw [hadd.1 i ∅]; simp
  | insert a T ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    exact le_trans (lcm_union_le hadd i _ _) (by linarith)

theorem lcm_sum {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (X : Fin n → Finset (Fin m)) (hEFX : IsEFX v X)
    (hpool : ∀ i, v i (LittleCharity.EFX.pool X) ≤ v i (X i))
    (hsrc : (LittleCharity.EFX.pool X).card < (LittleCharity.EFX.sources v X).card) (i : Fin n)
    (N' : Finset (Fin n))
    (hN' : N' = LittleCharity.EFX.sources v X ∪ {i} ∪ Finset.univ.filter (fun j => 2 ≤ (X j).card)) :
    v i (N'.biUnion X ∪ LittleCharity.EFX.pool X) ≤
      (2 * (N'.card : ℝ) - ((LittleCharity.EFX.pool X).card : ℝ)) * v i (X i) := by
  classical
  set src := LittleCharity.EFX.sources v X with hsrcdef
  set V := v i (X i) with hV
  have hV0 : 0 ≤ V := hadd.2 i _
  have hsrcN : src ⊆ N' := by
    intro x hx; rw [hN']; simp [hx]
  -- per-term bound
  have hterm : ∀ j ∈ N', v i (X j) ≤ 2 * V - (if j ∈ src then V else 0) := by
    intro j hj
    by_cases hjs : j ∈ src
    · have hsj : LittleCharity.EFX.IsSource v X j := by
        simpa [hsrcdef, LittleCharity.EFX.sources] using hjs
      have := hsj i
      simp only [LittleCharity.EFX.Envies, not_lt] at this
      simp only [hjs, if_true]
      linarith
    · simp only [hjs, if_false, sub_zero]
      rw [hN'] at hj
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ,
        true_and] at hj
      rcases hj with (hj | hj) | hj
      · exact absurd hj hjs
      · subst hj; linarith
      · exact lcm_efx_half v hadd X hEFX i j hj
  have h1 := lcm_union_le hadd i (N'.biUnion X) (LittleCharity.EFX.pool X)
  have h2 := lcm_biUnion_le hadd i X N'
  have h3 : ∑ j ∈ N', v i (X j) ≤ ∑ j ∈ N', (2 * V - (if j ∈ src then V else 0)) :=
    Finset.sum_le_sum hterm
  have h4 : ∑ j ∈ N', (2 * V - (if j ∈ src then V else 0)) = 2 * V * N'.card - V * src.card := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have : ∑ j ∈ N', (if j ∈ src then V else 0) = V * src.card := by
      have hf : N'.filter (fun j => j ∈ src) = src := by
        ext x; simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hsrcN h, h⟩⟩
      rw [← Finset.sum_filter, Finset.sum_const, hf, nsmul_eq_mul, mul_comm]
    rw [this]; ring
  have h5 : v i (LittleCharity.EFX.pool X) ≤ V := hpool i
  have hk : ((LittleCharity.EFX.pool X).card : ℝ) + 1 ≤ (src.card : ℝ) := by exact_mod_cast hsrc
  nlinarith

theorem lcm_prop13 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (N N' : Finset (Fin n)) (M M' : Finset (Fin m)) (hN : N' ⊆ N) (hM : M' ⊆ M)
    (hcard : (M \ M').card ≤ (N \ N').card) (i : Fin n) (hi : i ∈ N') :
    mms (v i) N.card M ≤ mms (v i) N'.card M' := by
  have hpos : 1 ≤ N'.card := Finset.card_pos.mpr ⟨i, hi⟩
  have hsum : N.card = N'.card + (N \ N').card := by
    have := Finset.card_sdiff_add_card_eq_card hN
    omega
  rw [hsum]
  exact lcm_mms_remove (v i) (fun A B h => lcm_add_mono hadd i h) _ _ hpos M M' hM hcard

theorem lcm_mms_avg {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (i : Fin n) (k : ℕ) (hk : 0 < k) (S : Finset (Fin m)) :
    mms (v i) k S ≤ v i S / (k : ℝ) := by
  classical
  haveI : NeZero k := ⟨hk.ne'⟩
  unfold mms
  apply ciSup_le
  intro f
  set a : Fin k → ℝ := fun j => v i (S.filter (fun g => f g = j)) with ha
  have hsum : ∑ j : Fin k, a j = v i S := by
    rw [hadd.1 i S]
    have : ∀ j : Fin k, a j = ∑ g ∈ S.filter (fun g => f g = j), v i {g} := fun j => hadd.1 i _
    simp_rw [this]
    exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
  have hle : ∀ j, (⨅ j', a j') ≤ a j := fun j => ciInf_le (Set.finite_range _).bddBelow j
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [le_div_iff₀ hk']
  calc (⨅ j', a j') * k = ∑ _j : Fin k, (⨅ j', a j') := by simp [mul_comm]
    _ ≤ ∑ j, a j := Finset.sum_le_sum (fun j _ => hle j)
    _ = v i S := hsum

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (X : Fin n → Finset (Fin m)) (hX : LittleCharity.EFX.IsPartialAllocation X) (hEFX : IsEFX v X)
    (hpool : ∀ i, v i (LittleCharity.EFX.pool X) ≤ v i (X i))
    (hsrc : (LittleCharity.EFX.pool X).card < (LittleCharity.EFX.sources v X).card) (i : Fin n) :
    mms (v i) n Finset.univ / (2 - ((LittleCharity.EFX.pool X).card : ℝ) / (n : ℝ)) ≤ v i (X i) := by
  classical
  set P := LittleCharity.EFX.pool X with hP
  set src := LittleCharity.EFX.sources v X with hsrcdef
  set N' : Finset (Fin n) :=
    src ∪ {i} ∪ Finset.univ.filter (fun j => 2 ≤ (X j).card) with hN'
  have hiN' : i ∈ N' := by simp [hN']
  have hsum := lcm_sum v hadd X hEFX hpool hsrc i N' hN'
  set M' : Finset (Fin m) := N'.biUnion X ∪ P with hM'
  have hn' : 1 ≤ N'.card := Finset.card_pos.mpr ⟨i, hiN'⟩
  have hn'n : N'.card ≤ n := by
    have := Finset.card_le_univ N'
    simpa using this
  have hkn : P.card < n := by
    have := Finset.card_le_univ src
    simp only [Fintype.card_fin] at this
    omega
  -- Proposition 13 for N = univ, N', M = univ, M'
  have hcard : (Finset.univ \ M').card ≤ (Finset.univ \ N').card := by
    have hsub : Finset.univ \ M' ⊆ (Finset.univ \ N').biUnion X := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      have hxM : x ∉ N'.biUnion X ∪ P := hx.2
      rw [Finset.mem_union, not_or] at hxM
      obtain ⟨hx1, hx2⟩ := hxM
      have hxu : x ∈ Finset.univ.biUnion X := by
        by_contra hn
        apply hx2
        rw [hP]
        unfold LittleCharity.EFX.pool
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩
      rw [Finset.mem_biUnion] at hxu
      obtain ⟨j, -, hj⟩ := hxu
      rw [Finset.mem_biUnion]
      refine ⟨j, ?_, hj⟩
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_univ _, fun hjN => hx1 (Finset.mem_biUnion.mpr ⟨j, hjN, hj⟩)⟩
    refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
    calc ∑ j ∈ Finset.univ \ N', (X j).card ≤ ∑ _j ∈ Finset.univ \ N', 1 := by
          apply Finset.sum_le_sum
          intro j hj
          have hjN : j ∉ N' := (Finset.mem_sdiff.mp hj).2
          have h2 : ¬ (2 ≤ (X j).card) := by
            intro h2; apply hjN; rw [hN']; simp [h2]
          omega
      _ = (Finset.univ \ N').card := by simp
  have hp13 := lcm_prop13 v hadd Finset.univ N' Finset.univ M' (Finset.subset_univ _)
    (Finset.subset_univ _) hcard i hiN'
  have havg := lcm_mms_avg v hadd i N'.card (by omega) M'
  rw [Finset.card_univ, Fintype.card_fin] at hp13
  -- numeric part
  have hV : 0 ≤ v i (X i) := hadd.2 i _
  have hn'r : (1 : ℝ) ≤ N'.card := by exact_mod_cast hn'
  have hn'nr : (N'.card : ℝ) ≤ n := by exact_mod_cast hn'n
  have hnpos : (0 : ℝ) < n := by linarith
  have hkr : (P.card : ℝ) < n := by exact_mod_cast hkn
  have hk0 : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  have hden : (0 : ℝ) < 2 - (P.card : ℝ) / n := by
    have : (P.card : ℝ) / n < 1 := (div_lt_one hnpos).mpr hkr
    linarith
  rw [div_le_iff₀ hden]
  have h1 : mms (v i) N'.card M' ≤ (2 - (P.card : ℝ) / N'.card) * v i (X i) := by
    refine le_trans havg ?_
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < N'.card)]
    have : (2 - (P.card : ℝ) / N'.card) * v i (X i) * N'.card
        = (2 * (N'.card : ℝ) - P.card) * v i (X i) := by
      field_simp
    rw [this]; exact hsum
  have h2 : (P.card : ℝ) / n ≤ (P.card : ℝ) / N'.card :=
    div_le_div_of_nonneg_left hk0 (by linarith) hn'nr
  have h3 : (2 - (P.card : ℝ) / N'.card) * v i (X i) ≤ v i (X i) * (2 - (P.card : ℝ) / n) := by
    nlinarith
  linarith
