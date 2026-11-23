-- Prove2me | solution 1 for ImplicitParityWL.lemma_4_12
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:31:44.397487+00:00
-- url     : https://prove2.me/submissions/fb78c287-fd25-4140-ad5d-a77e6da010a3

import Mathlib
import Definitions.Def_ImplicitParityWL_Address
import Theorems.Thm_ImplicitParityWL_lemma_4_6

open ImplicitParityWL

namespace Aux_lemma_4_12

lemma zmod2_eq_zero_or_one : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide

lemma word_dot_eq_sum_supp {k ℓ : ℕ} (x z : Word k ℓ) :
    x.dot z = ∑ c ∈ x.supp, z c := by
  unfold Word.dot Word.supp
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  rcases zmod2_eq_zero_or_one (x c) with h | h <;> simp [h]

lemma dot_congr_supp {k ℓ : ℕ} {x z₁ z₂ : Word k ℓ} {S : Finset (Coord k ℓ)}
    (hx : x.supp ⊆ S) (hz : ∀ c ∈ S, z₁ c = z₂ c) : x.dot z₁ = x.dot z₂ := by
  rw [word_dot_eq_sum_supp, word_dot_eq_sum_supp]
  exact Finset.sum_congr rfl (fun c hc => hz c (hx hc))

lemma dot_add_left {k ℓ : ℕ} (x y z : Word k ℓ) :
    (x + y).dot z = x.dot z + y.dot z := by
  unfold Word.dot
  simp [add_mul, Finset.sum_add_distrib]

lemma isBlockEven_add {k ℓ : ℕ} {x y : Word k ℓ}
    (hx : x.IsBlockEven) (hy : y.IsBlockEven) : (x + y).IsBlockEven := by
  have hbp : ∀ i : Fin k, (x + y).blockParity i = 0 := by
    intro i
    have h1 := hx.2 i
    have h2 := hy.2 i
    unfold Word.blockParity at h1 h2 ⊢
    simp only [Pi.add_apply, Finset.sum_add_distrib, h1, h2, add_zero]
  refine ⟨⟨fun i j => by rw [hbp i, hbp j], ?_⟩, hbp⟩
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  rw [hx.1.checksum, hy.1.checksum, add_zero]

lemma step_even {k ℓ : ℕ} (S : Finset (Coord k ℓ)) (c₀ : Coord k ℓ) (hc₀ : c₀ ∉ S)
    (z : Word k ℓ) (hz : ∀ x : Word k ℓ, x.IsBlockEven → x.supp ⊆ S → x.dot z = 0) :
    ∃ z' : Word k ℓ, (∀ c ∈ S, z' c = z c) ∧
      ∀ x : Word k ℓ, x.IsBlockEven → x.supp ⊆ insert c₀ S → x.dot z' = 0 := by
  classical
  by_cases hex : ∃ x₀ : Word k ℓ, x₀.IsBlockEven ∧ x₀.supp ⊆ insert c₀ S ∧ x₀ c₀ = 1
  · obtain ⟨x₀, hx₀_even, hx₀_supp, hx₀_c₀⟩ := hex
    let b₀ : ZMod 2 := ∑ c ∈ x₀.supp.erase c₀, z c
    let z' : Word k ℓ := Function.update z c₀ b₀
    have hz'_S : ∀ c ∈ S, z' c = z c := by
      intro c hc
      have hne : c ≠ c₀ := fun h => hc₀ (h ▸ hc)
      simp [z', hne]
    have hx₀_mem : c₀ ∈ x₀.supp := by
      simp [Word.supp, hx₀_c₀]
    have hx₀_dot : x₀.dot z' = 0 := by
      rw [word_dot_eq_sum_supp, ← Finset.add_sum_erase _ _ hx₀_mem]
      have hrest : ∑ c ∈ x₀.supp.erase c₀, z' c = b₀ := by
        apply Finset.sum_congr rfl
        intro c hc
        have hmem := Finset.mem_erase.mp hc
        have hS : c ∈ S := by
          have := hx₀_supp hmem.2
          simp only [Finset.mem_insert] at this
          exact this.resolve_left hmem.1
        exact hz'_S c hS
      simp only [z', Function.update_self, hrest]
      exact CharTwo.add_self_eq_zero b₀
    refine ⟨z', hz'_S, ?_⟩
    intro x hx_even hx_supp
    rcases zmod2_eq_zero_or_one (x c₀) with h0 | h1
    · have hxS : x.supp ⊆ S := by
        intro c hc
        have hins := hx_supp hc
        simp only [Finset.mem_insert] at hins
        rcases hins with rfl | hS
        · simp [Word.supp, h0] at hc
        · exact hS
      rw [dot_congr_supp hxS hz'_S]
      exact hz x hx_even hxS
    · have hsum_even : (x + x₀).IsBlockEven := isBlockEven_add hx_even hx₀_even
      have hsum_supp : (x + x₀).supp ⊆ S := by
        intro c hc
        simp only [Word.supp, Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply] at hc
        by_cases hcc : c = c₀
        · subst hcc
          rw [h1, hx₀_c₀] at hc
          exact absurd hc (by decide)
        · have hor : c ∈ x.supp ∨ c ∈ x₀.supp := by
            by_contra hnor
            push_neg at hnor
            simp only [Word.supp, Finset.mem_filter, Finset.mem_univ, true_and] at hnor
            rcases zmod2_eq_zero_or_one (x c) with hxc | hxc <;>
              rcases zmod2_eq_zero_or_one (x₀ c) with hx₀c | hx₀c <;>
              simp_all
          rcases hor with hmem | hmem
          · exact (Finset.mem_insert.mp (hx_supp hmem)).resolve_left hcc
          · exact (Finset.mem_insert.mp (hx₀_supp hmem)).resolve_left hcc
      have hsum_dot : (x + x₀).dot z' = 0 := by
        rw [dot_congr_supp hsum_supp hz'_S]
        exact hz (x + x₀) hsum_even hsum_supp
      rw [dot_add_left, hx₀_dot, add_zero] at hsum_dot
      exact hsum_dot
  · refine ⟨z, fun _ _ => rfl, ?_⟩
    push_neg at hex
    intro x hx_even hx_supp
    have h0 : x c₀ = 0 := by
      rcases zmod2_eq_zero_or_one (x c₀) with h | h
      · exact h
      · exact False.elim (hex x hx_even hx_supp h)
    have hxS : x.supp ⊆ S := by
      intro c hc
      rcases Finset.mem_insert.mp (hx_supp hc) with rfl | hS
      · simp [Word.supp, h0] at hc
      · exact hS
    exact hz x hx_even hxS

lemma ext_even {k ℓ : ℕ} : ∀ (n : ℕ) (S T : Finset (Coord k ℓ)), S ⊆ T → (T \ S).card = n →
    ∀ (z : Word k ℓ), (∀ x : Word k ℓ, x.IsBlockEven → x.supp ⊆ S → x.dot z = 0) →
    ∃ z' : Word k ℓ, (∀ c ∈ S, z' c = z c) ∧
      ∀ x : Word k ℓ, x.IsBlockEven → x.supp ⊆ T → x.dot z' = 0
  | 0, S, T, hST, hcard, z, hz => by
    have hEq : S = T := by
      have hEmpty : T \ S = ∅ := Finset.card_eq_zero.mp hcard
      have hTS : T ⊆ S := Finset.sdiff_eq_empty_iff_subset.mp hEmpty
      exact Finset.Subset.antisymm hST hTS
    subst hEq
    exact ⟨z, fun _ _ => rfl, hz⟩
  | n + 1, S, T, hST, hcard, z, hz => by
    classical
    have hne : (T \ S).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨c₀, hc₀⟩ := hne
    have hc₀T : c₀ ∈ T := (Finset.mem_sdiff.mp hc₀).1
    have hc₀S : c₀ ∉ S := (Finset.mem_sdiff.mp hc₀).2
    obtain ⟨z₁, hz₁S, hz₁_even⟩ := step_even S c₀ hc₀S z hz
    have hins_sub : insert c₀ S ⊆ T := Finset.insert_subset_iff.mpr ⟨hc₀T, hST⟩
    have hcard' : (T \ insert c₀ S).card = n := by
      have : T \ insert c₀ S = (T \ S).erase c₀ := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or]
        tauto
      rw [this, Finset.card_erase_of_mem hc₀]
      omega
    obtain ⟨z', hz'1, hz'_even⟩ := ext_even n (insert c₀ S) T hins_sub hcard' z₁ hz₁_even
    refine ⟨z', fun c hc => (hz'1 c (Finset.mem_insert_of_mem hc)).trans (hz₁S c hc), hz'_even⟩

lemma address_word_blockParity {k ℓ : ℕ} (a : Address k ℓ) (i : Fin k) :
    a.word.blockParity i = 1 := by
  classical
  unfold Word.blockParity Address.word
  simp

lemma address_word_checksum {k ℓ : ℕ} (a : Address k ℓ) :
    ∑ c : Coord k ℓ, a.word c • c.2 = 0 := by
  classical
  unfold Address.word
  rw [Fintype.sum_prod_type]
  have hrow : ∀ i : Fin k, (∑ b : BlockCoord ℓ, (if b = a.1 i then (1 : ZMod 2) else 0) • b) = a.1 i := by
    intro i
    simp
  simp_rw [hrow]
  exact a.2

lemma even_eq_zero_of_address_in_T {k ℓ : ℕ} (hk : 3 ≤ k) (hℓ : 1 ≤ ℓ)
    {T : Finset (Coord k ℓ)} (hT : T.card ≤ k + 1)
    {a : Address k ℓ} (ha : a.supp ⊆ T) {x : Word k ℓ}
    (hx_even : x.IsBlockEven) (hxT : x.supp ⊆ T) : x = 0 := by
  classical
  let y : Word k ℓ := a.word + x
  have hy_supp : y.supp ⊆ T := by
    intro c hc
    simp only [y, Word.supp, Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply] at hc
    by_cases hxa : a.word c = 1
    · apply ha
      unfold Address.word at hxa
      split_ifs at hxa with h
      · unfold Address.supp
        exact Finset.mem_image.mpr ⟨c.1, Finset.mem_univ _, Prod.ext rfl h.symm⟩
      · exact absurd hxa (by decide)
    · have ha0 : a.word c = 0 := (zmod2_eq_zero_or_one (a.word c)).resolve_right hxa
      rw [ha0, zero_add] at hc
      exact hxT (by simp [Word.supp, hc])
  have hy_bp : ∀ i : Fin k, y.blockParity i = 1 := by
    intro i
    unfold Word.blockParity
    simp only [y, Pi.add_apply, Finset.sum_add_distrib]
    have h1 := address_word_blockParity a i
    have h2 := hx_even.2 i
    unfold Word.blockParity at h1 h2
    rw [h1, h2, add_zero]
  let B : Fin k → Finset (BlockCoord ℓ) := fun i => Finset.univ.filter (fun b => y (i, b) = 1)
  have hB_parity : ∀ i : Fin k, ((B i).card : ZMod 2) = 1 := by
    intro i
    have h := hy_bp i
    unfold Word.blockParity at h
    rw [← h]
    simp only [B, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    rcases zmod2_eq_zero_or_one (y (i, b)) with hyb | hyb <;> simp [hyb]
  have hB_ge1 : ∀ i : Fin k, 1 ≤ (B i).card := by
    intro i
    by_contra h0
    have h0' : (B i).card = 0 := by omega
    have hp := hB_parity i
    rw [h0'] at hp
    exact absurd hp (by decide)
  have hB_sum_le : ∑ i : Fin k, (B i).card ≤ k + 1 := by
    have hEq : ∑ i : Fin k, (B i).card = y.supp.card := by
      unfold Word.supp
      rw [← Finset.card_sigma]
      refine Finset.card_bij (fun p _ => (p.1, p.2)) ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_sigma, Finset.mem_univ, true_and, B, Finset.mem_filter] at hp
        simp [hp]
      · intro p₁ _ p₂ _ h
        rcases Prod.mk.inj h with ⟨h1, h2⟩
        cases p₁; cases p₂
        simp only at h1 h2
        subst h1; subst h2; rfl
      · intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        exact ⟨⟨c.1, c.2⟩, by simp [B, hc], rfl⟩
    rw [hEq]
    exact le_trans (Finset.card_le_card hy_supp) hT
  have hB_eq1 : ∀ i : Fin k, (B i).card = 1 := by
    intro i₀
    have hge1 := hB_ge1 i₀
    by_contra hne1
    have hne2 : (B i₀).card ≠ 2 := by
      intro h2
      have hp := hB_parity i₀
      rw [h2] at hp
      exact absurd hp (by decide)
    have hge3 : 3 ≤ (B i₀).card := by omega
    have hrest : k - 1 ≤ ∑ i ∈ Finset.univ.erase i₀, (B i).card := by
      calc k - 1 = (Finset.univ.erase i₀).card := by simp
        _ = ∑ _i ∈ Finset.univ.erase i₀, 1 := by simp
        _ ≤ ∑ i ∈ Finset.univ.erase i₀, (B i).card :=
            Finset.sum_le_sum (fun i _ => hB_ge1 i)
    have htot := Finset.add_sum_erase Finset.univ (fun i => (B i).card) (Finset.mem_univ i₀)
    omega
  have hB_uniq : ∀ i : Fin k, ∃ b : BlockCoord ℓ, B i = {b} :=
    fun i => Finset.card_eq_one.mp (hB_eq1 i)
  let b : Fin k → BlockCoord ℓ := fun i => Classical.choose (hB_uniq i)
  have hb_spec : ∀ i : Fin k, B i = {b i} := fun i => Classical.choose_spec (hB_uniq i)
  have hy_val : ∀ (i : Fin k) (v : BlockCoord ℓ), y (i, v) = if v = b i then 1 else 0 := by
    intro i v
    have hmem : v ∈ B i ↔ v = b i := by rw [hb_spec i, Finset.mem_singleton]
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    split_ifs with hv
    · exact hmem.mpr hv
    · exact (zmod2_eq_zero_or_one (y (i, v))).resolve_right (mt hmem.mp hv)
  have hb_sum : ∑ i : Fin k, b i = 0 := by
    have hchk : ∑ c : Coord k ℓ, y c • c.2 = 0 := by
      simp only [y, Pi.add_apply, add_smul, Finset.sum_add_distrib]
      rw [address_word_checksum a, hx_even.1.checksum, add_zero]
    rw [Fintype.sum_prod_type] at hchk
    have hrow : ∀ i : Fin k, (∑ v : BlockCoord ℓ, y (i, v) • v) = b i := by
      intro i
      simp_rw [hy_val i]
      simp
    simp_rw [hrow] at hchk
    exact hchk
  let a' : Address k ℓ := ⟨b, hb_sum⟩
  have ha'_word : a'.word = y := by
    ext ⟨i, v⟩
    rw [hy_val i v]
    rfl
  have ha'_supp : a'.supp ⊆ T := by
    intro c hc
    apply hy_supp
    unfold Address.supp at hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
    simp [Word.supp, ← ha'_word, Address.word]
  have ha_eq : a = a' :=
    (ImplicitParityWL.lemma_4_6 k ℓ hk hℓ).2 T hT a a' ha ha'_supp
  ext c
  have h : a.word c = y c := by rw [ha_eq, ha'_word]
  simp only [y, Pi.add_apply] at h
  have : a.word c + x c = a.word c + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

end Aux_lemma_4_12

theorem solution (k ℓ : ℕ) (hk : 3 ≤ k) (hℓ : 1 ≤ ℓ) (S T : Finset (Coord k ℓ)) (hST : S ⊆ T)
    (hT : T.card ≤ k + 1) (z : Word k ℓ)
    (hz : ∀ x : Word k ℓ, x.IsBlockEven → x.supp ⊆ S → x.dot z = 0) :
    (∃ z' : Word k ℓ, (∀ c ∈ S, z' c = z c) ∧
      ∀ x : Word k ℓ, x.IsBlockEven → x.supp ⊆ T → x.dot z' = 0) ∧
    (∀ (a : Address k ℓ) (β : ZMod 2), a.supp ⊆ T → (a.supp ⊆ S → a.dot z = β) →
      ∃ z' : Word k ℓ, (∀ c ∈ S, z' c = z c) ∧
        (∀ x : Word k ℓ, x.IsBlockEven → x.supp ⊆ T → x.dot z' = 0) ∧ a.dot z' = β) := by
  classical
  refine ⟨Aux_lemma_4_12.ext_even (T \ S).card S T hST rfl z hz, ?_⟩
  intro a β haT haS
  have heven0 : ∀ x : Word k ℓ, x.IsBlockEven → x.supp ⊆ T → ∀ z' : Word k ℓ, x.dot z' = 0 := by
    intro x hx hxT z'
    have hx0 := Aux_lemma_4_12.even_eq_zero_of_address_in_T hk hℓ hT haT hx hxT
    subst hx0
    simp [Word.dot]
  by_cases hsub : a.supp ⊆ S
  · exact ⟨z, fun _ _ => rfl, fun x hx hxT => heven0 x hx hxT z, haS hsub⟩
  · have hne : (a.supp \ S).Nonempty := Finset.nonempty_iff_ne_empty.mpr
      (fun h => hsub (Finset.sdiff_eq_empty_iff_subset.mp h))
    obtain ⟨c₀, hc₀⟩ := hne
    have hc₀_a : c₀ ∈ a.supp := (Finset.mem_sdiff.mp hc₀).1
    have hc₀_S : c₀ ∉ S := (Finset.mem_sdiff.mp hc₀).2
    let rest : ZMod 2 := ∑ c ∈ a.supp.erase c₀, z c
    let z' : Word k ℓ := Function.update z c₀ (β - rest)
    have hz'S : ∀ c ∈ S, z' c = z c := by
      intro c hc
      have hne_c : c ≠ c₀ := fun h => hc₀_S (h ▸ hc)
      simp [z', hne_c]
    have hdot_a : a.dot z' = β := by
      unfold Address.dot
      rw [← Finset.add_sum_erase _ _ hc₀_a]
      have hsum_rest : ∑ c ∈ a.supp.erase c₀, z' c = rest := by
        apply Finset.sum_congr rfl
        intro c hc
        have hne_c : c ≠ c₀ := (Finset.mem_erase.mp hc).1
        simp [z', hne_c]
      simp [z', hsum_rest]
    exact ⟨z', hz'S, fun x hx hxT => heven0 x hx hxT z', hdot_a⟩
