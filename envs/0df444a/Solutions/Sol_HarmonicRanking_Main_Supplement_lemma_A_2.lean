-- Prove2me | solution 1 for HarmonicRanking.Main.Supplement.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T17:32:35.191597+00:00
-- url     : https://prove2.me/submissions/2b34477b-912e-4d85-b5f9-6583e9d2df3d

import Definitions.Def_HarmonicRanking_Main_Supplement_GridGames

set_option autoImplicit false

namespace HarmonicRanking.Main.Supplement

def cntA2 {m : ℕ} (c : Fin (m + 1) → Fin (m + 1)) (r : Fin m) : ℝ :=
  ((Finset.univ.filter fun j : Fin m => r.val < (c j.castSucc).val).card : ℝ)

lemma cntA2_nonneg {m : ℕ} (c : Fin (m + 1) → Fin (m + 1)) (r : Fin m) : 0 ≤ cntA2 c r := by
  unfold cntA2; positivity

lemma ell_eqA2 {m : ℕ} (c : Fin (m + 1) → Fin (m + 1)) (hc : IsPath c) (i : Fin m) :
    ell c i = cntA2 c i / m := by
  have hm : (0:ℝ) < m := by exact_mod_cast Fin.pos i
  set S : Set ℕ := {k : ℕ | ∃ hk : k < m + 1, i.val < (c ⟨k, hk⟩).val} with hS
  have hlast : c ⟨m, by omega⟩ = Fin.last m := hc.2
  have hne : S.Nonempty := ⟨m, by omega, by rw [hlast]; simpa using i.isLt⟩
  have hpmem : sInf S ∈ S := Nat.sInf_mem hne
  obtain ⟨hp, hip⟩ := hpmem
  have hfil : (Finset.univ.filter fun j : Fin m => i.val < (c j.castSucc).val)
      = Finset.univ.filter fun j : Fin m => sInf S ≤ j.val := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      by_contra hlt
      push Not at hlt
      exact Nat.notMem_of_lt_sInf hlt ⟨by omega, h⟩
    · intro h
      have : c ⟨sInf S, hp⟩ ≤ c j.castSucc := hc.1 (by
        show sInf S ≤ j.val
        exact h)
      exact lt_of_lt_of_le hip (by exact_mod_cast this)
  have hcard : (Finset.univ.filter fun j : Fin m => sInf S ≤ j.val).card = m - sInf S := by
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun j : Fin m => j.val < sInf S)
    have h2 : (Finset.univ.filter fun j : Fin m => j.val < sInf S).card = min m (sInf S) := by
      rw [← Fin.card_filter_val_lt]
    simp only [not_lt, Finset.card_univ, Fintype.card_fin] at h1
    omega
  unfold ell cntA2 pathInv
  rw [hfil, hcard]
  rw [Nat.cast_sub (by omega)]
  field_simp
  rfl

lemma gAt_succ {m : ℕ} (g : Fin m → Fin m → ℝ) (i j : Fin m) :
    gAt g i (j.val + 1) = g i j := by
  unfold gAt
  rw [dif_pos ⟨by omega, by have := j.isLt; omega⟩]
  rfl

lemma gAt_zero {m : ℕ} (g : Fin m → Fin m → ℝ) (i : Fin m) : gAt g i 0 = 0 := by
  unfold gAt; simp

lemma gAt_mono {m : ℕ} (g : Fin m → Fin m → ℝ) (hg : IsKTable g) (i : Fin m) (k : ℕ)
    (hk : k + 1 ≤ m) : gAt g i k ≤ gAt g i (k + 1) := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h
    rw [gAt_zero]
    have := gAt_succ g i ⟨0, by omega⟩
    simp only [zero_add] at this ⊢
    rw [this]
    exact hg.1 i
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [gAt_succ g i ⟨k', by omega⟩, gAt_succ g i ⟨k' + 1, by omega⟩]
    exact hg.2.1 i (by show k' ≤ k' + 1; omega)

lemma gAt_comp {m : ℕ} (g : Fin m → Fin m → ℝ) (hg : IsKTable g) (i j : Fin m) :
    gAt g i (j.val + 1) + gAt g j (i.val + 1) = 1 := by
  rw [gAt_succ, gAt_succ]; exact hg.2.2 i j

lemma gAt_anti {m : ℕ} (g : Fin m → Fin m → ℝ) (hg : IsKTable g) (i e j : Fin m)
    (hie : i ≤ e) : gAt g e (j.val + 1) ≤ gAt g i (j.val + 1) := by
  rw [gAt_succ, gAt_succ]
  have h1 := hg.2.2 e j
  have h2 := hg.2.2 i j
  have h3 : g j i ≤ g j e := hg.2.1 j hie
  linarith

lemma phi_mulA2 {m : ℕ} (hm : 1 ≤ m) (g : Fin m → Fin m → ℝ) (c d : Fin (m + 1) → Fin (m + 1))
    (hc : IsPath c) (hd : IsPath d) :
    (m : ℝ) ^ 2 * Phi g c d = (m : ℝ) ^ 2
      + ∑ r : Fin m, ((d r.castSucc).val * (gAt g r (d r.castSucc).val - 1) )
      + ∑ r : Fin m, ((c r.castSucc).val * (gAt g r (c r.castSucc).val - 1)
          + cntA2 d r * gAt g r (c r.castSucc).val + cntA2 c r * gAt g r (d r.castSucc).val) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  unfold Phi
  have h2 : ∑ i : Fin m, (ell d i * gAt g i (c i.castSucc).val + ell c i * gAt g i (d i.castSucc).val)
      = (∑ i : Fin m, (cntA2 d i * gAt g i (c i.castSucc).val + cntA2 c i * gAt g i (d i.castSucc).val)) / m := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [ell_eqA2 c hc, ell_eqA2 d hd]; ring
  rw [h2]
  have h3 : ∑ i : Fin m, (((c i.castSucc).val : ℝ) * (gAt g i (c i.castSucc).val - 1) +
          ((d i.castSucc).val : ℝ) * (gAt g i (d i.castSucc).val - 1))
      = ∑ r : Fin m, (((c r.castSucc).val : ℝ) * (gAt g r (c r.castSucc).val - 1))
        + ∑ r : Fin m, ((d r.castSucc).val * (gAt g r (d r.castSucc).val - 1) ) := by
    rw [← Finset.sum_add_distrib]
  have h4 : ∑ r : Fin m, ((c r.castSucc).val * (gAt g r (c r.castSucc).val - 1)
          + cntA2 d r * gAt g r (c r.castSucc).val + cntA2 c r * gAt g r (d r.castSucc).val)
      = ∑ r : Fin m, (((c r.castSucc).val : ℝ) * (gAt g r (c r.castSucc).val - 1))
        + ∑ i : Fin m, (cntA2 d i * gAt g i (c i.castSucc).val + cntA2 c i * gAt g i (d i.castSucc).val) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [h3, h4]
  field_simp
  ring

def tA2 {m : ℕ} (g : Fin m → Fin m → ℝ) (d cc : Fin (m + 1) → Fin (m + 1)) (r : Fin m) : ℝ :=
  (cc r.castSucc).val * (gAt g r (cc r.castSucc).val - 1)
    + cntA2 d r * gAt g r (cc r.castSucc).val + cntA2 cc r * gAt g r (d r.castSucc).val

lemma cnt_upd_ne {m : ℕ} (c : Fin (m + 1) → Fin (m + 1)) (i s' r : Fin m)
    (hs : s'.val + 1 = (c i.castSucc).val) (hr : r ≠ s') :
    cntA2 (Function.update c i.castSucc ⟨s'.val, by omega⟩) r = cntA2 c r := by
  unfold cntA2
  congr 2
  apply Finset.filter_congr
  intro j _
  rw [Function.update_apply]
  by_cases hj : j = i
  · subst hj
    simp only [if_true]
    have : r.val ≠ s'.val := fun h => hr (Fin.ext h)
    omega
  · have : j.castSucc ≠ i.castSucc := fun h => hj (Fin.castSucc_injective _ h)
    simp [this]

lemma cnt_upd_eq {m : ℕ} (c : Fin (m + 1) → Fin (m + 1)) (i s' : Fin m)
    (hs : s'.val + 1 = (c i.castSucc).val) :
    cntA2 (Function.update c i.castSucc ⟨s'.val, by omega⟩) s' = cntA2 c s' - 1 := by
  unfold cntA2
  have hmem : i ∈ Finset.univ.filter fun j : Fin m => s'.val < (c j.castSucc).val := by
    simp; omega
  have hset : (Finset.univ.filter fun j : Fin m =>
      s'.val < (Function.update c i.castSucc (⟨s'.val, by omega⟩ : Fin (m+1)) j.castSucc).val)
      = (Finset.univ.filter fun j : Fin m => s'.val < (c j.castSucc).val).erase i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, Function.update_apply]
    by_cases hj : j = i
    · subst hj; simp
    · have : j.castSucc ≠ i.castSucc := fun h => hj (Fin.castSucc_injective _ h)
      simp [this, hj]
  rw [hset, Finset.card_erase_of_mem hmem]
  have : 0 < (Finset.univ.filter fun j : Fin m => s'.val < (c j.castSucc).val).card :=
    Finset.card_pos.mpr ⟨i, hmem⟩
  rw [Nat.cast_sub (by omega)]; simp

lemma stepA2 {m : ℕ} (hm : 1 ≤ m) (g : Fin m → Fin m → ℝ) (hg : IsKTable g)
    (c d : Fin (m + 1) → Fin (m + 1)) (hc : IsPath c) (hd : IsPath d) (k r : Fin m)
    (h1 : r.val + 1 ≤ (c k.castSucc).val) (h2 : k.val + 1 ≤ (d r.castSucc).val) :
    ∃ c' : Fin (m + 1) → Fin (m + 1), IsPath c' ∧
      ∑ j, (c' j).val < ∑ j, (c j).val ∧ Phi g c' d ≤ Phi g c d := by
  have hsm : (c k.castSucc).val ≤ m := by have := (c k.castSucc).isLt; omega
  obtain ⟨s', hs'⟩ : ∃ s' : Fin m, s'.val + 1 = (c k.castSucc).val := ⟨⟨(c k.castSucc).val - 1, by omega⟩, by simp; omega⟩
  obtain ⟨i, hi, hmin⟩ : ∃ i : Fin m, c i.castSucc = c k.castSucc ∧
      ∀ j : Fin m, c j.castSucc = c k.castSucc → i ≤ j := by
    have hne : (Finset.univ.filter fun j : Fin m => c j.castSucc = c k.castSucc).Nonempty :=
      ⟨k, by simp⟩
    refine ⟨(Finset.univ.filter fun j : Fin m => c j.castSucc = c k.castSucc).min' hne, ?_, ?_⟩
    · exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
    · intro j hj
      exact Finset.min'_le _ _ (by simpa using hj)
  have hsi : s'.val + 1 = (c i.castSucc).val := by rw [hi]; exact hs'
  have hik : i ≤ k := hmin k rfl
  let v : Fin (m + 1) := ⟨s'.val, by omega⟩
  obtain ⟨c', hc'⟩ : ∃ c', c' = Function.update c i.castSucc v := ⟨_, rfl⟩
  have hc'x : ∀ x, c' x = if x = i.castSucc then v else c x := by
    intro x; rw [hc', Function.update_apply]
  have hc'le : ∀ x, c' x ≤ c x := by
    intro x
    rw [hc'x]
    split_ifs with h
    · subst h
      show s'.val ≤ _
      omega
    · exact le_refl _
  have hpath : IsPath c' := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      rw [hc'x x, hc'x y]
      by_cases hx : x = i.castSucc <;> by_cases hy : y = i.castSucc
      · simp [hx, hy]
      · simp only [hx, hy, if_true, if_false]
        have h3 : c i.castSucc ≤ c y := by rw [← hx]; exact hc.1 hxy
        show s'.val ≤ _
        have : (c i.castSucc).val ≤ (c y).val := h3
        omega
      · simp only [hx, hy, if_true, if_false]
        have hlt : x < i.castSucc := by rw [hy] at hxy; exact lt_of_le_of_ne hxy hx
        have hxv : x.val < i.val := hlt
        have hxm : x.val < m := by have := i.isLt; omega
        have h3 : c x ≤ c i.castSucc := hc.1 hlt.le
        have h4 : c x ≠ c i.castSucc := by
          intro h5
          have := hmin ⟨x.val, hxm⟩ (by
            have : (⟨x.val, hxm⟩ : Fin m).castSucc = x := Fin.ext rfl
            rw [this, h5, hi])
          have : i.val ≤ x.val := this
          omega
        have h6 : (c x).val < (c i.castSucc).val := lt_of_le_of_ne h3 (fun h => h4 (Fin.ext h))
        show (c x).val ≤ s'.val
        omega
      · simp only [hx, hy, if_false]; exact hc.1 hxy
    · rw [hc'x]
      have : Fin.last m ≠ i.castSucc := (Fin.castSucc_lt_last i).ne'
      simp [this]; exact hc.2
  refine ⟨c', hpath, ?_, ?_⟩
  · apply Finset.sum_lt_sum
    · intro x _; exact hc'le x
    · refine ⟨i.castSucc, Finset.mem_univ _, ?_⟩
      rw [hc'x]; simp only [if_true]
      show s'.val < _
      omega
  · -- the Φ comparison
    have hmpos : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    suffices hkey : (m : ℝ) ^ 2 * Phi g c' d ≤ (m : ℝ) ^ 2 * Phi g c d from
      le_of_mul_le_mul_left hkey hmpos
    rw [phi_mulA2 hm g c' d hpath hd, phi_mulA2 hm g c d hc hd]
    have hsum : ∑ r : Fin m, tA2 g d c' r ≤ ∑ r : Fin m, tA2 g d c r := by
      have hci : c' i.castSucc = v := by rw [hc'x]; simp
      have hcj : ∀ j : Fin m, j ≠ i → c' j.castSucc = c j.castSucc := by
        intro j hj
        rw [hc'x]
        have : j.castSucc ≠ i.castSucc := fun h => hj (Fin.castSucc_injective _ h)
        simp [this]
      have hcnt_ne : ∀ r, r ≠ s' → cntA2 c' r = cntA2 c r := by
        intro r hr; rw [hc']; exact cnt_upd_ne c i s' r hsi hr
      have hcnt_eq : cntA2 c' s' = cntA2 c s' - 1 := by
        rw [hc']; exact cnt_upd_eq c i s' hsi
      have hpt : ∀ r : Fin m, tA2 g d c' r - tA2 g d c r =
          (if r = i then ((s'.val : ℝ) * (gAt g i s'.val - 1)
              - ((s'.val : ℝ) + 1) * (gAt g i (s'.val + 1) - 1)
              + cntA2 d i * (gAt g i s'.val - gAt g i (s'.val + 1))) else 0)
          + (if r = s' then - gAt g s' (d s'.castSucc).val else 0) := by
        intro r
        by_cases hri : r = i <;> by_cases hrs : r = s'
        · subst hrs; subst hri
          simp only [tA2, hci, hcnt_eq, if_true]
          rw [← hsi]
          simp only [Nat.cast_add, Nat.cast_one]
          ring
        · subst hri
          simp only [tA2, hci, hcnt_ne r hrs, if_true, if_neg hrs]
          rw [← hsi]
          simp only [Nat.cast_add, Nat.cast_one]
          ring
        · subst hrs
          simp only [tA2, hcj r hri, hcnt_eq, if_true, if_neg hri]
          ring
        · simp only [tA2, hcj r hri, hcnt_ne r hrs, if_neg hri, if_neg hrs]
          ring
      have hdiff : ∑ r : Fin m, (tA2 g d c' r - tA2 g d c r) =
          ((s'.val : ℝ) * (gAt g i s'.val - 1)
              - ((s'.val : ℝ) + 1) * (gAt g i (s'.val + 1) - 1)
              + cntA2 d i * (gAt g i s'.val - gAt g i (s'.val + 1)))
          + (- gAt g s' (d s'.castSucc).val) := by
        rw [Finset.sum_congr rfl (fun r _ => hpt r), Finset.sum_add_distrib]
        simp [Finset.sum_ite_eq']
      have hD : i.val + 1 ≤ (d s'.castSucc).val := by
        have h5 : d r.castSucc ≤ d s'.castSucc := hd.1 (by
          show r.val ≤ s'.val
          omega)
        have h6 : (d r.castSucc).val ≤ (d s'.castSucc).val := h5
        have h7 : i.val ≤ k.val := hik
        omega
      have hDm : (d s'.castSucc).val ≤ m := by have := (d s'.castSucc).isLt; omega
      obtain ⟨e, he⟩ : ∃ e : Fin m, e.val + 1 = (d s'.castSucc).val :=
        ⟨⟨(d s'.castSucc).val - 1, by omega⟩, by simp; omega⟩
      have hcomp := gAt_comp g hg s' e
      rw [he] at hcomp
      have hanti := gAt_anti g hg i e s' (by show i.val ≤ e.val; omega)
      have hmono := gAt_mono g hg i s'.val (by have := s'.isLt; omega)
      have hN := cntA2_nonneg d i
      have hs0 : (0 : ℝ) ≤ s'.val := Nat.cast_nonneg _
      have hfin : ((s'.val : ℝ) * (gAt g i s'.val - 1)
              - ((s'.val : ℝ) + 1) * (gAt g i (s'.val + 1) - 1)
              + cntA2 d i * (gAt g i s'.val - gAt g i (s'.val + 1)))
          + (- gAt g s' (d s'.castSucc).val) ≤ 0 := by
        nlinarith [mul_nonneg (add_nonneg hs0 hN) (sub_nonneg.2 hmono)]
      have := Finset.sum_sub_distrib (s := Finset.univ) (fun r : Fin m => tA2 g d c' r) (fun r : Fin m => tA2 g d c r)
      linarith
    have e1 : ∑ r : Fin m, ((c' r.castSucc).val * (gAt g r (c' r.castSucc).val - 1)
          + cntA2 d r * gAt g r (c' r.castSucc).val + cntA2 c' r * gAt g r (d r.castSucc).val)
          = ∑ r : Fin m, tA2 g d c' r := rfl
    have e2 : ∑ r : Fin m, ((c r.castSucc).val * (gAt g r (c r.castSucc).val - 1)
          + cntA2 d r * gAt g r (c r.castSucc).val + cntA2 c r * gAt g r (d r.castSucc).val)
          = ∑ r : Fin m, tA2 g d c r := rfl
    rw [e1, e2]
    linarith

lemma reduceA2 {m : ℕ} (hm : 1 ≤ m) (g : Fin m → Fin m → ℝ) (hg : IsKTable g)
    (d : Fin (m + 1) → Fin (m + 1)) (hd : IsPath d) :
    ∀ n : ℕ, ∀ c : Fin (m + 1) → Fin (m + 1), IsPath c → ∑ j, (c j).val = n →
      ∃ c', IsTransposeFree c' d ∧ Phi g c' d ≤ Phi g c d := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hc hn
    by_cases h : ∃ k r : Fin m, r.val + 1 ≤ (c k.castSucc).val ∧ k.val + 1 ≤ (d r.castSucc).val
    · obtain ⟨k, r, h1, h2⟩ := h
      obtain ⟨c', hc', hlt, hle⟩ := stepA2 hm g hg c d hc hd k r h1 h2
      obtain ⟨c'', h3, h4⟩ := ih _ (by omega) c' hc' rfl
      exact ⟨c'', h3, h4.trans hle⟩
    · refine ⟨c, ⟨hc, hd, ?_⟩, le_refl _⟩
      intro k r hkr
      exact h ⟨k, r, hkr.1, hkr.2⟩

end HarmonicRanking.Main.Supplement

theorem solution (m : ℕ) (hm : 1 ≤ m) (g : Fin m → Fin m → ℝ)
    (hg : HarmonicRanking.Main.Supplement.IsKTable g) :
    HarmonicRanking.Main.Supplement.transposeFreeMin g =
      HarmonicRanking.Main.Supplement.twoPathMin g := by
  open HarmonicRanking.Main.Supplement in
  apply le_antisymm
  · unfold transposeFreeMin twoPathMin
    refine le_iInf fun a => le_iInf fun ha => le_iInf fun b => le_iInf fun hb => ?_
    obtain ⟨c', hc', hle⟩ := reduceA2 hm g hg b hb _ a ha rfl
    refine iInf_le_of_le c' (iInf_le_of_le b (iInf_le_of_le hc' ?_))
    exact_mod_cast hle
  · unfold transposeFreeMin twoPathMin
    refine le_iInf fun c => le_iInf fun d => le_iInf fun h => ?_
    exact iInf_le_of_le c (iInf_le_of_le h.1 (iInf_le_of_le d (iInf_le_of_le h.2.1 le_rfl)))
