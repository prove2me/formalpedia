-- Prove2me | solution 1 for ManipPotential.lemma_6_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:01:21.972788+00:00
-- url     : https://prove2.me/submissions/d65aca98-e367-421d-90c6-84f1d9659613

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_cycL
import Definitions.Def_ManipPotential_cycR
import Definitions.Def_ManipPotential_supp

open ManipPotential

namespace ManipPotentialLemma63Aux

/-- Generic form of Lemma 6.3 for a cyclic family `e`. -/
theorem gen {m : ℕ} [NeZero m] (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hB : BoundedMP K g) (e : Fin m → Ranking m)
    (hord : ∀ (S : Finset (Fin m)) (j : Fin m), j ∉ S → 2 ≤ S.card →
      ∃ j' ∈ S, ∀ h ∈ S, h ≠ j' → e j' h < e j' j)
    (P : Ranking m → ℚ) (hP : 0 ≤ P) (u₀ : ℚ) (hu₀ : 0 ≤ u₀)
    (hbase : ∀ (j : Fin m) (u : ℚ), u₀ < u → g (P + u • unitVec (e j)) = j) :
    ∀ n : ℕ, ∀ x : Fin m → ℚ, 0 ≤ x → (supp x).card = n + 1 →
      ((K : ℚ) + 1) ^ n * u₀ < ∑ j, x j →
        g (P + ∑ j, x j • unitVec (e j)) ∈ supp x := by
  have hlam : (1 : ℚ) ≤ (K : ℚ) + 1 := by
    have : (0 : ℚ) ≤ K := Nat.cast_nonneg K
    linarith
  have hlam0 : (0 : ℚ) < (K : ℚ) + 1 := by linarith
  intro n
  induction n with
  | zero =>
    intro x hx hcard hsum
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
    have hjS : j ∈ supp x := by rw [hj]; exact Finset.mem_singleton_self j
    have hzero : ∀ k, k ≠ j → x k = 0 := by
      intro k hk
      by_contra hne
      have : k ∈ supp x := by
        simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
        exact lt_of_le_of_ne (hx k) (Ne.symm hne)
      rw [hj] at this
      exact hk (Finset.mem_singleton.mp this)
    have hsum' : ∑ k, x k = x j := by
      rw [Finset.sum_eq_single j (fun k _ hk => hzero k hk) (fun h => absurd (Finset.mem_univ j) h)]
    have hvec : ∑ k, x k • (unitVec (e k) : Ranking m → ℚ) = x j • unitVec (e j) := by
      rw [Finset.sum_eq_single j (fun k _ hk => by rw [hzero k hk, zero_smul])
        (fun h => absurd (Finset.mem_univ j) h)]
    rw [hvec, hbase j (x j) (by rw [← hsum']; simpa using hsum)]
    exact hjS
  | succ n ih =>
    intro x hx hcard hsum
    by_contra hW
    set W := g (P + ∑ j, x j • unitVec (e j)) with hWdef
    have hcard2 : 2 ≤ (supp x).card := by omega
    obtain ⟨j', hj'S, hj'⟩ := hord (supp x) W hW hcard2
    obtain ⟨j'', hj''S, hj''ne⟩ : ∃ j'' ∈ supp x, j'' ≠ j' := by
      by_contra hcon
      push Not at hcon
      have : supp x ⊆ {j'} := fun k hk => Finset.mem_singleton.mpr (hcon k hk)
      have := Finset.card_le_card this
      simp at this
      omega
    have hxj'pos : 0 < x j' := by
      simpa [supp] using hj'S
    set lam : ℚ := (K : ℚ) + 1 with hlamdef
    set x' : Fin m → ℚ := x + (-(x j')) • Pi.single j' 1 + (x j' / lam) • Pi.single j'' 1
      with hx'def
    have hx'val : ∀ k, x' k = x k + (if k = j' then -(x j') else 0) +
        (if k = j'' then x j' / lam else 0) := by
      intro k
      simp only [hx'def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases h1 : k = j' <;> by_cases h2 : k = j'' <;> simp [h1, h2, Pi.single_apply]
    have hx'nonneg : 0 ≤ x' := by
      intro k
      simp only [Pi.zero_apply]
      rw [hx'val]
      have hxk : 0 ≤ x k := hx k
      have : 0 ≤ x j' / lam := div_nonneg (le_of_lt hxj'pos) (le_of_lt hlam0)
      by_cases h1 : k = j' <;> by_cases h2 : k = j''
      · exact absurd (h1.symm.trans h2) (Ne.symm hj''ne)
      · subst h1; simp [h2]
      · rw [if_neg h1, if_pos h2]; linarith
      · rw [if_neg h1, if_neg h2]; simpa using hxk
    have hsupp' : supp x' = (supp x).erase j' := by
      ext k
      simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      rw [hx'val]
      have hpos : 0 < x j' / lam := div_pos hxj'pos hlam0
      by_cases h1 : k = j'
      · subst h1; simp [hj''ne.symm]
      · by_cases h2 : k = j''
        · subst h2
          have hxk : 0 < x k := by simpa [supp] using hj''S
          simp [h1]; constructor <;> intro _ <;> linarith
        · simp [h1, h2]
    have hcard' : (supp x').card = n + 1 := by
      rw [hsupp', Finset.card_erase_of_mem hj'S]; omega
    have hsumx' : ∑ k, x' k = ∑ k, x k - x j' + x j' / lam := by
      simp only [hx'def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      simp [Finset.sum_pi_single']
      ring
    have hxle : x j' ≤ ∑ k, x k :=
      Finset.single_le_sum (fun k _ => hx k) (Finset.mem_univ j')
    have hsum'' : ((K : ℚ) + 1) ^ n * u₀ < ∑ k, x' k := by
      rw [hsumx']
      have h1 : (∑ k, x k) / lam ≤ ∑ k, x k - x j' + x j' / lam := by
        have hnn : 0 ≤ ∑ k, x k - x j' := by linarith
        have : (∑ k, x k - x j') / lam ≤ ∑ k, x k - x j' :=
          div_le_self hnn hlam
        have e1 : (∑ k, x k) / lam = (∑ k, x k - x j') / lam + x j' / lam := by ring
        linarith
      have h2 : ((K : ℚ) + 1) ^ n * u₀ < (∑ k, x k) / lam := by
        rw [lt_div_iff₀ hlam0]
        calc ((K : ℚ) + 1) ^ n * u₀ * lam = ((K : ℚ) + 1) ^ (n + 1) * u₀ := by
              rw [hlamdef]; ring
          _ < ∑ k, x k := hsum
      linarith
    have hIH := ih x' hx'nonneg hcard' hsum''
    set W' := g (P + ∑ j, x' j • unitVec (e j)) with hW'def
    rw [hsupp', Finset.mem_erase] at hIH
    have hlt := hj' W' hIH.2 hIH.1
    -- decomposition of the two profiles
    set A : Ranking m → ℚ := ∑ k ∈ Finset.univ.erase j', x k • unitVec (e k) with hAdef
    have hA0 : 0 ≤ A := by
      intro r
      simp only [hAdef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      apply Finset.sum_nonneg
      intro k _
      apply mul_nonneg (hx k)
      simp only [unitVec, Pi.single_apply]
      split_ifs <;> norm_num
    have hsplit : ∑ k, x k • (unitVec (e k) : Ranking m → ℚ) =
        A + x j' • unitVec (e j') := by
      rw [hAdef, ← Finset.sum_erase_add _ _ (Finset.mem_univ j')]
    have hδ : ∀ i, ∑ k, ((Pi.single i (1:ℚ) : Fin m → ℚ) k) • (unitVec (e k) : Ranking m → ℚ) =
        unitVec (e i) := by
      intro i
      rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_apply, hk])
        (fun h => absurd (Finset.mem_univ i) h)]
      simp
    have hsplit' : ∑ k, x' k • (unitVec (e k) : Ranking m → ℚ) =
        A + (x j' / lam) • unitVec (e j'') := by
      have : ∑ k, x' k • (unitVec (e k) : Ranking m → ℚ) =
          ∑ k, x k • (unitVec (e k) : Ranking m → ℚ) - x j' • unitVec (e j') +
            (x j' / lam) • unitVec (e j'') := by
        simp only [hx'def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul,
          Finset.sum_add_distrib, mul_smul]
        simp only [← Finset.smul_sum]
        rw [hδ j', hδ j'']
        simp only [neg_smul]
        abel
      rw [this, hsplit]; abel
    have hBMP := hB (P + A) (add_nonneg hP hA0) (e j') (e j'') (x j') (x j' / lam) hxj'pos
      (div_pos hxj'pos hlam0) (by rw [← hlamdef]; field_simp; rfl)
    have hWeq : g (P + A + x j' • unitVec (e j')) = W := by
      rw [hWdef, hsplit, add_assoc]
    have hW'eq : g (P + A + (x j' / lam) • unitVec (e j'')) = W' := by
      rw [hW'def, hsplit', add_assoc]
    rw [hWeq, hW'eq] at hBMP
    unfold Ranking.WeaklyPrefers at hBMP
    exact absurd (lt_of_le_of_lt hBMP hlt) (lt_irrefl _)

end ManipPotentialLemma63Aux

namespace ManipPotentialLemma63Aux

theorem ord_aux {m : ℕ} [NeZero m] (S : Finset (Fin m)) (j : Fin m) (hj : j ∉ S)
    (hS : S.Nonempty) (F : Fin m → Fin m) (hF : Function.Injective F) (hFj : F j = 0) :
    ∃ j' ∈ S, ∀ h ∈ S, h ≠ j' → (F j' - F h).val < (F j' - F j).val := by
  obtain ⟨j', hj'S, hmax⟩ := S.exists_max_image (fun a => (F a).val) hS
  refine ⟨j', hj'S, fun h hh hne => ?_⟩
  have hB : (F h).val ≤ (F j').val := hmax h hh
  have hBne : (F h).val ≠ (F j').val := fun heq => hne (hF (Fin.ext heq))
  have hB0 : (F h).val ≠ 0 := by
    intro h0
    have : F h = F j := by rw [hFj]; exact Fin.ext h0
    exact hj (hF this ▸ hh)
  rw [hFj, sub_zero, Fin.sub_val_of_le hB]
  omega

theorem ord_ell {m : ℕ} [NeZero m] (S : Finset (Fin m)) (j : Fin m) (hj : j ∉ S)
    (hS : 2 ≤ S.card) : ∃ j' ∈ S, ∀ h ∈ S, h ≠ j' → ell j' h < ell j' j := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨j', hj'S, H⟩ := ord_aux S j hj hne (fun a => a - j)
    (fun a b hab => by simpa using hab) (sub_self j)
  refine ⟨j', hj'S, fun h hh hne => ?_⟩
  have := H h hh hne
  simp only [sub_sub_sub_cancel_right] at this
  show (ell j' h) < (ell j' j)
  simp only [ell, Equiv.subLeft_apply]
  exact this

theorem ord_rr {m : ℕ} [NeZero m] (S : Finset (Fin m)) (j : Fin m) (hj : j ∉ S)
    (hS : 2 ≤ S.card) : ∃ j' ∈ S, ∀ h ∈ S, h ≠ j' → rr j' h < rr j' j := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨j', hj'S, H⟩ := ord_aux S j hj hne (fun a => j - a)
    (fun a b hab => by simpa using hab) (sub_self j)
  refine ⟨j', hj'S, fun h hh hne => ?_⟩
  have := H h hh hne
  simp only [sub_sub_sub_cancel_left] at this
  show (rr j' h) < (rr j' j)
  simp only [rr, Equiv.subRight_apply]
  exact this

end ManipPotentialLemma63Aux

theorem solution {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) (P : Ranking m → ℚ) (hP : 0 ≤ P) (u₀ : ℚ) (hu₀ : 0 ≤ u₀) :
    ((∀ (j : Fin m) (u : ℚ), u₀ < u → g (P + u • unitVec (ell j)) = j) →
      ∀ x : Fin m → ℚ, 0 ≤ x → x ≠ 0 →
        ((K : ℚ) + 1) ^ ((supp x).card - 1) * u₀ < ∑ j, x j → g (P + cycL x) ∈ supp x) ∧
    ((∀ (j : Fin m) (u : ℚ), u₀ < u → g (P + u • unitVec (rr j)) = j) →
      ∀ x : Fin m → ℚ, 0 ≤ x → x ≠ 0 →
        ((K : ℚ) + 1) ^ ((supp x).card - 1) * u₀ < ∑ j, x j → g (P + cycR x) ∈ supp x) := by
  have hcardpos : ∀ x : Fin m → ℚ, 0 ≤ x → x ≠ 0 → (supp x).card - 1 + 1 = (supp x).card := by
    intro x hx hx0
    have : (supp x).Nonempty := by
      by_contra hne
      apply hx0
      funext k
      have hk : k ∉ supp x := fun hk => hne ⟨k, hk⟩
      simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hk
      exact le_antisymm hk (hx k)
    have := Finset.card_pos.mpr this
    omega
  constructor
  · intro hbase x hx hx0 hsum
    have := ManipPotentialLemma63Aux.gen K g hg.2.1 ell
      (fun S j hj hS => ManipPotentialLemma63Aux.ord_ell S j hj hS) P hP u₀ hu₀ hbase
      ((supp x).card - 1) x hx (hcardpos x hx hx0).symm hsum
    simpa [cycL] using this
  · intro hbase x hx hx0 hsum
    have := ManipPotentialLemma63Aux.gen K g hg.2.1 rr
      (fun S j hj hS => ManipPotentialLemma63Aux.ord_rr S j hj hS) P hP u₀ hu₀ hbase
      ((supp x).card - 1) x hx (hcardpos x hx hx0).symm hsum
    simpa [cycR] using this
