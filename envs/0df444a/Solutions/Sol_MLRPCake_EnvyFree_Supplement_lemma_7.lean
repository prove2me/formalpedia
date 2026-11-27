-- Prove2me | solution 1 for MLRPCake.EnvyFree.Supplement.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:09:19.059187+00:00
-- url     : https://prove2.me/submissions/230791e4-95be-46c1-a675-4c6fa5611e38

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Definitions.Def_MLRPCake_EnvyFree_Supplement_Divisions
import Definitions.Def_MLRPCake_EnvyFree_Supplement_SwitchPoints

open MLRPCake
open MLRPCake.EnvyFree
open MLRPCake.EnvyFree.Supplement

/-- Lemma 7, p. 19: under MLRP there is a social-welfare maximizing allocation (maximizing over
all allocations, in any assignment order) all of whose cut points lie in the set `P` of
switching points together with `0` and `1`. -/
theorem solution {n : ℕ} (f : Fin n → ℝ → ℝ) (hn : 1 ≤ n) (hf : IsInstance f) (hm : IsMLRP f) :
    ∃ (x : ℕ → ℝ) (σ : Equiv.Perm (Fin n)), IsAllocation (n := n) x ∧
      (∀ (x' : ℕ → ℝ) (σ' : Equiv.Perm (Fin n)), IsAllocation (n := n) x' →
        SW f x' σ' ≤ SW f x σ) ∧
      ∀ k ≤ n, x k ∈ switchSet f := by
        classical
        have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
        obtain ⟨hpos, hmlrp⟩ := hm
        have hratio : ∀ d : ℕ, ∀ i j : Fin n, j.val = i.val + d → ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ 1 →
            f j x / f i x ≤ f j y / f i y := by
          intro d
          induction d with
          | zero =>
            intro i j hij x y hx hxy hy
            have : j = i := Fin.ext (by omega)
            subst this
            have h1 : 0 < f j x := hpos j x ⟨hx, by linarith⟩
            have h2 : 0 < f j y := hpos j y ⟨by linarith, hy⟩
            rw [div_self h1.ne', div_self h2.ne']
          | succ d ih =>
            intro i j hij x y hx hxy hy
            have hm' : i.val + d < n := by have := j.isLt; omega
            let m : Fin n := ⟨i.val + d, hm'⟩
            have h1 := ih i m rfl x y hx hxy hy
            have h2 := hmlrp m j (by simp only [m]; omega) x y hx hxy hy
            have hx1 : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx, by linarith⟩
            have hy1 : y ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, hy⟩
            have pix := hpos i x hx1
            have pmx := hpos m x hx1
            have pjx := hpos j x hx1
            have piy := hpos i y hy1
            have pmy := hpos m y hy1
            have pjy := hpos j y hy1
            have e1 : f j x / f i x = (f j x / f m x) * (f m x / f i x) := by field_simp
            have e2 : f j y / f i y = (f j y / f m y) * (f m y / f i y) := by field_simp
            rw [e1, e2]
            exact mul_le_mul h2 h1 (by positivity) (by positivity)
        have hup : ∀ i j : Fin n, i < j → ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ 1 → f i x ≤ f j x →
            f i y ≤ f j y := by
          intro i j hij x y hx hxy hy h
          have hij' : i.val < j.val := hij
          have hr := hratio (j.val - i.val) i j (by omega) x y hx hxy hy
          have pix := hpos i x ⟨hx, by linarith⟩
          have piy := hpos i y ⟨by linarith, hy⟩
          have h1 : 1 ≤ f j x / f i x := by rw [le_div_iff₀ pix]; linarith
          have h2 : 1 ≤ f j y / f i y := le_trans h1 hr
          rw [le_div_iff₀ piy] at h2; linarith
        have hargmax : ∀ t : ℝ, ∃ j : Fin n, ∀ i, f i t ≤ f j t := by
          intro t
          obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => f i t) hne
          exact ⟨j, fun i => hj i (Finset.mem_univ i)⟩
        obtain ⟨S, hS⟩ : ∃ S : ℕ → Set ℝ, S = fun k =>
            {t | t ∈ Set.Icc (0:ℝ) 1 ∧ ∃ j : Fin n, k ≤ j.val ∧ ∀ i, f i t ≤ f j t} := ⟨_, rfl⟩
        have hSmem : ∀ k t, t ∈ S k ↔ (t ∈ Set.Icc (0:ℝ) 1 ∧ ∃ j : Fin n, k ≤ j.val ∧ ∀ i, f i t ≤ f j t) := by
          intro k t; subst hS; rfl
        have hUPS : ∀ k t t', t ∈ S k → t ≤ t' → t' ≤ 1 → t' ∈ S k := by
          intro k t t' ht htt' ht'
          obtain ⟨⟨ht0, ht1⟩, j, hkj, hj⟩ := (hSmem k t).1 ht
          refine (hSmem k t').2 ⟨⟨by linarith, ht'⟩, ?_⟩
          obtain ⟨j', hj'⟩ := hargmax t'
          by_cases h : j ≤ j'
          · exact ⟨j', by have : j.val ≤ j'.val := h; omega, hj'⟩
          · push_neg at h
            refine ⟨j, hkj, fun i => le_trans (hj' i) ?_⟩
            exact hup j' j h t t' ht0 htt' ht' (hj j')
        obtain ⟨x, hxdef⟩ : ∃ x : ℕ → ℝ, x = fun k => sInf (insert (1:ℝ) (S k)) := ⟨_, rfl⟩
        have hxk : ∀ k, x k = sInf (insert (1:ℝ) (S k)) := by intro k; rw [hxdef]
        have hbdd : ∀ k, BddBelow (insert (1:ℝ) (S k)) := by
          intro k; refine ⟨0, ?_⟩
          intro y hy
          rcases hy with rfl | hy
          · norm_num
          · exact ((hSmem k y).1 hy).1.1
        have hx01 : ∀ k, 0 ≤ x k ∧ x k ≤ 1 := by
          intro k
          rw [hxk]
          constructor
          · apply le_csInf ⟨1, Set.mem_insert _ _⟩
            intro y hy
            rcases hy with rfl | hy
            · norm_num
            · exact ((hSmem k y).1 hy).1.1
          · exact csInf_le (hbdd k) (Set.mem_insert _ _)
        have hxmono : ∀ k k', k ≤ k' → x k ≤ x k' := by
          intro k k' hkk'
          rw [hxk, hxk]
          apply csInf_le_csInf (hbdd k) ⟨1, Set.mem_insert _ _⟩
          apply Set.insert_subset_insert
          intro t ht
          obtain ⟨ht, j, hj, hj'⟩ := (hSmem k' t).1 ht
          exact (hSmem k t).2 ⟨ht, j, le_trans hkk' hj, hj'⟩
        have hleft : ∀ k t, t ∈ S k → x k ≤ t := fun k t ht => by
          rw [hxk]; exact csInf_le (hbdd k) (Set.mem_insert_of_mem _ ht)
        have hx0 : x 0 = 0 := by
          apply le_antisymm _ (hx01 0).1
          obtain ⟨j, hj⟩ := hargmax 0
          exact hleft 0 0 ((hSmem 0 0).2 ⟨⟨le_refl _, zero_le_one⟩, j, Nat.zero_le _, hj⟩)
        have hxn : x n = 1 := by
          have : S n = ∅ := by
            ext t; simp only [Set.mem_empty_iff_false, iff_false]
            intro ht
            obtain ⟨-, j, hj, -⟩ := (hSmem n t).1 ht
            have := j.isLt; omega
          rw [hxk, this]; simp
        have hright : ∀ k t, x k < t → t ≤ 1 → t ∈ S k := by
          intro k t hlt ht1
          rw [hxk] at hlt
          obtain ⟨a, ha, hat⟩ := exists_lt_of_csInf_lt ⟨1, Set.mem_insert _ _⟩ hlt
          rcases ha with rfl | ha
          · linarith
          · exact hUPS k a t ha hat.le ht1
        obtain ⟨M, hM⟩ : ∃ M : ℝ → ℝ, M = Finset.univ.sup' hne f := ⟨_, rfl⟩
        have hMapp : ∀ t, M t = Finset.univ.sup' hne (fun i => f i t) := by
          intro t; rw [hM, Finset.sup'_apply]
        have hfM : ∀ i t, f i t ≤ M t := fun i t => by
          rw [hMapp]; exact Finset.le_sup' (fun i => f i t) (Finset.mem_univ i)
        have hMf : ∀ j t, (∀ i, f i t ≤ f j t) → M t = f j t := fun j t h =>
          le_antisymm (by rw [hMapp]; exact Finset.sup'_le _ _ (fun i _ => h i)) (hfM j t)
        have hMint : IntervalIntegrable M MeasureTheory.volume 0 1 := by
          rw [hM]
          apply Finset.sup'_induction hne f (p := fun g => IntervalIntegrable g MeasureTheory.volume 0 1)
          · intro g₁ h₁ g₂ h₂
            exact ⟨h₁.1.sup h₂.1, h₁.2.sup h₂.2⟩
          · intro i _; exact (hf i).2.2.1
        have hdens : ∀ i : Fin n, dens f (i:ℕ) = f i := by intro i; simp [dens, i.isLt]
        have halloc : ∀ x' : ℕ → ℝ, IsAllocation (n := n) x' → ∀ k ≤ n, 0 ≤ x' k ∧ x' k ≤ 1 := by
          intro x' hx'
          obtain ⟨h0, hmono, hn1⟩ := hx'
          have key : ∀ d k, k + d ≤ n → x' k ≤ x' (k + d) := by
            intro d; induction d with
            | zero => intro k _; simp
            | succ d ih => intro k hk; exact le_trans (ih k (by omega)) (hmono (k+d) (by omega))
          intro k hk
          constructor
          · have := key k 0 (by omega); simpa [h0] using this
          · have := key (n - k) k (by omega); rwa [Nat.add_sub_cancel' hk, hn1] at this
        have htele : ∀ x' : ℕ → ℝ, IsAllocation (n := n) x' →
            ∑ k : Fin n, ∫ t in x' k..x' (k+1), M t = ∫ t in (0:ℝ)..1, M t := by
          intro x' hx'
          have hb := halloc x' hx'
          rw [Fin.sum_univ_eq_sum_range (fun k => ∫ t in x' k..x' (k+1), M t) n]
          rw [intervalIntegral.sum_integral_adjacent_intervals, hx'.1, hx'.2.2]
          intro k hk
          apply hMint.mono_set
          rw [Set.uIcc_of_le (hx'.2.1 k hk), Set.uIcc_of_le zero_le_one]
          exact Set.Icc_subset_Icc (hb k hk.le).1 (hb (k+1) hk).2
        have hupper : ∀ (x' : ℕ → ℝ) (σ' : Equiv.Perm (Fin n)), IsAllocation (n := n) x' →
            SW f x' σ' ≤ ∫ t in (0:ℝ)..1, M t := by
          intro x' σ' hx'
          have hb := halloc x' hx'
          rw [← htele x' hx']
          unfold SW pieceVal
          rw [← Equiv.sum_comp σ' (fun k : Fin n => ∫ t in x' k..x' (k+1), M t)]
          apply Finset.sum_le_sum
          intro i _
          have hk := (σ' i).isLt
          have hle := hx'.2.1 (σ' i) hk
          have h0 := (hb (σ' i) hk.le).1
          have h1 := (hb ((σ' i : ℕ)+1) hk).2
          unfold val
          rw [hdens]
          apply intervalIntegral.integral_mono_on hle
          · apply (hf i).2.2.1.mono_set
            rw [Set.uIcc_of_le hle, Set.uIcc_of_le zero_le_one]
            exact Set.Icc_subset_Icc h0 h1
          · apply hMint.mono_set
            rw [Set.uIcc_of_le hle, Set.uIcc_of_le zero_le_one]
            exact Set.Icc_subset_Icc h0 h1
          · intro t _; exact hfM i t
        have hcell : ∀ k : Fin n, ∀ t, x k < t → t < x (k+1) → M t = f k t := by
          intro k t h1 h2
          have ht1 : t ≤ 1 := le_trans h2.le (hx01 _).2
          have ht0 : 0 ≤ t := le_trans (hx01 _).1 h1.le
          obtain ⟨-, j, hkj, hj⟩ := (hSmem _ _).1 (hright k t h1 ht1)
          have hj' : j = k := by
            by_contra hne'
            have hkj2 : k.val + 1 ≤ j.val := by
              have : j.val ≠ k.val := fun h => hne' (Fin.ext h)
              omega
            have := hleft (k+1) t ((hSmem _ _).2 ⟨⟨ht0, ht1⟩, j, hkj2, hj⟩)
            linarith
          subst hj'; exact hMf j t hj
        have hxalloc : IsAllocation (n := n) x := ⟨hx0, fun k _ => hxmono k (k+1) (by omega), hxn⟩
        have hlower : SW f x (Equiv.refl _) = ∫ t in (0:ℝ)..1, M t := by
          rw [← htele x hxalloc]
          unfold SW pieceVal
          apply Finset.sum_congr rfl
          intro k _
          simp only [Equiv.refl_apply]
          unfold val; rw [hdens]
          have hle := hxmono k (k+1) (by omega)
          rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle,
            MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
          intro t ht; exact (hcell k t ht.1 ht.2).symm
        refine ⟨x, Equiv.refl _, hxalloc, fun x' σ' hx' => (hupper x' σ' hx').trans hlower.ge, ?_⟩
        intro k hk
        by_cases hc0 : x k = 0
        · rw [hc0]; exact Or.inr (by simp)
        by_cases hc1 : x k = 1
        · rw [hc1]; exact Or.inr (by simp)
        have hcpos : 0 < x k := lt_of_le_of_ne (hx01 k).1 (Ne.symm hc0)
        have hclt : x k < 1 := lt_of_le_of_ne (hx01 k).2 hc1
        have hk0 : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with h | h
          · subst h; exact absurd hx0 hc0
          · exact h
        have hkn : k < n := lt_of_le_of_ne hk (fun h => hc1 (h ▸ hxn))
        have ha : ∀ t, x k < t → t ≤ 1 → ∃ j : Fin n, k ≤ j.val ∧ ∀ i, f i t ≤ f j t :=
          fun t h1 h2 => ((hSmem _ _).1 (hright k t h1 h2)).2
        have hb : ∀ t, 0 ≤ t → t < x k → ∀ j : Fin n, k ≤ j.val → ¬ ∀ i, f i t ≤ f j t := by
          intro t h0 h1 j hj hW
          have := hleft k t ((hSmem _ _).2 ⟨⟨h0, by linarith⟩, j, hj, hW⟩)
          linarith
        let L : Fin n → Fin n → Set ℝ := fun i j => {x | x ∈ Set.Icc (0:ℝ) 1 ∧ f i x ≤ f j x}
        let q : Fin n → Fin n → ℝ := fun i j => if (L i j).Nonempty then switchPt (f i) (f j) else 2
        have hq1 : ∀ i j t, t ∈ L i j → q i j ≤ t := by
          intro i j t ht
          have hne' : (L i j).Nonempty := ⟨t, ht⟩
          simp only [q, if_pos hne']
          exact csInf_le ⟨0, fun y hy => hy.1.1⟩ ht
        have hq2 : ∀ i j : Fin n, i < j → ∀ t, 0 ≤ t → t ≤ 1 → t ∉ L i j → t ≤ q i j := by
          intro i j hij t h0 h1 ht
          by_cases hne' : (L i j).Nonempty
          · simp only [q, if_pos hne']
            by_contra hlt; push_neg at hlt
            obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt hne' hlt
            exact ht ⟨⟨h0, h1⟩, hup i j hij s t hs.1.1 hst.le h1 hs.2⟩
          · simp only [q, if_neg hne']; linarith
        let I : Finset (Fin n) := Finset.univ.filter (fun i => i.val < k)
        let J : Finset (Fin n) := Finset.univ.filter (fun j => k ≤ j.val)
        have hImem : ∀ i, i ∈ I ↔ i.val < k := by intro i; simp [I]
        have hJmem : ∀ j, j ∈ J ↔ k ≤ j.val := by intro j; simp [J]
        have hIne : I.Nonempty := ⟨⟨0, hn⟩, (hImem _).2 (by simp; omega)⟩
        have hJne : J.Nonempty := ⟨⟨k, hkn⟩, (hJmem _).2 le_rfl⟩
        obtain ⟨R, hR⟩ : ∃ R, R = I.sup' hIne (fun i => J.inf' hJne (fun j => q i j)) := ⟨_, rfl⟩
        obtain ⟨Q, hQ⟩ : ∃ Q, Q = J.inf' hJne (fun j => I.sup' hIne (fun i => q i j)) := ⟨_, rfl⟩
        have hRQ : R ≤ Q := by
          rw [hR, hQ]
          apply Finset.sup'_le
          intro i hi
          apply Finset.le_inf'
          intro j hj
          exact le_trans (Finset.inf'_le _ hj) (Finset.le_sup' (fun i => q i j) hi)
        have hQc : Q ≤ x k := by
          by_contra hlt; push_neg at hlt
          have hmin := lt_min hlt hclt
          obtain ⟨t, ht⟩ : ∃ t, t = (x k + min Q 1) / 2 := ⟨_, rfl⟩
          have ht1 : x k < t := by rw [ht]; linarith
          have ht2 : t < min Q 1 := by rw [ht]; linarith
          have htQ : t < Q := lt_of_lt_of_le ht2 (min_le_left _ _)
          have ht3 : t ≤ 1 := le_trans ht2.le (min_le_right _ _)
          obtain ⟨j, hkj, hW⟩ := ha t ht1 ht3
          have : Q ≤ t := by
            rw [hQ]
            apply le_trans (Finset.inf'_le _ ((hJmem j).2 hkj))
            apply Finset.sup'_le
            intro i _
            exact hq1 i j t ⟨⟨by linarith, ht3⟩, hW i⟩
          linarith
        have hcR : x k ≤ R := by
          by_contra hlt; push_neg at hlt
          have hmax := max_lt hlt hcpos
          obtain ⟨t, ht⟩ : ∃ t, t = (max R 0 + x k) / 2 := ⟨_, rfl⟩
          have ht1 : max R 0 < t := by rw [ht]; linarith
          have ht2 : t < x k := by rw [ht]; linarith
          have ht0 : 0 ≤ t := le_trans (le_max_right _ _) ht1.le
          have htR : R < t := lt_of_le_of_lt (le_max_left _ _) ht1
          obtain ⟨i, hi⟩ := hargmax t
          have hik : i.val < k := by
            by_contra h; push_neg at h; exact hb t ht0 ht2 i h hi
          have : t ≤ R := by
            rw [hR]
            apply le_trans _ (Finset.le_sup' (fun i => J.inf' hJne (fun j => q i j)) ((hImem i).2 hik))
            apply Finset.le_inf'
            intro j hj
            have hkj : k ≤ j.val := (hJmem j).1 hj
            apply hq2 i j (by show i.val < j.val; omega) t ht0 (by linarith)
            intro htL
            exact hb t ht0 ht2 j hkj (fun i' => le_trans (hi i') htL.2)
          linarith
        have hRc : R = x k := le_antisymm (hRQ.trans hQc) hcR
        obtain ⟨i, hi, hRi⟩ := Finset.exists_mem_eq_sup' hIne (fun i => J.inf' hJne (fun j => q i j))
        obtain ⟨j, hj, hij⟩ := Finset.exists_mem_eq_inf' hJne (fun j => q i j)
        have hqc : q i j = x k := by rw [← hRc, hR, hRi]; exact hij.symm
        have hik : i.val < k := (hImem i).1 hi
        have hkj : k ≤ j.val := (hJmem j).1 hj
        refine Or.inl ⟨i, j, (show i.val < j.val by omega), ?_⟩
        by_cases hne' : (L i j).Nonempty
        · simp only [q, if_pos hne'] at hqc; exact hqc.symm
        · simp only [q, if_neg hne'] at hqc; linarith
