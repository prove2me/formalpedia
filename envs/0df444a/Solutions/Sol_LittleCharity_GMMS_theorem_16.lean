-- Prove2me | solution 1 for LittleCharity.GMMS.theorem_16
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T07:54:20.309634+00:00
-- url     : https://prove2.me/submissions/c878a518-1085-479c-8277-99d5900f0c49

import Mathlib
import Definitions.Def_LittleCharity_GMMS_Setting

set_option autoImplicit false

namespace LCGMMS16

variable {α : Type*} [DecidableEq α]

/-- Weight of a good relative to the threshold `x`. -/
noncomputable def phi (u : α → ℝ) (x : ℝ) (g : α) : ℝ :=
  if x < u g then 1 else if 3 * x / 4 < u g then 1 / 2 else 2 * u g / (3 * x)

lemma lin_le {x a c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (ha : a ≤ c * x) :
    2 * a / (3 * x) ≤ 2 * c / 3 := by
  rcases hx.eq_or_lt with h | h
  · subst h; simp; positivity
  · rw [div_le_iff₀ (by positivity)]; nlinarith

lemma phi_nonneg {u : α → ℝ} {x : ℝ} (hx : 0 ≤ x) {g : α} (hg : 0 ≤ u g) :
    0 ≤ phi u x g := by
  unfold phi
  split_ifs
  · norm_num
  · norm_num
  · exact div_nonneg (by linarith) (by linarith)

lemma phi_le_one {u : α → ℝ} {x : ℝ} (hx : 0 ≤ x) (g : α) : phi u x g ≤ 1 := by
  unfold phi
  split_ifs with h1 h2
  · exact le_rfl
  · norm_num
  · have := lin_le (c := 3 / 4) hx (by norm_num) (show u g ≤ 3 / 4 * x by linarith)
    linarith

lemma phi_le_half {u : α → ℝ} {x : ℝ} (hx : 0 ≤ x) {g : α} (hux : u g ≤ x) :
    phi u x g ≤ 1 / 2 := by
  unfold phi
  split_ifs with h1 h2
  · linarith
  · exact le_rfl
  · have := lin_le (c := 3 / 4) hx (by norm_num) (show u g ≤ 3 / 4 * x by linarith)
    linarith

lemma phi_le_lin {u : α → ℝ} {x : ℝ} (hx : 0 ≤ x) {g : α} (hux : u g ≤ x) :
    phi u x g ≤ 2 * u g / (3 * x) := by
  unfold phi
  split_ifs with h1 h2
  · linarith
  · rcases hx.eq_or_lt with h | h
    · subst h; linarith
    · rw [le_div_iff₀ (by positivity)]; linarith
  · exact le_rfl

lemma sum_phi_le_lin {u : α → ℝ} {x : ℝ} (hx : 0 ≤ x) (T : Finset α)
    (hT : ∀ g ∈ T, u g ≤ x) :
    ∑ g ∈ T, phi u x g ≤ 2 * (∑ g ∈ T, u g) / (3 * x) := by
  calc ∑ g ∈ T, phi u x g ≤ ∑ g ∈ T, 2 * u g / (3 * x) :=
        Finset.sum_le_sum fun g hg => phi_le_lin hx (hT g hg)
    _ = 2 * (∑ g ∈ T, u g) / (3 * x) := by rw [Finset.mul_sum, Finset.sum_div]

lemma own_bound {u : α → ℝ} {x : ℝ} (hnn : ∀ g, 0 ≤ u g) (hx : 0 ≤ x) (T : Finset α)
    (hT : ∑ g ∈ T, u g ≤ x) : ∑ g ∈ T, phi u x g ≤ 2 / 3 := by
  have hle : ∀ g ∈ T, u g ≤ x := fun g hg =>
    (Finset.single_le_sum (fun g _ => hnn g) hg).trans hT
  have h1 := sum_phi_le_lin hx T hle
  have h2 := lin_le (c := 1) hx (by norm_num) (show ∑ g ∈ T, u g ≤ 1 * x by linarith)
  linarith

lemma phi_zero {u : α → ℝ} {x : ℝ} (hx : 0 ≤ x) {g : α} (h0 : u g = 0) : phi u x g = 0 := by
  unfold phi
  rw [if_neg (by linarith), if_neg (by linarith), h0]
  simp

lemma own_half {u : α → ℝ} {x : ℝ} (hnn : ∀ g, 0 ≤ u g) (hx : 0 ≤ x) (T : Finset α)
    (hT : ∑ g ∈ T, u g ≤ x) (hnone : ∀ g ∈ T, u g ≤ 3 * x / 4 → u g ≤ 0) :
    ∑ g ∈ T, phi u x g ≤ 1 / 2 := by
  have hle : ∀ g ∈ T, u g ≤ x := fun g hg =>
    (Finset.single_le_sum (fun g _ => hnn g) hg).trans hT
  by_cases hL : ∃ l ∈ T, 3 * x / 4 < u l
  · obtain ⟨l, hl, hlu⟩ := hL
    rw [← Finset.add_sum_erase T _ hl]
    have hrest : ∀ g ∈ T.erase l, phi u x g = 0 := by
      intro g hg
      have hg' := Finset.mem_of_mem_erase hg
      have hne := Finset.ne_of_mem_erase hg
      by_cases hgl : 3 * x / 4 < u g
      · exfalso
        have hsub : ({l, g} : Finset α) ⊆ T :=
          Finset.insert_subset_iff.mpr ⟨hl, Finset.singleton_subset_iff.mpr hg'⟩
        have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => hnn g)
        rw [Finset.sum_pair (Ne.symm hne)] at h2
        linarith
      · exact phi_zero hx (le_antisymm (hnone g hg' (le_of_not_gt hgl)) (hnn g))
    rw [Finset.sum_eq_zero hrest, add_zero]
    exact phi_le_half hx (hle l hl)
  · push Not at hL
    have : ∀ g ∈ T, phi u x g = 0 := fun g hg =>
      phi_zero hx (le_antisymm (hnone g hg (hL g hg)) (hnn g))
    rw [Finset.sum_eq_zero this]; norm_num

lemma efx_bundle {u : α → ℝ} {x : ℝ} (hnn : ∀ g, 0 ≤ u g) (hx : 0 ≤ x) (B : Finset α)
    (h : ∀ g ∈ B, ∑ g' ∈ B.erase g, u g' ≤ x) : ∑ g ∈ B, phi u x g ≤ 1 := by
  rcases Nat.lt_or_ge B.card 2 with hc | hc
  · have h1 := Finset.sum_le_card_nsmul B (phi u x) 1 (fun g _ => phi_le_one hx g)
    rw [nsmul_eq_mul, mul_one] at h1
    have : (B.card : ℝ) ≤ 1 := by exact_mod_cast (by omega : B.card ≤ 1)
    linarith
  · have hle : ∀ g ∈ B, u g ≤ x := by
      intro g hg
      obtain ⟨g', hg', hne⟩ := Finset.exists_mem_ne (by omega : 1 < B.card) g
      have hmem : g ∈ B.erase g' := Finset.mem_erase.mpr ⟨Ne.symm hne, hg⟩
      exact (Finset.single_le_sum (fun g _ => hnn g) hmem).trans (h g' hg')
    rcases hc.eq_or_lt with h2 | h3
    · have h1 := Finset.sum_le_card_nsmul B (phi u x) (1 / 2) (fun g hg => phi_le_half hx (hle g hg))
      rw [nsmul_eq_mul, ← h2] at h1
      norm_num at h1
      linarith
    · obtain ⟨a, b, c, ha, hb, hc', hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp h3
      have ea := Finset.add_sum_erase B u ha
      have eb := Finset.add_sum_erase B u hb
      have ec := Finset.add_sum_erase B u hc'
      have hsub : ({a, b, c} : Finset α) ⊆ B := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl <;> assumption
      have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => hnn g)
      rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc] at hs
      have ha' := h a ha
      have hb' := h b hb
      have hc'' := h c hc'
      have hB : ∑ g ∈ B, u g ≤ 3 / 2 * x := by linarith
      have h1 := sum_phi_le_lin hx B hle
      have h2 := lin_le hx (by norm_num) hB
      linarith

lemma part_lower {u : α → ℝ} {x : ℝ} (hnn : ∀ g, 0 ≤ u g) (hx : 0 ≤ x) (Q : Finset α)
    (hQ : 7 * x / 4 < ∑ g ∈ Q, u g) :
    1 ≤ ∑ g ∈ Q, phi u x g ∧
      ∀ g0 ∈ Q, 0 < u g0 → u g0 ≤ 3 * x / 4 → 1 < ∑ g ∈ Q, phi u x g := by
  have pnn : ∀ g, 0 ≤ phi u x g := fun g => phi_nonneg hx (hnn g)
  have hpos : ∀ g0, 0 < u g0 → u g0 ≤ 3 * x / 4 → 0 < phi u x g0 := by
    intro g0 h1 h2
    have hx0 : 0 < x := by linarith
    unfold phi
    rw [if_neg (by linarith), if_neg (by linarith)]
    positivity
  by_cases hH : ∃ h ∈ Q, x < u h
  · obtain ⟨h, hh, hhu⟩ := hH
    have e1 : phi u x h = 1 := by unfold phi; rw [if_pos hhu]
    rw [← Finset.add_sum_erase Q _ hh, e1]
    have hr : 0 ≤ ∑ g ∈ Q.erase h, phi u x g := Finset.sum_nonneg (fun g _ => pnn g)
    refine ⟨by linarith, ?_⟩
    intro g0 hg0 h1 h2
    have hne : g0 ≠ h := by intro e; subst e; linarith
    have := Finset.single_le_sum (f := phi u x) (fun g _ => pnn g)
      (Finset.mem_erase.mpr ⟨hne, hg0⟩)
    linarith [hpos g0 h1 h2]
  push Not at hH
  have half : ∀ l, 3 * x / 4 < u l → l ∈ Q → phi u x l = 1 / 2 := by
    intro l hl hlQ
    unfold phi; rw [if_neg (not_lt.mpr (hH l hlQ)), if_pos hl]
  by_cases hL : ∃ l ∈ Q, 3 * x / 4 < u l
  · obtain ⟨l, hl, hlu⟩ := hL
    by_cases hL2 : ∃ l' ∈ Q.erase l, 3 * x / 4 < u l'
    · obtain ⟨l', hl', hlu'⟩ := hL2
      rw [← Finset.add_sum_erase Q _ hl, ← Finset.add_sum_erase (Q.erase l) _ hl',
        half l hlu hl, half l' hlu' (Finset.mem_of_mem_erase hl')]
      have hr : 0 ≤ ∑ g ∈ (Q.erase l).erase l', phi u x g :=
        Finset.sum_nonneg (fun g _ => pnn g)
      refine ⟨by linarith, ?_⟩
      intro g0 hg0 h1 h2
      have hne1 : g0 ≠ l := by intro e; subst e; linarith
      have hne2 : g0 ≠ l' := by intro e; subst e; linarith
      have := Finset.single_le_sum (f := phi u x) (fun g _ => pnn g)
        (Finset.mem_erase.mpr ⟨hne2, Finset.mem_erase.mpr ⟨hne1, hg0⟩⟩)
      linarith [hpos g0 h1 h2]
    · push Not at hL2
      have hx0 : 0 < x := by linarith [hH l hl]
      have eq : ∑ g ∈ Q.erase l, phi u x g = 2 * (∑ g ∈ Q.erase l, u g) / (3 * x) := by
        rw [Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun g hg => ?_
        unfold phi
        rw [if_neg (by linarith [hL2 g hg]), if_neg (not_lt.mpr (hL2 g hg))]
      have ea := Finset.add_sum_erase Q u hl
      have hrest : 1 / 2 < 2 * (∑ g ∈ Q.erase l, u g) / (3 * x) := by
        rw [lt_div_iff₀ (by positivity)]
        linarith [hH l hl]
      rw [← Finset.add_sum_erase Q _ hl, half l hlu hl, eq]
      exact ⟨by linarith, fun _ _ _ _ => by linarith⟩
  · push Not at hL
    have hx0 : 0 < x := by
      rcases hx.eq_or_lt with h | h
      · exfalso
        have : ∑ g ∈ Q, u g ≤ 0 := Finset.sum_nonpos fun g hg => by
          have := hL g hg; rw [← h] at this; linarith
        rw [← h] at hQ; linarith
      · exact h
    have eq : ∑ g ∈ Q, phi u x g = 2 * (∑ g ∈ Q, u g) / (3 * x) := by
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun g hg => ?_
      unfold phi
      rw [if_neg (by linarith [hL g hg]), if_neg (not_lt.mpr (hL g hg))]
    have : 1 < 2 * (∑ g ∈ Q, u g) / (3 * x) := by
      rw [lt_div_iff₀ (by positivity)]; linarith
    rw [eq]
    exact ⟨by linarith, fun _ _ _ _ => by linarith⟩

end LCGMMS16

open LCGMMS16

lemma lc16_pool_disj {n m : ℕ} (X : Fin n → Finset (Fin m)) (j : Fin n) :
    Disjoint (X j) (LittleCharity.EFX.pool X) :=
  Finset.disjoint_of_subset_left (Finset.subset_biUnion_of_mem X (Finset.mem_univ j))
    Finset.disjoint_sdiff

lemma lc16_donate_disj {n m : ℕ} (X : Fin n → Finset (Fin m))
    (hX : LittleCharity.EFX.IsPartialAllocation X) (s : Fin n) :
    LittleCharity.EFX.IsPartialAllocation (LittleCharity.GMMS.donate X s) := by
  intro a b hab
  simp only [LittleCharity.GMMS.donate]
  by_cases ha : a = s <;> by_cases hb : b = s
  · exact absurd (ha.trans hb.symm) hab
  · subst ha
    rw [Function.update_self, Function.update_of_ne hb]
    exact Finset.disjoint_union_left.mpr ⟨hX hab, (lc16_pool_disj X b).symm⟩
  · subst hb
    rw [Function.update_self, Function.update_of_ne ha]
    exact Finset.disjoint_union_right.mpr ⟨hX hab, lc16_pool_disj X a⟩
  · rw [Function.update_of_ne ha, Function.update_of_ne hb]
    exact hX hab

open LittleCharity.GMMS in
theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : LittleCharity.MMS.IsAdditive v)
    (X : Fin n → Finset (Fin m)) (hX : LittleCharity.EFX.IsPartialAllocation X) (hEFX : LittleCharity.MMS.IsEFX v X)
    (hpool : ∀ i, v i (LittleCharity.EFX.pool X) ≤ v i (X i))
    (s : Fin n) (hs : LittleCharity.EFX.IsSource v X s) :
    IsCompleteAllocation (donate X s) ∧ IsGMMS (4 / 7 : ℝ) v (donate X s) ∧
      ∀ i, v i (X i) ≤ v i (donate X s i) := by
  have hYd := lc16_donate_disj X hX s
  have hYs : donate X s s = X s ∪ LittleCharity.EFX.pool X := by
    simp [donate]
  have hYo : ∀ j, j ≠ s → donate X s j = X j := fun j hj => by
    simp only [donate]; rw [Function.update_of_ne hj]
  have hmono : ∀ i, v i (X i) ≤ v i (donate X s i) := by
    intro i
    by_cases hi : i = s
    · subst hi
      rw [hYs, hadd.1 i (X i), hadd.1 i (X i ∪ _)]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun g _ _ => hadd.2 i {g})
    · rw [hYo i hi]
  refine ⟨⟨hYd, ?_⟩, ?_, hmono⟩
  · -- the pool of the donated allocation is empty
    unfold LittleCharity.EFX.pool
    rw [Finset.sdiff_eq_empty_iff_subset]
    intro g _
    rw [Finset.mem_biUnion]
    by_cases hg : g ∈ Finset.univ.biUnion X
    · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hg
      by_cases hjs : j = s
      · subst hjs; exact ⟨j, Finset.mem_univ _, by rw [hYs]; exact Finset.mem_union_left _ hj⟩
      · exact ⟨j, Finset.mem_univ _, by rw [hYo j hjs]; exact hj⟩
    · refine ⟨s, Finset.mem_univ _, ?_⟩
      rw [hYs]
      exact Finset.mem_union_right _ (by
        unfold LittleCharity.EFX.pool
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hg⟩)
  · intro N' i hi
    set Y := donate X s with hYdef
    set u : Fin m → ℝ := fun g => v i {g} with hudef
    have hv : ∀ T, v i T = ∑ g ∈ T, u g := fun T => hadd.1 i T
    have hnn : ∀ g, 0 ≤ u g := fun g => hadd.2 i {g}
    set x := v i (Y i) with hxdef
    have hx : 0 ≤ x := hadd.2 i _
    have hXx : v i (X i) ≤ x := hmono i
    set k := N'.card with hkdef
    have hk : 0 < k := Finset.card_pos.mpr ⟨i, hi⟩
    set S := N'.biUnion Y with hSdef
    -- the key bound: every partition of S into k parts has a part of value ≤ 7x/4
    have key : ∀ f : Fin m → Fin k, ∃ t, v i (S.filter (fun g => f g = t)) ≤ 7 * x / 4 := by
      intro f
      by_contra hcon
      push Not at hcon
      have hpart : ∀ t, 7 * x / 4 < ∑ g ∈ S.filter (fun g => f g = t), u g := fun t => by
        rw [← hv]; exact hcon t
      have hfib : ∑ t, ∑ g ∈ S.filter (fun g => f g = t), phi u x g = ∑ g ∈ S, phi u x g :=
        Finset.sum_fiberwise S f (phi u x)
      have hdisj : (↑N' : Set (Fin n)).PairwiseDisjoint Y := fun a _ b _ hab => hYd hab
      have hbu : ∑ g ∈ S, phi u x g = ∑ j ∈ N', ∑ g ∈ Y j, phi u x g :=
        Finset.sum_biUnion hdisj
      have hsplit := Finset.add_sum_erase N' (fun j => ∑ g ∈ Y j, phi u x g) hi
      have hother : ∀ j ∈ N'.erase i,
          ∑ g ∈ Y j, phi u x g ≤ 1 + (if j = s then 1 / 3 else 0) := by
        intro j hj
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        by_cases hjs : j = s
        · subst hjs
          have his : i ≠ j := Ne.symm hji
          have hxi : x = v i (X i) := by rw [hxdef, hYo i his]
          rw [if_pos rfl, hYs, Finset.sum_union (lc16_pool_disj X j)]
          have hsrc : v i (X j) ≤ v i (X i) := not_lt.mp (hs i)
          have h1 := own_bound hnn hx (X j) (by rw [← hv]; linarith)
          have h2 := own_bound hnn hx (LittleCharity.EFX.pool X)
            (by rw [← hv]; linarith [hpool i])
          linarith
        · rw [if_neg hjs, add_zero, hYo j hjs]
          refine efx_bundle hnn hx (X j) fun g hg => ?_
          rw [← hv]
          exact (hEFX i j g hg).trans hXx
      have hsumo : ∑ j ∈ N'.erase i, ∑ g ∈ Y j, phi u x g ≤ (k : ℝ) - 1 + 1 / 3 := by
        refine (Finset.sum_le_sum hother).trans ?_
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
          Finset.sum_ite_eq']
        have hc : ((N'.erase i).card : ℝ) = (k : ℝ) - 1 := by
          have := Finset.card_erase_add_one hi
          rw [← hkdef] at this
          have : ((N'.erase i).card : ℝ) + 1 = k := by exact_mod_cast this
          linarith
        rw [hc]
        split_ifs <;> norm_num
      have hYiS : Y i ⊆ S := Finset.subset_biUnion_of_mem Y hi
      have hown : ∑ g ∈ Y i, u g ≤ x := by rw [← hv]
      have hlow : ∀ t, 1 ≤ ∑ g ∈ S.filter (fun g => f g = t), phi u x g :=
        fun t => (part_lower hnn hx _ (hpart t)).1
      have hsum1 : (k : ℝ) ≤ ∑ t, ∑ g ∈ S.filter (fun g => f g = t), phi u x g := by
        have := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hlow t)
        simpa using this
      by_cases hA : ∃ g0 ∈ S, 0 < u g0 ∧ u g0 ≤ 3 * x / 4
      · obtain ⟨g0, hg0, h1, h2⟩ := hA
        have hstrict : (k : ℝ) < ∑ t, ∑ g ∈ S.filter (fun g => f g = t), phi u x g := by
          have := Finset.sum_lt_sum (s := Finset.univ) (fun t _ => hlow t)
            ⟨f g0, Finset.mem_univ _, (part_lower hnn hx _ (hpart (f g0))).2 g0
              (Finset.mem_filter.mpr ⟨hg0, rfl⟩) h1 h2⟩
          simpa using this
        have hYi := own_bound hnn hx (Y i) hown
        linarith
      · push Not at hA
        have hYi := own_half hnn hx (Y i) hown fun g hg hle => by
          by_contra hpos
          push Not at hpos
          have := hA g (hYiS hg) hpos
          linarith
        linarith
    -- conclude
    have hmms : LittleCharity.MMS.mms (v i) k S ≤ 7 * x / 4 := by
      unfold LittleCharity.MMS.mms
      have : Nonempty (Fin m → Fin k) := ⟨fun _ => ⟨0, hk⟩⟩
      refine ciSup_le fun f => ?_
      obtain ⟨t, ht⟩ := key f
      exact (ciInf_le (Finite.bddBelow_range _) t).trans (by convert ht)
    linarith
