-- Prove2me | solution 1 for NashWilliams.exists_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:30:13.023332+00:00
-- url     : https://prove2.me/submissions/069887db-e282-43dc-b1c0-6c89d938f902

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting
public import Theorems.Thm_NashWilliams_joins_oth
public import Theorems.Thm_NashWilliams_dangerous_of_not_req
public import Theorems.Thm_NashWilliams_two_mul_dsF_le
public import Theorems.Thm_NashWilliams_dsF_union_add_inter
public import Theorems.Thm_NashWilliams_cutF_singleton_le_dsF
public import Theorems.Thm_NashWilliams_one_le_dsF
public import Theorems.Thm_NashWilliams_cr_three
public import Theorems.Thm_NashWilliams_cutF_eq_sum


set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]
namespace NashWilliams
theorem _root_.solution [DecidableEq ι] {K : ℕ} (hK : 2 ≤ K) {T : Finset V} {s : V}
    {ends : ι → V × V} {F : Finset ι} (hin : Inside T ends F) (hreq : Req K (T.erase s) ends F)
    (heven : Even (cutF ends F {s})) (hpos : 0 < cutF ends F {s}) :
    ∃ i ∈ F, ∃ j ∈ F, ∃ u v : V, i ≠ j ∧ Joins s u (ends i) ∧ Joins s v (ends j) ∧
      Req K (T.erase s) (Function.update ends i (u, v)) (F.erase j) := by
  classical
  obtain ⟨i, hiF, hiSE⟩ : ∃ i ∈ F, ((ends i).1 = s) ≠ ((ends i).2 = s) := by
    obtain ⟨i, hi⟩ := Finset.card_pos.1 hpos
    simp only [mem_filter, mem_singleton] at hi
    exact ⟨i, hi.1, hi.2⟩
  set u := oth s (ends i) with hu_def
  have hJi : Joins s u (ends i) := joins_oth hiSE
  have huT : u ∈ T.erase s := by
    obtain ⟨h1, h2⟩ := hin i hiF
    obtain ⟨h | h, hus⟩ := hJi
    · rw [h] at h2; exact mem_erase.2 ⟨hus, h2⟩
    · rw [h] at h1; exact mem_erase.2 ⟨hus, h1⟩
  by_contra hcon
  set D := (T.erase s).powerset.filter fun X => u ∈ X ∧ X ≠ T.erase s ∧ cutF ends F X ≤ K + 1
    with hD
  have hmemD : ∀ X ∈ D, X ⊆ T.erase s ∧ u ∈ X ∧ X ≠ T.erase s ∧ cutF ends F X ≤ K + 1 := by
    intro X hX
    simp only [hD, mem_filter, mem_powerset] at hX
    exact ⟨hX.1, hX.2⟩
  have hdang : ∀ j ∈ F, j ≠ i → ((ends j).1 = s) ≠ ((ends j).2 = s) →
      ∃ X ∈ D, oth s (ends j) ∈ X := by
    intro j hj hji hjSE
    have hfail : ¬ Req K (T.erase s) (Function.update ends i (u, oth s (ends j))) (F.erase j) :=
      fun h => hcon ⟨i, hiF, j, hj, u, oth s (ends j), Ne.symm hji, hJi, joins_oth hjSE, h⟩
    obtain ⟨X, hXT, hXne, huX, hvX, hXc⟩ :=
      dangerous_of_not_req hreq hiF hj (Ne.symm hji) hJi (joins_oth hjSE) hfail
    exact ⟨X, mem_filter.2 ⟨mem_powerset.2 hXT, huX, hXne, hXc⟩, hvX⟩
  set Nb := (F.filter fun j => j ≠ i ∧ ((ends j).1 = s) ≠ ((ends j).2 = s)).image
    fun j => oth s (ends j) with hNb
  have hNbD : ∀ v ∈ Nb, ∃ X ∈ D, v ∈ X := by
    intro v hv
    simp only [hNb, mem_image, mem_filter] at hv
    obtain ⟨j, ⟨hj, hji, hjSE⟩, rfl⟩ := hv
    exact hdang j hj hji hjSE
  obtain ⟨C, hCmem, hCmin⟩ :=
    (D.powerset.filter fun C => ∀ v ∈ Nb, ∃ X ∈ C, v ∈ X).exists_min_image card
      ⟨D, mem_filter.2 ⟨mem_powerset_self D, hNbD⟩⟩
  simp only [mem_filter, mem_powerset] at hCmem hCmin
  obtain ⟨hCD, hCcov⟩ := hCmem
  have hall : ∀ l ∈ F, ((ends l).1 = s) ≠ ((ends l).2 = s) → oth s (ends l) = u ∨
      oth s (ends l) ∈ Nb := by
    intro l hl hlSE
    by_cases hli : l = i
    · left; rw [hli]
    · right
      exact mem_image.2 ⟨l, mem_filter.2 ⟨hl, hli, hlSE⟩, rfl⟩
  have hhalf : ∀ X ∈ D, 2 * dsF s ends F X ≤ cutF ends F {s} := by
    intro X hX
    obtain ⟨hXT, huX, hXne, hXc⟩ := hmemD X hX
    exact two_mul_dsF_le hin hreq heven hXT ⟨u, huX⟩ hXne hXc
  have hpriv : ∀ X ∈ C, ∃ v ∈ Nb, v ∈ X ∧ ∀ Y ∈ C, Y ≠ X → v ∉ Y := by
    intro X hX
    by_contra! h
    have hcov' : ∀ v ∈ Nb, ∃ Y ∈ C.erase X, v ∈ Y := by
      intro v hv
      obtain ⟨Z, hZ, hvZ⟩ := hCcov v hv
      by_cases hZX : Z = X
      · obtain ⟨Y, hY, hYX, hvY⟩ := h v hv (hZX ▸ hvZ)
        exact ⟨Y, mem_erase.2 ⟨hYX, hY⟩, hvY⟩
      · exact ⟨Z, mem_erase.2 ⟨hZX, hZ⟩, hvZ⟩
    have := hCmin (C.erase X) ⟨(erase_subset X C).trans hCD, hcov'⟩
    have h2 := card_erase_lt_of_mem hX
    omega
  obtain h0 | h1 | h2 | h3 : C.card = 0 ∨ C.card = 1 ∨ C.card = 2 ∨ 2 < C.card := by omega
  · -- no cover set: `i` is the only edge at `s`
    rw [card_eq_zero] at h0
    subst h0
    have : cutF ends F {s} ≤ 1 := by
      unfold cutF
      calc _ ≤ ({i} : Finset ι).card := by
            refine card_le_card fun l hl => ?_
            simp only [mem_filter, mem_singleton] at hl
            by_contra hli
            rw [mem_singleton] at hli
            have hv : oth s (ends l) ∈ Nb := mem_image.2 ⟨l, mem_filter.2 ⟨hl.1, hli, hl.2⟩, rfl⟩
            obtain ⟨X, hX, -⟩ := hCcov _ hv
            simp at hX
        _ = 1 := card_singleton i
    obtain ⟨r, hr⟩ := heven
    omega
  · obtain ⟨X, rfl⟩ := card_eq_one.1 h1
    have hXD : X ∈ D := hCD (mem_singleton_self X)
    have hle : cutF ends F {s} ≤ dsF s ends F X := by
      refine cutF_singleton_le_dsF fun l hl hlSE => ?_
      rcases hall l hl hlSE with h | h
      · rw [h]; exact (hmemD X hXD).2.1
      · obtain ⟨Y, hY, hvY⟩ := hCcov _ h
        rw [mem_singleton] at hY
        exact hY ▸ hvY
    have := hhalf X hXD
    omega
  · obtain ⟨X, Y, hXY, rfl⟩ := card_eq_two.1 h2
    have hXD : X ∈ D := hCD (by simp)
    have hYD : Y ∈ D := hCD (by simp)
    have hle : cutF ends F {s} ≤ dsF s ends F (X ∪ Y) := by
      refine cutF_singleton_le_dsF fun l hl hlSE => ?_
      rcases hall l hl hlSE with h | h
      · rw [h]; exact mem_union_left _ (hmemD X hXD).2.1
      · obtain ⟨Z, hZ, hvZ⟩ := hCcov _ h
        simp only [mem_insert, mem_singleton] at hZ
        rcases hZ with rfl | rfl
        · exact mem_union_left _ hvZ
        · exact mem_union_right _ hvZ
    have hmod := dsF_union_add_inter s ends F X Y
    have hone := one_le_dsF hiF hJi (mem_inter.2 ⟨(hmemD X hXD).2.1, (hmemD Y hYD).2.1⟩)
    have := hhalf X hXD
    have := hhalf Y hYD
    omega
  · obtain ⟨X1, hX1, X2, hX2, X3, hX3, h12, h13, h23⟩ := two_lt_card.1 h3
    obtain ⟨hX1T, hu1, hX1ne, hX1c⟩ := hmemD X1 (hCD hX1)
    obtain ⟨hX2T, hu2, hX2ne, hX2c⟩ := hmemD X2 (hCD hX2)
    obtain ⟨hX3T, hu3, hX3ne, hX3c⟩ := hmemD X3 (hCD hX3)
    obtain ⟨v1, -, hv1, hv1o⟩ := hpriv X1 hX1
    obtain ⟨v2, -, hv2, hv2o⟩ := hpriv X2 hX2
    obtain ⟨v3, -, hv3, hv3o⟩ := hpriv X3 hX3
    have h12' := hv1o X2 hX2 (Ne.symm h12)
    have h13' := hv1o X3 hX3 (Ne.symm h13)
    have h21' := hv2o X1 hX1 h12
    have h23' := hv2o X3 hX3 (Ne.symm h23)
    have h31' := hv3o X1 hX1 h13
    have h32' := hv3o X2 hX2 h23
    have hR1 : K ≤ cutF ends F ((X1 \ X2) \ X3) := by
      refine hreq _ (sdiff_subset.trans (sdiff_subset.trans hX1T)) ⟨v1, by simp [hv1, h12', h13']⟩ ?_
      intro h
      have : u ∈ (X1 \ X2) \ X3 := by rw [h]; exact huT
      simp [hu2] at this
    have hR2 : K ≤ cutF ends F ((X2 \ X1) \ X3) := by
      refine hreq _ (sdiff_subset.trans (sdiff_subset.trans hX2T)) ⟨v2, by simp [hv2, h21', h23']⟩ ?_
      intro h
      have : u ∈ (X2 \ X1) \ X3 := by rw [h]; exact huT
      simp [hu1] at this
    have hR3 : K ≤ cutF ends F ((X3 \ X1) \ X2) := by
      refine hreq _ (sdiff_subset.trans (sdiff_subset.trans hX3T)) ⟨v3, by simp [hv3, h31', h32']⟩ ?_
      intro h
      have : u ∈ (X3 \ X1) \ X2 := by rw [h]; exact huT
      simp [hu1] at this
    have hZ : K ≤ cutF ends F (X1 ∩ X2 ∩ X3) := by
      refine hreq _ (inter_subset_left.trans (inter_subset_left.trans hX1T))
        ⟨u, by simp [hu1, hu2, hu3]⟩ ?_
      intro h
      have : v1 ∈ X1 ∩ X2 ∩ X3 := by rw [h]; exact hX1T hv1
      simp [h12'] at this
    have key := Finset.sum_le_sum fun l (_ : l ∈ F) => cr_three (ends l) X1 X2 X3
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← cutF_eq_sum] at key
    have hind : 1 ≤ ∑ l ∈ F, (if ((ends l).1 ∈ X1 ∩ X2 ∩ X3 ∧ (ends l).2 ∉ X1 ∪ X2 ∪ X3) ∨
        ((ends l).2 ∈ X1 ∩ X2 ∩ X3 ∧ (ends l).1 ∉ X1 ∪ X2 ∪ X3) then 1 else 0) := by
      refine le_trans ?_ (Finset.single_le_sum (fun l _ => Nat.zero_le _) hiF)
      have hs1 : s ∉ X1 := fun h => by simpa using hX1T h
      have hs2 : s ∉ X2 := fun h => by simpa using hX2T h
      have hs3 : s ∉ X3 := fun h => by simpa using hX3T h
      obtain ⟨h | h, -⟩ := hJi <;> rw [h] <;> simp [hu1, hu2, hu3, hs1, hs2, hs3]
    omega
end NashWilliams
