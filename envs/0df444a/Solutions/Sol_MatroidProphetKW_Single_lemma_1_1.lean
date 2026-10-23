-- Prove2me | solution 1 for MatroidProphetKW.Single.lemma_1_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T15:54:18.954729+00:00
-- url     : https://prove2.me/submissions/ac4ca93f-09e2-47f3-9580-efcb8c5b1e79

import Mathlib

open Set in
theorem solution {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α)
    (V R : Finset α) (hV : M.Indep (↑V : Set α)) (hR : M.Indep (↑R : Set α))
    (hcard : V.card = R.card) :
    ∃ φ : V ≃ R, ∀ v : V, M.Indep (↑(insert (v : α) (R.erase (φ v : α))) : Set α) := by
  classical
  let t : V → Finset α := fun v => R.filter (fun r => M.Indep (↑(insert (v : α) (R.erase r)) : Set α))
  -- every candidate in `t v` lies in `R`
  have htR : ∀ v, t v ⊆ R := fun v => Finset.filter_subset _ _
  -- full case
  have hfull : ∀ v : V, ((v : α) ∈ R ∨ (v : α) ∉ M.closure (↑R)) → t v = R := by
    intro v hv
    apply Finset.filter_true_of_mem
    intro r hr
    rcases hv with hvR | hvcl
    · by_cases hrv : r = v
      · subst hrv
        simpa [Finset.insert_erase hvR] using hR
      · have : insert (v : α) (R.erase r) = R.erase r :=
          Finset.insert_eq_of_mem (Finset.mem_erase.2 ⟨fun h => hrv h.symm, hvR⟩)
        rw [this]
        exact hR.subset (by simp)
    · have hvE : (v : α) ∈ M.E := hV.subset_ground (by simp)
      have hins : M.Indep (insert (v : α) (↑R : Set α)) :=
        (hR.insert_indep_iff_of_notMem (fun h => hvcl (M.subset_closure _ hR.subset_ground h))).2
          ⟨hvE, hvcl⟩
      exact hins.subset (by
        intro x hx
        simp only [Finset.coe_insert, Finset.coe_erase, mem_insert_iff, mem_sdiff,
          Finset.mem_coe, mem_singleton_iff] at hx ⊢
        tauto)
  have hall : ∀ s : Finset V, s.card ≤ (s.biUnion t).card := by
    intro s
    by_cases hA : ∃ v ∈ s, ((v : α) ∈ R ∨ (v : α) ∉ M.closure (↑R))
    · obtain ⟨v, hvs, hv⟩ := hA
      have h1 : R ⊆ s.biUnion t := by
        rw [← hfull v hv]; exact Finset.subset_biUnion_of_mem t hvs
      calc s.card ≤ Finset.univ.card := Finset.card_le_univ s
        _ = V.card := by simp
        _ = R.card := hcard
        _ ≤ _ := Finset.card_le_card h1
    · push Not at hA
      set U := s.biUnion t with hU
      have hUR : (↑U : Set α) ⊆ ↑R := by
        intro x hx
        simp only [hU, Finset.coe_biUnion, mem_iUnion, Finset.mem_coe] at hx
        obtain ⟨v, -, hx⟩ := hx
        exact htR v hx
      have hUind : M.Indep (↑U : Set α) := hR.subset hUR
      let S : Finset α := s.image Subtype.val
      have hSV : (↑S : Set α) ⊆ ↑V := by
        intro x hx
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
        exact v.2
      have hSind : M.Indep (↑S : Set α) := hV.subset hSV
      have hScl : (↑S : Set α) ⊆ M.closure ↑U := by
        intro x hx
        obtain ⟨v, hvs, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
        obtain ⟨hvR, hvcl⟩ := hA v hvs
        have hC := hR.fundCircuit_isCircuit hvcl (by simpa using hvR)
        have hsub : M.fundCircuit (v : α) ↑R \ {(v : α)} ⊆ ↑U := by
          intro y hy
          have hyC := hy.1
          have hyv : y ≠ v := hy.2
          have hyR : y ∈ R := by
            have := M.fundCircuit_subset_insert (v : α) (↑R) hyC
            simpa [hyv] using this
          have hind := (hR.mem_fundCircuit_iff hvcl (by simpa using hvR)).1 hyC
          simp only [hU, Finset.coe_biUnion, mem_iUnion, Finset.mem_coe]
          refine ⟨v, hvs, ?_⟩
          simp only [t, Finset.mem_filter]
          refine ⟨hyR, ?_⟩
          convert hind using 1
          ext z
          simp only [Finset.coe_insert, Finset.coe_erase, mem_insert_iff, mem_sdiff,
            Finset.mem_coe, mem_singleton_iff]
          constructor
          · rintro (rfl | ⟨h1, h2⟩)
            · exact ⟨Or.inl rfl, fun h => hyv h.symm⟩
            · exact ⟨Or.inr h1, h2⟩
          · rintro ⟨h1 | h1, h2⟩
            · exact Or.inl h1
            · exact Or.inr ⟨h1, h2⟩
        exact M.closure_subset_closure hsub (hC.mem_closure_sdiff_singleton_of_mem (M.mem_fundCircuit _ _))
      have key : (↑S : Set α).encard ≤ (↑U : Set α).encard := by
        rw [← hSind.eRk_eq_encard, ← hUind.eRk_eq_encard, ← M.eRk_closure_eq (↑U : Set α)]
        exact M.eRk_mono hScl
      rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard] at key
      have key' : S.card ≤ U.card := by exact_mod_cast key
      have hSc : S.card = s.card := Finset.card_image_of_injective s Subtype.val_injective
      omega
  obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  let g : V → R := fun v => ⟨f v, htR v (hft v)⟩
  have hginj : Function.Injective g := fun a b h => hfinj (congrArg Subtype.val h)
  have hgbij : Function.Bijective g := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hginj, by simpa using hcard⟩
  refine ⟨Equiv.ofBijective g hgbij, fun v => ?_⟩
  have := hft v
  simp only [t, Finset.mem_filter] at this
  exact this.2

