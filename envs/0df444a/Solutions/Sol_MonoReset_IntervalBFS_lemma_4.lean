-- Prove2me | solution 1 for MonoReset.IntervalBFS.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T04:48:54.377987+00:00
-- url     : https://prove2.me/submissions/f3fa5e5c-32c1-4ada-aef6-10dbf969785d

import Definitions.Def_MonoReset_IntervalBFS_Model

open Finset MonoReset.IntervalBFS

variable {n k : ℕ}

private lemma left_mem (I : Fin n × Fin n) : I.1 ∈ ivSet I := by
  simp only [ivSet, mem_filter, mem_univ, true_and]
  fin_omega

private lemma right_mem (I : Fin n × Fin n) : I.2 ∈ ivSet I := by
  simp [ivSet]

private lemma interval_singleton (a : Fin n) : ivSet (a, a) = {a} := by
  ext s
  simp only [ivSet, mem_filter, mem_univ, true_and, mem_singleton]
  fin_omega

private lemma interval_linear (a b s : Fin n) (hab : a ≤ b) :
    s ∈ ivSet (a, b) ↔ a ≤ s ∧ s ≤ b := by
  simp only [ivSet, mem_filter, mem_univ, true_and]
  fin_omega

private lemma interval_translate (a b s m : Fin n) :
    s ∈ ivSet (a, b) ↔ s - m ∈ ivSet (a - m, b - m) := by
  have : NeZero n := ⟨by have h := a.isLt; omega⟩
  simp only [ivSet, mem_filter, mem_univ, true_and, sub_sub_sub_cancel_right]

private lemma full_circle_iff (I : Fin n × Fin n) :
    ivSet I = univ ↔ (I.2 - I.1).val = n - 1 := by
  have : NeZero n := ⟨by have h := I.1.isLt; omega⟩
  have hn : 0 < n := by have h := I.1.isLt; omega
  constructor
  · intro h
    let z : Fin n := ⟨n - 1, by omega⟩
    have hz : I.1 + z ∈ ivSet I := by rw [h]; exact mem_univ _
    simp only [ivSet, mem_filter, mem_univ, true_and, add_sub_cancel_left] at hz
    have hlen := (I.2 - I.1).isLt
    dsimp [z] at hz
    omega
  · intro h
    ext s
    simp only [ivSet, mem_filter, mem_univ, true_and, iff_true]
    rw [h]
    have hs := (s - I.1).isLt
    omega

private lemma subset_prec_or_full (J I : Fin n × Fin n) (h : ivSet J ⊆ ivSet I) :
    (I.2 - I.1).val = n - 1 ∨ Prec J I := by
  have : NeZero n := ⟨by have hh := I.1.isLt; omega⟩
  by_cases hfull : (I.2 - I.1).val = n - 1
  · exact Or.inl hfull
  · right
    have ha := h (left_mem J)
    have hb := h (right_mem J)
    simp only [ivSet, mem_filter, mem_univ, true_and] at ha hb
    refine ⟨?_, hb⟩
    by_contra hrev
    have hn : 0 < n := by have hh := I.1.isLt; omega
    let z : Fin n := ⟨n - 1, by omega⟩
    have hz : I.1 + z ∈ ivSet J := by
      rw [interval_translate J.1 J.2 (I.1 + z) I.1]
      simp only [add_sub_cancel_left, ivSet, mem_filter, mem_univ, true_and]
      dsimp [z]
      fin_omega
    have hh := h hz
    simp only [ivSet, mem_filter, mem_univ, true_and, add_sub_cancel_left] at hh
    dsimp [z] at hh
    have hlen := (I.2 - I.1).isLt
    omega

private lemma monotone_fiber_interval (f : Fin n → Fin n) (hf : IsMonotonic f) (y : Fin n)
    (hy : ∃ x, f x = y) : ∃ I : Fin n × Fin n, ivSet I = univ.filter (fun x => f x = y) := by
  classical
  have : NeZero n := ⟨by have h := y.isLt; omega⟩
  rcases hf with hn | ⟨m, hm⟩
  · have h := y.isLt; omega
  · let F : Finset (Fin n) := univ.filter (fun x => f (m + x) = y)
    have hF : F.Nonempty := by
      obtain ⟨x, hx⟩ := hy
      refine ⟨x - m, ?_⟩
      simpa [F, add_comm m] using hx
    let a := F.min' hF
    let b := F.max' hF
    have ha : a ∈ F := min'_mem F hF
    have hb : b ∈ F := max'_mem F hF
    have hab : a ≤ b := min'_le F b hb
    have hfa : f (m + a) = y := (mem_filter.mp ha).2
    have hfb : f (m + b) = y := (mem_filter.mp hb).2
    have he (x : Fin n) : x ∈ ivSet (a, b) ↔ f (m + x) = y := by
      rw [interval_linear a b x hab]
      constructor
      · rintro ⟨hax, hxb⟩
        have hlo := hm hax
        have hhi := hm hxb
        dsimp only at hlo hhi
        rw [hfa] at hlo
        rw [hfb] at hhi
        have hEq : f (m + x) - f m = y - f m := Fin.ext (le_antisymm hhi hlo)
        simpa only [sub_add_cancel] using congrArg (fun t : Fin n => t + f m) hEq
      · intro hx
        have hxf : x ∈ F := mem_filter.mpr ⟨mem_univ _, hx⟩
        exact ⟨min'_le F x hxf, le_max' F x hxf⟩
    refine ⟨(m + a, m + b), ?_⟩
    ext x
    rw [interval_translate (m + a) (m + b) x m]
    simp only [add_sub_cancel_left]
    rw [he]
    simp only [mem_filter, mem_univ, true_and, add_comm m, sub_add_cancel]

private lemma monotone_image_between (f : Fin n → Fin n) (hf : IsMonotonic f)
    (a b s : Fin n) (hne : f a ≠ f b) (hs : s ∈ ivSet (a, b)) :
    f s ∈ ivSet (f a, f b) := by
  have : NeZero n := ⟨by have h := a.isLt; omega⟩
  rcases hf with hn | ⟨m, hm⟩
  · have h := a.isLt; omega
  · have hmono (x y : Fin n) (h : x - m ≤ y - m) :
        (f x - f m).val ≤ (f y - f m).val := by
      simpa only [add_comm m, sub_add_cancel] using hm h
    have hne' : f a - f m ≠ f b - f m := by
      intro h
      apply hne
      simpa only [sub_add_cancel] using congrArg (fun t : Fin n => t + f m) h
    rw [interval_translate a b s m] at hs
    rw [interval_translate (f a) (f b) (f s) (f m)]
    simp only [ivSet, mem_filter, mem_univ, true_and] at hs ⊢
    by_cases has : a - m ≤ s - m
    · by_cases hsb : s - m ≤ b - m
      · have h1 := hmono a s has
        have h2 := hmono s b hsb
        fin_omega
      · have hba : b - m ≤ a - m := by fin_omega
        have h1 := hmono b a hba
        have h2 := hmono a s has
        fin_omega
    · by_cases hsb : s - m ≤ b - m
      · have hba : b - m ≤ a - m := by fin_omega
        have h1 := hmono s b hsb
        have h2 := hmono b a hba
        fin_omega
      · fin_omega

private lemma mem_ivSet_or_swap (I : Fin n × Fin n) (h12 : I.1 ≠ I.2) (s : Fin n) :
    s ∈ ivSet I ∨ s ∈ ivSet (I.2, I.1) := by
  simp only [ivSet, mem_filter, mem_univ, true_and]
  fin_omega

private lemma endpoints_mem_subset_or_swap (I P : Fin n × Fin n)
    (h1 : I.1 ∈ ivSet P) (h2 : I.2 ∈ ivSet P) :
    ivSet I ⊆ ivSet P ∨ ivSet (I.2, I.1) ⊆ ivSet P := by
  simp only [ivSet, subset_iff, mem_filter, mem_univ, true_and] at h1 h2 ⊢
  by_cases hle : (I.1 - P.1).val ≤ (I.2 - P.1).val
  · left
    intro s hs
    fin_omega
  · right
    intro s hs
    fin_omega

private lemma univ_of_swap_subset (I : Fin n × Fin n) (h12 : I.1 ≠ I.2)
    (h : ivSet (I.2, I.1) ⊆ ivSet I) : ivSet I = univ := by
  ext s
  simp only [mem_univ, iff_true]
  rcases mem_ivSet_or_swap I h12 s with hs | hs
  · exact hs
  · exact h hs

theorem solution {n k : ℕ} (δ : Fin k → Fin n → Fin n) (hδ : ∀ a, IsMonotonic (δ a))
    (a : Fin k) (J I : Fin n × Fin n)
    (hI : ivSet I = Finset.univ.filter (fun s => δ a s ∈ ivSet J))
    (hIS : ivSet I ≠ Finset.univ) :
    ∃ J' : Fin n × Fin n, dPrime1 δ a (some I) = some J' ∧ Prec J' J := by
  have hJ_not_full : (J.2 - J.1).val ≠ n - 1 := by
    intro hfull
    have hJuniv : ivSet J = univ := (full_circle_iff J).mpr hfull
    apply hIS
    rw [hI, hJuniv]
    ext s
    simp
  have hI1 : δ a I.1 ∈ ivSet J := by
    have h := left_mem I
    rw [hI] at h
    exact (mem_filter.mp h).2
  have hI2 : δ a I.2 ∈ ivSet J := by
    have h := right_mem I
    rw [hI] at h
    exact (mem_filter.mp h).2
  by_cases hne : δ a I.1 ≠ δ a I.2
  · have h12 : I.1 ≠ I.2 := fun h => hne (congrArg (δ a) h)
    refine ⟨(δ a I.1, δ a I.2), ?_, ?_⟩
    · dsimp only [dPrime1]
      rw [if_pos hne]
    · rcases endpoints_mem_subset_or_swap (δ a I.1, δ a I.2) J hI1 hI2 with hsub | hswap
      · rcases subset_prec_or_full (δ a I.1, δ a I.2) J hsub with hfull | hprec
        · exact absurd hfull hJ_not_full
        · exact hprec
      · exfalso
        apply hIS
        apply univ_of_swap_subset I h12
        intro s hs
        have himg : δ a s ∈ ivSet (δ a I.2, δ a I.1) :=
          monotone_image_between (δ a) (hδ a) I.2 I.1 s hne.symm hs
        rw [hI]
        exact mem_filter.mpr ⟨mem_univ _, hswap himg⟩
  · have heq : δ a I.1 = δ a I.2 := not_ne_iff.mp hne
    by_cases h12 : I.1 = I.2
    · have hall : ∀ s ∈ ivSet I, δ a s = δ a I.1 := by
        intro s hs
        have hI_eq : I = (I.1, I.1) := Prod.ext rfl h12.symm
        rw [hI_eq, interval_singleton] at hs
        rw [mem_singleton.mp hs]
      refine ⟨(δ a I.1, δ a I.1), ?_, ?_⟩
      · dsimp only [dPrime1]
        rw [if_neg hne, if_pos hall]
      · simp only [ivSet, mem_filter, mem_univ, true_and] at hI1
        exact ⟨le_rfl, hI1⟩
    · obtain ⟨P, hP⟩ := monotone_fiber_interval (δ a) (hδ a) (δ a I.1) ⟨I.1, rfl⟩
      have hP1 : I.1 ∈ ivSet P := by rw [hP]; simp
      have hP2 : I.2 ∈ ivSet P := by rw [hP]; simp [heq]
      have hPI : ivSet P ⊆ ivSet I := by
        intro s hs
        rw [hP] at hs
        have hds : δ a s = δ a I.1 := (mem_filter.mp hs).2
        rw [hI]
        exact mem_filter.mpr ⟨mem_univ _, by rw [hds]; exact hI1⟩
      rcases endpoints_mem_subset_or_swap I P hP1 hP2 with hIP | hswap
      · have hall : ∀ s ∈ ivSet I, δ a s = δ a I.1 := by
          intro s hs
          have hsP := hIP hs
          rw [hP] at hsP
          exact (mem_filter.mp hsP).2
        refine ⟨(δ a I.1, δ a I.1), ?_, ?_⟩
        · dsimp only [dPrime1]
          rw [if_neg hne, if_pos hall]
        · simp only [ivSet, mem_filter, mem_univ, true_and] at hI1
          exact ⟨le_rfl, hI1⟩
      · exfalso
        exact hIS (univ_of_swap_subset I h12 (hswap.trans hPI))
