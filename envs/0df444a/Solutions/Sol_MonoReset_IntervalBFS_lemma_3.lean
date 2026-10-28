-- Prove2me | solution 1 for MonoReset.IntervalBFS.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T04:48:54.941165+00:00
-- url     : https://prove2.me/submissions/4eb8fe7d-0fcd-46d2-b6e0-756d7bdab68f

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

private lemma prec_subset (J I : Fin n × Fin n) (h : Prec J I) : ivSet J ⊆ ivSet I := by
  intro s hs
  have htr := interval_translate J.1 J.2 s I.1
  have hj : s - I.1 ∈ ivSet (J.1 - I.1, J.2 - I.1) := htr.mp hs
  have hxy : J.1 - I.1 ≤ J.2 - I.1 := h.1
  have hy := (interval_linear _ _ _ hxy).mp hj
  simp only [ivSet, mem_filter, mem_univ, true_and]
  exact hy.2.trans h.2

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

private lemma prec_mem_complement_left {J I : Fin n × Fin n} (hJ : J.1 ≠ J.2) (hJI : Prec J I) :
    I.1 ∈ ivSet (J.2, J.1) ∧ I.2 ∈ ivSet (J.2, J.1) := by
  rcases hJI with ⟨h1, h2⟩
  simp only [ivSet, mem_filter, mem_univ, true_and]
  constructor <;> fin_omega

private lemma prec_mem_complement_mid {J I : Fin n × Fin n} (hIJ : I.1 ≠ J.2) (hJI : Prec J I) :
    J.1 ∈ ivSet (I.1, J.2) ∧ I.2 ∈ ivSet (J.2, I.1) := by
  rcases hJI with ⟨h1, h2⟩
  simp only [ivSet, mem_filter, mem_univ, true_and]
  exact ⟨h1, by fin_omega⟩

private lemma lemma_3_step (δ : Fin k → Fin n → Fin n) (hδ : ∀ a, IsMonotonic (δ a))
    (a : Fin k) (I I' J : Fin n × Fin n)
    (hI : dPrime1 δ a (some I) = some I') (hJI : Prec J I) :
    ∃ J' : Fin n × Fin n, dPrime1 δ a (some J) = some J' ∧ Prec J' I' := by
  have hsubJI : ivSet J ⊆ ivSet I := prec_subset J I hJI
  have hJ1 : J.1 ∈ ivSet I := hsubJI (left_mem J)
  have hJ2 : J.2 ∈ ivSet I := hsubJI (right_mem J)
  by_cases hneI : δ a I.1 ≠ δ a I.2
  · have hI' : I' = (δ a I.1, δ a I.2) := by
      dsimp only [dPrime1] at hI
      rw [if_pos hneI] at hI
      exact (Option.some.inj hI).symm
    subst hI'
    have hJ1' : δ a J.1 ∈ ivSet (δ a I.1, δ a I.2) :=
      monotone_image_between (δ a) (hδ a) I.1 I.2 J.1 hneI hJ1
    have hJ2' : δ a J.2 ∈ ivSet (δ a I.1, δ a I.2) :=
      monotone_image_between (δ a) (hδ a) I.1 I.2 J.2 hneI hJ2
    by_cases hneJ : δ a J.1 ≠ δ a J.2
    · refine ⟨(δ a J.1, δ a J.2), ?_, ?_⟩
      · dsimp only [dPrime1]
        rw [if_pos hneJ]
      · have hIJ_ne : I.1 ≠ J.2 := by
          intro heq
          rcases hJI with ⟨h1, _⟩
          have hJ_eq : J.1 = J.2 := by fin_omega
          exact hneJ (congrArg (δ a) hJ_eq)
        have hmid := prec_mem_complement_mid hIJ_ne hJI
        have hneIJ : δ a I.1 ≠ δ a J.2 := by
          intro heq
          obtain ⟨P, hP⟩ := monotone_fiber_interval (δ a) (hδ a) (δ a I.1) ⟨I.1, rfl⟩
          have hP1 : I.1 ∈ ivSet P := by rw [hP]; simp
          have hP2 : J.2 ∈ ivSet P := by rw [hP]; simp [heq]
          rcases endpoints_mem_subset_or_swap (I.1, J.2) P hP1 hP2 with h1 | h2
          · have hJ1P := h1 hmid.1
            rw [hP] at hJ1P
            have hJ1eq : δ a J.1 = δ a I.1 := (mem_filter.mp hJ1P).2
            exact hneJ (hJ1eq.trans heq)
          · have hI2P := h2 hmid.2
            rw [hP] at hI2P
            have hI2eq : δ a I.2 = δ a I.1 := (mem_filter.mp hI2P).2
            exact hneI hI2eq.symm
        have h1 : δ a J.1 ∈ ivSet (δ a I.1, δ a J.2) :=
          monotone_image_between (δ a) (hδ a) I.1 J.2 J.1 hneIJ hmid.1
        simp only [ivSet, mem_filter, mem_univ, true_and] at h1 hJ2'
        exact ⟨h1, hJ2'⟩
    · have heqJ : δ a J.1 = δ a J.2 := not_ne_iff.mp hneJ
      by_cases hJ12 : J.1 = J.2
      · have hallJ : ∀ s ∈ ivSet J, δ a s = δ a J.1 := by
          intro s hs
          have hJ_eq : J = (J.1, J.1) := Prod.ext rfl hJ12.symm
          rw [hJ_eq, interval_singleton] at hs
          rw [mem_singleton.mp hs]
        refine ⟨(δ a J.1, δ a J.1), ?_, ?_⟩
        · dsimp only [dPrime1]
          rw [if_neg hneJ, if_pos hallJ]
        · simp only [ivSet, mem_filter, mem_univ, true_and] at hJ1'
          exact ⟨le_rfl, hJ1'⟩
      · obtain ⟨P, hP⟩ := monotone_fiber_interval (δ a) (hδ a) (δ a J.1) ⟨J.1, rfl⟩
        have hP1 : J.1 ∈ ivSet P := by rw [hP]; simp
        have hP2 : J.2 ∈ ivSet P := by rw [hP]; simp [heqJ]
        rcases endpoints_mem_subset_or_swap J P hP1 hP2 with hJP | hswap
        · have hallJ : ∀ s ∈ ivSet J, δ a s = δ a J.1 := by
            intro s hs
            have hsP := hJP hs
            rw [hP] at hsP
            exact (mem_filter.mp hsP).2
          refine ⟨(δ a J.1, δ a J.1), ?_, ?_⟩
          · dsimp only [dPrime1]
            rw [if_neg hneJ, if_pos hallJ]
          · simp only [ivSet, mem_filter, mem_univ, true_and] at hJ1'
            exact ⟨le_rfl, hJ1'⟩
        · exfalso
          have hcomp := prec_mem_complement_left hJ12 hJI
          have hI1P := hswap hcomp.1
          have hI2P := hswap hcomp.2
          rw [hP] at hI1P hI2P
          have h1 : δ a I.1 = δ a J.1 := (mem_filter.mp hI1P).2
          have h2 : δ a I.2 = δ a J.1 := (mem_filter.mp hI2P).2
          exact hneI (h1.trans h2.symm)
  · dsimp only [dPrime1] at hI
    rw [if_neg hneI] at hI
    split_ifs at hI with hallI
    have hI' : I' = (δ a I.1, δ a I.1) := (Option.some.inj hI).symm
    subst hI'
    have hallJ : ∀ s ∈ ivSet J, δ a s = δ a I.1 := fun s hs => hallI s (hsubJI hs)
    have hJ1eq : δ a J.1 = δ a I.1 := hallJ J.1 (left_mem J)
    have hJ2eq : δ a J.2 = δ a I.1 := hallJ J.2 (right_mem J)
    have hneJ : ¬ (δ a J.1 ≠ δ a J.2) := by
      rw [hJ1eq, hJ2eq]
      exact not_not.mpr rfl
    have hallJ' : ∀ s ∈ ivSet J, δ a s = δ a J.1 := by
      intro s hs
      rw [hallJ s hs, hJ1eq]
    refine ⟨(δ a I.1, δ a I.1), ?_, ⟨le_rfl, le_rfl⟩⟩
    dsimp only [dPrime1]
    rw [if_neg hneJ, if_pos hallJ', hJ1eq]

private lemma dPrime_none (δ : Fin k → Fin n → Fin n) (τ : List (Fin k)) :
    dPrime δ τ none = none := by
  induction τ with
  | nil => rfl
  | cons a τ ih => exact ih

theorem solution {n k : ℕ} (δ : Fin k → Fin n → Fin n) (hδ : ∀ a, IsMonotonic (δ a))
    (τ : List (Fin k)) (I I' : Fin n × Fin n) (hI : dPrime δ τ (some I) = some I')
    (J : Fin n × Fin n) (hJI : Prec J I) :
    ∃ J' : Fin n × Fin n, dPrime δ τ (some J) = some J' ∧ Prec J' I' := by
  induction τ generalizing I J with
  | nil =>
    have heq : I = I' := Option.some.inj hI
    subst heq
    exact ⟨J, rfl, hJI⟩
  | cons a τ ih =>
    change dPrime δ τ (dPrime1 δ a (some I)) = some I' at hI
    cases hd : dPrime1 δ a (some I) with
    | none =>
      rw [hd, dPrime_none] at hI
      contradiction
    | some K =>
      rw [hd] at hI
      obtain ⟨J₁, hJ₁, hprec₁⟩ := lemma_3_step δ hδ a I K J hd hJI
      obtain ⟨J', hJ', hprec'⟩ := ih K hI J₁ hprec₁
      refine ⟨J', ?_, hprec'⟩
      change dPrime δ τ (dPrime1 δ a (some J)) = some J'
      rw [hJ₁]
      exact hJ'
