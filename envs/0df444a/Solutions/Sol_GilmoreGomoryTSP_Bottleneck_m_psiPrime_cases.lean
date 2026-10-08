-- Prove2me | solution 1 for GilmoreGomoryTSP.Bottleneck.m_psiPrime_cases
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:14:59.263166+00:00
-- url     : https://prove2.me/submissions/b739b9b2-58f6-4c55-a549-b980a4e5c43c

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_Bottleneck_Model



namespace GilmoreGomoryTSP.Bottleneck

open MeasureTheory

lemma gg_c_nonneg {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, g x = 0) (i j : Fin (n + 1)) :
    0 ≤ GilmoreGomoryTSP.MinCost.c f g A B i j := by
  unfold GilmoreGomoryTSP.MinCost.c
  split_ifs with h
  · exact intervalIntegral.integral_nonneg h (fun x _ => hf0 x)
  · simp [hg0]

lemma gg_c_anti {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, g x = 0) (hf : MeasureTheory.LocallyIntegrable f)
    {i i' j j' : Fin (n + 1)} (hB : B i ≤ B i') (hA : A j' ≤ A j) :
    GilmoreGomoryTSP.MinCost.c f g A B i' j' ≤ GilmoreGomoryTSP.MinCost.c f g A B i j := by
  by_cases h' : B i' ≤ A j'
  · have h : B i ≤ A j := by linarith
    have e1 : GilmoreGomoryTSP.MinCost.c f g A B i' j' = ∫ x in B i'..A j', f x := by
      simp [GilmoreGomoryTSP.MinCost.c, h']
    have e2 : GilmoreGomoryTSP.MinCost.c f g A B i j = ∫ x in B i..A j, f x := by
      simp [GilmoreGomoryTSP.MinCost.c, h]
    rw [e1, e2]
    exact intervalIntegral.integral_mono_interval hB h' hA
      (Filter.Eventually.of_forall (fun x => hf0 x)) (MeasureTheory.IntegrableOn.intervalIntegrable (hf.integrableOn_isCompact isCompact_uIcc))
  · have e1 : GilmoreGomoryTSP.MinCost.c f g A B i' j' = 0 := by
      simp [GilmoreGomoryTSP.MinCost.c, h', hg0]
    rw [e1]
    exact gg_c_nonneg f g A B hf0 hg0 i j

lemma gg_exists_a {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (q : Fin n)
    (h : ∃ j : Fin (n + 1), (σ j : ℕ) ≤ q ∧ (q : ℕ) < j) : ∃ i : Fin (n + 1), (i : ℕ) ≤ q ∧ (q : ℕ) < σ i := by
  by_contra hne
  push_neg at hne
  obtain ⟨j, hj1, hj2⟩ := h
  have hsub : (Finset.Iic q.castSucc).image σ ⊆ Finset.Iic q.castSucc := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_Iic] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Fin.le_def] at hy ⊢
    exact hne y (by simpa using hy)
  have hcard : ((Finset.Iic q.castSucc).image σ).card = (Finset.Iic q.castSucc).card :=
    Finset.card_image_of_injective _ σ.injective
  have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  have hmem : σ j ∈ Finset.Iic q.castSucc := by
    simp only [Finset.mem_Iic, Fin.le_def]; simpa using hj1
  rw [← heq] at hmem
  simp only [Finset.mem_image, Finset.mem_Iic] at hmem
  obtain ⟨x, hx, hxj⟩ := hmem
  have := σ.injective hxj
  subst this
  rw [Fin.le_def] at hx
  simp at hx
  omega

theorem gg_eq30 {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, g x = 0) (hf : MeasureTheory.LocallyIntegrable f)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ))
    (ψ : Equiv.Perm (Fin (n + 1))) (q : Fin n) (hq : q ∈ starArcs φ ψ) :
    arcCost f g A B φ q ≤ m f g A B ψ := by
  unfold starArcs at hq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
  have hex : ∃ i : Fin (n + 1), (i : ℕ) ≤ q ∧ (q : ℕ) < (φ.symm (ψ i) : ℕ) := by
    rcases hq with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact ⟨i, hi⟩
    · exact gg_exists_a (ψ.trans φ.symm) q ⟨j, hj⟩
  obtain ⟨i, hi1, hi2⟩ := hex
  have hBi : B i ≤ B q.castSucc := hB (by rw [Fin.le_def]; simpa using hi1)
  have hAi : A (φ q.succ) ≤ A (ψ i) := by
    have := hφ (show q.succ ≤ φ.symm (ψ i) by rw [Fin.le_def]; simpa using hi2)
    simpa using this
  have := gg_c_anti f g A B hf0 hg0 hf hBi hAi
  refine le_trans this ?_
  exact Finset.le_sup' (fun i => GilmoreGomoryTSP.MinCost.c f g A B i (ψ i)) (Finset.mem_univ i)

theorem gg_phi_min {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, g x = 0) (hf : MeasureTheory.LocallyIntegrable f)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ)) :
    ∀ ψ : Equiv.Perm (Fin (n + 1)), m f g A B φ ≤ m f g A B ψ := by
  intro ψ
  unfold m
  apply Finset.sup'_le
  intro i _
  have hex : ∃ j, j ≤ i ∧ i ≤ φ.symm (ψ j) := by
    by_contra hne
    push_neg at hne
    have hsub : (Finset.Iic i).image (ψ.trans φ.symm) ⊆ Finset.Iio i := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_Iic, Finset.mem_Iio] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      exact hne y hy
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (ψ.trans φ.symm).injective] at h1
    simp [Fin.card_Iic, Fin.card_Iio] at h1
  obtain ⟨j, hj1, hj2⟩ := hex
  have hBj : B j ≤ B i := hB hj1
  have hAj : A (φ i) ≤ A (ψ j) := by
    have := hφ hj2
    simpa using this
  have := gg_c_anti f g A B hf0 hg0 hf hBj hAj
  refine le_trans this ?_
  exact Finset.le_sup' (fun i => GilmoreGomoryTSP.MinCost.c f g A B i (ψ i)) (Finset.mem_univ j)


def GGInv {n : ℕ} (φ σ : Equiv.Perm (Fin (n + 1))) (U : Finset (Fin n)) : Prop :=
  (∀ i, (∀ u ∈ U, i ≠ u.castSucc ∧ i ≠ u.succ) → σ i = φ i) ∧
  (∀ u ∈ U, σ u.castSucc = φ u.succ) ∧
  (∀ i, σ i = φ i ∨ (∃ u ∈ U, u.castSucc < i ∧ σ i = φ u.castSucc) ∨ ∃ u ∈ U, i = u.castSucc)

lemma gg_inv_step {n : ℕ} (φ σ : Equiv.Perm (Fin (n + 1))) (U : Finset (Fin n)) (q : Fin n)
    (hU : ∀ u ∈ U, u < q) (h : GGInv φ σ U) :
    GGInv φ (interchange σ q.castSucc q.succ) (insert q U) := by
  obtain ⟨ha, hb, hc⟩ := h
  have hsw : ∀ i, interchange σ q.castSucc q.succ i = σ (Equiv.swap q.castSucc q.succ i) := by
    intro i; rfl
  have hq1 : interchange σ q.castSucc q.succ q.castSucc = σ q.succ := by
    rw [hsw, Equiv.swap_apply_left]
  have hq2 : interchange σ q.castSucc q.succ q.succ = σ q.castSucc := by
    rw [hsw, Equiv.swap_apply_right]
  have hne : ∀ i, i ≠ q.castSucc → i ≠ q.succ → interchange σ q.castSucc q.succ i = σ i := by
    intro i h1 h2; rw [hsw, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hqs : σ q.succ = φ q.succ := by
    apply ha
    intro u hu
    have := hU u hu
    constructor <;> intro e <;> simp only [Fin.ext_iff, Fin.lt_def, Fin.val_succ, Fin.coe_castSucc] at e this <;> omega
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have h1 := hi q (Finset.mem_insert_self _ _)
    rw [hne i h1.1 h1.2]
    exact ha i (fun u hu => hi u (Finset.mem_insert_of_mem hu))
  · intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · rw [hq1, hqs]
    · have := hU u hu
      rw [hne _ (by intro e; simp only [Fin.ext_iff, Fin.val_succ, Fin.coe_castSucc] at e; simp only [Fin.lt_def] at this; omega)
        (by intro e; simp only [Fin.ext_iff, Fin.val_succ, Fin.coe_castSucc] at e; simp only [Fin.lt_def] at this; omega)]
      exact hb u hu
  · intro i
    by_cases h1 : i = q.castSucc
    · right; right; exact ⟨q, Finset.mem_insert_self _ _, h1⟩
    by_cases h2 : i = q.succ
    · subst h2
      rw [hq2]
      right; left
      rcases hc q.castSucc with h3 | ⟨u, hu, h3, h4⟩ | ⟨u, hu, h3⟩
      · exact ⟨q, Finset.mem_insert_self _ _, Fin.castSucc_lt_succ, h3⟩
      · exact ⟨u, Finset.mem_insert_of_mem hu, lt_trans h3 Fin.castSucc_lt_succ, h4⟩
      · have := hU u hu
        exfalso
        simp only [Fin.ext_iff, Fin.val_succ, Fin.coe_castSucc] at h3
        simp only [Fin.lt_def] at this
        omega
    · rw [hne i h1 h2]
      rcases hc i with h3 | ⟨u, hu, h3, h4⟩ | ⟨u, hu, h3⟩
      · left; exact h3
      · right; left; exact ⟨u, Finset.mem_insert_of_mem hu, h3, h4⟩
      · right; right; exact ⟨u, Finset.mem_insert_of_mem hu, h3⟩

lemma gg_inv_list {n : ℕ} (φ : Equiv.Perm (Fin (n + 1))) :
    ∀ (l : List (Fin n)), l.Pairwise (· < ·) → ∀ (σ : Equiv.Perm (Fin (n + 1))) (U : Finset (Fin n)),
      (∀ u ∈ U, ∀ q ∈ l, u < q) → GGInv φ σ U →
      GGInv φ (l.foldl (fun ψ q => interchange ψ q.castSucc q.succ) σ) (U ∪ l.toFinset) := by
  intro l
  induction l with
  | nil => intro _ σ U _ h; simpa using h
  | cons a t ih =>
    intro hp σ U hU h
    rw [List.pairwise_cons] at hp
    have h1 := gg_inv_step φ σ U a (fun u hu => hU u hu a (by simp)) h
    have h2 := ih hp.2 _ (insert a U) (by
      intro u hu q hq
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hp.1 q hq
      · exact lt_trans (hU u hu a (by simp)) (hp.1 q hq)) h1
    simp only [List.foldl_cons]
    have e : insert a U ∪ t.toFinset = U ∪ (a :: t).toFinset := by
      ext x; simp
    rw [e] at h2
    exact h2

lemma gg_psiPrime_inv {n : ℕ} (φ : Equiv.Perm (Fin (n + 1))) (T : Finset (Fin n)) :
    GGInv φ (psiPrime φ T) T := by
  classical
  have hbase : GGInv φ φ ∅ := ⟨fun _ _ => rfl, by simp, fun i => Or.inl rfl⟩
  have := gg_inv_list φ (((List.finRange n).filter (fun q => q ∈ T))) (by
    exact (List.pairwise_lt_finRange n).filter _) φ ∅ (by simp) hbase
  have e : (∅ ∪ ((List.finRange n).filter (fun q => q ∈ T)).toFinset) = T := by
    ext x; simp
  rw [e] at this
  exact this

theorem gg_cases {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, g x = 0) (hf : MeasureTheory.LocallyIntegrable f)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ))
    (T : Finset (Fin n)) :
    (∃ j : Fin (n + 1), m f g A B (psiPrime φ T) = GilmoreGomoryTSP.MinCost.c f g A B j (φ j)) ∨
      ∃ q ∈ T, m f g A B (psiPrime φ T) = arcCost f g A B φ q := by
  obtain ⟨ha, hb, hc⟩ := gg_psiPrime_inv φ T
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin (n + 1)))
    (fun i => GilmoreGomoryTSP.MinCost.c f g A B i (psiPrime φ T i))
  have hm : m f g A B (psiPrime φ T) = GilmoreGomoryTSP.MinCost.c f g A B i (psiPrime φ T i) := hi
  have hle : ∀ k, GilmoreGomoryTSP.MinCost.c f g A B k (psiPrime φ T k) ≤ m f g A B (psiPrime φ T) :=
    fun k => Finset.le_sup' (fun i => GilmoreGomoryTSP.MinCost.c f g A B i (psiPrime φ T i))
      (Finset.mem_univ k)
  rcases hc i with h3 | ⟨u, hu, h3, h4⟩ | ⟨u, hu, h3⟩
  · left; exact ⟨i, by rw [hm, h3]⟩
  · right
    refine ⟨u, hu, le_antisymm ?_ ?_⟩
    · rw [hm, h4]
      have hBi : B u.castSucc ≤ B i := hB h3.le
      have hAi : A (φ u.castSucc) ≤ A (φ u.succ) := hφ (Fin.castSucc_lt_succ).le
      have := gg_c_anti f g A B hf0 hg0 hf hBi hAi
      exact this
    · have := hle u.castSucc
      rw [hb u hu] at this
      exact this
  · right
    refine ⟨u, hu, ?_⟩
    rw [hm, h3, hb u hu]
    rfl

end GilmoreGomoryTSP.Bottleneck

open GilmoreGomoryTSP.Bottleneck


theorem solution {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, g x = 0) (hf : MeasureTheory.LocallyIntegrable f)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ))
    (T : Finset (Fin n)) (hT : IsMinSpanningTree f g A B φ T) :
    (∃ j : Fin (n + 1), m f g A B (psiPrime φ T) = GilmoreGomoryTSP.MinCost.c f g A B j (φ j)) ∨
      ∃ q ∈ T, m f g A B (psiPrime φ T) = arcCost f g A B φ q := by
  exact gg_cases f g A B hB hf0 hg0 hf φ hφ T
