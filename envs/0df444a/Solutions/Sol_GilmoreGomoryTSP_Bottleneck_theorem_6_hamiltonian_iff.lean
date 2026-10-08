-- Prove2me | solution 1 for GilmoreGomoryTSP.Bottleneck.theorem_6_hamiltonian_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:25:35.518986+00:00
-- url     : https://prove2.me/submissions/af824829-ed8d-40b4-8cdc-06966667b065

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



lemma gg_graphOf_adj {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (x y : Fin (n + 1)) :
    (graphOf σ).Adj x y ↔ x ≠ y ∧ (σ x = y ∨ σ y = x) := by
  unfold graphOf; rw [SimpleGraph.fromRel_adj]

lemma gg_adjArcs_adj {n : ℕ} (T : Finset (Fin n)) (x y : Fin (n + 1)) :
    (adjArcs T).Adj x y ↔ ∃ q ∈ T, (x = q.castSucc ∧ y = q.succ) ∨ (y = q.castSucc ∧ x = q.succ) := by
  unfold adjArcs; rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, ⟨q, hq, h1, h2⟩ | ⟨q, hq, h1, h2⟩⟩
    · exact ⟨q, hq, Or.inl ⟨h1, h2⟩⟩
    · exact ⟨q, hq, Or.inr ⟨h1, h2⟩⟩
  · rintro ⟨q, hq, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · refine ⟨?_, Or.inl ⟨q, hq, h1, h2⟩⟩
      rw [h1, h2]; exact (Fin.castSucc_lt_succ).ne
    · refine ⟨?_, Or.inr ⟨q, hq, h1, h2⟩⟩
      rw [h1, h2]; exact (Fin.castSucc_lt_succ).ne'

lemma gg_arc_adj {n : ℕ} {T : Finset (Fin n)} {q : Fin n} (hq : q ∈ T) :
    (adjArcs T).Adj q.castSucc q.succ :=
  (gg_adjArcs_adj T _ _).mpr ⟨q, hq, Or.inl ⟨rfl, rfl⟩⟩

lemma gg_closure {V : Type*} (H : SimpleGraph V) (P : V → Prop)
    (hP : ∀ x y, H.Adj x y → P x → P y) {x y : V} (h : H.Reachable x y) (hx : P x) : P y := by
  obtain ⟨w⟩ := h
  revert hx
  induction w with
  | nil => intro hx; exact hx
  | cons hadj p ih => intro hx; exact ih (hP _ _ hadj hx)

lemma gg_reach_mono {V : Type*} (G1 G2 : SimpleGraph V) (h : ∀ x y, G1.Adj x y → G2.Reachable x y)
    {x y : V} (hr : G1.Reachable x y) : G2.Reachable x y :=
  gg_closure G1 (fun z => G2.Reachable x z) (fun z w hzw hz => hz.trans (h z w hzw)) hr
    (SimpleGraph.Reachable.refl x)

lemma gg_conn_of {V : Type*} (G : SimpleGraph V) (a : V) (h : ∀ x, G.Reachable x a) :
    G.Connected :=
  haveI : Nonempty V := ⟨a⟩
  ⟨fun x y => (h x).trans (h y).symm⟩

/-- Removing an arc whose endpoints stay reachable keeps connectivity. -/
lemma gg_conn_remove {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (R : Finset (Fin n)) (q : Fin n)
    (hc : (graphOf σ ⊔ adjArcs (insert q R)).Connected)
    (hr : (graphOf σ ⊔ adjArcs R).Reachable q.castSucc q.succ) :
    (graphOf σ ⊔ adjArcs R).Connected := by
  apply gg_conn_of _ q.castSucc
  intro x
  have h1 := hc.preconnected q.castSucc x
  have := gg_closure (graphOf σ ⊔ adjArcs (insert q R))
    (fun z => (graphOf σ ⊔ adjArcs R).Reachable z q.castSucc) ?_ h1
    (SimpleGraph.Reachable.refl _)
  · exact this
  · intro z w hzw hz
    rw [SimpleGraph.sup_adj] at hzw
    rcases hzw with h | h
    · exact (SimpleGraph.Adj.reachable (show (graphOf σ ⊔ adjArcs R).Adj w z from
        Or.inl h.symm)).trans hz
    · obtain ⟨p, hp, hh⟩ := (gg_adjArcs_adj _ _ _).mp h
      rcases Finset.mem_insert.mp hp with rfl | hp
      · rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hr.symm
        · exact SimpleGraph.Reachable.refl _
      · refine (SimpleGraph.Adj.reachable (show (graphOf σ ⊔ adjArcs R).Adj w z from
          Or.inr ((gg_adjArcs_adj _ _ _).mpr ⟨p, hp, ?_⟩))).trans hz
        tauto

lemma gg_exists_min {n : ℕ} (φ : Equiv.Perm (Fin (n + 1))) :
    ∀ N : ℕ, ∀ S : Finset (Fin n), S.card = N → Connects φ S →
      ∃ S' ⊆ S, IsAdjSpanningTree φ S' := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro S hS hc
    by_cases hex : ∃ S' ⊂ S, Connects φ S'
    · obtain ⟨S', hS', hc'⟩ := hex
      obtain ⟨S'', h1, h2⟩ := ih S'.card (hS ▸ Finset.card_lt_card hS') S' rfl hc'
      exact ⟨S'', h1.trans hS'.subset, h2⟩
    · push_neg at hex
      exact ⟨S, subset_rfl, hc, hex⟩

lemma gg_minimal_no_reach {n : ℕ} (φ : Equiv.Perm (Fin (n + 1))) (T : Finset (Fin n))
    (hT : IsAdjSpanningTree φ T) (q : Fin n) (hq : q ∈ T) :
    ¬ (graphOf φ ⊔ adjArcs (T.erase q)).Reachable q.castSucc q.succ := by
  intro hr
  apply hT.2 (T.erase q) (Finset.erase_ssubset hq)
  apply gg_conn_remove φ (T.erase q) q _ hr
  rw [Finset.insert_erase hq]
  exact hT.1

lemma gg_interval {n : ℕ} (G : SimpleGraph (Fin (n + 1))) (S : Finset (Fin n))
    (hG : ∀ q ∈ S, G.Adj q.castSucc q.succ) :
    ∀ d : ℕ, ∀ a b : Fin (n + 1), (b : ℕ) = a + d →
      (∀ q : Fin n, a ≤ q.castSucc → q.succ ≤ b → q ∈ S) → G.Reachable a b := by
  intro d
  induction d with
  | zero =>
    intro a b h _
    have : a = b := Fin.ext (by omega)
    rw [this]
  | succ d ih =>
    intro a b h hS
    have hb : (b : ℕ) - 1 < n := by have := b.isLt; omega
    set q : Fin n := ⟨(b : ℕ) - 1, hb⟩ with hqdef
    have hqv : (q : ℕ) = (b : ℕ) - 1 := rfl
    have hq1 : (q.castSucc : ℕ) = b - 1 := rfl
    have hq2 : q.succ = b := Fin.ext (by simp [hqdef]; omega)
    have h1 : G.Reachable a q.castSucc := by
      apply ih a q.castSucc (by rw [hq1]; omega)
      intro p hp1 hp2
      apply hS p hp1
      rw [Fin.le_def] at hp2 ⊢
      simp only [Fin.val_succ, Fin.val_castSucc] at hp2 ⊢
      rw [hqv] at hp2
      omega
    have hqS : q ∈ S := by
      apply hS q
      · rw [Fin.le_def]; simp only [Fin.val_castSucc, hqv]; omega
      · rw [hq2]
    have := hG q hqS
    rw [hq2] at this
    exact h1.trans this.reachable


lemma gg_phi_reach {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (X : SimpleGraph (Fin (n + 1)))
    (k : Fin (n + 1)) : (graphOf σ ⊔ X).Reachable (σ k) k := by
  by_cases h : σ k = k
  · rw [h]
  · apply SimpleGraph.Adj.reachable
    left
    rw [gg_graphOf_adj]
    exact ⟨h, Or.inr rfl⟩

lemma gg_claimA {n : ℕ} (φ ψ : Equiv.Perm (Fin (n + 1)))
    (hψ : GilmoreGomoryTSP.MinCost.IsTour ψ) : Connects φ (starArcs φ ψ) := by
  classical
  unfold Connects
  set G := graphOf φ ⊔ adjArcs (starArcs φ ψ) with hG
  have hadj : ∀ q ∈ starArcs φ ψ, G.Adj q.castSucc q.succ := fun q hq => Or.inr (gg_arc_adj hq)
  have key : ∀ i, G.Reachable (ψ i) i := by
    intro i
    set k := φ.symm (ψ i) with hk
    have hψk : ψ i = φ k := by simp [hk]
    have h1 : G.Reachable (ψ i) k := by rw [hψk]; exact gg_phi_reach φ _ k
    have h2 : G.Reachable i k := by
      rcases le_total i k with hik | hki
      · apply gg_interval G (starArcs φ ψ) hadj ((k : ℕ) - i) i k
          (by have := Fin.le_def.mp hik; omega)
        intro q hq1 hq2
        unfold starArcs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        left
        refine ⟨i, ?_, ?_⟩
        · have := Fin.le_def.mp hq1; simpa using this
        · have := Fin.le_def.mp hq2; simp only [Fin.val_succ] at this; omega
      · apply SimpleGraph.Reachable.symm
        apply gg_interval G (starArcs φ ψ) hadj ((i : ℕ) - k) k i
          (by have := Fin.le_def.mp hki; omega)
        intro q hq1 hq2
        unfold starArcs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        right
        refine ⟨i, ?_, ?_⟩
        · have := Fin.le_def.mp hq1; simpa using this
        · have := Fin.le_def.mp hq2; simp only [Fin.val_succ] at this; omega
    exact h1.trans h2.symm
  set s : Finset (Fin (n + 1)) := Finset.univ.filter (fun x => G.Reachable x 0) with hs
  have hsub : s.map ψ.toEmbedding ⊆ s := by
    intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact (key x).trans hx
  have heq : s.map ψ.toEmbedding = s :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_map])
  by_cases hfull : s = Finset.univ
  · apply gg_conn_of G 0
    intro x
    have : x ∈ s := by rw [hfull]; exact Finset.mem_univ x
    simpa [hs] using this
  · exfalso
    refine hψ s ⟨0, ?_⟩ hfull heq
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact SimpleGraph.Reachable.refl _

lemma gg_exchange {n : ℕ} (φ : Equiv.Perm (Fin (n + 1))) (R : Finset (Fin n)) (q : Fin n)
    (T' : Finset (Fin n))
    (hc : (graphOf φ ⊔ adjArcs (insert q R)).Connected)
    (hn : ¬ (graphOf φ ⊔ adjArcs R).Reachable q.castSucc q.succ)
    (hT' : (graphOf φ ⊔ adjArcs T').Connected) :
    ∃ e ∈ T', e ∉ R ∧ (graphOf φ ⊔ adjArcs (insert e R)).Connected := by
  set G0 := graphOf φ ⊔ adjArcs R with hG0
  have hle0 : graphOf φ ≤ G0 := le_sup_left
  have hcross : ∃ e ∈ T', ¬ (G0.Reachable e.castSucc q.castSucc ↔ G0.Reachable e.succ q.castSucc) := by
    by_contra hno
    push_neg at hno
    apply hn
    have := gg_closure (graphOf φ ⊔ adjArcs T') (fun z => G0.Reachable z q.castSucc) ?_
      (hT'.preconnected q.castSucc q.succ) (SimpleGraph.Reachable.refl _)
    · exact this.symm
    · intro z w hzw hz
      rw [SimpleGraph.sup_adj] at hzw
      rcases hzw with h | h
      · exact (SimpleGraph.Adj.reachable (show G0.Adj w z from hle0 h.symm)).trans hz
      · obtain ⟨p, hp, hh⟩ := (gg_adjArcs_adj _ _ _).mp h
        have := hno p hp
        rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact this.mp hz
        · exact this.mpr hz
  obtain ⟨e, he, hne⟩ := hcross
  have hnotR : e ∉ R := by
    intro hR
    apply hne
    have hadj : G0.Adj e.castSucc e.succ := Or.inr (gg_arc_adj hR)
    exact ⟨fun h => hadj.reachable.symm.trans h, fun h => hadj.reachable.trans h⟩
  have hmono : ∀ x y, G0.Adj x y → (graphOf φ ⊔ adjArcs (insert e R)).Adj x y := by
    intro x y h
    rcases h with h | h
    · exact Or.inl h
    · obtain ⟨p, hp, hh⟩ := (gg_adjArcs_adj _ _ _).mp h
      exact Or.inr ((gg_adjArcs_adj _ _ _).mpr ⟨p, Finset.mem_insert_of_mem hp, hh⟩)
  have hAB : ∀ x, G0.Reachable x q.castSucc ∨ G0.Reachable x q.succ := by
    intro x
    have h1 := hc.preconnected q.castSucc x
    refine gg_closure (graphOf φ ⊔ adjArcs (insert q R))
      (fun z => G0.Reachable z q.castSucc ∨ G0.Reachable z q.succ) ?_ h1
      (Or.inl (SimpleGraph.Reachable.refl _))
    intro z w hzw hz
    have step : G0.Adj z w → G0.Reachable w q.castSucc ∨ G0.Reachable w q.succ := by
      intro hadj
      rcases hz with hz | hz
      · exact Or.inl (hadj.reachable.symm.trans hz)
      · exact Or.inr (hadj.reachable.symm.trans hz)
    rw [SimpleGraph.sup_adj] at hzw
    rcases hzw with h | h
    · exact step (hle0 h)
    · obtain ⟨p, hp, hh⟩ := (gg_adjArcs_adj _ _ _).mp h
      rcases Finset.mem_insert.mp hp with hpq | hp
      · subst hpq
        rcases hh with ⟨_, rfl⟩ | ⟨rfl, _⟩
        · exact Or.inr (SimpleGraph.Reachable.refl _)
        · exact Or.inl (SimpleGraph.Reachable.refl _)
      · exact step (Or.inr ((gg_adjArcs_adj _ _ _).mpr ⟨p, hp, hh⟩))
  have harc : (graphOf φ ⊔ adjArcs (insert e R)).Adj e.castSucc e.succ :=
    Or.inr (gg_arc_adj (Finset.mem_insert_self e R))
  obtain ⟨u, w, hu, hw, huw⟩ : ∃ u w, G0.Reachable u q.castSucc ∧ ¬ G0.Reachable w q.castSucc ∧
      (graphOf φ ⊔ adjArcs (insert e R)).Adj u w := by
    by_cases hP : G0.Reachable e.castSucc q.castSucc
    · refine ⟨e.castSucc, e.succ, hP, fun h => hne ⟨fun _ => h, fun _ => hP⟩, harc⟩
    · have hP2 : G0.Reachable e.succ q.castSucc := by
        by_contra hh
        exact hne ⟨fun h => absurd h hP, fun h => absurd h hh⟩
      exact ⟨e.succ, e.castSucc, hP2, hP, harc.symm⟩
  have hwb : G0.Reachable w q.succ := (hAB w).resolve_left hw
  refine ⟨e, he, hnotR, gg_conn_of _ q.castSucc ?_⟩
  intro x
  have hm : ∀ x y, G0.Reachable x y → (graphOf φ ⊔ adjArcs (insert e R)).Reachable x y :=
    fun x y h => gg_reach_mono G0 _ (fun x y h => (hmono x y h).reachable) h
  rcases hAB x with hx | hx
  · exact hm _ _ hx
  · exact (hm _ _ hx).trans ((hm _ _ hwb).symm.trans (huw.symm.reachable.trans (hm _ _ hu)))

lemma gg_bottleneck {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ)
    (φ : Equiv.Perm (Fin (n + 1))) (T T' : Finset (Fin n)) (b : ℝ)
    (hT : IsMinSpanningTree f g A B φ T) (hT' : Connects φ T')
    (hw : ∀ e ∈ T', arcCost f g A B φ e ≤ b) (hnn : ∀ q, 0 ≤ arcCost f g A B φ q) :
    ∀ q0 ∈ T, arcCost f g A B φ q0 ≤ b := by
  intro q0 hq0
  by_contra hlt
  push_neg at hlt
  have hn := gg_minimal_no_reach φ T hT.1 q0 hq0
  have hc : (graphOf φ ⊔ adjArcs (insert q0 (T.erase q0))).Connected := by
    rw [Finset.insert_erase hq0]; exact hT.1.1
  obtain ⟨e, heT', heR, hconn⟩ := gg_exchange φ (T.erase q0) q0 T' hc hn hT'
  obtain ⟨T3, hT3sub, hT3⟩ := gg_exists_min φ _ (insert e (T.erase q0)) rfl hconn
  have h1 := hT.2 T3 hT3
  have h2 : ∑ q ∈ T3, arcCost f g A B φ q ≤ ∑ q ∈ insert e (T.erase q0), arcCost f g A B φ q :=
    Finset.sum_le_sum_of_subset_of_nonneg hT3sub (fun i _ _ => hnn i)
  rw [Finset.sum_insert heR] at h2
  have h3 := (Finset.add_sum_erase T (fun q => arcCost f g A B φ q) hq0).symm
  have := hw e heT'
  linarith

lemma gg_cycle {V : Type*} [Fintype V] [DecidableEq V] (σ : Equiv.Perm V) (A : V → Prop) (a b : V)
    (ha : A a) (hσa : ¬ A (σ a))
    (hi : ∀ i, i ≠ a → i ≠ b → (A i ↔ A (σ i))) (hσb : A (σ b)) :
    ∃ k : ℕ, (σ ^ k) a = b := by
  classical
  have hex : ∃ k : ℕ, 0 < k ∧ A ((σ ^ k) a) :=
    ⟨orderOf σ, orderOf_pos σ, by rw [pow_orderOf_eq_one]; simpa using ha⟩
  obtain ⟨hk0, hkA⟩ := Nat.find_spec hex
  have hmin : ∀ j, j < Nat.find hex → ¬ (0 < j ∧ A ((σ ^ j) a)) :=
    fun j hj => Nat.find_min hex hj
  generalize Nat.find hex = k at hk0 hkA hmin
  obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hk' : (σ ^ k) a = σ ((σ ^ m) a) := by rw [hm, pow_succ']; rfl
  by_cases hm0 : m = 0
  · exfalso
    rw [hm, hm0] at hkA
    simp at hkA
    exact hσa hkA
  · have hmk : m < k := by omega
    have hnA : ¬ A ((σ ^ m) a) := fun h => hmin m hmk ⟨by omega, h⟩
    have hneqa : (σ ^ m) a ≠ a := fun h => hnA (by rw [h]; exact ha)
    by_cases hyb : (σ ^ m) a = b
    · exact ⟨m, hyb⟩
    · exfalso
      exact hnA ((hi _ hneqa hyb).mpr (by rw [← hk']; exact hkA))

lemma gg_pow_reach {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (X : SimpleGraph (Fin (n + 1)))
    (a : Fin (n + 1)) : ∀ k : ℕ, (graphOf σ ⊔ X).Reachable a ((σ ^ k) a) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    exact ih.trans (gg_phi_reach σ X _).symm

lemma gg_swap_facts {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (q : Fin n) :
    interchange σ q.castSucc q.succ q.castSucc = σ q.succ ∧
    interchange σ q.castSucc q.succ q.succ = σ q.castSucc ∧
    ∀ i, i ≠ q.castSucc → i ≠ q.succ → interchange σ q.castSucc q.succ i = σ i := by
  refine ⟨?_, ?_, ?_⟩
  · show σ (Equiv.swap q.castSucc q.succ q.castSucc) = _
    rw [Equiv.swap_apply_left]
  · show σ (Equiv.swap q.castSucc q.succ q.succ) = _
    rw [Equiv.swap_apply_right]
  · intro i h1 h2
    show σ (Equiv.swap q.castSucc q.succ i) = _
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

lemma gg_swap_reach {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (S : Finset (Fin n)) (q : Fin n)
    (hq : q ∈ S) (x : Fin (n + 1)) :
    (graphOf σ ⊔ adjArcs S).Reachable x (interchange σ q.castSucc q.succ x) := by
  obtain ⟨e1, e2, e3⟩ := gg_swap_facts σ q
  have harc : (graphOf σ ⊔ adjArcs S).Reachable q.castSucc q.succ :=
    (SimpleGraph.Adj.reachable (Or.inr (gg_arc_adj hq)))
  by_cases h1 : x = q.castSucc
  · subst h1
    rw [e1]
    exact harc.trans (gg_phi_reach σ _ _).symm
  by_cases h2 : x = q.succ
  · subst h2
    rw [e2]
    exact harc.symm.trans (gg_phi_reach σ _ _).symm
  · rw [e3 x h1 h2]
    exact (gg_phi_reach σ _ _).symm

lemma gg_reach_swap {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (S1 S2 : Finset (Fin n)) (q : Fin n)
    (hq : q ∈ S2) (hS : S1 ⊆ S2) {x y : Fin (n + 1)}
    (h : (graphOf (interchange σ q.castSucc q.succ) ⊔ adjArcs S1).Reachable x y) :
    (graphOf σ ⊔ adjArcs S2).Reachable x y := by
  refine gg_reach_mono _ _ ?_ h
  intro u v huv
  rw [SimpleGraph.sup_adj] at huv
  rcases huv with h | h
  · rw [gg_graphOf_adj] at h
    rcases h.2 with h | h
    · rw [← h]; exact gg_swap_reach σ S2 q hq u
    · rw [← h]; exact (gg_swap_reach σ S2 q hq v).symm
  · obtain ⟨p, hp, hh⟩ := (gg_adjArcs_adj _ _ _).mp h
    exact SimpleGraph.Adj.reachable (Or.inr ((gg_adjArcs_adj _ _ _).mpr ⟨p, hS hp, hh⟩))

lemma gg_merge {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (R : Finset (Fin n)) (q : Fin n)
    (hc : (graphOf σ ⊔ adjArcs (insert q R)).Connected)
    (hn : ¬ (graphOf σ ⊔ adjArcs R).Reachable q.castSucc q.succ) :
    (graphOf (interchange σ q.castSucc q.succ) ⊔ adjArcs R).Connected := by
  classical
  obtain ⟨e1, e2, e3⟩ := gg_swap_facts σ q
  set σ' := interchange σ q.castSucc q.succ with hσ'
  set G' := graphOf σ' ⊔ adjArcs R with hG'
  have hAB : ∀ x, G'.Reachable x q.castSucc ∨ G'.Reachable x q.succ := by
    intro x
    have h1 := hc.preconnected q.castSucc x
    refine gg_closure (graphOf σ ⊔ adjArcs (insert q R))
      (fun z => G'.Reachable z q.castSucc ∨ G'.Reachable z q.succ) ?_ h1
      (Or.inl (SimpleGraph.Reachable.refl _))
    intro z w hzw hz
    have triv : (w = q.castSucc ∨ w = q.succ) → (G'.Reachable w q.castSucc ∨ G'.Reachable w q.succ) := by
      rintro (rfl | rfl)
      · exact Or.inl (SimpleGraph.Reachable.refl _)
      · exact Or.inr (SimpleGraph.Reachable.refl _)
    have step : G'.Reachable w z → (G'.Reachable w q.castSucc ∨ G'.Reachable w q.succ) := by
      intro hwz
      rcases hz with hz | hz
      · exact Or.inl (hwz.trans hz)
      · exact Or.inr (hwz.trans hz)
    rw [SimpleGraph.sup_adj] at hzw
    rcases hzw with h | h
    · rw [gg_graphOf_adj] at h
      rcases h.2 with h | h
      · -- σ z = w
        by_cases hza : z = q.castSucc
        · subst hza
          rw [← h, ← e2]
          exact Or.inr (gg_phi_reach σ' _ _)
        by_cases hzb : z = q.succ
        · subst hzb
          rw [← h, ← e1]
          exact Or.inl (gg_phi_reach σ' _ _)
        · rw [← e3 z hza hzb] at h
          subst h
          exact step (gg_phi_reach σ' _ _)
      · -- σ w = z
        by_cases hwa : w = q.castSucc
        · exact triv (Or.inl hwa)
        by_cases hwb : w = q.succ
        · exact triv (Or.inr hwb)
        · rw [← e3 w hwa hwb] at h
          subst h
          exact step (gg_phi_reach σ' _ _).symm
    · obtain ⟨p, hp, hh⟩ := (gg_adjArcs_adj _ _ _).mp h
      rcases Finset.mem_insert.mp hp with hpq | hp
      · subst hpq
        apply triv
        rcases hh with ⟨_, rfl⟩ | ⟨rfl, _⟩
        · exact Or.inr rfl
        · exact Or.inl rfl
      · exact step (SimpleGraph.Adj.reachable (Or.inr ((gg_adjArcs_adj _ _ _).mpr ⟨p, hp, by tauto⟩)))
  have hab : G'.Reachable q.castSucc q.succ := by
    by_contra hnab
    have hb : ¬ G'.Reachable q.succ q.castSucc := fun h => hnab h.symm
    have hσa : ¬ G'.Reachable (σ q.castSucc) q.castSucc := by
      intro h
      apply hnab
      rw [← e2] at h
      exact ((gg_phi_reach σ' _ _).symm.trans h).symm
    have hσb : G'.Reachable (σ q.succ) q.castSucc := by
      rw [← e1]; exact gg_phi_reach σ' _ _
    have hi' : ∀ i, i ≠ q.castSucc → i ≠ q.succ →
        (G'.Reachable i q.castSucc ↔ G'.Reachable (σ i) q.castSucc) := by
      intro i hi1 hi2
      have h3 := e3 i hi1 hi2
      have h4 : G'.Reachable (σ i) i := by rw [← h3]; exact gg_phi_reach σ' _ _
      constructor
      · intro h; exact h4.trans h
      · intro h; exact h4.symm.trans h
    obtain ⟨k, hk⟩ := gg_cycle σ (fun x => G'.Reachable x q.castSucc) q.castSucc q.succ
      (SimpleGraph.Reachable.refl _) hσa hi' hσb
    apply hn
    have := gg_pow_reach σ (adjArcs R) q.castSucc k
    rwa [hk] at this
  apply gg_conn_of G' q.castSucc
  intro x
  rcases hAB x with h | h
  · exact h
  · exact h.trans hab.symm

lemma gg_tour_of_conn {n : ℕ} (ψ : Equiv.Perm (Fin (n + 1))) (hc : (graphOf ψ).Connected) :
    GilmoreGomoryTSP.MinCost.IsTour ψ := by
  intro s hne hproper hmap
  obtain ⟨x0, hx0⟩ := hne
  apply hproper
  ext y
  simp only [Finset.mem_univ, iff_true]
  have hcl : ∀ u v, (graphOf ψ).Adj u v → u ∈ s → v ∈ s := by
    intro u v h hu
    rw [gg_graphOf_adj] at h
    rcases h.2 with h | h
    · have h2 := Finset.mem_map_of_mem ψ.toEmbedding hu
      rw [hmap] at h2
      rw [← h]; exact h2
    · rw [← hmap] at hu
      obtain ⟨y', hy', hy'u⟩ := Finset.mem_map.mp hu
      have : y' = v := ψ.injective (by simpa using hy'u.trans h.symm)
      rw [← this]; exact hy'
  exact gg_closure (graphOf ψ) (fun z => z ∈ s) hcl (hc.preconnected x0 y) hx0

lemma gg_list_conn {n : ℕ} : ∀ l : List (Fin n), l.Nodup → ∀ (σ : Equiv.Perm (Fin (n + 1)))
    (W : Finset (Fin n)), l.toFinset = W → (graphOf σ ⊔ adjArcs W).Connected →
    (∀ q ∈ W, ¬ (graphOf σ ⊔ adjArcs (W.erase q)).Reachable q.castSucc q.succ) →
    (graphOf (l.foldl (fun ψ q => interchange ψ q.castSucc q.succ) σ)).Connected := by
  intro l
  induction l with
  | nil =>
    intro _ σ W hW hc _
    have : W = ∅ := by rw [← hW]; rfl
    subst this
    have e : graphOf σ ⊔ adjArcs (∅ : Finset (Fin n)) = graphOf σ := by
      ext x y
      simp [SimpleGraph.sup_adj, gg_adjArcs_adj]
    rw [e] at hc
    exact hc
  | cons a t ih =>
    intro hnd σ W hW hc hI2
    rw [List.nodup_cons] at hnd
    have haW : a ∈ W := by rw [← hW]; simp
    have hWe : W.erase a = t.toFinset := by
      rw [← hW, List.toFinset_cons, Finset.erase_insert]
      simpa using hnd.1
    have hc' : (graphOf (interchange σ a.castSucc a.succ) ⊔ adjArcs (W.erase a)).Connected := by
      apply gg_merge σ (W.erase a) a
      · rw [Finset.insert_erase haW]; exact hc
      · exact hI2 a haW
    have hI2' : ∀ q ∈ W.erase a, ¬ (graphOf (interchange σ a.castSucc a.succ) ⊔
        adjArcs ((W.erase a).erase q)).Reachable q.castSucc q.succ := by
      intro q hq hr
      have hqW : q ∈ W := Finset.mem_of_mem_erase hq
      have hqa : q ≠ a := Finset.ne_of_mem_erase hq
      apply hI2 q hqW
      refine gg_reach_swap σ ((W.erase a).erase q) (W.erase q) a ?_ ?_ hr
      · exact Finset.mem_erase.mpr ⟨hqa.symm, haW⟩
      · intro p hp
        simp only [Finset.mem_erase] at hp ⊢
        exact ⟨hp.1, hp.2.2⟩
    simp only [List.foldl_cons]
    exact ih hnd.2 _ (W.erase a) hWe.symm hc' hI2'

lemma gg_psiPrime_conn {n : ℕ} (φ : Equiv.Perm (Fin (n + 1))) (T : Finset (Fin n))
    (hT : IsAdjSpanningTree φ T) : (graphOf (psiPrime φ T)).Connected := by
  classical
  unfold psiPrime
  apply gg_list_conn _ _ φ T
  · ext x; simp
  · exact hT.1
  · exact fun q hq => gg_minimal_no_reach φ T hT q hq
  · exact (List.nodup_finRange n).filter _

theorem gg_goal {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, g x = 0) (hf : MeasureTheory.LocallyIntegrable f)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ))
    (T : Finset (Fin n)) (hT : IsMinSpanningTree f g A B φ T) :
    GilmoreGomoryTSP.MinCost.IsTour (psiPrime φ T) ∧
      ∀ ψ : Equiv.Perm (Fin (n + 1)), GilmoreGomoryTSP.MinCost.IsTour ψ →
        m f g A B (psiPrime φ T) ≤ m f g A B ψ := by
  refine ⟨gg_tour_of_conn _ (gg_psiPrime_conn φ T hT.1), ?_⟩
  intro ψ hψ
  have hnn : ∀ q, 0 ≤ arcCost f g A B φ q := fun q => gg_c_nonneg f g A B hf0 hg0 _ _
  have hall := gg_bottleneck f g A B φ T (starArcs φ ψ) (m f g A B ψ) hT (gg_claimA φ ψ hψ)
    (fun e he => gg_eq30 f g A B hB hf0 hg0 hf φ hφ ψ e he) hnn
  rcases gg_cases f g A B hB hf0 hg0 hf φ hφ T with ⟨j, hj⟩ | ⟨q, hq, hqe⟩
  · rw [hj]
    refine le_trans ?_ (gg_phi_min f g A B hB hf0 hg0 hf φ hφ ψ)
    exact Finset.le_sup' (fun i => GilmoreGomoryTSP.MinCost.c f g A B i (φ i)) (Finset.mem_univ j)
  · rw [hqe]; exact hall q hq

lemma gg_star22a {n : ℕ} (φ ψ : Equiv.Perm (Fin (n + 1))) (q : Fin n) (hq : q ∈ starArcs φ ψ) :
    ∃ i : Fin (n + 1), (i : ℕ) ≤ q ∧ (q : ℕ) < (φ.symm (ψ i) : ℕ) := by
  unfold starArcs at hq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
  rcases hq with ⟨i, hi⟩ | ⟨j, hj⟩
  · exact ⟨i, hi⟩
  · exact gg_exists_a (ψ.trans φ.symm) q ⟨j, hj⟩

theorem gg_thm6 {n : ℕ} (Γ : Fin (n + 1) → Finset (Fin (n + 1))) (hΓ : Monotone Γ)
    (φ : Equiv.Perm (Fin (n + 1)))
    (hφ : ∀ i, ∃ j : ℕ,
      Γ i = (Finset.univ.filter (fun k : Fin (n + 1) => (k : ℕ) < j)).map φ.toEmbedding) :
    (∃ ψ : Equiv.Perm (Fin (n + 1)), GilmoreGomoryTSP.MinCost.IsTour ψ ∧ ∀ i, ψ i ∈ Γ i) ↔
      (∀ q, φ q ∈ Γ q) ∧ (Gprime Γ φ).Connected := by
  classical
  have hdown : ∀ i k k', k' ≤ k → φ k ∈ Γ i → φ k' ∈ Γ i := by
    intro i k k' hkk h
    obtain ⟨j, hj⟩ := hφ i
    rw [hj, Finset.mem_map_equiv] at h ⊢
    simp only [Equiv.symm_apply_apply, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    have := Fin.le_def.mp hkk
    omega
  constructor
  · rintro ⟨ψ, hψ, hψΓ⟩
    have hψφ : ∀ i, ψ i = φ (φ.symm (ψ i)) := fun i => by simp
    have ha : ∀ q, φ q ∈ Γ q := by
      by_contra hne
      push_neg at hne
      obtain ⟨q, hq⟩ := hne
      have hsub : (Finset.Iic q).image (ψ.trans φ.symm) ⊆ Finset.Iio q := by
        intro x hx
        simp only [Finset.mem_image, Finset.mem_Iic, Finset.mem_Iio] at hx ⊢
        obtain ⟨y, hy, rfl⟩ := hx
        by_contra hge
        push_neg at hge
        apply hq
        apply hdown q (φ.symm (ψ y)) q hge
        rw [← hψφ]
        exact hΓ hy (hψΓ y)
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ (ψ.trans φ.symm).injective] at h1
      simp [Fin.card_Iic, Fin.card_Iio] at h1
    refine ⟨ha, ?_⟩
    have hconn := gg_claimA φ ψ hψ
    unfold Connects at hconn
    refine hconn.mono ?_
    intro x y hxy
    rw [SimpleGraph.sup_adj] at hxy
    unfold Gprime
    rw [SimpleGraph.fromRel_adj]
    rcases hxy with h | h
    · rw [gg_graphOf_adj] at h
      refine ⟨h.1, ?_⟩
      rcases h.2 with h2 | h2
      · exact Or.inl (Or.inl ⟨h2.symm, ha x⟩)
      · exact Or.inr (Or.inl ⟨h2.symm, ha y⟩)
    · obtain ⟨q, hq, hh⟩ := (gg_adjArcs_adj _ _ _).mp h
      have hkey : φ q.succ ∈ Γ q.castSucc := by
        obtain ⟨i, hi1, hi2⟩ := gg_star22a φ ψ q hq
        apply hdown q.castSucc (φ.symm (ψ i)) q.succ
        · rw [Fin.le_def]; simpa using hi2
        · rw [← hψφ]
          exact hΓ (by rw [Fin.le_def]; simpa using hi1) (hψΓ i)
      rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨by rw [h1, h2]; exact (Fin.castSucc_lt_succ).ne, Or.inl (Or.inr ⟨q, h1, h2, hkey⟩)⟩
      · refine ⟨by rw [h1, h2]; exact (Fin.castSucc_lt_succ).ne', Or.inr (Or.inr ⟨q, h1, h2, hkey⟩)⟩
  · rintro ⟨ha, hconn⟩
    set T0 : Finset (Fin n) := Finset.univ.filter (fun q => φ q.succ ∈ Γ q.castSucc) with hT0
    have hc0 : Connects φ T0 := by
      unfold Connects
      refine hconn.mono ?_
      intro x y hxy
      unfold Gprime at hxy
      rw [SimpleGraph.fromRel_adj] at hxy
      obtain ⟨hne, h | h⟩ := hxy
      · rcases h with ⟨h1, _⟩ | ⟨q, h1, h2, h3⟩
        · exact Or.inl ((gg_graphOf_adj _ _ _).mpr ⟨hne, Or.inl h1.symm⟩)
        · exact Or.inr ((gg_adjArcs_adj _ _ _).mpr ⟨q, by simp [hT0, h3], Or.inl ⟨h1, h2⟩⟩)
      · rcases h with ⟨h1, _⟩ | ⟨q, h1, h2, h3⟩
        · exact Or.inl ((gg_graphOf_adj _ _ _).mpr ⟨hne, Or.inr h1.symm⟩)
        · exact Or.inr ((gg_adjArcs_adj _ _ _).mpr ⟨q, by simp [hT0, h3], Or.inr ⟨h1, h2⟩⟩)
    obtain ⟨T, hTsub, hT⟩ := gg_exists_min φ _ T0 rfl hc0
    refine ⟨psiPrime φ T, gg_tour_of_conn _ (gg_psiPrime_conn φ T hT), ?_⟩
    intro i
    obtain ⟨_, hb, hc⟩ := gg_psiPrime_inv φ T
    rcases hc i with h | ⟨u, hu, hlt, hval⟩ | ⟨u, hu, rfl⟩
    · rw [h]; exact ha i
    · rw [hval]; exact hΓ hlt.le (ha _)
    · rw [hb u hu]
      have := hTsub hu
      simpa [hT0] using this

end GilmoreGomoryTSP.Bottleneck

open GilmoreGomoryTSP.Bottleneck


theorem solution {n : ℕ} (Γ : Fin (n + 1) → Finset (Fin (n + 1)))
    (hΓ : Monotone Γ) (hΓn : Γ (Fin.last n) = Finset.univ) (φ : Equiv.Perm (Fin (n + 1)))
    (hφ : ∀ i, ∃ j : ℕ,
      Γ i = (Finset.univ.filter (fun k : Fin (n + 1) => (k : ℕ) < j)).map φ.toEmbedding) :
    (∃ ψ : Equiv.Perm (Fin (n + 1)), GilmoreGomoryTSP.MinCost.IsTour ψ ∧ ∀ i, ψ i ∈ Γ i) ↔
      (∀ q, φ q ∈ Γ q) ∧ (Gprime Γ φ).Connected := by
  exact gg_thm6 Γ hΓ φ hφ
