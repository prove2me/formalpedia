-- Prove2me | solution 1 for IPProximity.Eisenbrand.steinitz
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:07:51.557741+00:00
-- url     : https://prove2.me/submissions/11875836-cf3e-4fd0-afb8-157794ee1c44

import Mathlib



namespace IPProximity.Eisenbrand

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def StGood {n : ℕ} (x : Fin n → E) (m : ℕ) (S : Finset (Fin n)) (c : ℝ) (l : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ l i ∧ l i ≤ 1) ∧ (∀ i, i ∉ S → l i = 0) ∧ ∑ i, l i = c ∧ ∑ i, l i • x i = 0

/-- reduction of fractional count -/
theorem st_frac_core {n m : ℕ} (hdim : Module.finrank ℝ E = m) (x : Fin n → E)
    (S : Finset (Fin n)) (c : ℝ) :
    ∀ N : ℕ, ∀ l, StGood x m S c l →
      (Finset.univ.filter (fun i => 0 < l i ∧ l i < 1)).card = N →
      ∃ l', StGood x m S c l' ∧ (Finset.univ.filter (fun i => 0 < l' i ∧ l' i < 1)).card ≤ m + 1 := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro l hl hN
  by_cases hsmall : N ≤ m + 1
  · exact ⟨l, hl, hN ▸ hsmall⟩
  push_neg at hsmall
  set G := Finset.univ.filter (fun i => 0 < l i ∧ l i < 1) with hG
  let L : (G → ℝ) →ₗ[ℝ] (E × ℝ) :=
    { toFun := fun w => (∑ j, w j • x j, ∑ j, w j)
      map_add' := by
        intro a b; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro a b; simp [Finset.smul_sum, Finset.mul_sum, mul_smul] }
  have hker : LinearMap.ker L ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe, hdim]
    omega
  obtain ⟨w, hwk, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hLw : L w = 0 := LinearMap.mem_ker.mp hwk
  let v : Fin n → ℝ := fun i => if h : i ∈ G then w ⟨i, h⟩ else 0
  have hvG : ∀ i, i ∉ G → v i = 0 := by intro i hi; simp [v, hi]
  have hsumG : ∀ f : Fin n → E, ∑ i, v i • f i = ∑ j : G, w j • f j := by
    intro f
    rw [← Finset.sum_subset (Finset.subset_univ G) (fun i _ hi => by simp [hvG i hi])]
    rw [← Finset.sum_coe_sort G]
    apply Finset.sum_congr rfl; intro j _; simp [v]
  have hsumG' : ∑ i, v i = ∑ j : G, w j := by
    rw [← Finset.sum_subset (Finset.subset_univ G) (fun i _ hi => by simp [hvG i hi])]
    rw [← Finset.sum_coe_sort G]
    apply Finset.sum_congr rfl; intro j _; simp [v]
  have hvx : ∑ i, v i • x i = 0 := by
    rw [hsumG]; have := congrArg Prod.fst hLw; simpa [L] using this
  have hvs : ∑ i, v i = 0 := by
    rw [hsumG']; have := congrArg Prod.snd hLw; simpa [L] using this
  -- nonzero coordinates
  set G' := G.filter (fun i => v i ≠ 0) with hG'
  have hG'ne : G'.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    apply hw0; funext ⟨j, hj⟩
    by_contra hwj
    have : j ∈ G' := by
      rw [hG', Finset.mem_filter]; exact ⟨hj, by simpa [v, hj] using hwj⟩
    rw [hne] at this; simp at this
  let tt : Fin n → ℝ := fun i => if 0 < v i then (1 - l i) / v i else - l i / v i
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image G' tt hG'ne
  have hi0G : i0 ∈ G := (Finset.mem_filter.mp hi0).1
  have hi0v : v i0 ≠ 0 := (Finset.mem_filter.mp hi0).2
  have hlG : ∀ i ∈ G, 0 < l i ∧ l i < 1 := fun i hi => (Finset.mem_filter.mp hi).2
  set t := tt i0 with ht
  have ttpos : ∀ i ∈ G', 0 < tt i := by
    intro i hi
    have h1 := hlG i (Finset.mem_filter.mp hi).1
    have h2 := (Finset.mem_filter.mp hi).2
    simp only [tt]
    split_ifs with h
    · apply div_pos <;> linarith
    · have : v i < 0 := lt_of_le_of_ne (not_lt.mp h) h2
      apply div_pos_of_neg_of_neg <;> linarith
  have htpos : 0 < t := ttpos i0 hi0
  let l' : Fin n → ℝ := fun i => l i + t * v i
  have hl'box : ∀ i, 0 ≤ l' i ∧ l' i ≤ 1 := by
    intro i
    by_cases hi : i ∈ G'
    · have h1 := hlG i (Finset.mem_filter.mp hi).1
      have h2 := (Finset.mem_filter.mp hi).2
      have hle : t ≤ tt i := hmin i hi
      simp only [tt] at hle
      simp only [l']
      split_ifs at hle with h
      · rw [le_div_iff₀ h] at hle
        constructor <;> nlinarith
      · have hneg : v i < 0 := lt_of_le_of_ne (not_lt.mp h) h2
        rw [le_div_iff_of_neg hneg] at hle
        constructor <;> nlinarith
    · have : v i = 0 := by
        by_cases hiG : i ∈ G
        · by_contra h; exact hi (Finset.mem_filter.mpr ⟨hiG, h⟩)
        · exact hvG i hiG
      simp [l', this, hl.1 i]
  have hl'good : StGood x m S c l' := by
    refine ⟨hl'box, ?_, ?_, ?_⟩
    · intro i hi
      have hli := hl.2.1 i hi
      have : i ∉ G := by intro h; have := (hlG i h).1; linarith
      simp [l', hli, hvG i this]
    · simp only [l', Finset.sum_add_distrib, ← Finset.mul_sum, hvs, hl.2.2.1]; ring
    · simp only [l', add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, hvx,
        hl.2.2.2]; simp
  -- fractional set shrinks
  have hsub : Finset.univ.filter (fun i => 0 < l' i ∧ l' i < 1) ⊆ G.erase i0 := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    rw [Finset.mem_erase]
    constructor
    · rintro rfl
      simp only [l', ht, tt] at hi'
      split_ifs at hi' with h
      · field_simp at hi'; linarith [hi'.2]
      · field_simp at hi'; linarith [hi'.1]
    · by_contra hiG
      have hv0 : v i = 0 := hvG i hiG
      have : l' i = l i := by simp [l', hv0]
      rw [this] at hi'
      exact hiG (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩)
  have hlt : (Finset.univ.filter (fun i => 0 < l' i ∧ l' i < 1)).card < N := by
    calc _ ≤ (G.erase i0).card := Finset.card_le_card hsub
      _ < G.card := Finset.card_erase_lt_of_mem hi0G
      _ = N := hN
  exact ih _ hlt l' hl'good rfl

theorem st_reduce_core {n m : ℕ} (hdim : Module.finrank ℝ E = m) (x : Fin n → E)
    (S : Finset (Fin n)) (hk : m < S.card) (l : Fin n → ℝ)
    (hl : StGood x m S ((S.card : ℝ) - m) l) :
    ∃ i0 ∈ S, ∃ μ, StGood x m (S.erase i0) (((S.erase i0).card : ℝ) - m) μ := by
  classical
  set k := S.card with hkdef
  have hk' : (m : ℝ) + 1 ≤ k := by exact_mod_cast hk
  set a : ℝ := ((k : ℝ) - 1 - m) / ((k : ℝ) - m) with ha
  have ha0 : 0 ≤ a := div_nonneg (by linarith) (by linarith)
  have ha1 : a ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hμ0 : StGood x m S ((k : ℝ) - 1 - m) (a • l) := by
    refine ⟨fun i => ?_, fun i hi => by simp [hl.2.1 i hi], ?_, ?_⟩
    · have := hl.1 i; simp only [Pi.smul_apply, smul_eq_mul]
      constructor <;> nlinarith
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hl.2.2.1, ha]
      have : (k:ℝ) - m ≠ 0 := by linarith
      field_simp
    · simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, hl.2.2.2, smul_zero]
  obtain ⟨μ, hμ, hcnt⟩ := st_frac_core hdim x S _ _ (a • l) hμ0 rfl
  have hex : ∃ i0 ∈ S, μ i0 = 0 := by
    by_contra hne
    push_neg at hne
    set G := Finset.univ.filter (fun i => 0 < μ i ∧ μ i < 1) with hG
    have hGS : G ⊆ S := by
      intro i hi
      by_contra hiS
      have := (Finset.mem_filter.mp hi).2.1
      rw [hμ.2.1 i hiS] at this; exact lt_irrefl _ this
    have hone : ∀ i ∈ S \ G, μ i = 1 := by
      intro i hi
      rw [Finset.mem_sdiff] at hi
      have h1 := hμ.1 i
      have h2 : 0 < μ i := lt_of_le_of_ne h1.1 (Ne.symm (hne i hi.1))
      by_contra h3
      exact hi.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2, lt_of_le_of_ne h1.2 h3⟩)
    have hsumS : ∑ i, μ i = ∑ i ∈ S, μ i :=
      (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hμ.2.1 i hi)).symm
    have hsplit := Finset.sum_sdiff hGS (f := μ)
    rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_sdiff_of_subset hGS] at hsplit
    have hc := hμ.2.2.1
    rw [hsumS, ← hsplit] at hc
    have hGc : (G.card : ℝ) ≤ m + 1 := by exact_mod_cast hcnt
    have hGk : G.card ≤ k := Finset.card_le_card hGS
    rw [Nat.cast_sub hGk] at hc
    rcases G.eq_empty_or_nonempty with he | hne'
    · rw [he] at hc; simp at hc; linarith
    · have hpos : 0 < ∑ i ∈ G, μ i :=
        Finset.sum_pos (fun i hi => (Finset.mem_filter.mp hi).2.1) hne'
      linarith
  obtain ⟨i0, hi0, hμi0⟩ := hex
  refine ⟨i0, hi0, μ, hμ.1, fun i hi => ?_, ?_, hμ.2.2.2⟩
  · rw [Finset.mem_erase] at hi
    by_cases h : i = i0
    · rw [h, hμi0]
    · exact hμ.2.1 i (fun hS => hi ⟨h, hS⟩)
  · rw [hμ.2.2.1, Finset.card_erase_of_mem hi0, Nat.cast_sub (by omega)]; push_cast; ring

theorem st_bound_core {n m : ℕ} (x : Fin n → E) (hnorm : ∀ i, ‖x i‖ ≤ 1)
    (S : Finset (Fin n))
    (h : S.card ≤ m ∨ ∃ l, StGood x m S ((S.card : ℝ) - m) l) :
    ‖∑ i ∈ S, x i‖ ≤ m := by
  classical
  rcases h with h | ⟨l, hl⟩
  · calc ‖∑ i ∈ S, x i‖ ≤ ∑ i ∈ S, ‖x i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ S, (1:ℝ) := Finset.sum_le_sum (fun i _ => hnorm i)
      _ = S.card := by simp
      _ ≤ m := by exact_mod_cast h
  · have hsumS : ∀ f : Fin n → E, ∑ i, l i • f i = ∑ i ∈ S, l i • f i := fun f =>
      (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by simp [hl.2.1 i hi])).symm
    have hsumS' : ∑ i, l i = ∑ i ∈ S, l i :=
      (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by simp [hl.2.1 i hi])).symm
    have heq : ∑ i ∈ S, x i = ∑ i ∈ S, (1 - l i) • x i := by
      simp only [sub_smul, one_smul, Finset.sum_sub_distrib, ← hsumS, hl.2.2.2, sub_zero]
    rw [heq]
    calc ‖∑ i ∈ S, (1 - l i) • x i‖ ≤ ∑ i ∈ S, ‖(1 - l i) • x i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ S, (1 - l i) := by
          apply Finset.sum_le_sum; intro i _
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [(hl.1 i).2])]
          have := hnorm i
          nlinarith [(hl.1 i).2]
      _ = m := by
          rw [Finset.sum_sub_distrib, ← hsumS', hl.2.2.1]; simp

theorem st_chain_core {n m : ℕ} (hdim : Module.finrank ℝ E = m) (x : Fin n → E)
    (hnorm : ∀ i, ‖x i‖ ≤ 1) : ∀ k : ℕ, ∀ S : Finset (Fin n), S.card = k →
    (S.card ≤ m ∨ ∃ l, StGood x m S ((S.card : ℝ) - m) l) →
    ∃ T : ℕ → Finset (Fin n), (∀ j ≤ k, T j ⊆ S ∧ (T j).card = j ∧ ‖∑ i ∈ T j, x i‖ ≤ m) ∧
      (∀ j < k, T j ⊆ T (j + 1)) := by
  classical
  intro k
  induction k with
  | zero =>
    intro S _ _
    refine ⟨fun _ => ∅, fun j hj => ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    have : j = 0 := by omega
    subst this; simp
  | succ k ih =>
    intro S hS h
    obtain ⟨i0, hi0, hS'⟩ : ∃ i0 ∈ S, ((S.erase i0).card ≤ m ∨
        ∃ l, StGood x m (S.erase i0) (((S.erase i0).card : ℝ) - m) l) := by
      by_cases hkm : S.card ≤ m
      · obtain ⟨i0, hi0⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
        exact ⟨i0, hi0, Or.inl (by rw [Finset.card_erase_of_mem hi0]; omega)⟩
      · rcases h with h | ⟨l, hl⟩
        · omega
        · obtain ⟨i0, hi0, μ, hμ⟩ := st_reduce_core hdim x S (by omega) l hl
          exact ⟨i0, hi0, Or.inr ⟨μ, hμ⟩⟩
    obtain ⟨T', hT1, hT2⟩ := ih (S.erase i0) (by rw [Finset.card_erase_of_mem hi0]; omega) hS'
    refine ⟨fun j => if j ≤ k then T' j else S, fun j hj => ?_, fun j hj => ?_⟩
    · by_cases hjk : j ≤ k
      · simp only [hjk, if_true]
        obtain ⟨a1, a2, a3⟩ := hT1 j hjk
        exact ⟨a1.trans (Finset.erase_subset _ _), a2, a3⟩
      · have : j = k + 1 := by omega
        subst this
        simp only [hjk, if_false]
        exact ⟨subset_rfl, hS, st_bound_core x hnorm S h⟩
    · by_cases hjk : j + 1 ≤ k
      · simp only [hjk, show j ≤ k by omega, if_true]; exact hT2 j (by omega)
      · have : j = k := by omega
        subst this
        simp only [le_refl, if_true, hjk, if_false]
        exact (hT1 j le_rfl).1.trans (Finset.erase_subset _ _)

theorem st_core {m n : ℕ} (hdim : Module.finrank ℝ E = m) (x : Fin n → E)
    (hsum : ∑ i, x i = 0) (hnorm : ∀ i, ‖x i‖ ≤ 1) :
    ∃ σ : Equiv.Perm (Fin n), ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ‖∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), x (σ j)‖ ≤ (m : ℝ) := by
  classical
  have hstart : (Finset.univ : Finset (Fin n)).card ≤ m ∨
      ∃ l, StGood x m Finset.univ (((Finset.univ : Finset (Fin n)).card : ℝ) - m) l := by
    rw [Finset.card_univ, Fintype.card_fin]
    by_cases hnm : n ≤ m
    · exact Or.inl hnm
    · right
      have hn : (m : ℝ) < n := by exact_mod_cast (not_le.mp hnm)
      have hn0 : (0 : ℝ) < n := by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
      refine ⟨fun _ => ((n : ℝ) - m) / n, fun i => ⟨?_, ?_⟩, fun i hi => absurd (Finset.mem_univ i) hi, ?_, ?_⟩
      · exact div_nonneg (by linarith) hn0.le
      · rw [div_le_one hn0]; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
      · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      · rw [← Finset.smul_sum, hsum, smul_zero]
  obtain ⟨T, hT1, hT2⟩ := st_chain_core hdim x hnorm n Finset.univ
    (by rw [Finset.card_univ, Fintype.card_fin]) hstart
  have hmono : ∀ a b, a ≤ b → b ≤ n → T a ⊆ T b := by
    intro a b hab hbn
    induction b with
    | zero => have : a = 0 := by omega
              subst this; exact subset_rfl
    | succ b ihb =>
      rcases Nat.eq_or_lt_of_le hab with h | h
      · rw [h]
      · exact (ihb (by omega) (by omega)).trans (hT2 b (by omega))
  have hone : ∀ j : Fin n, ∃ a, T ((j : ℕ) + 1) \ T j = {a} := by
    intro j
    apply Finset.card_eq_one.mp
    rw [Finset.card_sdiff_of_subset (hT2 j j.isLt), (hT1 _ (by omega)).2.1, (hT1 _ (by omega)).2.1]
    omega
  choose f hf using hone
  have hfin : ∀ j : Fin n, f j ∈ T ((j : ℕ) + 1) ∧ f j ∉ T j := by
    intro j
    have : f j ∈ T ((j : ℕ) + 1) \ T j := by rw [hf j]; exact Finset.mem_singleton_self _
    exact Finset.mem_sdiff.mp this
  have hkey : ∀ j j' : Fin n, (j : ℕ) < j' → f j ≠ f j' := by
    intro j j' hlt heq
    have h1 := hmono _ _ (show (j : ℕ) + 1 ≤ j' by omega) j'.isLt.le (hfin j).1
    rw [heq] at h1
    exact (hfin j').2 h1
  have hinj : Function.Injective f := by
    intro j j' heq
    rcases lt_trichotomy (j : ℕ) j' with h | h | h
    · exact absurd heq (hkey _ _ h)
    · exact Fin.ext h
    · exact absurd heq.symm (hkey _ _ h)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun k hk1 hkn => ?_⟩
  have himg : (Finset.univ.filter (fun j : Fin n => (j : ℕ) < k)).image f = T k := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
      have hj' := (Finset.mem_filter.mp hj).2
      exact hmono _ _ (by omega) hkn (hfin j).1
    · rw [Finset.card_image_of_injective _ hinj, Fin.card_filter_val_lt, (hT1 k hkn).2.1]
      omega
  have : ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k),
      x ((Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)) j) = ∑ i ∈ T k, x i := by
    rw [← himg, Finset.sum_image (fun a _ b _ h => hinj h)]
    rfl
  rw [this]
  exact (hT1 k hkn).2.2

end

end IPProximity.Eisenbrand

open IPProximity.Eisenbrand


theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {m n : ℕ} (hdim : Module.finrank ℝ E = m) (x : Fin n → E)
    (hsum : ∑ i, x i = 0) (hnorm : ∀ i, ‖x i‖ ≤ 1) :
    ∃ σ : Equiv.Perm (Fin n), ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ‖∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), x (σ j)‖ ≤ (m : ℝ) := by
  exact st_core hdim x hsum hnorm
