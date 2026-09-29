-- Prove2me | solution 1 for IPProximity.Eisenbrand.integrality_gap
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:24:28.495149+00:00
-- url     : https://prove2.me/submissions/ff29353f-a100-40da-bb9e-f2a2fb7d7bed

import Mathlib
import Definitions.Def_IPProximity_Eisenbrand_lpPolytope
import Definitions.Def_IPProximity_Eisenbrand_ipFeasible
import Definitions.Def_IPProximity_Eisenbrand_IsLPOptimal
import Definitions.Def_IPProximity_Eisenbrand_IsIPOptimal



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


theorem lin_core (bad : ℕ → Prop) [DecidablePred bad] :
    ∀ Z : Finset ℕ, ∀ lo hi : ℕ, (∀ z ∈ Z, lo ≤ z ∧ z ≤ hi) →
      (∀ a ∈ Z, ∀ b ∈ Z, a < b → ∃ t, a ≤ t ∧ t < b ∧ bad t) →
      Z.card ≤ ((Finset.Ico lo hi).filter bad).card + 1 := by
  intro Z
  induction Z using Finset.induction_on_max with
  | empty => intros; simp
  | insert b Z hlt ih =>
    intro lo hi hbd hpair
    have hbZ : b ∉ Z := fun h => lt_irrefl _ (hlt b h)
    rw [Finset.card_insert_of_notMem hbZ]
    rcases Z.eq_empty_or_nonempty with he | hne
    · simp [he]
    set a := Z.max' hne with ha
    have haZ : a ∈ Z := Z.max'_mem hne
    have hih := ih lo a (fun z hz => ⟨(hbd z (Finset.mem_insert_of_mem hz)).1, Z.le_max' z hz⟩)
      (fun a' ha' b' hb' h => hpair a' (Finset.mem_insert_of_mem ha') b'
        (Finset.mem_insert_of_mem hb') h)
    obtain ⟨t, ht1, ht2, ht3⟩ := hpair a (Finset.mem_insert_of_mem haZ) b
      (Finset.mem_insert_self _ _) (hlt a haZ)
    have hbhi := (hbd b (Finset.mem_insert_self _ _)).2
    have hsub : insert t ((Finset.Ico lo a).filter bad) ⊆ (Finset.Ico lo hi).filter bad := by
      intro s hs
      rw [Finset.mem_insert] at hs
      rcases hs with rfl | hs
      · have hlo := (hbd a (Finset.mem_insert_of_mem haZ)).1
        simp only [Finset.mem_filter, Finset.mem_Ico]; exact ⟨⟨by omega, by omega⟩, ht3⟩
      · simp only [Finset.mem_filter, Finset.mem_Ico] at hs ⊢
        exact ⟨⟨hs.1.1, by omega⟩, hs.2⟩
    have htn : t ∉ (Finset.Ico lo a).filter bad := by
      simp only [Finset.mem_filter, Finset.mem_Ico]; omega
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem htn] at this
    omega

theorem modinj_core {L q t t' : ℕ} (hL : 0 < L) (h1 : q ≤ t) (h2 : t < q + L) (h3 : q ≤ t')
    (h4 : t' < q + L) (h : t % L = t' % L) : t = t' := by
  rcases le_total t t' with h5 | h5
  · have hm := Nat.sub_mod_eq_zero_of_mod_eq h.symm
    rw [Nat.mod_eq_of_lt (by omega)] at hm
    omega
  · have hm := Nat.sub_mod_eq_zero_of_mod_eq h
    rw [Nat.mod_eq_of_lt (by omega)] at hm
    omega

theorem comb_core {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ} (Δ : ℕ)
    (e : α → Fin m → ℤ) (he : ∀ a i, |e a i| ≤ Δ) (hsum : ∑ a, e a = 0)
    (W : Finset α) (hW : W.card ≤ m) (hL : m * (2 * m * Δ + 1) ^ m < Fintype.card α) :
    ∃ B : Finset α, B.Nonempty ∧ Disjoint B W ∧ ∑ a ∈ B, e a = 0 := by
  classical
  set L := Fintype.card α with hLdef
  have hK : 1 ≤ (2 * m * Δ + 1) ^ m := Nat.one_le_pow _ _ (by omega)
  have hmL : m < L := lt_of_le_of_lt (by nlinarith) hL
  rcases Nat.eq_zero_or_pos Δ with hΔ0 | hΔpos
  · -- trivial case
    have : (Finset.univ \ W).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
      omega
    obtain ⟨a, ha⟩ := this
    refine ⟨{a}, Finset.singleton_nonempty _, ?_, ?_⟩
    · rw [Finset.disjoint_singleton_left]; exact (Finset.mem_sdiff.mp ha).2
    · rw [Finset.sum_singleton]; funext i; have := he a i; rw [hΔ0] at this; simp at this
      simp [this]
  have hLpos : 0 < L := by omega
  let φ : Fin L ≃ α := (Fintype.equivFin α).symm
  let xs : Fin L → (Fin m → ℝ) := fun k i => (e (φ k) i : ℝ) / Δ
  have hΔr : (0 : ℝ) < Δ := by exact_mod_cast hΔpos
  have hxs_sum : ∑ k, xs k = 0 := by
    funext i
    simp only [xs, Finset.sum_apply, Pi.zero_apply, ← Finset.sum_div]
    have : ∑ k, (e (φ k) i : ℝ) = ((∑ a, e a) i : ℤ) := by
      rw [Finset.sum_apply]; push_cast
      exact Equiv.sum_comp φ (fun a => (e a i : ℝ))
    rw [this, hsum]; simp
  have hxs_norm : ∀ k, ‖xs k‖ ≤ 1 := by
    intro k
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    simp only [xs, Real.norm_eq_abs, abs_div, abs_of_pos hΔr]
    rw [div_le_one hΔr, ← Int.cast_abs]; exact_mod_cast he _ _
  obtain ⟨σ, hσ⟩ := st_core (E := Fin m → ℝ) (m := m) (by simp) xs hxs_sum hxs_norm
  let pos : ℕ → α := fun t => φ (σ ⟨t % L, Nat.mod_lt _ hLpos⟩)
  let g : ℕ → Fin m → ℤ := fun t => e (pos t)
  let T : ℕ → Fin m → ℤ := fun j => ∑ t ∈ Finset.range j, g t
  have hTfilter : ∀ j ≤ L, T j = ∑ k ∈ Finset.univ.filter (fun k : Fin L => (k : ℕ) < j),
      e (φ (σ k)) := by
    intro j hj
    rw [Finset.sum_filter]
    let F : ℕ → Fin m → ℤ := fun t => if t < j then
      (if h : t < L then e (φ (σ ⟨t, h⟩)) else 0) else 0
    have h1 : ∑ a : Fin L, (if (a : ℕ) < j then e (φ (σ a)) else 0) = ∑ t ∈ Finset.range L, F t := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl; intro a _; simp [F, a.isLt]
    rw [h1, ← Finset.sum_filter]
    have : (Finset.range L).filter (fun t => t < j) = Finset.range j := by
      ext t; simp; omega
    rw [this]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    simp only [g, pos, F, dif_pos (show t < L by omega), Nat.mod_eq_of_lt (show t < L by omega)]
  have hTL : T L = 0 := by
    rw [hTfilter L le_rfl]
    have : Finset.univ.filter (fun k : Fin L => (k : ℕ) < L) = Finset.univ := by
      ext k; simp [k.isLt]
    rw [this, Equiv.sum_comp σ (fun k => e (φ k)), Equiv.sum_comp φ e, hsum]
  have hTper : ∀ j, T (L + j) = T j := by
    intro j
    simp only [T]
    rw [Finset.sum_range_add, show (∑ t ∈ Finset.range L, g t) = T L from rfl, hTL, zero_add]
    apply Finset.sum_congr rfl; intro t _
    simp only [g, pos, Nat.add_mod_left]
  have hTbd : ∀ j < L, ∀ i, |T j i| ≤ (m * Δ : ℤ) := by
    intro j hj i
    rcases Nat.eq_zero_or_pos j with h0 | hjpos
    · subst h0; simp [T]; positivity
    have hb := hσ j hjpos hj.le
    have hc : |(∑ k ∈ Finset.univ.filter (fun k : Fin L => (k : ℕ) < j), xs (σ k)) i| ≤ m :=
      le_trans (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ i) hb
    rw [Finset.sum_apply] at hc
    simp only [xs, ← Finset.sum_div, abs_div, abs_of_pos hΔr, div_le_iff₀ hΔr] at hc
    rw [hTfilter j hj.le, Finset.sum_apply]
    have : ((|∑ k ∈ Finset.univ.filter (fun k : Fin L => (k : ℕ) < j), e (φ (σ k)) i| : ℤ) : ℝ)
        ≤ ((m * Δ : ℤ) : ℝ) := by push_cast; exact hc
    exact_mod_cast this
  -- pigeonhole
  let box : Finset (Fin m → ℤ) := Fintype.piFinset (fun _ => Finset.Icc (-(m * Δ : ℤ)) (m * Δ))
  have hbox : box.card = (2 * m * Δ + 1) ^ m := by
    simp only [box, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    congr 1
    rw [show ((m * Δ : ℤ) + 1 - -(m * Δ : ℤ)) = ((2 * m * Δ + 1 : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  obtain ⟨p, _, hQ⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := Finset.range L) (t := box) (f := T) (n := m)
    (fun j hj => by
      simp only [box, Fintype.mem_piFinset, Finset.mem_Icc]
      intro i; exact abs_le.mp (hTbd j (Finset.mem_range.mp hj) i))
    (by rw [hbox, Finset.card_range, mul_comm]; exact hL)
  set Q := (Finset.range L).filter (fun j => T j = p) with hQdef
  have hQne : Q.Nonempty := Finset.card_pos.mp (by omega)
  set q := Q.min' hQne with hq
  have hqQ : q ∈ Q := Q.min'_mem hQne
  have hQmem : ∀ j ∈ Q, j < L ∧ T j = p := fun j hj => by
    simp only [hQdef, Finset.mem_filter, Finset.mem_range] at hj; exact hj
  set Z := insert (q + L) Q with hZ
  have hqL : q + L ∉ Q := fun h => by have := (hQmem _ h).1; omega
  have hZcard : Z.card = Q.card + 1 := Finset.card_insert_of_notMem hqL
  have hZbd : ∀ z ∈ Z, q ≤ z ∧ z ≤ q + L := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · omega
    · exact ⟨Q.min'_le z hz, by have := (hQmem z hz).1; omega⟩
  have hZT : ∀ z ∈ Z, T z = p := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · rw [add_comm, hTper]; exact (hQmem q hqQ).2
    · exact (hQmem z hz).2
  have posinj : ∀ t t', q ≤ t → t < q + L → q ≤ t' → t' < q + L → pos t = pos t' → t = t' := by
    intro t t' h1 h2 h3 h4 h
    have := congrArg Fin.val (σ.injective (φ.injective h))
    exact modinj_core hLpos h1 h2 h3 h4 this
  obtain ⟨a, haZ, b, hbZ, hab, hgood⟩ : ∃ a ∈ Z, ∃ b ∈ Z, a < b ∧
      ∀ t, a ≤ t → t < b → pos t ∉ W := by
    by_contra hcon
    push_neg at hcon
    have h1 := lin_core (fun t => pos t ∈ W) Z q (q + L) hZbd hcon
    have h2 : ((Finset.Ico q (q + L)).filter (fun t => pos t ∈ W)).card ≤ W.card := by
      apply Finset.card_le_card_of_injOn pos
      · intro t ht; exact (Finset.mem_filter.mp ht).2
      · intro t ht t' ht' h
        simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_setOf_eq] at ht ht'
        exact posinj t t' ht.1.1 ht.1.2 ht'.1.1 ht'.1.2 h
    omega
  have hTab : T a = T b := by rw [hZT a haZ, hZT b hbZ]
  have ha' := hZbd a haZ
  have hb' := hZbd b hbZ
  refine ⟨(Finset.Ico a b).image pos, ⟨pos a, Finset.mem_image_of_mem _
    (Finset.mem_Ico.mpr ⟨le_rfl, hab⟩)⟩, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro c hc
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hc
    rw [Finset.mem_Ico] at ht
    exact hgood t ht.1 ht.2
  · rw [Finset.sum_image]
    · have : ∑ t ∈ Finset.Ico a b, e (pos t) = T b - T a := Finset.sum_Ico_eq_sub _ hab.le
      rw [this, hTab, sub_self]
    · intro t ht t' ht' h
      simp only [Finset.coe_Ico, Set.mem_Ico] at ht ht'
      exact posinj t t' (by omega) (by omega) (by omega) (by omega) h

/-- at an extreme point, the strictly-interior coordinates number at most m -/
theorem vertex_card_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (u : Fin n → ℕ) (x : Fin n → ℝ) (hx : x ∈ Set.extremePoints ℝ (lpPolytope A b u)) :
    (Finset.univ.filter (fun i => 0 < x i ∧ x i < (u i : ℝ))).card ≤ m := by
  classical
  set F := Finset.univ.filter (fun i => 0 < x i ∧ x i < (u i : ℝ)) with hF
  by_contra hlt
  push_neg at hlt
  let E : (F → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi (fun i => if h : i ∈ F then LinearMap.proj (⟨i, h⟩ : F) else 0)
  let L : (F → ℝ) →ₗ[ℝ] (Fin m → ℝ) := (A.map (Int.cast : ℤ → ℝ)).mulVecLin ∘ₗ E
  have hker : LinearMap.ker L ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp [Module.finrank_fin_fun]
    exact hlt
  obtain ⟨w, hwk, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  set v := E w with hv
  have hAv : (A.map (Int.cast : ℤ → ℝ)).mulVec v = 0 := by
    have := LinearMap.mem_ker.mp hwk
    simpa [L] using this
  have hvF : ∀ i, i ∉ F → v i = 0 := by
    intro i hi; simp [hv, E, hi]
  have hv0 : v ≠ 0 := by
    intro h; apply hw0; funext ⟨i, hi⟩
    have := congrFun h i
    simpa [hv, E, hi] using this
  have hmem := hx.1
  -- eventually good
  have hev : ∀ᶠ t in nhds (0:ℝ), ∀ i, 0 ≤ x i + t * v i ∧ x i + t * v i ≤ (u i : ℝ) := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i ∈ F
    · have hi' := (Finset.mem_filter.mp hi).2
      have hc : Continuous (fun t : ℝ => x i + t * v i) := by continuity
      have h1 : ∀ᶠ t in nhds (0:ℝ), x i + t * v i ∈ Set.Ioo 0 (u i : ℝ) := by
        apply hc.continuousAt.preimage_mem_nhds
        apply Ioo_mem_nhds <;> simp [hi'.1, hi'.2]
      filter_upwards [h1] with t ht
      exact ⟨ht.1.le, ht.2.le⟩
    · filter_upwards with t
      simp [hvF i hi, hmem.2 i]
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hp := hball (y := ε/2) (by rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
  have hm := hball (y := -(ε/2)) (by rw [Real.dist_eq]; simp; rw [abs_of_pos (by linarith)]; linarith)
  have hin : ∀ t : ℝ, (∀ i, 0 ≤ x i + t * v i ∧ x i + t * v i ≤ (u i : ℝ)) →
      (x + t • v) ∈ lpPolytope A b u := by
    intro t ht
    refine ⟨?_, fun i => by simpa [mul_comm] using ht i⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hAv, hmem.1]; simp
  have hseg : x ∈ openSegment ℝ (x + (ε/2) • v) (x + (-(ε/2)) • v) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext i; simp; ring
  have := hx.2 (hin _ hp) (hin _ hm) hseg
  apply hv0
  have h2 : (ε/2) • v = 0 := by
    have := congrArg (fun y => y - x) this; simpa using this
  rcases smul_eq_zero.mp h2 with h | h
  · linarith
  · exact h


theorem int_split_core (m : ℕ) (Δ : ℤ) (hΔ : 0 ≤ Δ) (v : ℤ) (hv : |v| ≤ Δ * m) :
    ∃ w : Fin m → ℤ, (∀ j, |w j| ≤ Δ) ∧ ∑ j, w j = v := by
  let f : ℕ → ℤ := fun k => max (-(Δ * k)) (min (Δ * k) v)
  refine ⟨fun j => f (j + 1) - f j, ?_, ?_⟩
  · intro j
    simp only [f]
    push_cast
    generalize (j : ℕ) = k
    have : Δ * ((k:ℤ) + 1) = Δ * k + Δ := by ring
    rw [this]
    generalize Δ * (k:ℤ) = a
    rw [abs_le]
    constructor <;> omega
  · rw [Fin.sum_univ_eq_sum_range (fun j => f (j + 1) - f j), Finset.sum_range_sub]
    simp only [f]
    rw [abs_le] at hv
    push_cast
    generalize Δ * (m:ℤ) = a at hv ⊢
    omega

theorem fps_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (u : Fin n → ℕ) (Δ : ℕ) (hΔ : ∀ i j, |A i j| ≤ (Δ : ℤ))
    (x : Fin n → ℝ) (hx : x ∈ Set.extremePoints ℝ (lpPolytope A b u)) (z : Fin n → ℤ) :
    let r : Fin n → ℤ := fun i => if x i < (z i : ℝ) then ⌈x i⌉ else ⌊x i⌋
    let frac : Fin n → ℝ := fun i => x i - (r i : ℝ)
    (∀ i, |(-(Matrix.mulVec (A.map (Int.cast : ℤ → ℝ)) frac)) i| ≤ (Δ : ℝ) * m) ∧
      ∃ w : Fin m → Fin m → ℤ, (∀ j i, |w j i| ≤ (Δ : ℤ)) ∧
        ∀ i, ∑ j, (w j i : ℝ) = (-(Matrix.mulVec (A.map (Int.cast : ℤ → ℝ)) frac)) i := by
  classical
  intro r frac
  set F := Finset.univ.filter (fun i => 0 < x i ∧ x i < (u i : ℝ)) with hF
  have hcard : F.card ≤ m := vertex_card_core A b u x hx
  have hmem := hx.1
  have hfrac0 : ∀ i, i ∉ F → frac i = 0 := by
    intro i hi
    have hint : ∃ k : ℤ, x i = k := by
      by_cases h0 : x i = 0
      · exact ⟨0, by simp [h0]⟩
      by_cases h1 : x i = (u i : ℝ)
      · exact ⟨u i, by simp [h1]⟩
      exfalso; apply hi
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨lt_of_le_of_ne (hmem.2 i).1 (Ne.symm h0), lt_of_le_of_ne (hmem.2 i).2 h1⟩
    obtain ⟨k, hk⟩ := hint
    simp only [frac, r, hk]
    split_ifs <;> simp
  have hfrac1 : ∀ i, |frac i| ≤ 1 := by
    intro i
    simp only [frac, r]
    split_ifs
    · have h1 := Int.le_ceil (x i); have h2 := Int.ceil_lt_add_one (x i)
      rw [abs_le]; constructor <;> linarith
    · have h1 := Int.floor_le (x i); have h2 := Int.lt_floor_add_one (x i)
      rw [abs_le]; constructor <;> linarith
  have hbound : ∀ i, |(-(Matrix.mulVec (A.map (Int.cast : ℤ → ℝ)) frac)) i| ≤ (Δ : ℝ) * m := by
    intro i
    rw [Pi.neg_apply, abs_neg]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [← Finset.sum_subset (Finset.subset_univ F) (fun j _ hj => by simp [hfrac0 j hj])]
    calc |∑ j ∈ F, (A i j : ℝ) * frac j| ≤ ∑ j ∈ F, |(A i j : ℝ) * frac j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ F, (Δ : ℝ) := by
          apply Finset.sum_le_sum; intro j _
          rw [abs_mul]
          have h1 : |(A i j : ℝ)| ≤ Δ := by
            have := hΔ i j; rw [← Int.cast_abs]; exact_mod_cast this
          have h2 := hfrac1 j
          calc |(A i j : ℝ)| * |frac j| ≤ Δ * 1 :=
                mul_le_mul h1 h2 (abs_nonneg _) (Nat.cast_nonneg _)
            _ = Δ := mul_one _
      _ = (Δ : ℝ) * F.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ (Δ : ℝ) * m := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _); exact_mod_cast hcard
  refine ⟨hbound, ?_⟩
  -- integrality
  let vZ : Fin m → ℤ := fun i => Matrix.mulVec A r i - b i
  have hvZ : ∀ i, (-(Matrix.mulVec (A.map (Int.cast : ℤ → ℝ)) frac)) i = (vZ i : ℝ) := by
    intro i
    have hb := congrFun hmem.1 i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply] at hb
    simp only [vZ, frac, Pi.neg_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, mul_sub, Finset.sum_sub_distrib, hb]
    push_cast; ring
  have hsplit : ∀ i, ∃ w : Fin m → ℤ, (∀ j, |w j| ≤ Δ) ∧ ∑ j, w j = vZ i := by
    intro i
    apply int_split_core m Δ (by positivity)
    have := hbound i
    rw [hvZ i] at this
    have : ((|vZ i| : ℤ) : ℝ) ≤ ((Δ * m : ℤ) : ℝ) := by push_cast; exact this
    exact_mod_cast this
  choose w hw1 hw2 using hsplit
  refine ⟨fun j i => w i j, fun j i => hw1 i j, fun i => ?_⟩
  rw [hvZ i, ← hw2 i]; push_cast; rfl


theorem coord_core (x : ℝ) (z r yt : ℤ) (u : ℕ) (hx0 : 0 ≤ x) (hxu : x ≤ u) (hzu : (z : ℝ) ≤ u)
    (hz0 : (0 : ℝ) ≤ z)
    (hr : ((x < z ∧ x ≤ r ∧ (r : ℝ) ≤ z) ∨ ((z : ℝ) ≤ x ∧ (z : ℝ) ≤ r ∧ (r : ℝ) ≤ x)))
    (hyt : (0 ≤ yt ∧ yt ≤ z - r) ∨ (z - r ≤ yt ∧ yt ≤ 0)) :
    (0 : ℝ) ≤ ((z - yt : ℤ) : ℝ) ∧ ((z - yt : ℤ) : ℝ) ≤ u ∧ 0 ≤ x + yt ∧ x + yt ≤ u ∧
      |((z - yt : ℤ) : ℝ) - x| = |(z : ℝ) - x| - |(yt : ℝ)| := by
  have hyt' : ((0 : ℝ) ≤ yt ∧ (yt : ℝ) ≤ z - r) ∨ ((z : ℝ) - r ≤ yt ∧ (yt : ℝ) ≤ 0) := by
    rcases hyt with h | h
    · left; exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    · right; exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  push_cast
  rcases hr with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have hy0 : (0 : ℝ) ≤ yt := by rcases hyt' with h | h <;> linarith [h.1, h.2]
    have hy1 : (yt : ℝ) ≤ z - r := by rcases hyt' with h | h <;> linarith [h.1, h.2]
    refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg hy0]; ring
  · have hy0 : (yt : ℝ) ≤ 0 := by rcases hyt' with h | h <;> linarith [h.1, h.2]
    have hy1 : (z : ℝ) - r ≤ yt := by rcases hyt' with h | h <;> linarith [h.1, h.2]
    refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos hy0]; ring

theorem mulVec_cast_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin n → ℤ) :
    (A.map (Int.cast : ℤ → ℝ)).mulVec (fun i => (v i : ℝ)) = fun k => ((A.mulVec v) k : ℝ) := by
  funext k; simp [Matrix.mulVec, dotProduct]

theorem dot_cast_core {n : ℕ} (c v : Fin n → ℤ) :
    dotProduct (fun i => (c i : ℝ)) (fun i => (v i : ℝ)) = ((dotProduct c v : ℤ) : ℝ) := by
  simp [dotProduct]

theorem exchange_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (c : Fin n → ℤ) (u : Fin n → ℕ) (x : Fin n → ℝ) (hopt : IsLPOptimal A b c u x)
    (z : Fin n → ℤ) (hz : z ∈ ipFeasible A b u) (yt : Fin n → ℤ) (hA : A.mulVec yt = 0)
    (hyt : ∀ i, (0 ≤ yt i ∧ yt i ≤ z i - (if x i < (z i : ℝ) then ⌈x i⌉ else ⌊x i⌋)) ∨
      (z i - (if x i < (z i : ℝ) then ⌈x i⌉ else ⌊x i⌋) ≤ yt i ∧ yt i ≤ 0)) :
    (z - yt) ∈ ipFeasible A b u ∧ dotProduct c z ≤ dotProduct c (z - yt) ∧
      ∑ i, |((z - yt) i : ℝ) - x i| = ∑ i, |(z i : ℝ) - x i| - ∑ i, |(yt i : ℝ)| := by
  have hx := hopt.1
  have key : ∀ i, (0 : ℝ) ≤ ((z i - yt i : ℤ) : ℝ) ∧ ((z i - yt i : ℤ) : ℝ) ≤ u i ∧
      0 ≤ x i + yt i ∧ x i + yt i ≤ u i ∧
      |((z i - yt i : ℤ) : ℝ) - x i| = |(z i : ℝ) - x i| - |(yt i : ℝ)| := by
    intro i
    apply coord_core (x i) (z i) _ (yt i) (u i) (hx.2 i).1 (hx.2 i).2
      (by exact_mod_cast (hz.2 i).2) (by exact_mod_cast (hz.2 i).1) _ (hyt i)
    split_ifs with h
    · left
      exact ⟨h, Int.le_ceil _, by exact_mod_cast Int.ceil_le.mpr h.le⟩
    · right
      push_neg at h
      exact ⟨h, by exact_mod_cast Int.le_floor.mpr h, Int.floor_le _⟩
  refine ⟨⟨?_, fun i => ?_⟩, ?_, ?_⟩
  · rw [Matrix.mulVec_sub, hA, sub_zero]; exact hz.1
  · have := key i
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2.1⟩
  · have hmem : (x + fun i => (yt i : ℝ)) ∈ lpPolytope A b u := by
      refine ⟨?_, fun i => ⟨(key i).2.2.1, (key i).2.2.2.1⟩⟩
      rw [Matrix.mulVec_add, mulVec_cast_core, hA, hx.1]; funext k; simp
    have h1 := hopt.2 _ hmem
    rw [dotProduct_add, dot_cast_core] at h1
    have h2 : dotProduct c yt ≤ 0 := by
      have : ((dotProduct c yt : ℤ) : ℝ) ≤ 0 := by linarith
      exact_mod_cast this
    rw [dotProduct_sub]; linarith
  · rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    have := (key i).2.2.2.2
    simp only [Pi.sub_apply]; exact this

theorem fracsum_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (u : Fin n → ℕ) (x : Fin n → ℝ) (hx : x ∈ Set.extremePoints ℝ (lpPolytope A b u))
    (z : Fin n → ℤ) :
    ∑ i, |x i - ((if x i < (z i : ℝ) then ⌈x i⌉ else ⌊x i⌋ : ℤ) : ℝ)| ≤ m := by
  classical
  set F := Finset.univ.filter (fun i => 0 < x i ∧ x i < (u i : ℝ)) with hF
  have hcard : F.card ≤ m := vertex_card_core A b u x hx
  have hmem := hx.1
  set frac : Fin n → ℝ := fun i => x i - ((if x i < (z i : ℝ) then ⌈x i⌉ else ⌊x i⌋ : ℤ) : ℝ)
    with hfrac
  have hfrac0 : ∀ i, i ∉ F → frac i = 0 := by
    intro i hi
    have hint : ∃ k : ℤ, x i = k := by
      by_cases h0 : x i = 0
      · exact ⟨0, by simp [h0]⟩
      by_cases h1 : x i = (u i : ℝ)
      · exact ⟨u i, by simp [h1]⟩
      exfalso; apply hi
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨lt_of_le_of_ne (hmem.2 i).1 (Ne.symm h0), lt_of_le_of_ne (hmem.2 i).2 h1⟩
    obtain ⟨k, hk⟩ := hint
    simp only [frac, hk]
    split_ifs <;> simp
  have hfrac1 : ∀ i, |frac i| ≤ 1 := by
    intro i
    simp only [frac]
    split_ifs
    · have h1 := Int.le_ceil (x i); have h2 := Int.ceil_lt_add_one (x i)
      rw [abs_le]; constructor <;> linarith
    · have h1 := Int.floor_le (x i); have h2 := Int.lt_floor_add_one (x i)
      rw [abs_le]; constructor <;> linarith
  show ∑ i, |frac i| ≤ m
  rw [← Finset.sum_subset (Finset.subset_univ F) (fun j _ hj => by simp [hfrac0 j hj])]
  calc ∑ i ∈ F, |frac i| ≤ ∑ i ∈ F, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hfrac1 i)
    _ = F.card := by simp
    _ ≤ m := by exact_mod_cast hcard

theorem mulVec_single_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (j : Fin n) (s : ℤ)
    (k : Fin m) : A.mulVec (Pi.single j s) k = A k j * s := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem l1_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (c : Fin n → ℤ) (u : Fin n → ℕ) (Δ : ℕ) (hΔ : ∀ i j, |A i j| ≤ (Δ : ℤ))
    (x : Fin n → ℝ) (hopt : IsLPOptimal A b c u x)
    (hvert : x ∈ Set.extremePoints ℝ (lpPolytope A b u))
    (hfeas : (ipFeasible A b u).Nonempty) :
    ∃ z : Fin n → ℤ, IsIPOptimal A b c u z ∧
      ∑ i, |(z i : ℝ) - x i| ≤ (m : ℝ) * (2 * m * Δ + 1) ^ m := by
  classical
  let Fz : Finset (Fin n → ℤ) := (Fintype.piFinset (fun i => Finset.Icc (0:ℤ) (u i))).filter
    (fun z => A.mulVec z = b)
  have hFz : ∀ z, z ∈ Fz ↔ z ∈ ipFeasible A b u := by
    intro z; simp [Fz, ipFeasible, Fintype.mem_piFinset, and_comm]
  obtain ⟨z0, hz0⟩ := hfeas
  have hFzne : Fz.Nonempty := ⟨z0, (hFz z0).mpr hz0⟩
  obtain ⟨zm, hzmF, hzmax⟩ := Finset.exists_max_image Fz (fun z => dotProduct c z) hFzne
  let O := Fz.filter (fun z => ∀ z' ∈ Fz, dotProduct c z' ≤ dotProduct c z)
  have hOne : O.Nonempty := ⟨zm, Finset.mem_filter.mpr ⟨hzmF, hzmax⟩⟩
  obtain ⟨z, hzO, hzmin⟩ := Finset.exists_min_image O (fun z => ∑ i, |(z i : ℝ) - x i|) hOne
  have hzF := (Finset.mem_filter.mp hzO).1
  have hzopt := (Finset.mem_filter.mp hzO).2
  have hzfeas := (hFz z).mp hzF
  have hIP : IsIPOptimal A b c u z := ⟨hzfeas, fun z' hz' => hzopt z' ((hFz z').mpr hz')⟩
  refine ⟨z, hIP, ?_⟩
  by_contra hcon
  push_neg at hcon
  set r : Fin n → ℤ := fun i => if x i < (z i : ℝ) then ⌈x i⌉ else ⌊x i⌋ with hr
  set y : Fin n → ℤ := fun i => z i - r i with hy
  have hfs : ∑ i, |x i - (r i : ℝ)| ≤ m := fracsum_core A b u x hvert z
  set N := ∑ i, (y i).natAbs with hNdef
  have hD : ∑ i, |(z i : ℝ) - x i| ≤ (N : ℝ) + m := by
    have h1 : ∀ i, |(z i : ℝ) - x i| ≤ ((y i).natAbs : ℝ) + |x i - (r i : ℝ)| := by
      intro i
      rw [Nat.cast_natAbs]
      simp only [hy]; push_cast
      calc |(z i : ℝ) - x i| = |((z i : ℝ) - r i) - (x i - r i)| := by ring_nf
        _ ≤ |(z i : ℝ) - r i| + |x i - r i| := abs_sub _ _
    calc ∑ i, |(z i : ℝ) - x i| ≤ ∑ i, (((y i).natAbs : ℝ) + |x i - (r i : ℝ)|) :=
          Finset.sum_le_sum (fun i _ => h1 i)
      _ = (N : ℝ) + ∑ i, |x i - (r i : ℝ)| := by rw [Finset.sum_add_distrib, hNdef]; push_cast; rfl
      _ ≤ (N : ℝ) + m := by linarith
  have hN : m * (2 * m * Δ + 1) ^ m < N + m := by
    have : ((m * (2 * m * Δ + 1) ^ m : ℕ) : ℝ) < ((N + m : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  have hfps := fps_core A b u Δ hΔ x hvert z
  dsimp only at hfps
  obtain ⟨_, w, hw1, hw2⟩ := hfps
  have hwint : ∀ k, ∑ j, w j k = A.mulVec r k - b k := by
    intro k
    have h := hw2 k
    have hb := congrFun hvert.1.1 k
    have : (-((A.map (Int.cast : ℤ → ℝ)).mulVec (fun i => x i - (r i : ℝ)))) k =
        ((A.mulVec r k - b k : ℤ) : ℝ) := by
      rw [show (fun i => x i - (r i : ℝ)) = x - (fun i => (r i : ℝ)) from rfl,
        Matrix.mulVec_sub, mulVec_cast_core]
      simp only [Pi.neg_apply, Pi.sub_apply, hb]; push_cast; ring
    have h' := h.trans this
    exact_mod_cast h'
  let ind : ((Σ i : Fin n, Fin (y i).natAbs) ⊕ Fin m) → Fin n → ℤ :=
    Sum.elim (fun p => Pi.single p.1 (Int.sign (y p.1))) (fun _ => 0)
  let e : ((Σ i : Fin n, Fin (y i).natAbs) ⊕ Fin m) → Fin m → ℤ :=
    Sum.elim (fun p => A.mulVec (Pi.single p.1 (Int.sign (y p.1)))) (fun j => w j)
  have hsign : ∀ a : ℤ, |Int.sign a| ≤ 1 := by
    intro a
    rcases lt_trichotomy a 0 with h | h | h
    · rw [Int.sign_eq_neg_one_of_neg h]; simp
    · rw [h]; simp
    · rw [Int.sign_eq_one_of_pos h]; simp
  have he : ∀ a k, |e a k| ≤ Δ := by
    intro a k
    rcases a with p | j
    · simp only [e, Sum.elim_inl]
      rw [mulVec_single_core, abs_mul]
      have := hΔ k p.1
      have h2 := hsign (y p.1)
      calc |A k p.1| * |Int.sign (y p.1)| ≤ (Δ : ℤ) * 1 :=
            mul_le_mul this h2 (abs_nonneg _) (Nat.cast_nonneg _)
        _ = Δ := mul_one _
    · simp only [e, Sum.elim_inr]; exact hw1 j k
  have hsumind : ∑ p : (Σ i : Fin n, Fin (y i).natAbs), Pi.single p.1 (Int.sign (y p.1)) = y := by
    funext k
    rw [Finset.sum_apply, Fintype.sum_sigma]
    simp [Pi.single_apply]
    rw [mul_comm]; exact Int.sign_mul_abs _
  have hsum_e : ∑ a, e a = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [e, Sum.elim_inl, Sum.elim_inr]
    rw [← Matrix.mulVec_sum, hsumind]
    funext k
    rw [Pi.add_apply, Finset.sum_apply, hwint k, Pi.zero_apply]
    have : A.mulVec y = A.mulVec z - A.mulVec r := by
      rw [← Matrix.mulVec_sub]; rfl
    rw [this, hzfeas.1]; simp
  let W : Finset ((Σ i : Fin n, Fin (y i).natAbs) ⊕ Fin m) :=
    Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩
  have hWc : W.card = m := by simp [W]
  have hcardα : Fintype.card ((Σ i : Fin n, Fin (y i).natAbs) ⊕ Fin m) = N + m := by
    rw [Fintype.card_sum, Fintype.card_sigma]; simp [hNdef]
  obtain ⟨B, hBne, hBW, hBsum⟩ := comb_core Δ e he hsum_e W hWc.le (by rw [hcardα]; exact hN)
  have hBinl : ∀ a ∈ B, ∃ p, a = Sum.inl p := by
    intro a ha
    rcases a with p | j
    · exact ⟨p, rfl⟩
    · exfalso
      exact Finset.disjoint_left.mp hBW ha (by simp [W])
  set yt : Fin n → ℤ := ∑ a ∈ B, ind a with hyt
  have hA : A.mulVec yt = 0 := by
    rw [hyt, Matrix.mulVec_sum, ← hBsum]
    apply Finset.sum_congr rfl
    intro a ha
    obtain ⟨p, rfl⟩ := hBinl a ha
    rfl
  have hindsign : ∀ a i, (0 ≤ y i → 0 ≤ ind a i) ∧ (y i ≤ 0 → ind a i ≤ 0) := by
    intro a i
    rcases a with ⟨j, t⟩ | j
    · simp only [ind, Sum.elim_inl, Pi.single_apply]
      split_ifs with h
      · subst h
        constructor
        · intro h0; exact Int.sign_nonneg_iff.mpr h0
        · intro h0; exact Int.sign_nonpos_iff.mpr h0
      · simp
    · simp [ind]
  have hindsum : ∀ i, ∑ a, ind a i = y i := by
    intro i
    rw [Fintype.sum_sum_type]
    simp only [ind, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, Finset.sum_const_zero, add_zero]
    rw [← Finset.sum_apply, hsumind]
  have hytc : ∀ i, (0 ≤ yt i ∧ yt i ≤ y i) ∨ (y i ≤ yt i ∧ yt i ≤ 0) := by
    intro i
    have hyti : yt i = ∑ a ∈ B, ind a i := by rw [hyt, Finset.sum_apply]
    rcases le_total 0 (y i) with h | h
    · left
      rw [hyti]
      refine ⟨Finset.sum_nonneg (fun a _ => (hindsign a i).1 h), ?_⟩
      rw [← hindsum i]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun a _ _ => (hindsign a i).1 h)
    · right
      rw [hyti]
      refine ⟨?_, Finset.sum_nonpos (fun a _ => (hindsign a i).2 h)⟩
      rw [← hindsum i]
      have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
        (f := fun a => - ind a i) (fun a _ _ => by have := (hindsign a i).2 h; linarith)
      simp only [Finset.sum_neg_distrib] at this
      linarith
  have hytpos : 0 < ∑ i, |(yt i : ℝ)| := by
    obtain ⟨a, ha⟩ := hBne
    obtain ⟨⟨i, t⟩, rfl⟩ := hBinl a ha
    have hyi : y i ≠ 0 := by
      have := t.isLt
      exact Int.natAbs_ne_zero.mp (by omega)
    have hyti : yt i = ∑ a ∈ B, ind a i := by rw [hyt, Finset.sum_apply]
    have hone : ind (Sum.inl ⟨i, t⟩) i = Int.sign (y i) := by simp [ind]
    have hpos : 0 < |yt i| := by
      rcases lt_or_gt_of_ne hyi with h | h
      · have h1 : yt i ≤ -1 := by
          rw [hyti]
          have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.singleton_subset_iff.mpr ha)
            (f := fun a => - ind a i) (fun a _ _ => by have := (hindsign a i).2 h.le; linarith)
          simp only [Finset.sum_singleton, Finset.sum_neg_distrib, hone,
            Int.sign_eq_neg_one_of_neg h] at this
          linarith
        rw [abs_pos]; omega
      · have h1 : 1 ≤ yt i := by
          rw [hyti]
          have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.singleton_subset_iff.mpr ha)
            (f := fun a => ind a i) (fun a _ _ => (hindsign a i).1 h.le)
          simp only [Finset.sum_singleton, hone, Int.sign_eq_one_of_pos h] at this
          linarith
        rw [abs_pos]; omega
    have : (0 : ℝ) < |(yt i : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hpos
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun i => |(yt i : ℝ)|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  obtain ⟨hfe, hdot, hdist⟩ := exchange_core A b c u x hopt z hzfeas yt hA hytc
  have hO' : z - yt ∈ O := by
    refine Finset.mem_filter.mpr ⟨(hFz _).mpr hfe, fun z' hz' => le_trans (hzopt z' hz') hdot⟩
  have := hzmin _ hO'
  rw [hdist] at this
  linarith

theorem ig_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (c : Fin n → ℤ) (u : Fin n → ℕ) (Δ : ℕ) (hΔ : ∀ i j, |A i j| ≤ (Δ : ℤ))
    (x : Fin n → ℝ) (hopt : IsLPOptimal A b c u x)
    (hvert : x ∈ Set.extremePoints ℝ (lpPolytope A b u))
    (z : Fin n → ℤ) (hz : IsIPOptimal A b c u z) :
    dotProduct (fun i => (c i : ℝ)) x - dotProduct (fun i => (c i : ℝ)) (fun i => (z i : ℝ)) ≤
      ‖(fun i => (c i : ℝ))‖ * ((m : ℝ) * (2 * m * Δ + 1) ^ m) := by
  obtain ⟨z', hz', hd⟩ := l1_core A b c u Δ hΔ x hopt hvert ⟨z, hz.1⟩
  have heq : dotProduct c z' = dotProduct c z :=
    le_antisymm (hz.2 z' hz'.1) (hz'.2 z hz.1)
  have heqr : dotProduct (fun i => (c i : ℝ)) (fun i => (z i : ℝ)) =
      dotProduct (fun i => (c i : ℝ)) (fun i => (z' i : ℝ)) := by
    rw [dot_cast_core, dot_cast_core, heq]
  rw [heqr]
  have hc : ∀ i, |(c i : ℝ)| ≤ ‖(fun i => (c i : ℝ))‖ := by
    intro i
    have := norm_le_pi_norm (fun i => (c i : ℝ)) i
    rwa [Real.norm_eq_abs] at this
  calc dotProduct (fun i => (c i : ℝ)) x - dotProduct (fun i => (c i : ℝ)) (fun i => (z' i : ℝ))
      = ∑ i, (c i : ℝ) * (x i - z' i) := by
        simp only [dotProduct, ← Finset.sum_sub_distrib, mul_sub]
    _ ≤ ∑ i, ‖(fun i => (c i : ℝ))‖ * |(z' i : ℝ) - x i| := by
        apply Finset.sum_le_sum; intro i _
        calc (c i : ℝ) * (x i - z' i) ≤ |(c i : ℝ) * (x i - z' i)| := le_abs_self _
          _ = |(c i : ℝ)| * |(z' i : ℝ) - x i| := by rw [abs_mul, abs_sub_comm]
          _ ≤ _ := mul_le_mul_of_nonneg_right (hc i) (abs_nonneg _)
    _ = ‖(fun i => (c i : ℝ))‖ * ∑ i, |(z' i : ℝ) - x i| := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (norm_nonneg _)

end IPProximity.Eisenbrand

open IPProximity.Eisenbrand


theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (c : Fin n → ℤ) (u : Fin n → ℕ) (Δ : ℕ) (hΔ : ∀ i j, |A i j| ≤ (Δ : ℤ))
    (x : Fin n → ℝ) (hopt : IsLPOptimal A b c u x)
    (hvert : x ∈ Set.extremePoints ℝ (lpPolytope A b u))
    (z : Fin n → ℤ) (hz : IsIPOptimal A b c u z) :
    dotProduct (fun i => (c i : ℝ)) x - dotProduct (fun i => (c i : ℝ)) (fun i => (z i : ℝ)) ≤
      ‖(fun i => (c i : ℝ))‖ * ((m : ℝ) * (2 * m * Δ + 1) ^ m) := by
  exact ig_core A b c u Δ hΔ x hopt hvert z hz
