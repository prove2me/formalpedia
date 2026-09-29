-- Prove2me | solution 1 for JohnsonApprox.SetCover.greedy_setCover_ratio_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T18:36:26.954482+00:00
-- url     : https://prove2.me/submissions/46973a69-0e72-44d5-aa14-f427d5251875

import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem
import Definitions.Def_JohnsonApprox_SetCover_C1
import Definitions.Def_JohnsonApprox_SetCover_Config
import Definitions.Def_JohnsonApprox_SetCover_Fig1



namespace JohnsonApprox.SetCover

open Finset

lemma harmonic_sub_ge (a b : ℕ) (hba : b ≤ a) (ha : 0 < a) :
    ((a : ℚ) - b) / a ≤ harmonic a - harmonic b := by
  unfold harmonic
  rw [← Finset.sum_range_add_sum_Ico _ hba, add_sub_cancel_left]
  have : ∑ _i ∈ Ico b a, (1 / (a : ℚ)) ≤ ∑ i ∈ Ico b a, ((↑(i + 1) : ℚ))⁻¹ := by
    apply sum_le_sum
    intro i hi
    rw [mem_Ico] at hi
    rw [one_div]
    apply inv_anti₀ (by positivity)
    exact_mod_cast (by omega : i + 1 ≤ a)
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul] at this
  rw [Nat.cast_sub hba] at this
  calc ((a : ℚ) - b) / a = ((a : ℚ) - b) * (1 / a) := by ring
    _ ≤ _ := this

lemma harmonic_nonneg' (n : ℕ) : 0 ≤ harmonic n := by
  unfold harmonic; exact sum_nonneg (fun i _ => by positivity)

lemma harmonic_mono' {a b : ℕ} (h : a ≤ b) : harmonic a ≤ harmonic b := by
  unfold harmonic
  exact sum_le_sum_of_subset_of_nonneg (range_mono h) (fun i _ _ => by positivity)

variable {ι α : Type} [Fintype ι] [DecidableEq α]

theorem lemma2_selectable_card_le [DecidableEq ι]
    (K : Config ι α) (M1 M0 : Finset ι)
    (h1 : Selectable K M1) (h0 : M0.biUnion K.SET = K.UNCOV) :
    (M1.card : ℚ) ≤ ∑ i ∈ M0, harmonic (K.SET i).card := by
  obtain ⟨js, hrun, rfl⟩ := h1
  induction hrun generalizing M0 with
  | halt K _ =>
    simp only [List.toFinset_nil, card_empty, Nat.cast_zero]
    exact sum_nonneg (fun i _ => harmonic_nonneg' _)
  | step K j K' js hstep hrun' ih =>
    obtain ⟨hne, hmax, hU, hS⟩ := hstep
    have h0' : M0.biUnion K'.SET = K'.UNCOV := by
      rw [hS, hU, ← h0]
      ext x; simp only [mem_biUnion, mem_sdiff]
      constructor
      · rintro ⟨i, hi, hx, hxj⟩; exact ⟨⟨i, hi, hx⟩, hxj⟩
      · rintro ⟨⟨i, hi, hx⟩, hxj⟩; exact ⟨i, hi, hx, hxj⟩
    have hIH := ih M0 h0'
    -- the chosen set is nonempty
    set m := (K.SET j).card with hm
    have hm1 : 1 ≤ m := by
      obtain ⟨u, hu⟩ := nonempty_iff_ne_empty.2 hne
      rw [← K.union_eq, mem_biUnion] at hu
      obtain ⟨i, _, hui⟩ := hu
      have := hmax i
      have : 0 < (K.SET i).card := card_pos.2 ⟨u, hui⟩
      omega
    -- charging
    have hcharge : ∀ i, ((K.SET i ∩ K.SET j).card : ℚ) / m ≤
        harmonic (K.SET i).card - harmonic (K'.SET i).card := by
      intro i
      have hsd : (K'.SET i) = K.SET i \ K.SET j := by rw [hS]
      have hcard : (K'.SET i).card = (K.SET i).card - (K.SET i ∩ K.SET j).card := by
        have := card_sdiff_add_card_inter (K.SET i) (K.SET j)
        rw [hsd]; omega
      have hle : (K'.SET i).card ≤ (K.SET i).card := by rw [hsd]; exact card_le_card sdiff_subset
      rcases Nat.eq_zero_or_pos (K.SET i).card with h0i | hposi
      · have : (K.SET i ∩ K.SET j).card = 0 := by
          have := card_le_card (inter_subset_left : K.SET i ∩ K.SET j ⊆ K.SET i); omega
        have h0' : (K'.SET i).card = 0 := by omega
        rw [this, h0i, h0']; simp
      · have h1 := harmonic_sub_ge _ _ hle hposi
        have h2 : ((K.SET i ∩ K.SET j).card : ℚ) = (K.SET i).card - (K'.SET i).card := by
          rw [hcard, Nat.cast_sub (card_le_card inter_subset_left)]; ring
        rw [h2]
        refine le_trans ?_ h1
        apply div_le_div_of_nonneg_left
        · rw [sub_nonneg]; exact_mod_cast hle
        · exact_mod_cast hposi
        · exact_mod_cast hmax i
    have hcover : m ≤ ∑ i ∈ M0, (K.SET i ∩ K.SET j).card := by
      have hsub : K.SET j ⊆ M0.biUnion (fun i => K.SET i ∩ K.SET j) := by
        intro x hx
        have hxU : x ∈ K.UNCOV := by rw [← K.union_eq]; exact mem_biUnion.2 ⟨j, mem_univ _, hx⟩
        rw [← h0, mem_biUnion] at hxU
        obtain ⟨i, hi, hxi⟩ := hxU
        exact mem_biUnion.2 ⟨i, hi, mem_inter.2 ⟨hxi, hx⟩⟩
      exact (card_le_card hsub).trans card_biUnion_le
    have hsum1 : (1 : ℚ) ≤ ∑ i ∈ M0, (harmonic (K.SET i).card - harmonic (K'.SET i).card) := by
      calc (1 : ℚ) = (m : ℚ) / m := by rw [div_self]; exact_mod_cast (by omega : m ≠ 0)
        _ ≤ (∑ i ∈ M0, ((K.SET i ∩ K.SET j).card : ℚ)) / m := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact_mod_cast hcover
        _ = ∑ i ∈ M0, ((K.SET i ∩ K.SET j).card : ℚ) / m := by rw [sum_div]
        _ ≤ _ := sum_le_sum (fun i _ => hcharge i)
    rw [sum_sub_distrib] at hsum1
    have hins : ((j :: js).toFinset.card : ℚ) ≤ (js.toFinset.card : ℚ) + 1 := by
      rw [List.toFinset_cons]
      exact_mod_cast card_insert_le _ _
    linarith

lemma run_of_reach [DecidableEq ι] (S : ι → Finset α) {σ σf : State ι α}
    (hr : Relation.ReflTransGen (Step S) σ σf) (hf : Halts σf) :
    ∀ h : Finset.univ.biUnion σ.SET = σ.UNCOV, ∃ js : List ι,
      IsRun (⟨σ.UNCOV, σ.SET, h⟩ : Config ι α) js ∧ σf.SUB ⊆ σ.SUB ∪ js.toFinset.image S := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro h
    exact ⟨[], IsRun.halt _ hf, subset_union_left⟩
  | @head σ σ' hst _ ih =>
    intro h
    obtain ⟨j, hnh, hmax, rfl⟩ := hst
    have h' : Finset.univ.biUnion (fun i => σ.SET i \ σ.SET j) = σ.UNCOV \ σ.SET j := by
      rw [← h]; ext x; simp only [mem_biUnion, mem_univ, true_and, mem_sdiff]
      constructor
      · rintro ⟨i, hx, hxj⟩; exact ⟨⟨i, hx⟩, hxj⟩
      · rintro ⟨⟨i, hx⟩, hxj⟩; exact ⟨i, hx, hxj⟩
    obtain ⟨js, hrun, hsub⟩ := ih h'
    refine ⟨j :: js, IsRun.step _ j _ js ⟨hnh, hmax, rfl, rfl⟩ hrun, ?_⟩
    intro x hx
    have := hsub hx
    simp only [mem_union, mem_insert, mem_image, List.mem_toFinset, List.mem_cons] at this ⊢
    rcases this with (h1 | h1) | ⟨a, ha, hax⟩
    · exact Or.inr ⟨j, Or.inl rfl, h1.symm⟩
    · exact Or.inl h1
    · exact Or.inr ⟨a, Or.inr ha, hax⟩

theorem upper_bound (k : ℕ) {ι α : Type} [Fintype ι] [DecidableEq α] (S : ι → Finset α)
    (hk : InSC k S) (F₁ : Finset (Finset α)) (hc : Choosable S F₁) :
    (F₁.card : ℚ) ≤ harmonic k * opt S := by
  classical
  obtain ⟨σ, hr, hh, rfl⟩ := hc
  obtain ⟨js, hrun, hsub⟩ := run_of_reach S hr hh rfl
  simp only [init, empty_union] at hsub
  -- optimal cover
  obtain ⟨F', hF', hopt⟩ := Finset.exists_mem_eq_inf' (s := subcovers S)
    ⟨family S, family_mem_subcovers S⟩ Finset.card
  have hopt' : opt S = F'.card := hopt
  unfold subcovers at hF'
  rw [mem_filter, mem_powerset] at hF'
  obtain ⟨hFsub, hFcov⟩ := hF'
  have hch : ∀ A : F', ∃ i, S i = A.1 := fun A => by
    have := hFsub A.2; unfold family at this; simpa using this
  let M0 : Finset ι := F'.attach.image (fun A => (hch A).choose)
  have hM0card : M0.card ≤ F'.card := card_image_le.trans (by simp)
  have hM0 : M0.biUnion (initConfig S).SET = (initConfig S).UNCOV := by
    simp only [initConfig]
    apply le_antisymm
    · intro x hx; rw [mem_biUnion] at hx; obtain ⟨i, _, hx⟩ := hx
      unfold ground; exact mem_biUnion.2 ⟨i, mem_univ _, hx⟩
    · intro x hx; rw [← hFcov, mem_biUnion] at hx; obtain ⟨A, hA, hxA⟩ := hx
      rw [mem_biUnion]
      refine ⟨(hch ⟨A, hA⟩).choose, mem_image.2 ⟨⟨A, hA⟩, mem_attach _ _, rfl⟩, ?_⟩
      rw [(hch ⟨A, hA⟩).choose_spec]; exact hxA
  have h2 := lemma2_selectable_card_le (initConfig S) js.toFinset M0 ⟨js, hrun, rfl⟩ hM0
  have h3 : ∑ i ∈ M0, harmonic ((initConfig S).SET i).card ≤ M0.card * harmonic k := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum (fun i _ => harmonic_mono' (hk i))
  have h4 : (σ.SUB.card : ℚ) ≤ js.toFinset.card := by
    exact_mod_cast (card_le_card hsub).trans card_image_le
  have hHk := harmonic_nonneg' k
  have h5 : (M0.card : ℚ) ≤ opt S := by rw [hopt']; exact_mod_cast hM0card
  nlinarith

section general
variable {ι α : Type} [Fintype ι] [DecidableEq α] [DecidableEq ι]

/-- State after choosing the indices in `D`. -/
def stD (S : ι → Finset α) (D : Finset ι) : State ι α :=
  ⟨D.image S, ground S \ D.biUnion S, fun i => S i \ D.biUnion S⟩

lemma init_eq_stD (S : ι → Finset α) : init S = stD S ∅ := by
  unfold init stD; simp

lemma step_stD (S : ι → Finset α) (D : Finset ι) (j : ι)
    (hne : ¬ Halts (stD S D))
    (hmax : ∀ i, (S i \ D.biUnion S).card ≤ (S j \ D.biUnion S).card) :
    Step S (stD S D) (stD S (insert j D)) := by
  refine ⟨j, hne, hmax, ?_⟩
  unfold stD
  simp only [image_insert, biUnion_insert, State.mk.injEq, true_and]
  constructor
  · ext x; simp only [mem_sdiff, mem_union]; tauto
  · funext i; ext x; simp only [mem_sdiff, mem_union]; tauto

end general

variable (k : ℕ)

lemma fact_dvd (t : Fin k) : (t.val + 1) ∣ k.factorial := Nat.dvd_factorial (by omega) t.2

lemma blk_lt (t : Fin k) (q : Fin k.factorial) :
    q.val / (t.val + 1) < k.factorial / (t.val + 1) := by
  obtain ⟨m, hm⟩ := fact_dvd k t
  have hq : q.val < k.factorial := q.2
  rw [show k.factorial / (t.val + 1) = m by rw [hm]; exact Nat.mul_div_cancel_left _ (by omega),
    Nat.div_lt_iff_lt_mul (by omega)]
  calc (q : ℕ) < k.factorial := hq
    _ = _ := by rw [hm, mul_comm]

def inD (u c : ℕ) : Fig1Index k → Bool
  | .inl _ => false
  | .inr p => decide (u ≤ p.1.val ∨ (p.1.val + 1 = u ∧ p.2.val < c))

def D (u c : ℕ) : Finset (Fig1Index k) := univ.filter (fun i => inD k u c i = true)

@[simp] lemma mem_D_inl (u c : ℕ) (q : Fin k.factorial) : Sum.inl q ∉ D k u c := by
  simp [D, inD]

@[simp] lemma mem_D_inr (u c : ℕ) (p : Σ s : Fin k, Fin (k.factorial / (s.val + 1))) :
    Sum.inr p ∈ D k u c ↔ (u ≤ p.1.val ∨ (p.1.val + 1 = u ∧ p.2.val < c)) := by
  simp [D, inD]

lemma mem_U (u c : ℕ) (x : Fig1Point k) :
    x ∈ (D k u c).biUnion (fig1 k) ↔
      (u ≤ x.1.val ∨ (x.1.val + 1 = u ∧ x.2.val / (x.1.val + 1) < c)) := by
  simp only [mem_biUnion]
  constructor
  · rintro ⟨i, hi, hx⟩
    rcases i with q | ⟨t, b⟩
    · simp at hi
    · simp only [mem_D_inr] at hi
      simp only [fig1, mem_filter, mem_univ, true_and] at hx
      obtain ⟨rfl, hb⟩ := hx
      rw [hb]; exact hi
  · intro h
    refine ⟨.inr ⟨x.1, ⟨x.2.val / (x.1.val + 1), blk_lt k x.1 x.2⟩⟩, ?_, ?_⟩
    · simp only [mem_D_inr]; exact h
    · simp [fig1]

lemma D_top : D k k 0 = ∅ := by
  ext i; rcases i with q | ⟨t, b⟩ <;> simp

lemma D_bot : (D k 0 0).image (fig1 k) = fig1F₁ k := by
  ext A; simp only [mem_image, mem_univ, true_and, fig1F₁]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases i with q | p
    · simp at hi
    · exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩; exact ⟨.inr p, by simp, rfl⟩

lemma D_next (u : ℕ) (hu : 1 ≤ u) : D k u (k.factorial / u) = D k (u - 1) 0 := by
  ext i; rcases i with q | ⟨t, b⟩
  · simp
  · simp only [mem_D_inr]
    have hb := b.2
    constructor
    · rintro (h | ⟨h1, _⟩) <;> omega
    · intro h
      rcases h with h | h
      · rcases Nat.lt_or_ge t.val u with h' | h'
        · right; refine ⟨by omega, ?_⟩
          have : t.val + 1 = u := by omega
          rw [← this]; exact hb
        · left; exact h'
      · omega

lemma D_succ (u c : ℕ) (hu : 1 ≤ u) (huk : u ≤ k) (hc : c < k.factorial / u) :
    insert (Sum.inr ⟨⟨u - 1, by omega⟩, ⟨c, by rw [show u - 1 + 1 = u by omega]; exact hc⟩⟩)
      (D k u c) = D k u (c + 1) := by
  ext i; rcases i with q | ⟨t, b⟩
  · simp
  · simp only [mem_insert, mem_D_inr]
    constructor
    · rintro (h | h)
      · simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at h
        obtain ⟨rfl, h2⟩ := h
        have := (Fin.heq_ext_iff (by simp)).1 h2
        simp at this; right; exact ⟨by simp only [Fin.val_mk]; omega, by omega⟩
      · omega
    · rintro (h | ⟨h1, h2⟩)
      · right; left; exact h
      · rcases Nat.lt_or_ge b.val c with h3 | h3
        · right; right; exact ⟨h1, h3⟩
        · left
          rw [Sum.inr.injEq]
          exact Sigma.ext (Fin.ext (by simp only [Fin.val_mk]; omega))
            ((Fin.heq_ext_iff (by simp only [Fin.val_mk]; rw [show u - 1 + 1 = t.val + 1 by omega])).2
              (by simp only [Fin.val_mk]; omega))


lemma cu_lt (u c : ℕ) (hc : c < k.factorial / u) (r : ℕ) (hr : r < u) :
    c * u + r < k.factorial := by
  have h1 : (c + 1) * u ≤ k.factorial / u * u := Nat.mul_le_mul_right _ hc
  have h2 := Nat.div_mul_le_self k.factorial u
  nlinarith

lemma cu_div (u c r : ℕ) (hr : r < u) : (c * u + r) / u = c := by
  rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, add_zero]

lemma ground_fig1 : ground (fig1 k) = univ := by
  ext x; simp only [ground, mem_biUnion, mem_univ, true_and, iff_true]
  exact ⟨.inl x.2, by simp [fig1]⟩

lemma inl_card_le (q : Fin k.factorial) : (fig1 k (.inl q)).card ≤ k := by
  have := card_le_card_of_injOn (fun x : Fig1Point k => x.1.val) (s := fig1 k (.inl q))
    (t := range k) (fun x _ => by simp) (by
      intro x hx y hy hxy
      simp only [fig1, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx hy
      exact Prod.ext (Fin.ext hxy) (hx.trans hy.symm))
  simpa using this

lemma inr_card_le (t : Fin k) (b : Fin (k.factorial / (t.val + 1))) :
    (fig1 k (.inr ⟨t, b⟩)).card ≤ t.val + 1 := by
  have := card_le_card_of_injOn (fun x : Fig1Point k => x.2.val) (s := fig1 k (.inr ⟨t, b⟩))
    (t := Ico (b.val * (t.val + 1)) (b.val * (t.val + 1) + (t.val + 1))) (by
      intro x hx
      simp only [fig1, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx
      simp only [coe_Ico, Set.mem_Ico]
      rw [← hx.2]
      exact ⟨Nat.div_mul_le_self _ _, Nat.lt_div_mul_add (by omega)⟩) (by
      intro x hx y hy hxy
      simp only [fig1, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx hy
      exact Prod.ext (hx.1.trans hy.1.symm) (Fin.ext hxy))
  simpa using this

lemma inSC_fig1 : InSC k (fig1 k) := by
  intro i; rcases i with q | ⟨t, b⟩
  · exact inl_card_le k q
  · exact (inr_card_le k t b).trans (by omega)

lemma other_card (u c : ℕ) (i : Fig1Index k) :
    (fig1 k i \ (D k u c).biUnion (fig1 k)).card ≤ u := by
  rcases i with q | ⟨t, b⟩
  · have := card_le_card_of_injOn (fun x : Fig1Point k => x.1.val)
      (s := fig1 k (.inl q) \ (D k u c).biUnion (fig1 k)) (t := range u) (by
        intro x hx
        simp only [coe_sdiff, Set.mem_diff, mem_coe, mem_U] at hx
        simp only [coe_range, Set.mem_Iio]; omega) (by
        intro x hx y hy hxy
        simp only [coe_sdiff, Set.mem_diff, mem_coe, fig1, mem_filter, mem_univ, true_and] at hx hy
        exact Prod.ext (Fin.ext hxy) (hx.1.trans hy.1.symm))
    simpa using this
  · rcases Nat.lt_or_ge t.val u with h | h
    · exact (card_le_card sdiff_subset).trans ((inr_card_le k t b).trans (by omega))
    · have : fig1 k (.inr ⟨t, b⟩) \ (D k u c).biUnion (fig1 k) = ∅ := by
        rw [sdiff_eq_empty_iff_subset]; intro x hx
        simp only [fig1, mem_filter, mem_univ, true_and] at hx
        rw [mem_U]; left; rw [hx.1]; exact h
      rw [this]; simp

/-- the index chosen in state `(u, c)` -/
def jdx (u c : ℕ) (hu : 1 ≤ u) (huk : u ≤ k) (hc : c < k.factorial / u) : Fig1Index k :=
  Sum.inr ⟨⟨u - 1, by omega⟩, ⟨c, by rw [show u - 1 + 1 = u by omega]; exact hc⟩⟩

lemma j_card (u c : ℕ) (hu : 1 ≤ u) (huk : u ≤ k) (hc : c < k.factorial / u) :
    u ≤ (fig1 k (jdx k u c hu huk hc) \ (D k u c).biUnion (fig1 k)).card := by
  have hfp := Nat.factorial_pos k
  let f : ℕ → Fig1Point k := fun r =>
    (⟨u - 1, by omega⟩, ⟨(c * u + r) % k.factorial, Nat.mod_lt _ hfp⟩)
  have := card_le_card_of_injOn f (s := range u)
    (t := fig1 k (jdx k u c hu huk hc) \ (D k u c).biUnion (fig1 k)) (by
      intro r hr
      simp only [coe_range, Set.mem_Iio] at hr
      have hm : (c * u + r) % k.factorial = c * u + r := Nat.mod_eq_of_lt (cu_lt k u c hc r hr)
      simp only [coe_sdiff, Set.mem_diff, mem_coe, mem_U, jdx, fig1, mem_filter, mem_univ,
        true_and, f, hm, Fin.val_mk, show u - 1 + 1 = u by omega, cu_div u c r hr]
      omega) (by
      intro r1 hr1 r2 hr2 h
      simp only [coe_range, Set.mem_Iio] at hr1 hr2
      simp only [f, Prod.mk.injEq, Fin.mk.injEq, true_and] at h
      rw [Nat.mod_eq_of_lt (cu_lt k u c hc r1 hr1), Nat.mod_eq_of_lt (cu_lt k u c hc r2 hr2)] at h
      omega)
  simpa using this

lemma reach_c (u : ℕ) (hu : 1 ≤ u) (huk : u ≤ k) :
    ∀ c ≤ k.factorial / u, Relation.ReflTransGen (Step (fig1 k))
      (stD (fig1 k) (D k u 0)) (stD (fig1 k) (D k u c)) := by
  intro c
  induction c with
  | zero => intro _; exact Relation.ReflTransGen.refl
  | succ c ih =>
    intro hc
    have hc' : c < k.factorial / u := by omega
    refine (ih (by omega)).tail ?_
    rw [← D_succ k u c hu huk hc']
    have hj := j_card k u c hu huk hc'
    apply step_stD
    · intro hh
      unfold Halts stD at hh
      simp only at hh
      obtain ⟨x, hx⟩ := card_pos.1 (by omega : 0 < (fig1 k (jdx k u c hu huk hc') \
        (D k u c).biUnion (fig1 k)).card)
      rw [mem_sdiff] at hx
      have : x ∈ ground (fig1 k) \ (D k u c).biUnion (fig1 k) := by
        rw [ground_fig1]; exact mem_sdiff.2 ⟨mem_univ _, hx.2⟩
      rw [hh] at this; simp at this
    · intro i; exact (other_card k u c i).trans hj

lemma reach_all : ∀ m ≤ k, Relation.ReflTransGen (Step (fig1 k)) (init (fig1 k))
    (stD (fig1 k) (D k (k - m) 0)) := by
  intro m
  induction m with
  | zero => intro _; rw [Nat.sub_zero, D_top, init_eq_stD]
  | succ m ih =>
    intro hm
    have h1 := reach_c k (k - m) (by omega) (by omega) _ le_rfl
    rw [D_next k (k - m) (by omega), show k - m - 1 = k - (m + 1) by omega] at h1
    exact (ih (by omega)).trans h1

lemma choosable_fig1 : Choosable (fig1 k) (fig1F₁ k) := by
  refine ⟨_, by simpa using reach_all k k le_rfl, ?_, D_bot k⟩
  unfold Halts stD; simp only
  rw [sdiff_eq_empty_iff_subset]; intro x _; rw [mem_U]; left; exact Nat.zero_le _

lemma F0_mem : fig1F₀ k ∈ subcovers (fig1 k) := by
  unfold subcovers; rw [mem_filter, mem_powerset]
  refine ⟨fun A hA => ?_, ?_⟩
  · unfold fig1F₀ at hA; obtain ⟨q, _, rfl⟩ := mem_image.1 hA
    unfold family; exact mem_image.2 ⟨.inl q, mem_univ _, rfl⟩
  · rw [ground_fig1]; ext x; simp only [mem_biUnion, mem_univ, iff_true, id]
    exact ⟨_, mem_image.2 ⟨x.2, mem_univ _, rfl⟩, by simp [fig1]⟩

lemma opt_fig1 (hk : 1 ≤ k) : opt (fig1 k) = k.factorial := by
  apply le_antisymm
  · refine (inf'_le _ (F0_mem k)).trans ?_
    unfold fig1F₀; exact card_image_le.trans (by simp)
  · apply le_inf'
    intro F' hF'
    unfold subcovers at hF'; rw [mem_filter, mem_powerset, ground_fig1] at hF'
    obtain ⟨hsub, hcov⟩ := hF'
    have h1 : (univ : Finset (Fig1Point k)).card ≤ ∑ A ∈ F', A.card := by
      rw [← hcov]; exact card_biUnion_le
    have h2 : ∑ A ∈ F', A.card ≤ F'.card * k := by
      rw [← smul_eq_mul, ← sum_const]
      apply sum_le_sum; intro A hA
      have := hsub hA; unfold family at this; obtain ⟨i, _, rfl⟩ := mem_image.1 this
      exact inSC_fig1 k i
    simp only [card_univ, Fintype.card_prod, Fintype.card_fin] at h1
    have : k * k.factorial ≤ k * F'.card := by linarith [mul_comm F'.card k]
    exact Nat.le_of_mul_le_mul_left this (by omega)

lemma F1_card : ((fig1F₁ k).card : ℚ) = k.factorial * harmonic k := by
  have hinj : Function.Injective
      (fun i : (Σ s : Fin k, Fin (k.factorial / (s.val + 1))) => fig1 k (Sum.inr i)) := by
    rintro ⟨t, b⟩ ⟨t', b'⟩ h
    have hlt := cu_lt k (t.val + 1) b.val b.2 0 (by omega)
    have hp : ((t, ⟨b.val * (t.val + 1) + 0, hlt⟩) : Fig1Point k) ∈ fig1 k (.inr ⟨t, b⟩) := by
      simp only [fig1, mem_filter, mem_univ, true_and, Fin.val_mk]
      first | exact ⟨rfl, cu_div _ _ _ (by omega)⟩ | exact cu_div _ _ _ (by omega)
    simp only at h
    rw [h] at hp
    simp only [fig1, mem_filter, mem_univ, true_and, Fin.val_mk] at hp
    obtain ⟨rfl, hb⟩ := hp
    rw [cu_div _ _ _ (by omega)] at hb
    rw [Sigma.mk.inj_iff]; exact ⟨rfl, heq_of_eq (Fin.ext hb)⟩
  unfold fig1F₁
  rw [card_image_of_injective _ hinj, card_univ, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  push_cast
  rw [Fin.sum_univ_eq_sum_range (fun s => ((k.factorial / (s + 1) : ℕ) : ℚ)), harmonic, mul_sum]
  apply sum_congr rfl; intro s hs
  rw [mem_range] at hs
  rw [Nat.cast_div (Nat.dvd_factorial (by omega) hs) (by positivity)]
  push_cast; ring

theorem fig1_run (hk : 1 ≤ k) :
    InSC k (fig1 k) ∧ fig1F₀ k ∈ subcovers (fig1 k) ∧ opt (fig1 k) = k.factorial ∧
      Choosable (fig1 k) (fig1F₁ k) ∧
      ((fig1F₁ k).card : ℚ) = k.factorial * harmonic k :=
  ⟨inSC_fig1 k, F0_mem k, opt_fig1 k hk, choosable_fig1 k, F1_card k⟩

theorem greedy_setCover_ratio_harmonic (k : ℕ) (hk : 1 ≤ k) :
    (∀ {ι α : Type} [Fintype ι] [DecidableEq α] (S : ι → Finset α), InSC k S →
        ∀ F₁ : Finset (Finset α), Choosable S F₁ → (F₁.card : ℚ) ≤ harmonic k * opt S) ∧
      (∃ (ι α : Type) (_ : Fintype ι) (_ : DecidableEq α) (S : ι → Finset α), InSC k S ∧
        ∃ F₁ : Finset (Finset α), Choosable S F₁ ∧ 0 < opt S ∧
          (F₁.card : ℚ) = harmonic k * opt S) := by
  refine ⟨fun S hS F₁ hc => upper_bound k S hS F₁ hc, ?_⟩
  obtain ⟨h1, _, h3, h4, h5⟩ := fig1_run k hk
  refine ⟨Fig1Index k, Fig1Point k, inferInstance, inferInstance, fig1 k, h1, fig1F₁ k, h4, ?_, ?_⟩
  · rw [h3]; exact Nat.factorial_pos k
  · rw [h5, h3]; ring

end JohnsonApprox.SetCover

open JohnsonApprox.SetCover

theorem solution (k : ℕ) (hk : 1 ≤ k) :
    (∀ {ι α : Type} [Fintype ι] [DecidableEq α] (S : ι → Finset α), InSC k S →
        ∀ F₁ : Finset (Finset α), Choosable S F₁ → (F₁.card : ℚ) ≤ harmonic k * opt S) ∧
      (∃ (ι α : Type) (_ : Fintype ι) (_ : DecidableEq α) (S : ι → Finset α), InSC k S ∧
        ∃ F₁ : Finset (Finset α), Choosable S F₁ ∧ 0 < opt S ∧
          (F₁.card : ℚ) = harmonic k * opt S) := by
  exact JohnsonApprox.SetCover.greedy_setCover_ratio_harmonic k hk
