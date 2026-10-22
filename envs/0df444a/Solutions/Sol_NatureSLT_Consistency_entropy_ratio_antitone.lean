-- Prove2me | solution 1 for NatureSLT.Consistency.entropy_ratio_antitone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T17:11:31.156578+00:00
-- url     : https://prove2.me/submissions/55e39824-6357-45c9-842f-3df232481929

import Mathlib
import Definitions.Def_NatureSLT_Consistency_indicatorEntropy

open Finset

lemma g71m_holder {ι κ : Type*} (s : Finset ι) (t : Finset κ) (ht : t.Nonempty)
    (g : κ → ι → ℝ) (hg : ∀ i c, 0 ≤ g i c) :
    ∑ c ∈ s, ∏ i ∈ t, g i c ^ ((1 : ℝ) / t.card) ≤
      ∏ i ∈ t, (∑ c ∈ s, g i c) ^ ((1 : ℝ) / t.card) := by
  have hK : (0 : ℝ) < t.card := by exact_mod_cast ht.card_pos
  set S : κ → ℝ := fun i => ∑ c ∈ s, g i c with hS
  have hS0 : ∀ i, 0 ≤ S i := fun i => Finset.sum_nonneg fun c _ => hg i c
  by_cases hz : ∃ i ∈ t, S i = 0
  · obtain ⟨i0, hi0, h0⟩ := hz
    have hgi : ∀ c ∈ s, g i0 c = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun c _ => hg i0 c).mp h0
    have : ∑ c ∈ s, ∏ i ∈ t, g i c ^ ((1 : ℝ) / t.card) = 0 := by
      refine Finset.sum_eq_zero fun c hc => Finset.prod_eq_zero hi0 ?_
      rw [hgi c hc, Real.zero_rpow (by positivity)]
    rw [this]
    exact Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hS0 i) _
  push Not at hz
  have hSpos : ∀ i ∈ t, 0 < S i := fun i hi => lt_of_le_of_ne (hS0 i) (Ne.symm (hz i hi))
  have hP : 0 < ∏ i ∈ t, S i ^ ((1 : ℝ) / t.card) :=
    Finset.prod_pos fun i hi => Real.rpow_pos_of_pos (hSpos i hi) _
  have key : ∀ c, ∏ i ∈ t, (g i c / S i) ^ ((1 : ℝ) / t.card) ≤
      ∑ i ∈ t, ((1 : ℝ) / t.card) * (g i c / S i) := by
    intro c
    refine Real.geom_mean_le_arith_mean_weighted t (fun _ => (1 : ℝ) / t.card) (fun i => g i c / S i)
      (fun i _ => by positivity) ?_ (fun i hi => div_nonneg (hg i c) (hS0 i))
    rw [Finset.sum_const, nsmul_eq_mul]; field_simp
  have hsplit : ∀ c, ∏ i ∈ t, (g i c / S i) ^ ((1 : ℝ) / t.card) =
      (∏ i ∈ t, g i c ^ ((1 : ℝ) / t.card)) / ∏ i ∈ t, S i ^ ((1 : ℝ) / t.card) := by
    intro c
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Real.div_rpow (hg i c) (hS0 i)]
  have hsum : ∑ c ∈ s, ∑ i ∈ t, ((1 : ℝ) / t.card) * (g i c / S i) = 1 := by
    rw [Finset.sum_comm]
    have : ∀ i ∈ t, ∑ c ∈ s, ((1 : ℝ) / t.card) * (g i c / S i) = (1 : ℝ) / t.card := by
      intro i hi
      rw [← Finset.mul_sum, ← Finset.sum_div]
      rw [show ∑ c ∈ s, g i c = S i from rfl, div_self (hSpos i hi).ne', mul_one]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]; field_simp
  have : (∑ c ∈ s, ∏ i ∈ t, g i c ^ ((1 : ℝ) / t.card)) / ∏ i ∈ t, S i ^ ((1 : ℝ) / t.card) ≤ 1 := by
    rw [Finset.sum_div]
    refine le_trans ?_ hsum.le
    refine Finset.sum_le_sum fun c _ => ?_
    rw [← hsplit]; exact key c
  rwa [div_le_one hP] at this

lemma g71m_sa_last {n : ℕ} (i : Fin (n + 1)) :
    (Fin.castSucc i).succAbove (Fin.last n) = Fin.last (n + 1) := by
  have := i.2
  ext; simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_last]
  split_ifs with h <;> simp_all <;> omega

lemma g71m_sa_cs {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    (Fin.castSucc i).succAbove (Fin.castSucc j) = Fin.castSucc (i.succAbove j) := by
  ext; simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]; split_ifs <;> simp

lemma g71m_real_step (n : ℕ) {ι : Type*} (C : Finset ι) (f : ι → ℝ) (g : ι → Fin (n + 2) → ℝ)
    (L : ℝ) (P : Fin (n + 2) → ℝ) (hL0' : 0 ≤ L) (hf0 : ∀ c, 0 ≤ f c) (hg0 : ∀ c i, 0 ≤ g c i)
    (h2 : ∀ c, f c ≤ L) (h3 : ∀ i, ∑ c ∈ C, g c i ≤ P i)
    (h4 : ∀ c, f c ^ (n + 1) ≤ ∏ i, g c i) :
    (∑ c ∈ C, f c) ^ (n + 2) ≤ L * ∏ i, P i := by
  have hKpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have hP0 : ∀ i, 0 ≤ P i := fun i => (Finset.sum_nonneg fun c _ => hg0 c i).trans (h3 i)
  rcases C.eq_empty_or_nonempty with hCe | ⟨c0, _⟩
  · rw [hCe, Finset.sum_empty, zero_pow (by omega)]
    exact mul_nonneg hL0' (Finset.prod_nonneg fun i _ => hP0 i)
  set e : ℝ := ((n + 2 : ℕ) : ℝ)⁻¹ with he
  have hcard : (1 : ℝ) / ((Finset.univ : Finset (Fin (n + 2))).card : ℝ) = e := by simp [he]
  have hfc : ∀ c, f c ≤ L ^ e * ∏ i, g c i ^ e := by
    intro c
    have hsplit : f c = f c ^ e * (f c ^ (n + 1)) ^ e := by
      rw [← Real.mul_rpow (hf0 c) (pow_nonneg (hf0 c) _), ← pow_succ', he,
        Real.pow_rpow_inv_natCast (hf0 c) (by omega)]
    rw [hsplit]
    refine mul_le_mul (Real.rpow_le_rpow (hf0 c) (h2 c) (by positivity)) ?_
      (Real.rpow_nonneg (pow_nonneg (hf0 c) _) _) (Real.rpow_nonneg hL0' _)
    rw [Real.finsetProd_rpow _ _ (fun i _ => hg0 c i)]
    exact Real.rpow_le_rpow (pow_nonneg (hf0 c) _) (h4 c) (by positivity)
  have hsum : ∑ c ∈ C, f c ≤ L ^ e * ∏ i, P i ^ e := by
    calc ∑ c ∈ C, f c ≤ ∑ c ∈ C, L ^ e * ∏ i, g c i ^ e := Finset.sum_le_sum fun c _ => hfc c
      _ = L ^ e * ∑ c ∈ C, ∏ i, g c i ^ e := by rw [Finset.mul_sum]
      _ ≤ L ^ e * ∏ i, (∑ c ∈ C, g c i) ^ e := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hL0' _)
          have := g71m_holder C (Finset.univ : Finset (Fin (n + 2))) Finset.univ_nonempty
            (fun i c => g c i) (fun i c => hg0 c i)
          rw [hcard] at this
          exact this
      _ ≤ L ^ e * ∏ i, P i ^ e := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hL0' _)
          refine Finset.prod_le_prod (fun i _ => Real.rpow_nonneg
            (Finset.sum_nonneg fun c _ => hg0 c i) _) fun i _ => ?_
          exact Real.rpow_le_rpow (Finset.sum_nonneg fun c _ => hg0 c i) (h3 i) (by positivity)
  have hb : L ^ e * ∏ i, P i ^ e = (L * ∏ i, P i) ^ e := by
    rw [Real.mul_rpow hL0' (Finset.prod_nonneg fun i _ => hP0 i),
      Real.finsetProd_rpow _ _ (fun i _ => hP0 i)]
  rw [hb] at hsum
  calc (∑ c ∈ C, f c) ^ (n + 2) ≤ ((L * ∏ i, P i) ^ e) ^ (n + 2) :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun c _ => hf0 c) hsum (n + 2)
    _ = L * ∏ i, P i := by
        rw [he]
        exact Real.rpow_inv_natCast_pow (mul_nonneg hL0' (Finset.prod_nonneg fun i _ => hP0 i))
          (by omega)

theorem g71m_lw {X : Type*} [DecidableEq X] (n : ℕ) (A : Finset (Fin (n + 2) → X)) :
    (A.card : ℝ) ^ (n + 1) ≤
      ∏ i : Fin (n + 2), ((A.image fun x => x ∘ i.succAbove).card : ℝ) := by
  induction n with
  | zero =>
    rw [Fin.prod_univ_two, pow_one, ← Nat.cast_mul, Nat.cast_le, ← Finset.card_product]
    refine Finset.card_le_card_of_injOn (fun x => (x ∘ (0 : Fin 2).succAbove, x ∘ (1 : Fin 2).succAbove))
      (fun x hx => ?_) ?_
    · simp only [coe_product, Set.mem_prod, mem_coe, mem_image]
      exact ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
    · intro x _ y _ hxy
      simp only [Prod.mk.injEq] at hxy
      funext k
      fin_cases k
      · have := congrFun hxy.2 0; simpa using this
      · have := congrFun hxy.1 0; simpa using this
  | succ n ih =>
    set C := A.image (fun x => x (Fin.last (n + 2))) with hC
    set F : X → Finset (Fin (n + 2) → X) :=
      fun c => (A.filter (fun x => x (Fin.last (n + 2)) = c)).image Fin.init with hF
    set L : ℕ := (A.image fun x => x ∘ (Fin.last (n + 2)).succAbove).card with hL
    set P : Fin (n + 2) → ℕ :=
      fun i => (A.image fun x => x ∘ (Fin.castSucc i).succAbove).card with hP
    -- (1)
    have h1 : A.card = ∑ c ∈ C, (F c).card := by
      rw [Finset.card_eq_sum_card_image (fun x => x (Fin.last (n + 2))) A]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hF, Finset.card_image_of_injOn]
      intro x hx y hy hxy
      simp only [coe_filter, Set.mem_ofPred_eq] at hx hy
      rw [← Fin.snoc_init_self x, ← Fin.snoc_init_self y, hx.2, hy.2]
      rw [hxy]
    -- (2)
    have h2 : ∀ c, (F c).card ≤ L := by
      intro c
      refine Finset.card_le_card ?_
      intro y hy
      simp only [hF, mem_image, mem_filter] at hy
      obtain ⟨x, ⟨hx, _⟩, rfl⟩ := hy
      simp only [mem_image]
      refine ⟨x, hx, ?_⟩
      funext k
      simp [Fin.init]
    -- (3)
    have h3 : ∀ i : Fin (n + 2),
        ∑ c ∈ C, ((F c).image fun y => y ∘ i.succAbove).card ≤ P i := by
      intro i
      rw [← Finset.card_sigma]
      refine Finset.card_le_card_of_injOn
        (fun p : (Σ _ : X, Fin (n + 1) → X) => Fin.snoc (α := fun _ => X) p.2 p.1) (fun p hp => ?_) ?_
      · simp only [mem_coe, mem_sigma, mem_image, hF, mem_filter] at hp
        obtain ⟨_, x', ⟨⟨x, ⟨hx, hxc⟩, rfl⟩, hx'⟩⟩ := hp
        simp only [mem_coe, mem_image]
        refine ⟨x, hx, ?_⟩
        funext k
        refine Fin.lastCases ?_ (fun j => ?_) k
        · simp only [Function.comp_apply, Fin.snoc_last]
          rw [g71m_sa_last, hxc]
        · simp only [Function.comp_apply, Fin.snoc_castSucc]
          rw [g71m_sa_cs, ← hx']
          simp [Fin.init]
      · intro p _ q _ hpq
        simp only at hpq
        have h := Fin.snoc_injective2 hpq
        exact Sigma.ext h.2 (heq_of_eq h.1)
    -- (4)
    have h4 : ∀ c, ((F c).card : ℝ) ^ (n + 1) ≤
        ∏ i : Fin (n + 2), (((F c).image fun y => y ∘ i.succAbove).card : ℝ) := fun c => ih (F c)
    have := g71m_real_step n C (fun c => ((F c).card : ℝ))
      (fun c i => (((F c).image fun y => y ∘ i.succAbove).card : ℝ)) (L : ℝ) (fun i => (P i : ℝ))
      (Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)
      (fun c => by exact_mod_cast h2 c) (fun i => by exact_mod_cast h3 i) h4
    rw [Fin.prod_univ_castSucc, mul_comm, h1, Nat.cast_sum]
    exact this

open MeasureTheory
open NatureSLT.Consistency

lemma g71m_fin {Z Λ : Type*} (Q : Λ → Z → ℝ) (hQ : ∀ α z, Q α z = 0 ∨ Q α z = 1) {ℓ : ℕ}
    (z : Fin ℓ → Z) : (Set.range fun α : Λ => fun i : Fin ℓ => Q α (z i)).Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin ℓ => ({0, 1} : Set ℝ))
    (fun _ => Set.toFinite _)).subset ?_
  rintro _ ⟨α, rfl⟩
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, forall_const]
  exact fun i => hQ α (z i)

lemma g71m_div_card {Z Λ : Type*} (Q : Λ → Z → ℝ) (hQ : ∀ α z, Q α z = 0 ∨ Q α z = 1) {ℓ : ℕ}
    (z : Fin ℓ → Z) : diversity Q z = (g71m_fin Q hQ z).toFinset.card := by
  unfold diversity
  rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset, Set.Finite.coe_toFinset]

lemma g71m_div_lw {Z Λ : Type*} (Q : Λ → Z → ℝ) (hQ : ∀ α z, Q α z = 0 ∨ Q α z = 1) (n : ℕ)
    (z : Fin (n + 2) → Z) :
    (diversity Q z : ℝ) ^ (n + 1) ≤
      ∏ i : Fin (n + 2), (diversity Q (fun j => z (i.succAbove j)) : ℝ) := by
  classical
  have h := g71m_lw n (g71m_fin Q hQ z).toFinset
  rw [g71m_div_card Q hQ z]
  refine h.trans_eq (Finset.prod_congr rfl fun i _ => ?_)
  rw [g71m_div_card Q hQ, ← Set.ncard_coe_finset, ← Set.ncard_coe_finset, Finset.coe_image,
    Set.Finite.coe_toFinset, Set.Finite.coe_toFinset, ← Set.range_comp]
  rfl

lemma g71m_div_le {Z Λ : Type*} (Q : Λ → Z → ℝ) (hQ : ∀ α z, Q α z = 0 ∨ Q α z = 1) {ℓ : ℕ}
    (z : Fin ℓ → Z) : diversity Q z ≤ 2 ^ ℓ := by
  classical
  unfold diversity
  have hfin := g71m_fin Q hQ z
  haveI := hfin.to_subtype
  calc Nat.card (Set.range fun α : Λ => fun i : Fin ℓ => Q α (z i))
      ≤ Nat.card (Fin ℓ → Bool) := by
        refine Nat.card_le_card_of_injective (fun v i => decide (v.1 i = 1)) ?_
        rintro ⟨v, α, rfl⟩ ⟨w, β, rfl⟩ hvw
        apply Subtype.ext
        funext i
        have := congrFun hvw i
        simp only [decide_eq_decide] at this
        rcases hQ α (z i) with h1 | h1 <;> rcases hQ β (z i) with h2 | h2 <;>
          simp_all
    _ = 2 ^ ℓ := by simp

lemma g71m_div_pos {Z Λ : Type*} [Nonempty Λ] (Q : Λ → Z → ℝ)
    (hQ : ∀ α z, Q α z = 0 ∨ Q α z = 1) {ℓ : ℕ} (z : Fin ℓ → Z) : 1 ≤ diversity Q z := by
  rw [g71m_div_card Q hQ z, Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero,
    Set.Finite.toFinset_eq_empty]
  exact Set.range_nonempty _ |>.ne_empty

lemma g71m_int {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    (Q : Λ → Z → ℝ) (hQ : ∀ α z, Q α z = 0 ∨ Q α z = 1) (ℓ : ℕ)
    (hN : Measurable (fun z : Fin ℓ → Z => (diversity Q z : ℝ))) :
    Integrable (fun z : Fin ℓ → Z => Real.log (diversity Q z : ℝ))
      (Measure.pi fun _ : Fin ℓ => F) := by
  refine Integrable.of_bound (hN.log.aestronglyMeasurable) (Real.log (2 ^ ℓ)) ?_
  refine Filter.Eventually.of_forall fun z => ?_
  rw [Real.norm_eq_abs]
  rcases Nat.eq_zero_or_pos (diversity Q z) with h0 | hpos
  · rw [h0]; simp; positivity
  rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hpos))]
  exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast g71m_div_le Q hQ z)

lemma g71m_marg {Z : Type*} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F] (n : ℕ)
    (i : Fin (n + 1)) :
    (Measure.pi fun _ : Fin (n + 1) => F).map (fun z => fun j => z (i.succAbove j)) =
      Measure.pi fun _ : Fin n => F := by
  have : (fun z : Fin (n + 1) → Z => fun j => z (i.succAbove j)) =
      Prod.snd ∘ (MeasurableEquiv.piFinSuccAbove (fun _ => Z) i) := rfl
  rw [this, ← Measure.map_map measurable_snd (MeasurableEquiv.measurable _),
    (measurePreserving_piFinSuccAbove (fun _ => F) i).map_eq, Measure.map_snd_prod,
    measure_univ, one_smul]

theorem solution {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z)
    [IsProbabilityMeasure F] (Q : Λ → Z → ℝ) (hQ : ∀ α z, Q α z = 0 ∨ Q α z = 1)
    (hN : ∀ ℓ : ℕ, Measurable (fun z : Fin ℓ → Z => (diversity Q z : ℝ))) :
    AntitoneOn (fun ℓ : ℕ => entropy F Q ℓ / (ℓ : ℝ)) (Set.Ici 1) := by
  rcases isEmpty_or_nonempty Λ with hΛ | hΛ
  · have h0 : ∀ ℓ, entropy F Q ℓ = 0 := by
      intro ℓ
      unfold entropy
      have : ∀ z : Fin ℓ → Z, diversity Q z = 0 := by
        intro z; unfold diversity; simp [Set.range_eq_empty]
      simp [this]
    intro a _ b _ _
    simp [h0]
  refine antitoneOn_nat_Ici_of_succ_le fun ℓ hℓ => ?_
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 1 := ⟨ℓ - 1, by simp at hℓ; omega⟩
  -- key: (n+1) H(n+2) ≤ (n+2) H(n+1)
  have hkey : ((n : ℝ) + 1) * entropy F Q (n + 2) ≤ ((n : ℝ) + 2) * entropy F Q (n + 1) := by
    have hpt : ∀ z : Fin (n + 2) → Z, ((n : ℝ) + 1) * Real.log (diversity Q z : ℝ) ≤
        ∑ i : Fin (n + 2), Real.log (diversity Q (fun j => z (i.succAbove j)) : ℝ) := by
      intro z
      have h := g71m_div_lw Q hQ n z
      have hpos : ∀ {m : ℕ} (w : Fin m → Z), (0 : ℝ) < diversity Q w := fun w => by
        exact_mod_cast g71m_div_pos Q hQ w
      have := Real.log_le_log (pow_pos (hpos z) _) h
      rw [Real.log_pow, Real.log_prod (fun i _ => (hpos _).ne')] at this
      push_cast at this
      exact this
    have hint := g71m_int F Q hQ (n + 2) (hN _)
    have hint' : ∀ i : Fin (n + 2), Integrable
        (fun z : Fin (n + 2) → Z => Real.log (diversity Q (fun j => z (i.succAbove j)) : ℝ))
        (Measure.pi fun _ : Fin (n + 2) => F) := by
      intro i
      have h := g71m_int F Q hQ (n + 1) (hN _)
      rw [← g71m_marg F (n + 1) i] at h
      exact h.comp_measurable (measurable_pi_lambda _ fun j => measurable_pi_apply _)
    have heq : ∀ i : Fin (n + 2), ∫ z, Real.log (diversity Q (fun j => z (i.succAbove j)) : ℝ)
        ∂(Measure.pi fun _ : Fin (n + 2) => F) = entropy F Q (n + 1) := by
      intro i
      unfold entropy
      rw [← g71m_marg F (n + 1) i, integral_map
        (measurable_pi_lambda _ fun j => measurable_pi_apply _).aemeasurable]
      rw [g71m_marg F (n + 1) i]
      exact (hN _).log.aestronglyMeasurable
    calc ((n : ℝ) + 1) * entropy F Q (n + 2)
        = ∫ z, ((n : ℝ) + 1) * Real.log (diversity Q z : ℝ)
            ∂(Measure.pi fun _ : Fin (n + 2) => F) := by
          unfold entropy; rw [integral_const_mul]
      _ ≤ ∫ z, ∑ i : Fin (n + 2), Real.log (diversity Q (fun j => z (i.succAbove j)) : ℝ)
            ∂(Measure.pi fun _ : Fin (n + 2) => F) :=
          integral_mono (hint.const_mul _) (integrable_finset_sum _ fun i _ => hint' i) hpt
      _ = ∑ i : Fin (n + 2), entropy F Q (n + 1) := by
          rw [integral_finset_sum _ fun i _ => hint' i]
          exact Finset.sum_congr rfl fun i _ => heq i
      _ = ((n : ℝ) + 2) * entropy F Q (n + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  show entropy F Q (n + 1 + 1) / ((n + 1 + 1 : ℕ) : ℝ) ≤ entropy F Q (n + 1) / ((n + 1 : ℕ) : ℝ)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  linarith
