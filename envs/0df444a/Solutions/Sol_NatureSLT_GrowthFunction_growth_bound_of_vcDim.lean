-- Prove2me | solution 1 for NatureSLT.GrowthFunction.growth_bound_of_vcDim
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:07:18.102311+00:00
-- url     : https://prove2.me/submissions/e876fbfb-b85c-404d-81fa-1587b558c5fd

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_growthFunction
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
open NatureSLT.GrowthFunction

open Classical in
theorem g69w_numSep_le_sum {Z Λ : Type*} (Q : Λ → Z → Bool) (h : ℕ)
    (hsh : ∀ (k : ℕ) (w : Fin k → Z), Shatters Q w → k ≤ h) {ℓ : ℕ} (z : Fin ℓ → Z) :
    numSeparations Q z ≤ ∑ k ∈ Finset.Iic h, ℓ.choose k := by
  set 𝒜 : Finset (Finset (Fin ℓ)) :=
    Finset.univ.filter (fun s => ∃ α, ∀ i, i ∈ s ↔ Q α (z i) = true) with h𝒜
  have h1 : numSeparations Q z ≤ 𝒜.card := by
    unfold numSeparations
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn (fun f => Finset.univ.filter (fun i => f i = true)) ?_ ?_
    · rintro _ ⟨α, rfl⟩
      simp only [h𝒜, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      exact ⟨α, fun i => by simp⟩
    · intro f _ g _ hfg
      funext i
      have := congrArg (fun s => i ∈ s) hfg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
      cases hf : f i <;> cases hg : g i <;> simp_all
  have hvc : 𝒜.vcDim ≤ h := by
    unfold Finset.vcDim
    refine Finset.sup_le fun s hs => ?_
    rw [Finset.mem_shatterer] at hs
    set g := s.orderEmbOfFin rfl
    apply hsh s.card (fun m => z (g m))
    intro δ
    set t := (Finset.univ.filter (fun m => δ m = true)).map g.toEmbedding
    have hts : t ⊆ s := by
      intro x hx
      simp only [t, Finset.mem_map, Finset.mem_filter] at hx
      obtain ⟨m, _, rfl⟩ := hx
      exact s.orderEmbOfFin_mem rfl m
    obtain ⟨u, hu, hsu⟩ := hs hts
    simp only [h𝒜, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    obtain ⟨α, hα⟩ := hu
    refine ⟨α, fun m => ?_⟩
    have hmem : g m ∈ t ↔ δ m = true := by
      simp only [t, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨m', hm', he⟩
        have : m' = m := g.injective he
        rw [← this]; exact hm'
      · intro hm; exact ⟨m, hm, rfl⟩
    have hgs : g m ∈ s := s.orderEmbOfFin_mem rfl m
    rw [← hsu, Finset.mem_inter, hα] at hmem
    have := hmem
    cases hq : Q α (z (g m)) <;> cases hd : δ m <;> simp_all
  calc numSeparations Q z ≤ 𝒜.card := h1
    _ ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer 𝒜
    _ ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, (Fintype.card (Fin ℓ)).choose k :=
        Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ k ∈ Finset.Iic h, ℓ.choose k := by
        rw [Fintype.card_fin]
        exact Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.mpr hvc)

theorem g69w_sum_choose_le (h ℓ : ℕ) (hh : 0 < h) (hl : h ≤ ℓ) :
    ((∑ k ∈ Finset.Iic h, ℓ.choose k : ℕ) : ℝ) ≤ Real.exp h * ((ℓ : ℝ) / h) ^ h := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hl' : (0 : ℝ) < ℓ := by exact_mod_cast (lt_of_lt_of_le hh hl)
  set x : ℝ := (h : ℝ) / ℓ with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one hl']; exact_mod_cast hl
  have key : x ^ h * ((∑ k ∈ Finset.Iic h, ℓ.choose k : ℕ) : ℝ) ≤ Real.exp h := by
    push_cast
    rw [Finset.mul_sum]
    calc ∑ k ∈ Finset.Iic h, x ^ h * (ℓ.choose k : ℝ)
        ≤ ∑ k ∈ Finset.range (ℓ + 1), x ^ k * 1 ^ (ℓ - k) * (ℓ.choose k : ℝ) := by
          refine le_trans (Finset.sum_le_sum fun k hk => ?_)
            (Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => x ^ k * 1 ^ (ℓ - k) *
              (ℓ.choose k : ℝ)) (s := Finset.Iic h) ?_ ?_)
          · rw [Finset.mem_Iic] at hk
            simp only [one_pow, mul_one]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hx0.le hx1 hk) (by positivity)
          · intro k hk; simp only [Finset.mem_Iic] at hk; simp only [Finset.mem_range]; omega
          · intro k _ _; positivity
      _ = (x + 1) ^ ℓ := (add_pow x 1 ℓ).symm
      _ ≤ Real.exp x ^ ℓ := by
          apply pow_le_pow_left₀ (by positivity)
          linarith [Real.add_one_le_exp x]
      _ = Real.exp h := by
          rw [← Real.exp_nat_mul, hx]; congr 1; field_simp
  have hxh : 0 < x ^ h := by positivity
  have e : Real.exp h * ((ℓ : ℝ) / h) ^ h = Real.exp h / x ^ h := by
    rw [hx, div_pow, div_pow, div_div_eq_mul_div, mul_div_assoc]
  rw [e, le_div_iff₀ hxh, mul_comm]
  exact key

theorem solution {Z Λ : Type*} [Nonempty Z] [Nonempty Λ] (Q : Λ → Z → Bool)
    (h : ℕ) (hvc : vcDim Q = (h : ℕ∞)) :
    ∀ ℓ : ℕ, h < ℓ →
      growthFunction Q ℓ ≤ (h : ℝ) * (Real.log ((ℓ : ℝ) / (h : ℝ)) + 1) := by
  intro ℓ hl
  have hsh : ∀ (k : ℕ) (w : Fin k → Z), Shatters Q w → k ≤ h := by
    intro k w hw
    have : (k : ℕ∞) ≤ vcDim Q :=
      le_iSup₂_of_le (f := fun (k : ℕ) (_ : ∃ z : Fin k → Z, Shatters Q z) => (k : ℕ∞)) k
        ⟨w, hw⟩ le_rfl
    rw [hvc] at this; exact_mod_cast this
  have hmax : maxSeparations Q ℓ ≤ ∑ k ∈ Finset.Iic h, ℓ.choose k := by
    unfold maxSeparations
    exact ciSup_le fun z => g69w_numSep_le_sum Q h hsh z
  unfold growthFunction
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp only [Finset.Iic_eq_Icc, bot_eq_zero', Finset.Icc_self, Finset.sum_singleton,
      Nat.choose_zero_right] at hmax
    simp only [Nat.cast_zero, zero_mul]
    exact Real.log_nonpos (by positivity) (by exact_mod_cast hmax)
  · have hl' : (0 : ℝ) < ℓ := by exact_mod_cast (lt_trans hh hl)
    have hh' : (0 : ℝ) < h := by exact_mod_cast hh
    rcases Nat.eq_zero_or_pos (maxSeparations Q ℓ) with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      have : 0 ≤ Real.log ((ℓ : ℝ) / h) :=
        Real.log_nonneg (by rw [le_div_iff₀ hh']; simp; exact_mod_cast hl.le)
      positivity
    · have hb := g69w_sum_choose_le h ℓ hh hl.le
      have hm : (maxSeparations Q ℓ : ℝ) ≤ Real.exp h * ((ℓ : ℝ) / h) ^ h :=
        le_trans (by exact_mod_cast hmax) hb
      have := Real.log_le_log (by exact_mod_cast hpos) hm
      rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_pow] at this
      linarith
