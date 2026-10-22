-- Prove2me | solution 1 for NatureSLT.GrowthFunction.growth_function_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:40:25.835167+00:00
-- url     : https://prove2.me/submissions/c393a635-f39b-447a-b0d0-af7d638f7914

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_growthFunction
open NatureSLT.GrowthFunction
def g70slt_Sh {Z Λ : Type*} (Q : Λ → Z → Bool) {h : ℕ} (z : Fin h → Z) : Prop :=
  ∀ δ : Fin h → Bool, ∃ α : Λ, ∀ i : Fin h, Q α (z i) = δ i

open Classical in
theorem g69w_numSep_le_sum {Z Λ : Type*} (Q : Λ → Z → Bool) (h : ℕ)
    (hsh : ∀ (k : ℕ) (w : Fin k → Z), g70slt_Sh Q w → k ≤ h) {ℓ : ℕ} (z : Fin ℓ → Z) :
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

theorem g70slt_bound {Z Λ : Type*} [Nonempty Z] [Nonempty Λ] (Q : Λ → Z → Bool)
    (h : ℕ) (hsh : ∀ (k : ℕ) (w : Fin k → Z), g70slt_Sh Q w → k ≤ h) :
    ∀ ℓ : ℕ, h < ℓ →
      growthFunction Q ℓ ≤ (h : ℝ) * (Real.log ((ℓ : ℝ) / (h : ℝ)) + 1) := by
  intro ℓ hl
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

theorem g70slt_card_univ (ℓ : ℕ) : (Set.univ : Set (Fin ℓ → Bool)).ncard = 2 ^ ℓ := by
  rw [Set.ncard_univ, Nat.card_eq_fintype_card]; simp

theorem g70slt_numSep_le {Z Λ : Type*} (Q : Λ → Z → Bool) {ℓ : ℕ} (z : Fin ℓ → Z) :
    numSeparations Q z ≤ 2 ^ ℓ := by
  rw [← g70slt_card_univ]; exact Set.ncard_le_ncard (Set.subset_univ _)

theorem g70slt_numSep_pos {Z Λ : Type*} [Nonempty Λ] (Q : Λ → Z → Bool) {ℓ : ℕ}
    (z : Fin ℓ → Z) : 1 ≤ numSeparations Q z :=
  Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos (Set.toFinite _)).mpr (Set.range_nonempty _)).ne'

theorem g70slt_shatters_iff {Z Λ : Type*} (Q : Λ → Z → Bool) {ℓ : ℕ} (z : Fin ℓ → Z) :
    g70slt_Sh Q z ↔ numSeparations Q z = 2 ^ ℓ := by
  constructor
  · intro hs
    have : (Set.range fun α : Λ => fun i : Fin ℓ => Q α (z i)) = Set.univ :=
      Set.eq_univ_of_forall (fun δ => let ⟨α, hα⟩ := hs δ; ⟨α, funext hα⟩)
    unfold numSeparations; rw [this, g70slt_card_univ]
  · intro h δ
    have : (Set.range fun α : Λ => fun i : Fin ℓ => Q α (z i)) = Set.univ :=
      Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by rw [g70slt_card_univ, ← h]; rfl)
    have hm : δ ∈ Set.range fun α : Λ => fun i : Fin ℓ => Q α (z i) := by rw [this]; trivial
    obtain ⟨α, hα⟩ := hm
    exact ⟨α, fun i => congrFun hα i⟩

theorem g70slt_bdd {Z Λ : Type*} (Q : Λ → Z → Bool) (ℓ : ℕ) :
    BddAbove (Set.range fun z : Fin ℓ → Z => numSeparations Q z) :=
  ⟨2 ^ ℓ, by rintro _ ⟨z, rfl⟩; exact g70slt_numSep_le Q z⟩

theorem g70slt_max_mem {Z Λ : Type*} [Nonempty Z] (Q : Λ → Z → Bool) (ℓ : ℕ) :
    ∃ z : Fin ℓ → Z, maxSeparations Q ℓ = numSeparations Q z := by
  obtain ⟨z, hz⟩ := Nat.sSup_mem (Set.range_nonempty _) (g70slt_bdd Q ℓ)
  exact ⟨z, hz.symm⟩

theorem g70slt_le_max {Z Λ : Type*} (Q : Λ → Z → Bool) {ℓ : ℕ} (z : Fin ℓ → Z) :
    numSeparations Q z ≤ maxSeparations Q ℓ := le_ciSup (g70slt_bdd Q ℓ) z


/-- **Theorem 3.3** (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §3.5, p. 79).
Any growth function either satisfies `G^Λ(ℓ) = ℓ ln 2` (for every `ℓ`), or there is an integer
`h` with `G^Λ(h) = h ln 2` and `G^Λ(h + 1) < (h + 1) ln 2` such that
`G^Λ(ℓ) ≤ h (ln (ℓ / h) + 1)`. The bound is stated for `ℓ > h`, the range the book gives in both
of its restatements (the display after the Definition on p. 79 and (3.23) on p. 83). The `h`
is unique. At `h = 0` the right-hand side is `0` (Lean's `ℓ / 0 = 0`, `ln 0 = 0`), the limit of
`h (ln(ℓ/h) + 1)` as `h → 0⁺`. -/
theorem solution {Z Λ : Type*} [Nonempty Z] [Nonempty Λ] (Q : Λ → Z → Bool) :
    (∀ ℓ : ℕ, growthFunction Q ℓ = (ℓ : ℝ) * Real.log 2) ∨
    (∃ h : ℕ, growthFunction Q h = (h : ℝ) * Real.log 2 ∧
      growthFunction Q (h + 1) < ((h + 1 : ℕ) : ℝ) * Real.log 2 ∧
      ∀ ℓ : ℕ, h < ℓ →
        growthFunction Q ℓ ≤ (h : ℝ) * (Real.log ((ℓ : ℝ) / (h : ℝ)) + 1)) := by
  classical
  have hGsh : ∀ ℓ (z : Fin ℓ → Z), g70slt_Sh Q z → growthFunction Q ℓ = (ℓ : ℝ) * Real.log 2 := by
    intro ℓ z hz
    obtain ⟨z', hz'⟩ := g70slt_max_mem Q ℓ
    have : maxSeparations Q ℓ = 2 ^ ℓ := le_antisymm (hz' ▸ g70slt_numSep_le Q z')
      (by rw [← (g70slt_shatters_iff Q z).mp hz]; exact g70slt_le_max Q z)
    unfold growthFunction; rw [this]; push_cast; rw [Real.log_pow]
  by_cases hall : ∀ ℓ : ℕ, ∃ z : Fin ℓ → Z, g70slt_Sh Q z
  · left; intro ℓ; obtain ⟨z, hz⟩ := hall ℓ; exact hGsh ℓ z hz
  · right
    push Not at hall
    have hex : ∃ ℓ : ℕ, ∀ z : Fin ℓ → Z, ¬ g70slt_Sh Q z := hall
    have hspec := Nat.find_spec hex
    have hm0 : Nat.find hex ≠ 0 := by
      intro h0
      rw [h0] at hspec
      exact hspec Fin.elim0 (fun δ => ⟨Classical.arbitrary Λ, fun i => i.elim0⟩)
    obtain ⟨h, hm⟩ : ∃ h, Nat.find hex = h + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hPh : ∃ z : Fin h → Z, g70slt_Sh Q z := by
      have := Nat.find_min hex (show h < Nat.find hex by omega)
      push Not at this; exact this
    rw [hm] at hspec
    have hsh : ∀ (k : ℕ) (w : Fin k → Z), g70slt_Sh Q w → k ≤ h := by
      intro k w hw
      by_contra hk
      push Not at hk
      apply hspec (fun i => w (Fin.castLE hk i))
      intro δ
      obtain ⟨α, hα⟩ := hw (fun j => if hj : j.val < h + 1 then δ ⟨j, hj⟩ else false)
      exact ⟨α, fun i => by
        show Q α (w (Fin.castLE hk i)) = δ i
        rw [hα (Fin.castLE hk i), dif_pos (by simp; omega)]
        rfl⟩
    obtain ⟨z0, hz0⟩ := hPh
    refine ⟨h, hGsh h z0 hz0, ?_, g70slt_bound Q h hsh⟩
    obtain ⟨z, hz⟩ := g70slt_max_mem Q (h + 1)
    have hlt : numSeparations Q z < 2 ^ (h + 1) :=
      lt_of_le_of_ne (g70slt_numSep_le Q z) (fun e => hspec z ((g70slt_shatters_iff Q z).mpr e))
    unfold growthFunction
    rw [hz, show ((h + 1 : ℕ) : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ (h + 1)) by
      rw [Real.log_pow]]
    exact Real.log_lt_log (by exact_mod_cast g70slt_numSep_pos Q z) (by exact_mod_cast hlt)

