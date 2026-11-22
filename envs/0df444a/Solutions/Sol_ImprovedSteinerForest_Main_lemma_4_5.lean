-- Prove2me | solution 1 for ImprovedSteinerForest.Main.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T20:30:24.135859+00:00
-- url     : https://prove2.me/submissions/dfe58c9b-c69e-4ddf-9601-e5a67233d151

import Mathlib

namespace L45

noncomputable def phi (u : ℕ) (b : ℝ) : ℝ := ∑ h ∈ Finset.Icc 1 u, b ^ h / (h : ℝ)

lemma phi_zero (b : ℝ) : phi 0 b = 0 := by simp [phi]

lemma phi_succ (u : ℕ) (b : ℝ) : phi (u + 1) b = phi u b + b ^ (u + 1) / ((u + 1 : ℕ) : ℝ) := by
  unfold phi
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma phi_at_zero (u : ℕ) : phi u 0 = 0 := by
  induction u with
  | zero => exact phi_zero 0
  | succ n ih => rw [phi_succ, ih]; simp

lemma pow_sub_pow_ge {b c : ℝ} (hc : 0 ≤ c) (hcb : c ≤ b) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * c ^ n * (b - c) ≤ b ^ (n + 1) - c ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : b ^ (n + 2) - c ^ (n + 2) = b * (b ^ (n + 1) - c ^ (n + 1)) + c ^ (n + 1) * (b - c) := by
      ring
    rw [h1]
    have hcn : 0 ≤ c ^ n := pow_nonneg hc n
    have hbc : 0 ≤ b - c := by linarith
    have h2 : c * (((n + 1 : ℕ) : ℝ) * c ^ n * (b - c)) ≤ b * (b ^ (n + 1) - c ^ (n + 1)) := by
      have h3 : 0 ≤ ((n + 1 : ℕ) : ℝ) * c ^ n * (b - c) := by positivity
      calc c * (((n + 1 : ℕ) : ℝ) * c ^ n * (b - c)) ≤ b * (((n + 1 : ℕ) : ℝ) * c ^ n * (b - c)) :=
            mul_le_mul_of_nonneg_right hcb h3
        _ ≤ b * (b ^ (n + 1) - c ^ (n + 1)) := mul_le_mul_of_nonneg_left ih (by linarith)
    push_cast at h2 ⊢
    have : c ^ (n + 1) = c * c ^ n := by ring
    rw [this]
    nlinarith

/-- (A) `φ_u(c) - φ_{u'}(c) ≥ (u - u') c^u / u`. -/
lemma phi_gap {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) {u : ℕ} (_hu : 1 ≤ u) (u' d : ℕ) (hd : u' + d ≤ u) :
    phi u' c + (d : ℝ) * (c ^ u / (u : ℝ)) ≤ phi (u' + d) c := by
  induction d with
  | zero => simp
  | succ d ih =>
    have ih := ih (by omega)
    rw [← add_assoc, phi_succ]
    have hle : c ^ u / (u : ℝ) ≤ c ^ (u' + d + 1) / ((u' + d + 1 : ℕ) : ℝ) := by
      have hpos : (0 : ℝ) < ((u' + d + 1 : ℕ) : ℝ) := by positivity
      have hle' : ((u' + d + 1 : ℕ) : ℝ) ≤ (u : ℝ) := by exact_mod_cast hd
      have hp : c ^ u ≤ c ^ (u' + d + 1) := pow_le_pow_of_le_one hc hc1 (by omega)
      calc c ^ u / (u : ℝ) ≤ c ^ u / ((u' + d + 1 : ℕ) : ℝ) :=
            div_le_div_of_nonneg_left (pow_nonneg hc _) hpos hle'
        _ ≤ _ := div_le_div_of_nonneg_right hp hpos.le
    push_cast at ih hle ⊢
    linarith

/-- (B) `φ_u(c) + β (1 - c^u) ≤ φ_u(β + (1 - β) c)`. -/
lemma phi_shift {β c : ℝ} (hβ : 0 < β) (_hβ1 : β ≤ 1) (hc : 0 ≤ c) (hc1 : c ≤ 1) (u : ℕ) :
    phi u c + β * (1 - c ^ u) ≤ phi u (β + (1 - β) * c) := by
  induction u with
  | zero => simp [phi_zero]
  | succ n ih =>
    rw [phi_succ, phi_succ]
    set b := β + (1 - β) * c
    have hcb : c ≤ b := by simp only [b]; nlinarith
    have key := pow_sub_pow_ge hc hcb n
    have hbc : b - c = β * (1 - c) := by simp only [b]; ring
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have h2 : β * c ^ n * (1 - c) ≤ (b ^ (n + 1) - c ^ (n + 1)) / ((n + 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hpos]
      rw [hbc] at key
      linarith
    have h3 : (b ^ (n + 1) - c ^ (n + 1)) / ((n + 1 : ℕ) : ℝ) =
        b ^ (n + 1) / ((n + 1 : ℕ) : ℝ) - c ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := sub_div _ _ _
    have h4 : c ^ (n + 1) = c ^ n * c := pow_succ c n
    rw [h3, h4] at h2
    rw [h4]
    nlinarith [ih, h2]

noncomputable def wt (c : ℝ) (u : ℕ) : ℝ := if u = 0 then 0 else c ^ u / (u : ℝ)

/-- (C) pointwise potential drop. -/
lemma pointwise {β c : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hc : 0 ≤ c) (hc1 : c ≤ 1) {u u' : ℕ}
    (h : u' ≤ u) :
    phi u' c + β * (if 1 ≤ u then 1 else 0) ≤
      phi u (β + (1 - β) * c) + wt c u * (β * u - ((u : ℝ) - u')) := by
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · have : u' = 0 := by omega
    subst this
    simp [wt, phi_zero]
  · have hA := phi_gap hc hc1 hu u' (u - u') (by omega)
    have hB := phi_shift hβ hβ1 hc hc1 u
    rw [show u' + (u - u') = u by omega] at hA
    have hu0 : u ≠ 0 := by omega
    have hupos : (0 : ℝ) < u := by exact_mod_cast hu
    simp only [wt, hu0, if_false, show 1 ≤ u from hu, if_true]
    have hcast : ((u - u' : ℕ) : ℝ) = (u : ℝ) - u' := by push_cast [Nat.cast_sub h]; ring
    rw [hcast] at hA
    have e : c ^ u / (u : ℝ) * (β * u - ((u : ℝ) - u')) =
        β * c ^ u - ((u : ℝ) - u') * (c ^ u / (u : ℝ)) := by
      field_simp
    rw [e]
    linarith

lemma min_toNat_eq (x : ℕ∞) (j : ℕ) :
    ((min x (j : ℕ∞)).toNat : ℝ) = ∑ r ∈ Finset.range j, (if (r : ℕ∞) < x then (1 : ℝ) else 0) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ← ih]
    induction x using ENat.recTopCoe with
    | top =>
      rw [min_eq_right le_top, min_eq_right le_top, ENat.toNat_natCast, ENat.toNat_natCast,
        if_pos (ENat.natCast_lt_top j)]
      push_cast; ring
    | coe n =>
      by_cases hj : j < n
      · have h1 : ((j + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast (show j + 1 ≤ n by omega)
        have h2 : ((j : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast hj.le
        have h3 : ((j : ℕ) : ℕ∞) < (n : ℕ∞) := by exact_mod_cast hj
        rw [min_eq_right h1, min_eq_right h2, ENat.toNat_natCast, ENat.toNat_natCast, if_pos h3]
        push_cast; ring
      · have h1 : (n : ℕ∞) ≤ ((j + 1 : ℕ) : ℕ∞) := by exact_mod_cast (show n ≤ j + 1 by omega)
        have h2 : (n : ℕ∞) ≤ ((j : ℕ) : ℕ∞) := by exact_mod_cast (show n ≤ j by omega)
        have h3 : ¬ ((j : ℕ) : ℕ∞) < (n : ℕ∞) := by exact_mod_cast hj
        rw [min_eq_left h1, min_eq_left h2, if_neg h3]
        simp

open MeasureTheory

/-- One-round marking bound against an `m`-measurable nonnegative weight. -/
lemma key {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (β : ℝ)
    (A B : Set Ω) (hA : MeasurableSet[m] A) (hB : MeasurableSet[mΩ] B)
    (hmark : ∀ᵐ ω ∂P, ω ∉ A → β ≤ condExp m P (B.indicator (fun _ => (1 : ℝ))) ω)
    (f : Ω → ℝ) (hf : StronglyMeasurable[m] f) (hf0 : ∀ ω, 0 ≤ f ω) (hfi : Integrable f P) :
    β * ∫ ω, Aᶜ.indicator f ω ∂P ≤ ∫ ω, B.indicator (Aᶜ.indicator f) ω ∂P := by
  set G := Aᶜ.indicator f with hGdef
  have hG : StronglyMeasurable[m] G := hf.indicator hA.compl
  have hGi : Integrable G P := hfi.indicator (hm _ hA.compl)
  have e : B.indicator G = G * B.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hω : ω ∈ B <;> simp [hω]
  have hIi : Integrable (B.indicator fun _ => (1 : ℝ)) P := (integrable_const (1 : ℝ)).indicator hB
  have hprod : Integrable (G * B.indicator fun _ => (1 : ℝ)) P := by
    rw [← e]; exact hGi.indicator hB
  have hce := condExp_mul_of_stronglyMeasurable_left hG hprod hIi
  have hint2 : Integrable (G * condExp m P (B.indicator fun _ => (1 : ℝ))) P :=
    (integrable_condExp).congr hce
  calc β * ∫ ω, G ω ∂P = ∫ ω, β * G ω ∂P := (integral_const_mul β _).symm
    _ ≤ ∫ ω, (G * condExp m P (B.indicator fun _ => (1 : ℝ))) ω ∂P := by
        apply integral_mono_ae (hGi.const_mul β) hint2
        filter_upwards [hmark] with ω hω
        by_cases hωA : ω ∈ A
        · simp [hGdef, hωA]
        · have h1 := hω hωA
          have h2 : G ω = f ω := by simp [hGdef, hωA]
          simp only [Pi.mul_apply, h2]
          nlinarith [hf0 ω]
    _ = ∫ ω, (condExp m P (G * B.indicator fun _ => (1 : ℝ))) ω ∂P :=
        integral_congr_ae hce.symm
    _ = ∫ ω, (G * B.indicator fun _ => (1 : ℝ)) ω ∂P := integral_condExp hm
    _ = ∫ ω, B.indicator G ω ∂P := by rw [e]

lemma integ_comp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (V : Ω → ℕ) (hV : Measurable V) (k : ℕ) (hVk : ∀ ω, V ω ≤ k) (g : ℕ → ℝ) :
    Integrable (fun ω => g (V ω)) P := by
  refine Integrable.of_bound ((measurable_from_nat.comp hV).aestronglyMeasurable)
    (∑ n ∈ Finset.range (k + 1), |g n|) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun n => |g n|) (fun n _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le (hVk ω)))

open scoped Classical in
/-- number of unmarked witnesses after `r` rounds -/
noncomputable def unm {Ω : Type*} {k : ℕ} (marked : Fin k → ℕ → Set Ω) (r : ℕ) (ω : Ω) : ℕ :=
  ∑ i, if ω ∈ marked i r then 0 else 1

lemma unm_le {Ω : Type*} {k : ℕ} (marked : Fin k → ℕ → Set Ω) (r : ℕ) (ω : Ω) :
    unm marked r ω ≤ k := by
  classical
  unfold unm
  calc (∑ i, if ω ∈ marked i r then 0 else 1) ≤ ∑ _i : Fin k, 1 := by
        apply Finset.sum_le_sum; intro i _; split_ifs <;> omega
    _ = k := by simp

open scoped Classical in
lemma unm_cast {Ω : Type*} {k : ℕ} (marked : Fin k → ℕ → Set Ω) (r : ℕ) (ω : Ω) :
    (unm marked r ω : ℝ) = ∑ i, if ω ∈ marked i r then (0 : ℝ) else 1 := by
  classical
  unfold unm
  push_cast
  apply Finset.sum_congr rfl; intro i _; split_ifs <;> simp

lemma unm_pos_iff {Ω : Type*} {k : ℕ} (marked : Fin k → ℕ → Set Ω) (r : ℕ) (ω : Ω) :
    1 ≤ unm marked r ω ↔ ∃ i, ω ∉ marked i r := by
  classical
  unfold unm
  rw [Nat.one_le_iff_ne_zero, Ne, Finset.sum_eq_zero_iff]
  simp

lemma unm_zero {Ω : Type*} {k : ℕ} (marked : Fin k → ℕ → Set Ω) (h0 : ∀ i, marked i 0 = ∅)
    (ω : Ω) : unm marked 0 ω = k := by
  classical
  unfold unm
  simp [h0]

lemma unm_meas {Ω : Type*} {k : ℕ} (marked : Fin k → ℕ → Set Ω) (r : ℕ) (m : MeasurableSpace Ω)
    (h : ∀ i, MeasurableSet[m] (marked i r)) : Measurable[m] (unm marked r) := by
  classical
  unfold unm
  exact Finset.measurable_sum _ (fun i _ => Measurable.ite (h i) measurable_const measurable_const)

lemma wt_nonneg {c : ℝ} (hc : 0 ≤ c) (u : ℕ) : 0 ≤ wt c u := by
  unfold wt; split_ifs
  · exact le_rfl
  · positivity

/-- Supermartingale step: `E φ_{U_{r+1}}(c) + β P(U_r ≥ 1) ≤ E φ_{U_r}(β + (1-β)c)`. -/
lemma step {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (k : ℕ) (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (marked : Fin k → ℕ → Set Ω)
    (hmono : ∀ i r, marked i r ⊆ marked i (r + 1))
    (hadapt : ∀ i r, MeasurableSet[ℱ r] (marked i r))
    (hmark : ∀ i r, ∀ᵐ ω ∂P, ω ∉ marked i r →
      β ≤ condExp (ℱ r) P ((marked i (r + 1)).indicator (fun _ => (1 : ℝ))) ω)
    (r : ℕ) (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    ∫ ω, phi (unm marked (r + 1) ω) c ∂P +
        β * ∫ ω, (if 1 ≤ unm marked r ω then (1 : ℝ) else 0) ∂P
      ≤ ∫ ω, phi (unm marked r ω) (β + (1 - β) * c) ∂P := by
  classical
  have hUr : Measurable[ℱ r] (unm marked r) := unm_meas _ r _ (fun i => hadapt i r)
  have hU : ∀ s, Measurable (unm marked s) := fun s =>
    (unm_meas _ s _ (fun i => hadapt i s)).mono (ℱ.le s) le_rfl
  set W : Ω → ℝ := fun ω => wt c (unm marked r ω) with hWdef
  have hWm : StronglyMeasurable[ℱ r] W :=
    ((measurable_from_nat (f := wt c)).comp hUr).stronglyMeasurable
  have hW0 : ∀ ω, 0 ≤ W ω := fun ω => wt_nonneg hc _
  have hWi : Integrable W P := integ_comp P _ (hU r) k (unm_le marked r) (wt c)
  have hGi : ∀ i, Integrable ((marked i r)ᶜ.indicator W) P := fun i =>
    hWi.indicator (ℱ.le r _ (hadapt i r)).compl
  have hHi : ∀ i, Integrable ((marked i (r + 1)).indicator ((marked i r)ᶜ.indicator W)) P :=
    fun i => (hGi i).indicator (ℱ.le (r + 1) _ (hadapt i (r + 1)))
  have hkey : ∀ i, β * ∫ ω, (marked i r)ᶜ.indicator W ω ∂P
      - ∫ ω, (marked i (r + 1)).indicator ((marked i r)ᶜ.indicator W) ω ∂P ≤ 0 := fun i => by
    have := key P (ℱ r) (ℱ.le r) β _ _ (hadapt i r) (ℱ.le _ _ (hadapt i (r + 1))) (hmark i r)
      W hWm hW0 hWi
    linarith
  have hid : ∀ ω, wt c (unm marked r ω) *
      (β * (unm marked r ω : ℝ) - ((unm marked r ω : ℝ) - unm marked (r + 1) ω)) =
      ∑ i, (β * (marked i r)ᶜ.indicator W ω
        - (marked i (r + 1)).indicator ((marked i r)ᶜ.indicator W) ω) := by
    intro ω
    rw [unm_cast, unm_cast, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h1 : ω ∈ marked i r
    · have h2 := hmono i r h1
      simp [h1, h2]
    · by_cases h2 : ω ∈ marked i (r + 1)
      · simp [h1, h2, hWdef]; ring
      · simp [h1, h2, hWdef]; ring
  have hpt : ∀ ω, phi (unm marked (r + 1) ω) c + β * (if 1 ≤ unm marked r ω then (1 : ℝ) else 0)
      ≤ phi (unm marked r ω) (β + (1 - β) * c) + ∑ i, (β * (marked i r)ᶜ.indicator W ω
        - (marked i (r + 1)).indicator ((marked i r)ᶜ.indicator W) ω) := by
    intro ω
    rw [← hid ω]
    have hle : unm marked (r + 1) ω ≤ unm marked r ω := by
      unfold unm
      apply Finset.sum_le_sum
      intro i _
      by_cases h1 : ω ∈ marked i r
      · have h2 := hmono i r h1
        simp [h1, h2]
      · split_ifs <;> omega
    exact pointwise hβ hβ1 hc hc1 hle
  have hI1 : Integrable (fun ω => phi (unm marked (r + 1) ω) c) P :=
    integ_comp P _ (hU (r + 1)) k (unm_le marked (r + 1)) (fun n => phi n c)
  have hI2 : Integrable (fun ω => (if 1 ≤ unm marked r ω then (1 : ℝ) else 0)) P :=
    integ_comp P _ (hU r) k (unm_le marked r) (fun n => if 1 ≤ n then (1 : ℝ) else 0)
  have hI3 : Integrable (fun ω => phi (unm marked r ω) (β + (1 - β) * c)) P :=
    integ_comp P _ (hU r) k (unm_le marked r) (fun n => phi n (β + (1 - β) * c))
  have hI4 : Integrable (fun ω => ∑ i, (β * (marked i r)ᶜ.indicator W ω
        - (marked i (r + 1)).indicator ((marked i r)ᶜ.indicator W) ω)) P :=
    integrable_finsetSum _ (fun i _ => ((hGi i).const_mul β).sub (hHi i))
  have hmono_int : ∫ ω, (phi (unm marked (r + 1) ω) c
        + β * (if 1 ≤ unm marked r ω then (1 : ℝ) else 0)) ∂P
      ≤ ∫ ω, (phi (unm marked r ω) (β + (1 - β) * c) + ∑ i, (β * (marked i r)ᶜ.indicator W ω
        - (marked i (r + 1)).indicator ((marked i r)ᶜ.indicator W) ω)) ∂P :=
    integral_mono (hI1.add (hI2.const_mul β)) (hI3.add hI4) hpt
  have hfs : ∀ i ∈ (Finset.univ : Finset (Fin k)), Integrable (fun ω => β * (marked i r)ᶜ.indicator W ω
      - (marked i (r + 1)).indicator ((marked i r)ᶜ.indicator W) ω) P :=
    fun i _ => ((hGi i).const_mul β).sub (hHi i)
  rw [integral_add hI1 (hI2.const_mul β), integral_const_mul, integral_add hI3 hI4,
    integral_finsetSum _ hfs] at hmono_int
  have hsum : ∑ i, ∫ ω, (β * (marked i r)ᶜ.indicator W ω
        - (marked i (r + 1)).indicator ((marked i r)ᶜ.indicator W) ω) ∂P ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    rw [integral_sub ((hGi i).const_mul β) (hHi i), integral_const_mul]
    exact hkey i
  linarith

end L45

open MeasureTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (k : ℕ) (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (marked : Fin k → ℕ → Set Ω)
    (h0 : ∀ i, marked i 0 = ∅)
    (hmono : ∀ i r, marked i r ⊆ marked i (r + 1))
    (hadapt : ∀ i r, @MeasurableSet Ω (ℱ r) (marked i r))
    (hmark : ∀ i r, ∀ᵐ ω ∂P, ω ∉ marked i r →
      β ≤ MeasureTheory.condExp (ℱ r) P ((marked i (r + 1)).indicator (fun _ => (1 : ℝ))) ω)
    (x : Ω → ℕ∞) (hx : ∀ ω, x ω = ⨅ (r : ℕ) (_ : ∀ i, ω ∈ marked i r), (r : ℕ∞))
    (j : ℕ) :
    β * ∫ ω, ((min (x ω) (j : ℕ∞)).toNat : ℝ) ∂P ≤
        ∑ h ∈ Finset.Icc 1 k, (1 - (1 - β) ^ j) ^ h / (h : ℝ) ∧
      (k = 1 → (P {ω | (j : ℕ∞) < x ω}).toReal ≤ 1 - (1 - (1 - β) ^ j)) := by
  classical
  have hmono' : ∀ i, Monotone (marked i) := fun i => monotone_nat_of_le_succ (hmono i)
  have hU : ∀ s, Measurable (L45.unm marked s) := fun s =>
    (L45.unm_meas _ s _ (fun i => hadapt i s)).mono (ℱ.le s) le_rfl
  have hxc : ∀ ω (r : ℕ), (r : ℕ∞) < x ω ↔ 1 ≤ L45.unm marked r ω := by
    intro ω r
    rw [L45.unm_pos_iff, hx ω]
    constructor
    · intro h
      by_contra hne
      push Not at hne
      exact absurd h (not_lt.2
        (iInf₂_le (f := fun (r : ℕ) (_ : ∀ i, ω ∈ marked i r) => (r : ℕ∞)) r hne))
    · rintro ⟨i, hi⟩
      rw [← ENat.add_one_le_iff (ENat.natCast_ne_top r)]
      refine le_iInf₂ fun r' hr' => ?_
      have : r + 1 ≤ r' := by
        by_contra hlt
        exact hi (hmono' i (show r' ≤ r by omega) (hr' i))
      exact_mod_cast this
  constructor
  · set q := 1 - β with hq
    have hE : ∀ n, n ≤ j →
        β * ∑ r ∈ Finset.range n, ∫ ω, (if 1 ≤ L45.unm marked r ω then (1 : ℝ) else 0) ∂P
          + ∫ ω, L45.phi (L45.unm marked n ω) (1 - q ^ (j - n)) ∂P
          ≤ ∫ ω, L45.phi (L45.unm marked 0 ω) (1 - q ^ (j - 0)) ∂P := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        have ih := ih (by omega)
        have hq0 : 0 ≤ q := by rw [hq]; linarith
        have hq1 : q ≤ 1 := by rw [hq]; linarith
        have hc0 : 0 ≤ 1 - q ^ (j - (n + 1)) := by
          have : q ^ (j - (n + 1)) ≤ 1 := pow_le_one₀ hq0 hq1
          linarith
        have hc1 : 1 - q ^ (j - (n + 1)) ≤ 1 := by
          have := pow_nonneg hq0 (j - (n + 1))
          linarith
        have hst := L45.step P ℱ k β hβ hβ1 marked hmono hadapt hmark n _ hc0 hc1
        have hb : β + (1 - β) * (1 - q ^ (j - (n + 1))) = 1 - q ^ (j - n) := by
          have : j - n = (j - (n + 1)) + 1 := by omega
          rw [this, pow_succ, hq]; ring
        rw [hb] at hst
        rw [Finset.sum_range_succ, mul_add]
        linarith
    have h := hE j le_rfl
    have h0' : ∀ ω, L45.unm marked 0 ω = k := L45.unm_zero marked h0
    simp only [Nat.sub_self, pow_zero, sub_self, L45.phi_at_zero, integral_zero, add_zero,
      Nat.sub_zero, h0'] at h
    have hint : ∫ ω, ((min (x ω) (j : ℕ∞)).toNat : ℝ) ∂P =
        ∑ r ∈ Finset.range j, ∫ ω, (if 1 ≤ L45.unm marked r ω then (1 : ℝ) else 0) ∂P := by
      rw [← integral_finsetSum]
      · congr 1
        funext ω
        rw [L45.min_toNat_eq]
        apply Finset.sum_congr rfl
        intro r _
        simp only [hxc]
      · intro r _
        exact L45.integ_comp P _ (hU r) k (L45.unm_le marked r)
          (fun n => if 1 ≤ n then (1 : ℝ) else 0)
    rw [hint]
    simpa [L45.phi] using h
  · intro hk
    subst hk
    have hset : {ω | (j : ℕ∞) < x ω} = (marked 0 j)ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, hxc, L45.unm_pos_iff]
      constructor
      · rintro ⟨i, hi⟩
        rwa [Subsingleton.elim i 0] at hi
      · intro h
        exact ⟨0, h⟩
    have hind : ∀ n, ∫ ω, (marked 0 n)ᶜ.indicator (fun _ => (1 : ℝ)) ω ∂P ≤ (1 - β) ^ n := by
      intro n
      induction n with
      | zero => simp [h0]
      | succ n ih =>
        have hk := L45.key P (ℱ n) (ℱ.le n) β _ _ (hadapt 0 n) (ℱ.le _ _ (hadapt 0 (n + 1)))
          (hmark 0 n) (fun _ => (1 : ℝ)) stronglyMeasurable_const (fun _ => zero_le_one)
          (integrable_const _)
        have e : (marked 0 (n + 1))ᶜ.indicator (fun _ => (1 : ℝ)) = fun ω =>
            (marked 0 n)ᶜ.indicator (fun _ => (1 : ℝ)) ω
              - (marked 0 (n + 1)).indicator ((marked 0 n)ᶜ.indicator (fun _ => (1 : ℝ))) ω := by
          funext ω
          by_cases h1 : ω ∈ marked 0 n
          · have h2 := hmono 0 n h1
            simp [h1, h2]
          · by_cases h2 : ω ∈ marked 0 (n + 1) <;> simp [h1, h2]
        have hGi : Integrable ((marked 0 n)ᶜ.indicator (fun _ => (1 : ℝ))) P :=
          (integrable_const _).indicator (ℱ.le n _ (hadapt 0 n)).compl
        rw [e, integral_sub hGi (hGi.indicator (ℱ.le (n + 1) _ (hadapt 0 (n + 1))))]
        have hq : 0 ≤ 1 - β := by linarith
        calc _ ≤ (1 - β) * ∫ ω, (marked 0 n)ᶜ.indicator (fun _ => (1 : ℝ)) ω ∂P := by linarith
          _ ≤ (1 - β) * (1 - β) ^ n := mul_le_mul_of_nonneg_left ih hq
          _ = _ := by ring
    rw [hset]
    have := integral_indicator_one (μ := P) (ℱ.le j _ (hadapt 0 j)).compl
    rw [measureReal_def] at this
    rw [← this]
    have := hind j
    have e2 : (1 : ℝ) - (1 - (1 - β) ^ j) = (1 - β) ^ j := by ring
    rw [e2]
    exact this
