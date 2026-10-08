-- Prove2me | solution 1 for KingmanSubadditive.StationaryIncrements.stationary_smooth
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:28:57.040062+00:00
-- url     : https://prove2.me/submissions/3fc34bba-5dd2-4ef0-a601-6d205dade5b2

import Mathlib
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Stationarity
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Construction
open MeasureTheory ProbabilityTheory Filter


namespace KingmanSubadditive.StationaryIncrements

/-- the weights `1/(r(r+1))` in `ℝ≥0∞` -/
noncomputable def cw (r : ℕ) : ENNReal := ENNReal.ofReal (1 / ((r : ℝ) * ((r : ℝ) + 1)))

lemma tsum_subtype_ge (n : ℕ) (g : ℕ → ENNReal) :
    ∑' r : {r : ℕ // n ≤ r}, g r = ∑' r : ℕ, Set.indicator {r : ℕ | n ≤ r} g r :=
  tsum_subtype {r : ℕ | n ≤ r} g

/-- telescoping: `∑_{k} 1/((k+n)(k+n+1)) = 1/n` for `n ≥ 1` (real) -/
lemma hasSum_telescope (n : ℕ) (hn : 1 ≤ n) :
    HasSum (fun k : ℕ => 1 / (((k + n : ℕ) : ℝ) * (((k + n : ℕ) : ℝ) + 1))) (1 / (n : ℝ)) := by
  have hpos : ∀ k : ℕ, 0 ≤ 1 / (((k + n : ℕ) : ℝ) * (((k + n : ℕ) : ℝ) + 1)) := by
    intro k; positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hpos]
  have hterm : ∀ k : ℕ, 1 / (((k + n : ℕ) : ℝ) * (((k + n : ℕ) : ℝ) + 1))
      = 1 / ((k + n : ℕ) : ℝ) - 1 / (((k + 1 + n : ℕ) : ℝ)) := by
    intro k
    have h1 : (0 : ℝ) < ((k + n : ℕ) : ℝ) := by
      have : 1 ≤ k + n := by omega
      exact_mod_cast this
    have h2 : ((k + 1 + n : ℕ) : ℝ) = ((k + n : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [h2]
    field_simp
    ring
  have hsum : ∀ m : ℕ, ∑ k ∈ Finset.range m, 1 / (((k + n : ℕ) : ℝ) * (((k + n : ℕ) : ℝ) + 1))
      = 1 / (n : ℝ) - 1 / ((m + n : ℕ) : ℝ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, hterm]
      ring
  simp_rw [hsum]
  have : Tendsto (fun m : ℕ => 1 / ((m + n : ℕ) : ℝ)) atTop (nhds 0) := by
    have h2 : Tendsto (fun m : ℕ => m + n) atTop atTop := tendsto_add_atTop_nat n
    have h3 := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp h2
    refine h3.congr ?_
    intro m; simp [Function.comp, one_div]
  have := this.const_sub (1 / (n : ℝ))
  simpa using this

lemma tsum_cw_eq (n : ℕ) (hn : 1 ≤ n) :
    ∑' r : {r : ℕ // n ≤ r}, cw r = ENNReal.ofReal (1 / (n : ℝ)) := by
  let e : ℕ ≃ {r : ℕ // n ≤ r} :=
    { toFun := fun k => ⟨k + n, by omega⟩
      invFun := fun r => r.1 - n
      left_inv := fun k => by simp
      right_inv := fun r => by
        obtain ⟨r, hr⟩ := r
        simp only [Subtype.mk.injEq]
        omega }
  rw [← e.tsum_eq]
  have h := hasSum_telescope n hn
  have hpos : ∀ k : ℕ, 0 ≤ 1 / (((k + n : ℕ) : ℝ) * (((k + n : ℕ) : ℝ) + 1)) := by
    intro k; positivity
  rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hpos h.summable]
  rfl

/-- `nuLaw Γ` is a probability measure -/
lemma nuLaw_isProbabilityMeasure (Γ : ℝ → ℝ) : IsProbabilityMeasure (nuLaw Γ) := by
  constructor
  rw [nuLaw, Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  have := tsum_cw_eq 1 le_rfl
  simp only [cw] at this
  rw [this]
  simp

/-- evaluation of a sequence at a measurable index is measurable -/
lemma measurable_eval_comp {X : Type*} [MeasurableSpace X] (g : X → ℕ) (hg : Measurable g) :
    Measurable (fun p : X × (ℕ → ℕ) => p.2 (g p.1)) := by
  apply measurable_to_countable'
  intro m
  have : (fun p : X × (ℕ → ℕ) => p.2 (g p.1)) ⁻¹' {m}
      = ⋃ k : ℕ, ({p : X × (ℕ → ℕ) | g p.1 = k} ∩ {p | p.2 k = m}) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    constructor
    · intro h; exact ⟨g p.1, rfl, h⟩
    · rintro ⟨k, hk, h⟩; rw [hk]; exact h
  rw [this]
  refine MeasurableSet.iUnion fun k => MeasurableSet.inter ?_ ?_
  · exact (hg.comp measurable_fst) (measurableSet_singleton k)
  · have h2 : Measurable (fun p : X × (ℕ → ℕ) => p.2 k) := (measurable_pi_apply k).comp measurable_snd
    exact h2 (measurableSet_singleton m)

/-- the path map on the state space `ℝ × (ℕ → ℕ)`, shifted by `τ` -/
noncomputable def pathMap (ψ : ℝ → ℝ) (τ : ℝ) (p : ℝ × (ℕ → ℕ)) (t : Set.Ici (0 : ℝ)) : ℝ :=
  bigY ψ p.2 ((t : ℝ) + τ + p.1)

/-- the unshifted path map -/
noncomputable def pathMap0 (ψ : ℝ → ℝ) (p : ℝ × (ℕ → ℕ)) (t : Set.Ici (0 : ℝ)) : ℝ :=
  bigY ψ p.2 ((t : ℝ) + p.1)

/-- the state shift -/
noncomputable def Tshift (τ : ℝ) (p : ℝ × (ℕ → ℕ)) : ℝ × (ℕ → ℕ) :=
  (p.1 + τ - (⌊p.1 + τ⌋₊ : ℝ), fun r => p.2 (r + ⌊p.1 + τ⌋₊))

lemma measurable_bigY_state (ψ : ℝ → ℝ) (hψ : Continuous ψ) (c : ℝ) :
    Measurable (fun p : ℝ × (ℕ → ℕ) => bigY ψ p.2 (c + p.1)) := by
  unfold bigY
  have hfl0 : Measurable (fun e : ℝ => ⌊c + e⌋₊) :=
    Nat.measurable_floor.comp (measurable_const.add measurable_id)
  have hfl : Measurable (fun p : ℝ × (ℕ → ℕ) => ⌊c + p.1⌋₊) := hfl0.comp measurable_fst
  have hev : Measurable (fun p : ℝ × (ℕ → ℕ) => p.2 ⌊c + p.1⌋₊) :=
    measurable_eval_comp _ hfl0
  have hevR : Measurable (fun p : ℝ × (ℕ → ℕ) => (p.2 ⌊c + p.1⌋₊ : ℝ)) :=
    (Measurable.of_discrete (f := (fun n : ℕ => (n : ℝ)))).comp hev
  have hflR : Measurable (fun p : ℝ × (ℕ → ℕ) => (⌊c + p.1⌋₊ : ℝ)) :=
    (Measurable.of_discrete (f := (fun n : ℕ => (n : ℝ)))).comp hfl
  exact hevR.mul (hψ.measurable.comp (hevR.mul ((measurable_const.add measurable_fst).sub hflR)))

lemma measurable_pathMap (ψ : ℝ → ℝ) (hψ : Continuous ψ) (τ : ℝ) :
    Measurable (pathMap ψ τ) := by
  rw [measurable_pi_iff]
  intro t
  have := measurable_bigY_state ψ hψ ((t : ℝ) + τ)
  exact this

lemma measurable_pathMap0 (ψ : ℝ → ℝ) (hψ : Continuous ψ) :
    Measurable (pathMap0 ψ) := by
  rw [measurable_pi_iff]
  intro t
  exact measurable_bigY_state ψ hψ (t : ℝ)

lemma measurable_Tshift (τ : ℝ) : Measurable (Tshift τ) := by
  have hfl0 : Measurable (fun e : ℝ => ⌊e + τ⌋₊) :=
    Nat.measurable_floor.comp (measurable_id.add measurable_const)
  have hfl : Measurable (fun p : ℝ × (ℕ → ℕ) => ⌊p.1 + τ⌋₊) := hfl0.comp measurable_fst
  have hflR : Measurable (fun p : ℝ × (ℕ → ℕ) => (⌊p.1 + τ⌋₊ : ℝ)) :=
    (Measurable.of_discrete (f := (fun n : ℕ => (n : ℝ)))).comp hfl
  refine Measurable.prodMk ((measurable_fst.add measurable_const).sub hflR) ?_
  rw [measurable_pi_iff]
  intro r
  exact measurable_eval_comp (fun e : ℝ => r + ⌊e + τ⌋₊) (measurable_const.add hfl0)

/-- pointwise: shifting time by `τ` is the same as shifting the state -/
lemma pathMap_eq_Tshift (ψ : ℝ → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (p : ℝ × (ℕ → ℕ)) (hp : 0 ≤ p.1) :
    pathMap ψ τ p = pathMap0 ψ (Tshift τ p) := by
  funext t
  unfold pathMap pathMap0 Tshift bigY
  simp only
  have hfr : 0 ≤ p.1 + τ - (⌊p.1 + τ⌋₊ : ℝ) := by
    have := Nat.floor_le (by linarith : 0 ≤ p.1 + τ)
    linarith
  have hnn : 0 ≤ (t : ℝ) + (p.1 + τ - (⌊p.1 + τ⌋₊ : ℝ)) := by
    have := t.2
    simp only [Set.mem_Ici] at this
    linarith
  have h1 : (t : ℝ) + τ + p.1 = ((t : ℝ) + (p.1 + τ - (⌊p.1 + τ⌋₊ : ℝ))) + (⌊p.1 + τ⌋₊ : ℕ) := by
    ring
  rw [h1, Nat.floor_add_natCast hnn]
  push_cast
  congr 2
  ring


/-- the fractional shift `e ↦ e + τ - ⌊e + τ⌋₊` preserves the uniform law on `(0,1)` -/
lemma frac_shift_preimage (τ : ℝ) (hτ : 0 ≤ τ) (A : Set ℝ) (hA : MeasurableSet A) :
    (volume.restrict (Set.Ioo (0 : ℝ) 1)) ((fun e : ℝ => e + τ - (⌊e + τ⌋₊ : ℝ)) ⁻¹' A)
      = (volume.restrict (Set.Ioo (0 : ℝ) 1)) A := by
  have hf : Measurable (fun e : ℝ => e + τ - (⌊e + τ⌋₊ : ℝ)) :=
    (measurable_id.add measurable_const).sub
      ((Measurable.of_discrete (f := (fun n : ℕ => (n : ℝ)))).comp
        (Nat.measurable_floor.comp (measurable_id.add measurable_const)))
  set fτ : ℝ := τ - (⌊τ⌋₊ : ℝ) with hfτ
  have hfτ0 : 0 ≤ fτ := by
    have := Nat.floor_le hτ
    rw [hfτ]; linarith
  have hfτ1 : fτ < 1 := by
    have := Nat.lt_floor_add_one τ
    rw [hfτ]; linarith
  have key : ∀ e : ℝ, 0 < e → e + τ - (⌊e + τ⌋₊ : ℝ) = e + fτ - (⌊e + fτ⌋₊ : ℝ) := by
    intro e he
    have h1 : e + τ = (e + fτ) + (⌊τ⌋₊ : ℕ) := by rw [hfτ]; ring
    rw [h1, Nat.floor_add_natCast (by linarith)]
    push_cast
    ring
  have fl0 : ∀ e : ℝ, e + fτ < 1 → ⌊e + fτ⌋₊ = 0 := fun e h => Nat.floor_eq_zero.mpr h
  have fl1 : ∀ e : ℝ, 1 < e + fτ → e < 1 → ⌊e + fτ⌋₊ = 1 := by
    intro e h1 h2
    rw [Nat.floor_eq_iff (by linarith)]
    constructor
    · push_cast; linarith
    · push_cast; linarith
  rw [Measure.restrict_apply (hf hA), Measure.restrict_apply hA,
    ← measure_sdiff_null (s := (fun e : ℝ => e + τ - (⌊e + τ⌋₊ : ℝ)) ⁻¹' A ∩ Set.Ioo 0 1)
      (measure_singleton (1 - fτ)),
    ← measure_sdiff_null (s := A ∩ Set.Ioo 0 1) (measure_singleton fτ)]
  have hU : ((fun e : ℝ => e + τ - (⌊e + τ⌋₊ : ℝ)) ⁻¹' A ∩ Set.Ioo 0 1) \ {1 - fτ}
      = ((· + fτ) ⁻¹' (A ∩ Set.Ioo fτ 1)) ∪ ((· + (fτ - 1)) ⁻¹' (A ∩ Set.Ioo 0 fτ)) := by
    ext e
    simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioo,
      Set.mem_singleton_iff, Set.mem_union]
    constructor
    · rintro ⟨⟨hAe, h0, h1⟩, hne⟩
      rw [key e h0] at hAe
      by_cases hlt : e + fτ < 1
      · left
        rw [fl0 e hlt] at hAe
        simp only [Nat.cast_zero, sub_zero] at hAe
        exact ⟨hAe, by linarith, hlt⟩
      · right
        have hgt : 1 < e + fτ := by
          rcases lt_or_eq_of_le (not_lt.mp hlt) with h | h
          · exact h
          · exfalso; apply hne; linarith
        rw [fl1 e hgt h1] at hAe
        simp only [Nat.cast_one] at hAe
        refine ⟨?_, by linarith, by linarith⟩
        convert hAe using 1; ring
    · rintro (⟨hAe, h0, h1⟩ | ⟨hAe, h0, h1⟩)
      · have he0 : 0 < e := by linarith
        refine ⟨⟨?_, he0, by linarith⟩, by intro h; linarith⟩
        rw [key e he0, fl0 e h1]
        simp only [Nat.cast_zero, sub_zero]
        exact hAe
      · have he0 : 0 < e := by linarith
        refine ⟨⟨?_, he0, by linarith⟩, by intro h; linarith⟩
        rw [key e he0, fl1 e (by linarith) (by linarith)]
        simp only [Nat.cast_one]
        convert hAe using 1; ring
  have hV : (A ∩ Set.Ioo 0 1) \ {fτ} = (A ∩ Set.Ioo fτ 1) ∪ (A ∩ Set.Ioo 0 fτ) := by
    ext x
    simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_Ioo, Set.mem_singleton_iff, Set.mem_union]
    constructor
    · rintro ⟨⟨hAx, h0, h1⟩, hne⟩
      rcases lt_or_gt_of_ne hne with h | h
      · right; exact ⟨hAx, h0, h⟩
      · left; exact ⟨hAx, h, h1⟩
    · rintro (⟨hAx, h0, h1⟩ | ⟨hAx, h0, h1⟩)
      · exact ⟨⟨hAx, by linarith, h1⟩, by intro h; linarith⟩
      · exact ⟨⟨hAx, h0, by linarith⟩, by intro h; linarith⟩
  rw [hU, hV]
  have hm1 : MeasurableSet (A ∩ Set.Ioo fτ 1) := hA.inter measurableSet_Ioo
  have hm2 : MeasurableSet (A ∩ Set.Ioo 0 fτ) := hA.inter measurableSet_Ioo
  rw [measure_union _ ((measurable_add_const (fτ - 1)) hm2),
    measure_union _ hm2, measure_preimage_add_right, measure_preimage_add_right]
  · rw [Set.disjoint_left]
    intro x ⟨_, h1, _⟩ ⟨_, _, h2⟩
    linarith
  · rw [Set.disjoint_left]
    intro e ⟨_, _, h1⟩ ⟨_, h2, _⟩
    simp only [Set.mem_preimage] at *
    linarith

/-- the product law is invariant under the state shift -/
lemma prod_map_Tshift (Γ : ℝ → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) :
    ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (Measure.infinitePi (fun _ : ℕ => nuLaw Γ))).map (Tshift τ)
      = (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod (Measure.infinitePi (fun _ : ℕ => nuLaw Γ)) := by
  haveI := nuLaw_isProbabilityMeasure Γ
  set π := Measure.infinitePi (fun _ : ℕ => nuLaw Γ) with hπ
  symm
  apply Measure.prod_eq
  intro A B hA hB
  rw [Measure.map_apply (measurable_Tshift τ) (hA.prod hB),
    Measure.prod_apply ((measurable_Tshift τ) (hA.prod hB))]
  have hshift : ∀ k : ℕ, Measurable (fun v : ℕ → ℕ => fun r => v (r + k)) := by
    intro k
    rw [measurable_pi_iff]
    intro r
    exact measurable_pi_apply _
  have hπshift : ∀ k : ℕ, π.map (fun v : ℕ → ℕ => fun r => v (r + k)) = π := by
    intro k
    rw [hπ, Measure.map_infinitePi_infinitePi_of_inj (f := fun r : ℕ => r + k) (add_left_injective k)]
  have hpt : ∀ e : ℝ, π (Prod.mk e ⁻¹' (Tshift τ ⁻¹' (A ×ˢ B)))
      = Set.indicator ((fun e : ℝ => e + τ - (⌊e + τ⌋₊ : ℝ)) ⁻¹' A) (fun _ => π B) e := by
    intro e
    by_cases he : e + τ - (⌊e + τ⌋₊ : ℝ) ∈ A
    · rw [Set.indicator_of_mem (show e ∈ (fun e : ℝ => e + τ - (⌊e + τ⌋₊ : ℝ)) ⁻¹' A from he)]
      have : Prod.mk e ⁻¹' (Tshift τ ⁻¹' (A ×ˢ B))
          = (fun v : ℕ → ℕ => fun r => v (r + ⌊e + τ⌋₊)) ⁻¹' B := by
        ext v
        simp [Tshift, he]
      rw [this, ← Measure.map_apply (hshift _) hB, hπshift]
    · rw [Set.indicator_of_notMem (show e ∉ (fun e : ℝ => e + τ - (⌊e + τ⌋₊ : ℝ)) ⁻¹' A from he)]
      have : Prod.mk e ⁻¹' (Tshift τ ⁻¹' (A ×ˢ B)) = ∅ := by
        ext v
        simp [Tshift, he]
      rw [this, measure_empty]
  rw [lintegral_congr hpt]
  have hf : Measurable (fun e : ℝ => e + τ - (⌊e + τ⌋₊ : ℝ)) :=
    (measurable_id.add measurable_const).sub
      ((Measurable.of_discrete (f := (fun n : ℕ => (n : ℝ)))).comp
        (Nat.measurable_floor.comp (measurable_id.add measurable_const)))
  rw [lintegral_indicator_const (hf hA), frac_shift_preimage τ hτ A hA, mul_comm]

/-- the state map -/
def Smap {Ω : Type*} (η : Ω → ℝ) (ν : ℕ → Ω → ℕ) (ω : Ω) : ℝ × (ℕ → ℕ) :=
  (η ω, fun r => ν r ω)

lemma measurable_Smap {Ω : Type*} [MeasurableSpace Ω] (η : Ω → ℝ) (ν : ℕ → Ω → ℕ)
    (hη : Measurable η) (hν : ∀ r, Measurable (ν r)) : Measurable (Smap η ν) :=
  hη.prodMk (measurable_pi_iff.2 hν)

/-- the law of the state is the product law -/
lemma law_Smap {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Γ : ℝ → ℝ) (η : Ω → ℝ) (ν : ℕ → Ω → ℕ) (hC : IsConstruction Γ P η ν) :
    P.map (Smap η ν) = (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (Measure.infinitePi (fun _ : ℕ => nuLaw Γ)) := by
  have h1 := (indepFun_iff_map_prod_eq_prod_map_map hC.measurable_eta.aemeasurable
    (measurable_pi_iff.2 hC.measurable_nu).aemeasurable).1 hC.indep_eta_nu
  have h2 := (iIndepFun_iff_map_fun_eq_infinitePi_map hC.measurable_nu).1 hC.iIndep_nu
  simp_rw [hC.law_nu] at h2
  unfold Smap
  rw [h1, hC.law_eta, h2]

/-- a.e. the first state coordinate is nonnegative -/
lemma ae_fst_nonneg (Γ : ℝ → ℝ) :
    ∀ᵐ p ∂((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (Measure.infinitePi (fun _ : ℕ => nuLaw Γ))), 0 ≤ p.1 := by
  haveI := nuLaw_isProbabilityMeasure Γ
  rw [ae_iff]
  have : {p : ℝ × (ℕ → ℕ) | ¬ 0 ≤ p.1} = Set.Iio 0 ×ˢ Set.univ := by
    ext p; simp
  rw [this, Measure.prod_prod, Measure.restrict_apply measurableSet_Iio]
  have : Set.Iio (0 : ℝ) ∩ Set.Ioo 0 1 = ∅ := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioo, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro h1 h2; linarith
  rw [this]; simp

/-- the process is stationary -/
lemma isStationary_procY {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Γ : ℝ → ℝ) (ψ : ℝ → ℝ) (hψ : IsBump ψ) (η : Ω → ℝ) (ν : ℕ → Ω → ℕ)
    (hC : IsConstruction Γ P η ν) : IsStationary P (procY ψ η ν) := by
  haveI := nuLaw_isProbabilityMeasure Γ
  have hψc : Continuous ψ := hψ.1.continuous
  have hS := measurable_Smap η ν hC.measurable_eta hC.measurable_nu
  constructor
  · intro t _
    exact ((measurable_bigY_state ψ hψc t).comp hS).aemeasurable
  · intro τ hτ
    have e1 : (fun ω (t : Set.Ici (0 : ℝ)) => procY ψ η ν ((t : ℝ) + τ) ω)
        = pathMap ψ τ ∘ Smap η ν := rfl
    have e2 : (fun ω (t : Set.Ici (0 : ℝ)) => procY ψ η ν (t : ℝ) ω)
        = pathMap0 ψ ∘ Smap η ν := rfl
    rw [e1, e2, ← Measure.map_map (measurable_pathMap ψ hψc τ) hS,
      ← Measure.map_map (measurable_pathMap0 ψ hψc) hS, law_Smap P Γ η ν hC]
    have hae : pathMap ψ τ =ᵐ[(volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (Measure.infinitePi (fun _ : ℕ => nuLaw Γ))] (pathMap0 ψ ∘ Tshift τ) := by
      filter_upwards [ae_fst_nonneg Γ] with p hp
      exact pathMap_eq_Tshift ψ τ hτ p hp
    rw [Measure.map_congr hae, ← Measure.map_map (measurable_pathMap0 ψ hψc) (measurable_Tshift τ),
      prod_map_Tshift Γ τ hτ]


/-- the local model on the `n`-th interval -/
noncomputable def locG (ψ : ℝ → ℝ) (v : ℕ → ℕ) (n : ℕ) (s : ℝ) : ℝ :=
  (v n : ℝ) * ψ ((v n : ℝ) * (s - (n : ℝ)))

lemma contDiff_locG (ψ : ℝ → ℝ) (hψ : IsBump ψ) (v : ℕ → ℕ) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (locG ψ v n) := by
  unfold locG
  exact contDiff_const.mul (hψ.1.comp (contDiff_const.mul (contDiff_id.sub contDiff_const)))

lemma psi_zero_of_nonpos (ψ : ℝ → ℝ) (hψ : IsBump ψ) (x : ℝ) (hx : x ≤ 0) : ψ x = 0 := by
  apply hψ.2.1
  simp only [Set.mem_Ioo, not_and, not_lt]
  intro h; linarith

lemma psi_zero_of_ge (ψ : ℝ → ℝ) (hψ : IsBump ψ) (x : ℝ) (hx : 3 / 4 ≤ x) : ψ x = 0 := by
  apply hψ.2.1
  simp only [Set.mem_Ioo, not_and, not_lt]
  intro _; exact hx

/-- `bigY` is smooth on all of `ℝ` -/
lemma contDiff_bigY (ψ : ℝ → ℝ) (hψ : IsBump ψ) (v : ℕ → ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bigY ψ v) := by
  rw [contDiff_iff_contDiffAt]
  intro s₀
  by_cases h1 : s₀ < 1
  · -- on `(-∞, 1)` the process is `locG ψ v 0`
    refine (contDiff_locG ψ hψ v 0).contDiffAt.congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem (Iio_mem_nhds h1) ?_
    intro s hs
    simp only [Set.mem_Iio] at hs
    unfold bigY locG
    rw [Nat.floor_eq_zero.mpr hs]
  · push_neg at h1
    set n := ⌊s₀⌋₊ with hn
    have hn1 : 1 ≤ n := by
      rw [hn]; exact Nat.le_floor (by simpa using h1)
    have hs0 : 0 ≤ s₀ := by linarith
    have hfl : (n : ℝ) ≤ s₀ := Nat.floor_le hs0
    have hfl' : s₀ < (n : ℝ) + 1 := Nat.lt_floor_add_one s₀
    clear_value n
    refine (contDiff_locG ψ hψ v n).contDiffAt.congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem (Ioo_mem_nhds (by linarith : (n : ℝ) - 1 / 4 < s₀) hfl') ?_
    intro s hs
    simp only [Set.mem_Ioo] at hs
    unfold bigY locG
    by_cases hsn : (n : ℝ) ≤ s
    · have : ⌊s⌋₊ = n := by
        rw [Nat.floor_eq_iff (by linarith)]
        exact ⟨hsn, hs.2⟩
      rw [this]
    · push_neg at hsn
      -- here both sides vanish
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hm : ⌊s⌋₊ = m := by
        rw [Nat.floor_eq_iff (by push_cast at hs; linarith)]
        push_cast at hs hsn ⊢
        constructor <;> linarith
      rw [hm]
      have hR : ψ ((v (m + 1) : ℝ) * (s - ((m + 1 : ℕ) : ℝ))) = 0 := by
        apply psi_zero_of_nonpos ψ hψ
        have : s - ((m + 1 : ℕ) : ℝ) ≤ 0 := by linarith
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) this
      rw [hR, mul_zero]
      by_cases hv : v m = 0
      · rw [hv]; simp
      · have hv1 : (1 : ℝ) ≤ (v m : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hv
        have hL : ψ ((v m : ℝ) * (s - (m : ℝ))) = 0 := by
          apply psi_zero_of_ge ψ hψ
          have h34 : 3 / 4 ≤ s - (m : ℝ) := by push_cast at hs; linarith
          calc (3 / 4 : ℝ) = 1 * (3 / 4) := by ring
            _ ≤ (v m : ℝ) * (s - (m : ℝ)) := by
              apply mul_le_mul hv1 h34 (by norm_num) (by linarith)
        rw [hL, mul_zero]

/-- every sample path is smooth -/
lemma contDiffOn_procY {Ω : Type*} (ψ : ℝ → ℝ) (hψ : IsBump ψ) (η : Ω → ℝ) (ν : ℕ → Ω → ℕ)
    (ω : Ω) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => procY ψ η ν t ω) (Set.Ici 0) := by
  apply ContDiff.contDiffOn
  exact (contDiff_bigY ψ hψ (fun r => ν r ω)).comp (contDiff_id.add contDiff_const)

/-- a stationary process (with measurable path maps) has stationary increments -/
lemma hasStationaryIncrements_of_isStationary {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (y : ℝ → Ω → ℝ) (hy : IsStationary P y)
    (hpath : ∀ τ : ℝ, Measurable (fun ω (t : Set.Ici (0 : ℝ)) => y ((t : ℝ) + τ) ω)) :
    HasStationaryIncrements P y := by
  refine ⟨hy.1, ?_⟩
  intro τ hτ
  let G : (Set.Ici (0 : ℝ) → ℝ) → (Set.Ici (0 : ℝ) → ℝ) :=
    fun q t => q t - q ⟨0, by simp⟩
  have hG : Measurable G := by
    rw [measurable_pi_iff]
    intro t
    exact (measurable_pi_apply t).sub (measurable_pi_apply _)
  have e1 : (fun ω (t : Set.Ici (0 : ℝ)) => y ((t : ℝ) + τ) ω - y τ ω)
      = G ∘ (fun ω (t : Set.Ici (0 : ℝ)) => y ((t : ℝ) + τ) ω) := by
    funext ω t
    simp [G]
  have e2 : (fun ω (t : Set.Ici (0 : ℝ)) => y (t : ℝ) ω - y 0 ω)
      = G ∘ (fun ω (t : Set.Ici (0 : ℝ)) => y (t : ℝ) ω) := by
    funext ω t
    simp [G]
  have h0 : (fun ω (t : Set.Ici (0 : ℝ)) => y (t : ℝ) ω)
      = (fun ω (t : Set.Ici (0 : ℝ)) => y ((t : ℝ) + 0) ω) := by
    funext ω t; simp
  rw [e1, e2, ← Measure.map_map hG (hpath τ), hy.2 τ hτ, h0, Measure.map_map hG (hpath 0)]

/-- the main statement -/
theorem stationary_smooth_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Γ : ℝ → ℝ) (hΓpos : ∀ t : ℝ, 0 < t → 0 < Γ t)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) (ψ : ℝ → ℝ) (hψ : IsBump ψ) (η : Ω → ℝ)
    (ν : ℕ → Ω → ℕ) (hC : IsConstruction Γ P η ν) :
    IsStationary P (procY ψ η ν) ∧ HasStationaryIncrements P (procY ψ η ν) ∧
      ∀ ω : Ω, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => procY ψ η ν t ω) (Set.Ici 0) := by
  have hstat := isStationary_procY P Γ ψ hψ η ν hC
  refine ⟨hstat, ?_, fun ω => contDiffOn_procY ψ hψ η ν ω⟩
  apply hasStationaryIncrements_of_isStationary P _ hstat
  intro τ
  exact (measurable_pathMap ψ hψ.1.continuous τ).comp
    (measurable_Smap η ν hC.measurable_eta hC.measurable_nu)

end KingmanSubadditive.StationaryIncrements

open KingmanSubadditive.StationaryIncrements


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Γ : ℝ → ℝ) (hΓpos : ∀ t : ℝ, 0 < t → 0 < Γ t)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) (ψ : ℝ → ℝ) (hψ : IsBump ψ) (η : Ω → ℝ)
    (ν : ℕ → Ω → ℕ) (hC : IsConstruction Γ P η ν) :
    IsStationary P (procY ψ η ν) ∧ HasStationaryIncrements P (procY ψ η ν) ∧
      ∀ ω : Ω, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => procY ψ η ν t ω) (Set.Ici 0) := by
  exact stationary_smooth_core P Γ hΓpos hΓmono ψ hψ η ν hC
