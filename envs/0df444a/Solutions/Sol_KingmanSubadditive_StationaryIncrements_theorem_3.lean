-- Prove2me | solution 1 for KingmanSubadditive.StationaryIncrements.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:36:58.530933+00:00
-- url     : https://prove2.me/submissions/9a61694b-87dc-402b-9783-2cda4ad1ec3e

import Mathlib
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Stationarity
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Construction
open MeasureTheory Filter
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


lemma psi_nonneg (ψ : ℝ → ℝ) (hψ : IsBump ψ) (x : ℝ) : 0 ≤ ψ x := (hψ.2.2.1 x).1

lemma bigY_nonneg (ψ : ℝ → ℝ) (hψ : IsBump ψ) (v : ℕ → ℕ) (s : ℝ) : 0 ≤ bigY ψ v s := by
  unfold bigY
  exact mul_nonneg (by positivity) (psi_nonneg ψ hψ _)

lemma integral_psi_nonneg (ψ : ℝ → ℝ) (hψ : IsBump ψ) : 0 ≤ ∫ u in (0 : ℝ)..1, ψ u :=
  intervalIntegral.integral_nonneg zero_le_one (fun u _ => psi_nonneg ψ hψ u)

/-- `∫₀¹ m ψ(m e) de = ∫₀¹ ψ` for integers `m ≥ 1` -/
lemma inner_integral (ψ : ℝ → ℝ) (hψ : IsBump ψ) (m : ℕ) (hm : 1 ≤ m) :
    ∫ e in Set.Ioo (0 : ℝ) 1, (m : ℝ) * ψ ((m : ℝ) * e) = ∫ u in (0 : ℝ)..1, ψ u := by
  have hψc : Continuous ψ := hψ.1.continuous
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left (fun x => ψ x) hm0]
  simp only [mul_zero, mul_one, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hm0, one_mul]
  have hsplit : ∫ x in (0 : ℝ)..(m : ℝ), ψ x
      = (∫ x in (0 : ℝ)..1, ψ x) + ∫ x in (1 : ℝ)..(m : ℝ), ψ x := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hψc.intervalIntegrable _ _)
      (hψc.intervalIntegrable _ _)]
  rw [hsplit]
  have hzero : ∫ x in (1 : ℝ)..(m : ℝ), ψ x = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · exact intervalIntegral.integral_zero
    · intro x hx
      rw [Set.uIcc_of_le hm1] at hx
      exact psi_zero_of_ge ψ hψ x (by linarith [hx.1])
  rw [hzero, add_zero]

/-- `nuLaw` is carried by `{m ≥ 1}` -/
lemma ae_nuLaw_one_le (Γ : ℝ → ℝ) : ∀ᵐ m ∂(nuLaw Γ), 1 ≤ m := by
  rw [ae_iff]
  rw [nuLaw, Measure.sum_apply _ MeasurableSet.of_discrete]
  simp_rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  apply ENNReal.tsum_eq_zero.mpr
  intro n
  have : nextAbove Γ n ∉ {m : ℕ | ¬ 1 ≤ m} := by
    simp only [Set.mem_setOf_eq, not_not, nextAbove]
    omega
  rw [Set.indicator_of_notMem this, mul_zero]

/-- the kernel function `(e, m) ↦ m ψ(m e)` -/
noncomputable def Hfun (ψ : ℝ → ℝ) (q : ℝ × ℕ) : ℝ := (q.2 : ℝ) * ψ ((q.2 : ℝ) * q.1)

lemma measurable_Hfun (ψ : ℝ → ℝ) (hψ : Continuous ψ) : Measurable (Hfun ψ) := by
  unfold Hfun
  have h2 : Measurable (fun q : ℝ × ℕ => (q.2 : ℝ)) :=
    (Measurable.of_discrete (f := (fun n : ℕ => (n : ℝ)))).comp measurable_snd
  exact h2.mul (hψ.measurable.comp (h2.mul measurable_fst))

lemma lintegral_Hfun (Γ : ℝ → ℝ) (ψ : ℝ → ℝ) (hψ : IsBump ψ) :
    ∫⁻ q, ENNReal.ofReal (Hfun ψ q) ∂((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod (nuLaw Γ))
      = ENNReal.ofReal (∫ u in (0 : ℝ)..1, ψ u) := by
  haveI := nuLaw_isProbabilityMeasure Γ
  have hψc : Continuous ψ := hψ.1.continuous
  have hH' : Measurable (fun q : ℝ × ℕ => ENNReal.ofReal (Hfun ψ q)) :=
    ENNReal.measurable_ofReal.comp (measurable_Hfun ψ hψc)
  rw [lintegral_prod_symm' (fun q : ℝ × ℕ => ENNReal.ofReal (Hfun ψ q)) hH']
  have hin : ∀ᵐ m ∂(nuLaw Γ), ∫⁻ e, ENNReal.ofReal (Hfun ψ (e, m)) ∂(volume.restrict (Set.Ioo (0 : ℝ) 1))
      = ENNReal.ofReal (∫ u in (0 : ℝ)..1, ψ u) := by
    filter_upwards [ae_nuLaw_one_le Γ] with m hm
    have hint : Integrable (fun e : ℝ => (m : ℝ) * ψ ((m : ℝ) * e))
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
      have hc : Continuous (fun e : ℝ => (m : ℝ) * ψ ((m : ℝ) * e)) :=
        continuous_const.mul (hψc.comp (continuous_const.mul continuous_id))
      exact (hc.integrableOn_Icc (a := 0) (b := 1)).mono_set Set.Ioo_subset_Icc_self
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] (fun e : ℝ => (m : ℝ) * ψ ((m : ℝ) * e)) :=
      Filter.Eventually.of_forall (fun e => mul_nonneg (by positivity) (psi_nonneg ψ hψ _))
    unfold Hfun
    simp only
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, inner_integral ψ hψ m hm]
  rw [lintegral_congr_ae hin, lintegral_const, measure_univ, mul_one]

/-- a.e. the first state coordinate is `< 1` -/
lemma ae_fst_lt_one (Γ : ℝ → ℝ) :
    ∀ᵐ p ∂((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (Measure.infinitePi (fun _ : ℕ => nuLaw Γ))), p.1 < 1 := by
  haveI := nuLaw_isProbabilityMeasure Γ
  rw [ae_iff]
  have : {p : ℝ × (ℕ → ℕ) | ¬ p.1 < 1} = Set.Ici 1 ×ˢ Set.univ := by
    ext p; simp
  rw [this, Measure.prod_prod, Measure.restrict_apply measurableSet_Ici]
  have : Set.Ici (1 : ℝ) ∩ Set.Ioo 0 1 = ∅ := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioo, Set.mem_empty_iff_false,
      iff_false]
    rintro ⟨h1, h2, h3⟩; linarith
  rw [this]; simp

/-- the Lebesgue integral of `y₀` -/
lemma lintegral_y0 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Γ : ℝ → ℝ) (ψ : ℝ → ℝ) (hψ : IsBump ψ) (η : Ω → ℝ) (ν : ℕ → Ω → ℕ)
    (hC : IsConstruction Γ P η ν) :
    ∫⁻ ω, ENNReal.ofReal (procY ψ η ν 0 ω) ∂P = ENNReal.ofReal (∫ u in (0 : ℝ)..1, ψ u) := by
  haveI := nuLaw_isProbabilityMeasure Γ
  have hψc : Continuous ψ := hψ.1.continuous
  have hS := measurable_Smap η ν hC.measurable_eta hC.measurable_nu
  have hF : Measurable (fun p : ℝ × (ℕ → ℕ) => bigY ψ p.2 (0 + p.1)) :=
    measurable_bigY_state ψ hψc 0
  have hF' : Measurable (fun p : ℝ × (ℕ → ℕ) => ENNReal.ofReal (bigY ψ p.2 (0 + p.1))) :=
    ENNReal.measurable_ofReal.comp hF
  have e1 : ∫⁻ ω, ENNReal.ofReal (procY ψ η ν 0 ω) ∂P
      = ∫⁻ ω, (fun p : ℝ × (ℕ → ℕ) => ENNReal.ofReal (bigY ψ p.2 (0 + p.1))) (Smap η ν ω) ∂P := rfl
  rw [e1, ← lintegral_map hF' hS, law_Smap P Γ η ν hC]
  set μ := (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
    (Measure.infinitePi (fun _ : ℕ => nuLaw Γ)) with hμ
  have hae : (fun p : ℝ × (ℕ → ℕ) => ENNReal.ofReal (bigY ψ p.2 (0 + p.1)))
      =ᵐ[μ] (fun p => ENNReal.ofReal (Hfun ψ (p.1, p.2 0))) := by
    filter_upwards [ae_fst_lt_one Γ] with p hp
    unfold bigY Hfun
    rw [zero_add, Nat.floor_eq_zero.mpr hp]
    simp
  rw [lintegral_congr_ae hae]
  have hproj : Measurable (fun p : ℝ × (ℕ → ℕ) => (p.1, p.2 0)) :=
    measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)
  have hH' : Measurable (fun q : ℝ × ℕ => ENNReal.ofReal (Hfun ψ q)) :=
    ENNReal.measurable_ofReal.comp (measurable_Hfun ψ hψc)
  have hproj' : Measurable (Prod.map (id : ℝ → ℝ) (fun v : ℕ → ℕ => v 0)) := hproj
  have e2 : ∫⁻ p, ENNReal.ofReal (Hfun ψ (p.1, p.2 0)) ∂μ
      = ∫⁻ p, (fun q : ℝ × ℕ => ENNReal.ofReal (Hfun ψ q))
          (Prod.map (id : ℝ → ℝ) (fun v : ℕ → ℕ => v 0) p) ∂μ := rfl
  rw [e2, ← lintegral_map hH' hproj',
    hμ, ← Measure.map_prod_map _ _ measurable_id (measurable_pi_apply 0), Measure.map_id,
    Measure.infinitePi_map_eval]
  exact lintegral_Hfun Γ ψ hψ

/-- one-dimensional marginals agree -/
lemma law_yt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Γ : ℝ → ℝ) (ψ : ℝ → ℝ) (hψ : IsBump ψ) (η : Ω → ℝ) (ν : ℕ → Ω → ℕ)
    (hC : IsConstruction Γ P η ν) (t : ℝ) (ht : 0 ≤ t) :
    P.map (procY ψ η ν t) = P.map (procY ψ η ν 0) := by
  have hstat := isStationary_procY P Γ ψ hψ η ν hC
  have hψc : Continuous ψ := hψ.1.continuous
  have hS := measurable_Smap η ν hC.measurable_eta hC.measurable_nu
  have hpath : ∀ τ : ℝ, Measurable (fun ω (s : Set.Ici (0 : ℝ)) => procY ψ η ν ((s : ℝ) + τ) ω) :=
    fun τ => (measurable_pathMap ψ hψc τ).comp hS
  have hpath0 : Measurable (fun ω (s : Set.Ici (0 : ℝ)) => procY ψ η ν (s : ℝ) ω) :=
    (measurable_pathMap0 ψ hψc).comp hS
  have h := congrArg (Measure.map (fun q : Set.Ici (0 : ℝ) → ℝ => q ⟨0, by simp⟩)) (hstat.2 t ht)
  rw [Measure.map_map (measurable_pi_apply _) (hpath t),
    Measure.map_map (measurable_pi_apply _) hpath0] at h
  have e1 : (fun q : Set.Ici (0 : ℝ) → ℝ => q ⟨0, by simp⟩) ∘
      (fun ω (s : Set.Ici (0 : ℝ)) => procY ψ η ν ((s : ℝ) + t) ω) = procY ψ η ν t := by
    funext ω; simp
  have e2 : (fun q : Set.Ici (0 : ℝ) → ℝ => q ⟨0, by simp⟩) ∘
      (fun ω (s : Set.Ici (0 : ℝ)) => procY ψ η ν (s : ℝ) ω) = procY ψ η ν 0 := rfl
  rw [e1, e2] at h
  exact h

/-- the expectation statement -/
theorem expectation_abs_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Γ : ℝ → ℝ) (hΓpos : ∀ t : ℝ, 0 < t → 0 < Γ t)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) (ψ : ℝ → ℝ) (hψ : IsBump ψ) (η : Ω → ℝ)
    (ν : ℕ → Ω → ℕ) (hC : IsConstruction Γ P η ν) :
    ∀ t : ℝ, 0 ≤ t →
      Integrable (procY ψ η ν t) P ∧
        ∫ ω, |procY ψ η ν t ω| ∂P = ∫ ω, procY ψ η ν 0 ω ∂P ∧
        ∫ ω, procY ψ η ν 0 ω ∂P = ∫ u in (0 : ℝ)..1, ψ u := by
  have hψc : Continuous ψ := hψ.1.continuous
  have hS := measurable_Smap η ν hC.measurable_eta hC.measurable_nu
  have hy : ∀ t : ℝ, Measurable (procY ψ η ν t) :=
    fun t => (measurable_bigY_state ψ hψc t).comp hS
  have hnn0 : ∀ ω, 0 ≤ procY ψ η ν 0 ω := fun ω => bigY_nonneg ψ hψ _ _
  have hL := lintegral_y0 P Γ ψ hψ η ν hC
  have hint0 : Integrable (procY ψ η ν 0) P := by
    refine ⟨(hy 0).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn0), hL]
    exact ENNReal.ofReal_lt_top
  have hI0 : ∫ ω, procY ψ η ν 0 ω ∂P = ∫ u in (0 : ℝ)..1, ψ u := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn0)
      (hy 0).aestronglyMeasurable, hL, ENNReal.toReal_ofReal (integral_psi_nonneg ψ hψ)]
  intro t ht
  have hlaw := law_yt P Γ ψ hψ η ν hC t ht
  refine ⟨?_, ?_, hI0⟩
  · have k1 : Integrable (fun x : ℝ => x) (P.map (procY ψ η ν t)) ↔ Integrable (procY ψ η ν t) P :=
      integrable_map_measure aestronglyMeasurable_id (hy t).aemeasurable
    have k2 : Integrable (fun x : ℝ => x) (P.map (procY ψ η ν 0)) ↔ Integrable (procY ψ η ν 0) P :=
      integrable_map_measure aestronglyMeasurable_id (hy 0).aemeasurable
    rw [← k1, hlaw, k2]
    exact hint0
  · have habs : Continuous (fun x : ℝ => |x|) := continuous_abs
    have k1 : ∫ x, |x| ∂(P.map (procY ψ η ν t)) = ∫ ω, |procY ψ η ν t ω| ∂P :=
      integral_map (hy t).aemeasurable habs.aestronglyMeasurable
    have k2 : ∫ x, |x| ∂(P.map (procY ψ η ν 0)) = ∫ ω, |procY ψ η ν 0 ω| ∂P :=
      integral_map (hy 0).aemeasurable habs.aestronglyMeasurable
    rw [← k1, hlaw, k2]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => abs_of_nonneg (hnn0 ω))

lemma tsum_one_div_eq_top :
    ∑' n : {n : ℕ // 1 ≤ n}, ENNReal.ofReal (1 / (n : ℝ)) = ⊤ := by
  rw [tsum_subtype_ge 1 (fun n : ℕ => ENNReal.ofReal (1 / (n : ℝ)))]
  have hind : Set.indicator {n : ℕ | 1 ≤ n} (fun n : ℕ => ENNReal.ofReal (1 / (n : ℝ)))
      = fun n : ℕ => ENNReal.ofReal (1 / (n : ℝ)) := by
    funext n
    by_cases h : 1 ≤ n
    · simp [Set.indicator, h]
    · have : n = 0 := by omega
      subst this; simp
  rw [hind]
  by_contra hne
  have hs := ENNReal.summable_toReal hne
  apply Real.not_summable_one_div_natCast
  refine hs.congr ?_
  intro n
  simp [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 1 / (n : ℝ))]

/-- key estimate: `P{ν_n > Γ(n+½)} ≥ ∑_{r ≥ n} 1/(r(r+1))` for `n ≥ 1` -/
lemma prob_nu_gt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Γ : ℝ → ℝ)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) (η : Ω → ℝ) (ν : ℕ → Ω → ℕ)
    (hC : IsConstruction Γ P η ν) (n : ℕ) (hn : 1 ≤ n) :
    ∑' r : {r : ℕ // n ≤ r}, cw r ≤ P {ω | Γ ((n : ℝ) + 1 / 2) < (ν n ω : ℝ)} := by
  have hmeas : MeasurableSet {m : ℕ | Γ ((n : ℝ) + 1 / 2) < (m : ℝ)} := by
    exact MeasurableSet.of_discrete
  have h1 : P {ω | Γ ((n : ℝ) + 1 / 2) < (ν n ω : ℝ)}
      = (P.map (ν n)) {m : ℕ | Γ ((n : ℝ) + 1 / 2) < (m : ℝ)} := by
    rw [Measure.map_apply (hC.measurable_nu n) hmeas]
    rfl
  rw [h1, hC.law_nu n, nuLaw, Measure.sum_apply _ hmeas]
  simp_rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  rw [tsum_subtype_ge n cw, tsum_subtype_ge 1 (fun i : ℕ => ENNReal.ofReal (1 / ((i : ℝ) * ((i : ℝ) + 1))) * {m : ℕ | Γ ((n : ℝ) + 1 / 2) < (m : ℝ)}.indicator 1 (nextAbove Γ i))]
  apply ENNReal.tsum_le_tsum
  intro r
  by_cases hr : n ≤ r
  · have hr1 : 1 ≤ r := le_trans hn hr
    simp only [Set.indicator, Set.mem_setOf_eq, hr, hr1, if_true]
    have hmem : nextAbove Γ r ∈ {m : ℕ | Γ ((n : ℝ) + 1 / 2) < (m : ℝ)} := by
      simp only [Set.mem_setOf_eq, nextAbove]
      push_cast
      have hle : Γ ((n : ℝ) + 1 / 2) ≤ Γ ((r : ℝ) + 1 / 2) := by
        apply hΓmono
        · simp only [Set.mem_Ioi]; positivity
        · simp only [Set.mem_Ioi]; positivity
        · have : (n : ℝ) ≤ r := by exact_mod_cast hr
          linarith
      exact lt_of_le_of_lt hle (Nat.lt_floor_add_one _)
    have hlt : Γ ((n : ℝ) + 1 / 2) < (nextAbove Γ r : ℝ) := hmem
    rw [if_pos hlt]
    simp [cw]
  · simp [Set.indicator, hr]

/-- Kingman's divergence estimate -/
theorem series_divergent_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Γ : ℝ → ℝ) (hΓpos : ∀ t : ℝ, 0 < t → 0 < Γ t)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) (η : Ω → ℝ) (ν : ℕ → Ω → ℕ)
    (hC : IsConstruction Γ P η ν) :
    (∑' n : {n : ℕ // 1 ≤ n}, ∑' r : {r : ℕ // (n : ℕ) ≤ r},
        ENNReal.ofReal (1 / ((r : ℝ) * ((r : ℝ) + 1))))
        ≤ ∑' n : {n : ℕ // 1 ≤ n}, P {ω | Γ ((n : ℝ) + 1 / 2) < (ν n ω : ℝ)} ∧
      (∑' n : {n : ℕ // 1 ≤ n}, ∑' r : {r : ℕ // (n : ℕ) ≤ r},
        ENNReal.ofReal (1 / ((r : ℝ) * ((r : ℝ) + 1)))) = ⊤ := by
  constructor
  · apply ENNReal.tsum_le_tsum
    intro n
    exact prob_nu_gt P Γ hΓmono η ν hC n n.2
  · have : ∀ n : {n : ℕ // 1 ≤ n}, ∑' r : {r : ℕ // (n : ℕ) ≤ r},
        ENNReal.ofReal (1 / ((r : ℝ) * ((r : ℝ) + 1))) = ENNReal.ofReal (1 / (n : ℝ)) :=
      fun n => tsum_cw_eq n n.2
    simp_rw [this]
    exact tsum_one_div_eq_top


/-- `η ∈ (0,1)` almost surely -/
lemma ae_eta_mem {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Γ : ℝ → ℝ) (η : Ω → ℝ)
    (ν : ℕ → Ω → ℕ) (hC : IsConstruction Γ P η ν) :
    ∀ᵐ ω ∂P, η ω ∈ Set.Ioo (0 : ℝ) 1 := by
  have h : ∀ᵐ x ∂(P.map η), x ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [hC.law_eta]
    exact ae_restrict_mem measurableSet_Ioo
  exact (ae_map_iff hC.measurable_eta.aemeasurable measurableSet_Ioo).1 h

/-- value of the process at the sampling times -/
lemma procY_at_sample {Ω : Type*} (ψ : ℝ → ℝ) (hψ : IsBump ψ) (η : Ω → ℝ) (ν : ℕ → Ω → ℕ)
    (n : ℕ) (ω : Ω) (hν : 1 ≤ ν n ω) :
    procY ψ η ν ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω) ω = (ν n ω : ℝ) := by
  unfold procY bigY
  have hpos : (0 : ℝ) < (ν n ω : ℝ) := by exact_mod_cast hν
  have h1 : (1 : ℝ) ≤ (ν n ω : ℝ) := by exact_mod_cast hν
  have hinv : (ν n ω : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  have hinvpos : 0 < (ν n ω : ℝ)⁻¹ := inv_pos.mpr hpos
  have hs : (n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω + η ω = (n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ := by ring
  rw [hs]
  have hfl : ⌊(n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹⌋₊ = n := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · linarith
    · linarith
  rw [hfl]
  have : (ν n ω : ℝ) * ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - (n : ℝ)) = 1 / 2 := by
    field_simp
    ring
  rw [this, hψ.2.2.2, mul_one]

/-- the events `ν_n > Γ(n+½)` are independent -/
lemma iIndepSet_nu_gt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Γ : ℝ → ℝ) (η : Ω → ℝ) (ν : ℕ → Ω → ℕ) (hC : IsConstruction Γ P η ν) :
    iIndepSet (fun n : ℕ => {ω | Γ ((n : ℝ) + 1 / 2) < (ν n ω : ℝ)}) P := by
  have hmeas : ∀ n : ℕ, MeasurableSet {ω | Γ ((n : ℝ) + 1 / 2) < (ν n ω : ℝ)} := by
    intro n
    exact hC.measurable_nu n (MeasurableSet.of_discrete (s := {m : ℕ | Γ ((n : ℝ) + 1 / 2) < (m : ℝ)}))
  rw [iIndepSet_iff_meas_biInter hmeas]
  intro S
  have h := hC.iIndep_nu.measure_inter_preimage_eq_mul S
    (sets := fun n : ℕ => {m : ℕ | Γ ((n : ℝ) + 1 / 2) < (m : ℝ)})
    (fun n _ => MeasurableSet.of_discrete)
  exact h

/-- the reduction of Theorem 3 to the integer variables -/
theorem reduction_to_nu_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Γ : ℝ → ℝ) (hΓpos : ∀ t : ℝ, 0 < t → 0 < Γ t)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) (ψ : ℝ → ℝ) (hψ : IsBump ψ) (η : Ω → ℝ)
    (ν : ℕ → Ω → ℕ) (hC : IsConstruction Γ P η ν) :
    P {ω | ∀ᶠ t in atTop, |procY ψ η ν t ω| ≤ Γ t}
        ≤ P {ω | ∀ᶠ n : ℕ in atTop,
            |procY ψ η ν ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω) ω|
              ≤ Γ ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω)} ∧
      P {ω | ∀ᶠ n : ℕ in atTop,
            |procY ψ η ν ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω) ω|
              ≤ Γ ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω)}
        ≤ P {ω | ∀ᶠ n : ℕ in atTop, (ν n ω : ℝ) ≤ Γ ((n : ℝ) + 1 / 2)} ∧
      P {ω | ∀ᶠ n : ℕ in atTop, (ν n ω : ℝ) ≤ Γ ((n : ℝ) + 1 / 2)} = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · apply measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have htend : Tendsto (fun n : ℕ => (n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω) atTop atTop := by
      have h1 : Tendsto (fun n : ℕ => (n : ℝ) - η ω) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      refine tendsto_atTop_mono (fun n => ?_) h1
      have : 0 ≤ 1 / 2 * (ν n ω : ℝ)⁻¹ := by positivity
      linarith
    exact htend.eventually hω
  · apply measure_mono_ae
    filter_upwards [ae_eta_mem P Γ η ν hC] with ω hη
    intro hω
    have hω' : ∀ᶠ n : ℕ in atTop,
        |procY ψ η ν ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω) ω|
          ≤ Γ ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω) := hω
    show ∀ᶠ n : ℕ in atTop, (ν n ω : ℝ) ≤ Γ ((n : ℝ) + 1 / 2)
    clear hω
    rw [eventually_atTop] at hω' ⊢
    rename_i _
    have hω := hω'
    obtain ⟨N, hN⟩ := hω
    refine ⟨max N 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    have h := hN n hnN
    by_cases hν : ν n ω = 0
    · rw [hν]
      push_cast
      exact le_of_lt (hΓpos _ (by positivity))
    · have hν1 : 1 ≤ ν n ω := Nat.one_le_iff_ne_zero.mpr hν
      rw [procY_at_sample ψ hψ η ν n ω hν1] at h
      have hpos : (0 : ℝ) < (ν n ω : ℝ) := by exact_mod_cast hν1
      rw [abs_of_pos hpos] at h
      refine le_trans h ?_
      have h1 : (1 : ℝ) ≤ (ν n ω : ℝ) := by exact_mod_cast hν1
      have hinv : (ν n ω : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
      have hinvpos : 0 < (ν n ω : ℝ)⁻¹ := inv_pos.mpr hpos
      have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      apply hΓmono
      · simp only [Set.mem_Ioi]; linarith [hη.2]
      · simp only [Set.mem_Ioi]; positivity
      · linarith [hη.1]
  · set s : ℕ → Set Ω := fun n => {ω | Γ ((n : ℝ) + 1 / 2) < (ν n ω : ℝ)} with hs_def
    have hmeas : ∀ n : ℕ, MeasurableSet (s n) := by
      intro n
      exact hC.measurable_nu n (MeasurableSet.of_discrete (s := {m : ℕ | Γ ((n : ℝ) + 1 / 2) < (m : ℝ)}))
    have hsum : ∑' n : ℕ, P (s n) = ⊤ := by
      apply eq_top_iff.mpr
      rw [← (series_divergent_core P Γ hΓpos hΓmono η ν hC).2]
      refine le_trans (series_divergent_core P Γ hΓpos hΓmono η ν hC).1 ?_
      rw [tsum_subtype_ge 1 (fun n : ℕ => P (s n))]
      apply ENNReal.tsum_le_tsum
      intro n
      exact Set.indicator_le_self _ _ n
    have hone := measure_limsup_eq_one hmeas (iIndepSet_nu_gt P Γ η ν hC) hsum
    have hcompl : {ω | ∀ᶠ n : ℕ in atTop, (ν n ω : ℝ) ≤ Γ ((n : ℝ) + 1 / 2)}
        = (limsup s atTop)ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, mem_limsup_iff_frequently_mem,
        Filter.not_frequently, hs_def, not_lt]
    rw [hcompl, prob_compl_eq_one_sub (MeasurableSet.measurableSet_limsup hmeas), hone, tsub_self]


/-- a bump function exists -/
lemma exists_isBump : ∃ ψ : ℝ → ℝ, IsBump ψ := by
  let f : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · exact f.contDiff
  · intro x hx
    have hsupp := f.support_eq
    rw [Real.ball_eq_Ioo] at hsupp
    have : x ∉ Function.support f := by
      rw [hsupp]
      have e : (1 / 2 : ℝ) - 1 / 4 = 1 / 4 := by norm_num
      have e' : (1 / 2 : ℝ) + 1 / 4 = 3 / 4 := by norm_num
      rw [show f.rOut = 1 / 4 from rfl, e, e']
      exact hx
    exact Function.notMem_support.mp this
  · intro x
    refine ⟨f.nonneg, ?_⟩
    rw [f.one_of_mem_closedBall (Metric.mem_closedBall_self f.rIn_pos.le)]
    exact f.le_one
  · exact f.one_of_mem_closedBall (Metric.mem_closedBall_self f.rIn_pos.le)

instance uniform_isProbabilityMeasure : IsProbabilityMeasure (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioo]
  simp

/-- the canonical construction on `ℝ × (ℕ → ℕ)` -/
lemma isConstruction_canonical (Γ : ℝ → ℝ) :
    haveI := nuLaw_isProbabilityMeasure Γ
    IsConstruction Γ ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (Measure.infinitePi (fun _ : ℕ => nuLaw Γ)))
      (Prod.fst : ℝ × (ℕ → ℕ) → ℝ) (fun r (p : ℝ × (ℕ → ℕ)) => p.2 r) := by
  haveI := nuLaw_isProbabilityMeasure Γ
  set π := Measure.infinitePi (fun _ : ℕ => nuLaw Γ) with hπ
  set P := (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod π with hP
  have hmν : ∀ r : ℕ, Measurable (fun p : ℝ × (ℕ → ℕ) => p.2 r) :=
    fun r => (measurable_pi_apply r).comp measurable_snd
  have hlawν : ∀ r : ℕ, P.map (fun p : ℝ × (ℕ → ℕ) => p.2 r) = nuLaw Γ := by
    intro r
    have : (fun p : ℝ × (ℕ → ℕ) => p.2 r) = (fun v : ℕ → ℕ => v r) ∘ Prod.snd := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply r) measurable_snd, hP,
      Measure.map_snd_prod, measure_univ, one_smul, hπ, Measure.infinitePi_map_eval]
  refine ⟨measurable_fst, hmν, ?_, hlawν, ?_, ?_⟩
  · rw [hP, Measure.map_fst_prod, measure_univ, one_smul]
  · rw [indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
      (measurable_pi_iff.2 hmν).aemeasurable]
    have e1 : (fun p : ℝ × (ℕ → ℕ) => (p.1, fun r => p.2 r)) = id := rfl
    have hsnd : P.map Prod.snd = π := by
      rw [hP, Measure.map_snd_prod, measure_univ, one_smul]
    have hfst : P.map Prod.fst = volume.restrict (Set.Ioo (0 : ℝ) 1) := by
      rw [hP, Measure.map_fst_prod, measure_univ, one_smul]
    rw [e1, Measure.map_id]
    exact (hfst ▸ hsnd ▸ hP : P = (P.map Prod.fst).prod (P.map Prod.snd))
  · rw [iIndepFun_iff_map_fun_eq_infinitePi_map hmν]
    simp only [hlawν]
    have hsnd : P.map Prod.snd = π := by
      rw [hP, Measure.map_snd_prod, measure_univ, one_smul]
    exact hsnd

/-- **Theorem 3** -/
theorem theorem_3_core (Γ : ℝ → ℝ) (hΓpos : ∀ t : ℝ, 0 < t → 0 < Γ t)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
      ∃ y : ℝ → Ω → ℝ,
        (∀ t : ℝ, 0 ≤ t → Measurable (y t)) ∧
        HasStationaryIncrements P y ∧
        (∀ t : ℝ, 0 ≤ t → Integrable (y t) P) ∧
        (∀ ω : Ω, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => y t ω) (Set.Ici 0)) ∧
        P {ω | ∀ᶠ t in atTop, |y t ω| ≤ Γ t} = 0 := by
  haveI := nuLaw_isProbabilityMeasure Γ
  obtain ⟨ψ, hψ⟩ := exists_isBump
  set π := Measure.infinitePi (fun _ : ℕ => nuLaw Γ) with hπ
  set P := (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod π with hP
  have hC := isConstruction_canonical Γ
  set η : ℝ × (ℕ → ℕ) → ℝ := Prod.fst with hη
  set ν : ℕ → ℝ × (ℕ → ℕ) → ℕ := fun r p => p.2 r with hν
  refine ⟨ℝ × (ℕ → ℕ), inferInstance, P, inferInstance, procY ψ η ν, ?_, ?_, ?_, ?_, ?_⟩
  · intro t _
    exact (measurable_bigY_state ψ hψ.1.continuous t).comp
      (measurable_Smap η ν hC.measurable_eta hC.measurable_nu)
  · exact (stationary_smooth_core P Γ hΓpos hΓmono ψ hψ η ν hC).2.1
  · intro t ht
    exact (expectation_abs_core P Γ hΓpos hΓmono ψ hψ η ν hC t ht).1
  · exact (stationary_smooth_core P Γ hΓpos hΓmono ψ hψ η ν hC).2.2
  · obtain ⟨h1, h2, h3⟩ := reduction_to_nu_core P Γ hΓpos hΓmono ψ hψ η ν hC
    exact le_antisymm (h1.trans (h2.trans_eq h3)) bot_le

end KingmanSubadditive.StationaryIncrements

open KingmanSubadditive.StationaryIncrements


theorem solution (Γ : ℝ → ℝ) (hΓpos : ∀ t : ℝ, 0 < t → 0 < Γ t)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
      ∃ y : ℝ → Ω → ℝ,
        (∀ t : ℝ, 0 ≤ t → Measurable (y t)) ∧
        HasStationaryIncrements P y ∧
        (∀ t : ℝ, 0 ≤ t → Integrable (y t) P) ∧
        (∀ ω : Ω, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => y t ω) (Set.Ici 0)) ∧
        P {ω | ∀ᶠ t in atTop, |y t ω| ≤ Γ t} = 0 := by
  exact theorem_3_core Γ hΓpos hΓmono
