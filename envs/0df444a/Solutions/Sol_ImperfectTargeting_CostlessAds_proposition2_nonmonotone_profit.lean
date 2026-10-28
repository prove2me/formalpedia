-- Prove2me | solution 1 for ImperfectTargeting.CostlessAds.proposition2_nonmonotone_profit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T21:38:58.625835+00:00
-- url     : https://prove2.me/submissions/e8e1f8a5-688c-4fc2-aaf6-5c9a014bfb8f

import Mathlib
import Definitions.Def_ImperfectTargeting_CostlessAds_PricingGame
import Definitions.Def_ImperfectTargeting_CostlessAds_Setting

set_option autoImplicit false

open MeasureTheory Filter Topology Set

namespace ITCAProof

open ImperfectTargeting.CostlessAds

/-! ### The inner (rival-price) integral as measures of sets -/

lemma inner_eq (v L S p : ℝ) (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hp : p ≤ v) :
    ∫ q, profit v L S p q ∂ρ =
      p * L + ((p * S) * ρ.real (Ioi p) + (p * S / 2) * ρ.real {p}) := by
  have hv : ¬ v < p := not_lt.mpr hp
  have hfun : (fun q => profit v L S p q) = fun q =>
      p * L + ((p * S) * (Ioi p).indicator (1 : ℝ → ℝ) q
        + (p * S / 2) * ({p} : Set ℝ).indicator (1 : ℝ → ℝ) q) := by
    funext q
    rcases lt_trichotomy p q with h | h | h
    · have h1 : q ∈ Ioi p := h
      have h2 : q ∉ ({p} : Set ℝ) := by
        simp only [Set.mem_singleton_iff]; exact ne_of_gt h
      rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
      simp only [profit, hv, h, if_true, if_false, Pi.one_apply]; ring
    · subst h
      have h1 : p ∉ Ioi p := lt_irrefl p
      rw [Set.indicator_of_notMem h1, Set.indicator_of_mem (Set.mem_singleton p)]
      simp only [profit, hv, lt_irrefl, if_true, if_false, Pi.one_apply]; ring
    · have h1 : q ∉ Ioi p := not_lt.mpr h.le
      have h2 : q ∉ ({p} : Set ℝ) := by
        simp only [Set.mem_singleton_iff]; exact ne_of_lt h
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
      simp only [profit, hv, not_lt.mpr h.le, (ne_of_gt h), if_true, if_false]; ring
  have hi1 : Integrable ((Ioi p).indicator (1 : ℝ → ℝ)) ρ :=
    (integrable_const (1:ℝ)).indicator measurableSet_Ioi
  have hi2 : Integrable (({p} : Set ℝ).indicator (1 : ℝ → ℝ)) ρ :=
    (integrable_const (1:ℝ)).indicator (measurableSet_singleton p)
  have hi12 : Integrable (fun q => p * S * (Ioi p).indicator (1 : ℝ → ℝ) q
      + p * S / 2 * ({p} : Set ℝ).indicator (1 : ℝ → ℝ) q) ρ :=
    (hi1.const_mul _).add (hi2.const_mul _)
  rw [hfun, integral_add (integrable_const _) hi12,
    integral_add (hi1.const_mul _) (hi2.const_mul _),
    integral_const_mul (p * S / 2) (({p} : Set ℝ).indicator (1 : ℝ → ℝ)),
    integral_indicator_one (measurableSet_singleton p)]
  simp [integral_const_mul, integral_indicator_one measurableSet_Ioi]

/-! ### Continuous cdf pieces as Stieltjes functions -/

noncomputable def cdfF (p0 π L S cap x : ℝ) : ℝ := min cap (1 - (π / max x p0 - L) / S)

lemma cdfF_mono {p0 π L S cap : ℝ} (hp0 : 0 < p0) (hπ : 0 ≤ π) (hS : 0 < S) :
    Monotone (cdfF p0 π L S cap) := by
  intro x y hxy
  unfold cdfF
  apply min_le_min_left
  have hx0 : 0 < max x p0 := lt_of_lt_of_le hp0 (le_max_right _ _)
  have hm : max x p0 ≤ max y p0 := max_le_max hxy le_rfl
  have h1 : π / max y p0 ≤ π / max x p0 := div_le_div_of_nonneg_left hπ hx0 hm
  have h2 : (π / max y p0 - L) / S ≤ (π / max x p0 - L) / S :=
    div_le_div_of_nonneg_right (by linarith) hS.le
  linarith

lemma cdfF_cont {p0 π L S cap : ℝ} (hp0 : 0 < p0) : Continuous (cdfF p0 π L S cap) := by
  have hne : ∀ x : ℝ, max x p0 ≠ 0 := fun x => (lt_of_lt_of_le hp0 (le_max_right _ _)).ne'
  unfold cdfF
  exact continuous_const.min (continuous_const.sub
    (((continuous_const.div (continuous_id.max continuous_const) hne).sub
      continuous_const).div_const _))

noncomputable def stF (p0 π L S cap : ℝ) (hp0 : 0 < p0) (hπ : 0 ≤ π) (hS : 0 < S) :
    StieltjesFunction ℝ where
  toFun := cdfF p0 π L S cap
  mono' := cdfF_mono hp0 hπ hS
  right_continuous' _ := (cdfF_cont hp0).continuousWithinAt

/-- A mixed price strategy: continuous part on `[p0, v]` plus an atom of mass `a` at `v`. -/
lemma exists_strat (v p0 π L S a : ℝ) (hp0 : 0 < p0) (hpv : p0 < v) (hS : 0 < S) (hL : 0 ≤ L)
    (hπ : π = p0 * (L + S)) (ha : a = (π / v - L) / S) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧ ρ (Icc p0 v)ᶜ = 0 ∧
      (∀ x, x ≠ v → ρ {x} = 0) ∧ ρ.real {v} = a ∧
      (∀ x, x ≤ p0 → ρ.real (Ioi x) = 1) ∧
      (∀ x, p0 ≤ x → x < v → ρ.real (Ioi x) = (π / x - L) / S) ∧ ρ (Ioi v) = 0 := by
  have hv0 : 0 < v := hp0.trans hpv
  have hπ0 : 0 ≤ π := by rw [hπ]; have : 0 < L + S := by linarith
                         positivity
  set cap := 1 - a with hcap
  let F := stF p0 π L S cap hp0 hπ0 hS
  have hFx : ∀ x, F x = cdfF p0 π L S cap x := fun x => rfl
  have hlow : ∀ x, x ≤ p0 → F x = 0 := by
    intro x hx
    rw [hFx]; unfold cdfF
    rw [max_eq_right hx]
    have : 1 - (π / p0 - L) / S = 0 := by rw [hπ]; field_simp; ring
    rw [this]; exact min_eq_right (by linarith)
  have hexpr : ∀ x, p0 ≤ x → x ≤ v → 1 - (π / x - L) / S ≤ cap := by
    intro x hx hxv
    have hx0 : 0 < x := hp0.trans_le hx
    have : π / v ≤ π / x := div_le_div_of_nonneg_left hπ0 hx0 hxv
    have : (π / v - L) / S ≤ (π / x - L) / S := div_le_div_of_nonneg_right (by linarith) hS.le
    rw [hcap, ha]; linarith
  have hmid : ∀ x, p0 ≤ x → x ≤ v → F x = 1 - (π / x - L) / S := by
    intro x hx hxv
    rw [hFx]; unfold cdfF; rw [max_eq_left hx]; exact min_eq_right (hexpr x hx hxv)
  have hhigh : ∀ x, v ≤ x → F x = cap := by
    intro x hx
    rw [hFx]; unfold cdfF; rw [max_eq_left (hpv.le.trans hx)]
    apply min_eq_left
    have : π / x ≤ π / v := div_le_div_of_nonneg_left hπ0 hv0 hx
    have : (π / x - L) / S ≤ (π / v - L) / S := div_le_div_of_nonneg_right (by linarith) hS.le
    rw [hcap, ha]; linarith
  have hbot : Tendsto F atBot (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_le_atBot p0] with x hx; exact (hlow x hx).symm)
  have htop : Tendsto F atTop (𝓝 cap) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop v] with x hx; exact (hhigh x hx).symm)
  have hcont : Continuous F := cdfF_cont hp0
  have hsing : ∀ x, F.measure {x} = 0 := by
    intro x
    rw [StieltjesFunction.measure_singleton, (hcont.continuousWithinAt).leftLim_eq]; simp
  have hcap0 : 0 ≤ cap := by rw [hcap]; linarith
  have hIoi : ∀ x, F.measure (Ioi x) = ENNReal.ofReal (cap - F x) := fun x =>
    F.measure_Ioi htop x
  refine ⟨F.measure + ENNReal.ofReal a • Measure.dirac v, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    rw [Measure.add_apply, Measure.smul_apply, StieltjesFunction.measure_univ F hbot htop,
      Measure.dirac_apply_of_mem (mem_univ v), smul_eq_mul, mul_one, sub_zero,
      ← ENNReal.ofReal_add hcap0 ha0, show cap + a = 1 by rw [hcap]; ring]
    simp
  · rw [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Icc.compl,
      Set.indicator_of_notMem (by simp [hpv.le]), smul_eq_mul, mul_zero, add_zero]
    have hsub : (Icc p0 v)ᶜ ⊆ Iio p0 ∪ Ioi v := by
      intro x hx
      simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
      rcases hx with h | h
      · exact Or.inl h
      · exact Or.inr h
    apply measure_mono_null hsub
    apply measure_union_null
    · apply measure_mono_null Iio_subset_Iic_self
      rw [F.measure_Iic hbot, hlow p0 le_rfl]; simp
    · rw [hIoi, hhigh v le_rfl]; simp
  · intro x hx
    rw [Measure.add_apply, Measure.smul_apply, hsing,
      Measure.dirac_apply' _ (measurableSet_singleton x),
      Set.indicator_of_notMem (by simpa using hx.symm)]
    simp
  · rw [Measure.real, Measure.add_apply, Measure.smul_apply, hsing,
      Measure.dirac_apply_of_mem (mem_singleton v)]
    simp [ha0]
  · intro x hx
    rw [Measure.real, Measure.add_apply, Measure.smul_apply, hIoi, hlow x hx,
      Measure.dirac_apply_of_mem (show v ∈ Ioi x from lt_of_le_of_lt hx hpv),
      smul_eq_mul, mul_one, sub_zero, ← ENNReal.ofReal_add hcap0 ha0,
      show cap + a = 1 by rw [hcap]; ring]
    simp
  · intro x hx hxv
    have h0 : 0 ≤ cap - F x := by rw [hmid x hx hxv.le]; linarith [hexpr x hx hxv.le]
    rw [Measure.real, Measure.add_apply, Measure.smul_apply, hIoi,
      Measure.dirac_apply_of_mem (show v ∈ Ioi x from hxv),
      smul_eq_mul, mul_one, ← ENNReal.ofReal_add h0 ha0, ENNReal.toReal_ofReal (by linarith),
      hmid x hx hxv.le, hcap]
    ring
  · rw [Measure.add_apply, Measure.smul_apply, hIoi, hhigh v le_rfl,
      Measure.dirac_apply' _ measurableSet_Ioi,
      Set.indicator_of_notMem (show v ∉ Ioi v from lt_irrefl v)]
    simp

/-- Deviation payoffs against a strategy of the shape built by `exists_strat`. -/
lemma dev (v L S π p0 a : ℝ) (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hS : 0 < S)
    (hL : 0 ≤ L) (hp0 : 0 < p0) (hpv : p0 < v) (hπ : π = p0 * (L + S))
    (ha : a = (π / v - L) / S) (ha0 : 0 ≤ a)
    (h3 : ∀ x, x ≠ v → ρ {x} = 0) (h3b : ρ.real {v} = a)
    (h4 : ∀ x, x ≤ p0 → ρ.real (Ioi x) = 1)
    (h5 : ∀ x, p0 ≤ x → x < v → ρ.real (Ioi x) = (π / x - L) / S) (h6 : ρ (Ioi v) = 0) :
    (∀ p, ∫ q, profit v L S p q ∂ρ ≤ π) ∧
    (∀ p, p0 ≤ p → p < v → ∫ q, profit v L S p q ∂ρ = π) ∧
    (a = 0 → ∫ q, profit v L S v q ∂ρ = π) := by
  have hv0 : 0 < v := hp0.trans hpv
  have hπ0 : 0 < π := by rw [hπ]; have : 0 < L + S := by linarith
                         positivity
  have hsing : ∀ x, x ≠ v → ρ.real {x} = 0 := fun x hx => by simp [Measure.real, h3 x hx]
  have hatv : ∫ q, profit v L S v q ∂ρ = v * L + (v * S * 0 + v * S / 2 * a) := by
    rw [inner_eq v L S v ρ le_rfl, h3b]; simp [Measure.real, h6]
  have hπv : π = v * L + v * S * a := by rw [ha]; field_simp; ring
  have hmid : ∀ p, p0 ≤ p → p < v → ∫ q, profit v L S p q ∂ρ = π := by
    intro p hp hpv'
    have hp' : 0 < p := hp0.trans_le hp
    rw [inner_eq v L S p ρ hpv'.le, h5 p hp hpv', hsing p hpv'.ne]
    field_simp; ring
  refine ⟨?_, hmid, ?_⟩
  · intro p
    rcases lt_or_ge v p with hvp | hpv'
    · have : (fun q => profit v L S p q) = fun _ => 0 := by
        funext q; simp [profit, hvp]
      rw [this, integral_zero]; exact hπ0.le
    rcases eq_or_lt_of_le hpv' with h | h
    · rw [h, hatv, hπv]
      nlinarith [mul_nonneg (mul_nonneg hv0.le hS.le) ha0]
    · rcases le_or_gt p0 p with h' | h'
      · exact (hmid p h' h).le
      · rw [inner_eq v L S p ρ h.le, h4 p h'.le, hsing p h.ne, hπ]
        nlinarith
  · intro h
    rw [hatv, hπv, h]; ring

lemma exp_eq (g : ℝ → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : Set ℝ) (hs : μ sᶜ = 0)
    (c : ℝ) (hg : ∀ x ∈ s, g x = c) : ∫ x, g x ∂μ = c := by
  have h : ∀ᵐ x ∂μ, g x = c := by
    rw [ae_iff]; exact measure_mono_null (fun x hx hxs => hx (hg x hxs)) hs
  rw [integral_congr_ae h]; simp

lemma ne_swap {v1 L1 v2 L2 S : ℝ} {μ ν : Measure ℝ} (h : IsClearinghouseNE v1 L1 v2 L2 S μ ν) :
    IsClearinghouseNE v2 L2 v1 L1 S ν μ := ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

/-- The mixed-price equilibrium of a clearinghouse duopoly with common valuation `v`. -/
lemma mixed_NE (v L1 L2 S : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) (hL1 : 0 ≤ L1) (h12 : L1 ≤ L2)
    (hL2 : 0 < L2) (hS : 0 < S) :
    ∃ μ ν : Measure ℝ, IsClearinghouseNE v L1 v L2 S μ ν ∧
      expProfit v L1 S μ ν = v * L2 * (L1 + S) / (L2 + S) ∧
      expProfit v L2 S ν μ = v * L2 * (L2 + S) / (L2 + S) := by
  set p0 := v * L2 / (L2 + S) with hp0def
  have hLS : 0 < L2 + S := by linarith
  have hp0 : 0 < p0 := by positivity
  have hpv : p0 < v := by rw [hp0def, div_lt_iff₀ hLS]; nlinarith
  have hpa : (0:ℝ) = (p0 * (L2 + S) / v - L2) / S := by
    rw [hp0def]; field_simp; ring
  have hpb : (L2 - L1) / (L2 + S) = (p0 * (L1 + S) / v - L1) / S := by
    rw [hp0def]; field_simp; ring
  have hb0 : 0 ≤ (L2 - L1) / (L2 + S) := div_nonneg (by linarith) hLS.le
  have hb1 : (L2 - L1) / (L2 + S) ≤ 1 := by rw [div_le_one hLS]; linarith
  obtain ⟨μ, hμP, hμ2, hμ3, hμ3b, hμ4, hμ5, hμ6⟩ :=
    exists_strat v p0 (p0 * (L2 + S)) L2 S 0 hp0 hpv hS hL2.le rfl hpa le_rfl zero_le_one
  obtain ⟨ν, hνP, hν2, hν3, hν3b, hν4, hν5, hν6⟩ :=
    exists_strat v p0 (p0 * (L1 + S)) L1 S _ hp0 hpv hS hL1 rfl hpb hb0 hb1
  have dμ := dev v L2 S (p0 * (L2 + S)) p0 0 μ hS hL2.le hp0 hpv rfl hpa le_rfl
    hμ3 hμ3b hμ4 hμ5 hμ6
  have dν := dev v L1 S (p0 * (L1 + S)) p0 _ ν hS hL1 hp0 hpv rfl hpb hb0
    hν3 hν3b hν4 hν5 hν6
  have hμv : μ {v} = 0 := by
    have := hμ3b
    rw [Measure.real, ENNReal.toReal_eq_zero_iff] at this
    exact this.resolve_right (measure_ne_top μ _)
  have e1 : expProfit v L1 S μ ν = p0 * (L1 + S) := by
    unfold expProfit
    apply exp_eq _ μ (Ico p0 v)
    · have hsub : (Ico p0 v)ᶜ ⊆ (Icc p0 v)ᶜ ∪ {v} := by
        intro x hx
        simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_Icc,
          Set.mem_Ico] at hx ⊢
        by_cases h : x = v
        · exact Or.inr h
        · exact Or.inl (fun hc => hx ⟨hc.1, lt_of_le_of_ne hc.2 h⟩)
      exact measure_mono_null hsub (measure_union_null hμ2 hμv)
    · intro x hx; exact dν.2.1 x hx.1 hx.2
  have e2 : expProfit v L2 S ν μ = p0 * (L2 + S) := by
    unfold expProfit
    apply exp_eq _ ν (Icc p0 v) hν2
    intro x hx
    rcases eq_or_lt_of_le hx.2 with h | h
    · rw [h]; exact dμ.2.2 rfl
    · exact dμ.2.1 x hx.1 h
  refine ⟨μ, ν, ⟨⟨hμP, ?_⟩, ⟨hνP, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · exact measure_mono_null (compl_subset_compl.mpr (Icc_subset_Icc hp0.le hv1)) hμ2
  · exact measure_mono_null (compl_subset_compl.mpr (Icc_subset_Icc hp0.le hv1)) hν2
  · intro p'; rw [e1]; exact dν.1 p'
  · intro q'; rw [e2]; exact dμ.1 q'
  · rw [e1, hp0def]; field_simp
  · rw [e2, hp0def]; field_simp

/-- Bertrand subgame: no loyal consumers, both firms price at `0`. -/
lemma bertrand_NE (v S : ℝ) (hv : 0 ≤ v) (hS : 0 < S) :
    IsClearinghouseNE v 0 v 0 S (Measure.dirac 0) (Measure.dirac 0) ∧
      expProfit v 0 S (Measure.dirac 0) (Measure.dirac 0) = 0 := by
  have hstrat : IsStrategy (Measure.dirac (0:ℝ)) := by
    refine ⟨inferInstance, ?_⟩
    rw [Measure.dirac_apply' _ measurableSet_Icc.compl, Set.indicator_of_notMem (by simp)]
  have hval : ∀ p, ∫ q, profit v 0 S p q ∂(Measure.dirac (0:ℝ)) = profit v 0 S p 0 :=
    fun p => integral_dirac _ _
  have he : expProfit v 0 S (Measure.dirac 0) (Measure.dirac 0) = 0 := by
    unfold expProfit; simp only [integral_dirac]; simp [profit, not_lt.mpr hv]
  have hle : ∀ p, profit v 0 S p 0 ≤ 0 := by
    intro p; unfold profit; split_ifs with h1 h2 h3 <;> nlinarith
  refine ⟨⟨hstrat, hstrat, ?_, ?_⟩, he⟩
  · intro p; rw [he, hval]; exact hle p
  · intro q; rw [he, hval]; exact hle q

/-- Separated markets: each firm is a monopolist on its own consumers and prices at valuation. -/
lemma mono_NE (v1 L1 v2 L2 : ℝ) (hv1 : 0 ≤ v1) (hv1' : v1 ≤ 1) (hv2 : 0 ≤ v2) (hv2' : v2 ≤ 1)
    (hL1 : 0 ≤ L1) (hL2 : 0 ≤ L2) :
    IsClearinghouseNE v1 L1 v2 L2 0 (Measure.dirac v1) (Measure.dirac v2) ∧
      expProfit v1 L1 0 (Measure.dirac v1) (Measure.dirac v2) = v1 * L1 ∧
      expProfit v2 L2 0 (Measure.dirac v2) (Measure.dirac v1) = v2 * L2 := by
  have hp : ∀ v L p q : ℝ, profit v L 0 p q = if v < p then 0 else p * L := by
    intro v L p q; unfold profit; split_ifs <;> simp
  have hstrat : ∀ w : ℝ, 0 ≤ w → w ≤ 1 → IsStrategy (Measure.dirac w) := by
    intro w h0 h1
    refine ⟨inferInstance, ?_⟩
    rw [Measure.dirac_apply' _ measurableSet_Icc.compl, Set.indicator_of_notMem (by simp [h0, h1])]
  have hdev : ∀ v L w p : ℝ, 0 ≤ v → 0 ≤ L →
      ∫ q, profit v L 0 p q ∂(Measure.dirac w) ≤ v * L := by
    intro v L w p hv hL
    rw [integral_dirac, hp]
    split_ifs with h
    · positivity
    · nlinarith
  have he : ∀ v L w : ℝ, expProfit v L 0 (Measure.dirac v) (Measure.dirac w) = v * L := by
    intro v L w
    unfold expProfit
    simp only [integral_dirac]
    rw [hp, if_neg (lt_irrefl v)]
  refine ⟨⟨hstrat v1 hv1 hv1', hstrat v2 hv2 hv2', ?_, ?_⟩, he v1 L1 v2, he v2 L2 v1⟩
  · intro p; rw [he]; exact hdev v1 L1 v2 p hv1 hL1
  · intro q; rw [he]; exact hdev v2 L2 v1 q hv2 hL2

/-- Common valuation: an equilibrium with payoffs given through `max L1 L2`. -/
lemma same_NE (v L1 L2 S : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) (hL1 : 0 ≤ L1) (hL2 : 0 ≤ L2)
    (hS : 0 < S) :
    ∃ μ ν : Measure ℝ, IsClearinghouseNE v L1 v L2 S μ ν ∧
      expProfit v L1 S μ ν = v * max L1 L2 * (L1 + S) / (max L1 L2 + S) ∧
      expProfit v L2 S ν μ = v * max L1 L2 * (L2 + S) / (max L1 L2 + S) := by
  rcases le_total L1 L2 with h | h
  · rw [max_eq_right h]
    rcases eq_or_lt_of_le hL2 with h0 | h0
    · subst h0
      have h1 : L1 = 0 := le_antisymm h hL1
      subst h1
      obtain ⟨hne, he⟩ := bertrand_NE v S hv.le hS
      exact ⟨_, _, hne, by rw [he]; simp, by rw [he]; simp⟩
    · exact mixed_NE v L1 L2 S hv hv1 hL1 h h0 hS
  · rw [max_eq_left h]
    rcases eq_or_lt_of_le hL1 with h0 | h0
    · subst h0
      have h1 : L2 = 0 := le_antisymm h hL2
      subst h1
      obtain ⟨hne, he⟩ := bertrand_NE v S hv.le hS
      exact ⟨_, _, hne, by rw [he]; simp, by rw [he]; simp⟩
    · obtain ⟨μ, ν, hne, e1, e2⟩ := mixed_NE v L2 L1 S hv hv1 hL2 h h0 hS
      exact ⟨ν, μ, ne_swap hne, e2, e1⟩

/-! ### Payoffs of the chosen continuation in each stage-1 subgame -/

noncomputable def P1 (A α : ℝ) (s : Action × Action) : ℝ :=
  if s.1.1 = s.2.1 then
    val A s.1.1 * max (loyal₁ α s) (loyal₂ α s) * (loyal₁ α s + shoppers α s) /
      (max (loyal₁ α s) (loyal₂ α s) + shoppers α s)
  else val A s.1.1 * loyal₁ α s

noncomputable def P2 (A α : ℝ) (s : Action × Action) : ℝ :=
  if s.1.1 = s.2.1 then
    val A s.2.1 * max (loyal₁ α s) (loyal₂ α s) * (loyal₂ α s + shoppers α s) /
      (max (loyal₁ α s) (loyal₂ α s) + shoppers α s)
  else val A s.2.1 * loyal₂ α s

lemma exists_cont (A α : ℝ) (hA0 : 0 < A) (hA1 : A ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1)
    (s : Action × Action) :
    ∃ μν : Measure ℝ × Measure ℝ, IsPricingNE A α s μν.1 μν.2 ∧
      U₁ A α s μν.1 μν.2 = P1 A α s ∧ U₂ A α s μν.1 μν.2 = P2 A α s := by
  have hval : ∀ g, 0 < val A g ∧ val A g ≤ 1 := by
    intro g; cases g <;> simp [val, hA0, hA1]
  have hreach : ∀ sc, 0 < reach α sc ∧ reach α sc ≤ 1 := by
    intro sc; cases sc <;> simp [reach, hα, hα1]
  obtain ⟨⟨g1, sc1⟩, ⟨g2, sc2⟩⟩ := s
  obtain ⟨hr1, hr1'⟩ := hreach sc1
  obtain ⟨hr2, hr2'⟩ := hreach sc2
  by_cases h : g1 = g2
  · subst h
    have hS : shoppers α ((g1, sc1), (g1, sc2)) = reach α sc1 * reach α sc2 := by
      simp [shoppers]
    have hL1 : loyal₁ α ((g1, sc1), (g1, sc2)) = reach α sc1 - reach α sc1 * reach α sc2 := by
      simp only [loyal₁, hS]
    have hL2 : loyal₂ α ((g1, sc1), (g1, sc2)) = reach α sc2 - reach α sc1 * reach α sc2 := by
      simp only [loyal₂, hS]
    obtain ⟨μ, ν, hne, e1, e2⟩ := same_NE (val A g1) (loyal₁ α ((g1, sc1), (g1, sc2)))
      (loyal₂ α ((g1, sc1), (g1, sc2))) (shoppers α ((g1, sc1), (g1, sc2)))
      (hval g1).1 (hval g1).2
      (by rw [hL1]; nlinarith [mul_nonneg hr1.le (sub_nonneg.mpr hr2')])
      (by rw [hL2]; nlinarith [mul_nonneg hr2.le (sub_nonneg.mpr hr1')])
      (by rw [hS]; positivity)
    refine ⟨(μ, ν), hne, ?_, ?_⟩
    · unfold U₁ P1; dsimp only; rw [if_pos rfl]; exact e1
    · unfold U₂ P2; dsimp only; rw [if_pos rfl]; exact e2
  · have hS : shoppers α ((g1, sc1), (g2, sc2)) = 0 := by simp [shoppers, h]
    have hL1 : 0 ≤ loyal₁ α ((g1, sc1), (g2, sc2)) := by
      simp only [loyal₁, hS]; linarith
    have hL2 : 0 ≤ loyal₂ α ((g1, sc1), (g2, sc2)) := by
      simp only [loyal₂, hS]; linarith
    obtain ⟨hne, e1, e2⟩ := mono_NE (val A g1) (loyal₁ α ((g1, sc1), (g2, sc2)))
      (val A g2) (loyal₂ α ((g1, sc1), (g2, sc2)))
      (hval g1).1.le (hval g1).2 (hval g2).1.le (hval g2).2 hL1 hL2
    refine ⟨(Measure.dirac (val A g1), Measure.dirac (val A g2)), ?_, ?_, ?_⟩
    · unfold IsPricingNE; dsimp only; rw [hS]; exact hne
    · unfold U₁ P1; dsimp only; rw [if_neg h, hS]; exact e1
    · unfold U₂ P2; dsimp only; rw [if_neg h, hS]; exact e2

lemma P_diff (A α : ℝ) (g1 g2 : Group) (h : g1 ≠ g2) (sc1 sc2 : Scope) :
    P1 A α ((g1, sc1), (g2, sc2)) = val A g1 * reach α sc1 ∧
      P2 A α ((g1, sc1), (g2, sc2)) = val A g2 * reach α sc2 := by
  have hS : shoppers α ((g1, sc1), (g2, sc2)) = 0 := by simp [shoppers, h]
  unfold P1 P2 loyal₁ loyal₂; dsimp only; rw [if_neg h, if_neg h, hS]; simp

lemma P_ae (A α : ℝ) (g : Group) (hα1 : α ≤ 1) :
    P1 A α ((g, Scope.all), (g, Scope.expected)) = val A g * (1 - α) ∧
      P2 A α ((g, Scope.all), (g, Scope.expected)) = val A g * (α * (1 - α)) := by
  have hS : shoppers α ((g, Scope.all), (g, Scope.expected)) = α := by simp [shoppers, reach]
  unfold P1 P2 loyal₁ loyal₂; dsimp only; rw [if_pos rfl, if_pos rfl, hS]
  simp only [reach]
  rw [show (α - α) = 0 by ring, max_eq_left (by linarith), show (1 - α + α) = 1 by ring]
  constructor <;> ring

lemma P_ea (A α : ℝ) (g : Group) (hα1 : α ≤ 1) :
    P1 A α ((g, Scope.expected), (g, Scope.all)) = val A g * (α * (1 - α)) ∧
      P2 A α ((g, Scope.expected), (g, Scope.all)) = val A g * (1 - α) := by
  have hS : shoppers α ((g, Scope.expected), (g, Scope.all)) = α := by simp [shoppers, reach]
  unfold P1 P2 loyal₁ loyal₂; dsimp only; rw [if_pos rfl, if_pos rfl, hS]
  simp only [reach]
  rw [show (α - α) = 0 by ring, max_eq_right (by linarith), show (1 - α + α) = 1 by ring]
  constructor <;> ring

lemma P_ee (A α : ℝ) (g : Group) (hα : 0 < α) :
    P1 A α ((g, Scope.expected), (g, Scope.expected)) = val A g * (α * (1 - α)) ∧
      P2 A α ((g, Scope.expected), (g, Scope.expected)) = val A g * (α * (1 - α)) := by
  have hS : shoppers α ((g, Scope.expected), (g, Scope.expected)) = α * α := by
    simp [shoppers, reach]
  unfold P1 P2 loyal₁ loyal₂; dsimp only; rw [if_pos rfl, hS]
  simp only [reach, max_self]
  rw [show (α - α * α + α * α) = α by ring]
  constructor <;> field_simp <;> ring

lemma P_aa (A α : ℝ) (g : Group) :
    P1 A α ((g, Scope.all), (g, Scope.all)) = 0 ∧
      P2 A α ((g, Scope.all), (g, Scope.all)) = 0 := by
  have hS : shoppers α ((g, Scope.all), (g, Scope.all)) = 1 := by simp [shoppers, reach]
  unfold P1 P2 loyal₁ loyal₂; dsimp only; rw [if_pos rfl, hS]
  simp [reach]

lemma msgCost_zero (sc : Scope) : msgCost 0 sc = 0 := by cases sc <;> simp [msgCost]

end ITCAProof

open MeasureTheory ImperfectTargeting.CostlessAds in
theorem solution (A : ℝ) (hA0 : 0 < A) (hA : A < 1 / 4) :
    1 / 2 < αhat2 A ∧
    αhat2 A < αhat1 A ∧
    (∀ α : ℝ, 1 / 2 < α → α < αhat2 A →
      ∃ (play : Action × Action) (cont : Action × Action → Measure ℝ × Measure ℝ),
        IsSPNE A α 0 play cont ∧ totalProfit A α 0 play cont = 1 - α ^ 2) ∧
    (∀ α : ℝ, αhat2 A < α → α ≤ 1 →
      ∃ (play : Action × Action) (cont : Action × Action → Measure ℝ × Measure ℝ),
        IsSPNE A α 0 play cont ∧ totalProfit A α 0 play cont = 1 + A) ∧
    StrictAntiOn (fun α : ℝ => 1 - α ^ 2) (Set.Ico (1 / 2) (αhat2 A)) ∧
    1 - αhat2 A ^ 2 < 1 + A := by
  have hsq : 0 < Real.sqrt (1 - 4 * A) := Real.sqrt_pos.mpr (by linarith)
  have hsq2 : Real.sqrt (1 - 4 * A) ^ 2 = 1 - 4 * A := Real.sq_sqrt (by linarith)
  have hsq1 : Real.sqrt (1 - 4 * A) < 1 - 2 * A := by
    nlinarith [sq_nonneg (Real.sqrt (1 - 4 * A) - (1 - 2 * A))]
  have h2 : 1 / 2 < αhat2 A := by unfold αhat2; linarith
  have h21 : αhat2 A < αhat1 A := by unfold αhat2 αhat1; linarith
  -- stage-1 values from the chosen continuation
  have hV : ∀ (α : ℝ), 1 / 2 < α → α ≤ 1 →
      ∃ cont : Action × Action → Measure ℝ × Measure ℝ,
        (∀ s, IsPricingNE A α s (cont s).1 (cont s).2) ∧
        (∀ s, V₁ A α 0 cont s = ITCAProof.P1 A α s) ∧ (∀ s, V₂ A α 0 cont s = ITCAProof.P2 A α s) := by
    intro α hα hα1
    choose cont hcont using ITCAProof.exists_cont A α hA0 (by linarith) (by linarith) hα1
    refine ⟨cont, fun s => (hcont s).1, fun s => ?_, fun s => ?_⟩
    · unfold V₁; rw [(hcont s).2.1, ITCAProof.msgCost_zero]; ring
    · unfold V₂; rw [(hcont s).2.2, ITCAProof.msgCost_zero]; ring
  refine ⟨h2, h21, ?_, ?_, ?_, ?_⟩
  · intro α hα1 hα2
    have hαA : α < 1 - A := by unfold αhat1 at h21; linarith
    have hα1' : α ≤ 1 := by linarith
    have hkey : A < α * (1 - α) := by
      unfold αhat2 at hα2
      nlinarith
    obtain ⟨cont, hne, hV1, hV2⟩ := hV α hα1 hα1'
    have hb := ITCAProof.P_ae A α Group.b hα1'
    refine ⟨((Group.b, Scope.all), (Group.b, Scope.expected)), cont, ⟨hne, ?_, ?_⟩, ?_⟩
    · intro a'
      rw [hV1, hV1]; dsimp only
      obtain ⟨g, sc⟩ := a'
      rw [hb.1]; simp only [val]
      cases g <;> cases sc
      · rw [(ITCAProof.P_diff A α Group.a Group.b (by decide) _ _).1]; simp only [val, reach]; nlinarith
      · rw [(ITCAProof.P_diff A α Group.a Group.b (by decide) _ _).1]; simp only [val, reach]; nlinarith
      · rw [(ITCAProof.P_ee A α Group.b (by linarith)).1]; simp only [val]; nlinarith
      · rw [hb.1]; simp [val]
    · intro a'
      rw [hV2, hV2]; dsimp only
      obtain ⟨g, sc⟩ := a'
      rw [hb.2]; simp only [val]
      cases g <;> cases sc
      · rw [(ITCAProof.P_diff A α Group.b Group.a (by decide) _ _).2]; simp only [val, reach]; nlinarith
      · rw [(ITCAProof.P_diff A α Group.b Group.a (by decide) _ _).2]; simp only [val, reach]; nlinarith
      · rw [hb.2]; simp [val]
      · rw [(ITCAProof.P_aa A α Group.b).2]; nlinarith
    · unfold totalProfit; rw [hV1, hV2, hb.1, hb.2]; simp only [val]; ring
  · intro α hα2 hα1
    have hα1' : 1 / 2 < α := by linarith
    have hkey : α * (1 - α) ≤ A := by
      unfold αhat2 at hα2
      nlinarith
    obtain ⟨cont, hne, hV1, hV2⟩ := hV α hα1' hα1
    have hd := ITCAProof.P_diff A α Group.b Group.a (by decide) Scope.all Scope.all
    refine ⟨((Group.b, Scope.all), (Group.a, Scope.all)), cont, ⟨hne, ?_, ?_⟩, ?_⟩
    · intro a'
      rw [hV1, hV1]; dsimp only
      obtain ⟨g, sc⟩ := a'
      rw [hd.1]; simp only [val, reach]
      cases g <;> cases sc
      · rw [(ITCAProof.P_ea A α Group.a hα1).1]; simp only [val]; nlinarith
      · rw [(ITCAProof.P_aa A α Group.a).1]; norm_num
      · rw [(ITCAProof.P_diff A α Group.b Group.a (by decide) _ _).1]; simp only [val, reach]; linarith
      · rw [hd.1]; simp only [val, reach]; norm_num
    · intro a'
      rw [hV2, hV2]; dsimp only
      obtain ⟨g, sc⟩ := a'
      rw [hd.2]; simp only [val, reach]
      cases g <;> cases sc
      · rw [(ITCAProof.P_diff A α Group.b Group.a (by decide) _ _).2]; simp only [val, reach]; nlinarith
      · rw [hd.2]; simp only [val, reach]; norm_num
      · rw [(ITCAProof.P_ae A α Group.b hα1).2]; simp only [val]; linarith
      · rw [(ITCAProof.P_aa A α Group.b).2]; linarith
    · unfold totalProfit; rw [hV1, hV2, hd.1, hd.2]; simp only [val, reach]; ring
  · intro x hx y hy hxy
    simp only
    have : 0 < x := by have := hx.1; linarith
    nlinarith
  · nlinarith [sq_nonneg (αhat2 A)]
