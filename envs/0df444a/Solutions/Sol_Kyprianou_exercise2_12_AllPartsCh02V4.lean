-- Prove2me | solution 1 for Kyprianou.exercise2_12_AllPartsCh02V4
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T23:17:16.748282+00:00
-- url     : https://prove2.me/submissions/8add8765-c6ec-49dc-88c9-1af1aa50d284

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_exists_readable

open MeasureTheory ProbabilityTheory Filter Complex Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Exercise212Helpers

/-! ### Section 1: General Independence, Characteristic Function, and Pullback Helpers -/

private lemma iIndepFun_fin2_of_indepFun
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {f g : Ω → E}
    (h : IndepFun f g P) :
    iIndepFun (fun (i : Fin 2) (ω : Ω) => if i = 0 then f ω else g ω) P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  have hS : S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {0, 1} := by
    by_cases h0 : (0 : Fin 2) ∈ S <;> by_cases h1 : (1 : Fin 2) ∈ S
    · right; right; right; ext i; fin_cases i <;> simp [h0, h1]
    · right; left; ext i; fin_cases i <;> simp [h0, h1]
    · right; right; left; ext i; fin_cases i <;> simp [h0, h1]
    · left; ext i; fin_cases i <;> simp [h0, h1]
  rcases hS with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · rw [Finset.prod_pair (by decide : (0 : Fin 2) ≠ 1)]
    have hinter : (⋂ i ∈ ({0, 1} : Finset (Fin 2)),
        (fun ω => if i = 0 then f ω else g ω) ⁻¹' sets i) =
        f ⁻¹' sets 0 ∩ g ⁻¹' sets 1 := by
      ext ω; simp
    rw [hinter]
    exact (indepFun_iff_measure_inter_preimage_eq_mul.mp h) (sets 0) (sets 1)
      (hsets 0 (by simp)) (hsets 1 (by simp))

private lemma indepFun_prod_fst_snd
    {Ω₁ Ω₂ E₁ E₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [MeasurableSpace E₁] [MeasurableSpace E₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {f : Ω₁ → E₁} {g : Ω₂ → E₂} :
    IndepFun (fun p : Ω₁ × Ω₂ => f p.1) (fun p : Ω₁ × Ω₂ => g p.2) (P₁.prod P₂) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t _ _
  have h1 : (fun p : Ω₁ × Ω₂ => f p.1) ⁻¹' s ∩ (fun p : Ω₁ × Ω₂ => g p.2) ⁻¹' t =
      (f ⁻¹' s) ×ˢ (g ⁻¹' t) := by ext ⟨a, b⟩; simp
  have h2 : (fun p : Ω₁ × Ω₂ => f p.1) ⁻¹' s = (f ⁻¹' s) ×ˢ Set.univ := by ext ⟨a, b⟩; simp
  have h3 : (fun p : Ω₁ × Ω₂ => g p.2) ⁻¹' t = Set.univ ×ˢ (g ⁻¹' t) := by ext ⟨a, b⟩; simp
  rw [h1, h2, h3, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod,
    measure_univ, measure_univ, mul_one, one_mul]

private lemma aemeasurable_of_isLevyProcess
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ} (hX : IsLevyProcess X P) (t : ℝ≥0) :
    AEMeasurable (X t) P := by
  have hid := hX.stationary_increments 0 t
  have heq : increment X 0 t = X t := by
    funext ω; simp [increment, congrFun hX.start_zero ω]
  rw [heq] at hid
  exact hid.aemeasurable_snd

private lemma identDistrib_of_charFun_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f g : Ω → ℝ} (hf : AEMeasurable f P) (hg : AEMeasurable g P)
    (hchar : ∀ ξ : ℝ, charFun (P.map f) ξ = charFun (P.map g) ξ) :
    IdentDistrib f g P P := by
  refine ⟨hf, hg, ?_⟩
  have : IsProbabilityMeasure (P.map f) := Measure.isProbabilityMeasure_map hf
  have : IsProbabilityMeasure (P.map g) := Measure.isProbabilityMeasure_map hg
  exact Measure.ext_of_charFun (funext hchar)

private lemma iIndepFun_of_joint_charFun
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ} (hX : ∀ i, AEMeasurable (X i) P)
    (hchar : ∀ u : Fin n → ℝ,
      ∫ ω, Complex.exp (↑(∑ i : Fin n, u i * X i ω) * Complex.I) ∂P =
        ∏ i : Fin n, charFun (P.map (X i)) (u i)) :
    iIndepFun X P := by
  rw [iIndepFun_iff_charFunDual_pi hX]
  intro L
  let u : Fin n → ℝ := fun i => L (Pi.single i (1 : ℝ))
  have hL : ∀ v : Fin n → ℝ, L v = ∑ i : Fin n, u i * v i := by
    intro v
    have hv : v = ∑ i : Fin n, v i • Pi.single i (1 : ℝ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have hLsingle : ∀ (i : Fin n) (x : ℝ),
      (L.comp (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℝ) i)) x = u i * x := by
    intro i x
    have hx : Pi.single i x = x • Pi.single i (1 : ℝ) := by
      ext j; by_cases h : j = i <;> simp [h]
    change L (Pi.single i x) = u i * x
    rw [hx, map_smul, smul_eq_mul, mul_comm]
  have hXvec : AEMeasurable (fun ω (i : Fin n) => X i ω) P := aemeasurable_pi_lambda _ hX
  rw [charFunDual_apply, integral_map hXvec (by fun_prop)]
  have hlhs : (∫ ω, Complex.exp (↑(L (fun i => X i ω)) * Complex.I) ∂P) =
      ∫ ω, Complex.exp (↑(∑ i : Fin n, u i * X i ω) * Complex.I) ∂P := by
    congr 1; funext ω; rw [hL]
  rw [hlhs, hchar u]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [charFunDual_apply, charFun_apply_real]
  congr 1; funext x
  rw [hLsingle i x]
  push_cast; rfl

private lemma isLevyProcess_pullback
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {φ : Ω' → Ω}
    (hmp : MeasurePreserving φ P' P)
    {X : ℝ≥0 → Ω → ℝ} (hX : IsLevyProcess X P) :
    IsLevyProcess (fun t ω' => X t (φ ω')) P' where
  start_zero := by funext ω'; exact congrFun hX.start_zero (φ ω')
  indep_increments := by
    intro n t ht
    have h0 := hX.indep_increments n t ht
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h0 ⊢
    intro S sets hsets
    have hpre : (⋂ i ∈ S, increment (fun s ω' => X s (φ ω')) (t i.castSucc) (t i.succ) ⁻¹' sets i) =
        φ ⁻¹' (⋂ i ∈ S, increment X (t i.castSucc) (t i.succ) ⁻¹' sets i) := by
      ext ω'; simp [increment]
    rw [hpre]
    have hm_each : ∀ i ∈ S, NullMeasurableSet (increment X (t i.castSucc) (t i.succ) ⁻¹' sets i) P := by
      intro i hi
      have hinc_ae : AEMeasurable (increment X (t i.castSucc) (t i.succ)) P :=
        (aemeasurable_of_isLevyProcess hX (t i.succ)).sub (aemeasurable_of_isLevyProcess hX (t i.castSucc))
      exact hinc_ae.nullMeasurable (hsets i hi)
    have hm_inter : NullMeasurableSet (⋂ i ∈ S, increment X (t i.castSucc) (t i.succ) ⁻¹' sets i) P :=
      NullMeasurableSet.biInter (Finset.countable_toSet S) hm_each
    rw [hmp.measure_preimage hm_inter, h0 S hsets]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hpre_i : increment (fun s ω' => X s (φ ω')) (t i.castSucc) (t i.succ) ⁻¹' sets i =
        φ ⁻¹' (increment X (t i.castSucc) (t i.succ) ⁻¹' sets i) := rfl
    rw [hpre_i, hmp.measure_preimage (hm_each i hi)]
  stationary_increments := by
    intro s h
    have hid := hX.stationary_increments s h
    have hf1 : AEMeasurable (increment X s (s + h)) P := hid.aemeasurable_fst
    have hf2 : AEMeasurable (increment X 0 h) P := hid.aemeasurable_snd
    have h1 : IdentDistrib (increment X s (s + h) ∘ φ) (increment X s (s + h)) P' P :=
      { aemeasurable_fst := hf1.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving
        aemeasurable_snd := hf1
        map_eq := by
          rw [← AEMeasurable.map_map_of_aemeasurable (by rwa [hmp.map_eq]) hmp.measurable.aemeasurable,
            hmp.map_eq] }
    have h2 : IdentDistrib (increment X 0 h ∘ φ) (increment X 0 h) P' P :=
      { aemeasurable_fst := hf2.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving
        aemeasurable_snd := hf2
        map_eq := by
          rw [← AEMeasurable.map_map_of_aemeasurable (by rwa [hmp.map_eq]) hmp.measurable.aemeasurable,
            hmp.map_eq] }
    exact (h1.trans hid).trans h2.symm
  cadlag_ae := hmp.quasiMeasurePreserving.ae hX.cadlag_ae

/-! ### Section 2: Càdlàg Composition and General Lévy Subordination -/

private lemma isCadlag_of_continuous {f : ℝ≥0 → ℝ} (hf : Continuous f) : IsCadlag f := by
  intro t
  refine ⟨hf.continuousAt.continuousWithinAt, f t, ?_⟩
  exact hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

private lemma isCadlag_comp_monotone {f : ℝ≥0 → ℝ} {g : ℝ≥0 → ℝ≥0}
    (hf : IsCadlag f) (hg : IsCadlag (fun t => (g t : ℝ))) (hmon : Monotone g) :
    IsCadlag (fun t => f (g t)) := by
  intro t
  constructor
  · have hg_rc : ContinuousWithinAt g (Set.Ici t) t := NNReal.tendsto_coe.mp (hg t).1
    have hmaps : Set.MapsTo g (Set.Ici t) (Set.Ici (g t)) := fun _ hs => hmon hs
    exact (hf (g t)).1.comp hg_rc hmaps
  · by_cases ht0 : t = 0
    · subst ht0
      refine ⟨f (g 0), ?_⟩
      have hemp : Set.Iio (0 : ℝ≥0) = ∅ := by ext x; simp
      rw [hemp, nhdsWithin_empty]
      exact tendsto_bot
    · have htpos : (0 : ℝ≥0) < t := pos_iff_ne_zero.mpr ht0
      have : (nhdsWithin t (Set.Iio t)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
      obtain ⟨L_r, hLr⟩ := (hg t).2
      have hLnn : 0 ≤ L_r :=
        ge_of_tendsto hLr (Eventually.of_forall fun s => (g s).coe_nonneg)
      let L : ℝ≥0 := ⟨L_r, hLnn⟩
      have hL_tend : Tendsto g (nhdsWithin t (Set.Iio t)) (nhds L) :=
        NNReal.tendsto_coe.mp hLr
      have hg_le_L : ∀ s < t, g s ≤ L := by
        intro s hst
        have hev : ∀ᶠ u in nhdsWithin t (Set.Iio t), g s ≤ g u := by
          have hmem : Set.Ioo s t ∈ nhdsWithin t (Set.Iio t) := Ioo_mem_nhdsLT hst
          filter_upwards [hmem] with u hu
          exact hmon (le_of_lt hu.1)
        exact ge_of_tendsto hL_tend hev
      by_cases hreach : ∃ s₀ < t, g s₀ = L
      · obtain ⟨s₀, hs₀, hgs₀⟩ := hreach
        refine ⟨f L, tendsto_const_nhds.congr' ?_⟩
        have hmem : Set.Ioo s₀ t ∈ nhdsWithin t (Set.Iio t) := Ioo_mem_nhdsLT hs₀
        filter_upwards [hmem] with s hs
        have h1 : L ≤ g s := hgs₀ ▸ hmon (le_of_lt hs.1)
        have h2 : g s ≤ L := hg_le_L s hs.2
        rw [le_antisymm h2 h1]
      · push Not at hreach
        obtain ⟨l, hl⟩ := (hf L).2
        refine ⟨l, hl.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hL_tend ?_)⟩
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact lt_of_le_of_ne (hg_le_L s hs) (hreach s hs)

private noncomputable def dyadicUp (m : ℕ) (x : ℝ≥0) : ℝ≥0 :=
  ((Nat.floor ((2 : ℝ) ^ m * (x : ℝ)) + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ m

private lemma dyadicUp_ge (m : ℕ) (x : ℝ≥0) : x ≤ dyadicUp m x := by
  dsimp only [dyadicUp]
  rw [← NNReal.coe_le_coe]
  push_cast
  have hpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  rw [le_div_iff₀ hpos, mul_comm]
  exact le_of_lt (Nat.lt_floor_add_one _)

private lemma dyadicUp_le (m : ℕ) (x : ℝ≥0) :
    (dyadicUp m x : ℝ) ≤ (x : ℝ) + 1 / (2 : ℝ) ^ m := by
  dsimp only [dyadicUp]
  push_cast
  have hpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  rw [div_le_iff₀ hpos]
  have hfl : (Nat.floor ((2 : ℝ) ^ m * (x : ℝ)) : ℝ) ≤ (2 : ℝ) ^ m * (x : ℝ) :=
    Nat.floor_le (by positivity)
  have hmul : ((x : ℝ) + 1 / (2 : ℝ) ^ m) * (2 : ℝ) ^ m = (2 : ℝ) ^ m * (x : ℝ) + 1 := by
    field_simp
  linarith

private lemma dyadicUp_tendsto (x : ℝ≥0) :
    Tendsto (fun m => dyadicUp m x) atTop (nhdsWithin x (Set.Ici x)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (Eventually.of_forall fun m => dyadicUp_ge m x)
  rw [← NNReal.tendsto_coe]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by
      have ht : Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have h1 := (tendsto_const_nhds (x := (x : ℝ))).add ht
      simpa [one_div_pow] using h1)
    (fun m => NNReal.coe_le_coe.mpr (dyadicUp_ge m x))
    (fun m => dyadicUp_le m x)

private lemma dyadicUp_mono (m : ℕ) : Monotone (dyadicUp m) := by
  intro x y hxy
  dsimp only [dyadicUp]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hfl : Nat.floor ((2 : ℝ) ^ m * (x : ℝ)) ≤ Nat.floor ((2 : ℝ) ^ m * (y : ℝ)) :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hxy) (by positivity))
  exact_mod_cast Nat.add_le_add_right hfl 1

private noncomputable def dyadicVal (m k : ℕ) : ℝ≥0 :=
  ((k + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ m

private lemma dyadicVal_mono (m : ℕ) : Monotone (dyadicVal m) := by
  intro a b hab
  dsimp only [dyadicVal]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.add_le_add_right hab 1

private lemma psi_re_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → ℝ} {Ψ : ℝ → ℂ}
    (hX : IsLevyProcess X P)
    (hXchar : ∀ (t : ℝ≥0) (ξ : ℝ), charFun (P.map (X t)) ξ = Complex.exp (-((t : ℝ) : ℂ) * Ψ ξ))
    (ξ : ℝ) : 0 ≤ (Ψ ξ).re := by
  have : IsProbabilityMeasure (P.map (X 1)) :=
    Measure.isProbabilityMeasure_map (aemeasurable_of_isLevyProcess hX 1)
  have hnorm : ‖charFun (P.map (X 1)) ξ‖ ≤ 1 := norm_charFun_le_one ξ
  rw [hXchar 1 ξ] at hnorm
  simp only [NNReal.coe_one, Complex.ofReal_one, neg_mul, one_mul, Complex.norm_exp,
    Complex.neg_re] at hnorm
  have hle : -(Ψ ξ).re ≤ 0 := Real.exp_le_one_iff.mp hnorm
  linarith

private lemma aestronglyMeasurable_X_dyadicUp
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ} (hX : IsLevyProcess X P)
    {S : Ω → ℝ≥0} (hS : AEMeasurable (fun ω => (S ω : ℝ)) P) (m : ℕ) :
    AEStronglyMeasurable (fun ω => X (dyadicUp m (S ω)) ω) P := by
  obtain ⟨Smk, hSmk_meas, hSmk_ae⟩ := hS
  let kfun : Ω → ℕ := fun ω => Nat.floor ((2 : ℝ) ^ m * max 0 (Smk ω))
  have hk_meas : Measurable kfun :=
    Measurable.nat_floor (measurable_const.mul (measurable_const.max hSmk_meas))
  have hXex : ∀ k : ℕ, ∃ g : Ω → ℝ, Measurable g ∧ X (dyadicVal m k) =ᵐ[P] g :=
    fun k => aemeasurable_of_isLevyProcess hX (dyadicVal m k)
  choose fX hfX_meas hfX_ae using hXex
  have hfX_all : ∀ᵐ ω ∂P, ∀ k : ℕ, X (dyadicVal m k) ω = fX k ω :=
    ae_all_iff.mpr hfX_ae
  have hpair_meas : Measurable (fun p : Ω × ℕ => fX p.2 p.1) :=
    measurable_from_prod_countable_left hfX_meas
  have hg_meas : Measurable (fun ω => fX (kfun ω) ω) :=
    hpair_meas.comp (measurable_id.prodMk hk_meas)
  refine hg_meas.aestronglyMeasurable.congr ?_
  filter_upwards [hSmk_ae, hfX_all] with ω hωS hωX
  have hmax : max (0 : ℝ) (Smk ω) = (S ω : ℝ) := by
    rw [← hωS, max_eq_right (S ω).coe_nonneg]
  rw [← hωX (kfun ω)]
  simp only [dyadicUp, dyadicVal, kfun, hmax]

private lemma aestronglyMeasurable_dyadicUp_coe
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {S : Ω → ℝ≥0} (hS : AEMeasurable (fun ω => (S ω : ℝ)) P) (m : ℕ) :
    AEStronglyMeasurable (fun ω => (dyadicUp m (S ω) : ℝ)) P := by
  obtain ⟨Smk, hSmk_meas, hSmk_ae⟩ := hS
  let g : Ω → ℝ := fun ω => (dyadicVal m (Nat.floor ((2 : ℝ) ^ m * max 0 (Smk ω))) : ℝ)
  have hg_meas : Measurable g :=
    (measurable_of_countable (fun k : ℕ => (dyadicVal m k : ℝ))).comp
      (Measurable.nat_floor (measurable_const.mul (measurable_const.max hSmk_meas)))
  refine hg_meas.aestronglyMeasurable.congr ?_
  filter_upwards [hSmk_ae] with ω hωS
  have hmax : max (0 : ℝ) (Smk ω) = (S ω : ℝ) := by
    rw [← hωS, max_eq_right (S ω).coe_nonneg]
  simp only [g, dyadicUp, dyadicVal, hmax]

private lemma aemeasurable_subordinate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ} (hX : IsLevyProcess X P)
    {τ : ℝ≥0 → Ω → ℝ≥0} (hτ : IsLevyProcess (fun t ω => (τ t ω : ℝ)) P)
    (t : ℝ≥0) : AEMeasurable (fun ω => X (τ t ω) ω) P := by
  have happrox : ∀ m : ℕ, AEStronglyMeasurable (fun ω => X (dyadicUp m (τ t ω)) ω) P :=
    fun m => aestronglyMeasurable_X_dyadicUp hX (aemeasurable_of_isLevyProcess hτ t) m
  have htend : ∀ᵐ ω ∂P, Tendsto (fun m => X (dyadicUp m (τ t ω)) ω) atTop (nhds (X (τ t ω) ω)) := by
    filter_upwards [hX.cadlag_ae] with ω hω
    exact (hω (τ t ω)).1.tendsto.comp (dyadicUp_tendsto (τ t ω))
  exact (aestronglyMeasurable_of_tendsto_ae atTop happrox htend).aemeasurable

private lemma norm_exp_neg_mul_le_one {r : ℝ} (hr : 0 ≤ r) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖Complex.exp (-((r : ℂ)) * z)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have hre : (-((r : ℂ)) * z).re = -(r * z.re) := by
    simp [Complex.mul_re]
  rw [hre]
  exact Real.exp_le_one_iff.mpr (by nlinarith)

private lemma subordinate_joint_charFun
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (Ψ : ℝ → ℂ)
    (hX : IsLevyProcess X P)
    (hXchar : ∀ (t : ℝ≥0) (ξ : ℝ), charFun (P.map (X t)) ξ = Complex.exp (-((t : ℝ) : ℂ) * Ψ ξ))
    (τ : ℝ≥0 → Ω → ℝ≥0)
    (hτ : IsLevyProcess (fun t ω => (τ t ω : ℝ)) P)
    (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
    (hind : iIndepFun
      (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 => if i = 0 then X t ω else (τ t ω : ℝ)) P)
    (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t) (u : Fin n → ℝ) :
    ∫ ω, Complex.exp (↑(∑ k : Fin n, u k * (X (τ (t k.succ) ω) ω - X (τ (t k.castSucc) ω) ω)) * Complex.I) ∂P =
      ∏ k : Fin n, ∫ ω, Complex.exp (-((τ (t k.succ - t k.castSucc) ω : ℝ) : ℂ) * Ψ (u k)) ∂P := by
  have hΨ_re : ∀ ξ, 0 ≤ (Ψ ξ).re := fun ξ => psi_re_nonneg hX hXchar ξ
  have hind01 : IndepFun (fun ω (s : ℝ≥0) => X s ω) (fun ω (s : ℝ≥0) => (τ s ω : ℝ)) P := by
    have h := hind.indepFun (show (0 : Fin 2) ≠ 1 by decide)
    simpa only [↓reduceIte, show (1 : Fin 2) ≠ 0 by decide] using h
  have hτex : ∀ j : Fin (n + 1), ∃ g : Ω → ℝ, Measurable g ∧ (fun ω => (τ (t j) ω : ℝ)) =ᵐ[P] g :=
    fun j => aemeasurable_of_isLevyProcess hτ (t j)
  choose τmk hτmk_meas hτmk_ae_j using hτex
  have hτmk_ae : ∀ᵐ ω ∂P, ∀ j : Fin (n + 1), (τ (t j) ω : ℝ) = τmk j ω :=
    ae_all_iff.mpr hτmk_ae_j
  -- Step 1: Level-m dyadic expectation identity
  have hlevel : ∀ m : ℕ,
      (∫ ω, Complex.exp (↑(∑ k : Fin n, u k *
          (X (dyadicUp m (τ (t k.succ) ω)) ω - X (dyadicUp m (τ (t k.castSucc) ω)) ω)) * Complex.I) ∂P) =
      ∫ ω, ∏ k : Fin n, Complex.exp (-(((dyadicUp m (τ (t k.succ) ω) : ℝ) -
          (dyadicUp m (τ (t k.castSucc) ω) : ℝ)) : ℂ) * Ψ (u k)) ∂P := by
    intro m
    let Q := {q : Fin (n + 1) → ℕ // Monotone q}
    let idxOf : Ω → Fin (n + 1) → ℕ := fun ω j => Nat.floor ((2 : ℝ) ^ m * max 0 (τmk j ω))
    let E : Q → Set Ω := fun q => {ω | idxOf ω = q.1}
    have hE_meas : ∀ q : Q, MeasurableSet (E q) := by
      intro q
      have hidx_meas : Measurable idxOf :=
        measurable_pi_lambda _ fun j =>
          Measurable.nat_floor (measurable_const.mul (measurable_const.max (hτmk_meas j)))
      exact hidx_meas (measurableSet_singleton q.1)
    have hE_disj : Pairwise fun q₁ q₂ : Q => Disjoint (E q₁) (E q₂) := by
      intro q₁ q₂ hne
      rw [Set.disjoint_left]
      intro ω h1 h2
      exact hne (Subtype.ext (h1.symm.trans h2))
    have hE_ae_cover : ∀ᵐ ω ∂P, ω ∈ ⋃ q : Q, E q := by
      filter_upwards [hmon, hτmk_ae] with ω hωmon hωmk
      have hqm : Monotone (idxOf ω) := by
        intro a b hab
        dsimp only [idxOf]
        rw [← hωmk a, ← hωmk b, max_eq_right (τ (t a) ω).coe_nonneg,
          max_eq_right (τ (t b) ω).coe_nonneg]
        exact Nat.floor_mono (mul_le_mul_of_nonneg_left
          (NNReal.coe_le_coe.mpr (hωmon (ht hab))) (by positivity))
      exact Set.mem_iUnion.mpr ⟨⟨idxOf ω, hqm⟩, rfl⟩
    have hE_compl_zero : P (⋃ q : Q, E q)ᶜ = 0 := by rwa [ae_iff] at hE_ae_cover
    have hE_ae_univ : (⋃ q : Q, E q) =ᵐ[P] Set.univ := by
      rw [ae_eq_set]
      refine ⟨by rw [Set.sdiff_univ]; simp, ?_⟩
      have hdiff : Set.univ \ (⋃ q : Q, E q) = (⋃ q : Q, E q)ᶜ := by ext ω; simp
      rw [hdiff]; exact hE_compl_zero
    let F : Ω → ℂ := fun ω =>
      Complex.exp (↑(∑ k : Fin n, u k *
        (X (dyadicUp m (τ (t k.succ) ω)) ω - X (dyadicUp m (τ (t k.castSucc) ω)) ω)) * Complex.I)
    let G : Ω → ℂ := fun ω =>
      ∏ k : Fin n, Complex.exp (-(((dyadicUp m (τ (t k.succ) ω) : ℝ) -
        (dyadicUp m (τ (t k.castSucc) ω) : ℝ)) : ℂ) * Ψ (u k))
    have hF_ae : AEStronglyMeasurable F P := by
      have hXm : ∀ j : Fin (n + 1), AEStronglyMeasurable (fun ω => X (dyadicUp m (τ (t j) ω)) ω) P :=
        fun j => aestronglyMeasurable_X_dyadicUp hX (aemeasurable_of_isLevyProcess hτ (t j)) m
      have hsum : AEStronglyMeasurable
          (fun ω => ∑ k ∈ (Finset.univ : Finset (Fin n)), u k *
            (X (dyadicUp m (τ (t k.succ) ω)) ω - X (dyadicUp m (τ (t k.castSucc) ω)) ω)) P :=
        Finset.aestronglyMeasurable_fun_sum (Finset.univ : Finset (Fin n)) fun k _ =>
          aestronglyMeasurable_const.mul ((hXm k.succ).sub (hXm k.castSucc))
      exact Complex.continuous_exp.comp_aestronglyMeasurable
        ((Complex.continuous_ofReal.comp_aestronglyMeasurable hsum).mul aestronglyMeasurable_const)
    have hG_ae : AEStronglyMeasurable G P := by
      have hd_ae : ∀ j : Fin (n + 1), AEStronglyMeasurable (fun ω => (dyadicUp m (τ (t j) ω) : ℝ)) P :=
        fun j => aestronglyMeasurable_dyadicUp_coe (aemeasurable_of_isLevyProcess hτ (t j)) m
      exact Finset.aestronglyMeasurable_fun_prod (Finset.univ : Finset (Fin n)) fun k _ =>
        Complex.continuous_exp.comp_aestronglyMeasurable
          ((((Complex.continuous_ofReal.comp_aestronglyMeasurable (hd_ae k.succ)).sub
            (Complex.continuous_ofReal.comp_aestronglyMeasurable (hd_ae k.castSucc))).neg).mul
              aestronglyMeasurable_const)
    have hF_int : Integrable F P :=
      (integrable_const (1 : ℝ)).mono' hF_ae (Eventually.of_forall fun ω => by
        dsimp only [F]; rw [Complex.norm_exp_ofReal_mul_I])
    have hG_int : Integrable G P := by
      refine (integrable_const (1 : ℝ)).mono' hG_ae ?_
      filter_upwards [hmon] with ω hω
      dsimp only [G]; rw [norm_prod]
      refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun k _ => ?_
      have hsub_nn : 0 ≤ (dyadicUp m (τ (t k.succ) ω) : ℝ) - (dyadicUp m (τ (t k.castSucc) ω) : ℝ) :=
        sub_nonneg.mpr (NNReal.coe_le_coe.mpr (dyadicUp_mono m (hω (ht k.castSucc_le_succ))))
      rw [← Complex.ofReal_sub]
      exact norm_exp_neg_mul_le_one hsub_nn (hΨ_re (u k))
    have hF_split : ∫ ω, F ω ∂P = ∑' q : Q, ∫ ω in E q, F ω ∂P := by
      rw [← setIntegral_univ, ← setIntegral_congr_set hE_ae_univ]
      exact integral_iUnion hE_meas hE_disj hF_int.integrableOn
    have hG_split : ∫ ω, G ω ∂P = ∑' q : Q, ∫ ω in E q, G ω ∂P := by
      rw [← setIntegral_univ, ← setIntegral_congr_set hE_ae_univ]
      exact integral_iUnion hE_meas hE_disj hG_int.integrableOn
    rw [hF_split, hG_split]
    refine tsum_congr fun q => ?_
    let fq : (ℝ≥0 → ℝ) → ℂ := fun x =>
      Complex.exp (↑(∑ k : Fin n, u k * (x (dyadicVal m (q.1 k.succ)) - x (dyadicVal m (q.1 k.castSucc)))) * Complex.I)
    let gq : (ℝ≥0 → ℝ) → ℂ := fun y =>
      if (fun j : Fin (n + 1) => Nat.floor ((2 : ℝ) ^ m * max 0 (y (t j)))) = q.1 then 1 else 0
    have hfq_meas : Measurable fq := by
      refine Complex.continuous_exp.measurable.comp ((Complex.continuous_ofReal.measurable.comp ?_).mul measurable_const)
      exact Finset.measurable_sum _ fun k _ =>
        measurable_const.mul ((measurable_pi_apply _).sub (measurable_pi_apply _))
    have hgq_meas : Measurable gq := by
      have hpi : Measurable (fun (y : ℝ≥0 → ℝ) (j : Fin (n + 1)) => Nat.floor ((2 : ℝ) ^ m * max 0 (y (t j)))) :=
        measurable_pi_lambda _ fun j =>
          Measurable.nat_floor (measurable_const.mul (measurable_const.max (measurable_pi_apply (t j))))
      have hset : MeasurableSet {y : ℝ≥0 → ℝ | (fun j : Fin (n + 1) => Nat.floor ((2 : ℝ) ^ m * max 0 (y (t j)))) = q.1} :=
        hpi (measurableSet_singleton q.1)
      exact Measurable.ite hset measurable_const measurable_const
    have hind_fg : IndepFun (fun ω => fq (fun s => X s ω)) (fun ω => gq (fun s => (τ s ω : ℝ))) P :=
      hind01.comp hfq_meas hgq_meas
    have hfq_ae : AEStronglyMeasurable (fun ω => fq (fun s => X s ω)) P := by
      have hsum : AEStronglyMeasurable
          (fun ω => ∑ k ∈ (Finset.univ : Finset (Fin n)), u k *
            (X (dyadicVal m (q.1 k.succ)) ω - X (dyadicVal m (q.1 k.castSucc)) ω)) P :=
        Finset.aestronglyMeasurable_fun_sum (Finset.univ : Finset (Fin n)) fun k _ =>
          aestronglyMeasurable_const.mul
            ((aemeasurable_of_isLevyProcess hX _).aestronglyMeasurable.sub
              (aemeasurable_of_isLevyProcess hX _).aestronglyMeasurable)
      exact Complex.continuous_exp.comp_aestronglyMeasurable
        ((Complex.continuous_ofReal.comp_aestronglyMeasurable hsum).mul aestronglyMeasurable_const)
    have hEq_ind : (fun ω => gq (fun s => (τ s ω : ℝ))) =ᵐ[P] (E q).indicator (fun _ => (1 : ℂ)) := by
      filter_upwards [hτmk_ae] with ω hωmk
      have hidx_eq : (fun j : Fin (n + 1) => Nat.floor ((2 : ℝ) ^ m * max 0 (τ (t j) ω : ℝ))) = idxOf ω := by
        funext j; simp [idxOf, hωmk j]
      by_cases hmem : ω ∈ E q
      · have hmem' : idxOf ω = q.1 := hmem
        simp only [gq, Set.indicator_of_mem hmem, hidx_eq, hmem', ↓reduceIte]
      · have hne : idxOf ω ≠ q.1 := hmem
        simp only [gq, Set.indicator_of_notMem hmem, hidx_eq, hne, ↓reduceIte]
    have hgq_ae : AEStronglyMeasurable (fun ω => gq (fun s => (τ s ω : ℝ))) P :=
      (aestronglyMeasurable_const.indicator (hE_meas q)).congr hEq_ind.symm
    have hFq_eq : ∫ ω in E q, F ω ∂P = (P.real (E q) : ℂ) * ∫ ω, fq (fun s => X s ω) ∂P := by
      rw [← integral_indicator (hE_meas q)]
      have hcongr : (E q).indicator F =ᵐ[P] fun ω => fq (fun s => X s ω) * gq (fun s => (τ s ω : ℝ)) := by
        filter_upwards [hτmk_ae] with ω hωmk
        have hidx_eq : (fun j : Fin (n + 1) => Nat.floor ((2 : ℝ) ^ m * max 0 (τ (t j) ω : ℝ))) = idxOf ω := by
          funext j; simp [idxOf, hωmk j]
        by_cases hmem : ω ∈ E q
        · have hmem' : idxOf ω = q.1 := hmem
          rw [Set.indicator_of_mem hmem]
          dsimp only [gq]; rw [hidx_eq, if_pos hmem', mul_one]
          dsimp only [F, fq]
          congr 2; congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          have hup : ∀ j : Fin (n + 1), dyadicUp m (τ (t j) ω) = dyadicVal m (q.1 j) := by
            intro j
            have hmax : max (0 : ℝ) (τmk j ω) = (τ (t j) ω : ℝ) := by
              rw [← hωmk j, max_eq_right (τ (t j) ω).coe_nonneg]
            have hq : Nat.floor ((2 : ℝ) ^ m * (τ (t j) ω : ℝ)) = q.1 j := by
              rw [← hmax]; exact congrFun hmem' j
            simp [dyadicUp, dyadicVal, hq]
          rw [hup k.succ, hup k.castSucc]
        · rw [Set.indicator_of_notMem hmem]
          have hne : idxOf ω ≠ q.1 := hmem
          dsimp only [gq]; rw [hidx_eq, if_neg hne, mul_zero]
      rw [integral_congr_ae hcongr,
        hind_fg.integral_fun_mul_eq_mul_integral hfq_ae hgq_ae, mul_comm]
      congr 1
      rw [integral_congr_ae hEq_ind, integral_indicator_const (1 : ℂ) (hE_meas q)]
      simp [Complex.real_smul]
    have hfq_int : ∫ ω, fq (fun s => X s ω) ∂P =
        ∏ k : Fin n, Complex.exp (-(((dyadicVal m (q.1 k.succ) : ℝ) -
          (dyadicVal m (q.1 k.castSucc) : ℝ)) : ℂ) * Ψ (u k)) := by
      have hprod : (fun ω => fq (fun s => X s ω)) =
          fun ω => ∏ k : Fin n, Complex.exp (↑(u k * increment X (dyadicVal m (q.1 k.castSucc))
            (dyadicVal m (q.1 k.succ)) ω) * Complex.I) := by
        funext ω
        dsimp only [fq, increment]
        rw [← Complex.exp_sum]
        congr 1; push_cast; rw [Finset.sum_mul]
      rw [hprod]
      have hXind := hX.indep_increments n (fun j => dyadicVal m (q.1 j)) ((dyadicVal_mono m).comp q.2)
      have hXinc_ae : ∀ k : Fin n, AEMeasurable (increment X (dyadicVal m (q.1 k.castSucc))
          (dyadicVal m (q.1 k.succ))) P := fun k =>
        (aemeasurable_of_isLevyProcess hX _).sub (aemeasurable_of_isLevyProcess hX _)
      rw [hXind.integral_fun_prod_comp
        (f := fun k x => Complex.exp (↑(u k * x) * Complex.I))
        hXinc_ae (fun k => by fun_prop)]
      refine Finset.prod_congr rfl fun k _ => ?_
      have hle : dyadicVal m (q.1 k.castSucc) ≤ dyadicVal m (q.1 k.succ) :=
        (dyadicVal_mono m) (q.2 k.castSucc_le_succ)
      have hid := hX.stationary_increments (dyadicVal m (q.1 k.castSucc))
        (dyadicVal m (q.1 k.succ) - dyadicVal m (q.1 k.castSucc))
      rw [add_tsub_cancel_of_le hle] at hid
      have hinc0 : increment X 0 (dyadicVal m (q.1 k.succ) - dyadicVal m (q.1 k.castSucc)) =
          X (dyadicVal m (q.1 k.succ) - dyadicVal m (q.1 k.castSucc)) := by
        funext ω; simp [increment, congrFun hX.start_zero ω]
      rw [hinc0] at hid
      have hcf : (∫ ω, Complex.exp (↑(u k * increment X (dyadicVal m (q.1 k.castSucc))
            (dyadicVal m (q.1 k.succ)) ω) * Complex.I) ∂P) =
          charFun (P.map (X (dyadicVal m (q.1 k.succ) - dyadicVal m (q.1 k.castSucc)))) (u k) := by
        rw [charFun_apply_real, ← hid.map_eq, integral_map (hXinc_ae k) (by fun_prop)]
        congr 1; funext ω; push_cast; ring_nf
      rw [hcf, hXchar, NNReal.coe_sub hle, Complex.ofReal_sub]
    have hGq_eq : ∫ ω in E q, G ω ∂P =
        (P.real (E q) : ℂ) * ∏ k : Fin n, Complex.exp (-(((dyadicVal m (q.1 k.succ) : ℝ) -
          (dyadicVal m (q.1 k.castSucc) : ℝ)) : ℂ) * Ψ (u k)) := by
      have hGq_congr : ∀ᵐ ω ∂P, ω ∈ E q → G ω =
          ∏ k : Fin n, Complex.exp (-(((dyadicVal m (q.1 k.succ) : ℝ) -
            (dyadicVal m (q.1 k.castSucc) : ℝ)) : ℂ) * Ψ (u k)) := by
        filter_upwards [hτmk_ae] with ω hωmk hmem
        have hmem' : idxOf ω = q.1 := hmem
        dsimp only [G]
        refine Finset.prod_congr rfl fun k _ => ?_
        have hup : ∀ j : Fin (n + 1), dyadicUp m (τ (t j) ω) = dyadicVal m (q.1 j) := by
          intro j
          have hmax : max (0 : ℝ) (τmk j ω) = (τ (t j) ω : ℝ) := by
            rw [← hωmk j, max_eq_right (τ (t j) ω).coe_nonneg]
          have hq : Nat.floor ((2 : ℝ) ^ m * (τ (t j) ω : ℝ)) = q.1 j := by
            rw [← hmax]; exact congrFun hmem' j
          simp [dyadicUp, dyadicVal, hq]
        rw [hup k.succ, hup k.castSucc]
      rw [setIntegral_congr_ae (hE_meas q) hGq_congr, setIntegral_const]
      exact Complex.real_smul
    rw [hFq_eq, hfq_int, hGq_eq]
  -- Step 2: Pass to m → ∞ by Dominated Convergence on both sides
  have hL_tend : Tendsto (fun m => ∫ ω, Complex.exp (↑(∑ k : Fin n, u k *
      (X (dyadicUp m (τ (t k.succ) ω)) ω - X (dyadicUp m (τ (t k.castSucc) ω)) ω)) * Complex.I) ∂P)
      atTop (nhds (∫ ω, Complex.exp (↑(∑ k : Fin n, u k *
        (X (τ (t k.succ) ω) ω - X (τ (t k.castSucc) ω) ω)) * Complex.I) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1) ?_ ?_
    · intro m
      have hXm : ∀ j : Fin (n + 1), AEStronglyMeasurable (fun ω => X (dyadicUp m (τ (t j) ω)) ω) P :=
        fun j => aestronglyMeasurable_X_dyadicUp hX (aemeasurable_of_isLevyProcess hτ (t j)) m
      exact Complex.continuous_exp.comp_aestronglyMeasurable
        ((Complex.continuous_ofReal.comp_aestronglyMeasurable
          (Finset.aestronglyMeasurable_fun_sum (Finset.univ : Finset (Fin n)) fun k _ =>
            aestronglyMeasurable_const.mul ((hXm k.succ).sub (hXm k.castSucc)))).mul
          aestronglyMeasurable_const)
    · intro _; exact Eventually.of_forall fun ω => by rw [Complex.norm_exp_ofReal_mul_I]
    · filter_upwards [hX.cadlag_ae] with ω hω
      have hterm : ∀ j : Fin (n + 1),
          Tendsto (fun m => X (dyadicUp m (τ (t j) ω)) ω) atTop (nhds (X (τ (t j) ω) ω)) :=
        fun j => (hω (τ (t j) ω)).1.tendsto.comp (dyadicUp_tendsto (τ (t j) ω))
      refine (Complex.continuous_exp.tendsto _).comp
        (((Complex.continuous_ofReal.tendsto _).comp ?_).mul tendsto_const_nhds)
      exact tendsto_finsetSum _ fun k _ =>
        tendsto_const_nhds.mul ((hterm k.succ).sub (hterm k.castSucc))
  have hR_tend : Tendsto (fun m => ∫ ω, ∏ k : Fin n, Complex.exp (-(((dyadicUp m (τ (t k.succ) ω) : ℝ) -
      (dyadicUp m (τ (t k.castSucc) ω) : ℝ)) : ℂ) * Ψ (u k)) ∂P)
      atTop (nhds (∫ ω, ∏ k : Fin n, Complex.exp (-(((τ (t k.succ) ω : ℝ) -
        (τ (t k.castSucc) ω : ℝ)) : ℂ) * Ψ (u k)) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1) ?_ ?_
    · intro m
      have hd_ae : ∀ j : Fin (n + 1), AEStronglyMeasurable (fun ω => (dyadicUp m (τ (t j) ω) : ℝ)) P :=
        fun j => aestronglyMeasurable_dyadicUp_coe (aemeasurable_of_isLevyProcess hτ (t j)) m
      exact Finset.aestronglyMeasurable_fun_prod (Finset.univ : Finset (Fin n)) fun k _ =>
        Complex.continuous_exp.comp_aestronglyMeasurable
          ((((Complex.continuous_ofReal.comp_aestronglyMeasurable (hd_ae k.succ)).sub
            (Complex.continuous_ofReal.comp_aestronglyMeasurable (hd_ae k.castSucc))).neg).mul
              aestronglyMeasurable_const)
    · intro m
      filter_upwards [hmon] with ω hω
      rw [norm_prod]
      refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun k _ => ?_
      have hsub_nn : 0 ≤ (dyadicUp m (τ (t k.succ) ω) : ℝ) - (dyadicUp m (τ (t k.castSucc) ω) : ℝ) :=
        sub_nonneg.mpr (NNReal.coe_le_coe.mpr (dyadicUp_mono m (hω (ht k.castSucc_le_succ))))
      rw [← Complex.ofReal_sub]
      exact norm_exp_neg_mul_le_one hsub_nn (hΨ_re (u k))
    · refine Eventually.of_forall fun ω => ?_
      refine tendsto_finsetProd _ fun k _ => ?_
      have hterm : ∀ j : Fin (n + 1),
          Tendsto (fun m => (dyadicUp m (τ (t j) ω) : ℝ)) atTop (nhds (τ (t j) ω : ℝ)) :=
        fun j => NNReal.tendsto_coe.mpr (tendsto_nhds_of_tendsto_nhdsWithin (dyadicUp_tendsto (τ (t j) ω)))
      exact (Complex.continuous_exp.tendsto _).comp
        (((((Complex.continuous_ofReal.tendsto _).comp (hterm k.succ)).sub
          ((Complex.continuous_ofReal.tendsto _).comp (hterm k.castSucc))).neg).mul
          tendsto_const_nhds)
  have hmid : (∫ ω, Complex.exp (↑(∑ k : Fin n, u k *
        (X (τ (t k.succ) ω) ω - X (τ (t k.castSucc) ω) ω)) * Complex.I) ∂P) =
      ∫ ω, ∏ k : Fin n, Complex.exp (-(((τ (t k.succ) ω : ℝ) -
        (τ (t k.castSucc) ω : ℝ)) : ℂ) * Ψ (u k)) ∂P := by
    simp_rw [hlevel] at hL_tend
    exact tendsto_nhds_unique hL_tend hR_tend
  rw [hmid]
  -- Step 3: Factorize the RHS using independent stationary increments of τ
  have hτind := hτ.indep_increments n t ht
  have hτinc_ae : ∀ k : Fin n,
      AEMeasurable (increment (fun s ω => (τ s ω : ℝ)) (t k.castSucc) (t k.succ)) P := fun k =>
    (aemeasurable_of_isLevyProcess hτ (t k.succ)).sub (aemeasurable_of_isLevyProcess hτ (t k.castSucc))
  have hrew_prod : (∫ ω, ∏ k : Fin n, Complex.exp (-(((τ (t k.succ) ω : ℝ) -
        (τ (t k.castSucc) ω : ℝ)) : ℂ) * Ψ (u k)) ∂P) =
      ∫ ω, ∏ k : Fin n, Complex.exp
        (-(Complex.ofReal (increment (fun s ω => (τ s ω : ℝ)) (t k.castSucc) (t k.succ) ω)) * Ψ (u k)) ∂P := by
    congr 1; funext ω; refine Finset.prod_congr rfl fun k _ => ?_
    simp [increment, Complex.ofReal_sub]
  rw [hrew_prod, hτind.integral_fun_prod_comp
        (f := fun k (x : ℝ) => Complex.exp (-(Complex.ofReal x) * Ψ (u k)))
        hτinc_ae (fun k => by fun_prop)]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hle : t k.castSucc ≤ t k.succ := ht k.castSucc_le_succ
  have hid := hτ.stationary_increments (t k.castSucc) (t k.succ - t k.castSucc)
  rw [add_tsub_cancel_of_le hle] at hid
  have hinc0 : increment (fun s ω => (τ s ω : ℝ)) 0 (t k.succ - t k.castSucc) =
      fun ω => (τ (t k.succ - t k.castSucc) ω : ℝ) := by
    funext ω; simp [increment, congrFun hτ.start_zero ω]
  rw [hinc0] at hid
  have hcont_k : Continuous (fun x : ℝ => Complex.exp (-(Complex.ofReal x) * Ψ (u k))) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.neg.mul continuous_const)
  have hLHS : (∫ ω, Complex.exp
        (-(Complex.ofReal (increment (fun s ω => (τ s ω : ℝ)) (t k.castSucc) (t k.succ) ω)) * Ψ (u k)) ∂P) =
      ∫ x, Complex.exp (-(Complex.ofReal x) * Ψ (u k)) ∂(P.map (increment (fun s ω => (τ s ω : ℝ)) (t k.castSucc) (t k.succ))) :=
    (integral_map (hτinc_ae k) hcont_k.aestronglyMeasurable).symm
  have hRHS : (∫ ω, Complex.exp (-((τ (t k.succ - t k.castSucc) ω : ℝ) : ℂ) * Ψ (u k)) ∂P) =
      ∫ x, Complex.exp (-(Complex.ofReal x) * Ψ (u k)) ∂(P.map (fun ω => (τ (t k.succ - t k.castSucc) ω : ℝ))) :=
    (integral_map (aemeasurable_of_isLevyProcess hτ _) hcont_k.aestronglyMeasurable).symm
  rw [hLHS, hRHS, hid.map_eq]

private lemma subordinate_isLevyProcess
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (Ψ : ℝ → ℂ)
    (hX : IsLevyProcess X P)
    (hXchar : ∀ (t : ℝ≥0) (ξ : ℝ), charFun (P.map (X t)) ξ = Complex.exp (-((t : ℝ) : ℂ) * Ψ ξ))
    (τ : ℝ≥0 → Ω → ℝ≥0)
    (hτ : IsLevyProcess (fun t ω => (τ t ω : ℝ)) P)
    (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
    (hind : iIndepFun
      (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 => if i = 0 then X t ω else (τ t ω : ℝ)) P) :
    IsLevyProcess (fun t ω => X (τ t ω) ω) P ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => X (τ t ω) ω)) ξ =
        ∫ ω, Complex.exp (-((τ t ω : ℝ) : ℂ) * Ψ ξ) ∂P := by
  let Z : ℝ≥0 → Ω → ℝ := fun t ω => X (τ t ω) ω
  have hτ0 : ∀ ω, τ 0 ω = 0 := fun ω => by
    have h0 : (τ 0 ω : ℝ) = 0 := congrFun hτ.start_zero ω
    exact NNReal.coe_eq_zero.mp h0
  have hZ0 : Z 0 = fun _ => 0 := by
    funext ω; simp only [Z, hτ0 ω]; exact congrFun hX.start_zero ω
  have hZ_ae : ∀ t, AEMeasurable (Z t) P := fun t => aemeasurable_subordinate hX hτ t
  have hinc_char : ∀ (s t : ℝ≥0), s ≤ t → ∀ ξ : ℝ,
      charFun (P.map (increment Z s t)) ξ =
        ∫ ω, Complex.exp (-((τ (t - s) ω : ℝ) : ℂ) * Ψ ξ) ∂P := by
    intro s t hst ξ
    let tp : Fin 2 → ℝ≥0 := fun j => if j = 0 then s else t
    have htp : Monotone tp := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp [tp, hst] at hab ⊢
    have hcf := subordinate_joint_charFun P X Ψ hX hXchar τ hτ hmon hind 1 tp htp (fun _ => ξ)
    have hinc_ae : AEMeasurable (increment Z s t) P := (hZ_ae t).sub (hZ_ae s)
    rw [charFun_apply_real, integral_map hinc_ae (by fun_prop)]
    have h1 : (∫ ω, Complex.exp (↑ξ * ↑(increment Z s t ω) * Complex.I) ∂P) =
        ∫ ω, Complex.exp (↑(∑ k : Fin 1, (fun _ : Fin 1 => ξ) k *
          (X (τ (tp k.succ) ω) ω - X (τ (tp k.castSucc) ω) ω)) * Complex.I) ∂P := by
      congr 1; funext ω; simp [tp, increment, Z]
    rw [h1, hcf]
    simp [tp]
  have hZ_char : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (Z t)) ξ = ∫ ω, Complex.exp (-((τ t ω : ℝ) : ℂ) * Ψ ξ) ∂P := by
    intro t ξ
    have h := hinc_char 0 t bot_le ξ
    have heq : increment Z 0 t = Z t := by funext ω; simp [increment, congrFun hZ0 ω]
    simpa [heq] using h
  refine ⟨?_, hZ_char⟩
  refine
    { start_zero := hZ0
      indep_increments := ?_
      stationary_increments := ?_
      cadlag_ae := ?_ }
  · intro n t ht
    refine iIndepFun_of_joint_charFun
      (fun k => (hZ_ae (t k.succ)).sub (hZ_ae (t k.castSucc))) fun u => ?_
    have hcf := subordinate_joint_charFun P X Ψ hX hXchar τ hτ hmon hind n t ht u
    have h1 : (∫ ω, Complex.exp (↑(∑ k : Fin n, u k * increment Z (t k.castSucc) (t k.succ) ω) * Complex.I) ∂P) =
        ∏ k : Fin n, ∫ ω, Complex.exp (-((τ (t k.succ - t k.castSucc) ω : ℝ) : ℂ) * Ψ (u k)) ∂P := hcf
    rw [h1]
    refine Finset.prod_congr rfl fun k _ => ?_
    exact (hinc_char (t k.castSucc) (t k.succ) (ht k.castSucc_le_succ) (u k)).symm
  · intro s h
    refine identDistrib_of_charFun_eq
      ((hZ_ae (s + h)).sub (hZ_ae s)) ((hZ_ae h).sub (hZ_ae 0)) fun ξ => ?_
    rw [hinc_char s (s + h) le_self_add ξ, hinc_char 0 h bot_le ξ, add_tsub_cancel_left, tsub_zero]
  · filter_upwards [hX.cadlag_ae, hτ.cadlag_ae, hmon] with ω hXω hτω hmonω
    exact isCadlag_comp_monotone hXω hτω hmonω

/-! ### Section 3: Scaled Brownian Motion is a Lévy Process + Brownian Subordination -/

private lemma brownian_indep_increments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : LevyStochCalc.Brownian.BrownianMotion P) :
    HasIndependentIncrements (fun (t : ℝ≥0) (ω : Ω) => B.W (t : ℝ) ω - B.W 0 ω) P := by
  intro n
  induction n with
  | zero =>
    intro t _
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S _ _
    have hS : S = ∅ := Finset.eq_empty_of_isEmpty S
    subst hS; simp
  | succ n ih =>
    intro t ht
    let X : ℝ≥0 → Ω → ℝ := fun s ω => B.W (s : ℝ) ω - B.W 0 ω
    let t' : Fin (n + 1) → ℝ≥0 := fun j => t j.castSucc
    have ht' : Monotone t' := fun a b hab => ht (Fin.castSucc_le_castSucc_iff.mpr hab)
    have hprev := ih t' ht'
    let Y : Fin n → Ω → ℝ := fun k => increment X (t' k.castSucc) (t' k.succ)
    let Z : Ω → ℝ := increment X (t (Fin.last n).castSucc) (t (Fin.last (n + 1)))
    have hinc_eq : ∀ s u : ℝ≥0, increment X s u = fun ω => B.W (u : ℝ) ω - B.W (s : ℝ) ω := by
      intro s u; funext ω; simp [increment, X]
    have hind_last : IndepFun (fun ω (k : Fin n) => Y k ω) Z P := by
      have hle_last : t (Fin.last n).castSucc ≤ t (Fin.last (n + 1)) := ht (Fin.castSucc_le_succ _)
      by_cases heq : t (Fin.last n).castSucc = t (Fin.last (n + 1))
      · have hZ0 : Z = fun _ => 0 := by funext ω; simp [Z, increment, heq]
        rw [hZ0, indepFun_iff_measure_inter_preimage_eq_mul]
        intro A B _ _
        by_cases h0 : (0 : ℝ) ∈ B
        · have hpreB : (fun _ : Ω => (0 : ℝ)) ⁻¹' B = Set.univ := by ext; simp [h0]
          rw [hpreB, Set.inter_univ, measure_univ, mul_one]
        · have hpreB : (fun _ : Ω => (0 : ℝ)) ⁻¹' B = ∅ := by ext; simp [h0]
          rw [hpreB, Set.inter_empty, measure_empty, mul_zero]
      · have hlt : (t (Fin.last n).castSucc : ℝ) < (t (Fin.last (n + 1)) : ℝ) :=
          NNReal.coe_lt_coe.mpr (lt_of_le_of_ne hle_last heq)
        have hjoint := B.joint_increment_independent (t (Fin.last n).castSucc).coe_nonneg hlt
        have hZeq : Z = fun ω => B.W (t (Fin.last (n + 1)) : ℝ) ω - B.W (t (Fin.last n).castSucc : ℝ) ω :=
          hinc_eq _ _
        rw [hZeq]
        let W : ℝ → Ω → ℝ := B.W
        let mPast : MeasurableSpace Ω :=
          ⨆ j ∈ Set.Iic (t (Fin.last n).castSucc : ℝ), MeasurableSpace.comap (W j) inferInstance
        have hYeq_all : ∀ k : Fin n, Y k = fun ω => W (t' k.succ : ℝ) ω - W (t' k.castSucc : ℝ) ω :=
          fun k => hinc_eq _ _
        have hle_past : MeasurableSpace.comap (fun ω (k : Fin n) => Y k ω) inferInstance ≤ mPast := by
          let : MeasurableSpace Ω := mPast
          rw [← measurable_iff_comap_le]
          refine measurable_pi_lambda _ fun k => ?_
          rw [hYeq_all k]
          have hm : ∀ s : ℝ≥0, s ≤ t (Fin.last n).castSucc → Measurable (W (s : ℝ)) := by
            intro s hs
            rw [measurable_iff_comap_le]
            exact le_iSup₂_of_le (s : ℝ) (NNReal.coe_le_coe.mpr hs) le_rfl
          refine (hm (t' k.succ) ?_).sub (hm (t' k.castSucc) ?_)
          · exact ht (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last k.succ))
          · exact ht (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last k.castSucc))
        exact indep_of_indep_of_le_left hjoint hle_past
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets hsets
    let S' : Finset (Fin n) := Finset.univ.filter fun k => k.castSucc ∈ S
    by_cases hlast : Fin.last n ∈ S
    · have hinter : (⋂ i ∈ S, increment X (t i.castSucc) (t i.succ) ⁻¹' sets i) =
          ((fun ω (k : Fin n) => Y k ω) ⁻¹' (Set.univ.pi fun k => if k ∈ S' then sets k.castSucc else Set.univ)) ∩
          (Z ⁻¹' sets (Fin.last n)) := by
        ext ω
        simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_inter_iff, Set.mem_univ_pi,
          S', Finset.mem_filter]
        constructor
        · intro h
          refine ⟨fun k => ?_, h (Fin.last n) hlast⟩
          split_ifs with hk
          · exact h k.castSucc hk.2
          · trivial
        · rintro ⟨h1, h2⟩ i hi
          by_cases hil : i = Fin.last n
          · subst hil; exact h2
          · have h1' := h1 (i.castPred hil)
            have hmem : i.castPred hil ∈ Finset.univ ∧ (i.castPred hil).castSucc ∈ S :=
              ⟨Finset.mem_univ _, by rwa [Fin.castSucc_castPred i hil]⟩
            rw [if_pos hmem] at h1'
            have hsucc_eq : (i.castPred hil).succ.castSucc = i.succ := by ext; simp
            simpa only [Y, t', Fin.castSucc_castPred i hil, hsucc_eq] using h1'
      have hbox_meas : MeasurableSet (Set.univ.pi fun k : Fin n => if k ∈ S' then sets k.castSucc else Set.univ) :=
        MeasurableSet.univ_pi fun k => by
          split_ifs with hk
          · exact hsets k.castSucc (Finset.mem_filter.mp hk).2
          · exact MeasurableSet.univ
      rw [hinter, (indepFun_iff_measure_inter_preimage_eq_mul.mp hind_last) _ _ hbox_meas (hsets _ hlast)]
      have hbox_pre : (fun ω (k : Fin n) => Y k ω) ⁻¹'
            (Set.univ.pi fun k => if k ∈ S' then sets k.castSucc else Set.univ) =
          ⋂ k ∈ S', Y k ⁻¹' sets k.castSucc := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
        constructor
        · intro h k hk; have := h k; rwa [if_pos hk] at this
        · intro h k; split_ifs with hk
          · exact h k hk
          · trivial
      rw [hbox_pre, (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hprev) S'
        (fun k hk => hsets k.castSucc (Finset.mem_filter.mp hk).2)]
      have hprod_S : (∏ i ∈ S, P (increment X (t i.castSucc) (t i.succ) ⁻¹' sets i)) =
          (∏ k ∈ S', P (Y k ⁻¹' sets k.castSucc)) * P (Z ⁻¹' sets (Fin.last n)) := by
        rw [← Finset.mul_prod_erase S _ hlast, mul_comm]
        congr 1
        refine (Finset.prod_bij (fun (k : Fin n) (_ : k ∈ S') => k.castSucc) ?_ ?_ ?_ ?_).symm
        · intro k hk
          rw [Finset.mem_erase]
          exact ⟨Fin.castSucc_ne_last k, (Finset.mem_filter.mp hk).2⟩
        · intro a _ b _ h; exact Fin.castSucc_injective n h
        · intro i hi
          rw [Finset.mem_erase] at hi
          refine ⟨i.castPred hi.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Fin.castSucc_castPred i hi.1⟩
          rw [Fin.castSucc_castPred i hi.1]; exact hi.2
        · intro k _; rfl
      rw [hprod_S]
    · have hinter : (⋂ i ∈ S, increment X (t i.castSucc) (t i.succ) ⁻¹' sets i) =
          ⋂ k ∈ S', Y k ⁻¹' sets k.castSucc := by
        ext ω
        simp only [Set.mem_iInter, Set.mem_preimage, S', Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h k hk; exact h k.castSucc hk
        · intro h i hi
          have hne : i ≠ Fin.last n := fun heq => hlast (heq ▸ hi)
          have h1 := h (i.castPred hne) (by rw [Fin.castSucc_castPred i hne]; exact hi)
          have hsucc_eq : (i.castPred hne).succ.castSucc = i.succ := by ext; simp
          simpa only [Y, t', Fin.castSucc_castPred i hne, hsucc_eq] using h1
      rw [hinter, (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hprev) S'
        (fun k hk => hsets k.castSucc (Finset.mem_filter.mp hk).2)]
      refine Finset.prod_bij (fun (k : Fin n) (_ : k ∈ S') => k.castSucc) ?_ ?_ ?_ ?_
      · intro k hk; exact (Finset.mem_filter.mp hk).2
      · intro a _ b _ h; exact Fin.castSucc_injective n h
      · intro i hi
        have hne : i ≠ Fin.last n := fun heq => hlast (heq ▸ hi)
        refine ⟨i.castPred hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Fin.castSucc_castPred i hne⟩
        rwa [Fin.castSucc_castPred i hne]
      · intro k _; rfl

private lemma scaledBrownian_isLevyProcess
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : LevyStochCalc.Brownian.BrownianMotion P) (c : ℝ) :
    IsLevyProcess (fun (t : ℝ≥0) (ω : Ω) => c * (B.W (t : ℝ) ω - B.W 0 ω)) P ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => c * (B.W (t : ℝ) ω - B.W 0 ω))) ξ =
        Complex.exp (-((t : ℝ) : ℂ) * (((c * ξ) ^ 2 / 2 : ℝ) : ℂ)) := by
  let X0 : ℝ≥0 → Ω → ℝ := fun t ω => B.W (t : ℝ) ω - B.W 0 ω
  let X : ℝ≥0 → Ω → ℝ := fun t ω => c * X0 t ω
  have hX0_meas : ∀ t : ℝ≥0, Measurable (X0 t) := fun t =>
    (B.measurable_eval (t : ℝ)).sub (B.measurable_eval 0)
  have hX_meas : ∀ t : ℝ≥0, Measurable (X t) := fun t =>
    measurable_const.mul (hX0_meas t)
  have hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ = Complex.exp (-((t : ℝ) : ℂ) * (((c * ξ) ^ 2 / 2 : ℝ) : ℂ)) := by
    intro t ξ
    by_cases ht0 : t = 0
    · subst ht0
      have h0 : X 0 = fun _ => 0 := by funext ω; simp [X, X0]
      rw [h0, charFun_apply_real, integral_map measurable_const.aemeasurable (by fun_prop)]
      simp
    · have htpos : (0 : ℝ) < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht0)
      have hlaw : P.map (X0 t) = ProbabilityTheory.gaussianReal 0 t := by
        have h := B.increment_gaussian le_rfl htpos
        have hsub : (⟨(t : ℝ) - 0, by linarith⟩ : ℝ≥0) = t := by ext; simp
        rwa [hsub] at h
      rw [charFun_apply_real, integral_map (hX_meas t).aemeasurable (by fun_prop)]
      have hrew : (∫ ω, Complex.exp (↑ξ * ↑(X t ω) * Complex.I) ∂P) =
          charFun (P.map (X0 t)) (c * ξ) := by
        rw [charFun_apply_real, integral_map (hX0_meas t).aemeasurable (by fun_prop)]
        congr 1; funext ω; dsimp only [X]; push_cast; ring_nf
      rw [hrew, hlaw, charFun_gaussianReal]
      congr 1; push_cast; ring
  refine ⟨?_, hchar⟩
  refine
    { start_zero := by funext ω; simp
      indep_increments := ?_
      stationary_increments := ?_
      cadlag_ae := ?_ }
  · intro n t ht
    have h0 := brownian_indep_increments P B n t ht
    have heq : (fun k : Fin n => increment X (t k.castSucc) (t k.succ)) =
        fun k : Fin n => (fun x : ℝ => c * x) ∘ increment X0 (t k.castSucc) (t k.succ) := by
      funext k ω; simp only [Function.comp_apply, increment, X]; ring
    rw [heq]
    exact h0.comp (fun _ => fun x : ℝ => c * x) (fun _ => measurable_const.mul measurable_id)
  · intro s h
    have hinc_eq : ∀ u v : ℝ≥0, increment X u v = fun ω => c * (B.W (v : ℝ) ω - B.W (u : ℝ) ω) := by
      intro u v; funext ω; simp only [increment, X, X0]; ring
    rw [hinc_eq s (s + h), hinc_eq 0 h]
    by_cases hh0 : h = 0
    · subst hh0
      simp only [add_zero, sub_self, mul_zero]
      exact IdentDistrib.refl measurable_const.aemeasurable
    · have hhpos : (0 : ℝ) < (h : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hh0)
      have h1 := B.increment_gaussian (s : ℝ≥0).coe_nonneg
        (show (s : ℝ) < ((s + h : ℝ≥0) : ℝ) by rw [NNReal.coe_add]; linarith)
      have h2 := B.increment_gaussian le_rfl hhpos
      have hs1 : (⟨((s + h : ℝ≥0) : ℝ) - (s : ℝ), by rw [NNReal.coe_add]; linarith⟩ : ℝ≥0) = h := by
        ext; change (s : ℝ) + (h : ℝ) - (s : ℝ) = (h : ℝ); ring
      have hs2 : (⟨(h : ℝ) - 0, by linarith⟩ : ℝ≥0) = h := by ext; simp
      rw [hs1] at h1; rw [hs2] at h2
      have hm1 : Measurable (fun ω => B.W ((s + h : ℝ≥0) : ℝ) ω - B.W (s : ℝ) ω) :=
        (B.measurable_eval _).sub (B.measurable_eval _)
      have hm2 : Measurable (fun ω => B.W (h : ℝ) ω - B.W 0 ω) :=
        (B.measurable_eval _).sub (B.measurable_eval _)
      have hid0 : IdentDistrib (fun ω => B.W ((s + h : ℝ≥0) : ℝ) ω - B.W (s : ℝ) ω)
          (fun ω => B.W (h : ℝ) ω - B.W 0 ω) P P :=
        ⟨hm1.aemeasurable, hm2.aemeasurable, by rw [h1, h2]⟩
      exact hid0.comp (measurable_const.mul measurable_id)
  · filter_upwards [B.continuous_paths] with ω hcont
    exact isCadlag_of_continuous
      (continuous_const.mul ((hcont.comp NNReal.continuous_coe).sub continuous_const))

private lemma brownian_subordination
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : LevyStochCalc.Brownian.BrownianMotion P) (c : ℝ)
    (τ : ℝ≥0 → Ω → ℝ≥0)
    (hτ : IsLevyProcess (fun t ω => (τ t ω : ℝ)) P)
    (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
    (hind : iIndepFun
      (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
        if i = 0 then B.W (t : ℝ) ω else (τ t ω : ℝ)) P) :
    IsLevyProcess (fun t ω => c * (B.W (τ t ω : ℝ) ω - B.W 0 ω)) P ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => c * (B.W (τ t ω : ℝ) ω - B.W 0 ω))) ξ =
        ((∫ ω, Real.exp (-((c * ξ) ^ 2 / 2) * (τ t ω : ℝ)) ∂P : ℝ) : ℂ) := by
  obtain ⟨hX, hXchar⟩ := scaledBrownian_isLevyProcess P B c
  let Φ : (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) := fun f t => c * (f t - f 0)
  have hΦ : Measurable Φ :=
    measurable_pi_lambda _ fun t => measurable_const.mul ((measurable_pi_apply t).sub (measurable_pi_apply 0))
  have hind' : iIndepFun
      (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
        if i = 0 then c * (B.W (t : ℝ) ω - B.W 0 ω) else (τ t ω : ℝ)) P := by
    have h01 : IndepFun (fun ω (t : ℝ≥0) => B.W (t : ℝ) ω) (fun ω (t : ℝ≥0) => (τ t ω : ℝ)) P := by
      have h := hind.indepFun (show (0 : Fin 2) ≠ 1 by decide)
      simpa only [↓reduceIte, show (1 : Fin 2) ≠ 0 by decide] using h
    have h2 := iIndepFun_fin2_of_indepFun (h01.comp hΦ measurable_id)
    have hfun : (fun (i : Fin 2) (ω : Ω) => if i = 0 then (Φ ∘ fun ω t => B.W (t : ℝ) ω) ω
        else (id ∘ fun ω t => (τ t ω : ℝ)) ω) =
        fun (i : Fin 2) (ω : Ω) (t : ℝ≥0) =>
          if i = 0 then c * (B.W (t : ℝ) ω - B.W 0 ω) else (τ t ω : ℝ) := by
      funext i ω t; by_cases hi : i = 0 <;> simp [hi, Φ]
    rwa [hfun] at h2
  obtain ⟨hlevy, hcf⟩ := subordinate_isLevyProcess P
    (fun t ω => c * (B.W (t : ℝ) ω - B.W 0 ω))
    (fun ξ => (((c * ξ) ^ 2 / 2 : ℝ) : ℂ))
    hX hXchar τ hτ hmon hind'
  refine ⟨hlevy, fun t ξ => ?_⟩
  rw [hcf t ξ]
  have hrew : (fun ω => Complex.exp (-((τ t ω : ℝ) : ℂ) * (((c * ξ) ^ 2 / 2 : ℝ) : ℂ))) =
      fun ω => ((Real.exp (-((c * ξ) ^ 2 / 2) * (τ t ω : ℝ)) : ℝ) : ℂ) := by
    funext ω
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hrew]
  exact integral_ofReal

/-! ### Section 4: Part (3) — Poisson Process Monotonicity and Laplace Transform -/

private lemma poisson_monotone_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℝ≥0 → Ω → ℕ)
    (hNlevy : IsLevyProcess (fun t ω => (N t ω : ℝ)) P) :
    ∀ᵐ ω ∂P, Monotone (fun t => (N t ω : ℝ≥0)) := by
  have hN0 : ∀ ω, N 0 ω = 0 := fun ω =>
    Nat.cast_eq_zero.mp (congrFun hNlevy.start_zero ω)
  have hpair : ∀ (p q : ℚ≥0), p ≤ q →
      ∀ᵐ ω ∂P, (N (p : ℝ≥0) ω : ℝ) ≤ (N (q : ℝ≥0) ω : ℝ) := by
    intro p q hpq
    have hsle : (p : ℝ≥0) ≤ (q : ℝ≥0) := NNReal.coe_le_coe.mp (by exact_mod_cast hpq)
    have hid := hNlevy.stationary_increments (p : ℝ≥0) ((q : ℝ≥0) - (p : ℝ≥0))
    rw [add_tsub_cancel_of_le hsle] at hid
    have h0 : P {ω | increment (fun s ω => (N s ω : ℝ)) (p : ℝ≥0) (q : ℝ≥0) ω < 0} = 0 := by
      have hpre : {ω | increment (fun s ω => (N s ω : ℝ)) (p : ℝ≥0) (q : ℝ≥0) ω < 0} =
          increment (fun s ω => (N s ω : ℝ)) (p : ℝ≥0) (q : ℝ≥0) ⁻¹' Set.Iio (0 : ℝ) := rfl
      rw [hpre, hid.measure_mem_eq measurableSet_Iio]
      have hemp : increment (fun s ω => (N s ω : ℝ)) 0 ((q : ℝ≥0) - (p : ℝ≥0)) ⁻¹' Set.Iio (0 : ℝ) = ∅ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_Iio, increment, hN0 ω, Nat.cast_zero, sub_zero,
          Set.mem_empty_iff_false, iff_false, not_lt]
        exact Nat.cast_nonneg _
      rw [hemp, measure_empty]
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) h0
    simp only [Set.mem_ofPred_eq, increment] at hω ⊢
    linarith
  have hall : ∀ᵐ ω ∂P, ∀ (p q : ℚ≥0), p ≤ q → (N (p : ℝ≥0) ω : ℝ) ≤ (N (q : ℝ≥0) ω : ℝ) :=
    ae_all_iff.mpr fun p => ae_all_iff.mpr fun q => ae_all_iff.mpr fun hpq => hpair p q hpq
  filter_upwards [hall, hNlevy.cadlag_ae] with ω hrat hcad
  intro s t hst
  have hle_real : (N s ω : ℝ) ≤ (N t ω : ℝ) := by
    have hp_ex : ∀ n : ℕ, ∃ p : ℚ≥0, s < (p : ℝ≥0) ∧ (p : ℝ≥0) < s + 1 / ((n : ℝ≥0) + 1) := by
      intro n
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show (s : ℝ) < (s : ℝ) + 1 / ((n : ℝ) + 1) by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith)
      have hr0 : (0 : ℚ) ≤ r := by
        have : (0 : ℝ) ≤ (r : ℝ) := le_trans s.coe_nonneg (le_of_lt hr1)
        exact_mod_cast this
      refine ⟨⟨r, hr0⟩, ?_, ?_⟩
      · exact_mod_cast hr1
      · exact NNReal.coe_lt_coe.mp (by push_cast; exact hr2)
    have hq_ex : ∀ n : ℕ, ∃ q : ℚ≥0, t + 1 / ((n : ℝ≥0) + 1) < (q : ℝ≥0) ∧
        (q : ℝ≥0) < t + 2 / ((n : ℝ≥0) + 1) := by
      intro n
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show (t : ℝ) + 1 / ((n : ℝ) + 1) < (t : ℝ) + 2 / ((n : ℝ) + 1) by
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        have h2 : (2 : ℝ) / ((n : ℝ) + 1) = 2 * (1 / ((n : ℝ) + 1)) := by ring
        linarith)
      have hr0 : (0 : ℚ) ≤ r := by
        have : (0 : ℝ) ≤ (r : ℝ) := le_trans (by positivity) (le_of_lt hr1)
        exact_mod_cast this
      refine ⟨⟨r, hr0⟩, ?_, ?_⟩
      · exact NNReal.coe_lt_coe.mp (by push_cast; exact hr1)
      · exact NNReal.coe_lt_coe.mp (by push_cast; exact hr2)
    choose p hp1 hp2 using hp_ex
    choose q hq1 hq2 using hq_ex
    have hp_tend : Tendsto (fun n => (p n : ℝ≥0)) atTop (nhdsWithin s (Set.Ici s)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
        (Eventually.of_forall fun n => le_of_lt (hp1 n))
      rw [← NNReal.tendsto_coe]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by
          have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
            tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
          simpa using (tendsto_const_nhds (x := (s : ℝ))).add h0)
        (fun n => NNReal.coe_le_coe.mpr (le_of_lt (hp1 n)))
        (fun n => by
          have := NNReal.coe_le_coe.mpr (le_of_lt (hp2 n))
          simpa using this)
    have hq_tend : Tendsto (fun n => (q n : ℝ≥0)) atTop (nhdsWithin t (Set.Ici t)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
        (Eventually.of_forall fun n => le_trans le_self_add (le_of_lt (hq1 n)))
      rw [← NNReal.tendsto_coe]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by
          have h0 : Tendsto (fun n : ℕ => (2 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
            tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
          simpa using (tendsto_const_nhds (x := (t : ℝ))).add h0)
        (fun n => NNReal.coe_le_coe.mpr (le_trans le_self_add (le_of_lt (hq1 n))))
        (fun n => by
          have := NNReal.coe_le_coe.mpr (le_of_lt (hq2 n))
          simpa using this)
    have hpq : ∀ n : ℕ, p n ≤ q n := by
      intro n
      have h1 : (p n : ℝ≥0) < (q n : ℝ≥0) :=
        lt_trans (hp2 n) (lt_of_le_of_lt (add_le_add hst le_rfl) (hq1 n))
      have h2 : ((p n : ℚ) : ℝ) < ((q n : ℚ) : ℝ) := by
        simpa using NNReal.coe_lt_coe.mpr h1
      exact_mod_cast le_of_lt h2
    exact le_of_tendsto_of_tendsto ((hcad s).1.tendsto.comp hp_tend)
      ((hcad t).1.tendsto.comp hq_tend)
      (Eventually.of_forall fun n => hrat (p n) (q n) (hpq n))
  exact NNReal.coe_le_coe.mp (by simpa using hle_real)

private lemma poisson_laplace_transform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → ℕ) (r : ℝ≥0) (hNlaw : P.map N = ProbabilityTheory.poissonMeasure r)
    (q : ℝ) (hq : 0 ≤ q) :
    ∫ ω, Real.exp (-q * (N ω : ℝ)) ∂P = Real.exp (-(r : ℝ) * (1 - Real.exp (-q))) := by
  have hNae : AEMeasurable N P := by
    by_contra hnot
    have h0 : P.map N = 0 := Measure.map_of_not_aemeasurable hnot
    have h1 : (ProbabilityTheory.poissonMeasure r) Set.univ = 1 := measure_univ
    rw [← hNlaw, h0] at h1; simp at h1
  rw [← integral_map (f := fun n : ℕ => Real.exp (-q * (n : ℝ))) hNae (by fun_prop), hNlaw]
  have hint : Integrable (fun n : ℕ => Real.exp (-q * (n : ℝ))) (ProbabilityTheory.poissonMeasure r) := by
    refine (integrable_const (1 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
      (Eventually.of_forall fun n => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  rw [integral_countable hint]
  have hterm : ∀ n : ℕ,
      (ProbabilityTheory.poissonMeasure r).real {n} • Real.exp (-q * (n : ℝ)) =
        Real.exp (-(r : ℝ)) * (((r : ℝ) * Real.exp (-q)) ^ n / (Nat.factorial n : ℝ)) := by
    intro n
    rw [smul_eq_mul, poissonMeasure_real_singleton, mul_pow, ← Real.exp_nat_mul]
    have hexp2 : Real.exp ((n : ℝ) * -q) = Real.exp (-q * (n : ℝ)) := by congr 1; ring
    rw [hexp2]; ring
  simp_rw [hterm]
  rw [tsum_mul_left, (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * Real.exp (-q))).tsum_eq,
    ← Real.exp_eq_exp_ℝ, ← Real.exp_add]
  congr 1; ring

/-! ### Section 5: Existence of `δ`-Stable Subordinators and Symmetric `γ`-Stable Lévy Processes -/

private noncomputable def stableConst (δ : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), (1 - Real.exp (-x)) * x ^ (-1 - δ)

private lemma norm_cexp_sub_one_le {x : ℝ} (hx : 0 ≤ x) {z : ℂ} (hz : z.re ≤ 0) :
    ‖Complex.exp ((x : ℂ) * z) - 1‖ ≤ x * ‖z‖ := by
  let f : ℝ → ℂ := fun t => Complex.exp ((t : ℂ) * z)
  have hf_deriv : ∀ t : ℝ, HasDerivAt f (Complex.exp ((t : ℂ) * z) * (1 * z)) t := fun t =>
    ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z).cexp
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) x, ‖deriv f t‖ ≤ ‖z‖ := by
    intro t ht
    rw [(hf_deriv t).deriv, one_mul, norm_mul, Complex.norm_exp]
    have hre : ((t : ℂ) * z).re ≤ 0 := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonpos_of_nonneg_of_nonpos ht.1 hz
    calc Real.exp ((t : ℂ) * z).re * ‖z‖ ≤ 1 * ‖z‖ :=
          mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr hre) (norm_nonneg z)
      _ = ‖z‖ := one_mul _
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (hf_deriv t).differentiableAt) hbound (convex_Icc 0 x)
    ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩
  have h0 : f 0 = 1 := by simp [f]
  rw [h0, sub_zero, Real.norm_eq_abs, abs_of_nonneg hx, mul_comm] at h
  exact h

private lemma integrableOn_rpow_Ioc {δ : ℝ} (hδ1 : δ < 1) :
    IntegrableOn (fun x : ℝ => x ^ (-δ)) (Set.Ioc 0 1) volume :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    (intervalIntegral.intervalIntegrable_rpow' (by linarith))

private lemma integrableOn_rpow_Ioi {δ : ℝ} (hδ0 : 0 < δ) :
    IntegrableOn (fun x : ℝ => x ^ (-1 - δ)) (Set.Ioi 1) volume :=
  integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one

private lemma integrableOn_cexp_sub_one_rpow {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {z : ℂ} (hz : z.re ≤ 0) :
    IntegrableOn (fun x : ℝ => (Complex.exp ((x : ℂ) * z) - 1) * ((x ^ (-1 - δ) : ℝ) : ℂ))
      (Set.Ioi 0) volume := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have hmeas : AEStronglyMeasurable
        (fun x : ℝ => (Complex.exp ((x : ℂ) * z) - 1) * ((x ^ (-1 - δ) : ℝ) : ℂ))
        (volume.restrict (Set.Ioc 0 1)) := by
      refine (Continuous.aestronglyMeasurable (by fun_prop)).mul ?_
      exact (Complex.continuous_ofReal.measurable.comp (measurable_id.pow_const _)).aestronglyMeasurable
    refine ((integrableOn_rpow_Ioc hδ1).const_mul ‖z‖).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (le_of_lt hx.1) _)]
    have h1 := norm_cexp_sub_one_le (le_of_lt hx.1) hz
    have hrpow : x * x ^ (-1 - δ) = x ^ (-δ) := by
      calc x * x ^ (-1 - δ) = x ^ (1 : ℝ) * x ^ (-1 - δ) := by rw [Real.rpow_one]
        _ = x ^ (1 + (-1 - δ)) := (Real.rpow_add hx.1 _ _).symm
        _ = x ^ (-δ) := by congr 1; ring
    calc ‖Complex.exp ((x : ℂ) * z) - 1‖ * x ^ (-1 - δ)
        ≤ (x * ‖z‖) * x ^ (-1 - δ) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (le_of_lt hx.1) _)
      _ = ‖z‖ * (x * x ^ (-1 - δ)) := by ring
      _ = ‖z‖ * x ^ (-δ) := by rw [hrpow]
  · have hmeas : AEStronglyMeasurable
        (fun x : ℝ => (Complex.exp ((x : ℂ) * z) - 1) * ((x ^ (-1 - δ) : ℝ) : ℂ))
        (volume.restrict (Set.Ioi 1)) := by
      refine (Continuous.aestronglyMeasurable (by fun_prop)).mul ?_
      exact (Complex.continuous_ofReal.measurable.comp (measurable_id.pow_const _)).aestronglyMeasurable
    refine ((integrableOn_rpow_Ioi hδ0).const_mul 2).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (le_of_lt hx0) _)]
    have hre : ((x : ℂ) * z).re ≤ 0 := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hx0) hz
    have h2 : ‖Complex.exp ((x : ℂ) * z) - 1‖ ≤ 2 := by
      have hexp1 : Real.exp ((x : ℂ) * z).re ≤ 1 := Real.exp_le_one_iff.mpr hre
      calc ‖Complex.exp ((x : ℂ) * z) - 1‖
          ≤ ‖Complex.exp ((x : ℂ) * z)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = Real.exp ((x : ℂ) * z).re + 1 := by rw [Complex.norm_exp, norm_one]
        _ ≤ 2 := by linarith
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (le_of_lt hx0) _)

private lemma stableConst_integrableOn {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    IntegrableOn (fun x : ℝ => (1 - Real.exp (-x)) * x ^ (-1 - δ)) (Set.Ioi 0) volume := by
  have hc := (Complex.reCLM.integrable_comp
    (integrableOn_cexp_sub_one_rpow hδ0 hδ1 (z := (-1 : ℂ)) (by norm_num))).neg
  refine hc.congr (Eventually.of_forall fun x => ?_)
  have h1 : Complex.exp ((x : ℂ) * (-1 : ℂ)) = ((Real.exp (-x) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1; simp
  change -(((Complex.exp ((x : ℂ) * (-1 : ℂ)) - 1) * ((x ^ (-1 - δ) : ℝ) : ℂ)).re) =
    (1 - Real.exp (-x)) * x ^ (-1 - δ)
  rw [h1, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

private lemma stableConst_pos {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 < stableConst δ := by
  let f : ℝ → ℝ := fun x => (1 - Real.exp (-x)) * x ^ (-1 - δ)
  have hf_int : IntegrableOn f (Set.Ioi 0) volume := stableConst_integrableOn hδ0 hδ1
  have hsub : Set.Ioc (1 : ℝ) 2 ⊆ Set.Ioi 0 := fun x hx => lt_trans zero_lt_one hx.1
  have hnn : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))), 0 ≤ f x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    have h1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (le_of_lt hx0) _)
  have hle1 : ∫ x in Set.Ioc (1 : ℝ) 2, f x ≤ ∫ x in Set.Ioi (0 : ℝ), f x :=
    setIntegral_mono_set hf_int hnn hsub.eventuallyLE
  let m0 : ℝ := (1 - Real.exp (-1)) * (2 : ℝ) ^ (-1 - δ)
  have hm0_pos : 0 < m0 := by
    have h1 : Real.exp (-1 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    exact mul_pos (by linarith) (Real.rpow_pos_of_pos (by norm_num) _)
  have hle2 : ∫ _ in Set.Ioc (1 : ℝ) 2, m0 ≤ ∫ x in Set.Ioc (1 : ℝ) 2, f x := by
    refine setIntegral_mono_on (integrableOn_const (by simp)) (hf_int.mono_set hsub)
      measurableSet_Ioc fun x hx => ?_
    have hexp : Real.exp (-x) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith [hx.1])
    have hrp : (2 : ℝ) ^ (-1 - δ) ≤ x ^ (-1 - δ) :=
      Real.rpow_le_rpow_of_nonpos (lt_trans zero_lt_one hx.1) hx.2 (by linarith)
    exact mul_le_mul (by linarith) hrp (Real.rpow_nonneg (by norm_num) _)
      (by linarith [Real.exp_lt_one_iff.mpr (show (-1 : ℝ) < 0 by norm_num)])
  have hconst : ∫ _ in Set.Ioc (1 : ℝ) 2, m0 = m0 := by
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le (by norm_num)]
    norm_num
  dsimp only [stableConst]
  linarith

private lemma stable_laplace_integral {δ : ℝ} (hδ0 : 0 < δ) (_hδ1 : δ < 1)
    {q : ℝ} (hq : 0 ≤ q) :
    ∫ x in Set.Ioi (0 : ℝ), (1 - Real.exp (-q * x)) * x ^ (-1 - δ) = q ^ δ * stableConst δ := by
  rcases eq_or_lt_of_le hq with rfl | hqpos
  · simp [Real.zero_rpow hδ0.ne']
  · have hcomp := MeasureTheory.integral_comp_mul_left_Ioi
      (fun y : ℝ => (1 - Real.exp (-y)) * y ^ (-1 - δ)) 0 hqpos
    rw [mul_zero, smul_eq_mul] at hcomp
    have hcongr : ∫ x in Set.Ioi (0 : ℝ), (1 - Real.exp (-(q * x))) * (q * x) ^ (-1 - δ) =
        q ^ (-1 - δ) * ∫ x in Set.Ioi (0 : ℝ), (1 - Real.exp (-q * x)) * x ^ (-1 - δ) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      rw [Real.mul_rpow (le_of_lt hqpos) (le_of_lt hx)]
      ring
    rw [hcongr] at hcomp
    have hqne : q ^ (-1 - δ) ≠ 0 := (Real.rpow_pos_of_pos hqpos _).ne'
    have hinv : q ^ (-1 - δ) * (q ^ δ * stableConst δ) = q⁻¹ * stableConst δ := by
      rw [← mul_assoc, ← Real.rpow_add hqpos]
      have hexp : -1 - δ + δ = (-1 : ℝ) := by ring
      rw [hexp, Real.rpow_neg_one]
    exact mul_left_cancel₀ hqne (hcomp.trans hinv.symm)

private lemma toReal_mul_integral_prmPieceLaw_complex
    {E : Type} [MeasurableSpace E] [Nonempty E] {m : Measure E} [SigmaFinite m]
    (k : ℕ) (w : E → ℂ) :
    ((m (prmPiece m k)).toReal : ℂ) * ∫ x, w x ∂(prmPieceLaw m k) =
      ∫ x in prmPiece m k, w x ∂m := by
  by_cases h : m (prmPiece m k) = 0
  · rw [h, ENNReal.toReal_zero, Complex.ofReal_zero, zero_mul,
      Measure.restrict_eq_zero.mpr h, integral_zero_measure]
  · have ht : (m (prmPiece m k)).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨h, (measure_prmPiece_lt_top).ne⟩
    have hlaw : prmPieceLaw m k = (m (prmPiece m k))⁻¹ • m.restrict (prmPiece m k) := by
      unfold prmPieceLaw; rw [if_neg h]
    rw [hlaw, integral_smul_measure, Complex.real_smul, ENNReal.toReal_inv, ← mul_assoc,
      ← Complex.ofReal_mul, mul_inv_cancel₀ ht, Complex.ofReal_one, one_mul]

private lemma indepFun_prefix_nextBlock
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    {m : Measure E} [SigmaFinite m] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    (hd : IsPoissonPointFamily K X m μ) (M : ℕ) :
    IndepFun
      (fun ω (k : Fin M) => (K k.1 ω, fun n => X k.1 n ω))
      (fun ω => (K M ω, fun n => X M n ω)) μ := by
  let φ : Fin M ⊕ (Fin M × ℕ) → ℕ ⊕ ℕ × ℕ :=
    Sum.elim (fun k => Sum.inl k.1) (fun p => Sum.inr (p.1.1, p.2))
  let ψ : Unit ⊕ ℕ → ℕ ⊕ ℕ × ℕ :=
    Sum.elim (fun _ => Sum.inl M) (fun n => Sum.inr (M, n))
  have hφ : Function.Injective φ := by
    rintro (a | ⟨a, na⟩) (b | ⟨b, nb⟩) hab <;> simp [φ] at hab
    · congr 1; exact Fin.ext hab
    · congr 1; exact Prod.ext (Fin.ext hab.1) hab.2
  have hψ : Function.Injective ψ := by
    rintro (a | na) (b | nb) hab <;> simp [ψ] at hab
    · rfl
    · congr 1
  have hST : ∀ s t, φ s ≠ ψ t := by
    rintro (k | ⟨k, nk⟩) (⟨⟩ | n) <;> simp [φ, ψ]
    · exact ne_of_lt k.2
    · exact fun h _ => ne_of_lt k.2 h
  have h := hd.indepFun_pointFamily_split φ ψ hφ hψ hST
  have hextrL : Measurable
      (fun (g : (i : Fin M ⊕ (Fin M × ℕ)) → pointFamilyIndexType E (φ i)) (k : Fin M) =>
        (g (Sum.inl k), fun n => g (Sum.inr (k, n)))) :=
    measurable_pi_lambda _ fun k =>
      (measurable_pi_apply (Sum.inl k)).prodMk
        (measurable_pi_lambda _ fun n => measurable_pi_apply (Sum.inr (k, n)))
  have hextrR : Measurable
      (fun (g : (j : Unit ⊕ ℕ) → pointFamilyIndexType E (ψ j)) =>
        (g (Sum.inl ()), fun n => g (Sum.inr n))) :=
    (measurable_pi_apply (Sum.inl ())).prodMk
      (measurable_pi_lambda _ fun n => measurable_pi_apply (Sum.inr n))
  exact h.comp hextrL hextrR

private lemma prm_exp_integral
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    {m : Measure E} [SigmaFinite m] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    (hd : IsPoissonPointFamily K X m μ)
    {g : E → ℂ} (hg : Measurable g) (hre : ∀ x, (g x).re ≤ 0)
    (hint : Integrable (fun x => Complex.exp (g x) - 1) m)
    {S : Ω → ℂ}
    (hS : ∀ᵐ ω ∂μ, Tendsto (fun M => ∑ k ∈ Finset.range M, ∑ n ∈ Finset.range (K k ω), g (X k n ω))
      atTop (nhds (S ω))) :
    ∫ ω, Complex.exp (S ω) ∂μ = Complex.exp (∫ x, (Complex.exp (g x) - 1) ∂m) := by
  let B : ℕ → Ω → ℂ := fun k ω => ∏ n ∈ Finset.range (K k ω), Complex.exp (g (X k n ω))
  have hB_block_meas : Measurable (fun p : ℕ × (ℕ → E) =>
      ∏ n ∈ Finset.range p.1, Complex.exp (g (p.2 n))) := by
    have h : Measurable (fun p : (ℕ → E) × ℕ => ∏ n ∈ Finset.range p.2, Complex.exp (g (p.1 n))) :=
      measurable_from_prod_countable_left fun j =>
        Finset.measurable_prod (Finset.range j) fun n _ =>
          Complex.continuous_exp.measurable.comp (hg.comp (measurable_pi_apply n))
    exact h.comp measurable_swap
  have hB_meas : ∀ k, Measurable (B k) := fun k =>
    hB_block_meas.comp ((hd.measurable_count k).prodMk (measurable_pi_lambda _ fun n => hd.measurable_point k n))
  have hB_norm : ∀ k ω, ‖B k ω‖ ≤ 1 := fun k ω => by
    dsimp only [B]; rw [norm_prod]
    refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun n _ => ?_
    rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr (hre _)
  have hB_int : ∀ k, ∫ ω, B k ω ∂μ = Complex.exp (∫ x in prmPiece m k, (Complex.exp (g x) - 1) ∂m) := by
    intro k
    have h1 := integral_pieceProd_eq_exp hd (k := k) (w := fun x => Complex.exp (g x))
      (Complex.continuous_exp.measurable.comp hg) (fun x => by
        rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr (hre x))
    dsimp only [B]
    rw [h1]; congr 1
    have hsub : (∫ x, Complex.exp (g x) ∂(prmPieceLaw m k)) - 1 =
        ∫ x, (Complex.exp (g x) - 1) ∂(prmPieceLaw m k) := by
      have hcexp_int : Integrable (fun x => Complex.exp (g x)) (prmPieceLaw m k) :=
        (integrable_const (1 : ℝ)).mono' (Complex.continuous_exp.measurable.comp hg).aestronglyMeasurable
          (Eventually.of_forall fun x => by rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr (hre x))
      rw [integral_sub hcexp_int (integrable_const (1 : ℂ)), integral_const, probReal_univ, one_smul]
    rw [hsub, toReal_mul_integral_prmPieceLaw_complex]
  have hprod_int : ∀ M : ℕ,
      ∫ ω, ∏ k ∈ Finset.range M, B k ω ∂μ =
        Complex.exp (∑ k ∈ Finset.range M, ∫ x in prmPiece m k, (Complex.exp (g x) - 1) ∂m) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      have hsplit : (fun ω => ∏ k ∈ Finset.range (M + 1), B k ω) =
          fun ω => (∏ k ∈ Finset.range M, B k ω) * B M ω := by
        funext ω; exact Finset.prod_range_succ _ M
      rw [hsplit]
      have hind_M : IndepFun (fun ω => ∏ k ∈ Finset.range M, B k ω) (B M) μ := by
        have hpref : Measurable (fun f : Fin M → ℕ × (ℕ → E) =>
            ∏ k : Fin M, ∏ n ∈ Finset.range (f k).1, Complex.exp (g ((f k).2 n))) :=
          Finset.measurable_prod Finset.univ fun k _ => hB_block_meas.comp (measurable_pi_apply k)
        have hind := (indepFun_prefix_nextBlock hd M).comp hpref hB_block_meas
        have hL : (fun ω => ∏ k : Fin M, ∏ n ∈ Finset.range (K k.1 ω), Complex.exp (g (X k.1 n ω))) =
            fun ω => ∏ k ∈ Finset.range M, B k ω := by
          funext ω; exact Fin.prod_univ_eq_prod_range (fun k => B k ω) M
        simpa only [Function.comp_def, hL] using hind
      have hL_meas : Measurable (fun ω => ∏ k ∈ Finset.range M, B k ω) :=
        Finset.measurable_prod (Finset.range M) fun k _ => hB_meas k
      rw [hind_M.integral_fun_mul_eq_mul_integral hL_meas.aestronglyMeasurable (hB_meas M).aestronglyMeasurable,
        ih, hB_int M, ← Complex.exp_add, Finset.sum_range_succ]
  have hLHS_tend : Tendsto (fun M => ∫ ω, ∏ k ∈ Finset.range M, B k ω ∂μ)
      atTop (nhds (∫ ω, Complex.exp (S ω) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun M => (Finset.measurable_prod (Finset.range M) fun k _ => hB_meas k).aestronglyMeasurable)
      (integrable_const 1)
      (fun M => Eventually.of_forall fun ω => by
        rw [norm_prod]
        exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun k _ => hB_norm k ω) ?_
    filter_upwards [hS] with ω hω
    have heq : (fun M => ∏ k ∈ Finset.range M, B k ω) =
        fun M => Complex.exp (∑ k ∈ Finset.range M, ∑ n ∈ Finset.range (K k ω), g (X k n ω)) := by
      funext M; simp only [B, Complex.exp_sum]
    rw [heq]
    exact (Complex.continuous_exp.tendsto (S ω)).comp hω
  have hRHS_tend : Tendsto
      (fun M => Complex.exp (∑ k ∈ Finset.range M, ∫ x in prmPiece m k, (Complex.exp (g x) - 1) ∂m))
      atTop (nhds (Complex.exp (∫ x, (Complex.exp (g x) - 1) ∂m))) := by
    have hsum : HasSum (fun k => ∫ x in prmPiece m k, (Complex.exp (g x) - 1) ∂m)
        (∫ x, (Complex.exp (g x) - 1) ∂m) := by
      have h1 := hasSum_integral_iUnion (f := fun x => Complex.exp (g x) - 1) (μ := m)
        (fun k => measurableSet_prmPiece (m := m)) (pairwise_disjoint_prmPiece (m := m))
        (by rw [iUnion_prmPiece (m := m)]; exact hint.integrableOn)
      rwa [iUnion_prmPiece (m := m), setIntegral_univ] at h1
    exact (Complex.continuous_exp.tendsto _).comp hsum.tendsto_sum_nat
  simp_rw [hprod_int] at hLHS_tend
  exact tendsto_nhds_unique hLHS_tend hRHS_tend

private noncomputable def stableDensity (δ c : ℝ) (x : ℝ) : ℝ≥0 :=
  Real.toNNReal (if 0 < x then c * x ^ (-1 - δ) else 0)

private lemma stableDensity_measurable (δ c : ℝ) : Measurable (stableDensity δ c) :=
  (Measurable.ite measurableSet_Ioi (measurable_const.mul (measurable_id.pow_const _))
    measurable_const).real_toNNReal

private lemma stableDensity_pos {δ c x : ℝ} (hc_pos : 0 < c) (hx : 0 < x) :
    (stableDensity δ c x : ℝ) = c * x ^ (-1 - δ) := by
  simp only [stableDensity, if_pos hx, Real.coe_toNNReal']
  exact max_eq_left (mul_nonneg (le_of_lt hc_pos) (Real.rpow_nonneg (le_of_lt hx) _))

private lemma stable_prm_slice_integral {δ c : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc_pos : 0 < c)
    {s₁ s₂ : ℝ≥0} (hle : s₁ ≤ s₂) {z : ℂ} (hz : z.re ≤ 0) :
    Integrable ((Set.Ioc (s₁ : ℝ) (s₂ : ℝ) ×ˢ Set.Ioi (0 : ℝ)).indicator
      (fun q : ℝ × ℝ => Complex.exp ((q.2 : ℂ) * z) - 1))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.withDensity fun x => (stableDensity δ c x : ℝ≥0∞))) ∧
    (∫ p, (Set.Ioc (s₁ : ℝ) (s₂ : ℝ) ×ˢ Set.Ioi (0 : ℝ)).indicator
        (fun q : ℝ × ℝ => Complex.exp ((q.2 : ℂ) * z) - 1) p
        ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.withDensity fun x => (stableDensity δ c x : ℝ≥0∞)))) =
      (((s₂ : ℝ) - (s₁ : ℝ)) : ℂ) *
        ∫ x in Set.Ioi (0 : ℝ), (Complex.exp ((x : ℂ) * z) - 1) * ((c * x ^ (-1 - δ) : ℝ) : ℂ) := by
  set ν : Measure ℝ := volume.withDensity fun x => (stableDensity δ c x : ℝ≥0∞) with hν_def
  have : SigmaFinite ν := MeasureTheory.SigmaFinite.withDensity (stableDensity δ c)
  have hρ_meas : Measurable (stableDensity δ c) := stableDensity_measurable δ c
  set F1 : ℝ → ℂ := (Set.Ioc (s₁ : ℝ) (s₂ : ℝ)).indicator (fun _ => (1 : ℂ))
  set F2 : ℝ → ℂ := (Set.Ioi (0 : ℝ)).indicator (fun x => Complex.exp ((x : ℂ) * z) - 1)
  have hcongr_ρ : (fun x : ℝ => stableDensity δ c x • F2 x) =
      (Set.Ioi (0 : ℝ)).indicator (fun x => (Complex.exp ((x : ℂ) * z) - 1) * ((c * x ^ (-1 - δ) : ℝ) : ℂ)) := by
    funext x
    by_cases hx : x ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hx, NNReal.smul_def, Complex.real_smul,
        stableDensity_pos hc_pos hx, mul_comm]
      simp [F2, Set.indicator_of_mem hx]
    · simp [F2, Set.indicator_of_notMem hx]
  have hslice_int : Integrable F2 ν := by
    rw [hν_def, integrable_withDensity_iff_integrable_smul hρ_meas, hcongr_ρ,
      integrable_indicator_iff measurableSet_Ioi]
    have h1 := (integrableOn_cexp_sub_one_rpow hδ0 hδ1 hz).const_mul (c : ℂ)
    exact h1.congr (Eventually.of_forall fun x => by push_cast; ring)
  have hslice_val : (∫ x, F2 x ∂ν) =
      ∫ x in Set.Ioi (0 : ℝ), (Complex.exp ((x : ℂ) * z) - 1) * ((c * x ^ (-1 - δ) : ℝ) : ℂ) := by
    rw [hν_def, integral_withDensity_eq_integral_smul hρ_meas, hcongr_ρ, integral_indicator measurableSet_Ioi]
  have hprod_eq : (Set.Ioc (s₁ : ℝ) (s₂ : ℝ) ×ˢ Set.Ioi (0 : ℝ)).indicator
        (fun q : ℝ × ℝ => Complex.exp ((q.2 : ℂ) * z) - 1) =
      fun p : ℝ × ℝ => F1 p.1 * F2 p.2 := by
    funext ⟨s, x⟩
    by_cases hs : s ∈ Set.Ioc (s₁ : ℝ) (s₂ : ℝ) <;>
    by_cases hx : x ∈ Set.Ioi (0 : ℝ) <;>
    simp [F1, F2, Set.mem_prod, hs, hx]
  have hfst_int : Integrable F1 (volume.restrict (Set.Ioi (0 : ℝ))) := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact integrableOn_const (lt_of_le_of_lt (Measure.restrict_apply_le _ _)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)).ne
  have hint_j : Integrable ((Set.Ioc (s₁ : ℝ) (s₂ : ℝ) ×ˢ Set.Ioi (0 : ℝ)).indicator
      (fun q : ℝ × ℝ => Complex.exp ((q.2 : ℂ) * z) - 1)) ((volume.restrict (Set.Ioi (0 : ℝ))).prod ν) := by
    rw [hprod_eq, integrable_prod_iff]
    · refine ⟨Eventually.of_forall fun s => hslice_int.const_mul (F1 s), ?_⟩
      have heq : (fun s => ∫ x, ‖F1 s * F2 x‖ ∂ν) = fun s => ‖F1 s‖ * ∫ x, ‖F2 x‖ ∂ν := by
        funext s; simp_rw [norm_mul, integral_const_mul]
      rw [heq]; exact hfst_int.norm.mul_const _
    · exact (hfst_int.aestronglyMeasurable.comp_fst).mul (hslice_int.aestronglyMeasurable.comp_snd)
  refine ⟨hint_j, ?_⟩
  rw [hprod_eq, integral_prod_mul, hslice_val, integral_indicator measurableSet_Ioc, setIntegral_const,
    Complex.real_smul, mul_one, Measure.real, Measure.restrict_apply measurableSet_Ioc]
  have hinter : Set.Ioc (s₁ : ℝ) (s₂ : ℝ) ∩ Set.Ioi (0 : ℝ) = Set.Ioc (s₁ : ℝ) (s₂ : ℝ) :=
    Set.inter_eq_left.mpr fun s hs => lt_of_le_of_lt s₁.coe_nonneg hs.1
  rw [hinter, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hle)),
    Complex.ofReal_sub]

private lemma prm_subordinator_cadlag
    (K : ℕ → ℕ) (X : ℕ → ℕ → ℝ × ℝ)
    (hfin : ∀ t : ℝ≥0,
      (∑' k : ℕ, ∑ n ∈ Finset.range (K k),
        if X k n ∈ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.Ioi (0 : ℝ)) then ENNReal.ofReal (X k n).2 else 0) < ⊤) :
    IsCadlag (fun t : ℝ≥0 =>
      ((∑' k : ℕ, ∑ n ∈ Finset.range (K k),
        if X k n ∈ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.Ioi (0 : ℝ)) then ENNReal.ofReal (X k n).2 else 0).toNNReal : ℝ)) := by
  let tilde_τ : ℝ≥0 → ℝ≥0∞ := fun t =>
    ∑' k : ℕ, ∑ n ∈ Finset.range (K k),
      if X k n ∈ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.Ioi (0 : ℝ)) then ENNReal.ofReal (X k n).2 else 0
  let τ : ℝ≥0 → ℝ≥0 := fun t => (tilde_τ t).toNNReal
  have hmonR : Monotone (fun t : ℝ≥0 => (τ t : ℝ)) := by
    intro s t hst
    have hle : tilde_τ s ≤ tilde_τ t := by
      refine ENNReal.tsum_le_tsum fun k => Finset.sum_le_sum fun n _ => ?_
      split_ifs with h1 h2
      · exact le_rfl
      · exfalso; exact h2 ⟨⟨h1.1.1, le_trans h1.1.2 (NNReal.coe_le_coe.mpr hst)⟩, h1.2⟩
      · exact bot_le
      · exact le_rfl
    exact NNReal.coe_le_coe.mpr ((ENNReal.toNNReal_le_toNNReal (hfin s).ne (hfin t).ne).mpr hle)
  intro t
  refine ⟨?_, ⟨sSup ((fun s => (τ s : ℝ)) '' Set.Iio t), hmonR.tendsto_nhdsLT t⟩⟩
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨T, hT⟩ := exists_nat_gt ((t : ℝ) + 1)
  let a : ℕ → ℝ := fun k =>
    ∑ n ∈ Finset.range (K k),
      if X k n ∈ (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ Set.Ioi (0 : ℝ)) then (X k n).2 else 0
  have ha_nn : ∀ k, 0 ≤ a k := fun k =>
    Finset.sum_nonneg fun n _ => by
      split_ifs with h
      · exact le_of_lt h.2
      · exact le_rfl
  have htilde_T : tilde_τ (T : ℝ≥0) = ∑' k, ENNReal.ofReal (a k) := by
    have hTcoe : ((T : ℝ≥0) : ℝ) = (T : ℝ) := rfl
    dsimp only [tilde_τ]; simp only [hTcoe]
    refine tsum_congr fun k => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => by
      split_ifs with h
      · exact le_of_lt h.2
      · exact le_rfl)]
    refine Finset.sum_congr rfl fun n _ => by split_ifs <;> simp
  have ha_sum : Summable a := by
    have hlt : (∑' k, ENNReal.ofReal (a k)) < ⊤ := htilde_T ▸ hfin (T : ℝ≥0)
    exact ENNReal.summable_toReal hlt.ne |>.congr fun k => ENNReal.toReal_ofReal (ha_nn k)
  have htail_tend : Tendsto (fun M => ∑' k, a (k + M)) atTop (nhds 0) := by
    have hsub : (fun M => ∑' k, a (k + M)) = fun M => (∑' k, a k) - ∑ k ∈ Finset.range M, a k := by
      funext M; linarith [ha_sum.sum_add_tsum_nat_add M]
    rw [hsub, ← sub_self (∑' k, a k)]
    exact tendsto_const_nhds.sub ha_sum.hasSum.tendsto_sum_nat
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp htail_tend ε hε)
  have htail_lt : (∑' k, a (k + M)) < ε := by
    have h0 := hM M le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun k => ha_nn _)] at h0
    exact h0
  let pts : Finset ℝ :=
    ((Finset.range M).biUnion fun k =>
      (Finset.range (K k)).image fun n => (X k n).1).filter (fun r => (t : ℝ) < r)
  let δ₀ : ℝ := min 1 (if hne : pts.Nonempty then pts.min' hne - (t : ℝ) else 1)
  have hδ₀_pos : 0 < δ₀ := by
    refine lt_min one_pos ?_
    split_ifs with hne
    · have hm := Finset.min'_mem pts hne
      have hgt : (t : ℝ) < pts.min' hne := (Finset.mem_filter.mp hm).2
      linarith
    · exact one_pos
  refine ⟨δ₀, hδ₀_pos, fun s hs hdist => ?_⟩
  have hts : t ≤ s := hs
  have hs_lt_tδ : (s : ℝ) < (t : ℝ) + δ₀ := by
    rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hts))] at hdist
    linarith
  have hs_le_T : (s : ℝ) ≤ (T : ℝ) := by
    have : δ₀ ≤ 1 := min_le_left _ _
    linarith
  have hno_early : ∀ k < M, ∀ n < K k,
      X k n ∉ (Set.Ioc (t : ℝ) (s : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    intro k hk n hn hmem
    have hpt_mem : (X k n).1 ∈ pts := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk,
        Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, rfl⟩⟩, hmem.1.1⟩
    have hne : pts.Nonempty := ⟨_, hpt_mem⟩
    have hle_min : pts.min' hne ≤ (X k n).1 := Finset.min'_le _ _ hpt_mem
    have hδ_le : δ₀ ≤ pts.min' hne - (t : ℝ) := by
      have : δ₀ ≤ (if hne' : pts.Nonempty then pts.min' hne' - (t : ℝ) else 1) := min_le_right _ _
      simpa [hne] using this
    linarith [hmem.1.2]
  let bs : ℕ → ℝ := fun k =>
    ∑ n ∈ Finset.range (K k),
      if X k n ∈ (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ Set.Ioi (0 : ℝ)) then (X k n).2 else 0
  let bt : ℕ → ℝ := fun k =>
    ∑ n ∈ Finset.range (K k),
      if X k n ∈ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.Ioi (0 : ℝ)) then (X k n).2 else 0
  have hbs_nn : ∀ k, 0 ≤ bs k := fun k =>
    Finset.sum_nonneg fun n _ => by
      split_ifs with h
      · exact le_of_lt h.2
      · exact le_rfl
  have hbt_nn : ∀ k, 0 ≤ bt k := fun k =>
    Finset.sum_nonneg fun n _ => by
      split_ifs with h
      · exact le_of_lt h.2
      · exact le_rfl
  have hbs_le_a : ∀ k, bs k ≤ a k := fun k =>
    Finset.sum_le_sum fun n _ => by
      by_cases h1 : X k n ∈ (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ Set.Ioi (0 : ℝ))
      · have h2 : X k n ∈ (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ Set.Ioi (0 : ℝ)) :=
          ⟨⟨h1.1.1, le_trans h1.1.2 hs_le_T⟩, h1.2⟩
        simp [h1, h2]
      · rw [if_neg h1]
        split_ifs with h2
        · exact le_of_lt h2.2
        · exact le_rfl
  have hbt_le_bs : ∀ k, bt k ≤ bs k := fun k =>
    Finset.sum_le_sum fun n _ => by
      by_cases h1 : X k n ∈ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.Ioi (0 : ℝ))
      · have h2 : X k n ∈ (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ Set.Ioi (0 : ℝ)) :=
          ⟨⟨h1.1.1, le_trans h1.1.2 (NNReal.coe_le_coe.mpr hts)⟩, h1.2⟩
        simp [h1, h2]
      · rw [if_neg h1]
        split_ifs with h2
        · exact le_of_lt h2.2
        · exact le_rfl
  have hbs_sum : Summable bs := Summable.of_nonneg_of_le hbs_nn hbs_le_a ha_sum
  have hbt_sum : Summable bt := Summable.of_nonneg_of_le hbt_nn (fun k => le_trans (hbt_le_bs k) (hbs_le_a k)) ha_sum
  have hτs_eq : (τ s : ℝ) = ∑' k, bs k := by
    have htilde_s : tilde_τ s = ∑' k, ENNReal.ofReal (bs k) := by
      refine tsum_congr fun k => ?_
      rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => by
        split_ifs with h
        · exact le_of_lt h.2
        · exact le_rfl)]
      refine Finset.sum_congr rfl fun n _ => by split_ifs <;> simp
    change (tilde_τ s).toReal = _
    rw [htilde_s, ← ENNReal.ofReal_tsum_of_nonneg hbs_nn hbs_sum, ENNReal.toReal_ofReal (tsum_nonneg hbs_nn)]
  have hτt_eq : (τ t : ℝ) = ∑' k, bt k := by
    have htilde_t : tilde_τ t = ∑' k, ENNReal.ofReal (bt k) := by
      refine tsum_congr fun k => ?_
      rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => by
        split_ifs with h
        · exact le_of_lt h.2
        · exact le_rfl)]
      refine Finset.sum_congr rfl fun n _ => by split_ifs <;> simp
    change (tilde_τ t).toReal = _
    rw [htilde_t, ← ENNReal.ofReal_tsum_of_nonneg hbt_nn hbt_sum, ENNReal.toReal_ofReal (tsum_nonneg hbt_nn)]
  have hhead_eq : ∑ k ∈ Finset.range M, bs k = ∑ k ∈ Finset.range M, bt k := by
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun n hn => ?_
    by_cases h1 : X k n ∈ (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ Set.Ioi (0 : ℝ))
    · have h2 : X k n ∈ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
        by_contra hnot
        have hgt : (t : ℝ) < (X k n).1 := by
          by_contra hle; exact hnot ⟨⟨h1.1.1, not_lt.mp hle⟩, h1.2⟩
        exact hno_early k (Finset.mem_range.mp hk) n (Finset.mem_range.mp hn) ⟨⟨hgt, h1.1.2⟩, h1.2⟩
      simp [h1, h2]
    · have h2 : X k n ∉ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.Ioi (0 : ℝ)) :=
        fun h => h1 ⟨⟨h.1.1, le_trans h.1.2 (NNReal.coe_le_coe.mpr hts)⟩, h.2⟩
      simp [h1, h2]
  have htail_le : (∑' k, bs (k + M)) ≤ ∑' k, a (k + M) :=
    (hbs_sum.comp_injective (add_left_injective M)).tsum_le_tsum (fun k => hbs_le_a (k + M))
      (ha_sum.comp_injective (add_left_injective M))
  have hdiff_real : (τ s : ℝ) - (τ t : ℝ) ≤ ∑' k, a (k + M) := by
    rw [hτs_eq, hτt_eq, ← hbs_sum.sum_add_tsum_nat_add M, ← hbt_sum.sum_add_tsum_nat_add M, hhead_eq]
    have hbt_tail_nn : 0 ≤ ∑' k, bt (k + M) := tsum_nonneg fun k => hbt_nn (k + M)
    linarith
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hmonR hts))]
  linarith

private lemma exists_stable_subordinator (δ C : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hC : 0 < C) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (τ : ℝ≥0 → Ω → ℝ≥0),
      IsLevyProcess (fun t ω => (τ t ω : ℝ)) P ∧
      (∀ᵐ ω ∂P, Monotone (fun t => τ t ω)) ∧
      ∀ q : ℝ, 0 ≤ q → ∀ t : ℝ≥0,
        ∫ ω, Real.exp (-q * (τ t ω : ℝ)) ∂P = Real.exp (-(t : ℝ) * C * q ^ δ) := by
  let c : ℝ := C / stableConst δ
  have hc_pos : 0 < c := div_pos hC (stableConst_pos hδ0 hδ1)
  let ρ : ℝ → ℝ≥0 := stableDensity δ c
  have hρ_meas : Measurable ρ := stableDensity_measurable δ c
  have hρ_pos : ∀ {x : ℝ}, 0 < x → (ρ x : ℝ) = c * x ^ (-1 - δ) := fun hx => stableDensity_pos hc_pos hx
  let ν : Measure ℝ := volume.withDensity (fun x => (ρ x : ℝ≥0∞))
  have : SigmaFinite ν := MeasureTheory.SigmaFinite.withDensity ρ
  let m : Measure (ℝ × ℝ) := (volume.restrict (Set.Ioi (0 : ℝ))).prod ν
  have : SigmaFinite m := inferInstance
  have : Nonempty (ℝ × ℝ) := ⟨(0, 0)⟩
  obtain ⟨Ω, mΩ, P, fam, hfam_meas, hfam_law, hfam_indep, hP⟩ :=
    ProbabilityTheory.exists_hasLaw_indepFun (pointFamilyIndexType (ℝ × ℝ)) (pointFamilyLaw m)
  let : MeasurableSpace Ω := mΩ
  let : IsProbabilityMeasure P := hP
  let K : ℕ → Ω → ℕ := fun k => fam (Sum.inl k)
  let X : ℕ → ℕ → Ω → ℝ × ℝ := fun k n => fam (Sum.inr (k, n))
  have hcomb : pointFamilyCombined K X = fam := by
    funext i ω; rcases i with k | ⟨k, n⟩ <;> rfl
  have hd : IsPoissonPointFamily K X m P :=
    { measurable_count := fun k => hfam_meas (Sum.inl k)
      measurable_point := fun k n => hfam_meas (Sum.inr (k, n))
      indep := by rw [hcomb]; exact hfam_indep
      law_count := fun k => hfam_law (Sum.inl k)
      law_point := fun k n => hfam_law (Sum.inr (k, n)) }
  let tilde_τ : ℝ≥0 → Ω → ℝ≥0∞ := fun t ω =>
    ∑' k : ℕ, ∑ n ∈ Finset.range (K k ω),
      if X k n ω ∈ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.Ioi (0 : ℝ)) then ENNReal.ofReal (X k n ω).2 else 0
  let τ : ℝ≥0 → Ω → ℝ≥0 := fun t ω => (tilde_τ t ω).toNNReal
  have htilde_meas : ∀ t : ℝ≥0, Measurable (tilde_τ t) := by
    intro t
    have hset : MeasurableSet (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.Ioi (0 : ℝ)) :=
      measurableSet_Ioc.prod measurableSet_Ioi
    refine Measurable.tsum fun k => ?_
    have hp : Measurable (fun p : Ω × ℕ => ∑ n ∈ Finset.range p.2,
        if X k n p.1 ∈ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.Ioi (0 : ℝ)) then ENNReal.ofReal (X k n p.1).2 else 0) :=
      measurable_from_prod_countable_left fun j =>
        Finset.measurable_sum (Finset.range j) fun n _ =>
          Measurable.ite (hd.measurable_point k n hset)
            (ENNReal.measurable_ofReal.comp (measurable_snd.comp (hd.measurable_point k n)))
            measurable_const
    exact hp.comp (measurable_id.prodMk (hd.measurable_count k))
  have hτ_meas : ∀ t : ℝ≥0, Measurable (τ t) := fun t =>
    ENNReal.measurable_toNNReal.comp (htilde_meas t)
  -- Step 1: Almost sure simultaneous finiteness of tilde_τ t ω for all t
  have hfin_T : ∀ T : ℕ, ∀ᵐ ω ∂P, tilde_τ (T : ℝ≥0) ω < ⊤ := by
    intro T
    let A_small : Set (ℝ × ℝ) := Set.Ioc 0 (T : ℝ) ×ˢ Set.Ioc 0 1
    let A_big : Set (ℝ × ℝ) := Set.Ioc 0 (T : ℝ) ×ˢ Set.Ioi 1
    have hAs_meas : MeasurableSet A_small := measurableSet_Ioc.prod measurableSet_Ioc
    have hAb_meas : MeasurableSet A_big := measurableSet_Ioc.prod measurableSet_Ioi
    -- Small jumps: finite mean by Campbell (integral_pieceSum)
    let f_s : ℝ × ℝ → ℝ := fun z => if z ∈ A_small then z.2 else 0
    have hfs_meas : Measurable f_s := Measurable.ite hAs_meas measurable_snd measurable_const
    have hfs_nn : ∀ z, 0 ≤ f_s z := fun z => by
      dsimp only [f_s]; split_ifs with hz
      · exact le_of_lt hz.2.1
      · exact le_rfl
    have hfs_le1 : ∀ z, f_s z ≤ 1 := fun z => by
      dsimp only [f_s]; split_ifs with hz
      · exact hz.2.2
      · exact zero_le_one
    have hfs_int : Integrable f_s m := by
      rw [integrable_prod_iff hfs_meas.aestronglyMeasurable]
      have hslice : Integrable (fun x : ℝ => if x ∈ Set.Ioc (0 : ℝ) 1 then x else 0) ν := by
        rw [integrable_withDensity_iff_integrable_smul hρ_meas]
        have hcongr : (fun x : ℝ => ρ x • (if x ∈ Set.Ioc (0 : ℝ) 1 then x else 0)) =
            (Set.Ioc (0 : ℝ) 1).indicator (fun x => c * x ^ (-δ)) := by
          funext x
          by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
          · rw [Set.indicator_of_mem hx, if_pos hx, NNReal.smul_def, smul_eq_mul, hρ_pos hx.1]
            have hrp : x ^ (-1 - δ) * x = x ^ (-δ) := by
              calc x ^ (-1 - δ) * x = x ^ (-1 - δ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
                _ = x ^ ((-1 - δ) + 1) := (Real.rpow_add hx.1 _ _).symm
                _ = x ^ (-δ) := by congr 1; ring
            calc c * x ^ (-1 - δ) * x = c * (x ^ (-1 - δ) * x) := by ring
              _ = c * x ^ (-δ) := by rw [hrp]
          · simp [hx]
        rw [hcongr, integrable_indicator_iff measurableSet_Ioc]
        exact (integrableOn_rpow_Ioc hδ1).const_mul c
      refine ⟨Eventually.of_forall fun s => ?_, ?_⟩
      · by_cases hs : s ∈ Set.Ioc (0 : ℝ) (T : ℝ)
        · exact hslice.congr (Eventually.of_forall fun x => by
            simp only [f_s, A_small, Set.mem_prod, hs, true_and])
        · exact (integrable_zero _ _ _).congr (Eventually.of_forall fun x => by
            simp only [f_s, A_small, Set.mem_prod, hs, false_and, ↓reduceIte, Pi.zero_apply])
      · have hnorm_eq : (fun s : ℝ => ∫ x, ‖f_s (s, x)‖ ∂ν) =
            (Set.Ioc (0 : ℝ) (T : ℝ)).indicator (fun _ => ∫ x, ‖if x ∈ Set.Ioc (0 : ℝ) 1 then x else 0‖ ∂ν) := by
          funext s
          by_cases hs : s ∈ Set.Ioc (0 : ℝ) (T : ℝ)
          · rw [Set.indicator_of_mem hs]
            congr 1; funext x; simp only [f_s, A_small, Set.mem_prod, hs, true_and]
          · rw [Set.indicator_of_notMem hs]
            simp only [f_s, A_small, Set.mem_prod, hs, false_and, ↓reduceIte, norm_zero, integral_zero]
        rw [hnorm_eq, integrable_indicator_iff measurableSet_Ioc]
        refine integrableOn_const ?_
        have hle : volume.restrict (Set.Ioi (0 : ℝ)) (Set.Ioc 0 (T : ℝ)) ≤ volume (Set.Ioc 0 (T : ℝ)) :=
          Measure.restrict_apply_le _ _
        exact (lt_of_le_of_lt hle (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)).ne
    have hfs2_int : Integrable (fun z => f_s z ^ 2) m := by
      refine hfs_int.mono' (hfs_meas.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [hfs_nn z, hfs_le1 z]
    have hsmall_fin : ∀ᵐ ω ∂P,
        (∑' k : ℕ, ENNReal.ofReal (pieceSum K X f_s k ω)) < ⊤ := by
      have hlt : (∫⁻ ω, ∑' k : ℕ, ENNReal.ofReal (pieceSum K X f_s k ω) ∂P) < ⊤ := by
        rw [lintegral_tsum (f := fun k ω => ENNReal.ofReal (pieceSum K X f_s k ω)) fun k =>
          (ENNReal.measurable_ofReal.comp (measurable_pieceSum (hd.measurable_count k)
            (hd.measurable_point k) hfs_meas)).aemeasurable]
        have hpiece : ∀ k, ∫⁻ ω, ENNReal.ofReal (pieceSum K X f_s k ω) ∂P =
            ENNReal.ofReal (∫ z in prmPiece m k, f_s z ∂m) := by
          intro k
          have hps_nn : ∀ ω, 0 ≤ pieceSum K X f_s k ω := fun ω =>
            Finset.sum_nonneg fun n _ => hfs_nn _
          have hps_sq_int := integrable_sq_pieceSum hd hfs_meas hfs_int.integrableOn hfs2_int.integrableOn (k := k)
          have hps_int : Integrable (pieceSum K X f_s k) P := by
            refine ((integrable_const (1 : ℝ)).add hps_sq_int).mono'
              (measurable_pieceSum (hd.measurable_count k) (hd.measurable_point k) hfs_meas).aestronglyMeasurable
              (Eventually.of_forall fun ω => ?_)
            rw [Real.norm_eq_abs, abs_of_nonneg (hps_nn ω)]
            simp only [Pi.add_apply]
            nlinarith [sq_nonneg (pieceSum K X f_s k ω - 1)]
          rw [← ofReal_integral_eq_lintegral_ofReal hps_int (Eventually.of_forall hps_nn),
            integral_pieceSum hd hfs_meas hfs_int.integrableOn]
        simp_rw [hpiece]
        have hsum_int : HasSum (fun k => ∫ z in prmPiece m k, f_s z ∂m) (∫ z, f_s z ∂m) := by
          have h1 := hasSum_integral_iUnion (f := f_s) (μ := m)
            (fun k => measurableSet_prmPiece (m := m)) (pairwise_disjoint_prmPiece (m := m))
            (by rw [iUnion_prmPiece (m := m)]; exact hfs_int.integrableOn)
          rwa [iUnion_prmPiece (m := m), setIntegral_univ] at h1
        rw [← ENNReal.ofReal_tsum_of_nonneg
          (fun k => setIntegral_nonneg measurableSet_prmPiece fun z _ => hfs_nn z)
          hsum_int.summable, hsum_int.tsum_eq]
        exact ENNReal.ofReal_lt_top
      exact ae_lt_top (Measurable.tsum fun k =>
        ENNReal.measurable_ofReal.comp (measurable_pieceSum (hd.measurable_count k)
          (hd.measurable_point k) hfs_meas)) hlt.ne
    -- Big jumps: finite count by ae_poissonRandomMeasure_apply_lt_top
    have hm_big_lt_top : m A_big < ⊤ := by
      rw [Measure.prod_prod]
      refine ENNReal.mul_lt_top ?_ ?_
      · exact lt_of_le_of_lt (Measure.restrict_apply_le _ _) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
      · rw [MeasureTheory.withDensity_apply _ measurableSet_Ioi]
        have hcongr : ∫⁻ x in Set.Ioi (1 : ℝ), (ρ x : ℝ≥0∞) =
            ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal (c * x ^ (-1 - δ)) := by
          refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
          rw [← ENNReal.ofReal_coe_nnreal, hρ_pos (lt_trans zero_lt_one hx)]
        rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal ((integrableOn_rpow_Ioi hδ0).const_mul c)]
        · exact ENNReal.ofReal_lt_top
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          exact mul_nonneg (le_of_lt hc_pos) (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hx)) _)
    have hbig_fin := ae_poissonRandomMeasure_apply_lt_top hd hAb_meas hm_big_lt_top
    filter_upwards [hsmall_fin, hbig_fin] with ω hsm hbg
    rw [poissonRandomMeasure_apply hAb_meas] at hbg
    have hbig_sum_lt : (∑' k : ℕ, ∑ n ∈ Finset.range (K k ω),
        if X k n ω ∈ A_big then ENNReal.ofReal (X k n ω).2 else 0) < ⊤ := by
      classical
      have hfin_supp : {k : ℕ | thinnedCount K X A_big k ω ≠ 0}.Finite := by
        by_contra hinf
        have hinf' : {k : ℕ | thinnedCount K X A_big k ω ≠ 0}.Infinite := hinf
        have hge : ∀ M : ℕ, (M : ℝ≥0∞) ≤ ∑' k, (thinnedCount K X A_big k ω : ℝ≥0∞) := by
          intro M
          obtain ⟨S, hSsub, hScard⟩ := hinf'.exists_subset_card_eq M
          calc (M : ℝ≥0∞) = ∑ _k ∈ S, (1 : ℝ≥0∞) := by simp [hScard]
            _ ≤ ∑ k ∈ S, (thinnedCount K X A_big k ω : ℝ≥0∞) := by
                refine Finset.sum_le_sum fun k hk => ?_
                have hne : thinnedCount K X A_big k ω ≠ 0 := hSsub hk
                exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
            _ ≤ ∑' k, (thinnedCount K X A_big k ω : ℝ≥0∞) := ENNReal.sum_le_tsum S
        have htop : (∑' k, (thinnedCount K X A_big k ω : ℝ≥0∞)) = ⊤ :=
          eq_top_iff.mpr (le_of_forall_lt fun c hc => by
            obtain ⟨M, hM⟩ := ENNReal.exists_nat_gt hc.ne
            exact lt_of_lt_of_le hM (hge M))
        exact hbg.ne htop
      rw [tsum_eq_sum (s := hfin_supp.toFinset)]
      · exact ENNReal.sum_lt_top.mpr fun k _ =>
          ENNReal.sum_lt_top.mpr fun n _ => by split_ifs <;> simp
      · intro k hk
        simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hk
        refine Finset.sum_eq_zero fun n hn => ?_
        have hnot : X k n ω ∉ A_big := by
          intro hmem
          have hpos : 0 < thinnedCount K X A_big k ω := by
            unfold thinnedCount
            exact Finset.card_pos.mpr ⟨n, by simp [hn, hmem]⟩
          omega
        simp [hnot]
    have hsplit_le : tilde_τ (T : ℝ≥0) ω ≤
        (∑' k : ℕ, ENNReal.ofReal (pieceSum K X f_s k ω)) +
        (∑' k : ℕ, ∑ n ∈ Finset.range (K k ω),
          if X k n ω ∈ A_big then ENNReal.ofReal (X k n ω).2 else 0) := by
      have hTcoe : ((T : ℝ≥0) : ℝ) = (T : ℝ) := rfl
      dsimp only [tilde_τ]
      simp only [hTcoe]
      rw [← ENNReal.tsum_add]
      refine ENNReal.tsum_le_tsum fun k => ?_
      rw [pieceSum, ENNReal.ofReal_sum_of_nonneg (fun n _ => hfs_nn _), ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun n _ => ?_
      by_cases h1 : X k n ω ∈ (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ Set.Ioi (0 : ℝ))
      · rw [if_pos h1]
        by_cases hle1 : (X k n ω).2 ≤ 1
        · have hms : X k n ω ∈ A_small := ⟨h1.1, h1.2, hle1⟩
          have hmb : X k n ω ∉ A_big := fun h => not_lt_of_ge hle1 h.2
          simp [f_s, hms, hmb]
        · have hms : X k n ω ∉ A_small := fun h => hle1 h.2.2
          have hmb : X k n ω ∈ A_big := ⟨h1.1, lt_of_not_ge hle1⟩
          simp [f_s, hms, hmb]
      · rw [if_neg h1]; exact bot_le
    exact lt_of_le_of_lt hsplit_le (ENNReal.add_lt_top.mpr ⟨hsm, hbig_sum_lt⟩)
  have hfin_all : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, tilde_τ t ω < ⊤ := by
    filter_upwards [ae_all_iff.mpr hfin_T] with ω hT t
    obtain ⟨N, hN⟩ := exists_nat_ge (t : ℝ)
    have hmono : tilde_τ t ω ≤ tilde_τ (N : ℝ≥0) ω := by
      refine ENNReal.tsum_le_tsum fun k => Finset.sum_le_sum fun n _ => ?_
      split_ifs with h1 h2
      · exact le_rfl
      · exfalso; exact h2 ⟨⟨h1.1.1, le_trans h1.1.2 (by exact_mod_cast hN)⟩, h1.2⟩
      · exact bot_le
      · exact le_rfl
    exact lt_of_le_of_lt hmono (hT N)
  have hτ0 : ∀ ω, τ 0 ω = 0 := fun ω => by
    have : tilde_τ 0 ω = 0 := by
      simp only [tilde_τ, NNReal.coe_zero, Set.Ioc_self, Set.empty_prod,
        Set.mem_empty_iff_false, ↓reduceIte, Finset.sum_const_zero, tsum_zero]
    simp [τ, this]
  have hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω) := by
    filter_upwards [hfin_all] with ω hfin s t hst
    have hle : tilde_τ s ω ≤ tilde_τ t ω := by
      refine ENNReal.tsum_le_tsum fun k => Finset.sum_le_sum fun n _ => ?_
      split_ifs with h1 h2
      · exact le_rfl
      · exfalso; exact h2 ⟨⟨h1.1.1, le_trans h1.1.2 (NNReal.coe_le_coe.mpr hst)⟩, h1.2⟩
      · exact bot_le
      · exact le_rfl
    exact (ENNReal.toNNReal_le_toNNReal (hfin s).ne (hfin t).ne).mpr hle
  -- Step 2: Càdlàg paths on the full-measure finiteness event
  have hcad : ∀ᵐ ω ∂P, IsCadlag (fun t => (τ t ω : ℝ)) := by
    filter_upwards [hfin_all] with ω hfin
    exact prm_subordinator_cadlag (fun k => K k ω) (fun k n => X k n ω) hfin
  -- Step 3: Joint exponential identity for increments via prm_exp_integral
  have hjoint_exp : ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (_ : Monotone t)
      (z : Fin n → ℂ) (_ : ∀ j, (z j).re ≤ 0),
      ∫ ω, Complex.exp (∑ j : Fin n,
          (((τ (t j.succ) ω : ℝ) - (τ (t j.castSucc) ω : ℝ)) : ℂ) * z j) ∂P =
        ∏ j : Fin n, Complex.exp (((t j.succ : ℝ) - (t j.castSucc : ℝ)) *
          ∫ x in Set.Ioi (0 : ℝ), (Complex.exp ((x : ℂ) * z j) - 1) * ((c * x ^ (-1 - δ) : ℝ) : ℂ)) := by
    intro n t ht z hz
    let g : ℝ × ℝ → ℂ := fun p =>
      ∑ j : Fin n,
        if p ∈ (Set.Ioc (t j.castSucc : ℝ) (t j.succ : ℝ) ×ˢ Set.Ioi (0 : ℝ)) then (p.2 : ℂ) * z j else 0
    have hdisj_Ioc : ∀ (p : ℝ × ℝ) (j₁ j₂ : Fin n),
        p ∈ (Set.Ioc (t j₁.castSucc : ℝ) (t j₁.succ : ℝ) ×ˢ Set.Ioi (0 : ℝ)) →
        p ∈ (Set.Ioc (t j₂.castSucc : ℝ) (t j₂.succ : ℝ) ×ˢ Set.Ioi (0 : ℝ)) → j₁ = j₂ := by
      intro p j₁ j₂ h1 h2
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : t j₁.succ ≤ t j₂.castSucc := ht (Fin.succ_le_castSucc_iff.mpr hlt)
        linarith [h1.1.2, h2.1.1, NNReal.coe_le_coe.mpr hle]
      · have hle : t j₂.succ ≤ t j₁.castSucc := ht (Fin.succ_le_castSucc_iff.mpr hgt)
        linarith [h2.1.2, h1.1.1, NNReal.coe_le_coe.mpr hle]
    have hg_meas : Measurable g :=
      Finset.measurable_sum Finset.univ fun j _ =>
        Measurable.ite (measurableSet_Ioc.prod measurableSet_Ioi)
          ((Complex.continuous_ofReal.measurable.comp measurable_snd).mul measurable_const)
          measurable_const
    have hg_re : ∀ p, (g p).re ≤ 0 := fun p => by
      dsimp only [g]; rw [Complex.re_sum]
      refine Finset.sum_nonpos fun j _ => ?_
      split_ifs with hp
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hp.2) (hz j)
      · simp
    have hexp_g_eq : ∀ p : ℝ × ℝ, Complex.exp (g p) - 1 =
        ∑ j : Fin n,
          (Set.Ioc (t j.castSucc : ℝ) (t j.succ : ℝ) ×ˢ Set.Ioi (0 : ℝ)).indicator
            (fun q => Complex.exp ((q.2 : ℂ) * z j) - 1) p := by
      intro p
      by_cases hex : ∃ j₀ : Fin n, p ∈ (Set.Ioc (t j₀.castSucc : ℝ) (t j₀.succ : ℝ) ×ˢ Set.Ioi (0 : ℝ))
      · obtain ⟨j₀, hj₀⟩ := hex
        have hgp : g p = (p.2 : ℂ) * z j₀ := by
          dsimp only [g]
          rw [Finset.sum_eq_single j₀]
          · exact if_pos hj₀
          · intro j _ hne; exact if_neg fun h => hne (hdisj_Ioc p j j₀ h hj₀)
          · intro h; exact absurd (Finset.mem_univ j₀) h
        rw [hgp, Finset.sum_eq_single j₀]
        · rw [Set.indicator_of_mem hj₀]
        · intro j _ hne; exact Set.indicator_of_notMem (fun h => hne (hdisj_Ioc p j j₀ h hj₀)) _
        · intro h; exact absurd (Finset.mem_univ j₀) h
      · push Not at hex
        have hgp : g p = 0 := Finset.sum_eq_zero fun j _ => if_neg (hex j)
        rw [hgp, Complex.exp_zero, sub_self]
        exact (Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem (hex j) _).symm
    have hterm_int : ∀ j : Fin n,
        Integrable ((Set.Ioc (t j.castSucc : ℝ) (t j.succ : ℝ) ×ˢ Set.Ioi (0 : ℝ)).indicator
          (fun q : ℝ × ℝ => Complex.exp ((q.2 : ℂ) * z j) - 1)) m ∧
        (∫ p, (Set.Ioc (t j.castSucc : ℝ) (t j.succ : ℝ) ×ˢ Set.Ioi (0 : ℝ)).indicator
            (fun q : ℝ × ℝ => Complex.exp ((q.2 : ℂ) * z j) - 1) p ∂m) =
          (((t j.succ : ℝ) - (t j.castSucc : ℝ)) : ℂ) *
            ∫ x in Set.Ioi (0 : ℝ), (Complex.exp ((x : ℂ) * z j) - 1) * ((c * x ^ (-1 - δ) : ℝ) : ℂ) :=
      fun j => stable_prm_slice_integral hδ0 hδ1 hc_pos (ht j.castSucc_le_succ) (hz j)
    have hg_int : Integrable (fun p => Complex.exp (g p) - 1) m := by
      have : (fun p => Complex.exp (g p) - 1) =
          fun p => ∑ j : Fin n, (Set.Ioc (t j.castSucc : ℝ) (t j.succ : ℝ) ×ˢ Set.Ioi (0 : ℝ)).indicator
            (fun q => Complex.exp ((q.2 : ℂ) * z j) - 1) p := funext hexp_g_eq
      rw [this]
      exact integrable_finsetSum _ fun j _ => (hterm_int j).1
    -- Almost sure convergence of partial sums to ∑ j, (τ(t_{j+1}) - τ(t_j)) * z j
    have hS_tend : ∀ᵐ ω ∂P,
        Tendsto (fun M => ∑ k ∈ Finset.range M, ∑ m' ∈ Finset.range (K k ω), g (X k m' ω))
          atTop (nhds (∑ j : Fin n, (((τ (t j.succ) ω : ℝ) - (τ (t j.castSucc) ω : ℝ)) : ℂ) * z j)) := by
      filter_upwards [hfin_all] with ω hfin
      have hterm_tend : ∀ j : Fin n,
          Tendsto (fun M => ∑ k ∈ Finset.range M, ∑ m' ∈ Finset.range (K k ω),
              if X k m' ω ∈ (Set.Ioc (t j.castSucc : ℝ) (t j.succ : ℝ) ×ˢ Set.Ioi (0 : ℝ))
              then ((X k m' ω).2 : ℂ) * z j else 0)
            atTop (nhds ((((τ (t j.succ) ω : ℝ) - (τ (t j.castSucc) ω : ℝ)) : ℂ) * z j)) := by
        intro j
        let b : ℕ → ℝ := fun k => ∑ m' ∈ Finset.range (K k ω),
          if X k m' ω ∈ (Set.Ioc (t j.castSucc : ℝ) (t j.succ : ℝ) ×ˢ Set.Ioi (0 : ℝ)) then (X k m' ω).2 else 0
        have hb_nn : ∀ k, 0 ≤ b k := fun k =>
          Finset.sum_nonneg fun m' _ => by split_ifs with h; exact le_of_lt h.2; exact le_rfl
        have hadd_enn : tilde_τ (t j.succ) ω = tilde_τ (t j.castSucc) ω + ∑' k, ENNReal.ofReal (b k) := by
          dsimp only [tilde_τ]
          rw [← ENNReal.tsum_add]
          refine tsum_congr fun k => ?_
          rw [ENNReal.ofReal_sum_of_nonneg (fun m' _ => by split_ifs with h; exact le_of_lt h.2; exact le_rfl),
            ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun m' _ => ?_
          have hle : (t j.castSucc : ℝ) ≤ (t j.succ : ℝ) := NNReal.coe_le_coe.mpr (ht j.castSucc_le_succ)
          by_cases h1 : X k m' ω ∈ (Set.Ioc (0 : ℝ) (t j.succ : ℝ) ×ˢ Set.Ioi (0 : ℝ))
          · rw [if_pos h1]
            by_cases h2 : (X k m' ω).1 ≤ (t j.castSucc : ℝ)
            · have hm1 : X k m' ω ∈ (Set.Ioc (0 : ℝ) (t j.castSucc : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := ⟨⟨h1.1.1, h2⟩, h1.2⟩
              have hm2 : X k m' ω ∉ (Set.Ioc (t j.castSucc : ℝ) (t j.succ : ℝ) ×ˢ Set.Ioi (0 : ℝ)) :=
                fun h => not_lt_of_ge h2 h.1.1
              simp [hm1, hm2]
            · have hm1 : X k m' ω ∉ (Set.Ioc (0 : ℝ) (t j.castSucc : ℝ) ×ˢ Set.Ioi (0 : ℝ)) :=
                fun h => h2 h.1.2
              have hm2 : X k m' ω ∈ (Set.Ioc (t j.castSucc : ℝ) (t j.succ : ℝ) ×ˢ Set.Ioi (0 : ℝ)) :=
                ⟨⟨lt_of_not_ge h2, h1.1.2⟩, h1.2⟩
              simp [hm1, hm2]
          · have hm1 : X k m' ω ∉ (Set.Ioc (0 : ℝ) (t j.castSucc : ℝ) ×ˢ Set.Ioi (0 : ℝ)) :=
              fun h => h1 ⟨⟨h.1.1, le_trans h.1.2 hle⟩, h.2⟩
            have hm2 : X k m' ω ∉ (Set.Ioc (t j.castSucc : ℝ) (t j.succ : ℝ) ×ˢ Set.Ioi (0 : ℝ)) :=
              fun h => h1 ⟨⟨lt_of_le_of_lt (t j.castSucc).coe_nonneg h.1.1, h.1.2⟩, h.2⟩
            simp [h1, hm1, hm2]
        have hb_lt_top : (∑' k, ENNReal.ofReal (b k)) < ⊤ :=
          lt_of_le_of_lt (le_add_self.trans_eq hadd_enn.symm) (hfin (t j.succ))
        have hb_sum : Summable b :=
          (ENNReal.summable_toReal hb_lt_top.ne).congr fun k => ENNReal.toReal_ofReal (hb_nn k)
        have hb_tsum : (∑' k, b k) = (τ (t j.succ) ω : ℝ) - (τ (t j.castSucc) ω : ℝ) := by
          have h1 : (tilde_τ (t j.succ) ω).toReal =
              (tilde_τ (t j.castSucc) ω).toReal + (∑' k, ENNReal.ofReal (b k)).toReal := by
            rw [hadd_enn, ENNReal.toReal_add (hfin _).ne hb_lt_top.ne]
          have h2 : (∑' k, ENNReal.ofReal (b k)).toReal = ∑' k, b k := by
            rw [← ENNReal.ofReal_tsum_of_nonneg hb_nn hb_sum, ENNReal.toReal_ofReal (tsum_nonneg hb_nn)]
          rw [h2] at h1
          have hcoe : ∀ r : ℝ≥0, (τ r ω : ℝ) = (tilde_τ r ω).toReal := fun _ => rfl
          rw [hcoe, hcoe]; linarith
        have hrew : (fun M => ∑ k ∈ Finset.range M, ∑ m' ∈ Finset.range (K k ω),
              if X k m' ω ∈ (Set.Ioc (t j.castSucc : ℝ) (t j.succ : ℝ) ×ˢ Set.Ioi (0 : ℝ))
              then ((X k m' ω).2 : ℂ) * z j else 0) =
            fun M => ((∑ k ∈ Finset.range M, b k : ℝ) : ℂ) * z j := by
          funext M
          rw [Complex.ofReal_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          dsimp only [b]
          rw [Complex.ofReal_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun m' _ => by split_ifs <;> simp
        rw [hrew, ← Complex.ofReal_sub, ← hb_tsum]
        exact ((Complex.continuous_ofReal.tendsto _).comp hb_sum.hasSum.tendsto_sum_nat).mul tendsto_const_nhds
      have hswap : (fun M => ∑ k ∈ Finset.range M, ∑ m' ∈ Finset.range (K k ω), g (X k m' ω)) =
          fun M => ∑ j : Fin n, ∑ k ∈ Finset.range M, ∑ m' ∈ Finset.range (K k ω),
            if X k m' ω ∈ (Set.Ioc (t j.castSucc : ℝ) (t j.succ : ℝ) ×ˢ Set.Ioi (0 : ℝ))
            then ((X k m' ω).2 : ℂ) * z j else 0 := by
        funext M
        dsimp only [g]
        simp_rw [Finset.sum_comm (s := Finset.range (K _ ω)) (t := Finset.univ)]
        rw [Finset.sum_comm]
      rw [hswap]
      exact tendsto_finsetSum Finset.univ fun j _ => hterm_tend j
    rw [prm_exp_integral hd hg_meas hg_re hg_int hS_tend]
    have hint_eq : (∫ p, (Complex.exp (g p) - 1) ∂m) =
        ∑ j : Fin n, (((t j.succ : ℝ) - (t j.castSucc : ℝ)) : ℂ) *
          ∫ x in Set.Ioi (0 : ℝ), (Complex.exp ((x : ℂ) * z j) - 1) * ((c * x ^ (-1 - δ) : ℝ) : ℂ) := by
      have : (fun p => Complex.exp (g p) - 1) =
          fun p => ∑ j : Fin n, (Set.Ioc (t j.castSucc : ℝ) (t j.succ : ℝ) ×ˢ Set.Ioi (0 : ℝ)).indicator
            (fun q => Complex.exp ((q.2 : ℂ) * z j) - 1) p := funext hexp_g_eq
      rw [this, integral_finsetSum Finset.univ fun j _ => (hterm_int j).1]
      exact Finset.sum_congr rfl fun j _ => (hterm_int j).2
    rw [hint_eq, Complex.exp_sum]
  -- Step 4: Read off IsLevyProcess and exact Laplace transform!
  have hinc_cf : ∀ (s t : ℝ≥0), s ≤ t → ∀ ξ : ℝ,
      charFun (P.map (increment (fun r ω => (τ r ω : ℝ)) s t)) ξ =
        Complex.exp ((((t : ℝ) - (s : ℝ)) : ℂ) *
          ∫ x in Set.Ioi (0 : ℝ), (Complex.exp ((x : ℂ) * ((ξ : ℂ) * Complex.I)) - 1) *
            ((c * x ^ (-1 - δ) : ℝ) : ℂ)) := by
    intro s t hst ξ
    let tp : Fin 2 → ℝ≥0 := ![s, t]
    have htp : Monotone tp := fun a b hab => by
      fin_cases a <;> fin_cases b <;> simp [tp, hst] at hab ⊢
    have h1 := hjoint_exp 1 tp htp (fun _ => (ξ : ℂ) * Complex.I) (fun _ => by simp)
    have hinc_meas : Measurable (increment (fun r ω => (τ r ω : ℝ)) s t) :=
      (NNReal.continuous_coe.measurable.comp (hτ_meas t)).sub
        (NNReal.continuous_coe.measurable.comp (hτ_meas s))
    rw [charFun_apply_real, integral_map hinc_meas.aemeasurable (by fun_prop)]
    have hrew : (∫ ω, Complex.exp (↑ξ * ↑(increment (fun r ω => (τ r ω : ℝ)) s t ω) * Complex.I) ∂P) =
        ∫ ω, Complex.exp (∑ j : Fin 1, (((τ (tp j.succ) ω : ℝ) - (τ (tp j.castSucc) ω : ℝ)) : ℂ) *
          ((ξ : ℂ) * Complex.I)) ∂P := by
      congr 1; funext ω; simp only [Fin.sum_univ_one, tp, increment, Matrix.cons_val_zero,
        Matrix.cons_val_one, Fin.succ_zero_eq_one, Fin.castSucc_zero, Complex.ofReal_sub]
      congr 1; ring
    rw [hrew, h1]
    simp [tp]
  refine ⟨Ω, mΩ, P, hP, τ, ?_, hmon, ?_⟩
  · refine
      { start_zero := by funext ω; simp [hτ0 ω]
        indep_increments := ?_
        stationary_increments := ?_
        cadlag_ae := hcad }
    · intro n t ht
      refine iIndepFun_of_joint_charFun
        (fun k => ((NNReal.continuous_coe.measurable.comp (hτ_meas _)).sub
          (NNReal.continuous_coe.measurable.comp (hτ_meas _))).aemeasurable) fun u => ?_
      have h1 := hjoint_exp n t ht (fun j => (u j : ℂ) * Complex.I) (fun j => by simp)
      have hrew : (∫ ω, Complex.exp (↑(∑ k : Fin n, u k *
            increment (fun r ω => (τ r ω : ℝ)) (t k.castSucc) (t k.succ) ω) * Complex.I) ∂P) =
          ∫ ω, Complex.exp (∑ j : Fin n, (((τ (t j.succ) ω : ℝ) - (τ (t j.castSucc) ω : ℝ)) : ℂ) *
            ((u j : ℂ) * Complex.I)) ∂P := by
        congr 1; funext ω; congr 1
        simp only [Complex.ofReal_sum, Finset.sum_mul, increment]
        refine Finset.sum_congr rfl fun j _ => ?_
        push_cast; ring
      rw [hrew, h1]
      refine Finset.prod_congr rfl fun j _ => (hinc_cf _ _ (ht j.castSucc_le_succ) (u j)).symm
    · intro s h
      refine identDistrib_of_charFun_eq
        (((NNReal.continuous_coe.measurable.comp (hτ_meas _)).sub
          (NNReal.continuous_coe.measurable.comp (hτ_meas _))).aemeasurable)
        (((NNReal.continuous_coe.measurable.comp (hτ_meas _)).sub
          (NNReal.continuous_coe.measurable.comp (hτ_meas _))).aemeasurable) fun ξ => ?_
      rw [hinc_cf s (s + h) le_self_add ξ, hinc_cf 0 h bot_le ξ]
      simp [NNReal.coe_add]
  · -- Exact Laplace transform
    intro q hq t
    let tp : Fin 2 → ℝ≥0 := ![0, t]
    have htp : Monotone tp := fun a b hab => by
      fin_cases a <;> fin_cases b <;> simp [tp] at hab ⊢
    have h1 := hjoint_exp 1 tp htp (fun _ => -(q : ℂ)) (fun _ => by simpa using hq)
    have hLHS : (∫ ω, Complex.exp (∑ j : Fin 1, (((τ (tp j.succ) ω : ℝ) - (τ (tp j.castSucc) ω : ℝ)) : ℂ) *
          (-(q : ℂ))) ∂P) = ((∫ ω, Real.exp (-q * (τ t ω : ℝ)) ∂P : ℝ) : ℂ) := by
      have hrew : (fun ω => Complex.exp (∑ j : Fin 1, (((τ (tp j.succ) ω : ℝ) - (τ (tp j.castSucc) ω : ℝ)) : ℂ) *
            (-(q : ℂ)))) = fun ω => ((Real.exp (-q * (τ t ω : ℝ)) : ℝ) : ℂ) := by
        funext ω
        simp only [Fin.sum_univ_one, tp, Fin.succ_zero_eq_one, Fin.castSucc_zero,
          Matrix.cons_val_zero, Matrix.cons_val_one, hτ0 ω, NNReal.coe_zero, Complex.ofReal_zero,
          sub_zero, Complex.ofReal_exp]
        congr 1; push_cast; ring
      rw [hrew]
      exact integral_ofReal
    have hRHS_int : (∫ x in Set.Ioi (0 : ℝ), (Complex.exp ((x : ℂ) * (-(q : ℂ))) - 1) *
          ((c * x ^ (-1 - δ) : ℝ) : ℂ)) =
        ((-(c * (q ^ δ * stableConst δ)) : ℝ) : ℂ) := by
      have hrew : (fun x : ℝ => (Complex.exp ((x : ℂ) * (-(q : ℂ))) - 1) * ((c * x ^ (-1 - δ) : ℝ) : ℂ)) =
          fun x : ℝ => ((-c * ((1 - Real.exp (-q * x)) * x ^ (-1 - δ)) : ℝ) : ℂ) := by
        funext x
        have he : Complex.exp ((x : ℂ) * (-(q : ℂ))) = ((Real.exp (-q * x) : ℝ) : ℂ) := by
          rw [Complex.ofReal_exp]; congr 1; push_cast; ring
        rw [he]; push_cast; ring
      rw [hrew, show (∫ x in Set.Ioi (0 : ℝ), ((-c * ((1 - Real.exp (-q * x)) * x ^ (-1 - δ)) : ℝ) : ℂ)) =
          ((∫ x in Set.Ioi (0 : ℝ), (-c * ((1 - Real.exp (-q * x)) * x ^ (-1 - δ))) : ℝ) : ℂ) from integral_ofReal,
        integral_const_mul, stable_laplace_integral hδ0 hδ1 hq]
      push_cast; ring
    rw [hLHS] at h1
    simp only [Fin.prod_univ_one, tp, Fin.succ_zero_eq_one, Fin.castSucc_zero,
      Matrix.cons_val_zero, Matrix.cons_val_one, NNReal.coe_zero, Complex.ofReal_zero,
      sub_zero, hRHS_int] at h1
    have hcal : (((t : ℝ) : ℂ) * ((-(c * (q ^ δ * stableConst δ)) : ℝ) : ℂ)) =
        ((-(t : ℝ) * C * q ^ δ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      dsimp only [c]
      have hne : stableConst δ ≠ 0 := (stableConst_pos hδ0 hδ1).ne'
      field_simp [hne]
    rw [hcal, ← Complex.ofReal_exp] at h1
    exact Complex.ofReal_injective h1

private lemma exists_symmetric_stable (γ C₁ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ ≤ 2) (hC₁ : 0 < C₁) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Y : ℝ≥0 → Ω → ℝ),
      IsLevyProcess Y P ∧
      ∀ (t : ℝ≥0) (ξ : ℝ),
        charFun (P.map (Y t)) ξ = Complex.exp ((-(t : ℝ) * C₁ * |ξ| ^ γ : ℝ)) := by
  rcases eq_or_lt_of_le hγ2 with rfl | hγlt2
  · obtain ⟨Ω, mΩ, P, hP, ⟨B⟩⟩ := LevyStochCalc.Brownian.BrownianMotion.exists_readable
    let : MeasurableSpace Ω := mΩ
    let : IsProbabilityMeasure P := hP
    obtain ⟨hlevy, hchar⟩ := scaledBrownian_isLevyProcess P B (Real.sqrt (2 * C₁))
    refine ⟨Ω, mΩ, P, hP, fun t ω => Real.sqrt (2 * C₁) * (B.W (t : ℝ) ω - B.W 0 ω), hlevy, fun t ξ => ?_⟩
    rw [hchar t ξ]
    congr 1
    have hsq : (Real.sqrt (2 * C₁) * ξ) ^ 2 / 2 = C₁ * |ξ| ^ (2 : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.rpow_two, sq_abs]; ring
    rw [hsq]; push_cast; ring
  · obtain ⟨Ω₁, mΩ₁, P₁, hP₁, ⟨B⟩⟩ := LevyStochCalc.Brownian.BrownianMotion.exists_readable
    let : MeasurableSpace Ω₁ := mΩ₁
    let : IsProbabilityMeasure P₁ := hP₁
    obtain ⟨hB_levy, hB_char⟩ := scaledBrownian_isLevyProcess P₁ B 1
    obtain ⟨Ω₂, mΩ₂, P₂, hP₂, τ₂, hτ₂, hmon₂, hlap₂⟩ :=
      exists_stable_subordinator (γ / 2) (C₁ * (2 : ℝ) ^ (γ / 2))
        (by linarith) (by linarith) (by positivity)
    let : MeasurableSpace Ω₂ := mΩ₂
    let : IsProbabilityMeasure P₂ := hP₂
    let P' : Measure (Ω₁ × Ω₂) := P₁.prod P₂
    let X₁ : ℝ≥0 → Ω₁ → ℝ := fun t ω => 1 * (B.W (t : ℝ) ω - B.W 0 ω)
    let X' : ℝ≥0 → Ω₁ × Ω₂ → ℝ := fun t p => X₁ t p.1
    let τ' : ℝ≥0 → Ω₁ × Ω₂ → ℝ≥0 := fun t p => τ₂ t p.2
    have hmp1 := MeasureTheory.measurePreserving_fst (μ := P₁) (ν := P₂)
    have hmp2 := MeasureTheory.measurePreserving_snd (μ := P₁) (ν := P₂)
    have hX'_levy : IsLevyProcess X' P' := isLevyProcess_pullback hmp1 hB_levy
    have hτ'_levy : IsLevyProcess (fun t p => (τ' t p : ℝ)) P' := isLevyProcess_pullback hmp2 hτ₂
    have hmon' : ∀ᵐ p ∂P', Monotone (fun t => τ' t p) := hmp2.quasiMeasurePreserving.ae hmon₂
    have hX'_char : ∀ (t : ℝ≥0) (ξ : ℝ),
        charFun (P'.map (X' t)) ξ = Complex.exp (-((t : ℝ) : ℂ) * (((ξ ^ 2 / 2 : ℝ) : ℂ))) := by
      intro t ξ
      have hmap : P'.map (X' t) = P₁.map (X₁ t) := by
        rw [show X' t = X₁ t ∘ Prod.fst from rfl,
          ← AEMeasurable.map_map_of_aemeasurable
            (by rw [hmp1.map_eq]; exact aemeasurable_of_isLevyProcess hB_levy t)
            hmp1.measurable.aemeasurable,
          hmp1.map_eq]
      rw [hmap, hB_char t ξ]; simp
    have hind' : iIndepFun
        (fun (i : Fin 2) (p : Ω₁ × Ω₂) => fun t : ℝ≥0 => if i = 0 then X' t p else (τ' t p : ℝ)) P' := by
      have h := iIndepFun_fin2_of_indepFun
        (indepFun_prod_fst_snd (P₁ := P₁) (P₂ := P₂)
          (f := fun ω₁ t => X₁ t ω₁) (g := fun ω₂ t => (τ₂ t ω₂ : ℝ)))
      have heq : (fun (i : Fin 2) (p : Ω₁ × Ω₂) => if i = 0 then (fun t => X₁ t p.1) else (fun t => (τ₂ t p.2 : ℝ))) =
          fun (i : Fin 2) (p : Ω₁ × Ω₂) (t : ℝ≥0) => if i = 0 then X' t p else (τ' t p : ℝ) := by
        funext i p t; by_cases hi : i = 0 <;> simp [hi, X', τ']
      rwa [heq] at h
    obtain ⟨hY_levy, hY_char⟩ := subordinate_isLevyProcess P' X' (fun ξ => ((ξ ^ 2 / 2 : ℝ) : ℂ))
      hX'_levy hX'_char τ' hτ'_levy hmon' hind'
    refine ⟨Ω₁ × Ω₂, inferInstance, P', inferInstance, fun t p => X' (τ' t p) p, hY_levy, fun t ξ => ?_⟩
    rw [hY_char t ξ]
    have hrew : (fun p : Ω₁ × Ω₂ => Complex.exp (-((τ' t p : ℝ) : ℂ) * (((ξ ^ 2 / 2 : ℝ) : ℂ)))) =
        fun p : Ω₁ × Ω₂ => ((Real.exp (-(ξ ^ 2 / 2) * (τ₂ t p.2 : ℝ)) : ℝ) : ℂ) := by
      funext p; rw [Complex.ofReal_exp]; congr 1; dsimp only [τ']; push_cast; ring
    rw [hrew, show (∫ p : Ω₁ × Ω₂, ((Real.exp (-(ξ ^ 2 / 2) * (τ₂ t p.2 : ℝ)) : ℝ) : ℂ) ∂P') =
        ((∫ p : Ω₁ × Ω₂, Real.exp (-(ξ ^ 2 / 2) * (τ₂ t p.2 : ℝ)) ∂P' : ℝ) : ℂ) from integral_ofReal]
    have hsnd : ∫ p : Ω₁ × Ω₂, Real.exp (-(ξ ^ 2 / 2) * (τ₂ t p.2 : ℝ)) ∂P' =
        ∫ ω₂, Real.exp (-(ξ ^ 2 / 2) * (τ₂ t ω₂ : ℝ)) ∂P₂ := by
      have hae : AEStronglyMeasurable (fun ω₂ => Real.exp (-(ξ ^ 2 / 2) * (τ₂ t ω₂ : ℝ))) P₂ :=
        Real.continuous_exp.comp_aestronglyMeasurable
          (aestronglyMeasurable_const.mul (aemeasurable_of_isLevyProcess hτ₂ t).aestronglyMeasurable)
      rw [← hmp2.map_eq, integral_map hmp2.measurable.aemeasurable (by rw [hmp2.map_eq]; exact hae)]
    rw [hsnd, hlap₂ (ξ ^ 2 / 2) (by positivity) t, Complex.ofReal_exp]
    congr 1; congr 1
    have hpow : (2 : ℝ) ^ (γ / 2) * (ξ ^ 2 / 2) ^ (γ / 2) = |ξ| ^ γ := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      have hmul : (2 : ℝ) * (ξ ^ 2 / 2) = |ξ| ^ (2 : ℝ) := by rw [Real.rpow_two, sq_abs]; ring
      rw [hmul, ← Real.rpow_mul (abs_nonneg ξ)]
      congr 1; ring
    calc -(t : ℝ) * (C₁ * 2 ^ (γ / 2)) * (ξ ^ 2 / 2) ^ (γ / 2)
        = -(t : ℝ) * C₁ * (2 ^ (γ / 2) * (ξ ^ 2 / 2) ^ (γ / 2)) := by ring
      _ = -(t : ℝ) * C₁ * |ξ| ^ γ := by rw [hpow]

end Exercise212Helpers

theorem solution :
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
       [IsProbabilityMeasure P]
       (α C : ℝ) (hα : 0 < α) (hα2 : α < 2) (hC : 0 < C)
       (B : LevyStochCalc.Brownian.BrownianMotion P)
       (τ : ℝ≥0 → Ω → ℝ≥0)
       (hτ : ProbabilityTheory.IsLevyProcess
         (fun t ω => (τ t ω : ℝ)) P)
       (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
       (hlaplace : ∀ q : ℝ, 0 ≤ q → ∀ t : ℝ≥0,
         ∫ ω, Real.exp (-q * (τ t ω : ℝ)) ∂P =
         Real.exp (-(t : ℝ) * C * q ^ (α / 2)))
       (hind : ProbabilityTheory.iIndepFun
         (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
           if i = 0 then B.W (t : ℝ) ω else (τ t ω : ℝ)) P),
       ProbabilityTheory.IsLevyProcess
         (fun t ω => (B.W (τ t ω : ℝ) ω - B.W 0 ω)) P ∧
       ∀ (t : ℝ≥0) (ξ : ℝ),
         charFun (P.map (fun ω => (B.W (τ t ω : ℝ) ω - B.W 0 ω))) ξ =
         Complex.exp ((-(t : ℝ) * C * ((ξ ^ 2 / 2) ^ (α / 2)) : ℝ))) ∧
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
       [IsProbabilityMeasure P] (a : ℝ) (ha : 0 < a)
       (B : LevyStochCalc.Brownian.BrownianMotion P)
       (τ : ℝ≥0 → Ω → ℝ≥0)
       (hτ : ProbabilityTheory.IsLevyProcess
         (fun t ω => (τ t ω : ℝ)) P)
       (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
       (hlaplace : ∀ q : ℝ, 0 ≤ q → ∀ t : ℝ≥0,
         ∫ ω, Real.exp (-q * (τ t ω : ℝ)) ∂P =
         Real.exp (-(t : ℝ) * (2 / a) * (q / (q + a ^ 2))))
       (hind : ProbabilityTheory.iIndepFun
         (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
           if i = 0 then B.W (t : ℝ) ω else (τ t ω : ℝ)) P),
       ProbabilityTheory.IsLevyProcess
         (fun t ω => Real.sqrt 2 * (B.W (τ t ω : ℝ) ω - B.W 0 ω)) P ∧
       ∀ (t : ℝ≥0) (ξ : ℝ),
         charFun (P.map
           (fun ω => Real.sqrt 2 * (B.W (τ t ω : ℝ) ω - B.W 0 ω))) ξ =
         Complex.exp ((-(t : ℝ) * (2 / a) *
           (ξ ^ 2 / (ξ ^ 2 + a ^ 2)) : ℝ))) ∧
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
       [IsProbabilityMeasure P] (rate σ : ℝ)
       (hrate : 0 < rate) (hσ : 0 < σ)
       (B : LevyStochCalc.Brownian.BrownianMotion P)
       (N : ℝ≥0 → Ω → ℕ)
       (hNlaw : ∀ t : ℝ≥0,
         P.map (N t) =
         ProbabilityTheory.poissonMeasure (⟨2 * rate * (t : ℝ), by positivity⟩))
       (hNlevy : ProbabilityTheory.IsLevyProcess
         (fun t ω => (N t ω : ℝ)) P)
       (hind : ProbabilityTheory.iIndepFun
         (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
           if i = 0 then B.W (t : ℝ) ω else (N t ω : ℝ)) P),
       ProbabilityTheory.IsLevyProcess
         (fun t ω => σ * (B.W (N t ω : ℝ) ω - B.W 0 ω)) P ∧
       ∀ (t : ℝ≥0) (ξ : ℝ),
         charFun (P.map
           (fun ω => σ * (B.W (N t ω : ℝ) ω - B.W 0 ω))) ξ =
         Complex.exp ((-(t : ℝ) * 2 * rate *
           (1 - Real.exp (-(σ ^ 2 * ξ ^ 2) / 2)) : ℝ))) ∧
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
       [IsProbabilityMeasure P]
       (α β C : ℝ) (hα : 0 < α) (hα2 : α < 2)
       (hβ : 0 < β) (hβ1 : β < 1)
       (hadmissible : α / β ≤ 2) (hC : 0 < C)
       (X : ℝ≥0 → Ω → ℝ)
       (hX : ProbabilityTheory.IsLevyProcess X P)
       (hXstable : ∀ (t : ℝ≥0) (ξ : ℝ),
         charFun (P.map (X t)) ξ =
         Complex.exp ((-(t : ℝ) * C * |ξ| ^ α : ℝ))),
       ∃ (Ω' : Type) (measΩ' : MeasurableSpace Ω'),
         letI : MeasurableSpace Ω' := measΩ'
         ∃ (P' : Measure Ω') (probP' : IsProbabilityMeasure P'),
           letI : IsProbabilityMeasure P' := probP'
           ∃ (Y : ℝ≥0 → Ω' → ℝ) (τ : ℝ≥0 → Ω' → ℝ≥0),
             ProbabilityTheory.IsLevyProcess Y P' ∧
             ProbabilityTheory.IsLevyProcess
               (fun t ω => (τ t ω : ℝ)) P' ∧
             (∀ᵐ ω ∂P', Monotone (fun t => τ t ω)) ∧
             (∀ (t : ℝ≥0) (ξ : ℝ),
               charFun (P'.map (Y t)) ξ =
               Complex.exp ((-(t : ℝ) *
                 (C ^ (1 / β)) * |ξ| ^ (α / β) : ℝ))) ∧
             (∀ q : ℝ, 0 ≤ q → ∀ t : ℝ≥0,
               ∫ ω, Real.exp (-q * (τ t ω : ℝ)) ∂P' =
               Real.exp (-(t : ℝ) * q ^ β)) ∧
             ProbabilityTheory.iIndepFun
               (fun (i : Fin 2) (ω : Ω') => fun t : ℝ≥0 =>
                 if i = 0 then Y t ω else (τ t ω : ℝ)) P' ∧
             ProbabilityTheory.IsLevyProcess
               (fun t ω => Y (τ t ω) ω) P' ∧
             (∀ (t : ℝ≥0),
               P.map (X t) =
                 P'.map (fun ω => Y (τ t ω) ω))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Part (1): Brownian motion subordinated by an (α/2)-stable subordinator
    intro Ω _ P _ α C _ _ _ B τ hτ hmon hlaplace hind
    obtain ⟨hlevy, hcf⟩ := Exercise212Helpers.brownian_subordination P B 1 τ hτ hmon hind
    simp only [one_mul] at hlevy hcf
    refine ⟨hlevy, fun t ξ => ?_⟩
    rw [hcf t ξ]
    have hq : ∫ ω, Real.exp (-(ξ ^ 2 / 2) * (τ t ω : ℝ)) ∂P =
        Real.exp (-(t : ℝ) * C * (ξ ^ 2 / 2) ^ (α / 2)) :=
      hlaplace (ξ ^ 2 / 2) (by positivity) t
    rw [hq, Complex.ofReal_exp]
  · -- Part (2): √2 * B(τ) subordinated by compound-Poisson/inverse-Gaussian-type Laplace exponent
    intro Ω _ P _ a ha B τ hτ hmon hlaplace hind
    obtain ⟨hlevy, hcf⟩ := Exercise212Helpers.brownian_subordination P B (Real.sqrt 2) τ hτ hmon hind
    refine ⟨hlevy, fun t ξ => ?_⟩
    rw [hcf t ξ]
    have hsq : (Real.sqrt 2 * ξ) ^ 2 / 2 = ξ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]; ring
    rw [hsq, hlaplace (ξ ^ 2) (sq_nonneg ξ) t, Complex.ofReal_exp]
  · -- Part (3): σ * B(N) subordinated by a Poisson process of rate 2 * rate
    intro Ω _ P _ rate σ hrate hσ B N hNlaw hNlevy hind
    let τ : ℝ≥0 → Ω → ℝ≥0 := fun t ω => (N t ω : ℝ≥0)
    have hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω) :=
      Exercise212Helpers.poisson_monotone_ae P N hNlevy
    obtain ⟨hlevy, hcf⟩ := Exercise212Helpers.brownian_subordination P B σ τ hNlevy hmon hind
    refine ⟨hlevy, fun t ξ => ?_⟩
    change charFun (P.map (fun ω => σ * (B.W (τ t ω : ℝ) ω - B.W 0 ω))) ξ = _
    rw [hcf t ξ]
    have hlap := Exercise212Helpers.poisson_laplace_transform P (N t)
      ⟨2 * rate * (t : ℝ), by positivity⟩ (hNlaw t) ((σ * ξ) ^ 2 / 2) (by positivity)
    have hrew : (fun ω => Real.exp (-((σ * ξ) ^ 2 / 2) * (τ t ω : ℝ))) =
        fun ω => Real.exp (-((σ * ξ) ^ 2 / 2) * (N t ω : ℝ)) := rfl
    rw [hrew, hlap, Complex.ofReal_exp]
    congr 1; congr 1
    have h1 : -((σ * ξ) ^ 2 / 2) = -(σ ^ 2 * ξ ^ 2) / 2 := by ring
    rw [h1]; change -(2 * rate * (t : ℝ)) * _ = _; ring
  · -- Part (4): Factorization in marginal law of symmetric α-stable Lévy process
    intro Ω _ P _ α β C hα hα2 hβ hβ1 hadmissible hC X hX hXstable
    obtain ⟨Ω₁, mΩ₁, P₁, hP₁, Y₁, hY₁, hY₁_char⟩ :=
      Exercise212Helpers.exists_symmetric_stable (α / β) (C ^ (1 / β))
        (div_pos hα hβ) hadmissible (Real.rpow_pos_of_pos hC _)
    let : MeasurableSpace Ω₁ := mΩ₁
    let : IsProbabilityMeasure P₁ := hP₁
    obtain ⟨Ω₂, mΩ₂, P₂, hP₂, τ₂, hτ₂, hmon₂, hlap₂⟩ :=
      Exercise212Helpers.exists_stable_subordinator β 1 hβ hβ1 one_pos
    let : MeasurableSpace Ω₂ := mΩ₂
    let : IsProbabilityMeasure P₂ := hP₂
    let P' : Measure (Ω₁ × Ω₂) := P₁.prod P₂
    let Y : ℝ≥0 → Ω₁ × Ω₂ → ℝ := fun t p => Y₁ t p.1
    let τ : ℝ≥0 → Ω₁ × Ω₂ → ℝ≥0 := fun t p => τ₂ t p.2
    have hmp1 := MeasureTheory.measurePreserving_fst (μ := P₁) (ν := P₂)
    have hmp2 := MeasureTheory.measurePreserving_snd (μ := P₁) (ν := P₂)
    have hY_levy : IsLevyProcess Y P' := Exercise212Helpers.isLevyProcess_pullback hmp1 hY₁
    have hτ_levy : IsLevyProcess (fun t p => (τ t p : ℝ)) P' := Exercise212Helpers.isLevyProcess_pullback hmp2 hτ₂
    have hmon' : ∀ᵐ p ∂P', Monotone (fun t => τ t p) := hmp2.quasiMeasurePreserving.ae hmon₂
    have hY_char : ∀ (t : ℝ≥0) (ξ : ℝ),
        charFun (P'.map (Y t)) ξ = Complex.exp ((-(t : ℝ) * (C ^ (1 / β)) * |ξ| ^ (α / β) : ℝ)) := by
      intro t ξ
      have hmap : P'.map (Y t) = P₁.map (Y₁ t) := by
        rw [show Y t = Y₁ t ∘ Prod.fst from rfl,
          ← AEMeasurable.map_map_of_aemeasurable
            (by rw [hmp1.map_eq]; exact Exercise212Helpers.aemeasurable_of_isLevyProcess hY₁ t)
            hmp1.measurable.aemeasurable,
          hmp1.map_eq]
      rw [hmap, hY₁_char t ξ]
    have hlap' : ∀ q : ℝ, 0 ≤ q → ∀ t : ℝ≥0,
        ∫ p, Real.exp (-q * (τ t p : ℝ)) ∂P' = Real.exp (-(t : ℝ) * q ^ β) := by
      intro q hq t
      have hsnd : ∫ p : Ω₁ × Ω₂, Real.exp (-q * (τ₂ t p.2 : ℝ)) ∂P' =
          ∫ ω₂, Real.exp (-q * (τ₂ t ω₂ : ℝ)) ∂P₂ := by
        have hae : AEStronglyMeasurable (fun ω₂ => Real.exp (-q * (τ₂ t ω₂ : ℝ))) P₂ :=
          Real.continuous_exp.comp_aestronglyMeasurable
            (aestronglyMeasurable_const.mul
              (Exercise212Helpers.aemeasurable_of_isLevyProcess hτ₂ t).aestronglyMeasurable)
        rw [← hmp2.map_eq, integral_map hmp2.measurable.aemeasurable (by rw [hmp2.map_eq]; exact hae)]
      simpa only [τ, mul_one] using hsnd.trans (hlap₂ q hq t)
    have hind' : ProbabilityTheory.iIndepFun
        (fun (i : Fin 2) (p : Ω₁ × Ω₂) => fun t : ℝ≥0 => if i = 0 then Y t p else (τ t p : ℝ)) P' := by
      have h := Exercise212Helpers.iIndepFun_fin2_of_indepFun
        (Exercise212Helpers.indepFun_prod_fst_snd (P₁ := P₁) (P₂ := P₂)
          (f := fun ω₁ t => Y₁ t ω₁) (g := fun ω₂ t => (τ₂ t ω₂ : ℝ)))
      have heq : (fun (i : Fin 2) (p : Ω₁ × Ω₂) => if i = 0 then (fun t => Y₁ t p.1) else (fun t => (τ₂ t p.2 : ℝ))) =
          fun (i : Fin 2) (p : Ω₁ × Ω₂) (t : ℝ≥0) => if i = 0 then Y t p else (τ t p : ℝ) := by
        funext i p t; by_cases hi : i = 0 <;> simp [hi, Y, τ]
      rwa [heq] at h
    have hY_char_std : ∀ (t : ℝ≥0) (ξ : ℝ),
        charFun (P'.map (Y t)) ξ =
          Complex.exp (-((t : ℝ) : ℂ) * ((C ^ (1 / β) * |ξ| ^ (α / β) : ℝ) : ℂ)) := by
      intro t ξ; rw [hY_char t ξ]; congr 1; push_cast; ring
    obtain ⟨hsub_levy, hsub_char⟩ := Exercise212Helpers.subordinate_isLevyProcess P' Y
      (fun ξ => ((C ^ (1 / β) * |ξ| ^ (α / β) : ℝ) : ℂ)) hY_levy hY_char_std τ hτ_levy hmon' hind'
    refine ⟨Ω₁ × Ω₂, inferInstance, P', inferInstance, Y, τ,
      hY_levy, hτ_levy, hmon', hY_char, hlap', hind', hsub_levy, fun t => ?_⟩
    have hXae : AEMeasurable (X t) P := Exercise212Helpers.aemeasurable_of_isLevyProcess hX t
    have hZae : AEMeasurable (fun p => Y (τ t p) p) P' :=
      Exercise212Helpers.aemeasurable_of_isLevyProcess hsub_levy t
    have : IsProbabilityMeasure (P.map (X t)) := Measure.isProbabilityMeasure_map hXae
    have : IsProbabilityMeasure (P'.map (fun p => Y (τ t p) p)) := Measure.isProbabilityMeasure_map hZae
    refine Measure.ext_of_charFun (funext fun ξ => ?_)
    rw [hXstable t ξ, hsub_char t ξ]
    have hrew : (fun p : Ω₁ × Ω₂ => Complex.exp (-((τ t p : ℝ) : ℂ) * ((C ^ (1 / β) * |ξ| ^ (α / β) : ℝ) : ℂ))) =
        fun p : Ω₁ × Ω₂ => ((Real.exp (-(C ^ (1 / β) * |ξ| ^ (α / β)) * (τ t p : ℝ)) : ℝ) : ℂ) := by
      funext p; rw [Complex.ofReal_exp]; congr 1; push_cast; ring
    rw [hrew, show (∫ p : Ω₁ × Ω₂, ((Real.exp (-(C ^ (1 / β) * |ξ| ^ (α / β)) * (τ t p : ℝ)) : ℝ) : ℂ) ∂P') =
        ((∫ p : Ω₁ × Ω₂, Real.exp (-(C ^ (1 / β) * |ξ| ^ (α / β)) * (τ t p : ℝ)) ∂P' : ℝ) : ℂ) from integral_ofReal,
      hlap' (C ^ (1 / β) * |ξ| ^ (α / β)) (by positivity) t, Complex.ofReal_exp]
    congr 1; congr 1
    have hpow : (C ^ (1 / β) * |ξ| ^ (α / β)) ^ β = C * |ξ| ^ α := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul (le_of_lt hC), ← Real.rpow_mul (abs_nonneg ξ),
        one_div_mul_cancel hβ.ne', Real.rpow_one, div_mul_cancel₀ α hβ.ne']
    rw [hpow]; ring
