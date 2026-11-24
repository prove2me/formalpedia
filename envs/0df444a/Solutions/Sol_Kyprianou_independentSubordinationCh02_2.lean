-- Prove2me | solution 2 for Kyprianou.independentSubordinationCh02
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T00:09:50.035843+00:00
-- url     : https://prove2.me/submissions/29d95011-a097-4f40-99f6-04aa05794ab5

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Filter Complex Topology
open scoped NNReal ENNReal
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace IndependentSubordinationHelpers

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

end IndependentSubordinationHelpers

open IndependentSubordinationHelpers

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0 → Ω → ℝ≥0)
    (Ψ : ℝ → ℂ) (Ξ : ℂ → ℂ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hτ : ProbabilityTheory.IsLevyProcess
       (fun t ω => (τ t ω : ℝ)) P)
    (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
    (hind : ProbabilityTheory.iIndepFun
       (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
         if i = 0 then X t ω else (τ t ω : ℝ)) P)
    (hψ : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp (-(((t : ℝ) : ℂ)) * Ψ ξ))
    (hξ : ∀ (t : ℝ≥0) (z : ℂ), 0 ≤ z.re →
      ∫ ω, Complex.exp (-z * (((τ t ω : ℝ) : ℂ))) ∂P =
        Complex.exp (-(((t : ℝ) : ℂ)) * Ξ z)) :
    ProbabilityTheory.IsLevyProcess
      (fun t ω => X (τ t ω) ω) P ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => X (τ t ω) ω)) ξ =
      Complex.exp (-(((t : ℝ) : ℂ)) * Ξ (Ψ ξ)) := by
  -- Core Lévy property + mixture formula from the Ex 2.12 subordination kernel.
  obtain ⟨hlevy, hmix⟩ := subordinate_isLevyProcess P X Ψ hX hψ τ hτ hmon hind
  refine ⟨hlevy, fun t ξ => ?_⟩
  -- Compose mixture with the given complex Laplace transform of τ at z = Ψ ξ.
  have hre : 0 ≤ (Ψ ξ).re := psi_re_nonneg hX hψ ξ
  rw [hmix t ξ]
  -- Align `-((τ t ω : ℝ) : ℂ) * Ψ ξ` with `-Ψ ξ * ((τ t ω : ℝ) : ℂ)`.
  have hrew : (fun ω => Complex.exp (-((τ t ω : ℝ) : ℂ) * Ψ ξ)) =
      (fun ω => Complex.exp (-(Ψ ξ) * (((τ t ω : ℝ) : ℂ)))) := by
    funext ω; congr 1; ring
  rw [hrew]
  exact hξ t (Ψ ξ) hre
