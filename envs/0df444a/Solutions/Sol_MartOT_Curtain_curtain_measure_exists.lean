-- Prove2me | solution 1 for MartOT.Curtain.curtain_measure_exists
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T18:55:26.084118+00:00
-- url     : https://prove2.me/submissions/f93f0945-4a33-4570-bb0f-e1229486ff26

import Mathlib
import Definitions.Def_MartOT_Var_Setting

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

private lemma iSup_tsum_of_monotone {f : ℕ → ℕ → ℝ≥0∞} (hf : ∀ i, Monotone (fun n => f n i)) :
    ⨆ n : ℕ, ∑' i : ℕ, f n i = ∑' i : ℕ, ⨆ n : ℕ, f n i := by
  simp_rw [← lintegral_count]
  exact (lintegral_iSup (fun n => measurable_of_countable _) (fun _ _ hmn i => hf i hmn)).symm

private noncomputable def supMeasure (S : ℝ → Measure ℝ)
    (hmono : ∀ x x', x ≤ x' → S x ≤ S x') : Measure ℝ :=
  Measure.ofMeasurable (fun A _ => ⨆ n : ℕ, S (n : ℝ) A)
    (by simp)
    (fun f hf hd => by
      simp_rw [measure_iUnion hd hf]
      exact iSup_tsum_of_monotone fun i m n hmn => hmono _ _ (Nat.cast_le.mpr hmn) (f i))

private lemma supMeasure_apply (S : ℝ → Measure ℝ)
    (hmono : ∀ x x', x ≤ x' → S x ≤ S x') {A : Set ℝ} (hA : MeasurableSet A) :
    supMeasure S hmono A = ⨆ n : ℕ, S (n : ℝ) A :=
  Measure.ofMeasurable_apply A hA

private lemma le_supMeasure (S : ℝ → Measure ℝ)
    (hmono : ∀ x x', x ≤ x' → S x ≤ S x') (x : ℝ) :
    S x ≤ supMeasure S hmono := by
  refine Measure.le_iff.mpr fun A hA => ?_
  rw [supMeasure_apply S hmono hA]
  obtain ⟨n, hn⟩ := exists_nat_ge x
  exact (hmono x (n : ℝ) hn A).trans (le_iSup (fun m : ℕ => S (m : ℝ) A) n)

private lemma supMeasure_univ (μ : Measure ℝ) (S : ℝ → Measure ℝ)
    (hmono : ∀ x x', x ≤ x' → S x ≤ S x') (hmass : ∀ x, S x Set.univ = μ (Set.Iic x)) :
    supMeasure S hmono Set.univ = μ Set.univ := by
  rw [supMeasure_apply S hmono MeasurableSet.univ]
  simp_rw [hmass]
  have hm : Monotone (fun n : ℕ => Set.Iic (n : ℝ)) :=
    fun _ _ hmn => Set.Iic_subset_Iic.mpr (Nat.cast_le.mpr hmn)
  rw [← hm.measure_iUnion]
  congr 1
  ext r
  simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
  exact exists_nat_ge r

private lemma S_le_add_Ioc (μ : Measure ℝ) (S : ℝ → Measure ℝ)
    (hfin : ∀ x, IsFiniteMeasure (S x)) (hmono : ∀ x x', x ≤ x' → S x ≤ S x')
    (hmass : ∀ x, S x Set.univ = μ (Set.Iic x))
    {x x' : ℝ} (hxx' : x ≤ x') {B : Set ℝ} (hB : MeasurableSet B) :
    S x' B ≤ S x B + μ (Set.Ioc x x') := by
  have := hfin x
  have h1 : S x B + S x Bᶜ = μ (Set.Iic x) := by
    rw [measure_add_measure_compl hB, hmass x]
  have h2 : S x' B + S x' Bᶜ = μ (Set.Iic x') := by
    rw [measure_add_measure_compl hB, hmass x']
  have h3 : μ (Set.Iic x') = μ (Set.Iic x) + μ (Set.Ioc x x') := by
    rw [← measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Set.Iic_union_Ioc_eq_Iic hxx']
  have h4 : S x' B + S x Bᶜ ≤ S x B + μ (Set.Ioc x x') + S x Bᶜ := by
    calc S x' B + S x Bᶜ
        ≤ S x' B + S x' Bᶜ := add_le_add_right (hmono x x' hxx' Bᶜ) _
      _ = μ (Set.Iic x) + μ (Set.Ioc x x') := by rw [h2, h3]
      _ = S x B + S x Bᶜ + μ (Set.Ioc x x') := by rw [← h1]
      _ = S x B + μ (Set.Ioc x x') + S x Bᶜ := by ac_rfl
  exact (ENNReal.add_le_add_iff_right (measure_ne_top (S x) Bᶜ)).mp h4

private lemma exists_rat_antitone_tendsto (x : ℝ) :
    ∃ q : ℕ → ℚ, Antitone q ∧ (∀ n, x < (q n : ℝ)) ∧
      Tendsto (fun n => (q n : ℝ)) atTop (𝓝 x) := by
  let q : ℕ → ℚ := fun n => (((⌊x * (2 : ℝ) ^ n⌋ + 1 : ℤ) : ℚ) / (2 : ℚ) ^ n)
  have hq_cast : ∀ n : ℕ, (q n : ℝ) = ((⌊x * (2 : ℝ) ^ n⌋ : ℝ) + 1) / (2 : ℝ) ^ n := by
    intro n
    simp [q]
  have hgt : ∀ n, x < (q n : ℝ) := by
    intro n
    rw [hq_cast, lt_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)]
    exact Int.lt_floor_add_one (x * (2 : ℝ) ^ n)
  have hle : ∀ n, (q n : ℝ) ≤ x + (1 / 2 : ℝ) ^ n := by
    intro n
    rw [hq_cast, one_div, inv_pow, div_eq_mul_inv]
    have hfl : (⌊x * (2 : ℝ) ^ n⌋ : ℝ) ≤ x * (2 : ℝ) ^ n := Int.floor_le _
    have hpos : (0 : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹ := by positivity
    calc ((⌊x * (2 : ℝ) ^ n⌋ : ℝ) + 1) * ((2 : ℝ) ^ n)⁻¹
        ≤ (x * (2 : ℝ) ^ n + 1) * ((2 : ℝ) ^ n)⁻¹ := by gcongr
      _ = x + ((2 : ℝ) ^ n)⁻¹ := by
          rw [add_mul, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one, one_mul]
  have hanti : Antitone q := by
    refine antitone_nat_of_succ_le fun n => ?_
    dsimp only [q]
    have hlt : x * (2 : ℝ) ^ (n + 1) < ((2 * ⌊x * (2 : ℝ) ^ n⌋ + 2 : ℤ) : ℝ) := by
      have h1 : x * (2 : ℝ) ^ n < (⌊x * (2 : ℝ) ^ n⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      push_cast
      rw [pow_succ]
      linarith
    have hfl : ⌊x * (2 : ℝ) ^ (n + 1)⌋ + 1 ≤ 2 * (⌊x * (2 : ℝ) ^ n⌋ + 1) := by
      have h2 : ⌊x * (2 : ℝ) ^ (n + 1)⌋ < 2 * ⌊x * (2 : ℝ) ^ n⌋ + 2 := Int.floor_lt.mpr hlt
      omega
    have hflq : ((⌊x * (2 : ℝ) ^ (n + 1)⌋ + 1 : ℤ) : ℚ) ≤
        2 * ((⌊x * (2 : ℝ) ^ n⌋ + 1 : ℤ) : ℚ) := by
      exact_mod_cast hfl
    have hpow : (0 : ℚ) < (2 : ℚ) ^ n := by positivity
    rw [div_le_div_iff₀ (by positivity) hpow]
    calc ((⌊x * (2 : ℝ) ^ (n + 1)⌋ + 1 : ℤ) : ℚ) * (2 : ℚ) ^ n
        ≤ (2 * ((⌊x * (2 : ℝ) ^ n⌋ + 1 : ℤ) : ℚ)) * (2 : ℚ) ^ n := by gcongr
      _ = ((⌊x * (2 : ℝ) ^ n⌋ + 1 : ℤ) : ℚ) * (2 : ℚ) ^ (n + 1) := by rw [pow_succ]; ring
  have htend : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 x) := by
    have hright : Tendsto (fun n : ℕ => x + (1 / 2 : ℝ) ^ n) atTop (𝓝 x) := by
      simpa using tendsto_const_nhds.add
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hright
      (fun n => (hgt n).le) hle
  exact ⟨q, hanti, hgt, htend⟩

private lemma tendsto_S_of_antitone (μ : Measure ℝ) [IsFiniteMeasure μ] (S : ℝ → Measure ℝ)
    (hfin : ∀ x, IsFiniteMeasure (S x)) (hmono : ∀ x x', x ≤ x' → S x ≤ S x')
    (hmass : ∀ x, S x Set.univ = μ (Set.Iic x))
    {x : ℝ} {q : ℕ → ℚ} (hanti : Antitone q) (hgt : ∀ n, x < (q n : ℝ))
    (htend : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 x)) {B : Set ℝ} (hB : MeasurableSet B) :
    Tendsto (fun n => S (q n : ℝ) B) atTop (𝓝 (S x B)) := by
  have hIoc_inter : (⋂ n : ℕ, Set.Ioc x (q n : ℝ)) = ∅ := by
    ext z
    simp only [Set.mem_iInter, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false]
    intro hz
    have hzx : z ≤ x := ge_of_tendsto htend (Eventually.of_forall fun n => (hz n).2)
    exact not_lt.mpr hzx (hz 0).1
  have hIoc_tend : Tendsto (fun n : ℕ => μ (Set.Ioc x (q n : ℝ))) atTop (𝓝 0) := by
    have h1 := tendsto_measure_iInter_atTop (μ := μ)
      (s := fun n : ℕ => Set.Ioc x (q n : ℝ))
      (fun n => measurableSet_Ioc.nullMeasurableSet)
      (fun m n hmn => Set.Ioc_subset_Ioc_right (Rat.cast_le.mpr (hanti hmn)))
      ⟨0, measure_ne_top μ _⟩
    simpa [Function.comp_def, hIoc_inter] using h1
  have hupper : Tendsto (fun n : ℕ => S x B + μ (Set.Ioc x (q n : ℝ))) atTop (𝓝 (S x B)) := by
    simpa using tendsto_const_nhds.add hIoc_tend
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n => hmono x (q n : ℝ) (hgt n).le B)
    (fun n => S_le_add_Ioc μ S hfin hmono hmass (hgt n).le hB)

private lemma toReal_iInf_of_le_one {ι : Type*} [Nonempty ι] {a : ι → ℝ≥0∞}
    (ha : ∀ i, a i ≤ 1) :
    (⨅ i, a i).toReal = ⨅ i, (a i).toReal := by
  have hne : ∀ i, a i ≠ ∞ := fun i => ne_top_of_le_ne_top ENNReal.one_ne_top (ha i)
  have hinf_ne : (⨅ i, a i) ≠ ∞ := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    exact ne_top_of_le_ne_top (hne i₀) (iInf_le a i₀)
  have hbdd : BddBelow (Set.range fun i => (a i).toReal) :=
    ⟨0, fun _ ⟨_, hi⟩ => hi ▸ ENNReal.toReal_nonneg⟩
  refine le_antisymm ?_ ?_
  · exact le_ciInf fun i => ENNReal.toReal_mono (hne i) (iInf_le a i)
  · have hnonneg : 0 ≤ ⨅ i, (a i).toReal := le_ciInf fun _ => ENNReal.toReal_nonneg
    have hle : ENNReal.ofReal (⨅ i, (a i).toReal) ≤ ⨅ i, a i := by
      refine le_iInf fun i => ?_
      rw [← ENNReal.ofReal_toReal (hne i)]
      exact ENNReal.ofReal_le_ofReal (ciInf_le hbdd i)
    calc ⨅ i, (a i).toReal
        = (ENNReal.ofReal (⨅ i, (a i).toReal)).toReal := (ENNReal.toReal_ofReal hnonneg).symm
      _ ≤ (⨅ i, a i).toReal := ENNReal.toReal_mono hinf_ne hle

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ] (S : ℝ → Measure ℝ)
    (hfin : ∀ x, IsFiniteMeasure (S x)) (hmono : ∀ x x', x ≤ x' → S x ≤ S x')
    (hmass : ∀ x, S x Set.univ = μ (Set.Iic x)) :
    ∃ π : Measure (ℝ × ℝ), IsFiniteMeasure π ∧
      ∀ x : ℝ, (π.restrict (Set.Iic x ×ˢ Set.univ)).map Prod.fst = μ.restrict (Set.Iic x) ∧
        MartOT.Var.targetUpTo π x = S x := by
  let Sinf : Measure ℝ := supMeasure S hmono
  have hSinf_fin : IsFiniteMeasure Sinf :=
    ⟨by rw [supMeasure_univ μ S hmono hmass]; exact measure_lt_top μ Set.univ⟩
  have hS_le : ∀ x : ℝ, S x ≤ Sinf := le_supMeasure S hmono
  have hS_ac : ∀ x : ℝ, S x ≪ Sinf := fun x => Measure.absolutelyContinuous_of_le (hS_le x)
  have : ∀ x : ℝ, IsFiniteMeasure (S x) := hfin
  let h : ℚ → ℝ → ℝ≥0∞ := fun q => (S (q : ℝ)).rnDeriv Sinf
  have hh_meas : ∀ q : ℚ, Measurable (h q) := fun q => Measure.measurable_rnDeriv _ _
  have hh_int : ∀ (q : ℚ) (B : Set ℝ), ∫⁻ y in B, h q y ∂Sinf = S (q : ℝ) B :=
    fun q B => Measure.setLIntegral_rnDeriv (hS_ac (q : ℝ)) B
  have hh_int_univ : ∀ q : ℚ, ∫⁻ y, h q y ∂Sinf = S (q : ℝ) Set.univ := fun q => by
    rw [← setLIntegral_univ, hh_int]
  have hh_le_one : ∀ᵐ y ∂Sinf, ∀ q : ℚ, h q y ≤ 1 :=
    ae_all_iff.mpr fun q => Measure.rnDeriv_le_one_of_le (hS_le (q : ℝ))
  have hh_mono : ∀ᵐ y ∂Sinf, ∀ q₁ q₂ : ℚ, q₁ ≤ q₂ → h q₁ y ≤ h q₂ y := by
    refine ae_all_iff.mpr fun q₁ => ae_all_iff.mpr fun q₂ => ae_all_iff.mpr fun hq => ?_
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (hh_meas q₁) fun s _ _ => ?_
    rw [hh_int q₁ s, hh_int q₂ s]
    exact hmono (q₁ : ℝ) (q₂ : ℝ) (Rat.cast_le.mpr hq) s
  have hh_sup : ∀ᵐ y ∂Sinf, ⨆ n : ℕ, h (n : ℚ) y = 1 := by
    have hle1 : (fun y => ⨆ n : ℕ, h (n : ℚ) y) ≤ᵐ[Sinf] (fun _ => (1 : ℝ≥0∞)) :=
      hh_le_one.mono fun y hy => iSup_le fun n => hy (n : ℚ)
    have hint_le : ∫⁻ _ : ℝ, (1 : ℝ≥0∞) ∂Sinf ≤ ∫⁻ y, (⨆ n : ℕ, h (n : ℚ) y) ∂Sinf := by
      rw [lintegral_one, supMeasure_apply S hmono MeasurableSet.univ]
      refine iSup_le fun n => ?_
      have hn : S ((n : ℚ) : ℝ) Set.univ = ∫⁻ y, h (n : ℚ) y ∂Sinf := (hh_int_univ (n : ℚ)).symm
      rw [show (n : ℝ) = ((n : ℚ) : ℝ) by norm_cast, hn]
      exact lintegral_mono fun y => le_iSup (fun m : ℕ => h (m : ℚ) y) n
    have hfin_int : ∫⁻ y, (⨆ n : ℕ, h (n : ℚ) y) ∂Sinf ≠ ∞ :=
      ne_top_of_le_ne_top (by rw [lintegral_one]; exact measure_ne_top Sinf Set.univ)
        (lintegral_mono_ae hle1)
    exact ae_eq_of_ae_le_of_lintegral_le hle1 hfin_int aemeasurable_const hint_le
  have hh_inf : ∀ᵐ y ∂Sinf, ⨅ n : ℕ, h (-(n : ℚ)) y = 0 := by
    have hg_meas : Measurable (fun y => ⨅ n : ℕ, h (-(n : ℚ)) y) :=
      Measurable.iInf fun n => hh_meas (-(n : ℚ))
    have hIic_empty : (⋂ n : ℕ, Set.Iic (-(n : ℝ))) = ∅ := by
      ext r
      simp only [Set.mem_iInter, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_forall]
      obtain ⟨n, hn⟩ := exists_nat_gt (-r)
      exact ⟨n, by linarith⟩
    have hIic_tend : Tendsto (fun n : ℕ => μ (Set.Iic (-(n : ℝ)))) atTop (𝓝 0) := by
      have h1 := tendsto_measure_iInter_atTop (μ := μ)
        (s := fun n : ℕ => Set.Iic (-(n : ℝ)))
        (fun n => measurableSet_Iic.nullMeasurableSet)
        (fun m n hmn => Set.Iic_subset_Iic.mpr (neg_le_neg (Nat.cast_le.mpr hmn)))
        ⟨0, measure_ne_top μ _⟩
      simpa [Function.comp_def, hIic_empty] using h1
    have hint_le : ∀ n : ℕ, ∫⁻ y, (⨅ k : ℕ, h (-(k : ℚ)) y) ∂Sinf ≤ μ (Set.Iic (-(n : ℝ))) := by
      intro n
      calc ∫⁻ y, (⨅ k : ℕ, h (-(k : ℚ)) y) ∂Sinf
          ≤ ∫⁻ y, h (-(n : ℚ)) y ∂Sinf := lintegral_mono fun y => iInf_le (fun k : ℕ => h (-(k : ℚ)) y) n
        _ = S ((-(n : ℚ) : ℚ) : ℝ) Set.univ := hh_int_univ (-(n : ℚ))
        _ = μ (Set.Iic (-(n : ℝ))) := by rw [hmass]; norm_cast
    have hint_zero : ∫⁻ y, (⨅ k : ℕ, h (-(k : ℚ)) y) ∂Sinf = 0 :=
      le_antisymm (ge_of_tendsto hIic_tend (Eventually.of_forall hint_le)) (bot_le)
    exact (lintegral_eq_zero_iff hg_meas).mp hint_zero
  have hh_rc : ∀ᵐ y ∂Sinf, ∀ t : ℚ, ⨅ r : Set.Ioi t, h r y = h t y := by
    refine ae_all_iff.mpr fun t => ?_
    have hle_g : h t ≤ᵐ[Sinf] fun y => ⨅ r : Set.Ioi t, h r y :=
      hh_mono.mono fun y hy => le_iInf fun r => hy t r.1 r.2.le
    have hg_meas : Measurable (fun y => ⨅ r : Set.Ioi t, h r y) :=
      Measurable.iInf fun r => hh_meas r.1
    let rn : ℕ → ℚ := fun n => t + 1 / ((n : ℚ) + 1)
    have hrn_gt : ∀ n : ℕ, t < rn n := fun n => by
      dsimp only [rn]
      linarith [show (0 : ℚ) < 1 / ((n : ℚ) + 1) by positivity]
    have hrn_anti : Antitone rn := fun m n hmn => by
      dsimp only [rn]
      have h1 : (0 : ℚ) < (m : ℚ) + 1 := by positivity
      have h2 : (m : ℚ) + 1 ≤ (n : ℚ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
      have h3 : 1 / ((n : ℚ) + 1) ≤ 1 / ((m : ℚ) + 1) := one_div_le_one_div_of_le h1 h2
      linarith
    have hrn_inter : (⋂ n : ℕ, Set.Iic (rn n : ℝ)) = Set.Iic (t : ℝ) := by
      ext z
      simp only [Set.mem_iInter, Set.mem_Iic]
      constructor
      · intro hz
        have htend_rn : Tendsto (fun n : ℕ => (rn n : ℝ)) atTop (𝓝 (t : ℝ)) := by
          have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          simpa [rn] using tendsto_const_nhds.add h0
        exact ge_of_tendsto htend_rn (Eventually.of_forall hz)
      · intro hz n
        exact hz.trans (Rat.cast_le.mpr (hrn_gt n).le)
    have hIic_tend : Tendsto (fun n : ℕ => μ (Set.Iic (rn n : ℝ))) atTop (𝓝 (μ (Set.Iic (t : ℝ)))) := by
      have h1 := tendsto_measure_iInter_atTop (μ := μ)
        (s := fun n : ℕ => Set.Iic (rn n : ℝ))
        (fun n => measurableSet_Iic.nullMeasurableSet)
        (fun m n hmn => Set.Iic_subset_Iic.mpr (Rat.cast_le.mpr (hrn_anti hmn)))
        ⟨0, measure_ne_top μ _⟩
      simpa [Function.comp_def, hrn_inter] using h1
    have hint_le : ∫⁻ y, (⨅ r : Set.Ioi t, h r y) ∂Sinf ≤ ∫⁻ y, h t y ∂Sinf := by
      rw [hh_int_univ t, hmass (t : ℝ)]
      refine ge_of_tendsto hIic_tend (Eventually.of_forall fun n => ?_)
      calc ∫⁻ y, (⨅ r : Set.Ioi t, h r y) ∂Sinf
          ≤ ∫⁻ y, h (rn n) y ∂Sinf :=
            lintegral_mono fun y => iInf_le (fun r : Set.Ioi t => h r.1 y) ⟨rn n, hrn_gt n⟩
        _ = S (rn n : ℝ) Set.univ := hh_int_univ (rn n)
        _ = μ (Set.Iic (rn n : ℝ)) := hmass (rn n : ℝ)
    have hfin_ht : ∫⁻ y, h t y ∂Sinf ≠ ∞ := by
      rw [hh_int_univ t]
      exact measure_ne_top (S (t : ℝ)) Set.univ
    exact (ae_eq_of_ae_le_of_lintegral_le hle_g hfin_ht hg_meas.aemeasurable hint_le).symm
  let f : ℝ → ℚ → ℝ := fun y q => (h q y).toReal
  have hf_meas : Measurable f :=
    measurable_pi_lambda _ fun q => (hh_meas q).ennreal_toReal
  have hf_stieltjes : ∀ᵐ y ∂Sinf, IsRatStieltjesPoint f y := by
    filter_upwards [hh_le_one, hh_mono, hh_sup, hh_inf, hh_rc] with y h1 hm hsup hinf hrc
    have hne : ∀ q : ℚ, h q y ≠ ∞ := fun q => ne_top_of_le_ne_top ENNReal.one_ne_top (h1 q)
    have hf_mono : Monotone (f y) := fun q₁ q₂ hq =>
      ENNReal.toReal_mono (hne q₂) (hm q₁ q₂ hq)
    have hf_le_one : ∀ q : ℚ, f y q ≤ 1 := fun q => by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top (h1 q)
    have hf_top : Tendsto (f y) atTop (𝓝 1) := by
      rw [tendsto_order]
      refine ⟨fun b hb => ?_, fun b hb => Eventually.of_forall fun q => (hf_le_one q).trans_lt hb⟩
      have hlt : ENNReal.ofReal b < ⨆ n : ℕ, h (n : ℚ) y := by
        rw [hsup]
        exact ENNReal.ofReal_lt_one.mpr hb
      obtain ⟨N, hN⟩ := lt_iSup_iff.mp hlt
      rw [eventually_atTop]
      refine ⟨(N : ℚ), fun q hq => ?_⟩
      have hbN : b < f y (N : ℚ) := by
        by_cases hb0 : b < 0
        · exact hb0.trans_le ENNReal.toReal_nonneg
        · push Not at hb0
          rw [← ENNReal.toReal_ofReal hb0]
          exact (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top (hne (N : ℚ))).mpr hN
      exact hbN.trans_le (hf_mono hq)
    have hf_bot : Tendsto (f y) atBot (𝓝 0) := by
      rw [tendsto_order]
      refine ⟨fun a ha => Eventually.of_forall fun q => ha.trans_le ENNReal.toReal_nonneg,
        fun b hb => ?_⟩
      have hlt : (⨅ n : ℕ, h (-(n : ℚ)) y) < ENNReal.ofReal b := by
        rw [hinf]
        exact ENNReal.ofReal_pos.mpr hb
      obtain ⟨N, hN⟩ := iInf_lt_iff.mp hlt
      rw [eventually_atBot]
      refine ⟨-(N : ℚ), fun q hq => ?_⟩
      have hNb : f y (-(N : ℚ)) < b := by
        rw [← ENNReal.toReal_ofReal hb.le]
        exact (ENNReal.toReal_lt_toReal (hne (-(N : ℚ))) ENNReal.ofReal_ne_top).mpr hN
      exact (hf_mono hq).trans_lt hNb
    have hf_rc : ∀ t : ℚ, ⨅ r : Set.Ioi t, f y r = f y t := fun t => by
      have : Nonempty (Set.Ioi t) := ⟨⟨t + 1, lt_add_one t⟩⟩
      rw [← toReal_iInf_of_le_one (fun r : Set.Ioi t => h1 r.1), hrc t]
    exact ⟨hf_mono, hf_top, hf_bot, hf_rc⟩
  let κ : Kernel ℝ ℝ :=
    ⟨fun y => (stieltjesOfMeasurableRat f hf_meas y).measure,
      measurable_measure_stieltjesOfMeasurableRat hf_meas⟩
  have : IsMarkovKernel κ :=
    ⟨fun y => instIsProbabilityMeasure_stieltjesOfMeasurableRat hf_meas y⟩
  have hcomp_fin : IsFiniteMeasure (Sinf ⊗ₘ κ) :=
    ⟨by rw [Measure.compProd_apply_univ]; exact measure_lt_top Sinf Set.univ⟩
  let π : Measure (ℝ × ℝ) := (Sinf ⊗ₘ κ).map Prod.swap
  have hπ_fin : IsFiniteMeasure π := Measure.isFiniteMeasure_map (Sinf ⊗ₘ κ) Prod.swap
  have htarget_rat : ∀ q : ℚ, MartOT.Var.targetUpTo π (q : ℝ) = S (q : ℝ) := by
    intro q
    refine Measure.ext fun B hB => ?_
    rw [MartOT.Var.targetUpTo, Measure.map_apply measurable_snd hB,
      Measure.restrict_apply (measurable_snd hB)]
    have hset : Prod.snd ⁻¹' B ∩ (Set.Iic (q : ℝ) ×ˢ Set.univ) = Set.Iic (q : ℝ) ×ˢ B := by
      ext ⟨a, b⟩; simp [and_comm]
    rw [hset, Measure.map_apply measurable_swap (measurableSet_Iic.prod hB)]
    have hswap : Prod.swap ⁻¹' (Set.Iic (q : ℝ) ×ˢ B) = B ×ˢ Set.Iic (q : ℝ) := by
      ext ⟨b, a⟩; simp
    rw [hswap, Measure.compProd_apply_prod hB measurableSet_Iic]
    have hae : ∀ᵐ y ∂Sinf, κ y (Set.Iic (q : ℝ)) = h q y := by
      filter_upwards [hf_stieltjes, hh_le_one] with y hy h1
      change (stieltjesOfMeasurableRat f hf_meas y).measure (Set.Iic (q : ℝ)) = h q y
      rw [measure_stieltjesOfMeasurableRat_Iic hf_meas y (q : ℝ),
        stieltjesOfMeasurableRat_eq hf_meas y q,
        toRatCDF_of_isRatStieltjesPoint hy q]
      exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (h1 q))
    rw [lintegral_congr_ae (ae_restrict_of_ae hae), hh_int q B]
  have htarget : ∀ x : ℝ, MartOT.Var.targetUpTo π x = S x := by
    intro x
    refine Measure.ext fun B hB => ?_
    obtain ⟨q, hanti, hgt, htend⟩ := exists_rat_antitone_tendsto x
    have hS_tend : Tendsto (fun n => S (q n : ℝ) B) atTop (𝓝 (S x B)) :=
      tendsto_S_of_antitone μ S hfin hmono hmass hanti hgt htend hB
    have hπ_eq : ∀ z : ℝ, MartOT.Var.targetUpTo π z B = π (Set.Iic z ×ˢ B) := fun z => by
      rw [MartOT.Var.targetUpTo, Measure.map_apply measurable_snd hB,
        Measure.restrict_apply (measurable_snd hB)]
      congr 1
      ext ⟨a, b⟩; simp [and_comm]
    have hinter : (⋂ n : ℕ, Set.Iic (q n : ℝ) ×ˢ B) = Set.Iic x ×ˢ B := by
      ext ⟨a, b⟩
      simp only [Set.mem_iInter, Set.mem_prod, Set.mem_Iic]
      constructor
      · intro h
        exact ⟨ge_of_tendsto htend (Eventually.of_forall fun n => (h n).1), (h 0).2⟩
      · rintro ⟨ha, hb⟩ n
        exact ⟨ha.trans (hgt n).le, hb⟩
    have hπ_tend : Tendsto (fun n : ℕ => π (Set.Iic (q n : ℝ) ×ˢ B)) atTop
        (𝓝 (π (Set.Iic x ×ˢ B))) := by
      have h1 := tendsto_measure_iInter_atTop (μ := π)
        (s := fun n : ℕ => Set.Iic (q n : ℝ) ×ˢ B)
        (fun n => (measurableSet_Iic.prod hB).nullMeasurableSet)
        (fun m n hmn => Set.prod_mono_left (Set.Iic_subset_Iic.mpr (Rat.cast_le.mpr (hanti hmn))))
        ⟨0, measure_ne_top π _⟩
      simpa [Function.comp_def, hinter] using h1
    have hS_eq : (fun n : ℕ => π (Set.Iic (q n : ℝ) ×ˢ B)) = fun n : ℕ => S (q n : ℝ) B := by
      funext n
      rw [← hπ_eq (q n : ℝ), htarget_rat (q n)]
    rw [hS_eq] at hπ_tend
    rw [hπ_eq x]
    exact tendsto_nhds_unique hπ_tend hS_tend
  refine ⟨π, hπ_fin, fun x => ⟨?_, htarget x⟩⟩
  refine Measure.ext_of_Iic _ _ fun z => ?_
  rw [Measure.map_apply measurable_fst measurableSet_Iic,
    Measure.restrict_apply (measurable_fst measurableSet_Iic),
    Measure.restrict_apply measurableSet_Iic]
  have hset : (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Iic z ∩ (Set.Iic x ×ˢ (Set.univ : Set ℝ)) =
      Set.Iic (min z x) ×ˢ (Set.univ : Set ℝ) := by
    ext ⟨a, b⟩; simp
  rw [hset]
  have hmin : π (Set.Iic (min z x) ×ˢ Set.univ) = MartOT.Var.targetUpTo π (min z x) Set.univ := by
    rw [MartOT.Var.targetUpTo, Measure.map_apply measurable_snd MeasurableSet.univ,
      Set.preimage_univ, Measure.restrict_apply_univ]
  rw [hmin, htarget (min z x), hmass (min z x)]
  congr 1
  ext a
  simp
