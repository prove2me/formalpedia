-- Prove2me | solution 1 for Kyprianou.Ch03.killedSubordinator_givenMaximalRoot
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T19:32:41.23974+00:00
-- url     : https://prove2.me/submissions/cd1c1d76-6af4-4eb5-998e-c499c7e4353b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Theorems.Thm_Kyprianou_Ch03_spectrallyNegative_esscherCanonicalTilt
import Theorems.Thm_Kyprianou_Ch03_upwardPassage_zeroRootIsSubordinator

open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03.KilledSubordinatorProof

private lemma firstHittingTime_Ioi_mono
    {Omega : Type} (X : NNReal → Omega → ℝ) (ω : Omega) :
    Monotone (fun x : NNReal => firstHittingTime X (Set.Ioi (x : ℝ)) ω) := by
  intro x y hxy
  unfold firstHittingTime
  apply sInf_le_sInf
  rintro _ ⟨t, ⟨htpos, hty⟩, rfl⟩
  have hxy' : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast hxy
  exact ⟨t, ⟨htpos, lt_of_le_of_lt hxy' hty⟩, rfl⟩

private lemma firstHittingTime_Ioi_lt_coe_iff
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x a : NNReal) (ω : Omega) :
    firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (a : WithTop NNReal) ↔
      ∃ q : ℚ, 0 < q ∧ (q : ℝ) < (a : ℝ) ∧ (x : ℝ) < L.X (Real.toNNReal (q : ℝ)) ω := by
  constructor
  · intro hlt
    unfold firstHittingTime at hlt
    rcases sInf_lt_iff.mp hlt with ⟨_, ⟨t, ⟨htpos, htx⟩, rfl⟩, hta⟩
    have hta' : (t : ℝ) < (a : ℝ) := by exact_mod_cast (WithTop.coe_lt_coe.mp hta)
    have hrc := L.rightCont ω t
    have hmem : Set.Ioi (x : ℝ) ∈ 𝓝 (L.X t ω) := isOpen_Ioi.mem_nhds htx
    have hev : ∀ᶠ s in 𝓝[Set.Ici t] t, (x : ℝ) < L.X s ω := hrc.eventually hmem
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    rcases hev with ⟨δ, hδpos, hδ⟩
    let u : ℝ := min (a : ℝ) ((t : ℝ) + δ)
    have htu : (t : ℝ) < u := lt_min hta' (by linarith)
    rcases exists_rat_btwn htu with ⟨q, htq, hqu⟩
    have hq_pos : (0 : ℚ) < q := by
      have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htpos
      have : (0 : ℝ) < (q : ℝ) := lt_trans ht0 htq
      exact_mod_cast this
    have hq_lt_a : (q : ℝ) < (a : ℝ) := lt_of_lt_of_le hqu (min_le_left _ _)
    have hq_nn_ge : t ≤ Real.toNNReal (q : ℝ) := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (le_of_lt (by exact_mod_cast hq_pos))]
      exact le_of_lt htq
    have hq_dist : dist (Real.toNNReal (q : ℝ)) t < δ := by
      rw [NNReal.dist_eq, Real.coe_toNNReal _ (le_of_lt (by exact_mod_cast hq_pos)),
        abs_of_nonneg (by linarith)]
      have : (q : ℝ) < (t : ℝ) + δ := lt_of_lt_of_le hqu (min_le_right _ _)
      linarith
    exact ⟨q, hq_pos, hq_lt_a, hδ hq_dist hq_nn_ge⟩
  · rintro ⟨q, hqpos, hqa, hqx⟩
    unfold firstHittingTime
    have hqnn_pos : (0 : NNReal) < Real.toNNReal (q : ℝ) :=
      Real.toNNReal_pos.mpr (by exact_mod_cast hqpos)
    have hqnn_lt : Real.toNNReal (q : ℝ) < a := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (le_of_lt (by exact_mod_cast hqpos))]
      exact hqa
    exact lt_of_le_of_lt
      (sInf_le ⟨Real.toNNReal (q : ℝ), ⟨hqnn_pos, hqx⟩, rfl⟩)
      (WithTop.coe_lt_coe.mpr hqnn_lt)

private lemma measurable_firstHittingTime_Ioi
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) (x : NNReal) :
    Measurable (fun ω : Omega => firstHittingTime L.X (Set.Ioi (x : ℝ)) ω) := by
  have hlt : ∀ a : NNReal,
      MeasurableSet {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (a : WithTop NNReal)} := by
    intro a
    have hEq :
        {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (a : WithTop NNReal)} =
          ⋃ q : {q : ℚ // 0 < q ∧ (q : ℝ) < (a : ℝ)},
            {ω : Omega | (x : ℝ) < L.X (Real.toNNReal (q.1 : ℝ)) ω} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Subtype.exists]
      simpa [and_assoc] using firstHittingTime_Ioi_lt_coe_iff L x a ω
    rw [hEq]
    refine MeasurableSet.iUnion fun q => ?_
    have hmeasX : Measurable (L.X (Real.toNNReal (q.1 : ℝ))) :=
      (L.adapted (Real.toNNReal (q.1 : ℝ))).mono (F.le _) le_rfl
    exact measurableSet_lt measurable_const hmeasX
  have hlt_top : ∀ b : WithTop NNReal,
      MeasurableSet {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < b} := by
    intro b
    cases b with
    | top =>
      have hEq :
          {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (⊤ : WithTop NNReal)} =
            ⋃ n : ℕ, {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < ((n : NNReal) : WithTop NNReal)} := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
        constructor
        · intro h
          rcases WithTop.lt_top_iff_ne_top.mp h |> WithTop.ne_top_iff_exists.mp with ⟨t, ht⟩
          rw [← ht]
          rcases exists_nat_gt (t : ℝ) with ⟨n, hn⟩
          refine ⟨n, WithTop.coe_lt_coe.mpr ?_⟩
          exact_mod_cast hn
        · rintro ⟨n, hn⟩
          exact lt_trans hn (WithTop.coe_lt_top _)
      rw [hEq]
      exact MeasurableSet.iUnion fun n => hlt (n : NNReal)
    | coe a => exact hlt a
  exact measurable_of_Iio hlt_top

private noncomputable def killingMeasure (phi : ℝ) : Measure (WithTop NNReal) :=
  if phi = 0 then Measure.dirac ⊤
  else Measure.map
    (fun r : ℝ => (Real.toNNReal (-Real.log r / phi) : WithTop NNReal))
    (volume.restrict (Set.Ioc (0 : ℝ) 1))

private lemma measurable_expTransform (phi : ℝ) :
    Measurable (fun r : ℝ => (Real.toNNReal (-Real.log r / phi) : WithTop NNReal)) := by
  have h1 : Measurable (fun r : ℝ => Real.toNNReal (-Real.log r / phi)) :=
    ((Real.measurable_log.neg).div_const phi).real_toNNReal
  exact WithTop.measurable_coe.comp h1

private lemma isProbabilityMeasure_volume_Ioc_01 :
    IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ, Real.volume_Ioc]
  norm_num

private lemma isProbabilityMeasure_killingMeasure (phi : ℝ) :
    IsProbabilityMeasure (killingMeasure phi) := by
  unfold killingMeasure
  split_ifs with h
  · infer_instance
  · have : IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      isProbabilityMeasure_volume_Ioc_01
    exact Measure.isProbabilityMeasure_map (measurable_expTransform phi).aemeasurable

private lemma killingMeasure_Ioi {phi : ℝ} (hphi : 0 ≤ phi) (x : NNReal) :
    killingMeasure phi {z : WithTop NNReal | (x : WithTop NNReal) < z} =
      ENNReal.ofReal (Real.exp (-phi * (x : ℝ))) := by
  unfold killingMeasure
  split_ifs with h0
  · subst h0
    have hm : MeasurableSet {z : WithTop NNReal | (x : WithTop NNReal) < z} :=
      measurableSet_lt measurable_const measurable_id
    have hmem : (⊤ : WithTop NNReal) ∈ {z : WithTop NNReal | (x : WithTop NNReal) < z} :=
      WithTop.coe_lt_top x
    rw [Measure.dirac_apply' _ hm, Set.indicator_of_mem hmem]
    simp
  · have hpos : 0 < phi := lt_of_le_of_ne hphi (Ne.symm h0)
    have hmeasS : MeasurableSet {z : WithTop NNReal | (x : WithTop NNReal) < z} :=
      measurableSet_lt measurable_const measurable_id
    rw [Measure.map_apply (measurable_expTransform phi) hmeasS,
      Measure.restrict_apply ((measurable_expTransform phi) hmeasS)]
    have hPre :
        ((fun r : ℝ => (Real.toNNReal (-Real.log r / phi) : WithTop NNReal)) ⁻¹'
          {z : WithTop NNReal | (x : WithTop NNReal) < z}) ∩ Set.Ioc (0 : ℝ) 1 =
          Set.Ioo (0 : ℝ) (Real.exp (-phi * (x : ℝ))) := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ioc, Set.mem_Ioo,
        WithTop.coe_lt_coe]
      constructor
      · rintro ⟨hlt, hr0, hr1⟩
        have hlt_real : (x : ℝ) < -Real.log r / phi := by
          have hpos_rhs : 0 < -Real.log r / phi := by
            by_contra hle
            push Not at hle
            rw [Real.toNNReal_of_nonpos hle] at hlt
            exact not_lt_zero hlt
          rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (le_of_lt hpos_rhs)] at hlt
          exact hlt
        have hlog : Real.log r < -phi * (x : ℝ) := by
          have := (lt_div_iff₀ hpos).mp hlt_real
          linarith
        refine ⟨hr0, ?_⟩
        calc r = Real.exp (Real.log r) := (Real.exp_log hr0).symm
          _ < Real.exp (-phi * (x : ℝ)) := Real.exp_lt_exp.mpr hlog
      · rintro ⟨hr0, hr_exp⟩
        have hexp_le1 : Real.exp (-phi * (x : ℝ)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [x.coe_nonneg])
        have hr1 : r ≤ 1 := le_of_lt (lt_of_lt_of_le hr_exp hexp_le1)
        have hlog : Real.log r < -phi * (x : ℝ) := by
          rw [← Real.log_exp (-phi * (x : ℝ))]
          exact Real.log_lt_log hr0 hr_exp
        have hlt_real : (x : ℝ) < -Real.log r / phi :=
          (lt_div_iff₀ hpos).mpr (by linarith)
        have hpos_rhs : 0 ≤ -Real.log r / phi := le_trans x.coe_nonneg (le_of_lt hlt_real)
        refine ⟨?_, hr0, hr1⟩
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hpos_rhs]
        exact hlt_real
    rw [hPre, Real.volume_Ioo, sub_zero]

private lemma killingMeasure_top_of_eq_zero {phi : ℝ} (h0 : phi = 0) :
    killingMeasure phi {z : WithTop NNReal | z = ⊤} = 1 := by
  subst h0
  unfold killingMeasure
  simp

private lemma killingMeasure_ne_top_of_pos {phi : ℝ} (hpos : 0 < phi) :
    killingMeasure phi {z : WithTop NNReal | z != ⊤} = 1 := by
  unfold killingMeasure
  rw [if_neg (ne_of_gt hpos)]
  have hmeas : MeasurableSet {z : WithTop NNReal | z != ⊤} := by
    have hEq : {z : WithTop NNReal | z != ⊤} = ({⊤} : Set (WithTop NNReal))ᶜ := by
      ext z; simp
    rw [hEq]
    exact (MeasurableSet.singleton ⊤).compl
  rw [Measure.map_apply (measurable_expTransform phi) hmeas]
  have hPre :
      (fun r : ℝ => (Real.toNNReal (-Real.log r / phi) : WithTop NNReal)) ⁻¹'
        {z : WithTop NNReal | z != ⊤} = Set.univ := by
    ext r
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ, iff_true, bne_iff_ne]
    exact WithTop.coe_ne_top
  rw [hPre, Measure.restrict_apply_univ, Real.volume_Ioc]
  norm_num

private lemma isSubordinator_comp_fst
    {Omega1 OmegaZ : Type} [MeasurableSpace Omega1] [MeasurableSpace OmegaZ]
    {Q1 : Measure Omega1} [IsProbabilityMeasure Q1]
    {μZ : Measure OmegaZ} [IsProbabilityMeasure μZ]
    {S1 : NNReal → Omega1 → ℝ}
    (hSub : IsSubordinator Q1 S1)
    (hMeas : ∀ x : NNReal, Measurable (S1 x)) :
    IsSubordinator (Q1.prod μZ) (fun x p => S1 x p.1) := by
  have hfst : Measure.map Prod.fst (Q1.prod μZ) = Q1 := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · funext p
    exact congrFun hSub.1.start_zero p.1
  · intro n t ht
    rw [iIndepFun_iff]
    intro s f' hf'
    have hEq_lhs :
        (⋂ i ∈ s, f' i) = ⋂ i ∈ s, f' i := rfl
    have hpre : ∀ i ∈ s, ∃ B : Set ℝ, MeasurableSet B ∧
        f' i = Prod.fst ⁻¹' (increment S1 (t i.castSucc) (t i.succ) ⁻¹' B) := by
      intro i hi
      rcases hf' i hi with ⟨B, hB, hBi⟩
      refine ⟨B, hB, ?_⟩
      rw [← hBi]
      rfl
    choose B hB hBeq using hpre
    have hEq1 : (⋂ i ∈ s, f' i) =
        Prod.fst ⁻¹' (⋂ i ∈ s, if hi : i ∈ s then
          increment S1 (t i.castSucc) (t i.succ) ⁻¹' B i hi else Set.univ) := by
      ext p
      simp only [Set.mem_iInter, Set.mem_preimage]
      constructor
      · intro hp i hi
        rw [dif_pos hi]
        have := hp i hi
        rw [hBeq i hi] at this
        exact this
      · intro hp i hi
        rw [hBeq i hi]
        have := hp i hi
        rwa [dif_pos hi] at this
    have hMeasInner : MeasurableSet (⋂ i ∈ s, if hi : i ∈ s then
        increment S1 (t i.castSucc) (t i.succ) ⁻¹' B i hi else Set.univ) := by
      refine Finset.measurableSet_biInter s fun i hi => ?_
      rw [dif_pos hi]
      exact ((hMeas (t i.succ)).sub (hMeas (t i.castSucc))) (hB i hi)
    rw [hEq1, ← Measure.map_apply measurable_fst hMeasInner, hfst]
    have hInd := hSub.1.indep_increments n t ht
    rw [iIndepFun_iff] at hInd
    have hIndS := hInd s
      (f' := fun i => if hi : i ∈ s then
        increment S1 (t i.castSucc) (t i.succ) ⁻¹' B i hi else Set.univ)
      (by
        intro i hi
        rw [dif_pos hi]
        exact ⟨B i hi, hB i hi, rfl⟩)
    rw [hIndS]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [dif_pos hi, hBeq i hi]
    have hMi : MeasurableSet (increment S1 (t i.castSucc) (t i.succ) ⁻¹' B i hi) :=
      ((hMeas (t i.succ)).sub (hMeas (t i.castSucc))) (hB i hi)
    rw [← Measure.map_apply measurable_fst hMi, hfst]
  · intro s h
    have hM1 : Measurable (increment S1 s (s + h)) := (hMeas (s + h)).sub (hMeas s)
    have hM2 : Measurable (increment S1 0 h) := (hMeas h).sub (hMeas 0)
    refine ⟨(hM1.comp measurable_fst).aemeasurable, (hM2.comp measurable_fst).aemeasurable, ?_⟩
    change Measure.map (increment S1 s (s + h) ∘ Prod.fst) (Q1.prod μZ) =
      Measure.map (increment S1 0 h ∘ Prod.fst) (Q1.prod μZ)
    rw [← Measure.map_map hM1 measurable_fst, ← Measure.map_map hM2 measurable_fst, hfst]
    exact (hSub.1.stationary_increments s h).map_eq
  · have h := hSub.1.cadlag_ae
    rw [ae_iff] at h ⊢
    have hEq : {p : Omega1 × OmegaZ | ¬ IsCadlag (fun x => S1 x p.1)} =
        {ω : Omega1 | ¬ IsCadlag (fun x => S1 x ω)} ×ˢ Set.univ := by
      ext p; simp
    rw [hEq, Measure.prod_prod, h, zero_mul]
  · have h := hSub.2
    rw [ae_iff] at h ⊢
    have hEq : {p : Omega1 × OmegaZ | ¬ Monotone (fun x => S1 x p.1)} =
        {ω : Omega1 | ¬ Monotone (fun x => S1 x ω)} ×ˢ Set.univ := by
      ext p; simp
    rw [hEq, Measure.prod_prod, h, zero_mul]

private lemma indep_snd_comp_fst
    {Omega1 OmegaZ : Type} [MeasurableSpace Omega1] [MeasurableSpace OmegaZ]
    {Q1 : Measure Omega1} [IsProbabilityMeasure Q1]
    {μZ : Measure OmegaZ} [IsProbabilityMeasure μZ]
    {S1 : NNReal → Omega1 → ℝ} :
    Indep
      (MeasurableSpace.comap (Prod.snd : Omega1 × OmegaZ → OmegaZ) inferInstance)
      (MeasurableSpace.comap
        (fun p : Omega1 × OmegaZ => fun x : NNReal => S1 x p.1)
        (inferInstance : MeasurableSpace (NNReal → ℝ)))
      (Q1.prod μZ) := by
  rw [Indep_iff]
  rintro s t ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  let B1 : Set Omega1 := (fun ω : Omega1 => fun x : NNReal => S1 x ω) ⁻¹' B
  have h1 : (Prod.snd : Omega1 × OmegaZ → OmegaZ) ⁻¹' A =
      (Set.univ : Set Omega1) ×ˢ A := by ext p; simp
  have h2 : (fun p : Omega1 × OmegaZ => fun x : NNReal => S1 x p.1) ⁻¹' B =
      B1 ×ˢ (Set.univ : Set OmegaZ) := by ext p; simp [B1]
  have h3 : ((Set.univ : Set Omega1) ×ˢ A) ∩ (B1 ×ˢ (Set.univ : Set OmegaZ)) =
      B1 ×ˢ A := by ext p; simp [and_comm]
  rw [h1, h2, h3, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod,
    measure_univ, measure_univ, one_mul, mul_one, mul_comm]

private lemma measure_eq_on_pi_rectangles
    {μ ν : Measure (NNReal → WithTop NNReal)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hPure : ∀ (U : Finset NNReal) (B : NNReal → Set (WithTop NNReal)),
      (∀ u ∈ U, MeasurableSet (B u)) →
      (∀ u ∈ U, (⊤ ∉ B u) ∨ (B u = {⊤})) →
      μ (⋂ u ∈ U, {f : NNReal → WithTop NNReal | f u ∈ B u}) =
      ν (⋂ u ∈ U, {f : NNReal → WithTop NNReal | f u ∈ B u})) :
    μ = ν := by
  let 𝒞 : Set (Set (NNReal → WithTop NNReal)) :=
    {A | ∃ (U : Finset NNReal) (B : NNReal → Set (WithTop NNReal)),
      (∀ u ∈ U, MeasurableSet (B u)) ∧
      A = ⋂ u ∈ U, {f : NNReal → WithTop NNReal | f u ∈ B u}}
  have hGen : (inferInstance : MeasurableSpace (NNReal → WithTop NNReal)) =
      MeasurableSpace.generateFrom 𝒞 := by
    apply le_antisymm
    · rw [MeasurableSpace.pi_eq_generateFrom_projections]
      refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨x, s, hs, rfl⟩
      refine MeasurableSpace.measurableSet_generateFrom ?_
      refine ⟨{x}, fun _ => s, by simp [hs], ?_⟩
      ext f; simp
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨U, B, hB, rfl⟩
      exact Finset.measurableSet_biInter U fun u hu => (measurable_pi_apply u) (hB u hu)
  have hPi : IsPiSystem 𝒞 := by
    rintro _ ⟨U1, B1, hB1, rfl⟩ _ ⟨U2, B2, hB2, rfl⟩ _
    classical
    refine ⟨U1 ∪ U2, fun u => (if u ∈ U1 then B1 u else Set.univ) ∩ (if u ∈ U2 then B2 u else Set.univ), ?_, ?_⟩
    · intro u _
      refine MeasurableSet.inter ?_ ?_
      · split_ifs with h1; exact hB1 u h1; exact MeasurableSet.univ
      · split_ifs with h2; exact hB2 u h2; exact MeasurableSet.univ
    · ext f
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, Finset.mem_union]
      constructor
      · rintro ⟨h1, h2⟩ u _
        refine ⟨?_, ?_⟩
        · split_ifs with hu1; exact h1 u hu1; trivial
        · split_ifs with hu2; exact h2 u hu2; trivial
      · intro h
        refine ⟨fun u hu1 => ?_, fun u hu2 => ?_⟩
        · have := (h u (Or.inl hu1)).1; rwa [if_pos hu1] at this
        · have := (h u (Or.inr hu2)).2; rwa [if_pos hu2] at this
  have hAll : ∀ A ∈ 𝒞, μ A = ν A := by
    rintro _ ⟨U, B, hB, rfl⟩
    classical
    suffices hInd : ∀ n : ℕ, ∀ (B : NNReal → Set (WithTop NNReal)),
        (∀ u ∈ U, MeasurableSet (B u)) →
        (U.filter (fun u => ⊤ ∈ B u ∧ B u ≠ {⊤})).card = n →
        μ (⋂ u ∈ U, {f : NNReal → WithTop NNReal | f u ∈ B u}) =
        ν (⋂ u ∈ U, {f : NNReal → WithTop NNReal | f u ∈ B u}) from
      hInd _ B hB rfl
    intro n
    induction n with
    | zero =>
      intro B hB hcard
      apply hPure U B hB
      intro u hu
      by_cases htop : ⊤ ∈ B u
      · right
        by_contra hne
        have hmem : u ∈ U.filter (fun u => ⊤ ∈ B u ∧ B u ≠ {⊤}) :=
          Finset.mem_filter.mpr ⟨hu, htop, hne⟩
        have hpos := Finset.card_pos.mpr ⟨u, hmem⟩
        omega
      · left; exact htop
    | succ n ih =>
      intro B hB hcard
      have hne : (U.filter (fun u => ⊤ ∈ B u ∧ B u ≠ {⊤})).Nonempty :=
        Finset.card_pos.mp (by omega)
      rcases hne with ⟨u0, hu0⟩
      rw [Finset.mem_filter] at hu0
      rcases hu0 with ⟨hu0U, hu0top, hu0ne⟩
      let Bfin : NNReal → Set (WithTop NNReal) := fun u => if u = u0 then B u0 \ {⊤} else B u
      let Btop : NNReal → Set (WithTop NNReal) := fun u => if u = u0 then {⊤} else B u
      have hBfin : ∀ u ∈ U, MeasurableSet (Bfin u) := by
        intro u hu
        dsimp [Bfin]
        split_ifs with h
        · exact (hB u0 hu0U).diff (MeasurableSet.singleton ⊤)
        · exact hB u hu
      have hBtop : ∀ u ∈ U, MeasurableSet (Btop u) := by
        intro u hu
        dsimp [Btop]
        split_ifs with h
        · exact MeasurableSet.singleton ⊤
        · exact hB u hu
      let Afin : Set (NNReal → WithTop NNReal) := ⋂ u ∈ U, {f | f u ∈ Bfin u}
      let Atop : Set (NNReal → WithTop NNReal) := ⋂ u ∈ U, {f | f u ∈ Btop u}
      have hDisj : Disjoint Afin Atop := by
        rw [Set.disjoint_left]
        intro f hf1 hf2
        have h1 : f u0 ∈ Bfin u0 := by
          have := Set.mem_iInter₂.mp hf1 u0 hu0U; exact this
        have h2 : f u0 ∈ Btop u0 := by
          have := Set.mem_iInter₂.mp hf2 u0 hu0U; exact this
        simp only [Bfin, Btop, if_pos rfl, Set.mem_sdiff, Set.mem_singleton_iff] at h1 h2
        exact h1.2 h2
      have hUnion : (⋂ u ∈ U, {f : NNReal → WithTop NNReal | f u ∈ B u}) = Afin ∪ Atop := by
        ext f
        simp only [Afin, Atop, Set.mem_union, Set.mem_iInter, Set.mem_ofPred_eq]
        constructor
        · intro hf
          by_cases hfu0 : f u0 = ⊤
          · right
            intro u hu
            dsimp [Btop]
            split_ifs with h
            · rw [h]; exact hfu0
            · exact hf u hu
          · left
            intro u hu
            dsimp [Bfin]
            split_ifs with h
            · rw [h]; exact ⟨hf u0 hu0U, hfu0⟩
            · exact hf u hu
        · rintro (hf | hf) u hu
          · have := hf u hu
            dsimp [Bfin] at this
            split_ifs at this with h
            · rw [h]; rw [h] at this; exact this.1
            · exact this
          · have := hf u hu
            dsimp [Btop] at this
            split_ifs at this with h
            · rw [h]; rw [h] at this; rw [Set.mem_singleton_iff.mp this]; exact hu0top
            · exact this
      have hMeasAtop : MeasurableSet Atop :=
        Finset.measurableSet_biInter U fun u hu => (measurable_pi_apply u) (hBtop u hu)
      have hCardFin : (U.filter (fun u => ⊤ ∈ Bfin u ∧ Bfin u ≠ {⊤})).card = n := by
        have hEq : U.filter (fun u => ⊤ ∈ Bfin u ∧ Bfin u ≠ {⊤}) =
            (U.filter (fun u => ⊤ ∈ B u ∧ B u ≠ {⊤})).erase u0 := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_erase, Bfin]
          by_cases h : u = u0
          · subst h; simp
          · simp [h]
        rw [hEq, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hu0U, hu0top, hu0ne⟩), hcard]
        simp
      have hCardTop : (U.filter (fun u => ⊤ ∈ Btop u ∧ Btop u ≠ {⊤})).card = n := by
        have hEq : U.filter (fun u => ⊤ ∈ Btop u ∧ Btop u ≠ {⊤}) =
            (U.filter (fun u => ⊤ ∈ B u ∧ B u ≠ {⊤})).erase u0 := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_erase, Btop]
          by_cases h : u = u0
          · subst h; simp
          · simp [h]
        rw [hEq, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hu0U, hu0top, hu0ne⟩), hcard]
        simp
      rw [hUnion, measure_union hDisj hMeasAtop, measure_union hDisj hMeasAtop,
        ih Bfin hBfin hCardFin, ih Btop hBtop hCardTop]
  exact MeasureTheory.ext_of_generate_finite 𝒞 hGen hPi hAll (by simp)

end Kyprianou.Ch03.KilledSubordinatorProof

open Kyprianou.Ch03 Kyprianou.Ch03.KilledSubordinatorProof

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega)))
    (phi : Real)
    (hRoot : 0 <= phi ∧ L.ψ phi = 0 ∧
      (forall theta : Real, 0 <= theta ->
        L.ψ theta = 0 -> theta <= phi)) :
    exists (Omega2 : Type) (m2 : MeasurableSpace Omega2),
        letI : MeasurableSpace Omega2 := m2
        exists (Q : Measure Omega2) (hQ : IsProbabilityMeasure Q),
          letI : IsProbabilityMeasure Q := hQ
          exists (S : NNReal -> Omega2 -> Real)
                 (zeta : Omega2 -> WithTop NNReal),
            IsSubordinator Q S ∧
            Indep
              (MeasurableSpace.comap zeta
                (inferInstance : MeasurableSpace (WithTop NNReal)))
              (MeasurableSpace.comap
                (fun omega : Omega2 => fun x : NNReal => S x omega)
                (inferInstance : MeasurableSpace (NNReal -> Real)))
              Q ∧
            (forall x : NNReal,
              (Q {omega : Omega2 |
                (x : WithTop NNReal) < zeta omega}).toReal =
                  Real.exp (-phi * (x : Real))) ∧
            (phi = 0 ->
              (Q {omega : Omega2 | zeta omega = ⊤}).toReal = 1) ∧
            (0 < phi ->
              (Q {omega : Omega2 | zeta omega != ⊤}).toReal = 1) ∧
            Measure.map
              (fun omega : Omega =>
                fun x : NNReal =>
                  firstHittingTime L.X (Set.Ioi (x : Real)) omega) P =
            Measure.map
              (fun omega : Omega2 =>
                fun x : NNReal =>
                  if (x : WithTop NNReal) < zeta omega
                  then (Real.toNNReal (S x omega) : WithTop NNReal)
                  else ⊤) Q := by
  rcases spectrallyNegative_esscherCanonicalTilt P F L hNotDecreasing phi hRoot with
    ⟨Omega1, m1, Q1, hQ1, F1, L1, hNotDec1, hZeroRoot1, hTilt⟩
  let _ : MeasurableSpace Omega1 := m1
  have _ : IsProbabilityMeasure Q1 := hQ1
  rcases upwardPassage_zeroRootIsSubordinator Q1 F1 L1 hNotDec1 hZeroRoot1 with
    ⟨S1, hSub1, hMeasS1, hLaw1⟩
  let μZ : Measure (WithTop NNReal) := killingMeasure phi
  have : IsProbabilityMeasure μZ := isProbabilityMeasure_killingMeasure phi
  let Omega2 : Type := Omega1 × WithTop NNReal
  let m2 : MeasurableSpace Omega2 := inferInstance
  let Q : Measure Omega2 := Q1.prod μZ
  have hQ : IsProbabilityMeasure Q := inferInstance
  let S : NNReal → Omega2 → ℝ := fun x p => S1 x p.1
  let zeta : Omega2 → WithTop NNReal := Prod.snd
  refine ⟨Omega2, m2, Q, hQ, S, zeta, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isSubordinator_comp_fst hSub1 hMeasS1
  · exact indep_snd_comp_fst
  · intro x
    have hEq : {p : Omega2 | (x : WithTop NNReal) < zeta p} =
        (Set.univ : Set Omega1) ×ˢ {z : WithTop NNReal | (x : WithTop NNReal) < z} := by
      ext ⟨a, b⟩; exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
    rw [hEq, Measure.prod_prod, measure_univ, one_mul, killingMeasure_Ioi hRoot.1 x,
      ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))]
  · intro hphi0
    have hEq : {p : Omega2 | zeta p = ⊤} =
        (Set.univ : Set Omega1) ×ˢ {z : WithTop NNReal | z = ⊤} := by
      ext ⟨a, b⟩; exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
    rw [hEq, Measure.prod_prod, measure_univ, one_mul, killingMeasure_top_of_eq_zero hphi0]
    simp
  · intro hphipos
    have hEq : {p : Omega2 | zeta p != ⊤} =
        (Set.univ : Set Omega1) ×ˢ {z : WithTop NNReal | z != ⊤} := by
      ext ⟨a, b⟩; exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
    rw [hEq, Measure.prod_prod, measure_univ, one_mul, killingMeasure_ne_top_of_pos hphipos]
    simp
  · -- Path-space law equality via π-λ theorem on finite-dimensional rectangles
    let τP : Omega → NNReal → WithTop NNReal :=
      fun ω x => firstHittingTime L.X (Set.Ioi (x : ℝ)) ω
    let τ1 : Omega1 → NNReal → WithTop NNReal :=
      fun ω x => firstHittingTime L1.X (Set.Ioi (x : ℝ)) ω
    let σ1 : Omega1 → NNReal → WithTop NNReal :=
      fun ω x => (Real.toNNReal (S1 x ω) : WithTop NNReal)
    let τQ : Omega2 → NNReal → WithTop NNReal :=
      fun p x => if (x : WithTop NNReal) < p.2
        then (Real.toNNReal (S1 x p.1) : WithTop NNReal) else ⊤
    have hMeasτP : Measurable τP :=
      measurable_pi_lambda _ (fun x => measurable_firstHittingTime_Ioi L x)
    have hMeasτ1 : Measurable τ1 :=
      measurable_pi_lambda _ (fun x => measurable_firstHittingTime_Ioi L1 x)
    have hMeasσ1 : Measurable σ1 :=
      measurable_pi_lambda _ (fun x => WithTop.measurable_coe.comp (hMeasS1 x).real_toNNReal)
    have hMeasτQ : Measurable τQ :=
      measurable_pi_lambda _ (fun x =>
        Measurable.ite (measurableSet_lt measurable_const measurable_snd)
          (WithTop.measurable_coe.comp ((hMeasS1 x).comp measurable_fst).real_toNNReal)
          measurable_const)
    have : IsProbabilityMeasure (Measure.map τP P) :=
      Measure.isProbabilityMeasure_map hMeasτP.aemeasurable
    have : IsProbabilityMeasure (Measure.map τQ Q) :=
      Measure.isProbabilityMeasure_map hMeasτQ.aemeasurable
    have hQ1_eq : ∀ (U : Finset NNReal) (B : NNReal → Set (WithTop NNReal)),
        (∀ u ∈ U, MeasurableSet (B u)) →
        Q1 (⋂ u ∈ U, {ω : Omega1 | σ1 ω u ∈ B u}) =
        Q1 (⋂ u ∈ U, {ω : Omega1 | τ1 ω u ∈ B u}) := by
      intro U B hB
      let E : Set (NNReal → WithTop NNReal) := ⋂ u ∈ U, {f | f u ∈ B u}
      have hME : MeasurableSet E :=
        Finset.measurableSet_biInter U fun u hu => (measurable_pi_apply u) (hB u hu)
      have h := congrArg (fun m => m E) hLaw1
      rw [Measure.map_apply hMeasσ1 hME, Measure.map_apply hMeasτ1 hME] at h
      simpa [E, Set.preimage_iInter] using h
    refine measure_eq_on_pi_rectangles ?_
    intro U B hB hPure
    classical
    let E : Set (NNReal → WithTop NNReal) := ⋂ u ∈ U, {f | f u ∈ B u}
    have hME : MeasurableSet E :=
      Finset.measurableSet_biInter U fun u hu => (measurable_pi_apply u) (hB u hu)
    rw [Measure.map_apply hMeasτP hME, Measure.map_apply hMeasτQ hME]
    let Ufin : Finset NNReal := U.filter (fun u => ⊤ ∉ B u)
    let Utop : Finset NNReal := U.filter (fun u => B u = {⊤})
    have hUpart : ∀ u ∈ U, u ∈ Ufin ∨ u ∈ Utop := by
      intro u hu
      rcases hPure u hu with h1 | h2
      · left; exact Finset.mem_filter.mpr ⟨hu, h1⟩
      · right; exact Finset.mem_filter.mpr ⟨hu, h2⟩
    by_cases hBad : ∃ u ∈ Ufin, ∃ v ∈ Utop, v ≤ u
    · rcases hBad with ⟨u, hu, v, hv, hvu⟩
      have huU : u ∈ U := (Finset.mem_filter.mp hu).1
      have huNotTop : ⊤ ∉ B u := (Finset.mem_filter.mp hu).2
      have hvU : v ∈ U := (Finset.mem_filter.mp hv).1
      have hvTop : B v = {⊤} := (Finset.mem_filter.mp hv).2
      have hEmptyP : τP ⁻¹' E = ∅ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false, E, Set.mem_iInter,
          Set.mem_ofPred_eq]
        intro h
        have h1 : τP ω u ∈ B u := h u huU
        have h2 : τP ω v = ⊤ := by
          have := h v hvU; rwa [hvTop, Set.mem_singleton_iff] at this
        have hle : τP ω v ≤ τP ω u := firstHittingTime_Ioi_mono L.X ω hvu
        rw [h2, top_le_iff] at hle
        rw [hle] at h1
        exact huNotTop h1
      have hEmptyQ : τQ ⁻¹' E = ∅ := by
        ext p
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false, E, Set.mem_iInter,
          Set.mem_ofPred_eq]
        intro h
        have h1 : τQ p u ∈ B u := h u huU
        have h2 : τQ p v = ⊤ := by
          have := h v hvU; rwa [hvTop, Set.mem_singleton_iff] at this
        by_cases hlt : (u : WithTop NNReal) < p.2
        · have hvlt : (v : WithTop NNReal) < p.2 := lt_of_le_of_lt (WithTop.coe_le_coe.mpr hvu) hlt
          simp only [τQ, hvlt, ↓reduceIte] at h2
          exact WithTop.coe_ne_top h2
        · simp only [τQ, hlt, ↓reduceIte] at h1
          exact huNotTop h1
      rw [hEmptyP, hEmptyQ, measure_empty, measure_empty]
    · push Not at hBad
      by_cases hTopEmpty : Utop = ∅
      · by_cases hFinEmpty : Ufin = ∅
        · have hUEmpty : U = ∅ := by
            ext u
            simp only [Finset.notMem_empty, iff_false]
            intro hu
            rcases hUpart u hu with h1 | h2
            · simp [hFinEmpty] at h1
            · simp [hTopEmpty] at h2
          simp [E, hUEmpty, measure_univ]
        · have hFinNE : Ufin.Nonempty := Finset.nonempty_iff_ne_empty.mpr hFinEmpty
          let xmax : NNReal := Ufin.max' hFinNE
          have hxmax_mem : xmax ∈ Ufin := Finset.max'_mem Ufin hFinNE
          have hxmax_U : xmax ∈ U := (Finset.mem_filter.mp hxmax_mem).1
          have hxmax_notTop : ⊤ ∉ B xmax := (Finset.mem_filter.mp hxmax_mem).2
          have hU_eq_Ufin : U = Ufin := by
            ext u
            constructor
            · intro hu
              rcases hUpart u hu with h1 | h2
              · exact h1
              · simp [hTopEmpty] at h2
            · intro hu; exact (Finset.mem_filter.mp hu).1
          have hPreP : τP ⁻¹' E =
              {ω : Omega | firstHittingTime L.X (Set.Ioi (xmax : ℝ)) ω ≠ ⊤} ∩
                ⋂ u ∈ U, {ω : Omega | firstHittingTime L.X (Set.Ioi (u : ℝ)) ω ∈ B u} := by
            ext ω
            simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, E, τP]
            constructor
            · intro h
              refine ⟨?_, h⟩
              intro htop
              have := h xmax hxmax_U
              rw [htop] at this
              exact hxmax_notTop this
            · exact fun h => h.2
          have hPreQ : τQ ⁻¹' E =
              (⋂ u ∈ U, {ω : Omega1 | σ1 ω u ∈ B u}) ×ˢ
                {z : WithTop NNReal | (xmax : WithTop NNReal) < z} := by
            ext ⟨a, b⟩
            change τQ (a, b) ∈ E ↔
              a ∈ (⋂ u ∈ U, {ω : Omega1 | σ1 ω u ∈ B u}) ∧
                (xmax : WithTop NNReal) < b
            simp only [Set.mem_iInter, Set.mem_ofPred_eq, E, τQ, σ1]
            constructor
            · intro h
              have hlt_max : (xmax : WithTop NNReal) < b := by
                by_contra hle
                have hxm := h xmax hxmax_U
                simp only [hle, ↓reduceIte] at hxm
                exact hxmax_notTop hxm
              refine ⟨fun u hu => ?_, hlt_max⟩
              have hu_le : u ≤ xmax := Finset.le_max' Ufin u (hU_eq_Ufin ▸ hu)
              have hu_lt : (u : WithTop NNReal) < b :=
                lt_of_le_of_lt (WithTop.coe_le_coe.mpr hu_le) hlt_max
              have hmu := h u hu
              simpa only [hu_lt, ↓reduceIte] using hmu
            · rintro ⟨h1, hlt_max⟩ u hu
              have hu_le : u ≤ xmax := Finset.le_max' Ufin u (hU_eq_Ufin ▸ hu)
              have hu_lt : (u : WithTop NNReal) < b :=
                lt_of_le_of_lt (WithTop.coe_le_coe.mpr hu_le) hlt_max
              simpa only [hu_lt, ↓reduceIte] using h1 u hu
          rw [hPreP, hPreQ, Measure.prod_prod, mul_comm, killingMeasure_Ioi hRoot.1 xmax,
            hQ1_eq U B hB]
          exact hTilt xmax U (fun u hu => Finset.le_max' Ufin u (hU_eq_Ufin ▸ hu)) B hB
      · have hTopNE : Utop.Nonempty := Finset.nonempty_iff_ne_empty.mpr hTopEmpty
        let ymin : NNReal := Utop.min' hTopNE
        have hymin_mem : ymin ∈ Utop := Finset.min'_mem Utop hTopNE
        have hymin_U : ymin ∈ U := (Finset.mem_filter.mp hymin_mem).1
        have hymin_top : B ymin = {⊤} := (Finset.mem_filter.mp hymin_mem).2
        by_cases hFinEmpty : Ufin = ∅
        · have hU_eq_Utop : U = Utop := by
            ext u
            constructor
            · intro hu
              rcases hUpart u hu with h1 | h2
              · simp [hFinEmpty] at h1
              · exact h2
            · intro hu; exact (Finset.mem_filter.mp hu).1
          have hPreP : τP ⁻¹' E = {ω : Omega | τP ω ymin = ⊤} := by
            ext ω
            simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq, E]
            constructor
            · intro h
              have := h ymin hymin_U
              rwa [hymin_top, Set.mem_singleton_iff] at this
            · intro h u hu
              have huUtop : u ∈ Utop := hU_eq_Utop ▸ hu
              have huTop : B u = {⊤} := (Finset.mem_filter.mp huUtop).2
              rw [huTop, Set.mem_singleton_iff]
              have hle : ymin ≤ u := Finset.min'_le Utop u huUtop
              have hmono : τP ω ymin ≤ τP ω u := firstHittingTime_Ioi_mono L.X ω hle
              rw [h, top_le_iff] at hmono
              exact hmono
          have hPreQ : τQ ⁻¹' E =
              (Set.univ : Set Omega1) ×ˢ {z : WithTop NNReal | ¬ ((ymin : WithTop NNReal) < z)} := by
            ext ⟨a, b⟩
            change τQ (a, b) ∈ E ↔ True ∧ ¬ ((ymin : WithTop NNReal) < b)
            simp only [true_and, Set.mem_iInter, Set.mem_ofPred_eq, E, τQ]
            constructor
            · intro h hlt
              have hym := h ymin hymin_U
              rw [hymin_top, Set.mem_singleton_iff] at hym
              simp only [hlt, ↓reduceIte] at hym
              exact WithTop.coe_ne_top hym
            · intro hnot u hu
              have huUtop : u ∈ Utop := hU_eq_Utop ▸ hu
              have huTop : B u = {⊤} := (Finset.mem_filter.mp huUtop).2
              rw [huTop, Set.mem_singleton_iff]
              have hle : ymin ≤ u := Finset.min'_le Utop u huUtop
              have hnot_u : ¬ ((u : WithTop NNReal) < b) := fun hlt =>
                hnot (lt_of_le_of_lt (WithTop.coe_le_coe.mpr hle) hlt)
              simp only [hnot_u, ↓reduceIte]
          have hTilt_empty := hTilt ymin ∅ (by simp) B (by simp)
          simp only [Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ, Set.inter_univ,
            measure_univ, mul_one] at hTilt_empty
          have hMeasNeTop : MeasurableSet {ω : Omega | τP ω ymin ≠ ⊤} :=
            (measurable_firstHittingTime_Ioi L ymin) (MeasurableSet.singleton ⊤).compl
          have hP_top : P {ω : Omega | τP ω ymin = ⊤} =
              1 - ENNReal.ofReal (Real.exp (-phi * (ymin : ℝ))) := by
            have hCompl : {ω : Omega | τP ω ymin = ⊤} = {ω : Omega | τP ω ymin ≠ ⊤}ᶜ := by
              ext ω; simp
            rw [hCompl, measure_compl hMeasNeTop (measure_ne_top P _), measure_univ, hTilt_empty]
          have hMeasLtZ : MeasurableSet {z : WithTop NNReal | (ymin : WithTop NNReal) < z} :=
            measurableSet_lt measurable_const measurable_id
          have hZ_notlt : μZ {z : WithTop NNReal | ¬ ((ymin : WithTop NNReal) < z)} =
              1 - ENNReal.ofReal (Real.exp (-phi * (ymin : ℝ))) := by
            have hCompl : {z : WithTop NNReal | ¬ ((ymin : WithTop NNReal) < z)} =
                {z : WithTop NNReal | (ymin : WithTop NNReal) < z}ᶜ := by
              ext z; simp
            rw [hCompl, measure_compl hMeasLtZ (measure_ne_top μZ _), measure_univ,
              killingMeasure_Ioi hRoot.1 ymin]
          rw [hPreP, hPreQ, Measure.prod_prod, measure_univ, one_mul, hP_top, hZ_notlt]
        · have hFinNE : Ufin.Nonempty := Finset.nonempty_iff_ne_empty.mpr hFinEmpty
          let xmax : NNReal := Ufin.max' hFinNE
          have hxmax_mem : xmax ∈ Ufin := Finset.max'_mem Ufin hFinNE
          have hxmax_notTop : ⊤ ∉ B xmax := (Finset.mem_filter.mp hxmax_mem).2
          have hxy : xmax < ymin := hBad xmax hxmax_mem ymin hymin_mem
          have hPreP_eq : τP ⁻¹' E =
              (⋂ u ∈ Ufin, {ω : Omega | τP ω u ∈ B u}) \
                ({ω : Omega | τP ω ymin ≠ ⊤} ∩ ⋂ u ∈ Ufin, {ω : Omega | τP ω u ∈ B u}) := by
            ext ω
            simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_iInter,
              Set.mem_ofPred_eq, E]
            constructor
            · intro h
              refine ⟨fun u hu => h u (Finset.mem_filter.mp hu).1, ?_⟩
              rintro ⟨hne, _⟩
              have := h ymin hymin_U
              rw [hymin_top, Set.mem_singleton_iff] at this
              exact hne this
            · rintro ⟨hfin, hnot⟩ u hu
              rcases hUpart u hu with hu1 | hu2
              · exact hfin u hu1
              · have huTop : B u = {⊤} := (Finset.mem_filter.mp hu2).2
                rw [huTop, Set.mem_singleton_iff]
                have hymin_eq : τP ω ymin = ⊤ := by
                  by_contra hne; exact hnot ⟨hne, hfin⟩
                have hle : ymin ≤ u := Finset.min'_le Utop u hu2
                have hmono : τP ω ymin ≤ τP ω u := firstHittingTime_Ioi_mono L.X ω hle
                rw [hymin_eq, top_le_iff] at hmono
                exact hmono
          have hSubP : ({ω : Omega | τP ω ymin ≠ ⊤} ∩ ⋂ u ∈ Ufin, {ω : Omega | τP ω u ∈ B u}) ⊆
              (⋂ u ∈ Ufin, {ω : Omega | τP ω u ∈ B u}) := Set.inter_subset_right
          have hMeasSubP : MeasurableSet
              ({ω : Omega | τP ω ymin ≠ ⊤} ∩ ⋂ u ∈ Ufin, {ω : Omega | τP ω u ∈ B u}) :=
            ((measurable_firstHittingTime_Ioi L ymin) (MeasurableSet.singleton ⊤).compl).inter
              (Finset.measurableSet_biInter Ufin fun u hu =>
                (measurable_firstHittingTime_Ioi L u) (hB u (Finset.mem_filter.mp hu).1))
          have hP_fin_eq : (⋂ u ∈ Ufin, {ω : Omega | τP ω u ∈ B u}) =
              {ω : Omega | τP ω xmax ≠ ⊤} ∩ ⋂ u ∈ Ufin, {ω : Omega | τP ω u ∈ B u} := by
            ext ω
            simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
            constructor
            · intro h
              refine ⟨?_, h⟩
              intro htop
              have := h xmax hxmax_mem
              rw [htop] at this
              exact hxmax_notTop this
            · exact fun h => h.2
          have hPreQ_eq : τQ ⁻¹' E =
              (⋂ u ∈ Ufin, {ω : Omega1 | σ1 ω u ∈ B u}) ×ˢ
                ({z : WithTop NNReal | (xmax : WithTop NNReal) < z} \
                  {z : WithTop NNReal | (ymin : WithTop NNReal) < z}) := by
            ext ⟨a, b⟩
            change τQ (a, b) ∈ E ↔
              a ∈ (⋂ u ∈ Ufin, {ω : Omega1 | σ1 ω u ∈ B u}) ∧
                ((xmax : WithTop NNReal) < b ∧ ¬ ((ymin : WithTop NNReal) < b))
            simp only [Set.mem_iInter, Set.mem_ofPred_eq, E, τQ, σ1]
            constructor
            · intro h
              have hlt_max : (xmax : WithTop NNReal) < b := by
                by_contra hle
                have hxm := h xmax (Finset.mem_filter.mp hxmax_mem).1
                simp only [hle, ↓reduceIte] at hxm
                exact hxmax_notTop hxm
              have hnot_min : ¬ ((ymin : WithTop NNReal) < b) := by
                intro hlt
                have hym := h ymin hymin_U
                rw [hymin_top, Set.mem_singleton_iff] at hym
                simp only [hlt, ↓reduceIte] at hym
                exact WithTop.coe_ne_top hym
              refine ⟨fun u hu => ?_, hlt_max, hnot_min⟩
              have hu_le : u ≤ xmax := Finset.le_max' Ufin u hu
              have hu_lt : (u : WithTop NNReal) < b :=
                lt_of_le_of_lt (WithTop.coe_le_coe.mpr hu_le) hlt_max
              have hmu := h u (Finset.mem_filter.mp hu).1
              simpa only [hu_lt, ↓reduceIte] using hmu
            · rintro ⟨h1, hlt_max, hnot_min⟩ u hu
              rcases hUpart u hu with hu1 | hu2
              · have hu_le : u ≤ xmax := Finset.le_max' Ufin u hu1
                have hu_lt : (u : WithTop NNReal) < b :=
                  lt_of_le_of_lt (WithTop.coe_le_coe.mpr hu_le) hlt_max
                simpa only [hu_lt, ↓reduceIte] using h1 u hu1
              · have huTop : B u = {⊤} := (Finset.mem_filter.mp hu2).2
                rw [huTop, Set.mem_singleton_iff]
                have hle : ymin ≤ u := Finset.min'_le Utop u hu2
                have hnot_u : ¬ ((u : WithTop NNReal) < b) := fun hlt =>
                  hnot_min (lt_of_le_of_lt (WithTop.coe_le_coe.mpr hle) hlt)
                simp only [hnot_u, ↓reduceIte]
          have hSubZ : {z : WithTop NNReal | (ymin : WithTop NNReal) < z} ⊆
              {z : WithTop NNReal | (xmax : WithTop NNReal) < z} := fun z hz =>
            lt_trans (WithTop.coe_lt_coe.mpr hxy) hz
          have hMeasZmin : MeasurableSet {z : WithTop NNReal | (ymin : WithTop NNReal) < z} :=
            measurableSet_lt measurable_const measurable_id
          have hBfin : ∀ u ∈ Ufin, MeasurableSet (B u) :=
            fun u hu => hB u (Finset.mem_filter.mp hu).1
          have hP1 : P (⋂ u ∈ Ufin, {ω : Omega | τP ω u ∈ B u}) =
              ENNReal.ofReal (Real.exp (-phi * (xmax : ℝ))) *
                Q1 (⋂ u ∈ Ufin, {ω : Omega1 | τ1 ω u ∈ B u}) := by
            rw [hP_fin_eq]
            exact hTilt xmax Ufin (fun u hu => Finset.le_max' Ufin u hu) B hBfin
          have hP2 : P ({ω : Omega | τP ω ymin ≠ ⊤} ∩ ⋂ u ∈ Ufin, {ω : Omega | τP ω u ∈ B u}) =
              ENNReal.ofReal (Real.exp (-phi * (ymin : ℝ))) *
                Q1 (⋂ u ∈ Ufin, {ω : Omega1 | τ1 ω u ∈ B u}) :=
            hTilt ymin Ufin (fun u hu => le_of_lt (lt_of_le_of_lt (Finset.le_max' Ufin u hu) hxy)) B hBfin
          rw [hPreP_eq, measure_sdiff hSubP hMeasSubP.nullMeasurableSet (measure_ne_top P _),
            hP1, hP2,
            hPreQ_eq, Measure.prod_prod,
            measure_sdiff hSubZ hMeasZmin.nullMeasurableSet (measure_ne_top μZ _),
            killingMeasure_Ioi hRoot.1 xmax, killingMeasure_Ioi hRoot.1 ymin,
            hQ1_eq Ufin B hBfin, ENNReal.mul_sub (fun _ _ => measure_ne_top Q1 _),
            mul_comm (Q1 _), mul_comm (Q1 _)]
