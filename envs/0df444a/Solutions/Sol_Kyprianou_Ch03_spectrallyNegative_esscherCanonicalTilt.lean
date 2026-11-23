-- Prove2me | solution 1 for Kyprianou.Ch03.spectrallyNegative_esscherCanonicalTilt
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T19:59:32.876547+00:00
-- url     : https://prove2.me/submissions/cdf39904-ecd6-42aa-8352-f7b8ed7ccd9c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Theorems.Thm_Kyprianou_Ch03_exponentRegularity_infiniteLimitNonSubordinator
import Theorems.Thm_Kyprianou_Ch03_firstPassageZero_consequence1
import Theorems.Thm_Kyprianou_Ch03_spectrallyNegative_canonicalEsscherUncompleted

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03.EsscherCanonicalTiltProof

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

private lemma measurableSet_firstHittingTime_lt_F
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x a t : NNReal) (hat : a ≤ t) :
    MeasurableSet[F t]
      {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (a : WithTop NNReal)} := by
  have hEq :
      {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (a : WithTop NNReal)} =
        ⋃ q : {q : ℚ // 0 < q ∧ (q : ℝ) < (a : ℝ)},
          {ω : Omega | (x : ℝ) < L.X (Real.toNNReal (q.1 : ℝ)) ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Subtype.exists]
    simpa [and_assoc] using firstHittingTime_Ioi_lt_coe_iff L x a ω
  rw [hEq]
  refine MeasurableSet.iUnion fun q => ?_
  have hq_le_t : Real.toNNReal (q.1 : ℝ) ≤ t := by
    have hq_le_a : Real.toNNReal (q.1 : ℝ) ≤ a := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (le_of_lt (by exact_mod_cast q.2.1))]
      exact le_of_lt q.2.2
    exact le_trans hq_le_a hat
  have hmeasX : Measurable[F t] (L.X (Real.toNNReal (q.1 : ℝ))) :=
    (L.adapted (Real.toNNReal (q.1 : ℝ))).mono (F.mono hq_le_t) le_rfl
  exact @measurableSet_lt _ _ _ _ _ (F t) _ _ _ _ _ measurable_const hmeasX

private lemma measurable_of_Iio_on {Ω : Type} (m : MeasurableSpace Ω)
    {f : Ω → WithTop NNReal} (h : ∀ b : WithTop NNReal, MeasurableSet[m] (f ⁻¹' Set.Iio b)) :
    Measurable[m] f :=
  measurable_of_Iio h

private lemma measurable_min_firstHittingTime_F
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x t : NNReal) :
    Measurable[F t]
      (fun ω : Omega => min (firstHittingTime L.X (Set.Ioi (x : ℝ)) ω) (t : WithTop NNReal)) := by
  refine measurable_of_Iio_on (F t) ?_
  intro b
  by_cases hbt : b ≤ (t : WithTop NNReal)
  · cases b with
    | top =>
      exfalso
      exact not_le.mpr (WithTop.coe_lt_top t) hbt
    | coe a =>
      have hat : a ≤ t := WithTop.coe_le_coe.mp hbt
      have hEq :
          (fun ω : Omega => min (firstHittingTime L.X (Set.Ioi (x : ℝ)) ω) (t : WithTop NNReal)) ⁻¹'
              Set.Iio (a : WithTop NNReal) =
            {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (a : WithTop NNReal)} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_ofPred_eq, min_lt_iff]
        have hnot : ¬ ((t : WithTop NNReal) < (a : WithTop NNReal)) :=
          not_lt.mpr (WithTop.coe_le_coe.mpr hat)
        exact ⟨fun h => h.elim id (fun ht => absurd ht hnot), Or.inl⟩
      rw [hEq]
      exact measurableSet_firstHittingTime_lt_F L x a t hat
  · have htb : (t : WithTop NNReal) < b := not_le.mp hbt
    have hEq :
        (fun ω : Omega => min (firstHittingTime L.X (Set.Ioi (x : ℝ)) ω) (t : WithTop NNReal)) ⁻¹'
            Set.Iio b = Set.univ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_univ, iff_true, min_lt_iff]
      exact Or.inr htb
    rw [hEq]
    exact MeasurableSet.univ

private lemma measurable_firstHittingTime_Ioi
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) (x : NNReal) :
    Measurable (fun ω : Omega => firstHittingTime L.X (Set.Ioi (x : ℝ)) ω) := by
  have hlt : ∀ a : NNReal,
      MeasurableSet {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (a : WithTop NNReal)} :=
    fun a => F.le a _ (measurableSet_firstHittingTime_lt_F L x a a le_rfl)
  refine measurable_of_Iio fun b => ?_
  cases b with
  | top =>
    change MeasurableSet {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (⊤ : WithTop NNReal)}
    have hEq :
        {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (⊤ : WithTop NNReal)} =
          ⋃ n : ℕ, {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω <
            ((n : NNReal) : WithTop NNReal)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro h
        rcases WithTop.ne_top_iff_exists.mp (WithTop.lt_top_iff_ne_top.mp h) with ⟨t, ht⟩
        rw [← ht]
        rcases exists_nat_gt (t : ℝ) with ⟨n, hn⟩
        exact ⟨n, WithTop.coe_lt_coe.mpr (by exact_mod_cast hn)⟩
      · rintro ⟨n, hn⟩
        exact lt_trans hn (WithTop.coe_lt_top _)
    rw [hEq]
    exact MeasurableSet.iUnion fun n => hlt (n : NNReal)
  | coe a => exact hlt a

private lemma measurableSet_cyl_inter_bin_F
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x : NNReal) (U : Finset NNReal) (hU : ∀ u ∈ U, u ≤ x)
    (B : NNReal → Set (WithTop NNReal)) (hB : ∀ u ∈ U, MeasurableSet (B u))
    (a t : NNReal) :
    MeasurableSet[F t]
      ((⋂ u ∈ U, {ω : Omega | firstHittingTime L.X (Set.Ioi (u : ℝ)) ω ∈ B u}) ∩
        {ω : Omega | (a : WithTop NNReal) ≤ firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ∧
          firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (t : WithTop NNReal)}) := by
  let gx : Omega → WithTop NNReal :=
    fun ω => min (firstHittingTime L.X (Set.Ioi (x : ℝ)) ω) (t : WithTop NNReal)
  have hgx : Measurable[F t] gx := measurable_min_firstHittingTime_F L x t
  let Sbin : Set (WithTop NNReal) := Set.Ico (a : WithTop NNReal) (t : WithTop NNReal)
  have hSbin : MeasurableSet Sbin := measurableSet_Ico
  have hBinEq :
      {ω : Omega | (a : WithTop NNReal) ≤ firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ∧
        firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (t : WithTop NNReal)} = gx ⁻¹' Sbin := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Sbin, Set.mem_Ico, gx]
    constructor
    · rintro ⟨h1, h2⟩
      rw [min_eq_left (le_of_lt h2)]
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have hlt : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (t : WithTop NNReal) := by
        rcases min_lt_iff.mp h2 with h | h
        · exact h
        · exact absurd h (lt_irrefl _)
      rw [min_eq_left (le_of_lt hlt)] at h1
      exact ⟨h1, hlt⟩
  have hEq :
      ((⋂ u ∈ U, {ω : Omega | firstHittingTime L.X (Set.Ioi (u : ℝ)) ω ∈ B u}) ∩
        {ω : Omega | (a : WithTop NNReal) ≤ firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ∧
          firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (t : WithTop NNReal)}) =
      (gx ⁻¹' Sbin) ∩
        ⋂ u ∈ U, (fun ω => min (firstHittingTime L.X (Set.Ioi (u : ℝ)) ω) (t : WithTop NNReal)) ⁻¹'
          (B u ∩ Set.Iio (t : WithTop NNReal)) := by
    ext ω
    rw [← hBinEq]
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iio]
    constructor
    · rintro ⟨hA, hbin⟩
      refine ⟨hbin, fun u hu => ?_⟩
      have hle : firstHittingTime L.X (Set.Ioi (u : ℝ)) ω ≤
          firstHittingTime L.X (Set.Ioi (x : ℝ)) ω :=
        firstHittingTime_Ioi_mono L.X ω (hU u hu)
      have hult : firstHittingTime L.X (Set.Ioi (u : ℝ)) ω < (t : WithTop NNReal) :=
        lt_of_le_of_lt hle hbin.2
      rw [min_eq_left (le_of_lt hult)]
      exact ⟨hA u hu, hult⟩
    · rintro ⟨hbin, hA⟩
      refine ⟨fun u hu => ?_, hbin⟩
      have hle : firstHittingTime L.X (Set.Ioi (u : ℝ)) ω ≤
          firstHittingTime L.X (Set.Ioi (x : ℝ)) ω :=
        firstHittingTime_Ioi_mono L.X ω (hU u hu)
      have hult : firstHittingTime L.X (Set.Ioi (u : ℝ)) ω < (t : WithTop NNReal) :=
        lt_of_le_of_lt hle hbin.2
      have hmem := (hA u hu).1
      rwa [min_eq_left (le_of_lt hult)] at hmem
  rw [hEq]
  refine (hgx hSbin).inter (Finset.measurableSet_biInter U fun u hu => ?_)
  exact (measurable_min_firstHittingTime_F L u t) ((hB u hu).inter measurableSet_Iio)

private lemma X_at_firstHittingTime_eq
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x t : NNReal) (ω : Omega)
    (hHit : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω = (t : WithTop NNReal)) :
    L.X t ω = (x : ℝ) := by
  by_cases ht0 : t = 0
  · subst ht0
    rw [L.X_zero ω]
    by_contra hne
    have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_le_of_ne x.coe_nonneg hne
    have hrc := L.rightCont ω 0
    have hmem : Set.Iio (x : ℝ) ∈ 𝓝 (L.X 0 ω) := by
      rw [L.X_zero ω]; exact isOpen_Iio.mem_nhds hxpos
    have hev : ∀ᶠ s in 𝓝[Set.Ici (0 : NNReal)] 0, L.X s ω < (x : ℝ) := hrc.eventually hmem
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    rcases hev with ⟨δ, hδpos, hδ⟩
    have hge : (Real.toNNReal (δ / 2) : WithTop NNReal) ≤
        firstHittingTime L.X (Set.Ioi (x : ℝ)) ω := by
      unfold firstHittingTime
      refine le_sInf ?_
      rintro _ ⟨s, ⟨hspos, hsx⟩, rfl⟩
      refine WithTop.coe_le_coe.mpr ?_
      by_contra hslt
      push Not at hslt
      have hs_dist : dist s 0 < δ := by
        rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg s.coe_nonneg]
        have : (s : ℝ) < (Real.toNNReal (δ / 2) : ℝ) := by exact_mod_cast hslt
        rw [Real.coe_toNNReal _ (by linarith)] at this
        linarith
      have hlt_x : L.X s ω < (x : ℝ) := hδ hs_dist (bot_le : (0 : NNReal) ≤ s)
      exact not_lt.mpr (le_of_lt hlt_x) hsx
    rw [hHit, WithTop.coe_le_coe] at hge
    have hpos : (0 : NNReal) < Real.toNNReal (δ / 2) := Real.toNNReal_pos.mpr (by linarith)
    exact not_lt.mpr hge hpos
  · have htpos : (0 : NNReal) < t := pos_iff_ne_zero.mpr ht0
    apply le_antisymm
    · rcases L.leftLim ω t htpos with ⟨l, hl⟩
      have hle_l : L.X t ω ≤ l := L.noPosJumps ω t l htpos hl
      have hNeBot : (𝓝[<] t).NeBot := by
        rw [Filter.neBot_iff]
        intro hbot
        have hempty : (∅ : Set NNReal) ∈ 𝓝[<] t := by rw [hbot]; trivial
        rw [Metric.mem_nhdsWithin_iff] at hempty
        rcases hempty with ⟨δ, hδpos, hδ⟩
        let s : NNReal := Real.toNNReal (max ((t : ℝ) / 2) ((t : ℝ) - δ / 2))
        have ht0r : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htpos
        have hs_nonneg : 0 ≤ max ((t : ℝ) / 2) ((t : ℝ) - δ / 2) :=
          le_trans (by linarith) (le_max_left _ _)
        have hs_coe : (s : ℝ) = max ((t : ℝ) / 2) ((t : ℝ) - δ / 2) :=
          Real.coe_toNNReal _ hs_nonneg
        have hs_lt : s < t := by
          rw [← NNReal.coe_lt_coe, hs_coe]
          exact max_lt (by linarith) (by linarith)
        have hs_ball : s ∈ Metric.ball t δ := by
          rw [Metric.mem_ball, NNReal.dist_eq, abs_of_nonpos (sub_nonpos.mpr (le_of_lt (by exact_mod_cast hs_lt)))]
          have : (t : ℝ) - δ / 2 ≤ (s : ℝ) := by rw [hs_coe]; exact le_max_right _ _
          linarith
        exact hδ ⟨hs_ball, hs_lt⟩
      have hl_le_x : l ≤ (x : ℝ) := by
        refine le_of_tendsto hl ?_
        have hIoo : Set.Ioo (0 : NNReal) t ∈ 𝓝[<] t := Ioo_mem_nhdsLT htpos
        refine Filter.mem_of_superset hIoo fun s hs => ?_
        by_contra hsgt
        have hsgt' : (x : ℝ) < L.X s ω := not_le.mp hsgt
        have hle_s : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≤ (s : WithTop NNReal) := by
          unfold firstHittingTime
          exact sInf_le ⟨s, ⟨hs.1, hsgt'⟩, rfl⟩
        rw [hHit, WithTop.coe_le_coe] at hle_s
        exact not_lt.mpr hle_s hs.2
      exact le_trans hle_l hl_le_x
    · by_contra hlt
      push Not at hlt
      have hrc := L.rightCont ω t
      have hmem : Set.Iio (x : ℝ) ∈ 𝓝 (L.X t ω) := isOpen_Iio.mem_nhds hlt
      have hev : ∀ᶠ s in 𝓝[Set.Ici t] t, L.X s ω < (x : ℝ) := hrc.eventually hmem
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
      rcases hev with ⟨δ, hδpos, hδ⟩
      let u : NNReal := t + Real.toNNReal (δ / 2)
      have htu : (t : WithTop NNReal) < (u : WithTop NNReal) := by
        refine WithTop.coe_lt_coe.mpr ?_
        exact lt_add_of_pos_right t (Real.toNNReal_pos.mpr (by linarith))
      rw [← hHit] at htu
      unfold firstHittingTime at htu
      rcases sInf_lt_iff.mp htu with ⟨_, ⟨s, ⟨hspos, hsx⟩, rfl⟩, hsu⟩
      have hts : t ≤ s := by
        have hle : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≤ (s : WithTop NNReal) := by
          unfold firstHittingTime
          exact sInf_le ⟨s, ⟨hspos, hsx⟩, rfl⟩
        rw [hHit, WithTop.coe_le_coe] at hle
        exact hle
      have hsu' : s < u := WithTop.coe_lt_coe.mp hsu
      have hs_dist : dist s t < δ := by
        rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hts))]
        have : (s : ℝ) < (t : ℝ) + δ / 2 := by
          have hs_lt_u : (s : ℝ) < (u : ℝ) := by exact_mod_cast hsu'
          dsimp [u] at hs_lt_u
          rw [max_eq_left (by linarith)] at hs_lt_u
          exact hs_lt_u
        linarith
      exact not_lt.mpr (le_of_lt (hδ hs_dist hts)) hsx

private lemma fatou_stopping_bound
    {Omega1 : Type} [MeasurableSpace Omega1]
    {P1 Q1 : Measure Omega1} [IsProbabilityMeasure P1] [IsProbabilityMeasure Q1]
    {F1 : Filtration NNReal (inferInstance : MeasurableSpace Omega1)}
    (L0 : AvramDividend.Classical.SpectrallyNegativeLevy P1 F1)
    {phi : ℝ} (hphi : 0 ≤ phi) (hψ0 : L0.ψ phi = 0)
    (hEsscher : ∀ (t : NNReal) (A : Set Omega1),
      MeasurableSet[F1 t] A →
      Q1 A =
        ENNReal.ofReal
          (∫ ω, Set.indicator A
            (fun ω : Omega1 => esscherDensity L0.X phi (L0.ψ phi) t ω) ω ∂P1))
    (x : NNReal) (E : Set Omega1)
    (hE_filt : ∀ a t : NNReal,
      MeasurableSet[F1 t]
        (E ∩ {ω : Omega1 | (a : WithTop NNReal) ≤ firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ∧
          firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω < (t : WithTop NNReal)})) :
    ENNReal.ofReal (Real.exp (phi * (x : ℝ))) *
      P1 (E ∩ {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) ≤ Q1 E := by
  let τ : Omega1 → WithTop NNReal := fun ω => firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω
  have hBoundN : ∀ N : ℕ,
      ENNReal.ofReal (Real.exp (phi * (x : ℝ))) *
        P1 (E ∩ {ω : Omega1 | τ ω < ((N : NNReal) : WithTop NNReal)}) ≤ Q1 E := by
    intro N
    let a : ℕ → ℕ → NNReal := fun n k => (k : NNReal) / ((2 : NNReal) ^ n)
    let b : ℕ → ℕ → NNReal := fun n k => ((k + 1 : ℕ) : NNReal) / ((2 : NNReal) ^ n)
    let I : ℕ → ℕ → Set Omega1 := fun n k =>
      {ω : Omega1 | (a n k : WithTop NNReal) ≤ τ ω ∧ τ ω < (b n k : WithTop NNReal)}
    let fn : ℕ → Omega1 → ℝ≥0∞ := fun n ω =>
      ∑ k ∈ Finset.range (N * 2 ^ n),
        (E ∩ I n k).indicator
          (fun ω => ENNReal.ofReal (Real.exp (phi * L0.X (b n k) ω))) ω
    have hDisj : ∀ n : ℕ,
        Set.PairwiseDisjoint (Finset.range (N * 2 ^ n) : Set ℕ) (fun k => E ∩ I n k) := by
      intro n k1 _ k2 _ hne
      rw [Function.onFun, Set.disjoint_left]
      intro ω h1 h2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : b n k1 ≤ a n k2 := by
          dsimp [b, a]
          have hpow : (0 : NNReal) < (2 : NNReal) ^ n := pow_pos (by norm_num) n
          exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hlt) (le_of_lt hpow)
        exact not_lt.mpr (le_trans (WithTop.coe_le_coe.mpr hle) h2.2.1) h1.2.2
      · have hle : b n k2 ≤ a n k1 := by
          dsimp [b, a]
          have hpow : (0 : NNReal) < (2 : NNReal) ^ n := pow_pos (by norm_num) n
          exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hgt) (le_of_lt hpow)
        exact not_lt.mpr (le_trans (WithTop.coe_le_coe.mpr hle) h1.2.1) h2.2.2
    have hUnion : ∀ n : ℕ,
        (⋃ k ∈ Finset.range (N * 2 ^ n), E ∩ I n k) =
          E ∩ {ω : Omega1 | τ ω < ((N : NNReal) : WithTop NNReal)} := by
      intro n
      ext ω
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_range]
      constructor
      · rintro ⟨k, hk, hEω, _, hlt⟩
        refine ⟨hEω, lt_of_lt_of_le hlt (WithTop.coe_le_coe.mpr ?_)⟩
        dsimp [b]
        have hpow : (0 : NNReal) < (2 : NNReal) ^ n := pow_pos (by norm_num) n
        rw [div_le_iff₀ hpow]
        exact_mod_cast Nat.succ_le_of_lt hk
      · rintro ⟨hEω, hltN⟩
        rcases WithTop.ne_top_iff_exists.mp (WithTop.lt_top_iff_ne_top.mp
          (lt_trans hltN (WithTop.coe_lt_top _))) with ⟨t, ht⟩
        rw [← ht, WithTop.coe_lt_coe] at hltN
        let k : ℕ := Nat.floor ((t : ℝ) * (2 : ℝ) ^ n)
        have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
        have hk_lt : k < N * 2 ^ n := by
          rw [Nat.floor_lt (mul_nonneg t.coe_nonneg (le_of_lt hpow_pos))]
          have htN : (t : ℝ) < (N : ℝ) := by exact_mod_cast hltN
          have : (t : ℝ) * (2 : ℝ) ^ n < (N : ℝ) * (2 : ℝ) ^ n := mul_lt_mul_of_pos_right htN hpow_pos
          simpa [Nat.cast_mul, Nat.cast_pow] using this
        refine ⟨k, hk_lt, hEω, ?_, ?_⟩
        · rw [← ht, WithTop.coe_le_coe, ← NNReal.coe_le_coe]
          simp only [a, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
          rw [div_le_iff₀ hpow_pos]
          exact Nat.floor_le (mul_nonneg t.coe_nonneg (le_of_lt hpow_pos))
        · rw [← ht, WithTop.coe_lt_coe, ← NNReal.coe_lt_coe]
          simp only [b, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
          rw [lt_div_iff₀ hpow_pos]
          simpa [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one ((t : ℝ) * (2 : ℝ) ^ n)
    have hMeas_fn : ∀ n : ℕ, Measurable (fn n) := by
      intro n
      refine Finset.measurable_sum (Finset.range (N * 2 ^ n)) fun k _ => ?_
      have hMset : MeasurableSet (E ∩ I n k) := F1.le (b n k) _ (hE_filt (a n k) (b n k))
      have hMX : Measurable (L0.X (b n k)) := (L0.adapted (b n k)).mono (F1.le _) le_rfl
      exact (ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp (measurable_const.mul hMX)))).indicator hMset
    have hInt_fn : ∀ n : ℕ,
        ∫⁻ ω, fn n ω ∂P1 = Q1 (E ∩ {ω : Omega1 | τ ω < ((N : NNReal) : WithTop NNReal)}) := by
      intro n
      have hSum : ∫⁻ ω, fn n ω ∂P1 =
          ∑ k ∈ Finset.range (N * 2 ^ n),
            ∫⁻ ω, (E ∩ I n k).indicator
              (fun ω => ENNReal.ofReal (Real.exp (phi * L0.X (b n k) ω))) ω ∂P1 :=
        lintegral_finsetSum (Finset.range (N * 2 ^ n)) fun k _ => by
          have hMset : MeasurableSet (E ∩ I n k) := F1.le (b n k) _ (hE_filt (a n k) (b n k))
          have hMX : Measurable (L0.X (b n k)) := (L0.adapted (b n k)).mono (F1.le _) le_rfl
          exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hMX))).indicator hMset
      rw [hSum]
      have hTerm : ∀ k ∈ Finset.range (N * 2 ^ n),
          ∫⁻ ω, (E ∩ I n k).indicator
            (fun ω => ENNReal.ofReal (Real.exp (phi * L0.X (b n k) ω))) ω ∂P1 =
          Q1 (E ∩ I n k) := by
        intro k _
        have hMsetF : MeasurableSet[F1 (b n k)] (E ∩ I n k) := hE_filt (a n k) (b n k)
        have hMset : MeasurableSet (E ∩ I n k) := F1.le (b n k) _ hMsetF
        have hInt : Integrable
            ((E ∩ I n k).indicator (fun ω => Real.exp (phi * L0.X (b n k) ω))) P1 :=
          (L0.laplace (b n k) phi hphi).1.indicator hMset
        have hNonneg : 0 ≤ᵐ[P1]
            (E ∩ I n k).indicator (fun ω => Real.exp (phi * L0.X (b n k) ω)) :=
          Filter.Eventually.of_forall fun ω => by
            by_cases hω : ω ∈ E ∩ I n k
            · rw [Set.indicator_of_mem hω]; exact le_of_lt (Real.exp_pos _)
            · rw [Set.indicator_of_notMem hω]; exact le_rfl
        have hIndOfReal :
            (fun ω => (E ∩ I n k).indicator
              (fun ω => ENNReal.ofReal (Real.exp (phi * L0.X (b n k) ω))) ω) =
            (fun ω => ENNReal.ofReal
              ((E ∩ I n k).indicator (fun ω => Real.exp (phi * L0.X (b n k) ω)) ω)) := by
          ext ω
          by_cases hω : ω ∈ E ∩ I n k
          · simp [Set.indicator_of_mem hω]
          · simp [Set.indicator_of_notMem hω]
        rw [hIndOfReal, ← ofReal_integral_eq_lintegral_ofReal hInt hNonneg]
        have hEss := hEsscher (b n k) (E ∩ I n k) hMsetF
        have hDens : (fun ω => esscherDensity L0.X phi (L0.ψ phi) (b n k) ω) =
            (fun ω => Real.exp (phi * L0.X (b n k) ω)) := by
          ext ω; simp [esscherDensity, hψ0]
        rw [hDens] at hEss
        exact hEss.symm
      rw [Finset.sum_congr rfl hTerm, ← measure_biUnion_finset (hDisj n) (fun k _ =>
        F1.le (b n k) _ (hE_filt (a n k) (b n k))), hUnion n]
    have hLiminf : ∀ ω ∈ E ∩ {ω : Omega1 | τ ω < ((N : NNReal) : WithTop NNReal)},
        Filter.liminf (fun n => fn n ω) atTop = ENNReal.ofReal (Real.exp (phi * (x : ℝ))) := by
      intro ω hω
      have hltTop : τ ω < (⊤ : WithTop NNReal) := lt_trans hω.2 (WithTop.coe_lt_top (N : NNReal))
      rcases WithTop.ne_top_iff_exists.mp (WithTop.lt_top_iff_ne_top.mp hltTop) with ⟨t, ht⟩
      have hHit : τ ω = (t : WithTop NNReal) := ht.symm
      have htN : t < (N : NNReal) := WithTop.coe_lt_coe.mp (ht ▸ hω.2)
      let kn : ℕ → ℕ := fun n => Nat.floor ((t : ℝ) * (2 : ℝ) ^ n)
      have hfn_eq : ∀ n : ℕ, fn n ω = ENNReal.ofReal (Real.exp (phi * L0.X (b n (kn n)) ω)) := by
        intro n
        have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
        have hkn_lt : kn n < N * 2 ^ n := by
          rw [Nat.floor_lt (mul_nonneg t.coe_nonneg (le_of_lt hpow_pos))]
          have htN' : (t : ℝ) < (N : ℝ) := by exact_mod_cast htN
          have : (t : ℝ) * (2 : ℝ) ^ n < (N : ℝ) * (2 : ℝ) ^ n :=
            mul_lt_mul_of_pos_right htN' hpow_pos
          simpa [Nat.cast_mul, Nat.cast_pow] using this
        have hω_in : ω ∈ E ∩ I n (kn n) := by
          refine ⟨hω.1, ?_, ?_⟩
          · rw [hHit, WithTop.coe_le_coe, ← NNReal.coe_le_coe]
            simp only [a, kn, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
            rw [div_le_iff₀ hpow_pos]
            exact Nat.floor_le (mul_nonneg t.coe_nonneg (le_of_lt hpow_pos))
          · rw [hHit, WithTop.coe_lt_coe, ← NNReal.coe_lt_coe]
            simp only [b, kn, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
            rw [lt_div_iff₀ hpow_pos]
            simpa [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one ((t : ℝ) * (2 : ℝ) ^ n)
        dsimp [fn]
        rw [Finset.sum_eq_single (kn n)]
        · exact Set.indicator_of_mem hω_in _
        · intro k hk hne
          have hnot : ω ∉ E ∩ I n k := fun hmem =>
            Set.disjoint_left.mp (hDisj n (Finset.mem_range.mpr hkn_lt) hk hne.symm) hω_in hmem
          exact Set.indicator_of_notMem hnot _
        · intro hnot; exact absurd (Finset.mem_range.mpr hkn_lt) hnot
      have hTend_b : Tendsto (fun n => b n (kn n)) atTop (𝓝[Set.Ici t] t) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
        · rw [Metric.tendsto_atTop]
          intro ε hε
          rcases exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1) with ⟨m, hm⟩
          refine ⟨m, fun n hn => ?_⟩
          have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
          have ht_le_b : (t : ℝ) ≤ (b n (kn n) : ℝ) := by
            simp only [b, kn, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
            rw [le_div_iff₀ hpow_pos]
            exact le_of_lt (by simpa [Nat.cast_add, Nat.cast_one] using
              Nat.lt_floor_add_one ((t : ℝ) * (2 : ℝ) ^ n))
          have hb_le : (b n (kn n) : ℝ) ≤ (t : ℝ) + (1 / 2 : ℝ) ^ n := by
            simp only [b, kn, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
            rw [one_div, inv_pow, div_eq_mul_inv]
            have hfl : (kn n : ℝ) ≤ (t : ℝ) * (2 : ℝ) ^ n :=
              Nat.floor_le (mul_nonneg t.coe_nonneg (le_of_lt hpow_pos))
            have hstep : ((kn n : ℝ) + 1) * ((2 : ℝ) ^ n)⁻¹ ≤
                ((t : ℝ) * (2 : ℝ) ^ n + 1) * ((2 : ℝ) ^ n)⁻¹ :=
              mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr (le_of_lt hpow_pos))
            have hsimp : ((t : ℝ) * (2 : ℝ) ^ n + 1) * ((2 : ℝ) ^ n)⁻¹ =
                (t : ℝ) + ((2 : ℝ) ^ n)⁻¹ := by
              field_simp [ne_of_gt hpow_pos]
            simpa [kn, Nat.cast_add, Nat.cast_one, hsimp] using hstep
          rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht_le_b)]
          have hpow_le : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ m :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
          linarith
        · change t ≤ b n (kn n)
          rw [← NNReal.coe_le_coe]
          have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
          simp only [b, kn, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
          rw [le_div_iff₀ hpow_pos]
          exact le_of_lt (by simpa [Nat.cast_add, Nat.cast_one] using
            Nat.lt_floor_add_one ((t : ℝ) * (2 : ℝ) ^ n))
      have hTend_X : Tendsto (fun n => L0.X (b n (kn n)) ω) atTop (𝓝 (x : ℝ)) := by
        have hXt : L0.X t ω = (x : ℝ) := X_at_firstHittingTime_eq L0 x t ω hHit
        rw [← hXt]
        exact (L0.rightCont ω t).tendsto.comp hTend_b
      have hTend_f : Tendsto (fun n => fn n ω) atTop
          (𝓝 (ENNReal.ofReal (Real.exp (phi * (x : ℝ))))) := by
        simp_rw [hfn_eq]
        exact (ENNReal.continuous_ofReal.tendsto _).comp
          ((Real.continuous_exp.tendsto _).comp ((continuous_const.mul continuous_id).tendsto _ |>.comp hTend_X))
      exact hTend_f.liminf_eq
    have hMeasEN : MeasurableSet (E ∩ {ω : Omega1 | τ ω < ((N : NNReal) : WithTop NNReal)}) := by
      rw [← hUnion 0]
      exact Finset.measurableSet_biUnion _ fun k _ => F1.le (b 0 k) _ (hE_filt (a 0 k) (b 0 k))
    have hLe_ind :
        ∀ ω : Omega1,
          (E ∩ {ω : Omega1 | τ ω < ((N : NNReal) : WithTop NNReal)}).indicator
            (fun _ => ENNReal.ofReal (Real.exp (phi * (x : ℝ)))) ω ≤
          Filter.liminf (fun n => fn n ω) atTop := by
      intro ω
      by_cases hω : ω ∈ E ∩ {ω : Omega1 | τ ω < ((N : NNReal) : WithTop NNReal)}
      · rw [Set.indicator_of_mem hω, hLiminf ω hω]
      · rw [Set.indicator_of_notMem hω]; exact bot_le
    calc ENNReal.ofReal (Real.exp (phi * (x : ℝ))) *
          P1 (E ∩ {ω : Omega1 | τ ω < ((N : NNReal) : WithTop NNReal)})
        = ∫⁻ ω, (E ∩ {ω : Omega1 | τ ω < ((N : NNReal) : WithTop NNReal)}).indicator
            (fun _ => ENNReal.ofReal (Real.exp (phi * (x : ℝ)))) ω ∂P1 := by
          rw [lintegral_indicator hMeasEN, lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ∫⁻ ω, Filter.liminf (fun n => fn n ω) atTop ∂P1 := lintegral_mono hLe_ind
      _ ≤ Filter.liminf (fun n => ∫⁻ ω, fn n ω ∂P1) atTop := lintegral_liminf_le hMeas_fn
      _ = Q1 (E ∩ {ω : Omega1 | τ ω < ((N : NNReal) : WithTop NNReal)}) := by
          simp_rw [hInt_fn]; exact Filter.liminf_const _
      _ ≤ Q1 E := measure_mono Set.inter_subset_left
  have hUnionAll :
      (E ∩ {ω : Omega1 | τ ω ≠ ⊤}) =
        ⋃ N : ℕ, (E ∩ {ω : Omega1 | τ ω < ((N : NNReal) : WithTop NNReal)}) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hEω, hne⟩
      rcases WithTop.ne_top_iff_exists.mp hne with ⟨t, ht⟩
      rcases exists_nat_gt (t : ℝ) with ⟨N, hN⟩
      exact ⟨N, hEω, by rw [← ht, WithTop.coe_lt_coe]; exact_mod_cast hN⟩
    · rintro ⟨N, hEω, hlt⟩
      exact ⟨hEω, WithTop.lt_top_iff_ne_top.mp (lt_trans hlt (WithTop.coe_lt_top (N : NNReal)))⟩
  have hMonoN : Monotone (fun N : ℕ => E ∩ {ω : Omega1 | τ ω < ((N : NNReal) : WithTop NNReal)}) := by
    intro m n hmn ω hω
    have hmn' : (m : NNReal) ≤ (n : NNReal) := by exact_mod_cast hmn
    exact ⟨hω.1, lt_of_lt_of_le hω.2 (WithTop.coe_le_coe.mpr hmn')⟩
  rw [hUnionAll, hMonoN.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le hBoundN

private lemma prob_hit_ne_top_eq
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDec : ¬ (∀ᵐ ω : Omega ∂P, Antitone (fun t : NNReal => L.X t ω)))
    {phi : ℝ}
    (hRoot : 0 ≤ phi ∧ L.ψ phi = 0 ∧ ∀ θ : ℝ, 0 ≤ θ → L.ψ θ = 0 → θ ≤ phi)
    (x : NNReal) :
    P {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≠ ⊤} =
      ENNReal.ofReal (Real.exp (-phi * (x : ℝ))) := by
  let finiteTime : Omega → NNReal := fun ω => (firstHittingTime L.X (Set.Ioi (x : ℝ)) ω).untopD 0
  have hft : ∀ ω, firstHittingTime L.X (Set.Ioi (x : ℝ)) ω != ⊤ →
      firstHittingTime L.X (Set.Ioi (x : ℝ)) ω = (finiteTime ω : WithTop NNReal) := by
    intro ω hne
    have hne' : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≠ ⊤ := by simpa using hne
    rcases WithTop.ne_top_iff_exists.mp hne' with ⟨t, ht⟩
    dsimp [finiteTime]
    rw [← ht]
    rfl
  have hReal := firstPassageZero_consequence1 P F L hNotDec phi hRoot (x : ℝ) x.coe_nonneg finiteTime hft
  have hSetEq : {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≠ ⊤} =
      {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω != ⊤} := by
    ext ω; simp
  rw [hSetEq, ← ENNReal.ofReal_toReal (measure_ne_top P _), hReal]

private lemma not_ae_antitone_of_tendsto_psi
    {Omega : Type} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L1 : AvramDividend.Classical.SpectrallyNegativeLevy Q F)
    (hPos : ∃ θ : ℝ, 0 ≤ θ ∧ 0 < L1.ψ θ) :
    ¬ (∀ᵐ ω : Omega ∂Q, Antitone (fun t : NNReal => L1.X t ω)) := by
  intro hAnti
  rcases hPos with ⟨θ, hθ, hψpos⟩
  have hLe0 : ∀ᵐ ω : Omega ∂Q, L1.X 1 ω ≤ 0 := by
    filter_upwards [hAnti] with ω hω
    have h := hω (show (0 : NNReal) ≤ 1 by norm_num)
    dsimp only at h
    rwa [L1.X_zero ω] at h
  have hExpLe1 : ∀ᵐ ω : Omega ∂Q, Real.exp (θ * L1.X 1 ω) ≤ 1 := by
    filter_upwards [hLe0] with ω hω
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hθ hω)
  have hLap := L1.laplace 1 θ hθ
  have hIntLe : ∫ ω, Real.exp (θ * L1.X 1 ω) ∂Q ≤ ∫ _ : Omega, (1 : ℝ) ∂Q :=
    integral_mono_ae hLap.1 (integrable_const 1) hExpLe1
  rw [hLap.2, NNReal.coe_one, one_mul, integral_const, probReal_univ, smul_eq_mul, mul_one] at hIntLe
  have hψle : L1.ψ θ ≤ 0 := Real.exp_le_one_iff.mp hIntLe
  linarith


private lemma exp_sub_one_sub_le_half_sq_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    Real.exp u - 1 - u ≤ u ^ 2 / 2 := by
  let h : ℝ → ℝ := fun x => x ^ 2 / 2 - (Real.exp x - 1 - x)
  have hderiv : ∀ x : ℝ, HasDerivAt h (x + 1 - Real.exp x) x := fun x => by
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) (2 * x ^ (2 - 1) / 2) x :=
      (hasDerivAt_pow 2 x).div_const 2
    have h2 : HasDerivAt (fun t : ℝ => Real.exp t - 1 - t) (Real.exp x - 1) x :=
      ((Real.hasDerivAt_exp x).sub_const 1).fun_sub (hasDerivAt_id x)
    have h3 : HasDerivAt h (2 * x ^ (2 - 1) / 2 - (Real.exp x - 1)) x := h1.fun_sub h2
    have heq : 2 * x ^ (2 - 1) / 2 - (Real.exp x - 1) = x + 1 - Real.exp x := by
      norm_num; ring
    rwa [heq] at h3
  have hanti : Antitone h := by
    refine antitone_of_deriv_nonpos (fun x => (hderiv x).differentiableAt) (fun x => ?_)
    rw [(hderiv x).deriv]
    linarith [Real.add_one_le_exp x]
  have hge : h 0 ≤ h u := hanti hu
  dsimp only [h] at hge
  norm_num at hge
  linarith

private lemma abs_jumpIntegrand_le {a y : ℝ} (ha : 0 ≤ a) (hy : y < 0) :
    |Real.exp (a * y) - 1 - a * y * (Ioo (-1 : ℝ) 1).indicator 1 y| ≤
      max 1 (a ^ 2 / 2) * min 1 (y ^ 2) := by
  have hay : a * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hy.le
  by_cases h1 : -1 < y
  · have hmem : y ∈ Ioo (-1 : ℝ) 1 := ⟨h1, by linarith⟩
    have hy2_le : y ^ 2 ≤ 1 := by nlinarith
    rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one, min_eq_right hy2_le]
    have hge0 : 0 ≤ Real.exp (a * y) - 1 - a * y := by linarith [Real.add_one_le_exp (a * y)]
    rw [abs_of_nonneg hge0]
    have hle : Real.exp (a * y) - 1 - a * y ≤ (a * y) ^ 2 / 2 :=
      exp_sub_one_sub_le_half_sq_of_nonpos hay
    have hsq : (a * y) ^ 2 / 2 = (a ^ 2 / 2) * y ^ 2 := by ring
    rw [hsq] at hle
    exact hle.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg y))
  · push Not at h1
    have hnot : y ∉ Ioo (-1 : ℝ) 1 := fun h => by linarith [h.1]
    have hy2_ge : 1 ≤ y ^ 2 := by nlinarith
    rw [Set.indicator_of_notMem hnot, mul_zero, sub_zero, min_eq_left hy2_ge, mul_one]
    have hexp_le : Real.exp (a * y) ≤ 1 := Real.exp_le_one_iff.mpr hay
    have hexp_pos : 0 ≤ Real.exp (a * y) := Real.exp_nonneg _
    rw [abs_of_nonpos (by linarith)]
    have hle1 : -(Real.exp (a * y) - 1) ≤ 1 := by linarith
    exact hle1.trans (le_max_left _ _)

private lemma abs_exp_sub_one_mul_le {beta y : ℝ} (hBeta : 0 ≤ beta) (hy : y < 0) :
    |(Real.exp (beta * y) - 1) * y * (Ioo (-1 : ℝ) 1).indicator 1 y| ≤
      beta * min 1 (y ^ 2) := by
  by_cases h1 : -1 < y
  · have hmem : y ∈ Ioo (-1 : ℝ) 1 := ⟨h1, by linarith⟩
    have hy2_le : y ^ 2 ≤ 1 := by nlinarith
    rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one, min_eq_right hy2_le]
    have hby : beta * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hBeta hy.le
    have hexp_le : Real.exp (beta * y) ≤ 1 := Real.exp_le_one_iff.mpr hby
    have hge : beta * y + 1 ≤ Real.exp (beta * y) := Real.add_one_le_exp (beta * y)
    have habs_exp : |Real.exp (beta * y) - 1| ≤ -(beta * y) := by
      rw [abs_of_nonpos (by linarith)]; linarith
    rw [abs_mul, abs_of_neg hy]
    calc |Real.exp (beta * y) - 1| * (-y)
        ≤ (-(beta * y)) * (-y) := mul_le_mul_of_nonneg_right habs_exp (by linarith)
      _ = beta * y ^ 2 := by ring
  · push Not at h1
    have hnot : y ∉ Ioo (-1 : ℝ) 1 := fun h => by linarith [h.1]
    rw [Set.indicator_of_notMem hnot, mul_zero, abs_zero]
    exact mul_nonneg hBeta (le_min zero_le_one (sq_nonneg y))


private lemma esscher_tilt_any_filtration
    {Omega : Type} [MeasurableSpace Omega]
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (hEsscher : ∀ (t : NNReal) (A : Set Omega),
      MeasurableSet[F t] A →
      Q A =
        ENNReal.ofReal
          (∫ omega, Set.indicator A
            (fun omega : Omega =>
              esscherDensity L.X beta (L.ψ beta) t omega)
            omega ∂P)) :
    ∃ (Lbeta : AvramDividend.Classical.SpectrallyNegativeLevy Q F),
      Lbeta.X = L.X ∧
      ∀ θ : ℝ, 0 ≤ θ → Lbeta.ψ θ = L.ψ (θ + beta) - L.ψ beta := by
  -- Step 1: Basic measurability and lintegral representation of Q on F t
  have hX_measF : ∀ {s t : NNReal}, s ≤ t → Measurable[F t] (L.X s) :=
    fun hst => L.adapted.measurable_le hst
  have hX_meas : ∀ t : NNReal, Measurable (L.X t) := fun _ => L.adapted.measurable
  have hDens_int_eq_one : ∀ t : NNReal,
      (∫ omega, esscherDensity L.X beta (L.ψ beta) t omega ∂P) = 1 := by
    intro t
    have h1 := hEsscher t Set.univ MeasurableSet.univ
    simp only [measure_univ, Set.indicator_univ] at h1
    have hpos : 0 ≤ ∫ omega, esscherDensity L.X beta (L.ψ beta) t omega ∂P :=
      integral_nonneg fun _ => Real.exp_nonneg _
    have hofReal : ENNReal.ofReal (∫ omega, esscherDensity L.X beta (L.ψ beta) t omega ∂P) =
        ENNReal.ofReal 1 := by simpa using h1.symm
    exact (ENNReal.ofReal_eq_ofReal_iff hpos zero_le_one).mp hofReal
  have hDens_integrable : ∀ t : NNReal,
      Integrable (esscherDensity L.X beta (L.ψ beta) t) P := by
    intro t
    by_contra hnot
    have h0 : (∫ omega, esscherDensity L.X beta (L.ψ beta) t omega ∂P) = 0 := integral_undef hnot
    linarith [hDens_int_eq_one t]
  let Z : NNReal → Omega → ℝ≥0∞ := fun t omega =>
    ENNReal.ofReal (esscherDensity L.X beta (L.ψ beta) t omega)
  have hZ_measF : ∀ t : NNReal, Measurable[F t] (Z t) := fun t => by
    dsimp only [Z, esscherDensity]
    have hXt : Measurable[F t] (L.X t) := hX_measF (le_refl t)
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((hXt.const_mul beta).sub measurable_const))
  have hZ_meas : ∀ t : NNReal, Measurable (Z t) := fun t =>
    (hZ_measF t).mono (F.le t) le_rfl
  have hQ_eq_lintegral : ∀ (t : NNReal) (A : Set Omega),
      MeasurableSet[F t] A →
      Q A = ∫⁻ omega, A.indicator (Z t) omega ∂P := by
    intro t A hA
    have hA_m : MeasurableSet A := F.le t A hA
    rw [hEsscher t A hA, integral_indicator hA_m,
      ofReal_integral_eq_lintegral_ofReal (hDens_integrable t).integrableOn
        (ae_of_all _ fun _ => Real.exp_nonneg _),
      ← lintegral_indicator hA_m]
  have hZ_unit : ∀ t : NNReal, (∫⁻ omega, Z t omega ∂P) = 1 := by
    intro t
    have h := hQ_eq_lintegral t Set.univ MeasurableSet.univ
    simpa [measure_univ] using h.symm
  let W : ℝ → ℝ → ℝ≥0∞ := fun d x =>
    ENNReal.ofReal (Real.exp (beta * x - L.ψ beta * d))
  have hW_meas : ∀ d : ℝ, Measurable (W d) := fun d => by
    dsimp only [W]; fun_prop
  -- Step 2: Factorized joint law of (X_t - X_s, A ∈ F_s) under Q
  have hQ_inc_inter : ∀ {s t : NNReal} (hst : s ≤ t) {B : Set ℝ} (hB : MeasurableSet B)
      {A : Set Omega} (hA : MeasurableSet[F s] A),
      Q ((fun omega => L.X t omega - L.X s omega) ⁻¹' B ∩ A) =
        (∫⁻ omega, B.indicator (W ((t : ℝ) - (s : ℝ))) (L.X t omega - L.X s omega) ∂P) * Q A := by
    intro s t hst B hB A hA
    have hinc_F : Measurable[F t] (fun omega => L.X t omega - L.X s omega) :=
      (hX_measF (le_refl t)).sub (hX_measF hst)
    have hAFt : MeasurableSet[F t] A := F.mono hst A hA
    have hinter_F : MeasurableSet[F t] ((fun omega => L.X t omega - L.X s omega) ⁻¹' B ∩ A) :=
      (hinc_F hB).inter hAFt
    rw [hQ_eq_lintegral t _ hinter_F]
    have hfac : ∀ omega,
        ((fun omega => L.X t omega - L.X s omega) ⁻¹' B ∩ A).indicator (Z t) omega =
          B.indicator (W ((t : ℝ) - (s : ℝ))) (L.X t omega - L.X s omega) *
            A.indicator (Z s) omega := by
      intro omega
      by_cases hmem : omega ∈ (fun omega => L.X t omega - L.X s omega) ⁻¹' B ∩ A
      · rcases hmem with ⟨hBmem, hAmem⟩
        have hmem' : omega ∈ (fun omega => L.X t omega - L.X s omega) ⁻¹' B ∩ A := ⟨hBmem, hAmem⟩
        have hBmem' : L.X t omega - L.X s omega ∈ B := hBmem
        rw [Set.indicator_of_mem hmem', Set.indicator_of_mem hBmem',
          Set.indicator_of_mem hAmem]
        dsimp only [Z, W, esscherDensity]
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        congr 2; ring
      · rw [Set.indicator_of_notMem hmem]
        by_cases hBmem : L.X t omega - L.X s omega ∈ B
        · have hAnot : omega ∉ A := fun hAm => hmem ⟨hBmem, hAm⟩
          rw [Set.indicator_of_notMem hAnot, mul_zero]
        · rw [Set.indicator_of_notMem hBmem, zero_mul]
    simp_rw [hfac]
    have hinc_meas : Measurable (fun omega => L.X t omega - L.X s omega) :=
      (hX_meas t).sub (hX_meas s)
    have hf_meas : Measurable[MeasurableSpace.comap (fun omega => L.X t omega - L.X s omega) inferInstance]
        (fun omega => B.indicator (W ((t : ℝ) - (s : ℝ))) (L.X t omega - L.X s omega)) :=
      ((hW_meas _).indicator hB).comp (Measurable.of_comap_le le_rfl)
    have hg_meas : Measurable[F s] (A.indicator (Z s)) :=
      (hZ_measF s).indicator hA
    have hmul := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
      (measurable_iff_comap_le.mp hinc_meas) (F.le s) (L.indepIncrements s t hst) hf_meas hg_meas
    rw [hmul, ← hQ_eq_lintegral s A hA]
  have hQ_inc_preimage : ∀ {s t : NNReal} (hst : s ≤ t) {B : Set ℝ} (hB : MeasurableSet B),
      Q ((fun omega => L.X t omega - L.X s omega) ⁻¹' B) =
        ∫⁻ omega, B.indicator (W ((t : ℝ) - (s : ℝ))) (L.X t omega - L.X s omega) ∂P := by
    intro s t hst B hB
    have h := hQ_inc_inter hst hB MeasurableSet.univ
    simpa [Set.inter_univ, measure_univ] using h
  -- Step 3: Transformed triplet parameters
  let νbeta : Measure ℝ :=
    L.ν.withDensity (fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x)))
  let cbeta : ℝ :=
    L.c + beta * L.σ ^ 2 +
      ∫ x in {x : ℝ | |x| < 1}, (Real.exp (beta * x) - 1) * x ∂L.ν
  -- Step 4: νbeta properties
  have hν_Ici : νbeta (Ici 0) = 0 := by
    rw [withDensity_apply _ measurableSet_Ici]
    exact setLIntegral_measure_zero (Ici 0) _ L.ν_Ici
  have hν_ae_neg : ∀ᵐ y ∂L.ν, y < 0 := by
    rw [ae_iff]
    have hset : {y : ℝ | ¬ y < 0} = Ici (0 : ℝ) := by ext y; simp
    rw [hset]
    exact L.ν_Ici
  have hν_integrable : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂νbeta < ⊤ := by
    have hf_meas : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x))) := by fun_prop
    have hg_meas : Measurable (fun y : ℝ => ENNReal.ofReal (min 1 (y ^ 2))) := by fun_prop
    rw [lintegral_withDensity_eq_lintegral_mul _ hf_meas hg_meas]
    have hle : ∫⁻ y, ENNReal.ofReal (Real.exp (beta * y)) * ENNReal.ofReal (min 1 (y ^ 2)) ∂L.ν ≤
        ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂L.ν := by
      refine lintegral_mono_ae ?_
      filter_upwards [hν_ae_neg] with y hy
      have hexp1 : ENNReal.ofReal (Real.exp (beta * y)) ≤ 1 := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hBeta hy.le))
      calc ENNReal.ofReal (Real.exp (beta * y)) * ENNReal.ofReal (min 1 (y ^ 2))
          ≤ 1 * ENNReal.ofReal (min 1 (y ^ 2)) := by gcongr
        _ = ENNReal.ofReal (min 1 (y ^ 2)) := one_mul _
    exact lt_of_le_of_lt hle L.ν_integrable
  -- Step 5: Integrability of min(1, y^2) and the Laplace exponent shift identity
  have hmin_int : Integrable (fun y : ℝ => min 1 (y ^ 2)) L.ν := by
    refine ⟨(by fun_prop : Measurable (fun y : ℝ => min 1 (y ^ 2))).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have heq : (fun y : ℝ => ‖min 1 (y ^ 2)‖ₑ) = fun y : ℝ => ENNReal.ofReal (min 1 (y ^ 2)) := by
      ext y
      rw [Real.enorm_eq_ofReal (le_min zero_le_one (sq_nonneg y))]
    simpa only [heq] using L.ν_integrable
  have hjump_int : ∀ a : ℝ, 0 ≤ a →
      IntegrableOn
        (fun y : ℝ => Real.exp (a * y) - 1 - a * y * (Ioo (-1 : ℝ) 1).indicator 1 y)
        (Iio 0) L.ν := by
    intro a ha
    refine Integrable.mono' (hmin_int.integrableOn.const_mul (max 1 (a ^ 2 / 2))) ?_ ?_
    · have hm : Measurable (fun y : ℝ =>
          Real.exp (a * y) - 1 - a * y * (Ioo (-1 : ℝ) 1).indicator 1 y) := by
        have hind : Measurable ((Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ)) :=
          measurable_const.indicator measurableSet_Ioo
        exact ((Real.measurable_exp.comp (measurable_id.const_mul a)).sub measurable_const).sub
          ((measurable_id.const_mul a).mul hind)
      exact hm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
      rw [Real.norm_eq_abs]
      exact abs_jumpIntegrand_le ha hy
  have hshift_int :
      IntegrableOn
        (fun y : ℝ => (Real.exp (beta * y) - 1) * y * (Ioo (-1 : ℝ) 1).indicator 1 y)
        (Iio 0) L.ν := by
    refine Integrable.mono' (hmin_int.integrableOn.const_mul beta) ?_ ?_
    · have hind : Measurable ((Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ)) :=
        measurable_const.indicator measurableSet_Ioo
      have hm : Measurable (fun y : ℝ =>
          (Real.exp (beta * y) - 1) * y * (Ioo (-1 : ℝ) 1).indicator 1 y) :=
        (((Real.measurable_exp.comp (measurable_id.const_mul beta)).sub measurable_const).mul
          measurable_id).mul hind
      exact hm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
      rw [Real.norm_eq_abs]
      exact abs_exp_sub_one_mul_le hBeta hy
  have htilted_int : ∀ θ : ℝ, 0 ≤ θ →
      IntegrableOn
        (fun y : ℝ => Real.exp (beta * y) *
          (Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y))
        (Iio 0) L.ν := by
    intro θ hθ
    refine Integrable.mono' (hmin_int.integrableOn.const_mul (max 1 (θ ^ 2 / 2))) ?_ ?_
    · have hind : Measurable ((Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ)) :=
        measurable_const.indicator measurableSet_Ioo
      have hm : Measurable (fun y : ℝ => Real.exp (beta * y) *
          (Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y)) :=
        (Real.measurable_exp.comp (measurable_id.const_mul beta)).mul
          (((Real.measurable_exp.comp (measurable_id.const_mul θ)).sub measurable_const).sub
            ((measurable_id.const_mul θ).mul hind))
      exact hm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hexp1 : Real.exp (beta * y) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hBeta hy.le)
      calc Real.exp (beta * y) * |Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y|
          ≤ 1 * (max 1 (θ ^ 2 / 2) * min 1 (y ^ 2)) :=
            mul_le_mul hexp1 (abs_jumpIntegrand_le hθ hy)
              (abs_nonneg _) zero_le_one
        _ = max 1 (θ ^ 2 / 2) * min 1 (y ^ 2) := one_mul _
  have hdrift_set_eq :
      (∫ y in Iio (0 : ℝ), (Real.exp (beta * y) - 1) * y * (Ioo (-1 : ℝ) 1).indicator 1 y ∂L.ν) =
      ∫ x in {x : ℝ | |x| < 1}, (Real.exp (beta * x) - 1) * x ∂L.ν := by
    have hind_eq : ∀ y : ℝ,
        (Real.exp (beta * y) - 1) * y * (Ioo (-1 : ℝ) 1).indicator 1 y =
          (Ioo (-1 : ℝ) 1).indicator (fun x => (Real.exp (beta * x) - 1) * x) y := by
      intro y
      by_cases hy : y ∈ Ioo (-1 : ℝ) 1
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy]
    simp_rw [hind_eq]
    rw [setIntegral_indicator measurableSet_Ioo]
    have hset_abs : {x : ℝ | |x| < 1} = Ioo (-1 : ℝ) 1 := by
      ext x; simp [abs_lt]
    rw [hset_abs]
    refine setIntegral_congr_set ?_
    filter_upwards [hν_ae_neg] with y hy
    change (y ∈ Iio (0 : ℝ) ∩ Ioo (-1 : ℝ) 1) = (y ∈ Ioo (-1 : ℝ) 1)
    exact propext ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
  have hψ_shift : ∀ θ : ℝ, 0 ≤ θ →
      L.ψ (θ + beta) - L.ψ beta = laplaceExponent cbeta L.σ νbeta θ := by
    intro θ hθ
    dsimp only [SpectrallyNegativeLevy.ψ, laplaceExponent]
    have hsub_int :
        (∫ y in Iio (0 : ℝ),
          (Real.exp ((θ + beta) * y) - 1 - (θ + beta) * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂L.ν) -
        (∫ y in Iio (0 : ℝ),
          (Real.exp (beta * y) - 1 - beta * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂L.ν) =
        ∫ y in Iio (0 : ℝ),
          ((Real.exp ((θ + beta) * y) - 1 - (θ + beta) * y * (Ioo (-1 : ℝ) 1).indicator 1 y) -
           (Real.exp (beta * y) - 1 - beta * y * (Ioo (-1 : ℝ) 1).indicator 1 y)) ∂L.ν :=
      (integral_sub (hjump_int (θ + beta) (add_nonneg hθ hBeta)) (hjump_int beta hBeta)).symm
    have hpt : ∀ y : ℝ,
        (Real.exp ((θ + beta) * y) - 1 - (θ + beta) * y * (Ioo (-1 : ℝ) 1).indicator 1 y) -
        (Real.exp (beta * y) - 1 - beta * y * (Ioo (-1 : ℝ) 1).indicator 1 y) =
        Real.exp (beta * y) *
          (Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) +
        θ * ((Real.exp (beta * y) - 1) * y * (Ioo (-1 : ℝ) 1).indicator 1 y) := by
      intro y
      have hexp : Real.exp ((θ + beta) * y) = Real.exp (beta * y) * Real.exp (θ * y) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hexp]; ring
    have hsplit :
        (∫ y in Iio (0 : ℝ),
          ((Real.exp ((θ + beta) * y) - 1 - (θ + beta) * y * (Ioo (-1 : ℝ) 1).indicator 1 y) -
           (Real.exp (beta * y) - 1 - beta * y * (Ioo (-1 : ℝ) 1).indicator 1 y)) ∂L.ν) =
        (∫ y in Iio (0 : ℝ),
          Real.exp (beta * y) *
            (Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂L.ν) +
        θ * (∫ y in Iio (0 : ℝ),
          (Real.exp (beta * y) - 1) * y * (Ioo (-1 : ℝ) 1).indicator 1 y ∂L.ν) := by
      simp_rw [hpt]
      rw [integral_add (htilted_int θ hθ) ((hshift_int).const_mul θ), integral_const_mul]
    have hwd :
        (∫ y in Iio (0 : ℝ),
          (Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂νbeta) =
        ∫ y in Iio (0 : ℝ),
          Real.exp (beta * y) *
            (Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂L.ν := by
      dsimp only [νbeta]
      rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
        (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x))))
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _ measurableSet_Iio]
      refine setIntegral_congr_fun measurableSet_Iio fun y _ => ?_
      rw [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    have hcomb :
        (∫ y in Iio (0 : ℝ),
          (Real.exp ((θ + beta) * y) - 1 - (θ + beta) * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂L.ν) -
        (∫ y in Iio (0 : ℝ),
          (Real.exp (beta * y) - 1 - beta * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂L.ν) =
        (∫ y in Iio (0 : ℝ),
          (Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂νbeta) +
        θ * (∫ x in {x : ℝ | |x| < 1}, (Real.exp (beta * x) - 1) * x ∂L.ν) := by
      rw [hsub_int, hsplit, hwd, hdrift_set_eq]
    dsimp only [cbeta]
    linarith
  -- Step 6: Marginal law of X_t under Q and Laplace transform under Q
  have hQ_map_eq : ∀ t : NNReal,
      Q.map (L.X t) =
        (P.map (L.X t)).withDensity
          (fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x - L.ψ beta * (t : ℝ)))) := by
    intro t
    ext B hB
    rw [Measure.map_apply (hX_meas t) hB,
      withDensity_apply _ hB,
      setLIntegral_map hB (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x - L.ψ beta * (t : ℝ))))) (hX_meas t),
      ← lintegral_indicator (hX_meas t hB)]
    exact hQ_eq_lintegral t (L.X t ⁻¹' B) (hX_measF (le_refl t) hB)
  have hlaplace_Q : ∀ (t : NNReal) (θ : ℝ), 0 ≤ θ →
      Integrable (fun omega => Real.exp (θ * L.X t omega)) Q ∧
        ∫ omega, Real.exp (θ * L.X t omega) ∂Q =
          Real.exp ((t : ℝ) * laplaceExponent cbeta L.σ νbeta θ) := by
    intro t θ hθ
    have hexp_meas : Measurable (fun omega => Real.exp (θ * L.X t omega)) :=
      Real.measurable_exp.comp ((hX_meas t).const_mul θ)
    have hlint :
        (∫⁻ omega, ENNReal.ofReal (Real.exp (θ * L.X t omega)) ∂Q) =
        ENNReal.ofReal (Real.exp ((t : ℝ) * laplaceExponent cbeta L.σ νbeta θ)) := by
      have hg_meas : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (θ * x))) := by fun_prop
      have hd_meas : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x - L.ψ beta * (t : ℝ)))) := by
        fun_prop
      rw [← lintegral_map hg_meas (hX_meas t), hQ_map_eq t,
        lintegral_withDensity_eq_lintegral_mul _ hd_meas hg_meas]
      dsimp only [Pi.mul_apply]
      rw [lintegral_map (by fun_prop : Measurable (fun x : ℝ =>
        ENNReal.ofReal (Real.exp (beta * x - L.ψ beta * (t : ℝ))) *
          ENNReal.ofReal (Real.exp (θ * x)))) (hX_meas t)]
      have hfac : ∀ omega,
          ENNReal.ofReal (Real.exp (beta * L.X t omega - L.ψ beta * (t : ℝ))) *
            ENNReal.ofReal (Real.exp (θ * L.X t omega)) =
          ENNReal.ofReal (Real.exp (-(L.ψ beta * (t : ℝ)))) *
            ENNReal.ofReal (Real.exp ((θ + beta) * L.X t omega)) := by
        intro omega
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← ENNReal.ofReal_mul (Real.exp_nonneg _),
          ← Real.exp_add, ← Real.exp_add]
        congr 2; ring
      simp_rw [hfac]
      rw [lintegral_const_mul _ (by
        have := hX_meas t
        fun_prop)]
      rcases L.laplace t (θ + beta) (add_nonneg hθ hBeta) with ⟨hintP, hvalP⟩
      rw [← ofReal_integral_eq_lintegral_ofReal hintP (ae_of_all _ fun _ => Real.exp_nonneg _),
        hvalP, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      have hsh := hψ_shift θ hθ
      dsimp only [SpectrallyNegativeLevy.ψ] at hsh ⊢
      rw [← hsh]
      ring
    have hintQ : Integrable (fun omega => Real.exp (θ * L.X t omega)) Q := by
      refine ⟨hexp_meas.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      have heq : (fun omega => ‖Real.exp (θ * L.X t omega)‖ₑ) =
          fun omega => ENNReal.ofReal (Real.exp (θ * L.X t omega)) := by
        ext omega
        rw [Real.enorm_eq_ofReal (Real.exp_nonneg _)]
      rw [heq, hlint]
      exact ENNReal.ofReal_lt_top
    refine ⟨hintQ, ?_⟩
    have hpos : 0 ≤ ∫ omega, Real.exp (θ * L.X t omega) ∂Q :=
      integral_nonneg fun _ => Real.exp_nonneg _
    have hofReal : ENNReal.ofReal (∫ omega, Real.exp (θ * L.X t omega) ∂Q) =
        ENNReal.ofReal (Real.exp ((t : ℝ) * laplaceExponent cbeta L.σ νbeta θ)) := by
      rw [ofReal_integral_eq_lintegral_ofReal hintQ (ae_of_all _ fun _ => Real.exp_nonneg _), hlint]
    exact (ENNReal.ofReal_eq_ofReal_iff hpos (Real.exp_nonneg _)).mp hofReal
  -- Step 7: Assemble Lbeta : SpectrallyNegativeLevy Q F
  refine ⟨{
    X := L.X
    c := cbeta
    σ := L.σ
    ν := νbeta
    isProbability := inferInstance
    σ_nonneg := L.σ_nonneg
    ν_Ici := hν_Ici
    ν_integrable := hν_integrable
    X_zero := L.X_zero
    rightCont := L.rightCont
    leftLim := L.leftLim
    noPosJumps := L.noPosJumps
    adapted := L.adapted
    indepIncrements := fun s t hst => by
      rw [Indep_iff]
      intro s1 s2 hs1 hs2
      rcases hs1 with ⟨B, hB, rfl⟩
      rw [hQ_inc_inter hst hB hs2, hQ_inc_preimage hst hB]
    stationaryIncrements := fun s t hst => by
      have hinc_meas : Measurable (fun omega => L.X t omega - L.X s omega) :=
        (hX_meas t).sub (hX_meas s)
      refine ⟨hinc_meas.aemeasurable, (hX_meas (t - s)).aemeasurable, ?_⟩
      ext B hB
      rw [Measure.map_apply hinc_meas hB, Measure.map_apply (hX_meas (t - s)) hB,
        hQ_inc_preimage hst hB, hQ_eq_lintegral (t - s) (L.X (t - s) ⁻¹' B)
          (hX_measF (le_refl (t - s)) hB)]
      have hd : (t : ℝ) - (s : ℝ) = ((t - s : NNReal) : ℝ) := (NNReal.coe_sub hst).symm
      rw [hd]
      have hg_meas : Measurable (B.indicator (W ((t - s : NNReal) : ℝ))) :=
        (hW_meas _).indicator hB
      rw [← lintegral_map hg_meas hinc_meas, (L.stationaryIncrements s t hst).map_eq,
        lintegral_map hg_meas (hX_meas (t - s))]
      refine lintegral_congr fun omega => ?_
      by_cases hmem : L.X (t - s) omega ∈ B
      · have hmem' : omega ∈ L.X (t - s) ⁻¹' B := hmem
        simp [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem', W, Z, esscherDensity]
      · have hmem' : omega ∉ L.X (t - s) ⁻¹' B := hmem
        simp [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem']
    laplace := hlaplace_Q
  }, rfl, fun θ hθ => (hψ_shift θ hθ).symm⟩

end Kyprianou.Ch03.EsscherCanonicalTiltProof

open Kyprianou.Ch03 Kyprianou.Ch03.EsscherCanonicalTiltProof

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
    exists (Omega1 : Type) (m1 : MeasurableSpace Omega1),
      letI : MeasurableSpace Omega1 := m1
      exists (Q1 : Measure Omega1) (_hQ1 : IsProbabilityMeasure Q1)
             (F1 : Filtration NNReal m1)
             (L1 : AvramDividend.Classical.SpectrallyNegativeLevy Q1 F1),
        (¬ (∀ᵐ omega : Omega1 ∂ Q1,
          Antitone (fun t : NNReal => L1.X t omega))) ∧
        (forall theta : Real, 0 <= theta -> L1.ψ theta = 0 -> theta = 0) ∧
        (∀ (x : NNReal) (U : Finset NNReal),
          (∀ u ∈ U, u ≤ x) →
          ∀ (B : NNReal → Set (WithTop NNReal)),
            (∀ u ∈ U, MeasurableSet (B u)) →
            P ({omega : Omega |
                firstHittingTime L.X (Set.Ioi (x : Real)) omega ≠ ⊤} ∩
              ⋂ u ∈ U, {omega : Omega |
                firstHittingTime L.X (Set.Ioi (u : Real)) omega ∈ B u}) =
            ENNReal.ofReal (Real.exp (-phi * (x : Real))) *
              Q1 (⋂ u ∈ U, {omega : Omega1 |
                firstHittingTime L1.X (Set.Ioi (u : Real)) omega ∈ B u})) := by
  rcases spectrallyNegative_canonicalEsscherUncompleted P F L phi hRoot.1 with
    ⟨Omega1, m1, P1, Q1, hP1, hQ1, F1, L0, hPsiEq, hNotDec0, hLawHit, hEsscher⟩
  let _ : MeasurableSpace Omega1 := m1
  have _ : IsProbabilityMeasure P1 := hP1
  have _ : IsProbabilityMeasure Q1 := hQ1
  rcases esscher_tilt_any_filtration P1 Q1 F1 L0 phi hRoot.1 hEsscher with
    ⟨L1, hXeq, hPsiShift⟩
  have hNotDecP1 : ¬ (∀ᵐ ω : Omega1 ∂P1, Antitone (fun t : NNReal => L0.X t ω)) :=
    hNotDec0 hNotDecreasing
  have hRoot0 : 0 ≤ phi ∧ L0.ψ phi = 0 ∧ ∀ θ : ℝ, 0 ≤ θ → L0.ψ θ = 0 → θ ≤ phi := by
    refine ⟨hRoot.1, ?_, fun θ hθ hψ => hRoot.2.2 θ hθ (by rwa [← hPsiEq θ])⟩
    rw [hPsiEq phi]; exact hRoot.2.1
  have hNotDecQ1 : ¬ (∀ᵐ ω : Omega1 ∂Q1, Antitone (fun t : NNReal => L1.X t ω)) := by
    have hTend : Tendsto L.ψ atTop atTop :=
      exponentRegularity_infiniteLimitNonSubordinator P F L hNotDecreasing
    have hEv : ∀ᶠ u in atTop, (1 : ℝ) ≤ L.ψ u := Filter.tendsto_atTop.mp hTend 1
    rw [Filter.eventually_atTop] at hEv
    rcases hEv with ⟨M, hM⟩
    let u : ℝ := max M (phi + 1)
    have hu_psi : (1 : ℝ) ≤ L.ψ u := hM u (le_max_left _ _)
    have hu_gt : phi < u := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    refine not_ae_antitone_of_tendsto_psi Q1 F1 L1 ⟨u - phi, by linarith, ?_⟩
    have hge : 0 ≤ u - phi := by linarith
    rw [hPsiShift (u - phi) hge, sub_add_cancel, hPsiEq u, hPsiEq phi, hRoot.2.1, sub_zero]
    linarith
  have hZeroRoot1 : ∀ θ : ℝ, 0 ≤ θ → L1.ψ θ = 0 → θ = 0 := by
    intro θ hθ hψ
    rw [hPsiShift θ hθ, hPsiEq (θ + phi), hPsiEq phi, hRoot.2.1, sub_zero] at hψ
    have hle : θ + phi ≤ phi := hRoot.2.2 (θ + phi) (by linarith [hRoot.1]) hψ
    linarith
  refine ⟨Omega1, m1, Q1, hQ1, F1, L1, hNotDecQ1, hZeroRoot1, ?_⟩
  intro x U hU B hB
  let A0 : Set Omega1 := ⋂ u ∈ U, {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (u : ℝ)) ω ∈ B u}
  let A1 : Set Omega1 := ⋂ u ∈ U, {ω : Omega1 | firstHittingTime L1.X (Set.Ioi (u : ℝ)) ω ∈ B u}
  have hAeq : A0 = A1 := by simp [A0, A1, hXeq]
  -- Transfer LHS from P to P1 using hLawHit
  let Epath : Set (NNReal → WithTop NNReal) :=
    {f | f x ≠ ⊤} ∩ ⋂ u ∈ U, {f | f u ∈ B u}
  have hMeasEpath : MeasurableSet Epath :=
    ((measurable_pi_apply x) (MeasurableSet.singleton ⊤).compl).inter
      (Finset.measurableSet_biInter U fun u hu => (measurable_pi_apply u) (hB u hu))
  have hMeasτP : Measurable (fun ω : Omega => fun y : NNReal =>
      firstHittingTime L.X (Set.Ioi (y : ℝ)) ω) :=
    measurable_pi_lambda _ (fun y => measurable_firstHittingTime_Ioi L y)
  have hMeasτ0 : Measurable (fun ω : Omega1 => fun y : NNReal =>
      firstHittingTime L0.X (Set.Ioi (y : ℝ)) ω) :=
    measurable_pi_lambda _ (fun y => measurable_firstHittingTime_Ioi L0 y)
  have hLHS_eq :
      P ({ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≠ ⊤} ∩
          ⋂ u ∈ U, {ω : Omega | firstHittingTime L.X (Set.Ioi (u : ℝ)) ω ∈ B u}) =
      P1 (A0 ∩ {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) := by
    have h := congrArg (fun m => m Epath) hLawHit
    rw [Measure.map_apply hMeasτ0 hMeasEpath, Measure.map_apply hMeasτP hMeasEpath] at h
    rw [Set.inter_comm A0]
    simpa [Epath, A0, Set.preimage_inter, Set.preimage_iInter] using h.symm
  rw [hLHS_eq]
  change P1 (A0 ∩ {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) =
    ENNReal.ofReal (Real.exp (-phi * (x : ℝ))) * Q1 A1
  rw [← hAeq]
  -- Fatou bound on A0 and A0ᶜ
  have hFiltA : ∀ a t : NNReal,
      MeasurableSet[F1 t]
        (A0 ∩ {ω : Omega1 | (a : WithTop NNReal) ≤ firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ∧
          firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω < (t : WithTop NNReal)}) :=
    fun a t => measurableSet_cyl_inter_bin_F L0 x U hU B hB a t
  have hFiltAc : ∀ a t : NNReal,
      MeasurableSet[F1 t]
        (A0ᶜ ∩ {ω : Omega1 | (a : WithTop NNReal) ≤ firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ∧
          firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω < (t : WithTop NNReal)}) := by
    intro a t
    have hBin : MeasurableSet[F1 t]
        {ω : Omega1 | (a : WithTop NNReal) ≤ firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ∧
          firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω < (t : WithTop NNReal)} := by
      simpa using measurableSet_cyl_inter_bin_F L0 x ∅ (by simp) B (by simp) a t
    have hDiff :
        (A0ᶜ ∩ {ω : Omega1 | (a : WithTop NNReal) ≤ firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ∧
          firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω < (t : WithTop NNReal)}) =
        {ω : Omega1 | (a : WithTop NNReal) ≤ firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ∧
          firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω < (t : WithTop NNReal)} \
        (A0 ∩ {ω : Omega1 | (a : WithTop NNReal) ≤ firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ∧
          firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω < (t : WithTop NNReal)}) := by
      ext ω; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]; tauto
    rw [hDiff]
    exact hBin.diff (hFiltA a t)
  have hLeA := fatou_stopping_bound L0 hRoot.1 hRoot0.2.1 hEsscher x A0 hFiltA
  have hLeAc := fatou_stopping_bound L0 hRoot.1 hRoot0.2.1 hEsscher x A0ᶜ hFiltAc
  -- Complement sandwich: sum of LHS = 1 = sum of RHS
  have hMeasA0 : MeasurableSet A0 :=
    Finset.measurableSet_biInter U fun u hu => (measurable_firstHittingTime_Ioi L0 u) (hB u hu)
  have hDisjA : Disjoint
      (A0 ∩ {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤})
      (A0ᶜ ∩ {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) :=
    Disjoint.mono Set.inter_subset_left Set.inter_subset_left disjoint_compl_right
  have hUnionHit :
      (A0 ∩ {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) ∪
      (A0ᶜ ∩ {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) =
      {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤} := by
    rw [← Set.union_inter_distrib_right, Set.union_compl_self, Set.univ_inter]
  have hMeasAcHit : MeasurableSet
      (A0ᶜ ∩ {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) :=
    hMeasA0.compl.inter ((measurable_firstHittingTime_Ioi L0 x) (MeasurableSet.singleton ⊤).compl)
  have hSumP1 :
      P1 (A0 ∩ {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) +
      P1 (A0ᶜ ∩ {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) =
      ENNReal.ofReal (Real.exp (-phi * (x : ℝ))) := by
    rw [← measure_union hDisjA hMeasAcHit, hUnionHit]
    exact prob_hit_ne_top_eq P1 F1 L0 hNotDecP1 hRoot0 x
  have hSumQ1 : Q1 A0 + Q1 A0ᶜ = 1 := by
    rw [← measure_union disjoint_compl_right hMeasA0.compl, Set.union_compl_self, measure_univ]
  have hProdOne :
      ENNReal.ofReal (Real.exp (phi * (x : ℝ))) *
        ENNReal.ofReal (Real.exp (-phi * (x : ℝ))) = 1 := by
    rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _)), ← Real.exp_add]
    have : phi * (x : ℝ) + -phi * (x : ℝ) = 0 := by ring
    rw [this, Real.exp_zero, ENNReal.ofReal_one]
  have hSumEq :
      ENNReal.ofReal (Real.exp (phi * (x : ℝ))) *
        P1 (A0 ∩ {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) +
      ENNReal.ofReal (Real.exp (phi * (x : ℝ))) *
        P1 (A0ᶜ ∩ {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) =
      Q1 A0 + Q1 A0ᶜ := by
    rw [← mul_add, hSumP1, hProdOne, hSumQ1]
  have hEqMul :
      ENNReal.ofReal (Real.exp (phi * (x : ℝ))) *
        P1 (A0 ∩ {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) = Q1 A0 := by
    apply le_antisymm hLeA
    by_contra hlt
    have hlt' : ENNReal.ofReal (Real.exp (phi * (x : ℝ))) *
        P1 (A0 ∩ {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) < Q1 A0 :=
      not_le.mp hlt
    have hNeTopA : ENNReal.ofReal (Real.exp (phi * (x : ℝ))) *
        P1 (A0 ∩ {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top P1 _)
    have hNeTopAc : ENNReal.ofReal (Real.exp (phi * (x : ℝ))) *
        P1 (A0ᶜ ∩ {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top P1 _)
    have hStrict :
        ENNReal.ofReal (Real.exp (phi * (x : ℝ))) *
          P1 (A0 ∩ {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) +
        ENNReal.ofReal (Real.exp (phi * (x : ℝ))) *
          P1 (A0ᶜ ∩ {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) <
        Q1 A0 + Q1 A0ᶜ :=
      lt_of_lt_of_le (ENNReal.add_lt_add_right hNeTopAc hlt') (add_le_add_right hLeAc _)
    exact ne_of_lt hStrict hSumEq
  calc P1 (A0 ∩ {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤})
      = (ENNReal.ofReal (Real.exp (-phi * (x : ℝ))) *
          ENNReal.ofReal (Real.exp (phi * (x : ℝ)))) *
          P1 (A0 ∩ {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) := by
        rw [mul_comm (ENNReal.ofReal (Real.exp (-phi * (x : ℝ)))), hProdOne, one_mul]
    _ = ENNReal.ofReal (Real.exp (-phi * (x : ℝ))) *
          (ENNReal.ofReal (Real.exp (phi * (x : ℝ))) *
            P1 (A0 ∩ {ω : Omega1 | firstHittingTime L0.X (Set.Ioi (x : ℝ)) ω ≠ ⊤})) := by
        rw [mul_assoc]
    _ = ENNReal.ofReal (Real.exp (-phi * (x : ℝ))) * Q1 A0 := by rw [hEqMul]
