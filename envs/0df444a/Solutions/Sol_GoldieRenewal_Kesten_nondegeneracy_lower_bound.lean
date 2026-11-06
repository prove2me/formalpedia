-- Prove2me | solution 1 for GoldieRenewal.Kesten.nondegeneracy_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T04:22:46.369706+00:00
-- url     : https://prove2.me/submissions/66532d75-4b55-4251-bc40-8624fd3ae364
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Kesten_RandomDifferenceEquation
import Definitions.Def_GoldieRenewal_Kesten_Perpetuity
import Theorems.Thm_GoldieRenewal_Kesten_eq_4_6
import Theorems.Thm_GoldieRenewal_Kesten_ladder_lower_bound

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace KestenNondegAux

/-- Every probability law on `ℝ` has a median. -/
lemma exists_median (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∃ a : ℝ, GoldieRenewal.Kesten.IsMedian ν a := by
  set S : Set ℝ := {x | (2 : ℝ≥0∞)⁻¹ ≤ ν (Set.Iic x)} with hS
  have half_lt_one : (2 : ℝ≥0∞)⁻¹ < 1 := ENNReal.inv_lt_one.2 (by norm_num)
  have half_pos : (0 : ℝ≥0∞) < (2 : ℝ≥0∞)⁻¹ := by simp
  -- `ν (Iic n) → 1`
  have hup : Tendsto (fun n : ℕ => ν (Set.Iic (n : ℝ))) atTop (𝓝 (ν (⋃ n : ℕ, Set.Iic (n : ℝ)))) :=
    tendsto_measure_iUnion_atTop (fun i j hij => Set.Iic_subset_Iic.2 (by exact_mod_cast hij))
  have hU : (⋃ n : ℕ, Set.Iic (n : ℝ)) = Set.univ := by
    ext x; simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
    exact exists_nat_ge x
  rw [hU, measure_univ] at hup
  -- `ν (Iic (-n)) → 0`
  have hdown : Tendsto (fun n : ℕ => ν (Set.Iic (-(n : ℝ)))) atTop
      (𝓝 (ν (⋂ n : ℕ, Set.Iic (-(n : ℝ))))) :=
    tendsto_measure_iInter_atTop (fun _ => measurableSet_Iic.nullMeasurableSet)
      (fun i j hij => Set.Iic_subset_Iic.2 (by
        have : (i : ℝ) ≤ j := by exact_mod_cast hij
        linarith)) ⟨0, measure_ne_top _ _⟩
  have hI : (⋂ n : ℕ, Set.Iic (-(n : ℝ))) = ∅ := by
    ext x; simp only [Set.mem_iInter, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_forall,
      not_le]
    obtain ⟨n, hn⟩ := exists_nat_gt (-x)
    exact ⟨n, by linarith⟩
  rw [hI, measure_empty] at hdown
  obtain ⟨N, hN⟩ := (hup.eventually (lt_mem_nhds half_lt_one)).exists
  obtain ⟨L, hL⟩ := (hdown.eventually (gt_mem_nhds half_pos)).exists
  have hne : S.Nonempty := ⟨N, hN.le⟩
  have hbdd : BddBelow S := by
    refine ⟨-(L : ℝ), fun x hx => ?_⟩
    by_contra h
    push_neg at h
    have := measure_mono (μ := ν) (Set.Iic_subset_Iic.2 h.le)
    exact absurd (hx.trans this) (not_le.2 hL)
  set a := sInf S
  refine ⟨a, ?_, ?_⟩
  · -- `ν [a, ∞) ≥ 1/2` via `ν (-∞, a) ≤ 1/2`
    have hlt : ∀ k : ℕ, ν (Set.Iic (a - 1 / ((k : ℝ) + 1))) < (2 : ℝ≥0∞)⁻¹ := by
      intro k
      by_contra h
      push_neg at h
      have := csInf_le hbdd h
      have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    have hIio : Tendsto (fun k : ℕ => ν (Set.Iic (a - 1 / ((k : ℝ) + 1)))) atTop
        (𝓝 (ν (⋃ k : ℕ, Set.Iic (a - 1 / ((k : ℝ) + 1))))) := by
      apply tendsto_measure_iUnion_atTop
      intro i j hij
      apply Set.Iic_subset_Iic.2
      have : (i : ℝ) + 1 ≤ j + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
      have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) this
      linarith
    have hUio : (⋃ k : ℕ, Set.Iic (a - 1 / ((k : ℝ) + 1))) = Set.Iio a := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_Iio]
      constructor
      · rintro ⟨k, hk⟩
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      · intro hx
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
        exact ⟨k, by linarith⟩
    rw [hUio] at hIio
    have hle : ν (Set.Iio a) ≤ (2 : ℝ≥0∞)⁻¹ :=
      le_of_tendsto' hIio (fun k => (hlt k).le)
    have hsum : ν (Set.Iio a) + ν (Set.Ici a) = 1 := by
      rw [← measure_union (Set.disjoint_left.2 fun x h1 h2 => by
        simp only [Set.mem_Iio, Set.mem_Ici] at h1 h2; linarith) measurableSet_Ici,
        Set.Iio_union_Ici, measure_univ]
    have h2 : (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ = 1 := ENNReal.inv_two_add_inv_two
    by_contra h
    push_neg at h
    have : ν (Set.Iio a) + ν (Set.Ici a) < (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ :=
      ENNReal.add_lt_add_of_le_of_lt (by simp) hle h
    rw [hsum, h2] at this
    exact lt_irrefl _ this
  · -- `ν (-∞, a] ≥ 1/2` by continuity from above
    have hge : ∀ k : ℕ, (2 : ℝ≥0∞)⁻¹ ≤ ν (Set.Iic (a + 1 / ((k : ℝ) + 1))) := by
      intro k
      have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      obtain ⟨s, hs, hsa⟩ := exists_lt_of_csInf_lt hne (by linarith : sInf S < a + 1 / ((k : ℝ) + 1))
      exact hs.trans (measure_mono (Set.Iic_subset_Iic.2 hsa.le))
    have hIic : Tendsto (fun k : ℕ => ν (Set.Iic (a + 1 / ((k : ℝ) + 1)))) atTop
        (𝓝 (ν (⋂ k : ℕ, Set.Iic (a + 1 / ((k : ℝ) + 1))))) := by
      apply tendsto_measure_iInter_atTop (fun _ => measurableSet_Iic.nullMeasurableSet) _
        ⟨0, measure_ne_top _ _⟩
      intro i j hij
      apply Set.Iic_subset_Iic.2
      have : (i : ℝ) + 1 ≤ j + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
      have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) this
      linarith
    have hIa : (⋂ k : ℕ, Set.Iic (a + 1 / ((k : ℝ) + 1))) = Set.Iic a := by
      ext x
      simp only [Set.mem_iInter, Set.mem_Iic]
      constructor
      · intro h
        by_contra hx
        push_neg at hx
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
        have := h k
        linarith
      · intro hx k
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    rw [hIa] at hIic
    exact ge_of_tendsto' hIic hge

/-- The stopping-time (first-passage) estimate: if `A m` is determined by the first `m` pairs and
`B m` is the event `{f m ∈ T}` of probability `η`, then
`η · P(⋃ A m) ≤ P(⋃ (A m ∩ B m))`. -/
lemma first_passage {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ × ℝ) (hf : ∀ i, Measurable (f i)) (hind : iIndepFun f P)
    (A : ℕ → Set Ω)
    (hA : ∀ m, MeasurableSet[⨆ i ∈ Set.Iio m, MeasurableSpace.comap (f i) inferInstance] (A m))
    (T : Set (ℝ × ℝ)) (hT : MeasurableSet T) (η : ℝ≥0∞) (hη : ∀ m, P (f m ⁻¹' T) = η) :
    η * P (⋃ m, A m) ≤ P (⋃ m, (A m ∩ f m ⁻¹' T)) := by
  set 𝓕 : ℕ → MeasurableSpace Ω :=
    fun m => ⨆ i ∈ Set.Iio m, MeasurableSpace.comap (f i) inferInstance with h𝓕
  have hle : ∀ i, MeasurableSpace.comap (f i) inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    fun i => (hf i).comap_le
  have h𝓕le : ∀ m, 𝓕 m ≤ (inferInstance : MeasurableSpace Ω) := fun m =>
    iSup₂_le fun i _ => hle i
  have h𝓕mono : ∀ k m, k ≤ m → 𝓕 k ≤ 𝓕 m := by
    intro k m hkm
    apply iSup₂_le
    intro i hi
    exact le_iSup₂ (f := fun i (_ : i ∈ Set.Iio m) => MeasurableSpace.comap (f i) inferInstance) i
      (lt_of_lt_of_le hi hkm)
  set E := disjointed A with hE
  have hEm : ∀ m, MeasurableSet[𝓕 m] (E m) := by
    intro m
    rw [hE, disjointed_eq_inter_compl]
    refine MeasurableSet.inter (hA m) ?_
    refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun hj => ?_
    exact (h𝓕mono j m hj.le _ (hA j)).compl
  have hindep : ∀ m, P (E m ∩ f m ⁻¹' T) = P (E m) * η := by
    intro m
    have hI : Indep (𝓕 m) (⨆ i ∈ ({m} : Set ℕ), MeasurableSpace.comap (f i) inferInstance) P :=
      indep_iSup_of_disjoint hle hind.iIndep (by simp)
    have hB : MeasurableSet[⨆ i ∈ ({m} : Set ℕ), MeasurableSpace.comap (f i) inferInstance]
        (f m ⁻¹' T) := by
      have : MeasurableSet[MeasurableSpace.comap (f m) inferInstance] (f m ⁻¹' T) := ⟨T, hT, rfl⟩
      exact le_iSup₂ (f := fun i (_ : i ∈ ({m} : Set ℕ)) =>
        MeasurableSpace.comap (f i) inferInstance) m rfl _ this
    rw [(Indep_iff _ _ P).1 hI _ _ (hEm m) hB, hη]
  have hdisj : Pairwise (Function.onFun Disjoint fun m => E m ∩ f m ⁻¹' T) := by
    intro i j hij
    exact ((disjoint_disjointed A hij).mono Set.inter_subset_left Set.inter_subset_left)
  have hmeas : ∀ m, MeasurableSet (E m ∩ f m ⁻¹' T) := fun m =>
    (h𝓕le m _ (hEm m)).inter ((hf m) hT)
  calc η * P (⋃ m, A m) = η * P (⋃ m, E m) := by rw [hE, iUnion_disjointed]
    _ = η * ∑' m, P (E m) := by
        rw [measure_iUnion (disjoint_disjointed A) (fun m => h𝓕le m _ (hEm m))]
    _ = ∑' m, P (E m ∩ f m ⁻¹' T) := by
        rw [← ENNReal.tsum_mul_left]; congr 1; funext m; rw [hindep m, mul_comm]
    _ = P (⋃ m, (E m ∩ f m ⁻¹' T)) := (measure_iUnion hdisj hmeas).symm
    _ ≤ P (⋃ m, (A m ∩ f m ⁻¹' T)) := by
        apply measure_mono
        exact Set.iUnion_mono fun m => Set.inter_subset_inter_left _ (disjointed_subset A m)

end KestenNondegAux

open KestenNondegAux GoldieRenewal.Kesten in
theorem solution (κ : ℝ) (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hM : GoldieRenewal.Implicit.CramerConditions κ (μ.map Prod.snd))
    (hQ : ∫⁻ p, ENNReal.ofReal (|p.1| ^ κ) ∂μ < ∞)
    (h45 : ∀ c : ℝ, μ {p | p.1 = (1 - p.2) * c} < 1)
    (ρ : ProbabilityMeasure ℝ) (hρ : rdeOperator μ (ρ : Measure ℝ) = ρ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℝ in atTop, c ≤ t ^ κ * (ρ : Measure ℝ).real {r | t < |r|} := by
  have hκ : 0 < κ := hM.pos
  obtain ⟨a, ha⟩ := exists_median (ρ : Measure ℝ)
  -- a threshold `θ` with `μ{|Q + Ma − a| > θ} > 0`, from (4.5) at `c = a`
  have hne : 0 < μ {p : ℝ × ℝ | p.1 + p.2 * a - a ≠ 0} := by
    have hs : MeasurableSet {p : ℝ × ℝ | p.1 = (1 - p.2) * a} :=
      measurableSet_eq_fun measurable_fst (by fun_prop)
    have e : {p : ℝ × ℝ | p.1 + p.2 * a - a ≠ 0} = {p : ℝ × ℝ | p.1 = (1 - p.2) * a}ᶜ := by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, ne_eq]
      constructor <;> intro h h' <;> apply h <;> linarith
    rw [e, prob_compl_eq_one_sub hs]
    exact tsub_pos_of_lt (h45 a)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 0 < μ {p : ℝ × ℝ | 1 / ((k : ℝ) + 1) < |p.1 + p.2 * a - a|} := by
    by_contra h
    push_neg at h
    have hU : {p : ℝ × ℝ | p.1 + p.2 * a - a ≠ 0} ⊆
        ⋃ k : ℕ, {p : ℝ × ℝ | 1 / ((k : ℝ) + 1) < |p.1 + p.2 * a - a|} := by
      intro p hp
      simp only [Set.mem_setOf_eq] at hp
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (abs_pos.2 hp)
      exact Set.mem_iUnion.2 ⟨k, hk⟩
    have := measure_mono_null hU (measure_iUnion_null fun k => le_antisymm (h k) bot_le)
    exact (ne_of_gt hne) this
  set θ : ℝ := 1 / ((k : ℝ) + 1) with hθ
  have hθpos : 0 < θ := by positivity
  set B : Set (ℝ × ℝ) := {p : ℝ × ℝ | θ < |p.1 + p.2 * a - a|} with hB
  have hBm : MeasurableSet B := measurableSet_lt measurable_const (by fun_prop)
  set η : ℝ≥0∞ := μ B with hη
  have hηpos : 0 < η.toReal := ENNReal.toReal_pos (ne_of_gt hk) (measure_ne_top _ _)
  -- the i.i.d. sequence `(Q_i, M_i)` on `Ω = ℕ → ℝ × ℝ`
  let P : Measure (ℕ → ℝ × ℝ) := Measure.infinitePi (fun _ : ℕ => μ)
  let Q : ℕ → (ℕ → ℝ × ℝ) → ℝ := fun i ω => (ω i).1
  let M : ℕ → (ℕ → ℝ × ℝ) → ℝ := fun i ω => (ω i).2
  have hf : ∀ i, Measurable (fun ω : ℕ → ℝ × ℝ => ω i) := fun i => measurable_pi_apply i
  have hQm : ∀ i, Measurable (Q i) := fun i => measurable_fst.comp (hf i)
  have hMm : ∀ i, Measurable (M i) := fun i => measurable_snd.comp (hf i)
  have hind0 : iIndepFun (fun i (ω : ℕ → ℝ × ℝ) => ω i) P :=
    iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ => id) (fun _ => measurable_id)
  have hind : iIndepFun (fun i ω => (Q i ω, M i ω)) P := hind0
  have hlaw0 : ∀ i, P.map (fun ω : ℕ → ℝ × ℝ => ω i) = μ := fun i =>
    Measure.infinitePi_map_eval (fun _ : ℕ => μ) i
  have hlaw : ∀ i, P.map (fun ω => (Q i ω, M i ω)) = μ := hlaw0
  have hindM : iIndepFun M P := hind0.comp (fun _ => Prod.snd) (fun _ => measurable_snd)
  have hlawM : ∀ i, P.map (M i) = μ.map Prod.snd := by
    intro i
    rw [← hlaw0 i, Measure.map_map measurable_snd (hf i)]; rfl
  obtain ⟨δ, hδ, hev⟩ := ladder_lower_bound P κ (μ.map Prod.snd) hM M hMm hindM hlawM
  -- the change of variable `t = log((2/θ) x)`
  have hg : Tendsto (fun x : ℝ => Real.log ((2 / θ) * x)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.const_mul_atTop (by positivity))
  set K : ℝ := (2 / θ) ^ κ with hK
  have hKpos : 0 < K := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨η.toReal * δ / (2 * K), by positivity, ?_⟩
  filter_upwards [hg.eventually hev, eventually_gt_atTop |a|] with x hx hxa
  have hx0 : 0 < x := lt_of_le_of_lt (abs_nonneg a) hxa
  set y : ℝ := (2 / θ) * x with hy
  have hypos : 0 < y := by positivity
  have hexp : Real.exp (Real.log y) = y := Real.exp_log hypos
  simp only [Function.comp_apply, hexp] at hx
  -- first-passage events
  set A : ℕ → Set (ℕ → ℝ × ℝ) := fun m => {ω | y < |piProd M m ω|} with hA
  have hAm : ∀ m, MeasurableSet[⨆ i ∈ Set.Iio m,
      MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω i) inferInstance] (A m) := by
    intro m
    have hmeas : Measurable[⨆ i ∈ Set.Iio m,
        MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω i) inferInstance] (piProd M m) := by
      unfold piProd
      apply Finset.measurable_prod (m := ⨆ i ∈ Set.Iio m,
        MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω i) inferInstance)
      intro i hi
      have h1 : Measurable[MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω i) inferInstance]
          (fun ω : ℕ → ℝ × ℝ => ω i) := comap_measurable _
      have h2 := h1.mono (le_iSup₂ (f := fun i (_ : i ∈ Set.Iio m) =>
        MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω i) inferInstance) i
        (by simpa using Finset.mem_range.1 hi)) le_rfl
      exact measurable_snd.comp h2
    exact hmeas (measurableSet_lt measurable_const measurable_abs)
  have hFP := first_passage P (fun i ω => ω i) hf hind0 A hAm B hBm η
    (fun m => by rw [← Measure.map_apply (hf m) hBm, hlaw0 m])
  -- inclusion of events
  have hsub : (⋃ m, (A m ∩ (fun ω : ℕ → ℝ × ℝ => ω m) ⁻¹' B)) ⊆
      {ω | ∃ j : ℕ, 1 ≤ j ∧ x < |partialSum Q M j ω + piProd M j ω * a|} := by
    intro ω hω
    obtain ⟨m, hmA, hmB⟩ := Set.mem_iUnion.1 hω
    simp only [hA, Set.mem_setOf_eq] at hmA
    simp only [Set.mem_preimage, hB, Set.mem_setOf_eq] at hmB
    have hS : partialSum Q M (m + 1) ω = partialSum Q M m ω + piProd M m ω * Q m ω := by
      unfold partialSum; rw [Finset.sum_range_succ]
    have hPm : piProd M (m + 1) ω = piProd M m ω * M m ω := by
      unfold piProd; rw [Finset.prod_range_succ]
    have hdiff : (partialSum Q M (m + 1) ω + piProd M (m + 1) ω * a) -
        (partialSum Q M m ω + piProd M m ω * a) = piProd M m ω * ((ω m).1 + (ω m).2 * a - a) := by
      rw [hS, hPm]; simp only [Q, M]; ring
    have hbig : 2 * x < |(partialSum Q M (m + 1) ω + piProd M (m + 1) ω * a) -
        (partialSum Q M m ω + piProd M m ω * a)| := by
      rw [hdiff, abs_mul]
      have : y * θ = 2 * x := by rw [hy]; field_simp
      calc 2 * x = y * θ := this.symm
        _ < |piProd M m ω| * |(ω m).1 + (ω m).2 * a - a| :=
          mul_lt_mul'' hmA hmB hypos.le hθpos.le
    have htri := abs_sub (partialSum Q M (m + 1) ω + piProd M (m + 1) ω * a)
        (partialSum Q M m ω + piProd M m ω * a)
    by_cases h1 : x < |partialSum Q M (m + 1) ω + piProd M (m + 1) ω * a|
    · exact ⟨m + 1, by omega, h1⟩
    · have h2 : x < |partialSum Q M m ω + piProd M m ω * a| := by
        push_neg at h1; linarith
      refine ⟨m, ?_, h2⟩
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · exfalso
        subst h0
        simp [partialSum, piProd] at h2
        linarith
      · exact h0
  have hsub2 : {ω : ℕ → ℝ × ℝ | ∃ n : ℕ, 1 ≤ n ∧ y < |piProd M n ω|} ⊆ ⋃ m, A m := by
    intro ω hω
    obtain ⟨n, -, hn⟩ := hω
    exact Set.mem_iUnion.2 ⟨n, hn⟩
  have h46 := eq_4_6 κ μ hM hQ P Q M hQm hMm hind hlaw ρ hρ a ha x hx0.le
  -- combine, in real numbers
  have hchain : η.toReal * P.real {ω | ∃ n : ℕ, 1 ≤ n ∧ y < |piProd M n ω|} ≤
      2 * (ρ : Measure ℝ).real {r | x < |r|} := by
    have e1 : η * P {ω | ∃ n : ℕ, 1 ≤ n ∧ y < |piProd M n ω|} ≤
        2 * (ρ : Measure ℝ) {r | x < |r|} :=
      (mul_le_mul_right (measure_mono hsub2) η).trans (hFP.trans ((measure_mono hsub).trans h46))
    have e2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _)) e1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul] at e2
  have hexpk : Real.exp (-κ * Real.log y) = (K * x ^ κ)⁻¹ := by
    rw [hK, ← Real.mul_rpow (by positivity) hx0.le, ← hy, ← Real.rpow_neg hypos.le,
      Real.rpow_def_of_pos hypos]
    ring_nf
  rw [hexpk] at hx
  have hXpos : 0 < x ^ κ := Real.rpow_pos_of_pos hx0 _
  have key : η.toReal * δ ≤ 2 * (ρ : Measure ℝ).real {r | x < |r|} * (K * x ^ κ) := by
    have h3 := (mul_le_mul_of_nonneg_left hx hηpos.le).trans hchain
    have h4 : η.toReal * (δ * (K * x ^ κ)⁻¹) = η.toReal * δ / (K * x ^ κ) := by
      field_simp
    rw [h4, div_le_iff₀ (by positivity)] at h3
    exact h3
  rw [div_le_iff₀ (by positivity)]
  linarith
