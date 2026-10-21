-- Prove2me | solution 1 for GreedyRS.EFG.lemma3_argmin_finite
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:39:40.122022+00:00
-- url     : https://prove2.me/submissions/ec3a11d5-0601-4efe-b9f8-32acff407819

import Mathlib
import Definitions.Def_GreedyRS_EFG_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology
open GreedyRS.Greedy

instance prob_GEF : IsProbabilityMeasure stdNormalSeq := by
  unfold stdNormalSeq; infer_instance

theorem coord_indep_GEF : iIndepFun (fun (i : ℕ) (z : ℕ → ℝ) => z i) stdNormalSeq :=
  iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1) (X := fun _ ω => ω)
    (fun _ => measurable_id)

theorem coord_law_GEF (i : ℕ) :
    stdNormalSeq.map (fun z : ℕ → ℝ => z i) = gaussianReal 0 1 := by
  have := Measure.infinitePi_map_eval (fun _ : ℕ => gaussianReal 0 1) i
  exact this

theorem sum_law_GEF (J : Finset ℕ) :
    stdNormalSeq.map (fun z : ℕ → ℝ => ∑ i ∈ J, z i) = gaussianReal 0 (J.card : ℝ≥0) := by
  induction J using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero]
    rw [gaussianReal_zero_var, Measure.map_const]
    simp
  | insert a J ha ih =>
    have hind : IndepFun (fun z : ℕ → ℝ => z a) (∑ j ∈ J, fun z : ℕ → ℝ => z j) stdNormalSeq :=
      (coord_indep_GEF.indepFun_finsetSum_of_notMem (fun i => measurable_pi_apply i) ha).symm
    have hsum : (∑ j ∈ J, fun z : ℕ → ℝ => z j) = fun z => ∑ j ∈ J, z j := by
      funext z; simp [Finset.sum_apply]
    rw [hsum] at hind
    have := gaussianReal_add_gaussianReal_of_indepFun hind (coord_law_GEF a) ih
    have e : (fun z : ℕ → ℝ => ∑ i ∈ insert a J, z i) = (fun z : ℕ → ℝ => z a) + fun z => ∑ j ∈ J, z j := by
      funext z; simp [Finset.sum_insert ha]
    rw [e, this]
    congr 1
    · simp
    · rw [Finset.card_insert_of_notMem ha]; push_cast; ring

/-- block endpoints -/
def Nseq (n0 : ℕ) : ℕ → ℕ
  | 0 => n0
  | j + 1 => Nseq n0 j * (4 ^ j + 1)

theorem Nseq_pos (n0 : ℕ) (hn0 : 1 ≤ n0) (j : ℕ) : 0 < Nseq n0 j := by
  induction j with
  | zero => simp [Nseq]; omega
  | succ j ih => simp only [Nseq]; positivity

theorem Nseq_ge (n0 : ℕ) (j : ℕ) : n0 ≤ Nseq n0 j := by
  induction j with
  | zero => simp [Nseq]
  | succ j ih =>
    simp only [Nseq]
    calc n0 ≤ Nseq n0 j := ih
      _ ≤ Nseq n0 j * (4 ^ j + 1) := Nat.le_mul_of_pos_right _ (by positivity)

theorem Nseq_mono (n0 : ℕ) : Monotone (Nseq n0) := by
  apply monotone_nat_of_le_succ
  intro j
  simp only [Nseq]
  exact Nat.le_mul_of_pos_right _ (by positivity)

theorem Nseq_blk (n0 : ℕ) (j : ℕ) : Nseq n0 (j + 1) - Nseq n0 j = Nseq n0 j * 4 ^ j := by
  simp only [Nseq]
  rw [Nat.mul_add, Nat.mul_one]; omega

def Tblk (n0 j : ℕ) (z : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.Ico (Nseq n0 j) (Nseq n0 (j + 1)), z i

def Sn (n : ℕ) (z : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range n, z i

noncomputable def sig (n0 j : ℕ) : ℝ := Real.sqrt ((Nseq n0 j * 4 ^ j : ℕ) : ℝ)

theorem lowerTail_GEF (m : ℕ) (hm : 0 < m) :
    gaussianReal 0 (m : ℝ≥0) (Set.Iio (-(Real.sqrt m))) = gaussianReal 0 1 (Set.Iio (-1)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hmpos
  set c : ℝ := (Real.sqrt m)⁻¹ with hc
  have hmap := gaussianReal_map_const_mul (μ := 0) (v := (m : ℝ≥0)) c
  have hv : (NNReal.mk (c ^ 2) (sq_nonneg _)) * (m : ℝ≥0) = 1 := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_natCast, NNReal.coe_one]
    rw [hc, inv_pow, Real.sq_sqrt hmpos.le]
    field_simp
  rw [hv, mul_zero] at hmap
  have := congrArg (fun μ : Measure ℝ => μ (Set.Iio (-1))) hmap
  beta_reduce at this
  rw [← this, Measure.map_apply (measurable_const_mul c) measurableSet_Iio]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_Iio]
  rw [hc, inv_mul_lt_iff₀ hs]
  constructor <;> intro h <;> linarith

theorem cpos_GEF : gaussianReal 0 1 (Set.Iio (-1)) ≠ 0 := by
  intro h
  have := (gaussianReal_absolutelyContinuous' 0 (v := 1) one_ne_zero) h
  simp at this

theorem Tblk_meas (n0 j : ℕ) : Measurable (Tblk n0 j) := by
  unfold Tblk
  exact Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)

theorem Sn_meas (n : ℕ) : Measurable (Sn n) := by
  unfold Sn
  exact Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)

theorem PD_GEF (n0 : ℕ) (hn0 : 1 ≤ n0) (j : ℕ) :
    stdNormalSeq {z | Tblk n0 j z < -sig n0 j} = gaussianReal 0 1 (Set.Iio (-1)) := by
  have hlaw := sum_law_GEF (Finset.Ico (Nseq n0 j) (Nseq n0 (j + 1)))
  have hcard : (Finset.Ico (Nseq n0 j) (Nseq n0 (j + 1))).card = Nseq n0 j * 4 ^ j := by
    rw [Nat.card_Ico, Nseq_blk]
  rw [hcard] at hlaw
  have hm : 0 < Nseq n0 j * 4 ^ j := by have := Nseq_pos n0 hn0 j; positivity
  have : {z : ℕ → ℝ | Tblk n0 j z < -sig n0 j} = (Tblk n0 j) ⁻¹' (Set.Iio (-sig n0 j)) := rfl
  rw [this, ← Measure.map_apply (Tblk_meas n0 j) measurableSet_Iio]
  have hT : stdNormalSeq.map (Tblk n0 j) = gaussianReal 0 ((Nseq n0 j * 4 ^ j : ℕ) : ℝ≥0) := hlaw
  rw [hT]
  unfold sig
  exact lowerTail_GEF _ hm

theorem PG_GEF (n0 : ℕ) (hn0 : 1 ≤ n0) (j : ℕ) :
    stdNormalSeq {z | sig n0 j < |Sn (Nseq n0 j) z|} ≤ ENNReal.ofReal ((1 / 4 : ℝ) ^ j) := by
  have hlaw : stdNormalSeq.map (Sn (Nseq n0 j)) = gaussianReal 0 (Nseq n0 j : ℝ≥0) := by
    have := sum_law_GEF (Finset.range (Nseq n0 j))
    rw [Finset.card_range] at this
    exact this
  have hm : 0 < Nseq n0 j * 4 ^ j := by have := Nseq_pos n0 hn0 j; positivity
  have hsigpos : 0 < sig n0 j := Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hsub : {z : ℕ → ℝ | sig n0 j < |Sn (Nseq n0 j) z|} ⊆ (Sn (Nseq n0 j)) ⁻¹' {x : ℝ | sig n0 j ≤ |x - 0|} := by
    intro z hz; simp only [Set.mem_preimage, Set.mem_setOf_eq, sub_zero] at hz ⊢; exact hz.le
  refine (measure_mono hsub).trans ?_
  rw [← Measure.map_apply (Sn_meas _) (measurableSet_le measurable_const (by fun_prop)), hlaw]
  have hL2 : MemLp id 2 (gaussianReal 0 (Nseq n0 j : ℝ≥0)) := by
    simpa using memLp_id_gaussianReal' (μ := 0) (v := (Nseq n0 j : ℝ≥0)) 2 (by simp)
  have hcheb := meas_ge_le_variance_div_sq hL2 hsigpos
  have hE : (gaussianReal 0 (Nseq n0 j : ℝ≥0))[id] = 0 := by
    simpa using integral_id_gaussianReal (μ := 0) (v := (Nseq n0 j : ℝ≥0))
  have hV : variance id (gaussianReal 0 (Nseq n0 j : ℝ≥0)) = Nseq n0 j := by
    simpa using variance_id_gaussianReal (μ := 0) (v := (Nseq n0 j : ℝ≥0))
  rw [hE, hV] at hcheb
  refine le_trans (le_of_eq_of_le ?_ hcheb) ?_
  · rfl
  · apply ENNReal.ofReal_le_ofReal
    unfold sig
    rw [Real.sq_sqrt (by positivity)]
    push_cast
    have : (Nseq n0 j : ℝ) ≠ 0 := by exact_mod_cast (Nseq_pos n0 hn0 j).ne'
    rw [show ((1 / 4 : ℝ) ^ j) = 1 / (4 : ℝ) ^ j by rw [one_div, inv_pow, one_div]]
    apply le_of_eq
    field_simp

def mS (i : ℕ) : MeasurableSpace (ℕ → ℝ) :=
  MeasurableSpace.comap (fun z : ℕ → ℝ => z i) inferInstance

theorem mS_le (i : ℕ) : mS i ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
  (measurable_pi_apply i).comap_le

theorem iIndep_mS : iIndep mS stdNormalSeq :=
  (iIndepFun_iff_iIndep (fun _ => inferInstance) _ stdNormalSeq).1 coord_indep_GEF

theorem meas_sum_mS (S : Set ℕ) (B : Finset ℕ) (hB : ∀ i ∈ B, i ∈ S) :
    Measurable[⨆ i ∈ S, mS i] (fun z : ℕ → ℝ => ∑ i ∈ B, z i) := by
  refine Finset.measurable_sum (m := ⨆ i ∈ S, mS i) B (fun i hi => ?_)
  exact Measurable.mono (comap_measurable (fun z : ℕ → ℝ => z i))
    (le_iSup₂ (f := fun i (_ : i ∈ S) => mS i) i (hB i hi)) le_rfl

theorem mS_mono {S T : Set ℕ} (h : S ⊆ T) : (⨆ i ∈ S, mS i) ≤ (⨆ i ∈ T, mS i) :=
  iSup₂_le fun i hi => le_iSup₂ (f := fun i (_ : i ∈ T) => mS i) i (h hi)

/-- the "no block exceeds" event for blocks `a, ..., a+m-1` -/
def Fs (n0 a : ℕ) : ℕ → Set (ℕ → ℝ)
  | 0 => Set.univ
  | m + 1 => Fs n0 a m ∩ (Tblk n0 (a + m)) ⁻¹' Set.Ici (-sig n0 (a + m))

theorem Fs_meas (n0 a : ℕ) (m : ℕ) :
    MeasurableSet[⨆ i ∈ (↑(Finset.range (Nseq n0 (a + m))) : Set ℕ), mS i] (Fs n0 a m) := by
  induction m with
  | zero => exact MeasurableSet.univ
  | succ m ih =>
    unfold Fs
    refine MeasurableSet.inter ?_ ?_
    · refine (mS_mono ?_) _ ih
      intro i hi
      simp only [Finset.coe_range, Set.mem_Iio] at hi ⊢
      exact lt_of_lt_of_le hi (Nseq_mono n0 (by omega))
    · have hT : Measurable[⨆ i ∈ (↑(Finset.range (Nseq n0 (a + (m + 1)))) : Set ℕ), mS i]
          (Tblk n0 (a + m)) := by
        unfold Tblk
        apply meas_sum_mS
        intro i hi
        simp only [Finset.mem_Ico] at hi
        simp only [Finset.coe_range, Set.mem_Iio]
        exact lt_of_lt_of_le hi.2 (Nseq_mono n0 (by omega))
      exact hT measurableSet_Ici

theorem Tevent_meas (n0 j : ℕ) :
    MeasurableSet[⨆ i ∈ (↑(Finset.Ico (Nseq n0 j) (Nseq n0 (j + 1))) : Set ℕ), mS i]
      ((Tblk n0 j) ⁻¹' Set.Ici (-sig n0 j)) := by
  have hT : Measurable[⨆ i ∈ (↑(Finset.Ico (Nseq n0 j) (Nseq n0 (j + 1))) : Set ℕ), mS i]
      (Tblk n0 j) := by
    unfold Tblk
    apply meas_sum_mS
    intro i hi
    exact hi
  exact hT measurableSet_Ici

theorem Fs_prob (n0 : ℕ) (hn0 : 1 ≤ n0) (a m : ℕ) :
    stdNormalSeq (Fs n0 a m) = (1 - gaussianReal 0 1 (Set.Iio (-1))) ^ m := by
  induction m with
  | zero => simp [Fs]
  | succ m ih =>
    unfold Fs
    have hdis : Disjoint (↑(Finset.range (Nseq n0 (a + m))) : Set ℕ)
        (↑(Finset.Ico (Nseq n0 (a + m)) (Nseq n0 (a + m + 1))) : Set ℕ) := by
      rw [Set.disjoint_left]
      intro i hi hi'
      simp only [Finset.coe_range, Set.mem_Iio, Finset.coe_Ico, Set.mem_Ico] at hi hi'
      omega
    have hind := indep_iSup_of_disjoint mS_le iIndep_mS hdis
    rw [Indep_iff] at hind
    rw [hind _ _ (Fs_meas n0 a m) (Tevent_meas n0 (a + m)), ih, pow_succ]
    congr 1
    have hmeas : MeasurableSet ((Tblk n0 (a + m)) ⁻¹' Set.Iio (-sig n0 (a + m))) :=
      (Tblk_meas n0 _) measurableSet_Iio
    have : (Tblk n0 (a + m)) ⁻¹' Set.Ici (-sig n0 (a + m)) =
        ((Tblk n0 (a + m)) ⁻¹' Set.Iio (-sig n0 (a + m)))ᶜ := by
      ext z; simp
    rw [this, prob_compl_eq_one_sub hmeas]
    congr 1
    exact PD_GEF n0 hn0 (a + m)

theorem Fs_mem (n0 a m : ℕ) (z : ℕ → ℝ) :
    z ∈ Fs n0 a m ↔ ∀ j < m, -sig n0 (a + j) ≤ Tblk n0 (a + j) z := by
  induction m with
  | zero => simp [Fs]
  | succ m ih =>
    unfold Fs
    simp only [Set.mem_inter_iff, ih, Set.mem_preimage, Set.mem_Ici]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
      · exact h1 j h
      · rw [h]; exact h2
    · intro h
      exact ⟨fun j hj => h j (by omega), h m (by omega)⟩

theorem bad_null_GEF (n0 : ℕ) (hn0 : 1 ≤ n0) :
    stdNormalSeq {z : ℕ → ℝ | ¬ ∃ n, n0 ≤ n ∧ zbar z n < 0} = 0 := by
  set c := gaussianReal 0 1 (Set.Iio (-1)) with hcdef
  have hc0 : c ≠ 0 := cpos_GEF
  have hr : 1 - c < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hc0
  set Bad : Set (ℕ → ℝ) := {z | ¬ ∃ n, n0 ≤ n ∧ zbar z n < 0} with hBad
  have hsub : ∀ a m, Bad ⊆ (⋃ j ∈ Finset.range m, {z | sig n0 (a + j) < |Sn (Nseq n0 (a + j)) z|}) ∪
      Fs n0 a m := by
    intro a m z hz
    by_cases hF : z ∈ Fs n0 a m
    · right; exact hF
    · left
      rw [Fs_mem] at hF
      push Not at hF
      obtain ⟨j, hj, hjlt⟩ := hF
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_setOf_eq]
      refine ⟨j, hj, ?_⟩
      by_contra hG
      push Not at hG
      apply hz
      refine ⟨Nseq n0 (a + j + 1), (Nseq_ge n0 _), ?_⟩
      have hsplit : Sn (Nseq n0 (a + j + 1)) z = Sn (Nseq n0 (a + j)) z + Tblk n0 (a + j) z := by
        unfold Sn Tblk
        rw [← Finset.sum_range_add_sum_Ico _ (Nseq_mono n0 (Nat.le_succ (a + j)))]
      have hneg : Sn (Nseq n0 (a + j + 1)) z < 0 := by
        rw [hsplit]
        have := (abs_le.1 hG).2
        linarith
      unfold zbar
      have hpos : (0 : ℝ) < (Nseq n0 (a + j + 1) : ℝ) := by exact_mod_cast Nseq_pos n0 hn0 _
      exact div_neg_of_neg_of_pos hneg hpos
  set p : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal ((1 / 4 : ℝ) ^ j) with hp
  have hpsum : ∑' j, p j ≠ ⊤ := by
    rw [hp]
    have hs : Summable (fun j : ℕ => ((1 / 4 : ℝ) ^ j)) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hs]
    exact ENNReal.ofReal_ne_top
  set T : ℕ → ℝ≥0∞ := fun a => ∑' k, p (k + a) with hT
  have hbound : ∀ a m, stdNormalSeq Bad ≤ T a + (1 - c) ^ m := by
    intro a m
    calc stdNormalSeq Bad ≤ stdNormalSeq ((⋃ j ∈ Finset.range m,
          {z | sig n0 (a + j) < |Sn (Nseq n0 (a + j)) z|}) ∪ Fs n0 a m) := measure_mono (hsub a m)
      _ ≤ stdNormalSeq (⋃ j ∈ Finset.range m, {z | sig n0 (a + j) < |Sn (Nseq n0 (a + j)) z|}) +
          stdNormalSeq (Fs n0 a m) := measure_union_le _ _
      _ ≤ (∑ j ∈ Finset.range m, p (j + a)) + (1 - c) ^ m := by
          gcongr
          · refine (measure_biUnion_finset_le _ _).trans ?_
            apply Finset.sum_le_sum
            intro j _
            rw [add_comm j a]
            exact PG_GEF n0 hn0 (a + j)
          · rw [Fs_prob n0 hn0 a m]
      _ ≤ T a + (1 - c) ^ m := by
          gcongr
          exact ENNReal.sum_le_tsum _
  have h1 : ∀ a, stdNormalSeq Bad ≤ T a := by
    intro a
    have hlim : Tendsto (fun m : ℕ => T a + (1 - c) ^ m) atTop (𝓝 (T a + 0)) :=
      tendsto_const_nhds.add (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr)
    rw [add_zero] at hlim
    exact ge_of_tendsto' hlim (hbound a)
  have h2 : Tendsto T atTop (𝓝 0) := ENNReal.tendsto_sum_nat_add p hpsum
  exact le_antisymm (ge_of_tendsto' h2 h1) bot_le

theorem solution (n0 : ℕ) (hn0 : 1 ≤ n0) :
    ∀ᵐ z ∂GreedyRS.Greedy.stdNormalSeq, GreedyRS.Greedy.argminFrom (GreedyRS.Greedy.zbar z) n0 < ⊤ := by
  have hint : Integrable (fun z : ℕ → ℝ => z 0) stdNormalSeq := by
    have h1 : Integrable (id : ℝ → ℝ) (stdNormalSeq.map (fun z : ℕ → ℝ => z 0)) := by
      rw [coord_law_GEF 0]
      exact (memLp_id_gaussianReal' (μ := 0) (v := 1) 1 ENNReal.one_ne_top).integrable le_rfl
    exact (integrable_map_measure aestronglyMeasurable_id (measurable_pi_apply 0).aemeasurable).1 h1
  have hindep : Pairwise (fun i j => IndepFun (fun z : ℕ → ℝ => z i) (fun z : ℕ → ℝ => z j) stdNormalSeq) :=
    fun i j hij => coord_indep_GEF.indepFun hij
  have hident : ∀ i, IdentDistrib (fun z : ℕ → ℝ => z i) (fun z : ℕ → ℝ => z 0) stdNormalSeq stdNormalSeq :=
    fun i => ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
      by rw [coord_law_GEF i, coord_law_GEF 0]⟩
  have hmean : stdNormalSeq[fun z : ℕ → ℝ => z 0] = 0 := by
    have := integral_map (μ := stdNormalSeq) (φ := fun z : ℕ → ℝ => z 0) (f := fun x : ℝ => x)
      (measurable_pi_apply 0).aemeasurable aestronglyMeasurable_id
    rw [coord_law_GEF 0, integral_id_gaussianReal] at this
    exact this.symm
  have hslln := strong_law_ae_real (fun (j : ℕ) (z : ℕ → ℝ) => z j) hint hindep hident
  have hbad : ∀ᵐ z ∂stdNormalSeq, ∃ n, n0 ≤ n ∧ zbar z n < 0 := by
    rw [ae_iff]
    exact bad_null_GEF n0 hn0
  filter_upwards [hslln, hbad] with z h1 hb
  rw [hmean] at h1
  obtain ⟨n1, hn1, hneg⟩ := hb
  have h1' : Tendsto (zbar z) atTop (𝓝 0) := h1
  have hev : ∀ᶠ n in atTop, zbar z n1 < zbar z n := h1'.eventually (lt_mem_nhds hneg)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.Icc n0 (max N n1)) (zbar z)
    ⟨n1, by simp [hn1, le_max_right]⟩
  have hP : n0 ≤ m ∧ ∀ n, n0 ≤ n → zbar z m ≤ zbar z n := by
    refine ⟨(Finset.mem_Icc.1 hm).1, fun n hn => ?_⟩
    by_cases hnR : n ≤ max N n1
    · exact hmin n (Finset.mem_Icc.2 ⟨hn, hnR⟩)
    · have hNn : N ≤ n := by
        have := le_max_left N n1
        omega
      have h3 := hN n hNn
      have h4 := hmin n1 (Finset.mem_Icc.2 ⟨hn1, le_max_right _ _⟩)
      linarith
  calc argminFrom (zbar z) n0 ≤ (m : ℕ∞) := iInf₂_le m hP
    _ < ⊤ := ENat.coe_lt_top m
