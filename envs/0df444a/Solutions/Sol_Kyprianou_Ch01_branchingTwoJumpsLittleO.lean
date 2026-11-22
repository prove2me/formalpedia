-- Prove2me | solution 1 for Kyprianou.Ch01.branchingTwoJumpsLittleO
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-22T19:38:46.140082+00:00
-- url     : https://prove2.me/submissions/32d165c9-f4e5-4ce6-9da4-5338d7db700c

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace TJ

lemma rc_ev {f : ℝ≥0 → ℕ} {u : ℝ≥0} (h : ContinuousWithinAt f (Ici u) u) :
    ∃ v, u < v ∧ ∀ w ∈ Ico u v, f w = f u := by
  have : {w | f w = f u} ∈ 𝓝[≥] u := h ((isOpen_discrete {f u}).mem_nhds rfl)
  obtain ⟨v, hv, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp this
  exact ⟨v, hv, fun w hw => hsub hw⟩

section Markov
variable {Ω : Type*} [MeasurableSpace Ω]

lemma meas_nat (Y : ℝ≥0 → Ω → ℕ) {u r : ℝ≥0} (hur : u ≤ r) (v : ℕ) :
    @MeasurableSet Ω (naturalSigma (fun u ω => (Y u ω : ℝ)) r) {ω | Y u ω = v} := by
  have hle : MeasurableSpace.comap (fun ω => (Y u ω : ℝ)) inferInstance ≤
      naturalSigma (fun u ω => (Y u ω : ℝ)) r := by
    unfold naturalSigma PerfCorrMSQ.natFiltr
    exact le_iSup₂ (f := fun (u' : ℝ≥0) (_ : u' ≤ r) =>
      MeasurableSpace.comap (fun ω => (Y u' ω : ℝ)) inferInstance) u hur
  apply hle
  exact ⟨{(v:ℝ)}, measurableSet_singleton _, by ext ω; simp⟩

lemma nat_le (Y : ℝ≥0 → Ω → ℕ) (hMeas : ∀ t : ℝ≥0, Measurable (Y t)) (r : ℝ≥0) :
    naturalSigma (fun u ω => (Y u ω : ℝ)) r ≤ ‹MeasurableSpace Ω› := by
  unfold naturalSigma PerfCorrMSQ.natFiltr
  exact iSup₂_le fun u _ => (measurable_from_top.comp (hMeas u)).comap_le

lemma step (Y : ℝ≥0 → Ω → ℕ) (P : ℕ → Measure Ω) (law : PopulationLaws)
    (hMarkov : IsPopulationMarkovPath Y P law) (y : ℕ) {r : ℝ≥0} (h : ℝ≥0) {A : Set Ω}
    (hA : @MeasurableSet Ω (naturalSigma (fun u ω => (Y u ω : ℝ)) r) A) {v : ℕ}
    (hAv : A ⊆ {ω | Y r ω = v}) (w : ℕ) :
    P y (A ∩ {ω | Y (r + h) ω = w}) = P y A * law v h w := by
  rw [hMarkov.2.2 y r h w A hA, tsum_eq_single v]
  · rw [inter_eq_left.mpr hAv]
  · intro u hu
    rw [show A ∩ {ω | Y r ω = u} = ∅ from ?_, measure_empty, zero_mul]
    ext ω
    simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩
    exact hu (h2.symm.trans (hAv h1))

/-- Grid cylinder: value `z` at index `i0`, then value `w` at indices `i0+1, …, i0+1+m`. -/
def Cyl (Y : ℝ≥0 → Ω → ℕ) (h : ℝ≥0) (i0 m z w : ℕ) : Set Ω :=
  {ω | Y ((i0:ℝ≥0) * h) ω = z} ∩ {ω | ∀ j ≤ m, Y (((i0 + 1 + j : ℕ) : ℝ≥0) * h) ω = w}

lemma cyl_meas (Y : ℝ≥0 → Ω → ℕ) (h : ℝ≥0) (i0 m z w : ℕ) :
    @MeasurableSet Ω (naturalSigma (fun u ω => (Y u ω : ℝ)) (((i0 + 1 + m : ℕ) : ℝ≥0) * h))
      (Cyl Y h i0 m z w) := by
  refine MeasurableSet.inter (meas_nat Y ?_ z) ?_
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : i0 ≤ i0 + 1 + m)) bot_le
  · have : {ω | ∀ j ≤ m, Y (((i0 + 1 + j : ℕ) : ℝ≥0) * h) ω = w} =
        ⋂ j ∈ Iic m, {ω | Y (((i0 + 1 + j : ℕ) : ℝ≥0) * h) ω = w} := by
      ext ω; simp
    rw [this]
    refine MeasurableSet.biInter (to_countable _) fun j hj => meas_nat Y ?_ w
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast (by simp at hj; omega : i0 + 1 + j ≤ i0 + 1 + m)) bot_le

lemma cyl_prob (Y : ℝ≥0 → Ω → ℕ) (P : ℕ → Measure Ω) (law : PopulationLaws)
    (hMarkov : IsPopulationMarkovPath Y P law) (y : ℕ) (h : ℝ≥0) (i0 z w : ℕ) :
    ∀ m : ℕ, P y (Cyl Y h i0 m z w) =
      P y {ω | Y ((i0:ℝ≥0) * h) ω = z} * law z h w * (law w h w) ^ m := by
  intro m
  induction m with
  | zero =>
    have e : Cyl Y h i0 0 z w =
        {ω | Y ((i0:ℝ≥0) * h) ω = z} ∩ {ω | Y ((i0:ℝ≥0) * h + h) ω = w} := by
      ext ω
      simp only [Cyl, mem_inter_iff, mem_setOf_eq, nonpos_iff_eq_zero, forall_eq, add_zero]
      have : (((i0 + 1 : ℕ) : ℝ≥0) * h) = (i0:ℝ≥0) * h + h := by push_cast; ring
      rw [this]
    rw [e, step Y P law hMarkov y h (meas_nat Y le_rfl z) (fun ω hω => hω) w, pow_zero, mul_one]
  | succ m ih =>
    have e : Cyl Y h i0 (m + 1) z w = Cyl Y h i0 m z w ∩
        {ω | Y (((i0 + 1 + m : ℕ) : ℝ≥0) * h + h) ω = w} := by
      have ht : (((i0 + 1 + (m + 1) : ℕ) : ℝ≥0) * h) = ((i0 + 1 + m : ℕ) : ℝ≥0) * h + h := by
        push_cast; ring
      ext ω
      simp only [Cyl, mem_inter_iff, mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, fun j hj => h2 j (by omega)⟩, by rw [← ht]; exact h2 (m + 1) le_rfl⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, fun j hj => ?_⟩
        rcases Nat.lt_or_ge j (m + 1) with hj' | hj'
        · exact h2 j (by omega)
        · have : j = m + 1 := by omega
          subst this; rw [ht]; exact h3
    rw [e, step Y P law hMarkov y h (cyl_meas Y h i0 m z w) (fun ω hω => hω.2 m le_rfl) w, ih,
      pow_succ]
    ring

lemma cyl_diff_le (Y : ℝ≥0 → Ω → ℕ) (P : ℕ → Measure Ω) (law : PopulationLaws)
    (hMarkov : IsPopulationMarkovPath Y P law) (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (y : ℕ) (h : ℝ≥0) (i0 m z w : ℕ) :
    P y (Cyl Y h i0 0 z w \ Cyl Y h i0 m z w) ≤ law z h w * (1 - (law w h w) ^ m) := by
  have := hMarkov.1 y
  have hsub : Cyl Y h i0 m z w ⊆ Cyl Y h i0 0 z w := fun ω hω =>
    ⟨hω.1, fun j hj => hω.2 j (by omega)⟩
  have hmeas : MeasurableSet (Cyl Y h i0 m z w) := nat_le Y hMeas _ _ (cyl_meas Y h i0 m z w)
  rw [measure_diff hsub hmeas.nullMeasurableSet (measure_ne_top _ _),
    cyl_prob Y P law hMarkov y h i0 z w m, cyl_prob Y P law hMarkov y h i0 z w 0, pow_zero, mul_one]
  set a := P y {ω | Y ((i0:ℝ≥0) * h) ω = z}
  have ha : a ≤ 1 := prob_le_one
  rw [show a * law z h w - a * law z h w * law w h w ^ m = a * law z h w * (1 - law w h w ^ m) by
    rw [ENNReal.mul_sub (fun _ _ => ENNReal.mul_ne_top (measure_ne_top _ _) (PMF.apply_ne_top _ _)),
      mul_one]]
  calc a * law z h w * (1 - law w h w ^ m) ≤ 1 * law z h w * (1 - law w h w ^ m) := by gcongr
    _ = _ := by rw [one_mul]

end Markov

section ExpBound

lemma law_zero_diag {Ω : Type*} [MeasurableSpace Ω] (Y : ℝ≥0 → Ω → ℕ) (P : ℕ → Measure Ω)
    (law : PopulationLaws) (hMarkov : IsPopulationMarkovPath Y P law)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1) (y : ℕ) : law y 0 y = 1 := by
  rw [← hMarkov.2.1 y 0 y, hInitial]

lemma supermult (law : PopulationLaws) (hSemigroup : IsPopulationMarkovSemigroup law)
    (w : ℕ) (s t : ℝ≥0) : law w s w * law w t w ≤ law w (s + t) w := by
  rw [hSemigroup w s t, PMF.bind_apply]
  exact ENNReal.le_tsum (f := fun a => law w s a * law a t w) w

lemma supermult_pow (law : PopulationLaws) (hSemigroup : IsPopulationMarkovSemigroup law)
    (w : ℕ) (h1 : law w 0 w = 1) (u : ℝ≥0) : ∀ m : ℕ, law w u w ^ m ≤ law w ((m:ℝ≥0) * u) w := by
  intro m
  induction m with
  | zero => simp [h1]
  | succ m ih =>
    calc law w u w ^ (m + 1) = law w u w ^ m * law w u w := pow_succ _ _
      _ ≤ law w ((m:ℝ≥0) * u) w * law w u w := by gcongr
      _ ≤ law w ((m:ℝ≥0) * u + u) w := supermult law hSemigroup w _ _
      _ = law w (((m + 1 : ℕ) : ℝ≥0) * u) w := by congr 2; push_cast; ring

/-- `P_w(Y_u = w) ≥ exp(-λ w u)`. -/
lemma exp_le_diag {Ω : Type*} [MeasurableSpace Ω] (Y : ℝ≥0 → Ω → ℕ) (P : ℕ → Measure Ω)
    (law : PopulationLaws) (rate : ℝ≥0) (offspring : PMF ℕ)
    (hMarkov : IsPopulationMarkovPath Y P law)
    (hSemigroup : IsPopulationMarkovSemigroup law)
    (hGenerator : IsBranchingRateGenerator law rate offspring)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1) (w : ℕ) (u : ℝ≥0) :
    Real.exp (-((rate:ℝ) * w) * u) ≤ (law w u w).toReal := by
  set c0 : ℝ := (rate:ℝ) * w with hc0
  have h1 : law w 0 w = 1 := law_zero_diag Y P law hMarkov hInitial w
  rcases eq_zero_or_pos u with hu | hu
  · subst hu; simp [h1]
  -- slope at zero
  have hd := hGenerator w w
  simp only [if_true] at hd
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left] at hd
  have hsl : Tendsto (fun s : ℝ => ((law w s.toNNReal w).toReal - 1) / s) (𝓝[>] 0)
      (𝓝 (-c0)) := by
    refine hd.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [slope_def_field]
    simp [h1]
  have hu' : (0:ℝ) < u := hu
  -- for every ε > 0, exp(-(c0+ε)u) ≤ f u
  have key : ∀ ε > 0, Real.exp (-(c0 + ε) * u) ≤ (law w u w).toReal := by
    intro ε hε
    have hev : ∀ᶠ s in 𝓝[>] (0:ℝ), 1 - (c0 + ε) * s ≤ (law w s.toNNReal w).toReal := by
      filter_upwards [self_mem_nhdsWithin, (hsl.eventually (lt_mem_nhds (show -c0 - ε < -c0 by linarith)))]
        with s hs hs2
      have hs' : (0:ℝ) < s := hs
      rw [lt_div_iff₀ hs'] at hs2
      nlinarith
    have hseq : Tendsto (fun m : ℕ => (u:ℝ) / m) atTop (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact tendsto_const_div_atTop_nhds_zero_nat (u:ℝ)
      · filter_upwards [eventually_gt_atTop 0] with m hm
        exact div_pos hu' (by exact_mod_cast hm)
    have hev2 := hseq.eventually hev
    have hlim : Tendsto (fun m : ℕ => (1 + (-(c0 + ε) * u) / m) ^ m) atTop
        (𝓝 (Real.exp (-(c0 + ε) * u))) := Real.tendsto_one_add_div_pow_exp _
    refine le_of_tendsto hlim ?_
    have hsmall : ∀ᶠ m : ℕ in atTop, 0 ≤ 1 + (-(c0 + ε) * u) / m := by
      have : Tendsto (fun m : ℕ => 1 + (-(c0 + ε) * u) / m) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _)
      rw [add_zero] at this
      exact this.eventually (le_mem_nhds zero_lt_one)
    filter_upwards [hev2, hsmall, eventually_gt_atTop 0] with m hm hm0 hmpos
    have hmR : (0:ℝ) < m := by exact_mod_cast hmpos
    have heq : (1 + (-(c0 + ε) * u) / m) = 1 - (c0 + ε) * ((u:ℝ) / m) := by ring
    rw [heq] at hm0 ⊢
    have hnn : ((u:ℝ) / m).toNNReal = u / (m:ℝ≥0) := by
      rw [Real.toNNReal_div (NNReal.coe_nonneg u)]; simp
    rw [hnn] at hm
    calc (1 - (c0 + ε) * ((u:ℝ) / m)) ^ m ≤ ((law w (u / (m:ℝ≥0)) w).toReal) ^ m :=
          pow_le_pow_left₀ hm0 hm m
      _ = ((law w (u / (m:ℝ≥0)) w) ^ m).toReal := by rw [ENNReal.toReal_pow]
      _ ≤ (law w ((m:ℝ≥0) * (u / (m:ℝ≥0))) w).toReal :=
          ENNReal.toReal_mono (PMF.apply_ne_top _ _) (supermult_pow law hSemigroup w h1 _ m)
      _ = (law w u w).toReal := by
          rw [mul_div_cancel₀ _ (by exact_mod_cast hmpos.ne' : (m:ℝ≥0) ≠ 0)]
  have hcont : Tendsto (fun ε : ℝ => Real.exp (-(c0 + ε) * u)) (𝓝[>] 0)
      (𝓝 (Real.exp (-c0 * u))) := by
    have : Continuous (fun ε : ℝ => Real.exp (-(c0 + ε) * u)) := by fun_prop
    have h2 := this.tendsto 0
    simp only [add_zero] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hcont ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact key ε hε

end ExpBound

section Gen
variable {Ω : Type*} [MeasurableSpace Ω]

lemma law_zero_off (Y : ℝ≥0 → Ω → ℕ) (P : ℕ → Measure Ω) (law : PopulationLaws)
    (hMarkov : IsPopulationMarkovPath Y P law)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1) (z w : ℕ) (hw : w ≠ z) : law z 0 w = 0 := by
  have h1 := law_zero_diag Y P law hMarkov hInitial z
  have hs := (PMF.apply_eq_one_iff _ _).mp h1
  rw [PMF.apply_eq_zero_iff, hs]
  simpa using hw

/-- Limiting jump rates `q(z,w)` off the diagonal. -/
noncomputable def A (rate : ℝ≥0) (offspring : PMF ℕ) (z w : ℕ) : ℝ :=
  if w = z then 0 else if z ≤ w + 1 then (rate:ℝ) * z * (offspring (w + 1 - z)).toReal else 0

lemma A_nonneg (rate : ℝ≥0) (offspring : PMF ℕ) (z w : ℕ) : 0 ≤ A rate offspring z w := by
  unfold A; split_ifs <;> positivity

lemma off_slope (Y : ℝ≥0 → Ω → ℕ) (P : ℕ → Measure Ω) (law : PopulationLaws)
    (rate : ℝ≥0) (offspring : PMF ℕ) (hMarkov : IsPopulationMarkovPath Y P law)
    (hGenerator : IsBranchingRateGenerator law rate offspring)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1) (z w : ℕ) (hw : w ≠ z) :
    Tendsto (fun s : ℝ => (law z s.toNNReal w).toReal / s) (𝓝[>] 0)
      (𝓝 (A rate offspring z w)) := by
  have hd := hGenerator z w
  rw [if_neg hw] at hd
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left] at hd
  unfold A
  rw [if_neg hw]
  refine hd.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [slope_def_field]
  simp [law_zero_off Y P law hMarkov hInitial z w hw]

lemma diag_slope (Y : ℝ≥0 → Ω → ℕ) (P : ℕ → Measure Ω) (law : PopulationLaws)
    (rate : ℝ≥0) (offspring : PMF ℕ) (hMarkov : IsPopulationMarkovPath Y P law)
    (hGenerator : IsBranchingRateGenerator law rate offspring)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1) (z : ℕ) :
    Tendsto (fun s : ℝ => (1 - (law z s.toNNReal z).toReal) / s) (𝓝[>] 0)
      (𝓝 ((rate:ℝ) * z)) := by
  have hd := hGenerator z z
  rw [if_pos rfl] at hd
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left] at hd
  have h2 := hd.neg
  rw [neg_neg] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [slope_def_field]
  simp [law_zero_diag Y P law hMarkov hInitial z]
  ring

end Gen

lemma pmf_summable (p : PMF ℕ) : Summable (fun n => (p n).toReal) :=
  ENNReal.summable_toReal (by rw [p.tsum_coe]; exact ENNReal.one_ne_top)

lemma pmf_tsum (p : PMF ℕ) : ∑' n, (p n).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun n => PMF.apply_ne_top p n), PMF.tsum_coe, ENNReal.toReal_one]

lemma pmf_off (p : PMF ℕ) (z : ℕ) :
    ∑' w, (if w = z then 0 else (p w).toReal) = 1 - (p z).toReal := by
  have := (pmf_summable p).tsum_eq_add_tsum_ite z
  rw [pmf_tsum] at this
  linarith

lemma hk_tendsto {Tn : ℝ≥0} (hT : 0 < Tn) :
    Tendsto (fun k : ℕ => ((Tn / 2 ^ k : ℝ≥0) : ℝ)) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h1 : Tendsto (fun k : ℕ => ((2:ℝ) ^ k)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    have h2 := h1.const_mul (Tn:ℝ)
    rw [mul_zero] at h2
    refine h2.congr fun k => ?_
    push_cast; ring
  · exact Eventually.of_forall fun k => by
      show (0:ℝ) < ((Tn / 2 ^ k : ℝ≥0) : ℝ)
      exact_mod_cast div_pos hT (by positivity)

section Grid
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Two changes on the dyadic grid of mesh `Tn / 2^k`. -/
def E (Y : ℝ≥0 → Ω → ℕ) (Tn : ℝ≥0) (k : ℕ) : Set Ω :=
  {ω | ∃ i j l : ℕ, i < j ∧ j < l ∧ l ≤ 2 ^ k ∧
    Y ((i:ℝ≥0) * (Tn / 2 ^ k)) ω ≠ Y ((j:ℝ≥0) * (Tn / 2 ^ k)) ω ∧
    Y ((j:ℝ≥0) * (Tn / 2 ^ k)) ω ≠ Y ((l:ℝ≥0) * (Tn / 2 ^ k)) ω}

lemma E_mono (Y : ℝ≥0 → Ω → ℕ) (Tn : ℝ≥0) : Monotone (E Y Tn) := by
  refine monotone_nat_of_le_succ fun k ω hω => ?_
  obtain ⟨i, j, l, hij, hjl, hln, h1, h2⟩ := hω
  have ht : ∀ q : ℕ, (((2 * q : ℕ) : ℝ≥0) * (Tn / 2 ^ (k + 1))) = (q:ℝ≥0) * (Tn / 2 ^ k) := by
    intro q; push_cast; rw [pow_succ]; field_simp
  refine ⟨2 * i, 2 * j, 2 * l, by omega, by omega, by rw [pow_succ]; omega, ?_, ?_⟩
  · rw [ht, ht]; exact h1
  · rw [ht, ht]; exact h2

lemma E_incl (Y : ℝ≥0 → Ω → ℕ) (z : ℕ) (Tn : ℝ≥0) (k : ℕ) :
    E Y Tn k ⊆ {ω | Y 0 ω ≠ z} ∪ ⋃ i0 ∈ Finset.range (2 ^ k), ⋃ w, ⋃ (_ : w ≠ z),
      (Cyl Y (Tn / 2 ^ k) i0 0 z w \ Cyl Y (Tn / 2 ^ k) i0 (2 ^ k - i0 - 1) z w) := by
  classical
  intro ω hω
  obtain ⟨i, j, l, hij, hjl, hln, h1, h2⟩ := hω
  by_cases h0 : Y 0 ω = z
  · right
    set h : ℝ≥0 := Tn / 2 ^ k with hh
    set n : ℕ := 2 ^ k with hn
    set X : ℕ → ℕ := fun q => Y ((q:ℝ≥0) * h) ω with hX
    have hX0 : X 0 = z := by simp [hX, h0]
    have hex : ∃ p, p ≤ n ∧ X p ≠ z := by
      by_cases hi : X i = z
      · exact ⟨j, by omega, fun hj => h1 (hi.trans hj.symm)⟩
      · exact ⟨i, by omega, hi⟩
    have hp := Nat.find_spec hex
    have hmin : ∀ q < Nat.find hex, q ≤ n → X q = z := fun q hq hqn => by
      have := Nat.find_min hex hq
      push Not at this
      exact this hqn
    have hp0 : Nat.find hex ≠ 0 := fun h' => hp.2 (by rw [h']; exact hX0)
    obtain ⟨i0, hi0⟩ : ∃ i0, Nat.find hex = i0 + 1 := ⟨Nat.find hex - 1, by omega⟩
    simp only [mem_iUnion, Finset.mem_range]
    refine ⟨i0, by omega, X (Nat.find hex), hp.2, ⟨hmin i0 (by omega) (by omega), ?_⟩, ?_⟩
    · intro j' hj'
      have : j' = 0 := by omega
      subst this
      show X (i0 + 1 + 0) = X (Nat.find hex)
      rw [hi0]
    · rintro ⟨-, hall⟩
      have hw : ∀ q, Nat.find hex ≤ q → q ≤ n → X q = X (Nat.find hex) := fun q hq hqn => by
        have := hall (q - Nat.find hex) (by omega)
        rw [show i0 + 1 + (q - Nat.find hex) = q by omega] at this
        exact this
      rcases Nat.lt_or_ge j (Nat.find hex) with hjp | hjp
      · exact h1 ((hmin i (by omega) (by omega)).trans (hmin j hjp (by omega)).symm)
      · exact h2 ((hw j hjp (by omega)).trans (hw l (by omega) hln).symm)
  · left; exact h0

lemma one_sub_pow_le (Y : ℝ≥0 → Ω → ℕ) (P : ℕ → Measure Ω)
    (law : PopulationLaws) (rate : ℝ≥0) (offspring : PMF ℕ)
    (hMarkov : IsPopulationMarkovPath Y P law)
    (hSemigroup : IsPopulationMarkovSemigroup law)
    (hGenerator : IsBranchingRateGenerator law rate offspring)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1) (w m : ℕ) (h Tn : ℝ≥0)
    (hm : (m:ℝ≥0) * h ≤ Tn) :
    1 - law w h w ^ m ≤ ENNReal.ofReal (1 - Real.exp (-((rate:ℝ) * w) * Tn)) := by
  have he := exp_le_diag Y P law rate offspring hMarkov hSemigroup hGenerator hInitial w h
  have hc : 0 ≤ (rate:ℝ) * w := by positivity
  have hmR : (m:ℝ) * h ≤ Tn := by exact_mod_cast hm
  have h1 : Real.exp (-((rate:ℝ) * w) * Tn) ≤ (law w h w ^ m).toReal := by
    rw [ENNReal.toReal_pow]
    calc Real.exp (-((rate:ℝ) * w) * Tn) ≤ Real.exp (m * (-((rate:ℝ) * w) * h)) := by
          apply Real.exp_le_exp.mpr
          nlinarith
      _ = Real.exp (-((rate:ℝ) * w) * h) ^ m := Real.exp_nat_mul _ _
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le he m
  have h2 : ENNReal.ofReal (Real.exp (-((rate:ℝ) * w) * Tn)) ≤ law w h w ^ m :=
    (ENNReal.ofReal_le_iff_le_toReal (ENNReal.pow_ne_top (PMF.apply_ne_top _ _))).mpr h1
  rw [ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one]
  exact tsub_le_tsub_left h2 1

/-- Off-diagonal weight on the grid. -/
noncomputable def cw (law : PopulationLaws) (rate : ℝ≥0) (z : ℕ) (h Tn : ℝ≥0) (w : ℕ) : ℝ≥0∞ :=
  if w = z then 0 else law z h w * ENNReal.ofReal (1 - Real.exp (-((rate:ℝ) * w) * Tn))

lemma E_prob (Y : ℝ≥0 → Ω → ℕ) (P : ℕ → Measure Ω)
    (law : PopulationLaws) (rate : ℝ≥0) (offspring : PMF ℕ)
    (hMarkov : IsPopulationMarkovPath Y P law)
    (hSemigroup : IsPopulationMarkovSemigroup law)
    (hGenerator : IsBranchingRateGenerator law rate offspring)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1) (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (z : ℕ) (Tn : ℝ≥0) (k : ℕ) :
    P z (E Y Tn k) ≤ (2 ^ k : ℝ≥0∞) * ∑' w, cw law rate z (Tn / 2 ^ k) Tn w := by
  have hY0 : P z {ω | Y 0 ω ≠ z} = 0 := by
    have := hMarkov.1 z
    have hm : MeasurableSet {ω | Y 0 ω = z} := (measurableSet_singleton z).preimage (hMeas 0)
    have : {ω | Y 0 ω ≠ z} = {ω | Y 0 ω = z}ᶜ := by ext; simp
    rw [this, prob_compl_eq_zero_iff hm, hInitial]
  calc P z (E Y Tn k) ≤ P z ({ω | Y 0 ω ≠ z} ∪ ⋃ i0 ∈ Finset.range (2 ^ k), ⋃ w, ⋃ (_ : w ≠ z),
      (Cyl Y (Tn / 2 ^ k) i0 0 z w \ Cyl Y (Tn / 2 ^ k) i0 (2 ^ k - i0 - 1) z w)) :=
        measure_mono (E_incl Y z Tn k)
    _ ≤ P z {ω | Y 0 ω ≠ z} + P z (⋃ i0 ∈ Finset.range (2 ^ k), ⋃ w, ⋃ (_ : w ≠ z),
      (Cyl Y (Tn / 2 ^ k) i0 0 z w \ Cyl Y (Tn / 2 ^ k) i0 (2 ^ k - i0 - 1) z w)) :=
        measure_union_le _ _
    _ ≤ ∑ i0 ∈ Finset.range (2 ^ k), P z (⋃ w, ⋃ (_ : w ≠ z),
      (Cyl Y (Tn / 2 ^ k) i0 0 z w \ Cyl Y (Tn / 2 ^ k) i0 (2 ^ k - i0 - 1) z w)) := by
        rw [hY0, zero_add]; exact measure_biUnion_finset_le _ _
    _ ≤ ∑ i0 ∈ Finset.range (2 ^ k), ∑' w, cw law rate z (Tn / 2 ^ k) Tn w := by
        refine Finset.sum_le_sum fun i0 hi0 => (measure_iUnion_le _).trans
          (ENNReal.tsum_le_tsum fun w => ?_)
        unfold cw
        by_cases hw : w = z
        · simp [hw]
        · rw [if_neg hw]
          refine (measure_mono (iUnion_subset fun _ => subset_rfl)).trans ?_
          refine (cyl_diff_le Y P law hMarkov hMeas z _ i0 _ z w).trans ?_
          gcongr
          refine one_sub_pow_le Y P law rate offspring hMarkov hSemigroup hGenerator hInitial
            w _ _ Tn ?_
          have hi0' : i0 < 2 ^ k := Finset.mem_range.mp hi0
          calc ((2 ^ k - i0 - 1 : ℕ) : ℝ≥0) * (Tn / 2 ^ k) ≤ ((2 ^ k : ℕ) : ℝ≥0) * (Tn / 2 ^ k) := by
                gcongr; omega
            _ = Tn := by push_cast; field_simp
    _ = (2 ^ k : ℝ≥0∞) * ∑' w, cw law rate z (Tn / 2 ^ k) Tn w := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; rfl

end Grid

section Limits

lemma scheffe {a : ℕ → ℕ → ℝ} {B : ℕ → ℝ} {L : ℝ} {φ : ℕ → ℝ}
    (ha0 : ∀ k w, 0 ≤ a k w) (hB0 : ∀ w, 0 ≤ B w) (hsum : ∀ k, Summable (a k))
    (hB : Summable B)
    (hpt : ∀ w, Tendsto (fun k => a k w) atTop (𝓝 (B w)))
    (hL : Tendsto (fun k => ∑' w, a k w) atTop (𝓝 L))
    (hφ0 : ∀ w, 0 ≤ φ w) (hφ1 : ∀ w, φ w ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∑' w, a k w * φ w ≤ L - ∑' w, B w * (1 - φ w) + ε := by
  have hB' : Summable (fun w => B w * (1 - φ w)) :=
    hB.of_nonneg_of_le (fun w => mul_nonneg (hB0 w) (by linarith [hφ1 w]))
      (fun w => by nlinarith [hφ0 w, hB0 w])
  obtain ⟨N, hN⟩ : ∃ N, ∑' w, B w * (1 - φ w) - ε / 3 <
      ∑ w ∈ Finset.range N, B w * (1 - φ w) :=
    ((hB'.hasSum.tendsto_sum_nat).eventually
      (lt_mem_nhds (show ∑' w, B w * (1 - φ w) - ε / 3 < _ by linarith))).exists
  have hfin : Tendsto (fun k => ∑ w ∈ Finset.range N, a k w * (1 - φ w)) atTop
      (𝓝 (∑ w ∈ Finset.range N, B w * (1 - φ w))) :=
    tendsto_finset_sum _ fun w _ => (hpt w).mul_const _
  filter_upwards [hfin.eventually (lt_mem_nhds (show ∑ w ∈ Finset.range N, B w * (1 - φ w)
      - ε / 3 < _ by linarith)), hL.eventually (gt_mem_nhds (show L < L + ε / 3 by linarith))]
    with k hk1 hk2
  have hs2 : Summable (fun w => a k w * (1 - φ w)) :=
    (hsum k).of_nonneg_of_le (fun w => mul_nonneg (ha0 k w) (by linarith [hφ1 w]))
      (fun w => by nlinarith [ha0 k w, hφ0 w])
  have hsplit : ∑' w, a k w * φ w = ∑' w, a k w - ∑' w, a k w * (1 - φ w) := by
    rw [← (hsum k).tsum_sub hs2]; congr 1; funext w; ring
  have hle : ∑ w ∈ Finset.range N, a k w * (1 - φ w) ≤ ∑' w, a k w * (1 - φ w) :=
    hs2.sum_le_tsum _ (fun w _ => mul_nonneg (ha0 k w) (by linarith [hφ1 w]))
  linarith

lemma summable_of_lim {a : ℕ → ℕ → ℝ} {B : ℕ → ℝ} {L : ℝ}
    (ha0 : ∀ k w, 0 ≤ a k w) (hB0 : ∀ w, 0 ≤ B w) (hsum : ∀ k, Summable (a k))
    (hpt : ∀ w, Tendsto (fun k => a k w) atTop (𝓝 (B w)))
    (hL : Tendsto (fun k => ∑' w, a k w) atTop (𝓝 L)) : Summable B := by
  refine summable_of_sum_range_le hB0 (c := L) fun N => ?_
  have hfin : Tendsto (fun k => ∑ w ∈ Finset.range N, a k w) atTop
      (𝓝 (∑ w ∈ Finset.range N, B w)) := tendsto_finset_sum _ fun w _ => hpt w
  exact le_of_tendsto_of_tendsto' hfin hL fun k => (hsum k).sum_le_tsum _ (fun w _ => ha0 k w)

lemma A_sum_ge (rate : ℝ≥0) (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0) (z : ℕ)
    (hA : Summable (A rate offspring z)) : (rate:ℝ) * z ≤ ∑' w, A rate offspring z w := by
  rcases Nat.eq_zero_or_pos z with hz | hz
  · subst hz; simp only [Nat.cast_zero, mul_zero]
    exact tsum_nonneg (A_nonneg rate offspring 0)
  · have hinj : Function.Injective (fun m : ℕ => m + z - 1) := fun m1 m2 h => by
      simp only at h; omega
    have h1 := tsum_comp_le_tsum_of_inj hA (A_nonneg rate offspring z) hinj
    have h2 : (A rate offspring z ∘ fun m : ℕ => m + z - 1) =
        fun m => (rate:ℝ) * z * (offspring m).toReal := by
      funext m
      simp only [Function.comp, A]
      by_cases hm : m = 1
      · subst hm; simp [hNoNullJumps]
      · rw [if_neg (by omega), if_pos (by omega), show m + z - 1 + 1 - z = m by omega]
    rw [h2, tsum_mul_left, pmf_tsum, mul_one] at h1
    exact h1

end Limits

section Main
variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def ak (law : PopulationLaws) (z : ℕ) (Tn : ℝ≥0) (k w : ℕ) : ℝ :=
  if w = z then 0 else (law z (Tn / 2 ^ k) w).toReal / ((Tn / 2 ^ k : ℝ≥0) : ℝ)

lemma ak_nonneg (law : PopulationLaws) (z : ℕ) (Tn : ℝ≥0) (k w : ℕ) : 0 ≤ ak law z Tn k w := by
  unfold ak; split_ifs <;> positivity

lemma ak_summable (law : PopulationLaws) (z : ℕ) (Tn : ℝ≥0) (k : ℕ) :
    Summable (ak law z Tn k) :=
  ((pmf_summable (law z (Tn / 2 ^ k))).div_const ((Tn / 2 ^ k : ℝ≥0) : ℝ)).of_nonneg_of_le
    (ak_nonneg law z Tn k) (fun w => by
      unfold ak; split_ifs
      · positivity
      · exact le_rfl)

lemma ak_tsum (law : PopulationLaws) (z : ℕ) (Tn : ℝ≥0) (k : ℕ) :
    ∑' w, ak law z Tn k w =
      (1 - (law z (Tn / 2 ^ k) z).toReal) / ((Tn / 2 ^ k : ℝ≥0) : ℝ) := by
  have : ak law z Tn k = fun w =>
      (if w = z then 0 else (law z (Tn / 2 ^ k) w).toReal) / ((Tn / 2 ^ k : ℝ≥0) : ℝ) := by
    funext w; unfold ak; split_ifs <;> simp
  rw [this, tsum_div_const, pmf_off]

lemma ak_pt (Y : ℝ≥0 → Ω → ℕ) (P : ℕ → Measure Ω) (law : PopulationLaws)
    (rate : ℝ≥0) (offspring : PMF ℕ) (hMarkov : IsPopulationMarkovPath Y P law)
    (hGenerator : IsBranchingRateGenerator law rate offspring)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1) (z : ℕ) {Tn : ℝ≥0} (hT : 0 < Tn) (w : ℕ) :
    Tendsto (fun k => ak law z Tn k w) atTop (𝓝 (A rate offspring z w)) := by
  by_cases hw : w = z
  · subst hw; simp [ak, A]
  · refine ((off_slope Y P law rate offspring hMarkov hGenerator hInitial z w hw).comp
      (hk_tendsto hT)).congr fun k => ?_
    show (law z (Real.toNNReal ((Tn / 2 ^ k : ℝ≥0) : ℝ)) w).toReal / ((Tn / 2 ^ k : ℝ≥0) : ℝ) = _
    rw [Real.toNNReal_coe]
    simp [ak, hw]

lemma ak_L (Y : ℝ≥0 → Ω → ℕ) (P : ℕ → Measure Ω) (law : PopulationLaws)
    (rate : ℝ≥0) (offspring : PMF ℕ) (hMarkov : IsPopulationMarkovPath Y P law)
    (hGenerator : IsBranchingRateGenerator law rate offspring)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1) (z : ℕ) {Tn : ℝ≥0} (hT : 0 < Tn) :
    Tendsto (fun k => ∑' w, ak law z Tn k w) atTop (𝓝 ((rate:ℝ) * z)) := by
  refine ((diag_slope Y P law rate offspring hMarkov hGenerator hInitial z).comp
      (hk_tendsto hT)).congr fun k => ?_
  show (1 - (law z (Real.toNNReal ((Tn / 2 ^ k : ℝ≥0) : ℝ)) z).toReal) / ((Tn / 2 ^ k : ℝ≥0) : ℝ) = _
  rw [Real.toNNReal_coe, ak_tsum]

lemma Ek_real (Y : ℝ≥0 → Ω → ℕ) (P : ℕ → Measure Ω)
    (law : PopulationLaws) (rate : ℝ≥0) (offspring : PMF ℕ)
    (hMarkov : IsPopulationMarkovPath Y P law)
    (hSemigroup : IsPopulationMarkovSemigroup law)
    (hGenerator : IsBranchingRateGenerator law rate offspring)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1) (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (z : ℕ) {Tn : ℝ≥0} (hT : 0 < Tn) (k : ℕ) :
    (P z (E Y Tn k)).toReal ≤
      (Tn:ℝ) * ∑' w, ak law z Tn k w * (1 - Real.exp (-((rate:ℝ) * w) * Tn)) := by
  set h : ℝ≥0 := Tn / 2 ^ k with hh
  have hpos : (0:ℝ) < h := by exact_mod_cast div_pos hT (by positivity)
  have hcw : ∀ w, cw law rate z h Tn w ≤ law z h w := fun w => by
    unfold cw; split_ifs
    · exact bot_le
    · calc law z h w * ENNReal.ofReal (1 - Real.exp (-((rate:ℝ) * w) * Tn))
          ≤ law z h w * 1 := by
            gcongr; exact ENNReal.ofReal_le_one.mpr (by linarith [Real.exp_pos (-((rate:ℝ) * w) * Tn)])
        _ = _ := mul_one _
  have hcwt : ∀ w, cw law rate z h Tn w ≠ ⊤ := fun w => ne_top_of_le_ne_top (PMF.apply_ne_top _ _) (hcw w)
  have hsum_ne : ∑' w, cw law rate z h Tn w ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top) (ENNReal.tsum_le_tsum hcw)
  have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hsum_ne)
    (E_prob Y P law rate offspring hMarkov hSemigroup hGenerator hInitial hMeas z Tn k)
  rw [ENNReal.toReal_mul, ENNReal.tsum_toReal_eq hcwt] at h1
  refine h1.trans (le_of_eq ?_)
  have hpt : ∀ w, (cw law rate z h Tn w).toReal =
      (h:ℝ) * (ak law z Tn k w * (1 - Real.exp (-((rate:ℝ) * w) * Tn))) := by
    intro w
    unfold cw ak
    split_ifs
    · simp
    · have hle : -((rate:ℝ) * w) * Tn ≤ 0 := by
        have : 0 ≤ (rate:ℝ) * w * Tn := by positivity
        linarith
      have hexp : 0 ≤ 1 - Real.exp (-((rate:ℝ) * w) * Tn) := by
        linarith [Real.exp_le_one_iff.mpr hle]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hexp, ← hh]
      field_simp
  simp_rw [hpt]
  rw [show ((2:ℝ≥0∞) ^ k).toReal = (2:ℝ) ^ k by simp, tsum_mul_left, ← mul_assoc]
  congr 1
  rw [hh]; push_cast; field_simp

lemma grid_pt {x v Tn : ℝ≥0} (hxv : x < v) (hxT : x ≤ Tn) (hT : 0 < Tn) :
    ∀ᶠ k : ℕ in atTop, ⌈x / (Tn / 2 ^ k)⌉₊ ≤ 2 ^ k ∧
      x ≤ (⌈x / (Tn / 2 ^ k)⌉₊ : ℝ≥0) * (Tn / 2 ^ k) ∧
      (⌈x / (Tn / 2 ^ k)⌉₊ : ℝ≥0) * (Tn / 2 ^ k) < v := by
  have hsm := (hk_tendsto hT).mono_right nhdsWithin_le_nhds
  filter_upwards [hsm.eventually (gt_mem_nhds (show (0:ℝ) < (v:ℝ) - x by
    have := NNReal.coe_lt_coe.mpr hxv; linarith))] with k hk
  set h : ℝ≥0 := Tn / 2 ^ k with hh
  have hpos : 0 < h := div_pos hT (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · apply Nat.ceil_le.mpr
    calc x / h ≤ Tn / h := by gcongr
      _ = ((2 ^ k : ℕ) : ℝ≥0) := by rw [hh]; push_cast; field_simp
  · exact (div_le_iff₀ hpos).mp (Nat.le_ceil _)
  · have h1 : (⌈x / h⌉₊ : ℝ≥0) < x / h + 1 := Nat.ceil_lt_add_one bot_le
    have h2 : (⌈x / h⌉₊ : ℝ≥0) * h < (x / h + 1) * h := mul_lt_mul_of_pos_right h1 hpos
    rw [add_mul, div_mul_cancel₀ _ hpos.ne', one_mul] at h2
    refine lt_of_lt_of_le h2 ?_
    rw [← NNReal.coe_le_coe]; push_cast
    linarith

lemma DT_incl (Y : ℝ≥0 → Ω → ℕ) {T : ℝ} (hT : 0 < T) :
    {ω | ∃ a b c : ℝ≥0, a < b ∧ b < c ∧ (c : ℝ) ≤ T ∧ Y a ω ≠ Y b ω ∧ Y b ω ≠ Y c ω} ⊆
      {ω | ¬ IsCadlag (fun t : ℝ≥0 => Y t ω)} ∪ ⋃ k, E Y T.toNNReal k := by
  intro ω hω
  obtain ⟨a, b, c, hab, hbc, hcT, h1, h2⟩ := hω
  by_cases hc : IsCadlag (fun t : ℝ≥0 => Y t ω)
  · right
    have hTn : 0 < T.toNNReal := Real.toNNReal_pos.mpr hT
    have hcT' : c ≤ T.toNNReal := (Real.le_toNNReal_iff_coe_le hT.le).mpr hcT
    obtain ⟨va, hva, hvca⟩ := rc_ev (hc a).1
    obtain ⟨vb, hvb, hvcb⟩ := rc_ev (hc b).1
    obtain ⟨vc, hvc, hvcc⟩ := rc_ev (hc c).1
    have ea := grid_pt (lt_min hva hab) (hab.le.trans (hbc.le.trans hcT')) hTn
    have eb := grid_pt (lt_min hvb hbc) (hbc.le.trans hcT') hTn
    have ec := grid_pt hvc hcT' hTn
    obtain ⟨k, ⟨ia1, ia2, ia3⟩, ⟨ib1, ib2, ib3⟩, ⟨ic1, ic2, ic3⟩⟩ := (ea.and (eb.and ec)).exists
    set h : ℝ≥0 := T.toNNReal / 2 ^ k with hh
    have hpos : 0 < h := div_pos hTn (by positivity)
    have hlt : ∀ m n : ℕ, (m:ℝ≥0) * h < (n:ℝ≥0) * h → m < n := fun m n hmn => by
      exact_mod_cast lt_of_mul_lt_mul_right hmn bot_le
    refine mem_iUnion.mpr ⟨k, ⌈a / h⌉₊, ⌈b / h⌉₊, ⌈c / h⌉₊, ?_, ?_, ic1, ?_, ?_⟩
    · exact hlt _ _ (lt_of_lt_of_le (lt_of_lt_of_le ia3 (min_le_right _ _)) ib2)
    · exact hlt _ _ (lt_of_lt_of_le (lt_of_lt_of_le ib3 (min_le_right _ _)) ic2)
    · rw [hvca _ ⟨ia2, lt_of_lt_of_le ia3 (min_le_left _ _)⟩,
        hvcb _ ⟨ib2, lt_of_lt_of_le ib3 (min_le_left _ _)⟩]
      exact h1
    · rw [hvcb _ ⟨ib2, lt_of_lt_of_le ib3 (min_le_left _ _)⟩, hvcc _ ⟨ic2, ic3⟩]
      exact h2
  · left; exact hc

lemma main_bound (Y : ℝ≥0 → Ω → ℕ) (P : ℕ → Measure Ω)
    (law : PopulationLaws) (rate : ℝ≥0) (offspring : PMF ℕ)
    (hMarkov : IsPopulationMarkovPath Y P law)
    (hSemigroup : IsPopulationMarkovSemigroup law)
    (hGenerator : IsBranchingRateGenerator law rate offspring)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1) (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ y : ℕ, ∀ᵐ ω ∂P y, IsCadlag (fun t : ℝ≥0 => Y t ω))
    (z : ℕ) (hAs : Summable (A rate offspring z)) {T : ℝ} (hT : 0 < T) :
    (P z {ω | ∃ a b c : ℝ≥0, a < b ∧ b < c ∧ (c : ℝ) ≤ T ∧
        Y a ω ≠ Y b ω ∧ Y b ω ≠ Y c ω}).toReal ≤
      T * ((rate:ℝ) * z - ∑' w, A rate offspring z w * Real.exp (-((rate:ℝ) * w) * T)) := by
  have := hMarkov.1 z
  set Tn := T.toNNReal with hTn_def
  have hTn : (Tn:ℝ) = T := Real.coe_toNNReal _ hT.le
  have hTpos : 0 < Tn := Real.toNNReal_pos.mpr hT
  set Ψ := (rate:ℝ) * z - ∑' w, A rate offspring z w * Real.exp (-((rate:ℝ) * w) * T) with hΨ
  set φ : ℕ → ℝ := fun w => 1 - Real.exp (-((rate:ℝ) * w) * T) with hφ
  have hφ0 : ∀ w, 0 ≤ φ w := fun w => by
    have : Real.exp (-((rate:ℝ) * w) * T) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have : 0 ≤ (rate:ℝ) * w * T := by positivity
      linarith)
    simp only [hφ]; linarith
  have hφ1 : ∀ w, φ w ≤ 1 := fun w => by simp only [hφ]; linarith [Real.exp_pos (-((rate:ℝ) * w) * T)]
  have hN : P z {ω | ¬ IsCadlag (fun t : ℝ≥0 => Y t ω)} = 0 := ae_iff.mp (hCadlag z)
  have hmain : ∀ ε > 0, (P z {ω | ∃ a b c : ℝ≥0, a < b ∧ b < c ∧ (c : ℝ) ≤ T ∧
      Y a ω ≠ Y b ω ∧ Y b ω ≠ Y c ω}).toReal ≤ T * (Ψ + ε) := by
    intro ε hε
    have hsch := scheffe (ak_nonneg law z Tn) (A_nonneg rate offspring z) (ak_summable law z Tn)
      hAs (ak_pt Y P law rate offspring hMarkov hGenerator hInitial z hTpos)
      (ak_L Y P law rate offspring hMarkov hGenerator hInitial z hTpos) hφ0 hφ1 hε
    have he : ∑' w, A rate offspring z w * (1 - φ w) =
        ∑' w, A rate offspring z w * Real.exp (-((rate:ℝ) * w) * T) := by
      congr 1; funext w; simp only [hφ]; ring
    rw [he] at hsch
    obtain ⟨K, hK⟩ := eventually_atTop.mp hsch
    have hEK : ∀ k, K ≤ k → (P z (E Y Tn k)).toReal ≤ T * (Ψ + ε) := fun k hk => by
      have h1 := Ek_real Y P law rate offspring hMarkov hSemigroup hGenerator hInitial hMeas z
        hTpos k
      rw [hTn] at h1
      calc _ ≤ T * ∑' w, ak law z Tn k w * φ w := h1
        _ ≤ T * (Ψ + ε) := by
          have := hK k hk
          gcongr
    have hnn : 0 ≤ T * (Ψ + ε) := ENNReal.toReal_nonneg.trans (hEK K le_rfl)
    have hEle : ∀ k, P z (E Y Tn k) ≤ ENNReal.ofReal (T * (Ψ + ε)) := fun k => by
      calc P z (E Y Tn k) ≤ P z (E Y Tn (max k K)) := measure_mono (E_mono Y Tn (le_max_left k K))
        _ ≤ _ := (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hnn).mpr
            (hEK _ (le_max_right k K))
    apply ENNReal.toReal_le_of_le_ofReal hnn
    calc _ ≤ P z ({ω | ¬ IsCadlag (fun t : ℝ≥0 => Y t ω)} ∪ ⋃ k, E Y Tn k) :=
          measure_mono (DT_incl Y hT)
      _ ≤ P z {ω | ¬ IsCadlag (fun t : ℝ≥0 => Y t ω)} + P z (⋃ k, E Y Tn k) := measure_union_le _ _
      _ = ⨆ k, P z (E Y Tn k) := by rw [hN, zero_add, (E_mono Y Tn).measure_iUnion]
      _ ≤ _ := iSup_le hEle
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have := hmain (ε / T) (div_pos hε hT)
  calc _ ≤ T * (Ψ + ε / T) := this
    _ = T * Ψ + ε := by field_simp

end Main

end TJ

open TJ in
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℕ)
    (P : ℕ → Measure Ω) (law : PopulationLaws)
    (rate : ℝ≥0) (hRate : 0 < rate)
    (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (hBranching : HasBranchingProperty law)
    (hMarkov : IsPopulationMarkovPath Y P law)
    (hSemigroup : IsPopulationMarkovSemigroup law)
    (hGenerator : IsBranchingRateGenerator law rate offspring)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ y : ℕ, ∀ᵐ ω ∂P y,
      IsCadlag (fun t : ℝ≥0 => Y t ω)) :
    ∀ z : ℕ,
      Tendsto
        (fun T : ℝ => (P z {ω | ∃ a b c : ℝ≥0, a < b ∧ b < c ∧ (c : ℝ) ≤ T ∧
            Y a ω ≠ Y b ω ∧ Y b ω ≠ Y c ω}).toReal / T)
        (𝓝[>] 0) (𝓝 0) := by
  intro z
  have h1 : (0:ℝ≥0) < 1 := one_pos
  have hAs : Summable (A rate offspring z) :=
    summable_of_lim (ak_nonneg law z 1) (A_nonneg rate offspring z) (ak_summable law z 1)
      (ak_pt Y P law rate offspring hMarkov hGenerator hInitial z h1)
      (ak_L Y P law rate offspring hMarkov hGenerator hInitial z h1)
  have hge := A_sum_ge rate offspring hNoNullJumps z hAs
  set Ψ : ℝ → ℝ := fun T =>
    (rate:ℝ) * z - ∑' w, A rate offspring z w * Real.exp (-((rate:ℝ) * w) * T) with hΨ
  have hlim : Tendsto Ψ (𝓝[>] 0) (𝓝 ((rate:ℝ) * z - ∑' w, A rate offspring z w)) := by
    refine tendsto_const_nhds.sub ?_
    have := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0:ℝ))
      (f := fun T w => A rate offspring z w * Real.exp (-((rate:ℝ) * w) * T))
      (g := fun w => A rate offspring z w) hAs (fun w => by
        have hc : Continuous (fun T : ℝ => A rate offspring z w *
            Real.exp (-((rate:ℝ) * w) * T)) := by fun_prop
        have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using this) ?_
    · exact this
    · filter_upwards [self_mem_nhdsWithin] with T hT w
      have hT' : (0:ℝ) < T := hT
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (A_nonneg _ _ _ _) (Real.exp_pos _).le)]
      have : Real.exp (-((rate:ℝ) * w) * T) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have : 0 ≤ (rate:ℝ) * w * T := by positivity
        linarith)
      nlinarith [A_nonneg rate offspring z w]
  have hmax : Tendsto (fun T => max (Ψ T) 0) (𝓝[>] 0) (𝓝 0) := by
    have := hlim.max (tendsto_const_nhds (x := (0:ℝ)))
    rwa [max_eq_right (by linarith)] at this
  refine squeeze_zero' ?_ ?_ hmax
  · filter_upwards [self_mem_nhdsWithin] with T hT
    exact div_nonneg ENNReal.toReal_nonneg (le_of_lt hT)
  · filter_upwards [self_mem_nhdsWithin] with T hT
    have hT' : (0:ℝ) < T := hT
    rw [div_le_iff₀ hT']
    calc _ ≤ T * Ψ T := main_bound Y P law rate offspring hMarkov hSemigroup hGenerator hInitial
          hMeas hCadlag z hAs hT'
      _ = Ψ T * T := mul_comm _ _
      _ ≤ max (Ψ T) 0 * T := by gcongr; exact le_max_left _ _
