-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.tateFourier_tateFourier_eq_of_isSchwartzBruhat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/7e0b7dcd-30d5-5dae-966a-441b58d17231

import Mathlib
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_tateFourier_tateFourier_eq_of_isSchwartzBruhat

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal Filter Topology

noncomputable section

namespace LTLocalFourierInv

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

def ball (k : ℤ) : Set (v.adicCompletion K) := {y | Valued.v y ≤ WithZero.exp k}

theorem mem_ball {k : ℤ} {y : v.adicCompletion K} : y ∈ ball v k ↔ Valued.v y ≤ WithZero.exp k :=
  Iff.rfl

theorem zero_mem_ball (k : ℤ) : (0 : v.adicCompletion K) ∈ ball v k := by
  simp [mem_ball]

theorem exists_valued_eq_exp (k : ℤ) :
    ∃ t : v.adicCompletion K, t ≠ 0 ∧ Valued.v t = WithZero.exp k := by
  refine ⟨((AdelicLevel.uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : v.adicCompletion K),
    Units.ne_zero _, ?_⟩
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, AdelicLevel.valued_uniformizerUnit,
    ← WithZero.exp_zsmul]
  congr 1
  ring

theorem isOpen_ball (k : ℤ) : IsOpen (ball v k) := by
  obtain ⟨t, ht, hvt⟩ := exists_valued_eq_exp v k
  have : ball v k = {y | Valued.v y ≤ Valued.v t} := by rw [hvt]; rfl
  rw [this]
  exact AdelicLevel.isOpen_setOf_valued_le v t ht

theorem isClosed_ball (k : ℤ) : IsClosed (ball v k) := by
  obtain ⟨t, ht, hvt⟩ := exists_valued_eq_exp v k
  have : ball v k = {y | Valued.v y ≤ Valued.v t} := by rw [hvt]; rfl
  rw [this]
  exact AdelicLevel.isClosed_setOf_valued_le v t ht

theorem isClopen_ball (k : ℤ) : IsClopen (ball v k) := ⟨isClosed_ball v k, isOpen_ball v k⟩

theorem ball_eq_image (k : ℤ) {t : v.adicCompletion K} (ht : t ≠ 0) (hvt : Valued.v t = WithZero.exp k) :
    ball v k = (fun y => y * t) '' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  ext y
  simp only [mem_ball, Set.mem_image, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro hy
    refine ⟨y * t⁻¹, ?_, by field_simp⟩
    rw [map_mul, map_inv₀, hvt]
    calc Valued.v y * (WithZero.exp k)⁻¹ ≤ WithZero.exp k * (WithZero.exp k)⁻¹ :=
          mul_le_mul_left hy _
      _ = 1 := mul_inv_cancel₀ WithZero.exp_ne_zero
  · rintro ⟨z, hz, rfl⟩
    rw [map_mul, hvt]
    calc Valued.v z * WithZero.exp k ≤ 1 * WithZero.exp k := mul_le_mul_left hz _
      _ = WithZero.exp k := one_mul _

theorem isCompact_ball (k : ℤ) : IsCompact (ball v k) := by
  obtain ⟨t, ht, hvt⟩ := exists_valued_eq_exp v k
  rw [ball_eq_image v k ht hvt, ← coe_integersPositiveCompacts K v]
  exact (integersPositiveCompacts K v).isCompact.image (continuous_id.mul continuous_const)

theorem measurableSet_ball [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (k : ℤ) : MeasurableSet (ball v k) :=
  (isClosed_ball v k).measurableSet

theorem add_mem_ball {k : ℤ} {y z : v.adicCompletion K} (hy : y ∈ ball v k) (hz : z ∈ ball v k) :
    y + z ∈ ball v k := by
  rw [mem_ball] at hy hz ⊢
  exact (Valuation.map_add _ y z).trans (max_le hy hz)

theorem neg_mem_ball {k : ℤ} {y : v.adicCompletion K} (hy : y ∈ ball v k) : -y ∈ ball v k := by
  rw [mem_ball, Valuation.map_neg]; exact hy

theorem ball_mono {k l : ℤ} (h : k ≤ l) : ball v k ⊆ ball v l := fun _ hy =>
  hy.trans (WithZero.exp_le_exp.mpr h)

theorem exp_add_one_le_of_not_mem_ball {k : ℤ} {y : v.adicCompletion K} (hy : y ∉ ball v k) :
    WithZero.exp (k + 1) ≤ Valued.v y := by
  rw [mem_ball, not_le] at hy
  have hy0 : Valued.v y ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' hy)
  rw [← WithZero.exp_log hy0] at hy ⊢
  rw [WithZero.exp_lt_exp] at hy
  rw [WithZero.exp_le_exp]
  omega

variable {v}

section Char

variable (ψ : AddChar (v.adicCompletion K) ℂ) {n : ℤ}

theorem addChar_add_of_mem_ball (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (x : v.adicCompletion K) {d : v.adicCompletion K} (hd : d ∈ ball v n) : ψ (x + d) = ψ x := by
  rw [AddChar.map_add_eq_mul, hψn d hd, mul_one]

theorem continuous_addChar (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1) :
    Continuous ψ := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hev : ∀ᶠ y in 𝓝 x, ψ y = ψ x := by
    have hmem : (fun d => x + d) '' ball v n ∈ 𝓝 x := by
      have h1 : IsOpen ((fun d => x + d) '' ball v n) := (Homeomorph.addLeft x).isOpenMap _ (isOpen_ball v n)
      exact h1.mem_nhds ⟨0, zero_mem_ball v n, by simp⟩
    filter_upwards [hmem] with y hy
    obtain ⟨d, hd, rfl⟩ := hy
    exact addChar_add_of_mem_ball ψ hψn x hd
  exact (continuousAt_const.congr (Filter.EventuallyEq.symm hev) : ContinuousAt ψ x)

end Char

theorem exists_scale {f : v.adicCompletion K → ℂ} (hf : IsSchwartzBruhat f) :
    ∃ m : ℤ, ∀ (z d : v.adicCompletion K), d ∈ ball v (-m) → f (z + d) = f z := by
  obtain ⟨hlc, hcs⟩ := hf

  have hloc : ∀ x : v.adicCompletion K, ∃ k : ℕ, ∀ d ∈ ball v (-(k : ℤ)), f (x + d) = f x := by
    intro x
    obtain ⟨U, hU, hxU, hfU⟩ := hlc.exists_open x
    have hU0 : (fun d => x + d) ⁻¹' U ∈ 𝓝 (0 : v.adicCompletion K) :=
      (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hxU)
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hU0
    obtain ⟨k, hk⟩ := WithZero.exists_exp_neg_natCast_lt (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
    refine ⟨k, fun d hd => hfU _ (hγ ?_)⟩
    show Valued.v.restrict d < _
    rw [Valuation.restrict_lt_iff_lt_embedding]
    exact lt_of_le_of_lt hd hk
  choose k hk using hloc

  obtain ⟨T, hT⟩ := hcs.elim_finite_subcover (fun x => (fun d => x + d) '' ball v (-(k x)))
    (fun x => (Homeomorph.addLeft x).isOpenMap _ (isOpen_ball v _))
    (fun x hx => Set.mem_iUnion.mpr ⟨x, ⟨0, zero_mem_ball v _, by simp⟩⟩)
  classical
  refine ⟨(T.sup k : ℕ), fun z d hd => ?_⟩

  have key : ∀ x ∈ T, ∀ w : v.adicCompletion K, w ∈ (fun d => x + d) '' ball v (-(k x)) →
      w + d ∈ (fun d => x + d) '' ball v (-(k x)) := by
    intro x hx w hw
    obtain ⟨e, he, rfl⟩ := hw
    refine ⟨e + d, add_mem_ball v he (ball_mono v ?_ hd), by ring⟩
    have : k x ≤ T.sup k := Finset.le_sup hx
    omega
  have key' : ∀ x ∈ T, ∀ w : v.adicCompletion K, w ∈ (fun d => x + d) '' ball v (-(k x)) →
      w + -d ∈ (fun d => x + d) '' ball v (-(k x)) := by
    intro x hx w hw
    obtain ⟨e, he, rfl⟩ := hw
    refine ⟨e + -d, add_mem_ball v he (ball_mono v ?_ (neg_mem_ball v hd)), by ring⟩
    have : k x ≤ T.sup k := Finset.le_sup hx
    omega
  by_cases hz : ∃ x ∈ T, z ∈ (fun d => x + d) '' ball v (-(k x))
  · obtain ⟨x, hxT, hzx⟩ := hz
    have h1 : f z = f x := by
      obtain ⟨e, he, rfl⟩ := hzx
      exact hk x e he
    have h2 : f (z + d) = f x := by
      obtain ⟨e, he, hze⟩ := key x hxT z hzx
      rw [← hze]
      exact hk x e he
    rw [h1, h2]
  ·
    push Not at hz
    have hcov : ∀ w : v.adicCompletion K, (∀ x ∈ T, w ∉ (fun d => x + d) '' ball v (-(k x))) → f w = 0 := by
      intro w hw
      apply image_eq_zero_of_notMem_tsupport
      intro hwt
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hT hwt)
      obtain ⟨hxT, hwx⟩ := Set.mem_iUnion.mp hx
      exact hw x hxT hwx
    have hzd : ∀ x ∈ T, z + d ∉ (fun d => x + d) '' ball v (-(k x)) := by
      intro x hxT hmem
      have := key' x hxT _ hmem
      rw [add_neg_cancel_right] at this
      exact hz x hxT this
    rw [hcov z hz, hcov (z + d) hzd]

theorem scale_mono {f : v.adicCompletion K → ℂ} {m m' : ℤ}
    (hfm : ∀ (z d : v.adicCompletion K), d ∈ ball v (-m) → f (z + d) = f z) (h : m ≤ m') :
    ∀ (z d : v.adicCompletion K), d ∈ ball v (-m') → f (z + d) = f z :=
  fun z d hd => hfm z d (ball_mono v (by omega) hd)

theorem valued_natCast_le_one (j : ℕ) : Valued.v ((j : v.adicCompletion K)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    push_cast
    exact (Valuation.map_add _ _ _).trans (max_le ih (by simp))

section Char2

variable (ψ : AddChar (v.adicCompletion K) ℂ) {n : ℤ}

theorem norm_addChar_eq_one (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (w : v.adicCompletion K) : ‖ψ w‖ = 1 := by
  have hcont := continuous_addChar ψ hψn

  have hw0 : ∃ k : ℤ, w ∈ ball v k := by
    by_cases hw : w = 0
    · exact ⟨0, by simp [hw, mem_ball]⟩
    · exact ⟨WithZero.log (Valued.v w), by
        rw [mem_ball, WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hw)]⟩
  obtain ⟨k, hk⟩ := hw0
  obtain ⟨C, hC⟩ := (isCompact_ball v k).exists_bound_of_continuousOn hcont.continuousOn
  have hle : ∀ u ∈ ball v k, ‖ψ u‖ ≤ 1 := by
    intro u hu
    by_contra hlt
    rw [not_le] at hlt
    have hpow : ∀ j : ℕ, ‖ψ u‖ ^ j ≤ C := by
      intro j
      have hju : (j : v.adicCompletion K) * u ∈ ball v k := by
        rw [mem_ball, map_mul]
        calc Valued.v (j : v.adicCompletion K) * Valued.v u ≤ 1 * Valued.v u :=
              mul_le_mul_left (valued_natCast_le_one j) _
          _ ≤ WithZero.exp k := by rw [one_mul]; exact hu
      have := hC _ hju
      rwa [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, norm_pow] at this
    have ht := tendsto_pow_atTop_atTop_of_one_lt hlt
    rw [Filter.tendsto_atTop_atTop] at ht
    obtain ⟨j, hj⟩ := ht (C + 1)
    have := hj j le_rfl
    linarith [hpow j]
  have h1 := hle w hk
  have h2 := hle (-w) (neg_mem_ball v hk)
  rw [AddChar.map_neg_eq_inv, norm_inv] at h2
  have hpos : 0 < ‖ψ w‖ := by
    rw [norm_pos_iff]
    intro h0
    have := AddChar.map_neg_eq_inv ψ w
    have h1' : ψ (-w) * ψ w = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    rw [h0, mul_zero] at h1'
    exact zero_ne_one h1'
  have h3 : 1 ≤ ‖ψ w‖ := by rwa [inv_le_one₀ hpos] at h2
  exact le_antisymm h1 h3

theorem exists_phase_ne_one (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    {m : ℤ} {y : v.adicCompletion K} (hy : y ∉ ball v (n + m)) :
    ∃ d ∈ ball v (-m), ψ (d * y) ≠ 1 := by
  obtain ⟨w, hw, hψw⟩ := hψn'
  have hvy := exp_add_one_le_of_not_mem_ball v hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (zero_mem_ball v _)
  have hvy0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v y := lt_of_le_of_ne zero_le' ((Valuation.ne_zero_iff _).mpr hy0).symm
  refine ⟨w * y⁻¹, ?_, by rwa [inv_mul_cancel_right₀ hy0]⟩
  rw [mem_ball, map_mul, map_inv₀, mul_inv_le_iff₀ hvy0]
  calc Valued.v w ≤ WithZero.exp (n + 1) := hw
    _ = WithZero.exp (-m) * WithZero.exp (n + m + 1) := by rw [← WithZero.exp_add]; congr 1; ring
    _ ≤ WithZero.exp (-m) * Valued.v y := mul_le_mul_right hvy _

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

theorem tateFourier_eq_zero_of_not_mem
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    {f : v.adicCompletion K → ℂ} {m : ℤ}
    (hfm : ∀ (z d : v.adicCompletion K), d ∈ ball v (-m) → f (z + d) = f z)
    {y : v.adicCompletion K} (hy : y ∉ ball v (n + m)) : tateFourier ψ μ f y = 0 := by
  obtain ⟨d, hd, hψd⟩ := exists_phase_ne_one ψ hψn' hy
  have key : tateFourier ψ μ f y = ψ (d * y) * tateFourier ψ μ f y := by
    unfold tateFourier
    rw [← integral_const_mul]
    conv_lhs => rw [← integral_add_left_eq_self (μ := μ) (fun z => f z * ψ (z * y)) d]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [add_comm d z, hfm z d hd, add_mul, AddChar.map_add_eq_mul]
    ring
  have h1 : (1 - ψ (d * y)) * tateFourier ψ μ f y = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hψd
  · exact h

end Char2

section Main

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
  (ψ : AddChar (v.adicCompletion K) ℂ) {n : ℤ}

theorem tateFourier_ball_indicator
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (k : ℤ) (w : v.adicCompletion K) :
    tateFourier ψ μ ((ball v k).indicator fun _ => (1 : ℂ)) w =
      ((μ.real (ball v k) : ℝ) : ℂ) * (ball v (n + -k)).indicator (fun _ => (1 : ℂ)) w := by
  have h := LanglandsTunnell.TateLocal.tateFourier_indicator_setOf_valued_sub_le K v μ ψ n hψn hψn' 0 (-k) w
  have hset : {x : v.adicCompletion K | Valued.v (x - 0) ≤ WithZero.exp (-(-k))} = ball v k := by
    ext x; simp [mem_ball]
  have hset2 : {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-(-k))} = ball v k := by
    ext x; simp [mem_ball]
  rw [hset, hset2, zero_mul, AddChar.map_zero_eq_one, one_mul] at h
  exact h

variable {μ ψ}

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem continuous_of_isSchwartzBruhat {f : v.adicCompletion K → ℂ} (hf : IsSchwartzBruhat f) : Continuous f :=
  hf.1.continuous

theorem integrable_mul_addChar
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    {f : v.adicCompletion K → ℂ} (hf : IsSchwartzBruhat f) (y : v.adicCompletion K) :
    Integrable (fun z => f z * ψ (z * y)) μ := by
  have hc : Continuous fun z => f z * ψ (z * y) :=
    (continuous_of_isSchwartzBruhat hf).mul ((continuous_addChar ψ hψn).comp (continuous_id.mul continuous_const))
  exact hc.integrable_of_hasCompactSupport (hf.2.mul_right)

theorem tateFourier_tateFourier_of_scale
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    {f : v.adicCompletion K → ℂ} (hf : IsSchwartzBruhat f) {m : ℤ}
    (hfm : ∀ (z d : v.adicCompletion K), d ∈ ball v (-m) → f (z + d) = f z) (x : v.adicCompletion K) :
    tateFourier ψ μ (tateFourier ψ μ f) x =
      ((μ.real (ball v (n + m)) : ℝ) : ℂ) * ((μ.real (ball v (-m)) : ℝ) : ℂ) * f (-x) := by
  set E := ball v (n + m) with hE
  set D := ball v (-m) with hD
  have hψ1 := norm_addChar_eq_one ψ hψn
  have hψc := continuous_addChar ψ hψn
  have hfc := continuous_of_isSchwartzBruhat hf

  have hsupp : ∀ y, tateFourier ψ μ f y = E.indicator (fun _ => (1 : ℂ)) y * tateFourier ψ μ f y := by
    intro y
    by_cases hy : y ∈ E
    · rw [Set.indicator_of_mem hy, one_mul]
    · rw [Set.indicator_of_notMem hy, zero_mul, tateFourier_eq_zero_of_not_mem ψ μ hψn' hfm hy]

  set G : v.adicCompletion K → v.adicCompletion K → ℂ :=
    fun y z => (E.indicator (fun _ => (1 : ℂ)) y * ψ (y * x)) * (f z * ψ (z * y)) with hG

  have hLHS : tateFourier ψ μ (tateFourier ψ μ f) x = ∫ y, ∫ z, G y z ∂μ ∂μ := by
    have hL : tateFourier ψ μ (tateFourier ψ μ f) x = ∫ y, tateFourier ψ μ f y * ψ (y * x) ∂μ := rfl
    rw [hL]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hG]
    rw [integral_const_mul]
    conv_lhs => rw [hsupp y]
    unfold tateFourier
    ring

  have hEmeas : MeasurableSet E := measurableSet_ball v _
  have hEfin : μ E < ⊤ := (isCompact_ball v _).measure_lt_top
  have hint : Integrable (Function.uncurry G) (μ.prod μ) := by
    have hdom : Integrable (fun p : v.adicCompletion K × v.adicCompletion K =>
        E.indicator (fun _ => (1 : ℝ)) p.1 * ‖f p.2‖) (μ.prod μ) := by
      have hI1 : Integrable (E.indicator fun _ => (1 : ℝ)) μ :=
        (integrable_indicator_iff hEmeas).mpr (integrableOn_const hEfin.ne)
      have hI2 : Integrable (fun z => ‖f z‖) μ := (hfc.integrable_of_hasCompactSupport hf.2).norm
      exact hI1.mul_prod hI2
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine Measurable.aestronglyMeasurable ?_
      simp only [hG, Function.uncurry_def]
      refine ((((measurable_const.indicator hEmeas).comp measurable_fst)).mul
        (hψc.measurable.comp (measurable_fst.mul measurable_const))).mul
        ((hfc.measurable.comp measurable_snd).mul (hψc.measurable.comp (measurable_snd.mul measurable_fst)))
    · obtain ⟨y, z⟩ := p
      simp only [hG, Function.uncurry_apply_pair, norm_mul, hψ1, mul_one]
      by_cases hp : y ∈ E
      · simp [Set.indicator_of_mem hp]
      · simp [Set.indicator_of_notMem hp]

  have hswap : ∫ y, ∫ z, G y z ∂μ ∂μ = ∫ z, ∫ y, G y z ∂μ ∂μ := integral_integral_swap hint
  have hinner : ∀ z, ∫ y, G y z ∂μ = f z * (((μ.real E : ℝ) : ℂ) * D.indicator (fun _ => (1 : ℂ)) (z + x)) := by
    intro z
    have h1 : ∫ y, G y z ∂μ = f z * tateFourier ψ μ (E.indicator fun _ => (1 : ℂ)) (z + x) := by
      unfold tateFourier
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hG]
      rw [show y * (z + x) = z * y + y * x by ring, AddChar.map_add_eq_mul]
      ring
    rw [h1, hE, tateFourier_ball_indicator μ ψ hψn hψn' (n + m) (z + x)]
    congr 3
    rw [hD]; congr 1; ring

  set S : Set (v.adicCompletion K) := (fun z => z + x) ⁻¹' D with hS
  have hSmeas : MeasurableSet S := (measurableSet_ball v _).preimage (measurable_id.add measurable_const)
  have hlast : ∫ z, f z * D.indicator (fun _ => (1 : ℂ)) (z + x) ∂μ = ((μ.real D : ℝ) : ℂ) * f (-x) := by
    have hpt : ∀ z, f z * D.indicator (fun _ => (1 : ℂ)) (z + x) = S.indicator (fun _ => f (-x)) z := by
      intro z
      by_cases hz : z + x ∈ D
      · have hzS : z ∈ S := hz
        rw [Set.indicator_of_mem hz, Set.indicator_of_mem hzS, mul_one]
        have := hfm (-x) (z + x) hz
        rw [show -x + (z + x) = z by ring] at this
        exact this
      · have hzS : z ∉ S := hz
        rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hzS, mul_zero]
    simp_rw [hpt]
    rw [integral_indicator_const _ hSmeas, hS, Measure.real, measure_preimage_add_right]
    simp [Measure.real]

  rw [hLHS, hswap]
  simp_rw [hinner]
  simp_rw [show ∀ z, f z * (((μ.real E : ℝ) : ℂ) * D.indicator (fun _ => (1 : ℂ)) (z + x))
      = ((μ.real E : ℝ) : ℂ) * (f z * D.indicator (fun _ => (1 : ℂ)) (z + x)) from fun z => by ring]
  rw [integral_const_mul, hlast]
  ring

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem ball_zero_indicator_scale {k : ℤ} (hk : 0 ≤ k) :
    ∀ (z d : v.adicCompletion K), d ∈ ball v (-k) →
      (ball v 0).indicator (fun _ => (1 : ℂ)) (z + d) = (ball v 0).indicator (fun _ => (1 : ℂ)) z := by
  intro z d hd
  have hd0 : d ∈ ball v 0 := ball_mono v (by omega) hd
  by_cases hz : z ∈ ball v 0
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (add_mem_ball v hz hd0)]
  · have hzd : z + d ∉ ball v 0 := by
      intro h
      apply hz
      have := add_mem_ball v h (neg_mem_ball v hd0)
      rwa [add_neg_cancel_right] at this
    rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hzd]

theorem const_eq_const_zero
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    {M : ℤ} (hM : 0 ≤ M) :
    ((μ.real (ball v (n + M)) : ℝ) : ℂ) * ((μ.real (ball v (-M)) : ℝ) : ℂ) =
      ((μ.real (ball v (n + 0)) : ℝ) : ℂ) * ((μ.real (ball v (-0)) : ℝ) : ℂ) := by
  have hg : IsSchwartzBruhat ((ball v 0).indicator fun _ => (1 : ℂ)) :=
    IsSchwartzBruhat.indicator_const (isClopen_ball v 0) (isCompact_ball v 0) 1
  have h1 := tateFourier_tateFourier_of_scale (μ := μ) hψn hψn' hg (ball_zero_indicator_scale (v := v) hM) 0
  have h2 := tateFourier_tateFourier_of_scale (μ := μ) hψn hψn' hg (ball_zero_indicator_scale (v := v) le_rfl) 0
  simp only [neg_zero, Set.indicator_of_mem (zero_mem_ball v 0), mul_one] at h1 h2 ⊢
  rw [← h1, ← h2]

theorem main
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (f : v.adicCompletion K → ℂ) (hf : IsSchwartzBruhat f) (x : v.adicCompletion K) :
    tateFourier ψ μ (tateFourier ψ μ f) x =
      ((μ.real {y : v.adicCompletion K | Valued.v y ≤ 1} : ℝ) : ℂ) *
        ((μ.real {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp n} : ℝ) : ℂ) * f (-x) := by
  obtain ⟨m₀, hm₀⟩ := exists_scale (v := v) hf
  have hM := scale_mono (v := v) hm₀ (le_max_left m₀ 0)
  rw [tateFourier_tateFourier_of_scale hψn hψn' hf hM x, const_eq_const_zero hψn hψn' (le_max_right m₀ 0)]
  simp only [add_zero, neg_zero, ball, WithZero.exp_zero]
  ring

end Main

end LTLocalFourierInv

theorem solution (K : Type) [Field K]
    [NumberField K] (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (f : v.adicCompletion K → ℂ) (hf : IsSchwartzBruhat f) (x : v.adicCompletion K) :
    tateFourier ψ μ (tateFourier ψ μ f) x =
      ((μ.real {y : v.adicCompletion K | Valued.v y ≤ 1} : ℝ) : ℂ) *
        ((μ.real {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp n} : ℝ) : ℂ) * f (-x) :=
  LTLocalFourierInv.main hψn hψn' f hf x

end
end S_LanglandsTunnell_TateLocal_tateFourier_tateFourier_eq_of_isSchwartzBruhat
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_tateFourier_tateFourier_eq_of_isSchwartzBruhat (solution)
