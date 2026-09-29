-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_jacquetTruncated3_cellSectionOf_twistFamily_eq_finsum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d6d7fa4a-86c9-5dec-a98b-b7dbde3f20eb

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_CubicInduction_AdditiveJacquet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_jacquetTruncated3_cellSectionOf_twistFamily_eq_finsum

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

open scoped Classical

noncomputable section

namespace TruncFlat

open MeasureTheory NumberField.StandardAddChar LanglandsTunnell.TateLocal Filter Topology

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem isOpen_valued_le_exp (n : ℕ) :
    IsOpen {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (n : ℤ)} := by
  have h : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (n : ℤ)}
      = {x : v.adicCompletion ℚ | Valued.v (x - 0) ≤ WithZero.exp (- -(n : ℤ))} := by
    simp only [sub_zero, neg_neg]
  rw [h]
  exact (isClopen_setOf_valued_sub_le v 0 (-(n : ℤ))).isOpen

theorem exists_forall_valued_le_of_isCompact {S : Set (v.adicCompletion ℚ)} (hS : IsCompact S) :
    ∃ R : ℤ, ∀ x ∈ S, Valued.v x ≤ WithZero.exp R := by
  have hcov : S ⊆ ⋃ n : ℕ, {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (n : ℤ)} := by
    intro x _
    obtain ⟨n, hn⟩ := exists_valued_le_exp v x
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  have hdir : Directed (· ⊆ ·) fun n : ℕ => {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (n : ℤ)} := by
    intro a b
    refine ⟨max a b, fun x hx => ?_, fun x hx => ?_⟩
    · exact le_trans hx (WithZero.exp_le_exp.mpr (Nat.cast_le.mpr (le_max_left a b)))
    · exact le_trans hx (WithZero.exp_le_exp.mpr (Nat.cast_le.mpr (le_max_right a b)))
  obtain ⟨n, hn⟩ := hS.elim_directed_cover _ (isOpen_valued_le_exp v) hcov hdir
  exact ⟨n, fun x hx => hn hx⟩

theorem exists_forall_apply_eq_zero_of_exp_lt {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ}
    (hΦc : HasCompactSupport Φ) :
    ∃ R : ℤ, ∀ (q : Fin 3 → v.adicCompletion ℚ) (i : Fin 3), WithZero.exp R < Valued.v (q i) → Φ q = 0 := by
  have hK : IsCompact (tsupport Φ) := hΦc
  have hb : ∀ i : Fin 3, ∃ R : ℤ, ∀ q ∈ tsupport Φ, Valued.v (q i) ≤ WithZero.exp R := by
    intro i
    obtain ⟨R, hR⟩ := exists_forall_valued_le_of_isCompact v (hK.image (continuous_apply i))
    exact ⟨R, fun q hq => hR _ (Set.mem_image_of_mem _ hq)⟩
  choose R hR using hb
  have hRmax : ∀ j : Fin 3, R j ≤ max (R 0) (max (R 1) (R 2)) := by
    intro j
    fin_cases j <;> simp
  refine ⟨max (R 0) (max (R 1) (R 2)), fun q i hi => ?_⟩
  by_contra hq
  have hqs : q ∈ tsupport Φ := subset_tsupport Φ hq
  exact absurd ((hR i q hqs).trans (WithZero.exp_le_exp.mpr (hRmax i))) (not_le.mpr hi)

theorem eventually_exp_lt_valued_div {n d : LocalGL3 v → v.adicCompletion ℚ} {g : LocalGL3 v}
    (hn : Continuous n)
    (hd : Continuous d) (hng : n g ≠ 0) (hdg : d g = 0) (R : ℤ) :
    ∀ᶠ h in 𝓝 g, d h ≠ 0 → WithZero.exp R < Valued.v (n h / d h) := by
  obtain ⟨t, ht0, ht⟩ := exists_valued_eq_exp v (-R)
  have h1 : ∀ᶠ h in 𝓝 g, Valued.v (n h) = Valued.v (n g) := (hn.tendsto g).eventually (eventually_valued_eq v hng)
  have h2 : ∀ᶠ h in 𝓝 g, Valued.v (d h) < Valued.v (t * n g) := by
    have hlim : Tendsto d (𝓝 g) (𝓝 0) := by simpa [hdg] using hd.tendsto g
    exact hlim.eventually (eventually_valued_lt v (mul_ne_zero ht0 hng))
  filter_upwards [h1, h2] with h hn' hd' hd0
  have hvd : Valued.v (d h) ≠ 0 := (Valuation.ne_zero_iff _).mpr hd0
  rw [Valuation.map_mul, ht] at hd'
  rw [map_div₀, hn', lt_div_iff₀ (lt_of_le_of_ne zero_le' hvd.symm)]
  calc WithZero.exp R * Valued.v (d h) < WithZero.exp R * (WithZero.exp (-R) * Valued.v (n g)) :=
        mul_lt_mul_of_pos_left hd' WithZero.exp_pos
    _ = Valued.v (n g) := by rw [← mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, one_mul]

theorem eventually_cellSectionOf_eq_of_den {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ} {R : ℤ}
    (hR : ∀ (q : Fin 3 → v.adicCompletion ℚ) (i : Fin 3), WithZero.exp R < Valued.v (q i) → Φ q = 0) {g : LocalGL3 v}
    {n d : LocalGL3 v → v.adicCompletion ℚ} (i : Fin 3) (hn : Continuous n) (hd : Continuous d) (hng : n g ≠ 0)
    (hdg : d g = 0) (hratio : ∀ h, cellRatio v h i = n h / d h) (hden : ∀ h, h ∈ bigCell3 v → d h ≠ 0) :
    ∀ᶠ h in 𝓝 g, cellSectionOf v χ Φ h = cellSectionOf v χ Φ g := by
  have hg : g ∉ bigCell3 v := fun hmem => hden g hmem hdg
  rw [cellSectionOf_apply_of_notMem v χ Φ hg]
  filter_upwards [eventually_exp_lt_valued_div v hn hd hng hdg R] with h hh
  by_cases hhB : h ∈ bigCell3 v
  · rw [cellSectionOf_apply_of_mem v χ Φ hhB, hR (cellRatio v h) i (by rw [hratio]; exact hh (hden h hhB)), mul_zero]
  · exact cellSectionOf_apply_of_notMem v χ Φ hhB

theorem isLocallyConstant_cellSectionOf {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (hχ : ∀ i, IsLocallyConstant (χ i)) {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ} (hΦ : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) : IsLocallyConstant (cellSectionOf v χ Φ) := by
  obtain ⟨R, hR⟩ := exists_forall_apply_eq_zero_of_exp_lt v hΦc
  have hΦ' := hΦ
  rw [IsLocallyConstant.iff_eventually_eq] at hΦ' ⊢
  intro g
  by_cases hc : cornerEntry v g = 0
  · rcases exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero v hc with h21 | h22
    · exact eventually_cellSectionOf_eq_of_den v hR 0 (continuous_gl3Entry v 2 1) (continuous_cornerEntry v) h21 hc
        (fun h => rfl) (fun h hh => hh.1)
    · exact eventually_cellSectionOf_eq_of_den v hR 1 (continuous_gl3Entry v 2 2) (continuous_cornerEntry v) h22 hc
        (fun h => rfl) (fun h hh => hh.1)
  by_cases hl : lowerMinor v g = 0
  · exact eventually_cellSectionOf_eq_of_den v hR 2 (continuous_outerMinor v) (continuous_lowerMinor v)
      (outerMinor_ne_zero_of_lowerMinor_eq_zero v hc hl) hl (fun h => rfl) (fun h hh => hh.2)
  have hgB : g ∈ bigCell3 v := ⟨hc, hl⟩
  have hcA : ContinuousAt (cornerEntry v) g := (continuous_cornerEntry v).continuousAt
  have hlA : ContinuousAt (lowerMinor v) g := (continuous_lowerMinor v).continuousAt
  have hdA : ContinuousAt (gl3Det v) g := (continuous_gl3Det v).continuousAt
  have hmem : ∀ᶠ h in 𝓝 g, h ∈ bigCell3 v := by
    filter_upwards [hcA.eventually_ne hc, hlA.eventually_ne hl] with h hch hlh
    exact ⟨hch, hlh⟩
  have hval : ∀ᶠ h in 𝓝 g, cellValue v χ h = cellValue v χ g := by
    have hq0 : gl3Det v g / lowerMinor v g ≠ 0 := div_ne_zero (gl3Det_ne_zero v g) hl
    have hq1 : lowerMinor v g / cornerEntry v g ≠ 0 := div_ne_zero hl hc
    have e0 : ∀ᶠ h in nhds g,
        LanglandsTunnell.TateLocal.charExt (χ 0) (gl3Det v h / lowerMinor v h)
          = LanglandsTunnell.TateLocal.charExt (χ 0) (gl3Det v g / lowerMinor v g) :=
      (hdA.div hlA hl).eventually (eventually_charExt_eq v (χ 0) (hχ 0) hq0)
    have e1 : ∀ᶠ h in nhds g,
        LanglandsTunnell.TateLocal.charExt (χ 1) (lowerMinor v h / cornerEntry v h)
          = LanglandsTunnell.TateLocal.charExt (χ 1) (lowerMinor v g / cornerEntry v g) :=
      (hlA.div hcA hc).eventually (eventually_charExt_eq v (χ 1) (hχ 1) hq1)
    have e2 : ∀ᶠ h in nhds g, LanglandsTunnell.TateLocal.charExt (χ 2) (cornerEntry v h)
      = LanglandsTunnell.TateLocal.charExt (χ 2) (cornerEntry v g) :=
      hcA.eventually (eventually_charExt_eq v (χ 2) (hχ 2) hc)
    have e3 : ∀ᶠ h in nhds g, ‖gl3Det v h / lowerMinor v h‖ = ‖gl3Det v g / lowerMinor v g‖ :=
      (hdA.div hlA hl).eventually (eventually_norm_eq v hq0)
    have e4 : ∀ᶠ h in nhds g, ‖cornerEntry v h‖ = ‖cornerEntry v g‖ := hcA.eventually (eventually_norm_eq v hc)
    filter_upwards [e0, e1, e2, e3, e4] with h h0 h1 h2 h3 h4
    simp only [cellValue, h0, h1, h2, h3, h4]
  have hrA : ContinuousAt (cellRatio v) g := by
    rw [continuousAt_pi]
    intro i
    fin_cases i
    · exact ((continuous_gl3Entry v 2 1).continuousAt).div hcA hc
    · exact ((continuous_gl3Entry v 2 2).continuousAt).div hcA hc
    · exact ((continuous_outerMinor v).continuousAt).div hlA hl
  have hΦr : ∀ᶠ h in 𝓝 g, Φ (cellRatio v h) = Φ (cellRatio v g) := hrA.eventually (hΦ' (cellRatio v g))
  filter_upwards [hmem, hval, hΦr] with h h1 h2 h3
  rw [cellSectionOf_apply_of_mem v χ Φ h1, cellSectionOf_apply_of_mem v χ Φ hgB, h2, h3]

abbrev Unip3 : Type := v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ

theorem isAddHaarMeasure_selfDualHaarAt_rat :
    letI := localBorel ℚ v
    (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  have hN : (0 : NNReal) < (Ideal.absNorm v.asIdeal : NNReal) := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero h0
  unfold selfDualHaarAt
  exact Measure.IsAddHaarMeasure.nnreal_smul _ (NNReal.rpow_pos hN).ne'

def jacquetIntegrand (F : LocalGL3 v → ℂ) (q : Unip3 v) : ℂ :=
  psiLocal ℚ v (-(q.1 + q.2.1)) * F (antidiagonal3 v * upperUnipotent3 q.1 q.2.1 q.2.2)

theorem jacquetTruncated3_eq_setIntegral_jacquetIntegrand (c : ℤ) (F : LocalGL3 v → ℂ) :
    jacquetTruncated3 v c F
      = (letI := localBorel ℚ v; ∫ q in unipotentBall3 v c, jacquetIntegrand v F q ∂(jacquetHaar3 v)) :=
  rfl

theorem isClosed_valued_le (n : ℤ) :
    IsClosed {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n} := by
  have h : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n}
      = {x : v.adicCompletion ℚ | Valued.v (x - 0) ≤ WithZero.exp (- -n)} := by
    simp only [sub_zero, neg_neg]
  rw [h]
  exact (isClopen_setOf_valued_sub_le v 0 (-n)).isClosed

theorem isCompact_valued_le (n : ℤ) :
    IsCompact {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n} := by
  have h : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n}
      = {x : v.adicCompletion ℚ | Valued.v (x - 0) ≤ WithZero.exp (- -n)} := by
    simp only [sub_zero, neg_neg]
  rw [h]
  exact isCompact_setOf_valued_sub_le v 0 (-n)

theorem isCompact_unipotentBall3 (c : ℤ) : IsCompact (unipotentBall3 v c) := by
  have h : unipotentBall3 v c
      = {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c} ×ˢ
        ({y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp c} ×ˢ
          {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (2 * c)}) := by
    ext q
    simp only [mem_unipotentBall3_iff, Set.mem_prod, Set.mem_setOf_eq]
  rw [h]
  exact (isCompact_valued_le v c).prod ((isCompact_valued_le v c).prod (isCompact_valued_le v (2 * c)))

theorem measurableSet_unipotentBall3 (c : ℤ) :
    letI := localBorel ℚ v
    MeasurableSet (unipotentBall3 v c) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  exact (isCompact_unipotentBall3 v c).isClosed.measurableSet

theorem continuous_upperUnipotent3_coords :
    Continuous fun q : Unip3 v => (upperUnipotent3 q.1 q.2.1 q.2.2 : LocalGL3 v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun q : Unip3 v =>
      (!![1, q.1, q.2.2; 0, 1, q.2.1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun q : Unip3 v =>
      (!![1, -q.1, q.1 * q.2.1 - q.2.2; 0, 1, -q.2.1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_antidiagonal3_mul_upperUnipotent3_mul (g : LocalGL3 v) :
    Continuous fun q : Unip3 v => antidiagonal3 v * upperUnipotent3 q.1 q.2.1 q.2.2 * g :=
  (continuous_const.mul (continuous_upperUnipotent3_coords v)).mul continuous_const

theorem continuous_jacquetIntegrand {F : LocalGL3 v → ℂ} (hF : IsLocallyConstant F) (g : LocalGL3 v) :
    Continuous (jacquetIntegrand v (gl3AmbientRightTranslate (R := ℂ) g F)) := by
  have hFc : Continuous F := hF.continuous
  show Continuous fun q : Unip3 v =>
    psiLocal ℚ v (-(q.1 + q.2.1)) * gl3AmbientRightTranslate (R := ℂ) g F (antidiagonal3 v * upperUnipotent3 q.1 q.2.1 q.2.2)
  simp only [gl3AmbientRightTranslate_apply]
  exact ((continuous_psiLocal (K := ℚ) (v := v)).comp
    ((continuous_fst.add (continuous_fst.comp continuous_snd)).neg)).mul
    (hFc.comp (continuous_antidiagonal3_mul_upperUnipotent3_mul v g))

theorem integrableOn_jacquetIntegrand {F : LocalGL3 v → ℂ} (hF : IsLocallyConstant F) (g : LocalGL3 v) (c : ℤ) :
    letI := localBorel ℚ v
    IntegrableOn (jacquetIntegrand v (gl3AmbientRightTranslate (R := ℂ) g F)) (unipotentBall3 v c) (jacquetHaar3 v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  show IntegrableOn (jacquetIntegrand v (gl3AmbientRightTranslate (R := ℂ) g F)) (unipotentBall3 v c)
    ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)))
  exact (continuous_jacquetIntegrand v hF g).continuousOn.integrableOn_compact (isCompact_unipotentBall3 v c)

def vexpV (w : WithZero (Multiplicative ℤ)) : ℤ :=
  if hw : w = 0 then 0 else Multiplicative.toAdd (WithZero.unzero hw)

def vexp (x : v.adicCompletion ℚ) : ℤ := vexpV (Valued.v x)

theorem norm_eq_absNorm_zpow_vexp {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    ‖x‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ vexp v x := by
  have hv : Valued.v x ≠ (0 : WithZero (Multiplicative ℤ)) := (Valuation.ne_zero_iff _).mpr hx
  simp only [vexp, vexpV, dif_neg hv]
  rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv]
  push_cast
  rfl

theorem absNorm_pos : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h1 := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  have h0 : (0 : NNReal) < (Ideal.absNorm v.asIdeal : NNReal) := zero_lt_one.trans h1
  exact_mod_cast h0

theorem absNorm_complex_ne_zero : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
  have h := absNorm_pos v
  exact_mod_cast h.ne'

theorem ofReal_norm_cpow_eq {x : v.adicCompletion ℚ} (hx : x ≠ 0) (m : ℤ) (u : ℂ) :
    ((‖x‖ : ℝ) : ℂ) ^ ((m : ℂ) * u) =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (((vexp v x * m : ℤ) : ℂ) * u) := by
  have hN := absNorm_pos v
  have him : (Complex.log ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) * ((vexp v x : ℤ) : ℂ)).im = 0 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hN.le, ← Complex.ofReal_intCast, ← Complex.ofReal_mul,
      Complex.ofReal_im]
  rw [norm_eq_absNorm_zpow_vexp v hx]
  push_cast
  rw [← Complex.cpow_intCast, ← Complex.cpow_mul, ← mul_assoc]
  · rw [him]; exact neg_lt_zero.mpr Real.pi_pos
  · rw [him]; exact Real.pi_pos.le

theorem cellValue_lamU
    (lam : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (n : Fin 3 → ℤ)
    (lamU : ℂ → Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hlamU : ∀ (u : ℂ) (i : Fin 3) (a : (v.adicCompletion ℚ)ˣ),
      ((lamU u i a : ℂˣ) : ℂ) = ((lam i a : ℂˣ) : ℂ) * ((‖(a : v.adicCompletion ℚ)‖ : ℂ)) ^ ((n i : ℂ) * u))
    (u : ℂ) (h : LocalGL3 v) :
    cellValue v (lamU u) h =
      cellValue v lam h *
        (((‖gl3Det v h / lowerMinor v h‖ : ℝ) : ℂ) ^ ((n 0 : ℂ) * u) *
          ((‖lowerMinor v h / cornerEntry v h‖ : ℝ) : ℂ) ^ ((n 1 : ℂ) * u) *
          ((‖cornerEntry v h‖ : ℝ) : ℂ) ^ ((n 2 : ℂ) * u)) := by
  unfold cellValue
  by_cases h0 : gl3Det v h / lowerMinor v h = 0
  · simp [h0]
  by_cases h2 : cornerEntry v h = 0
  · simp [h2]
  by_cases h1 : lowerMinor v h / cornerEntry v h = 0
  · simp [h1]
  rw [charExt_of_ne_zero _ h0, charExt_of_ne_zero _ h0, charExt_of_ne_zero _ h2, charExt_of_ne_zero _ h2,
    charExt_of_ne_zero _ h1, charExt_of_ne_zero _ h1, hlamU u 0, hlamU u 1, hlamU u 2]
  simp only [Units.val_mk0]
  ring

def Kexp (n : Fin 3 → ℤ) (h : LocalGL3 v) : ℤ :=
  vexp v (gl3Det v h / lowerMinor v h) * n 0 + vexp v (lowerMinor v h / cornerEntry v h) * n 1 +
    vexp v (cornerEntry v h) * n 2

theorem flatFactor_eq_cpow (n : Fin 3 → ℤ) (u : ℂ) {h : LocalGL3 v} (hB : h ∈ bigCell3 v) :
    ((‖gl3Det v h / lowerMinor v h‖ : ℝ) : ℂ) ^ ((n 0 : ℂ) * u) *
        ((‖lowerMinor v h / cornerEntry v h‖ : ℝ) : ℂ) ^ ((n 1 : ℂ) * u) *
        ((‖cornerEntry v h‖ : ℝ) : ℂ) ^ ((n 2 : ℂ) * u) =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ ((Kexp v n h : ℂ) * u) := by
  obtain ⟨hc, hl⟩ := (mem_bigCell3_iff v h).mp hB
  have h0 : gl3Det v h / lowerMinor v h ≠ 0 := div_ne_zero (gl3Det_ne_zero v h) hl
  have h1 : lowerMinor v h / cornerEntry v h ≠ 0 := div_ne_zero hl hc
  rw [ofReal_norm_cpow_eq v h0, ofReal_norm_cpow_eq v h1, ofReal_norm_cpow_eq v hc,
    ← Complex.cpow_add _ _ (absNorm_complex_ne_zero v), ← Complex.cpow_add _ _ (absNorm_complex_ne_zero v)]
  congr 1
  simp only [Kexp]
  push_cast
  ring

def Kfun (lam : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (n : Fin 3 → ℤ) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (h : LocalGL3 v) : ℤ :=
  if cellSectionOf v lam Φ h = 0 then 0 else Kexp v n h

theorem cellSectionOf_lamU_eq
    (lam : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (n : Fin 3 → ℤ)
    (lamU : ℂ → Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hlamU : ∀ (u : ℂ) (i : Fin 3) (a : (v.adicCompletion ℚ)ˣ),
      ((lamU u i a : ℂˣ) : ℂ) = ((lam i a : ℂˣ) : ℂ) * ((‖(a : v.adicCompletion ℚ)‖ : ℂ)) ^ ((n i : ℂ) * u))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (u : ℂ) (h : LocalGL3 v) :
    cellSectionOf v (lamU u) Φ h =
      cellSectionOf v lam Φ h * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ ((Kfun v lam n Φ h : ℂ) * u) := by
  by_cases hB : h ∈ bigCell3 v
  · by_cases hz : cellSectionOf v lam Φ h = 0
    · have hK : Kfun v lam n Φ h = 0 := by simp only [Kfun, hz, if_true]
      have hz' : cellValue v lam h * Φ (cellRatio v h) = 0 := by
        rwa [cellSectionOf_apply_of_mem v lam Φ hB] at hz
      rw [hK, hz, cellSectionOf_apply_of_mem v (lamU u) Φ hB, cellValue_lamU v lam n lamU hlamU u h]
      calc cellValue v lam h *
            (((‖gl3Det v h / lowerMinor v h‖ : ℝ) : ℂ) ^ ((n 0 : ℂ) * u) *
              ((‖lowerMinor v h / cornerEntry v h‖ : ℝ) : ℂ) ^ ((n 1 : ℂ) * u) *
              ((‖cornerEntry v h‖ : ℝ) : ℂ) ^ ((n 2 : ℂ) * u)) * Φ (cellRatio v h)
          = (cellValue v lam h * Φ (cellRatio v h)) *
            (((‖gl3Det v h / lowerMinor v h‖ : ℝ) : ℂ) ^ ((n 0 : ℂ) * u) *
              ((‖lowerMinor v h / cornerEntry v h‖ : ℝ) : ℂ) ^ ((n 1 : ℂ) * u) *
              ((‖cornerEntry v h‖ : ℝ) : ℂ) ^ ((n 2 : ℂ) * u)) := by ring
        _ = 0 * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (((0 : ℤ) : ℂ) * u) := by rw [hz']; ring
    · have hK : Kfun v lam n Φ h = Kexp v n h := by simp only [Kfun, hz, if_false]
      rw [hK, cellSectionOf_apply_of_mem v (lamU u) Φ hB, cellSectionOf_apply_of_mem v lam Φ hB,
        cellValue_lamU v lam n lamU hlamU u h, flatFactor_eq_cpow v n u hB]
      ring
  · rw [cellSectionOf_apply_of_notMem v (lamU u) Φ hB, cellSectionOf_apply_of_notMem v lam Φ hB, zero_mul]

theorem vexp_congr {x y : v.adicCompletion ℚ} (hxy : Valued.v x = Valued.v y) : vexp v x = vexp v y := by
  simp only [vexp, hxy]

theorem isLocallyConstant_Kfun
    (lam : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i)) (n : Fin 3 → ℤ)
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) :
    IsLocallyConstant (Kfun v lam n Φ) := by
  have hf := isLocallyConstant_cellSectionOf v hlam hΦ.1 hΦ.2
  rw [IsLocallyConstant.iff_eventually_eq] at hf
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  by_cases hz : cellSectionOf v lam Φ g = 0
  · filter_upwards [hf g] with h hh
    simp only [Kfun, hh, hz, if_true]
  · have hB : g ∈ bigCell3 v := by
      by_contra hB
      exact hz (cellSectionOf_apply_of_notMem v lam Φ hB)
    obtain ⟨hc, hl⟩ := (mem_bigCell3_iff v g).mp hB
    have hcA : ContinuousAt (cornerEntry v) g := (continuous_cornerEntry v).continuousAt
    have hlA : ContinuousAt (lowerMinor v) g := (continuous_lowerMinor v).continuousAt
    have hdA : ContinuousAt (gl3Det v) g := (continuous_gl3Det v).continuousAt
    have hq0 : gl3Det v g / lowerMinor v g ≠ 0 := div_ne_zero (gl3Det_ne_zero v g) hl
    have hq1 : lowerMinor v g / cornerEntry v g ≠ 0 := div_ne_zero hl hc
    have e0 : ∀ᶠ h in 𝓝 g, Valued.v (gl3Det v h / lowerMinor v h) = Valued.v (gl3Det v g / lowerMinor v g) :=
      (hdA.div hlA hl).eventually (eventually_valued_eq v hq0)
    have e1 : ∀ᶠ h in 𝓝 g, Valued.v (lowerMinor v h / cornerEntry v h) = Valued.v (lowerMinor v g / cornerEntry v g) :=
      (hlA.div hcA hc).eventually (eventually_valued_eq v hq1)
    have e2 : ∀ᶠ h in 𝓝 g, Valued.v (cornerEntry v h) = Valued.v (cornerEntry v g) :=
      hcA.eventually (eventually_valued_eq v hc)
    filter_upwards [hf g, e0, e1, e2] with h hh h0 h1 h2
    have hz' : ¬ cellSectionOf v lam Φ h = 0 := by rwa [hh]
    simp only [Kfun, hz, hz', if_false, Kexp, vexp_congr v h0, vexp_congr v h1, vexp_congr v h2]

theorem main
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))

    (n : Fin 3 → ℤ)
    (lamU : ℂ → Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hlamU : ∀ (u : ℂ) (i : Fin 3) (a : (p.adicCompletion ℚ)ˣ),
      ((lamU u i a : ℂˣ) : ℂ) = ((lam i a : ℂˣ) : ℂ) * ((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ ((n i : ℂ) * u))
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (g : LocalGL3 p) (c : ℤ) :
    ∃ e : ℤ → ℂ, {i : ℤ | e i ≠ 0}.Finite ∧
      ∀ u : ℂ, jacquetTruncated3 p c (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf p (lamU u) Φ)) =
        ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * u) * e i := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := ⟨rfl⟩
  have hf : IsLocallyConstant (cellSectionOf p lam Φ) := isLocallyConstant_cellSectionOf p hlam hΦ.1 hΦ.2

  set κ : Unip3 p → ℤ := fun q => Kfun p lam n Φ (antidiagonal3 p * upperUnipotent3 q.1 q.2.1 q.2.2 * g) with hκ
  have hκlc : IsLocallyConstant κ :=
    (isLocallyConstant_Kfun p lam hlam n Φ hΦ).comp_continuous (continuous_antidiagonal3_mul_upperUnipotent3_mul p g)
  have hT : (κ '' unipotentBall3 p c).Finite :=
    ((isCompact_unipotentBall3 p c).image hκlc.continuous).finite_of_discrete
  have hmeas : ∀ j : ℤ, MeasurableSet (κ ⁻¹' {j}) := fun j => (hκlc.isOpen_fiber j).measurableSet

  set A : Unip3 p → ℂ := jacquetIntegrand p (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf p lam Φ)) with hA
  have hAint : IntegrableOn A (unipotentBall3 p c) (jacquetHaar3 p) := integrableOn_jacquetIntegrand p hf g c

  set e : ℤ → ℂ := fun i => ∫ q in unipotentBall3 p c, Set.indicator (κ ⁻¹' {-i}) A q ∂(jacquetHaar3 p) with he
  have he0 : ∀ i : ℤ, -i ∉ κ '' unipotentBall3 p c → e i = 0 := by
    intro i hi
    simp only [he]
    refine setIntegral_eq_zero_of_forall_eq_zero fun q hq => ?_
    rw [Set.indicator_of_notMem]
    intro hq'
    exact hi ⟨q, hq, hq'⟩
  have hsupp : {i : ℤ | e i ≠ 0} ⊆ (fun j => -j) '' (κ '' unipotentBall3 p c) := by
    intro i hi
    by_contra hni
    refine hi (he0 i fun hmem => hni ?_)
    exact ⟨-i, hmem, neg_neg i⟩
  refine ⟨e, (hT.image _).subset hsupp, fun u => ?_⟩

  have hpt : ∀ q : Unip3 p,
      jacquetIntegrand p (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf p (lamU u) Φ)) q =
        A q * ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ ((κ q : ℂ) * u) := by
    intro q
    simp only [hA, jacquetIntegrand, gl3AmbientRightTranslate_apply, hκ]
    rw [cellSectionOf_lamU_eq p lam n lamU hlamU Φ u]
    ring
  set T : Finset ℤ := hT.toFinset with hTdef
  have hsum : ∀ q ∈ unipotentBall3 p c,
      A q * ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ ((κ q : ℂ) * u) =
        ∑ j ∈ T, Set.indicator (κ ⁻¹' {j}) A q * ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ ((j : ℂ) * u) := by
    intro q hq
    have hmem : κ q ∈ T := by
      rw [hTdef, Set.Finite.mem_toFinset]
      exact ⟨q, hq, rfl⟩
    rw [Finset.sum_eq_single_of_mem (κ q) hmem]
    · rw [Set.indicator_of_mem (by simp)]
    · intro j _ hne
      rw [Set.indicator_of_notMem, zero_mul]
      simpa [Set.mem_preimage, Set.mem_singleton_iff] using fun h => hne h.symm
  rw [jacquetTruncated3_eq_setIntegral_jacquetIntegrand]
  calc ∫ q in unipotentBall3 p c, jacquetIntegrand p (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf p (lamU u) Φ)) q
          ∂(jacquetHaar3 p)
      = ∫ q in unipotentBall3 p c,
          ∑ j ∈ T, Set.indicator (κ ⁻¹' {j}) A q * ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ ((j : ℂ) * u)
            ∂(jacquetHaar3 p) :=
        setIntegral_congr_fun (measurableSet_unipotentBall3 p c) (fun q hq => by rw [hpt q, hsum q hq])
    _ = ∑ j ∈ T, ∫ q in unipotentBall3 p c,
          Set.indicator (κ ⁻¹' {j}) A q * ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ ((j : ℂ) * u) ∂(jacquetHaar3 p) :=
        integral_finsetSum T (fun j _ => ((hAint.indicator (hmeas j)).mul_const _))
    _ = ∑ j ∈ T, ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ ((j : ℂ) * u) * e (-j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_mul_const, mul_comm]
        simp only [he, neg_neg]
    _ = ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * u) * e i := by
        symm
        rw [finsum_eq_sum_of_support_subset (fun i : ℤ => (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * u) * e i)
          (s := T.image fun j => -j) ?_]
        · rw [Finset.sum_image (fun a _ b _ h => neg_injective h)]
          refine Finset.sum_congr rfl fun j _ => ?_
          push_cast
          rw [neg_neg]
        · intro i hi
          rw [Function.mem_support] at hi
          have hei : e i ≠ 0 := fun h0 => hi (by rw [h0, mul_zero])
          have := hsupp hei
          rw [Finset.coe_image, hTdef, Set.Finite.coe_toFinset]
          exact this

end TruncFlat

end

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))

    (n : Fin 3 → ℤ)
    (lamU : ℂ → Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hlamU : ∀ (u : ℂ) (i : Fin 3) (a : (p.adicCompletion ℚ)ˣ),
      ((lamU u i a : ℂˣ) : ℂ) = ((lam i a : ℂˣ) : ℂ) * ((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ ((n i : ℂ) * u))
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (g : LocalGL3 p) (c : ℤ) :
    ∃ e : ℤ → ℂ, {i : ℤ | e i ≠ 0}.Finite ∧
      ∀ u : ℂ, jacquetTruncated3 p c (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf p (lamU u) Φ)) =
        ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * u) * e i :=
  TruncFlat.main p lam hlam n lamU hlamU Φ hΦ g c

end S_LanglandsTunnell_CubicInduction_exists_forall_jacquetTruncated3_cellSectionOf_twistFamily_eq_finsum
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_jacquetTruncated3_cellSectionOf_twistFamily_eq_finsum (solution)
