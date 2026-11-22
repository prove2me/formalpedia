-- Prove2me | solution 1 for LCAGroup.weil_quotient_integral_formula
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:27:12.911026+00:00
-- url     : https://prove2.me/submissions/23390c15-2865-410a-bc62-9411ebe795f9

import Mathlib

open MeasureTheory Topology

set_option autoImplicit false

namespace Sol_LCAGroup_weil_quotient_integral_formula

open Filter Set
open scoped ENNReal NNReal

section CompactTestExpansion

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X}

/-- Absolute convergence in integral norm implies integrability of the pointwise sum. -/
theorem integrable_tsum_of_lintegral_eNorm [CompleteSpace E] {g : ℕ → X → E}
    (hm : ∀ n, AEStronglyMeasurable (g n) μ) (hs : ∑' n, ∫⁻ x, ‖g n x‖ₑ ∂μ ≠ ⊤) :
    Integrable (fun x ↦ ∑' n, g n x) μ := by
  refine ⟨.tsum hm, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun x ↦ enorm_tsum_le_tsum_enorm) ?_
  rwa [lintegral_tsum (fun n ↦ (hm n).enorm), lt_top_iff_ne_top]

variable [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [μ.Regular] [NormedSpace ℝ E]

/-- Compact-test density for a locally compact Hausdorff domain, without a normality
assumption: regularity sandwiches each finite-measure set between a compact and an open set. -/
theorem exists_compactTest_eLpNorm_sub_le {f : X → E} (hf : Integrable f μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g, eLpNorm (f - g) 1 μ ≤ ε ∧ Continuous g ∧ HasCompactSupport g := by
  classical
  refine (memLp_one_iff_integrable.mpr hf).induction_dense (by simp)
    (fun g : X → E ↦ Continuous g ∧ HasCompactSupport g) ?_ ?_ ?_ hε
  · intro c s hsm hsf δ hδ
    obtain ⟨η, hη, hsmall⟩ := exists_eLpNorm_indicator_le (p := 1) (μ := μ) (by simp) c hδ
    have hη' : (η : ℝ≥0∞) / 2 ≠ 0 := (ENNReal.half_pos (ENNReal.coe_ne_zero.mpr hη.ne')).ne'
    obtain ⟨U, hsU, hU, -, hUs⟩ := hsm.exists_isOpen_sdiff_lt hsf.ne hη'
    obtain ⟨K, hKs, hK, hsK⟩ := hsm.exists_isCompact_sdiff_lt hsf.ne hη'
    obtain ⟨b, hbK, hbU, hbs, hb⟩ := exists_continuous_one_zero_of_isCompact hK hU.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (hKs.trans hsU))
    have hμ : μ (U \ K) ≤ η := calc
      _ ≤ μ ((U \ s) ∪ (s \ K)) := measure_mono (by
          intro x hx
          by_cases hxs : x ∈ s
          · exact Or.inr ⟨hxs, hx.2⟩
          · exact Or.inl ⟨hx.1, hxs⟩)
      _ ≤ _ := measure_union_le _ _
      _ ≤ _ := (add_le_add hUs.le hsK.le).trans_eq (ENNReal.add_halves _)
    let g (x : X) := b x • c
    have hc : Continuous g := b.continuous.smul continuous_const
    have hs : HasCompactSupport g := hbs.comp_left (g := fun t : ℝ ↦ t • c) (zero_smul _ _)
    refine ⟨g, ?_, hc, hs⟩
    refine (eLpNorm_mono (g := (U \ K).indicator (fun _ ↦ c)) ?_).trans
      (hsmall _ hμ)
    intro x
    by_cases hxK : x ∈ K
    · simp [g, hxK, hKs hxK, show b x = 1 from hbK hxK]
    by_cases hxs : x ∈ s
    · simp only [Pi.sub_apply, indicator_of_mem hxs, indicator_of_mem
        (show x ∈ U \ K from ⟨hsU hxs, hxK⟩), g]
      rw [show b x • c - c = (b x - 1) • c by rw [sub_smul, one_smul], norm_smul]
      have hle : ‖b x - 1‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hb x).1, (hb x).2]
      simpa using mul_le_mul_of_nonneg_right hle (norm_nonneg c)
    · by_cases hxU : x ∈ U
      · simpa [g, hxU, hxK, hxs, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hb x).1] using
          mul_le_mul_of_nonneg_right (hb x).2 (norm_nonneg c)
      · simp [g, hxU, hxs, show b x = 0 from hbU hxU]
  · exact fun _ _ ⟨hc, hs⟩ ⟨hc', hs'⟩ ↦ ⟨hc.add hc', hs.add hs'⟩
  · exact fun g hg ↦ (hg.1.integrable_of_hasCompactSupport hg.2).1

/-- Expand an integrable function almost everywhere in compactly supported continuous
functions whose integral norms sum to a finite number. -/
theorem exists_compactTest_tsum {f : X → E} (hf : Integrable f μ) :
    ∃ g : ℕ → X → E, (∀ n, Continuous (g n) ∧ HasCompactSupport (g n)) ∧
      (∑' n, ∫⁻ x, ‖g n x‖ₑ ∂μ) ≠ ⊤ ∧ (f =ᵐ[μ] fun x ↦ ∑' n, g n x) := by
  obtain ⟨δ, hδ, hδs⟩ := ENNReal.exists_pos_sum_of_countable' (ε := ⊤) (by simp) ℕ
  choose a ha hac has using fun n ↦ exists_compactTest_eLpNorm_sub_le hf (hδ n).ne'
  let g : ℕ → X → E := fun n ↦ Nat.casesOn n (a 0) (fun k ↦ a (k + 1) - a k)
  have hg (n) : Continuous (g n) ∧ HasCompactSupport (g n) := by
    cases n with
    | zero => exact ⟨hac 0, has 0⟩
    | succ n => exact ⟨(hac _).sub (hac n), (has _).sub (has n)⟩
  have htail (n : ℕ) : eLpNorm (g (n + 1)) 1 μ ≤ δ n + δ (n + 1) := by
    have he : g (n+1) = (f - a n) - (f - a (n + 1)) := by dsimp [g]; abel
    have hm (k : ℕ) : AEStronglyMeasurable (f - a k) μ :=
      hf.1.sub ((hac k).integrable_of_hasCompactSupport (has k)).1
    exact he ▸ (eLpNorm_sub_le (hm n) (hm (n + 1)) le_rfl).trans
      (add_le_add (ha n) (ha (n + 1)))
  have hsum : ∑' n, eLpNorm (g n) 1 μ ≠ ⊤ := by
    intro h
    have h0 : eLpNorm (g 0) 1 μ ≠ ⊤ := (memLp_one_iff_integrable.mpr
      ((hac 0).integrable_of_hasCompactSupport (has 0))).eLpNorm_lt_top.ne
    have ht := ENNReal.tsum_add_one_eq_top h h0
    have hh := ENNReal.tsum_le_tsum (f := fun n ↦ eLpNorm (g (n + 1)) 1 μ)
      (g := fun n ↦ δ n + δ (n + 1)) htail
    rw [ht, ENNReal.tsum_add] at hh
    exact (not_le_of_gt (ENNReal.add_lt_top.mpr ⟨hδs,
      (ENNReal.tsum_comp_le_tsum_of_injective Nat.succ_injective δ).trans_lt hδs⟩)) hh
  refine ⟨g, hg, ?_, ?_⟩
  · simpa only [eLpNorm_one_eq_lintegral_enorm] using hsum
  · have hgm (n : ℕ) : AEStronglyMeasurable (g n) μ :=
      ((hg n).1.integrable_of_hasCompactSupport (hg n).2).1
    have herr := summable_norm_of_tsum_eLpNorm_ne_top (le_refl (1 : ℝ≥0∞))
        (fun n ↦ hf.1.sub ((hac n).integrable_of_hasCompactSupport (has n)).1)
        ((ENNReal.tsum_le_tsum (f := fun n ↦ eLpNorm (f - a n) 1 μ) (g := δ) ha).trans_lt hδs).ne
    filter_upwards [herr, summable_norm_of_tsum_eLpNorm_ne_top le_rfl hgm hsum] with x hx hx'
    symm
    apply HasSum.tsum_eq
    apply (hasSum_iff_tendsto_nat_of_summable_norm hx').mpr
    apply (tendsto_add_atTop_iff_nat 1).mp
    have hpart (n : ℕ) : ∑ i ∈ Finset.range (n+1), g i x = a n x := by
      induction n with
      | zero => simp [g]
      | succ n ih => rw [Finset.sum_range_succ, ih]; dsimp [g]; abel
    simp_rw [hpart]
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Pi.sub_apply, norm_sub_rev (f x)] using hx.tendsto_atTop_zero

end CompactTestExpansion

section Weil

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G) (hH : IsClosed (H : Set G))

/-- The fibre integral of `f` over the coset `q`, computed at the representative `q.out`. -/
noncomputable def cosetInt (μH : Measure H) (f : G → ℂ) (q : G ⧸ H) : ℂ :=
  ∫ h : H, f (q.out * (h : G)) ∂μH

omit [T2Space G] [LocallyCompactSpace G] in
/-- The fibre integral computed at `q.out` agrees with the fibre integral computed at any other
representative of the coset (left invariance of the Haar measure of `H`). -/
theorem cosetInt_mk (μH : Measure H) [μH.IsHaarMeasure] (f : G → ℂ) (x : G) :
    cosetInt H μH f (QuotientGroup.mk x) = ∫ h : H, f (x * (h : G)) ∂μH := by
  rw [cosetInt]
  set y : G := Quotient.out (QuotientGroup.mk x : G ⧸ H) with hydef
  have hy : (QuotientGroup.mk y : G ⧸ H) = QuotientGroup.mk x := Quotient.out_eq' _
  have hk : y⁻¹ * x ∈ H := QuotientGroup.eq.mp hy
  let k : H := ⟨y⁻¹ * x, hk⟩
  have hxe : x = y * (k : G) := by
    simp [k]
  have hassoc : ∀ h : H, x * (h : G) = y * ((k * h : H) : G) := by
    intro h
    rw [Subgroup.coe_mul, ← mul_assoc, ← hxe]
  simp_rw [hassoc]
  exact (MeasureTheory.integral_mul_left_eq_self (fun h : H ↦ f (y * (h : G))) k).symm

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular]

omit [T2Space G] [LocallyCompactSpace G] [μH.Regular] in
/-- Left Haar measure of a fibre does not depend on the representative of the coset. -/
lemma fibreMeasure_eq_of_mk_eq {U : Set G} {x y : G}
    (hxy : (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk y) :
    μH {h : H | x * (h : G) ∈ U} = μH {h : H | y * (h : G) ∈ U} := by
  have hk : x⁻¹ * y ∈ H := QuotientGroup.eq.mp hxy
  let k : H := ⟨x⁻¹ * y, hk⟩
  have hy : y = x * (k : G) := by simp [k]
  have hset :
      {h : H | y * (h : G) ∈ U} =
        (fun h : H => k * h) ⁻¹' {h : H | x * (h : G) ∈ U} := by
    ext h
    simp only [mem_preimage, Set.mem_ofPred_eq, hy, Subgroup.coe_mul, mul_assoc]
  have hembed : MeasurableEmbedding (fun h : H => k * h) :=
    (Homeomorph.mulLeft k).measurableEmbedding
  rw [hset, ← hembed.map_apply, map_mul_left_eq_self]

open scoped Pointwise in
omit [T2Space G] [LocallyCompactSpace G] in
/-- The fibre measure of an open set, as a function on the quotient, is lower semicontinuous. -/
lemma fibreMeasure_open_lowerSemicontinuous {U : Set G} (hU : IsOpen U) :
    LowerSemicontinuous fun q : G ⧸ H => μH {h : H | q.out * (h : G) ∈ U} := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro r
  rw [isOpen_iff_mem_nhds]
  intro q hq
  let x : G := q.out
  have hxq : QuotientGroup.mk x = q := Quotient.out_eq' q
  let V : Set H := {h : H | x * (h : G) ∈ U}
  have hVopen : IsOpen V :=
    hU.preimage ((continuous_const_mul x).comp continuous_subtype_val)
  have hVr : r < μH V := by simpa [V, x] using hq
  obtain ⟨K, hKV, hKc, hKμ⟩ :=
    (Measure.Regular.innerRegular (μ := μH)) hVopen r hVr
  let ι : H → G := fun h => x * (h : G)
  have hι : Continuous ι := (continuous_const_mul x).comp continuous_subtype_val
  have hKG : IsCompact (ι '' K) := hKc.image hι
  have hKGU : ι '' K ⊆ U := by
    rintro _ ⟨h, hh, rfl⟩
    exact hKV hh
  obtain ⟨W, hW, hWK⟩ := compact_open_separated_mul_left hKG hU hKGU
  have hWx : (fun v : G => v * x) '' W ∈ 𝓝 x := by
    have hmem : (Homeomorph.mulRight x) '' W ∈ 𝓝 (Homeomorph.mulRight x 1) := by
      rw [← (Homeomorph.mulRight x).map_nhds_eq (1 : G)]
      exact image_mem_map hW
    simpa [Homeomorph.coe_mulRight] using hmem
  have hπ : 𝓝 q = Filter.map (QuotientGroup.mk : G → G ⧸ H) (𝓝 x) := by
    simpa [hxq] using QuotientGroup.nhds_eq H x
  refine mem_of_superset (by
      rw [hπ]
      exact image_mem_map (m := (QuotientGroup.mk : G → G ⧸ H)) hWx) ?_
  rintro _ ⟨y, hyW, rfl⟩
  rw [mem_preimage, mem_Ioi]
  rcases hyW with ⟨v, hv, rfl⟩
  have hKy : K ⊆ {h : H | (v * x) * (h : G) ∈ U} := by
    intro h hh
    have hvK : v * (x * (h : G)) ∈ W * (ι '' K) := by
      exact Set.mul_mem_mul hv ⟨h, hh, rfl⟩
    simpa [mul_assoc] using hWK hvK
  have hle : μH K ≤ μH {h : H | (v * x) * (h : G) ∈ U} := measure_mono hKy
  have hinv := fibreMeasure_eq_of_mk_eq H μH (U := U) (x := v * x)
    (y := (QuotientGroup.mk (v * x) : G ⧸ H).out)
    (Quotient.out_eq' (QuotientGroup.mk (v * x) : G ⧸ H)).symm
  simpa [hinv] using hKμ.trans_le hle

omit [T2Space G] [LocallyCompactSpace G] [μH.Regular] in
include hH in
/-- A continuous compactly supported function is integrable on every coset. -/
lemma weilTest_fibre_integrable {E : Type*} [NormedAddCommGroup E]
    {f : G → E} (hc : Continuous f) (hs : HasCompactSupport f) (x : G) :
    Integrable (fun h : H ↦ f (x * (h : G))) μH := by
  let i : H → G := fun h ↦ x * (h : G)
  have hi : IsClosedEmbedding i :=
    (Homeomorph.mulLeft x).isClosedEmbedding.comp (IsClosedEmbedding.subtypeVal hH)
  exact (hc.comp hi.continuous).integrable_of_hasCompactSupport
    (.intro (hi.isProperMap.isCompact_preimage hs) fun x hx ↦
      image_eq_zero_of_notMem_tsupport (f := f) (x := i x) hx)

omit [T2Space G] [μH.Regular] in
include hH in
/-- The fibre integral of a continuous compactly supported function is continuous with compact
support on the quotient. -/
lemma weilTest_average {f : G → ℂ} (hc : Continuous f) (hs : HasCompactSupport f) :
    Continuous (cosetInt H μH f) ∧ HasCompactSupport (cosetInt H μH f) := by
  have : IsClosed (H : Set G) := hH
  have ses : TopologicalGroup.IsSES H.subtype (QuotientGroup.mk' H) :=
    TopologicalGroup.IsSES.ofClosedSubgroup H hH
  let g : CompactlySupportedContinuousMap G ℂ := ⟨⟨f, hc⟩, hs⟩
  have he : (ses.pushforward μH g : G ⧸ H → ℂ) = cosetInt H μH f := by
    funext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    change ses.pushforward μH g ((QuotientGroup.mk' H) x) = _
    rw [ses.pushforward_apply_apply]
    exact (cosetInt_mk H μH f x).symm
  rw [← he]
  exact ⟨(ses.pushforward μH g).continuous, (ses.pushforward μH g).hasCompactSupport⟩

omit [T2Space G] [μH.Regular] in
include hH in
/-- Fibre integrals of a real compactly supported continuous function are continuous with compact
support on the quotient. -/
lemma realFibreIntegral_average {g : G → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) :
    Continuous (fun q : G ⧸ H => ∫ h : H, g (q.out * (h : G)) ∂μH) ∧
      HasCompactSupport (fun q : G ⧸ H => ∫ h : H, g (q.out * (h : G)) ∂μH) := by
  obtain ⟨h₁, h₂⟩ := weilTest_average H hH μH (Complex.continuous_ofReal.comp hg)
    (hgs.comp_left Complex.ofReal_zero)
  have he : (fun q : G ⧸ H ↦ ∫ h : H, g (q.out * (h : G)) ∂μH) =
      Complex.re ∘ cosetInt H μH (Complex.ofReal ∘ g) := by
    funext q
    simp only [Function.comp_def, cosetInt]
    rw [integral_complex_ofReal, Complex.ofReal_re]
  rw [he]
  exact ⟨Complex.continuous_re.comp h₁, h₂.comp_left Complex.zero_re⟩

omit [T2Space G] [μH.Regular] in
include hH in
/-- Fibre integrals of a real compactly supported continuous function are continuous. -/
lemma continuous_realFibreIntegral {g : G → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) :
    Continuous fun q : G ⧸ H => ∫ h : H, g (q.out * (h : G)) ∂μH :=
  (realFibreIntegral_average H hH μH hg hgs).1

include hH in
/-- At a quotient point where the fibre measure of an open set is strictly above `c`, a compactly
supported bump in that set has fibre integral strictly above `c` nearby. -/
lemma exists_fibreBump_lt {U : Set G} (hU : IsOpen U)
    {q : G ⧸ H} {c : ℝ}
    (hlt : ENNReal.ofReal c < μH {h : H | q.out * (h : G) ∈ U}) :
    ∃ V : Set (G ⧸ H), IsOpen V ∧ q ∈ V ∧ ∃ g : G → ℝ, Continuous g ∧ HasCompactSupport g ∧
      (∀ x, 0 ≤ g x) ∧ (∀ x, g x ≤ 1) ∧ (∀ x, x ∉ U → g x = 0) ∧
      ∀ q' ∈ V, c < ∫ h : H, g (q'.out * (h : G)) ∂μH := by
  let x : G := q.out
  let fibre : Set H := {h : H | x * (h : G) ∈ U}
  have hfibre : IsOpen fibre :=
    hU.preimage ((continuous_const_mul x).comp continuous_subtype_val)
  have hlt' : ENNReal.ofReal c < μH fibre := hlt
  obtain ⟨L, hLf, hLc, hLμ⟩ :=
    (Measure.Regular.innerRegular (μ := μH)) hfibre (ENNReal.ofReal c) hlt'
  let ι : H → G := fun h => x * (h : G)
  have hι : Continuous ι := (continuous_const_mul x).comp continuous_subtype_val
  have hLG : IsCompact (ι '' L) := hLc.image hι
  have hLGU : ι '' L ⊆ U := by
    rintro _ ⟨h, hh, rfl⟩
    exact hLf hh
  obtain ⟨⟨gC, gcont⟩, hg1, hg0, hgs, hg01⟩ :=
    exists_continuous_one_zero_of_isCompact hLG hU.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hLGU)
  have hgU : ∀ y, y ∉ U → gC y = 0 := by
    intro y hy
    exact hg0 hy
  have hgs' : HasCompactSupport gC := hgs
  have hint : c < ∫ h : H, gC (x * (h : G)) ∂μH := by
    have hgint : Integrable (fun h : H => gC (ι h)) μH :=
      weilTest_fibre_integrable H hH μH gcont hgs' x
    have hone : (L.indicator (fun _ => (1 : ℝ≥0∞))) ≤ fun h => ENNReal.ofReal (gC (ι h)) := by
      intro h
      by_cases hh : h ∈ L
      · have : gC (ι h) = 1 := hg1 (mem_image_of_mem ι hh)
        simp [hh, this]
      · simp [hh]
    have hlin : μH L ≤ ENNReal.ofReal (∫ h, gC (ι h) ∂μH) := by
      calc μH L = ∫⁻ h in L, (1 : ℝ≥0∞) ∂μH := (setLIntegral_one L).symm
        _ = ∫⁻ h, L.indicator (fun _ => (1 : ℝ≥0∞)) h ∂μH :=
            (lintegral_indicator hLc.measurableSet _).symm
        _ ≤ ∫⁻ h, ENNReal.ofReal (gC (ι h)) ∂μH := lintegral_mono hone
        _ = ENNReal.ofReal (∫ h, gC (ι h) ∂μH) :=
            (ofReal_integral_eq_lintegral_ofReal hgint
              (Eventually.of_forall fun h => (hg01 (ι h)).1)).symm
    have hltL : ENNReal.ofReal c < ENNReal.ofReal (∫ h, gC (ι h) ∂μH) := hLμ.trans_le hlin
    by_contra hle
    exact absurd hltL (not_lt.mpr (ENNReal.ofReal_le_ofReal (not_lt.mp hle)))
  have hcont := continuous_realFibreIntegral H hH μH gcont hgs'
  have hpos : ∀ᶠ q' in 𝓝 q, c < ∫ h : H, gC (q'.out * (h : G)) ∂μH :=
    tendsto_const_nhds.eventually_lt (hcont.tendsto q) hint
  rw [eventually_nhds_iff] at hpos
  obtain ⟨V, hVq, hVo, hV⟩ := hpos
  exact ⟨V, hVo, hV, gC, gcont, hgs', fun y => (hg01 y).1, fun y => (hg01 y).2, hgU, hVq⟩

end Weil

section WeilQuotient

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G) (hH : IsClosed (H : Set G))
variable [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular]
variable (ν : Measure (G ⧸ H)) [ν.IsHaarMeasure] [ν.Regular]

omit [T2Space G] [μH.Regular] [ν.Regular] in
include hH in
/-- The fibre integral of a real compactly supported continuous function is integrable on the
quotient. -/
lemma weilTest_realAverage_integrable
    {g : G → ℝ} (hc : Continuous g) (hs : HasCompactSupport g) :
    Integrable (fun q : G ⧸ H ↦ ∫ h : H, g (q.out * (h : G)) ∂μH) ν := by
  obtain ⟨h₁, h₂⟩ := realFibreIntegral_average H hH μH hc hs
  exact h₁.integrable_of_hasCompactSupport h₂

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [BorelSpace G]
  [BorelSpace (G ⧸ H)] [μ.IsHaarMeasure] [μ.Regular] [μH.IsHaarMeasure] [μH.Regular] [ν.IsHaarMeasure] [ν.Regular] in
/-- Weil's formula for a real compactly supported continuous function. -/
lemma integral_eq_integral_realFibreIntegral
    (hν : ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
      ∫ x, φ x ∂μ = ∫ q : G ⧸ H, (∫ h : H, φ (q.out * (h : G)) ∂μH) ∂ν)
    {g : G → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) :
    ∫ x, g x ∂μ = ∫ q : G ⧸ H, (∫ h : H, g (q.out * (h : G)) ∂μH) ∂ν := by
  have hW := hν (fun x => (g x : ℂ)) (Complex.continuous_ofReal.comp hg)
    (hgs.comp_left Complex.ofReal_zero)
  have hfib : ∀ q : G ⧸ H, (∫ h : H, ((g (q.out * (h : G)) : ℝ) : ℂ) ∂μH) =
      ((∫ h : H, g (q.out * (h : G)) ∂μH : ℝ) : ℂ) := fun q => integral_complex_ofReal
  simp_rw [hfib] at hW
  rw [integral_complex_ofReal, integral_complex_ofReal] at hW
  exact Complex.ofReal_injective hW

omit [μ.IsHaarMeasure] [μ.Regular] [ν.Regular] in
include hH in
/-- On a compact subset of a strict fibre level set, finitely many test bumps give a
single minorant for the open set upstairs. -/
lemma weil_fibre_level_compact
    (hν : ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
      ∫ x, φ x ∂μ = ∫ q : G ⧸ H, (∫ h : H, φ (q.out * (h : G)) ∂μH) ∂ν)
    {U : Set G} (hU : IsOpen U) (hUf : μ U ≠ ⊤)
    {K : Set (G ⧸ H)} (hK : IsCompact K) {c : ℝ} (hc : 0 ≤ c)
    (hlev : ∀ q ∈ K, ENNReal.ofReal c < μH {h : H | q.out * (h : G) ∈ U}) :
    ν.real K * c ≤ μ.real U := by
  classical
  have : IsClosed (H : Set G) := hH
  choose V hVo hV g hgc hgs hg0 hg1 hgU hgt using fun q : K ↦
    exists_fibreBump_lt H hH μH hU (hlev q q.2)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hVo (fun q hq ↦ mem_iUnion.2 ⟨⟨q, hq⟩, hV _⟩)
  let b (x : G) := min (∑ i ∈ t, g i x) 1
  have hbc : Continuous b := (continuous_finsetSum _ fun i _ ↦ hgc i).min continuous_const
  have hbs : HasCompactSupport b := by
    have hs : HasCompactSupport (∑ i ∈ t, g i) := by
      clear hbc b ht
      induction t using Finset.induction_on with
      | empty => simpa using (HasCompactSupport.zero : HasCompactSupport (0 : G → ℝ))
      | insert i t hi ih => simpa [hi] using (hgs i).add ih
    simpa only [Function.comp_def, Finset.sum_apply] using
      hs.comp_left (g := fun y : ℝ ↦ min y 1) (by norm_num)
  have hb0 x : 0 ≤ b x := le_min (Finset.sum_nonneg fun i _ ↦ hg0 i x) zero_le_one
  have hmajor : K.indicator (fun _ ↦ c) ≤ fun q ↦ ∫ h : H, b (q.out * (h : G)) ∂μH := by
    intro q
    by_cases hq : q ∈ K
    · rw [indicator_of_mem hq]
      obtain ⟨i, hi, hVq⟩ := mem_iUnion₂.mp (ht hq)
      refine (hgt i q hVq).le.trans (integral_mono_of_nonneg (.of_forall fun h ↦ hg0 i _)
        (weilTest_fibre_integrable H hH μH hbc hbs q.out) (.of_forall fun h ↦ ?_))
      exact le_min (Finset.single_le_sum (fun j _ ↦ hg0 j _) hi) (hg1 i _)
    · simpa [hq] using integral_nonneg (μ := μH) (fun h : H ↦ hb0 (q.out * (h : G)))
  have hle := integral_mono_of_nonneg (μ := ν)
    (.of_forall (indicator_nonneg (fun _ _ ↦ hc)))
    (weilTest_realAverage_integrable H hH μH ν hbc hbs) (.of_forall hmajor)
  rw [integral_indicator_const _ hK.isClosed.measurableSet,
    ← integral_eq_integral_realFibreIntegral H μ μH ν hν hbc hbs] at hle
  refine hle.trans ?_
  have hU1 := (integrable_indicator_iff hU.measurableSet).mpr
    (integrableOn_const (C := (1 : ℝ)) hUf)
  calc ∫ x, b x ∂μ ≤ ∫ x, U.indicator (fun _ ↦ (1 : ℝ)) x ∂μ :=
        integral_mono_of_nonneg (.of_forall hb0) hU1 (.of_forall fun x ↦ by
          by_cases hx : x ∈ U
          · simp [hx, b]
          · simp [b, hx, fun i ↦ hgU i x hx])
    _ = μ.real U := by simp [integral_indicator_const _ hU.measurableSet]

omit [μ.IsHaarMeasure] in
include hH in
/-- Null sets upstairs are null on almost every fibre. Outer regularity lets us apply
the compact level estimate to open supersets of arbitrarily small measure. -/
lemma ae_weil_fibre
    (hν : ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
      ∫ x, φ x ∂μ = ∫ q : G ⧸ H, (∫ h : H, φ (q.out * (h : G)) ∂μH) ∂ν)
    {P : G → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ q : G ⧸ H ∂ν, ∀ᵐ h : H ∂μH, P (q.out * (h : G)) := by
  have : IsClosed (H : Set G) := hH
  let S := {x | ¬ P x}
  let m (s : Set G) (q : G ⧸ H) := μH {h : H | q.out * (h : G) ∈ s}
  have hz : μ S = 0 := ae_iff.mp hP
  have hsmall (r : ℝ≥0) (hr : 0 < r) : ∀ᵐ q ∂ν, m S q ≤ r := by
    rw [ae_iff]
    by_contra hpos
    obtain ⟨a, ha, ha'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (pos_iff_ne_zero.mpr hpos)
    obtain ⟨U, hSU, hU, hUf⟩ := S.exists_isOpen_lt_of_lt (μ := μ) (↑(a * r) : ℝ≥0∞)
      (by rw [hz, ENNReal.coe_pos]; exact mul_pos (ENNReal.coe_pos.mp ha) hr)
    have hsub : {q | ¬ m S q ≤ ↑r} ⊆ {q | ↑r < m U q} := fun q hq ↦
      (lt_of_not_ge hq).trans_le (measure_mono fun _ hh ↦ hSU hh)
    have ho : IsOpen {q | ↑r < m U q} :=
      (fibreMeasure_open_lowerSemicontinuous H μH hU).isOpen_preimage _
    obtain ⟨K, hKU, hK, haK⟩ := (Measure.Regular.innerRegular (μ := ν)) ho _
      (ha'.trans_le (measure_mono hsub))
    have hKf := hK.measure_lt_top (μ := ν)
    have h1 := weil_fibre_level_compact H hH μ μH ν hν hU (hUf.trans_le le_top).ne hK r.2
      (fun q hq ↦ by
        change ENNReal.ofReal (r : ℝ) < m U q
        rw [ENNReal.ofReal_coe_nnreal]
        exact hKU hq)
    have h2 : (a : ℝ) < ν.real K := by
      simpa [Measure.real] using (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top hKf.ne).mpr haK
    have h3 : μ.real U < (a : ℝ) * r := by
      simpa [Measure.real] using (ENNReal.toReal_lt_toReal (hUf.trans_le le_top).ne
        ENNReal.coe_ne_top).mpr hUf
    exact (not_lt_of_ge h1) (h3.trans (mul_lt_mul_of_pos_right h2 hr))
  have hall : ∀ᵐ q ∂ν, ∀ r : ℚ, 0 < (r : ℝ).toNNReal → m S q ≤ ↑(r : ℝ).toNNReal :=
    ae_all_iff.mpr fun r ↦ by
      by_cases hr : 0 < (r : ℝ).toNNReal
      · filter_upwards [hsmall _ hr] with q hq using fun _ ↦ hq
      · exact .of_forall fun _ h ↦ (hr h).elim
  filter_upwards [hall] with q hq
  apply ae_iff.mpr
  change m S q = 0
  by_contra h
  obtain ⟨r, -, hr, hr'⟩ := ENNReal.lt_iff_exists_rat_btwn.mp (pos_iff_ne_zero.mpr h)
  exact (not_lt_of_ge (hq r (ENNReal.coe_pos.mp hr))) hr'

omit [T2Space G] [μ.IsHaarMeasure] [μH.Regular] [ν.Regular] in
include hH in
/-- The fibre integral of the norm of a compact test satisfies Weil in lower-integral form. -/
lemma weilTest_fibreNorm
    (hν : ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
      ∫ x, φ x ∂μ = ∫ q : G ⧸ H, (∫ h : H, φ (q.out * (h : G)) ∂μH) ∂ν)
    {g : G → ℂ} (hc : Continuous g) (hs : HasCompactSupport g) :
    Measurable (fun q : G ⧸ H => ∫⁻ h : H, ‖g (q.out * (h : G))‖ₑ ∂μH) ∧
      (∫⁻ q : G ⧸ H, (∫⁻ h : H, ‖g (q.out * (h : G))‖ₑ ∂μH) ∂ν) = ∫⁻ x, ‖g x‖ₑ ∂μ := by
  have he (q : G ⧸ H) := ofReal_integral_norm_eq_lintegral_enorm
    (weilTest_fibre_integrable H hH μH hc hs q.out)
  simp_rw [← he]
  refine ⟨(continuous_realFibreIntegral H hH μH hc.norm hs.norm).measurable.ennreal_ofReal, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal
      (weilTest_realAverage_integrable H hH μH ν hc.norm hs.norm)
      (.of_forall fun q ↦ integral_nonneg fun h ↦ norm_nonneg _),
    ← integral_eq_integral_realFibreIntegral H μ μH ν hν hc.norm hs.norm,
    ofReal_integral_norm_eq_lintegral_enorm (hc.integrable_of_hasCompactSupport hs)]

include hH in
/-- Weil's formula for integrable functions: the fibre integrals exist quotient-almost
everywhere, define an integrable function and satisfy Weil's formula. -/
theorem weilQuotientIntegral_L1
    (hν : ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
      ∫ x, φ x ∂μ = ∫ q : G ⧸ H, (∫ h : H, φ (q.out * (h : G)) ∂μH) ∂ν)
    {f : G → ℂ} (hf : Integrable f μ) :
    (∀ᵐ q ∂ν, Integrable (fun h : H ↦ f (q.out * (h : G))) μH) ∧
      Integrable (cosetInt H μH f) ν ∧
      (∫ x, f x ∂μ) = ∫ q, cosetInt H μH f q ∂ν := by
  obtain ⟨g, hg, hs, he⟩ := exists_compactTest_tsum hf
  let B n (q : G ⧸ H) := ∫⁻ h : H, ‖g n (q.out * (h : G))‖ₑ ∂μH
  have hB n : Measurable (B n) ∧ (∫⁻ q, B n q ∂ν) = ∫⁻ x, ‖g n x‖ₑ ∂μ :=
    weilTest_fibreNorm H hH μ μH ν hν (hg n).1 (hg n).2
  have hsum : (∑' n, ∫⁻ q, B n q ∂ν) ≠ ⊤ := by simpa only [fun n ↦ (hB n).2] using hs
  have hfin : ∀ᵐ q ∂ν, ∑' n, B n q < ⊤ := by
    apply ae_lt_top' (AEMeasurable.tsum fun n ↦ (hB n).1.aemeasurable)
    rwa [lintegral_tsum fun n ↦ (hB n).1.aemeasurable]
  let A n := cosetInt H μH (g n)
  have hA n : AEStronglyMeasurable (A n) ν :=
    (weilTest_average H hH μH (hg n).1 (hg n).2).1.aestronglyMeasurable
  have hAsum : (∑' n, ∫⁻ q, ‖A n q‖ₑ ∂ν) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hsum
      (ENNReal.tsum_le_tsum (g := fun n ↦ ∫⁻ q, B n q ∂ν) fun n ↦ ?_)
    exact lintegral_mono fun q ↦ enorm_integral_le_lintegral_enorm _
  have hfib : ∀ᵐ q ∂ν, Integrable (fun h : H ↦ f (q.out * (h : G))) μH ∧
      cosetInt H μH f q = ∑' n, A n q := by
    filter_upwards [hfin, ae_weil_fibre H hH μ μH ν hν he] with q hq heq
    have hm n := (weilTest_fibre_integrable H hH μH (hg n).1 (hg n).2 q.out).1
    exact ⟨(integrable_tsum_of_lintegral_eNorm hm hq.ne).congr (Filter.EventuallyEq.symm heq),
      (integral_congr_ae heq).trans (integral_tsum hm hq.ne)⟩
  have heA : cosetInt H μH f =ᵐ[ν] fun q ↦ ∑' n, A n q := hfib.mono fun q hq ↦ hq.2
  refine ⟨hfib.mono fun q hq ↦ hq.1,
    (integrable_tsum_of_lintegral_eNorm hA hAsum).congr heA.symm, ?_⟩
  rw [integral_congr_ae he, integral_congr_ae heA, integral_tsum hA hAsum,
    integral_tsum (fun n ↦ (hg n).1.aestronglyMeasurable) hs]
  exact tsum_congr fun n ↦ hν (g n) (hg n).1 (hg n).2

end WeilQuotient

end Sol_LCAGroup_weil_quotient_integral_formula

open Sol_LCAGroup_weil_quotient_integral_formula in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular]
    (ν : Measure (G ⧸ H)) [ν.IsHaarMeasure] [ν.Regular]
    (hν : ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
      ∫ x, φ x ∂μ = ∫ q : G ⧸ H, (∫ h : H, φ (q.out * (h : G)) ∂μH) ∂ν)
    (f : G → ℂ) (hf : Integrable f μ) :
    (∀ᵐ q ∂ν, Integrable (fun h : H => f (q.out * (h : G))) μH) ∧
    Integrable (fun q : G ⧸ H => ∫ h : H, f (q.out * (h : G)) ∂μH) ν ∧
    ∫ x, f x ∂μ = ∫ q : G ⧸ H, (∫ h : H, f (q.out * (h : G)) ∂μH) ∂ν :=
  weilQuotientIntegral_L1 H hH μ μH ν hν hf
