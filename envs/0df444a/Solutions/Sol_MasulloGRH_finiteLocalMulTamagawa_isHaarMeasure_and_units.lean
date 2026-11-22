-- Prove2me | solution 1 for MasulloGRH.finiteLocalMulTamagawa_isHaarMeasure_and_units
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:33:16.141805+00:00
-- url     : https://prove2.me/submissions/c9298557-60b5-418e-bc2f-a97d5c68de2d

import Mathlib
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures
import Theorems.Thm_RiemannMasullo_locallyCompactSpace_adicCompletion

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false

/-!
# The local multiplicative Tamagawa measure at a finite place

`μ_v = q/(q-1) · |x|_v⁻¹ ν_v` restricted to `F_vˣ` is a Haar measure of `F_vˣ` and
`μ_v(𝒪_vˣ) = ν_v(𝒪_v) = N(𝔡_v)^{-1/2}`.

* The residue field of `𝒪_v` is `𝒪_F / 𝔭_v`, of cardinality `q = N(𝔭_v)`; hence `𝒪_v` is compact,
  `F_v` is locally compact, and the open unit ball has index `q` in `𝒪_v`.
* The module of `F_v` is the normalized absolute value: `μ(u • s) = ‖u‖ μ(s)` for every additive
  Haar measure `μ` (`distribHaarChar_eq_nnnorm`), checked on a uniformizer and on `𝒪_vˣ`.
* Therefore `|x|_v⁻¹ ν_v` is invariant under multiplication, and on `𝒪_vˣ = 𝒪_v \ {‖x‖ < 1}` the
  density is `1`, so `μ_v(𝒪_vˣ) = q/(q-1) · (1 - 1/q) · ν_v(𝒪_v)`.

The argument follows the proof in the open formalization mccorvie/riemann-masullo.

The platform theorem `RiemannMasullo.locallyCompactSpace_adicCompletion` (local compactness of
`F_v`) is imported because the definition of the additive Tamagawa measure `ν_v` refers to it
(it provides the instance needed to form `Measure.addHaar`).
-/

namespace Sol_MasulloGRH_finiteLocalMulTamagawa_isHaarMeasure_and_units

open Filter IsLocalRing Topology
open scoped WithZero Pointwise

variable {F : Type*} [Field F] [NumberField F]

/-- The norm of a nonzero element of the completion is `q ^ log (v x)`, where `q` is the absolute
norm of the prime. -/
theorem norm_eq_zpow_log (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) (hx : x ≠ 0) :
    ‖x‖ = (v.asIdeal.absNorm : ℝ) ^ WithZero.log (Valued.v x) := by
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ h0, WithZero.toAdd_unzero_eq_log]
  simp

/-- A uniformizer of the completed discrete valuation has norm the reciprocal of the
absolute norm of the prime ideal. -/
theorem norm_uniformizer_adicCompletion (v : HeightOneSpectrum (𝓞 F)) (π : v.adicCompletion F)
    (hπ : Valued.v.IsUniformizer π) :
    ‖π‖ = (v.asIdeal.absNorm : ℝ)⁻¹ := by
  have hval : Valued.v π = WithZero.exp (-1 : ℤ) := hπ.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective F)))
  rw [norm_eq_zpow_log v π hπ.ne_zero, hval, WithZero.log_exp]
  simp

/-- The residue field of a completion at a height-one prime is isomorphic to the quotient
of the base ring by that prime. -/
theorem nonempty_residueFieldEquiv_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    Nonempty ((𝓞 F ⧸ v.asIdeal) ≃+* ResidueField (v.adicCompletionIntegers F)) := by
  let O := v.adicCompletionIntegers F
  let f := (residue O).comp (algebraMap (𝓞 F) O)
  let q : 𝓞 F ⧸ v.asIdeal →+* ResidueField O := Ideal.Quotient.lift v.asIdeal f (by
    intro r hr
    rw [RingHom.comp_apply, residue_eq_zero_iff]
    apply (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).2
    change Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) < (1 : ℤᵐ⁰)
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v r
    exact h.trans_lt ((v.valuation_lt_one_iff_mem r).2 hr))
  let := Ideal.Quotient.field v.asIdeal
  refine ⟨RingEquiv.ofBijective q ⟨q.injective, ?_⟩⟩
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  -- Approximate the representative first by an element of `F`, then by one of `𝓞 F`.
  let ν : Valuation (v.adicCompletion F) ℤᵐ⁰ := Valued.v
  have hn : {z | ν (z - (x : v.adicCompletion F)) < 1} ∈ 𝓝 (x : v.adicCompletion F) := by
    refine Valued.mem_nhds.mpr ⟨1, ?_⟩
    intro z hz
    simpa using hz
  obtain ⟨a, ha⟩ := (v.denseRange_algebraMap F).mem_nhds hn
  change ν (algebraMap F (v.adicCompletion F) a - x) < 1 at ha
  have ha' : v.valuation F a ≤ 1 := by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    change ν (algebraMap F (v.adicCompletion F) a) ≤ 1
    simpa only [sub_add_cancel] using ν.map_add_le ha.le x.property
  obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer ha' 1
  have hr' : ν (algebraMap (𝓞 F) (v.adicCompletion F) r - algebraMap F (v.adicCompletion F) a) < 1 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← map_sub]
    change Valued.v (((algebraMap (𝓞 F) F) r - a : F) : v.adicCompletion F) < (1 : ℤᵐ⁰)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simpa only [Units.val_one] using hr
  refine ⟨Ideal.Quotient.mk _ r, sub_eq_zero.mp ?_⟩
  change residue O (algebraMap (𝓞 F) O r) - residue O x = 0
  rw [← map_sub, residue_eq_zero_iff]
  apply (Valuation.mem_maximalIdeal_iff _ ν).2
  change ν (algebraMap (𝓞 F) (v.adicCompletion F) r - x) < 1
  simpa only [sub_add_sub_cancel] using ν.map_add_lt hr' ha

/-- The cardinality of the completed residue field is the absolute norm of the prime. -/
theorem card_residueField_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (ResidueField (v.adicCompletionIntegers F)) = v.asIdeal.absNorm := by
  obtain ⟨e⟩ := nonempty_residueFieldEquiv_adicCompletion (F := F) v
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr e.toEquiv).symm

/-- The residue field of the completion at a height-one prime is finite. -/
theorem finite_residueField_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    Finite (ResidueField (v.adicCompletionIntegers F)) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_residueField_adicCompletion]
  exact (HeightOneSpectrum.one_lt_absNorm v).pos.ne'

open Valued.integer in
/-- Closed balls in the completion at a height-one prime are compact. -/
theorem properSpace_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    ProperSpace (v.adicCompletion F) := by
  have : IsDiscreteValuationRing (v.adicCompletionIntegers F) := inferInstance
  exact (properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (Γ₀ := ℤᵐ⁰)).2 ⟨inferInstance, ‹_›, finite_residueField_adicCompletion v⟩

/-- The integers of an adic completion are compact. -/
theorem compactSpace_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (v.adicCompletionIntegers F) := by
  have : IsClosed (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    Valued.isClosed_valuationSubring _
  have hcomplete : CompleteSpace (v.adicCompletionIntegers F) := IsClosed.completeSpace_coe
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
    ⟨hcomplete, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
      finite_residueField_adicCompletion v⟩


section Measure

variable (v : HeightOneSpectrum (𝓞 F))

/-- An element of the completion has norm one exactly when its valuation is one. -/
theorem norm_eq_one_iff (x : v.adicCompletion F) : ‖x‖ = 1 ↔ Valued.v x = 1 := by
  rw [le_antisymm_iff, Valued.toNormedField.norm_le_one_iff,
    Valued.toNormedField.one_le_norm_iff, ← le_antisymm_iff]

/-- The ring of integers of the completion is the closed unit ball. -/
theorem mem_integers_iff_norm (x : v.adicCompletion F) :
    x ∈ v.adicCompletionIntegers F ↔ ‖x‖ ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).trans
    Valued.toNormedField.norm_le_one_iff.symm

/-- The open unit ball is a subgroup of index `q = N(𝔭)` of the ring of integers, so its Haar
measure is `μ(𝒪) / q`. -/
theorem measure_ball_eq [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] :
    μ {x : v.adicCompletion F | ‖x‖ < 1} =
      μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) /
        (v.asIdeal.absNorm : ℝ≥0∞) := by
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  have hq₀ : (v.asIdeal.absNorm : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).pos.ne'
  have hqf : (v.asIdeal.absNorm : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hO : IsOpen (O : Set K) := Valued.isOpen_valuationSubring K
  let val : Valuation K ℤᵐ⁰ := Valued.v
  let : MeasurableSpace O := borel _
  have : BorelSpace O := ⟨rfl⟩
  let i := O.toSubring.subtype
  have hi : Topology.IsOpenEmbedding i := hO.isOpenEmbedding_subtypeVal
  let μO := μ.comap i
  have : μO.IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.comap (mH := inferInstance) μ (f := i.toAddMonoidHom) hi
  let r := (IsLocalRing.residue O).toAddMonoidHom
  have hindex : r.ker.index = v.asIdeal.absNorm := by
    rw [AddSubgroup.index_ker,
      AddMonoidHom.range_eq_top.mpr (IsLocalRing.residue_surjective (R := O)),
      AddSubgroup.card_top, card_residueField_adicCompletion]
  have : r.ker.FiniteIndex :=
    ⟨by rw [hindex]; exact (HeightOneSpectrum.one_lt_absNorm v).pos.ne'⟩
  have hker (a : O) : a ∈ r.ker ↔ ‖(a : K)‖ < 1 :=
    (IsLocalRing.residue_eq_zero_iff a).trans
      ((Valuation.mem_maximalIdeal_iff K val).trans Valued.toNormedField.norm_lt_one_iff.symm)
  have hkerMeas : MeasurableSet (r.ker : Set O) := by
    change MeasurableSet {a : O | a ∈ r.ker}
    simp_rw [hker]
    exact (isOpen_lt (continuous_norm.comp
      (continuous_subtype_val : Continuous (Subtype.val : O → K))) continuous_const).measurableSet
  have himg : i '' (r.ker : Set O) = {x : K | ‖x‖ < 1} := by
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨a, ha, rfl⟩
      exact (hker a).mp ha
    · intro hx
      let a : O := ⟨x, (mem_integers_iff_norm v x).mpr (le_of_lt hx)⟩
      exact ⟨a, (hker a).mpr hx, rfl⟩
  have h := r.ker.index_mul_measure hkerMeas μO
  change (r.ker.index : ℝ≥0∞) * μ.comap i r.ker = μ.comap i Set.univ at h
  rw [hindex, hi.measurableEmbedding.comap_apply, hi.measurableEmbedding.comap_apply,
    himg, Set.image_univ, show Set.range i = (O : Set K) from Subtype.range_coe] at h
  rw [← h, mul_comm, ENNReal.mul_div_cancel_right hq₀ hqf]

/-- In `ℤᵐ⁰` the elements `< 1` are those `≤ exp (-1)`. -/
theorem lt_one_iff_le_exp_neg_one (y : ℤᵐ⁰) : y < 1 ↔ y ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · rw [← WithZero.exp_zero, ← WithZero.log_lt_iff_lt_exp hy, ← WithZero.log_le_iff_le_exp hy]
    omega

/-- There is a unit `p` of valuation `exp (-1)` (a uniformizer); multiplication by `p` maps the
ring of integers onto the open unit ball. -/
theorem exists_uniformizer_smul :
    ∃ p : (v.adicCompletion F)ˣ, Valued.v p.val = WithZero.exp (-1 : ℤ) ∧
      p • (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = {x | ‖x‖ < 1} := by
  obtain ⟨π, hπ⟩ := v.valuedAdicCompletion_surjective F (WithZero.exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨Units.mk0 π hπ0, hπ, ?_⟩
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem, SetLike.mem_coe,
    HeightOneSpectrum.mem_adicCompletionIntegers, Set.mem_ofPred_eq,
    Valued.toNormedField.norm_lt_one_iff, lt_one_iff_le_exp_neg_one]
  simp only [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, smul_eq_mul, map_mul,
    map_inv₀, hπ]
  rw [inv_mul_le_iff₀ (by simp), mul_one]

/-- The module of the completion `F_v`: multiplication by a unit `u` scales every additive Haar
measure by the normalized absolute value `‖u‖`. -/
theorem distribHaarChar_eq_nnnorm [LocallyCompactSpace (v.adicCompletion F)]
    (u : (v.adicCompletion F)ˣ) :
    distribHaarChar (v.adicCompletion F) u = ‖u.val‖₊ := by
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  let μ : Measure K := Measure.addHaar
  have hO : IsOpen (O : Set K) := Valued.isOpen_valuationSubring K
  have : CompactSpace O := compactSpace_adicCompletionIntegers v
  have hOc : IsCompact (O : Set K) := isCompact_iff_compactSpace.mpr inferInstance
  have hO₀ : μ (O : Set K) ≠ 0 := (hO.measure_pos μ ⟨0, O.zero_mem⟩).ne'
  have hOf : μ (O : Set K) ≠ ⊤ := hOc.measure_ne_top
  have hq : (0 : ℝ) < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).pos
  obtain ⟨p, hp, hpO⟩ := exists_uniformizer_smul v
  have hpnorm : ‖p.val‖₊ = (v.asIdeal.absNorm : ℝ≥0)⁻¹ := by
    apply NNReal.eq
    rw [coe_nnnorm, norm_eq_zpow_log v p.val p.ne_zero, hp, WithZero.log_exp]
    simp
  -- the module of a uniformizer
  have hχp : distribHaarChar K p = ‖p.val‖₊ := by
    apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hO₀ hOf
    rw [hpO, measure_ball_eq v μ, hpnorm, ENNReal.coe_inv (by exact_mod_cast hq.ne'),
      ENNReal.coe_natCast, div_eq_mul_inv, mul_comm]
  -- the module of a unit of the ring of integers
  have hχU (w : Kˣ) (hw : Valued.v w.val = 1) : distribHaarChar K w = 1 := by
    apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hO₀ hOf
    have hset : w • (O : Set K) = O := by
      ext x
      rw [Set.mem_smul_set_iff_inv_smul_mem, SetLike.mem_coe, SetLike.mem_coe,
        HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers]
      simp only [Units.smul_def, Units.val_inv_eq_inv_val, smul_eq_mul, map_mul, map_inv₀, hw,
        inv_one, one_mul]
    rw [hset, ENNReal.coe_one, one_mul]
  -- every unit is a power of the uniformizer times a unit of the ring of integers
  set n : ℤ := WithZero.log (Valued.v u.val) with hn
  have hvu : Valued.v u.val = WithZero.exp n :=
    (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr u.ne_zero)).symm
  let w : Kˣ := u * p ^ n
  have hw : Valued.v w.val = 1 := by
    simp only [w, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hp, hvu]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hwnorm : ‖w.val‖₊ = 1 := NNReal.eq ((norm_eq_one_iff v w.val).mpr hw)
  have hu : u = w * p ^ (-n) := by
    simp only [w, zpow_neg, mul_inv_cancel_right]
  have hval : u.val = w.val * p.val ^ (-n) := by
    conv_lhs => rw [hu]
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val]
  rw [hval, nnnorm_mul, nnnorm_zpow, hwnorm, one_mul]
  conv_lhs => rw [hu]
  rw [map_mul, map_zpow, hχU w hw, hχp, one_mul]

/-- Multiplication by `a ≠ 0` scales an additive Haar measure of `F_v` by `‖a‖`, i.e.
`μ.map (a * ·) = ‖a‖⁻¹ • μ`. -/
theorem map_mul_left_eq [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]
    (a : v.adicCompletion F) (ha : a ≠ 0) :
    μ.map (a * ·) = ((‖a‖₊ : ℝ≥0∞) ^ 1)⁻¹ • μ := by
  have : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let u : (v.adicCompletion F)ˣ := Units.mk0 a ha
  ext s hs
  have hpre : (a * ·) ⁻¹' s = u⁻¹ • s := by
    ext x
    rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    rfl
  rw [Measure.map_apply (measurable_const_mul a) hs, hpre, ← distribHaarChar_mul μ,
    distribHaarChar_eq_nnnorm v, Units.val_inv_eq_inv_val, nnnorm_inv,
    ENNReal.coe_inv (by simp), pow_one]
  rfl

end Measure

/-- On the units of a normed field `K`, an additive Haar measure `μ` weighted by `‖x‖⁻ᵐ` and
restricted to `Kˣ` is a multiplicative Haar measure, provided multiplication by `a ≠ 0` scales
`μ` by `‖a‖ᵐ`, i.e. `μ.map (a * ·) = ‖a‖⁻ᵐ • μ`. -/
theorem isHaarMeasure_comap_units_withDensity {K : Type*} [NormedField K]
    [MeasurableSpace K] [BorelSpace K] [MeasurableSpace Kˣ] [BorelSpace Kˣ]
    (μ : Measure K) [μ.IsAddHaarMeasure] (m : ℕ)
    (hscale : ∀ a : K, a ≠ 0 → μ.map (a * ·) = (((‖a‖₊ : ℝ≥0∞) ^ m))⁻¹ • μ) :
    ((μ.withDensity fun x ↦ ((‖x‖₊ : ℝ≥0∞) ^ m)⁻¹).comap Units.val).IsHaarMeasure := by
  set ρ : K → ℝ≥0∞ := fun x ↦ ((‖x‖₊ : ℝ≥0∞) ^ m)⁻¹ with hρ
  set μ' := μ.withDensity ρ
  have hρm : Measurable ρ := by
    simp only [hρ]
    fun_prop
  have hopen : Topology.IsOpenEmbedding (Units.val : Kˣ → K) :=
    IsOpenUnits.isOpenEmbedding_unitsVal (M := K)
  have hemb : MeasurableEmbedding (Units.val : Kˣ → K) := hopen.measurableEmbedding
  have himg : ∀ s : Set Kˣ, MeasurableSet s → MeasurableSet (Units.val '' s) :=
    fun s hs ↦ hemb.measurableSet_image.mpr hs
  -- invariance of `μ'` under multiplication by a nonzero scalar
  have hinv : ∀ a : K, a ≠ 0 → μ'.map (a * ·) = μ' := by
    intro a ha
    have hmeas : Measurable (a * · : K → K) := (continuous_const.mul continuous_id).measurable
    set N : ℝ≥0∞ := (‖a‖₊ : ℝ≥0∞) ^ m with hN
    have hN0 : N ≠ 0 := by
      have : (‖a‖₊ : ℝ≥0∞) ≠ 0 := by simpa using ha
      exact pow_ne_zero m this
    have hNt : N ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
    have hρa (x : K) : ρ x = N * ρ (a * x) := by
      have hx : ((‖a * x‖₊ : ℝ≥0∞)) ^ m = N * (‖x‖₊ : ℝ≥0∞) ^ m := by
        rw [nnnorm_mul, ENNReal.coe_mul, mul_pow]
      simp only [hρ]
      rw [hx, ENNReal.mul_inv (Or.inl hN0) (Or.inl hNt), ← mul_assoc,
        ENNReal.mul_inv_cancel hN0 hNt, one_mul]
    ext t ht
    rw [Measure.map_apply hmeas ht, withDensity_apply _ (hmeas ht), withDensity_apply _ ht]
    conv_lhs => rw [show ρ = fun x ↦ N * ρ (a * x) from funext hρa]
    rw [lintegral_const_mul' _ _ hNt, ← setLIntegral_map ht hρm hmeas, hscale a ha,
      Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel hN0 hNt, one_mul]
  have hρpos : ∀ x, ρ x ≠ 0 := fun x ↦
    ENNReal.inv_ne_zero.mpr (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have h1 : IsFiniteMeasureOnCompacts (μ'.comap (Units.val : Kˣ → K)) := by
    refine ⟨fun C hC ↦ ?_⟩
    rw [hemb.comap_apply]
    rcases C.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨u₀, -, hu₀⟩ := hC.exists_isMinOn hne
      (continuous_norm.comp Units.continuous_val).continuousOn
    have hbound : ∀ x ∈ Units.val '' C, ρ x ≤ ρ u₀.val := by
      rintro _ ⟨u, hu, rfl⟩
      simp only [hρ]
      refine ENNReal.inv_le_inv.mpr (pow_le_pow_left₀ zero_le ?_ m)
      exact ENNReal.coe_le_coe.mpr (hu₀ hu)
    have hfin : ρ u₀.val ≠ ⊤ := by
      have : (‖(u₀ : K)‖₊ : ℝ≥0∞) ≠ 0 := by simp
      exact ENNReal.inv_ne_top.mpr (pow_ne_zero m this)
    calc μ' (Units.val '' C) = ∫⁻ x in Units.val '' C, ρ x ∂μ :=
          withDensity_apply _ (himg _ hC.measurableSet)
      _ ≤ ∫⁻ _ in Units.val '' C, ρ u₀.val ∂μ := setLIntegral_mono measurable_const hbound
      _ = ρ u₀.val * μ (Units.val '' C) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top hfin.lt_top
          (hC.image Units.continuous_val).measure_lt_top
  have h3 : Measure.IsOpenPosMeasure (μ'.comap (Units.val : Kˣ → K)) := by
    refine ⟨fun U hU hne ↦ ?_⟩
    rw [hemb.comap_apply]
    intro h0
    rw [withDensity_apply_eq_zero' hρm.aemeasurable] at h0
    have : {x | ρ x ≠ 0} = Set.univ := Set.eq_univ_of_forall hρpos
    rw [this, Set.univ_inter] at h0
    have hopen' : IsOpen (Units.val '' U) := hopen.isOpenMap U hU
    exact (hopen'.measure_pos μ (hne.image _)).ne' h0
  have h2 : Measure.IsMulLeftInvariant (μ'.comap (Units.val : Kˣ → K)) := by
    refine ⟨fun g ↦ ?_⟩
    ext s hs
    have hmeas : Measurable (g * · : Kˣ → Kˣ) := (continuous_const.mul continuous_id).measurable
    rw [Measure.map_apply hmeas hs, hemb.comap_apply, hemb.comap_apply]
    have himage : Units.val '' ((g * ·) ⁻¹' s) = (g.val * ·) ⁻¹' (Units.val '' s) := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨g * u, hu, rfl⟩
      · rintro ⟨u, hu, hux⟩
        refine ⟨g⁻¹ * u, by simpa using hu, ?_⟩
        simp only [Units.val_mul, hux, ← mul_assoc, Units.inv_mul, one_mul]
    rw [himage, ← Measure.map_apply (measurable_const_mul g.val) (himg s hs),
      hinv g.val g.ne_zero]
  exact { toIsFiniteMeasureOnCompacts := h1, toIsMulLeftInvariant := h2, toIsOpenPosMeasure := h3 }

end Sol_MasulloGRH_finiteLocalMulTamagawa_isHaarMeasure_and_units

open MasulloGRH Sol_MasulloGRH_finiteLocalMulTamagawa_isHaarMeasure_and_units in
theorem solution
    (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (finiteLocalMulTamagawa F v).IsHaarMeasure ∧
    finiteLocalMulTamagawa F v {u | Valued.v (u : v.adicCompletion F) = 1} =
      (ENNReal.ofReal (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
        multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))))⁻¹ := by
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  have : ProperSpace K := properSpace_adicCompletion v
  have : CompactSpace O := compactSpace_adicCompletionIntegers v
  have hO : IsOpen (O : Set K) := Valued.isOpen_valuationSubring K
  have hOc : IsCompact (O : Set K) := isCompact_iff_compactSpace.mpr inferInstance
  have hOmem (x : K) : x ∈ (O : Set K) ↔ ‖x‖ ≤ 1 := mem_integers_iff_norm v x
  -- the residue cardinality `q > 1`
  set q : ℝ≥0∞ := (Ideal.absNorm v.asIdeal : ℝ≥0∞) with hq
  have hq1 : 1 < q := by
    rw [hq]
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq₀ : q ≠ 0 := (zero_lt_one.trans hq1).ne'
  have hqf : q ≠ ⊤ := ENNReal.natCast_ne_top _
  have hqsub : q - 1 ≠ 0 := (tsub_pos_of_lt hq1).ne'
  have hqsubf : q - 1 ≠ ⊤ := (tsub_le_self.trans_lt hqf.lt_top).ne
  -- the additive Tamagawa measure `ν = (m / μ₀(𝒪)) • μ₀`, `μ₀` a Haar measure
  set m : ℝ≥0∞ := (ENNReal.ofReal (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
    multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))))⁻¹ with hm
  have hqR : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).pos
  have hsqrt := Real.sqrt_pos_of_pos
    (pow_pos hqR (multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))))
  have hm₀ : m ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hmf : m ≠ ⊤ := ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hsqrt).ne'
  let μ₀ : Measure K := Measure.addHaar
  have hμ₀pos : μ₀ (O : Set K) ≠ 0 := (hO.measure_pos μ₀ ⟨0, O.zero_mem⟩).ne'
  have hμ₀fin : μ₀ (O : Set K) ≠ ⊤ := hOc.measure_ne_top
  set ν : Measure K := RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v with hν
  have hνdef : ν = (m / μ₀ (O : Set K)) • μ₀ := rfl
  have hc₀ : m / μ₀ (O : Set K) ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hm₀, hμ₀fin⟩
  have hcf : m / μ₀ (O : Set K) ≠ ⊤ := ENNReal.div_ne_top hmf hμ₀pos
  have hνHaar : ν.IsAddHaarMeasure := by
    rw [hνdef]
    exact Measure.IsAddHaarMeasure.smul μ₀ hc₀ hcf
  have hνReg : ν.Regular := by
    rw [hνdef]
    exact Measure.Regular.smul hcf
  have hνO : ν (O : Set K) = m := by
    rw [hνdef, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.div_mul_cancel hμ₀pos hμ₀fin
  -- the weighted measure on the units is a Haar measure
  have hHaar := isHaarMeasure_comap_units_withDensity ν 1 (map_mul_left_eq v ν)
  simp only [pow_one] at hHaar
  have he : MeasurableEmbedding (Units.val : Kˣ → K) :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  refine ⟨?_, ?_⟩
  · unfold finiteLocalMulTamagawa
    exact Measure.IsHaarMeasure.smul _ (ENNReal.div_ne_zero.mpr ⟨hq₀, hqsubf⟩)
      (ENNReal.div_ne_top hqf hqsub)
  · -- the units of the ring of integers: `𝒪 \ {‖x‖ < 1}`, on which the density is `1`
    set U : Set Kˣ := {u | Valued.v (u : K) = 1} with hU
    have hUimage : (Units.val : Kˣ → K) '' U = (O : Set K) \ {x : K | ‖x‖ < 1} := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        have h1 : ‖(u : K)‖ = 1 := (norm_eq_one_iff v _).mpr hu
        exact ⟨(hOmem _).mpr h1.le, fun h : ‖(u : K)‖ < 1 ↦ h.ne h1⟩
      · rintro ⟨hx1, hx2⟩
        have h1 : ‖x‖ = 1 := le_antisymm ((hOmem x).mp hx1) (not_lt.mp hx2)
        have hx₀ : x ≠ 0 := norm_ne_zero_iff.mp (h1.trans_ne one_ne_zero)
        exact ⟨Units.mk0 x hx₀, (norm_eq_one_iff v x).mp h1, rfl⟩
    have hballm : MeasurableSet {x : K | ‖x‖ < 1} :=
      (isOpen_lt continuous_norm continuous_const).measurableSet
    have hsub : {x : K | ‖x‖ < 1} ⊆ (O : Set K) := fun x hx ↦ (hOmem x).mpr (le_of_lt hx)
    have hballf : ν {x : K | ‖x‖ < 1} ≠ ⊤ :=
      ((measure_mono hsub).trans_lt (hνO ▸ hmf.lt_top)).ne
    have hUm : MeasurableSet ((Units.val : Kˣ → K) '' U) := by
      rw [hUimage]
      exact hO.measurableSet.diff hballm
    have hνU : ((ν.withDensity fun x ↦ (‖x‖₊ : ℝ≥0∞)⁻¹).comap (Units.val : Kˣ → K)) U =
        (1 - q⁻¹) * m := by
      rw [he.comap_apply, withDensity_apply _ hUm]
      calc (∫⁻ x in Units.val '' U, (‖x‖₊ : ℝ≥0∞)⁻¹ ∂ν)
          = ∫⁻ _ in Units.val '' U, (1 : ℝ≥0∞) ∂ν := by
            apply setLIntegral_congr_fun hUm
            rintro _ ⟨u, hu, rfl⟩
            have h1 : ‖(u : K)‖₊ = 1 := NNReal.eq ((norm_eq_one_iff v _).mpr hu)
            simp [h1]
        _ = (1 - q⁻¹) * m := by
            rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
              one_mul, hUimage, measure_sdiff hsub hballm.nullMeasurableSet hballf,
              measure_ball_eq v ν, hνO, ENNReal.sub_mul (fun _ _ ↦ hmf), one_mul,
              div_eq_mul_inv, mul_comm q⁻¹]
    have hdiv : 1 - q⁻¹ = (q - 1) / q := by
      rw [div_eq_mul_inv, ENNReal.sub_mul (fun _ _ ↦ ENNReal.inv_ne_top.mpr hq₀),
        ENNReal.mul_inv_cancel hq₀ hqf, one_mul]
    change (q / (q - 1)) *
      ((ν.withDensity fun x ↦ (‖x‖₊ : ℝ≥0∞)⁻¹).comap (Units.val : Kˣ → K)) U = m
    have hcq : q / (q - 1) * ((q - 1) / q) = 1 := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ← mul_assoc (q - 1)⁻¹,
        ENNReal.inv_mul_cancel hqsub hqsubf, one_mul, ENNReal.mul_inv_cancel hq₀ hqf]
    rw [hνU, hdiv, ← mul_assoc, hcq, one_mul]
