-- Prove2me | solution 1 for MasulloGRH.exists_finiteLocalZeta_eq_laurent_mul_eulerFactor
-- status  : ACCEPTED   (prove)
-- author  : @WalrusPaul
-- created : 2026-11-22T19:32:45.368289+00:00
-- url     : https://prove2.me/submissions/66ab3c8b-f3f8-45ed-bdb1-11a719b00582

import Mathlib
import Definitions.Def_MasulloGRH_HeckeLFunction
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

open MasulloGRH
open scoped ENNReal NNReal Pointwise

namespace TateZ

variable {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

instance lcs : LocallyCompactSpace (v.adicCompletion F) :=
  RiemannMasullo.locallyCompactSpace_adicCompletion v

/-- `q = N(v)` as a real number. -/
noncomputable abbrev qr : ℝ := (Ideal.absNorm v.asIdeal : ℝ)

lemma one_lt_qr : (1 : ℝ) < qr v := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

lemma qr_pos : (0 : ℝ) < qr v := lt_trans one_pos (one_lt_qr v)

lemma norm_eq_zpow (x : v.adicCompletion F) (k : ℤ)
    (hx : Valued.v x = WithZero.exp k) :
    ‖x‖ = qr v ^ k := by
  rw [FinitePlace.norm_def, hx]
  rw [WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
  simp only [WithZero.exp, WithZero.unzero_coe, toAdd_ofAdd]
  push_cast; rfl

lemma norm_cases (x : v.adicCompletion F) (hx : x ≠ 0) : ∃ k : ℤ, ‖x‖ = qr v ^ k := by
  have hx0 : Valued.v x ≠ 0 := by simpa using hx
  exact ⟨_, norm_eq_zpow v x _ (WithZero.exp_log hx0).symm⟩

lemma exists_unif : ∃ π : (v.adicCompletion F)ˣ, ‖(π : v.adicCompletion F)‖ = (qr v)⁻¹ := by
  obtain ⟨x, hx⟩ := v.valuedAdicCompletion_surjective F (WithZero.exp (-1 : ℤ))
  have hx0 : x ≠ 0 := by
    intro h; rw [h, map_zero] at hx; exact WithZero.zero_ne_coe hx
  refine ⟨Units.mk0 x hx0, ?_⟩
  rw [Units.val_mk0, norm_eq_zpow v x (-1) hx, zpow_neg_one]

/-- Values of the norm below one are at most `q⁻¹`. -/
lemma norm_le_inv_of_lt_one (x : v.adicCompletion F) (hx : ‖x‖ < 1) : ‖x‖ ≤ (qr v)⁻¹ := by
  by_cases h0 : x = 0
  · subst h0; simp
  obtain ⟨k, hk⟩ := norm_cases v x h0
  rw [hk] at hx ⊢
  have hk' : k < 0 := by
    by_contra hcon
    push Not at hcon
    have := one_le_zpow₀ (one_lt_qr v).le hcon
    linarith
  rw [← zpow_neg_one]
  exact zpow_le_zpow_right₀ (one_lt_qr v).le (by omega)

@[instance_reducible] noncomputable def nnf : NontriviallyNormedField (v.adicCompletion F) :=
  { (inferInstance : NormedField (v.adicCompletion F)) with
    non_trivial := by
      obtain ⟨π, hπ⟩ := exists_unif v
      refine ⟨((π : v.adicCompletion F))⁻¹, ?_⟩
      rw [norm_inv, hπ, inv_inv]; exact one_lt_qr v }

lemma properSpace : ProperSpace (v.adicCompletion F) :=
  @ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _ (nnf v)
    (inferInstance : WeaklyLocallyCompactSpace (v.adicCompletion F))

lemma isCompact_closedBall (x : v.adicCompletion F) (r : ℝ) :
    IsCompact (Metric.closedBall x r) := by
  have := properSpace v
  exact ProperSpace.isCompact_closedBall x r

lemma integers_eq : (v.adicCompletionIntegers F : Set (v.adicCompletion F)) =
    Metric.closedBall 0 1 := by
  ext x
  simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Metric.mem_closedBall,
    dist_zero_right]
  exact (Valued.toNormedField.norm_le_one_iff).symm

noncomputable abbrev ν : Measure (v.adicCompletion F) :=
  RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v

lemma ν_eq : ν v = ((ENNReal.ofReal √((Ideal.absNorm v.asIdeal : ℝ) ^
      multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))))⁻¹ /
      Measure.addHaar (Metric.closedBall (0 : v.adicCompletion F) 1)) • Measure.addHaar := by
  rw [← integers_eq]; rfl

lemma addHaar_ball_pos : Measure.addHaar (Metric.closedBall (0 : v.adicCompletion F) 1) ≠ 0 :=
  ((IsUltrametricDist.isOpen_closedBall (0 : v.adicCompletion F) one_ne_zero).measure_pos
    _ ⟨0, Metric.mem_closedBall_self zero_le_one⟩).ne'

lemma addHaar_ball_lt_top : Measure.addHaar (Metric.closedBall (0 : v.adicCompletion F) 1) ≠ ∞ :=
  (isCompact_closedBall v 0 1).measure_lt_top.ne

lemma cst_ne_zero : ((ENNReal.ofReal √((Ideal.absNorm v.asIdeal : ℝ) ^
      multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))))⁻¹ /
      Measure.addHaar (Metric.closedBall (0 : v.adicCompletion F) 1)) ≠ 0 := by
  apply ENNReal.div_ne_zero.mpr
  refine ⟨by simp, addHaar_ball_lt_top v⟩

lemma cst_ne_top : ((ENNReal.ofReal √((Ideal.absNorm v.asIdeal : ℝ) ^
      multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))))⁻¹ /
      Measure.addHaar (Metric.closedBall (0 : v.adicCompletion F) 1)) ≠ ∞ := by
  apply ENNReal.div_ne_top _ (addHaar_ball_pos v)
  rw [ENNReal.inv_ne_top, ENNReal.ofReal_ne_zero_iff] -- ?
  apply Real.sqrt_pos.mpr
  exact pow_pos (qr_pos v) _

instance : (ν v).IsAddHaarMeasure := by
  rw [ν_eq]; exact Measure.IsAddHaarMeasure.smul _ (cst_ne_zero v) (cst_ne_top v)

instance : (ν v).Regular := by
  rw [ν_eq]; exact Measure.Regular.smul (cst_ne_top v)


/-! ### The index `[𝒪_v : 𝔪_v] = q` -/

/-- the image of a global integer in the completion -/
noncomputable def ι (r : 𝓞 F) : v.adicCompletion F :=
  algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r)

lemma norm_ι_le_one (r : 𝓞 F) : ‖ι v r‖ ≤ 1 :=
  FinitePlace.norm_le_one (K := F) v r

lemma norm_ι_lt_one_iff (r : 𝓞 F) : ‖ι v r‖ < 1 ↔ r ∈ v.asIdeal :=
  FinitePlace.norm_lt_one_iff_mem (K := F) v r

lemma ι_sub (r s : 𝓞 F) : ι v (r - s) = ι v r - ι v s := by
  simp [ι, map_sub]

lemma approx (x : v.adicCompletion F) (hx : ‖x‖ ≤ 1) : ∃ r : 𝓞 F, ‖x - ι v r‖ < 1 := by
  obtain ⟨k, hk⟩ := (Metric.denseRange_iff.mp (HeightOneSpectrum.denseRange_algebraMap (K := F) v))
    x 1 one_pos
  rw [dist_eq_norm] at hk
  have hk1 : ‖algebraMap F (v.adicCompletion F) k‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (x - algebraMap F (v.adicCompletion F) k) (-x)
    have : x - algebraMap F (v.adicCompletion F) k + -x = -(algebraMap F (v.adicCompletion F) k) := by
      ring
    rw [this, norm_neg, norm_neg] at h
    exact h.trans (max_le hk.le hx)
  have hv : v.valuation F k ≤ 1 := by
    have := (Valued.toNormedField.norm_le_one_iff).mp hk1
    rwa [show algebraMap F (v.adicCompletion F) k = (k : v.adicCompletion F) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hv 1
  refine ⟨a, ?_⟩
  have h2 : ‖ι v a - algebraMap F (v.adicCompletion F) k‖ < 1 := by
    rw [ι, ← map_sub]
    apply (Valued.toNormedField.norm_lt_one_iff).mpr
    rw [show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a - k) =
      ((algebraMap (𝓞 F) F a - k : F) : v.adicCompletion F) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simpa using ha
  have h := IsUltrametricDist.norm_add_le_max (x - algebraMap F (v.adicCompletion F) k)
    (algebraMap F (v.adicCompletion F) k - ι v a)
  rw [show x - algebraMap F (v.adicCompletion F) k + (algebraMap F (v.adicCompletion F) k - ι v a)
    = x - ι v a by ring] at h
  rw [← norm_neg (algebraMap F _ k - ι v a), neg_sub] at h
  exact h.trans_lt (max_lt hk h2)

lemma card_quot : Nat.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

lemma finite_quot : Finite (𝓞 F ⧸ v.asIdeal) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_quot]
  have := NumberField.HeightOneSpectrum.one_lt_absNorm v
  omega

lemma index_eq : ν v (Metric.closedBall 0 1) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) *
    ν v (Metric.ball 0 1) := by
  have := finite_quot v
  let _ := Fintype.ofFinite (𝓞 F ⧸ v.asIdeal)
  obtain ⟨rep, hmk⟩ : ∃ rep : (𝓞 F ⧸ v.asIdeal) → 𝓞 F,
      ∀ c, Ideal.Quotient.mk v.asIdeal (rep c) = c :=
    ⟨fun c => Quotient.out c, fun c => Ideal.Quotient.mk_out c⟩
  obtain ⟨T, hTdef⟩ : ∃ T : (𝓞 F ⧸ v.asIdeal) → Set (v.adicCompletion F),
      T = fun c => Metric.ball (ι v (rep c)) 1 := ⟨_, rfl⟩
  have hcover : Metric.closedBall 0 1 = ⋃ c, T c := by
    ext x
    simp only [mem_closedBall_zero_iff, Set.mem_iUnion, mem_ball_iff_norm, hTdef]
    constructor
    · intro hx
      obtain ⟨r, hr⟩ := approx v x hx
      refine ⟨Ideal.Quotient.mk v.asIdeal r, ?_⟩
      have h1 : rep (Ideal.Quotient.mk v.asIdeal r) - r ∈ v.asIdeal := by
        rw [← Ideal.Quotient.eq, hmk]
      have h2 := (norm_ι_lt_one_iff v _).mpr h1
      rw [ι_sub] at h2
      have h := IsUltrametricDist.norm_add_le_max (x - ι v r)
        (ι v r - ι v (rep (Ideal.Quotient.mk v.asIdeal r)))
      rw [show x - ι v r + (ι v r - ι v (rep (Ideal.Quotient.mk v.asIdeal r))) =
        x - ι v (rep (Ideal.Quotient.mk v.asIdeal r)) by ring] at h
      rw [← norm_neg (ι v r - _), neg_sub] at h
      exact h.trans_lt (max_lt hr h2)
    · rintro ⟨c, hc⟩
      have h := IsUltrametricDist.norm_add_le_max (x - ι v (rep c)) (ι v (rep c))
      rw [sub_add_cancel] at h
      exact h.trans (max_le hc.le (norm_ι_le_one v _))
  have hdisj : Pairwise (Function.onFun Disjoint T) := by
    intro c c' hcc'
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    simp only [mem_ball_iff_norm, hTdef] at hx hx'
    apply hcc'
    rw [← hmk c, ← hmk c', Ideal.Quotient.eq, ← norm_ι_lt_one_iff, ι_sub]
    have h := IsUltrametricDist.norm_add_le_max (ι v (rep c) - x) (x - ι v (rep c'))
    rw [sub_add_sub_cancel] at h
    rw [← norm_neg (ι v (rep c) - x), neg_sub] at h
    exact h.trans_lt (max_lt hx hx')
  have hT : ∀ c, ν v (T c) = ν v (Metric.ball 0 1) := by
    intro c
    have : T c = (fun h => -ι v (rep c) + h) ⁻¹' Metric.ball 0 1 := by
      rw [preimage_add_ball]; simp [hTdef]
    rw [this, measure_preimage_add]
  rw [hcover, measure_iUnion hdisj (fun c => by rw [hTdef]; exact Metric.isOpen_ball.measurableSet)]
  simp only [hT, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [Fintype.card_eq_nat_card, card_quot]


/-! ### Scaling of the additive Haar measure -/

lemma smul_closedBall_zero (a : (v.adicCompletion F)ˣ) (r : ℝ) :
    a • Metric.closedBall (0 : v.adicCompletion F) r =
      Metric.closedBall 0 (‖(a : v.adicCompletion F)‖ * r) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem, mem_closedBall_zero_iff, mem_closedBall_zero_iff,
    Units.smul_def, smul_eq_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv]
  have ha : 0 < ‖(a : v.adicCompletion F)‖ := norm_pos_iff.mpr a.ne_zero
  rw [inv_mul_le_iff₀ ha]

noncomputable abbrev δ : (v.adicCompletion F)ˣ →* ℝ≥0 := distribHaarChar (v.adicCompletion F)

lemma ν_closedBall_ne_zero : ν v (Metric.closedBall 0 1) ≠ 0 :=
  ((IsUltrametricDist.isOpen_closedBall (0 : v.adicCompletion F) one_ne_zero).measure_pos
    _ ⟨0, Metric.mem_closedBall_self zero_le_one⟩).ne'

lemma ν_closedBall_ne_top (x : v.adicCompletion F) (r : ℝ) : ν v (Metric.closedBall x r) ≠ ∞ :=
  (isCompact_closedBall v x r).measure_lt_top.ne

lemma δ_of_norm_one (u : (v.adicCompletion F)ˣ) (hu : ‖(u : v.adicCompletion F)‖ = 1) :
    δ v u = 1 := by
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := ν v) (ν_closedBall_ne_zero v)
    (ν_closedBall_ne_top v 0 1)
  rw [smul_closedBall_zero, hu, one_mul]; simp

lemma δ_unif (π : (v.adicCompletion F)ˣ) (hπ : ‖(π : v.adicCompletion F)‖ = (qr v)⁻¹) :
    δ v π = ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹ := by
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := ν v) (ν_closedBall_ne_zero v)
    (ν_closedBall_ne_top v 0 1)
  rw [smul_closedBall_zero, hπ, mul_one]
  have hb : Metric.closedBall (0 : v.adicCompletion F) (qr v)⁻¹ = Metric.ball 0 1 := by
    ext x
    rw [mem_closedBall_zero_iff, mem_ball_zero_iff]
    constructor
    · intro h; exact h.trans_lt (inv_lt_one_of_one_lt₀ (one_lt_qr v))
    · exact norm_le_inv_of_lt_one v x
  rw [hb, index_eq, ← mul_assoc]
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ 0 := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0)
  rw [ENNReal.coe_inv (by exact_mod_cast hq0), ENNReal.coe_natCast,
    ENNReal.inv_mul_cancel hq0 (ENNReal.natCast_ne_top _), one_mul]

lemma δ_eq (a : (v.adicCompletion F)ˣ) : δ v a = ‖(a : v.adicCompletion F)‖₊ := by
  obtain ⟨π, hπ⟩ := exists_unif v
  obtain ⟨k, hk⟩ := norm_cases v (a : v.adicCompletion F) a.ne_zero
  have hu : ‖((a * π ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ = 1 := by
    rw [Units.val_mul, norm_mul, Units.val_zpow_eq_zpow_val, norm_zpow, hπ, hk, inv_zpow,
      mul_inv_cancel₀ (zpow_pos (qr_pos v) k).ne']
  have hsplit : a = (a * π ^ k) * π ^ (-k) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hsplit, map_mul, map_zpow, δ_of_norm_one v _ hu, δ_unif v π hπ, one_mul, ← hsplit]
  apply NNReal.eq
  rw [coe_nnnorm, hk]
  push_cast
  rw [inv_zpow, zpow_neg, inv_inv]

lemma ν_smul (a : (v.adicCompletion F)ˣ) (E : Set (v.adicCompletion F)) :
    ν v (a • E) = (‖(a : v.adicCompletion F)‖₊ : ℝ≥0∞) * ν v E := by
  rw [← distribHaarChar_mul (ν v) a E, δ_eq]


/-! ### Change of variables `y = a z` -/

lemma map_mul_left (a : (v.adicCompletion F)ˣ) :
    Measure.map (fun z => (a : v.adicCompletion F) * z) (ν v) =
      (((‖(a : v.adicCompletion F)‖₊)⁻¹ : ℝ≥0) : ℝ≥0∞) • ν v := by
  ext E hE
  rw [Measure.map_apply (measurable_const_mul _) hE, Measure.smul_apply, smul_eq_mul]
  have hpre : (fun z => (a : v.adicCompletion F) * z) ⁻¹' E = a⁻¹ • E := by
    ext z
    rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def, smul_eq_mul]
  rw [hpre, ν_smul, Units.val_inv_eq_inv_val, nnnorm_inv]

lemma mulLeft_measurableEmbedding (a : (v.adicCompletion F)ˣ) :
    MeasurableEmbedding (fun z => (a : v.adicCompletion F) * z) :=
  (Homeomorph.mulLeft₀ (a : v.adicCompletion F) a.ne_zero).isClosedEmbedding.measurableEmbedding

lemma cov (a : (v.adicCompletion F)ˣ) (E : Set (v.adicCompletion F)) (φ : v.adicCompletion F → ℂ) :
    ∫ z in (fun z => (a : v.adicCompletion F) * z) ⁻¹' E, φ ((a : v.adicCompletion F) * z) ∂(ν v) =
      ((‖(a : v.adicCompletion F)‖⁻¹ : ℝ) : ℂ) * ∫ y in E, φ y ∂(ν v) := by
  rw [← (mulLeft_measurableEmbedding v a).setIntegral_map, map_mul_left, Measure.restrict_smul,
    integral_smul_measure, ENNReal.coe_toReal, NNReal.coe_inv, coe_nnnorm, Complex.real_smul]

/-! ### Transfer from `F_vˣ` to `F_v` -/

lemma val_measurableEmbedding :
    MeasurableEmbedding (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) := by
  have hr : Set.range (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) = {0}ᶜ := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩; exact u.ne_zero
    · intro hy; exact ⟨Units.mk0 y hy, rfl⟩
  have he : Topology.IsOpenEmbedding (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) :=
    ⟨Units.isEmbedding_val₀, by rw [hr]; exact isOpen_compl_singleton⟩
  exact he.measurableEmbedding

noncomputable abbrev Cq : ℝ≥0∞ :=
  (Ideal.absNorm v.asIdeal : ℝ≥0∞) / ((Ideal.absNorm v.asIdeal : ℝ≥0∞) - 1)

lemma Cq_ne_top : Cq v ≠ ∞ := by
  apply ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
  have := NumberField.HeightOneSpectrum.one_lt_absNorm v
  intro h
  rw [tsub_eq_zero_iff_le] at h
  exact absurd (by exact_mod_cast h : Ideal.absNorm v.asIdeal ≤ 1) (by omega)

lemma Cq_ne_zero : Cq v ≠ 0 := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm v
  apply ENNReal.div_ne_zero.mpr
  refine ⟨by exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0), ?_⟩
  exact ENNReal.sub_ne_top (ENNReal.natCast_ne_top _)

lemma measurable_nnnorm_inv :
    Measurable (fun y : v.adicCompletion F => (‖y‖₊⁻¹ : ℝ≥0)) :=
  measurable_nnnorm.inv

lemma transfer (g : (v.adicCompletion F)ˣ → ℂ) (G : v.adicCompletion F → ℂ)
    (hG : ∀ x : (v.adicCompletion F)ˣ, G x = g x) :
    (Integrable (fun y => ((‖y‖⁻¹ : ℝ) : ℂ) * G y) (ν v) →
      Integrable g (finiteLocalMulTamagawa F v)) ∧
    ∫ x, g x ∂(finiteLocalMulTamagawa F v) =
      ((Cq v).toReal : ℂ) * ∫ y, ((‖y‖⁻¹ : ℝ) : ℂ) * G y ∂(ν v) := by
  have he := val_measurableEmbedding v
  set w' : v.adicCompletion F → ℝ≥0 := fun y => ‖y‖₊⁻¹ with hw'
  have hcomap : ((ν v).withDensity (fun x => (‖x‖₊ : ℝ≥0∞)⁻¹)).comap Units.val =
      ((ν v).withDensity (fun x => (w' x : ℝ≥0∞))).comap Units.val := by
    ext A hA
    rw [he.comap_apply, he.comap_apply, withDensity_apply _ (he.measurableSet_image.mpr hA),
      withDensity_apply _ (he.measurableSet_image.mpr hA)]
    apply setLIntegral_congr_fun (he.measurableSet_image.mpr hA)
    rintro _ ⟨u, -, rfl⟩
    simp only [hw']
    rw [ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr u.ne_zero)]
  have hmap : Measure.map Units.val (((ν v).withDensity (fun x => (w' x : ℝ≥0∞))).comap
      Units.val) = (ν v).withDensity (fun x => (w' x : ℝ≥0∞)) := by
    rw [he.map_comap]
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    have h0 : {a : v.adicCompletion F | a ∉ Set.range Units.val} ⊆ {0} := by
      intro y hy
      by_contra h
      exact hy ⟨Units.mk0 y h, rfl⟩
    apply measure_mono_null h0
    rw [withDensity_apply _ (measurableSet_singleton 0)]
    rw [setLIntegral_congr_fun (measurableSet_singleton 0) (g := fun _ => 0)]
    · simp
    · intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy; simp [hw']
  have hsmul : (fun y => w' y • G y) = (fun y => ((‖y‖⁻¹ : ℝ) : ℂ) * G y) := by
    funext y
    rw [NNReal.smul_def, hw', NNReal.coe_inv, coe_nnnorm, Complex.real_smul]
  have hgG : G ∘ Units.val = g := funext hG
  constructor
  · intro hint
    unfold finiteLocalMulTamagawa
    apply Integrable.smul_measure _ (Cq_ne_top v)
    rw [hcomap, ← hgG, ← he.integrable_map_iff, hmap,
      integrable_withDensity_iff_integrable_smul (measurable_nnnorm_inv v), hsmul]
    exact hint
  · unfold finiteLocalMulTamagawa
    rw [integral_smul_measure, hcomap, ← hgG]
    rw [show (∫ x, (G ∘ Units.val) x ∂(((ν v).withDensity (fun x => (w' x : ℝ≥0∞))).comap
      Units.val)) = ∫ y, G y ∂(Measure.map Units.val (((ν v).withDensity
        (fun x => (w' x : ℝ≥0∞))).comap Units.val)) from (he.integral_map G).symm]
    rw [hmap, integral_withDensity_eq_integral_smul (measurable_nnnorm_inv v), hsmul,
      Complex.real_smul]

open Classical in
lemma cont_single : Continuous (fun y : v.adicCompletion F =>
    (RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F)
      v y)) := by
  have hS : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ Filter.principal {v}ᶜ := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]
    exact Set.finite_singleton v
  let g : v.adicCompletion F → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) =>
      w.adicCompletion F) (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      (Filter.principal {v}ᶜ) := fun y => ⟨Pi.mulSingle v y, by
        rw [Filter.eventually_principal]
        intro w hw
        rw [Set.mem_compl_singleton_iff] at hw
        rw [Pi.mulSingle_eq_of_ne hw]
        exact one_mem _⟩
  have hg : Continuous g := by
    rw [RestrictedProduct.continuous_rng_of_principal_iff_forall]
    intro w
    by_cases h : w = v
    · subst h
      simp only [g]
      have : (fun x : w.adicCompletion F => (Pi.mulSingle w x : (i : HeightOneSpectrum (𝓞 F)) →
          i.adicCompletion F) w) = id := by
        funext x; exact Pi.mulSingle_eq_same w x
      exact (congrArg Continuous this).mpr continuous_id
    · have : (fun x : v.adicCompletion F => (Pi.mulSingle v x : (i : HeightOneSpectrum (𝓞 F)) →
          i.adicCompletion F) w) = fun _ => 1 := by
        funext x; exact Pi.mulSingle_eq_of_ne h x
      exact (congrArg Continuous this).mpr continuous_const
  exact (RestrictedProduct.continuous_inclusion hS).comp hg

open Classical in
lemma val_finiteIdeleSingle (x : (v.adicCompletion F)ˣ) :
    ((finiteIdeleSingle v x : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) =
      RestrictedProduct.mulSingle
        (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v
          (x : v.adicCompletion F) := by
  apply RestrictedProduct.ext
  intro w
  by_cases h : w = v
  · subst h
    change (((Pi.mulSingle w x : (i : HeightOneSpectrum (𝓞 F)) → (i.adicCompletion F)ˣ) w :
      (w.adicCompletion F)ˣ) : w.adicCompletion F) = _
    rw [Pi.mulSingle_eq_same]
    exact (Pi.mulSingle_eq_same w (x : w.adicCompletion F)).symm
  · change (((Pi.mulSingle v x : (i : HeightOneSpectrum (𝓞 F)) → (i.adicCompletion F)ˣ) w :
      (w.adicCompletion F)ˣ) : w.adicCompletion F) = _
    rw [Pi.mulSingle_eq_of_ne h]
    exact (Pi.mulSingle_eq_of_ne h (x : v.adicCompletion F)).symm


lemma ideleSingle_mul (x y : (v.adicCompletion F)ˣ) :
    ideleSingle v (x * y) = ideleSingle v x * ideleSingle v y := by
  have h1 : finiteIdeleSingle v (x * y) = finiteIdeleSingle v x * finiteIdeleSingle v y := by
    unfold finiteIdeleSingle
    rw [RestrictedProduct.mulSingle_mul]
    exact map_mul _ _ _
  unfold ideleSingle
  rw [h1, show ((1 : (InfiniteAdeleRing F)ˣ), finiteIdeleSingle v x * finiteIdeleSingle v y)
    = (1, finiteIdeleSingle v x) * (1, finiteIdeleSingle v y) by simp]
  exact map_mul _ _ _

lemma ideleSingle_one : ideleSingle v (1 : (v.adicCompletion F)ˣ) = 1 := by
  have h1 : finiteIdeleSingle v 1 = 1 := by
    unfold finiteIdeleSingle
    rw [RestrictedProduct.mulSingle_one]
    exact map_one _
  unfold ideleSingle
  rw [h1, show ((1 : (InfiniteAdeleRing F)ˣ), (1 : (FiniteAdeleRing (𝓞 F) F)ˣ)) = 1 from rfl]
  exact map_one _

noncomputable def ideleSingleHom : (v.adicCompletion F)ˣ →* IdeleGroup F where
  toFun := ideleSingle v
  map_one' := ideleSingle_one v
  map_mul' := ideleSingle_mul v

noncomputable def lcHom (χ : HeckeCharacter F) : (v.adicCompletion F)ˣ →* Circle :=
  χ.toMonoidHom.comp ((QuotientGroup.mk' _).comp (ideleSingleHom v))

lemma lc_eq (χ : HeckeCharacter F) (x : (v.adicCompletion F)ˣ) :
    χ.localComponent v x = (lcHom v χ x : ℂ) := rfl

lemma lc_mul (χ : HeckeCharacter F) (x y : (v.adicCompletion F)ˣ) :
    χ.localComponent v (x * y) = χ.localComponent v x * χ.localComponent v y := by
  simp only [lc_eq, map_mul, Circle.coe_mul]

lemma lc_zpow (χ : HeckeCharacter F) (x : (v.adicCompletion F)ˣ) (k : ℤ) :
    χ.localComponent v (x ^ k) = χ.localComponent v x ^ k := by
  simp only [lc_eq, map_zpow, Circle.coe_zpow]

lemma lc_one (χ : HeckeCharacter F) : χ.localComponent v 1 = 1 := by
  simp only [lc_eq, map_one, Circle.coe_one]

lemma lc_norm (χ : HeckeCharacter F) (x : (v.adicCompletion F)ˣ) :
    ‖χ.localComponent v x‖ = 1 := by
  rw [lc_eq]; exact Circle.norm_coe _

lemma cont_ideleSingle : Continuous (ideleSingle v : (v.adicCompletion F)ˣ → IdeleGroup F) := by
  classical
  have h1 : Continuous (fun x : (v.adicCompletion F)ˣ =>
      ((ideleSingle v x : IdeleGroup F) : AdeleRing (𝓞 F) F)) := by
    have : (fun x : (v.adicCompletion F)ˣ =>
        ((ideleSingle v x : IdeleGroup F) : AdeleRing (𝓞 F) F)) =
        fun x => ((1 : InfiniteAdeleRing F), ((finiteIdeleSingle v x : (FiniteAdeleRing (𝓞 F) F)ˣ) :
          FiniteAdeleRing (𝓞 F) F)) := rfl
    rw [this]
    simp_rw [val_finiteIdeleSingle]
    exact continuous_const.prodMk ((cont_single v).comp Units.continuous_val)
  rw [Units.continuous_iff]
  refine ⟨h1, ?_⟩
  have : (fun x : (v.adicCompletion F)ˣ => (((ideleSingle v x)⁻¹ : IdeleGroup F) :
      AdeleRing (𝓞 F) F)) = (fun x => ((ideleSingle v x : IdeleGroup F) : AdeleRing (𝓞 F) F)) ∘
        (fun x => x⁻¹) := by
    funext x
    simp only [Function.comp_apply]
    rw [show ideleSingle v x⁻¹ = (ideleSingle v x)⁻¹ from map_inv (ideleSingleHom v) x]
  rw [this]
  exact h1.comp continuous_inv

lemma cont_lc (χ : HeckeCharacter F) : Continuous (χ.localComponent v) := by
  unfold HeckeCharacter.localComponent
  exact continuous_subtype_val.comp (χ.continuous.comp
    (QuotientGroup.continuous_mk.comp (cont_ideleSingle v)))


/-! ### Extension of `χ_v` by zero -/

section Chi

variable (χ : HeckeCharacter F)

noncomputable def χt : v.adicCompletion F → ℂ :=
  Function.extend (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) (χ.localComponent v) 0

lemma χt_val (x : (v.adicCompletion F)ˣ) : χt v χ x = χ.localComponent v x :=
  Units.val_injective.extend_apply _ _ _

lemma χt_zero : χt v χ 0 = 0 := by
  unfold χt
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨u, hu⟩; exact u.ne_zero hu

lemma χt_mk0 (y : v.adicCompletion F) (hy : y ≠ 0) :
    χt v χ y = χ.localComponent v (Units.mk0 y hy) := by
  rw [← χt_val]; rfl

lemma measurable_χt : Measurable (χt v χ) :=
  (val_measurableEmbedding v).measurable_extend (cont_lc v χ).measurable measurable_const

lemma norm_χt_le (y : v.adicCompletion F) : ‖χt v χ y‖ ≤ 1 := by
  by_cases hy : y = 0
  · rw [hy, χt_zero]; simp
  · rw [χt_mk0 v χ y hy, lc_norm]

lemma χt_mul (a : (v.adicCompletion F)ˣ) (z : v.adicCompletion F) :
    χt v χ ((a : v.adicCompletion F) * z) = χ.localComponent v a * χt v χ z := by
  by_cases hz : z = 0
  · rw [hz, mul_zero, χt_zero, mul_zero]
  · have : (a : v.adicCompletion F) * z =
        ((a * Units.mk0 z hz : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by simp
    rw [this, χt_val, lc_mul, χt_mk0 v χ z hz]

end Chi

/-! ### Shells -/

def S (n : ℤ) : Set (v.adicCompletion F) := {y | ‖y‖ = qr v ^ (-n)}

lemma measurableSet_S (n : ℤ) : MeasurableSet (S v n) :=
  (isClosed_eq continuous_norm continuous_const).measurableSet

lemma ne_zero_of_mem_S {n : ℤ} {y : v.adicCompletion F} (hy : y ∈ S v n) : y ≠ 0 := by
  intro h
  rw [S, Set.mem_ofPred_eq, h, norm_zero] at hy
  exact (zpow_pos (qr_pos v) (-n)).ne' hy.symm

lemma iUnion_S : ⋃ n, S v n = {0}ᶜ := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_compl_singleton_iff]
  constructor
  · rintro ⟨n, hn⟩; exact ne_zero_of_mem_S v hn
  · intro hy
    obtain ⟨k, hk⟩ := norm_cases v y hy
    exact ⟨-k, by simp [S, hk]⟩

lemma zpow_inj {m n : ℤ} (h : qr v ^ m = qr v ^ n) : m = n :=
  zpow_right_injective₀ (qr_pos v) (one_lt_qr v).ne' h

lemma S_disjoint : Pairwise (Function.onFun Disjoint (S v)) := by
  intro m n hmn
  rw [Function.onFun, Set.disjoint_left]
  intro y hm hn
  apply hmn
  have := zpow_inj v (hm.symm.trans hn)
  omega

lemma S_subset (n : ℤ) : S v n ⊆ Metric.closedBall 0 (qr v ^ (-n)) := by
  intro y hy; rw [mem_closedBall_zero_iff]; exact hy.le

lemma ν_closedBall_zpow (n : ℤ) : ν v (Metric.closedBall 0 (qr v ^ (-n))) =
    ENNReal.ofReal (qr v ^ (-n)) * ν v (Metric.closedBall 0 1) := by
  obtain ⟨π, hπ⟩ := exists_unif v
  have h1 : Metric.closedBall (0 : v.adicCompletion F) (qr v ^ (-n)) =
      (π ^ n) • Metric.closedBall 0 1 := by
    rw [smul_closedBall_zero, mul_one, Units.val_zpow_eq_zpow_val, norm_zpow, hπ, inv_zpow,
      zpow_neg]
  rw [h1, ν_smul]
  congr 1
  rw [Units.val_zpow_eq_zpow_val, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm, norm_zpow, hπ,
    inv_zpow, zpow_neg]

lemma ν_S_lt_top (n : ℤ) : ν v (S v n) < ∞ :=
  (measure_mono (S_subset v n)).trans_lt (isCompact_closedBall v 0 _).measure_lt_top

lemma ν_S_real_le (n : ℤ) :
    (ν v).real (S v n) ≤ qr v ^ (-n) * (ν v).real (Metric.closedBall 0 1) := by
  have h := measure_mono (μ := ν v) (S_subset v n)
  rw [ν_closedBall_zpow] at h
  rw [Measure.real, Measure.real]
  calc (ν v (S v n)).toReal
      ≤ (ENNReal.ofReal (qr v ^ (-n)) * ν v (Metric.closedBall 0 1)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ν_closedBall_ne_top v 0 1)) h
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (zpow_pos (qr_pos v) _).le]

lemma zpow_split (n k : ℤ) : qr v ^ (-(n + k)) = qr v ^ (-k) * qr v ^ (-n) := by
  rw [← zpow_add₀ (qr_pos v).ne']; ring_nf

lemma preimage_S (a : (v.adicCompletion F)ˣ) (k : ℤ) (ha : ‖(a : v.adicCompletion F)‖ = qr v ^ (-k))
    (n : ℤ) : (fun z => (a : v.adicCompletion F) * z) ⁻¹' S v (n + k) = S v n := by
  ext z
  simp only [S, Set.mem_preimage, Set.mem_ofPred_eq, norm_mul, ha, zpow_split]
  exact mul_right_inj' (zpow_pos (qr_pos v) _).ne'

/-! ### `q^{-s}` -/

noncomputable abbrev Xs (s : ℂ) : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)

lemma cpow_shell (n : ℤ) (s : ℂ) : (((qr v ^ (-n) : ℝ)) : ℂ) ^ s = Xs v s ^ n := by
  have hq0 : ((qr v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (qr_pos v).ne'
  have hqC : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = ((qr v : ℝ) : ℂ) := by simp [qr]
  rw [Xs, hqC, Complex.cpow_def_of_ne_zero (by exact_mod_cast (zpow_pos (qr_pos v) (-n)).ne'),
    Complex.cpow_def_of_ne_zero hq0, ← Complex.exp_int_mul,
    ← Complex.ofReal_log (zpow_pos (qr_pos v) (-n)).le, Real.log_zpow,
    ← Complex.ofReal_log (qr_pos v).le]
  congr 1
  push_cast; ring

lemma norm_Xs (s : ℂ) : ‖Xs v s‖ = qr v ^ (-s.re) := by
  rw [Xs, Complex.norm_natCast_cpow_of_pos]
  · simp [qr]
  · have := NumberField.HeightOneSpectrum.one_lt_absNorm v; omega

lemma norm_Xs_lt_one (s : ℂ) (hs : 0 < s.re) : ‖Xs v s‖ < 1 := by
  rw [norm_Xs]
  exact Real.rpow_lt_one_of_one_lt_of_neg (one_lt_qr v) (by linarith)

lemma Xs_ne_zero (s : ℂ) : Xs v s ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_Xs]
  exact (Real.rpow_pos_of_pos (qr_pos v) _).ne'

/-! ### Shell integrals -/

section Shell

variable (χ : HeckeCharacter F)

noncomputable def J (f : v.adicCompletion F → ℂ) (n : ℤ) : ℂ :=
  ∫ y in S v n, ((‖y‖⁻¹ : ℝ) : ℂ) * f y * χt v χ y ∂(ν v)

lemma integrableOn_S (f : v.adicCompletion F → ℂ) (hfm : Measurable f) (B : ℝ)
    (hB : ∀ y, ‖f y‖ ≤ B) (n : ℤ) :
    IntegrableOn (fun y => ((‖y‖⁻¹ : ℝ) : ℂ) * f y * χt v χ y) (S v n) (ν v) := by
  refine Measure.integrableOn_of_bounded (M := qr v ^ n * B) (ν_S_lt_top v n).ne ?_ ?_
  · exact (((Complex.measurable_ofReal.comp measurable_norm.inv).mul hfm).mul
      (measurable_χt v χ)).aestronglyMeasurable
  · rw [ae_restrict_iff' (measurableSet_S v n)]
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    have hy' : ‖y‖ = qr v ^ (-n) := hy
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, hy',
      zpow_neg, inv_inv]
    have hq : 0 ≤ qr v ^ n := (zpow_pos (qr_pos v) n).le
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB y)
    calc qr v ^ n * ‖f y‖ * ‖χt v χ y‖ ≤ qr v ^ n * B * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hB y) hq) (norm_χt_le v χ y) (norm_nonneg _)
            (mul_nonneg hq hB0)
      _ = qr v ^ n * B := mul_one _

lemma gen (f : v.adicCompletion F → ℂ) (hfm : Measurable f) (B : ℝ) (hB : ∀ y, ‖f y‖ ≤ B)
    (M : ℤ) (hM : ∀ y, qr v ^ M < ‖y‖ → f y = 0) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun y => ((‖y‖⁻¹ : ℝ) : ℂ) * (f y * χt v χ y * ((‖y‖ : ℝ) : ℂ) ^ s)) (ν v) ∧
    HasSum (fun n : ℤ => Xs v s ^ n * J v χ f n)
      (∫ y, ((‖y‖⁻¹ : ℝ) : ℂ) * (f y * χt v χ y * ((‖y‖ : ℝ) : ℂ) ^ s) ∂(ν v)) := by
  set H := fun y : v.adicCompletion F =>
    ((‖y‖⁻¹ : ℝ) : ℂ) * (f y * χt v χ y * ((‖y‖ : ℝ) : ℂ) ^ s) with hH
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hH0 : ∀ y ∉ ({0}ᶜ : Set (v.adicCompletion F)), H y = 0 := by
    intro y hy
    rw [Set.mem_compl_singleton_iff, not_not] at hy
    simp [hH, hy]
  have hHS : ∀ n : ℤ, ∀ y ∈ S v n,
      H y = Xs v s ^ n * (((‖y‖⁻¹ : ℝ) : ℂ) * f y * χt v χ y) := by
    intro n y hy
    have hy' : ((‖y‖ : ℝ) : ℂ) ^ s = Xs v s ^ n := by
      rw [show ‖y‖ = qr v ^ (-n) from hy]; exact cpow_shell v n s
    simp only [hH]
    rw [hy']; ring
  have hint : ∀ n, IntegrableOn H (S v n) (ν v) := by
    intro n
    have := (integrableOn_S v χ f hfm B hB n).const_mul (Xs v s ^ n)
    exact IntegrableOn.congr_fun this (fun y hy => (hHS n y hy).symm) (measurableSet_S v n)
  set r := ‖Xs v s‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r < 1 := norm_Xs_lt_one v s hs
  set C := B * (ν v).real (Metric.closedBall 0 1) with hC
  have hbound : ∀ n : ℤ, ∫ y in S v n, ‖H y‖ ∂(ν v) ≤ C * r ^ n := by
    intro n
    have hle : ∀ y ∈ S v n, ‖‖H y‖‖ ≤ r ^ n * qr v ^ n * B := by
      intro y hy
      rw [norm_norm, hHS n y hy]
      have hy' : ‖y‖ = qr v ^ (-n) := hy
      rw [norm_mul, norm_mul, norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_inv,
        abs_norm, hy', zpow_neg, inv_inv, ← hr]
      have hq : 0 ≤ qr v ^ n := (zpow_pos (qr_pos v) n).le
      calc r ^ n * (qr v ^ n * ‖f y‖ * ‖χt v χ y‖) ≤ r ^ n * (qr v ^ n * B * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left (hB y) hq)
              (norm_χt_le v χ y) (norm_nonneg _) (mul_nonneg hq hB0)) (zpow_nonneg hr0 n)
        _ = r ^ n * qr v ^ n * B := by ring
    have h1 := norm_setIntegral_le_of_norm_le_const (ν_S_lt_top v n) hle
    have h2 := ν_S_real_le v n
    calc ∫ y in S v n, ‖H y‖ ∂(ν v) ≤ ‖∫ y in S v n, ‖H y‖ ∂(ν v)‖ := Real.le_norm_self _
      _ ≤ r ^ n * qr v ^ n * B * (ν v).real (S v n) := h1
      _ ≤ r ^ n * qr v ^ n * B * (qr v ^ (-n) * (ν v).real (Metric.closedBall 0 1)) := by
          have : 0 ≤ r ^ n := zpow_nonneg hr0 n
          have : 0 ≤ qr v ^ n := (zpow_pos (qr_pos v) n).le
          gcongr
      _ = C * r ^ n := by
          have hq : qr v ^ n ≠ 0 := (zpow_pos (qr_pos v) n).ne'
          rw [hC, zpow_neg]
          field_simp
  have hzero : ∀ n : ℤ, n < -M → ∫ y in S v n, ‖H y‖ ∂(ν v) = 0 := by
    intro n hn
    rw [setIntegral_congr_fun (measurableSet_S v n) (g := fun _ => (0 : ℝ))]
    · simp
    · intro y hy
      have hy' : ‖y‖ = qr v ^ (-n) := hy
      have hfy : f y = 0 := hM y (by
        rw [hy']; exact zpow_lt_zpow_right₀ (one_lt_qr v) (by omega))
      simp [hH, hfy]
  have hsum : Summable (fun n : ℤ => ∫ y in S v n, ‖H y‖ ∂(ν v)) := by
    rw [summable_int_iff_summable_nat_and_neg]
    constructor
    · refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun y => norm_nonneg _))
        (fun n => ?_) ((summable_geometric_of_lt_one hr0 hr1).mul_left C)
      have := hbound n
      rwa [zpow_natCast] at this
    · apply summable_of_ne_finset_zero (s := Finset.range (M.toNat + 1))
      intro n hn
      rw [Finset.mem_range, not_lt] at hn
      exact hzero _ (by omega)
  have hU : IntegrableOn H (⋃ n, S v n) (ν v) :=
    integrableOn_iUnion_of_summable_integral_norm hint hsum
  rw [iUnion_S] at hU
  have hInt : Integrable H (ν v) := by
    refine (integrableOn_iff_integrable_of_support_subset ?_).mp hU
    intro y hy
    by_contra h
    exact hy (hH0 y h)
  refine ⟨hInt, ?_⟩
  have hS := hasSum_integral_iUnion (measurableSet_S v) (S_disjoint v)
    (by rw [iUnion_S]; exact hU)
  rw [iUnion_S, setIntegral_eq_integral_of_forall_compl_eq_zero hH0] at hS
  have heq : (fun n => ∫ x in S v n, H x ∂(ν v)) = fun n => Xs v s ^ n * J v χ f n := by
    funext n
    rw [setIntegral_congr_fun (measurableSet_S v n) (fun y hy => hHS n y hy), integral_const_mul]
    rfl
  rw [heq] at hS
  exact hS

end Shell


/-! ### The recursion for `J 1` -/

lemma exists_isUnif : ∃ π : (v.adicCompletion F)ˣ, IsUniformizerAt v π := by
  obtain ⟨x, hx⟩ := v.valuedAdicCompletion_surjective F (WithZero.exp (-1 : ℤ))
  have hx0 : x ≠ 0 := by
    intro h; rw [h, map_zero] at hx; exact WithZero.zero_ne_coe hx
  exact ⟨Units.mk0 x hx0, hx⟩

section Rec

variable (χ : HeckeCharacter F)

lemma J_one_mul (a : (v.adicCompletion F)ˣ) (k : ℤ) (ha : ‖(a : v.adicCompletion F)‖ = qr v ^ (-k))
    (n : ℤ) : J v χ (fun _ => 1) (n + k) = χ.localComponent v a * J v χ (fun _ => 1) n := by
  have h := cov v a (S v (n + k)) (fun y => ((‖y‖⁻¹ : ℝ) : ℂ) * 1 * χt v χ y)
  rw [preimage_S v a k ha n] at h
  have hc : ∀ z ∈ S v n, ((‖(a : v.adicCompletion F) * z‖⁻¹ : ℝ) : ℂ) * 1 *
      χt v χ ((a : v.adicCompletion F) * z) =
      ((qr v ^ k : ℝ) : ℂ) * χ.localComponent v a * (((‖z‖⁻¹ : ℝ) : ℂ) * 1 * χt v χ z) := by
    intro z hz
    rw [χt_mul, norm_mul, ha, mul_inv, zpow_neg, inv_inv]
    push_cast; ring
  rw [setIntegral_congr_fun (measurableSet_S v n) hc, integral_const_mul] at h
  unfold J
  have hq : ((qr v ^ k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (zpow_pos (qr_pos v) k).ne'
  rw [ha, zpow_neg, inv_inv] at h
  apply mul_left_cancel₀ hq
  rw [← h]; ring

lemma primeValue_of_unram (hun : χ.IsUnramifiedAt v) :
    ∃ π : (v.adicCompletion F)ˣ, IsUniformizerAt v π ∧ χ.primeValue v = χ.localComponent v π := by
  obtain ⟨π0, hπ0⟩ := exists_isUnif v
  have hex : χ.IsUnramifiedAt v ∧ ∃ x : (v.adicCompletion F)ˣ, IsUniformizerAt v x :=
    ⟨hun, π0, hπ0⟩
  refine ⟨hex.2.choose, hex.2.choose_spec, ?_⟩
  unfold HeckeCharacter.primeValue; rw [dif_pos hex]

lemma primeValue_of_ram (hun : ¬ χ.IsUnramifiedAt v) : χ.primeValue v = 0 := by
  unfold HeckeCharacter.primeValue; rw [dif_neg (fun h => hun h.1)]

lemma norm_primeValue_le : ‖χ.primeValue v‖ ≤ 1 := by
  by_cases hun : χ.IsUnramifiedAt v
  · obtain ⟨π, -, hπ⟩ := primeValue_of_unram v χ hun
    rw [hπ, lc_norm]
  · rw [primeValue_of_ram v χ hun, norm_zero]; exact zero_le_one

lemma J_one_eq_zero_of_ram (hun : ¬ χ.IsUnramifiedAt v) (n : ℤ) : J v χ (fun _ => 1) n = 0 := by
  unfold HeckeCharacter.IsUnramifiedAt at hun
  push Not at hun
  obtain ⟨u, hu1, hu2⟩ := hun
  have hnu : ‖(u : v.adicCompletion F)‖ = qr v ^ (-(0 : ℤ)) := by
    rw [norm_eq_zpow v _ 0 (by rw [hu1]; rfl)]; simp
  have h := J_one_mul v χ u 0 hnu n
  rw [add_zero] at h
  have : (1 - χ.localComponent v u) * J v χ (fun _ => 1) n = 0 := by
    rw [sub_mul, ← h]; ring
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd (sub_eq_zero.mp h').symm hu2
  · exact h'

lemma J_one_rec (n : ℤ) :
    J v χ (fun _ => 1) (n + 1) = χ.primeValue v * J v χ (fun _ => 1) n := by
  by_cases hun : χ.IsUnramifiedAt v
  · obtain ⟨π, hπ, hpv⟩ := primeValue_of_unram v χ hun
    have hnπ : ‖(π : v.adicCompletion F)‖ = qr v ^ (-(1 : ℤ)) := norm_eq_zpow v _ (-1) hπ
    rw [hpv]
    exact J_one_mul v χ π 1 hnπ n
  · rw [J_one_eq_zero_of_ram v χ hun, J_one_eq_zero_of_ram v χ hun, mul_zero]

end Rec

/-! ### Algebra -/

lemma alg (J : ℤ → ℂ) (a X Z : ℂ) (hX : X ≠ 0) (hZ : HasSum (fun n => X ^ n * J n) Z)
    (T : Finset ℤ) (hT : ∀ n ∉ T, J n - a * J (n - 1) = 0) :
    Z * (1 - a * X) = ∑ n ∈ T, X ^ n * (J n - a * J (n - 1)) := by
  have h1 : HasSum (fun n : ℤ => X ^ n * (a * J (n - 1))) (a * X * Z) := by
    rw [← (Equiv.addRight (1 : ℤ)).hasSum_iff]
    have heq : ((fun n : ℤ => X ^ n * (a * J (n - 1))) ∘ (Equiv.addRight (1 : ℤ))) =
        fun n => a * X * (X ^ n * J n) := by
      funext n
      simp only [Function.comp_apply, Equiv.coe_addRight, add_sub_cancel_right, zpow_add_one₀ hX]
      ring
    rw [heq]
    exact hZ.mul_left (a * X)
  have h2 := hZ.sub h1
  have h3 : HasSum (fun n : ℤ => X ^ n * (J n - a * J (n - 1)))
      (∑ n ∈ T, X ^ n * (J n - a * J (n - 1))) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => by rw [hT n hn, mul_zero])
  have h4 : (fun n : ℤ => X ^ n * J n - X ^ n * (a * J (n - 1))) =
      (fun n : ℤ => X ^ n * (J n - a * J (n - 1))) := by
    funext n; ring
  rw [h4] at h2
  rw [h3.unique h2]; ring

/-! ### Schwartz–Bruhat functions -/

lemma sb_M (f : v.adicCompletion F → ℂ) (hfc : HasCompactSupport f) :
    ∃ M : ℤ, ∀ y, qr v ^ M < ‖y‖ → f y = 0 := by
  obtain ⟨R, hR⟩ := (show IsCompact (tsupport f) from hfc).isBounded.subset_closedBall 0
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt R (one_lt_qr v)
  refine ⟨n, fun y hy => image_eq_zero_of_notMem_tsupport (fun hmem => ?_)⟩
  have := hR hmem
  rw [mem_closedBall_zero_iff] at this
  rw [zpow_natCast] at hy
  linarith

lemma sb_N (f : v.adicCompletion F → ℂ) (hf : IsLocallyConstant f) :
    ∃ N : ℤ, ∀ y, ‖y‖ ≤ qr v ^ (-N) → f y = f 0 := by
  have ho := hf.isOpen_fiber (f 0)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ho 0 rfl
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ (one_lt_qr v))
  refine ⟨n, fun y hy => hball ?_⟩
  rw [mem_ball_zero_iff]
  calc ‖y‖ ≤ qr v ^ (-(n : ℤ)) := hy
    _ = (qr v)⁻¹ ^ n := by rw [zpow_neg, zpow_natCast, inv_pow]
    _ < ε := hn


/-! ### Additional facts for the converse -/

lemma val_isOpenEmbedding :
    Topology.IsOpenEmbedding (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) := by
  have hr : Set.range (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) = {0}ᶜ := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩; exact u.ne_zero
    · intro hy; exact ⟨Units.mk0 y hy, rfl⟩
  exact ⟨Units.isEmbedding_val₀, by rw [hr]; exact isOpen_compl_singleton⟩

lemma valued_eq_one_of_norm (y : v.adicCompletion F) (hy : ‖y‖ = 1) : Valued.v y = 1 :=
  le_antisymm ((Valued.toNormedField.norm_le_one_iff).mp hy.le)
    ((Valued.toNormedField.one_le_norm_iff).mp hy.ge)

lemma ν_S_pos (n : ℤ) : 0 < (ν v).real (S v n) := by
  obtain ⟨π, hπ⟩ := exists_unif v
  have hS : S v n = Metric.sphere 0 (qr v ^ (-n)) := by
    ext y; simp [S]
  have hpos : 0 < ν v (S v n) := by
    rw [hS]
    refine (IsUltrametricDist.isOpen_sphere (0 : v.adicCompletion F)
      (zpow_pos (qr_pos v) (-n)).ne').measure_pos (ν v) ⟨((π : v.adicCompletion F)) ^ n, ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_zpow, hπ, inv_zpow, zpow_neg]
  exact ENNReal.toReal_pos hpos.ne' (ν_S_lt_top v n).ne

section Conv

variable (χ : HeckeCharacter F)

lemma J_congr (f g : v.adicCompletion F → ℂ) (n : ℤ) (h : ∀ y ∈ S v n, f y = g y) :
    J v χ f n = J v χ g n := by
  unfold J
  apply setIntegral_congr_fun (measurableSet_S v n)
  intro y hy
  simp only [h y hy]

lemma J_eq_zero (f : v.adicCompletion F → ℂ) (n : ℤ) (h : ∀ y ∈ S v n, f y = 0) :
    J v χ f n = 0 := by
  rw [J_congr v χ f (fun _ => 0) n h]
  simp [J]

lemma J_sum (T : Finset ℤ) (c : ℤ → ℂ) (e : ℤ → v.adicCompletion F → ℂ)
    (he : ∀ m, Measurable (e m)) (hb : ∀ m y, ‖e m y‖ ≤ 1) (n : ℤ) :
    J v χ (fun y => ∑ m ∈ T, c m * e m y) n = ∑ m ∈ T, c m * J v χ (e m) n := by
  unfold J
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    ring
  · intro m _
    exact (integrableOn_S v χ (e m) (he m) 1 (hb m) n).const_mul (c m)

lemma J_one_zero_of_unram (hun : χ.IsUnramifiedAt v) :
    J v χ (fun _ => 1) 0 = (ν v).real (S v 0) := by
  have h : J v χ (fun _ => 1) 0 = ∫ y in S v 0, (1 : ℂ) ∂(ν v) := by
    unfold J
    apply setIntegral_congr_fun (measurableSet_S v 0)
    intro y hy
    have hy' : ‖y‖ = 1 := by rw [show ‖y‖ = qr v ^ (-(0 : ℤ)) from hy]; simp
    have hy0 : y ≠ 0 := ne_zero_of_mem_S v hy
    have hχ : χt v χ y = 1 := by
      rw [χt_mk0 v χ y hy0]
      exact hun _ (valued_eq_one_of_norm v y hy')
    simp [hy', hχ]
  rw [h, setIntegral_const, Complex.real_smul, mul_one]

lemma J_one_ne_zero_of_unram (hun : χ.IsUnramifiedAt v) (m : ℤ) :
    J v χ (fun _ => 1) m ≠ 0 := by
  obtain ⟨π, hπ⟩ := exists_unif v
  have hnorm : ‖((π ^ m : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ = qr v ^ (-m) := by
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, hπ, inv_zpow, zpow_neg]
  have h := J_one_mul v χ (π ^ m) m hnorm 0
  rw [zero_add] at h
  rw [h, J_one_zero_of_unram v χ hun]
  apply mul_ne_zero
  · intro h0; have := lc_norm v χ (π ^ m); rw [h0, norm_zero] at this; exact zero_ne_one this
  · exact_mod_cast (ν_S_pos v 0).ne'

lemma chi_near_one : ∃ δ > 0, ∀ y : v.adicCompletion F, ‖y - 1‖ < δ → ‖χt v χ y - 1‖ < 1 / 2 := by
  have hc : ContinuousAt (χt v χ) 1 := by
    have h1 : (χt v χ) ∘ Units.val = χ.localComponent v := funext (χt_val v χ)
    have h2 : ContinuousAt ((χt v χ) ∘ Units.val) (1 : (v.adicCompletion F)ˣ) := by
      rw [h1]; exact (cont_lc v χ).continuousAt
    rw [(val_isOpenEmbedding v).continuousAt_iff] at h2
    simpa using h2
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp hc (1 / 2) (by norm_num)
  have h1 : χt v χ 1 = 1 := by
    have := χt_val v χ 1
    rw [Units.val_one] at this
    rw [this, lc_one]
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have := h (by rwa [dist_eq_norm])
  rwa [dist_eq_norm, h1] at this

end Conv


section Basis

variable (χ : HeckeCharacter F)

lemma isLocallyConstant_indicator_closedBall (x : v.adicCompletion F) (r : ℝ) (hr : r ≠ 0) :
    IsLocallyConstant (Set.indicator (Metric.closedBall x r) (1 : v.adicCompletion F → ℂ)) := by
  have hU : IsClopen (Metric.closedBall x r) := IsUltrametricDist.isClopen_closedBall x hr
  rw [← LocallyConstant.coe_charFn ℂ hU]
  exact (LocallyConstant.charFn ℂ hU).isLocallyConstant

lemma norm_indicator_le (U : Set (v.adicCompletion F)) (y : v.adicCompletion F) :
    ‖Set.indicator U (1 : v.adicCompletion F → ℂ) y‖ ≤ 1 := by
  by_cases hy : y ∈ U
  · simp [Set.indicator_of_mem hy]
  · simp [Set.indicator_of_notMem hy]

lemma basis_unram (hun : χ.IsUnramifiedAt v) :
    ∃ e : ℤ → v.adicCompletion F → ℂ, (∀ m, IsLocallyConstant (e m)) ∧
    (∀ m y, ‖e m y‖ ≤ 1) ∧
    (∀ m y, qr v ^ (-m) < ‖y‖ → e m y = 0) ∧
    ∃ β : ℤ → ℂ, (∀ m, β m ≠ 0) ∧
      ∀ m n, J v χ (e m) n - χ.primeValue v * J v χ (e m) (n - 1) =
        if n = m then β m else 0 := by
  refine ⟨fun m => Set.indicator (Metric.closedBall 0 (qr v ^ (-m))) 1, ?_, ?_, ?_,
    fun m => J v χ (fun _ => 1) m, J_one_ne_zero_of_unram v χ hun, ?_⟩
  · intro m
    exact isLocallyConstant_indicator_closedBall v 0 _ (zpow_pos (qr_pos v) _).ne'
  · intro m y
    exact norm_indicator_le v _ y
  · intro m y hy
    apply Set.indicator_of_notMem
    rw [mem_closedBall_zero_iff, not_le]; exact hy
  · intro m n
    have hJ : ∀ k, J v χ (Set.indicator (Metric.closedBall 0 (qr v ^ (-m))) 1) k =
        if m ≤ k then J v χ (fun _ => 1) k else 0 := by
      intro k
      split_ifs with hk
      · apply J_congr
        intro y hy
        apply Set.indicator_of_mem
        rw [mem_closedBall_zero_iff, show ‖y‖ = qr v ^ (-k) from hy]
        exact zpow_le_zpow_right₀ (one_lt_qr v).le (by omega)
      · apply J_eq_zero
        intro y hy
        apply Set.indicator_of_notMem
        rw [mem_closedBall_zero_iff, not_le, show ‖y‖ = qr v ^ (-k) from hy]
        exact zpow_lt_zpow_right₀ (one_lt_qr v) (by omega)
    simp only []
    rw [hJ n, hJ (n - 1)]
    rcases lt_trichotomy n m with h | h | h
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; ring
    · subst h; rw [if_pos le_rfl, if_neg (by omega), if_pos rfl]; ring
    · rw [if_pos (by omega), if_pos (by omega), if_neg (by omega)]
      have := J_one_rec v χ (n - 1)
      rw [sub_add_cancel] at this
      rw [this]; ring

lemma basis_ram (hun : ¬ χ.IsUnramifiedAt v) :
    ∃ e : ℤ → v.adicCompletion F → ℂ, (∀ m, IsLocallyConstant (e m)) ∧
    (∀ m y, ‖e m y‖ ≤ 1) ∧
    (∀ m y, qr v ^ (-m) < ‖y‖ → e m y = 0) ∧
    ∃ β : ℤ → ℂ, (∀ m, β m ≠ 0) ∧
      ∀ m n, J v χ (e m) n - χ.primeValue v * J v χ (e m) (n - 1) =
        if n = m then β m else 0 := by
  obtain ⟨π, hπ⟩ := exists_unif v
  obtain ⟨δ, hδ, hnear⟩ := chi_near_one v χ
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ (inv_lt_one_of_one_lt₀ (one_lt_qr v))
  have hqi0 : 0 < (qr v)⁻¹ := inv_pos.mpr (qr_pos v)
  have hqi1 : (qr v)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_qr v)
  set ρ : ℝ := (qr v)⁻¹ ^ (k + 1) with hρ
  have hρ0 : 0 < ρ := pow_pos hqi0 _
  have hρ1 : ρ < 1 := pow_lt_one₀ hqi0.le hqi1 (by omega)
  have hρδ : ρ < δ := by
    calc ρ = (qr v)⁻¹ ^ k * (qr v)⁻¹ := pow_succ _ _
      _ ≤ (qr v)⁻¹ ^ k * 1 := by gcongr
      _ = (qr v)⁻¹ ^ k := mul_one _
      _ < δ := hk
  have hπm : ∀ m : ℤ, ‖((π : v.adicCompletion F)) ^ m‖ = qr v ^ (-m) := by
    intro m; rw [norm_zpow, hπ, inv_zpow, zpow_neg]
  set W : ℤ → Set (v.adicCompletion F) :=
    fun m => Metric.closedBall (((π : v.adicCompletion F)) ^ m) (qr v ^ (-m) * ρ) with hWdef
  have hWS : ∀ m, ∀ y ∈ W m, y ∈ S v m := by
    intro m y hy
    rw [hWdef, Metric.mem_closedBall, dist_eq_norm] at hy
    have h2 : ‖y - ((π : v.adicCompletion F)) ^ m‖ < ‖((π : v.adicCompletion F)) ^ m‖ := by
      rw [hπm]
      calc _ ≤ qr v ^ (-m) * ρ := hy
        _ < qr v ^ (-m) * 1 := by gcongr; exact zpow_pos (qr_pos v) _
        _ = qr v ^ (-m) := mul_one _
    have h3 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2.ne
    rw [sub_add_cancel, max_eq_right h2.le, hπm] at h3
    exact h3
  have hnearW : ∀ m, ∀ y ∈ W m,
      ‖χt v χ y - χ.localComponent v (π ^ m)‖ ≤ 1 / 2 := by
    intro m y hy
    rw [hWdef, Metric.mem_closedBall, dist_eq_norm] at hy
    set z : v.adicCompletion F := (((π ^ m)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y
      with hz
    have hyz : y = (((π ^ m) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * z := by
      rw [hz, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    have hz1 : ‖z - 1‖ < δ := by
      have : z - 1 = (((π ^ m)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
          (y - ((π : v.adicCompletion F)) ^ m) := by
        rw [hz, mul_sub, ← Units.val_zpow_eq_zpow_val, ← Units.val_mul, inv_mul_cancel,
          Units.val_one]
      rw [this, norm_mul, Units.val_inv_eq_inv_val, norm_inv, Units.val_zpow_eq_zpow_val, hπm,
        zpow_neg, inv_inv]
      calc qr v ^ m * ‖y - ((π : v.adicCompletion F)) ^ m‖ ≤ qr v ^ m * (qr v ^ (-m) * ρ) := by
            gcongr
        _ = ρ := by rw [← mul_assoc, ← zpow_add₀ (qr_pos v).ne', add_neg_cancel, zpow_zero,
            one_mul]
        _ < δ := hρδ
    have hc := hnear z hz1
    rw [hyz, χt_mul, show χ.localComponent v (π ^ m) * χt v χ z - χ.localComponent v (π ^ m) =
      χ.localComponent v (π ^ m) * (χt v χ z - 1) by ring, norm_mul, lc_norm, one_mul]
    exact hc.le
  have hWr : ∀ m : ℤ, qr v ^ (-m) * ρ ≠ 0 := fun m => (mul_pos (zpow_pos (qr_pos v) _) hρ0).ne'
  have hWmeas : ∀ m, MeasurableSet (W m) := fun m => Metric.isClosed_closedBall.measurableSet
  have hWfin : ∀ m, ν v (W m) < ∞ := fun m => (isCompact_closedBall v _ _).measure_lt_top
  have hWpos : ∀ m, 0 < (ν v).real (W m) := by
    intro m
    have : 0 < ν v (W m) :=
      (IsUltrametricDist.isOpen_closedBall _ (hWr m)).measure_pos (ν v)
        ⟨_, Metric.mem_closedBall_self (mul_pos (zpow_pos (qr_pos v) _) hρ0).le⟩
    exact ENNReal.toReal_pos this.ne' (hWfin m).ne
  have hpv := primeValue_of_ram v χ hun
  refine ⟨fun m => Set.indicator (W m) 1, ?_, ?_, ?_, fun m => J v χ (Set.indicator (W m) 1) m,
    ?_, ?_⟩
  · intro m
    exact isLocallyConstant_indicator_closedBall v _ _ (hWr m)
  · intro m y
    exact norm_indicator_le v _ y
  · intro m y hy
    apply Set.indicator_of_notMem
    intro hW
    have := hWS m y hW
    rw [show ‖y‖ = qr v ^ (-m) from this] at hy
    exact lt_irrefl _ hy
  · intro m
    have hJ : J v χ (Set.indicator (W m) 1) m =
        ((qr v ^ m : ℝ) : ℂ) * ∫ y in W m, χt v χ y ∂(ν v) := by
      have hSW : S v m ∩ W m = W m := Set.inter_eq_right.mpr (fun y hy => hWS m y hy)
      unfold J
      calc ∫ y in S v m, ((‖y‖⁻¹ : ℝ) : ℂ) * Set.indicator (W m) 1 y * χt v χ y ∂(ν v)
          = ∫ y in S v m, ((qr v ^ m : ℝ) : ℂ) * Set.indicator (W m) (χt v χ) y ∂(ν v) := by
            apply setIntegral_congr_fun (measurableSet_S v m)
            intro y hy
            have hy' : ‖y‖ = qr v ^ (-m) := hy
            by_cases hyW : y ∈ W m
            · simp only [Set.indicator_of_mem hyW, Pi.one_apply, hy', zpow_neg, inv_inv]; ring
            · simp only [Set.indicator_of_notMem hyW]; ring
        _ = ((qr v ^ m : ℝ) : ℂ) * ∫ y in S v m, Set.indicator (W m) (χt v χ) y ∂(ν v) :=
            integral_const_mul _ _
        _ = ((qr v ^ m : ℝ) : ℂ) * ∫ y in W m, χt v χ y ∂(ν v) := by
            rw [setIntegral_indicator (hWmeas m), hSW]
    show J v χ (Set.indicator (W m) 1) m ≠ 0
    rw [hJ]
    apply mul_ne_zero (by exact_mod_cast (zpow_pos (qr_pos v) m).ne')
    intro h0
    have hint : IntegrableOn (χt v χ) (W m) (ν v) :=
      Measure.integrableOn_of_bounded (M := 1) (hWfin m).ne
        (measurable_χt v χ).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun y => norm_χt_le v χ y))
    have hest : ‖∫ y in W m, χt v χ y ∂(ν v) - (ν v).real (W m) • χ.localComponent v (π ^ m)‖
        ≤ 1 / 2 * (ν v).real (W m) := by
      rw [← setIntegral_const, ← integral_sub hint (integrableOn_const (hWfin m).ne)]
      exact norm_setIntegral_le_of_norm_le_const (hWfin m) (fun y hy => hnearW m y hy)
    rw [h0, zero_sub, norm_neg, norm_smul, lc_norm, mul_one, Real.norm_of_nonneg (hWpos m).le]
      at hest
    linarith [hWpos m]
  · intro m n
    rw [hpv, zero_mul, sub_zero]
    split_ifs with h
    · rw [h]
    · apply J_eq_zero
      intro y hy
      apply Set.indicator_of_notMem
      intro hW
      have h1 := hWS m y hW
      exact h (zpow_inj v (show qr v ^ (-n) = qr v ^ (-m) from hy.symm.trans h1) |> neg_inj.mp)

lemma basis :
    ∃ e : ℤ → v.adicCompletion F → ℂ, (∀ m, IsLocallyConstant (e m)) ∧
    (∀ m y, ‖e m y‖ ≤ 1) ∧
    (∀ m y, qr v ^ (-m) < ‖y‖ → e m y = 0) ∧
    ∃ β : ℤ → ℂ, (∀ m, β m ≠ 0) ∧
      ∀ m n, J v χ (e m) n - χ.primeValue v * J v χ (e m) (n - 1) =
        if n = m then β m else 0 := by
  by_cases hun : χ.IsUnramifiedAt v
  · exact basis_unram v χ hun
  · exact basis_ram v χ hun

end Basis


lemma isLocallyConstant_sum (T : Finset ℤ) (g : ℤ → v.adicCompletion F → ℂ)
    (h : ∀ m, IsLocallyConstant (g m)) : IsLocallyConstant (fun y => ∑ m ∈ T, g m y) := by
  induction T using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact IsLocallyConstant.const _
  | insert i T hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i).add ih

end TateZ

theorem solution
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (c : ℤ →₀ ℂ) :
    ∃ f : v.adicCompletion F → ℂ, IsLocallyConstant f ∧ HasCompactSupport f ∧
      ∀ s : ℂ, 0 < s.re →
        ∫ x : (v.adicCompletion F)ˣ,
            f (x : v.adicCompletion F) * χ.localComponent v x *
              ((‖(x : v.adicCompletion F)‖ : ℝ) : ℂ) ^ s ∂(finiteLocalMulTamagawa F v) =
          (c.sum fun n a => a * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) ^ n) *
            (1 - χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
  obtain ⟨e, he_lc, he_b, he_v, β, hβ, hD⟩ := TateZ.basis v χ
  set a := χ.primeValue v with ha
  set Cr : ℂ := ((TateZ.Cq v).toReal : ℂ) with hCr
  have hCr0 : Cr ≠ 0 := by
    rw [hCr]
    exact_mod_cast (ENNReal.toReal_pos (TateZ.Cq_ne_zero v) (TateZ.Cq_ne_top v)).ne'
  set T := c.support with hTdef
  set lam : ℤ → ℂ := fun m => c m / (Cr * β m) with hlam
  set f : v.adicCompletion F → ℂ := fun y => ∑ m ∈ T, lam m * e m y with hf
  have hf_lc : IsLocallyConstant f :=
    TateZ.isLocallyConstant_sum v T (fun m y => lam m * e m y)
      (fun m => (he_lc m).comp (fun t => lam m * t))
  have hf_v : ∀ y, ∑ m ∈ T, TateZ.qr v ^ (-m) < ‖y‖ → f y = 0 := by
    intro y hy
    apply Finset.sum_eq_zero
    intro m hm
    rw [he_v m y (lt_of_le_of_lt (Finset.single_le_sum
      (fun i _ => (zpow_pos (TateZ.qr_pos v) (-i)).le) hm) hy), mul_zero]
  have hf_cs : HasCompactSupport f :=
    HasCompactSupport.intro' (TateZ.isCompact_closedBall v 0 (∑ m ∈ T, TateZ.qr v ^ (-m)))
      Metric.isClosed_closedBall
      (fun y hy => hf_v y (by rw [mem_closedBall_zero_iff, not_le] at hy; exact hy))
  have he_m : ∀ m, Measurable (e m) := fun m => (he_lc m).continuous.measurable
  have hJf : ∀ n, TateZ.J v χ f n = ∑ m ∈ T, lam m * TateZ.J v χ (e m) n :=
    fun n => TateZ.J_sum v χ T lam e he_m he_b n
  have hDf : ∀ n, Cr * (TateZ.J v χ f n - a * TateZ.J v χ f (n - 1)) = c n := by
    intro n
    rw [hJf, hJf, Finset.mul_sum, ← Finset.sum_sub_distrib]
    have h1 : ∀ m ∈ T, lam m * TateZ.J v χ (e m) n - a * (lam m * TateZ.J v χ (e m) (n - 1)) =
        if n = m then lam m * β m else 0 := by
      intro m _
      rw [← mul_zero (lam m), ← mul_ite, ← hD m n]; ring
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq]
    split_ifs with hn
    · rw [hlam]; field_simp [hβ n]
    · rw [mul_zero]; exact (Finsupp.notMem_support_iff.mp hn).symm
  refine ⟨f, hf_lc, hf_cs, fun s hs => ?_⟩
  obtain ⟨B, hB⟩ := hf_lc.continuous.bounded_above_of_compact_support hf_cs
  obtain ⟨M, hM⟩ := TateZ.sb_M v f hf_cs
  obtain ⟨-, hS⟩ := TateZ.gen v χ f hf_lc.continuous.measurable B hB M hM s hs
  obtain ⟨-, hT2⟩ := TateZ.transfer v
    (fun x : (v.adicCompletion F)ˣ => f (x : v.adicCompletion F) * χ.localComponent v x *
      ((‖(x : v.adicCompletion F)‖ : ℝ) : ℂ) ^ s)
    (fun y => f y * TateZ.χt v χ y * ((‖y‖ : ℝ) : ℂ) ^ s)
    (by intro x; simp only [TateZ.χt_val])
  rw [hT2]
  have hT : ∀ n ∉ T, TateZ.J v χ f n - a * TateZ.J v χ f (n - 1) = 0 := by
    intro n hn
    have := hDf n
    rw [Finsupp.notMem_support_iff.mp hn] at this
    exact (mul_eq_zero.mp this).resolve_left hCr0
  have halg := TateZ.alg (TateZ.J v χ f) a (TateZ.Xs v s) _ (TateZ.Xs_ne_zero v s) hS T hT
  have hne : 1 - a * TateZ.Xs v s ≠ 0 := by
    intro h
    have h1 : ‖a * TateZ.Xs v s‖ < 1 := by
      rw [norm_mul]
      calc ‖a‖ * ‖TateZ.Xs v s‖ ≤ 1 * ‖TateZ.Xs v s‖ :=
            mul_le_mul_of_nonneg_right (TateZ.norm_primeValue_le v χ) (norm_nonneg _)
        _ < 1 := by rw [one_mul]; exact TateZ.norm_Xs_lt_one v s hs
    rw [← sub_eq_zero.mp h, norm_one] at h1
    exact lt_irrefl _ h1
  rw [eq_mul_inv_iff_mul_eq₀ hne, mul_assoc]
  change _ * (_ * (1 - a * TateZ.Xs v s)) = _
  rw [halg, Finset.mul_sum, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [← hDf n]; ring
