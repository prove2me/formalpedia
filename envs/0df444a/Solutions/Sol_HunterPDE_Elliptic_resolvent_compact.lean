-- Prove2me | solution 1 for HunterPDE.Elliptic.resolvent_compact
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T11:51:53.205274+00:00
-- url     : https://prove2.me/submissions/4456c7e5-1f2e-42ab-88ab-45976463b26b

import Mathlib
import Definitions.Def_HunterPDE_Elliptic_EllipticOperator

set_option autoImplicit false

open MeasureTheory

namespace Rel6f

variable {n : ℕ}


/-- `(∫₀¹ g)² ≤ ∫₀¹ g²` for continuous `g`. -/
lemma sq_intervalIntegral_le (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ t in (0:ℝ)..1, g t) ^ 2 ≤ ∫ t in (0:ℝ)..1, g t ^ 2 := by
  set c := ∫ t in (0:ℝ)..1, g t with hc
  have h0 : 0 ≤ ∫ t in (0:ℝ)..1, (g t - c) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun t _ => sq_nonneg _)
  have hexp : ∀ t, (g t - c) ^ 2 = g t ^ 2 - 2 * c * g t + c ^ 2 := fun t => by ring
  simp_rw [hexp] at h0
  have i1 : IntervalIntegrable (fun t => g t ^ 2) volume 0 1 :=
    (hg.pow 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => 2 * c * g t) volume 0 1 :=
    (continuous_const.mul hg).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (i1.sub i2) intervalIntegrable_const,
    intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at h0
  simp only [sub_zero, one_smul, smul_eq_mul, one_mul] at h0
  rw [← hc] at h0
  nlinarith

lemma grad_cont (φ : (EuclideanSpace ℝ (Fin n)) → ℝ) (hφ : ContDiff ℝ 1 φ) : Continuous (gradient φ) := by
  have : gradient φ = fun x => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ φ x) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)

/-- Pointwise: `(φ(x+h) − φ(x))² ≤ ‖h‖² ∫₀¹ ‖∇φ(x + t h)‖² dt`. -/
lemma pt_bound (φ : (EuclideanSpace ℝ (Fin n)) → ℝ) (hφ : ContDiff ℝ 1 φ) (x h : (EuclideanSpace ℝ (Fin n))) :
    (φ (x + h) - φ x) ^ 2 ≤ ‖h‖ ^ 2 * ∫ t in (0:ℝ)..1, ‖gradient φ (x + t • h)‖ ^ 2 := by
  have hd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  set g : ℝ → ℝ := fun t => fderiv ℝ φ (x + t • h) h with hg
  have hgc : Continuous g := by
    have : Continuous fun t : ℝ => x + t • h := continuous_const.add (continuous_id.smul continuous_const)
    exact ((hφ.continuous_fderiv one_ne_zero).comp this).clm_apply continuous_const
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun t : ℝ => φ (x + t • h)) (g t) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => x + t • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    exact (hd (x + t • h)).hasFDerivAt.comp_hasDerivAt t h1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hgc.intervalIntegrable _ _)
  simp only [one_smul, zero_smul, add_zero] at hftc
  rw [← hftc]
  refine (sq_intervalIntegral_le g hgc).trans ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by norm_num) ((hgc.pow 2).intervalIntegrable _ _)
    ((continuous_const.mul (((grad_cont φ hφ).comp (continuous_const.add
      (continuous_id.smul continuous_const))).norm.pow 2)).intervalIntegrable _ _) ?_
  intro t _
  have h1 : g t = inner ℝ (gradient φ (x + t • h)) h := by
    rw [hg, inner_gradient_left]
  rw [h1]
  have h2 := abs_real_inner_le_norm (gradient φ (x + t • h)) h
  have h3 : 0 ≤ ‖gradient φ (x + t • h)‖ * ‖h‖ := by positivity
  calc inner ℝ (gradient φ (x + t • h)) h ^ 2 = |inner ℝ (gradient φ (x + t • h)) h| ^ 2 := by
        rw [sq_abs]
    _ ≤ (‖gradient φ (x + t • h)‖ * ‖h‖) ^ 2 := by
        exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    _ = ‖h‖ ^ 2 * ‖gradient φ (x + t • h)‖ ^ 2 := by ring

lemma grad_hcs (φ : (EuclideanSpace ℝ (Fin n)) → ℝ) (hc : HasCompactSupport φ) : HasCompactSupport (gradient φ) := by
  have : gradient φ = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm ∘ fderiv ℝ φ := rfl
  rw [this]
  exact (hc.fderiv (𝕜 := ℝ)).comp_left (map_zero _)

/-- Translation estimate: `∫ (φ(x+h) − φ(x))² ≤ ‖h‖² ∫ ‖∇φ‖²`. -/
lemma transl (φ : (EuclideanSpace ℝ (Fin n)) → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (h : (EuclideanSpace ℝ (Fin n))) :
    ∫ x, (φ (x + h) - φ x) ^ 2 ≤ ‖h‖ ^ 2 * ∫ x, ‖gradient φ x‖ ^ 2 := by
  set ν : Measure ℝ := volume.restrict (Set.Ioc 0 1) with hν
  haveI : IsFiniteMeasure ν := by rw [hν]; infer_instance
  set G : (EuclideanSpace ℝ (Fin n)) → ℝ → ℝ := fun x t => ‖gradient φ (x + t • h)‖ ^ 2 with hG
  have hGc : Continuous (Function.uncurry G) :=
    ((grad_cont φ hφ).comp (continuous_fst.add (continuous_snd.smul continuous_const))).norm.pow 2
  obtain ⟨M, hM⟩ := (grad_cont φ hφ).bounded_above_of_compact_support (grad_hcs φ hc)
  set K' : Set (EuclideanSpace ℝ (Fin n)) := (fun p : (EuclideanSpace ℝ (Fin n)) × ℝ => p.1 - p.2 • h) '' (tsupport (gradient φ) ×ˢ Set.Icc 0 1)
    with hK'def
  have hK' : IsCompact K' :=
    ((grad_hcs φ hc).isCompact.prod isCompact_Icc).image
      (continuous_fst.sub (continuous_snd.smul continuous_const))
  have hbint : Integrable (fun p : (EuclideanSpace ℝ (Fin n)) × ℝ => K'.indicator (fun _ => M ^ 2) p.1 * (1 : ℝ))
      (volume.prod ν) := by
    refine Integrable.mul_prod (L := ℝ) (f := fun x => K'.indicator (fun _ => M ^ 2) x)
      (g := fun _ : ℝ => (1 : ℝ)) ?_ (integrable_const (1 : ℝ))
    exact (integrable_indicator_iff hK'.measurableSet).2 (integrableOn_const hK'.measure_lt_top.ne)
  have hsnd : ∀ᵐ p ∂(volume.prod ν), p.2 ∈ Set.Ioc (0:ℝ) 1 :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) (ν := ν)).ae
      (ae_restrict_mem measurableSet_Ioc)
  have hint : Integrable (Function.uncurry G) (volume.prod ν) := by
    refine Integrable.mono' hbint hGc.aestronglyMeasurable ?_
    filter_upwards [hsnd] with p hp
    obtain ⟨x, t⟩ := p
    simp only [Function.uncurry_apply_pair, hG, mul_one, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    by_cases hz : x + t • h ∈ tsupport (gradient φ)
    · have hx : x ∈ K' := ⟨(x + t • h, t), ⟨hz, Set.Ioc_subset_Icc_self hp⟩, by simp⟩
      rw [Set.indicator_of_mem hx]
      have := hM (x + t • h)
      have h0 : 0 ≤ ‖gradient φ (x + t • h)‖ := norm_nonneg _
      exact pow_le_pow_left₀ h0 this 2
    · have : gradient φ (x + t • h) = 0 := image_eq_zero_of_notMem_tsupport hz
      rw [this, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact Set.indicator_nonneg (fun _ _ => sq_nonneg M) _
  have h1 : ∀ x, (φ (x + h) - φ x) ^ 2 ≤ ‖h‖ ^ 2 * ∫ t, G x t ∂ν := by
    intro x
    have := pt_bound φ hφ x h
    rwa [intervalIntegral.integral_of_le zero_le_one] at this
  have hleft : Integrable (fun x => ∫ t, G x t ∂ν) volume := hint.integral_prod_left
  calc ∫ x, (φ (x + h) - φ x) ^ 2 ≤ ∫ x, ‖h‖ ^ 2 * ∫ t, G x t ∂ν :=
        integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) (hleft.const_mul _)
          (ae_of_all _ h1)
    _ = ‖h‖ ^ 2 * ∫ t, ∫ x, G x t ∂volume ∂ν := by
        rw [integral_const_mul, integral_integral_swap hint]
    _ = ‖h‖ ^ 2 * ∫ x, ‖gradient φ x‖ ^ 2 := by
        congr 1
        have : ∀ t : ℝ, ∫ x, G x t ∂volume = ∫ x, ‖gradient φ x‖ ^ 2 := fun t =>
          integral_add_right_eq_self (fun z => ‖gradient φ z‖ ^ 2) (t • h)
        simp_rw [this]
        rw [integral_const]
        simp [hν, Real.volume_Ioc]

/-! ### Grid cells -/

/-- The grid cell of side `s` with index `k`. -/
def cell (s : ℝ) (k : Fin n → ℤ) : Set (EuclideanSpace ℝ (Fin n)) :=
  WithLp.ofLp ⁻¹' (Set.univ.pi fun i => Set.Ico ((k i : ℝ) * s) (((k i : ℝ) + 1) * s))

/-- The index of the cell containing `x`. -/
noncomputable def key (s : ℝ) (x : (EuclideanSpace ℝ (Fin n))) : Fin n → ℤ := fun i => ⌊x i / s⌋

lemma mem_cell_key {s : ℝ} (hs : 0 < s) (x : (EuclideanSpace ℝ (Fin n))) : x ∈ cell s (key s x) := by
  simp only [cell, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico, key]
  intro i
  constructor
  · have := Int.floor_le (x i / s); rwa [le_div_iff₀ hs] at this
  · have := Int.lt_floor_add_one (x i / s); rwa [div_lt_iff₀ hs] at this

lemma measurableSet_cell (s : ℝ) (k : Fin n → ℤ) : MeasurableSet (cell s k) :=
  (MeasurableSet.univ_pi fun _ => measurableSet_Ico).preimage
    (PiLp.volume_preserving_ofLp (ι := Fin n)).measurable

lemma volume_cell {s : ℝ} (hs : 0 < s) (k : Fin n → ℤ) :
    volume (cell s k) = ENNReal.ofReal (s ^ n) := by
  rw [cell, (PiLp.volume_preserving_ofLp (ι := Fin n)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet, Real.volume_pi_Ico]
  have : ∀ i, ((k i : ℝ) + 1) * s - (k i : ℝ) * s = s := fun i => by ring
  simp_rw [this]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_pow hs.le]

lemma volume_cell_toReal {s : ℝ} (hs : 0 < s) (k : Fin n → ℤ) :
    (volume (cell s k)).toReal = s ^ n := by
  rw [volume_cell hs, ENNReal.toReal_ofReal (by positivity)]

lemma dist_le_of_cell {s : ℝ} (hs : 0 < s) {k : Fin n → ℤ} {x y : (EuclideanSpace ℝ (Fin n))} (hx : x ∈ cell s k)
    (hy : y ∈ cell s k) : dist x y ≤ Real.sqrt n * s := by
  simp only [cell, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico] at hx hy
  rw [EuclideanSpace.dist_eq]
  have h1 : ∑ i, dist (x i) (y i) ^ 2 ≤ ∑ _i : Fin n, s ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hxi := hx i
    have hyi := hy i
    rw [Real.dist_eq]
    have : |x i - y i| ≤ s := by
      rw [abs_le]; constructor <;> nlinarith [hxi.1, hxi.2, hyi.1, hyi.2]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  calc Real.sqrt (∑ i, dist (x i) (y i) ^ 2) ≤ Real.sqrt (n * s ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt n * s := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hs.le]

/-- Cell average of `f` at `x`. -/
noncomputable def avg (s : ℝ) (f : (EuclideanSpace ℝ (Fin n)) → ℝ) (x : (EuclideanSpace ℝ (Fin n))) : ℝ :=
  (s ^ n)⁻¹ * ∫ y in cell s (key s x), f y

/-! ### Cauchy–Schwarz on a set -/

lemma intOn_of_bdd {A : Set (EuclideanSpace ℝ (Fin n))} (hA : volume A ≠ ⊤) {g : (EuclideanSpace ℝ (Fin n)) → ℝ} (hg : Continuous g) (C : ℝ)
    (hC : ∀ y, |g y| ≤ C) : IntegrableOn g A := by
  haveI : IsFiniteMeasure (volume.restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hA.lt_top⟩
  exact Integrable.mono' (integrable_const C) hg.aestronglyMeasurable
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hC y)

lemma sq_setIntegral_le {A : Set (EuclideanSpace ℝ (Fin n))} (hA : volume A ≠ ⊤) (f : (EuclideanSpace ℝ (Fin n)) → ℝ) (hf : IntegrableOn f A)
    (hf2 : IntegrableOn (fun y => f y ^ 2) A) :
    (∫ y in A, f y) ^ 2 ≤ (volume A).toReal * ∫ y in A, f y ^ 2 := by
  haveI : IsFiniteMeasure (volume.restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hA.lt_top⟩
  obtain ⟨V, hV⟩ : ∃ V, V = (volume A).toReal := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I, I = ∫ y in A, f y := ⟨_, rfl⟩
  obtain ⟨I2, hI2⟩ : ∃ I2, I2 = ∫ y in A, f y ^ 2 := ⟨_, rfl⟩
  rw [← hV, ← hI, ← hI2]
  have key : ∀ c : ℝ, 0 ≤ I2 - 2 * c * I + c ^ 2 * V := by
    intro c
    have h0 : 0 ≤ ∫ y in A, (f y - c) ^ 2 := integral_nonneg fun y => sq_nonneg _
    have hexp : ∀ y, (f y - c) ^ 2 = f y ^ 2 - 2 * c * f y + c ^ 2 := fun y => by ring
    simp_rw [hexp] at h0
    have i1 : Integrable (fun y => f y ^ 2 - 2 * c * f y) (volume.restrict A) :=
      hf2.sub (hf.const_mul (2 * c))
    rw [integral_add i1 (integrable_const _), integral_sub hf2 (hf.const_mul (2 * c)),
      integral_const_mul, integral_const] at h0
    have hvr : (volume.restrict A).real Set.univ = V := by
      rw [hV, measureReal_def, Measure.restrict_apply_univ]
    rw [hvr, smul_eq_mul, ← hI, ← hI2] at h0
    linarith
  have hV0 : 0 ≤ V := hV ▸ ENNReal.toReal_nonneg
  rcases hV0.eq_or_lt with hV0 | hVp
  · have hI0 : I = 0 := by
      by_contra hne
      have := key ((I2 + 1) / (2 * I))
      rw [← hV0] at this
      have h2 : 2 * ((I2 + 1) / (2 * I)) * I = I2 + 1 := by field_simp
      nlinarith
    rw [hI0, ← hV0]; simp
  · have h := key (I / V)
    have h2 : I2 - 2 * (I / V) * I + (I / V) ^ 2 * V = I2 - I ^ 2 / V := by
      field_simp; ring
    rw [h2, sub_nonneg, div_le_iff₀ hVp] at h
    linarith

/-- Pointwise Poincaré on a cell. -/
lemma avg_pt {s : ℝ} (hs : 0 < s) (φ : (EuclideanSpace ℝ (Fin n)) → ℝ) (hφc : Continuous φ) (hcs : HasCompactSupport φ)
    (x : (EuclideanSpace ℝ (Fin n))) :
    (φ x - avg s φ x) ^ 2 ≤ (s ^ n)⁻¹ * ∫ y in cell s (key s x), (φ x - φ y) ^ 2 := by
  set A := cell s (key s x) with hA
  have hAf : volume A ≠ ⊤ := by rw [hA, volume_cell hs]; exact ENNReal.ofReal_ne_top
  have hV : (volume A).toReal = s ^ n := volume_cell_toReal hs _
  have hsn : 0 < s ^ n := by positivity
  obtain ⟨M, hM⟩ := hφc.bounded_above_of_compact_support hcs
  have hφi : IntegrableOn φ A := (hφc.integrable_of_hasCompactSupport hcs).integrableOn
  haveI : IsFiniteMeasure (volume.restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hAf.lt_top⟩
  have hgi : IntegrableOn (fun y => φ x - φ y) A := (integrable_const _).sub hφi
  have hg2 : IntegrableOn (fun y => (φ x - φ y) ^ 2) A := by
    refine intOn_of_bdd hAf ((continuous_const.sub hφc).pow 2) ((2 * M) ^ 2) fun y => ?_
    rw [abs_of_nonneg (sq_nonneg _)]
    have h1 := hM x
    have h2 := hM y
    rw [Real.norm_eq_abs] at h1 h2
    have : |φ x - φ y| ≤ 2 * M := by
      calc |φ x - φ y| ≤ |φ x| + |φ y| := abs_sub _ _
        _ ≤ 2 * M := by linarith
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have heq : φ x - avg s φ x = (s ^ n)⁻¹ * ∫ y in A, (φ x - φ y) := by
    rw [integral_sub (integrable_const _) hφi, integral_const]
    simp only [smul_eq_mul, Measure.real, Measure.restrict_apply_univ]
    rw [hV, avg, ← hA]
    field_simp
  rw [heq]
  have hcs2 := sq_setIntegral_le hAf _ hgi hg2
  rw [hV] at hcs2
  calc ((s ^ n)⁻¹ * ∫ y in A, (φ x - φ y)) ^ 2
        = (s ^ n)⁻¹ ^ 2 * (∫ y in A, (φ x - φ y)) ^ 2 := by ring
    _ ≤ (s ^ n)⁻¹ ^ 2 * (s ^ n * ∫ y in A, (φ x - φ y) ^ 2) :=
        mul_le_mul_of_nonneg_left hcs2 (by positivity)
    _ = (s ^ n)⁻¹ * ∫ y in A, (φ x - φ y) ^ 2 := by field_simp

/-- Cell-average error bound (Poincaré on the grid, via the translation estimate). -/
lemma avg_bound {s : ℝ} (hs : 0 < s) (φ : (EuclideanSpace ℝ (Fin n)) → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcs : HasCompactSupport φ) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    ∫ x in Ω, (φ x - avg s φ x) ^ 2 ≤
      (s ^ n)⁻¹ * (volume (Metric.closedBall (0:(EuclideanSpace ℝ (Fin n))) (Real.sqrt n * s))).toReal *
        (Real.sqrt n * s) ^ 2 * ∫ x, ‖gradient φ x‖ ^ 2 := by
  have hφc : Continuous φ := hφ.continuous
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = Real.sqrt n * s := ⟨_, rfl⟩
  rw [← hδ]
  obtain ⟨B, hB⟩ : ∃ B, B = Metric.closedBall (0:(EuclideanSpace ℝ (Fin n))) δ := ⟨_, rfl⟩
  rw [← hB]
  have hBm : MeasurableSet B := hB ▸ measurableSet_closedBall
  have hBf : volume B ≠ ⊤ := hB ▸ measure_closedBall_lt_top.ne
  have hBc : IsCompact B := hB ▸ isCompact_closedBall _ _
  obtain ⟨M, hM⟩ := hφc.bounded_above_of_compact_support hcs
  have hdiff : ∀ a b, (φ a - φ b) ^ 2 ≤ (2 * M) ^ 2 := by
    intro a b
    have h1 := hM a
    have h2 := hM b
    rw [Real.norm_eq_abs] at h1 h2
    have : |φ a - φ b| ≤ 2 * M := by
      calc |φ a - φ b| ≤ |φ a| + |φ b| := abs_sub _ _
        _ ≤ 2 * M := by linarith
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  obtain ⟨F, hF⟩ : ∃ F : (EuclideanSpace ℝ (Fin n)) × (EuclideanSpace ℝ (Fin n)) → ℝ,
      F = (Prod.snd ⁻¹' B).indicator (fun p => (φ (p.1 + p.2) - φ p.1) ^ 2) := ⟨_, rfl⟩
  have hF0 : ∀ p, 0 ≤ F p := fun p => by
    rw [hF]; exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  set K'' : Set (EuclideanSpace ℝ (Fin n)) := (fun p : (EuclideanSpace ℝ (Fin n)) × (EuclideanSpace ℝ (Fin n)) => p.1 - p.2) '' (tsupport φ ×ˢ B) ∪ tsupport φ with hK''
  have hK''c : IsCompact K'' :=
    ((hcs.isCompact.prod hBc).image (continuous_fst.sub continuous_snd)).union hcs.isCompact
  have hbint : Integrable (fun p : (EuclideanSpace ℝ (Fin n)) × (EuclideanSpace ℝ (Fin n)) =>
      K''.indicator (fun _ => (2 * M) ^ 2) p.1 * B.indicator (fun _ => (1:ℝ)) p.2)
      (volume.prod volume) := by
    refine Integrable.mul_prod (L := ℝ) (f := fun x => K''.indicator (fun _ => (2 * M) ^ 2) x)
      (g := fun h => B.indicator (fun _ => (1:ℝ)) h) ?_ ?_
    · exact (integrable_indicator_iff hK''c.measurableSet).2
        (integrableOn_const hK''c.measure_lt_top.ne)
    · exact (integrable_indicator_iff hBm).2 (integrableOn_const hBf)
  have hFm : AEStronglyMeasurable F (volume.prod volume) := by
    rw [hF]
    refine (Measurable.indicator ?_ (hBm.preimage measurable_snd)).aestronglyMeasurable
    exact (((hφc.comp (continuous_fst.add continuous_snd)).sub
      (hφc.comp continuous_fst)).pow 2).measurable
  have hFint : Integrable F (volume.prod volume) := by
    refine Integrable.mono' hbint hFm (ae_of_all _ fun p => ?_)
    obtain ⟨x, h⟩ := p
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 _)]
    by_cases hh : h ∈ B
    · have hmem : (x, h) ∈ Prod.snd ⁻¹' B := hh
      rw [hF, Set.indicator_of_mem hmem]
      simp only [Set.indicator_of_mem hh, mul_one]
      by_cases hx : x ∈ K''
      · rw [Set.indicator_of_mem hx]
        exact hdiff _ _
      · rw [Set.indicator_of_notMem hx]
        have h1 : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hx' => hx (Or.inr hx'))
        have h2 : φ (x + h) = 0 := image_eq_zero_of_notMem_tsupport
          (fun hx' => hx (Or.inl ⟨(x + h, h), ⟨hx', hh⟩, by simp⟩))
        simp [h1, h2]
    · have hmem : (x, h) ∉ Prod.snd ⁻¹' B := hh
      rw [hF, Set.indicator_of_notMem hmem]
      simp [Set.indicator_of_notMem hh]
  have hRint : Integrable (fun x => ∫ h, F (x, h)) volume := hFint.integral_prod_left
  have hR0 : ∀ x, 0 ≤ (s ^ n)⁻¹ * ∫ h, F (x, h) := fun x =>
    mul_nonneg (by positivity) (integral_nonneg fun h => hF0 _)
  -- pointwise bound
  have hpt : ∀ x, (φ x - avg s φ x) ^ 2 ≤ (s ^ n)⁻¹ * ∫ h, F (x, h) := by
    intro x
    refine (avg_pt hs φ hφc hcs x).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    set A := cell s (key s x) with hA
    have hAB : A ⊆ Metric.closedBall x δ := by
      intro y hy
      rw [Metric.mem_closedBall, hδ]
      exact dist_le_of_cell hs hy (mem_cell_key hs x)
    have hg : Continuous fun y => (φ x - φ y) ^ 2 := (continuous_const.sub hφc).pow 2
    have hgi : IntegrableOn (fun y => (φ x - φ y) ^ 2) (Metric.closedBall x δ) :=
      intOn_of_bdd measure_closedBall_lt_top.ne hg ((2 * M) ^ 2) fun y => by
        rw [abs_of_nonneg (sq_nonneg _)]; exact hdiff _ _
    calc ∫ y in A, (φ x - φ y) ^ 2 ≤ ∫ y in Metric.closedBall x δ, (φ x - φ y) ^ 2 :=
          setIntegral_mono_set hgi (ae_of_all _ fun y => sq_nonneg _) hAB.eventuallyLE
      _ = ∫ y, (Metric.closedBall x δ).indicator (fun y => (φ x - φ y) ^ 2) y :=
          (integral_indicator measurableSet_closedBall).symm
      _ = ∫ h, (Metric.closedBall x δ).indicator (fun y => (φ x - φ y) ^ 2) (x + h) :=
          (integral_add_left_eq_self _ x).symm
      _ = ∫ h, F (x, h) := by
          refine integral_congr_ae (ae_of_all _ fun h => ?_)
          have hiff : x + h ∈ Metric.closedBall x δ ↔ (x, h) ∈ Prod.snd ⁻¹' B := by
            simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Set.mem_preimage,
              hB, mem_closedBall_zero_iff, sub_zero]
          by_cases hh : x + h ∈ Metric.closedBall x δ
          · simp only [hF]
            rw [Set.indicator_of_mem hh, Set.indicator_of_mem (hiff.1 hh)]
            ring
          · simp only [hF]
            rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem (fun h' => hh (hiff.2 h'))]
  set G := ∫ x, ‖gradient φ x‖ ^ 2 with hG
  have hG0 : 0 ≤ G := integral_nonneg fun x => sq_nonneg _
  have hinner : ∀ h, ∫ x, F (x, h) = B.indicator (fun h => ∫ x, (φ (x + h) - φ x) ^ 2) h := by
    intro h
    by_cases hh : h ∈ B
    · rw [Set.indicator_of_mem hh]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      have hmem : (x, h) ∈ Prod.snd ⁻¹' B := hh
      simp only [hF]
      rw [Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hh]
      have : ∀ x, F (x, h) = 0 := fun x => by
        have hmem : (x, h) ∉ Prod.snd ⁻¹' B := hh
        rw [hF, Set.indicator_of_notMem hmem]
      simp [this]
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  calc ∫ x in Ω, (φ x - avg s φ x) ^ 2 ≤ ∫ x in Ω, (s ^ n)⁻¹ * ∫ h, F (x, h) :=
        integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _)
          ((hRint.const_mul _).integrableOn) (ae_of_all _ hpt)
    _ ≤ ∫ x, (s ^ n)⁻¹ * ∫ h, F (x, h) :=
        setIntegral_le_integral (hRint.const_mul _) (ae_of_all _ hR0)
    _ = (s ^ n)⁻¹ * ∫ h, ∫ x, F (x, h) := by
        rw [integral_const_mul, integral_integral_swap (f := fun x h => F (x, h)) hFint]
    _ ≤ (s ^ n)⁻¹ * ∫ h, B.indicator (fun _ => δ ^ 2 * G) h := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine integral_mono_of_nonneg (ae_of_all _ fun h => integral_nonneg fun x => hF0 _)
          ((integrable_indicator_iff hBm).2 (integrableOn_const hBf)) (ae_of_all _ fun h => ?_)
        show ∫ x, F (x, h) ≤ _
        rw [hinner]
        by_cases hh : h ∈ B
        · rw [Set.indicator_of_mem hh, Set.indicator_of_mem hh]
          refine (transl φ hφ hcs h).trans ?_
          have hn : ‖h‖ ≤ δ := by rw [hB, mem_closedBall_zero_iff] at hh; exact hh
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hn 2) hG0
        · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem hh]
    _ = (s ^ n)⁻¹ * (volume B).toReal * δ ^ 2 * G := by
        rw [integral_indicator_const _ hBm, smul_eq_mul, measureReal_def]
        ring

/-! ### The finite-rank cell-average operator on `L²(Ω)` -/

lemma mem_cell_iff {s : ℝ} (hs : 0 < s) (k : Fin n → ℤ) (x : (EuclideanSpace ℝ (Fin n))) : x ∈ cell s k ↔ key s x = k := by
  constructor
  · intro hx
    funext i
    simp only [cell, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico] at hx
    simp only [key]
    rw [Int.floor_eq_iff, le_div_iff₀ hs, div_lt_iff₀ hs]
    exact hx i
  · rintro rfl; exact mem_cell_key hs x

lemma coeFn_finsum {μ : Measure (EuclideanSpace ℝ (Fin n))} {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (g : ι → Lp ℝ 2 μ) : ⇑(∑ i ∈ S, g i) =ᵐ[μ] fun x => ∑ i ∈ S, g i x := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
    rw [hx]; rfl
  | @insert k S hk ih =>
    simp only [Finset.sum_insert hk]
    filter_upwards [Lp.coeFn_add (g k) (∑ i ∈ S, g i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2]

/-- Finite sums of rank-one maps `c • ⟪e k, ·⟫ e k` are compact (generic Hilbert space). -/
lemma rank_one_sum_compact {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (e : ι → H) (c : ℝ) :
    IsCompactOperator (∑ k ∈ S, c •
      ((ContinuousLinearMap.toSpanSingleton ℝ (e k)).comp (innerSL ℝ (e k))) : H →L[ℝ] H) := by
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isCompactOperator_zero
  | @insert k S hk ih =>
    rw [Finset.sum_insert hk, ContinuousLinearMap.coe_add', ContinuousLinearMap.coe_smul']
    refine IsCompactOperator.add (IsCompactOperator.smul ?_ _) ih
    rw [ContinuousLinearMap.coe_comp']
    exact (isCompactOperator_of_locallyCompactSpace_rng _).comp_clm _

section Op

variable (Ω : Set (EuclideanSpace ℝ (Fin n)))

lemma cellΩ_ne_top {s : ℝ} (hs : 0 < s) (k : Fin n → ℤ) :
    (volume.restrict Ω) (cell s k) ≠ ⊤ :=
  ((Measure.restrict_apply_le _ _).trans_lt
    (by rw [volume_cell hs]; exact ENNReal.ofReal_lt_top)).ne

/-- Indicator of a cell in `L²(Ω)`. -/
noncomputable def ek {s : ℝ} (hs : 0 < s) (k : Fin n → ℤ) : Lp ℝ 2 (volume.restrict Ω) :=
  indicatorConstLp 2 (measurableSet_cell s k) (cellΩ_ne_top Ω hs k) (1 : ℝ)

/-- The cell-average operator over the cells indexed by `S`. -/
noncomputable def Fop {s : ℝ} (hs : 0 < s) (S : Finset (Fin n → ℤ)) :
    Lp ℝ 2 (volume.restrict Ω) →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  ∑ k ∈ S, (s ^ n)⁻¹ •
    ((ContinuousLinearMap.toSpanSingleton ℝ (ek Ω hs k)).comp (innerSL ℝ (ek Ω hs k)))

lemma Fop_compact {s : ℝ} (hs : 0 < s) (S : Finset (Fin n → ℤ)) :
    IsCompactOperator (Fop Ω hs S) :=
  rank_one_sum_compact S (ek Ω hs) (s ^ n)⁻¹

lemma Fop_apply {s : ℝ} (hs : 0 < s) (S : Finset (Fin n → ℤ)) (f : Lp ℝ 2 (volume.restrict Ω)) :
    Fop Ω hs S f = ∑ k ∈ S,
      ((s ^ n)⁻¹ * ∫ x in cell s k, f x ∂(volume.restrict Ω)) • ek Ω hs k := by
  simp only [Fop, sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ek, L2.inner_indicatorConstLp_one]

lemma Fop_ae {s : ℝ} (hs : 0 < s) (S : Finset (Fin n → ℤ)) (f : Lp ℝ 2 (volume.restrict Ω)) :
    ⇑(Fop Ω hs S f) =ᵐ[volume.restrict Ω] fun x => if key s x ∈ S then
      (s ^ n)⁻¹ * ∫ y in cell s (key s x), f y ∂(volume.restrict Ω) else 0 := by
  rw [Fop_apply]
  have hk : ∀ k ∈ S, ⇑(((s ^ n)⁻¹ * ∫ x in cell s k, f x ∂(volume.restrict Ω)) • ek Ω hs k)
      =ᵐ[volume.restrict Ω] fun x => ((s ^ n)⁻¹ * ∫ y in cell s k, f y ∂(volume.restrict Ω)) *
        (cell s k).indicator (fun _ => (1:ℝ)) x := by
    intro k _
    filter_upwards [Lp.coeFn_smul ((s ^ n)⁻¹ * ∫ x in cell s k, f x ∂(volume.restrict Ω))
      (ek Ω hs k), indicatorConstLp_coeFn (p := 2) (hs := measurableSet_cell s k)
      (hμs := cellΩ_ne_top Ω hs k) (c := (1:ℝ))] with x h1 h2
    rw [h1, Pi.smul_apply, smul_eq_mul, ek, h2]
  filter_upwards [coeFn_finsum S _, (Filter.eventually_all_finset S).2 hk] with x h1 h2
  rw [h1, Finset.sum_congr rfl h2]
  by_cases hx : key s x ∈ S
  · rw [if_pos hx, Finset.sum_eq_single (key s x)]
    · rw [Set.indicator_of_mem (mem_cell_key hs x), mul_one]
    · intro b _ hb
      rw [Set.indicator_of_notMem (fun h => hb ((mem_cell_iff hs b x).1 h).symm), mul_zero]
    · intro h; exact absurd hx h
  · rw [if_neg hx]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [Set.indicator_of_notMem (fun h => hx (((mem_cell_iff hs b x).1 h) ▸ hb)), mul_zero]

end Op

end Rel6f

namespace HunterPDE.Elliptic.RC6f

open HunterPDE.Elliptic Rel6f

variable {n : ℕ}

/-- First component `JetL2 n Ω → L²(Ω)`. -/
noncomputable def Afst (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    JetL2 n Ω →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).compLpL 2 (volume.restrict Ω)

lemma Afst_ae (Ω : Set (EuclideanSpace ℝ (Fin n))) (U : JetL2 n Ω) :
    ⇑(Afst n Ω U) =ᵐ[volume.restrict Ω] fun x => (WithLp.ofLp (U x)).1 := by
  have := ContinuousLinearMap.coeFn_compLp (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))) U
  filter_upwards [this] with x hx
  show (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).compLp U x = _
  rw [hx]; rfl

lemma grad_add (φ ψ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : Differentiable ℝ φ)
    (hψ : Differentiable ℝ ψ) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => φ y + ψ y) x = gradient φ x + gradient ψ x := by
  show (InnerProductSpace.toDual ℝ _).symm (fderiv ℝ (fun y => φ y + ψ y) x) =
    (InnerProductSpace.toDual ℝ _).symm (fderiv ℝ φ x) +
      (InnerProductSpace.toDual ℝ _).symm (fderiv ℝ ψ x)
  rw [fderiv_fun_add (hφ x) (hψ x), map_add]

lemma grad_smul (c : ℝ) (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : Differentiable ℝ φ)
    (x : EuclideanSpace ℝ (Fin n)) : gradient (fun y => c * φ y) x = c • gradient φ x := by
  show (InnerProductSpace.toDual ℝ _).symm (fderiv ℝ (fun y => c * φ y) x) =
    c • (InnerProductSpace.toDual ℝ _).symm (fderiv ℝ φ x)
  rw [fderiv_const_mul (hφ x), LinearIsometryEquiv.map_smulₛₗ]
  simp

lemma grad_zero_of_notMem (φ : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∉ tsupport φ) : gradient φ x = 0 := by
  have : fderiv ℝ φ x = 0 := by
    by_contra h
    exact hx (support_fderiv_subset ℝ (Function.mem_support.2 h))
  show (InnerProductSpace.toDual ℝ _).symm (fderiv ℝ φ x) = 0
  rw [this, map_zero]

lemma tj_zero (Ω : Set (EuclideanSpace ℝ (Fin n))) : (0 : JetL2 n Ω) ∈ testJets n Ω := by
  refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_, ?_⟩
  · rw [tsupport_zero]; exact Set.empty_subset _
  · filter_upwards [Lp.coeFn_zero (Jet n) 2 (volume.restrict Ω)] with x hx
    rw [hx, grad_zero_of_notMem 0 x (by rw [tsupport_zero]; exact Set.notMem_empty x)]
    rfl

lemma tj_add (Ω : Set (EuclideanSpace ℝ (Fin n))) (U V : JetL2 n Ω) (hU : U ∈ testJets n Ω)
    (hV : V ∈ testJets n Ω) : U + V ∈ testJets n Ω := by
  obtain ⟨φ, hφ, hφc, hφs, hφU⟩ := hU
  obtain ⟨ψ, hψ, hψc, hψs, hψV⟩ := hV
  refine ⟨fun y => φ y + ψ y, hφ.add hψ, hφc.add hψc, ?_, ?_⟩
  · exact (tsupport_add φ ψ).trans (Set.union_subset hφs hψs)
  · filter_upwards [Lp.coeFn_add U V, hφU, hψV] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, grad_add φ ψ (hφ.differentiable (by simp))
      (hψ.differentiable (by simp)), ← WithLp.toLp_add]
    rfl

lemma tj_smul (Ω : Set (EuclideanSpace ℝ (Fin n))) (c : ℝ) (U : JetL2 n Ω)
    (hU : U ∈ testJets n Ω) : c • U ∈ testJets n Ω := by
  obtain ⟨φ, hφ, hφc, hφs, hφU⟩ := hU
  refine ⟨fun y => c * φ y, contDiff_const.mul hφ, hφc.mul_left (f := fun _ => c), ?_, ?_⟩
  · exact (tsupport_mul_subset_right (f := fun _ => c) (g := φ)).trans hφs
  · filter_upwards [Lp.coeFn_smul c U, hφU] with x h1 h2
    rw [h1, Pi.smul_apply, h2, grad_smul c φ (hφ.differentiable (by simp)) x, ← WithLp.toLp_smul]
    rfl

/-- The test jets form a subspace. -/
noncomputable def TJ (Ω : Set (EuclideanSpace ℝ (Fin n))) : Submodule ℝ (JetL2 n Ω) where
  carrier := testJets n Ω
  add_mem' := fun {U V} hU hV => tj_add Ω U V hU hV
  zero_mem' := tj_zero Ω
  smul_mem' := fun c U hU => tj_smul Ω c U hU

lemma H10_subset (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    ((H10 n Ω : Submodule ℝ (JetL2 n Ω)) : Set (JetL2 n Ω)) ⊆ closure (testJets n Ω) := by
  have h1 : Submodule.span ℝ (testJets n Ω) ≤ TJ Ω := Submodule.span_le.2 fun U hU => hU
  have h2 := Submodule.topologicalClosure_mono h1
  intro U hU
  have := h2 hU
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at this
  exact this

lemma norm_sq_L2 (Ω : Set (EuclideanSpace ℝ (Fin n))) (f : Lp ℝ 2 (volume.restrict Ω)) :
    ‖f‖ ^ 2 = ∫ x in Ω, f x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show inner ℝ (f x) (f x) = f x ^ 2
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

lemma norm_sq_jet (Ω : Set (EuclideanSpace ℝ (Fin n))) (U : JetL2 n Ω) :
    ‖U‖ ^ 2 = ∫ x in Ω, ‖U x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show inner ℝ (U x) (U x) = ‖U x‖ ^ 2
  rw [real_inner_self_eq_norm_sq]

/-- The grid estimate on a test jet. -/
lemma tj_est (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩm : MeasurableSet Ω) {s : ℝ} (hs : 0 < s)
    (S : Finset (Fin n → ℤ)) (hS : ∀ x ∈ Ω, key s x ∈ S) (U : JetL2 n Ω)
    (hU : U ∈ testJets n Ω) :
    ‖Afst n Ω U - Fop Ω hs S (Afst n Ω U)‖ ^ 2 ≤
      (s ^ n)⁻¹ * (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n))
        (Real.sqrt n * s))).toReal * (Real.sqrt n * s) ^ 2 * ‖U‖ ^ 2 := by
  obtain ⟨φ, hφ, hφc, hφs, hφU⟩ := hU
  have hφ1 : ContDiff ℝ 1 φ := by simpa using contDiff_infty.1 hφ 1
  obtain ⟨f, hf⟩ : ∃ f, f = Afst n Ω U := ⟨_, rfl⟩
  rw [← hf]
  have hfφ : ⇑f =ᵐ[volume.restrict Ω] φ := by
    filter_upwards [hf ▸ Afst_ae Ω U, hφU] with x h1 h2
    rw [h1, h2]
  have hφ0 : ∀ x ∉ Ω, φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hφs h))
  have hcellint : ∀ k, ∫ y in cell s k, f y ∂(volume.restrict Ω) = ∫ y in cell s k, φ y := by
    intro k
    rw [Measure.restrict_restrict (measurableSet_cell s k)]
    rw [integral_congr_ae (ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right hfφ)]
    exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_cell s k)
      Set.inter_subset_left (fun y hy => hφ0 y (fun h => hy.2 ⟨hy.1, h⟩))).symm
  have hFae : ⇑(Fop Ω hs S f) =ᵐ[volume.restrict Ω] avg s φ := by
    filter_upwards [Fop_ae Ω hs S f, ae_restrict_mem hΩm] with x h1 hx
    rw [h1, if_pos (hS x hx), hcellint]
    rfl
  have hnorm : ‖f - Fop Ω hs S f‖ ^ 2 = ∫ x in Ω, (φ x - avg s φ x) ^ 2 := by
    rw [norm_sq_L2]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub f (Fop Ω hs S f), hfφ, hFae] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hgrad : ∫ x, ‖gradient φ x‖ ^ 2 ≤ ‖U‖ ^ 2 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω) (fun x hx => by
      rw [grad_zero_of_notMem φ x (fun h => hx (hφs h))]; simp), norm_sq_jet]
    have hcs2 : HasCompactSupport (fun x => ‖gradient φ x‖ ^ 2) :=
      (grad_hcs φ hφc).comp_left (g := fun v : EuclideanSpace ℝ (Fin n) => ‖v‖ ^ 2) (by simp)
    refine integral_mono_ae ?_ ?_ ?_
    · exact ((((grad_cont φ hφ1).norm.pow 2)).integrable_of_hasCompactSupport hcs2).integrableOn
    · exact (L2.integrable_inner U U).congr (ae_of_all _ fun x => real_inner_self_eq_norm_sq _)
    · filter_upwards [hφU] with x hx
      rw [hx, WithLp.prod_norm_sq_eq_of_L2]
      exact le_add_of_nonneg_left (sq_nonneg _)
  rw [hnorm]
  refine (avg_bound hs φ hφ1 hφc Ω).trans ?_
  exact mul_le_mul_of_nonneg_left hgrad (by positivity)

lemma key_mem (Ω : Set (EuclideanSpace ℝ (Fin n))) {R : ℝ} (hR : Ω ⊆ Metric.closedBall 0 R)
    {s : ℝ} (hs : 0 < s) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) :
    key s x ∈ Finset.Icc (fun _ : Fin n => ⌊-R / s⌋) (fun _ => ⌊R / s⌋) := by
  rw [Finset.mem_Icc]
  have hxR : ‖x‖ ≤ R := by
    have := hR hx; rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hxi : ∀ i, |x i| ≤ R := fun i => by
    have := PiLp.norm_apply_le x i
    rw [Real.norm_eq_abs] at this
    linarith
  constructor
  · intro i
    simp only [key]
    apply Int.floor_mono
    exact div_le_div_of_nonneg_right (by linarith [neg_abs_le (x i), hxi i]) hs.le
  · intro i
    simp only [key]
    apply Int.floor_mono
    exact div_le_div_of_nonneg_right (by linarith [le_abs_self (x i), hxi i]) hs.le

lemma K_eq {s : ℝ} (hs : 0 < s) :
    (s ^ n)⁻¹ * (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n))
        (Real.sqrt n * s))).toReal * (Real.sqrt n * s) ^ 2 =
      (Real.sqrt n ^ n * (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal
        * n) * s ^ 2 := by
  rw [Measure.addHaar_closedBall' volume (0 : EuclideanSpace ℝ (Fin n)) (by positivity),
    finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have : s ^ n ≠ 0 := by positivity
  field_simp

/-- **Rellich–Kondrachov** for `H¹₀(Ω)`, `Ω` bounded open: the inclusion into `L²(Ω)` is compact. -/
theorem rellich (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) :
    IsCompactOperator ((Afst n Ω).comp (H10 n Ω).subtypeL) := by
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  set C0 : ℝ := Real.sqrt n ^ n *
    (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal * n with hC0
  have hC0n : 0 ≤ C0 := by positivity
  have hsk : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  set T := (Afst n Ω).comp (H10 n Ω).subtypeL with hT
  set Fk : ℕ → (H10 n Ω →L[ℝ] Lp ℝ 2 (volume.restrict Ω)) := fun k =>
    (Fop Ω (hsk k) (Finset.Icc (fun _ : Fin n => ⌊-R / (1 / ((k : ℝ) + 1))⌋)
      (fun _ => ⌊R / (1 / ((k : ℝ) + 1))⌋))).comp T with hFk
  have hbound : ∀ k : ℕ, ‖Fk k - T‖ ≤ Real.sqrt C0 * (1 / ((k : ℝ) + 1)) := by
    intro k
    set s : ℝ := 1 / ((k : ℝ) + 1) with hs_def
    have hs : 0 < s := hsk k
    set S := Finset.Icc (fun _ : Fin n => ⌊-R / s⌋) (fun _ => ⌊R / s⌋) with hSdef
    have hS : ∀ x ∈ Ω, key s x ∈ S := fun x hx => key_mem Ω hR hs x hx
    have hKs := K_eq (n := n) hs
    set K := (s ^ n)⁻¹ * (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n))
        (Real.sqrt n * s))).toReal * (Real.sqrt n * s) ^ 2 with hK
    have hK0 : 0 ≤ K := by rw [hKs]; positivity
    -- closed set containing the test jets
    set Z : Set (JetL2 n Ω) :=
      {U | ‖Afst n Ω U - Fop Ω hs S (Afst n Ω U)‖ ≤ Real.sqrt K * ‖U‖} with hZ
    have hZc : IsClosed Z := isClosed_le
      (continuous_norm.comp ((Afst n Ω).continuous.sub
        ((Fop Ω hs S).continuous.comp (Afst n Ω).continuous)))
      (continuous_const.mul continuous_norm)
    have hTJ : testJets n Ω ⊆ Z := by
      intro U hU
      have h2 := tj_est Ω hΩ.measurableSet hs S hS U hU
      show ‖Afst n Ω U - Fop Ω hs S (Afst n Ω U)‖ ≤ Real.sqrt K * ‖U‖
      calc ‖Afst n Ω U - Fop Ω hs S (Afst n Ω U)‖
          = Real.sqrt (‖Afst n Ω U - Fop Ω hs S (Afst n Ω U)‖ ^ 2) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (K * ‖U‖ ^ 2) := Real.sqrt_le_sqrt h2
        _ = Real.sqrt K * ‖U‖ := by
            rw [Real.sqrt_mul hK0, Real.sqrt_sq (norm_nonneg _)]
    have hH : ∀ u : H10 n Ω, (u : JetL2 n Ω) ∈ Z := fun u =>
      closure_minimal hTJ hZc (H10_subset Ω u.2)
    have hsqK : Real.sqrt K = Real.sqrt C0 * s := by
      rw [hKs, Real.sqrt_mul hC0n, Real.sqrt_sq hs.le]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
    have h1 := hH u
    have e1 : (Fk k - T) u = Fop Ω hs S (Afst n Ω u) - Afst n Ω u := rfl
    rw [e1, norm_sub_rev, ← hsqK]
    exact h1
  refine isCompactOperator_of_tendsto (l := Filter.atTop) (F := Fk) ?_
    (Filter.Eventually.of_forall fun k => (Fop_compact Ω (hsk k) _).comp_clm _)
  refine (tendsto_iff_norm_sub_tendsto_zero
    (E := H10 n Ω →L[ℝ] Lp ℝ 2 (volume.restrict Ω)) (f := Fk) (a := Filter.atTop) (b := T)).2 ?_
  refine squeeze_zero (fun k => norm_nonneg (Fk k - T)) hbound ?_
  have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (Real.sqrt C0)
  simpa using this

end HunterPDE.Elliptic.RC6f


set_option autoImplicit false

open scoped InnerProductSpace
open ContinuousLinearMap

namespace FB92

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Lax–Milgram core. -/
lemma core (a : V →L[ℝ] V →L[ℝ] ℝ) (C : ℝ) (hC : 0 < C) (hcoer : ∀ u, C * ‖u‖ ^ 2 ≤ a u u)
    (f : StrongDual ℝ V) : ∃! u : V, ∀ φ, a u φ = f φ := by
  have coercive : IsCoercive a := ⟨C, hC, fun u => by
    have := hcoer u; nlinarith [this]⟩
  set E := coercive.continuousLinearEquivOfBilin with hE
  set w0 := (InnerProductSpace.toDual ℝ V).symm f with hw0
  have key : ∀ y : V, (∀ φ, a y φ = f φ) ↔ E y = w0 := by
    intro y
    constructor
    · intro h
      refine ext_inner_right ℝ fun φ => ?_
      rw [hE, IsCoercive.continuousLinearEquivOfBilin_apply, h, hw0,
        InnerProductSpace.toDual_symm_apply]
    · intro h φ
      rw [← IsCoercive.continuousLinearEquivOfBilin_apply coercive, ← hE, h, hw0,
        InnerProductSpace.toDual_symm_apply]
  refine ⟨E.symm w0, (key _).2 (E.apply_symm_apply w0), fun y hy => ?_⟩
  have := (key y).1 hy
  rw [← this, E.symm_apply_apply]

/-- The bilinear form `(u, v) ↦ ⟪J u, J v⟫`. -/
noncomputable def jj (J : V →L[ℝ] H) : V →L[ℝ] V →L[ℝ] ℝ := (innerSL ℝ).bilinearComp J J

lemma jj_apply (J : V →L[ℝ] H) (u v : V) : jj J u v = ⟪J u, J v⟫_ℝ := by
  simp [jj]

/-- The homogeneous solution space of `b(u, φ) - lam ⟪J u, J φ⟫ = 0`. -/
noncomputable def Sub0 (J : V →L[ℝ] H) (b : V →L[ℝ] V →L[ℝ] ℝ) (lam : ℝ) : Submodule ℝ V :=
  LinearMap.ker ((b + (-lam) • jj J : V →L[ℝ] V →L[ℝ] ℝ) : V →ₗ[ℝ] V →L[ℝ] ℝ)

lemma mem_Sub0 (J : V →L[ℝ] H) (b : V →L[ℝ] V →L[ℝ] ℝ) (lam : ℝ) (u : V) :
    u ∈ Sub0 J b lam ↔ ∀ φ, b u φ + (-lam) * ⟪J u, J φ⟫_ℝ = 0 := by
  simp only [Sub0, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.ext_iff,
    ContinuousLinearMap.add_apply, smul_apply, jj_apply,
    ContinuousLinearMap.zero_apply, smul_eq_mul]

section
variable (J : V →L[ℝ] H) (b : V →L[ℝ] V →L[ℝ] ℝ) {γ C μ : ℝ}

lemma uniq (hC : 0 < C) (hcoer : ∀ u, C * ‖u‖ ^ 2 ≤ b u u + γ * ⟪J u, J u⟫_ℝ) (hμ : γ ≤ μ)
    (w : V) (hw : ∀ φ, b w φ + μ * ⟪J w, J φ⟫_ℝ = 0) : w = 0 := by
  have h1 := hcoer w
  have h2 := hw w
  have h3 : 0 ≤ ⟪J w, J w⟫_ℝ := real_inner_self_nonneg
  have h4 : C * ‖w‖ ^ 2 ≤ 0 := by nlinarith
  have h5 : ‖w‖ ^ 2 ≤ 0 := by
    by_contra h
    push_neg at h
    nlinarith
  have h6 : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
  exact norm_eq_zero.mp h6

lemma exist (hC : 0 < C) (hcoer : ∀ u, C * ‖u‖ ^ 2 ≤ b u u + γ * ⟪J u, J u⟫_ℝ) (hμ : γ ≤ μ)
    (g : H) : ∃ u, ∀ φ, b u φ + μ * ⟪J u, J φ⟫_ℝ = ⟪g, J φ⟫_ℝ := by
  have hc : ∀ u, C * ‖u‖ ^ 2 ≤ (b + μ • jj J) u u := by
    intro u
    simp only [ContinuousLinearMap.add_apply, smul_apply, jj_apply,
      smul_eq_mul]
    nlinarith [hcoer u, real_inner_self_nonneg (x := J u)]
  obtain ⟨u, hu, -⟩ := core (b + μ • jj J) C hC hc ((innerSL ℝ g).comp J)
  refine ⟨u, fun φ => ?_⟩
  have := hu φ
  simpa only [ContinuousLinearMap.add_apply, smul_apply, jj_apply,
    smul_eq_mul, ContinuousLinearMap.comp_apply, innerSL_apply_apply] using this


/-- The solution operator `g ↦ J u` (Lax–Milgram for `b + μ jj J`), factored through `V`. -/
lemma solK (hC : 0 < C) (hcoer : ∀ u, C * ‖u‖ ^ 2 ≤ b u u + γ * ⟪J u, J u⟫_ℝ) (hμ : γ ≤ μ) :
    ∃ S : H →L[ℝ] V, ∀ g u, (∀ φ, b u φ + μ * ⟪J u, J φ⟫_ℝ = ⟪g, J φ⟫_ℝ) → S g = u := by
  have happ : ∀ u v, (b + μ • jj J) u v = b u v + μ * ⟪J u, J v⟫_ℝ := by
    intro u v
    simp only [ContinuousLinearMap.add_apply, smul_apply, jj_apply, smul_eq_mul]
  have coercive : IsCoercive (b + μ • jj J) := ⟨C, hC, fun u => by
    rw [happ]
    have h1 := hcoer u
    have h2 : 0 ≤ ⟪J u, J u⟫_ℝ := real_inner_self_nonneg
    have h3 : C * ‖u‖ ^ 2 = C * ‖u‖ * ‖u‖ := by ring
    nlinarith⟩
  set E := coercive.continuousLinearEquivOfBilin with hE
  refine ⟨(E.symm : V →L[ℝ] V) ∘L ContinuousLinearMap.adjoint J, fun g u hu => ?_⟩
  have hEu : E u = ContinuousLinearMap.adjoint J g := by
    refine ext_inner_right ℝ fun φ => ?_
    rw [hE, IsCoercive.continuousLinearEquivOfBilin_apply, happ, hu φ,
      ContinuousLinearMap.adjoint_inner_left]
  rw [ContinuousLinearMap.comp_apply, ← hEu]
  exact E.symm_apply_apply u

lemma adjK (hC : 0 < C) (hcoer : ∀ u, C * ‖u‖ ^ 2 ≤ b u u + γ * ⟪J u, J u⟫_ℝ) (hμ : γ ≤ μ)
    (K : H →L[ℝ] H)
    (hK : ∀ g u, (∀ φ, b u φ + μ * ⟪J u, J φ⟫_ℝ = ⟪g, J φ⟫_ℝ) → K g = J u) :
    ∀ g v, (∀ φ, b.flip v φ + μ * ⟪J v, J φ⟫_ℝ = ⟪g, J φ⟫_ℝ) → adjoint K g = J v := by
  intro g v hv
  apply ext_inner_right ℝ
  intro h
  rw [adjoint_inner_left]
  obtain ⟨u, hu⟩ := exist J b hC hcoer hμ h
  rw [hK h u hu]
  have h1 := hv u
  have h2 := hu v
  rw [ContinuousLinearMap.flip_apply] at h1
  rw [real_inner_comm (J v) (J u)] at h2
  rw [real_inner_comm h (J v)]
  linarith

end

end FB92

open MeasureTheory

namespace HunterPDE.Elliptic.PDE92

open HunterPDE.Elliptic

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

/-- Pointwise integrand of `form`. -/
noncomputable def Gf (P : Coeffs n) (x : EuclideanSpace ℝ (Fin n)) (p q : Jet n) : ℝ :=
  ((∑ i, ∑ j, P.a i j x * (WithLp.ofLp p).2 i * (WithLp.ofLp q).2 j)
    - (∑ i, P.b i x * (WithLp.ofLp p).1 * (WithLp.ofLp q).2 i))
    + P.c x * (WithLp.ofLp p).1 * (WithLp.ofLp q).1

lemma form_eq (P : Coeffs n) (u v : H10 n Ω) :
    form P u v = ∫ x in Ω, Gf P x ((u : JetL2 n Ω) x) ((v : JetL2 n Ω) x) := rfl

lemma Gf_add_left (P : Coeffs n) (x : EuclideanSpace ℝ (Fin n)) (p p' q : Jet n) :
    Gf P x (p + p') q = Gf P x p q + Gf P x p' q := by
  simp only [Gf, WithLp.ofLp_add, Prod.fst_add, Prod.snd_add, PiLp.add_apply]
  simp only [mul_add, Finset.sum_add_distrib, add_mul]
  ring

lemma Gf_add_right (P : Coeffs n) (x : EuclideanSpace ℝ (Fin n)) (p q q' : Jet n) :
    Gf P x p (q + q') = Gf P x p q + Gf P x p q' := by
  simp only [Gf, WithLp.ofLp_add, Prod.fst_add, Prod.snd_add, PiLp.add_apply]
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  ring

lemma Gf_smul_left (P : Coeffs n) (x : EuclideanSpace ℝ (Fin n)) (c : ℝ) (p q : Jet n) :
    Gf P x (c • p) q = c * Gf P x p q := by
  simp only [Gf, WithLp.ofLp_smul, Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul]
  rw [mul_add, mul_sub]
  congr 1
  · congr 1
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
  · ring

lemma Gf_smul_right (P : Coeffs n) (x : EuclideanSpace ℝ (Fin n)) (c : ℝ) (p q : Jet n) :
    Gf P x p (c • q) = c * Gf P x p q := by
  simp only [Gf, WithLp.ofLp_smul, Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul]
  rw [mul_add, mul_sub]
  congr 1
  · congr 1
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
  · ring

lemma memLp_fst (U : JetL2 n Ω) :
    MemLp (fun x => (WithLp.ofLp (U x)).1) 2 (volume.restrict Ω) :=
  ContinuousLinearMap.comp_memLp (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))) U

lemma memLp_snd (U : JetL2 n Ω) (i : Fin n) :
    MemLp (fun x => (WithLp.ofLp (U x)).2 i) 2 (volume.restrict Ω) :=
  ContinuousLinearMap.comp_memLp
    ((EuclideanSpace.proj i).comp (WithLp.sndL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n)))) U

lemma int3 {f g h : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f ⊤ (volume.restrict Ω))
    (hg : MemLp g 2 (volume.restrict Ω)) (hh : MemLp h 2 (volume.restrict Ω)) :
    Integrable (fun x => f x * g x * h x) (volume.restrict Ω) := by
  have h1 : Integrable (g * h) (volume.restrict Ω) := hg.integrable_mul hh
  have h2 := h1.mul_of_top_right hf
  refine h2.congr (ae_of_all _ fun x => ?_)
  simp [mul_assoc]

lemma Gf_integrable (P : Coeffs n) (hP : P.Admissible Ω) (U V : JetL2 n Ω) :
    Integrable (fun x => Gf P x (U x) (V x)) (volume.restrict Ω) := by
  unfold Gf
  refine Integrable.add (Integrable.sub ?_ ?_) ?_
  · refine integrable_finsetSum _ fun i _ => ?_
    refine integrable_finsetSum _ fun j _ => ?_
    exact int3 (hP.1 i j) (memLp_snd U i) (memLp_snd V j)
  · refine integrable_finsetSum _ fun i _ => ?_
    exact int3 (hP.2.1 i) (memLp_fst U) (memLp_snd V i)
  · exact int3 hP.2.2.1 (memLp_fst U) (memLp_fst V)

lemma form_add_left (P : Coeffs n) (hP : P.Admissible Ω) (u u' v : H10 n Ω) :
    form P (u + u') v = form P u v + form P u' v := by
  rw [form_eq, form_eq, form_eq, Submodule.coe_add,
    ← integral_add (Gf_integrable P hP _ _) (Gf_integrable P hP _ _)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add (u : JetL2 n Ω) (u' : JetL2 n Ω)] with x hx
  rw [hx, Pi.add_apply, Gf_add_left]

lemma form_add_right (P : Coeffs n) (hP : P.Admissible Ω) (u v v' : H10 n Ω) :
    form P u (v + v') = form P u v + form P u v' := by
  rw [form_eq, form_eq, form_eq, Submodule.coe_add,
    ← integral_add (Gf_integrable P hP _ _) (Gf_integrable P hP _ _)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add (v : JetL2 n Ω) (v' : JetL2 n Ω)] with x hx
  rw [hx, Pi.add_apply, Gf_add_right]

lemma form_smul_left (P : Coeffs n) (c : ℝ) (u v : H10 n Ω) :
    form P (c • u) v = c * form P u v := by
  rw [form_eq, form_eq, Submodule.coe_smul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c (u : JetL2 n Ω)] with x hx
  rw [hx, Pi.smul_apply, Gf_smul_left]

lemma form_smul_right (P : Coeffs n) (c : ℝ) (u v : H10 n Ω) :
    form P u (c • v) = c * form P u v := by
  rw [form_eq, form_eq, Submodule.coe_smul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c (v : JetL2 n Ω)] with x hx
  rw [hx, Pi.smul_apply, Gf_smul_right]

/-- The inclusion into `L²(Ω)` as a continuous linear map. -/
noncomputable def T (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    H10 n Ω →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  ((WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).compLpL 2 (volume.restrict Ω)).comp
    (H10 n Ω).subtypeL

lemma l2inner_eq (u v : H10 n Ω) : l2inner u v = inner ℝ (T n Ω u) (T n Ω v) := by
  rw [L2.inner_def]
  unfold l2inner
  refine integral_congr_ae ?_
  have hu := ContinuousLinearMap.coeFn_compLp (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n)))
    (u : JetL2 n Ω)
  have hv := ContinuousLinearMap.coeFn_compLp (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n)))
    (v : JetL2 n Ω)
  filter_upwards [hu, hv] with x hx hy
  change val u x * val v x = inner ℝ
    ((WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).compLp (u : JetL2 n Ω) x)
    ((WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).compLp (v : JetL2 n Ω) x)
  rw [hx, hy]
  simp [val, mul_comm]


end HunterPDE.Elliptic.PDE92


namespace HunterPDE.Elliptic.PDE92

open HunterPDE.Elliptic

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

lemma toL2_eq (u : H10 n Ω) : toL2 u = T n Ω u := rfl

lemma l2pairing_eq (f : Lp ℝ 2 (volume.restrict Ω)) (φ : H10 n Ω) :
    l2pairing (f : EuclideanSpace ℝ (Fin n) → ℝ) φ = ⟪f, T n Ω φ⟫_ℝ := by
  rw [L2.inner_def]
  unfold l2pairing
  refine integral_congr_ae ?_
  have hv := ContinuousLinearMap.coeFn_compLp (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n)))
    (φ : JetL2 n Ω)
  filter_upwards [hv] with x hy
  change f x * val φ x = inner ℝ (f x)
    ((WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).compLp (φ : JetL2 n Ω) x)
  rw [hy]
  simp [val, mul_comm]

lemma formAdj_eq (P : Coeffs n) (hP : P.Admissible Ω) (u v : H10 n Ω) :
    formAdj P u v = form P v u := by
  have hsym : ∀ᵐ x ∂(volume.restrict Ω), ∀ i j, P.a i j x = P.a j i x := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j; exact hP.2.2.2 i j
  unfold formAdj form
  refine integral_congr_ae ?_
  filter_upwards [hsym] with x hx
  have h1 : (∑ i, ∑ j, P.a i j x * pd u i x * pd v j x) =
      ∑ i, ∑ j, P.a i j x * pd v i x * pd u j x := by
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hx i j]; ring
  have h2 : (∑ i, P.b i x * pd u i x * val v x) = ∑ i, P.b i x * val v x * pd u i x := by
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h1, h2]
  ring

/-- The bounded bilinear form `form P` as a continuous bilinear map. -/
noncomputable def bF (P : Coeffs n) (hP : P.Admissible Ω) (C₂ : ℝ)
    (hbd : ∀ u v : H10 n Ω, |form P u v| ≤ C₂ * ‖u‖ * ‖v‖) :
    H10 n Ω →L[ℝ] H10 n Ω →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ (fun u v => form P u v)
      (fun u u' v => form_add_left P hP u u' v)
      (fun c u v => by rw [form_smul_left P]; rfl)
      (fun u v v' => form_add_right P hP u v v')
      (fun c u v => by rw [form_smul_right P]; rfl)).mkContinuous₂ C₂
    (fun u v => by
      simp only [LinearMap.mk₂_apply, Real.norm_eq_abs]
      exact hbd u v)

lemma bF_apply (P : Coeffs n) (hP : P.Admissible Ω) (C₂ : ℝ)
    (hbd : ∀ u v : H10 n Ω, |form P u v| ≤ C₂ * ‖u‖ * ‖v‖) (u v : H10 n Ω) :
    bF P hP C₂ hbd u v = form P u v := rfl

lemma c_lower (P : Coeffs n) (hP : P.Admissible Ω) :
    ∀ᵐ x ∂(volume.restrict Ω), -(eLpNorm P.c ⊤ (volume.restrict Ω)).toReal ≤ P.c x := by
  have hlt : eLpNorm P.c ⊤ (volume.restrict Ω) ≠ ⊤ := hP.2.2.1.2.ne
  rw [eLpNorm_exponent_top] at hlt ⊢
  filter_upwards [ae_le_eLpNormEssSup (f := P.c) (μ := volume.restrict Ω)] with x hx
  have h1 : ‖P.c x‖ ≤ (eLpNormEssSup P.c (volume.restrict Ω)).toReal := by
    rw [← toReal_enorm]
    exact ENNReal.toReal_mono hlt hx
  rw [Real.norm_eq_abs] at h1
  have := neg_abs_le (P.c x)
  linarith

end HunterPDE.Elliptic.PDE92

namespace HunterPDE.Elliptic.RC6f

open HunterPDE.Elliptic

variable {n : ℕ}

set_option maxHeartbeats 2000000 in
/-- The leaf, given compactness of the embedding `H¹₀(Ω) ↪ L²(Ω)` for bounded `Ω`. -/
theorem main_of_rellich (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (P : Coeffs n) (hP : P.Admissible Ω) (γ : ℝ)
    (hγ : ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
      (∀ u : H10 n Ω, C₁ * ‖u‖ ^ 2 ≤ form P u u + γ * l2inner u u) ∧
      ∀ u v : H10 n Ω, |form P u v| ≤ C₂ * ‖u‖ * ‖v‖)
    (μ : ℝ) (hμ : γ ≤ μ)
    (hrel : Bornology.IsBounded Ω → IsCompactOperator (PDE92.T n Ω)) :
    ∃ K : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] Lp ℝ 2 (volume.restrict Ω),
      ⇑K = resolvent Ω P μ ∧ ⇑(ContinuousLinearMap.adjoint K) = resolventAdj Ω P μ ∧
      (Bornology.IsBounded Ω → IsCompactOperator K) := by
  have : CompleteSpace (H10 n Ω) := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  obtain ⟨C₁, hC₁, C₂, hC₂, hco, hbd⟩ := hγ
  obtain ⟨J, hJ⟩ : ∃ J, J = PDE92.T n Ω := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = PDE92.bF P hP C₂ hbd := ⟨_, rfl⟩
  have hbapp : ∀ u v, b u v = form P u v := fun u v => by rw [hb]; rfl
  have hcoer : ∀ u, C₁ * ‖u‖ ^ 2 ≤ b u u + γ * ⟪J u, J u⟫_ℝ := by
    intro u; rw [hbapp, hJ, ← PDE92.l2inner_eq]; exact hco u
  have hcoerF : ∀ u, C₁ * ‖u‖ ^ 2 ≤ b.flip u u + γ * ⟪J u, J u⟫_ℝ := by
    intro u; rw [ContinuousLinearMap.flip_apply]; exact hcoer u
  obtain ⟨S, hS⟩ := FB92.solK J b hC₁ hcoer hμ
  obtain ⟨K, hKdef⟩ : ∃ K : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] Lp ℝ 2 (volume.restrict Ω),
    K = J ∘L S := ⟨_, rfl⟩
  have hK : ∀ g u, (∀ φ, b u φ + μ * ⟪J u, J φ⟫_ℝ = ⟪g, J φ⟫_ℝ) → K g = J u := by
    intro g u hu
    rw [hKdef, ContinuousLinearMap.comp_apply, hS g u hu]
  refine ⟨K, ?_, ?_, ?_⟩
  · funext g
    obtain ⟨u, hu⟩ := FB92.exist J b hC₁ hcoer hμ g
    have hex : ∃ u : H10 n Ω,
        IsWeakSolution (form P) μ (l2pairing (g : EuclideanSpace ℝ (Fin n) → ℝ)) u := by
      refine ⟨u, fun φ => ?_⟩
      rw [PDE92.l2inner_eq, PDE92.l2pairing_eq, ← hbapp, ← hJ]
      exact hu φ
    unfold HunterPDE.Elliptic.resolvent
    rw [dif_pos hex]
    have hc := hex.choose_spec
    rw [hK g hex.choose (fun φ => by
      have := hc φ
      rw [PDE92.l2inner_eq, PDE92.l2pairing_eq, ← hbapp, ← hJ] at this
      exact this)]
    rw [hJ]; rfl
  · funext g
    obtain ⟨u, hu⟩ := FB92.exist J b.flip hC₁ hcoerF hμ g
    have hex : ∃ u : H10 n Ω,
        IsWeakSolution (formAdj P) μ (l2pairing (g : EuclideanSpace ℝ (Fin n) → ℝ)) u := by
      refine ⟨u, fun φ => ?_⟩
      have := hu φ
      rw [ContinuousLinearMap.flip_apply, hbapp] at this
      rw [PDE92.l2inner_eq, PDE92.l2pairing_eq, PDE92.formAdj_eq P hP, ← hJ]
      exact this
    unfold HunterPDE.Elliptic.resolventAdj
    rw [dif_pos hex]
    have hc := hex.choose_spec
    rw [FB92.adjK J b hC₁ hcoer hμ K hK g hex.choose (fun φ => by
      have := hc φ
      rw [PDE92.l2inner_eq, PDE92.l2pairing_eq, PDE92.formAdj_eq P hP, ← hJ] at this
      rw [ContinuousLinearMap.flip_apply, hbapp]
      exact this)]
    rw [hJ]; rfl
  · intro hΩb
    rw [hKdef]
    exact (hJ ▸ hrel hΩb).comp_clm _

end HunterPDE.Elliptic.RC6f

open HunterPDE.Elliptic MeasureTheory in
theorem solution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (P : Coeffs n) (hP : P.Admissible Ω) (γ : ℝ)
    (hγ : ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
      (∀ u : H10 n Ω, C₁ * ‖u‖ ^ 2 ≤ form P u u + γ * l2inner u u) ∧
      ∀ u v : H10 n Ω, |form P u v| ≤ C₂ * ‖u‖ * ‖v‖)
    (μ : ℝ) (hμ : γ ≤ μ) :
    ∃ K : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] Lp ℝ 2 (volume.restrict Ω),
      ⇑K = resolvent Ω P μ ∧ ⇑(ContinuousLinearMap.adjoint K) = resolventAdj Ω P μ ∧
      (Bornology.IsBounded Ω → IsCompactOperator K) := by
  exact HunterPDE.Elliptic.RC6f.main_of_rellich Ω P hP γ hγ μ hμ
    (fun hb => HunterPDE.Elliptic.RC6f.rellich Ω hΩ hb)
