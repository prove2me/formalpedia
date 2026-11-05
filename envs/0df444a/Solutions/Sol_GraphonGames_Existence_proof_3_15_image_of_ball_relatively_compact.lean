-- Prove2me | solution 1 for GraphonGames.Existence.proof_3_15_image_of_ball_relatively_compact
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T19:53:26.013913+00:00
-- url     : https://prove2.me/submissions/c4bbfa1d-de9b-4ec0-99cf-b2b9f33e0dc6

import Mathlib
import Definitions.Def_GraphonGames_Existence_Setting

open MeasureTheory
open scoped ENNReal

namespace GGCompactAux
open GraphonGames.Existence

noncomputable section

lemma l2_sq {A : Type*} [MeasurableSpace A] (μ : Measure A) (f : A → ℝ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] using
    (eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := f) (p := 2) (by norm_num))

/-- Hilbert–Schmidt bound `‖W_k g‖ ≤ ‖k‖_{L²(I×I)} ‖g‖`. -/
lemma kernel_bound (k : I → I → ℝ) (hkm : Measurable (Function.uncurry k)) (g : I → ℝ)
    (hg : MemLp g 2 volume) :
    eLpNorm (graphonApply k g) 2 volume ≤
      eLpNorm (Function.uncurry k) 2 (volume : Measure (I × I)) * eLpNorm g 2 volume := by
  have hrow (x : I) : Measurable (k x) :=
    hkm.comp (measurable_const.prodMk measurable_id)
  have hpoint (x : I) : ‖graphonApply k g x‖ₑ ≤
      eLpNorm (k x) 2 volume * eLpNorm g 2 volume := by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume
      (Real.holderConjugate_iff.mpr (by norm_num : (1 : ℝ) < 2 ∧ (2 : ℝ)⁻¹ + 2⁻¹ = 1))
      (hrow x).enorm.aemeasurable hg.1.enorm
    simpa only [Pi.mul_apply, enorm_mul,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞), ENNReal.toReal_ofNat] using h
  have hsq : eLpNorm (graphonApply k g) 2 volume ^ 2 ≤
      (eLpNorm (Function.uncurry k) 2 (volume : Measure (I × I)) * eLpNorm g 2 volume) ^ 2 := by
    rw [l2_sq]
    calc
      (∫⁻ x, ‖graphonApply k g x‖ₑ ^ 2) ≤
          ∫⁻ x, (eLpNorm (k x) 2 volume * eLpNorm g 2 volume) ^ 2 :=
        lintegral_mono fun x => ENNReal.pow_le_pow_left (hpoint x)
      _ = (∫⁻ x, ∫⁻ y, ‖k x y‖ₑ ^ 2) * eLpNorm g 2 volume ^ 2 := by
        simp_rw [mul_pow, l2_sq (volume : Measure I) (k _)]
        exact lintegral_mul_const _ (hkm.enorm.pow_const 2).lintegral_prod_right
      _ = (eLpNorm (Function.uncurry k) 2 (volume : Measure (I × I)) *
          eLpNorm g 2 volume) ^ 2 := by
        rw [mul_pow, l2_sq (volume : Measure (I × I)) (Function.uncurry k)]
        congr 1
        exact (lintegral_prod _ (hkm.enorm.pow_const 2).aemeasurable).symm
  apply (ENNReal.rpow_le_rpow_iff (z := 2) (by norm_num)).mp
  simpa only [ENNReal.rpow_two] using hsq

lemma kernel_memLp (k : I → I → ℝ) (hkm : Measurable (Function.uncurry k))
    (hk : MemLp (Function.uncurry k) 2 volume) (g : I → ℝ) (hg : MemLp g 2 volume) :
    MemLp (graphonApply k g) 2 volume := by
  refine ⟨?_, (kernel_bound k hkm g hg).trans_lt (ENNReal.mul_lt_top hk.2 hg.2)⟩
  exact (hkm.aestronglyMeasurable.mul (hg.comp_snd (volume : Measure I)).1).integral_prod_right'

lemma ae_integrable (k : I → I → ℝ) (hk : MemLp (Function.uncurry k) 2 volume) (g : I → ℝ)
    (hg : MemLp g 2 volume) : ∀ᵐ x ∂(volume : Measure I), Integrable (fun y => k x y * g y) volume :=
  (hk.integrable_mul (hg.comp_snd (volume : Measure I))).prod_right_ae

lemma apply_sub (k1 k2 : I → I → ℝ) (hk1 : MemLp (Function.uncurry k1) 2 volume)
    (hk2 : MemLp (Function.uncurry k2) 2 volume) (g : I → ℝ) (hg : MemLp g 2 volume) :
    graphonApply k1 g - graphonApply k2 g =ᵐ[volume] graphonApply (fun x y => k1 x y - k2 x y) g := by
  filter_upwards [ae_integrable k1 hk1 g hg, ae_integrable k2 hk2 g hg] with x h1 h2
  simp only [Pi.sub_apply, graphonApply, sub_mul]
  exact (integral_sub h1 h2).symm

lemma apply_add (k1 k2 : I → I → ℝ) (hk1 : MemLp (Function.uncurry k1) 2 volume)
    (hk2 : MemLp (Function.uncurry k2) 2 volume) (g : I → ℝ) (hg : MemLp g 2 volume) :
    graphonApply (fun x y => k1 x y + k2 x y) g =ᵐ[volume] graphonApply k1 g + graphonApply k2 g := by
  filter_upwards [ae_integrable k1 hk1 g hg, ae_integrable k2 hk2 g hg] with x h1 h2
  simp only [Pi.add_apply, graphonApply, add_mul]
  exact integral_add h1 h2

/-- kernel of a continuous function on `I × I` -/
def kp (p : C(I × I, ℝ)) : I → I → ℝ := fun x y => p (x, y)

lemma kp_meas (p : C(I × I, ℝ)) : Measurable (Function.uncurry (kp p)) :=
  p.continuous.measurable

lemma kp_memLp (p : C(I × I, ℝ)) : MemLp (Function.uncurry (kp p)) 2 volume :=
  MemLp.of_bound (kp_meas p).aestronglyMeasurable ‖p‖
    (Filter.Eventually.of_forall fun q => p.norm_coe_le_norm q)

abbrev E := Lp ℝ 2 (volume : Measure I)

def Sset (χ : ℝ) (k : I → I → ℝ) : Set E :=
  {F : E | ∃ g : I → ℝ, MemLp g 2 volume ∧ eLpNorm g 2 volume ≤ ENNReal.ofReal χ ∧
    (F : I → ℝ) =ᵐ[volume] graphonApply k g}

lemma cont_memLp (u : C(I, ℝ)) : MemLp (u : I → ℝ) 2 volume :=
  MemLp.of_bound u.continuous.aestronglyMeasurable ‖u‖
    (Filter.Eventually.of_forall fun q => u.norm_coe_le_norm q)

lemma tb_gen (χ : ℝ) (u v : C(I, ℝ)) (p : C(I × I, ℝ)) (hp : ∀ q, p q = u q.1 * v q.2) :
    TotallyBounded (Sset χ (kp p)) := by
  set U : E := (cont_memLp u).toLp u
  set M : ℝ := ‖v‖ * max χ 0
  have hK : IsCompact ((fun t : ℝ => t • U) '' Set.Icc (-M) M) :=
    isCompact_Icc.image (continuous_id.smul continuous_const)
  refine hK.totallyBounded.subset ?_
  rintro F ⟨g, hg, hgn, hF⟩
  set c : ℝ := ∫ y, v y * g y
  have hcb : |c| ≤ M := by
    have h1 : ‖c‖ₑ ≤ ‖v‖ₑ * ENNReal.ofReal χ := by
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      calc ∫⁻ y, ‖v y * g y‖ₑ ≤ ∫⁻ y, ‖v‖ₑ * ‖g y‖ₑ := by
            refine lintegral_mono fun y => ?_
            rw [enorm_mul]
            rw [← ofReal_norm (v y), ← ofReal_norm v]
            exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (v.norm_coe_le_norm y)) _
        _ = ‖v‖ₑ * eLpNorm g 1 volume := by
            rw [lintegral_const_mul' _ _ enorm_ne_top, eLpNorm_one_eq_lintegral_enorm]
        _ ≤ ‖v‖ₑ * eLpNorm g 2 volume := by
            gcongr
            exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hg.1
        _ ≤ ‖v‖ₑ * ENNReal.ofReal χ := by gcongr
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top) h1
    rw [toReal_enorm, ENNReal.toReal_mul, toReal_enorm, ENNReal.toReal_ofReal'] at h2
    simpa [M, Real.norm_eq_abs] using h2
  refine ⟨c, ⟨neg_le_of_abs_le hcb, le_of_abs_le hcb⟩, ?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul c U, (cont_memLp u).coeFn_toLp, hF] with x h1 h2 h3
  rw [h1, Pi.smul_apply, h2, h3]
  simp only [graphonApply, kp, hp, smul_eq_mul]
  simp_rw [mul_assoc]
  rw [integral_const_mul, mul_comm]

lemma tb_zero (χ : ℝ) : TotallyBounded (Sset χ (kp 0)) := by
  refine (Set.finite_singleton (0 : E)).totallyBounded.subset ?_
  rintro F ⟨g, -, -, hF⟩
  rw [Set.mem_singleton_iff]
  apply Lp.ext
  filter_upwards [hF, Lp.coeFn_zero ℝ 2 (volume : Measure I)] with x h1 h2
  rw [h1, h2]
  simp [graphonApply, kp]

lemma tb_add (χ : ℝ) (p q : C(I × I, ℝ)) (hp : TotallyBounded (Sset χ (kp p)))
    (hq : TotallyBounded (Sset χ (kp q))) : TotallyBounded (Sset χ (kp (p + q))) := by
  have hcp := hp.closure.isCompact_of_isClosed isClosed_closure
  have hcq := hq.closure.isCompact_of_isClosed isClosed_closure
  refine ((hcp.prod hcq).image continuous_add).totallyBounded.subset ?_
  rintro F ⟨g, hg, hgn, hF⟩
  have mp := kernel_memLp (kp p) (kp_meas p) (kp_memLp p) g hg
  have mq := kernel_memLp (kp q) (kp_meas q) (kp_memLp q) g hg
  refine ⟨(mp.toLp _, mq.toLp _), ⟨subset_closure ⟨g, hg, hgn, mp.coeFn_toLp⟩,
    subset_closure ⟨g, hg, hgn, mq.coeFn_toLp⟩⟩, ?_⟩
  apply Lp.ext
  have hadd := apply_add (kp p) (kp q) (kp_memLp p) (kp_memLp q) g hg
  filter_upwards [Lp.coeFn_add (mp.toLp _) (mq.toLp _), mp.coeFn_toLp, mq.coeFn_toLp, hF, hadd]
    with x h1 h2 h3 h4 h5
  show ((mp.toLp _ + mq.toLp _ : E) : I → ℝ) x = _
  rw [h1, Pi.add_apply, h2, h3, h4, ← Pi.add_apply, ← h5]
  rfl

lemma tb_smul (χ : ℝ) (c : ℝ) (p : C(I × I, ℝ)) (hp : TotallyBounded (Sset χ (kp p))) :
    TotallyBounded (Sset χ (kp (c • p))) := by
  refine (hp.image (uniformContinuous_id.const_smul c)).subset ?_
  rintro F ⟨g, hg, hgn, hF⟩
  have mp := kernel_memLp (kp p) (kp_meas p) (kp_memLp p) g hg
  refine ⟨mp.toLp _, ⟨g, hg, hgn, mp.coeFn_toLp⟩, ?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul c (mp.toLp _), mp.coeFn_toLp, hF] with x h1 h2 h3
  show ((c • mp.toLp _ : E) : I → ℝ) x = _
  rw [h1, Pi.smul_apply, h2, h3]
  simp only [graphonApply, kp, ContinuousMap.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc]
  rw [integral_const_mul]

/-- products `u(x) v(y)` -/
def S0 : Set C(I × I, ℝ) := {p | ∃ u v : C(I, ℝ), ∀ q, p q = u q.1 * v q.2}

lemma tb_span (χ : ℝ) (p : C(I × I, ℝ)) (hp : p ∈ Submodule.span ℝ S0) :
    TotallyBounded (Sset χ (kp p)) := by
  induction hp using Submodule.span_induction with
  | mem x hx => obtain ⟨u, v, h⟩ := hx; exact tb_gen χ u v x h
  | zero => exact tb_zero χ
  | add x y _ _ hx hy => exact tb_add χ x y hx hy
  | smul a x _ hx => exact tb_smul χ a x hx

def S0mon : Submonoid C(I × I, ℝ) where
  carrier := S0
  mul_mem' := by
    rintro a b ⟨u, v, ha⟩ ⟨u', v', hb⟩
    exact ⟨u * u', v * v', fun q => by simp [ha, hb]; ring⟩
  one_mem' := ⟨1, 1, fun q => by simp⟩

def fstC : C(I × I, ℝ) := ⟨fun q => (q.1 : ℝ), by fun_prop⟩
def sndC : C(I × I, ℝ) := ⟨fun q => (q.2 : ℝ), by fun_prop⟩

lemma adjoin_le_span (p : C(I × I, ℝ)) (hp : p ∈ Algebra.adjoin ℝ ({fstC, sndC} : Set C(I × I, ℝ))) :
    p ∈ Submodule.span ℝ S0 := by
  have h1 : p ∈ Subalgebra.toSubmodule (Algebra.adjoin ℝ ({fstC, sndC} : Set C(I × I, ℝ))) := hp
  rw [Algebra.adjoin_eq_span] at h1
  refine Submodule.span_mono ?_ h1
  have : Submonoid.closure ({fstC, sndC} : Set C(I × I, ℝ)) ≤ S0mon := by
    rw [Submonoid.closure_le]
    intro f hf
    rcases hf with rfl | rfl
    · exact ⟨⟨fun x => (x : ℝ), by fun_prop⟩, 1, fun q => by simp [fstC]⟩
    · exact ⟨1, ⟨fun x => (x : ℝ), by fun_prop⟩, fun q => by simp [sndC]⟩
  exact this

lemma density (w : I → I → ℝ) (hw : IsGraphon w) (δ : ℝ) (hδ : 0 < δ) :
    ∃ p ∈ Submodule.span ℝ S0,
      eLpNorm (Function.uncurry w - Function.uncurry (kp p)) 2 volume ≤ ENNReal.ofReal δ := by
  obtain ⟨g, hg, -⟩ := hw.2.2.exists_boundedContinuous_eLpNorm_sub_le (by norm_num)
    (ENNReal.ofReal_pos.mpr (half_pos hδ)).ne'
  set A := Algebra.adjoin ℝ ({fstC, sndC} : Set C(I × I, ℝ))
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    by_cases h : x.1 = y.1
    · have h2 : x.2 ≠ y.2 := fun h2 => hxy (Prod.ext h h2)
      refine ⟨_, ⟨sndC, Algebra.subset_adjoin (by simp), rfl⟩, ?_⟩
      simpa [sndC] using fun h' => h2 (Subtype.ext h')
    · refine ⟨_, ⟨fstC, Algebra.subset_adjoin (by simp), rfl⟩, ?_⟩
      simpa [fstC] using fun h' => h (Subtype.ext h')
  have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hmem : g.toContinuousMap ∈ closure (A : Set C(I × I, ℝ)) := by
    rw [← Subalgebra.topologicalClosure_coe, htop]; trivial
  obtain ⟨p, hpA, hdist⟩ := Metric.mem_closure_iff.mp hmem (δ / 2) (half_pos hδ)
  refine ⟨p, adjoin_le_span p hpA, ?_⟩
  have hgp : eLpNorm (fun q => g q - p q) 2 (volume : Measure (I × I)) ≤ ENNReal.ofReal (δ / 2) := by
    refine (eLpNorm_le_of_ae_bound (C := δ / 2) (Filter.Eventually.of_forall fun q => ?_)).trans ?_
    · have := ContinuousMap.norm_coe_le_norm (g.toContinuousMap - p) q
      rw [dist_eq_norm] at hdist
      simpa using this.trans hdist.le
    · simp
  have hm1 : AEStronglyMeasurable (Function.uncurry w - fun q => g q) volume :=
    hw.2.2.1.sub g.continuous.aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun q => g q - p q) (volume : Measure (I × I)) :=
    (g.continuous.sub p.continuous).aestronglyMeasurable
  have heq : Function.uncurry w - Function.uncurry (kp p) =
      (Function.uncurry w - fun q => g q) + (fun q => g q - p q) := by
    funext q; simp only [Pi.add_apply, Pi.sub_apply]
    show _ - p (q.1, q.2) = _
    ring
  rw [heq]
  calc eLpNorm ((Function.uncurry w - fun q => g q) + (fun q => g q - p q)) 2 volume
      ≤ eLpNorm (Function.uncurry w - fun q => g q) 2 volume +
          eLpNorm (fun q => g q - p q) 2 volume := eLpNorm_add_le hm1 hm2 (by norm_num)
    _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add hg hgp
    _ = ENNReal.ofReal δ := by rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf

end

end GGCompactAux

open GGCompactAux GraphonGames.Existence

theorem solution (w : I → I → ℝ) (hw : IsGraphon w) (χ : ℝ) :
    IsCompact (closure {F : Lp ℝ 2 (volume : Measure I) | ∃ g : I → ℝ, MemLp g 2 volume ∧
      eLpNorm g 2 volume ≤ ENNReal.ofReal χ ∧ (F : I → ℝ) =ᵐ[volume] graphonApply w g}) := by
  change IsCompact (closure (Sset χ w))
  refine TotallyBounded.isCompact_of_isClosed (TotallyBounded.closure ?_) isClosed_closure
  rw [Metric.totallyBounded_iff]
  intro ε hε
  set δ := ε / (2 * (|χ| + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨p, hp, hwp⟩ := density w hw δ hδ
  obtain ⟨t, htfin, hcover⟩ := Metric.totallyBounded_iff.mp (tb_span χ p hp) (ε / 2) (half_pos hε)
  refine ⟨t, htfin, ?_⟩
  rintro F ⟨g, hg, hgn, hF⟩
  have mp := kernel_memLp (kp p) (kp_meas p) (kp_memLp p) g hg
  have hF' : mp.toLp _ ∈ Sset χ (kp p) := ⟨g, hg, hgn, mp.coeFn_toLp⟩
  have := hcover hF'
  simp only [Set.mem_iUnion, Metric.mem_ball] at this ⊢
  obtain ⟨y, hy, hdy⟩ := this
  refine ⟨y, hy, ?_⟩
  -- distance between `F` and the approximant
  have hkm : Measurable (Function.uncurry (fun x y => w x y - kp p x y)) :=
    hw.1.sub (kp_meas p)
  have hdF : dist F (mp.toLp _) ≤ δ * |χ| := by
    rw [Lp.dist_def]
    have hcongr : eLpNorm (⇑F - ⇑(mp.toLp (graphonApply (kp p) g))) 2 volume =
        eLpNorm (graphonApply (fun x y => w x y - kp p x y) g) 2 volume := by
      apply eLpNorm_congr_ae
      filter_upwards [hF, mp.coeFn_toLp, apply_sub w (kp p) hw.2.2 (kp_memLp p) g hg]
        with x h1 h2 h3
      rw [Pi.sub_apply, h1, h2, ← h3]
      rfl
    rw [hcongr]
    have hb := kernel_bound _ hkm g hg
    have hb2 : eLpNorm (graphonApply (fun x y => w x y - kp p x y) g) 2 volume ≤
        ENNReal.ofReal δ * ENNReal.ofReal χ := by
      refine hb.trans (mul_le_mul' ?_ hgn)
      exact le_of_eq_of_le (by rfl) hwp
    have hb3 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hb2
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le, ENNReal.toReal_ofReal'] at hb3
    refine hb3.trans ?_
    gcongr
    exact max_le (le_abs_self χ) (abs_nonneg χ)
  have hsmall : δ * |χ| < ε / 2 := by
    have h2 : δ * (2 * (|χ| + 1)) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith [abs_nonneg χ]
  calc dist F y ≤ dist F (mp.toLp _) + dist (mp.toLp _) y := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring
