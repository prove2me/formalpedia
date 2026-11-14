-- Prove2me | solution 1 for HighDimProb.DvoretzkyMilman.dvoretzky_milman
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T03:20:22.010712+00:00
-- url     : https://prove2.me/submissions/8691d3ab-025c-48eb-b51e-24de0750ec7d

import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_HighDimProb_DvoretzkyMilman_ExpSup
import Definitions.Def_HighDimProb_DvoretzkyMilman_GaussianWidth
import Definitions.Def_HighDimProb_DvoretzkyMilman_StableDimension
import Definitions.Def_HighDimProb_DvoretzkyMilman_IsGaussianMatrix
import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_sudakov_fernique
import Theorems.Thm_GaussianMatrix_gordon_minimax
import Theorems.Thm_GaussianMatrix_gaussian_concentration

open MeasureTheory ProbabilityTheory GaussianMatrix HighDimProb.DvoretzkyMilman
open scoped Matrix RealInnerProductSpace

namespace DvoretzkyMilmanProof

/-! ### Part 1: Euclidean action of a matrix and Frobenius Lipschitz estimates -/

noncomputable def dmPhi {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm (M.mulVec x)

private lemma dmPhi_apply {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    dmPhi M x i = ∑ j : Fin n, M i j * x j := by
  simp [dmPhi, Matrix.mulVec, dotProduct]

private lemma dmPhi_zero_right {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    dmPhi M 0 = 0 := by
  ext i
  simp [dmPhi_apply]

private lemma dmPhi_sub_left {m n : ℕ} (M₁ M₂ : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    dmPhi (M₁ - M₂) x = dmPhi M₁ x - dmPhi M₂ x := by
  ext i
  simp [dmPhi_apply, sub_mul, Finset.sum_sub_distrib]

private lemma dmPhi_sub_right {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    dmPhi M (x - y) = dmPhi M x - dmPhi M y := by
  ext i
  simp [dmPhi_apply, mul_sub, Finset.sum_sub_distrib]

private lemma dm_norm_sq {κ : Type*} [Fintype κ] (u : EuclideanSpace ℝ κ) :
    ‖u‖ ^ 2 = ∑ j, u j ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma dm_norm_eq_sqrt {κ : Type*} [Fintype κ] (u : EuclideanSpace ℝ κ) :
    ‖u‖ = Real.sqrt (∑ j, u j ^ 2) := by
  rw [← dm_norm_sq, Real.sqrt_sq (norm_nonneg _)]

private lemma dm_inner_dmPhi {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (u : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) :
    ⟪u, dmPhi M x⟫ = ∑ i : Fin m, ∑ j : Fin n, u i * x j * M i j := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, dmPhi_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma dm_frobSq_nonneg {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ frobSq M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma dm_norm_dmPhi_le {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖dmPhi M x‖ ≤ frobNorm M * ‖x‖ := by
  have hsq : ‖dmPhi M x‖ ^ 2 ≤ frobSq M * ‖x‖ ^ 2 := by
    rw [dm_norm_sq, dm_norm_sq]
    unfold frobSq
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [dmPhi_apply]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => M i j) (fun j => x j)
  rw [frobNorm, ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (dm_frobSq_nonneg M),
    dm_norm_eq_sqrt (dmPhi M x), ← dm_norm_sq]
  exact Real.sqrt_le_sqrt hsq

private lemma dm_continuous_dmPhi_right {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    Continuous (dmPhi M) := by
  unfold dmPhi
  refine Continuous.comp (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous ?_
  refine continuous_pi fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

private lemma dm_continuous_frobNorm (p m : ℕ) :
    Continuous (fun X : Fin p → Fin m → ℝ => frobNorm (Matrix.of X)) := by
  unfold frobNorm frobSq
  simp only [Matrix.of_apply]
  fun_prop

private lemma dm_continuous_of_lip {p m : ℕ} (h : (Fin p → Fin m → ℝ) → ℝ) (L : ℝ)
    (hLip : ∀ X Y, |h X - h Y| ≤ L * frobNorm (Matrix.of X - Matrix.of Y)) :
    Continuous h := by
  rw [continuous_iff_continuousAt]
  intro X₀
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hc : Continuous (fun Y : Fin p → Fin m → ℝ => L * frobNorm (Matrix.of (Y - X₀))) :=
    continuous_const.mul ((dm_continuous_frobNorm p m).comp (continuous_id.sub continuous_const))
  have h0 : Filter.Tendsto (fun Y : Fin p → Fin m → ℝ => L * frobNorm (Matrix.of (Y - X₀)))
      (nhds X₀) (nhds 0) := by
    have := hc.tendsto X₀
    simpa [frobNorm, frobSq] using this
  refine squeeze_zero (fun _ => dist_nonneg) (fun Y => ?_) h0
  rw [Real.dist_eq]
  have := hLip Y X₀
  simpa [Matrix.of_sub_of] using this

private lemma dm_sup'_lip {ι α : Type*} (S : Finset ι) (hS : S.Nonempty)
    (f : ι → α → ℝ) (x y : α) {K : ℝ} (hK : ∀ i ∈ S, |f i x - f i y| ≤ K) :
    |(S.sup' hS fun i => f i x) - (S.sup' hS fun i => f i y)| ≤ K := by
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add']
    refine Finset.sup'_le hS _ fun i hi => ?_
    have hiK := (abs_sub_le_iff.1 (hK i hi)).1
    have hiy : f i y ≤ S.sup' hS fun j => f j y := Finset.le_sup' (fun j => f j y) hi
    linarith
  · rw [sub_le_iff_le_add']
    refine Finset.sup'_le hS _ fun i hi => ?_
    have hiK := (abs_sub_le_iff.1 (hK i hi)).2
    have hix : f i x ≤ S.sup' hS fun j => f j x := Finset.le_sup' (fun j => f j x) hi
    linarith

private lemma dm_iSup_lip {ι α : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → α → ℝ) (x y : α) (K : ℝ) (hK : ∀ i, |f i x - f i y| ≤ K) :
    |(⨆ i, f i x) - (⨆ i, f i y)| ≤ K := by
  have hbx : BddAbove (Set.range fun i => f i x) := (Set.finite_range _).bddAbove
  have hby : BddAbove (Set.range fun i => f i y) := (Set.finite_range _).bddAbove
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add']
    refine ciSup_le fun i => ?_
    have hiK := (abs_sub_le_iff.1 (hK i)).1
    have hiy : f i y ≤ ⨆ j, f j y := le_ciSup hby i
    linarith
  · rw [sub_le_iff_le_add']
    refine ciSup_le fun i => ?_
    have hiK := (abs_sub_le_iff.1 (hK i)).2
    have hix : f i x ≤ ⨆ j, f j x := le_ciSup hbx i
    linarith

private lemma dm_iInf_lip {ι α : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → α → ℝ) (x y : α) (K : ℝ) (hK : ∀ i, |f i x - f i y| ≤ K) :
    |(⨅ i, f i x) - (⨅ i, f i y)| ≤ K := by
  have hbx : BddBelow (Set.range fun i => f i x) := (Set.finite_range _).bddBelow
  have hby : BddBelow (Set.range fun i => f i y) := (Set.finite_range _).bddBelow
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_comm]
    refine le_ciInf fun i => ?_
    have hiK := (abs_sub_le_iff.1 (hK i)).1
    have hix : (⨅ j, f j x) ≤ f i x := ciInf_le hbx i
    linarith
  · rw [sub_le_comm]
    refine le_ciInf fun i => ?_
    have hiK := (abs_sub_le_iff.1 (hK i)).2
    have hiy : (⨅ j, f j y) ≤ f i y := ciInf_le hby i
    linarith

/-! ### Part 2: Gaussian matrix linear forms, moments, and pushforward law -/

private lemma dm_hasGaussianLaw_pi (κ : Type*) [Fintype κ] :
    HasGaussianLaw (fun x : κ → ℝ => x) (Measure.pi fun _ : κ => gaussianReal 0 1) := by
  exact iIndepFun.hasGaussianLaw (P := Measure.pi fun _ : κ => gaussianReal 0 1)
    (X := fun k (x : κ → ℝ) => x k) (fun k => ⟨by
      have := (measurePreserving_eval (fun _ : κ => gaussianReal (0 : ℝ) 1) k).map_eq
      rw [this]; infer_instance⟩)
    (iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id))

private lemma dm_hasGaussianLaw_id (p m : ℕ) :
    HasGaussianLaw (fun G : Fin p → Fin m → ℝ => G) (gaussianMatrix p m) := by
  exact iIndepFun.hasGaussianLaw (P := gaussianMatrix p m)
    (X := fun i (G : Fin p → Fin m → ℝ) => G i) (fun i => ⟨by
      have := (measurePreserving_eval
        (fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) i).map_eq
      unfold gaussianMatrix
      rw [this]
      have := (dm_hasGaussianLaw_pi (Fin m)).isGaussian_map
      rwa [Measure.map_id'] at this⟩)
    (iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id))

private lemma dm_measurePreserving_coord {p m : ℕ} (a : Fin p) (b : Fin m) :
    MeasurePreserving (fun G : Fin p → Fin m → ℝ => G a b) (gaussianMatrix p m)
      (gaussianReal 0 1) :=
  (measurePreserving_eval (fun _ : Fin m => gaussianReal 0 1) b).comp
    (measurePreserving_eval (fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal 0 1) a)

private lemma dm_memLp_coord {p m : ℕ} (a : Fin p) (b : Fin m) (q : ENNReal) (hq : q ≠ ⊤) :
    MemLp (fun G : Fin p → Fin m → ℝ => G a b) q (gaussianMatrix p m) :=
  (memLp_id_gaussianReal' q hq).comp_measurePreserving (dm_measurePreserving_coord a b)

private lemma dm_integral_comp_coord {p m : ℕ} (a : Fin p) (b : Fin m) (f : ℝ → ℝ)
    (hf : Measurable f) :
    ∫ G, f (G a b) ∂(gaussianMatrix p m) = ∫ x, f x ∂(gaussianReal 0 1) := by
  rw [← (dm_measurePreserving_coord a b).map_eq, integral_map]
  · exact (dm_measurePreserving_coord a b).measurable.aemeasurable
  · exact hf.aestronglyMeasurable

private lemma dm_integral_coord {p m : ℕ} (a : Fin p) (b : Fin m) :
    ∫ G, G a b ∂(gaussianMatrix p m) = 0 := by
  have := dm_integral_comp_coord a b (fun x => x) measurable_id
  simpa [integral_id_gaussianReal] using this

private lemma dm_integral_coord_sq {p m : ℕ} (a : Fin p) (b : Fin m) :
    ∫ G, G a b ^ 2 ∂(gaussianMatrix p m) = 1 := by
  rw [dm_integral_comp_coord a b (fun x => x ^ 2) (by fun_prop)]
  have h := variance_eq_sub (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp))
  rw [variance_id_gaussianReal] at h
  simp [integral_id_gaussianReal] at h
  exact h.symm

private lemma dm_integral_coord_mul {p m : ℕ} (a c : Fin p) (b d : Fin m) :
    ∫ G, G a b * G c d ∂(gaussianMatrix p m) = if a = c ∧ b = d then 1 else 0 := by
  by_cases hac : a = c
  · subst hac
    by_cases hbd : b = d
    · subst hbd
      simpa [← pow_two] using dm_integral_coord_sq a b
    · simp only [hbd, and_false, if_false]
      have hrow := measurePreserving_eval
        (fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) a
      have h1 : ∫ G, G a b * G a d ∂(gaussianMatrix p m)
          = ∫ x, x b * x d ∂(Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) := by
        have := integral_map (μ := gaussianMatrix p m) hrow.measurable.aemeasurable
          (f := fun x : Fin m → ℝ => x b * x d) (by fun_prop)
        unfold gaussianMatrix at this ⊢
        rw [hrow.map_eq] at this
        exact this.symm
      rw [h1]
      have hind : iIndepFun (fun (i : Fin m) (ω : Fin m → ℝ) => ω i)
          (Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) :=
        iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id)
      rw [(hind.indepFun hbd).integral_fun_mul_eq_mul_integral
        (measurable_pi_apply b).aestronglyMeasurable (measurable_pi_apply d).aestronglyMeasurable]
      have h0 : ∫ x, x b ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) = 0 := by
        have hb := measurePreserving_eval (fun _ : Fin m => gaussianReal (0 : ℝ) 1) b
        have := integral_map (μ := Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1)
          hb.measurable.aemeasurable (f := fun x : ℝ => x) (by fun_prop)
        rw [hb.map_eq, integral_id_gaussianReal] at this
        exact this.symm
      simp [h0]
  · simp only [hac, false_and, if_false]
    have hind : iIndepFun (fun (i : Fin p) (ω : Fin p → Fin m → ℝ) => ω i)
        (gaussianMatrix p m) :=
      iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id)
    have h2 := (hind.indepFun hac).comp (measurable_pi_apply b) (measurable_pi_apply d)
    have := h2.integral_fun_mul_eq_mul_integral
      (by
        have : Measurable (fun ω : Fin p → Fin m → ℝ => ω a b) := by fun_prop
        exact this.aestronglyMeasurable)
      (by
        have : Measurable (fun ω : Fin p → Fin m → ℝ => ω c d) := by fun_prop
        exact this.aestronglyMeasurable)
    simp only [Function.comp_def] at this
    rw [this, dm_integral_coord]
    simp

private lemma dm_integrable_coord_mul {p m : ℕ} (a c : Fin p) (b d : Fin m) (k : ℝ) :
    Integrable (fun G : Fin p → Fin m → ℝ => k * (G a b * G c d)) (gaussianMatrix p m) :=
  ((dm_memLp_coord a b 2 (by simp)).integrable_mul (dm_memLp_coord c d 2 (by simp))).const_mul k

noncomputable def dmLin {p m : ℕ} (c : Fin p → Fin m → ℝ) (G : Fin p → Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, c i j * G i j

noncomputable def dmLinCLM {ι : Type*} {p m : ℕ} (a : ι → Fin p → Fin m → ℝ) :
    (Fin p → Fin m → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun t => ∑ i, ∑ j,
    a t i j • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => Fin m → ℝ) i))

private lemma dm_hasGaussianLaw_lin {ι : Type*} [Fintype ι] {p m : ℕ}
    (a : ι → Fin p → Fin m → ℝ) :
    HasGaussianLaw (fun G t => dmLin (a t) G) (gaussianMatrix p m) := by
  have h := (dm_hasGaussianLaw_id p m).map_fun (dmLinCLM a)
  have e : (fun G t => dmLin (a t) G) = fun G => dmLinCLM a G := by
    funext G t
    simp [dmLinCLM, dmLin]
  rw [e]; exact h

private lemma dm_integrable_lin {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    Integrable (dmLin c) (gaussianMatrix p m) := by
  unfold dmLin
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((dm_memLp_coord i j 2 (by simp)).integrable (by simp)).const_mul _

private lemma dm_continuous_lin {p m : ℕ} (c : Fin p → Fin m → ℝ) : Continuous (dmLin c) := by
  unfold dmLin; fun_prop

private lemma dm_integral_lin {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    ∫ G, dmLin c G ∂(gaussianMatrix p m) = 0 := by
  unfold dmLin
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((dm_memLp_coord i j 2 (by simp)).integrable (by simp)).const_mul _]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finsetSum _ fun j _ =>
    ((dm_memLp_coord i j 2 (by simp)).integrable (by simp)).const_mul _]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_const_mul, dm_integral_coord, mul_zero]

private lemma dm_lin_sub {p m : ℕ} (c d : Fin p → Fin m → ℝ) (G : Fin p → Fin m → ℝ) :
    dmLin c G - dmLin d G = dmLin (c - d) G := by
  simp only [dmLin, ← Finset.sum_sub_distrib, Pi.sub_apply, sub_mul]

private lemma dm_integral_lin_sq {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    ∫ G, dmLin c G ^ 2 ∂(gaussianMatrix p m) = ∑ i, ∑ j, c i j ^ 2 := by
  have hexp : ∀ G : Fin p → Fin m → ℝ, dmLin c G ^ 2 =
      ∑ i, ∑ k, ∑ j, ∑ l, c i j * c k l * (G i j * G k l) := by
    intro G
    unfold dmLin
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
    dm_integrable_coord_mul i k j l _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
    dm_integrable_coord_mul i k j l _]
  rw [Finset.sum_eq_single i]
  · rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
      dm_integrable_coord_mul i i j l _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun l _ => dm_integrable_coord_mul i i j l _]
    rw [Finset.sum_eq_single j]
    · rw [integral_const_mul, dm_integral_coord_mul]; simp [sq]
    · intro l _ hl
      rw [integral_const_mul, dm_integral_coord_mul]; simp [Ne.symm hl]
    · simp
  · intro k _ hk
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
      dm_integrable_coord_mul i k j l _]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_finsetSum _ fun l _ => dm_integrable_coord_mul i k j l _]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [integral_const_mul, dm_integral_coord_mul]; simp [Ne.symm hk]
  · simp

private lemma dm_integrable_iSup {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype ι]
    [Nonempty ι] (f : ι → Ω → ℝ) (hf : ∀ t, Integrable (f t) μ) (hm : ∀ t, Measurable (f t)) :
    Integrable (fun ω => ⨆ t, f t ω) μ := by
  refine Integrable.mono' (integrable_finsetSum Finset.univ fun t _ => (hf t).abs)
    (Measurable.iSup hm).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_le]
  obtain ⟨t0⟩ := ‹Nonempty ι›
  have hb : BddAbove (Set.range fun t => f t ω) := (Set.finite_range _).bddAbove
  have hs : ∀ t, |f t ω| ≤ ∑ t, |f t ω| := fun t =>
    Finset.single_le_sum (f := fun t => |f t ω|) (fun t _ => abs_nonneg _) (Finset.mem_univ t)
  constructor
  · have h1 := le_ciSup hb t0
    have h2 := hs t0
    have := neg_abs_le (f t0 ω)
    linarith
  · exact ciSup_le fun t => (le_abs_self _).trans (hs t)

private lemma dm_integrable_iInf {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype ι]
    [Nonempty ι] (f : ι → Ω → ℝ) (hf : ∀ t, Integrable (f t) μ) (hm : ∀ t, Measurable (f t)) :
    Integrable (fun ω => ⨅ t, f t ω) μ := by
  refine Integrable.mono' (integrable_finsetSum Finset.univ fun t _ => (hf t).abs)
    (Measurable.iInf hm).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_le]
  obtain ⟨t0⟩ := ‹Nonempty ι›
  have hb : BddBelow (Set.range fun t => f t ω) := (Set.finite_range _).bddBelow
  have hs : ∀ t, |f t ω| ≤ ∑ t, |f t ω| := fun t =>
    Finset.single_le_sum (f := fun t => |f t ω|) (fun t _ => abs_nonneg _) (Finset.mem_univ t)
  constructor
  · refine le_ciInf fun t => ?_
    have := neg_abs_le (f t ω)
    have := hs t
    linarith
  · have h1 := ciInf_le hb t0
    have h2 := hs t0
    have := le_abs_self (f t0 ω)
    linarith

private lemma dm_mp_split (n m : ℕ) :
    MeasurePreserving
      (fun x : Fin (n + m) → ℝ => ((fun j : Fin n => x (Fin.castAdd m j)),
        (fun i : Fin m => x (Fin.natAdd n i))))
      (Measure.pi fun _ : Fin (n + m) => gaussianReal 0 1)
      ((Measure.pi fun _ : Fin n => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin m => gaussianReal 0 1)) := by
  have h1 := (measurePreserving_piCongrLeft (α := fun _ : Fin (n + m) => ℝ)
    (fun _ : Fin (n + m) => gaussianReal 0 1) finSumFinEquiv).symm
  have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin n ⊕ Fin m => ℝ)
    (fun _ => gaussianReal 0 1)
  have h3 := h2.comp h1
  convert h3 using 1
  funext x
  simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft_symm_apply]

private lemma dm_mp_row (n m : ℕ) :
    MeasurePreserving (fun H : Fin 1 → Fin (n + m) → ℝ => H 0) (gaussianMatrix 1 (n + m))
      (Measure.pi fun _ : Fin (n + m) => gaussianReal 0 1) :=
  measurePreserving_eval (fun _ : Fin 1 => Measure.pi fun _ : Fin (n + m) => gaussianReal 0 1) 0

private lemma dm_integral_castAdd (n m : ℕ) (f : (Fin n → ℝ) → ℝ) (hf : Measurable f) :
    ∫ H, f (fun j => H 0 (Fin.castAdd m j)) ∂(gaussianMatrix 1 (n + m))
      = ∫ x, f x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  have h := (measurePreserving_fst (μ := Measure.pi fun _ : Fin n => gaussianReal 0 1)
    (ν := Measure.pi fun _ : Fin m => gaussianReal 0 1)).comp ((dm_mp_split n m).comp (dm_mp_row n m))
  rw [← h.map_eq, integral_map h.measurable.aemeasurable hf.aestronglyMeasurable]
  rfl

private lemma dm_integrable_sqrt_sumsq {k m : ℕ} (σ : Fin k → Fin m) :
    Integrable (fun H : Fin 1 → Fin m → ℝ => Real.sqrt (∑ j, H 0 (σ j) ^ 2))
      (gaussianMatrix 1 m) := by
  have hQ : Integrable (fun H : Fin 1 → Fin m → ℝ => ∑ j, H 0 (σ j) ^ 2)
      (gaussianMatrix 1 m) :=
    integrable_finsetSum _ fun j _ => (dm_memLp_coord 0 (σ j) 2 (by simp)).integrable_sq
  refine Integrable.mono' ((integrable_const 1).add hQ) (by fun_prop : Continuous
    (fun H : Fin 1 → Fin m → ℝ => Real.sqrt (∑ j, H 0 (σ j) ^ 2))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun H => ?_)
  have hQ0 : 0 ≤ ∑ j, H 0 (σ j) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 := Real.sq_sqrt hQ0
  have h2 := Real.sqrt_nonneg (∑ j, H 0 (σ j) ^ 2)
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (Real.sqrt (∑ j, H 0 (σ j) ^ 2) - 1)]

private lemma dm_integral_le_of_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => X ω ^ 2) μ) (δ : ℝ) (hδ : 0 < δ) :
    ∫ ω, X ω ∂μ ≤ ((∫ ω, X ω ^ 2 ∂μ) / δ + δ) / 2 := by
  have hI : Integrable (fun ω => (X ω ^ 2 / δ + δ) / 2) μ :=
    ((hX2.div_const δ).add (integrable_const δ)).div_const 2
  have hpt : ∀ ω, X ω ≤ (X ω ^ 2 / δ + δ) / 2 := by
    intro ω
    rw [div_add' _ _ _ hδ.ne', div_div, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (X ω - δ)]
  refine (integral_mono hX hI hpt).trans (le_of_eq ?_)
  rw [integral_div, integral_add (hX2.div_const δ) (integrable_const δ), integral_div,
    integral_const]
  simp

private lemma dm_integral_le_of_integral_sq_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => X ω ^ 2) μ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∫ ω, X ω ^ 2 ∂μ ≤ c ^ 2) : ∫ ω, X ω ∂μ ≤ c := by
  rcases hc.lt_or_eq with hc | hc
  · refine (dm_integral_le_of_sq μ X hX hX2 c hc).trans ?_
    have : (∫ ω, X ω ^ 2 ∂μ) / c ≤ c := by
      rw [div_le_iff₀ hc]; nlinarith
    linarith
  · subst hc
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    refine (dm_integral_le_of_sq μ X hX hX2 δ hδ).trans ?_
    have : (∫ ω, X ω ^ 2 ∂μ) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by simpa using h) hδ.le
    linarith

private lemma dm_integral_sqrt_sumsq_le {k m : ℕ} (σ : Fin k → Fin m) :
    ∫ H, Real.sqrt (∑ j, H 0 (σ j) ^ 2) ∂(gaussianMatrix 1 m) ≤ Real.sqrt k := by
  have hQ : Integrable (fun H : Fin 1 → Fin m → ℝ => ∑ j, H 0 (σ j) ^ 2) (gaussianMatrix 1 m) :=
    integrable_finsetSum _ fun j _ => (dm_memLp_coord 0 (σ j) 2 (by simp)).integrable_sq
  have hQ0 : ∀ H : Fin 1 → Fin m → ℝ, 0 ≤ ∑ j, H 0 (σ j) ^ 2 := fun H =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS := dm_integrable_sqrt_sumsq σ
  have hS2 : Integrable (fun H : Fin 1 → Fin m → ℝ => Real.sqrt (∑ j, H 0 (σ j) ^ 2) ^ 2)
      (gaussianMatrix 1 m) :=
    hQ.congr (Filter.Eventually.of_forall fun H => (Real.sq_sqrt (hQ0 H)).symm)
  refine dm_integral_le_of_integral_sq_le _ _ hS hS2 _ (Real.sqrt_nonneg _) (le_of_eq ?_)
  rw [Real.sq_sqrt (Nat.cast_nonneg k)]
  simp_rw [Real.sq_sqrt (hQ0 _)]
  rw [integral_finsetSum _ fun j _ => (dm_memLp_coord 0 (σ j) 2 (by simp)).integrable_sq]
  simp [dm_integral_coord_sq]

/-! ### Pushforward of `IsGaussianMatrix` to `gaussianMatrix m n` -/

private lemma dm_pi_curry_eq (m n : ℕ) :
    (Measure.pi fun _ : Fin m × Fin n => gaussianReal 0 1).map
      (fun (f : Fin m × Fin n → ℝ) (i : Fin m) (j : Fin n) => f (i, j)) =
      gaussianMatrix m n := by
  set curry : (Fin m × Fin n → ℝ) → (Fin m → Fin n → ℝ) := fun f i j => f (i, j)
  set uncurry : (Fin m → Fin n → ℝ) → (Fin m × Fin n → ℝ) := fun G p => G p.1 p.2
  have hmeas_c : Measurable curry := by
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    exact measurable_pi_apply (i, j)
  have hmeas_u : Measurable uncurry := by
    refine measurable_pi_lambda _ fun p => ?_
    exact (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  have huncurry : (gaussianMatrix m n).map uncurry =
      Measure.pi fun _ : Fin m × Fin n => gaussianReal 0 1 := by
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.map_apply hmeas_u (.univ_pi hs)]
    have hpre : uncurry ⁻¹' (Set.univ.pi s) =
        Set.univ.pi (fun i : Fin m => Set.univ.pi (fun j : Fin n => s (i, j))) := by
      ext G
      simp [uncurry, Prod.forall]
    rw [hpre]
    unfold gaussianMatrix
    rw [Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    exact (Fintype.prod_prod_type fun p : Fin m × Fin n => (gaussianReal 0 1) (s p)).symm
  rw [← huncurry, Measure.map_map hmeas_c hmeas_u]
  have hid : curry ∘ uncurry = id := by funext G i j; rfl
  rw [hid, Measure.map_id]

private lemma dm_isGaussianMatrix_map {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {m n : ℕ} (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hA : IsGaussianMatrix P A) :
    AEMeasurable (fun ω (i : Fin m) (j : Fin n) => A ω i j) P ∧
      P.map (fun ω (i : Fin m) (j : Fin n) => A ω i j) = gaussianMatrix m n := by
  have hae_entry : ∀ p : Fin m × Fin n, AEMeasurable (fun ω => A ω p.1 p.2) P := by
    intro p
    by_contra hna
    have h0 := Measure.map_of_not_aemeasurable hna
    rw [hA.1 p] at h0
    have h1 := congr_arg (fun μ : Measure ℝ => μ Set.univ) h0
    simp at h1
  have hae_prod : AEMeasurable (fun ω (p : Fin m × Fin n) => A ω p.1 p.2) P :=
    aemeasurable_pi_lambda _ hae_entry
  set curry : (Fin m × Fin n → ℝ) → (Fin m → Fin n → ℝ) := fun f i j => f (i, j)
  have hmeas_c : Measurable curry := by
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    exact measurable_pi_apply (i, j)
  have hae_raw : AEMeasurable (fun ω (i : Fin m) (j : Fin n) => A ω i j) P :=
    hmeas_c.comp_aemeasurable hae_prod
  refine ⟨hae_raw, ?_⟩
  have hpi := hA.2.map_fun_eq_pi_map hae_entry
  simp_rw [hA.1] at hpi
  have hcomp : (fun ω (i : Fin m) (j : Fin n) => A ω i j) =
      curry ∘ (fun ω (p : Fin m × Fin n) => A ω p.1 p.2) := rfl
  rw [hcomp, ← hmeas_c.aemeasurable.map_map_of_aemeasurable hae_prod, hpi]
  exact dm_pi_curry_eq m n

/-! ### Part 3: Increment comparisons and Gaussian width connection -/

private lemma dm_coeff_same {m n : ℕ} (u : EuclideanSpace ℝ (Fin m))
    (x y : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    ∑ i : Fin m, ∑ j : Fin n, (u i * x j - u i * y j) ^ 2 = ∑ j : Fin n, (x j - y j) ^ 2 := by
  have su : ∑ i : Fin m, u i ^ 2 = 1 := by rw [← dm_norm_sq, hu, one_pow]
  have hterm : ∀ (i : Fin m) (j : Fin n),
      (u i * x j - u i * y j) ^ 2 = u i ^ 2 * (x j - y j) ^ 2 := fun _ _ => by ring
  simp_rw [hterm, ← Finset.mul_sum, ← Finset.sum_mul, su, one_mul]

private lemma dm_coeff_ineq {m n : ℕ} (u v : EuclideanSpace ℝ (Fin m))
    (x y : EuclideanSpace ℝ (Fin n)) (D : ℝ)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hx : ‖x‖ ≤ D) (hy : ‖y‖ ≤ D) (_hD : 0 ≤ D) :
    ∑ i : Fin m, ∑ j : Fin n, (u i * x j - v i * y j) ^ 2 ≤
      ∑ j : Fin n, (x j - y j) ^ 2 + ∑ i : Fin m, (D * u i - D * v i) ^ 2 := by
  have su : ∑ i : Fin m, u i ^ 2 = 1 := by rw [← dm_norm_sq, hu, one_pow]
  have sv : ∑ i : Fin m, v i ^ 2 = 1 := by rw [← dm_norm_sq, hv, one_pow]
  have sx : ∑ j : Fin n, x j ^ 2 ≤ D ^ 2 := by
    rw [← dm_norm_sq]; exact pow_le_pow_left₀ (norm_nonneg x) hx 2
  have sy : ∑ j : Fin n, y j ^ 2 ≤ D ^ 2 := by
    rw [← dm_norm_sq]; exact pow_le_pow_left₀ (norm_nonneg y) hy 2
  set α := ∑ i : Fin m, u i * v i with hαdef
  set β := ∑ j : Fin n, x j * y j with hβdef
  have hL : ∑ i : Fin m, ∑ j : Fin n, (u i * x j - v i * y j) ^ 2
      = (∑ i, u i ^ 2) * (∑ j, x j ^ 2) - 2 * (α * β) + (∑ i, v i ^ 2) * (∑ j, y j ^ 2) := by
    rw [hαdef, hβdef, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hRx : ∑ j : Fin n, (x j - y j) ^ 2 = ∑ j, x j ^ 2 - 2 * β + ∑ j, y j ^ 2 := by
    rw [hβdef, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hRu : ∑ i : Fin m, (D * u i - D * v i) ^ 2 =
      D ^ 2 * (∑ i, u i ^ 2 - 2 * α + ∑ i, v i ^ 2) := by
    rw [hαdef, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hα : α ≤ 1 := by
    have : 0 ≤ ∑ i : Fin m, (u i - v i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h1 : ∑ i : Fin m, (u i - v i) ^ 2 = ∑ i, u i ^ 2 - 2 * α + ∑ i, v i ^ 2 := by
      rw [hαdef, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    linarith
  have hβ : β ≤ D ^ 2 := by
    have : 0 ≤ ∑ j : Fin n, (x j - y j) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  rw [hL, hRx, hRu, su, sv]
  nlinarith [mul_nonneg (sub_nonneg.2 hα) (sub_nonneg.2 hβ)]

private lemma dm_coeffY_sq {m n : ℕ} (x y : EuclideanSpace ℝ (Fin n))
    (u v : EuclideanSpace ℝ (Fin m)) (D : ℝ) :
    ∑ _r : Fin 1, ∑ k : Fin (n + m),
      (Fin.append (fun j => x j) (fun i => D * u i) k -
        Fin.append (fun j => y j) (fun i => D * v i) k) ^ 2
      = ∑ j : Fin n, (x j - y j) ^ 2 + ∑ i : Fin m, (D * u i - D * v i) ^ 2 := by
  rw [Fin.sum_univ_one, Fin.sum_univ_add]
  simp

private lemma dm_lin_append {m n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin m)) (D : ℝ) (H : Fin 1 → Fin (n + m) → ℝ) :
    dmLin (fun _ k => Fin.append (fun j => x j) (fun i => D * u i) k) H =
      (∑ j : Fin n, x j * H 0 (Fin.castAdd m j)) +
        D * (∑ i : Fin m, u i * H 0 (Fin.natAdd n i)) := by
  unfold dmLin
  rw [Fin.sum_univ_one, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

private lemma dm_sup'_eq_iSup {α : Type*} (S : Finset α) (hS : S.Nonempty) (f : α → ℝ) :
    S.sup' hS f = ⨆ x : S, f x.1 := by
  have : Nonempty S := hS.to_subtype
  refine le_antisymm ?_ ?_
  · exact Finset.sup'_le hS _ fun x hx =>
      le_ciSup (f := fun y : S => f y.1) (Set.finite_range _).bddAbove ⟨x, hx⟩
  · exact ciSup_le fun x => Finset.le_sup' f x.2

private lemma dm_continuous_sup' {ι α : Type*} [TopologicalSpace α]
    (S : Finset ι) (hS : S.Nonempty) (F : ι → α → ℝ) (hF : ∀ i ∈ S, Continuous (F i)) :
    Continuous (fun a => S.sup' hS (fun i => F i a)) := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton i =>
    simpa using hF i (Finset.mem_singleton_self i)
  | cons i s his hs ih =>
    simp_rw [Finset.sup'_cons hs]
    exact (hF i (Finset.mem_cons.2 (Or.inl rfl))).sup
      (ih fun j hj => hF j (Finset.mem_cons.2 (Or.inr hj)))

private lemma dm_integral_sup_stdGaussian {m n : ℕ} {T : Set (EuclideanSpace ℝ (Fin n))}
    (S : Finset T) (hS : S.Nonempty) :
    ∫ g, S.sup' hS (fun x => ⟪g, x.1⟫) ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ∫ H, S.sup' hS (fun x => ∑ j : Fin n, x.1 j * H 0 (Fin.castAdd m j))
        ∂(gaussianMatrix 1 (n + m)) := by
  have hcont1 : Continuous (fun g : EuclideanSpace ℝ (Fin n) => S.sup' hS (fun x => ⟪g, x.1⟫)) := by
    refine dm_continuous_sup' S hS (fun x g => ⟪g, x.1⟫) fun x _ => ?_
    have heq : (fun g : EuclideanSpace ℝ (Fin n) => ⟪g, x.1⟫) =
        fun g => ∑ j : Fin n, x.1 j * (EuclideanSpace.equiv (Fin n) ℝ g) j := by
      funext g
      rw [PiLp.inner_apply]
      exact Finset.sum_congr rfl fun j _ => by simp [mul_comm]
    rw [heq]
    exact continuous_finsetSum Finset.univ fun j _ =>
      continuous_const.mul ((continuous_apply j).comp (EuclideanSpace.equiv (Fin n) ℝ).continuous)
  have hmeas_toLp : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.measurable
  rw [← map_pi_eq_stdGaussian, integral_map hmeas_toLp.aemeasurable hcont1.aestronglyMeasurable]
  have hf_eq : (fun v : Fin n → ℝ => S.sup' hS (fun x => ⟪WithLp.toLp 2 v, x.1⟫)) =
      (fun v : Fin n → ℝ => S.sup' hS (fun x => ∑ j : Fin n, x.1 j * v j)) := by
    funext v
    refine Finset.sup'_congr hS rfl fun x _ => ?_
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun j _ => by simp [mul_comm]
  rw [hf_eq]
  have hcont2 : Continuous (fun v : Fin n → ℝ => S.sup' hS (fun x => ∑ j : Fin n, x.1 j * v j)) :=
    dm_continuous_sup' S hS (fun x (v : Fin n → ℝ) => ∑ j : Fin n, x.1 j * v j) fun x _ =>
      continuous_finsetSum Finset.univ fun j _ => continuous_const.mul (continuous_apply j)
  exact (dm_integral_castAdd n m _ hcont2.measurable).symm

private lemma dm_width_nonneg {n : ℕ} {T : Set (EuclideanSpace ℝ (Fin n))}
    (h0T : (0 : EuclideanSpace ℝ (Fin n)) ∈ T) {w : ℝ} (hw : gaussianWidth T = (w : EReal)) :
    0 ≤ w := by
  let x0 : T := ⟨0, h0T⟩
  let S0 : Finset T := {x0}
  have hS0 : S0.Nonempty := Finset.singleton_nonempty x0
  have hle : ((∫ g, S0.sup' hS0 (fun x => ⟪g, x.1⟫)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) : ℝ) : EReal) ≤ gaussianWidth T := by
    unfold gaussianWidth expSup
    exact le_iSup (fun S : {s : Finset T // s.Nonempty} =>
      ((∫ g, S.1.sup' S.2 (fun x => ⟪g, x.1⟫) ∂(stdGaussian _) : ℝ) : EReal)) ⟨S0, hS0⟩
  have hint : ∫ g, S0.sup' hS0 (fun x => ⟪g, x.1⟫)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) = 0 := by
    simp [S0, x0]
  rw [hint, hw] at hle
  exact EReal.coe_le_coe_iff.1 hle

private lemma dm_width_sup_le {n : ℕ} {T : Set (EuclideanSpace ℝ (Fin n))}
    {w : ℝ} (hw : gaussianWidth T = (w : EReal)) (S : Finset T) (hS : S.Nonempty) :
    ∫ g, S.sup' hS (fun x => ⟪g, x.1⟫) ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) ≤ w := by
  have hle : ((∫ g, S.sup' hS (fun x => ⟪g, x.1⟫)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) : ℝ) : EReal) ≤ gaussianWidth T := by
    unfold gaussianWidth expSup
    exact le_iSup (fun S' : {s : Finset T // s.Nonempty} =>
      ((∫ g, S'.1.sup' S'.2 (fun x => ⟪g, x.1⟫) ∂(stdGaussian _) : ℝ) : EReal)) ⟨S, hS⟩
  rw [hw] at hle
  exact EReal.coe_le_coe_iff.1 hle

private lemma dm_width_exists_gt {n : ℕ} {T : Set (EuclideanSpace ℝ (Fin n))}
    {w r : ℝ} (hw : gaussianWidth T = (w : EReal)) (hr : r < w) :
    ∃ (S : Finset T) (hS : S.Nonempty),
      r < ∫ g, S.sup' hS (fun x => ⟪g, x.1⟫) ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have hlt : (r : EReal) < gaussianWidth T := by
    rw [hw]; exact EReal.coe_lt_coe_iff.2 hr
  unfold gaussianWidth expSup at hlt
  obtain ⟨⟨S, hS⟩, hSr⟩ := lt_iSup_iff.1 hlt
  exact ⟨S, hS, EReal.coe_lt_coe_iff.1 hSr⟩

/-! ### Part 4: Upper bound on expected finite supremum via Sudakov-Fernique -/

private lemma dm_upper_scaled {m n : ℕ} (hm : 0 < m)
    {T : Set (EuclideanSpace ℝ (Fin n))} {D w : ℝ} (hD : 0 ≤ D)
    (hxD : ∀ x : T, ‖x.1‖ ≤ D) (hw : gaussianWidth T = (w : EReal))
    (S : Finset T) (hS : S.Nonempty) (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) * ∫ G, S.sup' hS (fun x => ‖dmPhi (Matrix.of G) x.1‖) ∂(gaussianMatrix m n)
      ≤ w + D * Real.sqrt m := by
  obtain ⟨Fu, hFuS, hFufin, hFucov⟩ := Metric.finite_approx_of_totallyBounded
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin m)) 1).totallyBounded δ hδ
  set U := hFufin.toFinset with hUdef
  have hU1 : ∀ u ∈ U, ‖u‖ = 1 := by
    intro u hu
    rw [hUdef, Set.Finite.mem_toFinset] at hu
    simpa using hFuS hu
  have hcovU : ∀ v : EuclideanSpace ℝ (Fin m), ‖v‖ = 1 → ∃ u ∈ U, ‖v - u‖ ≤ δ := by
    intro v hv
    have hv' : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 := by simpa using hv
    obtain ⟨u, hu, huv⟩ := Set.mem_iUnion₂.1 (hFucov hv')
    refine ⟨u, by rw [hUdef, Set.Finite.mem_toFinset]; exact hu, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at huv; exact huv.le
  set I := U ×ˢ S
  have hIne : Nonempty I := by
    obtain ⟨u, hu, -⟩ := hcovU (EuclideanSpace.single (⟨0, hm⟩ : Fin m) 1) (by simp)
    obtain ⟨x, hx⟩ := hS
    exact ⟨⟨(u, x), Finset.mem_product.2 ⟨hu, hx⟩⟩⟩
  set a : I → Fin m → Fin n → ℝ := fun p i j => p.1.1 i * p.1.2.1 j
  set b : I → Fin 1 → Fin (n + m) → ℝ :=
    fun p _ k => Fin.append (fun j => p.1.2.1 j) (fun i => D * p.1.1 i) k
  have hinc : ∀ p q : I,
      ∫ G, (dmLin (a p) G - dmLin (a q) G) ^ 2 ∂(gaussianMatrix m n)
        ≤ ∫ H, (dmLin (b p) H - dmLin (b q) H) ^ 2 ∂(gaussianMatrix 1 (n + m)) := by
    intro p q
    simp_rw [dm_lin_sub]
    rw [dm_integral_lin_sq, dm_integral_lin_sq]
    simp only [a, b, Pi.sub_apply]
    rw [dm_coeffY_sq]
    have hp := Finset.mem_product.1 p.2
    have hq := Finset.mem_product.1 q.2
    exact dm_coeff_ineq p.1.1 q.1.1 p.1.2.1 q.1.2.1 D
      (hU1 _ hp.1) (hU1 _ hq.1) (hxD p.1.2) (hxD q.1.2) hD
  have hSF := sudakov_fernique (fun p G => dmLin (a p) G) (fun p H => dmLin (b p) H)
    (dm_hasGaussianLaw_lin a) (dm_hasGaussianLaw_lin b)
    (fun p => dm_integral_lin _) (fun p => dm_integral_lin _) hinc
  -- Integrability of `G ↦ S.sup' hS (fun x => ‖dmPhi (Matrix.of G) x.1‖)`
  have hLip_sup : ∀ X Y : Fin m → Fin n → ℝ,
      |(S.sup' hS fun x => ‖dmPhi (Matrix.of X) x.1‖) -
        (S.sup' hS fun x => ‖dmPhi (Matrix.of Y) x.1‖)| ≤
        (D + 1) * frobNorm (Matrix.of X - Matrix.of Y) := by
    intro X Y
    refine dm_sup'_lip S hS (fun x G => ‖dmPhi (Matrix.of G) x.1‖) X Y fun x _ => ?_
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← dmPhi_sub_left]
    calc ‖dmPhi (Matrix.of X - Matrix.of Y) x.1‖
        ≤ frobNorm (Matrix.of X - Matrix.of Y) * ‖x.1‖ := dm_norm_dmPhi_le _ _
      _ ≤ frobNorm (Matrix.of X - Matrix.of Y) * (D + 1) :=
          mul_le_mul_of_nonneg_left (by linarith [hxD x]) (Real.sqrt_nonneg _)
      _ = (D + 1) * frobNorm (Matrix.of X - Matrix.of Y) := mul_comm _ _
  have hInt_sup : Integrable (fun G : Fin m → Fin n → ℝ =>
      S.sup' hS (fun x => ‖dmPhi (Matrix.of G) x.1‖)) (gaussianMatrix m n) :=
    (gaussian_concentration _ (D + 1) (by linarith) hLip_sup 0 le_rfl).1
  have hXsup := dm_integrable_iSup (μ := gaussianMatrix m n) (fun p G => dmLin (a p) G)
    (fun p => dm_integrable_lin _) (fun p => (dm_continuous_lin _).measurable)
  have hYsup := dm_integrable_iSup (μ := gaussianMatrix 1 (n + m)) (fun p H => dmLin (b p) H)
    (fun p => dm_integrable_lin _) (fun p => (dm_continuous_lin _).measurable)
  have : Nonempty S := hS.to_subtype
  have hInt_g : Integrable (fun H : Fin 1 → Fin (n + m) → ℝ =>
      S.sup' hS (fun x => ∑ j : Fin n, x.1 j * H 0 (Fin.castAdd m j)))
      (gaussianMatrix 1 (n + m)) := by
    have heq : (fun H : Fin 1 → Fin (n + m) → ℝ =>
        S.sup' hS (fun x => ∑ j : Fin n, x.1 j * H 0 (Fin.castAdd m j))) =
        fun H => ⨆ x : S, dmLin (fun _ k =>
          Fin.append (fun j => x.1.1 j) (fun _ : Fin m => (0 : ℝ)) k) H := by
      funext H
      rw [dm_sup'_eq_iSup]
      congr 1; funext x
      have := dm_lin_append x.1.1 0 0 H
      simpa using this.symm
    rw [heq]
    exact dm_integrable_iSup _ (fun _ => dm_integrable_lin _)
      (fun _ => (dm_continuous_lin _).measurable)
  have hInt_h : Integrable (fun H : Fin 1 → Fin (n + m) → ℝ =>
      D * Real.sqrt (∑ i : Fin m, H 0 (Fin.natAdd n i) ^ 2))
      (gaussianMatrix 1 (n + m)) :=
    (dm_integrable_sqrt_sumsq (fun i : Fin m => Fin.natAdd n i)).const_mul D
  -- Pointwise net lower bound on matrix side
  have hnet_G : ∀ G : Fin m → Fin n → ℝ,
      (1 - δ) * S.sup' hS (fun x => ‖dmPhi (Matrix.of G) x.1‖) ≤ ⨆ p : I, dmLin (a p) G := by
    intro G
    obtain ⟨x, hxS, hx_eq⟩ := Finset.exists_mem_eq_sup' hS
      (fun x => ‖dmPhi (Matrix.of G) x.1‖)
    rw [hx_eq]
    set y := dmPhi (Matrix.of G) x.1
    have hbI : BddAbove (Set.range fun p : I => dmLin (a p) G) :=
      (Set.finite_range _).bddAbove
    by_cases hy0 : y = 0
    · obtain ⟨u, huU, -⟩ := hcovU (EuclideanSpace.single (⟨0, hm⟩ : Fin m) 1) (by simp)
      have hpI : (u, x) ∈ I := Finset.mem_product.2 ⟨huU, hxS⟩
      refine le_trans ?_ (le_ciSup hbI ⟨(u, x), hpI⟩)
      have h0 : dmLin (a ⟨(u, x), hpI⟩) G = ⟪u, y⟫ := by
        simpa [dmLin, a, y] using (dm_inner_dmPhi (Matrix.of G) u x.1).symm
      rw [h0, hy0, norm_zero, mul_zero, inner_zero_right]
    · set v : EuclideanSpace ℝ (Fin m) := (‖y‖⁻¹ : ℝ) • y
      have hv1 : ‖v‖ = 1 := norm_smul_inv_norm hy0
      have hvy : ⟪v, y⟫ = ‖y‖ := by
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
        have : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy0
        field_simp
      obtain ⟨u, huU, hvu⟩ := hcovU v hv1
      have hpI : (u, x) ∈ I := Finset.mem_product.2 ⟨huU, hxS⟩
      refine le_trans ?_ (le_ciSup hbI ⟨(u, x), hpI⟩)
      have hlin : dmLin (a ⟨(u, x), hpI⟩) G = ⟪u, y⟫ := by
        simpa [dmLin, a, y] using (dm_inner_dmPhi (Matrix.of G) u x.1).symm
      rw [hlin]
      have hdecomp : ⟪u, y⟫ = ⟪v, y⟫ - ⟪v - u, y⟫ := by rw [inner_sub_left]; ring
      have herr : ⟪v - u, y⟫ ≤ δ * ‖y‖ :=
        (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hvu (norm_nonneg y))
      rw [hdecomp, hvy]
      linarith
  -- Pointwise upper bound on vector side
  have hbound_H : ∀ H : Fin 1 → Fin (n + m) → ℝ,
      (⨆ p : I, dmLin (b p) H) ≤
        S.sup' hS (fun x => ∑ j : Fin n, x.1 j * H 0 (Fin.castAdd m j)) +
          D * Real.sqrt (∑ i : Fin m, H 0 (Fin.natAdd n i) ^ 2) := by
    intro H
    refine ciSup_le fun p => ?_
    have hp := Finset.mem_product.1 p.2
    have hlin : dmLin (b p) H =
        (∑ j : Fin n, p.1.2.1 j * H 0 (Fin.castAdd m j)) +
          D * (∑ i : Fin m, p.1.1 i * H 0 (Fin.natAdd n i)) :=
      dm_lin_append p.1.2.1 p.1.1 D H
    rw [hlin]
    have h1 : ∑ j : Fin n, p.1.2.1 j * H 0 (Fin.castAdd m j) ≤
        S.sup' hS (fun x => ∑ j : Fin n, x.1 j * H 0 (Fin.castAdd m j)) :=
      Finset.le_sup' (fun x : T => ∑ j : Fin n, x.1 j * H 0 (Fin.castAdd m j)) hp.2
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun i : Fin m => p.1.1 i) (fun i : Fin m => H 0 (Fin.natAdd n i))
    rw [← dm_norm_eq_sqrt, hU1 _ hp.1, one_mul] at hcs
    exact add_le_add h1 (mul_le_mul_of_nonneg_left hcs hD)
  calc (1 - δ) * ∫ G, S.sup' hS (fun x => ‖dmPhi (Matrix.of G) x.1‖) ∂(gaussianMatrix m n)
      = ∫ G, (1 - δ) * S.sup' hS (fun x => ‖dmPhi (Matrix.of G) x.1‖) ∂(gaussianMatrix m n) :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ G, (⨆ p : I, dmLin (a p) G) ∂(gaussianMatrix m n) :=
        integral_mono (hInt_sup.const_mul _) hXsup hnet_G
    _ ≤ ∫ H, (⨆ p : I, dmLin (b p) H) ∂(gaussianMatrix 1 (n + m)) := hSF
    _ ≤ ∫ H, (S.sup' hS (fun x => ∑ j : Fin n, x.1 j * H 0 (Fin.castAdd m j)) +
          D * Real.sqrt (∑ i : Fin m, H 0 (Fin.natAdd n i) ^ 2)) ∂(gaussianMatrix 1 (n + m)) :=
        integral_mono hYsup (hInt_g.add hInt_h) hbound_H
    _ = (∫ H, S.sup' hS (fun x => ∑ j : Fin n, x.1 j * H 0 (Fin.castAdd m j))
          ∂(gaussianMatrix 1 (n + m))) +
        D * ∫ H, Real.sqrt (∑ i : Fin m, H 0 (Fin.natAdd n i) ^ 2) ∂(gaussianMatrix 1 (n + m)) := by
        rw [integral_add hInt_g hInt_h, integral_const_mul]
    _ = (∫ g, S.sup' hS (fun x => ⟪g, x.1⟫) ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))) +
        D * ∫ H, Real.sqrt (∑ i : Fin m, H 0 (Fin.natAdd n i) ^ 2) ∂(gaussianMatrix 1 (n + m)) := by
        rw [dm_integral_sup_stdGaussian]
    _ ≤ w + D * Real.sqrt m :=
        add_le_add (dm_width_sup_le hw S hS)
          (mul_le_mul_of_nonneg_left (dm_integral_sqrt_sumsq_le _) hD)

private lemma dm_upper_expectation {m n : ℕ} (hm : 0 < m)
    {T : Set (EuclideanSpace ℝ (Fin n))} (h0T : (0 : EuclideanSpace ℝ (Fin n)) ∈ T)
    {D w : ℝ} (hD : 0 ≤ D) (hxD : ∀ x : T, ‖x.1‖ ≤ D)
    (hw : gaussianWidth T = (w : EReal)) (S : Finset T) (hS : S.Nonempty) :
    ∫ G, S.sup' hS (fun x => ‖dmPhi (Matrix.of G) x.1‖) ∂(gaussianMatrix m n)
      ≤ w + D * Real.sqrt m := by
  set E := ∫ G, S.sup' hS (fun x => ‖dmPhi (Matrix.of G) x.1‖) ∂(gaussianMatrix m n)
  set B := w + D * Real.sqrt m
  have hw0 : 0 ≤ w := dm_width_nonneg h0T hw
  have hB0 : 0 ≤ B := add_nonneg hw0 (mul_nonneg hD (Real.sqrt_nonneg _))
  by_contra hcon
  push Not at hcon
  have hEpos : 0 < E := lt_of_le_of_lt hB0 hcon
  have h1 := dm_upper_scaled hm hD hxD hw S hS ((E - B) / (2 * E))
    (div_pos (by linarith) (by linarith))
  have h2 : (1 - (E - B) / (2 * E)) * E = (E + B) / 2 := by
    field_simp; ring
  change (1 - (E - B) / (2 * E)) * E ≤ B at h1
  rw [h2] at h1
  linarith

/-! ### Part 5: Lower bound on expected min-max over net via Gordon's minimax -/

private lemma dm_lower_expectation {m n : ℕ} {T : Set (EuclideanSpace ℝ (Fin n))}
    {D : ℝ} (hD : 0 ≤ D) (hxD : ∀ x : T, ‖x.1‖ ≤ D)
    (U : Finset (EuclideanSpace ℝ (Fin m))) (hU1 : ∀ u ∈ U, ‖u‖ = 1) (hUne : Nonempty U)
    (S₀ : Finset T) (hS₀ : S₀.Nonempty) :
    (∫ g, S₀.sup' hS₀ (fun x => ⟪g, x.1⟫) ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))) -
        D * Real.sqrt m ≤
      ∫ G, (⨅ u : U, ⨆ x : S₀, ∑ i : Fin m, ∑ j : Fin n, u.1 i * x.1.1 j * G i j)
        ∂(gaussianMatrix m n) := by
  have : Nonempty S₀ := hS₀.to_subtype
  set b : U → S₀ → Fin 1 → Fin (n + m) → ℝ :=
    fun u x _ k => Fin.append (fun j => x.1.1 j) (fun i => D * u.1 i) k
  set a : U → S₀ → Fin m → Fin n → ℝ :=
    fun u x i j => u.1 i * x.1.1 j
  have hsame : ∀ (u : U) (x y : S₀),
      ∫ H, (dmLin (b u x) H - dmLin (b u y) H) ^ 2 ∂(gaussianMatrix 1 (n + m))
        ≤ ∫ G, (dmLin (a u x) G - dmLin (a u y) G) ^ 2 ∂(gaussianMatrix m n) := by
    intro u x y
    simp_rw [dm_lin_sub]
    rw [dm_integral_lin_sq, dm_integral_lin_sq]
    simp only [a, b, Pi.sub_apply]
    rw [dm_coeffY_sq, dm_coeff_same u.1 x.1.1 y.1.1 (hU1 _ u.2)]
    simp
  have hdiff : ∀ (u v : U) (x y : S₀), u ≠ v →
      ∫ G, (dmLin (a u x) G - dmLin (a v y) G) ^ 2 ∂(gaussianMatrix m n)
        ≤ ∫ H, (dmLin (b u x) H - dmLin (b v y) H) ^ 2 ∂(gaussianMatrix 1 (n + m)) := by
    intro u v x y _
    simp_rw [dm_lin_sub]
    rw [dm_integral_lin_sq, dm_integral_lin_sq]
    simp only [a, b, Pi.sub_apply]
    rw [dm_coeffY_sq]
    exact dm_coeff_ineq u.1 v.1 x.1.1 y.1.1 D
      (hU1 _ u.2) (hU1 _ v.2) (hxD x.1) (hxD y.1) hD
  have hGM := gordon_minimax (fun u x H => dmLin (b u x) H) (fun u x G => dmLin (a u x) G)
    (dm_hasGaussianLaw_lin (fun p : U × S₀ => b p.1 p.2))
    (dm_hasGaussianLaw_lin (fun p : U × S₀ => a p.1 p.2))
    (fun u x => dm_integral_lin _) (fun u x => dm_integral_lin _) hsame hdiff
  have hXmm : Integrable (fun H => ⨅ u : U, ⨆ x : S₀, dmLin (b u x) H)
      (gaussianMatrix 1 (n + m)) :=
    dm_integrable_iInf (fun u H => ⨆ x : S₀, dmLin (b u x) H)
      (fun u => dm_integrable_iSup (fun x H => dmLin (b u x) H) (fun _ => dm_integrable_lin _)
        (fun _ => (dm_continuous_lin _).measurable))
      (fun _ => Measurable.iSup fun _ => (dm_continuous_lin _).measurable)
  have hInt_g : Integrable (fun H : Fin 1 → Fin (n + m) → ℝ =>
      S₀.sup' hS₀ (fun x => ∑ j : Fin n, x.1 j * H 0 (Fin.castAdd m j)))
      (gaussianMatrix 1 (n + m)) := by
    have heq : (fun H : Fin 1 → Fin (n + m) → ℝ =>
        S₀.sup' hS₀ (fun x => ∑ j : Fin n, x.1 j * H 0 (Fin.castAdd m j))) =
        fun H => ⨆ x : S₀, dmLin (fun _ k =>
          Fin.append (fun j => x.1.1 j) (fun _ : Fin m => (0 : ℝ)) k) H := by
      funext H
      rw [dm_sup'_eq_iSup]
      congr 1; funext x
      have := dm_lin_append x.1.1 0 0 H
      simpa using this.symm
    rw [heq]
    exact dm_integrable_iSup _ (fun _ => dm_integrable_lin _)
      (fun _ => (dm_continuous_lin _).measurable)
  have hInt_h : Integrable (fun H : Fin 1 → Fin (n + m) → ℝ =>
      D * Real.sqrt (∑ i : Fin m, H 0 (Fin.natAdd n i) ^ 2))
      (gaussianMatrix 1 (n + m)) :=
    (dm_integrable_sqrt_sumsq (fun i : Fin m => Fin.natAdd n i)).const_mul D
  have hpt_H : ∀ H : Fin 1 → Fin (n + m) → ℝ,
      S₀.sup' hS₀ (fun x => ∑ j : Fin n, x.1 j * H 0 (Fin.castAdd m j)) -
        D * Real.sqrt (∑ i : Fin m, H 0 (Fin.natAdd n i) ^ 2) ≤
        ⨅ u : U, ⨆ x : S₀, dmLin (b u x) H := by
    intro H
    obtain ⟨x₀, hx₀S, hx₀_eq⟩ := Finset.exists_mem_eq_sup' hS₀
      (fun x => ∑ j : Fin n, x.1 j * H 0 (Fin.castAdd m j))
    rw [hx₀_eq]
    refine le_ciInf fun u => ?_
    have hb : BddAbove (Set.range fun x : S₀ => dmLin (b u x) H) :=
      (Set.finite_range _).bddAbove
    refine le_trans ?_ (le_ciSup hb ⟨x₀, hx₀S⟩)
    rw [dm_lin_append x₀.1 u.1 D H]
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun i : Fin m => u.1 i) (fun i : Fin m => -H 0 (Fin.natAdd n i))
    rw [← dm_norm_eq_sqrt, hU1 _ u.2, one_mul] at hcs
    simp only [neg_sq, mul_neg, Finset.sum_neg_distrib] at hcs
    have hDcs : D * (-∑ i : Fin m, u.1 i * H 0 (Fin.natAdd n i)) ≤
        D * Real.sqrt (∑ i : Fin m, H 0 (Fin.natAdd n i) ^ 2) :=
      mul_le_mul_of_nonneg_left hcs hD
    linarith
  calc (∫ g, S₀.sup' hS₀ (fun x => ⟪g, x.1⟫) ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))) -
          D * Real.sqrt m
      ≤ (∫ H, S₀.sup' hS₀ (fun x => ∑ j : Fin n, x.1 j * H 0 (Fin.castAdd m j))
          ∂(gaussianMatrix 1 (n + m))) -
        D * ∫ H, Real.sqrt (∑ i : Fin m, H 0 (Fin.natAdd n i) ^ 2)
          ∂(gaussianMatrix 1 (n + m)) := by
        rw [dm_integral_sup_stdGaussian]
        exact sub_le_sub_left (mul_le_mul_of_nonneg_left (dm_integral_sqrt_sumsq_le _) hD) _
    _ = ∫ H, (S₀.sup' hS₀ (fun x => ∑ j : Fin n, x.1 j * H 0 (Fin.castAdd m j)) -
          D * Real.sqrt (∑ i : Fin m, H 0 (Fin.natAdd n i) ^ 2)) ∂(gaussianMatrix 1 (n + m)) := by
        rw [integral_sub hInt_g hInt_h, integral_const_mul]
    _ ≤ ∫ H, (⨅ u : U, ⨆ x : S₀, dmLin (b u x) H) ∂(gaussianMatrix 1 (n + m)) :=
        integral_mono (hInt_g.sub hInt_h) hXmm hpt_H
    _ ≤ ∫ G, (⨅ u : U, ⨆ x : S₀, dmLin (a u x) G) ∂(gaussianMatrix m n) := hGM
    _ = ∫ G, (⨅ u : U, ⨆ x : S₀, ∑ i : Fin m, ∑ j : Fin n, u.1 i * x.1.1 j * G i j)
          ∂(gaussianMatrix m n) := rfl

/-! ### Part 6: Convex-hull ball inclusion via Hahn-Banach separation -/

private lemma dm_closedBall_subset_convexHull {m : ℕ}
    (F : Finset (EuclideanSpace ℝ (Fin m))) (hF : F.Nonempty) (r : ℝ)
    (hsupp : ∀ v : EuclideanSpace ℝ (Fin m), ‖v‖ = 1 → ∃ y ∈ F, r < ⟪v, y⟫) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r ⊆ convexHull ℝ (F : Set _) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  by_contra hzK
  have hconv : Convex ℝ (convexHull ℝ (F : Set (EuclideanSpace ℝ (Fin m)))) :=
    convex_convexHull ℝ _
  have hclosed : IsClosed (convexHull ℝ (F : Set (EuclideanSpace ℝ (Fin m)))) :=
    F.finite_toSet.isClosed_convexHull ℝ
  obtain ⟨f, u, hfz, hub⟩ := geometric_hahn_banach_point_closed hconv hclosed hzK
  set v₀ : EuclideanSpace ℝ (Fin m) := -((InnerProductSpace.toDual ℝ _).symm f)
  have hfv₀ : ∀ y : EuclideanSpace ℝ (Fin m), f y = -⟪v₀, y⟫ := by
    intro y
    simp [v₀, InnerProductSpace.toDual_symm_apply]
  have hlt_all : ∀ y ∈ F, ⟪v₀, y⟫ < ⟪v₀, z⟫ := by
    intro y hyF
    have hyK : y ∈ convexHull ℝ (F : Set _) := subset_convexHull ℝ _ hyF
    have h1 := hub y hyK
    rw [hfv₀ z] at hfz
    rw [hfv₀ y] at h1
    linarith
  have hv₀_ne : v₀ ≠ 0 := by
    obtain ⟨y₀, hy₀⟩ := hF
    intro hv0
    have h := hlt_all y₀ hy₀
    rw [hv0, inner_zero_left, inner_zero_left] at h
    exact lt_irrefl 0 h
  set v : EuclideanSpace ℝ (Fin m) := (‖v₀‖⁻¹ : ℝ) • v₀
  have hv1 : ‖v‖ = 1 := norm_smul_inv_norm hv₀_ne
  obtain ⟨y, hyF, hry⟩ := hsupp v hv1
  have hpos : 0 < ‖v₀‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hv₀_ne)
  have hyz : ⟪v, y⟫ < ⟪v, z⟫ := by
    rw [real_inner_smul_left, real_inner_smul_left]
    exact mul_lt_mul_of_pos_left (hlt_all y hyF) hpos
  have hzr : ⟪v, z⟫ ≤ r := by
    calc ⟪v, z⟫ ≤ ‖v‖ * ‖z‖ := real_inner_le_norm v z
      _ = ‖z‖ := by rw [hv1, one_mul]
      _ ≤ r := hz
  linarith

/-! ### Part 7: Tail probability arithmetic -/

private lemma dm_exp_tail_le {t : ℝ} (ht : 25 ≤ t) :
    ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) ≤ (1 / 200 : ENNReal) := by
  have ht2 : (200 : ℝ) ≤ 1 + t ^ 2 / 2 := by nlinarith
  have hexp_pos : 0 < Real.exp (t ^ 2 / 2) := Real.exp_pos _
  have hexp_ge : (200 : ℝ) ≤ Real.exp (t ^ 2 / 2) :=
    ht2.trans (by linarith [Real.add_one_le_exp (t ^ 2 / 2)])
  have hle : Real.exp (-t ^ 2 / 2) ≤ 1 / 200 := by
    rw [show -t ^ 2 / 2 = -(t ^ 2 / 2) by ring, Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) hexp_ge
  calc ENNReal.ofReal (Real.exp (-t ^ 2 / 2))
      ≤ ENNReal.ofReal (1 / 200) := ENNReal.ofReal_le_ofReal hle
    _ = (1 / 200 : ENNReal) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num

private lemma dm_prob_inter_ge {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {G₁ G₂ : Set α}
    (h1 : μ G₁ᶜ ≤ (1 / 200 : ENNReal)) (h2 : μ G₂ᶜ ≤ (1 / 200 : ENNReal)) :
    (99 / 100 : ENNReal) ≤ μ (G₁ ∩ G₂) := by
  have hcov : (Set.univ : Set α) ⊆ (G₁ ∩ G₂) ∪ G₁ᶜ ∪ G₂ᶜ := by
    intro x _
    by_cases hx1 : x ∈ G₁
    · by_cases hx2 : x ∈ G₂
      · exact Or.inl (Or.inl ⟨hx1, hx2⟩)
      · exact Or.inr hx2
    · exact Or.inl (Or.inr hx1)
  have hsum : (1 : ENNReal) ≤ μ (G₁ ∩ G₂) + μ G₁ᶜ + μ G₂ᶜ := by
    calc (1 : ENNReal) = μ Set.univ := measure_univ.symm
      _ ≤ μ ((G₁ ∩ G₂) ∪ G₁ᶜ ∪ G₂ᶜ) := measure_mono hcov
      _ ≤ μ ((G₁ ∩ G₂) ∪ G₁ᶜ) + μ G₂ᶜ := measure_union_le _ _
      _ ≤ μ (G₁ ∩ G₂) + μ G₁ᶜ + μ G₂ᶜ := add_le_add (measure_union_le _ _) le_rfl
  have hsum2 : (1 : ENNReal) ≤ μ (G₁ ∩ G₂) + (1 / 200 : ENNReal) + (1 / 200 : ENNReal) :=
    hsum.trans (add_le_add (add_le_add le_rfl h1) h2)
  have h99 : (99 / 100 : ENNReal) + (1 / 100 : ENNReal) = 1 := by
    have e1 : (99 / 100 : ENNReal) = ENNReal.ofReal (99 / 100) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
    have e2 : (1 / 100 : ENNReal) = ENNReal.ofReal (1 / 100) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
    rw [e1, e2, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  have h200 : (1 / 200 : ENNReal) + (1 / 200 : ENNReal) = (1 / 100 : ENNReal) := by
    have e1 : (1 / 200 : ENNReal) = ENNReal.ofReal (1 / 200) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
    have e2 : (1 / 100 : ENNReal) = ENNReal.ofReal (1 / 100) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
    rw [e1, e2, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  have hsum3 : (99 / 100 : ENNReal) + (1 / 100 : ENNReal) ≤
      μ (G₁ ∩ G₂) + (1 / 100 : ENNReal) := by
    rw [h99, ← h200, ← add_assoc]
    exact hsum2
  exact (ENNReal.add_le_add_iff_right (by norm_num : (1 / 100 : ENNReal) ≠ ⊤)).1 hsum3

noncomputable def dmSk {n : ℕ} {T : Set (EuclideanSpace ℝ (Fin n))} [DecidableEq T]
    (seq : ℕ → T) (k : ℕ) : Finset T :=
  (Finset.range (k + 1)).image seq

private lemma dmSk_nonempty {n : ℕ} {T : Set (EuclideanSpace ℝ (Fin n))} [DecidableEq T]
    (seq : ℕ → T) (k : ℕ) : (dmSk seq k).Nonempty :=
  ⟨seq 0, Finset.mem_image_of_mem seq (Finset.mem_range.2 (Nat.succ_pos k))⟩

noncomputable def dmSupSeq {m n : ℕ} {T : Set (EuclideanSpace ℝ (Fin n))} [DecidableEq T]
    (seq : ℕ → T) (k : ℕ) (G : Fin m → Fin n → ℝ) : ℝ :=
  (dmSk seq k).sup' (dmSk_nonempty seq k) (fun x => ‖dmPhi (Matrix.of G) x.1‖)

private lemma dmSupSeq_lip {m n : ℕ} {T : Set (EuclideanSpace ℝ (Fin n))} [DecidableEq T]
    {D : ℝ} (hxD : ∀ x : T, ‖x.1‖ ≤ D) (seq : ℕ → T) (k : ℕ)
    (X Y : Fin m → Fin n → ℝ) :
    |dmSupSeq seq k X - dmSupSeq seq k Y| ≤ D * frobNorm (Matrix.of X - Matrix.of Y) := by
  unfold dmSupSeq
  refine dm_sup'_lip (dmSk seq k) (dmSk_nonempty seq k)
    (fun x G => ‖dmPhi (Matrix.of G) x.1‖) X Y fun x _ => ?_
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [← dmPhi_sub_left]
  calc ‖dmPhi (Matrix.of X - Matrix.of Y) x.1‖
      ≤ frobNorm (Matrix.of X - Matrix.of Y) * ‖x.1‖ := dm_norm_dmPhi_le _ _
    _ ≤ frobNorm (Matrix.of X - Matrix.of Y) * D :=
        mul_le_mul_of_nonneg_left (hxD x) (Real.sqrt_nonneg _)
    _ = D * frobNorm (Matrix.of X - Matrix.of Y) := mul_comm _ _

private lemma dmSupSeq_cont {m n : ℕ} {T : Set (EuclideanSpace ℝ (Fin n))} [DecidableEq T]
    {D : ℝ} (hxD : ∀ x : T, ‖x.1‖ ≤ D) (seq : ℕ → T) (k : ℕ) :
    Continuous (dmSupSeq (m := m) seq k) :=
  dm_continuous_of_lip (dmSupSeq seq k) D (dmSupSeq_lip hxD seq k)

noncomputable def dmGoodUpper {m n : ℕ} {T : Set (EuclideanSpace ℝ (Fin n))} [DecidableEq T]
    (seq : ℕ → T) (r : ℝ) : Set (Fin m → Fin n → ℝ) :=
  ⋂ k : ℕ, {G | dmSupSeq seq k G ≤ r}

private lemma dmGoodUpper_measurable {m n : ℕ} {T : Set (EuclideanSpace ℝ (Fin n))} [DecidableEq T]
    {D : ℝ} (hxD : ∀ x : T, ‖x.1‖ ≤ D) (seq : ℕ → T) (r : ℝ) :
    MeasurableSet (dmGoodUpper (m := m) seq r) :=
  MeasurableSet.iInter fun k => isClosed_le (dmSupSeq_cont hxD seq k) continuous_const |>.measurableSet

private lemma dmGoodUpper_tail {m n : ℕ} (hm_pos : 0 < m)
    {T : Set (EuclideanSpace ℝ (Fin n))} [DecidableEq T]
    (h0T : (0 : EuclideanSpace ℝ (Fin n)) ∈ T)
    {D ε w t : ℝ} (hD_pos : 0 < D) (hxD : ∀ x : T, ‖x.1‖ ≤ D)
    (hε0 : 0 < ε) (hw_pos : 0 < w) (hw : gaussianWidth T = (w : EReal))
    (hDm : D * Real.sqrt m ≤ ε / 100 * w)
    (ht_pos : 0 ≤ t) (ht_ge25 : 25 ≤ t) (hDt_eq : D * t = ε / 4 * w)
    (seq : ℕ → T) :
    (gaussianMatrix m n) (dmGoodUpper (m := m) seq ((1 + ε) * w))ᶜ ≤ (1 / 200 : ENNReal) := by
  have hCompl : (dmGoodUpper (m := m) seq ((1 + ε) * w))ᶜ =
      ⋃ k : ℕ, {G | (1 + ε) * w < dmSupSeq seq k G} := by
    ext G; simp [dmGoodUpper]
  have hMono : Monotone (fun k : ℕ => {G : Fin m → Fin n → ℝ | (1 + ε) * w < dmSupSeq seq k G}) := by
    intro k l hkl G hG
    simp only [Set.mem_ofPred] at hG ⊢
    refine hG.trans_le ?_
    unfold dmSupSeq
    refine Finset.sup'_le (dmSk_nonempty seq k) _ fun x hx => ?_
    have hsub : dmSk seq k ⊆ dmSk seq l :=
      Finset.image_subset_image (Finset.range_mono (by omega))
    exact Finset.le_sup' (fun y : T => ‖dmPhi (Matrix.of G) y.1‖) (hsub hx)
  rw [hCompl, hMono.measure_iUnion]
  refine iSup_le fun k => ?_
  have hconc := (gaussian_concentration (dmSupSeq (m := m) seq k) D hD_pos
    (dmSupSeq_lip hxD seq k) t ht_pos).2
  have hExp_le : ∫ Y, dmSupSeq seq k Y ∂(gaussianMatrix m n) ≤ w + D * Real.sqrt m :=
    dm_upper_expectation hm_pos h0T hD_pos.le hxD hw (dmSk seq k) (dmSk_nonempty seq k)
  have hsub : {G : Fin m → Fin n → ℝ | (1 + ε) * w < dmSupSeq seq k G} ⊆
      {G : Fin m → Fin n → ℝ | (∫ Y, dmSupSeq seq k Y ∂(gaussianMatrix m n)) + D * t ≤ dmSupSeq seq k G} := by
    intro G hG
    simp only [Set.mem_ofPred] at hG ⊢
    have hmargin : w + D * Real.sqrt m + D * t ≤ (1 + ε) * w := by
      nlinarith [hDm, hDt_eq, mul_pos hε0 hw_pos]
    linarith
  exact (measure_mono hsub).trans (hconc.trans (dm_exp_tail_le ht_ge25))

private lemma dmGoodUpper_det {m n : ℕ} {T : Set (EuclideanSpace ℝ (Fin n))} [DecidableEq T]
    (seq : ℕ → T) (hseq_dense : DenseRange seq) (r : ℝ)
    {G : Fin m → Fin n → ℝ} (hG : G ∈ dmGoodUpper seq r) {x : EuclideanSpace ℝ (Fin n)}
    (hxT : x ∈ T) : ‖dmPhi (Matrix.of G) x‖ ≤ r := by
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set L : ℝ := frobNorm (Matrix.of G) + 1
  have hL_pos : 0 < L := by
    have : 0 ≤ frobNorm (Matrix.of G) := Real.sqrt_nonneg _
    linarith
  obtain ⟨_, ⟨k, rfl⟩, hdist⟩ :=
    Metric.mem_closure_iff.1 (hseq_dense ⟨x, hxT⟩) (δ / L) (div_pos hδ hL_pos)
  rw [Subtype.dist_eq, dist_eq_norm] at hdist
  have hk := Set.mem_iInter.1 hG k
  simp only [Set.mem_ofPred, dmSupSeq] at hk
  have hmem : seq k ∈ dmSk seq k :=
    Finset.mem_image_of_mem seq (Finset.mem_range.2 (Nat.lt_succ_self k))
  have hseq_le : ‖dmPhi (Matrix.of G) (seq k).1‖ ≤ r :=
    (Finset.le_sup' (fun z : T => ‖dmPhi (Matrix.of G) z.1‖) hmem).trans hk
  have hdiff_le : ‖dmPhi (Matrix.of G) x - dmPhi (Matrix.of G) (seq k).1‖ ≤ δ := by
    rw [← dmPhi_sub_right]
    calc ‖dmPhi (Matrix.of G) (x - (seq k).1)‖
        ≤ frobNorm (Matrix.of G) * ‖x - (seq k).1‖ := dm_norm_dmPhi_le _ _
      _ ≤ L * ‖x - (seq k).1‖ :=
          mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) (norm_nonneg _)
      _ ≤ L * (δ / L) := mul_le_mul_of_nonneg_left hdist.le hL_pos.le
      _ = δ := mul_div_cancel₀ δ hL_pos.ne'
  have htri : ‖dmPhi (Matrix.of G) x‖ ≤
      ‖dmPhi (Matrix.of G) (seq k).1‖ + ‖dmPhi (Matrix.of G) x - dmPhi (Matrix.of G) (seq k).1‖ := by
    simpa [add_sub_cancel] using norm_add_le
      (dmPhi (Matrix.of G) (seq k).1) (dmPhi (Matrix.of G) x - dmPhi (Matrix.of G) (seq k).1)
  linarith

private lemma dm_exists_good_upper {m n : ℕ} (hm_pos : 0 < m)
    {T : Set (EuclideanSpace ℝ (Fin n))} (h0T : (0 : EuclideanSpace ℝ (Fin n)) ∈ T)
    {D ε w t : ℝ} (hD_pos : 0 < D) (hxD : ∀ x : T, ‖x.1‖ ≤ D)
    (hε0 : 0 < ε) (hw_pos : 0 < w) (hw : gaussianWidth T = (w : EReal))
    (hDm : D * Real.sqrt m ≤ ε / 100 * w)
    (ht_pos : 0 ≤ t) (ht_ge25 : 25 ≤ t) (hDt_eq : D * t = ε / 4 * w) :
    ∃ GoodUpper : Set (Fin m → Fin n → ℝ),
      MeasurableSet GoodUpper ∧
      (gaussianMatrix m n) GoodUpperᶜ ≤ (1 / 200 : ENNReal) ∧
      ∀ G ∈ GoodUpper, ∀ x ∈ T, ‖dmPhi (Matrix.of G) x‖ ≤ (1 + ε) * w := by
  classical
  have : Nonempty T := ⟨⟨0, h0T⟩⟩
  obtain ⟨Dset, hDcnt, hDdense⟩ := TopologicalSpace.exists_countable_dense T
  have hDne : (insert (⟨0, h0T⟩ : T) Dset).Nonempty := Set.insert_nonempty _ _
  obtain ⟨seq, hseq_range⟩ := (hDcnt.insert ⟨0, h0T⟩).exists_eq_range hDne
  have hseq_dense : DenseRange seq := by
    rw [DenseRange, ← hseq_range]
    exact hDdense.mono (Set.subset_insert _ _)
  exact ⟨dmGoodUpper seq ((1 + ε) * w),
    dmGoodUpper_measurable hxD seq ((1 + ε) * w),
    dmGoodUpper_tail hm_pos h0T hD_pos hxD hε0 hw_pos hw hDm ht_pos ht_ge25 hDt_eq seq,
    fun _ hG _ hxT => dmGoodUpper_det seq hseq_dense ((1 + ε) * w) hG hxT⟩

noncomputable def dmMinMax {m n : ℕ} {T : Set (EuclideanSpace ℝ (Fin n))}
    (U : Finset (EuclideanSpace ℝ (Fin m))) (S₀ : Finset T) (G : Fin m → Fin n → ℝ) : ℝ :=
  ⨅ u : U, ⨆ x : S₀, ∑ i : Fin m, ∑ j : Fin n, u.1 i * x.1.1 j * G i j

private lemma dmMinMax_neg_lip {m n : ℕ} {T : Set (EuclideanSpace ℝ (Fin n))}
    {D : ℝ} (hxD : ∀ x : T, ‖x.1‖ ≤ D)
    (U : Finset (EuclideanSpace ℝ (Fin m))) (hU1 : ∀ u ∈ U, ‖u‖ = 1) [Nonempty U]
    (S₀ : Finset T) [Nonempty S₀] (X Y : Fin m → Fin n → ℝ) :
    |(-dmMinMax U S₀ X) - (-dmMinMax U S₀ Y)| ≤ D * frobNorm (Matrix.of X - Matrix.of Y) := by
  rw [neg_sub_neg, abs_sub_comm]
  unfold dmMinMax
  refine dm_iInf_lip
    (fun (u : U) (G : Fin m → Fin n → ℝ) =>
      ⨆ x : S₀, ∑ i : Fin m, ∑ j : Fin n, u.1 i * x.1.1 j * G i j)
    X Y (D * frobNorm (Matrix.of X - Matrix.of Y)) fun u => ?_
  refine dm_iSup_lip
    (fun (x : S₀) (G : Fin m → Fin n → ℝ) =>
      ∑ i : Fin m, ∑ j : Fin n, u.1 i * x.1.1 j * G i j)
    X Y (D * frobNorm (Matrix.of X - Matrix.of Y)) fun x => ?_
  have heqX := (dm_inner_dmPhi (Matrix.of X) u.1 x.1.1).symm
  have heqY := (dm_inner_dmPhi (Matrix.of Y) u.1 x.1.1).symm
  simp only [Matrix.of_apply] at heqX heqY
  rw [heqX, heqY, ← inner_sub_right, ← dmPhi_sub_left]
  calc |⟪u.1, dmPhi (Matrix.of X - Matrix.of Y) x.1.1⟫|
      ≤ ‖u.1‖ * ‖dmPhi (Matrix.of X - Matrix.of Y) x.1.1‖ := abs_real_inner_le_norm _ _
    _ = ‖dmPhi (Matrix.of X - Matrix.of Y) x.1.1‖ := by rw [hU1 _ u.2, one_mul]
    _ ≤ frobNorm (Matrix.of X - Matrix.of Y) * ‖x.1.1‖ := dm_norm_dmPhi_le _ _
    _ ≤ frobNorm (Matrix.of X - Matrix.of Y) * D :=
        mul_le_mul_of_nonneg_left (hxD x.1) (Real.sqrt_nonneg _)
    _ = D * frobNorm (Matrix.of X - Matrix.of Y) := mul_comm _ _

private lemma dmMinMax_cont {m n : ℕ} {T : Set (EuclideanSpace ℝ (Fin n))}
    {D : ℝ} (hxD : ∀ x : T, ‖x.1‖ ≤ D)
    (U : Finset (EuclideanSpace ℝ (Fin m))) (hU1 : ∀ u ∈ U, ‖u‖ = 1) [Nonempty U]
    (S₀ : Finset T) [Nonempty S₀] :
    Continuous (dmMinMax U S₀) := by
  have hc := dm_continuous_of_lip (fun G => -dmMinMax U S₀ G) D (dmMinMax_neg_lip hxD U hU1 S₀)
  convert hc.neg using 1
  funext G
  exact (neg_neg _).symm

private lemma dm_exists_good_lower {m n : ℕ} (hm_pos : 0 < m)
    {T : Set (EuclideanSpace ℝ (Fin n))}
    {D ε w t : ℝ} (hD_pos : 0 < D) (hxD : ∀ x : T, ‖x.1‖ ≤ D)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hw_pos : 0 < w) (hw : gaussianWidth T = (w : EReal))
    (hDm : D * Real.sqrt m ≤ ε / 100 * w)
    (ht_pos : 0 ≤ t) (ht_ge25 : 25 ≤ t) (hDt_eq : D * t = ε / 4 * w) :
    ∃ GoodLower : Set (Fin m → Fin n → ℝ),
      MeasurableSet GoodLower ∧
      (gaussianMatrix m n) GoodLowerᶜ ≤ (1 / 200 : ENNReal) ∧
      ∀ G ∈ GoodLower,
        (∀ x ∈ T, ‖dmPhi (Matrix.of G) x‖ ≤ (1 + ε) * w) →
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ((1 - ε) * w) ⊆
          convexHull ℝ (dmPhi (Matrix.of G) '' T) := by
  have hr_lt : (1 - ε / 4) * w < w := by nlinarith [mul_pos hε0 hw_pos]
  obtain ⟨S₀, hS₀_ne, hS₀_gt⟩ := dm_width_exists_gt hw hr_lt
  obtain ⟨Fu, hFuS, hFufin, hFucov⟩ := Metric.finite_approx_of_totallyBounded
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin m)) 1).totallyBounded (ε / 8) (by positivity)
  set U := hFufin.toFinset with hUdef
  have hU1 : ∀ u ∈ U, ‖u‖ = 1 := by
    intro u hu
    rw [hUdef, Set.Finite.mem_toFinset] at hu
    simpa using hFuS hu
  have hcovU : ∀ v : EuclideanSpace ℝ (Fin m), ‖v‖ = 1 → ∃ u ∈ U, ‖v - u‖ ≤ ε / 8 := by
    intro v hv
    have hv' : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 := by simpa using hv
    obtain ⟨u, hu, huv⟩ := Set.mem_iUnion₂.1 (hFucov hv')
    refine ⟨u, by rw [hUdef, Set.Finite.mem_toFinset]; exact hu, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at huv; exact huv.le
  have hUne : Nonempty U := by
    obtain ⟨u, hu, -⟩ := hcovU (EuclideanSpace.single (⟨0, hm_pos⟩ : Fin m) 1) (by simp)
    exact ⟨⟨u, hu⟩⟩
  have : Nonempty S₀ := hS₀_ne.to_subtype
  have hMeasLower : MeasurableSet {G : Fin m → Fin n → ℝ | (1 - 51 / 100 * ε) * w ≤ dmMinMax U S₀ G} :=
    isClosed_le continuous_const (dmMinMax_cont hxD U hU1 S₀) |>.measurableSet
  have hLowerTail :
      (gaussianMatrix m n) {G : Fin m → Fin n → ℝ | (1 - 51 / 100 * ε) * w ≤ dmMinMax U S₀ G}ᶜ ≤
        (1 / 200 : ENNReal) := by
    have hconc := (gaussian_concentration (fun G => -dmMinMax U S₀ G) D hD_pos
      (dmMinMax_neg_lip hxD U hU1 S₀) t ht_pos).2
    have hExp_ge : (1 - 26 / 100 * ε) * w ≤ ∫ G, dmMinMax U S₀ G ∂(gaussianMatrix m n) := by
      have hGM := dm_lower_expectation hD_pos.le hxD U hU1 hUne S₀ hS₀_ne
      change _ ≤ ∫ G, dmMinMax U S₀ G ∂(gaussianMatrix m n) at hGM
      nlinarith [hDm, hS₀_gt]
    have hsub : {G : Fin m → Fin n → ℝ | (1 - 51 / 100 * ε) * w ≤ dmMinMax U S₀ G}ᶜ ⊆
        {G | (∫ Y, -dmMinMax U S₀ Y ∂(gaussianMatrix m n)) + D * t ≤ -dmMinMax U S₀ G} := by
      intro G hG
      simp only [Set.mem_compl_iff, Set.mem_ofPred, not_le] at hG
      simp only [Set.mem_ofPred, integral_neg]
      nlinarith [hExp_ge, hDt_eq]
    exact (measure_mono hsub).trans (hconc.trans (dm_exp_tail_le ht_ge25))
  refine ⟨{G | (1 - 51 / 100 * ε) * w ≤ dmMinMax U S₀ G}, hMeasLower, hLowerTail, ?_⟩
  intro G hGL hGU
  classical
  let F : Finset (EuclideanSpace ℝ (Fin m)) := S₀.image (fun x : T => dmPhi (Matrix.of G) x.1)
  have hF_ne : F.Nonempty := hS₀_ne.image _
  have hF_sub : (F : Set (EuclideanSpace ℝ (Fin m))) ⊆ dmPhi (Matrix.of G) '' T := by
    intro y hy
    rcases Finset.mem_image.1 hy with ⟨x, _, rfl⟩
    exact ⟨x.1, x.2, rfl⟩
  refine (dm_closedBall_subset_convexHull F hF_ne ((1 - ε) * w) ?_).trans (convexHull_mono hF_sub)
  intro v hv1
  obtain ⟨u, huU, hvu⟩ := hcovU v hv1
  have hb_inf : BddBelow (Set.range fun u' : U =>
      ⨆ x : S₀, ∑ i : Fin m, ∑ j : Fin n, u'.1 i * x.1.1 j * G i j) :=
    (Set.finite_range _).bddBelow
  have hu_ge : (1 - 51 / 100 * ε) * w ≤
      ⨆ x : S₀, ∑ i : Fin m, ∑ j : Fin n, u i * x.1.1 j * G i j :=
    hGL.trans (ciInf_le hb_inf ⟨u, huU⟩)
  have hex_x : ∃ x : S₀,
      (1 - 51 / 100 * ε) * w ≤ ∑ i : Fin m, ∑ j : Fin n, u i * x.1.1 j * G i j := by
    have hsup_eq : (⨆ x : S₀, ∑ i : Fin m, ∑ j : Fin n, u i * x.1.1 j * G i j) =
        S₀.sup' hS₀_ne (fun x : T => ∑ i : Fin m, ∑ j : Fin n, u i * x.1 j * G i j) :=
      (dm_sup'_eq_iSup S₀ hS₀_ne
        (fun x : T => ∑ i : Fin m, ∑ j : Fin n, u i * x.1 j * G i j)).symm
    rw [hsup_eq] at hu_ge
    obtain ⟨x₀, hx₀S, hx₀_eq⟩ := Finset.exists_mem_eq_sup' hS₀_ne
      (fun x : T => ∑ i : Fin m, ∑ j : Fin n, u i * x.1 j * G i j)
    exact ⟨⟨x₀, hx₀S⟩, hx₀_eq ▸ hu_ge⟩
  obtain ⟨x, hx_ge⟩ := hex_x
  have hyF : dmPhi (Matrix.of G) x.1.1 ∈ F := Finset.mem_image_of_mem _ x.2
  refine ⟨dmPhi (Matrix.of G) x.1.1, hyF, ?_⟩
  have hinner_u : ⟪u, dmPhi (Matrix.of G) x.1.1⟫ =
      ∑ i : Fin m, ∑ j : Fin n, u i * x.1.1 j * G i j :=
    dm_inner_dmPhi (Matrix.of G) u x.1.1
  have hnorm_y : ‖dmPhi (Matrix.of G) x.1.1‖ ≤ 2 * w := by
    have h1 : ‖dmPhi (Matrix.of G) x.1.1‖ ≤ (1 + ε) * w := hGU x.1.1 x.1.2
    nlinarith [hε1, hw_pos]
  have hdecomp : ⟪v, dmPhi (Matrix.of G) x.1.1⟫ =
      ⟪u, dmPhi (Matrix.of G) x.1.1⟫ - ⟪u - v, dmPhi (Matrix.of G) x.1.1⟫ := by
    rw [inner_sub_left]; ring
  have herr : ⟪u - v, dmPhi (Matrix.of G) x.1.1⟫ ≤ (ε / 8) * (2 * w) := by
    have hnuv : ‖u - v‖ ≤ ε / 8 := by rw [norm_sub_rev]; exact hvu
    exact (real_inner_le_norm _ _).trans
      (mul_le_mul hnuv hnorm_y (norm_nonneg _) (by positivity))
  rw [hdecomp, hinner_u]
  nlinarith [mul_pos hε0 hw_pos]

end DvoretzkyMilmanProof

open DvoretzkyMilmanProof

theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {m n : ℕ} (A : Ω → Matrix (Fin m) (Fin n) ℝ),
        IsGaussianMatrix P A →
        ∀ (T : Set (EuclideanSpace ℝ (Fin n))), Bornology.IsBounded T →
        (0 : EuclideanSpace ℝ (Fin n)) ∈ T →
        ∀ (ε : ℝ), 0 < ε → ε < 1 →
        ∀ (w : ℝ), gaussianWidth T = (w : EReal) →
        (m : ℝ) ≤ c * ε ^ 2 * stableDimension w (Metric.diam T) →
        (99 / 100 : ENNReal) ≤
          P {ω |
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ((1 - ε) * w) ⊆
                convexHull ℝ ((fun x : EuclideanSpace ℝ (Fin n) =>
                  (EuclideanSpace.equiv (Fin m) ℝ).symm ((A ω).mulVec x)) '' T) ∧
              convexHull ℝ ((fun x : EuclideanSpace ℝ (Fin n) =>
                  (EuclideanSpace.equiv (Fin m) ℝ).symm ((A ω).mulVec x)) '' T) ⊆
                Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ((1 + ε) * w)} := by
  refine ⟨1 / 10000, by norm_num, ?_⟩
  intro Ω _ P _ m n A hA T hTbdd h0T ε hε0 hε1 w hw hm_le
  have hw0 : 0 ≤ w := dm_width_nonneg h0T hw
  -- Case 1: m = 0 (EuclideanSpace ℝ (Fin 0) is a singleton)
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · have huniv : {ω : Ω |
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 0)) ((1 - ε) * w) ⊆
            convexHull ℝ (dmPhi (A ω) '' T) ∧
          convexHull ℝ (dmPhi (A ω) '' T) ⊆
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin 0)) ((1 + ε) * w)} = Set.univ := by
      ext ω
      simp only [Set.mem_univ, iff_true, Set.mem_ofPred]
      have h0_mem : (0 : EuclideanSpace ℝ (Fin 0)) ∈ convexHull ℝ (dmPhi (A ω) '' T) := by
        apply subset_convexHull ℝ (dmPhi (A ω) '' T)
        exact ⟨0, h0T, dmPhi_zero_right (A ω)⟩
      constructor
      · intro z _
        rwa [Subsingleton.elim z 0]
      · intro z _
        rw [Subsingleton.elim z 0, Metric.mem_closedBall, dist_self]
        exact mul_nonneg (by linarith) hw0
    change (99 / 100 : ENNReal) ≤ P {ω |
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 0)) ((1 - ε) * w) ⊆
          convexHull ℝ (dmPhi (A ω) '' T) ∧
        convexHull ℝ (dmPhi (A ω) '' T) ⊆
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin 0)) ((1 + ε) * w)}
    rw [huniv, measure_univ]
    have hle1 : (99 / 100 : ENNReal) = ENNReal.ofReal (99 / 100) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
    rw [hle1, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  -- Case 2: m ≥ 1
  set D := Metric.diam T
  have hD0 : 0 ≤ D := Metric.diam_nonneg
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_pos
  have hD_pos : 0 < D := by
    rcases hD0.lt_or_eq with hpos | heq
    · exact hpos
    · exfalso
      rw [← heq, stableDimension, zero_pow two_ne_zero, div_zero, mul_zero] at hm_le
      linarith
  have hw_pos : 0 < w := by
    rcases hw0.lt_or_eq with hpos | heq
    · exact hpos
    · exfalso
      rw [← heq, stableDimension, zero_pow two_ne_zero, zero_div, mul_zero] at hm_le
      linarith
  have hxD : ∀ x : T, ‖x.1‖ ≤ D := by
    intro x
    rw [← dist_zero_right]
    exact Metric.dist_le_diam_of_mem hTbdd x.2 h0T
  have hmD_sq : (m : ℝ) * D ^ 2 ≤ (ε / 100 * w) ^ 2 := by
    unfold stableDimension at hm_le
    have hD2 : 0 < D ^ 2 := sq_pos_of_pos hD_pos
    have hmul := mul_le_mul_of_nonneg_right hm_le hD2.le
    have hrhs : 1 / 10000 * ε ^ 2 * (w ^ 2 / D ^ 2) * D ^ 2 = (ε / 100 * w) ^ 2 := by
      field_simp [hD_pos.ne']; ring
    rwa [hrhs] at hmul
  have hDm : D * Real.sqrt m ≤ ε / 100 * w := by
    have h1 := Real.sqrt_le_sqrt hmD_sq
    rw [Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq hD_pos.le,
      Real.sqrt_sq (by positivity : 0 ≤ ε / 100 * w), mul_comm] at h1
    exact h1
  set t : ℝ := ε * w / (4 * D)
  have ht_pos : 0 ≤ t := by positivity
  have ht_ge25 : 25 ≤ t := by
    have hsqrtm_ge : (1 : ℝ) ≤ Real.sqrt m := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hm1
    have hD_le : D ≤ ε / 100 * w := by nlinarith [hDm, hsqrtm_ge]
    dsimp [t]
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hDt_eq : D * t = ε / 4 * w := by
    dsimp [t]; field_simp [hD_pos.ne']
  obtain ⟨hae_raw, hmap_raw⟩ := dm_isGaussianMatrix_map P A hA
  obtain ⟨GoodUpper, hMeasUpper, hUpperTail, hUpperDet⟩ :=
    dm_exists_good_upper hm_pos h0T hD_pos hxD hε0 hw_pos hw hDm ht_pos ht_ge25 hDt_eq
  obtain ⟨GoodLower, hMeasLower, hLowerTail, hLowerDet⟩ :=
    dm_exists_good_lower hm_pos hD_pos hxD hε0 hε1 hw_pos hw hDm ht_pos ht_ge25 hDt_eq
  let Good : Set (Fin m → Fin n → ℝ) := GoodUpper ∩ GoodLower
  have hMeasGood : MeasurableSet Good := hMeasUpper.inter hMeasLower
  have hGoodProb : (99 / 100 : ENNReal) ≤ (gaussianMatrix m n) Good :=
    dm_prob_inter_ge (gaussianMatrix m n) hUpperTail hLowerTail
  have hPullback : (gaussianMatrix m n) Good =
      P ((fun ω (i : Fin m) (j : Fin n) => A ω i j) ⁻¹' Good) := by
    rw [← hmap_raw, Measure.map_apply_of_aemeasurable hae_raw hMeasGood]
  rw [hPullback] at hGoodProb
  refine hGoodProb.trans (measure_mono fun ω hω => ?_)
  obtain ⟨hωU, hωL⟩ := hω
  have hMatrix_eq : Matrix.of (fun i j => A ω i j) = A ω := by ext i j; rfl
  have hIncUpper : convexHull ℝ (dmPhi (A ω) '' T) ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ((1 + ε) * w) := by
    refine convexHull_min ?_ (convex_closedBall _ _)
    rintro _ ⟨x, hxT, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, ← hMatrix_eq]
    exact hUpperDet _ hωU x hxT
  have hIncLower : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ((1 - ε) * w) ⊆
      convexHull ℝ (dmPhi (A ω) '' T) := by
    rw [← hMatrix_eq]
    exact hLowerDet _ hωL (hUpperDet _ hωU)
  exact ⟨hIncLower, hIncUpper⟩
