-- Prove2me | solution 1 for IAFTRL.lemma_G_26
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:50:32.781676+00:00
-- url     : https://prove2.me/submissions/7acb504e-0ea0-44b4-a070-7f1ffc17aa9e

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_G26_body
import Definitions.Def_IAFTRL_G26_run
import Definitions.Def_IAFTRL_G26_window
import Theorems.Thm_G26G_Sharp_runN_SI
import Theorems.Thm_G26G_Sharp_win_inv
import Theorems.Thm_G26G_Sharp_win_ok
import Theorems.Thm_G26G_Sharp_win_pos
import Theorems.Thm_G26G_Sharp_win_round
import Theorems.Thm_G26R_runK_FI
import Theorems.Thm_IAFTRL_lemma_G_12
import Theorems.Thm_IAFTRL_lemma_J_4

-- ===== Solutions.G2.Haus =====

/-! ### The `k`-dimensional Hausdorff measure of a compact convex set of affine dimension `k` -/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace G11

variable {d : ℕ}

theorem hausdorff_pos_fin {K : Set (Fin d → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) :
    0 < μH[(Module.finrank ℝ (vectorSpan ℝ K) : ℝ)] K ∧
      μH[(Module.finrank ℝ (vectorSpan ℝ K) : ℝ)] K < ∞ := by
  set V := vectorSpan ℝ K with hV
  set k := Module.finrank ℝ V with hk
  obtain ⟨b₀, hb₀⟩ := hne
  let bV := Module.finBasisOfFinrankEq ℝ V hk.symm
  let φ : (Fin k → ℝ) →ₗ[ℝ] (Fin d → ℝ) := V.subtype ∘ₗ bV.equivFun.symm.toLinearMap
  have hφinj : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro y z h
    exact bV.equivFun.symm.injective (Subtype.val_injective h)
  obtain ⟨ψ, hψ⟩ := φ.exists_leftInverse_of_injective hφinj
  have hψφ : ∀ y, ψ (φ y) = y := fun y => by
    simpa using LinearMap.congr_fun hψ y
  have hφsurj : ∀ v ∈ V, ∃ y, φ y = v := fun v hv =>
    ⟨bV.equivFun ⟨v, hv⟩, by simp [φ]⟩
  let L : (Fin k → ℝ) → (Fin d → ℝ) := fun y => b₀ + φ y
  let G : (Fin d → ℝ) → (Fin k → ℝ) := fun x => ψ (x - b₀)
  have hLG : ∀ x ∈ K, L (G x) = x := by
    intro x hx
    obtain ⟨y, hy⟩ := hφsurj (x - b₀) (vsub_mem_vectorSpan ℝ hx hb₀)
    simp only [L, G, ← hy, hψφ]
    rw [hy]; abel
  have hKimg : L '' (G '' K) = K := by
    rw [Set.image_image]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; show L (G y) ∈ K; rw [hLG y hy]; exact hy
    · intro hx; exact ⟨x, hx, hLG x hx⟩
  -- Lipschitz constants
  obtain ⟨Kφ, hLφ⟩ : ∃ C, LipschitzWith C φ :=
    ⟨_, by simpa using (LinearMap.toContinuousLinearMap φ).lipschitz⟩
  obtain ⟨Kψ, hLψ⟩ : ∃ C, LipschitzWith C ψ :=
    ⟨_, by simpa using (LinearMap.toContinuousLinearMap ψ).lipschitz⟩
  have hL : LipschitzWith Kφ L := LipschitzWith.of_dist_le_mul fun y z => by
    simp only [L]; rw [dist_add_left]; exact hLφ.dist_le_mul _ _
  have hG : LipschitzWith Kψ G := LipschitzWith.of_dist_le_mul fun x y => by
    simp only [G]; rw [← dist_sub_right x y b₀]; exact hLψ.dist_le_mul _ _
  have hvol : (μH[(k : ℝ)] : Measure (Fin k → ℝ)) = volume := by
    simpa using (hausdorffMeasure_pi_real (ι := Fin k))
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  -- the image `G '' K` is compact, convex and full-dimensional
  have hGK : IsCompact (G '' K) := hK.image hG.continuous
  have hGconv : Convex ℝ (G '' K) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
    refine ⟨a • x + b • y, hconv hx hy ha hb hab, ?_⟩
    simp only [G]
    have : a • x + b • y - b₀ = a • (x - b₀) + b • (y - b₀) := by
      rw [smul_sub, smul_sub]
      nth_rewrite 1 [show b₀ = (a + b) • b₀ by rw [hab, one_smul]]
      rw [add_smul]; abel
    rw [this, map_add, map_smul, map_smul]
  have hspan : vectorSpan ℝ (G '' K) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hmem : ∀ w ∈ V, ψ w ∈ vectorSpan ℝ (G '' K) := by
      intro w hw
      rw [hV, vectorSpan_def] at hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_vsub.1 hw
        have : ψ (x -ᵥ y) = G x -ᵥ G y := by
          simp only [G, vsub_eq_sub]
          rw [← map_sub]; congr 1; abel
        rw [this]
        exact vsub_mem_vectorSpan ℝ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
    have := hmem (φ z) (by
      simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply]; exact Submodule.coe_mem _)
    rwa [hψφ] at this
  have hGne : (G '' K).Nonempty := ⟨G b₀, b₀, hb₀, rfl⟩
  have haff : affineSpan ℝ (G '' K) = ⊤ :=
    (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ _ _ hGne).2 hspan
  obtain ⟨z, hz⟩ := (hGconv.interior_nonempty_iff_affineSpan_eq_top).2 haff
  have hvolpos : 0 < volume (G '' K) :=
    lt_of_lt_of_le (isOpen_interior.measure_pos volume ⟨z, hz⟩) (measure_mono interior_subset)
  constructor
  · -- positivity
    have h1 := hG.hausdorffMeasure_image_le hk0 K
    rw [hvol] at h1
    by_contra h0
    push Not at h0
    have h0' : μH[(k : ℝ)] K = 0 := nonpos_iff_eq_zero.1 h0
    rw [h0', mul_zero] at h1
    exact absurd (nonpos_iff_eq_zero.1 h1) hvolpos.ne'
  · -- finiteness
    have h1 := hL.hausdorffMeasure_image_le hk0 (G '' K)
    rw [hKimg, hvol] at h1
    refine lt_of_le_of_lt h1 (ENNReal.mul_lt_top ?_ hGK.measure_lt_top)
    exact ENNReal.rpow_lt_top_of_nonneg hk0 ENNReal.coe_ne_top

end G11


-- ===== Solutions.T31.Geo =====

/-! ### General tools for the Theorem 3.1 leaves -/

open MeasureTheory Matrix Set

namespace T31

/-! #### Quadratic forms of positive definite matrices -/

/-! #### Convex hulls of compact sets in finite dimension -/

section Hull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- combinations of `n` points of `K` -/
def combSet (K : Set E) (n : ℕ) : Set E :=
  (fun p : (Fin n → ℝ) × (Fin n → E) => ∑ i, p.1 i • p.2 i) ''
    (stdSimplex ℝ (Fin n) ×ˢ Set.univ.pi (fun _ => K))

lemma combSet_succ {K : Set E} {z₀ : E} (hz₀ : z₀ ∈ K) (n : ℕ) :
    combSet K n ⊆ combSet K (n + 1) := by
  rintro x ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
  refine ⟨⟨Fin.snoc w 0, Fin.snoc z z₀⟩, ⟨⟨fun i => ?_, ?_⟩, fun i _ => ?_⟩, ?_⟩
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simpa using hw.1 j
  · simp [Fin.sum_univ_castSucc, hw.2]
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hz₀
    · simpa using hz j (mem_univ _)
  · simp [Fin.sum_univ_castSucc]

lemma combSet_mono {K : Set E} (hK : K.Nonempty) {k N : ℕ} (h : k ≤ N) :
    combSet K k ⊆ combSet K N := by
  obtain ⟨z₀, hz₀⟩ := hK
  induction N, h using Nat.le_induction with
  | base => exact le_rfl
  | succ N _ ih => exact ih.trans (combSet_succ hz₀ N)

lemma combSet_sub_hull (K : Set E) (n : ℕ) : combSet K n ⊆ convexHull ℝ K := by
  rintro x ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
  exact (convex_convexHull ℝ K).sum_mem (fun i _ => hw.1 i) hw.2
    (fun i _ => subset_convexHull ℝ K (hz i (mem_univ _)))

variable [FiniteDimensional ℝ E]

lemma hull_sub_combSet (K : Set E) :
    convexHull ℝ K ⊆ combSet K (Module.finrank ℝ E + 1) := by
  intro x hx
  obtain ⟨ι, _, z, w, hzK, hai, hw0, hw1, hsum⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hcard : Fintype.card ι ≤ Module.finrank ℝ E + 1 :=
    hai.card_le_finrank_succ.trans (Nat.succ_le_succ (Submodule.finrank_le _))
  have hne : K.Nonempty := convexHull_nonempty_iff.1 ⟨x, hx⟩
  refine combSet_mono hne hcard ?_
  let σ := Fintype.equivFin ι
  refine ⟨⟨w ∘ σ.symm, z ∘ σ.symm⟩, ⟨⟨fun i => (hw0 _).le, ?_⟩, fun i _ => hzK ⟨_, rfl⟩⟩, ?_⟩
  · simpa [Function.comp] using (Equiv.sum_comp σ.symm w).trans hw1
  · simp only [Function.comp]
    rw [← hsum]
    exact Equiv.sum_comp σ.symm (fun i => w i • z i)

lemma isCompact_convexHull_of {K : Set E} (hK : IsCompact K) : IsCompact (convexHull ℝ K) := by
  have : convexHull ℝ K = combSet K (Module.finrank ℝ E + 1) :=
    (hull_sub_combSet K).antisymm (combSet_sub_hull K _)
  rw [this]
  refine IsCompact.image ((isCompact_stdSimplex ℝ (Fin _)).prod (isCompact_univ_pi fun _ => hK)) ?_
  fun_prop

end Hull

/-! #### Integrals against measures supported on a compact set -/

variable {d : ℕ}

/-! #### Discrete measures -/

section Disc

variable {ι : Type*} [Fintype ι]

/-- the discrete measure `∑ r_i δ_{x_i}` -/
noncomputable def disc (r : ι → ℝ) (x : ι → Fin d → ℝ) : Measure (Fin d → ℝ) :=
  ∑ i, ENNReal.ofReal (r i) • Measure.dirac (x i)

instance disc_finite (r : ι → ℝ) (x : ι → Fin d → ℝ) : IsFiniteMeasure (disc r x) := by
  refine ⟨?_⟩
  simp only [disc, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.ofReal_lt_top

end Disc

/-! #### The gauge of `𝒮 = Conv(𝒜 ∪ -𝒜)` dominates the sup norm -/

lemma Sset_sub_ball {𝒜 : Set (Fin d → ℝ)} (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) :
    IAFTRL.Sset 𝒜 ⊆ Metric.closedBall 0 1 := by
  refine convexHull_min ?_ (convex_closedBall 0 1)
  have h1 : ∀ a ∈ 𝒜, ‖a‖ ≤ 1 := by
    intro a ha
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    have : a i * a i ≤ a ⬝ᵥ a :=
      Finset.single_le_sum (f := fun j => a j * a j) (fun j _ => mul_self_nonneg _)
        (Finset.mem_univ i)
    rw [Real.norm_eq_abs]
    have := hball a ha
    nlinarith [abs_mul_abs_self (a i), abs_nonneg (a i)]
  rintro x (hx | hx)
  · simpa using h1 x hx
  · have := h1 (-x) (by simpa using hx)
    simpa [norm_neg] using this

lemma Sset_nhds {𝒜 : Set (Fin d → ℝ)} (hne : 𝒜.Nonempty) (hspan : Submodule.span ℝ 𝒜 = ⊤) :
    IAFTRL.Sset 𝒜 ∈ nhds (0 : Fin d → ℝ) := by
  set S := IAFTRL.Sset 𝒜 with hSdef
  have hconv : Convex ℝ S := convex_convexHull ℝ _
  have hsymm : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    have h' : -(𝒜 ∪ -𝒜) = 𝒜 ∪ -𝒜 := by
      ext y; simp only [Set.mem_neg, Set.mem_union, neg_neg]; tauto
    have : -x ∈ -convexHull ℝ (𝒜 ∪ -𝒜) := by rw [Set.neg_mem_neg]; exact hx
    rw [← convexHull_neg, h'] at this
    exact this
  have haff : affineSpan ℝ S = ⊤ := by
    obtain ⟨a₀, ha₀⟩ := hne
    have hSne : S.Nonempty := ⟨a₀, subset_convexHull ℝ _ (Or.inl ha₀)⟩
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ _ _ hSne, eq_top_iff, ← hspan]
    refine Submodule.span_le.2 fun a ha => ?_
    have hpa : a ∈ S := subset_convexHull ℝ _ (Or.inl ha)
    have hna : -a ∈ S := subset_convexHull ℝ _ (Or.inr (by simpa using ha))
    have h2 := vsub_mem_vectorSpan ℝ hpa hna
    rw [vsub_eq_sub, sub_neg_eq_add] at h2
    have := Submodule.smul_mem _ (1 / 2 : ℝ) h2
    have e : (1 / 2 : ℝ) • (a + a) = a := by
      rw [← two_smul ℝ a, smul_smul]; norm_num
    rwa [e] at this
  obtain ⟨x, hx⟩ := (hconv.interior_nonempty_iff_affineSpan_eq_top).2 haff
  have hxn : S ∈ nhds x := mem_interior_iff_mem_nhds.1 hx
  have hx' : -x ∈ interior S := by
    rw [mem_interior_iff_mem_nhds]
    have : (fun y : Fin d → ℝ => -y) ⁻¹' S ∈ nhds (-x) :=
      continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hxn)
    exact Filter.mem_of_superset this fun y hy => by simpa using hsymm _ hy
  have h0 : (0 : Fin d → ℝ) ∈ interior S := by
    have := hconv.interior hx hx' (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa using this
  exact mem_interior_iff_mem_nhds.1 h0

lemma norm_le_sNorm {𝒜 : Set (Fin d → ℝ)} (hne : 𝒜.Nonempty) (hspan : Submodule.span ℝ 𝒜 = ⊤)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (x : Fin d → ℝ) : ‖x‖ ≤ IAFTRL.sNorm 𝒜 x := by
  have := le_gauge_of_subset_closedBall (absorbent_nhds_zero (Sset_nhds hne hspan)) zero_le_one
    (Sset_sub_ball hball) (x := x)
  simpa [IAFTRL.sNorm] using this

end T31


-- ===== Solutions.G1.Geo2 =====

/-! ### Generator geometry helpers -/

open MeasureTheory ProbabilityTheory Set IAFTRL

namespace G1L

variable {d : ℕ}

lemma Sset_gen {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IsGenerator 𝒜 ℬ) : Sset 𝒜 = Sset ℬ := by
  unfold Sset
  apply le_antisymm
  · refine convexHull_min ?_ (convex_convexHull ℝ _)
    rintro x (hx | hx)
    · exact convexHull_mono subset_union_left (hgen.2 hx)
    · have h1 : -x ∈ convexHull ℝ ℬ := hgen.2 hx
      have h2 : x ∈ convexHull ℝ (-ℬ) := by
        rw [convexHull_neg, Set.mem_neg]; exact h1
      exact convexHull_mono subset_union_right h2
  · exact convexHull_mono (union_subset_union hgen.1 (Set.neg_subset_neg.2 hgen.1))

lemma sNorm_gen {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IsGenerator 𝒜 ℬ) (x : Fin d → ℝ) :
    sNorm 𝒜 x = sNorm ℬ x := by
  unfold sNorm; rw [Sset_gen hgen]

lemma Kset_gen {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IsGenerator 𝒜 ℬ) : Kset 𝒜 = Kset ℬ :=
  ((convexHull_mono hgen.1).antisymm (convexHull_min hgen.2 (convex_convexHull ℝ ℬ))).symm

lemma exists_ne {ℬ : Set (Fin d → ℝ)} (hk : 1 ≤ kdim ℬ) (a : Fin d → ℝ) : ∃ b ∈ ℬ, b ≠ a := by
  by_contra h
  push Not at h
  have h1 : ℬ ⊆ {a} := fun b hb => h b hb
  have h2 : Kset ℬ ⊆ {a} := by
    unfold Kset; exact (convexHull_mono h1).trans (by rw [convexHull_singleton])
  have hsub : (Kset ℬ).Subsingleton := Set.subsingleton_singleton.anti h2
  have := (vectorSpan_eq_bot_iff_subsingleton ℝ).2 hsub
  unfold kdim at hk
  rw [this, finrank_bot] at hk
  omega

end G1L


-- ===== Solutions.G2.Meas =====

/-! ### Measurability of the reconstruction and of the exponential weights -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace G2M

variable {d : ℕ}

open Classical in
/-- Markov-ification of a measure -/
noncomputable def mk (ν : Measure (Fin d → ℝ)) : Measure (Fin d → ℝ) :=
  if ν univ = 1 then ν else Measure.dirac 0

lemma measurable_mk : Measurable (mk (d := d)) := by
  classical
  have hs : MeasurableSet {ν : Measure (Fin d → ℝ) | ν univ = 1} :=
    (Measure.measurable_coe MeasurableSet.univ) (measurableSet_singleton 1)
  exact Measurable.piecewise hs measurable_id measurable_const

instance mk_prob (ν : Measure (Fin d → ℝ)) : IsProbabilityMeasure (mk ν) := by
  unfold mk
  split_ifs with h
  · exact ⟨h⟩
  · infer_instance

lemma mk_eq (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν] : mk ν = ν := by
  unfold mk; rw [if_pos measure_univ]

/-- the Markov kernel `ν ↦ mk ν` -/
noncomputable def kmk : Kernel (Measure (Fin d → ℝ)) (Fin d → ℝ) :=
  ⟨mk, measurable_mk⟩

instance : IsMarkovKernel (kmk (d := d)) := ⟨fun ν => mk_prob ν⟩

/-- measurability of `ν ↦ ∫ f d(mk ν)` -/
lemma measurable_integral_mk {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) :
    Measurable fun ν : Measure (Fin d → ℝ) => ∫ x, f x ∂(mk ν) := by
  have := (hf.stronglyMeasurable.comp_measurable
    (measurable_snd (α := Measure (Fin d → ℝ)) (β := Fin d → ℝ))).integral_kernel_prod_right'
    (κ := kmk (d := d))
  exact this.measurable

/-- the design matrix entries of `mk ν` -/
noncomputable def cM (ν : Measure (Fin d → ℝ)) : Fin d → Fin d → ℝ :=
  fun i j => ∫ x, x i * x j ∂(mk ν)

lemma measurable_cM : Measurable (cM (d := d)) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  exact measurable_integral_mk (by fun_prop)

/-- entries of the inverse of a matrix given by its entries -/
noncomputable def invE (A : Fin d → Fin d → ℝ) : Fin d → Fin d → ℝ :=
  fun i j => (Matrix.of A)⁻¹ i j

lemma measurable_invE : Measurable (invE (d := d)) := by
  have hdet : Continuous fun A : Fin d → Fin d → ℝ => (Matrix.of A).det :=
    (continuous_id (X := Matrix (Fin d) (Fin d) ℝ)).matrix_det
  have hadj : Continuous fun A : Fin d → Fin d → ℝ => (Matrix.of A).adjugate :=
    (continuous_id (X := Matrix (Fin d) (Fin d) ℝ)).matrix_adjugate
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  have : (fun A : Fin d → Fin d → ℝ => invE A i j) =
      fun A => ((Matrix.of A).det)⁻¹ * (Matrix.of A).adjugate i j := by
    funext A
    simp only [invE, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [this]
  have h1 : Measurable fun A : Fin d → Fin d → ℝ => (Matrix.of A).adjugate i j :=
    ((continuous_apply j).comp ((continuous_apply i).comp hadj)).measurable
  exact (hdet.measurable.inv).mul h1

/-- the reconstruction vector `v_x(ν) = M(ν)⁻¹ x` computed from `mk ν` -/
noncomputable def V (ν : Measure (Fin d → ℝ)) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => ∑ j, invE (cM ν) i j * x j

lemma measurable_V : Measurable fun z : Measure (Fin d → ℝ) × (Fin d → ℝ) => V z.1 z.2 := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Finset.measurable_sum _ fun j _ => ?_
  have h1 : Measurable fun z : Measure (Fin d → ℝ) × (Fin d → ℝ) => invE (cM z.1) i j :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      (measurable_invE.comp (measurable_cM.comp measurable_fst)))
  exact h1.mul ((measurable_pi_apply j).comp measurable_snd)

lemma measurable_V_comp {α : Type*} {mα : MeasurableSpace α} {f : α → Measure (Fin d → ℝ)}
    {g : α → Fin d → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => V (f a) (g a) := by
  have h2 := (measurable_V (d := d)).comp (hf.prodMk hg)
  convert h2 using 1
  funext a
  simp only [Function.comp_apply]

lemma cM_eq (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν] :
    Matrix.of (cM ν) = IAFTRL.designMat ν := by
  ext i j; simp [cM, IAFTRL.designMat, mk_eq]

lemma V_eq (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν] (x : Fin d → ℝ) :
    V ν x = IAFTRL.gv ν x := by
  funext i
  simp only [V, IAFTRL.gv, IAFTRL.gM, invE, ← cM_eq ν, Matrix.mulVec, dotProduct]

end G2M


-- ===== Solutions.G2.Run =====

/-! ### Basic facts about GIA-FTRL runs -/

open MeasureTheory ProbabilityTheory Set IAFTRL
open scoped ENNReal

namespace G2R

variable {d : ℕ}

/-! #### Geometry -/

lemma Kset_compact {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) : IsCompact (Kset ℬ) :=
  T31.isCompact_convexHull_of hℬ

/-! #### Runs -/

section Run

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝒜 ℬ : Set (Fin d → ℝ)}
  {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

lemma hist_mono {s t : ℕ} (h : s ≤ t) : R.hist s ≤ R.hist t := by
  unfold GRun.hist
  exact iSup₂_mono' fun i hi => ⟨i, lt_of_lt_of_le hi h, le_rfl⟩

lemma meas_hist_triple {s t : ℕ} (h : s < t) :
    Measurable[R.hist t] (fun ω => (R.X s ω, R.A s ω, R.Y s ω)) := by
  refine Measurable.of_comap_le ?_
  exact le_iSup₂ (f := fun s (_ : s < t) =>
    MeasurableSpace.comap (fun ω => (R.X s ω, R.A s ω, R.Y s ω)) inferInstance) s h

lemma meas_hist_Y {s t : ℕ} (hs : s < t) : Measurable[R.hist t] (R.Y s) := by
  refine Measurable.of_comap_le ?_
  have h1 : MeasurableSpace.comap (R.Y s) inferInstance ≤
      MeasurableSpace.comap (fun ω => (R.X s ω, R.A s ω, R.Y s ω)) inferInstance := by
    have h2 : Measurable fun z : (Fin d → ℝ) × (Fin d → ℝ) × ℝ => z.2.2 := measurable_snd.snd
    rw [show R.Y s = (fun z : (Fin d → ℝ) × (Fin d → ℝ) × ℝ => z.2.2) ∘
      (fun ω => (R.X s ω, R.A s ω, R.Y s ω)) from rfl, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono h2.comap_le
  exact h1.trans (le_iSup₂ (f := fun s (_ : s < t) =>
    MeasurableSpace.comap (fun ω => (R.X s ω, R.A s ω, R.Y s ω)) inferInstance) s hs)

lemma feas (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (ω : Ω) :
    IsFeasible3_6 ℬ e (t + 1) (R.cumEst t ω) (R.p t ω) :=
  ((hR t ht).2.1.2 ω).1

lemma p_prob (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (ω : Ω) :
    IsProbabilityMeasure (R.p t ω) :=
  (feas hR ht ω).1

lemma p_supp (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (ω : Ω) :
    R.p t ω (Kset ℬ)ᶜ = 0 :=
  (feas hR ht ω).2.1

lemma thetaHat_eq (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {s : ℕ} (hs : s < T) (ω : Ω) :
    R.thetaHat s ω = R.Y s ω • G2M.V (R.p s ω) (R.X s ω) := by
  haveI := p_prob hR hs ω
  rw [GRun.thetaHat, G2M.V_eq]

lemma meas_thetaHat (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {s t : ℕ} (hs : s < t) (ht : t ≤ T) :
    Measurable[R.hist t] (R.thetaHat s) := by
  have hp0 : Measurable[R.hist s] (R.p s) := (hR s (by omega)).2.1.1
  have hp : Measurable[R.hist t] (R.p s) := hp0.mono (hist_mono hs.le) le_rfl
  have htr := meas_hist_triple (R := R) hs
  have hX : Measurable[R.hist t] (R.X s) := measurable_fst.comp htr
  have hY : Measurable[R.hist t] (R.Y s) := meas_hist_Y hs
  have hV : Measurable[R.hist t] fun ω => G2M.V (R.p s ω) (R.X s ω) :=
    G2M.measurable_V_comp hp hX
  have hm : Measurable[R.hist t] fun ω => R.Y s ω • G2M.V (R.p s ω) (R.X s ω) := hY.smul hV
  have : R.thetaHat s = fun ω => R.Y s ω • G2M.V (R.p s ω) (R.X s ω) :=
    funext (thetaHat_eq hR (by omega))
  rw [this]
  exact hm

lemma meas_cumEst (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t ≤ T) :
    Measurable[R.hist t] (R.cumEst t) := by
  unfold GRun.cumEst
  exact Finset.measurable_sum _ fun s hs => meas_thetaHat hR (Finset.mem_range.1 hs) ht

lemma G_le (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) : R.G t ≤ mΩ :=
  (hR t ht).1.2.2.2.2.1

lemma hist_le_G (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) : R.hist t ≤ R.G t :=
  (hR t ht).1.2.2.2.2.2.1

end Run

/-! #### Deterministic range bounds -/

lemma gB_pos : 0 < gB d := by unfold gB; positivity

section Bounds

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝒜 ℬ : Set (Fin d → ℝ)}
  {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

end Bounds

end G2R


-- ===== Solutions.G26.J11 =====

/-! ### Lemma J.11: uniform estimates for affine functions on a convex body -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace J11

variable {d : ℕ}

section

variable {D : Set (Fin d → ℝ)} (hD : IsCompact D) (hconv : Convex ℝ D) (hne : D.Nonempty)
include hD hconv hne

lemma haus_pos_fin : 0 < μH[(rdim D : ℝ)] D ∧ μH[(rdim D : ℝ)] D < ∞ :=
  G11.hausdorff_pos_fin hD hconv hne

lemma nvol_prob : IsProbabilityMeasure (nvol D) := by
  obtain ⟨h1, h2⟩ := haus_pos_fin hD hconv hne
  exact cond_isProbabilityMeasure_of_finite h1.ne' h2.ne

omit hconv hne in
lemma nvol_supp : nvol D Dᶜ = 0 := by
  unfold nvol
  rw [cond_apply hD.isClosed.measurableSet, Set.inter_compl_self, measure_empty, mul_zero]

/-- a homothetic copy of `D` with ratio `λ ∈ (0, 1]` has normalized volume `λ^r` -/
lemma nvol_hom {x0 : Fin d → ℝ} (hx0 : x0 ∈ D) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    AffineMap.homothety x0 r '' D ⊆ D ∧
    nvol D (AffineMap.homothety x0 r '' D) = ENNReal.ofReal (r ^ rdim D) := by
  obtain ⟨hHpos, hHfin⟩ := haus_pos_fin hD hconv hne
  have hhom : ∀ x, AffineMap.homothety x0 r x = r • (x - x0) + x0 := fun x => by
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  have hsub : AffineMap.homothety x0 r '' D ⊆ D := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hhom]
    have := hconv hx0 hx (by linarith : (0 : ℝ) ≤ 1 - r) hr0.le (by ring)
    convert this using 1
    rw [smul_sub, sub_smul, one_smul]; abel
  refine ⟨hsub, ?_⟩
  set c : ℝ≥0∞ := ((‖r‖₊ ^ (rdim D : ℝ) : ℝ≥0) : ℝ≥0∞) with hc
  have hlam : nvol D (AffineMap.homothety x0 r '' D) = c := by
    unfold nvol
    rw [cond_apply hD.isClosed.measurableSet, Set.inter_eq_right.2 hsub,
      hausdorffMeasure_homothety_image (Nat.cast_nonneg _) x0 hr0.ne', ENNReal.smul_def,
      smul_eq_mul, ← mul_assoc, mul_comm _ (c : ℝ≥0∞), mul_assoc,
      ENNReal.inv_mul_cancel hHpos.ne' hHfin.ne, mul_one]
  rw [hlam, hc, ← ENNReal.ofReal_coe_nnreal]
  congr 1
  rw [NNReal.coe_rpow, coe_nnnorm, Real.norm_eq_abs, abs_of_pos hr0, Real.rpow_natCast]

/-- **The contraction lower bound**: if `g ≥ c ≥ 0` on the `λ`-contraction of `D` toward
`x0`, then `∫ g dσ ≥ λ^r c` -/
lemma contr_lb {x0 : Fin d → ℝ} (hx0 : x0 ∈ D) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    {g : (Fin d → ℝ) → ℝ} (hg : Integrable g (nvol D)) (hg0 : ∀ x ∈ D, 0 ≤ g x) {c : ℝ}
    (hc : 0 ≤ c) (hgc : ∀ x ∈ D, c ≤ g (AffineMap.homothety x0 r x)) :
    r ^ rdim D * c ≤ ∫ x, g x ∂(nvol D) := by
  haveI := nvol_prob hD hconv hne
  obtain ⟨hsub, hvol⟩ := nvol_hom hD hconv hne hx0 hr0 hr1
  set H := AffineMap.homothety x0 r '' D with hH
  have hHm : MeasurableSet H :=
    (hD.image (AffineMap.homothety x0 r).continuous_of_finiteDimensional).isClosed.measurableSet
  have hsupp := nvol_supp hD
  have h1 : ∫ x, H.indicator (fun _ => c) x ∂(nvol D) ≤ ∫ x, g x ∂(nvol D) := by
    refine integral_mono_ae ((integrable_const c).indicator hHm) hg ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hsupp] with x hx
    simp only [Set.mem_compl_iff, not_not] at hx
    by_cases hxH : x ∈ H
    · rw [indicator_of_mem hxH]
      obtain ⟨y, hy, rfl⟩ := hxH
      exact hgc y hy
    · rw [indicator_of_notMem hxH]; exact hg0 x hx
  rw [integral_indicator hHm, setIntegral_const, smul_eq_mul, measureReal_def, hvol,
    ENNReal.toReal_ofReal (pow_nonneg hr0.le _)] at h1
  exact h1

end

/-- affine functions along a homothety -/
lemma aff_hom' (v : Fin d → ℝ) (c : ℝ) (x0 x : Fin d → ℝ) (r : ℝ) :
    AffineMap.homothety x0 r x ⬝ᵥ v + c = (1 - r) * (x0 ⬝ᵥ v + c) + r * (x ⬝ᵥ v + c) := by
  rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  simp only [add_dotProduct, smul_dotProduct, sub_dotProduct, smul_eq_mul]; ring

section Ineq

variable {D : Set (Fin d → ℝ)} (hD : IsCompact D) (hconv : Convex ℝ D) (hne : D.Nonempty)
include hD hconv hne

lemma cont_aff (v : Fin d → ℝ) (c : ℝ) : Continuous fun x : Fin d → ℝ => x ⬝ᵥ v + c := by
  simp only [dotProduct]; fun_prop

/-- **(J.17)** `R^p ≤ 2^p 4^r ∫ |f|^p dσ` at a maximizer of `|f|` -/
theorem J17 (v : Fin d → ℝ) (c : ℝ) {x0 : Fin d → ℝ} (hx0 : x0 ∈ D)
    (hmax : ∀ x ∈ D, |x ⬝ᵥ v + c| ≤ |x0 ⬝ᵥ v + c|) (p : ℕ) :
    |x0 ⬝ᵥ v + c| ^ p ≤ 2 ^ p * 4 ^ rdim D * ∫ x, |x ⬝ᵥ v + c| ^ p ∂(nvol D) := by
  haveI := nvol_prob hD hconv hne
  set R := |x0 ⬝ᵥ v + c| with hR
  have hR0 : 0 ≤ R := abs_nonneg _
  have hfc := (cont_aff hD hconv hne v c).abs.pow p
  have hint : Integrable (fun x => |x ⬝ᵥ v + c| ^ p) (nvol D) := by
    obtain ⟨Cb, hCb⟩ := hD.exists_bound_of_continuousOn hfc.continuousOn
    refine Integrable.of_bound hfc.aestronglyMeasurable Cb ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (nvol_supp hD)] with x hx
    simp only [Set.mem_compl_iff, not_not] at hx
    exact hCb x hx
  have h := contr_lb hD hconv hne hx0 (r := 1 / 4) (by norm_num) (by norm_num) hint
    (fun x _ => by positivity) (c := (R / 2) ^ p) (by positivity) (fun x hx => by
      refine pow_le_pow_left₀ (by positivity) ?_ p
      rw [aff_hom']
      have h1 := hmax x hx
      have h2 := abs_le.1 h1
      rcases le_total 0 (x0 ⬝ᵥ v + c) with h0 | h0
      · rw [hR, abs_of_nonneg h0] at h2 ⊢
        rw [abs_of_nonneg (by nlinarith)]; nlinarith
      · rw [hR, abs_of_nonpos h0] at h2 ⊢
        rw [abs_of_nonpos (by nlinarith)]; nlinarith)
  have e : R ^ p = 2 ^ p * 4 ^ rdim D * ((1 / 4) ^ rdim D * (R / 2) ^ p) := by
    rw [div_pow, div_pow, one_pow]; field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- **Inverse contraction**: for `f > 0` on `D` with `f(x0) = m` and `f ≤ R`, every
`λ ∈ (0, 1]` gives `λ^r ((1−λ)m + λR)^{−p} ≤ ∫ f^{−p} dσ` -/
theorem inv_contr (v : Fin d → ℝ) (c : ℝ) {x0 : Fin d → ℝ} (hx0 : x0 ∈ D)
    (hpos : ∀ x ∈ D, 0 < x ⬝ᵥ v + c) {R : ℝ} (hR : ∀ x ∈ D, x ⬝ᵥ v + c ≤ R)
    {l : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) (p : ℕ) :
    l ^ rdim D * (((1 - l) * (x0 ⬝ᵥ v + c) + l * R) ^ p)⁻¹ ≤
      ∫ x, ((x ⬝ᵥ v + c) ^ p)⁻¹ ∂(nvol D) := by
  haveI := nvol_prob hD hconv hne
  have hfc := cont_aff hD hconv hne v c
  obtain ⟨xm, hxm, hmin⟩ := hD.exists_isMinOn hne hfc.continuousOn
  have hm0 : 0 < xm ⬝ᵥ v + c := hpos xm hxm
  have hint : Integrable (fun x => ((x ⬝ᵥ v + c) ^ p)⁻¹) (nvol D) := by
    refine Integrable.of_bound ((hfc.measurable.pow_const p).inv).aestronglyMeasurable
      (((xm ⬝ᵥ v + c) ^ p)⁻¹) ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (nvol_supp hD)] with x hx
    simp only [Set.mem_compl_iff, not_not] at hx
    have h1 : xm ⬝ᵥ v + c ≤ x ⬝ᵥ v + c := hmin hx
    rw [Real.norm_eq_abs, abs_of_pos (by have := hpos x hx; positivity)]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hm0.le h1 p)
  have hR0 : 0 < R := lt_of_lt_of_le (hpos x0 hx0) (hR x0 hx0)
  refine contr_lb hD hconv hne hx0 hl0 hl1 hint (fun x hx => by
      have := hpos x hx; positivity) (by
        have := hpos x0 hx0; positivity) (fun x hx => ?_)
  have hHx : AffineMap.homothety x0 l x ∈ D := (nvol_hom hD hconv hne hx0 hl0 hl1).1 ⟨x, hx, rfl⟩
  have hp := hpos _ hHx
  refine inv_anti₀ (pow_pos hp p) (pow_le_pow_left₀ hp.le ?_ p)
  rw [aff_hom']
  have := hR x hx
  nlinarith

/-- **(J.20)** `m^{−(p−r)} ≤ 2^p R^r ∫ f^{−p} dσ` at a minimizer with value `m > 0` -/
theorem J20 (v : Fin d → ℝ) (c : ℝ) {x0 : Fin d → ℝ} (hx0 : x0 ∈ D)
    (hpos : ∀ x ∈ D, 0 < x ⬝ᵥ v + c) (hmin : ∀ x ∈ D, x0 ⬝ᵥ v + c ≤ x ⬝ᵥ v + c) {R : ℝ}
    (hR : ∀ x ∈ D, x ⬝ᵥ v + c ≤ R) {p : ℕ} (hp : rdim D ≤ p) :
    ((x0 ⬝ᵥ v + c) ^ (p - rdim D))⁻¹ ≤
      2 ^ p * R ^ rdim D * ∫ x, ((x ⬝ᵥ v + c) ^ p)⁻¹ ∂(nvol D) := by
  set m := x0 ⬝ᵥ v + c with hmdef
  have hm0 : 0 < m := hpos x0 hx0
  have hmR : m ≤ R := hR x0 hx0
  have hR0 : 0 < R := lt_of_lt_of_le hm0 hmR
  have h := inv_contr hD hconv hne v c hx0 hpos hR (l := m / R) (by positivity)
    ((div_le_one hR0).2 hmR) p
  have hle : (1 - m / R) * m + m / R * R ≤ 2 * m := by
    have e : m / R * R = m := by field_simp
    rw [e]; nlinarith [div_pos hm0 hR0]
  have h2 : (m / R) ^ rdim D * ((2 * m) ^ p)⁻¹ ≤ ∫ x, ((x ⬝ᵥ v + c) ^ p)⁻¹ ∂(nvol D) := by
    refine le_trans ?_ h
    refine mul_le_mul_of_nonneg_left (inv_anti₀ ?_ (pow_le_pow_left₀ ?_ hle p)) (by positivity)
    · have : 0 < (1 - m / R) * m + m / R * R := by
        have e : m / R * R = m := by field_simp
        rw [e]
        have : 0 ≤ (1 - m / R) * m := mul_nonneg (by
          rw [sub_nonneg, div_le_one hR0]; exact hmR) hm0.le
        linarith
      positivity
    · have e : m / R * R = m := by field_simp
      rw [e]
      have : 0 ≤ (1 - m / R) * m := mul_nonneg (by
        rw [sub_nonneg, div_le_one hR0]; exact hmR) hm0.le
      linarith
  have e : ((m ^ (p - rdim D))⁻¹) = 2 ^ p * R ^ rdim D * ((m / R) ^ rdim D * ((2 * m) ^ p)⁻¹) := by
    obtain ⟨k, hk⟩ : ∃ k, p = rdim D + k := ⟨p - rdim D, by omega⟩
    rw [hk, Nat.add_sub_cancel_left, mul_pow, div_pow, pow_add]
    field_simp
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

end Ineq

end J11


-- ===== Solutions.G26.Supp =====

/-! ### Support functions and extrema of affine fields on a compact body -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {d : ℕ}

/-- the `ℓ¹` radius of `D` -/
noncomputable def rad1 (D : Set (Fin d → ℝ)) : ℝ := sSup ((fun u : Fin d → ℝ => ∑ i, |u i|) '' D)

lemma abs_dot_le (u v : Fin d → ℝ) : |u ⬝ᵥ v| ≤ (∑ i, |u i|) * ‖v‖ := by
  unfold dotProduct
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (abs_nonneg _)

section

variable {D : Set (Fin d → ℝ)} (hD : IsCompact D)
include hD

lemma bdd_img (w : Fin d → ℝ) : BddAbove ((fun u => u ⬝ᵥ w) '' D) :=
  (hD.image (by simp only [dotProduct]; fun_prop)).bddAbove

lemma le_supp {u : Fin d → ℝ} (hu : u ∈ D) (w : Fin d → ℝ) : u ⬝ᵥ w ≤ supp D w :=
  le_csSup (bdd_img hD w) ⟨u, hu, rfl⟩

lemma supp_mem (hne : D.Nonempty) (w : Fin d → ℝ) : ∃ u ∈ D, u ⬝ᵥ w = supp D w := by
  have hc : IsCompact ((fun u => u ⬝ᵥ w) '' D) :=
    hD.image (by simp only [dotProduct]; fun_prop)
  obtain ⟨u, hu, he⟩ := hc.sSup_mem (hne.image _)
  exact ⟨u, hu, he⟩

lemma le_rad1 {u : Fin d → ℝ} (hu : u ∈ D) : ∑ i, |u i| ≤ rad1 D :=
  le_csSup (hD.image (by fun_prop)).bddAbove ⟨u, hu, rfl⟩

lemma supp_sub_le (hne : D.Nonempty) (w w' : Fin d → ℝ) :
    supp D w - supp D w' ≤ rad1 D * ‖w - w'‖ := by
  obtain ⟨u, hu, he⟩ := supp_mem hD hne w
  have h1 := le_supp hD hu w'
  have h2 := abs_dot_le u (w - w')
  have h3 : (∑ i, |u i|) * ‖w - w'‖ ≤ rad1 D * ‖w - w'‖ :=
    mul_le_mul_of_nonneg_right (le_rad1 hD hu) (norm_nonneg _)
  rw [dotProduct_sub] at h2
  have := (abs_le.1 h2).2
  linarith

lemma rad1_nonneg (hne : D.Nonempty) : 0 ≤ rad1 D := by
  obtain ⟨u, hu⟩ := hne
  exact le_trans (Finset.sum_nonneg fun i _ => abs_nonneg _) (le_rad1 hD hu)

lemma supp_lip (hne : D.Nonempty) : LipschitzWith (Real.toNNReal (rad1 D)) (supp D) := by
  refine LipschitzWith.of_dist_le_mul fun w w' => ?_
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (rad1_nonneg hD hne)]
  refine abs_le.2 ⟨?_, supp_sub_le hD hne w w'⟩
  have := supp_sub_le hD hne w' w
  rw [norm_sub_rev] at this
  linarith

lemma supp_cont (hne : D.Nonempty) : Continuous (supp D) := (supp_lip hD hne).continuous

lemma negMax_ge {u : Fin d → ℝ} (hu : u ∈ D) (V : Fin d → ℝ) (c : ℝ) :
    -(u ⬝ᵥ V + c) ≤ negMax D V c := by
  have := le_supp hD hu (-V)
  rw [dotProduct_neg] at this
  unfold negMax; linarith

lemma posMax_ge {u : Fin d → ℝ} (hu : u ∈ D) (V : Fin d → ℝ) (c : ℝ) :
    u ⬝ᵥ V + c ≤ posMax D V c := by
  have := le_supp hD hu V
  unfold posMax; linarith

lemma abs_le_absMax {u : Fin d → ℝ} (hu : u ∈ D) (V : Fin d → ℝ) (c : ℝ) :
    |u ⬝ᵥ V + c| ≤ absMax D V c := by
  unfold absMax
  refine abs_le.2 ⟨?_, le_trans (posMax_ge hD hu V c) (le_max_left _ _)⟩
  have := le_trans (negMax_ge hD hu V c) (le_max_right (posMax D V c) _)
  linarith

omit hD in
lemma negMax_le_absMax (V : Fin d → ℝ) (c : ℝ) : negMax D V c ≤ absMax D V c :=
  le_max_right _ _

lemma negMax_mem (hne : D.Nonempty) (V : Fin d → ℝ) (c : ℝ) :
    ∃ u ∈ D, -(u ⬝ᵥ V + c) = negMax D V c := by
  obtain ⟨u, hu, he⟩ := supp_mem hD hne (-V)
  refine ⟨u, hu, ?_⟩
  rw [dotProduct_neg] at he
  unfold negMax; linarith

lemma posMax_mem (hne : D.Nonempty) (V : Fin d → ℝ) (c : ℝ) :
    ∃ u ∈ D, u ⬝ᵥ V + c = posMax D V c := by
  obtain ⟨u, hu, he⟩ := supp_mem hD hne V
  exact ⟨u, hu, by unfold posMax; linarith⟩

/-- the absolute maximum is attained -/
lemma absMax_mem (hne : D.Nonempty) (V : Fin d → ℝ) (c : ℝ) :
    ∃ u ∈ D, |u ⬝ᵥ V + c| = absMax D V c ∧ ∀ x ∈ D, |x ⬝ᵥ V + c| ≤ |u ⬝ᵥ V + c| := by
  obtain ⟨u1, hu1, h1⟩ := posMax_mem hD hne V c
  obtain ⟨u2, hu2, h2⟩ := negMax_mem hD hne V c
  rcases le_total (negMax D V c) (posMax D V c) with h | h
  · have hA : absMax D V c = posMax D V c := max_eq_left h
    have hval : |u1 ⬝ᵥ V + c| = absMax D V c := by
      rw [hA, h1]
      refine abs_of_nonneg ?_
      have := negMax_ge hD hu1 V c
      linarith
    exact ⟨u1, hu1, hval, fun x hx => hval ▸ abs_le_absMax hD hx V c⟩
  · have hA : absMax D V c = negMax D V c := max_eq_right h
    have hval : |u2 ⬝ᵥ V + c| = absMax D V c := by
      rw [hA, ← h2, abs_of_nonpos]
      have := posMax_ge hD hu2 V c
      linarith
    exact ⟨u2, hu2, hval, fun x hx => hval ▸ abs_le_absMax hD hx V c⟩

lemma negMax_cont (hne : D.Nonempty) :
    Continuous fun p : (Fin d → ℝ) × ℝ => negMax D p.1 p.2 := by
  unfold negMax
  exact ((supp_cont hD hne).comp continuous_fst.neg).sub continuous_snd

lemma posMax_cont (hne : D.Nonempty) :
    Continuous fun p : (Fin d → ℝ) × ℝ => posMax D p.1 p.2 := by
  unfold posMax
  exact ((supp_cont hD hne).comp continuous_fst).add continuous_snd

lemma absMax_cont (hne : D.Nonempty) :
    Continuous fun p : (Fin d → ℝ) × ℝ => absMax D p.1 p.2 :=
  (posMax_cont hD hne).max (negMax_cont hD hne)

lemma negMax_meas (hne : D.Nonempty) {Ω : Type*} {m : MeasurableSpace Ω} {V : Ω → Fin d → ℝ}
    {c : Ω → ℝ} (hV : Measurable V) (hc : Measurable c) :
    Measurable fun ω => negMax D (V ω) (c ω) := by
  have h := (negMax_cont hD hne).measurable
  exact h.comp (f := fun ω => (V ω, c ω)) (hV.prodMk hc)

lemma absMax_meas (hne : D.Nonempty) {Ω : Type*} {m : MeasurableSpace Ω} {V : Ω → Fin d → ℝ}
    {c : Ω → ℝ} (hV : Measurable V) (hc : Measurable c) :
    Measurable fun ω => absMax D (V ω) (c ω) := by
  have h := (absMax_cont hD hne).measurable
  exact h.comp (f := fun ω => (V ω, c ω)) (hV.prodMk hc)

end

end G26


-- ===== Solutions.G26.Iface =====

/-! ### The abstract affine-field interface of Lemma G.25 -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {d : ℕ} {Ω : Type*}

section

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma FI.absMax_meas (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) :
    Measurable[F n] (fun ω => absMax D (V n ω) (c n ω)) :=
  G26.absMax_meas I.hD I.hne (I.Vm n hn) (I.cm n hn)

/-- deterministic envelope of the field and its extrema -/
lemma FI.env' (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ᵐ ω ∂μ, absMax D (V n ω) (c n ω) ≤ r ∧
      ∀ u ∈ D, |fz V c n ω u| ≤ r := by
  obtain ⟨r, hr⟩ := I.env n hn
  refine ⟨max r 0, le_max_right _ _, ?_⟩
  filter_upwards [hr] with ω h
  obtain ⟨x0, hx0, hval, -⟩ := absMax_mem I.hD I.hne (V n ω) (c n ω)
  have hA : absMax D (V n ω) (c n ω) ≤ max r 0 := by
    rw [← hval]; exact (h x0 hx0).trans (le_max_left _ _)
  exact ⟨hA, fun u hu => (abs_le_absMax I.hD hu _ _).trans hA⟩

end

end G26


-- ===== Solutions.G26.Contr =====

/-! ### Contraction probability: a small minimum of a positive affine field is unlikely -/

open MeasureTheory ProbabilityTheory Set J11

namespace G26

variable {d : ℕ} {D : Set (Fin d → ℝ)}

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma ofReal_int_le {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℝ} (h0 : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂ν) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂ν := by
  by_cases hf : Integrable f ν
  · rw [ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall h0)]
  · rw [integral_undef hf]; simp

end G26


-- ===== Solutions.G26.NegRec =====

/-! ### The negative integral moment recurrence (Lemmas G.24, G.25) -/

open MeasureTheory ProbabilityTheory Set J11

namespace G26

variable {d : ℕ} {Ω : Type*}

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

end G26

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma neg_fz (V : ℕ → Ω → (Fin d → ℝ)) (c : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (u : Fin d → ℝ) :
    -fz V c n ω u = u ⬝ᵥ (-V n ω) + (-c n ω) := by
  unfold fz; rw [dotProduct_neg]; ring

end G26

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

end G26

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma vneg_lt (k : ℕ) (hk : 2 ≤ k) (B : ℝ) (hB : 2 ^ 20 * (4 * k : ℝ) ≤ B) :
    1 + 1024 * (4 * k : ℝ) ^ 2 / B < 3 * k := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hB0 : 0 < B := by nlinarith
  have : 1024 * (4 * k : ℝ) ^ 2 / B ≤ k := by
    rw [div_le_iff₀ hB0]; nlinarith
  linarith

end G26


-- ===== Solutions.G26.RunK =====

/-! ### The loss-difference field on `K` satisfies the field interface (Lemma G.10) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26R

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}

section

variable (hd : 1 ≤ d) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ) (hspan : Submodule.span ℝ 𝒜 = ⊤)
include hd hℬ hgen hspan

end

end G26R

namespace G26R

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma Fx_lt {n : ℕ} (hn : n < T) : Fx R T n = R.G n := if_pos hn

lemma hist_le_m (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t ≤ T) : R.hist t ≤ mΩ := by
  unfold GRun.hist
  refine iSup₂_le fun s hs => ?_
  obtain ⟨⟨hX, hA, hY, -⟩, -⟩ := hR s (by omega)
  exact (hX.prodMk (hA.prodMk hY)).comap_le

lemma Fx_le (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {n : ℕ} (_ : n ≤ T) : Fx R T n ≤ mΩ := by
  unfold Fx; split_ifs with h
  · exact G2R.G_le hR h
  · exact le_rfl

lemma cumEst_Fx (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {n : ℕ} (hn : n ≤ T) :
    Measurable[Fx R T n] (R.cumEst n) := by
  rcases lt_or_eq_of_le hn with h | h
  · rw [Fx_lt h]; exact (G2R.meas_cumEst hR hn).mono (G2R.hist_le_G hR h) le_rfl
  · subst h
    have : Fx R n n = mΩ := if_neg (lt_irrefl n)
    rw [this]; exact (G2R.meas_cumEst hR le_rfl).mono (hist_le_m hR le_rfl) le_rfl

lemma cumEst_succ (n : ℕ) (ω : Ω) : R.cumEst (n + 1) ω = R.cumEst n ω + R.thetaHat n ω := by
  simp [GRun.cumEst, Finset.sum_range_succ]

end G26R


-- ===== Solutions.G26.RunW =====

/-! ### The remaining-budget shifted field on `K` (Lemma G.30) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26R

open G26

variable {d : ℕ}

lemma setNorm_eq {𝒜 : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) (hne : 𝒜.Nonempty) (w : Fin d → ℝ) :
    setNorm 𝒜 w = max (supp 𝒜 w) (supp 𝒜 (-w)) := by
  have hcont : Continuous fun a : Fin d → ℝ => |a ⬝ᵥ w| := by
    simp only [dotProduct]; fun_prop
  apply le_antisymm
  · refine csSup_le (hne.image _) ?_
    rintro _ ⟨a, ha, rfl⟩
    show |a ⬝ᵥ w| ≤ _
    rcases le_total 0 (a ⬝ᵥ w) with h | h
    · rw [abs_of_nonneg h]; exact (le_supp h𝒜 ha w).trans (le_max_left _ _)
    · rw [abs_of_nonpos h]
      have := le_supp h𝒜 ha (-w)
      rw [dotProduct_neg] at this
      exact this.trans (le_max_right _ _)
  · refine max_le ?_ ?_
    · obtain ⟨a, ha, he⟩ := supp_mem h𝒜 hne w
      rw [← he]
      exact (le_abs_self _).trans (le_csSup (h𝒜.image hcont).bddAbove ⟨a, ha, rfl⟩)
    · obtain ⟨a, ha, he⟩ := supp_mem h𝒜 hne (-w)
      rw [← he, dotProduct_neg]
      exact (neg_le_abs _).trans (le_csSup (h𝒜.image hcont).bddAbove ⟨a, ha, rfl⟩)

lemma setNorm_cont {𝒜 : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) (hne : 𝒜.Nonempty) :
    Continuous (setNorm 𝒜) := by
  have : setNorm 𝒜 = fun w => max (supp 𝒜 w) (supp 𝒜 (-w)) := funext (setNorm_eq h𝒜 hne)
  rw [this]
  exact (supp_cont h𝒜 hne).max ((supp_cont h𝒜 hne).comp continuous_neg)

variable {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma G_mono (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {j n : ℕ} (hjn : j ≤ n) (hn : n < T) :
    R.G j ≤ R.G n := by
  induction n, hjn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hjn ih => exact (ih (by omega)).trans (hR n (by omega)).1.2.2.2.2.2.2.2.1

lemma Acum_Fx (h𝒜 : IsCompact 𝒜) (hne : 𝒜.Nonempty) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R)
    (θ : Fin d → ℝ) {n : ℕ} (hn : n ≤ T) : Measurable[Fx R T n] (Acum 𝒜 R θ n) := by
  unfold Acum
  refine Finset.measurable_sum _ fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  have hθj : Measurable[R.G j] (R.θs j) := (hR j (by omega)).1.2.2.2.2.2.2.1
  have hc := (setNorm_cont h𝒜 hne).measurable
  rcases lt_or_eq_of_le hn with h | h
  · rw [Fx_lt h]
    exact hc.comp ((hθj.mono (G_mono hR hj'.le h) le_rfl).sub measurable_const)
  · subst h
    have : Fx R n n = mΩ := if_neg (lt_irrefl n)
    rw [this]
    exact hc.comp (((hR j hj').1.2.2.2.1).sub measurable_const)

end G26R

namespace G26R

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

end G26R


-- ===== Solutions.G26.Geo =====

/-! ### The projective body of normalized directions (Lemma G.16) -/

open MeasureTheory ProbabilityTheory Set IAFTRL

namespace G26G

open G26

variable {d : ℕ}

variable {𝒜 ℬ : Set (Fin d → ℝ)} {θ astar : Fin d → ℝ}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

lemma ne𝒜 : 𝒜.Nonempty := ⟨astar, H.hastar⟩

lemma haK : astar ∈ Kset ℬ := H.hgen.2 H.hastar

lemma Kc : IsCompact (Kset ℬ) := G2R.Kset_compact H.hℬ

omit H in
lemma Kconv : Convex ℝ (Kset ℬ) := convex_convexHull ℝ ℬ

lemma sig_pos : 0 < H.sig := (Classical.choose_spec H.hsharp).1

lemma sig_spec {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) :
    H.sig * sNorm ℬ (a - astar) ≤ gap θ astar a := by
  have h := (Classical.choose_spec H.hsharp).2 a (by rw [G1L.Kset_gen H.hgen]; exact ha)
  rw [G1L.sNorm_gen H.hgen] at h
  exact h

omit H in
lemma sNorm_nonneg (x : Fin d → ℝ) : 0 ≤ sNorm ℬ x := by unfold sNorm; exact gauge_nonneg _

lemma norm_le (x : Fin d → ℝ) : ‖x‖ ≤ sNorm ℬ x := by
  rw [← G1L.sNorm_gen H.hgen]; exact T31.norm_le_sNorm H.ne𝒜 H.hspan H.hball x

lemma gap_pos {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) (hne : a ≠ astar) : 0 < gap θ astar a := by
  have h1 : 0 < ‖a - astar‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have h2 := H.norm_le (a - astar)
  exact lt_of_lt_of_le (mul_pos H.sig_pos (lt_of_lt_of_le h1 h2)) (H.sig_spec ha)

/-- duality of the gauge of `𝒮` and the norm `‖·‖_𝒜` -/
lemma abs_dot_le_sNorm (x w : Fin d → ℝ) : |x ⬝ᵥ w| ≤ sNorm ℬ x * setNorm 𝒜 w := by
  rw [← G1L.sNorm_gen H.hgen]
  have hcont : Continuous fun a : Fin d → ℝ => |a ⬝ᵥ w| := by
    simp only [dotProduct]; fun_prop
  have hbdd := (H.h𝒜.image hcont).bddAbove
  have hS : ∀ y ∈ Sset 𝒜, |y ⬝ᵥ w| ≤ setNorm 𝒜 w := by
    intro y hy
    have hcvx : Convex ℝ {x : Fin d → ℝ | |x ⬝ᵥ w| ≤ setNorm 𝒜 w} := by
      have hl : IsLinearMap ℝ (fun x : Fin d → ℝ => x ⬝ᵥ w) :=
        ⟨fun x y => add_dotProduct x y w, fun c x => smul_dotProduct c x w⟩
      have : {x : Fin d → ℝ | |x ⬝ᵥ w| ≤ setNorm 𝒜 w} =
          {v | v ⬝ᵥ w ≤ setNorm 𝒜 w} ∩ {v | -setNorm 𝒜 w ≤ v ⬝ᵥ w} := by
        ext x; simp [abs_le, and_comm]
      rw [this]
      exact (convex_halfSpace_le hl _).inter (convex_halfSpace_ge hl _)
    refine convexHull_min ?_ hcvx hy
    rintro a (ha | ha)
    · exact le_csSup hbdd ⟨a, ha, rfl⟩
    · have : -a ∈ 𝒜 := ha
      show |a ⬝ᵥ w| ≤ _
      have h := le_csSup hbdd ⟨-a, this, rfl⟩
      simp only [neg_dotProduct, abs_neg] at h
      exact h
  have habs : Absorbent ℝ (Sset 𝒜) := absorbent_nhds_zero (T31.Sset_nhds H.ne𝒜 H.hspan)
  have hsn : 0 ≤ setNorm 𝒜 w := le_trans (abs_nonneg _) (hS 0 (by
    have : (0 : Fin d → ℝ) ∈ Sset 𝒜 := mem_of_mem_nhds (T31.Sset_nhds H.ne𝒜 H.hspan)
    exact this))
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  -- for every `r > ‖x‖_S ‖w‖`, `|x·w| ≤ r`
  by_cases hw : setNorm 𝒜 w = 0
  · -- `w` is orthogonal to `𝒜`, hence zero
    have hz : ∀ a ∈ 𝒜, a ⬝ᵥ w = 0 := fun a ha => by
      have h1 : |a ⬝ᵥ w| ≤ setNorm 𝒜 w := le_csSup hbdd ⟨a, ha, rfl⟩
      rw [hw] at h1
      exact abs_nonpos_iff.1 h1
    have hw0 : w = 0 := by
      have : ∀ v ∈ Submodule.span ℝ 𝒜, v ⬝ᵥ w = 0 := by
        intro v hv
        induction hv using Submodule.span_induction with
        | mem x hx => exact hz x hx
        | zero => simp
        | add x y _ _ hx hy => rw [add_dotProduct, hx, hy, add_zero]
        | smul c x _ hx => rw [smul_dotProduct, hx, smul_zero]
      rw [H.hspan] at this
      ext i
      have := this (Pi.single i 1) trivial
      simpa [single_dotProduct] using this
    rw [hw0, dotProduct_zero, abs_zero]
    rw [hw, mul_zero] at hr; exact hr.le
  · have hwpos : 0 < setNorm 𝒜 w := lt_of_le_of_ne hsn (Ne.symm hw)
    have hlt : gauge (Sset 𝒜) x < r / setNorm 𝒜 w := by
      rw [lt_div_iff₀ hwpos]; unfold sNorm at hr; exact hr
    obtain ⟨b, hb0, hbr, hxb⟩ := exists_lt_of_gauge_lt habs hlt
    obtain ⟨y, hy, rfl⟩ := hxb
    rw [smul_dotProduct, smul_eq_mul, abs_mul, abs_of_pos hb0]
    calc b * |y ⬝ᵥ w| ≤ b * setNorm 𝒜 w := mul_le_mul_of_nonneg_left (hS y hy) hb0.le
      _ ≤ r / setNorm 𝒜 w * setNorm 𝒜 w := mul_le_mul_of_nonneg_right hbr.le hwpos.le
      _ = r := div_mul_cancel₀ r hwpos.ne'

end Sharp

lemma gap_ndir_dot (a S : Fin d → ℝ) :
    (a - astar) ⬝ᵥ S = gap θ astar a * (ndir θ astar a ⬝ᵥ S) ∨ gap θ astar a = 0 := by
  by_cases h : gap θ astar a = 0
  · exact Or.inr h
  · left; unfold ndir; rw [smul_dotProduct, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ h, one_mul]

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

lemma ndir_mem {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) (hne : a ≠ astar) : ndir θ astar a ∈ UT ℬ θ astar :=
  subset_closure ⟨a, ⟨ha, hne⟩, rfl⟩

lemma U0_ne : (U0 ℬ θ astar).Nonempty := by
  obtain ⟨b, hb, hba⟩ := G1L.exists_ne H.hk astar
  exact ⟨_, b, ⟨subset_convexHull ℝ ℬ hb, hba⟩, rfl⟩

lemma U0_sNorm {u : Fin d → ℝ} (hu : u ∈ U0 ℬ θ astar) : sNorm ℬ u ≤ H.sig⁻¹ := by
  obtain ⟨a, ⟨ha, hne⟩, rfl⟩ := hu
  have h := H.gap_pos ha hne
  unfold ndir sNorm
  rw [gauge_smul_of_nonneg (inv_nonneg.2 h.le), smul_eq_mul]
  have h2 := H.sig_spec ha
  unfold sNorm at h2
  rw [inv_mul_le_iff₀ h]
  have hs := H.sig_pos
  rw [← div_eq_mul_inv, le_div_iff₀ hs]
  linarith

lemma U0_convex : Convex ℝ (U0 ℬ θ astar) := by
  rintro _ ⟨a1, ⟨ha1, hne1⟩, rfl⟩ _ ⟨a2, ⟨ha2, hne2⟩, rfl⟩ s t hs ht hst
  have g1 := H.gap_pos ha1 hne1
  have g2 := H.gap_pos ha2 hne2
  set Δ1 := gap θ astar a1
  set Δ2 := gap θ astar a2
  set c := s / Δ1 + t / Δ2 with hc
  have hc0 : 0 < c := by
    rcases eq_or_lt_of_le hs with h | h
    · have : 0 < t := by linarith
      rw [hc, ← h, zero_div, zero_add]; positivity
    · have : 0 ≤ t / Δ2 := by positivity
      rw [hc]; have : 0 < s / Δ1 := by positivity
      linarith
  set w1 := s / (c * Δ1)
  set w2 := t / (c * Δ2)
  have hw1 : 0 ≤ w1 := by positivity
  have hw2 : 0 ≤ w2 := by positivity
  have hw12 : w1 + w2 = 1 := by
    have : w1 + w2 = (s / Δ1 + t / Δ2) / c := by simp only [w1, w2]; field_simp
    rw [this, ← hc, div_self hc0.ne']
  set a := w1 • a1 + w2 • a2
  have haK : a ∈ Kset ℬ := Kconv ha1 ha2 hw1 hw2 hw12
  have hgap : gap θ astar a = 1 / c := by
    unfold gap
    have : a - astar = w1 • (a1 - astar) + w2 • (a2 - astar) := by
      simp only [a, smul_sub]
      have hh : astar = w1 • astar + w2 • astar := by rw [← add_smul, hw12, one_smul]
      conv_lhs => rw [hh]
      abel
    rw [this, add_dotProduct, smul_dotProduct, smul_dotProduct]
    simp only [smul_eq_mul]
    change w1 * Δ1 + w2 * Δ2 = 1 / c
    have e1 : w1 * Δ1 = s / c := by simp only [w1]; field_simp
    have e2 : w2 * Δ2 = t / c := by simp only [w2]; field_simp
    rw [e1, e2, ← add_div, hst]
  have hne : a ≠ astar := by
    intro h
    have := H.gap_pos haK
    rw [hgap] at this
    have h0 : gap θ astar a = 0 := by rw [h]; unfold gap; simp
    rw [hgap] at h0
    have : (1 : ℝ) / c ≠ 0 := by positivity
    exact this h0
  refine ⟨a, ⟨haK, hne⟩, ?_⟩
  unfold ndir
  rw [hgap]
  have : a - astar = w1 • (a1 - astar) + w2 • (a2 - astar) := by
    simp only [a, smul_sub]
    have hh : astar = w1 • astar + w2 • astar := by rw [← add_smul, hw12, one_smul]
    conv_lhs => rw [hh]
    abel
  rw [this, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  · congr 1; simp only [w1]; rw [show gap θ astar a1 = Δ1 from rfl]; field_simp
  · congr 1; simp only [w2]; rw [show gap θ astar a2 = Δ2 from rfl]; field_simp

lemma U0_bdd : U0 ℬ θ astar ⊆ Metric.closedBall 0 H.sig⁻¹ := by
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (H.norm_le u).trans (H.U0_sNorm hu)

lemma UT_compact : IsCompact (UT ℬ θ astar) :=
  (isCompact_closedBall (0 : Fin d → ℝ) H.sig⁻¹).of_isClosed_subset isClosed_closure
    (closure_minimal H.U0_bdd Metric.isClosed_closedBall)

lemma UT_convex : Convex ℝ (UT ℬ θ astar) := H.U0_convex.closure

lemma UT_ne : (UT ℬ θ astar).Nonempty := H.U0_ne.mono subset_closure

lemma UT_bdd {u : Fin d → ℝ} (hu : u ∈ UT ℬ θ astar) : ‖u‖ ≤ H.sig⁻¹ := by
  have := closure_minimal H.U0_bdd Metric.isClosed_closedBall hu
  rwa [Metric.mem_closedBall, dist_zero_right] at this

lemma DT_compact : IsCompact (DT ℬ θ astar) :=
  (isCompact_Icc.prod H.UT_compact).image (continuous_fst.smul continuous_snd)

lemma zero_mem_DT : (0 : Fin d → ℝ) ∈ DT ℬ θ astar := by
  obtain ⟨u, hu⟩ := H.UT_ne
  exact ⟨(0, u), ⟨⟨le_rfl, zero_le_one⟩, hu⟩, zero_smul _ _⟩

lemma DT_ne : (DT ℬ θ astar).Nonempty := ⟨0, H.zero_mem_DT⟩

lemma UT_sub_DT : UT ℬ θ astar ⊆ DT ℬ θ astar := fun u hu =>
  ⟨(1, u), ⟨⟨zero_le_one, le_rfl⟩, hu⟩, one_smul _ _⟩

lemma DT_mem {w : Fin d → ℝ} (hw : w ∈ DT ℬ θ astar) :
    ∃ l ∈ Icc (0 : ℝ) 1, ∃ u ∈ UT ℬ θ astar, w = l • u := by
  obtain ⟨⟨l, u⟩, ⟨hl, hu⟩, rfl⟩ := hw
  exact ⟨l, hl, u, hu, rfl⟩

/-- **homogeneous transfer**: a continuous degree-`k` homogeneous bound on centered differences
`φ(a − a*) ≤ Δ(a)^k M` passes to the cone body -/
lemma homog {φ : (Fin d → ℝ) → ℝ} (hφ : Continuous φ) {k : ℕ}
    (hhom : ∀ (c : ℝ) (w : Fin d → ℝ), 0 ≤ c → φ (c • w) = c ^ k * φ w) {M : ℝ} (hM : 0 ≤ M)
    (hK : ∀ a ∈ Kset ℬ, a ≠ astar → φ (a - astar) ≤ gap θ astar a ^ k * M) :
    ∀ w ∈ DT ℬ θ astar, φ w ≤ M := by
  have hU0 : ∀ u ∈ U0 ℬ θ astar, φ u ≤ M := by
    rintro _ ⟨a, ⟨ha, hne⟩, rfl⟩
    have g := H.gap_pos ha hne
    unfold ndir
    rw [hhom _ _ (inv_nonneg.2 g.le), inv_pow]
    rw [inv_mul_le_iff₀ (pow_pos g k)]
    exact hK a ha hne
  have hUT : ∀ u ∈ UT ℬ θ astar, φ u ≤ M := fun u hu =>
    closure_minimal hU0 (isClosed_le hφ continuous_const) hu
  intro w hw
  obtain ⟨l, ⟨hl0, hl1⟩, u, hu, rfl⟩ := H.DT_mem hw
  rw [hhom _ _ hl0]
  have h1 := hUT u hu
  have h2 : l ^ k ≤ 1 := pow_le_one₀ hl0 hl1
  have h3 : 0 ≤ l ^ k := pow_nonneg hl0 k
  nlinarith

/-- `|u·w| ≤ ‖w‖_𝒜 / ς` on the cone body -/
lemma DT_dot_le (w : Fin d → ℝ) : ∀ u ∈ DT ℬ θ astar, |u ⬝ᵥ w| ≤ H.sig⁻¹ * setNorm 𝒜 w := by
  have hsn : 0 ≤ setNorm 𝒜 w := le_trans (abs_nonneg _)
    (le_csSup ((H.h𝒜.image (by simp only [dotProduct]; fun_prop :
      Continuous fun a : Fin d → ℝ => |a ⬝ᵥ w|)).bddAbove) ⟨astar, H.hastar, rfl⟩)
  refine H.homog (φ := fun u => |u ⬝ᵥ w|) (by simp only [dotProduct]; fun_prop)
    (fun c v hc => by rw [smul_dotProduct, smul_eq_mul, abs_mul, abs_of_nonneg hc, pow_one])
    (by have := H.sig_pos; positivity) ?_
  intro a ha hne
  have h1 := H.abs_dot_le_sNorm (a - astar) w
  have h2 := H.sig_spec ha
  have hs := H.sig_pos
  rw [pow_one]
  calc |(a - astar) ⬝ᵥ w| ≤ sNorm ℬ (a - astar) * setNorm 𝒜 w := h1
    _ ≤ (gap θ astar a / H.sig) * setNorm 𝒜 w := by
        gcongr; rw [le_div_iff₀ hs]; linarith
    _ = gap θ astar a * (H.sig⁻¹ * setNorm 𝒜 w) := by ring

/-- the cone body lies in the span of the centered differences -/
lemma DT_sub_span : DT ℬ θ astar ⊆
    (Submodule.span ℝ ((fun a => a - astar) '' Kset ℬ) : Set (Fin d → ℝ)) := by
  set V := Submodule.span ℝ ((fun a => a - astar) '' Kset ℬ)
  have hV : IsClosed (V : Set (Fin d → ℝ)) := Submodule.closed_of_finiteDimensional V
  have hU0 : U0 ℬ θ astar ⊆ V := by
    rintro _ ⟨a, ⟨ha, -⟩, rfl⟩
    exact V.smul_mem _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  have hUT : UT ℬ θ astar ⊆ V := closure_minimal hU0 hV
  rintro _ ⟨⟨l, u⟩, ⟨-, hu⟩, rfl⟩
  exact V.smul_mem l (hUT hu)

lemma DT_bdd {w : Fin d → ℝ} (hw : w ∈ DT ℬ θ astar) : ‖w‖ ≤ H.sig⁻¹ := by
  obtain ⟨l, ⟨hl0, hl1⟩, u, hu, rfl⟩ := H.DT_mem hw
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hl0]
  have := H.UT_bdd hu
  have hs : 0 ≤ H.sig⁻¹ := inv_nonneg.2 H.sig_pos.le
  nlinarith [norm_nonneg u]

/-- **projective extension (G.306)**: the normalized field is dominated by the centered field -/
lemma DT_span_bound : ∃ Λ1 : ℝ, 0 < Λ1 ∧ ∀ (w : Fin d → ℝ) (M : ℝ),
    (∀ a ∈ Kset ℬ, |(a - astar) ⬝ᵥ w| ≤ M) → ∀ u ∈ DT ℬ θ astar, |u ⬝ᵥ w| ≤ Λ1 * M := by
  classical
  set s := (fun a => a - astar) '' Kset ℬ
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent ℝ s
  have : Finite b := hli.finite_of_isNoetherian
  haveI : Fintype b := Fintype.ofFinite b
  set L := Fintype.linearCombination ℝ (fun i : b => (i : Fin d → ℝ))
  have hL : LinearMap.range L = Submodule.span ℝ s := by
    rw [Fintype.range_linearCombination, Subtype.range_coe, hspan]
  obtain ⟨g, hg⟩ := L.rangeRestrict.exists_rightInverse_of_surjective L.range_rangeRestrict
  set gc := LinearMap.toContinuousLinearMap g
  refine ⟨(Fintype.card b : ℝ) * ‖gc‖ * H.sig⁻¹ + 1, add_pos_of_nonneg_of_pos (mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) gc.opNorm_nonneg) (inv_nonneg.2 H.sig_pos.le)) one_pos, ?_⟩
  intro w M hM u hu
  have hM0 : 0 ≤ M := by
    have := hM astar H.haK
    simpa using le_trans (abs_nonneg _) this
  have huV : u ∈ LinearMap.range L := by rw [hL]; exact H.DT_sub_span hu
  set c := g ⟨u, huV⟩
  have hLc : L c = u := by
    have := congrArg Subtype.val (LinearMap.congr_fun hg ⟨u, huV⟩)
    simpa [c] using this
  have hc : ‖c‖ ≤ ‖gc‖ * H.sig⁻¹ := by
    have h1 : ‖c‖ ≤ ‖gc‖ * ‖(⟨u, huV⟩ : LinearMap.range L)‖ := gc.le_opNorm _
    have h2 : ‖(⟨u, huV⟩ : LinearMap.range L)‖ = ‖u‖ := rfl
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (H.DT_bdd hu) gc.opNorm_nonneg)
  rw [← hLc, Fintype.linearCombination_apply, sum_dotProduct]
  calc |∑ i : b, (c i • (i : Fin d → ℝ)) ⬝ᵥ w| ≤ ∑ i : b, |(c i • (i : Fin d → ℝ)) ⬝ᵥ w| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : b, ‖c‖ * M := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [smul_dotProduct, smul_eq_mul, abs_mul]
        obtain ⟨a, ha, hai⟩ := hbs i.2
        have h1 : |(i : Fin d → ℝ) ⬝ᵥ w| ≤ M := by rw [← hai]; exact hM a ha
        have h2 : |c i| ≤ ‖c‖ := by
          have := norm_le_pi_norm c i
          rwa [Real.norm_eq_abs] at this
        exact mul_le_mul h2 h1 (abs_nonneg _) (norm_nonneg _)
    _ = (Fintype.card b : ℝ) * ‖c‖ * M := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ ((Fintype.card b : ℝ) * ‖gc‖ * H.sig⁻¹ + 1) * M := by
        have : (Fintype.card b : ℝ) * ‖c‖ ≤ (Fintype.card b : ℝ) * ‖gc‖ * H.sig⁻¹ + 1 := by
          have := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (Fintype.card b))
          linarith
        exact mul_le_mul_of_nonneg_right this hM0

end Sharp

end G26G


-- ===== Solutions.G26.RefGood =====

/-! ### A measurable sufficient condition for the reference to be `a*` -/

open MeasureTheory ProbabilityTheory Set IAFTRL

namespace G26G

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}

lemma goodS_meas (js n : ℕ) : MeasurableSet {S : Fin d → ℝ | goodS ℬ e js n S} := by
  have : {S : Fin d → ℝ | goodS ℬ e js n S} = ⋂ i : ℕ, {S | i ∈ Jset ℬ e → i ≠ js →
      cand ℬ e js ⬝ᵥ S + gbeta d n * hPen ℬ e js < cand ℬ e i ⬝ᵥ S + gbeta d n * hPen ℬ e i} := by
    ext S; simp [goodS]
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  by_cases h : i ∈ Jset ℬ e ∧ i ≠ js
  · have e1 : {S : Fin d → ℝ | i ∈ Jset ℬ e → i ≠ js →
        cand ℬ e js ⬝ᵥ S + gbeta d n * hPen ℬ e js < cand ℬ e i ⬝ᵥ S + gbeta d n * hPen ℬ e i} =
        {S | cand ℬ e js ⬝ᵥ S + gbeta d n * hPen ℬ e js <
          cand ℬ e i ⬝ᵥ S + gbeta d n * hPen ℬ e i} := by
      ext S; simp [h.1, h.2]
    rw [e1]
    exact measurableSet_lt (by simp only [dotProduct]; fun_prop) (by simp only [dotProduct]; fun_prop)
  · have e1 : {S : Fin d → ℝ | i ∈ Jset ℬ e → i ≠ js →
        cand ℬ e js ⬝ᵥ S + gbeta d n * hPen ℬ e js < cand ℬ e i ⬝ᵥ S + gbeta d n * hPen ℬ e i} =
        univ := by
      ext S; simp only [mem_setOf_eq, mem_univ, iff_true]
      intro h1 h2; exact absurd ⟨h1, h2⟩ h
    rw [e1]; exact MeasurableSet.univ

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

lemma D0_nonneg : 0 ≤ H.D0 he :=
  Finset.sum_nonneg fun i _ => inv_nonneg.2 (sNorm_nonneg _)

end Sharp

end G26G


-- ===== Solutions.G26.RunN =====

/-! ### The normalized field on the cone body satisfies the field interface (Lemmas G.17, G.28) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

lemma Lam1_eq : ∃ h, Lam1 ℬ θ astar = Classical.choose (p := fun Λ1 : ℝ => 0 < Λ1 ∧
    ∀ (w : Fin d → ℝ) (M : ℝ), (∀ a ∈ Kset ℬ, |(a - astar) ⬝ᵥ w| ≤ M) →
      ∀ u ∈ DT ℬ θ astar, |u ⬝ᵥ w| ≤ Λ1 * M) h :=
  ⟨H.DT_span_bound, by unfold Lam1; rw [dif_pos H.DT_span_bound]⟩

lemma Lam1_pos : 0 < Lam1 ℬ θ astar := by
  obtain ⟨h, e⟩ := H.Lam1_eq; rw [e]; exact (Classical.choose_spec h).1

lemma Lam1_spec {w : Fin d → ℝ} {M : ℝ} (hM : ∀ a ∈ Kset ℬ, |(a - astar) ⬝ᵥ w| ≤ M) {u : Fin d → ℝ}
    (hu : u ∈ DT ℬ θ astar) : |u ⬝ᵥ w| ≤ Lam1 ℬ θ astar * M := by
  obtain ⟨h, e⟩ := H.Lam1_eq; rw [e]; exact (Classical.choose_spec h).2 w M hM u hu

lemma kb_ge : 1 ≤ H.kb ∧ H.sig⁻¹ ≤ H.kb ∧ H.sig⁻¹ ^ 2 ≤ H.kb := by
  have : 0 ≤ H.sig⁻¹ := inv_nonneg.2 H.sig_pos.le
  unfold kb; refine ⟨?_, ?_, ?_⟩ <;> nlinarith

end Sharp

end G26G

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma Fx_mono' (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {j n : ℕ} (hjn : j ≤ n) (hn : n ≤ T) :
    Fx R T j ≤ Fx R T n := by
  rcases lt_or_eq_of_le hn with h | h
  · rw [Fx_lt (lt_of_le_of_lt hjn h), Fx_lt h]; exact G_mono hR hjn h
  · subst h
    have : Fx R n n = mΩ := if_neg (lt_irrefl n)
    rw [this]; exact Fx_le hR (le_trans hjn le_rfl)

lemma good_meas (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (js : ℕ) {j : ℕ} (hj : j ≤ T) :
    MeasurableSet[Fx R T j] {ω | goodS ℬ e js (j + 1) (R.cumEst j ω)} :=
  cumEst_Fx hR hj (goodS_meas js (j + 1))

lemma JN_meas (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (js m : ℕ) {n : ℕ} (hn : n ≤ T) :
    MeasurableSet[Fx R T n] (JN ℬ e js R m n) := by
  have : JN ℬ e js R m n = ⋂ j : ℕ, {ω | m ≤ j → j ≤ n → goodS ℬ e js (j + 1) (R.cumEst j ω)} := by
    ext ω; simp [JN]
  rw [this]
  refine MeasurableSet.iInter fun j => ?_
  by_cases h : m ≤ j ∧ j ≤ n
  · have e1 : {ω | m ≤ j → j ≤ n → goodS ℬ e js (j + 1) (R.cumEst j ω)} =
        {ω | goodS ℬ e js (j + 1) (R.cumEst j ω)} := by
      ext ω; simp [h.1, h.2]
    rw [e1]
    exact Fx_mono' hR h.2 hn _ (good_meas hR js (le_trans h.2 hn))
  · have e1 : {ω | m ≤ j → j ≤ n → goodS ℬ e js (j + 1) (R.cumEst j ω)} = univ := by
      ext ω; simp only [mem_setOf_eq, mem_univ, iff_true]
      intro h1 h2; exact absurd ⟨h1, h2⟩ h
    rw [e1]; exact MeasurableSet.univ

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

end Sharp

end G26G


-- ===== Solutions.G26.Scalar =====

/-! ### Killed scalar local moments (Lemma G.22 and the local moments of Lemma G.28) -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {Ω : Type*}

variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω}
  {Y : ℕ → Ω → ℝ} {I : ℕ → Set Ω} {m N : ℕ} {τ β : ℕ → ℝ} {B : ℝ}

lemma SI.Ym' (S : SI μ F Y I m N τ β B) {n : ℕ} (hn : n ≤ N) : Measurable (Y n) :=
  (S.Ym n hn).mono (S.Fle n hn) le_rfl

lemma SI.Im' (S : SI μ F Y I m N τ β B) {n : ℕ} (hn : n ≤ N) : MeasurableSet (I n) :=
  S.Fle n hn _ (S.Im n hn)

lemma SI.kinv_int [IsFiniteMeasure μ] (S : SI μ F Y I m N τ β B) {n : ℕ} (hmn : m ≤ n)
    (hn : n ≤ N) (P : ℕ) :
    Integrable ((I n).indicator (fun ω => (Y n ω)⁻¹ ^ P)) μ := by
  refine Integrable.of_bound (((S.Ym' hn).inv.pow_const P).indicator (S.Im' hn)).aestronglyMeasurable
    ((τ n)⁻¹ ^ P) ?_
  filter_upwards [S.low n hmn hn] with ω hω
  rw [Real.norm_eq_abs]
  by_cases h : ω ∈ I n
  · rw [Set.indicator_of_mem h]
    have hτ := S.τpos n
    have hy := hω h
    rw [abs_of_nonneg (by have : 0 < Y n ω := by linarith
                          positivity)]
    exact pow_le_pow_left₀ (by have : 0 < Y n ω := by linarith
                               positivity) (inv_anti₀ hτ hy) _
  · rw [Set.indicator_of_notMem h, abs_zero]; have := S.τpos n; positivity

lemma SI.kpos_int [IsFiniteMeasure μ] (S : SI μ F Y I m N τ β B) {n : ℕ} (hn : n ≤ N) (P : ℕ) :
    Integrable ((I n).indicator (fun ω => Y n ω ^ P)) μ := by
  obtain ⟨r, hr⟩ := S.env n hn
  refine Integrable.of_bound (((S.Ym' hn).pow_const P).indicator (S.Im' hn)).aestronglyMeasurable
    (|r| ^ P) ?_
  filter_upwards [hr] with ω hω
  rw [Real.norm_eq_abs]
  by_cases h : ω ∈ I n
  · rw [Set.indicator_of_mem h, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hω.trans (le_abs_self _)) _
  · rw [Set.indicator_of_notMem h, abs_zero]; positivity

end G26


-- ===== Solutions.G26.RunSIN =====

/-! ### Compensated normalized pointwise variables (Lemma G.28, (G.595)–(G.601)) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

lemma EcorN_le {u : Fin d → ℝ} (hu : u ∈ DT ℬ θ astar) (n : ℕ) (ω : Ω) :
    |Ecor R θ u n ω| ≤ H.sig⁻¹ * Acum 𝒜 R θ n ω := by
  unfold Ecor Acum
  rw [Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => H.DT_dot_le _ u hu)

lemma IN_meas (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (C : ℝ)
    (τ : ℕ → ℝ) (m : ℕ) {n : ℕ} (hn : n ≤ T) :
    MeasurableSet[Fx R T n] (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C τ m n) := by
  refine (JN_meas hR _ m hn).inter ?_
  have : {ω | ∀ j, m ≤ j → j ≤ n → negMax (DT ℬ θ astar) (R.cumEst j ω)
      (cN 𝒜 R θ H.sig⁻¹ C j ω) ≤ τ j} = ⋂ j : ℕ, {ω | m ≤ j → j ≤ n →
      negMax (DT ℬ θ astar) (R.cumEst j ω) (cN 𝒜 R θ H.sig⁻¹ C j ω) ≤ τ j} := by
    ext ω; simp
  rw [this]
  refine MeasurableSet.iInter fun j => ?_
  by_cases h : m ≤ j ∧ j ≤ n
  · have e1 : {ω | m ≤ j → j ≤ n → negMax (DT ℬ θ astar) (R.cumEst j ω)
        (cN 𝒜 R θ H.sig⁻¹ C j ω) ≤ τ j} = {ω | negMax (DT ℬ θ astar) (R.cumEst j ω)
        (cN 𝒜 R θ H.sig⁻¹ C j ω) ≤ τ j} := by
      ext ω; simp [h.1, h.2]
    rw [e1]
    have hS := cumEst_Fx hR (le_trans h.2 hn)
    have hc : Measurable[Fx R T j] (cN 𝒜 R θ H.sig⁻¹ C j) :=
      (measurable_const.mul (measurable_const.sub
        (Acum_Fx H.h𝒜 H.ne𝒜 hR θ (le_trans h.2 hn)))).neg
    have hm := G26.negMax_meas H.DT_compact H.DT_ne hS hc
    exact Fx_mono' hR h.2 hn _ (measurableSet_le hm measurable_const)
  · have e1 : {ω | m ≤ j → j ≤ n → negMax (DT ℬ θ astar) (R.cumEst j ω)
        (cN 𝒜 R θ H.sig⁻¹ C j ω) ≤ τ j} = univ := by
      ext ω; simp only [mem_setOf_eq, mem_univ, iff_true]
      intro h1 h2; exact absurd ⟨h1, h2⟩ h
    rw [e1]; exact MeasurableSet.univ

end Sharp

end G26G


-- ===== Solutions.G26.RunEnv =====

/-! ### Envelopes of the run fields: absolute maxima and block crossings (Lemmas G.15, G.30) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26

variable {d : ℕ} {Ω : Type*}

lemma rdim_le (D : Set (Fin d → ℝ)) : rdim D ≤ d := by
  unfold rdim
  have := Submodule.finrank_le (vectorSpan ℝ D)
  simpa using this

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma FI.absMax_int [IsProbabilityMeasure μ] (I : FI D μ F T V c J β B lo hi m0) {n : ℕ}
    (hn : n ≤ T) (P : ℕ) : Integrable (fun ω => absMax D (V n ω) (c n ω) ^ P) μ := by
  obtain ⟨r, hr0, hr⟩ := I.env' hn
  refine Integrable.of_bound
    (((I.absMax_meas hn).mono (I.Fle n hn) le_rfl).pow_const P).aestronglyMeasurable (r ^ P) ?_
  filter_upwards [hr, I.N0 n hn] with ω h h0
  have h1 : 0 ≤ absMax D (V n ω) (c n ω) := h0.trans (negMax_le_absMax _ _)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h1 _)]
  exact pow_le_pow_left₀ h1 h.1 P

end G26

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma kk_facts (d : ℕ) : 2 ≤ kk d ∧ 4 ≤ 4 * kk d ∧ Even (4 * kk d) ∧ d ≤ 4 * kk d ∧
    2 ^ 20 * ((4 * kk d : ℕ) : ℝ) ≤ gB d := by
  unfold kk gB
  refine ⟨by omega, by omega, ⟨2 * (1024 * (d + 1)), by ring⟩, by omega, ?_⟩
  push_cast; nlinarith

lemma cK_nonneg (d : ℕ) : 0 ≤ cK d := by
  unfold cK Cabs; positivity

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

end Sharp

end G26G


-- ===== Solutions.G26.Params =====

/-! ### Thresholds: buffers `τ_s = (s+1)^{7/8} + 4z` and logarithmic gap cutoffs -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26G

open G26 G26R

lemma p78_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : x ^ ((7 : ℝ) / 8) ≤ y ^ ((7 : ℝ) / 8) :=
  Real.rpow_le_rpow hx hxy (by norm_num)

lemma p78_ge_one {x : ℝ} (hx : 1 ≤ x) : 1 ≤ x ^ ((7 : ℝ) / 8) :=
  Real.one_le_rpow hx (by norm_num)

lemma tauB_mono {z : ℝ} (s : ℕ) : tauB z s ≤ tauB z (s + 1) := by
  unfold tauB
  have := p78_mono (x := (s : ℝ) + 1) (y := ((s + 1 : ℕ) : ℝ) + 1) (by positivity) (by push_cast; linarith)
  linarith

lemma tauB_delta (z : ℝ) (s : ℕ) : tauB z (s + 1) - tauB z s ≤ 1 := by
  unfold tauB
  have h := Real.rpow_add_le_add_rpow (p := (7 : ℝ) / 8) (a := (s : ℝ) + 1) (b := 1)
    (by positivity) zero_le_one (by norm_num) (by norm_num)
  rw [Real.one_rpow] at h
  have e : ((s + 1 : ℕ) : ℝ) + 1 = (s : ℝ) + 1 + 1 := by push_cast; ring
  rw [e]; linarith

lemma tauB_ge {z : ℝ} (hz : 0 ≤ z) (s : ℕ) :
    ((s : ℝ) + 1) ^ ((7 : ℝ) / 8) ≤ tauB z s ∧ 4 * z ≤ tauB z s ∧ 1 ≤ tauB z s := by
  unfold tauB
  have h1 := p78_ge_one (x := (s : ℝ) + 1) (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])
  refine ⟨by linarith, ?_, by linarith⟩
  have : 0 ≤ ((s : ℝ) + 1) ^ ((7 : ℝ) / 8) := by positivity
  linarith

lemma tauB_pos {z : ℝ} (hz : 0 ≤ z) (s : ℕ) : 0 < tauB z s := by
  linarith [(tauB_ge hz s).2.2]

lemma root8_pow {x : ℝ} (hx : 0 ≤ x) : root8 x ^ 8 = x := by
  unfold root8
  have h1 : Real.sqrt (Real.sqrt (Real.sqrt x)) ^ 2 = Real.sqrt (Real.sqrt x) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have h2 : Real.sqrt (Real.sqrt x) ^ 2 = Real.sqrt x := Real.sq_sqrt (Real.sqrt_nonneg _)
  have h3 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  calc Real.sqrt (Real.sqrt (Real.sqrt x)) ^ 8 =
      ((Real.sqrt (Real.sqrt (Real.sqrt x)) ^ 2) ^ 2) ^ 2 := by ring
    _ = x := by rw [h1, h2, h3]

lemma root8_nonneg (x : ℝ) : 0 ≤ root8 x := Real.sqrt_nonneg _

lemma root8_mono {x y : ℝ} (hxy : x ≤ y) : root8 x ≤ root8 y := by
  unfold root8
  exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hxy))

end G26G

namespace G26G

lemma root8_eq_rpow {x : ℝ} (hx : 0 ≤ x) : root8 x = x ^ ((1 : ℝ) / 8) := by
  have h1 : (x ^ ((1 : ℝ) / 8)) ^ (8 : ℕ) = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  have h2 := root8_pow hx
  have hn1 : 0 ≤ x ^ ((1 : ℝ) / 8) := Real.rpow_nonneg hx _
  exact (pow_left_inj₀ (root8_nonneg x) hn1 (by norm_num : (8 : ℕ) ≠ 0)).1 (h2.trans h1.symm)

lemma rpow78_eq {x : ℝ} (hx : 0 ≤ x) : x ^ ((7 : ℝ) / 8) = root8 x ^ 7 := by
  rw [root8_eq_rpow hx, ← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

lemma sqrt_eq_root8 {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x = root8 x ^ 4 := by
  rw [root8_eq_rpow hx, ← Real.rpow_natCast, ← Real.rpow_mul hx, Real.sqrt_eq_rpow]; norm_num

end G26G


-- ===== Solutions.G26.RefAlg =====

/-! ### Real-variable estimates for the reference block bound -/

open IAFTRL

namespace G26G

lemma tauB_ge_r7 {z : ℝ} (hz : 0 ≤ z) (n : ℕ) : root8 ((n : ℝ) + 1) ^ 7 ≤ tauB z n := by
  rw [← rpow78_eq (by positivity)]; exact (tauB_ge hz n).1

end G26G


-- ===== Solutions.G26.WinRef =====

/-! ### The alive window (Lemma G.28): dyadic blocks and reference errors -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma Dexpr_nonneg (d : ℕ) {sig c0 : ℝ} (hs : 0 < sig) (hc0 : 0 ≤ c0) : 0 ≤ Dexpr d sig c0 := by
  obtain ⟨hk2, -, -, -, hB⟩ := kk_facts d
  have hB' : 2 ^ 20 * (4 * (kk d : ℝ)) ≤ gB d := by exact_mod_cast hB
  have hBp := G2R.gB_pos (d := d)
  have hHn : 0 ≤ Hneg (kk d) (16 * d + 1) (gB d) := by
    unfold Hneg Kneg
    have := vneg_lt (kk d) hk2 (gB d) hB'
    exact div_nonneg (by positivity) (by linarith)
  have hcK := cK_nonneg d
  have hsi : 0 ≤ sig⁻¹ := inv_nonneg.2 hs.le
  unfold Dexpr
  positivity

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

lemma Dref_nonneg : 0 ≤ H.Dref he :=
  Dexpr_nonneg d H.sig_pos (by have := H.D0_nonneg he; positivity)

end Sharp

end G26G


-- ===== Solutions.G26.WinCross =====

/-! ### The alive window (Lemma G.28): normalized crossings over dyadic blocks -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

omit he in
lemma Hneg_kb_nonneg : 0 ≤ Hneg (kk d) (H.kb * (16 * d + 1)) (gB d) := by
  obtain ⟨hk2, -, -, -, hB⟩ := kk_facts d
  have hB' : 2 ^ 20 * (4 * (kk d : ℝ)) ≤ gB d := by exact_mod_cast hB
  have hBp := G2R.gB_pos (d := d)
  have : 0 ≤ H.kb := by linarith [H.kb_ge.1]
  unfold Hneg Kneg
  have := vneg_lt (kk d) hk2 (gB d) hB'
  exact div_nonneg (by positivity) (by linarith)

omit he in
lemma cX1_nonneg : 0 ≤ H.cX1 := by
  have := cK_nonneg d; have := H.Lam1_pos; unfold cX1; positivity

omit he in
lemma cXB_nonneg : 0 ≤ H.cXB := by
  have := H.Hneg_kb_nonneg; unfold cXB; positivity

end Sharp

end G26G


-- ===== Solutions.G26.WinMom =====

/-! ### The alive window (Lemma G.28): local per-point moments of the compensated variable -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma thr_win {n : ℕ} {z l kb : ℝ} (hz : 0 ≤ z) (hl : 0 ≤ l) (hkb : 0 ≤ kb)
    (hr : cTw d l kb ≤ root8 ((n : ℝ) + 1)) :
    gB d * (gbeta d (n + 1) * l + 2 * l + 2) ≤ tauB z n ∧
    40 * (((4 * kk d : ℕ) : ℝ) + 1) * (kb * gbeta d (n + 1)) * ((n : ℝ) + 1) ≤ tauB z n ^ 2 ∧
    10 * (((4 * kk d : ℕ) : ℝ) - 1) * (kb * gbeta d (n + 1)) / tauB z n ≤ 1 ∧
    ((4 * kk d : ℕ) : ℝ) + 1 ≤ tauB z n ∧ ((4 * kk d : ℕ) : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1) := by
  set r := root8 ((n : ℝ) + 1)
  have hP0 : (0 : ℝ) ≤ ((4 * kk d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hB0 := G2R.gB_pos (d := d)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have t1 : 0 ≤ gB d * (l * (16 * d + 3) + 2) := by positivity
  have t2 : 0 ≤ 40 * (((4 * kk d : ℕ) : ℝ) + 1) * kb * (16 * d + 1) := by positivity
  have t3 : 0 ≤ 10 * ((4 * kk d : ℕ) : ℝ) * kb * (16 * d + 1) := by positivity
  have hc1 : 1 ≤ cTw d l kb := by unfold cTw; linarith
  have hr1 : 1 ≤ r := hc1.trans hr
  have hr8 : r ^ 8 = (n : ℝ) + 1 := root8_pow (by positivity)
  have hsq : Real.sqrt (((n + 1 : ℕ) : ℝ)) = r ^ 4 := by
    rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring]; exact sqrt_eq_root8 (by positivity)
  have hg : gbeta d (n + 1) ≤ (16 * d + 1) * r ^ 4 := by
    unfold gbeta; rw [hsq]
    have : (1 : ℝ) ≤ r ^ 4 := one_le_pow₀ hr1
    nlinarith
  have hg0 : 0 ≤ gbeta d (n + 1) := by unfold gbeta; positivity
  have hτ := tauB_ge_r7 hz n
  have hr4 : (1 : ℝ) ≤ r ^ 4 := one_le_pow₀ hr1
  have hr47 : r ^ 5 ≤ r ^ 7 := pow_le_pow_right₀ hr1 (by norm_num)
  have h5 : r ^ 4 * r = r ^ 5 := by ring
  -- the pieces of the threshold
  have hc_a : gB d * (l * (16 * d + 3) + 2) ≤ r := by
    refine le_trans ?_ hr; unfold cTw; linarith
  have hc_b : 40 * (((4 * kk d : ℕ) : ℝ) + 1) * kb * (16 * d + 1) ≤ r := by
    refine le_trans ?_ hr; unfold cTw; linarith
  have hc_c : 10 * ((4 * kk d : ℕ) : ℝ) * kb * (16 * d + 1) ≤ r := by
    refine le_trans ?_ hr; unfold cTw; linarith
  have hc_d : ((4 * kk d : ℕ) : ℝ) + 1 ≤ r := by
    refine le_trans ?_ hr; unfold cTw; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the buffer dominates the update magnitude
    have h1 : gbeta d (n + 1) * l + 2 * l + 2 ≤ (l * (16 * d + 3) + 2) * r ^ 4 := by
      have := mul_le_mul_of_nonneg_left hg hl
      nlinarith [mul_nonneg hl hd0]
    calc gB d * (gbeta d (n + 1) * l + 2 * l + 2) ≤ gB d * ((l * (16 * d + 3) + 2) * r ^ 4) :=
          mul_le_mul_of_nonneg_left h1 hB0.le
      _ = gB d * (l * (16 * d + 3) + 2) * r ^ 4 := by ring
      _ ≤ r * r ^ 4 := mul_le_mul_of_nonneg_right hc_a (by positivity)
      _ = r ^ 5 := by ring
      _ ≤ tauB z n := hr47.trans hτ
  · have h7 : r ^ 14 ≤ tauB z n ^ 2 := by
      rw [show 14 = 7 * 2 by norm_num, pow_mul]
      exact pow_le_pow_left₀ (by positivity) hτ 2
    have hP1 : 0 ≤ 40 * (((4 * kk d : ℕ) : ℝ) + 1) * kb := by positivity
    calc 40 * (((4 * kk d : ℕ) : ℝ) + 1) * (kb * gbeta d (n + 1)) * ((n : ℝ) + 1)
        = 40 * (((4 * kk d : ℕ) : ℝ) + 1) * kb * gbeta d (n + 1) * r ^ 8 := by rw [hr8]; ring
      _ ≤ 40 * (((4 * kk d : ℕ) : ℝ) + 1) * kb * ((16 * d + 1) * r ^ 4) * r ^ 8 := by gcongr
      _ = 40 * (((4 * kk d : ℕ) : ℝ) + 1) * kb * (16 * d + 1) * r ^ 12 := by ring
      _ ≤ r * r ^ 12 := mul_le_mul_of_nonneg_right hc_b (by positivity)
      _ = r ^ 13 := by ring
      _ ≤ r ^ 14 := pow_le_pow_right₀ hr1 (by norm_num)
      _ ≤ tauB z n ^ 2 := h7
  · have hτ0 : 0 < tauB z n := tauB_pos hz n
    rw [div_le_one hτ0]
    calc 10 * (((4 * kk d : ℕ) : ℝ) - 1) * (kb * gbeta d (n + 1))
        ≤ 10 * ((4 * kk d : ℕ) : ℝ) * kb * ((16 * d + 1) * r ^ 4) := by
          have : 10 * (((4 * kk d : ℕ) : ℝ) - 1) ≤ 10 * ((4 * kk d : ℕ) : ℝ) := by linarith
          calc 10 * (((4 * kk d : ℕ) : ℝ) - 1) * (kb * gbeta d (n + 1))
              ≤ 10 * ((4 * kk d : ℕ) : ℝ) * (kb * gbeta d (n + 1)) :=
                mul_le_mul_of_nonneg_right this (mul_nonneg hkb hg0)
            _ ≤ 10 * ((4 * kk d : ℕ) : ℝ) * (kb * ((16 * d + 1) * r ^ 4)) := by gcongr
            _ = _ := by ring
      _ = 10 * ((4 * kk d : ℕ) : ℝ) * kb * (16 * d + 1) * r ^ 4 := by ring
      _ ≤ r * r ^ 4 := mul_le_mul_of_nonneg_right hc_c (by positivity)
      _ = r ^ 5 := by ring
      _ ≤ tauB z n := hr47.trans hτ
  · calc ((4 * kk d : ℕ) : ℝ) + 1 ≤ r := hc_d
      _ ≤ r ^ 7 := le_self_pow₀ hr1 (by norm_num)
      _ ≤ tauB z n := hτ
  · have : r ≤ r ^ 8 := le_self_pow₀ hr1 (by norm_num)
    rw [hr8] at this; linarith

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

omit he in
lemma cTw_ge (n : ℕ) {z : ℝ} (hz : 0 ≤ z) (hr : cTw d H.sig⁻¹ H.kb ≤ root8 ((n : ℝ) + 1)) :
    gB d * (gbeta d (n + 1) * H.sig⁻¹ + 2 * H.sig⁻¹ + 2) ≤ tauB z n :=
  (thr_win hz (inv_nonneg.2 H.sig_pos.le) (by linarith [H.kb_ge.1]) hr).1

omit he in
lemma cTw_mono {m n : ℕ} (hmn : m ≤ n) (hr : cTw d H.sig⁻¹ H.kb ≤ root8 ((m : ℝ) + 1)) :
    cTw d H.sig⁻¹ H.kb ≤ root8 ((n : ℝ) + 1) :=
  hr.trans (root8_mono (by have : (m : ℝ) ≤ n := by exact_mod_cast hmn
                           linarith))

omit he in
/-- the compensated scalar interface on the window -/
theorem win_SI (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ}
    (hcor : IsCorruptedG P 𝒜 θ C T R) {u : Fin d → ℝ} (hu : u ∈ UT ℬ θ astar) {z : ℝ}
    (hz : 0 ≤ z) {m t : ℕ} (ht : t ≤ T) (hmc : cTw d H.sig⁻¹ H.kb ≤ root8 ((m : ℝ) + 1)) :
    SI P (Fx R T) (YN R θ H.sig⁻¹ C (tauB z) u)
      (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m) m t (tauB z)
      (fun n => H.kb * gbeta d (n + 1)) (gB d) :=
  H.runN_SI he hR hcor (H.UT_sub_DT hu) (fun n => tauB_pos hz n) tauB_mono (tauB_delta z) ht
    (fun n hn => H.cTw_ge n hz (H.cTw_mono hn hmc))

end Sharp

end G26G


-- ===== Solutions.G26.WinContr =====

/-! ### Lemma G.26: the contraction step on the projective body -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

/-- the compensated direction vector: `YN(u) = u ⬝ᵥ Vc + (lC + 2τ)` -/
noncomputable def Vc (R : GRun d Ω) (θ : Fin d → ℝ) (n : ℕ) (ω : Ω) : Fin d → ℝ :=
  R.cumEst n ω - ∑ j ∈ Finset.range n, (R.θs j ω - θ)

lemma YN_eq (θ : Fin d → ℝ) (l C : ℝ) (τ : ℕ → ℝ) (u : Fin d → ℝ) (n : ℕ) (ω : Ω) :
    YN R θ l C τ u n ω = u ⬝ᵥ Vc R θ n ω + (l * C + 2 * τ n) := by
  unfold YN Vc Ecor
  rw [dotProduct_sub, dotProduct_sum]; ring

lemma Vc_meas (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (θ : Fin d → ℝ) {n : ℕ} (hn : n ≤ T) :
    Measurable (Vc R θ n) := by
  unfold Vc
  refine (((cumEst_Fx hR hn).mono (Fx_le hR hn) le_rfl)).sub (Finset.measurable_sum _ fun j hj => ?_)
  have hj' := Finset.mem_range.1 hj
  exact (hR j (by omega)).1.2.2.2.1.sub measurable_const

lemma Agood_meas (h𝒜 : IsCompact 𝒜) (hne : 𝒜.Nonempty) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R)
    (θ : Fin d → ℝ) (C : ℝ) : MeasurableSet (Agood 𝒜 R θ C T) := by
  have e : Agood 𝒜 R θ C T = ⋂ n ∈ Finset.range (T + 1),
      {ω | 0 ≤ Acum 𝒜 R θ n ω ∧ Acum 𝒜 R θ n ω ≤ C} := by
    ext ω; simp only [Agood, mem_setOf_eq, mem_iInter, Finset.mem_range]
    exact ⟨fun h n hn => h n (by omega), fun h n hn => h n (by omega)⟩
  rw [e]
  refine Finset.measurableSet_biInter _ fun n hn => ?_
  have hm := (Acum_Fx h𝒜 hne hR θ (n := n) (by have := Finset.mem_range.1 hn; omega)).mono
    (Fx_le hR (by have := Finset.mem_range.1 hn; omega)) le_rfl
  exact (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

omit he in
lemma cCo_nonneg : 0 ≤ H.cCo := by
  have := cK_nonneg d; have := H.Lam1_pos; unfold cCo; positivity

omit he in
lemma Bad_meas (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (C z : ℝ) {t : ℕ} (ht : t ≤ T) :
    MeasurableSet (Bad ℬ 𝒜 R θ astar H.sig⁻¹ C z t) := by
  have hS := (cumEst_Fx hR ht).mono (Fx_le hR ht) le_rfl
  have hc : Measurable (cN 𝒜 R θ H.sig⁻¹ C t) := by
    unfold cN
    exact ((measurable_const.sub ((Acum_Fx H.h𝒜 H.ne𝒜 hR θ ht).mono (Fx_le hR ht) le_rfl)).const_mul
      _).neg
  exact measurableSet_lt measurable_const (negMax_meas H.UT_compact H.UT_ne hS hc)

end Sharp

end G26G


-- ===== Solutions.G26.WinRatio =====

/-! ### Lemma G.26: uniform ratios for the normalized cumulative loss estimate -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

/-- the normalized vector `S_t/(t+1)` -/
noncomputable def Vf (R : GRun d Ω) (t : ℕ) (ω : Ω) : Fin d → ℝ := (((t : ℝ) + 1)⁻¹) • R.cumEst t ω

lemma Vf_dot (x : Fin d → ℝ) (t : ℕ) (ω : Ω) :
    x ⬝ᵥ Vf R t ω = x ⬝ᵥ R.cumEst t ω / ((t : ℝ) + 1) := by
  unfold Vf; rw [dotProduct_smul, smul_eq_mul]; ring

lemma joint_meas {V : Ω → Fin d → ℝ} (hV : Measurable V) :
    Measurable fun z : Ω × (Fin d → ℝ) => z.2 ⬝ᵥ V z.1 :=
  Continuous.measurable (f := fun q : (Fin d → ℝ) × (Fin d → ℝ) => q.1 ⬝ᵥ q.2)
    (by simp only [dotProduct]; fun_prop) |>.comp (measurable_snd.prodMk (hV.comp measurable_fst))

/-- Tonelli transfer of per-point moment bounds to a body integral on an event -/
lemma tonelli_bound {X : Type*} [MeasurableSpace X] {σ : Measure X} [IsProbabilityMeasure σ]
    (G : Set Ω) (Φ : Ω → X → ENNReal) (g : Ω → X → ℝ) (hg : Measurable (Function.uncurry g))
    (hle : ∀ ω ∈ G, ∀ᵐ x ∂σ, Φ ω x ≤ ENNReal.ofReal (g ω x)) {K : ℝ}
    (hint : ∀ᵐ x ∂σ, ∫⁻ ω, ENNReal.ofReal (g ω x) ∂P ≤ ENNReal.ofReal K) :
    ∫⁻ ω, G.indicator (fun ω => ∫⁻ x, Φ ω x ∂σ) ω ∂P ≤ ENNReal.ofReal K := by
  calc ∫⁻ ω, G.indicator (fun ω => ∫⁻ x, Φ ω x ∂σ) ω ∂P
      ≤ ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (g ω x) ∂σ ∂P := by
        refine lintegral_mono fun ω => ?_
        by_cases hω : ω ∈ G
        · rw [indicator_of_mem hω]; exact lintegral_mono_ae (hle ω hω)
        · rw [indicator_of_notMem hω]; exact bot_le
    _ = ∫⁻ x, ∫⁻ ω, ENNReal.ofReal (g ω x) ∂P ∂σ :=
        lintegral_lintegral_swap ((ENNReal.measurable_ofReal.comp hg).aemeasurable)
    _ ≤ ∫⁻ x, ENNReal.ofReal K ∂σ := lintegral_mono_ae hint
    _ = ENNReal.ofReal K := by simp

open Classical in
lemma meas_ind_uncurry {s : Set Ω} (hs : MeasurableSet s) {h : Ω × (Fin d → ℝ) → ℝ}
    (hh : Measurable h) :
    Measurable (Function.uncurry fun ω x => s.indicator (fun ω => h (ω, x)) ω) := by
  have e : (Function.uncurry fun ω x => s.indicator (fun ω => h (ω, x)) ω) =
      fun z => if z.1 ∈ s then h z else 0 := by
    funext z; simp [Function.uncurry, Set.indicator_apply]
  rw [e]
  exact Measurable.ite (measurable_fst hs) hh measurable_const

/-- **weighted AM–GM transfer for the inverse minimum (G.546)–(G.548)** -/
lemma amgm_inv {m Rr F a1 a2 : ℝ} {P r s : ℕ} (hm : 0 < m) (hR : 0 ≤ Rr) (hF : 0 ≤ F)
    (ha1 : 0 < a1) (ha2 : 0 < a2) (hrP : r < P)
    (hsw : ((r : ℝ) * s) / ((P : ℝ) * ((P - r : ℕ) : ℝ)) + (s : ℝ) / ((P - r : ℕ) : ℝ) ≤ 1)
    (hJ : (m ^ (P - r))⁻¹ ≤ 2 ^ P * Rr ^ r * F) :
    (m⁻¹) ^ s ≤ (2 ^ P * a1 ^ ((r : ℝ) / P) * a2) ^ ((s : ℝ) / ((P - r : ℕ) : ℝ)) *
      (((r : ℝ) * s) / ((P : ℝ) * ((P - r : ℕ) : ℝ)) * (Rr ^ P / a1) +
        (s : ℝ) / ((P - r : ℕ) : ℝ) * (F / a2) +
        (1 - ((r : ℝ) * s) / ((P : ℝ) * ((P - r : ℕ) : ℝ)) - (s : ℝ) / ((P - r : ℕ) : ℝ))) := by
  set q : ℝ := ((P - r : ℕ) : ℝ) with hq
  have hq0 : 0 < q := by rw [hq]; exact_mod_cast Nat.sub_pos_of_lt hrP
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le r) hrP)
  set w1 := ((r : ℝ) * s) / ((P : ℝ) * q) with hw1
  set w2 := (s : ℝ) / q with hw2
  have hw10 : 0 ≤ w1 := by positivity
  have hw20 : 0 ≤ w2 := by positivity
  have hmi : 0 ≤ m⁻¹ := (inv_pos.2 hm).le
  -- the root inequality
  have h1 : (m⁻¹) ^ s = ((m⁻¹) ^ (P - r)) ^ ((s : ℝ) / q) := by
    rw [← Real.rpow_natCast ((m⁻¹)) (P - r), ← Real.rpow_mul hmi, ← hq,
      mul_div_cancel₀ _ hq0.ne', Real.rpow_natCast]
  have hA0 : 0 ≤ 2 ^ P * Rr ^ r * F := by positivity
  have h2 : ((m⁻¹) ^ (P - r)) ^ ((s : ℝ) / q) ≤ (2 ^ P * Rr ^ r * F) ^ ((s : ℝ) / q) := by
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    rw [inv_pow]; exact hJ
  have h3 : (2 ^ P * Rr ^ r * F) ^ ((s : ℝ) / q) =
      ((2 : ℝ) ^ P) ^ ((s : ℝ) / q) * (Rr ^ P) ^ w1 * F ^ w2 := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
    congr 2
    rw [← Real.rpow_natCast Rr r, ← Real.rpow_natCast Rr P, ← Real.rpow_mul hR,
      ← Real.rpow_mul hR, hw1]
    congr 1; field_simp
  -- AM-GM
  have hsum : w1 + w2 + (1 - w1 - w2) = 1 := by ring
  have h4 := Real.geom_mean_le_arith_mean3_weighted hw10 hw20 (by linarith) (by positivity : 0 ≤ Rr ^ P / a1)
    (by positivity : 0 ≤ F / a2) zero_le_one hsum
  rw [Real.one_rpow, mul_one, mul_one] at h4
  have h5 : (Rr ^ P) ^ w1 * F ^ w2 =
      a1 ^ w1 * a2 ^ w2 * ((Rr ^ P / a1) ^ w1 * (F / a2) ^ w2) := by
    rw [Real.div_rpow (by positivity) ha1.le, Real.div_rpow hF ha2.le]
    field_simp
  have h6 : (2 ^ P * a1 ^ ((r : ℝ) / P) * a2) ^ ((s : ℝ) / q) =
      ((2 : ℝ) ^ P) ^ ((s : ℝ) / q) * (a1 ^ w1 * a2 ^ w2) := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity)
      (by positivity), ← Real.rpow_mul ha1.le]
    have : (r : ℝ) / P * ((s : ℝ) / q) = w1 := by rw [hw1]; field_simp
    rw [this]; ring
  rw [h1, h6]
  refine h2.trans (le_of_eq_of_le h3 ?_)
  rw [mul_assoc, h5, ← mul_assoc]
  refine mul_le_mul_of_nonneg_left h4 ?_
  positivity

/-- the numerical constant: `(2^P a1^{r/P} a2)^{s/(P-r)} ≤ 17^s` -/
lemma K0_le {d r s : ℕ} (hrd : r ≤ d) :
    (2 ^ (4 * kk d) * ((2 : ℝ) ^ (4 * kk d) * 4 ^ d * 8 ^ (4 * kk d)) ^ ((r : ℝ) / (4 * kk d : ℕ)) *
      (8 : ℝ) ^ (4 * kk d)) ^ ((s : ℝ) / ((4 * kk d - r : ℕ) : ℝ)) ≤ 17 ^ s := by
  have hkk : kk d = 1024 * (d + 1) := by unfold kk; rfl
  set P := 4 * kk d with hP
  have hPd : d ≤ P := by rw [hP, hkk]; omega
  have hrP : r < P := by rw [hP, hkk]; omega
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le r) hrP)
  have hq0 : (0 : ℝ) < ((P - r : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hrP
  -- `a1^{r/P} ≤ 64^r`
  have ha1 : ((2 : ℝ) ^ P * 4 ^ d * 8 ^ P) ^ ((r : ℝ) / P) ≤ (64 : ℝ) ^ r := by
    have hle : (2 : ℝ) ^ P * 4 ^ d * 8 ^ P ≤ (64 : ℝ) ^ P := by
      have : (4 : ℝ) ^ d ≤ 4 ^ P := pow_le_pow_right₀ (by norm_num) hPd
      calc (2 : ℝ) ^ P * 4 ^ d * 8 ^ P ≤ 2 ^ P * 4 ^ P * 8 ^ P := by gcongr
        _ = 64 ^ P := by rw [← mul_pow, ← mul_pow]; norm_num
    calc ((2 : ℝ) ^ P * 4 ^ d * 8 ^ P) ^ ((r : ℝ) / P) ≤ ((64 : ℝ) ^ P) ^ ((r : ℝ) / P) :=
          Real.rpow_le_rpow (by positivity) hle (by positivity)
      _ = 64 ^ r := by
          rw [← Real.rpow_natCast (64 : ℝ) P, ← Real.rpow_mul (by norm_num),
            mul_div_cancel₀ _ hP0.ne', Real.rpow_natCast]
  have hbase : 2 ^ P * ((2 : ℝ) ^ P * 4 ^ d * 8 ^ P) ^ ((r : ℝ) / P) * (8 : ℝ) ^ P ≤
      (17 : ℝ) ^ (P - r) := by
    -- `16^P 64^r 17^r ≤ 17^P` from `1088^r ≤ (17/16)^P`
    have hB : (1088 : ℝ) ≤ (17 / 16) ^ 4096 := by
      have h := one_add_mul_le_pow (a := (1 / 16 : ℝ)) (by norm_num) 1024
      have h' : (65 : ℝ) ≤ (17 / 16) ^ 1024 := by norm_num at h ⊢; linarith
      calc (1088 : ℝ) ≤ 65 ^ 4 := by norm_num
        _ ≤ ((17 / 16) ^ 1024) ^ 4 := pow_le_pow_left₀ (by norm_num) h' 4
        _ = (17 / 16) ^ 4096 := by rw [← pow_mul]
    have hB2 : (1088 : ℝ) ^ r ≤ (17 / 16) ^ P := by
      calc (1088 : ℝ) ^ r ≤ ((17 / 16) ^ 4096) ^ r := pow_le_pow_left₀ (by norm_num) hB r
        _ = (17 / 16) ^ (4096 * r) := by rw [← pow_mul]
        _ ≤ (17 / 16) ^ P := pow_le_pow_right₀ (by norm_num) (by rw [hP, hkk]; nlinarith)
    have h17 : (17 : ℝ) ^ P = 17 ^ (P - r) * 17 ^ r := by rw [← pow_add, Nat.sub_add_cancel hrP.le]
    have hkey : (16 : ℝ) ^ P * 64 ^ r * 17 ^ r ≤ 17 ^ P := by
      have e : (17 : ℝ) ^ P = 16 ^ P * (17 / 16) ^ P := by rw [← mul_pow]; norm_num
      have e2 : (64 : ℝ) ^ r * 17 ^ r = 1088 ^ r := by rw [← mul_pow]; norm_num
      rw [e, mul_assoc, e2]
      exact mul_le_mul_of_nonneg_left hB2 (by positivity)
    calc 2 ^ P * ((2 : ℝ) ^ P * 4 ^ d * 8 ^ P) ^ ((r : ℝ) / P) * (8 : ℝ) ^ P
        ≤ 2 ^ P * 64 ^ r * 8 ^ P := by gcongr
      _ = 16 ^ P * 64 ^ r := by rw [mul_right_comm, ← mul_pow]; norm_num
      _ ≤ 17 ^ (P - r) := by
          rw [h17] at hkey
          have : (0 : ℝ) < 17 ^ r := by positivity
          nlinarith
  calc (2 ^ P * ((2 : ℝ) ^ P * 4 ^ d * 8 ^ P) ^ ((r : ℝ) / P) * (8 : ℝ) ^ P) ^
        ((s : ℝ) / ((P - r : ℕ) : ℝ))
      ≤ ((17 : ℝ) ^ (P - r)) ^ ((s : ℝ) / ((P - r : ℕ) : ℝ)) :=
        Real.rpow_le_rpow (by positivity) hbase (by positivity)
    _ = 17 ^ s := by
        rw [← Real.rpow_natCast (17 : ℝ) (P - r), ← Real.rpow_mul (by norm_num),
          mul_div_cancel₀ _ hq0.ne', Real.rpow_natCast]

/-- the maximum and minimum of the normalized field on `U_θ` -/
noncomputable def Rf (ℬ : Set (Fin d → ℝ)) (θ astar : Fin d → ℝ) (R : GRun d Ω) (t : ℕ) (ω : Ω) : ℝ :=
  posMax (UT ℬ θ astar) (Vf R t ω) 0

noncomputable def mf (ℬ : Set (Fin d → ℝ)) (θ astar : Fin d → ℝ) (R : GRun d Ω) (t : ℕ) (ω : Ω) : ℝ :=
  -negMax (UT ℬ θ astar) (Vf R t ω) 0

lemma Vf_meas (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (htT : t ≤ T) : Measurable (Vf R t) := by
  unfold Vf
  exact ((cumEst_Fx hR htT).mono (Fx_le hR htT) le_rfl).const_smul (((t : ℝ) + 1)⁻¹)

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

/-- **the pointwise comparisons on the good event (G.540)–(G.542)** -/
lemma good_facts {C z : ℝ} (hz : 0 ≤ z) {m t : ℕ} (hmt : m ≤ t) (htT : t ≤ T)
    (hlC : H.sig⁻¹ * C ≤ tauB z t) (hC : 0 ≤ C) {ω : Ω}
    (hω : ω ∈ Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C z T m t) {x : Fin d → ℝ}
    (hx : x ∈ UT ℬ θ astar) :
    4 * tauB z t ≤ x ⬝ᵥ R.cumEst t ω ∧
      x ⬝ᵥ R.cumEst t ω ≤ YN R θ H.sig⁻¹ C (tauB z) x t ω ∧
      YN R θ H.sig⁻¹ C (tauB z) x t ω ≤ 2 * (x ⬝ᵥ R.cumEst t ω) := by
  obtain ⟨⟨hI, hA⟩, hB⟩ := hω
  have hl0 : 0 ≤ H.sig⁻¹ := inv_nonneg.2 H.sig_pos.le
  obtain ⟨hA0, hAC⟩ := hA t htT
  have hB' : negMax (UT ℬ θ astar) (R.cumEst t ω) (cN 𝒜 R θ H.sig⁻¹ C t ω) ≤ -(4 * tauB z t) := by
    simp only [Bad, mem_compl_iff, mem_setOf_eq, not_lt] at hB; exact hB
  have h1 := (negMax_ge H.UT_compact hx (R.cumEst t ω) (cN 𝒜 R θ H.sig⁻¹ C t ω)).trans hB'
  unfold cN at h1
  have hlA : H.sig⁻¹ * Acum 𝒜 R θ t ω ≤ H.sig⁻¹ * C := mul_le_mul_of_nonneg_left hAC hl0
  have hlA0 : 0 ≤ H.sig⁻¹ * Acum 𝒜 R θ t ω := mul_nonneg hl0 hA0
  have e1 : H.sig⁻¹ * (C - Acum 𝒜 R θ t ω) = H.sig⁻¹ * C - H.sig⁻¹ * Acum 𝒜 R θ t ω := by ring
  have hEc := H.EcorN_le (H.UT_sub_DT hx) (R := R) t ω
  have := abs_le.1 hEc
  have hτ0 := tauB_pos hz t
  refine ⟨by linarith, ?_, ?_⟩ <;> unfold YN <;> linarith

omit he in
lemma nvolUT_prob : IsProbabilityMeasure (nvol (UT ℬ θ astar)) :=
  nvol_prob H.UT_compact H.UT_convex H.UT_ne

omit he in
lemma ae_UT : ∀ᵐ x ∂(nvol (UT ℬ θ astar)), x ∈ UT ℬ θ astar :=
  ae_iff.2 (nvol_supp H.UT_compact)

omit he in
lemma IN_meas' (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (C z : ℝ) {m t : ℕ}
    (htT : t ≤ T) : MeasurableSet (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m t) :=
  Fx_le hR htT _ (H.IN_meas he hR C (tauB z) m htT)

omit he in
lemma YN_joint (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (C z : ℝ) {t : ℕ} (htT : t ≤ T) :
    Measurable fun q : Ω × (Fin d → ℝ) => YN R θ H.sig⁻¹ C (tauB z) q.2 t q.1 := by
  simp only [YN_eq]
  exact (joint_meas (Vc_meas hR θ htT)).add measurable_const

set_option maxHeartbeats 1000000 in
omit he in
/-- **(G.543)**: the positive body moment on the good event -/
theorem win_Fpos (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ}
    (hC : 0 ≤ C) (hcor : IsCorruptedG P 𝒜 θ C T R) {z : ℝ} (hz : 0 ≤ z) {m t : ℕ} (hmt : m ≤ t)
    (htT : t < T) (hmc : cTw d H.sig⁻¹ H.kb ≤ root8 ((m : ℝ) + 1))
    (hlC : H.sig⁻¹ * C ≤ (m : ℝ) + 1) (hmz : (m : ℝ) + 1 ≤ z)
    (hzt : z ≤ ((t : ℝ) + 1) * root8 (((m : ℝ) + 1) / ((t : ℝ) + 1)) ^ 7)
    (hξ : (2 * (Lam1 ℬ θ astar * max 1 (cK d) + 4) + 16) * root8 (((m : ℝ) + 1) / ((t : ℝ) + 1)) ≤ 1) :
    ∫⁻ ω, (Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C z T m t).indicator
      (fun ω => ∫⁻ x, ENNReal.ofReal ((x ⬝ᵥ Vf R t ω) ^ (4 * kk d)) ∂(nvol (UT ℬ θ astar))) ω ∂P ≤
      ENNReal.ofReal (8 ^ (4 * kk d)) := by
  haveI := H.nvolUT_prob
  have hτ4 := (tauB_ge hz t).2.1
  have hlCτ : H.sig⁻¹ * C ≤ tauB z t := by linarith
  have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have hev : Even (4 * kk d) := (kk_facts d).2.2.1
  refine tonelli_bound (P := P) _ _ (fun ω x =>
    (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m t).indicator
      (fun ω => (YN R θ H.sig⁻¹ C (tauB z) x t ω / ((t : ℝ) + 1)) ^ (4 * kk d)) ω)
    (meas_ind_uncurry (H.IN_meas' he hR C z htT.le)
      (((H.YN_joint hR C z htT.le).div_const _).pow_const _)) ?_ ?_
  · intro ω hω
    filter_upwards [H.ae_UT] with x hx
    obtain ⟨h1, h2, -⟩ := H.good_facts he hz hmt htT.le hlCτ hC hω hx
    rw [indicator_of_mem hω.1.1, Vf_dot]
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (div_nonneg (by linarith [tauB_pos hz t])
      ht1.le) (div_le_div_of_nonneg_right h2 ht1.le) _)
  · filter_upwards [H.ae_UT] with x hx
    have S := H.win_SI he hR hcor hx hz (t := t) htT.le hmc
    have hk := H.win_pos he hR hC hcor hx hz hmt htT hmc hlC hzt hξ
    have e1 : (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m t).indicator
        (fun ω => (YN R θ H.sig⁻¹ C (tauB z) x t ω / ((t : ℝ) + 1)) ^ (4 * kk d)) =
        fun ω => (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m t).indicator
          (fun ω => YN R θ H.sig⁻¹ C (tauB z) x t ω ^ (4 * kk d)) ω / ((t : ℝ) + 1) ^ (4 * kk d) := by
      funext ω
      by_cases hI : ω ∈ IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m t
      · rw [indicator_of_mem hI, indicator_of_mem hI, div_pow]
      · rw [indicator_of_notMem hI, indicator_of_notMem hI, zero_div]
    have hint := (S.kpos_int le_rfl (4 * kk d)).div_const (((t : ℝ) + 1) ^ (4 * kk d))
    have h0 : 0 ≤ᵐ[P] fun ω => (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m t).indicator
        (fun ω => YN R θ H.sig⁻¹ C (tauB z) x t ω ^ (4 * kk d)) ω / ((t : ℝ) + 1) ^ (4 * kk d) :=
      Filter.Eventually.of_forall fun ω => div_nonneg
        (Set.indicator_nonneg (fun ω _ => hev.pow_nonneg _) ω) (by positivity)
    simp only [e1]
    rw [← ofReal_integral_eq_lintegral_ofReal hint h0, integral_div]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ (by positivity)]
    calc _ = kpos P (YN R θ H.sig⁻¹ C (tauB z) x)
          (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m) (4 * kk d) t := rfl
      _ ≤ (8 * ((t : ℝ) + 1)) ^ (4 * kk d) := hk
      _ = 8 ^ (4 * kk d) * ((t : ℝ) + 1) ^ (4 * kk d) := mul_pow _ _ _

set_option maxHeartbeats 1000000 in
omit he in
/-- **(G.544)**: the inverse body moment on the good event -/
theorem win_Finv (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ}
    (hC : 0 ≤ C) (hcor : IsCorruptedG P 𝒜 θ C T R) {z : ℝ} (hz : 0 ≤ z) {m t : ℕ} (hmt : m ≤ t)
    (htT : t < T) (hmc : cTw d H.sig⁻¹ H.kb ≤ root8 ((m : ℝ) + 1))
    (hmhalf : 2 * ((m : ℝ) + 1) ≤ (t : ℝ) + 1)
    (hlC : H.sig⁻¹ * C ≤ (m : ℝ) + 1) (hmz : (m : ℝ) + 1 ≤ z) :
    ∫⁻ ω, (Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C z T m t).indicator
      (fun ω => ∫⁻ x, ENNReal.ofReal (((x ⬝ᵥ Vf R t ω) ^ (4 * kk d))⁻¹)
        ∂(nvol (UT ℬ θ astar))) ω ∂P ≤ ENNReal.ofReal (8 ^ (4 * kk d)) := by
  haveI := H.nvolUT_prob
  have hτ4 := (tauB_ge hz t).2.1
  have hlCτ : H.sig⁻¹ * C ≤ tauB z t := by linarith
  have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have hev : Even (4 * kk d) := (kk_facts d).2.2.1
  refine tonelli_bound (P := P) _ _ (fun ω x =>
    (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m t).indicator
      (fun ω => (2 * ((t : ℝ) + 1)) ^ (4 * kk d) *
        (YN R θ H.sig⁻¹ C (tauB z) x t ω)⁻¹ ^ (4 * kk d)) ω)
    (meas_ind_uncurry (H.IN_meas' he hR C z htT.le)
      (measurable_const.mul (((H.YN_joint hR C z htT.le).inv).pow_const _))) ?_ ?_
  · intro ω hω
    filter_upwards [H.ae_UT] with x hx
    obtain ⟨h1, h2, h3⟩ := H.good_facts he hz hmt htT.le hlCτ hC hω hx
    rw [indicator_of_mem hω.1.1, Vf_dot]
    refine ENNReal.ofReal_le_ofReal ?_
    have hτ0 := tauB_pos hz t
    have hS0 : 0 < x ⬝ᵥ R.cumEst t ω := by linarith
    have hY0 : 0 < YN R θ H.sig⁻¹ C (tauB z) x t ω := by linarith
    rw [← inv_pow, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [inv_div, div_le_iff₀ hS0]
    have hYY : (YN R θ H.sig⁻¹ C (tauB z) x t ω)⁻¹ * YN R θ H.sig⁻¹ C (tauB z) x t ω = 1 :=
      inv_mul_cancel₀ hY0.ne'
    calc ((t : ℝ) + 1) = ((t : ℝ) + 1) * ((YN R θ H.sig⁻¹ C (tauB z) x t ω)⁻¹ *
          YN R θ H.sig⁻¹ C (tauB z) x t ω) := by rw [hYY, mul_one]
      _ = 2 * ((t : ℝ) + 1) * (YN R θ H.sig⁻¹ C (tauB z) x t ω)⁻¹ *
          (YN R θ H.sig⁻¹ C (tauB z) x t ω / 2) := by ring
      _ ≤ 2 * ((t : ℝ) + 1) * (YN R θ H.sig⁻¹ C (tauB z) x t ω)⁻¹ * (x ⬝ᵥ R.cumEst t ω) := by
          gcongr; linarith
  · filter_upwards [H.ae_UT] with x hx
    have S := H.win_SI he hR hcor hx hz (t := t) htT.le hmc
    have hk := H.win_inv he hR hcor hx hz hmt htT hmc hmhalf
    have e1 : (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m t).indicator
        (fun ω => (2 * ((t : ℝ) + 1)) ^ (4 * kk d) *
          (YN R θ H.sig⁻¹ C (tauB z) x t ω)⁻¹ ^ (4 * kk d)) =
        fun ω => (2 * ((t : ℝ) + 1)) ^ (4 * kk d) *
          (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m t).indicator
          (fun ω => (YN R θ H.sig⁻¹ C (tauB z) x t ω)⁻¹ ^ (4 * kk d)) ω := by
      funext ω
      by_cases hI : ω ∈ IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m t
      · rw [indicator_of_mem hI, indicator_of_mem hI]
      · rw [indicator_of_notMem hI, indicator_of_notMem hI, mul_zero]
    have hint := (S.kinv_int hmt le_rfl (4 * kk d)).const_mul ((2 * ((t : ℝ) + 1)) ^ (4 * kk d))
    have h0 : 0 ≤ᵐ[P] fun ω => (2 * ((t : ℝ) + 1)) ^ (4 * kk d) *
        (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m t).indicator
          (fun ω => (YN R θ H.sig⁻¹ C (tauB z) x t ω)⁻¹ ^ (4 * kk d)) ω :=
      Filter.Eventually.of_forall fun ω => mul_nonneg (by positivity)
        (Set.indicator_nonneg (fun ω _ => hev.pow_nonneg _) ω)
    simp only [e1]
    rw [← ofReal_integral_eq_lintegral_ofReal hint h0, integral_const_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (2 * ((t : ℝ) + 1)) ^ (4 * kk d) * kinv P (YN R θ H.sig⁻¹ C (tauB z) x)
          (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m) (4 * kk d) t
        ≤ (2 * ((t : ℝ) + 1)) ^ (4 * kk d) * (4 / ((t : ℝ) + 1)) ^ (4 * kk d) :=
          mul_le_mul_of_nonneg_left hk (by positivity)
      _ = 8 ^ (4 * kk d) := by rw [← mul_pow]; congr 1; field_simp; ring

omit he in
lemma Gev_meas (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (C z : ℝ) {m t : ℕ}
    (htT : t ≤ T) : MeasurableSet (Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C z T m t) :=
  ((H.IN_meas' he hR C z htT).inter (Agood_meas H.h𝒜 H.ne𝒜 hR θ C)).inter
    (H.Bad_meas hR C z htT).compl

omit he in
lemma Rf_meas (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (htT : t ≤ T) :
    Measurable (Rf ℬ θ astar R t) := by
  have h := (posMax_cont H.UT_compact H.UT_ne).measurable.comp
    ((Vf_meas hR htT).prodMk (measurable_const (a := (0 : ℝ))))
  exact h

omit he in
lemma mf_meas (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (htT : t ≤ T) :
    Measurable (mf ℬ θ astar R t) :=
  (negMax_meas H.UT_compact H.UT_ne (Vf_meas hR htT) measurable_const).neg

/-- positivity of the normalized field on the good event -/
lemma good_pos {C z : ℝ} (hz : 0 ≤ z) {m t : ℕ} (hmt : m ≤ t) (htT : t ≤ T)
    (hlC : H.sig⁻¹ * C ≤ tauB z t) (hC : 0 ≤ C) {ω : Ω}
    (hω : ω ∈ Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C z T m t) {x : Fin d → ℝ}
    (hx : x ∈ UT ℬ θ astar) : 4 * tauB z t / ((t : ℝ) + 1) ≤ x ⬝ᵥ Vf R t ω + 0 := by
  rw [add_zero, Vf_dot]
  exact div_le_div_of_nonneg_right (H.good_facts he hz hmt htT hlC hC hω hx).1 (by positivity)

set_option maxHeartbeats 1000000 in
omit he in
/-- **(G.545)**: the maximum moment on the good event -/
theorem win_U (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ}
    (hC : 0 ≤ C) (hcor : IsCorruptedG P 𝒜 θ C T R) {z : ℝ} (hz : 0 ≤ z) {m t : ℕ} (hmt : m ≤ t)
    (htT : t < T) (hmc : cTw d H.sig⁻¹ H.kb ≤ root8 ((m : ℝ) + 1))
    (hlC : H.sig⁻¹ * C ≤ (m : ℝ) + 1) (hmz : (m : ℝ) + 1 ≤ z)
    (hzt : z ≤ ((t : ℝ) + 1) * root8 (((m : ℝ) + 1) / ((t : ℝ) + 1)) ^ 7)
    (hξ : (2 * (Lam1 ℬ θ astar * max 1 (cK d) + 4) + 16) * root8 (((m : ℝ) + 1) / ((t : ℝ) + 1)) ≤ 1) :
    ∫⁻ ω, (Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C z T m t).indicator
      (fun ω => ENNReal.ofReal (Rf ℬ θ astar R t ω ^ (4 * kk d))) ω ∂P ≤
      ENNReal.ofReal (2 ^ (4 * kk d) * 4 ^ d * 8 ^ (4 * kk d)) := by
  haveI := H.nvolUT_prob
  have hτ4 := (tauB_ge hz t).2.1
  have hlCτ : H.sig⁻¹ * C ≤ tauB z t := by linarith
  have hτ0 := tauB_pos hz t
  have hev : Even (4 * kk d) := (kk_facts d).2.2.1
  have hF := H.win_Fpos he hR hC hcor hz hmt htT hmc hlC hmz hzt hξ
  set G := Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C z T m t with hG
  have hpt : ∀ ω, G.indicator (fun ω => ENNReal.ofReal (Rf ℬ θ astar R t ω ^ (4 * kk d))) ω ≤
      ENNReal.ofReal (2 ^ (4 * kk d) * 4 ^ d) * G.indicator (fun ω => ∫⁻ x, ENNReal.ofReal
        ((x ⬝ᵥ Vf R t ω) ^ (4 * kk d)) ∂(nvol (UT ℬ θ astar))) ω := by
    intro ω
    by_cases hω : ω ∈ G
    · rw [indicator_of_mem hω, indicator_of_mem hω]
      obtain ⟨x0, hx0, -, hmax⟩ := absMax_mem H.UT_compact H.UT_ne (Vf R t ω) 0
      have hJ := J17 H.UT_compact H.UT_convex H.UT_ne (Vf R t ω) 0 hx0 hmax (4 * kk d)
      obtain ⟨x1, hx1, hx1e⟩ := posMax_mem H.UT_compact H.UT_ne (Vf R t ω) 0
      have hp1 := H.good_pos he hz hmt htT.le hlCτ hC hω hx1
      have hRf : 0 ≤ Rf ℬ θ astar R t ω := by
        unfold Rf; rw [← hx1e]; exact le_trans (by positivity) hp1
      have hRle : Rf ℬ θ astar R t ω ≤ |x0 ⬝ᵥ Vf R t ω + 0| := by
        unfold Rf; rw [← hx1e]; exact (le_abs_self _).trans (hmax x1 hx1)
      have h4 : (4 : ℝ) ^ rdim (UT ℬ θ astar) ≤ 4 ^ d := pow_le_pow_right₀ (by norm_num) (rdim_le _)
      have hint0 : 0 ≤ ∫ x, |x ⬝ᵥ Vf R t ω + 0| ^ (4 * kk d) ∂(nvol (UT ℬ θ astar)) :=
        integral_nonneg fun x => by positivity
      have hreal : Rf ℬ θ astar R t ω ^ (4 * kk d) ≤ 2 ^ (4 * kk d) * 4 ^ d *
          ∫ x, |x ⬝ᵥ Vf R t ω + 0| ^ (4 * kk d) ∂(nvol (UT ℬ θ astar)) := by
        calc Rf ℬ θ astar R t ω ^ (4 * kk d) ≤ |x0 ⬝ᵥ Vf R t ω + 0| ^ (4 * kk d) :=
              pow_le_pow_left₀ hRf hRle _
          _ ≤ _ := hJ
          _ ≤ _ := by gcongr
      calc ENNReal.ofReal (Rf ℬ θ astar R t ω ^ (4 * kk d))
          ≤ ENNReal.ofReal (2 ^ (4 * kk d) * 4 ^ d) * ENNReal.ofReal
              (∫ x, |x ⬝ᵥ Vf R t ω + 0| ^ (4 * kk d) ∂(nvol (UT ℬ θ astar))) := by
            rw [← ENNReal.ofReal_mul (by positivity)]; exact ENNReal.ofReal_le_ofReal hreal
        _ ≤ ENNReal.ofReal (2 ^ (4 * kk d) * 4 ^ d) * ∫⁻ x, ENNReal.ofReal
              (|x ⬝ᵥ Vf R t ω + 0| ^ (4 * kk d)) ∂(nvol (UT ℬ θ astar)) :=
            mul_le_mul_of_nonneg_left (ofReal_int_le fun x => by positivity) bot_le
        _ = _ := by
            congr 1; congr 1; funext x; rw [add_zero, hev.pow_abs]
    · rw [indicator_of_notMem hω, indicator_of_notMem hω, mul_zero]
  calc ∫⁻ ω, G.indicator (fun ω => ENNReal.ofReal (Rf ℬ θ astar R t ω ^ (4 * kk d))) ω ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (2 ^ (4 * kk d) * 4 ^ d) * G.indicator (fun ω => ∫⁻ x,
          ENNReal.ofReal ((x ⬝ᵥ Vf R t ω) ^ (4 * kk d)) ∂(nvol (UT ℬ θ astar))) ω ∂P :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (2 ^ (4 * kk d) * 4 ^ d) * ∫⁻ ω, G.indicator (fun ω => ∫⁻ x,
          ENNReal.ofReal ((x ⬝ᵥ Vf R t ω) ^ (4 * kk d)) ∂(nvol (UT ℬ θ astar))) ω ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 ^ (4 * kk d) * 4 ^ d) * ENNReal.ofReal (8 ^ (4 * kk d)) :=
        mul_le_mul_of_nonneg_left hF bot_le
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

set_option maxHeartbeats 2000000 in
omit he in
/-- **(G.546)–(G.549)**: the inverse minimum moments on the good event -/
theorem win_minv (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ}
    (hC : 0 ≤ C) (hcor : IsCorruptedG P 𝒜 θ C T R) {z : ℝ} (hz : 0 ≤ z) {m t : ℕ} (hmt : m ≤ t)
    (htT : t < T) (hmc : cTw d H.sig⁻¹ H.kb ≤ root8 ((m : ℝ) + 1))
    (hmhalf : 2 * ((m : ℝ) + 1) ≤ (t : ℝ) + 1)
    (hlC : H.sig⁻¹ * C ≤ (m : ℝ) + 1) (hmz : (m : ℝ) + 1 ≤ z)
    (hzt : z ≤ ((t : ℝ) + 1) * root8 (((m : ℝ) + 1) / ((t : ℝ) + 1)) ^ 7)
    (hξ : (2 * (Lam1 ℬ θ astar * max 1 (cK d) + 4) + 16) * root8 (((m : ℝ) + 1) / ((t : ℝ) + 1)) ≤ 1)
    {s : ℕ} (hs : s ≤ 10) :
    ∫⁻ ω, (Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C z T m t).indicator
      (fun ω => ENNReal.ofReal ((mf ℬ θ astar R t ω)⁻¹ ^ s)) ω ∂P ≤ ENNReal.ofReal (17 ^ s) := by
  haveI := H.nvolUT_prob
  have hτ4 := (tauB_ge hz t).2.1
  have hlCτ : H.sig⁻¹ * C ≤ tauB z t := by linarith
  have hτ0 := tauB_pos hz t
  have hev : Even (4 * kk d) := (kk_facts d).2.2.1
  have hkk : kk d = 1024 * (d + 1) := by unfold kk; rfl
  set r := rdim (UT ℬ θ astar) with hr
  have hrd : r ≤ d := rdim_le _
  have hrP : r < 4 * kk d := by rw [hkk]; omega
  have hq20 : (20 : ℝ) ≤ ((4 * kk d - r : ℕ) : ℝ) := by
    have : 20 ≤ 4 * kk d - r := by rw [hkk]; omega
    exact_mod_cast this
  have hq0 : (0 : ℝ) < ((4 * kk d - r : ℕ) : ℝ) := by linarith
  have hP0 : (0 : ℝ) < ((4 * kk d : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le r) hrP)
  have hrPr : (r : ℝ) ≤ ((4 * kk d : ℕ) : ℝ) := by exact_mod_cast hrP.le
  have hs0 : (s : ℝ) ≤ 10 := by exact_mod_cast hs
  set q : ℝ := ((4 * kk d - r : ℕ) : ℝ) with hq
  set w1 : ℝ := ((r : ℝ) * s) / (((4 * kk d : ℕ) : ℝ) * q) with hw1
  set w2 : ℝ := (s : ℝ) / q with hw2
  have hw10 : 0 ≤ w1 := by positivity
  have hw20 : 0 ≤ w2 := by positivity
  have hw1le : w1 ≤ w2 := by
    rw [hw1, hw2, mul_comm (r : ℝ), mul_div_assoc, div_mul_eq_div_div]
    have : (r : ℝ) / ((4 * kk d : ℕ) : ℝ) ≤ 1 := (div_le_one hP0).2 hrPr
    calc (s : ℝ) * ((r : ℝ) / ((4 * kk d : ℕ) : ℝ) / q) = (s : ℝ) / q * ((r : ℝ) / ((4 * kk d : ℕ) : ℝ)) := by ring
      _ ≤ (s : ℝ) / q * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = (s : ℝ) / q := mul_one _
  have hw2le : w2 ≤ 1 / 2 := by
    rw [hw2, div_le_iff₀ hq0]; linarith
  have hsw : w1 + w2 ≤ 1 := by linarith
  set a1 : ℝ := 2 ^ (4 * kk d) * 4 ^ d * 8 ^ (4 * kk d) with ha1
  set a2 : ℝ := 8 ^ (4 * kk d) with ha2
  have ha10 : 0 < a1 := by positivity
  have ha20 : 0 < a2 := by positivity
  set K0 : ℝ := (2 ^ (4 * kk d) * a1 ^ ((r : ℝ) / ((4 * kk d : ℕ) : ℝ)) * a2) ^ ((s : ℝ) / q) with hK0
  have hK0le : K0 ≤ 17 ^ s := K0_le hrd
  have hK00 : 0 ≤ K0 := by positivity
  set G := Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C z T m t with hG
  set Ψ : Ω → ENNReal := fun ω => ∫⁻ x, ENNReal.ofReal (((x ⬝ᵥ Vf R t ω) ^ (4 * kk d))⁻¹)
    ∂(nvol (UT ℬ θ astar)) with hΨ
  have hΨm : Measurable Ψ := by
    have hj := ENNReal.measurable_ofReal.comp
      (((joint_meas (Vf_meas hR htT.le)).pow_const (4 * kk d)).inv)
    exact hj.lintegral_prod_right'
  set k1 : ℝ := K0 * w1 / a1 with hk1
  set k2 : ℝ := K0 * w2 / a2 with hk2
  set k3 : ℝ := K0 * (1 - w1 - w2) with hk3
  have hk10 : 0 ≤ k1 := by positivity
  have hk20 : 0 ≤ k2 := by positivity
  have hk30 : 0 ≤ k3 := mul_nonneg hK00 (by linarith)
  -- the pointwise bound
  have hpt : ∀ ω, G.indicator (fun ω => ENNReal.ofReal ((mf ℬ θ astar R t ω)⁻¹ ^ s)) ω ≤
      (ENNReal.ofReal k1 * G.indicator (fun ω => ENNReal.ofReal (Rf ℬ θ astar R t ω ^ (4 * kk d))) ω +
        ENNReal.ofReal k2 * G.indicator Ψ ω) + ENNReal.ofReal k3 := by
    intro ω
    by_cases hω : ω ∈ G
    · rw [indicator_of_mem hω, indicator_of_mem hω, indicator_of_mem hω]
      obtain ⟨x0, hx0, hx0e⟩ := negMax_mem H.UT_compact H.UT_ne (Vf R t ω) 0
      have hpos : ∀ x ∈ UT ℬ θ astar, 0 < x ⬝ᵥ Vf R t ω + 0 := fun x hx =>
        lt_of_lt_of_le (by positivity) (H.good_pos he hz hmt htT.le hlCτ hC hω hx)
      have hmin : ∀ x ∈ UT ℬ θ astar, x0 ⬝ᵥ Vf R t ω + 0 ≤ x ⬝ᵥ Vf R t ω + 0 := by
        intro x hx
        have := negMax_ge H.UT_compact hx (Vf R t ω) 0
        rw [← hx0e] at this; linarith
      have hRx : ∀ x ∈ UT ℬ θ astar, x ⬝ᵥ Vf R t ω + 0 ≤ Rf ℬ θ astar R t ω := fun x hx =>
        posMax_ge H.UT_compact hx (Vf R t ω) 0
      have hJ := J20 H.UT_compact H.UT_convex H.UT_ne (Vf R t ω) 0 hx0 hpos hmin hRx
        (p := 4 * kk d) (by rw [← hr]; exact hrP.le)
      have hmeq : x0 ⬝ᵥ Vf R t ω + 0 = mf ℬ θ astar R t ω := by unfold mf; rw [← hx0e]; ring
      rw [hmeq] at hJ
      have hm0 : 0 < mf ℬ θ astar R t ω := hmeq ▸ hpos x0 hx0
      have hRf0 : 0 ≤ Rf ℬ θ astar R t ω := (hpos x0 hx0).le.trans (hRx x0 hx0)
      set F := ∫ x, ((x ⬝ᵥ Vf R t ω + 0) ^ (4 * kk d))⁻¹ ∂(nvol (UT ℬ θ astar)) with hF
      have hF0 : 0 ≤ F := integral_nonneg fun x => inv_nonneg.2 (hev.pow_nonneg _)
      have hA := amgm_inv (P := 4 * kk d) (r := r) (s := s) hm0 hRf0 hF0 ha10 ha20 hrP hsw hJ
      have hreal : (mf ℬ θ astar R t ω)⁻¹ ^ s ≤
          k1 * Rf ℬ θ astar R t ω ^ (4 * kk d) + k2 * F + k3 := by
        refine hA.trans (le_of_eq ?_)
        rw [hk1, hk2, hk3, hK0, hw1, hw2, hq]; ring
      have hFΨ : ENNReal.ofReal F ≤ Ψ ω := by
        rw [hΨ]; simp only [add_zero] at hF ⊢
        rw [hF]; exact ofReal_int_le fun x => inv_nonneg.2 (hev.pow_nonneg _)
      calc ENNReal.ofReal ((mf ℬ θ astar R t ω)⁻¹ ^ s)
          ≤ ENNReal.ofReal (k1 * Rf ℬ θ astar R t ω ^ (4 * kk d) + k2 * F + k3) :=
            ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal k1 * ENNReal.ofReal (Rf ℬ θ astar R t ω ^ (4 * kk d)) +
              ENNReal.ofReal k2 * ENNReal.ofReal F + ENNReal.ofReal k3 := by
            rw [ENNReal.ofReal_add (by positivity) hk30, ENNReal.ofReal_add (by positivity)
              (by positivity), ENNReal.ofReal_mul hk10, ENNReal.ofReal_mul hk20]
        _ ≤ _ := by gcongr
    · rw [indicator_of_notMem hω]; exact bot_le
  have hU := H.win_U he hR hC hcor hz hmt htT hmc hlC hmz hzt hξ
  have hFi := H.win_Finv he hR hC hcor hz hmt htT hmc hmhalf hlC hmz
  have hGm := H.Gev_meas he hR C z (m := m) htT.le
  have hm1 : Measurable fun ω => ENNReal.ofReal k1 *
      G.indicator (fun ω => ENNReal.ofReal (Rf ℬ θ astar R t ω ^ (4 * kk d))) ω :=
    measurable_const.mul ((ENNReal.measurable_ofReal.comp
      ((H.Rf_meas hR htT.le).pow_const _)).indicator hGm)
  calc ∫⁻ ω, G.indicator (fun ω => ENNReal.ofReal ((mf ℬ θ astar R t ω)⁻¹ ^ s)) ω ∂P
      ≤ ∫⁻ ω, ((ENNReal.ofReal k1 * G.indicator (fun ω => ENNReal.ofReal
          (Rf ℬ θ astar R t ω ^ (4 * kk d))) ω + ENNReal.ofReal k2 * G.indicator Ψ ω) +
          ENNReal.ofReal k3) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal k1 * ∫⁻ ω, G.indicator (fun ω => ENNReal.ofReal
          (Rf ℬ θ astar R t ω ^ (4 * kk d))) ω ∂P +
          ENNReal.ofReal k2 * ∫⁻ ω, G.indicator Ψ ω ∂P + ENNReal.ofReal k3 := by
        rw [lintegral_add_right _ measurable_const, lintegral_add_left hm1,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal k1 * ENNReal.ofReal a1 + ENNReal.ofReal k2 * ENNReal.ofReal a2 +
          ENNReal.ofReal k3 := by gcongr
    _ = ENNReal.ofReal (k1 * a1 + k2 * a2 + k3) := by
        rw [ENNReal.ofReal_add (by positivity) hk30, ENNReal.ofReal_add (by positivity)
          (by positivity), ENNReal.ofReal_mul hk10, ENNReal.ofReal_mul hk20]
    _ = ENNReal.ofReal K0 := by
        congr 1
        rw [hk1, hk2, hk3, div_mul_cancel₀ _ ha10.ne', div_mul_cancel₀ _ ha20.ne']; ring
    _ ≤ ENNReal.ofReal (17 ^ s) := ENNReal.ofReal_le_ofReal hK0le

end Sharp

end G26G


-- ===== Solutions.G26.WinLU =====

/-! ### Lemma G.26: the ratio variables `L_t, U_t` and their product moments -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

/-- the ratio variables, vanishing off the good event -/
noncomputable def Lt (G : Set Ω) (ℬ : Set (Fin d → ℝ)) (θ astar : Fin d → ℝ) (R : GRun d Ω) (t : ℕ) :
    Ω → ℝ :=
  G.indicator fun ω => max 1 (mf ℬ θ astar R t ω)⁻¹

noncomputable def Ut (G : Set Ω) (ℬ : Set (Fin d → ℝ)) (θ astar : Fin d → ℝ) (R : GRun d Ω) (t : ℕ) :
    Ω → ℝ :=
  G.indicator (Rf ℬ θ astar R t)

lemma max_pow_le {y : ℝ} (hy : 0 ≤ y) (n : ℕ) : max 1 y ^ n ≤ 1 + y ^ n := by
  rcases le_total 1 y with h | h
  · rw [max_eq_right h]; linarith [pow_nonneg (zero_le_one.trans h) n]
  · rw [max_eq_left h, one_pow]; linarith [pow_nonneg hy n]

lemma sq_le_tail {y c : ℝ} (hy : 0 ≤ y) (hc : 0 < c) {P : ℕ} (hP : 2 ≤ P) :
    y ^ 2 ≤ c ^ 2 + y ^ P / c ^ (P - 2) := by
  rcases le_total y c with h | h
  · have := pow_le_pow_left₀ hy h 2
    have : 0 ≤ y ^ P / c ^ (P - 2) := by positivity
    linarith
  · have h1 : c ^ (P - 2) ≤ y ^ (P - 2) := pow_le_pow_left₀ hc.le h _
    have h2 : y ^ P = y ^ 2 * y ^ (P - 2) := by rw [← pow_add]; congr 1; omega
    have h3 : y ^ 2 ≤ y ^ P / c ^ (P - 2) := by
      rw [le_div_iff₀ (by positivity), h2]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith

lemma amgm_k {a b κ : ℝ} (hκ : 0 < κ) : a * b ≤ (a ^ 2 / κ + κ * b ^ 2) / 2 := by
  have h : 0 ≤ (a - κ * b) ^ 2 / κ := by positivity
  have e : (a - κ * b) ^ 2 / κ = a ^ 2 / κ + κ * b ^ 2 - 2 * (a * b) := by field_simp; ring
  linarith

/-- real integral bound from a lintegral bound for a nonnegative integrable function -/
lemma int_le_of_lint {f : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (hfm : AEStronglyMeasurable f P) {K : ℝ}
    (hK : 0 ≤ K) (h : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal K) : ∫ ω, f ω ∂P ≤ K := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfm]
  exact ENNReal.toReal_le_of_le_ofReal hK h

lemma ofReal_ind (G : Set Ω) (g : Ω → ℝ) (ω : Ω) :
    ENNReal.ofReal (G.indicator g ω) = G.indicator (fun ω => ENNReal.ofReal (g ω)) ω := by
  by_cases h : ω ∈ G
  · rw [indicator_of_mem h, indicator_of_mem h]
  · rw [indicator_of_notMem h, indicator_of_notMem h, ENNReal.ofReal_zero]

lemma c17 (d : ℕ) : (2 : ℝ) ^ (4 * kk d) * 4 ^ d * 8 ^ (4 * kk d) ≤ 17 ^ (4 * kk d) := by
  have hkk : kk d = 1024 * (d + 1) := by unfold kk; rfl
  have hB : (4 : ℝ) ≤ (17 / 16) ^ 4096 := by
    have h := one_add_mul_le_pow (a := (1 / 16 : ℝ)) (by norm_num) 1024
    have h' : (65 : ℝ) ≤ (17 / 16) ^ 1024 := by norm_num at h ⊢; linarith
    calc (4 : ℝ) ≤ 65 := by norm_num
      _ ≤ (17 / 16) ^ 1024 := h'
      _ ≤ (17 / 16) ^ 4096 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hB2 : (4 : ℝ) ^ d ≤ (17 / 16) ^ (4 * kk d) := by
    calc (4 : ℝ) ^ d ≤ ((17 / 16) ^ 4096) ^ d := pow_le_pow_left₀ (by norm_num) hB d
      _ = (17 / 16) ^ (4096 * d) := by rw [← pow_mul]
      _ ≤ (17 / 16) ^ (4 * kk d) := pow_le_pow_right₀ (by norm_num) (by rw [hkk]; omega)
  have e1 : (2 : ℝ) ^ (4 * kk d) * 4 ^ d * 8 ^ (4 * kk d) = 16 ^ (4 * kk d) * 4 ^ d := by
    rw [mul_right_comm, ← mul_pow]; norm_num
  have e2 : (17 : ℝ) ^ (4 * kk d) = 16 ^ (4 * kk d) * (17 / 16) ^ (4 * kk d) := by
    rw [← mul_pow]; norm_num
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hB2 (by positivity)

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

set_option maxHeartbeats 2000000 in
omit he in
/-- **the product moments (G.550)–(G.551)**: `E[L^r U] ≤ 64^{r+1}` -/
theorem win_LU (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ}
    (hC : 0 ≤ C) (hcor : IsCorruptedG P 𝒜 θ C T R) {z : ℝ} (hz : 0 ≤ z) {m t : ℕ} (hmt : m ≤ t)
    (htT : t < T) (hmc : cTw d H.sig⁻¹ H.kb ≤ root8 ((m : ℝ) + 1))
    (hmhalf : 2 * ((m : ℝ) + 1) ≤ (t : ℝ) + 1)
    (hlC : H.sig⁻¹ * C ≤ (m : ℝ) + 1) (hmz : (m : ℝ) + 1 ≤ z)
    (hzt : z ≤ ((t : ℝ) + 1) * root8 (((m : ℝ) + 1) / ((t : ℝ) + 1)) ^ 7)
    (hξ : (2 * (Lam1 ℬ θ astar * max 1 (cK d) + 4) + 16) * root8 (((m : ℝ) + 1) / ((t : ℝ) + 1)) ≤ 1)
    {r : ℕ} (hr1 : 1 ≤ r) (hr5 : r ≤ 5) :
    Integrable (fun ω => Lt (Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C z T m t) ℬ θ astar R t ω ^ r *
        Ut (Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C z T m t) ℬ θ astar R t ω) P ∧
      ∫ ω, Lt (Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C z T m t) ℬ θ astar R t ω ^ r *
        Ut (Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C z T m t) ℬ θ astar R t ω ∂P ≤ 64 ^ (r + 1) := by
  set G := Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C z T m t with hG
  have hGm := H.Gev_meas he hR C z (m := m) htT.le
  have hτ4 := (tauB_ge hz t).2.1
  have hlCτ : H.sig⁻¹ * C ≤ tauB z t := by linarith
  have hτ0 := tauB_pos hz t
  have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have hL0 := H.Lam1_pos
  have hP2 : 2 ≤ 4 * kk d := by have := (kk_facts d).1; omega
  -- pointwise facts on the good event
  set RX := fun ω => absMax (Kset ℬ) (R.cumEst t ω) (-(astar ⬝ᵥ R.cumEst t ω)) with hRX
  have hRX0 : ∀ ω, 0 ≤ RX ω := fun ω =>
    (abs_nonneg _).trans (abs_le_absMax H.Kc H.haK (R.cumEst t ω) (-(astar ⬝ᵥ R.cumEst t ω)))
  have hmf : ∀ ω ∈ G, 4 * tauB z t / ((t : ℝ) + 1) ≤ mf ℬ θ astar R t ω := by
    intro ω hω
    obtain ⟨x0, hx0, hx0e⟩ := negMax_mem H.UT_compact H.UT_ne (Vf R t ω) 0
    have := H.good_pos he hz hmt htT.le hlCτ hC hω hx0
    unfold mf; rw [← hx0e]; linarith
  have hRf : ∀ ω ∈ G, 0 ≤ Rf ℬ θ astar R t ω ∧
      Rf ℬ θ astar R t ω ≤ Lam1 ℬ θ astar * RX ω / ((t : ℝ) + 1) := by
    intro ω hω
    obtain ⟨x1, hx1, hx1e⟩ := posMax_mem H.UT_compact H.UT_ne (Vf R t ω) 0
    have hp := H.good_pos he hz hmt htT.le hlCτ hC hω hx1
    have hM : ∀ a ∈ Kset ℬ, |(a - astar) ⬝ᵥ R.cumEst t ω| ≤ RX ω := by
      intro a ha
      have := abs_le_absMax H.Kc ha (R.cumEst t ω) (-(astar ⬝ᵥ R.cumEst t ω))
      rwa [sub_dotProduct, sub_eq_add_neg]
    have h1 := H.Lam1_spec hM (H.UT_sub_DT hx1)
    rw [add_zero, Vf_dot] at hp
    unfold Rf; rw [← hx1e, add_zero, Vf_dot]
    refine ⟨le_trans (by positivity) hp, ?_⟩
    exact div_le_div_of_nonneg_right ((le_abs_self _).trans h1) ht1.le
  set Lb := max 1 (((t : ℝ) + 1) / (4 * tauB z t)) with hLb
  have hLb1 : 1 ≤ Lb := le_max_left _ _
  have hLt : ∀ ω, 0 ≤ Lt G ℬ θ astar R t ω ∧ Lt G ℬ θ astar R t ω ≤ Lb := by
    intro ω
    unfold Lt
    by_cases hω : ω ∈ G
    · rw [indicator_of_mem hω]
      refine ⟨zero_le_one.trans (le_max_left _ _), max_le_max le_rfl ?_⟩
      have h := hmf ω hω
      have hm0 : 0 < mf ℬ θ astar R t ω := lt_of_lt_of_le (by positivity) h
      rw [inv_le_comm₀ hm0 (by positivity), inv_div]; exact h
    · rw [indicator_of_notMem hω]; exact ⟨le_rfl, by linarith⟩
  have hUt : ∀ ω, 0 ≤ Ut G ℬ θ astar R t ω ∧
      Ut G ℬ θ astar R t ω ≤ Lam1 ℬ θ astar * RX ω / ((t : ℝ) + 1) := by
    intro ω
    unfold Ut
    by_cases hω : ω ∈ G
    · rw [indicator_of_mem hω]; exact hRf ω hω
    · rw [indicator_of_notMem hω]; exact ⟨le_rfl, by have := hRX0 ω; positivity⟩
  -- measurability and integrability
  have hLm : Measurable (Lt G ℬ θ astar R t) :=
    (measurable_const.max (H.mf_meas hR htT.le).inv).indicator hGm
  have hUm : Measurable (Ut G ℬ θ astar R t) := (H.Rf_meas hR htT.le).indicator hGm
  have IK := runK_FI H.hd H.h𝒜 H.hℬ H.hgen H.hspan hR H.haK
  have hRX1 : Integrable RX P := by
    have := IK.absMax_int htT.le 1; simpa using this
  have hRX2 : Integrable (fun ω => RX ω ^ 2) P := IK.absMax_int htT.le 2
  have hRXP : Integrable (fun ω => RX ω ^ (4 * kk d)) P := IK.absMax_int htT.le (4 * kk d)
  have hU2i : Integrable (fun ω => Ut G ℬ θ astar R t ω ^ 2) P := by
    refine (hRX2.const_mul ((Lam1 ℬ θ astar / ((t : ℝ) + 1)) ^ 2)).mono' (hUm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    obtain ⟨h0, h1⟩ := hUt ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_pow]
    exact pow_le_pow_left₀ h0 (by rw [mul_comm, mul_div_assoc', mul_comm]; exact h1) 2
  have hL2i : Integrable (fun ω => Lt G ℬ θ astar R t ω ^ (2 * r)) P := by
    refine (integrable_const (Lb ^ (2 * r))).mono' (hLm.pow_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    obtain ⟨h0, h1⟩ := hLt ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ h0 h1 _
  have hLUi : Integrable (fun ω => Lt G ℬ θ astar R t ω ^ r * Ut G ℬ θ astar R t ω) P := by
    refine (hRX1.const_mul (Lb ^ r * (Lam1 ℬ θ astar / ((t : ℝ) + 1)))).mono'
      ((hLm.pow_const r).mul hUm).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    obtain ⟨h0, h1⟩ := hLt ω
    obtain ⟨h2, h3⟩ := hUt ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc Lt G ℬ θ astar R t ω ^ r * Ut G ℬ θ astar R t ω
        ≤ Lb ^ r * (Lam1 ℬ θ astar * RX ω / ((t : ℝ) + 1)) :=
          mul_le_mul (pow_le_pow_left₀ h0 h1 r) h3 h2 (by positivity)
      _ = Lb ^ r * (Lam1 ℬ θ astar / ((t : ℝ) + 1)) * RX ω := by ring
  refine ⟨hLUi, ?_⟩
  -- the moment of `L^{2r}`
  have hminv := H.win_minv he hR hC hcor hz hmt htT hmc hmhalf hlC hmz hzt hξ (s := 2 * r) (by omega)
  have hIm : ∀ ω ∈ G, (mf ℬ θ astar R t ω)⁻¹ ≤ ((t : ℝ) + 1) / (4 * tauB z t) := by
    intro ω hω
    have h := hmf ω hω
    have hm0 : 0 < mf ℬ θ astar R t ω := lt_of_lt_of_le (by positivity) h
    rw [inv_le_comm₀ hm0 (by positivity), inv_div]; exact h
  have hgi : Integrable (G.indicator fun ω => (mf ℬ θ astar R t ω)⁻¹ ^ (2 * r)) P := by
    refine (integrable_const ((((t : ℝ) + 1) / (4 * tauB z t)) ^ (2 * r))).mono'
      ((((H.mf_meas hR htT.le).inv).pow_const _).indicator hGm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ G
    · rw [indicator_of_mem hω, Real.norm_eq_abs, abs_of_nonneg]
      · have hm0 : 0 < mf ℬ θ astar R t ω := lt_of_lt_of_le (by positivity) (hmf ω hω)
        exact pow_le_pow_left₀ (inv_nonneg.2 hm0.le) (hIm ω hω) _
      · have hm0 : 0 < mf ℬ θ astar R t ω := lt_of_lt_of_le (by positivity) (hmf ω hω)
        positivity
    · rw [indicator_of_notMem hω, norm_zero]; positivity
  have hgint : ∫ ω, G.indicator (fun ω => (mf ℬ θ astar R t ω)⁻¹ ^ (2 * r)) ω ∂P ≤ 17 ^ (2 * r) := by
    refine int_le_of_lint (fun ω => ?_) hgi.aestronglyMeasurable (by positivity) ?_
    · by_cases hω : ω ∈ G
      · rw [indicator_of_mem hω]
        have hm0 : 0 < mf ℬ θ astar R t ω := lt_of_lt_of_le (by positivity) (hmf ω hω)
        positivity
      · rw [indicator_of_notMem hω]
    · simp only [ofReal_ind]; exact hminv
  have hL2 : ∫ ω, Lt G ℬ θ astar R t ω ^ (2 * r) ∂P ≤ 1 + 17 ^ (2 * r) := by
    calc ∫ ω, Lt G ℬ θ astar R t ω ^ (2 * r) ∂P
        ≤ ∫ ω, (1 + G.indicator (fun ω => (mf ℬ θ astar R t ω)⁻¹ ^ (2 * r)) ω) ∂P := by
          refine integral_mono hL2i ((integrable_const 1).add hgi) fun ω => ?_
          unfold Lt
          by_cases hω : ω ∈ G
          · rw [indicator_of_mem hω, indicator_of_mem hω]
            have hm0 : 0 < mf ℬ θ astar R t ω := lt_of_lt_of_le (by positivity) (hmf ω hω)
            exact max_pow_le (inv_nonneg.2 hm0.le) _
          · rw [indicator_of_notMem hω, indicator_of_notMem hω, zero_pow (by omega)]; norm_num
      _ = 1 + ∫ ω, G.indicator (fun ω => (mf ℬ θ astar R t ω)⁻¹ ^ (2 * r)) ω ∂P := by
          rw [integral_add (integrable_const 1) hgi]; simp
      _ ≤ 1 + 17 ^ (2 * r) := by linarith
  -- the moment of `U^2`
  have hUP := H.win_U he hR hC hcor hz hmt htT hmc hlC hmz hzt hξ
  have hfi : Integrable (G.indicator fun ω => Rf ℬ θ astar R t ω ^ (4 * kk d)) P := by
    refine (hRXP.const_mul ((Lam1 ℬ θ astar / ((t : ℝ) + 1)) ^ (4 * kk d))).mono'
      (((H.Rf_meas hR htT.le).pow_const _).indicator hGm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ G
    · rw [indicator_of_mem hω, Real.norm_eq_abs]
      obtain ⟨h0, h1⟩ := hRf ω hω
      rw [abs_of_nonneg (by positivity), ← mul_pow]
      exact pow_le_pow_left₀ h0 (by rw [mul_comm, mul_div_assoc', mul_comm]; exact h1) _
    · rw [indicator_of_notMem hω, norm_zero]; have := hRX0 ω; positivity
  have hfint : ∫ ω, G.indicator (fun ω => Rf ℬ θ astar R t ω ^ (4 * kk d)) ω ∂P ≤
      2 ^ (4 * kk d) * 4 ^ d * 8 ^ (4 * kk d) := by
    refine int_le_of_lint (fun ω => ?_) hfi.aestronglyMeasurable (by positivity) ?_
    · by_cases hω : ω ∈ G
      · rw [indicator_of_mem hω]; exact pow_nonneg (hRf ω hω).1 _
      · rw [indicator_of_notMem hω]
    · simp only [ofReal_ind]; exact hUP
  have hU2 : ∫ ω, Ut G ℬ θ astar R t ω ^ 2 ∂P ≤ 2 * 17 ^ 2 := by
    calc ∫ ω, Ut G ℬ θ astar R t ω ^ 2 ∂P
        ≤ ∫ ω, ((17 : ℝ) ^ 2 + G.indicator (fun ω => Rf ℬ θ astar R t ω ^ (4 * kk d)) ω /
            17 ^ (4 * kk d - 2)) ∂P := by
          refine integral_mono hU2i ((integrable_const _).add (hfi.div_const _)) fun ω => ?_
          have h := sq_le_tail (hUt ω).1 (by norm_num : (0 : ℝ) < 17) hP2
          refine h.trans (le_of_eq ?_)
          congr 1; unfold Ut
          by_cases hω : ω ∈ G
          · rw [indicator_of_mem hω, indicator_of_mem hω]
          · rw [indicator_of_notMem hω, indicator_of_notMem hω, zero_pow (by omega)]
      _ = 17 ^ 2 + (∫ ω, G.indicator (fun ω => Rf ℬ θ astar R t ω ^ (4 * kk d)) ω ∂P) /
            17 ^ (4 * kk d - 2) := by
          rw [integral_add (integrable_const _) (hfi.div_const _), integral_div]; simp
      _ ≤ 17 ^ 2 + 17 ^ (4 * kk d) / 17 ^ (4 * kk d - 2) := by
          gcongr; exact hfint.trans (c17 d)
      _ = 2 * 17 ^ 2 := by
          have e : (17 : ℝ) ^ (4 * kk d) = 17 ^ (4 * kk d - 2) * 17 ^ 2 := by
            rw [← pow_add]; congr 1; omega
          rw [e, mul_div_cancel_left₀ _ (by positivity)]; ring
  -- AM-GM
  have hκ : (0 : ℝ) < 64 ^ (r - 1) := by positivity
  calc ∫ ω, Lt G ℬ θ astar R t ω ^ r * Ut G ℬ θ astar R t ω ∂P
      ≤ ∫ ω, (Lt G ℬ θ astar R t ω ^ (2 * r) / 64 ^ (r - 1) +
          64 ^ (r - 1) * Ut G ℬ θ astar R t ω ^ 2) / 2 ∂P := by
        refine integral_mono hLUi (((hL2i.div_const _).add (hU2i.const_mul _)).div_const _)
          fun ω => ?_
        have h := amgm_k (a := Lt G ℬ θ astar R t ω ^ r) (b := Ut G ℬ θ astar R t ω) hκ
        rwa [← pow_mul, mul_comm r 2] at h
    _ = ((∫ ω, Lt G ℬ θ astar R t ω ^ (2 * r) ∂P) / 64 ^ (r - 1) +
          64 ^ (r - 1) * ∫ ω, Ut G ℬ θ astar R t ω ^ 2 ∂P) / 2 := by
        rw [integral_div, integral_add (hL2i.div_const _) (hU2i.const_mul _), integral_div,
          integral_const_mul]
    _ ≤ ((1 + 17 ^ (2 * r)) / 64 ^ (r - 1) + 64 ^ (r - 1) * (2 * 17 ^ 2)) / 2 := by gcongr
    _ ≤ 64 ^ (r + 1) := by
        have h1 : (1 : ℝ) + 17 ^ (2 * r) ≤ 64 ^ (2 * r) := by
          have : (2 : ℝ) * 17 ^ (2 * r) ≤ 64 ^ (2 * r) := by
            rw [pow_mul, pow_mul]
            have h : (2 : ℝ) * (17 ^ 2) ^ r ≤ (2 * 17 ^ 2) ^ r := by
              rw [mul_pow]; gcongr; exact le_self_pow₀ (by norm_num) (by omega)
            exact h.trans (pow_le_pow_left₀ (by norm_num) (by norm_num) r)
          have : (1 : ℝ) ≤ 17 ^ (2 * r) := one_le_pow₀ (by norm_num)
          linarith
        have e1 : (64 : ℝ) ^ (2 * r) / 64 ^ (r - 1) = 64 ^ (r + 1) := by
          rw [div_eq_iff (by positivity), ← pow_add]; congr 1; omega
        have e2 : (64 : ℝ) ^ (r - 1) * 64 ^ 2 = 64 ^ (r + 1) := by
          rw [← pow_add]; congr 1; omega
        have h2 : (1 + 17 ^ (2 * r)) / 64 ^ (r - 1) ≤ (64 : ℝ) ^ (r + 1) := by
          rw [← e1]; gcongr
        have h3 : (64 : ℝ) ^ (r - 1) * (2 * 17 ^ 2) ≤ 64 ^ (r + 1) := by
          rw [← e2]; gcongr; norm_num
        linarith

omit he in
/-- **the gap comparisons on the good event (G.552)–(G.554)** -/
theorem win_gaps (he : Function.Surjective e) {C z : ℝ} (hz : 0 ≤ z) (hC : 0 ≤ C) {m t : ℕ}
    (hmt : m ≤ t) (htT : t ≤ T) (hlC : H.sig⁻¹ * C ≤ tauB z t) {ω : Ω}
    (hω : ω ∈ Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C z T m t) :
    1 ≤ Lt (Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C z T m t) ℬ θ astar R t ω ∧
    0 ≤ Ut (Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C z T m t) ℬ θ astar R t ω ∧
    ∀ a ∈ Kset ℬ,
      4 * ((t + 1 : ℕ) : ℝ) ^ ((7 : ℝ) / 8) * ((a - astar) ⬝ᵥ θ) ≤ (a - astar) ⬝ᵥ R.cumEst t ω ∧
      (a - astar) ⬝ᵥ θ ≤ Lt (Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C z T m t) ℬ θ astar R t ω *
        ((a - astar) ⬝ᵥ R.cumEst t ω / ((t : ℝ) + 1)) ∧
      (a - astar) ⬝ᵥ R.cumEst t ω / ((t : ℝ) + 1) ≤
        Ut (Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C z T m t) ℬ θ astar R t ω * ((a - astar) ⬝ᵥ θ) := by
  set G := Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C z T m t with hG
  have hτ0 := tauB_pos hz t
  have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have hL : Lt G ℬ θ astar R t ω = max 1 (mf ℬ θ astar R t ω)⁻¹ := by
    unfold Lt; rw [indicator_of_mem hω]
  have hU : Ut G ℬ θ astar R t ω = Rf ℬ θ astar R t ω := by
    unfold Ut; rw [indicator_of_mem hω]
  -- the minimum is positive
  obtain ⟨x0, hx0, hx0e⟩ := negMax_mem H.UT_compact H.UT_ne (Vf R t ω) 0
  have hm0 : 0 < mf ℬ θ astar R t ω := by
    have := H.good_pos he hz hmt htT hlC hC hω hx0
    have h4 : 0 < 4 * tauB z t / ((t : ℝ) + 1) := div_pos (by linarith) ht1
    unfold mf; rw [← hx0e]
    linarith
  have hRf0 : 0 ≤ Rf ℬ θ astar R t ω :=
    hm0.le.trans (by unfold mf Rf; rw [← hx0e]; have := posMax_ge H.UT_compact hx0 (Vf R t ω) 0
                     linarith)
  refine ⟨hL ▸ le_max_left _ _, hU ▸ hRf0, fun a ha => ?_⟩
  by_cases hne : a = astar
  · subst hne; simp
  have hg := H.gap_pos ha hne
  have hu := H.ndir_mem ha hne
  have hX : (a - astar) ⬝ᵥ R.cumEst t ω = gap θ astar a * (ndir θ astar a ⬝ᵥ R.cumEst t ω) :=
    (gap_ndir_dot a (R.cumEst t ω)).resolve_right hg.ne'
  obtain ⟨h1, -, -⟩ := H.good_facts he hz hmt htT hlC hC hω hu
  have hgθ : (a - astar) ⬝ᵥ θ = gap θ astar a := rfl
  have hf : ndir θ astar a ⬝ᵥ Vf R t ω + 0 = ndir θ astar a ⬝ᵥ R.cumEst t ω / ((t : ℝ) + 1) := by
    rw [add_zero, Vf_dot]
  have hfm : mf ℬ θ astar R t ω ≤ ndir θ astar a ⬝ᵥ R.cumEst t ω / ((t : ℝ) + 1) := by
    have := negMax_ge H.UT_compact hu (Vf R t ω) 0
    unfold mf; rw [← hf]; linarith
  have hfR : ndir θ astar a ⬝ᵥ R.cumEst t ω / ((t : ℝ) + 1) ≤ Rf ℬ θ astar R t ω := by
    rw [← hf]; exact posMax_ge H.UT_compact hu (Vf R t ω) 0
  have hτ78 : ((t + 1 : ℕ) : ℝ) ^ ((7 : ℝ) / 8) ≤ tauB z t := by
    have := (tauB_ge hz t).1; push_cast; exact this
  rw [hgθ, hX, hL, hU]
  refine ⟨?_, ?_, ?_⟩
  · calc 4 * ((t + 1 : ℕ) : ℝ) ^ ((7 : ℝ) / 8) * gap θ astar a ≤ 4 * tauB z t * gap θ astar a := by
          gcongr
      _ ≤ gap θ astar a * (ndir θ astar a ⬝ᵥ R.cumEst t ω) := by nlinarith
  · have hfpos : 0 < ndir θ astar a ⬝ᵥ R.cumEst t ω / ((t : ℝ) + 1) := lt_of_lt_of_le hm0 hfm
    have h1' : 1 ≤ max 1 (mf ℬ θ astar R t ω)⁻¹ * (ndir θ astar a ⬝ᵥ R.cumEst t ω / ((t : ℝ) + 1)) := by
      calc (1 : ℝ) = (mf ℬ θ astar R t ω)⁻¹ * mf ℬ θ astar R t ω := (inv_mul_cancel₀ hm0.ne').symm
        _ ≤ (mf ℬ θ astar R t ω)⁻¹ * (ndir θ astar a ⬝ᵥ R.cumEst t ω / ((t : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hfm (inv_nonneg.2 hm0.le)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hfpos.le
    calc gap θ astar a = gap θ astar a * 1 := (mul_one _).symm
      _ ≤ gap θ astar a * (max 1 (mf ℬ θ astar R t ω)⁻¹ *
            (ndir θ astar a ⬝ᵥ R.cumEst t ω / ((t : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left h1' hg.le
      _ = _ := by ring
  · calc gap θ astar a * (ndir θ astar a ⬝ᵥ R.cumEst t ω) / ((t : ℝ) + 1)
        = gap θ astar a * (ndir θ astar a ⬝ᵥ R.cumEst t ω / ((t : ℝ) + 1)) := by ring
      _ ≤ gap θ astar a * Rf ℬ θ astar R t ω := mul_le_mul_of_nonneg_left hfR hg.le
      _ = _ := by ring

end Sharp

end G26G


-- ===== Solutions.G26.WinPar =====

/-! ### Lemma G.26: the window parameters and the per-round failure bound -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma log_e_ge {x : ℝ} (hx : 1 ≤ x) : 1 ≤ Real.log (Real.exp 1 * x) := by
  rw [Real.log_mul (Real.exp_pos 1).ne' (by linarith), Real.log_exp]
  linarith [Real.log_nonneg hx]

lemma Hcf_facts {C : ℝ} (hC : 0 ≤ C) : 1 ≤ nCf C ∧ C ≤ nCf C ∧ (nCf C : ℝ) + 1 ≤ Hcf C ∧ 1 ≤ Hcf C := by
  have h1 : C ≤ (nCf C : ℝ) := by
    unfold nCf; push_cast; linarith [Nat.le_ceil C]
  have hn : (1 : ℝ) ≤ (nCf C : ℝ) + 1 := by linarith [(Nat.cast_nonneg (nCf C) : (0 : ℝ) ≤ _)]
  have hl := log_e_ge hn
  have h3 : (nCf C : ℝ) + 1 ≤ Hcf C := by
    unfold Hcf; nlinarith
  exact ⟨by unfold nCf; omega, h1, h3, by linarith⟩

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

omit he in
lemma κ1_ge : 16 ≤ H.κ1 := by
  have := H.Lam1_pos; have : (0 : ℝ) ≤ max 1 (cK d) := le_trans zero_le_one (le_max_left _ _)
  unfold κ1; nlinarith

omit he in
lemma ε0_pos : 0 < H.ε0 := by have := H.κ1_ge; unfold ε0; positivity

end Sharp

end G26G


-- ===== Solutions.G26.WinSum =====

/-! ### Lemma G.26: the per-round failure bound and the weighted failure sum -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma sum_inv_sqrt_le (n : ℕ) :
    ∑ t ∈ Finset.range n, (Real.sqrt ((t : ℝ) + 1))⁻¹ ≤ 2 * Real.sqrt n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    set a := Real.sqrt (n : ℝ) with ha
    set b := Real.sqrt ((n : ℝ) + 1) with hb
    have ha2 : a ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
    have hb2 : b ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hb0 : 0 < b := Real.sqrt_pos.2 (by positivity)
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have hstep : b⁻¹ ≤ 2 * (b - a) := by
      rw [inv_le_iff_one_le_mul₀ hb0]
      nlinarith [sq_nonneg (a - b)]
    have : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [this]
    linarith

lemma sum_inv_sq_Ico {a : ℕ} (ha : 1 ≤ a) (b : ℕ) :
    ∑ t ∈ Finset.Ico a b, 1 / ((t : ℝ) + 1) ^ 2 ≤ 1 / (a : ℝ) := by
  have key : ∀ b, a ≤ b → ∑ t ∈ Finset.Ico a b, 1 / ((t : ℝ) + 1) ^ 2 ≤ 1 / (a : ℝ) - 1 / (b : ℝ) := by
    intro b hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      rw [Finset.sum_Ico_succ_top hab]
      have hb : (1 : ℝ) ≤ b := by exact_mod_cast ha.trans hab
      have h1 : 1 / ((b : ℝ) + 1) ^ 2 ≤ 1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      linarith
  rcases le_total a b with h | h
  · have := key b h
    have : (0 : ℝ) ≤ 1 / (b : ℝ) := by positivity
    linarith
  · rw [Finset.Ico_eq_empty_of_le h, Finset.sum_empty]; positivity

/-- `√H ≤ 5 + 6 √C log(e + C)` -/
lemma sqrt_Hc_le {C : ℝ} (hC : 0 ≤ C) :
    Real.sqrt (Hcf C) ≤ 5 + 6 * (Real.sqrt C * Real.log (Real.exp 1 + C)) := by
  obtain ⟨hn1, hCn, hnH, hH1⟩ := Hcf_facts hC
  set L := Real.log (Real.exp 1 + C) with hL
  have he1 := Real.add_one_le_exp (1 : ℝ)
  have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hL1 : 1 ≤ L := by
    have := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ Real.exp 1 + C by linarith)
    rw [Real.log_exp] at this; exact this
  have hn : (nCf C : ℝ) ≤ C + 2 := by
    unfold nCf; push_cast; linarith [Nat.ceil_lt_add_one hC]
  -- `log(e(n+1)) ≤ 4 L`
  have hlog : Real.log (Real.exp 1 * ((nCf C : ℝ) + 1)) ≤ 4 * L := by
    have h1 : Real.exp 1 * ((nCf C : ℝ) + 1) ≤ (Real.exp 1 + C) ^ 4 := by
      have h2 : ((nCf C : ℝ) + 1) ≤ 3 * (Real.exp 1 + C) := by linarith
      have h3 : Real.exp 1 * (3 * (Real.exp 1 + C)) ≤ (Real.exp 1 + C) ^ 4 := by
        have he27 := Real.exp_one_gt_d9
        set u := Real.exp 1 + C with hu
        have h4 : 2.7 ≤ u := by rw [hu]; linarith
        have hu3 : 9 ≤ u ^ 3 := by
          have := pow_le_pow_left₀ (by norm_num) h4 3
          norm_num at this; linarith
        have h6 : Real.exp 1 * (3 * u) ≤ 9 * u := by nlinarith
        have h7 : 9 * u ≤ u ^ 3 * u := mul_le_mul_of_nonneg_right hu3 (by linarith)
        calc Real.exp 1 * (3 * u) ≤ 9 * u := h6
          _ ≤ u ^ 3 * u := h7
          _ = u ^ 4 := by ring
      calc Real.exp 1 * ((nCf C : ℝ) + 1) ≤ Real.exp 1 * (3 * (Real.exp 1 + C)) := by gcongr
        _ ≤ _ := h3
    calc Real.log (Real.exp 1 * ((nCf C : ℝ) + 1)) ≤ Real.log ((Real.exp 1 + C) ^ 4) :=
          Real.log_le_log (by positivity) h1
      _ = 4 * L := by rw [Real.log_pow]; push_cast; ring
  have hH : Hcf C ≤ 4 * C * L + 12 * L := by
    unfold Hcf
    have hlog0 : 0 ≤ Real.log (Real.exp 1 * ((nCf C : ℝ) + 1)) :=
      le_trans zero_le_one (log_e_ge (by linarith [(Nat.cast_nonneg (nCf C) : (0 : ℝ) ≤ _)]))
    calc ((nCf C : ℝ) + 1) * Real.log (Real.exp 1 * ((nCf C : ℝ) + 1)) ≤ (C + 3) * (4 * L) :=
          mul_le_mul (by linarith) hlog hlog0 (by linarith)
      _ = 4 * C * L + 12 * L := by ring
  have hsC := Real.sqrt_nonneg C
  have hsL : Real.sqrt L ≤ L := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  -- `√(4CL) ≤ 2 √C L`
  have h1 : Real.sqrt (4 * C * L) ≤ 2 * (Real.sqrt C * L) := by
    rw [show 4 * C * L = 2 ^ 2 * C * L by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    have := mul_le_mul_of_nonneg_left hsL (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hsC)
    linarith
  -- `√(12 L) ≤ 5 + 4 √C L`
  have h2 : Real.sqrt (12 * L) ≤ 5 + 4 * (Real.sqrt C * L) := by
    rcases le_total C 1 with hC1 | hC1
    · have hL2 : L ≤ 2 := by
        rw [hL, show (2 : ℝ) = Real.log (Real.exp 2) by rw [Real.log_exp]]
        refine Real.log_le_log (by positivity) ?_
        have := Real.add_one_le_exp (2 : ℝ)
        have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith
      have : Real.sqrt (12 * L) ≤ 5 := by
        rw [Real.sqrt_le_left (by norm_num)]; linarith
      have : 0 ≤ 4 * (Real.sqrt C * L) := by positivity
      linarith
    · have hsC1 : 1 ≤ Real.sqrt C := by rw [Real.le_sqrt (by norm_num) hC]; linarith
      have : Real.sqrt (12 * L) ≤ 4 * Real.sqrt L := by
        rw [Real.sqrt_mul (by norm_num)]
        have : Real.sqrt 12 ≤ 4 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
        exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
      have h3 : Real.sqrt L ≤ Real.sqrt C * L := by
        calc Real.sqrt L ≤ L := hsL
          _ = 1 * L := (one_mul L).symm
          _ ≤ Real.sqrt C * L := mul_le_mul_of_nonneg_right hsC1 (by linarith)
      linarith
  calc Real.sqrt (Hcf C) ≤ Real.sqrt (4 * C * L + 12 * L) := Real.sqrt_le_sqrt hH
    _ ≤ Real.sqrt (4 * C * L) + Real.sqrt (12 * L) := by
        rw [Real.sqrt_le_left (by positivity)]
        have := Real.sq_sqrt (show 0 ≤ 4 * C * L by positivity)
        have := Real.sq_sqrt (show 0 ≤ 12 * L by positivity)
        nlinarith [Real.sqrt_nonneg (4 * C * L), Real.sqrt_nonneg (12 * L)]
    _ ≤ 5 + 6 * (Real.sqrt C * L) := by linarith

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

lemma Dθ_nonneg : 0 ≤ H.Dθ he := by
  have := H.Dref_nonneg he; have := H.cX1_nonneg; have := H.cXB_nonneg; have := H.cCo_nonneg
  unfold Dθ; positivity

end Sharp

end G26G


-- ===== Solutions.G26.G26Final =====

/-! ### Lemma G.26: final assembly -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

/-- the constant of the weighted failure sum -/
noncomputable def Wθ : ℝ := 6 * (2 * Real.sqrt (H.Uw he + 1) + 2 * H.Dθ he)

set_option maxHeartbeats 4000000 in
/-- **Lemma G.26** in the interface form of `IAFTRL.lemma_G_26` -/
theorem main_G26 :
    ∃ W : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (T : ℕ) (C : ℝ) (R : GRun d Ω), 1 ≤ T → 0 ≤ C →
        IsGIAFTRLRun P 𝒜 ℬ e T R → IsCorruptedG P 𝒜 θ C T R →
        ∃ (G : ℕ → Set Ω) (L U : ℕ → Ω → ℝ),
          (∀ t, MeasurableSet (G t)) ∧ (∀ t, Measurable (L t)) ∧ (∀ t, Measurable (U t)) ∧
          (∀ t < T, ∀ ω ∈ G t, 1 ≤ L t ω ∧ 0 ≤ U t ω ∧ ∀ a ∈ Kset ℬ,
            4 * ((t + 1 : ℕ) : ℝ) ^ ((7 : ℝ) / 8) * ((a - astar) ⬝ᵥ θ) ≤
              (a - astar) ⬝ᵥ R.cumEst t ω ∧
            (a - astar) ⬝ᵥ θ ≤ L t ω * ((a - astar) ⬝ᵥ R.cumEst t ω / ((t : ℝ) + 1)) ∧
            (a - astar) ⬝ᵥ R.cumEst t ω / ((t : ℝ) + 1) ≤ U t ω * ((a - astar) ⬝ᵥ θ)) ∧
          (∀ t < T, ∀ ω ∉ G t, L t ω = 0 ∧ U t ω = 0) ∧
          (∀ t < T, ∀ r ∈ ({1, 3, 5} : Finset ℕ),
            Integrable (fun ω => L t ω ^ r * U t ω) P ∧
            ∫ ω, L t ω ^ r * U t ω ∂P ≤ 64 ^ (r + 1)) ∧
          ∑ t ∈ Finset.range T, (Real.sqrt ((t : ℝ) + 1))⁻¹ * (P (G t)ᶜ).toReal ≤
            W * (1 + Real.sqrt C * Real.log (Real.exp 1 + C)) := by
  classical
  refine ⟨H.Wθ he, ?_⟩
  intro Ω _ P _ T C R hT hC hR hcor
  set Hc := Hcf C with hHc
  set t0 := H.t0f he C with ht0
  let mt : ℕ → ℕ := fun t => mw (H.M0 he) Hc t
  let zt : ℕ → ℝ := fun t => zw (mt t) t
  let Gt : ℕ → Set Ω := fun t =>
    Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (zt t) T (mt t) t
  let G : ℕ → Set Ω := fun t => if t0 ≤ t ∧ t < T then Gt t else ∅
  let L : ℕ → Ω → ℝ := fun t => if t0 ≤ t ∧ t < T then Lt (Gt t) ℬ θ astar R t else 0
  let U : ℕ → Ω → ℝ := fun t => if t0 ≤ t ∧ t < T then Ut (Gt t) ℬ θ astar R t else 0
  have hwin : ∀ t, t0 ≤ t → _ := fun t ht => H.win_ok he hC (t := t) ht
  refine ⟨G, L, U, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    by_cases h : t0 ≤ t ∧ t < T
    · simp only [G, if_pos h]; exact H.Gev_meas he hR C (zt t) h.2.le
    · simp only [G, if_neg h]; exact MeasurableSet.empty
  · intro t
    by_cases h : t0 ≤ t ∧ t < T
    · simp only [L, if_pos h]
      exact (measurable_const.max (H.mf_meas hR h.2.le).inv).indicator
        (H.Gev_meas he hR C (zt t) h.2.le)
    · simp only [L, if_neg h]; exact measurable_const
  · intro t
    by_cases h : t0 ≤ t ∧ t < T
    · simp only [U, if_pos h]
      exact (H.Rf_meas hR h.2.le).indicator (H.Gev_meas he hR C (zt t) h.2.le)
    · simp only [U, if_neg h]; exact measurable_const
  · intro t htT ω hω
    by_cases h : t0 ≤ t ∧ t < T
    · simp only [G, if_pos h] at hω
      simp only [L, U, if_pos h]
      obtain ⟨hm, hmt, -, -, hlC, -, -, hz0, hmz, -⟩ := hwin t h.1
      have hlCτ : H.sig⁻¹ * C ≤ tauB (zt t) t := by
        have := (tauB_ge hz0.le t).2.1; linarith
      exact H.win_gaps he hz0.le hC hmt htT.le hlCτ hω
    · simp only [G, if_neg h] at hω; exact absurd hω (Set.notMem_empty ω)
  · intro t htT ω hω
    by_cases h : t0 ≤ t ∧ t < T
    · simp only [G, if_pos h] at hω
      simp [L, U, if_pos h, Lt, Ut, indicator_of_notMem hω]
    · simp only [L, U, if_neg h]; exact ⟨rfl, rfl⟩
  · intro t htT r hr
    have hr' : 1 ≤ r ∧ r ≤ 5 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl <;> norm_num
    by_cases h : t0 ≤ t ∧ t < T
    · simp only [L, U, if_pos h]
      obtain ⟨hm, hmt, hmhalf, hmc, hlC, -, -, hz0, hmz, hzt, hξ, -⟩ := hwin t h.1
      exact H.win_LU he hR hC hcor hz0.le hmt htT hmc hmhalf hlC hmz hzt hξ hr'.1 hr'.2
    · simp only [L, U, if_neg h]
      refine ⟨by simp, ?_⟩
      simp only [Pi.zero_apply, mul_zero, integral_zero]
      positivity
  · -- the weighted failure sum
    obtain ⟨hn1, hCn, hnH, hH1⟩ := Hcf_facts hC
    have hD := H.Dθ_nonneg he
    have hU0 : 256 ≤ H.Uw he := by
      unfold Uw
      have := H.ε0_pos
      have : 0 ≤ 4 * ((H.M0 he : ℝ) + 3) / H.ε0 := by positivity
      have : 0 ≤ 4 / H.ε0 ^ 2 := by positivity
      linarith
    have ht0le : (t0 : ℝ) ≤ H.Uw he * Hc + 1 := by
      have := Nat.ceil_lt_add_one (show 0 ≤ H.Uw he * Hc by positivity)
      rw [ht0]; unfold t0f; linarith
    have ht0ge : H.Uw he * Hc ≤ (t0 : ℝ) := by rw [ht0]; unfold t0f; exact Nat.le_ceil _
    have ht01 : 1 ≤ t0 := by
      have : (1 : ℝ) ≤ t0 := by nlinarith
      exact_mod_cast this
    set f : ℕ → ℝ := fun t => (Real.sqrt ((t : ℝ) + 1))⁻¹ * (P (G t)ᶜ).toReal with hf
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range T) (fun t => t < t0)]
    -- the initial rounds
    have hA : ∑ t ∈ (Finset.range T).filter (fun t => t < t0), f t ≤ 2 * Real.sqrt t0 := by
      refine le_trans ?_ (sum_inv_sqrt_le t0)
      refine le_trans (Finset.sum_le_sum fun t _ => ?_)
        (Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) fun t _ _ => ?_)
      · show (Real.sqrt ((t : ℝ) + 1))⁻¹ * (P (G t)ᶜ).toReal ≤ (Real.sqrt ((t : ℝ) + 1))⁻¹
        have : (P (G t)ᶜ).toReal ≤ 1 := by
          have := prob_le_one (μ := P) (s := (G t)ᶜ)
          exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
        have h0 : 0 ≤ (Real.sqrt ((t : ℝ) + 1))⁻¹ := by positivity
        nlinarith
      · simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢; exact ht.2
      · positivity
    -- the later rounds
    have hB : ∑ t ∈ (Finset.range T).filter (fun t => ¬ t < t0), f t ≤
        H.Dθ he * (1 + Hc ^ 2) * (Real.sqrt ((t0 : ℝ) + 1))⁻¹ * (1 / (t0 : ℝ)) := by
      have hset : (Finset.range T).filter (fun t => ¬ t < t0) = Finset.Ico t0 T := by
        ext t; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, not_lt]; tauto
      rw [hset]
      calc ∑ t ∈ Finset.Ico t0 T, f t
          ≤ ∑ t ∈ Finset.Ico t0 T, H.Dθ he * (1 + Hc ^ 2) * (Real.sqrt ((t0 : ℝ) + 1))⁻¹ *
              (1 / ((t : ℝ) + 1) ^ 2) := by
            refine Finset.sum_le_sum fun t ht => ?_
            rw [Finset.mem_Ico] at ht
            have h : t0 ≤ t ∧ t < T := ht
            have hround := H.win_round he hR hC hcor ht.2 ht.1
            have hGt : (P (G t)ᶜ).toReal = P.real (Gt t)ᶜ := by
              simp only [G, if_pos h]; rfl
            show (Real.sqrt ((t : ℝ) + 1))⁻¹ * (P (G t)ᶜ).toReal ≤ _
            rw [hGt]
            have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
            have hs : (Real.sqrt ((t : ℝ) + 1))⁻¹ ≤ (Real.sqrt ((t0 : ℝ) + 1))⁻¹ := by
              refine inv_anti₀ (Real.sqrt_pos.2 (by positivity)) (Real.sqrt_le_sqrt ?_)
              have : (t0 : ℝ) ≤ t := by exact_mod_cast ht.1
              linarith
            have hb : H.Dθ he * (1 / ((t : ℝ) + 1) ^ 2 + (Hc / ((t : ℝ) + 1)) ^ 2) =
                H.Dθ he * (1 + Hc ^ 2) * (1 / ((t : ℝ) + 1) ^ 2) := by
              rw [div_pow]; ring
            calc (Real.sqrt ((t : ℝ) + 1))⁻¹ * P.real (Gt t)ᶜ
                ≤ (Real.sqrt ((t0 : ℝ) + 1))⁻¹ *
                    (H.Dθ he * (1 + Hc ^ 2) * (1 / ((t : ℝ) + 1) ^ 2)) := by
                  rw [← hb]
                  exact mul_le_mul hs hround measureReal_nonneg (by positivity)
              _ = _ := by ring
        _ = H.Dθ he * (1 + Hc ^ 2) * (Real.sqrt ((t0 : ℝ) + 1))⁻¹ *
              ∑ t ∈ Finset.Ico t0 T, 1 / ((t : ℝ) + 1) ^ 2 := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (sum_inv_sq_Ico ht01 T) (by positivity)
    -- combine
    have hsqH := sqrt_Hc_le hC
    have hsH : 1 ≤ Real.sqrt Hc := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
    have hsHc : Real.sqrt Hc ^ 2 = Hc := Real.sq_sqrt (by linarith)
    have hA' : 2 * Real.sqrt t0 ≤ 2 * Real.sqrt (H.Uw he + 1) * Real.sqrt Hc := by
      rw [mul_assoc, ← Real.sqrt_mul (by linarith)]
      gcongr
      nlinarith
    have hB' : H.Dθ he * (1 + Hc ^ 2) * (Real.sqrt ((t0 : ℝ) + 1))⁻¹ * (1 / (t0 : ℝ)) ≤
        2 * H.Dθ he * Real.sqrt Hc := by
      have ht0H : Hc ≤ (t0 : ℝ) := by nlinarith
      have hsq : Real.sqrt Hc ≤ Real.sqrt ((t0 : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
      have hs0 : 0 < Real.sqrt Hc := by linarith
      have h1 : (1 + Hc ^ 2) * (Real.sqrt ((t0 : ℝ) + 1))⁻¹ * (1 / (t0 : ℝ)) ≤ 2 * Real.sqrt Hc := by
        rw [mul_assoc, one_div, ← mul_inv, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
        have h2 : Real.sqrt Hc * Hc ≤ Real.sqrt ((t0 : ℝ) + 1) * (t0 : ℝ) :=
          mul_le_mul hsq ht0H (by linarith) (Real.sqrt_nonneg _)
        have h3 : 1 + Hc ^ 2 ≤ 2 * Hc ^ 2 := by nlinarith
        calc 1 + Hc ^ 2 ≤ 2 * Hc ^ 2 := h3
          _ = 2 * Real.sqrt Hc * (Real.sqrt Hc * Hc) := by
              have hss : Real.sqrt Hc * Real.sqrt Hc = Hc := Real.mul_self_sqrt (by linarith)
              rw [show 2 * Real.sqrt Hc * (Real.sqrt Hc * Hc) =
                2 * (Real.sqrt Hc * Real.sqrt Hc) * Hc by ring, hss]; ring
          _ ≤ 2 * Real.sqrt Hc * (Real.sqrt ((t0 : ℝ) + 1) * (t0 : ℝ)) := by gcongr
      calc H.Dθ he * (1 + Hc ^ 2) * (Real.sqrt ((t0 : ℝ) + 1))⁻¹ * (1 / (t0 : ℝ))
          = H.Dθ he * ((1 + Hc ^ 2) * (Real.sqrt ((t0 : ℝ) + 1))⁻¹ * (1 / (t0 : ℝ))) := by ring
        _ ≤ H.Dθ he * (2 * Real.sqrt Hc) := mul_le_mul_of_nonneg_left h1 hD
        _ = 2 * H.Dθ he * Real.sqrt Hc := by ring
    have hX : 0 ≤ Real.sqrt C * Real.log (Real.exp 1 + C) := by
      have : 0 ≤ Real.log (Real.exp 1 + C) :=
        Real.log_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)])
      positivity
    have hcoef : 0 ≤ 2 * Real.sqrt (H.Uw he + 1) + 2 * H.Dθ he := by positivity
    calc ∑ t ∈ (Finset.range T).filter (fun t => t < t0), f t +
          ∑ t ∈ (Finset.range T).filter (fun t => ¬ t < t0), f t
        ≤ (2 * Real.sqrt (H.Uw he + 1) + 2 * H.Dθ he) * Real.sqrt Hc := by linarith
      _ ≤ (2 * Real.sqrt (H.Uw he + 1) + 2 * H.Dθ he) *
            (5 + 6 * (Real.sqrt C * Real.log (Real.exp 1 + C))) :=
          mul_le_mul_of_nonneg_left hsqH hcoef
      _ ≤ H.Wθ he * (1 + Real.sqrt C * Real.log (Real.exp 1 + C)) := by
          unfold Wθ; nlinarith

end Sharp

end G26G

namespace IAFTRL

/-- **Lemma G.26** -/
theorem lemma_G_26_proved {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (hk : 1 ≤ kdim ℬ)
    (he : Function.Surjective e) (θ astar : Fin d → ℝ) (hθ : setNorm 𝒜 θ ≤ 1)
    (hastar : astar ∈ 𝒜) (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ)
    (hsharp : IsSharp 𝒜 θ astar) :
    ∃ W : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure P]
        (T : ℕ) (C : ℝ) (R : GRun d Ω), 1 ≤ T → 0 ≤ C →
        IsGIAFTRLRun P 𝒜 ℬ e T R → IsCorruptedG P 𝒜 θ C T R →
        ∃ (G : ℕ → Set Ω) (L U : ℕ → Ω → ℝ),
          (∀ t, MeasurableSet (G t)) ∧ (∀ t, Measurable (L t)) ∧ (∀ t, Measurable (U t)) ∧
          (∀ t < T, ∀ ω ∈ G t, 1 ≤ L t ω ∧ 0 ≤ U t ω ∧ ∀ a ∈ Kset ℬ,
            4 * ((t + 1 : ℕ) : ℝ) ^ ((7 : ℝ) / 8) * ((a - astar) ⬝ᵥ θ) ≤
              (a - astar) ⬝ᵥ R.cumEst t ω ∧
            (a - astar) ⬝ᵥ θ ≤ L t ω * ((a - astar) ⬝ᵥ R.cumEst t ω / ((t : ℝ) + 1)) ∧
            (a - astar) ⬝ᵥ R.cumEst t ω / ((t : ℝ) + 1) ≤ U t ω * ((a - astar) ⬝ᵥ θ)) ∧
          (∀ t < T, ∀ ω ∉ G t, L t ω = 0 ∧ U t ω = 0) ∧
          (∀ t < T, ∀ r ∈ ({1, 3, 5} : Finset ℕ),
            MeasureTheory.Integrable (fun ω => L t ω ^ r * U t ω) P ∧
            ∫ ω, L t ω ^ r * U t ω ∂P ≤ 64 ^ (r + 1)) ∧
          ∑ t ∈ Finset.range T, (Real.sqrt ((t : ℝ) + 1))⁻¹ * (P (G t)ᶜ).toReal ≤
            W * (1 + Real.sqrt C * Real.log (Real.exp 1 + C)) :=
  G26G.Sharp.main_G26 ⟨hd, h𝒜, hℬ, hgen, hball, hspan, hk, hθ, hastar, huniq, hsharp⟩ he

end IAFTRL


theorem _root_.solution : type_of% @IAFTRL.lemma_G_26_proved := @IAFTRL.lemma_G_26_proved
