-- Prove2me | solution 1 for IAFTRL.lemma_G_11
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-17T12:10:26.382206+00:00
-- url     : https://prove2.me/submissions/1b40d1f1-6ef7-4974-a7ab-a2cbf1b57f54

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL

-- ===== T31/Geo =====

/-! ### General tools for the Theorem 3.1 leaves -/

open MeasureTheory Matrix Set

namespace T31

/-! #### Quadratic forms of positive definite matrices -/

/-- Cauchy–Schwarz for a positive definite matrix. -/
lemma cs_pd {r : ℕ} (H : Matrix (Fin r) (Fin r) ℝ) (hH : H.PosDef) (a w : Fin r → ℝ) :
    (a ⬝ᵥ w) ^ 2 ≤ (a ⬝ᵥ H⁻¹ *ᵥ a) * (w ⬝ᵥ H *ᵥ w) := by
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hT : Hᵀ = H := by
    have := hH.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  set v := H⁻¹ *ᵥ a with hv
  have hHv : H *ᵥ v = a := by rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
    Matrix.one_mulVec]
  have hsym : ∀ x y : Fin r → ℝ, x ⬝ᵥ H *ᵥ y = y ⬝ᵥ H *ᵥ x := by
    intro x y
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
  have haw : a ⬝ᵥ w = v ⬝ᵥ H *ᵥ w := by rw [← hHv, hsym, dotProduct_comm]
  have hav : a ⬝ᵥ v = v ⬝ᵥ H *ᵥ v := by rw [hHv, dotProduct_comm]
  rw [haw, hav]
  by_cases hw : w = 0
  · subst hw; simp
  have hww : 0 < w ⬝ᵥ H *ᵥ w := by
    have := hH.dotProduct_mulVec_pos hw
    rwa [star_trivial] at this
  set t := (v ⬝ᵥ H *ᵥ w) / (w ⬝ᵥ H *ᵥ w)
  have hpsd : 0 ≤ (v - t • w) ⬝ᵥ H *ᵥ (v - t • w) := by
    by_cases h0 : v - t • w = 0
    · rw [h0]; simp
    · have := hH.dotProduct_mulVec_pos h0
      rw [star_trivial] at this
      exact this.le
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul] at hpsd
  rw [hsym w v] at hpsd
  have ht : t * (w ⬝ᵥ H *ᵥ w) = v ⬝ᵥ H *ᵥ w := by
    simp only [t]; field_simp
  nlinarith [ht]

/-- A quadratic-form bound gives the inverse-form bound. -/
lemma inv_le_of_qf {r : ℕ} (H : Matrix (Fin r) (Fin r) ℝ) (hH : H.PosDef) (a : Fin r → ℝ)
    (κ : ℝ) (hκ : 0 ≤ κ) (hqf : ∀ w, (a ⬝ᵥ w) ^ 2 ≤ κ * (w ⬝ᵥ H *ᵥ w)) :
    a ⬝ᵥ H⁻¹ *ᵥ a ≤ κ := by
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  set v := H⁻¹ *ᵥ a with hv
  have hHv : H *ᵥ v = a := by rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
    Matrix.one_mulVec]
  have h := hqf v
  rw [hHv, dotProduct_comm v a] at h
  by_cases hp : a ⬝ᵥ v ≤ 0
  · linarith
  · have hp' : 0 < a ⬝ᵥ v := lt_of_not_ge hp
    nlinarith

/-- Vectors orthogonal to a spanning set vanish. -/
lemma eq_zero_of_orth {d : ℕ} {S : Set (Fin d → ℝ)} (hspan : Submodule.span ℝ S = ⊤)
    (w : Fin d → ℝ) (h : ∀ a ∈ S, a ⬝ᵥ w = 0) : w = 0 := by
  have : ∀ v ∈ Submodule.span ℝ S, v ⬝ᵥ w = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => simp
    | add x y _ _ hx hy => rw [add_dotProduct, hx, hy, add_zero]
    | smul t x _ hx => rw [smul_dotProduct, hx, smul_zero]
  have hw := this w (by rw [hspan]; trivial)
  exact dotProduct_self_eq_zero.mp hw

lemma posDef_of_qf {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.IsHermitian)
    (h : ∀ y : Fin d → ℝ, y ≠ 0 → 0 < y ⬝ᵥ H *ᵥ y) : H.PosDef :=
  Matrix.PosDef.of_dotProduct_mulVec_pos hH (fun x hx => by simpa using h x hx)

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

lemma ae_mem {n : Measure (Fin d → ℝ)} {𝒜 : Set (Fin d → ℝ)} (hn : n 𝒜ᶜ = 0) :
    ∀ᵐ a ∂n, a ∈ 𝒜 := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hn] with a ha
  simpa using ha

lemma integrable_cpt {F : Type*} [NormedAddCommGroup F] {n : Measure (Fin d → ℝ)}
    [IsFiniteMeasure n] {𝒜 : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) (hn : n 𝒜ᶜ = 0)
    {f : (Fin d → ℝ) → F} (hf : Continuous f) : Integrable f n := by
  obtain ⟨C, hC⟩ := h𝒜.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (by filter_upwards [ae_mem hn] with a ha using hC a ha)

lemma qf_designMat {n : Measure (Fin d → ℝ)} [IsFiniteMeasure n] {𝒜 : Set (Fin d → ℝ)}
    (h𝒜 : IsCompact 𝒜) (hn : n 𝒜ᶜ = 0) (y : Fin d → ℝ) :
    y ⬝ᵥ IAFTRL.designMat n *ᵥ y = ∫ a, (a ⬝ᵥ y) ^ 2 ∂n := by
  have hI : ∀ i j, Integrable (fun a : Fin d → ℝ => y i * y j * (a i * a j)) n := fun i j =>
    integrable_cpt h𝒜 hn (by fun_prop)
  have hfun : (fun a : Fin d → ℝ => (a ⬝ᵥ y) ^ 2) =
      fun a => ∑ i, ∑ j, y i * y j * (a i * a j) := by
    funext a
    simp only [dotProduct, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hfun, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hI i j))]
  simp only [dotProduct, mulVec, IAFTRL.designMat, of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => hI i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]; ring

lemma designMat_herm (n : Measure (Fin d → ℝ)) : (IAFTRL.designMat n).IsHermitian := by
  ext i j
  simp [IAFTRL.designMat, mul_comm]

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

lemma disc_compl {r : ι → ℝ} {x : ι → Fin d → ℝ} {S : Set (Fin d → ℝ)} (hS : IsClosed S)
    (hx : ∀ i, x i ∈ S) : disc r x Sᶜ = 0 := by
  simp only [disc, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hS.measurableSet.compl, smul_eq_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp [Set.indicator_of_notMem (show x i ∉ Sᶜ from fun h => h (hx i))]

lemma integral_disc {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) (x : ι → Fin d → ℝ)
    (f : (Fin d → ℝ) → ℝ) : ∫ a, f a ∂(disc r x) = ∑ i, r i * f (x i) := by
  rw [disc, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hr i), smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma designMat_disc {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) (x : ι → Fin d → ℝ) (k l : Fin d) :
    IAFTRL.designMat (disc r x) k l = ∑ i, r i * (x i k * x i l) := by
  simp only [IAFTRL.designMat, of_apply]
  exact integral_disc hr x _

lemma qf_disc {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) (x : ι → Fin d → ℝ) (y : Fin d → ℝ) :
    y ⬝ᵥ IAFTRL.designMat (disc r x) *ᵥ y = ∑ i, r i * (x i ⬝ᵥ y) ^ 2 := by
  have hS : IsCompact (Set.range x) := (Set.finite_range x).isCompact
  rw [qf_designMat hS (disc_compl hS.isClosed (fun i => ⟨i, rfl⟩)), integral_disc hr]

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

/-- sharpness controls the sup norm of the centered difference -/
lemma sharp_norm {𝒜 : Set (Fin d → ℝ)} (hne : 𝒜.Nonempty) (hspan : Submodule.span ℝ 𝒜 = ⊤)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) {θ astar : Fin d → ℝ} {ς : ℝ}
    (hς : ∀ a ∈ IAFTRL.Kset 𝒜, ς * IAFTRL.sNorm 𝒜 (a - astar) ≤ (a - astar) ⬝ᵥ θ) (hςpos : 0 < ς)
    {u : Fin d → ℝ} (hu : u ∈ convexHull ℝ 𝒜) : ς * ‖u - astar‖ ≤ (u - astar) ⬝ᵥ θ :=
  (mul_le_mul_of_nonneg_left (norm_le_sNorm hne hspan hball _) hςpos.le).trans (hς u hu)

end T31

-- ===== G2/Haus =====

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

-- ===== G2/KL =====

/-! ### Relative entropy of a dominated probability measure -/

open MeasureTheory Set
open scoped ENNReal

namespace G11

lemma abs_mul_log_le {C t : ℝ} (ht0 : 0 ≤ t) (htC : t ≤ C) : |t * Real.log t| ≤ 1 + C * C := by
  rcases le_or_gt t 1 with h1 | h1
  · rcases ht0.eq_or_lt with h0 | h0
    · subst h0; simp; positivity
    have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0 h1
    have hlow : 1 - t⁻¹ ≤ Real.log t := Real.one_sub_inv_le_log_of_pos h0
    have : t * (1 - t⁻¹) = t - 1 := by field_simp
    have hm : t - 1 ≤ t * Real.log t := by
      rw [← this]; exact mul_le_mul_of_nonneg_left hlow ht0
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg C]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos ht0 hlog, sq_nonneg C]
  · have hlog : 0 ≤ Real.log t := Real.log_nonneg h1.le
    have hup : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos (by linarith)
    rw [abs_of_nonneg (mul_nonneg ht0 hlog)]
    nlinarith

/-- A probability measure dominated by `C ν` has relative entropy at most `log C`. -/
theorem kl_of_le {X : Type*} [MeasurableSpace X] {q ν : Measure X} [IsProbabilityMeasure q]
    [IsFiniteMeasure ν] {C : ℝ} (hC : 0 < C) (hle : ∀ s, q s ≤ ENNReal.ofReal C * ν s) :
    q ≪ ν ∧ Integrable (fun x => Real.log (q.rnDeriv ν x).toReal) q ∧
      ∫ x, Real.log (q.rnDeriv ν x).toReal ∂q ≤ Real.log C := by
  have hac : q ≪ ν := fun s hs => nonpos_iff_eq_zero.1 ((hle s).trans (by simp [hs]))
  have hle' : q ≤ ENNReal.ofReal C • ν := Measure.le_iff'.2 fun s => by simpa using hle s
  have hCne : ENNReal.ofReal C ≠ 0 := by simp [hC]
  haveI : IsFiniteMeasure (ENNReal.ofReal C • ν) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν _)
  have h1' : q.rnDeriv (ENNReal.ofReal C • ν) ≤ᵐ[ENNReal.ofReal C • ν] 1 :=
    Measure.rnDeriv_le_one_of_le hle'
  have h1 : ∀ᵐ x ∂ν, q.rnDeriv (ENNReal.ofReal C • ν) x ≤ 1 :=
    (Measure.ae_ennreal_smul_measure_iff hCne).1 h1'
  have h2 := Measure.rnDeriv_smul_right_of_ne_top q ν hCne ENNReal.ofReal_ne_top
  have hbound : ∀ᵐ x ∂ν, q.rnDeriv ν x ≤ ENNReal.ofReal C := by
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx2] at hx1
    simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply] at hx1
    calc q.rnDeriv ν x = ENNReal.ofReal C * ((ENNReal.ofReal C)⁻¹ * q.rnDeriv ν x) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hCne ENNReal.ofReal_ne_top, one_mul]
      _ ≤ ENNReal.ofReal C * 1 := by gcongr
      _ = ENNReal.ofReal C := mul_one _
  have hboundR : ∀ᵐ x ∂ν, (q.rnDeriv ν x).toReal ≤ C := by
    filter_upwards [hbound] with x hx
    exact ENNReal.toReal_le_of_le_ofReal hC.le hx
  have hmeas : Measurable fun x => (q.rnDeriv ν x).toReal :=
    (Measure.measurable_rnDeriv q ν).ennreal_toReal
  -- integrability through the `x log x` form
  have hint : Integrable (fun x => Real.log (q.rnDeriv ν x).toReal) q := by
    refine (integrable_rnDeriv_mul_log_iff hac).1 ?_
    refine Integrable.of_bound (hmeas.mul (hmeas.log)).aestronglyMeasurable (1 + C * C) ?_
    filter_upwards [hboundR] with x hx
    rw [Real.norm_eq_abs]
    exact abs_mul_log_le ENNReal.toReal_nonneg hx
  refine ⟨hac, hint, ?_⟩
  have hpos := Measure.rnDeriv_pos hac
  have hboundq : ∀ᵐ x ∂q, q.rnDeriv ν x ≤ ENNReal.ofReal C := hac.ae_le hbound
  calc ∫ x, Real.log (q.rnDeriv ν x).toReal ∂q ≤ ∫ _, Real.log C ∂q := by
        refine integral_mono_ae hint (integrable_const _) ?_
        filter_upwards [hpos, hboundq] with x hx0 hxC
        have hne : q.rnDeriv ν x ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hxC
        exact Real.log_le_log (ENNReal.toReal_pos hx0.ne' hne)
          (ENNReal.toReal_le_of_le_ofReal hC.le hxC)
    _ = Real.log C := by simp

end G11

-- ===== G2/G11Main =====

/-! ### Lemma G.11 -/

open MeasureTheory Set ProbabilityTheory IAFTRL
open scoped ENNReal NNReal

namespace G11

variable {d : ℕ}

/-- `e^{-1} < 0.37` -/
lemma exp_neg_one_lt : Real.exp (-1) < 0.37 := by
  have he := Real.exp_one_gt_d9
  have hpos := Real.exp_pos (-1)
  have hmul : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
  nlinarith

/-- the discrete part of the reference measure has mass `< 1/4` -/
lemma muDisc_univ (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) :
    muDisc ℬ e univ ≤ ENNReal.ofReal (Real.exp (-2) / (1 - Real.exp (-1))) ∧
      Real.exp (-2) / (1 - Real.exp (-1)) < 1 / 4 := by
  classical
  set a := Real.exp (-1) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a < 0.37 := exp_neg_one_lt
  have hgeom : HasSum (fun m : ℕ => Real.exp (-2) * a ^ m) (Real.exp (-2) * (1 - a)⁻¹) :=
    (hasSum_geometric_of_lt_one ha0.le (by linarith)).mul_left _
  have hterm : ∀ m : ℕ, piW ℬ e m ≤ Real.exp (-2) * a ^ m := by
    intro m
    have hh : (m : ℝ) + 2 ≤ hPen ℬ e m := by
      unfold hPen
      have : 0 ≤ ∑ i ∈ (Finset.range m).filter (· ∈ Jset ℬ e),
          Real.exp ((sNorm ℬ (cand ℬ e m - cand ℬ e i))⁻¹ ^ 8) :=
        Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
      linarith
    unfold piW
    have : Real.exp (-2) * a ^ m = Real.exp (-((m : ℝ) + 2)) := by
      rw [ha, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
    rw [this]
    exact Real.exp_le_exp.2 (by linarith)
  constructor
  · unfold muDisc
    rw [Measure.sum_apply _ MeasurableSet.univ]
    calc ∑' m, (if m ∈ Jset ℬ e then ENNReal.ofReal (piW ℬ e m) • Measure.dirac (cand ℬ e m)
          else 0) univ
        ≤ ∑' m : ℕ, ENNReal.ofReal (Real.exp (-2) * a ^ m) := by
          refine ENNReal.tsum_le_tsum fun m => ?_
          split_ifs
          · simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
            exact ENNReal.ofReal_le_ofReal (hterm m)
          · simp
      _ = ENNReal.ofReal (∑' m : ℕ, Real.exp (-2) * a ^ m) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hgeom.summable).symm
      _ = ENNReal.ofReal (Real.exp (-2) / (1 - a)) := by
          rw [hgeom.tsum_eq, div_eq_mul_inv]
  · have he2 : Real.exp (-2) = a ^ 2 := by
      rw [ha, ← Real.exp_nat_mul]; norm_num
    rw [he2, div_lt_iff₀ (by linarith)]
    nlinarith

lemma omega_gt (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) :
    1 / 2 < omegaMu ℬ e ∧ omegaMu ℬ e ≤ 1 ∧ muDisc ℬ e univ < ∞ := by
  obtain ⟨h1, h2⟩ := muDisc_univ ℬ e
  have hfin : muDisc ℬ e univ < ∞ := lt_of_le_of_lt h1 ENNReal.ofReal_lt_top
  have hpos : 0 < Real.exp (-2) / (1 - Real.exp (-1)) := by
    have := exp_neg_one_lt
    exact div_pos (Real.exp_pos _) (by linarith)
  have hle : (muDisc ℬ e univ).toReal ≤ Real.exp (-2) / (1 - Real.exp (-1)) :=
    ENNReal.toReal_le_of_le_ofReal hpos.le h1
  refine ⟨?_, ?_, hfin⟩
  · unfold omegaMu; linarith
  · unfold omegaMu; linarith [ENNReal.toReal_nonneg (a := muDisc ℬ e univ)]

/-- the main construction of Lemma G.11 -/
theorem main {𝒜 ℬ : Set (Fin d → ℝ)} (e : ℕ → Fin d → ℚ) (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ)
    (hgen : IsGenerator 𝒜 ℬ) (u : Fin d → ℝ) (hu : u ∈ Kset ℬ) (T : ℕ) (hT : 1 ≤ T) :
    ∃ q : Measure (Fin d → ℝ), IsProbabilityMeasure q ∧ q (Kset ℬ)ᶜ = 0 ∧ q ≪ refMu ℬ e ∧
      Integrable (fun x => Real.log (q.rnDeriv (refMu ℬ e) x).toReal) q ∧
      ∫ x, Real.log (q.rnDeriv (refMu ℬ e) x).toReal ∂q ≤
        Real.log 2 + 16 * (kdim ℬ : ℝ) * Real.log T ∧
      ∀ ϑ : Fin d → ℝ, setNorm 𝒜 ϑ ≤ 1 →
        |((fun i => ∫ x, x i ∂q) - u) ⬝ᵥ ϑ| ≤ 2 / T := by
  set K := Kset ℬ with hKdef
  set k := kdim ℬ with hkdef
  have hKc : IsCompact K := T31.isCompact_convexHull_of hℬ
  have hKconv : Convex ℝ K := convex_convexHull ℝ ℬ
  obtain ⟨hHpos, hHfin⟩ := hausdorff_pos_fin hKc hKconv ⟨u, hu⟩
  have hk : (Module.finrank ℝ (vectorSpan ℝ K) : ℝ) = (k : ℝ) := rfl
  rw [hk] at hHpos hHfin
  -- `λ_𝒦` is a probability measure
  haveI hlam : IsProbabilityMeasure (lamK ℬ) :=
    cond_isProbabilityMeasure_of_finite hHpos.ne' hHfin.ne
  haveI : IsProbabilityMeasure (Measure.pi fun _ : Fin 16 => lamK ℬ) := inferInstance
  have havg : Measurable fun v : Fin 16 → Fin d → ℝ => (16 : ℝ)⁻¹ • ∑ i, v i := by fun_prop
  haveI h16 : IsProbabilityMeasure (mu16 ℬ) := Measure.isProbabilityMeasure_map havg.aemeasurable
  -- the shrunken copy `𝒦_ε`
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  set ε : ℝ := (T : ℝ)⁻¹ with hε
  have hε0 : 0 < ε := inv_pos.2 hT0
  have hε1 : ε ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hT)
  set Kε := AffineMap.homothety u ε '' K with hKε
  have hhom : ∀ x, AffineMap.homothety u ε x = ε • (x - u) + u := fun x => by
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  have hKεsub : Kε ⊆ K := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hhom]
    have := hKconv hu hx (by linarith : (0 : ℝ) ≤ 1 - ε) hε0.le (by ring)
    convert this using 1
    rw [smul_sub, sub_smul, one_smul]; abel
  have hKεc : IsCompact Kε := hKc.image (AffineMap.homothety u ε).continuous_of_finiteDimensional
  have hKεconv : Convex ℝ Kε := hKconv.affine_image _
  have hKεm : MeasurableSet Kε := hKεc.isClosed.measurableSet
  -- `λ_𝒦(𝒦_ε) = ε^k`
  set c : ℝ≥0∞ := ((‖ε‖₊ ^ (k : ℝ) : ℝ≥0) : ℝ≥0∞) with hc
  have hlamε : lamK ℬ Kε = c := by
    unfold lamK
    rw [cond_apply hKc.isClosed.measurableSet, Set.inter_eq_right.2 hKεsub, hKε,
      hausdorffMeasure_homothety_image (Nat.cast_nonneg _) u hε0.ne', ENNReal.smul_def,
      smul_eq_mul, ← mul_assoc, mul_comm _ (c : ℝ≥0∞), mul_assoc,
      ENNReal.inv_mul_cancel hHpos.ne' hHfin.ne, mul_one]
  have hcpos : c ≠ 0 := by
    rw [hc]; simp only [ne_eq, ENNReal.coe_eq_zero]
    exact (NNReal.rpow_pos (by simp [hε0.ne'])).ne'
  have hcval : c = ENNReal.ofReal (ε ^ k) := by
    rw [hc, ← ENNReal.ofReal_coe_nnreal]
    congr 1
    rw [NNReal.coe_rpow, coe_nnnorm, Real.norm_eq_abs, abs_of_pos hε0, Real.rpow_natCast]
  -- `μ_16(𝒦_ε) ≥ ε^{16k}`
  have hμε : c ^ 16 ≤ mu16 ℬ Kε := by
    unfold mu16
    rw [Measure.map_apply havg hKεm]
    calc c ^ 16 = (Measure.pi fun _ : Fin 16 => lamK ℬ) (Set.univ.pi fun _ => Kε) := by
          rw [Measure.pi_pi]; simp [hlamε]
      _ ≤ _ := by
          refine measure_mono fun v hv => ?_
          simp only [Set.mem_pi, Set.mem_univ, true_implies] at hv
          show (16 : ℝ)⁻¹ • ∑ i, v i ∈ Kε
          rw [Finset.smul_sum]
          exact hKεconv.sum_mem (fun _ _ => by norm_num) (by simp) (fun i _ => hv i)
  have hμεpos : mu16 ℬ Kε ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 (pow_ne_zero 16 hcpos)) hμε)
  -- the comparison law
  set q := (mu16 ℬ)[|Kε] with hq
  haveI hqP : IsProbabilityMeasure q := cond_isProbabilityMeasure hμεpos
  have hqKε : q Kεᶜ = 0 := by
    rw [hq, cond_apply hKεm, Set.inter_compl_self, measure_empty, mul_zero]
  obtain ⟨hω, hω1, hdfin⟩ := omega_gt ℬ e
  have hω0 : 0 < omegaMu ℬ e := by linarith
  haveI : IsFiniteMeasure (refMu ℬ e) := by
    refine ⟨?_⟩
    unfold refMu
    rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ (μ := mu16 ℬ), mul_one]
    exact ENNReal.add_lt_top.2 ⟨hdfin, ENNReal.ofReal_lt_top⟩
  -- domination `q ≤ (T^{16k}/ω) μ`
  set C : ℝ := (T : ℝ) ^ (16 * k) / omegaMu ℬ e with hCdef
  have hC0 : 0 < C := by positivity
  have hdom : ∀ s, q s ≤ ENNReal.ofReal C * refMu ℬ e s := by
    intro s
    have h1 : q s ≤ (c ^ 16)⁻¹ * mu16 ℬ s := by
      rw [hq, cond_apply hKεm]
      exact mul_le_mul' (ENNReal.inv_le_inv.2 hμε) (measure_mono Set.inter_subset_right)
    have h2 : ENNReal.ofReal (omegaMu ℬ e) * mu16 ℬ s ≤ refMu ℬ e s := by
      unfold refMu
      rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      exact le_add_self
    have hcinv : (c ^ 16)⁻¹ = ENNReal.ofReal ((T : ℝ) ^ (16 * k)) := by
      rw [hcval, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_inv_of_pos (by positivity)]
      congr 1
      rw [hε, ← pow_mul, inv_pow, inv_inv, mul_comm]
    calc q s ≤ (c ^ 16)⁻¹ * mu16 ℬ s := h1
      _ = ENNReal.ofReal C * (ENNReal.ofReal (omegaMu ℬ e) * mu16 ℬ s) := by
          rw [hcinv, ← mul_assoc, ← ENNReal.ofReal_mul hC0.le, hCdef,
            div_mul_cancel₀ _ hω0.ne']
      _ ≤ ENNReal.ofReal C * refMu ℬ e s := by gcongr
  obtain ⟨hac, hint, hKL⟩ := kl_of_le hC0 hdom
  refine ⟨q, hqP, measure_mono_null (Set.compl_subset_compl.2 hKεsub) hqKε, hac, hint, ?_, ?_⟩
  · refine hKL.trans ?_
    rw [hCdef, Real.log_div (by positivity) hω0.ne', Real.log_pow]
    have : -Real.log (omegaMu ℬ e) ≤ Real.log 2 := by
      rw [← Real.log_inv]
      exact Real.log_le_log (inv_pos.2 hω0) (by
        rw [inv_le_comm₀ hω0 (by norm_num)]; linarith)
    push_cast
    linarith
  · intro ϑ hϑ
    -- the mean lies in `𝒦_ε`
    have hint_id : Integrable (fun x : Fin d → ℝ => x) q :=
      T31.integrable_cpt hKεc hqKε continuous_id
    have hmean : ∫ x, x ∂q ∈ Kε :=
      hKεconv.integral_mem hKεc.isClosed (T31.ae_mem hqKε) hint_id
    have hfun : (fun i => ∫ x, x i ∂q) = ∫ x, x ∂q := by
      funext i
      rw [eval_integral (fun j => hint_id.eval j)]
    rw [hfun]
    obtain ⟨y, hy, hyeq⟩ := hmean
    rw [← hyeq, hhom, add_sub_cancel_right, smul_dotProduct, smul_eq_mul, sub_dotProduct]
    have hconv' : convexHull ℝ 𝒜 = K :=
      (convexHull_min hgen.2 (convex_convexHull ℝ ℬ)).antisymm (convexHull_mono hgen.1)
    have habs : ∀ x ∈ K, |x ⬝ᵥ ϑ| ≤ 1 := by
      intro x hx
      rw [← hconv'] at hx
      have hcont : Continuous fun a : Fin d → ℝ => |a ⬝ᵥ ϑ| := by
        simp only [dotProduct]; fun_prop
      have hcvx : Convex ℝ {x : Fin d → ℝ | |x ⬝ᵥ ϑ| ≤ setNorm 𝒜 ϑ} := by
        have hl : IsLinearMap ℝ (fun x : Fin d → ℝ => x ⬝ᵥ ϑ) :=
          ⟨fun x y => add_dotProduct x y ϑ, fun c x => smul_dotProduct c x ϑ⟩
        have : {x : Fin d → ℝ | |x ⬝ᵥ ϑ| ≤ setNorm 𝒜 ϑ} =
            {w | w ⬝ᵥ ϑ ≤ setNorm 𝒜 ϑ} ∩ {w | -setNorm 𝒜 ϑ ≤ w ⬝ᵥ ϑ} := by
          ext x; simp [abs_le, and_comm]
        rw [this]
        exact (convex_halfSpace_le hl _).inter (convex_halfSpace_ge hl _)
      have := convexHull_min (fun a ha => le_csSup (h𝒜.image hcont).bddAbove ⟨a, ha, rfl⟩)
        hcvx hx
      exact le_trans (show |x ⬝ᵥ ϑ| ≤ setNorm 𝒜 ϑ from this) hϑ
    have h1 := habs y hy
    have h2 := habs u hu
    rw [abs_mul, abs_of_pos hε0]
    calc ε * |y ⬝ᵥ ϑ - u ⬝ᵥ ϑ| ≤ ε * (|y ⬝ᵥ ϑ| + |u ⬝ᵥ ϑ|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) hε0.le
      _ ≤ ε * 2 := mul_le_mul_of_nonneg_left (by linarith) hε0.le
      _ = 2 / T := by rw [hε]; ring

end G11

-- ===== G2/G11Sol =====

namespace IAFTRL

open MeasureTheory

theorem _root_.solution {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (hk : 1 ≤ kdim ℬ)
    (u : Fin d → ℝ) (hu : u ∈ Kset ℬ) (T : ℕ) (hT : 1 ≤ T) :
    ∃ q : Measure (Fin d → ℝ), IsProbabilityMeasure q ∧ q (Kset ℬ)ᶜ = 0 ∧ q ≪ refMu ℬ e ∧
      Integrable (fun x => Real.log (q.rnDeriv (refMu ℬ e) x).toReal) q ∧
      ∫ x, Real.log (q.rnDeriv (refMu ℬ e) x).toReal ∂q ≤
        Real.log 2 + 16 * (kdim ℬ : ℝ) * Real.log T ∧
      ∀ ϑ : Fin d → ℝ, setNorm 𝒜 ϑ ≤ 1 →
        |((fun i => ∫ x, x i ∂q) - u) ⬝ᵥ ϑ| ≤ 2 / T :=
  G11.main e h𝒜 hℬ hgen u hu T hT

end IAFTRL
