-- Prove2me | solution 1 for IAFTRL.lemma_G_1
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-17T14:39:53.346954+00:00
-- url     : https://prove2.me/submissions/87a33dcf-7812-4ee6-88c3-5e943652302b

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_chi
import Definitions.Def_IAFTRL_GTerms
import Theorems.Thm_IAFTRL_lemma_J_4
import Theorems.Thm_IAFTRL_lemma_G_12
import Theorems.Thm_IAFTRL_lemma_G_3
import Theorems.Thm_IAFTRL_lemma_G_26

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

-- ===== G2/Lex =====

/-! ### Lexicographic minimizers exist on compact sets -/

open Set IAFTRL

namespace G2L

variable {d : ℕ}

lemma lex_min_exists {M : Set (Fin d → ℝ)} (hM : IsCompact M) (hne : M.Nonempty) :
    ∃ b ∈ M, ∀ b' ∈ M, toLex b ≤ toLex b' := by
  have key : ∀ n : ℕ, ∃ b ∈ M, ∀ b' ∈ M, (∀ j : Fin d, j.val < n → b j = b' j) ∨
      ∃ i : Fin d, i.val < n ∧ (∀ j : Fin d, j < i → b j = b' j) ∧ b i < b' i := by
    intro n
    induction n with
    | zero =>
      obtain ⟨b, hb⟩ := hne
      exact ⟨b, hb, fun b' _ => Or.inl fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ n ih =>
      obtain ⟨b, hbM, hb⟩ := ih
      by_cases hnd : n < d
      · set M' := {b' ∈ M | ∀ j : Fin d, j.val < n → b' j = b j} with hM'
        have hM'c : IsCompact M' := by
          change IsCompact (M ∩ {b' : Fin d → ℝ | ∀ j : Fin d, j.val < n → b' j = b j})
          refine hM.inter_right ?_
          have : {b' : Fin d → ℝ | ∀ j : Fin d, j.val < n → b' j = b j} =
              ⋂ j : Fin d, ⋂ (_ : j.val < n), {b' | b' j = b j} := by
            ext b'; simp
          rw [this]
          exact isClosed_iInter fun j => isClosed_iInter fun _ =>
            isClosed_eq (continuous_apply j) continuous_const
        have hM'ne : M'.Nonempty := ⟨b, hbM, fun _ _ => rfl⟩
        obtain ⟨bs, ⟨hbsM, hbsb⟩, hmin⟩ :=
          hM'c.exists_isMinOn hM'ne (continuous_apply (⟨n, hnd⟩ : Fin d)).continuousOn
        refine ⟨bs, hbsM, fun b' hb'M => ?_⟩
        rcases hb b' hb'M with hA | ⟨i, hi, hpre, hlt⟩
        · have hb'M' : b' ∈ M' := ⟨hb'M, fun j hj => (hA j hj).symm⟩
          have hle : bs ⟨n, hnd⟩ ≤ b' ⟨n, hnd⟩ := hmin hb'M'
          rcases hle.lt_or_eq with hlt | heq
          · refine Or.inr ⟨⟨n, hnd⟩, Nat.lt_succ_self n, fun j hj => ?_, hlt⟩
            have hj' : j.val < n := hj
            rw [hbsb j hj', hA j hj']
          · refine Or.inl fun j hj => ?_
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
            · rw [hbsb j hj', hA j hj']
            · have : j = ⟨n, hnd⟩ := Fin.ext hj'
              rw [this, heq]
        · refine Or.inr ⟨i, Nat.lt_succ_of_lt hi, fun j hj => ?_, ?_⟩
          · have hj' : j.val < n := lt_trans hj hi
            rw [hbsb j hj', hpre j hj]
          · rw [hbsb i hi]; exact hlt
      · refine ⟨b, hbM, fun b' hb'M => ?_⟩
        rcases hb b' hb'M with hA | ⟨i, hi, hpre, hlt⟩
        · exact Or.inl fun j _ => hA j (lt_of_lt_of_le j.isLt (not_lt.1 hnd))
        · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hpre, hlt⟩
  obtain ⟨b, hbM, hb⟩ := key d
  refine ⟨b, hbM, fun b' hb'M => ?_⟩
  rcases hb b' hb'M with hA | ⟨i, -, hpre, hlt⟩
  · have : b = b' := funext fun j => hA j j.isLt
    rw [this]
  · exact le_of_lt ⟨i, hpre, hlt⟩

lemma lexMinimizer_mem {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) (hne : ℬ.Nonempty)
    (v : Fin d → ℝ) : lexMinimizer ℬ v ∈ ℬ := by
  have hc : Continuous fun x : Fin d → ℝ => x ⬝ᵥ v := by
    simp only [dotProduct]; fun_prop
  obtain ⟨b₀, hb₀, hmin⟩ := hℬ.exists_isMinOn hne hc.continuousOn
  set M := ℬ ∩ {b | b ⬝ᵥ v ≤ b₀ ⬝ᵥ v} with hM
  have hMc : IsCompact M := hℬ.inter_right (isClosed_le hc continuous_const)
  obtain ⟨b, ⟨hbℬ, hbv⟩, hlex⟩ := lex_min_exists hMc ⟨b₀, hb₀, show b₀ ⬝ᵥ v ≤ b₀ ⬝ᵥ v from le_refl _⟩
  have h : ∃ b ∈ ℬ, (∀ a ∈ ℬ, b ⬝ᵥ v ≤ a ⬝ᵥ v) ∧
      ∀ b' ∈ ℬ, (∀ a ∈ ℬ, b' ⬝ᵥ v ≤ a ⬝ᵥ v) → toLex b ≤ toLex b' :=
    ⟨b, hbℬ, fun a ha => le_trans hbv (hmin ha),
      fun b' hb' hb'min => hlex b' ⟨hb', hb'min b₀ hb₀⟩⟩
  unfold lexMinimizer
  rw [dif_pos h]
  exact (Classical.choose_spec h).1

lemma cand_mem {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) (hne : ℬ.Nonempty)
    (e : ℕ → Fin d → ℚ) (m : ℕ) : cand ℬ e m ∈ ℬ :=
  lexMinimizer_mem hℬ hne _

lemma gref_mem {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) (hne : ℬ.Nonempty)
    (e : ℕ → Fin d → ℚ) (t : ℕ) (S : Fin d → ℝ) : gref ℬ e t S ∈ ℬ :=
  cand_mem hℬ hne e _

end G2L

-- ===== G2/Ref =====

/-! ### The reference measure is a probability measure on `𝒦` -/

open MeasureTheory ProbabilityTheory Set IAFTRL
open scoped ENNReal

namespace G2F

variable {d : ℕ}

lemma Kc {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) : IsCompact (Kset ℬ) :=
  T31.isCompact_convexHull_of hℬ

lemma lamK_prob {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) (hne : ℬ.Nonempty) :
    IsProbabilityMeasure (lamK ℬ) := by
  obtain ⟨b, hb⟩ := hne
  obtain ⟨hpos, hfin⟩ := G11.hausdorff_pos_fin (T31.isCompact_convexHull_of hℬ)
    (convex_convexHull ℝ ℬ) ⟨b, subset_convexHull ℝ ℬ hb⟩
  exact cond_isProbabilityMeasure_of_finite hpos.ne' hfin.ne

lemma lamK_supp {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) : lamK ℬ (Kset ℬ)ᶜ = 0 := by
  unfold lamK
  rw [cond_apply (Kc hℬ).isClosed.measurableSet, Set.inter_compl_self,
    measure_empty, mul_zero]

lemma havg : Measurable fun v : Fin 16 → Fin d → ℝ => (16 : ℝ)⁻¹ • ∑ i, v i := by fun_prop

lemma mu16_prob {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) (hne : ℬ.Nonempty) :
    IsProbabilityMeasure (mu16 ℬ) := by
  haveI := lamK_prob hℬ hne
  exact Measure.isProbabilityMeasure_map havg.aemeasurable

lemma mu16_supp {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) (hne : ℬ.Nonempty) :
    mu16 ℬ (Kset ℬ)ᶜ = 0 := by
  haveI := lamK_prob hℬ hne
  have hKc := Kc hℬ
  have hconv : Convex ℝ (Kset ℬ) := convex_convexHull ℝ ℬ
  unfold mu16
  rw [Measure.map_apply havg hKc.isClosed.measurableSet.compl]
  refine measure_mono_null (t := ⋃ i : Fin 16, Function.eval i ⁻¹' (Kset ℬ)ᶜ) ?_ ?_
  · intro v hv
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_preimage, Function.eval, Set.mem_compl_iff, not_exists,
      not_not] at hcon
    apply hv
    show (16 : ℝ)⁻¹ • ∑ i, v i ∈ Kset ℬ
    rw [Finset.smul_sum]
    exact hconv.sum_mem (fun _ _ => by norm_num) (by simp) (fun i _ => hcon i)
  · exact measure_iUnion_null fun i => Measure.pi_eval_preimage_null _ (lamK_supp hℬ)

lemma muDisc_supp {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) (hne : ℬ.Nonempty)
    (e : ℕ → Fin d → ℚ) : muDisc ℬ e (Kset ℬ)ᶜ = 0 := by
  classical
  have hm := (Kc hℬ).isClosed.measurableSet.compl
  unfold muDisc
  rw [Measure.sum_apply _ hm]
  refine ENNReal.tsum_eq_zero.2 fun m => ?_
  split_ifs
  · rw [Measure.smul_apply, Measure.dirac_apply' _ hm, smul_eq_mul]
    have : cand ℬ e m ∉ (Kset ℬ)ᶜ := fun h =>
      h (subset_convexHull ℝ ℬ (G2L.cand_mem hℬ hne e m))
    simp [this]
  · simp

lemma refMu_prob {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) (hne : ℬ.Nonempty)
    (e : ℕ → Fin d → ℚ) : IsProbabilityMeasure (refMu ℬ e) := by
  haveI := mu16_prob hℬ hne
  obtain ⟨hω, hω1, hfin⟩ := G11.omega_gt ℬ e
  obtain ⟨hle, hlt⟩ := G11.muDisc_univ ℬ e
  refine ⟨?_⟩
  unfold refMu
  rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ (μ := mu16 ℬ), mul_one]
  unfold omegaMu
  have hx : (muDisc ℬ e univ).toReal ≤ 1 := by
    have := ENNReal.toReal_le_of_le_ofReal
      (div_pos (Real.exp_pos _) (by linarith [G11.exp_neg_one_lt])).le hle
    linarith
  rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one,
    ENNReal.ofReal_toReal hfin.ne]
  exact add_tsub_cancel_of_le (by
    rw [← ENNReal.ofReal_toReal hfin.ne, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hx)

lemma refMu_supp {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) (hne : ℬ.Nonempty)
    (e : ℕ → Fin d → ℚ) : refMu ℬ e (Kset ℬ)ᶜ = 0 := by
  unfold refMu
  rw [Measure.add_apply, Measure.smul_apply, muDisc_supp hℬ hne e, mu16_supp hℬ hne]
  simp

end G2F

-- ===== G2/Pot =====

/-! ### Exponential weights on a compactly supported reference: the potential argument -/

open MeasureTheory Set Real

namespace G2P

variable {d : ℕ}

/-- the barycenter of a measure -/
noncomputable def mean (ν : Measure (Fin d → ℝ)) : Fin d → ℝ := fun i => ∫ x, x i ∂ν

/-- the exponential-weights law `∝ e^{-xᵀS/β} μ(dx)` -/
noncomputable def gibbs (μ : Measure (Fin d → ℝ)) (β : ℝ) (S : Fin d → ℝ) :
    Measure (Fin d → ℝ) :=
  μ.tilted fun x => -(x ⬝ᵥ S) / β

/-- the potential `F_β(S) = -β log ∫ e^{-xᵀS/β} dμ` -/
noncomputable def Fpot (μ : Measure (Fin d → ℝ)) (β : ℝ) (S : Fin d → ℝ) : ℝ :=
  -β * Real.log (∫ x, Real.exp (-(x ⬝ᵥ S) / β) ∂μ)

lemma cont_dot (S : Fin d → ℝ) : Continuous fun x : Fin d → ℝ => x ⬝ᵥ S := by
  simp only [dotProduct]; fun_prop

section

variable {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ] {K : Set (Fin d → ℝ)}

lemma int_exp (hK : IsCompact K) (hμK : μ Kᶜ = 0) (β : ℝ) (S : Fin d → ℝ) :
    Integrable (fun x => Real.exp (-(x ⬝ᵥ S) / β)) μ :=
  T31.integrable_cpt hK hμK (((cont_dot S).neg.div_const β).rexp)

lemma Z_pos (hK : IsCompact K) (hμK : μ Kᶜ = 0) (β : ℝ) (S : Fin d → ℝ) :
    0 < ∫ x, Real.exp (-(x ⬝ᵥ S) / β) ∂μ :=
  integral_exp_pos (int_exp hK hμK β S)

lemma gibbs_prob (hK : IsCompact K) (hμK : μ Kᶜ = 0) (β : ℝ) (S : Fin d → ℝ) :
    IsProbabilityMeasure (gibbs μ β S) :=
  isProbabilityMeasure_tilted (int_exp hK hμK β S)

lemma gibbs_supp (hμK : μ Kᶜ = 0) (β : ℝ) (S : Fin d → ℝ) : gibbs μ β S Kᶜ = 0 :=
  tilted_absolutelyContinuous μ _ hμK

end

/-- the barycenter pairs linearly -/
lemma mean_dot {K : Set (Fin d → ℝ)} (hK : IsCompact K) {ν : Measure (Fin d → ℝ)}
    [IsFiniteMeasure ν] (hνK : ν Kᶜ = 0) (g : Fin d → ℝ) :
    mean ν ⬝ᵥ g = ∫ x, x ⬝ᵥ g ∂ν := by
  simp only [mean, dotProduct]
  rw [integral_finsetSum _ (fun i _ => T31.integrable_cpt hK hνK (by fun_prop))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_mul_const]

section

variable {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ] {K : Set (Fin d → ℝ)}
  (hK : IsCompact K) (hμK : μ Kᶜ = 0)
include hK hμK

/-- one step of the potential -/
lemma Fpot_step {β : ℝ} (hβ : 0 < β) (S g : Fin d → ℝ) :
    Fpot μ β (S + g) - Fpot μ β S = mean (gibbs μ β S) ⬝ᵥ g -
      β * Real.log (∫ x, Real.exp (-((x - mean (gibbs μ β S)) ⬝ᵥ g) / β) ∂(gibbs μ β S)) := by
  haveI := gibbs_prob hK hμK β S
  set q := gibbs μ β S
  set m := mean q
  have hZS := Z_pos hK hμK β S
  have hratio : ∫ x, Real.exp (-(x ⬝ᵥ (S + g)) / β) ∂μ =
      (∫ x, Real.exp (-(x ⬝ᵥ S) / β) ∂μ) * ∫ x, Real.exp (-(x ⬝ᵥ g) / β) ∂q := by
    have h := integral_exp_tilted (μ := μ) (fun x => -(x ⬝ᵥ S) / β) (fun x => -(x ⬝ᵥ g) / β)
    have hf : (fun x : Fin d → ℝ => Real.exp (((fun x => -(x ⬝ᵥ S) / β) +
        (fun x => -(x ⬝ᵥ g) / β)) x)) = fun x => Real.exp (-(x ⬝ᵥ (S + g)) / β) := by
      funext x; simp only [Pi.add_apply, dotProduct_add]; congr 1; ring
    rw [hf] at h
    change ∫ x, Real.exp (-(x ⬝ᵥ g) / β) ∂q = _ at h
    rw [h, mul_div_left_comm, div_self hZS.ne', mul_one]
  have hshift : ∫ x, Real.exp (-(x ⬝ᵥ g) / β) ∂q =
      Real.exp (-(m ⬝ᵥ g) / β) * ∫ x, Real.exp (-((x - m) ⬝ᵥ g) / β) ∂q := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [← Real.exp_add, sub_dotProduct]; congr 1; ring
  have hI : 0 < ∫ x, Real.exp (-((x - m) ⬝ᵥ g) / β) ∂q :=
    integral_exp_pos (T31.integrable_cpt hK (gibbs_supp hμK β S)
      ((((cont_dot g).comp (continuous_id.sub continuous_const)).neg.div_const β).rexp))
  unfold Fpot
  rw [hratio, hshift, Real.log_mul hZS.ne' (mul_pos (Real.exp_pos _) hI).ne',
    Real.log_mul (Real.exp_pos _).ne' hI.ne', Real.log_exp]
  field_simp
  ring

end


section

variable {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ] {K : Set (Fin d → ℝ)}
  (hK : IsCompact K) (hμK : μ Kᶜ = 0)
include hK hμK

/-- the Gibbs variational inequality (Donsker–Varadhan) -/
lemma Fpot_le_dv {β : ℝ} (hβ : 0 < β) (S : Fin d → ℝ) {q : Measure (Fin d → ℝ)}
    [IsProbabilityMeasure q] (hqK : q Kᶜ = 0) (hqμ : q ≪ μ) (hKL : Integrable (llr q μ) q) :
    Fpot μ β S ≤ mean q ⬝ᵥ S + β * ∫ x, llr q μ x ∂q := by
  set f : (Fin d → ℝ) → ℝ := fun x => -(x ⬝ᵥ S) / β with hf
  have hfμ : Integrable (fun x => Real.exp (f x)) μ := int_exp hK hμK β S
  have hfq : Integrable f q := T31.integrable_cpt hK hqK ((cont_dot S).neg.div_const β)
  have h1 := integral_llr_tilted_right hqμ hfq hfμ hKL
  haveI : IsProbabilityMeasure (μ.tilted f) := gibbs_prob hK hμK β S
  have hac : q ≪ μ.tilted f := hqμ.trans (absolutelyContinuous_tilted hfμ)
  have hint2 := integrable_llr_tilted_right hqμ hfq hKL hfμ
  have h2 := InformationTheory.integral_llr_add_sub_measure_univ_nonneg hac hint2
  simp only [probReal_univ, add_sub_cancel_right] at h2
  have hmean : ∫ x, f x ∂q = -(mean q ⬝ᵥ S) / β := by
    rw [mean_dot hK hqK, hf, integral_div, integral_neg]
  rw [h1, hmean] at h2
  unfold Fpot
  have hlog : -(mean q ⬝ᵥ S) / β - ∫ x, llr q μ x ∂q ≤
      Real.log (∫ x, Real.exp (-(x ⬝ᵥ S) / β) ∂μ) := by linarith
  have := mul_le_mul_of_nonneg_left hlog hβ.le
  rw [mul_sub, mul_div_cancel₀ _ hβ.ne'] at this
  linarith

lemma Fpot_zero (β : ℝ) : Fpot μ β 0 = 0 := by
  simp [Fpot]

lemma Fpot_mono {β β' : ℝ} (hβ : 0 < β) (hββ' : β ≤ β') (S : Fin d → ℝ) :
    Fpot μ β S ≤ Fpot μ β' S := by
  have hβ' : 0 < β' := lt_of_lt_of_le hβ hββ'
  set f' : (Fin d → ℝ) → ℝ := fun x => -(x ⬝ᵥ S) / β' with hf'
  have hfμ : Integrable (fun x => Real.exp (f' x)) μ := int_exp hK hμK β' S
  haveI : IsProbabilityMeasure (gibbs μ β' S) := gibbs_prob hK hμK β' S
  set q := gibbs μ β' S with hq
  have hqK : q Kᶜ = 0 := gibbs_supp hμK β' S
  have hqμ : q ≪ μ := tilted_absolutelyContinuous μ f'
  have hllr : llr q μ =ᵐ[q] fun x => f' x - Real.log (∫ x, Real.exp (f' x) ∂μ) :=
    hqμ.ae_le (log_rnDeriv_tilted_left_self hfμ)
  have hfq : Integrable f' q := T31.integrable_cpt hK hqK ((cont_dot S).neg.div_const β')
  have hKLi : Integrable (llr q μ) q := (hfq.sub (integrable_const _)).congr hllr.symm
  have hKLval : ∫ x, llr q μ x ∂q =
      -(mean q ⬝ᵥ S) / β' - Real.log (∫ x, Real.exp (-(x ⬝ᵥ S) / β') ∂μ) := by
    rw [integral_congr_ae hllr, integral_sub hfq (integrable_const _), integral_const,
      probReal_univ, one_smul, hf', integral_div, integral_neg, ← mean_dot hK hqK]
  have hKL0 : 0 ≤ ∫ x, llr q μ x ∂q := by
    have := Fpot_le_dv hK hμK hβ 0 hqK hqμ hKLi
    rw [Fpot_zero hK hμK, dotProduct_zero, zero_add] at this
    exact nonneg_of_mul_nonneg_right this hβ
  have h1 := Fpot_le_dv hK hμK hβ S hqK hqμ hKLi
  have heq : Fpot μ β' S = mean q ⬝ᵥ S + β' * ∫ x, llr q μ x ∂q := by
    rw [hKLval]; unfold Fpot; field_simp; ring
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_right hββ' hKL0]

/-- the centered log-moment is controlled by `χ` -/
lemma log_le_chi {β : ℝ} (hβ : 0 < β) {ν : Measure (Fin d → ℝ)} [IsProbabilityMeasure ν]
    (hνK : ν Kᶜ = 0) (g : Fin d → ℝ) :
    β * Real.log (∫ x, Real.exp (-((x - mean ν) ⬝ᵥ g) / β) ∂ν) ≤
      β * ∫ x, IAFTRL.chi (((x - mean ν) ⬝ᵥ g) / β) ∂ν := by
  obtain ⟨hJ1, -, -, -, hJ5, -⟩ := IAFTRL.lemma_J_4.{0}
  set h : (Fin d → ℝ) → ℝ := fun x => ((x - mean ν) ⬝ᵥ g) / β with hh
  have hhc : Continuous h :=
    ((cont_dot g).comp (continuous_id.sub continuous_const)).div_const β
  have hih : Integrable h ν := T31.integrable_cpt hK hνK hhc
  have hie : Integrable (fun x => Real.exp (-h x)) ν := T31.integrable_cpt hK hνK hhc.neg.rexp
  have hichi : Integrable (fun x => IAFTRL.chi (h x)) ν :=
    T31.integrable_cpt hK hνK (by unfold IAFTRL.chi; fun_prop)
  have hh0 : ∫ x, h x ∂ν = 0 := by
    have : ∫ x, (x - mean ν) ⬝ᵥ g ∂ν = 0 := by
      simp only [sub_dotProduct]
      rw [integral_sub (T31.integrable_cpt hK hνK (cont_dot g)) (integrable_const _),
        integral_const, probReal_univ, one_smul, ← mean_dot hK hνK, sub_self]
    rw [hh, integral_div, this, zero_div]
  have hI : 0 < ∫ x, Real.exp (-h x) ∂ν := integral_exp_pos hie
  have heq : (fun x => Real.exp (-((x - mean ν) ⬝ᵥ g) / β)) = fun x => Real.exp (-h x) := by
    funext x; rw [hh, neg_div]
  rw [heq]
  refine mul_le_mul_of_nonneg_left ?_ hβ.le
  calc Real.log (∫ x, Real.exp (-h x) ∂ν) ≤ (∫ x, Real.exp (-h x) ∂ν) - 1 :=
        Real.log_le_sub_one_of_pos hI
    _ = ∫ x, (Real.exp (-h x) - (-h x) - 1) ∂ν := by
        rw [integral_sub (f := fun x => Real.exp (-h x) - -h x) (g := fun _ => (1 : ℝ))
          (hie.sub hih.neg) (integrable_const _),
          integral_sub (f := fun x => Real.exp (-h x)) (g := fun x => -h x) hie hih.neg,
          integral_neg, hh0, integral_const, probReal_univ, one_smul]; ring
    _ ≤ ∫ x, IAFTRL.chi (h x) ∂ν := by
        refine integral_mono (hie.sub hih.neg |>.sub (integrable_const _)) hichi fun x => ?_
        have := hJ5 (-h x)
        rw [hJ1] at this
        exact this

end


section

variable {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ] {K : Set (Fin d → ℝ)}
  (hK : IsCompact K) (hμK : μ Kᶜ = 0)
include hK hμK

/-- **Telescoping (G.218)–(G.225).** -/
theorem telescope (β : ℕ → ℝ) (hβ : ∀ t, 0 < β t) (hmono : ∀ t, β t ≤ β (t + 1))
    (g : ℕ → Fin d → ℝ) {q : Measure (Fin d → ℝ)} [IsProbabilityMeasure q] (hqK : q Kᶜ = 0)
    (hqμ : q ≪ μ) (hKL : Integrable (llr q μ) q) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1),
        (mean (gibbs μ (β t) (∑ s ∈ Finset.range t, g s)) - mean q) ⬝ᵥ g t ≤
      ∑ t ∈ Finset.range (n + 1), β t * ∫ x, IAFTRL.chi
          (((x - mean (gibbs μ (β t) (∑ s ∈ Finset.range t, g s))) ⬝ᵥ g t) / β t)
          ∂(gibbs μ (β t) (∑ s ∈ Finset.range t, g s)) +
        β n * ∫ x, llr q μ x ∂q := by
  set S : ℕ → Fin d → ℝ := fun t => ∑ s ∈ Finset.range t, g s with hS
  have hSsucc : ∀ t, S (t + 1) = S t + g t := fun t => by simp [hS, Finset.sum_range_succ]
  -- the mixability gaps
  set D : ℕ → ℝ := fun t => β t * Real.log (∫ x, Real.exp
    (-((x - mean (gibbs μ (β t) (S t))) ⬝ᵥ g t) / β t) ∂(gibbs μ (β t) (S t))) with hD
  have hstep : ∀ t, mean (gibbs μ (β t) (S t)) ⬝ᵥ g t - D t =
      Fpot μ (β t) (S (t + 1)) - Fpot μ (β t) (S t) := fun t => by
    rw [hSsucc, Fpot_step hK hμK (hβ t)]
  have hclaim : ∀ n, ∑ t ∈ Finset.range (n + 1), (mean (gibbs μ (β t) (S t)) ⬝ᵥ g t - D t) ≤
      Fpot μ (β n) (S (n + 1)) := by
    intro n
    induction n with
    | zero =>
      simp only [zero_add, Finset.range_one, Finset.sum_singleton, hstep]
      have : S 0 = 0 := by simp [hS]
      rw [this, Fpot_zero hK hμK, sub_zero]
    | succ n ih =>
      rw [Finset.sum_range_succ, hstep]
      have := Fpot_mono hK hμK (hβ n) (hmono n) (S (n + 1))
      linarith
  have hdv := Fpot_le_dv hK hμK (hβ n) (S (n + 1)) hqK hqμ hKL
  have hsum : mean q ⬝ᵥ S (n + 1) = ∑ t ∈ Finset.range (n + 1), mean q ⬝ᵥ g t := by
    rw [hS]; simp only [dotProduct_sum]
  have hchi : ∀ t, D t ≤ β t * ∫ x, IAFTRL.chi
      (((x - mean (gibbs μ (β t) (S t))) ⬝ᵥ g t) / β t) ∂(gibbs μ (β t) (S t)) := by
    intro t
    haveI := gibbs_prob hK hμK (β t) (S t)
    exact log_le_chi hK hμK (hβ t) (gibbs_supp hμK (β t) (S t)) (g t)
  have h1 := hclaim n
  have h2 : ∑ t ∈ Finset.range (n + 1), D t ≤ ∑ t ∈ Finset.range (n + 1), β t * ∫ x,
      IAFTRL.chi (((x - mean (gibbs μ (β t) (S t))) ⬝ᵥ g t) / β t) ∂(gibbs μ (β t) (S t)) :=
    Finset.sum_le_sum fun t _ => hchi t
  simp only [Finset.sum_sub_distrib] at h1
  have h3 : ∑ t ∈ Finset.range (n + 1), (mean (gibbs μ (β t) (S t)) - mean q) ⬝ᵥ g t =
      ∑ t ∈ Finset.range (n + 1), mean (gibbs μ (β t) (S t)) ⬝ᵥ g t -
        ∑ t ∈ Finset.range (n + 1), mean q ⬝ᵥ g t := by
    rw [← Finset.sum_sub_distrib]; simp only [sub_dotProduct]
  rw [h3]
  linarith

end

end G2P

-- ===== G1/PotLoc =====

/-! ### The localized entropy telescope (Lemma J.2, (J.5)) -/

open MeasureTheory Set Real

namespace G2P

variable {d : ℕ}

section

variable {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ] {K : Set (Fin d → ℝ)}
  (hK : IsCompact K) (hμK : μ Kᶜ = 0)
include hK hμK

/-- the relative entropy of the Gibbs law is integrable, with the closed form -/
lemma gibbs_kl {β : ℝ} (S : Fin d → ℝ) :
    Integrable (llr (gibbs μ β S) μ) (gibbs μ β S) ∧
    ∫ x, llr (gibbs μ β S) μ x ∂(gibbs μ β S) =
      -(mean (gibbs μ β S) ⬝ᵥ S) / β - Real.log (∫ x, Real.exp (-(x ⬝ᵥ S) / β) ∂μ) := by
  set f : (Fin d → ℝ) → ℝ := fun x => -(x ⬝ᵥ S) / β with hf
  have hfμ : Integrable (fun x => Real.exp (f x)) μ := int_exp hK hμK β S
  haveI : IsProbabilityMeasure (gibbs μ β S) := gibbs_prob hK hμK β S
  set q := gibbs μ β S with hq
  have hqK : q Kᶜ = 0 := gibbs_supp hμK β S
  have hqμ : q ≪ μ := tilted_absolutelyContinuous μ f
  have hllr : llr q μ =ᵐ[q] fun x => f x - Real.log (∫ x, Real.exp (f x) ∂μ) :=
    hqμ.ae_le (log_rnDeriv_tilted_left_self hfμ)
  have hfq : Integrable f q := T31.integrable_cpt hK hqK ((cont_dot S).neg.div_const β)
  refine ⟨(hfq.sub (integrable_const _)).congr hllr.symm, ?_⟩
  rw [integral_congr_ae hllr, integral_sub hfq (integrable_const _), integral_const,
    probReal_univ, one_smul, hf, integral_div, integral_neg, ← mean_dot hK hqK]

/-- the Gibbs identity `F_β(S) = ⟨q, S⟩ + β D_KL(q, μ)` -/
lemma Fpot_eq_gibbs {β : ℝ} (hβ : 0 < β) (S : Fin d → ℝ) :
    Fpot μ β S = mean (gibbs μ β S) ⬝ᵥ S + β * ∫ x, llr (gibbs μ β S) μ x ∂(gibbs μ β S) := by
  rw [(gibbs_kl hK hμK S).2]; unfold Fpot; field_simp; ring

/-- an atom bounds the potential: `F_β(S) ≤ aᵀS + β log(1/μ{a})` -/
lemma Fpot_le_atom {β : ℝ} (hβ : 0 < β) (S : Fin d → ℝ) {a : Fin d → ℝ} (ha : 0 < μ {a}) :
    Fpot μ β S ≤ a ⬝ᵥ S + β * Real.log (1 / (μ {a}).toReal) := by
  have hpos : 0 < (μ {a}).toReal := ENNReal.toReal_pos ha.ne' (measure_ne_top _ _)
  have hint := int_exp hK hμK β S
  have hge : (μ {a}).toReal * Real.exp (-(a ⬝ᵥ S) / β) ≤
      ∫ x, Real.exp (-(x ⬝ᵥ S) / β) ∂μ := by
    have h1 := setIntegral_le_integral (s := {a}) hint (ae_of_all _ fun x => (Real.exp_pos _).le)
    rw [integral_singleton, smul_eq_mul, measureReal_def] at h1
    linarith
  have hlog := Real.log_le_log (mul_pos hpos (Real.exp_pos _)) hge
  rw [Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  unfold Fpot
  rw [one_div, Real.log_inv]
  have := mul_le_mul_of_nonneg_left hlog hβ.le
  rw [mul_add, mul_div_cancel₀ _ hβ.ne'] at this
  linarith

/-- **The localized telescope (J.5).** -/
theorem telescope_loc (β : ℕ → ℝ) (hβ : ∀ t, 0 < β t) (hmono : ∀ t, β t ≤ β (t + 1))
    (g : ℕ → Fin d → ℝ) {a : Fin d → ℝ} (ha : 0 < μ {a}) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1),
        (mean (gibbs μ (β t) (∑ s ∈ Finset.range t, g s)) - a) ⬝ᵥ g t ≤
      β 0 * Real.log (1 / (μ {a}).toReal) +
      ∑ t ∈ Finset.Ico 1 (n + 1), (β t - β (t - 1)) * (Real.log (1 / (μ {a}).toReal) -
        ∫ x, llr (gibbs μ (β t) (∑ s ∈ Finset.range t, g s)) μ x
          ∂(gibbs μ (β t) (∑ s ∈ Finset.range t, g s))) +
      ∑ t ∈ Finset.range (n + 1), (mean (gibbs μ (β t) (∑ s ∈ Finset.range t, g s)) ⬝ᵥ g t +
        β t * Real.log (∫ x, Real.exp (-(x ⬝ᵥ g t) / β t)
          ∂(gibbs μ (β t) (∑ s ∈ Finset.range t, g s)))) := by
  set S : ℕ → Fin d → ℝ := fun t => ∑ s ∈ Finset.range t, g s with hS
  set h := Real.log (1 / (μ {a}).toReal) with hh
  set KL : ℕ → ℝ := fun t => ∫ x, llr (gibbs μ (β t) (S t)) μ x ∂(gibbs μ (β t) (S t))
    with hKL
  set m : ℕ → Fin d → ℝ := fun t => mean (gibbs μ (β t) (S t)) with hm
  set D : ℕ → ℝ := fun t => m t ⬝ᵥ g t + β t * Real.log (∫ x, Real.exp (-(x ⬝ᵥ g t) / β t)
    ∂(gibbs μ (β t) (S t))) with hD
  have hSsucc : ∀ t, S (t + 1) = S t + g t := fun t => by simp [hS, Finset.sum_range_succ]
  -- the uncentered mixability gap equals the centered one
  have hDc : ∀ t, D t = β t * Real.log (∫ x, Real.exp (-((x - m t) ⬝ᵥ g t) / β t)
      ∂(gibbs μ (β t) (S t))) := by
    intro t
    haveI := gibbs_prob hK hμK (β t) (S t)
    have hβt := hβ t
    have hI : 0 < ∫ x, Real.exp (-((x - m t) ⬝ᵥ g t) / β t) ∂(gibbs μ (β t) (S t)) :=
      integral_exp_pos (T31.integrable_cpt hK (gibbs_supp hμK (β t) (S t))
        ((((cont_dot (g t)).comp (continuous_id.sub continuous_const)).neg.div_const _).rexp))
    have hshift : ∫ x, Real.exp (-(x ⬝ᵥ g t) / β t) ∂(gibbs μ (β t) (S t)) =
        Real.exp (-(m t ⬝ᵥ g t) / β t) *
          ∫ x, Real.exp (-((x - m t) ⬝ᵥ g t) / β t) ∂(gibbs μ (β t) (S t)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only
      rw [← Real.exp_add, sub_dotProduct]; congr 1; ring
    simp only [hD]
    rw [hshift, Real.log_mul (Real.exp_pos _).ne' hI.ne', Real.log_exp]
    field_simp
    ring
  -- one step
  have hstep : ∀ t, m t ⬝ᵥ g t - D t = Fpot μ (β t) (S (t + 1)) - Fpot μ (β t) (S t) := by
    intro t
    rw [hSsucc, Fpot_step hK hμK (hβ t), hDc t]
  -- the drift of the learning rate
  have hdrift : ∀ t, 1 ≤ t → Fpot μ (β (t - 1)) (S t) - Fpot μ (β t) (S t) ≤
      -(β t - β (t - 1)) * KL t := by
    intro t ht
    haveI := gibbs_prob hK hμK (β t) (S t)
    have hq := gibbs_kl hK hμK (β := β t) (S t)
    have h1 := Fpot_le_dv hK hμK (hβ (t - 1)) (S t) (gibbs_supp hμK (β t) (S t))
      (tilted_absolutelyContinuous μ _) hq.1
    have h2 := Fpot_eq_gibbs hK hμK (hβ t) (S t)
    simp only [hKL]
    nlinarith
  have hclaim : ∀ n, ∑ t ∈ Finset.range (n + 1), (m t ⬝ᵥ g t - D t) ≤
      Fpot μ (β n) (S (n + 1)) - ∑ t ∈ Finset.Ico 1 (n + 1), (β t - β (t - 1)) * KL t := by
    intro n
    induction n with
    | zero =>
      simp only [zero_add, Finset.range_one, Finset.sum_singleton, hstep, Finset.Ico_self,
        Finset.sum_empty, sub_zero]
      have : S 0 = 0 := by simp [hS]
      rw [this, Fpot_zero hK hμK, sub_zero]
    | succ n ih =>
      rw [Finset.sum_range_succ, hstep, Finset.sum_Ico_succ_top (by omega)]
      have := hdrift (n + 1) (by omega)
      simp only [Nat.add_sub_cancel] at this ⊢
      linarith
  have hfin := Fpot_le_atom hK hμK (hβ n) (S (n + 1)) ha
  have hsumS : a ⬝ᵥ S (n + 1) = ∑ t ∈ Finset.range (n + 1), a ⬝ᵥ g t := by
    simp only [hS, dotProduct_sum]
  -- `β_n h = β_0 h + Σ (β_t − β_{t−1}) h`
  have htele : β n * h = β 0 * h + ∑ t ∈ Finset.Ico 1 (n + 1), (β t - β (t - 1)) * h := by
    rw [← Finset.sum_mul]
    have : ∀ k, ∑ t ∈ Finset.Ico 1 (k + 1), (β t - β (t - 1)) = β k - β 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ihk =>
        rw [Finset.sum_Ico_succ_top (by omega), ihk]; simp
    rw [this]; ring
  have hc := hclaim n
  have h3 : ∑ t ∈ Finset.range (n + 1), (m t - a) ⬝ᵥ g t =
      ∑ t ∈ Finset.range (n + 1), (m t ⬝ᵥ g t - D t) + ∑ t ∈ Finset.range (n + 1), D t -
        ∑ t ∈ Finset.range (n + 1), a ⬝ᵥ g t := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by simp only [sub_dotProduct]; ring
  have h4 : ∑ t ∈ Finset.Ico 1 (n + 1), (β t - β (t - 1)) * (h - KL t) =
      ∑ t ∈ Finset.Ico 1 (n + 1), (β t - β (t - 1)) * h -
        ∑ t ∈ Finset.Ico 1 (n + 1), (β t - β (t - 1)) * KL t := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun t _ => by ring
  show ∑ t ∈ Finset.range (n + 1), (m t - a) ⬝ᵥ g t ≤ β 0 * h +
    ∑ t ∈ Finset.Ico 1 (n + 1), (β t - β (t - 1)) * (h - KL t) + ∑ t ∈ Finset.range (n + 1), D t
  rw [h3, h4]
  linarith

end


section

variable {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ] {K : Set (Fin d → ℝ)}
  (hK : IsCompact K) (hμK : μ Kᶜ = 0)
include hK hμK

/-- the mixability gap in centered form, and its two-sided bound -/
lemma mixGap_bounds {β : ℝ} (hβ : 0 < β) (S g : Fin d → ℝ) {c : ℝ}
    (hc : ∀ x ∈ K, |(x - mean (gibbs μ β S)) ⬝ᵥ g| ≤ c) :
    0 ≤ mean (gibbs μ β S) ⬝ᵥ g + β * Real.log (∫ x, Real.exp (-(x ⬝ᵥ g) / β) ∂(gibbs μ β S)) ∧
    mean (gibbs μ β S) ⬝ᵥ g + β * Real.log (∫ x, Real.exp (-(x ⬝ᵥ g) / β) ∂(gibbs μ β S)) ≤
      β * IAFTRL.chi (c / β) := by
  obtain ⟨hJ1, -, -, hJmono, -⟩ := IAFTRL.lemma_J_4.{0}
  haveI := gibbs_prob hK hμK β S
  set q := gibbs μ β S with hq
  have hqK : q Kᶜ = 0 := gibbs_supp hμK β S
  set m := mean q with hm
  have hcont : Continuous fun x : Fin d → ℝ => ((x - m) ⬝ᵥ g) / β :=
    ((cont_dot g).comp (continuous_id.sub continuous_const)).div_const β
  have hie : Integrable (fun x => Real.exp (-(((x - m) ⬝ᵥ g) / β))) q :=
    T31.integrable_cpt hK hqK hcont.neg.rexp
  have hih : Integrable (fun x => ((x - m) ⬝ᵥ g) / β) q := T31.integrable_cpt hK hqK hcont
  have hh0 : ∫ x, ((x - m) ⬝ᵥ g) / β ∂q = 0 := by
    rw [integral_div]
    simp only [sub_dotProduct]
    rw [integral_sub (T31.integrable_cpt hK hqK (cont_dot g)) (integrable_const _),
      integral_const, probReal_univ, one_smul, ← mean_dot hK hqK, sub_self, zero_div]
  have hI : 0 < ∫ x, Real.exp (-(((x - m) ⬝ᵥ g) / β)) ∂q := integral_exp_pos hie
  have hshift : ∫ x, Real.exp (-(x ⬝ᵥ g) / β) ∂q =
      Real.exp (-(m ⬝ᵥ g) / β) * ∫ x, Real.exp (-(((x - m) ⬝ᵥ g) / β)) ∂q := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [← Real.exp_add, sub_dotProduct]; congr 1; ring
  have heq : m ⬝ᵥ g + β * Real.log (∫ x, Real.exp (-(x ⬝ᵥ g) / β) ∂q) =
      β * Real.log (∫ x, Real.exp (-(((x - m) ⬝ᵥ g) / β)) ∂q) := by
    rw [hshift, Real.log_mul (Real.exp_pos _).ne' hI.ne', Real.log_exp]
    field_simp; ring
  rw [heq]
  constructor
  · refine mul_nonneg hβ.le (Real.log_nonneg ?_)
    have : ∫ x, (1 - ((x - m) ⬝ᵥ g) / β) ∂q ≤ ∫ x, Real.exp (-(((x - m) ⬝ᵥ g) / β)) ∂q :=
      integral_mono ((integrable_const 1).sub hih) hie fun x => by
        have := Real.add_one_le_exp (-(((x - m) ⬝ᵥ g) / β)); simp only; linarith
    rw [integral_sub (integrable_const 1) hih, hh0, integral_const, probReal_univ] at this
    simpa using this
  · have h1 := log_le_chi hK hμK hβ hqK g
    have heq2 : (fun x => Real.exp (-((x - mean q) ⬝ᵥ g) / β)) =
        fun x => Real.exp (-(((x - m) ⬝ᵥ g) / β)) := by
      funext x; rw [neg_div]
    rw [heq2] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hβ.le)
    calc ∫ x, IAFTRL.chi (((x - mean q) ⬝ᵥ g) / β) ∂q ≤ ∫ _, IAFTRL.chi (c / β) ∂q := by
          refine integral_mono_ae (T31.integrable_cpt hK hqK (by
              unfold IAFTRL.chi; exact (hcont.rexp.add hcont.neg.rexp).sub continuous_const))
            (integrable_const _) ?_
          filter_upwards [T31.ae_mem hqK] with x hx
          refine hJmono _ _ ?_
          rw [abs_div, abs_of_pos hβ]
          have hc0 : 0 ≤ c := le_trans (abs_nonneg _) (hc x hx)
          rw [abs_div, abs_of_pos hβ, abs_of_nonneg hc0]
          exact div_le_div_of_nonneg_right (hc x hx) hβ.le
      _ = IAFTRL.chi (c / β) := by simp

end

end G2P

-- ===== G1/Pen =====

/-! ### The penalty on good histories, (G.38)–(G.43) -/

open MeasureTheory Set Real

namespace G2P

variable {d : ℕ}

lemma one_add_mul_exp_le {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-y) * (1 + y) ≤ 2 * Real.exp (-y / 2) := by
  have h1 : Real.exp (-y) = Real.exp (-y / 2) * Real.exp (-y / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : 1 + y ≤ 2 * Real.exp (y / 2) := by linarith [Real.add_one_le_exp (y / 2)]
  have h3 : Real.exp (-y / 2) * Real.exp (y / 2) = 1 := by
    rw [← Real.exp_add, show -y / 2 + y / 2 = 0 by ring, Real.exp_zero]
  rw [h1]
  have h4 : 0 < Real.exp (-y / 2) := Real.exp_pos _
  calc Real.exp (-y / 2) * Real.exp (-y / 2) * (1 + y)
      ≤ Real.exp (-y / 2) * Real.exp (-y / 2) * (2 * Real.exp (y / 2)) := by gcongr
    _ = 2 * Real.exp (-y / 2) * (Real.exp (-y / 2) * Real.exp (y / 2)) := by ring
    _ = 2 * Real.exp (-y / 2) := by rw [h3, mul_one]

section

variable {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ] {K : Set (Fin d → ℝ)}
  (hK : IsCompact K) (hμK : μ Kᶜ = 0)
include hK hμK

/-- **Penalty on good histories** (G.38)–(G.43): if `(x − a)ᵀS ≥ 0` on `K` then
`h_a − D_KL(q, µ) ≤ (2/µ{a}) ∫_{x≠a} e^{−(x−a)ᵀS/(2β)} dµ` for the Gibbs law `q`. -/
theorem pen_good {β : ℝ} (hβ : 0 < β) (S : Fin d → ℝ) {a : Fin d → ℝ} (ha : 0 < μ {a})
    (hX : ∀ x ∈ K, 0 ≤ (x - a) ⬝ᵥ S) :
    Real.log (1 / (μ {a}).toReal) - ∫ x, llr (gibbs μ β S) μ x ∂(gibbs μ β S) ≤
      2 / (μ {a}).toReal * ∫ x in {a}ᶜ, Real.exp (-((x - a) ⬝ᵥ S) / (2 * β)) ∂μ := by
  set pa := (μ {a}).toReal with hpadef
  have hpa : 0 < pa := ENNReal.toReal_pos ha.ne' (measure_ne_top _ _)
  set c := a ⬝ᵥ S with hc
  set Z := ∫ x, Real.exp (-(x ⬝ᵥ S) / β) ∂μ with hZdef
  have hZ : 0 < Z := Z_pos hK hμK β S
  have hdc : Continuous fun x : Fin d → ℝ => (x - a) ⬝ᵥ S :=
    (cont_dot S).comp (continuous_id.sub continuous_const)
  have hE : Continuous fun x : Fin d → ℝ => Real.exp (-((x - a) ⬝ᵥ S) / β) :=
    (hdc.neg.div_const β).rexp
  have hEX : Continuous fun x : Fin d → ℝ =>
      Real.exp (-((x - a) ⬝ᵥ S) / β) * ((x - a) ⬝ᵥ S / β) :=
    hE.mul (hdc.div_const β)
  set Zs := ∫ x, Real.exp (-((x - a) ⬝ᵥ S) / β) ∂μ with hZsdef
  set J := ∫ x, Real.exp (-((x - a) ⬝ᵥ S) / β) * ((x - a) ⬝ᵥ S / β) ∂μ with hJdef
  have hexp : ∀ x : Fin d → ℝ, Real.exp (-(x ⬝ᵥ S) / β) =
      Real.exp (-c / β) * Real.exp (-((x - a) ⬝ᵥ S) / β) := by
    intro x; rw [← Real.exp_add]; congr 1; rw [hc, sub_dotProduct]; ring
  have hZs : Z = Real.exp (-c / β) * Zs := by
    rw [hZdef, hZsdef, ← integral_const_mul]; congr 1; funext x; exact hexp x
  have hZs0 : 0 < Zs := by
    have : 0 < Real.exp (-c / β) * Zs := hZs ▸ hZ
    exact pos_of_mul_pos_right this (Real.exp_pos _).le
  -- the mean
  haveI := gibbs_prob hK hμK β S
  have hmean : mean (gibbs μ β S) ⬝ᵥ S = c + β * J / Zs := by
    rw [mean_dot hK (gibbs_supp hμK β S) S, gibbs, integral_tilted]
    simp only [smul_eq_mul]
    have hsplit : ∀ x : Fin d → ℝ, Real.exp (-(x ⬝ᵥ S) / β) / Z * (x ⬝ᵥ S) =
        (Real.exp (-c / β) / Z) * (β * (Real.exp (-((x - a) ⬝ᵥ S) / β) * ((x - a) ⬝ᵥ S / β))) +
        (c / Z) * Real.exp (-(x ⬝ᵥ S) / β) := by
      intro x
      rw [hexp x]
      have : x ⬝ᵥ S = (x - a) ⬝ᵥ S + c := by rw [hc, sub_dotProduct]; ring
      rw [this]; field_simp
    rw [← hZdef]
    simp_rw [hsplit]
    rw [integral_add ((T31.integrable_cpt hK hμK hEX).const_mul β |>.const_mul _)
      ((int_exp hK hμK β S).const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul, ← hZdef, ← hJdef, hZs]
    field_simp
    ring
  -- the KL identity
  have hKL := (gibbs_kl hK hμK (β := β) S).2
  rw [hKL, hmean, ← hZdef, hZs, Real.log_mul (Real.exp_pos _).ne' hZs0.ne', Real.log_exp]
  -- split at the atom
  have hX0 : ∀ x, x = a → (x - a) ⬝ᵥ S = 0 := fun x h => by rw [h, sub_self, zero_dotProduct]
  have hZsplit : Zs = pa + ∫ x in {a}ᶜ, Real.exp (-((x - a) ⬝ᵥ S) / β) ∂μ := by
    rw [hZsdef, ← integral_add_compl (measurableSet_singleton a)
      (T31.integrable_cpt hK hμK hE), integral_singleton, hX0 a rfl]
    simp [measureReal_def, hpadef]
  have hJsplit : J = ∫ x in {a}ᶜ, Real.exp (-((x - a) ⬝ᵥ S) / β) * ((x - a) ⬝ᵥ S / β) ∂μ := by
    rw [hJdef, ← integral_add_compl (measurableSet_singleton a)
      (T31.integrable_cpt hK hμK hEX), integral_singleton, hX0 a rfl]
    simp
  set I := ∫ x in {a}ᶜ, Real.exp (-((x - a) ⬝ᵥ S) / β) ∂μ with hIdef
  set J' := ∫ x in {a}ᶜ, Real.exp (-((x - a) ⬝ᵥ S) / β) * ((x - a) ⬝ᵥ S / β) ∂μ with hJ'def
  have hrK : (μ.restrict {a}ᶜ) Kᶜ = 0 :=
    le_antisymm ((Measure.restrict_apply_le _ _).trans (le_of_eq hμK)) zero_le
  have hI0 : 0 ≤ I := integral_nonneg fun _ => (Real.exp_pos _).le
  have hJ0 : 0 ≤ J' := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [T31.ae_mem hrK] with x hx
    exact mul_nonneg (Real.exp_pos _).le (div_nonneg (hX x hx) hβ.le)
  -- the two estimates
  have hlog : Real.log Zs - Real.log pa ≤ I / pa := by
    rw [← Real.log_div hZs0.ne' hpa.ne', hZsplit]
    have := Real.log_le_sub_one_of_pos (show 0 < (pa + I) / pa by positivity)
    rw [add_div, div_self hpa.ne'] at this ⊢
    linarith
  have hJle : J / Zs ≤ J' / pa := by
    rw [hJsplit]
    exact div_le_div_of_nonneg_left hJ0 hpa (by rw [hZsplit]; linarith)
  have hfin : I + J' ≤ 2 * ∫ x in {a}ᶜ, Real.exp (-((x - a) ⬝ᵥ S) / (2 * β)) ∂μ := by
    rw [hIdef, hJ'def, ← integral_add (T31.integrable_cpt hK hrK hE)
      (T31.integrable_cpt hK hrK hEX), ← integral_const_mul]
    refine integral_mono_ae ((T31.integrable_cpt hK hrK hE).add
      (T31.integrable_cpt hK hrK hEX)) ((T31.integrable_cpt hK hrK
        ((hdc.neg.div_const _).rexp)).const_mul 2) ?_
    filter_upwards [T31.ae_mem hrK] with x hx
    have hy : 0 ≤ (x - a) ⬝ᵥ S / β := div_nonneg (hX x hx) hβ.le
    have h1 := one_add_mul_exp_le hy
    have h2 : -((x - a) ⬝ᵥ S) / β = -((x - a) ⬝ᵥ S / β) := by ring
    have h3 : -((x - a) ⬝ᵥ S) / (2 * β) = -((x - a) ⬝ᵥ S / β) / 2 := by ring
    rw [h2, h3]
    rw [mul_add, mul_one] at h1
    linarith
  have hpainv : Real.log (1 / pa) = -Real.log pa := by rw [one_div, Real.log_inv]
  rw [hpainv]
  have key : -Real.log pa - (-(c + β * J / Zs) / β - (-c / β + Real.log Zs)) =
      (Real.log Zs - Real.log pa) + J / Zs := by
    field_simp; ring
  rw [key]
  calc (Real.log Zs - Real.log pa) + J / Zs ≤ I / pa + J' / pa := add_le_add hlog hJle
    _ = (I + J') / pa := by ring
    _ ≤ (2 * ∫ x in {a}ᶜ, Real.exp (-((x - a) ⬝ᵥ S) / (2 * β)) ∂μ) / pa :=
        div_le_div_of_nonneg_right hfin hpa.le
    _ = _ := by ring

end

end G2P

-- ===== G1/G1Pen =====

/-! ### Lemma G.1: the relative-entropy penalty contribution -/

open MeasureTheory ProbabilityTheory Set IAFTRL

namespace G1P

variable {d : ℕ}

lemma atom_pos {ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {m : ℕ}
    (hm : m ∈ Jset ℬ e) {a : Fin d → ℝ} (ha : cand ℬ e m = a) : 0 < refMu ℬ e {a} := by
  classical
  have h1 : muDisc ℬ e {a} ≤ refMu ℬ e {a} := by
    unfold refMu; rw [Measure.add_apply]; exact le_self_add
  refine lt_of_lt_of_le ?_ h1
  unfold muDisc
  rw [Measure.sum_apply _ (measurableSet_singleton a)]
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum m)
  rw [if_pos hm, Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton a), ha]
  simp only [Set.indicator_of_mem (Set.mem_singleton a), Pi.one_apply, smul_eq_mul, mul_one]
  exact ENNReal.ofReal_pos.2 (Real.exp_pos _)

lemma int_le_of_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f g : Ω → ℝ}
    (hg : Integrable g P) (hg0 : ∀ ω, 0 ≤ g ω) (hfg : ∀ ω, f ω ≤ g ω) :
    ∫ ω, f ω ∂P ≤ ∫ ω, g ω ∂P := by
  by_cases hf : Integrable f P
  · exact integral_mono hf hg hfg
  · rw [integral_undef hf]; exact integral_nonneg hg0

lemma sum_inv_cube (T : ℕ) : ∑ t ∈ Finset.range T, (((t : ℝ) + 1) ^ 3)⁻¹ ≤ 2 := by
  have h : ∀ t ∈ Finset.range T, (((t : ℝ) + 1) ^ 3)⁻¹ ≤
      2 * ((((t : ℕ) : ℝ) + 1)⁻¹ - (((t + 1 : ℕ) : ℝ) + 1)⁻¹) := by
    intro t _
    push_cast
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have e1 : 2 * (((t : ℝ) + 1)⁻¹ - ((t : ℝ) + 1 + 1)⁻¹) = 2 / (((t : ℝ) + 1) * ((t : ℝ) + 2)) := by
      field_simp; ring
    rw [e1, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_nonneg ht 3, mul_nonneg ht ht]
  calc _ ≤ ∑ t ∈ Finset.range T, 2 * ((((t : ℕ) : ℝ) + 1)⁻¹ - (((t + 1 : ℕ) : ℝ) + 1)⁻¹) :=
        Finset.sum_le_sum h
    _ = 2 * ((((0 : ℕ) : ℝ) + 1)⁻¹ - (((T : ℕ) : ℝ) + 1)⁻¹) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub' (fun t : ℕ => (((t : ℕ) : ℝ) + 1)⁻¹)]
    _ ≤ 2 := by
        have : 0 ≤ (((T : ℕ) : ℝ) + 1)⁻¹ := by positivity
        simp only [Nat.cast_zero, zero_add, inv_one]
        linarith

lemma beta_diff (d t : ℕ) : 0 ≤ gbeta d (t + 1) - gbeta d t ∧
    gbeta d (t + 1) - gbeta d t ≤ (Real.sqrt ((t : ℝ) + 1))⁻¹ := by
  unfold gbeta
  push_cast
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have h1 : Real.sqrt t ≤ Real.sqrt (t + 1) := Real.sqrt_le_sqrt (by linarith)
  have hpos : 0 < Real.sqrt ((t : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have e1 : 16 * (d : ℝ) + Real.sqrt (t + 1) - (16 * d + Real.sqrt t) =
      Real.sqrt (t + 1) - Real.sqrt t := by ring
  rw [e1]
  refine ⟨by linarith, ?_⟩
  rw [← one_div, le_div_iff₀ hpos]
  have s1 := Real.sq_sqrt (show (0 : ℝ) ≤ t + 1 by positivity)
  have s2 := Real.sq_sqrt ht
  have s3 := Real.sqrt_nonneg (t : ℝ)
  nlinarith [mul_nonneg s3 (sub_nonneg.2 h1)]

/-- `Δ ≥ 0` on `𝒦` -/
lemma gap_nonneg {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IsGenerator 𝒜 ℬ) {θ astar : Fin d → ℝ}
    (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ) :
    ∀ x ∈ Kset ℬ, 0 ≤ (x - astar) ⬝ᵥ θ := by
  intro x hx
  have hconv : Convex ℝ {y : Fin d → ℝ | astar ⬝ᵥ θ ≤ y ⬝ᵥ θ} :=
    convex_halfSpace_ge ⟨fun y z => add_dotProduct y z θ, fun c y => smul_dotProduct c y θ⟩ _
  have hsub : ℬ ⊆ {y : Fin d → ℝ | astar ⬝ᵥ θ ≤ y ⬝ᵥ θ} := by
    intro b hb
    by_cases hba : b = astar
    · simp [hba]
    · exact (huniq b (hgen.1 hb) hba).le
  have := convexHull_min hsub hconv hx
  simp only [mem_setOf_eq] at this
  rw [sub_dotProduct]; linarith

section Main

variable {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}

theorem pen (hd : 1 ≤ d) (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (hk : 1 ≤ kdim ℬ)
    (he : Function.Surjective e) (θ astar : Fin d → ℝ) (hθ : setNorm 𝒜 θ ≤ 1)
    (hastar : astar ∈ 𝒜) (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ)
    (hsharp : IsSharp 𝒜 θ astar) :
    ∃ M J : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (T : ℕ) (C : ℝ) (R : GRun d Ω), 1 ≤ T → 0 ≤ C →
        IsGIAFTRLRun P 𝒜 ℬ e T R → IsCorruptedG P 𝒜 θ C T R →
        penI1 P ℬ e T R astar ≤ M + J * Real.sqrt C * Real.log (Real.exp 1 + C) := by
  obtain ⟨A, hA⟩ := lemma_G_3 hd 𝒜 ℬ e h𝒜 hℬ hgen hball hspan hk he θ astar hθ hastar huniq
    hsharp
  obtain ⟨W, hW⟩ := lemma_G_26 hd 𝒜 ℬ e h𝒜 hℬ hgen hball hspan hk he θ astar hθ hastar huniq
    hsharp
  obtain ⟨m, hm, hcand⟩ := lemma_G_12 𝒜 ℬ e h𝒜 hℬ hgen hball hspan he θ astar hastar huniq
    hsharp
  have hatom := atom_pos hm hcand
  have hBne : ℬ.Nonempty := convexHull_nonempty_iff.1 ⟨astar, hgen.2 hastar⟩
  haveI := G2F.refMu_prob hℬ hBne e
  have hμK := G2F.refMu_supp hℬ hBne e
  have hKc := G2F.Kc hℬ
  have hΔ0 := gap_nonneg hgen huniq
  set pa := (refMu ℬ e {astar}).toReal with hpadef
  have hpa : 0 < pa := ENNReal.toReal_pos hatom.ne' (measure_ne_top _ _)
  have hpa1 : pa ≤ 1 := by
    rw [hpadef, ← measureReal_def]; exact measureReal_le_one
  set h := hStar ℬ e astar with hhdef
  have hh0 : 0 ≤ h := by
    rw [hhdef, hStar]
    exact Real.log_nonneg (by rw [le_div_iff₀ hpa, one_mul]; exact hpa1)
  set A' := max A 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  refine ⟨gbeta d 1 * h + 4 * A' / pa + h * W, h * W, ?_⟩
  intro Ω _ P _ T C R hT hC hR hcor
  obtain ⟨G, L, U, hGm, -, -, hGood, -, -, hfail⟩ := hW P T C R hT hC hR hcor
  -- the per-round envelope
  have hround : ∀ t < T, ∫ ω, (h - klDivR (R.qw ℬ e t ω) (refMu ℬ e)) ∂P ≤
      2 * A' / pa * (((t : ℝ) + 1) ^ 3)⁻¹ + h * (P (G t)ᶜ).toReal := by
    intro t htT
    set c1 := 2 * A' / pa * (((t : ℝ) + 1) ^ 3)⁻¹ with hc1def
    have hc1 : 0 ≤ c1 := by positivity
    have hβ : 0 < gbeta d (t + 1) := by unfold gbeta; positivity
    have hi : Integrable ((G t)ᶜ.indicator (1 : Ω → ℝ)) P :=
      (integrable_const (1 : ℝ)).indicator (hGm t).compl
    have hg : Integrable (fun ω => c1 + h * (G t)ᶜ.indicator (1 : Ω → ℝ) ω) P :=
      (integrable_const _).add (hi.const_mul h)
    have hind : ∀ ω, 0 ≤ (G t)ᶜ.indicator (1 : Ω → ℝ) ω := fun ω =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    calc ∫ ω, (h - klDivR (R.qw ℬ e t ω) (refMu ℬ e)) ∂P
        ≤ ∫ ω, (c1 + h * (G t)ᶜ.indicator (1 : Ω → ℝ) ω) ∂P := by
          refine int_le_of_le hg (fun ω => add_nonneg hc1 (mul_nonneg hh0 (hind ω))) ?_
          intro ω
          set S := R.cumEst t ω with hS
          haveI := G2P.gibbs_prob hKc hμK (gbeta d (t + 1)) S
          have hKL : klDivR (R.qw ℬ e t ω) (refMu ℬ e) = ∫ x, llr (G2P.gibbs (refMu ℬ e)
              (gbeta d (t + 1)) S) (refMu ℬ e) x ∂(G2P.gibbs (refMu ℬ e) (gbeta d (t + 1)) S) :=
            rfl
          have hKL0 : 0 ≤ klDivR (R.qw ℬ e t ω) (refMu ℬ e) := by
            rw [hKL]
            have e3 := G2P.Fpot_le_dv hKc hμK hβ 0 (G2P.gibbs_supp hμK (gbeta d (t + 1)) S)
              (tilted_absolutelyContinuous _ _) (G2P.gibbs_kl hKc hμK S).1
            rw [G2P.Fpot_zero hKc hμK, dotProduct_zero, zero_add] at e3
            exact (mul_nonneg_iff_of_pos_left hβ).1 e3
          by_cases hω : ω ∈ G t
          · obtain ⟨-, -, hgap⟩ := hGood t htT ω hω
            have hX : ∀ x ∈ Kset ℬ, 0 ≤ (x - astar) ⬝ᵥ S := fun x hx =>
              le_trans (by have := hΔ0 x hx; positivity) (hgap x hx).1
            have hpg := G2P.pen_good hKc hμK hβ S hatom hX
            have hlap := hA (t + 1) S (by omega) (fun x hx => (hgap x hx).1)
            have hcast : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
            rw [hcast] at hlap
            have hlapA : ∫ x in {astar}ᶜ, Real.exp (-((x - astar) ⬝ᵥ S) / (2 * gbeta d (t + 1)))
                ∂(refMu ℬ e) ≤ A' * (((t : ℝ) + 1) ^ 3)⁻¹ := by
              rw [← div_eq_mul_inv]
              exact hlap.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
            have hfin : h - klDivR (R.qw ℬ e t ω) (refMu ℬ e) ≤ c1 := by
              rw [hKL, hhdef, hStar]
              refine hpg.trans ?_
              rw [hc1def, ← hpadef]
              calc 2 / pa * ∫ x in {astar}ᶜ, Real.exp (-((x - astar) ⬝ᵥ S) /
                    (2 * gbeta d (t + 1))) ∂(refMu ℬ e)
                  ≤ 2 / pa * (A' * (((t : ℝ) + 1) ^ 3)⁻¹) :=
                    mul_le_mul_of_nonneg_left hlapA (by positivity)
                _ = 2 * A' / pa * (((t : ℝ) + 1) ^ 3)⁻¹ := by ring
            have := mul_nonneg hh0 (hind ω)
            linarith
          · rw [Set.indicator_of_mem (show ω ∈ (G t)ᶜ from hω), Pi.one_apply, mul_one]
            linarith
      _ = c1 + h * (P (G t)ᶜ).toReal := by
          rw [integral_add (integrable_const _) (hi.const_mul h), integral_const,
            integral_const_mul, integral_indicator_one (hGm t).compl]
          simp [measureReal_def]
  -- summation
  have hsum1 : ∑ t ∈ Finset.Ico 1 T, (gbeta d (t + 1) - gbeta d t) *
      ∫ ω, (h - klDivR (R.qw ℬ e t ω) (refMu ℬ e)) ∂P ≤
      ∑ t ∈ Finset.range T, (Real.sqrt ((t : ℝ) + 1))⁻¹ *
        (2 * A' / pa * (((t : ℝ) + 1) ^ 3)⁻¹ + h * (P (G t)ᶜ).toReal) := by
    calc _ ≤ ∑ t ∈ Finset.Ico 1 T, (Real.sqrt ((t : ℝ) + 1))⁻¹ *
          (2 * A' / pa * (((t : ℝ) + 1) ^ 3)⁻¹ + h * (P (G t)ᶜ).toReal) := by
          refine Finset.sum_le_sum fun t ht => ?_
          have htT : t < T := (Finset.mem_Ico.1 ht).2
          obtain ⟨hb0, hb1⟩ := beta_diff d t
          have hnn : 0 ≤ 2 * A' / pa * (((t : ℝ) + 1) ^ 3)⁻¹ + h * (P (G t)ᶜ).toReal := by
            positivity
          calc _ ≤ (gbeta d (t + 1) - gbeta d t) *
                (2 * A' / pa * (((t : ℝ) + 1) ^ 3)⁻¹ + h * (P (G t)ᶜ).toReal) :=
                mul_le_mul_of_nonneg_left (hround t htT) hb0
            _ ≤ _ := mul_le_mul_of_nonneg_right hb1 hnn
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) (fun t _ _ => ?_)
          · exact Finset.mem_range.2 (Finset.mem_Ico.1 ht).2
          · positivity
  have hsq : ∀ t : ℕ, (Real.sqrt ((t : ℝ) + 1))⁻¹ ≤ 1 := fun t => by
    rw [inv_le_one₀ (Real.sqrt_pos.2 (by positivity))]
    exact Real.one_le_sqrt.2 (by have : (0 : ℝ) ≤ t := Nat.cast_nonneg t; linarith)
  have hsum2 : ∑ t ∈ Finset.range T, (Real.sqrt ((t : ℝ) + 1))⁻¹ *
      (2 * A' / pa * (((t : ℝ) + 1) ^ 3)⁻¹ + h * (P (G t)ᶜ).toReal) ≤
      4 * A' / pa + h * (W * (1 + Real.sqrt C * Real.log (Real.exp 1 + C))) := by
    simp only [mul_add, Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · calc ∑ t ∈ Finset.range T, (Real.sqrt ((t : ℝ) + 1))⁻¹ *
            (2 * A' / pa * (((t : ℝ) + 1) ^ 3)⁻¹)
          ≤ ∑ t ∈ Finset.range T, 2 * A' / pa * (((t : ℝ) + 1) ^ 3)⁻¹ := by
            refine Finset.sum_le_sum fun t _ => ?_
            have : 0 ≤ 2 * A' / pa * (((t : ℝ) + 1) ^ 3)⁻¹ := by positivity
            calc _ ≤ 1 * (2 * A' / pa * (((t : ℝ) + 1) ^ 3)⁻¹) :=
                  mul_le_mul_of_nonneg_right (hsq t) this
              _ = _ := one_mul _
        _ = 2 * A' / pa * ∑ t ∈ Finset.range T, (((t : ℝ) + 1) ^ 3)⁻¹ := by
            rw [Finset.mul_sum]
        _ ≤ 2 * A' / pa * 2 := mul_le_mul_of_nonneg_left (sum_inv_cube T) (by positivity)
        _ = 4 * A' / pa := by ring
    · calc ∑ t ∈ Finset.range T, (Real.sqrt ((t : ℝ) + 1))⁻¹ * (h * (P (G t)ᶜ).toReal)
          = h * ∑ t ∈ Finset.range T, (Real.sqrt ((t : ℝ) + 1))⁻¹ * (P (G t)ᶜ).toReal := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t _ => by ring
        _ ≤ h * (W * (1 + Real.sqrt C * Real.log (Real.exp 1 + C))) :=
            mul_le_mul_of_nonneg_left hfail hh0
        _ = _ := by ring
  unfold penI1
  rw [← hhdef]
  have : gbeta d 1 * h + (4 * A' / pa + h * (W * (1 + Real.sqrt C * Real.log (Real.exp 1 + C))))
      = gbeta d 1 * h + 4 * A' / pa + h * W + h * W * Real.sqrt C *
        Real.log (Real.exp 1 + C) := by ring
  linarith

end Main

end G1P

namespace IAFTRL

open MeasureTheory

theorem _root_.solution {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (hk : 1 ≤ kdim ℬ)
    (he : Function.Surjective e) (θ astar : Fin d → ℝ) (hθ : setNorm 𝒜 θ ≤ 1)
    (hastar : astar ∈ 𝒜) (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ)
    (hsharp : IsSharp 𝒜 θ astar) :
    ∃ M J : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (T : ℕ) (C : ℝ) (R : GRun d Ω), 1 ≤ T → 0 ≤ C →
        IsGIAFTRLRun P 𝒜 ℬ e T R → IsCorruptedG P 𝒜 θ C T R →
        penI1 P ℬ e T R astar ≤ M + J * Real.sqrt C * Real.log (Real.exp 1 + C) :=
  G1P.pen hd h𝒜 hℬ hgen hball hspan hk he θ astar hθ hastar huniq hsharp

end IAFTRL
