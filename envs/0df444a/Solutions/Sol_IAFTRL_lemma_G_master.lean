-- Prove2me | solution 1 for IAFTRL.lemma_G_master
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-17T14:09:11.368866+00:00
-- url     : https://prove2.me/submissions/6bc934c5-a3b4-4d14-b6a0-01e9e3ffde79

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_chi
import Definitions.Def_IAFTRL_GTerms
import Theorems.Thm_IAFTRL_lemma_J_4

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

-- ===== G2/Meas =====

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

/-- measurability of the barycenter of the exponential weights in the cumulative loss -/
lemma measurable_Z (μ : Measure (Fin d → ℝ)) [SFinite μ] (β : ℝ) :
    Measurable fun S : Fin d → ℝ => ∫ x, Real.exp (-(x ⬝ᵥ S) / β) ∂μ := by
  have hc : Continuous fun p : (Fin d → ℝ) × (Fin d → ℝ) => Real.exp (-(p.2 ⬝ᵥ p.1) / β) := by
    simp only [dotProduct]; fun_prop
  exact hc.stronglyMeasurable.integral_prod_right'.measurable

lemma measurable_integral_gibbs (μ : Measure (Fin d → ℝ)) [SFinite μ] (β : ℝ)
    {f : (Fin d → ℝ) × (Fin d → ℝ) → ℝ} (hf : StronglyMeasurable f) :
    Measurable fun S : Fin d → ℝ => ∫ x, f (S, x) ∂(G2P.gibbs μ β S) := by
  have heq : (fun S : Fin d → ℝ => ∫ x, f (S, x) ∂(G2P.gibbs μ β S)) = fun S =>
      ∫ x, (Real.exp (-(x ⬝ᵥ S) / β) / ∫ y, Real.exp (-(y ⬝ᵥ S) / β) ∂μ) * f (S, x) ∂μ := by
    funext S
    rw [G2P.gibbs, integral_tilted]
    rfl
  rw [heq]
  have hZ := measurable_Z μ β
  have hc : Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) => Real.exp (-(p.2 ⬝ᵥ p.1) / β) := by
    have : Continuous fun p : (Fin d → ℝ) × (Fin d → ℝ) => Real.exp (-(p.2 ⬝ᵥ p.1) / β) := by
      simp only [dotProduct]; fun_prop
    exact this.measurable
  have hg : StronglyMeasurable fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      (Real.exp (-(p.2 ⬝ᵥ p.1) / β) / ∫ y, Real.exp (-(y ⬝ᵥ p.1) / β) ∂μ) * f p :=
    ((hc.div (hZ.comp measurable_fst)).stronglyMeasurable).mul hf
  exact hg.integral_prod_right'.measurable

lemma measurable_mean_gibbs (μ : Measure (Fin d → ℝ)) [SFinite μ] (β : ℝ) :
    Measurable fun S : Fin d → ℝ => G2P.mean (G2P.gibbs μ β S) := by
  refine measurable_pi_iff.2 fun i => ?_
  exact measurable_integral_gibbs μ β
    ((continuous_apply i).comp continuous_snd).stronglyMeasurable

end G2M

-- ===== G2/Law =====

/-! ### Joint law of a sub-σ-algebra measurable statistic and a conditionally distributed variable -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace G2W

variable {Ω : Type*} {G : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
  [IsProbabilityMeasure P] (hG : G ≤ mΩ)
  {𝒵 : Type*} [MeasurableSpace 𝒵] {Z : Ω → 𝒵} (hZ : Measurable[G] Z)
  {E : Type*} [MeasurableSpace E] {X : Ω → E} (hX : Measurable X)
  (κ : Kernel 𝒵 E) [IsMarkovKernel κ]
  (hlaw : ∀ s, MeasurableSet s →
    P[(X ⁻¹' s).indicator (fun _ => (1 : ℝ)) | G] =ᵐ[P] fun ω => (κ (Z ω) s).toReal)
include hG hZ hX hlaw

theorem law_eq : P.map (fun ω => (Z ω, X ω)) = (P.map Z) ⊗ₘ κ := by
  have hZm : Measurable Z := hZ.mono hG le_rfl
  have hpair : Measurable fun ω => (Z ω, X ω) := hZm.prodMk hX
  haveI : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZm.aemeasurable
  haveI : IsProbabilityMeasure (P.map fun ω => (Z ω, X ω)) :=
    Measure.isProbabilityMeasure_map hpair.aemeasurable
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ (by simp)
  rintro _ ⟨B, hB, s, hs, rfl⟩
  rw [Measure.map_apply hpair (hB.prod hs), Measure.compProd_apply_prod hB hs,
    setLIntegral_map hB (κ.measurable_coe hs) hZm]
  have hZB : MeasurableSet[G] (Z ⁻¹' B) := hZ hB
  have hpre : (fun ω => (Z ω, X ω)) ⁻¹' (B ×ˢ s) = Z ⁻¹' B ∩ X ⁻¹' s := by ext; simp
  rw [hpre]
  have hint : Integrable ((X ⁻¹' s).indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const 1).indicator (hX hs)
  have h1 := setIntegral_condExp hG hint hZB
  rw [setIntegral_congr_ae (hG _ hZB) (by filter_upwards [hlaw s hs] with ω hω _ using hω)] at h1
  -- both sides as real numbers
  have hL : ∫ ω in Z ⁻¹' B, (X ⁻¹' s).indicator (fun _ => (1 : ℝ)) ω ∂P =
      P.real (Z ⁻¹' B ∩ X ⁻¹' s) := by
    rw [integral_indicator (hX hs), Measure.restrict_restrict (hX hs), setIntegral_const,
      smul_eq_mul, mul_one, Set.inter_comm]
  have hR : ∫ ω in Z ⁻¹' B, (κ (Z ω) s).toReal ∂P =
      (∫⁻ ω in Z ⁻¹' B, κ (Z ω) s ∂P).toReal := by
    exact integral_toReal (f := fun ω => κ (Z ω) s) ((κ.measurable_coe hs).comp hZm).aemeasurable
      (ae_of_all _ fun ω => measure_lt_top _ _)
  rw [hL, hR] at h1
  have hfin : ∫⁻ ω in Z ⁻¹' B, κ (Z ω) s ∂P ≠ ∞ := by
    refine ne_top_of_le_ne_top (measure_ne_top (P.restrict (Z ⁻¹' B)) univ) ?_
    calc ∫⁻ ω in Z ⁻¹' B, κ (Z ω) s ∂P ≤ ∫⁻ _ in Z ⁻¹' B, 1 ∂P :=
          lintegral_mono fun ω => prob_le_one
      _ = (P.restrict (Z ⁻¹' B)) univ := by simp
  rw [measureReal_def] at h1
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hfin).1 h1.symm

theorem lintegral_law {F : 𝒵 × E → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (Z ω, X ω) ∂P = ∫⁻ ω, ∫⁻ x, F (Z ω, x) ∂(κ (Z ω)) ∂P := by
  have hZm : Measurable Z := hZ.mono hG le_rfl
  have hpair : Measurable fun ω => (Z ω, X ω) := hZm.prodMk hX
  rw [← lintegral_map hF hpair, law_eq P hG hZ hX κ hlaw, Measure.lintegral_compProd hF,
    lintegral_map (hF.lintegral_kernel_prod_right') hZm]

theorem integral_law {F : 𝒵 × E → ℝ} (hF : StronglyMeasurable F)
    (hFi : Integrable (fun ω => F (Z ω, X ω)) P) :
    ∫ ω, F (Z ω, X ω) ∂P = ∫ ω, ∫ x, F (Z ω, x) ∂(κ (Z ω)) ∂P := by
  have hZm : Measurable Z := hZ.mono hG le_rfl
  have hpair : Measurable fun ω => (Z ω, X ω) := hZm.prodMk hX
  have hlawe := law_eq P hG hZ hX κ hlaw
  have hFi' : Integrable F ((P.map Z) ⊗ₘ κ) := by
    rw [← hlawe]
    exact (integrable_map_measure hF.aestronglyMeasurable hpair.aemeasurable).2 hFi
  rw [← integral_map hpair.aemeasurable hF.aestronglyMeasurable, hlawe,
    Measure.integral_compProd hFi',
    integral_map hZm.aemeasurable (hF.integral_kernel_prod_right').aestronglyMeasurable]

end G2W

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

-- ===== G2/Run =====

/-! ### Basic facts about GIA-FTRL runs -/

open MeasureTheory ProbabilityTheory Set IAFTRL
open scoped ENNReal

namespace G2R

variable {d : ℕ}

/-! #### Geometry -/

lemma conv_eq {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IsGenerator 𝒜 ℬ) :
    convexHull ℝ 𝒜 = Kset ℬ :=
  (convexHull_min hgen.2 (convex_convexHull ℝ ℬ)).antisymm (convexHull_mono hgen.1)

lemma abs_dot_le_one {𝒜 ℬ : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) (hgen : IsGenerator 𝒜 ℬ)
    {θ : Fin d → ℝ} (hθ : setNorm 𝒜 θ ≤ 1) {x : Fin d → ℝ} (hx : x ∈ Kset ℬ) :
    |x ⬝ᵥ θ| ≤ 1 := by
  rw [← conv_eq hgen] at hx
  have hcont : Continuous fun a : Fin d → ℝ => |a ⬝ᵥ θ| := by
    simp only [dotProduct]; fun_prop
  have hcvx : Convex ℝ {x : Fin d → ℝ | |x ⬝ᵥ θ| ≤ setNorm 𝒜 θ} := by
    have hl : IsLinearMap ℝ (fun x : Fin d → ℝ => x ⬝ᵥ θ) :=
      ⟨fun x y => add_dotProduct x y θ, fun c x => smul_dotProduct c x θ⟩
    have : {x : Fin d → ℝ | |x ⬝ᵥ θ| ≤ setNorm 𝒜 θ} =
        {w | w ⬝ᵥ θ ≤ setNorm 𝒜 θ} ∩ {w | -setNorm 𝒜 θ ≤ w ⬝ᵥ θ} := by
      ext x; simp [abs_le, and_comm]
    rw [this]
    exact (convex_halfSpace_le hl _).inter (convex_halfSpace_ge hl _)
  have := convexHull_min (fun a ha => le_csSup (h𝒜.image hcont).bddAbove ⟨a, ha, rfl⟩) hcvx hx
  exact le_trans (show |x ⬝ᵥ θ| ≤ setNorm 𝒜 θ from this) hθ

lemma Kset_compact {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) : IsCompact (Kset ℬ) :=
  T31.isCompact_convexHull_of hℬ

lemma span_B {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) : Submodule.span ℝ ℬ = ⊤ := by
  rw [eq_top_iff, ← hspan]
  refine Submodule.span_le.2 fun a ha => ?_
  have : convexHull ℝ ℬ ⊆ Submodule.span ℝ ℬ :=
    convexHull_min Submodule.subset_span (Submodule.span ℝ ℬ).convex
  exact this (hgen.2 ha)

lemma B_nonempty {𝒜 ℬ : Set (Fin d → ℝ)} (hd : 1 ≤ d) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) : ℬ.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have := span_B hgen hspan
  rw [h, Submodule.span_empty] at this
  have hne : (Pi.single (⟨0, hd⟩ : Fin d) (1 : ℝ)) ∈ (⊤ : Submodule ℝ (Fin d → ℝ)) := trivial
  rw [← this, Submodule.mem_bot] at hne
  have := congrFun hne ⟨0, hd⟩
  simp at this

/-- the gauge of `𝒮` is at most `2` on differences of points of `𝒦` -/
lemma sNorm_sub_le {𝒜 ℬ : Set (Fin d → ℝ)} (hd : 1 ≤ d) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) {u w : Fin d → ℝ} (hu : u ∈ Kset ℬ) (hw : w ∈ Kset ℬ) :
    sNorm ℬ (u - w) ≤ 2 := by
  have hBne := B_nonempty hd hgen hspan
  have habs : Absorbent ℝ (Sset ℬ) := absorbent_nhds_zero (T31.Sset_nhds hBne (span_B hgen hspan))
  have hconv : Convex ℝ (Sset ℬ) := convex_convexHull ℝ _
  have hsub : Kset ℬ ⊆ Sset ℬ := convexHull_mono subset_union_left
  have hsymm : ∀ x ∈ Sset ℬ, -x ∈ Sset ℬ := by
    intro x hx
    have h' : -(ℬ ∪ -ℬ) = ℬ ∪ -ℬ := by
      ext y; simp only [Set.mem_neg, Set.mem_union, neg_neg]; tauto
    have : -x ∈ -convexHull ℝ (ℬ ∪ -ℬ) := by rw [Set.neg_mem_neg]; exact hx
    rw [← convexHull_neg, h'] at this
    exact this
  have h1 : gauge (Sset ℬ) u ≤ 1 := gauge_le_one_of_mem (hsub hu)
  have h2 : gauge (Sset ℬ) (-w) ≤ 1 := gauge_le_one_of_mem (hsymm _ (hsub hw))
  have := gauge_add_le hconv habs u (-w)
  rw [← sub_eq_add_neg] at this
  unfold sNorm
  linarith


lemma meas_dot' {α : Type*} {mα : MeasurableSpace α} {f g : α → Fin d → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a => f a ⬝ᵥ g a := by
  simp only [dotProduct]
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hf).mul ((measurable_pi_apply i).comp hg)

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

/-- the latent action lies in `𝒦` almost surely -/
lemma X_mem_K [IsProbabilityMeasure P] (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (hℬ : IsCompact ℬ)
    {t : ℕ} (ht : t < T) : ∀ᵐ ω ∂P, R.X t ω ∈ Kset ℬ := by
  have hKc := (Kset_compact hℬ).isClosed.measurableSet.compl
  have hX : Measurable (R.X t) := (hR t ht).1.1
  have hlaw := (hR t ht).2.2.1 _ hKc
  have hGle := G_le hR ht
  have hint : Integrable ((R.X t ⁻¹' (Kset ℬ)ᶜ).indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const 1).indicator (hX hKc)
  have h1 := integral_condExp hGle (μ := P) (f := (R.X t ⁻¹' (Kset ℬ)ᶜ).indicator fun _ => (1 : ℝ))
  rw [integral_congr_ae hlaw] at h1
  simp only [p_supp hR ht, ENNReal.toReal_zero, integral_zero] at h1
  rw [integral_indicator (hX hKc), setIntegral_const, smul_eq_mul, mul_one] at h1
  have h0 : P (R.X t ⁻¹' (Kset ℬ)ᶜ) = 0 := by
    simp only [measureReal_restrict_apply_univ, measureReal_def] at h1
    exact (ENNReal.toReal_eq_zero_iff _).1 h1.symm |>.resolve_right (measure_ne_top _ _)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω
  simpa using hω

end Run


/-! #### Deterministic range bounds -/

/-- the deterministic range recursion -/
noncomputable def rho (d : ℕ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => rho d t + 2 * (gbeta d (t + 1) + rho d t / gB d)

lemma gbeta_pos (hd : 1 ≤ d) (t : ℕ) : 0 < gbeta d t := by
  unfold gbeta
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  positivity

lemma gB_pos : 0 < gB d := by unfold gB; positivity

lemma rho_nonneg (hd : 1 ≤ d) : ∀ t, 0 ≤ rho d t
  | 0 => le_refl _
  | t + 1 => by
    have h := rho_nonneg hd t
    have := gbeta_pos hd (t + 1)
    have := gB_pos (d := d)
    simp only [rho]; positivity

section Bounds

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝒜 ℬ : Set (Fin d → ℝ)}
  {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

lemma v_bound (hd : 1 ≤ d) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T)
    (ω : Ω) {ρ : ℝ}
    (hS : ∀ u ∈ Kset ℬ, ∀ w ∈ Kset ℬ, |(u - w) ⬝ᵥ R.cumEst t ω| ≤ ρ) :
    ∀ x ∈ Kset ℬ, ∀ u ∈ Kset ℬ, ∀ w ∈ Kset ℬ,
      |(u - w) ⬝ᵥ gv (R.p t ω) x| ≤ 2 * (gbeta d (t + 1) + ρ / gB d) := by
  intro x hX u hu w hw
  set S := R.cumEst t ω
  set b := gref ℬ e (t + 1) S
  have hbK : b ∈ Kset ℬ :=
    subset_convexHull ℝ ℬ (G2L.gref_mem hℬ (B_nonempty hd hgen hspan) e (t + 1) S)
  have hU := (feas hR ht ω).2.2.2.2.1
  have hβ := gbeta_pos hd (t + 1)
  have hB := gB_pos (d := d)
  have hUb : ∀ x ∈ Kset ℬ, gU ℬ e (t + 1) S x ≤ gbeta d (t + 1) + ρ / gB d := by
    intro y hy
    unfold gU
    have h1 : sNorm ℬ (y - gref ℬ e (t + 1) S) ≤ 2 := sNorm_sub_le hd hgen hspan hy hbK
    have h2 : gZ ℬ e (t + 1) S y ≤ ρ := by
      unfold gZ
      refine max_le ?_ ?_
      · exact le_trans (abs_nonneg _) (hS y hy b hbK)
      · have := hS y hy b hbK
        rw [sub_dotProduct] at this
        exact le_trans (le_abs_self _) this
    have h3 : gbeta d (t + 1) / 2 * sNorm ℬ (y - gref ℬ e (t + 1) S) ≤ gbeta d (t + 1) := by
      nlinarith
    have h4 : gZ ℬ e (t + 1) S y / gB d ≤ ρ / gB d := div_le_div_of_nonneg_right h2 hB.le
    linarith
  have h1 := hU u hu x hX
  have h2 := hU w hw x hX
  have heq : (u - w) ⬝ᵥ gv (R.p t ω) x =
      (u - b) ⬝ᵥ gv (R.p t ω) x - (w - b) ⬝ᵥ gv (R.p t ω) x := by
    simp only [sub_dotProduct]; ring
  rw [heq]
  calc |(u - b) ⬝ᵥ gv (R.p t ω) x - (w - b) ⬝ᵥ gv (R.p t ω) x|
      ≤ |(u - b) ⬝ᵥ gv (R.p t ω) x| + |(w - b) ⬝ᵥ gv (R.p t ω) x| :=
        abs_sub _ _
    _ ≤ gU ℬ e (t + 1) S u + gU ℬ e (t + 1) S w := add_le_add h1 h2
    _ ≤ 2 * (gbeta d (t + 1) + ρ / gB d) := by linarith [hUb u hu, hUb w hw]

lemma range_bound [IsProbabilityMeasure P] (hd : 1 ≤ d) (hℬ : IsCompact ℬ)
    (hgen : IsGenerator 𝒜 ℬ) (hspan : Submodule.span ℝ 𝒜 = ⊤)
    (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) :
    ∀ t, t ≤ T → ∀ᵐ ω ∂P, ∀ u ∈ Kset ℬ, ∀ w ∈ Kset ℬ,
      |(u - w) ⬝ᵥ R.cumEst t ω| ≤ rho d t := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ae_of_all _ fun ω u _ w _ => by simp [GRun.cumEst, rho]
  | succ t ih =>
    intro ht
    have ht' : t < T := by omega
    filter_upwards [ih (by omega), X_mem_K hR hℬ ht'] with ω hS hX
    intro u hu w hw
    have hv := v_bound hd hℬ hgen hspan hR ht' ω hS (R.X t ω) hX u hu w hw
    have hY : |R.Y t ω| ≤ 1 := (hR t ht').2.2.2.2.1.1 ω
    have hsum : R.cumEst (t + 1) ω = R.cumEst t ω + R.thetaHat t ω := by
      simp [GRun.cumEst, Finset.sum_range_succ]
    rw [hsum, dotProduct_add]
    have hθ : |(u - w) ⬝ᵥ R.thetaHat t ω| ≤ 2 * (gbeta d (t + 1) + rho d t / gB d) := by
      rw [GRun.thetaHat, dotProduct_smul, smul_eq_mul, abs_mul]
      calc |R.Y t ω| * |(u - w) ⬝ᵥ gv (R.p t ω) (R.X t ω)|
          ≤ 1 * (2 * (gbeta d (t + 1) + rho d t / gB d)) :=
            mul_le_mul hY hv (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    calc |(u - w) ⬝ᵥ R.cumEst t ω + (u - w) ⬝ᵥ R.thetaHat t ω|
        ≤ |(u - w) ⬝ᵥ R.cumEst t ω| + |(u - w) ⬝ᵥ R.thetaHat t ω| := abs_add_le _ _
      _ ≤ rho d t + 2 * (gbeta d (t + 1) + rho d t / gB d) := add_le_add (hS u hu w hw) hθ
      _ = rho d (t + 1) := rfl

/-- the almost sure bound on reconstruction differences in round `t` -/
lemma v_bound_ae [IsProbabilityMeasure P] (hd : 1 ≤ d) (hℬ : IsCompact ℬ)
    (hgen : IsGenerator 𝒜 ℬ) (hspan : Submodule.span ℝ 𝒜 = ⊤)
    (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) :
    ∀ᵐ ω ∂P, R.X t ω ∈ Kset ℬ ∧ ∀ u ∈ Kset ℬ, ∀ w ∈ Kset ℬ,
      |(u - w) ⬝ᵥ gv (R.p t ω) (R.X t ω)| ≤ 2 * (gbeta d (t + 1) + rho d t / gB d) := by
  filter_upwards [range_bound hd hℬ hgen hspan hR t ht.le, X_mem_K hR hℬ ht] with ω hS hX
  exact ⟨hX, v_bound hd hℬ hgen hspan hR ht ω hS (R.X t ω) hX⟩

end Bounds

end G2R

-- ===== G2/Exp =====

/-! ### Conditional expectation identities along a GIA-FTRL run -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix
open scoped ENNReal

namespace G2E

variable {d : ℕ}

/-- the statistic space `(p_t, S_t, θ_t)` -/
abbrev Zsp (d : ℕ) := Measure (Fin d → ℝ) × (Fin d → ℝ) × (Fin d → ℝ)

/-- the conditional law kernel of the latent action -/
noncomputable def kZ : Kernel (Zsp d) (Fin d → ℝ) := G2M.kmk.comap Prod.fst measurable_fst

instance : IsMarkovKernel (kZ (d := d)) := by unfold kZ; infer_instance

/-- the dot product as a continuous bilinear map -/
noncomputable def dotB : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => x ⬝ᵥ y) (fun x y z => add_dotProduct x y z)
    (fun c x y => smul_dotProduct c x y) (fun x y z => dotProduct_add x y z)
    (fun c x y => dotProduct_smul c x y)

noncomputable def dotL : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((Fin d → ℝ) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ dotB)

@[simp] lemma dotL_apply (x y : Fin d → ℝ) : dotL x y = x ⬝ᵥ y := rfl

lemma bil_designMat {ν : Measure (Fin d → ℝ)} [IsFiniteMeasure ν] {K : Set (Fin d → ℝ)}
    (hK : IsCompact K) (hν : ν Kᶜ = 0) (a θ : Fin d → ℝ) :
    ∫ x, (a ⬝ᵥ x) * (x ⬝ᵥ θ) ∂ν = a ⬝ᵥ (designMat ν *ᵥ θ) := by
  have hI : ∀ i j, Integrable (fun x : Fin d → ℝ => a i * θ j * (x i * x j)) ν := fun i j =>
    T31.integrable_cpt hK hν (by fun_prop)
  have hfun : (fun x : Fin d → ℝ => (a ⬝ᵥ x) * (x ⬝ᵥ θ)) =
      fun x => ∑ i, ∑ j, a i * θ j * (x i * x j) := by
    funext x
    simp only [dotProduct, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hfun, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hI i j))]
  simp only [dotProduct, Matrix.mulVec, designMat, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => hI i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]; ring

/-- the reconstruction identity `∫ (wᵀ M⁻¹ x)(xᵀ θ) p(dx) = wᵀ θ` -/
lemma recon {ν : Measure (Fin d → ℝ)} [IsProbabilityMeasure ν] {K : Set (Fin d → ℝ)}
    (hK : IsCompact K) (hν : ν Kᶜ = 0) (hPD : (designMat ν).PosDef) (w θ : Fin d → ℝ) :
    ∫ x, (w ⬝ᵥ gv ν x) * (x ⬝ᵥ θ) ∂ν = w ⬝ᵥ θ := by
  have hdet : IsUnit (designMat ν).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hPD.isUnit
  have h1 : ∀ x, w ⬝ᵥ gv ν x = (Matrix.vecMul w (designMat ν)⁻¹) ⬝ᵥ x := fun x => by
    rw [gv, gM, Matrix.dotProduct_mulVec]
  simp_rw [h1]
  rw [bil_designMat hK hν, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

section Run

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

/-- the statistic `(p_t, S_t, θ_t)` -/
noncomputable def Zst (R : GRun d Ω) (t : ℕ) (ω : Ω) : Zsp d := (R.p t ω, R.cumEst t ω, R.θs t ω)

lemma meas_Zst (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) :
    Measurable[R.G t] (Zst R t) := by
  have hhG := G2R.hist_le_G hR ht
  have hp : Measurable[R.G t] (R.p t) := ((hR t ht).2.1.1).mono hhG le_rfl
  have hS : Measurable[R.G t] (R.cumEst t) := (G2R.meas_cumEst hR ht.le).mono hhG le_rfl
  have hθ : Measurable[R.G t] (R.θs t) := (hR t ht).1.2.2.2.2.2.2.1
  exact hp.prodMk (hS.prodMk hθ)

lemma kZ_Zst (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (ω : Ω) :
    kZ (Zst R t ω) = R.p t ω := by
  haveI := G2R.p_prob hR ht ω
  simp [kZ, Zst, G2M.kmk, G2M.mk_eq]

lemma law_hyp (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) :
    ∀ s, MeasurableSet s → P[(R.X t ⁻¹' s).indicator (fun _ => (1 : ℝ)) | R.G t] =ᵐ[P]
      fun ω => (kZ (Zst R t ω) s).toReal := by
  intro s hs
  simp_rw [kZ_Zst hR ht]
  exact (hR t ht).2.2.1 s hs

lemma lint_law (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T)
    {F : Zsp d × (Fin d → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (Zst R t ω, R.X t ω) ∂P = ∫⁻ ω, ∫⁻ x, F (Zst R t ω, x) ∂(R.p t ω) ∂P := by
  rw [G2W.lintegral_law P (G2R.G_le hR ht) (meas_Zst hR ht) (hR t ht).1.1 kZ (law_hyp hR ht) hF]
  simp_rw [kZ_Zst hR ht]

lemma int_law (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T)
    {F : Zsp d × (Fin d → ℝ) → ℝ} (hF : StronglyMeasurable F)
    (hFi : Integrable (fun ω => F (Zst R t ω, R.X t ω)) P) :
    ∫ ω, F (Zst R t ω, R.X t ω) ∂P = ∫ ω, ∫ x, F (Zst R t ω, x) ∂(R.p t ω) ∂P := by
  rw [G2W.integral_law P (G2R.G_le hR ht) (meas_Zst hR ht) (hR t ht).1.1 kZ (law_hyp hR ht) hF
    hFi]
  simp_rw [kZ_Zst hR ht]

end Run


/-- the σ-algebra `G_t ∨ σ(X_t)` -/
def mX {Ω : Type*} (R : GRun d Ω) (t : ℕ) : MeasurableSpace Ω :=
  R.G t ⊔ MeasurableSpace.comap (R.X t) inferInstance

/-- the σ-algebra `G_t ∨ σ(X_t, A_t)` -/
def mXA {Ω : Type*} (R : GRun d Ω) (t : ℕ) : MeasurableSpace Ω :=
  R.G t ⊔ MeasurableSpace.comap (fun ω => (R.X t ω, R.A t ω)) inferInstance

section Ident

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

lemma integrable_A (hℬ : IsCompact ℬ) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) :
    Integrable (R.A t) P := by
  obtain ⟨C, hC⟩ := hℬ.exists_bound_of_continuousOn continuous_id.continuousOn
  exact Integrable.of_bound (hR t ht).1.2.1.aestronglyMeasurable C
    (ae_of_all _ fun ω => hC _ ((hR t ht).2.2.2.1.1 ω))

lemma meas_mean_p (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) :
    Measurable fun ω => G2P.mean (R.p t ω) := by
  have hp : Measurable (R.p t) :=
    ((hR t ht).2.1.1).mono ((G2R.hist_le_G hR ht).trans (G2R.G_le hR ht)) le_rfl
  have : (fun ω => G2P.mean (R.p t ω)) = fun ω i => ∫ x, x i ∂(G2M.mk (R.p t ω)) := by
    funext ω i
    haveI := G2R.p_prob hR ht ω
    rw [G2M.mk_eq]; rfl
  rw [this]
  exact measurable_pi_iff.2 fun i =>
    (G2M.measurable_integral_mk (continuous_apply i)).comp hp

lemma mean_mem {ν : Measure (Fin d → ℝ)} [IsProbabilityMeasure ν] {K : Set (Fin d → ℝ)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hν : ν Kᶜ = 0) : G2P.mean ν ∈ K := by
  have hint : Integrable (fun x : Fin d → ℝ => x) ν := T31.integrable_cpt hK hν continuous_id
  have hmem := hconv.integral_mem hK.isClosed (T31.ae_mem hν) hint
  have : G2P.mean ν = ∫ x, x ∂ν := by
    funext i; rw [eval_integral (fun j => hint.eval j)]; rfl
  rw [this]; exact hmem

/-- **The physical action has the mean of the sampling law.** -/
lemma A_step (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) :
    ∫ ω, R.A t ω ⬝ᵥ R.θs t ω ∂P = ∫ ω, G2P.mean (R.p t ω) ⬝ᵥ R.θs t ω ∂P := by
  obtain ⟨⟨hX, hA, -, hθ, hGle, -, hθG, -⟩, -, -, ⟨hAB, hAc⟩, -, hθn⟩ := hR t ht
  have hKc := G2R.Kset_compact hℬ
  have hm1 : mX R t ≤ mΩ := sup_le hGle hX.comap_le
  have hθm1 : StronglyMeasurable[mX R t] (R.θs t) :=
    (hθG.mono (le_sup_left : R.G t ≤ mX R t) le_rfl).stronglyMeasurable
  have hbA : ∀ ω, |R.A t ω ⬝ᵥ R.θs t ω| ≤ 1 := fun ω =>
    G2R.abs_dot_le_one h𝒜 hgen (hθn ω) (subset_convexHull ℝ ℬ (hAB ω))
  have hmeasAθ : Measurable fun ω => R.A t ω ⬝ᵥ R.θs t ω := G2R.meas_dot' hA hθ
  have hIθA : Integrable (fun ω => dotL (R.θs t ω) (R.A t ω)) P := by
    refine Integrable.of_bound ?_ 1 (ae_of_all _ fun ω => ?_)
    · simpa [dotProduct_comm] using hmeasAθ.aestronglyMeasurable
    · simpa [dotProduct_comm] using hbA ω
  have h1 := condExp_bilin_of_stronglyMeasurable_left dotL hθm1 hIθA (integrable_A hℬ hR ht)
  have h2 : ∫ ω, R.A t ω ⬝ᵥ R.θs t ω ∂P = ∫ ω, R.X t ω ⬝ᵥ R.θs t ω ∂P := by
    calc ∫ ω, R.A t ω ⬝ᵥ R.θs t ω ∂P = ∫ ω, dotL (R.θs t ω) (R.A t ω) ∂P := by
          simp [dotProduct_comm]
      _ = ∫ ω, P[fun ω => dotL (R.θs t ω) (R.A t ω) | mX R t] ω ∂P :=
          (integral_condExp hm1).symm
      _ = ∫ ω, dotL (R.θs t ω) (P[R.A t | mX R t] ω) ∂P := integral_congr_ae h1
      _ = ∫ ω, dotL (R.θs t ω) (R.X t ω) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hAc] with ω hω
          rw [show P[R.A t | mX R t] ω = R.X t ω from hω]
      _ = ∫ ω, R.X t ω ⬝ᵥ R.θs t ω ∂P := by simp [dotProduct_comm]
  -- the conditional law of `X_t`
  have hF : StronglyMeasurable fun z : Zsp d × (Fin d → ℝ) => z.2 ⬝ᵥ z.1.2.2 :=
    (G2R.meas_dot' measurable_snd (measurable_snd.comp (measurable_snd.comp measurable_fst))
      ).stronglyMeasurable
  have hFi : Integrable (fun ω => R.X t ω ⬝ᵥ R.θs t ω) P := by
    refine Integrable.of_bound (G2R.meas_dot' hX hθ).aestronglyMeasurable 1 ?_
    filter_upwards [G2R.X_mem_K hR hℬ ht] with ω hω
    exact G2R.abs_dot_le_one h𝒜 hgen (hθn ω) hω
  have h3 := int_law hR ht hF hFi
  simp only [Zst] at h3
  rw [h2, h3]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  haveI := G2R.p_prob hR ht ω
  exact (G2P.mean_dot hKc (G2R.p_supp hR ht ω) _).symm


/-- **Unbiased loss-difference estimates.** -/
lemma unbiased (hd : 1 ≤ d) (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T)
    {a : Zsp d → Fin d → ℝ} (ha : Measurable a) (haK : ∀ z, a z ∈ Kset ℬ)
    {c : Fin d → ℝ} (hc : c ∈ Kset ℬ) :
    Integrable (fun ω => (a (Zst R t ω) - c) ⬝ᵥ R.thetaHat t ω) P ∧
    ∫ ω, (a (Zst R t ω) - c) ⬝ᵥ R.thetaHat t ω ∂P =
      ∫ ω, (a (Zst R t ω) - c) ⬝ᵥ R.θs t ω ∂P := by
  obtain ⟨⟨hX, hA, hY, hθ, hGle, -, hθG, -⟩, -, -, ⟨hAB, hAc⟩, ⟨hYb, hYc⟩, hθn⟩ := hR t ht
  have hKc := G2R.Kset_compact hℬ
  set cb : ℝ := 2 * (gbeta d (t + 1) + G2R.rho d t / gB d) with hcb
  have hZ : Measurable[R.G t] (Zst R t) := meas_Zst hR ht
  -- the scalar coefficient `c₁ = (a - c)ᵀ v_X(p)`
  set F1 : Zsp d × (Fin d → ℝ) → ℝ := fun z => (a z.1 - c) ⬝ᵥ G2M.V z.1.1 z.2 with hF1
  have hF1m : Measurable F1 :=
    G2R.meas_dot' ((ha.comp measurable_fst).sub measurable_const)
      (G2M.measurable_V_comp (measurable_fst.comp measurable_fst) measurable_snd)
  set c1 : Ω → ℝ := fun ω => F1 (Zst R t ω, R.X t ω) with hc1
  have hc1eq : ∀ ω, c1 ω = (a (Zst R t ω) - c) ⬝ᵥ gv (R.p t ω) (R.X t ω) := fun ω => by
    haveI := G2R.p_prob hR ht ω
    simp only [hc1, hF1, Zst, G2M.V_eq]
  have hc1b : ∀ᵐ ω ∂P, |c1 ω| ≤ cb := by
    filter_upwards [G2R.v_bound_ae hd hℬ hgen hspan hR ht] with ω ⟨hXK, hv⟩
    rw [hc1eq]
    exact hv _ (haK _) _ hc
  -- measurability of `c₁` for the enlarged σ-algebras
  have hXmX : Measurable[mX R t] (R.X t) := Measurable.of_comap_le le_sup_right
  have hZmX : Measurable[mX R t] (Zst R t) := hZ.mono le_sup_left le_rfl
  have hc1mX : Measurable[mX R t] c1 := hF1m.comp (hZmX.prodMk hXmX)
  have hXAm : Measurable[mXA R t] (fun ω => (R.X t ω, R.A t ω)) :=
    Measurable.of_comap_le le_sup_right
  have hc1mXA : Measurable[mXA R t] c1 :=
    hF1m.comp ((hZ.mono le_sup_left le_rfl).prodMk (measurable_fst.comp hXAm))
  have hmX : mX R t ≤ mΩ := sup_le hGle hX.comap_le
  have hmXA : mXA R t ≤ mΩ := sup_le hGle (hX.prodMk hA).comap_le
  have hc1m : Measurable c1 := hc1mX.mono hmX le_rfl
  -- integrability
  have hYi : Integrable (R.Y t) P := Integrable.of_bound hY.aestronglyMeasurable 1
    (ae_of_all _ fun ω => by simpa using hYb ω)
  have hc1Y : Integrable (c1 * R.Y t) P := by
    refine Integrable.of_bound (hc1m.mul hY).aestronglyMeasurable cb ?_
    filter_upwards [hc1b] with ω hω
    rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    nlinarith [hYb ω, abs_nonneg (c1 ω), abs_nonneg (R.Y t ω)]
  have hAθ : ∀ ω, |R.A t ω ⬝ᵥ R.θs t ω| ≤ 1 := fun ω =>
    G2R.abs_dot_le_one h𝒜 hgen (hθn ω) (subset_convexHull ℝ ℬ (hAB ω))
  have hc1A : Integrable (fun ω => dotL (c1 ω • R.θs t ω) (R.A t ω)) P := by
    refine Integrable.of_bound ?_ cb ?_
    · simp only [dotL_apply, smul_dotProduct, smul_eq_mul]
      exact (hc1m.mul (G2R.meas_dot' hθ hA)).aestronglyMeasurable
    · filter_upwards [hc1b] with ω hω
      simp only [dotL_apply, smul_dotProduct, smul_eq_mul, Real.norm_eq_abs, abs_mul]
      rw [dotProduct_comm]
      nlinarith [hAθ ω, abs_nonneg (c1 ω), abs_nonneg (R.A t ω ⬝ᵥ R.θs t ω)]
  -- step a: replace the feedback by its conditional mean
  have hstepa : ∫ ω, c1 ω * R.Y t ω ∂P = ∫ ω, c1 ω * (R.A t ω ⬝ᵥ R.θs t ω) ∂P := by
    have h := condExp_mul_of_stronglyMeasurable_left hc1mXA.stronglyMeasurable hc1Y hYi
    calc ∫ ω, c1 ω * R.Y t ω ∂P = ∫ ω, (c1 * R.Y t) ω ∂P := rfl
      _ = ∫ ω, P[c1 * R.Y t | mXA R t] ω ∂P := (integral_condExp hmXA).symm
      _ = ∫ ω, (c1 * P[R.Y t | mXA R t]) ω ∂P := integral_congr_ae h
      _ = ∫ ω, c1 ω * (R.A t ω ⬝ᵥ R.θs t ω) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hYc] with ω hω
          rw [Pi.mul_apply, show P[R.Y t | mXA R t] ω = R.A t ω ⬝ᵥ R.θs t ω from hω]
  -- step b: replace the physical action by the latent one
  have hstepb : ∫ ω, c1 ω * (R.A t ω ⬝ᵥ R.θs t ω) ∂P =
      ∫ ω, c1 ω * (R.X t ω ⬝ᵥ R.θs t ω) ∂P := by
    have hf : StronglyMeasurable[mX R t] fun ω => c1 ω • R.θs t ω :=
      (hc1mX.smul (hθG.mono le_sup_left le_rfl)).stronglyMeasurable
    have h := condExp_bilin_of_stronglyMeasurable_left dotL hf hc1A (integrable_A hℬ hR ht)
    calc ∫ ω, c1 ω * (R.A t ω ⬝ᵥ R.θs t ω) ∂P = ∫ ω, dotL (c1 ω • R.θs t ω) (R.A t ω) ∂P := by
          simp [smul_dotProduct, dotProduct_comm]
      _ = ∫ ω, P[fun ω => dotL (c1 ω • R.θs t ω) (R.A t ω) | mX R t] ω ∂P :=
          (integral_condExp hmX).symm
      _ = ∫ ω, dotL (c1 ω • R.θs t ω) (P[R.A t | mX R t] ω) ∂P := integral_congr_ae h
      _ = ∫ ω, dotL (c1 ω • R.θs t ω) (R.X t ω) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hAc] with ω hω
          rw [show P[R.A t | mX R t] ω = R.X t ω from hω]
      _ = ∫ ω, c1 ω * (R.X t ω ⬝ᵥ R.θs t ω) ∂P := by
          simp [smul_dotProduct, dotProduct_comm]
  -- step c: the conditional law of the latent action
  set F2 : Zsp d × (Fin d → ℝ) → ℝ := fun z => F1 z * (z.2 ⬝ᵥ z.1.2.2) with hF2
  have hF2m : Measurable F2 :=
    hF1m.mul (G2R.meas_dot' measurable_snd
      (measurable_snd.comp (measurable_snd.comp measurable_fst)))
  have hF2i : Integrable (fun ω => F2 (Zst R t ω, R.X t ω)) P := by
    refine Integrable.of_bound (hF2m.comp ((hZ.mono hGle le_rfl).prodMk hX)).aestronglyMeasurable
      cb ?_
    filter_upwards [hc1b, G2R.X_mem_K hR hℬ ht] with ω hω hXK
    have hXθ := G2R.abs_dot_le_one h𝒜 hgen (hθn ω) hXK
    simp only [hF2, Zst, Real.norm_eq_abs, abs_mul]
    have : |F1 (Zst R t ω, R.X t ω)| ≤ cb := hω
    simp only [Zst] at this
    nlinarith [abs_nonneg (F1 ((R.p t ω, R.cumEst t ω, R.θs t ω), R.X t ω)),
      abs_nonneg (R.X t ω ⬝ᵥ R.θs t ω)]
  have hstepc := int_law hR ht hF2m.stronglyMeasurable hF2i
  -- step d: the reconstruction identity
  have hstepd : ∀ ω, ∫ x, F2 (Zst R t ω, x) ∂(R.p t ω) =
      (a (Zst R t ω) - c) ⬝ᵥ R.θs t ω := by
    intro ω
    haveI := G2R.p_prob hR ht ω
    have hPD := (G2R.feas hR ht ω).2.2.2.1
    have : (fun x => F2 (Zst R t ω, x)) =
        fun x => ((a (Zst R t ω) - c) ⬝ᵥ gv (R.p t ω) x) * (x ⬝ᵥ R.θs t ω) := by
      funext x; simp only [hF2, hF1, Zst, G2M.V_eq]
    rw [this]
    exact recon hKc (G2R.p_supp hR ht ω) hPD _ _
  -- assemble
  have hθhat : ∀ ω, (a (Zst R t ω) - c) ⬝ᵥ R.thetaHat t ω = c1 ω * R.Y t ω := fun ω => by
    rw [GRun.thetaHat, dotProduct_smul, smul_eq_mul, hc1eq, mul_comm]
  refine ⟨?_, ?_⟩
  · simp_rw [hθhat]; exact hc1Y
  · simp_rw [hθhat]
    rw [hstepa, hstepb]
    have : ∫ ω, c1 ω * (R.X t ω ⬝ᵥ R.θs t ω) ∂P = ∫ ω, F2 (Zst R t ω, R.X t ω) ∂P := rfl
    rw [this, hstepc]
    exact integral_congr_ae (ae_of_all _ hstepd)

end Ident

end G2E

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

-- ===== G2/Ftrl =====

/-! ### The all-history FTRL bound of GIA-FTRL -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix
open scoped ENNReal

namespace G2T

variable {d : ℕ}

lemma continuous_chi : Continuous IAFTRL.chi := by
  unfold IAFTRL.chi; fun_prop

lemma chi_nonneg (x : ℝ) : 0 ≤ IAFTRL.chi x := (IAFTRL.lemma_J_4.{0}).2.2.1 x

lemma chi_mono {x y : ℝ} (h : |x| ≤ |y|) : IAFTRL.chi x ≤ IAFTRL.chi y :=
  (IAFTRL.lemma_J_4.{0}).2.2.2.1 x y h

lemma measurable_integral_gibbs' (μ : Measure (Fin d → ℝ)) [SFinite μ] (β : ℝ) {α : Type*}
    [MeasurableSpace α] {σ : α → Fin d → ℝ} (hσ : Measurable σ)
    {f : α × (Fin d → ℝ) → ℝ} (hf : StronglyMeasurable f) :
    Measurable fun a => ∫ x, f (a, x) ∂(G2P.gibbs μ β (σ a)) := by
  have heq : (fun a => ∫ x, f (a, x) ∂(G2P.gibbs μ β (σ a))) = fun a =>
      ∫ x, (Real.exp (-(x ⬝ᵥ σ a) / β) / ∫ y, Real.exp (-(y ⬝ᵥ σ a) / β) ∂μ) * f (a, x) ∂μ := by
    funext a
    rw [G2P.gibbs, integral_tilted]
    rfl
  rw [heq]
  have hZ := (G2M.measurable_Z μ β).comp hσ
  have hc : Measurable fun p : α × (Fin d → ℝ) => Real.exp (-(p.2 ⬝ᵥ σ p.1) / β) :=
    (((G2R.meas_dot' measurable_snd (hσ.comp measurable_fst)).neg).div_const β).exp
  have hg : StronglyMeasurable fun p : α × (Fin d → ℝ) =>
      (Real.exp (-(p.2 ⬝ᵥ σ p.1) / β) / ∫ y, Real.exp (-(y ⬝ᵥ σ p.1) / β) ∂μ) * f p :=
    ((hc.div (hZ.comp measurable_fst)).stronglyMeasurable).mul hf
  exact hg.integral_prod_right'.measurable

section

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

/-- **The proxy-function step (G.226)–(G.232).** -/
lemma chi_step (hd : 1 ≤ d) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) :
    ∫⁻ ω, ENNReal.ofReal (gbeta d (t + 1) * ∫ x, IAFTRL.chi
        (((x - G2P.mean (gq ℬ e (t + 1) (R.cumEst t ω))) ⬝ᵥ R.thetaHat t ω) / gbeta d (t + 1))
        ∂(gq ℬ e (t + 1) (R.cumEst t ω))) ∂P ≤ ENNReal.ofReal (2 * d / gbeta d (t + 1)) := by
  have hne := G2R.B_nonempty hd hgen hspan
  haveI := G2F.refMu_prob hℬ hne e
  have hμK := G2F.refMu_supp hℬ hne e
  have hKc := G2F.Kc hℬ
  have hconv : Convex ℝ (Kset ℬ) := convex_convexHull ℝ ℬ
  set β := gbeta d (t + 1) with hβdef
  have hβ : 0 < β := G2R.gbeta_pos hd (t + 1)
  set μ := refMu ℬ e with hμdef
  have hq : ∀ S, gq ℬ e (t + 1) S = G2P.gibbs μ β S := fun S => rfl
  -- the conditional proxy
  set Ψ : G2E.Zsp d × (Fin d → ℝ) → ℝ := fun a => β * ∫ y, IAFTRL.chi
      (((y - G2P.mean (G2P.gibbs μ β a.1.2.1)) ⬝ᵥ G2M.V a.1.1 a.2) / β)
      ∂(G2P.gibbs μ β a.1.2.1) with hΨ
  have hσ : Measurable fun a : G2E.Zsp d × (Fin d → ℝ) => a.1.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hΨm : Measurable Ψ := by
    refine Measurable.const_mul ?_ β
    refine measurable_integral_gibbs' μ β hσ
      (f := fun a : (G2E.Zsp d × (Fin d → ℝ)) × (Fin d → ℝ) => IAFTRL.chi
        (((a.2 - G2P.mean (G2P.gibbs μ β a.1.1.2.1)) ⬝ᵥ G2M.V a.1.1.1 a.1.2) / β)) ?_
    refine (continuous_chi.measurable.comp ?_).stronglyMeasurable
    refine Measurable.div_const ?_ β
    refine G2R.meas_dot' (measurable_snd.sub ?_) ?_
    · exact (G2M.measurable_mean_gibbs μ β).comp (hσ.comp measurable_fst)
    · exact G2M.measurable_V_comp
        (measurable_fst.comp (measurable_fst.comp measurable_fst))
        (measurable_snd.comp measurable_fst)
  -- pathwise domination
  have hpath : ∀ ω, gbeta d (t + 1) * ∫ x, IAFTRL.chi
        (((x - G2P.mean (gq ℬ e (t + 1) (R.cumEst t ω))) ⬝ᵥ R.thetaHat t ω) / gbeta d (t + 1))
        ∂(gq ℬ e (t + 1) (R.cumEst t ω)) ≤ Ψ (G2E.Zst R t ω, R.X t ω) := by
    intro ω
    haveI := G2P.gibbs_prob hKc hμK β (R.cumEst t ω)
    have hqK := G2P.gibbs_supp hμK β (R.cumEst t ω)
    simp only [hΨ, G2E.Zst, hq]
    refine mul_le_mul_of_nonneg_left ?_ hβ.le
    set m := G2P.mean (G2P.gibbs μ β (R.cumEst t ω))
    set v := G2M.V (R.p t ω) (R.X t ω)
    have hθ : R.thetaHat t ω = R.Y t ω • v := G2R.thetaHat_eq hR ht ω
    have hY : |R.Y t ω| ≤ 1 := (hR t ht).2.2.2.2.1.1 ω
    refine integral_mono (T31.integrable_cpt hKc hqK (by
        refine continuous_chi.comp ?_
        exact ((G2P.cont_dot _).comp (continuous_id.sub continuous_const)).div_const β))
      (T31.integrable_cpt hKc hqK (by
        refine continuous_chi.comp ?_
        exact ((G2P.cont_dot _).comp (continuous_id.sub continuous_const)).div_const β))
      fun x => ?_
    refine chi_mono ?_
    rw [hθ, dotProduct_smul, smul_eq_mul, mul_div_assoc, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) hY
  -- integrate
  calc ∫⁻ ω, ENNReal.ofReal (gbeta d (t + 1) * ∫ x, IAFTRL.chi
        (((x - G2P.mean (gq ℬ e (t + 1) (R.cumEst t ω))) ⬝ᵥ R.thetaHat t ω) / gbeta d (t + 1))
        ∂(gq ℬ e (t + 1) (R.cumEst t ω))) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (Ψ (G2E.Zst R t ω, R.X t ω)) ∂P :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpath ω)
    _ = ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (Ψ (G2E.Zst R t ω, x)) ∂(R.p t ω) ∂P :=
        G2E.lint_law hR ht (ENNReal.measurable_ofReal.comp hΨm)
    _ ≤ ∫⁻ _, ENNReal.ofReal (2 * d / β) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [G2R.range_bound hd hℬ hgen hspan hR t ht.le] with ω hS
        haveI := G2R.p_prob hR ht ω
        have hpK := G2R.p_supp hR ht ω
        haveI := G2P.gibbs_prob hKc hμK β (R.cumEst t ω)
        have hqK := G2P.gibbs_supp hμK β (R.cumEst t ω)
        have hmK : G2P.mean (G2P.gibbs μ β (R.cumEst t ω)) ∈ Kset ℬ :=
          G2E.mean_mem hKc hconv hqK
        set cb := 2 * (gbeta d (t + 1) + G2R.rho d t / gB d)
        have hvb := G2R.v_bound hd hℬ hgen hspan hR ht ω hS
        -- boundedness of the proxy on `𝒦`
        have hΨb : ∀ x ∈ Kset ℬ, |Ψ (G2E.Zst R t ω, x)| ≤ β * IAFTRL.chi (cb / β) := by
          intro x hx
          have h0 : 0 ≤ Ψ (G2E.Zst R t ω, x) := by
            simp only [hΨ]
            exact mul_nonneg hβ.le (integral_nonneg fun y => chi_nonneg _)
          rw [abs_of_nonneg h0]
          simp only [hΨ, G2E.Zst]
          refine mul_le_mul_of_nonneg_left ?_ hβ.le
          calc ∫ y, IAFTRL.chi (((y - G2P.mean (G2P.gibbs μ β (R.cumEst t ω))) ⬝ᵥ
                G2M.V (R.p t ω) x) / β) ∂(G2P.gibbs μ β (R.cumEst t ω))
              ≤ ∫ _, IAFTRL.chi (cb / β) ∂(G2P.gibbs μ β (R.cumEst t ω)) := by
                refine integral_mono_ae (T31.integrable_cpt hKc hqK (by
                    refine continuous_chi.comp ?_
                    exact ((G2P.cont_dot _).comp (continuous_id.sub continuous_const)).div_const
                      β)) (integrable_const _) ?_
                filter_upwards [T31.ae_mem hqK] with y hy
                refine chi_mono ?_
                rw [G2M.V_eq, abs_div, abs_of_pos hβ, abs_div, abs_of_pos hβ]
                have hcb0 : 0 ≤ cb := le_trans (abs_nonneg _) (hvb x hx y hy _ hmK)
                rw [abs_of_nonneg hcb0]
                exact div_le_div_of_nonneg_right (hvb x hx y hy _ hmK) hβ.le
            _ = IAFTRL.chi (cb / β) := by simp
        have hΨi : Integrable (fun x => Ψ (G2E.Zst R t ω, x)) (R.p t ω) := by
          refine Integrable.of_bound
            (hΨm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
            (β * IAFTRL.chi (cb / β)) ?_
          filter_upwards [T31.ae_mem hpK] with x hx
          rw [Real.norm_eq_abs]; exact hΨb x hx
        have hΨ0 : 0 ≤ᵐ[R.p t ω] fun x => Ψ (G2E.Zst R t ω, x) := ae_of_all _ fun x => by
          simp only [hΨ, Pi.zero_apply]
          exact mul_nonneg hβ.le (integral_nonneg fun y => chi_nonneg _)
        rw [← ofReal_integral_eq_lintegral_ofReal hΨi hΨ0]
        refine ENNReal.ofReal_le_ofReal ?_
        have hC := (G2R.feas hR ht ω).2.2.2.2.2.2
        have heq : ∫ x, Ψ (G2E.Zst R t ω, x) ∂(R.p t ω) =
            gC ℬ e (t + 1) (R.cumEst t ω) (R.p t ω) := by
          simp only [hΨ, G2E.Zst, gC]
          rw [integral_const_mul]
          congr 1
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          simp only [G2M.V_eq]
          rfl
        rw [heq]
        exact hC
    _ = ENNReal.ofReal (2 * d / β) := by simp

end


section Explo

variable {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}

/-- **Exploration (G.233)–(G.236).** -/
lemma explo (hd : 1 ≤ d) (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) {t : ℕ} {S : Fin d → ℝ} {p : Measure (Fin d → ℝ)}
    (hf : IsFeasible3_6 ℬ e (t + 1) S p) {θ : Fin d → ℝ} (hθ : setNorm 𝒜 θ ≤ 1) :
    (G2P.mean p - G2P.mean (gq ℬ e (t + 1) S)) ⬝ᵥ θ ≤ 8 * d / gbeta d (t + 1) := by
  obtain ⟨hpP, hpK, ⟨w, hwF, hwK, hγ, hpeq⟩, -⟩ := hf
  have hne := G2R.B_nonempty hd hgen hspan
  haveI := G2F.refMu_prob hℬ hne e
  have hμK := G2F.refMu_supp hℬ hne e
  have hKc := G2F.Kc hℬ
  set β := gbeta d (t + 1) with hβdef
  have hβ : 0 < β := G2R.gbeta_pos hd (t + 1)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hβ16 : 16 * (d : ℝ) ≤ β := by
    simp only [hβdef, gbeta]; linarith [Real.sqrt_nonneg ((t + 1 : ℕ) : ℝ)]
  set q := gq ℬ e (t + 1) S with hqdef
  haveI hqP : IsProbabilityMeasure q := G2P.gibbs_prob hKc hμK β S
  have hqK : q (Kset ℬ)ᶜ = 0 := G2P.gibbs_supp hμK β S
  set γ := (w Set.univ).toReal with hγdef
  have hγ0 : 0 ≤ γ := ENNReal.toReal_nonneg
  have hΓ : gGam d (t + 1) = 4 * d / β := rfl
  have hγ1 : γ ≤ 1 := by
    have : 4 * (d : ℝ) / β ≤ 1 := by rw [div_le_one hβ]; linarith
    linarith [hγ.trans_eq hΓ]
  have hcont := G2P.cont_dot θ
  have hqI : Integrable (fun x : Fin d → ℝ => x ⬝ᵥ θ) q := T31.integrable_cpt hKc hqK hcont
  have hwI : Integrable (fun x : Fin d → ℝ => x ⬝ᵥ θ) w := T31.integrable_cpt hKc hwK hcont
  have hb : ∀ x ∈ Kset ℬ, |x ⬝ᵥ θ| ≤ 1 := fun x hx => G2R.abs_dot_le_one h𝒜 hgen hθ hx
  have hpθ : G2P.mean p ⬝ᵥ θ = (1 - γ) * ∫ x, x ⬝ᵥ θ ∂q + ∫ x, x ⬝ᵥ θ ∂w := by
    rw [G2P.mean_dot hKc hpK, hpeq, integral_add_measure (hqI.smul_measure ENNReal.ofReal_ne_top)
      hwI, integral_smul_measure, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
  have hqθ : G2P.mean q ⬝ᵥ θ = ∫ x, x ⬝ᵥ θ ∂q := G2P.mean_dot hKc hqK θ
  have ha : |∫ x, x ⬝ᵥ θ ∂q| ≤ 1 := by
    have := norm_integral_le_of_norm_le_const (μ := q) (C := 1)
      (by filter_upwards [T31.ae_mem hqK] with x hx using (Real.norm_eq_abs _).symm ▸ hb x hx)
    simpa using this
  have hbw : |∫ x, x ⬝ᵥ θ ∂w| ≤ γ := by
    have := norm_integral_le_of_norm_le_const (μ := w) (C := 1)
      (by filter_upwards [T31.ae_mem hwK] with x hx using (Real.norm_eq_abs _).symm ▸ hb x hx)
    simpa [measureReal_def, hγdef] using this
  rw [sub_dotProduct, hpθ, hqθ]
  have h1 := neg_abs_le (∫ x, x ⬝ᵥ θ ∂q)
  have h2 := le_abs_self (∫ x, x ⬝ᵥ θ ∂w)
  have hγΓ : γ ≤ 4 * d / β := hγ.trans_eq hΓ
  have : (1 - γ) * ∫ x, x ⬝ᵥ θ ∂q + ∫ x, x ⬝ᵥ θ ∂w - ∫ x, x ⬝ᵥ θ ∂q ≤ 2 * γ := by nlinarith
  have h8 : 2 * γ ≤ 8 * d / β := by
    calc 2 * γ ≤ 2 * (4 * d / β) := by linarith
      _ = 8 * d / β := by ring
  linarith

end Explo

/-- `∫ f ≤ B + c` from a pathwise bound `f ≤ g + c` with `∫⁻ g ≤ B` -/
lemma integral_le_of_lintegral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f g : Ω → ℝ} (hf : Integrable f P) (hg0 : ∀ ω, 0 ≤ g ω)
    {c B : ℝ} (hB : 0 ≤ B) (hfg : ∀ ω, f ω ≤ g ω + c)
    (hlint : ∫⁻ ω, ENNReal.ofReal (g ω) ∂P ≤ ENNReal.ofReal B) : ∫ ω, f ω ∂P ≤ B + c := by
  have hfc : Integrable (fun ω => f ω - c) P := hf.sub (integrable_const c)
  have hmax : Integrable (fun ω => max (f ω - c) 0) P := hfc.pos_part
  have h1 : ∫ ω, (f ω - c) ∂P ≤ ∫ ω, max (f ω - c) 0 ∂P :=
    integral_mono hfc hmax fun ω => le_max_left _ _
  have h2 : ∫ ω, max (f ω - c) 0 ∂P = (∫⁻ ω, ENNReal.ofReal (max (f ω - c) 0) ∂P).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => le_max_right _ _)
      hmax.aestronglyMeasurable
  have h3 : ∫⁻ ω, ENNReal.ofReal (max (f ω - c) 0) ∂P ≤ ENNReal.ofReal B := by
    refine le_trans (lintegral_mono fun ω => ?_) hlint
    refine ENNReal.ofReal_le_ofReal (max_le ?_ (hg0 ω))
    linarith [hfg ω]
  have h4 : (∫⁻ ω, ENNReal.ofReal (max (f ω - c) 0) ∂P).toReal ≤ B := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h3
    rwa [ENNReal.toReal_ofReal hB] at this
  rw [integral_sub hf (integrable_const c)] at h1
  simp only [integral_const, probReal_univ, one_smul] at h1
  linarith


section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

/-- **The all-history FTRL bound.** -/
theorem ftrl (hd : 1 ≤ d) (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (hT : 1 ≤ T)
    (u : Fin d → ℝ) (hu : u ∈ Kset ℬ) (q : Measure (Fin d → ℝ)) [IsProbabilityMeasure q]
    (hqK : q (Kset ℬ)ᶜ = 0) (hqμ : q ≪ refMu ℬ e)
    (hKL : Integrable (fun x => Real.log (q.rnDeriv (refMu ℬ e) x).toReal) q) (ε : ℝ)
    (hε : ∀ ϑ : Fin d → ℝ, setNorm 𝒜 ϑ ≤ 1 → |((fun i => ∫ x, x i ∂q) - u) ⬝ᵥ ϑ| ≤ ε) :
    gRegretVs P T R u ≤ gbeta d T * ∫ x, Real.log (q.rnDeriv (refMu ℬ e) x).toReal ∂q +
      ∑ t ∈ Finset.range T, 10 * (d : ℝ) / gbeta d (t + 1) + T * ε := by
  have hne := G2R.B_nonempty hd hgen hspan
  haveI := G2F.refMu_prob hℬ hne e
  have hμK := G2F.refMu_supp hℬ hne e
  have hKc := G2F.Kc hℬ
  have hconv : Convex ℝ (Kset ℬ) := convex_convexHull ℝ ℬ
  set μ := refMu ℬ e with hμdef
  set β : ℕ → ℝ := fun t => gbeta d (t + 1) with hβdef
  have hβpos : ∀ t, 0 < β t := fun t => G2R.gbeta_pos hd (t + 1)
  have hβmono : ∀ t, β t ≤ β (t + 1) := fun t => by
    simp only [hβdef, gbeta]
    gcongr; exact_mod_cast Nat.le_succ _
  set m' := G2P.mean q with hm'
  have hm'K : m' ∈ Kset ℬ := G2E.mean_mem hKc hconv hqK
  set KL := ∫ x, Real.log (q.rnDeriv μ x).toReal ∂q with hKLdef
  -- per-round objects
  set mq : ℕ → Ω → Fin d → ℝ := fun t ω => G2P.mean (G2P.gibbs μ (β t) (R.cumEst t ω))
    with hmq
  have hmqK : ∀ t ω, mq t ω ∈ Kset ℬ := fun t ω => by
    haveI := G2P.gibbs_prob hKc hμK (β t) (R.cumEst t ω)
    exact G2E.mean_mem hKc hconv (G2P.gibbs_supp hμK (β t) (R.cumEst t ω))
  have hdata : ∀ t < T, Measurable (R.A t) ∧ Measurable (R.θs t) ∧
      (∀ ω, setNorm 𝒜 (R.θs t ω) ≤ 1) ∧ Measurable (R.cumEst t) := fun t ht =>
    ⟨(hR t ht).1.2.1, (hR t ht).1.2.2.2.1, (hR t ht).2.2.2.2.2,
      (G2R.meas_cumEst hR ht.le).mono ((G2R.hist_le_G hR ht).trans (G2R.G_le hR ht)) le_rfl⟩
  have hmqm : ∀ t < T, Measurable (mq t) := fun t ht =>
    (G2M.measurable_mean_gibbs μ (β t)).comp (hdata t ht).2.2.2
  have hbd : ∀ t < T, ∀ x ∈ Kset ℬ, ∀ ω, |x ⬝ᵥ R.θs t ω| ≤ 1 := fun t ht x hx ω =>
    G2R.abs_dot_le_one h𝒜 hgen ((hdata t ht).2.2.1 ω) hx
  -- integrability helper for differences of `𝒦`-valued measurable maps
  have hintK : ∀ t < T, ∀ {a b : Ω → Fin d → ℝ}, Measurable a → Measurable b →
      (∀ ω, a ω ∈ Kset ℬ) → (∀ ω, b ω ∈ Kset ℬ) →
      Integrable (fun ω => (a ω - b ω) ⬝ᵥ R.θs t ω) P := by
    intro t ht a b ha hb haK hbK
    refine Integrable.of_bound (G2R.meas_dot' (ha.sub hb) (hdata t ht).2.1).aestronglyMeasurable
      2 (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, sub_dotProduct]
    have := hbd t ht _ (haK ω) ω
    have := hbd t ht _ (hbK ω) ω
    calc |a ω ⬝ᵥ R.θs t ω - b ω ⬝ᵥ R.θs t ω| ≤ |a ω ⬝ᵥ R.θs t ω| + |b ω ⬝ᵥ R.θs t ω| :=
          abs_sub _ _
      _ ≤ 2 := by linarith
  have hmpm : ∀ t < T, Measurable fun ω => G2P.mean (R.p t ω) := fun t ht =>
    G2E.meas_mean_p hR ht
  have hmpK : ∀ t < T, ∀ ω, G2P.mean (R.p t ω) ∈ Kset ℬ := fun t ht ω => by
    haveI := G2R.p_prob hR ht ω
    exact G2E.mean_mem hKc hconv (G2R.p_supp hR ht ω)
  -- (1) the regret as a sum of per-round integrals
  have hreg : gRegretVs P T R u =
      ∑ t ∈ Finset.range T, ∫ ω, (G2P.mean (R.p t ω) - u) ⬝ᵥ R.θs t ω ∂P := by
    unfold gRegretVs
    rw [integral_finsetSum _ fun t ht => hintK t (Finset.mem_range.1 ht)
      (hdata t (Finset.mem_range.1 ht)).1 measurable_const
      (fun ω => subset_convexHull ℝ ℬ ((hR t (Finset.mem_range.1 ht)).2.2.2.1.1 ω))
      (fun _ => hu)]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' := Finset.mem_range.1 ht
    have hA := G2E.A_step h𝒜 hℬ hgen hR ht'
    simp only [sub_dotProduct]
    rw [integral_sub, integral_sub, hA]
    · exact (hintK t ht' (hmpm t ht') measurable_const (hmpK t ht') (fun _ => hm'K)).add
        (integrable_const (m' ⬝ᵥ u)) |>.congr (ae_of_all _ fun ω => by
          simp only [sub_dotProduct]; ring) |> fun h => by
          exact Integrable.of_bound (G2R.meas_dot' (hmpm t ht') (hdata t ht').2.1
            ).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
              rw [Real.norm_eq_abs]; exact hbd t ht' _ (hmpK t ht' ω) ω)
    · exact Integrable.of_bound (G2R.meas_dot' measurable_const (hdata t ht').2.1
        ).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs]; exact hbd t ht' _ hu ω)
    · exact Integrable.of_bound (G2R.meas_dot' (hdata t ht').1 (hdata t ht').2.1
        ).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs]
          exact hbd t ht' _ (subset_convexHull ℝ ℬ ((hR t ht').2.2.2.1.1 ω)) ω)
    · exact Integrable.of_bound (G2R.meas_dot' measurable_const (hdata t ht').2.1
        ).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs]; exact hbd t ht' _ hu ω)
  -- measurability of the loss estimates
  have hθhm : ∀ t < T, Measurable (R.thetaHat t) := fun t ht => by
    have hp : Measurable (R.p t) :=
      ((hR t ht).2.1.1).mono ((G2R.hist_le_G hR ht).trans (G2R.G_le hR ht)) le_rfl
    have : R.thetaHat t = fun ω => R.Y t ω • G2M.V (R.p t ω) (R.X t ω) :=
      funext (G2R.thetaHat_eq hR ht)
    rw [this]
    exact (hR t ht).1.2.2.1.smul (G2M.measurable_V_comp hp (hR t ht).1.1)
  -- (2) unbiasedness of the comparator-relative estimates
  have hunb : ∀ t < T, Integrable (fun ω => (mq t ω - m') ⬝ᵥ R.thetaHat t ω) P ∧
      ∫ ω, (mq t ω - m') ⬝ᵥ R.thetaHat t ω ∂P = ∫ ω, (mq t ω - m') ⬝ᵥ R.θs t ω ∂P := by
    intro t ht
    have ha : Measurable fun z : G2E.Zsp d => G2P.mean (G2P.gibbs μ (β t) z.2.1) :=
      (G2M.measurable_mean_gibbs μ (β t)).comp (measurable_fst.comp measurable_snd)
    have haK : ∀ z : G2E.Zsp d, G2P.mean (G2P.gibbs μ (β t) z.2.1) ∈ Kset ℬ := fun z => by
      haveI := G2P.gibbs_prob hKc hμK (β t) z.2.1
      exact G2E.mean_mem hKc hconv (G2P.gibbs_supp hμK (β t) z.2.1)
    exact G2E.unbiased hd h𝒜 hℬ hgen hspan hR ht ha haK hm'K
  -- (3) the pathwise potential bound and its expectation
  set Φ : ℕ → Ω → ℝ := fun t ω => β t * ∫ x, IAFTRL.chi
      (((x - mq t ω) ⬝ᵥ R.thetaHat t ω) / β t) ∂(G2P.gibbs μ (β t) (R.cumEst t ω)) with hΦ
  have hΦ0 : ∀ t ω, 0 ≤ Φ t ω := fun t ω =>
    mul_nonneg (hβpos t).le (integral_nonneg fun x => chi_nonneg _)
  have hΦm : ∀ t < T, Measurable (Φ t) := fun t ht => by
    refine Measurable.const_mul ?_ _
    refine measurable_integral_gibbs' μ (β t) (hdata t ht).2.2.2
      (f := fun a : Ω × (Fin d → ℝ) => IAFTRL.chi
        (((a.2 - mq t a.1) ⬝ᵥ R.thetaHat t a.1) / β t)) ?_
    refine (continuous_chi.measurable.comp ?_).stronglyMeasurable
    exact (G2R.meas_dot' (measurable_snd.sub ((hmqm t ht).comp measurable_fst))
      ((hθhm t ht).comp measurable_fst)).div_const _
  have hΦint : ∀ t < T, ∫⁻ ω, ENNReal.ofReal (Φ t ω) ∂P ≤
      ENNReal.ofReal (2 * d / β t) := fun t ht => chi_step hd hℬ hgen hspan hR ht
  have hpot : ∫ ω, ∑ t ∈ Finset.range T, (mq t ω - m') ⬝ᵥ R.thetaHat t ω ∂P ≤
      ∑ t ∈ Finset.range T, 2 * (d : ℝ) / β t + gbeta d T * KL := by
    refine integral_le_of_lintegral (integrable_finset_sum _ fun t ht =>
        (hunb t (Finset.mem_range.1 ht)).1)
      (g := fun ω => ∑ t ∈ Finset.range T, Φ t ω)
      (fun ω => Finset.sum_nonneg fun t _ => hΦ0 t ω)
      (Finset.sum_nonneg fun t _ => (div_pos (by positivity) (hβpos t)).le) ?_ ?_
    · intro ω
      obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
      have h := G2P.telescope hKc hμK β hβpos hβmono (fun s => R.thetaHat s ω) hqK hqμ hKL n
      exact h
    · calc ∫⁻ ω, ENNReal.ofReal (∑ t ∈ Finset.range T, Φ t ω) ∂P
          = ∫⁻ ω, ∑ t ∈ Finset.range T, ENNReal.ofReal (Φ t ω) ∂P := by
            congr 1; funext ω
            exact ENNReal.ofReal_sum_of_nonneg fun t _ => hΦ0 t ω
        _ = ∑ t ∈ Finset.range T, ∫⁻ ω, ENNReal.ofReal (Φ t ω) ∂P :=
            lintegral_finset_sum _ fun t ht =>
              ENNReal.measurable_ofReal.comp (hΦm t (Finset.mem_range.1 ht))
        _ ≤ ∑ t ∈ Finset.range T, ENNReal.ofReal (2 * d / β t) :=
            Finset.sum_le_sum fun t ht => hΦint t (Finset.mem_range.1 ht)
        _ = ENNReal.ofReal (∑ t ∈ Finset.range T, 2 * (d : ℝ) / β t) :=
            (ENNReal.ofReal_sum_of_nonneg fun t _ => (div_pos (by positivity) (hβpos t)).le).symm
  -- (4) the exploration and comparator terms
  have hexp : ∀ t < T, ∫ ω, (G2P.mean (R.p t ω) - mq t ω) ⬝ᵥ R.θs t ω ∂P ≤ 8 * d / β t := by
    intro t ht
    have h := fun ω => explo hd h𝒜 hℬ hgen hspan (G2R.feas hR ht ω) ((hdata t ht).2.2.1 ω)
    calc ∫ ω, (G2P.mean (R.p t ω) - mq t ω) ⬝ᵥ R.θs t ω ∂P ≤ ∫ _, 8 * (d : ℝ) / β t ∂P :=
          integral_mono (hintK t ht (hmpm t ht) (hmqm t ht) (hmpK t ht) (hmqK t))
            (integrable_const _) fun ω => h ω
      _ = 8 * d / β t := by simp
  have hcmp : ∀ t < T, ∫ ω, (m' - u) ⬝ᵥ R.θs t ω ∂P ≤ ε := by
    intro t ht
    calc ∫ ω, (m' - u) ⬝ᵥ R.θs t ω ∂P ≤ ∫ _, ε ∂P :=
          integral_mono (hintK t ht measurable_const measurable_const (fun _ => hm'K)
            (fun _ => hu)) (integrable_const _)
            fun ω => le_trans (le_abs_self _) (hε _ ((hdata t ht).2.2.1 ω))
      _ = ε := by simp
  -- (5) assemble
  have hsplit : ∀ t < T, ∫ ω, (G2P.mean (R.p t ω) - u) ⬝ᵥ R.θs t ω ∂P =
      ∫ ω, (mq t ω - m') ⬝ᵥ R.θs t ω ∂P +
        ∫ ω, (G2P.mean (R.p t ω) - mq t ω) ⬝ᵥ R.θs t ω ∂P +
        ∫ ω, (m' - u) ⬝ᵥ R.θs t ω ∂P := by
    intro t ht
    have I1 := hintK t ht (hmqm t ht) measurable_const (hmqK t) (fun _ => hm'K)
    have I2 := hintK t ht (hmpm t ht) (hmqm t ht) (hmpK t ht) (hmqK t)
    have I3 := hintK t ht measurable_const measurable_const (fun _ => hm'K) (fun _ => hu)
    calc ∫ ω, (G2P.mean (R.p t ω) - u) ⬝ᵥ R.θs t ω ∂P
        = ∫ ω, ((mq t ω - m') ⬝ᵥ R.θs t ω + (G2P.mean (R.p t ω) - mq t ω) ⬝ᵥ R.θs t ω +
            (m' - u) ⬝ᵥ R.θs t ω) ∂P := by
          refine integral_congr_ae (ae_of_all _ fun ω => ?_)
          simp only [sub_dotProduct]; ring
      _ = _ := by
          rw [integral_add (f := fun ω => (mq t ω - m') ⬝ᵥ R.θs t ω +
              (G2P.mean (R.p t ω) - mq t ω) ⬝ᵥ R.θs t ω)
            (g := fun ω => (m' - u) ⬝ᵥ R.θs t ω) (I1.add I2) I3,
            integral_add (f := fun ω => (mq t ω - m') ⬝ᵥ R.θs t ω)
            (g := fun ω => (G2P.mean (R.p t ω) - mq t ω) ⬝ᵥ R.θs t ω) I1 I2]
  rw [hreg, Finset.sum_congr rfl fun t ht => hsplit t (Finset.mem_range.1 ht),
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hA : ∑ t ∈ Finset.range T, ∫ ω, (mq t ω - m') ⬝ᵥ R.θs t ω ∂P =
      ∫ ω, ∑ t ∈ Finset.range T, (mq t ω - m') ⬝ᵥ R.thetaHat t ω ∂P := by
    rw [integral_finsetSum _ fun t ht => (hunb t (Finset.mem_range.1 ht)).1]
    exact Finset.sum_congr rfl fun t ht => ((hunb t (Finset.mem_range.1 ht)).2).symm
  have hB : ∑ t ∈ Finset.range T, ∫ ω, (G2P.mean (R.p t ω) - mq t ω) ⬝ᵥ R.θs t ω ∂P ≤
      ∑ t ∈ Finset.range T, 8 * (d : ℝ) / β t :=
    Finset.sum_le_sum fun t ht => hexp t (Finset.mem_range.1 ht)
  have hC : ∑ t ∈ Finset.range T, ∫ ω, (m' - u) ⬝ᵥ R.θs t ω ∂P ≤ T * ε := by
    calc ∑ t ∈ Finset.range T, ∫ ω, (m' - u) ⬝ᵥ R.θs t ω ∂P ≤ ∑ _t ∈ Finset.range T, ε :=
          Finset.sum_le_sum fun t ht => hcmp t (Finset.mem_range.1 ht)
      _ = T * ε := by simp
  have hsum : ∑ t ∈ Finset.range T, 2 * (d : ℝ) / β t + ∑ t ∈ Finset.range T, 8 * (d : ℝ) / β t =
      ∑ t ∈ Finset.range T, 10 * (d : ℝ) / gbeta d (t + 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by simp only [hβdef]; ring
  rw [hA]
  linarith [hpot]

end Main

end G2T

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

-- ===== G1/Master =====

/-! ### The master decomposition (G.3)–(G.5) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix
open scoped ENNReal

namespace G1M

variable {d : ℕ}

section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

theorem master (hd : 1 ≤ d) (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (hT : 1 ≤ T)
    (θ astar : Fin d → ℝ) (hatom : 0 < refMu ℬ e {astar}) :
    gRegretVs P T R astar ≤ penI1 P ℬ e T R astar + stabI2 P ℬ e T R +
      exploI3 P ℬ e T R θ astar + corrI4 P ℬ e T R θ := by
  have hne := G2R.B_nonempty hd hgen hspan
  haveI := G2F.refMu_prob hℬ hne e
  have hμK := G2F.refMu_supp hℬ hne e
  have hKc := G2F.Kc hℬ
  have hconv : Convex ℝ (Kset ℬ) := convex_convexHull ℝ ℬ
  set μ := refMu ℬ e with hμdef
  have haK : astar ∈ Kset ℬ := by
    by_contra h
    have : μ {astar} ≤ μ (Kset ℬ)ᶜ := measure_mono (by simpa using h)
    rw [hμK] at this
    exact absurd (nonpos_iff_eq_zero.mp this) hatom.ne'
  set β : ℕ → ℝ := fun t => gbeta d (t + 1) with hβdef
  have hβpos : ∀ t, 0 < β t := fun t => G2R.gbeta_pos hd (t + 1)
  have hβmono : ∀ t, β t ≤ β (t + 1) := fun t => by
    simp only [hβdef, gbeta]
    gcongr; exact_mod_cast Nat.le_succ _
  set mq : ℕ → Ω → Fin d → ℝ := fun t ω => G2P.mean (G2P.gibbs μ (β t) (R.cumEst t ω))
    with hmq
  have hqw : ∀ t ω, R.qw ℬ e t ω = G2P.gibbs μ (β t) (R.cumEst t ω) := fun t ω => rfl
  have hmqK : ∀ t ω, mq t ω ∈ Kset ℬ := fun t ω => by
    haveI := G2P.gibbs_prob hKc hμK (β t) (R.cumEst t ω)
    exact G2E.mean_mem hKc hconv (G2P.gibbs_supp hμK (β t) (R.cumEst t ω))
  have hdata : ∀ t < T, Measurable (R.A t) ∧ Measurable (R.θs t) ∧
      (∀ ω, setNorm 𝒜 (R.θs t ω) ≤ 1) ∧ Measurable (R.cumEst t) := fun t ht =>
    ⟨(hR t ht).1.2.1, (hR t ht).1.2.2.2.1, (hR t ht).2.2.2.2.2,
      (G2R.meas_cumEst hR ht.le).mono ((G2R.hist_le_G hR ht).trans (G2R.G_le hR ht)) le_rfl⟩
  have hmqm : ∀ t < T, Measurable (mq t) := fun t ht =>
    (G2M.measurable_mean_gibbs μ (β t)).comp (hdata t ht).2.2.2
  have hbd : ∀ t < T, ∀ x ∈ Kset ℬ, ∀ ω, |x ⬝ᵥ R.θs t ω| ≤ 1 := fun t ht x hx ω =>
    G2R.abs_dot_le_one h𝒜 hgen ((hdata t ht).2.2.1 ω) hx
  have hintK : ∀ t < T, ∀ {a b : Ω → Fin d → ℝ}, Measurable a → Measurable b →
      (∀ ω, a ω ∈ Kset ℬ) → (∀ ω, b ω ∈ Kset ℬ) →
      Integrable (fun ω => (a ω - b ω) ⬝ᵥ R.θs t ω) P := by
    intro t ht a b ha hb haK hbK
    refine Integrable.of_bound (G2R.meas_dot' (ha.sub hb) (hdata t ht).2.1).aestronglyMeasurable
      2 (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, sub_dotProduct]
    have := hbd t ht _ (haK ω) ω
    have := hbd t ht _ (hbK ω) ω
    calc |a ω ⬝ᵥ R.θs t ω - b ω ⬝ᵥ R.θs t ω| ≤ |a ω ⬝ᵥ R.θs t ω| + |b ω ⬝ᵥ R.θs t ω| :=
          abs_sub _ _
      _ ≤ 2 := by linarith
  have hmpm : ∀ t < T, Measurable fun ω => G2P.mean (R.p t ω) := fun t ht =>
    G2E.meas_mean_p hR ht
  have hmpK : ∀ t < T, ∀ ω, G2P.mean (R.p t ω) ∈ Kset ℬ := fun t ht ω => by
    haveI := G2R.p_prob hR ht ω
    exact G2E.mean_mem hKc hconv (G2R.p_supp hR ht ω)
  -- θ is bounded on 𝒦
  obtain ⟨Cθ, hCθ⟩ := hKc.exists_bound_of_continuousOn (G2P.cont_dot θ).continuousOn
  have hintθ : ∀ {a b : Ω → Fin d → ℝ}, Measurable a → Measurable b →
      (∀ ω, a ω ∈ Kset ℬ) → (∀ ω, b ω ∈ Kset ℬ) →
      Integrable (fun ω => (a ω - b ω) ⬝ᵥ θ) P := by
    intro a b ha hb haK' hbK
    refine Integrable.of_bound (G2R.meas_dot' (ha.sub hb) measurable_const).aestronglyMeasurable
      (2 * Cθ) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, sub_dotProduct]
    have h1 := hCθ _ (haK' ω)
    have h2 := hCθ _ (hbK ω)
    rw [Real.norm_eq_abs] at h1 h2
    calc |a ω ⬝ᵥ θ - b ω ⬝ᵥ θ| ≤ |a ω ⬝ᵥ θ| + |b ω ⬝ᵥ θ| := abs_sub _ _
      _ ≤ 2 * Cθ := by linarith
  have hint_aff : ∀ (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν], ν (Kset ℬ)ᶜ = 0 →
      ∀ (a g : Fin d → ℝ), ∫ x, (x - a) ⬝ᵥ g ∂ν = (G2P.mean ν - a) ⬝ᵥ g := by
    intro ν _ hνK a g
    simp only [sub_dotProduct]
    rw [integral_sub (T31.integrable_cpt hKc hνK (G2P.cont_dot g)) (integrable_const _),
      integral_const, ← G2P.mean_dot hKc hνK g]
    simp
  -- (1) the regret as a sum of per-round integrals
  have hreg : gRegretVs P T R astar =
      ∑ t ∈ Finset.range T, ∫ ω, (G2P.mean (R.p t ω) - astar) ⬝ᵥ R.θs t ω ∂P := by
    unfold gRegretVs
    rw [integral_finsetSum _ fun t ht => hintK t (Finset.mem_range.1 ht)
      (hdata t (Finset.mem_range.1 ht)).1 measurable_const
      (fun ω => subset_convexHull ℝ ℬ ((hR t (Finset.mem_range.1 ht)).2.2.2.1.1 ω))
      (fun _ => haK)]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' := Finset.mem_range.1 ht
    have hA := G2E.A_step h𝒜 hℬ hgen hR ht'
    simp only [sub_dotProduct]
    rw [integral_sub, integral_sub, hA]
    · exact Integrable.of_bound (G2R.meas_dot' (hmpm t ht') (hdata t ht').2.1
        ).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs]; exact hbd t ht' _ (hmpK t ht' ω) ω)
    · exact Integrable.of_bound (G2R.meas_dot' measurable_const (hdata t ht').2.1
        ).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs]; exact hbd t ht' _ haK ω)
    · exact Integrable.of_bound (G2R.meas_dot' (hdata t ht').1 (hdata t ht').2.1
        ).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs]
          exact hbd t ht' _ (subset_convexHull ℝ ℬ ((hR t ht').2.2.2.1.1 ω)) ω)
    · exact Integrable.of_bound (G2R.meas_dot' measurable_const (hdata t ht').2.1
        ).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs]; exact hbd t ht' _ haK ω)
  -- measurability of the loss estimates
  have hθhm : ∀ t < T, Measurable (R.thetaHat t) := fun t ht => by
    have hp : Measurable (R.p t) :=
      ((hR t ht).2.1.1).mono ((G2R.hist_le_G hR ht).trans (G2R.G_le hR ht)) le_rfl
    have : R.thetaHat t = fun ω => R.Y t ω • G2M.V (R.p t ω) (R.X t ω) :=
      funext (G2R.thetaHat_eq hR ht)
    rw [this]
    exact (hR t ht).1.2.2.1.smul (G2M.measurable_V_comp hp (hR t ht).1.1)
  -- (2) unbiasedness of the comparator-relative estimates
  have hunb : ∀ t < T, Integrable (fun ω => (mq t ω - astar) ⬝ᵥ R.thetaHat t ω) P ∧
      ∫ ω, (mq t ω - astar) ⬝ᵥ R.thetaHat t ω ∂P = ∫ ω, (mq t ω - astar) ⬝ᵥ R.θs t ω ∂P := by
    intro t ht
    have ha : Measurable fun z : G2E.Zsp d => G2P.mean (G2P.gibbs μ (β t) z.2.1) :=
      (G2M.measurable_mean_gibbs μ (β t)).comp (measurable_fst.comp measurable_snd)
    have haK' : ∀ z : G2E.Zsp d, G2P.mean (G2P.gibbs μ (β t) z.2.1) ∈ Kset ℬ := fun z => by
      haveI := G2P.gibbs_prob hKc hμK (β t) z.2.1
      exact G2E.mean_mem hKc hconv (G2P.gibbs_supp hμK (β t) z.2.1)
    exact G2E.unbiased hd h𝒜 hℬ hgen hspan hR ht ha haK' haK
  -- (3) the exploration and corruption integrands
  have hI3pt : ∀ t < T, ∀ ω, (∫ x, (x - astar) ⬝ᵥ θ ∂(R.p t ω) -
      ∫ x, (x - astar) ⬝ᵥ θ ∂(R.qw ℬ e t ω)) = (G2P.mean (R.p t ω) - mq t ω) ⬝ᵥ θ := by
    intro t ht ω
    haveI := G2R.p_prob hR ht ω
    haveI := G2P.gibbs_prob hKc hμK (β t) (R.cumEst t ω)
    rw [hqw, hint_aff _ (G2R.p_supp hR ht ω), hint_aff _ (G2P.gibbs_supp hμK (β t) (R.cumEst t ω))]
    simp only [hmq, sub_dotProduct]; ring
  have hI4pt : ∀ t < T, ∀ ω, (∫ x, x ⬝ᵥ (R.θs t ω - θ) ∂(R.p t ω) -
      ∫ x, x ⬝ᵥ (R.θs t ω - θ) ∂(R.qw ℬ e t ω)) =
        (G2P.mean (R.p t ω) - mq t ω) ⬝ᵥ (R.θs t ω - θ) := by
    intro t ht ω
    haveI := G2R.p_prob hR ht ω
    haveI := G2P.gibbs_prob hKc hμK (β t) (R.cumEst t ω)
    rw [hqw, ← G2P.mean_dot hKc (G2R.p_supp hR ht ω) (R.θs t ω - θ),
      ← G2P.mean_dot hKc (G2P.gibbs_supp hμK (β t) (R.cumEst t ω)) (R.θs t ω - θ)]
    simp only [hmq, sub_dotProduct]
  have hsplit : ∀ t < T, ∫ ω, (G2P.mean (R.p t ω) - astar) ⬝ᵥ R.θs t ω ∂P =
      ∫ ω, (mq t ω - astar) ⬝ᵥ R.θs t ω ∂P +
      ∫ ω, (∫ x, (x - astar) ⬝ᵥ θ ∂(R.p t ω) - ∫ x, (x - astar) ⬝ᵥ θ ∂(R.qw ℬ e t ω)) ∂P +
      ∫ ω, (∫ x, x ⬝ᵥ (R.θs t ω - θ) ∂(R.p t ω) -
        ∫ x, x ⬝ᵥ (R.θs t ω - θ) ∂(R.qw ℬ e t ω)) ∂P := by
    intro t ht
    have I1 : Integrable (fun ω => (mq t ω - astar) ⬝ᵥ R.θs t ω) P :=
      hintK t ht (hmqm t ht) measurable_const (hmqK t) (fun _ => haK)
    have I2a := hintθ (hmpm t ht) (hmqm t ht) (hmpK t ht) (hmqK t)
    have I2 : Integrable (fun ω => ∫ x, (x - astar) ⬝ᵥ θ ∂(R.p t ω) -
        ∫ x, (x - astar) ⬝ᵥ θ ∂(R.qw ℬ e t ω)) P :=
      I2a.congr (ae_of_all _ fun ω => (hI3pt t ht ω).symm)
    have I3a := (hintK t ht (hmpm t ht) (hmqm t ht) (hmpK t ht) (hmqK t)).sub I2a
    have I3 : Integrable (fun ω => ∫ x, x ⬝ᵥ (R.θs t ω - θ) ∂(R.p t ω) -
        ∫ x, x ⬝ᵥ (R.θs t ω - θ) ∂(R.qw ℬ e t ω)) P :=
      I3a.congr (ae_of_all _ fun ω => by
        simp only [Pi.sub_apply]; rw [hI4pt t ht ω, dotProduct_sub])
    calc ∫ ω, (G2P.mean (R.p t ω) - astar) ⬝ᵥ R.θs t ω ∂P
        = ∫ ω, ((mq t ω - astar) ⬝ᵥ R.θs t ω +
            (∫ x, (x - astar) ⬝ᵥ θ ∂(R.p t ω) - ∫ x, (x - astar) ⬝ᵥ θ ∂(R.qw ℬ e t ω)) +
            (∫ x, x ⬝ᵥ (R.θs t ω - θ) ∂(R.p t ω) -
              ∫ x, x ⬝ᵥ (R.θs t ω - θ) ∂(R.qw ℬ e t ω))) ∂P := by
          refine integral_congr_ae (ae_of_all _ fun ω => ?_)
          simp only
          rw [hI3pt t ht ω, hI4pt t ht ω]
          simp only [sub_dotProduct, dotProduct_sub]; ring
      _ = _ := by
          rw [integral_add (f := fun ω => (mq t ω - astar) ⬝ᵥ R.θs t ω +
              (∫ x, (x - astar) ⬝ᵥ θ ∂(R.p t ω) - ∫ x, (x - astar) ⬝ᵥ θ ∂(R.qw ℬ e t ω)))
            (g := fun ω => ∫ x, x ⬝ᵥ (R.θs t ω - θ) ∂(R.p t ω) -
              ∫ x, x ⬝ᵥ (R.θs t ω - θ) ∂(R.qw ℬ e t ω)) (I1.add I2) I3,
            integral_add (f := fun ω => (mq t ω - astar) ⬝ᵥ R.θs t ω)
            (g := fun ω => ∫ x, (x - astar) ⬝ᵥ θ ∂(R.p t ω) -
              ∫ x, (x - astar) ⬝ᵥ θ ∂(R.qw ℬ e t ω)) I1 I2]
  -- (4) the relative entropy and mixability-gap terms
  have hKLdef : ∀ t ω, klDivR (R.qw ℬ e t ω) (refMu ℬ e) =
      ∫ x, llr (G2P.gibbs μ (β t) (R.cumEst t ω)) μ x ∂(G2P.gibbs μ (β t) (R.cumEst t ω)) :=
    fun t ω => rfl
  have hKLcf : ∀ t ω, klDivR (R.qw ℬ e t ω) (refMu ℬ e) =
      -(G2P.mean (G2P.gibbs μ (β t) (R.cumEst t ω)) ⬝ᵥ R.cumEst t ω) / β t -
        Real.log (∫ x, Real.exp (-(x ⬝ᵥ R.cumEst t ω) / β t) ∂μ) := fun t ω =>
    (G2P.gibbs_kl hKc hμK (β := β t) (R.cumEst t ω)).2
  have hKLint : ∀ t < T, Integrable (fun ω => klDivR (R.qw ℬ e t ω) (refMu ℬ e)) P := by
    intro t ht
    have hm : Measurable fun ω => klDivR (R.qw ℬ e t ω) (refMu ℬ e) := by
      have : (fun ω => klDivR (R.qw ℬ e t ω) (refMu ℬ e)) = fun ω =>
          -(G2P.mean (G2P.gibbs μ (β t) (R.cumEst t ω)) ⬝ᵥ R.cumEst t ω) / β t -
            Real.log (∫ x, Real.exp (-(x ⬝ᵥ R.cumEst t ω) / β t) ∂μ) := funext (hKLcf t)
      rw [this]
      exact ((G2R.meas_dot' (hmqm t ht) (hdata t ht).2.2.2).neg.div_const _).sub
        ((G2M.measurable_Z μ (β t)).comp (hdata t ht).2.2.2).log
    refine Integrable.of_bound hm.aestronglyMeasurable
      ((G2R.rho d t + β t * Real.log (1 / (μ {astar}).toReal)) / β t) ?_
    filter_upwards [G2R.range_bound hd hℬ hgen hspan hR t ht.le] with ω hS
    haveI := G2P.gibbs_prob hKc hμK (β t) (R.cumEst t ω)
    have hβt := hβpos t
    have hgk := G2P.gibbs_kl hKc hμK (β := β t) (R.cumEst t ω)
    have e1 := G2P.Fpot_eq_gibbs hKc hμK hβt (R.cumEst t ω)
    have e2 := G2P.Fpot_le_atom hKc hμK hβt (R.cumEst t ω) hatom
    have e3 := G2P.Fpot_le_dv hKc hμK hβt 0 (G2P.gibbs_supp hμK (β t) (R.cumEst t ω))
      (tilted_absolutelyContinuous _ _) hgk.1
    rw [G2P.Fpot_zero hKc hμK, dotProduct_zero, zero_add] at e3
    have e4 := hS astar haK (G2P.mean (G2P.gibbs μ (β t) (R.cumEst t ω))) (hmqK t ω)
    have hsub : astar ⬝ᵥ R.cumEst t ω -
        G2P.mean (G2P.gibbs μ (β t) (R.cumEst t ω)) ⬝ᵥ R.cumEst t ω ≤ G2R.rho d t := by
      rw [← sub_dotProduct]; exact (le_abs_self _).trans e4
    rw [hKLdef, Real.norm_eq_abs]
    have hKL0 := (mul_nonneg_iff_of_pos_left hβt).1 e3
    rw [abs_of_nonneg hKL0, le_div_iff₀ hβt]
    linarith
  have hDdef : ∀ t ω, R.mixGap ℬ e t ω =
      G2P.mean (G2P.gibbs μ (β t) (R.cumEst t ω)) ⬝ᵥ R.thetaHat t ω +
        β t * Real.log (∫ x, Real.exp (-(x ⬝ᵥ R.thetaHat t ω) / β t)
          ∂(G2P.gibbs μ (β t) (R.cumEst t ω))) := by
    intro t ω
    haveI := G2P.gibbs_prob hKc hμK (β t) (R.cumEst t ω)
    rw [G2P.mean_dot hKc (G2P.gibbs_supp hμK (β t) (R.cumEst t ω))]
    rfl
  have hDint : ∀ t < T, Integrable (fun ω => R.mixGap ℬ e t ω) P := by
    intro t ht
    have hσ := (hdata t ht).2.2.2
    have m1 : Measurable fun ω =>
        ∫ x, x ⬝ᵥ R.thetaHat t ω ∂(G2P.gibbs μ (β t) (R.cumEst t ω)) :=
      G2T.measurable_integral_gibbs' μ (β t) hσ
        (f := fun a : Ω × (Fin d → ℝ) => a.2 ⬝ᵥ R.thetaHat t a.1)
        (G2R.meas_dot' measurable_snd ((hθhm t ht).comp measurable_fst)).stronglyMeasurable
    have m2 : Measurable fun ω => ∫ x, Real.exp (-(x ⬝ᵥ R.thetaHat t ω) / β t)
        ∂(G2P.gibbs μ (β t) (R.cumEst t ω)) :=
      G2T.measurable_integral_gibbs' μ (β t) hσ
        (f := fun a : Ω × (Fin d → ℝ) => Real.exp (-(a.2 ⬝ᵥ R.thetaHat t a.1) / β t))
        ((G2R.meas_dot' measurable_snd ((hθhm t ht).comp measurable_fst)).neg.div_const
          _).exp.stronglyMeasurable
    have hm : Measurable fun ω => R.mixGap ℬ e t ω := by
      unfold GRun.mixGap
      exact m1.add (m2.log.const_mul _)
    refine Integrable.of_bound hm.aestronglyMeasurable
      (β t * IAFTRL.chi (2 * (gbeta d (t + 1) + G2R.rho d t / gB d) / β t)) ?_
    filter_upwards [G2R.range_bound hd hℬ hgen hspan hR t ht.le, G2R.X_mem_K hR hℬ ht]
      with ω hS hX
    have hvb := G2R.v_bound hd hℬ hgen hspan hR ht ω hS
    have hY : |R.Y t ω| ≤ 1 := (hR t ht).2.2.2.2.1.1 ω
    have hc : ∀ x ∈ Kset ℬ, |(x - G2P.mean (G2P.gibbs μ (β t) (R.cumEst t ω))) ⬝ᵥ
        R.thetaHat t ω| ≤ 2 * (gbeta d (t + 1) + G2R.rho d t / gB d) := by
      intro x hx
      rw [GRun.thetaHat, dotProduct_smul, smul_eq_mul, abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) hY).trans (hvb _ hX x hx _ (hmqK t ω))
    have hb := G2P.mixGap_bounds hKc hμK (hβpos t) (R.cumEst t ω) (R.thetaHat t ω) hc
    rw [Real.norm_eq_abs, hDdef, abs_of_nonneg hb.1]
    exact hb.2
  -- (5) the pathwise localized telescope
  have hpath : ∀ ω, ∑ t ∈ Finset.range T, (mq t ω - astar) ⬝ᵥ R.thetaHat t ω ≤
      gbeta d 1 * hStar ℬ e astar + ∑ t ∈ Finset.Ico 1 T, (gbeta d (t + 1) - gbeta d t) *
        (hStar ℬ e astar - klDivR (R.qw ℬ e t ω) (refMu ℬ e)) +
      ∑ t ∈ Finset.range T, R.mixGap ℬ e t ω := by
    intro ω
    obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
    have h := G2P.telescope_loc hKc hμK β hβpos hβmono (fun s => R.thetaHat s ω) hatom n
    refine le_of_le_of_eq h ?_
    have e2 : ∀ t ∈ Finset.Ico 1 (n + 1), (β t - β (t - 1)) *
        (Real.log (1 / (μ {astar}).toReal) -
          ∫ x, llr (G2P.gibbs μ (β t) (∑ s ∈ Finset.range t, R.thetaHat s ω)) μ x
            ∂(G2P.gibbs μ (β t) (∑ s ∈ Finset.range t, R.thetaHat s ω))) =
        (gbeta d (t + 1) - gbeta d t) *
          (hStar ℬ e astar - klDivR (R.qw ℬ e t ω) (refMu ℬ e)) := by
      intro t ht
      have : t - 1 + 1 = t := Nat.sub_add_cancel (Finset.mem_Ico.1 ht).1
      simp only [hβdef, this]
      rfl
    have e3 : ∀ t ∈ Finset.range (n + 1),
        G2P.mean (G2P.gibbs μ (β t) (∑ s ∈ Finset.range t, R.thetaHat s ω)) ⬝ᵥ R.thetaHat t ω +
          β t * Real.log (∫ x, Real.exp (-(x ⬝ᵥ R.thetaHat t ω) / β t)
            ∂(G2P.gibbs μ (β t) (∑ s ∈ Finset.range t, R.thetaHat s ω))) =
        R.mixGap ℬ e t ω := fun t _ => (hDdef t ω).symm
    rw [Finset.sum_congr rfl e2, Finset.sum_congr rfl e3]
    rfl
  -- (6) take expectations
  have hpot : ∫ ω, ∑ t ∈ Finset.range T, (mq t ω - astar) ⬝ᵥ R.thetaHat t ω ∂P ≤
      penI1 P ℬ e T R astar + stabI2 P ℬ e T R := by
    have hIcoT : ∀ t ∈ Finset.Ico 1 T, t < T := fun t ht => (Finset.mem_Ico.1 ht).2
    have hKLt : ∀ t ∈ Finset.Ico 1 T, Integrable (fun ω => (gbeta d (t + 1) - gbeta d t) *
        (hStar ℬ e astar - klDivR (R.qw ℬ e t ω) (refMu ℬ e))) P := fun t ht =>
      ((integrable_const _).sub (hKLint t (hIcoT t ht))).const_mul _
    have hF1 : Integrable (fun ω => ∑ t ∈ Finset.Ico 1 T, (gbeta d (t + 1) - gbeta d t) *
        (hStar ℬ e astar - klDivR (R.qw ℬ e t ω) (refMu ℬ e))) P :=
      integrable_finsetSum _ hKLt
    have hF2 : Integrable (fun ω => ∑ t ∈ Finset.range T, R.mixGap ℬ e t ω) P :=
      integrable_finsetSum _ fun t ht => hDint t (Finset.mem_range.1 ht)
    calc ∫ ω, ∑ t ∈ Finset.range T, (mq t ω - astar) ⬝ᵥ R.thetaHat t ω ∂P
        ≤ ∫ ω, (gbeta d 1 * hStar ℬ e astar + ∑ t ∈ Finset.Ico 1 T,
            (gbeta d (t + 1) - gbeta d t) *
              (hStar ℬ e astar - klDivR (R.qw ℬ e t ω) (refMu ℬ e)) +
            ∑ t ∈ Finset.range T, R.mixGap ℬ e t ω) ∂P :=
          integral_mono (integrable_finsetSum _ fun t ht => (hunb t (Finset.mem_range.1 ht)).1)
            (((integrable_const _).add hF1).add hF2) hpath
      _ = penI1 P ℬ e T R astar + stabI2 P ℬ e T R := by
          rw [integral_add (f := fun ω => gbeta d 1 * hStar ℬ e astar + ∑ t ∈ Finset.Ico 1 T,
              (gbeta d (t + 1) - gbeta d t) *
                (hStar ℬ e astar - klDivR (R.qw ℬ e t ω) (refMu ℬ e)))
              (g := fun ω => ∑ t ∈ Finset.range T, R.mixGap ℬ e t ω)
              ((integrable_const _).add hF1) hF2,
            integral_add (f := fun _ => gbeta d 1 * hStar ℬ e astar)
              (g := fun ω => ∑ t ∈ Finset.Ico 1 T, (gbeta d (t + 1) - gbeta d t) *
                (hStar ℬ e astar - klDivR (R.qw ℬ e t ω) (refMu ℬ e)))
              (integrable_const _) hF1, integral_const,
            integral_finsetSum _ hKLt,
            integral_finsetSum _ fun t ht => hDint t (Finset.mem_range.1 ht)]
          simp only [probReal_univ, one_smul, integral_const_mul]
          rfl
  -- (7) assemble
  have hA : ∑ t ∈ Finset.range T, ∫ ω, (mq t ω - astar) ⬝ᵥ R.θs t ω ∂P =
      ∫ ω, ∑ t ∈ Finset.range T, (mq t ω - astar) ⬝ᵥ R.thetaHat t ω ∂P := by
    rw [integral_finsetSum _ fun t ht => (hunb t (Finset.mem_range.1 ht)).1]
    exact Finset.sum_congr rfl fun t ht => ((hunb t (Finset.mem_range.1 ht)).2).symm
  have hfin : gRegretVs P T R astar =
      ∫ ω, ∑ t ∈ Finset.range T, (mq t ω - astar) ⬝ᵥ R.thetaHat t ω ∂P +
        exploI3 P ℬ e T R θ astar + corrI4 P ℬ e T R θ := by
    rw [hreg, Finset.sum_congr rfl fun t ht => hsplit t (Finset.mem_range.1 ht),
      Finset.sum_add_distrib, Finset.sum_add_distrib, hA]
    rfl
  rw [hfin]
  linarith [hpot]

end Main

end G1M

namespace IAFTRL

open MeasureTheory

theorem _root_.solution {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (hk : 1 ≤ kdim ℬ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
    (R : GRun d Ω) (hT : 1 ≤ T) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (θ astar : Fin d → ℝ)
    (hatom : 0 < refMu ℬ e {astar}) :
    gRegretVs P T R astar ≤ penI1 P ℬ e T R astar + stabI2 P ℬ e T R +
      exploI3 P ℬ e T R θ astar + corrI4 P ℬ e T R θ :=
  G1M.master hd h𝒜 hℬ hgen hspan hR hT θ astar hatom

end IAFTRL
