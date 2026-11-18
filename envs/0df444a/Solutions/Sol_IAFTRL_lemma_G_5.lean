-- Prove2me | solution 1 for IAFTRL.lemma_G_5
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-17T16:09:32.453713+00:00
-- url     : https://prove2.me/submissions/ea27abc9-0b4d-4fcb-9b61-5e3a5008be80

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_chi
import Definitions.Def_IAFTRL_GTerms
import Theorems.Thm_IAFTRL_lemma_J_4
import Theorems.Thm_IAFTRL_lemma_G_12
import Theorems.Thm_IAFTRL_lemma_G_3
import Theorems.Thm_IAFTRL_lemma_G_26
import Theorems.Thm_IAFTRL_lemma_G_7
import Theorems.Thm_IAFTRL_lemma_G_ref_id

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

-- ===== G1/Helpers =====

/-! ### Small helpers for the term lemmas G.1, G.4, G.5 -/

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

lemma int_le_of_le_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f g : Ω → ℝ}
    (hg : Integrable g P) (hg0 : 0 ≤ᵐ[P] g) (hfg : f ≤ᵐ[P] g) :
    ∫ ω, f ω ∂P ≤ ∫ ω, g ω ∂P := by
  by_cases hf : Integrable f P
  · exact integral_mono_ae hf hg hfg
  · rw [integral_undef hf]; exact integral_nonneg_of_ae hg0

lemma sum_inv_sq (T : ℕ) : ∑ t ∈ Finset.range T, (((t : ℝ) + 1) ^ 2)⁻¹ ≤ 2 := by
  have h : ∀ t ∈ Finset.range T, (((t : ℝ) + 1) ^ 2)⁻¹ ≤
      2 * ((((t : ℕ) : ℝ) + 1)⁻¹ - (((t + 1 : ℕ) : ℝ) + 1)⁻¹) := by
    intro t _
    push_cast
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have e1 : 2 * (((t : ℝ) + 1)⁻¹ - ((t : ℝ) + 1 + 1)⁻¹) =
        2 / (((t : ℝ) + 1) * ((t : ℝ) + 2)) := by
      field_simp; ring
    rw [e1, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc _ ≤ ∑ t ∈ Finset.range T, 2 * ((((t : ℕ) : ℝ) + 1)⁻¹ - (((t + 1 : ℕ) : ℝ) + 1)⁻¹) :=
        Finset.sum_le_sum h
    _ = 2 * ((((0 : ℕ) : ℝ) + 1)⁻¹ - (((T : ℕ) : ℝ) + 1)⁻¹) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub' (fun t : ℕ => (((t : ℕ) : ℝ) + 1)⁻¹)]
    _ ≤ 2 := by
        have : 0 ≤ (((T : ℕ) : ℝ) + 1)⁻¹ := by positivity
        simp only [Nat.cast_zero, zero_add, inv_one]
        linarith

lemma inv_sqrt_le_one (t : ℕ) : (Real.sqrt ((t : ℝ) + 1))⁻¹ ≤ 1 := by
  rw [inv_le_one₀ (Real.sqrt_pos.2 (by positivity))]
  exact Real.one_le_sqrt.2 (by have : (0 : ℝ) ≤ t := Nat.cast_nonneg t; linarith)

lemma harm_le (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Finset.range T, ((t : ℝ) + 1)⁻¹ ≤ Real.log (Real.exp 1 * T) := by
  have h := harmonic_le_one_add_log T
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  rw [Real.log_mul (Real.exp_pos 1).ne' hT0.ne', Real.log_exp]
  refine le_trans (le_of_eq ?_) h
  simp [harmonic]

lemma inv_pow32_le (t : ℕ) :
    (Real.sqrt ((t : ℝ) + 1))⁻¹ * ((t : ℝ) + 1)⁻¹ ≤
      6 * ((Real.sqrt (((t : ℕ) : ℝ) + 1))⁻¹ - (Real.sqrt (((t + 1 : ℕ) : ℝ) + 1))⁻¹) := by
  push_cast
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  set a := Real.sqrt ((t : ℝ) + 1) with ha
  set b := Real.sqrt ((t : ℝ) + 1 + 1) with hb
  have ha2 : a ^ 2 = (t : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = a ^ 2 + 1 := by rw [ha2, hb]; exact Real.sq_sqrt (by positivity)
  have ha1 : 1 ≤ a := Real.one_le_sqrt.2 (by linarith)
  have hb0 : 0 < b := Real.sqrt_pos.2 (by positivity)
  have ha0 : 0 < a := by linarith
  have hba : b ≤ 2 * a := by nlinarith
  have hab : a ≤ b := by nlinarith
  have hid : (6 * a ^ 2 * b - 6 * a ^ 3 - b) * (a + b) = 6 * a ^ 2 - a * b - b ^ 2 := by
    linear_combination (6 * a ^ 2) * hb2
  have hpos : 0 ≤ 6 * a ^ 2 - a * b - b ^ 2 := by nlinarith
  have key : 0 ≤ 6 * a ^ 2 * b - 6 * a ^ 3 - b := by
    have h1 : 0 ≤ (6 * a ^ 2 * b - 6 * a ^ 3 - b) * (a + b) := by rw [hid]; exact hpos
    exact nonneg_of_mul_nonneg_left h1 (by positivity)
  rw [← ha2]
  have e1 : 6 * (a⁻¹ - b⁻¹) = 6 * (b - a) / (a * b) := by field_simp
  rw [e1, ← mul_inv, div_eq_mul_inv]
  have e2 : (a * a ^ 2)⁻¹ = 1 / (a ^ 3) := by rw [one_div]; ring
  rw [e2, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma sum_inv_pow32 (T : ℕ) :
    ∑ t ∈ Finset.range T, (Real.sqrt ((t : ℝ) + 1))⁻¹ * ((t : ℝ) + 1)⁻¹ ≤ 6 := by
  calc _ ≤ ∑ t ∈ Finset.range T,
        6 * ((Real.sqrt (((t : ℕ) : ℝ) + 1))⁻¹ - (Real.sqrt (((t + 1 : ℕ) : ℝ) + 1))⁻¹) :=
        Finset.sum_le_sum fun t _ => inv_pow32_le t
    _ = 6 * ((Real.sqrt (((0 : ℕ) : ℝ) + 1))⁻¹ - (Real.sqrt (((T : ℕ) : ℝ) + 1))⁻¹) := by
        rw [← Finset.mul_sum,
          Finset.sum_range_sub' (fun t : ℕ => (Real.sqrt (((t : ℕ) : ℝ) + 1))⁻¹)]
    _ ≤ 6 := by
        have : 0 ≤ (Real.sqrt (((T : ℕ) : ℝ) + 1))⁻¹ := by positivity
        simp only [Nat.cast_zero, zero_add, Real.sqrt_one, inv_one]
        linarith

end G1P

-- ===== G1/Geo2 =====

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

-- ===== G1/Gibbs =====

/-! ### Gibbs-law helpers: proxy domination and density bounds -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix
open scoped ENNReal

namespace G2P

variable {d : ℕ}

lemma chi_le_exp_abs (y : ℝ) : IAFTRL.chi y ≤ Real.exp |y| := by
  unfold IAFTRL.chi
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]
    have : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  · rw [abs_of_nonpos hy]
    have : Real.exp y ≤ 1 := Real.exp_le_one_iff.2 hy
    linarith

lemma chi_zero' : IAFTRL.chi 0 = 0 := by
  unfold IAFTRL.chi; simp; norm_num

section

variable {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ] {K : Set (Fin d → ℝ)}
  (hK : IsCompact K) (hμK : μ Kᶜ = 0)
include hK hμK

/-- the mixability gap is dominated by the centered proxy -/
lemma mixGap_le_chi {β : ℝ} (hβ : 0 < β) (S g : Fin d → ℝ) :
    mean (gibbs μ β S) ⬝ᵥ g + β * Real.log (∫ x, Real.exp (-(x ⬝ᵥ g) / β) ∂(gibbs μ β S)) ≤
      β * ∫ x, IAFTRL.chi (((x - mean (gibbs μ β S)) ⬝ᵥ g) / β) ∂(gibbs μ β S) := by
  haveI := gibbs_prob hK hμK β S
  set q := gibbs μ β S with hq
  have hqK : q Kᶜ = 0 := gibbs_supp hμK β S
  set m := mean q with hm
  have hcont : Continuous fun x : Fin d → ℝ => -((x - m) ⬝ᵥ g) / β :=
    ((cont_dot g).comp (continuous_id.sub continuous_const)).neg.div_const β
  have hie : Integrable (fun x => Real.exp (-((x - m) ⬝ᵥ g) / β)) q :=
    T31.integrable_cpt hK hqK hcont.rexp
  have hI : 0 < ∫ x, Real.exp (-((x - m) ⬝ᵥ g) / β) ∂q := integral_exp_pos hie
  have hshift : ∫ x, Real.exp (-(x ⬝ᵥ g) / β) ∂q =
      Real.exp (-(m ⬝ᵥ g) / β) * ∫ x, Real.exp (-((x - m) ⬝ᵥ g) / β) ∂q := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [← Real.exp_add, sub_dotProduct]; congr 1; ring
  have heq : m ⬝ᵥ g + β * Real.log (∫ x, Real.exp (-(x ⬝ᵥ g) / β) ∂q) =
      β * Real.log (∫ x, Real.exp (-((x - m) ⬝ᵥ g) / β) ∂q) := by
    rw [hshift, Real.log_mul (Real.exp_pos _).ne' hI.ne', Real.log_exp]
    field_simp; ring
  rw [heq]
  exact log_le_chi hK hμK hβ hqK g

/-- integrals against the Gibbs law are dominated by `1/µ{a}` times `e^{−(x−a)ᵀS/β} µ` -/
lemma gibbs_le {β : ℝ} (hβ : 0 < β) (S : Fin d → ℝ) {a : Fin d → ℝ} (ha : 0 < μ {a})
    {g : (Fin d → ℝ) → ℝ} (hg0 : ∀ x, 0 ≤ g x) :
    ∫ x, g x ∂(gibbs μ β S) ≤
      ((μ {a}).toReal)⁻¹ * ∫ x, g x * Real.exp (-((x - a) ⬝ᵥ S) / β) ∂μ := by
  set pa := (μ {a}).toReal with hpadef
  have hpa : 0 < pa := ENNReal.toReal_pos ha.ne' (measure_ne_top _ _)
  set c := a ⬝ᵥ S with hc
  set Z := ∫ x, Real.exp (-(x ⬝ᵥ S) / β) ∂μ with hZdef
  have hZ : 0 < Z := Z_pos hK hμK β S
  have hE : Continuous fun x : Fin d → ℝ => Real.exp (-((x - a) ⬝ᵥ S) / β) :=
    (((cont_dot S).comp (continuous_id.sub continuous_const)).neg.div_const β).rexp
  set Zs := ∫ x, Real.exp (-((x - a) ⬝ᵥ S) / β) ∂μ with hZsdef
  have hexp : ∀ x : Fin d → ℝ, Real.exp (-(x ⬝ᵥ S) / β) =
      Real.exp (-c / β) * Real.exp (-((x - a) ⬝ᵥ S) / β) := by
    intro x; rw [← Real.exp_add]; congr 1; rw [hc, sub_dotProduct]; ring
  have hZs : Z = Real.exp (-c / β) * Zs := by
    rw [hZdef, hZsdef, ← integral_const_mul]; congr 1; funext x; exact hexp x
  have hZspa : pa ≤ Zs := by
    have h1 := setIntegral_le_integral (s := {a}) (T31.integrable_cpt hK hμK hE)
      (ae_of_all _ fun x => (Real.exp_pos _).le)
    rw [integral_singleton, smul_eq_mul, sub_self, zero_dotProduct, neg_zero, zero_div,
      Real.exp_zero, mul_one, measureReal_def] at h1
    exact h1
  have hZs0 : 0 < Zs := lt_of_lt_of_le hpa hZspa
  rw [gibbs, integral_tilted]
  simp only [smul_eq_mul]
  rw [← hZdef]
  have hpt : ∀ x, Real.exp (-(x ⬝ᵥ S) / β) / Z * g x =
      Zs⁻¹ * (g x * Real.exp (-((x - a) ⬝ᵥ S) / β)) := by
    intro x; rw [hexp x, hZs]; field_simp
  simp_rw [hpt]
  rw [integral_const_mul]
  have hI0 : 0 ≤ ∫ x, g x * Real.exp (-((x - a) ⬝ᵥ S) / β) ∂μ :=
    integral_nonneg fun x => mul_nonneg (hg0 x) (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hpa hZspa) hI0

end

end G2P


-- ===== G1/PComp =====

/-! ### The comparison law of Definition G.2 -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix
open scoped ENNReal

namespace G1C

variable {d : ℕ}

section Comp

variable {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}

/-- the extra exploration measure `ρ n|_{·≠a*}` -/
noncomputable def wc (ν : Measure (Fin d → ℝ)) (astar : Fin d → ℝ) (ρ : ℝ) :
    Measure (Fin d → ℝ) :=
  ENNReal.ofReal ρ • ν.restrict {astar}ᶜ

/-- the comparison law `p^c = (1 − γ) q + ρ n|_{·≠a*}` of Definition G.2 -/
noncomputable def pcomp (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (n : ℕ) (S : Fin d → ℝ)
    (ν : Measure (Fin d → ℝ)) (astar : Fin d → ℝ) (ρ : ℝ) : Measure (Fin d → ℝ) :=
  ENNReal.ofReal (1 - (wc ν astar ρ univ).toReal) • gq ℬ e n S + wc ν astar ρ

/-- integrals against the comparison law -/
lemma pcomp_int (hd : 1 ≤ d) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) {ν : Measure (Fin d → ℝ)} [IsFiniteMeasure ν]
    (hνK : ν (Kset ℬ)ᶜ = 0) {astar : Fin d → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) {n : ℕ} {S : Fin d → ℝ}
    (hγ : (wc ν astar ρ univ).toReal ≤ 1) {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂(pcomp ℬ e n S ν astar ρ) = (1 - (wc ν astar ρ univ).toReal) *
      ∫ x, f x ∂(gq ℬ e n S) + ρ * ∫ x, f x ∂(ν.restrict {astar}ᶜ) := by
  have hne := G2R.B_nonempty hd hgen hspan
  haveI := G2F.refMu_prob hℬ hne e
  have hμK := G2F.refMu_supp hℬ hne e
  have hKc := G2F.Kc hℬ
  haveI : IsProbabilityMeasure (gq ℬ e n S) := G2P.gibbs_prob hKc hμK (gbeta d n) S
  have hqK : gq ℬ e n S (Kset ℬ)ᶜ = 0 := G2P.gibbs_supp hμK (gbeta d n) S
  have hν'K : ν.restrict {astar}ᶜ (Kset ℬ)ᶜ = 0 :=
    le_antisymm ((Measure.restrict_apply_le _ _).trans (le_of_eq hνK)) zero_le
  have hwK : wc ν astar ρ (Kset ℬ)ᶜ = 0 := by
    rw [wc, Measure.smul_apply, hν'K, smul_zero]
  haveI : IsFiniteMeasure (wc ν astar ρ) := ⟨by
    rw [wc, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  rw [pcomp, integral_add_measure ((T31.integrable_cpt hKc hqK hf).smul_measure
    ENNReal.ofReal_ne_top) (T31.integrable_cpt hKc hwK hf), integral_smul_measure,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul, wc, integral_smul_measure,
    ENNReal.toReal_ofReal hρ, smul_eq_mul]

end Comp

end G1C

-- ===== G1/ExploX =====

/-! ### The exploration envelope `⟨p − q, Δ⟩ ≤ 2Γ` -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix
open scoped ENNReal

namespace G2X

variable {d : ℕ}

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

end G2X

-- ===== G1/G5Good =====

/-! ### Lemma G.5: the exploration integrand on comparison rounds, (G.95)–(G.97) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix
open scoped ENNReal

namespace G1E

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}

theorem explo_good (hd : 1 ≤ d) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) {θ astar : Fin d → ℝ} (haK : astar ∈ Kset ℬ)
    (hΔ0 : ∀ a ∈ Kset ℬ, 0 ≤ (a - astar) ⬝ᵥ θ) (hΔ2 : ∀ a ∈ Kset ℬ, (a - astar) ⬝ᵥ θ ≤ 2)
    {ν : Measure (Fin d → ℝ)} (hν : IsCtrAlloc ℬ θ astar ν)
    {n : ℕ} (hn : 1 ≤ n) {S : Fin d → ℝ} (href : gref ℬ e n S = astar)
    (hX0 : ∀ a ∈ Kset ℬ, 0 ≤ (a - astar) ⬝ᵥ S)
    {L U : ℝ} (hL : 1 ≤ L) (hU0 : 0 ≤ U)
    (hgapL : ∀ a ∈ Kset ℬ, (a - astar) ⬝ᵥ θ ≤ L * ((a - astar) ⬝ᵥ S / n))
    (hgapU : ∀ a ∈ Kset ℬ, (a - astar) ⬝ᵥ S / n ≤ U * ((a - astar) ⬝ᵥ θ))
    (hρ1 : 16 * gB d * L ^ 2 / n ≤ 1)
    (hN : 16 * gB d * L ^ 2 / n * (ν univ).toReal ≤ gGam d n)
    (hN4 : 16 * gB d * L ^ 2 / n * (ν univ).toReal ≤ 1 / 4)
    (hq : 3 / 4 ≤ (gq ℬ e n S {astar}).toReal)
    (ha : 0 < refMu ℬ e {astar})
    (hprox : 64 * ∫ x in {astar}ᶜ, Real.exp (-((x - astar) ⬝ᵥ S) / (2 * gbeta d n))
        ∂(refMu ℬ e) ≤ 2 * d * (16 * gB d * L ^ 2 / n) ^ 2 * (refMu ℬ e {astar}).toReal)
    {p : Measure (Fin d → ℝ)} (hmin : IsMin3_6 ℬ e n S p) :
    ∫ x, (x - astar) ⬝ᵥ θ ∂p - ∫ x, (x - astar) ⬝ᵥ θ ∂(gq ℬ e n S) ≤
      2 * ((refMu ℬ e {astar}).toReal)⁻¹ * (∫ x in {astar}ᶜ, Real.exp (-((x - astar) ⬝ᵥ S) /
        (2 * gbeta d n)) ∂(refMu ℬ e)) * (L * U) +
      16 * gB d * ctrCost θ astar ν / n * (L ^ 3 * U) := by
  have hne := G2R.B_nonempty hd hgen hspan
  haveI := G2F.refMu_prob hℬ hne e
  have hμK := G2F.refMu_supp hℬ hne e
  have hKc := G2F.Kc hℬ
  set μ := refMu ℬ e with hμdef
  set β := gbeta d n with hβdef
  have hβ : 0 < β := G2R.gbeta_pos hd n
  set q := gq ℬ e n S with hqdef
  haveI hqP : IsProbabilityMeasure q := G2P.gibbs_prob hKc hμK β S
  have hqK : q (Kset ℬ)ᶜ = 0 := G2P.gibbs_supp hμK β S
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set B := gB d with hBdef
  have hB0 : 0 < B := by rw [hBdef, gB]; positivity
  set ρ := 16 * B * L ^ 2 / n with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hfeas := lemma_G_7 hd 𝒜 ℬ e hℬ hgen hspan θ astar haK hΔ0 hΔ2 ν hν n hn S href hX0 L hL
    hgapL hρ1 hN hN4 hq ha hprox
  have hopt : ∫ x, gGapHat ℬ e n S x ∂p ≤
      ∫ x, gGapHat ℬ e n S x ∂(G1C.pcomp ℬ e n S ν astar ρ) := hmin.2 _ hfeas
  obtain ⟨hpP, hpK, -⟩ := hmin.1
  obtain ⟨hνfin, hνB, -, -⟩ := hν
  haveI := hνfin
  have hνK : ν (Kset ℬ)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 (subset_convexHull ℝ ℬ)) hνB
  have hν'K : ν.restrict {astar}ᶜ (Kset ℬ)ᶜ = 0 :=
    le_antisymm ((Measure.restrict_apply_le _ _).trans (le_of_eq hνK)) zero_le
  -- continuity
  have hΔc : Continuous fun x : Fin d → ℝ => (x - astar) ⬝ᵥ θ :=
    (G2P.cont_dot θ).comp (continuous_id.sub continuous_const)
  have hhc : Continuous (gGapHat ℬ e n S) := by
    unfold gGapHat gZ
    exact continuous_const.min ((continuous_const.max ((G2P.cont_dot S).sub
      continuous_const)).div_const _)
  have hhat : ∀ x ∈ Kset ℬ, gGapHat ℬ e n S x = min 2 ((x - astar) ⬝ᵥ S / n) := by
    intro x hx
    unfold gGapHat gZ
    rw [href, ← sub_dotProduct, max_eq_right (hX0 x hx)]
  -- (1) `Δ ≤ L Δ̂` on `𝒦`
  have h1 : ∫ x, (x - astar) ⬝ᵥ θ ∂p ≤ L * ∫ x, gGapHat ℬ e n S x ∂p := by
    rw [← integral_const_mul]
    refine integral_mono_ae (T31.integrable_cpt hKc hpK hΔc)
      ((T31.integrable_cpt hKc hpK hhc).const_mul L) ?_
    filter_upwards [T31.ae_mem hpK] with x hx
    rw [hhat x hx]
    rcases le_total ((x - astar) ⬝ᵥ S / n) 2 with h | h
    · rw [min_eq_right h]; exact hgapL x hx
    · rw [min_eq_left h]; have := hΔ2 x hx; nlinarith
  -- (2) the comparison law
  set γ := (G1C.wc ν astar ρ univ).toReal with hγdef
  have hγ0 : 0 ≤ γ := ENNReal.toReal_nonneg
  have hγ1 : γ ≤ 1 := by
    have hw : γ = ρ * (ν.restrict {astar}ᶜ univ).toReal := by
      rw [hγdef, G1C.wc, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hρ0.le]
    have : (ν.restrict {astar}ᶜ univ).toReal ≤ (ν univ).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (Measure.restrict_apply_le _ _)
    have := mul_le_mul_of_nonneg_left this hρ0.le
    linarith
  have h2 := G1C.pcomp_int (e := e) (n := n) (S := S) hd hℬ hgen hspan hνK hρ0.le hγ1 hhc
  -- (3) `Δ̂ ≤ U Δ` on `𝒦`
  have hhatU : ∀ x ∈ Kset ℬ, gGapHat ℬ e n S x ≤ U * ((x - astar) ⬝ᵥ θ) := fun x hx => by
    rw [hhat x hx]; exact (min_le_right _ _).trans (hgapU x hx)
  have hhat0 : ∀ x, 0 ≤ gGapHat ℬ e n S x := fun x => by
    unfold gGapHat gZ
    exact le_min (by norm_num) (div_nonneg (le_max_left _ _) hn0.le)
  have h3 : ∫ x, gGapHat ℬ e n S x ∂q ≤ U * ∫ x, (x - astar) ⬝ᵥ θ ∂q := by
    rw [← integral_const_mul]
    refine integral_mono_ae (T31.integrable_cpt hKc hqK hhc)
      ((T31.integrable_cpt hKc hqK hΔc).const_mul U) ?_
    filter_upwards [T31.ae_mem hqK] with x hx using hhatU x hx
  -- (4) `⟨q, Δ⟩ ≤ 2 I / π*`
  set pa := (μ {astar}).toReal with hpadef
  have hpa : 0 < pa := ENNReal.toReal_pos ha.ne' (measure_ne_top _ _)
  set I := ∫ x in {astar}ᶜ, Real.exp (-((x - astar) ⬝ᵥ S) / (2 * β)) ∂μ with hIdef
  have h4 : ∫ x, (x - astar) ⬝ᵥ θ ∂q ≤ 2 * pa⁻¹ * I := by
    set g := ({astar}ᶜ : Set (Fin d → ℝ)).indicator (fun _ => (2 : ℝ)) with hgdef
    have hg0 : ∀ x, 0 ≤ g x := fun x => Set.indicator_nonneg (fun _ _ => by norm_num) x
    have hgi : Integrable g q := (integrable_const _).indicator (measurableSet_singleton _).compl
    have hA1 : ∫ x, (x - astar) ⬝ᵥ θ ∂q ≤ ∫ x, g x ∂q := by
      refine integral_mono_ae (T31.integrable_cpt hKc hqK hΔc) hgi ?_
      filter_upwards [T31.ae_mem hqK] with x hx
      by_cases hxa : x = astar
      · rw [hxa, sub_self, zero_dotProduct]; exact hg0 _
      · rw [hgdef, indicator_of_mem (show x ∈ ({astar}ᶜ : Set (Fin d → ℝ)) from hxa)]
        exact hΔ2 x hx
    have hA2 : ∫ x, g x ∂q ≤ pa⁻¹ * ∫ x, g x * Real.exp (-((x - astar) ⬝ᵥ S) / β) ∂μ :=
      G2P.gibbs_le hKc hμK hβ S ha hg0
    have hE2 : Continuous fun u : Fin d → ℝ => 2 * Real.exp (-((u - astar) ⬝ᵥ S) / (2 * β)) :=
      continuous_const.mul (((((G2P.cont_dot S).comp
        (continuous_id.sub continuous_const)).neg).div_const _).rexp)
    have hA3 : ∫ x, g x * Real.exp (-((x - astar) ⬝ᵥ S) / β) ∂μ ≤ 2 * I := by
      have hi2 : Integrable (({astar}ᶜ : Set (Fin d → ℝ)).indicator
          (fun u => 2 * Real.exp (-((u - astar) ⬝ᵥ S) / (2 * β)))) μ :=
        (T31.integrable_cpt hKc hμK hE2).indicator (measurableSet_singleton astar).compl
      calc ∫ x, g x * Real.exp (-((x - astar) ⬝ᵥ S) / β) ∂μ
          ≤ ∫ u, ({astar}ᶜ : Set (Fin d → ℝ)).indicator
              (fun u => 2 * Real.exp (-((u - astar) ⬝ᵥ S) / (2 * β))) u ∂μ := by
            refine G1P.int_le_of_le_ae hi2 (ae_of_all _ fun u =>
              Set.indicator_nonneg (fun _ _ => by positivity) u) ?_
            filter_upwards [T31.ae_mem hμK] with u hu
            by_cases hua : u = astar
            · rw [hgdef, indicator_of_notMem (show u ∉ ({astar}ᶜ : Set (Fin d → ℝ)) by simp [hua]),
                zero_mul, indicator_of_notMem (show u ∉ ({astar}ᶜ : Set (Fin d → ℝ)) by simp [hua])]
            · rw [hgdef, indicator_of_mem (show u ∈ ({astar}ᶜ : Set (Fin d → ℝ)) from hua),
                indicator_of_mem (show u ∈ ({astar}ᶜ : Set (Fin d → ℝ)) from hua)]
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
              have hXu := hX0 u hu
              have e1 : -((u - astar) ⬝ᵥ S) / β = -((u - astar) ⬝ᵥ S / (2 * β)) * 2 := by
                field_simp
              have e2 : -((u - astar) ⬝ᵥ S) / (2 * β) = -((u - astar) ⬝ᵥ S / (2 * β)) := by ring
              rw [e1, e2]
              have : 0 ≤ (u - astar) ⬝ᵥ S / (2 * β) := by positivity
              linarith
        _ = 2 * I := by
            rw [integral_indicator (measurableSet_singleton astar).compl, integral_const_mul]
    calc _ ≤ _ := hA1
      _ ≤ _ := hA2
      _ ≤ pa⁻¹ * (2 * I) := mul_le_mul_of_nonneg_left hA3 (by positivity)
      _ = 2 * pa⁻¹ * I := by ring
  -- (5) the allocation part
  have h5 : ∫ x, gGapHat ℬ e n S x ∂(ν.restrict {astar}ᶜ) ≤ U * ctrCost θ astar ν := by
    have hB1 : ∫ x, gGapHat ℬ e n S x ∂(ν.restrict {astar}ᶜ) ≤
        ∫ x, U * ((x - astar) ⬝ᵥ θ) ∂(ν.restrict {astar}ᶜ) := by
      refine integral_mono_ae (T31.integrable_cpt hKc hν'K hhc)
        ((T31.integrable_cpt hKc hν'K hΔc).const_mul U) ?_
      filter_upwards [T31.ae_mem hν'K] with x hx using hhatU x hx
    have hB2 : ∫ x, (x - astar) ⬝ᵥ θ ∂(ν.restrict {astar}ᶜ) ≤ ∫ x, (x - astar) ⬝ᵥ θ ∂ν := by
      refine setIntegral_le_integral (T31.integrable_cpt hKc hνK hΔc) ?_
      filter_upwards [T31.ae_mem hνK] with x hx using hΔ0 x hx
    rw [integral_const_mul] at hB1
    unfold ctrCost
    exact hB1.trans (mul_le_mul_of_nonneg_left hB2 hU0)
  have h6 : 0 ≤ ∫ x, (x - astar) ⬝ᵥ θ ∂q := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [T31.ae_mem hqK] with x hx using hΔ0 x hx
  have h7 : 0 ≤ ∫ x, gGapHat ℬ e n S x ∂q := integral_nonneg hhat0
  -- assemble
  have hpc : ∫ x, gGapHat ℬ e n S x ∂(G1C.pcomp ℬ e n S ν astar ρ) ≤
      U * (2 * pa⁻¹ * I) + ρ * (U * ctrCost θ astar ν) := by
    rw [h2]
    have : (1 - γ) * ∫ x, gGapHat ℬ e n S x ∂q ≤ ∫ x, gGapHat ℬ e n S x ∂q := by
      have := mul_le_mul_of_nonneg_right (show 1 - γ ≤ 1 by linarith) h7
      linarith
    have h8 : ∫ x, gGapHat ℬ e n S x ∂q ≤ U * (2 * pa⁻¹ * I) :=
      h3.trans (mul_le_mul_of_nonneg_left h4 hU0)
    have h9 := mul_le_mul_of_nonneg_left h5 hρ0.le
    linarith
  have hfin : ∫ x, (x - astar) ⬝ᵥ θ ∂p ≤ L * (U * (2 * pa⁻¹ * I) + ρ * (U * ctrCost θ astar ν)) :=
    h1.trans (mul_le_mul_of_nonneg_left (hopt.trans hpc) (by linarith))
  have e1 : L * (U * (2 * pa⁻¹ * I) + ρ * (U * ctrCost θ astar ν)) =
      2 * pa⁻¹ * I * (L * U) + 16 * B * ctrCost θ astar ν / n * (L ^ 3 * U) := by
    rw [hρdef]; field_simp
  rw [e1] at hfin
  linarith

end G1E

-- ===== G1/G5Explo =====

/-! ### Lemma G.5: the exploration contribution under the fixed loss vector -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix
open scoped ENNReal

namespace G1E

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}

lemma int_aff {K : Set (Fin d → ℝ)} (hK : IsCompact K) (ν : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ν] (hνK : ν Kᶜ = 0) (a g : Fin d → ℝ) :
    ∫ x, (x - a) ⬝ᵥ g ∂ν = (G2P.mean ν - a) ⬝ᵥ g := by
  simp only [sub_dotProduct]
  rw [integral_sub (T31.integrable_cpt hK hνK (G2P.cont_dot g)) (integrable_const _),
    integral_const, ← G2P.mean_dot hK hνK g]
  simp

/-- the size conditions on the comparison event (pure arithmetic) -/
lemma sizes {d B N aν sR nR β L : ℝ} (hd1 : 1 ≤ d) (hB : 1 ≤ B) (hN0 : 0 ≤ N)
    (haν : aν = 68 * B * N / d + 1) (hsR2 : sR ^ 2 = nR) (hsR1 : 1 ≤ sR) (hsd : d ≤ sR)
    (hβ : β ≤ 17 * sR) (hβ0 : 0 < β) (hL : 1 ≤ L) (hz1 : L ^ 2 ≤ sR / aν)
    (hz2 : L ^ 2 ≤ nR / (16 * B)) :
    16 * B * L ^ 2 / nR ≤ 1 ∧ 16 * B * L ^ 2 / nR * N ≤ 4 * d / β ∧
      16 * B * L ^ 2 / nR * N ≤ 1 / 4 := by
  have hnR0 : 0 < nR := by rw [← hsR2]; positivity
  have haν1 : 1 ≤ aν := by
    have : 0 ≤ 68 * B * N / d := by positivity
    linarith
  have hL2a : L ^ 2 * aν ≤ sR := by rwa [le_div_iff₀ (by linarith)] at hz1
  have haνd : 272 * B * N ≤ 4 * d * aν := by
    rw [haν]
    have e : 4 * d * (68 * B * N / d + 1) = 272 * B * N + 4 * d := by field_simp; ring
    rw [e]; linarith
  have h1 : 272 * B * N * L ^ 2 ≤ 4 * d * aν * L ^ 2 :=
    mul_le_mul_of_nonneg_right haνd (by positivity)
  have h2 : 4 * d * aν * L ^ 2 ≤ 4 * d * sR := by
    have := mul_le_mul_of_nonneg_left hL2a (show (0 : ℝ) ≤ 4 * d by positivity)
    linarith
  have hkey : 16 * B * L ^ 2 / nR * N * sR ≤ 4 * d / 17 := by
    rw [← hsR2]
    have e : 16 * B * L ^ 2 / sR ^ 2 * N * sR = 16 * B * N * L ^ 2 / sR := by
      field_simp
    rw [e, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hρN : 16 * B * L ^ 2 / nR * N ≤ 4 * d / 17 / sR := by
    rw [le_div_iff₀ (by linarith)]; exact hkey
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_one hnR0]
    rw [le_div_iff₀ (by positivity)] at hz2; linarith
  · refine hρN.trans ?_
    rw [div_div, div_le_div_iff₀ (by positivity) hβ0]
    nlinarith
  · refine hρN.trans ?_
    rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

/-- the atom-mass and proxy-budget conditions (pure arithmetic) -/
lemma laplace_sizes {A' pa I nR d B L : ℝ} (hA' : 0 ≤ A') (hpa : 0 < pa) (hI0 : 0 ≤ I)
    (hnR1 : 1 ≤ nR) (hd1 : 1 ≤ d) (hB : 1 ≤ B) (hL : 1 ≤ L) (hI : I ≤ A' / nR ^ 3)
    (hnA : 4 * A' / pa ≤ nR) (hnP : A' / (8 * d * B ^ 2 * pa) ≤ nR) :
    pa⁻¹ * I ≤ 1 / 4 ∧ 64 * I ≤ 2 * d * (16 * B * L ^ 2 / nR) ^ 2 * pa := by
  have hnR0 : 0 < nR := by linarith
  have hn3 : nR ≤ nR ^ 3 := by
    have h1 : 1 ≤ nR ^ 2 := one_le_pow₀ hnR1
    calc nR = nR * 1 := (mul_one _).symm
      _ ≤ nR * nR ^ 2 := mul_le_mul_of_nonneg_left h1 hnR0.le
      _ = nR ^ 3 := by ring
  constructor
  · rw [inv_mul_le_iff₀ hpa]
    have h1 : A' / nR ^ 3 ≤ A' / nR := div_le_div_of_nonneg_left hA' hnR0 hn3
    have h2 : A' / nR ≤ pa / 4 := by
      rw [div_le_div_iff₀ hnR0 (by norm_num)]
      rw [div_le_iff₀ hpa] at hnA; linarith
    linarith
  · have hL2 : 1 ≤ L ^ 2 := by nlinarith
    have h1 : 2 * d * (16 * B / nR) ^ 2 * pa ≤ 2 * d * (16 * B * L ^ 2 / nR) ^ 2 * pa := by
      have : 16 * B / nR ≤ 16 * B * L ^ 2 / nR := by
        apply div_le_div_of_nonneg_right _ hnR0.le; nlinarith
      have h0 : 0 ≤ 16 * B / nR := by positivity
      have := pow_le_pow_left₀ h0 this 2
      have hc : 0 ≤ 2 * d := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hc) hpa.le
    have h2 : 64 * (A' / nR ^ 3) ≤ 2 * d * (16 * B / nR) ^ 2 * pa := by
      rw [div_le_iff₀ (by positivity)] at hnP
      have e1 : 64 * (A' / nR ^ 3) = 64 * A' / nR ^ 3 := by ring
      have e2 : 2 * d * (16 * B / nR) ^ 2 * pa = 512 * d * B ^ 2 * pa / nR ^ 2 := by
        field_simp; ring
      rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
      have : 64 * A' * nR ^ 2 ≤ 512 * d * B ^ 2 * pa * nR * nR ^ 2 := by
        have := mul_le_mul_of_nonneg_right hnP (show (0 : ℝ) ≤ 64 * nR ^ 2 by positivity)
        nlinarith
      nlinarith
    linarith

/-- the exponential weights keep mass `≥ 1 − I/π*` on `a*` -/
lemma q_atom (hd : 1 ≤ d) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) {astar : Fin d → ℝ} (ha : 0 < refMu ℬ e {astar})
    {n : ℕ} {S : Fin d → ℝ} (hX0 : ∀ a ∈ Kset ℬ, 0 ≤ (a - astar) ⬝ᵥ S) :
    1 - ((refMu ℬ e {astar}).toReal)⁻¹ * ∫ x in {astar}ᶜ,
      Real.exp (-((x - astar) ⬝ᵥ S) / (2 * gbeta d n)) ∂(refMu ℬ e) ≤
      (gq ℬ e n S {astar}).toReal := by
  have hne := G2R.B_nonempty hd hgen hspan
  haveI := G2F.refMu_prob hℬ hne e
  have hμK := G2F.refMu_supp hℬ hne e
  have hKc := G2F.Kc hℬ
  set μ := refMu ℬ e with hμdef
  set β := gbeta d n with hβdef
  have hβ : 0 < β := G2R.gbeta_pos hd n
  set q := gq ℬ e n S with hqdef
  haveI hqP : IsProbabilityMeasure q := G2P.gibbs_prob hKc hμK β S
  set g := ({astar}ᶜ : Set (Fin d → ℝ)).indicator (fun _ => (1 : ℝ)) with hgdef
  have hg0 : ∀ x, 0 ≤ g x := fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have h1 : ∫ x, g x ∂q ≤ ((μ {astar}).toReal)⁻¹ * ∫ x, g x *
      Real.exp (-((x - astar) ⬝ᵥ S) / β) ∂μ := G2P.gibbs_le hKc hμK hβ S ha hg0
  have hE2 : Continuous fun u : Fin d → ℝ => Real.exp (-((u - astar) ⬝ᵥ S) / (2 * β)) :=
    ((((G2P.cont_dot S).comp (continuous_id.sub continuous_const)).neg).div_const _).rexp
  have h2 : ∫ x, g x * Real.exp (-((x - astar) ⬝ᵥ S) / β) ∂μ ≤
      ∫ x in {astar}ᶜ, Real.exp (-((x - astar) ⬝ᵥ S) / (2 * β)) ∂μ := by
    rw [← integral_indicator (measurableSet_singleton astar).compl]
    refine G1P.int_le_of_le_ae ((T31.integrable_cpt hKc hμK hE2).indicator
      (measurableSet_singleton astar).compl) (ae_of_all _ fun u =>
        Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) u) ?_
    filter_upwards [T31.ae_mem hμK] with u hu
    by_cases hua : u = astar
    · rw [hgdef, indicator_of_notMem (show u ∉ ({astar}ᶜ : Set (Fin d → ℝ)) by simp [hua]),
        zero_mul, indicator_of_notMem (show u ∉ ({astar}ᶜ : Set (Fin d → ℝ)) by simp [hua])]
    · rw [hgdef, indicator_of_mem (show u ∈ ({astar}ᶜ : Set (Fin d → ℝ)) from hua),
        indicator_of_mem (show u ∈ ({astar}ᶜ : Set (Fin d → ℝ)) from hua), one_mul]
      refine Real.exp_le_exp.2 ?_
      have hXu := hX0 u hu
      have e1 : -((u - astar) ⬝ᵥ S) / β = -((u - astar) ⬝ᵥ S / (2 * β)) * 2 := by field_simp
      have e2 : -((u - astar) ⬝ᵥ S) / (2 * β) = -((u - astar) ⬝ᵥ S / (2 * β)) := by ring
      rw [e1, e2]
      have : 0 ≤ (u - astar) ⬝ᵥ S / (2 * β) := by positivity
      linarith
  have h3 : ∫ x, g x ∂q = (q {astar}ᶜ).toReal := by
    show ∫ x, ({astar}ᶜ : Set (Fin d → ℝ)).indicator (fun _ => (1 : ℝ)) x ∂q = _
    rw [integral_indicator (measurableSet_singleton astar).compl, setIntegral_const,
      smul_eq_mul, mul_one, measureReal_def]
  have h4 : (q {astar}).toReal + (q {astar}ᶜ).toReal = 1 := by
    rw [← measureReal_def, ← measureReal_def,
      measureReal_add_measureReal_compl (measurableSet_singleton astar), probReal_univ]
  have hpa : 0 ≤ ((μ {astar}).toReal)⁻¹ := by positivity
  have h5 := mul_le_mul_of_nonneg_left h2 hpa
  linarith

set_option maxHeartbeats 3200000 in
theorem explo (hd : 1 ≤ d) (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (hk : 1 ≤ kdim ℬ)
    (he : Function.Surjective e) (θ astar : Fin d → ℝ) (hθ : setNorm 𝒜 θ ≤ 1)
    (hastar : astar ∈ 𝒜) (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ)
    (hsharp : IsSharp 𝒜 θ astar) :
    ∃ J : ℝ, ∀ ν : Measure (Fin d → ℝ), IsCtrAlloc ℬ θ astar ν →
      ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (T : ℕ) (C : ℝ) (R : GRun d Ω), 1 ≤ T → 0 ≤ C →
        IsGIAFTRLRun P 𝒜 ℬ e T R → IsCorruptedG P 𝒜 θ C T R →
        exploI3 P ℬ e T R θ astar ≤
          16 * gB d * 64 ^ 4 * ctrCost θ astar ν * Real.log (Real.exp 1 * T) + M +
            J * Real.sqrt C * Real.log (Real.exp 1 + C) := by
  obtain ⟨A, hA⟩ := lemma_G_3 hd 𝒜 ℬ e h𝒜 hℬ hgen hball hspan hk he θ astar hθ hastar huniq
    hsharp
  obtain ⟨W, hW⟩ := lemma_G_26 hd 𝒜 ℬ e h𝒜 hℬ hgen hball hspan hk he θ astar hθ hastar huniq
    hsharp
  obtain ⟨m, hm, hcand⟩ := lemma_G_12 𝒜 ℬ e h𝒜 hℬ hgen hball hspan he θ astar hastar huniq
    hsharp
  obtain ⟨Tr, hTr⟩ := lemma_G_ref_id hd 𝒜 ℬ e h𝒜 hℬ hgen hball hspan he θ astar hastar huniq hsharp
  have hatom := G1P.atom_pos hm hcand
  have hne := G2R.B_nonempty hd hgen hspan
  haveI := G2F.refMu_prob hℬ hne e
  have hμK := G2F.refMu_supp hℬ hne e
  have hKc := G2F.Kc hℬ
  have hΔ0 := G1P.gap_nonneg hgen huniq
  have haK : astar ∈ Kset ℬ := hcand ▸ subset_convexHull ℝ ℬ (G2L.cand_mem hℬ hne e m)
  have hΔ2 : ∀ a ∈ Kset ℬ, (a - astar) ⬝ᵥ θ ≤ 2 := by
    intro a ha
    have h1 := abs_le.1 (G2R.abs_dot_le_one h𝒜 hgen hθ ha)
    have h2 := abs_le.1 (G2R.abs_dot_le_one h𝒜 hgen hθ haK)
    rw [sub_dotProduct]; linarith
  obtain ⟨b, hb, hba⟩ := G1L.exists_ne hk astar
  have hbK : b ∈ Kset ℬ := subset_convexHull ℝ ℬ hb
  have hΔb : 0 < (b - astar) ⬝ᵥ θ := by
    have := huniq b (hgen.1 hb) hba; rw [sub_dotProduct]; linarith
  set pa := (refMu ℬ e {astar}).toReal with hpadef
  have hpa : 0 < pa := ENNReal.toReal_pos hatom.ne' (measure_ne_top _ _)
  set A' := max A 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  set B := gB d with hBdef
  have hB1 : 1 ≤ B := by
    rw [hBdef, gB]
    have : (1 : ℝ) ≤ d + 1 := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
    nlinarith [show (1 : ℝ) ≤ 2 ^ 36 by norm_num]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨8 * d * W, fun ν hν => ?_⟩
  haveI hνfin : IsFiniteMeasure ν := hν.1
  have hνK : ν (Kset ℬ)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 (subset_convexHull ℝ ℬ)) hν.2.1
  set N := (ν univ).toReal with hNdef
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  set aν := 68 * B * N / d + 1 with haνdef
  have haν : 1 ≤ aν := by have : 0 ≤ 68 * B * N / d := by positivity
                          linarith
  set c := ctrCost θ astar ν with hcdef
  have hc0 : 0 ≤ c := by
    rw [hcdef, ctrCost]
    refine integral_nonneg_of_ae ?_
    filter_upwards [T31.ae_mem hνK] with x hx using hΔ0 x hx
  set T1 : ℕ := Tr + d ^ 2 + ⌈4 * A' / pa⌉₊ + ⌈A' / (8 * d * B ^ 2 * pa)⌉₊ + 1 with hT1def
  refine ⟨8 * d * T1 + 4 * 64 ^ 2 * A' / pa + 8 * d * W + 48 * d * 64 ^ 6 * aν ^ 2 +
    16 * d * 64 ^ 6 * (16 * B) ^ 2, ?_⟩
  intro Ω _ P _ T C R hT hC hR hcor
  obtain ⟨G, L, U, hGm, hLm, hUm, hGood, hoff, hmom, hfail⟩ := hW P T C R hT hC hR hcor
  -- nonnegativity and the product lower bound
  have hLU0 : ∀ t < T, ∀ ω, 0 ≤ L t ω ∧ 0 ≤ U t ω := by
    intro t ht ω
    by_cases hω : ω ∈ G t
    · obtain ⟨hL1, hU0, -⟩ := hGood t ht ω hω; exact ⟨by linarith, hU0⟩
    · obtain ⟨h1, h2⟩ := hoff t ht ω hω; rw [h1, h2]; exact ⟨le_rfl, le_rfl⟩
  have hLU1 : ∀ t < T, ∀ ω ∈ G t, 1 ≤ L t ω * U t ω := by
    intro t ht ω hω
    obtain ⟨hL1, hU0, hgap⟩ := hGood t ht ω hω
    obtain ⟨-, h1, h2⟩ := hgap b hbK
    have h3 : (b - astar) ⬝ᵥ θ ≤ L t ω * (U t ω * ((b - astar) ⬝ᵥ θ)) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
    by_contra hlt
    push Not at hlt
    have : L t ω * (U t ω * ((b - astar) ⬝ᵥ θ)) < (b - astar) ⬝ᵥ θ := by
      rw [← mul_assoc]; nlinarith
    linarith
  have hmomr : ∀ t < T, ∀ r ∈ ({1, 3, 5} : Finset ℕ), Integrable (fun ω => L t ω ^ r * U t ω) P ∧
      ∫ ω, L t ω ^ r * U t ω ∂P ≤ 64 ^ (r + 1) := hmom
  -- the per-round envelope
  set E : ℕ → Ω → ℝ := fun t ω => ∫ x, (x - astar) ⬝ᵥ θ ∂(R.p t ω) -
    ∫ x, (x - astar) ⬝ᵥ θ ∂(R.qw ℬ e t ω) with hEdef
  have hEbd : ∀ t < T, ∀ ω, E t ω ≤ 8 * d * (Real.sqrt ((t : ℝ) + 1))⁻¹ := by
    intro t ht ω
    haveI := G2R.p_prob hR ht ω
    haveI : IsProbabilityMeasure (R.qw ℬ e t ω) :=
      G2P.gibbs_prob hKc hμK (gbeta d (t + 1)) (R.cumEst t ω)
    have h1 := G2X.explo hd h𝒜 hℬ hgen hspan (G2R.feas hR ht ω) hθ
    simp only [hEdef]
    rw [int_aff hKc _ (G2R.p_supp hR ht ω), int_aff hKc (R.qw ℬ e t ω)
      (G2P.gibbs_supp hμK (gbeta d (t + 1)) (R.cumEst t ω))]
    have e1 : (G2P.mean (R.p t ω) - astar) ⬝ᵥ θ - (G2P.mean (R.qw ℬ e t ω) - astar) ⬝ᵥ θ =
        (G2P.mean (R.p t ω) - G2P.mean (gq ℬ e (t + 1) (R.cumEst t ω))) ⬝ᵥ θ := by
      have : G2P.mean (R.qw ℬ e t ω) = G2P.mean (gq ℬ e (t + 1) (R.cumEst t ω)) := rfl
      rw [this]; simp only [sub_dotProduct]; ring
    rw [e1]
    refine h1.trans ?_
    have hsq : 0 < Real.sqrt ((t : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have hβge : Real.sqrt ((t : ℝ) + 1) ≤ gbeta d (t + 1) := by
      rw [gbeta]; push_cast; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hsq hβge) (by positivity)
  -- the remainder sequence
  set Rt : ℕ → ℝ := fun t =>
    8 * d * (if t + 1 < T1 then 1 else 0) + 2 * A' / pa * 64 ^ 2 * (((t : ℝ) + 1) ^ 3)⁻¹ +
    16 * B * c * 64 ^ 4 * ((t : ℝ) + 1)⁻¹ +
    8 * d * ((Real.sqrt ((t : ℝ) + 1))⁻¹ * (P (G t)ᶜ).toReal) +
    8 * d * 64 ^ 6 * aν ^ 2 * ((Real.sqrt ((t : ℝ) + 1))⁻¹ * ((t : ℝ) + 1)⁻¹) +
    8 * d * 64 ^ 6 * (16 * B) ^ 2 * (((t : ℝ) + 1) ^ 2)⁻¹ with hRt
  have hround : ∀ t < T, ∫ ω, E t ω ∂P ≤ Rt t := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have hsq : 0 < Real.sqrt ((t : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have hsq1 := G1P.inv_sqrt_le_one t
    have hrest : 0 ≤ 2 * A' / pa * 64 ^ 2 * (((t : ℝ) + 1) ^ 3)⁻¹ +
        16 * B * c * 64 ^ 4 * ((t : ℝ) + 1)⁻¹ +
        8 * d * ((Real.sqrt ((t : ℝ) + 1))⁻¹ * (P (G t)ᶜ).toReal) +
        8 * d * 64 ^ 6 * aν ^ 2 * ((Real.sqrt ((t : ℝ) + 1))⁻¹ * ((t : ℝ) + 1)⁻¹) +
        8 * d * 64 ^ 6 * (16 * B) ^ 2 * (((t : ℝ) + 1) ^ 2)⁻¹ := by positivity
    by_cases hTt : t + 1 < T1
    · have h1 : ∫ ω, E t ω ∂P ≤ ∫ _ω, 8 * (d : ℝ) ∂P :=
        G1P.int_le_of_le (integrable_const _) (fun _ => by positivity) fun ω =>
          (hEbd t ht ω).trans (by
            have := mul_le_mul_of_nonneg_left hsq1 (show (0 : ℝ) ≤ 8 * d by positivity)
            linarith)
      rw [integral_const, probReal_univ, one_smul] at h1
      have : Rt t = 8 * d * 1 + (2 * A' / pa * 64 ^ 2 * (((t : ℝ) + 1) ^ 3)⁻¹ +
        16 * B * c * 64 ^ 4 * ((t : ℝ) + 1)⁻¹ +
        8 * d * ((Real.sqrt ((t : ℝ) + 1))⁻¹ * (P (G t)ᶜ).toReal) +
        8 * d * 64 ^ 6 * aν ^ 2 * ((Real.sqrt ((t : ℝ) + 1))⁻¹ * ((t : ℝ) + 1)⁻¹) +
        8 * d * 64 ^ 6 * (16 * B) ^ 2 * (((t : ℝ) + 1) ^ 2)⁻¹) := by
        rw [hRt]; simp only [if_pos hTt]; ring
      rw [this]; linarith
    · push Not at hTt
      have hcast : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
      set nR := (t : ℝ) + 1 with hnR
      have hnR1 : 1 ≤ nR := by linarith
      have hnR0 : 0 < nR := by linarith
      set sR := Real.sqrt nR with hsR
      have hsR2 : sR ^ 2 = nR := Real.sq_sqrt (by linarith)
      have hsR1 : 1 ≤ sR := Real.one_le_sqrt.2 hnR1
      -- the round threshold
      have hT1R : (T1 : ℝ) ≤ nR := by
        have : (T1 : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by exact_mod_cast hTt
        rw [hcast] at this; exact this
      have hT1eq : (T1 : ℝ) = (Tr : ℝ) + (d : ℝ) ^ 2 + (⌈4 * A' / pa⌉₊ : ℝ) +
          (⌈A' / (8 * d * B ^ 2 * pa)⌉₊ : ℝ) + 1 := by rw [hT1def]; push_cast; ring
      have hc1 := Nat.le_ceil (4 * A' / pa)
      have hc2 := Nat.le_ceil (A' / (8 * d * B ^ 2 * pa))
      have hTr0 : (0 : ℝ) ≤ Tr := Nat.cast_nonneg _
      have hcc1 : (0 : ℝ) ≤ (⌈4 * A' / pa⌉₊ : ℝ) := Nat.cast_nonneg _
      have hcc2 : (0 : ℝ) ≤ (⌈A' / (8 * d * B ^ 2 * pa)⌉₊ : ℝ) := Nat.cast_nonneg _
      have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
      have hnd : (d : ℝ) ^ 2 ≤ nR := by linarith
      have hnA : 4 * A' / pa ≤ nR := by linarith
      have hnP : A' / (8 * d * B ^ 2 * pa) ≤ nR := by linarith
      have hnTr : Tr ≤ t + 1 := by
        have : Tr ≤ T1 := by rw [hT1def]; omega
        omega
      have hsd : (d : ℝ) ≤ sR := by
        rw [hsR]; exact Real.le_sqrt_of_sq_le hnd
      have hβ17 : gbeta d (t + 1) ≤ 17 * sR := by
        rw [gbeta, hcast, ← hsR]; linarith
      have hβ0 : 0 < gbeta d (t + 1) := G2R.gbeta_pos hd (t + 1)
      -- the size conditions, for every `L` on the comparison event
      have hsizes : ∀ L : ℝ, 1 ≤ L → L ^ 2 ≤ sR / aν → L ^ 2 ≤ nR / (16 * B) →
          16 * gB d * L ^ 2 / ((t + 1 : ℕ) : ℝ) ≤ 1 ∧
          16 * gB d * L ^ 2 / ((t + 1 : ℕ) : ℝ) * N ≤ gGam d (t + 1) ∧
          16 * gB d * L ^ 2 / ((t + 1 : ℕ) : ℝ) * N ≤ 1 / 4 := by
        intro L hL hz1 hz2
        rw [hcast, ← hBdef, gGam]
        exact sizes hd1 hB1 hN0 haνdef hsR2 hsR1 hsd hβ17 hβ0 hL hz1 hz2
      -- the comparison-round envelope
      set k := 8 * (d : ℝ) * sR⁻¹ with hkdef
      have hk0 : 0 ≤ k := by positivity
      set z1 := sR / aν with hz1def
      set z2 := nR / (16 * B) with hz2def
      have hz10 : 0 < z1 := by positivity
      have hz20 : 0 < z2 := by positivity
      set c1 := 2 * A' / pa * (nR ^ 3)⁻¹ with hc1def
      set c2 := 16 * B * c / nR with hc2def
      have hc10 : 0 ≤ c1 := by positivity
      have hc20 : 0 ≤ c2 := by positivity
      obtain ⟨hi1, hm1⟩ := hmomr t ht 1 (by simp)
      obtain ⟨hi3, hm3⟩ := hmomr t ht 3 (by simp)
      obtain ⟨hi5, hm5⟩ := hmomr t ht 5 (by simp)
      simp only [pow_one] at hi1 hm1
      have hiG : Integrable ((G t)ᶜ.indicator (1 : Ω → ℝ)) P :=
        (integrable_const (1 : ℝ)).indicator (hGm t).compl
      set g : Ω → ℝ := fun ω => c1 * (L t ω * U t ω) + c2 * (L t ω ^ 3 * U t ω) +
        k * ((G t)ᶜ.indicator (1 : Ω → ℝ) ω + L t ω ^ 5 * U t ω / z1 ^ 2 +
          L t ω ^ 5 * U t ω / z2 ^ 2) with hgdef
      have hgi : Integrable g P :=
        ((hi1.const_mul c1).add (hi3.const_mul c2)).add
          (((hiG.add (hi5.div_const _)).add (hi5.div_const _)).const_mul k)
      have hg0 : ∀ ω, 0 ≤ g ω := by
        intro ω
        obtain ⟨hL0, hU0⟩ := hLU0 t ht ω
        have : 0 ≤ (G t)ᶜ.indicator (1 : Ω → ℝ) ω :=
          Set.indicator_nonneg (fun _ _ => zero_le_one) ω
        simp only [hgdef]; positivity
      have hEg : ∀ ω, E t ω ≤ g ω := by
        intro ω
        obtain ⟨hL0, hU0⟩ := hLU0 t ht ω
        have hEk : E t ω ≤ k := by
          have := hEbd t ht ω; rw [← hnR, ← hsR] at this; rw [hkdef]; exact this
        have hind0 : 0 ≤ (G t)ᶜ.indicator (1 : Ω → ℝ) ω :=
          Set.indicator_nonneg (fun _ _ => zero_le_one) ω
        have hA1 : 0 ≤ c1 * (L t ω * U t ω) := by positivity
        have hA3 : 0 ≤ c2 * (L t ω ^ 3 * U t ω) := by positivity
        have hA5 : 0 ≤ L t ω ^ 5 * U t ω / z1 ^ 2 := by positivity
        have hA6 : 0 ≤ L t ω ^ 5 * U t ω / z2 ^ 2 := by positivity
        -- tail rounds: `1 ≤ L⁵U/z²`
        have htail : ∀ z : ℝ, 0 < z → ω ∈ G t → z < L t ω ^ 2 → 1 ≤ L t ω ^ 5 * U t ω / z ^ 2 := by
          intro z hz hω hzL
          have hLU := hLU1 t ht ω hω
          rw [le_div_iff₀ (by positivity), one_mul]
          have h1 : z ^ 2 ≤ (L t ω ^ 2) ^ 2 := pow_le_pow_left₀ hz.le hzL.le 2
          have h2 : (L t ω ^ 2) ^ 2 ≤ L t ω ^ 5 * U t ω := by
            have : (L t ω ^ 2) ^ 2 * 1 ≤ (L t ω ^ 2) ^ 2 * (L t ω * U t ω) :=
              mul_le_mul_of_nonneg_left hLU (by positivity)
            calc (L t ω ^ 2) ^ 2 = (L t ω ^ 2) ^ 2 * 1 := (mul_one _).symm
              _ ≤ _ := this
              _ = L t ω ^ 5 * U t ω := by ring
          linarith
        by_cases hω : ω ∈ G t
        · obtain ⟨hL1, hU0', hgap⟩ := hGood t ht ω hω
          by_cases hz1 : L t ω ^ 2 ≤ z1
          · by_cases hz2 : L t ω ^ 2 ≤ z2
            · -- the comparison round
              have hLap : ∀ a ∈ Kset ℬ, 4 * ((t + 1 : ℕ) : ℝ) ^ ((7 : ℝ) / 8) *
                  ((a - astar) ⬝ᵥ θ) ≤ (a - astar) ⬝ᵥ R.cumEst t ω := fun a ha => (hgap a ha).1
              have href := hTr (t + 1) (R.cumEst t ω) hnTr hLap
              have hX0 : ∀ a ∈ Kset ℬ, 0 ≤ (a - astar) ⬝ᵥ R.cumEst t ω := fun a ha =>
                le_trans (by have := hΔ0 a ha; positivity) (hLap a ha)
              have hIb := hA (t + 1) (R.cumEst t ω) (by omega) hLap
              rw [hcast] at hIb
              set I := ∫ x in {astar}ᶜ, Real.exp (-((x - astar) ⬝ᵥ R.cumEst t ω) /
                (2 * gbeta d (t + 1))) ∂(refMu ℬ e) with hIdef
              have hI0 : 0 ≤ I := integral_nonneg fun _ => (Real.exp_pos _).le
              have hIA : I ≤ A' / nR ^ 3 :=
                hIb.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
              obtain ⟨hqa, hpx⟩ := laplace_sizes hA'0 hpa hI0 hnR1 hd1 hB1 hL1 hIA hnA hnP
              obtain ⟨hs1, hs2, hs3⟩ := hsizes _ hL1 hz1 hz2
              have hq34 : 3 / 4 ≤ (gq ℬ e (t + 1) (R.cumEst t ω) {astar}).toReal := by
                have := q_atom (n := t + 1) hd hℬ hgen hspan hatom hX0
                rw [← hpadef] at this
                linarith
              have hprox : 64 * I ≤ 2 * d * (16 * gB d * L t ω ^ 2 / ((t + 1 : ℕ) : ℝ)) ^ 2 *
                  (refMu ℬ e {astar}).toReal := by
                rw [hcast, ← hBdef, ← hpadef]; exact hpx
              have hgapL' : ∀ a ∈ Kset ℬ, (a - astar) ⬝ᵥ θ ≤
                  L t ω * ((a - astar) ⬝ᵥ R.cumEst t ω / ((t + 1 : ℕ) : ℝ)) := by
                intro a ha; rw [hcast]; exact (hgap a ha).2.1
              have hgapU' : ∀ a ∈ Kset ℬ, (a - astar) ⬝ᵥ R.cumEst t ω / ((t + 1 : ℕ) : ℝ) ≤
                  U t ω * ((a - astar) ⬝ᵥ θ) := by
                intro a ha; rw [hcast]; exact (hgap a ha).2.2
              have h := explo_good hd hℬ hgen hspan haK hΔ0 hΔ2 hν (by omega : 1 ≤ t + 1) href
                hX0 hL1 hU0' hgapL' hgapU' hs1 hs2 hs3 hq34 hatom hprox ((hR t ht).2.1.2 ω)
              have hE' : E t ω ≤ 2 * ((refMu ℬ e {astar}).toReal)⁻¹ * I * (L t ω * U t ω) +
                  16 * gB d * ctrCost θ astar ν / ((t + 1 : ℕ) : ℝ) * (L t ω ^ 3 * U t ω) := h
              rw [hcast, ← hBdef, ← hpadef, ← hcdef] at hE'
              have hLU0' : 0 ≤ L t ω * U t ω := mul_nonneg hL0 hU0
              have hc1' : 2 * pa⁻¹ * I * (L t ω * U t ω) ≤ c1 * (L t ω * U t ω) := by
                refine mul_le_mul_of_nonneg_right ?_ hLU0'
                rw [hc1def]
                have : 2 * pa⁻¹ * I ≤ 2 * pa⁻¹ * (A' / nR ^ 3) :=
                  mul_le_mul_of_nonneg_left hIA (by positivity)
                refine this.trans (le_of_eq ?_)
                field_simp
              have hc2' : 16 * B * c / nR * (L t ω ^ 3 * U t ω) = c2 * (L t ω ^ 3 * U t ω) := by
                rw [hc2def]
              have := mul_nonneg hk0 (add_nonneg (add_nonneg hind0 hA5) hA6)
              simp only [hgdef]
              linarith
            · push Not at hz2
              have h1 := htail z2 hz20 hω hz2
              have h2 : k ≤ k * (L t ω ^ 5 * U t ω / z2 ^ 2) := le_mul_of_one_le_right hk0 h1
              have h3 : k * (L t ω ^ 5 * U t ω / z2 ^ 2) ≤
                  k * ((G t)ᶜ.indicator (1 : Ω → ℝ) ω + L t ω ^ 5 * U t ω / z1 ^ 2 +
                    L t ω ^ 5 * U t ω / z2 ^ 2) :=
                mul_le_mul_of_nonneg_left (by linarith) hk0
              simp only [hgdef]
              linarith
          · push Not at hz1
            have h1 := htail z1 hz10 hω hz1
            have h2 : k ≤ k * (L t ω ^ 5 * U t ω / z1 ^ 2) := le_mul_of_one_le_right hk0 h1
            have h3 : k * (L t ω ^ 5 * U t ω / z1 ^ 2) ≤
                k * ((G t)ᶜ.indicator (1 : Ω → ℝ) ω + L t ω ^ 5 * U t ω / z1 ^ 2 +
                  L t ω ^ 5 * U t ω / z2 ^ 2) :=
              mul_le_mul_of_nonneg_left (by linarith) hk0
            simp only [hgdef]
            linarith
        · have h1 : (G t)ᶜ.indicator (1 : Ω → ℝ) ω = 1 := by
            rw [indicator_of_mem (show ω ∈ (G t)ᶜ from hω), Pi.one_apply]
          have h3 : k * 1 ≤ k * ((G t)ᶜ.indicator (1 : Ω → ℝ) ω + L t ω ^ 5 * U t ω / z1 ^ 2 +
              L t ω ^ 5 * U t ω / z2 ^ 2) :=
            mul_le_mul_of_nonneg_left (by linarith) hk0
          simp only [hgdef]
          linarith
      -- integrate the envelope
      have hint : ∫ ω, g ω ∂P = c1 * ∫ ω, L t ω * U t ω ∂P + c2 * ∫ ω, L t ω ^ 3 * U t ω ∂P +
          k * ((P (G t)ᶜ).toReal + (∫ ω, L t ω ^ 5 * U t ω ∂P) / z1 ^ 2 +
            (∫ ω, L t ω ^ 5 * U t ω ∂P) / z2 ^ 2) := by
        have hgeq : g = fun ω => (c1 * (L t ω * U t ω) + c2 * (L t ω ^ 3 * U t ω)) +
            (k * (G t)ᶜ.indicator (1 : Ω → ℝ) ω + (k / z1 ^ 2) * (L t ω ^ 5 * U t ω) +
              (k / z2 ^ 2) * (L t ω ^ 5 * U t ω)) := by
          funext ω; simp only [hgdef]; ring
        have i1 : Integrable (fun ω => c1 * (L t ω * U t ω)) P := hi1.const_mul c1
        have i2 : Integrable (fun ω => c2 * (L t ω ^ 3 * U t ω)) P := hi3.const_mul c2
        have i3 : Integrable (fun ω => k * (G t)ᶜ.indicator (1 : Ω → ℝ) ω) P := hiG.const_mul k
        have i4 : Integrable (fun ω => (k / z1 ^ 2) * (L t ω ^ 5 * U t ω)) P := hi5.const_mul _
        have i5 : Integrable (fun ω => (k / z2 ^ 2) * (L t ω ^ 5 * U t ω)) P := hi5.const_mul _
        rw [hgeq,
          integral_add (f := fun ω => c1 * (L t ω * U t ω) + c2 * (L t ω ^ 3 * U t ω))
            (g := fun ω => k * (G t)ᶜ.indicator (1 : Ω → ℝ) ω + (k / z1 ^ 2) * (L t ω ^ 5 * U t ω) +
              (k / z2 ^ 2) * (L t ω ^ 5 * U t ω)) (i1.add i2) ((i3.add i4).add i5),
          integral_add (f := fun ω => c1 * (L t ω * U t ω))
            (g := fun ω => c2 * (L t ω ^ 3 * U t ω)) i1 i2,
          integral_add (f := fun ω => k * (G t)ᶜ.indicator (1 : Ω → ℝ) ω +
              (k / z1 ^ 2) * (L t ω ^ 5 * U t ω))
            (g := fun ω => (k / z2 ^ 2) * (L t ω ^ 5 * U t ω)) (i3.add i4) i5,
          integral_add (f := fun ω => k * (G t)ᶜ.indicator (1 : Ω → ℝ) ω)
            (g := fun ω => (k / z1 ^ 2) * (L t ω ^ 5 * U t ω)) i3 i4,
          integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
          integral_const_mul, integral_indicator_one (hGm t).compl, measureReal_def]
        ring
      have e64 : ∀ r : ℕ, ((64 : ℝ) ^ (r + 1)) = 64 ^ (r + 1) := fun r => rfl
      have hbound : ∫ ω, g ω ∂P ≤ c1 * 64 ^ 2 + c2 * 64 ^ 4 +
          k * ((P (G t)ᶜ).toReal + 64 ^ 6 / z1 ^ 2 + 64 ^ 6 / z2 ^ 2) := by
        rw [hint]
        have h1 := mul_le_mul_of_nonneg_left hm1 hc10
        have h3 := mul_le_mul_of_nonneg_left hm3 hc20
        have h5a : (∫ ω, L t ω ^ 5 * U t ω ∂P) / z1 ^ 2 ≤ 64 ^ (5 + 1) / z1 ^ 2 :=
          div_le_div_of_nonneg_right hm5 (by positivity)
        have h5b : (∫ ω, L t ω ^ 5 * U t ω ∂P) / z2 ^ 2 ≤ 64 ^ (5 + 1) / z2 ^ 2 :=
          div_le_div_of_nonneg_right hm5 (by positivity)
        have h56 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (le_refl
          (P (G t)ᶜ).toReal) h5a) h5b) hk0
        norm_num at h1 h3 h56 ⊢
        linarith
      have hz1sq : z1 ^ 2 = nR / aν ^ 2 := by rw [hz1def, div_pow, hsR2]
      have hz2sq : z2 ^ 2 = nR ^ 2 / (16 * B) ^ 2 := by rw [hz2def, div_pow]
      have hsRinv : sR⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsR1
      have e1 : k * (64 ^ 6 / z1 ^ 2) = 8 * d * 64 ^ 6 * aν ^ 2 * (sR⁻¹ * nR⁻¹) := by
        rw [hz1sq, hkdef]; field_simp
      have e2 : k * (64 ^ 6 / z2 ^ 2) ≤ 8 * d * 64 ^ 6 * (16 * B) ^ 2 * (nR ^ 2)⁻¹ := by
        rw [hz2sq, hkdef]
        have : 8 * (d : ℝ) * sR⁻¹ * (64 ^ 6 / (nR ^ 2 / (16 * B) ^ 2)) =
            sR⁻¹ * (8 * d * 64 ^ 6 * (16 * B) ^ 2 * (nR ^ 2)⁻¹) := by field_simp
        rw [this]
        have h0 : 0 ≤ 8 * d * 64 ^ 6 * (16 * B) ^ 2 * (nR ^ 2)⁻¹ := by positivity
        calc sR⁻¹ * (8 * d * 64 ^ 6 * (16 * B) ^ 2 * (nR ^ 2)⁻¹) ≤
            1 * (8 * d * 64 ^ 6 * (16 * B) ^ 2 * (nR ^ 2)⁻¹) := mul_le_mul_of_nonneg_right hsRinv h0
          _ = _ := one_mul _
      have hRt' : Rt t = 8 * d * 0 + c1 * 64 ^ 2 + c2 * 64 ^ 4 + k * (P (G t)ᶜ).toReal +
          8 * d * 64 ^ 6 * aν ^ 2 * (sR⁻¹ * nR⁻¹) +
          8 * d * 64 ^ 6 * (16 * B) ^ 2 * (nR ^ 2)⁻¹ := by
        simp only [hRt, if_neg (show ¬(t + 1 < T1) by omega)]
        rw [← hnR, ← hsR, hc1def, hc2def, hkdef]
        ring
      calc ∫ ω, E t ω ∂P ≤ ∫ ω, g ω ∂P := G1P.int_le_of_le hgi hg0 hEg
        _ ≤ _ := hbound
        _ ≤ Rt t := by
          rw [hRt']
          have : k * ((P (G t)ᶜ).toReal + 64 ^ 6 / z1 ^ 2 + 64 ^ 6 / z2 ^ 2) =
              k * (P (G t)ᶜ).toReal + k * (64 ^ 6 / z1 ^ 2) + k * (64 ^ 6 / z2 ^ 2) := by ring
          rw [this, e1]
          linarith
  -- summation
  unfold exploI3
  have hsum : ∑ t ∈ Finset.range T, ∫ ω, E t ω ∂P ≤ ∑ t ∈ Finset.range T, Rt t :=
    Finset.sum_le_sum fun t ht => hround t (Finset.mem_range.1 ht)
  have hfirst : ∑ t ∈ Finset.range T, 8 * (d : ℝ) * (if t + 1 < T1 then 1 else 0) ≤
      8 * d * T1 := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : ((Finset.range T).filter (fun t => t + 1 < T1)).card ≤ T1 := by
      calc _ ≤ (Finset.range T1).card := by
            refine Finset.card_le_card fun t ht => ?_
            simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
            omega
        _ = T1 := Finset.card_range T1
    exact_mod_cast this
  have hS1 := G1P.sum_inv_cube T
  have hS2 := G1P.harm_le T hT
  have hS4 := G1P.sum_inv_pow32 T
  have hS5 := G1P.sum_inv_sq T
  have hRsum : ∑ t ∈ Finset.range T, Rt t =
      ∑ t ∈ Finset.range T, 8 * (d : ℝ) * (if t + 1 < T1 then 1 else 0) +
      2 * A' / pa * 64 ^ 2 * ∑ t ∈ Finset.range T, (((t : ℝ) + 1) ^ 3)⁻¹ +
      16 * B * c * 64 ^ 4 * ∑ t ∈ Finset.range T, ((t : ℝ) + 1)⁻¹ +
      8 * d * ∑ t ∈ Finset.range T, (Real.sqrt ((t : ℝ) + 1))⁻¹ * (P (G t)ᶜ).toReal +
      8 * d * 64 ^ 6 * aν ^ 2 *
        ∑ t ∈ Finset.range T, (Real.sqrt ((t : ℝ) + 1))⁻¹ * ((t : ℝ) + 1)⁻¹ +
      8 * d * 64 ^ 6 * (16 * B) ^ 2 * ∑ t ∈ Finset.range T, (((t : ℝ) + 1) ^ 2)⁻¹ := by
    simp only [hRt, Finset.sum_add_distrib, Finset.mul_sum]
  have hEsum : ∑ t ∈ Finset.range T, ∫ ω, (∫ x, (x - astar) ⬝ᵥ θ ∂(R.p t ω) -
      ∫ x, (x - astar) ⬝ᵥ θ ∂(R.qw ℬ e t ω)) ∂P = ∑ t ∈ Finset.range T, ∫ ω, E t ω ∂P := rfl
  rw [hEsum]
  refine hsum.trans ?_
  rw [hRsum]
  have k1 := mul_le_mul_of_nonneg_left hS1 (show (0 : ℝ) ≤ 2 * A' / pa * 64 ^ 2 by positivity)
  have k2 := mul_le_mul_of_nonneg_left hS2 (show (0 : ℝ) ≤ 16 * B * c * 64 ^ 4 by positivity)
  have k3 := mul_le_mul_of_nonneg_left hfail (show (0 : ℝ) ≤ 8 * d by positivity)
  have k4 := mul_le_mul_of_nonneg_left hS4 (show (0 : ℝ) ≤ 8 * d * 64 ^ 6 * aν ^ 2 by positivity)
  have k5 := mul_le_mul_of_nonneg_left hS5
    (show (0 : ℝ) ≤ 8 * d * 64 ^ 6 * (16 * B) ^ 2 by positivity)
  have hfinal : 16 * B * c * 64 ^ 4 * Real.log (Real.exp 1 * T) =
      16 * gB d * 64 ^ 4 * ctrCost θ astar ν * Real.log (Real.exp 1 * T) := by
    rw [hBdef, hcdef]; ring
  rw [← hfinal]
  have k1' := k1.trans (le_of_eq (show 2 * A' / pa * 64 ^ 2 * 2 = 4 * 64 ^ 2 * A' / pa by ring))
  have k3' := k3.trans (le_of_eq (show 8 * (d : ℝ) * (W * (1 + Real.sqrt C *
    Real.log (Real.exp 1 + C))) = 8 * d * W + 8 * d * W * Real.sqrt C *
      Real.log (Real.exp 1 + C) by ring))
  have k4' := k4.trans (le_of_eq (show 8 * (d : ℝ) * 64 ^ 6 * aν ^ 2 * 6 =
    48 * d * 64 ^ 6 * aν ^ 2 by ring))
  have k5' := k5.trans (le_of_eq (show 8 * (d : ℝ) * 64 ^ 6 * (16 * B) ^ 2 * 2 =
    16 * d * 64 ^ 6 * (16 * B) ^ 2 by ring))
  linarith [k1', k2, k3', k4', k5', hfirst]

end G1E

-- ===== G1/G5Sol =====

namespace IAFTRL

open MeasureTheory

theorem _root_.solution {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (hk : 1 ≤ kdim ℬ)
    (he : Function.Surjective e) (θ astar : Fin d → ℝ) (hθ : setNorm 𝒜 θ ≤ 1)
    (hastar : astar ∈ 𝒜) (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ)
    (hsharp : IsSharp 𝒜 θ astar) :
    ∃ J : ℝ, ∀ n : Measure (Fin d → ℝ), IsCtrAlloc ℬ θ astar n →
      ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (T : ℕ) (C : ℝ) (R : GRun d Ω), 1 ≤ T → 0 ≤ C →
        IsGIAFTRLRun P 𝒜 ℬ e T R → IsCorruptedG P 𝒜 θ C T R →
        exploI3 P ℬ e T R θ astar ≤
          16 * gB d * 64 ^ 4 * ctrCost θ astar n * Real.log (Real.exp 1 * T) + M +
            J * Real.sqrt C * Real.log (Real.exp 1 + C) :=
  G1E.explo hd h𝒜 hℬ hgen hball hspan hk he θ astar hθ hastar huniq hsharp

end IAFTRL
