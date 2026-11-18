-- Prove2me | solution 1 for IAFTRL.theorem_3_1_alloc
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-17T09:08:48.862562+00:00
-- url     : https://prove2.me/submissions/44475ed2-b1da-45d1-8221-c34bebc8c373

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL

-- ===== Geo =====

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

-- ===== Transfer =====

/-! ### Transfer of centered allocations from `𝒜` to a generator `ℬ` (Lemma J.10) -/

open MeasureTheory Matrix Set

namespace T31

variable {d : ℕ}

lemma conv_eq {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IAFTRL.IsGenerator 𝒜 ℬ) :
    convexHull ℝ 𝒜 = convexHull ℝ ℬ :=
  (convexHull_min hgen.2 (convex_convexHull ℝ ℬ)).antisymm (convexHull_mono hgen.1)

/-- an allocation on the generator is an allocation on the action set -/
lemma alloc_of_gen {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IAFTRL.IsGenerator 𝒜 ℬ)
    {θ astar : Fin d → ℝ} {n : Measure (Fin d → ℝ)} (hn : IAFTRL.IsCtrAlloc ℬ θ astar n) :
    IAFTRL.IsCtrAlloc 𝒜 θ astar n := by
  obtain ⟨hfin, hsupp, hpd, hfeas⟩ := hn
  refine ⟨hfin, measure_mono_null (compl_subset_compl.2 hgen.1) hsupp, hpd, fun u hu => ?_⟩
  exact hfeas u (by rwa [← conv_eq hgen])

/-- Jensen for squares over a finite convex combination -/
lemma sq_comb_le {κ : Type*} [Fintype κ] (w : κ → ℝ) (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (v : κ → ℝ) : (∑ j, w j * v j) ^ 2 ≤ ∑ j, w j * v j ^ 2 := by
  have := (Even.convexOn_pow (𝕜 := ℝ) (n := 2) even_two).map_sum_le (t := Finset.univ)
    (w := w) (p := v) (fun j _ => hw0 j) hw1 (fun j _ => Set.mem_univ _)
  simpa [smul_eq_mul] using this

/-- **Transfer (Lemma J.10).** Every finite feasible centered allocation on `𝒜` can be replaced
by one on the generator `ℬ` with the same cost. -/
theorem transfer {𝒜 ℬ : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) (hℬ : IsClosed ℬ)
    (hgen : IAFTRL.IsGenerator 𝒜 ℬ) {θ astar : Fin d → ℝ} {n : Measure (Fin d → ℝ)}
    (hn : IAFTRL.IsCtrAlloc 𝒜 θ astar n) :
    ∃ n', IAFTRL.IsCtrAlloc ℬ θ astar n' ∧
      IAFTRL.ctrCost θ astar n' = IAFTRL.ctrCost θ astar n := by
  obtain ⟨hfin, hsupp, hpd, hfeas⟩ := hn
  by_cases h0 : n = 0
  · refine ⟨n, ⟨hfin, by simp [h0], hpd, fun u hu => hfeas u ?_⟩, rfl⟩
    rwa [conv_eq hgen]
  haveI : NeZero n := ⟨h0⟩
  -- the moment map
  let φ : (Fin d → ℝ) → (Fin d → Fin d → ℝ) × ℝ :=
    fun a => (fun k l => a k * a l, (a - astar) ⬝ᵥ θ)
  have hφc : Continuous φ := by
    simp only [φ, dotProduct]
    fun_prop
  have hφi : Integrable φ n := integrable_cpt h𝒜 hsupp hφc
  have hK : IsCompact (convexHull ℝ (φ '' 𝒜)) := isCompact_convexHull_of (h𝒜.image hφc)
  have hmem : ⨍ a, φ a ∂n ∈ convexHull ℝ (φ '' 𝒜) :=
    (convex_convexHull ℝ _).average_mem hK.isClosed
      (by filter_upwards [ae_mem hsupp] with a ha using subset_convexHull ℝ _ ⟨a, ha, rfl⟩) hφi
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.1 hmem
  choose a ha hφa using hz
  -- the total mass
  set c : ℝ := n.real univ with hc
  have hcpos : 0 < c := by
    rw [hc, measureReal_def]
    exact ENNReal.toReal_pos (NeZero.ne (n univ)) (measure_ne_top n univ)
  -- `∫ φ = c • Σ w_i φ(a_i)`
  have hint : ∫ x, φ x ∂n = c • ∑ i, w i • φ (a i) := by
    have := average_eq (μ := n) φ
    rw [← hsum] at this
    simp only [hφa]
    rw [this, smul_smul, mul_inv_cancel₀ hcpos.ne', one_smul]
  -- components
  have hcomp1 : ∀ k l, (∫ x, φ x ∂n).1 k l = ∫ x, x k * x l ∂n := by
    intro k l
    have h1 : Integrable (fun x => (φ x).1) n := hφi.fst
    rw [fst_integral hφi, eval_integral (fun k => h1.eval k), eval_integral]
    intro l
    exact (h1.eval k).eval l
  have hcomp2 : (∫ x, φ x ∂n).2 = ∫ x, (x - astar) ⬝ᵥ θ ∂n := snd_integral hφi
  have hdesign : ∀ k l, IAFTRL.designMat n k l = c * ∑ i, w i * (a i k * a i l) := by
    intro k l
    have := congrArg (fun m => m.1 k l) hint
    simp only [hcomp1, Prod.fst_sum, Prod.smul_fst, Prod.fst_sum, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, φ] at this
    simp only [IAFTRL.designMat, of_apply, this]
  have hcost : IAFTRL.ctrCost θ astar n = c * ∑ i, w i * ((a i - astar) ⬝ᵥ θ) := by
    have := congrArg (fun m => m.2) hint
    simp only [hcomp2] at this
    rw [IAFTRL.ctrCost, this]
    simp [Prod.snd_sum, φ, smul_eq_mul]
  -- quadratic form of `H_n`
  have hqf : ∀ y, y ⬝ᵥ IAFTRL.designMat n *ᵥ y = c * ∑ i, w i * (a i ⬝ᵥ y) ^ 2 := by
    intro y
    have hfin' : IAFTRL.designMat n = IAFTRL.designMat (disc (fun i => c * w i) a) := by
      ext k l
      rw [hdesign, designMat_disc (fun i => mul_nonneg hcpos.le (hw0 i)), Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hfin', qf_disc (fun i => mul_nonneg hcpos.le (hw0 i)), Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  -- decompose each `a i` in the generator
  have hab : ∀ i, a i ∈ convexHull ℝ ℬ := fun i => hgen.2 (ha i)
  choose κ hκ w' z' hw'0 hw'1 hz' hsum' using fun i => mem_convexHull_iff_exists_fintype.1 (hab i)
  letI : ∀ i, Fintype (κ i) := hκ
  let r : (Σ i, κ i) → ℝ := fun p => c * w p.1 * w' p.1 p.2
  let x : (Σ i, κ i) → Fin d → ℝ := fun p => z' p.1 p.2
  have hr : ∀ p, 0 ≤ r p := fun p => mul_nonneg (mul_nonneg hcpos.le (hw0 _)) (hw'0 _ _)
  have hxℬ : ∀ p, x p ∈ ℬ := fun p => hz' _ _
  -- the dot products of `a i` are averages
  have hdot : ∀ i (y : Fin d → ℝ), a i ⬝ᵥ y = ∑ j, w' i j * (z' i j ⬝ᵥ y) := by
    intro i y
    rw [← hsum' i, sum_dotProduct]
    simp [smul_dotProduct]
  have hqf' : ∀ y, y ⬝ᵥ IAFTRL.designMat (disc r x) *ᵥ y =
      c * ∑ i, w i * ∑ j, w' i j * (z' i j ⬝ᵥ y) ^ 2 := by
    intro y
    rw [qf_disc hr, Fintype.sum_sigma, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [r, x]; ring
  have hmono : ∀ y, y ⬝ᵥ IAFTRL.designMat n *ᵥ y ≤ y ⬝ᵥ IAFTRL.designMat (disc r x) *ᵥ y := by
    intro y
    rw [hqf, hqf']
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) hcpos.le
    refine mul_le_mul_of_nonneg_left ?_ (hw0 i)
    rw [hdot]
    exact sq_comb_le (w' i) (hw'0 i) (hw'1 i) _
  have hpd' : (IAFTRL.designMat (disc r x)).PosDef := by
    refine posDef_of_qf (designMat_herm _) fun y hy => ?_
    have := hpd.dotProduct_mulVec_pos hy
    rw [star_trivial] at this
    exact this.trans_le (hmono y)
  refine ⟨disc r x, ⟨inferInstance, disc_compl hℬ hxℬ, hpd', fun u hu => ?_⟩, ?_⟩
  · have hu' : u ∈ convexHull ℝ 𝒜 := by rwa [conv_eq hgen]
    refine inv_le_of_qf _ hpd' _ _ (by positivity) fun y => ?_
    have h1 := cs_pd _ hpd (u - astar) y
    have h2 := hfeas u hu'
    have h3 : 0 ≤ y ⬝ᵥ IAFTRL.designMat n *ᵥ y := by
      by_cases hy : y = 0
      · simp [hy]
      · have := hpd.dotProduct_mulVec_pos hy
        rw [star_trivial] at this
        exact this.le
    calc ((u - astar) ⬝ᵥ y) ^ 2
        ≤ ((u - astar) ⬝ᵥ (IAFTRL.designMat n)⁻¹ *ᵥ (u - astar)) *
          (y ⬝ᵥ IAFTRL.designMat n *ᵥ y) := h1
      _ ≤ (((u - astar) ⬝ᵥ θ) ^ 2 / 2) * (y ⬝ᵥ IAFTRL.designMat n *ᵥ y) :=
          mul_le_mul_of_nonneg_right h2 h3
      _ ≤ (((u - astar) ⬝ᵥ θ) ^ 2 / 2) * (y ⬝ᵥ IAFTRL.designMat (disc r x) *ᵥ y) :=
          mul_le_mul_of_nonneg_left (hmono y) (by positivity)
  · rw [hcost, IAFTRL.ctrCost, integral_disc hr, Fintype.sum_sigma, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hΔ : (a i - astar) ⬝ᵥ θ = ∑ j, w' i j * ((z' i j - astar) ⬝ᵥ θ) := by
      simp only [sub_dotProduct, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw'1 i,
        one_mul]
      rw [hdot]
    rw [hΔ, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [r, x]; ring

end T31

-- ===== G6 =====

/-! ### Lemma G.6: sharpness gives a finite feasible centered allocation -/

open MeasureTheory Matrix Set

namespace T31

variable {d : ℕ}

lemma qf_le_entries (M : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    x ⬝ᵥ M *ᵥ x ≤ (∑ k, ∑ l, |M k l|) * ‖x‖ ^ 2 := by
  have h : x ⬝ᵥ M *ᵥ x = ∑ k, ∑ l, x k * (M k l * x l) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [h, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun l _ => ?_
  have hk : |x k| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x k
  have hl : |x l| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x l
  calc x k * (M k l * x l) ≤ |x k * (M k l * x l)| := le_abs_self _
    _ = |M k l| * (|x k| * |x l|) := by rw [abs_mul, abs_mul]; ring
    _ ≤ |M k l| * (‖x‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hk hl (abs_nonneg _) (norm_nonneg _))
          (abs_nonneg _)
    _ = |M k l| * ‖x‖ ^ 2 := by ring

lemma qf_nonneg_of_posDef {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) (y : Fin d → ℝ) :
    0 ≤ y ⬝ᵥ H *ᵥ y := by
  by_cases hy : y = 0
  · simp [hy]
  · have := hH.dotProduct_mulVec_pos hy
    rw [star_trivial] at this
    exact this.le

/-- **Lemma G.6.** -/
theorem G6 (𝒜 : Set (Fin d → ℝ)) (h𝒜 : IsCompact 𝒜) (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) (θ astar : Fin d → ℝ) (hastar : astar ∈ 𝒜)
    (hsharp : IAFTRL.IsSharp 𝒜 θ astar) :
    ∃ n : Measure (Fin d → ℝ), IAFTRL.IsCtrAlloc 𝒜 θ astar n := by
  obtain ⟨ς, hς, hsh⟩ := hsharp
  have hne : 𝒜.Nonempty := ⟨astar, hastar⟩
  obtain ⟨b, hb𝒜, hbspan, hli⟩ := exists_linearIndependent ℝ 𝒜
  have hbspan' : Submodule.span ℝ b = ⊤ := hbspan.trans hspan
  haveI : Fintype b := hli.setFinite.fintype
  let x : b → Fin d → ℝ := Subtype.val
  have hx𝒜 : ∀ i, x i ∈ 𝒜 := fun i => hb𝒜 i.2
  -- the unit-weight design
  let H1 := IAFTRL.designMat (disc (fun _ : b => (1 : ℝ)) x)
  have hqf1 : ∀ y, y ⬝ᵥ H1 *ᵥ y = ∑ i, (x i ⬝ᵥ y) ^ 2 := by
    intro y
    simp only [H1]
    rw [qf_disc (fun _ => zero_le_one)]
    simp
  have hH1 : H1.PosDef := by
    refine posDef_of_qf (designMat_herm _) fun y hy => ?_
    rw [hqf1]
    by_contra hle
    push_neg at hle
    have hz : ∀ i, x i ⬝ᵥ y = 0 := by
      intro i
      have h0 : ∑ i, (x i ⬝ᵥ y) ^ 2 = 0 :=
        le_antisymm hle (Finset.sum_nonneg fun i _ => sq_nonneg _)
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i ⬝ᵥ y))).1 h0 i
        (Finset.mem_univ _)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    exact hy (eq_zero_of_orth hbspan' y fun a ha => hz ⟨a, ha⟩)
  set K : ℝ := ∑ k, ∑ l, |H1⁻¹ k l| with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  set α : ℝ := 2 * K / ς ^ 2 + 1 with hα
  have hα0 : 0 < α := by positivity
  let n := disc (fun _ : b => α) x
  have hqfn : ∀ y, y ⬝ᵥ IAFTRL.designMat n *ᵥ y = α * (y ⬝ᵥ H1 *ᵥ y) := by
    intro y
    simp only [n]
    rw [qf_disc (fun _ => hα0.le), hqf1, Finset.mul_sum]
  refine ⟨n, ⟨inferInstance, disc_compl h𝒜.isClosed hx𝒜, ?_, fun u hu => ?_⟩⟩
  · refine posDef_of_qf (designMat_herm _) fun y hy => ?_
    rw [hqfn]
    have := hH1.dotProduct_mulVec_pos hy
    rw [star_trivial] at this
    positivity
  · have hpdn : (IAFTRL.designMat n).PosDef := by
      refine posDef_of_qf (designMat_herm _) fun y hy => ?_
      rw [hqfn]
      have := hH1.dotProduct_mulVec_pos hy
      rw [star_trivial] at this
      positivity
    set v := u - astar
    have hnorm := sharp_norm hne hspan hball hsh hς hu
    have hΔ0 : 0 ≤ v ⬝ᵥ θ := le_trans (by positivity) hnorm
    have hv2 : ς ^ 2 * ‖v‖ ^ 2 ≤ (v ⬝ᵥ θ) ^ 2 := by
      have h0 : 0 ≤ ς * ‖v‖ := by positivity
      have := mul_le_mul hnorm hnorm h0 hΔ0
      nlinarith [this]
    have hKv : K * ‖v‖ ^ 2 ≤ α * ((v ⬝ᵥ θ) ^ 2 / 2) := by
      have hς2 : 0 < ς ^ 2 := by positivity
      have h1 : K * ‖v‖ ^ 2 ≤ K * ((v ⬝ᵥ θ) ^ 2 / ς ^ 2) :=
        mul_le_mul_of_nonneg_left (by rw [le_div_iff₀ hς2]; linarith) hK0
      have h2 : K * ((v ⬝ᵥ θ) ^ 2 / ς ^ 2) ≤ α * ((v ⬝ᵥ θ) ^ 2 / 2) := by
        rw [hα]
        have : K * ((v ⬝ᵥ θ) ^ 2 / ς ^ 2) = (2 * K / ς ^ 2) * ((v ⬝ᵥ θ) ^ 2 / 2) := by
          field_simp
        rw [this]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    refine inv_le_of_qf _ hpdn _ _ (by positivity) fun y => ?_
    have hcs := cs_pd H1 hH1 v y
    have hqe := qf_le_entries H1⁻¹ v
    have hy0 := qf_nonneg_of_posDef hH1 y
    rw [hqfn]
    calc (v ⬝ᵥ y) ^ 2 ≤ (v ⬝ᵥ H1⁻¹ *ᵥ v) * (y ⬝ᵥ H1 *ᵥ y) := hcs
      _ ≤ (K * ‖v‖ ^ 2) * (y ⬝ᵥ H1 *ᵥ y) := mul_le_mul_of_nonneg_right hqe hy0
      _ ≤ (α * ((v ⬝ᵥ θ) ^ 2 / 2)) * (y ⬝ᵥ H1 *ᵥ y) := mul_le_mul_of_nonneg_right hKv hy0
      _ = (v ⬝ᵥ θ) ^ 2 / 2 * (α * (y ⬝ᵥ H1 *ᵥ y)) := by ring

end T31

-- ===== Alloc =====

/-! ### A fixed finite comparison allocation (Appendix F.1.1) -/

open MeasureTheory Matrix Set

namespace T31

variable {d : ℕ}

lemma abs_dot_le (v w : Fin d → ℝ) : |v ⬝ᵥ w| ≤ ‖v‖ * ∑ k, |w k| := by
  simp only [dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using norm_le_pi_norm v k)
    (abs_nonneg _)

/-- the optimal action lies in the generator -/
lemma astar_mem_gen {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IAFTRL.IsGenerator 𝒜 ℬ)
    {θ astar : Fin d → ℝ} (hastar : astar ∈ 𝒜)
    (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ) : astar ∈ ℬ := by
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.1 (hgen.2 hastar)
  have hgap : ∀ i, 0 ≤ w i * ((z i - astar) ⬝ᵥ θ) := by
    intro i
    refine mul_nonneg (hw0 i) ?_
    rw [sub_dotProduct]
    by_cases h : z i = astar
    · simp [h]
    · linarith [huniq (z i) (hgen.1 (hz i)) h]
  have hsum0 : ∑ i, w i * ((z i - astar) ⬝ᵥ θ) = 0 := by
    simp only [sub_dotProduct, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
    have : ∑ i, w i * (z i ⬝ᵥ θ) = astar ⬝ᵥ θ := by
      rw [← hsum, sum_dotProduct]; simp [smul_dotProduct]
    rw [this, sub_self]
  obtain ⟨i, hi⟩ : ∃ i, 0 < w i := by
    by_contra hcon
    push_neg at hcon
    have : ∑ i, w i ≤ 0 := Finset.sum_nonpos fun i _ => hcon i
    linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hgap i)).1 hsum0 i
    (Finset.mem_univ _)
  have hΔ : (z i - astar) ⬝ᵥ θ = 0 := by
    rcases mul_eq_zero.1 hzero with h | h
    · exact absurd h hi.ne'
    · exact h
  by_contra hB
  have hne : z i ≠ astar := fun h => hB (h ▸ hz i)
  have := huniq (z i) (hgen.1 (hz i)) hne
  rw [sub_dotProduct] at hΔ
  linarith

/-- **(F.1)–(F.8).** -/
theorem alloc (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (h𝒜 : IsCompact 𝒜)
    (hℬ : IsCompact ℬ) (hgen : IAFTRL.IsGenerator 𝒜 ℬ) (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) (θ astar : Fin d → ℝ) (hastar : astar ∈ 𝒜)
    (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ) (hsharp : IAFTRL.IsSharp 𝒜 θ astar) :
    ∃ n : Measure (Fin d → ℝ), IAFTRL.IsCtrAlloc ℬ θ astar n ∧
      IAFTRL.ctrCost θ astar n ≤ 2 * IAFTRL.cstarCtr ℬ θ astar := by
  have hne : 𝒜.Nonempty := ⟨astar, hastar⟩
  obtain ⟨ς, hς, hsh⟩ := id hsharp
  set S := IAFTRL.ctrCost θ astar '' {n | IAFTRL.IsCtrAlloc ℬ θ astar n} with hS
  have hcs : IAFTRL.cstarCtr ℬ θ astar = sInf S := rfl
  obtain ⟨n0, hn0⟩ := G6 𝒜 h𝒜 hball hspan θ astar hastar hsharp
  obtain ⟨n1, hn1, -⟩ := transfer h𝒜 hℬ.isClosed hgen hn0
  have hSne : S.Nonempty := ⟨_, n1, hn1, rfl⟩
  have hgap : ∀ a ∈ 𝒜, 0 ≤ (a - astar) ⬝ᵥ θ := by
    intro a ha
    rw [sub_dotProduct]
    by_cases h : a = astar
    · simp [h]
    · linarith [huniq a ha h]
  have hcost0 : ∀ n, IAFTRL.IsCtrAlloc ℬ θ astar n → 0 ≤ IAFTRL.ctrCost θ astar n := by
    rintro n ⟨_, hsupp, _, _⟩
    exact integral_nonneg_of_ae
      (by filter_upwards [ae_mem hsupp] with a ha using hgap a (hgen.1 ha))
  have hc0 : 0 ≤ IAFTRL.cstarCtr ℬ θ astar := by
    rw [hcs]
    exact le_csInf hSne (by rintro _ ⟨n, hn, rfl⟩; exact hcost0 n hn)
  have hnorm1 : ∀ a ∈ 𝒜, ‖a‖ ≤ 1 := fun a ha => by
    simpa using Sset_sub_ball hball (subset_convexHull ℝ _ (Or.inl ha) : a ∈ IAFTRL.Sset 𝒜)
  have hconv : convexHull ℝ ℬ = convexHull ℝ 𝒜 := (conv_eq hgen).symm
  rcases hc0.lt_or_eq with hpos | hzero
  · -- positive complexity: approximate the infimum within a factor two
    have hlt : sInf S < 2 * sInf S := by rw [← hcs]; linarith
    obtain ⟨_, ⟨n, hn, rfl⟩, hlt'⟩ := exists_lt_of_csInf_lt hSne hlt
    exact ⟨n, hn, by rw [hcs]; exact hlt'.le⟩
  -- zero complexity
  by_cases hw : ∃ w : Fin d → ℝ, w ≠ 0 ∧ w ⬝ᵥ astar = 0
  · exfalso
    obtain ⟨w, hw0, hwa⟩ := hw
    obtain ⟨a, ha, haw⟩ : ∃ a ∈ 𝒜, a ⬝ᵥ w ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hw0 (eq_zero_of_orth hspan w hcon)
    have hane : a ≠ astar := by
      rintro rfl; apply haw; rw [dotProduct_comm]; exact hwa
    have hΔa : 0 < (a - astar) ⬝ᵥ θ := by
      rw [sub_dotProduct]; linarith [huniq a ha hane]
    set W : ℝ := ∑ k, |w k| with hWdef
    have hW : 0 < W := by
      obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by
        by_contra hcon; push_neg at hcon; exact hw0 (funext hcon)
      exact lt_of_lt_of_le (abs_pos.2 hk)
        (Finset.single_le_sum (f := fun k => |w k|) (fun k _ => abs_nonneg _)
          (Finset.mem_univ k))
    have haw2 : 0 < (a ⬝ᵥ w) ^ 2 := by positivity
    set κ : ℝ := ς * (a ⬝ᵥ w) ^ 2 / (((a - astar) ⬝ᵥ θ) ^ 2 * W ^ 2) with hκdef
    have hκ : 0 < κ := by positivity
    have hlow : ∀ n, IAFTRL.IsCtrAlloc ℬ θ astar n → κ ≤ IAFTRL.ctrCost θ astar n := by
      rintro n ⟨hfin, hsupp, hpd, hfeas⟩
      have hx : (a - astar) ⬝ᵥ w = a ⬝ᵥ w := by
        rw [sub_dotProduct, dotProduct_comm astar w, hwa, sub_zero]
      have hcsw := cs_pd _ hpd (a - astar) w
      have hfa := hfeas a (hgen.2 ha)
      have hww := qf_nonneg_of_posDef hpd w
      -- `w ᵀ H w ≤ (2 W² / ς) c^n`
      have hpt : ∀ b ∈ 𝒜, (b ⬝ᵥ w) ^ 2 ≤ (2 * W ^ 2 / ς) * ((b - astar) ⬝ᵥ θ) := by
        intro b hb
        have hbw : b ⬝ᵥ w = (b - astar) ⬝ᵥ w := by
          rw [sub_dotProduct, dotProduct_comm astar w, hwa, sub_zero]
        have h1 := abs_dot_le (b - astar) w
        have h2 : ‖b - astar‖ ≤ 2 := (norm_sub_le _ _).trans (by
          linarith [hnorm1 b hb, hnorm1 astar hastar])
        have h3 := sharp_norm hne hspan hball hsh hς (subset_convexHull ℝ _ hb)
        have hn0 : 0 ≤ ‖b - astar‖ := norm_nonneg _
        rw [hbw]
        have h4 : ((b - astar) ⬝ᵥ w) ^ 2 ≤ (‖b - astar‖ * W) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        have h5 : (‖b - astar‖ * W) ^ 2 ≤ 2 * W ^ 2 * ‖b - astar‖ := by
          have : (‖b - astar‖ * W) ^ 2 = W ^ 2 * (‖b - astar‖ * ‖b - astar‖) := by ring
          rw [this]
          have : ‖b - astar‖ * ‖b - astar‖ ≤ 2 * ‖b - astar‖ :=
            mul_le_mul_of_nonneg_right h2 hn0
          nlinarith [sq_nonneg W]
        have h6 : 2 * W ^ 2 * ‖b - astar‖ ≤ (2 * W ^ 2 / ς) * ((b - astar) ⬝ᵥ θ) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hς]
          nlinarith [sq_nonneg W]
        linarith
      have hint1 : Integrable (fun b : Fin d → ℝ => (b ⬝ᵥ w) ^ 2) n :=
        integrable_cpt hℬ hsupp (by simp only [dotProduct]; fun_prop)
      have hint2 : Integrable (fun b : Fin d → ℝ => (2 * W ^ 2 / ς) * ((b - astar) ⬝ᵥ θ)) n :=
        integrable_cpt hℬ hsupp (by simp only [dotProduct]; fun_prop)
      have hwH : w ⬝ᵥ IAFTRL.designMat n *ᵥ w ≤ (2 * W ^ 2 / ς) * IAFTRL.ctrCost θ astar n := by
        rw [qf_designMat hℬ hsupp, IAFTRL.ctrCost, ← integral_const_mul]
        exact integral_mono_ae hint1 hint2
          (by filter_upwards [ae_mem hsupp] with b hb using hpt b (hgen.1 hb))
      have hmain : (a ⬝ᵥ w) ^ 2 ≤
          (((a - astar) ⬝ᵥ θ) ^ 2 * W ^ 2 / ς) * IAFTRL.ctrCost θ astar n := by
        rw [← hx]
        calc ((a - astar) ⬝ᵥ w) ^ 2
            ≤ ((a - astar) ⬝ᵥ (IAFTRL.designMat n)⁻¹ *ᵥ (a - astar)) *
              (w ⬝ᵥ IAFTRL.designMat n *ᵥ w) := hcsw
          _ ≤ (((a - astar) ⬝ᵥ θ) ^ 2 / 2) * (w ⬝ᵥ IAFTRL.designMat n *ᵥ w) :=
              mul_le_mul_of_nonneg_right hfa hww
          _ ≤ (((a - astar) ⬝ᵥ θ) ^ 2 / 2) * ((2 * W ^ 2 / ς) * IAFTRL.ctrCost θ astar n) :=
              mul_le_mul_of_nonneg_left hwH (by positivity)
          _ = (((a - astar) ⬝ᵥ θ) ^ 2 * W ^ 2 / ς) * IAFTRL.ctrCost θ astar n := by
              field_simp
      rw [hκdef, div_le_iff₀ (by positivity)]
      have : (((a - astar) ⬝ᵥ θ) ^ 2 * W ^ 2 / ς) * IAFTRL.ctrCost θ astar n * ς =
          IAFTRL.ctrCost θ astar n * (((a - astar) ⬝ᵥ θ) ^ 2 * W ^ 2) := by
        field_simp
      nlinarith [this, hmain]
    have : κ ≤ IAFTRL.cstarCtr ℬ θ astar := by
      rw [hcs]
      exact le_csInf hSne (by rintro _ ⟨n, hn, rfl⟩; exact hlow n hn)
    linarith
  -- every vector orthogonal to `a*` vanishes: the single atom at `a*` is feasible at zero cost
  push_neg at hw
  have hastar0 : astar ≠ 0 := by
    intro h0
    let e : Fin d → ℝ := Pi.single ⟨0, hd⟩ 1
    have he : e ≠ 0 := by
      intro h
      have := congrFun h ⟨0, hd⟩
      simp [e] at this
    exact hw e he (by simp [h0])
  have hastarB := astar_mem_gen hgen hastar huniq
  have hnpos : 0 < ‖astar‖ := norm_pos_iff.2 hastar0
  set m : ℝ := 2 / (ς ^ 2 * ‖astar‖ ^ 2) with hm
  have hm0 : 0 < m := by positivity
  let n := disc (fun _ : Unit => m) (fun _ => astar)
  have hqfn : ∀ y, y ⬝ᵥ IAFTRL.designMat n *ᵥ y = m * (astar ⬝ᵥ y) ^ 2 := by
    intro y
    simp only [n]
    rw [qf_disc (fun _ => hm0.le)]
    simp
  have hpdn : (IAFTRL.designMat n).PosDef := by
    refine posDef_of_qf (designMat_herm _) fun y hy => ?_
    rw [hqfn]
    have : astar ⬝ᵥ y ≠ 0 := by rw [dotProduct_comm]; exact hw y hy
    positivity
  have haa : astar ⬝ᵥ astar ≠ 0 := fun h => hastar0 (dotProduct_self_eq_zero.1 h)
  refine ⟨n, ⟨inferInstance, disc_compl hℬ.isClosed (fun _ => hastarB), hpdn, fun u hu => ?_⟩, ?_⟩
  · set v := u - astar with hv
    set t : ℝ := (v ⬝ᵥ astar) / (astar ⬝ᵥ astar)
    have hvt : v = t • astar := by
      by_contra hne'
      have h1 : v - t • astar ≠ 0 := sub_ne_zero.2 hne'
      apply hw _ h1
      rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
      simp only [t]
      field_simp
      ring
    have hu' : u ∈ convexHull ℝ 𝒜 := by rwa [← hconv]
    have h3 := sharp_norm hne hspan hball hsh hς hu'
    rw [← hv, hvt, norm_smul, Real.norm_eq_abs] at h3
    have hΔ0 : 0 ≤ v ⬝ᵥ θ := by rw [hvt] at *; exact le_trans (by positivity) h3
    have ht2 : t ^ 2 * (ς ^ 2 * ‖astar‖ ^ 2) ≤ (v ⬝ᵥ θ) ^ 2 := by
      rw [hvt] at hΔ0 ⊢
      have h0 : 0 ≤ ς * (|t| * ‖astar‖) := by positivity
      have := mul_le_mul h3 h3 h0 hΔ0
      calc t ^ 2 * (ς ^ 2 * ‖astar‖ ^ 2)
          = (ς * (|t| * ‖astar‖)) * (ς * (|t| * ‖astar‖)) := by rw [← sq_abs t]; ring
        _ ≤ _ := this
        _ = _ := by ring
    refine inv_le_of_qf _ hpdn _ _ (by positivity) fun y => ?_
    rw [hqfn, hvt, smul_dotProduct, smul_eq_mul, ← hvt]
    have hD : 0 < ς ^ 2 * ‖astar‖ ^ 2 := by positivity
    have : t ^ 2 ≤ (v ⬝ᵥ θ) ^ 2 / 2 * m := by
      rw [hm, div_mul_div_comm, le_div_iff₀ (by positivity)]
      nlinarith [ht2]
    calc (t * (astar ⬝ᵥ y)) ^ 2 = t ^ 2 * (astar ⬝ᵥ y) ^ 2 := by ring
      _ ≤ ((v ⬝ᵥ θ) ^ 2 / 2 * m) * (astar ⬝ᵥ y) ^ 2 :=
          mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = (v ⬝ᵥ θ) ^ 2 / 2 * (m * (astar ⬝ᵥ y) ^ 2) := by ring
  · rw [IAFTRL.ctrCost, integral_disc (fun _ => hm0.le), ← hzero]
    simp

end T31

namespace IAFTRL

open MeasureTheory

theorem _root_.solution {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (h𝒜 : IsCompact 𝒜)
    (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ) (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) (θ astar : Fin d → ℝ) (hastar : astar ∈ 𝒜)
    (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ) (hsharp : IsSharp 𝒜 θ astar) :
    ∃ n : Measure (Fin d → ℝ), IsCtrAlloc ℬ θ astar n ∧
      ctrCost θ astar n ≤ 2 * cstarCtr ℬ θ astar :=
  T31.alloc hd 𝒜 ℬ h𝒜 hℬ hgen hball hspan θ astar hastar huniq hsharp

end IAFTRL
