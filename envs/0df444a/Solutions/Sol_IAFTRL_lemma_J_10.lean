-- Prove2me | solution 1 for IAFTRL.lemma_J_10
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-17T09:02:17.42593+00:00
-- url     : https://prove2.me/submissions/7090a27c-961c-4a7b-ac2e-7354df115c5f

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

-- ===== J10 =====

/-! ### Lemma J.10 -/

open MeasureTheory Matrix Set

namespace T31

variable {d : ℕ}

lemma cont_absdot (z : Fin d → ℝ) : Continuous fun a : Fin d → ℝ => |a ⬝ᵥ z| := by
  simp only [dotProduct]
  fun_prop

lemma le_setNorm {X : Set (Fin d → ℝ)} (hX : IsCompact X) {a : Fin d → ℝ} (ha : a ∈ X)
    (z : Fin d → ℝ) : |a ⬝ᵥ z| ≤ IAFTRL.setNorm X z :=
  le_csSup (hX.image (cont_absdot z)).bddAbove ⟨a, ha, rfl⟩

lemma dot_linear (z : Fin d → ℝ) : IsLinearMap ℝ (fun x : Fin d → ℝ => x ⬝ᵥ z) :=
  ⟨fun x y => add_dotProduct x y z, fun c x => smul_dotProduct c x z⟩

lemma convex_absdot (z : Fin d → ℝ) (s : ℝ) : Convex ℝ {x : Fin d → ℝ | |x ⬝ᵥ z| ≤ s} := by
  have h1 := convex_halfSpace_le (dot_linear z) s
  have h2 := convex_halfSpace_ge (dot_linear z) (-s)
  have : {x : Fin d → ℝ | |x ⬝ᵥ z| ≤ s} = {w | w ⬝ᵥ z ≤ s} ∩ {w | -s ≤ w ⬝ᵥ z} := by
    ext x; simp [abs_le, and_comm]
  rw [this]
  exact h1.inter h2

lemma empty_of_gen {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IAFTRL.IsGenerator 𝒜 ℬ) (hB : ℬ = ∅) :
    𝒜 = ∅ := by
  have := hgen.2
  rw [hB, convexHull_empty] at this
  exact subset_empty_iff.1 this

theorem setNorm_eq {𝒜 ℬ : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ)
    (hgen : IAFTRL.IsGenerator 𝒜 ℬ) (z : Fin d → ℝ) :
    IAFTRL.setNorm 𝒜 z = IAFTRL.setNorm ℬ z := by
  rcases ℬ.eq_empty_or_nonempty with hB | hB
  · simp [IAFTRL.setNorm, empty_of_gen hgen hB, hB]
  apply le_antisymm
  · refine csSup_le ((hB.mono hgen.1).image _) ?_
    rintro _ ⟨a, ha, rfl⟩
    have hconv : convexHull ℝ ℬ ⊆ {x | |x ⬝ᵥ z| ≤ IAFTRL.setNorm ℬ z} :=
      convexHull_min (fun b hb => le_setNorm hℬ hb z) (convex_absdot z _)
    exact hconv (hgen.2 ha)
  · exact csSup_le_csSup (h𝒜.image (cont_absdot z)).bddAbove (hB.image _) (Set.image_mono hgen.1)

theorem cstar_eq {𝒜 ℬ : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ)
    (hgen : IAFTRL.IsGenerator 𝒜 ℬ) (θ astar : Fin d → ℝ) :
    IAFTRL.cstarCtr 𝒜 θ astar = IAFTRL.cstarCtr ℬ θ astar := by
  unfold IAFTRL.cstarCtr
  congr 1
  ext v
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨n', hn', hc⟩ := transfer h𝒜 hℬ.isClosed hgen hn
    exact ⟨n', hn', hc⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, alloc_of_gen hgen hn, rfl⟩

lemma meas_dot {Ω : Type*} [MeasurableSpace Ω] {f g : Ω → Fin d → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun ω => f ω ⬝ᵥ g ω := by
  simp only [dotProduct]
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hf).mul ((measurable_pi_apply i).comp hg)

theorem regret_eq {𝒜 ℬ : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) (hgen : IAFTRL.IsGenerator 𝒜 ℬ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
    (R : IAFTRL.GRun d Ω) (hR : ∀ t < T, Measurable (R.A t) ∧ Measurable (R.θs t) ∧
        (∀ ω, R.A t ω ∈ ℬ) ∧ ∀ ω, IAFTRL.setNorm 𝒜 (R.θs t ω) ≤ 1) :
    sSup (IAFTRL.gRegretVs P T R '' 𝒜) = sSup (IAFTRL.gRegretVs P T R '' ℬ) := by
  rcases ℬ.eq_empty_or_nonempty with hB | hB
  · simp [empty_of_gen hgen hB, hB]
  set f := IAFTRL.gRegretVs P T R with hf
  -- the comparators with bounded losses
  let D : Set (Fin d → ℝ) := {x | ∀ t < T, ∀ ω, |x ⬝ᵥ R.θs t ω| ≤ 1}
  have hD : Convex ℝ D := by
    have : D = ⋂ t ∈ Finset.range T, ⋂ ω, {x | |x ⬝ᵥ R.θs t ω| ≤ 1} := by
      ext x; simp [D]
    rw [this]
    exact convex_iInter₂ fun t _ => convex_iInter fun ω => convex_absdot _ _
  have h𝒜D : 𝒜 ⊆ D := fun a ha t ht ω => (le_setNorm h𝒜 ha _).trans ((hR t ht).2.2.2 ω)
  have hAD : ∀ t < T, ∀ ω, R.A t ω ∈ D := fun t ht ω => h𝒜D (hgen.1 ((hR t ht).2.2.1 ω))
  have hterm : ∀ x ∈ D, ∀ t < T, ∀ ω, |(R.A t ω - x) ⬝ᵥ R.θs t ω| ≤ 2 := by
    intro x hx t ht ω
    rw [sub_dotProduct]
    have h1 := hAD t ht ω t ht ω
    have h2 := hx t ht ω
    calc |R.A t ω ⬝ᵥ R.θs t ω - x ⬝ᵥ R.θs t ω|
        ≤ |R.A t ω ⬝ᵥ R.θs t ω| + |x ⬝ᵥ R.θs t ω| := abs_sub _ _
      _ ≤ 2 := by linarith
  have hbound : ∀ x ∈ D, ∀ ω,
      ‖∑ t ∈ Finset.range T, (R.A t ω - x) ⬝ᵥ R.θs t ω‖ ≤ 2 * T := by
    intro x hx ω
    refine (norm_sum_le _ _).trans ?_
    calc ∑ t ∈ Finset.range T, ‖(R.A t ω - x) ⬝ᵥ R.θs t ω‖
        ≤ ∑ t ∈ Finset.range T, (2 : ℝ) :=
          Finset.sum_le_sum fun t ht => by
            rw [Real.norm_eq_abs]; exact hterm x hx t (Finset.mem_range.1 ht) ω
      _ = 2 * T := by simp [mul_comm]
  have hint : ∀ x ∈ D,
      Integrable (fun ω => ∑ t ∈ Finset.range T, (R.A t ω - x) ⬝ᵥ R.θs t ω) P := by
    intro x hx
    have hm : Measurable fun ω => ∑ t ∈ Finset.range T, (R.A t ω - x) ⬝ᵥ R.θs t ω :=
      Finset.measurable_sum _ fun t ht =>
        meas_dot (((hR t (Finset.mem_range.1 ht)).1).sub measurable_const)
          (hR t (Finset.mem_range.1 ht)).2.1
    exact Integrable.of_bound hm.aestronglyMeasurable (2 * T) (ae_of_all _ (hbound x hx))
  have hfb : ∀ x ∈ D, |f x| ≤ 2 * T := by
    intro x hx
    have := norm_integral_le_of_norm_le_const (μ := P) (ae_of_all _ (hbound x hx))
    simpa [hf, IAFTRL.gRegretVs, measureReal_def] using this
  have hbddB : BddAbove (f '' ℬ) := ⟨2 * T, by
    rintro _ ⟨b, hb, rfl⟩; exact (le_abs_self _).trans (hfb b (h𝒜D (hgen.1 hb)))⟩
  have hbddA : BddAbove (f '' 𝒜) := ⟨2 * T, by
    rintro _ ⟨b, hb, rfl⟩; exact (le_abs_self _).trans (hfb b (h𝒜D hb))⟩
  -- affinity of the regret in the comparator
  have haff : ∀ x ∈ D, ∀ y ∈ D, ∀ a b : ℝ, a + b = 1 →
      f (a • x + b • y) = a * f x + b * f y := by
    intro x hx y hy a b hab
    simp only [hf, IAFTRL.gRegretVs]
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hint x hx).const_mul a)
      ((hint y hy).const_mul b)]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [sub_dotProduct, add_dotProduct, smul_dotProduct, smul_eq_mul]
    linear_combination (-(R.A t ω ⬝ᵥ R.θs t ω)) * hab
  set s := sSup (f '' ℬ) with hs
  let Q : Set (Fin d → ℝ) := {x | x ∈ D ∧ f x ≤ s}
  have hQ : Convex ℝ Q := by
    rintro x ⟨hxD, hxs⟩ y ⟨hyD, hys⟩ a b ha hb hab
    refine ⟨hD hxD hyD ha hb hab, ?_⟩
    show f (a • x + b • y) ≤ s
    rw [haff x hxD y hyD a b hab]
    calc a * f x + b * f y ≤ a * s + b * s :=
          add_le_add (mul_le_mul_of_nonneg_left hxs ha) (mul_le_mul_of_nonneg_left hys hb)
      _ = s := by rw [← add_mul, hab, one_mul]
  have hℬQ : ℬ ⊆ Q := fun b hb => ⟨h𝒜D (hgen.1 hb), le_csSup hbddB ⟨b, hb, rfl⟩⟩
  have h𝒜Q : 𝒜 ⊆ Q := hgen.2.trans (convexHull_min hℬQ hQ)
  apply le_antisymm
  · refine csSup_le ((hB.mono hgen.1).image _) ?_
    rintro _ ⟨a, ha, rfl⟩
    exact (h𝒜Q ha).2
  · exact csSup_le_csSup hbddA (hB.image _) (Set.image_mono hgen.1)

end T31

namespace IAFTRL

open MeasureTheory

theorem _root_.solution {d : ℕ} (𝒜 ℬ : Set (Fin d → ℝ)) (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ)
    (hgen : IsGenerator 𝒜 ℬ) :
    (∀ z : Fin d → ℝ, setNorm 𝒜 z = setNorm ℬ z) ∧
    (∀ θ astar : Fin d → ℝ, astar ∈ 𝒜 → (∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ) →
      cstarCtr 𝒜 θ astar = cstarCtr ℬ θ astar) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
      (R : GRun d Ω), (∀ t < T, Measurable (R.A t) ∧ Measurable (R.θs t) ∧
        (∀ ω, R.A t ω ∈ ℬ) ∧ ∀ ω, setNorm 𝒜 (R.θs t ω) ≤ 1) →
      sSup (gRegretVs P T R '' 𝒜) = sSup (gRegretVs P T R '' ℬ)) :=
  ⟨T31.setNorm_eq h𝒜 hℬ hgen, fun θ astar _ _ => T31.cstar_eq h𝒜 hℬ hgen θ astar,
    fun P _ T R hR => T31.regret_eq h𝒜 hgen P T R hR⟩

end IAFTRL
