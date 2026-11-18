-- Prove2me | solution 1 for IAFTRL.proposition_G_1
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-17T13:17:54.43961+00:00
-- url     : https://prove2.me/submissions/70d4b80e-0838-4a72-9744-928a7a9f5316

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Theorems.Thm_IAFTRL_proposition_G_1_anc
import Theorems.Thm_IAFTRL_proposition_G_2

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

-- ===== G1/Red =====

/-! ### Proposition G.1 from the bound at `a*` and the adversarial bound -/

open MeasureTheory Set IAFTRL

namespace G1R

variable {d : ℕ}

lemma le_setNorm {X : Set (Fin d → ℝ)} (hX : IsCompact X) {a : Fin d → ℝ} (ha : a ∈ X)
    (z : Fin d → ℝ) : |a ⬝ᵥ z| ≤ setNorm X z := by
  have hc : Continuous fun a : Fin d → ℝ => |a ⬝ᵥ z| := by
    simp only [dotProduct]; fun_prop
  exact le_csSup (hX.image hc).bddAbove ⟨a, ha, rfl⟩

lemma convex_absdot (z : Fin d → ℝ) (s : ℝ) : Convex ℝ {x : Fin d → ℝ | |x ⬝ᵥ z| ≤ s} := by
  have hl : IsLinearMap ℝ (fun x : Fin d → ℝ => x ⬝ᵥ z) :=
    ⟨fun x y => add_dotProduct x y z, fun c x => smul_dotProduct c x z⟩
  have : {x : Fin d → ℝ | |x ⬝ᵥ z| ≤ s} = {w | w ⬝ᵥ z ≤ s} ∩ {w | -s ≤ w ⬝ᵥ z} := by
    ext x; simp [abs_le, and_comm]
  rw [this]
  exact (convex_halfSpace_le hl s).inter (convex_halfSpace_ge hl (-s))

/-- on the symmetric hull the losses are bounded by the action seminorm -/
lemma abs_dot_Sset {𝒜 : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) (z : Fin d → ℝ) :
    ∀ s ∈ Sset 𝒜, |s ⬝ᵥ z| ≤ setNorm 𝒜 z := by
  refine fun s hs => convexHull_min ?_ (convex_absdot z _) hs
  rintro x (hx | hx)
  · exact le_setNorm h𝒜 hx z
  · have := le_setNorm h𝒜 (show -x ∈ 𝒜 from hx) z
    rwa [neg_dotProduct, abs_neg] at this

/-- the gauge of `𝒮` and the action seminorm are dual -/
lemma dual_le {𝒜 : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) (hne : 𝒜.Nonempty)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) (x z : Fin d → ℝ) :
    |x ⬝ᵥ z| ≤ sNorm 𝒜 x * setNorm 𝒜 z := by
  have habs : Absorbent ℝ (Sset 𝒜) := absorbent_nhds_zero (T31.Sset_nhds hne hspan)
  obtain ⟨a, ha⟩ := hne
  have hN : 0 ≤ setNorm 𝒜 z := le_trans (abs_nonneg _) (le_setNorm h𝒜 ha z)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hlt : sNorm 𝒜 x < sNorm 𝒜 x + ε / (setNorm 𝒜 z + 1) := by
    have : 0 < ε / (setNorm 𝒜 z + 1) := by positivity
    linarith
  obtain ⟨b, hb0, hblt, hxb⟩ := exists_lt_of_gauge_lt habs hlt
  obtain ⟨s, hs, rfl⟩ := hxb
  rw [smul_dotProduct, smul_eq_mul, abs_mul, abs_of_pos hb0]
  have h1 := abs_dot_Sset h𝒜 z s hs
  calc b * |s ⬝ᵥ z| ≤ b * setNorm 𝒜 z := mul_le_mul_of_nonneg_left h1 hb0.le
    _ ≤ (sNorm 𝒜 (b • s) + ε / (setNorm 𝒜 z + 1)) * setNorm 𝒜 z :=
        mul_le_mul_of_nonneg_right hblt.le hN
    _ = sNorm 𝒜 (b • s) * setNorm 𝒜 z + ε * (setNorm 𝒜 z / (setNorm 𝒜 z + 1)) := by ring
    _ ≤ sNorm 𝒜 (b • s) * setNorm 𝒜 z + ε * 1 := by
        gcongr
        rw [div_le_one (by linarith)]; linarith
    _ = _ := by ring

/-- losses on the convex hull are bounded by the action seminorm -/
lemma abs_dot_hull {𝒜 : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) {z x : Fin d → ℝ}
    (hx : x ∈ convexHull ℝ 𝒜) : |x ⬝ᵥ z| ≤ setNorm 𝒜 z :=
  convexHull_min (fun a ha => le_setNorm h𝒜 ha z) (convex_absdot z _) hx

lemma meas_dot {Ω : Type*} [MeasurableSpace Ω] {f g : Ω → Fin d → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun ω => f ω ⬝ᵥ g ω := by
  simp only [dotProduct]
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hf).mul ((measurable_pi_apply i).comp hg)

/-- **The late branch (G.23)–(G.28).** -/
lemma late_branch {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} (h𝒜 : IsCompact 𝒜)
    (hgen : IsGenerator 𝒜 ℬ) (hspan : Submodule.span ℝ 𝒜 = ⊤) {θ astar : Fin d → ℝ}
    (hastar : astar ∈ 𝒜) {ς : ℝ} (hς : 0 < ς)
    (hsh : ∀ a ∈ Kset 𝒜, ς * sNorm 𝒜 (a - astar) ≤ (a - astar) ⬝ᵥ θ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {T : ℕ} {C : ℝ}
    {R : GRun d Ω} (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (hcor : IsCorruptedG P 𝒜 θ C T R)
    (hTC : C ≤ T * ς) {u : Fin d → ℝ} (hu : u ∈ 𝒜) :
    gRegretVs P T R u ≤ gRegretVs P T R astar := by
  have hne : 𝒜.Nonempty := ⟨astar, hastar⟩
  have hb : ∀ t < T, ∀ ω, ∀ v ∈ 𝒜, |(R.A t ω - v) ⬝ᵥ R.θs t ω| ≤ 2 := by
    intro t ht ω v hv
    obtain ⟨-, -, -, ⟨hA, -⟩, -, hθ⟩ := hR t ht
    rw [sub_dotProduct]
    have h1 := (le_setNorm h𝒜 (hgen.1 (hA ω)) (R.θs t ω)).trans (hθ ω)
    have h2 := (le_setNorm h𝒜 hv (R.θs t ω)).trans (hθ ω)
    calc |R.A t ω ⬝ᵥ R.θs t ω - v ⬝ᵥ R.θs t ω|
        ≤ |R.A t ω ⬝ᵥ R.θs t ω| + |v ⬝ᵥ R.θs t ω| := abs_sub _ _
      _ ≤ 2 := by linarith
  have hint : ∀ v ∈ 𝒜, Integrable (fun ω => ∑ t ∈ Finset.range T, (R.A t ω - v) ⬝ᵥ R.θs t ω) P := by
    intro v hv
    refine integrable_finsetSum _ fun t ht => ?_
    have ht' := Finset.mem_range.1 ht
    exact Integrable.of_bound (meas_dot ((hR t ht').1.2.1.sub measurable_const)
      (hR t ht').1.2.2.2.1).aestronglyMeasurable 2
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hb t ht' ω v hv)
  unfold gRegretVs
  refine integral_mono_ae (hint u hu) (hint astar hastar) ?_
  filter_upwards [hcor.2] with ω hω
  set g := sNorm 𝒜 (u - astar)
  have hg0 : 0 ≤ g := gauge_nonneg _
  have huK : u ∈ Kset 𝒜 := subset_convexHull ℝ 𝒜 hu
  have hΔ := hsh u huK
  have hstep : ∀ t ∈ Finset.range T, (R.A t ω - u) ⬝ᵥ R.θs t ω ≤
      (R.A t ω - astar) ⬝ᵥ R.θs t ω - ς * g + g * setNorm 𝒜 (R.θs t ω - θ) := by
    intro t _
    have hd := dual_le h𝒜 hne hspan (u - astar) (R.θs t ω - θ)
    have heq : (R.A t ω - u) ⬝ᵥ R.θs t ω = (R.A t ω - astar) ⬝ᵥ R.θs t ω -
        (u - astar) ⬝ᵥ θ - (u - astar) ⬝ᵥ (R.θs t ω - θ) := by
      simp only [sub_dotProduct, dotProduct_sub]; ring
    rw [heq]
    have := neg_abs_le ((u - astar) ⬝ᵥ (R.θs t ω - θ))
    nlinarith
  calc ∑ t ∈ Finset.range T, (R.A t ω - u) ⬝ᵥ R.θs t ω
      ≤ ∑ t ∈ Finset.range T, ((R.A t ω - astar) ⬝ᵥ R.θs t ω - ς * g +
          g * setNorm 𝒜 (R.θs t ω - θ)) := Finset.sum_le_sum hstep
    _ = ∑ t ∈ Finset.range T, (R.A t ω - astar) ⬝ᵥ R.θs t ω +
          g * (∑ t ∈ Finset.range T, setNorm 𝒜 (R.θs t ω - θ) - T * ς) := by
        simp only [mul_sub, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ ∑ t ∈ Finset.range T, (R.A t ω - astar) ⬝ᵥ R.θs t ω := by
        have : ∑ t ∈ Finset.range T, setNorm 𝒜 (R.θs t ω - θ) - T * ς ≤ 0 := by linarith
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hg0 this]

/-- **The early-branch scalar bound (G.29)–(G.31).** -/
lemma early_scalar {T : ℕ} (hT : 1 ≤ T) {ς C : ℝ} (hς : 0 < ς) (hTC : T * ς < C) :
    Real.sqrt T * Real.log (Real.exp 1 * T) ≤
      (2 + Real.log (1 + ς⁻¹)) / Real.sqrt ς * (Real.sqrt C * Real.log (Real.exp 1 + C)) := by
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hC : 0 < C := lt_of_le_of_lt (by positivity) hTC
  have hTle : (T : ℝ) ≤ C / ς := by rw [le_div_iff₀ hς]; linarith
  have hsq : Real.sqrt T ≤ Real.sqrt C / Real.sqrt ς := by
    rw [← Real.sqrt_div hC.le]; exact Real.sqrt_le_sqrt hTle
  have hL : 1 ≤ Real.log (Real.exp 1 + C) := by
    rw [Real.le_log_iff_exp_le (by positivity)]; linarith [Real.exp_pos 1]
  have hlogC : Real.log C ≤ Real.log (Real.exp 1 + C) :=
    Real.log_le_log hC (by linarith [Real.exp_pos 1])
  have hlogς : Real.log ς⁻¹ ≤ Real.log (1 + ς⁻¹) :=
    Real.log_le_log (inv_pos.2 hς) (by linarith)
  have hlog1 : 0 ≤ Real.log (1 + ς⁻¹) :=
    Real.log_nonneg (by linarith [inv_pos.2 hς])
  have hlogeT : Real.log (Real.exp 1 * T) ≤ (2 + Real.log (1 + ς⁻¹)) * Real.log (Real.exp 1 + C) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
    have hlT : Real.log T ≤ Real.log C + Real.log ς⁻¹ := by
      rw [← Real.log_mul hC.ne' (inv_pos.2 hς).ne']
      exact Real.log_le_log (by positivity) (by rw [← div_eq_mul_inv]; exact hTle)
    nlinarith
  have hsT : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  have hleT : 0 ≤ Real.log (Real.exp 1 * T) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
    linarith [Real.log_nonneg hT1]
  calc Real.sqrt T * Real.log (Real.exp 1 * T)
      ≤ (Real.sqrt C / Real.sqrt ς) * ((2 + Real.log (1 + ς⁻¹)) * Real.log (Real.exp 1 + C)) :=
        mul_le_mul hsq hlogeT hleT (by positivity)
    _ = _ := by ring

end G1R

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
        ∀ u ∈ 𝒜, gRegretVs P T R u ≤
          16 * gB d * 64 ^ 4 * ctrCost θ astar n * Real.log (Real.exp 1 * T) + M +
            J * Real.sqrt C * Real.log (Real.exp 1 + C) := by
  obtain ⟨ς, hς, hsh⟩ := id hsharp
  obtain ⟨J0, hJ0⟩ := proposition_G_1_anc hd 𝒜 ℬ e h𝒜 hℬ hgen hball hspan hk he θ astar hθ
    hastar huniq hsharp
  set K0 : ℝ := 320 * ((d : ℝ) + 1) * ((2 + Real.log (1 + ς⁻¹)) / Real.sqrt ς) with hK0def
  have hK0 : 0 ≤ K0 := by
    have : 0 ≤ Real.log (1 + ς⁻¹) := Real.log_nonneg (by linarith [inv_pos.2 hς])
    positivity
  refine ⟨|J0| + K0, fun n hn => ?_⟩
  obtain ⟨M0, hM0⟩ := hJ0 n hn
  have hcost : 0 ≤ ctrCost θ astar n := by
    obtain ⟨_, hsupp, _, _⟩ := hn
    refine integral_nonneg_of_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hsupp] with a ha
    have ha' : a ∈ 𝒜 := hgen.1 (by simpa using ha)
    show (0 : ℝ) ≤ (a - astar) ⬝ᵥ θ
    rw [sub_dotProduct]
    by_cases h : a = astar
    · simp [h]
    · linarith [huniq a ha' h]
  refine ⟨max M0 0, ?_⟩
  intro Ω _ P _ T C R hT hC hR hcor u hu
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hlogeT : 0 ≤ Real.log (Real.exp 1 * T) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
    linarith [Real.log_nonneg hT1]
  have hL : 0 ≤ Real.log (Real.exp 1 + C) :=
    Real.log_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have hX : 0 ≤ Real.sqrt C * Real.log (Real.exp 1 + C) := mul_nonneg (Real.sqrt_nonneg _) hL
  have hfirst : 0 ≤ 16 * gB d * 64 ^ 4 * ctrCost θ astar n * Real.log (Real.exp 1 * T) := by
    have : 0 ≤ gB d := by unfold gB; positivity
    positivity
  have hJ : J0 * Real.sqrt C * Real.log (Real.exp 1 + C) ≤
      (|J0| + K0) * Real.sqrt C * Real.log (Real.exp 1 + C) := by
    have := le_abs_self J0
    nlinarith
  by_cases hTC : C ≤ T * ς
  · -- late branch
    have h1 := G1R.late_branch h𝒜 hgen hspan hastar hς hsh hR hcor hTC hu
    have h2 := hM0 P T C R hT hC hR hcor
    have h3 : M0 ≤ max M0 0 := le_max_left _ _
    linarith
  · -- early branch
    push Not at hTC
    have h1 := proposition_G_2 hd 𝒜 ℬ e h𝒜 hℬ hgen hball hspan hk he P T R hT hR u (hgen.2 hu)
    have h2 := G1R.early_scalar hT hς hTC
    have h3 : 320 * ((d : ℝ) + 1) * Real.sqrt T * Real.log (Real.exp 1 * T) ≤
        K0 * Real.sqrt C * Real.log (Real.exp 1 + C) := by
      have hd0 : 0 ≤ 320 * ((d : ℝ) + 1) := by positivity
      calc 320 * ((d : ℝ) + 1) * Real.sqrt T * Real.log (Real.exp 1 * T)
          = 320 * ((d : ℝ) + 1) * (Real.sqrt T * Real.log (Real.exp 1 * T)) := by ring
        _ ≤ 320 * ((d : ℝ) + 1) * ((2 + Real.log (1 + ς⁻¹)) / Real.sqrt ς *
            (Real.sqrt C * Real.log (Real.exp 1 + C))) := mul_le_mul_of_nonneg_left h2 hd0
        _ = K0 * Real.sqrt C * Real.log (Real.exp 1 + C) := by rw [hK0def]; ring
    have h4 : K0 * Real.sqrt C * Real.log (Real.exp 1 + C) ≤
        (|J0| + K0) * Real.sqrt C * Real.log (Real.exp 1 + C) := by
      have := abs_nonneg J0
      nlinarith
    have h5 : (0 : ℝ) ≤ max M0 0 := le_max_right _ _
    linarith

end IAFTRL
