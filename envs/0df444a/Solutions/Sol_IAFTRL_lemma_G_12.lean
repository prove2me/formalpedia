-- Prove2me | solution 1 for IAFTRL.lemma_G_12
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-17T13:19:48.09066+00:00
-- url     : https://prove2.me/submissions/bebe065c-f766-4a28-abfc-10eff5272645

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

-- ===== G1/G12 =====

/-! ### Lemma G.12: every sharp optimal action is a reference atom -/

open MeasureTheory Set IAFTRL

namespace G12

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


lemma lexMinimizer_min {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) (hne : ℬ.Nonempty)
    (v : Fin d → ℝ) : lexMinimizer ℬ v ∈ ℬ ∧ ∀ a ∈ ℬ, lexMinimizer ℬ v ⬝ᵥ v ≤ a ⬝ᵥ v := by
  have hc : Continuous fun x : Fin d → ℝ => x ⬝ᵥ v := by
    simp only [dotProduct]; fun_prop
  obtain ⟨b₀, hb₀, hmin⟩ := hℬ.exists_isMinOn hne hc.continuousOn
  set M := ℬ ∩ {b | b ⬝ᵥ v ≤ b₀ ⬝ᵥ v} with hM
  have hMc : IsCompact M := hℬ.inter_right (isClosed_le hc continuous_const)
  obtain ⟨b, ⟨hbℬ, hbv⟩, hlex⟩ := G2L.lex_min_exists hMc
    ⟨b₀, hb₀, show b₀ ⬝ᵥ v ≤ b₀ ⬝ᵥ v from le_refl _⟩
  have h : ∃ b ∈ ℬ, (∀ a ∈ ℬ, b ⬝ᵥ v ≤ a ⬝ᵥ v) ∧
      ∀ b' ∈ ℬ, (∀ a ∈ ℬ, b' ⬝ᵥ v ≤ a ⬝ᵥ v) → toLex b ≤ toLex b' :=
    ⟨b, hbℬ, fun a ha => le_trans hbv (hmin ha),
      fun b' hb' hb'min => hlex b' ⟨hb', hb'min b₀ hb₀⟩⟩
  unfold lexMinimizer
  rw [dif_pos h]
  exact ⟨(Classical.choose_spec h).1, (Classical.choose_spec h).2.1⟩

/-- **Lemma G.12.** -/
theorem atom {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ)
    (hgen : IsGenerator 𝒜 ℬ) (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤)
    (he : Function.Surjective e) {θ astar : Fin d → ℝ} (hastar : astar ∈ 𝒜)
    (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ) (hsharp : IsSharp 𝒜 θ astar) :
    ∃ m ∈ Jset ℬ e, cand ℬ e m = astar := by
  classical
  obtain ⟨ς, hς, hsh⟩ := hsharp
  have hne : 𝒜.Nonempty := ⟨astar, hastar⟩
  have hastarB := astar_mem_gen hgen hastar huniq
  have hBne : ℬ.Nonempty := ⟨astar, hastarB⟩
  have hconv : convexHull ℝ ℬ = convexHull ℝ 𝒜 :=
    (convexHull_mono hgen.1).antisymm (convexHull_min hgen.2 (convex_convexHull ℝ ℬ))
  -- a rational direction close to `θ`
  have hd0 : (0 : ℝ) < d + 1 := by positivity
  have hδ : 0 < ς / (2 * (d + 1)) := by positivity
  have hq : ∃ q : Fin d → ℚ, ∀ i, |(q i : ℝ) - θ i| < ς / (2 * (d + 1)) := by
    refine ⟨fun i => Classical.choose (exists_rat_btwn (show θ i < θ i + ς / (2 * (d + 1)) by
      linarith)), fun i => ?_⟩
    have h := Classical.choose_spec (exists_rat_btwn (show θ i < θ i + ς / (2 * (d + 1)) by
      linarith))
    rw [abs_lt]; constructor <;> linarith [h.1, h.2]
  obtain ⟨q, hq⟩ := hq
  set qr : Fin d → ℝ := fun i => (q i : ℝ) with hqr
  -- the perturbation is small in the action seminorm
  have hsmall : setNorm 𝒜 (qr - θ) ≤ ς / 2 := by
    refine csSup_le (hne.image _) ?_
    rintro _ ⟨a, ha, rfl⟩
    have ha1 : ∀ i, |a i| ≤ 1 := by
      intro i
      have : a i * a i ≤ a ⬝ᵥ a :=
        Finset.single_le_sum (f := fun j => a j * a j) (fun j _ => mul_self_nonneg _)
          (Finset.mem_univ i)
      have := hball a ha
      nlinarith [abs_mul_abs_self (a i), abs_nonneg (a i)]
    simp only [dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |a i * (qr - θ) i| ≤ ∑ _i : Fin d, ς / (2 * (d + 1)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          have := hq i
          calc |a i| * |(qr - θ) i| ≤ 1 * (ς / (2 * (d + 1))) :=
                mul_le_mul (ha1 i) (by simpa [hqr] using this.le) (abs_nonneg _) zero_le_one
            _ = _ := one_mul _
      _ = d * (ς / (2 * (d + 1))) := by simp
      _ ≤ ς / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  -- `a*` is the unique minimizer of `a ↦ aᵀq` on `ℬ`
  have hstrict : ∀ b ∈ ℬ, b ≠ astar → astar ⬝ᵥ qr < b ⬝ᵥ qr := by
    intro b hb hne'
    have hbK : b ∈ Kset 𝒜 := by
      show b ∈ convexHull ℝ 𝒜; rw [← hconv]; exact subset_convexHull ℝ ℬ hb
    have h1 := hsh b hbK
    have hg : 0 < sNorm 𝒜 (b - astar) := by
      have h2 := T31.norm_le_sNorm hne hspan hball (b - astar)
      have : 0 < ‖b - astar‖ := norm_pos_iff.2 (sub_ne_zero.2 hne')
      linarith
    have h3 := dual_le h𝒜 hne hspan (b - astar) (qr - θ)
    have h4 : (b - astar) ⬝ᵥ qr = (b - astar) ⬝ᵥ θ + (b - astar) ⬝ᵥ (qr - θ) := by
      rw [dotProduct_sub]; ring
    have h5 := neg_abs_le ((b - astar) ⬝ᵥ (qr - θ))
    have h6 : sNorm 𝒜 (b - astar) * setNorm 𝒜 (qr - θ) ≤ sNorm 𝒜 (b - astar) * (ς / 2) :=
      mul_le_mul_of_nonneg_left hsmall hg.le
    have : 0 < (b - astar) ⬝ᵥ qr := by nlinarith
    rw [sub_dotProduct] at this
    linarith
  -- the enumeration reaches `q`
  obtain ⟨m, hm⟩ := he q
  have hcand : ∀ k, (∀ i, (e k i : ℝ) = qr i) → cand ℬ e k = astar := by
    intro k hk
    have hv : (fun i => (e k i : ℝ)) = qr := funext hk
    obtain ⟨hmem, hmin⟩ := lexMinimizer_min hℬ hBne (fun i => (e k i : ℝ))
    unfold cand
    rw [hv] at hmem hmin ⊢
    by_contra hneq
    exact absurd (hmin astar hastarB) (not_le.2 (hstrict _ hmem hneq))
  have hex : ∃ k, cand ℬ e k = astar := ⟨m, hcand m fun i => by rw [hm]⟩
  refine ⟨Nat.find hex, fun i hi => ?_, Nat.find_spec hex⟩
  rw [Nat.find_spec hex]
  exact Nat.find_min hex hi

end G12

namespace IAFTRL

open MeasureTheory

theorem _root_.solution {d : ℕ} (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤)
    (he : Function.Surjective e) (θ astar : Fin d → ℝ) (hastar : astar ∈ 𝒜)
    (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ) (hsharp : IsSharp 𝒜 θ astar) :
    ∃ m ∈ Jset ℬ e, cand ℬ e m = astar :=
  G12.atom h𝒜 hℬ hgen hball hspan he hastar huniq hsharp

end IAFTRL
