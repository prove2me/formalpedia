-- Prove2me | solution 1 for MartOT.Var.badTuples_measurableSet
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T06:54:48.590382+00:00
-- url     : https://prove2.me/submissions/106a7b25-acc9-4f6f-8309-a6ca4e0df6da

import Mathlib
import Definitions.Def_MartOT_Var_BadTuples

open MeasureTheory MartOT.Var

namespace MOTBadAux

/-- regroup a weighted sum along the fibres of `f`. -/
lemma sum_fiber_expand {ι β R : Type*} [Fintype ι] [DecidableEq β] [CommSemiring R]
    (f : ι → β) (g : ι → R) (φ : β → R) (T : Finset β) (hT : ∀ i, f i ∈ T) :
    ∑ i, g i * φ (f i) = ∑ b ∈ T, φ b * ∑ i, (if f i = b then g i else 0) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ∀ b, φ b * (if f i = b then g i else 0) = if f i = b then g i * φ (f i) else 0 := by
    intro b; split_ifs with h
    · subst h; ring
    · simp
  simp_rw [this]
  rw [Finset.sum_ite_eq]
  simp [hT i]

lemma fiber_transfer {ι ι' β R : Type*} [Fintype ι] [Fintype ι'] [DecidableEq β] [CommSemiring R]
    (f : ι → β) (f' : ι' → β) (g : ι → R) (h : ι' → R)
    (hgh : ∀ b, ∑ i, (if f i = b then g i else 0) = ∑ j, (if f' j = b then h j else 0))
    (φ : β → R) : ∑ i, g i * φ (f i) = ∑ j, h j * φ (f' j) := by
  classical
  set T := Finset.univ.image f ∪ Finset.univ.image f'
  rw [sum_fiber_expand f g φ T (fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))),
    sum_fiber_expand f' h φ T (fun i => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))]
  simp_rw [hgh]

/-- closedness/measurability of the "exists a bad direction in the simplex" set. -/
lemma measurableSet_exists_simplex {R K : Type} [Fintype R] [Fintype K] :
    MeasurableSet {Av : (R → K → ℝ) × (K → ℝ) | ∃ z ∈ stdSimplex ℝ K,
      (∀ r, ∑ κ, Av.1 r κ * z κ = 0) ∧ ∑ κ, Av.2 κ * z κ < 0} := by
  have hset : {Av : (R → K → ℝ) × (K → ℝ) | ∃ z ∈ stdSimplex ℝ K,
      (∀ r, ∑ κ, Av.1 r κ * z κ = 0) ∧ ∑ κ, Av.2 κ * z κ < 0} =
      ⋃ m : ℕ, Prod.fst '' {q : ((R → K → ℝ) × (K → ℝ)) × stdSimplex ℝ K |
        (∀ r, ∑ κ, q.1.1 r κ * (q.2 : K → ℝ) κ = 0) ∧
          ∑ κ, q.1.2 κ * (q.2 : K → ℝ) κ ≤ -(1 / ((m : ℝ) + 1))} := by
    ext Av
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, Prod.exists, Subtype.exists,
      exists_and_right, exists_eq_right]
    constructor
    · rintro ⟨z, hz, h1, h2⟩
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (neg_pos.2 h2)
      refine ⟨m, z, hz, h1, ?_⟩
      show ∑ κ, Av.2 κ * z κ ≤ _
      linarith
    · rintro ⟨m, z, hz, h1, h2⟩
      refine ⟨z, hz, h1, lt_of_le_of_lt h2 ?_⟩
      have : (0:ℝ) < 1 / ((m:ℝ) + 1) := by positivity
      linarith
  rw [hset]
  refine MeasurableSet.iUnion fun m => ?_
  have : CompactSpace (stdSimplex ℝ K) := isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ K)
  refine IsClosed.measurableSet (isClosedMap_fst_of_compactSpace _ ?_)
  have hc1 : ∀ r, Continuous fun q : ((R → K → ℝ) × (K → ℝ)) × stdSimplex ℝ K =>
      ∑ κ, q.1.1 r κ * (q.2 : K → ℝ) κ := fun r =>
    continuous_finset_sum _ fun κ _ =>
      ((continuous_apply κ).comp ((continuous_apply r).comp (continuous_fst.comp continuous_fst))).mul
        ((continuous_apply κ).comp (continuous_subtype_val.comp continuous_snd))
  have hc2 : Continuous fun q : ((R → K → ℝ) × (K → ℝ)) × stdSimplex ℝ K =>
      ∑ κ, q.1.2 κ * (q.2 : K → ℝ) κ :=
    continuous_finset_sum _ fun κ _ =>
      ((continuous_apply κ).comp (continuous_snd.comp continuous_fst)).mul
        ((continuous_apply κ).comp (continuous_subtype_val.comp continuous_snd))
  have : {q : ((R → K → ℝ) × (K → ℝ)) × stdSimplex ℝ K |
        (∀ r, ∑ κ, q.1.1 r κ * (q.2 : K → ℝ) κ = 0) ∧
          ∑ κ, q.1.2 κ * (q.2 : K → ℝ) κ ≤ -(1 / ((m : ℝ) + 1))} =
      (⋂ r, {q | ∑ κ, q.1.1 r κ * (q.2 : K → ℝ) κ = 0}) ∩
        {q | ∑ κ, q.1.2 κ * (q.2 : K → ℝ) κ ≤ -(1 / ((m : ℝ) + 1))} := by
    ext q; simp
  rw [this]
  exact (isClosed_iInter fun r => isClosed_eq (hc1 r) continuous_const).inter
    (isClosed_le hc2 continuous_const)

/-- a finite weighted sum of Dirac masses. -/
noncomputable def D {ι : Type} [Fintype ι] (u : ι → NNReal) (q : ι → ℝ × ℝ) : Measure (ℝ × ℝ) :=
  ∑ i, (u i : ENNReal) • Measure.dirac (q i)

lemma D_apply {ι : Type} [Fintype ι] (u : ι → NNReal) (q : ι → ℝ × ℝ) {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) : D u q s = ∑ i, (u i : ENNReal) * s.indicator 1 (q i) := by
  simp [D, Measure.finsetSum_apply, Measure.dirac_apply' _ hs]
  rfl

lemma D_univ {ι : Type} [Fintype ι] (u : ι → NNReal) (q : ι → ℝ × ℝ) :
    D u q Set.univ = ((∑ i, u i : NNReal) : ENNReal) := by
  rw [D_apply u q MeasurableSet.univ]; simp

instance D_finite {ι : Type} [Fintype ι] (u : ι → NNReal) (q : ι → ℝ × ℝ) :
    IsFiniteMeasure (D u q) := ⟨by rw [D_univ]; exact ENNReal.coe_lt_top⟩

lemma integrable_D {ι : Type} [Fintype ι] (u : ι → NNReal) (q : ι → ℝ × ℝ) (f : ℝ × ℝ → ℝ) :
    Integrable f (D u q) := by
  unfold D
  refine integrable_finsetSum_measure.2 fun i _ => ?_
  exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.coe_ne_top

lemma integral_D {ι : Type} [Fintype ι] (u : ι → NNReal) (q : ι → ℝ × ℝ) (f : ℝ × ℝ → ℝ) :
    ∫ p, f p ∂(D u q) = ∑ i, (u i : ℝ) * f (q i) := by
  unfold D
  rw [integral_finsetSum_measure fun i _ =>
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.coe_ne_top]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac]
  simp

lemma cost_D {ι : Type} [Fintype ι] (c : ℝ → ℝ → ℝ) (u : ι → NNReal) (q : ι → ℝ × ℝ) :
    cost c (D u q) = ((∑ i, (u i : ℝ) * c (q i).1 (q i).2 : ℝ) : EReal) := by
  have hP : ∀ g : ℝ × ℝ → ℝ, ∫⁻ p, ENNReal.ofReal (g p) ∂(D u q) =
      ∑ i, (u i : ENNReal) * ENNReal.ofReal (g (q i)) := by
    intro g
    unfold D
    rw [lintegral_finsetSum_measure]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_smul_measure, lintegral_dirac]
    rfl
  have e1 : cost c (D u q) = ((∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂(D u q) : ENNReal) : EReal) -
      ((∫⁻ p, ENNReal.ofReal (-c p.1 p.2) ∂(D u q) : ENNReal) : EReal) := by
    simp only [cost, integralE, ModelRiskOT.Duality.extIntegral]
    congr 3
  rw [e1, hP (fun p => c p.1 p.2), hP (fun p => -c p.1 p.2)]
  have hfin : ∀ g : ℝ × ℝ → ℝ, ∑ i, (u i : ENNReal) * ENNReal.ofReal (g (q i)) ≠ ⊤ := by
    intro g
    exact ENNReal.sum_ne_top.2 fun i _ => ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  rw [← EReal.coe_ennreal_toReal (hfin (fun p => c p.1 p.2)),
    ← EReal.coe_ennreal_toReal (hfin (fun p => -c p.1 p.2)), ← EReal.coe_sub,
    EReal.coe_eq_coe_iff]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top),
    ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal']
  rw [← mul_sub]
  congr 1
  rcases le_total 0 (c (q i).1 (q i).2) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

lemma ind_eq (u : NNReal) (g : ℝ × ℝ → ℝ) (a : ℝ × ℝ) (b : ℝ) :
    (u : ENNReal) * Set.indicator (g ⁻¹' {b}) 1 a = ((if g a = b then u else 0 : NNReal) : ENNReal) := by
  by_cases h : g a = b <;> simp [Set.indicator, h]

lemma map_D_singleton {ι : Type} [Fintype ι] (u : ι → NNReal) (q : ι → ℝ × ℝ) (g : ℝ × ℝ → ℝ)
    (hg : Measurable g) (b : ℝ) :
    (D u q).map g {b} = ((∑ i, (if g (q i) = b then u i else 0) : NNReal) : ENNReal) := by
  rw [Measure.map_apply hg (measurableSet_singleton b), D_apply u q (hg (measurableSet_singleton b))]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ind_eq]

lemma map_D_apply {ι : Type} [Fintype ι] (u : ι → NNReal) (q : ι → ℝ × ℝ) (g : ℝ × ℝ → ℝ)
    (hg : Measurable g) {s : Set ℝ} (hs : MeasurableSet s) :
    (D u q).map g s = ∑ i, (u i : ENNReal) * s.indicator 1 (g (q i)) := by
  rw [Measure.map_apply hg hs, D_apply u q (hg hs)]
  rfl

lemma nnreal_sum_eq_of_real {ι ι' : Type} [Fintype ι] [Fintype ι'] (a : ι → NNReal) (a' : ι' → NNReal)
    (h : ∑ i, (a i : ℝ) = ∑ j, (a' j : ℝ)) : ∑ i, a i = ∑ j, a' j := by
  apply NNReal.coe_injective; push_cast; exact h

lemma competitor_iff {ι ι' : Type} [Fintype ι] [Fintype ι'] (u : ι → NNReal) (q : ι → ℝ × ℝ)
    (u' : ι' → NNReal) (q' : ι' → ℝ × ℝ) :
    IsCompetitor (D u q) (D u' q') ↔
      (∀ b, ∑ i, (if (q i).1 = b then (u i : ℝ) else 0) = ∑ j, (if (q' j).1 = b then (u' j : ℝ) else 0)) ∧
      (∀ b, ∑ i, (if (q i).2 = b then (u i : ℝ) else 0) = ∑ j, (if (q' j).2 = b then (u' j : ℝ) else 0)) ∧
      (∀ b, ∑ i, (if (q i).1 = b then (u i : ℝ) * (q i).2 else 0) =
        ∑ j, (if (q' j).1 = b then (u' j : ℝ) * (q' j).2 else 0)) := by
  classical
  constructor
  · rintro ⟨h1, h2, -, -, h3⟩
    refine ⟨fun b => ?_, fun b => ?_, fun b => ?_⟩
    · have := congrArg (fun m : Measure ℝ => m {b}) h1
      simp only [map_D_singleton _ _ _ measurable_fst, ENNReal.coe_inj] at this
      have := congrArg (fun x : NNReal => (x : ℝ)) this
      push_cast [apply_ite] at this
      simpa using this
    · have := congrArg (fun m : Measure ℝ => m {b}) h2
      simp only [map_D_singleton _ _ _ measurable_snd, ENNReal.coe_inj] at this
      have := congrArg (fun x : NNReal => (x : ℝ)) this
      push_cast [apply_ite] at this
      simpa using this
    · have := h3 (Set.indicator {b} 1) (measurable_one.indicator (measurableSet_singleton b))
        ⟨1, fun x => by by_cases hx : x = b <;> simp [Set.indicator, hx]⟩
      rw [integral_D, integral_D] at this
      convert this using 2 with i _ j _
      · by_cases hx : (q i).1 = b <;> simp [Set.indicator, hx]
      · by_cases hx : (q' j).1 = b <;> simp [Set.indicator, hx]
  · rintro ⟨h1, h2, h3⟩
    have key : ∀ (g : ℝ × ℝ → ℝ), Measurable g →
        (∀ b, ∑ i, (if g (q i) = b then (u i : ℝ) else 0) =
          ∑ j, (if g (q' j) = b then (u' j : ℝ) else 0)) → (D u q).map g = (D u' q').map g := by
      intro g hg hgb
      refine Measure.ext fun s hs => ?_
      rw [map_D_apply _ _ _ hg hs, map_D_apply _ _ _ hg hs]
      refine fiber_transfer (fun i => g (q i)) (fun j => g (q' j)) (fun i => (u i : ENNReal))
        (fun j => (u' j : ENNReal)) (fun b => ?_) (s.indicator 1)
      have e : ∀ {κ : Type} [Fintype κ] (w : κ → NNReal) (r : κ → ℝ × ℝ),
          ∑ i, (if g (r i) = b then (w i : ENNReal) else 0) =
            ((∑ i, (if g (r i) = b then w i else 0) : NNReal) : ENNReal) := by
        intro κ _ w r; push_cast [apply_ite]; simp
      rw [e, e, ENNReal.coe_inj]
      apply NNReal.coe_injective
      push_cast [apply_ite]
      simpa using hgb b
    refine ⟨key _ measurable_fst h1, key _ measurable_snd h2, integrable_D _ _ _, integrable_D _ _ _,
      fun ρ hρ _ => ?_⟩
    rw [integral_D, integral_D]
    have := fiber_transfer (fun i => (q i).1) (fun j => (q' j).1) (fun i => (u i : ℝ) * (q i).2)
      (fun j => (u' j : ℝ) * (q' j).2) h3 ρ
    convert this using 2 with i _ j _ <;> ring

lemma repr {ι : Type} [Fintype ι] (m : Measure (ℝ × ℝ)) [IsFiniteMeasure m] (q : ι → ℝ × ℝ)
    (hm : m (Set.range q)ᶜ = 0) : ∃ u : ι → NNReal, m = D u q := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨fun _ => 0, ?_⟩
    have : Set.range q = ∅ := Set.range_eq_empty q
    rw [this, Set.compl_empty] at hm
    have h0 : m = 0 := Measure.measure_univ_eq_zero.1 hm
    rw [h0]; ext s hs; rw [D_apply _ _ hs]; simp
  · let u : ι → NNReal := fun i => if Function.invFun q (q i) = i then (m {q i}).toNNReal else 0
    refine ⟨u, ?_⟩
    have hfib : ∀ b ∈ Finset.univ.image q,
        ∑ i, (if q i = b then (u i : ENNReal) else 0) = m {b} := by
      intro b hb
      obtain ⟨i0, -, rfl⟩ := Finset.mem_image.1 hb
      have hk : q (Function.invFun q (q i0)) = q i0 := Function.invFun_eq ⟨i0, rfl⟩
      rw [Finset.sum_eq_single (Function.invFun q (q i0))]
      · rw [if_pos hk]
        simp only [u, hk, if_true, ENNReal.coe_toNNReal (measure_ne_top m _)]
      · intro i _ hi
        by_cases hqi : q i = q i0
        · rw [if_pos hqi]
          simp only [u, hqi]
          rw [if_neg (Ne.symm hi)]; simp
        · rw [if_neg hqi]
      · intro h; exact absurd (Finset.mem_univ _) h
    ext s hs
    rw [D_apply _ _ hs]
    have e1 := sum_fiber_expand q (fun i => (u i : ENNReal)) (s.indicator 1) (Finset.univ.image q)
      (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i))
    rw [e1, Finset.sum_congr rfl fun b hb => by rw [hfib b hb]]
    have hsr : m s = m (s ∩ Set.range q) := by
      refine le_antisymm ?_ (measure_mono Set.inter_subset_left)
      calc m s = m (s ∩ Set.range q ∪ s \ Set.range q) := by rw [Set.inter_union_diff]
        _ ≤ m (s ∩ Set.range q) + m (s \ Set.range q) := measure_union_le _ _
        _ ≤ m (s ∩ Set.range q) + m (Set.range q)ᶜ := by
            gcongr; exact Set.diff_subset_compl _ _
        _ = m (s ∩ Set.range q) := by rw [hm, add_zero]
    have hT : s ∩ Set.range q = ↑((Finset.univ.image q).filter (· ∈ s)) := by
      ext x; simp [and_comm]
    rw [hsr, hT, ← sum_measure_singleton, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b ∈ s <;> simp [Set.indicator, hb]

/-- the grid of points `(x_i, y_j)`. -/
def grid {n : ℕ} (p : Fin n → ℝ × ℝ) : Fin n × Fin n → ℝ × ℝ := fun ij => ((p ij.1).1, (p ij.2).2)

lemma grid_conc {n : ℕ} (p : Fin n → ℝ × ℝ) (α α' : Measure (ℝ × ℝ)) (hα : α (Set.range p)ᶜ = 0)
    (h1 : α.map Prod.fst = α'.map Prod.fst) (h2 : α.map Prod.snd = α'.map Prod.snd) :
    α' (Set.range (grid p))ᶜ = 0 := by
  have hX : MeasurableSet (Set.range fun i => (p i).1)ᶜ := (Set.finite_range _).measurableSet.compl
  have hY : MeasurableSet (Set.range fun i => (p i).2)ᶜ := (Set.finite_range _).measurableSet.compl
  have hsub : (Set.range (grid p))ᶜ ⊆ Prod.fst ⁻¹' (Set.range fun i => (p i).1)ᶜ ∪
      Prod.snd ⁻¹' (Set.range fun i => (p i).2)ᶜ := by
    intro a ha
    by_contra h
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, not_or, not_not] at h
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := h
    exact ha ⟨(i, j), by simp [grid, hi, hj]⟩
  have e1 : α' (Prod.fst ⁻¹' (Set.range fun i => (p i).1)ᶜ) = 0 := by
    rw [← Measure.map_apply measurable_fst hX, ← h1, Measure.map_apply measurable_fst hX]
    refine measure_mono_null ?_ hα
    intro a ha hr; obtain ⟨i, rfl⟩ := hr; exact ha ⟨i, rfl⟩
  have e2 : α' (Prod.snd ⁻¹' (Set.range fun i => (p i).2)ᶜ) = 0 := by
    rw [← Measure.map_apply measurable_snd hY, ← h2, Measure.map_apply measurable_snd hY]
    refine measure_mono_null ?_ hα
    intro a ha hr; obtain ⟨i, rfl⟩ := hr; exact ha ⟨i, rfl⟩
  exact measure_mono_null hsub (measure_union_null e1 e2)

lemma bad_iff (c : ℝ → ℝ → ℝ) (n : ℕ) (p : Fin n → ℝ × ℝ) :
    p ∈ BadTuples c n ↔ ∃ u : Fin n → NNReal, ∃ u' : Fin n × Fin n → NNReal,
      IsCompetitor (D u p) (D u' (grid p)) ∧
        ∑ j, (u' j : ℝ) * c (grid p j).1 (grid p j).2 < ∑ i, (u i : ℝ) * c (p i).1 (p i).2 := by
  constructor
  · rintro ⟨α, hαf, hαc, α', hcomp, hlt⟩
    obtain ⟨u, rfl⟩ := repr α p hαc
    have hgc := grid_conc p _ α' hαc hcomp.1 hcomp.2.1
    have : IsFiniteMeasure α' := ⟨by
      have := congrArg (fun m : Measure ℝ => m Set.univ) hcomp.1
      simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at this
      rw [← this]; exact measure_lt_top _ _⟩
    obtain ⟨u', rfl⟩ := repr α' (grid p) hgc
    refine ⟨u, u', hcomp, ?_⟩
    rw [cost_D, cost_D, EReal.coe_lt_coe_iff] at hlt
    exact hlt
  · rintro ⟨u, u', hcomp, hlt⟩
    refine ⟨D u p, inferInstance, ?_, D u' (grid p), hcomp, ?_⟩
    · rw [D_apply _ _ (Set.finite_range p).measurableSet.compl]
      simp
    · rw [cost_D, cost_D, EReal.coe_lt_coe_iff]; exact hlt

lemma forall_b_iff {ι ι' : Type} [Fintype ι] [Fintype ι'] (f : ι → ℝ) (f' : ι' → ℝ)
    (hr : ∀ j, ∃ i, f' j = f i) (g : ι → ℝ) (h : ι' → ℝ) :
    (∀ b, ∑ i, (if f i = b then g i else 0) = ∑ j, (if f' j = b then h j else 0)) ↔
      ∀ k, ∑ i, (if f i = f k then g i else 0) = ∑ j, (if f' j = f k then h j else 0) := by
  refine ⟨fun H k => H (f k), fun H b => ?_⟩
  by_cases hb : ∃ k, f k = b
  · obtain ⟨k, rfl⟩ := hb; exact H k
  · push_neg at hb
    rw [Finset.sum_eq_zero fun i _ => if_neg (hb i), Finset.sum_eq_zero fun j _ => ?_]
    obtain ⟨i, hi⟩ := hr j
    rw [if_neg (by rw [hi]; exact hb i)]

abbrev KK (n : ℕ) := Fin n ⊕ (Fin n × Fin n)
abbrev RR (n : ℕ) := Fin n ⊕ (Fin n ⊕ Fin n)

noncomputable def Amat {n : ℕ} (p : Fin n → ℝ × ℝ) : RR n → KK n → ℝ :=
  Sum.elim
    (fun k => Sum.elim (fun i => if (p i).1 = (p k).1 then 1 else 0)
      (fun ij => -(if (p ij.1).1 = (p k).1 then 1 else 0)))
    (Sum.elim
      (fun k => Sum.elim (fun i => if (p i).2 = (p k).2 then 1 else 0)
        (fun ij => -(if (p ij.2).2 = (p k).2 then 1 else 0)))
      (fun k => Sum.elim (fun i => if (p i).1 = (p k).1 then (p i).2 else 0)
        (fun ij => -(if (p ij.1).1 = (p k).1 then (p ij.2).2 else 0))))

noncomputable def vvec (c : ℝ → ℝ → ℝ) {n : ℕ} (p : Fin n → ℝ × ℝ) : KK n → ℝ :=
  Sum.elim (fun i => -c (p i).1 (p i).2) (fun ij => c (p ij.1).1 (p ij.2).2)

def W {n : ℕ} (u : Fin n → NNReal) (u' : Fin n × Fin n → NNReal) : KK n → ℝ :=
  Sum.elim (fun i => (u i : ℝ)) (fun j => (u' j : ℝ))

lemma conds_iff (c : ℝ → ℝ → ℝ) {n : ℕ} (p : Fin n → ℝ × ℝ) (u : Fin n → NNReal)
    (u' : Fin n × Fin n → NNReal) :
    (IsCompetitor (D u p) (D u' (grid p)) ∧
        ∑ j, (u' j : ℝ) * c (grid p j).1 (grid p j).2 < ∑ i, (u i : ℝ) * c (p i).1 (p i).2) ↔
      (∀ r, ∑ κ, Amat p r κ * W u u' κ = 0) ∧ ∑ κ, vvec c p κ * W u u' κ < 0 := by
  have f1 : ∀ k, ∑ κ, Amat p (Sum.inl k) κ * W u u' κ =
      ∑ i, (if (p i).1 = (p k).1 then (u i : ℝ) else 0) -
        ∑ j, (if (grid p j).1 = (p k).1 then (u' j : ℝ) else 0) := by
    intro k
    rw [Fintype.sum_sum_type, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;>
      simp only [Amat, W, grid, Sum.elim_inl, Sum.elim_inr] <;> split_ifs <;> simp_all <;> ring
  have f2 : ∀ k, ∑ κ, Amat p (Sum.inr (Sum.inl k)) κ * W u u' κ =
      ∑ i, (if (p i).2 = (p k).2 then (u i : ℝ) else 0) -
        ∑ j, (if (grid p j).2 = (p k).2 then (u' j : ℝ) else 0) := by
    intro k
    rw [Fintype.sum_sum_type, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;>
      simp only [Amat, W, grid, Sum.elim_inl, Sum.elim_inr] <;> split_ifs <;> simp_all <;> ring
  have f3 : ∀ k, ∑ κ, Amat p (Sum.inr (Sum.inr k)) κ * W u u' κ =
      ∑ i, (if (p i).1 = (p k).1 then (u i : ℝ) * (p i).2 else 0) -
        ∑ j, (if (grid p j).1 = (p k).1 then (u' j : ℝ) * (grid p j).2 else 0) := by
    intro k
    rw [Fintype.sum_sum_type, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;>
      simp only [Amat, W, grid, Sum.elim_inl, Sum.elim_inr] <;> split_ifs <;> simp_all <;> ring
  have fv : ∑ κ, vvec c p κ * W u u' κ =
      ∑ j, (u' j : ℝ) * c (grid p j).1 (grid p j).2 - ∑ i, (u i : ℝ) * c (p i).1 (p i).2 := by
    rw [Fintype.sum_sum_type, sub_eq_add_neg, ← Finset.sum_neg_distrib, add_comm]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;>
      simp only [vvec, W, grid, Sum.elim_inl, Sum.elim_inr] <;> ring
  rw [competitor_iff, fv, sub_neg]
  simp only [Sum.forall, f1, f2, f3, sub_eq_zero]
  rw [forall_b_iff (fun i => (p i).1) (fun j => (grid p j).1) (fun j => ⟨j.1, rfl⟩),
    forall_b_iff (fun i => (p i).2) (fun j => (grid p j).2) (fun j => ⟨j.2, rfl⟩),
    forall_b_iff (fun i => (p i).1) (fun j => (grid p j).1) (fun j => ⟨j.1, rfl⟩)]

lemma scale_iff {R K : Type} [Fintype R] [Fintype K] (A : R → K → ℝ) (v : K → ℝ) :
    (∃ w : K → ℝ, (∀ κ, 0 ≤ w κ) ∧ (∀ r, ∑ κ, A r κ * w κ = 0) ∧ ∑ κ, v κ * w κ < 0) ↔
      ∃ z ∈ stdSimplex ℝ K, (∀ r, ∑ κ, A r κ * z κ = 0) ∧ ∑ κ, v κ * z κ < 0 := by
  constructor
  · rintro ⟨w, hw0, hA, hv⟩
    set t := ∑ κ, w κ
    have ht : 0 < t := by
      rcases (Finset.sum_nonneg fun κ _ => hw0 κ : 0 ≤ t).lt_or_eq with h | h
      · exact h
      · exfalso
        have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun κ _ => hw0 κ).1 h.symm
        have : ∑ κ, v κ * w κ = 0 := Finset.sum_eq_zero fun κ hκ => by rw [h0 κ hκ, mul_zero]
        linarith
    refine ⟨fun κ => w κ / t, ⟨fun κ => div_nonneg (hw0 κ) ht.le, ?_⟩, fun r => ?_, ?_⟩
    · rw [← Finset.sum_div, div_self ht.ne']
    · simp_rw [mul_div_assoc', ← Finset.sum_div, hA r, zero_div]
    · simp_rw [mul_div_assoc', ← Finset.sum_div]; exact div_neg_of_neg_of_pos hv ht
  · rintro ⟨z, hz, hA, hv⟩
    exact ⟨z, hz.1, hA, hv⟩

lemma bad_iff' (c : ℝ → ℝ → ℝ) (n : ℕ) (p : Fin n → ℝ × ℝ) :
    p ∈ BadTuples c n ↔ ∃ z ∈ stdSimplex ℝ (KK n),
      (∀ r, ∑ κ, Amat p r κ * z κ = 0) ∧ ∑ κ, vvec c p κ * z κ < 0 := by
  rw [bad_iff, ← scale_iff]
  constructor
  · rintro ⟨u, u', h⟩
    refine ⟨W u u', fun κ => ?_, (conds_iff c p u u').1 h⟩
    rcases κ with i | j <;> simp [W]
  · rintro ⟨w, hw0, h⟩
    refine ⟨fun i => (w (Sum.inl i)).toNNReal, fun j => (w (Sum.inr j)).toNNReal, ?_⟩
    have hW : W (fun i => (w (Sum.inl i)).toNNReal) (fun j => (w (Sum.inr j)).toNNReal) = w := by
      funext κ; rcases κ with i | j <;> simp [W, Real.coe_toNNReal _ (hw0 _)]
    rw [conds_iff, hW]; exact h

lemma measurable_Av (c : ℝ → ℝ → ℝ) (hc : Measurable (Function.uncurry c)) (n : ℕ) :
    Measurable fun p : Fin n → ℝ × ℝ => (Amat p, vvec c p) := by
  have hx : ∀ i : Fin n, Measurable fun p : Fin n → ℝ × ℝ => (p i).1 :=
    fun i => measurable_fst.comp (measurable_pi_apply i)
  have hy : ∀ i : Fin n, Measurable fun p : Fin n → ℝ × ℝ => (p i).2 :=
    fun i => measurable_snd.comp (measurable_pi_apply i)
  refine Measurable.prodMk (measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun κ => ?_)
    (measurable_pi_iff.2 fun κ => ?_)
  · rcases r with k | k | k <;> rcases κ with i | ij <;> simp only [Amat, Sum.elim_inl, Sum.elim_inr]
    · exact Measurable.ite (measurableSet_eq_fun (hx i) (hx k)) measurable_const measurable_const
    · exact (Measurable.ite (measurableSet_eq_fun (hx ij.1) (hx k)) measurable_const
        measurable_const).neg
    · exact Measurable.ite (measurableSet_eq_fun (hy i) (hy k)) measurable_const measurable_const
    · exact (Measurable.ite (measurableSet_eq_fun (hy ij.2) (hy k)) measurable_const
        measurable_const).neg
    · exact Measurable.ite (measurableSet_eq_fun (hx i) (hx k)) (hy i) measurable_const
    · exact (Measurable.ite (measurableSet_eq_fun (hx ij.1) (hx k)) (hy ij.2)
        measurable_const).neg
  · rcases κ with i | ij <;> simp only [vvec, Sum.elim_inl, Sum.elim_inr]
    · exact (hc.comp ((hx i).prodMk (hy i))).neg
    · exact hc.comp ((hx ij.1).prodMk (hy ij.2))

end MOTBadAux

open MOTBadAux in
theorem solution (c : ℝ → ℝ → ℝ) (hc : Measurable (Function.uncurry c))
    (n : ℕ) : MeasurableSet (BadTuples c n) := by
  have : BadTuples c n = (fun p : Fin n → ℝ × ℝ => (Amat p, vvec c p)) ⁻¹'
      {Av : (RR n → KK n → ℝ) × (KK n → ℝ) | ∃ z ∈ stdSimplex ℝ (KK n),
        (∀ r, ∑ κ, Av.1 r κ * z κ = 0) ∧ ∑ κ, Av.2 κ * z κ < 0} := by
    ext p; exact bad_iff' c n p
  rw [this]
  exact measurable_Av c hc n measurableSet_exists_simplex
