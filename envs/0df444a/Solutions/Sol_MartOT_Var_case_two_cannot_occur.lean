-- Prove2me | solution 1 for MartOT.Var.case_two_cannot_occur
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:31:25.507665+00:00
-- url     : https://prove2.me/submissions/fec220bd-4a3d-4a1f-895c-a6adaaac434b

import Mathlib
import Definitions.Def_MartOT_Var_BadTuples
import Theorems.Thm_MartOT_Var_reroute_improves

open MeasureTheory MartOT.Var

namespace MartOTVarCaseTwoAux

/-! ### Section 1: Basic `integralE`, finite-sum measure, and fiber-regrouping helpers -/

lemma toENNReal_coe (r : ℝ) : ((r : EReal)).toENNReal = ENNReal.ofReal r := by
  cases le_total 0 r with
  | inl h =>
    have h1 : (0 : EReal) ≤ (r : EReal) := by exact_mod_cast h
    have h2 : (((r : EReal)).toENNReal : EReal) = (r : EReal) := EReal.coe_toENNReal h1
    have h3 : ((ENNReal.ofReal r : ENNReal) : EReal) = (r : EReal) := by
      rw [EReal.coe_ennreal_ofReal, max_eq_left h]
    exact EReal.coe_ennreal_injective (h2.trans h3.symm)
  | inr h =>
    have h1 : (r : EReal) ≤ 0 := by exact_mod_cast h
    rw [EReal.toENNReal_of_nonpos h1, ENNReal.ofReal_of_nonpos h]

lemma toENNReal_neg_coe (r : ℝ) : (-(r : EReal)).toENNReal = ENNReal.ofReal (-r) := by
  rw [← EReal.coe_neg, toENNReal_coe]

lemma integralE_eq_coe {X : Type*} [MeasurableSpace X] (m : Measure X) (f : X → ℝ)
    (hf : Integrable f m) :
    integralE m f = ((∫ x, f x ∂m : ℝ) : EReal) := by
  unfold integralE ModelRiskOT.Duality.extIntegral
  simp_rw [toENNReal_coe, toENNReal_neg_coe]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  have hpos : ∫⁻ x, ENNReal.ofReal (f x) ∂m ≠ ⊤ := by
    have hle : ∫⁻ x, ENNReal.ofReal (f x) ∂m ≤ ∫⁻ x, ‖f x‖ₑ ∂m :=
      lintegral_mono fun x => by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    exact (lt_of_le_of_lt hle hf.2).ne
  have hneg : ∫⁻ x, ENNReal.ofReal (-f x) ∂m ≠ ⊤ := by
    have hle : ∫⁻ x, ENNReal.ofReal (-f x) ∂m ≤ ∫⁻ x, ‖f x‖ₑ ∂m :=
      lintegral_mono fun x => by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
    exact (lt_of_le_of_lt hle hf.2).ne
  have hcoe : ∀ a : ENNReal, a ≠ ⊤ → ((a.toReal : ℝ) : EReal) = (a : EReal) := fun a ha => by
    have h : ENNReal.ofReal a.toReal = a := ENNReal.ofReal_toReal ha
    calc ((a.toReal : ℝ) : EReal) = ((ENNReal.ofReal a.toReal : ENNReal) : EReal) := by
          rw [EReal.coe_ennreal_ofReal, max_eq_left ENNReal.toReal_nonneg]
      _ = (a : EReal) := by rw [h]
  rw [EReal.coe_sub, hcoe _ hpos, hcoe _ hneg]

lemma integrable_finset_sum_measure {X ι : Type*} [MeasurableSpace X] {f : X → ℝ}
    {s : Finset ι} {μ : ι → Measure X} (h : ∀ i ∈ s, Integrable f (μ i)) :
    Integrable f (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact integrable_add_measure.mpr
      ⟨h a (Finset.mem_insert_self a s),
        ih fun i hi => h i (Finset.mem_insert_of_mem hi)⟩

lemma integral_finset_sum_measure {X ι : Type*} [MeasurableSpace X] {f : X → ℝ}
    {s : Finset ι} {μ : ι → Measure X} (h : ∀ i ∈ s, Integrable f (μ i)) :
    ∫ x, f x ∂(∑ i ∈ s, μ i) = ∑ i ∈ s, ∫ x, f x ∂(μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    rw [integral_add_measure (h a (Finset.mem_insert_self a s))
      (integrable_finset_sum_measure fun i hi => h i (Finset.mem_insert_of_mem hi))]
    rw [ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

lemma sum_fiber_expand {ι β R : Type*} [Fintype ι] [DecidableEq β] [CommSemiring R]
    (f : ι → β) (g : ι → R) (φ : β → R) (T : Finset β) (hT : ∀ i, f i ∈ T) :
    ∑ i, g i * φ (f i) = ∑ b ∈ T, φ b * ∑ i, (if f i = b then g i else 0) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hterm : ∀ b, φ b * (if f i = b then g i else 0) = if f i = b then g i * φ (f i) else 0 := by
    intro b
    split_ifs with h
    · subst h; ring
    · simp
  simp_rw [hterm]
  rw [Finset.sum_ite_eq]
  simp [hT i]

lemma fiber_transfer {ι ι' β R : Type*} [Fintype ι] [Fintype ι'] [DecidableEq β] [CommSemiring R]
    (f : ι → β) (f' : ι' → β) (g : ι → R) (h : ι' → R)
    (hgh : ∀ b, ∑ i, (if f i = b then g i else 0) = ∑ j, (if f' j = b then h j else 0))
    (φ : β → R) :
    ∑ i, g i * φ (f i) = ∑ j, h j * φ (f' j) := by
  classical
  set T := Finset.univ.image f ∪ Finset.univ.image f'
  rw [sum_fiber_expand f g φ T (fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))),
    sum_fiber_expand f' h φ T (fun j => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))]
  simp_rw [hgh]

/-! ### Section 2: Finite representation and simplex reduction of `BadTuples` -/

abbrev RR (n : ℕ) := Fin n ⊕ (Fin n ⊕ Fin n)
abbrev KK (n : ℕ) := Fin n ⊕ (Fin n × Fin n)

def eK (n : ℕ) : KK n ≃ Fin (n + n * n) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) finProdFinEquiv).trans finSumFinEquiv

def grid {n : ℕ} (p : Fin n → ℝ × ℝ) (ij : Fin n × Fin n) : ℝ × ℝ :=
  ((p ij.1).1, (p ij.2).2)

noncomputable def AmatKK {n : ℕ} (p : Fin n → ℝ × ℝ) : RR n → KK n → ℝ
  | Sum.inl k =>
      Sum.elim (fun i => if (p i).1 = (p k).1 then 1 else 0)
        (fun ij => -(if (p ij.1).1 = (p k).1 then 1 else 0))
  | Sum.inr (Sum.inl k) =>
      Sum.elim (fun i => if (p i).2 = (p k).2 then 1 else 0)
        (fun ij => -(if (p ij.2).2 = (p k).2 then 1 else 0))
  | Sum.inr (Sum.inr k) =>
      Sum.elim (fun i => if (p i).1 = (p k).1 then (p i).2 else 0)
        (fun ij => -(if (p ij.1).1 = (p k).1 then (p ij.2).2 else 0))

noncomputable def vvecKK (c : ℝ → ℝ → ℝ) {n : ℕ} (p : Fin n → ℝ × ℝ) : KK n → ℝ :=
  Sum.elim (fun i => -c (p i).1 (p i).2) (fun ij => c (p ij.1).1 (p ij.2).2)

noncomputable def Amat {n : ℕ} (p : Fin n → ℝ × ℝ) (r : RR n) (j : Fin (n + n * n)) : ℝ :=
  AmatKK p r ((eK n).symm j)

noncomputable def vvec (c : ℝ → ℝ → ℝ) {n : ℕ} (p : Fin n → ℝ × ℝ) (j : Fin (n + n * n)) : ℝ :=
  vvecKK c p ((eK n).symm j)

lemma measurable_Av (c : ℝ → ℝ → ℝ) (hc : Measurable (Function.uncurry c)) (n : ℕ) :
    Measurable fun p : Fin n → ℝ × ℝ => (Amat p, vvec c p) := by
  have hx : ∀ i : Fin n, Measurable fun p : Fin n → ℝ × ℝ => (p i).1 :=
    fun i => measurable_fst.comp (measurable_pi_apply i)
  have hy : ∀ i : Fin n, Measurable fun p : Fin n → ℝ × ℝ => (p i).2 :=
    fun i => measurable_snd.comp (measurable_pi_apply i)
  refine Measurable.prodMk
    (measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun j => ?_)
    (measurable_pi_iff.2 fun j => ?_)
  · unfold Amat
    rcases r with k | k | k <;> rcases (eK n).symm j with i | ij <;>
      simp only [AmatKK, Sum.elim_inl, Sum.elim_inr]
    · exact Measurable.ite (measurableSet_eq_fun (hx i) (hx k)) measurable_const measurable_const
    · exact (Measurable.ite (measurableSet_eq_fun (hx ij.1) (hx k))
        measurable_const measurable_const).neg
    · exact Measurable.ite (measurableSet_eq_fun (hy i) (hy k)) measurable_const measurable_const
    · exact (Measurable.ite (measurableSet_eq_fun (hy ij.2) (hy k))
        measurable_const measurable_const).neg
    · exact Measurable.ite (measurableSet_eq_fun (hx i) (hx k)) (hy i) measurable_const
    · exact (Measurable.ite (measurableSet_eq_fun (hx ij.1) (hx k))
        (hy ij.2) measurable_const).neg
  · unfold vvec
    rcases (eK n).symm j with i | ij <;> simp only [vvecKK, Sum.elim_inl, Sum.elim_inr]
    · exact (hc.comp ((hx i).prodMk (hy i))).neg
    · exact hc.comp ((hx ij.1).prodMk (hy ij.2))

/-- A finite weighted sum of Dirac masses. -/
noncomputable def diracSum {ι : Type*} [Fintype ι] (u : ι → NNReal) (q : ι → ℝ × ℝ) :
    Measure (ℝ × ℝ) :=
  ∑ i, (u i : ENNReal) • Measure.dirac (q i)

lemma diracSum_apply {ι : Type*} [Fintype ι] (u : ι → NNReal) (q : ι → ℝ × ℝ)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    diracSum u q s = ∑ i, (u i : ENNReal) * s.indicator 1 (q i) := by
  rw [diracSum, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]

lemma integrable_diracSum {ι : Type*} [Fintype ι] (u : ι → NNReal) (q : ι → ℝ × ℝ)
    (f : ℝ × ℝ → ℝ) : Integrable f (diracSum u q) := by
  refine integrable_finset_sum_measure fun i _ => ?_
  have h1 : Integrable f (Measure.dirac (q i)) := integrable_dirac (by simp)
  by_cases hu : (u i : ENNReal) = 0
  · simp [hu]
  · exact h1.smul_measure ENNReal.coe_ne_top

lemma integral_diracSum {ι : Type*} [Fintype ι] (u : ι → NNReal) (q : ι → ℝ × ℝ)
    (f : ℝ × ℝ → ℝ) :
    ∫ x, f x ∂(diracSum u q) = ∑ i, (u i : ℝ) * f (q i) := by
  rw [diracSum, integral_finset_sum_measure fun i _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.coe_ne_top]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.coe_toReal, smul_eq_mul]

lemma cost_diracSum (c : ℝ → ℝ → ℝ) {ι : Type*} [Fintype ι] (u : ι → NNReal)
    (q : ι → ℝ × ℝ) :
    cost c (diracSum u q) = ((∑ i, (u i : ℝ) * c (q i).1 (q i).2 : ℝ) : EReal) := by
  unfold cost
  rw [integralE_eq_coe _ _ (integrable_diracSum u q _), integral_diracSum]

lemma finite_measure_repr {ι : Type*} [Fintype ι] [Nonempty ι] (m : Measure (ℝ × ℝ))
    [IsFiniteMeasure m] (q : ι → ℝ × ℝ) (hm : m (Set.range q)ᶜ = 0) :
    ∃ u : ι → NNReal, m = diracSum u q := by
  classical
  let idx : ℝ × ℝ → ι := fun x =>
    if h : x ∈ Set.range q then Classical.choose h else Classical.arbitrary ι
  have hidx : ∀ x ∈ Set.range q, q (idx x) = x := fun x hx => by
    simp only [idx, dif_pos hx]
    exact Classical.choose_spec hx
  refine ⟨fun i => if i = idx (q i) then (m {q i}).toNNReal else 0, ?_⟩
  ext s hs
  rw [diracSum_apply _ _ hs]
  have hms : m s = m (s ∩ Set.range q) := by
    have hsub : s \ (s ∩ Set.range q) ⊆ (Set.range q)ᶜ := fun x hx => by
      simp only [Set.mem_sdiff, Set.mem_inter_iff, not_and] at hx
      exact hx.2 hx.1
    have hnull : m (s \ (s ∩ Set.range q)) = 0 := measure_mono_null hsub hm
    have hdisj : Disjoint (s ∩ Set.range q) (s \ (s ∩ Set.range q)) := disjoint_sdiff_self_right
    have hunion : (s ∩ Set.range q) ∪ (s \ (s ∩ Set.range q)) = s :=
      Set.union_sdiff_cancel Set.inter_subset_left
    have hrange_meas : MeasurableSet (Set.range q) := (Set.finite_range q).measurableSet
    calc m s = m ((s ∩ Set.range q) ∪ (s \ (s ∩ Set.range q))) := by rw [hunion]
      _ = m (s ∩ Set.range q) + m (s \ (s ∩ Set.range q)) :=
          measure_union hdisj (hs.diff (hs.inter hrange_meas))
      _ = m (s ∩ Set.range q) := by rw [hnull, add_zero]
  rw [hms]
  set S : Finset (ℝ × ℝ) := Finset.univ.image q
  have hS : (S : Set (ℝ × ℝ)) = Set.range q := by
    ext x; simp [S]
  have hinter : s ∩ Set.range q = ⋃ x ∈ S.filter (· ∈ s), ({x} : Set (ℝ × ℝ)) := by
    ext x
    simp [← hS, and_comm]
  rw [hinter, measure_biUnion_finset (fun x _ y _ hxy => Set.disjoint_singleton.2 hxy)
    (fun x _ => measurableSet_singleton x)]
  rw [Finset.sum_filter]
  have hsum_rhs : ∑ i : ι,
      ((if i = idx (q i) then (m {q i}).toNNReal else 0 : NNReal) : ENNReal) *
        s.indicator 1 (q i) =
      ∑ x ∈ S, if x ∈ s then m {x} else 0 := by
    have hSmem : ∀ i : ι, q i ∈ S := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ _)
    calc ∑ i : ι,
          ((if i = idx (q i) then (m {q i}).toNNReal else 0 : NNReal) : ENNReal) *
            s.indicator 1 (q i)
        = ∑ x ∈ S, s.indicator 1 x *
            ∑ i : ι, (if q i = x then
              ((if i = idx (q i) then (m {q i}).toNNReal else 0 : NNReal) : ENNReal)
              else 0) :=
          sum_fiber_expand q (fun i => ((if i = idx (q i) then (m {q i}).toNNReal else 0 : NNReal) : ENNReal))
            (s.indicator 1) S hSmem
      _ = ∑ x ∈ S, if x ∈ s then m {x} else 0 := by
          refine Finset.sum_congr rfl fun x hx => ?_
          have hx' : x ∈ Set.range q := by rwa [← hS]
          have hinner : ∑ i : ι, (if q i = x then
              ((if i = idx (q i) then (m {q i}).toNNReal else 0 : NNReal) : ENNReal)
              else 0) = m {x} := by
            have hterm : ∀ i : ι, (if q i = x then
                ((if i = idx (q i) then (m {q i}).toNNReal else 0 : NNReal) : ENNReal)
                else 0) = if i = idx x then m {x} else 0 := by
              intro i
              by_cases hqi : q i = x
              · rw [if_pos hqi, hqi]
                by_cases hi : i = idx x
                · rw [if_pos hi, if_pos hi, ENNReal.coe_toNNReal (measure_ne_top m _)]
                · rw [if_neg hi, if_neg hi]; simp
              · rw [if_neg hqi]
                have hi : i ≠ idx x := fun h => hqi (h ▸ hidx x hx')
                rw [if_neg hi]
            simp_rw [hterm]
            simp
          rw [hinner]
          by_cases hxs : x ∈ s
          · simp [hxs]
          · simp [hxs]
  exact hsum_rhs.symm

lemma grid_conc {n : ℕ} (p : Fin n → ℝ × ℝ) (α α' : Measure (ℝ × ℝ))
    (hα : α (Set.range p)ᶜ = 0) (hcomp : IsCompetitor α α') :
    α' (Set.range (grid p))ᶜ = 0 := by
  have hsub : (Set.range (grid p))ᶜ ⊆
      Prod.fst ⁻¹' (Set.range (fun i => (p i).1))ᶜ ∪
        Prod.snd ⁻¹' (Set.range (fun i => (p i).2))ᶜ := by
    intro q hq
    by_contra h
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, not_or, not_not] at h
    rcases h with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact hq ⟨(i, j), Prod.ext hi hj⟩
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · have hm : MeasurableSet (Set.range (fun i => (p i).1))ᶜ :=
      (Set.finite_range _).measurableSet.compl
    rw [← Measure.map_apply measurable_fst hm, ← hcomp.1, Measure.map_apply measurable_fst hm]
    refine measure_mono_null ?_ hα
    intro q hq hmem
    rcases hmem with ⟨i, rfl⟩
    exact hq ⟨i, rfl⟩
  · have hm : MeasurableSet (Set.range (fun i => (p i).2))ᶜ :=
      (Set.finite_range _).measurableSet.compl
    rw [← Measure.map_apply measurable_snd hm, ← hcomp.2.1, Measure.map_apply measurable_snd hm]
    refine measure_mono_null ?_ hα
    intro q hq hmem
    rcases hmem with ⟨i, rfl⟩
    exact hq ⟨i, rfl⟩

lemma diracSum_map_singleton {ι : Type*} [Fintype ι] (u : ι → NNReal) (q : ι → ℝ × ℝ)
    (g : ℝ × ℝ → ℝ) (hg : Measurable g) (b : ℝ) :
    ((diracSum u q).map g) {b} =
      ((∑ i, if g (q i) = b then u i else 0 : NNReal) : ENNReal) := by
  rw [Measure.map_apply hg (measurableSet_singleton b),
    diracSum_apply u q (hg (measurableSet_singleton b)), ENNReal.ofNNReal_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : g (q i) = b
  · simp [Set.indicator_of_mem, h]
  · simp [Set.indicator_of_notMem, h]

def BadSimplex (c : ℝ → ℝ → ℝ) (n m K : ℕ) : Set (Fin n → ℝ × ℝ) :=
  {p | (∀ i, |(p i).1| ≤ (K : ℝ) ∧ |(p i).2| ≤ (K : ℝ)) ∧
    (∀ i j, |c (p i).1 (p j).2| ≤ (K : ℝ)) ∧
    ∃ z ∈ stdSimplex ℝ (Fin (n + n * n)),
      (∀ r : RR n, ∑ j, Amat p r j * z j = 0) ∧
      ∑ j, vvec c p j * z j ≤ -(1 / ((m : ℝ) + 1))}

lemma badTuples_subset_iUnion_badSimplex (c : ℝ → ℝ → ℝ) {n : ℕ} (hn : 0 < n) :
    BadTuples c n ⊆ ⋃ m : ℕ, ⋃ K : ℕ, BadSimplex c n m K := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  intro p hp
  rcases hp with ⟨α, hαfin, hαconc, α', hcomp, hlt⟩
  have hα'fin : IsFiniteMeasure α' := by
    constructor
    have h1 : α' Set.univ = (α'.map Prod.fst) Set.univ := by
      rw [Measure.map_apply measurable_fst MeasurableSet.univ]; rfl
    rw [h1, ← hcomp.1, Measure.map_apply measurable_fst MeasurableSet.univ]
    exact measure_lt_top α _
  obtain ⟨u, rfl⟩ := finite_measure_repr α p hαconc
  obtain ⟨u', rfl⟩ := finite_measure_repr α' (grid p) (grid_conc p _ α' hαconc hcomp)
  have hfst : ∀ k : Fin n,
      ∑ i : Fin n, (if (p i).1 = (p k).1 then (u i : ℝ) else 0) =
      ∑ ij : Fin n × Fin n, (if (p ij.1).1 = (p k).1 then (u' ij : ℝ) else 0) := by
    intro k
    have h := congr_arg (fun μ : Measure ℝ => μ {(p k).1}) hcomp.1
    rw [diracSum_map_singleton u p Prod.fst measurable_fst,
      diracSum_map_singleton u' (grid p) Prod.fst measurable_fst] at h
    have hnn : (∑ i : Fin n, if (p i).1 = (p k).1 then u i else 0) =
        ∑ ij : Fin n × Fin n, if (grid p ij).1 = (p k).1 then u' ij else 0 :=
      ENNReal.coe_inj.mp h
    have hreal := congr_arg NNReal.toReal hnn
    rw [NNReal.coe_sum, NNReal.coe_sum] at hreal
    have hl : ∑ i : Fin n, (if (p i).1 = (p k).1 then (u i : ℝ) else 0) =
        ∑ i : Fin n, ((if (p i).1 = (p k).1 then u i else 0 : NNReal) : ℝ) :=
      Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
    have hr : ∑ ij : Fin n × Fin n, (if (p ij.1).1 = (p k).1 then (u' ij : ℝ) else 0) =
        ∑ ij : Fin n × Fin n, ((if (grid p ij).1 = (p k).1 then u' ij else 0 : NNReal) : ℝ) :=
      Finset.sum_congr rfl fun ij _ => by
        by_cases hx : (p ij.1).1 = (p k).1
        · rw [if_pos hx, if_pos (show (grid p ij).1 = (p k).1 from hx)]
        · rw [if_neg hx, if_neg (show (grid p ij).1 ≠ (p k).1 from hx)]; rfl
    rw [hl, hr, hreal]
  have hsnd : ∀ k : Fin n,
      ∑ i : Fin n, (if (p i).2 = (p k).2 then (u i : ℝ) else 0) =
      ∑ ij : Fin n × Fin n, (if (p ij.2).2 = (p k).2 then (u' ij : ℝ) else 0) := by
    intro k
    have h := congr_arg (fun μ : Measure ℝ => μ {(p k).2}) hcomp.2.1
    rw [diracSum_map_singleton u p Prod.snd measurable_snd,
      diracSum_map_singleton u' (grid p) Prod.snd measurable_snd] at h
    have hnn : (∑ i : Fin n, if (p i).2 = (p k).2 then u i else 0) =
        ∑ ij : Fin n × Fin n, if (grid p ij).2 = (p k).2 then u' ij else 0 :=
      ENNReal.coe_inj.mp h
    have hreal := congr_arg NNReal.toReal hnn
    rw [NNReal.coe_sum, NNReal.coe_sum] at hreal
    have hl : ∑ i : Fin n, (if (p i).2 = (p k).2 then (u i : ℝ) else 0) =
        ∑ i : Fin n, ((if (p i).2 = (p k).2 then u i else 0 : NNReal) : ℝ) :=
      Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
    have hr : ∑ ij : Fin n × Fin n, (if (p ij.2).2 = (p k).2 then (u' ij : ℝ) else 0) =
        ∑ ij : Fin n × Fin n, ((if (grid p ij).2 = (p k).2 then u' ij else 0 : NNReal) : ℝ) :=
      Finset.sum_congr rfl fun ij _ => by
        by_cases hx : (p ij.2).2 = (p k).2
        · rw [if_pos hx, if_pos (show (grid p ij).2 = (p k).2 from hx)]
        · rw [if_neg hx, if_neg (show (grid p ij).2 ≠ (p k).2 from hx)]; rfl
    rw [hl, hr, hreal]
  have hbary : ∀ k : Fin n,
      ∑ i : Fin n, (if (p i).1 = (p k).1 then (p i).2 * (u i : ℝ) else 0) =
      ∑ ij : Fin n × Fin n, (if (p ij.1).1 = (p k).1 then (p ij.2).2 * (u' ij : ℝ) else 0) := by
    intro k
    let ρ : ℝ → ℝ := Set.indicator {(p k).1} (fun _ => 1)
    have hρm : Measurable ρ := measurable_const.indicator (measurableSet_singleton _)
    have hρb : ∃ C, ∀ x, |ρ x| ≤ C := ⟨1, fun x => by
      by_cases hx : x = (p k).1 <;> simp [ρ, hx]⟩
    have h := hcomp.2.2.2.2 ρ hρm hρb
    rw [integral_diracSum, integral_diracSum] at h
    have h1 : ∀ i : Fin n, (u i : ℝ) * (ρ (p i).1 * (p i).2) =
        if (p i).1 = (p k).1 then (p i).2 * (u i : ℝ) else 0 := by
      intro i
      by_cases hx : (p i).1 = (p k).1 <;> simp [ρ, hx, mul_comm]
    have h2 : ∀ ij : Fin n × Fin n, (u' ij : ℝ) * (ρ (grid p ij).1 * (grid p ij).2) =
        if (p ij.1).1 = (p k).1 then (p ij.2).2 * (u' ij : ℝ) else 0 := by
      intro ij
      by_cases hx : (p ij.1).1 = (p k).1 <;> simp [ρ, grid, hx, mul_comm]
    simp_rw [h1, h2] at h
    exact h
  have hcost : ∑ ij : Fin n × Fin n, (u' ij : ℝ) * c (p ij.1).1 (p ij.2).2 <
      ∑ i : Fin n, (u i : ℝ) * c (p i).1 (p i).2 := by
    rw [cost_diracSum, cost_diracSum] at hlt
    exact_mod_cast hlt
  let wKK : KK n → ℝ := Sum.elim (fun i => (u i : ℝ)) (fun ij => (u' ij : ℝ))
  let w : Fin (n + n * n) → ℝ := fun j => wKK ((eK n).symm j)
  have hw0 : ∀ j, 0 ≤ w j := fun j => by
    dsimp only [w, wKK]
    rcases (eK n).symm j with i | ij <;> simp
  have hAw : ∀ r : RR n, ∑ j, Amat p r j * w j = 0 := by
    intro r
    have heq : ∑ j, Amat p r j * w j = ∑ κ : KK n, AmatKK p r κ * wKK κ :=
      Fintype.sum_equiv (eK n).symm _ _ fun j => rfl
    rw [heq, Fintype.sum_sum_type]
    rcases r with k | k | k
    · simp only [AmatKK, wKK, Sum.elim_inl, Sum.elim_inr]
      have s1 : ∑ i : Fin n, (if (p i).1 = (p k).1 then (1 : ℝ) else 0) * (u i : ℝ) =
          ∑ i : Fin n, if (p i).1 = (p k).1 then (u i : ℝ) else 0 :=
        Finset.sum_congr rfl fun i _ => by split_ifs <;> ring
      have s2 : ∑ ij : Fin n × Fin n,
            (-(if (p ij.1).1 = (p k).1 then (1 : ℝ) else 0)) * (u' ij : ℝ) =
          -(∑ ij : Fin n × Fin n, if (p ij.1).1 = (p k).1 then (u' ij : ℝ) else 0) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun ij _ => by split_ifs <;> ring
      rw [s1, s2, hfst k, add_neg_cancel]
    · simp only [AmatKK, wKK, Sum.elim_inl, Sum.elim_inr]
      have s1 : ∑ i : Fin n, (if (p i).2 = (p k).2 then (1 : ℝ) else 0) * (u i : ℝ) =
          ∑ i : Fin n, if (p i).2 = (p k).2 then (u i : ℝ) else 0 :=
        Finset.sum_congr rfl fun i _ => by split_ifs <;> ring
      have s2 : ∑ ij : Fin n × Fin n,
            (-(if (p ij.2).2 = (p k).2 then (1 : ℝ) else 0)) * (u' ij : ℝ) =
          -(∑ ij : Fin n × Fin n, if (p ij.2).2 = (p k).2 then (u' ij : ℝ) else 0) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun ij _ => by split_ifs <;> ring
      rw [s1, s2, hsnd k, add_neg_cancel]
    · simp only [AmatKK, wKK, Sum.elim_inl, Sum.elim_inr]
      have s1 : ∑ i : Fin n, (if (p i).1 = (p k).1 then (p i).2 else 0) * (u i : ℝ) =
          ∑ i : Fin n, if (p i).1 = (p k).1 then (p i).2 * (u i : ℝ) else 0 :=
        Finset.sum_congr rfl fun i _ => by split_ifs <;> ring
      have s2 : ∑ ij : Fin n × Fin n,
            (-(if (p ij.1).1 = (p k).1 then (p ij.2).2 else 0)) * (u' ij : ℝ) =
          -(∑ ij : Fin n × Fin n, if (p ij.1).1 = (p k).1 then (p ij.2).2 * (u' ij : ℝ) else 0) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun ij _ => by split_ifs <;> ring
      rw [s1, s2, hbary k, add_neg_cancel]
  have hvw : ∑ j, vvec c p j * w j < 0 := by
    have heq : ∑ j, vvec c p j * w j = ∑ κ : KK n, vvecKK c p κ * wKK κ :=
      Fintype.sum_equiv (eK n).symm _ _ fun j => rfl
    rw [heq, Fintype.sum_sum_type]
    simp only [vvecKK, wKK, Sum.elim_inl, Sum.elim_inr]
    have s1 : ∑ i : Fin n, -c (p i).1 (p i).2 * (u i : ℝ) =
        -(∑ i : Fin n, (u i : ℝ) * c (p i).1 (p i).2) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have s2 : ∑ ij : Fin n × Fin n, c (p ij.1).1 (p ij.2).2 * (u' ij : ℝ) =
        ∑ ij : Fin n × Fin n, (u' ij : ℝ) * c (p ij.1).1 (p ij.2).2 :=
      Finset.sum_congr rfl fun ij _ => by ring
    rw [s1, s2]
    linarith
  set T := ∑ j, w j
  have hT : 0 < T := by
    rcases (Finset.sum_nonneg fun j _ => hw0 j : 0 ≤ T).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hw0 j).1 h.symm
      have : ∑ j, vvec c p j * w j = 0 :=
        Finset.sum_eq_zero fun j hj => by rw [h0 j hj, mul_zero]
      linarith
  let z : Fin (n + n * n) → ℝ := fun j => w j / T
  have hz : z ∈ stdSimplex ℝ (Fin (n + n * n)) := by
    refine ⟨fun j => div_nonneg (hw0 j) hT.le, ?_⟩
    rw [← Finset.sum_div, div_self hT.ne']
  have hAz : ∀ r : RR n, ∑ j, Amat p r j * z j = 0 := fun r => by
    simp_rw [z, mul_div_assoc', ← Finset.sum_div, hAw r, zero_div]
  have hvz : ∑ j, vvec c p j * z j < 0 := by
    simp_rw [z, mul_div_assoc', ← Finset.sum_div]
    exact div_neg_of_neg_of_pos hvw hT
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (neg_pos.2 hvz)
  let M : ℝ := (∑ i : Fin n, (|(p i).1| + |(p i).2|)) +
    ∑ i : Fin n, ∑ j : Fin n, |c (p i).1 (p j).2|
  obtain ⟨K, hK⟩ := exists_nat_gt M
  refine Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨K, ?_, ?_, z, hz, hAz, ?_⟩⟩
  · intro i
    have h1 : |(p i).1| + |(p i).2| ≤ ∑ i' : Fin n, (|(p i').1| + |(p i').2|) :=
      Finset.single_le_sum (f := fun i' : Fin n => |(p i').1| + |(p i').2|)
        (fun i' _ => by positivity) (Finset.mem_univ i)
    have h2 : 0 ≤ ∑ i' : Fin n, ∑ j' : Fin n, |c (p i').1 (p j').2| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h3 : 0 ≤ |(p i).1| := abs_nonneg _
    have h4 : 0 ≤ |(p i).2| := abs_nonneg _
    constructor <;> linarith
  · intro i j
    have h1 : |c (p i).1 (p j).2| ≤ ∑ j' : Fin n, |c (p i).1 (p j').2| :=
      Finset.single_le_sum (f := fun j' : Fin n => |c (p i).1 (p j').2|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 : ∑ j' : Fin n, |c (p i).1 (p j').2| ≤
        ∑ i' : Fin n, ∑ j' : Fin n, |c (p i').1 (p j').2| :=
      Finset.single_le_sum (f := fun i' : Fin n => ∑ j' : Fin n, |c (p i').1 (p j').2|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h3 : 0 ≤ ∑ i' : Fin n, (|(p i').1| + |(p i').2|) :=
      Finset.sum_nonneg fun _ _ => by positivity
    linarith
  · linarith

/-! ### Section 3: Lexicographic Borel selection on a compact simplex -/

lemma lex_borel_selection_aux {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (d : ℕ)
    (F : Set (Y × (Fin d → ℝ))) (hF : IsClosed F)
    (hFsub : F ⊆ Set.univ ×ˢ stdSimplex ℝ (Fin d))
    (hE : MeasurableSet (Prod.fst '' F)) :
    ∀ k (hk : k ≤ d), ∃ s : Fin k → Y → ℝ, (∀ j, Measurable (s j)) ∧
      ∀ y ∈ Prod.fst '' F, ∃ z : Fin d → ℝ, (y, z) ∈ F ∧
        ∀ j : Fin k, z ⟨j.1, lt_of_lt_of_le j.2 hk⟩ = s j y := by
  have : CompactSpace (stdSimplex ℝ (Fin d)) :=
    isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ (Fin d))
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨Fin.elim0, fun j => Fin.elim0 j, fun y hy => ?_⟩
    rcases hy with ⟨⟨y', z⟩, hmem, rfl⟩
    exact ⟨z, hmem, fun j => Fin.elim0 j⟩
  | succ k ih =>
    intro hk1
    have hk : k ≤ d := Nat.le_of_succ_le hk1
    obtain ⟨s, hs_meas, hs_wit⟩ := ih hk
    let S : Y → Set (Fin d → ℝ) := fun y =>
      {z : Fin d → ℝ | (y, z) ∈ F ∧ ∀ j : Fin k, z ⟨j.1, lt_of_lt_of_le j.2 hk⟩ = s j y}
    let val : Y → ℝ := fun y => sInf ((fun z : Fin d → ℝ => z ⟨k, hk1⟩) '' S y)
    have hS_att : ∀ y ∈ Prod.fst '' F,
        (∃ z ∈ S y, z ⟨k, hk1⟩ = val y) ∧ ∀ z ∈ S y, val y ≤ z ⟨k, hk1⟩ := by
      intro y hy
      have hSne : (S y).Nonempty := by
        obtain ⟨z, hzF, hzs⟩ := hs_wit y hy
        exact ⟨z, hzF, hzs⟩
      have hSclosed : IsClosed (S y) := by
        have h1 : IsClosed {z : Fin d → ℝ | (y, z) ∈ F} :=
          hF.preimage (continuous_const.prodMk continuous_id)
        have h2 : IsClosed {z : Fin d → ℝ |
            ∀ j : Fin k, z ⟨j.1, lt_of_lt_of_le j.2 hk⟩ = s j y} := by
          have : {z : Fin d → ℝ |
              ∀ j : Fin k, z ⟨j.1, lt_of_lt_of_le j.2 hk⟩ = s j y} =
              ⋂ j : Fin k, {z | z ⟨j.1, lt_of_lt_of_le j.2 hk⟩ = s j y} := by
            ext z; simp
          rw [this]
          exact isClosed_iInter fun j => isClosed_eq (continuous_apply _) continuous_const
        exact h1.inter h2
      have hSsub : S y ⊆ stdSimplex ℝ (Fin d) := fun z hz => (hFsub hz.1).2
      have hScomp : IsCompact (S y) :=
        (isCompact_stdSimplex ℝ (Fin d)).of_isClosed_subset hSclosed hSsub
      have hTcomp : IsCompact ((fun z : Fin d → ℝ => z ⟨k, hk1⟩) '' S y) :=
        hScomp.image (continuous_apply (⟨k, hk1⟩ : Fin d))
      have hTne : ((fun z : Fin d → ℝ => z ⟨k, hk1⟩) '' S y).Nonempty := hSne.image _
      refine ⟨?_, fun z hz => csInf_le hTcomp.bddBelow ⟨z, hz, rfl⟩⟩
      obtain ⟨z, hz, hzk⟩ := hTcomp.sInf_mem hTne
      exact ⟨z, hz, hzk⟩
    have hval_meas : Measurable val := by
      refine measurable_of_Iic fun t => ?_
      have hpre : val ⁻¹' Set.Iic t =
          {y : Y | ∃ z : stdSimplex ℝ (Fin d),
            (y, (z : Fin d → ℝ)) ∈ F ∧
            (∀ j : Fin k, (z : Fin d → ℝ) ⟨j.1, lt_of_lt_of_le j.2 hk⟩ = s j y) ∧
            (z : Fin d → ℝ) ⟨k, hk1⟩ ≤ t} ∪
          (if 0 ≤ t then (Prod.fst '' F)ᶜ else ∅) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_ofPred_eq]
        by_cases hy : y ∈ Prod.fst '' F
        · have hnot : y ∉ (if 0 ≤ t then (Prod.fst '' F)ᶜ else ∅) := by
            split_ifs <;> simp [hy]
          simp only [hnot, or_false]
          constructor
          · intro hle
            obtain ⟨⟨z, hzS, hzk⟩, _⟩ := hS_att y hy
            exact ⟨⟨z, (hFsub hzS.1).2⟩, hzS.1, hzS.2, hzk.trans_le hle⟩
          · rintro ⟨z, hzF, hzs, hzt⟩
            exact ((hS_att y hy).2 z.1 ⟨hzF, hzs⟩).trans hzt
        · have hSempty : S y = ∅ := by
            ext z
            simp only [S, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
            intro hzF _
            exact hy ⟨(y, z), hzF, rfl⟩
          have hval0 : val y = 0 := by simp [val, hSempty]
          have hno : ¬ ∃ z : stdSimplex ℝ (Fin d),
              (y, (z : Fin d → ℝ)) ∈ F ∧
              (∀ j : Fin k, (z : Fin d → ℝ) ⟨j.1, lt_of_lt_of_le j.2 hk⟩ = s j y) ∧
              (z : Fin d → ℝ) ⟨k, hk1⟩ ≤ t := by
            rintro ⟨z, hzF, _, _⟩
            exact hy ⟨(y, z.1), hzF, rfl⟩
          simp only [hval0, hno, false_or]
          by_cases ht : 0 ≤ t <;> simp [ht, hy]
      rw [hpre]
      refine MeasurableSet.union ?_ ?_
      swap
      · split_ifs
        · exact hE.compl
        · exact MeasurableSet.empty
      let φ : Y → Y × (Fin k → ℝ) := fun y => (y, fun j => s j y)
      have hφ : Measurable φ := measurable_id.prodMk (measurable_pi_iff.2 hs_meas)
      let Ct : Set ((Y × (Fin k → ℝ)) × stdSimplex ℝ (Fin d)) :=
        {q | (q.1.1, (q.2 : Fin d → ℝ)) ∈ F ∧
          (∀ j : Fin k, (q.2 : Fin d → ℝ) ⟨j.1, lt_of_lt_of_le j.2 hk⟩ = q.1.2 j) ∧
          (q.2 : Fin d → ℝ) ⟨k, hk1⟩ ≤ t}
      have hCt : IsClosed Ct := by
        have hc1 : IsClosed {q : (Y × (Fin k → ℝ)) × stdSimplex ℝ (Fin d) |
            (q.1.1, (q.2 : Fin d → ℝ)) ∈ F} :=
          hF.preimage ((continuous_fst.comp continuous_fst).prodMk
            (continuous_subtype_val.comp continuous_snd))
        have hc2 : IsClosed {q : (Y × (Fin k → ℝ)) × stdSimplex ℝ (Fin d) |
            ∀ j : Fin k, (q.2 : Fin d → ℝ) ⟨j.1, lt_of_lt_of_le j.2 hk⟩ = q.1.2 j} := by
          have : {q : (Y × (Fin k → ℝ)) × stdSimplex ℝ (Fin d) |
              ∀ j : Fin k, (q.2 : Fin d → ℝ) ⟨j.1, lt_of_lt_of_le j.2 hk⟩ = q.1.2 j} =
              ⋂ j : Fin k, {q | (q.2 : Fin d → ℝ) ⟨j.1, lt_of_lt_of_le j.2 hk⟩ = q.1.2 j} := by
            ext q; simp
          rw [this]
          exact isClosed_iInter fun j => isClosed_eq
            ((continuous_apply _).comp (continuous_subtype_val.comp continuous_snd))
            ((continuous_apply j).comp (continuous_snd.comp continuous_fst))
        have hc3 : IsClosed {q : (Y × (Fin k → ℝ)) × stdSimplex ℝ (Fin d) |
            (q.2 : Fin d → ℝ) ⟨k, hk1⟩ ≤ t} :=
          isClosed_le ((continuous_apply _).comp (continuous_subtype_val.comp continuous_snd))
            continuous_const
        exact hc1.inter (hc2.inter hc3)
      have hproj : MeasurableSet (Prod.fst '' Ct) :=
        (isClosedMap_fst_of_compactSpace _ hCt).measurableSet
      have heq : {y : Y | ∃ z : stdSimplex ℝ (Fin d),
            (y, (z : Fin d → ℝ)) ∈ F ∧
            (∀ j : Fin k, (z : Fin d → ℝ) ⟨j.1, lt_of_lt_of_le j.2 hk⟩ = s j y) ∧
            (z : Fin d → ℝ) ⟨k, hk1⟩ ≤ t} = φ ⁻¹' (Prod.fst '' Ct) := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_image, Prod.exists,
          exists_and_right, exists_eq_right, Ct, φ]
      rw [heq]
      exact hφ hproj
    let s' : Fin (k + 1) → Y → ℝ := fun j y =>
      if h : j.1 < k then s ⟨j.1, h⟩ y else val y
    refine ⟨s', fun j => ?_, fun y hy => ?_⟩
    · dsimp only [s']
      split_ifs with h
      · exact hs_meas ⟨j.1, h⟩
      · exact hval_meas
    · obtain ⟨⟨z, hzS, hzk⟩, _⟩ := hS_att y hy
      refine ⟨z, hzS.1, fun j => ?_⟩
      dsimp only [s']
      by_cases h : j.1 < k
      · rw [dif_pos h]
        exact hzS.2 ⟨j.1, h⟩
      · rw [dif_neg h]
        have hjeq : j.1 = k := by omega
        have hfin : (⟨j.1, lt_of_lt_of_le j.2 hk1⟩ : Fin d) = ⟨k, hk1⟩ := Fin.ext hjeq
        rw [hfin]
        exact hzk

lemma lex_borel_selection {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (d : ℕ)
    (F : Set (Y × (Fin d → ℝ))) (hF : IsClosed F)
    (hFsub : F ⊆ Set.univ ×ˢ stdSimplex ℝ (Fin d)) :
    MeasurableSet (Prod.fst '' F) ∧
    ∃ sel : Y → (Fin d → ℝ), Measurable sel ∧
      ∀ y ∈ Prod.fst '' F, (y, sel y) ∈ F := by
  have : CompactSpace (stdSimplex ℝ (Fin d)) :=
    isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ (Fin d))
  let F' : Set (Y × stdSimplex ℝ (Fin d)) := {q | (q.1, (q.2 : Fin d → ℝ)) ∈ F}
  have hF' : IsClosed F' :=
    hF.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hfst_eq : Prod.fst '' F = Prod.fst '' F' := by
    ext y
    constructor
    · rintro ⟨⟨y', z⟩, hzF, rfl⟩
      exact ⟨(y', ⟨z, (hFsub hzF).2⟩), hzF, rfl⟩
    · rintro ⟨⟨y', z⟩, hzF, rfl⟩
      exact ⟨(y', z.1), hzF, rfl⟩
  have hE : MeasurableSet (Prod.fst '' F) := by
    rw [hfst_eq]
    exact (isClosedMap_fst_of_compactSpace _ hF').measurableSet
  obtain ⟨s, hs_meas, hs_wit⟩ := lex_borel_selection_aux d F hF hFsub hE d le_rfl
  refine ⟨hE, fun y j => s j y, measurable_pi_iff.2 hs_meas, fun y hy => ?_⟩
  obtain ⟨z, hzF, hzs⟩ := hs_wit y hy
  have hz_eq : z = fun j => s j y := funext fun j => hzs j
  dsimp only
  rwa [← hz_eq]

/-! ### Section 4: Weighted average measures `ω` and `ω'` -/

lemma piece_integrable {P : Type*} [MeasurableSpace P] (θ : Measure P) [IsFiniteMeasure θ]
    {a : P → ℝ} (ha1 : ∀ p, a p ≤ 1)
    {g : P → ℝ × ℝ} (hg : Measurable g)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ᵐ p ∂θ, |f (g p)| ≤ M) :
    Integrable f ((θ.withDensity (fun p => ENNReal.ofReal (a p))).map g) := by
  rw [integrable_map_measure hf.aestronglyMeasurable hg.aemeasurable]
  have hle : θ.withDensity (fun p => ENNReal.ofReal (a p)) ≤ θ := by
    calc θ.withDensity (fun p => ENNReal.ofReal (a p))
        ≤ θ.withDensity 1 := withDensity_mono (ae_of_all _ fun p => by
          simpa using ENNReal.ofReal_le_ofReal (ha1 p))
      _ = θ := by simp
  have : IsFiniteMeasure (θ.withDensity (fun p => ENNReal.ofReal (a p))) :=
    isFiniteMeasure_of_le θ hle
  refine Integrable.of_bound (hf.comp hg).aestronglyMeasurable M ?_
  have hM' : ∀ᵐ p ∂(θ.withDensity (fun p => ENNReal.ofReal (a p))), |f (g p)| ≤ M :=
    Measure.absolutelyContinuous_of_le hle hM
  filter_upwards [hM'] with p hp
  simpa [Real.norm_eq_abs] using hp

lemma piece_integral {P : Type*} [MeasurableSpace P] (θ : Measure P)
    {a : P → ℝ} (ha_meas : Measurable a) (ha0 : ∀ p, 0 ≤ a p)
    {g : P → ℝ × ℝ} (hg : Measurable g)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    ∫ q, f q ∂((θ.withDensity (fun p => ENNReal.ofReal (a p))).map g) =
      ∫ p, a p * f (g p) ∂θ := by
  rw [integral_map hg.aemeasurable hf.aestronglyMeasurable]
  have hmeas : Measurable (fun p => ENNReal.ofReal (a p)) :=
    ENNReal.measurable_ofReal.comp ha_meas
  rw [integral_withDensity_eq_integral_toReal_smul hmeas
    (ae_of_all _ fun p => ENNReal.ofReal_lt_top) (fun p => f (g p))]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  dsimp only
  rw [ENNReal.toReal_ofReal (ha0 p), smul_eq_mul]

lemma piece_prod_integrable {P : Type*} [MeasurableSpace P] (θ : Measure P) [IsFiniteMeasure θ]
    {a : P → ℝ} (ha_meas : Measurable a) (ha0 : ∀ p, 0 ≤ a p) (ha1 : ∀ p, a p ≤ 1)
    {g : P → ℝ × ℝ} (hg : Measurable g)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ᵐ p ∂θ, |f (g p)| ≤ M) :
    Integrable (fun p => a p * f (g p)) θ := by
  refine Integrable.of_bound (ha_meas.mul (hf.comp hg)).aestronglyMeasurable (max M 0) ?_
  filter_upwards [hM] with p hp
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha0 p)]
  calc a p * |f (g p)| ≤ 1 * |f (g p)| := mul_le_mul_of_nonneg_right (ha1 p) (abs_nonneg _)
    _ = |f (g p)| := one_mul _
    _ ≤ M := hp
    _ ≤ max M 0 := le_max_left _ _

lemma avg_integrable {P ι : Type*} [MeasurableSpace P] [Fintype ι]
    (θ : Measure P) [IsFiniteMeasure θ] {n : ℕ} (hn : n ≠ 0)
    {a : ι → P → ℝ} (ha1 : ∀ i p, a i p ≤ 1)
    {g : ι → P → ℝ × ℝ} (hg : ∀ i, Measurable (g i))
    {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ i, ∀ᵐ p ∂θ, |f (g i p)| ≤ M) :
    Integrable f ((n : ENNReal)⁻¹ •
      ∑ i : ι, (θ.withDensity (fun p => ENNReal.ofReal (a i p))).map (g i)) := by
  refine (integrable_finset_sum_measure fun i _ =>
    piece_integrable θ (ha1 i) (hg i) hf (hM i)).smul_measure ?_
  exact ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr hn)

lemma avg_integral {P ι : Type*} [MeasurableSpace P] [Fintype ι]
    (θ : Measure P) [IsFiniteMeasure θ] {n : ℕ}
    {a : ι → P → ℝ} (ha_meas : ∀ i, Measurable (a i))
    (ha0 : ∀ i p, 0 ≤ a i p) (ha1 : ∀ i p, a i p ≤ 1)
    {g : ι → P → ℝ × ℝ} (hg : ∀ i, Measurable (g i))
    {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ i, ∀ᵐ p ∂θ, |f (g i p)| ≤ M) :
    ∫ q, f q ∂((n : ENNReal)⁻¹ •
      ∑ i : ι, (θ.withDensity (fun p => ENNReal.ofReal (a i p))).map (g i)) =
      (n : ℝ)⁻¹ * ∫ p, (∑ i : ι, a i p * f (g i p)) ∂θ := by
  rw [integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  congr 1
  rw [integral_finset_sum_measure fun i _ =>
    piece_integrable θ (ha1 i) (hg i) hf (hM i)]
  simp_rw [piece_integral θ (ha_meas _) (ha0 _) (hg _) hf]
  rw [← integral_finsetSum _ fun i _ =>
    piece_prod_integrable θ (ha_meas i) (ha0 i) (ha1 i) (hg i) hf (hM i)]

lemma avg_map_apply {P ι : Type*} [MeasurableSpace P] [Fintype ι]
    (θ : Measure P) (n : ℕ)
    {a : ι → P → ℝ} (ha_meas : ∀ i, Measurable (a i))
    (ha0 : ∀ i p, 0 ≤ a i p)
    {g : ι → P → ℝ × ℝ} (hg : ∀ i, Measurable (g i))
    {φ : ℝ × ℝ → ℝ} (hφ : Measurable φ) {s : Set ℝ} (hs : MeasurableSet s) :
    (((n : ENNReal)⁻¹ •
      ∑ i : ι, (θ.withDensity (fun p => ENNReal.ofReal (a i p))).map (g i)).map φ) s =
      (n : ENNReal)⁻¹ * ∫⁻ p,
        ENNReal.ofReal (∑ i : ι, a i p * s.indicator (1 : ℝ → ℝ) (φ (g i p))) ∂θ := by
  rw [Measure.map_apply hφ hs, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
  congr 1
  have hterm : ∀ i : ι,
      ((θ.withDensity (fun p => ENNReal.ofReal (a i p))).map (g i)) (φ ⁻¹' s) =
      ∫⁻ p, ENNReal.ofReal (a i p * s.indicator (1 : ℝ → ℝ) (φ (g i p))) ∂θ := by
    intro i
    rw [Measure.map_apply (hg i) (hφ hs),
      withDensity_apply _ ((hg i) (hφ hs)),
      ← lintegral_indicator ((hg i) (hφ hs))]
    refine lintegral_congr fun p => ?_
    by_cases h : φ (g i p) ∈ s
    · have hp : p ∈ g i ⁻¹' (φ ⁻¹' s) := h
      simp [Set.indicator_of_mem hp, Set.indicator_of_mem h]
    · have hp : p ∉ g i ⁻¹' (φ ⁻¹' s) := h
      simp [Set.indicator_of_notMem hp, Set.indicator_of_notMem h]
  simp_rw [hterm]
  rw [← lintegral_finsetSum (f := fun i p => ENNReal.ofReal (a i p * s.indicator (1 : ℝ → ℝ) (φ (g i p))))
    _ fun i _ => ENNReal.measurable_ofReal.comp ((ha_meas i).mul
      ((measurable_const.indicator hs).comp (hφ.comp (hg i))))]
  refine lintegral_congr fun p => ?_
  exact (ENNReal.ofReal_sum_of_nonneg fun i _ =>
    mul_nonneg (ha0 i p) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)).symm

end MartOTVarCaseTwoAux

open MartOTVarCaseTwoAux in
theorem solution (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : ConvexLE μ ν) (c : ℝ → ℝ → ℝ)
    (hc : Measurable (Function.uncurry c)) (hint : SuffIntegrable μ ν c)
    (π : Measure (ℝ × ℝ)) (hπ : IsOptimal c μ ν π) (hfin : cost c π < ⊤) (n : ℕ) :
    ¬ ∃ γ : Measure (Fin n → ℝ × ℝ), 0 < γ (BadTuples c n) ∧
        ∀ i, γ.map (fun z : Fin n → ℝ × ℝ => z i) ≤ π := by
  classical
  rintro ⟨γ, hγpos, hγle⟩
  by_cases hn0 : n = 0
  · subst hn0
    have hempty : BadTuples c 0 = ∅ := by
      ext p
      simp only [BadTuples, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists,
        not_and]
      intro α _ hαconc α' hcomp hlt
      have hr : Set.range p = ∅ := Set.range_eq_empty p
      rw [hr, Set.compl_empty] at hαconc
      have hα0 : α = 0 := Measure.measure_univ_eq_zero.mp hαconc
      have hα'0 : α' = 0 := by
        refine Measure.measure_univ_eq_zero.mp ?_
        have h1 : α' Set.univ = (α'.map Prod.fst) Set.univ := by
          rw [Measure.map_apply measurable_fst MeasurableSet.univ]; rfl
        rw [h1, ← hcomp.1, hα0]; simp
      rw [hα0, hα'0] at hlt
      exact lt_irrefl _ hlt
    rw [hempty, measure_empty] at hγpos
    exact lt_irrefl _ hγpos
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hπ_prob : IsProbabilityMeasure π := by
    constructor
    have h1 : π Set.univ = (π.map Prod.fst) Set.univ := by
      rw [Measure.map_apply measurable_fst MeasurableSet.univ]; rfl
    rw [h1, hπ.1.1.1, measure_univ]
  have hγ_fin : IsFiniteMeasure γ := by
    constructor
    have hi : γ Set.univ = (γ.map (fun z : Fin n → ℝ × ℝ => z ⟨0, hn⟩)) Set.univ := by
      rw [Measure.map_apply (measurable_pi_apply (⟨0, hn⟩ : Fin n)) MeasurableSet.univ]; rfl
    rw [hi]
    exact lt_of_le_of_lt (hγle ⟨0, hn⟩ Set.univ) (measure_lt_top π _)
  -- Step 1: find m₀, K₀ with 0 < γ (BadSimplex c n m₀ K₀)
  have hpos_union : 0 < γ (⋃ m : ℕ, ⋃ K : ℕ, BadSimplex c n m K) :=
    lt_of_lt_of_le hγpos (measure_mono (badTuples_subset_iUnion_badSimplex c hn))
  have hex_m : ∃ m : ℕ, 0 < γ (⋃ K : ℕ, BadSimplex c n m K) := by
    by_contra hall
    push Not at hall
    have h0 : γ (⋃ m : ℕ, ⋃ K : ℕ, BadSimplex c n m K) = 0 :=
      measure_iUnion_null fun m => le_antisymm (hall m) bot_le
    exact hpos_union.ne' h0
  obtain ⟨m₀, hm₀⟩ := hex_m
  have hex_K : ∃ K : ℕ, 0 < γ (BadSimplex c n m₀ K) := by
    by_contra hall
    push Not at hall
    have h0 : γ (⋃ K : ℕ, BadSimplex c n m₀ K) = 0 :=
      measure_iUnion_null fun K => le_antisymm (hall K) bot_le
    exact hm₀.ne' h0
  obtain ⟨K₀, hK₀⟩ := hex_K
  -- Step 2: lexicographic Borel selection on the closed constraint set F
  let d := n + n * n
  let δ : ℝ := 1 / ((m₀ : ℝ) + 1)
  have hδpos : 0 < δ := by positivity
  let Y := (RR n → Fin d → ℝ) × (Fin d → ℝ)
  let F : Set (Y × (Fin d → ℝ)) :=
    {q | (∀ j, 0 ≤ q.2 j) ∧ (∑ j, q.2 j = 1) ∧
      (∀ r : RR n, ∑ j, q.1.1 r j * q.2 j = 0) ∧
      ∑ j, q.1.2 j * q.2 j ≤ -δ}
  have hFclosed : IsClosed F := by
    have h1 : IsClosed {q : Y × (Fin d → ℝ) | ∀ j, 0 ≤ q.2 j} := by
      have : {q : Y × (Fin d → ℝ) | ∀ j, 0 ≤ q.2 j} = ⋂ j, {q | 0 ≤ q.2 j} := by ext q; simp
      rw [this]
      exact isClosed_iInter fun j =>
        isClosed_le continuous_const ((continuous_apply j).comp continuous_snd)
    have h2 : IsClosed {q : Y × (Fin d → ℝ) | ∑ j, q.2 j = 1} :=
      isClosed_eq (continuous_finsetSum _ fun j _ => (continuous_apply j).comp continuous_snd)
        continuous_const
    have h3 : IsClosed {q : Y × (Fin d → ℝ) | ∀ r : RR n, ∑ j, q.1.1 r j * q.2 j = 0} := by
      have : {q : Y × (Fin d → ℝ) | ∀ r : RR n, ∑ j, q.1.1 r j * q.2 j = 0} =
          ⋂ r : RR n, {q | ∑ j, q.1.1 r j * q.2 j = 0} := by ext q; simp
      rw [this]
      exact isClosed_iInter fun r => isClosed_eq
        (continuous_finsetSum _ fun j _ =>
          ((continuous_apply j).comp ((continuous_apply r).comp
            (continuous_fst.comp continuous_fst))).mul
            ((continuous_apply j).comp continuous_snd))
        continuous_const
    have h4 : IsClosed {q : Y × (Fin d → ℝ) | ∑ j, q.1.2 j * q.2 j ≤ -δ} :=
      isClosed_le
        (continuous_finsetSum _ fun j _ =>
          ((continuous_apply j).comp (continuous_snd.comp continuous_fst)).mul
            ((continuous_apply j).comp continuous_snd))
        continuous_const
    exact h1.inter (h2.inter (h3.inter h4))
  have hFsub : F ⊆ Set.univ ×ˢ stdSimplex ℝ (Fin d) := fun q hq =>
    ⟨Set.mem_univ _, hq.1, hq.2.1⟩
  obtain ⟨hE_meas, sel, hsel_meas, hsel_mem⟩ := lex_borel_selection d F hFclosed hFsub
  let Av : (Fin n → ℝ × ℝ) → Y := fun p => (Amat p, vvec c p)
  have hAv_meas : Measurable Av := measurable_Av c hc n
  set B : Set (Fin n → ℝ × ℝ) := BadSimplex c n m₀ K₀
  have hB_eq : B =
      ({p : Fin n → ℝ × ℝ | (∀ i, |(p i).1| ≤ (K₀ : ℝ) ∧ |(p i).2| ≤ (K₀ : ℝ)) ∧
        (∀ i j, |c (p i).1 (p j).2| ≤ (K₀ : ℝ))} ∩ Av ⁻¹' (Prod.fst '' F)) := by
    ext p
    simp only [B, BadSimplex, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_image,
      Prod.exists, exists_and_right, exists_eq_right, F, Av, δ, stdSimplex]
    tauto
  have hB_meas : MeasurableSet B := by
    rw [hB_eq]
    have hx : ∀ i : Fin n, Measurable fun p : Fin n → ℝ × ℝ => (p i).1 :=
      fun i => measurable_fst.comp (measurable_pi_apply i)
    have hy : ∀ i : Fin n, Measurable fun p : Fin n → ℝ × ℝ => (p i).2 :=
      fun i => measurable_snd.comp (measurable_pi_apply i)
    have hbd1 : MeasurableSet {p : Fin n → ℝ × ℝ |
        ∀ i, |(p i).1| ≤ (K₀ : ℝ) ∧ |(p i).2| ≤ (K₀ : ℝ)} := by
      have : {p : Fin n → ℝ × ℝ | ∀ i, |(p i).1| ≤ (K₀ : ℝ) ∧ |(p i).2| ≤ (K₀ : ℝ)} =
          ⋂ i : Fin n, ({p | |(p i).1| ≤ (K₀ : ℝ)} ∩ {p | |(p i).2| ≤ (K₀ : ℝ)}) := by
        ext p; simp
      rw [this]
      exact MeasurableSet.iInter fun i =>
        (measurableSet_le (hx i).abs measurable_const).inter
          (measurableSet_le (hy i).abs measurable_const)
    have hbd2 : MeasurableSet {p : Fin n → ℝ × ℝ | ∀ i j, |c (p i).1 (p j).2| ≤ (K₀ : ℝ)} := by
      have : {p : Fin n → ℝ × ℝ | ∀ i j, |c (p i).1 (p j).2| ≤ (K₀ : ℝ)} =
          ⋂ i : Fin n, ⋂ j : Fin n, {p | |c (p i).1 (p j).2| ≤ (K₀ : ℝ)} := by
        ext p; simp
      rw [this]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
        measurableSet_le (hc.comp ((hx i).prodMk (hy j))).abs measurable_const
    exact (hbd1.inter hbd2).inter (hAv_meas hE_meas)
  -- Step 3: restrict γ to B and define measurable weights u, u'
  let θ : Measure (Fin n → ℝ × ℝ) := γ.restrict B
  have hθ_fin : IsFiniteMeasure θ := isFiniteMeasure_of_le γ Measure.restrict_le_self
  have hθ_pos : 0 < θ Set.univ := by rwa [Measure.restrict_apply_univ]
  have hθ_ae : ∀ᵐ p ∂θ, p ∈ B := ae_restrict_mem hB_meas
  let u : Fin n → (Fin n → ℝ × ℝ) → ℝ := fun i p =>
    if p ∈ B then sel (Av p) (eK n (Sum.inl i)) else 0
  let u' : Fin n × Fin n → (Fin n → ℝ × ℝ) → ℝ := fun ij p =>
    if p ∈ B then sel (Av p) (eK n (Sum.inr ij)) else 0
  have hu_meas : ∀ i, Measurable (u i) := fun i =>
    Measurable.ite hB_meas ((measurable_pi_apply _).comp (hsel_meas.comp hAv_meas)) measurable_const
  have hu'_meas : ∀ ij, Measurable (u' ij) := fun ij =>
    Measurable.ite hB_meas ((measurable_pi_apply _).comp (hsel_meas.comp hAv_meas)) measurable_const
  have hsel_B : ∀ p ∈ B, (Av p, sel (Av p)) ∈ F := fun p hp => by
    rw [hB_eq] at hp
    exact hsel_mem (Av p) hp.2
  have hu0 : ∀ i p, 0 ≤ u i p := fun i p => by
    dsimp only [u]; split_ifs with hp
    · exact (hsel_B p hp).1 _
    · exact le_rfl
  have hu'0 : ∀ ij p, 0 ≤ u' ij p := fun ij p => by
    dsimp only [u']; split_ifs with hp
    · exact (hsel_B p hp).1 _
    · exact le_rfl
  have hu1 : ∀ i p, u i p ≤ 1 := fun i p => by
    dsimp only [u]; split_ifs with hp
    · have h := hsel_B p hp
      calc sel (Av p) (eK n (Sum.inl i))
          ≤ ∑ j, sel (Av p) j := Finset.single_le_sum (fun j _ => h.1 j) (Finset.mem_univ _)
        _ = 1 := h.2.1
    · exact zero_le_one
  have hu'1 : ∀ ij p, u' ij p ≤ 1 := fun ij p => by
    dsimp only [u']; split_ifs with hp
    · have h := hsel_B p hp
      calc sel (Av p) (eK n (Sum.inr ij))
          ≤ ∑ j, sel (Av p) j := Finset.single_le_sum (fun j _ => h.1 j) (Finset.mem_univ _)
        _ = 1 := h.2.1
    · exact zero_le_one
  -- Pointwise algebraic competitor equations for every p
  have hEq_fst : ∀ p (b : ℝ),
      ∑ i : Fin n, (if (p i).1 = b then u i p else 0) =
      ∑ ij : Fin n × Fin n, (if (grid p ij).1 = b then u' ij p else 0) := by
    intro p b
    by_cases hp : p ∈ B
    · by_cases hb : ∃ k : Fin n, (p k).1 = b
      · rcases hb with ⟨k, rfl⟩
        have hr := (hsel_B p hp).2.2.1 (Sum.inl k)
        have heq : ∑ j, Amat p (Sum.inl k) j * sel (Av p) j =
            ∑ κ : KK n, AmatKK p (Sum.inl k) κ * sel (Av p) (eK n κ) := by
          refine Fintype.sum_equiv (eK n).symm _ _ fun j => ?_
          simp [Amat]
        rw [heq, Fintype.sum_sum_type] at hr
        simp only [AmatKK, Sum.elim_inl, Sum.elim_inr] at hr
        have s1 : ∑ i : Fin n, (if (p i).1 = (p k).1 then (1 : ℝ) else 0) *
              sel (Av p) (eK n (Sum.inl i)) =
            ∑ i : Fin n, if (p i).1 = (p k).1 then u i p else 0 :=
          Finset.sum_congr rfl fun i _ => by simp only [u, if_pos hp]; split_ifs <;> ring
        have s2 : ∑ ij : Fin n × Fin n, (-(if (p ij.1).1 = (p k).1 then (1 : ℝ) else 0)) *
              sel (Av p) (eK n (Sum.inr ij)) =
            -(∑ ij : Fin n × Fin n, if (grid p ij).1 = (p k).1 then u' ij p else 0) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun ij _ => ?_
          simp only [u', grid, if_pos hp]; split_ifs <;> ring
        rw [s1, s2] at hr
        linarith
      · push Not at hb
        have h1 : ∀ i : Fin n, (if (p i).1 = b then u i p else 0) = 0 := fun i => if_neg (hb i)
        have h2 : ∀ ij : Fin n × Fin n, (if (grid p ij).1 = b then u' ij p else 0) = 0 :=
          fun ij => if_neg (hb ij.1)
        simp [h1, h2]
    · simp [u, u', hp]
  have hEq_snd : ∀ p (b : ℝ),
      ∑ i : Fin n, (if (p i).2 = b then u i p else 0) =
      ∑ ij : Fin n × Fin n, (if (grid p ij).2 = b then u' ij p else 0) := by
    intro p b
    by_cases hp : p ∈ B
    · by_cases hb : ∃ k : Fin n, (p k).2 = b
      · rcases hb with ⟨k, rfl⟩
        have hr := (hsel_B p hp).2.2.1 (Sum.inr (Sum.inl k))
        have heq : ∑ j, Amat p (Sum.inr (Sum.inl k)) j * sel (Av p) j =
            ∑ κ : KK n, AmatKK p (Sum.inr (Sum.inl k)) κ * sel (Av p) (eK n κ) := by
          refine Fintype.sum_equiv (eK n).symm _ _ fun j => ?_
          simp [Amat]
        rw [heq, Fintype.sum_sum_type] at hr
        simp only [AmatKK, Sum.elim_inl, Sum.elim_inr] at hr
        have s1 : ∑ i : Fin n, (if (p i).2 = (p k).2 then (1 : ℝ) else 0) *
              sel (Av p) (eK n (Sum.inl i)) =
            ∑ i : Fin n, if (p i).2 = (p k).2 then u i p else 0 :=
          Finset.sum_congr rfl fun i _ => by simp only [u, if_pos hp]; split_ifs <;> ring
        have s2 : ∑ ij : Fin n × Fin n, (-(if (p ij.2).2 = (p k).2 then (1 : ℝ) else 0)) *
              sel (Av p) (eK n (Sum.inr ij)) =
            -(∑ ij : Fin n × Fin n, if (grid p ij).2 = (p k).2 then u' ij p else 0) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun ij _ => ?_
          simp only [u', grid, if_pos hp]; split_ifs <;> ring
        rw [s1, s2] at hr
        linarith
      · push Not at hb
        have h1 : ∀ i : Fin n, (if (p i).2 = b then u i p else 0) = 0 := fun i => if_neg (hb i)
        have h2 : ∀ ij : Fin n × Fin n, (if (grid p ij).2 = b then u' ij p else 0) = 0 :=
          fun ij => if_neg (hb ij.2)
        simp [h1, h2]
    · simp [u, u', hp]
  have hEq_bary : ∀ p (b : ℝ),
      ∑ i : Fin n, (if (p i).1 = b then u i p * (p i).2 else 0) =
      ∑ ij : Fin n × Fin n, (if (grid p ij).1 = b then u' ij p * (grid p ij).2 else 0) := by
    intro p b
    by_cases hp : p ∈ B
    · by_cases hb : ∃ k : Fin n, (p k).1 = b
      · rcases hb with ⟨k, rfl⟩
        have hr := (hsel_B p hp).2.2.1 (Sum.inr (Sum.inr k))
        have heq : ∑ j, Amat p (Sum.inr (Sum.inr k)) j * sel (Av p) j =
            ∑ κ : KK n, AmatKK p (Sum.inr (Sum.inr k)) κ * sel (Av p) (eK n κ) := by
          refine Fintype.sum_equiv (eK n).symm _ _ fun j => ?_
          simp [Amat]
        rw [heq, Fintype.sum_sum_type] at hr
        simp only [AmatKK, Sum.elim_inl, Sum.elim_inr] at hr
        have s1 : ∑ i : Fin n, (if (p i).1 = (p k).1 then (p i).2 else 0) *
              sel (Av p) (eK n (Sum.inl i)) =
            ∑ i : Fin n, if (p i).1 = (p k).1 then u i p * (p i).2 else 0 :=
          Finset.sum_congr rfl fun i _ => by simp only [u, if_pos hp]; split_ifs <;> ring
        have s2 : ∑ ij : Fin n × Fin n, (-(if (p ij.1).1 = (p k).1 then (p ij.2).2 else 0)) *
              sel (Av p) (eK n (Sum.inr ij)) =
            -(∑ ij : Fin n × Fin n, if (grid p ij).1 = (p k).1 then u' ij p * (grid p ij).2 else 0) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun ij _ => ?_
          simp only [u', grid, if_pos hp]; split_ifs <;> ring
        rw [s1, s2] at hr
        linarith
      · push Not at hb
        have h1 : ∀ i : Fin n, (if (p i).1 = b then u i p * (p i).2 else 0) = 0 :=
          fun i => if_neg (hb i)
        have h2 : ∀ ij : Fin n × Fin n,
            (if (grid p ij).1 = b then u' ij p * (grid p ij).2 else 0) = 0 :=
          fun ij => if_neg (hb ij.1)
        simp [h1, h2]
    · simp [u, u', hp]
  have hIneq_cost : ∀ p ∈ B,
      (∑ ij : Fin n × Fin n, u' ij p * c (grid p ij).1 (grid p ij).2) -
        (∑ i : Fin n, u i p * c (p i).1 (p i).2) ≤ -δ := by
    intro p hp
    have hr := (hsel_B p hp).2.2.2
    have heq : ∑ j, vvec c p j * sel (Av p) j =
        ∑ κ : KK n, vvecKK c p κ * sel (Av p) (eK n κ) := by
      refine Fintype.sum_equiv (eK n).symm _ _ fun j => ?_
      simp [vvec]
    rw [heq, Fintype.sum_sum_type] at hr
    simp only [vvecKK, Sum.elim_inl, Sum.elim_inr] at hr
    have s1 : ∑ i : Fin n, -c (p i).1 (p i).2 * sel (Av p) (eK n (Sum.inl i)) =
        -(∑ i : Fin n, u i p * c (p i).1 (p i).2) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [u, if_pos hp]; ring
    have s2 : ∑ ij : Fin n × Fin n, c (p ij.1).1 (p ij.2).2 * sel (Av p) (eK n (Sum.inr ij)) =
        ∑ ij : Fin n × Fin n, u' ij p * c (grid p ij).1 (grid p ij).2 :=
      Finset.sum_congr rfl fun ij _ => by simp only [u', grid, if_pos hp]; ring
    rw [s1, s2] at hr
    linarith
  -- Step 4: define ω and ω'
  let g_orig : Fin n → (Fin n → ℝ × ℝ) → ℝ × ℝ := fun i p => p i
  let g_grid : Fin n × Fin n → (Fin n → ℝ × ℝ) → ℝ × ℝ := fun ij p => grid p ij
  have hg_orig : ∀ i, Measurable (g_orig i) := fun i => measurable_pi_apply i
  have hg_grid : ∀ ij, Measurable (g_grid ij) := fun ij =>
    (measurable_fst.comp (measurable_pi_apply ij.1)).prodMk
      (measurable_snd.comp (measurable_pi_apply ij.2))
  let ω : Measure (ℝ × ℝ) :=
    (n : ENNReal)⁻¹ • ∑ i : Fin n, (θ.withDensity (fun p => ENNReal.ofReal (u i p))).map (g_orig i)
  let ω' : Measure (ℝ × ℝ) :=
    (n : ENNReal)⁻¹ • ∑ ij : Fin n × Fin n,
      (θ.withDensity (fun p => ENNReal.ofReal (u' ij p))).map (g_grid ij)
  -- Step 5: ω ≤ π (hence IsFiniteMeasure ω)
  have hωπ : ω ≤ π := by
    have hpiece : ∀ i : Fin n,
        (θ.withDensity (fun p => ENNReal.ofReal (u i p))).map (g_orig i) ≤ π := fun i => by
      have h1 : θ.withDensity (fun p => ENNReal.ofReal (u i p)) ≤ γ := by
        calc θ.withDensity (fun p => ENNReal.ofReal (u i p))
            ≤ θ.withDensity 1 := withDensity_mono (ae_of_all _ fun p => by
              simpa using ENNReal.ofReal_le_ofReal (hu1 i p))
          _ = θ := by simp
          _ ≤ γ := Measure.restrict_le_self
      have hmap : (θ.withDensity (fun p => ENNReal.ofReal (u i p))).map (g_orig i) ≤
          γ.map (g_orig i) :=
        Measure.le_iff.2 fun s hs => by
          rw [Measure.map_apply (hg_orig i) hs, Measure.map_apply (hg_orig i) hs]
          exact h1 _
      exact hmap.trans (hγle i)
    intro s
    simp only [ω, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
    calc (n : ENNReal)⁻¹ * ∑ i : Fin n,
          ((θ.withDensity (fun p => ENNReal.ofReal (u i p))).map (g_orig i)) s
        ≤ (n : ENNReal)⁻¹ * ∑ _i : Fin n, π s := by
          gcongr with i
          exact hpiece i
      _ = (n : ENNReal)⁻¹ * ((n : ENNReal) * π s) := by simp
      _ = π s := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr hn0) (ENNReal.natCast_ne_top n),
            one_mul]
  have : IsFiniteMeasure ω := isFiniteMeasure_of_le π hωπ
  -- Step 6: IsCompetitor ω ω'
  have hbd_y_orig : ∀ i : Fin n, ∀ᵐ p ∂θ, |(g_orig i p).2| ≤ (K₀ : ℝ) := fun i => by
    filter_upwards [hθ_ae] with p hp
    exact (hp.1 i).2
  have hbd_y_grid : ∀ ij : Fin n × Fin n, ∀ᵐ p ∂θ, |(g_grid ij p).2| ≤ (K₀ : ℝ) := fun ij => by
    filter_upwards [hθ_ae] with p hp
    exact (hp.1 ij.2).2
  have hcomp : IsCompetitor ω ω' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · ext s hs
      rw [avg_map_apply θ n hu_meas hu0 hg_orig measurable_fst hs,
        avg_map_apply θ n hu'_meas hu'0 hg_grid measurable_fst hs]
      congr 1
      refine lintegral_congr fun p => congr_arg ENNReal.ofReal ?_
      exact fiber_transfer (fun i => (p i).1) (fun ij => (grid p ij).1)
        (fun i => u i p) (fun ij => u' ij p) (hEq_fst p) (s.indicator 1)
    · ext s hs
      rw [avg_map_apply θ n hu_meas hu0 hg_orig measurable_snd hs,
        avg_map_apply θ n hu'_meas hu'0 hg_grid measurable_snd hs]
      congr 1
      refine lintegral_congr fun p => congr_arg ENNReal.ofReal ?_
      exact fiber_transfer (fun i => (p i).2) (fun ij => (grid p ij).2)
        (fun i => u i p) (fun ij => u' ij p) (hEq_snd p) (s.indicator 1)
    · exact avg_integrable θ hn0 hu1 hg_orig measurable_snd hbd_y_orig
    · exact avg_integrable θ hn0 hu'1 hg_grid measurable_snd hbd_y_grid
    · intro ρ hρm ⟨C, hC⟩
      let fρ : ℝ × ℝ → ℝ := fun q => ρ q.1 * q.2
      have hfρ : Measurable fρ := (hρm.comp measurable_fst).mul measurable_snd
      have hbd1 : ∀ i : Fin n, ∀ᵐ p ∂θ, |fρ (g_orig i p)| ≤ max C 0 * (K₀ : ℝ) := fun i => by
        filter_upwards [hθ_ae] with p hp
        dsimp only [fρ, g_orig]
        rw [abs_mul]
        exact mul_le_mul ((hC _).trans (le_max_left _ _)) (hp.1 i).2 (abs_nonneg _) (le_max_right _ _)
      have hbd2 : ∀ ij : Fin n × Fin n, ∀ᵐ p ∂θ, |fρ (g_grid ij p)| ≤ max C 0 * (K₀ : ℝ) :=
        fun ij => by
          filter_upwards [hθ_ae] with p hp
          dsimp only [fρ, g_grid, grid]
          rw [abs_mul]
          exact mul_le_mul ((hC _).trans (le_max_left _ _)) (hp.1 ij.2).2 (abs_nonneg _)
            (le_max_right _ _)
      change ∫ q, fρ q ∂ω = ∫ q, fρ q ∂ω'
      rw [avg_integral θ hu_meas hu0 hu1 hg_orig hfρ hbd1,
        avg_integral θ hu'_meas hu'0 hu'1 hg_grid hfρ hbd2]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun p => ?_)
      have h1 : ∑ i : Fin n, u i p * fρ (g_orig i p) =
          ∑ i : Fin n, (u i p * (p i).2) * ρ (p i).1 :=
        Finset.sum_congr rfl fun i _ => by dsimp only [fρ, g_orig]; ring
      have h2 : ∑ ij : Fin n × Fin n, u' ij p * fρ (g_grid ij p) =
          ∑ ij : Fin n × Fin n, (u' ij p * (grid p ij).2) * ρ (grid p ij).1 :=
        Finset.sum_congr rfl fun ij _ => by dsimp only [fρ, g_grid]; ring
      dsimp only
      rw [h1, h2]
      exact fiber_transfer (fun i => (p i).1) (fun ij => (grid p ij).1)
        (fun i => u i p * (p i).2) (fun ij => u' ij p * (grid p ij).2) (hEq_bary p) ρ
  -- Step 7: cost c ω' < cost c ω
  let fc : ℝ × ℝ → ℝ := fun q => c q.1 q.2
  have hfc : Measurable fc := hc
  have hbd_c_orig : ∀ i : Fin n, ∀ᵐ p ∂θ, |fc (g_orig i p)| ≤ (K₀ : ℝ) := fun i => by
    filter_upwards [hθ_ae] with p hp
    exact hp.2.1 i i
  have hbd_c_grid : ∀ ij : Fin n × Fin n, ∀ᵐ p ∂θ, |fc (g_grid ij p)| ≤ (K₀ : ℝ) := fun ij => by
    filter_upwards [hθ_ae] with p hp
    exact hp.2.1 ij.1 ij.2
  have hlt : cost c ω' < cost c ω := by
    unfold cost
    rw [integralE_eq_coe ω _ (avg_integrable θ hn0 hu1 hg_orig hfc hbd_c_orig),
      integralE_eq_coe ω' _ (avg_integrable θ hn0 hu'1 hg_grid hfc hbd_c_grid)]
    norm_cast
    change ∫ q, fc q ∂ω' < ∫ q, fc q ∂ω
    rw [avg_integral θ hu_meas hu0 hu1 hg_orig hfc hbd_c_orig,
      avg_integral θ hu'_meas hu'0 hu'1 hg_grid hfc hbd_c_grid]
    have hn_inv : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hn)
    refine mul_lt_mul_of_pos_left ?_ hn_inv
    have hint1 : Integrable (fun p => ∑ i : Fin n, u i p * fc (g_orig i p)) θ :=
      integrable_finsetSum _ fun i _ =>
        piece_prod_integrable θ (hu_meas i) (hu0 i) (hu1 i) (hg_orig i) hfc (hbd_c_orig i)
    have hint2 : Integrable (fun p => ∑ ij : Fin n × Fin n, u' ij p * fc (g_grid ij p)) θ :=
      integrable_finsetSum _ fun ij _ =>
        piece_prod_integrable θ (hu'_meas ij) (hu'0 ij) (hu'1 ij) (hg_grid ij) hfc (hbd_c_grid ij)
    rw [← sub_neg, ← integral_sub hint2 hint1]
    have hle : ∫ p, ((∑ ij : Fin n × Fin n, u' ij p * fc (g_grid ij p)) -
        (∑ i : Fin n, u i p * fc (g_orig i p))) ∂θ ≤ ∫ _p, (-δ) ∂θ := by
      refine integral_mono_ae (hint2.sub hint1) (integrable_const _) ?_
      filter_upwards [hθ_ae] with p hp
      exact hIneq_cost p hp
    have hconst : ∫ _p, (-δ) ∂θ < 0 := by
      rw [integral_const, smul_eq_mul]
      have hθreal : 0 < (θ Set.univ).toReal :=
        ENNReal.toReal_pos hθ_pos.ne' (measure_ne_top θ _)
      have : θ.real Set.univ = (θ Set.univ).toReal := rfl
      rw [this]
      nlinarith
    exact lt_of_le_of_lt hle hconst
  -- Step 8: reroute_improves contradicts optimality of π
  have himp := MartOT.Var.reroute_improves μ ν hμν c hc hint π hπ.1 hfin ω ω' hωπ hcomp hlt
  exact not_lt.mpr (hπ.2 (π - ω + ω') himp.1) himp.2
