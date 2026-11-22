-- Prove2me | solution 1 for NashPoly.Generic.theorem_A_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:28:19.376377+00:00
-- url     : https://prove2.me/submissions/00767989-4cfd-43f9-9294-f1cd0792e1cd

import Mathlib
import Definitions.Def_NashPoly_Generic_Coef
import Definitions.Def_NashPoly_Generic_ComplexKKT

open MvPolynomial MeasureTheory NashPoly.Generic

namespace NashPolyTheoremA1Aux

/-! ### Part 1: Zero set of a nonzero multivariate real polynomial has Lebesgue measure zero -/

private lemma continuous_mvpoly_eval {ι : Type} [Fintype ι] (P : MvPolynomial ι ℝ) :
    Continuous (fun x : ι → ℝ => MvPolynomial.eval x P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simpa only [eval_C] using (continuous_const : Continuous (fun _ : ι → ℝ => a))
  | add p q hp hq =>
    have h : Continuous (fun x : ι → ℝ => MvPolynomial.eval x p + MvPolynomial.eval x q) :=
      Continuous.add hp hq
    simpa only [map_add] using h
  | mul_X p i hp =>
    have h : Continuous (fun x : ι → ℝ => MvPolynomial.eval x p * x i) :=
      Continuous.mul hp (continuous_apply i)
    simpa only [map_mul, eval_X] using h

private lemma volume_mvpoly_eval_eq_zero_fin :
    ∀ (k : ℕ) (P : MvPolynomial (Fin k) ℝ), P ≠ 0 →
      volume {x : Fin k → ℝ | MvPolynomial.eval x P = 0} = 0
  | 0, P, hP => by
    have hne : ∀ x : Fin 0 → ℝ, MvPolynomial.eval x P ≠ 0 := by
      intro x hx
      apply hP
      have heq : P = MvPolynomial.C (MvPolynomial.eval x P) := by
        ext s
        have hs : s = 0 := by ext i; exact Fin.elim0 i
        subst hs
        rw [MvPolynomial.coeff_C, if_pos rfl, MvPolynomial.eval_eq']
        by_cases h0 : (0 : Fin 0 →₀ ℕ) ∈ P.support
        · rw [Finset.sum_eq_single 0]
          · simp
          · intro t _ ht
            exact (ht (by ext i; exact Fin.elim0 i)).elim
          · intro h; exact (h h0).elim
        · have hsupp : P.support = ∅ := by
            ext t
            simp only [Finset.notMem_empty, iff_false]
            have ht : t = 0 := by ext i; exact Fin.elim0 i
            rwa [ht]
          rw [hsupp, Finset.sum_empty]
          exact MvPolynomial.notMem_support_iff.mp h0
      rw [heq, hx, map_zero]
    have hempty : {x : Fin 0 → ℝ | MvPolynomial.eval x P = 0} = ∅ := by
      ext x
      simp [hne x]
    rw [hempty, measure_empty]
  | k + 1, P, hP => by
    let Q : Polynomial (MvPolynomial (Fin k) ℝ) := MvPolynomial.finSuccEquiv ℝ k P
    have hQ : Q ≠ 0 := by
      intro h0
      exact hP ((MvPolynomial.finSuccEquiv ℝ k).injective (by simp [Q, h0]))
    let L : MvPolynomial (Fin k) ℝ := Q.leadingCoeff
    have hL : L ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
    have hIH : volume {x' : Fin k → ℝ | MvPolynomial.eval x' L = 0} = 0 :=
      volume_mvpoly_eval_eq_zero_fin k L hL
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0
    have hmp : MeasurePreserving e volume (volume.prod volume) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0
    let S : Set (Fin (k + 1) → ℝ) := {x | MvPolynomial.eval x P = 0}
    let T : Set (ℝ × (Fin k → ℝ)) := {p | MvPolynomial.eval (Fin.cons p.1 p.2) P = 0}
    have hT_meas : MeasurableSet T := by
      have hcons : Continuous (fun p : ℝ × (Fin k → ℝ) => (Fin.cons p.1 p.2 : Fin (k + 1) → ℝ)) := by
        apply continuous_pi
        intro i
        refine Fin.cases ?_ ?_ i
        · simpa using continuous_fst
        · intro j
          have hc : Continuous (fun p : ℝ × (Fin k → ℝ) => p.2 j) :=
            (continuous_apply j).comp continuous_snd
          simpa using hc
      exact (isClosed_eq ((continuous_mvpoly_eval P).comp hcons) continuous_const).measurableSet
    have hpre : e ⁻¹' T = S := by
      ext x
      change MvPolynomial.eval (Fin.cons (e x).1 (e x).2) P = 0 ↔ MvPolynomial.eval x P = 0
      have hx : Fin.cons (e x).1 (e x).2 = x := by
        ext i
        refine Fin.cases ?_ ?_ i
        · simp [e]
        · intro j
          simp [e, Fin.tail]
      rw [hx]
    change volume S = 0
    rw [← hpre, hmp.measure_preimage hT_meas.nullMeasurableSet]
    rw [Measure.prod_apply_symm hT_meas]
    have hae : ∀ᵐ x' ∂(volume : Measure (Fin k → ℝ)),
        volume ((fun t : ℝ => (t, x')) ⁻¹' T) = 0 := by
      have hne_ae : ∀ᵐ x' ∂(volume : Measure (Fin k → ℝ)), MvPolynomial.eval x' L ≠ 0 := by
        rw [ae_iff]
        simpa using hIH
      filter_upwards [hne_ae] with x' hx'
      let q : Polynomial ℝ := Q.map (MvPolynomial.eval x')
      have hq_ne : q ≠ 0 := by
        intro hq0
        have hc : q.coeff Q.natDegree = 0 := by rw [hq0]; simp
        rw [Polynomial.coeff_map] at hc
        exact hx' hc
      have hset : ((fun t : ℝ => (t, x')) ⁻¹' T) = {t : ℝ | q.IsRoot t} := by
        ext t
        change MvPolynomial.eval (Fin.cons t x') P = 0 ↔ q.IsRoot t
        simp only [Polynomial.IsRoot, q, Q]
        rw [MvPolynomial.eval_eq_eval_mv_eval']
      rw [hset]
      exact (Polynomial.finite_setOfPred_isRoot hq_ne).measure_zero volume
    rw [lintegral_congr_ae hae, lintegral_zero]

private lemma volume_mvpoly_eval_eq_zero {ι : Type} [Fintype ι]
    (P : MvPolynomial ι ℝ) (hP : P ≠ 0) :
    volume {x : ι → ℝ | MvPolynomial.eval x P = 0} = 0 := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let P' : MvPolynomial (Fin (Fintype.card ι)) ℝ := MvPolynomial.renameEquiv ℝ e.symm P
  have hP' : P' ≠ 0 := by
    intro h0
    exact hP ((MvPolynomial.renameEquiv ℝ e.symm).injective (by simp [P', h0]))
  have h0 : volume {x : Fin (Fintype.card ι) → ℝ | MvPolynomial.eval x P' = 0} = 0 :=
    volume_mvpoly_eval_eq_zero_fin (Fintype.card ι) P' hP'
  let me : (Fin (Fintype.card ι) → ℝ) ≃ᵐ (ι → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e
  have hmp : MeasurePreserving me volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) e
  let S : Set (ι → ℝ) := {x | MvPolynomial.eval x P = 0}
  have hS_meas : MeasurableSet S :=
    (isClosed_eq (continuous_mvpoly_eval P) continuous_const).measurableSet
  have hpre : me ⁻¹' S = {x : Fin (Fintype.card ι) → ℝ | MvPolynomial.eval x P' = 0} := by
    ext x
    change MvPolynomial.eval (me x) P = 0 ↔ MvPolynomial.eval x P' = 0
    simp only [P', MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename]
    have hcomp : me x ∘ e = x := by
      ext j
      simp [me, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
    have hcomp2 : x ∘ e.symm = me x := by
      ext i
      have := congrFun hcomp (e.symm i)
      simpa using this.symm
    rw [hcomp2]
  change volume S = 0
  rw [← hmp.measure_preimage hS_meas.nullMeasurableSet, hpre]
  exact h0

/-! ### Part 2: Algebraic dependence of k + 1 polynomials in k variables over any field -/

private lemma exists_nonzero_mvpoly_relation {K : Type*} [Field K] {ι : Type} [Fintype ι]
    (F : ι → MvPolynomial ι K) (G : MvPolynomial ι K) :
    ∃ P : MvPolynomial (Option ι) K,
      P ≠ 0 ∧ MvPolynomial.aeval (fun u : Option ι => Option.elim u G F) P = 0 := by
  classical
  let k : ℕ := Fintype.card ι
  let D : ℕ := max G.totalDegree (Finset.univ.sup (fun j => (F j).totalDegree)) + 1
  let C : ℕ := (k + 1) * D + 1
  let M : ℕ := (C + 1) ^ k
  have hM_pos : 1 ≤ M := Nat.one_le_pow k (C + 1) (Nat.succ_pos C)
  let Sdom : Finset (Option ι →₀ ℕ) :=
    (Fintype.piFinset (fun _ : Option ι => Finset.range (M + 1))).image
      Finsupp.equivFunOnFinite.symm
  let Scod : Finset (ι →₀ ℕ) :=
    (Fintype.piFinset (fun _ : ι => Finset.range (C * M + 1))).image
      Finsupp.equivFunOnFinite.symm
  have hcard_dom : Sdom.card = (M + 1) ^ (k + 1) := by
    rw [Finset.card_image_of_injective _ Finsupp.equivFunOnFinite.symm.injective,
      Fintype.card_piFinset]
    simp [k]
  have hcard_cod : Scod.card = (C * M + 1) ^ k := by
    rw [Finset.card_image_of_injective _ Finsupp.equivFunOnFinite.symm.injective,
      Fintype.card_piFinset]
    simp [k]
  have hcard_lt : Scod.card < Sdom.card := by
    rw [hcard_dom, hcard_cod]
    have h1 : C * M + 1 ≤ (C + 1) * M := by
      have : (C + 1) * M = C * M + M := by ring
      omega
    have h2 : (C * M + 1) ^ k ≤ ((C + 1) * M) ^ k := Nat.pow_le_pow_left h1 k
    have h3 : ((C + 1) * M) ^ k = M ^ (k + 1) := by
      rw [mul_pow, pow_succ']
    have h4 : M ^ (k + 1) < (M + 1) ^ (k + 1) :=
      Nat.pow_lt_pow_left (Nat.lt_succ_self M) (Nat.succ_ne_zero k)
    exact lt_of_le_of_lt (h2.trans_eq h3) h4
  let toPoly : (Sdom → K) →ₗ[K] MvPolynomial (Option ι) K :=
    { toFun := fun v => ∑ s : Sdom, MvPolynomial.monomial s.1 (v s)
      map_add' := fun v w => by
        simp [map_add, Finset.sum_add_distrib]
      map_smul' := fun r v => by
        simp [Finset.smul_sum, MvPolynomial.smul_monomial] }
  have htoPoly_inj : Function.Injective toPoly := by
    intro v w hvw
    ext ⟨s, hs⟩
    have hc := congrArg (fun p => MvPolynomial.coeff s p) hvw
    change MvPolynomial.coeff s (∑ t : Sdom, MvPolynomial.monomial t.1 (v t)) =
      MvPolynomial.coeff s (∑ t : Sdom, MvPolynomial.monomial t.1 (w t)) at hc
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_sum] at hc
    simp_rw [MvPolynomial.coeff_monomial] at hc
    have hsum : ∀ u : Sdom → K,
        (∑ t ∈ Sdom.attach, if t.1 = s then u t else 0) = u ⟨s, hs⟩ := by
      intro u
      rw [Finset.sum_eq_single ⟨s, hs⟩]
      · simp
      · intro t _ ht
        have hne : t.1 ≠ s := fun h => ht (Subtype.ext h)
        simp [hne]
      · intro hmem; exact (hmem (Finset.mem_attach _ _)).elim
    change (∑ t ∈ Sdom.attach, if t.1 = s then v t else 0) =
      (∑ t ∈ Sdom.attach, if t.1 = s then w t else 0) at hc
    rw [hsum v, hsum w] at hc
    exact hc
  let val : Option ι → MvPolynomial ι K := fun u => Option.elim u G F
  have hdeg_le : ∀ u : Option ι, (val u).totalDegree ≤ D := by
    intro u
    cases u with
    | none =>
      simp only [val, Option.elim_none, D]
      exact le_trans (le_max_left _ _) (Nat.le_succ _)
    | some j =>
      simp only [val, Option.elim_some, D]
      exact le_trans (le_trans (Finset.le_sup (f := fun j => (F j).totalDegree) (Finset.mem_univ j))
        (le_max_right _ _)) (Nat.le_succ _)
  have hsupp_mono : ∀ s ∈ Sdom,
      (MvPolynomial.aeval val (MvPolynomial.monomial s (1 : K))).support ⊆ Scod := by
    intro s hs t ht
    have hs_le : ∀ u : Option ι, s u ≤ M := by
      rw [Finset.mem_image] at hs
      rcases hs with ⟨f, hf, rfl⟩
      intro u
      have hu := (Fintype.mem_piFinset.mp hf) u
      rw [Finset.mem_range] at hu
      have hfu : (Finsupp.equivFunOnFinite.symm f) u = f u := by
        change (Finsupp.equivFunOnFinite (Finsupp.equivFunOnFinite.symm f)) u = f u
        rw [Equiv.apply_symm_apply]
      rw [hfu]
      exact Nat.lt_succ_iff.mp hu
    have haeval_eq : MvPolynomial.aeval val (MvPolynomial.monomial s (1 : K)) =
        ∏ u : Option ι, (val u) ^ (s u) := by
      rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod_of_support_subset _
        (Finset.subset_univ s.support) _ (fun _ _ => pow_zero _)]
    have htd : (MvPolynomial.aeval val (MvPolynomial.monomial s (1 : K))).totalDegree
        ≤ C * M := by
      rw [haeval_eq]
      calc (∏ u : Option ι, (val u) ^ (s u)).totalDegree
          ≤ ∑ u : Option ι, ((val u) ^ (s u)).totalDegree :=
            MvPolynomial.totalDegree_finsetProd _ _
        _ ≤ ∑ u : Option ι, s u * (val u).totalDegree :=
            Finset.sum_le_sum fun u _ => MvPolynomial.totalDegree_pow _ _
        _ ≤ ∑ _u : Option ι, M * D :=
            Finset.sum_le_sum fun u _ => Nat.mul_le_mul (hs_le u) (hdeg_le u)
        _ = (k + 1) * (M * D) := by simp [k]
        _ ≤ C * M := by
            have : (k + 1) * (M * D) = ((k + 1) * D) * M := by ring
            rw [this]
            exact Nat.mul_le_mul_right M (Nat.le_succ _)
    have ht_le : ∀ j : ι, t j ≤ C * M := by
      intro j
      have h1 : t j ≤ t.sum (fun _ n => n) := by
        by_cases hj : j ∈ t.support
        · exact Finset.single_le_sum (f := fun i => t i) (fun _ _ => Nat.zero_le _) hj
        · simp [Finsupp.notMem_support_iff.mp hj]
      exact h1.trans ((MvPolynomial.le_totalDegree ht).trans htd)
    rw [Finset.mem_image]
    refine ⟨fun j => t j, Fintype.mem_piFinset.mpr fun j => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (ht_le j)), ?_⟩
    ext j
    change (Finsupp.equivFunOnFinite (Finsupp.equivFunOnFinite.symm fun j => t j)) j = t j
    rw [Equiv.apply_symm_apply]
  let evLin : (Sdom → K) →ₗ[K] MvPolynomial ι K :=
    (MvPolynomial.aeval val).toLinearMap.comp toPoly
  have hsupp_ev : ∀ v : Sdom → K, (evLin v).support ⊆ Scod := by
    intro v t ht
    have hsum_eq : evLin v = ∑ s : Sdom,
        MvPolynomial.C (v s) * MvPolynomial.aeval val (MvPolynomial.monomial s.1 (1 : K)) := by
      change MvPolynomial.aeval val (∑ s : Sdom, MvPolynomial.monomial s.1 (v s)) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      have hm : MvPolynomial.monomial s.1 (v s) = MvPolynomial.C (v s) * MvPolynomial.monomial s.1 1 := by
        rw [MvPolynomial.C_mul_monomial, mul_one]
      rw [hm, map_mul, MvPolynomial.aeval_C, Algebra.algebraMap_eq_smul_one, MvPolynomial.smul_eq_C_mul, mul_one]
    rw [hsum_eq] at ht
    have hmem := Finset.mem_biUnion.mp (MvPolynomial.support_sum ht)
    rcases hmem with ⟨s, _, hts⟩
    have hts' : t ∈ (MvPolynomial.aeval val (MvPolynomial.monomial s.1 (1 : K))).support := by
      rw [MvPolynomial.mem_support_iff] at hts ⊢
      rw [MvPolynomial.coeff_C_mul] at hts
      exact right_ne_zero_of_mul hts
    exact hsupp_mono s.1 s.2 hts'
  let φ : (Sdom → K) →ₗ[K] (Scod → K) :=
    { toFun := fun v t => MvPolynomial.coeff t.1 (evLin v)
      map_add' := fun v w => by ext t; simp [map_add]
      map_smul' := fun r v => by ext t; simp [map_smul] }
  have hnot_inj : ¬ Function.Injective φ := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_coe, Fintype.card_coe] at hle
    omega
  rw [Function.Injective] at hnot_inj
  push Not at hnot_inj
  rcases hnot_inj with ⟨v₁, v₂, hφeq, hne⟩
  let v : Sdom → K := v₁ - v₂
  have hv_ne : v ≠ 0 := sub_ne_zero.mpr hne
  have hφv : φ v = 0 := by
    simp [v, map_sub, hφeq]
  refine ⟨toPoly v, ?_, ?_⟩
  · intro h0
    exact hv_ne (htoPoly_inj (by simp [h0]))
  · change evLin v = 0
    ext t
    by_cases ht : t ∈ Scod
    · have := congrFun hφv ⟨t, ht⟩
      simpa [φ] using this
    · have ht' : t ∉ (evLin v).support := fun h => ht (hsupp_ev v h)
      simpa [MvPolynomial.mem_support_iff] using ht'

/-! ### Part 3: Clearing denominators to an integral domain -/

private lemma exists_nonzero_mvpoly_relation_domain {R : Type*} [CommRing R] [IsDomain R]
    {ι : Type} [Fintype ι] (F : ι → MvPolynomial ι R) (G : MvPolynomial ι R) :
    ∃ P : MvPolynomial (Option ι) R,
      P ≠ 0 ∧ MvPolynomial.aeval (fun u : Option ι => Option.elim u G F) P = 0 := by
  classical
  let K := FractionRing R
  let j : R →+* K := algebraMap R K
  have hj : Function.Injective j := IsFractionRing.injective R K
  let FK : ι → MvPolynomial ι K := fun u => MvPolynomial.map j (F u)
  let GK : MvPolynomial ι K := MvPolynomial.map j G
  rcases exists_nonzero_mvpoly_relation FK GK with ⟨PK, hPK_ne, hPK_zero⟩
  rcases IsLocalization.exist_integer_multiples (nonZeroDivisors R) PK.support
      (fun s => MvPolynomial.coeff s PK) with ⟨b, hb⟩
  choose r hr using fun s (hs : s ∈ PK.support) => hb s hs
  let PR : MvPolynomial (Option ι) R :=
    ∑ s ∈ PK.support.attach, MvPolynomial.monomial s.1 (r s.1 s.2)
  have hmap_PR : MvPolynomial.map j PR = MvPolynomial.C (j b.1) * PK := by
    ext s
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul]
    simp only [PR, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    by_cases hs : s ∈ PK.support
    · rw [Finset.sum_eq_single ⟨s, hs⟩]
      · simp only [↓reduceIte]
        have h := hr s hs
        rw [Algebra.smul_def] at h
        exact h
      · intro t _ ht
        have hne : t.1 ≠ s := fun h => ht (Subtype.ext h)
        simp [hne]
      · intro hmem; exact (hmem (Finset.mem_attach _ _)).elim
    · have h0 : MvPolynomial.coeff s PK = 0 := MvPolynomial.notMem_support_iff.mp hs
      rw [h0, mul_zero]
      have hsum0 : (∑ t ∈ PK.support.attach, if t.1 = s then r t.1 t.2 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro t _
        have hne : t.1 ≠ s := fun h => hs (h ▸ t.2)
        simp [hne]
      rw [hsum0, map_zero]
  have hb_ne : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hjb_ne : j b.1 ≠ 0 := by
    intro h0
    exact hb_ne (hj (by simpa using h0))
  have hPR_ne : PR ≠ 0 := by
    intro h0
    have hm : MvPolynomial.C (j b.1) * PK = 0 := by
      rw [← hmap_PR, h0, map_zero]
    have hC_ne : (MvPolynomial.C (j b.1) : MvPolynomial (Option ι) K) ≠ 0 := by
      intro hC0
      exact hjb_ne (MvPolynomial.C_injective (Option ι) K (by simpa using hC0))
    exact hPK_ne ((mul_eq_zero.mp hm).resolve_left hC_ne)
  have hPR_zero : MvPolynomial.aeval (fun u : Option ι => Option.elim u G F) PR = 0 := by
    apply MvPolynomial.map_injective j hj
    rw [map_zero]
    have hcomm :
        (MvPolynomial.map j).comp
          (MvPolynomial.aeval (fun u : Option ι => Option.elim u G F)).toRingHom =
        (MvPolynomial.aeval (fun u : Option ι => Option.elim u GK FK)).toRingHom.comp
          (MvPolynomial.map j) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [j]
      · intro u
        cases u <;> simp [GK, FK]
    have hev := RingHom.congr_fun hcomm PR
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] at hev
    rw [hev, hmap_PR, map_mul, hPK_zero, mul_zero]
  exact ⟨PR, hPR_ne, hPR_zero⟩

/-! ### Part 4: Zariski-generic finiteness for any parameterized polynomial map `F : ℂ^K → ℂ^K` -/

private lemma exists_poly_finiteness_certificate {ι Rest : Type} [Fintype ι] [Fintype Rest]
    (F : ι → MvPolynomial ι (MvPolynomial Rest ℝ)) :
    ∃ P : MvPolynomial (ι ⊕ Rest) ℝ, P ≠ 0 ∧
      ∀ (y : ι → ℝ) (r : Rest → ℝ),
        MvPolynomial.eval (Sum.elim y r) P ≠ 0 →
        {z : ι → ℂ | ∀ j : ι,
          MvPolynomial.eval₂ ((algebraMap ℝ ℂ).comp (MvPolynomial.eval r)) z (F j) =
            (y j : ℂ)}.Finite := by
  classical
  let R := MvPolynomial Rest ℝ
  have hrel : ∀ i : ι, ∃ P : MvPolynomial (Option ι) R,
      P ≠ 0 ∧ MvPolynomial.aeval (fun u : Option ι => Option.elim u (MvPolynomial.X i) F) P = 0 :=
    fun i => exists_nonzero_mvpoly_relation_domain F (MvPolynomial.X i)
  choose P_opt hP_ne hP_zero using hrel
  let Q : ι → Polynomial (MvPolynomial ι R) := fun i => MvPolynomial.optionEquivLeft R ι (P_opt i)
  have hQ_ne : ∀ i : ι, Q i ≠ 0 := by
    intro i h0
    exact hP_ne i ((MvPolynomial.optionEquivLeft R ι).injective (by simp [Q, h0]))
  let L : ι → MvPolynomial ι R := fun i => (Q i).leadingCoeff
  have hL_ne : ∀ i : ι, L i ≠ 0 := fun i => Polynomial.leadingCoeff_ne_zero.mpr (hQ_ne i)
  let Lprod : MvPolynomial ι R := ∏ i : ι, L i
  have hLprod_ne : Lprod ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hL_ne i
  let P : MvPolynomial (ι ⊕ Rest) ℝ := (MvPolynomial.sumAlgEquiv ℝ ι Rest).symm Lprod
  have hP_ne' : P ≠ 0 := by
    intro h0
    exact hLprod_ne ((MvPolynomial.sumAlgEquiv ℝ ι Rest).symm.injective (by simp [P, h0]))
  refine ⟨P, hP_ne', fun y r hyr => ?_⟩
  have heval_sum :
      (MvPolynomial.eval₂Hom (MvPolynomial.eval r) y).comp
        (MvPolynomial.sumAlgEquiv ℝ ι Rest).toRingHom =
      MvPolynomial.eval (Sum.elim y r) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro u
      cases u <;> simp
  have hLprod_eval : MvPolynomial.eval₂Hom (MvPolynomial.eval r) y Lprod ≠ 0 := by
    have h := RingHom.congr_fun heval_sum P
    change MvPolynomial.eval₂Hom (MvPolynomial.eval r) y (MvPolynomial.sumAlgEquiv ℝ ι Rest P) =
      MvPolynomial.eval (Sum.elim y r) P at h
    rw [show MvPolynomial.sumAlgEquiv ℝ ι Rest P = Lprod from
      AlgEquiv.apply_symm_apply (MvPolynomial.sumAlgEquiv ℝ ι Rest) Lprod] at h
    rw [h]
    exact hyr
  have hL_eval : ∀ i : ι, MvPolynomial.eval₂Hom (MvPolynomial.eval r) y (L i) ≠ 0 := by
    rw [map_prod] at hLprod_eval
    exact fun i => Finset.prod_ne_zero_iff.mp hLprod_eval i (Finset.mem_univ i)
  let ev_ry_C : MvPolynomial ι R →+* ℂ :=
    (algebraMap ℝ ℂ).comp (MvPolynomial.eval₂Hom (MvPolynomial.eval r) y)
  let q : ι → Polynomial ℂ := fun i => (Q i).map ev_ry_C
  have hq_ne : ∀ i : ι, q i ≠ 0 := by
    intro i hq0
    have hc : (q i).coeff (Q i).natDegree = 0 := by rw [hq0]; simp
    rw [Polynomial.coeff_map] at hc
    change ((MvPolynomial.eval₂Hom (MvPolynomial.eval r) y (L i) : ℝ) : ℂ) = 0 at hc
    exact hL_eval i (Complex.ofReal_eq_zero.mp hc)
  have hsub :
      {z : ι → ℂ | ∀ j : ι,
        MvPolynomial.eval₂ ((algebraMap ℝ ℂ).comp (MvPolynomial.eval r)) z (F j) = (y j : ℂ)} ⊆
      Set.pi Set.univ (fun i : ι => {w : ℂ | (q i).IsRoot w}) := by
    intro z hz i _
    change (q i).IsRoot (z i)
    simp only [Polynomial.IsRoot]
    let ev_z : MvPolynomial ι R →+* ℂ :=
      MvPolynomial.eval₂Hom ((algebraMap ℝ ℂ).comp (MvPolynomial.eval r)) z
    have hhom_eq :
        ev_z.comp (MvPolynomial.aeval (fun u : Option ι => Option.elim u (MvPolynomial.X i) F)).toRingHom =
        (Polynomial.evalRingHom (z i)).comp
          ((Polynomial.mapRingHom ev_ry_C).comp (MvPolynomial.optionEquivLeft R ι).toRingHom) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [ev_z, ev_ry_C, MvPolynomial.optionEquivLeft_apply]
      · intro u
        cases u with
        | none =>
          simp [ev_z, MvPolynomial.optionEquivLeft_apply]
        | some j =>
          simp [ev_z, ev_ry_C, MvPolynomial.optionEquivLeft_apply]
          exact hz j
    have hev := RingHom.congr_fun hhom_eq (P_opt i)
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, hP_zero i, map_zero] at hev
    simpa [q, Q] using hev.symm
  exact (Set.Finite.pi fun i => Polynomial.finite_setOfPred_isRoot (hq_ne i)).subset hsub

/-! ### Part 5: Reduction of `NashPoly.Generic.theorem_A_1` to Part 4 + Part 1 -/

private def linMono {N : ℕ} {n : Fin N → ℕ} {a : Fin N → Fin N → ℕ}
    (ha : ∀ i j, 0 < a i j) (i : Fin N) (k : Fin (n i)) : MonoF n a i :=
  ⟨fun v => if v = ⟨i, k⟩ then ⟨1, Nat.succ_lt_succ (ha i v.1)⟩ else ⟨0, Nat.zero_lt_succ _⟩,
   fun j => by
     by_cases hj : j = i
     · subst hj
       have hsum : (∑ k' : Fin (n j),
           ((if (⟨j, k'⟩ : Var n) = ⟨j, k⟩
             then (⟨1, Nat.succ_lt_succ (ha j j)⟩ : Fin (a j j + 1))
             else (⟨0, Nat.zero_lt_succ _⟩ : Fin (a j j + 1))) : ℕ)) =
           ∑ k' : Fin (n j), if k' = k then 1 else 0 := by
         refine Finset.sum_congr rfl fun k' _ => ?_
         by_cases hk : k' = k
         · subst hk; simp
         · have hne : (⟨j, k'⟩ : Var n) ≠ ⟨j, k⟩ := fun h => by
             cases h
             exact hk rfl
           simp [hk, hne]
       dsimp only
       simp only [apply_ite Fin.val]
       rw [hsum]
       simpa using Nat.succ_le_of_lt (ha j j)
     · have hsum : (∑ k' : Fin (n j),
           ((if (⟨j, k'⟩ : Var n) = ⟨i, k⟩
             then (⟨1, Nat.succ_lt_succ (ha i j)⟩ : Fin (a i j + 1))
             else (⟨0, Nat.zero_lt_succ _⟩ : Fin (a i j + 1))) : ℕ)) = 0 := by
         apply Finset.sum_eq_zero
         intro k' _
         have hne : (⟨j, k'⟩ : Var n) ≠ ⟨i, k⟩ := fun h => hj (congrArg Sigma.fst h)
         simp [hne]
       dsimp only
       simp only [apply_ite Fin.val]
       rw [hsum]
       exact Nat.zero_le _⟩

private def constMono {N : ℕ} {n m : Fin N → ℕ} {d : (i : Fin N) → Fin (m i) → ℕ}
    (i : Fin N) (j : Fin (m i)) : MonoG n m d i j :=
  ⟨fun _ => ⟨0, Nat.zero_lt_succ _⟩, by simp⟩

private lemma linMono_exp {N : ℕ} {n : Fin N → ℕ} {a : Fin N → Fin N → ℕ}
    (ha : ∀ i j, 0 < a i j) (i : Fin N) (k : Fin (n i)) :
    (Finsupp.equivFunOnFinite.symm fun v => ((linMono ha i k).1 v : ℕ)) =
      Finsupp.single ⟨i, k⟩ 1 := by
  ext v
  have h1 : (Finsupp.equivFunOnFinite.symm fun v => ((linMono ha i k).1 v : ℕ)) v =
      ((linMono ha i k).1 v : ℕ) := by
    let f : Var n → ℕ := fun v => ((linMono ha i k).1 v : ℕ)
    exact congrFun (Finsupp.equivFunOnFinite.apply_symm_apply f) v
  rw [h1, Finsupp.single_apply]
  dsimp [linMono]
  by_cases hv : v = ⟨i, k⟩
  · subst hv; simp
  · have hv' : (⟨i, k⟩ : Var n) ≠ v := Ne.symm hv
    simp [hv, hv']

private lemma constMono_exp {N : ℕ} {n m : Fin N → ℕ} {d : (i : Fin N) → Fin (m i) → ℕ}
    (i : Fin N) (j : Fin (m i)) :
    (Finsupp.equivFunOnFinite.symm fun k => ((constMono (n := n) (m := m) (d := d) i j).1 k : ℕ)) =
      0 := by
  ext k
  have h1 : (Finsupp.equivFunOnFinite.symm fun k =>
      ((constMono (n := n) (m := m) (d := d) i j).1 k : ℕ)) k =
      ((constMono (n := n) (m := m) (d := d) i j).1 k : ℕ) := by
    let f : Fin (n i) → ℕ := fun k => ((constMono (n := n) (m := m) (d := d) i j).1 k : ℕ)
    exact congrFun (Finsupp.equivFunOnFinite.apply_symm_apply f) k
  rw [h1]
  simp [constMono]

private abbrev Idx {N : ℕ} (n m : Fin N → ℕ) (a : Fin N → Fin N → ℕ)
    (d : (i : Fin N) → Fin (m i) → ℕ) : Type :=
  (Σ i, MonoF n a i) ⊕ (Σ i, Σ j : Fin (m i), MonoG n m d i j)

private abbrev Unk {N : ℕ} (n m : Fin N → ℕ) : Type :=
  Var n ⊕ (Σ i : Fin N, Fin (m i))

private def embIdx {N : ℕ} (n m : Fin N → ℕ) (a : Fin N → Fin N → ℕ)
    (d : (i : Fin N) → Fin (m i) → ℕ) (ha : ∀ i j, 0 < a i j) :
    Unk n m → Idx n m a d
  | Sum.inl ⟨i, k⟩ => Sum.inl ⟨i, linMono ha i k⟩
  | Sum.inr ⟨i, j⟩ => Sum.inr ⟨i, j, constMono i j⟩

private lemma linMono_injective {N : ℕ} {n : Fin N → ℕ} {a : Fin N → Fin N → ℕ}
    (ha : ∀ i j, 0 < a i j) (i : Fin N) :
    Function.Injective (linMono (n := n) ha i) := by
  intro k₁ k₂ h
  have hv := congrArg (fun α : MonoF n a i => (α.1 ⟨i, k₁⟩ : ℕ)) h
  dsimp [linMono] at hv
  simp only [↓reduceIte] at hv
  by_cases hk : (⟨i, k₁⟩ : Var n) = ⟨i, k₂⟩
  · cases hk
    rfl
  · simp [hk] at hv

private lemma embIdx_injective' {N : ℕ} (n m : Fin N → ℕ) (a : Fin N → Fin N → ℕ)
    (d : (i : Fin N) → Fin (m i) → ℕ) (ha : ∀ i j, 0 < a i j) :
    Function.Injective (embIdx n m a d ha) := by
  intro u₁ u₂ h
  cases u₁ with
  | inl v₁ =>
    cases u₂ with
    | inl v₂ =>
      rcases v₁ with ⟨i₁, k₁⟩
      rcases v₂ with ⟨i₂, k₂⟩
      dsimp only [embIdx] at h
      have hsig : (⟨i₁, linMono ha i₁ k₁⟩ : Σ i, MonoF n a i) = ⟨i₂, linMono ha i₂ k₂⟩ :=
        Sum.inl.inj h
      have hi : i₁ = i₂ := congrArg Sigma.fst hsig
      subst hi
      have hα : linMono ha i₁ k₁ = linMono ha i₁ k₂ := eq_of_heq (Sigma.mk.inj_iff.mp hsig).2
      have hk : k₁ = k₂ := linMono_injective ha i₁ hα
      subst hk
      rfl
    | inr _ =>
      dsimp only [embIdx] at h
      exact (Sum.inl_ne_inr h).elim
  | inr w₁ =>
    cases u₂ with
    | inl _ =>
      dsimp only [embIdx] at h
      exact (Sum.inr_ne_inl h).elim
    | inr w₂ =>
      rcases w₁ with ⟨i₁, j₁⟩
      rcases w₂ with ⟨i₂, j₂⟩
      dsimp only [embIdx] at h
      have hsig : (⟨i₁, j₁, constMono i₁ j₁⟩ : Σ i, Σ j : Fin (m i), MonoG n m d i j) =
          ⟨i₂, j₂, constMono i₂ j₂⟩ := Sum.inr.inj h
      have hi : i₁ = i₂ := congrArg Sigma.fst hsig
      subst hi
      have hsig2 : (⟨j₁, constMono i₁ j₁⟩ : Σ j : Fin (m i₁), MonoG n m d i₁ j) =
          ⟨j₂, constMono i₁ j₂⟩ := eq_of_heq (Sigma.mk.inj_iff.mp hsig).2
      have hj : j₁ = j₂ := congrArg Sigma.fst hsig2
      subst hj
      rfl

private abbrev RestIdx {N : ℕ} (n m : Fin N → ℕ) (a : Fin N → Fin N → ℕ)
    (d : (i : Fin N) → Fin (m i) → ℕ) (ha : ∀ i j, 0 < a i j) : Type :=
  {t : Idx n m a d // t ∉ Set.range (embIdx n m a d ha)}

private noncomputable def fRest {N : ℕ} (n m : Fin N → ℕ) (a : Fin N → Fin N → ℕ)
    (d : (i : Fin N) → Fin (m i) → ℕ) (ha : ∀ i j, 0 < a i j) (i : Fin N) :
    MvPolynomial (Var n) (MvPolynomial (RestIdx n m a d ha) ℝ) := by
  classical
  exact ∑ α : MonoF n a i,
    if h : (Sum.inl ⟨i, α⟩ : Idx n m a d) ∈ Set.range (embIdx n m a d ha) then 0
    else MvPolynomial.monomial
      (Finsupp.equivFunOnFinite.symm fun v => (α.1 v : ℕ))
      (MvPolynomial.X ⟨Sum.inl ⟨i, α⟩, h⟩)

private noncomputable def gRest {N : ℕ} (n m : Fin N → ℕ) (a : Fin N → Fin N → ℕ)
    (d : (i : Fin N) → Fin (m i) → ℕ) (ha : ∀ i j, 0 < a i j) (i : Fin N) (j : Fin (m i)) :
    MvPolynomial (Fin (n i)) (MvPolynomial (RestIdx n m a d ha) ℝ) := by
  classical
  exact ∑ β : MonoG n m d i j,
    if h : (Sum.inr ⟨i, j, β⟩ : Idx n m a d) ∈ Set.range (embIdx n m a d ha) then 0
    else MvPolynomial.monomial
      (Finsupp.equivFunOnFinite.symm fun k => (β.1 k : ℕ))
      (MvPolynomial.X ⟨Sum.inr ⟨i, j, β⟩, h⟩)

private noncomputable def kktMap {N : ℕ} (n m : Fin N → ℕ) (a : Fin N → Fin N → ℕ)
    (d : (i : Fin N) → Fin (m i) → ℕ) (ha : ∀ i j, 0 < a i j) :
    Unk n m → MvPolynomial (Unk n m) (MvPolynomial (RestIdx n m a d ha) ℝ)
  | Sum.inl ⟨i, k⟩ =>
    (∑ j : Fin (m i),
      MvPolynomial.X (Sum.inr ⟨i, j⟩) *
        MvPolynomial.rename (fun k' => Sum.inl ⟨i, k'⟩)
          (MvPolynomial.pderiv k (gRest n m a d ha i j))) -
      MvPolynomial.rename Sum.inl (MvPolynomial.pderiv ⟨i, k⟩ (fRest n m a d ha i))
  | Sum.inr ⟨i, j⟩ =>
    - MvPolynomial.rename (fun k' => Sum.inl ⟨i, k'⟩) (gRest n m a d ha i j)

private lemma mem_range_embIdx_inr {N : ℕ} (n m : Fin N → ℕ) (a : Fin N → Fin N → ℕ)
    (d : (i : Fin N) → Fin (m i) → ℕ) (ha : ∀ i j, 0 < a i j)
    (i : Fin N) (j : Fin (m i)) (β : MonoG n m d i j) :
    ((Sum.inr ⟨i, j, β⟩ : Idx n m a d) ∈ Set.range (embIdx n m a d ha)) ↔
      β = constMono i j := by
  constructor
  · rintro ⟨u, hu⟩
    cases u with
    | inl v =>
      rcases v with ⟨i', k'⟩
      dsimp only [embIdx] at hu
      exact (Sum.inl_ne_inr hu).elim
    | inr w =>
      rcases w with ⟨i', j'⟩
      dsimp only [embIdx] at hu
      have hsig : (⟨i', j', constMono i' j'⟩ : Σ i, Σ j : Fin (m i), MonoG n m d i j) =
          ⟨i, j, β⟩ := Sum.inr.inj hu
      have hi : i' = i := congrArg Sigma.fst hsig
      subst hi
      have hsig2 : (⟨j', constMono i' j'⟩ : Σ j : Fin (m i'), MonoG n m d i' j) =
          ⟨j, β⟩ := eq_of_heq (Sigma.mk.inj_iff.mp hsig).2
      have hj : j' = j := congrArg Sigma.fst hsig2
      subst hj
      exact (eq_of_heq (Sigma.mk.inj_iff.mp hsig2).2).symm
  · rintro rfl
    exact ⟨Sum.inr ⟨i, j⟩, rfl⟩

private lemma mem_range_embIdx_inl {N : ℕ} (n m : Fin N → ℕ) (a : Fin N → Fin N → ℕ)
    (d : (i : Fin N) → Fin (m i) → ℕ) (ha : ∀ i j, 0 < a i j)
    (i : Fin N) (α : MonoF n a i) :
    ((Sum.inl ⟨i, α⟩ : Idx n m a d) ∈ Set.range (embIdx n m a d ha)) ↔
      ∃ k' : Fin (n i), α = linMono ha i k' := by
  constructor
  · rintro ⟨u, hu⟩
    cases u with
    | inr w =>
      rcases w with ⟨i', j'⟩
      dsimp only [embIdx] at hu
      exact (Sum.inr_ne_inl hu).elim
    | inl v =>
      rcases v with ⟨i', k'⟩
      dsimp only [embIdx] at hu
      have hsig : (⟨i', linMono ha i' k'⟩ : Σ i, MonoF n a i) = ⟨i, α⟩ := Sum.inl.inj hu
      have hi : i' = i := congrArg Sigma.fst hsig
      subst hi
      exact ⟨k', (eq_of_heq (Sigma.mk.inj_iff.mp hsig).2).symm⟩
  · rintro ⟨k', rfl⟩
    exact ⟨Sum.inl ⟨i, k'⟩, rfl⟩

private lemma polyG_decomp {N : ℕ} (n m : Fin N → ℕ) (a : Fin N → Fin N → ℕ)
    (d : (i : Fin N) → Fin (m i) → ℕ) (ha : ∀ i j, 0 < a i j)
    (c : Coef n m a d) (i : Fin N) (j : Fin (m i)) :
    polyG c i j = MvPolynomial.C (c (embIdx n m a d ha (Sum.inr ⟨i, j⟩))) +
      MvPolynomial.map (MvPolynomial.eval (fun t : RestIdx n m a d ha => c t.1))
        (gRest n m a d ha i j) := by
  classical
  unfold polyG gRest
  rw [map_sum]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (constMono i j))]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [constMono_exp, MvPolynomial.monomial_zero']
    rfl
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (constMono i j))]
    have hconst_mem :
        (Sum.inr ⟨i, j, constMono i j⟩ : Idx n m a d) ∈ Set.range (embIdx n m a d ha) :=
      ⟨Sum.inr ⟨i, j⟩, rfl⟩
    simp only [hconst_mem, ↓reduceDIte, map_zero, zero_add]
    refine Finset.sum_congr rfl fun β hβ => ?_
    have hne : β ≠ constMono i j := (Finset.mem_erase.mp hβ).1
    have hnotmem :
        (Sum.inr ⟨i, j, β⟩ : Idx n m a d) ∉ Set.range (embIdx n m a d ha) := by
      rwa [mem_range_embIdx_inr]
    simp only [hnotmem, ↓reduceDIte, MvPolynomial.map_monomial, MvPolynomial.eval_X]

private lemma pderiv_polyG_eq {N : ℕ} (n m : Fin N → ℕ) (a : Fin N → Fin N → ℕ)
    (d : (i : Fin N) → Fin (m i) → ℕ) (ha : ∀ i j, 0 < a i j)
    (c : Coef n m a d) (i : Fin N) (j : Fin (m i)) (k : Fin (n i)) :
    MvPolynomial.pderiv k (polyG c i j) =
      MvPolynomial.map (MvPolynomial.eval (fun t : RestIdx n m a d ha => c t.1))
        (MvPolynomial.pderiv k (gRest n m a d ha i j)) := by
  rw [polyG_decomp n m a d ha c i j, map_add, MvPolynomial.pderiv_C, zero_add, MvPolynomial.pderiv_map]

private lemma pderiv_polyF_decomp {N : ℕ} (n m : Fin N → ℕ) (a : Fin N → Fin N → ℕ)
    (d : (i : Fin N) → Fin (m i) → ℕ) (ha : ∀ i j, 0 < a i j)
    (c : Coef n m a d) (i : Fin N) (k : Fin (n i)) :
    MvPolynomial.pderiv ⟨i, k⟩ (polyF c i) =
      MvPolynomial.C (c (embIdx n m a d ha (Sum.inl ⟨i, k⟩))) +
        MvPolynomial.map (MvPolynomial.eval (fun t : RestIdx n m a d ha => c t.1))
          (MvPolynomial.pderiv ⟨i, k⟩ (fRest n m a d ha i)) := by
  classical
  unfold polyF fRest
  rw [← MvPolynomial.pderiv_map, map_sum, map_sum, map_sum]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (linMono ha i k))]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [linMono_exp, MvPolynomial.pderiv_monomial_single]
    simp [embIdx]
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (linMono ha i k))]
    have hlin_mem :
        (Sum.inl ⟨i, linMono ha i k⟩ : Idx n m a d) ∈ Set.range (embIdx n m a d ha) :=
      ⟨Sum.inl ⟨i, k⟩, rfl⟩
    simp only [hlin_mem, ↓reduceDIte, map_zero, zero_add]
    refine Finset.sum_congr rfl fun α hα => ?_
    have hne : α ≠ linMono ha i k := (Finset.mem_erase.mp hα).1
    by_cases hmem : (Sum.inl ⟨i, α⟩ : Idx n m a d) ∈ Set.range (embIdx n m a d ha)
    · simp only [hmem, ↓reduceDIte, map_zero]
      rcases (mem_range_embIdx_inl n m a d ha i α).mp hmem with ⟨k', rfl⟩
      have hk' : k' ≠ k := fun h => hne (by rw [h])
      rw [linMono_exp, MvPolynomial.pderiv_monomial]
      have hzero : (Finsupp.single (⟨i, k'⟩ : Var n) 1) ⟨i, k⟩ = 0 := by
        apply Finsupp.single_eq_of_ne
        intro heq
        cases heq
        exact hk' rfl
      simp [hzero]
    · simp only [hmem, ↓reduceDIte, MvPolynomial.map_monomial, MvPolynomial.eval_X]

end NashPolyTheoremA1Aux

open NashPolyTheoremA1Aux in
theorem solution {N : ℕ} (n m : Fin N → ℕ) (a : Fin N → Fin N → ℕ)
    (d : (i : Fin N) → Fin (m i) → ℕ) (ha : ∀ i j, 0 < a i j) (hd : ∀ i j, 0 < d i j) :
    ∀ᵐ c ∂(volume : Measure (Coef n m a d)), (A1Sol (polyF c) (polyG c)).Finite := by
  classical
  let _ := hd
  let eIdx : Unk n m ⊕ RestIdx n m a d ha ≃ Idx n m a d :=
    (Equiv.sumCongr (Equiv.ofInjective _ (embIdx_injective' n m a d ha))
      (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range (embIdx n m a d ha)))
  rcases exists_poly_finiteness_certificate (kktMap n m a d ha) with ⟨P, hP_ne, hP_fin⟩
  let PIdx : MvPolynomial (Idx n m a d) ℝ := MvPolynomial.renameEquiv ℝ eIdx P
  have hPIdx_ne : PIdx ≠ 0 := by
    intro h0
    exact hP_ne ((MvPolynomial.renameEquiv ℝ eIdx).injective (by simp [PIdx, h0]))
  have hvol0 : volume {c : Coef n m a d | MvPolynomial.eval c PIdx = 0} = 0 :=
    volume_mvpoly_eval_eq_zero PIdx hPIdx_ne
  have hae : ∀ᵐ c ∂(volume : Measure (Coef n m a d)), MvPolynomial.eval c PIdx ≠ 0 := by
    rw [ae_iff]
    simpa using hvol0
  filter_upwards [hae] with c hc
  let y : Unk n m → ℝ := fun u => c (embIdx n m a d ha u)
  let r : RestIdx n m a d ha → ℝ := fun t => c t.1
  have hyr : MvPolynomial.eval (Sum.elim y r) P ≠ 0 := by
    have hcomp : c ∘ eIdx = Sum.elim y r := by
      ext u
      cases u <;> rfl
    have h1 : MvPolynomial.eval c PIdx = MvPolynomial.eval (Sum.elim y r) P := by
      simp only [PIdx, MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename, hcomp]
    rwa [← h1]
  have hZfin := hP_fin y r hyr
  let toZ : ((Var n → ℂ) × ((Σ i, Fin (m i)) → ℂ)) → (Unk n m → ℂ) := fun p => Sum.elim p.1 p.2
  have htoZ_inj : Function.Injective toZ := by
    intro p₁ p₂ h
    ext v
    · exact congrFun h (Sum.inl v)
    · exact congrFun h (Sum.inr v)
  have hmaps : Set.MapsTo toZ (A1Sol (polyF c) (polyG c))
      {z : Unk n m → ℂ | ∀ u : Unk n m,
        MvPolynomial.eval₂ ((algebraMap ℝ ℂ).comp (MvPolynomial.eval r)) z
          (kktMap n m a d ha u) = (y u : ℂ)} := by
    intro p hp u
    have heval₂_map : ∀ {σ : Type} (w : σ → ℂ)
        (q : MvPolynomial σ (MvPolynomial (RestIdx n m a d ha) ℝ)),
        MvPolynomial.eval₂ ((algebraMap ℝ ℂ).comp (MvPolynomial.eval r)) w q =
          MvPolynomial.aeval w (MvPolynomial.map (MvPolynomial.eval r) q) := by
      intro σ w q
      rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    cases u with
    | inl v =>
      rcases v with ⟨i, k⟩
      have hp1 := (hp i).1 k
      simp only [kktMap, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_X, MvPolynomial.eval₂_rename]
      have hterm1 : ∀ j : Fin (m i),
          MvPolynomial.eval₂ ((algebraMap ℝ ℂ).comp (MvPolynomial.eval r))
            (toZ p ∘ fun k' => Sum.inl ⟨i, k'⟩)
            (MvPolynomial.pderiv k (gRest n m a d ha i j)) =
          MvPolynomial.aeval (fun k' => p.1 ⟨i, k'⟩) (MvPolynomial.pderiv k (polyG c i j)) := by
        intro j
        rw [pderiv_polyG_eq n m a d ha c i j k, ← heval₂_map]
        rfl
      have hterm2 :
          MvPolynomial.eval₂ ((algebraMap ℝ ℂ).comp (MvPolynomial.eval r))
            (toZ p ∘ Sum.inl)
            (MvPolynomial.pderiv ⟨i, k⟩ (fRest n m a d ha i)) =
          MvPolynomial.aeval p.1 (MvPolynomial.map (MvPolynomial.eval r)
            (MvPolynomial.pderiv ⟨i, k⟩ (fRest n m a d ha i))) := by
        rw [← heval₂_map]
        rfl
      simp only [hterm1, hterm2]
      have htoZ_inr : ∀ j : Fin (m i), toZ p (Sum.inr ⟨i, j⟩) = p.2 ⟨i, j⟩ := fun _ => rfl
      simp only [htoZ_inr]
      rw [hp1, pderiv_polyF_decomp n m a d ha c i k, map_add, MvPolynomial.aeval_C]
      simp [y, r]
    | inr w =>
      rcases w with ⟨i, j⟩
      have hp2 := (hp i).2 j
      simp only [kktMap, MvPolynomial.eval₂_neg, MvPolynomial.eval₂_rename]
      have hterm :
          MvPolynomial.eval₂ ((algebraMap ℝ ℂ).comp (MvPolynomial.eval r))
            (toZ p ∘ fun k' => Sum.inl ⟨i, k'⟩) (gRest n m a d ha i j) =
          MvPolynomial.aeval (fun k' => p.1 ⟨i, k'⟩)
            (MvPolynomial.map (MvPolynomial.eval r) (gRest n m a d ha i j)) := by
        rw [← heval₂_map]
        rfl
      rw [hterm]
      rw [polyG_decomp n m a d ha c i j, map_add, MvPolynomial.aeval_C] at hp2
      change ((y (Sum.inr ⟨i, j⟩) : ℝ) : ℂ) +
        MvPolynomial.aeval (fun k' => p.1 ⟨i, k'⟩)
          (MvPolynomial.map (MvPolynomial.eval r) (gRest n m a d ha i j)) = 0 at hp2
      linear_combination -hp2
  exact Set.Finite.of_finite_image (hZfin.subset (Set.mapsTo_iff_image_subset.mp hmaps)) htoZ_inj.injOn
