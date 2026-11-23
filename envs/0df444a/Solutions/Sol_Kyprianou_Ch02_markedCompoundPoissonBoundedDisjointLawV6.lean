-- Prove2me | solution 1 for Kyprianou.Ch02.markedCompoundPoissonBoundedDisjointLawV6
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T12:35:49.302171+00:00
-- url     : https://prove2.me/submissions/20ec2878-4733-41c6-b55f-5425a7e83a00

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_exercise2_2_AllPartsCh02V6

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace MarkedCPBoundedHelpers

private def closedSimplex (n : ℕ) (t : ℝ≥0) : Set (Fin n → ℝ) :=
  {v : Fin n → ℝ | (∀ i, 0 ≤ v i ∧ v i ≤ (t : ℝ)) ∧ Monotone v}

private def diagSet (n : ℕ) : Set (Fin n → ℝ) :=
  ⋃ (i : Fin n) (j : Fin n) (_ : i ≠ j), {v : Fin n → ℝ | v i = v j}

private lemma volume_eq_coord_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    volume {v : Fin n → ℝ | v i = v j} = 0 := by
  let S : Submodule ℝ (Fin n → ℝ) :=
    { carrier := {v : Fin n → ℝ | v i = v j}
      zero_mem' := rfl
      add_mem' := fun {a b} ha hb => show a i + b i = a j + b j by rw [ha, hb]
      smul_mem' := fun r {a} ha => show r * a i = r * a j by rw [ha] }
  have hSne : S ≠ ⊤ := by
    intro htop
    let e : Fin n → ℝ := fun k => if k = i then 1 else 0
    have hmem : e ∈ S := by rw [htop]; trivial
    have h1 : e i = e j := hmem
    simp [e, hij.symm] at h1
  exact Measure.addHaar_submodule volume S hSne

private lemma volume_diagSet_zero (n : ℕ) : volume (diagSet n) = 0 := by
  unfold diagSet
  exact measure_iUnion_null fun i => measure_iUnion_null fun j =>
    measure_iUnion_null fun hij => volume_eq_coord_zero hij

private lemma poissonMeasure_singleton_eq (r : ℝ≥0) (k : ℕ) :
    ProbabilityTheory.poissonMeasure r {k} =
      ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (Nat.factorial k : ℝ)) := by
  rw [← poissonMeasure_real_singleton r k, Measure.real,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

private lemma aemeasurable_N_of_law
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℝ≥0) (N : ℝ≥0 → Ω → ℕ)
    (hNlaw : ∀ t, P.map (N t) = ProbabilityTheory.poissonMeasure (rate * t))
    (t : ℝ≥0) : AEMeasurable (N t) P := by
  by_contra hnot
  have h0 : P.map (N t) = 0 := Measure.map_of_not_aemeasurable hnot
  have h1 : (ProbabilityTheory.poissonMeasure (rate * t)) Set.univ = 1 := measure_univ
  rw [← hNlaw t, h0] at h1
  simp at h1

private lemma N_zero_eq_zero
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (N : ℝ≥0 → Ω → ℕ)
    (hNlevy : ProbabilityTheory.IsLevyProcess (fun t ω => (N t ω : ℝ)) P)
    (ω : Ω) : N 0 ω = 0 :=
  Nat.cast_eq_zero.mp (congrFun hNlevy.start_zero ω)

private lemma measurable_marked_mu_eval
    {Ω : Type} [MeasurableSpace Ω]
    (T : ℕ → Ω → ℝ≥0) (ξ : ℕ → Ω → ℝ)
    (hTmeas : ∀ n : ℕ, 0 < n → Measurable (T n))
    (hξmeas : ∀ k : ℕ, Measurable (ξ k))
    {B : Set (ℝ × ℝ)} (hB : MeasurableSet B) :
    Measurable (fun ω =>
      (Measure.sum (fun n : ℕ => Measure.dirac ((T (n + 1) ω : ℝ), ξ (n + 1) ω))) B) := by
  have hfun : (fun ω => (Measure.sum (fun n : ℕ => Measure.dirac ((T (n + 1) ω : ℝ), ξ (n + 1) ω))) B) =
      fun ω => ∑' n : ℕ, B.indicator (fun _ => (1 : ℝ≥0∞)) ((T (n + 1) ω : ℝ), ξ (n + 1) ω) := by
    ext ω
    rw [Measure.sum_apply _ hB]
    congr 1; ext n
    rw [Measure.dirac_apply' _ hB]; rfl
  rw [hfun]
  refine Measurable.tsum fun n => ?_
  exact (measurable_const.indicator hB).comp
    ((NNReal.continuous_coe.measurable.comp (hTmeas (n + 1) (Nat.succ_pos n))).prodMk (hξmeas (n + 1)))

private lemma T_ae_eq_mN_measurable
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (N : ℝ≥0 → Ω → ℕ) (T : ℕ → Ω → ℝ≥0)
    (harrival : ∀ᵐ ω ∂P, ∀ (n : ℕ), 0 < n → ∀ (s : ℝ≥0), (n ≤ N s ω ↔ T n ω ≤ s))
    (k : ℕ) (hk : 0 < k) :
    ∃ Ttilde : Ω → ℝ,
      Measurable[⨆ s : ℝ≥0, MeasurableSpace.comap (N s) inferInstance] Ttilde ∧
      (fun ω => (T k ω : ℝ)) =ᵐ[P] Ttilde := by
  let mN : MeasurableSpace Ω := ⨆ s : ℝ≥0, MeasurableSpace.comap (N s) inferInstance
  let rat : ℕ × ℕ → ℝ≥0 := fun q => (q.1 : ℝ≥0) / ((q.2 : ℝ≥0) + 1)
  let Tinf : Ω → ℝ≥0∞ := fun ω =>
    ⨅ q : ℕ × ℕ, if k ≤ N (rat q) ω then ((rat q : ℝ≥0) : ℝ≥0∞) else ⊤
  have hTinf_meas : Measurable[mN] Tinf := by
    refine Measurable.iInf fun q => ?_
    have hNr : Measurable[mN] (N (rat q)) :=
      Measurable.mono (comap_measurable (N (rat q))) (le_iSup (fun s => MeasurableSpace.comap (N s) inferInstance) (rat q)) le_rfl
    have hset : MeasurableSet[mN] {ω | k ≤ N (rat q) ω} :=
      hNr (MeasurableSet.of_discrete (s := {m : ℕ | k ≤ m}))
    exact Measurable.ite hset measurable_const measurable_const
  refine ⟨fun ω => (Tinf ω).toReal, ENNReal.measurable_toReal.comp hTinf_meas, ?_⟩
  filter_upwards [harrival] with ω ha
  have hTinf_eq : Tinf ω = ((T k ω : ℝ≥0) : ℝ≥0∞) := by
    apply le_antisymm
    · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
      have hrat_ex : ∃ q : ℚ, (T k ω : ℝ) < (q : ℝ) ∧ (q : ℝ) < (T k ω : ℝ) + (ε : ℝ) :=
        exists_rat_btwn (lt_add_of_pos_right _ (by exact_mod_cast hε))
      obtain ⟨q, hq1, hq2⟩ := hrat_ex
      have hq_nn : (0 : ℚ) ≤ q := by
        have : (0 : ℝ) ≤ (q : ℝ) := le_trans (T k ω).coe_nonneg (le_of_lt hq1)
        exact_mod_cast this
      let p : ℕ × ℕ := (q.num.toNat, q.den - 1)
      have hrat_p : (rat p : ℝ) = (q : ℝ) := by
        dsimp [rat, p]
        have hden : 0 < q.den := q.pos
        have hnum : (q.num.toNat : ℝ) = (q.num : ℝ) := by
          have : 0 ≤ q.num := Rat.num_nonneg.mpr hq_nn
          exact_mod_cast Int.toNat_of_nonneg this
        have hden_eq : ((q.den - 1 : ℕ) : ℝ) + 1 = (q.den : ℝ) := by
          exact_mod_cast Nat.sub_add_cancel hden
        simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
        rw [hnum, hden_eq, Rat.cast_def]
      have hle_p : T k ω ≤ rat p := by
        change (T k ω : ℝ) ≤ (rat p : ℝ)
        rw [hrat_p]; exact le_of_lt hq1
      have hkN : k ≤ N (rat p) ω := (ha k hk (rat p)).mpr hle_p
      calc Tinf ω ≤ if k ≤ N (rat p) ω then ((rat p : ℝ≥0) : ℝ≥0∞) else ⊤ := iInf_le _ p
        _ = ((rat p : ℝ≥0) : ℝ≥0∞) := if_pos hkN
        _ ≤ ((T k ω : ℝ≥0) : ℝ≥0∞) + (ε : ℝ≥0∞) := by
            rw [← ENNReal.coe_add, ENNReal.coe_le_coe]
            change (rat p : ℝ) ≤ (T k ω : ℝ) + (ε : ℝ)
            rw [hrat_p]; exact le_of_lt hq2
    · refine le_iInf fun q => ?_
      split_ifs with hq
      · exact ENNReal.coe_le_coe.mpr ((ha k hk (rat q)).mp hq)
      · exact le_top
  rw [hTinf_eq, ENNReal.coe_toReal]

private lemma restrict_map_pair_eq_prod
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℝ≥0) (N : ℝ≥0 → Ω → ℕ) (T : ℕ → Ω → ℝ≥0) (ξ : ℕ → Ω → ℝ)
    (hTmeas : ∀ n : ℕ, 0 < n → Measurable (T n))
    (hξmeas : ∀ k : ℕ, Measurable (ξ k))
    (hNlaw : ∀ t, P.map (N t) = ProbabilityTheory.poissonMeasure (rate * t))
    (harrival : ∀ᵐ ω ∂P, ∀ (n : ℕ), 0 < n → ∀ (s : ℝ≥0), (n ≤ N s ω ↔ T n ω ≤ s))
    (hcross : ProbabilityTheory.Indep
      (⨆ k : ℕ, MeasurableSpace.comap (ξ k) inferInstance)
      (⨆ s : ℝ≥0, MeasurableSpace.comap (N s) inferInstance) P)
    (t : ℝ≥0) (n : ℕ) :
    ((P.restrict {ω | N t ω = n}).map
        (fun ω => (fun j : Fin n => (T (j.val + 1) ω : ℝ), fun j : Fin n => ξ (j.val + 1) ω))) =
      ((P.restrict {ω | N t ω = n}).map (fun ω => fun j : Fin n => (T (j.val + 1) ω : ℝ))).prod
        (P.map (fun ω => fun j : Fin n => ξ (j.val + 1) ω)) := by
  let Tvec : Ω → (Fin n → ℝ) := fun ω j => (T (j.val + 1) ω : ℝ)
  let ξvec : Ω → (Fin n → ℝ) := fun ω j => ξ (j.val + 1) ω
  have hTvec_meas : Measurable Tvec :=
    measurable_pi_lambda _ fun j => NNReal.continuous_coe.measurable.comp (hTmeas (j.val + 1) (Nat.succ_pos _))
  have hξvec_meas : Measurable ξvec :=
    measurable_pi_lambda _ fun j => hξmeas (j.val + 1)
  have hξvec_mξ : Measurable[⨆ k : ℕ, MeasurableSpace.comap (ξ k) inferInstance] ξvec :=
    @measurable_pi_lambda Ω (Fin n) (fun _ => ℝ) (⨆ k : ℕ, MeasurableSpace.comap (ξ k) inferInstance) _ _ fun j =>
      Measurable.mono (comap_measurable (ξ (j.val + 1)))
        (le_iSup (fun k => MeasurableSpace.comap (ξ k) inferInstance) (j.val + 1)) le_rfl
  have hex : ∀ j : Fin n, ∃ g : Ω → ℝ,
      Measurable[⨆ s : ℝ≥0, MeasurableSpace.comap (N s) inferInstance] g ∧
      (fun ω => (T (j.val + 1) ω : ℝ)) =ᵐ[P] g :=
    fun j => T_ae_eq_mN_measurable P N T harrival (j.val + 1) (Nat.succ_pos _)
  choose g hg_mN hg_ae using hex
  let gvec : Ω → (Fin n → ℝ) := fun ω j => g j ω
  have hgvec_mN : Measurable[⨆ s : ℝ≥0, MeasurableSpace.comap (N s) inferInstance] gvec :=
    @measurable_pi_lambda Ω (Fin n) (fun _ => ℝ) (⨆ s : ℝ≥0, MeasurableSpace.comap (N s) inferInstance) _ _ hg_mN
  have hgvec_ae : Tvec =ᵐ[P] gvec := by
    have hall : ∀ᵐ ω ∂P, ∀ j : Fin n, (T (j.val + 1) ω : ℝ) = g j ω := ae_all_iff.mpr hg_ae
    filter_upwards [hall] with ω hω
    ext j; exact hω j
  have hNt_mN : Measurable[⨆ s : ℝ≥0, MeasurableSpace.comap (N s) inferInstance] (N t) :=
    Measurable.mono (comap_measurable (N t))
      (le_iSup (fun s => MeasurableSpace.comap (N s) inferInstance) t) le_rfl
  symm
  refine Measure.prod_eq fun B C hB hC => ?_
  rw [Measure.map_apply (hTvec_meas.prodMk hξvec_meas) (hB.prod hC),
    Measure.restrict_apply ((hTvec_meas.prodMk hξvec_meas) (hB.prod hC)),
    Measure.map_apply hTvec_meas hB, Measure.restrict_apply (hTvec_meas hB),
    Measure.map_apply hξvec_meas hC]
  have hset1 : (((fun ω => (Tvec ω, ξvec ω)) ⁻¹' (B ×ˢ C) ∩ {ω | N t ω = n}) : Set Ω) =ᵐ[P]
      ((ξvec ⁻¹' C) ∩ (gvec ⁻¹' B ∩ (N t) ⁻¹' {n}) : Set Ω) := by
    filter_upwards [hgvec_ae] with ω hω
    change (ω ∈ (fun ω => (Tvec ω, ξvec ω)) ⁻¹' (B ×ˢ C) ∩ {ω | N t ω = n}) =
      (ω ∈ (ξvec ⁻¹' C) ∩ (gvec ⁻¹' B ∩ (N t) ⁻¹' {n}))
    apply propext
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
      Set.mem_setOf_eq, hω]
    tauto
  have hset2 : ((Tvec ⁻¹' B ∩ {ω | N t ω = n}) : Set Ω) =ᵐ[P]
      ((gvec ⁻¹' B ∩ (N t) ⁻¹' {n}) : Set Ω) := by
    filter_upwards [hgvec_ae] with ω hω
    change (ω ∈ Tvec ⁻¹' B ∩ {ω | N t ω = n}) = (ω ∈ gvec ⁻¹' B ∩ (N t) ⁻¹' {n})
    apply propext
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, hω]
  rw [measure_congr hset1, measure_congr hset2]
  have hm1 : MeasurableSet[⨆ k : ℕ, MeasurableSpace.comap (ξ k) inferInstance] (ξvec ⁻¹' C) := hξvec_mξ hC
  have hm2 : MeasurableSet[⨆ s : ℝ≥0, MeasurableSpace.comap (N s) inferInstance] (gvec ⁻¹' B ∩ (N t) ⁻¹' {n}) :=
    (hgvec_mN hB).inter (hNt_mN (measurableSet_singleton n))
  rw [(Indep_iff _ _ P).mp hcross _ _ hm1 hm2, mul_comm]

private lemma measurePreserving_zipEquiv
    (n : ℕ) (ν₁ ν₂ : Measure ℝ) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
    MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm
      ((Measure.pi (fun _ : Fin n => ν₁)).prod (Measure.pi (fun _ : Fin n => ν₂)))
      (Measure.pi (fun _ : Fin n => ν₁.prod ν₂)) := by
  let e := (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm
  refine ⟨e.measurable, ?_⟩
  symm
  let C : Set (Set (ℝ × ℝ)) := Set.image2 (· ×ˢ ·) {s : Set ℝ | MeasurableSet s} {u : Set ℝ | MeasurableSet u}
  have hgen : MeasurableSpace.generateFrom C = (inferInstance : MeasurableSpace (ℝ × ℝ)) :=
    @generateFrom_prod ℝ ℝ _ _
  have hpi : IsPiSystem C := by
    rintro _ ⟨s1, hs1, u1, hu1, rfl⟩ _ ⟨s2, hs2, u2, hu2, rfl⟩ _
    exact ⟨s1 ∩ s2, Set.mem_setOf_eq.mpr ((Set.mem_setOf_eq.mp hs1).inter (Set.mem_setOf_eq.mp hs2)),
      u1 ∩ u2, Set.mem_setOf_eq.mpr ((Set.mem_setOf_eq.mp hu1).inter (Set.mem_setOf_eq.mp hu2)),
      Set.prod_inter_prod.symm⟩
  have hspan : ∀ j : Fin n, (ν₁.prod ν₂).FiniteSpanningSetsIn C := fun _ =>
    { set := fun _ => Set.univ ×ˢ Set.univ
      set_mem := fun _ => ⟨Set.univ, Set.mem_setOf_eq.mpr MeasurableSet.univ,
        Set.univ, Set.mem_setOf_eq.mpr MeasurableSet.univ, rfl⟩
      finite := fun _ => by rw [Measure.prod_prod]; simp
      spanning := by simp [Set.iUnion_const] }
  refine Measure.pi_eq_generateFrom (fun _ => hgen) (fun _ => hpi) hspan fun S hS => ?_
  have hrect : ∀ j : Fin n, ∃ s u : Set ℝ, MeasurableSet s ∧ MeasurableSet u ∧ S j = s ×ˢ u := by
    intro j
    rcases hS j with ⟨s, hs, u, hu, hsu⟩
    exact ⟨s, u, hs, hu, hsu.symm⟩
  choose s u hs hu hSu using hrect
  have hSmeas : MeasurableSet (Set.univ.pi S) :=
    MeasurableSet.univ_pi fun j => by rw [hSu j]; exact (hs j).prod (hu j)
  rw [Measure.map_apply e.measurable hSmeas]
  have hpre : e ⁻¹' Set.univ.pi S = (Set.univ.pi s) ×ˢ (Set.univ.pi u) := by
    ext ⟨v, y⟩
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod, hSu]
    constructor
    · intro h; exact ⟨fun j => (h j).1, fun j => (h j).2⟩
    · rintro ⟨h1, h2⟩ j; exact ⟨h1 j, h2 j⟩
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hSu j, Measure.prod_prod]

private lemma symm_simplex_prod_eq
    (n : ℕ) (t : ℝ≥0) (F : Measure ℝ) [IsProbabilityMeasure F]
    (E : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hEmeas : MeasurableSet E)
    (hEsymm : ∀ (σ : Equiv.Perm (Fin n)) (v y : Fin n → ℝ), (v ∘ σ, y ∘ σ) ∈ E ↔ (v, y) ∈ E) :
    (Nat.factorial n : ℝ≥0∞) *
        ((volume.restrict (closedSimplex n t)).prod (Measure.pi (fun _ : Fin n => F))) E =
      ((volume.restrict (Set.univ.pi (fun _ : Fin n => Set.Icc (0 : ℝ) (t : ℝ)))).prod
        (Measure.pi (fun _ : Fin n => F))) E := by
  let Q : Set (Fin n → ℝ) := Set.univ.pi (fun _ : Fin n => Set.Icc (0 : ℝ) (t : ℝ))
  let Δs : Set (Fin n → ℝ) := {v : Fin n → ℝ | (∀ i, 0 ≤ v i ∧ v i ≤ (t : ℝ)) ∧ StrictMono v}
  have hQmeas : MeasurableSet Q := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hΔs_meas : MeasurableSet Δs := by
    have h1 : MeasurableSet {v : Fin n → ℝ | ∀ i, 0 ≤ v i ∧ v i ≤ (t : ℝ)} := by
      have : {v : Fin n → ℝ | ∀ i, 0 ≤ v i ∧ v i ≤ (t : ℝ)} = Q := by
        ext v; simp only [Set.mem_setOf_eq, Q, Set.mem_univ_pi, Set.mem_Icc]
      rw [this]; exact hQmeas
    have h2 : MeasurableSet {v : Fin n → ℝ | StrictMono v} := by
      have : {v : Fin n → ℝ | StrictMono v} =
          ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j), {v : Fin n → ℝ | v i < v j} := by
        ext v; simp [StrictMono]
      rw [this]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
        MeasurableSet.iInter fun _ => measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)
    exact h1.inter h2
  have hdiag_meas : MeasurableSet (diagSet n) := by
    unfold diagSet
    exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
      MeasurableSet.iUnion fun _ => measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)
  let μF : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => F)
  -- Closed simplex and strict simplex agree up to diagSet n (volume 0)
  have hrest_eq : volume.restrict (closedSimplex n t) = volume.restrict Δs := by
    apply Measure.restrict_congr_set
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ (volume_diagSet_zero n)
      intro v ⟨⟨hbd, hmono⟩, hnot⟩
      by_contra hnd
      apply hnot
      refine ⟨hbd, fun i j hij => lt_of_le_of_ne (hmono (le_of_lt hij)) ?_⟩
      intro heq
      exact hnd (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨ne_of_lt hij, heq⟩⟩⟩)
    · have hsub : Δs \ closedSimplex n t = ∅ := by
        ext v; simp only [Set.mem_sdiff, Set.mem_empty_iff_false, iff_false, not_and, not_not]
        exact fun ⟨hbd, hsm⟩ => ⟨hbd, hsm.monotone⟩
      rw [hsub, measure_empty]
  -- Partition Q \ diagSet n into n! disjoint chambers (· ∘ σ) ⁻¹' Δs
  let chamber : Equiv.Perm (Fin n) → Set (Fin n → ℝ) := fun σ => (fun v : Fin n → ℝ => v ∘ σ) ⁻¹' Δs
  have hch_meas : ∀ σ, MeasurableSet (chamber σ) := fun σ =>
    hΔs_meas.preimage (measurable_pi_lambda _ fun i => measurable_pi_apply (σ i))
  have hch_disj : Pairwise (fun σ₁ σ₂ => Disjoint (chamber σ₁) (chamber σ₂)) := by
    intro σ₁ σ₂ hne
    rw [Set.disjoint_left]
    intro v h1 h2
    apply hne
    have hsm1 : StrictMono (v ∘ σ₁) := h1.2
    have hsm2 : StrictMono (v ∘ σ₂) := h2.2
    have hperm : (List.ofFn (v ∘ σ₁)).Perm (List.ofFn (v ∘ σ₂)) := by
      have hp : ∀ σ : Equiv.Perm (Fin n), (List.ofFn (v ∘ σ)).Perm (List.ofFn v) := fun σ => by
        have hfin : ((List.finRange n).map σ).Perm (List.finRange n) := by
          rw [List.perm_ext_iff_of_nodup ((List.nodup_finRange n).map σ.injective) (List.nodup_finRange n)]
          intro i; simp only [List.mem_map, List.mem_finRange, true_and, iff_true]
          exact ⟨σ.symm i, σ.apply_symm_apply i⟩
        simpa only [List.ofFn_eq_map, List.map_map] using hfin.map v
      exact (hp σ₁).trans (hp σ₂).symm
    have hpw1 : (List.ofFn (v ∘ σ₁)).Pairwise (· ≤ ·) :=
      List.pairwise_ofFn.mpr fun i j hij => le_of_lt (hsm1 hij)
    have hpw2 : (List.ofFn (v ∘ σ₂)).Pairwise (· ≤ ·) :=
      List.pairwise_ofFn.mpr fun i j hij => le_of_lt (hsm2 hij)
    have heqf : v ∘ σ₁ = v ∘ σ₂ :=
      List.ofFn_inj.mp (hperm.eq_of_pairwise (fun _ _ _ _ hab hba => le_antisymm hab hba) hpw1 hpw2)
    have hvinj : Function.Injective v := by
      intro a b hab
      have := hsm1.injective (show (v ∘ σ₁) (σ₁.symm a) = (v ∘ σ₁) (σ₁.symm b) by simpa using hab)
      exact σ₁.symm.injective this
    ext i; exact congrArg Fin.val (hvinj (congrFun heqf i))
  have hQ_ae_eq : (Q : Set (Fin n → ℝ)) =ᵐ[volume] ⋃ σ : Equiv.Perm (Fin n), chamber σ := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ (volume_diagSet_zero n)
      intro v ⟨hvQ, hnot⟩
      by_contra hnd
      apply hnot
      refine Set.mem_iUnion.mpr ⟨Tuple.sort v, ?_, ?_⟩
      · intro i; exact hvQ (Tuple.sort v i) (Set.mem_univ _)
      · intro i j hij
        refine lt_of_le_of_ne (Tuple.monotone_sort v (le_of_lt hij)) ?_
        intro heq
        exact hnd (Set.mem_iUnion.mpr ⟨Tuple.sort v i, Set.mem_iUnion.mpr ⟨Tuple.sort v j,
          Set.mem_iUnion.mpr ⟨fun h => ne_of_lt hij ((Tuple.sort v).injective h), heq⟩⟩⟩)
    · have hsub : (⋃ σ : Equiv.Perm (Fin n), chamber σ) \ Q = ∅ := by
        ext v; simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_empty_iff_false, iff_false, not_and, not_not]
        rintro ⟨σ, hσ⟩ i _
        have := hσ.1 (σ.symm i)
        simpa using this
      rw [hsub, measure_empty]
  -- Measure equality on each chamber by coordinate permutation invariance
  have hpiece : ∀ σ : Equiv.Perm (Fin n),
      (volume.prod μF) (E ∩ (chamber σ ×ˢ Set.univ)) = (volume.prod μF) (E ∩ (Δs ×ˢ Set.univ)) := by
    intro σ
    have hmp1 : MeasurePreserving (fun v : Fin n → ℝ => v ∘ σ) volume volume := by
      have h := measurePreserving_piCongrLeft (fun _ : Fin n => (volume : Measure ℝ)) σ.symm
      have heq : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm)) =
          (fun v : Fin n → ℝ => v ∘ σ) := by
        ext v i
        simpa [MeasurableEquiv.piCongrLeft] using
          Equiv.piCongrLeft_apply_apply (fun _ : Fin n => ℝ) σ.symm v (σ i)
      rwa [heq, ← volume_pi] at h
    have hmp2 : MeasurePreserving (fun y : Fin n → ℝ => y ∘ σ) μF μF := by
      have h := measurePreserving_piCongrLeft (fun _ : Fin n => F) σ.symm
      have heq : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm)) =
          (fun y : Fin n → ℝ => y ∘ σ) := by
        ext y i
        simpa [MeasurableEquiv.piCongrLeft] using
          Equiv.piCongrLeft_apply_apply (fun _ : Fin n => ℝ) σ.symm y (σ i)
      rwa [heq] at h
    have hmp := hmp1.prod hmp2
    have hpre : (Prod.map (fun v : Fin n → ℝ => v ∘ σ) (fun y : Fin n → ℝ => y ∘ σ)) ⁻¹'
        (E ∩ (Δs ×ˢ Set.univ)) = E ∩ (chamber σ ×ˢ Set.univ) := by
      ext ⟨v, y⟩
      simp only [Set.mem_preimage, Prod.map_apply, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ,
        and_true, chamber, hEsymm σ v y]
    rw [← hpre, hmp.measure_preimage (hEmeas.inter (hΔs_meas.prod MeasurableSet.univ)).nullMeasurableSet]
  -- Assemble the sum over all n! permutations
  rw [hrest_eq, Measure.restrict_congr_set hQ_ae_eq]
  have hprod_rest : ∀ (S : Set (Fin n → ℝ)), MeasurableSet S →
      ((volume.restrict S).prod μF) E = (volume.prod μF) (E ∩ (S ×ˢ Set.univ)) := by
    intro S hS
    rw [Measure.prod_apply hEmeas, Measure.prod_apply (hEmeas.inter (hS.prod MeasurableSet.univ))]
    rw [← lintegral_indicator hS]
    refine lintegral_congr fun v => ?_
    by_cases hv : v ∈ S
    · simp only [Set.indicator_of_mem hv]
      congr 1; ext y; simp [hv]
    · simp only [Set.indicator_of_notMem hv]
      have hempty : Prod.mk v ⁻¹' (E ∩ (S ×ˢ Set.univ)) = ∅ := by
        ext y; simp [hv]
      rw [hempty, measure_empty]
  rw [hprod_rest Δs hΔs_meas, hprod_rest (⋃ σ, chamber σ) (MeasurableSet.iUnion hch_meas)]
  have hunion : E ∩ ((⋃ σ : Equiv.Perm (Fin n), chamber σ) ×ˢ Set.univ) =
      ⋃ σ : Equiv.Perm (Fin n), (E ∩ (chamber σ ×ˢ Set.univ)) := by
    ext ⟨v, y⟩; simp
  rw [hunion]
  symm
  have hdisj : Pairwise fun σ₁ σ₂ : Equiv.Perm (Fin n) =>
      Disjoint (E ∩ (chamber σ₁ ×ˢ Set.univ)) (E ∩ (chamber σ₂ ×ˢ Set.univ)) :=
    fun σ₁ σ₂ hne => Set.disjoint_left.mpr fun p hp1 hp2 =>
      Set.disjoint_left.mp (hch_disj hne) hp1.2.1 hp2.2.1
  rw [measure_iUnion hdisj
    (fun σ => hEmeas.inter ((hch_meas σ).prod MeasurableSet.univ))]
  simp_rw [hpiece, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]

private lemma multinomial_card_nat :
    ∀ (m n : ℕ) (k : Fin m → ℕ) (r : ℕ),
      (∑ i : Fin m, k i) + r = n →
      (Finset.univ.filter (fun f : Fin n → Option (Fin m) =>
        (∀ i : Fin m, (Finset.univ.filter (fun j : Fin n => f j = some i)).card = k i) ∧
        (Finset.univ.filter (fun j : Fin n => f j = none)).card = r)).card *
        (Nat.factorial r * ∏ i : Fin m, Nat.factorial (k i)) = Nat.factorial n := by
  intro m
  induction m with
  | zero =>
    intro n k r hsum
    simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add, Finset.prod_empty, mul_one] at hsum ⊢
    subst hsum
    have hcard1 : (Finset.univ.filter (fun f : Fin r → Option (Fin 0) =>
        (∀ i : Fin 0, (Finset.univ.filter (fun j : Fin r => f j = some i)).card = k i) ∧
        (Finset.univ.filter (fun j : Fin r => f j = none)).card = r)).card = 1 := by
      have heq : Finset.univ.filter (fun f : Fin r → Option (Fin 0) =>
          (∀ i : Fin 0, (Finset.univ.filter (fun j : Fin r => f j = some i)).card = k i) ∧
          (Finset.univ.filter (fun j : Fin r => f j = none)).card = r) = {fun _ => none} := by
        ext f
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro _
          ext j
          cases hf : f j with
          | none => rfl
          | some x => exact Fin.elim0 x
        · rintro rfl
          exact ⟨fun i => Fin.elim0 i, by simp⟩
      rw [heq, Finset.card_singleton]
    rw [hcard1, one_mul]
  | succ m ih =>
    intro n k r hsum
    let k' : Fin m → ℕ := fun i => k i.castSucc
    let kl : ℕ := k (Fin.last m)
    have hsum_split : (∑ i : Fin m, k' i) + r + kl = n := by
      rw [Fin.sum_univ_castSucc] at hsum
      dsimp [k', kl]; omega
    let n' : ℕ := n - kl
    have hkl_le : kl ≤ n := by omega
    have hsum' : (∑ i : Fin m, k' i) + r = n' := by omega
    -- Partition valid assignments f by the kl-element subset S = {j | f j = some (Fin.last m)}
    let Good := Finset.univ.filter (fun f : Fin n → Option (Fin (m + 1)) =>
      (∀ i : Fin (m + 1), (Finset.univ.filter (fun j : Fin n => f j = some i)).card = k i) ∧
      (Finset.univ.filter (fun j : Fin n => f j = none)).card = r)
    let Good' := Finset.univ.filter (fun g : Fin n' → Option (Fin m) =>
      (∀ i : Fin m, (Finset.univ.filter (fun j : Fin n' => g j = some i)).card = k' i) ∧
      (Finset.univ.filter (fun j : Fin n' => g j = none)).card = r)
    have hcard_good : Good.card = Nat.choose n kl * Good'.card := by
      let PSet : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard kl
      have hcard_PSet : PSet.card = Nat.choose n kl := by
        simp [PSet, Finset.card_powersetCard]
      rw [← hcard_PSet]
      -- Fiber over S = {j | f j = some (Fin.last m)}
      have hfib : Good.card = ∑ S ∈ PSet, (Good.filter (fun f => Finset.univ.filter (fun j => f j = some (Fin.last m)) = S)).card := by
        rw [← Finset.card_biUnion]
        · congr 1; ext f
          simp only [Finset.mem_biUnion, Finset.mem_filter, PSet, Finset.mem_powersetCard,
            Finset.subset_univ, true_and]
          constructor
          · intro hf
            refine ⟨Finset.univ.filter (fun j => f j = some (Fin.last m)), ?_, hf, rfl⟩
            exact (Finset.mem_filter.mp hf).2.1 (Fin.last m)
          · rintro ⟨_, _, hf, _⟩; exact hf
        · intro S₁ _ S₂ _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro f h1 h2
          simp only [Finset.mem_filter] at h1 h2
          exact hne (h1.2.symm.trans h2.2)
      rw [hfib]
      have hconst : ∀ S ∈ PSet,
          (Good.filter (fun f => Finset.univ.filter (fun j => f j = some (Fin.last m)) = S)).card = Good'.card := by
        intro S hS
        have hScard : S.card = kl := (Finset.mem_powersetCard.mp hS).2
        have hScompl_card : Fintype.card {j : Fin n // j ∉ S} = n' := by
          rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hScard]
        let e : {j : Fin n // j ∉ S} ≃ Fin n' := Fintype.equivFinOfCardEq hScompl_card
        refine Finset.card_bij
          (fun f hf => fun a : Fin n' =>
            match f (e.symm a).1 with
            | none => none
            | some i => if h : i.val < m then some ⟨i.val, h⟩ else none)
          ?_ ?_ ?_
        · intro f hf
          simp only [Finset.mem_filter, Good, Finset.mem_univ, true_and] at hf
          obtain ⟨⟨hfk, hfr⟩, hfS⟩ := hf
          have hnotlast : ∀ a : Fin n', f (e.symm a).1 ≠ some (Fin.last m) := by
            intro a heq
            have hmem : (e.symm a).1 ∈ S := by
              set x := (e.symm a).1
              rw [← hfS]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
            exact (e.symm a).2 hmem
          simp only [Good', Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro i
            change _ = k i.castSucc
            rw [← hfk i.castSucc]
            refine Finset.card_bij (fun a _ => (e.symm a).1) ?_ ?_ ?_
            · intro a ha
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
              cases hfa : f (e.symm a).1 with
              | none => simp [hfa] at ha
              | some u =>
                simp only [hfa] at ha
                split_ifs at ha with hu
                injection ha with ha'
                have : u = i.castSucc := Fin.ext (by simpa using congrArg Fin.val ha')
                rw [this]
            · intro a _ b _ hab
              exact e.symm.injective (Subtype.ext hab)
            · intro j hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              have hjS : j ∉ S := by
                intro hmem
                have hmem' : j ∈ Finset.univ.filter (fun j : Fin n => f j = some (Fin.last m)) := by
                  rwa [hfS]
                have hfl := (Finset.mem_filter.mp hmem').2
                rw [hj] at hfl
                exact Fin.castSucc_ne_last i (Option.some.inj hfl)
              refine ⟨e ⟨j, hjS⟩, ?_, by simp⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply, hj]
              simp [Fin.val_castSucc, i.isLt]
          · rw [← hfr]
            refine Finset.card_bij (fun a _ => (e.symm a).1) ?_ ?_ ?_
            · intro a ha
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
              cases hfa : f (e.symm a).1 with
              | none => rfl
              | some u =>
                simp only [hfa] at ha
                split_ifs at ha with hu
                exfalso
                have : u = Fin.last m := Fin.ext (by simp [Fin.last]; omega)
                rw [this] at hfa
                exact hnotlast a hfa
            · intro a _ b _ hab
              exact e.symm.injective (Subtype.ext hab)
            · intro j hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              have hjS : j ∉ S := by
                intro hmem
                have hmem' : j ∈ Finset.univ.filter (fun j : Fin n => f j = some (Fin.last m)) := by
                  rwa [hfS]
                have hfl := (Finset.mem_filter.mp hmem').2
                rw [hj] at hfl
                simp at hfl
              refine ⟨e ⟨j, hjS⟩, ?_, by simp⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply, hj]
        · intro f₁ hf₁ f₂ hf₂ heq
          simp only [Finset.mem_filter, Good, Finset.mem_univ, true_and] at hf₁ hf₂
          funext j
          by_cases hj : j ∈ S
          · have hmem1 : j ∈ Finset.univ.filter (fun j : Fin n => f₁ j = some (Fin.last m)) := by
              rwa [hf₁.2]
            have hmem2 : j ∈ Finset.univ.filter (fun j : Fin n => f₂ j = some (Fin.last m)) := by
              rwa [hf₂.2]
            have h1 : f₁ j = some (Fin.last m) := (Finset.mem_filter.mp hmem1).2
            have h2 : f₂ j = some (Fin.last m) := (Finset.mem_filter.mp hmem2).2
            rw [h1, h2]
          · have h1ne : f₁ j ≠ some (Fin.last m) := fun h => by
              apply hj; rw [← hf₁.2]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
            have h2ne : f₂ j ≠ some (Fin.last m) := fun h => by
              apply hj; rw [← hf₂.2]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
            have hfun := congrFun heq (e ⟨j, hj⟩)
            simp only [Equiv.symm_apply_apply] at hfun
            cases h1 : f₁ j with
            | none =>
              cases h2 : f₂ j with
              | none => rfl
              | some u2 =>
                have hu2 : u2.val < m := by
                  by_contra hge
                  apply h2ne; rw [h2]; exact congrArg some (Fin.ext (by simp [Fin.last]; omega))
                simp [h1, h2, hu2] at hfun
            | some u1 =>
              have hu1 : u1.val < m := by
                by_contra hge
                apply h1ne; rw [h1]; exact congrArg some (Fin.ext (by simp [Fin.last]; omega))
              cases h2 : f₂ j with
              | none => simp [h1, h2, hu1] at hfun
              | some u2 =>
                have hu2 : u2.val < m := by
                  by_contra hge
                  apply h2ne; rw [h2]; exact congrArg some (Fin.ext (by simp [Fin.last]; omega))
                simp only [h1, h2, dif_pos hu1, dif_pos hu2, Option.some.injEq] at hfun
                exact congrArg some (Fin.ext (by simpa using congrArg Fin.val hfun))
        · intro g hg
          simp only [Good', Finset.mem_filter, Finset.mem_univ, true_and] at hg
          let f : Fin n → Option (Fin (m + 1)) := fun j =>
            if hj : j ∈ S then some (Fin.last m)
            else (g (e ⟨j, hj⟩)).map Fin.castSucc
          refine ⟨f, ?_, ?_⟩
          · simp only [Finset.mem_filter, Good, Finset.mem_univ, true_and]
            have hfS : Finset.univ.filter (fun j : Fin n => f j = some (Fin.last m)) = S := by
              ext j
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, f]
              split_ifs with hj
              · simp [hj]
              · simp only [hj, iff_false]
                cases g (e ⟨j, hj⟩) with
                | none => simp
                | some u => simp [Fin.castSucc_ne_last]
            refine ⟨⟨?_, ?_⟩, hfS⟩
            · intro i
              refine Fin.lastCases ?_ (fun i0 => ?_) i
              · rw [hfS, hScard]
              · change _ = k' i0
                rw [← hg.1 i0]
                refine Finset.card_bij (fun j hj => e ⟨j, by
                  intro hmem
                  have hj' := (Finset.mem_filter.mp hj).2
                  simp only [f, dif_pos hmem] at hj'
                  exact Fin.castSucc_ne_last i0 (Option.some.inj hj').symm⟩) ?_ ?_ ?_
                · intro j hj
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
                  have hjS : j ∉ S := by
                    intro hmem
                    simp only [f, dif_pos hmem] at hj
                    exact Fin.castSucc_ne_last i0 (Option.some.inj hj).symm
                  simp only [f, dif_neg hjS] at hj
                  cases hge : g (e ⟨j, hjS⟩) with
                  | none => simp [hge] at hj
                  | some u =>
                    simp only [hge, Option.map_some, Option.some.injEq] at hj
                    rw [Fin.castSucc_inj.mp hj]
                · intro j₁ _ j₂ _ he
                  exact congrArg Subtype.val (e.injective he)
                · intro a ha
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
                  refine ⟨(e.symm a).1, ?_, by simp⟩
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and, f, dif_neg (e.symm a).2,
                    Subtype.coe_eta, Equiv.apply_symm_apply, ha, Option.map_some]
            · rw [← hg.2]
              refine Finset.card_bij (fun j hj => e ⟨j, by
                intro hmem
                have hj' := (Finset.mem_filter.mp hj).2
                simp only [f, dif_pos hmem] at hj'
                simp at hj'⟩) ?_ ?_ ?_
              · intro j hj
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
                have hjS : j ∉ S := by
                  intro hmem; simp [f, dif_pos hmem] at hj
                simp only [f, dif_neg hjS] at hj
                cases hge : g (e ⟨j, hjS⟩) with
                | none => rfl
                | some u => simp [hge] at hj
              · intro j₁ _ j₂ _ he
                exact congrArg Subtype.val (e.injective he)
              · intro a ha
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
                refine ⟨(e.symm a).1, ?_, by simp⟩
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, f, dif_neg (e.symm a).2,
                  Subtype.coe_eta, Equiv.apply_symm_apply, ha, Option.map_none]
          · funext a
            simp only [f, dif_neg (e.symm a).2, Subtype.coe_eta, Equiv.apply_symm_apply]
            cases hga : g a with
            | none => rfl
            | some u => simp [u.isLt]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
    -- Combine with induction hypothesis and Nat.choose_mul_factorial_mul_factorial
    have hih := ih n' k' r hsum'
    rw [Fin.prod_univ_castSucc]
    calc Good.card * (Nat.factorial r * ((∏ i : Fin m, Nat.factorial (k' i)) * Nat.factorial kl))
        = (Nat.choose n kl * Good'.card) * (Nat.factorial r * ((∏ i : Fin m, Nat.factorial (k' i)) * Nat.factorial kl)) := by
            rw [hcard_good]
      _ = (Nat.choose n kl * Nat.factorial kl) *
            (Good'.card * (Nat.factorial r * ∏ i : Fin m, Nat.factorial (k' i))) := by ring
      _ = (Nat.choose n kl * Nat.factorial kl) * Nat.factorial n' := by rw [hih]
      _ = Nat.choose n kl * Nat.factorial kl * Nat.factorial (n - kl) := by ring
      _ = Nat.factorial n := Nat.choose_mul_factorial_mul_factorial hkl_le

open Classical in
private lemma pi_measure_counts_eq
    (m n : ℕ) (ρ : Measure (ℝ × ℝ)) [IsProbabilityMeasure ρ]
    (A : Fin m → Set (ℝ × ℝ)) (hAmeas : ∀ i, MeasurableSet (A i))
    (hAdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (k : Fin m → ℕ) :
    (Measure.pi (fun _ : Fin n => ρ))
        {z : Fin n → ℝ × ℝ | ∀ i : Fin m, (Finset.univ.filter (fun j : Fin n => z j ∈ A i)).card = k i} =
      if ∑ i : Fin m, k i ≤ n then
        ENNReal.ofReal ((Nat.factorial n : ℝ) /
          ((Nat.factorial (n - ∑ i : Fin m, k i) : ℝ) * ∏ i : Fin m, (Nat.factorial (k i) : ℝ))) *
          (ρ (⋃ i : Fin m, A i)ᶜ) ^ (n - ∑ i : Fin m, k i) *
          ∏ i : Fin m, (ρ (A i)) ^ (k i)
      else 0 := by
  let S : Set (Fin n → ℝ × ℝ) :=
    {z : Fin n → ℝ × ℝ | ∀ i : Fin m, (Finset.univ.filter (fun j : Fin n => z j ∈ A i)).card = k i}
  by_cases hle : ∑ i : Fin m, k i ≤ n
  · rw [if_pos hle]
    let r : ℕ := n - ∑ i : Fin m, k i
    have hsum : (∑ i : Fin m, k i) + r = n := by omega
    let B0 : Set (ℝ × ℝ) := (⋃ i : Fin m, A i)ᶜ
    let cell : Option (Fin m) → Set (ℝ × ℝ) := fun o =>
      match o with
      | some i => A i
      | none => B0
    have hcell_meas : ∀ o, MeasurableSet (cell o) := fun o => by
      cases o with
      | some i => exact hAmeas i
      | none => exact (MeasurableSet.iUnion hAmeas).compl
    have hcell_disj : Pairwise (fun o₁ o₂ => Disjoint (cell o₁) (cell o₂)) := by
      intro o₁ o₂ hne
      cases o₁ with
      | none =>
        cases o₂ with
        | none => exact absurd rfl hne
        | some i =>
          rw [Set.disjoint_left]
          intro x hx hxi; exact hx (Set.mem_iUnion.mpr ⟨i, hxi⟩)
      | some i =>
        cases o₂ with
        | none =>
          rw [Set.disjoint_left]
          intro x hxi hx; exact hx (Set.mem_iUnion.mpr ⟨i, hxi⟩)
        | some j =>
          exact hAdisj (fun h => hne (congrArg some h))
    let Good : Finset (Fin n → Option (Fin m)) := Finset.univ.filter (fun f =>
      (∀ i : Fin m, (Finset.univ.filter (fun j : Fin n => f j = some i)).card = k i) ∧
      (Finset.univ.filter (fun j : Fin n => f j = none)).card = r)
    have hS_eq : S = ⋃ f ∈ Good, Set.univ.pi (fun j : Fin n => cell (f j)) := by
      ext z
      simp only [S, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_univ_pi]
      constructor
      · intro hz
        classical
        let f : Fin n → Option (Fin m) := fun j =>
          if h : ∃ i : Fin m, z j ∈ A i then some h.choose else none
        have hfz : ∀ j : Fin n, z j ∈ cell (f j) := by
          intro j
          dsimp [f]
          split_ifs with h
          · exact h.choose_spec
          · simp only [cell, B0, Set.mem_compl_iff, Set.mem_iUnion]; exact h
        have hfi : ∀ (j : Fin n) (i : Fin m), f j = some i ↔ z j ∈ A i := by
          intro j i
          constructor
          · intro h; have := hfz j; rwa [h] at this
          · intro hzi
            have hex : ∃ i : Fin m, z j ∈ A i := ⟨i, hzi⟩
            dsimp [f]
            rw [dif_pos hex]
            congr 1
            by_contra hne
            exact Set.disjoint_left.mp (hAdisj hne) hex.choose_spec hzi
        have hf_good : f ∈ Good := by
          simp only [Good, Finset.mem_filter, Finset.mem_univ, true_and]
          have hki : ∀ i : Fin m, (Finset.univ.filter (fun j : Fin n => f j = some i)).card = k i := by
            intro i
            rw [← hz i]
            congr 1; ext j; simp [hfi j i]
          refine ⟨hki, ?_⟩
          have hpart : (∑ i : Fin m, (Finset.univ.filter (fun j : Fin n => f j = some i)).card) +
              (Finset.univ.filter (fun j : Fin n => f j = none)).card = n := by
            have hu : (Finset.univ.biUnion (fun i : Fin m => Finset.univ.filter (fun j : Fin n => f j = some i))) ∪
                (Finset.univ.filter (fun j : Fin n => f j = none)) = Finset.univ := by
              ext j; simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
                Finset.mem_univ, true_and, iff_true]
              cases hf : f j with
              | none => exact Or.inr rfl
              | some i => exact Or.inl ⟨i, rfl⟩
            have hd1 : Disjoint
                (Finset.univ.biUnion (fun i : Fin m => Finset.univ.filter (fun j : Fin n => f j = some i)))
                (Finset.univ.filter (fun j : Fin n => f j = none)) := by
              rw [Finset.disjoint_left]
              intro j h1 h2
              simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
              rcases h1 with ⟨i, hi⟩
              rw [hi] at h2; simp at h2
            have hd2 : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
                (fun i => Finset.univ.filter (fun j : Fin n => f j = some i)) := by
              intro i₁ _ i₂ _ hne
              change Disjoint _ _
              rw [Finset.disjoint_left]
              intro j h1 h2
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
              exact hne (Option.some.inj (h1.symm.trans h2))
            have htot := congrArg Finset.card hu
            rw [Finset.card_union_of_disjoint hd1, Finset.card_biUnion hd2, Finset.card_univ,
              Fintype.card_fin] at htot
            exact htot
          simp_rw [hki] at hpart
          omega
        exact ⟨f, hf_good, hfz⟩
      · rintro ⟨f, hf, hfz⟩ i
        simp only [Good, Finset.mem_filter, Finset.mem_univ, true_and] at hf
        rw [← hf.1 i]
        congr 1; ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hzi
          by_contra hne
          exact Set.disjoint_left.mp (hcell_disj hne) (hfz j) hzi
        · intro hfi
          have := hfz j; rwa [hfi] at this
    change (Measure.pi (fun _ : Fin n => ρ)) S = _
    rw [hS_eq]
    have hdisj_boxes : (Good : Set (Fin n → Option (Fin m))).PairwiseDisjoint
        (fun f => Set.univ.pi (fun j : Fin n => cell (f j))) := by
      intro f₁ _ f₂ _ hne
      change Disjoint _ _
      rw [Set.disjoint_left]
      intro z h1 h2
      apply hne
      funext j
      by_contra hfj
      exact Set.disjoint_left.mp (hcell_disj hfj) (h1 j (Set.mem_univ j)) (h2 j (Set.mem_univ j))
    rw [measure_biUnion_finset hdisj_boxes (fun f _ => MeasurableSet.univ_pi fun j => hcell_meas (f j))]
    have hbox : ∀ f ∈ Good,
        (Measure.pi (fun _ : Fin n => ρ)) (Set.univ.pi (fun j : Fin n => cell (f j))) =
          (ρ B0) ^ r * ∏ i : Fin m, (ρ (A i)) ^ (k i) := by
      intro f hf
      simp only [Good, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      rw [Measure.pi_pi]
      have hprod_part : (∏ j : Fin n, ρ (cell (f j))) =
          (∏ j ∈ Finset.univ.filter (fun j : Fin n => f j = none), ρ (cell (f j))) *
          (∏ i : Fin m, ∏ j ∈ Finset.univ.filter (fun j : Fin n => f j = some i), ρ (cell (f j))) := by
        have hd2 : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
            (fun i => Finset.univ.filter (fun j : Fin n => f j = some i)) := by
          intro i₁ _ i₂ _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro j h1 h2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          exact hne (Option.some.inj (h1.symm.trans h2))
        rw [← Finset.prod_biUnion hd2]
        have hd1 : Disjoint
            (Finset.univ.filter (fun j : Fin n => f j = none))
            (Finset.univ.biUnion (fun i : Fin m => Finset.univ.filter (fun j : Fin n => f j = some i))) := by
          rw [Finset.disjoint_left]
          intro j h1 h2
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          rcases h2 with ⟨i, hi⟩
          rw [h1] at hi; simp at hi
        rw [← Finset.prod_union hd1]
        congr 1; ext j
        simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
          true_and, true_iff]
        cases f j with
        | none => exact Or.inl rfl
        | some i => exact Or.inr ⟨i, rfl⟩
      rw [hprod_part]
      congr 1
      · have h1 : ∀ j ∈ Finset.univ.filter (fun j : Fin n => f j = none), ρ (cell (f j)) = ρ B0 := by
          intro j hj; rw [(Finset.mem_filter.mp hj).2]
        rw [Finset.prod_congr rfl h1, Finset.prod_const, hf.2]
      · refine Finset.prod_congr rfl fun i _ => ?_
        have h1 : ∀ j ∈ Finset.univ.filter (fun j : Fin n => f j = some i), ρ (cell (f j)) = ρ (A i) := by
          intro j hj; rw [(Finset.mem_filter.mp hj).2]
        rw [Finset.prod_congr rfl h1, Finset.prod_const, hf.1 i]
    rw [Finset.sum_congr rfl hbox, Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
    congr 1
    congr 1
    have hcard_eq := multinomial_card_nat m n k r hsum
    have hcard_real : (Good.card : ℝ) * ((Nat.factorial r : ℝ) * ∏ i : Fin m, (Nat.factorial (k i) : ℝ)) =
        (Nat.factorial n : ℝ) := by
      exact_mod_cast hcard_eq
    have hdenom_ne : ((Nat.factorial r : ℝ) * ∏ i : Fin m, (Nat.factorial (k i) : ℝ)) ≠ 0 := by
      refine mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)) ?_
      rw [Finset.prod_ne_zero_iff]
      intro i _
      exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k i))
    have hdiv : (Good.card : ℝ) = (Nat.factorial n : ℝ) /
        ((Nat.factorial r : ℝ) * ∏ i : Fin m, (Nat.factorial (k i) : ℝ)) :=
      eq_div_of_mul_eq hdenom_ne hcard_real
    rw [← ENNReal.ofReal_natCast, hdiv]
  · rw [if_neg hle]
    have hempty : S = ∅ := by
      ext z
      simp only [S, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hz
      have hdisj_fin : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
          (fun i => Finset.univ.filter (fun j : Fin n => z j ∈ A i)) := by
        intro i₁ _ i₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro j h1 h2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        exact Set.disjoint_left.mp (hAdisj hne) h1 h2
      have hcard_le : (∑ i : Fin m, (Finset.univ.filter (fun j : Fin n => z j ∈ A i)).card) ≤ n := by
        rw [← Finset.card_biUnion hdisj_fin]
        calc (Finset.univ.biUnion (fun i : Fin m => Finset.univ.filter (fun j : Fin n => z j ∈ A i))).card
            ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
          _ = n := by simp
      simp_rw [hz] at hcard_le
      exact hle hcard_le
    change (Measure.pi (fun _ : Fin n => ρ)) S = 0
    rw [hempty, measure_empty]

private lemma intensity_eq_mul_rho
    (rate : ℝ≥0) (t : ℝ≥0) (ht : 0 < t)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    {B : Set (ℝ × ℝ)} (hBmeas : MeasurableSet B)
    (hBsub : B ⊆ Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ) :
    ((volume.restrict (Set.Ici (0 : ℝ))).prod ((rate : ℝ≥0∞) • F)) B =
      ((rate * t : ℝ≥0) : ℝ≥0∞) *
        (((ENNReal.ofReal (t : ℝ))⁻¹ • (volume.restrict (Set.Icc (0 : ℝ) (t : ℝ)))).prod F) B := by
  let μI : Measure ℝ := volume.restrict (Set.Ici (0 : ℝ))
  let μC : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))
  let μO : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))
  have h1 : (μI.prod ((rate : ℝ≥0∞) • F)) B = (rate : ℝ≥0∞) * ∫⁻ x in Set.Ioc (0 : ℝ) (t : ℝ), F (Prod.mk x ⁻¹' B) := by
    rw [Measure.prod_apply hBmeas]
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [lintegral_const_mul _ (measurable_measure_prodMk_left hBmeas)]
    congr 1
    rw [← lintegral_indicator measurableSet_Ici, ← lintegral_indicator measurableSet_Ioc]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) (t : ℝ)
    · have hx' : x ∈ Set.Ici (0 : ℝ) := le_of_lt hx.1
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    · simp only [Set.indicator_of_notMem hx]
      by_cases hx' : x ∈ Set.Ici (0 : ℝ)
      · simp only [Set.indicator_of_mem hx']
        have hempty : Prod.mk x ⁻¹' B = ∅ := by
          ext y; simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
          intro hxy; exact hx (hBsub hxy).1
        rw [hempty, measure_empty]
      · simp [Set.indicator_of_notMem hx']
  have h2 : (((ENNReal.ofReal (t : ℝ))⁻¹ • μC).prod F) B =
      (ENNReal.ofReal (t : ℝ))⁻¹ * ∫⁻ x in Set.Ioc (0 : ℝ) (t : ℝ), F (Prod.mk x ⁻¹' B) := by
    rw [Measure.prod_apply hBmeas, lintegral_smul_measure, smul_eq_mul]
    congr 1
    rw [← lintegral_indicator measurableSet_Icc, ← lintegral_indicator measurableSet_Ioc]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) (t : ℝ)
    · have hx' : x ∈ Set.Icc (0 : ℝ) (t : ℝ) := ⟨le_of_lt hx.1, hx.2⟩
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    · simp only [Set.indicator_of_notMem hx]
      by_cases hx' : x ∈ Set.Icc (0 : ℝ) (t : ℝ)
      · simp only [Set.indicator_of_mem hx']
        have hempty : Prod.mk x ⁻¹' B = ∅ := by
          ext y; simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
          intro hxy; exact hx (hBsub hxy).1
        rw [hempty, measure_empty]
      · simp [Set.indicator_of_notMem hx']
  rw [h1, h2, ← mul_assoc]
  congr 1
  have htpos : (0 : ℝ≥0∞) < ENNReal.ofReal (t : ℝ) := ENNReal.ofReal_pos.mpr ht
  rw [ENNReal.coe_mul, ENNReal.ofReal_coe_nnreal, mul_assoc,
    ENNReal.mul_inv_cancel (by exact_mod_cast ne_of_gt ht) ENNReal.coe_ne_top, mul_one]

end MarkedCPBoundedHelpers

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hFzero : F {0} = 0)
    (N : ℝ≥0 → Ω → ℕ)
    (T : ℕ → Ω → ℝ≥0)
    (ξ : ℕ → Ω → ℝ)
    (hTmeas : ∀ n : ℕ, 0 < n → Measurable (T n))
    (hξmeas : ∀ k : ℕ, Measurable (ξ k))
    (hNlevy : ProbabilityTheory.IsLevyProcess
       (fun t ω => (N t ω : ℝ)) P)
    (hNlaw : ∀ t : ℝ≥0,
       P.map (N t) = ProbabilityTheory.poissonMeasure (rate * t))
    (harrival : ∀ᵐ ω ∂P,
       ∀ (n : ℕ), 0 < n →
         ∀ (t : ℝ≥0), (n ≤ N t ω ↔ T n ω ≤ t))
    (hmarklaw : ∀ k : ℕ, P.map (ξ k) = F)
    (hIID : ProbabilityTheory.iIndepFun ξ P)
    (hcross : ProbabilityTheory.Indep
      (⨆ k : ℕ, MeasurableSpace.comap (ξ k) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (N t) inferInstance) P)
    (t : ℝ≥0) (m : ℕ) (A : Fin m → Set (ℝ × ℝ))
    (hAmeas : ∀ i, MeasurableSet (A i))
    (hAsub : ∀ i, A i ⊆ Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ)
    (hAdisj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    let μ : Ω → Measure (ℝ × ℝ) := fun ω =>
      Measure.sum (fun n : ℕ =>
        Measure.dirac ((T (n + 1) ω : ℝ), ξ (n + 1) ω))
    let intensity : Measure (ℝ × ℝ) :=
      (volume.restrict (Set.Ici (0 : ℝ))).prod ((rate : ENNReal) • F)
    (∀ i : Fin m,
       P.map (fun ω => μ ω (A i)) =
         (ProbabilityTheory.poissonMeasure (intensity (A i)).toNNReal).map
           (Nat.cast : ℕ → ENNReal)) ∧
    ProbabilityTheory.iIndepFun (fun i (ω : Ω) => μ ω (A i)) P := by
  intro μ intensity
  classical
  let X : Fin m → Ω → ℝ≥0∞ := fun i ω => μ ω (A i)
  have hXmeas : ∀ i : Fin m, Measurable (X i) := fun i =>
    MarkedCPBoundedHelpers.measurable_marked_mu_eval T ξ hTmeas hξmeas (hAmeas i)
  let ν : Fin m → Measure ℝ≥0∞ := fun i =>
    (ProbabilityTheory.poissonMeasure (intensity (A i)).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)
  have hν_prob : ∀ i : Fin m, IsProbabilityMeasure (ν i) := fun i =>
    Measure.isProbabilityMeasure_map measurable_from_top.aemeasurable
  -- Core reduction: it suffices to show P.map (fun ω i => X i ω) = Measure.pi ν
  suffices hjoint_eq : P.map (fun ω i => X i ω) = Measure.pi ν by
    have hmarg : ∀ i : Fin m, P.map (X i) = ν i := by
      intro i
      have hev := (measurePreserving_eval ν i).map_eq
      rw [← hjoint_eq, Measure.map_map (measurable_pi_apply i) (measurable_pi_lambda _ hXmeas)] at hev
      exact hev
    refine ⟨hmarg, (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hXmeas i).aemeasurable)).mpr ?_⟩
    simpa [hmarg] using hjoint_eq
  -- Handle t = 0 separately
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht0 | ht
  · subst ht0
    have hAempty : ∀ i : Fin m, A i = ∅ := by
      intro i
      have hsub := hAsub i
      simp only [NNReal.coe_zero, Set.Ioc_self, Set.empty_prod, Set.subset_empty_iff] at hsub
      exact hsub
    have hX0 : (fun ω (i : Fin m) => X i ω) = fun _ _ => 0 := by
      ext ω i; simp [X, hAempty i]
    have hpo0 : ProbabilityTheory.poissonMeasure 0 = Measure.dirac 0 := by
      ext s hs
      rw [ProbabilityTheory.poissonMeasure, Measure.dirac_apply' _ hs, Measure.sum_apply _ hs]
      rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
      simp [Measure.dirac_apply' _ hs]
    have hν0 : ν = fun _ : Fin m => Measure.dirac 0 := by
      funext i
      simp only [ν, hAempty i, measure_empty, ENNReal.toNNReal_zero]
      rw [hpo0, Measure.map_dirac' measurable_from_top, Nat.cast_zero]
    rw [hX0, Measure.map_const, measure_univ, one_smul, hν0]
    symm
    refine Measure.pi_eq fun s _ => ?_
    simp only [Measure.dirac_apply' _ (MeasurableSet.univ_pi ‹_›)]
    by_cases h0 : (fun _ : Fin m => (0 : ℝ≥0∞)) ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem h0]
      refine (Finset.prod_eq_one fun i _ => ?_).symm
      rw [Measure.dirac_apply' _ (‹∀ i, MeasurableSet (s i)› i), Set.indicator_of_mem (h0 i (Set.mem_univ i))]
      rfl
    · rw [Set.indicator_of_notMem h0]
      simp only [Set.mem_univ_pi, not_forall] at h0
      obtain ⟨i0, hi0⟩ := h0
      refine (Finset.prod_eq_zero (Finset.mem_univ i0) ?_).symm
      rw [Measure.dirac_apply' _ (‹∀ i, MeasurableSet (s i)› i0), Set.indicator_of_notMem hi0]
  -- Case 0 < t: establish the joint PMF identity on all k : Fin m → ℕ
  let ρ : Measure (ℝ × ℝ) :=
    ((ENNReal.ofReal (t : ℝ))⁻¹ • (volume.restrict (Set.Icc (0 : ℝ) (t : ℝ)))).prod F
  have hU_prob : IsProbabilityMeasure
      ((ENNReal.ofReal (t : ℝ))⁻¹ • (volume.restrict (Set.Icc (0 : ℝ) (t : ℝ)))) := by
    constructor
    simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, Real.volume_Icc, sub_zero]
    exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr ht)) ENNReal.ofReal_ne_top
  have hρ_prob : IsProbabilityMeasure ρ := inferInstance
  -- Step 1: Joint PMF on every k : Fin m → ℕ
  have hjoint_pmf : ∀ k : Fin m → ℕ,
      P {ω | ∀ i : Fin m, X i ω = (k i : ℝ≥0∞)} =
        ∏ i : Fin m, ProbabilityTheory.poissonMeasure (intensity (A i)).toNNReal {k i} := by
    intro k
    -- Partition by N t ω = n
    have hN_ae := MarkedCPBoundedHelpers.aemeasurable_N_of_law P rate N hNlaw t
    have hsplit : {ω | ∀ i : Fin m, X i ω = (k i : ℝ≥0∞)} =
        ⋃ n : ℕ, {ω | N t ω = n ∧ ∀ i : Fin m, X i ω = (k i : ℝ≥0∞)} := by
      ext ω; simp
    have hdisj_n : Pairwise (fun n₁ n₂ : ℕ =>
        Disjoint {ω | N t ω = n₁ ∧ ∀ i : Fin m, X i ω = (k i : ℝ≥0∞)}
                 {ω | N t ω = n₂ ∧ ∀ i : Fin m, X i ω = (k i : ℝ≥0∞)}) := by
      intro n₁ n₂ hne
      rw [Set.disjoint_left]
      intro ω h1 h2; exact hne (h1.1.symm.trans h2.1)
    have hnm_n : ∀ n : ℕ, NullMeasurableSet {ω | N t ω = n ∧ ∀ i : Fin m, X i ω = (k i : ℝ≥0∞)} P := by
      intro n
      have h1 : NullMeasurableSet ((N t) ⁻¹' {n}) P := hN_ae.nullMeasurable (measurableSet_singleton n)
      have h2 : MeasurableSet {ω | ∀ i : Fin m, X i ω = (k i : ℝ≥0∞)} := by
        have : {ω | ∀ i : Fin m, X i ω = (k i : ℝ≥0∞)} = ⋂ i : Fin m, (X i) ⁻¹' {(k i : ℝ≥0∞)} := by
          ext ω; simp
        rw [this]
        exact MeasurableSet.iInter fun i => hXmeas i (measurableSet_singleton _)
      exact h1.inter h2.nullMeasurableSet
    rw [hsplit, measure_iUnion₀ (fun a b h => (hdisj_n h).aedisjoint) hnm_n]
    -- Compute each n-slice P {ω | N t ω = n ∧ ∀ i, X i ω = k i}
    have hslice : ∀ n : ℕ,
        P {ω | N t ω = n ∧ ∀ i : Fin m, X i ω = (k i : ℝ≥0∞)} =
          P {ω | N t ω = n} * (Measure.pi (fun _ : Fin n => ρ))
            {z : Fin n → ℝ × ℝ | ∀ i : Fin m, (Finset.univ.filter (fun j : Fin n => z j ∈ A i)).card = k i} := by
      intro n
      -- On {N t ω = n}, μ ω (A i) = ∑ j : Fin n, 1_{A i}(T (j+1) ω, ξ (j+1) ω) a.s.
      have hfin_ae : ∀ᵐ ω ∂P, N t ω = n →
          ∀ i : Fin m, X i ω = ((Finset.univ.filter (fun j : Fin n =>
            ((T (j.val + 1) ω : ℝ), ξ (j.val + 1) ω) ∈ A i)).card : ℝ≥0∞) := by
        filter_upwards [harrival] with ω ha hNt i
        change (Measure.sum (fun j : ℕ => Measure.dirac ((T (j + 1) ω : ℝ), ξ (j + 1) ω))) (A i) = _
        rw [Measure.sum_apply _ (hAmeas i)]
        have hvan : ∀ j : ℕ, n ≤ j → Measure.dirac ((T (j + 1) ω : ℝ), ξ (j + 1) ω) (A i) = 0 := by
          intro j hj
          rw [Measure.dirac_apply' _ (hAmeas i), Set.indicator_of_notMem]
          intro hmem
          have hle_t : T (j + 1) ω ≤ t := by exact_mod_cast (hAsub i hmem).1.2
          have hjN : j + 1 ≤ N t ω := (ha (j + 1) (Nat.succ_pos j) t).mpr hle_t
          omega
        rw [tsum_eq_sum (s := Finset.range n) (fun j hj => hvan j (by simp at hj; omega))]
        rw [← Fin.sum_univ_eq_sum_range (fun j => Measure.dirac ((T (j + 1) ω : ℝ), ξ (j + 1) ω) (A i)) n]
        have hterm : ∀ j : Fin n,
            Measure.dirac ((T (j.val + 1) ω : ℝ), ξ (j.val + 1) ω) (A i) =
              if ((T (j.val + 1) ω : ℝ), ξ (j.val + 1) ω) ∈ A i then (1 : ℝ≥0∞) else 0 := fun j => by
          rw [Measure.dirac_apply' _ (hAmeas i)]
          by_cases hm : ((T (j.val + 1) ω : ℝ), ξ (j.val + 1) ω) ∈ A i
          · simp [Set.indicator_of_mem hm, hm]
          · simp [Set.indicator_of_notMem hm, hm]
        simp_rw [hterm, Finset.sum_boole]
      let E_pi : Set (Fin n → ℝ × ℝ) :=
        {z : Fin n → ℝ × ℝ | ∀ i : Fin m, (Finset.univ.filter (fun j : Fin n => z j ∈ A i)).card = k i}
      have hE_pi_meas : MeasurableSet E_pi := by
        have hrew : E_pi = ⋂ i : Fin m,
            (fun z : Fin n → ℝ × ℝ => ∑ j : Fin n, (A i).indicator (fun _ => (1 : ℕ)) (z j)) ⁻¹' {k i} := by
          ext z
          simp only [E_pi, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
          refine forall_congr' fun i => ?_
          have hsum_eq : (∑ j : Fin n, (A i).indicator (fun _ => (1 : ℕ)) (z j)) =
              (Finset.univ.filter (fun j : Fin n => z j ∈ A i)).card := by
            have : ∀ j : Fin n, (A i).indicator (fun _ => (1 : ℕ)) (z j) = if z j ∈ A i then 1 else 0 := by
              intro j; by_cases h : z j ∈ A i <;> simp [h]
            simp_rw [this, Finset.sum_boole, Nat.cast_id]
          rw [hsum_eq]
        rw [hrew]
        refine MeasurableSet.iInter fun i => ?_
        have hmeas_sum : Measurable (fun z : Fin n → ℝ × ℝ => ∑ j : Fin n, (A i).indicator (fun _ => (1 : ℕ)) (z j)) :=
          Finset.measurable_sum _ fun j _ => (measurable_const.indicator (hAmeas i)).comp (measurable_pi_apply j)
        exact hmeas_sum (measurableSet_singleton (k i))
      let e := (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm
      let E_pair : Set ((Fin n → ℝ) × (Fin n → ℝ)) := e ⁻¹' E_pi
      have hE_pair_meas : MeasurableSet E_pair := e.measurable hE_pi_meas
      have hset_ae : {ω | N t ω = n ∧ ∀ i : Fin m, X i ω = (k i : ℝ≥0∞)} =ᵐ[P]
          {ω | N t ω = n ∧ (fun j : Fin n => (T (j.val + 1) ω : ℝ), fun j : Fin n => ξ (j.val + 1) ω) ∈ E_pair} := by
        filter_upwards [hfin_ae] with ω hω
        apply propext
        constructor
        · rintro ⟨hNt, hXk⟩
          refine ⟨hNt, fun i => ?_⟩
          have h1 := hω hNt i
          rw [hXk i] at h1
          exact (Nat.cast_inj (R := ℝ≥0∞)).mp h1.symm
        · rintro ⟨hNt, hEp⟩
          refine ⟨hNt, fun i => ?_⟩
          rw [hω hNt i]
          exact congrArg Nat.cast (hEp i)
      rw [measure_congr hset_ae]
      cases n with
      | zero =>
        by_cases hk0 : ∀ i : Fin m, k i = 0
        · have hEp_univ : E_pi = Set.univ := by
            ext z; simp [E_pi, hk0]
          have hset_eq : {ω | N t ω = 0 ∧ (fun j : Fin 0 => (T (j.val + 1) ω : ℝ),
              fun j : Fin 0 => ξ (j.val + 1) ω) ∈ E_pair} = {ω | N t ω = 0} := by
            ext ω; simp [E_pair, hEp_univ]
          rw [hset_eq]
          change P {ω | N t ω = 0} = P {ω | N t ω = 0} * (Measure.pi (fun _ : Fin 0 => ρ)) E_pi
          rw [hEp_univ, measure_univ, mul_one]
        · have hEp_empty : E_pi = ∅ := by
            ext z
            simp only [E_pi, Set.mem_setOf_eq, Finset.univ_eq_empty, Finset.filter_empty,
              Finset.card_empty, Set.mem_empty_iff_false, iff_false]
            intro h; exact hk0 fun i => (h i).symm
          have hset_eq : {ω | N t ω = 0 ∧ (fun j : Fin 0 => (T (j.val + 1) ω : ℝ),
              fun j : Fin 0 => ξ (j.val + 1) ω) ∈ E_pair} = ∅ := by
            ext ω; simp [E_pair, hEp_empty]
          rw [hset_eq]
          change P ∅ = P {ω | N t ω = 0} * (Measure.pi (fun _ : Fin 0 => ρ)) E_pi
          rw [hEp_empty, measure_empty, measure_empty, mul_zero]
      | succ n0 =>
        let n' := n0 + 1
        have hn' : 0 < n' := Nat.succ_pos n0
        let Tvec : Ω → (Fin n' → ℝ) := fun ω j => (T (j.val + 1) ω : ℝ)
        let ξvec : Ω → (Fin n' → ℝ) := fun ω j => ξ (j.val + 1) ω
        have hTvec_meas : Measurable Tvec :=
          measurable_pi_lambda _ fun j => NNReal.continuous_coe.measurable.comp (hTmeas (j.val + 1) (Nat.succ_pos _))
        have hξvec_meas : Measurable ξvec :=
          measurable_pi_lambda _ fun j => hξmeas (j.val + 1)
        have hLHS_map : P {ω | N t ω = n' ∧ (Tvec ω, ξvec ω) ∈ E_pair} =
            ((P.restrict {ω | N t ω = n'}).map (fun ω => (Tvec ω, ξvec ω))) E_pair := by
          rw [Measure.map_apply (hTvec_meas.prodMk hξvec_meas) hE_pair_meas,
            Measure.restrict_apply ((hTvec_meas.prodMk hξvec_meas) hE_pair_meas)]
          congr 1; ext ω; simp [and_comm]
        rw [hLHS_map, MarkedCPBoundedHelpers.restrict_map_pair_eq_prod P rate N T ξ hTmeas hξmeas hNlaw harrival hcross t n']
        -- Identify (P.restrict {N t = n'}).map Tvec via Kyprianou.exercise2_2_AllPartsCh02V6 (Part i)
        have hex22 := (Kyprianou.exercise2_2_AllPartsCh02V6 P rate hrate N T hTmeas hNlaw hNlevy harrival).1 t ht n' hn'
        have hTlaw : (P.restrict {ω | N t ω = n'}).map Tvec =
            (P {ω | N t ω = n'} * ENNReal.ofReal ((Nat.factorial n' : ℝ) / ((t : ℝ) ^ n'))) •
              (volume.restrict (MarkedCPBoundedHelpers.closedSimplex n' t)) := by
          ext B hB
          rw [Measure.map_apply hTvec_meas hB, Measure.restrict_apply (hTvec_meas hB)]
          have hsetB : Tvec ⁻¹' B ∩ {ω | N t ω = n'} = {ω | N t ω = n' ∧ Tvec ω ∈ B} := by
            ext ω; simp [and_comm]
          rw [hsetB, hex22 B hB]
          simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hB]
          rfl
        -- Identify P.map ξvec = Measure.pi (fun _ => F)
        have hξlaw : P.map ξvec = Measure.pi (fun _ : Fin n' => F) := by
          have hpre : iIndepFun (fun j : Fin n' => ξ (j.val + 1)) P :=
            hIID.precomp (fun a b h => Fin.ext (Nat.succ.inj h))
          have hmap := (iIndepFun_iff_map_fun_eq_pi_map
            (fun j : Fin n' => (hξmeas (j.val + 1)).aemeasurable)).mp hpre
          simpa only [ξvec, hmarklaw] using hmap
        rw [hTlaw, hξlaw, Measure.prod_smul_left, Measure.smul_apply, smul_eq_mul]
        -- Use permutation symmetry of E_pair to replace closedSimplex by [0, t]^n'
        have hEsymm : ∀ (σ : Equiv.Perm (Fin n')) (v y : Fin n' → ℝ), (v ∘ σ, y ∘ σ) ∈ E_pair ↔ (v, y) ∈ E_pair := by
          intro σ v y
          simp only [E_pair, Set.mem_preimage, E_pi, Set.mem_setOf_eq, e]
          refine forall_congr' fun i => ?_
          have hcard : (Finset.univ.filter (fun j : Fin n' => (v (σ j), y (σ j)) ∈ A i)).card =
              (Finset.univ.filter (fun j : Fin n' => (v j, y j) ∈ A i)).card := by
            refine Finset.card_bij (fun j _ => σ j) ?_ ?_ ?_
            · intro j hj; simpa using hj
            · intro a _ b _ h; exact σ.injective h
            · intro b hb
              refine ⟨σ.symm b, ?_, σ.apply_symm_apply b⟩
              simpa using hb
          change (Finset.univ.filter (fun j : Fin n' => (v (σ j), y (σ j)) ∈ A i)).card = k i ↔
            (Finset.univ.filter (fun j : Fin n' => (v j, y j) ∈ A i)).card = k i
          rw [hcard]
        have hsym := MarkedCPBoundedHelpers.symm_simplex_prod_eq n' t F E_pair hE_pair_meas hEsymm
        -- Relate (t^n')⁻¹ • (volume.restrict Q).prod (Measure.pi F) to Measure.pi ρ
        have htn_pos : (0 : ℝ) < (t : ℝ) ^ n' := pow_pos ht n'
        have hcoef : ENNReal.ofReal ((Nat.factorial n' : ℝ) / ((t : ℝ) ^ n')) =
            (ENNReal.ofReal ((t : ℝ) ^ n'))⁻¹ * (Nat.factorial n' : ℝ≥0∞) := by
          rw [div_eq_mul_inv, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_inv_of_pos htn_pos,
            ENNReal.ofReal_natCast, mul_comm]
        rw [hcoef, mul_assoc, mul_assoc, hsym]
        congr 1
        let μU : Measure ℝ := (ENNReal.ofReal (t : ℝ))⁻¹ • (volume.restrict (Set.Icc (0 : ℝ) (t : ℝ)))
        have hpiU : Measure.pi (fun _ : Fin n' => μU) =
            (ENNReal.ofReal ((t : ℝ) ^ n'))⁻¹ •
              (volume.restrict (Set.univ.pi (fun _ : Fin n' => Set.Icc (0 : ℝ) (t : ℝ)))) := by
          refine Measure.pi_eq fun s hs => ?_
          simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (MeasurableSet.univ_pi hs)]
          have hinter : Set.univ.pi s ∩ Set.univ.pi (fun _ : Fin n' => Set.Icc (0 : ℝ) (t : ℝ)) =
              Set.univ.pi (fun i => s i ∩ Set.Icc (0 : ℝ) (t : ℝ)) := by
            ext x; simp only [Set.mem_inter_iff, Set.mem_univ_pi, forall_and]
          rw [hinter, volume_pi, Measure.pi_pi]
          simp_rw [μU, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (hs _)]
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          congr 1
          rw [← ENNReal.inv_pow, ← ENNReal.ofReal_pow t.coe_nonneg]
        have hmp_zip := MarkedCPBoundedHelpers.measurePreserving_zipEquiv n' μU F
        have hE_eq := hmp_zip.measure_preimage hE_pi_meas.nullMeasurableSet
        rw [hpiU, Measure.prod_smul_left, Measure.smul_apply, smul_eq_mul] at hE_eq
        exact hE_eq
    -- Substitute hslice and pi_measure_counts_eq, then evaluate the tsum
    simp_rw [hslice, MarkedCPBoundedHelpers.pi_measure_counts_eq m _ ρ A hAmeas hAdisj k]
    let K : ℕ := ∑ i : Fin m, k i
    let lam : ℝ := (rate : ℝ) * (t : ℝ)
    let q0 : ℝ := (ρ (⋃ i : Fin m, A i)ᶜ).toReal
    let p : Fin m → ℝ := fun i => (ρ (A i)).toReal
    have hq0_nn : 0 ≤ q0 := ENNReal.toReal_nonneg
    have hp_nn : ∀ i : Fin m, 0 ≤ p i := fun _ => ENNReal.toReal_nonneg
    have hlam_nn : 0 ≤ lam := mul_nonneg rate.coe_nonneg t.coe_nonneg
    have hq0_eq : ρ (⋃ i : Fin m, A i)ᶜ = ENNReal.ofReal q0 :=
      (ENNReal.ofReal_toReal (measure_ne_top ρ _)).symm
    have hp_eq : ∀ i : Fin m, ρ (A i) = ENNReal.ofReal (p i) := fun i =>
      (ENNReal.ofReal_toReal (measure_ne_top ρ _)).symm
    have hsum_pq : q0 + ∑ i : Fin m, p i = 1 := by
      have htot : ρ (⋃ i : Fin m, A i)ᶜ + ρ (⋃ i : Fin m, A i) = 1 := by
        rw [add_comm, measure_add_measure_compl (MeasurableSet.iUnion hAmeas), measure_univ]
      rw [measure_iUnion hAdisj hAmeas, tsum_fintype] at htot
      have htot_real := congrArg ENNReal.toReal htot
      rw [ENNReal.toReal_add (measure_ne_top ρ _)
        (ENNReal.sum_lt_top.mpr (fun i _ => measure_lt_top ρ _)).ne,
        ENNReal.toReal_sum (fun i _ => measure_ne_top ρ _), ENNReal.toReal_one] at htot_real
      exact htot_real
    -- Shift tsum from n : ℕ to r = n - K
    have hshift : (∑' n : ℕ, P {ω | N t ω = n} *
        if K ≤ n then
          ENNReal.ofReal ((Nat.factorial n : ℝ) /
            ((Nat.factorial (n - K) : ℝ) * ∏ i : Fin m, (Nat.factorial (k i) : ℝ))) *
            (ρ (⋃ i : Fin m, A i)ᶜ) ^ (n - K) *
            ∏ i : Fin m, (ρ (A i)) ^ (k i)
        else 0) =
      ∑' r : ℕ, P {ω | N t ω = K + r} *
        (ENNReal.ofReal ((Nat.factorial (K + r) : ℝ) /
          ((Nat.factorial r : ℝ) * ∏ i : Fin m, (Nat.factorial (k i) : ℝ))) *
          (ρ (⋃ i : Fin m, A i)ᶜ) ^ r *
          ∏ i : Fin m, (ρ (A i)) ^ (k i)) := by
      rw [← Summable.tsum_add_tsum_compl (s := {n : ℕ | K ≤ n}) ENNReal.summable ENNReal.summable]
      have hzero : (∑' n : (({n : ℕ | K ≤ n} : Set ℕ)ᶜ : Set ℕ),
          P {ω | N t ω = n.1} *
            if K ≤ n.1 then
              ENNReal.ofReal ((Nat.factorial n.1 : ℝ) /
                ((Nat.factorial (n.1 - K) : ℝ) * ∏ i : Fin m, (Nat.factorial (k i) : ℝ))) *
                (ρ (⋃ i : Fin m, A i)ᶜ) ^ (n.1 - K) *
                ∏ i : Fin m, (ρ (A i)) ^ (k i)
            else 0) = 0 := by
        refine ENNReal.tsum_eq_zero.mpr fun n => ?_
        have hnot : ¬ K ≤ n.1 := n.2
        rw [if_neg hnot, mul_zero]
      rw [hzero, add_zero]
      let eShift : ℕ ≃ ({n : ℕ | K ≤ n} : Set ℕ) :=
        { toFun := fun r => ⟨K + r, Nat.le_add_right K r⟩
          invFun := fun n => n.1 - K
          left_inv := fun r => Nat.add_sub_cancel_left K r
          right_inv := fun n => Subtype.ext (Nat.add_sub_of_le n.2) }
      rw [← eShift.tsum_eq]
      refine tsum_congr fun r => ?_
      simp only [eShift, Equiv.coe_fn_mk, Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left]
    rw [hshift]
    -- Simplify each r-term by cancelling (K + r)!
    have hr_term : ∀ r : ℕ,
        P {ω | N t ω = K + r} *
          (ENNReal.ofReal ((Nat.factorial (K + r) : ℝ) /
            ((Nat.factorial r : ℝ) * ∏ i : Fin m, (Nat.factorial (k i) : ℝ))) *
            (ρ (⋃ i : Fin m, A i)ᶜ) ^ r *
            ∏ i : Fin m, (ρ (A i)) ^ (k i)) =
        ENNReal.ofReal (Real.exp (-lam) * (∏ i : Fin m, (lam * p i) ^ (k i) / (Nat.factorial (k i) : ℝ))) *
          ENNReal.ofReal ((lam * q0) ^ r / (Nat.factorial r : ℝ)) := by
      intro r
      have hPN : P {ω | N t ω = K + r} =
          ENNReal.ofReal (Real.exp (-lam) * lam ^ (K + r) / (Nat.factorial (K + r) : ℝ)) := by
        have hpre : {ω | N t ω = K + r} = (N t) ⁻¹' {K + r} := rfl
        rw [hpre, ← Measure.map_apply_of_aemeasurable hN_ae (measurableSet_singleton _), hNlaw t,
          MarkedCPBoundedHelpers.poissonMeasure_singleton_eq]
        push_cast [lam]; rfl
      rw [hPN, hq0_eq]
      simp_rw [hp_eq]
      rw [← ENNReal.ofReal_pow hq0_nn]
      have hprod_p : (∏ i : Fin m, (ENNReal.ofReal (p i)) ^ (k i)) =
          ENNReal.ofReal (∏ i : Fin m, (p i) ^ (k i)) := by
        simp_rw [← ENNReal.ofReal_pow (hp_nn _)]
        rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => pow_nonneg (hp_nn i) (k i))]
      rw [hprod_p]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by
          refine mul_nonneg (Real.exp_nonneg _) (Finset.prod_nonneg fun i _ => by positivity))]
      congr 1
      have hfactKr : (Nat.factorial (K + r) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hfactr : (Nat.factorial r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hfactk : (∏ i : Fin m, (Nat.factorial (k i) : ℝ)) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        exact fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k i))
      have hlamK : lam ^ K = ∏ i : Fin m, lam ^ (k i) := by
        dsimp [K]; rw [Finset.prod_pow_eq_pow_sum]
      have hprod_split : (∏ i : Fin m, (lam * p i) ^ (k i) / (Nat.factorial (k i) : ℝ)) =
          (lam ^ K * ∏ i : Fin m, (p i) ^ (k i)) / (∏ i : Fin m, (Nat.factorial (k i) : ℝ)) := by
        rw [Finset.prod_div_distrib, hlamK, ← Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_congr rfl fun i _ => mul_pow lam (p i) (k i)
      rw [hprod_split, pow_add, mul_pow lam q0 r]
      field_simp [hfactKr, hfactr, hfactk]
    simp_rw [hr_term]
    rw [ENNReal.tsum_mul_left]
    -- Sum ∑' r, ENNReal.ofReal ((lam * q0)^r / r!) = ENNReal.ofReal (Real.exp (lam * q0))
    have hexp_sum : (∑' r : ℕ, ENNReal.ofReal ((lam * q0) ^ r / (Nat.factorial r : ℝ))) =
        ENNReal.ofReal (Real.exp (lam * q0)) := by
      have hhas : HasSum (fun r : ℕ => (lam * q0) ^ r / (Nat.factorial r : ℝ)) (Real.exp (lam * q0)) := by
        rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
        have hs : Summable (fun r : ℕ => ((Nat.factorial r : ℝ)⁻¹ • (lam * q0) ^ r)) :=
          NormedSpace.expSeries_summable' (lam * q0)
        have heq : (fun r : ℕ => (lam * q0) ^ r / (Nat.factorial r : ℝ)) =
            (fun r : ℕ => ((Nat.factorial r : ℝ)⁻¹ • (lam * q0) ^ r)) := by
          ext r; rw [smul_eq_mul, div_eq_inv_mul]
        rw [heq]
        exact hs.hasSum
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun r => by positivity) hhas.summable, hhas.tsum_eq]
    rw [hexp_sum, ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg _) (Finset.prod_nonneg fun i _ => by positivity))]
    -- Rewrite RHS product of Poisson point masses
    have hrhs_term : ∀ i : Fin m,
        ProbabilityTheory.poissonMeasure (intensity (A i)).toNNReal {k i} =
          ENNReal.ofReal (Real.exp (-(lam * p i)) * (lam * p i) ^ (k i) / (Nat.factorial (k i) : ℝ)) := by
      intro i
      rw [MarkedCPBoundedHelpers.poissonMeasure_singleton_eq]
      have hint_eq : ((intensity (A i)).toNNReal : ℝ) = lam * p i := by
        have hmul := MarkedCPBoundedHelpers.intensity_eq_mul_rho rate t ht F (hAmeas i) (hAsub i)
        change (((volume.restrict (Set.Ici (0 : ℝ))).prod ((rate : ℝ≥0∞) • F)) (A i)).toReal = lam * p i
        rw [hmul, ENNReal.toReal_mul, ENNReal.coe_toReal]
        push_cast [lam, p]; rfl
      rw [hint_eq]
    simp_rw [hrhs_term]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
    congr 1
    have hexp_comb : Real.exp (-lam) * Real.exp (lam * q0) = ∏ i : Fin m, Real.exp (-(lam * p i)) := by
      rw [← Real.exp_add, ← Real.exp_sum]
      congr 1
      have : -lam + lam * q0 = -(lam * (1 - q0)) := by ring
      rw [this, show (1 - q0 : ℝ) = ∑ i : Fin m, p i by linarith [hsum_pq],
        Finset.mul_sum, Finset.sum_neg_distrib]
    calc Real.exp (-lam) * (∏ i : Fin m, (lam * p i) ^ (k i) / (Nat.factorial (k i) : ℝ)) * Real.exp (lam * q0)
        = (Real.exp (-lam) * Real.exp (lam * q0)) *
            ∏ i : Fin m, (lam * p i) ^ (k i) / (Nat.factorial (k i) : ℝ) := by ring
      _ = (∏ i : Fin m, Real.exp (-(lam * p i))) *
            ∏ i : Fin m, (lam * p i) ^ (k i) / (Nat.factorial (k i) : ℝ) := by rw [hexp_comb]
      _ = ∏ i : Fin m, (Real.exp (-(lam * p i)) * ((lam * p i) ^ (k i) / (Nat.factorial (k i) : ℝ))) := by
            rw [Finset.prod_mul_distrib]
      _ = ∏ i : Fin m, (Real.exp (-(lam * p i)) * (lam * p i) ^ (k i) / (Nat.factorial (k i) : ℝ)) := by
            refine Finset.prod_congr rfl fun i _ => by ring
  -- Step 2: Deduce P.map (fun ω i => X i ω) = Measure.pi ν on all measurable sets
  let natEmbed : (Fin m → ℕ) → (Fin m → ℝ≥0∞) := fun k i => (k i : ℝ≥0∞)
  have hnat_inj : Function.Injective natEmbed := fun k₁ k₂ h => by
    ext i; exact (Nat.cast_inj (R := ℝ≥0∞)).mp (congrFun h i)
  let R : Set (Fin m → ℝ≥0∞) := Set.range natEmbed
  have hR_count : R.Countable := Set.countable_range natEmbed
  have hR_meas : MeasurableSet R := hR_count.measurableSet
  -- Both measures put zero mass outside R
  have hLHS_compl : (P.map (fun ω i => X i ω)) Rᶜ = 0 := by
    rw [Measure.map_apply (measurable_pi_lambda _ hXmeas) hR_meas.compl]
    have hsub : (fun ω i => X i ω) ⁻¹' Rᶜ ⊆
        {ω | ¬ ∀ (n : ℕ), 0 < n → ∀ (s : ℝ≥0), (n ≤ N s ω ↔ T n ω ≤ s)} := by
      intro ω hmem
      by_contra ha
      simp only [Set.mem_setOf_eq, not_not] at ha
      apply hmem
      refine ⟨fun i => (Finset.univ.filter (fun j : Fin (N t ω) =>
          ((T (j.val + 1) ω : ℝ), ξ (j.val + 1) ω) ∈ A i)).card, ?_⟩
      ext i
      change _ = (Measure.sum (fun j : ℕ => Measure.dirac ((T (j + 1) ω : ℝ), ξ (j + 1) ω))) (A i)
      rw [Measure.sum_apply _ (hAmeas i)]
      have hvan : ∀ j : ℕ, N t ω ≤ j → Measure.dirac ((T (j + 1) ω : ℝ), ξ (j + 1) ω) (A i) = 0 := by
        intro j hj
        rw [Measure.dirac_apply' _ (hAmeas i), Set.indicator_of_notMem]
        intro hmemA
        have hle_t : T (j + 1) ω ≤ t := by exact_mod_cast (hAsub i hmemA).1.2
        have hjN : j + 1 ≤ N t ω := (ha (j + 1) (Nat.succ_pos j) t).mpr hle_t
        omega
      rw [tsum_eq_sum (s := Finset.range (N t ω)) (fun j hj => hvan j (by simp at hj; omega)),
        ← Fin.sum_univ_eq_sum_range _ (N t ω)]
      have hterm : ∀ j : Fin (N t ω),
          Measure.dirac ((T (j.val + 1) ω : ℝ), ξ (j.val + 1) ω) (A i) =
            if ((T (j.val + 1) ω : ℝ), ξ (j.val + 1) ω) ∈ A i then (1 : ℝ≥0∞) else 0 := fun j => by
        rw [Measure.dirac_apply' _ (hAmeas i)]
        by_cases hm : ((T (j.val + 1) ω : ℝ), ξ (j.val + 1) ω) ∈ A i
        · simp [Set.indicator_of_mem hm, hm]
        · simp [Set.indicator_of_notMem hm, hm]
      simp_rw [hterm, Finset.sum_boole]
      rfl
    exact measure_mono_null hsub harrival
  have hRHS_compl : (Measure.pi ν) Rᶜ = 0 := by
    have hR_eq : R = Set.univ.pi (fun _ : Fin m => Set.range (Nat.cast : ℕ → ℝ≥0∞)) := by
      ext y
      simp only [R, natEmbed, Set.mem_range, Set.mem_univ_pi]
      constructor
      · rintro ⟨k, rfl⟩ i; exact ⟨k i, rfl⟩
      · intro h; choose k hk using h; exact ⟨k, funext hk⟩
    rw [hR_eq, prob_compl_eq_one_sub (MeasurableSet.univ_pi fun _ => (Set.countable_range _).measurableSet),
      Measure.pi_pi]
    have hone : ∀ i : Fin m, ν i (Set.range (Nat.cast : ℕ → ℝ≥0∞)) = 1 := by
      intro i
      rw [Measure.map_apply measurable_from_top (Set.countable_range _).measurableSet]
      have : (Nat.cast : ℕ → ℝ≥0∞) ⁻¹' Set.range (Nat.cast : ℕ → ℝ≥0∞) = Set.univ := by
        ext n; simp
      rw [this, measure_univ]
    simp [hone]
  -- Both measures agree on every singleton {natEmbed k}
  have hsing : ∀ k : Fin m → ℕ,
      (P.map (fun ω i => X i ω)) {natEmbed k} = (Measure.pi ν) {natEmbed k} := by
    intro k
    rw [Measure.map_apply (measurable_pi_lambda _ hXmeas) (measurableSet_singleton _)]
    have hpre : (fun ω i => X i ω) ⁻¹' {natEmbed k} = {ω | ∀ i : Fin m, X i ω = (k i : ℝ≥0∞)} := by
      ext ω; simp [natEmbed, funext_iff]
    rw [hpre, hjoint_pmf k]
    have hsing_pi : ({natEmbed k} : Set (Fin m → ℝ≥0∞)) = Set.univ.pi (fun i => {(k i : ℝ≥0∞)}) := by
      ext y; simp [natEmbed, funext_iff]
    rw [hsing_pi, Measure.pi_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Measure.map_apply measurable_from_top (measurableSet_singleton _)]
    have hnat_pre : (Nat.cast : ℕ → ℝ≥0∞) ⁻¹' {(k i : ℝ≥0∞)} = {k i} := by
      ext n; simp
    rw [hnat_pre]
  -- Conclude equality on every measurable set S via countable decomposition S ∩ R
  ext S hS
  have hsplit_meas : ∀ (M : Measure (Fin m → ℝ≥0∞)), M Rᶜ = 0 →
      M S = ∑' k : Fin m → ℕ, if natEmbed k ∈ S then M {natEmbed k} else 0 := by
    intro M hM0
    have h1 : M S = M (S ∩ R) := by
      rw [← measure_inter_add_sdiff S hR_meas,
        measure_mono_null (Set.sdiff_subset_compl S R) hM0, add_zero]
    rw [h1]
    have hSR : S ∩ R = ⋃ k : Fin m → ℕ, if natEmbed k ∈ S then {natEmbed k} else ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_iUnion, R, Set.mem_range]
      constructor
      · rintro ⟨hyS, k, rfl⟩
        exact ⟨k, by rw [if_pos hyS]; rfl⟩
      · rintro ⟨k, hk⟩
        by_cases hmem : natEmbed k ∈ S
        · rw [if_pos hmem] at hk; rw [Set.mem_singleton_iff.mp hk]; exact ⟨hmem, k, rfl⟩
        · rw [if_neg hmem] at hk; exact absurd hk (Set.notMem_empty y)
    rw [hSR, measure_iUnion]
    · refine tsum_congr fun k => ?_
      split_ifs <;> simp
    · intro k₁ k₂ hne
      change Disjoint (if natEmbed k₁ ∈ S then {natEmbed k₁} else ∅)
        (if natEmbed k₂ ∈ S then {natEmbed k₂} else ∅)
      split_ifs
      · exact Set.disjoint_singleton.mpr fun heq => hne (hnat_inj heq)
      · exact Set.disjoint_empty _
      · exact Set.empty_disjoint _
      · exact Set.empty_disjoint _
    · intro k
      split_ifs
      · exact measurableSet_singleton _
      · exact MeasurableSet.empty
  rw [hsplit_meas _ hLHS_compl, hsplit_meas _ hRHS_compl]
  refine tsum_congr fun k => ?_
  split_ifs
  · exact hsing k
  · rfl
