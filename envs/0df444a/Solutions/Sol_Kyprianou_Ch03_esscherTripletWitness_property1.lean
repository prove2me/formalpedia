-- Prove2me | solution 1 for Kyprianou.Ch03.esscherTripletWitness_property1
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T17:50:42.474644+00:00
-- url     : https://prove2.me/submissions/f05b6b9b-75b3-49a1-a02e-e3059abee445

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace EsscherTripletWitnessProp1Aux

private lemma measurable_X_F_le
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal mΩ)
    (X : NNReal → Omega → ℝ)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    {s t : NNReal} (hst : s ≤ t) :
    Measurable[F t] (X s) := by
  rw [measurable_iff_comap_le, hNatural t]
  refine le_trans ?_ le_sup_left
  exact le_iSup₂_of_le s hst le_rfl

private lemma measurable_X
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal mΩ)
    (X : NNReal → Omega → ℝ)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F) (t : NNReal) :
    Measurable (X t) :=
  (measurable_X_F_le P F X hNatural (le_refl t)).mono (F.le t) le_rfl

private lemma fin_sum_sub_telescope {n : ℕ} (f : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    have hprev := ih (fun k : Fin (m + 1) => f k.castSucc)
    have hcast : ∀ i : Fin m, (i.castSucc : Fin (m + 1)).succ = i.succ.castSucc := fun _ => rfl
    have hcast2 : ∀ i : Fin m, (i.castSucc : Fin (m + 1)).castSucc = i.castSucc.castSucc := fun _ => rfl
    have hsum : ∑ x : Fin m, (f x.castSucc.succ - f x.castSucc.castSucc) =
        f (Fin.last m).castSucc - f 0 := by
      simpa only [hcast, hcast2, Fin.castSucc_zero] using hprev
    rw [hsum]
    have hlast_succ : (Fin.last m).succ = Fin.last (m + 1) := rfl
    have hlast_cast : (Fin.last m).castSucc = (Fin.last m).castSucc := rfl
    rw [hlast_succ]
    ring

end EsscherTripletWitnessProp1Aux

open Kyprianou.Ch03 EsscherTripletWitnessProp1Aux

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp ((((t : Real) : Complex)) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : Real)
    (hBeta : IntegrableOn
      (fun x : Real => Real.exp (beta * x))
      {x : Real | 1 <= abs x} T.levyMeasure)
    (hEsscher : forall (t : NNReal) (A : Set Omega),
      MeasurableSet[F t] A ->
      Q A =
        ENNReal.ofReal
          (∫ omega, Set.indicator A
            (fun omega : Omega =>
              esscherDensity X beta
                (Real.log
                  (∫ eta, Real.exp (beta * X 1 eta) ∂P))
                t omega) omega ∂P)) :
    forall (Tbeta : ProbabilityTheory.LevyKhintchineTriple),
      (Tbeta.drift =
        T.drift + beta * (T.gaussianVariance : Real) +
          ∫ x in {x : Real | abs x < 1},
            (Real.exp (beta * x) - 1) * x ∂T.levyMeasure ∧ Tbeta.gaussianVariance = T.gaussianVariance ∧ Tbeta.levyMeasure =
        T.levyMeasure.withDensity
          (fun x : Real => ENNReal.ofReal (Real.exp (beta * x)))) ->
      ProbabilityTheory.IsLevyProcess X Q := by
  let _ := T
  let _ := hLK
  let _ := hBeta
  intro Tbeta _
  set k : ℝ := Real.log (∫ eta, Real.exp (beta * X 1 eta) ∂P)
  have hX_measF : ∀ {s t : NNReal}, s ≤ t → Measurable[F t] (X s) :=
    fun hst => EsscherTripletWitnessProp1Aux.measurable_X_F_le P F X hNatural hst
  have hX_meas : ∀ t : NNReal, Measurable (X t) :=
    EsscherTripletWitnessProp1Aux.measurable_X P F X hNatural
  -- Step 1: Integrability and lintegral representation of Q on F t
  have hDens_int_eq_one : ∀ t : NNReal,
      (∫ omega, esscherDensity X beta k t omega ∂P) = 1 := by
    intro t
    have h1 := hEsscher t Set.univ MeasurableSet.univ
    simp only [measure_univ, Set.indicator_univ] at h1
    have hpos : 0 ≤ ∫ omega, esscherDensity X beta k t omega ∂P :=
      integral_nonneg fun omega => Real.exp_nonneg _
    have hofReal : ENNReal.ofReal (∫ omega, esscherDensity X beta k t omega ∂P) =
        ENNReal.ofReal 1 := by simpa using h1.symm
    exact (ENNReal.ofReal_eq_ofReal_iff hpos zero_le_one).mp hofReal
  have hDens_integrable : ∀ t : NNReal,
      Integrable (esscherDensity X beta k t) P := by
    intro t
    by_contra hnot
    have h0 : (∫ omega, esscherDensity X beta k t omega ∂P) = 0 := integral_undef hnot
    linarith [hDens_int_eq_one t]
  let Z : NNReal → Omega → ℝ≥0∞ := fun t omega =>
    ENNReal.ofReal (esscherDensity X beta k t omega)
  have hZ_meas : ∀ t : NNReal, Measurable (Z t) := fun t => by
    dsimp only [Z, esscherDensity]
    have := hX_meas t
    fun_prop
  have hQ_eq_lintegral : ∀ (t : NNReal) (A : Set Omega),
      MeasurableSet[F t] A →
      Q A = ∫⁻ omega, A.indicator (Z t) omega ∂P := by
    intro t A hA
    have hA_m : MeasurableSet A := F.le t A hA
    rw [hEsscher t A hA, integral_indicator hA_m,
      ofReal_integral_eq_lintegral_ofReal (hDens_integrable t).integrableOn
        (ae_of_all _ fun _ => Real.exp_nonneg _),
      ← lintegral_indicator hA_m]
  have hZ_unit : ∀ t : NNReal, (∫⁻ omega, Z t omega ∂P) = 1 := by
    intro t
    have h := hQ_eq_lintegral t Set.univ MeasurableSet.univ
    simpa [measure_univ] using h.symm
  -- Step 2: Helper for a single increment under Q
  let W_inc : ℝ → ℝ → ℝ≥0∞ := fun d x =>
    ENNReal.ofReal (Real.exp (beta * x - k * d))
  have hW_meas : ∀ d : ℝ, Measurable (W_inc d) := fun d => by
    dsimp only [W_inc]
    fun_prop
  have hinc_meas : ∀ s t : NNReal, Measurable (ProbabilityTheory.increment X s t) := fun s t =>
    (hX_meas t).sub (hX_meas s)
  have hinc_measF : ∀ {s t T' : NNReal}, s ≤ T' → t ≤ T' →
      Measurable[F T'] (ProbabilityTheory.increment X s t) := fun hs ht =>
    (hX_measF ht).sub (hX_measF hs)
  have hinc_indep_pair : ∀ (s t : NNReal), s ≤ t →
      IndepFun (X s) (ProbabilityTheory.increment X s t) P := by
    intro s t hst
    let tp : Fin 3 → NNReal := ![0, s, t]
    have htp : Monotone tp := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [tp]
    have hind := (hX.indep_increments 2 tp htp).indepFun (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
    have h0 : ProbabilityTheory.increment X (tp (0 : Fin 2).castSucc) (tp (0 : Fin 2).succ) = X s := by
      ext omega
      simp [ProbabilityTheory.increment, tp, hX.start_zero]
    have h1 : ProbabilityTheory.increment X (tp (1 : Fin 2).castSucc) (tp (1 : Fin 2).succ) =
        ProbabilityTheory.increment X s t := by
      ext omega
      simp [ProbabilityTheory.increment, tp]
    rwa [h0, h1] at hind
  have hQ_inc_preimage : ∀ {s t : NNReal} (hst : s ≤ t) {B : Set ℝ} (hB : MeasurableSet B),
      Q (ProbabilityTheory.increment X s t ⁻¹' B) =
        ∫⁻ omega, (B.indicator (W_inc ((t : ℝ) - (s : ℝ)))) (ProbabilityTheory.increment X s t omega) ∂P := by
    intro s t hst B hB
    have hA_F : MeasurableSet[F t] (ProbabilityTheory.increment X s t ⁻¹' B) :=
      hinc_measF hst (le_refl t) hB
    rw [hQ_eq_lintegral t _ hA_F]
    have hfac : ∀ omega,
        (ProbabilityTheory.increment X s t ⁻¹' B).indicator (Z t) omega =
          Z s omega * B.indicator (W_inc ((t : ℝ) - (s : ℝ))) (ProbabilityTheory.increment X s t omega) := by
      intro omega
      by_cases hmem : ProbabilityTheory.increment X s t omega ∈ B
      · have hmem' : omega ∈ ProbabilityTheory.increment X s t ⁻¹' B := hmem
        rw [Set.indicator_of_mem hmem', Set.indicator_of_mem hmem]
        dsimp only [Z, W_inc, esscherDensity, ProbabilityTheory.increment]
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        congr 2
        ring
      · have hmem' : omega ∉ ProbabilityTheory.increment X s t ⁻¹' B := hmem
        rw [Set.indicator_of_notMem hmem', Set.indicator_of_notMem hmem, mul_zero]
    simp_rw [hfac]
    have hind_pair := hinc_indep_pair s t hst
    have hg1 : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x - k * (s : ℝ)))) := by
      fun_prop
    have hg2 : Measurable (B.indicator (W_inc ((t : ℝ) - (s : ℝ)))) :=
      (hW_meas _).indicator hB
    have hind_fg : IndepFun (Z s)
        (fun omega => B.indicator (W_inc ((t : ℝ) - (s : ℝ))) (ProbabilityTheory.increment X s t omega)) P :=
      hind_pair.comp hg1 hg2
    have hmul := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
      (hZ_meas s).aemeasurable (hg2.comp (hinc_meas s t)).aemeasurable hind_fg
    dsimp only [Function.comp_apply] at hmul
    rw [hmul, hZ_unit s, one_mul]
  have hW_inc_unit : ∀ {s t : NNReal} (hst : s ≤ t),
      (∫⁻ omega, W_inc ((t : ℝ) - (s : ℝ)) (ProbabilityTheory.increment X s t omega) ∂P) = 1 := by
    intro s t hst
    have h := hQ_inc_preimage hst MeasurableSet.univ
    simpa [Set.preimage_univ, Set.indicator_univ, measure_univ] using h.symm
  -- Assemble all four fields of IsLevyProcess X Q
  refine ⟨hX.start_zero, ?_, ?_, ?_⟩
  · -- Field 2: HasIndependentIncrements X Q
    intro n t ht
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S B hB
    let t' : Fin (n + 2) → NNReal := Fin.cons 0 t
    have ht' : Monotone t' := by
      intro i j hij
      cases i using Fin.cases with
      | zero => simp [t']
      | succ i' =>
        cases j using Fin.cases with
        | zero => exact absurd hij (not_le.mpr (Fin.succ_pos i'))
        | succ j' =>
          simp only [t', Fin.cons_succ]
          exact ht (Fin.succ_le_succ_iff.mp hij)
    let V : Fin (n + 1) → Omega → ℝ := fun j =>
      ProbabilityTheory.increment X (t' j.castSucc) (t' j.succ)
    have hV_indep : iIndepFun V P := hX.indep_increments (n + 1) t' ht'
    have hV_zero : V 0 = X (t 0) := by
      ext omega
      simp [V, t', ProbabilityTheory.increment, hX.start_zero]
    have hV_succ : ∀ i : Fin n, V i.succ = ProbabilityTheory.increment X (t i.castSucc) (t i.succ) := by
      intro i
      ext omega
      simp [V, t', ProbabilityTheory.increment]
    let g : Fin (n + 1) → ℝ → ℝ≥0∞ :=
      Fin.cases
        (fun x => ENNReal.ofReal (Real.exp (beta * x - k * (t 0 : ℝ))))
        (fun i =>
          if i ∈ S then
            (B i).indicator (W_inc ((t i.succ : ℝ) - (t i.castSucc : ℝ)))
          else
            W_inc ((t i.succ : ℝ) - (t i.castSucc : ℝ)))
    have hg_meas : ∀ j : Fin (n + 1), Measurable (g j) := by
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · dsimp only [g, Fin.cases_zero]
        fun_prop
      · dsimp only [g, Fin.cases_succ]
        split_ifs with hi
        · exact (hW_meas _).indicator (hB i hi)
        · exact hW_meas _
    have hV_meas : ∀ j : Fin (n + 1), Measurable (V j) := fun j =>
      hinc_meas (t' j.castSucc) (t' j.succ)
    have hcomp_indep : iIndepFun (fun j => (g j) ∘ (V j)) P :=
      hV_indep.comp g hg_meas
    let T_end : NNReal := t (Fin.last n)
    have hA_F : MeasurableSet[F T_end]
        (⋂ i ∈ S, ProbabilityTheory.increment X (t i.castSucc) (t i.succ) ⁻¹' B i) := by
      refine MeasurableSet.biInter S.countable_toSet fun i hi => ?_
      have h1 : t i.castSucc ≤ T_end := ht (Fin.le_last _)
      have h2 : t i.succ ≤ T_end := ht (Fin.le_last _)
      exact hinc_measF h1 h2 (hB i hi)
    rw [hQ_eq_lintegral T_end _ hA_F]
    have hZ_factor : ∀ omega,
        Z T_end omega =
          Z (t 0) omega *
            ∏ i : Fin n, W_inc ((t i.succ : ℝ) - (t i.castSucc : ℝ))
              (ProbabilityTheory.increment X (t i.castSucc) (t i.succ) omega) := by
      intro omega
      dsimp only [Z, W_inc, esscherDensity, ProbabilityTheory.increment]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.exp_nonneg _),
        ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_sum, ← Real.exp_add]
      congr 2
      have htelX : ∑ i : Fin n, (X (t i.succ) omega - X (t i.castSucc) omega) =
          X T_end omega - X (t 0) omega :=
        EsscherTripletWitnessProp1Aux.fin_sum_sub_telescope (fun j => X (t j) omega)
      have htelt : ∑ i : Fin n, ((t i.succ : ℝ) - (t i.castSucc : ℝ)) =
          (T_end : ℝ) - (t 0 : ℝ) :=
        EsscherTripletWitnessProp1Aux.fin_sum_sub_telescope (fun j => (t j : ℝ))
      have hsum_eq :
          ∑ i : Fin n, (beta * (X (t i.succ) omega - X (t i.castSucc) omega) -
            k * ((t i.succ : ℝ) - (t i.castSucc : ℝ))) =
          beta * (X T_end omega - X (t 0) omega) - k * ((T_end : ℝ) - (t 0 : ℝ)) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, htelX, htelt]
      rw [hsum_eq]
      ring
    have hind_prod : ∀ omega,
        (⋂ i ∈ S, ProbabilityTheory.increment X (t i.castSucc) (t i.succ) ⁻¹' B i).indicator
            (Z T_end) omega =
          ∏ j : Fin (n + 1), g j (V j omega) := by
      intro omega
      rw [Fin.prod_univ_succ]
      have h0_eq : g 0 (V 0 omega) = Z (t 0) omega := by
        simp [g, hV_zero, Z, esscherDensity]
      rw [h0_eq]
      by_cases hmem : omega ∈ ⋂ i ∈ S, ProbabilityTheory.increment X (t i.castSucc) (t i.succ) ⁻¹' B i
      · rw [Set.indicator_of_mem hmem, hZ_factor omega]
        congr 1
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hV_succ i]
        dsimp only [g, Fin.cases_succ]
        split_ifs with hi
        · have himem : ProbabilityTheory.increment X (t i.castSucc) (t i.succ) omega ∈ B i := by
            have := Set.mem_iInter₂.mp hmem i hi
            exact this
          exact (Set.indicator_of_mem himem _).symm
        · rfl
      · rw [Set.indicator_of_notMem hmem]
        simp only [Set.mem_iInter, Set.mem_preimage, not_forall] at hmem
        rcases hmem with ⟨i₀, hi₀, hnotmem⟩
        have hzero : g i₀.succ (V i₀.succ omega) = 0 := by
          rw [hV_succ i₀]
          dsimp only [g, Fin.cases_succ]
          rw [if_pos hi₀]
          exact Set.indicator_of_notMem hnotmem _
        have hprod0 : (∏ i : Fin n, g i.succ (V i.succ omega)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i₀) hzero
        rw [hprod0, mul_zero]
    simp_rw [hind_prod]
    have hprod_int := lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
      (fun j => (g j) ∘ (V j)) hcomp_indep (fun j => (hg_meas j).comp (hV_meas j))
    dsimp only [Function.comp_apply] at hprod_int
    rw [hprod_int, Fin.prod_univ_succ]
    have h0_int : (∫⁻ omega, g 0 (V 0 omega) ∂P) = 1 := by
      have heq : (fun omega => g 0 (V 0 omega)) = Z (t 0) := by
        ext omega; simp [g, hV_zero, Z, esscherDensity]
      rw [heq, hZ_unit (t 0)]
    rw [h0_int, one_mul]
    rw [← Finset.prod_subset (Finset.subset_univ S)]
    · refine Finset.prod_congr rfl fun i hi => ?_
      have heq : (fun omega => g i.succ (V i.succ omega)) =
          fun omega => (B i).indicator (W_inc ((t i.succ : ℝ) - (t i.castSucc : ℝ)))
            (ProbabilityTheory.increment X (t i.castSucc) (t i.succ) omega) := by
        ext omega
        simp [g, hV_succ i, hi]
      rw [heq, ← hQ_inc_preimage (ht i.castSucc_le_succ) (hB i hi)]
    · intro i _ hi
      have heq : (fun omega => g i.succ (V i.succ omega)) =
          fun omega => W_inc ((t i.succ : ℝ) - (t i.castSucc : ℝ))
            (ProbabilityTheory.increment X (t i.castSucc) (t i.succ) omega) := by
        ext omega
        simp [g, hV_succ i, hi]
      rw [heq, hW_inc_unit (ht i.castSucc_le_succ)]
  · -- Field 3: HasStationaryIncrements X Q
    intro s h
    refine ⟨(hinc_meas s (s + h)).aemeasurable, (hinc_meas 0 h).aemeasurable, ?_⟩
    ext B hB
    rw [Measure.map_apply (hinc_meas s (s + h)) hB,
      Measure.map_apply (hinc_meas 0 h) hB,
      hQ_inc_preimage (le_self_add : s ≤ s + h) hB,
      hQ_inc_preimage (zero_le : (0 : NNReal) ≤ h) hB]
    have hd : ((s + h : NNReal) : ℝ) - (s : ℝ) = ((h : NNReal) : ℝ) - ((0 : NNReal) : ℝ) := by
      push_cast; ring
    rw [hd]
    have hg_meas : Measurable (B.indicator (W_inc ((h : ℝ) - ((0 : NNReal) : ℝ)))) :=
      (hW_meas _).indicator hB
    rw [← lintegral_map hg_meas (hinc_meas s (s + h)),
      (hX.stationary_increments s h).map_eq,
      lintegral_map hg_meas (hinc_meas 0 h)]
  · -- Field 4: cadlag_ae under Q (follows from P-completion of F 0)
    rw [ae_iff]
    have hP0 : P {omega : Omega | ¬ ProbabilityTheory.IsCadlag (fun t => X t omega)} = 0 :=
      ae_iff.mp hX.cadlag_ae
    rcases exists_measurable_superset_of_null hP0 with ⟨N, hsub, hN_meas, hPN⟩
    have hN_F0 : MeasurableSet[F 0] N := by
      have hle : MeasurableSpace.generateFrom
          {A : Set Omega | ∃ N' : Set Omega, MeasurableSet N' ∧ P N' = 0 ∧ A ⊆ N'} ≤ F 0 := by
        rw [hNatural 0]
        exact le_sup_right
      exact hle N (MeasurableSpace.measurableSet_generateFrom ⟨N, hN_meas, hPN, Subset.rfl⟩)
    have hQN : Q N = 0 := by
      rw [hEsscher 0 N hN_F0]
      have hzero_ae : Set.indicator N (esscherDensity X beta k 0) =ᵐ[P] (fun _ => (0 : ℝ)) := by
        have hN_ae : ∀ᵐ omega ∂P, omega ∉ N := by simpa [ae_iff] using hPN
        filter_upwards [hN_ae] with omega hnot
        simp [Set.indicator_of_notMem hnot]
      rw [integral_congr_ae hzero_ae, integral_zero, ENNReal.ofReal_zero]
    exact measure_mono_null hsub hQN
