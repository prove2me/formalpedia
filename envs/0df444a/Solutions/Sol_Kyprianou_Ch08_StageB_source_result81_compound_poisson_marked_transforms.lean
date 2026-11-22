-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_compound_poisson_marked_transforms
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T18:32:37.867032+00:00
-- url     : https://prove2.me/submissions/7c991006-51b8-47c5-98b5-078d4a2e31c2

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.Independence.Integration
import Theorems.Thm_levy_foundations_compoundPoissonDriverExists
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_jumpCount_measurable_public
import Theorems.Thm_levy_foundations_compoundPoissonJumpCountLaw
import Theorems.Thm_levy_foundations_compoundPoissonCharFun
import Theorems.Thm_AvramDividend_Classical_chat06_laplace_random_mark_sum_without_pgf_assumption

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem result81_driver_blocks_independent
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {J : Measure ℝ}
    (h : LevyFoundations.IsCompoundPoissonDriver τ Y r J P) :
    IndepFun (fun ω i => τ i ω) (fun ω i => Y i ω) P := by
  let m (k : ℕ ⊕ ℕ) := MeasurableSpace.comap (Sum.elim τ Y k) inferInstance
  have hm (k : ℕ ⊕ ℕ) : m k ≤ mΩ := by
    cases k with
    | inl i => exact (h.measurable_interarrival i).comap_le
    | inr i => exact (h.measurable_mark i).comap_le
  have hd : Disjoint (range (Sum.inl : ℕ → ℕ ⊕ ℕ)) (range (Sum.inr : ℕ → ℕ ⊕ ℕ)) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
    cases hj
  have hs := indep_iSup_of_disjoint hm h.indep.iIndep hd
  change Indep (MeasurableSpace.comap (fun ω (i : ℕ) => τ i ω) inferInstance)
    (MeasurableSpace.comap (fun ω (i : ℕ) => Y i ω) inferInstance) P
  apply indep_of_indep_of_le hs
  · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    apply iSup_le
    intro i
    rw [MeasurableSpace.comap_comp]
    exact le_iSup_of_le (Sum.inl i) (le_iSup_of_le ⟨i, rfl⟩ le_rfl)
  · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    apply iSup_le
    intro i
    rw [MeasurableSpace.comap_comp]
    exact le_iSup_of_le (Sum.inr i) (le_iSup_of_le ⟨i, rfl⟩ le_rfl)

private theorem result81_fixed_mark_product
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {τ Y : ℕ → Ω → ℝ}
    {r : ℝ≥0} {J : Measure ℝ} (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r J P)
    (β : ℝ) (k : ℕ) :
    (∫ ω, Real.exp (β * ∑ j ∈ Finset.range k, Y j ω) ∂P) =
      (∫ y, Real.exp (β * y) ∂J) ^ k := by
  let F (y : ℝ) := Real.exp (β * y)
  have hF : Measurable F := by fun_prop
  have hfin : iIndepFun (fun i : Fin k => fun ω => F (Y (i : ℕ) ω)) P := by
    simpa only [Function.comp_def, Function.comp_apply, Sum.elim_inr] using (((hd.indep.precomp (g := Sum.inr) Sum.inr_injective).precomp (g := @Fin.val k) Fin.val_injective).comp (fun _ => F) (fun _ => hF))
  have he (j : Fin k) : (∫ ω, F (Y j ω) ∂P) = (∫ y, F y ∂J) := by
    rw [← integral_map (hd.measurable_mark j).aemeasurable hF.aestronglyMeasurable,
      (hd.law_mark j).map_eq]
  simp_rw [Finset.mul_sum, Real.exp_sum, ← Fin.prod_univ_eq_prod_range]
  change (∫ ω, ∏ j : Fin k, F (Y j ω) ∂P) = _
  rw [hfin.integral_fun_prod_eq_prod_integral
    (fun j => (hF.comp (hd.measurable_mark j)).aestronglyMeasurable)]
  simpa only [he, F, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem solution
    (J : Measure ℝ) [IsProbabilityMeasure J] (hJ : ∀ᵐ y ∂J, y ≤ 0)
    (r : ℝ≥0) (hr : 0 < r) (t : ℝ≥0) :
    ∃ μ : ProbabilityMeasure ℝ,
      (∀ ξ : ℝ, charFun (μ : Measure ℝ) ξ =
        Complex.exp ((((r : ℝ) * (t : ℝ) : ℝ) : ℂ) * (charFun J ξ - 1))) ∧
      (∀ β : ℝ, 0 ≤ β → Integrable (fun x => Real.exp (β * x)) (μ : Measure ℝ) ∧
        (∫ x, Real.exp (β * x) ∂(μ : Measure ℝ)) =
          Real.exp ((r : ℝ) * (t : ℝ) * ((∫ y, Real.exp (β * y) ∂J) - 1))) := by
  obtain ⟨Ω, mΩ, P, τ, Y, hP, hd⟩ := levy_foundations_compoundPoissonDriverExists r hr J
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure P := hP
  let N (ω : Ω) := LevyFoundations.jumpCount (fun i => LevyFoundations.arrival τ i ω) (t : ℝ)
  let Z (ω : Ω) := ∑ j ∈ Finset.range (N ω), Y j ω
  have hN : Measurable N := by
    simpa [N] using (AvramDividend.Classical.avram_a06_compound_jumpCount_measurable_public τ hd.measurable_interarrival (t : ℝ))
  have hZ : Measurable Z := by
    have hs : Measurable (fun p : ℕ × Ω => ∑ j ∈ Finset.range p.1, Y j p.2) :=
      measurable_from_prod_countable_right fun n => Finset.measurable_sum (Finset.range n) fun j _ => (hd.measurable_mark j).comp (measurable_id : Measurable (fun y : Ω => y))
    exact hs.comp (hN.prodMk measurable_id)
  have hcompound : LevyFoundations.compoundPoisson 0 τ Y (t : ℝ) = Z := by
    funext ω
    simp [LevyFoundations.compoundPoisson, LevyFoundations.piecewisePath, Z, N]
  refine ⟨⟨P.map Z, Measure.isProbabilityMeasure_map hZ.aemeasurable⟩, ?_, ?_⟩
  · intro ξ
    change charFun (P.map Z) ξ = _
    rw [← hcompound]
    simpa [mul_assoc, mul_left_comm] using levy_foundations_compoundPoissonCharFun hd hr 0 t ξ
  · intro β hβ
    let F (x : ℝ) := Real.exp (β * x)
    have hF : Measurable F := by fun_prop
    have hY (j : ℕ) : ∀ᵐ ω ∂P, Y j ω ≤ 0 := by
      apply (ae_map_iff (hd.measurable_mark j).aemeasurable measurableSet_Iic).1
      simpa only [(hd.law_mark j).map_eq] using hJ
    have hZF : Integrable (F ∘ Z) P := by
      apply Integrable.of_bound (hF.comp hZ).aestronglyMeasurable 1
      filter_upwards [ae_all_iff.2 hY] with ω hω
      have hz : Z ω ≤ 0 := Finset.sum_nonpos (fun i _ => hω i)
      simpa only [Function.comp_apply, F, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        Real.exp_le_one_iff] using mul_nonpos_of_nonneg_of_nonpos hβ hz
    refine ⟨(integrable_map_measure hF.aestronglyMeasurable hZ.aemeasurable).2 hZF, ?_⟩
    change (∫ x, F x ∂(P.map Z)) = _
    rw [integral_map hZ.aemeasurable hF.aestronglyMeasurable]
    have hNat : Measurable (fun a : ℕ → ℝ => LevyFoundations.jumpCount
        (fun i => LevyFoundations.arrival (fun j p => p j) i a) (t : ℝ)) :=
      by simpa using (AvramDividend.Classical.avram_a06_compound_jumpCount_measurable_public
        (Ω := ℕ → ℝ) (fun j p => p j) (fun j => measurable_pi_apply j) (t : ℝ))
    have hNY : IndepFun N (fun ω j => Y j ω) P :=
      (result81_driver_blocks_independent hd).comp hNat measurable_id
    have hLaw : HasLaw N (poissonMeasure (r * t)) P := ⟨hN.aemeasurable, levy_foundations_compoundPoissonJumpCountLaw hd hr t⟩
    simpa only [NNReal.coe_mul] using
      AvramDividend.Classical.chat06_laplace_random_mark_sum_without_pgf_assumption
        P N Y hN hd.measurable_mark hNY (r * t) hLaw β (∫ y, F y ∂J) hZF
        (result81_fixed_mark_product hd β)
