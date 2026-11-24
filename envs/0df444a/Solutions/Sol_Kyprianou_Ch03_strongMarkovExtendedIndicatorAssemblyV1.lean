-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovExtendedIndicatorAssemblyV1
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-24T07:20:42.547398+00:00
-- url     : https://prove2.me/submissions/16cc35a6-cb49-4fb5-ad25-d698063b0af5

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (Y : Omega → (NNReal → Real))
    (nu : Measure (NNReal → Real))
    (hY : AEMeasurable Y (P.restrict {omega : Omega | tau omega ≠ ⊤}))
    (hLaw : ∀ B : Set Omega, (∀ s : NNReal, MeasurableSet[F s]
      (B ∩ {omega : Omega | tau omega ≤ (s : WithTop NNReal)})) →
      Measure.map Y (P.restrict (B ∩ {omega : Omega | tau omega ≠ ⊤})) =
        P (B ∩ {omega : Omega | tau omega ≠ ⊤}) • nu) :
    ∀ A : Set Omega,
      (∀ s : NNReal, MeasurableSet[F s]
        (A ∩ {omega : Omega | tau omega ≤ (s : WithTop NNReal)})) →
      Measure.map (fun omega => (Set.indicator A (fun _ : Omega => (1 : Real)) omega,
        Y omega)) (P.restrict {omega : Omega | tau omega ≠ ⊤}) =
      (Measure.map (Set.indicator A (fun _ : Omega => (1 : Real)))
        (P.restrict {omega : Omega | tau omega ≠ ⊤})).prod nu := by
  intro A hA
  set O : Set Omega := {omega : Omega | tau omega ≠ ⊤} with hO
  set μ := P.restrict O with hμ
  -- measurability of the relevant sets
  have hle : ∀ s : NNReal, MeasurableSet {omega : Omega | tau omega ≤ (s : WithTop NNReal)} :=
    fun s => F.le s _ (hTau s)
  have hOeq : O = ⋃ n : ℕ, {omega : Omega | tau omega ≤ ((n : NNReal) : WithTop NNReal)} := by
    ext omega
    simp only [hO, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      lift tau omega to NNReal using h with c
      obtain ⟨n, hn⟩ := exists_nat_ge c
      exact ⟨n, WithTop.coe_le_coe.mpr hn⟩
    · rintro ⟨n, hn⟩
      exact ne_top_of_le_ne_top WithTop.coe_ne_top hn
  have hOm : MeasurableSet O := by
    rw [hOeq]; exact MeasurableSet.iUnion fun n => hle _
  set A' := A ∩ O with hA'
  have hA'eq : A' = ⋃ n : ℕ, (A ∩ {omega : Omega | tau omega ≤ ((n : NNReal) : WithTop NNReal)}) := by
    rw [hA', hOeq, Set.inter_iUnion]
  have hA'm : MeasurableSet A' := by
    rw [hA'eq]; exact MeasurableSet.iUnion fun n => F.le _ _ (hA _)
  have hAc : ∀ s : NNReal, MeasurableSet[F s]
      (Aᶜ ∩ {omega : Omega | tau omega ≤ (s : WithTop NNReal)}) := by
    intro s
    have : Aᶜ ∩ {omega : Omega | tau omega ≤ (s : WithTop NNReal)} =
        {omega : Omega | tau omega ≤ (s : WithTop NNReal)} \
          (A ∩ {omega : Omega | tau omega ≤ (s : WithTop NNReal)}) := by
      ext omega; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_diff]; tauto
    rw [this]; exact (hTau s).diff (hA s)
  have hU : ∀ s : NNReal, MeasurableSet[F s]
      (Set.univ ∩ {omega : Omega | tau omega ≤ (s : WithTop NNReal)}) := by
    intro s; rw [Set.univ_inter]; exact hTau s
  -- trivial case
  by_cases h0 : P O = 0
  · have : μ = 0 := Measure.restrict_eq_zero.mpr h0
    rw [this, Measure.map_zero, Measure.map_zero, Measure.zero_prod]
  -- `nu` is finite
  have hlawU := hLaw Set.univ hU
  rw [Set.univ_inter] at hlawU
  have hnu : IsFiniteMeasure nu := by
    constructor
    have h1 := congrArg (fun m : Measure (NNReal → Real) => m Set.univ) hlawU
    simp only [Measure.smul_apply, smul_eq_mul] at h1
    rw [Measure.map_apply_of_aemeasurable hY MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ] at h1
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    rw [htop, ENNReal.mul_top h0] at h1
    exact measure_ne_top P O h1
  -- measurable modifications
  set Y' := hY.mk Y
  have hY'm : Measurable Y' := hY.measurable_mk
  have hYY' : Y =ᵐ[μ] Y' := hY.ae_eq_mk
  let ind : Omega → ℝ := A'.indicator (fun _ => (1 : ℝ))
  have hind_m : Measurable ind := measurable_const.indicator hA'm
  have hindA : Set.indicator A (fun _ : Omega => (1 : Real)) =ᵐ[μ] ind := by
    filter_upwards [ae_restrict_mem hOm] with omega hom
    by_cases ha : omega ∈ A
    · simp [ind, hA', ha, hom]
    · simp [ind, hA', ha]
  have hLHS : Measure.map (fun omega => (Set.indicator A (fun _ : Omega => (1 : Real)) omega,
      Y omega)) μ = Measure.map (fun omega => (ind omega, Y' omega)) μ :=
    Measure.map_congr (hindA.prodMk hYY')
  have hRHS : Measure.map (Set.indicator A (fun _ : Omega => (1 : Real))) μ =
      Measure.map ind μ := Measure.map_congr hindA
  rw [hLHS, hRHS]
  -- split along `A'`
  have hsplit : μ = μ.restrict A' + μ.restrict A'ᶜ := (Measure.restrict_add_restrict_compl hA'm).symm
  have hr1 : μ.restrict A' = P.restrict (A ∩ O) := by
    rw [hμ, Measure.restrict_restrict hA'm, hA', Set.inter_assoc, Set.inter_self]
  have hr2 : μ.restrict A'ᶜ = P.restrict (Aᶜ ∩ O) := by
    rw [hμ, Measure.restrict_restrict hA'm.compl]
    congr 1
    ext omega; simp only [hA', Set.mem_inter_iff, Set.mem_compl_iff]; tauto
  have hpair : Measurable (fun omega => (ind omega, Y' omega)) := hind_m.prodMk hY'm
  -- the law of `Y'` on each piece
  have hYA : Measure.map Y' (P.restrict (A ∩ O)) = P (A ∩ O) • nu := by
    rw [← hLaw A hA]
    refine Measure.map_congr ?_
    have : P.restrict (A ∩ O) ≤ μ := by rw [← hr1]; exact Measure.restrict_le_self
    exact Filter.EventuallyEq.symm (ae_mono this hYY')
  have hYAc : Measure.map Y' (P.restrict (Aᶜ ∩ O)) = P (Aᶜ ∩ O) • nu := by
    rw [← hLaw Aᶜ hAc]
    refine Measure.map_congr ?_
    have : P.restrict (Aᶜ ∩ O) ≤ μ := by rw [← hr2]; exact Measure.restrict_le_self
    exact Filter.EventuallyEq.symm (ae_mono this hYY')
  have hind1 : ind =ᵐ[P.restrict (A ∩ O)] fun _ => (1 : ℝ) := by
    filter_upwards [ae_restrict_mem (hA'm : MeasurableSet (A ∩ O))] with omega hom
    simp [ind, hA', hom]
  have hind0 : ind =ᵐ[P.restrict (Aᶜ ∩ O)] fun _ => (0 : ℝ) := by
    filter_upwards [ae_restrict_mem (hA'm.compl.inter hOm |>.congr (by
      ext omega; simp only [hA', Set.mem_inter_iff, Set.mem_compl_iff]; tauto) :
      MeasurableSet (Aᶜ ∩ O))] with omega hom
    have : omega ∉ A' := fun h => hom.1 h.1
    simp [ind, this]
  rw [hsplit, Measure.map_add _ _ hpair, Measure.map_add _ _ hind_m, hr1, hr2, Measure.add_prod]
  congr 1
  · rw [Measure.map_congr (hind1.prodMk (Filter.EventuallyEq.refl _ Y')),
      Measure.map_congr hind1, Measure.map_const, Measure.restrict_apply_univ]
    have : (fun omega => ((1 : ℝ), Y' omega)) = Prod.mk (1 : ℝ) ∘ Y' := rfl
    rw [this, ← Measure.map_map measurable_prodMk_left hY'm, hYA, ← Measure.dirac_prod,
      Measure.prod_smul_right, Measure.prod_smul_left]
  · rw [Measure.map_congr (hind0.prodMk (Filter.EventuallyEq.refl _ Y')),
      Measure.map_congr hind0, Measure.map_const, Measure.restrict_apply_univ]
    have : (fun omega => ((0 : ℝ), Y' omega)) = Prod.mk (0 : ℝ) ∘ Y' := rfl
    rw [this, ← Measure.map_map measurable_prodMk_left hY'm, hYAc, ← Measure.dirac_prod,
      Measure.prod_smul_right, Measure.prod_smul_left]
