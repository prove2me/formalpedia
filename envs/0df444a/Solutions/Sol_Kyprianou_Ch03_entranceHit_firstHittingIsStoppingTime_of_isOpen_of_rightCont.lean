-- Prove2me | solution 1 for Kyprianou.Ch03.entranceHit_firstHittingIsStoppingTime_of_isOpen_of_rightCont
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-24T06:20:21.059811+00:00
-- url     : https://prove2.me/submissions/f9841636-29ab-4a2d-a2b5-a814d0316d72

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace HitOpenAux

/-- On a right-continuous path, hitting an open set before `s` is witnessed at a rational time. -/
theorem hit_lt_iff {Omega : Type} (X : NNReal → Omega → Real) (B : Set Real) (hB : IsOpen B)
    (omega : Omega) (hrc : ∀ t : NNReal, ContinuousWithinAt (fun u => X u omega) (Set.Ici t) t)
    (s : NNReal) :
    Kyprianou.Ch03.firstHittingTime X B omega < (s : WithTop NNReal) ↔
      ∃ q : ℚ, 0 < q ∧ (q : ℝ) < s ∧ X (Real.toNNReal q) omega ∈ B := by
  unfold Kyprianou.Ch03.firstHittingTime
  constructor
  · intro h
    obtain ⟨b, ⟨t, ⟨ht0, htB⟩, rfl⟩, hts⟩ := sInf_lt_iff.mp h
    have hts' : t < s := WithTop.coe_lt_coe.mp hts
    have hev : ∀ᶠ v in 𝓝[≥] t, X v omega ∈ B :=
      (hrc t).eventually (hB.mem_nhds htB)
    obtain ⟨w, htw, hw⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
    have hmin : (t : ℝ) < min (w : ℝ) s := lt_min (by exact_mod_cast htw) (by exact_mod_cast hts')
    obtain ⟨q, htq, hqm⟩ := exists_rat_btwn hmin
    have hq0 : (0 : ℝ) < q := (NNReal.coe_nonneg t).trans_lt htq
    refine ⟨q, by exact_mod_cast hq0, hqm.trans_le (min_le_right _ _), hw ?_⟩
    constructor
    · rw [Real.le_toNNReal_iff_coe_le hq0.le]; exact htq.le
    · rw [Real.toNNReal_lt_iff_lt_coe hq0.le]; exact hqm.trans_le (min_le_left _ _)
  · rintro ⟨q, hq0, hqs, hqB⟩
    have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
    refine lt_of_le_of_lt (sInf_le ⟨Real.toNNReal q, ⟨by simpa using hq0', hqB⟩, rfl⟩) ?_
    rw [WithTop.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe hq0'.le]
    exact hqs

/-- `τ ≤ t` iff `τ < t + 1/(n + n0 + 1)` for every `n`. -/
theorem le_iff_forall_lt (τ : WithTop NNReal) (t : NNReal) (n0 : ℕ) :
    τ ≤ (t : WithTop NNReal) ↔
      ∀ n : ℕ, τ < ((t + 1 / ((n + n0 : ℕ) + 1 : NNReal) : NNReal) : WithTop NNReal) := by
  constructor
  · intro h n
    refine lt_of_le_of_lt h ?_
    rw [WithTop.coe_lt_coe]
    exact lt_add_of_pos_right _ (by positivity)
  · intro h
    by_contra hlt
    push_neg at hlt
    induction τ using WithTop.recTopCoe with
    | top => exact absurd (h 0) (not_lt.mpr le_top)
    | coe c =>
      have hct : t < c := WithTop.coe_lt_coe.mp hlt
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (tsub_pos_of_lt hct)
      have h1 : 1 / (((k + n0 : ℕ) : NNReal) + 1) ≤ 1 / ((k : NNReal) + 1) := by
        gcongr
        exact_mod_cast Nat.le_add_right k n0
      have h2 : t + 1 / (((k + n0 : ℕ) : NNReal) + 1) < c := by
        have := (lt_tsub_iff_left).mp (h1.trans_lt hk)
        exact this
      exact absurd (WithTop.coe_lt_coe.mp (h k)) (not_lt.mpr h2.le)

end HitOpenAux

open HitOpenAux in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (B : Set Real)
    (hB : IsOpen B)
    (hRC : F.IsRightContinuous)
    (entranceTime hittingTime : Omega -> NNReal)
    (hEntranceTime : forall omega,
      Kyprianou.Ch03.firstEntranceTime X B omega != ⊤ ->
        Kyprianou.Ch03.firstEntranceTime X B omega = (entranceTime omega : WithTop NNReal))
    (hHittingTime : forall omega,
      Kyprianou.Ch03.firstHittingTime X B omega != ⊤ ->
        Kyprianou.Ch03.firstHittingTime X B omega = (hittingTime omega : WithTop NNReal)) :
    IsStoppingTime F (Kyprianou.Ch03.firstHittingTime X B) := by
  set τ := Kyprianou.Ch03.firstHittingTime X B with hτ
  -- a measurable null set outside of which paths are càdlàg
  have hae := hX.cadlag_ae
  rw [ae_iff] at hae
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null hae
  have hgood : ∀ omega, omega ∉ N →
      ∀ t : NNReal, ContinuousWithinAt (fun u => X u omega) (Set.Ici t) t := by
    intro omega hom t
    by_contra hbad
    exact hom (hNsub (fun hc => hbad (hc t).1))
  -- null subsets belong to every `F s`
  have hnull : ∀ s : NNReal, ∀ A : Set Omega, A ⊆ N → MeasurableSet[F s] A := by
    intro s A hA
    rw [hNatural s]
    exact (le_sup_right : _ ≤ PerfCorrMSQ.natFiltr X s ⊔ _) A
      (MeasurableSpace.measurableSet_generateFrom ⟨N, hNm, hN0, hA⟩)
  have hmod : ∀ s : NNReal, ∀ A U : Set Omega, MeasurableSet[F s] U →
      (∀ omega, omega ∉ N → (omega ∈ A ↔ omega ∈ U)) → MeasurableSet[F s] A := by
    intro s A U hU hAU
    have hEq : A = (U \ N) ∪ (A ∩ N) := by
      ext omega
      by_cases hom : omega ∈ N
      · simp [hom]
      · simp [hom, hAU omega hom]
    rw [hEq]
    exact (hU.diff (hnull s N subset_rfl)).union (hnull s _ Set.inter_subset_right)
  -- `X q` is `F q`-measurable
  have hXm : ∀ u : NNReal, MeasurableSet[F u] {omega | X u omega ∈ B} := by
    intro u
    rw [hNatural u]
    refine (le_sup_left : PerfCorrMSQ.natFiltr X u ≤ _) _ ?_
    refine (le_iSup₂ (f := fun v (_ : v ≤ u) =>
      MeasurableSpace.comap (X v) (inferInstance : MeasurableSpace ℝ)) u le_rfl) _ ?_
    exact ⟨B, hB.measurableSet, rfl⟩
  -- `{τ < s} ∈ F s`
  have hlt : ∀ s : NNReal, MeasurableSet[F s] {omega | τ omega < (s : WithTop NNReal)} := by
    intro s
    let U : Set Omega := ⋃ q : ℚ, ⋃ (_ : 0 < q ∧ (q : ℝ) < s),
      {omega | X (Real.toNNReal q) omega ∈ B}
    have hU : MeasurableSet[F s] U := by
      refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_
      have hle : Real.toNNReal q ≤ s := by
        rw [Real.toNNReal_le_iff_le_coe]; exact hq.2.le
      exact F.mono hle _ (hXm _)
    refine hmod s _ U hU fun omega hom => ?_
    simp only [Set.mem_setOf_eq, U, Set.mem_iUnion, exists_prop]
    rw [hτ, hit_lt_iff X B hB omega (hgood omega hom) s]
    constructor
    · rintro ⟨q, h1, h2, h3⟩; exact ⟨q, ⟨h1, h2⟩, h3⟩
    · rintro ⟨q, ⟨h1, h2⟩, h3⟩; exact ⟨q, h1, h2, h3⟩
  -- right-continuity
  intro t
  have hplus : MeasurableSet[Filtration.rightCont F t] {omega | τ omega ≤ (t : WithTop NNReal)} := by
    rw [Filtration.rightCont_eq_of_neBot_nhdsGT]
    refine MeasurableSpace.measurableSet_iInf.mpr fun j => ?_
    refine MeasurableSpace.measurableSet_iInf.mpr fun htj => ?_
    obtain ⟨n0, hn0⟩ := exists_nat_one_div_lt (tsub_pos_of_lt htj)
    have hset : {omega | τ omega ≤ (t : WithTop NNReal)} =
        ⋂ n : ℕ, {omega | τ omega <
          ((t + 1 / ((n + n0 : ℕ) + 1 : NNReal) : NNReal) : WithTop NNReal)} := by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact le_iff_forall_lt (τ omega) t n0
    rw [hset]
    refine MeasurableSet.iInter fun n => ?_
    have hle : t + 1 / (((n + n0 : ℕ) : NNReal) + 1) ≤ j := by
      have h1 : 1 / (((n + n0 : ℕ) : NNReal) + 1) ≤ 1 / ((n0 : NNReal) + 1) := by
        gcongr
        exact_mod_cast Nat.le_add_left n0 n
      have h2 := ((lt_tsub_iff_left).mp (h1.trans_lt hn0)).le
      exact h2
    exact F.mono hle _ (hlt _)
  exact hRC.RC t _ hplus
