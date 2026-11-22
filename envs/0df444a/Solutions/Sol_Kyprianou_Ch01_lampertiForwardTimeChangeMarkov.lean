-- Prove2me | solution 1 for Kyprianou.Ch01.lampertiForwardTimeChangeMarkov
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-22T16:17:37.568013+00:00
-- url     : https://prove2.me/submissions/432ae09a-61c4-4f8b-907f-4a98961da0c6

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_lampertiForwardCylinderMarkov
import Theorems.Thm_Kyprianou_Ch01_lampertiForwardGenerator
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace LampertiTimeChangeAux

/-- Law of an a.e.-measurable ℕ-valued random variable as a PMF (junk if not measurable). -/
noncomputable def lawOf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℕ) : PMF ℕ := by
  classical
  exact if h : AEMeasurable f P then
    @Measure.toPMF ℕ _ _ _ (P.map f) (Measure.isProbabilityMeasure_map h)
  else PMF.pure 0

lemma lawOf_apply {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℕ) (h : AEMeasurable f P) (k : ℕ) :
    lawOf P f k = P {ω | f ω = k} := by
  classical
  unfold lawOf
  rw [dif_pos h, Measure.toPMF_apply, Measure.map_apply_of_aemeasurable h (measurableSet_singleton k)]
  rfl

lemma eq_pure_of_mass_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℕ) (h : AEMeasurable f P) (y : ℕ) (h1 : P {ω | f ω = y} = 1) :
    lawOf P f = PMF.pure y := by
  ext k
  rw [lawOf_apply P f h k, PMF.pure_apply]
  split_ifs with hk
  · subst hk; exact h1
  · have hnm : NullMeasurableSet {ω | f ω = y} P := h.nullMeasurable (measurableSet_singleton y)
    have hc : P {ω | f ω = y}ᶜ = 0 := by
      rw [measure_compl₀ hnm (measure_ne_top _ _), h1]; simp
    refine le_antisymm ?_ bot_le
    rw [← hc]
    apply measure_mono
    intro ω hω hω'
    exact hk ((hω : f ω = k).symm.trans hω')

end LampertiTimeChangeAux

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℕ)
    (P : ℕ → Measure Ω) (law : PopulationLaws)
    (rate : ℝ≥0) (hRate : 0 < rate)
    (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (hBranching : HasBranchingProperty law)
    (hMarkov : IsPopulationMarkovPath Y P law)
    (hSemigroup : IsPopulationMarkovSemigroup law)
    (hGenerator : IsBranchingRateGenerator law rate offspring)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ y : ℕ, ∀ᵐ ω ∂P y,
      IsCadlag (fun t : ℝ≥0 => Y t ω)) :
    ∃ lawX : PopulationLaws,
      IsPopulationMarkovSemigroup lawX ∧
      (∀ z : ℕ, lawX z 0 = PMF.pure z) ∧
      (∀ z k : ℕ,
        HasDerivWithinAt
          (fun t : ℝ => ((lawX z (Real.toNNReal t)) k).toReal)
          (if k = z then (if z = 0 then 0 else -(rate : ℝ))
           else if 1 ≤ z ∧ z ≤ k + 1 then
             (rate : ℝ) * (offspring (k + 1 - z)).toReal
           else 0)
          (Set.Ici 0) 0) ∧
      ∀ y : ℕ,
        (∀ t : ℝ≥0, AEMeasurable (fun ω => branchingToPoisson Y t ω) (P y)) ∧
        P y {ω | branchingToPoisson Y 0 ω = y} = 1 ∧
        ∀ (m : ℕ) (u : Fin m → ℝ≥0) (v : Fin m → ℕ) (s t : ℝ≥0) (k : ℕ),
          (∀ i, u i ≤ s) →
          P y ({ω | ∀ i, branchingToPoisson Y (u i) ω = v i} ∩
              {ω | branchingToPoisson Y (s + t) ω = k}) =
            ∑' z : ℕ, P y ({ω | ∀ i, branchingToPoisson Y (u i) ω = v i} ∩
              {ω | branchingToPoisson Y s ω = z}) * lawX z t k := by
  classical
  have hA := lampertiForwardCylinderMarkov Y P law rate hRate offspring hNoNullJumps
    hBranching hMarkov hSemigroup hGenerator hInitial hMeas hCadlag
  have hB := lampertiForwardGenerator Y P law rate hRate offspring hNoNullJumps
    hBranching hMarkov hSemigroup hGenerator hInitial hMeas hCadlag
  have hProb : ∀ z : ℕ, IsProbabilityMeasure (P z) := hMarkov.1
  have hmeas : ∀ z t, AEMeasurable (fun ω => branchingToPoisson Y t ω) (P z) :=
    fun z t => (hA z).1 t
  refine ⟨fun z t => @LampertiTimeChangeAux.lawOf Ω _ (P z) (hProb z)
    (fun ω => branchingToPoisson Y t ω), ?_, ?_, ?_, ?_⟩
  · intro y s t
    ext k
    rw [PMF.bind_apply, LampertiTimeChangeAux.lawOf_apply (P y) _ (hmeas y (s + t)) k]
    have := (hA y).2.2 0 Fin.elim0 Fin.elim0 s t k (fun i => Fin.elim0 i)
    have huniv : {ω : Ω | ∀ i : Fin 0,
        branchingToPoisson Y (Fin.elim0 i) ω = Fin.elim0 i} = Set.univ := by
      ext ω; simp
    rw [huniv] at this
    simp only [Set.univ_inter] at this
    rw [this]
    congr 1; funext z
    rw [LampertiTimeChangeAux.lawOf_apply (P y) _ (hmeas y s) z,
        LampertiTimeChangeAux.lawOf_apply (P z) _ (hmeas z t) k]
  · intro z
    exact @LampertiTimeChangeAux.eq_pure_of_mass_one Ω _ (P z) (hProb z)
      (fun ω => branchingToPoisson Y 0 ω) (hmeas z 0) z (hA z).2.1
  · intro z k
    have := hB z k
    convert this using 2 with t
    rw [LampertiTimeChangeAux.lawOf_apply (P z) _ (hmeas z _) k]
  · intro y
    refine ⟨(hA y).1, (hA y).2.1, ?_⟩
    intro m u v s t k hu
    rw [(hA y).2.2 m u v s t k hu]
    congr 1; funext z
    rw [LampertiTimeChangeAux.lawOf_apply (P z) _ (hmeas z t) k]
