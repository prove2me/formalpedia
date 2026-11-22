-- Prove2me | solution 1 for Kyprianou.Ch01.stoppedCompoundPoissonMarkov
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-22T11:22:13.552569+00:00
-- url     : https://prove2.me/submissions/f264dae2-feea-4348-bfd3-066aebc9ec05

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_stoppedCompoundPoissonCylinderMarkov
import Theorems.Thm_Kyprianou_Ch01_stoppedCompoundPoissonGenerator
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false


namespace StoppedCPAux

/-- Law of an a.e.-measurable ℕ-valued random variable as a PMF (junk if not measurable). -/
noncomputable def lawOf {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (f : Ω → ℕ) : PMF ℕ := by
  classical
  exact if h : AEMeasurable f Q then
    @Measure.toPMF ℕ _ _ _ (Q.map f) (Measure.isProbabilityMeasure_map h)
  else PMF.pure 0

lemma lawOf_apply {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (f : Ω → ℕ) (h : AEMeasurable f Q) (k : ℕ) :
    lawOf Q f k = Q {ω | f ω = k} := by
  classical
  unfold lawOf
  rw [dif_pos h, Measure.toPMF_apply, Measure.map_apply_of_aemeasurable h (measurableSet_singleton k)]
  rfl

lemma eq_pure_of_mass_one {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (f : Ω → ℕ) (h : AEMeasurable f Q) (y : ℕ) (h1 : Q {ω | f ω = y} = 1) :
    lawOf Q f = PMF.pure y := by
  ext k
  rw [lawOf_apply Q f h k, PMF.pure_apply]
  split_ifs with hk
  · subst hk; exact h1
  · have hnm : NullMeasurableSet {ω | f ω = y} Q := h.nullMeasurable (measurableSet_singleton y)
    have hc : Q {ω | f ω = y}ᶜ = 0 := by
      rw [measure_compl₀ hnm (measure_ne_top _ _), h1]; simp
    refine le_antisymm ?_ bot_le
    rw [← hc]
    apply measure_mono
    intro ω hω hω'
    exact hk ((hω : f ω = k).symm.trans hω')

end StoppedCPAux

theorem solution
    {Ω' : Type*} [MeasurableSpace Ω']
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω' → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hDriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∃ lawC : PopulationLaws,
      IsPopulationMarkovSemigroup lawC ∧
      (∀ z : ℕ, lawC z 0 = PMF.pure z) ∧
      (∀ z k : ℕ,
        HasDerivWithinAt
          (fun t : ℝ => ((lawC z (Real.toNNReal t)) k).toReal)
          (if k = z then (if z = 0 then 0 else -(rate : ℝ))
           else if 1 ≤ z ∧ z ≤ k + 1 then
             (rate : ℝ) * (offspring (k + 1 - z)).toReal
           else 0)
          (Set.Ici 0) 0) ∧
      ∀ y : ℕ,
        (∀ t : ℝ≥0, ∀ᵐ ω ∂Q,
          0 ≤ stoppedIntegerCompoundPoisson y arrival marks t ω) ∧
        (∀ t : ℝ≥0, AEMeasurable
          (fun ω => (stoppedIntegerCompoundPoisson y arrival marks t ω).toNat) Q) ∧
        Q {ω | (stoppedIntegerCompoundPoisson y arrival marks 0 ω).toNat = y} = 1 ∧
        ∀ (m : ℕ) (u : Fin m → ℝ≥0) (v : Fin m → ℕ) (s t : ℝ≥0) (k : ℕ),
          (∀ i, u i ≤ s) →
          Q ({ω | ∀ i,
                (stoppedIntegerCompoundPoisson y arrival marks (u i) ω).toNat = v i} ∩
              {ω | (stoppedIntegerCompoundPoisson y arrival marks (s + t) ω).toNat = k}) =
            ∑' z : ℕ, Q ({ω | ∀ i,
                (stoppedIntegerCompoundPoisson y arrival marks (u i) ω).toNat = v i} ∩
              {ω | (stoppedIntegerCompoundPoisson y arrival marks s ω).toNat = z}) *
              lawC z t k  := by
  classical
  have hA := stoppedCompoundPoissonCylinderMarkov Q rate hRate arrival marks jumpLaw hDriver hSupport
  have hB := stoppedCompoundPoissonGenerator Q rate hRate offspring hNoNullJumps arrival marks
    jumpLaw hDriver hSupport hJumpMass
  set X : ℕ → ℝ≥0 → Ω' → ℕ := fun z t ω =>
    (stoppedIntegerCompoundPoisson z arrival marks t ω).toNat with hX_def
  have hmeas : ∀ z t, AEMeasurable (X z t) Q := fun z t => (hA z).2.1 t
  refine ⟨fun z t => StoppedCPAux.lawOf Q (X z t), ?_, ?_, ?_, ?_⟩
  · -- Chapman–Kolmogorov from the cylinder Markov identity with no constraints
    intro y s t
    ext k
    rw [PMF.bind_apply, StoppedCPAux.lawOf_apply Q _ (hmeas y (s + t)) k]
    have := (hA y).2.2.2 0 Fin.elim0 Fin.elim0 s t k (fun i => Fin.elim0 i)
    have huniv : {ω : Ω' | ∀ i : Fin 0,
        (stoppedIntegerCompoundPoisson y arrival marks (Fin.elim0 i) ω).toNat = Fin.elim0 i} =
        Set.univ := by
      ext ω; simp
    rw [huniv] at this
    simp only [Set.univ_inter] at this
    rw [show {ω | X y (s + t) ω = k} =
      {ω | (stoppedIntegerCompoundPoisson y arrival marks (s + t) ω).toNat = k} from rfl, this]
    congr 1; funext z
    rw [StoppedCPAux.lawOf_apply Q _ (hmeas y s) z, StoppedCPAux.lawOf_apply Q _ (hmeas z t) k]
  · intro z
    exact StoppedCPAux.eq_pure_of_mass_one Q _ (hmeas z 0) z (hA z).2.2.1
  · intro z k
    have := hB z k
    convert this using 2 with t
    rw [StoppedCPAux.lawOf_apply Q _ (hmeas z _) k]
  · intro y
    refine ⟨(hA y).1, (hA y).2.1, (hA y).2.2.1, ?_⟩
    intro m u v s t k hu
    rw [(hA y).2.2.2 m u v s t k hu]
    congr 1; funext z
    rw [StoppedCPAux.lawOf_apply Q _ (hmeas z t) k]
