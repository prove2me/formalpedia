-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNoArrivalTwoPopulationIndicator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:08:06.314128+00:00
-- url     : https://prove2.me/submissions/d7443a2a-3b69-432b-93ee-29f961e81f6e

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiBeforeInitialArrivalPopulationAE
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (rate : NNReal) (hrate : 0 < rate)
    (offspring : PMF Nat) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : Nat -> Omega -> Real)
    (jumpLaw : Measure Real) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : Real | ∃ k : Nat, x = (k : Real) - 1} = 1)
    (hJumpMass : ∀ k : Nat,
      jumpLaw ({((k : Real) - 1)} : Set Real) = offspring k)
    (hNoExplosion : ∀ y : Nat, ∀ᵐ omega ∂Q,
      ∀ t : NNReal, ∃ s : NNReal,
        (t : ENNReal) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s omega)
    (a b : Nat) (t : NNReal) (k : Nat) :
    (Q.prod Q) {zeta : Omega × Omega |
      (((a : Real) * (t : Real) <
        ProbabilityTheory.arrival arrival 0 zeta.1) ∧
        ((b : Real) * (t : Real) <
        ProbabilityTheory.arrival arrival 0 zeta.2)) ∧
      (compoundPoissonToBranching
        (integerCompoundPoisson a arrival marks) t zeta.1).toNat +
      (compoundPoissonToBranching
        (integerCompoundPoisson b arrival marks) t zeta.2).toNat = k} =
    if k = a + b then
      (Q.prod Q) (Set.prod
        {omega : Omega | (a : Real) * (t : Real) <
          ProbabilityTheory.arrival arrival 0 omega}
        {omega : Omega | (b : Real) * (t : Real) <
          ProbabilityTheory.arrival arrival 0 omega})
    else 0 := by
  classical
  let Sa : Set Omega := {w | (a : Real)*(t : Real) < ProbabilityTheory.arrival arrival 0 w}
  let Sb : Set Omega := {w | (b : Real)*(t : Real) < ProbabilityTheory.arrival arrival 0 w}
  let V : Set (Omega × Omega) := Set.prod Sa Sb
  let F : Nat -> Omega -> Nat := fun y omega =>
    (compoundPoissonToBranching
      (integerCompoundPoisson y arrival marks) t omega).toNat
  change (Q.prod Q) {zeta |
      (zeta.1 ∈ Sa ∧ zeta.2 ∈ Sb) ∧
      F a zeta.1 + F b zeta.2 = k} =
    if k = a + b then (Q.prod Q) V else 0
  have hA : ∀ᵐ omega ∂Q, omega ∈ Sa -> F a omega = a := by
    simpa only [Sa, F, Set.mem_setOf_eq] using
      (Kyprianou.Ch01.reverseLampertiBeforeInitialArrivalPopulationAE
        Q rate hrate offspring hNoZeroJumps arrival marks
        jumpLaw hdriver hSupport hJumpMass hNoExplosion a t)
  have hB : ∀ᵐ omega ∂Q, omega ∈ Sb -> F b omega = b := by
    simpa only [Sb, F, Set.mem_setOf_eq] using
      (Kyprianou.Ch01.reverseLampertiBeforeInitialArrivalPopulationAE
        Q rate hrate offspring hNoZeroJumps arrival marks
        jumpLaw hdriver hSupport hJumpMass hNoExplosion b t)
  have hZeroA : Q {omega | ¬ (omega ∈ Sa -> F a omega = a)} = 0 := (ae_iff).mp hA
  have hZeroB : Q {omega | ¬ (omega ∈ Sb -> F b omega = b)} = 0 := (ae_iff).mp hB
  have hProdA : ∀ᵐ zeta ∂(Q.prod Q), zeta.1 ∈ Sa -> F a zeta.1 = a := by
    apply (ae_iff).mpr
    have hs : {zeta : Omega × Omega | ¬ (zeta.1 ∈ Sa -> F a zeta.1 = a)} =
      Set.prod {omega | ¬ (omega ∈ Sa -> F a omega = a)} Set.univ := by
      ext zeta; simp [Set.prod]
    rw [hs]
    change (Q.prod Q)
      ({omega | ¬ (omega ∈ Sa -> F a omega = a)} ×ˢ Set.univ) = 0
    rw [Measure.prod_prod, hZeroA, zero_mul]
  have hProdB : ∀ᵐ zeta ∂(Q.prod Q), zeta.2 ∈ Sb -> F b zeta.2 = b := by
    apply (ae_iff).mpr
    have hs : {zeta : Omega × Omega | ¬ (zeta.2 ∈ Sb -> F b zeta.2 = b)} =
      Set.prod Set.univ {omega | ¬ (omega ∈ Sb -> F b omega = b)} := by
      ext zeta; simp [Set.prod]
    rw [hs]
    change (Q.prod Q)
      (Set.univ ×ˢ {omega | ¬ (omega ∈ Sb -> F b omega = b)}) = 0
    rw [Measure.prod_prod, hZeroB, mul_zero]
  have hPair : ∀ᵐ zeta ∂(Q.prod Q),
      (zeta.1 ∈ Sa ∧ zeta.2 ∈ Sb) ->
      F a zeta.1 + F b zeta.2 = a + b := by
    filter_upwards [hProdA, hProdB] with zeta hfa hfb hv
    rw [hfa hv.1, hfb hv.2]
  by_cases hk : k = a + b
  · subst k
    simp only [if_pos rfl]
    apply measure_congr
    filter_upwards [hPair] with zeta hz
    exact propext ⟨fun h => h.1, fun h => ⟨h, hz h⟩⟩
  · rw [if_neg hk]
    have hMass : (Q.prod Q) {zeta |
        (zeta.1 ∈ Sa ∧ zeta.2 ∈ Sb) ∧
        F a zeta.1 + F b zeta.2 = k} =
        (Q.prod Q) (∅ : Set (Omega × Omega)) := by
      apply measure_congr
      filter_upwards [hPair] with zeta hz
      apply propext
      change (((zeta.1 ∈ Sa ∧ zeta.2 ∈ Sb) ∧
        F a zeta.1 + F b zeta.2 = k) ↔ False)
      constructor
      · intro h
        exact hk (h.2.symm.trans (hz h.1))
      · exact False.elim
    simpa using hMass
