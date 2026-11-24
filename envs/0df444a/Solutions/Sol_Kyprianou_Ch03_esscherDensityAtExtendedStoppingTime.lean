-- Prove2me | solution 1 for Kyprianou.Ch03.esscherDensityAtExtendedStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T15:02:59.925264+00:00
-- url     : https://prove2.me/submissions/053edf86-b25e-443d-87e7-04f36efca830

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_esscherDensityFiniteCutV1
import Theorems.Thm_Kyprianou_Ch03_nonnegativeDensityExtendCutV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch03

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
                t omega) omega ∂P))
    (tau : Omega -> WithTop NNReal)
    (hStopping : IsStoppingTime F tau)
    (tauFinite : Omega -> NNReal)
    (hTauFinite : forall omega, tau omega != ⊤ ->
      tau omega = (tauFinite omega : WithTop NNReal)) :
    forall (A : Set Omega),
      (forall t : NNReal,
        MeasurableSet[F t]
          (Set.inter A {omega : Omega |
            tau omega <= (t : WithTop NNReal)})) ->
      Q (Set.inter A {omega : Omega | tau omega != ⊤}) =
        ENNReal.ofReal
          (∫ omega,
            Set.indicator
              (Set.inter A {eta : Omega | tau eta != ⊤})
              (fun eta : Omega =>
                esscherDensity X beta
                  (Real.log
                    (∫ z, Real.exp (beta * X 1 z) ∂P))
                  (tauFinite eta) eta)
              omega ∂P) := by
  classical
  intro A hA
  let B : ℕ → Set Omega := fun n => A ∩ {omega | tau omega ≤ ((n : NNReal) : WithTop NNReal)}
  let Z : Omega → ℝ := fun eta => esscherDensity X beta
    (Real.log (∫ z, Real.exp (beta * X 1 z) ∂P)) (tauFinite eta) eta
  have hB : ∀ n, MeasurableSet (B n) := fun n => F.le (n : NNReal) _ (hA n)
  have hmono : Monotone B := by
    intro n m hnm omega hmem
    have hn : tau omega ≤ ((n : NNReal) : WithTop NNReal) := hmem.2
    have hnm' : (n : NNReal) ≤ (m : NNReal) := by exact_mod_cast hnm
    exact ⟨hmem.1, hn.trans (WithTop.coe_le_coe.mpr hnm')⟩
  have hZ : ∀ omega, 0 ≤ Z omega := fun omega => Real.exp_nonneg _
  have hc := esscherDensityFiniteCutV1 P Q F X hX hNatural T hLK beta hBeta
    hEsscher tau hStopping tauFinite hTauFinite A hA
  have hu : (⋃ n, B n) = A ∩ {omega | tau omega ≠ ⊤} := by
    ext omega
    simp only [Set.mem_iUnion, B, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, ha, hn⟩
      exact ⟨ha, ne_top_of_le_ne_top (by simp) hn⟩
    · rintro ⟨ha, ht⟩
      obtain ⟨n, hn⟩ := exists_nat_ge (tauFinite omega)
      exact ⟨n, ha, by rw [hTauFinite omega (by simpa using ht)]; exact_mod_cast hn⟩
  have h := nonnegativeDensityExtendCutV1 P Q B Z hB hmono hZ
    (fun n => (hc n).1) (fun n => (hc n).2)
  rw [hu] at h
  have hSet : {w : Omega | tau w != ⊤} = {w | tau w ≠ ⊤} := by
    ext w
    simp
  change Q (A ∩ {w | tau w != ⊤}) =
    ENNReal.ofReal (∫ w, (A ∩ {w | tau w != ⊤}).indicator Z w ∂P)
  rw [hSet]
  exact h
