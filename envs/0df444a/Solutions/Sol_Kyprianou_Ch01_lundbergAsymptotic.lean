-- Prove2me | solution 1 for Kyprianou.Ch01.lundbergAsymptotic
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-21T09:20:07.729648+00:00
-- url     : https://prove2.me/submissions/137ab454-b2c4-4625-bdaf-21e80a4299a0

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Theorems.Thm_Kyprianou_Ch01_ruinDeficitIntegratedTail
import Theorems.Thm_Kyprianou_Ch01_pollaczekKhintchineRuin
import Theorems.Thm_Kyprianou_Ch01_integratedTailLaw_exists
import Theorems.Thm_Kyprianou_Ch01_lundbergRootEquation
import Theorems.Thm_Kyprianou_Ch01_pkSeriesCramerAsymptotic

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal

set_option autoImplicit false
universe u

theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hrate : 0 < rate)
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu)
    (premium : ℝ) (hpremium : 0 < premium)
    (hnet : (rate : ℝ) * mu < premium)
    (nu : ℝ) (hnu : 0 < nu)
    (hnonlattice : IsNonLattice F)
    (hint : Integrable
      (fun ω => Real.exp (-nu * riskSurplus arrival claims premium 0 1 ω)) P)
    (hroot : (∫ ω, Real.exp
      (-nu * riskSurplus arrival claims premium 0 1 ω) ∂P) = 1) :
    let weightedTail : ℝ≥0∞ :=
      ∫⁻ y in Set.Ioi (0 : ℝ),
        ENNReal.ofReal
          (y * Real.exp (nu * y) * (F (Set.Ioi y)).toReal) ∂volume
    Tendsto (fun x : ℝ => Real.exp (nu * x) *
      ruinProbability P arrival claims premium x) atTop
      (nhds (if weightedTail = ⊤ then 0 else
        (((rate : ℝ) * nu / (premium - (rate : ℝ) * mu)) *
          weightedTail.toReal)⁻¹)) := by
  intro weightedTail
  -- Theorem 1.9: ψ(0) = λμ/c and the deficit law is the integrated tail.
  obtain ⟨hpsi0, hdef⟩ := Kyprianou.Ch01.ruinDeficitIntegratedTail
    P arrival claims rate F hd hrate mu hmu hclaimpos hclaimint hmean
    premium hpremium hnet
  -- The integrated-tail law exists as a probability measure on [0, ∞).
  obtain ⟨eta, hetaProb, hetaSupport, heta⟩ :=
    Kyprianou.Ch01.integratedTailLaw_exists F mu hmu hclaimpos hclaimint hmean
  haveI := hetaProb
  -- Theorem 1.8: Pollaczek–Khintchine series for the survival probability.
  have hPK := Kyprianou.Ch01.pollaczekKhintchineRuin
    P arrival claims rate F hd hrate mu hmu hclaimpos hclaimint hmean
    premium hpremium hnet eta hetaSupport
    (fun x hx => by rw [hdef x hx, heta x hx])
  -- The Cramér root gives the Lundberg equation for F.
  obtain ⟨hexpint, hlundberg⟩ := Kyprianou.Ch01.lundbergRootEquation
    P arrival claims rate F hd hrate hclaimpos premium hpremium nu hnu hint hroot
  -- Analytic asymptotics of the defective PK renewal series.
  have hA := Kyprianou.Ch01.pkSeriesCramerAsymptotic rate hrate F mu hmu
    hclaimpos hclaimint hmean premium hpremium hnet nu hnu hexpint hlundberg
    eta hetaSupport heta
  refine hA.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have h := hPK x hx
  rw [hpsi0] at h
  congr 1
  linarith
