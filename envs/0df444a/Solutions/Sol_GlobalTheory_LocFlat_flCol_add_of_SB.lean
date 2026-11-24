-- Prove2me | solution 1 for GlobalTheory.LocFlat.flCol_add_of_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:00:10.114065+00:00
-- url     : https://prove2.me/submissions/1e84c447-6a23-4d55-9f8a-7ae5dd7a75ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFactorThroughFlatMapFourierJacobiColumn
import Theorems.Thm_GlobalTheory_LocFlat_flCol_integrand_integrable
import Theorems.Thm_GlobalTheory_LocFlat_flCol_eq_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.LocFlat
theorem _root_.solution (ψ : AddChar k Circle) (hψ : Continuous ψ) (ν : Measure k)
    (hν : ν.IsAddHaarMeasure) (p : ℕ) (Φ₁ Φ₂ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (h₁ : Φ₁ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (h₂ : Φ₂ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    flCol ψ ν p (Φ₁ + Φ₂) = flCol ψ ν p Φ₁ + flCol ψ ν p Φ₂ := by
  funext x
  simp only [flCol_eq_integral, Pi.add_apply, add_mul]
  exact integral_add (flCol_integrand_integrable ψ hψ ν hν p Φ₁ h₁ x)
    (flCol_integrand_integrable ψ hψ ν hν p Φ₂ h₂ x)
end GlobalTheory.LocFlat
