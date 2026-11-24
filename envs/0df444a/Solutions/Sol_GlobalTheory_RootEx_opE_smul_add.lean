-- Prove2me | solution 1 for GlobalTheory.RootEx.opE_smul_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:04:12.674133+00:00
-- url     : https://prove2.me/submissions/8a3b985d-b8a8-4faf-9783-4a20aa6ed3c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Theorems.Thm_GlobalTheory_RootEx_integrable_opE_integrand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c : ℕ}
namespace GlobalTheory.RootEx
theorem _root_.solution (p : ℕ) {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k)
    [ν.IsAddHaarMeasure] (z : ℂ) {Φ Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (hΨ : Ψ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    opE ψ ν p (z • Φ + Ψ) = z • opE ψ ν p Φ + opE ψ ν p Ψ := by
  funext x₀
  have h1 := (integrable_opE_integrand p hψ ν hΦ x₀).const_mul z
  have h2 := integrable_opE_integrand p hψ ν hΨ x₀
  simp only [opE, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_add h1 h2]
  congr 1
  funext e
  ring
end GlobalTheory.RootEx
