-- Prove2me | solution 1 for GlobalTheory.TopCongr.hat_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:01.18332+00:00
-- url     : https://prove2.me/submissions/02a5e075-af6f-4650-872d-b5c9ad31e5fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CongruenceUnipotentMatrixReduction
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_fourier_eq_zero_pi
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.TopCongr
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.TopCongr
theorem _root_.solution [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
    {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) {ε : k}
    (hε : valuation k ε = 1) (y₀ : n → k) {η : n → k} (hη : ¬ ∀ i, η i ∈ 𝒪[k]) :
    hat ψ ν ε (cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀)) η = 0 := by
  classical
  have := hν.1
  have := secondCountable k
  have hs : ∀ z ∈ box n (1 : kˣ), ∀ x,
      cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀) (x + z) =
      cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀) x := fun z hz x => by
    have : (Submodule.Quotient.mk (x + z) : (n → k) ⧸ box n (1 : kˣ)) = Submodule.Quotient.mk x :=
      (Submodule.Quotient.eq _).2 (by simpa using hz)
    simp only [cosetInd, Set.indicator_apply, Set.mem_setOf_eq, this]
  refine Eq.trans ?_ (FourierPi.fourier_eq_zero_pi (Measure.pi fun _ => ν) hψ (s := 1)
    (fun z hz x => hs z (fun i => hz i trivial) x) (y := ε • η) fun h' => hη fun i => ?_)
  · simp only [hat, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  · simpa [cball, hε, Valuation.mem_integer_iff] using h' i trivial
end GlobalTheory.TopCongr
