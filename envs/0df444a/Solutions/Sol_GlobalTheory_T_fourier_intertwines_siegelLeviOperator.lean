-- Prove2me | solution 1 for GlobalTheory.T.fourier_intertwines_siegelLeviOperator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:12.091288+00:00
-- url     : https://prove2.me/submissions/a713376c-6d99-47c1-938b-10d1eee51c91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierIntertwinesSiegelLeviOperator
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierIntertwinesSiegelLeviOperatorStatement
import Theorems.Thm_GlobalTheory_KSp_fou_parFun_levi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∀ p ∈ sieg c ν, ∀ q ∈ sieg c ν, weyl c ν * p = q * weyl c ν → ∀ φ : Matrix α ν E → ℂ, fou c ψ Q μ (parFun c ψ χ Q (mat c p) φ) = parFun c ψ χ Q (mat c q) (fou c ψ Q μ φ) := by
  first | exact @GlobalTheory.KSp.fou_parFun_levi | exact GlobalTheory.KSp.fou_parFun_levi | (intros; apply GlobalTheory.KSp.fou_parFun_levi <;> assumption)
end _root_.GlobalTheory.T
