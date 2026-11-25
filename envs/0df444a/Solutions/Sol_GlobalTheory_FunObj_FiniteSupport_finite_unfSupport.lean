-- Prove2me | solution 1 for GlobalTheory.FunObj.FiniteSupport.finite_unfSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:52:18.949804+00:00
-- url     : https://prove2.me/submissions/e4adc0cd-2a7e-4f14-a303-d864b25d9f6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteUnfSupportOfNeOne
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_finite_unfSupport_of_ne_one
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_ne_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.FiniteSupport
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.RootEx.Supp GlobalTheory.RootEx.FJUnipotent
namespace GlobalTheory.FunObj.FiniteSupport
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
    [ν.IsAddHaarMeasure] (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (J : G.Level) :
    Even G.m → IsUnif ϖ → HasConductor ψ 1 → G.IsTensor ϖ e (oppositePath G.m) T →
      (∀ j, 0 < j → j < G.m → IsOpen (J (G.m, j) : Set (GL (Fin (G.rank (G.m, j))) k))) →
      ∀ (keep : Bool) (ρ : Reps hs J), (unfSupport ψ ν keep ρ T).Finite :=
  fun _ _ hψ hT hJ keep ρ => finite_unfSupport_of_ne_one ν hψ.ne_one hT hJ keep ρ
end GlobalTheory.FunObj.FiniteSupport
