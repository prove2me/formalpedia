-- Prove2me | solution 1 for GlobalTheory.FunObj.FiniteSupport.transpose_mem_matLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:47:15.843325+00:00
-- url     : https://prove2.me/submissions/b63b60bb-59fb-4839-9a95-c1faba476a2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteUnfSupportOfNeOne
import Theorems.Thm_GlobalTheory_SplitFlip_smul_diagLat


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
variable {k : Type} [Field k] {a c b : ℕ}
variable [ValuativeRel k]
namespace GlobalTheory.FunObj.FiniteSupport
theorem _root_.solution [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι κ : Type} (u : kˣ) {x : Matrix κ ι k} (hx : Bd (valuation k (u : k)) x) :
    xᵀ ∈ matLat ι (u • stdLat k κ) := fun i => by
  rw [stdLat, smul_diagLat]
  exact fun j => by simpa using hx j i
end GlobalTheory.FunObj.FiniteSupport
