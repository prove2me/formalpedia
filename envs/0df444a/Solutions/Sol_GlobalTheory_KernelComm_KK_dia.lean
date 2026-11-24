-- Prove2me | solution 1 for GlobalTheory.KernelComm.KK_dia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:58:04.137195+00:00
-- url     : https://prove2.me/submissions/dc04f94e-c5a7-4877-92bf-295aecb8e89a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Theorems.Thm_GlobalTheory_KernelComm_KK_mem
import Theorems.Thm_GlobalTheory_KernelComm_eq_of_base
import Theorems.Thm_GlobalTheory_KernelComm_KK_same
import Theorems.Thm_GlobalTheory_LatPair_dia_mem_EqForm
import Theorems.Thm_GlobalTheory_LatPair_phiOne_dia


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.PairOp
noncomputable section
open GlobalTheory GlobalTheory.KernelComm
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}
variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
variable {V' V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]
  {μ : kˣ →* ℂˣ} {π' : Representation ℂ (GL n' k) V'} {π : Representation ℂ (GL n k) V}
  {θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V}
  (hμ : IsUnram μ) (hθ : IsEquivTheta μ π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n)
namespace GlobalTheory.KernelComm
theorem _root_.solution (s : 𝓀[k]ˣ) {φ : Form k n' V'} (hφ : φ ∈ EqForm π') :
    KK hμ hθ P₀ Q₀ (dia s φ) = dia s (KK hμ hθ P₀ Q₀ φ) := by
  refine eq_of_base Q₀ (KK_mem hμ hθ P₀ Q₀ _) (dia_mem_EqForm s (KK_mem hμ hθ P₀ Q₀ φ)) ?_
  rw [dia_apply, KK_same hμ hθ P₀ Q₀ hφ (P := s • P₀) (Q := s • Q₀) rfl rfl,
    KK_same hμ hθ P₀ Q₀ (dia_mem_EqForm s hφ) rfl rfl, dia_apply]
  congr 1
  exact Subtype.ext (phiOne_dia s).symm
end GlobalTheory.KernelComm
