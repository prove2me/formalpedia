-- Prove2me | solution 1 for GlobalTheory.KernelCommTw.FFStar_KK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:54:44.351768+00:00
-- url     : https://prove2.me/submissions/7e40c290-3d93-43c1-b124-6f073a81226c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelsCommuteTwisted
import Theorems.Thm_GlobalTheory_KernelCommTw_U_KK
import Theorems.Thm_GlobalTheory_KernelCommTw_KK_dia
import Theorems.Thm_GlobalTheory_KernelCommTw_KK_ram
import Theorems.Thm_GlobalTheory_KernelComm_KK_dia
import Theorems.Thm_GlobalTheory_KernelComm_KK_ram
import Theorems.Thm_GlobalTheory_KernelComm_U_KK
import Theorems.Thm_GlobalTheory_LatPair_dia_mem_EqForm
import Theorems.Thm_GlobalTheory_PairOp_FFStar_eq_U_GsStar


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
open GlobalTheory GlobalTheory.KernelCommTw
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {V' V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]
variable {l' l : kˣ →* ℂˣ} {π' : Representation ℂ (GL n' k) V'} {π : Representation ℂ (GL n k) V}
  {θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V}
variable (hl : IsUnram l) (hθ : IsTwEquiv l' l π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n)
namespace GlobalTheory.KernelCommTw
theorem _root_.solution (hl' : IsUnram l') (q : Unif k) (χ : AddChar 𝓀[k] ℂ) {φ : Form k n' V'} (hφ : φ ∈ EqForm π')
    (h : φ ∈ Mram k n' V') :
    FFStar q χ (KK hl hθ P₀ Q₀ φ) = ((l' q.unit : ℂ) * (l q.unit : ℂ))⁻¹ • KK hl hθ P₀ Q₀ (FFStar q χ φ) := by
  have h1 : GsStar χ (KK hl hθ P₀ Q₀ φ) = KK hl hθ P₀ Q₀ (GsStar χ φ) := by
    simp only [GsStar, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, KK_dia hl hθ P₀ Q₀ hl' _ hφ]
  have h2 : GsStar χ φ ∈ EqForm π' := by
    simp only [GsStar, LinearMap.sum_apply, LinearMap.smul_apply]
    exact sum_mem fun c _ => Submodule.smul_mem _ _ (dia_mem_EqForm _ hφ)
  rw [FFStar_eq_U_GsStar q χ h, FFStar_eq_U_GsStar q χ (KK_ram hl hθ P₀ Q₀ hl' hφ h), h1,
    U_KK hl hθ P₀ Q₀ hl' q h2]
end GlobalTheory.KernelCommTw
