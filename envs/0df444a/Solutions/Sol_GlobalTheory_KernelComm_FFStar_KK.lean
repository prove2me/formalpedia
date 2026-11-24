-- Prove2me | solution 1 for GlobalTheory.KernelComm.FFStar_KK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:26:13.801994+00:00
-- url     : https://prove2.me/submissions/d0b86e6f-d075-4665-9155-f6a47b9b0b50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Theorems.Thm_GlobalTheory_KernelComm_U_KK
import Theorems.Thm_GlobalTheory_KernelComm_KK_dia
import Theorems.Thm_GlobalTheory_KernelComm_KK_ram
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
open GlobalTheory GlobalTheory.KernelComm
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}
variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
variable {V' V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]
  {μ : kˣ →* ℂˣ} {π' : Representation ℂ (GL n' k) V'} {π : Representation ℂ (GL n k) V}
  {θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V}
  (hμ : IsUnram μ) (hθ : IsEquivTheta μ π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n)
namespace GlobalTheory.KernelComm
theorem _root_.solution {t : ℕ} (ht : Fintype.card n = Fintype.card n' + (t + 1)) (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
    {φ : Form k n' V'} (hφ : φ ∈ EqForm π') (h : φ ∈ Mram k n' V') :
    FFStar q χ (KK hμ hθ P₀ Q₀ φ) = scal k t • KK hμ hθ P₀ Q₀ (FFStar q χ φ) := by
  have h1 : GsStar χ (KK hμ hθ P₀ Q₀ φ) = KK hμ hθ P₀ Q₀ (GsStar χ φ) := by
    simp only [GsStar, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, KK_dia hμ hθ P₀ Q₀ _ hφ]
  have h2 : GsStar χ φ ∈ EqForm π' := by
    simp only [GsStar, LinearMap.sum_apply, LinearMap.smul_apply]
    exact sum_mem fun c _ => Submodule.smul_mem _ _ (dia_mem_EqForm _ hφ)
  rw [FFStar_eq_U_GsStar q χ h, FFStar_eq_U_GsStar q χ (KK_ram hμ hθ P₀ Q₀ hφ h), h1, U_KK hμ hθ P₀ Q₀ ht q h2]
end GlobalTheory.KernelComm
