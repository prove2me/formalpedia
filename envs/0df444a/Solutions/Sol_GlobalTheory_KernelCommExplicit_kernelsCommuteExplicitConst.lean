-- Prove2me | solution 1 for GlobalTheory.KernelCommExplicit.kernelsCommuteExplicitConst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:27:55.893177+00:00
-- url     : https://prove2.me/submissions/f039f69c-6254-462a-b264-d7e791683774

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelsCommuteTwisted
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelsCommuteExplicitConst
import Theorems.Thm_GlobalTheory_KernelCommTw_KK_FFStar
import Theorems.Thm_GlobalTheory_KernelCommTw_KK_dia
import Theorems.Thm_GlobalTheory_KernelCommTw_KK_mem
import Theorems.Thm_GlobalTheory_KernelCommTw_KK_ram
import Theorems.Thm_GlobalTheory_KernelCommTw_KK_smul
import Theorems.Thm_GlobalTheory_KernelComm_KK_dia
import Theorems.Thm_GlobalTheory_KernelComm_KK_mem
import Theorems.Thm_GlobalTheory_KernelComm_KK_ram
import Theorems.Thm_GlobalTheory_KernelComm_KK_smul
import Theorems.Thm_GlobalTheory_LatPair_FFStar_mem_EqForm
import Theorems.Thm_GlobalTheory_LatPair_dia_mem_EqForm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.KernelCommTw
noncomputable section
open GlobalTheory GlobalTheory.KernelCommExplicit
namespace GlobalTheory.KernelCommExplicit
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (l' l : kˣ →* ℂˣ), IsUnram l' → IsUnram l → ∀ (P₀ : Pair k n') (Q₀ : Pair k n), ∀ (V' V : Type) [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V] (π' : Representation ℂ (GL n' k) V') (π : Representation ℂ (GL n k) V) (θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V), (∀ (g : GL n' k) (h : GL n k) (v : V') (Ψ Ψ' : SB (Matrix n n' k)), (∀ x, Ψ'.1 x = (l' (Matrix.GeneralLinearGroup.det g) : ℂ) * (l (Matrix.GeneralLinearGroup.det h) : ℂ) * Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (π' g v) Ψ' = π h (θ v Ψ)) → ∃ K : EqForm π' →ₗ[ℂ] EqForm π, (∀ φ, (K φ).1 Q₀ = θ (φ.1 P₀) (phiOneSB P₀ Q₀)) ∧ (∀ (s : 𝓀[k]ˣ) φ, (K ⟨dia s φ.1, dia_mem_EqForm s φ.2⟩).1 = dia s (K φ).1) ∧ ∀ φ : EqForm π', φ.1 ∈ Mram k n' V' → (K φ).1 ∈ Mram k n V ∧ (K ⟨FFStar q (resChar ψ hψ q) φ.1, FFStar_mem_EqForm q _ φ.2⟩).1 = ((l' q.unit : ℂ) * (l q.unit : ℂ)) • FFStar q (resChar ψ hψ q) (K φ).1 := by
  intro k _ _ _ _ n n' _ _ _ _ q ψ hψ l' l hl' hl P₀ Q₀ V' V _ _ _ _ π' π θ hθ
  refine ⟨LinearMap.codRestrict (EqForm π) (KK hl hθ P₀ Q₀ ∘ₗ (EqForm π').subtype)
    fun φ => KK_mem hl hθ P₀ Q₀ φ.1, fun φ => ?_, fun s φ => KK_dia hl hθ P₀ Q₀ hl' s φ.2, fun φ h =>
      ⟨KK_ram hl hθ P₀ Q₀ hl' φ.2 h, KK_FFStar hl hθ P₀ Q₀ hl' q _ φ.2 h⟩⟩
  show KK hl hθ P₀ Q₀ φ.1 Q₀ = _
  simpa using KK_smul hl hθ P₀ Q₀ φ.1 1
end GlobalTheory.KernelCommExplicit
