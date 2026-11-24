-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliAdj.hasAdj_qdet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:54:13.720856+00:00
-- url     : https://prove2.me/submissions/75c42081-d559-4c65-9c6f-c16d026bfd97

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetOppositeNegStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetAdjointForm
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAdj_HasAdj_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAdj_HasAdj_ofFn
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAdj_HasAdj_tm
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAdj_HasAdj_intCast
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAdj_HasAdj_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CapelliAdj
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.CapelliAdj
theorem _root_.solution {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {n : ℕ} {X Y : Fin n → Fin n → Module.End ℂ V}
    (h : ∀ (i j : Fin n) (φ ψ : V), B (X i j φ) ψ = -B φ (Y i j ψ)) (v : ℂ) :
    HasAdj B (qdet X v)
      (MulOpposite.unop (qdet (fun a b => MulOpposite.op (-Y a b)) ((starRingEnd ℂ) v))) := by
  unfold qdet qminor
  have e : ∀ (F : Equiv.Perm (Fin n) → (Module.End ℂ V)ᵐᵒᵖ),
      MulOpposite.unop (∑ σ, F σ) = ∑ σ, MulOpposite.unop (F σ) := fun F =>
    map_sum (MulOpposite.opAddEquiv.symm : (Module.End ℂ V)ᵐᵒᵖ ≃+ Module.End ℂ V) F Finset.univ
  rw [e]
  refine HasAdj.sum _ _ _ fun σ _ => ?_
  rw [MulOpposite.unop_mul, MulOpposite.unop_intCast]
  refine (HasAdj.intCast B _).mul ?_
  apply HasAdj.ofFn
  intro k
  have hk := HasAdj.tm h (v - ((k : ℕ) : ℂ)) (σ k) k
  simpa [map_sub, map_natCast] using hk
end GlobalTheory.CompanionTheory.CapelliAdj
