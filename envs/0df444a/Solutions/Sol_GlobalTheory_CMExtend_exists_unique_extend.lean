-- Prove2me | solution 1 for GlobalTheory.CMExtend.exists_unique_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:18:41.273195+00:00
-- url     : https://prove2.me/submissions/d5a78591-4d94-4d0f-86dd-c098029e92bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodNormIntegral
import Theorems.Thm_GlobalTheory_CMExtend_extHom_apply
import Theorems.Thm_GlobalTheory_CMExtend_ringHom_ext_orderC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.CMExtend
namespace GlobalTheory.CMExtend
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → (∃! ρE : E →+* Module.End K (K ⊗[O] H), ∀ a : orderC c, ρE a = (ρ a).baseChange K) := by
  intro E _ _ _ c hc l hl O _ _ _ _ K _ _ _ hlm hcard D hD hcl I _ φ hφ H _ _ ρ Fil B hlat heig
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective O K)
  refine ⟨extHom K hc ((baseChangeRingHom O K H).comp ρ), fun a => extHom_apply hc _ a, ?_⟩
  intro f hf
  exact ringHom_ext_orderC hc f _ fun a => by rw [hf a, extHom_apply hc _ a]; rfl
end GlobalTheory.CMExtend
