-- Prove2me | solution 1 for GlobalTheory.T.cm_type_period_galois_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:05:30.132847+00:00
-- url     : https://prove2.me/submissions/cef10db9-f3c3-4ced-b0b3-cc449f110eb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodGaloisIntegral
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodGaloisIntegralStatement
import Theorems.Thm_GlobalTheory_CMFormBound_formClaims


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → (∀ i, 0 ≤ val_vp O l (algebraMap O K (B (e i) (f i))) ∧ val_vp O l (algebraMap O K (B (e i) (f i))) ≤ val_vp O l (algebraMap O K D)) → (∃! ρE : E →+* Module.End K (K ⊗[O] H), ∀ a : orderC c, ρE a = (ρ a).baseChange K) → FormClaims l φ ρ B D e f := by
  first | exact @GlobalTheory.CMFormBound.formClaims | exact GlobalTheory.CMFormBound.formClaims | (intros; apply GlobalTheory.CMFormBound.formClaims <;> assumption)
end _root_.GlobalTheory.T
