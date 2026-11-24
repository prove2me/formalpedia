-- Prove2me | solution 1 for GlobalTheory.T.cm_type_period_integral_third
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:05:27.833805+00:00
-- url     : https://prove2.me/submissions/425dae01-293f-4b24-bd88-7ed47ba56ba3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralThird
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralThirdStatement
import Theorems.Thm_GlobalTheory_EigenLattice_iSupIndep_and_smul_mem_iSup


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ) → iSupIndep (fun σ : E →+* K => eigLat ρ σ) ∧ ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ := by
  first | exact @GlobalTheory.EigenLattice.iSupIndep_and_smul_mem_iSup | exact GlobalTheory.EigenLattice.iSupIndep_and_smul_mem_iSup | (intros; apply GlobalTheory.EigenLattice.iSupIndep_and_smul_mem_iSup <;> assumption)
end _root_.GlobalTheory.T
