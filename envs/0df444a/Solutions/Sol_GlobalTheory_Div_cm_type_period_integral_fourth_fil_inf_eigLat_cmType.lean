-- Prove2me | solution 1 for GlobalTheory.Div.cm_type_period_integral_fourth.fil_inf_eigLat_cmType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:51:26.97698+00:00
-- url     : https://prove2.me/submissions/08c46d83-30dc-4cdf-9164-0fbba72f6416

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralFourth
import Theorems.Thm_GlobalTheory_Div_cm_type_period_integral_fourth_exists_smul_mem_of_tmul_mem_baseChange

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
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.cm_type_period_integral_fourth
namespace GlobalTheory.Div.cm_type_period_integral_fourth
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → ∀ i, Fil ⊓ eigLat ρ (φ i) = eigLat ρ (φ i) := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ _ D _ _ I _ φ _ H _ _ ρ Fil B hL i
  refine inf_eq_right.2 fun h hh => ?_
  obtain ⟨-, -, -, -, hsat, hbc, -⟩ := hL
  have h1 : inK K H h ∈ Fil.baseChange K := by
    rw [hbc]
    exact le_iSup (fun j => eigK ρ (φ j)) i hh
  obtain ⟨d, hd, hdh⟩ := exists_smul_mem_of_tmul_mem_baseChange Fil h h1
  exact hsat d h hd hdh
end GlobalTheory.Div.cm_type_period_integral_fourth
