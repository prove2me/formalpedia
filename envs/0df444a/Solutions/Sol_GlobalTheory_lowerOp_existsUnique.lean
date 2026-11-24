-- Prove2me | solution 1 for GlobalTheory.lowerOp_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:19:03.284147+00:00
-- url     : https://prove2.me/submissions/e1e68906-d2cb-4bee-9f99-c5df9e9fd8e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodValuationBound
import Theorems.Thm_GlobalTheory_inK_injective_of_free
import Theorems.Thm_GlobalTheory_existsUnique_endo_line
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ i, ∃! N, IsLower ρ (φ i) (e i) (f i) N := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ _ D _ _ I _ φ _ H _ _ ρ Fil B hLat hEig e f hGen i
  haveI : Module.Free O H := hLat.1
  have hmem : e i ∈ eigLat ρ (φ i) := by rw [(hGen i).1]; exact Submodule.mem_span_singleton_self _
  have hv : inK (O := O) K H (e i) ∈ eigK ρ (φ i) := hmem
  have he0 : e i ≠ 0 := by
    obtain ⟨g, hg0, hgs⟩ := (hEig.2.1 (φ i)).2.1
    intro h
    apply hg0
    have : g ∈ eigLat ρ (φ i) := hgs ▸ Submodule.mem_span_singleton_self g
    rw [(hGen i).1, h] at this
    simpa using this
  have hv0 : inK (O := O) K H (e i) ≠ 0 := fun h => he0 (inK_injective_of_free (O := O) K H (h.trans (map_zero (inK (O := O) K H)).symm))
  have key := existsUnique_endo_line (eigK ρ) hEig.1 (φ i) (inK K H (e i)) (inK K H (f i)) hv hv0 (hLat.2.2.2.1 (φ i))
  unfold IsLower
  exact key
end GlobalTheory
