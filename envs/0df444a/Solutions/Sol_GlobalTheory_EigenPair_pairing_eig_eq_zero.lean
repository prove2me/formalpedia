-- Prove2me | solution 1 for GlobalTheory.EigenPair.pairing_eig_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:08:09.121581+00:00
-- url     : https://prove2.me/submissions/c2a6de01-fb2e-44a8-877b-df6282101cd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralFifth
import Theorems.Thm_GlobalTheory_EigenPair_exists_sep
import Theorems.Thm_GlobalTheory_EigenPair_adj_baseChange

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
namespace GlobalTheory.EigenPair
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → ∀ σ σ' : E →+* K, σ' ≠ bar σ → ∀ x ∈ eigK ρ σ, ∀ y ∈ eigK ρ σ', B.baseChange K x y = 0 := by
  intro E _ _ _ c hc l _ O _ _ _ _ K _ _ _ _ _ D _ _ I _ φ _ H _ _ ρ Fil B hL σ σ' hne x hx y hy
  haveI : CharZero K := by
    refine ⟨fun m n hmn => ?_⟩
    rw [← map_natCast (algebraMap O K), ← map_natCast (algebraMap O K) n] at hmn
    exact Nat.cast_injective (IsFractionRing.injective O K hmn)
  obtain ⟨a, b, hab, hsep⟩ := GlobalTheory.EigenPair.exists_sep c hc σ σ' hne
  have hadj := hL.2.2.2.2.2.2.2.2 a b hab
  have hxa : (ρ a).baseChange K x = σ a • x :=
    Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hx a)
  have hyb : (ρ b).baseChange K y = σ' b • y :=
    Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hy b)
  have key := GlobalTheory.EigenPair.adj_baseChange B (ρ a) (ρ b) hadj x y
  rw [hxa, hyb, LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul] at key
  have h2 : (σ a - σ' b) * B.baseChange K x y = 0 := by rw [sub_mul, key, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hsep)
end GlobalTheory.EigenPair
