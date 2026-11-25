-- Prove2me | solution 1 for GlobalTheory.DetBound.detClaims
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:54:29.299732+00:00
-- url     : https://prove2.me/submissions/b655304e-b8dd-4f15-a048-ae6dd2f4eace

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodTraceIntegral
import Theorems.Thm_GlobalTheory_DetBound_exists_wedge_generator
import Theorems.Thm_GlobalTheory_DetBound_exists_wedge_eq_smul_dvd
import Theorems.Thm_GlobalTheory_DetBound_val_bounds_of_dvd
import Theorems.Thm_GlobalTheory_DetBound_gens_mem_linearIndependent
import Theorems.Thm_GlobalTheory_DetBound_smul_mem_span_gens

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
open GlobalTheory GlobalTheory.DetBound
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
namespace GlobalTheory.DetBound
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → DetClaims K l Fil D e := by
  intro E _ _ _ c _ l hl O _ _ _ _ K _ _ _ hlm _ D hD _ I _ φ hφ H _ _ ρ Fil B hL hE e f hG
  haveI : Module.Free O H := hL.1
  haveI : Module.Finite O H := hL.2.1
  obtain ⟨hmem, hli⟩ := gens_mem_linearIndependent hφ hL hE hG
  let e₀ : I → Fil := fun i => ⟨e i, hmem i⟩
  have he₀ : ∀ i, (e₀ i : H) = e i := fun i => rfl
  have hli₀ : LinearIndependent O e₀ := LinearIndependent.of_comp Fil.subtype hli
  have hrank : Module.finrank O Fil = Fintype.card I := by
    apply le_antisymm
    · let g : Fil →ₗ[O] Submodule.span O (Set.range e₀) :=
        ((LinearMap.lsmul O Fil D).codRestrict _ (fun x => smul_mem_span_gens hφ hL hE hG e₀ he₀ x))
      have hg : Function.Injective g := by
        intro x y hxy
        have : D • x = D • y := congrArg Subtype.val hxy
        exact smul_right_injective _ hD this
      exact (LinearMap.finrank_le_finrank_of_injective hg).trans (finrank_range_le_card e₀)
    · exact hli₀.fintype_card_le_finrank
  refine ⟨inferInstance, hrank, hmem, exists_wedge_generator hrank, ?_⟩
  intro ω hω s e' he'
  obtain ⟨u, hu, hdvd⟩ := exists_wedge_eq_smul_dvd hrank (fun j => e' (s j)) D (by
    intro x
    have h := smul_mem_span_gens hφ hL hE hG e' he' x
    have : Set.range (fun j => e' (s j)) = Set.range e' := s.surjective.range_comp e'
    rw [this]; exact h) ω hω
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  exact ⟨u, hu, val_bounds_of_dvd O K l hl0 hlm u D _ hD hdvd⟩
end GlobalTheory.DetBound
