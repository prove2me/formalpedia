-- Prove2me | solution 1 for GlobalTheory.DivLin.nilPart_claims
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:12.050381+00:00
-- url     : https://prove2.me/submissions/bc0b634d-b6ca-4dea-b351-546f55b42408

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScaledRestrictionEndomorphisms
import Theorems.Thm_GlobalTheory_DivLin_restr_mul_eq_zero
import Theorems.Thm_GlobalTheory_DivLin_restr_commute
import Theorems.Thm_GlobalTheory_DivLin_restr_skew
import Theorems.Thm_GlobalTheory_DivLin_restr_iso
import Theorems.Thm_GlobalTheory_DivLin_nilPart_eq
import Theorems.Thm_GlobalTheory_DivLin_nilPart_sq
import Theorems.Thm_GlobalTheory_DivLin_nilPart_commute
import Theorems.Thm_GlobalTheory_DivLin_nilPart_skew
import Theorems.Thm_GlobalTheory_DivLin_nilPart_iso
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
open GlobalTheory GlobalTheory.DivLin
namespace GlobalTheory.DivLin
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (O : Type) [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] (H : Type) [AddCommGroup H] [Module O H], Module.Free O H → ∀ (ρ : orderC c →+* Module.End O H) (B : LinearMap.BilinForm O H) (I : Type) [Fintype I] (N : I → Module.End K (K ⊗[O] H)) (D : O) (M : I → Module.End O H), (∀ i, IsScaledRestr D (N i) (M i)) → (∀ i (a : OF E), Commute (N i) ((ρ (ofF c a)).baseChange K)) → (∀ i j, N i * N j = 0) → (∀ i x y, B.baseChange K (N i x) y + B.baseChange K x (N i y) = 0) → (∀ i j x y, B.baseChange K (N i x) (N j y) = 0) → ∀ (l : ℕ) (R : Type) [CommRing R] [Algebra O R] (t : I → R), (∀ x : R ⊗[O] H, ∃ y : R ⊗[O] H, (1 + nilPart l M R t) x = x + (lPrime l : R) • y) ∧ ((1 + nilPart l M R t) * (1 - nilPart l M R t) = 1 ∧ (1 - nilPart l M R t) * (1 + nilPart l M R t) = 1) ∧ (∀ a : OF E, Commute (1 + nilPart l M R t) ((ρ (ofF c a)).baseChange R)) ∧ ∀ x y : R ⊗[O] H, B.baseChange R ((1 + nilPart l M R t) x) ((1 + nilPart l M R t) y) = B.baseChange R x y := by
  intro E _ _ _ c O _ _ K _ _ _ H _ _ hfree ρ B I _ N D M hMN hcomm hNN hskew hiso l R _ _ t
  haveI := hfree
  have hMM : ∀ i j, M i * M j = 0 := fun i j => restr_mul_eq_zero (hMN i) (hMN j) (hNN i j)
  have hMρ : ∀ (a : OF E) i, Commute (M i) (ρ (ofF c a)) := fun a i => restr_commute _ (hMN i) (hcomm i a)
  have hMskew : ∀ i x y, B (M i x) y + B x (M i y) = 0 := fun i => restr_skew B (hMN i) (hskew i)
  have hMiso : ∀ i j x y, B (M i x) (M j y) = 0 := fun i j => restr_iso B (hMN i) (hMN j) (hiso i j)
  have hnn := nilPart_sq R hMM l t
  refine ⟨fun x => ⟨(∑ i, t i • (M i).baseChange R) x, ?_⟩, ⟨?_, ?_⟩, fun a => ?_, fun x y => ?_⟩
  · rw [LinearMap.add_apply, Module.End.one_apply, nilPart_eq, LinearMap.smul_apply]
  · rw [add_mul, one_mul, mul_sub, mul_one, hnn]; abel
  · rw [sub_mul, one_mul, mul_add, mul_one, hnn]; abel
  · exact (Commute.one_left _).add_left (nilPart_commute R _ (hMρ a) l t)
  · simp only [LinearMap.add_apply, Module.End.one_apply, map_add]
    linear_combination nilPart_skew R B hMskew hMiso l t x y + nilPart_iso R B hMskew hMiso l t x y
end GlobalTheory.DivLin
