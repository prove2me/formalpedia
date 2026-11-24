-- Prove2me | solution 1 for GlobalTheory.JR.SplitEt.algebraMap_norm_eq_mul_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:09:44.605572+00:00
-- url     : https://prove2.me/submissions/9501ff30-d69c-47bb-8be6-8784bba8849c

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSplitEtaleHermitianPairIsometry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SplitEt
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]
namespace GlobalTheory.JR.SplitEt
theorem _root_.solution (z : E) : algebraMap F E (Algebra.norm F z) = z * star z := by
  have h2 : Module.finrank F E = 2 := Unram.finrank_eq
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let σ : E ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := starRingAut)
    (fun x => by rw [starRingAut_apply]; exact Unram.star_fix (E := E) x)
  have hσz : ∀ y, σ y = star y := fun y => rfl
  have hσ : (1 : E ≃ₐ[F] E) ≠ σ := by
    obtain ⟨y, hy⟩ := Unram.star_ne (F := F) (E := E)
    intro h
    apply hy
    rw [← hσz, ← h]
    rfl
  classical
  have hle := AlgEquiv.card_le (F := F) (K := E)
  have hge : ({1, σ} : Finset (E ≃ₐ[F] E)).card ≤ Fintype.card (E ≃ₐ[F] E) := Finset.card_le_univ _
  rw [Finset.card_pair hσ] at hge
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by omega
  haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card, hcard, h2])
  have huniv : ({1, σ} : Finset (E ≃ₐ[F] E)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [Finset.card_pair hσ, hcard])
  rw [Algebra.norm_eq_prod_automorphisms, ← huniv, Finset.prod_pair hσ, hσz]
  rfl
end GlobalTheory.JR.SplitEt
