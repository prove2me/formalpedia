-- Prove2me | solution 1 for GlobalTheory.SteinitzProd.steinitz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:52:10.413924+00:00
-- url     : https://prove2.me/submissions/7208d55f-e6c9-48e7-a9d6-3a1185b9899a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FinitelyManyIsoClassesProjectiveNumberField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SteinitzPiIdealsLinearEquivOfClassGroupProd
import Theorems.Thm_GlobalTheory_SteinitzProd_exists_pi_equiv
import Theorems.Thm_GlobalTheory_ProjModFinIso_nonempty_equiv_of_mk0_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SteinitzProd
variable {R : Type} [CommRing R] [IsDedekindDomain R]
namespace GlobalTheory.SteinitzProd
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (ι : Type) [Fintype ι]
    (I J : ι → (Ideal R)⁰), ∏ i, ClassGroup.mk0 (I i) = ∏ i, ClassGroup.mk0 (J i) →
    Nonempty (((i : ι) → (I i : Ideal R)) ≃ₗ[R] ((i : ι) → (J i : Ideal R))) := by
  intro R _ _ ι _ I J h
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := ι))
  let e : ι ≃ Fin (n + 1) := (Fintype.equivFin ι).trans (finCongr hn)
  obtain ⟨L, hL, ⟨f⟩⟩ := exists_pi_equiv e I
  obtain ⟨L', hL', ⟨f'⟩⟩ := exists_pi_equiv e J
  obtain ⟨g⟩ := GlobalTheory.ProjModFinIso.nonempty_equiv_of_mk0_eq (R := R) (I := L) (J := L')
    (by rw [hL, hL', h])
  exact ⟨f ≪≫ₗ g.prodCongr (LinearEquiv.refl R _) ≪≫ₗ f'.symm⟩
end GlobalTheory.SteinitzProd
