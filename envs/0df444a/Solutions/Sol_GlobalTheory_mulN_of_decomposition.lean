-- Prove2me | solution 1 for GlobalTheory.mulN_of_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:41:32.045963+00:00
-- url     : https://prove2.me/submissions/3a96db59-6f49-49cb-b0f7-1f58feaa4f54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NatCardEqOfEquivPiField
import Theorems.Thm_GlobalTheory_MulLaw_natCard_eq_of_equiv_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n j : ℕ), (n : K) ≠ 0 → 1 ≤ j → Nonempty (SecM P.A P.L ((n ^ 2 * j : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K))) ≃ₗ[Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)] ({x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A // x ^ n = 1} → SecM P.A P.L (j : ℤ) (baseOver (Spec (CommRingCat.of K)))))) → GlobalSectionsRankAlgClosed → PolBaseChangeSt → MulNSt := by
  intro hQ hRel hH hBC S _ P n hn
  obtain ⟨h1, h2, h3, h4⟩ := hQ S P n hn
  refine ⟨h1, h2, h3, h4, fun k _ _ t hk => ?_⟩
  obtain ⟨P', g, hg, hdim, hmul, -⟩ := hBC S _ t P
  obtain ⟨e⟩ := hRel k P' n 1 hk le_rfl
  have hn2 : 1 ≤ n ^ 2 * 1 := by
    rw [Nat.mul_one]; exact Nat.one_le_pow _ _ hn
  have hU := hH k P' (n ^ 2 * 1) hn2
  have hV := hH k P' 1 le_rfl
  rw [one_pow] at hV
  have hF : IsField Γ((baseOver (Spec (CommRingCat.of k))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)
  have hcard := MulLaw.natCard_eq_of_equiv_pi hF e (Nat.pow_pos hn2) hU hV
  have φ : (baseOver (Spec (CommRingCat.of k)) ⟶ P'.A) ≃* (Over.mk t ⟶ P.A) := by
    have ψ := MulLaw.basePointsEquiv hg hmul (baseOver (Spec (CommRingCat.of k)))
    have ht : (baseOver (Spec (CommRingCat.of k))).hom ≫ t = t := Category.id_comp t
    rw [ht] at ψ
    exact ψ
  rw [← Nat.card_congr (φ.toEquiv.subtypeEquiv
    (p := fun x => x ^ n = 1) (q := fun x => x ^ n = 1) (fun x => by
      show x ^ n = 1 ↔ φ x ^ n = 1
      rw [← map_pow, map_eq_one_iff φ φ.injective])), hcard, hdim, Nat.mul_one, ← pow_mul]
end GlobalTheory
