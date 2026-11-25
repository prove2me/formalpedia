-- Prove2me | solution 1 for GlobalTheory.torsion_invariant_descends
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:47:15.669816+00:00
-- url     : https://prove2.me/submissions/6ae97e0f-c94f-4ec0-af23-7cc8d530301b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Theorems.Thm_GlobalTheory_existsUnique_descend_of_torsion_invariant

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
    (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n →
      IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧
        (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ),
      (n : K) ≠ 0 → ∀ (U : P.A.left.Opens) (f : Γ(P.A.left, (mulA P.A n).left ⁻¹ᵁ U)),
      (∀ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A, y ^ n = 1 →
        ∀ (e : (mulA P.A n).left ⁻¹ᵁ U ≤
          ((toUnit P.A ≫ y) * 𝟙 P.A).left ⁻¹ᵁ ((mulA P.A n).left ⁻¹ᵁ U)),
          (((toUnit P.A ≫ y) * 𝟙 P.A).left.appLE _ _ e).hom f = f) →
      ∃! g : Γ(P.A.left, U), ((mulA P.A n).left.app U).hom g = f := by
  intro H K _ _ P n hn U f hf
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr fun h => hn (by rw [h, Nat.cast_zero])
  obtain ⟨h1, -, h3, h4⟩ := H _ P n hn1
  have : Etale (mulA P.A n).left := h4 (by
    simpa using (Ne.isUnit hn).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
  have : IsCommMonObj P.A := P.isAb.comm
  exact existsUnique_descend_of_torsion_invariant P.A n U f hf
end GlobalTheory
