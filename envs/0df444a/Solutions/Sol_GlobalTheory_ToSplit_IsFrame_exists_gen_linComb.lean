-- Prove2me | solution 1 for GlobalTheory.ToSplit.IsFrame.exists_gen_linComb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:48:23.809115+00:00
-- url     : https://prove2.me/submissions/8cc79412-25b3-432b-85e7-1a2ccaee636f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtension
import Theorems.Thm_GlobalTheory_ToSplit_exists_gen_descent
import Theorems.Thm_GlobalTheory_ToSplit_inv_eq_div_mul_inv
import Theorems.Thm_GlobalTheory_ToSplit_prod_erase_one_perm_apply_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ToSplit
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
  {q : G ⟶ B} {i : splitTorus S X ⟶ G} [IsMonHom q] [IsMonHom i]
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
  (hk : IsPullback i (toUnit _) q (η[B]))
include hk
omit hk [IsMonHom q] [IsMonHom i] [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
namespace GlobalTheory.ToSplit
namespace IsFrame
theorem _root_.solution {χ : X} {O : RigLB B}
    {u : ∀ j, Γ(G.left, q.left ⁻¹ᵁ O.L.U j)ˣ} (h : IsFrame q i χ O u) {Y Y' : Over S} (π : Y' ⟶ Y)
    [Flat π.left] [Surjective π.left] [QuasiCompact π.left] {K : Type} [Fintype K]
    (φ : K → (Y.left ⟶ B.left)) (ψ : K → (Y' ⟶ G)) (ε : K → ℤ)
    (hψ : ∀ I, (ψ I).left ≫ q.left = π.left ≫ φ I)
    (hinv : ∀ (Z : Over S) (g₁ g₂ : Z ⟶ Y') (z : Z.left), g₁ ≫ π = g₂ ≫ π →
      ∃ t : K → (Z ⟶ splitTorus S X), (∀ I, g₁ ≫ ψ I = (t I ≫ i) * (g₂ ≫ ψ I)) ∧
        ∏ I, charGerm z (t I) (Multiplicative.ofAdd χ) ^ ε I = 1) :
    ∃ t : LB.Gen (LB.LinComb O.L φ ε), t.IsGen := by
  have hm : ∀ (j : K → O.L.ι) (y : Y'.left), π.left y ∈ LB.wchart O.L φ j →
      ∀ I, q.left ((ψ I).left y) ∈ O.L.U (j I) := fun j y hy I => by
    have : (π.left ≫ φ I) y ∈ O.L.U (j I) := LB.wchart_le O.L φ j I hy
    rwa [← hψ] at this
  have le : ∀ (j : K → O.L.ι) (I : K),
      π.left ⁻¹ᵁ LB.wchart O.L φ j ≤ (ψ I).left ⁻¹ᵁ (q.left ⁻¹ᵁ O.L.U (j I)) :=
    fun j I y hy => hm j y hy I
  obtain ⟨f, hf⟩ : ∃ f : ∀ j : K → O.L.ι, Γ(Y'.left, π.left ⁻¹ᵁ LB.wchart O.L φ j)ˣ,
      ∀ (j : K → O.L.ι) (Z : Scheme.{0}) (r : Z ⟶ Y'.left) (z : Z),
        π.left (r z) ∈ LB.wchart O.L φ j →
        gm r z _ (f j) = ∏ I, (gm (r ≫ (ψ I).left) z _ (u (j I)))⁻¹ ^ ε I := by
    refine ⟨fun j => ∏ I, (res (le j I) (pullU (ψ I).left _ (u (j I))))⁻¹ ^ ε I,
      fun j Z r z hz => ?_⟩
    refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun I _ => ?_)
    rw [map_zpow, map_inv, gm_res_pull r _ z (le j I) hz]
  refine exists_gen_descent π (LB.LinComb O.L φ ε) f (fun j Z g₁ g₂ z e h₁ h₂ => ?_)
    (fun j j' y h₁ h₂ => ?_)
  · obtain ⟨t, hI, h1⟩ := hinv Z g₁ g₂ z e
    have hc : ∀ I : K, gm (g₁.left ≫ (ψ I).left) z _ (u (j I)) =
        charGerm z (t I) (Multiplicative.ofAdd χ) * gm (g₂.left ≫ (ψ I).left) z _ (u (j I)) :=
      fun I => by
        have := h.1 (j I) Z (t I) (g₂ ≫ ψ I) z (hm j _ h₂ I)
        rw [← hI] at this
        exact this
    refine (hf j _ _ z h₁).trans (Eq.trans ?_ (hf j _ _ z h₂).symm)
    rw [Finset.prod_congr rfl fun I _ => congrArg (·⁻¹ ^ ε I) (hc I)]
    exact prod_erase_one_perm_apply_eq_zero _ _ _ h1
  · refine (hf j _ (𝟙 _) y h₁).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      (gm_linComb O.L φ ε π.left y j j' h₁ h₂) (hf j' _ (𝟙 _) y h₂)).symm)
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun I _ => ?_
    rw [← mul_zpow, ← hψ, h.2.1 _ _ _ (ψ I).left y (hm j y h₁ I) (hm j' y h₂ I), Category.id_comp,
      ← inv_eq_div_mul_inv]
end IsFrame
end GlobalTheory.ToSplit
