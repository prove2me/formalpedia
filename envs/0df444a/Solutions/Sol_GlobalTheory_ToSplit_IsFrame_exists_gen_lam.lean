-- Prove2me | solution 1 for GlobalTheory.ToSplit.IsFrame.exists_gen_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:01:46.294115+00:00
-- url     : https://prove2.me/submissions/47570aec-c641-486f-913b-1c9144820c5f

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
import Theorems.Thm_GlobalTheory_ToSplit_exists_act
import Theorems.Thm_GlobalTheory_ToSplit_comp_psum
import Theorems.Thm_GlobalTheory_ToSplit_psum_comp
import Theorems.Thm_GlobalTheory_ToSplit_psum_mul
import Theorems.Thm_GlobalTheory_ToSplit_prod_square_eq_one
import Theorems.Thm_GlobalTheory_ToSplit_cover_tensorHom
import Theorems.Thm_GlobalTheory_ToSplit_IsFrame_exists_gen_linComb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
namespace GlobalTheory.ToSplit
namespace IsFrame
theorem _root_.solution [IsCommMonObj G] {χ : X} {O : RigLB B}
    {u : ∀ j, Γ(G.left, q.left ⁻¹ᵁ O.L.U j)ˣ} (h : IsFrame q i χ O u) :
    ∃ t : LB.Gen (abelian₂ B O.L), t.IsGen := by
  obtain ⟨⟨_, _⟩, _⟩ := cover_tensorHom (q := q)
  have hx : ∀ k, x2 G k ≫ q = (q ⊗ₘ q) ≫ x2 B k := fun k => by
    fin_cases k <;> simp [x2]
  refine h.exists_gen_linComb (q ⊗ₘ q) (K := ULift.{0} (Finset (Fin 2)))
    (fun I => (psum B (x2 B) I.down).left) (fun I => psum G (x2 G) I.down)
    (fun I => (-1) ^ (2 - I.down.card)) (fun I => ?_) (fun Z g₁ g₂ z e => ?_)
  · refine congrArg Over.Hom.left
      (?_ : psum G (x2 G) I.down ≫ q = (q ⊗ₘ q) ≫ psum B (x2 B) I.down)
    rw [psum_comp, comp_psum, funext hx]
  · have ht : ∀ k, ∃ t : Z ⟶ splitTorus S X, g₁ ≫ x2 G k = (t ≫ i) * (g₂ ≫ x2 G k) := fun k =>
      exists_act hk (by rw [Category.assoc, Category.assoc, hx, reassoc_of% e])
    choose t ht using ht
    refine ⟨fun I => psum _ t I.down, fun I => ?_,
      prod_square_eq_one ((MonoidHom.eval (Multiplicative.ofAdd χ)).comp (charGerm z)) t⟩
    rw [comp_psum, comp_psum, psum_comp, ← psum_mul, funext ht]
end IsFrame
end GlobalTheory.ToSplit
