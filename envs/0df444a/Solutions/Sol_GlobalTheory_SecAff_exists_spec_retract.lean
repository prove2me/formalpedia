-- Prove2me | solution 1 for GlobalTheory.SecAff.exists_spec_retract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:35:50.256278+00:00
-- url     : https://prove2.me/submissions/55fb429c-1bd7-427d-9fd8-a5feb51dc1e7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' T'' : Over S}
namespace GlobalTheory.SecAff
theorem _root_.solution {V : S.Opens} [IsAffine T'.left]
    (g : T' ⟶ overRes (T := baseOver S) V) :
    ∃ (R : Type) (_ : CommRing R)
      (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S) V).left)
      (e : baseAt t ⟶ T') (e' : T' ⟶ baseAt t), e' ≫ e = 𝟙 T' ∧ e' ≫ homAt t = g := by
  let t : Spec (CommRingCat.of Γ(T'.left, ⊤)) ⟶ (overRes (T := baseOver S) V).left :=
    T'.left.isoSpec.inv ≫ g.left
  let e : baseAt t ⟶ T' := Over.homMk T'.left.isoSpec.inv (by
    change T'.left.isoSpec.inv ≫ T'.hom = (T'.left.isoSpec.inv ≫ g.left) ≫ _
    rw [Category.assoc, Over.w g])
  let e' : T' ⟶ baseAt t := Over.homMk T'.left.isoSpec.hom (by
    change T'.left.isoSpec.hom ≫ (T'.left.isoSpec.inv ≫ g.left) ≫ _ = T'.hom
    rw [Category.assoc, Over.w g, Iso.hom_inv_id_assoc])
  refine ⟨_, _, t, e, e', ?_, ?_⟩
  · ext1
    exact T'.left.isoSpec.hom_inv_id
  · ext1
    exact T'.left.isoSpec.hom_inv_id_assoc _
end GlobalTheory.SecAff
