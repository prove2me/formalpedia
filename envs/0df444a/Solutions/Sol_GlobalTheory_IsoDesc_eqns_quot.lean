-- Prove2me | solution 1 for GlobalTheory.IsoDesc.eqns_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:38:23.39826+00:00
-- url     : https://prove2.me/submissions/8a533741-4834-49df-8307-390b4bb2469b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapDescends
import Theorems.Thm_GlobalTheory_IsoDesc_cubV_toBase_hom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.IsoDesc
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G B' : Over S'} {B : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj B']
  [IsCommMonObj B'] [GrpObj B] [IsCommMonObj B] {P : CP G} {M' : CP B'} {M : CP B} {q : G ⟶ B'}
  {β : B'.left ⟶ B.left} {hβ : β ≫ B.hom = B'.hom ≫ f}
namespace GlobalTheory.IsoDesc
theorem _root_.solution {hq : q.left ≫ B'.hom = G.hom ≫ 𝟙 S'} {hw : (q.left ≫ β) ≫ B.hom = G.hom ≫ f} {u w}
    (Hu : IsCPMap P M' (𝟙 S') q.left hq u) (Hw : IsCPMap P M f (q.left ≫ β) hw w) {s} (hs : IsQuot u w s)
    {T : Over S'} {z : T.left} {I J} (hI : Good M'.L.L z I) (hJ : Good M.L.L z J) :
    Eqns M' M hβ z I J (fun x : T ⟶ G => x ≫ q)
      (fun x => gm x.left z _ (s (J ((x ≫ q).left ≫ β)) (I (x ≫ q).left))) := by
  obtain ⟨K, hK⟩ := exists_good_pt P.L.isLB z
  obtain ⟨V, hV⟩ : ∃ V : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
    V = fun x => gm x.left z _ (s (J ((x ≫ q).left ≫ β)) (I (x ≫ q).left)) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
    ∀ x, U x = gw u x.left z (I (x.left ≫ q.left)) (K x.left) := ⟨_, fun _ => rfl⟩
  rw [← hV]
  obtain ⟨a₁, a₂, a₃⟩ := Hw.vals T z K J hK hJ (fun x => V x * U x) (fun x => by
    rw [hV, hU, ← Category.assoc]
    exact (hs _ x.left z _ _ _ (hJ ((x.left ≫ q.left) ≫ β)) (hI (x.left ≫ q.left)) (hK x.left)).symm)
  obtain ⟨b₁, b₂, b₃⟩ := Hu.vals T z K I hK hI U hU
  refine ⟨?_, fun x => ?_, fun x y v => ?_⟩
  · rw [Category.comp_id] at b₁
    rw [a₁, b₁, _root_.mul_assoc]
  · have a := a₂ x
    have b := b₂ x
    rw [← Category.assoc] at a
    rw [Over.comp_left]
    apply Additive.ofMul.injective
    have a' := congrArg Additive.ofMul a
    have b' := congrArg Additive.ofMul b
    simp only [ofMul_mul] at a' b' ⊢
    linear_combination (norm := abel) a' - b'
  · have a := a₃ x y v
    have b := b₃ x y v
    have e : ∀ x : T ⟶ G, toBase hw x = toBase hβ (x ≫ q) := fun x =>
      Over.OverMorphism.ext (Category.assoc _ _ _).symm
    rw [e, e, e] at a
    rw [_root_.id, cubV_toBase_hom] at b
    generalize @id (T.left.presheaf.stalk z)ˣ (cubV M.c (T := Over.mk (T.hom ≫ f)) z J (toBase hβ (x ≫ q))
      (toBase hβ (y ≫ q)) (toBase hβ (v ≫ q))) = C at a ⊢
    apply Additive.ofMul.injective
    have a' := congrArg Additive.ofMul a
    have b' := congrArg Additive.ofMul b
    simp only [ofMul_mul] at a' b' ⊢
    linear_combination (norm := abel) a' - b'
end GlobalTheory.IsoDesc
