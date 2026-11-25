-- Prove2me | solution 1 for GlobalTheory.IsoDesc.isCPMap_of_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:20:26.636629+00:00
-- url     : https://prove2.me/submissions/a0531ed1-14ea-4a5c-afe9-750d4307a275

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
import Theorems.Thm_GlobalTheory_IsoDesc_kap_injective
import Theorems.Thm_GlobalTheory_IsoDesc_exists_good_epi
import Theorems.Thm_GlobalTheory_IsoDesc_kap_val
import Theorems.Thm_GlobalTheory_IsoDesc_kap_gw
import Theorems.Thm_GlobalTheory_IsoDesc_IsQuot_trans
import Theorems.Thm_GlobalTheory_IsoDesc_exists_lift
import Theorems.Thm_P2M_GlobalTheory_IsoDesc_exists_lift__24f218a0e0ac
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff


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
theorem _root_.solution [IsMonHom q] [Flat q.left] [Surjective q.left]
    (mul : ∀ (T : Over S') (x y : T ⟶ B'), toBase hβ (x * y) = toBase hβ x * toBase hβ y)
    {v : LB.Iso M'.L.L (M.L.L.pull β)} (hv : PGen v)
    (H : ∀ (T : Over S') (z : T.left) (I J), Good M'.L.L z I → Good M.L.L z J →
      Eqns M' M hβ z I J (fun x : T ⟶ G => x ≫ q)
        (fun x => gw v (x ≫ q).left z (J ((x ≫ q).left ≫ β)) (I (x ≫ q).left))) :
    IsCPMap M' M f β hβ v := by
  refine ⟨mul, (isGen_iff v).2 hv, fun T z I J hI hJ W hW => ⟨?_, fun x => ?_, fun x y u => ?_⟩⟩
  · have := (H T z I J hI hJ).1
    simp only [MonObj.one_comp] at this
    rw [hW]; exact this
  on_goal 1 => obtain ⟨T', ρ, x', _, _, e₁⟩ := exists_lift (q := q) x
  on_goal 2 => obtain ⟨T', ρ, x', y', u', _, _, e₁, e₂, e₃⟩ := exists_lift₃ (q := q) x y u
  all_goals
    obtain ⟨z, rfl⟩ := ρ.left.surjective z
    have : Epi ρ.left := Flat.epi_of_flat_of_surjective _
    obtain ⟨I', hI', eI⟩ := exists_good_epi M'.L.isLB ρ.left z hI
    obtain ⟨J', hJ', eJ⟩ := exists_good_epi M.L.isLB ρ.left z hJ
    obtain ⟨W', hW'⟩ : ∃ W' : (T' ⟶ B') → (T'.left.presheaf.stalk z)ˣ,
      ∀ b, gw v b.left z (J' (b.left ≫ β)) (I' b.left) = W' b := ⟨_, fun _ => rfl⟩
    have k : ∀ b, kap ρ.left z (W b) = W' (ρ ≫ b) := fun b => by
      rw [hW, kap_gw, ← hW', Over.comp_left, Category.assoc, eI, eJ]
    have E := H T' z I' J' hI' hJ'
    simp only [hW'] at E
    apply kap_injective ρ.left z
  · have a := E.2.1 x'
    simp only [GrpObj.inv_comp, e₁] at a
    rw [map_mul, map_mul, k, k, kap_val _ _ _ eI, kap_val _ _ _ eJ, GrpObj.comp_inv, ← Category.assoc]
    exact a
  · have a := E.2.2 x' y' u'
    simp only [MonObj.mul_comp, MonObj.one_comp, e₁, e₂, e₃] at a
    have c' : kap ρ.left z (cubV M'.c (ρ.left z) I x y u) = cubV M'.c z I' (ρ ≫ x) (ρ ≫ y) (ρ ≫ u) := by
      refine (kap_val (L := M'.L.L) (φ := thφ B' (x3 B')) (ε := thε) M'.c.t ρ.left z eI _).trans ?_
      refine congrArg (fun r => val (L := M'.L.L) (φ := thφ B' (x3 B')) (ε := thε) M'.c.t r z I') ?_
      rw [← comp_lift, ← comp_lift]; rfl
    have c : kap ρ.left z (@id (T.left.presheaf.stalk (ρ.left z))ˣ (cubV M.c (T := Over.mk (T.hom ≫ f)) (ρ.left z) J
        (toBase hβ x) (toBase hβ y) (toBase hβ u))) = @id (T'.left.presheaf.stalk z)ˣ
        (cubV M.c (T := Over.mk (T'.hom ≫ f)) z J' (toBase hβ (ρ ≫ x)) (toBase hβ (ρ ≫ y)) (toBase hβ (ρ ≫ u))) := by
      let ρ' : Over.mk (T'.hom ≫ f) ⟶ Over.mk (T.hom ≫ f) := Over.homMk ρ.left (by simp)
      have e : ∀ a : T ⟶ B', toBase hβ (ρ ≫ a) = ρ' ≫ toBase hβ a := fun a =>
        Over.OverMorphism.ext (Category.assoc _ _ _)
      rw [e, e, e]
      refine (kap_val (L := M.L.L) (φ := thφ B (x3 B)) (ε := thε) M.c.t ρ.left z eJ _).trans ?_
      refine congrArg (fun r => val (L := M.L.L) (φ := thφ B (x3 B)) (ε := thε) M.c.t r z J') ?_
      rw [← comp_lift, ← comp_lift]; rfl
    simp only [map_mul, k, c, c', MonObj.comp_mul, MonObj.comp_one]
    exact a
end GlobalTheory.IsoDesc
