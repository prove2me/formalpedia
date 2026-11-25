-- Prove2me | solution 1 for GlobalTheory.UU.IsCPMap.cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:56:45.610353+00:00
-- url     : https://prove2.me/submissions/5f118323-6f29-4113-922c-cfdd5f193530

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapCompCancel
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_pgen_cancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']
  {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
namespace GlobalTheory.UU
namespace IsCPMap
theorem _root_.solution {P : CP G} {P' : CP G'} {P'' : CP G''} {f' : S'' ⟶ S'} {F' : G''.left ⟶ G'.left}
    {hw' : F' ≫ G'.hom = G''.hom ≫ f'} {w : LB.Iso P'.L.L (P.L.L.pull F)} {w' : LB.Iso P''.L.L (P'.L.L.pull F')}
    {hw'' : (F' ≫ F) ≫ G.hom = G''.hom ≫ f' ≫ f} {w'' : LB.Iso P''.L.L (P.L.L.pull (F' ≫ F))}
    (h : IsCPMap P' P f F hw w) (h'' : IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'')
    (mul : ∀ (T : Over S'') (x y : T ⟶ G''), toBase hw' (x * y) = toBase hw' x * toBase hw' y)
    (Tw : Tri w w' w'') : IsCPMap P'' P' f' F' hw' w' := by
  have key : ∀ (T : Over S''), ∃ ρ : Over.mk (T.hom ≫ f' ≫ f) ⟶ Over.mk ((Over.mk (T.hom ≫ f')).hom ≫ f),
      ρ.left = 𝟙 T.left ∧ ∀ x : T ⟶ G'', toBase hw'' x = ρ ≫ toBase hw (toBase hw' x) := fun T =>
    ⟨Over.homMk (𝟙 T.left) (by simp), rfl, fun x => Over.OverMorphism.ext
      ((Category.assoc _ _ _).symm.trans (Category.id_comp _).symm)⟩
  refine ⟨mul, (isGen_iff _).2 (Tw.pgen_cancel P.L.isLB ((isGen_iff _).1 h.gen) ((isGen_iff _).1 h''.gen)),
    fun T z J'' J' hJ'' hJ' B hB => ?_⟩
  obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
  obtain ⟨ρ, hρ, e⟩ := key T
  obtain ⟨a₁, a₂, a₃⟩ := h.vals (Over.mk (T.hom ≫ f')) z J' J hJ' hJ _ (fun _ => rfl)
  let β := toBaseHom mul T
  let A : (Over.mk (T.hom ≫ f') ⟶ G') → (T.left.presheaf.stalk z)ˣ :=
    fun x => gw w x.left z (J (x.left ≫ F)) (J' x.left)
  have hAB : ∀ x : T ⟶ G'', A (β x) * B x = gw w'' x.left z (J (x.left ≫ F' ≫ F)) (J'' x.left) := fun x => by
    rw [hB, ← Category.assoc]
    exact (Tw _ x.left z _ _ _ (hJ ((x.left ≫ F') ≫ F)) (hJ' (x.left ≫ F')) (hJ'' x.left)).symm
  obtain ⟨b₁, b₂, b₃⟩ := h''.vals T z J'' J hJ'' hJ (fun x => A (β x) * B x) hAB
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · rw [map_one, ← Category.assoc, _root_.mul_assoc] at b₁
    exact mul_left_cancel (a := A 1) (a₁.symm.trans b₁)
  · have a : val P.sym ((x.left ≫ F') ≫ F) z J * A (β x) = A (β x)⁻¹ * val P'.sym (x.left ≫ F') z J' := a₂ (β x)
    have b := b₂ x
    rw [map_inv, ← Category.assoc, ← _root_.mul_assoc, a, _root_.mul_assoc, _root_.mul_assoc] at b
    exact mul_left_cancel b
  · have c : @_root_.id (T.left.presheaf.stalk z)ˣ (cubV P.c (T := Over.mk (T.hom ≫ f' ≫ f)) z J (toBase hw'' x)
        (toBase hw'' y) (toBase hw'' u)) = cubV P.c (T := Over.mk ((Over.mk (T.hom ≫ f')).hom ≫ f)) z J
        (toBase hw (β x)) (toBase hw (β y)) (toBase hw (β u)) := by
      have e' : (lift (toBase hw'' x) (lift (toBase hw'' y) (toBase hw'' u))).left =
          (lift (toBase hw (β x)) (lift (toBase hw (β y)) (toBase hw (β u)))).left := by
        rw [e, e, e, ← comp_lift, ← comp_lift, Over.comp_left, hρ]; exact Category.id_comp _
      exact congrArg (fun r => val (L := P.L.L) (φ := thφ G (x3 G)) (ε := thε) P.c.t r z J) e'
    obtain ⟨C, hC⟩ : ∃ C : (T.left.presheaf.stalk z)ˣ, C = cubV P.c (T := Over.mk ((Over.mk (T.hom ≫ f')).hom ≫ f)) z J
        (toBase hw (β x)) (toBase hw (β y)) (toBase hw (β u)) := ⟨_, rfl⟩
    obtain ⟨C', hC'⟩ : ∃ C' : (T.left.presheaf.stalk z)ˣ, C' = cubV P'.c (T := Over.mk (T.hom ≫ f')) z J'
        (β x) (β y) (β u) := ⟨_, rfl⟩
    have a : C * A (β x * β y) * A (β x * β u) * A (β y * β u) * A 1 =
        A (β x * β y * β u) * A (β x) * A (β y) * A (β u) * C' := by
      rw [hC, hC']; exact a₃ (β x) (β y) (β u)
    have b := b₃ x y u
    rw [c.trans hC.symm] at b
    simp only [map_mul, map_one] at b
    have g : C' * B (x * y) * B (x * u) * B (y * u) * B 1 =
        B (x * y * u) * B x * B y * B u * cubV P''.c z J'' x y u := by
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      have b' := congrArg Additive.ofMul b
      simp only [ofMul_mul] at a' b' ⊢
      linear_combination (norm := abel) b' - a'
    rw [hC'] at g
    exact g
end IsCPMap
end GlobalTheory.UU
