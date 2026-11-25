-- Prove2me | solution 1 for GlobalTheory.UU.BiTransport.exists_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:19:25.844075+00:00
-- url     : https://prove2.me/submissions/a5b1bf40-42aa-4de4-b6bd-85b4dbd6e58c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompRedIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_BiTrivTransport
import Theorems.Thm_GlobalTheory_UU_BiTransport_toBase_surj
import Theorems.Thm_GlobalTheory_UU_BiTransport_exists_over
import Theorems.Thm_GlobalTheory_UU_BiTransport_toBase_comp
import Theorems.Thm_GlobalTheory_UU_BiTransport_exists_gen_val
import Theorems.Thm_GlobalTheory_IsCoaction_injective
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_coe_unitsAddMonoidAlgebraEquiv
import Theorems.Thm_GlobalTheory_mem_coactionWeightSpace
import Theorems.Thm_GlobalTheory_trivialCoaction_apply
import Theorems.Thm_GlobalTheory_tupleCoface_last
import Theorems.Thm_GlobalTheory_tupleCoface_zero
import Theorems.Thm_GlobalTheory_tupleContraction_apply
import Theorems.Thm_P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_unitsAddMonoidAlgebraEquiv
attribute [local simp] GlobalTheory.mem_coactionWeightSpace
attribute [local simp] GlobalTheory.trivialCoaction_apply
attribute [local simp] GlobalTheory.tupleCoface_last
attribute [local simp] GlobalTheory.tupleCoface_zero
attribute [local simp] GlobalTheory.tupleContraction_apply
attribute [local simp] P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0



set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.BiTransport
variable {S S₀ : Scheme.{0}} {ρ : S₀ ⟶ S}
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] {G₀ H₀ : Over S₀} [GrpObj G₀] [IsCommMonObj G₀]
  [GrpObj H₀] {F : G₀.left ⟶ G.left} {hw : F ≫ G.hom = G₀.hom ≫ ρ} {E : H₀.left ⟶ H.left}
  {P : CP G} {P₀ : CP G₀} {w : LB.Iso P₀.L.L (P.L.L.pull F)} {i : H ⟶ G} {i₀ : H₀ ⟶ G₀}
namespace GlobalTheory.UU.BiTransport
theorem _root_.solution [Mono ρ] (hF : IsPullback F G₀.hom G.hom ρ) (hE : IsGrpPullback H₀ H ρ E)
    (hP : IsCPMap P₀ P ρ F hw w) (hi : E ≫ i.left = i₀.left ≫ F) [IsMonHom i₀] (σ : BiTriv P₀.c i₀) :
    ∃ s : LB.Gen (LB.LinComb P.L.L (fun k => pullback.fst (H ⊗ G).hom ρ ≫ lamφ i k) Oε), s.IsGen ∧
      (∀ (Z : Over S) (t t' : Z ⟶ H) (x : Z ⟶ G) (a b d : Z.left ⟶ pullback (H ⊗ G).hom ρ),
        a ≫ pullback.fst _ _ = (lift (t * t') x).left → b ≫ pullback.fst _ _ = (lift t x).left →
        d ≫ pullback.fst _ _ = (lift t' x).left → ∀ (z : Z.left) (I), Good P.L.L z I →
        val s a z I = cubV P.c z I (t ≫ i) (t' ≫ i) x * val s b z I * val s d z I) ∧
      (∀ (Z : Over S) (t : Z ⟶ H) (x x' : Z ⟶ G) (a b d : Z.left ⟶ pullback (H ⊗ G).hom ρ),
        a ≫ pullback.fst _ _ = (lift t (x * x')).left → b ≫ pullback.fst _ _ = (lift t x).left →
        d ≫ pullback.fst _ _ = (lift t x').left → ∀ (z : Z.left) (I), Good P.L.L z I →
        val s a z I = cubV P.c z I (t ≫ i) x x' * val s b z I * val s d z I) := by
  obtain ⟨s, hs, hv⟩ := exists_gen_val hF hE.1 hP hi σ.s σ.gen
  have ov : ∀ (Z : Over S) (a : Z.left ⟶ pullback (H ⊗ G).hom ρ) (p : Z ⟶ H ⊗ G), a ≫ pullback.fst _ _ = p.left →
      ∃ T : Over S₀, Z = Over.mk (T.hom ≫ ρ) := fun Z a p ha => exists_over (a ≫ pullback.snd _ _) (by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, ha]; exact Over.w p)
  refine ⟨s, hs, fun Z t t' x a b d ha hb hd z I hI => ?_, fun Z t x x' a b d ha hb hd z I hI => ?_⟩
  · obtain ⟨T, rfl⟩ := ov Z a _ ha
    obtain ⟨t, rfl⟩ := toBase_surj hE.1 hE.1.w t
    obtain ⟨t', rfl⟩ := toBase_surj hE.1 hE.1.w t'
    obtain ⟨x, rfl⟩ := toBase_surj hF hw x
    obtain ⟨J', hJ'⟩ := exists_good_pt P₀.L.isLB (Z := T.left) z
    have m : toBase hE.1.w t * toBase hE.1.w t' = toBase hE.1.w (t * t') :=
      Over.OverMorphism.ext (hE.2 T t t' _ _ rfl rfl)
    rw [m] at ha
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G₀) → (T.left.presheaf.stalk z)ˣ,
      ∀ y, W y = gw w y.left z (I (y.left ≫ F)) (J' y.left) := ⟨_, fun _ => rfl⟩
    have c := (hP.vals T z J' I hJ' hI W hW).2.2 (t ≫ i₀) (t' ≫ i₀) x
    have l := σ.law1 T t t' x z J' hJ'
    have va := hv T _ _ a ha z J' I hJ' hI W hW
    have vb := hv T _ _ b hb z J' I hJ' hI W hW
    have vd := hv T _ _ d hd z J' I hJ' hI W hW
    rw [MonObj.mul_comp] at va
    rw [toBase_comp (hw := hw) hE.1.w hi, toBase_comp (hw := hw) hE.1.w hi]
    show @id (T.left.presheaf.stalk z)ˣ (val s a z I) = @id (T.left.presheaf.stalk z)ˣ
      (cubV P.c (T := Over.mk (T.hom ≫ ρ)) z I (toBase hw (t ≫ i₀)) (toBase hw (t' ≫ i₀)) (toBase hw x)) *
        @id (T.left.presheaf.stalk z)ˣ (val s b z I) * @id (T.left.presheaf.stalk z)ˣ (val s d z I)
    generalize @id (T.left.presheaf.stalk z)ˣ (cubV P.c (T := Over.mk (T.hom ≫ ρ)) z I (toBase hw (t ≫ i₀))
      (toBase hw (t' ≫ i₀)) (toBase hw x)) = C at c ⊢
    refine va.trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg (C * ·) vb) vd).symm)
    rw [l]
    apply Additive.ofMul.injective
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul, ofMul_inv] at c' ⊢
    linear_combination (norm := abel) -c'
  · obtain ⟨T, rfl⟩ := ov Z a _ ha
    obtain ⟨t, rfl⟩ := toBase_surj hE.1 hE.1.w t
    obtain ⟨x, rfl⟩ := toBase_surj hF hw x
    obtain ⟨x', rfl⟩ := toBase_surj hF hw x'
    obtain ⟨J', hJ'⟩ := exists_good_pt P₀.L.isLB (Z := T.left) z
    rw [← hP.mul] at ha
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G₀) → (T.left.presheaf.stalk z)ˣ,
      ∀ y, W y = gw w y.left z (I (y.left ≫ F)) (J' y.left) := ⟨_, fun _ => rfl⟩
    have c := (hP.vals T z J' I hJ' hI W hW).2.2 (t ≫ i₀) x x'
    have l := σ.law2 T t x x' z J' hJ'
    have va := hv T _ _ a ha z J' I hJ' hI W hW
    have vb := hv T _ _ b hb z J' I hJ' hI W hW
    have vd := hv T _ _ d hd z J' I hJ' hI W hW
    rw [← _root_.mul_assoc (t ≫ i₀)] at va
    rw [toBase_comp (hw := hw) hE.1.w hi]
    show @id (T.left.presheaf.stalk z)ˣ (val s a z I) = @id (T.left.presheaf.stalk z)ˣ
      (cubV P.c (T := Over.mk (T.hom ≫ ρ)) z I (toBase hw (t ≫ i₀)) (toBase hw x) (toBase hw x')) *
        @id (T.left.presheaf.stalk z)ˣ (val s b z I) * @id (T.left.presheaf.stalk z)ˣ (val s d z I)
    generalize @id (T.left.presheaf.stalk z)ˣ (cubV P.c (T := Over.mk (T.hom ≫ ρ)) z I (toBase hw (t ≫ i₀))
      (toBase hw x) (toBase hw x')) = C at c ⊢
    refine va.trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg (C * ·) vb) vd).symm)
    rw [l]
    apply Additive.ofMul.injective
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul, ofMul_inv] at c' ⊢
    linear_combination (norm := abel) -c'
end GlobalTheory.UU.BiTransport
