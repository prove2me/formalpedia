-- Prove2me | solution 1 for GlobalTheory.KS.Primitive.pbT_coc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:21.295365+00:00
-- url     : https://prove2.me/submissions/596f9f5e-0479-4018-b8b7-577d49e8e19a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenInfOfIsSeparated
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CechPrimitive
import Theorems.Thm_GlobalTheory_KS_Primitive_rsT_eq_rs
import Theorems.Thm_GlobalTheory_KS_Primitive_pbT_eq
import Theorems.Thm_GlobalTheory_KS_Primitive_le_pre_inf
import Theorems.Thm_GlobalTheory_KuennethOne_appLE_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_appLE
import Theorems.Thm_GlobalTheory_KuennethOne_rs_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.KuennethOne.appLE_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_appLE
attribute [local simp] GlobalTheory.KuennethOne.rs_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_self


section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
namespace GlobalTheory.KS.Primitive
open GlobalTheory.KuennethOne
variable {T Z A : Scheme.{0}} {I : Type} {U : I → A.Opens} {c : C1 U}
private lemma pbT_add' (f : T ⟶ A) {O₀ : A.Opens} (s s' : Γ(A, O₀)) {N : T.Opens}
    (hN : N ≤ f ⁻¹ᵁ O₀) : pbT f (s + s') N = pbT f s N + pbT f s' N := by
  simp only [pbT_eq f _ hN, map_add]
private lemma pbT_rsT' (f : T ⟶ A) {O₀ O : A.Opens} (s : Γ(A, O₀)) (hO : O ≤ O₀) {N : T.Opens}
    (hN : N ≤ f ⁻¹ᵁ O) : pbT f (rsT s O) N = pbT f s N := by
  rw [rsT_eq_rs s hO, pbT_eq f _ hN, pbT_eq f s (hN.trans (f.preimage_mono hO))]
  show (f.appLE O N hN).hom ((A.presheaf.map (homOfLE hO).op).hom s) = _
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
end GlobalTheory.KS.Primitive
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Primitive
open GlobalTheory.KuennethOne
variable {T Z A : Scheme.{0}} {I : Type} {U : I → A.Opens} {c : C1 U}
namespace GlobalTheory.KS.Primitive
theorem _root_.solution (hc : IsCoc U c) (f : T ⟶ A) (i j k : I) {N : T.Opens} (hi : N ≤ f ⁻¹ᵁ U i)
    (hj : N ≤ f ⁻¹ᵁ U j) (hk : N ≤ f ⁻¹ᵁ U k) :
    pbT f (c i j) N + pbT f (c j k) N = pbT f (c i k) N := by
  have hN : N ≤ f ⁻¹ᵁ (U i ⊓ U j ⊓ U k) := le_pre_inf f (le_pre_inf f hi hj) hk
  have l1 : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j := inf_le_left
  have l2 : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have l3 : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  rw [← pbT_rsT' f (c i j) l1 hN, ← pbT_rsT' f (c j k) l2 hN, ← pbT_rsT' f (c i k) l3 hN,
    ← pbT_add' f _ _ hN, hc i j k]
end GlobalTheory.KS.Primitive
