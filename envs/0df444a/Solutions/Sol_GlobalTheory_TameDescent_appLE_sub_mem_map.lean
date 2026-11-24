-- Prove2me | solution 1 for GlobalTheory.TameDescent.appLE_sub_mem_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:29:08.612146+00:00
-- url     : https://prove2.me/submissions/afd91a87-0138-4442-832c-39f144b8d5d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsumSmulEqOneOfTame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantTowerAlgebraMapInjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FlatOfTameDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MemMapKerOfOneTmulEqZeroOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_QuotientIsFiniteLocallyOfFiniteTypeDescendStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsPullbackFlatOfTame
import Theorems.Thm_GlobalTheory_TameDescent_specMap_fromSpec_comp_eq_iff
import Theorems.Thm_GlobalTheory_mem_map_ker_of_one_tmul_eq_zero_of_flat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.TameDescent
namespace GlobalTheory.TameDescent
theorem _root_.solution {X Y : Scheme.{0}} (p : Y ⟶ X) [Flat p] (t : Y ⟶ Y) {U : X.Opens}
    {W : Y.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (e : W ≤ p ⁻¹ᵁ U)
    (h : W ≤ t ⁻¹ᵁ W) {k : Type} [Field k] (a : Γ(X, U) →+* k)
    (ht : pullback.fst p (Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec) ≫ t =
      pullback.fst p (Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec)) (c : Γ(Y, W)) :
    (t.appLE W W h).hom c - c ∈ (RingHom.ker a).map (p.appLE U W e).hom := by
  let := a.toAlgebra
  let := (p.appLE U W e).hom.toAlgebra
  have : Module.Flat Γ(X, U) Γ(Y, W) := p.flat_appLE hU hW e
  refine mem_map_ker_of_one_tmul_eq_zero_of_flat Γ(X, U) Γ(Y, W) k _ ?_
  let r : Γ(Y, W) ⟶ CommRingCat.of (k ⊗[Γ(X, U)] Γ(Y, W)) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  let l : CommRingCat.of k ⟶ CommRingCat.of (k ⊗[Γ(X, U)] Γ(Y, W)) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  have w : (Spec.map r ≫ hW.fromSpec) ≫ p =
      Spec.map l ≫ Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec := by
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec p hU hW e,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    exact (CommRingCat.isPushout_tensorProduct Γ(X, U) k Γ(Y, W)).w.symm
  refine (specMap_fromSpec_comp_eq_iff t hW h r).1 ?_ c
  rw [← pullback.lift_fst _ _ w, Category.assoc, ht]
end GlobalTheory.TameDescent
