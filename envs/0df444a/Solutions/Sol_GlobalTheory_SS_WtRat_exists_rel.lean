-- Prove2me | solution 1 for GlobalTheory.SS.WtRat.exists_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:33:48.706356+00:00
-- url     : https://prove2.me/submissions/0d0e5f81-95fc-4055-81b8-07070e155f95

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeightedRelationOfMinimalSupportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFractionEvalSectionAffineNearPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGenericFunctionFieldPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusWeightTestGenericPointRationalPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRatioOfWeightSums
import Theorems.Thm_GlobalTheory_SS_WtRat_chr_one
import Theorems.Thm_GlobalTheory_SS_WtRat_chr_add
import Theorems.Thm_GlobalTheory_SS_WtRat_chr_zero
import Theorems.Thm_GlobalTheory_SS_WtRat_chr_ext
import Theorems.Thm_GlobalTheory_SS_WtRat_chr_comp
import Theorems.Thm_GlobalTheory_SS_WtRat_exists_chr
import Theorems.Thm_GlobalTheory_SS_WtRat_ev_appLE
import Theorems.Thm_GlobalTheory_SS_WtRat_ev_congr
import Theorems.Thm_GlobalTheory_T_exists_fraction_evalSection_affine_near_point
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WtRat
namespace GlobalTheory.SS.WtRat
theorem _root_.solution {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] {X : Type} [AddCommGroup X]
    (i : splitTorus (Sp k) X ⟶ G) {F : Type} [Field F] {s : Sp F ⟶ Sp k} (g : Over.mk s ⟶ G)
    (U : G.left.Opens) (f : Γ(G.left, U)) (h₁ : ⊤ ≤ (((1 : Over.mk s ⟶ splitTorus (Sp k) X) ≫ i) * g).left ⁻¹ᵁ U) :
    ∃ (S : Finset X) (p q : X → F), ∑ χ ∈ S, p χ ≠ 0 ∧
      ∀ (t : Over.mk s ⟶ splitTorus (Sp k) X) (h : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ U),
        ev (R := F) ((t ≫ i) * g).left U h f * ∑ χ ∈ S, chr t χ * p χ = ∑ χ ∈ S, chr t χ * q χ := by
  classical
  let R := AddMonoidAlgebra F X
  let sR : Sp R ⟶ Sp k := spMap (algebraMap F R) ≫ s
  let π : Over.mk sR ⟶ Over.mk s := Over.homMk (spMap (algebraMap F R)) rfl
  obtain ⟨tR, htR⟩ := exists_chr (X := X) sR (AddMonoidAlgebra.of F X)
  let a : Over.mk sR ⟶ G := (tR ≫ i) * (π ≫ g)
  let cH (t : Over.mk s ⟶ splitTorus (Sp k) X) : Multiplicative X →* F :=
    { toFun := fun χ => chr t χ.toAdd, map_one' := chr_zero t, map_mul' := fun x y => chr_add t _ _ }
  let e (t : Over.mk s ⟶ splitTorus (Sp k) X) : R →+* F := (AddMonoidAlgebra.lift F F X (cH t)).toRingHom
  have hid (t) : spMap (e t) ≫ spMap (algebraMap F R) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    exact (AddMonoidAlgebra.lift F F X (cH t)).commutes x
  have he (t) : spMap (e t) ≫ sR = s := by
    rw [← Category.assoc, hid, Category.id_comp]
  have ha (t) : (Over.homMk (spMap (e t)) (he t) : Over.mk s ⟶ Over.mk sR) ≫ a = (t ≫ i) * g := by
    have h1 : (Over.homMk (spMap (e t)) (he t) : Over.mk s ⟶ Over.mk sR) ≫ tR = t := by
      refine chr_ext fun χ => ?_
      rw [chr_comp, htR]
      exact AddMonoidAlgebra.lift_of (cH t) (Multiplicative.ofAdd χ)
    have h2 : (Over.homMk (spMap (e t)) (he t) : Over.mk s ⟶ Over.mk sR) ≫ π = 𝟙 _ :=
      Over.OverMorphism.ext (hid t)
    rw [MonObj.comp_mul, ← Category.assoc, h1, ← Category.assoc, h2, Category.id_comp]
  have ha' (t) : spMap (e t) ≫ a.left = ((t ≫ i) * g).left := congrArg CommaMorphism.left (ha t)
  have hx : spMap (e 1) (IsLocalRing.closedPoint F) ∈ a.left ⁻¹ᵁ U := by
    have := h₁ (show IsLocalRing.closedPoint F ∈ (⊤ : (Sp F).Opens) from trivial)
    rw [← ha'] at this
    exact this
  obtain ⟨α, β, hβ, hαβ⟩ := GlobalTheory.T.exists_fraction_evalSection_affine_near_point R (a.left ⁻¹ᵁ U) ((a.left.appLE U _ le_rfl).hom f) _ hx
  have hsum (t) (w : R) (S : Finset X) (hS : w.coeff.support ⊆ S) : e t w = ∑ χ ∈ S, chr t χ * w.coeff χ := by
    show AddMonoidAlgebra.lift F F X (cH t) w = _
    rw [AddMonoidAlgebra.lift_apply, Finsupp.sum_of_support_subset _ hS _ (by simp)]
    exact Finset.sum_congr rfl fun χ _ => mul_comm _ _
  refine ⟨α.coeff.support ∪ β.coeff.support, β.coeff, α.coeff, ?_, fun t h => ?_⟩
  · have h2 := hsum 1 β _ (Finset.subset_union_right (s₁ := α.coeff.support))
    simp only [chr_one, _root_.one_mul] at h2
    rw [← h2]
    intro h0
    refine hβ ?_
    show e 1 β ∈ IsLocalRing.maximalIdeal F
    rw [h0]; exact zero_mem _
  · rw [← hsum t β _ Finset.subset_union_right, ← hsum t α _ Finset.subset_union_left]
    have h' : ⊤ ≤ (spMap (e t) ≫ a.left) ⁻¹ᵁ U := by rw [ha']; exact h
    refine Eq.trans ?_ (hαβ F (e t) h')
    congr 1
    exact (ev_congr (ha' t).symm U h h' f).trans (ev_appLE (spMap (e t)) a.left U _ le_rfl h' h' f).symm
end GlobalTheory.SS.WtRat
