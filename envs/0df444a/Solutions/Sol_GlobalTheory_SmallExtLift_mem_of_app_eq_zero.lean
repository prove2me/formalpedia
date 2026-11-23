-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.mem_of_app_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:15.914707+00:00
-- url     : https://prove2.me/submissions/e7a201d7-319b-4b08-a540-b66de559a6fa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension

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
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SmallExtLift
variable {X Y Z : Scheme.{0}}
variable {R : Type} [CommRing R]
variable {R' : Type} [CommRing R'] {φ : R →+* R'} {p : X ⟶ Spec (CommRingCat.of R)}
  {π : Y ⟶ X} {f' : Y ⟶ Spec (CommRingCat.of R')}
namespace GlobalTheory.SmallExtLift
theorem _root_.solution (hφ : Function.Surjective φ)
    (H : IsPullback π f' p (Spec.map (CommRingCat.ofHom φ))) {V : X.Opens} (hV : IsAffineOpen V)
    (a : Γ(X, V)) (ha : (π.app V).hom a = 0) : a ∈ (RingHom.ker φ).map (cst p V) := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := V) (UY := π ⁻¹ᵁ V) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hV)
  set J := (RingHom.ker φ).map (cst p V)
  let l : R' →+* Γ(X, V) ⧸ J := φ.liftOfSurjective hφ ⟨(Ideal.Quotient.mk J).comp (cst p V),
    fun r hr => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hr)⟩
  have hl : ∀ r, l (φ r) = Ideal.Quotient.mk J (cst p V r) := fun r =>
    φ.liftOfSurjective_comp_apply hφ _ r
  have w : p.appLE ⊤ V le_top ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) =
      (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_top ≫
        (Scheme.ΓSpecIso (CommRingCat.of R')).hom ≫ CommRingCat.ofHom l := by
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv]
    have : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_top =
      (Spec.map (CommRingCat.ofHom φ)).appTop := Scheme.Hom.appLE_eq_app _
    rw [this, ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id_assoc]
    ext r
    exact (hl r).symm
  have e := congrArg (fun q => q.hom a) (po.inl_desc _ _ w)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    Scheme.Hom.appLE_eq_app, ha, map_zero] at e
  exact Ideal.Quotient.eq_zero_iff_mem.1 e.symm
end GlobalTheory.SmallExtLift
