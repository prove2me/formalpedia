-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isReduced_of_isReduced_stalk_one_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/eb7f214a-3e61-5346-b558-9eaeda439b9f

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isReduced_of_isReduced_stalk_one_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace HomogRed

theorem isReduced_of_forall_isClosed {X : Scheme.{0}} [JacobsonSpace X]
    (h : ∀ x : X, IsClosed ({x} : Set X) → _root_.IsReduced (X.presheaf.stalk x)) : IsReduced X := by

  have haff : ∀ (U : X.Opens) (hU : IsAffineOpen U), _root_.IsReduced Γ(X, U) := by
    intro U hU
    apply isReduced_ofLocalizationMaximal
    intro J hJ
    let y : PrimeSpectrum Γ(X, U) := ⟨J, hJ.isPrime⟩
    have hy : hU.fromSpec y ∈ U := show hU.fromSpec y ∈ (U : Set X) from hU.range_fromSpec ▸ Set.mem_range_self y

    have hyc : IsClosed ({hU.fromSpec y} : Set X) := by
      have h1 : IsClosed ({y} : Set (PrimeSpectrum Γ(X, U))) := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).2 hJ
      have h2 := hU.fromSpec.isOpenEmbedding.preimage_closedPoints (Y := X)
      have : y ∈ hU.fromSpec.base ⁻¹' closedPoints X := by rw [h2]; exact h1
      exact this
    have hred := h _ hyc
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hy⟩
    haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) J := hU.isLocalization_stalk' y hy
    let e := (IsLocalization.algEquiv J.primeCompl (Localization.AtPrime J) (X.presheaf.stalk (hU.fromSpec y)))
    exact isReduced_of_injective e.toRingHom e.injective

  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    haveI := haff U hU
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
    have hloc := hU.isLocalization_stalk ⟨x, hxU⟩
    exact @isReduced_localizationPreserves _ _ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (X.presheaf.stalk x) _ _
      hloc (haff U hU)
  exact isReduced_of_isReduced_stalk X

end HomogRed

open _root_.MonObj _root_.CategoryTheory.MonObj _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (L : RelativeGroupLaw k g)
    (he : _root_.IsReduced (G.presheaf.stalk ((L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k)))) :
    IsReduced G := by
  classical
  haveI : GrpObj (Over.mk g) := L.grpObjOverMk
  have := LocallyOfFiniteType.jacobsonSpace g
  apply HomogRed.isReduced_of_forall_isClosed
  intro x hx

  let e' : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Over.mk g := Over.homMk (L.one (𝟙 _)).1 (L.one (𝟙 _)).2
  let x' : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Over.mk g := Over.homMk _ ((pointEquivClosedPoint g).symm ⟨x, hx⟩).2
  let α := (GrpObj.mulRight (A := Over.mk g) e').symm ≪≫ (GrpObj.mulRight (A := Over.mk g) x')
  have hα : e' ≫ α.hom = x' := by
    dsimp only [Iso.trans_hom, Iso.symm_hom, α]
    rw [← Category.assoc, ← Iso.eq_comp_inv]
    simp [comp_lift_assoc]
  have hα' : α.hom.left ((L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k)) = x := by
    have h1 := congr(($hα).left (IsLocalRing.closedPoint k))
    simp only [e', x', Over.comp_left, Over.homMk_left, Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at h1
    refine h1.trans ?_
    exact pointOfClosedPoint_apply g x hx _

  let β : G ≅ G := (Over.forget _).mapIso α
  have hβ : β.hom = α.hom.left := rfl
  rw [← hα', ← hβ]
  have hst : IsIso (β.hom.stalkMap ((L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k))) := inferInstance
  exact isReduced_of_injective (β.hom.stalkMap _).hom
    ((ConcreteCategory.isIso_iff_bijective _).1 hst).1

end S_GoodReductionJacobian_RelativeGroupLaw_isReduced_of_isReduced_stalk_one_of_isAlgClosed
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isReduced_of_isReduced_stalk_one_of_isAlgClosed (solution)
