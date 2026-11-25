-- Prove2me | solution 1 for GlobalTheory.LocalRingGeneralisation.exists_stalk_equiv_localization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:01:18.460198+00:00
-- url     : https://prove2.me/submissions/6f0d9d79-6d61-45b3-bd63-823c25e4906c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_StalkGenerizationGermCompat
import Theorems.Thm_GlobalTheory_LocalRingGeneralisation_isIso_stalkMap_fromSpecStalk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open GlobalTheory GlobalTheory.LocalRingGeneralisation
namespace GlobalTheory.LocalRingGeneralisation
theorem _root_.solution : ∀ {X : Scheme.{0}} (x : X) (p : Ideal (X.presheaf.stalk x)) [p.IsPrime], ∃ (q : X) (e : X.presheaf.stalk q ≃+* Localization.AtPrime p), q ⤳ x ∧ ∀ (U : X.Opens) (hq : q ∈ U) (hx : x ∈ U) (s : Γ(X, U)), e ((X.presheaf.germ U q hq).hom s) = algebraMap (X.presheaf.stalk x) (Localization.AtPrime p) ((X.presheaf.germ U x hx).hom s) := by
  intro X x p _
  let y : Spec (X.presheaf.stalk x) := (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x))
  have := isIso_stalkMap_fromSpecStalk X x y
  refine ⟨X.fromSpecStalk x y,
    (asIso ((X.fromSpecStalk x).stalkMap y) ≪≫ Spec.stalkIso _ y).commRingCatIsoToRingEquiv, ?_, ?_⟩
  · have : X.fromSpecStalk x y ∈ Set.range (X.fromSpecStalk x) := ⟨y, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  · intro U hq hx s
    have h1 := Scheme.Hom.germ_stalkMap_apply (X.fromSpecStalk x) U y hq s
    show (Spec.stalkIso _ y).hom ((X.fromSpecStalk x).stalkMap y ((X.presheaf.germ U _ hq).hom s)) = _
    rw [h1, Scheme.fromSpecStalk_app hx]
    have h2 := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom ((X.presheaf.germ U x hx).hom s)))
      (Spec.germ_stalkMapIso_hom (R := X.presheaf.stalk x) (x := y))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
    rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom,
      Iso.inv_hom_id, CommRingCat.id_apply] at h2
    rw [← h2]
    simp only [← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]
    erw [TopCat.Presheaf.germ_res]
end GlobalTheory.LocalRingGeneralisation
