-- Prove2me | solution 1 for GlobalTheory.AbLaw.MulN.mulA_finite_flat_surjective_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:52:59.773068+00:00
-- url     : https://prove2.me/submissions/b993d2ed-34f5-45da-9626-36677b2f5d5a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulAFiniteFlatSurjectiveEtale
import Theorems.Thm_GlobalTheory_AbLaw_MulN_isMonHom_mulA
import Theorems.Thm_GlobalTheory_AbLaw_MulN_isPullback_baseChange
import Theorems.Thm_GlobalTheory_AbLaw_MulN_surjective_of_geomFibres
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_isAb_pullback


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
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.MulN
namespace GlobalTheory.AbLaw.MulN
theorem _root_.solution :
    (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left) → (∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → ∀ f : A ⟶ A, IsMonHom f → IsFinite f.left → Flat f.left ∧ Surjective f.left) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (X Y : Over S) (f : X ⟶ Y), Flat X.hom → LocallyOfFiniteType Y.hom → IsFinite f.left → (∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S), Flat ((Over.pullback t).map f).left) → Flat f.left) → (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ), IsUnit (n : Γ(S, ⊤)) → FormallyUnramified (mulA G n).left) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left) := by
  intro hfin hK hfib hunr S _ P n hn
  have hc := P.isAb.comm
  have hsm := P.isAb.smooth
  have hf := hfin S P n hn
  have hm := isMonHom_mulA P.A n
  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      Flat ((Over.pullback t).map (mulA P.A n)).left ∧
        Surjective ((Over.pullback t).map (mulA P.A n)).left := fun K _ _ t =>
    hK K _ (TLinPf.isAb_pullback t P.A P.isAb) _ inferInstance
      (MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_baseChange t _) hf)
  have hflat : Flat (mulA P.A n).left :=
    hfib S _ _ _ inferInstance inferInstance hf fun K _ _ t => (hgeo K t).1
  refine ⟨hf, hflat, surjective_of_geomFibres _ fun K _ _ t => (hgeo K t).2, fun hu => ?_⟩
  have := hunr S P.A n hu
  have : IsLocallyNoetherian P.A.left := LocallyOfFiniteType.isLocallyNoetherian P.A.hom
  exact Etale.of_formallyUnramified_of_flat _
end GlobalTheory.AbLaw.MulN
