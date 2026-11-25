-- Prove2me | solution 1 for GlobalTheory.WitnessData.witness_data_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:22:39.90781+00:00
-- url     : https://prove2.me/submissions/79210a4b-bd21-4f43-8bfe-75ee1e06e5c9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataIsoOfTwoWitnesses
import Theorems.Thm_GlobalTheory_WitnessData_exists_isPullDeg_pre
import Theorems.Thm_GlobalTheory_WitnessData_comm_of_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_specOf_id


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.WitnessData
namespace GlobalTheory.WitnessData
theorem _root_.solution : Laws → Laws2 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (I : Ideal R) (f : O' →+* R) (u : R), AdmBase R I → I ≠ ⊤ → Function.Injective f → ∀ (χ χ' : Sp R ⟶ Y.X) (W : ArcWit Y a I f u χ) (W' : ArcWit Y a I f u χ'), ∃ hD : IsPullDeg (RingHom.id R) W.P.D.toPre W'.P.D.toPre, (∀ y, hD.xe (W'.e y) = W.e y) ∧ (∀ x, (letI := H.starRing; W'.P.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (W.P.oD.onB.act x))) ∧ ∃ w' : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ W.φ)), W'.φ = (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ W.φ ∧ HEq W'.w w' ∧ Tri W.w hD.w w' := by
  intro _ _ h5 E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a R _ _ _ _ I f u hR _ hf χ χ' W W'
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
  obtain ⟨s1', s2', s3', s4', s5', s6'⟩ := W'.spec
  obtain ⟨Wo, hWo, ⟨ψW⟩⟩ := h5.psiOnExists R I hR W.P.D
  let F := AlgebraicClosure (FractionRing R)
  have hi : Function.Injective (((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))).comp f) :=
    ((algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R _)).comp hf
  letI : Algebra (FractionRing O') F := (IsFractionRing.lift (K := FractionRing O') hi).toAlgebra
  have hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
      algebraMap (FractionRing R) F (algebraMap R _ (f x)) := fun x => IsFractionRing.lift_algebraMap hi x
  obtain ⟨hD, h₁, w', h₂, h₃, h₄⟩ := exists_isPullDeg_pre W.he W'.he W.e.toAddEquiv W'.e.toAddEquiv s1 s1' s2 s2'
    s3 s3' s5 s5' F _ (s6 F _ hF rfl).1 (s6' F _ hF rfl).1 hWo ψW
  exact ⟨hD, h₁, fun x => comm_of_pullback (specOf_id R) s1.1 hD.e.hom h₂ (s4 x) (s4' x), w', h₂, h₃, h₄⟩
end GlobalTheory.WitnessData
