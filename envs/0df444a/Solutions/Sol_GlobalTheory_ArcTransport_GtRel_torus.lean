-- Prove2me | solution 1 for GlobalTheory.ArcTransport.GtRel.torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T06:02:09.856272+00:00
-- url     : https://prove2.me/submissions/ce01bbcc-4b40-47d1-9f3e-de8cf90a768c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsCommonField
import Theorems.Thm_P2M_GlobalTheory_ArcTransport_exists_good__b067f9275064
import Theorems.Thm_GlobalTheory_ArcTransport_GtRel_over_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_toStk_valF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_top_le_iff_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ArcTransport
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {Φ : D'.P.A.left ⟶ D.P.A.left}
variable {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
variable (gp : IsGrpPullback D'.P.A D.P.A (spMap f) Φ) (hT : (TF (R := R') F).hom ≫ spMap f = (TF (R := R) F).hom)
variable {e : D.X ≃+ D'.X} (hc : ∀ y, (D'.c (e y)).left ≫ Φ = spMap f ≫ (D.c y).left)
variable {w : LB.Iso D'.P.L (D.P.L.pull Φ)} (hw : PGen w)
include gp hT hc hw
namespace GlobalTheory.ArcTransport
namespace GtRel
theorem _root_.solution {u : D.X → Fˣ} {g₀ : GtPtF D F} {g : GtPtF D' F} (h : GtRel w e u g₀ g) {t : D.X → F}
    (hb : g₀.b = DegPre.zeroF D F)
    (ht : ∀ χ j, LB.Coh D.P.L (DegPre.gtφ D F g₀.b χ) j → ⊤ ≤ LB.wchart D.P.L (DegPre.gtφ D F g₀.b χ) j →
      valF (𝟙 (Sp F)) _ ((g₀.s χ).s j).val = t χ) :
    g.b = DegPre.zeroF D' F ∧ ∀ χ j, LB.Coh D'.P.L (DegPre.gtφ D' F g.b χ) j →
      ⊤ ≤ LB.wchart D'.P.L (DegPre.gtφ D' F g.b χ) j →
      valF (𝟙 (Sp F)) _ ((g.s χ).s j).val = u (e.symm χ) * t (e.symm χ) := by
  obtain ⟨hb', hv⟩ := h.over_zero gp hT hc hw hb
  refine ⟨hb', fun χ j hj hle => ?_⟩
  obtain ⟨χ, rfl⟩ := e.surjective χ
  have y : Sp F := (default : PrimeSpectrum F)
  have m : (𝟙 (Sp F) : Sp F ⟶ Sp F) y ∈ LB.wchart D'.P.L (DegPre.gtφ D' F g.b (e χ)) j := hle trivial
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB (Y := Sp F) y
  obtain ⟨J', hJ', e'⟩ := exists_good D'.P.L D'.P.isLB (Z := Sp F) y _ j hj (Set.mem_iInter.1 m)
  have m₀ := hJ.mem (DegPre.gtφ D F g₀.b χ) (𝟙 _)
  have t₀ := ht χ (fun k => J (𝟙 _ ≫ DegPre.gtφ D F g₀.b χ k)) (fun a b h => congrArg (fun q => J (𝟙 _ ≫ q)) h)
    ((top_le_iff_mem (𝟙 (Sp F)) _ y).2 m₀)
  rw [AddEquiv.symm_apply_apply, ← t₀]
  apply (toStk y).injective
  rw [map_mul]
  refine (toStk_valF (𝟙 (Sp F)) _ y m _).trans (Eq.trans ?_ (congrArg _ (toStk_valF (𝟙 (Sp F)) _ y m₀ _)).symm)
  refine Eq.trans (congrArg Units.val ?_) (congrArg Units.val (hv χ y J J' hJ hJ'))
  exact (val_of (g.s (e χ)) (𝟙 _) y J' j (fun k => by rw [Category.id_comp]; exact e' k)).symm
end GtRel
end GlobalTheory.ArcTransport
