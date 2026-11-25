-- Prove2me | solution 1 for GlobalTheory.DescTheta.nonvanishing_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:51.309301+00:00
-- url     : https://prove2.me/submissions/4f23d5bb-90af-4b5c-918c-0965cf36f17c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSumSmulSeparatingInertia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSecOnNonvanishingOfTameQuotient
import Theorems.Thm_GlobalTheory_DescTheta_mem_basicOpen_resG
import Theorems.Thm_GlobalTheory_DescTheta_mem_basicOpen_mul
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
import Theorems.Thm_GlobalTheory_LB_coord_isoOfGen_hom_app
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.DescTheta
open GlobalTheory.LB
variable {X Y : Scheme.{0}}
namespace GlobalTheory.DescTheta
theorem _root_.solution {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen)
    {V : X.Opens} (s : Γ(toMod L, V)) (x : X) :
    (∃ p, x ∈ X.basicOpen (coord ((isoOfGen hL hM w hw).hom.app V s) p)) ↔
      ∃ q, x ∈ X.basicOpen (coord s q) := by
  have key (p : M.ι) (q : L.ι) (hp : x ∈ V ⊓ M.U p) (hq : x ∈ V ⊓ L.U q) :
      x ∈ X.basicOpen (coord ((isoOfGen hL hM w hw).hom.app V s) p) ↔
        x ∈ X.basicOpen (coord s q) := by
    have e := coord_isoOfGen_hom_app hL hM w hw s p q (W := (V ⊓ M.U p) ⊓ (V ⊓ L.U q))
      inf_le_left inf_le_right (inf_le_inf inf_le_right inf_le_right)
    have e' := congrArg (fun a => x ∈ X.basicOpen a) e
    simp only [mem_basicOpen_mul, mem_basicOpen_resG, eq_iff_iff] at e'
    have hx : x ∈ (V ⊓ M.U p) ⊓ (V ⊓ L.U q) := ⟨hp, hq⟩
    have hx' : x ∈ X.basicOpen (U := M.U p ⊓ L.U q)
        ((show Γ(X, M.U p ⊓ L.U q)ˣ from w.s (p, q)) : Γ(X, M.U p ⊓ L.U q)) :=
      (X.basicOpen_of_isUnit (U := M.U p ⊓ L.U q) (Units.isUnit _)).ge ⟨hp.2, hq.2⟩
    exact ⟨fun h => (e'.1 ⟨hx, h⟩).2.2, fun h => (e'.2 ⟨⟨hx, hx'⟩, hx, h⟩).2⟩
  constructor
  · rintro ⟨p, hp⟩
    have hp' := X.basicOpen_le _ hp
    obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ x))
    exact ⟨q, (key p q hp' ⟨hp'.1, hq⟩).1 hp⟩
  · rintro ⟨q, hq⟩
    have hq' := X.basicOpen_le _ hq
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ x))
    exact ⟨p, (key p q ⟨hq'.1, hp⟩ hq').2 hq⟩
end GlobalTheory.DescTheta
