-- Prove2me | solution 1 for GlobalTheory.DescTheta.exists_sec_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:59:03.860413+00:00
-- url     : https://prove2.me/submissions/50aa4f2d-2eac-4909-b094-e1d9ce3c4f7b

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
import Theorems.Thm_GlobalTheory_DescTheta_mem_basicOpen_appLE
import Theorems.Thm_GlobalTheory_DescTheta_mem_basicOpen_mul
import Theorems.Thm_GlobalTheory_DescTheta_isQuasicoherent_pushforward
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
import Theorems.Thm_GlobalTheory_QCoh_exists_pow_smul_eq_res
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
theorem _root_.solution {G : Over X} {L : LB G.left} (h : PushInvertible G L)
    {W : X.Opens} (hW : IsAffineOpen W) {x : X} (hx : x ∈ W) :
    ∃ (s : Γ(toMod L, G.hom ⁻¹ᵁ W)) (u : G.left), G.hom u = x ∧
      ∃ i, u ∈ G.left.basicOpen (coord s i) := by
  have := isQuasicoherent_pushforward h
  obtain ⟨V, hV, θ, hθ, -, h2⟩ := h x
  obtain ⟨b, hb, hxb⟩ := hW.exists_basicOpen_le ⟨x, hV⟩ hx
  obtain ⟨n, t, ht⟩ := QCoh.exists_pow_smul_eq_res ((Scheme.Modules.pushforward G.hom).obj (toMod L))
    hW b (X.basicOpen_le b) rfl
    ((toMod L).presheaf.map (homOfLE (G.hom.preimage_mono hb)).op (mkSec θ hθ))
  obtain ⟨u, i, rfl, hi⟩ := h2 x hV
  refine ⟨t, u, rfl, i, ?_⟩
  have e : (G.hom.appLE (X.basicOpen b) (G.hom ⁻¹ᵁ (X.basicOpen b) ⊓ L.U i) inf_le_left).hom
      (resG X (X.basicOpen_le b) b ^ n) *
        resG G.left (inf_le_inf_right _ (G.hom.preimage_mono hb)) (θ i) =
      resG G.left (inf_le_inf_right _ (G.hom.preimage_mono (X.basicOpen_le b)))
        (coord (L := L) t i) := congrArg (fun t => coord (L := L) t i) ht
  have e' := congrArg (fun a => u ∈ G.left.basicOpen a) e
  simp only [mem_basicOpen_mul, mem_basicOpen_resG, mem_basicOpen_appLE, eq_iff_iff] at e'
  have hu : u ∈ G.hom ⁻¹ᵁ (X.basicOpen b) ⊓ L.U i := ⟨hxb, (G.left.basicOpen_le _ hi).2⟩
  refine (e'.1 ⟨⟨hu, ?_⟩, hu, hi⟩).2
  have hb' : IsUnit (resG X (X.basicOpen_le b) b) := X.toRingedSpace.isUnit_res_basicOpen b
  rw [X.basicOpen_of_isUnit (hb'.pow n)]
  exact hxb
end GlobalTheory.DescTheta
