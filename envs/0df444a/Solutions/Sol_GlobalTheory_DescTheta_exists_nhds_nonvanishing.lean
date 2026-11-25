-- Prove2me | solution 1 for GlobalTheory.DescTheta.exists_nhds_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:02:38.179849+00:00
-- url     : https://prove2.me/submissions/4c92ed5d-0ad9-4afb-850f-4a39484e0df6

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
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
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
    {W : X.Opens} {O : G.left.Opens} (hO : G.hom ⁻¹ᵁ W ≤ O) (s : Γ(toMod L, O)) (u : G.left)
    (hu : G.hom u ∈ W) (hs : ∃ i, u ∈ G.left.basicOpen (coord s i)) :
    ∃ U : X.Opens, U ≤ W ∧ G.hom u ∈ U ∧ ∀ z ∈ U, ∃ u' : G.left, G.hom u' = z ∧
      ∃ i, u' ∈ G.left.basicOpen (coord s i) := by
  obtain ⟨V, hV, θ, -, h1, h2⟩ := h (G.hom u)
  have hle : G.hom ⁻¹ᵁ (W ⊓ V) ≤ O := (G.hom.preimage_mono inf_le_left).trans hO
  obtain ⟨a, ha, -⟩ := h1 (W ⊓ V) inf_le_right _
    (coord_mem ((toMod L).presheaf.map (homOfLE hle).op s))
  have key (i : L.ι) (u' : G.left) (h' : G.hom u' ∈ W ⊓ V) :
      u' ∈ G.left.basicOpen (coord s i) ↔
        G.hom u' ∈ X.basicOpen a ∧ u' ∈ G.left.basicOpen (θ i) := by
    have e' := congrArg (fun a => u' ∈ G.left.basicOpen a) (ha i)
    simp only [coord_map, mem_basicOpen_mul, mem_basicOpen_resG, mem_basicOpen_appLE,
      eq_iff_iff] at e'
    by_cases hi : u' ∈ L.U i
    · have hx : u' ∈ G.hom ⁻¹ᵁ (W ⊓ V) ⊓ L.U i := ⟨h', hi⟩
      simpa only [hx, true_and] using e'
    · exact ⟨fun h => (hi (G.left.basicOpen_le _ h).2).elim,
        fun h => (hi (G.left.basicOpen_le _ h.2).2).elim⟩
  obtain ⟨i, hi⟩ := hs
  refine ⟨X.basicOpen a, (X.basicOpen_le a).trans inf_le_left, ((key i u ⟨hu, hV⟩).1 hi).1,
    fun z hz => ?_⟩
  obtain ⟨u', j, rfl, hj⟩ := h2 z (X.basicOpen_le a hz).2
  exact ⟨u', rfl, j, (key j u' (X.basicOpen_le a hz)).2 ⟨hz, hj⟩⟩
end GlobalTheory.DescTheta
