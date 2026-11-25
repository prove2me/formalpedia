-- Prove2me | solution 1 for GlobalTheory.IotaInj.eq_zero_of_gs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:49:47.074807+00:00
-- url     : https://prove2.me/submissions/36b840df-9dea-408f-ae38-6ed2d84fcd40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_MemOfNonempty
import Theorems.Thm_GlobalTheory_IotaInj_mem_of_nonempty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.IotaInj
open GlobalTheory.TorusExt
variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.IotaInj
theorem _root_.solution (y : Spec (CommRingCat.of F)) {V : (Spec (CommRingCat.of R)).Opens}
    {p : Spec (CommRingCat.of R)} (hp : p ∈ V) (a : Γ(Spec (CommRingCat.of R), V))
    (h : gs (jFK (R := R) F ≫ jK R) y V a = 0) : a = 0 := by
  by_contra ha
  have : Nonempty V := ⟨⟨p, hp⟩⟩
  have hne : (Spec (CommRingCat.of R)).basicOpen a ≠ ⊥ := fun e => ha ((basicOpen_eq_bot_iff a).1 e)
  obtain ⟨p', hp'⟩ : ∃ p', p' ∈ (Spec (CommRingCat.of R)).basicOpen a := by
    by_contra hc
    exact hne (eq_bot_iff.2 fun z hz => (hc ⟨z, hz⟩).elim)
  have hm : y ∈ (jFK (R := R) F ≫ jK R) ⁻¹ᵁ (Spec (CommRingCat.of R)).basicOpen a := mem_of_nonempty y hp'
  rw [Scheme.preimage_basicOpen, Scheme.mem_basicOpen _ _ y (mem_of_nonempty y hp)] at hm
  rw [gs_eq _ y V (mem_of_nonempty y hp)] at h
  exact hm.ne_zero h
end GlobalTheory.IotaInj
