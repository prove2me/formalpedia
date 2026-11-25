-- Prove2me | solution 1 for GlobalTheory.ConstFam.linearIndependent_of_isExtension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:10:59.998523+00:00
-- url     : https://prove2.me/submissions/e89773ed-6c74-4c9e-bd6a-dc7b54e1720d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
variable {X X' Y Y' Z : Scheme.{0}}
variable {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
variable {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
namespace GlobalTheory.ConstFam
theorem _root_.solution {k E : Type} [Field k] [Field E] [Algebra k E] {V W : Type} [AddCommGroup V]
    [Module k V] [AddCommGroup W] [Module E W] {a : V →ₛₗ[algebraMap k E] W} (ha : IsExtension a) {ι : Type*}
    {v : ι → V} (hv : LinearIndependent k v) : LinearIndependent E (fun i => a (v i)) := by
  rw [linearIndependent_iff'] at hv ⊢
  intro S c hc i hi
  refine (Module.forall_dual_apply_eq_zero_iff k (c i)).1 fun ℓ => ?_
  obtain ⟨Λ, hΛ⟩ := ha.coord ℓ
  refine hv S (fun i => ℓ (c i)) ?_ i hi
  have := congrArg Λ hc
  rw [map_sum, map_zero] at this
  exact (Finset.sum_congr rfl fun i _ => (hΛ _ _).symm).trans this
end GlobalTheory.ConstFam
