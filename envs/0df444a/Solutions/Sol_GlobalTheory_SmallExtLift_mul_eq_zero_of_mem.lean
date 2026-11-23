-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.mul_eq_zero_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:43:34.747103+00:00
-- url     : https://prove2.me/submissions/aec382c6-2d94-47e7-aad1-23750ddac928

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension

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
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SmallExtLift
variable {X Y Z : Scheme.{0}}
variable {R : Type} [CommRing R]
namespace GlobalTheory.SmallExtLift
theorem _root_.solution {B : Type*} [CommRing B] (c : R →+* B) {I : Ideal R} {ε : R}
    (h : ∀ a ∈ I, a * ε = 0) {b : B} (hb : b ∈ I.map c) : c ε * b = 0 := by
  have : I.map c ≤ RingHom.ker (RingHom.id B) ⊔ (Ideal.span {c ε}).annihilator := by
    refine le_sup_of_le_right (Ideal.map_le_iff_le_comap.2 fun a ha => ?_)
    rw [Ideal.mem_comap, Ideal.span, Submodule.mem_annihilator_span_singleton, smul_eq_mul,
      ← map_mul, h a ha, map_zero]
  have h2 := this hb
  rw [(RingHom.injective_iff_ker_eq_bot _).1 (fun _ _ e => e), bot_sup_eq, Ideal.span,
    Submodule.mem_annihilator_span_singleton, smul_eq_mul] at h2
  rw [mul_comm, h2]
end GlobalTheory.SmallExtLift
