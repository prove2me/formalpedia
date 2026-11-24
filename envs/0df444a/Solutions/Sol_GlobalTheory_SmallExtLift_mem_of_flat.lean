-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.mem_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:46:08.933497+00:00
-- url     : https://prove2.me/submissions/a02c514e-f068-4416-b3b5-66a0fb69bdbc

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
theorem _root_.solution [IsLocalRing R] {ε : R} (hε : ε ≠ 0) {B : Type} [CommRing B] (c : R →+* B)
    (hf : c.Flat) (a : B) (ha : c ε * a = 0) : a ∈ (IsLocalRing.maximalIdeal R).map c := by
  letI := c.toAlgebra
  haveI : Module.Flat R B := hf
  obtain ⟨l, d, y, hy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := B)
    (f := fun _ : Unit => ε) (x := fun _ => a)
    (by rw [Fintype.sum_unique, Algebra.smul_def]; exact ha)
  have : a = ∑ j, d () j • y j := hy ()
  rw [this]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem c ?_)
  have h := hc j
  rw [Fintype.sum_unique] at h
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact hε (hu.mul_left_eq_zero.1 h)
end GlobalTheory.SmallExtLift
