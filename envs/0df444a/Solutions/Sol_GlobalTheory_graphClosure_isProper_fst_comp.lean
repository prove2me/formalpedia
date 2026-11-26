-- Prove2me | solution 1 for GlobalTheory.graphClosure.isProper_fst_comp
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:21:59.05453+00:00
-- url     : https://prove2.me/submissions/56cfebf6-5efe-4a64-b433-268f977912fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
noncomputable section
variable {S Z₁ Z₂ U T T' : Scheme.{u}} (f₁ : Z₁ ⟶ S) (f₂ : Z₂ ⟶ S) (u : U ⟶ Z₁) (φ : U ⟶ Z₂)
  (h : u ≫ f₁ = φ ≫ f₂)
open GlobalTheory.graphClosure
theorem _root_.solution [IsProper f₁] [IsProper f₂] : IsProper (fst f₁ f₂ u φ h ≫ f₁) := by
  first
    | (intros; rfl)
    | exact Iff.rfl
    | (intros; ext; rfl)
    | (intros; exact (Finset.sup_univ_eq_ciSup _))
    | (intros; simp [GlobalTheory.mem_saturation_iff'])
    | (intros; exact (isoTransvection.pow ..))
    | (intros; ext; simp)
    | (intros; exact?)

