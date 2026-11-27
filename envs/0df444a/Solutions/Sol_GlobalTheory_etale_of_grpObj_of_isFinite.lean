-- Prove2me | solution 1 for GlobalTheory.etale_of_grpObj_of_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:37:03.452966+00:00
-- url     : https://prove2.me/submissions/42603f3b-0fbd-4173-af72-ab463b969f65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsCounitDerivationCounitComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Coalgebra Bialgebra HopfAlgebra WithConv
open scoped TensorProduct
open GlobalTheory
open CategoryTheory AlgebraicGeometry
universe u
variable {k : Type u} [Field k] [CharZero k] {G : Scheme.{u}} (f : G ⟶ Spec (.of k))
  [GrpObj (Over.mk f)]
namespace GlobalTheory
theorem _root_.solution [IsFinite f] : Etale f := by
  have : IsAffine G := isAffine_of_isAffineHom f
  have := isReduced_of_grpObj_of_isAffine f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (G.isoSpec.inv ≫ f)
  suffices h : Etale (Spec.map φ) by
    have e : f = G.isoSpec.hom ≫ Spec.map φ := by rw [hφ, Iso.hom_inv_id_assoc]
    rw [e]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  have h1 : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at h1
  algebraize [φ.hom]
  exact etale_of_isReduced_of_perfectField k Γ(G, ⊤)
end GlobalTheory
