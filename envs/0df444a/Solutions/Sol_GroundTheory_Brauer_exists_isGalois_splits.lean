-- Prove2me | solution 1 for GroundTheory.Brauer.exists_isGalois_splits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:19.840321+00:00
-- url     : https://prove2.me/submissions/6fdbc0b8-5b14-49bc-aa41-8aad30b6328c

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Degree
import Definitions.Def_GroundTheory_Brauer_Splitting
import Theorems.Thm_GroundTheory_Brauer_isSeparable_coe_iff
import Theorems.Thm_GroundTheory_Brauer_nonempty_algEquiv_matrix_of_maximal
import Theorems.Thm_GroundTheory_Brauer_exists_maximal_isSeparable
import Theorems.Thm_GroundTheory_Brauer_nonempty_algEquiv_matrix_of_algHom_field
import Theorems.Thm_GroundTheory_Brauer_nonempty_algEquiv_matrix_of_matrix
import Theorems.Thm_GroundTheory_Brauer_isCentral_of_isCentral_matrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct Module
universe u v w
variable {K : Type u} [Field K]
namespace GroundTheory.Brauer
theorem _root_.solution (A : Type v) [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K A] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ IsGalois K L ∧
      ∃ n : ℕ, Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  obtain ⟨m, _, D, _, _, _, ⟨eA⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A
  have : Algebra.IsCentral K (Matrix (Fin m) (Fin m) D) := Algebra.IsCentral.of_algEquiv K _ _ eA
  have : Algebra.IsCentral K D := isCentral_of_isCentral_matrix (ι := Fin m)
  obtain ⟨F, hFc, hFmax, hFs⟩ := exists_maximal_isSeparable (K := K) (D := D)
  let _ : Field F := fieldOfIsMulCommutative F
  obtain ⟨eD⟩ := nonempty_algEquiv_matrix_of_maximal F hFmax
  have : Algebra.IsSeparable K F := ⟨fun z ↦ (isSeparable_coe_iff z).mp (hFs z z.2)⟩
  let σ : F →ₐ[K] SeparableClosure K := IsSepClosed.lift (K := K) (L := F) (M := SeparableClosure K)
  let _ : Algebra F (SeparableClosure K) := σ.toRingHom.toAlgebra
  have : IsScalarTower K F (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun k ↦ (σ.commutes k).symm
  obtain ⟨e⟩ := nonempty_algEquiv_matrix_of_matrix eA eD
  exact ⟨IntermediateField.normalClosure K F (SeparableClosure K), inferInstance, inferInstance, inferInstance,
    inferInstance, _, nonempty_algEquiv_matrix_of_algHom_field
      (IsScalarTower.toAlgHom K F (IntermediateField.normalClosure K F (SeparableClosure K))) e⟩
end GroundTheory.Brauer
