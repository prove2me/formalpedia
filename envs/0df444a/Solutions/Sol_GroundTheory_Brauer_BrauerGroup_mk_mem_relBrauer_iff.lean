-- Prove2me | solution 1 for GroundTheory.Brauer.BrauerGroup.mk_mem_relBrauer_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:43:40.903261+00:00
-- url     : https://prove2.me/submissions/712785c6-65fd-40b5-a6ab-c60a131adf34

import Mathlib
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Theorems.Thm_GroundTheory_Brauer_BrauerGroup_baseChange_mk
import Theorems.Thm_GroundTheory_Brauer_BrauerGroup_mem_relBrauer_iff
import Theorems.Thm_GroundTheory_Brauer_BrauerGroup_one_def
import Theorems.Thm_GroundTheory_Brauer_baseChangeTensor_tmul
import Theorems.Thm_GroundTheory_Brauer_isBrauerEquivalent_iff_nonempty_algEquiv
import Theorems.Thm_GroundTheory_Brauer_isBrauerEquivalent_of_algEquiv_matrix
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.baseChangeTensor_tmul
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier


attribute [local simp] GroundTheory.Brauer.BrauerGroup.baseChange_mk

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct
universe u v
open GroundTheory.Brauer.BrauerGroup
variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
variable {K L}
namespace GroundTheory.Brauer.BrauerGroup
theorem _root_.solution (A : CSA.{u, u} K) :
    ⟦A⟧ ∈ relBrauer K L ↔
      ∃ n : ℕ, Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) := by
  rw [mem_relBrauer_iff, baseChange_mk, BrauerGroup.one_def, Quotient.eq]
  change IsBrauerEquivalent (baseChangeCSA L A) (oneCSA L) ↔ _
  have : IsArtinianRing (baseChangeCSA L A) := IsArtinianRing.of_finite L _
  obtain ⟨k, hk, D, _, _, _, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite L (baseChangeCSA L A)
  constructor
  · intro h
    obtain ⟨g⟩ := (isBrauerEquivalent_iff_nonempty_algEquiv e
      ((matrixFinOneAlgEquiv (K := L) L).symm)).mp h
    exact ⟨k, ⟨e.trans g.mapMatrix⟩⟩
  · rintro ⟨n, ⟨f⟩⟩
    have hn : n ≠ 0 := by
      rintro rfl
      exact one_ne_zero (f.injective (Subsingleton.elim _ _) : (1 : L ⊗[K] A) = 0)
    have : NeZero n := ⟨hn⟩
    exact isBrauerEquivalent_of_algEquiv_matrix (C := L) f
      ((matrixFinOneAlgEquiv (K := L) L).symm)
end GroundTheory.Brauer.BrauerGroup
