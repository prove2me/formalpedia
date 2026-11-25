-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.cellUnion_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:22.086414+00:00
-- url     : https://prove2.me/submissions/b978dd94-a2f5-4634-8b3f-9d9f688103f5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_cellUnion
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {X : Type*} {k : ℕ} (C : Fin k → Set X)
variable {C}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (j : Fin k) : cellUnion C ((j : ℕ) + 1) = cellUnion C j ∪ C j := by
  ext x
  simp only [mem_cellUnion, mem_union]
  constructor
  · rintro ⟨l, hl, hx⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | hl
    · exact Or.inl ⟨l, hl, hx⟩
    · exact Or.inr (Fin.ext hl ▸ hx)
  · rintro (⟨l, hl, hx⟩ | hx)
    · exact ⟨l, by omega, hx⟩
    · exact ⟨j, by omega, hx⟩
end GroundTheory.Automorphic.Parabolic
