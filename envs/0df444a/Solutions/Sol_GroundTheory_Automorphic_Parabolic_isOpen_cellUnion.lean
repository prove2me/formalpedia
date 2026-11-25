-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isOpen_cellUnion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:35:00.620585+00:00
-- url     : https://prove2.me/submissions/4af4ecf8-e53c-460c-8359-cb852c9276b5

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
variable [TopologicalSpace X]
variable (hdisj : Pairwise fun i j => Disjoint (C i) (C j)) (hcov : ∀ x, ∃ l, x ∈ C l)
  (hcl : ∀ j, closure (C j) ⊆ ⋃ l : Fin k, ⋃ (_ : j ≤ l), C l)
include hdisj hcov hcl
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (j : ℕ) : IsOpen (cellUnion C j) := by
  have hc : (cellUnion C j)ᶜ = ⋃ l : Fin k, ⋃ (_ : j ≤ (l : ℕ)), closure (C l) := by
    ext x
    simp only [mem_compl_iff, mem_cellUnion, mem_iUnion, not_exists, not_and, exists_prop]
    constructor
    · intro h
      obtain ⟨l, hl⟩ := hcov x
      exact ⟨l, not_lt.1 fun h' => h l h' hl, subset_closure hl⟩
    · rintro ⟨l, hjl, hx⟩ l' hl' hx'
      obtain ⟨l'', hll'', hx''⟩ := mem_iUnion₂.1 (hcl l hx)
      have : l'' = l' := by
        by_contra hne
        exact Set.disjoint_left.1 (hdisj hne) hx'' hx'
      subst this
      have : (l : ℕ) ≤ l'' := hll''
      omega
  have hc' : (⋃ l : Fin k, ⋃ (_ : j ≤ (l : ℕ)), closure (C l)) =
      ⋃ l ∈ Finset.univ.filter (fun l : Fin k => j ≤ (l : ℕ)), closure (C l) := by
    ext x
    simp
  rw [← isClosed_compl_iff, hc, hc']
  exact isClosed_biUnion_finset fun l _ => isClosed_closure
end GroundTheory.Automorphic.Parabolic
