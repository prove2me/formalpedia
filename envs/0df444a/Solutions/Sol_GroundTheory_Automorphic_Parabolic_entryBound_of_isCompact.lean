-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.entryBound_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:51:27.676254+00:00
-- url     : https://prove2.me/submissions/f6accc8a-d482-4e72-b620-ea4af56d477d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_pow_mul_mem_of_isCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {S : Set (GL (Fin n) F)} (hS : IsCompact S) :
    ∃ e : ℕ, ∀ g ∈ S, EntryBound F e (g : Matrix (Fin n) (Fin n) F) ∧
      EntryBound F e ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨e, he⟩ := exists_pow_mul_mem_of_isCompact F n (hS.union (hS.image continuous_inv))
  exact ⟨e, fun g hg => ⟨fun i j => he g (Or.inl hg) i j,
    fun i j => he g⁻¹ (Or.inr ⟨g, hg, rfl⟩) i j⟩⟩
end GroundTheory.Automorphic.Parabolic
