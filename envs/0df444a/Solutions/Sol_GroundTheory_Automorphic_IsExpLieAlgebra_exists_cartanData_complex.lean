-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.exists_cartanData_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:09:47.810128+00:00
-- url     : https://prove2.me/submissions/3745ebba-a4ba-4370-8b12-7213c4c47721

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Theorems.Thm_GroundTheory_Automorphic_exists_cartanBasis
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_expG_smul_mem_maxCompact_complex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
open NormedSpace
open scoped Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Automorphic
namespace IsExpLieAlgebra
theorem _root_.solution {G : Subgroup (Matrix ι ι ℂ)ˣ}
    {𝔤 : Submodule ℝ (Matrix ι ι ℂ)} (h : IsExpLieAlgebra G 𝔤) (hstar : ∀ X ∈ 𝔤, Xᴴ ∈ 𝔤) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ h.lieSubalgebra) (ε : Fin d → ℝ),
      (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (∀ i j, traceForm h.lieSubalgebra (b i) (b j) = if i = j then ε i else 0) ∧
      ∀ i, ε i = -1 → ∀ t : ℝ, h.expG (t • h.ofLie (b i)) ∈ maxCompact G := by
  obtain ⟨d, b, ε, hε, horth, hskew⟩ := exists_cartanBasis (L := h.lieSubalgebra) hstar
  exact ⟨d, b, ε, hε, horth, fun i hi t => h.expG_smul_mem_maxCompact_complex (hskew i hi) t⟩
end IsExpLieAlgebra
end GroundTheory.Automorphic
