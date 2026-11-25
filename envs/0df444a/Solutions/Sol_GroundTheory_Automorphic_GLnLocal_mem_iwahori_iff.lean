-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.mem_iwahori_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:00:45.005907+00:00
-- url     : https://prove2.me/submissions/470c5ab7-ad37-4c8d-aa47-8aa78d85b8a7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_residue_eq_zero_iff_valuation_lt_one
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_residue_ne_zero_iff_valuation_eq_one
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_mem_iwahori
import Theorems.Thm_GroundTheory_Automorphic_borel_diag_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_mem_borel_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset ValuativeRel
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution {g : GL (Fin n) F} :
    g ∈ iwahori F n ↔ (∀ i j, valuation F (g i j) ≤ 1) ∧
      (∀ i j, j < i → valuation F (g i j) < 1) ∧ ∀ i, valuation F (g i i) = 1 := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    change residueReduction F n u ∈ borel n _ at hu
    refine ⟨fun i j => (Valuation.mem_integer_iff _ _).mp (u i j).2, fun i j hij => ?_,
      fun i => ?_⟩
    · exact (residue_eq_zero_iff_valuation_lt_one F (u i j)).mp ((mem_borel_iff _).mp hu i j hij)
    · exact (residue_ne_zero_iff_valuation_eq_one F (u i i)).mp (borel_diag_ne_zero hu i)
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨x, hx, hxg⟩ := exists_mem_iwahori F n (g : Matrix (Fin n) (Fin n) F) h1 h2 h3
    rwa [show x = g from Units.ext hxg] at hx
end GroundTheory.Automorphic.GLnLocal
