-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.bijective_mk_affineWeylGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:43:16.970013+00:00
-- url     : https://prove2.me/submissions/ecb8ae4b-2529-442f-936d-001fb5399f53

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_eq_of_affineWeylGL_mem_doubleCoset
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_mem_doubleCoset_affineWeylGL
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset ValuativeRel
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution :
    Function.Bijective fun w : ExtendedAffineWeyl n =>
      DoubleCoset.mk (iwahori F n) (iwahori F n) (affineWeylGL F n w) := by
  constructor
  · intro w w' hww'
    obtain ⟨x, hx, y, hy, hxy⟩ := (DoubleCoset.eq _ _ _ _).mp hww'
    exact eq_of_affineWeylGL_mem_doubleCoset F n (mem_doubleCoset.mpr ⟨x, hx, y, hy, hxy⟩)
  · intro q
    obtain ⟨w, hw⟩ := exists_mem_doubleCoset_affineWeylGL F n q.out
    refine ⟨w, ?_⟩
    simp only
    rw [← mk_eq_of_doubleCoset_eq (doubleCoset_eq_of_mem hw), out_eq']
end GroundTheory.Automorphic.GLnLocal
