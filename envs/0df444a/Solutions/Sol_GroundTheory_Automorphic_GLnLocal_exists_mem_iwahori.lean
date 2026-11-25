-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.exists_mem_iwahori
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:55:31.360366+00:00
-- url     : https://prove2.me/submissions/4cef03a4-d967-4e19-9eef-7ded3fe46518

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_residueReduction_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_residue_eq_zero_iff_valuation_lt_one
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_residue_ne_zero_iff_valuation_eq_one
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
theorem _root_.solution (M : Matrix (Fin n) (Fin n) F)
    (h1 : ∀ i j, valuation F (M i j) ≤ 1) (h2 : ∀ i j, j < i → valuation F (M i j) < 1)
    (h3 : ∀ i, valuation F (M i i) = 1) :
    ∃ x ∈ iwahori F n, (x : Matrix (Fin n) (Fin n) F) = M := by
  classical
  let A : Matrix (Fin n) (Fin n) 𝒪[F] :=
    Matrix.of fun i j => ⟨M i j, (Valuation.mem_integer_iff _ _).mpr (h1 i j)⟩
  let Ā := (IsLocalRing.residue 𝒪[F]).mapMatrix A
  have hup : Ā.IsUpperTriangular := by
    intro i j hij
    exact (residue_eq_zero_iff_valuation_lt_one F (A i j)).mpr (h2 i j hij)
  have hdiag : ∀ i, Ā i i ≠ 0 := fun i => (residue_ne_zero_iff_valuation_eq_one F (A i i)).mpr (h3 i)
  have hdetĀ : IsUnit Ā.det := by
    rw [det_of_isUpperTriangular hup, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hdiag i
  have hdetA : IsUnit A.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    exact hdetĀ.ne_zero
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det A).mpr hdetA
  refine ⟨integralGLHom F n u, ⟨u, ?_, rfl⟩, ?_⟩
  · change residueReduction F n u ∈ borel n _
    rw [mem_borel_iff]
    intro i j hij
    rw [residueReduction_apply, hu]
    exact hup hij
  · ext i j
    rw [integralGLHom_apply, hu]
    rfl
end GroundTheory.Automorphic.GLnLocal
