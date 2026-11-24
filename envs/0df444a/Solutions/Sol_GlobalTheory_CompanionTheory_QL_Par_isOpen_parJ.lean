-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Par.isOpen_parJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:59:56.405903+00:00
-- url     : https://prove2.me/submissions/95ae7b07-d118-4704-b846-d27f7c79adcb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricSubgroupCompactOpenMeasure
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Par_isOpen_O
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Par_isOpen_GLint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Par
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.Par
theorem _root_.solution (h : LF O ϖ nrm q) (r c : ℕ) : IsOpen (parJ O ϖ r c) := by
  have hP : IsOpen {x : F | ∃ o ∈ O, x = ϖ * o} := by
    have e : {x : F | ∃ o ∈ O, x = ϖ * o} = (fun x => ϖ⁻¹ * x) ⁻¹' (O : Set F) := by
      ext x
      constructor
      · rintro ⟨o, ho, rfl⟩
        simpa [h.ne] using ho
      · intro hx
        exact ⟨_, hx, by simp [h.ne]⟩
    rw [e]
    exact (isOpen_O h).preimage (continuous_const.mul continuous_id)
  have e : parJ O ϖ r c = (GLint O (r + c) : Set (GL (Fin (r + c)) F)) ∩
      ⋂ i : Fin c, ⋂ j : Fin r, (fun g : GL (Fin (r + c)) F =>
        (g : Matrix (Fin (r + c)) (Fin (r + c)) F) (Fin.natAdd r i) (Fin.castAdd c j)) ⁻¹'
          {x : F | ∃ o ∈ O, x = ϖ * o} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [e]
  exact (isOpen_GLint h _).inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    hP.preimage (Units.continuous_val.matrix_elem _ _))
end GlobalTheory.CompanionTheory.QL.Par
