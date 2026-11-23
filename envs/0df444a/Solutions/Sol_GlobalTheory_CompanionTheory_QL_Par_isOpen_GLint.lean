-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Par.isOpen_GLint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:42.061005+00:00
-- url     : https://prove2.me/submissions/c1269d01-7156-4937-8e6c-d6a6b8384c4d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricSubgroupCompactOpenMeasure
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Par_isOpen_O

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
theorem _root_.solution (h : LF O ϖ nrm q) (n : ℕ) : IsOpen (GLint O n : Set (GL (Fin n) F)) := by
  have hv : ∀ a b : Fin n, Continuous fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) a b :=
    fun a b => Units.continuous_val.matrix_elem a b
  have hw : ∀ a b : Fin n, Continuous fun g : GL (Fin n) F =>
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a b :=
    fun a b => (hv a b).comp continuous_inv
  have e : (GLint O n : Set (GL (Fin n) F)) =
      (⋂ a, ⋂ b, (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) a b) ⁻¹' (O : Set F)) ∩
      (⋂ a, ⋂ b, (fun g : GL (Fin n) F =>
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a b) ⁻¹' (O : Set F)) := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [e]
  exact (isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
      (isOpen_O h).preimage (hv a b)).inter
    (isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
      (isOpen_O h).preimage (hw a b))
end GlobalTheory.CompanionTheory.QL.Par
