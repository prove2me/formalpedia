-- Prove2me | solution 1 for GlobalTheory.HermUnimod.fixed_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:29:09.701164+00:00
-- url     : https://prove2.me/submissions/e82cf323-27af-41df-8b5e-984f6938768b

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormOneAddEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.HermUnimod
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]
namespace GlobalTheory.HermUnimod
theorem _root_.solution (a : E) (ha : star a = a) : ∃ u : F, algebraMap F E u = a := by
  let L : E →ₗ[F] E :=
    { toFun := fun y => star y - y
      map_add' := by
        intro x y
        simp only [star_add]
        abel
      map_smul' := by
        intro c y
        simp only [Algebra.smul_def, star_mul', Unram.star_fix, RingHom.id_apply, mul_sub] }
  have hfin : Module.finrank F E = 2 := Unram.finrank_eq
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hlt : LinearMap.ker L < ⊤ := by
    obtain ⟨y, hy⟩ := Unram.star_ne (F := F) (E := E)
    refine lt_top_iff_ne_top.2 fun h => hy ?_
    have : y ∈ LinearMap.ker L := h ▸ Submodule.mem_top
    simpa [L, sub_eq_zero] using this
  have h1 : Module.finrank F (LinearMap.ker L) < 2 := hfin ▸ Submodule.finrank_lt hlt.ne
  have hle : LinearMap.range (Algebra.linearMap F E) ≤ LinearMap.ker L := by
    rintro _ ⟨x, rfl⟩
    simp [L, Unram.star_fix]
  have hr : Module.finrank F (LinearMap.range (Algebra.linearMap F E)) = 1 := by
    rw [LinearMap.finrank_range_of_inj (algebraMap F E).injective, Module.finrank_self]
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hmem : a ∈ LinearMap.ker L := by simp [L, ha]
  rw [← heq] at hmem
  obtain ⟨u, hu⟩ := hmem
  exact ⟨u, hu⟩
end GlobalTheory.HermUnimod
