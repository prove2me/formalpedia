-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QuotVan.mulMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:43.319474+00:00
-- url     : https://prove2.me/submissions/8be09d9b-9366-436d-afca-144f73aec8c8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TopoPolish
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MapWithDensityEqOfScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QuotVan
namespace GlobalTheory.CompanionTheory.QuotVan
theorem _root_.solution {Q : Type} [Group Q] (N M : Subgroup Q) (hinf : N ⊓ M = ⊥) :
    Function.Injective (fun p : N × M => (p.1 : Q) * (p.2 : Q)) := by
  rintro ⟨u, m⟩ ⟨u', m'⟩ h
  have h' : (u : Q) * m = u' * m' := h
  have h1 : (u' : Q)⁻¹ * u = m' * (m : Q)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
    exact h'
  have h2 : (u' : Q)⁻¹ * u ∈ N ⊓ M :=
    ⟨N.mul_mem (N.inv_mem u'.2) u.2, by rw [h1]; exact M.mul_mem m'.2 (M.inv_mem m.2)⟩
  rw [hinf, Subgroup.mem_bot] at h2
  have hu : (u : Q) = u' := (inv_mul_eq_one.1 h2).symm
  have hm : (m : Q) = m' := by
    rw [hu] at h'
    exact mul_left_cancel h'
  exact Prod.ext (Subtype.ext hu) (Subtype.ext hm)
end GlobalTheory.CompanionTheory.QuotVan
