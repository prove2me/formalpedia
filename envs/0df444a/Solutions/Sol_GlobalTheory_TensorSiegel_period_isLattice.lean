-- Prove2me | solution 1 for GlobalTheory.TensorSiegel.period_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:49:52.698046+00:00
-- url     : https://prove2.me/submissions/fa17ead0-8669-43e8-9e5c-1c660eb2ca10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveTensorOmegaStd
import Theorems.Thm_GlobalTheory_TensorSiegel_kron_posDef
import Theorems.Thm_GlobalTheory_TensorSiegel_kron_one_map_im
import Theorems.Thm_GlobalTheory_TensorSiegel_range_period
import Theorems.Thm_GlobalTheory_discreteTopology_periodLattice_of_isUnit
import Theorems.Thm_GlobalTheory_intVec_eq_zero_of_period_eq_zero
import Theorems.Thm_GlobalTheory_span_periodLattice_eq_top_of_isUnit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.PTheta Matrix
open scoped Kronecker
noncomputable section
open GlobalTheory GlobalTheory.TensorSiegel
variable {r h g : ℕ} (σ : Fin r × Fin h ≃ Fin g) {R : Type*} [CommRing R]
namespace GlobalTheory.TensorSiegel
theorem _root_.solution {τ : Matrix (Fin h) (Fin h) ℂ} (hτ : (τ.map Complex.im).PosDef) :
    Function.Injective (period σ τ) ∧ DiscreteTopology (period σ τ).range ∧
      Submodule.span ℝ (Set.range (period σ τ)) = ⊤ := by
  have hu : IsUnit ((kron σ 1 τ).map Complex.im).det := by
    rw [kron_one_map_im]
    exact (isUnit_iff_isUnit_det _).1 (kron_posDef σ PosDef.one hτ).isUnit
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := intVec_eq_zero_of_period_eq_zero hu _ _ hx
    ext u (i | i)
    · simpa [coordFst] using congrFun h1 (σ (u, i))
    · simpa [coordSnd] using congrFun h2 (σ (u, i))
  · rw [range_period]
    exact discreteTopology_periodLattice_of_isUnit hu
  · rw [← AddMonoidHom.coe_range, range_period]
    exact span_periodLattice_eq_top_of_isUnit hu
end GlobalTheory.TensorSiegel
