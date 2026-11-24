-- Prove2me | solution 1 for GlobalTheory.exists_algHom_ker_eq_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:38:05.256024+00:00
-- url     : https://prove2.me/submissions/7134e8e1-1978-4e6f-969a-46a0d3b84835

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TensorEqZeroOfForallGeometricPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (F B : Type) [Field F] [IsAlgClosed F] [CommRing B]
    [Algebra F B] [Module.Finite F B] (m : Ideal B) [m.IsMaximal] :
    ∃ ψ : B →ₐ[F] F, ∀ b, ψ b = 0 → b ∈ m := by
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  have hb : Function.Bijective (algebraMap F (B ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : F ≃ₐ[F] (B ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId F (B ⧸ m)) hb
  refine ⟨(e.symm : (B ⧸ m) →ₐ[F] F).comp (Ideal.Quotient.mkₐ F m), fun b h => ?_⟩
  have h' : e.symm (Ideal.Quotient.mk m b) = 0 := h
  rw [map_eq_zero_iff _ e.symm.injective] at h'
  exact Ideal.Quotient.eq_zero_iff_mem.mp h'
end GlobalTheory
