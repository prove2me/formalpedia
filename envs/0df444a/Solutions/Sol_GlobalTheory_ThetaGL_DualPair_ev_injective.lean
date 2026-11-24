-- Prove2me | solution 1 for GlobalTheory.ThetaGL.DualPair.ev_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:31:10.621076+00:00
-- url     : https://prove2.me/submissions/839fdc31-0475-455d-86d8-d5744f1bcbdd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_IsParahoricVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairContragredientQuotient
import Theorems.Thm_GlobalTheory_ThetaGL_DualPair_ev_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ThetaGL.DualPair.ev_tmul

set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct
open GlobalTheory GlobalTheory.ThetaGL GlobalTheory.ThetaGL.DualPair
variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.ThetaGL.DualPair
theorem _root_.solution (π : Representation ℂ G W) : Function.Injective (ev V π) := by
  refine (injective_iff_map_eq_zero _).2 fun t ht => ?_
  let b := Module.Basis.ofVectorSpace ℂ V
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left b t
  have hc : ∀ i ∈ c.support, c i = 0 := by
    intro i hi
    apply Subtype.ext
    refine LinearMap.ext fun w => ?_
    have h0 : ev V π (c.sum fun i n => b i ⊗ₜ[ℂ] n) w = 0 := by rw [ht]; rfl
    have h1 : ∑ j ∈ c.support, ((c j : Module.Dual ℂ W) w) • b j = 0 := by
      rw [← h0, Finsupp.sum, map_sum, LinearMap.sum_apply]
      rfl
    exact linearIndependent_iff'.1 b.linearIndependent c.support _ h1 i hi
  rw [Finsupp.sum]
  exact Finset.sum_eq_zero fun i hi => by rw [hc i hi, TensorProduct.tmul_zero]
end GlobalTheory.ThetaGL.DualPair
