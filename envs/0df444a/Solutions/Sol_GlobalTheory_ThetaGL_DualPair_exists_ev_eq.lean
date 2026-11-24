-- Prove2me | solution 1 for GlobalTheory.ThetaGL.DualPair.exists_ev_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:48:25.265901+00:00
-- url     : https://prove2.me/submissions/b24cb28c-0beb-4129-852b-254bbaac8442

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_IsParahoricVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairContragredientQuotient
import Theorems.Thm_GlobalTheory_ThetaGL_DualPair_ev_tmul
import Theorems.Thm_GlobalTheory_ThetaGL_DualPair_exists_fixed
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
theorem _root_.solution (π : Representation ℂ G W) (hπ : IsAdmissible π) (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (T : W →ₗ[ℂ] V)
    (hT : ∀ k ∈ K, ∀ x, T (π k x) = T x) : ∃ t, ev V π t = T := by
  haveI : FiniteDimensional ℂ (fixed π K) := hπ.2 K hKo hKc
  have hle : LinearMap.range T ≤ (fixed π K).map T := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨w', hw', h⟩ := exists_fixed (V := V) π hπ.1 K hKc w
    exact ⟨w', hw', (h T hT).symm⟩
  haveI : FiniteDimensional ℂ (LinearMap.range T) := Submodule.finiteDimensional_of_le hle
  let b := Module.finBasis ℂ (LinearMap.range T)
  let l : _ → Module.Dual ℂ W := fun i => b.coord i ∘ₗ T.rangeRestrict
  have hl : ∀ i, l i ∈ smoothPart π.dual := fun i =>
    mem_smoothPart_of_nhds (Filter.mem_of_superset (hKo.mem_nhds (one_mem K)) fun g hg => by
      refine LinearMap.ext fun x => ?_
      show l i (π g⁻¹ x) = l i x
      have : T.rangeRestrict (π g⁻¹ x) = T.rangeRestrict x :=
        Subtype.ext (hT _ (inv_mem hg) x)
      simp only [l, LinearMap.comp_apply, this])
  refine ⟨∑ i, (b i : V) ⊗ₜ[ℂ] (⟨l i, hl i⟩ : smoothPart π.dual), LinearMap.ext fun w => ?_⟩
  rw [map_sum, LinearMap.sum_apply]
  have h2 : ((∑ i, b.repr (T.rangeRestrict w) i • b i : LinearMap.range T) : V) = T w := by
    rw [b.sum_repr]
    rfl
  rw [Submodule.coe_sum] at h2
  exact h2
end GlobalTheory.ThetaGL.DualPair
