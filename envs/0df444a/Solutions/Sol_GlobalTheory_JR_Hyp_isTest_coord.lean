-- Prove2me | solution 1 for GlobalTheory.JR.Hyp.isTest_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:59:47.551444+00:00
-- url     : https://prove2.me/submissions/d11dd539-b63e-4ccc-b20f-63285bf9ac01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportIdempotentCoordin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Hyp
namespace GlobalTheory.JR.Hyp
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (e : A.L), (∀ p, Hyp.ci A e (Hyp.cc A e p) = p) → (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) → (∀ φ : A.L → ℂ, IsTest φ → IsTest (fun p => φ (Hyp.cc A e p))) ∧ ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun y => Φ (Hyp.ci A e y)) := by
  intro F E _ _ _ _ _ A e h1 h2
  let ι : A.K →ₗ[F] A.L := (Algebra.linearMap A.K A.L).restrictScalars F
  let f : (A.K × A.K) →ₗ[F] A.L :=
    LinearMap.mulRight F e ∘ₗ ι ∘ₗ LinearMap.fst F A.K A.K +
      LinearMap.mulRight F (1 - e) ∘ₗ ι ∘ₗ LinearMap.snd F A.K A.K
  let tr : A.L →ₗ[F] A.K := (Algebra.trace A.K A.L).restrictScalars F
  let g : A.L →ₗ[F] A.K × A.K :=
    LinearMap.prod (tr ∘ₗ LinearMap.mulRight F e) (tr ∘ₗ LinearMap.mulRight F (1 - e))
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  have hf : ∀ p, f p = cc A e p := fun p => rfl
  have hg : ∀ y, g y = ci A e y := fun y => rfl
  have cf : Continuous (cc A e) := by
    have := IsModuleTopology.continuous_of_linearMap f
    simpa [funext hf] using this
  have cg : Continuous (ci A e) := by
    have := IsModuleTopology.continuous_of_linearMap g
    simpa [funext hg] using this
  let H : (A.K × A.K) ≃ₜ A.L :=
    { toFun := cc A e, invFun := ci A e, left_inv := h1, right_inv := h2,
      continuous_toFun := cf, continuous_invFun := cg }
  refine ⟨fun φ hφ => ⟨hφ.1.comp_continuous cf, hφ.2.comp_homeomorph H⟩,
    fun Φ hΦ => ⟨hΦ.1.comp_continuous cg, hΦ.2.comp_homeomorph H.symm⟩⟩
end GlobalTheory.JR.Hyp
