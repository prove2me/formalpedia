-- Prove2me | solution 1 for GlobalTheory.SW.Hyper.exists_fun
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:42.450845+00:00
-- url     : https://prove2.me/submissions/597265a5-83ab-453d-a102-dcc80355b330

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Hyper
variable {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
namespace GlobalTheory.SW.Hyper
theorem _root_.solution (P : Ideal O) [hP : P.IsMaximal] (N : Submodule O M) (v : M) (hv : v ∉ N)
    (hPv : ∀ c ∈ P, c • v ∈ N) (hc : ∀ x, ∃ r : O, x - r • v ∈ N) :
    ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N := by
  classical
  let g : O →ₗ[O] M ⧸ N := LinearMap.toSpanSingleton O (M ⧸ N) (N.mkQ v)
  have hker : LinearMap.ker g = P := by
    ext r
    simp only [LinearMap.mem_ker, g, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro h
      by_contra hr
      obtain ⟨y, i, hi, hyi⟩ := hP.exists_inv hr
      apply hv
      have hv' : v = y • (r • v) + i • v := by rw [smul_smul, ← add_smul, hyi, one_smul]
      rw [hv']
      exact N.add_mem (N.smul_mem y h) (hPv i hi)
    · exact hPv r
  have hs : Function.Surjective g := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N z
    obtain ⟨r, hr⟩ := hc x
    refine ⟨r, ?_⟩
    simp only [g, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← neg_sub]
    exact N.neg_mem hr
  let e : (O ⧸ P) ≃ₗ[O] M ⧸ N :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (g.quotKerEquivOfSurjective hs)
  refine ⟨e.symm.toLinearMap ∘ₗ N.mkQ, ?_, ?_⟩
  · intro h0
    apply hv
    have h1 : (e.symm.toLinearMap ∘ₗ N.mkQ) v = 0 := by rw [h0]; rfl
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using h1
  · rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]
end GlobalTheory.SW.Hyper
