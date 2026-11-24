-- Prove2me | solution 1 for GlobalTheory.KeyKa.exists_basis_det_ne_zero_of_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:31:04.722939+00:00
-- url     : https://prove2.me/submissions/ea26f794-d3ac-4a81-b89a-9d65db4e88bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsUnitDetOfProductMapNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PointMatrixMulLeftMulMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrEqJacobianOfIntegralPoints
import Theorems.Thm_GlobalTheory_DiscrJacobian_der_tmul
import Theorems.Thm_GlobalTheory_DiscrJacobian_mu_tmul
import Theorems.Thm_GlobalTheory_DiscrJacobian_pairing_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DiscrJacobian.der_tmul
attribute [local simp] GlobalTheory.DiscrJacobian.mu_tmul
attribute [local simp] GlobalTheory.DiscrJacobian.pairing_tmul



set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa
namespace GlobalTheory.KeyKa
theorem _root_.solution {O B Ix : Type} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [AddCommGroup B] [Module O B] [Fintype Ix] [DecidableEq Ix]
    (φ : B →ₗ[O] (Ix → O)) (hφ : Function.Injective φ) (c : O) (hc : c ≠ 0)
    (hs : ∀ t : Ix → O, ∃ y, φ y = c • t) :
    ∃ b : Module.Basis Ix O B, (Matrix.of fun a a' => φ (b a') a).det ≠ 0 := by
  have hfin : Module.Finite O B := Module.Finite.of_injective φ hφ
  have hfree : Module.Free O B :=
    Module.Free.of_equiv (LinearEquiv.ofInjective φ hφ).symm
  have h1 : Module.finrank O B ≤ Module.finrank O (Ix → O) :=
    LinearMap.finrank_le_finrank_of_injective hφ
  have h2 : Module.finrank O (Ix → O) ≤ Module.finrank O (LinearMap.range φ) := by
    let ψ : (Ix → O) →ₗ[O] LinearMap.range φ :=
      LinearMap.codRestrict _ (c • LinearMap.id) (fun t => by
        obtain ⟨y, hy⟩ := hs t
        exact ⟨y, hy⟩)
    refine LinearMap.finrank_le_finrank_of_injective (f := ψ) ?_
    rw [injective_iff_map_eq_zero]
    intro t ht
    have h3 : c • t = 0 := congrArg Subtype.val ht
    exact (smul_eq_zero.1 h3).resolve_left hc
  rw [← (LinearEquiv.ofInjective φ hφ).finrank_eq] at h2
  have h3 : Module.finrank O B = Fintype.card Ix := by
    rw [le_antisymm h1 h2, Module.finrank_fintype_fun_eq_card]
  let b : Module.Basis Ix O B :=
    (Module.finBasisOfFinrankEq O B h3).reindex (Fintype.equivFin Ix).symm
  refine ⟨b, fun h0 => ?_⟩
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have h4 : φ (∑ a, v a • b a) = 0 := by
    ext a
    have := congrFun hMv a
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [map_sum, Finset.sum_apply, Pi.zero_apply, ← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  have h5 : ∑ a, v a • b a = 0 := hφ (h4.trans (map_zero φ).symm)
  exact hv (funext (Fintype.linearIndependent_iff.1 b.linearIndependent v h5))
end GlobalTheory.KeyKa
