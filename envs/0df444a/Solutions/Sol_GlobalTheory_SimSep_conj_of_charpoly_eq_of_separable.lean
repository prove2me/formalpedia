-- Prove2me | solution 1 for GlobalTheory.SimSep.conj_of_charpoly_eq_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:02:48.169861+00:00
-- url     : https://prove2.me/submissions/c49c8f07-ad34-47f4-bdad-c2620aeb3f26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCyclicVectorOfSeparableCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjOfCharpolyEqOfCharpolySeparable
import Theorems.Thm_GlobalTheory_SimSep_mulVec_aeval_eq_zero_iff
import Theorems.Thm_GlobalTheory_LatOrb_exists_cyclicVector_of_separable_charpoly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.SimSep
namespace GlobalTheory.SimSep
theorem _root_.solution : ∀ (R : Type) [Field R] (m : ℕ)
    (N U : Matrix (Fin m) (Fin m) R), N.charpoly = U.charpoly → N.charpoly.Separable →
    ∃ P : GL (Fin m) R, N * P.val = P.val * U := by
  intro R _ m N U hc hs
  obtain ⟨v, hv⟩ := GlobalTheory.LatOrb.exists_cyclicVector_of_separable_charpoly m N hs
  obtain ⟨w, hw⟩ := GlobalTheory.LatOrb.exists_cyclicVector_of_separable_charpoly m U (hc ▸ hs)
  let φ : R[X] →ₗ[R] (Fin m → R) :=
    { toFun := fun p => aeval N p *ᵥ v
      map_add' := fun a b => by simp [Matrix.add_mulVec]
      map_smul' := fun c a => by simp [Matrix.smul_mulVec] }
  let ψ : R[X] →ₗ[R] (Fin m → R) :=
    { toFun := fun p => aeval U p *ᵥ w
      map_add' := fun a b => by simp [Matrix.add_mulVec]
      map_smul' := fun c a => by simp [Matrix.smul_mulVec] }
  have hφ : Function.Surjective φ := fun u => let ⟨p, hp⟩ := hv u; ⟨p, hp.symm⟩
  have hψ : Function.Surjective ψ := fun u => let ⟨p, hp⟩ := hw u; ⟨p, hp.symm⟩
  have hker : LinearMap.ker ψ = LinearMap.ker φ := by
    ext p
    simp only [LinearMap.mem_ker]
    show aeval U p *ᵥ w = 0 ↔ aeval N p *ᵥ v = 0
    rw [mulVec_aeval_eq_zero_iff U w hw, mulVec_aeval_eq_zero_iff N v hv, hc]
  let T : (Fin m → R) ≃ₗ[R] (Fin m → R) :=
    ((ψ.quotKerEquivOfSurjective hψ).symm.trans (Submodule.quotEquivOfEq _ _ hker)).trans
      (φ.quotKerEquivOfSurjective hφ)
  have hT : ∀ p, T (ψ p) = φ p := by
    intro p
    have h1 : (ψ.quotKerEquivOfSurjective hψ).symm (ψ p) = Submodule.Quotient.mk p := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [T, LinearEquiv.trans_apply, h1, Submodule.quotEquivOfEq_mk]
    rfl
  have hcomm : ∀ x, T (U *ᵥ x) = N *ᵥ T x := by
    intro x
    obtain ⟨p, rfl⟩ := hψ x
    have e1 : U *ᵥ ψ p = ψ (X * p) := by
      show U *ᵥ (aeval U p *ᵥ w) = aeval U (X * p) *ᵥ w
      rw [map_mul, aeval_X, Matrix.mulVec_mulVec]
    have e2 : N *ᵥ φ p = φ (X * p) := by
      show N *ᵥ (aeval N p *ᵥ v) = aeval N (X * p) *ᵥ v
      rw [map_mul, aeval_X, Matrix.mulVec_mulVec]
    rw [e1, hT, hT, e2]
  have hl : T.toLinearMap.comp T.symm.toLinearMap = LinearMap.id :=
    LinearMap.ext fun x => by simp
  have hr : T.symm.toLinearMap.comp T.toLinearMap = LinearMap.id :=
    LinearMap.ext fun x => by simp
  let P : GL (Fin m) R :=
    ⟨LinearMap.toMatrix' T.toLinearMap, LinearMap.toMatrix' T.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp, hl, LinearMap.toMatrix'_id],
      by rw [← LinearMap.toMatrix'_comp, hr, LinearMap.toMatrix'_id]⟩
  refine ⟨P, Matrix.toLin'.injective (LinearMap.ext fun x => ?_)⟩
  simp only [P, Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_toMatrix',
    Matrix.toLin'_apply, LinearEquiv.coe_coe]
  exact (hcomm x).symm
end GlobalTheory.SimSep
