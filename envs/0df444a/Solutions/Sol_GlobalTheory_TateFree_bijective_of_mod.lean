-- Prove2me | solution 1 for GlobalTheory.TateFree.bijective_of_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:58:20.841671+00:00
-- url     : https://prove2.me/submissions/1ca2e83b-9e78-4d11-9b84-6c8f98a6f98a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply
attribute [local simp] GlobalTheory.PDiv.digit_zero
attribute [local simp] GlobalTheory.PDiv.muChar_muT
attribute [local simp] GlobalTheory.PDivGroup.muLieGen_dlogT



set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory
open GlobalTheory.TateFree
variable {p : ℕ} [Fact p.Prime] {M N : Type} [AddCommGroup M] [Module ℤ_[p] M] [AddCommGroup N]
  [Module ℤ_[p] N]
namespace GlobalTheory.TateFree
theorem _root_.solution [Module.Finite ℤ_[p] M] [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] N]
    [Module.Free ℤ_[p] N] (f : M →ₗ[ℤ_[p]] N) (hr : finrank ℤ_[p] M = finrank ℤ_[p] N)
    (h : ∀ x, (∃ z, (p : ℤ_[p]) • z = f x) → ∃ y, (p : ℤ_[p]) • y = x) :
    Function.Bijective f := by
  obtain ⟨e⟩ := (FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq).2 hr.symm
  suffices H : IsUnit (LinearMap.det (e.toLinearMap ∘ₗ f)) by
    have h1 := ((LinearMap.isUnit_iff_isUnit_det _).2 H)
    rw [Module.End.isUnit_iff] at h1
    exact (Function.Bijective.of_comp_iff' e.bijective f).1 h1
  let b := Module.finBasis ℤ_[p] M
  let A := LinearMap.toMatrix b b (e.toLinearMap ∘ₗ f)
  rw [← LinearMap.det_toMatrix b, ← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod,
    RingHom.mem_ker, RingHom.map_det]
  intro h0
  obtain ⟨v, hv, hA⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  let c : _ → ℤ_[p] := fun i => ((v i).val : ℤ_[p])
  have hc : ∀ i, PadicInt.toZMod (c i) = v i := fun i => by simp [c]
  have h1 : ∀ i, ∃ d : ℤ_[p], d * p = A.mulVec c i := fun i => by
    have h1 : A.mulVec c i ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [RingHom.mem_ker, RingHom.map_mulVec, show PadicInt.toZMod ∘ c = v from funext hc]
      exact congrFun hA i
    rwa [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h1
  choose d hd using h1
  obtain ⟨y, hy⟩ := h (b.equivFun.symm c) ⟨e.symm (b.equivFun.symm d), e.injective <|
    b.equivFun.injective <| funext fun i => by
      have h2 := congrFun (LinearMap.toMatrix_mulVec_repr b b (e.toLinearMap ∘ₗ f)
        (b.equivFun.symm c)) i
      rw [← b.equivFun_apply, b.equivFun.apply_symm_apply] at h2
      rw [map_smul, map_smul, e.apply_symm_apply, b.equivFun.apply_symm_apply, Pi.smul_apply,
        smul_eq_mul, mul_comm, hd]
      exact h2⟩
  refine hv (funext fun i => ?_)
  have h3 := congrFun (congrArg b.equivFun hy) i
  rw [map_smul, b.equivFun.apply_symm_apply] at h3
  rw [← hc, ← h3]
  simp
end GlobalTheory.TateFree
