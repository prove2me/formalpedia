-- Prove2me | solution 1 for GlobalTheory.TateFree.natCard_eq_pow_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:00:53.556065+00:00
-- url     : https://prove2.me/submissions/99a9f074-2106-447e-9cc0-b183a3d6aed0

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
theorem _root_.solution [Module.Finite ℤ_[p] M] [Module.Free ℤ_[p] M] {X : Type}
    [AddCommGroup X] (f : M →+ X) (hf : Function.Surjective f)
    (hk : ∀ x, f x = 0 ↔ ∃ y, (p : ℤ_[p]) • y = x) : Nat.card X = p ^ finrank ℤ_[p] M := by
  let b := Module.finBasis ℤ_[p] M
  let g : M →+ (Fin (finrank ℤ_[p] M) → ZMod p) :=
    AddMonoidHom.pi fun i => (PadicInt.toZMod (p := p)).toAddMonoidHom.comp
      (b.coord i).toAddMonoidHom
  have hg : Function.Surjective g := fun v =>
    ⟨b.equivFun.symm fun i => ((v i).val : ℤ_[p]), funext fun i => by
      change PadicInt.toZMod (b.equivFun (b.equivFun.symm _) i) = _
      rw [LinearEquiv.apply_symm_apply]
      simp⟩
  have hker : f.ker = g.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, hk]
    constructor
    · rintro ⟨y, rfl⟩
      funext i
      simp [g]
    · intro hx
      have : ∀ i, ∃ c : ℤ_[p], c * p = b.repr x i := fun i => by
        have h1 : b.repr x i ∈ RingHom.ker (PadicInt.toZMod (p := p)) := congrFun hx i
        rwa [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
          Ideal.mem_span_singleton'] at h1
      choose c hc using this
      refine ⟨b.equivFun.symm c, b.equivFun.injective (funext fun i => ?_)⟩
      rw [map_smul, LinearEquiv.apply_symm_apply]
      simp [← hc, mul_comm]
  rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv, hker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hg).toEquiv]
  simp [Nat.card_pi]
end GlobalTheory.TateFree
