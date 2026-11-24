-- Prove2me | solution 1 for GlobalTheory.LocalNorm.exists_sub_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:49:05.846631+00:00
-- url     : https://prove2.me/submissions/acdab546-f990-406b-a946-ab0c4643daa3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsBinaryEqAdicCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LocalNorm
namespace GlobalTheory.LocalNorm
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra.Unramified A B] (σ : B →ₐ[A] B) (hσ : ∃ b, σ b ≠ b) (P : Ideal B) (hP : P ≠ ⊤) :
    ∃ b, b - σ b ∉ P := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t, ht, ht1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := A) (S := B)).1
    inferInstance
  obtain ⟨b, hb⟩ := hσ
  set ψ := Algebra.TensorProduct.productMap (AlgHom.id A B) σ with hψ
  have h0 : ψ t = 0 := by
    have := congrArg ψ (ht b)
    simp only [map_mul, map_sub, map_zero, hψ, Algebra.TensorProduct.productMap_apply_tmul,
      AlgHom.id_apply, map_one, one_mul, mul_one] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hb)
  have h1 : ∀ z, Algebra.TensorProduct.lmul' A z - ψ z ∈ P := by
    intro z
    induction z with
    | zero => simp
    | tmul x y =>
      simp only [hψ, Algebra.TensorProduct.productMap_apply_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.lmul'_apply_tmul, ← mul_sub]
      exact P.mul_mem_left _ (hcon y)
    | add x y hx hy =>
      have := P.add_mem hx hy
      rw [map_add, map_add]
      convert this using 1
      ring
  have := h1 t
  rw [ht1, h0, sub_zero] at this
  exact hP ((Ideal.eq_top_iff_one P).2 this)
end GlobalTheory.LocalNorm
