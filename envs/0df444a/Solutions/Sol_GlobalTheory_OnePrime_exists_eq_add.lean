-- Prove2me | solution 1 for GlobalTheory.OnePrime.exists_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:16:10.633464+00:00
-- url     : https://prove2.me/submissions/db43c136-1b59-45aa-b3e2-b247f60d569d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SplitUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueMaximalAbovePlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped TensorProduct
namespace GlobalTheory.OnePrime
open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]
private theorem exists_eq_one_tmul_add_mul (x : Op p R) :
    ∃ (r : R) (t : Op p R), x = (1 : ℤ_[p]) ⊗ₜ r + (p : Op p R) * t := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul z r =>
    obtain ⟨n, -, hn⟩ := PadicInt.exists_mem_range (x := z)
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hn
    obtain ⟨t, ht⟩ := hn
    refine ⟨(n : R) * r, t ⊗ₜ r, ?_⟩
    have hz : z = (n : ℤ_[p]) + t * p := by rw [ht]; ring
    have h1 : (n : ℤ_[p]) ⊗ₜ[ℤ] r = (1 : ℤ_[p]) ⊗ₜ ((n : R) * r) := by
      calc (n : ℤ_[p]) ⊗ₜ[ℤ] r = ((n : ℤ_[p]) ⊗ₜ[ℤ] (1 : R)) * ((1 : ℤ_[p]) ⊗ₜ r) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        _ = (n : Op p R) * ((1 : ℤ_[p]) ⊗ₜ r) := by rw [Algebra.TensorProduct.natCast_def]
        _ = ((1 : ℤ_[p]) ⊗ₜ[ℤ] (n : R)) * ((1 : ℤ_[p]) ⊗ₜ r) := by
            rw [Algebra.TensorProduct.natCast_def']
        _ = (1 : ℤ_[p]) ⊗ₜ ((n : R) * r) := by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have h2 : (t * p) ⊗ₜ[ℤ] r = (p : Op p R) * (t ⊗ₜ r) := by
      rw [Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]
    rw [hz, TensorProduct.add_tmul, h1, h2]
  | add x y hx hy =>
    obtain ⟨r₁, t₁, h₁⟩ := hx
    obtain ⟨r₂, t₂, h₂⟩ := hy
    exact ⟨r₁ + r₂, t₁ + t₂, by rw [h₁, h₂, TensorProduct.tmul_add]; ring⟩
end GlobalTheory.OnePrime
end
end

set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory GlobalTheory.OnePrime
open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]
namespace GlobalTheory.OnePrime
theorem _root_.solution (w : Place p R) (s : w.Ow) :
    ∃ (r : R) (t : w.Ow), s = w.toOw r + (p : w.Ow) * t := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨r, t, h⟩ := exists_eq_one_tmul_add_mul x
  refine ⟨r, Ideal.Quotient.mk _ t, ?_⟩
  rw [h, map_add, map_mul, map_natCast]
  rfl
end GlobalTheory.OnePrime
