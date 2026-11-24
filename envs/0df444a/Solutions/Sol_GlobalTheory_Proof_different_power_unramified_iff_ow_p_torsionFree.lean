-- Prove2me | solution 1 for GlobalTheory.Proof.different_power_unramified_iff.ow_p_torsionFree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:28:10.825316+00:00
-- url     : https://prove2.me/submissions/8c4bae63-326a-4c48-be43-4514e27f3f2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SplitUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DifferentPowerUnramifiedIff
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
namespace GlobalTheory.Proof.different_power_unramified_iff
open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
private lemma eq_zero_of_natCast_mul_eq_zero_op (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    [IsDomain R] [CharZero R] [Module.Finite ℤ R] (z : Op p R) (hz : (p : Op p R) * z = 0) :
    z = 0 := by
  have hp := (Fact.out : p.Prime)
  have : Module.Free ℤ R := Module.free_of_finite_type_torsion_free'
  have hsmul : (p : ℤ_[p]) • z = 0 := by
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    exact hz
  rcases smul_eq_zero.mp hsmul with h | h
  · exact absurd h (Nat.cast_ne_zero.mpr hp.ne_zero)
  · exact h
end GlobalTheory.Proof.different_power_unramified_iff
end
end

set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.different_power_unramified_iff
open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
namespace GlobalTheory.Proof.different_power_unramified_iff
theorem _root_.solution (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [Module.Finite ℤ R] (w : Place p R) (x : w.Ow) (hx : (p : w.Ow) * x = 0) : x = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hy : (p : Op p R) * y ∈ Ideal.span {1 - w.e} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_natCast]
    exact hx
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hy
  have hey : w.e * y = 0 := by
    apply eq_zero_of_natCast_mul_eq_zero_op p R
    have hee : w.e * w.e = w.e := w.idem
    calc (p : Op p R) * (w.e * y) = w.e * ((p : Op p R) * y) := by ring
      _ = w.e * (a * (1 - w.e)) := by rw [ha]
      _ = a * (w.e - w.e * w.e) := by ring
      _ = 0 := by rw [hee, sub_self, mul_zero]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  exact ⟨y, by rw [mul_sub, mul_one, mul_comm y, hey, sub_zero]⟩
end GlobalTheory.Proof.different_power_unramified_iff
