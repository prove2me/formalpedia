-- Prove2me | solution 1 for OAI.AnalyticBridge.fixed_crt_choice_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:04:20.289362+00:00
-- url     : https://prove2.me/submissions/d61957f1-4f07-4666-82fc-106e558c4c40

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
section
namespace OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
namespace AnalyticBridge
variable {Ω : Type*}
private theorem CRTChoice.coordinates_injective :
    Function.Injective CRTChoice.coordinates := by
  intro x y h
  cases x
  cases y
  simp only [CRTChoice.coordinates, Prod.mk.injEq] at h ⊢
  simp_all
end AnalyticBridge
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace ExpBound
end ExpBound
namespace ShortDraftMellin
end ShortDraftMellin
end OAI
end

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open OAI.AnalyticBridge
variable {Ω : Type*}
namespace OAI.AnalyticBridge
theorem _root_.solution
    (Q : Finset CRTChoice) (F K b0 : ℕ)
    (hF : F ≠ 0) (hK : K ≠ 0) (hb0 : b0 ≠ 0)
    (hQ : ∀ q ∈ Q,
      q.J * q.C * q.e * q.v = F ∧
      q.J = q.s * q.J2 ∧
      q.b1 * q.b2 = b0 ^ 2 * q.J2 ^ 2 * q.s ∧
      q.A1 ∣ q.b1 * q.b2 ∧ q.A2 ∣ q.b1 * q.b2 ∧
      q.d ∣ F * b0 ∧ q.d * q.e * q.kpp = K) :
    Q.card ≤ F.divisors.card ^ 6 *
      (b0 ^ 2 * F ^ 3).divisors.card ^ 4 *
      (F * b0).divisors.card * K.divisors.card := by
  let DF := F.divisors
  let P := b0 ^ 2 * F ^ 3
  let DP := P.divisors
  let DFB := (F * b0).divisors
  let DK := K.divisors
  let T := (DF ×ˢ (DF ×ˢ (DF ×ˢ DF))) ×ˢ
      ((DF ×ˢ (DF ×ˢ (DP ×ˢ DP))) ×ˢ
      (DP ×ˢ (DP ×ˢ (DFB ×ˢ DK))))
  have hP : P ≠ 0 := by simp [P, hb0, hF]
  have hmap : Set.MapsTo CRTChoice.coordinates (Q : Set CRTChoice) (T : Set _) := by
    intro q hq
    obtain ⟨hlabel, hJ, hbprod, hA1, hA2, hd, hrow⟩ := hQ q hq
    have hJdvd : q.J ∣ F := by
      refine ⟨q.C * q.e * q.v, ?_⟩
      calc F = q.J * q.C * q.e * q.v := hlabel.symm
           _ = q.J * (q.C * q.e * q.v) := by ring
    have hsF : q.s ∣ F := by
      apply Nat.dvd_trans _ hJdvd
      refine ⟨q.J2, ?_⟩
      exact hJ
    have hJ2F : q.J2 ∣ F := by
      apply Nat.dvd_trans _ hJdvd
      refine ⟨q.s, ?_⟩
      simpa [mul_comm] using hJ
    have hcore : q.J2 ^ 2 * q.s ∣ F ^ 3 := by
      convert mul_dvd_mul (pow_dvd_pow_of_dvd hJ2F 2) hsF using 1 <;> first | rfl | ring
    have hbP : q.b1 * q.b2 ∣ P := by
      rw [hbprod]
      convert Nat.mul_dvd_mul_left (b0 ^ 2) hcore using 1 <;> first | rfl | ring
    have hb1P : q.b1 ∣ P := (Nat.dvd_mul_right q.b1 q.b2).trans hbP
    have hb2P : q.b2 ∣ P := (Nat.dvd_mul_left q.b2 q.b1).trans hbP
    have hkppK : q.kpp ∣ K := by
      refine ⟨q.d * q.e, ?_⟩
      calc K = q.d * q.e * q.kpp := hrow.symm
           _ = q.kpp * (q.d * q.e) := by ring
    have hC : q.C ∣ F := by
      refine ⟨q.J * q.e * q.v, ?_⟩
      calc F = q.J * q.C * q.e * q.v := hlabel.symm
           _ = q.C * (q.J * q.e * q.v) := by ring
    have he : q.e ∣ F := by
      refine ⟨q.J * q.C * q.v, ?_⟩
      calc F = q.J * q.C * q.e * q.v := hlabel.symm
           _ = q.e * (q.J * q.C * q.v) := by ring
    have hv : q.v ∣ F := by
      refine ⟨q.J * q.C * q.e, ?_⟩
      calc F = q.J * q.C * q.e * q.v := hlabel.symm
           _ = q.v * (q.J * q.C * q.e) := by ring
    change CRTChoice.coordinates q ∈ T
    simp only [CRTChoice.coordinates, T, Finset.mem_product]
    exact ⟨⟨Nat.mem_divisors.mpr ⟨hJdvd, hF⟩,
      Nat.mem_divisors.mpr ⟨hC, hF⟩,
      Nat.mem_divisors.mpr ⟨he, hF⟩,
      Nat.mem_divisors.mpr ⟨hv, hF⟩⟩,
      ⟨⟨Nat.mem_divisors.mpr ⟨hsF, hF⟩,
        Nat.mem_divisors.mpr ⟨hJ2F, hF⟩,
        Nat.mem_divisors.mpr ⟨hb1P, hP⟩,
        Nat.mem_divisors.mpr ⟨hb2P, hP⟩⟩,
       ⟨Nat.mem_divisors.mpr ⟨hA1.trans hbP, hP⟩,
        Nat.mem_divisors.mpr ⟨hA2.trans hbP, hP⟩,
        Nat.mem_divisors.mpr ⟨hd, mul_ne_zero hF hb0⟩,
        Nat.mem_divisors.mpr ⟨hkppK, hK⟩⟩⟩⟩
  have hcard := Finset.card_le_card_of_injOn CRTChoice.coordinates hmap
    CRTChoice.coordinates_injective.injOn
  convert hcard using 1
  simp [T, DF, DP, DFB, DK, P, Finset.card_product]
  ring
end OAI.AnalyticBridge
