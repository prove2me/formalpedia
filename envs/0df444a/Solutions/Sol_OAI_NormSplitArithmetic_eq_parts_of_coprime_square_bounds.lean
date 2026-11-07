-- Prove2me | solution 1 for OAI.NormSplitArithmetic.eq_parts_of_coprime_square_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:13:10.064622+00:00
-- url     : https://prove2.me/submissions/232e9682-3bab-4bbc-abc6-57e6a5dc940b

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.NormSplitArithmetic
namespace OAI.NormSplitArithmetic
theorem _root_.solution {a b m n : ℕ}
    (hcop : m.Coprime n) (ha2 : a ∣ m ^ 2) (hb2 : b ∣ n ^ 2)
    (hprod : a * b = m * n) : a = m ∧ b = n := by
  have hm2n : (m ^ 2).Coprime n :=
    (Nat.coprime_pow_left_iff (by decide) m n).mpr hcop
  have hmn2 : m.Coprime (n ^ 2) :=
    (Nat.coprime_pow_right_iff (by decide) m n).mpr hcop
  have han : a.Coprime n := hm2n.coprime_dvd_left ha2
  have hmb : m.Coprime b := hmn2.coprime_dvd_right hb2
  have ha_mn : a ∣ m * n := ⟨b, hprod.symm⟩
  have hm_ab : m ∣ a * b := ⟨n, hprod⟩
  have hn_ab : n ∣ a * b := ⟨m, by rw [hprod, mul_comm]⟩
  have ha_m : a ∣ m := han.dvd_of_dvd_mul_right ha_mn
  have hm_a : m ∣ a := hmb.dvd_of_dvd_mul_right hm_ab
  have hb_n : b ∣ n := by
    have hbn : b.Coprime m := (hmn2.symm).coprime_dvd_left hb2
    have hb_mn : b ∣ n * m := ⟨a, by
      calc
        n * m = m * n := mul_comm n m
        _ = a * b := hprod.symm
        _ = b * a := mul_comm a b⟩
    exact hbn.dvd_of_dvd_mul_right hb_mn
  have hn_b : n ∣ b := han.symm.dvd_of_dvd_mul_left hn_ab
  exact ⟨Nat.dvd_antisymm ha_m hm_a, Nat.dvd_antisymm hb_n hn_b⟩
end OAI.NormSplitArithmetic
