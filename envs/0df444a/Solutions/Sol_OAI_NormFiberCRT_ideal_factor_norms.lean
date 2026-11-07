-- Prove2me | solution 1 for OAI.NormFiberCRT.ideal_factor_norms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:14:27.568659+00:00
-- url     : https://prove2.me/submissions/b5e8d636-6c65-40ab-ad55-26562cedf57d

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Theorems.Thm_OAI_NormSplitArithmetic_eq_parts_of_coprime_square_bounds
import Theorems.Thm_OAI_NormFiberCRT_ideal_eq_factors
section
namespace OAI
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
namespace ShortDraftHeckeBridge
end ShortDraftHeckeBridge
namespace NormSplitArithmetic
end NormSplitArithmetic
namespace NormFiberCRT
private theorem ring_rank_two : Module.finrank ℤ O = 2 := by
  rw [NumberField.RingOfIntegers.rank K,
    IsCyclotomicExtension.Rat.finrank 3 K]
  decide
end NormFiberCRT
namespace NormFiberMult
end NormFiberMult
namespace ShortDraftHeckeBridge
end ShortDraftHeckeBridge
open Filter Asymptotics
namespace ShortDraftHeckeBridge
end ShortDraftHeckeBridge
end
end OAI
end

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
open OAI.NormFiberCRT
namespace OAI.NormFiberCRT
theorem _root_.solution (I : Ideal O) (m n : ℕ)
    (hcop : m.Coprime n) (hI : Ideal.absNorm I = m * n) :
    Ideal.absNorm (I ⊔ Ideal.span {(m : O)}) = m ∧
      Ideal.absNorm (I ⊔ Ideal.span {(n : O)}) = n := by
  have hAm : Ideal.absNorm (Ideal.span {(m : O)}) = m ^ 2 := by
    rw [Ideal.absNorm_span_natCast, ring_rank_two]
  have hBn : Ideal.absNorm (Ideal.span {(n : O)}) = n ^ 2 := by
    rw [Ideal.absNorm_span_natCast, ring_rank_two]
  have hmdiv : Ideal.absNorm (I ⊔ Ideal.span {(m : O)}) ∣ m ^ 2 := by
    rw [← hAm]
    exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
  have hndiv : Ideal.absNorm (I ⊔ Ideal.span {(n : O)}) ∣ n ^ 2 := by
    rw [← hBn]
    exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
  have hprod := congrArg Ideal.absNorm (ideal_eq_factors I m n hcop hI)
  rw [map_mul, hI] at hprod
  exact NormSplitArithmetic.eq_parts_of_coprime_square_bounds hcop hmdiv hndiv hprod.symm
end OAI.NormFiberCRT
