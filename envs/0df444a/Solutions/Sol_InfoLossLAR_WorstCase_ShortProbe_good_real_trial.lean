-- Prove2me | solution 1 for InfoLossLAR.WorstCase.ShortProbe.good_real_trial
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T04:42:39.593285+00:00
-- url     : https://prove2.me/submissions/12410960-929c-4233-8637-a28d3380ff32

import Theorems.Thm_RegevLWE_GaussConv_smoothing_remark
import Theorems.Thm_RegevLWE_GaussConv_claim_3_8
import Definitions.Def_InfoLossLAR_BDD_Coordinates
import Definitions.Def_InfoLossLAR_LoadedBatchBundle_05
import Definitions.Def_InfoLossLAR_RegevSearch
import Definitions.Def_InfoLossLAR_WorstCase_Encoding
import Definitions.Def_InfoLossLAR_WorstCase_Family
import Definitions.Def_InfoLossLAR_WorstCase_FixedT
import Definitions.Def_InfoLossLAR_WorstCase_LatticeProblems
import Definitions.Def_InfoLossLAR_WorstCase_Laws
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_ShorAlgorithms_QFT_Circuit
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.LDL
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Vector.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Order.Hom.Set
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Tactic

set_option linter.all false

namespace AFT
end AFT

namespace AFT.BetaReference
end AFT.BetaReference

namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic

namespace AFT.BinaryArithmetic.RationalBits
end AFT.BinaryArithmetic.RationalBits

namespace AFT.FiniteConvolutionProgram
end AFT.FiniteConvolutionProgram

namespace AFT.GaussianSource
end AFT.GaussianSource

namespace AFT.RationalNumerics
end AFT.RationalNumerics

namespace CurrentAFT
end CurrentAFT

namespace InfoLossLAR.WorstCase
end InfoLossLAR.WorstCase

namespace InfoLossLAR.WorstCase.GaussianLatticeTransport
end InfoLossLAR.WorstCase.GaussianLatticeTransport

namespace InfoLossLAR.WorstCase.GaussianProjection
end InfoLossLAR.WorstCase.GaussianProjection

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry
end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding
end InfoLossLAR.WorstCase.GaussianRandomizedRounding

namespace InfoLossLAR.WorstCase.IntegerBasis
end InfoLossLAR.WorstCase.IntegerBasis

namespace InfoLossLAR.WorstCase.RationalGramSchmidt
end InfoLossLAR.WorstCase.RationalGramSchmidt

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native
end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

namespace InfoLossLAR.WorstCase.RationalInverse
end InfoLossLAR.WorstCase.RationalInverse

namespace InfoLossLAR.WorstCase.RegevSketch
end InfoLossLAR.WorstCase.RegevSketch

namespace Integration9_9
end Integration9_9

namespace Integration9_9.LARPlatformEncoding
end Integration9_9.LARPlatformEncoding

namespace Integration9_9.TM2NativeFiniteDraw
end Integration9_9.TM2NativeFiniteDraw

namespace Integration9_9.TM2NativeFiniteSeries
end Integration9_9.TM2NativeFiniteSeries

namespace Integration9_9.TM2NativeGaussian
end Integration9_9.TM2NativeGaussian

namespace Integration9_9.TM2NativeRootGroupProfiles
end Integration9_9.TM2NativeRootGroupProfiles

namespace OAI.MetricKMedian.Binary
end OAI.MetricKMedian.Binary

namespace OAI.MetricKMedian.Binary.Automatic
end OAI.MetricKMedian.Binary.Automatic

/- Helper module AFT.RationalHeight. -/
section P2MDyadicModule0

namespace AFT.RationalNumerics

open scoped BigOperators

namespace HeightBound

theorem mono {value : ℚ} {first second : ℕ} (h : HeightBound value first) (hle : first ≤ second) :
    HeightBound value second := by
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hle
  exact ⟨h.1.trans hp,h.2.trans hp⟩

private theorem reduced_le (num : ℤ) (den : ℕ) (hd : 0 < den) :
    (Rat.divInt num (den : ℤ)).num.natAbs ≤ num.natAbs ∧ (Rat.divInt num (den : ℤ)).den ≤ den := by
  constructor
  · by_cases hn : num=0
    · simp [hn]
    · exact Nat.le_of_dvd (Int.natAbs_pos.mpr hn)
        (Int.natAbs_dvd_natAbs.mpr (Rat.num_dvd num (by exact_mod_cast hd.ne')))
  · exact Nat.le_of_dvd hd (by exact_mod_cast Rat.den_dvd num (den : ℤ))

theorem zero : HeightBound 0 0 := by norm_num [HeightBound]

theorem of_int {value : ℤ} {bits : ℕ} (h : value.natAbs ≤ 2^bits) : HeightBound (value : ℚ) bits := by
  constructor
  · simpa using h
  · simpa using (Nat.one_le_pow bits 2 (by decide))

theorem mul {first second : ℚ} {firstBits secondBits : ℕ}
    (hf : HeightBound first firstBits) (hs : HeightBound second secondBits) :
    HeightBound (first*second) (firstBits+secondBits) := by
  have heq : first*second=Rat.divInt (first.num*second.num) (first.den*second.den : ℤ) := by
    calc
      _ = Rat.divInt first.num first.den * Rat.divInt second.num second.den := by rw [Rat.num_divInt_den,Rat.num_divInt_den]
      _ = _ := Rat.divInt_mul_divInt _ _
  have hr := reduced_le (first.num*second.num) (first.den*second.den)
    (Nat.mul_pos first.den_pos second.den_pos)
  rw [Nat.cast_mul,← heq] at hr
  simp only [Int.natAbs_mul] at hr
  rw [HeightBound,pow_add]
  exact ⟨hr.1.trans (Nat.mul_le_mul hf.1 hs.1),hr.2.trans (Nat.mul_le_mul hf.2 hs.2)⟩

theorem inv {value : ℚ} {bits : ℕ} (h : HeightBound value bits) : HeightBound value⁻¹ bits := by
  by_cases hz : value=0
  · subst value
    norm_num [HeightBound]
    exact Nat.one_le_pow bits 2 (by decide)
  constructor
  · simp only [Rat.num_inv,Int.natAbs_mul,Int.natAbs_natCast]
    have hsign : value.num.sign.natAbs=1 := by
      rcases lt_or_gt_of_ne (Rat.num_ne_zero.mpr hz) with hn|hn
      · simp [Int.sign_eq_neg_one_of_neg hn]
      · simp [Int.sign_eq_one_of_pos hn]
    simpa only [hsign,one_mul,mul_one] using h.2
  · simpa only [Rat.den_inv_of_ne_zero hz] using h.1

theorem div {first second : ℚ} {firstBits secondBits : ℕ}
    (hf : HeightBound first firstBits) (hs : HeightBound second secondBits) :
    HeightBound (first/second) (firstBits+secondBits) := by
  simpa only [div_eq_mul_inv] using hf.mul hs.inv

end HeightBound

end AFT.RationalNumerics

end P2MDyadicModule0

/- Helper module AFT.BinaryRationalLiterals. -/
section P2MDyadicModule1

namespace AFT.BinaryArithmetic

theorem bits_value (n : ℕ) : value n.bits=n := by
  induction n using Nat.binaryRec with
  | zero => simp [value]
  | bit b n ih =>
    by_cases hn : n=0
    · subst n
      cases b <;> simp [Nat.bit_val,value]
    · rw [Nat.bits_append_bit n b (fun hh => False.elim (hn hh))]
      simp only [value,ih,Nat.bit_val]
      omega

namespace RationalBits

/-- Existence of a finite literal encoding, used when constructing a fixed
program. The result is stored data, not an invocation of a real oracle. -/
theorem exists_code (q : ℚ) : ∃ code : RationalBits,code.decode=q := by
  let negative := decide (q.num < 0)
  have hsign : signedValue negative q.num.natAbs.bits=q.num := by
    simp only [signedValue,bits_value,negative]
    by_cases hn : q.num < 0
    · simp [hn,abs_of_neg hn]
    · simp [hn,abs_of_nonneg (by omega : 0 ≤ q.num)]
  let code : RationalBits :=
    ⟨negative,q.num.natAbs.bits,q.den.bits,
      by rw [bits_value,Nat.size_eq_bits_len],
      by rw [bits_value,Nat.size_eq_bits_len],
      by simpa only [bits_value] using q.den_pos,
      by simpa only [bits_value] using q.reduced⟩
  refine ⟨code,?_⟩
  rw [decode_fraction]
  change (signedValue negative q.num.natAbs.bits : ℚ)/(value q.den.bits : ℚ)=q
  rw [hsign,bits_value,Rat.num_div_den]

end RationalBits

end AFT.BinaryArithmetic

end P2MDyadicModule1

/- Helper module AFT.RationalPiProgram. -/
section P2MDyadicModule2

namespace AFT.RationalNumerics

open scoped BigOperators

noncomputable section

open scoped Classical

theorem arctan_term_bound (value : ℝ) (hv : 0 ≤ value) (hv' : value ≤ 1/2) (index : ℕ) :
    |(-1 : ℝ)^index*value^(2*index+1)/(2*index+1 : ℕ)| ≤ (1/2 : ℝ)^(index+1) := by
  rw [abs_div,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    abs_of_nonneg (pow_nonneg hv _),abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ value^(2*index+1) := div_le_self (pow_nonneg hv _) (by exact_mod_cast (show 1≤2*index+1 by omega))
    _ ≤ (1/2 : ℝ)^(2*index+1) := pow_le_pow_left₀ hv hv' _
    _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

/-- On the two actual rational inputs, absolute geometric majorization
bounds the entire remaining series, including its alternating signs. -/
theorem arctanSum_error (value : ℚ) (hv : 0 ≤ value) (hv' : value ≤ 1/2) (terms : ℕ) :
    |(arctanSum value terms : ℝ)-Real.arctan value| ≤ (1/2 : ℝ)^terms := by
  have hv0 : (0 : ℝ) ≤ value := by exact_mod_cast hv
  have hv1 : (value : ℝ) ≤ 1/2 := by
    have hh : value*2 ≤ 1 := (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).mp hv'
    have hh' : (value : ℝ)*2 ≤ 1 := by exact_mod_cast hh
    linarith
  let term := fun index : ℕ => (-1 : ℝ)^index*(value : ℝ)^(2*index+1)/(2*index+1 : ℕ)
  have hseries : HasSum term (Real.arctan value) := Real.hasSum_arctan (by
    rw [Real.norm_eq_abs,abs_of_nonneg hv0]
    linarith)
  have hsplit := hseries.summable.sum_add_tsum_nat_add terms
  rw [hseries.tsum_eq] at hsplit
  have hcast : (arctanSum value terms : ℝ)=∑ i∈Finset.range terms,term i := by
    unfold arctanSum term
    push_cast
    rfl
  have hgeom : Summable (fun i : ℕ => (1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i) :=
    (summable_geometric_of_norm_lt_one (show ‖(1/2 : ℝ)‖<1 by norm_num)).mul_left _
  have hbound (i : ℕ) : ‖term (i+terms)‖ ≤ (1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i := by
    have hh := arctan_term_bound (value : ℝ) hv0 hv1 (i+terms)
    rw [← pow_add]
    have hi : i+terms+1=terms+1+i := by omega
    simpa only [term,Real.norm_eq_abs,hi] using hh
  have htail := (summable_nat_add_iff terms).mpr hseries.summable
  have hnorm := htail.norm
  have hsum := (norm_tsum_le_tsum_norm hnorm).trans (Summable.tsum_le_tsum hbound hnorm hgeom)
  have hgeomval : (∑' i : ℕ,(1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i)=(1/2 : ℝ)^terms := by
    have hh := ((hasSum_geometric_of_norm_lt_one (show ‖(1/2 : ℝ)‖<1 by norm_num)).mul_left
      ((1/2 : ℝ)^(terms+1))).tsum_eq
    calc
      _ = (1/2 : ℝ)^(terms+1)*2 := by
        simpa only [show ((1 : ℝ)-1/2)⁻¹=2 by norm_num] using hh
      _ = _ := by rw [pow_succ]; ring
  rw [hgeomval,Real.norm_eq_abs] at hsum
  rw [hcast,abs_sub_comm,show Real.arctan (value : ℝ)-(∑ i∈Finset.range terms,term i)=
    ∑' i,term (i+terms) by linarith]
  exact hsum

/-- `bits+3` terms of each short series give the requested binary accuracy. -/
theorem piApprox_error (bits : ℕ) : |(piApprox bits : ℝ)-Real.pi| ≤ 1/(2 : ℝ)^bits := by
  have h1 := arctanSum_error (1/2) (by norm_num) (by norm_num) (bits+3)
  have h2 := arctanSum_error (1/3) (by norm_num) (by norm_num) (bits+3)
  have hid : Real.pi=4*(Real.arctan (1/2)+Real.arctan (1/3)) := by
    have hh := Real.arctan_inv_2_add_arctan_inv_3
    norm_num only [one_div] at ⊢
    linarith
  have he : (piApprox bits : ℝ)-Real.pi=4*((arctanSum (1/2) (bits+3) : ℝ)-Real.arctan (1/2)+
      ((arctanSum (1/3) (bits+3) : ℝ)-Real.arctan (1/3))) := by
    rw [hid]
    simp only [piApprox,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_add]
    ring
  rw [he,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  calc
    _ ≤ 4*(|(arctanSum (1/2) (bits+3) : ℝ)-Real.arctan (1/2)|+
        |(arctanSum (1/3) (bits+3) : ℝ)-Real.arctan (1/3)|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ 4*((1/2 : ℝ)^(bits+3)+(1/2 : ℝ)^(bits+3)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using add_le_add h1 h2
    _ = _ := by rw [pow_add,div_pow,one_pow]; norm_num; ring

end

end AFT.RationalNumerics

end P2MDyadicModule2

/- Helper module AFT.RationalExpProgram. -/
section P2MDyadicModule3

namespace AFT.RationalNumerics

open scoped BigOperators

noncomputable section

open scoped Classical

theorem expSum_error (value : ℚ) (hv : 0 ≤ value) (hv' : value ≤ 1/2)
    (terms : ℕ) (ht : 0 < terms) :
    |(expSum value terms : ℝ)-Real.exp value| ≤ 2*(1/2 : ℝ)^terms := by
  have hv0 : (0 : ℝ) ≤ value := by exact_mod_cast hv
  have hv1 : (value : ℝ) ≤ 1/2 := by
    have hh : value*2 ≤ 1 := (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).mp hv'
    have hh' : (value : ℝ)*2 ≤ 1 := by exact_mod_cast hh
    linarith
  have hterm : (1 : ℝ) ≤ terms := by exact_mod_cast ht
  have hfactorial : (1 : ℝ) ≤ terms.factorial := by exact_mod_cast Nat.factorial_pos terms
  have hden : (0 : ℝ) < (terms.factorial : ℝ)*terms := by positivity
  have hquot : ((terms+1 : ℕ) : ℝ)/((terms.factorial : ℝ)*terms) ≤ 2 := by
    apply (div_le_iff₀ hden).mpr
    push_cast
    nlinarith
  have hh := Real.exp_bound (x := (value : ℝ)) (by rw [abs_of_nonneg hv0]; linarith) ht
  have he : (expSum value terms : ℝ)=∑ i∈Finset.range terms,(value : ℝ)^i/(i.factorial : ℕ) := by
    unfold expSum
    push_cast
    rfl
  rw [he,abs_sub_comm]
  apply hh.trans
  rw [abs_of_nonneg hv0]
  exact (mul_le_mul (pow_le_pow_left₀ hv0 hv1 terms) hquot (by positivity) (by positivity)).trans_eq (mul_comm _ _)

/-- Taking reciprocals of quantities at least one has Lipschitz constant
one; it avoids amplification by an exponentially large positive exponential. -/
theorem inv_error_of_ge_one (first second : ℝ) (hf : 1 ≤ first) (hs : 1 ≤ second) :
    |first⁻¹-second⁻¹| ≤ |first-second| := by
  have hfirst : first ≠ 0 := by linarith
  have hsecond : second ≠ 0 := by linarith
  have he : first⁻¹-second⁻¹=(second-first)/(first*second) := by field_simp
  rw [he,abs_div,abs_sub_comm,abs_of_nonneg (by positivity : 0 ≤ first*second)]
  exact div_le_self (abs_nonneg _) (by nlinarith)

theorem power_error_unit_interval (first second : ℝ)
    (hf : 0 ≤ first ∧ first ≤ 1) (hs : 0 ≤ second ∧ second ≤ 1) (count : ℕ) :
    |first^count-second^count| ≤ (count : ℝ)*|first-second| := by
  have hh := abs_pow_sub_pow_le first second count
  rw [abs_of_nonneg hf.1,abs_of_nonneg hs.1] at hh
  have hp : max first second^(count-1) ≤ 1 := pow_le_one₀ (le_max_of_le_left hf.1) (max_le hf.2 hs.2)
  calc
    _ ≤ |first-second| *count*max first second^(count-1) := hh
    _ ≤ |first-second| *count*1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

/-- A polynomial range reduction parameter is sufficient for any requested
number of binary digits. The approximation remains positive and bounded. -/
theorem expNegScaled_error (argument : ℚ) (scale bits : ℕ)
    (ha : 0 ≤ argument) (hscale : 0 < scale) (hbound : 2*argument ≤ (scale : ℚ)) :
    |(expNegScaled argument scale bits : ℝ)-Real.exp (-(argument : ℝ))| ≤ 1/(2 : ℝ)^bits := by
  let value : ℚ := argument/(scale : ℚ)
  let terms := bits+scale+1
  have hs0 : (0 : ℚ) < scale := by exact_mod_cast hscale
  have hv0 : 0 ≤ value := div_nonneg ha hs0.le
  have hv1 : value ≤ 1/2 := by
    apply (div_le_iff₀ hs0).mpr
    linarith
  have ht : 0 < terms := by dsimp [terms]; omega
  have hfirst := expSum_ge_one value hv0 terms ht
  have hsecond : (1 : ℝ) ≤ Real.exp (value : ℝ) := Real.one_le_exp_iff.mpr (by exact_mod_cast hv0)
  have hpi := power_error_unit_interval ((expSum value terms : ℝ)⁻¹) ((Real.exp (value : ℝ))⁻¹)
    ⟨by positivity,inv_le_one_of_one_le₀ hfirst⟩ ⟨by positivity,inv_le_one_of_one_le₀ hsecond⟩ scale
  have hi := inv_error_of_ge_one (expSum value terms) (Real.exp (value : ℝ)) hfirst hsecond
  have happrox := (hpi.trans (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg scale))).trans
    (mul_le_mul_of_nonneg_left (expSum_error value hv0 hv1 terms ht) (Nat.cast_nonneg scale))
  have hexp : (Real.exp (value : ℝ))⁻¹^scale=Real.exp (-(argument : ℝ)) := by
    rw [← Real.exp_neg,← Real.exp_nat_mul]
    congr 1
    dsimp [value]
    push_cast
    field_simp
  have hprogram : (expNegScaled argument scale bits : ℝ)=(expSum value terms : ℝ)⁻¹^scale := by
    simp only [expNegScaled,value,terms,Rat.cast_pow,Rat.cast_inv]
  rw [hprogram,← hexp]
  apply happrox.trans
  have hsbound : (scale : ℝ) ≤ (2 : ℝ)^scale := by exact_mod_cast (Nat.lt_two_pow_self (n:=scale)).le
  calc
    _ ≤ (2 : ℝ)^scale*(2*(1/2 : ℝ)^terms) := mul_le_mul_of_nonneg_right hsbound (by positivity)
    _ = _ := by
      dsimp [terms]
      rw [pow_add,pow_add,div_pow,one_pow,div_pow,one_pow]
      field_simp

theorem expNegApprox_error (argument : ℚ) (bits : ℕ) :
    |(expNegApprox argument bits : ℝ)-Real.exp (-max (argument : ℝ) 0)| ≤ 1/(2 : ℝ)^bits := by
  have hb : 2*max argument 0 ≤ (expScale argument : ℚ) := by
    have hh := Nat.le_ceil (max argument 0)
    simp only [expScale,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    linarith
  have hh := expNegScaled_error (max argument 0) (expScale argument) bits
    (le_max_right _ _) (expScale_positive argument) hb
  simpa only [expNegApprox,Rat.cast_max,Rat.cast_zero] using hh

/-- On nonnegative arguments the negative exponential is globally
one-Lipschitz. This controls the separate rational argument approximation. -/
theorem exp_neg_lipschitz (first second : ℝ) (hf : 0 ≤ first) (hs : 0 ≤ second) :
    |Real.exp (-first)-Real.exp (-second)| ≤ |first-second| := by
  have ordered (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      Real.exp (-a)-Real.exp (-b) ≤ b-a := by
    have he := Real.add_one_le_exp (a-b)
    have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (-a)).le
    have heq : Real.exp (-a)*Real.exp (a-b)=Real.exp (-b) := by rw [← Real.exp_add]; congr 1; ring
    rw [heq] at hm
    have hl : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hh := mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr hab)
    nlinarith
  rcases le_total first second with h|h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))),
      abs_of_nonpos (sub_nonpos.mpr h)]
    have hh := ordered first second hf h
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr (by linarith))),
      abs_of_nonneg (sub_nonneg.mpr h)]
    have hh := ordered second first hs h
    linarith

end

end AFT.RationalNumerics

end P2MDyadicModule3

/- Helper module AFT.RationalGaussianProgram. -/
section P2MDyadicModule4

namespace AFT.RationalNumerics

noncomputable section

/-- The finite pi and exponential programs together approximate the actual
Gaussian exponential; all precision guard digits are computed rationally. -/
theorem gaussianApprox_error (squaredWidth : ℚ) (point : ℤ) (bits : ℕ)
    (hwidth : 0 < squaredWidth) :
    |(gaussianApprox squaredWidth point bits : ℝ)-
      Real.exp (-Real.pi*(point : ℝ)^2/(squaredWidth : ℝ))| ≤ 1/(2 : ℝ)^bits := by
  let ratio := gaussianRatio squaredWidth point
  let guard := gaussianGuard squaredWidth point
  let argument := piApprox (bits+guard+1)*ratio
  have hr0 : (0 : ℚ) ≤ ratio := div_nonneg (sq_nonneg _) hwidth.le
  have hr : (0 : ℝ) ≤ ratio := by exact_mod_cast hr0
  have hguard : (ratio : ℝ) ≤ (guard : ℝ) := by exact_mod_cast Nat.le_ceil ratio
  have hguardpow : (guard : ℝ) ≤ (2 : ℝ)^guard := by exact_mod_cast (Nat.lt_two_pow_self (n:=guard)).le
  have hpi := piApprox_error (bits+guard+1)
  have harg : |(argument : ℝ)-Real.pi*(ratio : ℝ)| ≤ 1/(2 : ℝ)^(bits+1) := by
    have he : (argument : ℝ)-Real.pi*(ratio : ℝ)=((piApprox (bits+guard+1) : ℝ)-Real.pi)*(ratio : ℝ) := by
      dsimp [argument]
      push_cast
      ring
    rw [he,abs_mul,abs_of_nonneg hr]
    calc
      _ ≤ (1/(2 : ℝ)^(bits+guard+1))*(2 : ℝ)^guard :=
        mul_le_mul hpi (hguard.trans hguardpow) hr (by positivity)
      _ = _ := by rw [pow_add,pow_add,pow_add]; field_simp
  have ht : 0 ≤ Real.pi*(ratio : ℝ) := mul_nonneg Real.pi_pos.le hr
  have hclip : |max (argument : ℝ) 0-Real.pi*(ratio : ℝ)| ≤ 1/(2 : ℝ)^(bits+1) := by
    have hh := abs_max_sub_max_le_abs (argument : ℝ) (Real.pi*(ratio : ℝ)) 0
    rw [max_eq_left ht] at hh
    exact hh.trans harg
  have he := expNegApprox_error argument (bits+1)
  have hl := exp_neg_lipschitz (max (argument : ℝ) 0) (Real.pi*(ratio : ℝ)) (le_max_right _ _) ht
  have htarget : -Real.pi*(point : ℝ)^2/(squaredWidth : ℝ) = -(Real.pi*(ratio : ℝ)) := by
    dsimp [ratio,gaussianRatio]
    push_cast
    ring
  rw [htarget]
  calc
    _ ≤ |(expNegApprox argument (bits+1) : ℝ)-Real.exp (-max (argument : ℝ) 0)|+
        |Real.exp (-max (argument : ℝ) 0)-Real.exp (-(Real.pi*(ratio : ℝ)))| := abs_sub_le _ _ _
    _ ≤ 1/(2 : ℝ)^(bits+1)+1/(2 : ℝ)^(bits+1) := add_le_add he (hl.trans hclip)
    _ = _ := by rw [pow_succ]; field_simp; norm_num

end

end AFT.RationalNumerics

end P2MDyadicModule4

/- Helper module AFT.GaussianTail. -/
section P2MDyadicModule5

namespace AFT.GaussianSource

open scoped BigOperators Classical

theorem realNormalizer_eq_toReal (width : ℝ) :
    realNormalizer width = (normalizer width).toReal := by
  rw [normalizer, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  simp [realNormalizer, ENNReal.toReal_ofReal, (weight_pos width _).le]

set_option backward.isDefEq.respectTransparency false in
theorem integerGaussian_toReal (width : ℝ) (hw : 0 < width) (z : ℤ) :
    (integerGaussian width hw z).toReal = weight width z / realNormalizer width := by
  rw [integerGaussian, PMF.normalize_apply, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (weight_pos width z).le]
  change weight width z * (normalizer width).toReal⁻¹ = _
  rw [← realNormalizer_eq_toReal]
  rfl

end AFT.GaussianSource

end P2MDyadicModule5

/- Helper module AFT.GaussianConvolution. -/
section P2MDyadicModule6

namespace AFT.GaussianSource

open scoped BigOperators Classical

noncomputable def shiftedWeight (width center : ℝ) (z : ℤ) : ℝ :=
  Real.exp (-(Real.pi / width ^ 2) * ((z : ℝ) - center) ^ 2)

noncomputable def theta (width center : ℝ) : ℝ :=
  ∑' z : ℤ, shiftedWeight width center z

noncomputable def thetaFourier (width center : ℝ) (z : ℤ) : ℂ :=
  Complex.exp (-Real.pi * (width : ℂ) ^ 2 * (z : ℂ) ^ 2 +
    2 * Real.pi * Complex.I * center * z)

/-- Poisson summation for an arbitrarily shifted integer lattice. -/
theorem theta_poisson (width center : ℝ) (hw : 0 < width) :
    (theta width center : ℂ) / width = ∑' z : ℤ, thetaFourier width center z := by
  have hs : ((width : ℂ) ^ 2) ^ (1 / 2 : ℂ) = width := by
    have hr : (width ^ 2) ^ (1 / 2 : ℝ) = width := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hw.le]
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
    rw [Complex.ofReal_cpow (sq_nonneg width)] at hc
    simpa using hc
  have hp := Complex.tsum_exp_neg_quadratic
    (a := (width : ℂ) ^ 2) (by simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using sq_pos_of_pos hw)
    (Complex.I * center)
  rw [hs] at hp
  have hleft : (∑' z : ℤ, Complex.exp (-Real.pi * (width : ℂ) ^ 2 * z ^ 2 +
      2 * Real.pi * (Complex.I * center) * z)) =
      ∑' z : ℤ, thetaFourier width center z := by
    apply tsum_congr
    intro z
    congr 1
    ring
  have hright : (∑' z : ℤ, Complex.exp
      (-Real.pi / (width : ℂ) ^ 2 * (z + Complex.I * (Complex.I * center)) ^ 2)) =
      (theta width center : ℂ) := by
    rw [theta, Complex.ofReal_tsum]
    apply tsum_congr
    intro z
    rw [shiftedWeight, Complex.ofReal_exp]
    congr 1
    push_cast
    have hI : Complex.I * (Complex.I * (center : ℂ)) = -(center : ℂ) := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    rw [hI]
    ring
  rw [hleft, hright] at hp
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hp.symm

theorem thetaFourier_norm (width center : ℝ) (hw : 0 < width) (z : ℤ) :
    ‖thetaFourier width center z‖ = weight (1 / width) z := by
  rw [thetaFourier, Complex.norm_exp]
  simp [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.neg_re ]
  unfold weight
  congr 1
  field_simp

theorem summable_thetaFourier (width center : ℝ) (hw : 0 < width) :
    Summable (thetaFourier width center) := by
  apply Summable.of_norm
  simpa only [thetaFourier_norm width center hw] using summable_weight (1 / width) (by positivity)

/-- The nonzero Fourier modes control the entire relative error, uniformly
in the center, by the zero-centered dual Gaussian mass. -/
theorem theta_relative_error (width center : ℝ) (hw : 0 < width) :
    |theta width center / width - 1| ≤ realNormalizer (1 / width) - 1 := by
  let f := thetaFourier width center
  have hf := summable_thetaFourier width center hw
  have hnorm : Summable (fun z : ℤ => ‖if z = 0 then (0 : ℂ) else f z‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
      (summable_weight (1 / width) (by positivity))
    intro z
    split_ifs
    · exact (show ‖(0 : ℂ)‖ = 0 by norm_num).symm ▸ (weight_pos (1 / width) z).le
    · exact le_of_eq (thetaFourier_norm width center hw z)
  have hzero : f 0 = 1 := by simp [f, thetaFourier]
  have heq := hf.tsum_eq_add_tsum_ite (0 : ℤ)
  change (∑' z : ℤ, f z) = f 0 + ∑' z : ℤ, if z = 0 then 0 else f z at heq
  rw [hzero] at heq
  have hdual := (summable_weight (1 / width) (by positivity)).tsum_eq_add_tsum_ite (0 : ℤ)
  change realNormalizer (1 / width) = weight (1 / width) 0 + _ at hdual
  have hwzero : weight (1 / width) 0 = 1 := by simp [weight]
  rw [hwzero] at hdual
  have hnormsum : (∑' z : ℤ, ‖if z = 0 then (0 : ℂ) else f z‖) =
      realNormalizer (1 / width) - 1 := by
    have heq' : (∑' z : ℤ, ‖if z = 0 then (0 : ℂ) else f z‖) =
        ∑' z : ℤ, if z = 0 then 0 else weight (1 / width) z := by
      apply tsum_congr
      intro z
      split_ifs
      · exact norm_zero
      · exact thetaFourier_norm width center hw z
    rw [heq']
    linarith
  have hcomplex : ((theta width center / width - 1 : ℝ) : ℂ) =
      ∑' z : ℤ, if z = 0 then 0 else f z := by
    push_cast
    rw [theta_poisson width center hw]
    change (∑' z : ℤ, f z) - 1 = _
    rw [heq]
    ring
  have h := norm_tsum_le_tsum_norm hnorm
  rw [← hcomplex, Complex.norm_real, Real.norm_eq_abs, hnormsum] at h
  exact h

/-- Explicit exponentially small theta error. -/
noncomputable def thetaError (width : ℝ) : ℝ :=
  2 * (Real.exp (-Real.pi * width ^ 2) / (1 - Real.exp (-Real.pi * width ^ 2)))

theorem thetaError_nonneg (width : ℝ) (hw : 0 < width) : 0 ≤ thetaError width := by
  have h : Real.exp (-Real.pi * width ^ 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, sq_pos_of_pos hw])
  exact mul_nonneg (by norm_num) (div_nonneg (Real.exp_pos _).le (by linarith))

theorem theta_relative_error_exp (width center : ℝ) (hw : 0 < width) :
    |theta width center / width - 1| ≤ thetaError width := by
  apply (theta_relative_error width center hw).trans
  have h := realNormalizer_le_geometric (1 / width) (by positivity)
  have heq : Real.pi / (1 / width) ^ 2 = Real.pi * width ^ 2 := by field_simp
  rw [heq, ← neg_mul] at h
  unfold thetaError
  linarith

theorem summable_shiftedWeight (width center : ℝ) (hw : 0 < width) :
    Summable (shiftedWeight width center) := by
  let coefficient := Real.pi / width ^ 2
  have hc : 0 < coefficient := div_pos Real.pi_pos (sq_pos_of_pos hw)
  have hw' : 0 < Real.sqrt 2 * width := by positivity
  apply Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) _
    ((summable_weight (Real.sqrt 2 * width) hw').mul_left
      (Real.exp (coefficient * center ^ 2)))
  intro z
  unfold weight
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsq := mul_nonneg hc.le (sq_nonneg ((z : ℝ) - 2 * center))
  change -coefficient * ((z : ℝ) - center) ^ 2 ≤ _
  have heq : coefficient * center ^ 2 + -(Real.pi / (2 * width ^ 2)) * (z : ℝ) ^ 2 =
      coefficient * center ^ 2 - coefficient * (z : ℝ) ^ 2 / 2 := by
    dsimp [coefficient]
    ring
  rw [heq]
  nlinarith

theorem theta_pos (width center : ℝ) (hw : 0 < width) : 0 < theta width center := by
  have hzero := (summable_shiftedWeight width center hw).le_tsum (0 : ℤ)
    (fun z _ => (Real.exp_pos _).le)
  change shiftedWeight width center 0 ≤ theta width center at hzero
  exact (show 0 < shiftedWeight width center 0 by
    unfold shiftedWeight
    positivity).trans_le hzero

/-- The theta error decreases with the Gaussian width. -/
theorem thetaError_antitone (left right : ℝ) (hl : 0 < left) (h : left ≤ right) :
    thetaError right ≤ thetaError left := by
  have hr : 0 < right := hl.trans_le h
  have hl1 : Real.exp (-Real.pi * left ^ 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, sq_pos_of_pos hl])
  have hr1 : Real.exp (-Real.pi * right ^ 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, sq_pos_of_pos hr])
  have hsq : left ^ 2 ≤ right ^ 2 := (sq_le_sq₀ hl.le hr.le).mpr h
  have he : Real.exp (-Real.pi * right ^ 2) ≤ Real.exp (-Real.pi * left ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  unfold thetaError
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply (div_le_div_iff₀ (by linarith : 0 < 1 - Real.exp (-Real.pi * right ^ 2))
    (by linarith : 0 < 1 - Real.exp (-Real.pi * left ^ 2))).mpr
  nlinarith

theorem thetaError_le_four_exp (width : ℝ) (hw : 1 ≤ width) :
    thetaError width ≤ 4 * Real.exp (-Real.pi * width ^ 2) := by
  have hw0 : 0 < width := zero_lt_one.trans_le hw
  have hcoef : 1 ≤ Real.pi * width ^ 2 := by
    have hsq : 1 ≤ width ^ 2 := by nlinarith
    nlinarith [Real.pi_gt_three]
  have he : 2 ≤ Real.exp (Real.pi * width ^ 2) :=
    (by linarith : 2 ≤ Real.pi * width ^ 2 + 1).trans (Real.add_one_le_exp _)
  have hhalf : Real.exp (-Real.pi * width ^ 2) ≤ 1 / 2 := by
    rw [neg_mul, Real.exp_neg]
    exact (inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 1 / 2)).mpr
      (by simpa using he)
  have hden : 0 < 1 - Real.exp (-Real.pi * width ^ 2) := by linarith
  unfold thetaError
  have hquot : Real.exp (-Real.pi * width ^ 2) /
      (1 - Real.exp (-Real.pi * width ^ 2)) ≤ 2 * Real.exp (-Real.pi * width ^ 2) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [Real.exp_pos (-Real.pi * width ^ 2)]
  linarith

end AFT.GaussianSource

end P2MDyadicModule6

/- Helper module AFT.CenteredGaussianProgram. -/
section P2MDyadicModule7

namespace AFT.RationalNumerics

noncomputable section

set_option backward.isDefEq.respectTransparency false

theorem centeredGaussianSquaredWidth_pos (squaredWidth center : ℚ) (hw : 0<squaredWidth) :
    0<centeredGaussianSquaredWidth squaredWidth center := by
  unfold centeredGaussianSquaredWidth
  have hd : (0 : ℚ)<center.den := by exact_mod_cast center.den_pos
  positivity

theorem centeredGaussianRatio (squaredWidth center : ℚ) (point : ℤ) :
    (gaussianRatio (centeredGaussianSquaredWidth squaredWidth center)
      (centeredGaussianNumerator center point) : ℝ)=
      ((point : ℝ)-(center : ℝ))^2/(squaredWidth : ℝ) := by
  have hd : (center.den : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt center.den_pos)
  have hc : (center : ℝ)=(center.num : ℝ)/(center.den : ℝ) := Rat.cast_def center
  unfold gaussianRatio centeredGaussianSquaredWidth centeredGaussianNumerator
  push_cast
  rw [hc]
  field_simp

/-- The error is uniform in the center and integer point. All guard
precision in the pi and exponential programs is computed rationally. -/
theorem centeredGaussianApprox_error (squaredWidth center : ℚ) (point : ℤ) (bits : ℕ)
    (hw : 0<squaredWidth) :
    |(centeredGaussianApprox squaredWidth center point bits : ℝ)-
      Real.exp (-Real.pi*((point : ℝ)-(center : ℝ))^2/(squaredWidth : ℝ))|≤1/(2 : ℝ)^bits := by
  have hh := gaussianApprox_error (centeredGaussianSquaredWidth squaredWidth center)
    (centeredGaussianNumerator center point) bits (centeredGaussianSquaredWidth_pos squaredWidth center hw)
  have he : -Real.pi*(centeredGaussianNumerator center point : ℝ)^2 /
      (centeredGaussianSquaredWidth squaredWidth center : ℝ)=
      -Real.pi*((point : ℝ)-(center : ℝ))^2/(squaredWidth : ℝ) := by
    have hr := centeredGaussianRatio squaredWidth center point
    simp only [gaussianRatio,Rat.cast_div,Rat.cast_pow,Rat.cast_intCast] at hr
    calc
      _ = -Real.pi*((centeredGaussianNumerator center point : ℝ)^2 /
          (centeredGaussianSquaredWidth squaredWidth center : ℝ)) := by ring
      _ = -Real.pi*(((point : ℝ)-(center : ℝ))^2/(squaredWidth : ℝ)) := congrArg (-Real.pi*·) hr
      _ = _ := by ring
  rw [he] at hh
  exact hh

theorem centeredGaussianApprox_positive (squaredWidth center : ℚ) (point : ℤ) (bits : ℕ) :
    0<centeredGaussianApprox squaredWidth center point bits := gaussianApprox_positive _ _ _

theorem centeredGaussianApprox_shifted_error (squaredWidth center : ℚ) (width : ℝ)
    (point : ℤ) (bits : ℕ) (hw : 0<squaredWidth) (hsquare : width^2=(squaredWidth : ℝ)) :
    |(centeredGaussianApprox squaredWidth center point bits : ℝ)-
      GaussianSource.shiftedWeight width center point|≤1/(2 : ℝ)^bits := by
  have hh := centeredGaussianApprox_error squaredWidth center point bits hw
  have he : GaussianSource.shiftedWeight width center point=
      Real.exp (-Real.pi*((point : ℝ)-(center : ℝ))^2/(squaredWidth : ℝ)) := by
    unfold GaussianSource.shiftedWeight
    rw [hsquare]
    congr 1
    ring
  rw [he]
  exact hh

theorem centeredGaussianAnchor_bounds (center : ℚ) :
    (centeredGaussianAnchor center : ℝ)≤(center : ℝ) ∧
      (center : ℝ)<(centeredGaussianAnchor center : ℝ)+1 := by
  constructor
  · exact_mod_cast (Int.floor_le center)
  · exact_mod_cast (Int.lt_floor_add_one center)

end

end AFT.RationalNumerics

end P2MDyadicModule7

/- Helper module AFT.TotalVariation. -/
section P2MDyadicModule8

namespace AFT

open scoped BigOperators Classical

variable {α β : Type*} [Fintype α] [Fintype β]

namespace FiniteDist

/-- A stochastic kernel also contracts the `L¹` norm of an arbitrary signed
measure. This applies before clipping, where `TVBound.mix` alone would not. -/
theorem signed_kernel_l1_contraction (weight : α → ℝ) (kernel : α → FiniteDist β) :
    (∑ output, |∑ input, weight input * (kernel input).weight output|) ≤
      ∑ input, |weight input| := by
  calc
    (∑ output, |∑ input, weight input * (kernel input).weight output|) ≤
        ∑ output, ∑ input, |weight input| * (kernel input).weight output := by
      apply Finset.sum_le_sum
      intro output _
      have h := Finset.abs_sum_le_sum_abs
        (fun input => weight input * (kernel input).weight output) Finset.univ
      simpa only [abs_mul, abs_of_nonneg ((kernel _).nonneg _)] using h
    _ = ∑ input, |weight input| := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, sum_one, mul_one]

end FiniteDist

end AFT

end P2MDyadicModule8

/- Helper module AFT.ClippedConvolution. -/
section P2MDyadicModule9

namespace AFT.GaussianSource

open scoped BigOperators Classical

theorem integerMass_eq_pmf (width : ℝ) (hw : 0 < width) (z : ℤ) :
    integerMass width z = (integerGaussian width hw z).toReal := (integerGaussian_toReal width hw z).symm

end AFT.GaussianSource

end P2MDyadicModule9

/- Helper module AFT.CountableNormalizedTilt. -/
section P2MDyadicModule10

namespace AFT

open scoped BigOperators

/-- Normalizing a positive approximate density costs at most
`error / (1-error)` in total variation. Both masses are genuine normalized
countable laws; no unknown normalizer is treated as one. -/
theorem normalized_tilt_total_variation {State : Type*}
    (reference actual : State → ℝ)
    (href : ∀ state, 0 ≤ reference state)
    (hreference : Summable reference) (hactual : Summable actual)
    (href_one : ∑' state, reference state = 1)
    (hactual_one : ∑' state, actual state = 1)
    (scale error : ℝ) (herror : 0 ≤ error) (herror_one : error < 1)
    (hpoint : ∀ state, |actual state - scale * reference state| ≤
      error * scale * reference state) :
    (∑' state, |actual state-reference state|) / 2 ≤ error / (1-error) := by
  have hdiff := hactual.sub (hreference.mul_left scale)
  have hnorm : |1-scale| ≤ error*scale := by
    have ht := norm_tsum_le_tsum_norm hdiff.norm
    rw [hactual.tsum_sub (hreference.mul_left scale),tsum_mul_left,hactual_one,href_one,mul_one,Real.norm_eq_abs] at ht
    have hb := hdiff.norm.tsum_le_tsum (fun state => by
      simpa only [Real.norm_eq_abs] using hpoint state) (hreference.mul_left (error*scale))
    rw [tsum_mul_left,href_one,mul_one] at hb
    exact ht.trans hb
  have hs : scale ≤ 1/(1-error) := by
    apply (le_div_iff₀ (by linarith : 0<1-error)).mpr
    have hh' := (neg_le_abs (1-scale)).trans hnorm
    nlinarith
  have hbound (state : State) : |actual state-reference state| ≤
      (2*error*scale)*reference state := by
    calc
      _ = |(actual state-scale*reference state)+(scale-1)*reference state| := by congr 1; ring
      _ ≤ |actual state-scale*reference state|+|(scale-1)*reference state| := abs_add_le _ _
      _ ≤ error*scale*reference state+(error*scale)*reference state := by
        apply add_le_add (hpoint state)
        rw [abs_mul,abs_of_nonneg (href state),abs_sub_comm]
        exact mul_le_mul_of_nonneg_right hnorm (href state)
      _ = _ := by ring
  have hsum := (hactual.sub hreference).norm.tsum_le_tsum
    (fun state => by simpa only [Real.norm_eq_abs] using hbound state)
    (hreference.mul_left (2*error*scale))
  simp only [Real.norm_eq_abs,tsum_mul_left,href_one,mul_one] at hsum
  have hmul := mul_le_mul_of_nonneg_left hs herror
  rw [mul_one_div] at hmul
  linarith

end AFT

end P2MDyadicModule10

/- Helper module AFT.SignedConditioning. -/
section P2MDyadicModule11

namespace AFT.SignedConditioning

open scoped BigOperators Classical

noncomputable section

variable {Color : Type*} [Fintype Color]

theorem mass_difference_le_l1 (first second : Color → ℝ) :
    |(∑ color, first color) - ∑ color, second color| ≤ ∑ color, |first color - second color| := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

/-- Normalizing a signed mass loses at most twice its L1 error divided by
its actual positive mass. Only the reference mass needs pointwise positivity. -/
theorem normalized_signed_l1 (signed reference : Color → ℝ)
    (href : ∀ color, 0 ≤ reference color)
    (hsigned : 0 < ∑ color, signed color) (hreference : 0 < ∑ color, reference color) :
    (∑ color, |signed color / (∑ x, signed x) - reference color / (∑ x, reference x)|) ≤
      2 * (∑ color, |signed color - reference color|) / (∑ color, signed color) := by
  let total := ∑ color, signed color
  let referenceTotal := ∑ color, reference color
  let error := ∑ color, |signed color - reference color|
  have hmass : |referenceTotal - total| ≤ error := by
    simpa only [abs_sub_comm] using mass_difference_le_l1 signed reference
  have hpoint (color) : |signed color / total - reference color / referenceTotal| ≤
      |signed color - reference color| / total +
        reference color * |referenceTotal - total| / (total * referenceTotal) := by
    have heq : signed color / total - reference color / referenceTotal =
        (signed color - reference color) / total +
          reference color * (referenceTotal - total) / (total * referenceTotal) := by
      dsimp only [total, referenceTotal]
      field_simp
      ring
    rw [heq]
    exact (abs_add_le _ _).trans_eq (by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hsigned,
        abs_of_pos (mul_pos hsigned hreference), abs_of_nonneg (href color)])
  have hh := Finset.sum_le_sum (fun color (_ : color ∈ Finset.univ) => hpoint color)
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul] at hh
  have heq : (∑ color, |signed color - reference color|) / total +
      (∑ color, reference color) * |referenceTotal - total| / (total * referenceTotal) =
        (error + |referenceTotal - total|) / total := by
    dsimp only [error, total, referenceTotal]
    field_simp
  rw [heq] at hh
  apply hh.trans
  apply div_le_div_of_nonneg_right _ hsigned.le
  linarith

end

end AFT.SignedConditioning

end P2MDyadicModule11

/- Helper module AFT.FiniteTicketSampler. -/
section P2MDyadicModule12

namespace AFT.FiniteTicketSampler

open scoped BigOperators Classical

/-- Exactly the declared number of tickets selects each table entry,
including zero-count entries and indices beyond the end of the table. -/
theorem bucket_count (counts : List ℕ) (index : ℕ) :
    (∑ ticket ∈ Finset.range counts.sum, if bucket counts ticket = index then 1 else 0) =
      counts[index]?.getD 0 := by
  induction counts generalizing index with
  | nil => simp
  | cons count rest ih =>
    rw [List.sum_cons, Finset.sum_range_add]
    have hfirst (ticket : ℕ) (ht : ticket ∈ Finset.range count) :
        bucket (count :: rest) ticket = 0 := by
      simp only [bucket, if_pos (Finset.mem_range.mp ht)]
    have hsecond (ticket : ℕ) : bucket (count :: rest) (count + ticket) = 1 + bucket rest ticket := by
      simp only [bucket, show ¬count + ticket < count by omega, if_false, Nat.add_sub_cancel_left]
    simp_rw [hsecond]
    cases index with
    | zero =>
      have hf : (∑ ticket ∈ Finset.range count, if bucket (count :: rest) ticket = 0 then 1 else 0) = count := by
        calc
          _ = ∑ _ticket ∈ Finset.range count, (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro ticket ht
            rw [hfirst ticket ht]
            simp
          _ = _ := by simp
      simp [hf]
    | succ index =>
      have hf : (∑ ticket ∈ Finset.range count,
          if bucket (count :: rest) ticket = index + 1 then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro ticket ht
        rw [hfirst ticket ht]
        simp
      simp only [hf, zero_add, Nat.add_comm 1, Nat.add_right_cancel_iff,
        List.getElem?_cons_succ, ih]

end AFT.FiniteTicketSampler

end P2MDyadicModule12

/- Helper module AFT.FiniteQuantization. -/
section P2MDyadicModule13

namespace AFT.FiniteQuantization

open scoped BigOperators Classical

noncomputable section

variable {Color : Type*} [Fintype Color]

theorem deficit_le_card (law : FiniteDist Color) (tickets : ℕ) : deficit law tickets ≤ Fintype.card Color := by
  have hh := Finset.sum_le_sum fun color (_ : color ∈ Finset.univ) =>
    (Nat.lt_floor_add_one ((tickets : ℝ) * law.weight color)).le
  rw [← Finset.mul_sum, law.sum_one, mul_one, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] at hh
  have ht : (tickets : ℝ) ≤ (floorTotal law tickets : ℝ) + Fintype.card Color := by
    simpa only [floorTotal, floorCount, Nat.cast_sum] using hh
  have ht' : tickets ≤ floorTotal law tickets + Fintype.card Color := by exact_mod_cast ht
  unfold deficit
  omega

theorem floor_error_le (law : FiniteDist Color) (tickets : ℕ) (ht : 0 < tickets) (color : Color) :
    |(floorCount law tickets color : ℝ) / tickets - law.weight color| ≤ 1 / tickets := by
  have ht0 : (0 : ℝ) < tickets := by exact_mod_cast ht
  have hh := Nat.abs_floor_sub_le (mul_nonneg ht0.le (law.nonneg color))
  have heq : (floorCount law tickets color : ℝ) / tickets - law.weight color =
      ((floorCount law tickets color : ℝ) - (tickets : ℝ) * law.weight color) / tickets := by field_simp
  rw [heq, abs_div, abs_of_pos ht0]
  exact div_le_div_of_nonneg_right hh ht0.le

theorem roundedLaw_l1_le (law : FiniteDist Color) (tickets : ℕ) (ht : 0 < tickets) (fallback : Color) :
    (∑ color, |(roundedLaw law tickets ht fallback).weight color - law.weight color|) ≤
      2 * (Fintype.card Color : ℝ) / tickets := by
  have ht0 : (0 : ℝ) < tickets := by exact_mod_cast ht
  have hp (color) : |(roundedLaw law tickets ht fallback).weight color - law.weight color| ≤
      1 / tickets + if color = fallback then (deficit law tickets : ℝ) / tickets else 0 := by
    have heq : (roundedLaw law tickets ht fallback).weight color - law.weight color =
        ((floorCount law tickets color : ℝ) / tickets - law.weight color) +
          (if color = fallback then (deficit law tickets : ℝ) / tickets else 0) := by
      simp only [roundedLaw, count, Nat.cast_add, add_div]
      split_ifs <;> push_cast <;> ring
    rw [heq]
    apply (abs_add_le _ _).trans
    apply add_le_add (floor_error_le law tickets ht color)
    apply le_of_eq
    apply abs_of_nonneg
    split_ifs <;> positivity
  have hh := Finset.sum_le_sum (fun color (_ : color ∈ Finset.univ) => hp color)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at hh
  have hd : (deficit law tickets : ℝ) ≤ Fintype.card Color := by exact_mod_cast deficit_le_card law tickets
  have hd' := div_le_div_of_nonneg_right hd ht0.le
  calc
    _ ≤ (Fintype.card Color : ℝ) * (1 / tickets) + (deficit law tickets : ℝ) / tickets := hh
    _ ≤ (Fintype.card Color : ℝ) * (1 / tickets) + Fintype.card Color / tickets := add_le_add le_rfl hd'
    _ = _ := by ring

end

end AFT.FiniteQuantization

end P2MDyadicModule13

/- Helper module AFT.QuantizedSampling. -/
section P2MDyadicModule14

namespace AFT.FiniteTicketSampler

open scoped BigOperators Classical

theorem drawFin_law {n : ℕ} (counts : Fin n → ℕ) (hpositive : 0 < ∑ index, counts index)
    (index : Fin n) :
    (by
      letI : NeZero (∑ index, counts index) := ⟨hpositive.ne'⟩
      exact ((FiniteDist.uniform (Fin (∑ index, counts index))).map (drawFin counts)).weight index) =
      (counts index : ℝ) / (∑ index, counts index) := by
  letI : NeZero (∑ index, counts index) := ⟨hpositive.ne'⟩
  have hc := bucket_count (List.ofFn counts) index.val
  simp only [List.sum_ofFn, List.getElem?_ofFn, dif_pos index.isLt, Option.getD_some] at hc
  have hreal : (∑ ticket ∈ Finset.range (∑ index, counts index),
      if bucket (List.ofFn counts) ticket = index.val then (1 : ℝ) else 0) = counts index := by
    exact_mod_cast hc
  simp only [FiniteDist.map_weight, FiniteDist.uniform_weight, Fintype.card_fin,
    drawFin, Fin.ext_iff]
  simp_rw [show ∀ ticket : Fin (∑ index, counts index),
    (if bucket (List.ofFn counts) ticket.val = index.val then ((∑ index, counts index : ℕ) : ℝ)⁻¹ else 0) =
      ((∑ index, counts index : ℕ) : ℝ)⁻¹ *
        (if bucket (List.ofFn counts) ticket.val = index.val then 1 else 0) from
          fun ticket => by split_ifs <;> simp]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range
    (fun ticket => if bucket (List.ofFn counts) ticket = index.val then (1 : ℝ) else 0)
      (∑ index, counts index), hreal]
  ring

end FiniteTicketSampler

namespace FiniteQuantization

open scoped BigOperators Classical

noncomputable section

end

end FiniteQuantization

end AFT

end P2MDyadicModule14

/- Helper module AFT.FairBitSampling. -/
section P2MDyadicModule15

namespace AFT.FiniteTicketSampler

open scoped BigOperators Classical

theorem independent_fair_bits_uniform (bits : ℕ) :
    FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2)) =
      FiniteDist.uniform (Fin bits → Fin 2) := by
  apply FiniteDist.ext
  intro word
  simp only [FiniteDist.independent, FiniteDist.uniform_weight, Fintype.card_fin,
    Finset.prod_const, Finset.card_univ, Fintype.card_fun, Nat.cast_pow, inv_pow]

theorem bitTicket_uniform (bits : ℕ) :
    (FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map (bitTicket bits) =
      FiniteDist.uniform (Fin (2 ^ bits)) := by
  rw [independent_fair_bits_uniform]
  exact FiniteDist.uniform_map_equiv finFunctionFinEquiv

theorem drawBitTable_law {n : ℕ} (bits : ℕ) (counts : Fin n → ℕ)
    (htotal : ∑ index, counts index = 2 ^ bits) (index : Fin n) :
    ((FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map
      (drawBitTable bits counts htotal)).weight index = (counts index : ℝ) / (2 : ℝ) ^ bits := by
  have hpos : 0 < ∑ index, counts index := by rw [htotal]; positivity
  letI : NeZero (∑ index, counts index) := ⟨hpos.ne'⟩
  have hu := bitTicket_uniform bits
  have ht := FiniteDist.uniform_map_equiv (finCongr htotal.symm)
  have hm := congrArg (fun p : FiniteDist (Fin (2 ^ bits)) =>
    p.map (fun ticket => drawFin counts (Fin.cast htotal.symm ticket))) hu
  rw [FiniteDist.map_map] at hm
  have hc := congrArg (fun p : FiniteDist (Fin (∑ index, counts index)) => p.map (drawFin counts)) ht
  rw [FiniteDist.map_map] at hc
  change ((FiniteDist.uniform (Fin (2 ^ bits))).map
    (fun ticket => drawFin counts (Fin.cast htotal.symm ticket))) = _ at hc
  change ((FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map
    (fun word => drawFin counts (Fin.cast htotal.symm (bitTicket bits word)))).weight index = _
  rw [hm, hc]
  exact (drawFin_law counts hpos index).trans (by simp only [htotal, Nat.cast_pow, Nat.cast_ofNat])

end FiniteTicketSampler

end AFT

end P2MDyadicModule15

/- Helper module AFT.RationalFiniteQuantization. -/
section P2MDyadicModule16

namespace AFT.RationalFiniteQuantization

open scoped BigOperators

variable {size : ℕ}

noncomputable section

theorem floorCount_eq (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) (index : Fin (size + 1)) :
    floorCount weight tickets index =
      FiniteQuantization.floorCount (law weight hnonneg hsum) tickets index := by
  simp only [floorCount, FiniteQuantization.floorCount, law, ← Int.floor_toNat]
  have hcast : (tickets : ℝ) * (weight index : ℝ) =
      ((tickets : ℚ) * weight index : ℚ) := by push_cast; rfl
  rw [hcast, Rat.floor_cast]

theorem counts_eq (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) (index : Fin (size + 1)) :
    counts weight tickets index =
      FiniteQuantization.count (law weight hnonneg hsum) tickets 0 index := by
  simp only [counts, FiniteQuantization.count, deficit, FiniteQuantization.deficit,
    floorTotal, FiniteQuantization.floorTotal, floorCount_eq weight hnonneg hsum]
  split_ifs <;> rfl

theorem roundedLaw_eq (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) (ht : 0 < tickets) :
    roundedLaw weight hnonneg hsum tickets ht =
      FiniteQuantization.roundedLaw (law weight hnonneg hsum) tickets ht 0 := by
  apply FiniteDist.ext
  intro index
  exact congrArg (fun count : ℕ => (count : ℝ) / tickets)
    (counts_eq weight hnonneg hsum tickets index)

theorem roundedLaw_l1_le (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) (ht : 0 < tickets) :
    (∑ index, |(roundedLaw weight hnonneg hsum tickets ht).weight index -
      (weight index : ℝ)|) ≤ 2 * (size + 1 : ℝ) / tickets := by
  rw [roundedLaw_eq]
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, law] using
    FiniteQuantization.roundedLaw_l1_le (law weight hnonneg hsum) tickets ht 0

theorem draw_law (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (bits : ℕ) :
    (FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map
      (draw weight hnonneg hsum bits) =
      roundedLaw weight hnonneg hsum (2 ^ bits) (by positivity) := by
  apply FiniteDist.ext
  intro index
  unfold draw
  simpa only [roundedLaw, Nat.cast_pow, Nat.cast_ofNat] using
    FiniteTicketSampler.drawBitTable_law bits (counts weight (2 ^ bits))
      (counts_total weight hnonneg hsum (2 ^ bits)) index

end

end AFT.RationalFiniteQuantization

end P2MDyadicModule16

/- Helper module AFT.CountableChannelComposition. -/
section P2MDyadicModule17

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {First Second Output : Type*} [Fintype Output]

theorem countableChannel_summable (mass : First → ℝ) (hs : Summable mass)
    (channel : First → FiniteDist Output) (output : Output) :
    Summable (fun point => mass point*(channel point).weight output) := by
  apply Summable.of_norm_bounded hs.norm
  intro point
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg ((channel point).nonneg output)]
  apply mul_le_of_le_one_right (abs_nonneg _)
  rw [← (channel point).sum_one]
  exact Finset.single_le_sum (fun value _ => (channel point).nonneg value) (Finset.mem_univ output)

end

end AFT.FiniteDist

end P2MDyadicModule17

/- Helper module AFT.CenteredGaussianResources. -/
section P2MDyadicModule18

namespace AFT.RationalNumerics

open GaussianSource FiniteConvolutionProgram

open scoped BigOperators

noncomputable section

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 400000

set_option maxRecDepth 2048

theorem centeredGaussianRatio_rat (squaredWidth center : ℚ) (point : ℤ) :
    gaussianRatio (centeredGaussianSquaredWidth squaredWidth center) (centeredGaussianNumerator center point)=
      ((point : ℚ)-center)^2/squaredWidth := by
  exact_mod_cast centeredGaussianRatio squaredWidth center point

theorem centeredWindowRatio_bounds (squaredWidth center : ℚ) (cutoff : ℕ)
    (hwidth : 1 ≤ squaredWidth) (point : Window cutoff) :
    0 ≤ gaussianRatio (centeredGaussianSquaredWidth squaredWidth center)
      (centeredGaussianNumerator center (centeredGaussianAnchor center+point)) ∧
    gaussianRatio (centeredGaussianSquaredWidth squaredWidth center)
      (centeredGaussianNumerator center (centeredGaussianAnchor center+point)) ≤ (cutoff+1 : ℚ)^2 := by
  rw [centeredGaussianRatio_rat]
  have hfloor := Int.floor_le center
  have hfloor' := Int.lt_floor_add_one center
  have hp := Finset.mem_Icc.mp point.property
  have hlo : -(cutoff : ℚ) ≤ (point : ℤ) := by exact_mod_cast hp.1
  have hhi : ((point : ℤ) : ℚ) ≤ cutoff := by exact_mod_cast hp.2
  have hdiff : |((centeredGaussianAnchor center+(point : ℤ) : ℤ) : ℚ)-center| ≤ (cutoff+1 : ℚ) := by
    rw [abs_le]
    simp only [centeredGaussianAnchor,Int.cast_add]
    change -(↑cutoff+1) ≤ (⌊center⌋ : ℚ)+(point : ℤ)-center ∧
      (⌊center⌋ : ℚ)+(point : ℤ)-center ≤ ↑cutoff+1
    constructor <;> linarith
  refine ⟨by positivity,?_⟩
  apply (div_le_self (sq_nonneg _) hwidth).trans
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hdiff

end

end AFT.RationalNumerics

end P2MDyadicModule18

/- Helper module AFT.FiniteProductVariation. -/
section P2MDyadicModule19

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {A B : Type*} [Fintype A] [Fintype B]

theorem l1_map_le (first second : FiniteDist A) (map : A → B) :
    (∑ b,|(first.map map).weight b-(second.map map).weight b|) ≤ ∑ a,|first.weight a-second.weight a| := by
  simp only [map_weight,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ b,∑ a,|(if map a=b then first.weight a else 0)-(if map a=b then second.weight a else 0)| :=
      Finset.sum_le_sum fun b _ => Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single (map a)]
      · simp
      · intro b _ hba
        simp [Ne.symm hba]
      · simp

theorem l1_prod_le (first first' : FiniteDist A) (second second' : FiniteDist B) :
    (∑ pair,|(first.prod second).weight pair-(first'.prod second').weight pair|) ≤
      (∑ a,|first.weight a-first'.weight a|)+(∑ b,|second.weight b-second'.weight b|) := by
  simp only [prod_weight,Fintype.sum_prod_type]
  calc
    _ ≤ ∑ a,∑ b,(|first.weight a-first'.weight a| *second.weight b+
        first'.weight a*|second.weight b-second'.weight b|) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      have he : first.weight a*second.weight b-first'.weight a*second'.weight b=
          (first.weight a-first'.weight a)*second.weight b+first'.weight a*(second.weight b-second'.weight b) := by ring
      rw [he]
      simpa only [abs_mul,abs_of_nonneg (second.nonneg _),abs_of_nonneg (first'.nonneg _)] using abs_add_le
        ((first.weight a-first'.weight a)*second.weight b) (first'.weight a*(second.weight b-second'.weight b))
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,second.sum_one,mul_one,← Finset.sum_mul,first'.sum_one,one_mul]

omit [Fintype B] in
/-- The comparison is for the literal finite product law; all coordinate
errors are summed once. -/
theorem l1_independent_fin_le (count : ℕ) (first second : Fin count → FiniteDist A) :
    (∑ word,|(independent first).weight word-(independent second).weight word|) ≤
      ∑ i,∑ a,|(first i).weight a-(second i).weight a| := by
  induction count with
  | zero => simp only [independent,Fin.prod_univ_zero,sub_self,abs_zero,Finset.sum_const_zero,Fin.sum_univ_zero,le_refl]
  | succ count ih =>
    let tailFirst := independent (fun i : Fin count => first i.succ)
    let tailSecond := independent (fun i : Fin count => second i.succ)
    have hsplit (law : Fin (count+1) → FiniteDist A) : independent law=
        ((law 0).prod (independent (fun i : Fin count => law i.succ))).map (Fin.consEquiv (fun _ : Fin (count+1) => A)) := by
      ext word
      rw [map_equiv_weight]
      change (∏ i,(law i).weight (word i))=(law 0).weight (word 0)*∏ i : Fin count,(law i.succ).weight (word i.succ)
      exact Fin.prod_univ_succ _
    rw [hsplit first,hsplit second,Fin.sum_univ_succ]
    apply (l1_map_le _ _ _).trans
    exact (l1_prod_le (first 0) (second 0) tailFirst tailSecond).trans (add_le_add le_rfl (ih _ _))

end

end AFT.FiniteDist

end P2MDyadicModule19

/- Helper module AFT.FiniteConditionalSampling. -/
section P2MDyadicModule20

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 400000

theorem map_prod_functions {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (first : FiniteDist A) (second : FiniteDist B) (f : A → C) (g : B → D) :
    (first.prod second).map (fun pair => (f pair.1,g pair.2))=(first.map f).prod (second.map g) := by
  ext point
  rcases point with ⟨left,right⟩
  simp only [map_weight,prod_weight,Fintype.sum_prod_type,Prod.mk.injEq,Finset.sum_mul,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : f a=left <;> by_cases hb : g b=right <;> simp [ha,hb]

end

end AFT.FiniteDist

end P2MDyadicModule20

/- Helper module AFT.RationalPositiveNormalize. -/
section P2MDyadicModule21

namespace AFT.RationalNumerics

open scoped BigOperators

noncomputable section

open scoped Classical

set_option backward.isDefEq.respectTransparency false

theorem positiveNormalizeDraw_law {count : ℕ} (raw : Fin (count+1) → ℚ) (bits : ℕ) :
    (FiniteDist.independent (fun _ : Fin (bits+(count+1)+1) => FiniteDist.uniform (Fin 2))).map (positiveNormalizeDraw raw bits)=
      RationalFiniteQuantization.roundedLaw (positiveWeightProgram raw)
        (positiveWeightProgram_nonneg raw) (positiveWeightProgram_sum raw) (2^(bits+(count+1)+1)) (by positivity) := by
  exact RationalFiniteQuantization.draw_law _ _ _ _

theorem positiveNormalizeDraw_l1 {count : ℕ} (raw : Fin (count+1) → ℚ) (bits : ℕ) :
    (∑index,|((FiniteDist.independent (fun _ : Fin (bits+(count+1)+1) => FiniteDist.uniform (Fin 2))).map
      (positiveNormalizeDraw raw bits)).weight index-(positiveProgramLaw raw).weight index|)≤1/(2 : ℝ)^bits := by
  rw [positiveNormalizeDraw_law]
  have hh := RationalFiniteQuantization.roundedLaw_l1_le (positiveWeightProgram raw)
    (positiveWeightProgram_nonneg raw) (positiveWeightProgram_sum raw) (2^(bits+(count+1)+1)) (by positivity)
  apply hh.trans
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  have hp : ((count+1 : ℕ) : ℝ)≤(2 : ℝ)^(count+1) := by exact_mod_cast (Nat.lt_two_pow_self (n:=count+1)).le
  calc
    _≤2*((2 : ℝ)^(count+1))/(2 : ℝ)^(bits+(count+1)+1) := by
      gcongr
      simpa only [Nat.cast_add,Nat.cast_one] using hp
    _=_ := by rw [pow_add,pow_add];field_simp;ring

end

end AFT.RationalNumerics

end P2MDyadicModule21

/- Helper module Solutions.RegevBridgeGaussianRandomizedRounding. -/
section P2MDyadicModule22

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding

open AFT GaussianSource

open scoped BigOperators Classical ENNReal

noncomputable section

def roundingNormalizer (width center : ℝ) : ℝ≥0∞ :=
  ∑' value : ℤ,ENNReal.ofReal (shiftedWeight width center value)

theorem roundingNormalizer_ne_zero (width center : ℝ) : roundingNormalizer width center≠0 := by
  intro hz
  have hv := ENNReal.tsum_eq_zero.mp hz (0 : ℤ)
  exact (not_le_of_gt (show 0<shiftedWeight width center 0 from Real.exp_pos _)) (ENNReal.ofReal_eq_zero.mp hv)

theorem roundingNormalizer_ne_top (width center : ℝ) (hwidth : 0<width) :
    roundingNormalizer width center≠⊤ :=
  (summable_shiftedWeight width center hwidth).tsum_ofReal_ne_top

/-- The kernel uses the existing shifted theta normalizer exactly. -/
theorem roundingNormalizer_toReal (width center : ℝ) :
    (roundingNormalizer width center).toReal=theta width center := by
  unfold roundingNormalizer theta
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro value
  exact ENNReal.toReal_ofReal (Real.exp_nonneg _)

/-- The displayed error is genuinely below one for widths at least one. -/
theorem roundingError_lt_one (width : ℝ) (hwidth : 1≤width) : thetaError width<1 := by
  have hs : 1≤width^2 := one_le_pow₀ hwidth
  have hp : 3<Real.pi*width^2 := by nlinarith [Real.pi_gt_three]
  have he : 4<Real.exp (Real.pi*width^2) :=
    (by linarith : (4 : ℝ)<Real.pi*width^2+1).trans_le (Real.add_one_le_exp _)
  have hn : Real.exp (-Real.pi*width^2)<1/4 := by
    rw [show -Real.pi*width^2=-(Real.pi*width^2) by ring,Real.exp_neg]
    apply (inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ)<1/4)).2
    simpa using he
  exact (thetaError_le_four_exp width hwidth).trans_lt (by linarith)

/-- The actual conditional PMF D_(Z-center),width shifted back to Z. -/
def roundingPMF (width : ℝ) (hwidth : 0<width) (center : ℝ) : PMF ℤ :=
  PMF.normalize (fun value => ENNReal.ofReal (shiftedWeight width center value))
    (roundingNormalizer_ne_zero width center) (roundingNormalizer_ne_top width center hwidth)

/-- Exact real conditional density of the normalized rounding PMF. -/
theorem roundingPMF_toReal (width : ℝ) (hwidth : 0<width) (center : ℝ) (value : ℤ) :
    (roundingPMF width hwidth center value).toReal=shiftedWeight width center value/theta width center := by
  change (ENNReal.ofReal (shiftedWeight width center value)*(roundingNormalizer width center)⁻¹).toReal=_
  rw [ENNReal.toReal_mul,ENNReal.toReal_inv,roundingNormalizer_toReal,
    ENNReal.toReal_ofReal (show 0 ≤ shiftedWeight width center value from Real.exp_nonneg _)]
  rfl

/-- Uniform pointwise bounds around the continuous-kernel reference. The
normalization error is proved, rather than supplied as a kernel certificate. -/
theorem roundingPMF_density_bounds (width : ℝ) (hwidth : 1≤width) (center : ℝ) (value : ℤ) :
    shiftedWeight width center value/(width*(1+thetaError width)) ≤
        (roundingPMF width (zero_lt_one.trans_le hwidth) center value).toReal ∧
      (roundingPMF width (zero_lt_one.trans_le hwidth) center value).toReal ≤
        shiftedWeight width center value/(width*(1-thetaError width)) := by
  have hw : 0<width := zero_lt_one.trans_le hwidth
  have herr := roundingError_lt_one width hwidth
  have ht := abs_le.mp (theta_relative_error_exp width center hw)
  have hlow : width*(1-thetaError width)≤theta width center := by
    rw [mul_comm]
    exact (le_div_iff₀ hw).mp (by linarith [ht.1])
  have hupp : theta width center≤width*(1+thetaError width) := by
    rw [mul_comm]
    exact (div_le_iff₀ hw).mp (by linarith [ht.2])
  rw [roundingPMF_toReal]
  have ha : 0 ≤ shiftedWeight width center value := Real.exp_nonneg _
  exact ⟨div_le_div_of_nonneg_left ha (theta_pos width center hw) hupp,
    div_le_div_of_nonneg_left ha (mul_pos hw (by linarith)) hlow⟩

/-- The exact modular output of Gaussian randomized rounding. -/
def modularRounding (q : ℕ) [NeZero q] (width : ℝ) (hwidth : 0<width) (center : ℝ) :
    FiniteDist (ZMod q) :=
  finiteLaw ((roundingPMF width hwidth center).map (fun value : ℤ => (value : ZMod q)))

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding

end P2MDyadicModule22

/- Helper module Solutions.RegevBridgeGaussianRoundingFiniteBits. -/
section P2MDyadicModule23

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding

open AFT GaussianSource AFT.RationalNumerics

open scoped BigOperators Classical

def rawNormalizer (squaredWidth center : ℚ) (cutoff bits : ℕ) : ℚ :=
  ∑ index,rawTable squaredWidth center cutoff bits index

noncomputable section

theorem rawTable_pos (squaredWidth center : ℚ) (cutoff bits : ℕ) (index : Fin (2*cutoff+1)) :
    0< rawTable squaredWidth center cutoff bits index := centeredGaussianApprox_positive _ _ _ _

theorem rawNormalizer_pos (squaredWidth center : ℚ) (cutoff bits : ℕ) :
    0< rawNormalizer squaredWidth center cutoff bits := by
  exact (rawTable_pos squaredWidth center cutoff bits 0).trans_le
    (Finset.single_le_sum (fun index _ => (rawTable_pos squaredWidth center cutoff bits index).le) (Finset.mem_univ 0))

theorem windowMass_pos (width : ℝ) (center : ℚ) (cutoff : ℕ) :
    0<∑ index : Fin (2*cutoff+1),shiftedWeight width center (windowPoint center cutoff index) := by
  have hz : 0< shiftedWeight width center (windowPoint center cutoff 0) := Real.exp_pos _
  exact hz.trans_le (Finset.single_le_sum
    (f := fun index : Fin (2*cutoff+1) => shiftedWeight width center (windowPoint center cutoff index))
    (fun index _ => (show 0 ≤ shiftedWeight width center (windowPoint center cutoff index) from Real.exp_nonneg _))
    (Finset.mem_univ 0))

/-- The exact truncated law, using the same true Gaussian weights as the
infinite randomized-rounding PMF. -/
def windowLaw (width : ℝ) (center : ℚ) (cutoff : ℕ) : FiniteDist (Fin (2*cutoff+1)) :=
  FiniteDist.normalize (fun index => shiftedWeight width center (windowPoint center cutoff index))
    (fun _ => Real.exp_nonneg _) (windowMass_pos width center cutoff)

/-- The finite reference is literally the full kernel conditioned to the
public integer window; the full theta normalization cancels exactly. -/
theorem windowLaw_eq_conditional (width : ℝ) (hwidth : 0< width) (center : ℚ) (cutoff : ℕ)
    (index : Fin (2*cutoff+1)) :
    (windowLaw width center cutoff).weight index=
      (roundingPMF width hwidth center (windowPoint center cutoff index)).toReal /
        ∑ point : Fin (2*cutoff+1),(roundingPMF width hwidth center (windowPoint center cutoff point)).toReal := by
  simp_rw [roundingPMF_toReal]
  simp only [windowLaw,FiniteDist.normalize]
  rw [←Finset.sum_div]
  field_simp [(theta_pos width center hwidth).ne',(windowMass_pos width center cutoff).ne']

theorem positiveProgramLaw_rawTable (squaredWidth center : ℚ) (cutoff bits : ℕ) (index : Fin (2*cutoff+1)) :
    (positiveProgramLaw (rawTable squaredWidth center cutoff bits)).weight index=
      (rawTable squaredWidth center cutoff bits index : ℝ)/(rawNormalizer squaredWidth center cutoff bits : ℝ) := by
  have hp (point : Fin (2*cutoff+1)) : positivePartProgram (rawTable squaredWidth center cutoff bits) point=
      rawTable squaredWidth center cutoff bits point := max_eq_right (rawTable_pos squaredWidth center cutoff bits point).le
  have hn : positiveNormalizerProgram (rawTable squaredWidth center cutoff bits)=rawNormalizer squaredWidth center cutoff bits := by
    simp only [positiveNormalizerProgram,hp,rawNormalizer]
  simp only [positiveProgramLaw,positiveWeightProgram,hn,if_neg (rawNormalizer_pos squaredWidth center cutoff bits).ne',hp,Rat.cast_div]

theorem rawTable_error (squaredWidth center : ℚ) (width : ℝ) (cutoff bits : ℕ)
    (hsquared : 0< squaredWidth) (hwidth : width^2=(squaredWidth : ℝ)) :
    (∑ index : Fin (2*cutoff+1),|(rawTable squaredWidth center cutoff bits index : ℝ)-
      shiftedWeight width center (windowPoint center cutoff index)|)≤(2*cutoff+1 : ℕ)/(2 : ℝ)^bits := by
  have h := Finset.sum_le_sum (fun index (_ : index∈(Finset.univ : Finset (Fin (2*cutoff+1)))) =>
    centeredGaussianApprox_shifted_error squaredWidth center width (windowPoint center cutoff index) bits hsquared hwidth)
  simpa only [rawTable,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one_div] using h

/-- Certified numerical normalization error, with the actual computed
positive denominator retained explicitly. -/
theorem table_l1 (squaredWidth center : ℚ) (width : ℝ) (cutoff bits : ℕ)
    (hsquared : 0< squaredWidth) (hwidth : width^2=(squaredWidth : ℝ)) :
    (∑ index,|(positiveProgramLaw (rawTable squaredWidth center cutoff bits)).weight index-
      (windowLaw width center cutoff).weight index|)≤
        2*((2*cutoff+1 : ℕ)/(2 : ℝ)^bits)/(rawNormalizer squaredWidth center cutoff bits : ℝ) := by
  let approximate : Fin (2*cutoff+1) → ℝ := fun index => (rawTable squaredWidth center cutoff bits index : ℝ)
  let exactWeight : Fin (2*cutoff+1) → ℝ := fun index => shiftedWeight width center (windowPoint center cutoff index)
  have hn : (rawNormalizer squaredWidth center cutoff bits : ℝ)=∑ index,approximate index := by
    simp only [rawNormalizer,Rat.cast_sum,approximate]
  have hp : 0<∑ index,approximate index := by
    rw [←hn]
    exact_mod_cast rawNormalizer_pos squaredWidth center cutoff bits
  have he := SignedConditioning.normalized_signed_l1 approximate exactWeight (fun _ => Real.exp_nonneg _)
    hp (windowMass_pos width center cutoff)
  simp_rw [positiveProgramLaw_rawTable]
  change (∑ index,|approximate index/(rawNormalizer squaredWidth center cutoff bits : ℝ)-
    exactWeight index/(∑ point,exactWeight point)|)≤_
  rw [hn]
  apply he.trans
  rw [←hn]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (rawTable_error squaredWidth center width cutoff bits hsquared hwidth) (by norm_num))
    (by exact_mod_cast (rawNormalizer_pos squaredWidth center cutoff bits).le)

/-- The anchor is always within one of the center. Thus a fixed lower
Gaussian mass is available uniformly in every rational center and cutoff. -/
theorem anchorWeight_lower (width : ℝ) (hwidth : 1≤ width) (center : ℚ) (cutoff : ℕ) :
    Real.exp (-Real.pi)≤ shiftedWeight width center
      (windowPoint center cutoff ⟨cutoff,by omega⟩) := by
  have hw : 0< width := zero_lt_one.trans_le hwidth
  have hs := centeredGaussianAnchor_bounds center
  have hpoint : windowPoint center cutoff ⟨cutoff,by omega⟩=centeredGaussianAnchor center := by
    simp [windowPoint]
  rw [hpoint]
  have hdiff : ((centeredGaussianAnchor center : ℝ)-(center : ℝ))^2≤1 := by
    nlinarith [hs.1,hs.2]
  have hsq : 1≤ width^2 := one_le_pow₀ hwidth
  have hexp : (Real.pi/width^2)*((centeredGaussianAnchor center : ℝ)-(center : ℝ))^2≤ Real.pi := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hw)).2
    nlinarith [Real.pi_pos]
  unfold shiftedWeight
  apply Real.exp_le_exp.mpr
  nlinarith [hexp]

theorem rawNormalizer_anchor_lower (squaredWidth center : ℚ) (width : ℝ) (cutoff bits : ℕ)
    (hsquared : 0< squaredWidth) (hsquare : width^2=(squaredWidth : ℝ)) (hwidth : 1≤ width) :
    Real.exp (-Real.pi)-1/(2 : ℝ)^bits≤(rawNormalizer squaredWidth center cutoff bits : ℝ) := by
  let anchor : Fin (2*cutoff+1) := ⟨cutoff,by omega⟩
  have he := centeredGaussianApprox_shifted_error squaredWidth center width
    (windowPoint center cutoff anchor) bits hsquared hsquare
  have hm : (rawTable squaredWidth center cutoff bits anchor : ℝ)≤
      (rawNormalizer squaredWidth center cutoff bits : ℝ) := by
    exact_mod_cast Finset.single_le_sum
      (fun index _ => (rawTable_pos squaredWidth center cutoff bits index).le) (Finset.mem_univ anchor)
  have hl := anchorWeight_lower width hwidth center cutoff
  have hdiff := (abs_le.mp he).1
  change -(1/(2 : ℝ)^bits)≤(rawTable squaredWidth center cutoff bits anchor : ℝ)-
    shiftedWeight width center (windowPoint center cutoff anchor) at hdiff
  dsimp only [anchor] at *
  linarith

private theorem exp_pi_lt_128 : Real.exp Real.pi<128 := by
  have he : Real.exp (4 : ℝ)=(Real.exp 1)^4 := by
    simpa only [Nat.cast_ofNat,mul_one] using Real.exp_nat_mul (1 : ℝ) 4
  have hp : (Real.exp 1)^4<(3 : ℝ)^4 := pow_lt_pow_left₀ (Real.exp_one_lt_three)
    (Real.exp_pos 1).le (by norm_num)
  have hπ := Real.exp_lt_exp.mpr Real.pi_lt_four
  rw [he] at hπ
  norm_num at hp
  linarith

theorem rawNormalizer_ge (squaredWidth center : ℚ) (width : ℝ) (cutoff bits : ℕ)
    (hsquared : 0< squaredWidth) (hsquare : width^2=(squaredWidth : ℝ)) (hwidth : 1≤ width)
    (hbits : 9≤ bits) :
    (1/256 : ℝ)≤(rawNormalizer squaredWidth center cutoff bits : ℝ) := by
  have he : (1/128 : ℝ)< Real.exp (-Real.pi) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_lt_one_div_of_lt (Real.exp_pos Real.pi) exp_pi_lt_128
  have hp : (512 : ℝ)≤(2 : ℝ)^bits := by
    calc
      _ = (2 : ℝ)^9 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) hbits
  have herr : 1/(2 : ℝ)^bits≤1/512 := one_div_le_one_div_of_le (by norm_num) hp
  have h := rawNormalizer_anchor_lower squaredWidth center width cutoff bits hsquared hsquare hwidth
  linarith

theorem table_l1_precision (squaredWidth center : ℚ) (width : ℝ) (cutoff bits : ℕ)
    (hsquared : 0< squaredWidth) (hsquare : width^2=(squaredWidth : ℝ)) (hwidth : 1≤ width) :
    (∑ index,|(positiveProgramLaw (rawTable squaredWidth center cutoff (roundingPrecision cutoff bits))).weight index-
      (windowLaw width center cutoff).weight index|)≤1/(2 : ℝ)^bits := by
  have hn := rawNormalizer_ge squaredWidth center width cutoff (roundingPrecision cutoff bits)
    hsquared hsquare hwidth (by unfold roundingPrecision;omega)
  have ht := table_l1 squaredWidth center width cutoff (roundingPrecision cutoff bits) hsquared hsquare
  have hc : ((2*cutoff+1 : ℕ) : ℝ)≤(2 : ℝ)^(2*cutoff+1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := 2*cutoff+1)).le
  apply ht.trans
  calc
    _ ≤ 2*((2*cutoff+1 : ℕ)/(2 : ℝ)^(roundingPrecision cutoff bits))/(1/256) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hn
    _ ≤ 2*((2 : ℝ)^(2*cutoff+1)/(2 : ℝ)^(roundingPrecision cutoff bits))/(1/256) := by gcongr
    _ = _ := by
      unfold roundingPrecision
      rw [pow_add,pow_add]
      field_simp
      ring

/-- Uniformly in the rational center, the executed finite-bit index draw is
within 2^-bits in L1 of the actual window-conditioned Gaussian rounding. -/
theorem finiteDrawIndex_l1 (squaredWidth center : ℚ) (width : ℝ) (cutoff bits : ℕ)
    (hsquared : 0< squaredWidth) (hsquare : width^2=(squaredWidth : ℝ)) (hwidth : 1≤ width) :
    (∑ index,|((FiniteDist.independent (fun _ : Fin ((bits+1)+(2*cutoff+1)+1) => FiniteDist.uniform (Fin 2))).map
        (finiteDrawIndex squaredWidth center cutoff bits)).weight index-
      (windowLaw width center cutoff).weight index|)≤1/(2 : ℝ)^bits := by
  have hc := positiveNormalizeDraw_l1 (rawTable squaredWidth center cutoff (roundingPrecision cutoff (bits+1))) (bits+1)
  have hn := table_l1_precision squaredWidth center width cutoff (bits+1) hsquared hsquare hwidth
  have htri : (∑ index,|((FiniteDist.independent (fun _ : Fin ((bits+1)+(2*cutoff+1)+1) => FiniteDist.uniform (Fin 2))).map
        (finiteDrawIndex squaredWidth center cutoff bits)).weight index-
      (windowLaw width center cutoff).weight index|)≤1/(2 : ℝ)^(bits+1)+1/(2 : ℝ)^(bits+1) := by
    apply le_trans _ (add_le_add hc hn)
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro index _
    exact abs_sub_le _ ((positiveProgramLaw (rawTable squaredWidth center cutoff (roundingPrecision cutoff (bits+1)))).weight index) _
  apply htri.trans_eq
  rw [pow_succ]
  field_simp
  ring

/-- The actual modular finite-bit output has the same certified numerical
error. Only the omitted infinite tail remains outside this finite-window
implementation theorem. -/
theorem finiteDraw_modular_l1 (q : ℕ) [NeZero q] (squaredWidth center : ℚ) (width : ℝ)
    (cutoff bits : ℕ) (hsquared : 0< squaredWidth)
    (hsquare : width^2=(squaredWidth : ℝ)) (hwidth : 1≤ width) :
    (∑ value : ZMod q,|((FiniteDist.independent (fun _ : Fin ((bits+1)+(2*cutoff+1)+1) => FiniteDist.uniform (Fin 2))).map
        (fun word => (finiteDraw squaredWidth center cutoff bits word : ZMod q))).weight value-
      ((windowLaw width center cutoff).map (fun index => (windowPoint center cutoff index : ZMod q))).weight value|)≤
        1/(2 : ℝ)^bits := by
  have h := FiniteDist.l1_map_le
    ((FiniteDist.independent (fun _ : Fin ((bits+1)+(2*cutoff+1)+1) => FiniteDist.uniform (Fin 2))).map
      (finiteDrawIndex squaredWidth center cutoff bits))
    (windowLaw width center cutoff) (fun index => (windowPoint center cutoff index : ZMod q))
  rw [FiniteDist.map_map] at h
  exact h.trans (finiteDrawIndex_l1 squaredWidth center width cutoff bits hsquared hsquare hwidth)

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding

end P2MDyadicModule23

/- Helper module Solutions.RegevBridgeGaussianRoundingTail. -/
section P2MDyadicModule24

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding

open AFT GaussianSource AFT.RationalNumerics

open scoped BigOperators Classical

noncomputable section

def tailEnvelope (width radius : ℝ) : ℝ :=
  Real.sqrt 2*(1+thetaError (Real.sqrt 2*width))/(1-thetaError width)*
    Real.exp (-Real.pi*radius^2/(2*width^2))

theorem summable_roundingMass (width : ℝ) (hwidth : 0<width) (center : ℝ) :
    Summable (fun value : ℤ => (roundingPMF width hwidth center value).toReal) := by
  simp_rw [roundingPMF_toReal]
  exact (summable_shiftedWeight width center hwidth).div_const _

private theorem theta_ratio_bound (width : ℝ) (hwidth : 1≤width) (center : ℝ) :
    theta (Real.sqrt 2*width) center/theta width center ≤
      Real.sqrt 2*(1+thetaError (Real.sqrt 2*width))/(1-thetaError width) := by
  have hw : 0<width := zero_lt_one.trans_le hwidth
  have hb : 0<Real.sqrt 2*width := by positivity
  have hs := roundingError_lt_one width hwidth
  have hl := (abs_le.mp (theta_relative_error_exp width center hw)).1
  have hu := (abs_le.mp (theta_relative_error_exp (Real.sqrt 2*width) center hb)).2
  have hlow : width*(1-thetaError width)≤theta width center := by
    rw [mul_comm]
    exact (le_div_iff₀ hw).mp (by linarith)
  have hupp : theta (Real.sqrt 2*width) center≤
      (Real.sqrt 2*width)*(1+thetaError (Real.sqrt 2*width)) := by
    have hn : theta (Real.sqrt 2*width) center/(Real.sqrt 2*width)≤1+thetaError (Real.sqrt 2*width) := by linarith
    exact ((div_le_iff₀ hb).mp hn).trans_eq (mul_comm _ _)
  have hpos : 0<width*(1-thetaError width) := mul_pos hw (by linarith)
  have ha : 0≤(Real.sqrt 2*width)*(1+thetaError (Real.sqrt 2*width)) := by
    have he := thetaError_nonneg (Real.sqrt 2*width) hb
    positivity
  calc
    _ ≤ ((Real.sqrt 2*width)*(1+thetaError (Real.sqrt 2*width)))/theta width center :=
      div_le_div_of_nonneg_right hupp (theta_pos width center hw).le
    _ ≤ ((Real.sqrt 2*width)*(1+thetaError (Real.sqrt 2*width)))/(width*(1-thetaError width)) :=
      div_le_div_of_nonneg_left ha hpos hlow
    _ = _ := by field_simp [hw.ne']

/-- Pointwise tail domination uses the actual shifted Gaussian at both
widths, so it is uniform over all real centers. -/
theorem shiftedWeight_tail_le (width center radius : ℝ) (hwidth : 0<width) (hradius : 0≤radius)
    (value : ℤ) (hfar : radius≤|(value : ℝ)-center|) :
    shiftedWeight width center value≤
      Real.exp (-Real.pi*radius^2/(2*width^2))*shiftedWeight (Real.sqrt 2*width) center value := by
  have hroot : (Real.sqrt (2 : ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hsq : radius^2≤((value : ℝ)-center)^2 := by
    have h := (sq_le_sq₀ hradius (abs_nonneg ((value : ℝ)-center))).2 hfar
    simpa only [sq_abs] using h
  let a := Real.pi/(2*width^2)
  have ha : 0≤a := by dsimp [a];positivity
  have hh := mul_le_mul_of_nonneg_left hsq ha
  unfold shiftedWeight
  rw [←Real.exp_add,mul_pow,hroot]
  apply Real.exp_le_exp.mpr
  have he0 : -(Real.pi/width^2)*((value : ℝ)-center)^2=-2*a*((value : ℝ)-center)^2 := by dsimp [a];ring
  have he1 : -Real.pi*radius^2/(2*width^2)=-a*radius^2 := by dsimp [a];ring
  rw [he0,he1]
  change -2*a*((value : ℝ)-center)^2≤-a*radius^2+(-a)*((value : ℝ)-center)^2
  nlinarith

def roundingTail (width : ℝ) (hwidth : 0<width) (center radius : ℝ) : ℝ :=
  ∑' value : ℤ,if radius≤|(value : ℝ)-center| then (roundingPMF width hwidth center value).toReal else 0

/-- Full countable tail probability of the true normalized rounding PMF. -/
theorem roundingTail_le (width : ℝ) (hwidth : 1≤width) (center radius : ℝ) (hradius : 0≤radius) :
    roundingTail width (zero_lt_one.trans_le hwidth) center radius≤tailEnvelope width radius := by
  have hw : 0<width := zero_lt_one.trans_le hwidth
  have hb : 0<Real.sqrt 2*width := by positivity
  let factor := Real.exp (-Real.pi*radius^2/(2*width^2))/theta width center
  have hf : 0≤factor := div_nonneg (Real.exp_nonneg _) (theta_pos width center hw).le
  have hsum := (summable_shiftedWeight (Real.sqrt 2*width) center hb).mul_left factor
  have hp (value : ℤ) :
      (if radius≤|(value : ℝ)-center| then (roundingPMF width hw center value).toReal else 0)≤
        factor*shiftedWeight (Real.sqrt 2*width) center value := by
    split_ifs with hfar
    · rw [roundingPMF_toReal]
      have h := div_le_div_of_nonneg_right (shiftedWeight_tail_le width center radius hw hradius value hfar)
        (theta_pos width center hw).le
      exact h.trans_eq (by dsimp [factor];ring)
    · exact mul_nonneg hf (Real.exp_nonneg _)
  have hs : Summable (fun value : ℤ => if radius≤|(value : ℝ)-center| then
      (roundingPMF width hw center value).toReal else 0) :=
    Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) hp hsum
  have ht := hs.tsum_le_tsum hp hsum
  rw [tsum_mul_left] at ht
  change roundingTail width hw center radius≤factor*theta (Real.sqrt 2*width) center at ht
  apply ht.trans
  unfold tailEnvelope factor
  have hr := mul_le_mul_of_nonneg_right (theta_ratio_bound width hwidth center)
    (Real.exp_nonneg (-Real.pi*radius^2/(2*width^2)))
  convert hr using 1
  ring

/-- Omitted points from the floor-centered palette are genuinely far from
the original rational center, using integer discreteness on both sides. -/
theorem outsideWindow_far (center : ℚ) (cutoff : ℕ) (value : ℤ)
    (hout : value∉Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
      (centeredGaussianAnchor center+(cutoff : ℤ))) :
    (cutoff : ℝ)≤|(value : ℝ)-(center : ℝ)| := by
  have hs := centeredGaussianAnchor_bounds center
  have ho : value≤centeredGaussianAnchor center-(cutoff : ℤ)-1 ∨
      centeredGaussianAnchor center+(cutoff : ℤ)+1≤value := by
    simp only [Finset.mem_Icc,not_and_or] at hout
    omega
  rcases ho with hl|hr
  · have hlR : (value : ℝ)≤(centeredGaussianAnchor center : ℝ)-(cutoff : ℝ)-1 := by exact_mod_cast hl
    apply le_trans _ (neg_le_abs ((value : ℝ)-(center : ℝ)))
    linarith [hs.1]
  · have hrR : (centeredGaussianAnchor center : ℝ)+(cutoff : ℝ)+1≤(value : ℝ) := by exact_mod_cast hr
    apply le_trans _ (le_abs_self ((value : ℝ)-(center : ℝ)))
    linarith [hs.2]

def outsideWindowMass (width : ℝ) (hwidth : 0<width) (center : ℚ) (cutoff : ℕ) : ℝ :=
  ∑' value : ℤ,if value∉Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
    (centeredGaussianAnchor center+(cutoff : ℤ)) then (roundingPMF width hwidth center value).toReal else 0

/-- A uniform analytic bound on the entire omitted probability of the same
infinite kernel approximated by the executed finite-bit sampler. -/
theorem outsideWindowMass_le (width : ℝ) (hwidth : 1≤width) (center : ℚ) (cutoff : ℕ) :
    outsideWindowMass width (zero_lt_one.trans_le hwidth) center cutoff≤tailEnvelope width cutoff := by
  have hw : 0<width := zero_lt_one.trans_le hwidth
  have hmass := summable_roundingMass width hw center
  have hs : Summable (fun value : ℤ => if value∉Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
      (centeredGaussianAnchor center+(cutoff : ℤ)) then (roundingPMF width hw center value).toReal else 0) := by
    apply Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) _ hmass
    intro value
    by_cases h : value∉Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
      (centeredGaussianAnchor center+(cutoff : ℤ))
    · rw [if_pos h]
    · rw [if_neg h]
      exact ENNReal.toReal_nonneg
  have ht : Summable (fun value : ℤ => if (cutoff : ℝ)≤|(value : ℝ)-(center : ℝ)| then
      (roundingPMF width hw center value).toReal else 0) := by
    apply Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) _ hmass
    intro value
    by_cases h : (cutoff : ℝ)≤|(value : ℝ)-(center : ℝ)|
    · rw [if_pos h]
    · rw [if_neg h]
      exact ENNReal.toReal_nonneg
  have hp (value : ℤ) :
      (if value∉Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
        (centeredGaussianAnchor center+(cutoff : ℤ)) then (roundingPMF width hw center value).toReal else 0)≤
      (if (cutoff : ℝ)≤|(value : ℝ)-(center : ℝ)| then (roundingPMF width hw center value).toReal else 0) := by
    by_cases hout : value∉Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
      (centeredGaussianAnchor center+(cutoff : ℤ))
    · have hfar := outsideWindow_far center cutoff value hout
      rw [if_pos hout,if_pos hfar]
    · rw [if_neg hout]
      split_ifs
      · exact ENNReal.toReal_nonneg
      · exact le_rfl
  exact (hs.tsum_le_tsum hp ht).trans (roundingTail_le width hwidth center cutoff (Nat.cast_nonneg _))

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding

end P2MDyadicModule24

/- Helper module Solutions.RegevBridgeGaussianRoundingTruncation. -/
section P2MDyadicModule25

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding

open AFT GaussianSource AFT.RationalNumerics

open scoped BigOperators Classical

noncomputable section

/-- Exact indexing of the actual integer window around the computed floor. -/
def windowPointEquiv (center : ℚ) (cutoff : ℕ) : Fin (2*cutoff+1) ≃
    ↥(Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
      (centeredGaussianAnchor center+(cutoff : ℤ))) where
  toFun index := ⟨windowPoint center cutoff index,by
    have hi := index.isLt
    simp only [Finset.mem_Icc,windowPoint]
    constructor <;> omega⟩
  invFun point := ⟨(point.val-centeredGaussianAnchor center+(cutoff : ℤ)).toNat,by
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp point.property
    omega⟩
  left_inv index := by
    apply Fin.ext
    change ((windowPoint center cutoff index)-centeredGaussianAnchor center+(cutoff : ℤ)).toNat=index.val
    simp only [windowPoint]
    have hi := index.isLt
    omega
  right_inv point := by
    apply Subtype.ext
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp point.property
    change windowPoint center cutoff ⟨(point.val-centeredGaussianAnchor center+(cutoff : ℤ)).toNat,_⟩=point.val
    simp only [windowPoint]
    omega

theorem windowPoint_sum (center : ℚ) (cutoff : ℕ) (test : ℤ → ℝ) :
    (∑ index : Fin (2*cutoff+1),test (windowPoint center cutoff index))=
      ∑ value ∈ Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
        (centeredGaussianAnchor center+(cutoff : ℤ)),test value := by
  have h := (windowPointEquiv center cutoff).sum_comp (fun point => test point.val)
  rw [Finset.sum_coe_sort] at h
  exact h

/-- Finite-output normalization loses at most twice the discarded mass. -/
theorem normalized_subprobability_l1 {Output : Type*} [Fintype Output]
    (full : FiniteDist Output) (retained : Output → ℝ)
    (hzero : ∀ output,0≤retained output) (hfull : ∀ output,retained output≤full.weight output)
    (hpos : 0<∑ output,retained output) :
    (∑ output,|retained output/(∑ point,retained point)-full.weight output|)≤
      2*(1-∑ output,retained output) := by
  let mass := ∑ output,retained output
  have hmass : mass≤1 := (Finset.sum_le_sum (fun output _ => hfull output)).trans_eq full.sum_one
  have hpoint (output : Output) :
      |retained output/mass-full.weight output|≤
        (retained output/mass-retained output)+(full.weight output-retained output) := by
    have hnorm : retained output≤retained output/mass := by
      apply (le_div_iff₀ hpos).mpr
      exact mul_le_of_le_one_right (hzero output) hmass
    calc
      _ ≤ |retained output/mass-retained output|+|retained output-full.weight output| :=
        abs_sub_le _ (retained output) _
      _ = _ := by rw [abs_of_nonneg (by linarith),abs_of_nonpos (by linarith [hfull output])];ring
  calc
    _ ≤ ∑ output,((retained output/mass-retained output)+(full.weight output-retained output)) :=
      Finset.sum_le_sum (fun output _ => hpoint output)
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib,←Finset.sum_div,
        full.sum_one,div_self (ne_of_gt hpos)]
      ring

/-- Real masses of the genuine countable rounding kernel sum to one. -/
theorem roundingMass_sum (width : ℝ) (hwidth : 0<width) (center : ℝ) :
    (∑' value : ℤ,(roundingPMF width hwidth center value).toReal)=1 := by
  simp_rw [roundingPMF_toReal]
  rw [tsum_div_const]
  exact div_self (theta_pos width center hwidth).ne'

def retainedResidue (q : ℕ) (width : ℝ) (hwidth : 0<width) (center : ℚ) (cutoff : ℕ) (output : ZMod q) : ℝ :=
  ∑ index : Fin (2*cutoff+1),@ite ℝ ((windowPoint center cutoff index : ZMod q)=output)
    (Classical.propDecidable _) (roundingPMF width hwidth center (windowPoint center cutoff index)).toReal 0

theorem retainedResidue_sum (q : ℕ) [NeZero q] (width : ℝ) (hwidth : 0<width) (center : ℚ) (cutoff : ℕ) :
    (∑ output : ZMod q,retainedResidue q width hwidth center cutoff output)=
      ∑ index : Fin (2*cutoff+1),(roundingPMF width hwidth center (windowPoint center cutoff index)).toReal := by
  unfold retainedResidue
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  exact @Fintype.sum_ite_eq (ZMod q) ℝ _ _
    (fun first second => Classical.propDecidable (first=second))
      (windowPoint center cutoff index : ZMod q)
      (fun _ => (roundingPMF width hwidth center (windowPoint center cutoff index)).toReal)

theorem retainedResidue_nonneg (q : ℕ) (width : ℝ) (hwidth : 0<width) (center : ℚ) (cutoff : ℕ)
    (output : ZMod q) : 0≤retainedResidue q width hwidth center cutoff output := by
  unfold retainedResidue
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

theorem retainedResidue_le (q : ℕ) [NeZero q] (width : ℝ) (hwidth : 0<width) (center : ℚ) (cutoff : ℕ)
    (output : ZMod q) : retainedResidue q width hwidth center cutoff output≤
      (modularRounding q width hwidth center).weight output := by
  unfold retainedResidue modularRounding
  rw [Integration.finiteLaw_map_weight]
  have hs : Summable (fun value : ℤ => @ite ℝ ((value : ZMod q)=output) (Classical.propDecidable _)
      (roundingPMF width hwidth center value).toReal 0) := by
    apply Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) _ (summable_roundingMass width hwidth center)
    intro value
    by_cases h : (value : ZMod q)=output
    · rw [if_pos h]
    · rw [if_neg h]
      exact ENNReal.toReal_nonneg
  have he := windowPoint_sum center cutoff (fun value : ℤ => @ite ℝ ((value : ZMod q)=output) (Classical.propDecidable _)
      (roundingPMF width hwidth center value).toReal 0)
  rw [he]
  exact hs.sum_le_tsum _ (fun _ _ => by split_ifs <;> positivity)

theorem retainedResidue_pos (q : ℕ) [NeZero q] (width : ℝ) (hwidth : 0<width) (center : ℚ) (cutoff : ℕ) :
    0<∑ output : ZMod q,retainedResidue q width hwidth center cutoff output := by
  rw [retainedResidue_sum]
  simp_rw [roundingPMF_toReal]
  rw [←Finset.sum_div]
  exact div_pos (windowMass_pos width center cutoff) (theta_pos width center hwidth)

theorem windowLaw_modular_weight (q : ℕ) [NeZero q] (width : ℝ) (hwidth : 0<width)
    (center : ℚ) (cutoff : ℕ) (output : ZMod q) :
    ((windowLaw width center cutoff).map (fun index => (windowPoint center cutoff index : ZMod q))).weight output=
      retainedResidue q width hwidth center cutoff output/(∑ point : ZMod q,retainedResidue q width hwidth center cutoff point) := by
  rw [FiniteDist.map_weight,retainedResidue_sum]
  simp_rw [windowLaw_eq_conditional width hwidth center cutoff]
  unfold retainedResidue
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro index _
  split_ifs <;> simp

/-- The discarded countable mass is exactly one minus the retained finite
mass. This identity retains the true kernel normalization throughout. -/
theorem outsideWindowMass_eq (q : ℕ) [NeZero q] (width : ℝ) (hwidth : 0<width) (center : ℚ) (cutoff : ℕ) :
    outsideWindowMass width hwidth center cutoff=
      1-∑ output : ZMod q,retainedResidue q width hwidth center cutoff output := by
  rw [retainedResidue_sum,windowPoint_sum center cutoff
    (fun value : ℤ => (roundingPMF width hwidth center value).toReal)]
  let window := Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
    (centeredGaussianAnchor center+(cutoff : ℤ))
  let mass := fun value : ℤ => (roundingPMF width hwidth center value).toReal
  have hs := summable_roundingMass width hwidth center
  have hinside : Summable (fun value : ℤ => if value∈window then mass value else 0) := by
    apply Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) _ hs
    intro value
    split_ifs
    · exact le_rfl
    · exact ENNReal.toReal_nonneg
  have houtside : Summable (fun value : ℤ => if value∉window then mass value else 0) := by
    apply Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) _ hs
    intro value
    by_cases h : value∉window
    · rw [if_pos h]
    · rw [if_neg h]
      exact ENNReal.toReal_nonneg
  have he : (∑' value : ℤ,if value∈window then mass value else 0)+
      (∑' value : ℤ,if value∉window then mass value else 0)=1 := by
    rw [←hinside.tsum_add houtside]
    calc
      _ = ∑' value : ℤ,mass value := by
        apply tsum_congr
        intro value
        by_cases h : value∈window <;> simp [h]
      _ = _ := roundingMass_sum width hwidth center
  have hi : (∑' value : ℤ,if value∈window then mass value else 0)=∑ value∈window,mass value := by
    rw [tsum_eq_sum (s := window) (fun value hv => if_neg hv)]
    apply Finset.sum_congr rfl
    intro value hv
    rw [if_pos hv]
  rw [hi] at he
  change (∑' value : ℤ,if value∉window then mass value else 0)=1-∑ value∈window,mass value
  linarith

/-- Conditioning the true infinite kernel to the implemented public window
loses at most twice its actual omitted mass in finite-output L1. -/
theorem windowLaw_modular_l1 (q : ℕ) [NeZero q] (width : ℝ) (hwidth : 0<width)
    (center : ℚ) (cutoff : ℕ) :
    (∑ output : ZMod q,|((windowLaw width center cutoff).map
        (fun index => (windowPoint center cutoff index : ZMod q))).weight output-
      (modularRounding q width hwidth center).weight output|)≤
      2*outsideWindowMass width hwidth center cutoff := by
  simp_rw [windowLaw_modular_weight q width hwidth center cutoff]
  have h := normalized_subprobability_l1 (modularRounding q width hwidth center)
    (retainedResidue q width hwidth center cutoff)
    (retainedResidue_nonneg q width hwidth center cutoff)
    (retainedResidue_le q width hwidth center cutoff)
    (retainedResidue_pos q width hwidth center cutoff)
  rw [←outsideWindowMass_eq q width hwidth center cutoff] at h
  exact h

/-- Complete accuracy of the executed finite-bit modular rounding sampler
relative to its full infinite Gaussian kernel, including the omitted tail. -/
theorem finiteDraw_full_modular_l1 (q : ℕ) [NeZero q] (squaredWidth center : ℚ) (width : ℝ)
    (cutoff bits : ℕ) (hsquared : 0<squaredWidth)
    (hsquare : width^2=(squaredWidth : ℝ)) (hwidth : 1≤width) :
    (∑ output : ZMod q,|((FiniteDist.independent (fun _ : Fin ((bits+1)+(2*cutoff+1)+1) => FiniteDist.uniform (Fin 2))).map
        (fun word => (finiteDraw squaredWidth center cutoff bits word : ZMod q))).weight output-
      (modularRounding q width (zero_lt_one.trans_le hwidth) center).weight output|)≤
      1/(2 : ℝ)^bits+2*tailEnvelope width cutoff := by
  have hb := finiteDraw_modular_l1 q squaredWidth center width cutoff bits hsquared hsquare hwidth
  have ht := windowLaw_modular_l1 q width (zero_lt_one.trans_le hwidth) center cutoff
  have he := mul_le_mul_of_nonneg_left (outsideWindowMass_le width hwidth center cutoff) (by norm_num : (0 : ℝ)≤2)
  have htail := ht.trans he
  apply le_trans _ (add_le_add hb htail)
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro output _
  exact abs_sub_le _ (((windowLaw width center cutoff).map
    (fun index => (windowPoint center cutoff index : ZMod q))).weight output) _

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding

end P2MDyadicModule25

/- Helper module Solutions.RegevBridgeGaussianRoundingContinuous. -/
section P2MDyadicModule26

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency true

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding

open AFT GaussianSource MeasureTheory

open scoped BigOperators Classical

noncomputable section

theorem roundingMass_le_one (width : ℝ) (hwidth : 0<width) (center : ℝ) (value : ℤ) :
    (roundingPMF width hwidth center value).toReal≤1 := by
  have h := ENNReal.toReal_mono (by simp : (1 : ENNReal)≠⊤) (PMF.coe_le_one (roundingPMF width hwidth center) value)
  simpa only [ENNReal.toReal_one] using h

theorem roundingError_lt_half (width : ℝ) (hwidth : 1 ≤ width) : thetaError width<1/2 := by
  have hs : 1 ≤ width^2 := one_le_pow₀ hwidth
  have hp : 3<Real.pi*width^2 := by nlinarith [Real.pi_gt_three]
  have he3 : (8 : ℝ)<Real.exp 3 := by
    have h := Real.exp_one_gt_two
    have he : Real.exp 3=(Real.exp 1)^3 := by rw [←Real.exp_nat_mul];norm_num
    rw [he]
    have he2 : 4<(Real.exp 1)^2 := by nlinarith
    nlinarith [mul_pos (by linarith : 0<Real.exp 1-2) (by linarith : 0<(Real.exp 1)^2-4)]
  have he := he3.trans (Real.exp_lt_exp.mpr hp)
  have hn : Real.exp (-Real.pi*width^2)<1/8 := by
    rw [show -Real.pi*width^2=-(Real.pi*width^2) by ring,Real.exp_neg]
    apply (inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ)<1/8)).2
    simpa using he
  exact (thetaError_le_four_exp width hwidth).trans_lt (by linarith)

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding

end P2MDyadicModule26

/- Helper module Solutions.RegevBridgeGaussianRoundingEquivariance. -/
section P2MDyadicModule27

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding

open AFT GaussianSource AFT.RationalNumerics

open scoped BigOperators Classical

/-- Integer translation leaves the actual rational pi/exponential input
ratio unchanged, even after clearing the center denominator. -/
theorem centeredGaussianApprox_translate (squaredWidth center : ℚ) (shift point : ℤ) (bits : ℕ) :
    centeredGaussianApprox squaredWidth (center+shift) (point+shift) bits=
      centeredGaussianApprox squaredWidth center point bits := by
  have hr : gaussianRatio (centeredGaussianSquaredWidth squaredWidth (center+shift))
      (centeredGaussianNumerator (center+shift) (point+shift))=
      gaussianRatio (centeredGaussianSquaredWidth squaredWidth center)
        (centeredGaussianNumerator center point) := by
    have hreal : (gaussianRatio (centeredGaussianSquaredWidth squaredWidth (center+shift))
        (centeredGaussianNumerator (center+shift) (point+shift)) : ℝ)=
        (gaussianRatio (centeredGaussianSquaredWidth squaredWidth center)
          (centeredGaussianNumerator center point) : ℝ) := by
      rw [centeredGaussianRatio,centeredGaussianRatio]
      push_cast
      ring
    exact_mod_cast hreal
  unfold centeredGaussianApprox gaussianApprox gaussianGuard
  rw [hr]

theorem windowPoint_translate (center : ℚ) (shift : ℤ) (cutoff : ℕ) (index : Fin (2*cutoff+1)) :
    windowPoint (center+shift) cutoff index=windowPoint center cutoff index+shift := by
  unfold windowPoint centeredGaussianAnchor
  rw [Int.floor_add_intCast]
  ring

theorem rawTable_translate (squaredWidth center : ℚ) (shift : ℤ) (cutoff bits : ℕ)
    (index : Fin (2*cutoff+1)) :
    rawTable squaredWidth (center+shift) cutoff bits index=rawTable squaredWidth center cutoff bits index := by
  unfold rawTable
  rw [windowPoint_translate,centeredGaussianApprox_translate]

/-- The same exact random tape chooses the same palette index after every
integer translation. No approximate distribution comparison is used. -/
theorem finiteDrawIndex_translate (squaredWidth center : ℚ) (shift : ℤ) (cutoff bits : ℕ)
    (word : Fin ((bits+1)+(2*cutoff+1)+1) → Fin 2) :
    finiteDrawIndex squaredWidth (center+shift) cutoff bits word=
      finiteDrawIndex squaredWidth center cutoff bits word := by
  have hr : rawTable squaredWidth (center+shift) cutoff (roundingPrecision cutoff (bits+1))=
      rawTable squaredWidth center cutoff (roundingPrecision cutoff (bits+1)) := by
    funext index
    exact rawTable_translate squaredWidth center shift cutoff _ index
  unfold finiteDrawIndex drawIndex
  rw [hr]

/-- Exact pathwise translation equivariance of the executed bounded-tape
rounding program, including the floor anchor and numerical normalization. -/
theorem finiteDraw_translate (squaredWidth center : ℚ) (shift : ℤ) (cutoff bits : ℕ)
    (word : Fin ((bits+1)+(2*cutoff+1)+1) → Fin 2) :
    finiteDraw squaredWidth (center+shift) cutoff bits word=
      finiteDraw squaredWidth center cutoff bits word+shift := by
  unfold finiteDraw
  rw [finiteDrawIndex_translate,windowPoint_translate]

end InfoLossLAR.WorstCase.GaussianRandomizedRounding

end P2MDyadicModule27

/- Helper module Solutions.RegevBridgeGaussianRoundingBinary. -/
section P2MDyadicModule28

set_option autoImplicit false

set_option maxRecDepth 2048

set_option maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding

open AFT GaussianSource RationalNumerics BinaryArithmetic

open BinaryArithmetic.RationalBits BetaReference

open scoped BigOperators

theorem binaryAnchor_value (center : RationalBits) :
    (binaryAnchor center).data.decode=(centeredGaussianAnchor center.decode : ℚ) := by
  cases hs : center.negative with
  | false =>
    have hn : 0 ≤ center.decode := by
      rw [decode_fraction]
      simp only [signedValue,hs,ite_false,Bool.false_eq_true,Int.cast_natCast]
      positivity
    simp only [binaryAnchor,hs,ite_false,Bool.false_eq_true,ofNat_value,floorNatural_value]
    rw [←Int.cast_natCast,Int.natCast_floor_eq_floor hn]
    rfl
  | true =>
    have hn : center.decode ≤ 0 := by
      rw [decode_fraction]
      simp only [signedValue,hs,ite_true,Int.cast_neg,Int.cast_natCast]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)
    simp only [binaryAnchor,hs,ite_true,ofInt_value,signedValue,ceilNatural_value,negate_value]
    rw [Int.natCast_ceil_eq_ceil (neg_nonneg.mpr hn),Int.ceil_neg,neg_neg]
    rfl

theorem binaryRoundingPoint_ratio (squaredWidth center : RationalBits) (cutoff index : ℕ) :
    (quotient
      (multiply
        (add (add (binaryAnchor center).data (ofUnaryInteger (integerDifference index cutoff).value).data).data (negate center).data).data
        (add (add (binaryAnchor center).data (ofUnaryInteger (integerDifference index cutoff).value).data).data (negate center).data).data).data
      squaredWidth).data.decode=
      gaussianRatio (centeredGaussianSquaredWidth squaredWidth.decode center.decode)
        (centeredGaussianNumerator center.decode (centeredGaussianAnchor center.decode+(index : ℤ)-(cutoff : ℤ))) := by
  simp only [quotient_value,RationalBits.multiply_value,RationalBits.add_value,binaryAnchor_value,ofUnaryInteger_value,
    integerDifference_value,negate_value]
  rw [centeredGaussianRatio_rat]
  push_cast
  ring

theorem binaryRoundingPoint_value (squaredWidth center : RationalBits) (cutoff precision index : ℕ) :
    (binaryRoundingPoint squaredWidth center cutoff precision index).data.decode=
      centeredGaussianApprox squaredWidth.decode center.decode
        (centeredGaussianAnchor center.decode+(index : ℤ)-(cutoff : ℤ)) precision := by
  simp only [binaryRoundingPoint,gaussianFromRatio_value,binaryRoundingPoint_ratio,
    centeredGaussianApprox,gaussianApprox,gaussianGuard]

theorem binaryRoundingRaw_value (squaredWidth center : RationalBits) (cutoff bits : ℕ) (index : Fin (2*cutoff+1)) :
    ((binaryRoundingRaw squaredWidth center cutoff bits).data.get index).decode=
      rawTable squaredWidth.decode center.decode cutoff (roundingPrecision cutoff (bits+1)) index := by
  simp only [binaryRoundingRaw,Vector.get_cast,buildArray_get,binaryRoundingPoint_value,
    Fin.val_cast,addCounter_value,doubleCounter_value,rawTable,roundingPrecision,windowPoint]

theorem binaryRoundingDrawIndex_value (squaredWidth center : RationalBits) (cutoff bits : ℕ)
    (word : Fin ((bits+1)+(2*cutoff+1)+1) → Fin 2) :
    (binaryRoundingDrawIndex squaredWidth center cutoff bits word).value=
      (finiteDrawIndex squaredWidth.decode center.decode cutoff bits word).val := by
  simp only [binaryRoundingDrawIndex,binaryPositiveDraw_value]
  have he : (fun index => ((binaryRoundingRaw squaredWidth center cutoff bits).data.get index).decode)=
      rawTable squaredWidth.decode center.decode cutoff (roundingPrecision cutoff (bits+1)) :=
    funext (binaryRoundingRaw_value squaredWidth center cutoff bits)
  rw [he]
  rfl

noncomputable section

open Polynomial

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding

end P2MDyadicModule28

/- Helper module Integration9_9.TM2NativeFiniteDraw. -/
section P2MDyadicModule29

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option synthInstance.maxSize 1024

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.TM2NativeFiniteDraw

open AFT AFT.RationalNumerics AFT.BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2NativeFiniteSeries TM2NativeRootGroupProfiles

open scoped BigOperators

theorem tape_ofFn (bits : ℕ) (word : Fin bits → Fin 2) :
    List.ofFn (fun i => digitBoolean (word i))=(readBitTape bits word).digits := by
  induction bits with
  | zero => rfl
  | succ bits ih =>
    simp only [List.ofFn_succ,readBitTape,ih]
    rfl

theorem bucket_eq (counts : List ℕ) (ticket : ℕ) : bucket (counts,ticket)=FiniteTicketSampler.bucket counts ticket := by
  induction counts generalizing ticket with
  | nil => rfl
  | cons head tail ih =>
    simp only [bucket,List.length_cons,List.range_succ_eq_map,List.findIdx_cons,List.take_succ_cons,List.take_zero,List.sum_cons,List.sum_nil,Nat.add_zero]
    by_cases h : ticket<head
    · simp only [h,decide_true,Bool.cond_true,FiniteTicketSampler.bucket,ite_true]
    · simp only [h,decide_false,Bool.cond_false,List.findIdx_map,Function.comp_def,FiniteTicketSampler.bucket,ite_false]
      have he : (fun i => decide (ticket<head+(tail.take (i+1)).sum))=
          (fun i => decide (ticket-head<(tail.take (i+1)).sum)) := by
        funext i
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        omega
      simp only [he]
      change bucket (tail,ticket-head)+1=1+FiniteTicketSampler.bucket tail (ticket-head)
      rw [ih,Nat.add_comm]

end Integration9_9.TM2NativeFiniteDraw

end P2MDyadicModule29

/- Helper module Integration9_9.TM2NativeTicketDraw. -/
section P2MDyadicModule30

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option synthInstance.maxSize 1024

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.TM2NativeTicketDraw

open AFT AFT.RationalNumerics AFT.BinaryArithmetic CurrentAFT

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2NativeFiniteDraw TM2NativeFiniteSeries

open scoped BigOperators

theorem supplement_eq (extra : ℕ) (xs : List ℕ) : supplement (extra,xs)=supplementFirst extra xs := by cases xs <;> rfl

theorem ticketTable_native (weights : List RationalBits) (ticks : List Unit)
    (hb : (weights.map (fun q => ⌊(2 : ℚ)^ticks.length*q.decode⌋₊)).sum≤2^ticks.length) :
    ticketTable (weights.map RationalBits.decode,ticks)=(BinaryArithmetic.ticketTable weights ticks.length).data.map value := by
  rw [BinaryArithmetic.ticketTable_value weights ticks.length hb]
  simp only [ticketTable,supplement_eq,floorTable,dyadicFloor,dyadicPower,natSum,List.map_map,Function.comp_def]

theorem current_native {count : ℕ} (weights : Vector RationalBits (count+1))
    (hn : ∀ i,0≤(weights.get i).decode) (hm : ∑i,(weights.get i).decode=1)
    (bits : ℕ) (word : Fin bits → Fin 2) :
    current (List.ofFn (fun i => (weights.get i).decode),List.ofFn (fun i => digitBoolean (word i)))=
      (binaryRationalDraw weights bits word).value := by
  have hb := RationalFiniteQuantization.floorTotal_le (fun i => (weights.get i).decode) hn hm (2^bits)
  simp only [RationalFiniteQuantization.floorTotal,RationalFiniteQuantization.floorCount,Nat.cast_pow,Nat.cast_ofNat] at hb
  have ht : ticketTable (List.ofFn (fun i => (weights.get i).decode),TM2NativeFiniteDraw.ticks (List.ofFn (fun i => digitBoolean (word i))))=
      (BinaryArithmetic.ticketTable (List.ofFn weights.get) bits).data.map value := by
    have hl : (TM2NativeFiniteDraw.ticks (List.ofFn (fun i => digitBoolean (word i)))).length=bits := by simp [TM2NativeFiniteDraw.ticks]
    have hh := ticketTable_native (List.ofFn weights.get) (TM2NativeFiniteDraw.ticks (List.ofFn (fun i => digitBoolean (word i))))
      (by simpa only [hl,List.map_ofFn,List.sum_ofFn,Function.comp_def] using hb)
    simpa only [hl,List.map_ofFn,Function.comp_def] using hh
  rw [current,ht,bucket_eq]
  simp only [binaryRationalDraw,binaryBucket_value,tapeValue,tape_ofFn]

end Integration9_9.TM2NativeTicketDraw

end P2MDyadicModule30

/- Helper module Integration9_9.TM2NativePositiveDraw. -/
section P2MDyadicModule31

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option synthInstance.maxSize 1024

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.TM2NativePositiveDraw

open AFT AFT.RationalNumerics AFT.BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2NativeRootGroupProfiles

open scoped BigOperators

theorem positive_eq (q : ℚ) : positive q=max 0 q := by
  by_cases h : q<0
  · simp only [positive,h,ite_true,max_eq_left h.le]
  · simp only [positive,h,ite_false,max_eq_right (le_of_not_gt h)]

theorem normalize_value {count : ℕ} (raw : Fin (count+1) → ℚ) :
    normalize (List.ofFn raw)=List.ofFn (positiveWeightProgram raw) := by
  have ht : total (List.ofFn raw)=positiveNormalizerProgram raw := by
    simp only [total,clipped,List.map_ofFn,List.sum_ofFn,positive_eq,positiveNormalizerProgram,positivePartProgram,Function.comp_def]
  simp only [normalize,ht]
  by_cases h : positiveNormalizerProgram raw=0
  · simp only [h,ite_true,List.length_ofFn]
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
      change (if i=0 then (1 : ℚ) else 0)=positiveWeightProgram raw ⟨i,by simpa using hj⟩
      simp only [positiveWeightProgram,h,ite_true,Fin.ext_iff,Fin.val_zero]
  · simp only [h,ite_false,clipped,List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    simp only [positiveWeightProgram,h,ite_false,positivePartProgram,positive_eq,Function.comp_def]

theorem normalize_native {count : ℕ} (raw : Vector RationalBits (count+1)) :
    normalize (List.ofFn (fun i => (raw.get i).decode))=
      List.ofFn (fun i => ((RationalBits.binaryPositiveNormalize raw).data.get i).decode) := by
  rw [normalize_value]
  simp only [RationalBits.binaryPositiveNormalize_value]

theorem current_native {count : ℕ} (raw : Vector RationalBits (count+1)) (bits : ℕ)
    (word : Fin (bits+(count+1)+1) → Fin 2) :
    current (List.ofFn (fun i => (raw.get i).decode),List.ofFn (fun i => digitBoolean (word i)))=
      (binaryPositiveDraw raw bits word).value := by
  rw [current,normalize_native]
  have hn (i) : 0≤((RationalBits.binaryPositiveNormalize raw).data.get i).decode := by
    rw [RationalBits.binaryPositiveNormalize_value]
    exact positiveWeightProgram_nonneg _ i
  have hm : ∑i,((RationalBits.binaryPositiveNormalize raw).data.get i).decode=1 := by
    simpa only [RationalBits.binaryPositiveNormalize_value] using positiveWeightProgram_sum (fun i => (raw.get i).decode)
  rw [TM2NativeTicketDraw.current_native _ hn hm]
  simp only [binaryPositiveDraw,binaryRationalDraw_cast,addCounter_value]

end Integration9_9.TM2NativePositiveDraw

end P2MDyadicModule31

/- Helper module Solutions.RegevBridgeGaussianRoundingNative. -/
section P2MDyadicModule32

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option synthInstance.maxSize 1024

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Native

open AFT GaussianSource RationalNumerics BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 TM2NativeFiniteSeries TM2NativeGaussian

open scoped BigOperators

attribute [local irreducible] expSum arctanSum expNegScaled expNegApprox piApprox
  gaussianApprox centeredGaussianApprox

theorem anchor_eq (center : ℚ) : anchor center=(centeredGaussianAnchor center : ℚ) := by
  unfold anchor
  split <;> rename_i hc
  · have hn := Int.natCast_ceil_eq_ceil (neg_nonneg.mpr hc.le)
    rw [←Int.cast_natCast,hn,Int.ceil_neg,Int.cast_neg,neg_neg]
    rfl
  · rw [←Int.cast_natCast,Int.natCast_floor_eq_floor (le_of_not_gt hc)]
    rfl

theorem indexTicks_length (input : Request) :
    (indexTicks input).length=2*(cutoffTicks input).length+1 := by
  simp only [indexTicks,List.length_append,List.length_singleton]
  omega

theorem precisionTicks_length (input : Request) :
    (precisionTicks input).length=roundingPrecision (cutoffTicks input).length (input.1.2.2.length+1) := by
  simp only [precisionTicks,List.length_append,List.length_singleton,List.length_replicate,
    indexTicks_length,roundingPrecision]

theorem ratioTicks_length (input : Request) :
    (ratioTicks input).length=((cutoffTicks input).length+1)^2 := by
  simp only [ratioTicks,List.length_flatMap,List.length_append,List.length_singleton,
    List.map_const',List.sum_replicate]
  ring

theorem widthSquared_ge_one (input : Request) : 1 ≤ widthSquared input := by
  unfold widthSquared
  split
  · assumption
  · exact le_rfl

theorem ratio_eq (input : Request) (index : Fin (2*(cutoffTicks input).length+1)) :
    ratio (input,index.val)=gaussianRatio
      (centeredGaussianSquaredWidth (widthSquared input) input.1.1.2)
      (centeredGaussianNumerator input.1.1.2 (windowPoint input.1.1.2 (cutoffTicks input).length index)) := by
  rw [centeredGaussianRatio_rat]
  simp only [ratio,anchor_eq,windowPoint,Int.cast_add,Int.cast_sub,Int.cast_natCast]
  ring

theorem pointValue_eq (input : Request) (index : Fin (2*(cutoffTicks input).length+1)) :
    pointValue (input,index.val)=rawTable (widthSquared input) input.1.1.2 (cutoffTicks input).length
      (roundingPrecision (cutoffTicks input).length (input.1.2.2.length+1)) index := by
  have hr := centeredWindowRatio_bounds (widthSquared input) input.1.1.2 (cutoffTicks input).length
    (widthSquared_ge_one input) (FiniteConvolutionProgram.windowIndexEquiv (cutoffTicks input).length index)
  have he : centeredGaussianAnchor input.1.1.2+
      (FiniteConvolutionProgram.windowIndexEquiv (cutoffTicks input).length index : ℤ)=
      windowPoint input.1.1.2 (cutoffTicks input).length index := by
    simp only [FiniteConvolutionProgram.windowIndexEquiv,Equiv.coe_fn_mk,windowPoint]
    ring
  rw [he,←ratio_eq] at hr
  have hb : ratio (input,index.val) ≤ ((ratioTicks input).length : ℚ) := by
    rw [ratioTicks_length]
    exact_mod_cast hr.2
  unfold pointValue
  rw [gaussianCapped_eq ((ratio (input,index.val),precisionTicks input),ratioTicks input) hr.1 hb,
    ratio_eq,precisionTicks_length]
  simp only [rawTable,centeredGaussianApprox,gaussianApprox,gaussianGuard]

theorem raw_eq (input : Request) : raw input=List.ofFn
    (fun index : Fin (2*(cutoffTicks input).length+1) => rawTable (widthSquared input) input.1.1.2
      (cutoffTicks input).length (roundingPrecision (cutoffTicks input).length (input.1.2.2.length+1)) index) := by
  apply List.ext_getElem
  · simp only [raw,List.length_map,List.length_range,List.length_ofFn,indexTicks_length]
  · intro index hfirst hsecond
    simp only [raw,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact pointValue_eq input ⟨index,by simpa only [List.length_ofFn] using hsecond⟩

theorem selected_typed (squaredWidth center : RationalBits) (cutoff bits : ℕ)
    (hwidth : 1 ≤ squaredWidth.decode) (word : Fin ((bits+1)+(2*cutoff+1)+1) → Fin 2) :
    selected (typedRequest squaredWidth center cutoff bits word)=
      (finiteDrawIndex squaredWidth.decode center.decode cutoff bits word).val := by
  have hraw : raw (typedRequest squaredWidth center cutoff bits word)=
      List.ofFn (fun index => ((binaryRoundingRaw squaredWidth center cutoff bits).data.get index).decode) := by
    rw [raw_eq]
    simp only [widthSquared,typedRequest,cutoffTicks,List.length_replicate,if_pos hwidth]
    apply congrArg List.ofFn
    funext index
    simpa only [rawTable,windowPoint,Fin.val_cast,List.length_replicate] using
      (binaryRoundingRaw_value squaredWidth center cutoff bits index).symm
  rw [selected,hraw]
  change TM2NativePositiveDraw.current
    (List.ofFn (fun index => ((binaryRoundingRaw squaredWidth center cutoff bits).data.get index).decode),
      List.ofFn (fun index => digitBoolean (word index)))=_
  rw [TM2NativePositiveDraw.current_native]
  exact binaryRoundingDrawIndex_value squaredWidth center cutoff bits word

theorem current_typed (squaredWidth center : RationalBits) (cutoff bits : ℕ)
    (hwidth : 1 ≤ squaredWidth.decode) (word : Fin ((bits+1)+(2*cutoff+1)+1) → Fin 2) :
    current (typedRequest squaredWidth center cutoff bits word)=
      (finiteDraw squaredWidth.decode center.decode cutoff bits word : ℚ) := by
  rw [current,selected_typed squaredWidth center cutoff bits hwidth word]
  simp only [typedRequest,cutoffTicks,List.length_replicate,anchor_eq,finiteDraw,windowPoint]
  push_cast
  ring

/-- Exact native program output on every valid numerical input and every
coin tape. The polynomial certificate itself accepts all Request values. -/
theorem output_typed (squaredWidth center : RationalBits) (cutoff bits : ℕ)
    (hwidth : 1 ≤ squaredWidth.decode) (word : Fin ((bits+1)+(2*cutoff+1)+1) → Fin 2) :
    output (typedRequest squaredWidth center cutoff bits word)=
      finiteDraw squaredWidth.decode center.decode cutoff bits word := by
  rw [output,current_typed squaredWidth center cutoff bits hwidth word,Rat.num_intCast]

/-- Code existence is used solely in this semantic proof; the running
native program receives ordinary encoded rational inputs. -/
theorem output_numerical (squaredWidth center : ℚ) (cutoff bits : ℕ)
    (hwidth : 1 ≤ squaredWidth) (word : Fin ((bits+1)+(2*cutoff+1)+1) → Fin 2) :
    output (numericalRequest squaredWidth center cutoff bits word)=
      finiteDraw squaredWidth center cutoff bits word := by
  obtain ⟨widthCode,hwidthCode⟩ := RationalBits.exists_code squaredWidth
  obtain ⟨centerCode,hcenterCode⟩ := RationalBits.exists_code center
  have h := output_typed widthCode centerCode cutoff bits (by simpa only [hwidthCode] using hwidth) word
  simpa only [typedRequest,numericalRequest,hwidthCode,hcenterCode] using h

/-- Every sample of the native program has the previously proved full
Gaussian-kernel error, including its infinite omitted tail. -/
theorem output_modular_l1 (q : ℕ) [NeZero q] (squaredWidth center : ℚ) (width : ℝ) (cutoff bits : ℕ)
    (hwidthSquared : 1 ≤ squaredWidth) (hsquare : width^2=(squaredWidth : ℝ)) (hwidth : 1 ≤ width) :
    (∑ result : ZMod q, |((FiniteDist.independent (fun _ : Fin ((bits+1)+(2*cutoff+1)+1) => FiniteDist.uniform (Fin 2))).map
      (fun word => (output (numericalRequest squaredWidth center cutoff bits word) : ZMod q))).weight result-
      (modularRounding q width (zero_lt_one.trans_le hwidth) center).weight result|) ≤
        1/(2 : ℝ)^bits+2*tailEnvelope width cutoff := by
  simp_rw [output_numerical squaredWidth center cutoff bits hwidthSquared]
  exact finiteDraw_full_modular_l1 q squaredWidth center width cutoff bits (zero_lt_one.trans_le hwidthSquared) hsquare hwidth

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Native

end P2MDyadicModule32

/- Helper module Solutions.RegevBridgeGaussianProjectionQuadratic. -/
section P2MDyadicModule33

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open AFT GaussianSource

open scoped BigOperators

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

/-- The scalar variance parameter after projecting a lattice Gaussian of
width R and applying the integer-rounding kernel of width w. -/
def projectedSquaredWidth (latticeWidth kernelWidth : ℝ) (direction : Space) : ℝ :=
  kernelWidth^2+latticeWidth^2*‖direction‖^2

/-- The actual rank-one precision quadratic in the lattice variable. -/
def projectionPrecision (latticeWidth kernelWidth : ℝ) (direction value : Space) : ℝ :=
  ‖value‖^2/latticeWidth^2+(inner ℝ direction value)^2/kernelWidth^2

def projectionCenter (latticeWidth kernelWidth : ℝ) (direction : Space) (output : ℝ) : Space :=
  (latticeWidth^2*output/projectedSquaredWidth latticeWidth kernelWidth direction) • direction

omit [InnerProductSpace ℝ Space] in
theorem projectedSquaredWidth_pos (latticeWidth kernelWidth : ℝ) (direction : Space)
    (hkernel : 0<kernelWidth) : 0<projectedSquaredWidth latticeWidth kernelWidth direction := by
  unfold projectedSquaredWidth
  positivity

/-- Rank-one completion of the square for the literal scalar projection.
Unlike a continuous integral estimate, this identity holds at every output,
so it applies in particular at the integer outputs of the rounding kernel. -/
theorem projection_complete_square (latticeWidth kernelWidth : ℝ) (direction value : Space) (output : ℝ)
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) :
    ‖value‖^2/latticeWidth^2+(output-inner ℝ direction value)^2/kernelWidth^2=
      output^2/projectedSquaredWidth latticeWidth kernelWidth direction+
        projectionPrecision latticeWidth kernelWidth direction
          (value-projectionCenter latticeWidth kernelWidth direction output) := by
  have ht := projectedSquaredWidth_pos latticeWidth kernelWidth direction hkernel
  have hnorm (scale : ℝ) : ‖value-scale • direction‖^2=
      ‖value‖^2-2*scale*inner ℝ direction value+scale^2*‖direction‖^2 := by
    rw [norm_sub_sq_real,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,real_inner_smul_right,real_inner_comm value direction]
    ring
  unfold projectionPrecision projectionCenter
  rw [hnorm,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
  unfold projectedSquaredWidth at ht ⊢
  field_simp [hlattice.ne',hkernel.ne',ht.ne']
  ring

/-- The precision is positive and bounded above by its smallest isotropic
smoothing scale. This is the comparison needed before a lattice Poisson
bound can be applied; no lattice mass conclusion is assumed here. -/
theorem projectionPrecision_bounds (latticeWidth kernelWidth : ℝ) (direction value : Space)
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) :
    ‖value‖^2/latticeWidth^2 ≤ projectionPrecision latticeWidth kernelWidth direction value ∧
      projectionPrecision latticeWidth kernelWidth direction value ≤
        (projectedSquaredWidth latticeWidth kernelWidth direction/(latticeWidth^2*kernelWidth^2))*‖value‖^2 := by
  have hinner : (inner ℝ direction value)^2 ≤ ‖direction‖^2*‖value‖^2 := by
    simpa only [real_inner_self_eq_norm_sq,pow_two] using real_inner_mul_inner_self_le direction value
  constructor
  · unfold projectionPrecision
    exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (sq_pos_of_pos hkernel).le)
  · unfold projectionPrecision projectedSquaredWidth
    have h := div_le_div_of_nonneg_right hinner (sq_pos_of_pos hkernel).le
    calc
      _ ≤ ‖value‖^2/latticeWidth^2+(‖direction‖^2*‖value‖^2)/kernelWidth^2 := add_le_add le_rfl h
      _ = _ := by field_simp

/-- Exact pointwise numerator factorization for the integer-output
rounding kernel, with output variance R²‖e‖²+w². -/
theorem projection_weight_factorization (latticeWidth kernelWidth : ℝ) (direction value : Space) (output : ℤ)
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) :
    Real.exp (-Real.pi*‖value‖^2/latticeWidth^2)*
      shiftedWeight kernelWidth (inner ℝ direction value) output=
      weight (Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)) output*
        Real.exp (-Real.pi*projectionPrecision latticeWidth kernelWidth direction
          (value-projectionCenter latticeWidth kernelWidth direction output)) := by
  have ht := projectedSquaredWidth_pos latticeWidth kernelWidth direction hkernel
  unfold shiftedWeight weight
  rw [Real.sq_sqrt ht.le,←Real.exp_add,←Real.exp_add]
  apply congrArg Real.exp
  have he := projection_complete_square latticeWidth kernelWidth direction value (output : ℝ) hlattice hkernel
  have he' := congrArg (fun scalar : ℝ => -Real.pi*scalar) he
  convert he' using 1 <;> ring

/-- Summing the literal factorization over any countable lattice index
leaves a translated rank-one Gaussian mass. No integral-distance estimate
is evaluated at integer points. -/
theorem projection_weight_tsum {Index : Type*} (points : Index → Space)
    (latticeWidth kernelWidth : ℝ) (direction : Space) (output : ℤ)
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) :
    (∑' index,Real.exp (-Real.pi*‖points index‖^2/latticeWidth^2)*
      shiftedWeight kernelWidth (inner ℝ direction (points index)) output)=
      weight (Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)) output*
        ∑' index,Real.exp (-Real.pi*projectionPrecision latticeWidth kernelWidth direction
          (points index-projectionCenter latticeWidth kernelWidth direction output)) := by
  simp_rw [projection_weight_factorization latticeWidth kernelWidth direction _ output hlattice hkernel]
  exact tsum_mul_left

/-- The minimal isotropic squared width controlling the ellipsoidal
rank-one mass is R²w²/(w²+R²‖e‖²). -/
def projectionEffectiveSquaredWidth (latticeWidth kernelWidth : ℝ) (direction : Space) : ℝ :=
  latticeWidth^2*kernelWidth^2/projectedSquaredWidth latticeWidth kernelWidth direction

omit [InnerProductSpace ℝ Space] in
theorem projectionEffectiveSquaredWidth_pos (latticeWidth kernelWidth : ℝ) (direction : Space)
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) :
    0<projectionEffectiveSquaredWidth latticeWidth kernelWidth direction :=
  div_pos (mul_pos (sq_pos_of_pos hlattice) (sq_pos_of_pos hkernel))
    (projectedSquaredWidth_pos latticeWidth kernelWidth direction hkernel)

omit [InnerProductSpace ℝ Space] in
theorem projectionEffectiveSquaredWidth_le (latticeWidth kernelWidth : ℝ) (direction : Space)
    (hkernel : 0<kernelWidth) :
    projectionEffectiveSquaredWidth latticeWidth kernelWidth direction ≤ latticeWidth^2 := by
  apply (div_le_iff₀ (projectedSquaredWidth_pos latticeWidth kernelWidth direction hkernel)).mpr
  unfold projectedSquaredWidth
  nlinarith [mul_nonneg (sq_nonneg latticeWidth) (sq_nonneg ‖direction‖),sq_nonneg latticeWidth]

end

end InfoLossLAR.WorstCase.GaussianProjection

end P2MDyadicModule33

/- Helper module Solutions.RegevBridgeGaussianProjectionTransform. -/
section P2MDyadicModule34

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 400000

namespace InfoLossLAR.WorstCase.GaussianProjection

open scoped BigOperators

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

def projectionTransform (latticeWidth kernelWidth : ℝ) (direction : Space) : Space →L[ℝ] Space :=
  (1/latticeWidth) • ContinuousLinearMap.id ℝ Space+
    (latticeWidth/(kernelWidth*(Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)+kernelWidth))) •
      (innerSL ℝ direction).smulRight direction

def projectionInverse (latticeWidth kernelWidth : ℝ) (direction : Space) : Space →L[ℝ] Space :=
  latticeWidth • ContinuousLinearMap.id ℝ Space-
    (latticeWidth^3/(Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)*
      (Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)+kernelWidth))) •
      (innerSL ℝ direction).smulRight direction

theorem projectionTransform_apply (latticeWidth kernelWidth : ℝ) (direction value : Space) :
    projectionTransform latticeWidth kernelWidth direction value=
      (1/latticeWidth) • value+
        (latticeWidth/(kernelWidth*(Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)+kernelWidth))*
          inner ℝ direction value) • direction := by
  simp only [projectionTransform,add_apply,smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,smul_smul]
  rfl

theorem projectionInverse_apply (latticeWidth kernelWidth : ℝ) (direction value : Space) :
    projectionInverse latticeWidth kernelWidth direction value=
      latticeWidth • value-
        (latticeWidth^3/(Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)*
          (Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)+kernelWidth))*inner ℝ direction value) • direction := by
  simp only [projectionInverse,sub_apply,smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,smul_smul]
  rfl

/-- Explicit square root of the rank-one precision form. -/
theorem projectionTransform_norm_sq (latticeWidth kernelWidth : ℝ) (direction value : Space)
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) :
    ‖projectionTransform latticeWidth kernelWidth direction value‖^2=
      projectionPrecision latticeWidth kernelWidth direction value := by
  let total := Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)
  let coefficient := latticeWidth/(kernelWidth*(total+kernelWidth))
  have ht : 0<total := Real.sqrt_pos.mpr (projectedSquaredWidth_pos latticeWidth kernelWidth direction hkernel)
  have htotal : total^2=kernelWidth^2+latticeWidth^2*‖direction‖^2 :=
    Real.sq_sqrt (projectedSquaredWidth_pos latticeWidth kernelWidth direction hkernel).le
  have hsum : total+kernelWidth≠0 := (add_pos ht hkernel).ne'
  have hc : 2*(1/latticeWidth)*coefficient+coefficient^2*‖direction‖^2=1/kernelWidth^2 := by
    dsimp only [coefficient]
    field_simp [hlattice.ne',hkernel.ne',hsum]
    nlinarith [htotal]
  rw [projectionTransform_apply]
  change ‖(1/latticeWidth) • value+(coefficient*inner ℝ direction value) • direction‖^2=_
  rw [norm_add_sq_real,norm_smul,norm_smul,mul_pow,mul_pow,Real.norm_eq_abs,Real.norm_eq_abs,sq_abs,sq_abs,
    real_inner_smul_left,real_inner_smul_right,real_inner_comm direction value]
  calc
    _ = ‖value‖^2/latticeWidth^2+
        (2*(1/latticeWidth)*coefficient+coefficient^2*‖direction‖^2)*(inner ℝ direction value)^2 := by ring
    _ = _ := by rw [hc];unfold projectionPrecision;ring

omit [InnerProductSpace ℝ Space] in
private theorem inverse_coefficient (latticeWidth kernelWidth : ℝ) (direction : Space)
    (_hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) :
    let total := Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)
    let forward := latticeWidth/(kernelWidth*(total+kernelWidth))
    let backward := latticeWidth^3/(total*(total+kernelWidth))
    forward*latticeWidth-backward/latticeWidth-forward*backward*‖direction‖^2=0 := by
  dsimp only
  have ht := Real.sqrt_pos.mpr (projectedSquaredWidth_pos latticeWidth kernelWidth direction hkernel)
  have hs : Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)+kernelWidth≠0 := (add_pos ht hkernel).ne'
  have htotal := Real.sq_sqrt (projectedSquaredWidth_pos latticeWidth kernelWidth direction hkernel).le
  unfold projectedSquaredWidth at htotal
  field_simp [_hlattice.ne',hkernel.ne',ht.ne',hs]
  unfold projectedSquaredWidth
  have hh := congrArg (fun scalar : ℝ => latticeWidth^2*scalar) htotal
  nlinarith [hh]

/-- The inverse is explicit and includes the zero-direction case. -/
theorem projectionTransform_inverse (latticeWidth kernelWidth : ℝ) (direction value : Space)
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) :
    projectionTransform latticeWidth kernelWidth direction (projectionInverse latticeWidth kernelWidth direction value)=value := by
  let total := Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)
  let forward := latticeWidth/(kernelWidth*(total+kernelWidth))
  let backward := latticeWidth^3/(total*(total+kernelWidth))
  have hc := inverse_coefficient latticeWidth kernelWidth direction hlattice hkernel
  change forward*latticeWidth-backward/latticeWidth-forward*backward*‖direction‖^2=0 at hc
  rw [projectionTransform_apply,projectionInverse_apply]
  simp only [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
  calc
    _ = ((1/latticeWidth)*latticeWidth) • value+
        ((forward*latticeWidth-backward/latticeWidth-forward*backward*‖direction‖^2)*inner ℝ direction value) • direction := by
      dsimp [forward,backward,total]
      module
    _ = value := by rw [hc,one_div_mul_cancel hlattice.ne'];simp

theorem projectionInverse_transform (latticeWidth kernelWidth : ℝ) (direction value : Space)
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) :
    projectionInverse latticeWidth kernelWidth direction (projectionTransform latticeWidth kernelWidth direction value)=value := by
  let total := Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)
  let forward := latticeWidth/(kernelWidth*(total+kernelWidth))
  let backward := latticeWidth^3/(total*(total+kernelWidth))
  have hc := inverse_coefficient latticeWidth kernelWidth direction hlattice hkernel
  change forward*latticeWidth-backward/latticeWidth-forward*backward*‖direction‖^2=0 at hc
  rw [projectionInverse_apply,projectionTransform_apply]
  simp only [inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
  calc
    _ = (latticeWidth*(1/latticeWidth)) • value+
        ((forward*latticeWidth-backward/latticeWidth-forward*backward*‖direction‖^2)*inner ℝ direction value) • direction := by
      dsimp [forward,backward,total]
      module
    _ = value := by rw [hc,mul_one_div_cancel hlattice.ne'];simp

/-- A genuine continuous linear equivalence, not an assumed change of
variables or a record of an unimplemented Gaussian algorithm. -/
def projectionEquiv (latticeWidth kernelWidth : ℝ) (direction : Space)
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) : Space ≃L[ℝ] Space where
  toFun := projectionTransform latticeWidth kernelWidth direction
  invFun := projectionInverse latticeWidth kernelWidth direction
  left_inv := fun value => projectionInverse_transform latticeWidth kernelWidth direction value hlattice hkernel
  right_inv := fun value => projectionTransform_inverse latticeWidth kernelWidth direction value hlattice hkernel
  map_add' := (projectionTransform latticeWidth kernelWidth direction).map_add
  map_smul' := (projectionTransform latticeWidth kernelWidth direction).map_smul
  continuous_toFun := (projectionTransform latticeWidth kernelWidth direction).continuous
  continuous_invFun := (projectionInverse latticeWidth kernelWidth direction).continuous

theorem projectionTransform_symmetric (latticeWidth kernelWidth : ℝ) (direction first second : Space) :
    inner ℝ (projectionTransform latticeWidth kernelWidth direction first) second=
      inner ℝ first (projectionTransform latticeWidth kernelWidth direction second) := by
  rw [projectionTransform_apply,projectionTransform_apply]
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
    real_inner_comm direction first]
  ring

/-- Inverse norm comparison needed for bounding the actual nonzero dual
Gaussian sum of the transformed lattice by the original smoothing sum. -/
theorem projectionInverse_norm_bounds (latticeWidth kernelWidth : ℝ) (direction value : Space)
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) :
    projectionEffectiveSquaredWidth latticeWidth kernelWidth direction*‖value‖^2 ≤
        ‖projectionInverse latticeWidth kernelWidth direction value‖^2 ∧
      ‖projectionInverse latticeWidth kernelWidth direction value‖^2 ≤ latticeWidth^2*‖value‖^2 := by
  have hp := projectionPrecision_bounds latticeWidth kernelWidth direction
    (projectionInverse latticeWidth kernelWidth direction value) hlattice hkernel
  rw [←projectionTransform_norm_sq latticeWidth kernelWidth direction _ hlattice hkernel,
    projectionTransform_inverse latticeWidth kernelWidth direction value hlattice hkernel] at hp
  have he := projectionEffectiveSquaredWidth_pos latticeWidth kernelWidth direction hlattice hkernel
  have ht := projectedSquaredWidth_pos latticeWidth kernelWidth direction hkernel
  constructor
  · have hm := mul_le_mul_of_nonneg_left hp.2 he.le
    apply hm.trans_eq
    unfold projectionEffectiveSquaredWidth
    field_simp
  · have h := (div_le_iff₀ (sq_pos_of_pos hlattice)).mp hp.1
    simpa only [mul_comm] using h

end

end InfoLossLAR.WorstCase.GaussianProjection

end P2MDyadicModule34

/- Helper module Solutions.RegevBridgeGaussianLatticeTransport. -/
section P2MDyadicModule35

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.GaussianLatticeTransport

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ}

instance image_discrete (lattice : Submodule ℤ (Space (dimension := dimension)))
    [DiscreteTopology lattice]
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension)) :
    DiscreteTopology (imageLattice lattice transform) := by
  unfold imageLattice
  infer_instance

instance image_full_rank (lattice : Submodule ℤ (Space (dimension := dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension)) :
    IsZLattice ℝ (imageLattice lattice transform) := by
  unfold imageLattice
  infer_instance

/-- Self-adjointness transports dual membership through the forward map. -/
theorem mem_dual_image_iff (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (selfAdjoint : ∀ first second, inner ℝ (transform first) second =
      inner ℝ first (transform second)) (value : Space (dimension := dimension)) :
    value ∈ dual (imageLattice lattice transform) ↔ transform value ∈ dual lattice := by
  change (∀ test ∈ imageLattice lattice transform,
    inner ℝ value test ∈ (1 : Submodule ℤ ℝ)) ↔
    ∀ test ∈ lattice, inner ℝ (transform value) test ∈ (1 : Submodule ℤ ℝ)
  constructor
  · intro membership test test_mem
    rw [selfAdjoint]
    apply membership
    simpa using test_mem
  · intro membership test test_mem
    have h := membership (transform.symm test) test_mem
    rw [selfAdjoint, transform.apply_symm_apply] at h
    exact h

/-- The dual of the image is parametrized by the inverse map on the old dual. -/
def dualEquiv (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (selfAdjoint : ∀ first second, inner ℝ (transform first) second =
      inner ℝ first (transform second)) :
    dual lattice ≃ dual (imageLattice lattice transform) where
  toFun value := ⟨transform.symm value,
    (mem_dual_image_iff lattice transform selfAdjoint _).mpr (by simpa using value.property)⟩
  invFun value := ⟨transform value,
    (mem_dual_image_iff lattice transform selfAdjoint _).mp value.property⟩
  left_inv value := by ext; simp
  right_inv value := by ext; simp

@[simp] theorem dualEquiv_eq_zero_iff (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (selfAdjoint : ∀ first second, inner ℝ (transform first) second =
      inner ℝ first (transform second)) (value : dual lattice) :
    dualEquiv lattice transform selfAdjoint value = 0 ↔ value = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    have h' := congrArg (fun z : dual (imageLattice lattice transform) =>
      transform (z : Space (dimension := dimension))) h
    change transform (transform.symm (value : Space (dimension := dimension))) =
      transform (0 : Space (dimension := dimension)) at h'
    change (value : Space (dimension := dimension)) = 0
    simpa only [transform.apply_symm_apply, map_zero] using h'
  · rintro rfl
    apply Subtype.ext
    change transform.symm (0 : Space (dimension := dimension)) = 0
    exact map_zero _

def dualNonzeroEquiv (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (selfAdjoint : ∀ first second, inner ℝ (transform first) second =
      inner ℝ first (transform second)) :
    {value : dual lattice // value ≠ 0} ≃
      {value : dual (imageLattice lattice transform) // value ≠ 0} :=
  (dualEquiv lattice transform selfAdjoint).subtypeEquiv (by
    intro value
    exact not_congr (dualEquiv_eq_zero_iff lattice transform selfAdjoint value).symm)

/-- Exact reindexing of the entire nonzero-dual Gaussian sum. -/
theorem rhoDualNonzero_image (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (selfAdjoint : ∀ first second, inner ℝ (transform first) second =
      inner ℝ first (transform second)) (width : ℝ) :
    rhoDualNonzero width (imageLattice lattice transform) =
      ∑' value : {value : dual lattice // value ≠ 0},
        rho width (transform.symm ((value : dual lattice) : Space (dimension := dimension))) := by
  unfold rhoDualNonzero
  symm
  have reindex := (dualNonzeroEquiv lattice transform selfAdjoint).tsum_eq
    (fun value : {value : dual (imageLattice lattice transform) // value ≠ 0} =>
      rho width ((value.val : dual (imageLattice lattice transform)) : Space (dimension := dimension)))
  exact reindex

/-- The image parametrization also preserves the literal lattice variable. -/
def latticeEquiv (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension)) :
    lattice ≃ₗ[ℤ] imageLattice lattice transform :=
  ZLattice.comap_equiv ℝ lattice transform.symm.toLinearEquiv

/-- Exact primal-coset reindexing, before any Gaussian approximation. -/
theorem rhoCoset_image (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (width : ℝ) (shift : Space (dimension := dimension)) :
    rhoCoset width (imageLattice lattice transform) (transform shift) =
      ∑' value : lattice, rho width (transform ((value : Space (dimension := dimension)) + shift)) := by
  unfold rhoCoset
  have reindex := (latticeEquiv lattice transform).toEquiv.tsum_eq
    (fun value : imageLattice lattice transform =>
      rho width ((value : Space (dimension := dimension)) + transform shift))
  change (∑' value : lattice, rho width
    (transform (value : Space (dimension := dimension)) + transform shift)) = _ at reindex
  simpa only [map_add] using reindex.symm

end

end InfoLossLAR.WorstCase.GaussianLatticeTransport

end P2MDyadicModule35

/- Helper module Solutions.RegevBridgeGaussianProjectionSmoothing. -/
section P2MDyadicModule36

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open RegevLWE.GaussConv

noncomputable section

open scoped BigOperators

def projectionEffectiveWidth {Space : Type*} [NormedAddCommGroup Space]
    (latticeWidth kernelWidth : ℝ) (direction : Space) : ℝ :=
  Real.sqrt (projectionEffectiveSquaredWidth latticeWidth kernelWidth direction)

theorem projectionEffectiveWidth_pos {Space : Type*} [NormedAddCommGroup Space]
    (latticeWidth kernelWidth : ℝ) (direction : Space) (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) :
    0<projectionEffectiveWidth latticeWidth kernelWidth direction :=
  Real.sqrt_pos.mpr (projectionEffectiveSquaredWidth_pos latticeWidth kernelWidth direction hlattice hkernel)

theorem projectionEffectiveWidth_sq {Space : Type*} [NormedAddCommGroup Space]
    (latticeWidth kernelWidth : ℝ) (direction : Space) (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) :
    (projectionEffectiveWidth latticeWidth kernelWidth direction)^2=
      projectionEffectiveSquaredWidth latticeWidth kernelWidth direction :=
  Real.sq_sqrt (projectionEffectiveSquaredWidth_pos latticeWidth kernelWidth direction hlattice hkernel).le

/-- Actual dual Gaussian comparison induced by the explicit rank-one
inverse, before any lattice or probability-law abstraction is introduced. -/
theorem projectionInverse_rho_le {dimension : ℕ} (latticeWidth kernelWidth scale : ℝ)
    (direction value : EuclideanSpace ℝ (Fin dimension))
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) (hscale : 0<scale) :
    rho scale (projectionInverse latticeWidth kernelWidth direction value) ≤
      rho (scale/projectionEffectiveWidth latticeWidth kernelWidth direction) value := by
  have he := projectionEffectiveWidth_pos latticeWidth kernelWidth direction hlattice hkernel
  have hbound := (projectionInverse_norm_bounds latticeWidth kernelWidth direction value hlattice hkernel).1
  have hsq := projectionEffectiveWidth_sq latticeWidth kernelWidth direction hlattice hkernel
  unfold rho
  apply Real.exp_le_exp.mpr
  rw [div_pow]
  have heq : -Real.pi*‖value‖^2/(scale^2/(projectionEffectiveWidth latticeWidth kernelWidth direction)^2)=
      -Real.pi*(projectionEffectiveSquaredWidth latticeWidth kernelWidth direction*‖value‖^2)/scale^2 := by
    rw [←hsq]
    field_simp
  rw [heq]
  apply div_le_div_of_nonneg_right _ (sq_pos_of_pos hscale).le
  exact mul_le_mul_of_nonpos_left hbound (neg_nonpos.mpr Real.pi_pos.le)

/-- A usable public version of the smoothing-threshold consequence. The
zero-dimensional case is discharged, and the positive-dimensional case
uses the recovered, proved exact characterization of smoothingParam. -/
theorem dual_mass_le_of_smoothing {dimension : ℕ}
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    {error width : ℝ} (herror : 0<error) (hwidth : 0<width) (hsmoothing : smoothingParam lattice error ≤ width) :
    rhoDualNonzero (1/width) lattice ≤ error := by
  rcases Nat.eq_zero_or_pos dimension with rfl | hdimension
  · have : Subsingleton (EuclideanSpace ℝ (Fin 0)) := inferInstance
    have : IsEmpty {value : dual lattice // value≠0} :=
      ⟨fun value => value.property (Subsingleton.elim value.val 0)⟩
    unfold rhoDualNonzero
    simp [herror.le]
  · obtain ⟨_,hantitone,_,_,hthreshold⟩ := RegevLWE.GaussConv.smoothing_remark hdimension lattice
    obtain ⟨hpositive,hequal⟩ := hthreshold error herror
    rw [←hequal]
    exact hantitone.antitoneOn hpositive hwidth hsmoothing

/-- The effective width is exactly Rw/√(w²+R²‖e‖²), with positive
widths fixing the square-root branch. -/
theorem projectionEffectiveWidth_eq {Space : Type*} [NormedAddCommGroup Space]
    (latticeWidth kernelWidth : ℝ) (direction : Space) (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) :
    projectionEffectiveWidth latticeWidth kernelWidth direction=
      latticeWidth*kernelWidth/Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction) := by
  apply (sq_eq_sq₀ (projectionEffectiveWidth_pos latticeWidth kernelWidth direction hlattice hkernel).le
    (by positivity : 0 ≤ latticeWidth*kernelWidth/Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction))).mp
  rw [projectionEffectiveWidth_sq latticeWidth kernelWidth direction hlattice hkernel,div_pow,mul_pow,
    Real.sq_sqrt (projectedSquaredWidth_pos latticeWidth kernelWidth direction hkernel).le]
  rfl

/-- Increasing the positive Gaussian width increases every actual mass. -/
theorem rho_width_mono {dimension : ℕ} {first second : ℝ} (hfirst : 0<first) (hsecond : first ≤ second)
    (value : EuclideanSpace ℝ (Fin dimension)) : rho first value ≤ rho second value := by
  have hs : 0<second := hfirst.trans_le hsecond
  unfold rho
  apply Real.exp_le_exp.mpr
  have h := div_le_div_of_nonneg_left (mul_nonneg Real.pi_pos.le (sq_nonneg ‖value‖))
    (sq_pos_of_pos hfirst) ((sq_le_sq₀ hfirst.le hs.le).mpr hsecond)
  simpa only [neg_div,neg_mul] using neg_le_neg h

/-- Summability of the actual nonzero-dual Gaussian, with all premises
discharged by the proved smoothing characterization, including dim 0. -/
theorem summable_dual_of_smoothing {dimension : ℕ}
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    {error width : ℝ} (herror : 0<error) (hwidth : 0<width) (hsmoothing : smoothingParam lattice error ≤ width) :
    Summable (fun value : {value : dual lattice // value≠0} => rho (1/width) (value : EuclideanSpace ℝ (Fin dimension))) := by
  rcases Nat.eq_zero_or_pos dimension with rfl | hdimension
  · have : Subsingleton (EuclideanSpace ℝ (Fin 0)) := inferInstance
    have : IsEmpty {value : dual lattice // value≠0} :=
      ⟨fun value => value.property (Subsingleton.elim value.val 0)⟩
    have : Fintype {value : dual lattice // value≠0} := Fintype.ofIsEmpty
    exact HasSum.summable (hasSum_fintype _)
  · obtain ⟨_,_,_,_,hthreshold⟩ := RegevLWE.GaussConv.smoothing_remark hdimension lattice
    obtain ⟨hpositive,hequal⟩ := hthreshold error herror
    have hs : Summable (fun value : {value : dual lattice // value≠0} =>
        rho (1/smoothingParam lattice error) (value : EuclideanSpace ℝ (Fin dimension))) := by
      by_contra hnonsummable
      have hzero := tsum_eq_zero_of_not_summable hnonsummable
      change rhoDualNonzero (1/smoothingParam lattice error) lattice=0 at hzero
      rw [hequal] at hzero
      exact herror.ne' hzero
    apply Summable.of_nonneg_of_le (fun value => Real.exp_nonneg _) _ hs
    intro value
    apply rho_width_mono (div_pos zero_lt_one hwidth)
    exact one_div_le_one_div_of_le hpositive hsmoothing

/-- The entire nonzero-dual Gaussian of the actual transformed lattice
is controlled by the original smoothing threshold at the effective width. -/
theorem projection_dual_mass_le {dimension : ℕ}
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (latticeWidth kernelWidth error : ℝ) (direction : EuclideanSpace ℝ (Fin dimension))
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) (herror : 0<error)
    (hsmoothing : smoothingParam lattice error ≤ projectionEffectiveWidth latticeWidth kernelWidth direction) :
    rhoDualNonzero 1 (GaussianLatticeTransport.imageLattice lattice
      (projectionEquiv latticeWidth kernelWidth direction hlattice hkernel)) ≤ error := by
  let transform := projectionEquiv latticeWidth kernelWidth direction hlattice hkernel
  have hself : ∀ first second,inner ℝ (transform first) second=inner ℝ first (transform second) :=
    projectionTransform_symmetric latticeWidth kernelWidth direction
  rw [GaussianLatticeTransport.rhoDualNonzero_image lattice transform hself]
  have hsum := summable_dual_of_smoothing lattice herror
    (projectionEffectiveWidth_pos latticeWidth kernelWidth direction hlattice hkernel) hsmoothing
  have hpoint (value : {value : dual lattice // value≠0}) :
      rho 1 (transform.symm (value : EuclideanSpace ℝ (Fin dimension))) ≤
        rho (1/projectionEffectiveWidth latticeWidth kernelWidth direction) (value : EuclideanSpace ℝ (Fin dimension)) :=
    projectionInverse_rho_le latticeWidth kernelWidth 1 direction _ hlattice hkernel zero_lt_one
  have htransformed := Summable.of_nonneg_of_le (fun value => Real.exp_nonneg _) hpoint hsum
  exact (htransformed.tsum_le_tsum hpoint hsum).trans
    (dual_mass_le_of_smoothing lattice herror
      (projectionEffectiveWidth_pos latticeWidth kernelWidth direction hlattice hkernel) hsmoothing)

/-- Actual anisotropic smoothing is derived from the original lattice,
not supplied as an extra oracle or a hypothesis on a missing decoder. -/
theorem projection_smoothing_le_one {dimension : ℕ}
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (latticeWidth kernelWidth error : ℝ) (direction : EuclideanSpace ℝ (Fin dimension))
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) (herror : 0<error)
    (hsmoothing : smoothingParam lattice error ≤ projectionEffectiveWidth latticeWidth kernelWidth direction) :
    smoothingParam (GaussianLatticeTransport.imageLattice lattice
      (projectionEquiv latticeWidth kernelWidth direction hlattice hkernel)) error ≤ 1 := by
  unfold smoothingParam
  apply csInf_le
  · exact ⟨0,fun width membership => membership.1.le⟩
  · refine ⟨zero_lt_one,?_⟩
    simpa only [div_one] using projection_dual_mass_le lattice latticeWidth kernelWidth error direction hlattice hkernel herror hsmoothing

/-- Uniform translation mass of the genuine rank-one image lattice,
proved by the recovered Poisson theorem after concrete dual smoothing. -/
theorem projection_shift_mass_bound {dimension : ℕ}
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (latticeWidth kernelWidth error : ℝ) (direction shift : EuclideanSpace ℝ (Fin dimension))
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) (herror : 0<error)
    (hsmoothing : smoothingParam lattice error ≤ projectionEffectiveWidth latticeWidth kernelWidth direction) :
    let image := GaussianLatticeTransport.imageLattice lattice
      (projectionEquiv latticeWidth kernelWidth direction hlattice hkernel)
    |rhoCoset 1 image shift-(ZLattice.covolume image)⁻¹| ≤ error*(ZLattice.covolume image)⁻¹ := by
  have h := RegevLWE.GaussConv.claim_3_8
    (GaussianLatticeTransport.imageLattice lattice (projectionEquiv latticeWidth kernelWidth direction hlattice hkernel)) shift
    herror zero_lt_one (projection_smoothing_le_one lattice latticeWidth kernelWidth error direction hlattice hkernel herror hsmoothing)
  simpa only [one_pow,one_mul] using h

end

end InfoLossLAR.WorstCase.GaussianProjection

end P2MDyadicModule36

/- Helper module Solutions.RegevBridgeGaussianLatticeScaling. -/
section P2MDyadicModule37

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open RegevLWE.GaussConv GaussianLatticeTransport

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

theorem dilation_apply (factor : ℝ) (hfactor : 0<factor) (value : ScalingSpace (dimension:=dimension)) :
    dilation factor hfactor value=factor • value := rfl

theorem dilation_symmetric (factor : ℝ) (hfactor : 0<factor) (first second : ScalingSpace (dimension:=dimension)) :
    inner ℝ (dilation factor hfactor first) second=inner ℝ first (dilation factor hfactor second) := by
  rw [dilation_apply,dilation_apply,real_inner_smul_left,real_inner_smul_right]

theorem rho_dilation_inverse (factor width : ℝ) (hfactor : 0<factor) (hwidth : 0<width)
    (value : ScalingSpace (dimension:=dimension)) :
    rho width ((dilation factor hfactor).symm value)=rho (factor*width) value := by
  unfold rho
  rw [dilation_symm_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hfactor)]
  congr 1
  field_simp [hfactor.ne',hwidth.ne']

theorem rhoDualNonzero_dilation (lattice : Submodule ℤ (ScalingSpace (dimension:=dimension)))
    (factor width : ℝ) (hfactor : 0<factor) (hwidth : 0<width) :
    rhoDualNonzero width (GaussianLatticeTransport.imageLattice lattice (dilation factor hfactor))=
      rhoDualNonzero (factor*width) lattice := by
  rw [rhoDualNonzero_image lattice (dilation factor hfactor) (dilation_symmetric factor hfactor)]
  simp_rw [rho_dilation_inverse factor width hfactor hwidth]
  rfl

/-- A proved smoothing upper bound under actual lattice dilation.
Only the source smoothing condition is required. -/
theorem dilation_smoothing_le
    (lattice : Submodule ℤ (ScalingSpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (factor width error : ℝ) (hfactor : 0<factor) (hwidth : 0<width) (herror : 0<error)
    (hsmoothing : smoothingParam lattice error ≤ width) :
    smoothingParam (GaussianLatticeTransport.imageLattice lattice (dilation factor hfactor)) error ≤ factor*width := by
  have hm : rhoDualNonzero (1/(factor*width)) (GaussianLatticeTransport.imageLattice lattice (dilation factor hfactor)) ≤ error := by
    rw [rhoDualNonzero_dilation lattice factor (1/(factor*width)) hfactor (by positivity)]
    have he : factor*(1/(factor*width))=1/width := by field_simp
    rw [he]
    exact dual_mass_le_of_smoothing lattice herror hwidth hsmoothing
  unfold smoothingParam
  apply csInf_le
  · exact ⟨0,fun value membership => membership.1.le⟩
  · exact ⟨mul_pos hfactor hwidth,hm⟩

/-- The exact qL smoothing condition needed in the coset-conditioned
BDD sample experiment follows from the original lattice bound. -/
theorem dilation_bdd_smoothing
    (lattice : Submodule ℤ (ScalingSpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (factor latticeWidth error : ℝ) (hfactor : 0<factor) (hlattice : 0<latticeWidth) (herror : 0<error)
    (hsmoothing : smoothingParam lattice error ≤ latticeWidth/(Real.sqrt 2*factor)) :
    smoothingParam (GaussianLatticeTransport.imageLattice lattice (dilation factor hfactor)) error ≤ latticeWidth/Real.sqrt 2 := by
  have hw : 0<latticeWidth/(Real.sqrt 2*factor) := by positivity
  have h := dilation_smoothing_le lattice factor (latticeWidth/(Real.sqrt 2*factor)) error hfactor hw herror hsmoothing
  have he : factor*(latticeWidth/(Real.sqrt 2*factor))=latticeWidth/Real.sqrt 2 := by field_simp
  rwa [he] at h

end

end InfoLossLAR.WorstCase.GaussianProjection

end P2MDyadicModule37

/- Helper module Solutions.RegevBridgeGaussianProjectionProbability. -/
section P2MDyadicModule38

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open AFT GaussianSource RegevLWE.GaussConv

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

abbrev ProbabilitySpace := EuclideanSpace ℝ (Fin dimension)

/-- Positive coset normalizer from the actual Poisson mass bound. -/
theorem rhoCoset_pos_of_smoothing
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift : ProbabilitySpace (dimension:=dimension)) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width) :
    0<rhoCoset width lattice shift := by
  have h := (abs_le.mp (claim_3_8 lattice shift herror hwidth hsmoothing)).1
  have hp : 0<width^dimension*(ZLattice.covolume lattice)⁻¹ :=
    mul_pos (pow_pos hwidth _) (inv_pos.mpr (ZLattice.covolume_pos lattice))
  nlinarith

theorem summable_coset_of_smoothing
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift : ProbabilitySpace (dimension:=dimension)) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width) :
    Summable (fun value : lattice => rho width ((value : ProbabilitySpace (dimension:=dimension))+shift)) := by
  by_contra hnonsummable
  have hzero := tsum_eq_zero_of_not_summable hnonsummable
  have hpos := rhoCoset_pos_of_smoothing lattice shift hwidth herror herrorOne hsmoothing
  exact hpos.ne' hzero

/-- The genuine discrete Gaussian masses on the actual lattice coset. -/
def cosetMass (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension)))
    (shift : ProbabilitySpace (dimension:=dimension)) (width : ℝ) (value : lattice) : ℝ :=
  discreteGaussian lattice shift width ((value : ProbabilitySpace (dimension:=dimension))+shift)

theorem cosetMass_formula (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension)))
    (shift : ProbabilitySpace (dimension:=dimension)) (width : ℝ) (value : lattice) :
    cosetMass lattice shift width value=
      rho width ((value : ProbabilitySpace (dimension:=dimension))+shift)/rhoCoset width lattice shift := by
  unfold cosetMass discreteGaussian
  rw [Set.indicator_of_mem]
  simpa only [Set.mem_ofPred_eq,add_sub_cancel_right] using value.property

theorem cosetMass_nonneg
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift : ProbabilitySpace (dimension:=dimension)) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width)
    (value : lattice) : 0 ≤ cosetMass lattice shift width value := by
  rw [cosetMass_formula]
  exact div_nonneg (Real.exp_nonneg _) (rhoCoset_pos_of_smoothing lattice shift hwidth herror herrorOne hsmoothing).le

theorem cosetMass_summable
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift : ProbabilitySpace (dimension:=dimension)) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width) :
    Summable (cosetMass lattice shift width) := by
  simp_rw [funext (cosetMass_formula lattice shift width)]
  exact (summable_coset_of_smoothing lattice shift hwidth herror herrorOne hsmoothing).div_const _

theorem cosetMass_sum
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift : ProbabilitySpace (dimension:=dimension)) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width) :
    (∑' value : lattice,cosetMass lattice shift width value)=1 := by
  simp_rw [cosetMass_formula]
  rw [tsum_div_const]
  exact div_self (rhoCoset_pos_of_smoothing lattice shift hwidth herror herrorOne hsmoothing).ne'

/-- Literal PMF of the input lattice-Gaussian sample law. This does not
assert the existence of an efficient DGS sampler. -/
def cosetPMF
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift : ProbabilitySpace (dimension:=dimension)) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width) : PMF lattice :=
  ⟨fun value => ENNReal.ofReal (cosetMass lattice shift width value),by
    apply ENNReal.summable.hasSum_iff.mpr
    rw [←ENNReal.ofReal_tsum_of_nonneg (cosetMass_nonneg lattice shift hwidth herror herrorOne hsmoothing)
      (cosetMass_summable lattice shift hwidth herror herrorOne hsmoothing),
      cosetMass_sum lattice shift hwidth herror herrorOne hsmoothing,ENNReal.ofReal_one]⟩

theorem cosetPMF_toReal
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift : ProbabilitySpace (dimension:=dimension)) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width)
    (value : lattice) :
    (cosetPMF lattice shift hwidth herror herrorOne hsmoothing value).toReal=cosetMass lattice shift width value :=
  ENNReal.toReal_ofReal (cosetMass_nonneg lattice shift hwidth herror herrorOne hsmoothing value)

/-- Normalization of the real masses of any literal countable PMF. -/
theorem pmf_realMass_sum {State : Type*} (law : PMF State) :
    (∑' value : State,(law value).toReal)=1 := by
  rw [←ENNReal.tsum_toReal_eq (fun value => law.apply_ne_top value),law.tsum_coe,ENNReal.toReal_one]

theorem pmf_realMass_summable {State : Type*} (law : PMF State) :
    Summable (fun value : State => (law value).toReal) := by
  by_contra hnonsummable
  have hzero := tsum_eq_zero_of_not_summable hnonsummable
  rw [pmf_realMass_sum] at hzero
  norm_num at hzero

/-- The literal mixed integer-output law from a genuine lattice Gaussian
sample followed by the actual normalized shifted-integer Gaussian kernel.
This defines the law of a supplied sample, not a DGS sampling algorithm. -/
def projectedPMF
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift direction : ProbabilitySpace (dimension:=dimension)) {latticeWidth kernelWidth error : ℝ}
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) (herror : 0<error) (herrorOne : error<1)
    (hsmoothing : smoothingParam lattice error ≤ latticeWidth) : PMF ℤ :=
  (cosetPMF lattice shift hlattice herror herrorOne hsmoothing).bind
    (fun value => GaussianRandomizedRounding.roundingPMF kernelWidth hkernel
      (inner ℝ direction ((value : ProbabilitySpace (dimension:=dimension))+shift)))

theorem projectedPMF_toReal
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift direction : ProbabilitySpace (dimension:=dimension)) {latticeWidth kernelWidth error : ℝ}
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) (herror : 0<error) (herrorOne : error<1)
    (hsmoothing : smoothingParam lattice error ≤ latticeWidth) (output : ℤ) :
    (projectedPMF lattice shift direction hlattice hkernel herror herrorOne hsmoothing output).toReal=
      ∑' value : lattice,cosetMass lattice shift latticeWidth value*
        (GaussianRandomizedRounding.roundingPMF kernelWidth hkernel
          (inner ℝ direction ((value : ProbabilitySpace (dimension:=dimension))+shift)) output).toReal := by
  rw [projectedPMF,PMF.bind_apply,ENNReal.tsum_toReal_eq]
  · simp only [ENNReal.toReal_mul,cosetPMF_toReal]
  · intro value
    exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)

/-- Uniform control of the kernel denominator is kept separate from the
lattice Poisson estimate until both have been applied to the actual law. -/
theorem multiplicative_sandwich_error (actual reference numeratorError denominatorError : ℝ)
    (href : 0 ≤ reference) (hnumerator : 0 ≤ numeratorError) (hdenominator : 0 ≤ denominatorError)
    (hsmall : denominatorError<1)
    (hlower : (1-numeratorError)*reference ≤ (1+denominatorError)*actual)
    (hupper : (1-denominatorError)*actual ≤ (1+numeratorError)*reference) :
    |actual-reference| ≤ ((numeratorError+denominatorError)/(1-denominatorError))*reference := by
  have hden : 0<1-denominatorError := sub_pos.mpr hsmall
  have hu : (actual-reference)*(1-denominatorError) ≤ (numeratorError+denominatorError)*reference := by nlinarith
  have hl : -((numeratorError+denominatorError)*reference) ≤ (actual-reference)*(1-denominatorError) := by
    by_cases hdiff : reference ≤ actual
    · have hp := mul_nonneg (sub_nonneg.mpr hdiff) hden.le
      have he := mul_nonneg (add_nonneg hnumerator hdenominator) href
      linarith
    · have hp := mul_nonneg hdenominator (sub_nonneg.mpr (le_of_not_ge hdiff))
      nlinarith
  have h := abs_le.mpr ⟨hl,hu⟩
  rw [abs_mul,abs_of_pos hden] at h
  have h' := (le_div_iff₀ hden).mpr h
  simpa only [mul_div_right_comm] using h'

end

end InfoLossLAR.WorstCase.GaussianProjection

end P2MDyadicModule38

/- Helper module Solutions.RegevBridgeGaussianProjectionLaw. -/
section P2MDyadicModule39

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open AFT GaussianSource RegevLWE.GaussConv

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

abbrev ProjectionSpace := EuclideanSpace ℝ (Fin dimension)

/-- The original-coordinate ellipsoidal Gaussian mass has the same
uniform relative shift bound as the actual image-lattice mass. -/
theorem projection_ellipsoid_mass_bound
    (lattice : Submodule ℤ (ProjectionSpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (latticeWidth kernelWidth error : ℝ) (direction shift : ProjectionSpace (dimension:=dimension))
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) (herror : 0<error)
    (hsmoothing : smoothingParam lattice error ≤ projectionEffectiveWidth latticeWidth kernelWidth direction) :
    let image := GaussianLatticeTransport.imageLattice lattice
      (projectionEquiv latticeWidth kernelWidth direction hlattice hkernel)
    |(∑' value : lattice,Real.exp (-Real.pi*projectionPrecision latticeWidth kernelWidth direction
      ((value : ProjectionSpace (dimension:=dimension))+shift)))-(ZLattice.covolume image)⁻¹| ≤
        error*(ZLattice.covolume image)⁻¹ := by
  let transform := projectionEquiv latticeWidth kernelWidth direction hlattice hkernel
  have h := projection_shift_mass_bound lattice latticeWidth kernelWidth error direction (transform shift)
    hlattice hkernel herror hsmoothing
  dsimp only at h
  rw [GaussianLatticeTransport.rhoCoset_image lattice transform 1 shift] at h
  have he (value : ProjectionSpace (dimension:=dimension)) : rho 1 (transform value)=
      Real.exp (-Real.pi*projectionPrecision latticeWidth kernelWidth direction value) := by
    unfold rho
    rw [one_pow,div_one]
    have hn : ‖transform value‖^2=projectionPrecision latticeWidth kernelWidth direction value :=
      projectionTransform_norm_sq latticeWidth kernelWidth direction value hlattice hkernel
    rw [hn]
  simp_rw [he] at h
  exact h

/-- The literal scalar-output numerator after drawing the lattice
Gaussian and applying the shifted-integer Gaussian kernel. -/
def projectedNumerator
    (lattice : Submodule ℤ (ProjectionSpace (dimension:=dimension)))
    (shift direction : ProjectionSpace (dimension:=dimension)) (latticeWidth kernelWidth : ℝ) (output : ℤ) : ℝ :=
  ∑' value : lattice,Real.exp (-Real.pi*‖(value : ProjectionSpace (dimension:=dimension))+shift‖^2/latticeWidth^2)*
    shiftedWeight kernelWidth (inner ℝ direction ((value : ProjectionSpace (dimension:=dimension))+shift)) output

/-- True pointwise scalar projection estimate at every integer output.
The common covolume scale is explicit and will be removed only after
proving normalization of the actual mixed probability law. -/
theorem projectedNumerator_relative_error
    (lattice : Submodule ℤ (ProjectionSpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (latticeWidth kernelWidth error : ℝ) (direction shift : ProjectionSpace (dimension:=dimension))
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) (herror : 0<error)
    (hsmoothing : smoothingParam lattice error ≤ projectionEffectiveWidth latticeWidth kernelWidth direction)
    (output : ℤ) :
    let image := GaussianLatticeTransport.imageLattice lattice
      (projectionEquiv latticeWidth kernelWidth direction hlattice hkernel)
    |projectedNumerator lattice shift direction latticeWidth kernelWidth output-
      (ZLattice.covolume image)⁻¹*weight (Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)) output| ≤
        error*(ZLattice.covolume image)⁻¹*
          weight (Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)) output := by
  let center := projectionCenter latticeWidth kernelWidth direction (output : ℝ)
  have hmass := projection_ellipsoid_mass_bound lattice latticeWidth kernelWidth error direction (shift-center)
    hlattice hkernel herror hsmoothing
  have he := projection_weight_tsum (fun value : lattice => (value : ProjectionSpace (dimension:=dimension))+shift)
    latticeWidth kernelWidth direction output hlattice hkernel
  have hshift (value : lattice) :
      ((value : ProjectionSpace (dimension:=dimension))+shift)-center=
        (value : ProjectionSpace (dimension:=dimension))+(shift-center) := add_sub_assoc _ _ _
  change projectedNumerator lattice shift direction latticeWidth kernelWidth output=_ at he
  simp_rw [show projectionCenter latticeWidth kernelWidth direction (output : ℝ)=center from rfl,hshift] at he
  rw [he]
  let gaussian := weight (Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)) output
  have hg : 0 ≤ gaussian := (weight_pos _ _).le
  calc
    _ = gaussian*|(∑' value : lattice,Real.exp (-Real.pi*projectionPrecision latticeWidth kernelWidth direction
        ((value : ProjectionSpace (dimension:=dimension))+(shift-center))))-
        (ZLattice.covolume (GaussianLatticeTransport.imageLattice lattice
          (projectionEquiv latticeWidth kernelWidth direction hlattice hkernel)))⁻¹| := by
      change |gaussian*_-_*gaussian|=_
      rw [mul_comm _ gaussian,←mul_sub,abs_mul,abs_of_nonneg hg]
    _ ≤ gaussian*(error*(ZLattice.covolume (GaussianLatticeTransport.imageLattice lattice
          (projectionEquiv latticeWidth kernelWidth direction hlattice hkernel)))⁻¹) :=
      mul_le_mul_of_nonneg_left hmass hg
    _ = _ := by ring

end

end InfoLossLAR.WorstCase.GaussianProjection

end P2MDyadicModule39

/- Helper module Solutions.RegevBridgeGaussianProjectionMixture. -/
section P2MDyadicModule40

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open AFT GaussianSource RegevLWE.GaussConv GaussianRandomizedRounding

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

abbrev MixtureSpace := EuclideanSpace ℝ (Fin dimension)

/-- The effective smoothing width never exceeds the source width. -/
theorem projectionEffectiveWidth_le (latticeWidth kernelWidth : ℝ) (direction : MixtureSpace (dimension:=dimension))
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth) :
    projectionEffectiveWidth latticeWidth kernelWidth direction ≤ latticeWidth := by
  calc
    _ ≤ Real.sqrt (latticeWidth^2) := Real.sqrt_le_sqrt
      (projectionEffectiveSquaredWidth_le latticeWidth kernelWidth direction hkernel)
    _ = _ := Real.sqrt_sq hlattice.le

/-- The theta denominator is controlled on the actual lattice/kernel
mixture, not by substituting a continuous density at isolated integers. -/
theorem projectedPMF_density_bounds
    (lattice : Submodule ℤ (MixtureSpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift direction : MixtureSpace (dimension:=dimension)) {latticeWidth kernelWidth error : ℝ}
    (hlattice : 0<latticeWidth) (hkernel : 1 ≤ kernelWidth) (herror : 0<error) (herrorOne : error<1)
    (hsmoothing : smoothingParam lattice error ≤ latticeWidth) (output : ℤ) :
    projectedNumerator lattice shift direction latticeWidth kernelWidth output/
        (rhoCoset latticeWidth lattice shift*kernelWidth*(1+thetaError kernelWidth)) ≤
      (projectedPMF lattice shift direction hlattice (zero_lt_one.trans_le hkernel) herror herrorOne hsmoothing output).toReal ∧
    (projectedPMF lattice shift direction hlattice (zero_lt_one.trans_le hkernel) herror herrorOne hsmoothing output).toReal ≤
      projectedNumerator lattice shift direction latticeWidth kernelWidth output/
        (rhoCoset latticeWidth lattice shift*kernelWidth*(1-thetaError kernelWidth)) := by
  have hw : 0<kernelWidth := zero_lt_one.trans_le hkernel
  let numerator : lattice → ℝ := fun value =>
    rho latticeWidth ((value : MixtureSpace (dimension:=dimension))+shift)*
      shiftedWeight kernelWidth (inner ℝ direction ((value : MixtureSpace (dimension:=dimension))+shift)) output
  let actual : lattice → ℝ := fun value => cosetMass lattice shift latticeWidth value*
    (roundingPMF kernelWidth hw (inner ℝ direction ((value : MixtureSpace (dimension:=dimension))+shift)) output).toReal
  have hweight (center : ℝ) : shiftedWeight kernelWidth center output ≤ 1 := by
    unfold shiftedWeight
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_pos Real.pi_pos (sq_pos_of_pos hw)).le) (sq_nonneg _)
  have hn : Summable numerator := by
    apply Summable.of_nonneg_of_le
      (f:=fun value : lattice => rho latticeWidth ((value : MixtureSpace (dimension:=dimension))+shift))
    · intro value
      exact mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
    · intro value
      exact mul_le_of_le_one_right (Real.exp_nonneg _)
        (hweight (inner ℝ direction ((value : MixtureSpace (dimension:=dimension))+shift)))
    · exact summable_coset_of_smoothing lattice shift hlattice herror herrorOne hsmoothing
  have ha : Summable actual := by
    apply Summable.of_nonneg_of_le (f:=cosetMass lattice shift latticeWidth)
    · intro value
      exact mul_nonneg (cosetMass_nonneg lattice shift hlattice herror herrorOne hsmoothing value) ENNReal.toReal_nonneg
    · intro value
      exact mul_le_of_le_one_right (cosetMass_nonneg lattice shift hlattice herror herrorOne hsmoothing value)
        (roundingMass_le_one kernelWidth hw (inner ℝ direction ((value : MixtureSpace (dimension:=dimension))+shift)) output)
    · exact cosetMass_summable lattice shift hlattice herror herrorOne hsmoothing
  have hlo (value : lattice) : numerator value/(rhoCoset latticeWidth lattice shift*kernelWidth*(1+thetaError kernelWidth)) ≤ actual value := by
    have h := mul_le_mul_of_nonneg_left
      (roundingPMF_density_bounds kernelWidth hkernel (inner ℝ direction ((value : MixtureSpace (dimension:=dimension))+shift)) output).1
      (cosetMass_nonneg lattice shift hlattice herror herrorOne hsmoothing value)
    dsimp only [numerator,actual]
    simpa only [cosetMass_formula,div_mul_div_comm,mul_assoc] using h
  have hhi (value : lattice) : actual value ≤ numerator value/(rhoCoset latticeWidth lattice shift*kernelWidth*(1-thetaError kernelWidth)) := by
    have h := mul_le_mul_of_nonneg_left
      (roundingPMF_density_bounds kernelWidth hkernel (inner ℝ direction ((value : MixtureSpace (dimension:=dimension))+shift)) output).2
      (cosetMass_nonneg lattice shift hlattice herror herrorOne hsmoothing value)
    dsimp only [numerator,actual]
    simpa only [cosetMass_formula,div_mul_div_comm,mul_assoc] using h
  have hlow := (hn.div_const _).tsum_le_tsum hlo ha
  have hhigh := ha.tsum_le_tsum hhi (hn.div_const _)
  rw [tsum_div_const] at hlow hhigh
  have he : (∑' value : lattice,actual value)=
      (projectedPMF lattice shift direction hlattice hw herror herrorOne hsmoothing output).toReal := by
    exact (projectedPMF_toReal lattice shift direction hlattice hw herror herrorOne hsmoothing output).symm
  rw [he] at hlow hhigh
  exact ⟨hlow,hhigh⟩

/-- Relative error after combining the lattice Poisson numerator and the
uniform theta denominator of the actual integer-rounding kernel. -/
def mixtureError (kernelWidth error : ℝ) : ℝ :=
  (error+thetaError kernelWidth)/(1-thetaError kernelWidth)

theorem projectedPMF_relative_error
    (lattice : Submodule ℤ (MixtureSpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift direction : MixtureSpace (dimension:=dimension)) {latticeWidth kernelWidth error : ℝ}
    (hlattice : 0<latticeWidth) (hkernel : 1 ≤ kernelWidth) (herror : 0<error) (herrorOne : error<1)
    (hsmoothing : smoothingParam lattice error ≤ projectionEffectiveWidth latticeWidth kernelWidth direction)
    (output : ℤ) :
    let sourceSmoothing := hsmoothing.trans (projectionEffectiveWidth_le latticeWidth kernelWidth direction hlattice (zero_lt_one.trans_le hkernel))
    let image := GaussianLatticeTransport.imageLattice lattice
      (projectionEquiv latticeWidth kernelWidth direction hlattice (zero_lt_one.trans_le hkernel))
    let totalWidth := Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)
    let scale := ((ZLattice.covolume image)⁻¹*realNormalizer totalWidth)/(rhoCoset latticeWidth lattice shift*kernelWidth)
    |(projectedPMF lattice shift direction hlattice (zero_lt_one.trans_le hkernel) herror herrorOne sourceSmoothing output).toReal-
      scale*integerMass totalWidth output| ≤ mixtureError kernelWidth error*scale*integerMass totalWidth output := by
  have hw : 0<kernelWidth := zero_lt_one.trans_le hkernel
  have hs := hsmoothing.trans (projectionEffectiveWidth_le latticeWidth kernelWidth direction hlattice hw)
  let image := GaussianLatticeTransport.imageLattice lattice (projectionEquiv latticeWidth kernelWidth direction hlattice hw)
  let normalizer := (ZLattice.covolume image)⁻¹
  let sourceMass := rhoCoset latticeWidth lattice shift
  let totalWidth := Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)
  let scale := (normalizer*realNormalizer totalWidth)/(sourceMass*kernelWidth)
  let actual := (projectedPMF lattice shift direction hlattice hw herror herrorOne hs output).toReal
  let numerator := projectedNumerator lattice shift direction latticeWidth kernelWidth output
  let base := normalizer*weight totalWidth output/(sourceMass*kernelWidth)
  let delta := thetaError kernelWidth
  have hnormalizer : 0<normalizer := inv_pos.mpr (ZLattice.covolume_pos image)
  have hsource : 0<sourceMass := rhoCoset_pos_of_smoothing lattice shift hlattice herror herrorOne hs
  have hproduct : 0<sourceMass*kernelWidth := mul_pos hsource hw
  have hdelta : 0 ≤ delta := thetaError_nonneg kernelWidth hw
  have hden : 0<1-delta := sub_pos.mpr (roundingError_lt_one kernelWidth hkernel)
  have hplus : 0<1+delta := by linarith
  have hbase : 0 ≤ base := div_nonneg (mul_nonneg hnormalizer.le (weight_pos _ _).le) hproduct.le
  have hraw := projectedNumerator_relative_error lattice latticeWidth kernelWidth error direction shift hlattice hw herror hsmoothing output
  dsimp only at hraw
  change |numerator-normalizer*weight totalWidth output| ≤ error*normalizer*weight totalWidth output at hraw
  have hnlow : (1-error)*(normalizer*weight totalWidth output) ≤ numerator := by nlinarith [(abs_le.mp hraw).1]
  have hnhigh : numerator ≤ (1+error)*(normalizer*weight totalWidth output) := by nlinarith [(abs_le.mp hraw).2]
  have hactual := projectedPMF_density_bounds lattice shift direction hlattice hkernel herror herrorOne hs output
  have halow : numerator ≤ actual*(sourceMass*kernelWidth*(1+delta)) :=
    (div_le_iff₀ (mul_pos hproduct hplus)).mp hactual.1
  have hahigh : actual*(sourceMass*kernelWidth*(1-delta)) ≤ numerator :=
    (le_div_iff₀ (mul_pos hproduct hden)).mp hactual.2
  have haLower : numerator/(sourceMass*kernelWidth) ≤ (1+delta)*actual := by
    apply (div_le_iff₀ hproduct).mpr
    nlinarith only [halow]
  have haUpper : (1-delta)*actual ≤ numerator/(sourceMass*kernelWidth) := by
    apply (le_div_iff₀ hproduct).mpr
    nlinarith only [hahigh]
  have hlower : (1-error)*base ≤ (1+delta)*actual := by
    have h := (div_le_div_of_nonneg_right hnlow hproduct.le).trans haLower
    simpa only [base,mul_div_assoc] using h
  have hupper : (1-delta)*actual ≤ (1+error)*base := by
    have h := haUpper.trans (div_le_div_of_nonneg_right hnhigh hproduct.le)
    simpa only [base,mul_div_assoc] using h
  have hbound := multiplicative_sandwich_error actual base error delta hbase herror.le hdelta
    (roundingError_lt_one kernelWidth hkernel) hlower hupper
  have ht : 0<totalWidth := Real.sqrt_pos.mpr (projectedSquaredWidth_pos latticeWidth kernelWidth direction hw)
  have hn : 0<realNormalizer totalWidth := zero_lt_one.trans_le (realNormalizer_ge_one totalWidth ht)
  have hscale : scale*integerMass totalWidth output=base := by
    dsimp only [scale,base,integerMass]
    field_simp [hn.ne',hsource.ne',hw.ne']
  change |actual-scale*integerMass totalWidth output| ≤ mixtureError kernelWidth error*scale*integerMass totalWidth output
  rw [mul_assoc,hscale]
  simpa only [mixtureError,delta] using hbound

/-- Full countable total variation for the actual lattice-Gaussian then
shifted-integer-Gaussian experiment, with all infinite normalizers retained
until the final probability-law normalization step. -/
theorem projectedPMF_totalVariation
    (lattice : Submodule ℤ (MixtureSpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift direction : MixtureSpace (dimension:=dimension)) {latticeWidth kernelWidth error : ℝ}
    (hlattice : 0<latticeWidth) (hkernel : 1 ≤ kernelWidth) (herror : 0<error) (herrorOne : error<1)
    (hsmoothing : smoothingParam lattice error ≤ projectionEffectiveWidth latticeWidth kernelWidth direction)
    (hsmall : mixtureError kernelWidth error<1) :
    let sourceSmoothing := hsmoothing.trans (projectionEffectiveWidth_le latticeWidth kernelWidth direction hlattice (zero_lt_one.trans_le hkernel))
    let totalWidth := Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)
    (∑' output : ℤ, |(projectedPMF lattice shift direction hlattice (zero_lt_one.trans_le hkernel) herror herrorOne sourceSmoothing output).toReal-
      integerMass totalWidth output|)/2 ≤ mixtureError kernelWidth error/(1-mixtureError kernelWidth error) := by
  have hw : 0<kernelWidth := zero_lt_one.trans_le hkernel
  have hs := hsmoothing.trans (projectionEffectiveWidth_le latticeWidth kernelWidth direction hlattice hw)
  let image := GaussianLatticeTransport.imageLattice lattice (projectionEquiv latticeWidth kernelWidth direction hlattice hw)
  let totalWidth := Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)
  let scale := ((ZLattice.covolume image)⁻¹*realNormalizer totalWidth)/(rhoCoset latticeWidth lattice shift*kernelWidth)
  let actual := projectedPMF lattice shift direction hlattice hw herror herrorOne hs
  have ht : 0<totalWidth := Real.sqrt_pos.mpr (projectedSquaredWidth_pos latticeWidth kernelWidth direction hw)
  have he : 0 ≤ mixtureError kernelWidth error := div_nonneg
    (add_nonneg herror.le (thetaError_nonneg kernelWidth hw))
    (sub_pos.mpr (roundingError_lt_one kernelWidth hkernel)).le
  have hpoint (output : ℤ) : |(actual output).toReal-scale*integerMass totalWidth output| ≤
      mixtureError kernelWidth error*scale*integerMass totalWidth output :=
    projectedPMF_relative_error lattice shift direction hlattice hkernel herror herrorOne hsmoothing output
  exact normalized_tilt_total_variation (integerMass totalWidth) (fun output => (actual output).toReal)
    (integerMass_nonneg totalWidth ht) (summable_integerMass totalWidth ht) (pmf_realMass_summable actual)
    (integerMass_sum totalWidth ht) (pmf_realMass_sum actual) scale (mixtureError kernelWidth error) he hsmall hpoint

theorem mixtureError_nonneg {kernelWidth error : ℝ} (hkernel : 1 ≤ kernelWidth) (herror : 0 ≤ error) :
    0 ≤ mixtureError kernelWidth error :=
  div_nonneg (add_nonneg herror (thetaError_nonneg kernelWidth (zero_lt_one.trans_le hkernel)))
    (sub_pos.mpr (roundingError_lt_one kernelWidth hkernel)).le

theorem mixtureError_le_half {kernelWidth error : ℝ} (hkernel : 1 ≤ kernelWidth)
    (hsmall : 2*error+3*thetaError kernelWidth ≤ 1) : mixtureError kernelWidth error ≤ 1/2 := by
  apply (div_le_iff₀ (sub_pos.mpr (roundingError_lt_one kernelWidth hkernel))).mpr
  linarith

/-- Explicit full-law error with no unknown scale or unnormalized
reference left in the conclusion. -/
theorem projectedPMF_totalVariation_exp
    (lattice : Submodule ℤ (MixtureSpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift direction : MixtureSpace (dimension:=dimension)) {latticeWidth kernelWidth error : ℝ}
    (hlattice : 0<latticeWidth) (hkernel : 1 ≤ kernelWidth) (herror : 0<error) (herrorOne : error<1)
    (hsmoothing : smoothingParam lattice error ≤ projectionEffectiveWidth latticeWidth kernelWidth direction)
    (hsmall : 2*error+3*thetaError kernelWidth ≤ 1) :
    let sourceSmoothing := hsmoothing.trans (projectionEffectiveWidth_le latticeWidth kernelWidth direction hlattice (zero_lt_one.trans_le hkernel))
    let totalWidth := Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)
    (∑' output : ℤ, |(projectedPMF lattice shift direction hlattice (zero_lt_one.trans_le hkernel) herror herrorOne sourceSmoothing output).toReal-
      integerMass totalWidth output|)/2 ≤ 4*error+16*Real.exp (-Real.pi*kernelWidth^2) := by
  have hh := mixtureError_le_half hkernel hsmall
  have hn := mixtureError_nonneg hkernel herror.le
  have he : mixtureError kernelWidth error<1 := by linarith
  have hc : mixtureError kernelWidth error/(1-mixtureError kernelWidth error) ≤ 2*mixtureError kernelWidth error := by
    apply (div_le_iff₀ (sub_pos.mpr he)).mpr
    nlinarith
  have hg : mixtureError kernelWidth error ≤ 2*(error+thetaError kernelWidth) := by
    apply (div_le_iff₀ (sub_pos.mpr (roundingError_lt_one kernelWidth hkernel))).mpr
    have hp := add_nonneg herror.le (thetaError_nonneg kernelWidth (zero_lt_one.trans_le hkernel))
    have ht := roundingError_lt_half kernelWidth hkernel
    nlinarith [mul_nonneg hp (by linarith : 0 ≤ 1-2*thetaError kernelWidth)]
  exact (projectedPMF_totalVariation lattice shift direction hlattice hkernel herror herrorOne hsmoothing he).trans
    (hc.trans (by linarith [thetaError_le_four_exp kernelWidth hkernel]))

/-- In the BDD parameter range R²‖e‖²≤w², the scalar output width lies
between w and √2w, and the required effective smoothing width is at least R/√2. -/
theorem projection_width_bounds (latticeWidth kernelWidth : ℝ) (direction : MixtureSpace (dimension:=dimension))
    (hlattice : 0<latticeWidth) (hkernel : 0<kernelWidth)
    (hsmall : latticeWidth^2*‖direction‖^2 ≤ kernelWidth^2) :
    kernelWidth ≤ Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction) ∧
      Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction) ≤ Real.sqrt 2*kernelWidth ∧
      latticeWidth/Real.sqrt 2 ≤ projectionEffectiveWidth latticeWidth kernelWidth direction := by
  have ht := Real.sqrt_pos.mpr (projectedSquaredWidth_pos latticeWidth kernelWidth direction hkernel)
  have hroot : 0<Real.sqrt (2 : ℝ) := by positivity
  have htotal := Real.sq_sqrt (projectedSquaredWidth_pos latticeWidth kernelWidth direction hkernel).le
  have hsq : (Real.sqrt (2 : ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hlo : kernelWidth ≤ Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction) := by
    apply (sq_le_sq₀ hkernel.le ht.le).mp
    rw [htotal]
    unfold projectedSquaredWidth
    nlinarith [mul_nonneg (sq_nonneg latticeWidth) (sq_nonneg ‖direction‖)]
  have hhi : Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction) ≤ Real.sqrt 2*kernelWidth := by
    apply (sq_le_sq₀ ht.le (mul_pos hroot hkernel).le).mp
    rw [htotal,mul_pow,hsq]
    unfold projectedSquaredWidth
    linarith
  refine ⟨hlo,hhi,?_⟩
  rw [projectionEffectiveWidth_eq latticeWidth kernelWidth direction hlattice hkernel]
  calc
    latticeWidth/Real.sqrt 2=latticeWidth*kernelWidth/(Real.sqrt 2*kernelWidth) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (mul_pos hlattice hkernel).le ht hhi

end

end InfoLossLAR.WorstCase.GaussianProjection

end P2MDyadicModule40

/- Helper module Solutions.RegevBridgeGaussianRoundingCountable. -/
section P2MDyadicModule41

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding

open AFT GaussianSource GaussianProjection

open scoped BigOperators Classical

noncomputable section

/-- Every coordinate of an actual finite probability law is at most one. -/
theorem finiteWeight_le_one {Output : Type*} [Fintype Output] (law : FiniteDist Output) (output : Output) :
    law.weight output ≤ 1 := by
  exact (Finset.single_le_sum (fun result _ => law.nonneg result) (Finset.mem_univ output)).trans_eq law.sum_one

theorem summable_countable_kernel {State Output : Type*} [Fintype Output]
    (source : PMF State) (kernel : State → FiniteDist Output) (output : Output) :
    Summable (fun state => (source state).toReal*(kernel state).weight output) := by
  apply Summable.of_nonneg_of_le
    (fun state => mul_nonneg ENNReal.toReal_nonneg ((kernel state).nonneg output))
    (fun state => mul_le_of_le_one_right ENNReal.toReal_nonneg (finiteWeight_le_one (kernel state) output))
    (pmf_realMass_summable source)

/-- A genuine finite output law after a possibly infinite lattice-source
PMF and an independently randomized finite output kernel. -/
def countableMix {State Output : Type*} [Fintype Output]
    (source : PMF State) (kernel : State → FiniteDist Output) : FiniteDist Output where
  weight output := ∑' state,(source state).toReal*(kernel state).weight output
  nonneg output := tsum_nonneg (fun state => mul_nonneg ENNReal.toReal_nonneg ((kernel state).nonneg output))
  sum_one := by
    rw [←Summable.tsum_finsetSum (fun output _ => summable_countable_kernel source kernel output)]
    simp_rw [←Finset.mul_sum,FiniteDist.sum_one,mul_one]
    exact pmf_realMass_sum source

/-- The countable mixture is exactly the finite-law image of a literal
PMF bind whenever the output kernels are given as PMFs. -/
theorem countableMix_bind {State Output : Type*} [Fintype Output]
    (source : PMF State) (kernel : State → PMF Output) :
    countableMix source (fun state => finiteLaw (kernel state))=
      finiteLaw (source.bind kernel) := by
  ext output
  change (∑' state,(source state).toReal*(kernel state output).toReal)=(source.bind kernel output).toReal
  rw [PMF.bind_apply,ENNReal.tsum_toReal_eq]
  · simp only [ENNReal.toReal_mul]
  · intro state
    exact ENNReal.mul_ne_top (source.apply_ne_top state) ((kernel state).apply_ne_top output)

/-- A uniform conditional L1 bound survives a genuinely countable source.
The source may correlate all parameters of its output kernel. -/
theorem countableMix_l1_le {State Output : Type*} [Fintype Output]
    (source : PMF State) (first second : State → FiniteDist Output) (error : ℝ)
    (herror : ∀ state,(∑ output,|(first state).weight output-(second state).weight output|) ≤ error) :
    (∑ output,|(countableMix source first).weight output-(countableMix source second).weight output|) ≤ error := by
  have hsfirst := summable_countable_kernel source first
  have hssecond := summable_countable_kernel source second
  have hsabs (output : Output) : Summable (fun state =>
      (source state).toReal*|(first state).weight output-(second state).weight output|) := by
    have h := ((hsfirst output).sub (hssecond output)).norm
    simpa only [Real.norm_eq_abs,←mul_sub,abs_mul,abs_of_nonneg ENNReal.toReal_nonneg] using h
  have hpoint (output : Output) : |(countableMix source first).weight output-(countableMix source second).weight output| ≤
      ∑' state,(source state).toReal*|(first state).weight output-(second state).weight output| := by
    change |(∑' state,(source state).toReal*(first state).weight output)-
      (∑' state,(source state).toReal*(second state).weight output)| ≤ _
    rw [←(hsfirst output).tsum_sub (hssecond output)]
    have h := norm_tsum_le_tsum_norm (((hsfirst output).sub (hssecond output)).norm)
    simpa only [Real.norm_eq_abs,←mul_sub,abs_mul,abs_of_nonneg ENNReal.toReal_nonneg] using h
  have hsum (selected : Finset Output) : Summable (fun state =>
      ∑ output ∈ selected,(source state).toReal*|(first state).weight output-(second state).weight output|) := by
    induction selected using Finset.induction_on with
    | empty => simp
    | @insert output selected hnot ih =>
      simp_rw [Finset.sum_insert hnot]
      exact (hsabs output).add ih
  calc
    _ ≤ ∑ output,∑' state,(source state).toReal*|(first state).weight output-(second state).weight output| :=
      Finset.sum_le_sum (fun output _ => hpoint output)
    _ = ∑' state,∑ output,(source state).toReal*|(first state).weight output-(second state).weight output| :=
      (Summable.tsum_finsetSum (fun output _ => hsabs output)).symm
    _ ≤ ∑' state,(source state).toReal*error := by
      apply (hsum Finset.univ).tsum_le_tsum _ ((pmf_realMass_summable source).mul_right error)
      intro state
      rw [←Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (herror state) ENNReal.toReal_nonneg
    _ = error := by rw [tsum_mul_right,pmf_realMass_sum,one_mul]

/-- Actual native finite-bit rounding from an arbitrary countable source
has its complete per-output kernel error, including the infinite tail. -/
theorem native_countableMix_l1 {State : Type*} (source : PMF State) (q : ℕ) [NeZero q]
    (squaredWidth : ℚ) (center : State → ℚ) (width : ℝ) (cutoff bits : ℕ)
    (hwidthSquared : 1 ≤ squaredWidth) (hsquare : width^2=(squaredWidth : ℝ)) (hwidth : 1 ≤ width) :
    (∑ output : ZMod q, |(countableMix source (fun state =>
      (FiniteDist.independent (fun _ : Fin ((bits+1)+(2*cutoff+1)+1) => FiniteDist.uniform (Fin 2))).map
        (fun word => (Native.output (Native.numericalRequest squaredWidth (center state) cutoff bits word) : ZMod q)))).weight output-
      (countableMix source (fun state => modularRounding q width (zero_lt_one.trans_le hwidth) (center state))).weight output|) ≤
        1/(2 : ℝ)^bits+2*tailEnvelope width cutoff := by
  apply countableMix_l1_le
  intro state
  exact Native.output_modular_l1 q squaredWidth (center state) width cutoff bits hwidthSquared hsquare hwidth

/-- The ideal kernel mixture is the literal reduction modulo q of the
entire countable rounded-input law. -/
theorem countableMix_modularRounding {State : Type*} (source : PMF State) (q : ℕ) [NeZero q]
    (width : ℝ) (hwidth : 0<width) (center : State → ℝ) :
    countableMix source (fun state => modularRounding q width hwidth (center state))=
      finiteLaw ((source.bind (fun state => roundingPMF width hwidth (center state))).map
        (fun value : ℤ => (value : ZMod q))) := by
  unfold modularRounding
  rw [countableMix_bind,PMF.map_bind]

/-- Finite reduction of a countable PMF cannot increase its complete L1
error. Every infinite series used in the proof is summable. -/
theorem finiteLaw_map_l1_le {State Output : Type*} [Fintype Output]
    (first second : PMF State) (compute : State → Output) :
    (∑ output, |(finiteLaw (first.map compute)).weight output-(finiteLaw (second.map compute)).weight output|) ≤
      ∑' state, |(first state).toReal-(second state).toReal| := by
  have hfirst (output : Output) : Summable (fun state => if compute state=output then (first state).toReal else 0) := by
    apply Summable.of_nonneg_of_le _ _ (pmf_realMass_summable first)
    · intro state;split_ifs <;> positivity
    · intro state;split_ifs <;> simp [ENNReal.toReal_nonneg]
  have hsecond (output : Output) : Summable (fun state => if compute state=output then (second state).toReal else 0) := by
    apply Summable.of_nonneg_of_le _ _ (pmf_realMass_summable second)
    · intro state;split_ifs <;> positivity
    · intro state;split_ifs <;> simp [ENNReal.toReal_nonneg]
  have habs (output : Output) : Summable (fun state =>
      if compute state=output then |(first state).toReal-(second state).toReal| else 0) := by
    apply Summable.of_nonneg_of_le _ _ ((pmf_realMass_summable first).sub (pmf_realMass_summable second)).norm
    · intro state;split_ifs <;> positivity
    · intro state
      rw [Real.norm_eq_abs]
      split_ifs <;> simp [abs_nonneg]
  have hpoint (output : Output) :
      |(finiteLaw (first.map compute)).weight output-(finiteLaw (second.map compute)).weight output| ≤
        ∑' state,if compute state=output then |(first state).toReal-(second state).toReal| else 0 := by
    rw [Integration.finiteLaw_map_weight,Integration.finiteLaw_map_weight,
      ←(hfirst output).tsum_sub (hsecond output)]
    have he (state : State) :
        |(if compute state=output then (first state).toReal else 0)-
          (if compute state=output then (second state).toReal else 0)|=
          if compute state=output then |(first state).toReal-(second state).toReal| else 0 := by split_ifs <;> simp
    have h := norm_tsum_le_tsum_norm (((hfirst output).sub (hsecond output)).norm)
    simpa only [Real.norm_eq_abs,he] using h
  calc
    _ ≤ ∑ output,∑' state,if compute state=output then |(first state).toReal-(second state).toReal| else 0 :=
      Finset.sum_le_sum (fun output _ => hpoint output)
    _ = ∑' state,∑ output,if compute state=output then |(first state).toReal-(second state).toReal| else 0 :=
      (Summable.tsum_finsetSum (fun output _ => habs output)).symm
    _ = _ := by simp

/-- Accuracy against the literal modular image of the actual countable
source/kernel PMF, not merely an auxiliary finite-source experiment. -/
theorem native_countable_to_PMF_l1 {State : Type*} (source : PMF State) (q : ℕ) [NeZero q]
    (squaredWidth : ℚ) (center : State → ℚ) (width : ℝ) (cutoff bits : ℕ)
    (hwidthSquared : 1 ≤ squaredWidth) (hsquare : width^2=(squaredWidth : ℝ)) (hwidth : 1 ≤ width) :
    (∑ output : ZMod q, |(countableMix source (fun state =>
      (FiniteDist.independent (fun _ : Fin ((bits+1)+(2*cutoff+1)+1) => FiniteDist.uniform (Fin 2))).map
        (fun word => (Native.output (Native.numericalRequest squaredWidth (center state) cutoff bits word) : ZMod q)))).weight output-
      (finiteLaw ((source.bind (fun state => roundingPMF width (zero_lt_one.trans_le hwidth) (center state))).map
        (fun value : ℤ => (value : ZMod q)))).weight output|) ≤ 1/(2 : ℝ)^bits+2*tailEnvelope width cutoff := by
  rw [←countableMix_modularRounding]
  exact native_countableMix_l1 source q squaredWidth center width cutoff bits hwidthSquared hsquare hwidth

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding

end P2MDyadicModule41

/- Helper module Solutions.RegevBridgeGaussianProjectionNative. -/
section P2MDyadicModule42

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open AFT GaussianSource RegevLWE.GaussConv GaussianRandomizedRounding

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

abbrev NativeProjectionSpace := EuclideanSpace ℝ (Fin dimension)

/-- End-to-end sample-law guarantee for the actual native finite-tape
kernel applied to a genuine lattice-Gaussian sample. The given rational
centers are exact representations of the projection; no real input sampler
or efficient DGS existence is postulated. -/
theorem native_projected_totalVariation
    (lattice : Submodule ℤ (NativeProjectionSpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (q : ℕ) [NeZero q] (shift direction : NativeProjectionSpace (dimension:=dimension))
    (center : lattice → ℚ) (squaredWidth : ℚ) {latticeWidth kernelWidth error : ℝ}
    (hlattice : 0<latticeWidth) (hkernel : 1 ≤ kernelWidth) (hwidthSquared : 1 ≤ squaredWidth)
    (hsquare : kernelWidth^2=(squaredWidth : ℝ)) (herror : 0<error) (herrorOne : error<1)
    (hsmoothing : smoothingParam lattice error ≤ projectionEffectiveWidth latticeWidth kernelWidth direction)
    (hsmall : 2*error+3*thetaError kernelWidth ≤ 1)
    (hcenter : ∀ value : lattice,(center value : ℝ)=inner ℝ direction ((value : NativeProjectionSpace (dimension:=dimension))+shift))
    (cutoff bits : ℕ) :
    let sourceSmoothing := hsmoothing.trans (projectionEffectiveWidth_le latticeWidth kernelWidth direction hlattice (zero_lt_one.trans_le hkernel))
    let source := cosetPMF lattice shift hlattice herror herrorOne sourceSmoothing
    let totalWidth := Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)
    (∑ output : ZMod q, |(countableMix source (fun value =>
      (FiniteDist.independent (fun _ : Fin ((bits+1)+(2*cutoff+1)+1) => FiniteDist.uniform (Fin 2))).map
        (fun word => (Native.output (Native.numericalRequest squaredWidth (center value) cutoff bits word) : ZMod q)))).weight output-
      (finiteLaw ((integerGaussian totalWidth (Real.sqrt_pos.mpr (projectedSquaredWidth_pos latticeWidth kernelWidth direction (zero_lt_one.trans_le hkernel)))).map
        (fun value : ℤ => (value : ZMod q)))).weight output|)/2 ≤
      1/(2 : ℝ)^(bits+1)+tailEnvelope kernelWidth cutoff+4*error+16*Real.exp (-Real.pi*kernelWidth^2) := by
  have hw : 0<kernelWidth := zero_lt_one.trans_le hkernel
  have hs := hsmoothing.trans (projectionEffectiveWidth_le latticeWidth kernelWidth direction hlattice hw)
  let source := cosetPMF lattice shift hlattice herror herrorOne hs
  let projected := projectedPMF lattice shift direction hlattice hw herror herrorOne hs
  let totalWidth := Real.sqrt (projectedSquaredWidth latticeWidth kernelWidth direction)
  have ht : 0<totalWidth := Real.sqrt_pos.mpr (projectedSquaredWidth_pos latticeWidth kernelWidth direction hw)
  let gaussian := integerGaussian totalWidth ht
  let actual := countableMix source (fun value =>
    (FiniteDist.independent (fun _ : Fin ((bits+1)+(2*cutoff+1)+1) => FiniteDist.uniform (Fin 2))).map
      (fun word => (Native.output (Native.numericalRequest squaredWidth (center value) cutoff bits word) : ZMod q)))
  have hprojected : (source.bind (fun value => roundingPMF kernelWidth hw (center value)))=projected := by
    change source.bind _=source.bind _
    apply congrArg source.bind
    funext value
    rw [hcenter value]
  have hnative := native_countable_to_PMF_l1 source q squaredWidth center kernelWidth cutoff bits hwidthSquared hsquare hkernel
  rw [hprojected] at hnative
  have hmap := finiteLaw_map_l1_le projected gaussian (fun value : ℤ => (value : ZMod q))
  have hfull := projectedPMF_totalVariation_exp lattice shift direction hlattice hkernel herror herrorOne hsmoothing hsmall
  change (∑' output : ℤ, |(projected output).toReal-integerMass totalWidth output|)/2 ≤ _ at hfull
  have he (output : ℤ) : (gaussian output).toReal=integerMass totalWidth output :=
    (integerMass_eq_pmf totalWidth ht output).symm
  simp_rw [he] at hmap
  have htriangle := Finset.sum_le_sum (fun output (_ : output ∈ (Finset.univ : Finset (ZMod q))) =>
    abs_sub_le (actual.weight output) ((finiteLaw (projected.map (fun value : ℤ => (value : ZMod q)))).weight output)
      ((finiteLaw (gaussian.map (fun value : ℤ => (value : ZMod q)))).weight output))
  rw [Finset.sum_add_distrib] at htriangle
  have hdyadic : (1/(2 : ℝ)^bits)/2=1/(2 : ℝ)^(bits+1) := by rw [pow_succ];ring
  change (∑ output : ZMod q, |actual.weight output-(finiteLaw (gaussian.map (fun value : ℤ => (value : ZMod q)))).weight output|)/2 ≤ _
  linarith [hdyadic]

end

end InfoLossLAR.WorstCase.GaussianProjection

end P2MDyadicModule42

/- Helper module Solutions.RegevBridgeGaussianGridProjection. -/
section P2MDyadicModule43

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection.VarianceGrid

open AFT GaussianSource GaussianRandomizedRounding RegevLWE.GaussConv

open scoped BigOperators

noncomputable section

/-- Uniform truncation error profile over the publicly enumerated width
interval. The upper width controls the Gaussian tail; the lower width
controls both theta normalizers. -/
def intervalTail (lower upper radius : ℝ) : ℝ :=
  Real.sqrt 2*(1+thetaError lower)/(1-thetaError lower)*Real.exp (-Real.pi*radius^2/(2*upper^2))

theorem tailEnvelope_interval {lower width upper : ℝ} (radius : ℝ)
    (hlower : 1 ≤ lower) (hlowerWidth : lower ≤ width) (hwidthUpper : width ≤ upper) :
    tailEnvelope width radius ≤ intervalTail lower upper radius := by
  have hlo : 0<lower := zero_lt_one.trans_le hlower
  have hw : 0<width := hlo.trans_le hlowerWidth
  have hu : 0<upper := hw.trans_le hwidthUpper
  have hwOne : 1 ≤ width := hlower.trans hlowerWidth
  have hroot : (1 : ℝ) ≤ Real.sqrt 2 := by apply Real.le_sqrt_of_sq_le;norm_num
  have ht := thetaError_antitone lower width hlo hlowerWidth
  have htb := thetaError_antitone lower (Real.sqrt 2*width) hlo
    (hlowerWidth.trans (le_mul_of_one_le_left hw.le hroot))
  have hdlo : 0<1-thetaError lower := sub_pos.mpr (roundingError_lt_one lower hlower)
  have hdw : 0<1-thetaError width := sub_pos.mpr (roundingError_lt_one width hwOne)
  have hnum : 0 ≤ Real.sqrt 2*(1+thetaError lower) := by
    have he := thetaError_nonneg lower hlo
    positivity
  have hfactor : Real.sqrt 2*(1+thetaError (Real.sqrt 2*width))/(1-thetaError width) ≤
      Real.sqrt 2*(1+thetaError lower)/(1-thetaError lower) := by
    apply (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl htb) (Real.sqrt_nonneg 2)) hdw.le).trans
    exact div_le_div_of_nonneg_left hnum hdlo (by linarith)
  have hn : 0 ≤ Real.pi*radius^2 := mul_nonneg Real.pi_pos.le (sq_nonneg radius)
  have hsq : 2*width^2 ≤ 2*upper^2 := by nlinarith [(sq_le_sq₀ hw.le hu.le).mpr hwidthUpper]
  have hfrac := div_le_div_of_nonneg_left hn (mul_pos (by norm_num : (0 : ℝ)<2) (sq_pos_of_pos hw)) hsq
  have hexp : Real.exp (-Real.pi*radius^2/(2*width^2)) ≤ Real.exp (-Real.pi*radius^2/(2*upper^2)) := by
    apply Real.exp_le_exp.mpr
    calc
      _ = -(Real.pi*radius^2/(2*width^2)) := by ring
      _ ≤ -(Real.pi*radius^2/(2*upper^2)) := neg_le_neg hfrac
      _ = _ := by ring
  unfold tailEnvelope intervalTail
  exact (mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hexp (div_nonneg hnum hdlo.le))

/-- The actual sampler conditional on its countable lattice input. -/
def sampleLaw {State : Type*} (source : PMF State) (q : ℕ) [NeZero q]
    (squaredWidth : ℚ) (center : State → ℚ) (cutoff bits : ℕ) : FiniteDist (ZMod q) :=
  countableMix source (fun value =>
    (FiniteDist.independent (fun _ : Fin ((bits+1)+(2*cutoff+1)+1) => FiniteDist.uniform (Fin 2))).map
      (fun word => (Native.output (Native.numericalRequest squaredWidth (center value) cutoff bits word) : ZMod q)))

end

end InfoLossLAR.WorstCase.GaussianProjection.VarianceGrid

end P2MDyadicModule43

/- Helper module Solutions.RegevBridgeGaussianCosetGeometry. -/
section P2MDyadicModule44

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

open AFT GaussianSource RegevLWE.GaussConv GaussianRandomizedRounding

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

/-- Public coefficients and the hidden secret live in the same fixed
input basis; zero secret coordinates are allowed. -/
def publicCoordinates {Index : Type*} [Fintype Index] (q : ℕ)
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (value : lattice) : Index → ZMod q :=
  fun index => (basis.equivFun value index : ZMod q)

theorem pairing_basis {Index : Type*} [Fintype Index]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice)
    (nearest : dual lattice) (value : lattice) :
    pairing lattice nearest value=∑ index,basis.equivFun value index*pairing lattice nearest (basis index) := by
  have h := congrArg (pairing lattice nearest) (basis.sum_repr value)
  rw [map_sum] at h
  simp only [map_smul,smul_eq_mul,Module.Basis.equivFun_apply] at h ⊢
  exact h.symm

/-- Exact secret dot product in the actual public residue coordinates. -/
theorem pairing_mod_basis {Index : Type*} [Fintype Index] (q : ℕ)
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice)
    (nearest : dual lattice) (value : lattice) :
    (pairing lattice nearest value : ZMod q)=
      ∑ index,secretCoordinates q lattice basis nearest index*publicCoordinates q lattice basis value index := by
  rw [pairing_basis lattice basis nearest value]
  push_cast
  apply Finset.sum_congr rfl
  intro index _
  exact mul_comm _ _

/-- Canonical input-basis representative of each public residue vector. -/
def lift {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (color : Index → ZMod q) : lattice :=
  basis.equivFun.symm (fun index => ((color index).val : ℤ))

theorem publicCoordinates_lift {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (color : Index → ZMod q) :
    publicCoordinates q lattice basis (lift q lattice basis color)=color := by
  funext index
  unfold publicCoordinates lift
  rw [LinearEquiv.apply_symm_apply]
  simp only [Int.cast_natCast,ZMod.natCast_zmod_val]

theorem modulusLattice_le (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension))) :
    modulusLattice q lattice ≤ lattice := by
  intro value membership
  obtain ⟨original,horiginal,rfl⟩ := (mem_dilated_lattice lattice (q : ℝ) (Nat.cast_pos.mpr (NeZero.pos q)) value).mp membership
  have h := lattice.smul_mem (q : ℤ) horiginal
  simpa only [←Int.cast_smul_eq_zsmul ℝ,Int.cast_natCast] using h

/-- The actual point in the coset qL+u, viewed back in L. -/
def sample (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (shift : lattice) (value : modulusLattice q lattice) : lattice :=
  ⟨(value : Space (dimension:=dimension))+(shift : Space (dimension:=dimension)),
    lattice.add_mem (modulusLattice_le q lattice value.property) shift.property⟩

/-- Conditioning on one public coset fixes the integral secret pairing
modulo q, although the sampled lattice vector remains random. -/
theorem pairing_mod_coset (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (nearest : dual lattice) (shift : lattice) (value : modulusLattice q lattice) :
    (pairing lattice nearest (sample q lattice shift value) : ZMod q)=(pairing lattice nearest shift : ZMod q) := by
  obtain ⟨original,horiginal,heq⟩ :=
    (mem_dilated_lattice lattice (q : ℝ) (Nat.cast_pos.mpr (NeZero.pos q)) (value : Space (dimension:=dimension))).mp value.property
  let originalPoint : lattice := ⟨original,horiginal⟩
  have hreal : (pairing lattice nearest (sample q lattice shift value) : ℝ)=
      ((q : ℤ)*pairing lattice nearest originalPoint+pairing lattice nearest shift : ℤ) := by
    push_cast
    simp only [pairing_spec]
    change inner ℝ (nearest : Space (dimension:=dimension))
      ((value : Space (dimension:=dimension))+(shift : Space (dimension:=dimension)))=
      (q : ℝ)*inner ℝ (nearest : Space (dimension:=dimension)) original+
        inner ℝ (nearest : Space (dimension:=dimension)) (shift : Space (dimension:=dimension))
    rw [←heq,inner_add_right,real_inner_smul_right]
  have hinteger : pairing lattice nearest (sample q lattice shift value)=
      (q : ℤ)*pairing lattice nearest originalPoint+pairing lattice nearest shift := by exact_mod_cast hreal
  simp [hinteger]

instance modulus_discrete (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] :
    DiscreteTopology (modulusLattice q lattice) := by unfold modulusLattice;infer_instance

instance modulus_full_rank (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice] :
    IsZLattice ℝ (modulusLattice q lattice) := by unfold modulusLattice;infer_instance

theorem publicCoordinates_add {Index : Type*} [Fintype Index] (q : ℕ)
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (first second : lattice) :
    publicCoordinates q lattice basis (first+second)=publicCoordinates q lattice basis first+publicCoordinates q lattice basis second := by
  funext index
  simp only [publicCoordinates,map_add,Pi.add_apply,Int.cast_add]

theorem publicCoordinates_sub {Index : Type*} [Fintype Index] (q : ℕ)
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (first second : lattice) :
    publicCoordinates q lattice basis (first-second)=publicCoordinates q lattice basis first-publicCoordinates q lattice basis second := by
  funext index
  simp only [publicCoordinates,map_sub,Pi.sub_apply,Int.cast_sub]

/-- The zero public-coefficient fiber is exactly the actual q-dilate. -/
theorem publicCoordinates_zero_iff {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (value : lattice) :
    publicCoordinates q lattice basis value=0 ↔ (value : Space (dimension:=dimension)) ∈ modulusLattice q lattice := by
  constructor
  · intro hzero
    have hdiv (index : Index) : (q : ℤ) ∣ basis.equivFun value index :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp (by simpa only [publicCoordinates,Pi.zero_apply] using congrFun hzero index)
    let original := basis.equivFun.symm (fun index => basis.equivFun value index/(q : ℤ))
    have he : (q : ℤ) • original=value := by
      apply basis.equivFun.injective
      rw [map_smul]
      funext index
      simp only [original,LinearEquiv.apply_symm_apply,Pi.smul_apply,smul_eq_mul]
      exact Int.mul_ediv_cancel' (hdiv index)
    apply (mem_dilated_lattice lattice (q : ℝ) (Nat.cast_pos.mpr (NeZero.pos q)) (value : Space (dimension:=dimension))).mpr
    refine ⟨(original : Space (dimension:=dimension)),original.property,?_⟩
    have h := congrArg (fun point : lattice => (point : Space (dimension:=dimension))) he
    simpa only [Submodule.coe_smul,←Int.cast_smul_eq_zsmul ℝ,Int.cast_natCast] using h
  · intro membership
    obtain ⟨original,horiginal,heq⟩ :=
      (mem_dilated_lattice lattice (q : ℝ) (Nat.cast_pos.mpr (NeZero.pos q)) (value : Space (dimension:=dimension))).mp membership
    let originalPoint : lattice := ⟨original,horiginal⟩
    have he : value=(q : ℤ) • originalPoint := by
      apply Subtype.ext
      change (value : Space (dimension:=dimension))=(q : ℤ) • original
      rw [←Int.cast_smul_eq_zsmul ℝ,Int.cast_natCast]
      exact heq.symm
    rw [he]
    funext index
    simp [publicCoordinates,Pi.smul_apply]

theorem publicCoordinates_sample {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice)
    (shift : lattice) (value : modulusLattice q lattice) :
    publicCoordinates q lattice basis (sample q lattice shift value)=publicCoordinates q lattice basis shift := by
  let original : lattice := ⟨(value : Space (dimension:=dimension)),modulusLattice_le q lattice value.property⟩
  have hz : publicCoordinates q lattice basis original=0 :=
    (publicCoordinates_zero_iff q lattice basis original).mpr value.property
  change publicCoordinates q lattice basis (original+shift)=publicCoordinates q lattice basis shift
  rw [publicCoordinates_add,hz,zero_add]

theorem publicCoordinates_fiber {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice)
    (color : Index → ZMod q) (value : lattice) :
    publicCoordinates q lattice basis value=color ↔
      ((value-lift q lattice basis color : lattice) : Space (dimension:=dimension)) ∈ modulusLattice q lattice := by
  rw [←publicCoordinates_zero_iff q lattice basis (value-lift q lattice basis color),
    publicCoordinates_sub,publicCoordinates_lift,sub_eq_zero]

end

end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

end P2MDyadicModule44

/- Helper module Solutions.RegevBridgeFiniteProductMass. -/
section P2MDyadicModule45

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open scoped BigOperators

noncomputable section

/-- The full countable joint product law, not just its coordinate marginals. -/
def finiteProductMass {Index : Type*} (dimension : ℕ) (mass : Index → ℝ) (word : Fin dimension → Index) : ℝ :=
  ∏ index,mass (word index)

theorem finiteProductMass_nonnegative {Index : Type*} (dimension : ℕ) (mass : Index → ℝ)
    (hnonnegative : ∀ value,0 ≤ mass value) (word : Fin dimension → Index) :
    0 ≤ finiteProductMass dimension mass word := Finset.prod_nonneg (fun _ _ => hnonnegative _)

/-- A genuine full infinite product-law normalization in finitely many
coordinates, valid without finiteness of the individual coordinate space. -/
theorem finiteProductMass_hasSum {Index : Type*} (dimension : ℕ) (mass : Index → ℝ)
    (hnonnegative : ∀ value,0 ≤ mass value) (hsummable : Summable mass) :
    HasSum (finiteProductMass dimension mass) ((∑' value,mass value)^dimension) := by
  classical
  induction dimension with
  | zero =>
    rw [pow_zero]
    have heq : finiteProductMass 0 mass=(fun _ : Fin 0 → Index => (1 : ℝ)) := by
      funext word
      simp only [finiteProductMass,Finset.univ_eq_empty,Finset.prod_empty]
    rw [heq]
    convert hasSum_fintype (fun _ : Fin 0 → Index => (1 : ℝ)) using 1
    simp
  | succ dimension ih =>
    have hs := hsummable.mul_of_nonneg ih.summable hnonnegative
      (finiteProductMass_nonnegative dimension mass hnonnegative)
    have hp := hsummable.hasSum.mul ih hs
    have hcompose : (fun pair : Index×(Fin dimension → Index) => mass pair.1*finiteProductMass dimension mass pair.2)=
        (finiteProductMass (dimension+1) mass) ∘ (Fin.consEquiv (fun _ : Fin (dimension+1) => Index)) := by
      funext pair
      simp only [Function.comp_apply,Fin.consEquiv,Equiv.coe_fn_mk,finiteProductMass,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
    rw [hcompose] at hp
    have h := (Fin.consEquiv (fun _ : Fin (dimension+1) => Index)).hasSum_iff.mp hp
    simpa only [pow_succ,mul_comm] using h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule45

/- Helper module Solutions.RegevBridgeDependentProductMass. -/
section P2MDyadicModule46

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open scoped BigOperators

noncomputable section

/-- Full jointly independent countable family normalization, allowing
coordinate-dependent channels and output tests in every factor. -/
theorem dependentProductMass_hasSum {Index : Type*} (dimension : ℕ)
    (mass : Fin dimension → Index → ℝ)
    (hnonnegative : ∀ index value,0 ≤ mass index value) (hsummable : ∀ index,Summable (mass index)) :
    HasSum (fun word : Fin dimension → Index => ∏ index,mass index (word index))
      (∏ index,∑' value,mass index value) := by
  classical
  induction dimension with
  | zero =>
    have heq : (fun word : Fin 0 → Index => ∏ index,mass index (word index))=(fun _ => (1 : ℝ)) := by
      funext word
      simp
    rw [heq]
    simpa only [Finset.univ_eq_empty,Finset.prod_empty,Fintype.sum_unique] using
      (hasSum_fintype (fun _ : Fin 0 → Index => (1 : ℝ)))
  | succ dimension ih =>
    have htail := ih (fun index => mass index.succ) (fun index => hnonnegative index.succ)
      (fun index => hsummable index.succ)
    have htailNonnegative (word : Fin dimension → Index) : 0 ≤ ∏ index,mass index.succ (word index) :=
      Finset.prod_nonneg (fun _ _ => hnonnegative _ _)
    have hs := (hsummable 0).mul_of_nonneg htail.summable (hnonnegative 0) htailNonnegative
    have hp := (hsummable 0).hasSum.mul htail hs
    have hcompose : (fun pair : Index×(Fin dimension → Index) => mass 0 pair.1*(∏ index,mass index.succ (pair.2 index)))=
        (fun word : Fin (dimension+1) → Index => ∏ index,mass index (word index)) ∘
          (Fin.consEquiv (fun _ : Fin (dimension+1) => Index)) := by
      funext pair
      simp only [Function.comp_apply,Fin.consEquiv,Equiv.coe_fn_mk,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
    rw [hcompose] at hp
    have h := (Fin.consEquiv (fun _ : Fin (dimension+1) => Index)).hasSum_iff.mp hp
    simpa only [Fin.prod_univ_succ] using h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule46

/- Helper module Solutions.RegevBridgeCountableProductChannel. -/
section P2MDyadicModule47

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open AFT

open scoped BigOperators

noncomputable section

/-- The literal full output table after independent finite kernels are
applied to the whole independent countable source pool. -/
def countableProductChannel {Source Output : Type*} [Fintype Output]
    (count : ℕ) (mass : Source → ℝ) (hnonnegative : ∀ source,0 ≤ mass source)
    (hsummable : Summable mass) (hmass : (∑' source,mass source)=1)
    (kernel : Fin count → Source → FiniteDist Output) : FiniteDist (Fin count → Output) :=
  FiniteDist.countableMix (finiteProductMass count mass) (finiteProductMass_nonnegative count mass hnonnegative)
    (finiteProductMass_hasSum count mass hnonnegative hsummable).summable
    (by rw [(finiteProductMass_hasSum count mass hnonnegative hsummable).tsum_eq,hmass,one_pow])
    (fun source => FiniteDist.independent (fun index => kernel index (source index)))

/-- Every joint table probability factors exactly; the statement is much
stronger than correctness of the separate output marginals. -/
theorem countableProductChannel_eq {Source Output : Type*} [Fintype Output]
    (count : ℕ) (mass : Source → ℝ) (hnonnegative : ∀ source,0 ≤ mass source)
    (hsummable : Summable mass) (hmass : (∑' source,mass source)=1)
    (kernel : Fin count → Source → FiniteDist Output) :
    countableProductChannel count mass hnonnegative hsummable hmass kernel=
      FiniteDist.independent (fun index => FiniteDist.countableMix mass hnonnegative hsummable hmass (kernel index)) := by
  classical
  ext output
  change (∑' source : Fin count → Source,
    (∏ index,mass (source index))*(∏ index,(kernel index (source index)).weight (output index)))=
    ∏ index,∑' source,mass source*(kernel index source).weight (output index)
  have hpoint (source : Fin count → Source) :
      (∏ index,mass (source index))*(∏ index,(kernel index (source index)).weight (output index))=
        ∏ index,mass (source index)*(kernel index (source index)).weight (output index) :=
    (Finset.prod_mul_distrib).symm
  simp_rw [hpoint]
  exact (dependentProductMass_hasSum count
    (fun index source => mass source*(kernel index source).weight (output index))
    (fun _ _ => mul_nonneg (hnonnegative _) ((kernel _ _).nonneg _))
    (fun index => FiniteDist.countableChannel_summable mass hsummable (kernel index) (output index))).tsum_eq

/-- A common single-row error contributes once per actual fresh table row. -/
theorem countableProductChannel_l1 {Source Output : Type*} [Fintype Output]
    (count : ℕ) (mass : Source → ℝ) (hnonnegative : ∀ source,0 ≤ mass source)
    (hsummable : Summable mass) (hmass : (∑' source,mass source)=1)
    (kernel : Fin count → Source → FiniteDist Output) (ideal : Fin count → FiniteDist Output)
    (error : ℝ)
    (herror : ∀ index,(∑ output,|(FiniteDist.countableMix mass hnonnegative hsummable hmass (kernel index)).weight output-
      (ideal index).weight output|)/2 ≤ error) :
    (∑ table,|(countableProductChannel count mass hnonnegative hsummable hmass kernel).weight table-
      (FiniteDist.independent ideal).weight table|)/2 ≤ count*error := by
  rw [countableProductChannel_eq]
  have h := FiniteDist.l1_independent_fin_le count
    (fun index => FiniteDist.countableMix mass hnonnegative hsummable hmass (kernel index)) ideal
  have hb : (∑ index : Fin count,∑ output,|(FiniteDist.countableMix mass hnonnegative hsummable hmass (kernel index)).weight output-
      (ideal index).weight output|) ≤ (count : ℝ)*(2*error) := by
    calc
      _ ≤ ∑ _index : Fin count,2*error := Finset.sum_le_sum (fun index _ => by linarith [herror index])
      _ = _ := by simp
  linarith

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule47

/- Helper module Solutions.RegevBridgeGaussianCosetPartition. -/
section P2MDyadicModule48

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

open AFT GaussianSource RegevLWE.GaussConv

open scoped BigOperators Classical

noncomputable section

variable {dimension : ℕ} {Index : Type*} [Fintype Index] [DecidableEq Index]

/-- Exact partition of L by its actual input-basis residue vector. -/
def partitionEquiv (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (basis : Module.Basis Index ℤ lattice) : lattice ≃ (Index → ZMod q) × modulusLattice q lattice where
  toFun value :=
    let color := publicCoordinates q lattice basis value
    (color,⟨((value-lift q lattice basis color : lattice) : Space (dimension:=dimension)),
      (publicCoordinates_fiber q lattice basis color value).mp rfl⟩)
  invFun pair := sample q lattice (lift q lattice basis pair.1) pair.2
  left_inv value := by
    apply Subtype.ext
    change ((value : Space (dimension:=dimension))-(lift q lattice basis (publicCoordinates q lattice basis value) : Space (dimension:=dimension)))+
      (lift q lattice basis (publicCoordinates q lattice basis value) : Space (dimension:=dimension))=(value : Space (dimension:=dimension))
    abel
  right_inv pair := by
    rcases pair with ⟨color,value⟩
    have hc := (publicCoordinates_sample q lattice basis (lift q lattice basis color) value).trans
      (publicCoordinates_lift q lattice basis color)
    apply Prod.ext
    · exact hc
    · apply Subtype.ext
      change ((sample q lattice (lift q lattice basis color) value : Space (dimension:=dimension))-
        (lift q lattice basis (publicCoordinates q lattice basis (sample q lattice (lift q lattice basis color) value)) : Space (dimension:=dimension)))=
        (value : Space (dimension:=dimension))
      rw [hc]
      change ((value : Space (dimension:=dimension))+(lift q lattice basis color : Space (dimension:=dimension)))-
        (lift q lattice basis color : Space (dimension:=dimension))=(value : Space (dimension:=dimension))
      abel

omit [DecidableEq Index] in
theorem partitionEquiv_public_symm (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (basis : Module.Basis Index ℤ lattice) (pair : (Index → ZMod q) × modulusLattice q lattice) :
    publicCoordinates q lattice basis ((partitionEquiv q lattice basis).symm pair)=pair.1 := by
  exact congrArg Prod.fst ((partitionEquiv q lattice basis).apply_symm_apply pair)

/-- The true public coefficient law of the original lattice Gaussian. -/
def coefficientLaw (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (basis : Module.Basis Index ℤ lattice) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width) :
    FiniteDist (Index → ZMod q) :=
  finiteLaw ((cosetPMF lattice 0 hwidth herror herrorOne hsmoothing).map (publicCoordinates q lattice basis))

/-- Every public point mass is the actual qL-coset Gaussian mass divided
by the original lattice normalizer. No coset probability is assumed. -/
theorem coefficientLaw_weight (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (basis : Module.Basis Index ℤ lattice) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width)
    (color : Index → ZMod q) :
    (coefficientLaw q lattice basis hwidth herror herrorOne hsmoothing).weight color=
      rhoCoset width (modulusLattice q lattice) (lift q lattice basis color : Space (dimension:=dimension))/rhoCoset width lattice 0 := by
  classical
  let source := cosetPMF lattice 0 hwidth herror herrorOne hsmoothing
  let function : lattice → ℝ := fun value =>
    if publicCoordinates q lattice basis value=color then (source value).toReal else 0
  have hfunction : Summable function := by
    apply Summable.of_nonneg_of_le _ _ (pmf_realMass_summable source)
    · intro value;dsimp only [function];split_ifs <;> positivity
    · intro value;dsimp only [function];split_ifs <;> simp [ENNReal.toReal_nonneg]
  let equivalence := partitionEquiv q lattice basis
  have hpairs : Summable (function ∘ equivalence.symm) := equivalence.symm.summable_iff.mpr hfunction
  change Summable (fun pair => function (equivalence.symm pair)) at hpairs
  have hreindex := equivalence.symm.tsum_eq function
  rw [hpairs.tsum_prod,tsum_fintype] at hreindex
  unfold coefficientLaw
  rw [Integration.finiteLaw_map_weight]
  suffices hfinal : (∑' value : lattice,function value)=
      rhoCoset width (modulusLattice q lattice) (lift q lattice basis color : Space (dimension:=dimension))/rhoCoset width lattice 0 by
    calc
      _ = ∑' value : lattice,function value := by
        apply tsum_congr
        intro value
        dsimp only [function,source]
        split_ifs <;> rfl
      _ = _ := hfinal
  rw [←hreindex]
  have hinner (selected : Index → ZMod q) :
      (∑' value : modulusLattice q lattice,function (equivalence.symm (selected,value)))=
      if selected=color then rhoCoset width (modulusLattice q lattice)
        (lift q lattice basis selected : Space (dimension:=dimension))/rhoCoset width lattice 0 else 0 := by
    have hpublic (value : modulusLattice q lattice) : publicCoordinates q lattice basis (equivalence.symm (selected,value))=selected :=
      partitionEquiv_public_symm q lattice basis (selected,value)
    dsimp only [function]
    simp_rw [hpublic]
    by_cases hc : selected=color
    · simp only [hc,ite_true]
      simp only [source,cosetPMF_toReal,cosetMass_formula,add_zero]
      rw [tsum_div_const]
      rfl
    · simp only [hc,ite_false,tsum_zero]
  simp_rw [hinner]
  simp

/-- The actual public residues of a wide lattice Gaussian are near uniform.
The common covolume scale is removed using both laws' true normalization,
so no determinant-index identity or unproved conditional law is needed. -/
theorem coefficientLaw_uniform (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (basis : Module.Basis Index ℤ lattice) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1)
    (hsmoothing : smoothingParam lattice error ≤ width)
    (hmodulus : smoothingParam (modulusLattice q lattice) error ≤ width) :
    (∑ color : Index → ZMod q, |(coefficientLaw q lattice basis hwidth herror herrorOne hsmoothing).weight color-
      (FiniteDist.uniform (Index → ZMod q)).weight color|)/2 ≤ error/(1-error) := by
  classical
  let actual := coefficientLaw q lattice basis hwidth herror herrorOne hsmoothing
  let reference := FiniteDist.uniform (Index → ZMod q)
  let mass := rhoCoset width lattice 0
  let main := width^dimension*(ZLattice.covolume (modulusLattice q lattice))⁻¹
  let scale := (Fintype.card (Index → ZMod q) : ℝ)*main/mass
  have hmass : 0 < mass := rhoCoset_pos_of_smoothing lattice 0 hwidth herror herrorOne hsmoothing
  have hcard : (Fintype.card (Index → ZMod q) : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hscaled (color : Index → ZMod q) : scale*reference.weight color=main/mass := by
    change ((Fintype.card (Index → ZMod q) : ℝ)*main/mass)*(Fintype.card (Index → ZMod q) : ℝ)⁻¹=main/mass
    field_simp
  have hpoint (color : Index → ZMod q) : |actual.weight color-scale*reference.weight color| ≤
      error*scale*reference.weight color := by
    rw [mul_assoc error scale,hscaled]
    change |(coefficientLaw q lattice basis hwidth herror herrorOne hsmoothing).weight color-main/mass| ≤ error*(main/mass)
    rw [coefficientLaw_weight,←sub_div,abs_div,abs_of_pos hmass]
    have h := div_le_div_of_nonneg_right
      (claim_3_8 (modulusLattice q lattice) (lift q lattice basis color : Space (dimension:=dimension)) herror hwidth hmodulus) hmass.le
    simpa only [main,mul_div_assoc] using h
  have h := normalized_tilt_total_variation reference.weight actual.weight reference.nonneg
    (hasSum_fintype _).summable (hasSum_fintype _).summable
    (by rw [tsum_fintype];exact reference.sum_one)
    (by rw [tsum_fintype];exact actual.sum_one) scale error herror.le herrorOne hpoint
  simpa only [tsum_fintype] using h

/-- The original quantitative BDD smoothing condition simultaneously
justifies the true source Gaussian and every qL conditional experiment. -/
theorem source_and_modulus_smoothing (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    {width error : ℝ} (hwidth : 0<width) (herror : 0<error)
    (hsmoothing : smoothingParam lattice error ≤ width/(Real.sqrt 2*(q : ℝ))) :
    smoothingParam lattice error ≤ width ∧
      smoothingParam (modulusLattice q lattice) error ≤ width/Real.sqrt 2 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q from NeZero.one_le)
  have hroot : (1 : ℝ) ≤ Real.sqrt 2 := by apply Real.le_sqrt_of_sq_le;norm_num
  have hproduct : (1 : ℝ) ≤ Real.sqrt 2*(q : ℝ) := by nlinarith
  exact ⟨hsmoothing.trans (div_le_self hwidth.le hproduct),
    dilation_bdd_smoothing lattice q width error (by exact_mod_cast NeZero.pos q) hwidth herror hsmoothing⟩

/-- Exact mass disintegration on the proved partition: the conditional
source is the genuine qL-coset Gaussian, not an independent surrogate. -/
theorem coefficientLaw_conditional_factorization (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (basis : Module.Basis Index ℤ lattice) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1)
    (hsmoothing : smoothingParam lattice error ≤ width)
    (hmodulus : smoothingParam (modulusLattice q lattice) error ≤ width)
    (color : Index → ZMod q) (value : modulusLattice q lattice) :
    (cosetPMF lattice 0 hwidth herror herrorOne hsmoothing (sample q lattice (lift q lattice basis color) value)).toReal=
      (coefficientLaw q lattice basis hwidth herror herrorOne hsmoothing).weight color*
        (cosetPMF (modulusLattice q lattice) (lift q lattice basis color : Space (dimension:=dimension))
          hwidth herror herrorOne hmodulus value).toReal := by
  rw [coefficientLaw_weight]
  simp only [cosetPMF_toReal,cosetMass_formula,add_zero]
  change rho width ((value : Space (dimension:=dimension))+(lift q lattice basis color : Space (dimension:=dimension)))/rhoCoset width lattice 0=
    (rhoCoset width (modulusLattice q lattice) (lift q lattice basis color : Space (dimension:=dimension))/rhoCoset width lattice 0)*
      (rho width ((value : Space (dimension:=dimension))+(lift q lattice basis color : Space (dimension:=dimension)))/
        rhoCoset width (modulusLattice q lattice) (lift q lattice basis color : Space (dimension:=dimension)))
  have hp := (rhoCoset_pos_of_smoothing (modulusLattice q lattice) (lift q lattice basis color : Space (dimension:=dimension))
    hwidth herror herrorOne hmodulus).ne'
  field_simp

/-- Full disintegration commutes with every actual finite output kernel,
including kernels whose hidden-center parameters depend on the sample. -/
theorem countableMix_coset_partition {Output : Type*} [Fintype Output]
    (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (basis : Module.Basis Index ℤ lattice) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1)
    (hsmoothing : smoothingParam lattice error ≤ width)
    (hmodulus : smoothingParam (modulusLattice q lattice) error ≤ width)
    (kernel : lattice → FiniteDist Output) :
    GaussianRandomizedRounding.countableMix (cosetPMF lattice 0 hwidth herror herrorOne hsmoothing) kernel=
      (coefficientLaw q lattice basis hwidth herror herrorOne hsmoothing).mix (fun color =>
        GaussianRandomizedRounding.countableMix (cosetPMF (modulusLattice q lattice)
          (lift q lattice basis color : Space (dimension:=dimension)) hwidth herror herrorOne hmodulus)
          (fun value => kernel (sample q lattice (lift q lattice basis color) value))) := by
  classical
  let source := cosetPMF lattice 0 hwidth herror herrorOne hsmoothing
  let equivalence := partitionEquiv q lattice basis
  ext output
  have hs := GaussianRandomizedRounding.summable_countable_kernel source kernel output
  have hpairs := equivalence.symm.summable_iff.mpr hs
  have hreindex := equivalence.symm.tsum_eq (fun value => (source value).toReal*(kernel value).weight output)
  change Summable (fun pair => (source (equivalence.symm pair)).toReal*(kernel (equivalence.symm pair)).weight output) at hpairs
  rw [hpairs.tsum_prod,tsum_fintype] at hreindex
  change (∑' value : lattice,(source value).toReal*(kernel value).weight output)=_
  rw [←hreindex,FiniteDist.mix_weight]
  apply Finset.sum_congr rfl
  intro color _
  change (∑' value : modulusLattice q lattice,
    (cosetPMF lattice 0 hwidth herror herrorOne hsmoothing (sample q lattice (lift q lattice basis color) value)).toReal*
      (kernel (sample q lattice (lift q lattice basis color) value)).weight output)=_
  simp_rw [coefficientLaw_conditional_factorization q lattice basis hwidth herror herrorOne hsmoothing hmodulus,mul_assoc]
  rw [tsum_mul_left]
  rfl

end

end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

end P2MDyadicModule48

/- Helper module Solutions.RegevBridgeGaussianNativeSecretShift. -/
section P2MDyadicModule49

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

open AFT GaussianSource RegevLWE.GaussConv GaussianRandomizedRounding

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

/-- Integer translation equivariance holds for the actual native program,
including its rational numerical approximation and the same finite tape. -/
theorem native_output_translate (squaredWidth center : ℚ) (shift : ℤ) (cutoff bits : ℕ)
    (hwidth : 1 ≤ squaredWidth) (word : Fin ((bits+1)+(2*cutoff+1)+1) → Fin 2) :
    Native.output (Native.numericalRequest squaredWidth (center+shift) cutoff bits word)=
      Native.output (Native.numericalRequest squaredWidth center cutoff bits word)+shift := by
  rw [Native.output_numerical squaredWidth (center+shift) cutoff bits hwidth,
    Native.output_numerical squaredWidth center cutoff bits hwidth]
  exact finiteDraw_translate squaredWidth center shift cutoff bits word

/-- This hidden centering is used only in the analysis of the executed
query-center program. The program never receives the nearest lattice point. -/
def errorCenter (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (nearest : dual lattice) (center : lattice → ℚ) (value : lattice) : ℚ :=
  center value-(pairing lattice nearest value : ℚ)

theorem errorCenter_spec (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (nearest : dual lattice) (query : Space (dimension:=dimension)) (center : lattice → ℚ)
    (hcenter : ∀ value : lattice,(center value : ℝ)=inner ℝ query (value : Space (dimension:=dimension))) (value : lattice) :
    (errorCenter lattice nearest center value : ℝ)=
      inner ℝ (query-(nearest : Space (dimension:=dimension))) (value : Space (dimension:=dimension)) := by
  unfold errorCenter
  push_cast
  rw [hcenter,pairing_spec,inner_sub_left]

/-- Exact pathwise secret-plus-error identity for every original lattice
sample. It holds before taking any probability or invoking smoothing. -/
theorem native_query_secret_shift (q : ℕ) (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (nearest : dual lattice) (center : lattice → ℚ) (squaredWidth : ℚ) (hwidth : 1 ≤ squaredWidth)
    (cutoff bits : ℕ) (value : lattice) (word : Fin ((bits+1)+(2*cutoff+1)+1) → Fin 2) :
    (Native.output (Native.numericalRequest squaredWidth (center value) cutoff bits word) : ZMod q)=
      (pairing lattice nearest value : ZMod q)+
        (Native.output (Native.numericalRequest squaredWidth (errorCenter lattice nearest center value) cutoff bits word) : ZMod q) := by
  have hcenter : center value=errorCenter lattice nearest center value+(pairing lattice nearest value : ℚ) := by
    unfold errorCenter;ring
  rw [hcenter,native_output_translate squaredWidth _ _ cutoff bits hwidth,Int.cast_add]
  exact add_comm _ _

/-- On a fixed public residue fiber the secret term is constant; all
remaining randomness is exactly the executed error-center kernel. -/
theorem native_coset_secret_shift (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (nearest : dual lattice)
    (center : lattice → ℚ) (squaredWidth : ℚ) (hwidth : 1 ≤ squaredWidth)
    (cutoff bits : ℕ) (shift : lattice) (value : modulusLattice q lattice)
    (word : Fin ((bits+1)+(2*cutoff+1)+1) → Fin 2) :
    (Native.output (Native.numericalRequest squaredWidth (center (sample q lattice shift value)) cutoff bits word) : ZMod q)=
      (pairing lattice nearest shift : ZMod q)+
        (Native.output (Native.numericalRequest squaredWidth (errorCenter lattice nearest center (sample q lattice shift value)) cutoff bits word) : ZMod q) := by
  rw [native_query_secret_shift q lattice nearest center squaredWidth hwidth cutoff bits (sample q lattice shift value) word,
    pairing_mod_coset q lattice nearest shift value]

/-- The constant secret term is the actual input-basis LWE dot product. -/
theorem native_basis_secret_shift {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice)
    (nearest : dual lattice) (center : lattice → ℚ) (squaredWidth : ℚ) (hwidth : 1 ≤ squaredWidth)
    (cutoff bits : ℕ) (color : Index → ZMod q) (value : modulusLattice q lattice)
    (word : Fin ((bits+1)+(2*cutoff+1)+1) → Fin 2) :
    (Native.output (Native.numericalRequest squaredWidth (center (sample q lattice (lift q lattice basis color) value)) cutoff bits word) : ZMod q)=
      (∑ index,secretCoordinates q lattice basis nearest index*color index)+
        (Native.output (Native.numericalRequest squaredWidth (errorCenter lattice nearest center (sample q lattice (lift q lattice basis color) value)) cutoff bits word) : ZMod q) := by
  rw [native_coset_secret_shift q lattice nearest center squaredWidth hwidth cutoff bits (lift q lattice basis color) value word,
    pairing_mod_basis q lattice basis nearest (lift q lattice basis color),publicCoordinates_lift]

end

end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

end P2MDyadicModule49

/- Helper module Solutions.RegevBridgeGaussianRoundingTable. -/
section P2MDyadicModule50

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding

open AFT GaussianSource

open scoped BigOperators Classical

noncomputable section

/-- A shared source may correlate all centers. A uniform conditional
error bound survives mixing over its entire joint law. -/
theorem l1_mix_le_uniform {Source Output : Type*} [Fintype Source] [Fintype Output]
    (source : FiniteDist Source) (first second : Source → FiniteDist Output) (error : ℝ)
    (herror : ∀ input, (∑ result, |(first input).weight result-(second input).weight result|) ≤ error) :
    (∑ result, |(source.mix first).weight result-(source.mix second).weight result|) ≤ error := by
  simp only [FiniteDist.mix_weight,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ result,∑ input, source.weight input*|(first input).weight result-(second input).weight result| := by
      apply Finset.sum_le_sum
      intro result _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro input _
      rw [←mul_sub,abs_mul,abs_of_nonneg (source.nonneg input)]
    _ = ∑ input,source.weight input*(∑ result, |(first input).weight result-(second input).weight result|) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ input,source.weight input*error := Finset.sum_le_sum (fun input _ =>
      mul_le_mul_of_nonneg_left (herror input) (source.nonneg input))
    _ = error := by rw [←Finset.sum_mul,source.sum_one,one_mul]

end

namespace Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

end Native

end InfoLossLAR.WorstCase.GaussianRandomizedRounding

end P2MDyadicModule50

/- Helper module Solutions.RegevBridgeGaussianLWEGeneration. -/
section P2MDyadicModule51

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

open AFT GaussianSource RegevLWE.GaussConv GaussianRandomizedRounding

open scoped BigOperators Classical

noncomputable section

variable {dimension : ℕ}

/-- Finite postprocessing commutes with the actual countable-source law. -/
theorem countableMix_map {State Output Image : Type*} [Fintype Output] [Fintype Image]
    (source : PMF State) (kernel : State → FiniteDist Output) (image : Output → Image) :
    (countableMix source kernel).map image=countableMix source (fun state => (kernel state).map image) := by
  classical
  ext output
  change (∑ result,if image result=output then
    ∑' state,(source state).toReal*(kernel state).weight result else 0)=
      ∑' state,(source state).toReal*(∑ result,if image result=output then (kernel state).weight result else 0)
  calc
    _ = ∑ result,∑' state,(source state).toReal*(if image result=output then (kernel state).weight result else 0) := by
      apply Finset.sum_congr rfl
      intro result _
      by_cases h : image result=output <;> simp only [h,ite_true,ite_false,mul_zero,tsum_zero]
    _ = ∑' state,∑ result,(source state).toReal*(if image result=output then (kernel state).weight result else 0) := by
      symm
      apply Summable.tsum_finsetSum
      intro result _
      by_cases h : image result=output
      · simpa only [h,ite_true] using summable_countable_kernel source kernel result
      · simp only [h,ite_false,mul_zero];exact summable_zero
    _ = _ := by simp only [Finset.mul_sum]

/-- Actual classical postprocessing of one lattice-Gaussian sample and a
fresh finite tape. All public coefficients use the supplied input basis. -/
def nativeLWELaw {Index : Type*} [Fintype Index] [DecidableEq Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice)
    (source : PMF lattice) (squaredWidth : ℚ) (center : lattice → ℚ) (cutoff bits : ℕ) :
    FiniteDist ((Index → ZMod q) × ZMod q) :=
  countableMix source (fun value =>
    (FiniteDist.independent (fun _ : Fin ((bits+1)+(2*cutoff+1)+1) => FiniteDist.uniform (Fin 2))).map
      (fun word => (publicCoordinates q lattice basis value,
        (Native.output (Native.numericalRequest squaredWidth (center value) cutoff bits word) : ZMod q))))

/-- The finite conditional joint law is exactly its analyzed error law
followed by adding the fixed input-basis secret dot product. -/
theorem native_coset_joint {Index : Type*} [Fintype Index] [DecidableEq Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice)
    (nearest : dual lattice) (source : PMF (modulusLattice q lattice))
    (center : lattice → ℚ) (squaredWidth : ℚ) (hwidth : 1 ≤ squaredWidth)
    (cutoff bits : ℕ) (color : Index → ZMod q) :
    countableMix source (fun value =>
      (FiniteDist.independent (fun _ : Fin ((bits+1)+(2*cutoff+1)+1) => FiniteDist.uniform (Fin 2))).map
        (fun word => (publicCoordinates q lattice basis (sample q lattice (lift q lattice basis color) value),
          (Native.output (Native.numericalRequest squaredWidth (center (sample q lattice (lift q lattice basis color) value)) cutoff bits word) : ZMod q))))=
      (VarianceGrid.sampleLaw source q squaredWidth
        (fun value => errorCenter lattice nearest center (sample q lattice (lift q lattice basis color) value)) cutoff bits).map
          (fun output => (color,(∑ index,secretCoordinates q lattice basis nearest index*color index)+output)) := by
  rw [VarianceGrid.sampleLaw,countableMix_map]
  apply congrArg (countableMix source)
  funext value
  rw [FiniteDist.map_map]
  apply congrArg (FiniteDist.independent (fun _ : Fin ((bits+1)+(2*cutoff+1)+1) => FiniteDist.uniform (Fin 2))).map
  funext word
  apply Prod.ext
  · exact (publicCoordinates_sample q lattice basis (lift q lattice basis color) value).trans (publicCoordinates_lift q lattice basis color)
  · exact native_basis_secret_shift q lattice basis nearest center squaredWidth hwidth cutoff bits color value word

end

end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

end P2MDyadicModule51

/- Helper module Solutions.RegevBridgeIntegerBasis. -/
section P2MDyadicModule52

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open scoped BigOperators

open GaussianProjection

noncomputable section

variable {dimension : ℕ}

theorem integerBasis_apply (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) (index : Fin dimension) :
    (integerBasis basis hdet index : Space (dimension:=dimension))=WithLp.toLp 2 (fun row => (basis row index : ℝ)) := by
  exact (Module.Basis.restrictScalars_apply ℤ (realBasis basis hdet) index).trans (realBasis_apply basis hdet index)

/-- The coefficient vector sent to the native program represents exactly
its target-defined lattice point `latVec basis value`. -/
theorem coefficient_point (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (value : Fin dimension → ℤ) :
    ((integerBasis basis hdet).equivFun.symm value : Space (dimension:=dimension))=latVec basis value := by
  rw [Module.Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum,Submodule.coe_smul,integerBasis_apply]
  ext row
  simp only [WithLp.ofLp_sum,WithLp.ofLp_smul,WithLp.ofLp_toLp,Finset.sum_apply,latVec,Matrix.mulVec,dotProduct,
    Int.cast_sum,Int.cast_mul,zsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro index _
  exact mul_comm _ _

theorem projection_spec (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (query : Fin dimension → ℚ) (value : Fin dimension → ℤ) :
    (projection basis query value : ℝ)=inner ℝ (rationalPoint query) (latVec basis value) := by
  unfold projection rationalPoint latVec
  rw [PiLp.inner_apply]
  push_cast
  simp only [Real.inner_apply]

/-- The center supplied to the real analyzed source is exactly rational,
computed from its original input-basis integer coefficients. -/
def exactCenter (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (query : Fin dimension → ℚ) (value : inputLattice basis hdet) : ℚ :=
  projection basis query ((integerBasis basis hdet).equivFun value)

theorem exactCenter_spec (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (query : Fin dimension → ℚ) (value : inputLattice basis hdet) :
    (exactCenter basis hdet query value : ℝ)=inner ℝ (rationalPoint query) (value : Space (dimension:=dimension)) := by
  unfold exactCenter
  rw [projection_spec]
  have h := coefficient_point basis hdet ((integerBasis basis hdet).equivFun value)
  rw [LinearEquiv.symm_apply_apply] at h
  rw [←h]

end

end InfoLossLAR.WorstCase.IntegerBasis

end P2MDyadicModule52

/- Helper module Solutions.RegevBridgeIntegerBasisNative. -/
section P2MDyadicModule53

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis.Native

open AFT GaussianSource GaussianProjection GaussianRandomizedRounding BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

private theorem zip_ofFn {α β : Type*} {count : ℕ} (left : Fin count → α) (right : Fin count → β) :
    (List.ofFn left).zip (List.ofFn right)=List.ofFn (fun index => (left index,right index)) := by
  apply List.ext_getElem
  · simp
  · intros;simp

theorem dot_ofFn {count : ℕ} (left : Fin count → ℚ) (right : Fin count → ℤ) :
    dot (List.ofFn left,List.ofFn right)=∑ index,left index*(right index : ℚ) := by
  simp only [dot,zip_ofFn,List.map_ofFn,List.sum_ofFn,Function.comp_apply]

theorem matrixApply_ofFn {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (value : Fin dimension → ℤ) :
    matrixApply (List.ofFn (fun row => List.ofFn (basis row)),List.ofFn value)=List.ofFn (basis.mulVec value) := by
  simp only [matrixApply,List.map_ofFn]
  apply congrArg List.ofFn
  funext row
  simp only [Function.comp_apply,Integration9_9.TM2NativeAffineApply.dot,zip_ofFn,List.map_ofFn,List.sum_ofFn]
  rfl

theorem projection_ofFn {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (value : Fin dimension → ℤ) (query : Fin dimension → ℚ) :
    projection ((List.ofFn (fun row => List.ofFn (basis row)),List.ofFn value),List.ofFn query)=
      IntegerBasis.projection basis query value := by
  rw [projection,matrixApply_ofFn,dot_ofFn]
  rfl

/-- Signed modular output agrees exactly with the target ZMod encoding. -/
theorem residue_cast (q : ℕ) [NeZero q] (value : ℤ) : (residue (value,q) : ZMod q)=(value : ZMod q) := by
  unfold residue
  by_cases hnegative : value<0
  · simp only [hnegative,ite_true,ZMod.natCast_mod]
    rw [Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt value.natAbs (NeZero.pos q)))]
    simp only [ZMod.natCast_self,zero_sub,ZMod.natCast_mod]
    rw [←Int.cast_natCast,Int.natCast_natAbs,abs_of_neg hnegative,Int.cast_neg,neg_neg]
  · simp only [hnegative,ite_false,ZMod.natCast_mod]
    rw [←Int.cast_natCast,Int.natCast_natAbs,abs_of_nonneg (le_of_not_gt hnegative)]

theorem residue_value (q : ℕ) [NeZero q] (value : ℤ) : residue (value,q)=(value : ZMod q).val := by
  have hless : residue (value,q)<q := by
    unfold residue
    split_ifs <;> exact Nat.mod_lt _ (NeZero.pos q)
  have h := congrArg ZMod.val (residue_cast q value)
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hless] using h

theorem roundingRequest_numerical {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (value : Fin dimension → ℤ) (query : Fin dimension → ℚ) (q : ℕ) (squaredWidth : ℚ)
    (cutoff bits : ℕ) (word : Fin ((bits+1)+(2*cutoff+1)+1) → Fin 2) :
    roundingRequest (numericalRequest basis value query q squaredWidth cutoff bits word)=
      GaussianRandomizedRounding.Native.numericalRequest squaredWidth (IntegerBasis.projection basis query value) cutoff bits word := by
  simp only [roundingRequest,numericalRequest,projection_ofFn]
  rfl

/-- Exact literal machine semantics on every finite random tape. -/
theorem output_numerical {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (value : Fin dimension → ℤ) (query : Fin dimension → ℚ) (q : ℕ) [NeZero q] (squaredWidth : ℚ)
    (hwidth : 1 ≤ squaredWidth) (cutoff bits : ℕ) (word : Fin ((bits+1)+(2*cutoff+1)+1) → Fin 2) :
    output (numericalRequest basis value query q squaredWidth cutoff bits word)=
      (List.ofFn (fun index => (value index : ZMod q).val),
        (finiteDraw squaredWidth (IntegerBasis.projection basis query value) cutoff bits word : ZMod q).val) := by
  unfold output
  rw [roundingRequest_numerical,GaussianRandomizedRounding.Native.output_numerical squaredWidth _ cutoff bits hwidth]
  simp only [numericalRequest,List.map_ofFn,residue_value]
  rfl

theorem decodeSample_numerical {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (value : Fin dimension → ℤ) (query : Fin dimension → ℚ) (q : ℕ) [NeZero q] (squaredWidth : ℚ)
    (hwidth : 1 ≤ squaredWidth) (cutoff bits : ℕ) (word : Fin ((bits+1)+(2*cutoff+1)+1) → Fin 2) :
    decodeSample dimension q (output (numericalRequest basis value query q squaredWidth cutoff bits word))=
      ((fun index => (value index : ZMod q)),
        (finiteDraw squaredWidth (IntegerBasis.projection basis query value) cutoff bits word : ZMod q)) := by
  rw [output_numerical basis value query q squaredWidth hwidth]
  apply Prod.ext
  · funext index
    simp [decodeSample,List.getD_eq_getElem?_getD]
  · exact ZMod.natCast_zmod_val _

/-- The actual native binary program's finite observed sample law when
its integer coefficient input comes from the given lattice source. -/
noncomputable def sourceLaw {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (source : PMF (inputLattice basis hdet)) (query : Fin dimension → ℚ) (q : ℕ) [NeZero q]
    (squaredWidth : ℚ) (cutoff bits : ℕ) : AFT.FiniteDist ((Fin dimension → ZMod q) × ZMod q) :=
  countableMix source (fun value =>
    (AFT.FiniteDist.independent (fun _ : Fin ((bits+1)+(2*cutoff+1)+1) => AFT.FiniteDist.uniform (Fin 2))).map
      (fun word => decodeSample dimension q (output (numericalRequest basis ((integerBasis basis hdet).equivFun value)
        query q squaredWidth cutoff bits word))))

/-- The proved distributional LWE guarantee refers to this literal native
program, with matrix multiplication, rational projection and signed
residues all computed by its certified encoded machines. -/
theorem sourceLaw_eq {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (source : PMF (inputLattice basis hdet)) (query : Fin dimension → ℚ) (q : ℕ) [NeZero q]
    (squaredWidth : ℚ) (hwidth : 1 ≤ squaredWidth) (cutoff bits : ℕ) :
    sourceLaw basis hdet source query q squaredWidth cutoff bits=
      CosetGeometry.nativeLWELaw q (inputLattice basis hdet) (integerBasis basis hdet) source squaredWidth
        (exactCenter basis hdet query) cutoff bits := by
  unfold sourceLaw CosetGeometry.nativeLWELaw
  apply congrArg (countableMix source)
  funext value
  apply congrArg (AFT.FiniteDist.independent (fun _ : Fin ((bits+1)+(2*cutoff+1)+1) => AFT.FiniteDist.uniform (Fin 2))).map
  funext word
  rw [decodeSample_numerical basis _ query q squaredWidth hwidth,
    GaussianRandomizedRounding.Native.output_numerical squaredWidth _ cutoff bits hwidth]
  rfl

end InfoLossLAR.WorstCase.IntegerBasis.Native

end P2MDyadicModule53

/- Helper module Solutions.RegevBridgeNativeLWETable. -/
section P2MDyadicModule54

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis.Native

open AFT GaussianSource GaussianProjection GaussianRandomizedRounding GaussianPoissonSeries

open scoped BigOperators

noncomputable section

/-- Complete native output table on the genuine iid lattice source pool.
Every row has independent rounding coins and retains the common query. -/
def sourceTableLaw {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (source : PMF (inputLattice basis hdet)) (query : Fin dimension → ℚ)
    (q count : ℕ) [NeZero q] (squaredWidth : ℚ) (cutoff bits : ℕ) :
    FiniteDist (Fin count → ((Fin dimension → ZMod q)×ZMod q)) :=
  countableProductChannel count (fun value => (source value).toReal) (fun _ => ENNReal.toReal_nonneg)
    (pmf_realMass_summable source) (pmf_realMass_sum source)
    (fun _ => sourceRowKernel basis hdet query q squaredWidth cutoff bits)

end

end InfoLossLAR.WorstCase.IntegerBasis.Native

end P2MDyadicModule54

/- Helper module Solutions.RegevBridgeGaussianNumericalBudget. -/
section P2MDyadicModule55

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

open AFT GaussianSource GaussianRandomizedRounding RegevLWE.GaussConv

open scoped BigOperators

noncomputable section

/-- The complete shifted-normalizer prefactor is uniformly bounded in
the actual wide-kernel regime, including its dependence on both widths. -/
theorem intervalTail_le_six {lower upper radius : ℝ} (hlower : 1 ≤ lower) :
    VarianceGrid.intervalTail lower upper radius ≤ 6*Real.exp (-Real.pi*radius^2/(2*upper^2)) := by
  have ht := roundingError_lt_half lower hlower
  have htzero := thetaError_nonneg lower (zero_lt_one.trans_le hlower)
  have hroot : Real.sqrt (2 : ℝ) ≤ 2 := by apply Real.sqrt_le_iff.mpr;norm_num
  have hden : 0<1-thetaError lower := by linarith
  have hnum : Real.sqrt 2*(1+thetaError lower) ≤ 3 := by nlinarith
  have hfactor : Real.sqrt 2*(1+thetaError lower)/(1-thetaError lower) ≤ 6 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  exact mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _)

/-- Elementary explicit exponential bound, before taking any asymptotic
limit. It also discharges the theta smallness premise at every sigma≥2. -/
theorem sigma_gaussian_exp_le (sigma : ℕ) (hsigma : 2 ≤ sigma) :
    Real.exp (-Real.pi*(sigma : ℝ)^2/2) ≤ 1/(2 : ℝ)^(2*sigma) := by
  have hs : (2 : ℝ) ≤ sigma := by exact_mod_cast hsigma
  have hp : (0 : ℝ)<sigma := by linarith
  have hquad : 2*(sigma : ℝ) ≤ Real.pi*(sigma : ℝ)^2/2 := by
    nlinarith [Real.pi_gt_three,sq_nonneg ((sigma : ℝ)-2)]
  have he : (2 : ℝ)^(2*sigma) ≤ Real.exp ((2*sigma : ℕ) : ℝ) := by
    have heq : Real.exp ((2*sigma : ℕ) : ℝ)=(Real.exp 1)^(2*sigma) := by
      rw [←Real.exp_nat_mul]
      simp only [mul_one]
    rw [heq]
    exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le _
  calc
    _ ≤ Real.exp (-((2*sigma : ℕ) : ℝ)) := by
      apply Real.exp_le_exp.mpr
      push_cast
      linarith
    _ = 1/Real.exp ((2*sigma : ℕ) : ℝ) := by rw [Real.exp_neg,one_div]
    _ ≤ _ := one_div_le_one_div_of_le (by positivity) he

/-- The source error need only be a fixed inverse polynomial. The kernel
smallness premise is automatic for epsilon≤1/8 and sigma≥2. -/
theorem sigma_theta_small (sigma : ℕ) (hsigma : 2 ≤ sigma) {error : ℝ} (herror : error ≤ 1/8) :
    2*error+3*thetaError ((sigma : ℝ)/Real.sqrt 2) ≤ 1 := by
  have hs : (2 : ℝ) ≤ sigma := by exact_mod_cast hsigma
  have hr : 0<Real.sqrt (2 : ℝ) := by positivity
  have hrTwo : Real.sqrt (2 : ℝ) ≤ 2 := by apply Real.sqrt_le_iff.mpr;norm_num
  have hlo : 1 ≤ (sigma : ℝ)/Real.sqrt 2 := (le_div_iff₀ hr).mpr (by linarith)
  have hloSq : ((sigma : ℝ)/Real.sqrt 2)^2=(sigma : ℝ)^2/2 := by
    rw [div_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have htheta := thetaError_le_four_exp ((sigma : ℝ)/Real.sqrt 2) hlo
  rw [hloSq] at htheta
  have heq : -Real.pi*((sigma : ℝ)^2/2)= -Real.pi*(sigma : ℝ)^2/2 := by ring
  rw [heq] at htheta
  have hpow : (16 : ℝ) ≤ 2^(2*sigma) := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 4 ≤ 2*sigma)
    norm_num at hh ⊢
    exact hh
  have hfrac := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<16) hpow
  have hb := sigma_gaussian_exp_le sigma hsigma
  nlinarith

end

end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

end P2MDyadicModule55

/- Helper module Solutions.RegevBridgeRationalGramSchmidt. -/
section P2MDyadicModule56

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open InnerProductSpace

open scoped BigOperators

abbrev QVector (dimension : ℕ) := Fin dimension → ℚ

abbrev Space (dimension : ℕ) := EuclideanSpace ℝ (Fin dimension)

def innerQ {dimension : ℕ} (left right : QVector dimension) : ℚ := ∑ index,left index*right index

def realVec {dimension : ℕ} (vector : QVector dimension) : Space dimension :=
  WithLp.toLp 2 (fun index => (vector index : ℝ))

theorem realVec_zero {dimension : ℕ} : realVec (0 : QVector dimension)=0 := by ext index;simp [realVec]

theorem realVec_add {dimension : ℕ} (left right : QVector dimension) : realVec (left+right)=realVec left+realVec right := by
  ext index
  exact Rat.cast_add _ _

theorem realVec_sub {dimension : ℕ} (left right : QVector dimension) : realVec (left-right)=realVec left-realVec right := by
  ext index
  exact Rat.cast_sub _ _

theorem realVec_smul {dimension : ℕ} (scalar : ℚ) (vector : QVector dimension) :
    realVec (scalar • vector)=(scalar : ℝ) • realVec vector := by
  ext index
  exact Rat.cast_mul _ _

theorem realVec_list_sum {dimension : ℕ} (vectors : List (QVector dimension)) :
    realVec vectors.sum=(vectors.map realVec).sum := by
  induction vectors with
  | nil => exact realVec_zero
  | cons head tail ih => simp only [List.sum_cons,List.map_cons,realVec_add,ih]

theorem innerQ_real {dimension : ℕ} (left right : QVector dimension) :
    (innerQ left right : ℝ)=inner ℝ (realVec left) (realVec right) := by
  unfold innerQ realVec
  rw [PiLp.inner_apply]
  push_cast
  simp only [Real.inner_apply]

/-- Every projection uses the original current vector and cached earlier
orthogonal vectors; the running algorithm never recomputes its recursion tree. -/
def projection {dimension : ℕ} (orthogonal current : QVector dimension) : QVector dimension :=
  (innerQ orthogonal current/innerQ orthogonal orthogonal) • orthogonal

def orthogonalStep {dimension : ℕ} (previous : List (QVector dimension)) (current : QVector dimension) : QVector dimension :=
  current-(previous.map (fun orthogonal => projection orthogonal current)).sum

/-- Materialized rational Gram--Schmidt cache. A finite input prefix is
processed exactly once; division by zero keeps malformed inputs total. -/
def cache {dimension count : ℕ} (vectors : Fin count → QVector dimension) : ℕ → List (QVector dimension)
  | 0 => []
  | steps+1 =>
      let previous := cache vectors steps
      let current := if h : steps<count then vectors ⟨steps,h⟩ else 0
      previous++[orthogonalStep previous current]

theorem cache_length {dimension count : ℕ} (vectors : Fin count → QVector dimension) (steps : ℕ) :
    (cache vectors steps).length=steps := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp only [cache,List.length_append,List.length_singleton,ih]

def orthogonal {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) : QVector dimension :=
  (cache vectors count).getD index.val 0

def squaredNorm {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) : ℚ := innerQ (orthogonal vectors index) (orthogonal vectors index)

noncomputable section

theorem projection_real {dimension : ℕ} (orthogonal current : QVector dimension) :
    realVec (projection orthogonal current)=
      (inner ℝ (realVec orthogonal) (realVec current)/‖realVec orthogonal‖^2) • realVec orthogonal := by
  rw [projection,realVec_smul,Rat.cast_div,innerQ_real,innerQ_real,real_inner_self_eq_norm_sq]

theorem orthogonalStep_real {dimension : ℕ} (previous : List (QVector dimension)) (current : QVector dimension) :
    realVec (orthogonalStep previous current)=realVec current-
      ((previous.map realVec).map (fun orthogonal => (inner ℝ orthogonal (realVec current)/‖orthogonal‖^2) • orthogonal)).sum := by
  rw [orthogonalStep,realVec_sub,realVec_list_sum]
  simp only [List.map_map,Function.comp_def,projection_real]

private theorem sum_Iio_fin {count : ℕ} {Value : Type*} [AddCommMonoid Value]
    (index : Fin count) (function : Fin count → Value) :
    (∑ previous ∈ Finset.Iio index,function previous)=
      ∑ previous : Fin index.val,function ⟨previous.val,previous.isLt.trans index.isLt⟩ := by
  classical
  refine Finset.sum_bij (fun previous membership =>
    (⟨previous.val,show previous < index from Finset.mem_Iio.mp membership⟩ : Fin index.val)) ?_ ?_ ?_ ?_
  · intro previous membership
    exact Finset.mem_univ _
  · intro first hfirst second hsecond hequal
    exact Fin.ext (congrArg (fun value : Fin index.val => value.val) hequal)
  · intro previous membership
    refine ⟨⟨previous.val,previous.isLt.trans index.isLt⟩,Finset.mem_Iio.mpr (show (⟨previous.val,previous.isLt.trans index.isLt⟩ : Fin count) < index from previous.isLt),?_⟩
    rfl
  · intro previous membership
    congr 1

/-- Every materialized rational cache prefix is exactly the ordinary real
Gram--Schmidt prefix after the actual rational-to-real embedding. -/
theorem cache_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (steps : ℕ) (hsteps : steps ≤ count) :
    (cache vectors steps).map realVec=List.ofFn (fun index : Fin steps =>
      gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hsteps index)) := by
  classical
  induction steps with
  | zero => rfl
  | succ steps ih =>
    have hprevious : steps ≤ count := by omega
    have hstep : steps<count := by omega
    let index : Fin count := ⟨steps,hstep⟩
    rw [cache,List.map_append,List.map_singleton,ih hprevious,List.ofFn_succ_last]
    apply congrArg₂ List.append
    · apply congrArg List.ofFn
      funext previous
      congr 1
    · apply congrArg (fun value : Space dimension => [value])
      change realVec (orthogonalStep (cache vectors steps) (if h : steps<count then vectors ⟨steps,h⟩ else 0))=
        gramSchmidt ℝ (fun position => realVec (vectors position)) index
      rw [dif_pos hstep,orthogonalStep_real,ih hprevious]
      simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def]
      have h := gramSchmidt_def'' ℝ (fun position => realVec (vectors position)) index
      rw [sum_Iio_fin] at h
      have hequal : (∑ previous : Fin steps,
          (inner ℝ (gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hprevious previous))
            (realVec (vectors index))/‖gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hprevious previous)‖^2) •
              gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hprevious previous))=
          ∑ previous : Fin index.val,
          (inner ℝ (gramSchmidt ℝ (fun position => realVec (vectors position)) ⟨previous.val,previous.isLt.trans index.isLt⟩)
            (realVec (vectors index))/‖gramSchmidt ℝ (fun position => realVec (vectors position)) ⟨previous.val,previous.isLt.trans index.isLt⟩‖^2) •
              gramSchmidt ℝ (fun position => realVec (vectors position)) ⟨previous.val,previous.isLt.trans index.isLt⟩ := rfl
      rw [hequal]
      exact sub_eq_iff_eq_add.mpr h

theorem orthogonal_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) :
    realVec (orthogonal vectors index)=gramSchmidt ℝ (fun position => realVec (vectors position)) index := by
  have h := congrArg (fun values : List (Space dimension) => values.getD index.val (realVec (0 : QVector dimension)))
    (cache_real vectors count (le_refl count))
  rw [List.getD_map] at h
  simpa [orthogonal,index.isLt] using h

theorem squaredNorm_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) :
    (squaredNorm vectors index : ℝ)=‖gramSchmidt ℝ (fun position => realVec (vectors position)) index‖^2 := by
  rw [squaredNorm,innerQ_real,orthogonal_real,real_inner_self_eq_norm_sq]

/-- Orthogonal projection only decreases the original column's square norm. -/
theorem gramSchmidt_norm_sq_le {dimension count : ℕ} (vectors : Fin count → Space dimension)
    (index : Fin count) :
    ‖gramSchmidt ℝ vectors index‖^2 ≤ ‖vectors index‖^2 := by
  let orthogonal := gramSchmidt ℝ vectors
  have heq : inner ℝ (orthogonal index) (vectors index)=inner ℝ (orthogonal index) (orthogonal index) := by
    conv_lhs => arg 3; rw [gramSchmidt_def'' ℝ vectors index]
    simp only [RCLike.ofReal_real_eq_id,id_eq]
    rw [inner_add_right]
    suffices inner ℝ (orthogonal index)
        (∑ previous ∈ Finset.Iio index,
          (inner ℝ (orthogonal previous) (vectors index)/‖orthogonal previous‖^2) • orthogonal previous)=0 by
      change inner ℝ (orthogonal index) (orthogonal index)+_=inner ℝ (orthogonal index) (orthogonal index)
      rw [this,add_zero]
    simp only [inner_sum,inner_smul_right]
    apply Finset.sum_eq_zero
    intro previous membership
    rw [gramSchmidt_orthogonal ℝ vectors (Finset.mem_Iio.mp membership).ne',mul_zero]
  have hnonneg := (real_inner_self_nonneg (x := vectors index-orthogonal index))
  rw [inner_sub_sub_self,real_inner_comm (orthogonal index) (vectors index),heq,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hnonneg
  change ‖orthogonal index‖^2 ≤ _
  linarith

theorem squaredNorm_le {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) :
    squaredNorm vectors index ≤ innerQ (vectors index) (vectors index) := by
  have h := gramSchmidt_norm_sq_le (fun position => realVec (vectors position)) index
  rw [←squaredNorm_real,←real_inner_self_eq_norm_sq,←innerQ_real] at h
  exact_mod_cast h

end

def inputVectors {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (column : Fin dimension) : QVector dimension := fun row => (basis row column : ℚ)

noncomputable section

theorem inputVectors_real {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (column : Fin dimension) :
    realVec (inputVectors basis column)=IntegerBasis.realBasis basis hdet column := by
  rw [IntegerBasis.realBasis_apply]
  ext row
  simp [realVec,inputVectors]

theorem inputVectors_independent {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) :
    LinearIndependent ℝ (fun position => realVec (inputVectors basis position)) := by
  simpa only [inputVectors_real basis hdet] using (IntegerBasis.realBasis basis hdet).linearIndependent

end

noncomputable section

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule56

/- Helper module Solutions.RegevBridgeRationalGramSchmidtGeometry. -/
section P2MDyadicModule57

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open InnerProductSpace

open scoped BigOperators

/-- Exact rational upper-triangular change from original input columns to
its materialized orthogonal cache. -/
def upper {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (row column : Fin count) : ℚ :=
  innerQ (orthogonal vectors row) (vectors column)/squaredNorm vectors row

noncomputable section

theorem inner_gramSchmidt_original {dimension count : ℕ} (vectors : Fin count → Space dimension)
    (index : Fin count) :
    inner ℝ (gramSchmidt ℝ vectors index) (vectors index)=‖gramSchmidt ℝ vectors index‖^2 := by
  conv_lhs => arg 3; rw [gramSchmidt_def'' ℝ vectors index]
  simp only [RCLike.ofReal_real_eq_id,id_eq]
  rw [inner_add_right]
  suffices inner ℝ (gramSchmidt ℝ vectors index)
      (∑ previous ∈ Finset.Iio index,
        (inner ℝ (gramSchmidt ℝ vectors previous) (vectors index)/‖gramSchmidt ℝ vectors previous‖^2) •
          gramSchmidt ℝ vectors previous)=0 by
    rw [this,add_zero,real_inner_self_eq_norm_sq]
  simp only [inner_sum,inner_smul_right]
  apply Finset.sum_eq_zero
  intro previous membership
  rw [gramSchmidt_orthogonal ℝ vectors (Finset.mem_Iio.mp membership).ne',mul_zero]

theorem upper_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (row column : Fin count) :
    (upper vectors row column : ℝ)=
      inner ℝ (gramSchmidt ℝ (fun index => realVec (vectors index)) row) (realVec (vectors column))/
        ‖gramSchmidt ℝ (fun index => realVec (vectors index)) row‖^2 := by
  rw [upper,Rat.cast_div,innerQ_real,orthogonal_real,squaredNorm_real]

theorem upper_diagonal {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (independent : LinearIndependent ℝ (fun index => realVec (vectors index))) (index : Fin count) :
    upper vectors index index=1 := by
  have hreal : (upper vectors index index : ℝ)=1 := by
    rw [upper_real,inner_gramSchmidt_original]
    exact div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero index independent)))
  exact_mod_cast hreal

theorem upper_triangular {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (row column : Fin count) (before : column < row) :
    upper vectors row column=0 := by
  have hreal : (upper vectors row column : ℝ)=0 := by
    rw [upper_real,gramSchmidt_inv_triangular ℝ (fun index => realVec (vectors index)) before,zero_div]
  exact_mod_cast hreal

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule57

/- Helper module Solutions.RegevBridgeWideGaussianFlatTapes. -/
section P2MDyadicModule58

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics

open scoped BigOperators

noncomputable section

theorem independent_uniform {Index Value : Type*} [Fintype Index] [DecidableEq Index]
    [Fintype Value] [Nonempty Value] :
    FiniteDist.independent (fun _ : Index => FiniteDist.uniform Value)=FiniteDist.uniform (Index → Value) := by
  ext word
  simp only [FiniteDist.independent,FiniteDist.uniform_weight,Finset.prod_const,Finset.card_univ,
    Fintype.card_fun,Nat.cast_pow,inv_pow]

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule58

/- Helper module Solutions.RegevBridgeFlatTrialParser. -/
section P2MDyadicModule59

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

/-- Pure integer-address parser correctness, separated from Gaussian
metadata so elaboration never expands a numerical width configuration. -/
theorem splitTrial_ofFn (proposal coin attempts total : ℕ) (hbits : attempts*(proposal+coin) ≤ total)
    (tape : Fin total → Bool) (attempt : Fin attempts) :
    splitTrial ((proposal,coin),(List.ofFn tape,attempt.val))=
      (List.ofFn (fun bit : Fin proposal => tape (Fin.castLE hbits
        (finProdFinEquiv (attempt,Fin.castAdd coin bit)))),
       List.ofFn (fun bit : Fin coin => tape (Fin.castLE hbits
        (finProdFinEquiv (attempt,Fin.natAdd proposal bit))))) := by
  let start := attempt.val*(proposal+coin)
  have hend : start+proposal+coin ≤ total := by
    have htrial := Nat.mul_le_mul_right (proposal+coin) (show attempt.val+1 ≤ attempts by omega)
    dsimp [start]
    nlinarith
  apply Prod.ext
  · apply List.ext_getElem
    · simp only [splitTrial,List.length_take,List.length_drop,List.length_ofFn]
      change min proposal (total-start)=proposal
      omega
    · intro bit hfirst hsecond
      simp only [splitTrial,List.getElem_take,List.getElem_drop,List.getElem_ofFn]
      apply congrArg tape
      apply Fin.ext
      simp only [Fin.val_castLE,finProdFinEquiv,Equiv.coe_fn_mk]
      dsimp [start]
      ac_rfl
  · apply List.ext_getElem
    · simp only [splitTrial,List.length_take,List.length_drop,List.length_ofFn]
      change min coin (total-start-proposal)=coin
      omega
    · intro bit hfirst hsecond
      simp only [splitTrial,List.getElem_take,List.getElem_drop,List.getElem_ofFn]
      apply congrArg tape
      apply Fin.ext
      simp only [Fin.val_castLE,finProdFinEquiv,Equiv.coe_fn_mk]
      dsimp [start]
      ac_rfl

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule59

/- Helper module Solutions.RegevBridgeGramDeterminant. -/
section P2MDyadicModule60

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open InnerProductSpace

open scoped BigOperators

def prefixGram {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) : Matrix (Fin steps) (Fin steps) ℤ :=
  fun first second => ∑ row,basis row (Fin.castLE hsteps first)*basis row (Fin.castLE hsteps second)

noncomputable section

theorem prefixGram_real {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) :
    (prefixGram basis steps hsteps).map (fun value => (value : ℝ))=
      Matrix.gram ℝ (fun index => realVec (inputVectors basis (Fin.castLE hsteps index))) := by
  ext first second
  simp only [prefixGram,Matrix.map_apply,Matrix.gram_apply,realVec,inputVectors,PiLp.inner_apply,
    Real.inner_apply,Int.cast_sum,Int.cast_mul,Rat.cast_intCast]

theorem prefixGram_det_ne_zero {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (steps : ℕ) (hsteps : steps ≤ dimension) :
    (prefixGram basis steps hsteps).det ≠ 0 := by
  have independent : LinearIndependent ℝ
      (fun index : Fin steps => realVec (inputVectors basis (Fin.castLE hsteps index))) :=
    (inputVectors_independent basis hdet).comp (Fin.castLE hsteps) (Fin.castLE_injective hsteps)
  have h := Matrix.det_gram_ne_zero_iff_linearIndependent.mpr independent
  rw [←prefixGram_real,←Int.cast_det] at h
  exact_mod_cast h

/-- The subtraction made by Gram--Schmidt lies in the span of precisely
the original earlier columns, not an assumed short basis. -/
theorem gramSchmidt_correction_mem_prefix {dimension count : ℕ}
    (vectors : Fin count → QVector dimension) (index : Fin count) :
    realVec (vectors index)-realVec (orthogonal vectors index) ∈
      Submodule.span ℝ (Set.range (fun previous : Fin index.val =>
        realVec (vectors ⟨previous.val,previous.isLt.trans index.isLt⟩))) := by
  classical
  let family := fun position => realVec (vectors position)
  have hset : Set.range (fun previous : Fin index.val =>
      realVec (vectors ⟨previous.val,previous.isLt.trans index.isLt⟩))=family '' Set.Iio index := by
    ext point
    constructor
    · rintro ⟨previous,rfl⟩
      refine ⟨⟨previous.val,previous.isLt.trans index.isLt⟩,?_,rfl⟩
      exact previous.isLt
    · rintro ⟨previous,hprevious,rfl⟩
      exact ⟨⟨previous.val,hprevious⟩,rfl⟩
  rw [hset,←span_gramSchmidt_Iio ℝ family index,orthogonal_real]
  have h := gramSchmidt_def'' ℝ family index
  have hcorrection : family index-gramSchmidt ℝ family index=
      ∑ previous ∈ Finset.Iio index,
        (inner ℝ (gramSchmidt ℝ family previous) (family index)/‖gramSchmidt ℝ family previous‖^2) •
          gramSchmidt ℝ family previous := by
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm,RCLike.ofReal_real_eq_id,id_eq] using h)
  change family index-gramSchmidt ℝ family index ∈ _
  rw [hcorrection]
  apply Submodule.sum_mem
  intro previous hprevious
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨previous,Finset.mem_Iio.mp hprevious,rfl⟩

end

def prefixPairing {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (index : Fin dimension) (previous : Fin index.val) : ℤ :=
  ∑ row,basis row ⟨previous.val,previous.isLt.trans index.isLt⟩*basis row index

def gramNumerator {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (index : Fin dimension) (row : Fin dimension) : ℤ :=
  (prefixGram basis index.val index.isLt.le).det*basis row index-
    ∑ previous : Fin index.val,
      Matrix.cramer (prefixGram basis index.val index.isLt.le) (prefixPairing basis index) previous*
        basis row ⟨previous.val,previous.isLt.trans index.isLt⟩

noncomputable section

/-- Multiplying the cached rational GS vector by the original integer
prefix-Gram determinant gives an explicitly integral Cramer numerator.
This is the denominator control needed for binary, rather than unit-cost,
complexity of the cached rational orthogonalization. -/
theorem gram_determinant_scales_orthogonal {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (index : Fin dimension) :
    ((prefixGram basis index.val index.isLt.le).det : ℚ) • orthogonal (inputVectors basis) index=
      fun row => (gramNumerator basis index row : ℚ) := by
  classical
  let previousColumn (previous : Fin index.val) : Fin dimension :=
    ⟨previous.val,previous.isLt.trans index.isLt⟩
  let family (previous : Fin index.val) := realVec (inputVectors basis (previousColumn previous))
  let gram := prefixGram basis index.val index.isLt.le
  let rhs := prefixPairing basis index
  let castGram := gram.map (fun value => (value : ℝ))
  obtain ⟨coefficients,hcoefficients⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (gramSchmidt_correction_mem_prefix (inputVectors basis) index)
  change (∑ previous,coefficients previous • family previous)=
    realVec (inputVectors basis index)-realVec (orthogonal (inputVectors basis) index) at hcoefficients
  have hinner (first second : Fin index.val) : inner ℝ (family first) (family second)=
      (gram first second : ℝ) := by
    simp only [family,previousColumn,realVec,inputVectors,PiLp.inner_apply,Real.inner_apply,
      gram,prefixGram,Int.cast_sum,Int.cast_mul,Rat.cast_intCast]
    rfl
  have htarget (previous : Fin index.val) :
      inner ℝ (family previous) (realVec (inputVectors basis index))=(rhs previous : ℝ) := by
    simp only [family,previousColumn,realVec,inputVectors,PiLp.inner_apply,Real.inner_apply,prefixPairing,rhs,
      Int.cast_sum,Int.cast_mul,Rat.cast_intCast]
  have horthogonal (previous : Fin index.val) :
      inner ℝ (family previous) (realVec (orthogonal (inputVectors basis) index))=0 := by
    rw [orthogonal_real,real_inner_comm]
    exact gramSchmidt_inv_triangular ℝ (fun position => realVec (inputVectors basis position)) previous.isLt
  have hlinear : castGram.mulVec coefficients=fun previous => (rhs previous : ℝ) := by
    funext previous
    have h := congrArg (fun vector : Space dimension => inner ℝ (family previous) vector) hcoefficients
    simp only [inner_sum,inner_smul_right,inner_sub_right,horthogonal,sub_zero,htarget,hinner] at h
    simpa only [Matrix.mulVec,dotProduct,castGram,Matrix.map_apply,mul_comm] using h
  have hcramer : Matrix.cramer castGram (fun previous => (rhs previous : ℝ))=
      (gram.det : ℝ) • coefficients := by
    rw [←hlinear,Matrix.cramer_eq_adjugate_mulVec,Matrix.mulVec_mulVec,Matrix.adjugate_mul,
      Matrix.smul_mulVec,Matrix.one_mulVec,←Int.cast_det]
  have hcramerCast (previous : Fin index.val) :
      Matrix.cramer castGram (fun position => (rhs position : ℝ)) previous=
        (Matrix.cramer gram rhs previous : ℝ) := by
    rw [Matrix.cramer_apply,Matrix.cramer_apply]
    have hmatrix : castGram.updateCol previous (fun position => (rhs position : ℝ))=
        (gram.updateCol previous rhs).map (fun value => (value : ℝ)) := by
      ext first second
      simp only [Matrix.updateCol_apply,Matrix.map_apply,castGram]
      split_ifs <;> rfl
    rw [hmatrix,←Int.cast_det]
  have hscaled : (gram.det : ℝ) • (∑ previous,coefficients previous • family previous)=
      ∑ previous,(Matrix.cramer gram rhs previous : ℝ) • family previous := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro previous _
    rw [smul_smul]
    have h := congrArg (fun values : Fin index.val → ℝ => values previous) hcramer
    simp only [Pi.smul_apply,smul_eq_mul,hcramerCast] at h
    rw [←h]
  have h := congrArg (fun vector : Space dimension => (gram.det : ℝ) • vector) hcoefficients
  change (gram.det : ℝ) • (∑ previous,coefficients previous • family previous)=_ at h
  rw [hscaled] at h
  ext row
  have hrow := congrArg (fun vector : Space dimension => vector row) h
  simp only [family,previousColumn,realVec,inputVectors,WithLp.ofLp_sum,WithLp.ofLp_smul,WithLp.ofLp_sub,Finset.sum_apply,
    Pi.smul_apply,Pi.sub_apply,smul_eq_mul,Rat.cast_intCast] at hrow
  change (gram.det : ℚ)*orthogonal (inputVectors basis) index row=(gramNumerator basis index row : ℚ)
  apply Rat.cast_injective (α:=ℝ)
  simp only [gramNumerator,Rat.cast_sub,Rat.cast_mul,Rat.cast_sum,Rat.cast_intCast,Int.cast_sub,Int.cast_mul,Int.cast_sum]
  change (gram.det : ℝ)*(orthogonal (inputVectors basis) index row : ℝ)=_
  dsimp [gram,rhs] at hrow ⊢
  linarith

theorem prefixGram_entry_bound {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) (bound : ℤ) (hbound : 0 ≤ bound)
    (hentries : ∀ row column,|basis row column| ≤ bound) (first second : Fin steps) :
    |prefixGram basis steps hsteps first second| ≤ (dimension : ℤ)*bound^2 := by
  unfold prefixGram
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ row,|basis row (Fin.castLE hsteps first)*basis row (Fin.castLE hsteps second)|) ≤
        ∑ _row : Fin dimension,bound^2 := by
      apply Finset.sum_le_sum
      intro row _
      rw [abs_mul,pow_two]
      exact mul_le_mul (hentries row _) (hentries row _) (abs_nonneg _) hbound
    _ = _ := by simp

/-- Every prefix determinant has a bound whose logarithm is polynomial
in the input dimension and the logarithmic entry bound. -/
theorem prefixGram_det_bound {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) (bound : ℤ) (hbound : 0 ≤ bound)
    (hentries : ∀ row column,|basis row column| ≤ bound) :
    |(prefixGram basis steps hsteps).det| ≤ (steps.factorial : ℤ)*((dimension : ℤ)*bound^2)^steps := by
  have h := Matrix.det_le (abv:=AbsoluteValue.abs)
    (prefixGram_entry_bound basis steps hsteps bound hbound hentries)
  simpa only [AbsoluteValue.abs_apply,Fintype.card_fin,nsmul_eq_mul] using h

/-- A uniform polynomial exponent bounds every integer prefix Gram
normalizer, directly from an entry bit bound of the original input. -/
theorem prefixGram_det_binary_bound {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) (height : ℕ)
    (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height) :
    |(prefixGram basis steps hsteps).det| ≤ (2 : ℤ)^((2*dimension+2*height)*dimension) := by
  have hdimension : (dimension : ℤ) ≤ 2^dimension := by
    exact_mod_cast (Nat.lt_two_pow_self (n:=dimension)).le
  have hstep : (steps : ℤ) ≤ 2^dimension := (by exact_mod_cast hsteps : (steps : ℤ) ≤ dimension).trans hdimension
  have hfactorial : (steps.factorial : ℤ) ≤ 2^(dimension*steps) := by
    calc
      _ ≤ (steps : ℤ)^steps := by exact_mod_cast Nat.factorial_le_pow steps
      _ ≤ ((2 : ℤ)^dimension)^steps := pow_le_pow_left₀ (Nat.cast_nonneg steps) hstep _
      _ = _ := by rw [←pow_mul]
  have hentryGram : (dimension : ℤ)*((2 : ℤ)^height)^2 ≤ 2^(dimension+2*height) := by
    calc
      _ ≤ (2 : ℤ)^dimension*((2 : ℤ)^height)^2 :=
        mul_le_mul_of_nonneg_right hdimension (sq_nonneg _)
      _ = _ := by rw [←pow_mul,←pow_add];congr 1;omega
  calc
    _ ≤ (steps.factorial : ℤ)*((dimension : ℤ)*((2 : ℤ)^height)^2)^steps :=
      prefixGram_det_bound basis steps hsteps ((2 : ℤ)^height) (by positivity) hentries
    _ ≤ (2 : ℤ)^(dimension*steps)*(2^(dimension+2*height))^steps :=
      mul_le_mul hfactorial (pow_le_pow_left₀ (by positivity) hentryGram _)
        (by positivity) (by positivity)
    _ = 2^((2*dimension+2*height)*steps) := by
      rw [←pow_mul,←pow_add]
      congr 1
      ring
    _ ≤ _ := pow_le_pow_right₀ (by norm_num)
      (Nat.mul_le_mul_left (2*dimension+2*height) hsteps)

/-- Every cached rational coordinate has a small absolute magnitude even
when canonical numerators and denominators require separate control. -/
theorem orthogonal_coordinate_abs_bound {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (height : ℕ)
    (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (index row : Fin dimension) :
    |orthogonal (inputVectors basis) index row| ≤ (2 : ℚ)^(dimension+height) := by
  have hcoordinate : orthogonal (inputVectors basis) index row^2 ≤
      squaredNorm (inputVectors basis) index := by
    unfold squaredNorm innerQ
    simp only [←sq]
    exact Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ row)
  have hcolumn : innerQ (inputVectors basis index) (inputVectors basis index) ≤
      (dimension : ℚ)*((2 : ℚ)^height)^2 := by
    unfold innerQ inputVectors
    simp only [←sq]
    calc
      _ ≤ ∑ _ : Fin dimension,((2 : ℚ)^height)^2 := by
        apply Finset.sum_le_sum
        intro position _
        have hentry : |(basis position index : ℚ)| ≤ (2 : ℚ)^height := by
          exact_mod_cast hentries position index
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hentry
      _ = _ := by simp
  have hdimension : (dimension : ℚ) ≤ 2^dimension := by
    exact_mod_cast (Nat.lt_two_pow_self (n:=dimension)).le
  have hpower : (1 : ℚ) ≤ 2^dimension := one_le_pow₀ (by norm_num)
  have hdimensionSquare : (dimension : ℚ) ≤ ((2 : ℚ)^dimension)^2 := by nlinarith
  have hsquare : orthogonal (inputVectors basis) index row^2 ≤ ((2 : ℚ)^(dimension+height))^2 := by
    calc
      _ ≤ squaredNorm (inputVectors basis) index := hcoordinate
      _ ≤ innerQ (inputVectors basis index) (inputVectors basis index) := squaredNorm_le _ index
      _ ≤ (dimension : ℚ)*((2 : ℚ)^height)^2 := hcolumn
      _ ≤ ((2 : ℚ)^dimension)^2*((2 : ℚ)^height)^2 :=
        mul_le_mul_of_nonneg_right hdimensionSquare (sq_nonneg _)
      _ = _ := by rw [pow_add,mul_pow]
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hsquare)

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule60

/- Helper module Solutions.RegevBridgeRationalDenominator. -/
section P2MDyadicModule61

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.RationalDenominator

/-- Any nonzero integral clearing denominator is divisible by the canonical
positive denominator of the rational number. -/
theorem den_dvd {r : ℚ} {D N : ℤ} (hD : D≠0) (h : (D : ℚ)*r=N) :
    (r.den : ℤ) ∣ D := by
  have hDQ : (D : ℚ)≠0 := by exact_mod_cast hD
  have hr : r=(N : ℚ)/(D : ℚ) := (eq_div_iff hDQ).mpr (by simpa only [mul_comm] using h)
  rw [hr]
  simpa only [Rat.divInt_eq_div] using Rat.den_dvd N D

/-- Canonical denominators never exceed any nonzero integral clearing denominator. -/
theorem den_le_natAbs {r : ℚ} {D N : ℤ} (hD : D≠0) (h : (D : ℚ)*r=N) :
    r.den≤D.natAbs := by
  have hd := den_dvd hD h
  have hn : r.den ∣ D.natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hD) hn

/-- Clearing-denominator bounds control the canonical numerator as well. -/
theorem num_bound_rat {r : ℚ} {D N : ℤ} (hD : D≠0) (h : (D : ℚ)*r=N) :
    |(r.num : ℚ)| ≤ |(D : ℚ)| * |r| := by
  have hd : (r.den : ℚ) ≤ |(D : ℚ)| := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using
      (Nat.cast_le (α := ℚ)).mpr (den_le_natAbs hD h)
  calc
    |(r.num : ℚ)|=|(r.den : ℚ)*r| := congrArg abs (Rat.den_mul_eq_num r).symm
    _ = (r.den : ℚ)*|r| := by rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ _ := mul_le_mul_of_nonneg_right hd (abs_nonneg _)

/-- A magnitude bound and clearing-denominator bound yield a natural bound
on both stored rational integer fields. -/
theorem fields_bound {r : ℚ} {D N : ℤ} (hD : D≠0) (h : (D : ℚ)*r=N)
    (M : ℕ) (hM : |r|≤M) : r.den≤D.natAbs ∧ r.num.natAbs≤D.natAbs*M := by
  refine ⟨den_le_natAbs hD h,?_⟩
  have hn := (num_bound_rat hD h).trans (mul_le_mul_of_nonneg_left hM (abs_nonneg _))
  have hn' : (r.num.natAbs : ℚ) ≤ ((D.natAbs*M : ℕ) : ℚ) := by
    simpa only [Nat.cast_mul,Nat.cast_natAbs,Int.cast_abs] using hn
  exact_mod_cast hn'

end InfoLossLAR.WorstCase.RationalDenominator

end P2MDyadicModule61

/- Helper module Solutions.RegevBridgeRationalGramSchmidtHeight. -/
section P2MDyadicModule62

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open AFT.RationalNumerics

open scoped BigOperators

/-- A fixed polynomial in the dimension and input entry height controls
every reduced cached rational coordinate. -/
def coordinateHeight (dimension height : ℕ) : ℕ :=
  (2*dimension+2*height)*dimension+dimension+height

noncomputable section

/-- Canonical numerator and denominator sizes are polynomial, using the
actual integer Gram determinant rather than an arithmetic-operation count. -/
theorem orthogonal_coordinate_height {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (height : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (index row : Fin dimension) :
    HeightBound (orthogonal (inputVectors basis) index row) (coordinateHeight dimension height) := by
  have hnonzero := prefixGram_det_ne_zero basis hdet index.val index.isLt.le
  have hvector := gram_determinant_scales_orthogonal basis index
  have hcoordinate := congrArg (fun vector : QVector dimension => vector row) hvector
  simp only [Pi.smul_apply,smul_eq_mul] at hcoordinate
  have habs := orthogonal_coordinate_abs_bound basis height hentries index row
  have hM : |orthogonal (inputVectors basis) index row| ≤ ((2^(dimension+height) : ℕ) : ℚ) := by
    exact_mod_cast habs
  obtain ⟨hden,hnum⟩ := RationalDenominator.fields_bound hnonzero hcoordinate (2^(dimension+height)) hM
  have hD : (prefixGram basis index.val index.isLt.le).det.natAbs ≤
      2^((2*dimension+2*height)*dimension) := by
    have h := prefixGram_det_binary_bound basis index.val index.isLt.le height hentries
    have hcast : (((prefixGram basis index.val index.isLt.le).det.natAbs : ℕ) : ℤ) ≤
        (2 : ℤ)^((2*dimension+2*height)*dimension) := by
      simpa only [Int.natCast_natAbs] using h
    exact_mod_cast hcast
  constructor
  · apply hnum.trans
    apply (Nat.mul_le_mul_right (2^(dimension+height)) hD).trans_eq
    rw [←pow_add]
    congr 1
    unfold coordinateHeight
    omega
  · apply (hden.trans hD).trans
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by unfold coordinateHeight;omega)

theorem realVec_injective {dimension : ℕ} : Function.Injective (realVec (dimension:=dimension)) := by
  intro first second hequal
  funext index
  apply Rat.cast_injective (α:=ℝ)
  exact congrArg (fun vector : Space dimension => vector index) hequal

/-- Every materialized prefix consists of the very same final cached
orthogonal vectors, so all prefix state encodings share one height bound. -/
theorem cache_prefix_eq {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (steps : ℕ) (hsteps : steps ≤ count) :
    cache vectors steps=List.ofFn (fun index : Fin steps => orthogonal vectors (Fin.castLE hsteps index)) := by
  apply (List.map_injective_iff.mpr realVec_injective)
  rw [cache_real vectors steps hsteps,List.map_ofFn]
  apply congrArg List.ofFn
  funext index
  exact (orthogonal_real vectors _).symm

theorem cache_coordinate_height {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (height : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (steps : ℕ) (hsteps : steps ≤ dimension) (vector : QVector dimension)
    (membership : vector ∈ cache (inputVectors basis) steps) (row : Fin dimension) :
    HeightBound (vector row) (coordinateHeight dimension height) := by
  rw [cache_prefix_eq _ steps hsteps] at membership
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp membership
  exact orthogonal_coordinate_height basis hdet height hentries _ row

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule62

/- Helper module Solutions.RegevBridgeRationalGramSchmidtNative. -/
section P2MDyadicModule63

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

/-- Total native rational list dot product; malformed lengths truncate. -/
def dot (input : List ℚ × List ℚ) : ℚ :=
  ((input.1.zip input.2).map (fun pair => pair.1*pair.2)).sum

def projectionEntry (input : (List ℚ × List ℚ) × ℕ) : ℚ :=
  dot (input.1.1,input.1.2)/dot (input.1.1,input.1.1)*input.1.1[input.2]?.getD 0

def rowValue (input : (List (List ℚ) × List ℚ) × ℕ) : ℚ :=
  input.1.2[input.2]?.getD 0-
    (input.1.1.map (fun previous => projectionEntry ((previous,input.1.2),input.2))).sum

/-- One native materialized Gram--Schmidt step uses its original current
column throughout and stores the complete new rational vector. -/
def orthogonalStep (input : List (List ℚ) × List ℚ) : List ℚ :=
  (List.range input.2.length).map (fun row => rowValue (input,row))

/-- Unary size reflection materializes the exact actual binary encoding
length; it never enumerates a Gaussian window or a numerical magnitude. -/
def rationalTicks (value : ℚ) : List Unit :=
  List.replicate 7 ()++(value.num.natAbs.bits.flatMap (fun _ => [(),()]))++
    value.den.bits.map (fun _ => ())

def vectorTicks (vector : List ℚ) : List Unit :=
  vector.flatMap (fun value => rationalTicks value++rationalTicks value++[()])

def matrixTicks (matrix : List (List ℚ)) : List Unit :=
  matrix.flatMap (fun vector => vectorTicks vector++vectorTicks vector++[()])

theorem rationalTicks_length (value : ℚ) : (rationalTicks value).length=(Ratio.encode value).length := by
  rw [Ratio.encode_length]
  simp only [rationalTicks,List.length_append,List.length_replicate,List.length_flatMap,
    List.map_const',List.sum_replicate,List.length_cons,List.length_nil,nsmul_eq_mul,Nat.cast_id]
  omega

theorem vectorTicks_length (vector : List ℚ) :
    (vectorTicks vector).length=(encodeList Ratio.encode vector).length := by
  induction vector with
  | nil => rfl
  | cons head tail ih =>
    simp only [vectorTicks,List.flatMap_cons,List.length_append,List.length_singleton,
      rationalTicks_length,EncodedList.cons_length] at *
    omega

theorem matrixTicks_length (matrix : List (List ℚ)) :
    (matrixTicks matrix).length=(encodeList (encodeList Ratio.encode) matrix).length := by
  induction matrix with
  | nil => rfl
  | cons head tail ih =>
    simp only [matrixTicks,List.flatMap_cons,List.length_append,List.length_singleton,
      vectorTicks_length,EncodedList.cons_length] at *
    omega

/-- Every intermediate cache is size-guarded, giving an unconditional
polynomial-time loop on arbitrary encodings. Valid matrix correctness will
be discharged using the independently proved integer-Gram height bound. -/
def cacheStep (state : List Unit × List (List ℚ)) (current : List ℚ) : List Unit × List (List ℚ) :=
  let next := state.2++[orthogonalStep (state.2,current)]
  (state.1,if (matrixTicks next).length ≤ state.1.length then next else [])

/-- Actual guarded list cache program. The guard's complete runtime bound
holds for every encoded input, including malformed or singular matrices. -/
def cached (input : List (List ℚ) × List Unit) : List (List ℚ) :=
  (input.1.foldl cacheStep (input.2,[])).2

theorem dot_ofFn {dimension : ℕ} (first second : QVector dimension) :
    dot (List.ofFn first,List.ofFn second)=innerQ first second := by
  induction dimension with
  | zero => simp [dot,innerQ]
  | succ dimension ih =>
    simp only [dot,List.ofFn_succ,List.zip_cons_cons,List.map_cons,List.sum_cons]
    change first 0*second 0+dot (List.ofFn (Fin.tail first),List.ofFn (Fin.tail second))= _
    rw [ih]
    simp only [innerQ,Fin.sum_univ_succ,Fin.tail_def]

theorem vector_list_sum_apply {dimension : ℕ} (vectors : List (QVector dimension)) (index : Fin dimension) :
    vectors.sum index=(vectors.map (fun vector => vector index)).sum := by
  induction vectors with
  | nil => rfl
  | cons head tail ih => simp only [List.sum_cons,List.map_cons,Pi.add_apply,ih]

theorem orthogonalStep_ofFn {dimension : ℕ} (previous : List (QVector dimension))
    (current : QVector dimension) :
    orthogonalStep (previous.map List.ofFn,List.ofFn current)=
      List.ofFn (RationalGramSchmidt.orthogonalStep previous current) := by
  apply List.ext_getElem
  · simp only [orthogonalStep,List.length_map,List.length_range,List.length_ofFn]
  · intro row hfirst hsecond
    have hrow : row < dimension := by
      simpa only [orthogonalStep,List.length_map,List.length_range,List.length_ofFn] using hfirst
    simp only [orthogonalStep,List.length_ofFn,List.getElem_map,List.getElem_range,rowValue,
      List.getElem?_ofFn,hrow,↓reduceDIte,Option.getD_some,List.map_map,Function.comp_def,
      projectionEntry,dot_ofFn,List.getElem_ofFn]
    simp only [RationalGramSchmidt.orthogonalStep,Pi.sub_apply,vector_list_sum_apply,List.map_map,
      Function.comp_def,projection,Pi.smul_apply,smul_eq_mul]

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule63

/- Helper module Solutions.RegevBridgeRationalGramSchmidtCacheBudget. -/
section P2MDyadicModule64

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

noncomputable section

theorem encoded_list_length_bound {Value : Type} (encoding : Value → List Bool)
    (values : List Value) (bound : ℕ) (hbound : ∀ value ∈ values,(encoding value).length ≤ bound) :
    (encodeList encoding values).length ≤ values.length*(2*bound+1) := by
  induction values with
  | nil => simp only [EncodedList.nil,List.length_nil,zero_mul,le_refl]
  | cons head tail ih =>
    rw [EncodedList.cons_length,List.length_cons]
    have hhead := hbound head (by simp)
    have htail := ih (fun value membership => hbound value (by simp [membership]))
    nlinarith

theorem rational_encoding_height {value : ℚ} {height : ℕ} (hvalue : HeightBound value height) :
    (Ratio.encode value).length ≤ 3*height+10 := by
  apply Ratio.length_height
  constructor
  · have h := (Nat.cast_le (α:=ℤ)).mpr hvalue.1
    simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using h
  · exact_mod_cast hvalue.2

theorem vector_encoding_height {dimension : ℕ} (vector : QVector dimension) (height : ℕ)
    (hvector : ∀ row,HeightBound (vector row) height) :
    (encodeList Ratio.encode (List.ofFn vector)).length ≤ dimension*(6*height+21) := by
  have h := encoded_list_length_bound Ratio.encode (List.ofFn vector) (3*height+10) (by
    intro value membership
    obtain ⟨row,rfl⟩ := List.mem_ofFn.mp membership
    exact rational_encoding_height (hvector row))
  simpa only [List.length_ofFn,show 2*(3*height+10)+1=6*height+21 by omega] using h

def cacheEncodingBound (dimension height : ℕ) : ℕ :=
  dimension*(2*dimension*(6*coordinateHeight dimension height+21)+1)

/-- The original determinant-derived height bound controls every complete
native cache-prefix encoding by one public polynomial. -/
theorem cache_encoding_bound {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (height : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (steps : ℕ) (hsteps : steps ≤ dimension) :
    (encodeList (encodeList Ratio.encode) ((cache (inputVectors basis) steps).map List.ofFn)).length ≤
      cacheEncodingBound dimension height := by
  have h := encoded_list_length_bound (encodeList Ratio.encode)
    ((cache (inputVectors basis) steps).map List.ofFn) (dimension*(6*coordinateHeight dimension height+21)) (by
      intro vector membership
      obtain ⟨source,hsource,rfl⟩ := List.mem_map.mp membership
      exact vector_encoding_height source _ (cache_coordinate_height basis hdet height hentries steps hsteps source hsource))
  rw [List.length_map,cache_length] at h
  apply h.trans
  unfold cacheEncodingBound
  calc
    steps*(2*(dimension*(6*coordinateHeight dimension height+21))+1) ≤
        dimension*(2*(dimension*(6*coordinateHeight dimension height+21))+1) := Nat.mul_le_mul_right _ hsteps
    _ = _ := by ring

/-- Prefix refinement is proved for the actual guarded list loop. Its
encoding bound is a local arithmetic invariant, discharged below from the
original integer matrix's determinant-derived size bounds. -/
theorem cacheFold_ofFn {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (ticks : List Unit)
    (hbudget : ∀ steps,steps ≤ count →
      (encodeList (encodeList Ratio.encode) ((cache vectors steps).map List.ofFn)).length ≤ ticks.length)
    (steps : ℕ) (hsteps : steps ≤ count) :
    (List.ofFn (fun index : Fin steps => List.ofFn (vectors (Fin.castLE hsteps index)))).foldl cacheStep (ticks,[])=
      (ticks,(cache vectors steps).map List.ofFn) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    have hprevious : steps ≤ count := by omega
    have hstep : steps < count := by omega
    rw [List.ofFn_succ_last,List.foldl_append]
    change List.foldl cacheStep
      ((List.ofFn (fun index : Fin steps => List.ofFn (vectors (Fin.castLE hprevious index)))).foldl cacheStep (ticks,[]))
      [List.ofFn (vectors ⟨steps,hstep⟩)] = _
    rw [ih hprevious,List.foldl_cons,List.foldl_nil]
    have hnext : (cache vectors steps).map List.ofFn++
        [orthogonalStep ((cache vectors steps).map List.ofFn,List.ofFn (vectors ⟨steps,hstep⟩))]=
        (cache vectors (steps+1)).map List.ofFn := by
      rw [orthogonalStep_ofFn,cache,List.map_append,List.map_singleton,dif_pos hstep]
    have hguard : (matrixTicks ((cache vectors steps).map List.ofFn++
        [orthogonalStep ((cache vectors steps).map List.ofFn,List.ofFn (vectors ⟨steps,hstep⟩))])).length ≤ ticks.length := by
      rw [hnext,matrixTicks_length]
      exact hbudget (steps+1) hsteps
    simp only [cacheStep,hguard,if_true]
    exact congrArg (fun matrix => (ticks,matrix)) hnext

/-- For every nonsingular input basis, the actual native cache agrees
exactly with rational Gram--Schmidt once supplied the public polynomial
encoding budget. No oracle or assumed GS algorithm appears. -/
theorem cached_integer_basis {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (height : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (ticks : List Unit) (hticks : cacheEncodingBound dimension height ≤ ticks.length) :
    cached (List.ofFn (fun index => List.ofFn (inputVectors basis index)),ticks)=
      (cache (inputVectors basis) dimension).map List.ofFn := by
  have h := cacheFold_ofFn (inputVectors basis) ticks (fun steps hsteps =>
    (cache_encoding_bound basis hdet height hentries steps hsteps).trans hticks) dimension (le_refl dimension)
  change (List.ofFn (fun index : Fin dimension => List.ofFn (inputVectors basis index))).foldl cacheStep (ticks,[])=_ at h
  exact congrArg Prod.snd h

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule64

/- Helper module Solutions.RegevBridgeRationalGramSchmidtInput. -/
section P2MDyadicModule65

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

def integerTicks (value : ℤ) : List Unit := List.replicate 3 ()++value.natAbs.bits.map (fun _ => ())

def integerVectorTicks (vector : List ℤ) : List Unit :=
  vector.flatMap (fun value => integerTicks value++integerTicks value++[()])

def integerMatrixTicks (matrix : List (List ℤ)) : List Unit :=
  matrix.flatMap (fun vector => integerVectorTicks vector++integerVectorTicks vector++[()])

/-- The guard budget is generated in unary polynomial size from the
actual binary input length, not from an exponentially large entry value. -/
def inputBudget (input : List (List ℤ)) : List Unit :=
  let slots := integerMatrixTicks input++[()]
  slots.flatMap (fun _ => slots.flatMap (fun _ => slots.flatMap
    (fun _ => slots.flatMap (fun _ => List.replicate 128 ()))))

def rationalColumn (column : List ℤ) : List ℚ := column.map (fun value : ℤ => (value : ℚ))

def rationalColumns (input : List (List ℤ)) : List (List ℚ) := input.map rationalColumn

/-- Complete unconditional native cached orthogonalization of original
integer input columns, with all guards and loop sizes computed publicly. -/
def inputCache (input : List (List ℤ)) : List (List ℚ) := cached (rationalColumns input,inputBudget input)

theorem integerTicks_length (value : ℤ) : (integerTicks value).length=(Signed.encode value).length := by
  simp only [integerTicks,List.length_append,List.length_replicate,List.length_map,Signed.encode_length]

theorem integerVectorTicks_length (vector : List ℤ) :
    (integerVectorTicks vector).length=(encodeList Signed.encode vector).length := by
  induction vector with
  | nil => rfl
  | cons head tail ih =>
    simp only [integerVectorTicks,List.flatMap_cons,List.length_append,List.length_singleton,
      integerTicks_length,EncodedList.cons_length] at *
    omega

theorem integerMatrixTicks_length (matrix : List (List ℤ)) :
    (integerMatrixTicks matrix).length=(encodeList (encodeList Signed.encode) matrix).length := by
  induction matrix with
  | nil => rfl
  | cons head tail ih =>
    simp only [integerMatrixTicks,List.flatMap_cons,List.length_append,List.length_singleton,
      integerVectorTicks_length,EncodedList.cons_length] at *
    omega

theorem inputBudget_length (matrix : List (List ℤ)) :
    (inputBudget matrix).length=128*((integerMatrixTicks matrix).length+1)^4 := by
  simp only [inputBudget,List.length_flatMap,List.map_const',List.sum_replicate,List.length_replicate,
    List.length_append,List.length_singleton,nsmul_eq_mul,Nat.cast_id]
  ring

def transposeColumn (input : List (List ℤ) × ℕ) : List ℤ :=
  input.1.map (fun row => row[input.2]?.getD 0)

def transpose (input : List (List ℤ)) : List (List ℤ) :=
  (List.range input.length).map (fun column => transposeColumn (input,column))

/-- Actual row-encoded matrix input is transposed by a native program
before the cached column orthogonalization. -/
def basisCache (input : List (List ℤ)) : List (List ℚ) := inputCache (transpose input)

noncomputable section

/-- Coarse fixed polynomial suitable for unconditional guarded runtime. -/
theorem cacheEncodingBound_coarse (dimension height length : ℕ)
    (hdimension : dimension ≤ length) (hheight : height ≤ length) :
    cacheEncodingBound dimension height ≤ 128*(length+1)^4 := by
  have hlinear : length ≤ (length+1)^2 := by nlinarith
  have hcross : height*dimension ≤ (length+1)^2 := by
    calc
      _ ≤ length*length := Nat.mul_le_mul hheight hdimension
      _ ≤ _ := by nlinarith
  have hsquare : dimension*dimension ≤ (length+1)^2 := by
    calc
      _ ≤ length*length := Nat.mul_le_mul hdimension hdimension
      _ ≤ _ := by nlinarith
  have hcache : coordinateHeight dimension height ≤ 6*(length+1)^2 := by
    unfold coordinateHeight
    nlinarith
  unfold cacheEncodingBound
  calc
    _ ≤ (length+1)*(2*(length+1)*(6*(6*(length+1)^2)+21)+1) := by gcongr <;> omega
    _ ≤ _ := by
      have hpowerOne := Nat.pow_le_pow_right (by omega : 1 ≤ length+1) (show 1 ≤ 4 by omega)
      have hpowerTwo := Nat.pow_le_pow_right (by omega : 1 ≤ length+1) (show 2 ≤ 4 by omega)
      simp only [pow_one] at hpowerOne
      nlinarith

def inputColumns {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) : List (List ℤ) :=
  List.ofFn (fun column => List.ofFn (fun row => basis row column))

theorem inputColumns_dimension {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) :
    dimension ≤ (integerMatrixTicks (inputColumns basis)).length := by
  rw [integerMatrixTicks_length]
  have h := EncodedList.length_le (encodeList Signed.encode) (inputColumns basis)
  simpa only [inputColumns,List.length_ofFn] using h

theorem inputColumns_entry_height {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (row column : Fin dimension) :
    |basis row column| ≤ (2 : ℤ)^(integerMatrixTicks (inputColumns basis)).length := by
  have hcolumn : List.ofFn (fun position => basis position column) ∈ inputColumns basis :=
    List.mem_ofFn.mpr ⟨column,rfl⟩
  have hentry : basis row column ∈ List.ofFn (fun position => basis position column) :=
    List.mem_ofFn.mpr ⟨row,rfl⟩
  have hcolumnSize := EncodedList.member_length (encodeList Signed.encode) (inputColumns basis) _ hcolumn
  have hentrySize := EncodedList.member_length Signed.encode _ _ hentry
  have hbits : (basis row column).natAbs.bits.length ≤ (integerMatrixTicks (inputColumns basis)).length := by
    rw [integerMatrixTicks_length]
    rw [Signed.encode_length] at hentrySize
    omega
  have hvalue := (NatBinary.le_two_pow_length (basis row column).natAbs).trans
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hbits)
  have hcast := (Nat.cast_le (α:=ℤ)).mpr hvalue
  simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using hcast

theorem rationalColumns_input {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) :
    rationalColumns (inputColumns basis)=List.ofFn (fun index => List.ofFn (inputVectors basis index)) := by
  simp only [rationalColumns,rationalColumn,inputColumns,List.map_ofFn,Function.comp_def]
  rfl

/-- The fully generated binary-input native cache exactly returns the
original nonsingular integer basis's rational orthogonalization. Every
size guard is discharged from the actual input encoding itself. -/
theorem inputCache_correct {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) :
    inputCache (inputColumns basis)=(cache (inputVectors basis) dimension).map List.ofFn := by
  unfold inputCache
  rw [rationalColumns_input]
  apply cached_integer_basis basis hdet (integerMatrixTicks (inputColumns basis)).length
    (inputColumns_entry_height basis)
  rw [inputBudget_length]
  exact cacheEncodingBound_coarse dimension _ _ (inputColumns_dimension basis) le_rfl

theorem transpose_input_rows {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) :
    transpose (List.ofFn (fun row => List.ofFn (fun column => basis row column)))=inputColumns basis := by
  apply List.ext_getElem
  · simp only [transpose,List.length_map,List.length_range,List.length_ofFn,inputColumns]
  · intro column hfirst hsecond
    have hcolumn : column < dimension := by
      simpa only [transpose,List.length_map,List.length_range,List.length_ofFn] using hfirst
    simp only [transpose,List.length_ofFn,List.getElem_map,List.getElem_range,transposeColumn,
      List.map_ofFn,Function.comp_def,List.getElem?_ofFn,hcolumn,↓reduceDIte,Option.getD_some,
      inputColumns,List.getElem_ofFn]

/-- End-to-end exact native GS caching for the target's original row-major
integer matrix convention, with an unconditional polynomial-time program. -/
theorem basisCache_correct {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) :
    basisCache (List.ofFn (fun row => List.ofFn (fun column => basis row column)))=
      (cache (inputVectors basis) dimension).map List.ofFn := by
  rw [basisCache,transpose_input_rows,inputCache_correct basis hdet]

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule65

/- Helper module Solutions.RegevBridgeInitialGaussianFlatRowsNative. -/
section P2MDyadicModule66

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT AFT.RationalNumerics GaussianRandomizedRounding

noncomputable section

theorem rowSlice_ofFn (count total : ℕ) (tape : Fin (count*total) → Bool) (row : Fin count) :
    rowSlice ((total,List.ofFn tape),row.val)=
      List.ofFn (Integration9_9.BlockCoins.blockEquiv count total tape row) := by
  have h := congrArg Prod.fst (Wide.splitTrial_ofFn total 0 count (count*total) (by simp) tape row)
  change (Wide.splitTrial ((total,0),(List.ofFn tape,row.val))).1=_
  refine h.trans ?_
  apply congrArg List.ofFn
  funext bit
  apply congrArg tape
  apply Fin.ext
  rfl

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule66

/- Helper module Solutions.RegevBridgeLatticeInterfaces. -/
section P2MDyadicModule67

set_option autoImplicit false

open QAlgorithms.Complexity

namespace InfoLossLAR.WorstCase

/-- The fixed modulus is prime, independently of any asymptotic threshold. -/
theorem famq_prime (lam : ℕ) : (famq lam).Prime :=
  (Nat.find_spec (Nat.exists_infinite_primes (2 ^ 16 * famL lam ^ 64))).2

end InfoLossLAR.WorstCase

end P2MDyadicModule67

/- Helper module Solutions.RegevBridgeGaussianProjection. -/
section P2MDyadicModule68

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open AFT GaussianSource

open scoped BigOperators Classical

noncomputable section

/-- A coordinate of the genuine integer product PMF has exactly its scalar law. -/
theorem independentCoordinates_eval (p : PMF ℤ) (dimension : ℕ) (index : Fin dimension) :
    (independentCoordinates p dimension).map (fun vector : Fin dimension → ℤ => vector index)=p := by
  induction dimension with
  | zero => exact Fin.elim0 index
  | succ dimension ih =>
    cases index using Fin.cases with
    | zero =>
      rw [independentCoordinates,PMF.map_bind]
      have hhead (head : ℤ) :
          ((independentCoordinates p dimension).map (Fin.cons head)).map
            (fun vector : Fin (dimension+1) → ℤ => vector 0)=PMF.pure head := by
        rw [PMF.map_comp]
        exact PMF.map_const _ _
      simp_rw [hhead]
      exact PMF.bind_pure p
    | succ index =>
      rw [independentCoordinates,PMF.map_bind]
      simp_rw [PMF.map_comp]
      simp only [Function.comp_def,Fin.cons_succ]
      simp_rw [ih]
      exact PMF.bind_const p p

private theorem finiteLaw_map_finite {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (function : α → β) :
    (finiteLaw p).map function=finiteLaw (p.map function) := by
  apply FiniteDist.ext
  intro b
  rw [FiniteDist.map_weight,Integration.finiteLaw_map_weight,tsum_fintype]
  rfl

/-- Reducing a genuine Gaussian coordinate modulo q gives the scalar modular
integer PMF, independently of the surrounding dimension. -/
theorem residueGaussian_eval_integer (q dimension : ℕ) [NeZero q]
    (width : ℝ) (hwidth : 0 < width) (index : Fin dimension) :
    (residueGaussian dimension q width hwidth).map (fun vector : Fin dimension → ZMod q => vector index)=
      finiteLaw ((integerGaussian width hwidth).map (fun value : ℤ => (value : ZMod q))) := by
  unfold residueGaussian
  rw [finiteLaw_map_finite,PMF.map_comp]
  change finiteLaw ((independentCoordinates (integerGaussian width hwidth) dimension).map
    (fun vector => (vector index : ZMod q)))=_
  have h := congrArg (fun law : PMF ℤ => law.map (fun value : ℤ => (value : ZMod q)))
    (independentCoordinates_eval (integerGaussian width hwidth) dimension index)
  rw [PMF.map_comp] at h
  exact congrArg finiteLaw h

/-- The actual modular integer PMF is the platform scalar Gaussian, not merely
an approximation to it. -/
theorem modularInteger_eq_scalarLaw (q : ℕ) [NeZero q]
    (width : ℝ) (hwidth : 0 < width) :
    finiteLaw ((integerGaussian width hwidth).map (fun value : ℤ => (value : ZMod q)))=
      scalarLaw q width hwidth := by
  apply FiniteDist.ext
  intro error
  have h := congrArg (fun law : FiniteDist (ZMod q) => law.weight error)
    (residueGaussian_eval_integer q 1 width hwidth 0)
  change ((residueGaussian 1 q width hwidth).map (Equiv.funUnique (Fin 1) (ZMod q))).weight error=_ at h
  rw [FiniteDist.map_equiv_weight,Integration.residueGaussian_weight_eq_chiG] at h
  change _=chiG q 1 width (fun _ => error)
  exact h.symm

end

end InfoLossLAR.WorstCase.GaussianProjection

end P2MDyadicModule68

/- Helper module Solutions.RegevBridgeGaussianBlockProduct. -/
section P2MDyadicModule69

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open AFT GaussianSource Matrix

open scoped BigOperators Classical

noncomputable section

/-- Coordinatewise deterministic decoding preserves the complete independent
product law of the genuine integer PMF, even for noninjective decoding. -/
theorem independentCoordinates_map_apply {Value : Type*} (law : PMF ℤ)
    (decode : ℤ → Value) (dimension : ℕ) (values : Fin dimension → Value) :
    ((independentCoordinates law dimension).map (fun vector index => decode (vector index))) values=
      ∏ index,(law.map decode) (values index) := by
  induction dimension with
  | zero =>
    simp [independentCoordinates,PMF.pure_map,Subsingleton.elim values (fun i => Fin.elim0 i)]
    funext index
    exact Fin.elim0 index
  | succ dimension ih =>
    have hcons (head : Value) (tail : PMF (Fin dimension → Value)) :
        (tail.map (Fin.cons head)) values=
          if head=values 0 then tail (Fin.tail values) else 0 := by
      have hp (vector : Fin dimension → Value) :
          values=Fin.cons head vector ↔ head=values 0 ∧ vector=Fin.tail values := by
        constructor
        · intro h
          exact ⟨by simpa using (congrFun h 0).symm,by simpa using (congrArg Fin.tail h).symm⟩
        · rintro ⟨rfl,rfl⟩
          exact (Fin.cons_self_tail values).symm
      rw [PMF.map_apply]
      simp_rw [hp]
      by_cases hh : head=values 0 <;> simp [hh]
    have hdecode (head : ℤ) :
        (((independentCoordinates law dimension).map (Fin.cons head)).map
          (fun vector index => decode (vector index)))=
        (((independentCoordinates law dimension).map (fun vector index => decode (vector index))).map
          (Fin.cons (decode head))) := by
      rw [PMF.map_comp,PMF.map_comp]
      apply congrArg (fun f => (independentCoordinates law dimension).map f)
      funext vector index
      cases index using Fin.cases <;> rfl
    rw [independentCoordinates,PMF.map_bind,PMF.bind_apply,Fin.prod_univ_succ]
    simp_rw [hdecode,hcons]
    change _ = (law.map decode) (values 0)*(∏ index,(law.map decode) (Fin.tail values index))
    rw [←ih (Fin.tail values)]
    conv_rhs => rw [PMF.map_apply]
    rw [←ENNReal.tsum_mul_right]
    apply tsum_congr
    intro head
    by_cases hh : decode head=values 0 <;> simp [hh,eq_comm]

/-- The whole modular Gaussian block is a product of scalar Gaussian laws.
This is full joint independence; equality of coordinate marginals alone
would not justify replacing a block by scalar samples. -/
theorem residueGaussian_eq_independent (q dimension : ℕ) [NeZero q]
    (width : ℝ) (hwidth : 0 < width) :
    residueGaussian dimension q width hwidth=
      FiniteDist.independent (fun _ : Fin dimension => scalarLaw q width hwidth) := by
  apply FiniteDist.ext
  intro values
  change (((independentCoordinates (integerGaussian width hwidth) dimension).map
    (fun vector index => (vector index : ZMod q))) values).toReal=
      ∏ index,(scalarLaw q width hwidth).weight (values index)
  rw [independentCoordinates_map_apply,ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro index _
  have h := congrArg (fun source : FiniteDist (ZMod q) => source.weight (values index))
    (modularInteger_eq_scalarLaw q width hwidth)
  exact h

/-- Flattening all rows of all independent blocks yields genuinely independent
scalar Gaussian errors at every scalar-sample position. -/
theorem residueGaussian_blocks_flatten (q dimension blocks : ℕ) [NeZero q]
    (width : ℝ) (hwidth : 0 < width) :
    (FiniteDist.independent (fun _ : Fin blocks => residueGaussian dimension q width hwidth)).map
      (fun errors (index : Fin blocks × Fin dimension) => errors index.1 index.2)=
      FiniteDist.independent (fun _ : Fin blocks × Fin dimension => scalarLaw q width hwidth) := by
  let flatten : (Fin blocks → Fin dimension → ZMod q) ≃ ((Fin blocks × Fin dimension) → ZMod q) :=
    { toFun := fun errors index => errors index.1 index.2
      invFun := fun errors block row => errors (block,row)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change (FiniteDist.independent (fun _ : Fin blocks => residueGaussian dimension q width hwidth)).map flatten=_
  apply FiniteDist.ext
  intro values
  rw [FiniteDist.map_equiv_weight]
  simp only [FiniteDist.independent,residueGaussian_eq_independent]
  rw [Fintype.prod_prod_type]
  rfl

@[simp] theorem regroup_flattenObserved {q N dimension blocks : ℕ}
    (table : Fin blocks → Matrix (Fin dimension) (Fin N) (ZMod q) × (Fin dimension → ZMod q)) :
    regroupObserved (flattenObserved table)=table := by
  funext block
  apply Prod.ext <;> funext row <;> rfl

/-- Exact scalar-to-block source interface. All rows of all genuine Gaussian
LWE blocks are jointly identical to independent public scalar rows and
independent scalar Gaussian errors with the same common secret. -/
theorem observedRealTable_flatten (q N dimension blocks : ℕ) [NeZero q]
    (width : ℝ) (hwidth : 0 < width) (secret : Fin N → ZMod q) :
    (larObservedRealTableLaw q N dimension blocks (residueGaussian dimension q width hwidth) secret).map
      flattenObserved=
      ((FiniteDist.uniform ((Fin blocks × Fin dimension) → Fin N → ZMod q)).prod
        (FiniteDist.independent (fun _ : Fin blocks × Fin dimension => scalarLaw q width hwidth))).map
          (fun draw index => (draw.1 index,(draw.1 index) ⬝ᵥ secret+draw.2 index)) := by
  let matrices := FiniteDist.uniform (Fin blocks → Matrix (Fin dimension) (Fin N) (ZMod q))
  let errors := FiniteDist.independent (fun _ : Fin blocks => residueGaussian dimension q width hwidth)
  let flattenMatrix : (Fin blocks → Matrix (Fin dimension) (Fin N) (ZMod q)) ≃
      ((Fin blocks × Fin dimension) → Fin N → ZMod q) :=
    { toFun := fun table index => table index.1 index.2
      invFun := fun table block row => table (block,row)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hp := FiniteDist.map_prod_functions matrices errors
    (fun table (index : Fin blocks × Fin dimension) => table index.1 index.2)
    (fun noise (index : Fin blocks × Fin dimension) => noise index.1 index.2)
  have hm : matrices.map (fun table (index : Fin blocks × Fin dimension) => table index.1 index.2)=
      FiniteDist.uniform ((Fin blocks × Fin dimension) → Fin N → ZMod q) :=
    FiniteDist.uniform_map_equiv flattenMatrix
  unfold larObservedRealTableLaw
  change ((matrices.prod errors).map (fun draw block =>
    (draw.1 block,(draw.1 block).mulVec secret+draw.2 block))).map flattenObserved=_
  calc
    _ = ((matrices.prod errors).map (fun draw =>
        ((fun (index : Fin blocks × Fin dimension) => draw.1 index.1 index.2),
         (fun (index : Fin blocks × Fin dimension) => draw.2 index.1 index.2)))).map
          (fun draw index => (draw.1 index,(draw.1 index) ⬝ᵥ secret+draw.2 index)) := by
      rw [FiniteDist.map_map,FiniteDist.map_map]
      rfl
    _ = ((matrices.map (fun table (index : Fin blocks × Fin dimension) => table index.1 index.2)).prod
        (errors.map (fun noise (index : Fin blocks × Fin dimension) => noise index.1 index.2))).map
          (fun draw index => (draw.1 index,(draw.1 index) ⬝ᵥ secret+draw.2 index)) := by rw [hp]
    _ = _ := by rw [hm,residueGaussian_blocks_flatten]

/-- Starting with independent scalar observations and grouping them produces
exactly the original block source, without a statistical approximation. -/
theorem scalarObserved_regroup (q N dimension blocks : ℕ) [NeZero q]
    (width : ℝ) (hwidth : 0 < width) (secret : Fin N → ZMod q) :
    (((FiniteDist.uniform ((Fin blocks × Fin dimension) → Fin N → ZMod q)).prod
        (FiniteDist.independent (fun _ : Fin blocks × Fin dimension => scalarLaw q width hwidth))).map
          (fun draw index => (draw.1 index,(draw.1 index) ⬝ᵥ secret+draw.2 index))).map regroupObserved=
      larObservedRealTableLaw q N dimension blocks (residueGaussian dimension q width hwidth) secret := by
  rw [←observedRealTable_flatten q N dimension blocks width hwidth secret,FiniteDist.map_map]
  apply FiniteDist.ext
  intro table
  simp only [FiniteDist.map_weight,regroup_flattenObserved]
  exact @Fintype.sum_ite_eq' _ ℝ _ _ (fun first second => Classical.propDecidable (first=second)) table
    (larObservedRealTableLaw q N dimension blocks (residueGaussian dimension q width hwidth) secret).weight

end

end InfoLossLAR.WorstCase.GaussianProjection

end P2MDyadicModule69

/- Helper module Solutions.RegevBridgeGaussianRegroupMachine. -/
section P2MDyadicModule70

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.GaussianRegroupMachine

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.GaussianProjection QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open LARPlatformEncoding

private theorem range_map {Value : Type} (count : ℕ) (f : ℕ → Value) :
    (List.range count).map f=List.ofFn (fun index : Fin count => f index.val) := by
  apply List.ext_getElem <;> simp

theorem rowAt_value {blocks dimension : ℕ} (table : (Fin blocks × Fin dimension) → Row)
    (b : Fin blocks) (r : Fin dimension) :
    rowAt ((List.replicate blocks (), (List.replicate dimension (),naturalRows table)),(b.val,r.val))=
      table (b,r) := by
  have he : b.val*dimension+r.val=(finProdFinEquiv (b,r)).val := by
    change b.val*dimension+r.val=r.val+dimension*b.val
    ac_rfl
  simp only [rowAt,List.length_replicate,naturalRows,he,List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some]
  exact congrArg table (finProdFinEquiv.symm_apply_apply (b,r))

theorem rows_value {blocks dimension : ℕ} (table : (Fin blocks × Fin dimension) → Row)
    (b : Fin blocks) :
    rows ((List.replicate blocks (), (List.replicate dimension (),naturalRows table)),b.val)=
      List.ofFn (fun r => table (b,r)) := by
  simp only [rows,List.length_replicate,range_map]
  apply congrArg List.ofFn
  funext row
  exact rowAt_value table b row

theorem current_value {blocks dimension : ℕ} (table : (Fin blocks × Fin dimension) → Row) :
    current (List.replicate blocks (), (List.replicate dimension (),naturalRows table))=
      List.ofFn (fun b => (List.ofFn (fun r => (table (b,r)).1),List.ofFn (fun r => (table (b,r)).2))) := by
  simp only [current,List.length_replicate,range_map]
  apply congrArg List.ofFn
  funext b
  simp only [block,rows_value,List.map_ofFn,Function.comp_def]

/-- The genuine bounded native serialization produces exactly the platform
block-LWE query. It never reads the hidden secret or unobserved error values. -/
theorem encoded_value {q N blocks dimension : ℕ} (security : ℕ) (pp : Str)
    (table : (Fin blocks × Fin dimension) → (Fin N → ZMod q) × ZMod q) :
    encoded (unary security,(pp,(List.replicate blocks (), (List.replicate dimension (),
      naturalRows (fun index => (List.ofFn (fun column => ((table index).1 column).val),(table index).2.val))))))=
      encInput security pp (encTable (regroupObserved table)) := by
  rw [encoded,current_value]
  exact serializeObservedInput_ofFn security pp (regroupObserved table)

end Integration9_9.GaussianRegroupMachine

end P2MDyadicModule70

/- Helper module Solutions.RegevBridgeNativeLWETableLoader. -/
section P2MDyadicModule71

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

namespace InfoLossLAR.WorstCase.NativeLWETableLoader

open QAlgorithms.Complexity AFT GaussianRandomizedRounding GaussianProjection AFT.BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem rowTicks_length {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (query : Fin dimension → ℚ) (q : ℕ) (squaredWidth : ℚ) (cutoff bits : ℕ) :
    (rowTicks (numericalContext basis query q squaredWidth cutoff bits)).length=(bits+1)+(2*cutoff+1)+1 := by
  simp only [rowTicks,numericalContext,List.length_append,List.length_replicate,List.length_cons,List.length_nil]
  omega

theorem rowRequest_numerical {dimension count : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (values : Fin count → Fin dimension → ℤ) (query : Fin dimension → ℚ) (q : ℕ)
    (squaredWidth : ℚ) (cutoff bits : ℕ)
    (tape : Fin (count*((bits+1)+(2*cutoff+1)+1)) → Fin 2) (row : Fin count) :
    rowRequest (((numericalContext basis query q squaredWidth cutoff bits,List.ofFn (fun i => List.ofFn (values i))),
      List.ofFn (fun j => digitBoolean (tape j))),row.val)=
      IntegerBasis.Native.numericalRequest basis (values row) query q squaredWidth cutoff bits (rowDigits tape row) := by
  simp only [rowRequest,List.getElem?_ofFn,row.isLt,dif_pos,Option.getD_some,rowTicks_length]
  rw [RationalGramSchmidt.Native.rowSlice_ofFn]
  unfold IntegerBasis.Native.numericalRequest numericalContext
  congr 1

/-- Exact per-tape semantics of the entire executable row producer. The
query and width are common to all rows, while source rows and random slices
remain distinct. No hidden nearest point is an input to this program. -/
theorem current_numerical {dimension count : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (values : Fin count → Fin dimension → ℤ) (query : Fin dimension → ℚ) (q : ℕ)
    (squaredWidth : ℚ) (cutoff bits : ℕ)
    (tape : Fin (count*((bits+1)+(2*cutoff+1)+1)) → Fin 2) :
    current ((numericalContext basis query q squaredWidth cutoff bits,List.ofFn (fun i => List.ofFn (values i))),
      List.ofFn (fun j => digitBoolean (tape j)))=
      List.ofFn (fun row => IntegerBasis.Native.output
        (IntegerBasis.Native.numericalRequest basis (values row) query q squaredWidth cutoff bits (rowDigits tape row))) := by
  apply List.ext_getElem
  · simp only [current,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    have hrow : i<count := by simpa only [current,List.length_map,List.length_range,List.length_ofFn] using hi
    simpa only [current,List.length_ofFn,List.getElem_map,List.getElem_range,List.getElem_ofFn] using
      congrArg IntegerBasis.Native.output (rowRequest_numerical basis values query q squaredWidth cutoff bits tape ⟨i,hrow⟩)

end InfoLossLAR.WorstCase.NativeLWETableLoader

end P2MDyadicModule71

/- Helper module Solutions.AdvantageBridgeAffineActualProbability. -/
section P2MDyadicModule72

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity AFT

open scoped BigOperators Classical

/-- Exact coordinate mapping of actual independent products, retaining their
actual finite-index decidable equality instance. -/
theorem actual_independent_map {Index Input Output : Type} [Fintype Index] [DecidableEq Index]
    [Fintype Input] [Fintype Output] (law : Index → FiniteDist Input)
    (decode : Index → Input → Output) :
    (FiniteDist.independent law).map (fun word index => decode index (word index))=
      FiniteDist.independent (fun index => (law index).map (decode index)) := by
  ext values
  simp only [FiniteDist.map_weight,FiniteDist.independent]
  have h := Fintype.prod_sum (fun index point =>
    if decode index point=values index then (law index).weight point else 0)
  apply Eq.trans ?_ h.symm
  apply Finset.sum_congr rfl
  intro word _
  rw [Fintype.prod_ite_zero]
  simp only [funext_iff]

/-- Whole independent paired coordinates are exactly the two independent
coordinate arrays, with their original finite-index instance. -/
theorem actual_independent_prod_expectation {Index First Second : Type}
    [Fintype Index] [DecidableEq Index] [Fintype First] [Fintype Second]
    (first : Index → FiniteDist First) (second : Index → FiniteDist Second)
    (value : (Index → First × Second) → ℝ) :
    (FiniteDist.independent (fun index => (first index).prod (second index))).expectation value=
      (FiniteDist.independent first).expectation (fun left =>
        (FiniteDist.independent second).expectation (fun right => value (fun index => (left index,right index)))) := by
  unfold FiniteDist.expectation FiniteDist.independent
  rw [←(Equiv.arrowProdEquivProdArrow Index (fun _ => First) (fun _ => Second)).symm.sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right _
  simp only [Equiv.arrowProdEquivProdArrow,Equiv.coe_fn_symm_mk,FiniteDist.prod_weight,
    Finset.prod_mul_distrib,mul_assoc]

end InfoLossLAR.WorstCase

end

end P2MDyadicModule72

/- Helper module Solutions.RegevBridgeNativeLWETableLoaderLaw. -/
section P2MDyadicModule73

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

noncomputable section

namespace InfoLossLAR.WorstCase.NativeLWETableLoader

open QAlgorithms.Complexity AFT AFT.BinaryArithmetic GaussianRandomizedRounding

/-- The actual contiguous flat tape, not an assumed array of independent
coins, induces exactly the independent row tapes. -/
theorem flat_row_law (count total : ℕ) :
    (FiniteDist.uniform (Fin (count*total) → Fin 2)).map (fun tape => rowDigits tape)=
      FiniteDist.independent (fun _ : Fin count =>
        FiniteDist.independent (fun _ : Fin total => FiniteDist.uniform (Fin 2))) := by
  rw [show (fun tape : Fin (count*total) → Fin 2 => rowDigits tape)=digitsEquiv count total by rfl,
    FiniteDist.uniform_map_equiv]
  simp only [Wide.independent_uniform]

theorem decode_current_numerical {dimension count : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (values : Fin count → Fin dimension → ℤ)
    (query : Fin dimension → ℚ) (q : ℕ) [NeZero q] (squaredWidth : ℚ) (cutoff bits : ℕ)
    (tape : Fin (count*((bits+1)+(2*cutoff+1)+1)) → Fin 2) :
    decodeTable dimension q count (current
      ((numericalContext basis query q squaredWidth cutoff bits,List.ofFn (fun i => List.ofFn (values i))),
      List.ofFn (fun j => digitBoolean (tape j))))=
      fun row => IntegerBasis.Native.decodeSample dimension q (IntegerBasis.Native.output
        (IntegerBasis.Native.numericalRequest basis (values row) query q squaredWidth cutoff bits (rowDigits tape row))) := by
  rw [current_numerical]
  funext row
  simp only [decodeTable,List.getElem?_ofFn,row.isLt,dif_pos,Option.getD_some]

theorem actualPoolKernel_eq {dimension count : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (values : Fin count → Fin dimension → ℤ)
    (query : Fin dimension → ℚ) (q : ℕ) [NeZero q] (squaredWidth : ℚ) (cutoff bits : ℕ) :
    actualPoolKernel basis values query q squaredWidth cutoff bits=
      FiniteDist.independent (fun row =>
        (FiniteDist.independent (fun _ : Fin ((bits+1)+(2*cutoff+1)+1) => FiniteDist.uniform (Fin 2))).map
          (fun tape => IntegerBasis.Native.decodeSample dimension q (IntegerBasis.Native.output
            (IntegerBasis.Native.numericalRequest basis (values row) query q squaredWidth cutoff bits tape)))) := by
  unfold actualPoolKernel
  simp_rw [decode_current_numerical]
  have h := congrArg (fun law : FiniteDist (Fin count → Fin ((bits+1)+(2*cutoff+1)+1) → Fin 2) =>
    law.map (fun tapes row => IntegerBasis.Native.decodeSample dimension q (IntegerBasis.Native.output
      (IntegerBasis.Native.numericalRequest basis (values row) query q squaredWidth cutoff bits (tapes row)))))
    (flat_row_law count ((bits+1)+(2*cutoff+1)+1))
  rw [FiniteDist.map_map] at h
  exact h.trans (actual_independent_map
    (fun _ : Fin count => FiniteDist.independent (fun _ : Fin ((bits+1)+(2*cutoff+1)+1) => FiniteDist.uniform (Fin 2)))
    (fun row tape => IntegerBasis.Native.decodeSample dimension q (IntegerBasis.Native.output
      (IntegerBasis.Native.numericalRequest basis (values row) query q squaredWidth cutoff bits tape))))

/-- Thus the same actual flat-bit machine is precisely the complete
countable-product channel used in the proved source-table error bound. -/
theorem actualPoolKernel_lattice {dimension count : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (values : Fin count → IntegerBasis.inputLattice basis hdet)
    (query : Fin dimension → ℚ) (q : ℕ) [NeZero q] (squaredWidth : ℚ) (cutoff bits : ℕ) :
    actualPoolKernel basis (fun i => (IntegerBasis.integerBasis basis hdet).equivFun (values i))
      query q squaredWidth cutoff bits=
      FiniteDist.independent (fun row => IntegerBasis.Native.sourceRowKernel basis hdet query q squaredWidth cutoff bits (values row)) :=
  actualPoolKernel_eq _ _ _ _ _ _ _

end InfoLossLAR.WorstCase.NativeLWETableLoader

end

end P2MDyadicModule73

/- Helper module Solutions.RegevBridgeNativeLWETableLoaderObserved. -/
section P2MDyadicModule74

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

namespace InfoLossLAR.WorstCase.NativeLWETableLoader

open QAlgorithms.Complexity AFT AFT.BinaryArithmetic GaussianProjection

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.GaussianRegroupMachine Integration9_9.LARPlatformEncoding

theorem output_canonical {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (value : Fin dimension → ℤ) (query : Fin dimension → ℚ) (q : ℕ) [NeZero q]
    (squaredWidth : ℚ) (hwidth : 1 ≤ squaredWidth) (cutoff bits : ℕ)
    (tape : Fin ((bits+1)+(2*cutoff+1)+1) → Fin 2) :
    IntegerBasis.Native.output (IntegerBasis.Native.numericalRequest basis value query q squaredWidth cutoff bits tape)=
      (List.ofFn (fun i => ((IntegerBasis.Native.decodeSample dimension q
        (IntegerBasis.Native.output (IntegerBasis.Native.numericalRequest basis value query q squaredWidth cutoff bits tape))).1 i).val),
       (IntegerBasis.Native.decodeSample dimension q
        (IntegerBasis.Native.output (IntegerBasis.Native.numericalRequest basis value query q squaredWidth cutoff bits tape))).2.val) := by
  rw [IntegerBasis.Native.decodeSample_numerical basis value query q squaredWidth hwidth,
    IntegerBasis.Native.output_numerical basis value query q squaredWidth hwidth]

/-- Pointwise exact platform input, on every source pool and every flat
random tape. This supplies the actual observed block shape required by
LoadedBatch without assuming a Gaussian or independent source pool. -/
theorem observed_exact {dimension blocks rows : ℕ} (sec : ℕ) (pp : Str)
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (values : Fin (blocks*rows) → Fin dimension → ℤ) (query : Fin dimension → ℚ) (q : ℕ) [NeZero q]
    (squaredWidth : ℚ) (hwidth : 1 ≤ squaredWidth) (cutoff bits : ℕ)
    (tape : Fin ((blocks*rows)*((bits+1)+(2*cutoff+1)+1)) → Fin 2) :
    observed ((unary sec,pp),((List.replicate blocks (),List.replicate rows ()),
      ((numericalContext basis query q squaredWidth cutoff bits,List.ofFn (fun i => List.ofFn (values i))),
        List.ofFn (fun j => digitBoolean (tape j)))))=
      encInput sec pp (encTable (regroupObserved (nativeTable basis values query q squaredWidth cutoff bits tape))) := by
  unfold observed
  rw [current_numerical]
  have hrows : (List.ofFn (fun row => IntegerBasis.Native.output
      (IntegerBasis.Native.numericalRequest basis (values row) query q squaredWidth cutoff bits (rowDigits tape row))))=
      naturalRows (fun index =>
        (List.ofFn (fun column => ((nativeTable basis values query q squaredWidth cutoff bits tape index).1 column).val),
          (nativeTable basis values query q squaredWidth cutoff bits tape index).2.val)) := by
    unfold naturalRows
    apply congrArg List.ofFn
    funext i
    simp only [nativeTable,Equiv.apply_symm_apply]
    exact output_canonical basis (values i) query q squaredWidth hwidth cutoff bits (rowDigits tape i)
  rw [hrows]
  exact encoded_value sec pp _

end InfoLossLAR.WorstCase.NativeLWETableLoader

end P2MDyadicModule74

/- Helper module Solutions.RegevBridgeNativeLWETableLoaderShape. -/
section P2MDyadicModule75

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

noncomputable section

namespace InfoLossLAR.WorstCase.NativeLWETableLoader

open QAlgorithms.Complexity AFT GaussianProjection GaussianRandomizedRounding

open Integration9_9.GaussianRegroupMachine

open scoped BigOperators

private theorem law_ext_expectation {T : Type*} [Fintype T] (first second : FiniteDist T)
    (h : ∀ test : T → ℝ,first.expectation test=second.expectation test) : first=second := by
  classical
  apply FiniteDist.ext
  intro x
  have he := h (fun y => if y=x then 1 else 0)
  simpa [FiniteDist.expectation] using he

theorem ideal_row_prod {q N : ℕ} [NeZero q] (secret : Fin N → ZMod q)
    (noise : FiniteDist (ZMod q)) :
    CosetGeometry.idealLWELaw q secret noise=
      ((FiniteDist.uniform (Fin N → ZMod q)).prod noise).map
        (fun draw => (draw.1,dotProduct draw.1 secret+draw.2)) := by
  apply law_ext_expectation
  intro test
  rw [CosetGeometry.idealLWELaw,FiniteDist.expectation_mix,FiniteDist.expectation_map,
    FiniteDist.expectation_prod]
  apply congrArg (FiniteDist.uniform (Fin N → ZMod q)).expectation
  funext color
  rw [FiniteDist.expectation_map]
  apply congrArg noise.expectation
  funext value
  change test (color,(∑ i,secret i*color i)+value)=test (color,(∑ i,color i*secret i)+value)
  simp only [mul_comm]

/-- The literal ideal scalar table is the independent product expected by
the native row guarantee, for the one fixed common secret. -/
theorem ideal_product_scalar {q N blocks rows : ℕ} [NeZero q]
    (width : ℝ) (hwidth : 0 < width) (secret : Fin N → ZMod q) :
    FiniteDist.independent (fun _ : Fin blocks×Fin rows =>
      CosetGeometry.idealLWELaw q secret (scalarLaw q width hwidth))=
      scalarInputLaw q N rows blocks width hwidth secret := by
  simp_rw [ideal_row_prod]
  rw [←actual_independent_map
    (fun _ : Fin blocks×Fin rows => (FiniteDist.uniform (Fin N → ZMod q)).prod (scalarLaw q width hwidth))
    (fun _ draw => (draw.1,dotProduct draw.1 secret+draw.2))]
  apply law_ext_expectation
  intro test
  rw [FiniteDist.expectation_map,actual_independent_prod_expectation,Wide.independent_uniform]
  rw [scalarInputLaw,FiniteDist.expectation_map,FiniteDist.expectation_prod]
  rfl

theorem independent_product_reindex {T : Type*} [Fintype T] (blocks rows : ℕ) (law : FiniteDist T) :
    (FiniteDist.independent (fun _ : Fin (blocks*rows) => law)).map (productTableEquiv blocks rows)=
      FiniteDist.independent (fun _ : Fin blocks×Fin rows => law) := by
  classical
  ext table
  rw [FiniteDist.map_equiv_weight]
  change (∏ i : Fin (blocks*rows),law.weight (table (finProdFinEquiv.symm i)))=
    ∏ i : Fin blocks×Fin rows,law.weight (table i)
  exact finProdFinEquiv.symm.prod_comp (fun i => law.weight (table i))

/-- Public indexing alone transforms the whole ideal scalar product into
the exact ordinary observed block-Gaussian input used by LoadedBatch. -/
theorem ideal_product_group {q N blocks rows : ℕ} [NeZero q]
    (width : ℝ) (hwidth : 0 < width) (secret : Fin N → ZMod q) :
    (FiniteDist.independent (fun _ : Fin (blocks*rows) =>
      CosetGeometry.idealLWELaw q secret (scalarLaw q width hwidth))).map groupTable=
      larObservedRealTableLaw q N rows blocks (GaussianSource.residueGaussian rows q width hwidth) secret := by
  have h := congrArg (fun law : FiniteDist ((Fin blocks×Fin rows) → ((Fin N → ZMod q)×ZMod q)) =>
    law.map regroupObserved) (independent_product_reindex blocks rows
      (CosetGeometry.idealLWELaw q secret (scalarLaw q width hwidth)))
  rw [FiniteDist.map_map,ideal_product_scalar,scalarInputLaw] at h
  exact h.trans (scalarObserved_regroup q N rows blocks width hwidth secret)

end InfoLossLAR.WorstCase.NativeLWETableLoader

end

end P2MDyadicModule75

/- Helper module Solutions.RegevBridgeIntegerDualCoordinates. -/
section P2MDyadicModule76

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

/-- Each integral dual coordinate is exactly the pairing with the
corresponding original input column. -/
theorem dualCoordinates_inner (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (value : Fin dimension → ℤ) (index : Fin dimension) :
    inner ℝ (dualCoordinates basis hdet value) (integerBasis basis hdet index : Space (dimension:=dimension))=(value index : ℝ) := by
  have hreal : (integerBasis basis hdet index : Space (dimension:=dimension))=realBasis basis hdet index :=
    Module.Basis.restrictScalars_apply ℤ (realBasis basis hdet) index
  have hdual (column row : Fin dimension) :
      inner ℝ (dualRealBasis basis hdet column) (realBasis basis hdet row)=if row=column then 1 else 0 :=
    LinearMap.BilinForm.apply_dualBasis_left inner_nondegenerate (realBasis basis hdet) column row
  rw [dualCoordinates_apply,hreal,sum_inner]
  simp only [←Int.cast_smul_eq_zsmul ℝ,real_inner_smul_left]
  simp_rw [hdual]
  simp

end

end InfoLossLAR.WorstCase.IntegerBasis

end P2MDyadicModule76

/- Helper module Solutions.RegevBridgeRationalInverseAlgebra. -/
section P2MDyadicModule77

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalInverse

open RationalGramSchmidt AFT.RationalNumerics

open scoped BigOperators

noncomputable section

/-- Analytical Cramer specification only. The native implementation below
will use the cached rational orthogonalization and reverse substitution. -/
def dualVector {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : QVector n :=
  fun row => (Matrix.cramer B.transpose (Pi.single i 1) row : ℚ)/(B.det : ℚ)

theorem dualVector_pairing {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (i k : Fin n) : innerQ (dualVector B i) (inputVectors B k)=if k=i then 1 else 0 := by
  have hD : (B.det : ℚ)≠0 := by exact_mod_cast hdet
  have hh:=congrFun (Matrix.mulVec_cramer B.transpose (Pi.single i 1)) k
  simp only [Matrix.mulVec,dotProduct,Matrix.det_transpose,Pi.smul_apply,smul_eq_mul,
    Matrix.transpose_apply,Pi.single_apply] at hh
  have hcast : (∑ row,(B row k : ℚ)*(Matrix.cramer B.transpose (Pi.single i 1) row : ℚ))=
      (B.det : ℚ)*(if k=i then 1 else 0) := by exact_mod_cast hh
  calc
    _ = (∑ row,(B row k : ℚ)*(Matrix.cramer B.transpose (Pi.single i 1) row : ℚ))/(B.det : ℚ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro row _
      simp only [innerQ,dualVector,inputVectors]
      ring
    _ = ((B.det : ℚ)*(if k=i then 1 else 0))/(B.det : ℚ) := by rw [hcast]
    _ = _ := by split_ifs <;> simp [hD]

/-- Pairings with the original input columns determine the entire real
vector, using the actual Euclidean dual basis. -/
theorem real_pairings_unique {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (x y : IntegerBasis.Space (dimension:=n))
    (h : ∀ k,inner ℝ x (IntegerBasis.realBasis B hdet k)=inner ℝ y (IntegerBasis.realBasis B hdet k)) : x=y := by
  apply (IntegerBasis.dualRealBasis B hdet).ext_elem
  intro k
  change ((LinearMap.BilinForm.dualBasis (innerₗ _) IntegerBasis.inner_nondegenerate
    (IntegerBasis.realBasis B hdet)).repr x) k=
    ((LinearMap.BilinForm.dualBasis (innerₗ _) IntegerBasis.inner_nondegenerate
      (IntegerBasis.realBasis B hdet)).repr y) k
  rw [LinearMap.BilinForm.dualBasis_repr_apply,LinearMap.BilinForm.dualBasis_repr_apply]
  exact h k

theorem dualVector_real {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (i : Fin n) :
    realVec (dualVector B i)=IntegerBasis.dualRealBasis B hdet i := by
  apply real_pairings_unique B hdet
  intro k
  have hx : inner ℝ (realVec (dualVector B i)) (IntegerBasis.realBasis B hdet k)=if k=i then 1 else 0 := by
    rw [←inputVectors_real B hdet k,←innerQ_real,dualVector_pairing B hdet]
    split_ifs <;> norm_num
  rw [hx]
  exact (LinearMap.BilinForm.apply_dualBasis_left IntegerBasis.inner_nondegenerate
    (IntegerBasis.realBasis B hdet) i k).symm

theorem rational_pairings_unique {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (x y : QVector n) (h : ∀ k,innerQ x (inputVectors B k)=innerQ y (inputVectors B k)) : x=y := by
  apply realVec_injective
  apply real_pairings_unique B hdet
  intro k
  rw [←inputVectors_real B hdet k,←innerQ_real,←innerQ_real,h k]

/-- A coarse binary determinant bound has polynomial exponent in dimension
and original integer entry height. -/
theorem determinant_binary_bound {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (H : ℕ)
    (hentries : ∀ r c,|B r c|≤(2 : ℤ)^H) : |B.det|≤(2 : ℤ)^((n+H)*n) := by
  have hdim : (n : ℤ)≤2^n := by exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have hfac : (n.factorial : ℤ)≤2^(n*n) := by
    calc
      _ ≤ (n : ℤ)^n := by exact_mod_cast Nat.factorial_le_pow n
      _ ≤ ((2 : ℤ)^n)^n := pow_le_pow_left₀ (Nat.cast_nonneg _) hdim _
      _ = _ := by rw [←pow_mul]
  have hh:=Matrix.det_le (abv:=AbsoluteValue.abs) hentries
  have hd : |B.det|≤(n.factorial : ℤ)*((2 : ℤ)^H)^n := by
    simpa only [AbsoluteValue.abs_apply,Fintype.card_fin,nsmul_eq_mul] using hh
  calc
    _ ≤ (n.factorial : ℤ)*((2 : ℤ)^H)^n := hd
    _ ≤ (2 : ℤ)^(n*n)*((2 : ℤ)^H)^n := mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = _ := by rw [←pow_mul,←pow_add];congr 1;ring

theorem cramer_binary_bound {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (H : ℕ)
    (hentries : ∀ r c,|B r c|≤(2 : ℤ)^H) (i row : Fin n) :
    |Matrix.cramer B.transpose (Pi.single i 1) row|≤(2 : ℤ)^((n+H)*n) := by
  rw [Matrix.cramer_apply]
  apply determinant_binary_bound _ H
  intro r c
  simp only [Matrix.updateCol_apply,Matrix.transpose_apply]
  split_ifs
  · simp only [Pi.single_apply]
    split_ifs <;> simp
    exact one_le_pow₀ (by norm_num : (1 : ℤ)≤2)
  · exact hentries c r

def dualHeight (n H : ℕ) : ℕ := 2*((n+H)*n)

theorem dualVector_height {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (H : ℕ)
    (hentries : ∀ r c,|B r c|≤(2 : ℤ)^H) (i row : Fin n) :
    HeightBound (dualVector B i row) (dualHeight n H) := by
  have hnum : (Matrix.cramer B.transpose (Pi.single i 1) row).natAbs≤2^((n+H)*n) := by
    have hh : ((Matrix.cramer B.transpose (Pi.single i 1) row).natAbs : ℤ)≤(2 : ℤ)^((n+H)*n) := by
      simpa only [Int.natCast_natAbs] using cramer_binary_bound B H hentries i row
    exact_mod_cast hh
  have hden : B.det.natAbs≤2^((n+H)*n) := by
    have hh : (B.det.natAbs : ℤ)≤(2 : ℤ)^((n+H)*n) := by
      simpa only [Int.natCast_natAbs] using determinant_binary_bound B H hentries
    exact_mod_cast hh
  have hh:=(HeightBound.of_int hnum).div (HeightBound.of_int hden)
  simpa only [dualVector,dualHeight,two_mul] using hh

end

end InfoLossLAR.WorstCase.RationalInverse

end P2MDyadicModule77

/- Helper module Solutions.RegevBridgeRationalInverseRecurrence. -/
section P2MDyadicModule78

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalInverse

open RationalGramSchmidt AFT.RationalNumerics

open scoped BigOperators

@[simp] theorem innerQ_sub_left {n : ℕ} (x y z : QVector n) :
    innerQ (x-y) z=innerQ x z-innerQ y z := by simp [innerQ,sub_mul,Finset.sum_sub_distrib]

@[simp] theorem innerQ_smul_left {n : ℕ} (a : ℚ) (x y : QVector n) :
    innerQ (a • x) y=a*innerQ x y := by simp [innerQ,Finset.mul_sum,mul_assoc]

theorem innerQ_sum_left {n : ℕ} {J : Type*} (s : Finset J) (x : J → QVector n) (y : QVector n) :
    innerQ (∑ j∈s,x j) y=∑ j∈s,innerQ (x j) y := by
  simp only [innerQ,Finset.sum_apply,Finset.sum_mul]
  rw [Finset.sum_comm]

/-- One reverse triangular substitution step. Its only arithmetic operands
are the cached original rational orthogonalization and future dual columns. -/
def dualStep {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (cache : Fin n → QVector n) (i : Fin n) : QVector n :=
  (squaredNorm (inputVectors B) i)⁻¹ • orthogonal (inputVectors B) i-
    ∑ j∈Finset.Ioi i,upper (inputVectors B) i j • cache j

noncomputable section

theorem dualStep_pairing {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (cache : Fin n → QVector n) (i k : Fin n)
    (hcache : ∀ j,i< j → cache j=dualVector B j) :
    innerQ (dualStep B cache i) (inputVectors B k)=if k=i then 1 else 0 := by
  rw [dualStep,innerQ_sub_left,innerQ_smul_left,innerQ_sum_left]
  simp only [innerQ_smul_left]
  have hfirst : (squaredNorm (inputVectors B) i)⁻¹*innerQ (orthogonal (inputVectors B) i) (inputVectors B k)=
      upper (inputVectors B) i k := by unfold upper;ring
  rw [hfirst]
  have hsum : (∑ j∈Finset.Ioi i,upper (inputVectors B) i j*innerQ (cache j) (inputVectors B k))=
      if i< k then upper (inputVectors B) i k else 0 := by
    calc
      _ = ∑ j∈Finset.Ioi i,if k=j then upper (inputVectors B) i j else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcache j (Finset.mem_Ioi.mp hj),dualVector_pairing B hdet]
        split_ifs <;> simp
      _ = _ := by simp only [Finset.sum_ite_eq,Finset.mem_Ioi]
  rw [hsum]
  by_cases he : k=i
  · subst k
    simp [upper_diagonal _ (inputVectors_independent B hdet)]
  · by_cases hi : i< k
    · simp [hi,he]
    · have hk : k< i := lt_of_le_of_ne (le_of_not_gt hi) he
      rw [upper_triangular _ i k hk]
      simp [hi,he]

theorem dualStep_correct {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (cache : Fin n → QVector n) (i : Fin n)
    (hcache : ∀ j,i< j → cache j=dualVector B j) : dualStep B cache i=dualVector B i := by
  apply rational_pairings_unique B hdet
  intro k
  rw [dualStep_pairing B hdet cache i k hcache,dualVector_pairing B hdet]

/-- A complete matrix cache is updated from the last column backwards.
Every completed column is already a final original-input dual column. -/
def dualCache {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : ℕ → Fin n → QVector n
  | 0 => fun _ => 0
  | steps+1 =>
      let previous :=dualCache B steps
      if h : steps< n then
        let i : Fin n :=⟨n-1-steps,by omega⟩
        Function.update previous i (dualStep B previous i)
      else previous

theorem dualCache_formula {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (steps : ℕ) (hsteps : steps≤ n) (j : Fin n) :
    dualCache B steps j=if n-steps≤ j.val then dualVector B j else 0 := by
  induction steps generalizing j with
  | zero =>
    have hj : ¬n≤ j.val := by omega
    simp [dualCache,hj]
  | succ steps ih =>
    have hs : steps< n := by omega
    let i : Fin n :=⟨n-1-steps,by omega⟩
    have hf : ∀ k,i< k → dualCache B steps k=dualVector B k := by
      intro k hk
      rw [ih (by omega) k]
      have ht : n-steps≤ k.val := by change i.val< k.val at hk;dsimp [i] at hk;omega
      simp only [if_pos ht]
    have he:=dualStep_correct B hdet (dualCache B steps) i hf
    change (if h : steps< n then Function.update (dualCache B steps)
      (⟨n-1-steps,by omega⟩ : Fin n) (dualStep B (dualCache B steps) ⟨n-1-steps,by omega⟩) else dualCache B steps) j=_
    rw [dif_pos hs]
    change Function.update (dualCache B steps) i (dualStep B (dualCache B steps) i) j=_
    rw [he]
    by_cases hj : j=i
    · subst j
      rw [Function.update_self]
      have ht : n-(steps+1)≤ i.val := by dsimp [i];omega
      simp only [if_pos ht]
    · rw [Function.update_of_ne hj,ih (by omega) j]
      have hv : j.val≠n-1-steps := by intro h;apply hj;exact Fin.ext h
      have ht : (n-steps≤ j.val)=(n-(steps+1)≤ j.val) := propext (by omega)
      simp only [ht]

theorem dualCache_complete {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    dualCache B n=dualVector B := by
  funext j
  rw [dualCache_formula B hdet n (le_refl n)]
  simp

theorem dualCache_height {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (H : ℕ) (hentries : ∀ r c,|B r c|≤(2 : ℤ)^H)
    (steps : ℕ) (hs : steps≤ n) (j row : Fin n) :
    HeightBound (dualCache B steps j row) (coordinateHeight n H) := by
  rw [dualCache_formula B hdet steps hs]
  split_ifs
  · exact (dualVector_height B H hentries j row).mono (by unfold dualHeight coordinateHeight;nlinarith)
  · exact HeightBound.zero.mono (Nat.zero_le _)

end

end InfoLossLAR.WorstCase.RationalInverse

end P2MDyadicModule78

/- Helper module Solutions.RegevBridgeRationalInverseNative. -/
section P2MDyadicModule79

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalInverse.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open RationalGramSchmidt

open RationalGramSchmidt.Native

open scoped BigOperators

abbrev Context := List (List ℚ) × List (List ℚ)

abbrev State := Context × (List Unit × List (List ℚ))

/-- One rational summand of reverse triangular substitution. -/
def term (input : (((Context × List (List ℚ)) × ℕ) × ℕ) × ℕ) : ℚ :=
  let source := input.1
  let gs := source.1.1.1.2[source.1.2]?.getD []
  if source.1.2< input.2 then
    dot (gs,source.1.1.1.1[input.2]?.getD [])/dot (gs,gs)*
      (source.1.1.2[input.2]?.getD [])[source.2]?.getD 0 else 0

/-- One entry uses only native rational operations and bounded index lists. -/
def entry (input : ((Context × List (List ℚ)) × ℕ) × ℕ) : ℚ :=
  let gs := input.1.1.1.2[input.1.2]?.getD []
  gs[input.2]?.getD 0/dot (gs,gs)-
    ((List.range input.1.1.1.1.length).map (fun j => term (input,j))).sum

def column (input : (Context × List (List ℚ)) × ℕ) : List ℚ :=
  (List.range input.1.1.1.length).map (fun row => entry (input,row))

def replaceColumn (input : (List (List ℚ) × ℕ) × List ℚ) : List (List ℚ) :=
  (List.range input.1.1.length).map (fun j => if j=input.1.2 then input.2 else input.1.1[j]?.getD [])

/-- A public encoding-length guard bounds every fold state, including
malformed and singular inputs. Correctness proves that it never fires on
nonsingular original integer matrices. -/
def step (state : State) (counter : ℕ) : State :=
  let index := state.1.1.length-1-counter
  let next := replaceColumn ((state.2.2,index),column ((state.1,state.2.2),index))
  (state.1,(state.2.1,if (matrixTicks next).length≤ state.2.1.length then next else []))

/-- The actual cache consumes the original row-major integer input. The
only preprocessing is the previously certified native orthogonalization. -/
def cached (input : List (List ℤ)) : List (List ℚ) :=
  let original := rationalColumns (transpose input)
  let gs := basisCache input
  let zeros := original.map (fun row => row.map (fun _ => (0 : ℚ)))
  ((List.range input.length).foldl step ((original,gs),(inputBudget input,zeros))).2.2

def transposeRational (input : List (List ℚ)) : List (List ℚ) :=
  (List.range input.length).map (fun row => input.map (fun column => column[row]?.getD 0))

/-- Native row-major output for the original integer matrix's inverse
transpose. No determinant, real dual-basis or arbitrary real oracle is
called by this program. -/
def current (input : List (List ℤ)) : List (List ℚ) := transposeRational (cached input)

end InfoLossLAR.WorstCase.RationalInverse.Native

end P2MDyadicModule79

/- Helper module Solutions.RegevBridgeRationalInverseRefinement. -/
section P2MDyadicModule80

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalInverse.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open RationalGramSchmidt

open RationalGramSchmidt.Native

open scoped BigOperators

noncomputable section

def matrixOf {n : ℕ} (vectors : Fin n → QVector n) : List (List ℚ) :=
  List.ofFn (fun j => List.ofFn (vectors j))

def context {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : Context :=
  (matrixOf (inputVectors B),matrixOf (orthogonal (inputVectors B)))

theorem term_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (cache : Fin n → QVector n) (i row j : Fin n) :
    term ((((context B,matrixOf cache),i.val),row.val),j.val)=
      if i< j then upper (inputVectors B) i j*cache j row else 0 := by
  simp only [term,context,matrixOf,List.getElem?_ofFn,i.isLt,j.isLt,row.isLt,
    ↓reduceDIte,Option.getD_some,dot_ofFn]
  rfl

theorem column_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (cache : Fin n → QVector n) (i : Fin n) :
    column ((context B,matrixOf cache),i.val)=List.ofFn (dualStep B cache i) := by
  apply List.ext_getElem
  · simp only [column,context,matrixOf,List.length_map,List.length_range,List.length_ofFn]
  · intro row hfirst hsecond
    have hr : row< n := by simpa only [List.length_ofFn] using hsecond
    let r : Fin n :=⟨row,hr⟩
    have hs : (List.range n).map (fun j => term ((((context B,matrixOf cache),i.val),row),j))=
        List.ofFn (fun j : Fin n => if i< j then upper (inputVectors B) i j*cache j r else 0) := by
      apply List.ext_getElem
      · simp
      · intro j hj hk
        have hjn : j< n := by simpa using hj
        simpa only [List.getElem_map,List.getElem_range,List.getElem_ofFn] using term_ofFn B cache i r ⟨j,hjn⟩
    have hi : Finset.Ioi i=Finset.univ.filter (fun j => i< j) := by ext j;simp
    have hlen : (context B).1.length=n := by simp [context,matrixOf]
    simp only [column,hlen,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    change entry ((((context B,matrixOf cache),i.val),row))=dualStep B cache i r
    simp only [entry,hlen]
    rw [hs,Fin.sum_ofFn]
    simp only [context,matrixOf,List.getElem?_ofFn,i.isLt,hr,↓reduceDIte,Option.getD_some,dot_ofFn]
    simp only [dualStep,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,hi,Finset.sum_filter,squaredNorm,ite_apply,Pi.zero_apply]
    ring

theorem replaceColumn_ofFn {n : ℕ} (cache : Fin n → QVector n) (i : Fin n) (value : QVector n) :
    replaceColumn ((matrixOf cache,i.val),List.ofFn value)=matrixOf (Function.update cache i value) := by
  apply List.ext_getElem
  · simp [replaceColumn,matrixOf]
  · intro j hj hk
    have hjn : j< n := by simpa only [matrixOf,List.length_ofFn] using hk
    let k : Fin n :=⟨j,hjn⟩
    simp only [replaceColumn,matrixOf,List.length_ofFn,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    change (if j=i.val then List.ofFn value else (List.ofFn (fun j => List.ofFn (cache j)))[j]?.getD [])=
      List.ofFn (Function.update cache i value k)
    by_cases h : k=i
    · subst k
      have hjval : j=i.val := congrArg Fin.val h
      simp only [hjval,ite_true,Function.update_self]
    · have hji : j≠i.val := by intro he;apply h;exact Fin.ext he
      simp only [hji,if_false,List.getElem?_ofFn,hjn,↓reduceDIte,Option.getD_some,Function.update_of_ne h]
      rfl

/-- The Cramer bound controls every whole reverse-substitution cache. -/
theorem dualCache_encoding_bound {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (H : ℕ) (hentries : ∀ r c,|B r c|≤ (2 : ℤ)^H) (steps : ℕ) (hs : steps≤ n) :
    (encodeList (encodeList Ratio.encode) (matrixOf (dualCache B steps))).length≤ cacheEncodingBound n H := by
  have he := encoded_list_length_bound (encodeList Ratio.encode) (matrixOf (dualCache B steps))
    (n*(6*coordinateHeight n H+21)) (by
      intro vector hv
      obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hv
      exact vector_encoding_height _ _ (fun row => dualCache_height B hdet H hentries steps hs j row))
  simpa only [matrixOf,List.length_ofFn,cacheEncodingBound,Nat.mul_assoc] using he

theorem step_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (ticks : List Unit)
    (steps : ℕ) (hs : steps< n)
    (hb : (encodeList (encodeList Ratio.encode) (matrixOf (dualCache B (steps+1)))).length≤ ticks.length) :
    step (context B,(ticks,matrixOf (dualCache B steps))) steps=
      (context B,(ticks,matrixOf (dualCache B (steps+1)))) := by
  let i : Fin n :=⟨n-1-steps,by omega⟩
  have hn : replaceColumn ((matrixOf (dualCache B steps),i.val),
      column ((context B,matrixOf (dualCache B steps)),i.val))=matrixOf (dualCache B (steps+1)) := by
    rw [column_ofFn,replaceColumn_ofFn]
    rw [dualCache,dif_pos hs]
  have hg : (matrixTicks (replaceColumn ((matrixOf (dualCache B steps),i.val),
      column ((context B,matrixOf (dualCache B steps)),i.val)))).length≤ ticks.length := by
    rw [hn,matrixTicks_length]
    exact hb
  have hlen : (context B).1.length=n := by simp [context,matrixOf]
  simp only [step,hlen]
  change (context B,(ticks,if (matrixTicks (replaceColumn ((matrixOf (dualCache B steps),i.val),
      column ((context B,matrixOf (dualCache B steps)),i.val)))).length≤ ticks.length then _ else []))=_
  rw [if_pos hg,hn]

theorem fold_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (ticks : List Unit)
    (hb : ∀ steps,steps≤ n →
      (encodeList (encodeList Ratio.encode) (matrixOf (dualCache B steps))).length≤ ticks.length)
    (steps : ℕ) (hs : steps≤ n) :
    (List.range steps).foldl step (context B,(ticks,matrixOf (fun _ : Fin n => (0 : QVector n))))=
      (context B,(ticks,matrixOf (dualCache B steps))) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    rw [List.range_succ,List.foldl_append,ih (by omega),List.foldl_cons,List.foldl_nil]
    exact step_ofFn B ticks steps (by omega) (hb (steps+1) hs)

def inputRows {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : List (List ℤ) :=
  List.ofFn (fun row => List.ofFn (fun col => B row col))

theorem inputRows_dimension {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    n≤ (integerMatrixTicks (inputRows B)).length := inputColumns_dimension B.transpose

theorem inputRows_entry_height {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (row col : Fin n) :
    |B row col|≤ (2 : ℤ)^(integerMatrixTicks (inputRows B)).length :=
  inputColumns_entry_height B.transpose col row

theorem basisCache_matrix {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    basisCache (inputRows B)=matrixOf (orthogonal (inputVectors B)) := by
  rw [inputRows,basisCache_correct B hdet,cache_prefix_eq _ n (le_refl n),List.map_ofFn]
  rfl

/-- Exact refinement of the guarded reverse loop for every nonsingular
original integer input; the public bit-size guard never changes its data. -/
theorem cached_correct {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    cached (inputRows B)=matrixOf (dualVector B) := by
  have hb : ∀ steps,steps≤ n →
      (encodeList (encodeList Ratio.encode) (matrixOf (dualCache B steps))).length≤ (inputBudget (inputRows B)).length := by
    intro steps hs
    apply (dualCache_encoding_bound B hdet (integerMatrixTicks (inputRows B)).length
      (inputRows_entry_height B) steps hs).trans
    rw [inputBudget_length]
    exact cacheEncodingBound_coarse n _ _ (inputRows_dimension B) le_rfl
  have ho : rationalColumns (transpose (inputRows B))=matrixOf (inputVectors B) := by
    rw [inputRows,transpose_input_rows,rationalColumns_input]
    rfl
  have hz : (matrixOf (inputVectors B)).map (fun row => row.map (fun _ => (0 : ℚ)))=
      matrixOf (fun _ : Fin n => (0 : QVector n)) := by
    simp only [matrixOf,List.map_ofFn,Function.comp_def]
    rfl
  unfold cached
  rw [ho,basisCache_matrix B hdet]
  dsimp only
  rw [hz]
  have hl : (inputRows B).length=n := by simp [inputRows]
  rw [hl]
  change ((List.range n).foldl step
    (context B,(inputBudget (inputRows B),matrixOf (fun _ : Fin n => (0 : QVector n))))).2.2=_
  rw [fold_ofFn B _ hb n (le_refl n),dualCache_complete B hdet]

theorem transposeRational_ofFn {n : ℕ} (v : Fin n → QVector n) :
    transposeRational (matrixOf v)=List.ofFn (fun row : Fin n => List.ofFn (fun col : Fin n => v col row)) := by
  apply List.ext_getElem
  · simp [transposeRational,matrixOf]
  · intro row hr hs
    have hrow : row< n := by simpa using hs
    simp only [transposeRational,matrixOf,List.length_ofFn,List.getElem_map,List.getElem_range,
      List.getElem_ofFn,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,hrow,↓reduceDIte,Option.getD_some]

/-- Row-major output is exactly the original matrix inverse transpose. -/
theorem current_correct {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    current (inputRows B)=List.ofFn (fun row : Fin n => List.ofFn (fun col : Fin n => dualVector B col row)) := by
  rw [current,cached_correct B hdet,transposeRational_ofFn]

end

end InfoLossLAR.WorstCase.RationalInverse.Native

end P2MDyadicModule80

/- Helper module Solutions.RegevBridgeBDDResidualStep. -/
section P2MDyadicModule81

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

noncomputable section

variable {dimension : ℕ}

theorem reconstruct_residualNearest (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (q : ℕ) [NeZero q] (nearest : dual (inputLattice basis hdet)) :
    reconstructPoint basis hdet q (secretCoordinates q (inputLattice basis hdet) (integerBasis basis hdet) nearest)
      (residualNearest basis hdet q nearest : Space (dimension:=dimension))=(nearest : Space (dimension:=dimension)) := by
  have hq : (q : ℝ)≠0 := by exact_mod_cast NeZero.ne q
  simp only [reconstructPoint,residualNearest,smul_smul,mul_inv_cancel₀ hq,one_smul,sub_add_cancel]

end

end InfoLossLAR.WorstCase.IntegerBasis

end P2MDyadicModule81

/- Helper module Solutions.RegevBridgeBDDNativeArithmetic. -/
section P2MDyadicModule82

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.BDDNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics RationalGramSchmidt RationalInverse

open RationalGramSchmidt.Native

open scoped BigOperators

/-- Apply the actual native original inverse transpose to arbitrary signed
integer coordinates. Invalid input shapes retain total list semantics. -/
def lift (input : List (List ℤ) × List ℤ) : List ℚ :=
  (RationalInverse.Native.current input.1).map (fun row =>
    dot (row,input.2.map (fun value : ℤ => (value : ℚ))))

end InfoLossLAR.WorstCase.BDDNative

end P2MDyadicModule82

/- Helper module Solutions.RegevBridgeBDDNativeSemantics. -/
section P2MDyadicModule83

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.BDDNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics RationalGramSchmidt RationalInverse

open RationalGramSchmidt.Native

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

def combination {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (coords : Fin n → ℤ) : QVector n :=
  ∑ col,(coords col : ℚ) • dualVector B col

theorem lift_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (coords : Fin n → ℤ) :
    lift (RationalInverse.Native.inputRows B,List.ofFn coords)=List.ofFn (combination B coords) := by
  rw [lift,RationalInverse.Native.current_correct B hdet]
  simp only [List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext row
  rw [dot_ofFn]
  simp only [innerQ,combination,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro col _
  ring

theorem realVec_sum {n : ℕ} {J : Type*} (s : Finset J) (vectors : J → QVector n) :
    realVec (∑ j∈s,vectors j)=∑ j∈s,realVec (vectors j) := by
  ext row
  simp [realVec,Finset.sum_apply,Rat.cast_sum]

theorem combination_real {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (coords : Fin n → ℤ) :
    realVec (combination B coords)=IntegerBasis.dualCoordinates B hdet coords := by
  rw [combination,realVec_sum,IntegerBasis.dualCoordinates_apply]
  apply Finset.sum_congr rfl
  intro col _
  rw [realVec_smul,dualVector_real B hdet]
  simp only [Rat.cast_intCast,Int.cast_smul_eq_zsmul]

end

end InfoLossLAR.WorstCase.BDDNative

end P2MDyadicModule83

/- Helper module Solutions.RegevBridgeBDDTranscriptSemantics. -/
section P2MDyadicModule84

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.BDDNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics RationalGramSchmidt RationalInverse

open RationalGramSchmidt.Native

open Integration9_9.TM2NativeFiniteSeries

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

def digitCoefficients {n steps : ℕ} (q : ℕ) (digits : Fin steps → Fin n → ℕ) : Fin n → ℤ :=
  fun row => ∑ k : Fin steps,(q : ℤ)^k.val*(digits k row : ℤ)

def terminalQuery {n steps : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (q : ℕ)
    (query : QVector n) (digits : Fin steps → Fin n → ℕ) : QVector n :=
  ((q : ℚ)^steps)⁻¹ • (query-combination B (digitCoefficients q digits))

end

end InfoLossLAR.WorstCase.BDDNative

end P2MDyadicModule84

/- Helper module Solutions.RegevBridgeBDDNativeIteration. -/
section P2MDyadicModule85

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.BDDNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics RationalGramSchmidt RationalInverse

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

/-- The hidden lattice points are specifications only. Neither the native
transcript processor nor its verifier reads this sequence. -/
def nearestSequence {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (q : ℕ) [NeZero q] (nearest : dual (IntegerBasis.inputLattice B hdet)) :
    ℕ → dual (IntegerBasis.inputLattice B hdet)
  | 0 => nearest
  | k+1 => IntegerBasis.residualNearest B hdet q (nearestSequence B hdet q nearest k)

def goodDigits {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (q : ℕ) [NeZero q] (nearest : dual (IntegerBasis.inputLattice B hdet)) (k : ℕ) (row : Fin n) : ℕ :=
  (secretCoordinates q (IntegerBasis.inputLattice B hdet) (IntegerBasis.integerBasis B hdet)
    (nearestSequence B hdet q nearest k) row).val

def goodPrefix {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (q : ℕ) [NeZero q] (nearest : dual (IntegerBasis.inputLattice B hdet)) (steps : ℕ) :
    IntegerBasis.Space (dimension:=n) :=
  ∑ k∈Finset.range steps,(q : ℝ)^k • IntegerBasis.secretLift B hdet q
    (secretCoordinates q (IntegerBasis.inputLattice B hdet) (IntegerBasis.integerBasis B hdet)
      (nearestSequence B hdet q nearest k))

theorem goodPrefix_telescopes {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (q : ℕ) [NeZero q] (nearest : dual (IntegerBasis.inputLattice B hdet)) (steps : ℕ) :
    goodPrefix B hdet q nearest steps=(nearest : IntegerBasis.Space (dimension:=n))-
      (q : ℝ)^steps • (nearestSequence B hdet q nearest steps : IntegerBasis.Space (dimension:=n)) := by
  induction steps with
  | zero => simp [goodPrefix,nearestSequence]
  | succ steps ih =>
    have hr := IntegerBasis.reconstruct_residualNearest B hdet q (nearestSequence B hdet q nearest steps)
    have hs : (nearestSequence B hdet q nearest steps : IntegerBasis.Space (dimension:=n))-
        IntegerBasis.secretLift B hdet q
          (secretCoordinates q (IntegerBasis.inputLattice B hdet) (IntegerBasis.integerBasis B hdet)
            (nearestSequence B hdet q nearest steps))=
        (q : ℝ) • (nearestSequence B hdet q nearest (steps+1) : IntegerBasis.Space (dimension:=n)) := by
      change (q : ℝ) • (nearestSequence B hdet q nearest (steps+1) : IntegerBasis.Space (dimension:=n))+_= _ at hr
      rw [←hr]
      abel
    rw [goodPrefix,Finset.sum_range_succ]
    change goodPrefix B hdet q nearest steps+_= _
    rw [ih]
    calc
      _ = (nearest : IntegerBasis.Space (dimension:=n))-(q : ℝ)^steps •
          ((nearestSequence B hdet q nearest steps : IntegerBasis.Space (dimension:=n))-
            IntegerBasis.secretLift B hdet q
              (secretCoordinates q (IntegerBasis.inputLattice B hdet) (IntegerBasis.integerBasis B hdet)
                (nearestSequence B hdet q nearest steps))) := by module
      _ = _ := by rw [hs,smul_smul,pow_succ]

theorem goodCombination_real {n steps : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (q : ℕ) [NeZero q] (nearest : dual (IntegerBasis.inputLattice B hdet)) :
    realVec (combination B (digitCoefficients q (fun k : Fin steps => goodDigits B hdet q nearest k.val)))=
      goodPrefix B hdet q nearest steps := by
  rw [combination_real B hdet]
  have hc : digitCoefficients q (fun k : Fin steps => goodDigits B hdet q nearest k.val)=
      ∑ k : Fin steps,(q : ℤ)^k.val • (fun row => (goodDigits B hdet q nearest k.val row : ℤ)) := by
    funext row
    simp only [digitCoefficients,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [hc,map_sum]
  simp only [map_smul]
  unfold goodPrefix
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro k _
  simp only [←Int.cast_smul_eq_zsmul ℝ,Int.cast_pow,Int.cast_natCast,IntegerBasis.secretLift,goodDigits]

/-- The complete transcript formula is exactly the iterative residual
query when each decoded residue is correct. -/
theorem terminalQuery_error {n steps : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (q : ℕ) [NeZero q] (query : QVector n) (nearest : dual (IntegerBasis.inputLattice B hdet)) :
    realVec (terminalQuery B q query (fun k : Fin steps => goodDigits B hdet q nearest k.val))-
      (nearestSequence B hdet q nearest steps : IntegerBasis.Space (dimension:=n))=
      ((q : ℝ)^steps)⁻¹ • (realVec query-(nearest : IntegerBasis.Space (dimension:=n))) := by
  have hq : (q : ℝ)^steps≠0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne q)
  rw [terminalQuery,realVec_smul,realVec_sub,goodCombination_real B hdet,goodPrefix_telescopes]
  simp only [Rat.cast_inv,Rat.cast_pow,Rat.cast_natCast]
  rw [smul_sub,smul_sub,smul_smul,inv_mul_cancel₀ hq,one_smul]
  module

/-- All successful residual stages contract the full Euclidean error by
the exact modulus power. The explicit stopping condition is retained. -/
theorem terminalQuery_error_norm {n steps : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (q : ℕ) [NeZero q] (query : QVector n) (nearest : dual (IntegerBasis.inputLattice B hdet)) :
    ‖realVec (terminalQuery B q query (fun k : Fin steps => goodDigits B hdet q nearest k.val))-
      (nearestSequence B hdet q nearest steps : IntegerBasis.Space (dimension:=n))‖=
      ‖realVec query-(nearest : IntegerBasis.Space (dimension:=n))‖/(q : ℝ)^steps := by
  rw [terminalQuery_error B hdet,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (pow_pos (by exact_mod_cast NeZero.pos q) steps))]
  ring

end

end InfoLossLAR.WorstCase.BDDNative

end P2MDyadicModule85

/- Helper module HonestResidualTables. -/
section P2MDyadicModule86

set_option exponentiation.threshold 1024

set_option autoImplicit false

open scoped BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch

open AFT.GaussianSource

private theorem grid_weight_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (z : ℤ) :
    weight a z ≤ weight b z := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg
    (div_le_div_of_nonneg_left Real.pi_pos.le (sq_pos_of_pos ha)
      ((sq_le_sq₀ ha.le (ha.trans_le hab).le).mpr hab))) (sq_nonneg _)

private theorem grid_theta_reciprocal (a : ℝ) (ha : 0 < a) :
    realNormalizer a = a * realNormalizer a⁻¹ := by
  have hp := Real.tsum_exp_neg_mul_int_sq (sq_pos_of_pos ha)
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq ha.le] at hp
  have hw (z : ℤ) : weight a⁻¹ z = Real.exp (-Real.pi * a ^ 2 * (z:ℝ)^2) := by
    unfold weight
    congr 1
    rw [inv_pow, div_inv_eq_mul]
    ring
  have he (z : ℤ) : weight a z = Real.exp (-Real.pi / a ^ 2 * (z:ℝ)^2) := by
    unfold weight
    rw [neg_div]
  unfold realNormalizer
  simp_rw [hw, he]
  rw [hp]
  field_simp

private theorem grid_tv_bound {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑' z : ℤ, |weight a z / realNormalizer a - weight b z / realNormalizer b|)/2 ≤
      (b^2-a^2)/a^2 := by
  let Z := realNormalizer
  have hb := ha.trans_le hab
  have haZ : 0 < Z a := zero_lt_one.trans_le (realNormalizer_ge_one a ha)
  have hbZ : 0 < Z b := zero_lt_one.trans_le (realNormalizer_ge_one b hb)
  have hmono : Z a ≤ Z b := (summable_weight a ha).tsum_le_tsum
    (grid_weight_mono ha hab) (summable_weight b hb)
  have hdual : Z b⁻¹ ≤ Z a⁻¹ := (summable_weight b⁻¹ (inv_pos.mpr hb)).tsum_le_tsum
    (grid_weight_mono (inv_pos.mpr hb) (inv_anti₀ ha hab)) (summable_weight a⁻¹ (inv_pos.mpr ha))
  have hratio : Z b / Z a ≤ b / a := by
    apply (div_le_div_iff₀ haZ ha).mpr
    calc
      Z b * a = (b * Z b⁻¹) * a := by rw [show Z b = b * Z b⁻¹ from grid_theta_reciprocal b hb]
      _ ≤ (b * Z a⁻¹) * a := by gcongr
      _ = b * Z a := by rw [show Z a = a * Z a⁻¹ from grid_theta_reciprocal a ha]; ring
  let p := fun z => weight a z / Z a
  let t := fun z => weight b z / Z b
  let L := Z b / Z a
  have hL : 1 ≤ L := (one_le_div haZ).mpr hmono
  have hsump : Summable p := (summable_weight a ha).div_const _
  have hsumt : Summable t := (summable_weight b hb).div_const _
  have hmassp : ∑' z, p z = 1 := by rw [show (∑' z, p z) = Z a / Z a from tsum_div_const, div_self haZ.ne']
  have hmasst : ∑' z, t z = 1 := by rw [show (∑' z, t z) = Z b / Z b from tsum_div_const, div_self hbZ.ne']
  have hdom (z : ℤ) : p z ≤ L * t z := by
    calc
      p z ≤ weight b z / Z a := div_le_div_of_nonneg_right (grid_weight_mono ha hab z) haZ.le
      _ = L * t z := by dsimp [L,t]; field_simp
  have hpt (z : ℤ) : |p z - t z| ≤ (L-1) * t z + (L*t z-p z) := by
    have hpos : 0 ≤ t z := div_nonneg (weight_pos _ _).le hbZ.le
    exact abs_le.mpr ⟨by nlinarith [mul_nonneg (sub_nonneg.mpr hL) hpos], by linarith [hdom z]⟩
  have hadd := (hsumt.mul_left (L-1)).add ((hsumt.mul_left L).sub hsump)
  have hsum := (hsump.sub hsumt).norm.tsum_le_tsum (fun z => by simpa only [Real.norm_eq_abs] using hpt z) hadd
  simp only [Real.norm_eq_abs] at hsum
  rw [(hsumt.mul_left (L-1)).tsum_add ((hsumt.mul_left L).sub hsump),
    (hsumt.mul_left L).tsum_sub hsump, tsum_mul_left, tsum_mul_left, hmassp, hmasst] at hsum
  calc
    _ ≤ L-1 := by change (∑' z, |p z-t z|)/2 ≤ _; linarith
    _ ≤ b/a-1 := sub_le_sub_right hratio 1
    _ ≤ _ := by
      rw [div_sub_one ha.ne']
      rw [div_le_div_iff₀ ha (sq_pos_of_pos ha)]
      nlinarith [mul_nonneg (mul_nonneg ha.le (sub_nonneg.mpr hab)) hb.le]

theorem residual_variance_grid_gaussian_tv
    (s q M : ℕ) (hs : 2 ≤ s) (hq : 2 ≤ q) (hM : 0 < M)
    (E : ℝ) (hE : 0 ≤ E) (hcap : E ≤ (s : ℝ)^2 / 2) :
    ∃ i : Fin (M + 1), ∀ j : ℕ,
      let den : ℚ := (q : ℚ)^(2*j)
      let v : ℚ := (s : ℚ)^2 - ((s : ℚ)^2/2) * (i.val : ℚ) / M / den
      let total := E / (den : ℝ) + (v : ℝ)
      let mass := fun (width : ℝ) (z : ℤ) => AFT.GaussianSource.weight width z /
        AFT.GaussianSource.realNormalizer width
      (s : ℚ)^2/2 ≤ v ∧ v ≤ (s : ℚ)^2 ∧
      0 ≤ (s : ℝ)^2 - total ∧
      (s : ℝ)^2 - total ≤ (s : ℝ)^2 / (2 * M * (den : ℝ)) ∧
      (∑' z : ℤ, |mass (Real.sqrt total) z - mass (s : ℝ) z|)/2 ≤
        1 / ((M : ℝ) * (den : ℝ)) := by
  let H := (s:ℝ)^2/2
  have hsR : 0 < (s:ℝ) := by exact_mod_cast (show 0<s by omega)
  have hH : 0 < H := by dsimp [H]; positivity
  have hm : 0 < (M:ℝ) := by exact_mod_cast hM
  let a := E * M / H
  have ha : 0 ≤ a := div_nonneg (mul_nonneg hE hm.le) hH.le
  have haM : a ≤ M := by
    apply (div_le_iff₀ hH).mpr
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hcap hm.le
  let i : Fin (M+1) := ⟨⌈a⌉₊, Nat.lt_succ_iff.mpr ((Nat.ceil_le).mpr haM)⟩
  have hi₁ : a ≤ (i.val:ℝ) := Nat.le_ceil _
  have hi₂ : (i.val:ℝ) < a+1 := Nat.ceil_lt_add_one ha
  let g := H * i.val / M
  have hEg : E ≤ g := by
    apply (le_div_iff₀ hm).mpr
    have := (div_le_iff₀ hH).mp hi₁
    linarith only [this]
  have hgap : g - E ≤ H/M := by
    apply (le_div_iff₀ hm).mpr
    have haux := mul_lt_mul_of_pos_right hi₂ hH
    dsimp only [a] at haux
    rw [add_mul,div_mul_cancel₀ _ hH.ne',one_mul] at haux
    dsimp only [g]
    rw [sub_mul,div_mul_cancel₀ _ hm.ne']
    linarith only [haux]
  have hiM : (i.val:ℝ) ≤ M := by exact_mod_cast (show i.val ≤ M by omega)
  have hgpos : 0 ≤ g := by dsimp [g]; positivity
  have hgcap : g ≤ H := by
    apply (div_le_iff₀ hm).mpr
    exact mul_le_mul_of_nonneg_left hiM hH.le
  refine ⟨i,fun j => ?_⟩
  dsimp only
  let d := (q:ℝ)^(2*j)
  have hqR : 1 ≤ (q:ℝ) := by exact_mod_cast (show 1≤q by omega)
  have hd : 1 ≤ d := one_le_pow₀ hqR
  have hdpos := zero_lt_one.trans_le hd
  let v := (s:ℝ)^2 - g/d
  let total := E/d + v
  have hsmall : g/d ≤ H := (div_le_self hgpos hd).trans hgcap
  have hvlo : H ≤ v := by dsimp only [v]; dsimp [H] at hsmall ⊢; linarith
  have hvhi : v ≤ (s:ℝ)^2 := sub_le_self _ (div_nonneg hgpos hdpos.le)
  have htotal : H ≤ total := hvlo.trans (le_add_of_nonneg_left (div_nonneg hE hdpos.le))
  have htotalpos := hH.trans_le htotal
  have hdiff : (s:ℝ)^2-total = (g-E)/d := by dsimp only [total,v]; ring
  have hdiffpos : 0 ≤ (s:ℝ)^2-total := by rw [hdiff]; positivity
  have hdiffle : (s:ℝ)^2-total ≤ H/(M*d) := by
    rw [hdiff,← div_div]; exact div_le_div_of_nonneg_right hgap hdpos.le
  have hroot := Real.sq_sqrt htotalpos.le
  have hroots : Real.sqrt total ≤ s := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hsR.le).mp
    linarith only [hroot,hdiffpos]
  have htv := grid_tv_bound (Real.sqrt_pos.mpr htotalpos) hroots
  rw [hroot] at htv
  have hrel : ((s:ℝ)^2-total)/total ≤ 1/((M:ℝ)*d) := by
    apply (div_le_iff₀ htotalpos).mpr
    calc
      _ ≤ H/((M:ℝ)*d) := hdiffle
      _ ≤ total/((M:ℝ)*d) := div_le_div_of_nonneg_right htotal (mul_pos hm hdpos).le
      _ = _ := by ring
  have hc : (((s:ℚ)^2-((s:ℚ)^2/2)*(i.val:ℚ)/M/(q:ℚ)^(2*j):ℚ):ℝ) = v := by
    push_cast
    rfl
  have hcden : (((q:ℚ)^(2*j):ℚ):ℝ) = d := by push_cast; rfl
  rw [hcden,hc]
  constructor
  · apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact hvlo
  constructor
  · apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact hvhi
  refine ⟨hdiffpos,?_,htv.trans hrel⟩
  change (s:ℝ)^2-total ≤ _
  calc
    _ ≤ H/((M:ℝ)*d) := hdiffle
    _ = _ := by dsimp [H]; ring

end InfoLossLAR.WorstCase.RegevSearch

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace InfoLossLAR.WorstCase.GaussianProjection.VarianceGrid

open AFT GaussianSource GaussianRandomizedRounding RegevLWE.GaussConv

noncomputable section

theorem native_projected_at_width {dimension : ℕ}
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (q : ℕ) [NeZero q] (direction : EuclideanSpace ℝ (Fin dimension))
    (sigma : ℕ) (hsigma : 2 ≤ sigma) (squared : ℚ) (delta : ℝ) {latticeWidth error : ℝ}
    (hlattice : 0<latticeWidth) (herror : 0<error) (herrorOne : error<1)
    (hsmoothing : smoothingParam lattice error ≤ latticeWidth/Real.sqrt 2)
    (henergy : latticeWidth^2*‖direction‖^2 ≤ (sigma : ℝ)^2/2)
    (hsmall : 2*error+3*thetaError ((sigma : ℝ)/Real.sqrt 2) ≤ 1)
    (hpointLower : (sigma : ℝ)^2/2 ≤ (squared:ℝ)) (hpointUpper : (squared:ℝ) ≤ (sigma:ℝ)^2)
    (hgrid : (∑' z : ℤ, |integerMass (Real.sqrt (latticeWidth^2*‖direction‖^2+(squared:ℝ))) z -
      integerMass (sigma:ℝ) z|)/2 ≤ delta)
    (cutoff bits : ℕ) :
    let sourceSmoothing := hsmoothing.trans (div_le_self hlattice.le (by apply Real.le_sqrt_of_sq_le;norm_num : (1 : ℝ) ≤ Real.sqrt 2))
    ∀ (shift : EuclideanSpace ℝ (Fin dimension)) (center : lattice → ℚ),
      (∀ value : lattice,(center value : ℝ)=inner ℝ direction ((value : EuclideanSpace ℝ (Fin dimension))+shift)) →
      let source := cosetPMF lattice shift hlattice herror herrorOne sourceSmoothing
      (∑ output : ZMod q, |(sampleLaw source q squared center cutoff bits).weight output-
        (finiteLaw ((integerGaussian (sigma : ℝ) (by exact_mod_cast (show 0<sigma by omega))).map
          (fun value : ℤ => (value : ZMod q)))).weight output|)/2 ≤
        1/(2 : ℝ)^(bits+1)+intervalTail ((sigma : ℝ)/Real.sqrt 2) sigma cutoff+
          4*error+16*Real.exp (-Real.pi*(sigma : ℝ)^2/2)+delta := by
  have hs : (2 : ℝ) ≤ sigma := by exact_mod_cast hsigma
  have hspos : (0 : ℝ)<sigma := by linarith
  have hroot : 0<Real.sqrt (2 : ℝ) := by positivity
  have hrootOne : (1 : ℝ) ≤ Real.sqrt 2 := by apply Real.le_sqrt_of_sq_le;norm_num
  have hrootTwo : Real.sqrt (2 : ℝ) ≤ 2 := by apply Real.sqrt_le_iff.mpr;norm_num
  let lower : ℝ := (sigma : ℝ)/Real.sqrt 2
  have hloPos : 0<lower := div_pos hspos hroot
  have hloOne : 1 ≤ lower := (le_div_iff₀ hroot).mpr (by linarith)
  have hloSq : lower^2=(sigma : ℝ)^2/2 := by
    dsimp only [lower]
    rw [div_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsourceSmoothing := hsmoothing.trans (div_le_self hlattice.le hrootOne)
  let energy := latticeWidth^2*‖direction‖^2
  have henergyZero : 0 ≤ energy := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  dsimp only
  intro shift center hcenter
  let source := cosetPMF lattice shift hlattice herror herrorOne hsourceSmoothing
  let width := Real.sqrt (squared : ℝ)
  let totalWidth := Real.sqrt (energy+(squared : ℝ))
  have hp : 1 ≤ squared := by
    apply (Rat.cast_le (K:=ℝ)).mp
    push_cast
    nlinarith [sq_nonneg ((sigma:ℝ)-2)]
  have hpReal : (1 : ℝ) ≤ squared := by exact_mod_cast hp
  have hwPos : 0<width := Real.sqrt_pos.mpr (zero_lt_one.trans_le hpReal)
  have hwSq : width^2=(squared : ℝ) := Real.sq_sqrt (zero_lt_one.trans_le hpReal).le
  have hwOne : 1 ≤ width := by
    apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) hwPos.le).mp
    rw [hwSq]
    simpa using hpReal
  have hloWidth : lower ≤ width := by
    apply (sq_le_sq₀ hloPos.le hwPos.le).mp
    rw [hloSq,hwSq]
    exact hpointLower
  have hwidthSigma : width ≤ sigma := by
    apply (sq_le_sq₀ hwPos.le hspos.le).mp
    rwa [hwSq]
  have heff := (projection_width_bounds latticeWidth width direction hlattice hwPos
    (by rw [hwSq];exact henergy.trans hpointLower)).2.2
  have hsEff := hsmoothing.trans heff
  have htheta := thetaError_antitone lower width hloPos hloWidth
  have hsmallWidth : 2*error+3*thetaError width ≤ 1 := by linarith
  have htotal : Real.sqrt (projectedSquaredWidth latticeWidth width direction)=totalWidth := by
    unfold projectedSquaredWidth
    rw [hwSq]
    congr 1
    dsimp [energy]
    ring
  have hnative := native_projected_totalVariation lattice q shift direction center squared hlattice hwOne hp hwSq herror herrorOne
    hsEff hsmallWidth hcenter cutoff bits
  dsimp only at hnative
  simp only [htotal] at hnative
  have htPos : 0<totalWidth := Real.sqrt_pos.mpr (by linarith only [henergyZero,hpReal])
  let intermediate := finiteLaw ((integerGaussian totalWidth htPos).map (fun value : ℤ => (value : ZMod q)))
  let target := finiteLaw ((integerGaussian (sigma : ℝ) hspos).map (fun value : ℤ => (value : ZMod q)))
  let actual := sampleLaw source q squared center cutoff bits
  change (∑ output : ZMod q, |actual.weight output-intermediate.weight output|)/2 ≤
    1/(2 : ℝ)^(bits+1)+tailEnvelope width cutoff+4*error+16*Real.exp (-Real.pi*width^2) at hnative
  have hmap := finiteLaw_map_l1_le (integerGaussian totalWidth htPos) (integerGaussian (sigma : ℝ) hspos)
    (fun value : ℤ => (value : ZMod q))
  simp_rw [←integerMass_eq_pmf] at hmap
  have htail := tailEnvelope_interval (cutoff : ℝ) hloOne hloWidth hwidthSigma
  have hexp : Real.exp (-Real.pi*width^2) ≤ Real.exp (-Real.pi*(sigma : ℝ)^2/2) := by
    have h := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hpointLower (neg_nonpos.mpr Real.pi_pos.le))
    rw [←hwSq] at h
    have he : -Real.pi*((sigma : ℝ)^2/2)= -Real.pi*(sigma : ℝ)^2/2 := by ring
    rwa [he] at h
  have htriangle := Finset.sum_le_sum (fun output (_ : output ∈ (Finset.univ : Finset (ZMod q))) =>
    abs_sub_le (actual.weight output) (intermediate.weight output) (target.weight output))
  rw [Finset.sum_add_distrib] at htriangle
  change (∑ output : ZMod q, |actual.weight output-target.weight output|)/2 ≤ _
  linarith

end

end InfoLossLAR.WorstCase.GaussianProjection.VarianceGrid

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

open AFT GaussianSource GaussianRandomizedRounding RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ}

def score (sigma : ℕ) (error : ℝ) (cutoff bits : ℕ) (delta : ℝ) :=
  1/(2:ℝ)^(bits+1)+VarianceGrid.intervalTail ((sigma:ℝ)/Real.sqrt 2) sigma cutoff+
  4*error+16*Real.exp (-Real.pi*(sigma:ℝ)^2/2)+delta

theorem native_lwe_at_width {Index : Type*} [Fintype Index] [DecidableEq Index]
    (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (basis : Module.Basis Index ℤ lattice) (nearest : dual lattice)
    (query : Space (dimension:=dimension)) (center : lattice → ℚ)
    (hcenter : ∀ value : lattice,(center value : ℝ)=inner ℝ query (value : Space (dimension:=dimension)))
    (sigma : ℕ) (hsigma : 2 ≤ sigma) (squaredWidth : ℚ) (delta : ℝ) {latticeWidth error : ℝ}
    (hlattice : 0<latticeWidth) (herror : 0<error) (herrorOne : error<1)
    (hsmoothing : smoothingParam lattice error ≤ latticeWidth/(Real.sqrt 2*(q : ℝ)))
    (henergy : latticeWidth^2*‖query-(nearest : Space (dimension:=dimension))‖^2 ≤ (sigma : ℝ)^2/2)
    (hsmall : 2*error+3*thetaError ((sigma : ℝ)/Real.sqrt 2) ≤ 1)
    (hpointLower : (sigma : ℝ)^2/2 ≤ (squaredWidth:ℝ)) (hpointUpper : (squaredWidth:ℝ) ≤ (sigma:ℝ)^2)
    (hgrid : (∑' z : ℤ, |integerMass (Real.sqrt (latticeWidth^2*‖query-(nearest : Space (dimension:=dimension))‖^2+(squaredWidth:ℝ))) z -
      integerMass (sigma:ℝ) z|)/2 ≤ delta)
    (cutoff bits : ℕ) :
    let sourceSmoothing := (source_and_modulus_smoothing q lattice hlattice herror hsmoothing).1
    let source := cosetPMF lattice 0 hlattice herror herrorOne sourceSmoothing
    let noise := finiteLaw ((integerGaussian (sigma : ℝ) (by exact_mod_cast (show 0<sigma by omega))).map
      (fun value : ℤ => (value : ZMod q)))
    (∑ output,|(nativeLWELaw q lattice basis source squaredWidth center cutoff bits).weight output-
        (idealLWELaw q (secretCoordinates q lattice basis nearest) noise).weight output|)/2 ≤
          error/(1-error)+score sigma error cutoff bits delta := by
  have hrootOne : (1 : ℝ) ≤ Real.sqrt 2 := by apply Real.le_sqrt_of_sq_le;norm_num
  obtain ⟨hsource,hmodulus⟩ := source_and_modulus_smoothing q lattice hlattice herror hsmoothing
  have hmodulusSource := hmodulus.trans (div_le_self hlattice.le hrootOne)
  let source := cosetPMF lattice 0 hlattice herror herrorOne hsource
  let noise := finiteLaw ((integerGaussian (sigma : ℝ) (by exact_mod_cast (show 0<sigma by omega))).map
    (fun value : ℤ => (value : ZMod q)))
  let marginal := coefficientLaw q lattice basis hlattice herror herrorOne hsource
  let embedding := fun (color : Index → ZMod q) (output : ZMod q) =>
    (color,(∑ index,secretCoordinates q lattice basis nearest index*color index)+output)
  let ideal := fun color => noise.map (embedding color)
  have hindex := VarianceGrid.native_projected_at_width (modulusLattice q lattice) q
    (query-(nearest : Space (dimension:=dimension))) sigma hsigma squaredWidth delta hlattice herror herrorOne
    hmodulus henergy hsmall hpointLower hpointUpper hgrid cutoff bits
  have hwidth : 1 ≤ squaredWidth := by
    apply (Rat.cast_le (K:=ℝ)).mp
    have hs : (2:ℝ) ≤ sigma := by exact_mod_cast hsigma
    push_cast
    nlinarith [sq_nonneg ((sigma:ℝ)-2)]
  let conditional := fun color => VarianceGrid.sampleLaw
    (cosetPMF (modulusLattice q lattice) (lift q lattice basis color : Space (dimension:=dimension))
      hlattice herror herrorOne hmodulusSource) q squaredWidth
    (fun value => errorCenter lattice nearest center (sample q lattice (lift q lattice basis color) value)) cutoff bits
  let actual := fun color => (conditional color).map (embedding color)
  have hconditional (color : Index → ZMod q) :
      (∑ output,|(conditional color).weight output-noise.weight output|)/2 ≤ score sigma error cutoff bits delta := by
    apply hindex (lift q lattice basis color : Space (dimension:=dimension))
      (fun value => errorCenter lattice nearest center (sample q lattice (lift q lattice basis color) value))
    intro value
    exact errorCenter_spec lattice nearest query center hcenter (sample q lattice (lift q lattice basis color) value)
  have hmapped (color : Index → ZMod q) :
      (∑ output,|(actual color).weight output-(ideal color).weight output|) ≤ 2*score sigma error cutoff bits delta := by
    have hmap := FiniteDist.l1_map_le (conditional color) noise (embedding color)
    exact hmap.trans (by linarith [hconditional color])
  have hrounding := l1_mix_le_uniform marginal actual ideal (2*score sigma error cutoff bits delta) hmapped
  have hprior := FiniteDist.signed_kernel_l1_contraction
    (fun color => marginal.weight color-(FiniteDist.uniform (Index → ZMod q)).weight color) ideal
  have hchange : (∑ output,|(marginal.mix ideal).weight output-
      ((FiniteDist.uniform (Index → ZMod q)).mix ideal).weight output|) ≤
      ∑ color,|marginal.weight color-(FiniteDist.uniform (Index → ZMod q)).weight color| := by
    simpa only [FiniteDist.mix_weight,←Finset.sum_sub_distrib,←sub_mul] using hprior
  have huniform := coefficientLaw_uniform q lattice basis hlattice herror herrorOne hsource hmodulusSource
  have hdisintegrate : nativeLWELaw q lattice basis source squaredWidth center cutoff bits=marginal.mix actual := by
    unfold nativeLWELaw
    rw [countableMix_coset_partition q lattice basis hlattice herror herrorOne hsource hmodulusSource]
    apply congrArg marginal.mix
    funext color
    exact native_coset_joint q lattice basis nearest _ center squaredWidth hwidth cutoff bits color
  change (∑ output,|(nativeLWELaw q lattice basis source squaredWidth center cutoff bits).weight output-
    ((FiniteDist.uniform (Index → ZMod q)).mix ideal).weight output|)/2 ≤ _
  rw [hdisintegrate]
  have htriangle := Finset.sum_le_sum (fun output (_ : output ∈ (Finset.univ : Finset ((Index → ZMod q) × ZMod q))) =>
    abs_sub_le ((marginal.mix actual).weight output) ((marginal.mix ideal).weight output)
      (((FiniteDist.uniform (Index → ZMod q)).mix ideal).weight output))
  rw [Finset.sum_add_distrib] at htriangle
  linarith

end

end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis.Native

open AFT GaussianSource GaussianProjection GaussianRandomizedRounding GaussianPoissonSeries

open RegevLWE.GaussConv BDDNative RationalGramSchmidt

open scoped BigOperators

noncomputable section

/-- A single publicly enumerable index controls every correctly updated digit's actual native
table, at arbitrary table length and numerical precision. The rational query at each
stage is the native residual of the true earlier digits. -/
theorem common_residual_native_tables {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (q sigma M : ℕ) [NeZero q] (hq : 2 ≤ q) (hs : 2 ≤ sigma) (hM : 0 < M)
    (x : Fin n → ℚ) (u : dual (inputLattice B hB)) {R error : ℝ}
    (hR : 0 < R) (he : 0 < error) (he1 : error < 1)
    (hsmooth : smoothingParam (inputLattice B hB) error ≤ R/(Real.sqrt 2 * (q:ℝ)))
    (hE : R^2*‖rationalPoint x-(u:Space (dimension:=n))‖^2 ≤ (sigma:ℝ)^2/2)
    (hsmall : 2*error+3*thetaError ((sigma:ℝ)/Real.sqrt 2) ≤ 1) :
    let source := cosetPMF (inputLattice B hB) 0 hR he he1
      (CosetGeometry.source_and_modulus_smoothing q (inputLattice B hB) hR he hsmooth).1
    let noise := finiteLaw ((integerGaussian (sigma:ℝ) (by exact_mod_cast (show 0<sigma by omega))).map
      (fun z : ℤ => (z:ZMod q)))
    ∃ i : Fin (M+1), ∀ j count cutoff bits : ℕ,
      let den : ℚ := (q:ℚ)^(2*j)
      let v : ℚ := (sigma:ℚ)^2-((sigma:ℚ)^2/2)*(i.val:ℚ)/M/den
      let y := terminalQuery B q x (fun k : Fin j => goodDigits B hB q u k.val)
      let a := nearestSequence B hB q u j
      let ideal := FiniteDist.independent (fun _ : Fin count => CosetGeometry.idealLWELaw q
        (CosetGeometry.secretCoordinates q (inputLattice B hB) (integerBasis B hB) a) noise)
      (∑ t, |(sourceTableLaw B hB source y q count v cutoff bits).weight t-ideal.weight t|)/2 ≤
        count*(error/(1-error)+CosetGeometry.score sigma error cutoff bits (1/((M:ℝ)*(den:ℝ)))) := by
  let E := R^2*‖rationalPoint x-(u:Space (dimension:=n))‖^2
  obtain ⟨i,hi⟩ := RegevSearch.residual_variance_grid_gaussian_tv sigma q M hs hq hM E (by positivity) hE
  dsimp only
  refine ⟨i,fun j count cutoff bits => ?_⟩
  let y := terminalQuery B q x (fun k : Fin j => goodDigits B hB q u k.val)
  let a := nearestSequence B hB q u j
  let d : ℚ := (q:ℚ)^(2*j)
  let v : ℚ := (sigma:ℚ)^2-((sigma:ℚ)^2/2)*(i.val:ℚ)/M/d
  have hden : (d:ℝ) = (q:ℝ)^(2*j) := by simp [d]
  have hd : 1 ≤ (d:ℝ) := hden ▸ one_le_pow₀ (by exact_mod_cast (show 1≤q by omega))
  have hj := hi j
  dsimp only at hj
  obtain ⟨hlo,hhi,_,_,htv⟩ := hj
  change (sigma:ℚ)^2/2 ≤ v at hlo
  change v ≤ (sigma:ℚ)^2 at hhi
  have hvlo : (sigma:ℝ)^2/2 ≤ (v:ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr hlo
  have hvhi : (v:ℝ) ≤ (sigma:ℝ)^2 := by
    simpa only [Rat.cast_pow,Rat.cast_natCast] using (Rat.cast_le (K:=ℝ)).mpr hhi
  have hen : R^2*‖rationalPoint y-(a:Space (dimension:=n))‖^2 = E/(d:ℝ) := by
    have hn := terminalQuery_error_norm (steps:=j) B hB q x u
    change ‖rationalPoint y-(a:Space (dimension:=n))‖ =
      ‖rationalPoint x-(u:Space (dimension:=n))‖/(q:ℝ)^j at hn
    rw [hn,hden, Nat.mul_comm 2 j,pow_mul,div_pow]
    dsimp only [E]; ring
  have hen' : R^2*‖rationalPoint y-(a:Space (dimension:=n))‖^2 ≤ (sigma:ℝ)^2/2 := by
    rw [hen]
    exact (div_le_self (by dsimp [E]; positivity) hd).trans hE
  have hgrid : (∑' z : ℤ, |integerMass (Real.sqrt (R^2*‖rationalPoint y-(a:Space (dimension:=n))‖^2+(v:ℝ))) z-
      integerMass (sigma:ℝ) z|)/2 ≤ 1/((M:ℝ)*(d:ℝ)) := by
    rw [hen]; exact htv
  have hrow := CosetGeometry.native_lwe_at_width q (inputLattice B hB) (integerBasis B hB) a
    (rationalPoint y) (exactCenter B hB y) (exactCenter_spec B hB y)
    sigma hs v _ hR he he1 hsmooth hen' hsmall hvlo hvhi hgrid cutoff bits
  have hv : 1 ≤ v := by
    have hss : (2:ℚ) ≤ sigma := by exact_mod_cast hs
    change (sigma:ℚ)^2/2 ≤ v at hlo
    nlinarith [sq_nonneg ((sigma:ℚ)-2)]
  apply countableProductChannel_l1
  intro _
  change (∑ t, |(sourceLaw B hB _ y q v cutoff bits).weight t - _|)/2 ≤ _
  rw [sourceLaw_eq B hB _ y q v hv cutoff bits]
  exact hrow

/-- Public block regrouping transfers the simultaneous estimate to exactly the observed LWE laws used by search. -/
theorem common_residual_native_blocks {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (q sigma M : ℕ) [NeZero q] (hq : 2 ≤ q) (hs : 2 ≤ sigma) (hM : 0 < M)
    (x : Fin n → ℚ) (u : dual (inputLattice B hB)) {R error : ℝ}
    (hR : 0 < R) (he : 0 < error) (he1 : error < 1)
    (hsmooth : smoothingParam (inputLattice B hB) error ≤ R/(Real.sqrt 2 * (q:ℝ)))
    (hE : R^2*‖rationalPoint x-(u:Space (dimension:=n))‖^2 ≤ (sigma:ℝ)^2/2)
    (hsmall : 2*error+3*thetaError ((sigma:ℝ)/Real.sqrt 2) ≤ 1) :
    let source := cosetPMF (inputLattice B hB) 0 hR he he1
      (CosetGeometry.source_and_modulus_smoothing q (inputLattice B hB) hR he hsmooth).1
    ∃ i : Fin (M+1), ∀ j blocks rows cutoff bits : ℕ,
      let den : ℚ := (q:ℚ)^(2*j)
      let v : ℚ := (sigma:ℚ)^2-((sigma:ℚ)^2/2)*(i.val:ℚ)/M/den
      let y := terminalQuery B q x (fun k : Fin j => goodDigits B hB q u k.val)
      let a := nearestSequence B hB q u j
      let actual := (sourceTableLaw B hB source y q (blocks*rows) v cutoff bits).map NativeLWETableLoader.groupTable
      let ideal := larObservedRealTableLaw q n rows blocks
        (residueGaussian rows q (sigma:ℝ) (by exact_mod_cast (show 0<sigma by omega)))
        (CosetGeometry.secretCoordinates q (inputLattice B hB) (integerBasis B hB) a)
      (∑ t, |actual.weight t-ideal.weight t|)/2 ≤
        ((blocks*rows:ℕ):ℝ)*(error/(1-error)+CosetGeometry.score sigma error cutoff bits (1/((M:ℝ)*(den:ℝ)))) := by
  obtain ⟨i,hi⟩ := common_residual_native_tables B hB q sigma M hq hs hM x u hR he he1 hsmooth hE hsmall
  dsimp only
  refine ⟨i,fun j blocks rows cutoff bits => ?_⟩
  have hj := hi j (blocks*rows) cutoff bits
  dsimp only at hj
  let den : ℚ := (q:ℚ)^(2*j)
  let v : ℚ := (sigma:ℚ)^2-((sigma:ℚ)^2/2)*(i.val:ℚ)/M/den
  let y := terminalQuery B q x (fun k : Fin j => goodDigits B hB q u k.val)
  let a := nearestSequence B hB q u j
  let μ := sourceTableLaw B hB (cosetPMF (inputLattice B hB) 0 hR he he1
    (CosetGeometry.source_and_modulus_smoothing q (inputLattice B hB) hR he hsmooth).1) y q (blocks*rows) v cutoff bits
  let s := CosetGeometry.secretCoordinates q (inputLattice B hB) (integerBasis B hB) a
  have hspos : 0 < (sigma:ℝ) := by exact_mod_cast (show 0<sigma by omega)
  let ν := FiniteDist.independent (fun _ : Fin (blocks*rows) => CosetGeometry.idealLWELaw q s (scalarLaw q sigma hspos))
  rw [modularInteger_eq_scalarLaw] at hj
  rw [← NativeLWETableLoader.ideal_product_group]
  have hm := FiniteDist.l1_map_le μ ν (@NativeLWETableLoader.groupTable q n blocks rows)
  exact (div_le_div_of_nonneg_right hm (by norm_num : (0:ℝ) ≤ 2)).trans hj

end

end InfoLossLAR.WorstCase.IntegerBasis.Native

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.IntegerBasis.Native

open AFT GaussianSource GaussianProjection GaussianRandomizedRounding GaussianPoissonSeries

open RegevLWE.GaussConv BDDNative RationalGramSchmidt GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

private theorem residual_tail_bound (sigma m : ℕ) (hsigma : 2 ≤ sigma) (hm : 0 < m) :
    VarianceGrid.intervalTail ((sigma : ℝ)/Real.sqrt 2) sigma ((sigma*m : ℕ) : ℝ) ≤
      6/(m : ℝ) := by
  have hs : (2 : ℝ) ≤ sigma := by exact_mod_cast hsigma
  have hp : (0 : ℝ) < sigma := by linarith
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hr : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hrTwo : Real.sqrt (2 : ℝ) ≤ 2 := by apply Real.sqrt_le_iff.mpr; norm_num
  have hlo : 1 ≤ (sigma : ℝ)/Real.sqrt 2 := (le_div_iff₀ hr).mpr (by linarith)
  have h := intervalTail_le_six (upper:=(sigma : ℝ)) (radius:=((sigma*m : ℕ) : ℝ)) hlo
  have heq : -Real.pi*((sigma*m : ℕ) : ℝ)^2/(2*(sigma : ℝ)^2)= -Real.pi*(m : ℝ)^2/2 := by
    push_cast
    field_simp
  rw [heq] at h
  have hquad : (m : ℝ) ≤ Real.pi*(m : ℝ)^2/2 := by
    nlinarith [Real.pi_gt_three, sq_nonneg ((m : ℝ)-1)]
  have hexp : Real.exp (-Real.pi*(m : ℝ)^2/2) ≤ 1/(2 : ℝ)^m := by
    calc
      _ ≤ Real.exp (-(m : ℝ)) := Real.exp_le_exp.mpr (by linarith)
      _ = 1/Real.exp (m : ℝ) := by rw [Real.exp_neg, one_div]
      _ ≤ 1/(2 : ℝ)^m := by
        apply one_div_le_one_div_of_le (by positivity)
        have heq : Real.exp (m : ℝ) = (Real.exp 1)^m := by
          rw [← Real.exp_nat_mul]
          simp
        rw [heq]
        exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le _
  have hpow : (m : ℝ) ≤ (2 : ℝ)^m := by
    have hh : m ≤ 2^m := (Nat.le_add_right m 1).trans (Nat.lt_two_pow_self (n:=m))
    exact_mod_cast hh
  have hrecip : 1/(2 : ℝ)^m ≤ 1/(m : ℝ) :=
    one_div_le_one_div_of_le (by positivity) hpow
  calc
    _ ≤ 6 * Real.exp (-Real.pi*(m : ℝ)^2/2) := h
    _ ≤ 6 * (1/(2 : ℝ)^m) := mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ ≤ 6 * (1/(m : ℝ)) := mul_le_mul_of_nonneg_left hrecip (by norm_num)
    _ = 6/(m : ℝ) := by ring

/-- One dimension-dependent public list of rational schedules works at every digit, with a constant additive whole-table budget. -/
theorem common_residual_constant_blocks {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (q sigma blocks rows : ℕ) [NeZero q] (hq : 2 ≤ q) (hs : 2 ≤ sigma)
    (x : Fin n → ℚ) (u : dual (inputLattice B hB)) {R error : ℝ}
    (hR : 0 < R) (he : 0 < error) (he1 : error < 1)
    (hsmooth : smoothingParam (inputLattice B hB) error ≤ R/(Real.sqrt 2 * (q:ℝ)))
    (hE : R^2*‖rationalPoint x-(u:Space (dimension:=n))‖^2 ≤ (sigma:ℝ)^2/2)
    (hsmall : 2*error+3*thetaError ((sigma:ℝ)/Real.sqrt 2) ≤ 1) :
    let m := 768*(blocks*rows+1)
    let source := cosetPMF (inputLattice B hB) 0 hR he he1
      (CosetGeometry.source_and_modulus_smoothing q (inputLattice B hB) hR he hsmooth).1
    ∃ i : Fin (m+1), ∀ j : ℕ,
      let den : ℚ := (q:ℚ)^(2*j)
      let v : ℚ := (sigma:ℚ)^2-((sigma:ℚ)^2/2)*(i.val:ℚ)/m/den
      let y := terminalQuery B q x (fun k : Fin j => goodDigits B hB q u k.val)
      let a := nearestSequence B hB q u j
      let actual := (sourceTableLaw B hB source y q (blocks*rows) v (sigma*m) m).map NativeLWETableLoader.groupTable
      let ideal := larObservedRealTableLaw q n rows blocks
        (residueGaussian rows q (sigma:ℝ) (by exact_mod_cast (show 0<sigma by omega)))
        (CosetGeometry.secretCoordinates q (inputLattice B hB) (integerBasis B hB) a)
      (∑ t, |actual.weight t-ideal.weight t|)/2 ≤
        ((blocks*rows:ℕ):ℝ) * (error/(1-error)+4*error+16*Real.exp (-Real.pi*(sigma:ℝ)^2/2)) + 1/96 := by
  let c := blocks*rows
  let m := 768*(c+1)
  have hm : 0 < m := by dsimp [m]; omega
  have hmr : 0 < (m:ℝ) := by exact_mod_cast hm
  have hspos : 0 < (sigma:ℝ) := by exact_mod_cast (show 0<sigma by omega)
  obtain ⟨i,hi⟩ := common_residual_native_blocks B hB q sigma m hq hs hm x u hR he he1 hsmooth hE hsmall
  dsimp only
  refine ⟨i,fun j => ?_⟩
  have h := hi j blocks rows (sigma*m) m
  apply h.trans
  have hpow : (m:ℝ) ≤ (2:ℝ)^(m+1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n:=m)).le.trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ m))
  have hd : (1:ℝ) ≤ (((q:ℚ)^(2*j):ℚ):ℝ) := by
    push_cast
    exact one_le_pow₀ (by exact_mod_cast (show 1≤q by omega))
  have hgrid : 1/((m:ℝ)*(((q:ℚ)^(2*j):ℚ):ℝ)) ≤ 1/(m:ℝ) :=
    one_div_le_one_div_of_le hmr (le_mul_of_one_le_right hmr.le hd)
  have hbits := one_div_le_one_div_of_le hmr hpow
  have htail := residual_tail_bound sigma m hs hm
  have hr : (c:ℝ)* (8/(m:ℝ)) ≤ 1/96 := by
    rw [mul_div_assoc']
    apply (div_le_iff₀ hmr).mpr
    dsimp [m]; push_cast; linarith
  unfold score
  change (c:ℝ)*_ ≤ (c:ℝ)*_ + 1/96
  have hcomb : 1/(2:ℝ)^(m+1) + VarianceGrid.intervalTail ((sigma:ℝ)/Real.sqrt 2) sigma ((sigma*m:ℕ):ℝ) +
      1/((m:ℝ)*(((q:ℚ)^(2*j):ℚ):ℝ)) ≤ 8/(m:ℝ) := by
    calc
      _ ≤ 1/(m:ℝ)+6/(m:ℝ)+1/(m:ℝ) := add_le_add (add_le_add hbits htail) hgrid
      _ = _ := by ring
  linarith only [mul_le_mul_of_nonneg_left hcomb (Nat.cast_nonneg c),hr]

end

end InfoLossLAR.WorstCase.IntegerBasis.Native

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.IntegerBasis.Native

open scoped BigOperators

noncomputable section

private theorem poly_cap (p : Polynomial ℕ) {n : ℕ} (h1 : 1 ≤ n) (hp : p.eval 1 ≤ n) :
    p.eval n ≤ n^(p.natDegree+1) := by
  calc
    p.eval n = ∑ i ∈ Finset.range (p.natDegree+1), p.coeff i * n^i := p.eval_eq_sum_range n
    _ ≤ ∑ i ∈ Finset.range (p.natDegree+1), p.coeff i * n^p.natDegree :=
      Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right h1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    _ = p.eval 1 * n^p.natDegree := by
      rw [← Finset.sum_mul]; congr 1; simpa using (p.eval_eq_sum_range 1).symm
    _ ≤ n * n^p.natDegree := Nat.mul_le_mul_right _ hp
    _ = _ := by rw [pow_succ,mul_comm]

/-- At the fixed-family smoothing error, every polynomially bounded scalar row
count eventually makes the intrinsic whole-table variation at most 1/32. -/
theorem polynomial_rows_intrinsic_budget (p : Polynomial ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ c ≤ p.eval n,
      let ε := 1/(2:ℝ)^(Nat.size (n+2))^2
      (c:ℝ)*(ε/(1-ε)+4*ε+16*Real.exp (-Real.pi*((n:ℝ)+2)^2/2)) ≤ 1/32 := by
  let a := p.natDegree+1
  refine ⟨max 704 (max (p.eval 1) (2^(a+1))),?_⟩
  intro n hn c hc
  have hn704 : 704 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := by omega
  have hn1' : 1 ≤ n+2 := by omega
  have hpa : c ≤ n^a := hc.trans (poly_cap p hn1 ((le_max_left _ _).trans ((le_max_right _ _).trans hn)))
  let s := Nat.size (n+2)
  have h2 : 2^(a+1) ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hs : a+1 ≤ s := (Nat.lt_size.mpr (show 2^(a+1) ≤ n+2 by omega)).le
  have hss : s ≤ n+2 := Nat.size_le.mpr (Nat.lt_two_pow_self)
  have hpc : (n+2)^(a+1) ≤ 2^(s^2) := by
    calc
      _ ≤ (2^s)^(a+1) := Nat.pow_le_pow_left (Nat.lt_size_self _).le _
      _ = 2^(s*(a+1)) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by simpa [pow_two] using Nat.mul_le_mul_left s hs)
  have hcap : 704*c ≤ 2^(s^2) := by
    calc
      _ ≤ (n+2)*(n+2)^a := Nat.mul_le_mul (by omega) (hpa.trans (Nat.pow_le_pow_left (by omega) a))
      _ = (n+2)^(a+1) := by rw [pow_succ (n+2) a, mul_comm]
      _ ≤ _ := hpc
  let Z := (2:ℝ)^(s^2)
  have hZpos : 0 < Z := by dsimp [Z]; positivity
  have hZ : 2 ≤ Z := by
    have hz : 1 ≤ s^2 := Nat.one_le_pow _ _ (by omega)
    simpa [Z] using (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hz)
  let ε := 1/Z
  have hep : 0 < ε := one_div_pos.mpr hZpos
  have hehalf : ε ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hZ
  have hratio : ε/(1-ε) ≤ 2*ε := (div_le_iff₀ (by linarith)).mpr (by nlinarith [mul_nonneg hep.le (show 0 ≤ 1-2*ε by linarith)])
  have hpow : Z ≤ Real.exp (Real.pi*((n:ℝ)+2)^2/2) := by
    calc
      Z ≤ (Real.exp 1)^(s^2) := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le _
      _ = Real.exp ((s:ℝ)^2) := by rw [←Real.exp_nat_mul]; push_cast; rw [mul_one]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hsr : (s:ℝ) ≤ (n:ℝ)+2 := by exact_mod_cast hss
        have hsq := (sq_le_sq₀ (Nat.cast_nonneg s) (by positivity)).mpr hsr
        nlinarith [mul_nonneg (show 0 ≤ Real.pi-2 by linarith [Real.pi_gt_three]) (sq_nonneg ((n:ℝ)+2))]
  have hexp : Real.exp (-Real.pi*((n:ℝ)+2)^2/2) ≤ ε := by
    rw [show -Real.pi*((n:ℝ)+2)^2/2 = -(Real.pi*((n:ℝ)+2)^2/2) by ring, Real.exp_neg, ←one_div]
    exact one_div_le_one_div_of_le hZpos hpow
  have hprod : 704*(c:ℝ) ≤ Z := by dsimp only [Z]; exact_mod_cast hcap
  change (c:ℝ)*(ε/(1-ε)+4*ε+16*_ ) ≤ _
  calc
    _ ≤ (c:ℝ)*(22*ε) := mul_le_mul_of_nonneg_left (by linarith [hexp,hratio]) (Nat.cast_nonneg c)
    _ = (22*(c:ℝ))/Z := by dsimp only [ε];ring
    _ ≤ _ := (div_le_iff₀ hZpos).mpr (by linarith)

end

end InfoLossLAR.WorstCase.IntegerBasis.Native

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.IntegerBasis.Native

open AFT GaussianSource GaussianProjection GaussianRandomizedRounding GaussianPoissonSeries

open RegevLWE.GaussConv BDDNative RationalGramSchmidt GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

/-- For sufficiently large n, one public rational width schedule gives actual observed
LWE input tables within 1/24 of their exact fixed-secret law at every honest digit.
The polynomial bounds the total scalar rows, including every row of each observed block. -/
theorem common_good_observed_blocks (p : Polynomial ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ blocks rows : ℕ, blocks*rows ≤ p.eval n →
    ∀ (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (q : ℕ) [NeZero q], 2 ≤ q →
    ∀ (x : Fin n → ℚ) (u : dual (inputLattice B hB)) (R : ℝ) (hR : 0 < R),
    let error := 1/(2:ℝ)^((n+2).size)^2
    let sigma := n+2
    ∀ (he : 0 < error) (he1 : error < 1)
      (hsmooth : smoothingParam (inputLattice B hB) error ≤ R/(Real.sqrt 2 * (q:ℝ))),
    R^2*‖rationalPoint x-(u:Space (dimension:=n))‖^2 ≤ (sigma:ℝ)^2/2 →
    let m := 768*(blocks*rows+1)
    let source := cosetPMF (inputLattice B hB) 0 hR he he1
      (CosetGeometry.source_and_modulus_smoothing q (inputLattice B hB) hR he hsmooth).1
    ∃ i : Fin (m+1), ∀ j : ℕ,
      let den : ℚ := (q:ℚ)^(2*j)
      let v : ℚ := (sigma:ℚ)^2-((sigma:ℚ)^2/2)*(i.val:ℚ)/m/den
      let y := terminalQuery B q x (fun k : Fin j => goodDigits B hB q u k.val)
      let a := nearestSequence B hB q u j
      let actual := (sourceTableLaw B hB source y q (blocks*rows) v (sigma*m) m).map NativeLWETableLoader.groupTable
      let ideal := larObservedRealTableLaw q n rows blocks
        (residueGaussian rows q (sigma:ℝ) (by exact_mod_cast (show 0<sigma by omega)))
        (CosetGeometry.secretCoordinates q (inputLattice B hB) (integerBasis B hB) a)
      (∑ t, |actual.weight t-ideal.weight t|)/2 ≤
        1/24 := by
  obtain ⟨N,hN⟩ := polynomial_rows_intrinsic_budget p
  refine ⟨max N 2,?_⟩
  intro n hn blocks rows hc B hB q _ hq x u R hR
  simp only
  intro he he1 hsmooth hE
  let e := 1/(2:ℝ)^((n+2).size)^2
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have h3 : 3 ≤ Nat.size (n+2) := Nat.lt_size.mpr (by norm_num; omega)
  have he8 : e ≤ 1/8 := by
    apply one_div_le_one_div_of_le (by norm_num)
    calc
      (8:ℝ) = 2^3 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.mul_self_le_mul_self h3])
  have ht := sigma_theta_small (n+2) (by omega) he8
  obtain ⟨i,hi⟩ := common_residual_constant_blocks B hB q (n+2) blocks rows hq (by omega)
    x u hR he he1 hsmooth hE ht
  refine ⟨i,fun j => (hi j).trans ?_⟩
  have hb := hN n ((le_max_left _ _).trans hn) (blocks*rows) hc
  dsimp only at hb ⊢
  push_cast at hb ⊢
  linarith only [hb]

end

end InfoLossLAR.WorstCase.IntegerBasis.Native

end P2MDyadicModule86

/- Helper module Recovery. -/
section P2MDyadicModule87

set_option autoImplicit false

set_option maxHeartbeats 1200000

namespace InfoLossLAR.WorstCase.ShortProbe

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RationalGramSchmidt RationalInverse

open scoped BigOperators

noncomputable section

abbrev intRows {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℤ) :=
  List.ofFn fun i => List.ofFn (C i)

theorem lift_eq {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (z : Fin n → ℤ) (u : Fin n → ℚ)
    (h : ∀ j, ∑ i, (B i j:ℚ)*u i=z j) :
    BDDNative.lift (intRows B,List.ofFn z) = List.ofFn u := by
  rw [show intRows B = RationalInverse.Native.inputRows B from rfl,BDDNative.lift_ofFn _ hB]
  apply congrArg List.ofFn
  apply rational_pairings_unique B hB
  intro k
  have hsum (i : Fin n) : innerQ (dualVector B i) (inputVectors B k) = if k=i then 1 else 0 :=
    dualVector_pairing B hB i k
  change (∑ j,(∑ i, (z i : ℚ) • dualVector B i) j * inputVectors B k j) = _
  simp only [Finset.sum_apply,Pi.smul_apply, smul_eq_mul,Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  change (∑ i,(z i:ℚ) * innerQ (dualVector B i) (inputVectors B k)) = _
  simp_rw [hsum]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simpa only [innerQ,inputVectors,mul_comm] using (h k).symm

end

end InfoLossLAR.WorstCase.ShortProbe

end P2MDyadicModule87

/- Helper module TrialLaw. -/
section P2MDyadicModule88

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 900000

namespace InfoLossLAR.WorstCase.ShortProbe

open scoped BigOperators Classical

open GaussianProjection GaussianProjection.CosetGeometry IntegerBasis RegevLWE.GaussConv AFT

open NativeLWETableLoader GaussianPoissonSeries AFT.BinaryArithmetic

open Integration9_9.GaussianRegroupMachine QAlgorithms.Complexity

open RegevSketch

noncomputable section

theorem mix_expectation {X Y : Type*} [Fintype Y] (p : X → ℝ) (h0 : ∀ x,0≤p x)
    (hS : Summable p) (h1 : ∑' x,p x=1) (K : X → FiniteDist Y) (test : Y → ℝ) :
    (FiniteDist.countableMix p h0 hS h1 K).expectation test = ∑' x,p x*(K x).expectation test := by
  unfold FiniteDist.expectation FiniteDist.countableMix
  dsimp only
  simp_rw [←tsum_mul_right, Finset.mul_sum, ← mul_assoc]
  exact (Summable.tsum_finsetSum (fun y _ =>
    (FiniteDist.countableChannel_summable p hS K y).mul_right (test y))).symm

def observedWord {n blocks rows : ℕ} (sec : ℕ) (pp : Str)
    (B : Matrix (Fin n) (Fin n) ℤ) (values : Fin (blocks*rows) → Fin n → ℤ)
    (x : Fin n → ℚ) (q : ℕ) (v : ℚ) (cutoff bits : ℕ)
    (tape : Fin ((blocks*rows)*((bits+1)+(2*cutoff+1)+1)) → Fin 2) : Str :=
  observed ((unary sec,pp),((List.replicate blocks (),List.replicate rows ()),
      ((numericalContext B x q v cutoff bits,List.ofFn fun i => List.ofFn (values i)),
        List.ofFn fun j => digitBoolean (tape j))))

theorem actual_test {n blocks rows : ℕ} (sec : ℕ) (pp : Str)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (R : ℝ)
    (source : PMF (inputLattice B hB))
    (hm : ∀ z, coefficientMass B R z = (source ((integerBasis B hB).equivFun.symm z)).toReal)
    (x : Fin n → ℚ) (q : ℕ) [NeZero q] (v : ℚ) (hv : 1 ≤ v) (cutoff bits : ℕ) (test : Str → ℝ) :
    ((IntegerBasis.Native.sourceTableLaw B hB source x q (blocks*rows) v cutoff bits).map
       (groupTable (blocks:=blocks) (rows:=rows))).expectation
          (fun t => test (encInput sec pp (encTable t))) =
      ∑' values : Fin (blocks*rows) → Fin n → ℤ, (∏ j,coefficientMass B R (values j)) *
        (FiniteDist.uniform (Fin ((blocks*rows)*((bits+1)+(2*cutoff+1)+1)) → Fin 2)).expectation
          (fun tape => test (observedWord (blocks:=blocks) (rows:=rows) sec pp B values x q v cutoff bits tape)) := by
  rw [FiniteDist.expectation_map]
  unfold IntegerBasis.Native.sourceTableLaw countableProductChannel
  rw [mix_expectation]
  let e : (Fin (blocks*rows) → Fin n → ℤ) ≃ (Fin (blocks*rows) → inputLattice B hB) :=
    Equiv.piCongrRight fun _ => (integerBasis B hB).equivFun.symm.toEquiv
  rw [← e.tsum_eq]
  apply tsum_congr
  intro vals
  apply congrArg₂ (·*·)
  · exact Finset.prod_congr rfl fun j _ => (hm (vals j)).symm
  · rw [←actualPoolKernel_lattice]
    unfold actualPoolKernel
    rw [FiniteDist.expectation_map]
    apply congrArg (FiniteDist.uniform _).expectation
    funext tape
    simp only [Function.comp_apply,observedWord,observed_exact _ _ _ _ _ _ _ hv,
      decode_current_numerical]
    have he (j : Fin (blocks*rows)) :
        (integerBasis B hB).equivFun (e vals j) = vals j := by
      apply LinearEquiv.apply_symm_apply
    simp_rw [he]
    rfl

end

end InfoLossLAR.WorstCase.ShortProbe

end P2MDyadicModule88

/- Helper module TrialCore. -/
section P2MDyadicModule89

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

set_option maxRecDepth 20000

namespace InfoLossLAR.WorstCase.ShortProbe

open scoped BigOperators Classical

open QAlgorithms.Complexity Integration9_9.LARPlatformEncoding Integration9_9.LoadedBatch.Schedule

open GaussianProjection GaussianProjection.CosetGeometry IntegerBasis RegevLWE.GaussConv AFT

open NativeLWETableLoader GaussianPoissonSeries RegevSketch RegevSearch

noncomputable section

attribute [local irreducible] famq famd IntegerBasis.Native.sourceTableLaw larObservedRealTableLaw GaussianSource.residueGaussian cosetPMF FiniteDist.map FiniteDist.expectation

theorem givenLattice {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) :
    inputModule B=inputLattice B hB := by
  unfold inputModule inputLattice
  congr 2
  funext i
  simp [realBasis_apply,latVec,Matrix.mulVec_single]

theorem coset_source_coefficients {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (R ε : ℝ) (hR : 0 < R) (he : 0<ε) (he' : ε<1)
    (hsm : smoothingParam (inputLattice B hB) ε ≤ R) (z : Fin n → ℤ) :
    coefficientMass B R z = ((cosetPMF (inputLattice B hB) 0 hR he he' hsm)
       ((integerBasis B hB).equivFun.symm z)).toReal := by
  let e := (integerBasis B hB).equivFun.symm.toEquiv
  have heq (y : Fin n → ℤ) : (e y : EuclideanSpace ℝ (Fin n))=latVec B y := coefficient_point B hB y
  have hz : (∑' y : Fin n → ℤ,rho R (latVec B y)) = rhoCoset R (inputLattice B hB) 0 := by
    have h := e.tsum_eq (fun x : inputLattice B hB => rho R (x : EuclideanSpace ℝ (Fin n)))
    simpa only [rhoCoset,add_zero,heq] using h
  rw [cosetPMF_toReal,cosetMass_formula,add_zero]
  change rho R (latVec B z) / (∑' y : Fin n → ℤ,rho R (latVec B y)) = rho R (e z : EuclideanSpace ℝ (Fin n)) / _
  rw [hz,heq]

theorem from_coords {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (u : Fin n → ℚ)
    (z : Fin n → ℤ) (hu : ∀ j, ∑ i, (B i j:ℚ)*u i=z j) :
    dualCoordinates B hB z=rationalPoint u := by
  have hcast := (BDDNative.lift_ofFn B hB z).symm.trans (lift_eq B hB z u hu)
  have eq : BDDNative.combination B z = u := List.ofFn_inj.mp hcast
  rw [←BDDNative.combination_real,eq]
  rfl

theorem coords_mod {n q : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (z : Fin n → ℤ) :
    secretCoordinates q (inputLattice B hB) (integerBasis B hB)
      ⟨dualCoordinates B hB z,dualCoordinates_mem B hB z⟩ = fun j => (z j:ZMod q) := by
  funext i
  have hr : (pairing (inputLattice B hB) ⟨dualCoordinates B hB z,dualCoordinates_mem B hB z⟩
      (integerBasis B hB i) : ℝ) = (z i:ℝ) := by
    rw [pairing_spec]
    exact dualCoordinates_inner _ _ _ _
  have hi : pairing (inputLattice B hB) ⟨dualCoordinates B hB z,dualCoordinates_mem B hB z⟩
      (integerBasis B hB i) = z i := by exact_mod_cast hr
  exact congrArg (fun i : ℤ => (i:ZMod q)) hi

theorem born_range (T : MFamily) (w : Str) (event : Str → Prop) :
    0 ≤ outputProb T w event ∧ outputProb T w event ≤ 1 := by
  unfold outputProb
  have hn := (runLayered_mass (T.circ w.length) (basisInput (a := T.anc w.length) (toBits w))).trans
    (basisInput_mass (a := T.anc w.length) (toBits w))
  simp only [Complex.normSq_eq_norm_sq] at hn
  constructor
  · exact Finset.sum_nonneg fun j _ => by split <;> positivity
  · rw [←hn]
    apply Finset.sum_le_sum
    intro j _
    split <;> first | exact le_rfl | positivity

theorem tv_transfer {α : Type*} [Fintype α] (p q : FiniteDist α) (t : α → ℝ)
    (ht : ∀ a, 0 ≤ t a ∧ t a ≤ 1) :
    p.expectation t - q.expectation t ≤ (∑ a, |p.weight a - q.weight a|) / 2 := by
  have hp (x : α) : 2*((p.weight x - q.weight x)*t x) ≤
      |p.weight x-q.weight x| + (p.weight x-q.weight x) := by
    by_cases h : 0 ≤ p.weight x - q.weight x
    · rw [abs_of_nonneg h]
      nlinarith [mul_le_mul_of_nonneg_left (ht x).2 h]
    · rw [abs_of_nonpos (le_of_not_ge h)]
      nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) (ht x).1]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun x _ => hp x)
  simp only [← Finset.mul_sum,sub_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib,p.sum_one,q.sum_one,sub_self,add_zero] at hh
  unfold FiniteDist.expectation
  linarith

abbrev window (samples : Polynomial ℕ) (n : ℕ) : ℕ := 768*(samples.eval n*famd n+1)

def variance (n M i : ℕ) : ℚ := (famσ n:ℚ)^2-((famσ n:ℚ)^2/2)*(i:ℚ)/M

theorem variance_at_least_one {n M : ℕ} (hM : 0<M) (i : Fin (M+1)) : 1 ≤ variance n M i.val := by
  have hn : (2:ℚ)≤(famσ n:ℚ) := by unfold famσ famL;push_cast;linarith
  have hci : (i.val:ℚ)≤M := by exact_mod_cast (Nat.lt_succ_iff.mp i.isLt)
  have hbound : ((famσ n:ℚ)^2/2)*(i.val:ℚ)/M ≤ (famσ n:ℚ)^2/2 :=
    (div_le_iff₀ (by exact_mod_cast hM)).mpr (mul_le_mul_of_nonneg_left hci (by positivity))
  unfold variance
  nlinarith only [sq_nonneg ((famσ n:ℚ)-2),hn,hbound]

theorem zero_query {n q : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℚ) (digits : Fin 0 → Fin n → ℕ) :
    BDDNative.terminalQuery B q x digits=x := by
  simp [BDDNative.terminalQuery,BDDNative.digitCoefficients,BDDNative.combination]

theorem grid_generic (p : Polynomial ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ blocks rows, blocks*rows ≤ p.eval n →
    ∀ (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (q : ℕ) [NeZero q], 2 ≤ q →
    ∀ (x : Fin n → ℚ) (U : dual (inputLattice B hB)) (R : ℝ) (hR : 0<R),
    ∀ (he : 0<smoothingError n) (he1 : smoothingError n<1)
      (hsm : smoothingParam (inputLattice B hB) (smoothingError n) ≤ R/(Real.sqrt 2*(q:ℝ))),
    R^2*‖rationalPoint x-(U:IntegerBasis.Space (dimension:=n))‖^2 ≤ ((n+2:ℕ):ℝ)^2/2 →
    let M := 768*(blocks*rows+1)
    let source := cosetPMF (inputLattice B hB) 0 hR he he1
      (source_and_modulus_smoothing q (inputLattice B hB) hR he hsm).1
    ∃ i : Fin (M+1),
      let actual := (IntegerBasis.Native.sourceTableLaw B hB source x q (blocks*rows)
        (variance n M i.val) ((n+2)*M) M).map (groupTable (blocks:=blocks) (rows:=rows))
      let ideal := larObservedRealTableLaw q n rows blocks (GaussianSource.residueGaussian rows q (↑(n+2:ℕ))
        (by exact_mod_cast (show 0<n+2 by omega))) (secretCoordinates q (inputLattice B hB) (integerBasis B hB) U)
      (∑ t,|actual.weight t-ideal.weight t|)/2 ≤ 1/24 := by
  obtain ⟨N,h⟩ := IntegerBasis.Native.common_good_observed_blocks p
  refine ⟨N,?_⟩
  intro n hn blocks rows hrows B hB q _ hq x U R hR he he1 hsm hd
  obtain ⟨i,hi⟩ := h n hn blocks rows hrows B hB q hq x U R hR he he1 hsm hd
  refine ⟨i,?_⟩
  have H := hi 0
  dsimp only at H ⊢
  rw [zero_query,BDDNative.nearestSequence] at H
  simpa only [variance,famσ,famL,Nat.mul_zero,pow_zero,div_one] using H

end

end InfoLossLAR.WorstCase.ShortProbe

end P2MDyadicModule89

/- Helper module TrialCoordinates. -/
section P2MDyadicModule90

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

set_option maxRecDepth 20000

namespace InfoLossLAR.WorstCase.ShortProbe

open scoped BigOperators Classical

open QAlgorithms.Complexity Integration9_9.LARPlatformEncoding Integration9_9.LoadedBatch.Schedule

open GaussianProjection GaussianProjection.CosetGeometry IntegerBasis RegevLWE.GaussConv AFT

open NativeLWETableLoader GaussianPoissonSeries RegevSketch RegevSearch

noncomputable section

attribute [local irreducible] famq famd IntegerBasis.Native.sourceTableLaw larObservedRealTableLaw GaussianSource.residueGaussian cosetPMF FiniteDist.map FiniteDist.expectation

theorem grid_coordinates (p : Polynomial ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (blocks rows : ℕ), blocks*rows ≤ p.eval n → ∀ (q : ℕ) [NeZero q], 2 ≤ q → ∀ (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (R : ℚ), 0 < R →
      Real.sqrt 2*(q:ℝ)*smoothingParam (inputModule B) (smoothingError n) < (R:ℝ) →
    ∀ (x u : Fin n → ℚ) (z : Fin n → ℤ), (∀ j,∑ i,(B i j:ℚ)*u i=z j) →
      (R:ℝ)^2*(∑ i,((x i-u i:ℚ):ℝ)^2) < (famσ n:ℝ)^2/4 →
    ∃ (i : Fin ((768*(blocks*rows+1)) + 1)) (source : PMF (inputLattice B hB)),
      (∀ a, coefficientMass B (R:ℝ) a = (source ((integerBasis B hB).equivFun.symm a)).toReal) ∧
      let M := (768*(blocks*rows+1))
      let actual := (IntegerBasis.Native.sourceTableLaw B hB source x q (blocks*rows)
        (variance n M i.val) (famσ n*M) M).map (groupTable (blocks:=blocks) (rows:=rows))
      let ideal := larObservedRealTableLaw q n rows blocks (GaussianSource.residueGaussian rows q (famσ n:ℝ) (by unfold famσ famL; positivity))
        (fun j => (z j : ZMod q))
      (∑ t,|actual.weight t - ideal.weight t|)/2 ≤ 1/24 := by
  obtain ⟨N,hN⟩ := grid_generic p
  refine ⟨max N 2,?_⟩
  intro n ht blocks rows hp q inst hq B hB R hR hsm x u z hu hd
  have hn2 : 2 ≤ n := by omega
  have he : 0<smoothingError n := by unfold smoothingError;positivity
  have he1 : smoothingError n<1 := by
    unfold smoothingError
    have hp : 0 < (n+2).size := Nat.size_pos.mpr (by omega)
    have hs : 0 < (n+2).size^2 := by positivity
    have hpow : (1:ℝ)<2^((n+2).size^2) := one_lt_pow₀ (by norm_num) (by omega)
    exact (div_lt_iff₀ (zero_lt_one.trans hpow)).mpr (by simpa using hpow)
  let L := inputLattice B hB
  let U : dual L := ⟨dualCoordinates B hB z,dualCoordinates_mem B hB z⟩
  have hRq : 0 < Real.sqrt 2*(q:ℝ) := mul_pos (by positivity) (by exact_mod_cast (NeZero.pos q))
  have hR' : 0 < (R:ℝ) := Rat.cast_pos.mpr hR
  have hsm' : smoothingParam L (smoothingError n) ≤ (R:ℝ)/(Real.sqrt 2*(q:ℝ)) := by
    apply (le_div_iff₀ hRq).mpr
    rw [givenLattice B hB] at hsm
    calc
      _ = (Real.sqrt 2*(q:ℝ))*smoothingParam (inputLattice B hB) (smoothingError n) := mul_comm _ _
      _ ≤ _ := hsm.le
  have herr : ‖rationalPoint x-(U:IntegerBasis.Space (dimension:=n))‖^2 = ∑ i,((x i-u i:ℚ):ℝ)^2 := by
    change ‖rationalPoint x - dualCoordinates B hB z‖^2=_
    rw [from_coords B hB u z hu,EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    change ((x i:ℝ)-(u i:ℝ))^2=_
    rw [Rat.cast_sub]
  have hd' : (R:ℝ)^2*‖rationalPoint x-(U:IntegerBasis.Space (dimension:=n))‖^2 ≤ ((n+2:ℕ):ℝ)^2/2 := by
    rw [herr]
    change (R:ℝ)^2*(∑ i,((x i-u i:ℚ):ℝ)^2) < ((n+2:ℕ):ℝ)^2/4 at hd
    linarith only [hd, sq_nonneg (((n+2:ℕ):ℝ))]
  obtain ⟨i,hi⟩ := hN n (by omega) blocks rows hp B hB q hq x U (R:ℝ) hR'
    he he1 hsm' hd'
  let M := (768*(blocks*rows+1))
  let s := fun j : Fin n => (z j:ZMod q)
  let source := cosetPMF L 0 hR' he he1 (source_and_modulus_smoothing q L hR' he hsm').1
  let actual := (IntegerBasis.Native.sourceTableLaw B hB source x q (blocks*rows)
    (variance n M i.val) (famσ n*M) M).map (groupTable (blocks:=blocks) (rows:=rows))
  let ideal := larObservedRealTableLaw q n rows blocks (GaussianSource.residueGaussian rows q (famσ n:ℝ) (by unfold famσ famL; positivity)) s
  have sg : secretCoordinates q (inputLattice B hB) (integerBasis B hB) U = s := coords_mod B hB z
  have hj := hi
  dsimp only at hj
  rw [sg] at hj
  have htv : (∑ t, |actual.weight t - ideal.weight t|)/2 ≤ 1/24 := by
    dsimp only [ideal,actual,source,L,M,variance,famσ,famL,famN]
    exact hj
  exact ⟨i,source,coset_source_coefficients B hB (R:ℝ) (smoothingError n) hR' he he1 _,htv⟩

end

end InfoLossLAR.WorstCase.ShortProbe

end P2MDyadicModule90

/- Helper module GridRaw. -/
section P2MDyadicModule91

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

set_option maxRecDepth 20000

namespace InfoLossLAR.WorstCase.ShortProbe

open scoped BigOperators Classical

open QAlgorithms.Complexity Integration9_9.LARPlatformEncoding Integration9_9.LoadedBatch.Schedule

open GaussianProjection GaussianProjection.CosetGeometry IntegerBasis RegevLWE.GaussConv AFT

open NativeLWETableLoader GaussianPoissonSeries RegevSketch RegevSearch

noncomputable section

attribute [local irreducible] famq famd IntegerBasis.Native.sourceTableLaw larObservedRealTableLaw GaussianSource.residueGaussian cosetPMF FiniteDist.map FiniteDist.expectation

theorem grid_raw (p samples : Polynomial ℕ) (hp : ∀ n, samples.eval n*famd n ≤ p.eval n) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (R : ℚ), 0 < R →
      Real.sqrt 2*(famq n:ℝ)*smoothingParam (inputModule B) (smoothingError n) < (R:ℝ) →
    ∀ (x u : Fin n → ℚ) (z : Fin n → ℤ), (∀ j,∑ i,(B i j:ℚ)*u i=z j) →
      (R:ℝ)^2*(∑ i,((x i-u i:ℚ):ℝ)^2) < (famσ n:ℝ)^2/4 →
    ∃ (i : Fin (window samples n + 1)) (source : PMF (inputLattice B hB)),
      (∀ a, coefficientMass B (R:ℝ) a = (source ((integerBasis B hB).equivFun.symm a)).toReal) ∧
      let M := window samples n
      let actual := (IntegerBasis.Native.sourceTableLaw B hB source x (famq n) (samples.eval n*famd n)
        (variance n M i.val) (famσ n*M) M).map (groupTable (blocks:=samples.eval n) (rows:=famd n))
      let ideal := larObservedRealTableLaw (famq n) n (famd n) (samples.eval n) (GaussianSource.residueGaussian (famd n) (famq n) (famσ n:ℝ) (by unfold famσ famL; positivity))
        (fun j => (z j : ZMod (famq n)))
      (∑ t,|actual.weight t - ideal.weight t|)/2 ≤ 1/24 := by
  obtain ⟨N,h⟩ := grid_coordinates p
  refine ⟨N,?_⟩
  intro n hn B hB R hR hwide x u z hu hd
  exact h n hn (samples.eval n) (famd n) (hp n) (famq n) (famq_prime n).two_le B hB R hR hwide x u z hu hd

end

end InfoLossLAR.WorstCase.ShortProbe

end P2MDyadicModule91

/- Helper module TrialGrid. -/
section P2MDyadicModule92

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

set_option maxRecDepth 20000

namespace InfoLossLAR.WorstCase.ShortProbe

open scoped BigOperators Classical

open QAlgorithms.Complexity Integration9_9.LARPlatformEncoding Integration9_9.LoadedBatch.Schedule

open GaussianProjection GaussianProjection.CosetGeometry IntegerBasis RegevLWE.GaussConv AFT

open NativeLWETableLoader GaussianPoissonSeries RegevSketch RegevSearch

noncomputable section

attribute [local irreducible] famq famd IntegerBasis.Native.sourceTableLaw larObservedRealTableLaw GaussianSource.residueGaussian cosetPMF FiniteDist.map FiniteDist.expectation

theorem grid_trial (p samples : Polynomial ℕ) (hp : ∀ n, samples.eval n*famd n ≤ p.eval n) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (R : ℚ), 0 < R →
      Real.sqrt 2*(famq n:ℝ)*smoothingParam (inputModule B) (smoothingError n) < (R:ℝ) →
    ∀ (x u : Fin n → ℚ) (z : Fin n → ℤ), (∀ j,∑ i,(B i j:ℚ)*u i=z j) →
      (R:ℝ)^2*(∑ i,((x i-u i:ℚ):ℝ)^2) < (famσ n:ℝ)^2/4 →
    ∃ (i : Fin (window samples n + 1)) (source : PMF (inputLattice B hB)),
      (∀ a, coefficientMass B (R:ℝ) a = (source ((integerBasis B hB).equivFun.symm a)).toReal) ∧
      let M := window samples n
      let actual := (IntegerBasis.Native.sourceTableLaw B hB source x (famq n) (samples.eval n*famd n)
        (variance n M i.val) (famσ n*M) M).map (groupTable (blocks:=samples.eval n) (rows:=famd n))
      let ideal := larObservedRealTableLaw (famq n) n (famd n) (samples.eval n) (fixedGaussianSource (famd n) n)
        (fun j => (z j : ZMod (famq n)))
      (∑ t,|actual.weight t - ideal.weight t|)/2 ≤ 1/24 := by
  have he (n : ℕ) : fixedGaussianSource (famd n) n = GaussianSource.residueGaussian (famd n) (famq n) (famσ n:ℝ) (by unfold famσ famL; positivity) := rfl
  simp_rw [he]
  exact grid_raw p samples hp

end

end InfoLossLAR.WorstCase.ShortProbe

end P2MDyadicModule92

/- Helper module TrialTransfer. -/
section P2MDyadicModule93

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

set_option maxRecDepth 20000

namespace InfoLossLAR.WorstCase.ShortProbe

open scoped BigOperators Classical

open QAlgorithms.Complexity Integration9_9.LARPlatformEncoding Integration9_9.LoadedBatch.Schedule

open GaussianProjection GaussianProjection.CosetGeometry IntegerBasis RegevLWE.GaussConv AFT

open NativeLWETableLoader GaussianPoissonSeries RegevSketch RegevSearch

noncomputable section

attribute [local irreducible] famq famd IntegerBasis.Native.sourceTableLaw larObservedRealTableLaw GaussianSource.residueGaussian cosetPMF FiniteDist.map FiniteDist.expectation

theorem fair_from_tv {n blocks rows q : ℕ} [NeZero q]
    (sec : ℕ) (pp : Str) (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (R : ℝ)
    (source : PMF (inputLattice B hB))
    (hm : ∀ z, coefficientMass B R z = (source ((integerBasis B hB).equivFun.symm z)).toReal)
    (x : Fin n → ℚ) (v : ℚ) (hv : 1≤v) (cutoff bits : ℕ)
    (ideal : FiniteDist (Fin blocks → Matrix (Fin rows) (Fin n) (ZMod q) × (Fin rows → ZMod q)))
    (A : MFamily) (event : Str → Prop)
    (hsearch : (3/4:ℝ) ≤ ideal.expectation (fun t => outputProb A (encInput sec pp (encTable t)) event))
    (htv : let actual := (IntegerBasis.Native.sourceTableLaw B hB source x q (blocks*rows) v cutoff bits).map
                 (groupTable (blocks:=blocks) (rows:=rows))
           (∑ t, |actual.weight t - ideal.weight t|)/2 ≤ 1/24) :
    (17/24:ℝ) ≤ ∑' vals : Fin (blocks*rows) → Fin n → ℤ,(∏ j,coefficientMass B R (vals j)) *
      (FiniteDist.uniform (Fin ((blocks*rows)*((bits+1)+(2*cutoff+1)+1)) → Fin 2)).expectation
        (fun tape => outputProb A (observedWord (blocks:=blocks) (rows:=rows) sec pp B vals x q v cutoff bits tape) event) := by
  let actual := (IntegerBasis.Native.sourceTableLaw B hB source x q (blocks*rows) v cutoff bits).map
                 (groupTable (blocks:=blocks) (rows:=rows))
  let test := fun raw => outputProb A raw event
  let f := fun (t : Fin blocks → Matrix (Fin rows) (Fin n) (ZMod q) × (Fin rows → ZMod q)) =>
      test (encInput sec pp (encTable t))
  have stable := tv_transfer ideal actual f (fun _ => born_range _ _ _)
  have sym : (∑ t, |ideal.weight t - actual.weight t|)/2 ≤ 1/24 := by
    simp_rw [abs_sub_comm (ideal.weight _) (actual.weight _)]
    exact htv
  have he : (17/24:ℝ) ≤ actual.expectation f := by
    change (3/4:ℝ) ≤ ideal.expectation f at hsearch
    linarith only [hsearch,stable.trans sym]
  exact he.trans_eq (actual_test sec pp B hB R source hm x q v hv cutoff bits test)

end

end InfoLossLAR.WorstCase.ShortProbe

end P2MDyadicModule93

/- Helper module FixedFair. -/
section P2MDyadicModule94

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

set_option maxRecDepth 20000

namespace InfoLossLAR.WorstCase.ShortProbe

open scoped BigOperators Classical

open QAlgorithms.Complexity Integration9_9.LARPlatformEncoding Integration9_9.LoadedBatch.Schedule

open GaussianProjection GaussianProjection.CosetGeometry IntegerBasis RegevLWE.GaussConv AFT

open NativeLWETableLoader GaussianPoissonSeries RegevSketch RegevSearch

noncomputable section

attribute [local irreducible] famq famd IntegerBasis.Native.sourceTableLaw larObservedRealTableLaw GaussianSource.residueGaussian cosetPMF FiniteDist.map FiniteDist.expectation

theorem fixed_fair {n blocks : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (R : ℝ)
    (source : PMF (inputLattice B hB))
    (hm : ∀ z, coefficientMass B R z = (source ((integerBasis B hB).equivFun.symm z)).toReal)
    (x : Fin n → ℚ) (v : ℚ) (hv : 1≤v) (cutoff bits : ℕ)
    (ideal : FiniteDist (Fin blocks → Matrix (Fin (famd n)) (Fin n) (ZMod (famq n)) × (Fin (famd n) → ZMod (famq n))))
    (A : MFamily) (event : Str → Prop)
    (hsearch : (3/4:ℝ) ≤ ideal.expectation (fun t => outputProb A (encInput n (famPP n) (encTable t)) event))
    (htv : let actual := (IntegerBasis.Native.sourceTableLaw B hB source x (famq n) (blocks*famd n) v cutoff bits).map
                 (groupTable (blocks:=blocks) (rows:=famd n))
           (∑ t, |actual.weight t - ideal.weight t|)/2 ≤ 1/24) :
    (17/24:ℝ) ≤ ∑' vals : Fin (blocks*famd n) → Fin n → ℤ,(∏ j,coefficientMass B R (vals j)) *
      (FiniteDist.uniform (Fin ((blocks*famd n)*((bits+1)+(2*cutoff+1)+1)) → Fin 2)).expectation
        (fun tape => outputProb A (observedWord (blocks:=blocks) (rows:=famd n) n (famPP n) B vals x (famq n) v cutoff bits tape) event) :=
    fair_from_tv n (famPP n) B hB R source hm x v hv cutoff bits ideal A event hsearch htv

end

end InfoLossLAR.WorstCase.ShortProbe

end P2MDyadicModule94

/- Helper module KnownSearch. -/
section P2MDyadicModule95

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

set_option maxRecDepth 20000

namespace InfoLossLAR.WorstCase.ShortProbe

open scoped BigOperators Classical

open QAlgorithms.Complexity Integration9_9.LARPlatformEncoding Integration9_9.LoadedBatch.Schedule

open GaussianProjection GaussianProjection.CosetGeometry IntegerBasis RegevLWE.GaussConv AFT

open NativeLWETableLoader GaussianPoissonSeries RegevSketch RegevSearch

noncomputable section

attribute [local irreducible] famq famd IntegerBasis.Native.sourceTableLaw larObservedRealTableLaw GaussianSource.residueGaussian cosetPMF FiniteDist.map FiniteDist.expectation

theorem known_search {samples : Polynomial ℕ} {A : MFamily} {S : Set ℕ} {K n : ℕ}
    (hh : SearchOn A samples K S) (hn : n ∈ S) (ht : K≤n) (z : Fin n → ℤ) :
    let s := fun j : Fin n => (z j:ZMod (famq n))
    let ideal := larObservedRealTableLaw (famq n) n (famd n) (samples.eval n) (fixedGaussianSource (famd n) n) s
    let event := fun raw : Str => (readVector raw).2=List.ofFn fun j => (s j).val
    3/4 ≤ ideal.expectation (fun t => outputProb A (encInput n (famPP n) (encTable t)) event) := by
  exact hh n hn ht (fun j => (z j:ZMod (famq n)))

end

end InfoLossLAR.WorstCase.ShortProbe

end P2MDyadicModule95

/- Helper module TrialReady. -/
section P2MDyadicModule96

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

set_option maxRecDepth 20000

namespace InfoLossLAR.WorstCase.ShortProbe

open scoped BigOperators Classical

open QAlgorithms.Complexity Integration9_9.LARPlatformEncoding Integration9_9.LoadedBatch.Schedule

open GaussianProjection GaussianProjection.CosetGeometry IntegerBasis RegevLWE.GaussConv AFT

open NativeLWETableLoader GaussianPoissonSeries RegevSketch RegevSearch

noncomputable section

attribute [local irreducible] famq famd IntegerBasis.Native.sourceTableLaw larObservedRealTableLaw GaussianSource.residueGaussian cosetPMF FiniteDist.map FiniteDist.expectation

def successEvent {n : ℕ} (z : Fin n → ℤ) (raw : Str) : Prop :=
  (readVector raw).2=List.ofFn fun j => (z j:ZMod (famq n)).val

def fixedInputLaw (n blocks : ℕ) (z : Fin n → ℤ) := larObservedRealTableLaw (famq n) n (famd n) blocks
  (fixedGaussianSource (famd n) n) (fun j => (z j : ZMod (famq n)))

theorem ready {n : ℕ} (samples : Polynomial ℕ) (A : MFamily) (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det≠0) (R : ℚ) (x : Fin n → ℚ) (z : Fin n → ℤ)
    (i : Fin (window samples n + 1)) (source : PMF (inputLattice B hB))
    (hm : ∀ a, coefficientMass B (R:ℝ) a = (source ((integerBasis B hB).equivFun.symm a)).toReal)
    (hH : 3/4 ≤ (fixedInputLaw n (samples.eval n) z).expectation
      (fun t => outputProb A (encInput n (famPP n) (encTable t)) (successEvent z)))
    (htv : let M := window samples n
           let actual := (IntegerBasis.Native.sourceTableLaw B hB source x (famq n) (samples.eval n*famd n)
             (variance n M i.val) (famσ n*M) M).map (groupTable (blocks:=samples.eval n) (rows:=famd n))
           (∑ t, |actual.weight t - (fixedInputLaw n (samples.eval n) z).weight t|)/2 ≤ 1/24) :
    let M := window samples n
    let rows := samples.eval n*famd n
    let v := variance n M i.val
    let cutoff' := famσ n*M
    let bits := M
    (17/24:ℝ) ≤ ∑' vals : Fin rows → Fin n → ℤ,(∏ j,coefficientMass B (R:ℝ) (vals j)) *
      (FiniteDist.uniform (Fin (rows*((bits+1)+(2*cutoff'+1)+1)) → Fin 2)).expectation
        (fun tape => outputProb A (observedWord (blocks:=samples.eval n) (rows:=famd n) n (famPP n) B vals x
          (famq n) v cutoff' bits tape) (successEvent z)) := by
  have hM : 0<window samples n := Nat.mul_pos (by decide : 0<768) (Nat.succ_pos _)
  dsimp only at htv ⊢
  exact fixed_fair B hB (R:ℝ) source hm x (variance n (window samples n) i.val) (variance_at_least_one hM i)
    (famσ n*window samples n) (window samples n) (fixedInputLaw n (samples.eval n) z) A (successEvent z) hH htv

end

end InfoLossLAR.WorstCase.ShortProbe

end P2MDyadicModule96

/- Helper module TrialFair. -/
section P2MDyadicModule97

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

set_option maxRecDepth 20000

namespace InfoLossLAR.WorstCase.ShortProbe

open scoped BigOperators Classical

open QAlgorithms.Complexity Integration9_9.LARPlatformEncoding Integration9_9.LoadedBatch.Schedule

open GaussianProjection GaussianProjection.CosetGeometry IntegerBasis RegevLWE.GaussConv AFT

open NativeLWETableLoader GaussianPoissonSeries RegevSketch RegevSearch

noncomputable section

attribute [local irreducible] famq famd IntegerBasis.Native.sourceTableLaw larObservedRealTableLaw GaussianSource.residueGaussian cosetPMF FiniteDist.map FiniteDist.expectation

theorem good_real_trial_proof (p samples : Polynomial ℕ) (hp : ∀ n, samples.eval n*famd n ≤ p.eval n)
    (A : MFamily) (cutoff : ℕ) (S : Set ℕ) (hsearch : SearchOn A samples cutoff S) :
    ∃ N : ℕ, ∀ n ∈ S, N ≤ n → ∀ (B : Matrix (Fin n) (Fin n) ℤ), B.det≠0 →
    ∀ (R : ℚ), 0 < R →
      Real.sqrt 2*(famq n:ℝ)*smoothingParam (inputModule B) (smoothingError n) < (R:ℝ) →
    ∀ (x u : Fin n → ℚ) (z : Fin n → ℤ), (∀ j,∑ i,(B i j:ℚ)*u i=z j) →
      (R:ℝ)^2*(∑ i,((x i-u i:ℚ):ℝ)^2) < (famσ n:ℝ)^2/4 →
    ∃ i : Fin (window samples n + 1),
      let M := window samples n
      let rows := samples.eval n*famd n
      let v := variance n M i.val
      let cutoff' := famσ n*M
      let bits := M
      (17/24:ℝ) ≤ ∑' vals : Fin rows → Fin n → ℤ,(∏ j, coefficientMass B (R:ℝ) (vals j)) *
        (FiniteDist.uniform (Fin (rows*((bits+1)+(2*cutoff'+1)+1)) → Fin 2)).expectation
        (fun tape => outputProb A (observedWord (blocks:=samples.eval n) (rows:=famd n) n (famPP n) B vals x
          (famq n) v cutoff' bits tape) (fun raw => (readVector raw).2=List.ofFn fun j => (z j:ZMod (famq n)).val)) := by
  obtain ⟨N,hN⟩ := grid_trial p samples hp
  refine ⟨max N cutoff,?_⟩
  intro n hn ht B hB R hR hsm x u z hu hd
  obtain ⟨i,source,hm,htv⟩ := hN n ((le_max_left _ _).trans ht) B hB R hR hsm x u z hu hd
  refine ⟨i,?_⟩
  dsimp only at htv ⊢
  have H := known_search hsearch hn ((le_max_right _ _).trans ht) z
  exact ready samples A B hB R x z i source hm H htv

end

end InfoLossLAR.WorstCase.ShortProbe

end P2MDyadicModule97

open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open InfoLossLAR.WorstCase.RegevSearch InfoLossLAR.WorstCase.NativeLWETableLoader
open RegevLWE.GaussConv AFT Integration9_9.LARPlatformEncoding
open scoped BigOperators Classical

set_option maxRecDepth 30000
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] observed famq famd outputProb coefficientMass
theorem solution (p samples : Polynomial ℕ) (hp : ∀ n, samples.eval n*famd n ≤ p.eval n)
    (A : MFamily) (cutoff : ℕ) (S : Set ℕ) (hsearch : SearchOn A samples cutoff S) :
    ∃ N : ℕ, ∀ n ∈ S, N ≤ n → ∀ (B : Matrix (Fin n) (Fin n) ℤ), B.det≠0 →
    ∀ (R : ℚ), 0 < R →
      Real.sqrt 2*(famq n:ℝ)*smoothingParam (inputModule B) (smoothingError n) < (R:ℝ) →
    ∀ (x u : Fin n → ℚ) (z : Fin n → ℤ), (∀ j,∑ i,(B i j:ℚ)*u i=z j) →
      (R:ℝ)^2*(∑ i,((x i-u i:ℚ):ℝ)^2) < (famσ n:ℝ)^2/4 →
    ∃ i : Fin ((768*(samples.eval n*famd n+1)) + 1),
      let M := (768*(samples.eval n*famd n+1))
      let rows := samples.eval n*famd n
      let v := ((famσ n:ℚ)^2-((famσ n:ℚ)^2/2)*(i.val:ℚ)/M)
      let cutoff' := famσ n*M
      let bits := M
      (17/24:ℝ) ≤ ∑' vals : Fin rows → Fin n → ℤ,(∏ j, coefficientMass B (R:ℝ) (vals j)) *
        (FiniteDist.uniform (Fin (rows*((bits+1)+(2*cutoff'+1)+1)) → Fin 2)).expectation
        (fun tape => outputProb A (observed ((unary n,famPP n),((List.replicate (samples.eval n) (),List.replicate (famd n) ()),
             ((((List.ofFn (fun i => List.ofFn (B i)),List.ofFn x),
               (famq n,(v,(List.replicate cutoff' (),List.replicate bits ())))),List.ofFn (fun i => List.ofFn (vals i))),
                List.ofFn (fun j => decide ((tape j).val=1)))))) (fun raw => (readVector raw).2=List.ofFn fun j => (z j:ZMod (famq n)).val)) := by
  exact InfoLossLAR.WorstCase.ShortProbe.good_real_trial_proof p samples hp A cutoff S hsearch
