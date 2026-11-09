-- Prove2me | solution 1 for OAI.SharpPlanar.Residual28.bound0_1_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:02:37.179162+00:00
-- url     : https://prove2.me/submissions/5cc945e0-cb35-431e-b38e-e828a033d18a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G383
import Definitions.Def_OAIQ098G411
import Definitions.Def_OAIQ098G1560
import Definitions.Def_OAIQ098G1655
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1691
import Definitions.Def_OAIQ098G1693
import Definitions.Def_OAIQ098G1696
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint1_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint2_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint3_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint4_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint5_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint6_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel28_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tm1_28_0_sums_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tm1_28_1_KContains_g
import Theorems.Thm_OAI_SharpPlanar_D_0_g
import Theorems.Thm_OAI_SharpPlanar_D_1_g
import Theorems.Thm_OAI_SharpPlanar_D_3_g
import Theorems.Thm_OAI_SharpPlanar_D_4_g
import Theorems.Thm_OAI_SharpPlanar_D_7_g
import Theorems.Thm_OAI_SharpPlanar_D_9_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_coefficientBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointLambda_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointZ_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_powFast_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_abs_bound_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_neg_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_bBounds_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piBounds_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_precision_pos_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_inflate_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_qiBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_b_pos_g
import Theorems.Thm_OAI_SharpPlanar_cached_density_rule_contains_g
import Theorems.Thm_OAI_SharpPlanar_complexLambda_ofReal_g
import Theorems.Thm_OAI_SharpPlanar_complexZ_ofReal_g
import Theorems.Thm_OAI_SharpPlanar_continuousOn_density_g
import Theorems.Thm_OAI_SharpPlanar_h_pos_g
import Theorems.Thm_OAI_SharpPlanar_piece_interval_g
import Theorems.Thm_OAI_SharpPlanar_tableMomentK_eq_g
import Theorems.Thm_OAI_SharpPlanar_table_range_mass_g
import Theorems.Thm_OAI_SharpPlanar_transformedMoment_rule_error_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

lemma denominator_ne (t : ℝ) : (t : ℂ) + Complex.I * h ≠ 0 := by
  intro he
  have hh := congrArg Complex.im he
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.ofReal_re, Complex.I_im, zero_mul, one_mul, zero_add, Complex.zero_im] at hh
  exact (ne_of_gt h_pos_g) hh

lemma continuous_lambda : Continuous lambda := by
  unfold lambda
  fun_prop (disch := intro t; exact mul_ne_zero (by exact_mod_cast b_pos_g.ne') (denominator_ne t))

lemma continuous_z : Continuous z := by
  unfold z
  fun_prop (disch := intro t; exact denominator_ne t)

lemma continuous_kernelMoment (ell : ℕ) (s : ℝ) : Continuous (kernelMoment ell s) := by
  unfold kernelMoment
  exact (continuous_lambda.mul ((continuous_const.mul continuous_z).pow ell)).mul
    (Complex.continuous_exp.comp ((continuous_const.mul continuous_z).mul continuous_const))

lemma piece_integrable (p : CardinalData) (ell j : ℕ) (hj : j < 6) (s : ℝ) :
    IntervalIntegrable (fun t => density p j t * kernelMoment ell s t) volume
      ((j : ℝ)/6) (((j : ℝ)+1)/6) := by
  exact ((continuousOn_density_g p j).mul (continuous_kernelMoment ell s).continuousOn).mono
    (fun _ ht => piece_interval_g hj ht) |>.intervalIntegrable

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals

lemma zeroBox_contains : zeroBox.Contains 0 := by simp [zeroBox,CBox.Contains,RBox.Contains]
end SharpPlanar.IntegerIntervals

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma kernel0Box_contains {p : PointBox} {t : ℝ} (hp : p.Contains t) {m : ℕ}
    (hm : m < 128) : (kernel0Box p m).Contains
      (lambda t*Complex.exp (Complex.I*Real.pi*z t*m)) := by
  have he := CBox.contains_powFast_g hp.2.2.2.2 9 (4*m) (by omega)
  rw [← Complex.exp_nat_mul] at he
  have hz := CBox.contains_mul_g hp.2.1 he
  unfold kernel0Box
  convert hz using 1
  all_goals try with_reducible_and_instances rfl
  rw [pointLambda_eq_g,pointZ_eq_g]
  congr 2
  push_cast
  ring

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerIntervals

lemma finSum_contains {N : ℕ} {f : Fin N → CBox} {g : Fin N → ℂ}
    (h : ∀ i, (f i).Contains (g i)) : (finSum f).Contains (∑ i, g i) := by
  induction N with
  | zero => simpa [finSum] using zeroBox_contains
  | succ N ih =>
    rw [Fin.sum_univ_succ]
    exact CBox.contains_add_g (h 0) (ih (fun i => h i.succ))

end SharpPlanar.IntegerIntervals

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MomentRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recurrences for the direct and transformed Gaussian moments -/

namespace SharpPlanar
open ComplexConjugate
open IntegerIntervals IntegerBasis
lemma transformed_factor_zero_contains {a : CBox} {t : ℝ} {m : ℕ}
    (ha : a.Contains (lambda t*Complex.exp (Complex.I*Real.pi*z t*m))) :
    a.Contains (complexTransformedFactor m 1 0 t) := by
  simpa only [complexTransformedFactor,complexZ_ofReal_g,complexLambda_ofReal_g,pow_zero,
    Nat.factorial_zero,Nat.cast_one,div_one,mul_one,Complex.ofReal_natCast] using ha
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_AtomKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
lemma atomPoints_contains (j : Fin 7) : (atomPoints j).Contains ((j.val:ℝ)/6) := by
  fin_cases j
  · simpa [atomPoints] using atomPoint0_contains_g
  · simpa [atomPoints] using atomPoint1_contains_g
  · simpa [atomPoints] using atomPoint2_contains_g
  · simpa [atomPoints] using atomPoint3_contains_g
  · simpa [atomPoints] using atomPoint4_contains_g
  · simpa [atomPoints] using atomPoint5_contains_g
  · simpa [atomPoints] using atomPoint6_contains_g
lemma atomKernel28_0_eq (j : Fin 7) : atomKernel28_0 j = kernel0Box (atomPoints j) 28 := by
  fin_cases j <;> decide +kernel
lemma atomKernel28_0_contains (j : Fin 7) : (atomKernel28_0 j).Contains
    (complexTransformedFactor 28 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel28_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=28) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_NodeIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
namespace Numerical

lemma dSmall_contains : dSmall.Contains (Real.pi*(3+2*b)/18) := by
  have hb := RBox.contains_add_g (RBox.contains_rat_g 3 1 (by norm_num))
    (RBox.contains_scale_g bBounds_contains_g 2 1 (by norm_num))
  convert RBox.contains_scale_g (RBox.contains_mul_g piBounds_contains_g hb) 1 18 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring)
lemma dOther_contains : dOther.Contains (Real.pi*(3-2*b)/18) := by
  have hb := RBox.contains_add_g (RBox.contains_rat_g 3 1 (by norm_num))
    (RBox.contains_scale_g bBounds_contains_g (-2) 1 (by norm_num))
  convert RBox.contains_scale_g (RBox.contains_mul_g piBounds_contains_g hb) 1 18 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring)
lemma dBase_contains : dBase.Contains (7*Real.pi*b/9) := by
  convert RBox.contains_scale_g (RBox.contains_mul_g piBounds_contains_g bBounds_contains_g) 7 9 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring)

lemma dBox_contains (n : ℕ) (hn : n%12 ∈ residues) : (dBox n).Contains (D n) := by
  have hh : D n = D (n%12) := by simp [D]
  rw [hh]
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with hn|hn|hn|hn|hn|hn
  · simpa [D_0_g,hn,dBox,neg_mul,neg_div] using RBox.neg_contains_g dBase_contains
  · simpa [D_1_g,hn,dBox] using dSmall_contains
  · simpa [D_3_g,hn,dBox,neg_mul,neg_div] using RBox.neg_contains_g dSmall_contains
  · simpa [D_4_g,hn,dBox] using dBase_contains
  · simpa [D_7_g,hn,dBox,neg_mul,neg_div] using RBox.neg_contains_g dOther_contains
  · simpa [D_9_g,hn,dBox] using dOther_contains

end Numerical
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableMomentsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Certified quadrature and atomic bounds for the Gaussian moments -/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid Numerical
open scoped BigOperators

lemma tableMoment_error (a : Bool) {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (ell : ℕ) :
    ‖tableMomentIntegral a m ell-tableMomentRule a m ell‖ < 1/10^22 :=
  transformedMoment_rule_error_g _ _ (table_range_mass_g a) hm0 hm1 (by norm_num) ell

lemma table_kernel_zero_contains {box : CBox} {t : ℝ} {m : ℕ}
    (ha : box.Contains ((lambda t * Complex.exp (Complex.I*Real.pi*z t*m))*1)) :
    box.Contains (complexTransformedFactor m 1 0 t) := by
  exact transformed_factor_zero_contains (by simpa only [mul_one] using ha)
lemma table_kernel_one_contains {box : CBox} {t : ℝ} {m : ℕ}
    (ha : box.Contains ((lambda t * Complex.exp (Complex.I*Real.pi*z t*m))*(Complex.I*Real.pi*z t))) :
    box.Contains (complexTransformedFactor m 1 1 t) := by
  simpa only [complexTransformedFactor,complexZ_ofReal_g,complexLambda_ofReal_g,pow_one,
    Nat.factorial_one,Nat.cast_one,div_one,Complex.ofReal_one,mul_one,Complex.ofReal_natCast] using ha

lemma tableAtomBox_contains (a : Bool) {kernel : Fin 7 → CBox} {m : ℝ} {ell : ℕ}
    (hk : ∀ j, (kernel j).Contains (complexTransformedFactor m 1 ell ((j.val:ℝ)/6))) :
    (tableAtomBox a kernel).Contains (tableMomentAtom a m ell) := by
  have hh := finSum_contains (fun j : Fin 7 => CBox.contains_mul_g
    (CBox.contains_scale_g (coefficientBox_contains_g j.val) (if j.val=0 then 1 else 2) 1 (by norm_num)) (hk j))
  have hs := CBox.contains_scale_g hh (if a then 17 else -13) 1000 (by norm_num)
  change (tableAtomBox a kernel).Contains _ at hs
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  cases a <;> simp [tableMomentAtom,tableConstant]


lemma tableMomentK_contains {a : Bool} {m : ℝ} {ell : ℕ} {ab rb : CBox}
    (ha : ab.Contains (tableMomentAtom a m ell))
    (hr : rb.Contains (tableMomentRule a m ell)) (hm0 : 0 ≤ m) (hm1 : m ≤ 100) :
    (inflate (ab.add rb).re).Contains (tableMomentK a m ell) := by
  apply inflate_contains_g (CBox.contains_add_g ha hr).1
  unfold tableMomentK
  have he := (Complex.abs_re_le_norm (tableMomentIntegral a m ell-tableMomentRule a m ell)).trans_lt
    (tableMoment_error a hm0 hm1 ell)
  simpa only [Complex.add_re,Complex.sub_re,add_sub_add_left_eq_sub] using he
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableRuleBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Interval bounds for the transformed Gaussian quadrature rule -/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma tableRule_contains_bridge (a : Bool) (m : ℕ) (b : Bool)
    {c k : Fin 6 → Fin 16 → Fin 16 → CBox}
    (hc : ∀ j i v, (c j i v).Contains ((fejerWeight (16*i.val+v.val):ℂ)*
      tableDensity a j.val (quadraturePoint j.val (16*i.val+v.val))))
    (hk : ∀ j i v, (k j i v).Contains
      (lambda (quadraturePoint j.val (16*i.val+v.val))*
      Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+v.val))*m)*
      (if b then Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+v.val)) else 1))) :
    (cachedMomentRuleBox c k).Contains (tableMomentRule a m (if b then 1 else 0)) := by
  apply cached_density_rule_contains_g hc
  intro j i v
  cases b
  · exact table_kernel_zero_contains (hk j i v)
  · exact table_kernel_one_contains (hk j i v)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical

namespace tm1_28_0
lemma checked : cachedMomentRuleBox density1 kernel28_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq_g]
  decide +kernel
lemma contains : ans.Contains (tableMomentRule true 28 0) := by
  rw [← checked]
  simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] using @tableRule_contains_bridge true 28 false density1 kernel28_0
    density1_contains_g kernel28_0_contains_g
lemma atomChecked : tableAtomBox true atomKernel28_0 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (tableMomentAtom true 28 0) := by
  rw [← atomChecked]
  exact tableAtomBox_contains true atomKernel28_0_contains
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma KContains : realAnswer.Contains (tableMomentK true 28 0) := by
  rw [← realChecked]
  exact tableMomentK_contains atomContains contains (by norm_num) (by norm_num)
end tm1_28_0

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_DataSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed and summable parts of cardinal data

Splitting cardinal data separates the fixed coefficients from the absolutely summable interpolation unknowns.
-/

namespace SharpPlanar
open MeasureTheory
lemma density_split (p : CardinalData) (j : ℕ) (t : ℝ) :
    density p j t = density (fixedPart p) j t+density (positiveData p.x) j t := by
  simp only [density,fixedPart,positiveData,lp.coeFn_zero,Pi.zero_apply,
    Complex.ofReal_zero,zero_mul,zero_add,tsum_zero,add_zero]
lemma K_split (p : CardinalData) (ell : ℕ) (s : ℝ) :
    K p ell s = K (fixedPart p) ell s+K (positiveData p.x) ell s := by
  have hp (j : ℕ) (hj : j<6) :
      (∫t in (j:ℝ)/6..((j:ℝ)+1)/6, density p j t*kernelMoment ell s t) =
      (∫t in (j:ℝ)/6..((j:ℝ)+1)/6, density (fixedPart p) j t*kernelMoment ell s t)+
      (∫t in (j:ℝ)/6..((j:ℝ)+1)/6, density (positiveData p.x) j t*kernelMoment ell s t) := by
    rw [← intervalIntegral.integral_add (piece_integrable _ ell j hj s) (piece_integrable _ ell j hj s)]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [density_split,add_mul]
  unfold K
  simp only [fixedPart,positiveData,Complex.ofReal_zero,zero_mul,zero_add]
  rw [← Complex.add_re,add_assoc,← Finset.sum_add_distrib]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  exact hp j (Finset.mem_range.mp hj)
lemma K_fixed₁ (x : X) (ell : ℕ) (s : ℝ) :
    K (fixed₁ x) ell s=K (fixed₁ 0) ell s+K (positiveData x) ell s := K_split _ _ _
lemma K_fixed₂ (x : X) (ell : ℕ) (s : ℝ) :
    K (fixed₂ x) ell s=K (fixed₂ 0) ell s+K (positiveData x) ell s := K_split _ _ _
lemma transformedJets_fixed₁ (x : X) (ni : Node×Bool) :
    transformedJets (fixed₁ x) ni=transformedJets (fixed₁ 0) ni + S x ni := by
  change _=transformedJets (fixed₁ 0) ni+Scoords x ni
  simp only [transformedJets,Scoords]
  split
  · rw [K_fixed₁ x 0 _,K_fixed₁ x 1 _]; ring
  · rw [K_fixed₁ x 0 _]; ring
lemma transformedJets_fixed₂ (x : X) (ni : Node×Bool) :
    transformedJets (fixed₂ x) ni=transformedJets (fixed₂ 0) ni + S x ni := by
  change _=transformedJets (fixed₂ 0) ni+Scoords x ni
  simp only [transformedJets,Scoords]
  split
  · rw [K_fixed₂ x 0 _,K_fixed₂ x 1 _]; ring
  · rw [K_fixed₂ x 0 _]; ring
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_ExactJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Jets of the exact cardinal interpolants

The exact interpolation equations give value and derivative contacts on the triangular shell radii.
-/

namespace SharpPlanar
lemma contactList_apply (n : Node) (d : Bool) :
    contactList (n,d)=if n.val=1 ∧ d=true then 1 else 0 := by
  classical
  unfold contactList columnVector
  rw [lp.single_apply]
  by_cases hn : n.val=1
  · have he : n=firstNode := Subtype.ext hn
    subst n
    cases d <;> simp [firstNode]
  · have he : n≠firstNode := by intro hh; exact hn (congrArg Subtype.val hh)
    simp [hn,he]
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar
open Numerical
lemma tableList_apply (a : Bool) (ni : Node×Bool) :
    tableList a ni = if ni.2 then (tableD a ni.1.val:ℝ) else (tableC a ni.1.val:ℝ) := rfl
lemma tableData_false : tableData false=fixed₁ (tableList false) := by
  simp [tableData,tableConstant,tableC,tableD,fixed₁]
lemma tableData_true : tableData true=fixed₂ (tableList true) := by
  simp [tableData,tableConstant,tableC,tableD,fixed₂]
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_ResidualBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Residuals of the cardinal interpolation equations

The finite coefficient families have small residuals in the exact interpolation equations.
-/

namespace SharpPlanar
open Numerical IntegerIntervals
lemma tableResidual_apply (a : Bool) (n : Node) (d : Bool) :
    tableResidual a (n,d)=
      (if d then (tableD a n.val:ℝ) else (tableC a n.val:ℝ))-
      transformedJets (tableData (!a)) (n,d)+
      (if a=false ∧ n.val=1 ∧ d=true then 1 else 0) := by
  cases a
  · have h := transformedJets_fixed₂ (tableList true) (n,d)
    rw [← tableData_true] at h
    change tableList false (n,d)-S (tableList true) (n,d)-
      (transformedJets (fixed₂ 0) (n,d)-contactList (n,d))=_
    rw [tableList_apply,contactList_apply]
    simp only [Bool.not_false,true_and]
    rw [h]
    ring
  · have h := transformedJets_fixed₁ (tableList false) (n,d)
    rw [← tableData_false] at h
    change tableList true (n,d)-S (tableList false) (n,d)-
      transformedJets (fixed₁ 0) (n,d)=_
    rw [tableList_apply]
    simp only [Bool.not_true,Bool.true_eq_false,false_and,ite_false, if_false,add_zero]
    rw [h]
    ring
lemma tableResidual_deriv (a : Bool) (n : Node) :
    tableResidual a (n,true)=(tableD a n.val:ℝ)+
      (if a=false ∧ n.val=1 then 1 else 0)+
      (tableMomentK (!a) n.val 1-D n.val*tableMomentK (!a) n.val 0)/(Q n.val) := by
  rw [tableResidual_apply]
  simp only [transformedJets,ite_true, if_true,and_true,tableMomentK_eq_g,
    Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one]
  ring
lemma RBox.abs_lt {a : RBox} {x : ℝ} {u v : ℤ} (hx : a.Contains x)
    (hv : 0<v) (hc : a.bound*v<precision*u) : |x|<(u:ℝ)/v := by
  have h1 := RBox.abs_bound_g hx
  have hv' : (0:ℝ)<v := by exact_mod_cast hv
  have h2 : (a.bound:ℝ)*v < (precision:ℝ)*u := by exact_mod_cast hc
  apply (mul_lt_mul_iff_right₀ precision_pos_g).mp
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ hv').mpr
  exact (mul_le_mul_of_nonneg_right h1 hv'.le).trans_lt h2
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Residual28
open IntegerIntervals IntegerBasis Numerical CachedData
lemma contains0_1 : box0_1.Contains (tableResidual false (node,true)) := by
  rw [tableResidual_deriv]
  have hv := RBox.contains_rat_g (-107613) 10000000000 (by norm_num)
  have hq := qiBox_contains_g 28 (by norm_num [residues])
  have hd := dBox_contains 28 (by norm_num [residues])
  have hh := RBox.contains_add_g hv (RBox.contains_mul_g (RBox.contains_add_g tm1_28_1.KContains_g (RBox.neg_contains_g (RBox.contains_mul_g hd tm1_28_0.KContains))) hq)
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [box0_1,node,tableC,tableD,tableRaw,div_eq_mul_inv,sub_eq_add_neg])
lemma bound0_1_g_oai : |tableResidual false (node,true)| < (1:ℝ)/10^9 := by
  simpa only [Int.cast_one,Int.cast_pow,Int.cast_ofNat] using RBox.abs_lt (u := 1) contains0_1 (by norm_num : (0:ℤ)<10^9) (by decide +kernel)
end SharpPlanar.Residual28

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Residual28.bound0_1_g_oai := @OAI.SharpPlanar.Residual28.bound0_1_g_oai
