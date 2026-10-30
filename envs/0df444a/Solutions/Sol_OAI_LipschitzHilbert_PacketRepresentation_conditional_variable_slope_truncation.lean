-- Prove2me | solution 1 for OAI.LipschitzHilbert.PacketRepresentation.conditional_variable_slope_truncation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:24:45.493985+00:00
-- url     : https://prove2.me/submissions/44591f64-efb7-4fcd-89af-9ec70d5d27c2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_LipschitzHilbert
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_PacketRepresentation_actual_sharp_band_measurable_restricted_log

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_IntGeometricSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric bound used on the two sides of a dyadic crossover. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem int_geometric_summable {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1) :
    Summable (fun k : ℤ => r^k.natAbs) := by
  have h := summable_geometric_of_abs_lt_one (r:=r) (by simpa only [abs_of_nonneg hr] using hr1)
  apply Summable.of_nat_of_neg
  · simpa only [Int.natAbs_natCast] using h
  · simpa only [Int.natAbs_neg,Int.natAbs_natCast] using h

theorem int_geometric_tsum_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1) :
    (∑' k : ℤ, r^k.natAbs)≤2/(1-r) := by
  have h := summable_geometric_of_abs_lt_one (r:=r) (by simpa only [abs_of_nonneg hr] using hr1)
  have hnat : Summable (fun n : ℕ => r^(n:ℤ).natAbs) := by simpa only [Int.natAbs_natCast] using h
  have hneg : Summable (fun n : ℕ => r^(-n:ℤ).natAbs) := by
    simpa only [Int.natAbs_neg,Int.natAbs_natCast] using h
  have heq : (∑' k : ℤ, r^k.natAbs)=(∑' n : ℕ, r^n)+(∑' n : ℕ, r^n)-1 := by
    simpa only [Int.natAbs_neg,Int.natAbs_natCast,Int.natAbs_zero,pow_zero] using
      (hnat.tsum_of_nat_of_neg (f:=fun k : ℤ => r^k.natAbs) hneg)
  rw [heq,tsum_geometric_of_abs_lt_one (r:=r)
    (by simpa only [abs_of_nonneg hr] using hr1),div_eq_mul_inv]
  linarith

theorem int_geometric_shift_sum_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1)
    (S : Finset ℤ) (a : ℤ) :
    (∑ k∈S, r^(k-a).natAbs)≤2/(1-r) := by
  classical
  have he : (∑ k∈S.image (fun k => k-a), r^k.natAbs)=∑ k∈S, r^(k-a).natAbs :=
    Finset.sum_image (g:=fun k : ℤ => k-a) (fun i _ j _ hij => by
      change i-a=j-a at hij
      omega)
  rw [←he]
  exact ((int_geometric_summable hr hr1).sum_le_tsum _ (fun k _ => pow_nonneg hr k.natAbs)).trans
    (int_geometric_tsum_le hr hr1)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeClassBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Amplitude levels of comparable support measure have a bounded
sum-to-energy ratio, independently of their number. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem amplitude_class_bound (S : Finset ℤ) (mass : ℤ → ℝ) (m : ℝ)
    (hlow : ∀ i∈S, m ≤ mass i) (hhigh : ∀ i∈S, mass i≤2*m) :
    (∑ i∈S, (2:ℝ)^i*Real.sqrt (mass i))≤
      4*Real.sqrt 2*Real.sqrt (∑ i∈S, ((2:ℝ)^i*Real.sqrt (mass i))^2) := by
  classical
  by_cases hS : S.Nonempty
  · let j := S.max' hS
    have hj : j∈S := Finset.max'_mem S hS
    have hgeom := int_geometric_shift_sum_le (r:=(1/2:ℝ)) (by norm_num) (by norm_num) S j
    have hp (i : ℤ) (hi : i∈S) : (2:ℝ)^i=(2:ℝ)^j*(1/2:ℝ)^(i-j).natAbs := by
      have hij : i≤j := Finset.le_max' S i hi
      have hn : ((i-j).natAbs:ℤ)=j-i := by omega
      have he : (1/2:ℝ)^(i-j).natAbs=(2:ℝ)^(-((i-j).natAbs:ℤ)) := by
        simp only [zpow_neg,zpow_natCast,one_div,inv_pow]
      rw [he,hn,←zpow_add₀ (by norm_num : (2:ℝ)≠0)]
      congr 1
      omega
    have hmass (i : ℤ) (hi : i∈S) : Real.sqrt (mass i)≤Real.sqrt 2*Real.sqrt (mass j) := by
      calc
        _ ≤ Real.sqrt (2*mass j) := Real.sqrt_le_sqrt ((hhigh i hi).trans (mul_le_mul_of_nonneg_left (hlow j hj) (by norm_num)))
        _ = _ := Real.sqrt_mul (by norm_num) _
    have hs : (∑ i∈S, (2:ℝ)^i*Real.sqrt (mass i))≤
        4*Real.sqrt 2*((2:ℝ)^j*Real.sqrt (mass j)) := by
      calc
        _ ≤ ∑ i∈S, ((2:ℝ)^j*(1/2:ℝ)^(i-j).natAbs)*(Real.sqrt 2*Real.sqrt (mass j)) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [hp i hi]
          exact mul_le_mul_of_nonneg_left (hmass i hi) (by positivity)
        _ = ((2:ℝ)^j*(Real.sqrt 2*Real.sqrt (mass j)))*(∑ i∈S, (1/2:ℝ)^(i-j).natAbs) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ ((2:ℝ)^j*(Real.sqrt 2*Real.sqrt (mass j)))*4 :=
          mul_le_mul_of_nonneg_left (by norm_num at hgeom ⊢; exact hgeom) (by positivity)
        _ = _ := by ring
    have hterm : (2:ℝ)^j*Real.sqrt (mass j)≤
        Real.sqrt (∑ i∈S, ((2:ℝ)^i*Real.sqrt (mass i))^2) := by
      apply Real.le_sqrt_of_sq_le
      exact Finset.single_le_sum (fun i _ => sq_nonneg ((2:ℝ)^i*Real.sqrt (mass i))) hj
    exact hs.trans (mul_le_mul_of_nonneg_left hterm (by positivity))
  · have hz : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [hz,Finset.sum_empty,Real.sqrt_zero,mul_zero,le_refl]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteClassRegroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact regrouping of the two amplitude indices by support-measure
class, with every original summand retained. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem finite_class_weighted_sum {ι κ : Type*} [DecidableEq κ]
    (I : Finset ι) (classify : ι → κ) (a : ι → ℝ) (w : κ → ℝ) :
    (∑ k∈I.image classify, w k*(∑ i∈I.filter (fun i => classify i=k), a i))=
      ∑ i∈I, w (classify i)*a i := by
  calc
    _ = ∑ k∈I.image classify, ∑ i∈I.filter (fun i => classify i=k), w (classify i)*a i := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem classify hi) _

theorem finite_class_bilinear_sum {ι κ α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset ι) (J : Finset κ) (ci : ι → α) (cj : κ → β)
    (a : ι → ℝ) (b : κ → ℝ) (K : α → β → ℝ) :
    (∑ k∈I.image ci, ∑ l∈J.image cj,
      K k l*(∑ i∈I.filter (fun i => ci i=k), a i)*(∑ j∈J.filter (fun j => cj j=l), b j))=
    ∑ i∈I, ∑ j∈J, K (ci i) (cj j)*a i*b j := by
  calc
    _ = ∑ k∈I.image ci, ∑ j∈J, K k (cj j)*(∑ i∈I.filter (fun i => ci i=k), a i)*b j := by
      apply Finset.sum_congr rfl
      intro k _
      exact finite_class_weighted_sum J cj b (fun l => K k l*(∑ i∈I.filter (fun i => ci i=k), a i))
    _ = ∑ j∈J, ∑ k∈I.image ci, K k (cj j)*(∑ i∈I.filter (fun i => ci i=k), a i)*b j := Finset.sum_comm
    _ = ∑ j∈J, ∑ i∈I, K (ci i) (cj j)*a i*b j := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = (∑ k∈I.image ci, K k (cj j)*(∑ i∈I.filter (fun i => ci i=k), a i))*b j :=
          (Finset.sum_mul ..).symm
        _ = (∑ i∈I, K (ci i) (cj j)*a i)*b j := by
          rw [finite_class_weighted_sum I ci a (fun k => K k (cj j))]
        _ = _ := Finset.sum_mul ..
    _ = _ := Finset.sum_comm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteSchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Schur estimate used to sum the measure classes in the
restricted-to-strong argument. No factor depends on the index counts. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem finite_schur_bound {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (K : ι → κ → ℝ) (a : ι → ℝ) (b : κ → ℝ) (M : ℝ)
    (hM : 0≤M) (hK : ∀ i∈I, ∀ j∈J, 0≤K i j)
    (ha : ∀ i∈I, 0≤a i) (hb : ∀ j∈J, 0≤b j)
    (hrow : ∀ i∈I, (∑ j∈J, K i j)≤M)
    (hcol : ∀ j∈J, (∑ i∈I, K i j)≤M) :
    (∑ i∈I, ∑ j∈J, K i j*a i*b j)≤
      M*Real.sqrt (∑ i∈I, (a i)^2)*Real.sqrt (∑ j∈J, (b j)^2) := by
  classical
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (I×ˢJ)
    (r:=fun p => K p.1 p.2*a p.1*b p.2)
    (f:=fun p => K p.1 p.2*(a p.1)^2)
    (g:=fun p => K p.1 p.2*(b p.2)^2)
    (fun p hp => mul_nonneg (hK p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2) (sq_nonneg _))
    (fun p hp => mul_nonneg (hK p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2) (sq_nonneg _))
    (fun p _ => by ring_nf; exact le_rfl)
  simp only [Finset.sum_product] at hs
  have hleft : (∑ i∈I, ∑ j∈J, K i j*(a i)^2)≤M*(∑ i∈I, (a i)^2) := by
    calc
      _ = ∑ i∈I, (∑ j∈J, K i j)*(a i)^2 := by simp only [Finset.sum_mul]
      _ ≤ ∑ i∈I, M*(a i)^2 := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (hrow i hi) (sq_nonneg _))
      _ = _ := (Finset.mul_sum ..).symm
  have hright : (∑ i∈I, ∑ j∈J, K i j*(b j)^2)≤M*(∑ j∈J, (b j)^2) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ j∈J, (∑ i∈I, K i j)*(b j)^2 := by simp only [Finset.sum_mul]
      _ ≤ ∑ j∈J, M*(b j)^2 := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right (hcol j hj) (sq_nonneg _))
      _ = _ := (Finset.mul_sum ..).symm
  have hleft0 : 0≤∑ i∈I, ∑ j∈J, K i j*(a i)^2 :=
    Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => mul_nonneg (hK i hi j hj) (sq_nonneg _)))
  have hright0 : 0≤∑ i∈I, ∑ j∈J, K i j*(b j)^2 :=
    Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => mul_nonneg (hK i hi j hj) (sq_nonneg _)))
  have hsq := hs.trans (mul_le_mul hleft hright hright0 (hleft0.trans hleft))
  have hS0 : 0≤∑ i∈I, ∑ j∈J, K i j*a i*b j :=
    Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => mul_nonneg (mul_nonneg (hK i hi j hj) (ha i hi)) (hb j hj)))
  have htarget : 0≤M*Real.sqrt (∑ i∈I, (a i)^2)*Real.sqrt (∑ j∈J, (b j)^2) := by positivity
  apply (sq_le_sq₀ hS0 htarget).mp
  calc
    _ ≤ (M*(∑ i∈I, (a i)^2))*(M*(∑ j∈J, (b j)^2)) := hsq
    _ = _ := by rw [mul_pow,mul_pow,Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
      Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_MeasureClassKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable cubic separation of dyadic measure classes, with a finite
convolution bound uniform in the number and range of classes. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem measureClassKernel_nonneg (k : ℤ) : 0 ≤ measureClassKernel k := by
  unfold measureClassKernel
  positivity

theorem measureClassKernel_neg (k : ℤ) : measureClassKernel (-k)=measureClassKernel k := by
  simp only [measureClassKernel,Int.natAbs_neg]

theorem measureClassKernel_summable : Summable measureClassKernel := by
  have h : Summable (fun n : ℕ => ((n:ℝ)^3)⁻¹) := Real.summable_nat_pow_inv.mpr (by norm_num)
  have hs : Summable (fun n : ℕ => (((n:ℝ)+1)^3)⁻¹) := by
    simpa only [Function.comp_def,Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one] using h.comp_injective Nat.succ_injective
  apply Summable.of_nat_of_neg
  · simpa only [measureClassKernel,Int.natAbs_natCast] using hs
  · simpa only [measureClassKernel,Int.natAbs_neg,Int.natAbs_natCast] using hs

theorem measureClassKernel_shift_sum_le (S : Finset ℤ) (a : ℤ) :
    (∑ k∈S, measureClassKernel (k-a))≤∑' k, measureClassKernel k := by
  classical
  have he : (∑ k∈S.image (fun k => k-a), measureClassKernel k)=
      ∑ k∈S, measureClassKernel (k-a) :=
    Finset.sum_image (g:=fun k : ℤ => k-a) (fun i _ j _ hij => by
      change i-a=j-a at hij
      omega)
  rw [←he]
  exact measureClassKernel_summable.sum_le_tsum _ (fun k _ => measureClassKernel_nonneg k)

theorem measure_class_convolution_bound (I J : Finset ℤ) (a b : ℤ → ℝ)
    (ha : ∀ i∈I, 0≤a i) (hb : ∀ j∈J, 0≤b j) :
    (∑ i∈I, ∑ j∈J, measureClassKernel (i-j)*a i*b j)≤
      (∑' k, measureClassKernel k)*Real.sqrt (∑ i∈I, (a i)^2)*Real.sqrt (∑ j∈J, (b j)^2) := by
  apply finite_schur_bound I J (fun i j => measureClassKernel (i-j)) a b _
    (tsum_nonneg measureClassKernel_nonneg) (fun i _ j _ => measureClassKernel_nonneg (i-j)) ha hb
  · intro i _
    have he (j : ℤ) : measureClassKernel (i-j)=measureClassKernel (j-i) := by
      rw [show i-j=-(j-i) by omega,measureClassKernel_neg]
    simp_rw [he]
    exact measureClassKernel_shift_sum_le J i
  · intro j _
    exact measureClassKernel_shift_sum_le I j

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MeasureClassLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic restricted estimate is dominated by the summable
kernel of the actual dyadic support-measure classes. -/
noncomputable section
namespace LipschitzHilbert

theorem measure_class_log_bound (m n : ℝ) (i j : ℤ)
    (hm : 0 < m) (hn : 0<n)
    (hml : (2:ℝ)^i ≤ m) (hmu : m≤(2:ℝ)^(i+1))
    (hnl : (2:ℝ)^j≤n) (hnu : n≤(2:ℝ)^(j+1)) :
    ((1+|Real.log (m/n)|)^3)⁻¹ ≤ measureClassLogConstant*measureClassKernel (i-j) := by
  have hc : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hmlog := Real.log_le_log (zpow_pos (by norm_num : (0:ℝ)<2) i) hml
  have hmulog := Real.log_le_log hm hmu
  have hnlog := Real.log_le_log (zpow_pos (by norm_num : (0:ℝ)<2) j) hnl
  have hnulog := Real.log_le_log hn hnu
  simp only [Real.log_zpow,Int.cast_add,Int.cast_one] at hmlog hmulog hnlog hnulog
  have habs : |((i:ℝ)-(j:ℝ))*Real.log 2|≤|Real.log m-Real.log n|+Real.log 2 := by
    apply abs_le.mpr
    constructor
    · nlinarith only [hmulog,hnlog,neg_abs_le (Real.log m-Real.log n)]
    · nlinarith only [hmlog,hnulog,le_abs_self (Real.log m-Real.log n)]
  rw [abs_mul,abs_of_pos hc,←Real.log_div hm.ne' hn.ne'] at habs
  have hcinv : Real.log 2*(1/Real.log 2)=1 := by field_simp
  have hC : 0<2+1/Real.log 2 := by positivity
  have hdenom : 1+|(i:ℝ)-(j:ℝ)|≤(2+1/Real.log 2)*(1+|Real.log (m/n)|) := by
    apply (mul_le_mul_iff_right₀ hc).mp
    have hnonneg := mul_nonneg hc.le (abs_nonneg (Real.log (m/n)))
    nlinarith only [habs,hcinv,hnonneg,abs_nonneg (Real.log (m/n))]
  have hnat : (Int.natAbs (i-j):ℝ)=|(i:ℝ)-(j:ℝ)| := by
    rw [Nat.cast_natAbs,Int.cast_abs,Int.cast_sub]
  have hpow := pow_le_pow_left₀ (by positivity : 0≤1+|(i:ℝ)-(j:ℝ)|) hdenom 3
  have hd : 0<(1+|Real.log (m/n)|)^3 := by positivity
  have hk : 0<(1+|(i:ℝ)-(j:ℝ)|)^3 := by positivity
  have hdiv : 1/(1+|Real.log (m/n)|)^3≤(2+1/Real.log 2)^3/(1+|(i:ℝ)-(j:ℝ)|)^3 := by
    apply (div_le_div_iff₀ hd hk).mpr
    simpa only [one_mul,mul_pow] using hpow
  simpa only [measureClassLogConstant,measureClassKernel,hnat,add_comm,div_eq_mul_inv,one_mul] using hdiv

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteLogAmplitudeSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical core of the restricted-to-strong lemma: logarithmic
decay sums over finitely many amplitude levels with a uniform constant. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem finite_log_amplitude_sum (I J : Finset ℤ) (m n : ℤ → ℝ) (ci cj : ℤ → ℤ)
    (hm : ∀ i∈I, 0 < m i) (hn : ∀ j∈J, 0<n j)
    (hml : ∀ i∈I, (2:ℝ)^(ci i) ≤ m i) (hmu : ∀ i∈I, m i≤(2:ℝ)^(ci i+1))
    (hnl : ∀ j∈J, (2:ℝ)^(cj j)≤n j) (hnu : ∀ j∈J, n j≤(2:ℝ)^(cj j+1)) :
    (∑ i∈I, ∑ j∈J, ((1+|Real.log (m i/n j)|)^3)⁻¹*
      ((2:ℝ)^i*Real.sqrt (m i))*((2:ℝ)^j*Real.sqrt (n j)))≤
    (32*measureClassLogConstant*(∑' k, measureClassKernel k))*
      Real.sqrt (∑ i∈I, ((2:ℝ)^i*Real.sqrt (m i))^2)*
      Real.sqrt (∑ j∈J, ((2:ℝ)^j*Real.sqrt (n j))^2) := by
  classical
  let a := fun i : ℤ => (2:ℝ)^i*Real.sqrt (m i)
  let b := fun j : ℤ => (2:ℝ)^j*Real.sqrt (n j)
  let A := fun k : ℤ => ∑ i∈I.filter (fun i => ci i=k), a i
  let B := fun l : ℤ => ∑ j∈J.filter (fun j => cj j=l), b j
  let E := fun k : ℤ => ∑ i∈I.filter (fun i => ci i=k), (a i)^2
  let F := fun l : ℤ => ∑ j∈J.filter (fun j => cj j=l), (b j)^2
  have hA (k : ℤ) : A k≤4*Real.sqrt 2*Real.sqrt (E k) := by
    apply amplitude_class_bound (I.filter (fun i => ci i=k)) m ((2:ℝ)^k)
    · intro i hi
      obtain ⟨hi,he⟩ := Finset.mem_filter.mp hi
      simpa only [he] using hml i hi
    · intro i hi
      obtain ⟨hi,he⟩ := Finset.mem_filter.mp hi
      calc
        _ ≤ (2:ℝ)^(k+1) := by simpa only [he] using hmu i hi
        _ = 2*(2:ℝ)^k := by rw [zpow_add₀ (by norm_num : (2:ℝ)≠0)]; norm_num; ring
  have hB (l : ℤ) : B l≤4*Real.sqrt 2*Real.sqrt (F l) := by
    apply amplitude_class_bound (J.filter (fun j => cj j=l)) n ((2:ℝ)^l)
    · intro j hj
      obtain ⟨hj,he⟩ := Finset.mem_filter.mp hj
      simpa only [he] using hnl j hj
    · intro j hj
      obtain ⟨hj,he⟩ := Finset.mem_filter.mp hj
      calc
        _ ≤ (2:ℝ)^(l+1) := by simpa only [he] using hnu j hj
        _ = 2*(2:ℝ)^l := by rw [zpow_add₀ (by norm_num : (2:ℝ)≠0)]; norm_num; ring
  have hA0 (k : ℤ) : 0≤A k := Finset.sum_nonneg (fun i _ => by dsimp only [a]; positivity)
  have hB0 (l : ℤ) : 0≤B l := Finset.sum_nonneg (fun j _ => by dsimp only [b]; positivity)
  have hclasses : (∑ k∈I.image ci, ∑ l∈J.image cj, measureClassKernel (k-l)*A k*B l)≤
      32*(∑' k, measureClassKernel k)*Real.sqrt (∑ i∈I, (a i)^2)*Real.sqrt (∑ j∈J, (b j)^2) := by
    have hdom (k l : ℤ) : measureClassKernel (k-l)*A k*B l≤
        32*(measureClassKernel (k-l)*Real.sqrt (E k)*Real.sqrt (F l)) := by
      calc
        _ ≤ measureClassKernel (k-l)*(4*Real.sqrt 2*Real.sqrt (E k))*(4*Real.sqrt 2*Real.sqrt (F l)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (hA k) (measureClassKernel_nonneg _)) (hB l)
            (hB0 l) (mul_nonneg (measureClassKernel_nonneg _) (by positivity))
        _ = 16*(Real.sqrt 2)^2*(measureClassKernel (k-l)*Real.sqrt (E k)*Real.sqrt (F l)) := by ring
        _ = _ := by rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]; ring
    have hE : (∑ k∈I.image ci, E k)=∑ i∈I, (a i)^2 :=
      Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem ci hi) (fun i => (a i)^2)
    have hF : (∑ l∈J.image cj, F l)=∑ j∈J, (b j)^2 :=
      Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem cj hj) (fun j => (b j)^2)
    calc
      _ ≤ ∑ k∈I.image ci, ∑ l∈J.image cj, 32*(measureClassKernel (k-l)*Real.sqrt (E k)*Real.sqrt (F l)) :=
        Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => hdom k l))
      _ = 32*(∑ k∈I.image ci, ∑ l∈J.image cj, measureClassKernel (k-l)*Real.sqrt (E k)*Real.sqrt (F l)) := by
        simp only [Finset.mul_sum]
      _ ≤ 32*((∑' k, measureClassKernel k)*Real.sqrt (∑ k∈I.image ci, (Real.sqrt (E k))^2)*
          Real.sqrt (∑ l∈J.image cj, (Real.sqrt (F l))^2)) :=
        mul_le_mul_of_nonneg_left (measure_class_convolution_bound (I.image ci) (J.image cj)
          (fun k => Real.sqrt (E k)) (fun l => Real.sqrt (F l))
          (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _)) (by norm_num)
      _ = _ := by
        have he (k : ℤ) : (Real.sqrt (E k))^2=E k := Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        have hf (l : ℤ) : (Real.sqrt (F l))^2=F l := Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        simp_rw [he,hf,hE,hF]
        ring
  calc
    _ ≤ ∑ i∈I, ∑ j∈J, (measureClassLogConstant*measureClassKernel (ci i-cj j))*a i*b j := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (measure_class_log_bound (m i) (n j) (ci i) (cj j) (hm i hi) (hn j hj)
          (hml i hi) (hmu i hi) (hnl j hj) (hnu j hj)) (by positivity))
        (by positivity)
    _ = measureClassLogConstant*(∑ k∈I.image ci, ∑ l∈J.image cj, measureClassKernel (k-l)*A k*B l) := by
      rw [finite_class_bilinear_sum I J ci cj a b (fun k l => measureClassKernel (k-l))]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ measureClassLogConstant*(32*(∑' k, measureClassKernel k)*
        Real.sqrt (∑ i∈I, (a i)^2)*Real.sqrt (∑ j∈J, (b j)^2)) :=
      mul_le_mul_of_nonneg_left hclasses (by dsimp only [measureClassLogConstant]; positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_DyadicMeasureClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The support-measure class is chosen from the actual positive
measure by the integer floor of its base-two logarithm. -/
noncomputable section
namespace LipschitzHilbert

theorem dyadicMeasureClass_bounds {m : ℝ} (hm : 0 < m) :
    (2:ℝ)^(dyadicMeasureClass m) ≤ m ∧ m<(2:ℝ)^(dyadicMeasureClass m+1) := by
  have hc : 0<Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · apply (Real.log_le_log_iff (zpow_pos (by norm_num) _) hm).mp
    rw [Real.log_zpow]
    exact (le_div_iff₀ hc).mp (Int.floor_le _)
  · apply (Real.log_lt_log_iff hm (zpow_pos (by norm_num) _)).mp
    rw [Real.log_zpow,Int.cast_add,Int.cast_one]
    exact (div_lt_iff₀ hc).mp (Int.lt_floor_add_one _)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteRestrictedStrong
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-amplitude restricted-to-strong estimate from Section 2.
The matrix entries are the restricted bilinear pairings. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem restrictedStrongConstant_pos : 0 < restrictedStrongConstant := by
  have hK : 0≤∑' k, measureClassKernel k := tsum_nonneg measureClassKernel_nonneg
  have hC : 0 ≤ measureClassLogConstant := by unfold measureClassLogConstant; positivity
  unfold restrictedStrongConstant
  positivity

theorem finite_restricted_strong (I J : Finset ℤ) (m n : ℤ → ℝ)
    (B : ℤ → ℤ → ℂ) (C : ℝ) (hC : 0≤C)
    (hm : ∀ i∈I, 0 < m i) (hn : ∀ j∈J, 0<n j)
    (hB : ∀ i∈I, ∀ j∈J, ‖B i j‖≤
      C*((1+|Real.log (m i/n j)|)^3)⁻¹*Real.sqrt (m i)*Real.sqrt (n j)) :
    ‖∑ i∈I, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) • B i j‖≤
      C*restrictedStrongConstant*
        Real.sqrt (∑ i∈I, ((2:ℝ)^i*Real.sqrt (m i))^2)*
        Real.sqrt (∑ j∈J, ((2:ℝ)^j*Real.sqrt (n j))^2) := by
  have hnum := finite_log_amplitude_sum I J m n
    (fun i => dyadicMeasureClass (m i)) (fun j => dyadicMeasureClass (n j)) hm hn
    (fun i hi => (dyadicMeasureClass_bounds (hm i hi)).1)
    (fun i hi => (dyadicMeasureClass_bounds (hm i hi)).2.le)
    (fun j hj => (dyadicMeasureClass_bounds (hn j hj)).1)
    (fun j hj => (dyadicMeasureClass_bounds (hn j hj)).2.le)
  have hmajor : ‖∑ i∈I, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) • B i j‖≤
      C*(∑ i∈I, ∑ j∈J, ((1+|Real.log (m i/n j)|)^3)⁻¹*
        ((2:ℝ)^i*Real.sqrt (m i))*((2:ℝ)^j*Real.sqrt (n j))) := by
    calc
      _ ≤ ∑ i∈I, ‖∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) • B i j‖ := norm_sum_le _ _
      _ ≤ ∑ i∈I, ∑ j∈J, ‖((2:ℝ)^i*(2:ℝ)^j) • B i j‖ :=
        Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
      _ ≤ ∑ i∈I, ∑ j∈J, C*(((1+|Real.log (m i/n j)|)^3)⁻¹*
          ((2:ℝ)^i*Real.sqrt (m i))*((2:ℝ)^j*Real.sqrt (n j))) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_smul,Real.norm_of_nonneg (by positivity : 0≤(2:ℝ)^i*(2:ℝ)^j)]
        calc
          _ ≤ ((2:ℝ)^i*(2:ℝ)^j)*
              (C*((1+|Real.log (m i/n j)|)^3)⁻¹*Real.sqrt (m i)*Real.sqrt (n j)) :=
            mul_le_mul_of_nonneg_left (hB i hi j hj) (by positivity)
          _ = _ := by ring
      _ = _ := by simp only [Finset.mul_sum]
  apply hmajor.trans
  calc
    _ ≤ C*((32*measureClassLogConstant*(∑' k, measureClassKernel k))*
        Real.sqrt (∑ i∈I, ((2:ℝ)^i*Real.sqrt (m i))^2)*
        Real.sqrt (∑ j∈J, ((2:ℝ)^j*Real.sqrt (n j))^2)) :=
      mul_le_mul_of_nonneg_left hnum hC
    _ ≤ C*restrictedStrongConstant*
        Real.sqrt (∑ i∈I, ((2:ℝ)^i*Real.sqrt (m i))^2)*
        Real.sqrt (∑ j∈J, ((2:ℝ)^j*Real.sqrt (n j))^2) := by
      dsimp only [restrictedStrongConstant]
      nlinarith only [mul_nonneg hC (mul_nonneg
        (Real.sqrt_nonneg (∑ i∈I, ((2:ℝ)^i*Real.sqrt (m i))^2))
        (Real.sqrt_nonneg (∑ j∈J, ((2:ℝ)^j*Real.sqrt (n j))^2)))]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual disjoint amplitude levels and their square-energy budget. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

theorem amplitudeLevel_finite (μ : Measure X) {f : X → E} (hf : MemLp f 2 μ) (i : ℤ) :
    μ (amplitudeLevel f i)≠∞ := by
  let eps : ℝ≥0 := ⟨(2:ℝ)^(i-1),(zpow_pos (by norm_num) _).le⟩
  have heps : eps≠0 := by
    intro h
    have := congrArg (fun t : ℝ≥0 => (t:ℝ)) h
    exact (zpow_pos (by norm_num : (0:ℝ)<2) (i-1)).ne' this
  have h := hf.meas_ge_lt_top (by norm_num) (by norm_num) heps
  apply ne_top_of_le_ne_top h.ne (measure_mono ?_)
  intro x hx
  exact_mod_cast hx.1.le

theorem amplitude_energy_budget (μ : Measure X) {f : X → E}
    (hf : MemLp f 2 μ) (hm : Measurable (fun x => ‖f x‖)) (I : Finset ℤ) :
    (∑ i∈I, ((2:ℝ)^i*Real.sqrt (μ.real (amplitudeLevel f i)))^2)≤
      4*(∫ x, ‖f x‖^2 ∂μ) := by
  have hsq := hf.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hlevel (i : ℤ) : (2:ℝ)^(2*i)*μ.real (amplitudeLevel f i)≤
      4*(∫ x in amplitudeLevel f i, ‖f x‖^2 ∂μ) := by
    have hp : (2:ℝ)^i=2*(2:ℝ)^(i-1) := by
      rw [show i=(i-1)+1 by omega,zpow_add₀ (by norm_num : (2:ℝ)≠0)]
      norm_num
      ring
    have hbound : (∫ _ in amplitudeLevel f i, ((2:ℝ)^i)^2/4 ∂μ)≤
        ∫ x in amplitudeLevel f i, ‖f x‖^2 ∂μ := by
      apply setIntegral_mono_on
        (integrableOn_const (amplitudeLevel_finite μ hf i)) hsq.integrableOn (amplitudeLevel_measurable hm i)
      intro x hx
      have hn : 0<(2:ℝ)^(i-1) := zpow_pos (by norm_num) _
      have hs := sq_le_sq₀ hn.le (norm_nonneg (f x)) |>.2 hx.1.le
      rw [hp]
      nlinarith only [hs]
    rw [setIntegral_const,smul_eq_mul] at hbound
    have he : (2:ℝ)^(2*i)=((2:ℝ)^i)^2 := by rw [mul_comm (2:ℤ) i,zpow_mul]; norm_num
    rw [he]
    nlinarith only [hbound]
  calc
    _ = ∑ i∈I, (2:ℝ)^(2*i)*μ.real (amplitudeLevel f i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow,Real.sq_sqrt measureReal_nonneg]
      congr 1
      rw [mul_comm (2:ℤ) i,zpow_mul]
      norm_num
    _ ≤ ∑ i∈I, 4*(∫ x in amplitudeLevel f i, ‖f x‖^2 ∂μ) := Finset.sum_le_sum (fun i _ => hlevel i)
    _ = 4*(∫ x in ⋃ i∈I, amplitudeLevel f i, ‖f x‖^2 ∂μ) := by
      rw [←Finset.mul_sum,integral_biUnion_finset I (fun i _ => amplitudeLevel_measurable hm i)
        (fun i _ j _ hij => amplitudeLevel_disjoint f hij) (fun _ _ => hsq.integrableOn)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (setIntegral_le_integral hsq
      (Filter.Eventually.of_forall (fun x => sq_nonneg ‖f x‖))) (by norm_num)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RestrictedStrongForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restricted-to-strong estimate for the actual finite amplitude
approximations of Hilbert-valued functions. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem amplitudePiece_measurable {f : X → EuclideanSpace ℂ κ} (hf : Measurable f) (i : ℤ) :
    Measurable (amplitudePiece f i) :=
  measurable_const.smul (hf.indicator (amplitudeLevel_measurable hf.norm i))

omit [MeasurableSpace X] in
theorem amplitudePiece_bounded (f : X → EuclideanSpace ℂ κ) (i : ℤ) (x : X) :
    ‖amplitudePiece f i x‖≤1 := by
  by_cases hx : x∈amplitudeLevel f i
  · change ‖(2:ℝ)^(-i) • (amplitudeLevel f i).indicator f x‖≤1
    rw [Set.indicator_of_mem hx,norm_smul,Real.norm_of_nonneg (zpow_pos (by norm_num) _).le]
    calc
      _ ≤ (2:ℝ)^(-i)*(2:ℝ)^i := mul_le_mul_of_nonneg_left hx.2 (zpow_pos (by norm_num) _).le
      _ = _ := by rw [←zpow_add₀ (by norm_num : (2:ℝ)≠0)]; simp
  · simp only [amplitudePiece,Pi.smul_apply,Set.indicator_of_notMem hx,smul_zero,norm_zero,zero_le_one]

omit [MeasurableSpace X] in
theorem amplitudePiece_supported (f : X → EuclideanSpace ℂ κ) (i : ℤ) (x : X)
    (hx : x∉amplitudeLevel f i) : amplitudePiece f i x=0 := by
  simp only [amplitudePiece,Pi.smul_apply,Set.indicator_of_notMem hx,smul_zero]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite amplitude approximations converge in squared L2 energy.
The cutoff is the actual disjoint union of its amplitude levels. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem amplitudeApprox_measurable {f : X → EuclideanSpace ℂ κ} (hf : Measurable f) (I : Finset ℤ) :
    Measurable (amplitudeApprox f I) := by
  rw [amplitudeApprox_eq_indicator]
  exact hf.indicator (Finset.measurableSet_biUnion _ (fun i _ => amplitudeLevel_measurable hf.norm i))

omit [MeasurableSpace X] in
theorem amplitudeApprox_sub_norm_le (f : X → EuclideanSpace ℂ κ) (I : Finset ℤ) (x : X) :
    ‖amplitudeApprox f I x-f x‖≤‖f x‖ := by
  rw [amplitudeApprox_eq_indicator]
  by_cases hx : x∈⋃ i∈I, amplitudeLevel f i
  · simp only [Set.indicator_of_mem hx,sub_self,norm_zero,norm_nonneg]
  · simp only [Set.indicator_of_notMem hx,zero_sub,norm_neg,le_refl]

omit [MeasurableSpace X] in
theorem amplitudeApprox_eventually_eq (f : X → EuclideanSpace ℂ κ) (x : X) :
    ∀ᶠ n : ℕ in atTop, amplitudeApprox f (Finset.Icc (-(n:ℤ)) n) x=f x := by
  by_cases hx : f x=0
  · filter_upwards [] with n
    rw [amplitudeApprox_eq_indicator]
    by_cases hm : x∈⋃ i∈Finset.Icc (-(n:ℤ)) n, amplitudeLevel f i
    · rw [Set.indicator_of_mem hm]
    · rw [Set.indicator_of_notMem hm,hx]
  · obtain ⟨i,hi⟩ := exists_mem_Ioc_zpow (norm_pos_iff.mpr hx) (by norm_num : (1:ℝ)<2)
    have hlevel : x∈amplitudeLevel f (i+1) := by
      change (2:ℝ)^(i+1-1)<‖f x‖ ∧ ‖f x‖≤(2:ℝ)^(i+1)
      simpa only [Set.mem_Ioc,add_sub_cancel_right] using hi
    filter_upwards [eventually_ge_atTop (i+1).natAbs] with n hn
    rw [amplitudeApprox_eq_indicator,Set.indicator_of_mem]
    exact Set.mem_iUnion.mpr ⟨i+1,Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr (by omega),hlevel⟩⟩

theorem amplitudeApprox_energy_tendsto (μ : Measure X) {f : X → EuclideanSpace ℂ κ}
    (hf : Measurable f) (hf2 : MemLp f 2 μ) :
    Tendsto (fun n : ℕ => ∫ x, ‖amplitudeApprox f (Finset.Icc (-(n:ℤ)) n) x-f x‖^2 ∂μ)
      atTop (𝓝 0) := by
  have hdom := hf2.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have h := tendsto_integral_of_dominated_convergence (μ:=μ) (fun x => ‖f x‖^2)
    (F:=fun n x => ‖amplitudeApprox f (Finset.Icc (-(n:ℤ)) n) x-f x‖^2) (f:=fun _ => (0:ℝ))
    (fun n => (((amplitudeApprox_measurable hf _).sub hf).norm.pow_const 2).aestronglyMeasurable)
    hdom
    (fun n => Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (amplitudeApprox_sub_norm_le f _ x) 2))
    (Filter.Eventually.of_forall (fun x => by
      apply tendsto_const_nhds.congr'
      filter_upwards [amplitudeApprox_eventually_eq f x] with n hn
      simp only [hn,sub_self,norm_zero,zero_pow (by decide : 2≠0)]))
  simpa only [integral_zero] using h

theorem amplitudeApprox_Lp_tendsto (μ : Measure X) {f : X → EuclideanSpace ℂ κ}
    (hf : Measurable f) (hf2 : MemLp f 2 μ) :
    Tendsto (fun n : ℕ => (amplitudeApprox_memLp μ hf hf2 (Finset.Icc (-(n:ℤ)) n)).toLp
      (amplitudeApprox f (Finset.Icc (-(n:ℤ)) n))) atTop (𝓝 (hf2.toLp f)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n : ℕ => amplitudeApprox f (Finset.Icc (-(n:ℤ)) n))
    (fun n => amplitudeApprox_memLp μ hf hf2 (Finset.Icc (-(n:ℤ)) n)) f hf2).mpr
  have he (n : ℕ) : eLpNorm (amplitudeApprox f (Finset.Icc (-(n:ℤ)) n)-f) 2 μ=
      ENNReal.ofReal (Real.sqrt (∫ x, ‖amplitudeApprox f (Finset.Icc (-(n:ℤ)) n) x-f x‖^2 ∂μ)) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      ((amplitudeApprox_memLp μ hf hf2 (Finset.Icc (-(n:ℤ)) n)).sub hf2)]
    norm_num [Real.sqrt_eq_rpow]
  simp_rw [he]
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_sqrt.continuousAt.tendsto.comp (amplitudeApprox_energy_tendsto μ hf hf2))
  simpa only [Function.comp_def,Real.sqrt_zero,ENNReal.ofReal_zero] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same normalized amplitude pieces in the actual L2 quotient,
including null levels and exact finite reconstruction. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem amplitudeLpPiece_zero (μ : Measure X) {f : X → EuclideanSpace ℂ κ}
    (hf : Measurable f) (hf2 : MemLp f 2 μ) (i : ℤ)
    (hzero : μ.real (amplitudeLevel f i)=0) : amplitudeLpPiece μ hf hf2 i=0 := by
  have hμ : μ (amplitudeLevel f i)=0 :=
    (measureReal_eq_zero_iff (amplitudeLevel_finite μ hf2 i)).mp hzero
  have ha : amplitudePiece f i=ᵐ[μ] 0 := by
    apply ae_iff.mpr
    apply measure_mono_null (t:=amplitudeLevel f i) ?_ hμ
    intro x hx
    by_contra hn
    exact hx (amplitudePiece_supported f i x hn)
  exact ((amplitudePiece_memLp μ hf hf2 i).toLp_congr (MemLp.zero) ha).trans (MemLp.toLp_zero _)

theorem amplitudeApprox_toLp (μ : Measure X) {f : X → EuclideanSpace ℂ κ}
    (hf : Measurable f) (hf2 : MemLp f 2 μ) (I : Finset ℤ) :
    (amplitudeApprox_memLp μ hf hf2 I).toLp (amplitudeApprox f I)=
      ∑ i∈I, (2:ℝ)^i • amplitudeLpPiece μ hf hf2 i := by
  apply Lp.ext
  have hi (i : ℤ) : ((2:ℝ)^i • amplitudeLpPiece μ hf hf2 i : Lp (EuclideanSpace ℂ κ) 2 μ)=ᵐ[μ]
      (2:ℝ)^i • amplitudePiece f i :=
    (Lp.coeFn_smul _ _).trans ((amplitudePiece_memLp μ hf hf2 i).coeFn_toLp.fun_comp
      (fun y => (2:ℝ)^i • y))
  calc
    _ =ᵐ[μ] amplitudeApprox f I := (amplitudeApprox_memLp μ hf hf2 I).coeFn_toLp
    _ =ᵐ[μ] ∑ i∈I, ((2:ℝ)^i • amplitudeLpPiece μ hf hf2 i : Lp (EuclideanSpace ℂ κ) 2 μ) :=
      (eventuallyEq_sum (fun i _ => hi i)).symm
    _ =ᵐ[μ] _ := (Lp.coeFn_finsetSum _ _).symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlanarSchwartzInversion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier inversion on the actual product plane, and the frozen
multiplier identity for every planar Schwartz input. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert

theorem planarFourier_integrable (f : SchwartzMap (ℝ×ℝ) ℂ) :
    Integrable (planarFourier f) (volume.prod volume) := by
  have h : Integrable (planarFourierSchwartz f : ℝ×ℝ → ℂ) (volume.prod volume) :=
    (planarFourierSchwartz f).integrable
  simpa only [funext (planarFourierSchwartz_apply f)] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact modulated convolution kernels for the fixed vertical bin
profiles, with a uniform L1 norm at every width and carrier. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem modulatedTimeKernel_fourier (K : ℝ → ℂ) (W center eta : ℝ) (hW : 0<W) :
    𝓕 (modulatedTimeKernel K W center) eta=𝓕 K (W*(eta-center)) := by
  rw [←scaledTimeKernel_fourier K W hW (eta-center)]
  rw [Real.fourier_eq,Real.fourier_eq]
  simp only [Real.inner_apply,modulatedTimeKernel]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [←mul_smul,←Real.fourierChar.map_add_eq_mul]
  congr 2
  ring

theorem modulatedTimeKernel_norm (K : ℝ → ℂ) (W center t : ℝ) (hW : 0<W) :
    ‖modulatedTimeKernel K W center t‖=W⁻¹*‖K (t/W)‖ := by
  rw [modulatedTimeKernel,Circle.norm_smul,scaledTimeKernel,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg hW.le]

theorem modulatedTimeKernel_l1 (K : SchwartzMap ℝ ℂ) (W center : ℝ) (hW : 0<W) :
    (∫ t, ‖modulatedTimeKernel K W center t‖)=∫ t, ‖K t‖ := by
  simp_rw [modulatedTimeKernel_norm K W center _ hW]
  rw [integral_const_mul,Measure.integral_comp_div (fun t => ‖K t‖) W,
    abs_of_pos hW,smul_eq_mul]
  rw [←mul_assoc,inv_mul_cancel₀ hW.ne',one_mul]

theorem verticalProfileKernel_fourier (q : SchwartzMap ℝ ℂ) (W center eta : ℝ) (hW : 0<W) :
    𝓕 (verticalProfileKernel q W center) eta=q (W*(eta-center)) := by
  rw [verticalProfileKernel,modulatedTimeKernel_fourier _ W center eta hW]
  have h : (𝓕 (𝓕⁻ q : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ)=q := fourier_fourierInv_eq q
  exact congrArg (fun f : SchwartzMap ℝ ℂ => f (W*(eta-center))) h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarFrequencyPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two separated frequency factors are Fourier transforms of actual
Schwartz convolution kernels. Thus the lattice average uses actual packets. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem planarInverseSchwartz_apply (F : SchwartzMap (ℝ×ℝ) ℂ) (x : ℝ×ℝ) :
    planarInverseSchwartz F x=planarInverse F x := by
  rw [← planarFourier_inversion (planarInverseSchwartz F) x]
  congr 1
  funext omega
  exact planarInverseSchwartz_fourier F omega

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalInverseMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact inverse-frequency representation of vertical convolution. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem vertical_inverse_multiplier (k : ℝ → ℂ) (F : ℝ×ℝ → ℂ)
    (hk : Integrable k) (hF : Integrable F planeMeasure)
    (x : ℝ×ℝ) :
    verticalConvolution k (planarInverse F) x =
      ∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (𝓕 k (omega.2)*F omega) ∂planeMeasure := by
  let phase := fun (t : ℝ) (omega : ℝ×ℝ) =>
    x.1*omega.1+(x.2-t)*omega.2
  let H := fun p : ℝ×(ℝ×ℝ) =>
    (k p.1*F p.2)*(Real.fourierChar (phase p.1 p.2):ℂ)
  have hH : Integrable H (volume.prod planeMeasure) := by
    apply (hk.mul_prod hF).mul_bdd (c := 1)
    · exact (show Continuous (fun p : ℝ×(ℝ×ℝ) =>
        (Real.fourierChar (phase p.1 p.2) : ℂ)) by dsimp [phase]; fun_prop).aestronglyMeasurable
    · filter_upwards [] with p
      exact le_of_eq (Circle.norm_coe _)
  have hleft (t : ℝ) : k t*planarInverse F (x.1,x.2-t) =
      ∫ omega, H (t,omega) ∂planeMeasure := by
    rw [planarInverse, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with omega
    change k t*((Real.fourierChar (phase t omega):ℂ)*F omega)=_
    dsimp only [H]
    ring
  have hright (omega : ℝ×ℝ) : (∫ t, H (t,omega)) =
      Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (𝓕 k (omega.2)*F omega) := by
    rw [Real.fourier_eq]
    simp only [Real.inner_apply, Circle.smul_def, smul_eq_mul]
    rw [← integral_mul_const, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [H]
    have hp : phase t omega=(x.1*omega.1+x.2*omega.2)+(-(t*(omega.2))) := by
      dsimp [phase]
      ring
    rw [hp, Real.fourierChar.map_add_eq_mul]
    push_cast
    ring
  calc
    _ = ∫ t, ∫ omega, H (t,omega) ∂planeMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall hleft)
    _ = ∫ omega, (∫ t, H (t,omega) ∂volume) ∂planeMeasure := integral_integral_swap hH
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hright)


theorem schwartz_vertical_multiplier (K : ℝ → ℂ) (hK : Integrable K)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    verticalConvolution K f z=
      planarInverse (fun omega => 𝓕 K omega.2*planarFourier f omega) z := by
  have h := vertical_inverse_multiplier K (planarFourier f) hK (planarFourier_integrable f) z
  simpa only [funext (planarFourier_inversion f),planarInverse] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SchwartzVerticalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical frequency cutoffs preserve the actual planar Schwartz class. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem schwartzVerticalProjection_eq_convolution (q : SchwartzMap ℝ ℂ) (W center : ℝ)
    (hW : 0<W) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    schwartzVerticalProjection q W center f z=
      verticalConvolution (verticalProfileKernel q W center) f z := by
  rw [schwartz_vertical_multiplier (verticalProfileKernel q W center)
    (modulatedTimeKernel_integrable (𝓕⁻ q : SchwartzMap ℝ ℂ) W center hW)]
  simp_rw [verticalProfileKernel_fourier q W center _ hW]
  rw [schwartzVerticalProjection,planarInverseSchwartz_apply]
  congr 1
  funext omega
  rw [SchwartzMap.smulLeftCLM_apply_apply (verticalProfile_temperate q W center),
    planarFourierSchwartz_apply,smul_eq_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TimeErrorEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A normalized integrable envelope for the two endpoint errors in a
sharp time truncation. Its integral is independent of its radius. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem timeErrorEnvelope_nonneg (r t : ℝ) (hr : 0 < r) : 0≤timeErrorEnvelope r t := by
  unfold timeErrorEnvelope
  positivity

theorem timeErrorEnvelope_eq (r t : ℝ) (hr : 0 < r) :
    timeErrorEnvelope r t=r⁻¹*lineEnvelope 0 r 1 t := by
  unfold timeErrorEnvelope lineEnvelope
  simp only [sub_zero,pow_one]
  have hden : r^2+t^2≠0 := ne_of_gt (by positivity)
  have hden' : 1+(t/r)^2≠0 := ne_of_gt (by positivity)
  field_simp

theorem timeErrorEnvelope_integrable (r : ℝ) (hr : 0 < r) :
    Integrable (timeErrorEnvelope r) := by
  have h := (integrable_lineEnvelope_one 0 r hr).const_mul r⁻¹
  simpa only [←timeErrorEnvelope_eq r _ hr] using h

theorem timeErrorEnvelope_integral (r : ℝ) (hr : 0 < r) :
    (∫ t, timeErrorEnvelope r t)=Real.pi := by
  simp_rw [timeErrorEnvelope_eq r _ hr]
  rw [integral_const_mul,integral_lineEnvelope_one 0 r hr]
  field_simp

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ProductSlopePrincipalValueBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fatou passage from uniform actual sharp truncations to the pointwise
symmetric principal value in product coordinates. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem productSlopePrincipalValue_eLpNorm_le (u : (ℝ×ℝ) → ℝ) (hu : Measurable u)
    (f : (ℝ×ℝ) → ℂ) (hf : Differentiable ℝ f) (R : ℝ) (hR : 0<R) (hRsmall : R≤1/4)
    (C : ℝ≥0∞)
    (hbound : ∀ epsilon : ℝ, 0<epsilon → epsilon<R →
      eLpNorm (shortSlopeOperator (sharpTimeKernel epsilon R) u f) 2 planeMeasure≤C) :
    eLpNorm (productSlopePrincipalValue u R f) 2 planeMeasure≤C := by
  apply Lp.eLpNorm_le_of_ae_tendsto (u:=(atTop : Filter ℕ))
    (Eventually.of_forall fun n => hbound _ (pvInnerRadius_pos R hR n) (pvInnerRadius_lt R hR n))
    (fun n => (shortSlopeOperator_measurable _ (sharpTimeKernel_measurable _ R) u hu f hf.continuous.measurable).aestronglyMeasurable)
  exact Eventually.of_forall (shortSharp_tendsto_productSlopePrincipalValue u f hf R hR hRsmall)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceL2Gram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact L2 Gram identities for the finite physical packet sums. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem memLp_inner_integral (mu : Measure X) (f g : X → E)
    (hf : MemLp f 2 mu) (hg : MemLp g 2 mu) :
    inner ℂ (hf.toLp f) (hg.toLp g)=∫ x, inner ℂ (f x) (g x) ∂mu := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hfx hgx
  rw [hfx,hgx]

theorem memLp_toL2_norm_sq (mu : Measure X) (f : X → E) (hf : MemLp f 2 mu) :
    ‖hf.toLp f‖^2=∫ x, ‖f x‖^2 ∂mu := by
  have h := memLp_inner_integral mu f f hf hf
  simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow] at h
  change ((‖hf.toLp f‖^2 : ℝ) : ℂ)=(∫ x, ((‖f x‖^2 : ℝ) : ℂ) ∂mu) at h
  rw [integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_L2Indicator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable cutoffs as contractions on the actual complex L2 space. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert
variable {X : Type*} [MeasurableSpace X]

theorem l2Indicator_toLp (mu : Measure X) (S : Set X) (hS : MeasurableSet S)
    (f : X → ℂ) (hf : MemLp f 2 mu) :
    l2Indicator mu S hS (hf.toLp f)=(hf.indicator hS).toLp (S.indicator f) := by
  apply Lp.ext
  filter_upwards [((Lp.memLp (hf.toLp f)).indicator hS).coeFn_toLp,
    (hf.indicator hS).coeFn_toLp,hf.coeFn_toLp] with z hz hz' hfz
  change (((Lp.memLp (hf.toLp f)).indicator hS).toLp (S.indicator (hf.toLp f))) z=_
  rw [hz,hz']
  by_cases h : z∈S
  · simp only [Set.indicator_of_mem h,hfz]
  · simp only [Set.indicator_of_notMem h]

theorem l2Indicator_coe (mu : Measure X) (S : Set X) (hS : MeasurableSet S)
    (f : Lp ℂ 2 mu) : l2Indicator mu S hS f=ᵐ[mu] S.indicator f :=
  ((Lp.memLp f).indicator hS).coeFn_toLp

theorem l2Indicator_inner (mu : Measure X) (S : Set X) (hS : MeasurableSet S)
    (f g : Lp ℂ 2 mu) :
    inner ℂ (l2Indicator mu S hS f) g=inner ℂ f (l2Indicator mu S hS g) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2Indicator_coe mu S hS f,l2Indicator_coe mu S hS g] with z hf hg
  rw [hf,hg]
  by_cases hz : z∈S
  · simp only [Set.indicator_of_mem hz]
  · simp only [Set.indicator_of_notMem hz,inner_zero_left,inner_zero_right]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_L2IndicatorAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested measurable cutoffs on L2. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert
variable {X : Type*} [MeasurableSpace X]

theorem l2Indicator_nested (mu : Measure X) (S T : Set X) (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hST : S⊆T) (f : Lp ℂ 2 mu) :
    l2Indicator mu S hS (l2Indicator mu T hT f)=l2Indicator mu S hS f := by
  apply Lp.ext
  filter_upwards [l2Indicator_coe mu S hS (l2Indicator mu T hT f),
    l2Indicator_coe mu T hT f,l2Indicator_coe mu S hS f] with z h1 h2 h3
  rw [h1,h3]
  by_cases hz : z∈S
  · simp only [Set.indicator_of_mem hz,h2,Set.indicator_of_mem (hST hz)]
  · simp only [Set.indicator_of_notMem hz]

theorem l2Indicator_idempotent (mu : Measure X) (S : Set X) (hS : MeasurableSet S)
    (f : Lp ℂ 2 mu) : l2Indicator mu S hS (l2Indicator mu S hS f)=l2Indicator mu S hS f :=
  l2Indicator_nested mu S S hS hS (Subset.rfl) f

theorem l2Indicator_norm_le (mu : Measure X) (S : Set X) (hS : MeasurableSet S)
    (f : Lp ℂ 2 mu) : ‖l2Indicator mu S hS f‖≤‖f‖ := l2IndicatorLM_norm mu S hS f

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteRestrictedStrongNull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Null support-measure levels contribute zero and can be removed
before the positive-measure class argument. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem finite_restricted_strong_nonneg (I J : Finset ℤ) (m n : ℤ → ℝ)
    (B : ℤ → ℤ → ℂ) (C : ℝ) (hC : 0≤C)
    (hm : ∀ i∈I, 0 ≤ m i) (hn : ∀ j∈J, 0≤n j)
    (hB : ∀ i∈I, ∀ j∈J, ‖B i j‖≤
      C*((1+|Real.log (m i/n j)|)^3)⁻¹*Real.sqrt (m i)*Real.sqrt (n j)) :
    ‖∑ i∈I, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) • B i j‖≤
      C*restrictedStrongConstant*
        Real.sqrt (∑ i∈I, ((2:ℝ)^i*Real.sqrt (m i))^2)*
        Real.sqrt (∑ j∈J, ((2:ℝ)^j*Real.sqrt (n j))^2) := by
  classical
  let Ip := I.filter (fun i => 0 < m i)
  let Jp := J.filter (fun j => 0<n j)
  have hIp : Ip⊆I := Finset.filter_subset _ _
  have hJp : Jp⊆J := Finset.filter_subset _ _
  have hz (i : ℤ) (hi : i∈I) (j : ℤ) (hj : j∈J) (hzero : m i=0 ∨ n j=0) : B i j=0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    rcases hzero with he | he
    · simpa only [he,Real.sqrt_zero,mul_zero,zero_mul] using hB i hi j hj
    · simpa only [he,Real.sqrt_zero,mul_zero] using hB i hi j hj
  have heq : (∑ i∈Ip, ∑ j∈Jp, ((2:ℝ)^i*(2:ℝ)^j) • B i j)=
      ∑ i∈I, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) • B i j := by
    calc
      _ = ∑ i∈Ip, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) • B i j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_subset hJp
        intro j hj hjp
        have hn0 : n j=0 := le_antisymm (le_of_not_gt (by simpa only [Jp,Finset.mem_filter,hj,true_and] using hjp)) (hn j hj)
        rw [hz i (hIp hi) j hj (Or.inr hn0),smul_zero]
      _ = _ := by
        apply Finset.sum_subset hIp
        intro i hi hip
        have hm0 : m i=0 := le_antisymm (le_of_not_gt (by simpa only [Ip,Finset.mem_filter,hi,true_and] using hip)) (hm i hi)
        exact Finset.sum_eq_zero (fun j hj => by rw [hz i hi j hj (Or.inl hm0),smul_zero])
  rw [←heq]
  have h := finite_restricted_strong Ip Jp m n B C hC
    (fun i hi => (Finset.mem_filter.mp hi).2) (fun j hj => (Finset.mem_filter.mp hj).2)
    (fun i hi j hj => hB i (hIp hi) j (hJp hj))
  apply h.trans
  have hE : (∑ i∈Ip, ((2:ℝ)^i*Real.sqrt (m i))^2)≤∑ i∈I, ((2:ℝ)^i*Real.sqrt (m i))^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hIp (fun _ _ _ => sq_nonneg _)
  have hF : (∑ j∈Jp, ((2:ℝ)^j*Real.sqrt (n j))^2)≤∑ j∈J, ((2:ℝ)^j*Real.sqrt (n j))^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hJp (fun _ _ _ => sq_nonneg _)
  have hconstant := restrictedStrongConstant_pos.le
  gcongr

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RestrictedStrongLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous bilinear form with the paper's restricted logarithmic
estimate has the uniform L2 bound. Continuity is used only in the final
passage from actual finite amplitude approximations. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem restricted_strong_Lp (μ : Measure X)
    (B : Lp (EuclideanSpace ℂ κ) 2 μ →L[ℝ] Lp (EuclideanSpace ℂ κ) 2 μ →L[ℝ] ℂ)
    (C : ℝ) (hC : 0≤C)
    (hB : ∀ F G : Set X, MeasurableSet F → MeasurableSet G → μ F≠∞ → μ G≠∞ →
      0<μ.real F → 0<μ.real G →
      ∀ (u v : X → EuclideanSpace ℂ κ), Measurable u → Measurable v →
        (∀ x, ‖u x‖≤1) → (∀ x, ‖v x‖≤1) →
        (∀ x, x∉F → u x=0) → (∀ x, x∉G → v x=0) →
      ∀ (hu : MemLp u 2 μ) (hv : MemLp v 2 μ),
        ‖B (hu.toLp u) (hv.toLp v)‖≤C*((1+|Real.log (μ.real F/μ.real G)|)^3)⁻¹*
          Real.sqrt (μ.real F)*Real.sqrt (μ.real G))
    (f g : X → EuclideanSpace ℂ κ) (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ) :
    ‖B (hf2.toLp f) (hg2.toLp g)‖≤
      4*C*restrictedStrongConstant*Real.sqrt (∫ x, ‖f x‖^2 ∂μ)*Real.sqrt (∫ x, ‖g x‖^2 ∂μ) := by
  let beta := fun i j : ℤ => B (amplitudeLpPiece μ hf hf2 i) (amplitudeLpPiece μ hg hg2 j)
  have hbeta (i j : ℤ) : ‖beta i j‖≤
      C*((1+|Real.log (μ.real (amplitudeLevel f i)/μ.real (amplitudeLevel g j))|)^3)⁻¹*
        Real.sqrt (μ.real (amplitudeLevel f i))*Real.sqrt (μ.real (amplitudeLevel g j)) := by
    by_cases hi : μ.real (amplitudeLevel f i)=0
    · simp only [beta,amplitudeLpPiece_zero μ hf hf2 i hi,map_zero,zero_apply,
        norm_zero,hi,Real.sqrt_zero,mul_zero,zero_mul,le_refl]
    · by_cases hj : μ.real (amplitudeLevel g j)=0
      · simp only [beta,amplitudeLpPiece_zero μ hg hg2 j hj,map_zero,norm_zero,
          hj,Real.sqrt_zero,mul_zero,le_refl]
      · exact hB _ _ (amplitudeLevel_measurable hf.norm i) (amplitudeLevel_measurable hg.norm j)
          (amplitudeLevel_finite μ hf2 i) (amplitudeLevel_finite μ hg2 j)
          (lt_of_le_of_ne measureReal_nonneg (Ne.symm hi)) (lt_of_le_of_ne measureReal_nonneg (Ne.symm hj))
          _ _ (amplitudePiece_measurable hf i) (amplitudePiece_measurable hg j)
          (amplitudePiece_bounded f i) (amplitudePiece_bounded g j)
          (amplitudePiece_supported f i) (amplitudePiece_supported g j)
          (amplitudePiece_memLp μ hf hf2 i) (amplitudePiece_memLp μ hg hg2 j)
  have hfinite (I J : Finset ℤ) :
      ‖B ((amplitudeApprox_memLp μ hf hf2 I).toLp (amplitudeApprox f I))
        ((amplitudeApprox_memLp μ hg hg2 J).toLp (amplitudeApprox g J))‖≤
      4*C*restrictedStrongConstant*Real.sqrt (∫ x, ‖f x‖^2 ∂μ)*Real.sqrt (∫ x, ‖g x‖^2 ∂μ) := by
    have heq : B ((amplitudeApprox_memLp μ hf hf2 I).toLp (amplitudeApprox f I))
        ((amplitudeApprox_memLp μ hg hg2 J).toLp (amplitudeApprox g J))=
        ∑ i∈I, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) • beta i j := by
      rw [amplitudeApprox_toLp,amplitudeApprox_toLp]
      simp only [map_sum,map_smul,sum_apply,smul_apply,
        Finset.smul_sum,smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_comm]
    rw [heq]
    have hn := finite_restricted_strong_nonneg I J
      (fun i => μ.real (amplitudeLevel f i)) (fun j => μ.real (amplitudeLevel g j)) beta C hC
      (fun _ _ => measureReal_nonneg) (fun _ _ => measureReal_nonneg) (fun i _ j _ => hbeta i j)
    have hEf := amplitude_energy_budget μ hf2 hf.norm I
    have hEg := amplitude_energy_budget μ hg2 hg.norm J
    have hrootf : Real.sqrt (∑ i∈I, ((2:ℝ)^i*Real.sqrt (μ.real (amplitudeLevel f i)))^2)≤
        2*Real.sqrt (∫ x, ‖f x‖^2 ∂μ) := by
      calc
        _ ≤ Real.sqrt (4*(∫ x, ‖f x‖^2 ∂μ)) := Real.sqrt_le_sqrt hEf
        _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]; norm_num
    have hrootg : Real.sqrt (∑ j∈J, ((2:ℝ)^j*Real.sqrt (μ.real (amplitudeLevel g j)))^2)≤
        2*Real.sqrt (∫ x, ‖g x‖^2 ∂μ) := by
      calc
        _ ≤ Real.sqrt (4*(∫ x, ‖g x‖^2 ∂μ)) := Real.sqrt_le_sqrt hEg
        _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]; norm_num
    apply hn.trans
    calc
      _ ≤ C*restrictedStrongConstant*(2*Real.sqrt (∫ x, ‖f x‖^2 ∂μ))*(2*Real.sqrt (∫ x, ‖g x‖^2 ∂μ)) := by
        have hconstant := restrictedStrongConstant_pos.le
        gcongr
      _ = _ := by ring
  have hfn := amplitudeApprox_Lp_tendsto μ hf hf2
  have hgn := amplitudeApprox_Lp_tendsto μ hg hg2
  have hlim := (B.isBoundedBilinearMap.continuous.tendsto _).comp (hfn.prodMk_nhds hgn)
  exact le_of_tendsto hlim.norm (Filter.Eventually.of_forall (fun n =>
    hfinite (Finset.Icc (-(n:ℤ)) n) (Finset.Icc (-(n:ℤ)) n)))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RestrictedStrongOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restricted logarithmic estimate controls the actual L2 operator
norm. A finite truncation's preliminary continuity suffices; its original
continuity bound does not enter the final constant. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem restricted_strong_Lp_norm (μ : Measure X)
    (B : HilbertLp (κ := κ) μ →L[ℝ] HilbertLp (κ := κ) μ →L[ℝ] ℂ)
    (C : ℝ) (hC : 0≤C) (hB : HasRestrictedLogBound μ B C)
    (f g : HilbertLp (κ := κ) μ) :
    ‖B f g‖≤4*C*restrictedStrongConstant*‖f‖*‖g‖ := by
  have h := restricted_strong_Lp μ B C hC hB f g
    (Lp.stronglyMeasurable f).measurable (Lp.stronglyMeasurable g).measurable (Lp.memLp f) (Lp.memLp g)
  have hroot (v : HilbertLp (κ := κ) μ) : Real.sqrt (∫ x, ‖v x‖^2 ∂μ)=‖v‖ := by
    rw [← memLp_toL2_norm_sq μ v (Lp.memLp v), Lp.toLp_coeFn, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg v)]
  simpa only [Lp.toLp_coeFn, hroot] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ScalarRestrictedStrong
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar complex instance of the proved restricted-to-strong
estimate, transported through the one-dimensional orthonormal basis. -/
noncomputable section
open MeasureTheory Function Set
open scoped ENNReal
namespace LipschitzHilbert
variable {X : Type*} [MeasurableSpace X]

theorem scalarDrop_lift (mu : Measure X) (f : Lp ℂ 2 mu) : scalarDrop mu (scalarLift mu f)=f := by
  apply Lp.ext
  filter_upwards [(scalarCoordinate.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).coeFn_compLpL (scalarLift mu f),
    (scalarCoordinate.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).coeFn_compLpL f] with z hz hz'
  change (scalarDrop mu (scalarLift mu f)) z=scalarCoordinate.symm ((scalarLift mu f) z) at hz
  rw [hz]
  change (scalarLift mu f) z=scalarCoordinate (f z) at hz'
  rw [hz',scalarCoordinate.symm_apply_apply]

theorem scalarLift_norm (mu : Measure X) (f : Lp ℂ 2 mu) : ‖scalarLift mu f‖=‖f‖ := by
  rw [Lp.norm_def,Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [(scalarCoordinate.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).coeFn_compLpL f] with z hz
  change (scalarLift mu f) z=scalarCoordinate (f z) at hz
  rw [hz,scalarCoordinate.norm_map]

theorem scalarDrop_toLp (mu : Measure X) (f : X → EuclideanSpace ℂ (Fin 1)) (hf : MemLp f 2 mu) :
    scalarDrop mu (hf.toLp f)=
      ((scalarCoordinate.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp_memLp' hf).toLp
        ((scalarCoordinate.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) ∘ f) := by
  apply Lp.ext
  filter_upwards [(scalarCoordinate.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).coeFn_compLpL (hf.toLp f),
    hf.coeFn_toLp,
    ((scalarCoordinate.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp_memLp' hf).coeFn_toLp]
    with z hz hfz hout
  change (scalarDrop mu (hf.toLp f)) z=scalarCoordinate.symm ((hf.toLp f) z) at hz
  rw [hz,hout,hfz]
  rfl

theorem scalar_restricted_strong_norm (mu : Measure X)
    (B : Lp ℂ 2 mu →L[ℝ] Lp ℂ 2 mu →L[ℝ] ℂ)
    (C : ℝ) (hC : 0≤C) (hB : HasScalarRestrictedLogBound mu B C)
    (f g : Lp ℂ 2 mu) :
    ‖B f g‖≤4*C*restrictedStrongConstant*‖f‖*‖g‖ := by
  let B' := B.bilinearComp (scalarDrop mu) (scalarDrop mu)
  have hB' : HasRestrictedLogBound mu B' C := by
    intro F G hF hG hFfin hGfin hFpos hGpos u v hum hvm hu hv hus hvs hu2 hv2
    change ‖B (scalarDrop mu (hu2.toLp u)) (scalarDrop mu (hv2.toLp v))‖≤_
    rw [scalarDrop_toLp,scalarDrop_toLp]
    apply hB F G hF hG hFfin hGfin hFpos hGpos
    · exact scalarCoordinate.symm.continuous.measurable.comp hum
    · exact scalarCoordinate.symm.continuous.measurable.comp hvm
    · intro z
      change ‖scalarCoordinate.symm (u z)‖≤1
      simpa only [scalarCoordinate.symm.norm_map] using hu z
    · intro z
      change ‖scalarCoordinate.symm (v z)‖≤1
      simpa only [scalarCoordinate.symm.norm_map] using hv z
    · intro z hz; simp only [comp_apply,hus z hz,map_zero]
    · intro z hz; simp only [comp_apply,hvs z hz,map_zero]
  have h := restricted_strong_Lp_norm mu B' C hC hB' (scalarLift mu f) (scalarLift mu g)
  simpa only [B',ContinuousLinearMap.bilinearComp_apply,scalarDrop_lift,scalarLift_norm] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_KernelDifferencePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A kernel L1 error controls the actual localized bilinear form by the
smaller of the input and test masses. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem slopeOperator_kernel_sub (K J : ℝ → ℂ) (hK : Integrable K) (hJ : Integrable J)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    slopeKernelOperator (fun t => K t-J t) u f z=
      slopeKernelOperator K u f z-slopeKernelOperator J u f z := by
  simp only [slopeKernelOperator,sub_mul]
  exact integral_sub (slope_integrand_integrable K hK u f z)
    (slope_integrand_integrable J hJ u f z)

theorem shortSlopeOperator_kernel_sub (K J : ℝ → ℂ) (hK : Integrable K) (hJ : Integrable J)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    shortSlopeOperator (fun t => K t-J t) u f z=
      shortSlopeOperator K u f z-shortSlopeOperator J u f z := by
  simp only [shortSlopeOperator_eq_kernel]
  have heq : shortTimeKernel (fun t => K t-J t)=
      fun t => shortTimeKernel K t-shortTimeKernel J t := by
    funext t
    unfold shortTimeKernel
    split_ifs <;> simp
  rw [heq]
  exact slopeOperator_kernel_sub _ _ (shortTimeKernel_integrable K hK)
    (shortTimeKernel_integrable J hJ) u f z

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortL2Operator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The preliminary L2 realization of the short-time operator. Its
logarithmic kernel norm is used only for continuity and density. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem shortSchwartzToL2_norm (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    ‖shortSchwartzToL2 K hKm hK u hu f‖≤(2*∫ t, ‖K t‖)*‖f.toLp 2 planeMeasure‖ := by
  have he := (shortSlopeOperator_energy K hKm hK u hu f f.continuous.measurable (f.memLp 2 planeMeasure)).2
  have hout := memLp_toL2_norm_sq planeMeasure (shortSlopeOperator K u f) (shortSchwartz_memLp K hKm hK u hu f)
  have hin := memLp_toL2_norm_sq planeMeasure f (f.memLp 2 planeMeasure)
  change ‖shortSchwartzToL2 K hKm hK u hu f‖^2=_ at hout
  change ‖f.toLp 2 planeMeasure‖^2=_ at hin
  rw [←hout,←hin] at he
  have hnonneg : 0≤∫ t, ‖K t‖ := integral_nonneg fun _ => norm_nonneg _
  have hsq : ‖shortSchwartzToL2 K hKm hK u hu f‖^2≤
      ((2*∫ t, ‖K t‖)*‖f.toLp 2 planeMeasure‖)^2 := by
    exact he.trans_eq (by ring)
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num) hnonneg) (norm_nonneg _))).1 hsq

theorem shortL2Operator_onSchwartz (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    shortL2Operator K hKm hK u hu (f.toLp 2 planeMeasure)=shortSchwartzToL2 K hKm hK u hu f := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · exact ⟨2*∫ t, ‖K t‖,shortSchwartzToL2_norm K hKm hK u hu⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NormalizedBandProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed normalization of the original vertical cutoff controls its
L1, L2 and uniform sizes without changing its frequency band or strip. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem verticalProjectionCost_pos (p : SchwartzMap ℝ ℂ) : 0<verticalProjectionCost p := by
  unfold verticalProjectionCost
  have h : 0≤∫ s, ‖(𝓕⁻ p : SchwartzMap ℝ ℂ) s‖ := integral_nonneg fun _ => norm_nonneg _
  linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalL2Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual vertical Schwartz multiplier extends to L2. This
preliminary bound supplies continuity for restricted-test approximation. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem verticalSchwartzToL2_norm (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    ‖verticalSchwartzToL2 p w f‖≤verticalProjectionCost p*‖f.toLp 2 planeMeasure‖ := by
  let K := verticalProfileKernel p w 0
  let A := ∫ s, ‖(𝓕⁻ p : SchwartzMap ℝ ℂ) s‖
  have hKm : Measurable K := by
    unfold K verticalProfileKernel modulatedTimeKernel scaledTimeKernel
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (continuous_const.mul ((𝓕⁻ p : SchwartzMap ℝ ℂ).continuous.comp (by fun_prop)))).measurable
  have hKi : Integrable K := modulatedTimeKernel_integrable (𝓕⁻ p) w 0 hw
  have he := (verticalConvolution_energy_bound K hKi hKm f f.continuous.measurable
    (f.memLp 2 planeMeasure)).2
  have hid : verticalConvolution K f=schwartzVerticalProjection p w 0 f := by
    funext z
    exact (schwartzVerticalProjection_eq_convolution p w 0 hw f z).symm
  have hmass : (∫ s, ‖K s‖)=A := modulatedTimeKernel_l1 (𝓕⁻ p) w 0 hw
  rw [hid,hmass] at he
  have hout := memLp_toL2_norm_sq planeMeasure (schwartzVerticalProjection p w 0 f)
    ((schwartzVerticalProjection p w 0 f).memLp 2 planeMeasure)
  have hin := memLp_toL2_norm_sq planeMeasure f (f.memLp 2 planeMeasure)
  change ‖verticalSchwartzToL2 p w f‖^2=_ at hout
  change ‖f.toLp 2 planeMeasure‖^2=_ at hin
  rw [←hout,←hin] at he
  have hA : 0≤A := integral_nonneg fun _ => norm_nonneg _
  have hAC : A≤verticalProjectionCost p := by
    change A≤1+A
    linarith only [hA]
  have hsquare : ‖verticalSchwartzToL2 p w f‖^2≤
      (verticalProjectionCost p*‖f.toLp 2 planeMeasure‖)^2 := by
    apply he.trans
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA hAC 2) (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (verticalProjectionCost_pos p).le (norm_nonneg _))).1 hsquare

theorem verticalL2Projection_onSchwartz (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    verticalL2Projection p w (f.toLp 2 planeMeasure)=(schwartzVerticalProjection p w 0 f).toLp 2 planeMeasure := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · exact ⟨verticalProjectionCost p,verticalSchwartzToL2_norm p w hw⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BandL2Pairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous L2 realization of the actual short-time band pairing. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem bandL2Operator_onSchwartz (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (hw : 0<w) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    bandL2Operator K hKm hK u hu p w (f.toLp 2 planeMeasure)=
      shortSchwartzToL2 K hKm hK u hu (schwartzVerticalProjection p w 0 f) := by
  change shortL2Operator K hKm hK u hu (verticalL2Projection p w (f.toLp 2 planeMeasure))=_
  rw [verticalL2Projection_onSchwartz p w hw,shortL2Operator_onSchwartz]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TimeEndpointComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A factor-two change of the inner time endpoint costs a fixed L1
constant. Every positive inner endpoint has such a dyadic representative. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_close_lower (r s R t : ℝ) (hr : 0 < r)
    (hrs : r ≤ s) (hsr : s≤2*r) :
    ‖sharpTimeKernel r R t-sharpTimeKernel s R t‖≤3*timeErrorEnvelope r t := by
  have hq := timeErrorEnvelope_nonneg r t hr
  by_cases hs : s< |t|
  · have hr' : r< |t| := hrs.trans_lt hs
    simp only [sharpTimeKernel,hr',hs,true_and,sub_self,norm_zero]
    positivity
  · by_cases hr' : r< |t|
    · by_cases hR : |t|<R
      · have ht : 0< |t| := hr.trans hr'
        have ht2 : |t|≤2*r := (le_of_not_gt hs).trans hsr
        have hd : 0 < r^2+t^2 := by positivity
        have hpoly : r^2+t^2≤3*r*|t| := by
          nlinarith [sq_abs t,mul_nonneg (sub_nonneg.mpr hr'.le) (sub_nonneg.mpr ht2)]
        have hcond1 : r< |t| ∧ |t|<R := ⟨hr',hR⟩
        have hcond2 : ¬(s< |t| ∧ |t|<R) := fun h => hs h.1
        simp only [sharpTimeKernel,ite_eq_left hcond1,ite_eq_right hcond2,sub_zero,
          norm_inv,Complex.norm_real,Real.norm_eq_abs,timeErrorEnvelope]
        rw [←mul_div_assoc,inv_eq_one_div]
        apply (div_le_div_iff₀ ht hd).2
        nlinarith only [hpoly]
      · have hcond1 : ¬(r< |t| ∧ |t|<R) := fun h => hR h.2
        have hcond2 : ¬(s< |t| ∧ |t|<R) := fun h => hR h.2
        simp only [sharpTimeKernel,ite_eq_right hcond1,ite_eq_right hcond2,sub_self,norm_zero]
        positivity
    · have hcond1 : ¬(r< |t| ∧ |t|<R) := fun h => hr' h.1
      have hcond2 : ¬(s< |t| ∧ |t|<R) := fun h => hs h.1
      simp only [sharpTimeKernel,ite_eq_right hcond1,ite_eq_right hcond2,sub_self,norm_zero]
      positivity

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalConvolutionLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical convolution on the L2 quotient, with its actual integral representative. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalConvolution_congr_ae (K : ℝ → ℂ) (f g : ℝ×ℝ → ℂ)
    (hf : Measurable f) (hg : Measurable g) (hfg : f=ᵐ[planeMeasure] g) :
    verticalConvolution K f=ᵐ[planeMeasure] verticalConvolution K g := by
  have he : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ z ∂planeMeasure,
      f (z.1,z.2-t)=g (z.1,z.2-t) := by
    apply Filter.Eventually.of_forall
    intro t
    exact (verticalTranslation_measurePreserving t).quasiMeasurePreserving.ae hfg
  have hm : MeasurableSet {p : ℝ×(ℝ×ℝ) | f (p.2.1,p.2.2-p.1)=g (p.2.1,p.2.2-p.1)} :=
    measurableSet_eq_fun (hf.comp (by fun_prop)) (hg.comp (by fun_prop))
  have hs := (Measure.ae_ae_comm hm).mp he
  filter_upwards [hs] with z hz
  apply integral_congr_ae
  filter_upwards [hz] with t ht
  rw [ht]

theorem verticalConvolution_integrand_ae (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f)
    (hf : MemLp f 2 planeMeasure) :
    ∀ᵐ z ∂planeMeasure, Integrable (fun t => K t*f (z.1,z.2-t)) := by
  filter_upwards [(verticalConvolution_energy_joint_integrable K hK hKm f hfm hf).prod_left_ae]
    with z hz
  have hc := (weighted_integral_cauchySchwarz volume (fun t => ‖K t‖)
    (fun t => ‖f (z.1,z.2-t)‖) hKm.norm (hfm.norm.comp (by fun_prop))
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hK.norm hz).1
  exact hc.mono' ((hKm.mul (hfm.comp (by fun_prop))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => le_of_eq (norm_mul _ _))

theorem verticalConvolution_sub_ae (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f g : ℝ×ℝ → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 planeMeasure) (hg : MemLp g 2 planeMeasure) :
    verticalConvolution K (f-g)=ᵐ[planeMeasure]
      (verticalConvolution K f-verticalConvolution K g) := by
  filter_upwards [verticalConvolution_integrand_ae K hK hKm f hfm hf,
    verticalConvolution_integrand_ae K hK hKm g hgm hg] with z hfz hgz
  change (∫ t, K t*(f (z.1,z.2-t)-g (z.1,z.2-t)))=_
  simp_rw [mul_sub]
  exact integral_sub hfz hgz

theorem verticalConvolutionLp_coe (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (f : Lp ℂ 2 planeMeasure) :
    (verticalConvolutionLp K hK hKm f : (ℝ×ℝ) → ℂ)=ᵐ[planeMeasure] verticalConvolution K f :=
  MemLp.coeFn_toLp _

theorem verticalConvolutionLp_toLp (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (f : ℝ×ℝ → ℂ) (hfm : Measurable f) (hf : MemLp f 2 planeMeasure) :
    verticalConvolutionLp K hK hKm (hf.toLp f)=
      (verticalConvolution_energy_bound K hK hKm f hfm hf).1.toLp (verticalConvolution K f) := by
  apply Lp.ext
  exact (verticalConvolutionLp_coe K hK hKm _).trans
    ((verticalConvolution_congr_ae K _ f (Lp.stronglyMeasurable (hf.toLp f)).measurable hfm hf.coeFn_toLp).trans
      (MemLp.coeFn_toLp _).symm)

theorem verticalConvolutionLp_sub (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (f g : Lp ℂ 2 planeMeasure) :
    verticalConvolutionLp K hK hKm (f-g)=
      verticalConvolutionLp K hK hKm f-verticalConvolutionLp K hK hKm g := by
  apply Lp.ext
  have hc := verticalConvolution_congr_ae K (show Lp ℂ 2 planeMeasure from f-g) ((f : (ℝ×ℝ)→ℂ)-(g : (ℝ×ℝ)→ℂ))
    (Lp.stronglyMeasurable (f-g)).measurable ((Lp.stronglyMeasurable f).measurable.sub (Lp.stronglyMeasurable g).measurable)
    (Lp.coeFn_sub f g)
  have hs := verticalConvolution_sub_ae K hK hKm f g (Lp.stronglyMeasurable f).measurable
    (Lp.stronglyMeasurable g).measurable (Lp.memLp f) (Lp.memLp g)
  filter_upwards [verticalConvolutionLp_coe K hK hKm (f-g),hc,hs,
    verticalConvolutionLp_coe K hK hKm f,verticalConvolutionLp_coe K hK hKm g,
    Lp.coeFn_sub (verticalConvolutionLp K hK hKm f) (verticalConvolutionLp K hK hKm g)]
    with z h1 h2 h3 h4 h5 h6
  rw [h1,h2,h3,h6]
  simp only [Pi.sub_apply,h4,h5]

theorem verticalConvolutionLp_norm (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (f : Lp ℂ 2 planeMeasure) :
    ‖verticalConvolutionLp K hK hKm f‖≤(∫ t, ‖K t‖)*‖f‖ := by
  have h := (verticalConvolution_energy_bound K hK hKm f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).2
  rw [←memLp_toL2_norm_sq planeMeasure _ (Lp.memLp f),Lp.toLp_coeFn,
    ←memLp_toL2_norm_sq planeMeasure _
      (verticalConvolution_energy_bound K hK hKm f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).1] at h
  change ‖verticalConvolutionLp K hK hKm f‖^2≤(∫ t, ‖K t‖)^2*‖f‖^2 at h
  have hn : 0≤∫ t, ‖K t‖ := integral_nonneg (fun t => norm_nonneg (K t))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hn (norm_nonneg f))).mp
  simpa only [mul_pow] using h

theorem verticalConvolutionLp_continuous (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K) :
    Continuous (verticalConvolutionLp K hK hKm) := by
  apply LipschitzWith.continuous (K:=⟨∫ t, ‖K t‖,integral_nonneg fun _ => norm_nonneg _⟩)
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [dist_eq_norm,dist_eq_norm,←verticalConvolutionLp_sub]
  exact verticalConvolutionLp_norm K hK hKm (f-g)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinLpReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reconstruction of a vertical frequency band for arbitrary L2 inputs. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem verticalProfileLp_continuous (q : SchwartzMap ℝ ℂ) (W center : ℝ) (hW : 0<W) :
    Continuous (verticalProfileLp q W center hW) :=
  verticalConvolutionLp_continuous _ (verticalProfileKernel_integrable q W center hW)
    (verticalProfileKernel_continuous q W center).measurable

theorem verticalProfileLp_schwartz (q : SchwartzMap ℝ ℂ) (W center : ℝ) (hW : 0<W)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    verticalProfileLp q W center hW (f.toLp 2 planeMeasure)=
      (schwartzVerticalProjection q W center f).toLp 2 planeMeasure := by
  apply Lp.ext
  have heq := verticalConvolutionLp_toLp (verticalProfileKernel q W center)
    (verticalProfileKernel_integrable q W center hW)
    (verticalProfileKernel_continuous q W center).measurable f f.continuous.measurable
    (f.memLp 2 planeMeasure)
  change verticalProfileLp q W center hW (f.toLp 2 planeMeasure)=_ at heq
  rw [heq]
  have hmem := (verticalConvolution_energy_bound (verticalProfileKernel q W center)
    (verticalProfileKernel_integrable q W center hW)
    (verticalProfileKernel_continuous q W center).measurable f f.continuous.measurable
    (f.memLp 2 planeMeasure)).1
  filter_upwards [hmem.coeFn_toLp,
    (schwartzVerticalProjection q W center f).coeFn_toLp 2 planeMeasure] with z hz hz'
  rw [hz,hz',schwartzVerticalProjection_eq_convolution _ W center hW]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LocalizedBandStrong
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform strong L2 control of the actual positive-band pairing,
localized in a narrow horizontal strip. -/
noncomputable section
open Set MeasureTheory Function
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem indicator_unit {X : Type*} (A : Set X) (f : X → ℂ) (hf : ∀ z, ‖f z‖≤1) :
    ∀ z, ‖A.indicator f z‖≤1 := by
  intro z
  by_cases hz : z∈A
  · simpa only [Set.indicator_of_mem hz] using hf z
  · simp only [Set.indicator_of_notMem hz,norm_zero,zero_le_one]

theorem indicator_support_subset {X : Type*} (A F : Set X) (f : X → ℂ)
    (hf : ∀ z, z∉F → f z=0) : support (A.indicator f)⊆F := by
  intro z hz
  by_contra hn
  by_cases ha : z∈A
  · exact hz (by rw [Set.indicator_of_mem ha,hf z hn])
  · exact hz (Set.indicator_of_notMem ha f)

theorem localized_sharp_band_strong (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (p : SchwartzMap ℝ ℂ) (hp : ∀ s, p s≠0 → 1 ≤ s ∧ s≤2) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R w : ℝ, (he : 0<epsilon) → (heR : epsilon≤R) → R≤1/4 → 0<w →
    ∀ (field : Plane → ℝ) (hfield : LipschitzWith 1 field), (∀ z, |field z|≤1/4) →
    ∀ l r : ℝ, 1200*(r-l)≤1 → ∀ f g : Lp ℂ 2 planeMeasure,
      ‖localizedSharpBandPairing epsilon R he (he.trans_le heR) field hfield p w l r f g‖≤C*‖f‖*‖g‖ := by
  obtain ⟨C,hC,hbound⟩ := actual_sharp_band_measurable_restricted_log hVariation hLL hH p hp
  refine ⟨4*C*restrictedStrongConstant,mul_pos (mul_pos (by norm_num) hC) restrictedStrongConstant_pos,?_⟩
  intro epsilon R w he heR hR hw field hfield hfb l r hwidth f g
  apply scalar_restricted_strong_norm planeMeasure _ C hC.le _ f g
  intro F G hF hG hFfin hGfin hFpos hGpos u v hum hvm hu hv hus hvs hu2 hv2
  change ‖sharpBandL2Pairing epsilon R he (he.trans_le heR) field hfield p w
    (stripL2Cutoff l r (hu2.toLp u)) (stripL2Cutoff l r (hv2.toLp v))‖≤_
  unfold stripL2Cutoff
  rw [l2Indicator_toLp,l2Indicator_toLp]
  exact hbound epsilon R w he heR hR hw field hfield hfb
    ((horizontalStrip l r).indicator u) ((horizontalStrip l r).indicator v)
    (hum.indicator (horizontalStrip_measurable l r)) (hvm.indicator (horizontalStrip_measurable l r))
    (indicator_unit _ u hu) (indicator_unit _ v hv) G F hG hF hGfin hFfin hFpos hGpos
    (indicator_support_subset _ F u hus) (indicator_support_subset _ G v hvs) l r hwidth
    (fun z hz => Set.indicator_of_notMem (show z∉horizontalStrip l r from hz) u) (fun z hz => Set.indicator_of_notMem (show z∉horizontalStrip l r from hz) v)
    (hu2.indicator (horizontalStrip_measurable l r)) (hv2.indicator (horizontalStrip_measurable l r))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LocalizedBandOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The localized positive-band Hilbert operator has a uniform L2 norm,
independent of its sharp inner endpoint and vertical frequency width. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem localizedSharpBandPairing_eq_inner (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p : SchwartzMap ℝ ℂ) (w l r : ℝ)
    (f g : Lp ℂ 2 planeMeasure) :
    localizedSharpBandPairing epsilon R he hR field hfield p w l r f g=
      inner ℂ g (localizedSharpBandOperator epsilon R he hR field hfield p w l r f) := by
  exact l2Indicator_inner planeMeasure (horizontalStrip l r) (horizontalStrip_measurable l r)
    g ((bandL2Operator (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
      (sharpTimeKernel_integrable epsilon R he hR) (fun z => field (planeCoordinates z))
      (by simpa only [mul_one] using product_slope_lipschitz field hfield) p w) (stripL2Cutoff l r f))

theorem localized_sharp_band_operator_norm (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (p : SchwartzMap ℝ ℂ) (hp : ∀ s, p s≠0 → 1 ≤ s ∧ s≤2) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R w : ℝ, (he : 0<epsilon) → (heR : epsilon≤R) → R≤1/4 → 0<w →
    ∀ (field : Plane → ℝ) (hfield : LipschitzWith 1 field), (∀ z, |field z|≤1/4) →
    ∀ l r : ℝ, 1200*(r-l)≤1 →
      ‖localizedSharpBandOperator epsilon R he (he.trans_le heR) field hfield p w l r‖≤C := by
  obtain ⟨C,hC,hbound⟩ := localized_sharp_band_strong hVariation hLL hH p hp
  refine ⟨C,hC,?_⟩
  intro epsilon R w he heR hR hw field hfield hfb l r hwidth
  apply ContinuousLinearMap.opNorm_le_bound _ hC.le
  intro f
  let T := localizedSharpBandOperator epsilon R he (he.trans_le heR) field hfield p w l r
  have h := hbound epsilon R w he heR hR hw field hfield hfb l r hwidth f (T f)
  rw [localizedSharpBandPairing_eq_inner] at h
  change ‖inner ℂ (T f) (T f)‖≤C*‖f‖*‖T f‖ at h
  rw [inner_self_eq_norm_sq_to_K] at h
  simp only [norm_pow,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg (T f))] at h
  by_cases hz : ‖T f‖=0
  · rw [show ‖localizedSharpBandOperator epsilon R he (he.trans_le heR) field hfield p w l r f‖=0 from hz]
    exact mul_nonneg hC.le (norm_nonneg f)
  · have ht : 0<‖T f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ ht).mp
    simpa only [pow_two,mul_comm] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalHorizontalCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical Fourier projections commute with measurable horizontal
cutoffs. The proof uses their actual convolution representatives. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem verticalL2Projection_eq_profile (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : Lp ℂ 2 planeMeasure) :
    verticalL2Projection p w f=verticalProfileLp p w 0 hw f := by
  have hd : DenseRange (fun g : SchwartzMap (ℝ×ℝ) ℂ => g.toLp 2 planeMeasure) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  refine hd.induction_on f ?_ ?_
  · exact isClosed_eq (verticalL2Projection p w).continuous (verticalProfileLp_continuous p w 0 hw)
  · intro g
    rw [verticalL2Projection_onSchwartz _ _ hw,verticalProfileLp_schwartz]

theorem verticalConvolution_horizontal_indicator (K : ℝ → ℂ) (S : Set ℝ) (f : ℝ×ℝ → ℂ) :
    verticalConvolution K ((Prod.fst ⁻¹' S).indicator f)=
      (Prod.fst ⁻¹' S).indicator (verticalConvolution K f) := by
  funext z
  by_cases hz : z.1∈S
  · rw [Set.indicator_of_mem (show z∈Prod.fst ⁻¹' S from hz)]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [Set.indicator_of_mem (show (z.1,z.2-t)∈Prod.fst ⁻¹' S from hz)]
  · rw [Set.indicator_of_notMem (show z∉Prod.fst ⁻¹' S from hz)]
    apply integral_eq_zero_of_ae
    filter_upwards [] with t
    change K t*((Prod.fst ⁻¹' S).indicator f (z.1,z.2-t))=0
    rw [Set.indicator_of_notMem (show (z.1,z.2-t)∉Prod.fst ⁻¹' S from hz),mul_zero]

theorem verticalConvolutionLp_horizontal_indicator (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (S : Set ℝ) (hS : MeasurableSet S) (f : Lp ℂ 2 planeMeasure) :
    verticalConvolutionLp K hK hKm (l2Indicator planeMeasure (Prod.fst ⁻¹' S) (hS.preimage measurable_fst) f)=
      l2Indicator planeMeasure (Prod.fst ⁻¹' S) (hS.preimage measurable_fst) (verticalConvolutionLp K hK hKm f) := by
  let M := l2Indicator planeMeasure (Prod.fst ⁻¹' S) (hS.preimage measurable_fst)
  have hc := verticalConvolution_congr_ae K (M f) ((Prod.fst ⁻¹' S).indicator f)
    (Lp.stronglyMeasurable (M f)).measurable
    ((Lp.stronglyMeasurable f).measurable.indicator (hS.preimage measurable_fst))
    (l2Indicator_coe planeMeasure _ _ f)
  apply Lp.ext
  filter_upwards [verticalConvolutionLp_coe K hK hKm (M f),hc,
    l2Indicator_coe planeMeasure (Prod.fst ⁻¹' S) (hS.preimage measurable_fst) (verticalConvolutionLp K hK hKm f),
    verticalConvolutionLp_coe K hK hKm f] with z hz hc hz' hf
  change verticalConvolutionLp K hK hKm (M f) z=_
  rw [hz,hc,verticalConvolution_horizontal_indicator,hz']
  by_cases hmem : z.1∈S
  · simp only [Set.indicator_of_mem (show z∈Prod.fst ⁻¹' S from hmem),hf]
  · simp only [Set.indicator_of_notMem (show z∉Prod.fst ⁻¹' S from hmem)]

theorem verticalL2Projection_horizontal_indicator (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (S : Set ℝ) (hS : MeasurableSet S) (f : Lp ℂ 2 planeMeasure) :
    verticalL2Projection p w (l2Indicator planeMeasure (Prod.fst ⁻¹' S) (hS.preimage measurable_fst) f)=
      l2Indicator planeMeasure (Prod.fst ⁻¹' S) (hS.preimage measurable_fst) (verticalL2Projection p w f) := by
  rw [verticalL2Projection_eq_profile _ _ hw,verticalL2Projection_eq_profile _ _ hw]
  exact verticalConvolutionLp_horizontal_indicator _ _ _ S hS f

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SchwartzConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complex conjugation reflects the Fourier support of an actual
Schwartz function, and preserves its L2 norm and pointwise size. -/
noncomputable section
open MeasureTheory Function
open scoped ENNReal ComplexConjugate
namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem planarFourier_conj (f : SchwartzMap (ℝ×ℝ) ℂ) (omega : ℝ×ℝ) :
    planarFourier (schwartzConj f) omega=conj (planarFourier f (-omega)) := by
  unfold planarFourier
  rw [←integral_conj]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [schwartzConj_apply,Circle.smul_def,smul_eq_mul,Real.fourierChar_apply,map_mul,
    Prod.fst_neg,Prod.snd_neg,mul_neg,neg_add_rev,neg_neg,←Complex.exp_conj,Complex.conj_ofReal,Complex.conj_I]
  congr 2
  push_cast
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_L2Conjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conjugation is an isometric real-linear involution of complex L2. -/
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace LipschitzHilbert
variable {X : Type*} [MeasurableSpace X]

theorem l2Conj_coe (mu : Measure X) (f : Lp ℂ 2 mu) :
    l2Conj mu f=ᵐ[mu] fun x => conj (f x) :=
  Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL f

theorem l2Conj_norm (mu : Measure X) (f : Lp ℂ 2 mu) : ‖l2Conj mu f‖=‖f‖ := by
  rw [Lp.norm_def,Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [l2Conj_coe mu f] with x hx
  rw [hx,Complex.norm_conj]

theorem l2Conj_onSchwartz (f : SchwartzMap (ℝ×ℝ) ℂ) :
    l2Conj PacketRepresentation.planeMeasure (f.toLp 2 PacketRepresentation.planeMeasure)=
      (schwartzConj f).toLp 2 PacketRepresentation.planeMeasure := by
  apply Lp.ext
  filter_upwards [l2Conj_coe PacketRepresentation.planeMeasure (f.toLp 2 PacketRepresentation.planeMeasure),
    (f.memLp 2 PacketRepresentation.planeMeasure).coeFn_toLp,
    ((schwartzConj f).memLp 2 PacketRepresentation.planeMeasure).coeFn_toLp] with x hx hfx hcx
  change (f.toLp 2 PacketRepresentation.planeMeasure) x=f x at hfx
  change ((schwartzConj f).toLp 2 PacketRepresentation.planeMeasure) x=schwartzConj f x at hcx
  rw [hx,hfx,hcx,schwartzConj_apply]

theorem l2_maps_eq_onSchwartz
    (T S : Lp ℂ 2 PacketRepresentation.planeMeasure →L[ℝ] Lp ℂ 2 PacketRepresentation.planeMeasure)
    (h : ∀ f : SchwartzMap (ℝ×ℝ) ℂ,
      T (f.toLp 2 PacketRepresentation.planeMeasure)=S (f.toLp 2 PacketRepresentation.planeMeasure)) : T=S := by
  apply DFunLike.coe_injective
  apply T.continuous.ext_on (SchwartzMap.denseRange_toLpCLM (F:=ℂ)
    (by norm_num : (2:ℝ≥0∞)≠⊤)) S.continuous
  rintro _ ⟨f,rfl⟩
  exact h f

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ReflectedBandProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Negative vertical bands are conjugates of positive vertical bands. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem conjugateReflectedCutoff_projection (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    schwartzVerticalProjection (conjugateReflectedCutoff p) w 0 f=
      schwartzConj (schwartzVerticalProjection p w 0 (schwartzConj f)) := by
  apply planar_schwartz_ext_fourier
  intro omega
  simp only [planarFourier_conj,schwartzVerticalProjection_fourier,
    conjugateReflectedCutoff_apply,sub_zero,Prod.snd_neg,mul_neg,map_mul,neg_neg,
    starRingEnd_apply,star_star]

theorem sharpTimeKernel_conj (epsilon R t : ℝ) :
    conj (sharpTimeKernel epsilon R t)=sharpTimeKernel epsilon R t := by
  unfold sharpTimeKernel
  split_ifs <;> simp

theorem shortSlopeOperator_conj (K : ℝ → ℂ) (hK : ∀ t, conj (K t)=K t)
    (u : (ℝ×ℝ) → ℝ) (f : (ℝ×ℝ) → ℂ) (z : ℝ×ℝ) :
    shortSlopeOperator K u (fun y => conj (f y)) z=conj (shortSlopeOperator K u f z) := by
  unfold shortSlopeOperator
  rw [←integral_conj]
  apply integral_congr_ae
  filter_upwards [] with t
  split_ifs <;> simp only [map_mul,hK,map_zero]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_OperatorConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conjugation identities extend from actual Schwartz integrals to
continuous L2 operators by density. -/
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem verticalL2Projection_reflected (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w) :
    (verticalL2Projection (conjugateReflectedCutoff p) w).restrictScalars ℝ=
      (l2Conj planeMeasure).comp
        (((verticalL2Projection p w).restrictScalars ℝ).comp (l2Conj planeMeasure)) := by
  apply l2_maps_eq_onSchwartz
  intro f
  change verticalL2Projection (conjugateReflectedCutoff p) w (f.toLp 2 planeMeasure)=
    l2Conj planeMeasure (verticalL2Projection p w (l2Conj planeMeasure (f.toLp 2 planeMeasure)))
  rw [l2Conj_onSchwartz,verticalL2Projection_onSchwartz _ w hw,
    verticalL2Projection_onSchwartz _ w hw,l2Conj_onSchwartz,
    conjugateReflectedCutoff_projection]

theorem shortL2Operator_conjugate (K : ℝ → ℂ) (hKm : Measurable K) (hKi : Integrable K)
    (hK : ∀ t, conj (K t)=K t) (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) :
    ((shortL2Operator K hKm hKi u hu).restrictScalars ℝ).comp (l2Conj planeMeasure)=
      (l2Conj planeMeasure).comp ((shortL2Operator K hKm hKi u hu).restrictScalars ℝ) := by
  apply l2_maps_eq_onSchwartz
  intro f
  change shortL2Operator K hKm hKi u hu (l2Conj planeMeasure (f.toLp 2 planeMeasure))=
    l2Conj planeMeasure (shortL2Operator K hKm hKi u hu (f.toLp 2 planeMeasure))
  rw [l2Conj_onSchwartz,shortL2Operator_onSchwartz,shortL2Operator_onSchwartz]
  apply Lp.ext
  filter_upwards [(shortSchwartz_memLp K hKm hKi u hu (schwartzConj f)).coeFn_toLp,
    l2Conj_coe planeMeasure (shortSchwartzToL2 K hKm hKi u hu f),
    (shortSchwartz_memLp K hKm hKi u hu f).coeFn_toLp] with z hcf hc hf
  change (shortSchwartzToL2 K hKm hKi u hu (schwartzConj f)) z=_ at hcf
  change (shortSchwartzToL2 K hKm hKi u hu f) z=shortSlopeOperator K u f z at hf
  rw [hcf,hc,hf]
  exact shortSlopeOperator_conj K hK u f z

theorem l2Indicator_conjugate (S : Set (ℝ×ℝ)) (hS : MeasurableSet S) :
    ((l2Indicator planeMeasure S hS).restrictScalars ℝ).comp (l2Conj planeMeasure)=
      (l2Conj planeMeasure).comp ((l2Indicator planeMeasure S hS).restrictScalars ℝ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [l2Indicator_coe planeMeasure S hS (l2Conj planeMeasure f),
    l2Conj_coe planeMeasure f,l2Conj_coe planeMeasure (l2Indicator planeMeasure S hS f),
    l2Indicator_coe planeMeasure S hS f] with z hl hc hr hs
  change (l2Indicator planeMeasure S hS (l2Conj planeMeasure f)) z=
    (l2Conj planeMeasure (l2Indicator planeMeasure S hS f)) z
  rw [hl,hr,hs]
  by_cases hz : z∈S
  · simp only [Set.indicator_of_mem hz,hc]
  · simp only [Set.indicator_of_notMem hz,map_zero]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalProjectionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Addition and exact absorption of vertical multipliers on Schwartz
functions and their continuous L2 realizations. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem verticalL2Projection_add_profile (p q : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w) :
    verticalL2Projection (p+q) w=verticalL2Projection p w+verticalL2Projection q w := by
  have h := l2_maps_eq_onSchwartz ((verticalL2Projection (p+q) w).restrictScalars ℝ)
    ((verticalL2Projection p w+verticalL2Projection q w).restrictScalars ℝ) (fun f => by
      change verticalL2Projection (p+q) w (f.toLp 2 planeMeasure)=
        verticalL2Projection p w (f.toLp 2 planeMeasure)+verticalL2Projection q w (f.toLp 2 planeMeasure)
      rw [verticalL2Projection_onSchwartz _ _ hw,verticalL2Projection_onSchwartz _ _ hw,
        verticalL2Projection_onSchwartz _ _ hw,schwartzVerticalProjection_add_profile]
      exact map_add (SchwartzMap.toLpCLM ℂ ℂ 2 planeMeasure) _ _)
  apply ContinuousLinearMap.ext
  intro f
  exact congrArg (fun T : Lp ℂ 2 planeMeasure →L[ℝ] Lp ℂ 2 planeMeasure => T f) h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LocalizedSubbandOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bound for an enlarged band controls every subband, with the norm
of the projected input. Horizontal localization commutes with projections. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem verticalL2Projection_strip (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (l r : ℝ) (f : Lp ℂ 2 planeMeasure) :
    verticalL2Projection p w (stripL2Cutoff l r f)=stripL2Cutoff l r (verticalL2Projection p w f) :=
  verticalL2Projection_horizontal_indicator p w hw (Set.Icc l r) measurableSet_Icc f

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortSlopeLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous short-time operator agrees on every L2 class with
its integral representative. This permits exact support localization. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem shortSample_measurable (u : (ℝ×ℝ) → ℝ) (hu : Measurable u)
    (f : (ℝ×ℝ) → ℂ) (hf : Measurable f) :
    Measurable (fun p : ℝ×(ℝ×ℝ) => shortSample u f p.1 p.2) := by
  unfold shortSample
  exact (hf.comp (by fun_prop)).ite (measurableSet_le (by fun_prop) measurable_const) measurable_const

theorem shortSample_energy (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hf : MemLp f 2 planeMeasure) (t : ℝ) :
    MemLp (shortSample u f t) 2 planeMeasure ∧
      (∫ z, ‖shortSample u f t z‖^2 ∂planeMeasure)≤4*∫ z, ‖f z‖^2 ∂planeMeasure := by
  unfold shortSample
  by_cases ht : |t|≤1/4
  · simpa only [shortSample,ite_eq_left ht,Function.comp_def,verticalSampling,sub_zero] using
      verticalSampling_energy u hu t t 0 ht f hfm hf
  · simp only [ite_eq_right ht,norm_zero,zero_pow (by decide : 2≠0),integral_zero]
    exact ⟨MemLp.zero',by positivity⟩

theorem shortSample_congr_ae (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f g : (ℝ×ℝ) → ℂ) (hfg : f=ᵐ[planeMeasure] g) (t : ℝ) :
    shortSample u f t=ᵐ[planeMeasure] shortSample u g t := by
  unfold shortSample
  by_cases ht : |t|≤1/4
  · have hm := verticalSampling_measurable u hu.continuous.measurable t t 0
    have hq : Measure.QuasiMeasurePreserving (verticalSampling u t t 0) planeMeasure planeMeasure :=
      ⟨hm,Measure.absolutelyContinuous_of_le_smul
        (planar_map_le_four _ hm (verticalSampling_antilipschitz u hu t t 0 ht))⟩
    filter_upwards [hq.ae hfg] with z hz
    simpa only [ite_eq_left ht,verticalSampling,sub_zero] using hz
  · simp only [ite_eq_right ht]
    exact Filter.Eventually.of_forall fun _ => rfl

theorem shortSlopeOperator_congr_ae (K : ℝ → ℂ)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f g : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hfg : f=ᵐ[planeMeasure] g) :
    shortSlopeOperator K u f=ᵐ[planeMeasure] shortSlopeOperator K u g := by
  have he : ∀ᵐ t ∂(volume : Measure ℝ), shortSample u f t=ᵐ[planeMeasure] shortSample u g t :=
    Filter.Eventually.of_forall (shortSample_congr_ae u hu f g hfg)
  have hm : MeasurableSet {p : ℝ×(ℝ×ℝ) | shortSample u f p.1 p.2=shortSample u g p.1 p.2} :=
    measurableSet_eq_fun (shortSample_measurable u hu.continuous.measurable f hfm)
      (shortSample_measurable u hu.continuous.measurable g hgm)
  have hs := (Measure.ae_ae_comm hm).mp he
  filter_upwards [hs] with z hz
  have hrep (h : (ℝ×ℝ) → ℂ) : shortSlopeOperator K u h z=∫ t, K t*shortSample u h t z := by
    unfold shortSlopeOperator shortSample
    congr 1
    funext t
    split_ifs <;> simp
  rw [hrep,hrep]
  apply integral_congr_ae
  filter_upwards [hz] with t ht
  rw [ht]

theorem shortSlopeOperator_integrand_ae (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hf : MemLp f 2 planeMeasure) :
    ∀ᵐ z ∂planeMeasure, Integrable (fun t => K t*shortSample u f t z) := by
  let H := fun p : ℝ×(ℝ×ℝ) => ‖K p.1‖*‖shortSample u f p.1 p.2‖^2
  have hsm := shortSample_measurable u hu.continuous.measurable f hfm
  have hm : Measurable H := (hKm.comp measurable_fst).norm.mul (hsm.norm.pow_const 2)
  have hzero (p) : 0≤H p := mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hi : Integrable H (volume.prod planeMeasure) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    constructor
    · exact Filter.Eventually.of_forall fun t =>
        ((shortSample_energy u hu f hfm hf t).1.integrable_norm_pow (by decide : 2≠0)).const_mul ‖K t‖
    · apply (hK.norm.mul_const (4*∫ z, ‖f z‖^2 ∂planeMeasure)).mono'
        hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      filter_upwards [] with t
      simp only [Real.norm_of_nonneg (hzero _)]
      rw [Real.norm_of_nonneg (integral_nonneg fun z => hzero (t,z))]
      change (∫ z, ‖K t‖*‖shortSample u f t z‖^2 ∂planeMeasure)≤_
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (shortSample_energy u hu f hfm hf t).2 (norm_nonneg _)
  filter_upwards [hi.prod_left_ae] with z hz
  have hs : Measurable (fun t => shortSample u f t z) := by
    exact hsm.comp (measurable_id.prodMk measurable_const)
  have hc := (weighted_integral_cauchySchwarz volume (fun t => ‖K t‖)
    (fun t => ‖shortSample u f t z‖) hKm.norm hs.norm (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) hK.norm hz).1
  exact hc.mono' ((hKm.mul hs).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => le_of_eq (norm_mul _ _))

theorem shortSlopeOperator_sub_ae (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f g : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 planeMeasure) (hg : MemLp g 2 planeMeasure) :
    shortSlopeOperator K u (f-g)=ᵐ[planeMeasure] shortSlopeOperator K u f-shortSlopeOperator K u g := by
  filter_upwards [shortSlopeOperator_integrand_ae K hKm hK u hu f hfm hf,
    shortSlopeOperator_integrand_ae K hKm hK u hu g hgm hg] with z hfz hgz
  have hrep (h : (ℝ×ℝ) → ℂ) : shortSlopeOperator K u h z=∫ t, K t*shortSample u h t z := by
    unfold shortSlopeOperator shortSample
    congr 1
    funext t
    split_ifs <;> simp
  simp only [Pi.sub_apply,hrep]
  rw [←integral_sub hfz hgz]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold shortSample
  split_ifs <;> simp [mul_sub]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortSlopeLpRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual integral realization of the continuous L2 short-time map. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem shortSlopeLp_coe (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f : Lp ℂ 2 planeMeasure) :
    (shortSlopeLp K hKm hK u hu f : (ℝ×ℝ) → ℂ)=ᵐ[planeMeasure] shortSlopeOperator K u f :=
  MemLp.coeFn_toLp _

theorem shortSlopeLp_toLp (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hf : MemLp f 2 planeMeasure) :
    shortSlopeLp K hKm hK u hu (hf.toLp f)=
      (shortSlopeOperator_energy K hKm hK u hu f hfm hf).1.toLp (shortSlopeOperator K u f) := by
  apply Lp.ext
  exact (shortSlopeLp_coe K hKm hK u hu _).trans
    ((shortSlopeOperator_congr_ae K u hu _ f (Lp.stronglyMeasurable (hf.toLp f)).measurable
      hfm hf.coeFn_toLp).trans (MemLp.coeFn_toLp _).symm)

theorem shortSlopeLp_sub (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f g : Lp ℂ 2 planeMeasure) :
    shortSlopeLp K hKm hK u hu (f-g)=shortSlopeLp K hKm hK u hu f-shortSlopeLp K hKm hK u hu g := by
  apply Lp.ext
  have hc := shortSlopeOperator_congr_ae K u hu (show Lp ℂ 2 planeMeasure from f-g)
    ((f : (ℝ×ℝ) → ℂ)-(g : (ℝ×ℝ) → ℂ)) (Lp.stronglyMeasurable (f-g)).measurable
    ((Lp.stronglyMeasurable f).measurable.sub (Lp.stronglyMeasurable g).measurable) (Lp.coeFn_sub f g)
  have hs := shortSlopeOperator_sub_ae K hKm hK u hu f g (Lp.stronglyMeasurable f).measurable
    (Lp.stronglyMeasurable g).measurable (Lp.memLp f) (Lp.memLp g)
  filter_upwards [shortSlopeLp_coe K hKm hK u hu (f-g),hc,hs,
    shortSlopeLp_coe K hKm hK u hu f,shortSlopeLp_coe K hKm hK u hu g,
    Lp.coeFn_sub (shortSlopeLp K hKm hK u hu f) (shortSlopeLp K hKm hK u hu g)]
    with z h1 h2 h3 h4 h5 h6
  rw [h1,h2,h3,h6]
  simp only [Pi.sub_apply,h4,h5]

theorem shortSlopeLp_norm (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f : Lp ℂ 2 planeMeasure) :
    ‖shortSlopeLp K hKm hK u hu f‖≤(2*∫ t, ‖K t‖)*‖f‖ := by
  have h := (shortSlopeOperator_energy K hKm hK u hu f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).2
  rw [←memLp_toL2_norm_sq planeMeasure _ (Lp.memLp f),Lp.toLp_coeFn,
    ←memLp_toL2_norm_sq planeMeasure _
      (shortSlopeOperator_energy K hKm hK u hu f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).1] at h
  change ‖shortSlopeLp K hKm hK u hu f‖^2≤4*(∫ t, ‖K t‖)^2*‖f‖^2 at h
  have hn : 0≤2*∫ t, ‖K t‖ := mul_nonneg (by norm_num) (integral_nonneg fun _ => norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hn (norm_nonneg f))).mp
  calc
    _ ≤ 4*(∫ t, ‖K t‖)^2*‖f‖^2 := h
    _ = _ := by ring

theorem shortSlopeLp_continuous (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) : Continuous (shortSlopeLp K hKm hK u hu) := by
  apply LipschitzWith.continuous (K:=⟨2*∫ t, ‖K t‖,by positivity⟩)
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [dist_eq_norm,dist_eq_norm,←shortSlopeLp_sub]
  exact shortSlopeLp_norm K hKm hK u hu (f-g)

theorem shortL2Operator_eq_actual (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f : Lp ℂ 2 planeMeasure) :
    shortL2Operator K hKm hK u hu f=shortSlopeLp K hKm hK u hu f := by
  have hd : DenseRange (fun g : SchwartzMap (ℝ×ℝ) ℂ => g.toLp 2 planeMeasure) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  refine hd.induction_on f ?_ ?_
  · exact isClosed_eq (shortL2Operator K hKm hK u hu).continuous (shortSlopeLp_continuous K hKm hK u hu)
  · intro g
    rw [shortL2Operator_onSchwartz]
    change shortSchwartzToL2 K hKm hK u hu g=
      shortSlopeLp K hKm hK u hu ((g.memLp 2 planeMeasure).toLp (g : (ℝ×ℝ) → ℂ))
    rw [shortSlopeLp_toLp K hKm hK u hu g g.continuous.measurable (g.memLp 2 planeMeasure)]
    rfl

theorem shortL2Operator_coe (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f : Lp ℂ 2 planeMeasure) :
    (shortL2Operator K hKm hK u hu f : (ℝ×ℝ) → ℂ)=ᵐ[planeMeasure] shortSlopeOperator K u f := by
  rw [shortL2Operator_eq_actual]
  exact shortSlopeLp_coe K hKm hK u hu f

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortHorizontalLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite horizontal propagation for the actual truncated operator.
An output set sees only its horizontal enlargement by the outer radius. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem shortSlopeOperator_horizontal_localization (K : ℝ → ℂ)
    (u : (ℝ×ℝ) → ℝ) (f : (ℝ×ℝ) → ℂ) (S T : Set ℝ) (R : ℝ)
    (hK : ∀ t, R < |t| → K t=0) (hST : ∀ x∈S, ∀ t : ℝ, |t|≤R → x-t∈T) :
    (Prod.fst ⁻¹' S).indicator (shortSlopeOperator K u ((Prod.fst ⁻¹' T).indicator f))=
      (Prod.fst ⁻¹' S).indicator (shortSlopeOperator K u f) := by
  funext z
  by_cases hz : z.1∈S
  · rw [Set.indicator_of_mem (show z∈Prod.fst ⁻¹' S from hz),
      Set.indicator_of_mem (show z∈Prod.fst ⁻¹' S from hz)]
    unfold shortSlopeOperator
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases ht : |t|≤R
    · have hin : (z.1-t,z.2-t*u z)∈Prod.fst ⁻¹' T := hST z.1 hz t ht
      rw [Set.indicator_of_mem hin]
    · rw [hK t (lt_of_not_ge ht)]
      simp only [zero_mul]
  · simp only [Set.indicator_of_notMem (show z∉Prod.fst ⁻¹' S from hz)]

theorem shortL2Operator_horizontal_localization (K : ℝ → ℂ) (hKm : Measurable K) (hKi : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (S T : Set ℝ)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (R : ℝ)
    (hK : ∀ t, R < |t| → K t=0) (hST : ∀ x∈S, ∀ t : ℝ, |t|≤R → x-t∈T)
    (f : Lp ℂ 2 planeMeasure) :
    l2Indicator planeMeasure (Prod.fst ⁻¹' S) (hS.preimage measurable_fst)
      (shortL2Operator K hKm hKi u hu
        (l2Indicator planeMeasure (Prod.fst ⁻¹' T) (hT.preimage measurable_fst) f))=
      l2Indicator planeMeasure (Prod.fst ⁻¹' S) (hS.preimage measurable_fst)
        (shortL2Operator K hKm hKi u hu f) := by
  let M := l2Indicator planeMeasure (Prod.fst ⁻¹' T) (hT.preimage measurable_fst)
  have hc := shortSlopeOperator_congr_ae K u hu (M f) ((Prod.fst ⁻¹' T).indicator f)
    (Lp.stronglyMeasurable (M f)).measurable
    ((Lp.stronglyMeasurable f).measurable.indicator (hT.preimage measurable_fst))
    (l2Indicator_coe planeMeasure _ _ f)
  apply Lp.ext
  filter_upwards [l2Indicator_coe planeMeasure (Prod.fst ⁻¹' S) (hS.preimage measurable_fst)
      (shortL2Operator K hKm hKi u hu (M f)),
    l2Indicator_coe planeMeasure (Prod.fst ⁻¹' S) (hS.preimage measurable_fst)
      (shortL2Operator K hKm hKi u hu f),
    shortL2Operator_coe K hKm hKi u hu (M f),hc,
    shortL2Operator_coe K hKm hKi u hu f] with z h1 h2 h3 h4 h5
  rw [h1,h2]
  by_cases hz : z.1∈S
  · simp only [Set.indicator_of_mem (show z∈Prod.fst ⁻¹' S from hz)]
    rw [h3,h4,h5]
    have hraw := congrFun (shortSlopeOperator_horizontal_localization K u f S T R hK hST) z
    simpa only [Set.indicator_of_mem (show z∈Prod.fst ⁻¹' S from hz)] using hraw
  · simp only [Set.indicator_of_notMem (show z∉Prod.fst ⁻¹' S from hz)]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_L2SpatialPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Squaring and summing local L2 estimates over a measurable partition,
with a finite overlap bound for the enlarged input sets. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem l2Indicator_norm_sq (S : Set (ℝ×ℝ)) (hS : MeasurableSet S) (f : Lp ℂ 2 planeMeasure) :
    ‖l2Indicator planeMeasure S hS f‖^2=∫ z in S, ‖f z‖^2 ∂planeMeasure := by
  change ‖((Lp.memLp f).indicator hS).toLp (S.indicator f)‖^2=_
  rw [memLp_toL2_norm_sq]
  have he : (fun z => ‖S.indicator f z‖^2)=S.indicator (fun z => ‖f z‖^2) := by
    funext z
    by_cases hz : z∈S <;> simp [Set.indicator,hz]
  rw [he,integral_indicator hS]

theorem l2Indicator_finite_overlap {ι : Type*} (J : Finset ι) (S : ι → Set (ℝ×ℝ))
    (hS : ∀ i, MeasurableSet (S i)) (D : ℝ)
    (hD : ∀ z, (∑ i∈J, (S i).indicator (fun _ => (1:ℝ)) z)≤D)
    (f : Lp ℂ 2 planeMeasure) :
    (∑ i∈J, ‖l2Indicator planeMeasure (S i) (hS i) f‖^2)≤D*‖f‖^2 := by
  have hfi := (Lp.memLp f).integrable_norm_pow (by decide : 2≠0)
  have he (i : ι) : (fun z => (S i).indicator (fun _ => (1:ℝ)) z*‖f z‖^2)=
      (S i).indicator (fun z => ‖f z‖^2) := by
    funext z
    by_cases hz : z∈S i <;> simp [Set.indicator,hz]
  calc
    _ = ∑ i∈J, ∫ z, (S i).indicator (fun _ => (1:ℝ)) z*‖f z‖^2 ∂planeMeasure := by
      apply Finset.sum_congr rfl
      intro i _
      rw [l2Indicator_norm_sq,he,integral_indicator (hS i)]
    _ = ∫ z, ∑ i∈J, (S i).indicator (fun _ => (1:ℝ)) z*‖f z‖^2 ∂planeMeasure := by
      symm
      apply integral_finsetSum
      intro i _
      rw [he]
      exact hfi.indicator (hS i)
    _ ≤ ∫ z, D*‖f z‖^2 ∂planeMeasure := by
      apply integral_mono
      · apply integrable_finsetSum
        intro i _
        rw [he]
        exact hfi.indicator (hS i)
      · exact hfi.const_mul D
      · intro z
        change (∑ i∈J, (S i).indicator (fun _ => (1:ℝ)) z*‖f z‖^2)≤D*‖f z‖^2
        rw [←Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (hD z) (sq_nonneg _)
    _ = _ := by
      rw [integral_const_mul,←memLp_toL2_norm_sq planeMeasure _ (Lp.memLp f),Lp.toLp_coeFn]

theorem l2Indicator_partition_bound {ι : Type*} [Countable ι]
    (Q S : ι → Set (ℝ×ℝ)) (hQ : ∀ i, MeasurableSet (Q i)) (hS : ∀ i, MeasurableSet (S i))
    (hdisjoint : Pairwise (fun i j => Disjoint (Q i) (Q j))) (hcover : ⋃ i, Q i=univ)
    (B D : ℝ) (hB : 0≤B) (f g : Lp ℂ 2 planeMeasure)
    (hlocal : ∀ i, ‖l2Indicator planeMeasure (Q i) (hQ i) g‖^2≤
      B*‖l2Indicator planeMeasure (S i) (hS i) f‖^2)
    (hover : ∀ J : Finset ι, ∀ z, (∑ i∈J, (S i).indicator (fun _ => (1:ℝ)) z)≤D) :
    ‖g‖^2≤B*D*‖f‖^2 := by
  have hg := (Lp.memLp g).integrable_norm_pow (by decide : 2≠0)
  have hpartition := integral_iUnion (μ:=planeMeasure) (f:=fun z => ‖g z‖^2)
    hQ hdisjoint (by simpa only [hcover,integrableOn_univ] using hg)
  rw [hcover,setIntegral_univ] at hpartition
  have henergy : ‖g‖^2=∫ z, ‖g z‖^2 ∂planeMeasure := by
    simpa only [Lp.toLp_coeFn] using memLp_toL2_norm_sq planeMeasure g (Lp.memLp g)
  rw [henergy,hpartition]
  apply Real.tsum_le_of_sum_le (fun i => integral_nonneg fun _ => sq_nonneg _)
  intro J
  calc
    _ = ∑ i∈J, ‖l2Indicator planeMeasure (Q i) (hQ i) g‖^2 := by
      exact Finset.sum_congr rfl (fun i _ => (l2Indicator_norm_sq (Q i) (hQ i) g).symm)
    _ ≤ ∑ i∈J, B*‖l2Indicator planeMeasure (S i) (hS i) f‖^2 := Finset.sum_le_sum fun i _ => hlocal i
    _ = B*(∑ i∈J, ‖l2Indicator planeMeasure (S i) (hS i) f‖^2) := (Finset.mul_sum _ _ _).symm
    _ ≤ B*(D*‖f‖^2) := mul_le_mul_of_nonneg_left (l2Indicator_finite_overlap J S hS D (hover J) f) hB
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_HorizontalStripCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete partition into horizontal strips; their one-cell
extensions have uniformly bounded overlap and contain short translates. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem horizontalCell_floor (d : ℝ) (hd : 0<d) (x : ℝ) : x∈horizontalCell d ⌊x/d⌋ := by
  have hlo := mul_le_mul_of_nonneg_right (Int.floor_le (x/d)) hd.le
  have hhi := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (x/d)) hd
  rw [div_mul_cancel₀ _ hd.ne'] at hlo hhi
  exact ⟨hlo,hhi⟩

theorem horizontalCell_disjoint (d : ℝ) (hd : 0<d) :
    Pairwise (fun j k : ℤ => Disjoint (horizontalCell d j) (horizontalCell d k)) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro x hxj hxk
  rcases lt_or_gt_of_ne hjk with hlt|hlt
  · have h : (j:ℝ)+1≤k := by exact_mod_cast (show j+1≤k by omega)
    have hm := mul_le_mul_of_nonneg_right h hd.le
    exact (not_lt_of_ge (hm.trans hxk.1)) hxj.2
  · have h : (k:ℝ)+1≤j := by exact_mod_cast (show k+1≤j by omega)
    have hm := mul_le_mul_of_nonneg_right h hd.le
    exact (not_lt_of_ge (hm.trans hxj.1)) hxk.2

theorem horizontalCell_subset (d : ℝ) (hd : 0<d) (j : ℤ) :
    horizontalCell d j⊆horizontalEnlargement d j := by
  intro x hx
  constructor
  · linarith only [hx.1,hd]
  · linarith only [hx.2,hd]

theorem horizontalEnlargement_translate (d : ℝ) (_hd : 0<d) (j : ℤ)
    (x : ℝ) (hx : x∈horizontalCell d j) (t : ℝ) (ht : |t|≤d) :
    x-t∈horizontalEnlargement d j := by
  have ht' := abs_le.mp ht
  constructor
  · change ((j:ℝ)-1)*d≤x-t
    linarith only [hx.1,ht'.2]
  · change x-t≤((j:ℝ)+2)*d
    linarith only [hx.2,ht'.1]

theorem horizontalEnlargement_index (d : ℝ) (hd : 0<d) (x : ℝ) (j : ℤ)
    (hx : x∈horizontalEnlargement d j) :
    j∈Finset.Icc (⌊x/d⌋-2) (⌊x/d⌋+2) := by
  have hf := horizontalCell_floor d hd x
  have hleft : (⌊x/d⌋:ℝ)-2≤j := by
    have h : (((⌊x/d⌋:ℤ):ℝ)-2-(j:ℝ))*d≤0 := by
      dsimp only [horizontalCell,horizontalEnlargement,mem_Ico,mem_Icc] at hf hx
      nlinarith only [hf.1,hx.2,hd]
    nlinarith only [h,hd]
  have hright : (j:ℝ)<(⌊x/d⌋:ℝ)+2 := by
    have h : ((j:ℝ)-((⌊x/d⌋:ℤ):ℝ)-2)*d<0 := by
      dsimp only [horizontalCell,horizontalEnlargement,mem_Ico,mem_Icc] at hf hx
      nlinarith only [hf.2,hx.1,hd]
    nlinarith only [h,hd]
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast hleft
  · exact_mod_cast hright.le

theorem horizontalEnlargement_overlap (d : ℝ) (hd : 0<d) (J : Finset ℤ) (x : ℝ) :
    (∑ j∈J, (horizontalEnlargement d j).indicator (fun _ => (1:ℝ)) x)≤5 := by
  classical
  let A := J.filter (fun j => x∈horizontalEnlargement d j)
  have hsub : A⊆Finset.Icc (⌊x/d⌋-2) (⌊x/d⌋+2) := fun j hj =>
    horizontalEnlargement_index d hd x j (Finset.mem_filter.mp hj).2
  have hc : A.card≤5 := by
    have h := Finset.card_le_card hsub
    rw [Int.card_Icc] at h
    omega
  have heq : (∑ j∈J, (horizontalEnlargement d j).indicator (fun _ => (1:ℝ)) x)=(A.card:ℝ) := by
    simp only [Set.indicator]
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
    rfl
  rw [heq]
  exact_mod_cast hc

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_GlobalBandLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact patching of the local band theorem over disjoint horizontal
strips, with a uniform finite-overlap cost. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem bandL2Operator_horizontal_patch (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (d : ℝ) (hd : 0<d) (hRd : R≤d) (j : ℤ) (f : Lp ℂ 2 planeMeasure) :
    l2Indicator planeMeasure ((Prod.fst : (ℝ×ℝ) → ℝ) ⁻¹' horizontalCell d j) (measurableSet_Ico.preimage measurable_fst)
      (bandL2Operator (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
        (sharpTimeKernel_integrable epsilon R he hR) (fun z => field (planeCoordinates z))
        (by simpa only [mul_one] using product_slope_lipschitz field hfield) p w f)=
    l2Indicator planeMeasure ((Prod.fst : (ℝ×ℝ) → ℝ) ⁻¹' horizontalCell d j) (measurableSet_Ico.preimage measurable_fst)
      (localizedSharpBandOperator epsilon R he hR field hfield p w (((j:ℝ)-1)*d) (((j:ℝ)+2)*d) f) := by
  let lo := ((j:ℝ)-1)*d
  let hi := ((j:ℝ)+2)*d
  let M := stripL2Cutoff lo hi
  let Q := l2Indicator planeMeasure ((Prod.fst : (ℝ×ℝ) → ℝ) ⁻¹' horizontalCell d j) (measurableSet_Ico.preimage measurable_fst)
  let T := shortL2Operator (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
    (sharpTimeKernel_integrable epsilon R he hR) (fun z => field (planeCoordinates z))
    (by simpa only [mul_one] using product_slope_lipschitz field hfield)
  have hsub : (Prod.fst : (ℝ×ℝ) → ℝ) ⁻¹' horizontalCell d j⊆(Prod.fst : (ℝ×ℝ) → ℝ) ⁻¹' horizontalEnlargement d j :=
    preimage_mono (horizontalCell_subset d hd j)
  have hQM (g : Lp ℂ 2 planeMeasure) : Q (M g)=Q g :=
    l2Indicator_nested planeMeasure _ _ _ _ hsub g
  have hloc := shortL2Operator_horizontal_localization (sharpTimeKernel epsilon R)
    (sharpTimeKernel_measurable epsilon R) (sharpTimeKernel_integrable epsilon R he hR)
    (fun z => field (planeCoordinates z)) (by simpa only [mul_one] using product_slope_lipschitz field hfield)
    (horizontalCell d j) (horizontalEnlargement d j) measurableSet_Ico measurableSet_Icc R
    (fun t ht => by
      unfold sharpTimeKernel
      rw [ite_eq_right (by intro h; linarith only [h.2,ht])])
    (fun x hx t ht => horizontalEnlargement_translate d hd j x hx t (ht.trans hRd))
    (verticalL2Projection p w f)
  change Q (T (M (verticalL2Projection p w f)))=Q (T (verticalL2Projection p w f)) at hloc
  change Q (T (verticalL2Projection p w f))=Q (M (T (verticalL2Projection p w (M f))))
  rw [hQM]
  rw [verticalL2Projection_strip p w hw lo hi f]
  exact hloc.symm

theorem bandL2Operator_global_from_local (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (d : ℝ) (hd : 0<d) (hRd : R≤d) (C : ℝ) (hC : 0≤C)
    (hlocal : ∀ j : ℤ,
      ‖localizedSharpBandOperator epsilon R he hR field hfield p w (((j:ℝ)-1)*d) (((j:ℝ)+2)*d)‖≤C)
    (f : Lp ℂ 2 planeMeasure) :
    ‖bandL2Operator (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
      (sharpTimeKernel_integrable epsilon R he hR) (fun z => field (planeCoordinates z))
      (by simpa only [mul_one] using product_slope_lipschitz field hfield) p w f‖≤3*C*‖f‖ := by
  let Q := fun j : ℤ => (Prod.fst : (ℝ×ℝ) → ℝ) ⁻¹' horizontalCell d j
  let S := fun j : ℤ => (Prod.fst : (ℝ×ℝ) → ℝ) ⁻¹' horizontalEnlargement d j
  let T := bandL2Operator (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
    (sharpTimeKernel_integrable epsilon R he hR) (fun z => field (planeCoordinates z))
    (by simpa only [mul_one] using product_slope_lipschitz field hfield) p w
  have hbound (j : ℤ) : ‖l2Indicator planeMeasure (Q j) (measurableSet_Ico.preimage measurable_fst) (T f)‖≤
      C*‖l2Indicator planeMeasure (S j) (measurableSet_Icc.preimage measurable_fst) f‖ := by
    let lo := ((j:ℝ)-1)*d
    let hi := ((j:ℝ)+2)*d
    let A := localizedSharpBandOperator epsilon R he hR field hfield p w lo hi
    let M := stripL2Cutoff lo hi
    have hid : A (M f)=A f := by
      change stripL2Cutoff lo hi (shortL2Operator _ _ _ _ _
        (verticalL2Projection p w (M (M f))))=stripL2Cutoff lo hi (shortL2Operator _ _ _ _ _
        (verticalL2Projection p w (M f)))
      rw [show M (M f)=M f from l2Indicator_idempotent planeMeasure _ _ f]
    have hA : ‖A f‖≤C*‖M f‖ := by
      rw [←hid]
      exact (A.le_opNorm (M f)).trans (mul_le_mul_of_nonneg_right (hlocal j) (norm_nonneg _))
    rw [show T f=bandL2Operator (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
      (sharpTimeKernel_integrable epsilon R he hR) (fun z => field (planeCoordinates z))
      (by simpa only [mul_one] using product_slope_lipschitz field hfield) p w f from rfl]
    rw [bandL2Operator_horizontal_patch epsilon R he hR field hfield p w hw d hd hRd j f]
    exact (l2Indicator_norm_le planeMeasure _ _ (A f)).trans hA
  have hcover : ⋃ j : ℤ, Q j=univ := by
    ext z
    simp only [Q,mem_iUnion,mem_preimage,mem_univ,iff_true]
    exact ⟨⌊z.1/d⌋,horizontalCell_floor d hd z.1⟩
  have hdisjoint : Pairwise (fun j k => Disjoint (Q j) (Q k)) := fun j k hjk =>
    (horizontalCell_disjoint d hd hjk).preimage _
  have he := l2Indicator_partition_bound Q S (fun _ => measurableSet_Ico.preimage measurable_fst)
    (fun _ => measurableSet_Icc.preimage measurable_fst) hdisjoint hcover (C^2) 5 (sq_nonneg C) f (T f)
    (fun j => by
      have h := pow_le_pow_left₀ (norm_nonneg _) (hbound j) 2
      simpa only [mul_pow] using h)
    (fun J z => horizontalEnlargement_overlap d hd J z.1)
  change ‖T f‖≤3*C*‖f‖
  have htarget : 0≤3*C*‖f‖ := by positivity
  nlinarith only [he,htarget,norm_nonneg (T f),sq_nonneg (C*‖f‖)]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NegativeBandOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reflected negative band inherits the positive-band L2 constant
through the exact conjugation symmetry of the real Hilbert kernel. -/
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem localizedSharpBandOperator_reflected
    (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p : SchwartzMap ℝ ℂ)
    (w l r : ℝ) (hw : 0<w) (f : Lp ℂ 2 planeMeasure) :
    localizedSharpBandOperator epsilon R he hR field hfield (conjugateReflectedCutoff p) w l r f=
      l2Conj planeMeasure (localizedSharpBandOperator epsilon R he hR field hfield p w l r
        (l2Conj planeMeasure f)) := by
  let C := l2Conj planeMeasure
  let M := stripL2Cutoff l r
  let K := sharpTimeKernel epsilon R
  let u := fun z : ℝ×ℝ => field (planeCoordinates z)
  have hu : LipschitzWith 2 u := by simpa only [u,mul_one] using product_slope_lipschitz field hfield
  let S := shortL2Operator K (sharpTimeKernel_measurable epsilon R)
    (sharpTimeKernel_integrable epsilon R he hR) u hu
  have hM (g : Lp ℂ 2 planeMeasure) : M (C g)=C (M g) :=
    congrArg (fun T : Lp ℂ 2 planeMeasure →L[ℝ] Lp ℂ 2 planeMeasure => T g)
      (l2Indicator_conjugate (horizontalStrip l r) (horizontalStrip_measurable l r))
  have hS (g : Lp ℂ 2 planeMeasure) : S (C g)=C (S g) :=
    congrArg (fun T : Lp ℂ 2 planeMeasure →L[ℝ] Lp ℂ 2 planeMeasure => T g)
      (shortL2Operator_conjugate K (sharpTimeKernel_measurable epsilon R)
        (sharpTimeKernel_integrable epsilon R he hR) (sharpTimeKernel_conj epsilon R) u hu)
  have hP (g : Lp ℂ 2 planeMeasure) : verticalL2Projection (conjugateReflectedCutoff p) w g=
      C (verticalL2Projection p w (C g)) :=
    congrArg (fun T : Lp ℂ 2 planeMeasure →L[ℝ] Lp ℂ 2 planeMeasure => T g)
      (verticalL2Projection_reflected p w hw)
  change M (S (verticalL2Projection (conjugateReflectedCutoff p) w (M f)))=
    C (M (S (verticalL2Projection p w (M (C f)))))
  rw [hP,hS,hM,←hM f]

theorem localized_negative_band_operator_norm (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (p : SchwartzMap ℝ ℂ) (hp : ∀ s, p s≠0 → 1 ≤ s ∧ s≤2) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R w : ℝ, (he : 0<epsilon) → (heR : epsilon≤R) → R≤1/4 → 0<w →
    ∀ (field : Plane → ℝ) (hfield : LipschitzWith 1 field), (∀ z, |field z|≤1/4) →
    ∀ l r : ℝ, 1200*(r-l)≤1 →
      ‖localizedSharpBandOperator epsilon R he (he.trans_le heR) field hfield
        (conjugateReflectedCutoff p) w l r‖≤C := by
  obtain ⟨C,hC,hbound⟩ := localized_sharp_band_operator_norm hVariation hLL hH p hp
  refine ⟨C,hC,?_⟩
  intro epsilon R w he heR hR hw field hfield hfb l r hwidth
  apply ContinuousLinearMap.opNorm_le_bound _ hC.le
  intro f
  rw [localizedSharpBandOperator_reflected _ _ _ _ _ _ _ _ _ _ hw,l2Conj_norm]
  calc
    _ ≤ ‖localizedSharpBandOperator epsilon R he (he.trans_le heR) field hfield p w l r‖*
        ‖l2Conj planeMeasure f‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ C*‖f‖ := by
      rw [l2Conj_norm]
      exact mul_le_mul_of_nonneg_right (hbound epsilon R w he heR hR hw field hfield hfb l r hwidth) (norm_nonneg _)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_GlobalBandOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global positive and negative vertical-band bounds at one absolute
short scale, conditional on martingale variation, the directional
maximal estimate, and the horizontal Hilbert estimate. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem sharpBandOperator_norm_of_strip_bounds (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (hRsmall : R≤1/10000) (field : Plane → ℝ) (hfield : LipschitzWith 1 field)
    (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w) (C : ℝ) (hC : 0≤C)
    (hlocal : ∀ l r : ℝ, 1200*(r-l)≤1 →
      ‖localizedSharpBandOperator epsilon R he hR field hfield p w l r‖≤C) :
    ‖sharpBandOperator epsilon R he hR field hfield p w‖≤3*C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  exact bandL2Operator_global_from_local epsilon R he hR field hfield p w hw (1/10000)
    (by norm_num) hRsmall C hC (fun j => hlocal _ _ (by ring_nf; norm_num)) f

theorem global_positive_band_operator_norm (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (p : SchwartzMap ℝ ℂ) (hp : ∀ s, p s≠0 → 1 ≤ s ∧ s≤2) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R w : ℝ, (he : 0<epsilon) → (heR : epsilon≤R) → R≤1/10000 → 0<w →
    ∀ (field : Plane → ℝ) (hfield : LipschitzWith 1 field), (∀ z, |field z|≤1/4) →
      ‖sharpBandOperator epsilon R he (he.trans_le heR) field hfield p w‖≤C := by
  obtain ⟨C,hC,hlocal⟩ := localized_sharp_band_operator_norm hVariation hLL hH p hp
  refine ⟨3*C,by positivity,?_⟩
  intro epsilon R w he heR hR hw field hfield hfb
  apply sharpBandOperator_norm_of_strip_bounds epsilon R he (he.trans_le heR) hR field hfield p w hw C hC.le
  exact hlocal epsilon R w he heR (by linarith only [hR]) hw field hfield hfb

theorem global_negative_band_operator_norm (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (p : SchwartzMap ℝ ℂ) (hp : ∀ s, p s≠0 → 1 ≤ s ∧ s≤2) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R w : ℝ, (he : 0<epsilon) → (heR : epsilon≤R) → R≤1/10000 → 0<w →
    ∀ (field : Plane → ℝ) (hfield : LipschitzWith 1 field), (∀ z, |field z|≤1/4) →
      ‖sharpBandOperator epsilon R he (he.trans_le heR) field hfield (conjugateReflectedCutoff p) w‖≤C := by
  obtain ⟨C,hC,hlocal⟩ := localized_negative_band_operator_norm hVariation hLL hH p hp
  refine ⟨3*C,by positivity,?_⟩
  intro epsilon R w he heR hR hw field hfield hfb
  apply sharpBandOperator_norm_of_strip_bounds epsilon R he (he.trans_le heR) hR field hfield
    (conjugateReflectedCutoff p) w hw C hC.le
  exact hlocal epsilon R w he heR (by linarith only [hR]) hw field hfield hfb

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_GlobalBandPrincipalValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proved global band bounds pass to the actual symmetric principal
value, by the explicit pointwise limit and Fatou. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem sharpBandOperator_eLpNorm_le (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p : SchwartzMap ℝ ℂ)
    (w : ℝ) (hw : 0<w) (C : ℝ) (hC : 0≤C)
    (hbound : ‖sharpBandOperator epsilon R he hR field hfield p w‖≤C)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    eLpNorm (shortSlopeOperator (sharpTimeKernel epsilon R) (fun z => field (planeCoordinates z))
      (schwartzVerticalProjection p w 0 f)) 2 planeMeasure≤ENNReal.ofReal (C*‖f.toLp 2 planeMeasure‖) := by
  let g := schwartzVerticalProjection p w 0 f
  let u := fun z => field (planeCoordinates z)
  have hu : LipschitzWith 2 u := by simpa only [mul_one] using product_slope_lipschitz field hfield
  have hm := shortSchwartz_memLp (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
    (sharpTimeKernel_integrable epsilon R he hR) u hu g
  have hn := ((sharpBandOperator epsilon R he hR field hfield p w).le_opNorm (f.toLp 2 planeMeasure)).trans
    (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))
  change ‖bandL2Operator _ _ _ _ _ p w (f.toLp 2 planeMeasure)‖≤_ at hn
  rw [bandL2Operator_onSchwartz _ _ _ _ _ p w hw f] at hn
  change ‖hm.toLp (shortSlopeOperator (sharpTimeKernel epsilon R) u g)‖≤C*‖f.toLp 2 planeMeasure‖ at hn
  rw [Lp.norm_toLp] at hn
  apply (ENNReal.toReal_le_toReal hm.eLpNorm_ne_top (by simp)).mp
  simpa only [ENNReal.toReal_ofReal (mul_nonneg hC (norm_nonneg _))] using hn

theorem band_principalValue_of_uniform_norm (field : Plane → ℝ) (hfield : LipschitzWith 1 field)
    (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w) (R : ℝ) (hR : 0<R) (hRsmall : R≤1/4)
    (C : ℝ) (hC : 0≤C)
    (hbound : ∀ epsilon : ℝ, (he : 0<epsilon) → (heR : epsilon≤R) →
      ‖sharpBandOperator epsilon R he (he.trans_le heR) field hfield p w‖≤C)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    MemLp (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R
      (schwartzVerticalProjection p w 0 f)) 2 planeMeasure ∧
    eLpNorm (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R
      (schwartzVerticalProjection p w 0 f)) 2 planeMeasure≤ENNReal.ofReal (C*‖f.toLp 2 planeMeasure‖) := by
  have hum : Measurable (fun z => field (planeCoordinates z)) := hfield.continuous.measurable.comp planeCoordinates.measurable
  have hn := productSlopePrincipalValue_eLpNorm_le (fun z => field (planeCoordinates z)) hum
    (schwartzVerticalProjection p w 0 f) (schwartzVerticalProjection p w 0 f).differentiable R hR hRsmall
    (ENNReal.ofReal (C*‖f.toLp 2 planeMeasure‖)) (fun epsilon he heR =>
      sharpBandOperator_eLpNorm_le epsilon R he (he.trans_le heR.le) field hfield p w hw C hC
        (hbound epsilon he heR.le) f)
  exact ⟨⟨(productSlopePrincipalValue_measurable (fun z => field (planeCoordinates z)) hum
    (schwartzVerticalProjection p w 0 f) (schwartzVerticalProjection p w 0 f).differentiable R hR
    hRsmall).aestronglyMeasurable,hn.trans_lt ENNReal.ofReal_lt_top⟩,hn⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NarrowBandCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed nonzero, real and even narrow cutoff for the
p=2 band-to-full reduction. Its positive part is in [1,101/100]. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem narrowBandPositive_support (s : ℝ) (hs : narrowBandPositive s≠0) :
    1 ≤ s ∧ s≤101/100 := by
  have hn : narrowBandBump s≠0 := by
    intro h
    exact hs (by simp only [narrowBandPositive_apply,h,Complex.ofReal_zero])
  have hm : s∈Function.support narrowBandBump := hn
  rw [narrowBandBump.support_eq] at hm
  have hd : |s-201/200|<1/400 := by
    simpa only [Metric.mem_ball,Real.dist_eq,narrowBandBump] using hm
  exact ⟨by linarith [(abs_lt.mp hd).1],by linarith [(abs_lt.mp hd).2]⟩

theorem narrowBandPositive_band (s : ℝ) (hs : narrowBandPositive s≠0) : 1 ≤ s ∧ s≤2 := by
  have h := narrowBandPositive_support s hs
  exact ⟨h.1,by linarith only [h.2]⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ConditionalSlopePrincipalValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full principal-value bound for small bounded slope fields follows
from the proved global band theorem and the precise published reduction. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem sharpBandOperator_add_profile (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p q : SchwartzMap ℝ ℂ)
    (w : ℝ) (hw : 0<w) :
    sharpBandOperator epsilon R he hR field hfield (p+q) w=
      sharpBandOperator epsilon R he hR field hfield p w+
        sharpBandOperator epsilon R he hR field hfield q w := by
  apply ContinuousLinearMap.ext
  intro f
  change shortL2Operator _ _ _ _ _ (verticalL2Projection (p+q) w f)=
    shortL2Operator _ _ _ _ _ (verticalL2Projection p w f)+
      shortL2Operator _ _ _ _ _ (verticalL2Projection q w f)
  rw [verticalL2Projection_add_profile p q w hw]
  simp only [add_apply,map_add]

theorem global_narrow_band_operator_norm (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) :
    ∃ B : ℝ, 0<B ∧ ∀ epsilon R w : ℝ, (he : 0<epsilon) → (heR : epsilon≤R) → R≤1/10000 → 0<w →
    ∀ (field : Plane → ℝ) (hfield : LipschitzWith 1 field), (∀ z, |field z|≤1/4) →
      ‖sharpBandOperator epsilon R he (he.trans_le heR) field hfield narrowBandProfile w‖≤B := by
  obtain ⟨B₁,hB₁,hpos⟩ := global_positive_band_operator_norm hVariation hLL hH narrowBandPositive narrowBandPositive_band
  obtain ⟨B₂,hB₂,hneg⟩ := global_negative_band_operator_norm hVariation hLL hH narrowBandPositive narrowBandPositive_band
  refine ⟨B₁+B₂,add_pos hB₁ hB₂,?_⟩
  intro epsilon R w he heR hR hw field hfield hfb
  rw [narrowBandProfile,sharpBandOperator_add_profile _ _ _ _ _ _ _ _ w hw]
  exact (norm_add_le _ _).trans (add_le_add
    (hpos epsilon R w he heR hR hw field hfield hfb)
    (hneg epsilon R w he heR hR hw field hfield hfb))

theorem conditional_slope_principalValue (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (hReassembly : BandToFullInput) :
    ∃ C : ℝ, 0<C ∧ ∀ R : ℝ, 0<R → R≤1/10000 →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ f : SchwartzMap (ℝ×ℝ) ℂ,
      MemLp (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R f) 2 planeMeasure ∧
      eLpNorm (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R f) 2 planeMeasure≤
        ENNReal.ofReal (C*‖f.toLp 2 planeMeasure‖) := by
  obtain ⟨B,hB,hband⟩ := global_narrow_band_operator_norm hVariation hLL hH
  obtain ⟨C,hC,hfull⟩ := hReassembly B hB
  refine ⟨C,hC,?_⟩
  intro R hR hRsmall field hfield hfb f
  apply hfull R hR hRsmall field hfield hfb _ f
  intro w hw g
  exact band_principalValue_of_uniform_norm field hfield narrowBandProfile w hw R hR
    (by linarith only [hRsmall]) B hB.le
    (fun epsilon he heR => hband epsilon R w he heR hRsmall hw field hfield hfb) g

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ProductSlopePVTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite sharp truncation is the difference of two actual principal
values; the identity is proved using the continuous symmetric quotient. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert.PacketRepresentation

theorem symmetric_regularized_continuous (F : ℝ → ℂ) (hF : Differentiable ℝ F) :
    Continuous (Function.update (fun t : ℝ => t⁻¹ • (F t-F (-t))) 0
      (deriv (fun t : ℝ => F t-F (-t)) 0)) := by
  let g := fun t : ℝ => F t-F (-t)
  have hg : Differentiable ℝ g := hF.sub (hF.comp differentiable_neg)
  have hg0 : g 0=0 := by simp only [g,neg_zero,sub_self]
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t=0
  · subst t
    apply continuousAt_update_same.mpr
    simpa only [zero_add,hg0,sub_zero] using (hg 0).hasDerivAt.tendsto_slope_zero
  · apply (continuousAt_update_of_ne ht).mpr
    exact (continuousAt_id.inv₀ ht).smul hg.continuous.continuousAt

theorem productSymmetricTruncation_eq_pv_sub (u : (ℝ×ℝ) → ℝ)
    (f : (ℝ×ℝ) → ℂ) (hf : Differentiable ℝ f) (epsilon R : ℝ) (he : 0<epsilon)
    (heR : epsilon≤R) (z : ℝ×ℝ) :
    productSymmetricTruncation u epsilon R f z=
      productSlopePrincipalValue u R f z-productSlopePrincipalValue u epsilon f z := by
  let F := fun t : ℝ => f (productSlopeSample u t z)
  have hF : Differentiable ℝ F := by
    unfold F productSlopeSample
    fun_prop
  let reg := Function.update (fun t : ℝ => t⁻¹ • (F t-F (-t))) 0
    (deriv (fun t : ℝ => F t-F (-t)) 0)
  have hreg : Continuous reg := symmetric_regularized_continuous F hF
  change (∫ t in epsilon..R, t⁻¹ • (F t-F (-t)))=
    (∫ t in (0:ℝ)..R, reg t)-(∫ t in (0:ℝ)..epsilon, reg t)
  rw [←intervalIntegral.integral_add_adjacent_intervals
    (hreg.intervalIntegrable 0 epsilon) (hreg.intervalIntegrable epsilon R),add_sub_cancel_left]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le heR] at ht
  exact (Function.update_of_ne (he.trans_le ht.1).ne'
    (deriv (fun t : ℝ => F t-F (-t)) 0) (fun t : ℝ => t⁻¹ • (F t-F (-t)))).symm

theorem shortSharp_eq_pv_sub (u : (ℝ×ℝ) → ℝ) (f : (ℝ×ℝ) → ℂ)
    (hf : Differentiable ℝ f) (epsilon R : ℝ) (he : 0<epsilon) (heR : epsilon≤R)
    (hR : R≤1/4) :
    shortSlopeOperator (sharpTimeKernel epsilon R) u f=
      productSlopePrincipalValue u R f-productSlopePrincipalValue u epsilon f := by
  funext z
  rw [shortSharp_eq_productSymmetric u f hf.continuous epsilon R he heR hR z,
    productSymmetricTruncation_eq_pv_sub u f hf epsilon R he heR z]
  rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ConditionalSlopeOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-frequency uniform sharp-truncation bounds for bounded small
slope fields, conditional only on the four precisely cited inputs. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem conditional_slope_truncation (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (hReassembly : BandToFullInput) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R : ℝ, 0<epsilon → epsilon≤R → R≤1/10000 →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ f : SchwartzMap (ℝ×ℝ) ℂ,
      eLpNorm (shortSlopeOperator (sharpTimeKernel epsilon R) (fun z => field (planeCoordinates z)) f)
        2 planeMeasure≤ENNReal.ofReal (C*‖f.toLp 2 planeMeasure‖) := by
  obtain ⟨C,hC,hpv⟩ := conditional_slope_principalValue hVariation hLL hH hReassembly
  refine ⟨2*C,by positivity,?_⟩
  intro epsilon R he heR hR field hfield hfb f
  obtain ⟨hlm,hlarge⟩ := hpv R (he.trans_le heR) hR field hfield hfb f
  obtain ⟨hsm,hsmall⟩ := hpv epsilon he (heR.trans hR) field hfield hfb f
  rw [shortSharp_eq_pv_sub _ f f.differentiable epsilon R he heR (by linarith only [hR])]
  have h := (eLpNorm_sub_le (μ:=planeMeasure) (p:=2)
    (f:=productSlopePrincipalValue (fun z => field (planeCoordinates z)) R f)
    (g:=productSlopePrincipalValue (fun z => field (planeCoordinates z)) epsilon f)
    hlm.aestronglyMeasurable hsm.aestronglyMeasurable (by norm_num)).trans
      (add_le_add hlarge hsmall)
  apply h.trans_eq
  rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DominatedKernelAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A time kernel may depend measurably on the output point. An integrable
scalar majorant still gives the same elementary L2 averaging bound. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem dominatedKernelAverage_energy (A : ℝ×(ℝ×ℝ) → ℂ) (hAm : Measurable A)
    (w : ℝ → ℝ) (hwm : Measurable w) (hw : Integrable w) (hw0 : ∀ t, 0≤w t)
    (hA : ∀ p, ‖A p‖≤w p.1) (F : ℝ×(ℝ×ℝ) → ℂ) (hFm : Measurable F)
    (B : ℝ) (hF : ∀ t, MemLp (fun z => F (t,z)) 2 planeMeasure)
    (henergy : ∀ t, (∫ z, ‖F (t,z)‖^2 ∂planeMeasure)≤B) :
    MemLp (fun z => ∫ t, A (t,z)*F (t,z)) 2 planeMeasure ∧
      (∫ z, ‖∫ t, A (t,z)*F (t,z)‖^2 ∂planeMeasure)≤(∫ t, w t)^2*B := by
  let H := fun p : ℝ×(ℝ×ℝ) => w p.1*‖F p‖^2
  have hHm : Measurable H := (hwm.comp measurable_fst).mul (hFm.norm.pow_const 2)
  have hH0 (p) : 0≤H p := mul_nonneg (hw0 _) (sq_nonneg _)
  have hi : Integrable H (volume.prod planeMeasure) := by
    apply (integrable_prod_iff hHm.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun t =>
        ((hF t).integrable_norm_pow (by decide : 2≠0)).const_mul (w t)
    · apply (hw.mul_const B).mono'
        hHm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      filter_upwards [] with t
      rw [Real.norm_of_nonneg (integral_nonneg fun z => norm_nonneg (H (t,z)))]
      simp only [Real.norm_of_nonneg (hH0 _)]
      change (∫ z, w t*‖F (t,z)‖^2 ∂planeMeasure)≤w t*B
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (henergy t) (hw0 t)
  have hm : Measurable (fun z => ∫ t, A (t,z)*F (t,z)) :=
    (hAm.mul hFm).stronglyMeasurable.prod_swap.integral_prod_right'.measurable
  have hp : ∀ᵐ z ∂planeMeasure, ‖∫ t, A (t,z)*F (t,z)‖^2≤
      (∫ t, w t)*(∫ t, H (t,z)) := by
    filter_upwards [hi.prod_left_ae] with z hz
    obtain ⟨hprod,hcs⟩ := weighted_integral_cauchySchwarz volume w
      (fun t => ‖F (t,z)‖) hwm (hFm.norm.comp (by fun_prop))
      hw0 (fun _ => norm_nonneg _) hw hz
    have hn : ‖∫ t, A (t,z)*F (t,z)‖≤∫ t, w t*‖F (t,z)‖ :=
      norm_integral_le_of_norm_le hprod (Filter.Eventually.of_forall fun t => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hA (t,z)) (norm_nonneg _))
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hcs
  have hdom := hi.integral_prod_right.const_mul (∫ t, w t)
  have he : Integrable (fun z => ‖∫ t, A (t,z)*F (t,z)‖^2) planeMeasure := by
    apply hdom.mono' (hm.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hp] with z hz
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hz
  refine ⟨(memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2 he,?_⟩
  have htotal : (∫ t, ∫ z, H (t,z) ∂planeMeasure)≤(∫ t, w t)*B := by
    rw [←integral_mul_const]
    apply integral_mono hi.integral_prod_left (hw.mul_const B)
    intro t
    change (∫ z, w t*‖F (t,z)‖^2 ∂planeMeasure)≤_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (henergy t) (hw0 t)
  calc
    _ ≤ ∫ z, (∫ t, w t)*(∫ t, H (t,z)) ∂planeMeasure :=
      integral_mono_ae he hdom hp
    _ = (∫ t, w t)*(∫ t, ∫ z, H (t,z) ∂planeMeasure) := by
      rw [integral_const_mul]
      exact congrArg (fun a => (∫ t, w t)*a)
        (integral_integral_swap (f:=fun (z : ℝ×ℝ) (t : ℝ) => H (t,z)) hi.swap)
    _ ≤ (∫ t, w t)*((∫ t, w t)*B) :=
      mul_le_mul_of_nonneg_left htotal (integral_nonneg hw0)
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VariableEndpointKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable factor between one half and one may change both sharp
endpoints. The resulting kernel error has a uniform integrable majorant. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_close_upper (r R S t : ℝ) (hR : 0<R)
    (hRS : R≤S) (hSR : S≤2*R) :
    ‖sharpTimeKernel r R t-sharpTimeKernel r S t‖≤3*timeErrorEnvelope R t := by
  have hq := timeErrorEnvelope_nonneg R t hR
  by_cases hr : r< |t|
  · by_cases htR : |t|<R
    · have htS : |t|<S := htR.trans_le hRS
      simp only [sharpTimeKernel, hr, htR, htS, and_self, ite_true, if_true, sub_self, norm_zero]
      positivity
    · by_cases htS : |t|<S
      · have ht : 0< |t| := hR.trans_le (le_of_not_gt htR)
        have ht2 : |t|≤2*R := htS.le.trans hSR
        have hd : 0<R^2+t^2 := by positivity
        have hpoly : R^2+t^2≤3*R*|t| := by
          nlinarith [sq_abs t,mul_nonneg (sub_nonneg.mpr (le_of_not_gt htR))
            (sub_nonneg.mpr ht2)]
        simp only [sharpTimeKernel,hr,htR,htS,true_and,ite_true, if_true,ite_false, if_false,
          zero_sub,norm_neg,norm_inv,Complex.norm_real,Real.norm_eq_abs,timeErrorEnvelope]
        rw [←mul_div_assoc,inv_eq_one_div]
        apply (div_le_div_iff₀ ht hd).2
        nlinarith only [hpoly]
      · simp only [sharpTimeKernel,hr,htR,htS,true_and,ite_false, if_false,sub_self,norm_zero]
        positivity
  · simp only [sharpTimeKernel,hr,false_and,ite_false, if_false,sub_self,norm_zero]
    positivity

theorem endpointErrorMajorant_nonneg (epsilon R t : ℝ) (he : 0<epsilon) (hR : 0<R) :
    0≤endpointErrorMajorant epsilon R t := by
  exact add_nonneg (mul_nonneg (by norm_num) (timeErrorEnvelope_nonneg _ _ (by linarith)))
    (mul_nonneg (by norm_num) (timeErrorEnvelope_nonneg _ _ (by linarith)))

theorem endpointErrorMajorant_measurable (epsilon R : ℝ) :
    Measurable (endpointErrorMajorant epsilon R) := by
  unfold endpointErrorMajorant timeErrorEnvelope
  fun_prop

theorem endpointErrorMajorant_integrable (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R) :
    Integrable (endpointErrorMajorant epsilon R) :=
  ((timeErrorEnvelope_integrable _ (by linarith)).const_mul 6).add
    ((timeErrorEnvelope_integrable _ (by linarith)).const_mul 6)

theorem endpointErrorMajorant_integral (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R) :
    (∫ t, endpointErrorMajorant epsilon R t)=12*Real.pi := by
  change (∫ t, 6*timeErrorEnvelope (epsilon/2) t+6*timeErrorEnvelope (R/2) t)=_
  rw [integral_add
    ((timeErrorEnvelope_integrable _ (by linarith)).const_mul 6)
    ((timeErrorEnvelope_integrable _ (by linarith)).const_mul 6)]
  simp only [integral_const_mul, timeErrorEnvelope_integral _ (by linarith : 0<epsilon/2),
    timeErrorEnvelope_integral _ (by linarith : 0<R/2)]
  ring

theorem sharpTimeKernel_scaled_diff (epsilon R a t : ℝ)
    (he : 0<epsilon) (hR : 0<R) (ha : 1/2≤a) (ha1 : a≤1) :
    ‖sharpTimeKernel (epsilon*a) (R*a) t-sharpTimeKernel epsilon R t‖≤
      endpointErrorMajorant epsilon R t := by
  have h1 := sharpTimeKernel_close_lower (epsilon/2) (epsilon*a) (R*a) t
    (by linarith) (by nlinarith) (by nlinarith)
  have h2 := sharpTimeKernel_close_upper (epsilon/2) (R/2) (R*a) t
    (by linarith) (by nlinarith) (by nlinarith)
  have h3 := sharpTimeKernel_close_upper (epsilon/2) (R/2) R t
    (by linarith) (by linarith) (by linarith)
  have h4 := sharpTimeKernel_close_lower (epsilon/2) epsilon R t
    (by linarith) (by linarith) (by linarith)
  have heq : sharpTimeKernel (epsilon*a) (R*a) t-sharpTimeKernel epsilon R t=
      (sharpTimeKernel (epsilon*a) (R*a) t-sharpTimeKernel (epsilon/2) (R*a) t)+
      (sharpTimeKernel (epsilon/2) (R*a) t-sharpTimeKernel (epsilon/2) (R/2) t)+
      (sharpTimeKernel (epsilon/2) (R/2) t-sharpTimeKernel (epsilon/2) R t)+
      (sharpTimeKernel (epsilon/2) R t-sharpTimeKernel epsilon R t) := by ring
  rw [norm_sub_rev] at h1 h2
  rw [heq]
  have hn := norm_add_le
    ((sharpTimeKernel (epsilon*a) (R*a) t-sharpTimeKernel (epsilon/2) (R*a) t)+
      (sharpTimeKernel (epsilon/2) (R*a) t-sharpTimeKernel (epsilon/2) (R/2) t)+
      (sharpTimeKernel (epsilon/2) (R/2) t-sharpTimeKernel (epsilon/2) R t))
    (sharpTimeKernel (epsilon/2) R t-sharpTimeKernel epsilon R t)
  have hn2 := norm_add_le
    ((sharpTimeKernel (epsilon*a) (R*a) t-sharpTimeKernel (epsilon/2) (R*a) t)+
      (sharpTimeKernel (epsilon/2) (R*a) t-sharpTimeKernel (epsilon/2) (R/2) t))
    (sharpTimeKernel (epsilon/2) (R/2) t-sharpTimeKernel (epsilon/2) R t)
  have hn3 := norm_add_le
    (sharpTimeKernel (epsilon*a) (R*a) t-sharpTimeKernel (epsilon/2) (R*a) t)
    (sharpTimeKernel (epsilon/2) (R*a) t-sharpTimeKernel (epsilon/2) (R/2) t)
  unfold endpointErrorMajorant
  linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariableEndpointOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform L2 control of the error caused by measurable changes of both
time endpoints, with no regularity assumption on the endpoint factor. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem endpointKernelError_measurable (epsilon R : ℝ) (a : (ℝ×ℝ) → ℝ)
    (ha : Measurable a) : Measurable (endpointKernelError epsilon R a) := by
  have hm : Measurable (fun p : ℝ×(ℝ×ℝ) =>
      sharpTimeKernel (epsilon*a p.2) (R*a p.2) p.1) := by
    unfold sharpTimeKernel
    have hs : MeasurableSet {p : ℝ×(ℝ×ℝ) |
        epsilon*a p.2 < |p.1| ∧ |p.1| < R*a p.2} :=
      by measurability
    exact (show Measurable (fun p : ℝ×(ℝ×ℝ) => (p.1 : ℂ)⁻¹) by fun_prop).ite hs measurable_const
  exact hm.sub ((sharpTimeKernel_measurable epsilon R).comp measurable_fst)

theorem endpointErrorOperator_energy (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (a u : (ℝ×ℝ) → ℝ) (ham : Measurable a)
    (ha : ∀ z, 1/2≤a z) (ha1 : ∀ z, a z≤1) (hu : LipschitzWith 2 u)
    (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hf : MemLp f 2 planeMeasure) :
    MemLp (endpointErrorOperator epsilon R a u f) 2 planeMeasure ∧
      (∫ z, ‖endpointErrorOperator epsilon R a u f z‖^2 ∂planeMeasure)≤
        4*(12*Real.pi)^2*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
  have h := dominatedKernelAverage_energy (endpointKernelError epsilon R a)
    (endpointKernelError_measurable epsilon R a ham) (endpointErrorMajorant epsilon R)
    (endpointErrorMajorant_measurable epsilon R) (endpointErrorMajorant_integrable epsilon R he hR)
    (fun t => endpointErrorMajorant_nonneg epsilon R t he hR)
    (fun p => sharpTimeKernel_scaled_diff epsilon R (a p.2) p.1 he hR (ha p.2) (ha1 p.2))
    (fun p => shortSample u f p.1 p.2) (shortSample_measurable u hu.continuous.measurable f hfm)
    (4*∫ z, ‖f z‖^2 ∂planeMeasure) (fun t => (shortSample_energy u hu f hfm hf t).1)
    (fun t => (shortSample_energy u hu f hfm hf t).2)
  rw [endpointErrorMajorant_integral epsilon R he hR] at h
  exact ⟨h.1,h.2.trans_eq (by ring)⟩

theorem endpointErrorOperator_bound (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (a u : (ℝ×ℝ) → ℝ) (ham : Measurable a)
    (ha : ∀ z, 1/2≤a z) (ha1 : ∀ z, a z≤1) (hu : LipschitzWith 2 u)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    eLpNorm (endpointErrorOperator epsilon R a u f) 2 planeMeasure≤
      ENNReal.ofReal ((24*Real.pi)*‖f.toLp 2 planeMeasure‖) := by
  obtain ⟨hm,he2⟩ := endpointErrorOperator_energy epsilon R he hR a u ham ha ha1 hu f
    f.continuous.measurable (f.memLp 2 planeMeasure)
  rw [←memLp_toL2_norm_sq planeMeasure _ hm,
    ←memLp_toL2_norm_sq planeMeasure f (f.memLp 2 planeMeasure)] at he2
  change ‖hm.toLp (endpointErrorOperator epsilon R a u f)‖^2≤
    4*(12*Real.pi)^2*‖f.toLp 2 planeMeasure‖^2 at he2
  have hn : ‖hm.toLp (endpointErrorOperator epsilon R a u f)‖≤
      (24*Real.pi)*‖f.toLp 2 planeMeasure‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    exact he2.trans_eq (by ring)
  rw [←Lp.enorm_toLp hm, ←ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hn

theorem endpointErrorOperator_eq_sub (epsilon R : ℝ) (he : 0<epsilon)
    (heR : epsilon≤R) (hR : R≤1/4) (a u : (ℝ×ℝ) → ℝ)
    (ha : ∀ z, 1/2≤a z) (ha1 : ∀ z, a z≤1)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    endpointErrorOperator epsilon R a u f z=
      productSymmetricTruncation u (epsilon*a z) (R*a z) f z-
        shortSlopeOperator (sharpTimeKernel epsilon R) u f z := by
  have ha0 : 0<a z := by linarith [ha z]
  have hR0 := he.trans_le heR
  have hj := sharpTimeKernel_integrable (epsilon*a z) (R*a z)
    (mul_pos he ha0) (mul_pos hR0 ha0)
  have hk := sharpTimeKernel_integrable epsilon R he hR0
  have hrep : endpointErrorOperator epsilon R a u f z=
      shortSlopeOperator (fun t => sharpTimeKernel (epsilon*a z) (R*a z) t-
        sharpTimeKernel epsilon R t) u f z := by
    unfold endpointErrorOperator endpointKernelError shortSlopeOperator
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases ht : |t|≤1/4
    · simp only [shortSample,ite_eq_left ht]
    · simp only [shortSample,ite_eq_right ht,mul_zero]
  rw [hrep,shortSlopeOperator_kernel_sub _ _ hj hk]
  congr 1
  exact shortSharp_eq_productSymmetric u f f.continuous _ _ (mul_pos he ha0)
    (mul_le_mul_of_nonneg_right heR ha0.le) (by nlinarith [ha1 z]) z

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ConditionalVariableEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full-frequency slope estimate allows measurable, comparably
scaled inner and outer endpoints. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem conditional_variable_slope_truncation_oai (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (hReassembly : BandToFullInput) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R : ℝ, 0<epsilon → epsilon≤R → R≤1/10000 →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (a : (ℝ×ℝ) → ℝ), Measurable a → (∀ z, 1/2≤a z) → (∀ z, a z≤1) →
    ∀ f : SchwartzMap (ℝ×ℝ) ℂ,
      MemLp (fun z => productSymmetricTruncation (fun z => field (planeCoordinates z))
        (epsilon*a z) (R*a z) f z) 2 planeMeasure ∧
      eLpNorm (fun z => productSymmetricTruncation (fun z => field (planeCoordinates z))
        (epsilon*a z) (R*a z) f z) 2 planeMeasure≤ENNReal.ofReal (C*‖f.toLp 2 planeMeasure‖) := by
  obtain ⟨C,hC,hbound⟩ := conditional_slope_truncation hVariation hLL hH hReassembly
  refine ⟨C+24*Real.pi,by positivity,?_⟩
  intro epsilon R he heR hR field hfield hfb a ham ha ha1 f
  let u := fun z => field (planeCoordinates z)
  have hu : LipschitzWith 2 u := by
    simpa only [mul_one] using product_slope_lipschitz field hfield
  have heq : (fun z => productSymmetricTruncation u (epsilon*a z) (R*a z) f z)=
      endpointErrorOperator epsilon R a u f+shortSlopeOperator (sharpTimeKernel epsilon R) u f := by
    funext z
    have h := endpointErrorOperator_eq_sub epsilon R he heR (by linarith only [hR]) a u ha ha1 f z
    exact (eq_sub_iff_add_eq.mp h).symm
  rw [heq]
  have hmem := (endpointErrorOperator_energy epsilon R he (he.trans_le heR) a u ham ha ha1 hu
    f f.continuous.measurable (f.memLp 2 planeMeasure)).1
  have hmem2 := shortSchwartz_memLp _ (sharpTimeKernel_measurable epsilon R)
    (sharpTimeKernel_integrable epsilon R he (he.trans_le heR)) u hu f
  refine ⟨hmem.add hmem2,?_⟩
  calc
    _ ≤ eLpNorm (endpointErrorOperator epsilon R a u f) 2 planeMeasure+
        eLpNorm (shortSlopeOperator (sharpTimeKernel epsilon R) u f) 2 planeMeasure :=
      eLpNorm_add_le hmem.aestronglyMeasurable hmem2.aestronglyMeasurable (by norm_num)
    _ ≤ ENNReal.ofReal ((24*Real.pi)*‖f.toLp 2 planeMeasure‖)+
        ENNReal.ofReal (C*‖f.toLp 2 planeMeasure‖) :=
      add_le_add (endpointErrorOperator_bound epsilon R he (he.trans_le heR) a u ham ha ha1 hu f)
        (hbound epsilon R he heR hR field hfield hfb f)
    _ = ENNReal.ofReal ((C+24*Real.pi)*‖f.toLp 2 planeMeasure‖) := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.PacketRepresentation.conditional_variable_slope_truncation_oai := @OAI.LipschitzHilbert.PacketRepresentation.conditional_variable_slope_truncation_oai
