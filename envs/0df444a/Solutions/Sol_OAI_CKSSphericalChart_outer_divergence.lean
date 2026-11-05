-- Prove2me | solution 1 for OAI.CKSSphericalChart.outer_divergence
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:02:25.745042+00:00
-- url     : https://prove2.me/submissions/0ebdd975-1934-4501-aac6-20373bd446c2

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport
import Theorems.Thm_OAI_CKSInducedSphere_smoothDatum_rapid

set_option linter.all false

section
namespace OAI

noncomputable section
namespace CKSCalculus
noncomputable section
open Filter Set
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma D_const (e x : E) (c : ℝ) : D e (fun _ => c) x = 0 := by simp [D]

end
end CKSCalculus

end









end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter
open scoped Topology ContDiff

lemma phi_smooth : ContDiffOn ℝ ∞ phi (Ioi 0) := by
  unfold phi
  have hc : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothTransition ((x-6)/6)) := by fun_prop
  exact (contDiffOn_const.sub hc.contDiffOn).add
    (hc.contDiffOn.mul ((contDiffOn_id.inv (fun x hx => ne_of_gt hx)).pow 3))
lemma xi_smooth : ContDiff ℝ ∞ xi := by unfold xi; fun_prop
lemma zeta_smooth : ContDiff ℝ ∞ zeta := by unfold zeta; fun_prop

lemma bendingV_smooth {R : ℝ} (hR : 0 < R) :
    ContDiffOn ℝ ∞ (bendingV R) (Ioi 0) := by
  unfold bendingV
  have hc : ContDiffOn ℝ ∞ (fun r : ℝ => phi (r/R)) (Ioi 0) :=
    phi_smooth.comp (contDiffOn_id.div_const R) (fun r hr => div_pos hr hR)
  exact (contDiffOn_id.mul hc).mul
    ((xi_smooth.comp (contDiff_id.div_const (R^2))).contDiffOn)
lemma bendingZeta_smooth (R : ℝ) : ContDiff ℝ ∞ (bendingZeta R) :=
  zeta_smooth.comp (contDiff_id.div_const R)

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Finset

def dproj (x : Vec) (k i j : Ix) : ℝ :=
  -(if k = i then 1 else 0) * x j - x i * (if k = j then 1 else 0)

def dTangentTrace (x : Vec) (H : Mat) (K : Ix → Mat) (k : Ix) : ℝ :=
  ∑ i, ∑ j, (dproj x k i j * H i j + proj x i j * K k i j)

def dHessTF (x : Vec) (H : Mat) (K : Ix → Mat) (k i j : Ix) : ℝ :=
  (∑ a, ∑ b, (dproj x k i a * H a b * proj x b j +
    proj x i a * K k a b * proj x b j + proj x i a * H a b * dproj x k b j)) -
      dTangentTrace x H K k / 2 * proj x i j - tangentTrace x H / 2 * dproj x k i j

def divHessTF (x : Vec) (H : Mat) (K : Ix → Mat) (j : Ix) : ℝ :=
  ∑ k, ∑ i, ∑ l, proj x k i * proj x j l * dHessTF x H K k i l

def dRoundLap (x : Vec) (g : Vec) (H : Mat) (K : Ix → Mat) (k : Ix) : ℝ :=
  dTangentTrace x H K k - 2 * (g k + ∑ i, x i * H k i)

lemma proj_symm (x : Vec) (i j : Ix) : proj x i j = proj x j i := by
  simp only [proj, eq_comm, mul_comm]

lemma proj_normal {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (i : Ix) :
    ∑ j, proj x i j * x j = 0 := by
  simp only [proj, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq univ i (fun j => x j), ite_eq_left (mem_univ i)]
  simp_rw [mul_assoc, ← pow_two]
  rw [← Finset.mul_sum, hx]
  ring

lemma proj_idempotent {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (i j : Ix) :
    ∑ k, proj x i k * proj x k j = proj x i j := by
  simp only [proj, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' univ j (fun k => (if i = k then 1 else 0) - x i * x k),
    ite_eq_left (mem_univ j)]
  have hn := proj_normal hx i
  simp only [proj] at hn
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  simp only [hn, zero_mul, sub_zero]

lemma proj_trace {x : Vec} (hx : ∑ i, x i ^ 2 = 1) : ∑ i, proj x i i = 2 := by
  simp only [proj, ← pow_two, Finset.sum_sub_distrib]
  rw [hx]
  norm_num

lemma contracted_dproj {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (a : Ix) :
    ∑ k, ∑ i, proj x k i * dproj x k i a = -2 * x a := by
  have he (k i : Ix) : proj x k i * dproj x k i a =
      -(if k = i then proj x k i else 0) * x a -
        (if k = a then 1 else 0) * (proj x k i * x i) := by
    simp only [dproj]
    split_ifs <;> ring
  simp only [he, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_neg_distrib, Finset.sum_ite_eq, mem_univ, ite_true, proj_normal hx,
    mul_zero, sub_zero]
  rw [proj_trace hx]

lemma sum3_rotate (f : Ix → Ix → Ix → ℝ) :
    (∑ i, ∑ a, ∑ b, f i a b) = ∑ a, ∑ b, ∑ i, f i a b := by
  simpa only [Fintype.sum_prod_type] using
    (Finset.sum_comm (s := (univ : Finset Ix)) (t := (univ : Finset (Ix × Ix)))
      (f := fun i ab => f i ab.1 ab.2))

lemma sum4_comm (f : Ix → Ix → Ix → Ix → ℝ) :
    (∑ k, ∑ i, ∑ a, ∑ b, f k i a b) = ∑ a, ∑ b, ∑ k, ∑ i, f k i a b := by
  simpa only [Fintype.sum_prod_type] using
    (Finset.sum_comm (s := (univ : Finset (Ix × Ix))) (t := (univ : Finset (Ix × Ix)))
      (f := fun ki ab => f ki.1 ki.2 ab.1 ab.2))

lemma contraction_left_dproj {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (B : Ix → Ix → ℝ) :
    (∑ k, ∑ i, proj x k i * (∑ a, ∑ b, dproj x k i a * B a b)) =
      ∑ a, ∑ b, (-2 * x a) * B a b := by
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [sum4_comm]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  simp only [← Finset.sum_mul, contracted_dproj hx]

lemma contraction_left_proj {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (B : Ix → Ix → Ix → ℝ) :
    (∑ k, ∑ i, proj x k i * (∑ a, ∑ b, proj x i a * B k a b)) =
      ∑ k, ∑ a, ∑ b, proj x k a * B k a b := by
  apply sum_congr rfl
  intro k hk
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [sum3_rotate]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  rw [← Finset.sum_mul, proj_idempotent hx]

lemma contraction_trace_term {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (v : Vec) (j : Ix) :
    (∑ k, ∑ i, proj x k i * (v k * proj x i j)) = ∑ k, v k * proj x k j := by
  apply sum_congr rfl
  intro k hk
  simp_rw [mul_left_comm (proj x k _) (v k), ← Finset.mul_sum]
  rw [proj_idempotent hx]

lemma contraction_right_dproj {x : Vec} (_hx : ∑ i, x i ^ 2 = 1) (H : Mat) (j : Ix) :
    (∑ k, ∑ a, ∑ b, proj x k a * (H a b * dproj x k b j)) =
      -tangentTrace x H * x j - ∑ a, ∑ b, proj x j a * H a b * x b := by
  have he (k a b : Ix) : proj x k a * (H a b * dproj x k b j) =
      -(if k = b then proj x k a * H a b else 0) * x j -
        (if k = j then proj x k a * H a b * x b else 0) := by
    simp only [dproj]
    split_ifs <;> ring
  simp_rw [he]
  rw [sum3_rotate]
  simp only [sum_sub_distrib, ← sum_mul, sum_neg_distrib, sum_ite_eq', mem_univ, ite_true]
  simp_rw [proj_symm x _ _]
  simp only [← Finset.sum_neg_distrib, tangentTrace]

lemma sum3_last (f : Ix → Ix → Ix → ℝ) :
    (∑ i, ∑ a, ∑ b, f i a b) = ∑ b, ∑ i, ∑ a, f i a b := by
  simpa only [Fintype.sum_prod_type] using
    (Finset.sum_comm (s := (univ : Finset (Ix × Ix))) (t := (univ : Finset Ix))
      (f := fun ia b => f ia.1 ia.2 b))

def normalH (x : Vec) (H : Mat) (j : Ix) : ℝ := ∑ a, ∑ b, proj x j a * H a b * x b
def projectedK (x : Vec) (K : Ix → Mat) (j : Ix) : ℝ :=
  ∑ k, proj x j k * (∑ a, ∑ b, proj x a b * K k a b)
def projectedTraceDeriv (x : Vec) (H : Mat) (K : Ix → Mat) (j : Ix) : ℝ :=
  ∑ k, proj x j k * dTangentTrace x H K k

def rawContract (x : Vec) (D : Ix → Ix → Ix → ℝ) (j : Ix) : ℝ :=
  ∑ k, ∑ i, proj x k i * D k i j

lemma rawContract_add (x : Vec) (D E : Ix → Ix → Ix → ℝ) (j : Ix) :
    rawContract x (D + E) j = rawContract x D j + rawContract x E j := by
  simp only [rawContract, Pi.add_apply, mul_add, sum_add_distrib]

lemma rawContract_sub (x : Vec) (D E : Ix → Ix → Ix → ℝ) (j : Ix) :
    rawContract x (D - E) j = rawContract x D j - rawContract x E j := by
  simp only [rawContract, Pi.sub_apply, mul_sub, sum_sub_distrib]

lemma rawContract_smul (x : Vec) (D : Ix → Ix → Ix → ℝ) (c : ℝ) (j : Ix) :
    rawContract x (c • D) j = c * rawContract x D j := by
  simp only [rawContract, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, Finset.mul_sum]

lemma first_contribution {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (H : Mat)
    (hH : ∀ i j, H i j = H j i) (j : Ix) :
    rawContract x (fun k i j => ∑ a, ∑ b, dproj x k i a * (H a b * proj x b j)) j =
      -2 * normalH x H j := by
  rw [rawContract, contraction_left_dproj hx]
  unfold normalH
  rw [sum_comm]
  simp only [Finset.mul_sum]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  rw [hH b a, proj_symm x a j]
  ring

lemma second_contribution {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (K : Ix → Mat)
    (hK : ∀ k a b, K k a b = K b k a) (j : Ix) :
    rawContract x (fun k i j => ∑ a, ∑ b, proj x i a * (K k a b * proj x b j)) j =
      projectedK x K j := by
  rw [rawContract, contraction_left_proj hx, sum3_last]
  unfold projectedK
  apply sum_congr rfl
  intro b hb
  simp only [Finset.mul_sum]
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro a ha
  rw [hK k a b, proj_symm x b j]
  ring

lemma third_contribution {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (H : Mat) (j : Ix) :
    rawContract x (fun k i j => ∑ a, ∑ b, proj x i a * (H a b * dproj x k b j)) j =
      -tangentTrace x H * x j - normalH x H j := by
  rw [rawContract, contraction_left_proj hx, contraction_right_dproj hx]
  rfl

lemma trace_contribution {x : Vec} (hx : ∑ i, x i ^ 2 = 1)
    (H : Mat) (K : Ix → Mat) (j : Ix) :
    rawContract x (fun k i j => dTangentTrace x H K k / 2 * proj x i j) j =
      projectedTraceDeriv x H K j / 2 := by
  rw [rawContract, contraction_trace_term hx]
  unfold projectedTraceDeriv
  rw [Finset.sum_div]
  apply sum_congr rfl
  intro k hk
  rw [proj_symm x k j]
  ring

lemma rawContract_tfHessian {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (H : Mat) (K : Ix → Mat)
    (hH : ∀ i j, H i j = H j i) (hK : ∀ k a b, K k a b = K b k a) (j : Ix) :
    rawContract x (dHessTF x H K) j =
      -3 * normalH x H j + projectedK x K j - projectedTraceDeriv x H K j / 2 := by
  have he : dHessTF x H K =
      ((fun k i j => ∑ a, ∑ b, dproj x k i a * (H a b * proj x b j)) +
      (fun k i j => ∑ a, ∑ b, proj x i a * (K k a b * proj x b j)) +
      (fun k i j => ∑ a, ∑ b, proj x i a * (H a b * dproj x k b j))) -
      (fun k i j => dTangentTrace x H K k / 2 * proj x i j) -
      (tangentTrace x H / 2) • dproj x := by
    funext k i j
    simp only [dHessTF, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      sum_add_distrib, mul_assoc]
  rw [he, rawContract_sub, rawContract_sub, rawContract_add, rawContract_add,
    first_contribution hx H hH, second_contribution hx K hK, third_contribution hx H,
    trace_contribution hx, rawContract_smul]
  change _ - tangentTrace x H / 2 * (∑ k, ∑ i, proj x k i * dproj x k i j) = _
  rw [contracted_dproj hx]
  ring

lemma dTangentTrace_formula (x : Vec) (H : Mat) (K : Ix → Mat)
    (hH : ∀ i j, H i j = H j i) (k : Ix) :
    dTangentTrace x H K k = (∑ a, ∑ b, proj x a b * K k a b) -
      2 * (∑ b, H k b * x b) := by
  have he (i j : Ix) : dproj x k i j * H i j =
      -(if k = i then H i j * x j else 0) -
        (if k = j then H i j * x i else 0) := by
    simp only [dproj]
    split_ifs <;> ring
  simp only [dTangentTrace, he, sum_add_distrib, sum_sub_distrib,
    sum_neg_distrib]
  have h1 : (∑ i, ∑ j, if k = i then H i j * x j else 0) = ∑ b, H k b * x b := by
    rw [sum_comm]
    simp only [sum_ite_eq, mem_univ, ite_true]
  have h2 : (∑ i, ∑ j, if k = j then H i j * x i else 0) = ∑ b, H k b * x b := by
    simp only [sum_ite_eq, mem_univ, ite_true]
    simp_rw [hH _ k]
  rw [h1, h2]
  ring

lemma projectedTraceDeriv_formula (x : Vec) (H : Mat) (K : Ix → Mat)
    (hH : ∀ i j, H i j = H j i) (j : Ix) :
    projectedTraceDeriv x H K j = projectedK x K j - 2 * normalH x H j := by
  simp only [projectedTraceDeriv, dTangentTrace_formula x H K hH, mul_sub,
    sum_sub_distrib, projectedK, normalH, Finset.mul_sum]
  congr 1
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro b hb
  ring

lemma rawContract_tfHessian_simplified {x : Vec} (hx : ∑ i, x i ^ 2 = 1)
    (H : Mat) (K : Ix → Mat) (hH : ∀ i j, H i j = H j i)
    (hK : ∀ k a b, K k a b = K b k a) (j : Ix) :
    rawContract x (dHessTF x H K) j = projectedK x K j / 2 - 2 * normalH x H j := by
  rw [rawContract_tfHessian hx H K hH hK, projectedTraceDeriv_formula x H K hH]
  ring

lemma projected_twice {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (v : Vec) (j : Ix) :
    (∑ l, proj x j l * (∑ k, proj x l k * v k)) = ∑ k, proj x j k * v k := by
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [← Finset.sum_mul, proj_idempotent hx]

lemma divHessTF_eq {x : Vec} (hx : ∑ i, x i ^ 2 = 1)
    (g : Vec) (H : Mat) (K : Ix → Mat) (hH : ∀ i j, H i j = H j i)
    (hK : ∀ k a b, K k a b = K b k a) (j : Ix) :
    divHessTF x H K j = ∑ k, proj x j k * (g k + dRoundLap x g H K k / 2) := by
  have hc : divHessTF x H K j = ∑ l, proj x j l * rawContract x (dHessTF x H K) l := by
    simp only [divHessTF, rawContract, Finset.mul_sum]
    rw [sum3_last]
    apply sum_congr rfl
    intro l hl
    apply sum_congr rfl
    intro k hk
    apply sum_congr rfl
    intro i hi
    ring
  rw [hc]
  simp_rw [rawContract_tfHessian_simplified hx H K hH hK]
  have hkp : (∑ l, proj x j l * projectedK x K l) = projectedK x K j :=
    projected_twice hx _ j
  have hhp : (∑ l, proj x j l * normalH x H l) = normalH x H j := by
    simp only [normalH, ← Finset.mul_sum, mul_assoc]
    exact projected_twice hx _ j
  have hproj : (∑ l, proj x j l * (projectedK x K l / 2 - 2 * normalH x H l)) =
      projectedK x K j / 2 - 2 * normalH x H j := by
    simp only [mul_sub, ← mul_div_assoc, sum_sub_distrib, ← sum_div,
      mul_left_comm (proj x j _) 2, ← Finset.mul_sum, hkp, hhp]
  rw [hproj]
  simp only [dRoundLap, dTangentTrace_formula x H K hH, projectedK, normalH]
  rw [sum_div, Finset.mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro k hk
  simp only [← Finset.mul_sum, mul_assoc]
  have hm : (∑ i, x i * H k i) = ∑ i, H k i * x i := by simp_rw [mul_comm (x _)]
  rw [hm]
  ring

lemma hessTF_symm (x : Vec) (H : Mat) (hH : ∀ i j, H i j = H j i) (i j : Ix) :
    hessTF x H i j = hessTF x H j i := by
  unfold hessTF
  rw [proj_symm x i j]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  rw [proj_symm x i b, proj_symm x a j, hH b a]
  ring

lemma hessTF_normal_left {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (H : Mat) (j : Ix) :
    ∑ i, x i * hessTF x H i j = 0 := by
  simp only [hessTF, mul_sub, Finset.mul_sum, sum_sub_distrib]
  have he (i a b : Ix) : x i * (proj x i a * H a b * proj x b j) =
      (proj x a i * x i) * (H a b * proj x b j) := by rw [proj_symm x i a]; ring
  simp_rw [he]
  rw [sum3_rotate]
  simp only [← Finset.sum_mul, proj_normal hx, zero_mul, sum_const_zero]
  have ht (i : Ix) : x i * (tangentTrace x H / 2 * proj x i j) =
      tangentTrace x H / 2 * (proj x j i * x i) := by rw [proj_symm x i j]; ring
  simp_rw [ht, ← Finset.mul_sum, proj_normal hx]
  ring

lemma hessTF_trace_zero {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (H : Mat) :
    ∑ i, hessTF x H i i = 0 := by
  simp only [hessTF, sum_sub_distrib, ← Finset.mul_sum, proj_trace hx]
  have he (i a b : Ix) : proj x i a * H a b * proj x b i =
      (proj x b i * proj x i a) * H a b := by ring
  simp_rw [he]
  rw [sum3_rotate]
  simp only [← Finset.sum_mul, proj_idempotent hx]
  simp_rw [proj_symm x _ _]
  change tangentTrace x H - tangentTrace x H / 2 * 2 = 0
  ring

end
end CKSInducedSphere

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open MvPolynomial

def radiusSq : Poly := ∑ i : Fin 3, X i ^ 2

lemma laplacian_apply (p : Poly) :
    laplacian p = ∑ i : Fin 3, pderiv i (pderiv i p) := by
  simp [laplacian]

def euler : Derivation ℝ Poly Poly := ∑ i : Fin 3, (X i : Poly) • pderiv i

lemma rotation_apply (i j : Fin 3) (p : Poly) :
    rotation i j p = X i * pderiv j p - X j * pderiv i p := by
  simp [rotation, smul_eq_mul]

lemma euler_apply (p : Poly) : euler p = ∑ i : Fin 3, X i * pderiv i p := by
  simp [euler, Fin.sum_univ_three, Derivation.smul_apply, smul_eq_mul]

lemma euler_homogeneous {p : Poly} {n : ℕ} (hp : p.IsHomogeneous n) :
    euler p = (n : ℝ) • p := by
  rw [euler_apply, hp.sum_X_mul_pderiv, Nat.cast_smul_eq_nsmul ℝ]

lemma pderiv_commute (i j : Fin 3) (p : Poly) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p k hp =>
    by_cases hi : i = k <;> by_cases hj : j = k <;>
      simp_all [map_add, pderiv_X] <;> ring

lemma laplacian_X_mul (i : Fin 3) (p : Poly) :
    laplacian (X i * p) = X i * laplacian p + 2 * pderiv i p := by
  fin_cases i <;>
    simp [laplacian_apply, Fin.sum_univ_three, map_add, pderiv_X] <;> ring

lemma laplacian_pderiv (i : Fin 3) (p : Poly) :
    laplacian (pderiv i p) = pderiv i (laplacian p) := by
  simp only [laplacian_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pderiv_commute j i p, pderiv_commute j i (pderiv j p)]

lemma laplacian_rotation (i j : Fin 3) (p : Poly) :
    laplacian (rotation i j p) = rotation i j (laplacian p) := by
  rw [rotation_apply, map_sub, laplacian_X_mul, laplacian_X_mul,
    laplacian_pderiv, laplacian_pderiv, rotation_apply, pderiv_commute i j p]
  ring

lemma rotation_homogeneous (i j : Fin 3) {p : Poly} {n : ℕ}
    (hp : p.IsHomogeneous n) : (rotation i j p).IsHomogeneous n := by
  cases n with
  | zero =>
    have hC := totalDegree_eq_zero_iff_eq_C.mp
      ((totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hp)
    rw [hC, rotation_apply]
    simpa using (isHomogeneous_zero (σ := Fin 3) (R := ℝ) 0)
  | succ n =>
    rw [rotation_apply]
    have hi := (isHomogeneous_X (R := ℝ) i).mul (hp.pderiv (i := j))
    have hj := (isHomogeneous_X (R := ℝ) j).mul (hp.pderiv (i := i))
    simpa [Nat.add_comm] using hi.sub hj

lemma rotation_casimir (p : Poly) :
    rotation 0 1 (rotation 0 1 p) + rotation 0 2 (rotation 0 2 p) +
      rotation 1 2 (rotation 1 2 p) =
      radiusSq * laplacian p - euler (euler p) - euler p := by
  simp [rotation_apply, euler_apply, laplacian_apply, radiusSq,
    Fin.sum_univ_three, map_add, map_sub, pderiv_X]
  ring

theorem harmonic_rotation_eigenvalue {h : Poly} {l : ℕ}
    (hh : h.IsHomogeneous l) (hΔ : laplacian h = 0) :
    rotation 0 1 (rotation 0 1 h) + rotation 0 2 (rotation 0 2 h) +
      rotation 1 2 (rotation 1 2 h) = -((l : ℝ) * ((l : ℝ) + 1)) • h := by
  rw [rotation_casimir, hΔ, euler_homogeneous hh, Derivation.map_smul, euler_homogeneous hh]
  simp only [mul_zero, zero_sub, smul_smul, ← neg_smul, ← sub_smul]
  congr 1
  ring

lemma sphereEval_X (i : Fin 3) : sphereEval (X i) = sphereCoordinate i :=
  aeval_X _ _

open MeasureTheory

open scoped Pointwise
def sphereHome (u : Ambient ≃ₗᵢ[ℝ] Ambient) : Sphere ≃ₜ Sphere :=
  u.toHomeomorph.subtype (fun x => by
    simp only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.coe_toHomeomorph,
      u.norm_map])

def rotatedCoordinate (i j : Fin 3) (t : ℝ) (k : Fin 3) : C(Sphere, ℝ) :=
  if k = i then Real.cos t • sphereCoordinate i - Real.sin t • sphereCoordinate j
  else if k = j then Real.sin t • sphereCoordinate i + Real.cos t • sphereCoordinate j
  else sphereCoordinate k

def rotationAction (i j : Fin 3) (t : ℝ) : Poly →ₐ[ℝ] C(Sphere, ℝ) :=
  aeval (rotatedCoordinate i j t)

lemma rotationAction_zero (i j : Fin 3) : rotationAction i j 0 = sphereEval := by
  apply MvPolynomial.algHom_ext
  intro k
  simp only [rotationAction, sphereEval, aeval_X, rotatedCoordinate, Real.cos_zero,
    Real.sin_zero, one_smul, zero_smul, sub_zero, zero_add]
  split_ifs with hi hj
  · subst k; rfl
  · subst k; rfl
  · rfl

lemma rotationAction_apply (i j : Fin 3) (hij : i ≠ j) (t : ℝ)
    (p : Poly) (x : Sphere) :
    rotationAction i j t p x = sphereEval p (sphereHome (planeRotation i j hij t) x) := by
  have h : (ContinuousMap.evalAlgHom ℝ ℝ x).comp (rotationAction i j t) =
      (ContinuousMap.evalAlgHom ℝ ℝ (sphereHome (planeRotation i j hij t) x)).comp
        sphereEval := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, ContinuousMap.evalAlgHom_apply, rotationAction,
      aeval_X, sphereEval]
    change rotatedCoordinate i j t k x = (planeRotationMap i j t x.1) k
    rw [planeRotationMap_apply]
    simp only [rotatedCoordinate]
    split_ifs <;> rfl
  exact congrArg (fun f : Poly →ₐ[ℝ] ℝ => f p) h

lemma rotatedCoordinate_hasDerivAt_zero (i j : Fin 3) (hij : i ≠ j) (k : Fin 3) :
    HasDerivAt (fun t => rotatedCoordinate i j t k)
      (sphereEval (rotation i j (X k))) 0 := by
  have hs := (Real.hasDerivAt_sin (0 : ℝ))
  have hc := (Real.hasDerivAt_cos (0 : ℝ))
  by_cases hi : k = i
  · subst k
    convert! (hc.smul_const (sphereCoordinate i)).sub
        (hs.smul_const (sphereCoordinate j)) using 1 <;>
      simp [rotatedCoordinate, rotation_apply, hij, pderiv_X, sphereEval_X]
    rfl
  · by_cases hj : k = j
    · subst k
      convert! (hs.smul_const (sphereCoordinate i)).add
          (hc.smul_const (sphereCoordinate j)) using 1 <;>
        simp [rotatedCoordinate, rotation_apply, hij.symm, pderiv_X, sphereEval_X]
      rfl
    · simpa [rotatedCoordinate, rotation_apply, hi, hj, Ne.symm hi, Ne.symm hj,
        pderiv_X] using hasDerivAt_const (0 : ℝ) (sphereCoordinate k)

lemma rotationAction_hasDerivAt_zero (i j : Fin 3) (hij : i ≠ j) (p : Poly) :
    HasDerivAt (fun t => rotationAction i j t p) (sphereEval (rotation i j p)) 0 := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa [rotationAction, rotation_apply] using
      hasDerivAt_const (0 : ℝ) (algebraMap ℝ C(Sphere, ℝ) a)
  | add p q hp hq =>
    convert! hp.add hq using 1 <;> simp only [map_add]
    rfl
  | mul_X p k hp =>
    have hk : HasDerivAt (fun t => rotationAction i j t (X k))
        (sphereEval (rotation i j (X k))) 0 :=
      by simpa only [rotationAction, aeval_X] using
        rotatedCoordinate_hasDerivAt_zero i j hij k
    convert! hp.mul hk using 1
    · funext t; exact map_mul (rotationAction i j t) p (X k)
    · rw [Derivation.leibniz, map_add]
      simp only [smul_eq_mul, map_mul, rotationAction_zero]
      ring

def eigenvalue (l : ℕ) : ℝ := (l : ℝ) * ((l : ℝ) + 1)

lemma rotation_harmonic {p : Poly} {l : ℕ} (hp : p.IsHomogeneous l)
    (hΔ : laplacian p = 0) (i j : Fin 3) :
    (rotation i j p).IsHomogeneous l ∧ laplacian (rotation i j p) = 0 := by
  exact ⟨rotation_homogeneous i j hp, by rw [laplacian_rotation, hΔ, map_zero]⟩

lemma rotationWord_harmonic {l : ℕ} {p : Poly}
    (hp : p.IsHomogeneous l) (hΔ : laplacian p = 0) (w : List (Fin 3 × Fin 3)) :
    (rotationWord w p).IsHomogeneous l ∧ laplacian (rotationWord w p) = 0 := by
  induction w with
  | nil => exact ⟨hp, hΔ⟩
  | cons ij w ih => exact rotation_harmonic ih.1 ih.2 ij.1 ij.2

open scoped Manifold ContDiff Topology
open Set

lemma rotationGenerator_apply (i j k : Fin 3) (x : Ambient) :
    rotationGenerator i j x k = (if k = j then x i else 0) - (if k = i then x j else 0) := rfl

attribute [local instance] cksLocalInst_1853

lemma planeRotation_hasDerivAt (i j : Fin 3) (hij : i ≠ j) (x : Ambient) (t : ℝ) :
    HasDerivAt (fun s => planeRotation i j hij s x)
      (rotationGenerator i j (planeRotation i j hij t x)) t := by
  have h : HasDerivAt (fun s => fun k : Fin 3 =>
      if k = i then Real.cos s * x i - Real.sin s * x j
      else if k = j then Real.sin s * x i + Real.cos s * x j else x k)
      (fun k => (rotationGenerator i j (planeRotation i j hij t x)) k) t := by
    apply hasDerivAt_pi.mpr
    intro k
    by_cases hi : k = i
    · subst k
      convert! ((Real.hasDerivAt_cos t).mul_const (x i)).sub
        ((Real.hasDerivAt_sin t).mul_const (x j)) using 1
      · funext s; simp
      · simp [rotationGenerator_apply, planeRotation_apply, planeRotationMap_apply, hij, hij.symm]
        ring
    · by_cases hj : k = j
      · subst k
        convert! ((Real.hasDerivAt_sin t).mul_const (x i)).add
          ((Real.hasDerivAt_cos t).mul_const (x j)) using 1
        · funext s; simp [hij.symm]
        · simp [rotationGenerator_apply, planeRotation_apply, planeRotationMap_apply, hij.symm]
          ring
      · simpa [rotationGenerator_apply, hi, hj] using hasDerivAt_const t (x k)
  convert! (PiLp.hasFDerivAt_toLp 2 _).comp_hasDerivAt t h using 1

lemma smoothRotation_orbit_derivative {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    (i j : Fin 3) (hij : i ≠ j) (x : Sphere) (t : ℝ) :
    HasDerivAt (fun s => F (planeRotation i j hij s (x : Ambient)))
      (smoothRotation i j F (planeRotation i j hij t (x : Ambient))) t := by
  have hn : (planeRotation i j hij t (x : Ambient)) ≠ 0 := by
    simpa using (planeRotation i j hij t).injective.ne (sphere_ne_zero x)
  have hd := (hF.contDiffAt (puncturedSpace.isOpen.mem_nhds hn)).differentiableAt (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt t (planeRotation_hasDerivAt i j hij x t)

def polynomialExtension (p : Poly) (x : Ambient) : ℝ := aeval (fun i => x i) p

lemma polynomialExtension_smooth (p : Poly) : ContDiff ℝ ∞ (polynomialExtension p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    convert! (contDiff_const : ContDiff ℝ ∞ (fun _ : Ambient => a)) using 1
    funext x; simp [polynomialExtension]
  | add p q hp hq =>
    convert! hp.add hq using 1
    funext x; exact map_add (aeval (fun i => x i)) p q
  | mul_X p k hp =>
    convert! hp.mul (EuclideanSpace.proj k).contDiff using 1
    funext x; simp [polynomialExtension]

lemma polynomialExtension_on_sphere (p : Poly) (x : Sphere) :
    polynomialExtension p x = sphereEval p x := by
  have h : aeval (fun i => (x : Ambient) i) =
      (ContinuousMap.evalAlgHom ℝ ℝ x).comp sphereEval := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [sphereEval, sphereCoordinate]
    rfl
  exact congrArg (fun h : Poly →ₐ[ℝ] ℝ => h p) h

lemma harmonicCoefficientPolynomial_spec (l : ℕ) (f : SphereL2) :
    (harmonicCoefficientPolynomial l f).IsHomogeneous l ∧
    laplacian (harmonicCoefficientPolynomial l f) = 0 ∧
    toL2 (sphereEval (harmonicCoefficientPolynomial l f)) = (harmonicProjection l f : SphereL2) :=
  Classical.choose_spec (harmonicL2_exists_polynomial (harmonicProjection l f))

lemma radialExtension_pos_smul (f : Sphere → ℝ) (x : Ambient) {a : ℝ} (ha : 0 < a) :
    radialExtension f (a • x) = radialExtension f x := by
  by_cases hx : x = 0
  · simp [hx, radialExtension]
  rw [radialExtension, dite_eq_left (smul_ne_zero ha.ne' hx), radialExtension, dite_eq_left hx]
  congr 1
  apply Subtype.ext
  simp only [normalizeSphere, norm_smul, Real.norm_eq_abs, abs_of_pos ha, mul_inv_rev,
    smul_smul]
  congr 1
  field_simp

lemma radialExtension_isometry (f : Sphere → ℝ) (e : Ambient ≃ₗᵢ[ℝ] Ambient)
    (x : Ambient) (hx : x ≠ 0) :
    radialExtension f (e x) = f (sphereHome e (normalizeSphere ⟨x, hx⟩)) := by
  rw [radialExtension, dite_eq_left (by simpa using e.injective.ne hx)]
  congr 1
  apply Subtype.ext
  simp [normalizeSphere, sphereHome]

lemma polynomial_sphere_smooth (p : Poly) : SmoothSphere (sphereEval p) := by
  have h := (polynomialExtension_smooth p).contMDiff.comp (contMDiff_coe_sphere (n := 2))
  convert! h using 1
  funext x
  exact (polynomialExtension_on_sphere p x).symm

lemma radialExtension_fderiv_self {f : Sphere → ℝ} (hf : SmoothSphere f)
    {x : Ambient} (hx : x ≠ 0) : fderiv ℝ (radialExtension f) x x = 0 := by
  have hd := ((radialExtension_smooth hf).contDiffAt
    (puncturedSpace.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hd' : HasFDerivAt (radialExtension f) (fderiv ℝ (radialExtension f) x) ((1 : ℝ) • x) := by
    simpa using hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt 1 ((hasDerivAt_id (1 : ℝ)).smul_const x)
  have he : (fun s : ℝ => radialExtension f (s • x)) =ᶠ[nhds 1]
      (fun _ => radialExtension f x) := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact radialExtension_pos_smul f x hs
  have h2 := (hasDerivAt_const (1 : ℝ) (radialExtension f x)).congr_of_eventuallyEq he
  simpa using h1.unique h2

lemma smoothRotation_radial_polynomial (p : Poly) (i j : Fin 3) {x : Ambient} (hx : x ≠ 0) :
    smoothRotation i j (radialExtension (sphereEval p)) x =
      radialExtension (sphereEval (rotation i j p)) x := by
  by_cases hij : i = j
  · subst j
    have hg : rotationGenerator i i x = 0 := by ext k; simp [rotationGenerator_apply]
    simp [smoothRotation, hg, rotation_apply, radialExtension]
  have hd := ((radialExtension_smooth (polynomial_sphere_smooth p)).contDiffAt
    (puncturedSpace.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hd' : HasFDerivAt (radialExtension (sphereEval p))
      (fderiv ℝ (radialExtension (sphereEval p)) x) (planeRotation i j hij 0 x) := by
    simpa using hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt (0 : ℝ) (planeRotation_hasDerivAt i j hij x 0)
  let y : Sphere := normalizeSphere ⟨x, hx⟩
  have h2 := (ContinuousMap.evalCLM (R := ℝ) y).hasFDerivAt.comp_hasDerivAt 0
    (rotationAction_hasDerivAt_zero i j hij p)
  have he : (fun t => radialExtension (sphereEval p) (planeRotation i j hij t x)) =
      fun t => rotationAction i j t p y := by
    funext t
    rw [rotationAction_apply i j hij]
    exact radialExtension_isometry _ _ _ hx
  change HasDerivAt (fun s => radialExtension (sphereEval p) (planeRotation i j hij s x)) _ 0 at h1
  rw [he] at h1
  have h := h1.unique h2
  simpa [smoothRotation, radialExtension, hx, y] using h

lemma rotationGenerator_decomposition (x v : Ambient) :
    ‖x‖ ^ 2 • v = (∑ i : Fin 3, ∑ j : Fin 3, (x i * v j) • rotationGenerator i j x) +
      (∑ i : Fin 3, x i * v i) • x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply PiLp.ext
  intro k
  fin_cases k <;> simp [Fin.sum_univ_three, rotationGenerator_apply] <;> ring

lemma radial_polynomial_fderiv (p : Poly) {x : Ambient} (hx : x ≠ 0) (v : Ambient) :
    fderiv ℝ (radialExtension (sphereEval p)) x v =
      ∑ i : Fin 3, ∑ j : Fin 3, (x i * v j / ‖x‖ ^ 2) *
        radialExtension (sphereEval (rotation i j p)) x := by
  have h := congrArg (fderiv ℝ (radialExtension (sphereEval p)) x)
    (rotationGenerator_decomposition x v)
  simp only [map_add, map_sum, map_smul, radialExtension_fderiv_self (polynomial_sphere_smooth p) hx,
    smul_eq_mul] at h
  have hrot (i j : Fin 3) : fderiv ℝ (radialExtension (sphereEval p)) x (rotationGenerator i j x) =
      radialExtension (sphereEval (rotation i j p)) x := smoothRotation_radial_polynomial p i j hx
  simp only [hrot] at h
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  apply (eq_div_iff (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).mpr
  simpa [mul_comm, mul_zero] using h

end
end CKSSphericalHarmonics

end

noncomputable section
namespace CKSSpectralHeat
noncomputable section
open Set Filter Real
open scoped Topology ContDiff

lemma eigenvalue_ge_six (n : ℕ) : 6 ≤ eigenvalue n := by
  unfold eigenvalue
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith
lemma eigenvalue_pos (n : ℕ) : 0 < eigenvalue n := by linarith [eigenvalue_ge_six n]

lemma kernel_smooth : ContDiff ℝ ∞ kernel := by unfold kernel; fun_prop

lemma kernel_nonneg_time {t : ℝ} (ht : 0 ≤ t) : kernel t = exp (-t) := by
  simp [kernel, smoothTransition.one_of_one_le (show 1 ≤ t + 1 by linarith)]

lemma kernel_zero {t : ℝ} (ht : t ≤ -1) : kernel t = 0 := by
  simp [kernel, smoothTransition.zero_of_nonpos (show t + 1 ≤ 0 by linarith)]

lemma kernel_derivative_bounded (b : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ t, ‖iteratedDeriv b kernel t‖ ≤ C := by
  have hc : Continuous (iteratedDeriv b kernel) :=
    kernel_smooth.continuous_iteratedDeriv b (by exact_mod_cast (le_top : (b : ℕ∞) ≤ ⊤))
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 1, le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro t
  by_cases htlo : t < -2
  · have heq : kernel =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds (show t < -1 by linarith)] with x hx
      exact kernel_zero hx.le
    rw [heq.iteratedDeriv_eq b]
    simp [le_trans zero_le_one (le_max_right C 1)]
  by_cases hthi : 1 < t
  · have heq : kernel =ᶠ[𝓝 t] (fun x => exp (-1 * x)) := by
      filter_upwards [Ioi_mem_nhds (show 0 < t by linarith)] with x hx
      simpa using kernel_nonneg_time hx.le
    rw [heq.iteratedDeriv_eq b, iteratedDeriv_exp_const_mul]
    have he : exp (-t) ≤ 1 := exp_le_one_iff.2 (by linarith)
    calc
      ‖(-1 : ℝ) ^ b * exp (-1 * t)‖ = exp (-t) := by
        rw [norm_mul, norm_pow]
        simp [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      _ ≤ 1 := he
      _ ≤ max C 1 := le_max_right _ _
  · exact (hC t ⟨not_lt.mp htlo, not_lt.mp hthi⟩).trans (le_max_left _ _)

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def Rapid (coeff : ℕ → B) : Prop :=
  ∀ b : ℕ, Summable (fun n => eigenvalue n ^ b * ‖coeff n‖)

def inverseCoeff (coeff : ℕ → B) (n : ℕ) : B :=
  (1 - eigenvalue n / 2)⁻¹ • coeff n

lemma inverse_denominator_bound (n : ℕ) : |(1 - eigenvalue n / 2)⁻¹| ≤ 1 / 2 := by
  have he := eigenvalue_ge_six n
  have hd : 2 ≤ |1 - eigenvalue n / 2| := by
    rw [abs_of_neg (by linarith)]
    linarith
  rw [abs_inv]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hd

omit [CompleteSpace B] in
lemma inverseCoeff_rapid [CompleteSpace B] (coeff : ℕ → B) (h : Rapid coeff) : Rapid (inverseCoeff coeff) := by
  intro b
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (eigenvalue_pos n).le _) (norm_nonneg _))
    _ ((h b).mul_left (1 / 2))
  intro n
  rw [inverseCoeff, norm_smul, Real.norm_eq_abs]
  calc
    eigenvalue n ^ b * (|(1 - eigenvalue n / 2)⁻¹| * ‖coeff n‖) ≤
      eigenvalue n ^ b * ((1 / 2) * ‖coeff n‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (inverse_denominator_bound n) (norm_nonneg _))
          (pow_nonneg (eigenvalue_pos n).le _)
    _ = (1 / 2) * (eigenvalue n ^ b * ‖coeff n‖) := by ring

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C] [CompleteSpace C]

end
end CKSSpectralHeat

end

end OAI
end

section
namespace OAI


noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff

lemma U_open : IsOpen U := isClosed_singleton.isOpen_compl

attribute [local instance] CKSLorentz.two_atLeastTwo

lemma expand_vec (x : E) : x = ∑ i : Ix, x i • e i := by
  ext j
  simp [e_apply]

def third (F : E → ℝ) (x : E) : Ix → Mat := fun k i j => pd k (pd i (pd j F)) x

lemma partial_smooth {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) (i : Ix) :
    ContDiffOn ℝ ∞ (pd i F) U :=
  (hF.fderiv_of_isOpen U_open (by simp)).clm_apply contDiffOn_const

lemma hess_smooth {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) (i j : Ix) :
    ContDiffOn ℝ ∞ (fun x => hess F x i j) U :=
  partial_smooth (partial_smooth hF j) i

lemma partial_partial {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E} (hx : x ∈ U)
    (i j : Ix) :
    pd i (pd j F) x = fderiv ℝ (fderiv ℝ F) x (e i) (e j) := by
  have hd := ((hF.fderiv_of_isOpen (m := ∞) U_open (by simp)).contDiffAt
    (U_open.mem_nhds hx)).differentiableAt (by simp)
  unfold pd
  rw [fderiv_clm_apply hd (differentiableAt_const (e j))]
  simp

lemma partial_comm {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E} (hx : x ∈ U)
    (i j : Ix) : pd i (pd j F) x = pd j (pd i F) x := by
  rw [partial_partial hF hx, partial_partial hF hx]
  exact ((hF.contDiffAt (U_open.mem_nhds hx)).isSymmSndFDerivAt (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using (ENat.LEInfty.out (m := 2)))).eq _ _

lemma third_cycle {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E} (hx : x ∈ U)
    (k i j : Ix) : third F x k i j = third F x j k i := by
  change pd k (pd i (pd j F)) x = pd j (pd k (pd i F)) x
  have he : pd i (pd j F) =ᶠ[𝓝 x] pd j (pd i F) := by
    filter_upwards [U_open.mem_nhds hx] with y hy
    exact partial_comm hF hy i j
  have he' := congrArg (fun A : E →L[ℝ] ℝ => A (e k)) (he.fderiv_eq)
  change pd k (pd i (pd j F)) x = pd k (pd j (pd i F)) x at he'
  rw [he', partial_comm (partial_smooth hF i) hx k j]

lemma fderiv_expand (F : E → ℝ) (x v : E) : fderiv ℝ F x v = ∑ i, v i * grad F x i := by
  conv_lhs => rw [expand_vec v]
  simp only [map_sum, map_smul, smul_eq_mul, grad, pd]

lemma smooth_diff {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E} (hx : x ∈ U) :
    DifferentiableAt ℝ F x := (hF.contDiffAt (U_open.mem_nhds hx)).differentiableAt (by simp)

lemma pd_add {F G : E → ℝ} {x : E} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) (k : Ix) :
    pd k (fun y => F y + G y) x = pd k F x + pd k G x := by
  simp only [pd, fderiv_fun_add hF hG, add_apply]

lemma pd_sub {F G : E → ℝ} {x : E} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) (k : Ix) :
    pd k (fun y => F y - G y) x = pd k F x - pd k G x := by
  simp only [pd, fderiv_fun_sub hF hG, sub_apply]

lemma pd_mul {F G : E → ℝ} {x : E} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) (k : Ix) :
    pd k (fun y => F y * G y) x = pd k F x * G x + F x * pd k G x := by
  rw [pd, fderiv_fun_mul hF hG]
  simp only [add_apply, smul_apply, smul_eq_mul, pd]
  ring

lemma pd_sum {J : Type*} (s : Finset J) {A : J → E → ℝ} {x : E}
    (hA : ∀ j ∈ s, DifferentiableAt ℝ (A j) x) (k : Ix) :
    pd k (fun y => ∑ j ∈ s, A j y) x = ∑ j ∈ s, pd k (A j) x := by
  simp only [pd, fderiv_fun_sum hA, _root_.sum_apply]

lemma pd_const_mul {F : E → ℝ} {x : E} (hF : DifferentiableAt ℝ F x)
    (c : ℝ) (k : Ix) : pd k (fun y => c * F y) x = c * pd k F x := by
  erw [pd_mul (differentiableAt_const c) hF, pd_const, zero_mul, zero_add]

lemma pd_div_const {F : E → ℝ} {x : E} (hF : DifferentiableAt ℝ F x)
    (c : ℝ) (k : Ix) : pd k (fun y => F y / c) x = pd k F x / c := by
  simp_rw [div_eq_mul_inv, mul_comm _ c⁻¹]
  exact pd_const_mul hF _ k

lemma coordinate_smooth (i : Ix) : ContDiffOn ℝ ∞ (fun x : E => x i) U :=
  (EuclideanSpace.proj (𝕜 := ℝ) (ι := Ix) i).contDiff.contDiffOn

lemma proj_smooth (i j : Ix) : ContDiffOn ℝ ∞ (fun x : E => proj (fun a => x a) i j) U :=
  contDiffOn_const.sub ((coordinate_smooth i).mul (coordinate_smooth j))

lemma pd_proj (x : E) (k i j : Ix) :
    pd k (fun y : E => proj (fun a => y a) i j) x = dproj (fun a => x a) k i j := by
  unfold proj
  erw [pd_sub (differentiableAt_const (if i = j then (1 : ℝ) else 0)) ((EuclideanSpace.proj i).differentiableAt.fun_mul
    (EuclideanSpace.proj j).differentiableAt), pd_const,
    pd_mul (EuclideanSpace.proj i).differentiableAt (EuclideanSpace.proj j).differentiableAt]
  simp only [partial_of_clm, EuclideanSpace.proj, PiLp.proj_apply, e_apply, eq_comm, dproj]
  ring

lemma trace_smooth {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (fun x => tangentTrace (fun a => x a) (hess F x)) U := by
  unfold tangentTrace
  exact ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
    (proj_smooth i j).mul (hess_smooth hF i j)))

lemma pd_tangentTrace {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E} (hx : x ∈ U)
    (k : Ix) : pd k (fun y => tangentTrace (fun a => y a) (hess F y)) x =
      dTangentTrace (fun a => x a) (hess F x) (third F x) k := by
  unfold tangentTrace dTangentTrace
  rw [pd_sum univ (fun i _ => smooth_diff
    (ContDiffOn.sum (fun j _ => (proj_smooth i j).mul (hess_smooth hF i j))) hx)]
  apply sum_congr rfl
  intro i hi
  rw [pd_sum univ (fun j _ => smooth_diff ((proj_smooth i j).mul (hess_smooth hF i j)) hx)]
  apply sum_congr rfl
  intro j hj
  erw [pd_mul (smooth_diff (proj_smooth i j) hx) (smooth_diff (hess_smooth hF i j) hx), pd_proj]
  rfl

lemma roundLaplacian_smooth {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (roundLaplacian F) U :=
  (trace_smooth hF).sub (contDiffOn_const.mul (ContDiffOn.sum (fun i _ =>
    (coordinate_smooth i).mul (partial_smooth hF i))))

lemma pd_roundLaplacian {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E} (hx : x ∈ U)
    (k : Ix) : pd k (roundLaplacian F) x =
      dRoundLap (fun a => x a) (grad F x) (hess F x) (third F x) k := by
  have hs : ContDiffOn ℝ ∞ (fun y => ∑ i : Ix, y i * pd i F y) U :=
    ContDiffOn.sum (fun i _ => (coordinate_smooth i).mul (partial_smooth hF i))
  change pd k (fun y => tangentTrace (fun a => y a) (hess F y) -
    2 * ∑ i : Ix, y i * pd i F y) x = _
  erw [pd_sub (smooth_diff (trace_smooth hF) hx) (smooth_diff ((contDiffOn_const (c := (2 : ℝ))).mul hs) hx),
    pd_tangentTrace hF hx, pd_const_mul (smooth_diff hs hx),
    pd_sum univ (fun i _ => smooth_diff ((coordinate_smooth i).mul (partial_smooth hF i)) hx)]
  simp only [grad, pd_mul (smooth_diff (coordinate_smooth _) hx)
    (smooth_diff (partial_smooth hF _) hx), pd_coordinate,
    ite_mul, one_mul, zero_mul, sum_add_distrib, sum_ite_eq, Finset.mem_univ, ite_true,
    dRoundLap, hess]

lemma pd_traceFreeHess {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E} (hx : x ∈ U)
    (k i j : Ix) : pd k (fun y => traceFreeHess F y i j) x =
      dHessTF (fun a => x a) (hess F x) (third F x) k i j := by
  have hp (a b : Ix) := smooth_diff (proj_smooth a b) hx
  have hh (a b : Ix) := smooth_diff (hess_smooth hF a b) hx
  have hcore : DifferentiableAt ℝ (fun y : E =>
      ∑ a, ∑ b, proj (fun c => y c) i a * hess F y a b * proj (fun c => y c) b j) x :=
    DifferentiableAt.fun_sum (fun a _ => DifferentiableAt.fun_sum (fun b _ => ((hp i a).fun_mul (hh a b)).fun_mul (hp b j)))
  unfold traceFreeHess hessTF
  erw [pd_sub hcore ((smooth_diff ((trace_smooth hF).div_const 2) hx).fun_mul (hp i j)),
    pd_mul (smooth_diff ((trace_smooth hF).div_const 2) hx) (hp i j),
    pd_div_const (smooth_diff (trace_smooth hF) hx), pd_tangentTrace hF hx, pd_proj]
  rw [pd_sum univ (fun a _ => DifferentiableAt.fun_sum (fun b _ =>
    ((hp i a).fun_mul (hh a b)).fun_mul (hp b j)))]
  have hs (a : Ix) : pd k (fun y : E => ∑ b,
      proj (fun c => y c) i a * hess F y a b * proj (fun c => y c) b j) x =
      ∑ b, (dproj (fun c => x c) k i a * hess F x a b * proj (fun c => x c) b j +
      proj (fun c => x c) i a * third F x k a b * proj (fun c => x c) b j +
      proj (fun c => x c) i a * hess F x a b * dproj (fun c => x c) k b j) := by
    rw [pd_sum univ (fun b _ => ((hp i a).fun_mul (hh a b)).fun_mul (hp b j))]
    apply sum_congr rfl
    intro b hb
    erw [pd_mul ((hp i a).fun_mul (hh a b)) (hp b j), pd_mul (hp i a) (hh a b), pd_proj, pd_proj]
    change (_ * _ + _ * third F x k a b) * _ + _ * _ = _
    ring
  simp_rw [hs]
  unfold dHessTF
  ring

theorem divergence_traceFreeHess {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U)
    {x : E} (hx : ‖x‖ = 1) (j : Ix) :
    tensorDivergence (traceFreeHess F) x j = sphereGradient (fun y => F y + roundLaplacian F y / 2) x j := by
  have hxU : x ∈ U := by intro h; simp [h] at hx
  have hc : tensorDivergence (traceFreeHess F) x j =
      divHessTF (fun a => x a) (hess F x) (third F x) j := by
    simp only [tensorDivergence, divHessTF, pd_traceFreeHess hF hxU]
  rw [hc, divHessTF_eq (unit_sum_sq hx) (grad F x) (hess F x) (third F x)
    (fun i j => partial_comm hF hxU i j) (fun k i j => third_cycle hF hxU k i j)]
  unfold sphereGradient grad
  apply sum_congr rfl
  intro k hk
  rw [pd_add (smooth_diff hF hxU) (smooth_diff ((roundLaplacian_smooth hF).div_const 2) hxU),
    pd_div_const (smooth_diff (roundLaplacian_smooth hF) hxU), pd_roundLaplacian hF hxU]
  rfl

end
end CKSInducedSphere

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter
open scoped Topology ContDiff

lemma eigenvalue_shift (n : ℕ) : eigenvalue (n + 2) = CKSSpectralHeat.eigenvalue n := by
  simp only [eigenvalue, CKSSpectralHeat.eigenvalue, Nat.cast_add, Nat.cast_ofNat]
  ring

lemma radialExtension_norm_bound (f : C(Sphere, ℝ)) (x : Ambient) :
    ‖radialExtension f x‖ ≤ ‖f‖ := by
  by_cases hx : x ≠ 0
  · rw [radialExtension, dite_eq_left hx]
    exact ContinuousMap.norm_coe_le_norm f _
  · simp [radialExtension, hx]

def angularField (i j : Fin 3) (x : Ambient) : Ambient →L[ℝ] ℝ :=
  (x i / ‖x‖ ^ 2) • EuclideanSpace.proj j

lemma angularField_smooth (i j : Fin 3) : ContDiffOn ℝ ∞ (angularField i j) puncturedSpace := by
  have hn : ContDiffOn ℝ ∞ (fun x : Ambient => ‖x‖) puncturedSpace := by
    intro x hx
    exact (contDiffAt_norm ℝ hx).contDiffWithinAt
  exact ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).contDiff.contDiffOn.div (hn.pow 2)
    (fun x hx => pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).smul contDiffOn_const

lemma radial_polynomial_hasFDerivAt (p : Poly) {x : Ambient} (hx : x ≠ 0) :
    HasFDerivAt (radialExtension (sphereEval p))
      (∑ i : Fin 3, ∑ j : Fin 3,
        radialExtension (sphereEval (rotation i j p)) x • angularField i j x) x := by
  have hd := ((radialExtension_smooth (polynomial_sphere_smooth p)).contDiffAt
    (puncturedSpace.isOpen.mem_nhds hx)).differentiableAt (by simp)
  convert! hd.hasFDerivAt using 1
  ext v
  rw [radial_polynomial_fderiv p hx v]
  simp only [sum_apply, smul_apply, smul_eq_mul,
    angularField, EuclideanSpace.proj, PiLp.proj_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma temporalJet_hasDerivAt (b n : ℕ) (t : ℝ) :
    HasDerivAt (temporalJet b n) (temporalJet (b + 1) n t) t := by
  have hk := (CKSSpectralHeat.kernel_smooth.differentiable_iteratedDeriv b
    (by exact_mod_cast (ENat.natCast_lt_top b))).differentiableAt (x := CKSSpectralHeat.eigenvalue n * t) |>.hasDerivAt
  have h := (hk.comp t ((hasDerivAt_id t).const_mul (CKSSpectralHeat.eigenvalue n))).const_mul
    (CKSSpectralHeat.eigenvalue n ^ b)
  convert! h using 1
  simp only [temporalJet, iteratedDeriv_succ, pow_succ]
  ring

lemma temporalJet_bound (b : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n t,
    ‖temporalJet b n t‖ ≤ C * CKSSpectralHeat.eigenvalue n ^ b := by
  obtain ⟨C, hC, hb⟩ := CKSSpectralHeat.kernel_derivative_bounded b
  refine ⟨C, hC, fun n t => ?_⟩
  rw [temporalJet, norm_mul, norm_pow, Real.norm_eq_abs,
    abs_of_pos (CKSSpectralHeat.eigenvalue_pos n)]
  nlinarith [mul_le_mul_of_nonneg_left (hb (CKSSpectralHeat.eigenvalue n * t))
    (pow_nonneg (CKSSpectralHeat.eigenvalue_pos n).le b)]

def heatDomain : Set SpaceTime := {z | z.2 ≠ 0}

lemma heatDomain_open : IsOpen heatDomain :=
  isOpen_ne_fun continuous_snd continuous_const

def heatField : Option (Fin 3 × Fin 3) → SpaceTime → SpaceTime →L[ℝ] ℝ
  | none, _ => ContinuousLinearMap.fst ℝ ℝ Ambient
  | some ij, z => (angularField ij.1 ij.2 z.2).comp (ContinuousLinearMap.snd ℝ ℝ Ambient)

lemma heatField_smooth (o : Option (Fin 3 × Fin 3)) : ContDiffOn ℝ ∞ (heatField o) heatDomain := by
  cases o with
  | none => exact contDiffOn_const
  | some ij =>
    exact ((angularField_smooth ij.1 ij.2).comp contDiffOn_snd
      (fun z hz => hz)).clm_comp contDiffOn_const

def heatNext (a : HeatJet) : Option (Fin 3 × Fin 3) → HeatJet
  | none => (a.1 + 1, a.2)
  | some ij => (a.1, ij :: a.2)

lemma heatTerm_derivative_identity (p : ℕ → Poly) (a : HeatJet) (n : ℕ) (z : SpaceTime) :
    (∑ o : Option (Fin 3 × Fin 3), heatTerm p (heatNext a o) n z • heatField o z) =
    temporalJet a.1 n z.1 •
      ((∑ i : Fin 3, ∑ j : Fin 3,
        radialExtension (sphereEval (rotation i j (rotationWord a.2 (p n)))) z.2 •
          angularField i j z.2).comp (ContinuousLinearMap.snd ℝ ℝ Ambient)) +
    radialExtension (sphereEval (rotationWord a.2 (p n))) z.2 •
      ((ContinuousLinearMap.toSpanSingleton ℝ (temporalJet (a.1 + 1) n z.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ Ambient)) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [Fintype.sum_option, Fintype.sum_prod_type, heatTerm, heatNext, heatField,
    rotationWord, sum_apply, smul_apply,
    add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, Finset.mul_sum]
  simp only [mul_assoc, mul_left_comm, mul_comm]
  exact add_comm _ _

lemma heatTerm_hasFDerivAt (p : ℕ → Poly) (a : HeatJet) (n : ℕ) (z : SpaceTime)
    (hz : z ∈ heatDomain) :
    HasFDerivAt (heatTerm p a n)
      (∑ o : Option (Fin 3 × Fin 3), heatTerm p (heatNext a o) n z • heatField o z) z := by
  have ht := (temporalJet_hasDerivAt a.1 n z.1).hasFDerivAt.comp z
    (ContinuousLinearMap.fst ℝ ℝ Ambient).hasFDerivAt
  have hx := (radial_polynomial_hasFDerivAt (rotationWord a.2 (p n)) hz).comp z
    (ContinuousLinearMap.snd ℝ ℝ Ambient).hasFDerivAt
  rw [heatTerm_derivative_identity]
  convert! ht.mul hx using 1

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix e grad hess pd proj roundLaplacian sphereGradient tensorDivergence)
open scoped Topology ContDiff

lemma thetaFrame_smooth : ContDiff ℝ ∞ thetaFrame := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i <;> dsimp [thetaFrame] <;> fun_prop
lemma phiUnit_smooth : ContDiff ℝ ∞ phiUnit := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i <;> dsimp [phiUnit] <;> fun_prop

lemma angular_chain {F : E → ℝ} {x : Point}
    (hF : DifferentiableAt ℝ F (sphereParam x)) (i : Ix) :
    D (basis i) (fun y => F (sphereParam y)) x =
      ∑ k : Ix, chartVector i x k * grad F (sphereParam x) k := by
  unfold D
  change fderiv ℝ (F ∘ sphereParam) x (basis i) = _
  rw [fderiv_comp x hF (sphereParam_smooth.differentiable (by simp) x)]
  change fderiv ℝ F (sphereParam x) (fderiv ℝ sphereParam x (basis i)) = _
  rw [fderiv_sphereParam, CKSInducedSphere.fderiv_expand]

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff
open CKSSphericalHarmonics (smoothRotation smoothCasimir rotationGenerator)

lemma rotationGenerator_eq (i j : Ix) (x : E) :
    rotationGenerator i j x = x i • e j - x j • e i := by
  ext k
  simp only [CKSSphericalHarmonics.rotationGenerator_apply, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul, e_apply]
  split_ifs <;> ring

lemma smoothRotation_pd (i j : Ix) (F : E → ℝ) (x : E) :
    smoothRotation i j F x = x i * pd j F x - x j * pd i F x := by
  rw [smoothRotation, rotationGenerator_eq]
  simp only [map_sub, map_smul, smul_eq_mul, pd]

lemma pd_smoothRotation {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E}
    (hx : x ∈ U) (i j k : Ix) :
    pd k (smoothRotation i j F) x =
      (if k = i then 1 else 0) * pd j F x + x i * hess F x k j -
      ((if k = j then 1 else 0) * pd i F x + x j * hess F x k i) := by
  have he : smoothRotation i j F = fun y => y i * pd j F y - y j * pd i F y := by
    funext y
    exact smoothRotation_pd i j F y
  rw [he]
  erw [pd_sub ((smooth_diff (coordinate_smooth i) hx).fun_mul (smooth_diff (partial_smooth hF j) hx))
    ((smooth_diff (coordinate_smooth j) hx).fun_mul (smooth_diff (partial_smooth hF i) hx)),
    pd_mul (smooth_diff (coordinate_smooth i) hx) (smooth_diff (partial_smooth hF j) hx),
    pd_mul (smooth_diff (coordinate_smooth j) hx) (smooth_diff (partial_smooth hF i) hx)]
  simp only [pd_coordinate, hess]

lemma smoothRotation_square {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E}
    (hx : x ∈ U) (i j : Ix) (hij : i ≠ j) :
    smoothRotation i j (smoothRotation i j F) x =
      x i ^ 2 * hess F x j j - 2 * x i * x j * hess F x i j +
      x j ^ 2 * hess F x i i - x i * grad F x i - x j * grad F x j := by
  rw [smoothRotation_pd, pd_smoothRotation hF hx, pd_smoothRotation hF hx]
  simp only [ite_true, ite_eq_right hij, ite_eq_right (Ne.symm hij), one_mul, zero_mul,
    grad, hess, partial_comm hF hx j i]
  ring

theorem roundLaplacian_eq_Casimir {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U)
    {x : E} (hx : ‖x‖ = 1) : roundLaplacian F x = smoothCasimir F x := by
  have hxU : x ∈ U := by intro h; simp [h] at hx
  have hs : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1 := by
    simpa only [Fin.sum_univ_three] using unit_sum_sq hx
  have hH (i j : Ix) : hess F x i j = hess F x j i := partial_comm hF hxU i j
  simp only [smoothCasimir, Pi.add_apply, smoothRotation_square hF hxU 0 1 (by decide),
    smoothRotation_square hF hxU 0 2 (by decide), smoothRotation_square hF hxU 1 2 (by decide),
    roundLaplacian, roundLap, tangentTrace, proj, Fin.sum_univ_three]
  norm_num only [show (0 : Ix) ≠ 1 by decide, show (0 : Ix) ≠ 2 by decide,
    show (1 : Ix) ≠ 0 by decide, show (1 : Ix) ≠ 2 by decide,
    show (2 : Ix) ≠ 0 by decide, show (2 : Ix) ≠ 1 by decide,
    ite_true, ite_false]
  rw [hH 1 0, hH 2 0, hH 2 1]
  linear_combination -(hess F x 0 0 + hess F x 1 1 + hess F x 2 2) * hs

end
end CKSInducedSphere

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix)
open scoped Topology ContDiff

lemma D_line {F : Point → ℝ} {x : Point} (hF : DifferentiableAt ℝ F x) (v : Point) :
    D v F x = deriv (fun s : ℝ => F (x + s • v)) 0 := by
  have hd : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x using 1
    simp
  have hf : HasFDerivAt F (fderiv ℝ F x) (x + (0:ℝ) • v) := by simpa using hF.hasFDerivAt
  have hh := hf.comp_hasDerivAt 0 hd
  simpa only [zero_smul,add_zero,D,Function.comp_def] using hh.deriv.symm

lemma D_line_congr {F G : Point → ℝ} {x : Point}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (v : Point)
    (he : ∀ s : ℝ, F (x+s•v) = G (x+s•v)) : D v F x = D v G x := by
  rw [D_line hF,D_line hG]
  congr 1
  funext s
  exact he s

lemma angular_line_radial (x : Point) (k : Ix) (hk : k ≠ 0) (s : ℝ) :
    (x+s•basis k) 0 = x 0 := by
  simp [basis,Ne.symm hk]

lemma angular_first_congr_leaf {F G : Point → ℝ} {x : Point}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x)
    (he : ∀ y : Point, y 0 = x 0 → F y = G y) (k : Ix) (hk : k ≠ 0) :
    D (basis k) F x = D (basis k) G x := by
  apply D_line_congr hF hG
  intro s
  exact he _ (angular_line_radial x k hk s)

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSDifferentialSeries
noncomputable section
open Set Filter
open scoped Topology ContDiff
variable {E I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype J]
variable {s : Set E} (hs : IsOpen s)
variable (A : J → E → E →L[ℝ] ℝ) (hA : ∀ j, ContDiffOn ℝ ∞ (A j) s)
variable (next : I → J → I) (F : I → ℕ → E → ℝ)
variable (hF : ∀ i n x, x ∈ s → HasFDerivAt (F i n)
  (∑ j, F (next i j) n x • A j x) x)
variable (bound : ∀ i, ∃ u : ℕ → ℝ, Summable u ∧ ∀ n x, x ∈ s → ‖F i n x‖ ≤ u n)

def series (i : I) (x : E) : ℝ := ∑' n, F i n x

include bound

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma series_summable [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : I) {x : E} (hx : x ∈ s) : Summable (fun n => F i n x) := by
  obtain ⟨u, hu, hb⟩ := bound i
  exact Summable.of_norm_bounded hu (fun n => hb n x hx)

include hF

lemma series_continuous (i : I) : ContinuousOn (series F i) s := by
  obtain ⟨u, hu, hb⟩ := bound i
  exact continuousOn_tsum (fun n x hx => (hF i n x hx).continuousAt.continuousWithinAt) hu hb

include hs hA

lemma series_hasFDerivAt (i : I) {x : E} (hx : x ∈ s) :
    HasFDerivAt (series F i) (∑ j, series F (next i j) x • A j x) x := by
  have bounds := bound
  choose u hu hb using bounds
  let K : ℝ := (∑ j, ‖A j x‖) + 1
  have hc : ContinuousAt (fun y => ∑ j, ‖A j y‖) x := by
    exact (continuousOn_finsetSum _ (fun j _ =>
      (hA j).continuousOn.norm)).continuousAt (hs.mem_nhds hx)
  have he : ∀ᶠ y in 𝓝 x, (∑ j, ‖A j y‖) < K :=
    hc.eventually_lt continuousAt_const (by dsimp [K]; linarith)
  have hn : {y | y ∈ s ∧ (∑ j, ‖A j y‖) < K} ∈ 𝓝 x :=
    inter_mem (hs.mem_nhds hx) he
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hn
  have hlocal (j : J) (y : E) (hy : y ∈ Metric.ball x r) : ‖A j y‖ ≤ K := by
    exact (Finset.single_le_sum (fun k _ => norm_nonneg (A k y))
      (Finset.mem_univ j)).trans (hrs hy).2.le
  have hus : Summable (fun n => K * ∑ j, u (next i j) n) :=
    (summable_sum (fun j _ => hu (next i j))).mul_left K
  have hderiv := hasFDerivAt_tsum_of_isPreconnected hus Metric.isOpen_ball
    (convex_ball x r).isPreconnected
    (fun n y hy => hF i n y (hrs hy).1)
    (fun n y hy => (show ‖∑ j, F (next i j) n y • A j y‖ ≤ K * ∑ j, u (next i j) n from by
      calc
        ‖∑ j, F (next i j) n y • A j y‖ ≤ ∑ j, ‖F (next i j) n y • A j y‖ := norm_sum_le _ _
        _ ≤ ∑ j, u (next i j) n * K := by
          apply Finset.sum_le_sum
          intro j hj
          rw [norm_smul]
          exact mul_le_mul (hb _ n y (hrs hy).1) (hlocal j y hy) (norm_nonneg _)
            ((norm_nonneg _).trans (hb _ n y (hrs hy).1))
        _ = K * ∑ j, u (next i j) n := by rw [← Finset.sum_mul]; ring))
    (Metric.mem_ball_self hr) (series_summable F bound i hx) (Metric.mem_ball_self hr)
  convert! hderiv using 1
  symm
  rw [Summable.tsum_finsetSum (fun j _ => (series_summable F bound (next i j) hx).smul_const (A j x))]
  apply Finset.sum_congr rfl
  intro j hj
  exact (series_summable F bound (next i j) hx).tsum_smul_const (A j x)

theorem series_contDiff (i : I) : ContDiffOn ℝ ∞ (series F i) s := by
  apply contDiffOn_infty.mpr
  intro N
  induction N generalizing i with
  | zero => exact contDiffOn_zero.mpr (series_continuous A next F hF bound i)
  | succ N ih =>
    rw [Nat.cast_add, Nat.cast_one]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hs.uniqueDiffOn).mpr
    refine ⟨by simp, ⟨fun x => ∑ j, series F (next i j) x • A j x, ?_, ?_⟩⟩
    · exact ContDiffOn.sum (fun j _ => (ih (next i j)).smul ((hA j).of_le (by exact_mod_cast (le_top : (N : ℕ∞) ≤ ⊤))))
    · intro x hx
      exact (series_hasFDerivAt hs A hA next F hF bound i hx).hasFDerivWithinAt

end
end CKSDifferentialSeries

end

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold

lemma heatTerm_bound (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n z, z ∈ heatDomain → ‖heatTerm p a n z‖ ≤ u n := by
  obtain ⟨C, hC, hb⟩ := temporalJet_bound a.1
  refine ⟨fun n => C * (CKSSpectralHeat.eigenvalue n ^ a.1 *
    ‖sphereEval (rotationWord a.2 (p n))‖), (hp a.2 a.1).mul_left C, ?_⟩
  intro n z hz
  dsimp only
  rw [heatTerm, norm_mul, ← mul_assoc]
  exact mul_le_mul (hb n z.1) (radialExtension_norm_bound _ _) (norm_nonneg _)
    (mul_nonneg hC (pow_nonneg (CKSSpectralHeat.eigenvalue_pos n).le _))

lemma jointHeatSeries_summable (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet)
    {z : SpaceTime} (hz : z ∈ heatDomain) : Summable (fun n => heatTerm p a n z) :=
  CKSDifferentialSeries.series_summable (heatTerm p) (heatTerm_bound p hp) a hz

theorem jointHeatSeries_smooth (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet) :
    ContDiffOn ℝ ∞ (jointHeatSeries p a) heatDomain :=
  CKSDifferentialSeries.series_contDiff heatDomain_open heatField heatField_smooth
    heatNext (heatTerm p) (heatTerm_hasFDerivAt p) (heatTerm_bound p hp) a

lemma jointHeatSeries_hasFDerivAt (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet)
    {z : SpaceTime} (hz : z ∈ heatDomain) :
    HasFDerivAt (jointHeatSeries p a)
      (∑ o : Option (Fin 3 × Fin 3), jointHeatSeries p (heatNext a o) z • heatField o z) z :=
  CKSDifferentialSeries.series_hasFDerivAt heatDomain_open heatField heatField_smooth
    heatNext (heatTerm p) (heatTerm_hasFDerivAt p) (heatTerm_bound p hp) a hz

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix e grad hess pd proj roundLaplacian sphereGradient tensorDivergence)
open scoped Topology ContDiff

lemma D_neg (v : Point) (f : Point → ℝ) (x : Point) :
    D v (fun y => -f y) x = -D v f x := by simp [D, fderiv_fun_neg]

def equator (x : Point) : E := WithLp.toLp 2 ![Real.cos (x 2),Real.sin (x 2),0]

lemma theta_theta (x : Point) : fderiv ℝ thetaFrame x (basis 1) = -sphereParam x := by
  ext j
  rw [component_fderiv (thetaFrame_smooth.differentiable (by simp) x)]
  have hd1 : DifferentiableAt ℝ (fun y : Point => y 1) x := (coord 1).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun y : Point => y 2) x := (coord 2).differentiableAt
  have dc (a b : Ix) : D (basis a) (fun y : Point => y b) x = if b = a then 1 else 0 := D_coord a b x
  fin_cases j <;> dsimp [thetaFrame,sphereParam]
  all_goals
    simp only [D_mul _ hd1.cos hd2.cos, D_mul _ hd1.cos hd2.sin,
      D_sin _ hd1,D_sin _ hd2,D_cos _ hd1,D_cos _ hd2,dc, D_neg,
      Fin.reduceEq,ite_true,ite_false]
    ring

lemma theta_phi (x : Point) : fderiv ℝ thetaFrame x (basis 2) = Real.cos (x 1) • phiUnit x := by
  ext j
  rw [component_fderiv (thetaFrame_smooth.differentiable (by simp) x)]
  have hd1 : DifferentiableAt ℝ (fun y : Point => y 1) x := (coord 1).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun y : Point => y 2) x := (coord 2).differentiableAt
  have dc (a b : Ix) : D (basis a) (fun y : Point => y b) x = if b = a then 1 else 0 := D_coord a b x
  fin_cases j <;> dsimp [thetaFrame,phiUnit]
  all_goals
    simp only [D_mul _ hd1.cos hd2.cos, D_mul _ hd1.cos hd2.sin,
      D_sin _ hd1,D_sin _ hd2,D_cos _ hd1,D_cos _ hd2,dc, D_neg,
      Fin.reduceEq,ite_true,ite_false]
    ring

lemma unit_theta (x : Point) : fderiv ℝ phiUnit x (basis 1) = 0 := by
  ext j
  rw [component_fderiv (phiUnit_smooth.differentiable (by simp) x)]
  have hd2 : DifferentiableAt ℝ (fun y : Point => y 2) x := (coord 2).differentiableAt
  have dc (a b : Ix) : D (basis a) (fun y : Point => y b) x = if b = a then 1 else 0 := D_coord a b x
  fin_cases j <;> dsimp [phiUnit]
  all_goals
    simp only [D_neg, D_sin _ hd2,D_cos _ hd2,dc,D_const, Fin.reduceEq, ite_false]
    <;> ring

lemma unit_phi (x : Point) : fderiv ℝ phiUnit x (basis 2) = -equator x := by
  ext j
  rw [component_fderiv (phiUnit_smooth.differentiable (by simp) x)]
  have hd2 : DifferentiableAt ℝ (fun y : Point => y 2) x := (coord 2).differentiableAt
  have dc (a b : Ix) : D (basis a) (fun y : Point => y b) x = if b = a then 1 else 0 := D_coord a b x
  fin_cases j <;> dsimp [phiUnit,equator]
  all_goals
    simp only [D_neg, D_sin _ hd2,D_cos _ hd2,dc,D_const, ite_true]
    ring

lemma equator_decomposition (x : Point) : equator x =
    Real.sin (x 1) • sphereParam x + Real.cos (x 1) • thetaFrame x := by
  ext i
  fin_cases i <;> dsimp [equator,sphereParam,thetaFrame]
  · linear_combination -Real.cos (x 2) * (Real.sin_sq_add_cos_sq (x 1))
  · linear_combination -Real.sin (x 2) * (Real.sin_sq_add_cos_sq (x 1))
  · ring

lemma projected_frame (x : Point) (i j : Ix) :
    proj (fun k => sphereParam x k) i j =
      thetaFrame x i * thetaFrame x j + phiUnit x i * phiUnit x j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [proj,sphereParam,thetaFrame,phiUnit,Fin.reduceEq]
  all_goals ring_nf <;> simp only [Real.sin_sq] <;> ring

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

lemma positive_uIcc {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : uIcc a r ⊆ Ioi 0 := by
  intro s hs
  exact lt_of_lt_of_le (lt_min ha hr) hs.1

lemma positive_interval_integrable {q : ℝ → ℝ} (hq : ContinuousOn q (Ioi 0))
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : IntervalIntegrable q volume a r :=
  (hq.mono (positive_uIcc ha hr)).intervalIntegrable

lemma primitive_hasDerivAt {q : ℝ → ℝ} (hq : ContinuousOn q (Ioi 0))
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : HasDerivAt (primitive a q) (q r) r := by
  exact intervalIntegral.integral_hasDerivAt_right (positive_interval_integrable hq ha hr)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hq r hr)
    (hq.continuousAt (isOpen_Ioi.mem_nhds hr))

lemma primitive_smooth {q : ℝ → ℝ} (hq : ContDiffOn ℝ ∞ q (Ioi 0))
    {a : ℝ} (ha : 0 < a) : ContDiffOn ℝ ∞ (primitive a q) (Ioi 0) := by
  apply (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mpr
  constructor
  · intro r hr
    exact (primitive_hasDerivAt hq.continuousOn ha hr).differentiableAt.differentiableWithinAt
  · exact hq.congr (fun r hr => (primitive_hasDerivAt hq.continuousOn ha hr).deriv)

lemma paddingDensity_smooth : ContDiffOn ℝ ∞ paddingDensity (Ioi 0) := by
  exact contDiffOn_const.div (contDiffOn_id.mul (contDiffOn_id.sqrt (fun r hr => ne_of_gt hr)))
    (fun r hr => mul_ne_zero (ne_of_gt hr) (Real.sqrt_ne_zero'.mpr hr))

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter MvPolynomial
open scoped Topology ContDiff Manifold

lemma jointHeatSeries_fderiv_tsum (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet)
    {z : SpaceTime} (hz : z ∈ heatDomain) (v : SpaceTime) :
    fderiv ℝ (jointHeatSeries p a) z v = ∑' n,
      (∑ o : Option (Fin 3 × Fin 3), heatTerm p (heatNext a o) n z • heatField o z) v := by
  rw [(jointHeatSeries_hasFDerivAt p hp a hz).fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  rw [Summable.tsum_finsetSum (fun o _ =>
    (jointHeatSeries_summable p hp (heatNext a o) hz).mul_right (heatField o z v))]
  apply Finset.sum_congr rfl
  intro o ho
  exact (tsum_mul_right).symm

lemma heatTerm_directional_rotation (p : ℕ → Poly) (a : HeatJet) (n : ℕ)
    (t : ℝ) {x : Ambient} (hx : x ≠ 0) (i j : Fin 3) :
    (∑ o : Option (Fin 3 × Fin 3), heatTerm p (heatNext a o) n (t, x) • heatField o (t, x))
      (0, rotationGenerator i j x) = heatTerm p (a.1, (i,j) :: a.2) n (t, x) := by
  rw [heatTerm_derivative_identity]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, zero_mul, mul_zero, add_zero]
  rw [← (radial_polynomial_hasFDerivAt (rotationWord a.2 (p n)) hx).fderiv]
  change temporalJet a.1 n t * smoothRotation i j
    (radialExtension (sphereEval (rotationWord a.2 (p n)))) x = _
  rw [smoothRotation_radial_polynomial _ i j hx]
  rfl

lemma spatialHeat_smooth (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet) (t : ℝ) :
    ContDiffOn ℝ ∞ (spatialHeat p a t) puncturedSpace :=
  (jointHeatSeries_smooth p hp a).comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => hx)

lemma spatialHeat_rotation (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet)
    (t : ℝ) {x : Ambient} (hx : x ≠ 0) (i j : Fin 3) :
    smoothRotation i j (spatialHeat p a t) x = spatialHeat p (a.1, (i,j) :: a.2) t x := by
  have hd := (jointHeatSeries_hasFDerivAt p hp a (z := (t,x)) hx).comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  change HasFDerivAt (spatialHeat p a t) _ x at hd
  rw [smoothRotation, hd.fderiv]
  change (∑ o, jointHeatSeries p (heatNext a o) (t,x) • heatField o (t,x))
    (0, rotationGenerator i j x) = _
  rw [← (jointHeatSeries_hasFDerivAt p hp a hx).fderiv,
    jointHeatSeries_fderiv_tsum p hp a hx]
  simp_rw [heatTerm_directional_rotation p a _ t hx i j]
  rfl

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix e grad hess pd proj roundLaplacian sphereGradient tensorDivergence U)
open scoped Topology ContDiff

lemma sphereParam_mem (x : Point) : sphereParam x ∈ U := by
  intro h
  have hn := sphereParam_norm x
  simp [h] at hn

lemma angular_smooth {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) :
    ContDiff ℝ ∞ (fun y => F (sphereParam y)) :=
  hF.comp_contDiff sphereParam_smooth sphereParam_mem

lemma angular_first {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) (i : Ix) :
    (D (basis i) (fun y => F (sphereParam y))) =
      fun y => fderiv ℝ F (sphereParam y) (chartVector i y) := by
  funext x
  rw [angular_chain (CKSInducedSphere.smooth_diff hF (sphereParam_mem x)),
    CKSInducedSphere.fderiv_expand]

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

lemma paddingWeight_smooth (R : ℝ) : ContDiff ℝ ∞ (paddingWeight R) := by
  unfold paddingWeight
  fun_prop

lemma paddingIntegrand_smooth (R : ℝ) :
    ContDiffOn ℝ ∞ (fun r => paddingWeight R r * paddingDensity r) (Ioi 0) :=
  (paddingWeight_smooth R).contDiffOn.mul paddingDensity_smooth
lemma paddingMass_smooth {R : ℝ} (hR : 0 < R) : ContDiffOn ℝ ∞ (paddingMass R) (Ioi 0) :=
  primitive_smooth (paddingIntegrand_smooth R) hR

lemma heatDensity_smooth {R : ℝ} (hR : 0 < R) : ContDiffOn ℝ ∞ (heatDensity R) (Ioi 0) := by
  unfold heatDensity
  exact (bendingZeta_smooth R).contDiffOn.div
    ((contDiffOn_const.mul contDiffOn_id).mul (contDiffOn_const.add ((bendingV_smooth hR).pow 2)))
    (fun r hr => ne_of_gt (mul_pos (mul_pos (by norm_num) hr) (by positivity)))

lemma heatTime_smooth {R : ℝ} (hR : 0 < R) : ContDiffOn ℝ ∞ (heatTime R) (Ioi 0) :=
  primitive_smooth (heatDensity_smooth hR) (by positivity)

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff
open CKSSphericalHarmonics

inductive HeatGenerated (p : ℕ → Poly) : (ℝ → E → ℝ) → Prop
  | basic (a : HeatJet) : HeatGenerated p (spatialHeat p a)
  | zero : HeatGenerated p (fun _ _ => 0)
  | add {F G} : HeatGenerated p F → HeatGenerated p G →
      HeatGenerated p (fun t x => F t x + G t x)
  | coeff (c : E → ℝ) {F} : ContDiffOn ℝ ∞ c U → HeatGenerated p F →
      HeatGenerated p (fun t x => c x * F t x)
  | congr {F G} : HeatGenerated p F → (∀ t x, x ∈ U → F t x = G t x) →
      HeatGenerated p G

variable {p : ℕ → Poly} (hp : PolynomialRapid p)
include hp

lemma HeatGenerated.joint_smooth {F : ℝ → E → ℝ} (hF : HeatGenerated p F) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain := by
  induction hF with
  | basic a => exact jointHeatSeries_smooth p hp a
  | zero => exact contDiffOn_const
  | add _ _ hF hG => exact hF.add hG
  | coeff c hc _ hF =>
    exact (hc.comp contDiffOn_snd (fun z hz => hz)).mul hF
  | congr _ he hF =>
    exact hF.congr (fun z hz => (he z.1 z.2 hz).symm)

lemma HeatGenerated.spatial_smooth {F : ℝ → E → ℝ} (hF : HeatGenerated p F) (t : ℝ) :
    ContDiffOn ℝ ∞ (F t) U :=
  (hF.joint_smooth hp).comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => hx)

omit hp in
lemma HeatGenerated.sum {J : Type*} (s : Finset J) {F : J → ℝ → E → ℝ}
    (h : ∀ j ∈ s, HeatGenerated p (F j)) :
    HeatGenerated p (fun t x => ∑ j ∈ s, F j t x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (HeatGenerated.zero (p := p))
  | @insert j s hj ih =>
    simpa only [Finset.sum_insert hj] using
      (h j (mem_insert_self j s)).add (ih (fun k hk => h k (mem_insert_of_mem hk)))

omit hp in
lemma angularCoefficient_smooth (i : Ix) :
    ContDiffOn ℝ ∞ (fun x : E => x i / ‖x‖ ^ 2) U := by
  have hn : ContDiffOn ℝ ∞ (fun x : E => ‖x‖) U := by
    intro x hx
    exact (contDiffAt_norm ℝ hx).contDiffWithinAt
  exact (coordinate_smooth i).div (hn.pow 2)
    (fun x hx => pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

lemma pd_spatialHeat (a : HeatJet) (t : ℝ) {x : E} (hx : x ∈ U) (j : Ix) :
    pd j (spatialHeat p a t) x =
      ∑ i : Ix, (x i / ‖x‖ ^ 2) * spatialHeat p (a.1, (i,j) :: a.2) t x := by
  have hd := (jointHeatSeries_hasFDerivAt p hp a (z := (t,x)) hx).comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  change HasFDerivAt (spatialHeat p a t) _ x at hd
  rw [pd, hd.fderiv]
  change (∑ o, jointHeatSeries p (heatNext a o) (t,x) • heatField o (t,x)) (0, e j) = _
  simp only [Fintype.sum_option, add_apply,
    _root_.sum_apply, smul_apply, heatField,
    angularField, ContinuousLinearMap.coe_fst', ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', smul_eq_mul, mul_zero, zero_add,
    Fintype.sum_prod_type, EuclideanSpace.proj, PiLp.proj_apply, e_apply, heatNext]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  apply sum_congr rfl
  intro i hi
  exact mul_comm _ _

lemma HeatGenerated.partial {F : ℝ → E → ℝ} (hF : HeatGenerated p F) (j : Ix) :
    HeatGenerated p (fun t x => pd j (F t) x) := by
  induction hF with
  | basic a =>
    apply HeatGenerated.congr (HeatGenerated.sum univ (fun i _ =>
      HeatGenerated.coeff _ (angularCoefficient_smooth i) (HeatGenerated.basic (a.1,(i,j)::a.2))))
    intro t x hx
    exact (pd_spatialHeat hp a t hx j).symm
  | zero => simpa only [pd_const] using (HeatGenerated.zero (p := p))
  | @add F G hF hG ihF ihG =>
    apply HeatGenerated.congr (ihF.add ihG)
    intro t x hx
    exact (pd_add (smooth_diff (hF.spatial_smooth hp t) hx)
      (smooth_diff (hG.spatial_smooth hp t) hx) j).symm
  | @coeff c F hc hF ih =>
    apply HeatGenerated.congr ((HeatGenerated.coeff _ (partial_smooth hc j) hF).add
      (HeatGenerated.coeff _ hc ih))
    intro t x hx
    exact (pd_mul (smooth_diff hc hx) (smooth_diff (hF.spatial_smooth hp t) hx) j).symm
  | @congr F G hF he ih =>
    apply HeatGenerated.congr ih
    intro t x hx
    have he' : F t =ᶠ[𝓝 x] G t := by
      filter_upwards [U_open.mem_nhds hx] with y hy
      exact he t y hy
    exact congrArg (fun A : E →L[ℝ] ℝ => A (e j)) he'.fderiv_eq

end
end CKSInducedSphere

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter MvPolynomial
open scoped Topology ContDiff Manifold

lemma smoothRotation_congr {F G : Ambient → ℝ} (h : EqOn F G puncturedSpace)
    (i j : Fin 3) {x : Ambient} (hx : x ≠ 0) :
    smoothRotation i j F x = smoothRotation i j G x := by
  have he : F =ᶠ[𝓝 x] G := by
    filter_upwards [puncturedSpace.isOpen.mem_nhds hx] with y hy
    exact h hy
  rw [smoothRotation, smoothRotation, he.fderiv_eq]

lemma spatialHeat_casimir (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet)
    (t : ℝ) {x : Ambient} (hx : x ≠ 0) :
    smoothCasimir (spatialHeat p a t) x =
      spatialHeat p (a.1, (0,1) :: (0,1) :: a.2) t x +
      spatialHeat p (a.1, (0,2) :: (0,2) :: a.2) t x +
      spatialHeat p (a.1, (1,2) :: (1,2) :: a.2) t x := by
  have h (i j : Fin 3) : smoothRotation i j (smoothRotation i j (spatialHeat p a t)) x =
      spatialHeat p (a.1, (i,j) :: (i,j) :: a.2) t x := by
    rw [smoothRotation_congr (fun y hy => spatialHeat_rotation p hp a t hy i j) i j hx]
    exact spatialHeat_rotation p hp _ t hx i j
  simp only [smoothCasimir, Pi.add_apply]
  rw [h 0 1, h 0 2, h 1 2]

lemma radialExtension_poly_add (p q : Poly) (x : Ambient) :
    radialExtension (sphereEval (p + q)) x =
      radialExtension (sphereEval p) x + radialExtension (sphereEval q) x := by
  by_cases hx : x ≠ 0 <;> simp [radialExtension, hx]

lemma radialExtension_poly_smul (c : ℝ) (p : Poly) (x : Ambient) :
    radialExtension (sphereEval (c • p)) x = c * radialExtension (sphereEval p) x := by
  by_cases hx : x ≠ 0 <;> simp [radialExtension, hx]

lemma rotationWord_smul (w : List (Fin 3 × Fin 3)) (c : ℝ) (p : Poly) :
    rotationWord w (c • p) = c • rotationWord w p := by
  induction w with
  | nil => rfl
  | cons ij w ih => simp only [rotationWord, ih, Derivation.map_smul]

def HighHarmonic (p : ℕ → Poly) : Prop :=
  ∀ n, (p n).IsHomogeneous (n + 2) ∧ laplacian (p n) = 0

lemma heatPolynomials_harmonic (f : C(Sphere, ℝ)) : HighHarmonic (heatPolynomials f) := by
  intro n
  exact ⟨(harmonicCoefficientPolynomial_spec (n+2) (toL2 f)).1,
    (harmonicCoefficientPolynomial_spec (n+2) (toL2 f)).2.1⟩

lemma heatTerm_casimir (p : ℕ → Poly) (hh : HighHarmonic p) (a : HeatJet)
    (n : ℕ) (z : SpaceTime) :
    heatTerm p (a.1, (0,1) :: (0,1) :: a.2) n z +
    heatTerm p (a.1, (0,2) :: (0,2) :: a.2) n z +
    heatTerm p (a.1, (1,2) :: (1,2) :: a.2) n z =
      -CKSSpectralHeat.eigenvalue n * heatTerm p a n z := by
  have he := harmonic_rotation_eigenvalue (rotationWord_harmonic (hh n).1 (hh n).2 a.2).1
    (rotationWord_harmonic (hh n).1 (hh n).2 a.2).2
  have he' := congrArg (fun q => radialExtension (sphereEval q) z.2) he
  simp only [radialExtension_poly_add, radialExtension_poly_smul] at he'
  change _ = -eigenvalue (n+2) * _ at he'
  rw [eigenvalue_shift] at he'
  simp only [heatTerm, rotationWord]
  rw [← mul_add, ← mul_add]
  convert! congrArg (fun v => temporalJet a.1 n z.1 * v) he' using 1
  ring

lemma spatialHeat_casimir_series (p : ℕ → Poly) (hp : PolynomialRapid p)
    (hh : HighHarmonic p) (a : HeatJet) (t : ℝ) {x : Ambient} (hx : x ≠ 0) :
    smoothCasimir (spatialHeat p a t) x =
      ∑' n, -CKSSpectralHeat.eigenvalue n * heatTerm p a n (t,x) := by
  rw [spatialHeat_casimir p hp a t hx]
  unfold spatialHeat jointHeatSeries
  rw [← (jointHeatSeries_summable p hp _ hx).tsum_add (jointHeatSeries_summable p hp _ hx),
    ← ((jointHeatSeries_summable p hp _ hx).add (jointHeatSeries_summable p hp _ hx)).tsum_add
      (jointHeatSeries_summable p hp _ hx)]
  congr 1
  funext n
  exact heatTerm_casimir p hh a n _

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix Mat e grad hess pd proj roundLaplacian sphereGradient tensorDivergence U)
open scoped Topology ContDiff

lemma pair_symm (M : Mat) (hM : ∀ i j, M i j = M j i) (v w : E) :
    pair M v w = pair M w v := by
  unfold pair
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [hM j i]
  ring

lemma pair_normal (M : Mat) (n v : E) (hn : ∀ j : Ix, ∑ i : Ix, n i * M i j = 0) :
    pair M n v = 0 := by
  unfold pair
  rw [sum_comm]
  have he (j : Ix) : (∑ i : Ix, n i * v j * M i j) = v j * ∑ i : Ix, n i * M i j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  simp only [he,hn,mul_zero,sum_const_zero]

lemma pair_trace (M : Mat) (x : Point)
    (hn : ∀ j : Ix, ∑ i : Ix, sphereParam x i * M i j = 0) :
    pair M (thetaFrame x) (thetaFrame x) + pair M (phiUnit x) (phiUnit x) = ∑ i : Ix, M i i := by
  have he : pair M (thetaFrame x) (thetaFrame x) + pair M (phiUnit x) (phiUnit x) =
      ∑ i : Ix, ∑ j : Ix, proj (fun k => sphereParam x k) i j * M i j := by
    simp [pair,projected_frame,add_mul,sum_add_distrib]
  rw [he]
  simp only [proj,sub_mul,sum_sub_distrib,ite_mul,one_mul,zero_mul,sum_ite_eq]
  change (∑ i : Ix, M i i) - pair M (sphereParam x) (sphereParam x) = _
  rw [pair_normal M _ _ hn,sub_zero]

lemma dPair_symm {T : E → Mat} (_hT : ∀ i j, ContDiffOn ℝ ∞ (fun y => T y i j) U)
    (hS : ∀ y ∈ U, ∀ i j, T y i j = T y j i) {n : E} (hn : n ∈ U) (d v w : E) :
    dPair T n d v w = dPair T n d w v := by
  apply pair_symm
  intro i j
  have he : (fun y => T y i j) =ᶠ[𝓝 n] (fun y => T y j i) :=
    Filter.eventually_of_mem (CKSInducedSphere.U_open.mem_nhds hn) (fun y hy => hS y hy i j)
  rw [he.fderiv_eq]

lemma pair_smooth {T : E → Mat} (hT : ∀ i j, ContDiffOn ℝ ∞ (fun y => T y i j) U)
    {v w : Point → E} (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun x => pair (T (sphereParam x)) (v x) (w x)) := by
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  exact (((EuclideanSpace.proj i).contDiff.comp hv).mul
    ((EuclideanSpace.proj j).contDiff.comp hw)).mul (angular_smooth (hT i j))

lemma D_sum {J : Type*} (s : Finset J) {f : J → Point → ℝ} {x : Point}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) (v : Point) :
    D v (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, D v (f i) x := by
  simp only [D, fderiv_fun_sum hf, _root_.sum_apply]

lemma pair_derivative {T : E → Mat} (hT : ∀ i j, ContDiffOn ℝ ∞ (fun y => T y i j) U)
    {v w : Point → E} (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w) (x : Point) (k : Ix) :
    D (basis k) (fun y => pair (T (sphereParam y)) (v y) (w y)) x =
      pair (T (sphereParam x)) (fderiv ℝ v x (basis k)) (w x) +
      pair (T (sphereParam x)) (v x) (fderiv ℝ w x (basis k)) +
      dPair T (sphereParam x) (chartVector k x) (v x) (w x) := by
  have hvd (i : Ix) : DifferentiableAt ℝ (fun y => v y i) x :=
    (contDiff_euclidean.mp hv i).differentiable (by simp) x
  have hwd (i : Ix) : DifferentiableAt ℝ (fun y => w y i) x :=
    (contDiff_euclidean.mp hw i).differentiable (by simp) x
  have htd (i j : Ix) := (angular_smooth (hT i j)).differentiable (by simp) x
  have hterm (i j : Ix) : DifferentiableAt ℝ
      (fun y => v y i * w y j * T (sphereParam y) i j) x := ((hvd i).mul (hwd j)).mul (htd i j)
  change D (basis k) (fun y => ∑ i : Ix, ∑ j : Ix, v y i * w y j * T (sphereParam y) i j) x = _
  rw [D_sum univ (f := fun i y => ∑ j : Ix, v y i * w y j * T (sphereParam y) i j)
    (fun i _ => by
      convert! (DifferentiableAt.sum (u := univ) (fun j _ => hterm i j)) using 1)]
  have he (i : Ix) := D_sum univ (f := fun j y => v y i * w y j * T (sphereParam y) i j)
    (fun j _ => hterm i j) (basis k)
  simp only [he, pair, dPair]
  simp only [← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  erw [D_mul _ ((hvd i).mul (hwd j)) (htd i j), D_mul _ (hvd i) (hwd j)]
  rw [angular_first (hT i j)]
  rw [component_fderiv (hv.differentiable (by simp) x), component_fderiv (hw.differentiable (by simp) x)]
  dsimp only [Pi.mul_apply]
  ring

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter MvPolynomial
open scoped Topology ContDiff Manifold

lemma inversePolynomials_rapid (p : ℕ → Poly) (hp : PolynomialRapid p) :
    PolynomialRapid (inversePolynomials p) := by
  intro w b
  have h := CKSSpectralHeat.inverseCoeff_rapid (fun n => sphereEval (rotationWord w (p n))) (hp w) b
  simpa only [inversePolynomials, rotationWord_smul, map_smul, CKSSpectralHeat.inverseCoeff] using h

lemma inversePolynomials_harmonic (p : ℕ → Poly) (hh : HighHarmonic p) :
    HighHarmonic (inversePolynomials p) := by
  intro n
  refine ⟨(homogeneousSubmodule (Fin 3) ℝ (n+2)).smul_mem _ (hh n).1, ?_⟩
  simp only [inversePolynomials, map_smul, (hh n).2, smul_zero]

lemma heatTerm_inverse (p : ℕ → Poly) (a : HeatJet) (n : ℕ) (z : SpaceTime) :
    heatTerm (inversePolynomials p) a n z =
      (1 - CKSSpectralHeat.eigenvalue n / 2)⁻¹ * heatTerm p a n z := by
  simp only [heatTerm, inversePolynomials, rotationWord_smul, radialExtension_poly_smul]
  ring

lemma casimir_terms_summable (p : ℕ → Poly) (hp : PolynomialRapid p)
    (hh : HighHarmonic p) (a : HeatJet) {z : SpaceTime} (hz : z ∈ heatDomain) :
    Summable (fun n => -CKSSpectralHeat.eigenvalue n * heatTerm p a n z) := by
  have h := ((jointHeatSeries_summable p hp (a.1, (0,1)::(0,1)::a.2) hz).add
    (jointHeatSeries_summable p hp (a.1, (0,2)::(0,2)::a.2) hz)).add
    (jointHeatSeries_summable p hp (a.1, (1,2)::(1,2)::a.2) hz)
  exact h.congr (fun n => heatTerm_casimir p hh a n z)

theorem spatialHeat_inverse_equation (p : ℕ → Poly) (hp : PolynomialRapid p)
    (hh : HighHarmonic p) (a : HeatJet) (t : ℝ) {x : Ambient} (hx : x ≠ 0) :
    spatialHeat (inversePolynomials p) a t x +
      smoothCasimir (spatialHeat (inversePolynomials p) a t) x / 2 = spatialHeat p a t x := by
  have hip := inversePolynomials_rapid p hp
  have hih := inversePolynomials_harmonic p hh
  rw [spatialHeat_casimir_series _ hip hih a t hx, ← tsum_div_const]
  unfold spatialHeat jointHeatSeries
  rw [← (jointHeatSeries_summable _ hip a hx).tsum_add
    ((casimir_terms_summable _ hip hih a hx).div_const 2)]
  congr 1
  funext n
  rw [heatTerm_inverse]
  have hd : 1 - CKSSpectralHeat.eigenvalue n / 2 ≠ 0 := by
    have he := CKSSpectralHeat.eigenvalue_ge_six n
    linarith
  calc
    _ = ((1 - CKSSpectralHeat.eigenvalue n / 2)⁻¹ *
      (1 - CKSSpectralHeat.eigenvalue n / 2)) * heatTerm p a n (t,x) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hd, one_mul]

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix Mat e grad hess pd proj roundLaplacian sphereGradient tensorDivergence U)
open scoped Topology ContDiff

lemma projected_test (x : Point) (z : E)
    (hz : ∑ i : Ix, sphereParam x i * z i = 0) (l : Ix) :
    (∑ j : Ix, z j * proj (fun i => sphereParam x i) j l) = z l := by
  simp only [proj,mul_sub,sum_sub_distrib,mul_ite,mul_one,mul_zero,sum_ite_eq']
  have he : (∑ j : Ix, z j * (sphereParam x j * sphereParam x l)) =
      (∑ j : Ix, sphereParam x j * z j) * sphereParam x l := by
    rw [sum_mul]
    apply sum_congr rfl
    intro j hj
    ring
  rw [he,hz,zero_mul,sub_zero]
  simp

lemma dPair_expansion (T : E → Mat) (n d v w : E) :
    dPair T n d v w = ∑ k : Ix, ∑ i : Ix, ∑ j : Ix,
      d k * v i * w j * pd k (fun y => T y i j) n := by
  simp only [dPair,pair,CKSInducedSphere.fderiv_expand,grad,mul_sum]
  rw [CKSInducedSphere.sum3_rotate,CKSInducedSphere.sum3_rotate]
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

lemma divergence_test (T : E → Mat) (x : Point) (z : E)
    (hz : ∑ i : Ix, sphereParam x i * z i = 0) :
    (∑ j : Ix, z j * tensorDivergence T (sphereParam x) j) =
      ∑ k : Ix, ∑ i : Ix, ∑ l : Ix,
        proj (fun a => sphereParam x a) k i * z l * pd k (fun y => T y i l) (sphereParam x) := by
  simp only [tensorDivergence,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro l hl
  calc
    _ = proj (fun a => sphereParam x a) k i *
      (∑ j : Ix, z j * proj (fun a => sphereParam x a) j l) *
      pd k (fun y => T y i l) (sphereParam x) := by
        simp only [mul_sum,sum_mul]
        apply sum_congr rfl
        intro j hj
        ring
    _ = _ := by rw [projected_test x z hz l]

lemma divergence_frame (T : E → Mat) (x : Point) (z : E)
    (hz : ∑ i : Ix, sphereParam x i * z i = 0) :
    (∑ j : Ix, z j * tensorDivergence T (sphereParam x) j) =
      dPair T (sphereParam x) (thetaFrame x) (thetaFrame x) z +
      dPair T (sphereParam x) (phiUnit x) (phiUnit x) z := by
  rw [divergence_test T x z hz,dPair_expansion,dPair_expansion]
  simp only [projected_frame,add_mul,sum_add_distrib]

lemma gradient_test (F : E → ℝ) (x : Point) (z : E)
    (hz : ∑ i : Ix, sphereParam x i * z i = 0) :
    (∑ j : Ix, z j * sphereGradient F (sphereParam x) j) = fderiv ℝ F (sphereParam x) z := by
  rw [CKSInducedSphere.fderiv_expand]
  simp only [sphereGradient,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  calc
    _ = (∑ j : Ix, z j * proj (fun a => sphereParam x a) j i) * grad F (sphereParam x) i := by
      simp only [sum_mul]
      apply sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [projected_test x z hz i]

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix Mat e grad hess pd proj roundLaplacian sphereGradient tensorDivergence U)
open scoped Topology ContDiff

def tensorC (T : E → Mat) (x : Point) := pair (T (sphereParam x)) (phiUnit x) (phiUnit x)

lemma tensorA_smooth {T : E → Mat} (hT : ∀ i j, ContDiffOn ℝ ∞ (fun y => T y i j) U) :
    ContDiff ℝ ∞ (tensorA T) := pair_smooth hT thetaFrame_smooth thetaFrame_smooth
lemma tensorB_smooth {T : E → Mat} (hT : ∀ i j, ContDiffOn ℝ ∞ (fun y => T y i j) U) :
    ContDiff ℝ ∞ (tensorB T) := pair_smooth hT thetaFrame_smooth phiUnit_smooth

lemma tensorPhi_smooth {T : E → Mat} (hT : ∀ i j, ContDiffOn ℝ ∞ (fun y => T y i j) U) :
    ContDiff ℝ ∞ (tensorPhi T) := ((coord 1).contDiff.sin).mul (tensorB_smooth hT)

lemma frame_derivatives {T : E → Mat} (hT : ∀ i j, ContDiffOn ℝ ∞ (fun y => T y i j) U)
    (hS : ∀ y ∈ U, ∀ i j, T y i j = T y j i)
    (hN : ∀ y : E, ‖y‖ = 1 → ∀ j : Ix, ∑ i : Ix, y i * T y i j = 0) (x : Point) :
    D (basis 1) (tensorA T) x = dPair T (sphereParam x) (thetaFrame x) (thetaFrame x) (thetaFrame x) ∧
    D (basis 2) (tensorA T) x = Real.sin (x 1) * dPair T (sphereParam x) (phiUnit x) (thetaFrame x) (thetaFrame x) +
      2 * Real.cos (x 1) * tensorB T x ∧
    D (basis 1) (tensorB T) x = dPair T (sphereParam x) (thetaFrame x) (thetaFrame x) (phiUnit x) ∧
    D (basis 2) (tensorB T) x = Real.sin (x 1) * dPair T (sphereParam x) (phiUnit x) (thetaFrame x) (phiUnit x) +
      Real.cos (x 1) * (tensorC T x - tensorA T x) ∧
    D (basis 2) (tensorC T) x = Real.sin (x 1) * dPair T (sphereParam x) (phiUnit x) (phiUnit x) (phiUnit x) -
      2 * Real.cos (x 1) * tensorB T x := by
  have hn (v : E) : pair (T (sphereParam x)) (sphereParam x) v = 0 :=
    pair_normal _ _ _ (hN _ (sphereParam_norm x))
  have hs (v w : E) := pair_symm (T (sphereParam x)) (hS _ (sphereParam_mem x)) v w
  have hr (v : E) : pair (T (sphereParam x)) v (sphereParam x) = 0 := by rw [hs,hn]
  refine ⟨?_,?_,?_,?_,?_⟩
  · unfold tensorA
    rw [pair_derivative hT thetaFrame_smooth thetaFrame_smooth,theta_theta]
    simp only [pair_neg_left,pair_neg_right,hn,hr,neg_zero,zero_add,chartVector,Matrix.cons_val_one,Matrix.cons_val_zero]
  · unfold tensorA
    rw [pair_derivative hT thetaFrame_smooth thetaFrame_smooth,theta_phi]
    change pair (T (sphereParam x)) (Real.cos (x 1) • phiUnit x) (thetaFrame x) +
      pair (T (sphereParam x)) (thetaFrame x) (Real.cos (x 1) • phiUnit x) +
      dPair T (sphereParam x) (Real.sin (x 1) • phiUnit x) (thetaFrame x) (thetaFrame x) = _
    rw [pair_smul_left,pair_smul_right,dPair_smul_dir,hs (phiUnit x) (thetaFrame x)]
    unfold tensorB
    ring
  · unfold tensorB
    rw [pair_derivative hT thetaFrame_smooth phiUnit_smooth,theta_theta,unit_theta]
    simp only [pair_neg_left,hn,neg_zero,pair_zero_right,zero_add,chartVector,Matrix.cons_val_one,Matrix.cons_val_zero]
  · unfold tensorB
    rw [pair_derivative hT thetaFrame_smooth phiUnit_smooth,theta_phi,unit_phi,equator_decomposition]
    change pair (T (sphereParam x)) (Real.cos (x 1) • phiUnit x) (phiUnit x) +
      pair (T (sphereParam x)) (thetaFrame x) (-(Real.sin (x 1) • sphereParam x + Real.cos (x 1) • thetaFrame x)) +
      dPair T (sphereParam x) (Real.sin (x 1) • phiUnit x) (thetaFrame x) (phiUnit x) = _
    simp only [pair_smul_left,pair_neg_right,pair_add_right,pair_smul_right,dPair_smul_dir,hr,mul_zero,zero_add]
    unfold tensorA tensorC
    ring
  · unfold tensorC
    rw [pair_derivative hT phiUnit_smooth phiUnit_smooth,unit_phi,equator_decomposition]
    change pair (T (sphereParam x)) (-(Real.sin (x 1) • sphereParam x + Real.cos (x 1) • thetaFrame x)) (phiUnit x) +
      pair (T (sphereParam x)) (phiUnit x) (-(Real.sin (x 1) • sphereParam x + Real.cos (x 1) • thetaFrame x)) +
      dPair T (sphereParam x) (Real.sin (x 1) • phiUnit x) (phiUnit x) (phiUnit x) = _
    simp only [pair_neg_left,pair_add_left,pair_smul_left,pair_neg_right,pair_add_right,
      pair_smul_right,dPair_smul_dir,hr,hn,mul_zero,zero_add]
    rw [hs (phiUnit x) (thetaFrame x)]
    unfold tensorB
    ring

lemma tensor_trace_free {T : E → Mat}
    (hN : ∀ y : E, ‖y‖ = 1 → ∀ j : Ix, ∑ i : Ix, y i * T y i j = 0)
    (hTr : ∀ y : E, ‖y‖ = 1 → ∑ i : Ix, T y i i = 0) : tensorC T = fun x => -tensorA T x := by
  funext x
  have h := pair_trace (T (sphereParam x)) x (hN _ (sphereParam_norm x))
  rw [hTr _ (sphereParam_norm x)] at h
  change tensorA T x + tensorC T x = 0 at h
  linarith

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff
open CKSSphericalHarmonics

lemma sphereGradient_rotations (F : E → ℝ) {x : E} (hx : ‖x‖ = 1) (j : Ix) :
    sphereGradient F x j = ∑ i : Ix, x i * smoothRotation i j F x := by
  simp only [sphereGradient, proj, grad, smoothRotation_pd, sub_mul, ite_mul,
    one_mul, zero_mul, sum_sub_distrib, sum_ite_eq, Finset.mem_univ, ite_true]
  rw [show (∑ i, x i * (x i * pd j F x - x j * pd i F x)) =
    (∑ i, x i ^ 2) * pd j F x - ∑ i, x j * x i * pd i F x by
      rw [sum_mul, ← sum_sub_distrib]
      apply sum_congr rfl
      intro i hi
      ring, unit_sum_sq hx, one_mul]

lemma smoothRotation_congr_sphere {F G : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U)
    (h : ∀ x : E, ‖x‖ = 1 → F x = G x) {x : E} (hx : ‖x‖ = 1) (i j : Ix) :
    smoothRotation i j F x = smoothRotation i j G x := by
  by_cases hij : i = j
  · subst j
    simp [smoothRotation_pd]
  let s : Sphere := ⟨x, by simpa [Metric.mem_sphere, dist_zero_right] using hx⟩
  have he : (fun t => F (planeRotation i j hij t x)) =
      fun t => G (planeRotation i j hij t x) := by
    funext t
    apply h
    rw [(planeRotation i j hij t).norm_map, hx]
  have hFd := smoothRotation_orbit_derivative hF i j hij s 0
  have hGd := smoothRotation_orbit_derivative hG i j hij s 0
  change HasDerivAt (fun t => F (planeRotation i j hij t x)) _ 0 at hFd
  rw [he] at hFd
  simpa only [s, planeRotation_zero] using hFd.unique hGd

lemma sphereGradient_congr_sphere {F G : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U)
    (h : ∀ x : E, ‖x‖ = 1 → F x = G x) {x : E} (hx : ‖x‖ = 1) (j : Ix) :
    sphereGradient F x j = sphereGradient G x j := by
  rw [sphereGradient_rotations F hx, sphereGradient_rotations G hx]
  apply sum_congr rfl
  intro i hi
  rw [smoothRotation_congr_sphere hF hG h hx i j]

lemma heatTensor_tangent (p : ℕ → Poly) (t : ℝ) {x : E} (hx : ‖x‖ = 1) (j : Ix) :
    ∑ i : Ix, x i * heatTensor p t x i j = 0 :=
  hessTF_normal_left (unit_sum_sq hx) _ j

lemma heatTensor_trace_zero (p : ℕ → Poly) (t : ℝ) {x : E} (hx : ‖x‖ = 1) :
    ∑ i : Ix, heatTensor p t x i i = 0 :=
  hessTF_trace_zero (unit_sum_sq hx) _

theorem heatTensor_divergence (p : ℕ → Poly) (hp : PolynomialRapid p)
    (hh : HighHarmonic p) (t : ℝ) {x : E} (hx : ‖x‖ = 1) (j : Ix) :
    tensorDivergence (heatTensor p t) x j =
      sphereGradient (spatialHeat p (0,[]) t) x j := by
  have hi := spatialHeat_smooth _ (inversePolynomials_rapid p hp) (0,[]) t
  change tensorDivergence (traceFreeHess (spatialHeat (inversePolynomials p) (0,[]) t)) x j = _
  rw [divergence_traceFreeHess hi hx]
  apply sphereGradient_congr_sphere (hi.add ((roundLaplacian_smooth hi).div_const 2))
    (spatialHeat_smooth p hp _ t) _ hx j
  intro y hy
  rw [roundLaplacian_eq_Casimir hi hy]
  exact spatialHeat_inverse_equation p hp hh _ t (by intro h; simp [h] at hy)

end
end CKSInducedSphere

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix Mat e grad hess pd proj roundLaplacian sphereGradient tensorDivergence U)
open scoped Topology ContDiff

lemma tensorPhi_derivatives {T : E → Mat}
    (hT : ∀ i j, ContDiffOn ℝ ∞ (fun y => T y i j) U) (x : Point) :
    D (basis 1) (tensorPhi T) x = Real.cos (x 1) * tensorB T x + Real.sin (x 1) * D (basis 1) (tensorB T) x ∧
    D (basis 2) (tensorPhi T) x = Real.sin (x 1) * D (basis 2) (tensorB T) x := by
  have hd : DifferentiableAt ℝ (fun y : Point => y 1) x := (coord 1).differentiableAt
  have hB := (tensorB_smooth hT).differentiable (by simp) x
  have hc (k : Ix) : D (basis k) (fun y : Point => Real.sin (y 1)) x =
      Real.cos (x 1) * (if (1 : Ix) = k then 1 else 0) := by
    rw [D_sin _ hd]
    change Real.cos (x 1) * D (basis k) (coord 1) x = _
    rw [D_coord]
  constructor
  · unfold tensorPhi
    rw [D_mul _ hd.sin hB,hc]
    norm_num
    ring
  · unfold tensorPhi
    rw [D_mul _ hd.sin hB,hc,ite_eq_right (show (1 : Ix) ≠ 2 by decide)]
    ring

theorem tensor_chart_divergence {T : E → Mat}
    (hT : ∀ i j, ContDiffOn ℝ ∞ (fun y => T y i j) U)
    (hS : ∀ y ∈ U, ∀ i j, T y i j = T y j i)
    (hN : ∀ y : E, ‖y‖ = 1 → ∀ j : Ix, ∑ i : Ix, y i * T y i j = 0)
    (hTr : ∀ y : E, ‖y‖ = 1 → ∑ i : Ix, T y i i = 0)
    (x : Point) (hs : Real.sin (x 1) ≠ 0) :
    (D (basis 1) (tensorA T) x + D (basis 2) (tensorPhi T) x / Real.sin (x 1)^2 +
      2 * Real.cos (x 1) * tensorA T x / Real.sin (x 1) =
      ∑ j : Ix, thetaFrame x j * tensorDivergence T (sphereParam x) j) ∧
    (D (basis 1) (tensorPhi T) x - D (basis 2) (tensorA T) x +
      Real.cos (x 1) * tensorPhi T x / Real.sin (x 1) =
      Real.sin (x 1) * ∑ j : Ix, phiUnit x j * tensorDivergence T (sphereParam x) j) := by
  obtain ⟨hAθ,hAφ,hBθ,hBφ,hCφ⟩ := frame_derivatives hT hS hN x
  obtain ⟨hPθ,hPφ⟩ := tensorPhi_derivatives hT x
  have hC : tensorC T x = -tensorA T x := congrFun (tensor_trace_free hN hTr) x
  have hCd : D (basis 2) (tensorC T) x = -D (basis 2) (tensorA T) x := by
    rw [tensor_trace_free hN hTr,D_neg]
  rw [hCφ,hAφ] at hCd
  have hTraceD : dPair T (sphereParam x) (phiUnit x) (phiUnit x) (phiUnit x) =
      -dPair T (sphereParam x) (phiUnit x) (thetaFrame x) (thetaFrame x) := by
    apply mul_left_cancel₀ hs
    linear_combination hCd
  constructor
  · rw [hAθ,hPφ,hBφ,hC,divergence_frame T x _ (theta_tangent x),
      dPair_symm hT hS (sphereParam_mem x) (phiUnit x) (phiUnit x) (thetaFrame x)]
    field_simp
    ring
  · rw [hPθ,hBθ,hAφ,divergence_frame T x _ (unit_tangent x),hTraceD]
    unfold tensorPhi
    field_simp
    ring

theorem tensor_chart_gradient {F : E → ℝ} {T : E → Mat}
    (hF : ContDiffOn ℝ ∞ F U)
    (hT : ∀ i j, ContDiffOn ℝ ∞ (fun y => T y i j) U)
    (hS : ∀ y ∈ U, ∀ i j, T y i j = T y j i)
    (hN : ∀ y : E, ‖y‖ = 1 → ∀ j : Ix, ∑ i : Ix, y i * T y i j = 0)
    (hTr : ∀ y : E, ‖y‖ = 1 → ∑ i : Ix, T y i i = 0)
    (hDiv : ∀ y : E, ‖y‖ = 1 → ∀ j : Ix, tensorDivergence T y j = sphereGradient F y j)
    (x : Point) (hs : Real.sin (x 1) ≠ 0) :
    (D (basis 1) (tensorA T) x + D (basis 2) (tensorPhi T) x / Real.sin (x 1)^2 +
      2 * Real.cos (x 1) * tensorA T x / Real.sin (x 1) = D (basis 1) (fun y => F (sphereParam y)) x) ∧
    (D (basis 1) (tensorPhi T) x - D (basis 2) (tensorA T) x +
      Real.cos (x 1) * tensorPhi T x / Real.sin (x 1) = D (basis 2) (fun y => F (sphereParam y)) x) := by
  obtain ⟨hθ,hφ⟩ := tensor_chart_divergence hT hS hN hTr x hs
  simp only [hDiv _ (sphereParam_norm x)] at hθ hφ
  rw [gradient_test F x _ (theta_tangent x)] at hθ
  rw [gradient_test F x _ (unit_tangent x)] at hφ
  constructor
  · rw [angular_first hF]
    exact hθ
  · rw [angular_first hF]
    change _ = fderiv ℝ F (sphereParam x) (Real.sin (x 1) • phiUnit x)
    rw [map_smul,smul_eq_mul]
    exact hφ

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff Manifold
open CKSSphericalHarmonics

lemma HeatGenerated.neg {p : ℕ → Poly} {F : ℝ → E → ℝ} (hF : HeatGenerated p F) :
    HeatGenerated p (fun t x => -F t x) := by
  simpa only [neg_one_mul] using HeatGenerated.coeff (fun _ => (-1:ℝ)) contDiffOn_const hF

lemma HeatGenerated.sub {p : ℕ → Poly} {F G : ℝ → E → ℝ}
    (hF : HeatGenerated p F) (hG : HeatGenerated p G) :
    HeatGenerated p (fun t x => F t x - G t x) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

lemma heatTensor_generated (p : ℕ → Poly) (hp : PolynomialRapid p) (i j : Ix) :
    HeatGenerated (inversePolynomials p) (fun t x => heatTensor p t x i j) := by
  have hi := inversePolynomials_rapid p hp
  have hH (a b : Ix) : HeatGenerated (inversePolynomials p)
      (fun t x => hess (spatialHeat (inversePolynomials p) (0,[]) t) x a b) :=
    ((HeatGenerated.basic (0,[]) (p := inversePolynomials p)).partial hi b).partial hi a
  change HeatGenerated _ (fun t x =>
    (∑ a, ∑ b, proj (fun c => x c) i a * hess (spatialHeat (inversePolynomials p) (0,[]) t) x a b * proj (fun c => x c) b j) -
    (∑ a, ∑ b, proj (fun c => x c) a b * hess (spatialHeat (inversePolynomials p) (0,[]) t) x a b) / 2 * proj (fun c => x c) i j)
  apply HeatGenerated.sub
  · apply HeatGenerated.congr (HeatGenerated.sum univ (fun a _ => HeatGenerated.sum univ (fun b _ =>
      HeatGenerated.coeff _ ((proj_smooth i a).mul (proj_smooth b j)) (hH a b))))
    intro t x hx
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    ring
  · apply HeatGenerated.congr (HeatGenerated.coeff
      (fun x => proj (fun c => x c) i j / 2) ((proj_smooth i j).div_const 2)
      (HeatGenerated.sum univ (fun a _ => HeatGenerated.sum univ (fun b _ =>
        HeatGenerated.coeff _ (proj_smooth a b) (hH a b)))))
    intro t x hx
    ring

end
end CKSInducedSphere

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics
open CKSInducedSphere (E Ix Mat U)
open scoped Topology ContDiff

lemma positiveChart_open : IsOpen positiveChart := isOpen_lt continuous_const (coord 0).continuous

lemma joint_slice {F : ℝ → E → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain) (t : ℝ) :
    ContDiffOn ℝ ∞ (F t) U := by
  exact hF.comp (contDiffOn_const.prodMk contDiffOn_id) (fun x hx => hx)

lemma radius_comp_smooth {q : ℝ → ℝ} (hq : ContDiffOn ℝ ∞ q (Ioi 0)) :
    ContDiffOn ℝ ∞ (fun x : Point => q (x 0)) positiveChart :=
  hq.comp (coord 0).contDiff.contDiffOn (fun _ hx => hx)

lemma joint_chart_smooth {F : ℝ → E → ℝ} {t : ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) :
    ContDiffOn ℝ ∞ (fun x : Point => F (t (x 0)) (sphereParam x)) positiveChart :=
  hF.comp ((radius_comp_smooth ht).prodMk sphereParam_smooth.contDiffOn)
    (fun x _ => sphereParam_mem x)

lemma chartMass_smooth {F : ℝ → E → ℝ} {t c : ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) (hc : ContDiffOn ℝ ∞ c (Ioi 0)) :
    ContDiffOn ℝ ∞ (chartMass F t c) positiveChart :=
  (radius_comp_smooth hc).add (joint_chart_smooth hF ht)

lemma chartTensorA_smooth {T : ℝ → E → Mat} {t : ℝ → ℝ}
    (hT : ∀ i j, ContDiffOn ℝ ∞ (fun z : ℝ × E => T z.1 z.2 i j) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) :
    ContDiffOn ℝ ∞ (chartTensorA T t) positiveChart := by
  unfold chartTensorA tensorA pair
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.sum
  intro j hj
  exact (((contDiff_euclidean.mp thetaFrame_smooth i).mul
    (contDiff_euclidean.mp thetaFrame_smooth j)).contDiffOn).mul
      (joint_chart_smooth (F := fun s y => T s y i j) (hT i j) ht)

lemma chartTensorPhi_smooth {T : ℝ → E → Mat} {t : ℝ → ℝ}
    (hT : ∀ i j, ContDiffOn ℝ ∞ (fun z : ℝ × E => T z.1 z.2 i j) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) :
    ContDiffOn ℝ ∞ (chartTensorPhi T t) positiveChart := by
  unfold chartTensorPhi tensorPhi tensorB pair
  apply ((coord 1).contDiff.sin.contDiffOn).mul
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.sum
  intro j hj
  exact (((contDiff_euclidean.mp thetaFrame_smooth i).mul
    (contDiff_euclidean.mp phiUnit_smooth j)).contDiffOn).mul
      (joint_chart_smooth (F := fun s y => T s y i j) (hT i j) ht)

lemma chartMass_first {F : ℝ → E → ℝ} {t c : ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) (hc : ContDiffOn ℝ ∞ c (Ioi 0))
    {x : Point} (hx : x ∈ positiveChart) (i : Ix) (hi : i ≠ 0) :
    D (basis i) (chartMass F t c) x =
      D (basis i) (fun y => F (t (x 0)) (sphereParam y)) x := by
  have hfull := (chartMass_smooth hF ht hc).contDiffAt (positiveChart_open.mem_nhds hx)
  have hfixed := (joint_slice hF (t (x 0))).comp_contDiff sphereParam_smooth sphereParam_mem
  have he := angular_first_congr_leaf (hfull.differentiableAt (by simp))
    ((contDiff_const.add hfixed).differentiable (by simp) x)
    (G := fun y => c (x 0) + F (t (x 0)) (sphereParam y))
    (by intro y hy; simp only [chartMass,hy]) i hi
  simpa only [D, fderiv_const_add] using he

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere
open scoped Topology ContDiff

lemma chartTensorA_first {T : ℝ → E → Mat} {t : ℝ → ℝ}
    (hT : ∀ i j, ContDiffOn ℝ ∞ (fun z : ℝ × E => T z.1 z.2 i j) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) {x : Point} (hx : x ∈ positiveChart)
    (i : Ix) (hi : i ≠ 0) : D (basis i) (chartTensorA T t) x =
      D (basis i) (tensorA (T (t (x 0)))) x := by
  apply angular_first_congr_leaf
    (((chartTensorA_smooth hT ht).contDiffAt (positiveChart_open.mem_nhds hx)).differentiableAt (by simp))
    ((tensorA_smooth (fun a b => joint_slice (F := fun s y => T s y a b) (hT a b) _)).differentiable (by simp) x) _ i hi
  intro y hy
  simp only [chartTensorA,hy]

lemma chartTensorPhi_first {T : ℝ → E → Mat} {t : ℝ → ℝ}
    (hT : ∀ i j, ContDiffOn ℝ ∞ (fun z : ℝ × E => T z.1 z.2 i j) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) {x : Point} (hx : x ∈ positiveChart)
    (i : Ix) (hi : i ≠ 0) : D (basis i) (chartTensorPhi T t) x =
      D (basis i) (tensorPhi (T (t (x 0)))) x := by
  apply angular_first_congr_leaf
    (((chartTensorPhi_smooth hT ht).contDiffAt (positiveChart_open.mem_nhds hx)).differentiableAt (by simp))
    ((tensorPhi_smooth (fun a b => joint_slice (F := fun s y => T s y a b) (hT a b) _)).differentiable (by simp) x) _ i hi
  intro y hy
  simp only [chartTensorPhi,hy]

lemma varying_chart_divergence {F : ℝ → E → ℝ} {T : ℝ → E → Mat} {t c : ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (hT : ∀ i j, ContDiffOn ℝ ∞ (fun z : ℝ × E => T z.1 z.2 i j) heatDomain)
    (hS : ∀ s, ∀ y ∈ U, ∀ i j, T s y i j = T s y j i)
    (hN : ∀ s, ∀ y : E, ‖y‖ = 1 → ∀ j : Ix, ∑ i, y i * T s y i j = 0)
    (hTr : ∀ s, ∀ y : E, ‖y‖ = 1 → ∑ i : Ix, T s y i i = 0)
    (hDiv : ∀ s, ∀ y : E, ‖y‖ = 1 → ∀ j : Ix, tensorDivergence (T s) y j = sphereGradient (F s) y j)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) (hc : ContDiffOn ℝ ∞ c (Ioi 0))
    {x : Point} (hx : x ∈ positiveChart) (hs : Real.sin (x 1) ≠ 0) :
    (D (basis 1) (chartTensorA T t) x + D (basis 2) (chartTensorPhi T t) x / Real.sin (x 1)^2 +
      2*Real.cos (x 1)*chartTensorA T t x / Real.sin (x 1) = D (basis 1) (chartMass F t c) x) ∧
    (D (basis 1) (chartTensorPhi T t) x - D (basis 2) (chartTensorA T t) x +
      Real.cos (x 1)*chartTensorPhi T t x / Real.sin (x 1) = D (basis 2) (chartMass F t c) x) := by
  rw [chartTensorA_first hT ht hx 1 (by decide),chartTensorA_first hT ht hx 2 (by decide),
    chartTensorPhi_first hT ht hx 1 (by decide),chartTensorPhi_first hT ht hx 2 (by decide),
    chartMass_first hF ht hc hx 1 (by decide),chartMass_first hF ht hc hx 2 (by decide)]
  exact tensor_chart_gradient (joint_slice hF _) (fun i j => joint_slice (F := fun s y => T s y i j) (hT i j) _)
    (hS _) (hN _) (hTr _) (hDiv _) x hs

lemma heatTensor_symmetric_U (p : ℕ → Poly) (hp : PolynomialRapid p)
    (t : ℝ) (x : E) (hx : x ∈ U) (i j : Ix) : heatTensor p t x i j = heatTensor p t x j i :=
  hessTF_symm _ _ (fun a b => partial_comm
    (spatialHeat_smooth _ (inversePolynomials_rapid p hp) _ t) hx a b) i j

lemma canonicalF_joint (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E => canonicalF f₀ m z.1 z.2) heatDomain :=
  contDiffOn_const.add (jointHeatSeries_smooth _ (smoothDatum_rapid f₀ hf₀) (0,[]))
lemma canonicalT_joint (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (i j : Ix) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E => canonicalT f₀ z.1 z.2 i j) heatDomain :=
  (heatTensor_generated _ (smoothDatum_rapid f₀ hf₀) i j).joint_smooth
    (inversePolynomials_rapid _ (smoothDatum_rapid f₀ hf₀))

theorem canonical_chart_divergence (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {t c : ℝ → ℝ} (ht : ContDiffOn ℝ ∞ t (Ioi 0)) (hc : ContDiffOn ℝ ∞ c (Ioi 0))
    {x : Point} (hx : x ∈ positiveChart) (hs : Real.sin (x 1) ≠ 0) :
    (D (basis 1) (chartTensorA (canonicalT f₀) t) x + D (basis 2) (chartTensorPhi (canonicalT f₀) t) x / Real.sin (x 1)^2 +
      2*Real.cos (x 1)*chartTensorA (canonicalT f₀) t x / Real.sin (x 1) = D (basis 1) (chartMass (canonicalF f₀ m) t c) x) ∧
    (D (basis 1) (chartTensorPhi (canonicalT f₀) t) x - D (basis 2) (chartTensorA (canonicalT f₀) t) x +
      Real.cos (x 1)*chartTensorPhi (canonicalT f₀) t x / Real.sin (x 1) = D (basis 2) (chartMass (canonicalF f₀ m) t c) x) := by
  have hp := smoothDatum_rapid f₀ hf₀
  apply varying_chart_divergence (canonicalF_joint f₀ hf₀ m) (canonicalT_joint f₀ hf₀)
    (heatTensor_symmetric_U _ hp) (fun s y hy j => heatTensor_tangent _ s hy j)
    (fun s y hy => heatTensor_trace_zero _ s hy) _ ht hc hx hs
  intro s y hy j
  unfold canonicalF canonicalT
  rw [sphereGradient_const_add]
  exact heatTensor_divergence _ hp (heatPolynomials_harmonic f₀) s hy j

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology ContDiff

lemma outer_divergence (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0 < R) {x : Point} (hr : 0 < x 0) (hs : Real.sin (x 1) ≠ 0) :
    (D (basis 1) (outerA f₀ R) x + D (basis 2) (outerPhi f₀ R) x / Real.sin (x 1)^2 +
      2*Real.cos (x 1)*outerA f₀ R x / Real.sin (x 1) = D (basis 1) (outerMass f₀ m R) x) ∧
    (D (basis 1) (outerPhi f₀ R) x - D (basis 2) (outerA f₀ R) x +
      Real.cos (x 1)*outerPhi f₀ R x / Real.sin (x 1) = D (basis 2) (outerMass f₀ m R) x) :=
  canonical_chart_divergence f₀ hf₀ m (heatTime_smooth hR) (paddingMass_smooth hR) hr hs

end
end CKSSphericalChart

end

end OAI
end

theorem solution : type_of% @OAI.CKSSphericalChart.outer_divergence := @OAI.CKSSphericalChart.outer_divergence
