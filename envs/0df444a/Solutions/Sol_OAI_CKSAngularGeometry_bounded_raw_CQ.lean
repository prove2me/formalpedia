-- Prove2me | solution 1 for OAI.CKSAngularGeometry.bounded_raw_CQ
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:18:36.535205+00:00
-- url     : https://prove2.me/submissions/9b93e127-d0ab-46ed-8b21-6afd34466488

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport

set_option linter.all false

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev CombinedJet := Jet × ScalarJet

def operators (j : CombinedJet) : ℝ × ℝ :=
  (scalarCurvature j.1, lapseLaplacian j.1 j.2)

def regular : Set CombinedJet := {j | determinant j.1.1 ≠ 0 ∧ j.2.1 ≠ 0}

lemma inverse_component_smooth {j : CombinedJet} (hj : j ∈ regular) (i k : I) :
    ContDiffAt ℝ ∞ (fun y : CombinedJet => inverse y.1.1 i k) j := by
  unfold inverse
  apply ContDiffAt.div
  · fin_cases i <;> fin_cases k <;> dsimp <;> fun_prop
  · exact determinant_smooth.contDiffAt.comp j (by fun_prop)
  · exact hj.1

lemma christoffel_smooth {j : CombinedJet} (hj : j ∈ regular) (a i k : I) :
    ContDiffAt ℝ ∞ (fun y : CombinedJet => christoffel y.1 a i k) j := by
  unfold christoffel
  apply ContDiffAt.div_const
  apply ContDiffAt.sum
  intro l hl
  exact (inverse_component_smooth hj a l).mul (by fun_prop)

lemma inverseDerivative_smooth {j : CombinedJet} (hj : j ∈ regular) (s a b : I) :
    ContDiffAt ℝ ∞ (fun y : CombinedJet => inverseDerivative y.1 s a b) j := by
  unfold inverseDerivative
  apply ContDiffAt.neg
  apply ContDiffAt.sum
  intro i hi
  apply ContDiffAt.sum
  intro k hk
  exact ((inverse_component_smooth hj a i).mul (by fun_prop)).mul
    (inverse_component_smooth hj k b)

lemma christoffelDerivative_smooth {j : CombinedJet} (hj : j ∈ regular) (s a i k : I) :
    ContDiffAt ℝ ∞ (fun y : CombinedJet => christoffelDerivative y.1 s a i k) j := by
  unfold christoffelDerivative
  apply ContDiffAt.div_const
  apply ContDiffAt.sum
  intro l hl
  exact ((inverseDerivative_smooth hj s a l).mul (by fun_prop)).add
    ((inverse_component_smooth hj a l).mul (by fun_prop))

lemma ricci_smooth {j : CombinedJet} (hj : j ∈ regular) (i k : I) :
    ContDiffAt ℝ ∞ (fun y : CombinedJet => ricci y.1 i k) j := by
  unfold ricci
  apply ContDiffAt.add
  · apply ContDiffAt.sum
    intro a ha
    exact (christoffelDerivative_smooth hj a a i k).sub
      (christoffelDerivative_smooth hj k a i a)
  · apply ContDiffAt.sum
    intro a ha
    apply ContDiffAt.sum
    intro b hb
    exact ((christoffel_smooth hj a a b).mul (christoffel_smooth hj b i k)).sub
      ((christoffel_smooth hj a k b).mul (christoffel_smooth hj b i a))

lemma operators_smooth {j : CombinedJet} (hj : j ∈ regular) :
    ContDiffAt ℝ ∞ operators j := by
  apply ContDiffAt.prodMk
  · unfold scalarCurvature
    apply ContDiffAt.sum
    intro i hi
    apply ContDiffAt.sum
    intro k hk
    exact (inverse_component_smooth hj i k).mul (ricci_smooth hj i k)
  · unfold lapseLaplacian
    apply ContDiffAt.sum
    intro i hi
    apply ContDiffAt.sum
    intro k hk
    apply (inverse_component_smooth hj i k).mul
    apply ContDiffAt.add
    · apply ContDiffAt.sub
      · apply ContDiffAt.div (g := fun y : CombinedJet => y.2.1^2)
        · fun_prop
        · fun_prop
        · exact pow_ne_zero 2 hj.2
      · apply ContDiffAt.div (g := fun y : CombinedJet => y.2.1)
        · fun_prop
        · fun_prop
        · exact hj.2
    · apply ContDiffAt.div (g := fun y : CombinedJet => y.2.1)
      · apply ContDiffAt.sum
        intro a ha
        exact (christoffel_smooth hj a i k).mul (by fun_prop)
      · fun_prop
      · exact hj.2

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma christoffel_rescale (c : ℝ) (j : Jet) (hc : c ≠ 0) (a i k : I) :
    christoffel (rescale c j) a i k = christoffel j a i k := by
  unfold christoffel
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [inverse_rescale c j hc]
  dsimp [rescale]
  field_simp

lemma inverseDerivative_rescale (c : ℝ) (j : Jet) (hc : c ≠ 0) (s a b : I) :
    inverseDerivative (rescale c j) s a b = inverseDerivative j s a b / c := by
  unfold inverseDerivative
  simp only [Finset.sum_div,neg_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  rw [inverse_rescale c j hc,inverse_rescale c j hc]
  dsimp [rescale]
  field_simp

lemma christoffelDerivative_rescale (c : ℝ) (j : Jet) (hc : c ≠ 0) (s a i k : I) :
    christoffelDerivative (rescale c j) s a i k = christoffelDerivative j s a i k := by
  unfold christoffelDerivative
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [inverseDerivative_rescale c j hc,inverse_rescale c j hc]
  dsimp [rescale]
  field_simp

lemma ricci_rescale (c : ℝ) (j : Jet) (hc : c ≠ 0) (i k : I) :
    ricci (rescale c j) i k = ricci j i k := by
  simp only [ricci,christoffelDerivative_rescale c j hc,christoffel_rescale c j hc]

lemma scalar_rescale (c : ℝ) (j : Jet) (hc : c ≠ 0) :
    scalarCurvature (rescale c j) = scalarCurvature j / c := by
  simp only [scalarCurvature,inverse_rescale c j hc,ricci_rescale c j hc,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma lapse_rescale (c : ℝ) (j : Jet) (z : ScalarJet) (hc : c ≠ 0) :
    lapseLaplacian (rescale c j) z = lapseLaplacian j z / c := by
  simp only [lapseLaplacian,inverse_rescale c j hc,christoffel_rescale c j hc,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  ring

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma radial_momentum_bound {r w B q q₀ : ℝ} (hr : 1 ≤ r) (hw : 0 ≤ w) (hB : 0 ≤ B)
    (hq : |q-q₀-2*w/r^2| ≤ B*w/r^3) : |q-q₀| ≤ (2+B)*w/r^2 := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have ha : |q-q₀| ≤ |q-q₀-2*w/r^2|+|2*w/r^2| := by
    have := abs_add_le (q-q₀-2*w/r^2) (2*w/r^2)
    convert this using 1
    congr 1
    ring
  rw [abs_of_nonneg (by positivity : 0 ≤ 2*w/r^2)] at ha
  have he : B*w/r^3 ≤ B*w/r^2 := by gcongr; norm_num
  have hid : B*w/r^2+2*w/r^2 = (2+B)*w/r^2 := by ring
  linarith

lemma smallNull_to_CQ {r w S B D T Q a a₀ q q₀ x x₀ : ℝ}
    (hr : 1 ≤ r) (hw : 0 ≤ w) (hS : 0 ≤ S) (hB : 0 ≤ B)
    (hD : 0 ≤ D) (hT : 0 ≤ T) (hQ : 0 ≤ Q)
    (hx : |x-x₀-2*w/(r^3*Real.sqrt r)| ≤ S*w/r^4)
    (hq : |q-q₀-2*w/r^2| ≤ B*w/r^3) (hq₀ : |q₀| ≤ Q/r^3)
    (ha : |a-1| ≤ D/r^2) (ha₀ : |a-a₀| ≤ T*w/r^3) :
    |((x+a*q)-(x₀+a₀*q₀))-(q-q₀)-2*w/(r^3*Real.sqrt r)| ≤
      (S+D*(2+B)+T*Q)*w/r^4 := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hdq := radial_momentum_bound hr hw hB hq
  have h₁ : |(a-1)*(q-q₀)| ≤ D*(2+B)*w/r^4 := by
    rw [abs_mul]
    calc
      _ ≤ (D/r^2)*((2+B)*w/r^2) := mul_le_mul ha hdq (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have h₂ : |(a-a₀)*q₀| ≤ T*Q*w/r^4 := by
    rw [abs_mul]
    calc
      _ ≤ (T*w/r^3)*(Q/r^3) := mul_le_mul ha₀ hq₀ (abs_nonneg _) (by positivity)
      _ = T*Q*w/r^6 := by ring
      _ ≤ _ := by gcongr; norm_num
  have he : ((x+a*q)-(x₀+a₀*q₀))-(q-q₀)-2*w/(r^3*Real.sqrt r) =
      (x-x₀-2*w/(r^3*Real.sqrt r))+(a-1)*(q-q₀)+(a-a₀)*q₀ := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  have ht := abs_add_le (x-x₀-2*w/(r^3*Real.sqrt r)) ((a-1)*(q-q₀))
  have heq : |S| * w/r^4+D*(2+B)*w/r^4+T*Q*w/r^4 = (|S| + D*(2+B)+T*Q)*w/r^4 := by ring
  rw [← abs_of_nonneg hS] at hx ⊢
  linarith

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma productJet_smooth : ContDiff ℝ ∞ (fun j : ScalarJet × ScalarJet => productJet j.1 j.2) := by
  unfold productJet
  fun_prop

lemma reciprocalJet_smooth {j : ScalarJet} (h0 : j.1 ≠ 0) : ContDiffAt ℝ ∞ reciprocalJet j := by
  unfold reciprocalJet
  apply ContDiffAt.prodMk
  · exact contDiffAt_const.div (by fun_prop) h0
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro a
    exact (by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => -j.2.1 a) j).div
      (by fun_prop) (pow_ne_zero 2 h0)
  · apply contDiffAt_pi.mpr
    intro a
    apply contDiffAt_pi.mpr
    intro b
    exact ((by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => 2*j.2.1 a*j.2.1 b) j).div
      (by fun_prop) (pow_ne_zero 3 h0)).sub
      ((by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => j.2.2 a b) j).div (by fun_prop) (pow_ne_zero 2 h0))

lemma sqrtJet_smooth {j : ScalarJet} (h0 : 0 < j.1) : ContDiffAt ℝ ∞ sqrtJet j := by
  have hs : ContDiffAt ℝ ∞ (fun j : ScalarJet => Real.sqrt j.1) j :=
    (by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => j.1) j).sqrt h0.ne'
  unfold sqrtJet
  apply ContDiffAt.prodMk hs
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro a
    exact (by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => j.2.1 a) j).div (hs.const_smul (2:ℝ)) (by positivity)
  · apply contDiffAt_pi.mpr
    intro a
    apply contDiffAt_pi.mpr
    intro b
    exact ((by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => j.2.2 a b) j).div (hs.const_smul (2:ℝ)) (by positivity)).sub
      ((by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => j.2.1 a*j.2.1 b) j).div ((hs.pow 3).const_smul (4:ℝ)) (by positivity))

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma determinantJet_smooth : ContDiff ℝ ∞ determinantJet := by
  unfold determinantJet
  exact (productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun q : MatrixScalarJet => (q 0 0,q 1 1)))).sub
    (productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun q : MatrixScalarJet => (q 0 1,q 1 0))))

lemma inverseMatrixJet_smooth {q : MatrixScalarJet}
    (h0 : determinant (fun i k => (q i k).1) ≠ 0) (i k : I) :
    ContDiffAt ℝ ∞ (fun p : MatrixScalarJet => inverseMatrixJet p i k) q := by
  have hc : ContDiffAt ℝ ∞ (fun p : MatrixScalarJet =>
      (!![p 1 1, -p 0 1; -p 1 0, p 0 0] : MatrixScalarJet) i k) q := by
    fin_cases i <;> fin_cases k <;> dsimp <;> fun_prop
  exact productJet_smooth.contDiffAt.comp q
    (hc.prodMk ((reciprocalJet_smooth h0).comp q determinantJet_smooth.contDiffAt))

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma normalizedLieJet_smooth (i k : I) : ContDiff ℝ ∞ (fun j : ExpansionInput => normalizedLieJet j i k) := by
  unfold normalizedLieJet
  apply ContDiff.sum
  intro a ha
  exact ((productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞
      (fun j : ExpansionInput => (j.2.2.2.1 a,j.2.1 a i k)))).add
    (productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞
      (fun j : ExpansionInput => (j.1 a k,j.2.2.2.2 i a))))).add
    (productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞
      (fun j : ExpansionInput => (j.1 i a,j.2.2.2.2 k a))))

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma smallNull_remainders_bound {r w A C B D x y z : ℝ}
    (hr : 1 ≤ r) (hw : 0 ≤ w) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hx : |x| ≤ C*A*w) (hy : |y| ≤ B) (hz : |z| ≤ D*A*w/r^3) :
    |x/r^4-2*w*y/(r^6*Real.sqrt r)+z/(2*r^2)| ≤
      (C*A+2*B+D*A)*w/r^4 := by
  have hr0 : 0 < r := by linarith
  have hs1 : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr hr
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hpad : |2*w*y/(r^6*Real.sqrt r)| ≤ 2*B*w/r^4 := by
    rw [abs_div,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg hw,abs_of_pos (mul_pos (pow_pos hr0 6) hsr)]
    calc
      _ ≤ 2*w*B/(r^6*Real.sqrt r) := by gcongr
      _ ≤ 2*w*B/r^4 := by
        apply div_le_div_of_nonneg_left (by positivity) (pow_pos hr0 4)
        exact (pow_le_pow_right₀ hr (by decide : 4 ≤ 6)).trans
          (le_mul_of_one_le_right (pow_nonneg hr0.le _) hs1)
      _ = _ := by ring
  have hcurv : |z/(2*r^2)| ≤ D*A*w/r^4 := by
    rw [abs_div,abs_of_pos (mul_pos (by norm_num : (0:ℝ) < 2) (pow_pos hr0 2))]
    calc
      _ ≤ (D*A*w/r^3)/(2*r^2) := by gcongr
      _ = D*A*w/(2*r^5) := by ring
      _ ≤ D*A*w/r^4 := by
        apply div_le_div_of_nonneg_left (by positivity) (pow_pos hr0 4)
        exact (pow_le_pow_right₀ hr (by decide : 4 ≤ 5)).trans
          (by nlinarith [pow_nonneg hr0.le 5])
  have hres : |x/r^4| ≤ C*A*w/r^4 := by
    rw [abs_div,abs_of_pos (pow_pos hr0 4)]
    exact div_le_div₀ (mul_nonneg (mul_nonneg hC hA) hw) hx (pow_pos hr0 4) le_rfl
  apply (abs_add_le _ _).trans
  have hs : |x/r^4-2*w*y/(r^6*Real.sqrt r)| ≤ |x/r^4|+|2*w*y/(r^6*Real.sqrt r)| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (x/r^4) (-(2*w*y/(r^6*Real.sqrt r)))
  have he : C*A*w/r^4+2*B*w/r^4+D*A*w/r^4 = (C*A+2*B+D*A)*w/r^4 := by ring
  linarith

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def lapseCoefficientRegion : Set LapseCoefficientInput :=
  {p | 0 < (lapseRad p).1 ∧ (lapseD p).1 ≠ 0}
lemma lapseV_smooth : ContDiff ℝ ∞ lapseV := by
  have hp : ContDiff ℝ ∞ (fun p : LapseCoefficientInput => productJet (lT p) (lT p)) :=
    productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun p : LapseCoefficientInput => (lT p,lT p)))
  unfold lapseV
  exact ((contDiff_const.fun_div (by fun_prop : ContDiff ℝ ∞ (fun p : LapseCoefficientInput => 1+lz p^2)) (by intro p; positivity))).fun_smul
    (((by fun_prop : ContDiff ℝ ∞ (fun p : LapseCoefficientInput => (2:ℝ) • lT p)).add
      ((by fun_prop : ContDiff ℝ ∞ (fun p : LapseCoefficientInput => lz p^3)).fun_smul hp)).sub (by fun_prop))
lemma lapseRad_smooth : ContDiff ℝ ∞ lapseRad :=
  contDiff_const.add ((by fun_prop : ContDiff ℝ ∞ (fun p : LapseCoefficientInput => lz p^3)).fun_smul lapseV_smooth)
lemma lapseD_smooth : ContDiff ℝ ∞ lapseD := by unfold lapseD; fun_prop
lemma lapseA_smooth {p : LapseCoefficientInput} (hp : p ∈ lapseCoefficientRegion) :
    ContDiffAt ℝ ∞ lapseA p := by
  have hs := (sqrtJet_smooth hp.1).comp p lapseRad_smooth.contDiffAt
  have hs1 := hs.add (contDiffAt_const (c := constantJet 1))
  have hs0 : (sqrtJet (lapseRad p)+constantJet 1).1 ≠ 0 := by
    change Real.sqrt (lapseRad p).1+1 ≠ 0
    positivity
  have hi := (reciprocalJet_smooth hs0).comp p hs1
  have hvi : ContDiffAt ℝ ∞ (fun p : LapseCoefficientInput =>
      productJet (lapseV p) (reciprocalJet (sqrtJet (lapseRad p)+constantJet 1))) p :=
    productJet_smooth.contDiffAt.comp p (lapseV_smooth.contDiffAt.prodMk hi)
  exact productJet_smooth.contDiffAt.comp p
    ((hvi.sub (by fun_prop)).prodMk ((reciprocalJet_smooth hp.2).comp p lapseD_smooth.contDiffAt))
lemma lapseCoefficientRegion_open : IsOpen lapseCoefficientRegion :=
  (isOpen_lt continuous_const (continuous_fst.comp lapseRad_smooth.continuous)).inter
    (isOpen_ne_fun (continuous_fst.comp lapseD_smooth.continuous) continuous_const)
lemma lapseCoefficientRegion_zero (T F D : ScalarJet) : (0,T,F,D) ∈ lapseCoefficientRegion := by
  simp [lapseCoefficientRegion,lapseRad,lapseD,constantJet,lz]

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI


noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def normalResidual (p : MomentumInput) : ℝ :=
  normalizedMean p*((mc p 2).1-(mc p 1).1)-
  mz p^3*tensorPair (mq p) (mX p) (fun i k => (mT p i k).1)-
  2*normalizedSpeed p*((mc p 3).1-mz p^4*∑ a, (mS p a).1*(mc p 1).2.1 a)+
  mz p*covectorDiv (mq p) (mE p)-
  2*mz p^4*covectorPair (mq p) (fun a => (mE p a).1) (accelerationCoefficient p)

def angularResidual (p : MomentumInput) (a : I) : ℝ :=
  normalizedSpeed p*(mEr p a-mz p^4*covectorLie (mS p) (mE p) a)+
  normalizedMean p*(mE p a).1+
  mz p*(tensorDiv (mq p) (mT p) a-(mc p 2).2.1 a-(mc p 1).2.1 a)+
  mw p*mz p^3*accelerationCoefficient p a+
  mz p^4*(((mc p 2).1-(mc p 1).1)*accelerationCoefficient p a-
    ∑ i, ∑ k, (mT p i a).1*inverse (mq p).1 i k*accelerationCoefficient p k)

def momentumResidual (p : MomentumInput) : ℝ × (I → ℝ) :=
  (normalResidual p,angularResidual p)
def momentumRegion : Set MomentumInput :=
  {p | determinant (mq p).1 ≠ 0 ∧ 1+mz p^3*(mc p 0).1 ≠ 0}

lemma momentumRegion_open : IsOpen momentumRegion := by
  apply IsOpen.inter
  · exact isOpen_ne_fun (determinant_smooth.continuous.comp (by fun_prop)) continuous_const
  · exact isOpen_ne_fun (by fun_prop) continuous_const

lemma momentInverse_smooth {p : MomentumInput} (hp : p ∈ momentumRegion) (i k : I) :
    ContDiffAt ℝ ∞ (fun p : MomentumInput => inverse (mq p).1 i k) p := by
  have hh := inverse_component_smooth (j := ((mq p),(1,0,0))) ⟨hp.1,by norm_num⟩ i k
  exact hh.comp p (by fun_prop : ContDiffAt ℝ ∞ (fun p : MomentumInput => ((mq p,(1,0,0)) : CombinedJet)) p)
lemma momentChristoffel_smooth {p : MomentumInput} (hp : p ∈ momentumRegion) (a i k : I) :
    ContDiffAt ℝ ∞ (fun p : MomentumInput => christoffel (mq p) a i k) p := by
  exact (christoffel_smooth (j := ((mq p),(1,0,0))) ⟨hp.1,by norm_num⟩ a i k).comp p
    (by fun_prop : ContDiffAt ℝ ∞ (fun p : MomentumInput => ((mq p,(1,0,0)) : CombinedJet)) p)
lemma normalizedSpeed_smooth : ContDiff ℝ ∞ normalizedSpeed := by
  unfold normalizedSpeed
  exact ((by fun_prop : ContDiff ℝ ∞ (fun p : MomentumInput => 1+mz p^2)).sqrt
    (by intro p; positivity)).mul (by fun_prop)
lemma normalizedMean_smooth : ContDiff ℝ ∞ normalizedMean :=
  (contDiff_const.mul normalizedSpeed_smooth).mul (by fun_prop)
lemma accelerationCoefficient_smooth {p : MomentumInput} (hp : p ∈ momentumRegion) (a : I) :
    ContDiffAt ℝ ∞ (fun p : MomentumInput => accelerationCoefficient p a) p :=
  (by fun_prop : ContDiffAt ℝ ∞ (fun p : MomentumInput => (mc p 0).2.1 a) p).div
    (by fun_prop) hp.2
lemma momentCovectorDiv_smooth {p : MomentumInput} (hp : p ∈ momentumRegion) :
    ContDiffAt ℝ ∞ (fun p : MomentumInput => covectorDiv (mq p) (mE p)) p := by
  unfold covectorDiv
  apply ContDiffAt.sum; intro i _
  apply ContDiffAt.sum; intro k _
  apply (momentInverse_smooth hp i k).mul
  apply ContDiffAt.sub (by fun_prop)
  apply ContDiffAt.sum; intro a _
  exact (momentChristoffel_smooth hp a i k).mul (by fun_prop)
lemma momentTensorDiv_smooth {p : MomentumInput} (hp : p ∈ momentumRegion) (a : I) :
    ContDiffAt ℝ ∞ (fun p : MomentumInput => tensorDiv (mq p) (mT p) a) p := by
  unfold tensorDiv
  apply ContDiffAt.sum; intro i _
  apply ContDiffAt.sum; intro k _
  apply (momentInverse_smooth hp i k).mul
  apply ContDiffAt.sub (by fun_prop)
  apply ContDiffAt.sum; intro b _
  exact ((momentChristoffel_smooth hp b i k).mul (by fun_prop)).add
    ((momentChristoffel_smooth hp b i a).mul (by fun_prop))
lemma momentTensorPair_smooth {p : MomentumInput} (hp : p ∈ momentumRegion) :
    ContDiffAt ℝ ∞ (fun p : MomentumInput => tensorPair (mq p) (mX p) (fun i k => (mT p i k).1)) p := by
  unfold tensorPair
  apply ContDiffAt.sum; intro i _
  apply ContDiffAt.sum; intro k _
  apply ContDiffAt.sum; intro a _
  apply ContDiffAt.sum; intro b _
  exact (((momentInverse_smooth hp i a).mul (momentInverse_smooth hp k b)).mul (by fun_prop)).mul (by fun_prop)
lemma momentCovectorPair_smooth {p : MomentumInput} (hp : p ∈ momentumRegion) :
    ContDiffAt ℝ ∞ (fun p : MomentumInput => covectorPair (mq p) (fun a => (mE p a).1) (accelerationCoefficient p)) p := by
  unfold covectorPair
  apply ContDiffAt.sum; intro i _
  apply ContDiffAt.sum; intro k _
  exact ((momentInverse_smooth hp i k).mul (by fun_prop)).mul (accelerationCoefficient_smooth hp k)

lemma momentumResidual_smooth {p : MomentumInput} (hp : p ∈ momentumRegion) :
    ContDiffAt ℝ ∞ momentumResidual p := by
  have hl (a : I) : ContDiff ℝ ∞ (fun p : MomentumInput => covectorLie (mS p) (mE p) a) := by
    unfold covectorLie
    fun_prop
  have hm := normalizedMean_smooth.contDiffAt (x := p)
  have hu := normalizedSpeed_smooth.contDiffAt (x := p)
  apply ContDiffAt.prodMk
  · unfold normalResidual
    apply ContDiffAt.sub
    · apply ContDiffAt.add
      · apply ContDiffAt.sub
        · apply ContDiffAt.sub
          · exact hm.mul (by fun_prop)
          · exact ContDiffAt.mul (by fun_prop) (momentTensorPair_smooth hp)
        · exact (contDiffAt_const.mul hu).mul (by fun_prop)
      · exact ContDiffAt.mul (by fun_prop) (momentCovectorDiv_smooth hp)
    · exact ContDiffAt.mul (by fun_prop) (momentCovectorPair_smooth hp)
  · apply contDiffAt_pi.mpr
    intro a
    unfold angularResidual
    have ht : ContDiffAt ℝ ∞ (fun p : MomentumInput =>
        ∑ i, ∑ k, (mT p i a).1*inverse (mq p).1 i k*accelerationCoefficient p k) p := by
      apply ContDiffAt.sum; intro i _
      apply ContDiffAt.sum; intro k _
      exact (ContDiffAt.mul (by fun_prop) (momentInverse_smooth hp i k)).mul
        (accelerationCoefficient_smooth hp k)
    apply ContDiffAt.add
    · apply ContDiffAt.add
      · apply ContDiffAt.add
        · apply ContDiffAt.add
          · apply hu.mul
            apply ContDiffAt.sub (by fun_prop)
            exact ContDiffAt.mul (by fun_prop) (hl a).contDiffAt
          · exact hm.mul (by fun_prop)
        · exact ContDiffAt.mul (by fun_prop)
            (((momentTensorDiv_smooth hp a).sub (by fun_prop)).sub (by fun_prop))
      · exact ContDiffAt.mul (by fun_prop) (accelerationCoefficient_smooth hp a)
    · apply ContDiffAt.mul (by fun_prop)
      exact (ContDiffAt.mul (by fun_prop) (accelerationCoefficient_smooth hp a)).sub ht

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma covectorDiv_rescale (q : Jet) (E : CovectorJet) {c : ℝ} (hc : c ≠ 0) (d : ℝ) :
    covectorDiv (rescale c q) (d • E) = (d/c)*covectorDiv q E := by
  simp only [covectorDiv,inverse_rescale c q hc,christoffel_rescale c q hc,
    Pi.smul_apply,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Fin.sum_univ_two]
  ring
lemma tensorDiv_rescale (q : Jet) (T : CovariantTensorJet) {c : ℝ} (hc : c ≠ 0) (d : ℝ) (a : I) :
    tensorDiv (rescale c q) (d • T) a = (d/c)*tensorDiv q T a := by
  simp only [tensorDiv,inverse_rescale c q hc,christoffel_rescale c q hc,
    Pi.smul_apply,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Fin.sum_univ_two]
  ring
lemma covectorPair_rescale (q : Jet) (E B : I → ℝ) {c : ℝ} (hc : c ≠ 0) (d e : ℝ) :
    covectorPair (rescale c q) (d • E) (e • B) = (d*e/c)*covectorPair q E B := by
  simp only [covectorPair,inverse_rescale c q hc,Pi.smul_apply,smul_eq_mul,Fin.sum_univ_two]
  ring
lemma tensorPair_rescale (q : Jet) (X T : Mat) {c : ℝ} (hc : c ≠ 0) (d e : ℝ) :
    tensorPair (rescale c q) (d • X) (e • T) = (d*e/c^2)*tensorPair q X T := by
  simp only [tensorPair,inverse_rescale c q hc,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_two]
  ring
lemma covectorLie_smul (S E : CovectorJet) (c d : ℝ) (a : I) :
    covectorLie (c • S) (d • E) a = c*d*covectorLie S E a := by
  simp only [covectorLie,Pi.smul_apply,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Fin.sum_univ_two]
  ring

theorem coordinateQ_factor {p : MomentumInput} (hz : mz p ≠ 0) :
    coordinateQ p = normalizedMean p*mw p*mz p^2+mz p^3*normalResidual p := by
  have hc : 1/mz p^2 ≠ 0 := one_div_ne_zero (pow_ne_zero _ hz)
  unfold coordinateQ normalMomentum
  erw [tensorPair_rescale _ _ _ hc,covectorDiv_rescale _ _ hc]
  have hE : (fun a => ((mz p^2 • mE p) a).1) = mz p^2 • (fun a => (mE p a).1) := rfl
  rw [hE,covectorPair_rescale _ _ _ hc]
  simp only [physicalLJet,physicalTJet,constantJet,Prod.fst_add,Prod.smul_fst,smul_eq_mul]
  unfold normalResidual
  field_simp
  ring

theorem coordinateZ_factor {p : MomentumInput} (hz : mz p ≠ 0) (a : I) :
    coordinateZ p a = mz p^2*angularResidual p a := by
  have hc : 1/mz p^2 ≠ 0 := one_div_ne_zero (pow_ne_zero _ hz)
  unfold coordinateZ angularMomentum
  rw [covectorLie_smul,tensorDiv_rescale _ _ hc]
  simp only [inverse_rescale _ _ hc,physicalLJet,physicalTJet,constantJet,
    Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,Pi.add_apply,
    Pi.zero_apply,smul_eq_mul,zero_add]
  unfold angularResidual
  simp only [Fin.sum_univ_two]
  field_simp
  ring

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def rawRegular (p : RawCollarInput) : Prop := determinant (fun i k => (rawQ p i k).1) ≠ 0

lemma rawQ_smooth : ContDiff ℝ ∞ rawQ := by unfold rawQ; fun_prop
lemma rawExpansionInput_smooth : ContDiff ℝ ∞ rawExpansionInput := by
  unfold rawExpansionInput rawQ rawDQ rawQr rawS rawDS
  fun_prop
lemma rawC_smooth (i k : I) : ContDiff ℝ ∞ (fun p => rawC p i k) := by
  unfold rawC
  exact (by unfold rawQr; fun_prop : ContDiff ℝ ∞ (fun p : RawCollarInput => rawQr p i k)).sub
    ((by fun_prop : ContDiff ℝ ∞ rz).fun_smul ((normalizedLieJet_smooth i k).comp rawExpansionInput_smooth))
lemma matrixTraceJet_smooth {q t : MatrixScalarJet}
    (h : determinant (fun i k => (q i k).1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun qt : MatrixScalarJet × MatrixScalarJet => matrixTraceJet qt.1 qt.2) (q,t) := by
  unfold matrixTraceJet
  apply ContDiffAt.sum; intro i _
  apply ContDiffAt.sum; intro k _
  exact productJet_smooth.contDiffAt.comp (q,t)
    (((inverseMatrixJet_smooth h i k).comp (q,t) (by fun_prop :
      ContDiffAt ℝ ∞ (fun qt : MatrixScalarJet × MatrixScalarJet => qt.1) (q,t))).prodMk (by fun_prop : ContDiffAt ℝ ∞ (fun qt : MatrixScalarJet × MatrixScalarJet => qt.2 k i) (q,t)))
lemma traceFreeJet_smooth {q t : MatrixScalarJet}
    (h : determinant (fun i k => (q i k).1) ≠ 0) :
    ContDiffAt ℝ ∞ (fun qt : MatrixScalarJet × MatrixScalarJet => traceFreeJet qt.1 qt.2) (q,t) := by
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro k
  unfold traceFreeJet
  exact (by fun_prop : ContDiffAt ℝ ∞ (fun qt : MatrixScalarJet × MatrixScalarJet => qt.2 i k) (q,t)).sub
    ((productJet_smooth.contDiffAt.comp (q,t) ((matrixTraceJet_smooth h).prodMk (by fun_prop))).const_smul (1/2:ℝ))
lemma rawD_smooth {p : RawCollarInput} (hp : rawRegular p) : ContDiffAt ℝ ∞ rawD p := by
  have hc : ContDiff ℝ ∞ rawC := contDiff_pi.mpr fun i => contDiff_pi.mpr fun k => rawC_smooth i k
  exact ((matrixTraceJet_smooth hp).comp p (rawQ_smooth.contDiffAt.prodMk hc.contDiffAt)).const_smul (1/4:ℝ)
lemma rawT_smooth : ContDiff ℝ ∞ rawT := by unfold rawT; fun_prop
lemma rawF_smooth : ContDiff ℝ ∞ rawF := by
  unfold rawF constantJet
  fun_prop
lemma rawLapseInput_smooth {p : RawCollarInput} (hp : rawRegular p) :
    ContDiffAt ℝ ∞ rawLapseInput p :=
  (by fun_prop : ContDiffAt ℝ ∞ rz p).prodMk
    (rawT_smooth.contDiffAt.prodMk (rawF_smooth.contDiffAt.prodMk (rawD_smooth hp)))
lemma rawA_smooth {p : RawCollarInput} (hp : rawRegular p)
    (hl : rawLapseInput p ∈ lapseCoefficientRegion) : ContDiffAt ℝ ∞ rawA p :=
  (lapseA_smooth hl).comp p (rawLapseInput_smooth hp)
lemma rawMomentumInput_smooth {p : RawCollarInput} (hp : rawRegular p)
    (hl : rawLapseInput p ∈ lapseCoefficientRegion) : ContDiffAt ℝ ∞ rawMomentumInput p := by
  have hq := rawQ_smooth.contDiffAt (x:=p)
  have ha := rawA_smooth hp hl
  have hD := rawD_smooth hp
  have ht0 := traceFreeJet_smooth (q:=rawQ p) (t:=rtau p) hp
  have ht1 := ht0.comp p (hq.prodMk
      (by fun_prop : ContDiffAt ℝ ∞ (fun p : RawCollarInput => rtau p) p))
  have hτ : ContDiffAt ℝ ∞ (fun p : RawCollarInput => traceFreeJet (rawQ p) (rtau p)) p := ht1
  have hc : ContDiff ℝ ∞ rawC := contDiff_pi.mpr fun i => contDiff_pi.mpr fun k => rawC_smooth i k
  have hx0 := traceFreeJet_smooth (q:=rawQ p) (t:=rawC p) hp
  have hx1 := hx0.comp p (hq.prodMk hc.contDiffAt)
  have hχ : ContDiffAt ℝ ∞ (fun p : RawCollarInput => traceFreeJet (rawQ p) (rawC p)) p := hx1
  have hs : ContDiff ℝ ∞ (fun p : RawCollarInput => Real.sqrt (1+rz p^2)) :=
    (by fun_prop : ContDiff ℝ ∞ (fun p : RawCollarInput => 1+rz p^2)).sqrt (by intro p; positivity)
  have hspeed : ContDiffAt ℝ ∞ rawLambda p := by
    unfold rawLambda
    exact hs.contDiffAt.mul (contDiffAt_const.add ((by fun_prop : ContDiffAt ℝ ∞ (fun p : RawCollarInput => rz p^3) p).mul (contDiffAt_fst.comp p ha)))
  have hX : ContDiffAt ℝ ∞ rawX p := by
    apply contDiffAt_pi.mpr; intro i
    apply contDiffAt_pi.mpr; intro k
    exact (hspeed.div_const 2).mul (contDiffAt_fst.comp p (contDiffAt_pi.mp (contDiffAt_pi.mp hχ i) k))
  unfold rawMomentumInput scalarMatrixToJet
  apply ContDiffAt.prodMk (by fun_prop)
  apply ContDiffAt.prodMk (by fun_prop)
  apply ContDiffAt.prodMk
  · fun_prop
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro a
    fin_cases a <;> dsimp <;>
      first | exact ha | exact rawT_smooth.contDiffAt | exact hD | dsimp [rawL,rawTr]; fun_prop
  apply ContDiffAt.prodMk
  · unfold rawS; fun_prop
  apply ContDiffAt.prodMk (by fun_prop)
  apply ContDiffAt.prodMk
  · exact (by fun_prop : ContDiffAt ℝ ∞ (fun p : RawCollarInput => 1-re p) p).smul hτ
  exact hX.prodMk (by fun_prop)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def lapseResidual (p : MomentumInput) : ℝ :=
  ∑ i, ∑ k, inverse (mq p).1 i k *
    (2*mz p^3*accelerationCoefficient p i*accelerationCoefficient p k-
      (mc p 0).2.2 i k/(1+mz p^3*(mc p 0).1)+
      ∑ a, christoffel (mq p) a i k*accelerationCoefficient p a)

def nullQuadratic (p : MomentumInput) : ℝ :=
  -(tensorPair (mq p) (mX p) (mX p)+
    tensorPair (mq p) (fun i k => (mT p i k).1) (fun i k => (mT p i k).1))/2+
    nullRatio p*tensorPair (mq p) (mX p) (fun i k => (mT p i k).1)-
    covectorPair (mq p) (fun i => (mE p i).1) (fun i => (mE p i).1)

def nullMomentumRegion : Set MomentumInput := {p | p ∈ momentumRegion ∧ nullD p ≠ 0}
lemma nullD_smooth : ContDiff ℝ ∞ nullD := by unfold nullD; fun_prop

lemma nullRatio_smooth {p : MomentumInput} (hp : p ∈ nullMomentumRegion) :
    ContDiffAt ℝ ∞ nullRatio p := by
  have hs : normalizedSpeed p ≠ 0 := mul_ne_zero (Real.sqrt_ne_zero'.mpr (by positivity)) hp.1.2
  exact (by fun_prop : ContDiffAt ℝ ∞ (fun p : MomentumInput => 1+mz p^3*(mc p 1).1) p).div
    (normalizedSpeed_smooth.contDiffAt.mul nullD_smooth.contDiffAt) (mul_ne_zero hs hp.2)
lemma lapseResidual_smooth {p : MomentumInput} (hp : p ∈ momentumRegion) :
    ContDiffAt ℝ ∞ lapseResidual p := by
  unfold lapseResidual
  apply ContDiffAt.sum; intro i _
  apply ContDiffAt.sum; intro k _
  apply (momentInverse_smooth hp i k).mul
  apply ContDiffAt.add
  · exact (((by fun_prop : ContDiffAt ℝ ∞ (fun p : MomentumInput => 2*mz p^3) p).mul
      (accelerationCoefficient_smooth hp i)).mul (accelerationCoefficient_smooth hp k)).sub
      ((by fun_prop : ContDiffAt ℝ ∞ (fun p : MomentumInput => (mc p 0).2.2 i k) p).div
        (by fun_prop) hp.2)
  · apply ContDiffAt.sum; intro a _
    exact (momentChristoffel_smooth hp a i k).mul (accelerationCoefficient_smooth hp a)

lemma momentTensorPair_fields_smooth {p : MomentumInput} (hp : p ∈ momentumRegion)
    {X T : MomentumInput → Mat} (hX : ContDiffAt ℝ ∞ X p) (hT : ContDiffAt ℝ ∞ T p) :
    ContDiffAt ℝ ∞ (fun p => tensorPair (mq p) (X p) (T p)) p := by
  unfold tensorPair
  apply ContDiffAt.sum; intro i _
  apply ContDiffAt.sum; intro k _
  apply ContDiffAt.sum; intro a _
  apply ContDiffAt.sum; intro b _
  exact (((momentInverse_smooth hp i a).mul (momentInverse_smooth hp k b)).mul
    (contDiffAt_pi.mp (contDiffAt_pi.mp hX i) k)).mul
      (contDiffAt_pi.mp (contDiffAt_pi.mp hT a) b)
lemma momentCovectorPair_fields_smooth {p : MomentumInput} (hp : p ∈ momentumRegion)
    {E B : MomentumInput → I → ℝ} (hE : ContDiffAt ℝ ∞ E p) (hB : ContDiffAt ℝ ∞ B p) :
    ContDiffAt ℝ ∞ (fun p => covectorPair (mq p) (E p) (B p)) p := by
  unfold covectorPair
  apply ContDiffAt.sum; intro i _
  apply ContDiffAt.sum; intro k _
  exact ((momentInverse_smooth hp i k).mul (contDiffAt_pi.mp hE i)).mul (contDiffAt_pi.mp hB k)
lemma nullQuadratic_smooth {p : MomentumInput} (hp : p ∈ nullMomentumRegion) :
    ContDiffAt ℝ ∞ nullQuadratic p := by
  unfold nullQuadratic
  exact ((((momentTensorPair_fields_smooth hp.1 (by fun_prop) (by fun_prop)).add
    (momentTensorPair_fields_smooth hp.1 (by fun_prop) (by fun_prop))).neg.div_const 2).add
    ((nullRatio_smooth hp).mul (momentTensorPair_smooth hp.1))).sub
    (momentCovectorPair_fields_smooth hp.1 (by fun_prop) (by fun_prop))

def nullResidual (p : NullInput) : ℝ :=
  2*(nFr p-mz (nP p)^3*∑ a, (mS (nP p) a).1*(nF p).2.1 a)/nullD (nP p)-
  mz (nP p)*(mc (nP p) 4).1*(2-6*mz (nP p)*(nF p).1)/nullD (nP p)-
  mz (nP p)*lapseResidual (nP p)+mz (nP p)^2*nullQuadratic (nP p)-
  nullRatio (nP p)*(covectorDiv (mq (nP p)) (mE (nP p))-
    2*mz (nP p)^3*covectorPair (mq (nP p)) (fun a => (mE (nP p) a).1)
      (accelerationCoefficient (nP p)))

def nullRegion : Set NullInput := nP ⁻¹' nullMomentumRegion

lemma nullResidual_smooth {p : NullInput} (hp : p ∈ nullRegion) :
    ContDiffAt ℝ ∞ nullResidual p := by
  have hproj : ContDiffAt ℝ ∞ nP p := by fun_prop
  have hD := nullD_smooth.contDiffAt.comp p hproj
  have hR := (nullRatio_smooth hp).comp p hproj
  have hLap := (lapseResidual_smooth hp.1).comp p hproj
  have hQ := (nullQuadratic_smooth hp).comp p hproj
  have hdiv := (momentCovectorDiv_smooth hp.1).comp p hproj
  have hpair : ContDiffAt ℝ ∞ (fun p : NullInput =>
      covectorPair (mq (nP p)) (fun a => (mE (nP p) a).1)
      (accelerationCoefficient (nP p))) p := by
    have h0 := momentCovectorPair_fields_smooth hp.1
      (by fun_prop : ContDiffAt ℝ ∞ (fun p : MomentumInput => fun a => (mE p a).1) (nP p))
      (contDiffAt_pi.mpr fun a => accelerationCoefficient_smooth hp.1 a)
    exact h0.comp p hproj
  unfold nullResidual
  exact (((((by fun_prop : ContDiffAt ℝ ∞ (fun p : NullInput =>
    2*(nFr p-mz (nP p)^3*∑ a, (mS (nP p) a).1*(nF p).2.1 a)) p).div hD hp.2).sub
    ((by fun_prop : ContDiffAt ℝ ∞ (fun p : NullInput =>
      mz (nP p)*(mc (nP p) 4).1*(2-6*mz (nP p)*(nF p).1)) p).div hD hp.2)).sub
      ((by fun_prop : ContDiffAt ℝ ∞ (fun p : NullInput => mz (nP p)) p).mul hLap)).add ((by fun_prop : ContDiffAt ℝ ∞ (fun p : NullInput => mz (nP p)^2) p).mul hQ)).sub
    (hR.mul (hdiv.sub ((by fun_prop : ContDiffAt ℝ ∞ (fun p : NullInput => 2*mz (nP p)^3) p).mul hpair)))

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def meanResidual (p : MomentumInput) : ℝ :=
  2/(Real.sqrt (1+mz p^2)+1)+2*Real.sqrt (1+mz p^2)*mz p*
    ((mc p 0).1+(mc p 4).1+mz p^3*(mc p 0).1*(mc p 4).1)
lemma meanResidual_smooth : ContDiff ℝ ∞ meanResidual := by
  have hs : ContDiff ℝ ∞ (fun p : MomentumInput => Real.sqrt (1+mz p^2)) :=
    (by fun_prop : ContDiff ℝ ∞ (fun p : MomentumInput => 1+mz p^2)).sqrt
      (by intro p; positivity)
  unfold meanResidual
  exact (contDiff_const.fun_div (hs.add contDiff_const) (by intro p; positivity)).add
    ((((contDiff_const.mul hs).mul (by fun_prop))).mul (by fun_prop))
lemma normalizedMean_factor (p : MomentumInput) :
    normalizedMean p-2 = mz p^2*meanResidual p := by
  have hs := Real.sq_sqrt (show 0 ≤ 1+mz p^2 by positivity)
  have hn : Real.sqrt (1+mz p^2)+1 ≠ 0 := by positivity
  unfold normalizedMean normalizedSpeed meanResidual
  field_simp
  linear_combination hs

lemma momentum_uniform_on_compact {K : Set MomentumInput} (hK : IsCompact K)
    (hreg : K ⊆ momentumRegion) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ≥0, ∃ B : ℝ, 0 ≤ B ∧
      LipschitzOnWith C momentumResidual (Metric.cthickening δ K) ∧
      ∀ p ∈ Metric.cthickening δ K, ‖momentumResidual p‖ ≤ B ∧ |meanResidual p| ≤ B := by
  let : FiniteDimensional ℝ MomentumInput := inferInstance
  let : ProperSpace MomentumInput := FiniteDimensional.proper ℝ MomentumInput
  obtain ⟨δ,hδ,hsub⟩ := hK.exists_cthickening_subset_open momentumRegion_open hreg
  have hk := hK.cthickening (r := δ)
  obtain ⟨C,hC⟩ : ∃ C, LipschitzOnWith C momentumResidual (Metric.cthickening δ K) := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hk
    intro p hp
    obtain ⟨C,t,ht,hC⟩ := ((momentumResidual_smooth (hsub hp)).of_le
      (by simp : (1:ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
    exact ⟨C,t,mem_nhdsWithin_of_mem_nhds ht,hC⟩
  obtain ⟨B₁,hB₁⟩ := hk.exists_bound_of_continuousOn
    (fun p hp => (momentumResidual_smooth (hsub hp)).continuousAt.continuousWithinAt)
  obtain ⟨B₂,hB₂⟩ := hk.exists_bound_of_continuousOn meanResidual_smooth.continuous.continuousOn
  refine ⟨δ,hδ,C,max 0 (max B₁ B₂),le_max_left _ _,hC,?_⟩
  intro p hp
  constructor
  · exact (hB₁ p hp).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hB₂ p hp).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem weighted_momentum {K : Set MomentumInput} (hK : IsCompact K)
    (hreg : K ⊆ momentumRegion) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ p p₀ : MomentumInput, p ∈ Metric.cthickening δ K → p₀ ∈ Metric.cthickening δ K →
      ∀ r A : ℝ, 1 ≤ r → mz p = 1/r → mz p₀ = 1/r → mw p₀ = 0 →
      0 ≤ mw p → 0 ≤ A → ‖p-p₀‖ ≤ A*mw p →
      |coordinateQ p₀| ≤ B/r^3 ∧
      |coordinateQ p-coordinateQ p₀-normalizedMean p*mw p/r^2| ≤ C*A*mw p/r^3 ∧
      |coordinateQ p-coordinateQ p₀-2*mw p/r^2| ≤ (C*A+B)*mw p/r^3 ∧
      (∀ a, |coordinateZ p₀ a| ≤ B/r^2) ∧
      (∀ a, |coordinateZ p a-coordinateZ p₀ a| ≤ C*A*mw p/r^2) ∧
      |normalizedMean p-2| ≤ B/r^2 := by
  obtain ⟨δ,hδ,C,B,hB,hLip,hbound⟩ := momentum_uniform_on_compact hK hreg
  refine ⟨δ,hδ,C,B,C.coe_nonneg,hB,?_⟩
  intro p p₀ hp hp₀ r A hr hz hz₀ hw₀ hw hA hd
  have hr0 : 0 < r := by linarith
  have hzn : mz p ≠ 0 := by rw [hz]; positivity
  have hz₀n : mz p₀ ≠ 0 := by rw [hz₀]; positivity
  have hres : ‖momentumResidual p-momentumResidual p₀‖ ≤ (C:ℝ)*(A*mw p) := by
    have hh := hLip.dist_le_mul p hp p₀ hp₀
    rw [dist_eq_norm,dist_eq_norm] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hd C.coe_nonneg)
  have hn : |normalResidual p-normalResidual p₀| ≤ (C:ℝ)*(A*mw p) :=
    (show _ ≤ ‖momentumResidual p-momentumResidual p₀‖ from norm_fst_le _).trans hres
  have hn₀ : |normalResidual p₀| ≤ B := (norm_fst_le (momentumResidual p₀)).trans (hbound p₀ hp₀).1
  have ha (a : I) : |angularResidual p a-angularResidual p₀ a| ≤ (C:ℝ)*(A*mw p) :=
    (norm_le_pi_norm (angularResidual p-angularResidual p₀) a).trans ((norm_snd_le _).trans hres)
  have ha₀ (a : I) : |angularResidual p₀ a| ≤ B :=
    (norm_le_pi_norm (angularResidual p₀) a).trans ((norm_snd_le _).trans (hbound p₀ hp₀).1)
  have hq₀ : coordinateQ p₀ = normalResidual p₀/r^3 := by
    rw [coordinateQ_factor hz₀n,hz₀,hw₀]
    ring
  have hdiff : coordinateQ p-coordinateQ p₀-normalizedMean p*mw p/r^2 =
      (normalResidual p-normalResidual p₀)/r^3 := by
    rw [coordinateQ_factor hzn,hq₀,hz]
    ring
  have hmean : |normalizedMean p-2| ≤ B/r^2 := by
    rw [normalizedMean_factor,hz,abs_mul,abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ (1/r)^2*B := mul_le_mul_of_nonneg_left (hbound p hp).2 (sq_nonneg _)
      _ = _ := by ring
  have hqd : |coordinateQ p-coordinateQ p₀-normalizedMean p*mw p/r^2| ≤ (C:ℝ)*A*mw p/r^3 := by
    rw [hdiff,abs_div,abs_of_pos (pow_pos hr0 3)]
    exact (div_le_div_of_nonneg_right hn (pow_nonneg hr0.le 3)).trans_eq (by ring)
  refine ⟨?_,hqd,?_,?_,?_,hmean⟩
  · rw [hq₀,abs_div,abs_of_pos (pow_pos hr0 3)]
    exact div_le_div_of_nonneg_right hn₀ (pow_nonneg hr0.le 3)
  · have he : coordinateQ p-coordinateQ p₀-2*mw p/r^2 =
        (coordinateQ p-coordinateQ p₀-normalizedMean p*mw p/r^2)+(normalizedMean p-2)*mw p/r^2 := by ring
    rw [he]
    apply (abs_add_le _ _).trans
    have ht : |(normalizedMean p-2)*mw p/r^2| ≤ B*mw p/r^3 := by
      rw [abs_div,abs_mul,abs_of_nonneg hw,abs_of_nonneg (sq_nonneg r)]
      calc
        _ ≤ (B/r^2)*mw p/r^2 := by gcongr
        _ = B*mw p/r^4 := by ring
        _ ≤ B*mw p/r^3 := by
          apply div_le_div_of_nonneg_left (mul_nonneg hB hw) (pow_pos hr0 3)
          simpa only [pow_succ,mul_one] using mul_le_mul_of_nonneg_left hr (pow_nonneg hr0.le 3)
    exact (add_le_add hqd ht).trans_eq (by ring)
  · intro a
    rw [coordinateZ_factor hz₀n,hz₀,abs_mul,abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (ha₀ a) (sq_nonneg (1/r))).trans_eq (by ring)
  · intro a
    rw [coordinateZ_factor hzn,coordinateZ_factor hz₀n,hz,hz₀,← mul_sub,abs_mul,
      abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (ha a) (sq_nonneg (1/r))).trans_eq (by ring)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def rawDomain : Set RawCollarInput := {p | rawRegular p ∧
  rawLapseInput p ∈ lapseCoefficientRegion ∧ rawMomentumInput p ∈ momentumRegion}

lemma rawRegular_cont {p : RawCollarInput} (hp : rawRegular p) :
    ∀ᶠ q in 𝓝 p, rawRegular q := by
  have hc : ContinuousAt (fun p : RawCollarInput => determinant (fun i k => (rawQ p i k).1)) p :=
    determinant_smooth.contDiffAt.continuousAt.comp
      (by fun_prop : ContinuousAt (fun p : RawCollarInput => (fun i k => (rawQ p i k).1)) p)
  exact hc.eventually (eventually_ne_nhds hp)
lemma rawDomain_open : IsOpen rawDomain := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hl := (rawLapseInput_smooth hp.1).continuousAt.eventually
    (lapseCoefficientRegion_open.mem_nhds hp.2.1)
  have hm := (rawMomentumInput_smooth hp.1 hp.2.1).continuousAt.eventually
    (momentumRegion_open.mem_nhds hp.2.2)
  filter_upwards [rawRegular_cont hp.1,hl,hm] with q hq hql hqm
  exact ⟨hq,hql,hqm⟩
lemma rawDomain_at_zero {p : RawCollarInput} (hz : rz p = 0)
    (hσ : determinant (fun i k => (rmat p 0 i k).1) ≠ 0) : p ∈ rawDomain := by
  have hq : rawQ p = rmat p 0 := by simp [rawQ,hz]
  have hreg : rawRegular p := by simpa [rawRegular,hq] using hσ
  have hl : rawLapseInput p ∈ lapseCoefficientRegion := by
    simpa only [rawLapseInput,hz] using lapseCoefficientRegion_zero (rawT p) (rawF p) (rawD p)
  refine ⟨hreg,hl,?_⟩
  change determinant (scalarMatrixToJet (rawQ p)).1 ≠ 0 ∧
    1+rz p^3*(rawA p).1 ≠ 0
  exact ⟨by simpa [scalarMatrixToJet,hq] using hσ,by simp [hz]⟩

lemma rawMomentum_uniform {K : Set RawCollarInput} (hK : IsCompact K)
    (hreg : K ⊆ rawDomain) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ≥0,
      Metric.cthickening δ K ⊆ rawDomain ∧
      LipschitzOnWith C rawMomentumInput (Metric.cthickening δ K) ∧
      IsCompact (rawMomentumInput '' Metric.cthickening δ K) := by
  let : FiniteDimensional ℝ RawMetricData := inferInstance
  let : FiniteDimensional ℝ RawTensorData := inferInstance
  let : FiniteDimensional ℝ RawCollarData := inferInstance
  let : FiniteDimensional ℝ RawCollarInput := inferInstance
  let : ProperSpace RawCollarInput := FiniteDimensional.proper ℝ RawCollarInput
  obtain ⟨δ,hδ,hsub⟩ := hK.exists_cthickening_subset_open rawDomain_open hreg
  have hk := hK.cthickening (r:=δ)
  obtain ⟨C,hC⟩ : ∃ C, LipschitzOnWith C rawMomentumInput (Metric.cthickening δ K) := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hk
    intro p hp
    obtain ⟨C,t,ht,hC⟩ := ((rawMomentumInput_smooth (hsub hp).1 (hsub hp).2.1).of_le
      (by simp : (1:ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
    exact ⟨C,t,mem_nhdsWithin_of_mem_nhds ht,hC⟩
  exact ⟨δ,hδ,C,hsub,hC,hk.image_of_continuousOn hC.continuousOn⟩

def rawZeroRadius (p : RawCollarInput) : RawCollarInput := (fun i => if i=0 then 0 else p.1 i,p.2)

lemma rawOriginal_z (p : RawCollarInput) : rz (rawOriginal p) = rz p := by simp [rawOriginal,rz]
lemma rawOriginal_w (p : RawCollarInput) : rwgt (rawOriginal p) = 0 := by simp [rawOriginal,rwgt,show (4:Fin 5) ≠ 0 by decide]
lemma rawZeroRadius_z (p : RawCollarInput) : rz (rawZeroRadius p) = 0 := by simp [rawZeroRadius,rz]
lemma rawZeroRadius_dist (p : RawCollarInput) : dist p (rawZeroRadius p) ≤ |rz p| := by
  rw [dist_eq_norm]
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
    intro i
    by_cases hi : i=0
    · subst i; simp [rawZeroRadius,rz]
    · simp [rawZeroRadius,hi,abs_nonneg]
  · simp [rawZeroRadius]
lemma rawOriginal_difference {p : RawCollarInput} {A : ℝ} (hA : 0 ≤ A)
    (hw : 0 ≤ rwgt p) (h : ∀ i, i ≠ 0 → |p.1 i| ≤ A*rwgt p) :
    ‖p-rawOriginal p‖ ≤ A*rwgt p := by
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hA hw)).mpr
    intro i
    by_cases hi : i=0
    · subst i; simp [rawOriginal,rz,mul_nonneg hA hw]
    · simpa [rawOriginal,hi,Real.norm_eq_abs] using h i hi
  · simp [rawOriginal,mul_nonneg hA hw]

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma lapseResidual_factor {p : MomentumInput} (_hp : p ∈ momentumRegion) :
    lapseLaplacian (mq p) (constantJet 1+mz p^3 • mc p 0) = mz p^3*lapseResidual p := by
  simp only [lapseLaplacian,lapseResidual,accelerationCoefficient,constantJet,
    Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,Pi.zero_apply,Pi.add_apply,
    Pi.smul_apply,Matrix.smul_apply,smul_eq_mul,zero_add,Fin.sum_univ_two]
  field_simp

lemma radius_ratios {z : ℝ} (hz : z ≠ 0) :
    z*z/(1/z^2)^2=z^6 ∧ z^2*z^2/(1/z^2)=z^6 ∧
      z^2/(1/z^2)=z^4 ∧ z^2*z^3/(1/z^2)=z^7 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp

lemma quadratic_rescale (q : Jet) (X T : Mat) (E : I → ℝ) (a z : ℝ) (hz : z ≠ 0) :
    -(tensorPair (rescale (1/z^2) q) (z • X) (z • X)+
      tensorPair (rescale (1/z^2) q) (z • T) (z • T))/2+
      a*tensorPair (rescale (1/z^2) q) (z • X) (z • T)-
      covectorPair (rescale (1/z^2) q) (z^2 • E) (z^2 • E) =
    z^6*(-(tensorPair q X X+tensorPair q T T)/2+a*tensorPair q X T-covectorPair q E E) := by
  have hc := one_div_ne_zero (pow_ne_zero 2 hz)
  rw [tensorPair_rescale q X X hc,tensorPair_rescale q T T hc,
    tensorPair_rescale q X T hc,covectorPair_rescale q E E hc]
  rw [(radius_ratios hz).1,(radius_ratios hz).2.1]
  ring

lemma physicalNullQuadratic_factor {p : MomentumInput} (hz : mz p ≠ 0) :
    physicalNullQuadratic p = mz p^6*nullQuadratic p := by
  exact quadratic_rescale (mq p) (mX p) (fun i k => (mT p i k).1)
    (fun a => (mE p a).1) (nullRatio p) (mz p) hz
lemma physicalNullEta_factor {p : MomentumInput} (hz : mz p ≠ 0) :
    physicalNullEta p = mz p^4*(covectorDiv (mq p) (mE p)-
      2*mz p^3*covectorPair (mq p) (fun a => (mE p a).1) (accelerationCoefficient p)) := by
  have hc := one_div_ne_zero (pow_ne_zero 2 hz)
  unfold physicalNullEta
  erw [covectorDiv_rescale _ _ hc,covectorPair_rescale _ _ _ hc]
  rw [(radius_ratios hz).2.2.1,(radius_ratios hz).2.2.2]
  ring

lemma null_mass_algebra (z w r s Fr SF F D : ℝ) (hd : 1+z^3*D ≠ 0) :
    2*(w/(r*s)+z^2*Fr-z^5*SF)/(1+z^3*D)*z^2+
      (1/(1+z^3*D)-1)*(2-6*z*F)*z^2 =
    2*w/(r*s)/(1+z^3*D)*z^2+
      z^4*(2*(Fr-z^3*SF)/(1+z^3*D)-z*D*(2-6*z*F)/(1+z^3*D)) := by
  field_simp
  ring

lemma coordinateSmallNull_factor_z {p : NullInput} (r : ℝ)
    (hz : mz (nP p) ≠ 0) (hp : p ∈ nullRegion) :
    coordinateSmallNull p r =
      2*mw (nP p)/(r*Real.sqrt r)/nullD (nP p)*mz (nP p)^2+
      (scalarCurvature (mq (nP p))/2-1)*mz (nP p)^2+
      mz (nP p)^4*nullResidual p := by
  have hc := one_div_ne_zero (pow_ne_zero 2 hz)
  have hm := null_mass_algebra (mz (nP p)) (mw (nP p)) r (Real.sqrt r) (nFr p)
    (∑ a, (mS (nP p) a).1*(nF p).2.1 a) (nF p).1 (mc (nP p) 4).1 hp.2
  change 2*(mw (nP p)/(r*Real.sqrt r)+mz (nP p)^2*nFr p-
    mz (nP p)^5*∑ a, (mS (nP p) a).1*(nF p).2.1 a)/nullD (nP p)*mz (nP p)^2+
    (1/nullD (nP p)-1)*(2-6*mz (nP p)*(nF p).1)*mz (nP p)^2 = _ at hm
  unfold coordinateSmallNull
  rw [scalar_rescale _ _ hc,lapse_rescale _ _ _ hc,lapseResidual_factor hp.1,
    physicalNullQuadratic_factor hz,physicalNullEta_factor hz]
  simp only [div_div_eq_mul_div,div_one]
  unfold nullResidual
  unfold nullD at hm ⊢
  linear_combination hm

theorem coordinateSmallNull_factor {p : NullInput} {r : ℝ}
    (hr : 0 < r) (hz : mz (nP p) = 1/r) (hp : p ∈ nullRegion) :
    coordinateSmallNull p r =
      2*mw (nP p)/(r^3*Real.sqrt r)/nullD (nP p)+
      (scalarCurvature (mq (nP p))/2-1)/r^2+nullResidual p/r^4 := by
  have hzn : mz (nP p) ≠ 0 := by rw [hz]; positivity
  rw [coordinateSmallNull_factor_z r hzn hp,hz]
  ring

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def ratioResidual (p : MomentumInput) : ℝ :=
  ((mc p 1).1-(mc p 0).1-(mc p 4).1-mz p^3*(mc p 0).1*(mc p 4).1)/
    (normalizedSpeed p*nullD p)
lemma ratioResidual_smooth {p : MomentumInput} (hp : p ∈ nullMomentumRegion) :
    ContDiffAt ℝ ∞ ratioResidual p := by
  have hs : normalizedSpeed p ≠ 0 :=
    mul_ne_zero (Real.sqrt_pos.mpr (by positivity)).ne' hp.1.2
  exact (by fun_prop : ContDiffAt ℝ ∞ (fun p : MomentumInput =>
    (mc p 1).1-(mc p 0).1-(mc p 4).1-mz p^3*(mc p 0).1*(mc p 4).1) p).div
      (normalizedSpeed_smooth.contDiffAt.mul nullD_smooth.contDiffAt) (mul_ne_zero hs hp.2)
lemma nullRatio_factor {p : MomentumInput} (hp : p ∈ nullMomentumRegion) :
    nullRatio p = 1/Real.sqrt (1+mz p^2)+mz p^3*ratioResidual p := by
  have hs : Real.sqrt (1+mz p^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have ha := hp.1.2
  have hd : 1+mz p^3*(mc p 4).1 ≠ 0 := hp.2
  unfold nullRatio ratioResidual normalizedSpeed nullD
  field_simp
  ring
lemma inverse_hyperbolic_ratio (z : ℝ) :
    1/Real.sqrt (1+z^2)-1 = -z^2/(Real.sqrt (1+z^2)*(Real.sqrt (1+z^2)+1)) := by
  have hs : Real.sqrt (1+z^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hs1 : Real.sqrt (1+z^2)+1 ≠ 0 := by positivity
  have hs2 := Real.sq_sqrt (show 0 ≤ 1+z^2 by positivity)
  field_simp
  nlinarith
lemma inverse_hyperbolic_ratio_bound (z : ℝ) :
    |1/Real.sqrt (1+z^2)-1| ≤ z^2 := by
  rw [inverse_hyperbolic_ratio,abs_div,abs_neg,abs_of_nonneg (sq_nonneg z),
    abs_of_pos (by positivity : 0 < Real.sqrt (1+z^2)*(Real.sqrt (1+z^2)+1))]
  apply div_le_self (sq_nonneg z)
  have hs : 1 ≤ Real.sqrt (1+z^2) := Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg z])
  nlinarith
lemma nullRatio_bound {p : MomentumInput} (hp : p ∈ nullMomentumRegion)
    {r B : ℝ} (hr : 1 ≤ r) (hz : mz p = 1/r) (hB : 0 ≤ B)
    (hb : |ratioResidual p| ≤ B) : |nullRatio p-1| ≤ (1+B)/r^2 := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hzr : 0 ≤ mz p := by rw [hz]; positivity
  rw [nullRatio_factor hp]
  have he : 1/Real.sqrt (1+mz p^2)+mz p^3*ratioResidual p-1 =
      (1/Real.sqrt (1+mz p^2)-1)+mz p^3*ratioResidual p := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_nonneg (pow_nonneg hzr 3)]
  calc
    _ ≤ mz p^2+mz p^3*B := add_le_add (inverse_hyperbolic_ratio_bound _) (by gcongr)
    _ = 1/r^2+B/r^3 := by rw [hz]; ring
    _ ≤ 1/r^2+B/r^2 := by gcongr; norm_num
    _ = _ := by ring
lemma nullRatio_difference {p q : MomentumInput} (hp : p ∈ nullMomentumRegion)
    (hq : q ∈ nullMomentumRegion) (hz : mz p = mz q) :
    nullRatio p-nullRatio q = mz p^3*(ratioResidual p-ratioResidual q) := by
  rw [nullRatio_factor hp,nullRatio_factor hq,← hz]
  ring

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma rawMomentum_z (p : RawCollarInput) : mz (rawMomentumInput p) = rz p := rfl
lemma rawMomentum_w (p : RawCollarInput) : mw (rawMomentumInput p) = rwgt p := rfl

theorem raw_weighted_momentum {K : Set RawCollarInput} (hK : IsCompact K)
    (hreg : K ⊆ rawDomain) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ p : RawCollarInput, p ∈ Metric.cthickening δ K →
      rawOriginal p ∈ Metric.cthickening δ K →
      ∀ r A : ℝ, 1 ≤ r → rz p = 1/r → 0 ≤ rwgt p → 0 ≤ A →
      (∀ i, i ≠ 0 → |p.1 i| ≤ A*rwgt p) →
      |coordinateQ (rawMomentumInput (rawOriginal p))| ≤ B/r^3 ∧
      |coordinateQ (rawMomentumInput p)-coordinateQ (rawMomentumInput (rawOriginal p))-
        normalizedMean (rawMomentumInput p)*rwgt p/r^2| ≤ C*A*rwgt p/r^3 ∧
      |coordinateQ (rawMomentumInput p)-coordinateQ (rawMomentumInput (rawOriginal p))-
        2*rwgt p/r^2| ≤ (C*A+B)*rwgt p/r^3 ∧
      (∀ a, |coordinateZ (rawMomentumInput (rawOriginal p)) a| ≤ B/r^2) ∧
      (∀ a, |coordinateZ (rawMomentumInput p) a-
        coordinateZ (rawMomentumInput (rawOriginal p)) a| ≤ C*A*rwgt p/r^2) ∧
      |normalizedMean (rawMomentumInput p)-2| ≤ B/r^2 := by
  obtain ⟨δ,hδ,Craw,hdom,hraw,hcompact⟩ := rawMomentum_uniform hK hreg
  have hinput : rawMomentumInput '' Metric.cthickening δ K ⊆ momentumRegion := by
    rintro _ ⟨p,hp,rfl⟩
    exact (hdom hp).2.2
  obtain ⟨ε,hε,C,B,hC,hB,hest⟩ := weighted_momentum hcompact hinput
  refine ⟨δ,hδ,C*Craw,B,mul_nonneg hC Craw.coe_nonneg,hB,?_⟩
  intro p hp hp₀ r A hr hz hw hA hparams
  have hd : ‖rawMomentumInput p-rawMomentumInput (rawOriginal p)‖ ≤
      ((Craw:ℝ)*A)*rwgt p := by
    have hh := hraw.dist_le_mul p hp (rawOriginal p) hp₀
    rw [dist_eq_norm,dist_eq_norm] at hh
    exact (hh.trans (mul_le_mul_of_nonneg_left
      (rawOriginal_difference hA hw hparams) Craw.coe_nonneg)).trans_eq (by ring)
  have hp' : rawMomentumInput p ∈ Metric.cthickening ε
      (rawMomentumInput '' Metric.cthickening δ K) :=
    Metric.self_subset_cthickening _ ⟨p,hp,rfl⟩
  have hp₀' : rawMomentumInput (rawOriginal p) ∈ Metric.cthickening ε
      (rawMomentumInput '' Metric.cthickening δ K) :=
    Metric.self_subset_cthickening _ ⟨rawOriginal p,hp₀,rfl⟩
  have hh := hest (rawMomentumInput p) (rawMomentumInput (rawOriginal p)) hp' hp₀'
    r ((Craw:ℝ)*A) hr hz (by simpa only [rawMomentum_z,rawOriginal_z] using hz)
    (rawOriginal_w p) hw (mul_nonneg Craw.coe_nonneg hA) hd
  simpa only [rawMomentum_w,mul_assoc] using hh

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma scalarMatrixToJet_sub (q q' : MatrixScalarJet) :
    scalarMatrixToJet q-scalarMatrixToJet q' = scalarMatrixToJet (q-q') := rfl
lemma scalarMatrixToJet_norm (q : MatrixScalarJet) : ‖scalarMatrixToJet q‖ ≤ ‖q‖ := by
  have hq (i k : I) : ‖q i k‖ ≤ ‖q‖ := Matrix.norm_entry_le_entrywise_sup_norm q
  apply norm_prod_le_iff.mpr
  constructor
  · exact (Matrix.norm_le_iff (norm_nonneg q)).mpr fun i k => (norm_fst_le (q i k)).trans (hq i k)
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg q)).mpr
    intro a
    apply (Matrix.norm_le_iff (norm_nonneg q)).mpr
    intro i k
    exact (norm_le_pi_norm (q i k).2.1 a).trans ((norm_fst_le (q i k).2).trans
      ((norm_snd_le (q i k)).trans (hq i k)))
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg q)).mpr
    intro a
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg q)).mpr
    intro b
    apply (Matrix.norm_le_iff (norm_nonneg q)).mpr
    intro i k
    exact (Matrix.norm_entry_le_entrywise_sup_norm (q i k).2.2).trans
      ((norm_snd_le (q i k).2).trans ((norm_snd_le (q i k)).trans (hq i k)))

lemma scalarCurvatureJet_smooth {q : Jet} (hq : determinant q.1 ≠ 0) :
    ContDiffAt ℝ ∞ scalarCurvature q := by
  have h0 := operators_smooth (j:=(q,(1,0,0))) ⟨hq,by norm_num⟩
  have h1 := h0.comp q (by fun_prop : ContDiffAt ℝ ∞ (fun q : Jet => (q,((1,0,0):ScalarJet))) q)
  exact contDiffAt_fst.comp q h1

lemma rawQ_difference (p : RawCollarInput) :
    rawQ p-rawQ (rawOriginal p) = (-re p*rz p^3) • rmat p 1 := by
  simp only [rawQ,rawOriginal,rz,re,rmat,ite_true,
    ite_eq_right (show (1:Fin 5) ≠ 0 by decide),sub_zero,mul_one]
  module

theorem raw_curvature_uniform {K : Set RawCollarInput} (hK : IsCompact K)
    (hreg : K ⊆ rawDomain) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ p : RawCollarInput, p ∈ Metric.cthickening δ K →
      rawOriginal p ∈ Metric.cthickening δ K →
      ∀ r A : ℝ, 1 ≤ r → rz p = 1/r → 0 ≤ rwgt p → 0 ≤ A →
      |re p| ≤ A*rwgt p →
      |scalarCurvature (scalarMatrixToJet (rawQ p))-
        scalarCurvature (scalarMatrixToJet (rawQ (rawOriginal p)))| ≤ C*A*rwgt p/r^3 := by
  let : FiniteDimensional ℝ RawMetricData := inferInstance
  let : FiniteDimensional ℝ RawTensorData := inferInstance
  let : FiniteDimensional ℝ RawCollarData := inferInstance
  let : FiniteDimensional ℝ RawCollarInput := inferInstance
  let : ProperSpace RawCollarInput := FiniteDimensional.proper ℝ RawCollarInput
  obtain ⟨δ,hδ,hsub⟩ := hK.exists_cthickening_subset_open rawDomain_open hreg
  have hk := hK.cthickening (r:=δ)
  have hqcont : Continuous (fun p => scalarMatrixToJet (rawQ p)) := by
    unfold scalarMatrixToJet
    fun_prop
  have hqc := hk.image hqcont
  obtain ⟨L,hLip⟩ : ∃ L, LipschitzOnWith L scalarCurvature
      ((fun p => scalarMatrixToJet (rawQ p)) '' Metric.cthickening δ K) := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hqc
    rintro _ ⟨p,hp,rfl⟩
    have hdet : determinant (scalarMatrixToJet (rawQ p)).1 ≠ 0 := (hsub hp).1
    obtain ⟨L,t,ht,hL⟩ := ((scalarCurvatureJet_smooth hdet).of_le
      (by simp : (1:ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
    exact ⟨L,t,mem_nhdsWithin_of_mem_nhds ht,hL⟩
  obtain ⟨B,hbound⟩ := hk.exists_bound_of_continuousOn
    (show ContinuousOn (fun p : RawCollarInput => rmat p 1) (Metric.cthickening δ K) from (by fun_prop))
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  refine ⟨δ,hδ,L*M,mul_nonneg L.coe_nonneg hM,?_⟩
  intro p hp hp₀ r A hr hz hw hA he
  have hr0 : 0 < r := by linarith
  have hm : ‖rmat p 1‖ ≤ M := (hbound p hp).trans (le_max_left _ _)
  have hdiff : ‖rawQ p-rawQ (rawOriginal p)‖ ≤ M*A*rwgt p/r^3 := by
    rw [rawQ_difference,norm_smul,Real.norm_eq_abs,abs_mul,abs_neg,hz,abs_pow,
      abs_of_pos (by positivity : 0 < (1:ℝ)/r)]
    calc
      _ ≤ (A*rwgt p)*(1/r)^3*M := by gcongr
      _ = _ := by ring
  have hh := hLip.dist_le_mul _ ⟨p,hp,rfl⟩ _ ⟨rawOriginal p,hp₀,rfl⟩
  rw [dist_eq_norm,dist_eq_norm,scalarMatrixToJet_sub] at hh
  exact (hh.trans (mul_le_mul_of_nonneg_left
    ((scalarMatrixToJet_norm _).trans hdiff) L.coe_nonneg)).trans_eq (by ring)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev nr (p : RawNullInput) := p.1

def rawNullDomain : Set RawNullInput := nr ⁻¹' rawDomain
lemma rawNullDomain_open : IsOpen rawNullDomain := rawDomain_open.preimage (by fun_prop)

lemma rawNullMap_regular {p : RawNullInput} (hp : p ∈ rawNullDomain) :
    rawNullMap p ∈ nullRegion := by
  refine ⟨hp.2.2,?_⟩
  exact hp.2.1.2
lemma rawNullMap_smooth {p : RawNullInput} (hp : p ∈ rawNullDomain) :
    ContDiffAt ℝ ∞ rawNullMap p := by
  have hm := (rawMomentumInput_smooth hp.1 hp.2.1).comp p
    (by fun_prop : ContDiffAt ℝ ∞ nr p)
  have hf := rawF_smooth.contDiffAt.comp p (by fun_prop : ContDiffAt ℝ ∞ nr p)
  exact hm.prodMk (hf.prodMk (by fun_prop))

lemma rawNullResidual_smooth {p : RawNullInput} (hp : p ∈ rawNullDomain) :
    ContDiffAt ℝ ∞ (fun p => nullResidual (rawNullMap p)) p := by
  have h0 := nullResidual_smooth (rawNullMap_regular hp)
  exact h0.comp p (rawNullMap_smooth hp)
lemma rawNullPadding_smooth {p : RawNullInput} (hp : p ∈ rawNullDomain) :
    ContDiffAt ℝ ∞ (fun p => (rawD p.1).1/nullD (rawMomentumInput p.1)) p := by
  have hD := contDiffAt_fst.comp p ((rawD_smooth hp.1).comp p
    (by fun_prop : ContDiffAt ℝ ∞ nr p))
  have hM := (rawMomentumInput_smooth hp.1 hp.2.1).comp p
    (by fun_prop : ContDiffAt ℝ ∞ nr p)
  exact hD.div (nullD_smooth.contDiffAt.comp p hM) (rawNullMap_regular hp).2

lemma rawNullOriginal_diff {p : RawNullInput} {A : ℝ} (hA : 0 ≤ A)
    (hw : 0 ≤ rwgt p.1) (hparams : ∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) :
    ‖p-rawNullOriginal p‖ ≤ A*rwgt p.1 := by
  apply norm_prod_le_iff.mpr
  refine ⟨rawOriginal_difference hA hw hparams,?_⟩
  change ‖p.2-p.2‖ ≤ _
  rw [sub_self,norm_zero]
  exact mul_nonneg hA hw

theorem raw_null_uniform {K : Set RawNullInput} (hK : IsCompact K)
    (hreg : K ⊆ rawNullDomain) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C B D : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ 0 ≤ D ∧
      Metric.cthickening δ K ⊆ rawNullDomain ∧
      ∀ p : RawNullInput, p ∈ Metric.cthickening δ K →
      rawNullOriginal p ∈ Metric.cthickening δ K →
      ∀ r A : ℝ, 1 ≤ r → rz p.1 = 1/r → 0 ≤ rwgt p.1 → 0 ≤ A →
      (∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) →
      |nullResidual (rawNullMap p)-nullResidual (rawNullMap (rawNullOriginal p))| ≤ C*A*rwgt p.1 ∧
      |(rawD p.1).1/nullD (rawMomentumInput p.1)| ≤ B ∧
      |scalarCurvature (scalarMatrixToJet (rawQ p.1))-
        scalarCurvature (scalarMatrixToJet (rawQ (rawOriginal p.1)))| ≤ D*A*rwgt p.1/r^3 := by
  let : FiniteDimensional ℝ RawMetricData := inferInstance
  let : FiniteDimensional ℝ RawTensorData := inferInstance
  let : FiniteDimensional ℝ RawCollarData := inferInstance
  let : FiniteDimensional ℝ RawCollarInput := inferInstance
  let : FiniteDimensional ℝ RawNullInput := inferInstance
  let : ProperSpace RawNullInput := FiniteDimensional.proper ℝ RawNullInput
  have hKp := hK.image (show Continuous nr from by fun_prop)
  have hKpreg : nr '' K ⊆ rawDomain := by rintro _ ⟨p,hp,rfl⟩; exact hreg hp
  obtain ⟨ε,hε,D,hD,hcurv⟩ := raw_curvature_uniform hKp hKpreg
  let U : Set RawNullInput := rawNullDomain ∩ nr ⁻¹' Metric.thickening ε (nr '' K)
  have hopen : IsOpen U := rawNullDomain_open.inter
    ((Metric.isOpen_thickening).preimage (by fun_prop : Continuous nr))
  have hKU : K ⊆ U := by
    intro p hp
    exact ⟨hreg hp,Metric.self_subset_thickening hε (nr '' K) ⟨p,hp,rfl⟩⟩
  obtain ⟨δ,hδ,hsub⟩ := hK.exists_cthickening_subset_open hopen hKU
  have hdom : Metric.cthickening δ K ⊆ rawNullDomain := fun _ hp => (hsub hp).1
  have hk := hK.cthickening (r:=δ)
  obtain ⟨C,hLip⟩ : ∃ C, LipschitzOnWith C (fun p => nullResidual (rawNullMap p))
      (Metric.cthickening δ K) := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hk
    intro p hp
    obtain ⟨C,t,ht,hC⟩ := ((rawNullResidual_smooth (hdom hp)).of_le
      (by simp : (1:ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
    exact ⟨C,t,mem_nhdsWithin_of_mem_nhds ht,hC⟩
  obtain ⟨B,hB⟩ := hk.exists_bound_of_continuousOn
    (fun p hp => (rawNullPadding_smooth (hdom hp)).continuousAt.continuousWithinAt)
  refine ⟨δ,hδ,C,max B 0,D,C.coe_nonneg,le_max_right _ _,hD,hdom,?_⟩
  intro p hp hp₀ r A hr hz hw hA hparams
  constructor
  · have hh := hLip.dist_le_mul p hp (rawNullOriginal p) hp₀
    rw [dist_eq_norm,dist_eq_norm] at hh
    exact (hh.trans (mul_le_mul_of_nonneg_left
      (rawNullOriginal_diff hA hw hparams) C.coe_nonneg)).trans_eq (by ring)
  constructor
  · exact (hB p hp).trans (le_max_left _ _)
  · apply hcurv p.1
      (Metric.thickening_subset_cthickening ε (nr '' K) (hsub hp).2)
      (Metric.thickening_subset_cthickening ε (nr '' K) (hsub hp₀).2)
      r A hr hz hw hA
    exact hparams 1 (by decide)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma rawSmallNull_difference {p : RawNullInput} {r : ℝ}
    (hr : 0 < r) (hz : rz p.1=1/r) (hp : p ∈ rawNullDomain)
    (hp₀ : rawNullOriginal p ∈ rawNullDomain) :
    coordinateSmallNull (rawNullMap p) r-coordinateSmallNull (rawNullMap (rawNullOriginal p)) r-
      2*rwgt p.1/(r^3*Real.sqrt r) =
    (nullResidual (rawNullMap p)-nullResidual (rawNullMap (rawNullOriginal p)))/r^4-
      2*rwgt p.1*((rawD p.1).1/nullD (rawMomentumInput p.1))/(r^6*Real.sqrt r)+
      (scalarCurvature (scalarMatrixToJet (rawQ p.1))-
        scalarCurvature (scalarMatrixToJet (rawQ (rawOriginal p.1))))/(2*r^2) := by
  have hz₀ : mz (nP (rawNullMap (rawNullOriginal p))) = 1/r := by
    change rz (rawOriginal p.1) = 1/r
    rw [rawOriginal_z,hz]
  rw [coordinateSmallNull_factor hr hz (rawNullMap_regular hp),
    coordinateSmallNull_factor hr hz₀ (rawNullMap_regular hp₀)]
  have hw₀ : mw (nP (rawNullMap (rawNullOriginal p))) = 0 := rawOriginal_w p.1
  rw [hw₀]
  have hd : nullD (rawMomentumInput p.1) = 1+(1/r)^3*(rawD p.1).1 := by
    change 1+rz p.1^3*(rawD p.1).1 = _
    rw [hz]
  have hd0 : nullD (rawMomentumInput p.1) ≠ 0 := (rawNullMap_regular hp).2
  change 2*rwgt p.1/(r^3*Real.sqrt r)/nullD (rawMomentumInput p.1)+
    (scalarCurvature (scalarMatrixToJet (rawQ p.1))/2-1)/r^2+
    nullResidual (rawNullMap p)/r^4-
    (2*0/(r^3*Real.sqrt r)/nullD (rawMomentumInput (rawOriginal p.1))+
      (scalarCurvature (scalarMatrixToJet (rawQ (rawOriginal p.1)))/2-1)/r^2+
      nullResidual (rawNullMap (rawNullOriginal p))/r^4)-2*rwgt p.1/(r^3*Real.sqrt r) = _
  have hpad : 2*rwgt p.1/(r^3*Real.sqrt r)/nullD (rawMomentumInput p.1)-
      2*rwgt p.1/(r^3*Real.sqrt r) =
      -2*rwgt p.1*((rawD p.1).1/nullD (rawMomentumInput p.1))/(r^6*Real.sqrt r) := by
    rw [hd] at hd0 ⊢
    have hd1 : r^3+(rawD p.1).1 ≠ 0 := by
      intro he
      apply hd0
      field_simp [hr.ne']
      simpa using he
    field_simp [hr.ne',hd1]
    ring
  linear_combination hpad

theorem raw_weighted_small_null {K : Set RawNullInput} (hK : IsCompact K)
    (hreg : K ⊆ rawNullDomain) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ p : RawNullInput, p ∈ Metric.cthickening δ K →
      rawNullOriginal p ∈ Metric.cthickening δ K →
      ∀ r A : ℝ, 1 ≤ r → rz p.1=1/r → 0 ≤ rwgt p.1 → 0 ≤ A →
      (∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) →
      |coordinateSmallNull (rawNullMap p) r-coordinateSmallNull (rawNullMap (rawNullOriginal p)) r-
        2*rwgt p.1/(r^3*Real.sqrt r)| ≤ C*(A+1)*rwgt p.1/r^4 := by
  obtain ⟨δ,hδ,C,B,D,hC,hB,hD,hdom,hest⟩ := raw_null_uniform hK hreg
  refine ⟨δ,hδ,C+2*B+D,by positivity,?_⟩
  intro p hp hp₀ r A hr hz hw hA hparams
  obtain ⟨hx,hy,hz'⟩ := hest p hp hp₀ r A hr hz hw hA hparams
  have hr0 : 0 < r := by linarith
  rw [rawSmallNull_difference hr0 hz (hdom hp) (hdom hp₀)]
  apply (smallNull_remainders_bound hr hw hA hC hB hD hx hy hz').trans
  apply div_le_div_of_nonneg_right _ (pow_nonneg hr0.le 4)
  apply mul_le_mul_of_nonneg_right _ hw
  nlinarith

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def rawNullZeroRadius (p : RawNullInput) : RawNullInput := (rawZeroRadius p.1,p.2)
def rawReferenceFamily (K : Set MatrixScalarJet) (B : ℝ) : Set RawNullInput :=
  {p | rmat p.1 0 ∈ K ∧ rz p.1 = 0} ∩ Metric.closedBall 0 B
lemma rawReferenceFamily_compact {K : Set MatrixScalarJet} (hK : IsCompact K) (B : ℝ) :
    IsCompact (rawReferenceFamily K B) := by
  let : FiniteDimensional ℝ RawMetricData := inferInstance
  let : FiniteDimensional ℝ RawTensorData := inferInstance
  let : FiniteDimensional ℝ RawCollarData := inferInstance
  let : FiniteDimensional ℝ RawCollarInput := inferInstance
  let : FiniteDimensional ℝ RawNullInput := inferInstance
  let : ProperSpace RawNullInput := FiniteDimensional.proper ℝ RawNullInput
  exact (isCompact_closedBall (0:RawNullInput) B).inter_left
    ((hK.isClosed.preimage (by fun_prop)).inter (isClosed_eq (by fun_prop) continuous_const))
lemma rawReferenceFamily_regular {K : Set MatrixScalarJet}
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1) ≠ 0) (B : ℝ) :
    rawReferenceFamily K B ⊆ rawNullDomain := by
  intro p hp
  exact rawDomain_at_zero hp.1.2 (hreg _ hp.1.1)

lemma rawOriginal_norm (p : RawCollarInput) : ‖rawOriginal p‖ ≤ ‖p‖ := by
  apply norm_prod_le_iff.mpr
  refine ⟨?_,?_⟩
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    by_cases hi : i=0
    · subst i
      exact (norm_le_pi_norm p.1 0).trans (norm_fst_le p)
    · simp only [rawOriginal,hi,ite_false,norm_zero]
      exact norm_nonneg p
  · exact norm_snd_le p
lemma rawZeroRadius_norm (p : RawCollarInput) : ‖rawZeroRadius p‖ ≤ ‖p‖ := by
  apply norm_prod_le_iff.mpr
  refine ⟨?_,norm_snd_le p⟩
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  by_cases hi : i=0
  · simp only [rawZeroRadius,hi,ite_true,norm_zero]
    exact norm_nonneg p
  · simp only [rawZeroRadius,hi,ite_false]
    exact (norm_le_pi_norm p.1 i).trans (norm_fst_le p)
lemma rawNullOriginal_norm (p : RawNullInput) : ‖rawNullOriginal p‖ ≤ ‖p‖ :=
  norm_prod_le_iff.mpr ⟨(rawOriginal_norm p.1).trans (norm_fst_le p),norm_snd_le p⟩
lemma rawNullZeroRadius_norm (p : RawNullInput) : ‖rawNullZeroRadius p‖ ≤ ‖p‖ :=
  norm_prod_le_iff.mpr ⟨(rawZeroRadius_norm p.1).trans (norm_fst_le p),norm_snd_le p⟩
lemma rawNullZeroRadius_close (p : RawNullInput) :
    dist p (rawNullZeroRadius p) ≤ |rz p.1| := by
  change max (dist p.1 (rawZeroRadius p.1)) (dist p.2 p.2) ≤ _
  rw [max_le_iff,dist_self]
  exact ⟨rawZeroRadius_dist p.1,abs_nonneg _⟩
lemma rawNullZeroRadius_mem {K : Set MatrixScalarJet} {B : ℝ} {p : RawNullInput}
    (hq : rmat p.1 0 ∈ K) (hp : ‖p‖ ≤ B) :
    rawNullZeroRadius p ∈ rawReferenceFamily K B := by
  refine ⟨⟨hq,rawZeroRadius_z _⟩,?_⟩
  simpa only [Metric.mem_closedBall,dist_zero_right] using (rawNullZeroRadius_norm p).trans hp
lemma raw_reference_tube {K : Set MatrixScalarJet} {B δ : ℝ} {p : RawNullInput}
    (hq : rmat p.1 0 ∈ K) (hp : ‖p‖ ≤ B) (hz : |rz p.1| ≤ δ) :
    p ∈ Metric.cthickening δ (rawReferenceFamily K B) ∧
    rawNullOriginal p ∈ Metric.cthickening δ (rawReferenceFamily K B) := by
  constructor
  · exact Metric.mem_cthickening_of_dist_le p (rawNullZeroRadius p) δ _
      (rawNullZeroRadius_mem hq hp) ((rawNullZeroRadius_close p).trans hz)
  · apply Metric.mem_cthickening_of_dist_le (rawNullOriginal p)
      (rawNullZeroRadius (rawNullOriginal p)) δ _
      (rawNullZeroRadius_mem hq ((rawNullOriginal_norm p).trans hp))
    exact (rawNullZeroRadius_close _).trans (by simpa only [rawNullOriginal,rawOriginal_z] using hz)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma rawRatioResidual_smooth {p : RawNullInput} (hp : p ∈ rawNullDomain) :
    ContDiffAt ℝ ∞ (fun p => ratioResidual (rawMomentumInput p.1)) p := by
  exact (ratioResidual_smooth (rawNullMap_regular hp)).comp p
    ((rawMomentumInput_smooth hp.1 hp.2.1).comp p (by fun_prop))

lemma raw_ratio_uniform {K : Set RawNullInput} (hK : IsCompact K)
    (hreg : K ⊆ rawNullDomain) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ p : RawNullInput, p ∈ Metric.cthickening δ K →
      rawNullOriginal p ∈ Metric.cthickening δ K →
      ∀ r A : ℝ, 1 ≤ r → rz p.1 = 1/r → 0 ≤ rwgt p.1 → 0 ≤ A →
      (∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) →
      |nullRatio (rawMomentumInput p.1)-1| ≤ (1+B)/r^2 ∧
      |nullRatio (rawMomentumInput p.1)-nullRatio (rawMomentumInput (rawOriginal p.1))| ≤
        C*A*rwgt p.1/r^3 := by
  let : FiniteDimensional ℝ RawMetricData := inferInstance
  let : FiniteDimensional ℝ RawTensorData := inferInstance
  let : FiniteDimensional ℝ RawCollarData := inferInstance
  let : FiniteDimensional ℝ RawCollarInput := inferInstance
  let : FiniteDimensional ℝ RawNullInput := inferInstance
  let : ProperSpace RawNullInput := FiniteDimensional.proper ℝ RawNullInput
  obtain ⟨δ,hδ,hdom⟩ := hK.exists_cthickening_subset_open rawNullDomain_open hreg
  have hk := hK.cthickening (r:=δ)
  obtain ⟨C,hLip⟩ : ∃ C, LipschitzOnWith C (fun p => ratioResidual (rawMomentumInput p.1))
      (Metric.cthickening δ K) := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hk
    intro p hp
    obtain ⟨C,t,ht,hC⟩ := ((rawRatioResidual_smooth (hdom hp)).of_le
      (by simp : (1:ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
    exact ⟨C,t,mem_nhdsWithin_of_mem_nhds ht,hC⟩
  obtain ⟨B,hB⟩ := hk.exists_bound_of_continuousOn
    (fun p hp => (rawRatioResidual_smooth (hdom hp)).continuousAt.continuousWithinAt)
  refine ⟨δ,hδ,C,max B 0,C.coe_nonneg,le_max_right _ _,?_⟩
  intro p hp hp₀ r A hr hz hw hA hparams
  refine ⟨nullRatio_bound (rawNullMap_regular (hdom hp)) hr hz
    (le_max_right _ _) ((hB p hp).trans (le_max_left _ _)),?_⟩
  have he : mz (rawMomentumInput p.1) = mz (rawMomentumInput (rawOriginal p.1)) :=
    (rawOriginal_z p.1).symm
  erw [nullRatio_difference (rawNullMap_regular (hdom hp))
    (rawNullMap_regular (hdom hp₀)) he]
  have hz' : mz (rawMomentumInput p.1) = 1/r := hz
  erw [hz',abs_mul,abs_of_nonneg (by positivity : 0 ≤ (1/r)^3)]
  have hh := hLip.dist_le_mul p hp (rawNullOriginal p) hp₀
  rw [dist_eq_norm,dist_eq_norm] at hh
  have hb := hh.trans (mul_le_mul_of_nonneg_left (rawNullOriginal_diff hA hw hparams) C.coe_nonneg)
  exact (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (1/r)^3)).trans_eq (by ring)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma inverse_radius_threshold {δ r : ℝ} (hδ : 0 < δ) (hr : max 1 (1/δ) ≤ r) :
    1 ≤ r ∧ |1/r| ≤ δ := by
  have hr1 := (le_max_left 1 (1/δ)).trans hr
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  refine ⟨hr1,?_⟩
  rw [abs_of_pos (one_div_pos.mpr hr0)]
  apply (div_le_iff₀ hr0).mpr
  simpa only [mul_comm] using ((div_le_iff₀ hδ).mp ((le_max_right _ _).trans hr))

theorem bounded_raw_small_null {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1) ≠ 0) (B : ℝ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ p : RawNullInput, rmat p.1 0 ∈ K → ‖p‖ ≤ B →
      ∀ r A : ℝ, R₀ ≤ r → rz p.1=1/r → 0 ≤ rwgt p.1 → 0 ≤ A →
      (∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) →
      |coordinateSmallNull (rawNullMap p) r-coordinateSmallNull (rawNullMap (rawNullOriginal p)) r-
        2*rwgt p.1/(r^3*Real.sqrt r)| ≤ C*(A+1)*rwgt p.1/r^4 := by
  obtain ⟨δ,hδ,C,hC,hh⟩ := raw_weighted_small_null (rawReferenceFamily_compact hK B)
    (rawReferenceFamily_regular hreg B)
  refine ⟨max 1 (1/δ),le_max_left _ _,C,hC,?_⟩
  intro p hq hp r A hr hz hw hA hparams
  obtain ⟨hr1,hd⟩ := inverse_radius_threshold hδ hr
  obtain ⟨hp',hp₀'⟩ := raw_reference_tube hq hp (by simpa only [hz] using hd)
  exact hh p hp' hp₀' r A hr1 hz hw hA hparams

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma raw_projected_reference_tube {K : Set MatrixScalarJet} {B δ : ℝ} {p : RawNullInput}
    (hq : rmat p.1 0 ∈ K) (hp : ‖p‖ ≤ B) (hz : |rz p.1| ≤ δ) :
    p.1 ∈ Metric.cthickening δ (nr '' rawReferenceFamily K B) ∧
    rawOriginal p.1 ∈ Metric.cthickening δ (nr '' rawReferenceFamily K B) := by
  constructor
  · exact Metric.mem_cthickening_of_dist_le p.1 (rawZeroRadius p.1) δ _
      ⟨rawNullZeroRadius p,rawNullZeroRadius_mem hq hp,rfl⟩ ((rawZeroRadius_dist p.1).trans hz)
  · exact Metric.mem_cthickening_of_dist_le (rawOriginal p.1)
      (rawZeroRadius (rawOriginal p.1)) δ _
      ⟨rawNullZeroRadius (rawNullOriginal p),
        rawNullZeroRadius_mem hq ((rawNullOriginal_norm p).trans hp),rfl⟩
      ((rawZeroRadius_dist _).trans (by simpa only [rawOriginal_z] using hz))

theorem bounded_raw_momentum {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1) ≠ 0) (B : ℝ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ p : RawNullInput, rmat p.1 0 ∈ K → ‖p‖ ≤ B →
      ∀ r A : ℝ, R₀ ≤ r → rz p.1=1/r → 0 ≤ rwgt p.1 → 0 ≤ A →
      (∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) →
      |coordinateQ (rawMomentumInput (rawOriginal p.1))| ≤ D/r^3 ∧
      |coordinateQ (rawMomentumInput p.1)-coordinateQ (rawMomentumInput (rawOriginal p.1))-
        normalizedMean (rawMomentumInput p.1)*rwgt p.1/r^2| ≤ C*A*rwgt p.1/r^3 ∧
      |coordinateQ (rawMomentumInput p.1)-coordinateQ (rawMomentumInput (rawOriginal p.1))-
        2*rwgt p.1/r^2| ≤ (C*A+D)*rwgt p.1/r^3 ∧
      (∀ a, |coordinateZ (rawMomentumInput (rawOriginal p.1)) a| ≤ D/r^2) ∧
      (∀ a, |coordinateZ (rawMomentumInput p.1) a-
        coordinateZ (rawMomentumInput (rawOriginal p.1)) a| ≤ C*A*rwgt p.1/r^2) ∧
      |normalizedMean (rawMomentumInput p.1)-2| ≤ D/r^2 := by
  have hfamily := (rawReferenceFamily_compact hK B).image (show Continuous nr from by fun_prop)
  have hregular : nr '' rawReferenceFamily K B ⊆ rawDomain := by
    rintro _ ⟨p,hp,rfl⟩
    exact rawReferenceFamily_regular hreg B hp
  obtain ⟨δ,hδ,C,D,hC,hD,hh⟩ := raw_weighted_momentum hfamily hregular
  refine ⟨max 1 (1/δ),le_max_left _ _,C,D,hC,hD,?_⟩
  intro p hq hp r A hr hz hw hA hparams
  obtain ⟨hr1,hd⟩ := inverse_radius_threshold hδ hr
  obtain ⟨hp',hp₀'⟩ := raw_projected_reference_tube hq hp (by simpa only [hz] using hd)
  exact hh p.1 hp' hp₀' r A hr1 hz hw hA hparams

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

theorem bounded_raw_ratio {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1) ≠ 0) (B : ℝ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ p : RawNullInput, rmat p.1 0 ∈ K → ‖p‖ ≤ B →
      ∀ r A : ℝ, R₀ ≤ r → rz p.1=1/r → 0 ≤ rwgt p.1 → 0 ≤ A →
      (∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) →
      |nullRatio (rawMomentumInput p.1)-1| ≤ D/r^2 ∧
      |nullRatio (rawMomentumInput p.1)-nullRatio (rawMomentumInput (rawOriginal p.1))| ≤
        C*A*rwgt p.1/r^3 := by
  obtain ⟨δ,hδ,C,D,hC,hD,hh⟩ := raw_ratio_uniform (rawReferenceFamily_compact hK B)
    (rawReferenceFamily_regular hreg B)
  refine ⟨max 1 (1/δ),le_max_left _ _,C,1+D,hC,by positivity,?_⟩
  intro p hq hp r A hr hz hw hA hparams
  obtain ⟨hr1,hd⟩ := inverse_radius_threshold hδ hr
  obtain ⟨hp',hp₀'⟩ := raw_reference_tube hq hp (by simpa only [hz] using hd)
  exact hh p hp' hp₀' r A hr1 hz hw hA hparams

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

theorem bounded_raw_CQ {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1) ≠ 0) (B A : ℝ) (hA : 0 ≤ A) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ p : RawNullInput, rmat p.1 0 ∈ K → ‖p‖ ≤ B →
      ∀ r : ℝ, R₀ ≤ r → rz p.1=1/r → 0 ≤ rwgt p.1 →
      (∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) →
      |coordinateQ (rawMomentumInput (rawOriginal p.1))| ≤ D/r^3 ∧
      |coordinateQ (rawMomentumInput p.1)-coordinateQ (rawMomentumInput (rawOriginal p.1))-
        2*rwgt p.1/r^2| ≤ C*rwgt p.1/r^3 ∧
      |(coordinateEnergy (rawNullMap p) r-coordinateEnergy (rawNullMap (rawNullOriginal p)) r)-
          (coordinateQ (rawMomentumInput p.1)-coordinateQ (rawMomentumInput (rawOriginal p.1)))-
        2*rwgt p.1/(r^3*Real.sqrt r)| ≤ C*rwgt p.1/r^4 ∧
      (∀ a, |coordinateZ (rawMomentumInput (rawOriginal p.1)) a| ≤ D/r^2) ∧
      (∀ a, |coordinateZ (rawMomentumInput p.1) a-
        coordinateZ (rawMomentumInput (rawOriginal p.1)) a| ≤ C*rwgt p.1/r^2) := by
  obtain ⟨R₁,hR₁,S,hS,hsmall⟩ := bounded_raw_small_null hK hreg B
  obtain ⟨R₂,hR₂,M,N,hM,hN,hmom⟩ := bounded_raw_momentum hK hreg B
  obtain ⟨R₃,hR₃,T,U,hT,hU,hratio⟩ := bounded_raw_ratio hK hreg B
  let C : ℝ := S*(A+1)+U*(2+(M*A+N))+T*A*N+(M*A+N)+M*A
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp₁ : 0 ≤ S*(A+1) := by positivity
  have hp₂ : 0 ≤ U*(2+(M*A+N)) := by positivity
  have hp₃ : 0 ≤ T*A*N := by positivity
  have hp₄ : 0 ≤ M*A := mul_nonneg hM hA
  have hC₁ : M*A+N ≤ C := by dsimp [C]; linarith
  have hC₂ : S*(A+1)+U*(2+(M*A+N))+T*A*N ≤ C := by
    dsimp [C]; have := mul_nonneg hM hA; linarith
  have hC₃ : M*A ≤ C := le_trans (by linarith) hC₁
  refine ⟨max R₁ (max R₂ R₃),hR₁.trans (le_max_left _ _),C,N,hC,hN,?_⟩
  intro p hq hp r hr hz hw hparams
  have hr₁ : R₁ ≤ r := (le_max_left _ _).trans hr
  have hr₂ : R₂ ≤ r := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hr
  have hr₃ : R₃ ≤ r := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hr
  have hr0 : 1 ≤ r := hR₁.trans hr₁
  have hsmall' := hsmall p hq hp r A hr₁ hz hw hA hparams
  obtain ⟨hq₀,hdq,hdq',hz₀,hdz,hmean⟩ := hmom p hq hp r A hr₂ hz hw hA hparams
  obtain ⟨ha,hda⟩ := hratio p hq hp r A hr₃ hz hw hA hparams
  have hCQ := smallNull_to_CQ hr0 hw (mul_nonneg hS (by positivity))
    (show 0 ≤ M*A+N by positivity) hU (mul_nonneg hT hA) hN
    hsmall' hdq' hq₀ ha hda
  refine ⟨hq₀,hdq'.trans ?_,hCQ.trans ?_,hz₀,fun a => (hdz a).trans ?_⟩
  · gcongr
  · change (S*(A+1)+U*(2+(M*A+N))+(T*A)*N)*rwgt p.1/r^4 ≤ C*rwgt p.1/r^4
    gcongr
  · gcongr

end
end CKSAngularGeometry

end

end OAI
end

theorem solution : type_of% @OAI.CKSAngularGeometry.bounded_raw_CQ := @OAI.CKSAngularGeometry.bounded_raw_CQ
