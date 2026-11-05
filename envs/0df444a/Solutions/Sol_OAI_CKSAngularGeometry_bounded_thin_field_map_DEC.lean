-- Prove2me | solution 1 for OAI.CKSAngularGeometry.bounded_thin_field_map_DEC
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:17:43.363423+00:00
-- url     : https://prove2.me/submissions/78f2115b-4cfe-4683-a7af-3196775f8a04

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport
import Theorems.Thm_OAI_CKSAngularGeometry_bounded_raw_CQ

set_option linter.all false

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev CombinedJet := Jet × ScalarJet

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

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSCalculus
noncomputable section
open Filter Set
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma D_const (e x : E) (c : ℝ) : D e (fun _ => c) x = 0 := by simp [D]

lemma D_D_const (e w x : E) (c : ℝ) : D w (D e (fun _ => c)) x = 0 := by
  have h : D e (fun _ : E => c) = fun _ => 0 := funext (fun y => D_const e y c)
  rw [h, D_const]

end
end CKSCalculus

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

lemma actualScalarJet_const (c : ℝ) (x : Point) : actualScalarJet (fun _ => c) x = constantJet c := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext a; exact D_const _ _ _
  · ext a b; exact D_D_const _ _ _ _

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
namespace CKSEnd
noncomputable section


section Cone

variable {E E₀ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]

def DEC (C Q : ℝ) (Z : E) : Prop := Real.sqrt (Q ^ 2 + ‖Z‖ ^ 2) ≤ C

omit [NormedSpace ℝ E] in
lemma momentum_norm [NormedSpace ℝ E] (Q : ℝ) (Z : E) :
    ‖(WithLp.toLp 2 (Q, Z) : WithLp 2 (ℝ × E))‖ =
      Real.sqrt (Q ^ 2 + ‖Z‖ ^ 2) := by
  simp [WithLp.prod_norm_eq_of_L2, Real.norm_eq_abs]

lemma DEC.add {C₀ Q₀ C₁ Q₁ : ℝ} {Z₀ Z₁ : E}
    (h₀ : DEC C₀ Q₀ Z₀) (h₁ : DEC C₁ Q₁ Z₁) :
    DEC (C₀ + C₁) (Q₀ + Q₁) (Z₀ + Z₁) := by
  let V₀ : WithLp 2 (ℝ × E) := WithLp.toLp 2 (Q₀, Z₀)
  let V₁ : WithLp 2 (ℝ × E) := WithLp.toLp 2 (Q₁, Z₁)
  have hn := norm_add_le V₀ V₁
  change ‖(WithLp.toLp 2 (Q₀ + Q₁, Z₀ + Z₁) : WithLp 2 (ℝ × E))‖ ≤
    ‖V₀‖ + ‖V₁‖ at hn
  rw [momentum_norm, momentum_norm, momentum_norm] at hn
  exact hn.trans (add_le_add h₀ h₁)

omit [NormedSpace ℝ E] in
lemma DEC.of_null_margins [NormedSpace ℝ E] {C Q a b : ℝ} {Z : E}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hm : a ≤ C - Q) (hp : b ≤ C + Q)
    (hz : ‖Z‖ ^ 2 ≤ a * b) : DEC C Q Z := by
  have hC : 0 ≤ C := by linarith
  have hmul := mul_le_mul hm hp hb (ha.trans hm)
  apply (Real.sqrt_le_iff).2
  constructor
  · exact hC
  · nlinarith

lemma DEC.after_common_norm {C Q C₀ Q₀ a b : ℝ} {Z : E} {Z₀ : E₀}
    (I : E₀ →ₗᵢ[ℝ] E) (h₀ : DEC C₀ Q₀ Z₀)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hm : a ≤ (C - C₀) - (Q - Q₀))
    (hp : b ≤ (C - C₀) + (Q - Q₀))
    (hz : ‖Z - I Z₀‖ ^ 2 ≤ a * b) : DEC C Q Z := by
  have h₀' : DEC C₀ Q₀ (I Z₀) := by simpa [DEC] using h₀
  have hδ := DEC.of_null_margins ha hb hm hp hz
  have h := h₀'.add hδ
  simpa using h

def smallMargin (r w : ℝ) : ℝ := w / (r ^ 3 * Real.sqrt r)

def largeMargin (r w : ℝ) : ℝ := w / r ^ 2

theorem collar_DEC_of_weighted_errors
    {C Q C₀ Q₀ r w A B C₁ : ℝ} {Z : E} {Z₀ : E₀}
    (I : E₀ →ₗᵢ[ℝ] E) (h₀ : DEC C₀ Q₀ Z₀)
    (hr : 1 ≤ r) (hw : 0 ≤ w) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC₁ : 0 ≤ C₁)
    (hAr : A ^ 2 ≤ r) (hBr : B ≤ r) (hC₁r : C₁ ^ 4 ≤ r)
    (hsmall : |((C - C₀) - (Q - Q₀)) - 2 * smallMargin r w| ≤ A * w / r ^ 4)
    (hlarge : |(Q - Q₀) - 2 * largeMargin r w| ≤ B * w / r ^ 3)
    (htan : ‖Z - I Z₀‖ ≤ C₁ * w / r ^ 3) :
    DEC C Q Z := by
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hs2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0.le
  have hAs : A ≤ Real.sqrt r := by nlinarith
  have hCs : C₁ ^ 2 ≤ Real.sqrt r := by nlinarith [sq_nonneg (C₁ ^ 2 - Real.sqrt r)]
  have hsmallerr : A * w / r ^ 4 ≤ smallMargin r w := by
    calc
      A * w / r ^ 4 ≤ Real.sqrt r * w / r ^ 4 := by gcongr
      _ = smallMargin r w := by
        unfold smallMargin
        field_simp
        nlinarith [hs2]
  have hlargeerr : B * w / r ^ 3 ≤ largeMargin r w := by
    calc
      B * w / r ^ 3 ≤ r * w / r ^ 3 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBr hw)
          (pow_nonneg (hB.trans hBr) 3)
      _ = largeMargin r w := by unfold largeMargin; field_simp
  have ha : 0 ≤ smallMargin r w := by unfold smallMargin; positivity
  have hb : 0 ≤ largeMargin r w := by unfold largeMargin; positivity
  have hm : smallMargin r w ≤ (C - C₀) - (Q - Q₀) := by
    have := (abs_le.mp hsmall).1
    linarith
  have hq : largeMargin r w ≤ Q - Q₀ := by
    have := (abs_le.mp hlarge).1
    linarith
  have hp : largeMargin r w ≤ (C - C₀) + (Q - Q₀) := by linarith
  have hz : ‖Z - I Z₀‖ ^ 2 ≤ smallMargin r w * largeMargin r w := by
    calc
      ‖Z - I Z₀‖ ^ 2 ≤ (C₁ * w / r ^ 3) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _)
          (div_nonneg (mul_nonneg hC₁ hw) (pow_nonneg hr0.le 3))).2 htan
      _ = C₁ ^ 2 * w ^ 2 / r ^ 6 := by ring
      _ ≤ Real.sqrt r * w ^ 2 / r ^ 6 := by gcongr
      _ = smallMargin r w * largeMargin r w := by
        unfold smallMargin largeMargin
        field_simp
        nlinarith [hs2]
  exact DEC.after_common_norm I h₀ ha hb hm hp hz

end Cone

end
end CKSEnd

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
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise InnerProductSpace

abbrev AngularEuclidean := EuclideanSpace ℝ I

def covectorEmbedding (q : Mat) (E : I → ℝ) : AngularEuclidean :=
  WithLp.toLp 2 ![Real.sqrt (q 1 1/determinant q)*(E 0-q 0 1/q 1 1*E 1),
    E 1/Real.sqrt (q 1 1)]

lemma covectorEmbedding_smooth {q : Mat} {E : I → ℝ} (hq : positiveAngular q) :
    ContDiffAt ℝ ∞ (fun p : Mat × (I → ℝ) => covectorEmbedding p.1 p.2) (q,E) := by
  apply ((WithLp.linearEquiv 2 ℝ (I → ℝ)).symm.toContinuousLinearEquiv).contDiff.contDiffAt.comp (q,E)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ ∞ (fun p : Mat × (I → ℝ) =>
      Real.sqrt (p.1 1 1/determinant p.1)*(p.2 0-p.1 0 1/p.1 1 1*p.2 1)) (q,E)
    apply ContDiffAt.mul
    · exact ((by fun_prop : ContDiffAt ℝ ∞ (fun p : Mat × (I → ℝ) => p.1 1 1) (q,E)).div
        (determinant_smooth.contDiffAt.comp (q,E) (by fun_prop : ContDiffAt ℝ ∞ (fun p : Mat × (I → ℝ) => p.1) (q,E))) hq.2.ne').sqrt
          (div_pos hq.1 hq.2).ne'
    · apply (by fun_prop : ContDiffAt ℝ ∞ (fun p : Mat × (I → ℝ) => p.2 0) (q,E)).sub
      exact ((by fun_prop : ContDiffAt ℝ ∞ (fun p : Mat × (I → ℝ) => p.1 0 1) (q,E)).div
        (by fun_prop) hq.1.ne').mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun p : Mat × (I → ℝ) => p.2 1/Real.sqrt (p.1 1 1)) (q,E)
    exact (by fun_prop : ContDiffAt ℝ ∞ (fun p : Mat × (I → ℝ) => p.2 1) (q,E)).div
      ((by fun_prop : ContDiffAt ℝ ∞ (fun p : Mat × (I → ℝ) => p.1 1 1) (q,E)).sqrt hq.1.ne')
      (Real.sqrt_pos.mpr hq.1).ne'

lemma covectorEmbedding_linear (q : Mat) (c : ℝ) (E : I → ℝ) :
    covectorEmbedding q (c • E) = c • covectorEmbedding q E := by
  ext i
  fin_cases i <;> simp [covectorEmbedding] <;> ring

lemma covectorEmbedding_norm_sq {q : Mat} (hq : positiveAngular q) (hs : q 1 0=q 0 1)
    (E : I → ℝ) : ‖covectorEmbedding q E‖^2 = ∑ i, ∑ k, inverse q i k*E i*E k := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [covectorEmbedding,Fin.sum_univ_two,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,Real.norm_eq_abs,sq_abs]
  have hsqrt : Real.sqrt (q 1 1/determinant q)^2 = q 1 1/determinant q :=
    Real.sq_sqrt (div_pos hq.1 hq.2).le
  have hsqrt' : Real.sqrt (q 1 1)^2 = q 1 1 := Real.sq_sqrt hq.1.le
  rw [mul_pow,div_pow,hsqrt,hsqrt']
  simp only [inverse,hs]
  have hd : determinant q=q 0 0*q 1 1-q 0 1*q 0 1 := by simp [determinant,hs]
  field_simp [hq.1.ne',hq.2.ne']
  rw [hd]
  simp only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
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

lemma matrixScalarJets_norm_le_three (q : Point → Mat) (x : Point) :
    ‖matrixScalarJets q x‖ ≤ ‖matrixThreeJets q x‖ := by
  apply (Matrix.norm_le_iff (norm_nonneg _)).mpr
  intro i k
  exact (norm_fst_le (matrixThreeJets q x i k)).trans
    (Matrix.norm_entry_le_entrywise_sup_norm (matrixThreeJets q x))

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

lemma tensorDiv_rescale (q : Jet) (T : CovariantTensorJet) {c : ℝ} (hc : c ≠ 0) (d : ℝ) (a : I) :
    tensorDiv (rescale c q) (d • T) a = (d/c)*tensorDiv q T a := by
  simp only [tensorDiv,inverse_rescale c q hc,christoffel_rescale c q hc,
    Pi.smul_apply,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Fin.sum_univ_two]
  ring
lemma covectorPair_rescale (q : Jet) (E B : I → ℝ) {c : ℝ} (hc : c ≠ 0) (d e : ℝ) :
    covectorPair (rescale c q) (d • E) (e • B) = (d*e/c)*covectorPair q E B := by
  simp only [covectorPair,inverse_rescale c q hc,Pi.smul_apply,smul_eq_mul,Fin.sum_univ_two]
  ring

lemma covectorLie_smul (S E : CovectorJet) (c d : ℝ) (a : I) :
    covectorLie (c • S) (d • E) a = c*d*covectorLie S E a := by
  simp only [covectorLie,Pi.smul_apply,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Fin.sum_univ_two]
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

def rawZeroRadius (p : RawCollarInput) : RawCollarInput := (fun i => if i=0 then 0 else p.1 i,p.2)

lemma rawOriginal_z (p : RawCollarInput) : rz (rawOriginal p) = rz p := by simp [rawOriginal,rz]

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

abbrev nr (p : RawNullInput) := p.1

def rawNullDomain : Set RawNullInput := nr ⁻¹' rawDomain
lemma rawNullDomain_open : IsOpen rawNullDomain := rawDomain_open.preimage (by fun_prop)

lemma rawNullOriginal_diff {p : RawNullInput} {A : ℝ} (hA : 0 ≤ A)
    (hw : 0 ≤ rwgt p.1) (hparams : ∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) :
    ‖p-rawNullOriginal p‖ ≤ A*rwgt p.1 := by
  apply norm_prod_le_iff.mpr
  refine ⟨rawOriginal_difference hA hw hparams,?_⟩
  change ‖p.2-p.2‖ ≤ _
  rw [sub_self,norm_zero]
  exact mul_nonneg hA hw

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

def thinTensor (t : RawTensorData) : RawTensorData :=
  (((fun i => if i=3 then constantJet (t.1.1 i).1 else t.1.1 i),t.1.2),t.2)
def thinRaw (p : RawNullInput) : RawNullInput :=
  ((p.1.1,(p.1.2.1,thinTensor p.1.2.2)),p.2)

lemma thinQ (p : RawNullInput) : rawQ (thinRaw p).1=rawQ p.1 := rfl
lemma thinC (p : RawNullInput) : rawC (thinRaw p).1=rawC p.1 := rfl
lemma thinD (p : RawNullInput) : rawD (thinRaw p).1=rawD p.1 := rfl
lemma thinT (p : RawNullInput) : rawT (thinRaw p).1=rawT p.1 := rfl
lemma thinF (p : RawNullInput) : rawF (thinRaw p).1=rawF p.1 := rfl
lemma thinL (p : RawNullInput) : rawL (thinRaw p).1=rawL p.1 := rfl
lemma thinTr (p : RawNullInput) : (rawTr (thinRaw p).1).1=(rawTr p.1).1 := rfl
lemma thinA (p : RawNullInput) : rawA (thinRaw p).1=rawA p.1 := by
  unfold rawA rawLapseInput
  rw [thinT,thinF,thinD]
  rfl
lemma thinX (p : RawNullInput) : rawX (thinRaw p).1=rawX p.1 := by
  funext i k
  unfold rawX rawLambda
  rw [thinA,thinQ,thinC]
  rfl
attribute [local irreducible] rawA rawX rawQ rawD rawT rawL rawF rawTr

lemma thin_mz (p : RawNullInput) : mz (nP (rawNullMap (thinRaw p)))=mz (nP (rawNullMap p)) := by
  simp only [mz,nP,rawNullMap,rawMomentumInput,rz,thinRaw]
lemma thin_mw (p : RawNullInput) : mw (nP (rawNullMap (thinRaw p)))=mw (nP (rawNullMap p)) := by
  simp only [mw,nP,rawNullMap,rawMomentumInput,rwgt,thinRaw]
lemma thin_mq (p : RawNullInput) : mq (nP (rawNullMap (thinRaw p)))=mq (nP (rawNullMap p)) := by
  simp only [mq,nP,rawNullMap,rawMomentumInput]
  rw [thinQ]
lemma thin_mS (p : RawNullInput) : mS (nP (rawNullMap (thinRaw p)))=mS (nP (rawNullMap p)) := by
  simp only [mS,nP,rawNullMap,rawMomentumInput,rawS,re,rshift,thinRaw]
lemma thin_mE (p : RawNullInput) : mE (nP (rawNullMap (thinRaw p)))=mE (nP (rawNullMap p)) := by
  simp only [mE,nP,rawNullMap,rawMomentumInput,re,reta,thinRaw,thinTensor]
lemma thin_mT (p : RawNullInput) : mT (nP (rawNullMap (thinRaw p)))=mT (nP (rawNullMap p)) := by
  simp only [mT,nP,rawNullMap,rawMomentumInput]
  change (1-re p.1) • traceFreeJet (rawQ (thinRaw p).1) (rtau p.1) =
    (1-re p.1) • traceFreeJet (rawQ p.1) (rtau p.1)
  rw [thinQ]
lemma thin_mEr (p : RawNullInput) : mEr (nP (rawNullMap (thinRaw p)))=mEr (nP (rawNullMap p)) := by
  simp only [mEr,nP,rawNullMap,rawMomentumInput,re,retar,reta,rθ,thinRaw,thinTensor]
lemma thin_mX (p : RawNullInput) : mX (nP (rawNullMap (thinRaw p)))=mX (nP (rawNullMap p)) := by
  simp only [mX,nP,rawNullMap,rawMomentumInput]
  exact thinX p
lemma thin_mc0 (p : RawNullInput) : mc (nP (rawNullMap (thinRaw p))) 0=mc (nP (rawNullMap p)) 0 := by
  simp only [mc,nP,rawNullMap,rawMomentumInput,Matrix.cons_val_zero]
  exact thinA p
lemma thin_mc1 (p : RawNullInput) : mc (nP (rawNullMap (thinRaw p))) 1=mc (nP (rawNullMap p)) 1 := by
  simp only [mc,nP,rawNullMap,rawMomentumInput,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact thinT p
lemma thin_mc2 (p : RawNullInput) : mc (nP (rawNullMap (thinRaw p))) 2=mc (nP (rawNullMap p)) 2 := by
  simp only [mc,nP,rawNullMap,rawMomentumInput]
  exact thinL p
lemma thin_mc4 (p : RawNullInput) : mc (nP (rawNullMap (thinRaw p))) 4=mc (nP (rawNullMap p)) 4 := by
  simp only [mc,nP,rawNullMap,rawMomentumInput]
  exact thinD p
lemma thin_mc3 (p : RawNullInput) : (mc (nP (rawNullMap (thinRaw p))) 3).1=(mc (nP (rawNullMap p)) 3).1 := by
  simp only [mc,nP,rawNullMap,rawMomentumInput]
  exact thinTr p
lemma thin_nF (p : RawNullInput) : nF (rawNullMap (thinRaw p))=nF (rawNullMap p) := by
  simp only [nF,rawNullMap]
  exact thinF p
lemma thin_nFr (p : RawNullInput) : nFr (rawNullMap (thinRaw p))=nFr (rawNullMap p) := by
  simp only [nFr,rawNullMap,re,rθ,thinRaw]

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
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise InnerProductSpace

def commonAngularMomentum (p : MomentumInput) : AngularEuclidean :=
  mz p • covectorEmbedding (mq p).1 (coordinateZ p)

def rawAngularResidual (p : RawNullInput) : AngularEuclidean :=
  covectorEmbedding (rawAngularMatrix p) (angularResidual (rawMomentumInput p.1))

def rawPositiveDomain : Set RawNullInput := rawNullDomain ∩ {p | positiveAngular (rawAngularMatrix p)}

lemma rawAngularMatrix_smooth : ContDiff ℝ ∞ rawAngularMatrix := by
  apply contDiff_pi.mpr; intro i
  apply contDiff_pi.mpr; intro k
  exact contDiff_fst.comp ((contDiff_pi.mp (contDiff_pi.mp rawQ_smooth i) k).comp (by fun_prop))

lemma rawPositiveDomain_open : IsOpen rawPositiveDomain := by
  apply rawNullDomain_open.inter
  apply IsOpen.inter
  · exact isOpen_lt continuous_const ((continuous_apply 1).comp ((continuous_apply 1).comp rawAngularMatrix_smooth.continuous))
  · exact isOpen_lt continuous_const (determinant_smooth.continuous.comp rawAngularMatrix_smooth.continuous)

lemma rawAngularResidual_smooth {p : RawNullInput} (hp : p ∈ rawPositiveDomain) :
    ContDiffAt ℝ ∞ rawAngularResidual p := by
  have hm := (rawMomentumInput_smooth hp.1.1 hp.1.2.1).comp p
    (by fun_prop : ContDiffAt ℝ ∞ nr p)
  have hz := (contDiffAt_snd.comp _ (momentumResidual_smooth hp.1.2.2)).comp p hm
  have he : ContDiffAt ℝ ∞ (fun x : Mat × Point => covectorEmbedding x.1 x.2)
      (rawAngularMatrix p,angularResidual (rawMomentumInput p.1)) := covectorEmbedding_smooth hp.2
  change ContDiffAt ℝ ∞ ((fun x : Mat × Point => covectorEmbedding x.1 x.2) ∘
    (fun p : RawNullInput => (rawAngularMatrix p,angularResidual (rawMomentumInput p.1)))) p
  exact he.comp p (rawAngularMatrix_smooth.contDiffAt.prodMk hz)

lemma commonAngularMomentum_factor {p : MomentumInput} (hz : mz p ≠ 0) :
    commonAngularMomentum p = mz p^3 • covectorEmbedding (mq p).1 (angularResidual p) := by
  have he : coordinateZ p = mz p^2 • angularResidual p := funext fun a => coordinateZ_factor hz a
  rw [commonAngularMomentum,he,covectorEmbedding_linear,smul_smul]
  congr 1
  ring

lemma rawPositiveFamily_regular {K : Set MatrixScalarJet}
    (hreg : ∀ q ∈ K, positiveAngular (fun i k => (q i k).1)) (B : ℝ) :
    rawReferenceFamily K B ⊆ rawPositiveDomain := by
  intro p hp
  refine ⟨rawReferenceFamily_regular (fun q hq => (hreg q hq).2.ne') B hp,?_⟩
  have he : rawAngularMatrix p = fun i k => (rmat p.1 0 i k).1 := by
    change (fun i k => ((rmat p.1 0 + (rz p.1^3*(1-re p.1)) • rmat p.1 1) i k).1) = _
    rw [hp.1.2]
    simp only [zero_pow (by decide : 3 ≠ 0),zero_mul,zero_smul,add_zero]
  change positiveAngular (rawAngularMatrix p)
  rw [he]
  exact hreg _ hp.1.1

theorem bounded_raw_common_angular {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, positiveAngular (fun i k => (q i k).1)) (B : ℝ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ p : RawNullInput, rmat p.1 0 ∈ K → ‖p‖ ≤ B →
      ∀ r A : ℝ, R₀ ≤ r → rz p.1=1/r → 0 ≤ rwgt p.1 → 0 ≤ A →
      (∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) →
      positiveAngular (rawAngularMatrix p) ∧ positiveAngular (rawAngularMatrix (rawNullOriginal p)) ∧
      ‖commonAngularMomentum (rawMomentumInput p.1)-
        commonAngularMomentum (rawMomentumInput (rawOriginal p.1))‖ ≤ C*A*rwgt p.1/r^3 := by
  let : FiniteDimensional ℝ RawMetricData := inferInstance
  let : FiniteDimensional ℝ RawTensorData := inferInstance
  let : FiniteDimensional ℝ RawCollarData := inferInstance
  let : FiniteDimensional ℝ RawCollarInput := inferInstance
  let : FiniteDimensional ℝ RawNullInput := inferInstance
  let : ProperSpace RawNullInput := FiniteDimensional.proper ℝ RawNullInput
  have hk := rawReferenceFamily_compact hK B
  obtain ⟨δ,hδ,hdom⟩ := hk.exists_cthickening_subset_open rawPositiveDomain_open (rawPositiveFamily_regular hreg B)
  obtain ⟨C,hLip⟩ : ∃ C, LipschitzOnWith C rawAngularResidual
      (Metric.cthickening δ (rawReferenceFamily K B)) := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (hk.cthickening (r:=δ))
    intro p hp
    obtain ⟨C,t,ht,hC⟩ := ((rawAngularResidual_smooth (hdom hp)).of_le
      (by simp : (1:ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
    exact ⟨C,t,mem_nhdsWithin_of_mem_nhds ht,hC⟩
  refine ⟨max 1 (1/δ),le_max_left _ _,C,C.coe_nonneg,?_⟩
  intro p hq hp r A hr hz hw hA hparams
  obtain ⟨hr1,hd⟩ := inverse_radius_threshold hδ hr
  obtain ⟨hp',hp₀'⟩ := raw_reference_tube hq hp (by simpa only [hz] using hd)
  refine ⟨(hdom hp').2,(hdom hp₀').2,?_⟩
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hz₁ : mz (rawMomentumInput p.1)=1/r := hz
  have hz₀ : mz (rawMomentumInput (rawOriginal p.1))=1/r := (rawOriginal_z p.1).trans hz
  rw [commonAngularMomentum_factor (by rw [hz₁]; positivity),
    commonAngularMomentum_factor (by rw [hz₀]; positivity),hz₁,hz₀,← smul_sub,norm_smul]
  change ‖(1/r)^3‖*‖rawAngularResidual p-rawAngularResidual (rawNullOriginal p)‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (1/r)^3)]
  have hh := hLip.dist_le_mul p hp' (rawNullOriginal p) hp₀'
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
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise InnerProductSpace

lemma commonAngularMomentum_norm_sq {p : MomentumInput} (hz : mz p ≠ 0)
    (hp : positiveAngular (mq p).1) (hs : (mq p).1 1 0=(mq p).1 0 1) :
    ‖commonAngularMomentum p‖^2 =
      covectorPair (rescale (1/mz p^2) (mq p)) (coordinateZ p) (coordinateZ p) := by
  rw [commonAngularMomentum,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,
    covectorEmbedding_norm_sq hp hs]
  have hc := one_div_ne_zero (pow_ne_zero 2 hz)
  have hh := covectorPair_rescale (mq p) (coordinateZ p) (coordinateZ p) hc 1 1
  simp only [one_smul,mul_one] at hh
  rw [hh]
  unfold covectorPair
  field_simp

lemma coordinateDEC_iff {p : NullInput} {r : ℝ} (hz : mz (nP p) ≠ 0)
    (hp : positiveAngular (mq (nP p)).1) (hs : (mq (nP p)).1 1 0=(mq (nP p)).1 0 1) :
    coordinateDEC p r ↔ CKSEnd.DEC (coordinateEnergy p r) (coordinateQ (nP p))
      (commonAngularMomentum (nP p)) := by
  unfold coordinateDEC CKSEnd.DEC
  rw [commonAngularMomentum_norm_sq hz hp hs]

theorem bounded_raw_DEC {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, positiveAngular (fun i k => (q i k).1)) (B A : ℝ) (hA : 0 ≤ A) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧
      ∀ p : RawNullInput, rmat p.1 0 ∈ K → ‖p‖ ≤ B →
      ∀ r : ℝ, R₀ ≤ r → rz p.1=1/r → 0 ≤ rwgt p.1 →
      (∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) →
      (rawAngularMatrix p) 1 0=(rawAngularMatrix p) 0 1 →
      (rawAngularMatrix (rawNullOriginal p)) 1 0=(rawAngularMatrix (rawNullOriginal p)) 0 1 →
      coordinateDEC (rawNullMap (rawNullOriginal p)) r → coordinateDEC (rawNullMap p) r := by
  obtain ⟨R₁,hR₁,C,D,hC,hD,hscalar⟩ := bounded_raw_CQ hK (fun q hq => (hreg q hq).2.ne') B A hA
  obtain ⟨R₂,hR₂,T,hT,htan⟩ := bounded_raw_common_angular hK hreg B
  let R₀ := max R₁ (max R₂ (max (C^2) (max C ((T*A)^4))))
  refine ⟨R₀,hR₁.trans (le_max_left _ _),?_⟩
  intro p hq hp r hr hz hw hparams hs hs₀ hDEC
  have hr₁ : R₁ ≤ r := (le_max_left _ _).trans hr
  have hr₂ : R₂ ≤ r := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hr
  have hr3 : max (C^2) (max C ((T*A)^4)) ≤ r :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hr
  have hCr₂ : C^2 ≤ r := (le_max_left _ _).trans hr3
  have hCr : C ≤ r := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hr3
  have hTr : (T*A)^4 ≤ r := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hr3
  have hr1 : 1 ≤ r := hR₁.trans hr₁
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  obtain ⟨hq₀,hdq,hsmall,hz₀,hdz⟩ := hscalar p hq hp r hr₁ hz hw hparams
  obtain ⟨hpos,hpos₀,ht⟩ := htan p hq hp r A hr₂ hz hw hA hparams
  have hz₁ : mz (nP (rawNullMap p)) ≠ 0 := by change rz p.1 ≠ 0; rw [hz]; positivity
  have hz₀ : mz (nP (rawNullMap (rawNullOriginal p))) ≠ 0 := by
    change rz (rawOriginal p.1) ≠ 0
    rw [rawOriginal_z,hz]; positivity
  apply (coordinateDEC_iff hz₁ hpos hs).mpr
  have h₀ := (coordinateDEC_iff hz₀ hpos₀ hs₀).mp hDEC
  apply CKSEnd.collar_DEC_of_weighted_errors (LinearIsometry.id) h₀ hr1 hw hC hC
    (mul_nonneg hT hA) hCr₂ hCr hTr
  · simpa only [CKSEnd.smallMargin,mul_div_assoc,nP,rawNullMap,rawNullOriginal,nr] using hsmall
  · simpa only [CKSEnd.largeMargin,mul_div_assoc,nP,rawNullMap,rawNullOriginal,nr] using hdq
  · exact ht

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

lemma matrixDerivedJets_norm_le_three (q : Point → Mat) (x : Point) (a : I) :
    ‖matrixScalarJets (fun y i k => D (basis a) (fun z => q z i k) y) x‖ ≤ ‖matrixThreeJets q x‖ := by
  apply (Matrix.norm_le_iff (norm_nonneg _)).mpr
  intro i k
  exact ((norm_le_pi_norm (matrixThreeJets q x i k).2 a).trans
    (norm_snd_le (matrixThreeJets q x i k))).trans
    (Matrix.norm_entry_le_entrywise_sup_norm (matrixThreeJets q x))

def CollarCoefficientFields.BoundedAt (f : CollarCoefficientFields) (B : ℝ) (x : Point) : Prop :=
  (∀ i : Fin 2, ‖matrixThreeJets (f.metric i.castSucc) x‖ ≤ B) ∧
  ‖matrixScalarJets (f.metric 2) x‖ ≤ B ∧
  ‖fun a => actualThreeJet (fun y => f.shift y a) x‖ ≤ B ∧
  (∀ i, ‖actualScalarJet (f.scalar i) x‖ ≤ B) ∧
  ‖fun a => actualScalarJet (fun y => f.eta y a) x‖ ≤ B ∧
  ‖matrixScalarJets f.tau x‖ ≤ B ∧ ‖f.etar x‖ ≤ B ∧
  |f.massRadial x| ≤ B ∧ |f.massGap x| ≤ B

lemma fieldRaw_norm {b : Fin 5 → ℝ} {f : CollarCoefficientFields} {x : Point}
    {B : ℝ} (hB : 0 ≤ B) (hb : ‖b‖ ≤ B) (hf : f.BoundedAt B x) :
    ‖fieldRaw b f x‖ ≤ B := by
  apply norm_prod_le_iff.mpr
  constructor
  · apply norm_prod_le_iff.mpr
    refine ⟨hb,?_⟩
    apply norm_prod_le_iff.mpr
    constructor
    · apply norm_prod_le_iff.mpr
      constructor
      · apply norm_prod_le_iff.mpr
        constructor
        · apply (pi_norm_le_iff_of_nonneg hB).mpr
          intro i
          fin_cases i
          · exact (matrixScalarJets_norm_le_three _ _).trans (hf.1 0)
          · exact (matrixScalarJets_norm_le_three _ _).trans (hf.1 1)
          · exact hf.2.1
        · apply (pi_norm_le_iff_of_nonneg hB).mpr; intro i
          apply (pi_norm_le_iff_of_nonneg hB).mpr; intro a
          exact (matrixDerivedJets_norm_le_three _ _ _).trans (hf.1 i)
      · apply norm_prod_le_iff.mpr
        constructor
        · apply (pi_norm_le_iff_of_nonneg hB).mpr; intro a
          exact (norm_fst_le (actualThreeJet (fun y => f.shift y a) x)).trans
            ((norm_le_pi_norm (fun a => actualThreeJet (fun y => f.shift y a) x) a).trans hf.2.2.1)
        · apply (pi_norm_le_iff_of_nonneg hB).mpr; intro a
          apply (pi_norm_le_iff_of_nonneg hB).mpr; intro k
          exact ((norm_le_pi_norm (actualThreeJet (fun y => f.shift y k) x).2 a).trans
            (norm_snd_le (actualThreeJet (fun y => f.shift y k) x))).trans
            ((norm_le_pi_norm (fun k => actualThreeJet (fun y => f.shift y k) x) k).trans hf.2.2.1)
    · apply norm_prod_le_iff.mpr
      constructor
      · exact norm_prod_le_iff.mpr ⟨(pi_norm_le_iff_of_nonneg hB).mpr hf.2.2.2.1,hf.2.2.2.2.1⟩
      · exact norm_prod_le_iff.mpr ⟨hf.2.2.2.2.2.1,hf.2.2.2.2.2.2.1⟩
  · apply norm_prod_le_iff.mpr
    simpa only [fieldRaw, Real.norm_eq_abs] using (show ‖f.massRadial x‖ ≤ B ∧ ‖f.massGap x‖ ≤ B from
      And.intro (by simpa only [Real.norm_eq_abs] using hf.2.2.2.2.2.2.2.1)
        (by simpa only [Real.norm_eq_abs] using hf.2.2.2.2.2.2.2.2))

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
lemma thinRaw_acceleration (p : RawNullInput) :
    accelerationCoefficient (nP (rawNullMap (thinRaw p)))=accelerationCoefficient (nP (rawNullMap p)) := by
  funext a
  simp only [accelerationCoefficient,thin_mc0,thin_mz]

lemma thinRaw_Q (p : RawNullInput) :
    coordinateQ (nP (rawNullMap (thinRaw p)))=coordinateQ (nP (rawNullMap p)) := by
  simp only [coordinateQ,normalizedMean,normalizedSpeed,physicalLJet,physicalTJet,thinRaw_acceleration,thin_mz,thin_mw,thin_mq,thin_mS,thin_mE,thin_mT,thin_mX,thin_mc0,thin_mc1,thin_mc2,thin_mc3,thin_mc4]
lemma thinRaw_Z (p : RawNullInput) :
    coordinateZ (nP (rawNullMap (thinRaw p)))=coordinateZ (nP (rawNullMap p)) := by
  funext a
  simp only [coordinateZ,normalizedMean,normalizedSpeed,physicalLJet,physicalTJet,thinRaw_acceleration,thin_mz,thin_mw,thin_mq,thin_mS,thin_mE,thin_mT,thin_mEr,thin_mc0,thin_mc1,thin_mc2,thin_mc4]
lemma thinRaw_ratio (p : RawNullInput) :
    nullRatio (nP (rawNullMap (thinRaw p)))=nullRatio (nP (rawNullMap p)) := by
  simp only [nullRatio,nullD,normalizedSpeed,thin_mz,thin_mc0,thin_mc1,thin_mc4]
lemma thinRaw_smallNull (p : RawNullInput) (r : ℝ) :
    coordinateSmallNull (rawNullMap (thinRaw p)) r=coordinateSmallNull (rawNullMap p) r := by
  simp only [coordinateSmallNull,nullD,nullRatio,normalizedSpeed,physicalNullQuadratic,physicalNullEta,thinRaw_acceleration,thin_mz,thin_mw,thin_mq,thin_mS,thin_mE,thin_mT,thin_mX,thin_mc0,thin_mc1,thin_mc4,thin_nF,thin_nFr]
lemma thinRaw_DEC (p : RawNullInput) (r : ℝ) :
    coordinateDEC (rawNullMap (thinRaw p)) r ↔ coordinateDEC (rawNullMap p) r := by
  simp only [coordinateDEC,coordinateEnergy,thinRaw_Q,thinRaw_Z,thinRaw_smallNull,thinRaw_ratio,thin_mq,thin_mz]
lemma thinRaw_old (p : RawNullInput) : thinRaw (rawNullOriginal p)=rawNullOriginal (thinRaw p) := rfl
lemma thinRaw_angular (p : RawNullInput) : rawAngularMatrix (thinRaw p)=rawAngularMatrix p := rfl

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

def CollarCoefficientFields.freezeRadial (f : CollarCoefficientFields) (x : Point) : CollarCoefficientFields :=
  { f with scalar := fun i y => if i=3 then f.scalar 3 x else f.scalar i y }

lemma fieldRaw_freeze (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point) :
    fieldRaw b (f.freezeRadial x) x=thinRaw (fieldRaw b f x) := by
  have he : (fun i => actualScalarJet ((f.freezeRadial x).scalar i) x)=
      (fun i => if i=3 then constantJet (actualScalarJet (f.scalar i) x).1 else actualScalarJet (f.scalar i) x) := by
    funext i
    by_cases hi : i=3
    · subst i; simp only [CollarCoefficientFields.freezeRadial,ite_true]
      exact actualScalarJet_const _ _
    · simp only [CollarCoefficientFields.freezeRadial,hi,ite_false]
  unfold fieldRaw
  rw [he]
  rfl

lemma freezeRadial_bounded {f : CollarCoefficientFields} {B : ℝ} {x : Point}
    (hB : 0 ≤ B) (hf : f.ThinBoundedAt B x) : (f.freezeRadial x).BoundedAt B x := by
  refine ⟨hf.1,hf.2.1,hf.2.2.1,?_,hf.2.2.2.2.2⟩
  intro i
  by_cases hi : i=3
  · subst i
    change ‖actualScalarJet (fun _ : Point => f.scalar 3 x) x‖ ≤ B
    rw [actualScalarJet_const]
    exact norm_prod_le_iff.mpr ⟨by simpa only [constantJet,Real.norm_eq_abs] using hf.2.2.2.2.1,
      norm_prod_le_iff.mpr ⟨by simpa [constantJet] using hB,by simpa [constantJet] using hB⟩⟩
  · simpa only [CollarCoefficientFields.freezeRadial,hi,ite_false] using hf.2.2.2.1 i hi

lemma fieldRaw_thin_norm {b : Fin 5 → ℝ} {f : CollarCoefficientFields} {B : ℝ} {x : Point}
    (hB : 0 ≤ B) (hb : ‖b‖ ≤ B) (hf : f.ThinBoundedAt B x) :
    ‖thinRaw (fieldRaw b f x)‖ ≤ B := by
  rw [← fieldRaw_freeze]
  exact fieldRaw_norm hB hb (freezeRadial_bounded hB hf)

theorem bounded_thin_field_map_DEC {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, positiveAngular (fun i k => (q i k).1)) {B A : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point),
      matrixScalarJets (f.metric 0) x ∈ K → ‖b‖ ≤ B → f.ThinBoundedAt B x →
      ∀ r : ℝ, R₀ ≤ r → b 0=1/r → 0 ≤ b 4 →
      (∀ i, i ≠ 0 → |b i| ≤ A*b 4) →
      (rawAngularMatrix (fieldRaw b f x)) 1 0=(rawAngularMatrix (fieldRaw b f x)) 0 1 →
      (rawAngularMatrix (rawNullOriginal (fieldRaw b f x))) 1 0=
        (rawAngularMatrix (rawNullOriginal (fieldRaw b f x))) 0 1 →
      coordinateDEC (rawNullMap (rawNullOriginal (fieldRaw b f x))) r →
      coordinateDEC (rawNullMap (fieldRaw b f x)) r := by
  obtain ⟨R,hR,hh⟩ := bounded_raw_DEC hK hreg B A hA
  refine ⟨R,hR,?_⟩
  intro b f x hq hb hf r hr hz hw hparams hs hs₀ hDEC
  apply (thinRaw_DEC (fieldRaw b f x) r).mp
  apply hh (thinRaw (fieldRaw b f x)) hq (fieldRaw_thin_norm hB hb hf) r hr hz hw hparams hs
  · simpa only [← thinRaw_old,thinRaw_angular] using hs₀
  · rw [← thinRaw_old]
    exact (thinRaw_DEC _ r).mpr hDEC

end
end CKSAngularGeometry

end

end OAI
end

theorem solution : type_of% @OAI.CKSAngularGeometry.bounded_thin_field_map_DEC := @OAI.CKSAngularGeometry.bounded_thin_field_map_DEC
