-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.exists_heat_uniform_majorant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:38:52.856402+00:00
-- url     : https://prove2.me/submissions/e51bf009-0665-433e-a283-dcbbc7baa860

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/HeatBound.lean:L87-L145
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.exists_heat_uniform_majorant. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Theorems.Thm_OAI_TriangularHilbert_Heat_exists_score_polynomial_bound
import Theorems.Thm_OAI_TriangularHilbert_Heat_heatAtBounds_of_norms
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_norm_matrix_le_entries

-- ---- from OAI.Analysis.TriangularHilbert.WeightedStar ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma rowStar_apply (A : Three → Matrix ι ι ℂ) (v : Three) (a b : BlockSpace ι) :
    rowStar A v a b = if a.1 = v then triangleBlocks A a.1 b.1 a.2 b.2 else 0 := by
  simp [rowStar, vertexProj, triangle, blocks, Matrix.diagonal_mul, ite_mul]

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.NormBounds ----
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma entryNormConstant_nonneg : 0 ≤ entryNormConstant ι := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _))

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.HeatInsert ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma heatMask_eq_diagonal (d : Three → ι → ℝ) :
    heatMask d = Matrix.diagonal (fun a : BlockSpace ι => (d a.1 a.2 : ℂ)) := by
  ext ⟨v,i⟩ ⟨w,j⟩
  by_cases hv : v = w <;> by_cases hi : i = j <;>
    simp [heatMask, blockD, blocks, Matrix.diagonal, hv, hi, Prod.mk.injEq]

lemma heatCarrier_norm (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) (v w : Three) :
    ‖heatCarrier A h u p σ v w‖ = ‖rowStar (heatArray A h u p σ) v‖ := by
  unfold heatCarrier
  split_ifs
  · rfl
  · exact norm_star (rowStar (heatArray A h u p σ) v)

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GaussianDom ----
namespace OAI

section

namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma gaussian_exponent_le {σ b : ℝ} (hσ : 0 < σ) (hσb : σ ≤ b) (u p : ℝ) :
    -(u-p)^2 / (2*σ) ≤ u^2/(2*b) - p^2/(4*b) := by
  have hb : 0 < b := hσ.trans_le hσb
  calc
    _ ≤ -(u-p)^2 / (2*b) := by
      rw [neg_div, neg_div]
      exact neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith))
    _ = (-2*(u-p)^2)/(4*b) := by field_simp; ring
    _ ≤ (2*u^2-p^2)/(4*b) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg (p - 2*u)]
    _ = _ := by field_simp; ring

lemma weight_le_gaussian {h a σ b : ℝ} (hh : 0 ≤ h) (ha : 0 < a)
    (haσ : a ≤ σ) (hσb : σ ≤ b) (u p : ℝ) :
    weight h u p σ ≤
      (h * (Real.sqrt (2*Real.pi*a))⁻¹ * Real.exp (u^2/(2*b))) *
        Real.exp (-p^2/(4*b)) := by
  have hσ := ha.trans_le haσ
  have hn : (Real.sqrt (2*Real.pi*σ))⁻¹ ≤ (Real.sqrt (2*Real.pi*a))⁻¹ := by
    simp only [← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    exact Real.sqrt_le_sqrt (by gcongr)
  have he := Real.exp_le_exp.mpr (gaussian_exponent_le hσ hσb u p)
  unfold weight density
  calc
    _ ≤ h * ((Real.sqrt (2*Real.pi*a))⁻¹ * Real.exp (u^2/(2*b)-p^2/(4*b))) := by
      gcongr
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring_nf

lemma rootWeight_le_gaussian {h a σ b : ℝ} (hh : 0 ≤ h) (ha : 0 < a)
    (haσ : a ≤ σ) (hσb : σ ≤ b) (u p : ℝ) :
    Real.sqrt (weight h u p σ) ≤
      Real.sqrt (h * (Real.sqrt (2*Real.pi*a))⁻¹ * Real.exp (u^2/(2*b))) *
        Real.exp (-p^2/(8*b)) := by
  have hh' := Real.sqrt_le_sqrt (weight_le_gaussian hh ha haσ hσb u p)
  rw [Real.sqrt_mul (by positivity), ← Real.exp_half] at hh'
  convert! hh' using 1
  congr 2
  field_simp
  ring

lemma integrable_one_add_sq_sq_gaussian {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => (1+x^2)^2 * Real.exp (-b*x^2)) := by
  have h0 : Integrable (fun x : ℝ => Real.exp (-b*x^2)) := by
    simpa using (integrable_rpow_mul_exp_neg_mul_sq hb (s := 0) (by norm_num))
  have h2 : Integrable (fun x : ℝ => x^2 * Real.exp (-b*x^2)) := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq hb (s := (2:ℕ)) (by norm_num))
  have h4 : Integrable (fun x : ℝ => x^4 * Real.exp (-b*x^2)) := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq hb (s := (4:ℕ)) (by norm_num))
  convert! h0.add ((h2.const_mul 2).add h4) using 1
  ext x
  dsimp
  ring

lemma planeGaussian_pos (b : ℝ) (z : ℝ × ℝ) : 0 < planeGaussian b z := Real.exp_pos _
lemma planeGaussian_le_one {b : ℝ} (hb : 0 ≤ b) (z : ℝ × ℝ) : planeGaussian b z ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (add_nonneg (sq_nonneg _) (sq_nonneg _))
lemma one_le_planePoly (z : ℝ × ℝ) : 1 ≤ planePoly z := by
  unfold planePoly
  nlinarith [sq_nonneg z.1, sq_nonneg z.2, mul_nonneg (sq_nonneg z.1) (sq_nonneg z.2)]
lemma planePoly_nonneg (z : ℝ × ℝ) : 0 ≤ planePoly z := (by norm_num : (0:ℝ) ≤ 1).trans (one_le_planePoly z)

lemma integrable_planePoly_sq_gaussian {b : ℝ} (hb : 0 < b) :
    Integrable (fun z => planePoly z ^2 * planeGaussian b z) := by
  have hh := (integrable_one_add_sq_sq_gaussian hb).mul_prod (integrable_one_add_sq_sq_gaussian hb)
  convert! hh using 1
  ext z
  simp only [planePoly, planeGaussian]
  rw [show -b * (z.1^2+z.2^2) = -b*z.1^2 + -b*z.2^2 by ring, Real.exp_add]
  ring

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.PlaneChart ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
open MatrixEnergy
noncomputable section

lemma chart_pair_bound {D : ℝ} {d : ℝ} (hd : |d| ≤ D) (i j k : Three) (hjk : j ≠ k)
    (z : ℝ × ℝ) : z.1^2+z.2^2 ≤ 4*((chart i d z j)^2+(chart i d z k)^2)+3*D^2 := by
  have hD : 0 ≤ D := (abs_nonneg d).trans hd
  have hd2 : d^2 ≤ D^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hD).2 hd
  have hgen (x y : ℝ) : x^2+y^2+(d-x-y)^2 ≤ 4*(x^2+y^2)+3*D^2 := by
    nlinarith [sq_nonneg (x-y), sq_nonneg (d+x), sq_nonneg (d+y)]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at hjk
  all_goals norm_num [chart]
  all_goals nlinarith [hgen z.1 z.2, hgen (d-z.1-z.2) z.1, hgen (d-z.1-z.2) z.2,
    sq_nonneg z.1, sq_nonneg z.2, sq_nonneg (d-z.1-z.2)]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.PlaneDom ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

lemma endpoint_gaussian_bound {D d b : ℝ} (hb : 0 < b) (hd : |d| ≤ D)
    (i j k : Three) (hjk : j ≠ k) (z : ℝ × ℝ) :
    Real.exp (-((chart i d z j)^2+(chart i d z k)^2)/(8*b)) ≤
      Real.exp (3*D^2/(32*b)) * planeGaussian (1/(32*b)) z := by
  have hh := chart_pair_bound hd i j k hjk z
  rw [planeGaussian, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he : -((chart i d z j)^2+(chart i d z k)^2)/(8*b) ≤
      (3*D^2-(z.1^2+z.2^2))/(32*b) := by
    rw [div_le_div_iff₀ (by positivity : 0 < 8*b) (by positivity : 0 < 32*b)]
    nlinarith
  convert! he using 1
  ring

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma exists_heatArray_gaussian_bound (A : Three → Matrix ι ι ℂ) {h a b D : ℝ}
    (hh : 0 < h) (ha : 0 < a) (hab : a ≤ b) (_hD : 0 ≤ D) (u : ι → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Three → ℝ) (i : Three) (d : ℝ) (z : ℝ × ℝ),
      |d| ≤ D → p = chart i d z → ∀ (σ : Three → ℝ),
      (∀ w, a ≤ σ w) → (∀ w, σ w ≤ b) → ∀ v k l,
      ‖heatArray A h u p σ v k l‖ ≤ C * planeGaussian (1/(32*b)) z := by
  let K : Three × ι × ι → ℝ := fun t => rootCoefficient h a b (u t.2.1) *
    ‖A t.1 t.2.1 t.2.2‖ * rootCoefficient h a b (u t.2.2)
  have hK t : 0 ≤ K t := by dsimp [K, rootCoefficient]; positivity
  let C := (∑ t, K t) * Real.exp (3*D^2/(32*b))
  refine ⟨C, mul_nonneg (Finset.sum_nonneg (fun t _ => hK t)) (Real.exp_pos _).le, ?_⟩
  intro p i d z hd hp σ hσa hσb v k l
  subst p
  have hb := ha.trans_le hab
  have hv : v ≠ v+1 := by fin_cases v <;> decide
  have hleft := rootWeight_le_gaussian hh.le ha (hσa v) (hσb v) (u k) (chart i d z v)
  have hright := rootWeight_le_gaussian hh.le ha (hσa (v+1)) (hσb (v+1)) (u l) (chart i d z (v+1))
  have hc : K (v,k,l) ≤ ∑ t, K t := Finset.single_le_sum (fun t _ => hK t) (Finset.mem_univ _)
  calc
    _ = Real.sqrt (weight h (u k) (chart i d z v) (σ v)) * ‖A v k l‖ *
        Real.sqrt (weight h (u l) (chart i d z (v+1)) (σ (v+1))) := by
      simp only [heatArray, weightedArray, heatWeights, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ (rootCoefficient h a b (u k) * Real.exp (-(chart i d z v)^2/(8*b))) * ‖A v k l‖ *
        (rootCoefficient h a b (u l) * Real.exp (-(chart i d z (v+1))^2/(8*b))) := by
      dsimp only [rootCoefficient]
      gcongr
    _ = K (v,k,l) * Real.exp (-((chart i d z v)^2+(chart i d z (v+1))^2)/(8*b)) := by
      dsimp [K]
      rw [show -((chart i d z v)^2+(chart i d z (v+1))^2)/(8*b) =
        -(chart i d z v)^2/(8*b) + -(chart i d z (v+1))^2/(8*b) by ring, Real.exp_add]
      ring
    _ ≤ (∑ t, K t) * (Real.exp (3*D^2/(32*b)) * planeGaussian (1/(32*b)) z) := by
      exact mul_le_mul hc (endpoint_gaussian_bound hb hd i v (v+1) hv z)
        (Real.exp_pos _).le (Finset.sum_nonneg (fun t _ => hK t))
    _ = _ := by dsimp [C]; ring

omit [Fintype ι] [DecidableEq ι] in
lemma triangleBlocks_entry_bound (W : Three → Matrix ι ι ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hW : ∀ v i j, ‖W v i j‖ ≤ M) (a b : Three) (i j : ι) :
    ‖triangleBlocks W a b i j‖ ≤ M := by
  fin_cases a <;> fin_cases b <;> simp [triangleBlocks, Matrix.conjTranspose_apply]
  all_goals first | exact hM | exact hW _ _ _

lemma norm_rowStar_le_bound (W : Three → Matrix ι ι ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hW : ∀ v i j, ‖W v i j‖ ≤ M) (v : Three) :
    ‖rowStar W v‖ ≤ entryNormConstant (BlockSpace ι) * M := by
  apply norm_matrix_le_entries
  intro a b
  rw [rowStar_apply]
  split_ifs
  · exact triangleBlocks_entry_bound W hM hW _ _ _ _
  · simpa using hM

lemma exists_heatCarrier_gaussian_bound (A : Three → Matrix ι ι ℂ) {h a b D : ℝ}
    (hh : 0 < h) (ha : 0 < a) (hab : a ≤ b) (hD : 0 ≤ D) (u : ι → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Three) (d : ℝ) (z : ℝ × ℝ), |d| ≤ D →
      ∀ (σ : Three → ℝ), (∀ w, a ≤ σ w) → (∀ w, σ w ≤ b) → ∀ v w,
      ‖heatCarrier A h u (chart i d z) σ v w‖ ≤ C * planeGaussian (1/(32*b)) z := by
  obtain ⟨C,hC,hbound⟩ := exists_heatArray_gaussian_bound A hh ha hab hD u
  refine ⟨entryNormConstant (BlockSpace ι) * C, mul_nonneg entryNormConstant_nonneg hC, ?_⟩
  intro i d z hd σ hσa hσb v w
  rw [heatCarrier_norm]
  calc
    _ ≤ entryNormConstant (BlockSpace ι) * (C * planeGaussian (1/(32*b)) z) :=
      norm_rowStar_le_bound _ (mul_nonneg hC (planeGaussian_pos _ _).le)
        (hbound _ i d z hd rfl σ hσa hσb) v
    _ = _ := by ring

lemma norm_heatMask_le (r : Three → ι → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hr : ∀ w j, |r w j| ≤ M) : ‖heatMask r‖ ≤ entryNormConstant (BlockSpace ι) * M := by
  apply norm_matrix_le_entries
  intro a b
  rw [heatMask_eq_diagonal]
  by_cases hab : a = b
  · subst b
    simpa only [Matrix.diagonal_apply_eq, Complex.norm_real, Real.norm_eq_abs] using hr a.1 a.2
  · simpa only [Matrix.diagonal_apply_ne _ hab, norm_zero] using hM

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.HeatBound ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma HeatAtBounds.mono {A : Three → Matrix ι ι ℂ} {h : ℝ} {u : ι → ℝ}
    {p σ : Three → ℝ} {M N : ℝ} (hb : HeatAtBounds A h u p σ M) (hMN : M ≤ N) :
    HeatAtBounds A h u p σ N := by
  exact ⟨fun v => (hb.energy v).trans hMN, fun v w => (hb.first v w).trans hMN,
    fun v w => (hb.pure v w).trans hMN, fun v w => (hb.variance v w).trans hMN,
    fun v w => (hb.cost v w).trans hMN, fun v w z hw hz => (hb.mixed v w z hw hz).trans hMN⟩

lemma exists_heat_uniform_majorant (A : Three → Matrix ι ι ℂ) {h a b D : ℝ}
    (hh : 0 < h) (ha : 0 < a) (hab : a ≤ b) (hD : 0 ≤ D) (u : ι → ℝ) :
    ∃ B : (ℝ × ℝ) → ℝ, Integrable B ∧ (∀ z, 0 ≤ B z) ∧
      ∀ (i : Three) (d : ℝ) (z : ℝ × ℝ), |d| ≤ D → ∀ (σ : Three → ℝ),
      (∀ w, a ≤ σ w) → (∀ w, σ w ≤ b) → HeatAtBounds A h u (chart i d z) σ (B z) := by
  obtain ⟨R,hR,hRB⟩ := exists_heatCarrier_gaussian_bound A hh ha hab hD u
  obtain ⟨S,hS,hSB⟩ := exists_score_polynomial_bound u ha hD
  let T := entryNormConstant (BlockSpace ι)
  let L := T*S
  let Q := T*(S^2+a⁻¹)
  have hT : 0 ≤ T := entryNormConstant_nonneg
  have hL : 0 ≤ L := mul_nonneg hT hS
  have hQ : 0 ≤ Q := mul_nonneg hT (add_nonneg (sq_nonneg _) (inv_nonneg.mpr ha.le))
  let N := ‖traceRealCLM (ι := BlockSpace ι)‖
  let C := N * R^3 * (1+(3/2:ℝ)*L+(3/4:ℝ)*L^2+(3/2:ℝ)*Q)
  have hN : 0 ≤ N := norm_nonneg _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbpos : 0 < b := ha.trans_le hab
  have hb : 0 < 1/(32*b) := by positivity
  refine ⟨fun z => C * (planePoly z^2 * planeGaussian (1/(32*b)) z),
    (integrable_planePoly_sq_gaussian hb).const_mul C,
    fun z => mul_nonneg hC (mul_nonneg (sq_nonneg _) (planeGaussian_pos _ _).le), ?_⟩
  intro i d z hd σ hσa hσb
  have hσ : ∀ w, 0 < σ w := fun w => ha.trans_le (hσa w)
  let P := planePoly z
  let G := planeGaussian (1/(32*b)) z
  have hP : 0 ≤ P := planePoly_nonneg z
  have hP1 : 1 ≤ P := one_le_planePoly z
  have hG : 0 ≤ G := (planeGaussian_pos _ _).le
  have hG1 : G ≤ 1 := planeGaussian_le_one hb.le z
  have hr v w : ‖heatCarrier A h u (chart i d z) σ v w‖^3 ≤ R^3 * G := by
    calc
      _ ≤ (R*G)^3 := pow_le_pow_left₀ (norm_nonneg _) (hRB i d z hd σ hσa hσb v w) 3
      _ = R^3*G^3 := mul_pow _ _ _
      _ ≤ R^3 * G := by gcongr; nlinarith [mul_nonneg hG (sub_nonneg.mpr hG1)]
  have hl w : ‖heatMask (fun a j => if a = w then score (u j) (chart i d z a) (σ a) else 0)‖ ≤ L*P := by
    calc
      _ ≤ T*(S*P) := norm_heatMask_le _ (mul_nonneg hS hP) (by
        intro a j; split_ifs
        · exact (hSB i d z hd σ hσa a j).1
        · simpa using mul_nonneg hS hP)
      _ = _ := by dsimp [L]; ring
  have hq w : ‖heatMask (fun a j => if a = w then score (u j) (chart i d z a) (σ a)^2-(σ a)⁻¹ else 0)‖ ≤ Q*P^2 := by
    calc
      _ ≤ T*((S^2+a⁻¹)*P^2) := norm_heatMask_le _ (by positivity) (by
        intro k j; split_ifs
        · exact (hSB i d z hd σ hσa k j).2
        · simpa using (show 0 ≤ (S^2+a⁻¹)*P^2 by positivity))
      _ = _ := by dsimp [Q]; ring
  apply (heatAtBounds_of_norms A hh u (chart i d z) hσ
    (mul_nonneg (pow_nonneg hR _) hG) (mul_nonneg hL hP)
    (mul_nonneg hQ (sq_nonneg P)) hr hl hq).mono
  change N*(R^3*G)*(1+(3/2:ℝ)*(L*P)+(3/4:ℝ)*(L*P)^2+(3/2:ℝ)*(Q*P^2)) ≤ C*(P^2*G)
  have hP2 : P ≤ P^2 := by nlinarith
  have h1P2 : 1 ≤ P^2 := le_trans hP1 hP2
  calc
    _ = N*R^3*G*(1+(3/2:ℝ)*L*P+(3/4:ℝ)*L^2*P^2+(3/2:ℝ)*Q*P^2) := by ring
    _ ≤ N*R^3*G*(P^2+(3/2:ℝ)*L*P^2+(3/4:ℝ)*L^2*P^2+(3/2:ℝ)*Q*P^2) := by gcongr
    _ = _ := by dsimp [C]; ring
end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.Heat.exists_heat_uniform_majorant.{uι} := @_root_.OAI.TriangularHilbert.Heat.exists_heat_uniform_majorant.{uι}
