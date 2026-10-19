-- Prove2me | solution 1 for OAI.TriangularHilbert.MatrixEnergy.energy_jump_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:08:23.356983+00:00
-- url     : https://prove2.me/submissions/5588a7be-4e24-4b71-8bba-e97fad31aae3

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/RankJump.lean:L68-L88
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.MatrixEnergy.energy_jump_le. The node keeps its source
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_energy_hasFDerivWithinAt

-- ---- from OAI.Analysis.TriangularHilbert.MatrixSupport ----
namespace OAI

universe uι uκ uX uμ

section
open scoped BigOperators
noncomputable section
namespace TriangularHilbert.MatrixEnergy

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace InnerProductSpace

end TriangularHilbert.MatrixEnergy

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary
namespace TriangularHilbert.MatrixEnergy

variable {ι : Type uι} [Fintype ι]

theorem traceReal_mul_comm (A B : Matrix ι ι ℂ) : traceReal (A * B) = traceReal (B * A) := by
  unfold traceReal; rw [Matrix.trace_mul_comm]
variable [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary MeasureTheory Filter
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem regularize_posDef {P : Matrix ι ι ℂ} (hP : P.PosSemidef)
    {η : ℝ} (hη : 0 < η) : (regularize P η).PosDef :=
  Matrix.PosDef.posSemidef_add hP (Matrix.PosDef.one.smul hη)

omit [Fintype ι] in
theorem regularize_posSemidef {P : Matrix ι ι ℂ} (hP : P.PosSemidef)
    {η : ℝ} (hη : 0 ≤ η) : (regularize P η).PosSemidef :=
  hP.add (Matrix.PosSemidef.one.smul hη)

theorem continuous_sqrt_matrix {X : Type uX} [TopologicalSpace X]
    {P : X → Matrix ι ι ℂ} (hP : _root_.Continuous P)
    (hn : ∀ x, (P x).PosSemidef) : _root_.Continuous (fun x => CFC.sqrt (P x)) :=
  CFC.continuousOn_sqrt.comp_continuous hP (fun x => (hn x).nonneg)

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma gradient_gram (R D A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    traceReal (A * (Rᴴ * D + Dᴴ * R)) = 2 * hsReal (R * A) D := by
  have he : traceReal (A * (Dᴴ * R)) = traceReal (A * (Rᴴ * D)) := by
    rw [traceReal_mul_comm, ← traceReal_star (Dᴴ * R * A)]
    simp only [Matrix.conjTranspose_mul, hA.eq, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  simp only [hsReal, Matrix.conjTranspose_mul, hA.eq, Matrix.mul_assoc,
    mul_add, traceReal_add, he]
  ring

lemma energyGradient_gram (P R D : Matrix ι ι ℂ) :
    energyGradient P (Rᴴ * D + Dᴴ * R) =
      3 * hsReal (R * CFC.sqrt P) D := by
  have hs : (CFC.sqrt P).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
  rw [energyGradient_apply, gradient_gram R D (CFC.sqrt P) hs]
  ring

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace TriangularHilbert.MatrixEnergy
variable {ι : Type uι} {κ : Type uκ} {μ : Type uμ} [Fintype ι] [Fintype κ] [Fintype μ]

omit [Fintype ι] [Fintype μ] in
theorem norm_mul_entry_le (R : Matrix ι κ ℂ) (S : Matrix κ μ ℂ) (i : ι) (j : μ) :
    ‖(R * S) i j‖ ≤ rowNorm R i * colNorm S j := by
  calc
    ‖(R * S) i j‖ ≤ ∑ k, ‖R i k * S k j‖ := norm_sum_le _ _
    _ = ∑ k, ‖R i k‖ * ‖S k j‖ := by simp only [norm_mul]
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

omit [Fintype κ] in
theorem colNorm_sq (R : Matrix ι κ ℂ) (j : κ) :
    (colNorm R j)^2 = ((Rᴴ * R) j j).re := by
  rw [colNorm, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

variable [DecidableEq κ]

theorem colNorm_sqrt_gram (R : Matrix ι κ ℂ) (j : κ) :
    colNorm (CFC.sqrt (Rᴴ * R)) j = colNorm R j := by
  have hsP := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Rᴴ * R))
  have he : (colNorm (CFC.sqrt (Rᴴ * R)) j)^2 = (colNorm R j)^2 := by
    rw [colNorm_sq, hsP.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self (Rᴴ * R) (Matrix.posSemidef_conjTranspose_mul_self R).nonneg,
      colNorm_sq]
  exact (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp he

theorem entry_gradient_le (R : Matrix ι κ ℂ) (i : ι) (j : κ) :
    ‖(R * CFC.sqrt (Rᴴ * R)) i j‖ ≤ rowNorm R i * colNorm R j := by
  simpa only [colNorm_sqrt_gram] using norm_mul_entry_le R (CFC.sqrt (Rᴴ * R)) i j

end TriangularHilbert.MatrixEnergy
end
end
end
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GramDeriv ----
namespace OAI

universe uι uE uF

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter MeasureTheory
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma regularized_energyGram_hasFDerivAt (R : Matrix ι ι ℂ) {η : ℝ} (hη : 0 < η) :
    HasFDerivAt (fun X : Matrix ι ι ℂ => energy (regularize (Xᴴ * X) η))
      (gramGradientAt R (regularize (Rᴴ * R) η)) R := by
  have hg := (((hasFDerivAt_id R (𝕜 := ℝ)).star).mul' (hasFDerivAt_id R)).add_const
    (η • (1 : Matrix ι ι ℂ))
  have hp := regularize_posDef (Matrix.posSemidef_conjTranspose_mul_self R) hη
  have hn : ∀ᶠ X : Matrix ι ι ℂ in 𝓝 R, 0 ≤ regularize (Xᴴ * X) η :=
    Eventually.of_forall fun X =>
      (regularize_posSemidef (Matrix.posSemidef_conjTranspose_mul_self X) hη.le).nonneg
  have hh := (energy_hasFDerivWithinAt hp).comp_hasFDerivAt R hg hn
  convert! hh using 1
  ext D
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    smul_apply, ContinuousLinearMap.id_apply, id_eq,
    ContinuousLinearEquiv.coe_coe, starL'_apply, smul_eq_mul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Matrix.star_eq_conjTranspose]
  rw [energyGradient_gram, gramGradientAt_apply]

lemma continuousAt_tendstoUniformlyOnFilter {E : Type uE} {F : Type uF} [TopologicalSpace E]
    [UniformSpace F] {H : ℝ × E → F} {x : E}
    (hH : ContinuousAt H (0, x)) :
    TendstoUniformlyOnFilter (fun η y => H (η, y)) (fun y => H (0, y))
      (𝓝[>] 0) (𝓝 x) := by
  apply tendstoUniformlyOnFilter_iff_tendsto.mpr
  have hp : (𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x ≤ 𝓝 (0, x) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mono nhdsWithin_le_nhds le_rfl
  have h₂ : Tendsto H ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) (𝓝 (H (0, x))) :=
    hH.mono_left hp
  have h₁ : Tendsto (fun p : ℝ × E => H (0, p.2))
      ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) (𝓝 (H (0, x))) :=
    hH.tendsto.comp (tendsto_const_nhds.prodMk_nhds tendsto_snd)
  exact (h₁.prodMk_nhds h₂).mono_right (nhds_le_uniformity _)

lemma continuous_gramRegularization : Continuous
    (fun p : ℝ × Matrix ι ι ℂ => gramRegularization p.1 p.2) := by
  unfold gramRegularization regularize
  fun_prop

lemma gramRegularization_posSemidef (η : ℝ) (R : Matrix ι ι ℂ) :
    (gramRegularization η R).PosSemidef :=
  regularize_posSemidef (Matrix.posSemidef_conjTranspose_mul_self _) (sq_nonneg _)

lemma continuous_regularizedGradient : Continuous
    (fun p : ℝ × Matrix ι ι ℂ => gramGradientAt p.2 (gramRegularization p.1 p.2)) := by
  unfold gramGradientAt
  have hs : Continuous (fun p : ℝ × Matrix ι ι ℂ => CFC.sqrt (gramRegularization p.1 p.2)) :=
    continuous_sqrt_matrix continuous_gramRegularization
      (fun p => gramRegularization_posSemidef p.1 p.2)
  have hr : Continuous (fun p : ℝ × Matrix ι ι ℂ =>
      (p.2 * CFC.sqrt (gramRegularization p.1 p.2))ᴴ) := (continuous_snd.mul hs).star
  have hm : Continuous (fun p : ℝ × Matrix ι ι ℂ =>
      (ContinuousLinearMap.mul ℝ (Matrix ι ι ℂ))
        ((p.2 * CFC.sqrt (gramRegularization p.1 p.2))ᴴ)) :=
    (ContinuousLinearMap.mul ℝ (Matrix ι ι ℂ)).continuous.comp hr
  have ht : Continuous (fun p : ℝ × Matrix ι ι ℂ =>
      traceRealCLM.comp ((ContinuousLinearMap.mul ℝ (Matrix ι ι ℂ))
        ((p.2 * CFC.sqrt (gramRegularization p.1 p.2))ᴴ))) :=
    (ContinuousLinearMap.compL ℝ (Matrix ι ι ℂ) (Matrix ι ι ℂ) ℝ
      traceRealCLM).continuous.comp hm
  exact ht.const_smul (3 : ℝ)

lemma eventually_regularizedEnergy_deriv (R : Matrix ι ι ℂ) :
    ∀ᶠ p : ℝ × Matrix ι ι ℂ in (𝓝[>] (0 : ℝ)) ×ˢ 𝓝 R,
      HasFDerivAt (fun X => energy (gramRegularization p.1 X))
        (gramGradientAt p.2 (gramRegularization p.1 p.2)) p.2 := by
  have hp0 : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), 0 < η := self_mem_nhdsWithin
  have hh : ∀ᶠ p : ℝ × Matrix ι ι ℂ in (𝓝[>] (0 : ℝ)) ×ˢ 𝓝 R, 0 < p.1 :=
    hp0.prod_inl _
  filter_upwards [hh] with p hp
  exact regularized_energyGram_hasFDerivAt p.2 (sq_pos_of_pos hp)

lemma continuous_regularizedEnergy_single (R : Matrix ι ι ℂ) :
    Continuous (fun η : ℝ => energy (gramRegularization η R)) := by
  have hp : Continuous (fun η : ℝ => gramRegularization η R) := by
    unfold gramRegularization regularize
    fun_prop
  exact traceRealCLM.continuous.comp (hp.mul (continuous_sqrt_matrix hp
    (fun η => gramRegularization_posSemidef η R)))

lemma tendsto_regularizedEnergy (R : Matrix ι ι ℂ) :
    Tendsto (fun η => energy (gramRegularization η R))
      (𝓝[>] 0) (𝓝 (energy (Rᴴ * R))) := by
  have ht := (continuous_regularizedEnergy_single R).tendsto (0 : ℝ)
  rw [gramRegularization_zero] at ht
  exact ht.mono_left nhdsWithin_le_nhds

theorem energyGram_hasFDerivAt (R : Matrix ι ι ℂ) :
    HasFDerivAt (fun X : Matrix ι ι ℂ => energy (Xᴴ * X))
      (gramGradientAt R (Rᴴ * R)) R := by
  have hh := hasFDerivAt_of_tendstoUniformlyOnFilter (𝕜 := ℝ) (x := R)
    (f := fun (η : ℝ) (X : Matrix ι ι ℂ) => energy (gramRegularization η X))
    (f' := fun (η : ℝ) (X : Matrix ι ι ℂ) => gramGradientAt X (gramRegularization η X))
    (g := fun X : Matrix ι ι ℂ => energy (Xᴴ * X))
    (g' := fun X : Matrix ι ι ℂ => gramGradientAt X (gramRegularization 0 X))
    (continuousAt_tendstoUniformlyOnFilter
      (continuous_regularizedGradient.continuousAt (x := (0, R))))
    (eventually_regularizedEnergy_deriv R)
    (Eventually.of_forall (fun X => tendsto_regularizedEnergy X))
  simpa only [gramRegularization_zero] using hh

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.RankJump ----
namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma abs_hsReal_le_sum (X Y : Matrix ι ι ℂ) :
    |hsReal X Y| ≤ ∑ i, ∑ j, ‖X i j‖ * ‖Y i j‖ := by
  unfold hsReal traceReal
  calc
    _ ≤ ‖(Xᴴ * Y).trace‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ j, ∑ i, ‖star (X i j) * Y i j‖ := by
      unfold Matrix.trace
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      exact norm_sum_le _ _
    _ = _ := by simp only [norm_mul,norm_star]; rw [Finset.sum_comm]

lemma segmentMatrix_hasDerivAt (A B : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (segmentMatrix A B) (B-A) t := by
  convert! (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).smul_const A).add
    ((hasDerivAt_id t).smul_const B) using 1; simp [sub_eq_add_neg,add_comm]

lemma segmentEnergy_hasDerivAt (A B : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (fun s => energy ((segmentMatrix A B s)ᴴ * segmentMatrix A B s))
      (3 * hsReal (segmentMatrix A B t * CFC.sqrt ((segmentMatrix A B t)ᴴ * segmentMatrix A B t)) (B-A)) t := by
  exact (energyGram_hasFDerivAt _).comp_hasDerivAt t (segmentMatrix_hasDerivAt A B t)

omit [Fintype ι] [DecidableEq ι] in
lemma segmentMatrix_norm_entry_le (A B : Matrix ι ι ℂ) (M : ι → ι → ℝ)
    (hA : ∀ i j, ‖A i j‖ ≤ M i j) (hB : ∀ i j, ‖B i j‖ ≤ M i j)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) (i j : ι) :
    ‖segmentMatrix A B t i j‖ ≤ M i j := by
  calc
    _ ≤ ‖((1-t):ℝ) • A i j‖ + ‖t • B i j‖ := norm_add_le _ _
    _ = (1-t)*‖A i j‖+t*‖B i j‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ht.1,
        abs_of_nonneg (by linarith [ht.2] : 0 ≤ 1-t)]
    _ ≤ (1-t)*M i j+t*M i j := add_le_add
      (mul_le_mul_of_nonneg_left (hA i j) (by linarith [ht.2]))
      (mul_le_mul_of_nonneg_left (hB i j) ht.1)
    _ = _ := by ring

omit [DecidableEq ι] in
lemma rowNorm_mono {X Y : Matrix ι ι ℂ} (h : ∀ i j, ‖X i j‖ ≤ ‖Y i j‖) (i : ι) :
    rowNorm X i ≤ rowNorm Y i := by
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum (fun j _ => sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr (h i j))

omit [DecidableEq ι] in
lemma colNorm_mono {X Y : Matrix ι ι ℂ} (h : ∀ i j, ‖X i j‖ ≤ ‖Y i j‖) (j : ι) :
    colNorm X j ≤ colNorm Y j := by
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum (fun i _ => sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr (h i j))

lemma energy_jump_le (A B M : Matrix ι ι ℂ)
    (hA : ∀ i j, ‖A i j‖ ≤ ‖M i j‖) (hB : ∀ i j, ‖B i j‖ ≤ ‖M i j‖) :
    |energy (Bᴴ*B) - energy (Aᴴ*A)| ≤
      3 * ∑ i, ∑ j, rowNorm M i * colNorm M j * ‖(B-A) i j‖ := by
  have hb (t : ℝ) (ht : t ∈ Set.Ico 0 1) :
      ‖3 * hsReal (segmentMatrix A B t * CFC.sqrt ((segmentMatrix A B t)ᴴ * segmentMatrix A B t)) (B-A)‖ ≤
      3 * ∑ i, ∑ j, rowNorm M i * colNorm M j * ‖(B-A) i j‖ := by
    rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 3), Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply (abs_hsReal_le_sum _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (entry_gradient_le _ i j).trans
    have he := segmentMatrix_norm_entry_le A B (fun i j => ‖M i j‖) hA hB ⟨ht.1,ht.2.le⟩
    exact mul_le_mul (rowNorm_mono he i) (colNorm_mono he j) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (segmentEnergy_hasDerivAt A B t).hasDerivWithinAt) hb
  simpa [segmentMatrix,Real.norm_eq_abs] using h
end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
open MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.MatrixEnergy.energy_jump_le.{uι} := @_root_.OAI.TriangularHilbert.MatrixEnergy.energy_jump_le.{uι}
