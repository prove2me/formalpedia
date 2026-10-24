-- Prove2me | solution 1 for OAI.PinchedHartogs.normalCurvature_model
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:12:19.931983+00:00
-- url     : https://prove2.me/submissions/65242b0a-18af-40f6-9559-6b6577f46d28

import Mathlib
import Definitions.Def_PinchedKahler
import Definitions.Def_OAIQWPH001

section
-- module Solutions.OAIQW_PinchedHartogs.Obstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler69_1

open Set Filter Topology
open scoped ContDiff
noncomputable section
namespace PinchedHartogs

lemma zero_mem_ball : (0 : Base) ∈ ball := by simp [ball]

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.MetricCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler1607_1 uKahler1618_1

open Set Filter Topology
open scoped ContDiff
noncomputable section

namespace PinchedHartogs

open scoped Matrix.Norms.Elementwise

lemma dbar_congr {f g : Ambient → ℂ} {p : Ambient} (h : f =ᶠ[𝓝 p] g) (i : Fin 3) :
    dbar f p i = dbar g p i := by
  simp only [dbar, h.fderiv_eq]

lemma dz_add {f g : Ambient → ℂ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (i : Fin 3) :
    dz (fun q => f q + g q) p i = dz f p i + dz g p i := by
  have hd : fderiv ℝ (fun q => f q + g q) p = fderiv ℝ f p + fderiv ℝ g p := fderiv_add hf hg
  simp only [dz, hd, add_apply]
  ring

lemma dbar_add {f g : Ambient → ℂ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (i : Fin 3) :
    dbar (fun q => f q + g q) p i = dbar f p i + dbar g p i := by
  have hd : fderiv ℝ (fun q => f q + g q) p = fderiv ℝ f p + fderiv ℝ g p := fderiv_add hf hg
  simp only [dbar, hd, add_apply]
  ring

lemma dz_mul {f g : Ambient → ℂ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (i : Fin 3) :
    dz (fun q => f q * g q) p i = dz f p i * g p + f p * dz g p i := by
  have hd : fderiv ℝ (fun q => f q * g q) p = f p • fderiv ℝ g p + g p • fderiv ℝ f p := fderiv_mul hf hg
  simp only [dz, hd, add_apply,
    smul_apply, smul_eq_mul]
  ring

lemma dbar_mul {f g : Ambient → ℂ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (i : Fin 3) :
    dbar (fun q => f q * g q) p i = dbar f p i * g p + f p * dbar g p i := by
  have hd : fderiv ℝ (fun q => f q * g q) p = f p • fderiv ℝ g p + g p • fderiv ℝ f p := fderiv_mul hf hg
  simp only [dbar, hd, add_apply,
    smul_apply, smul_eq_mul]
  ring

lemma dz_real_comp {f : Ambient → ℝ} {p : Ambient} {ρ : ℝ → ℝ} {ρ' : ℝ}
    (hf : DifferentiableAt ℝ f p) (hρ : HasDerivAt ρ ρ' (f p)) (i : Fin 3) :
    dz (fun q => (ρ (f q) : ℂ)) p i = (ρ' : ℂ) * dz (fun q => (f q : ℂ)) p i := by
  have h := (hρ.comp_hasFDerivAt p hf.hasFDerivAt)
  have hd : fderiv ℝ (fun q => (ρ (f q) : ℂ)) p = Complex.ofRealCLM.comp (ρ' • fderiv ℝ f p) :=
    (Complex.ofRealCLM.hasFDerivAt.comp p h).fderiv
  simp only [dz, hd, fderiv_real_cast hf]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

lemma dbar_real_comp {f : Ambient → ℝ} {p : Ambient} {ρ : ℝ → ℝ} {ρ' : ℝ}
    (hf : DifferentiableAt ℝ f p) (hρ : HasDerivAt ρ ρ' (f p)) (i : Fin 3) :
    dbar (fun q => (ρ (f q) : ℂ)) p i = (ρ' : ℂ) * dbar (fun q => (f q : ℂ)) p i := by
  have h := (hρ.comp_hasFDerivAt p hf.hasFDerivAt)
  have hd : fderiv ℝ (fun q => (ρ (f q) : ℂ)) p = Complex.ofRealCLM.comp (ρ' • fderiv ℝ f p) :=
    (Complex.ofRealCLM.hasFDerivAt.comp p h).fderiv
  simp only [dbar, hd, fderiv_real_cast hf]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

lemma _root_.OAI.ContDiffAt.hartogs_dbar {f : Ambient → ℂ} {p : Ambient} {m n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f p) (hmn : m + 1 ≤ n) (i : Fin 3) :
    ContDiffAt ℝ m (fun q => dbar f q i) p := by
  have hd := hf.fderiv_right hmn
  unfold PinchedHartogs.dbar
  exact ((hd.clm_apply contDiffAt_const).add
    (contDiffAt_const.mul (hd.clm_apply contDiffAt_const))).div_const 2

lemma complexHessian_real_comp {f : Ambient → ℝ} {p : Ambient}
    {ρ ρ' : ℝ → ℝ} {ρ'' : ℝ} (hf : ContDiffAt ℝ 2 f p)
    (hρ : ∀ᶠ y in 𝓝 (f p), HasDerivAt ρ (ρ' y) y)
    (hρ' : HasDerivAt ρ' ρ'' (f p)) (i j : Fin 3) :
    complexHessian (fun q => ρ (f q)) p i j =
      (ρ' (f p) : ℂ) * complexHessian f p i j +
        (ρ'' : ℂ) * dz (fun q => (f q : ℂ)) p i * dbar (fun q => (f q : ℂ)) p j := by
  have he : (fun q => dbar (fun r => (ρ (f r) : ℂ)) q j) =ᶠ[𝓝 p]
      (fun q => (ρ' (f q) : ℂ) * dbar (fun r => (f r : ℂ)) q j) := by
    filter_upwards [hf.eventually (by norm_num), hf.continuousAt hρ] with q hq hρq
    exact dbar_real_comp (hq.differentiableAt (by norm_num)) hρq j
  have hdφ := hf.differentiableAt (by norm_num)
  have hdρ : DifferentiableAt ℝ (fun q => (ρ' (f q) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p (hρ'.differentiableAt.comp p hdφ)
  have hdb : DifferentiableAt ℝ (fun q => dbar (fun r => (f r : ℂ)) q j) p :=
    (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 1) (by norm_num) j).differentiableAt (by norm_num)
  unfold complexHessian
  rw [dz_congr he, dz_mul hdρ hdb, dz_real_comp hdφ hρ']
  ring

lemma dz_const_mul {f : Ambient → ℂ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (c : ℂ) (i : Fin 3) :
    dz (fun q => c * f q) p i = c * dz f p i := by
  have hd : fderiv ℝ (fun q => c * f q) p = c • fderiv ℝ f p := fderiv_const_mul hf c
  simp only [dz, hd, smul_apply, smul_eq_mul]
  ring

lemma dbar_const_mul {f : Ambient → ℂ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (c : ℂ) (i : Fin 3) :
    dbar (fun q => c * f q) p i = c * dbar f p i := by
  have hd : fderiv ℝ (fun q => c * f q) p = c • fderiv ℝ f p := fderiv_const_mul hf c
  simp only [dbar, hd, smul_apply, smul_eq_mul]
  ring

lemma complexHessian_add {f g : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (hg : ContDiffAt ℝ 2 g p) (i j : Fin 3) :
    complexHessian (fun q => f q + g q) p i j =
      complexHessian f p i j + complexHessian g p i j := by
  have he : (fun q => dbar (fun r => ((f r + g r : ℝ) : ℂ)) q j) =ᶠ[𝓝 p]
      (fun q => dbar (fun r => (f r : ℂ)) q j + dbar (fun r => (g r : ℂ)) q j) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with q hq hq'
    simp only [Complex.ofReal_add]
    exact dbar_add ((_root_.OAI.ContDiffAt.hartogs_real_cast hq).differentiableAt (by norm_num))
      ((_root_.OAI.ContDiffAt.hartogs_real_cast hq').differentiableAt (by norm_num)) j
  unfold complexHessian
  rw [dz_congr he]
  exact dz_add ((_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 1) (by norm_num) j).differentiableAt (by norm_num))
    ((_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hg) (m := 1) (by norm_num) j).differentiableAt (by norm_num)) i

lemma complexHessian_const_mul {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (c : ℝ) (i j : Fin 3) :
    complexHessian (fun q => c * f q) p i j = (c : ℂ) * complexHessian f p i j := by
  have he : (fun q => dbar (fun r => ((c * f r : ℝ) : ℂ)) q j) =ᶠ[𝓝 p]
      (fun q => (c : ℂ) * dbar (fun r => (f r : ℂ)) q j) := by
    filter_upwards [hf.eventually (by norm_num)] with q hq
    simp only [Complex.ofReal_mul]
    exact dbar_const_mul ((_root_.OAI.ContDiffAt.hartogs_real_cast hq).differentiableAt (by norm_num)) c j
  unfold complexHessian
  rw [dz_congr he]
  exact dz_const_mul ((_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 1) (by norm_num) j).differentiableAt (by norm_num)) c i

lemma dbar_conj {f : Ambient → ℂ} {p : Ambient} (hf : DifferentiableAt ℝ f p) (i : Fin 3) :
    dbar (fun q => star (f q)) p i = star (dz f p i) := by
  have hd : fderiv ℝ (fun q => star (f q)) p = Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f p) :=
    (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp p hf.hasFDerivAt).fderiv
  simp only [dz, dbar, hd]
  simp [star_sub, star_mul]
  ring

lemma dz_fiber (p : Ambient) (i : Fin 3) :
    dz (fun q => q.2) p i = if i = 2 then 1 else 0 := by
  have hd : fderiv ℝ (fun q : Ambient => q.2) p = ContinuousLinearMap.snd ℝ Base ℂ :=
    (ContinuousLinearMap.snd ℝ Base ℂ).fderiv
  fin_cases i <;> simp [dz, hd, coordVector]

lemma negLogOneSub_hasDerivAt {x : ℝ} (hx : 1 - x ≠ 0) :
    HasDerivAt (fun y : ℝ => -Real.log (1 - y)) ((1 - x)⁻¹) x := by
  have hh : HasDerivAt (fun y : ℝ => -Real.log (1 - y)) (-(-1 / (1-x))) x :=
    (((hasDerivAt_id x).const_sub 1).log hx).neg
  have he : -(-1 / (1-x)) = (1-x)⁻¹ := by simp [neg_div, one_div]
  rw [he] at hh
  exact hh

lemma invOneSub_hasDerivAt {x : ℝ} (hx : 1 - x ≠ 0) :
    HasDerivAt (fun y : ℝ => (1 - y)⁻¹) (((1 - x) ^ 2)⁻¹) x := by
  have hh : HasDerivAt (fun y : ℝ => (1 - y)⁻¹) (-(-1) / (1-x)^2) x :=
    ((hasDerivAt_id x).const_sub 1).inv hx
  have he : -(-1:ℝ) / (1-x)^2 = ((1-x)^2)⁻¹ := by simp [one_div]
  rw [he] at hh
  exact hh

lemma complexHessian_negLogOneSub {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (hp : 1 - f p ≠ 0) (i j : Fin 3) :
    complexHessian (fun q => -Real.log (1 - f q)) p i j =
      ((1 - f p)⁻¹ : ℝ) * complexHessian f p i j +
        ((((1 - f p) ^ 2)⁻¹ : ℝ) : ℂ) * dz (fun q => (f q : ℂ)) p i *
          dbar (fun q => (f q : ℂ)) p j := by
  have hρ : ∀ᶠ y in 𝓝 (f p), HasDerivAt (fun y : ℝ => -Real.log (1-y)) ((1-y)⁻¹) y := by
    filter_upwards [((continuousAt_const.sub continuousAt_id).eventually_ne hp)] with y hy
    exact negLogOneSub_hasDerivAt hy
  exact complexHessian_real_comp (ρ := fun y : ℝ => -Real.log (1-y))
    (ρ' := fun y : ℝ => (1-y)⁻¹) hf hρ (invOneSub_hasDerivAt hp) i j

lemma psi_contDiffAt {z : Base} (hz : z ∈ ball) : ContDiffAt ℝ ∞ psi z := by
  have hp : 0 < 1 - ‖z‖ ^ 2 := by
    have h := norm_nonneg z
    change ‖z‖ < 1 at hz
    nlinarith
  exact ((contDiffAt_const.sub (contDiff_norm_sq ℂ).contDiffAt).log hp.ne').neg

lemma dz_dz_comm {f : Ambient → ℂ} {p : Ambient} (hf : ContDiffAt ℝ 2 f p)
    (i j : Fin 3) :
    dz (fun q => dz f q j) p i = dz (fun q => dz f q i) p j := by
  have hs := hf.isSymmSndFDerivAt (by norm_num)
  change (fderiv ℝ (fun q => dz f q j) p (coordVector i) -
    Complex.I * fderiv ℝ (fun q => dz f q j) p (Complex.I • coordVector i)) / 2 =
    (fderiv ℝ (fun q => dz f q i) p (coordVector j) -
    Complex.I * fderiv ℝ (fun q => dz f q i) p (Complex.I • coordVector j)) / 2
  simp only [fderiv_dz_apply hf]
  conv_lhs =>
    rw [hs (coordVector i) (coordVector j), hs (coordVector i) (Complex.I • coordVector j),
      hs (Complex.I • coordVector i) (coordVector j),
      hs (Complex.I • coordVector i) (Complex.I • coordVector j)]
  ring

lemma complexHessian_closed {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 3 f p) (i j k : Fin 3) :
    dz (fun q => complexHessian f q k j) p i =
      dz (fun q => complexHessian f q i j) p k := by
  exact dz_dz_comm (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 2) (by norm_num) j) i k

lemma dz_linear (L : Ambient →L[ℂ] ℂ) (p : Ambient) (i : Fin 3) :
    dz L p i = L (coordVector i) := by
  have hd : fderiv ℝ L p = L.restrictScalars ℝ := (L.restrictScalars ℝ).fderiv
  rw [dz, hd]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  have hI := Complex.I_sq
  linear_combination -L (coordVector i) / 2 * hI

lemma dbar_linear (L : Ambient →L[ℂ] ℂ) (p : Ambient) (i : Fin 3) :
    dbar L p i = 0 := by
  have hd : fderiv ℝ L p = L.restrictScalars ℝ := (L.restrictScalars ℝ).fderiv
  rw [dbar, hd]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  have hI := Complex.I_sq
  linear_combination L (coordVector i) / 2 * hI

lemma dbar_linear_norm_sq (L : Ambient →L[ℂ] ℂ) (p : Ambient) (i : Fin 3) :
    dbar (fun q => (‖L q‖ ^ 2 : ℝ)) p i = L p * star (L (coordVector i)) := by
  have he (q : Ambient) : ((‖L q‖ ^ 2 : ℝ) : ℂ) = L q * star (L q) := by
    simpa only [Complex.normSq_eq_norm_sq, Complex.star_def] using (Complex.mul_conj (L q)).symm
  simp only [he]
  rw [dbar_mul (L.differentiableAt.restrictScalars ℝ) (L.differentiableAt.restrictScalars ℝ).star,
      dbar_linear, dbar_conj (L.differentiableAt.restrictScalars ℝ), dz_linear]
  simp

lemma dz_linear_norm_sq (L : Ambient →L[ℂ] ℂ) (p : Ambient) (i : Fin 3) :
    dz (fun q => (‖L q‖ ^ 2 : ℝ)) p i = star (L p) * L (coordVector i) := by
  have he (q : Ambient) : ((‖L q‖ ^ 2 : ℝ) : ℂ) = L q * star (L q) := by
    simpa only [Complex.normSq_eq_norm_sq, Complex.star_def] using (Complex.mul_conj (L q)).symm
  simp only [he]
  rw [dz_mul (L.differentiableAt.restrictScalars ℝ) (L.differentiableAt.restrictScalars ℝ).star,
      dz_linear, dz_conj (L.differentiableAt.restrictScalars ℝ), dbar_linear]
  simp [mul_comm]

lemma complexHessian_linear_norm_sq (L : Ambient →L[ℂ] ℂ) (p : Ambient) (i j : Fin 3) :
    complexHessian (fun q => ‖L q‖ ^ 2) p i j = L (coordVector i) * star (L (coordVector j)) := by
  unfold complexHessian
  simp only [dbar_linear_norm_sq]
  rw [dz_mul (L.differentiableAt.restrictScalars ℝ) (differentiableAt_const _), dz_linear]
  simp [dz]

private lemma coordCLM_apply (i : Fin 3) (u : Ambient) : coordCLM i u = coordinates u i := rfl

private lemma coordCLM_coordVector (i j : Fin 3) :
    coordCLM i (coordVector j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [coordCLM_apply, coordinates, coordVector]

lemma base_norm_sq_coordinates (p : Ambient) :
    ‖p.1‖ ^ 2 = ‖coordCLM 0 p‖ ^ 2 + ‖coordCLM 1 p‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  rfl

lemma complexHessian_base_norm_sq (p : Ambient) (i j : Fin 3) :
    complexHessian (fun q : Ambient => ‖q.1‖ ^ 2) p i j =
      (if i = 0 then 1 else 0) * (if j = 0 then 1 else 0) +
      (if i = 1 then 1 else 0) * (if j = 1 then 1 else 0) := by
  have hC (k : Fin 3) : ContDiffAt ℝ 2 (fun q => ‖coordCLM k q‖ ^ 2) p :=
    (contDiff_norm_sq ℂ).contDiffAt.comp p ((coordCLM k).contDiff.restrict_scalars ℝ).contDiffAt
  simp only [base_norm_sq_coordinates]
  rw [complexHessian_add (hC 0) (hC 1), complexHessian_linear_norm_sq, complexHessian_linear_norm_sq]
  simp only [coordCLM_coordVector]
  fin_cases i <;> fin_cases j <;> norm_num

lemma dbar_base_norm_sq (p : Ambient) (i : Fin 3) :
    dbar (fun q : Ambient => (‖q.1‖ ^ 2 : ℝ)) p i =
      p.1 0 * (if i = 0 then 1 else 0) + p.1 1 * (if i = 1 then 1 else 0) := by
  have hd (k : Fin 3) : DifferentiableAt ℝ (fun q : Ambient => ((‖coordCLM k q‖ ^ 2 : ℝ) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p (((contDiff_norm_sq ℂ (n := 1)).contDiffAt.comp p ((coordCLM k).contDiff.restrict_scalars ℝ).contDiffAt).differentiableAt (by norm_num))
  simp only [base_norm_sq_coordinates, Complex.ofReal_add]
  rw [dbar_add (hd 0) (hd 1), dbar_linear_norm_sq, dbar_linear_norm_sq]
  simp only [coordCLM_apply]
  fin_cases i <;> simp [coordinates, coordVector]

lemma dz_base_norm_sq (p : Ambient) (i : Fin 3) :
    dz (fun q : Ambient => (‖q.1‖ ^ 2 : ℝ)) p i =
      star (p.1 0) * (if i = 0 then 1 else 0) + star (p.1 1) * (if i = 1 then 1 else 0) := by
  have hd (k : Fin 3) : DifferentiableAt ℝ (fun q : Ambient => ((‖coordCLM k q‖ ^ 2 : ℝ) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p (((contDiff_norm_sq ℂ (n := 1)).contDiffAt.comp p ((coordCLM k).contDiff.restrict_scalars ℝ).contDiffAt).differentiableAt (by norm_num))
  simp only [base_norm_sq_coordinates, Complex.ofReal_add]
  rw [dz_add (hd 0) (hd 1), dz_linear_norm_sq, dz_linear_norm_sq]
  simp only [coordCLM_apply]
  fin_cases i <;> simp [coordinates, coordVector]

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler2074_1 uKahler2080_1 uKahler2312_1 uKahler2472_1

open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

lemma dz_holomorphic {f : Ambient → ℂ} {p : Ambient} (hf : DifferentiableAt ℂ f p)
    (i : Fin 3) : dz f p i = fderiv ℂ f p (coordVector i) := by
  rw [dz, (hf.hasFDerivAt.restrictScalars ℝ).fderiv]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  linear_combination -fderiv ℂ f p (coordVector i) / 2 * Complex.I_sq

lemma dbar_holomorphic {f : Ambient → ℂ} {p : Ambient} (hf : DifferentiableAt ℂ f p)
    (i : Fin 3) : dbar f p i = 0 := by
  rw [dbar, (hf.hasFDerivAt.restrictScalars ℝ).fderiv]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  linear_combination fderiv ℂ f p (coordVector i) / 2 * Complex.I_sq

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

lemma barrier_den_ne_zero {s : ℝ} (hs : s < 0) : 1 - Real.exp s ≠ 0 :=
  ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr hs))

lemma logarithmicBarrier_hasDerivAt {s : ℝ} (hs : s < 0) :
    HasDerivAt logarithmicBarrier (barrierX s) s := by
  have hh := ((hasDerivAt_const s (1 : ℝ)).sub (Real.hasDerivAt_exp s)).log
    (barrier_den_ne_zero hs)
  convert hh.neg using 1 <;> try rfl
  dsimp [barrierX]
  ring

lemma barrierX_hasDerivAt {s : ℝ} (hs : s < 0) :
    HasDerivAt barrierX (barrierQ s) s := by
  convert (Real.hasDerivAt_exp s).div
    ((hasDerivAt_const s (1 : ℝ)).sub (Real.hasDerivAt_exp s)) (barrier_den_ne_zero hs) using 1 <;> try rfl
  dsimp [barrierQ, barrierX]
  field_simp [barrier_den_ne_zero hs]
  ; ring

lemma barrierQ_hasDerivAt {s : ℝ} (hs : s < 0) :
    HasDerivAt barrierQ (barrierThird s) s := by
  convert (barrierX_hasDerivAt hs).mul
    ((hasDerivAt_const s (1 : ℝ)).add (barrierX_hasDerivAt hs)) using 1 <;> try rfl
  dsimp [barrierQ, barrierThird]
  ring

lemma barrierThird_hasDerivAt {s : ℝ} (hs : s < 0) :
    HasDerivAt barrierThird (barrierFourth s) s := by
  convert (barrierQ_hasDerivAt hs).mul
    ((hasDerivAt_const s (1 : ℝ)).add ((barrierX_hasDerivAt hs).const_mul 2)) using 1 <;> try rfl
  dsimp [barrierFourth, barrierThird, barrierQ]
  ring

lemma barrierX_contDiffAt {s : ℝ} (hs : s < 0) : ContDiffAt ℝ ∞ barrierX s :=
  Real.contDiff_exp.contDiffAt.div (contDiffAt_const.sub Real.contDiff_exp.contDiffAt)
    (barrier_den_ne_zero hs)
lemma barrierQ_contDiffAt {s : ℝ} (hs : s < 0) : ContDiffAt ℝ ∞ barrierQ s :=
  (barrierX_contDiffAt hs).mul (contDiffAt_const.add (barrierX_contDiffAt hs))
lemma logarithmicBarrier_contDiffAt {s : ℝ} (hs : s < 0) : ContDiffAt ℝ ∞ logarithmicBarrier s :=
  ((contDiffAt_const.sub Real.contDiff_exp.contDiffAt).log (barrier_den_ne_zero hs)).neg

lemma complexHessian_barrier {s : Ambient → ℝ} {p : Ambient}
    (hs : ContDiffAt ℝ ∞ s p) (hn : s p < 0) (i j : Fin 3) :
    complexHessian (logarithmicBarrier ∘ s) p i j =
      (barrierX (s p) : ℂ) * complexHessian s p i j +
        (barrierQ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p i * dbar (fun q => (s q : ℂ)) p j := by
  apply complexHessian_real_comp (hs.of_le (by exact WithTop.coe_le_coe.mpr le_top))
  · filter_upwards [Iio_mem_nhds hn] with y hy
    exact logarithmicBarrier_hasDerivAt hy
  · exact barrierX_hasDerivAt hn

lemma dz_complexHessian_real_comp {s : Ambient → ℝ} {p : Ambient}
    {ρ₀ ρ₁ ρ₂ ρ₃ : ℝ → ℝ} {V : Set ℝ}
    (hs : ContDiffAt ℝ 3 s p) (hV : IsOpen V) (hp : s p ∈ V)
    (h₀ : ∀ y ∈ V, HasDerivAt ρ₀ (ρ₁ y) y)
    (h₁ : ∀ y ∈ V, HasDerivAt ρ₁ (ρ₂ y) y)
    (h₂ : ∀ y ∈ V, HasDerivAt ρ₂ (ρ₃ y) y) (a c d : Fin 3) :
    dz (fun q => complexHessian (ρ₀ ∘ s) q c d) p a =
      (ρ₁ (s p) : ℂ) * dz (fun q => complexHessian s q c d) p a +
      (ρ₂ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p a * complexHessian s p c d +
      (ρ₂ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p c * complexHessian s p a d +
      (ρ₂ (s p) : ℂ) * dz (fun q => dz (fun r => (s r : ℂ)) q c) p a *
        dbar (fun q => (s q : ℂ)) p d +
      (ρ₃ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p a *
        dz (fun q => (s q : ℂ)) p c * dbar (fun q => (s q : ℂ)) p d := by
  have he : (fun q => complexHessian (ρ₀ ∘ s) q c d) =ᶠ[𝓝 p]
      (fun q => (ρ₁ (s q) : ℂ) * complexHessian s q c d +
       (ρ₂ (s q) : ℂ) * dz (fun r => (s r : ℂ)) q c * dbar (fun r => (s r : ℂ)) q d) := by
    filter_upwards [hs.eventually (by norm_num), hs.continuousAt (hV.mem_nhds hp)] with q hq hnq
    apply complexHessian_real_comp (hq.of_le (by norm_num))
    · filter_upwards [hV.mem_nhds hnq] with y hy
      exact h₀ y hy
    · exact h₁ (s q) hnq
  have hx : DifferentiableAt ℝ (fun q => (ρ₁ (s q) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p ((h₁ (s p) hp).differentiableAt.comp p (hs.differentiableAt (by norm_num)))
  have hq : DifferentiableAt ℝ (fun q => (ρ₂ (s q) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p ((h₂ (s p) hp).differentiableAt.comp p (hs.differentiableAt (by norm_num)))
  have hh : DifferentiableAt ℝ (fun q => complexHessian s q c d) p :=
    ((_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 2) (by norm_num) d) (m := 1) (by norm_num) c) :
      ContDiffAt ℝ 1 _ p).differentiableAt (by norm_num)
  have hz : DifferentiableAt ℝ (fun q => dz (fun r => (s r : ℂ)) q c) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 1) (by norm_num) c).differentiableAt (by norm_num)
  have hb : DifferentiableAt ℝ (fun q => dbar (fun r => (s r : ℂ)) q d) p :=
    (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 1) (by norm_num) d).differentiableAt (by norm_num)
  erw [dz_congr he, dz_add (hx.mul hh) ((hq.mul hz).mul hb), dz_mul hx hh,
    dz_mul (hq.mul hz) hb, dz_mul hq hz,
    dz_real_comp (hs.differentiableAt (by norm_num)) (h₁ (s p) hp),
    dz_real_comp (hs.differentiableAt (by norm_num)) (h₂ (s p) hp)]
  dsimp [complexHessian]
  ring

lemma dbar_dz_complexHessian_real_comp {s : Ambient → ℝ} {p : Ambient}
    {ρ₀ ρ₁ ρ₂ ρ₃ ρ₄ : ℝ → ℝ} {V : Set ℝ}
    (hs : ContDiffAt ℝ 4 s p) (hV : IsOpen V) (hp : s p ∈ V)
    (h₀ : ∀ y ∈ V, HasDerivAt ρ₀ (ρ₁ y) y)
    (h₁ : ∀ y ∈ V, HasDerivAt ρ₁ (ρ₂ y) y)
    (h₂ : ∀ y ∈ V, HasDerivAt ρ₂ (ρ₃ y) y)
    (h₃ : ∀ y ∈ V, HasDerivAt ρ₃ (ρ₄ y) y) (a b c d : Fin 3) :
    dbar (fun q => dz (fun r => complexHessian (ρ₀ ∘ s) r c d) q a) p b =
      (ρ₂ (s p) : ℂ) * dbar (fun q => (s q : ℂ)) p b * dz (fun q => complexHessian s q c d) p a +
      (ρ₁ (s p) : ℂ) * dbar (fun q => dz (fun r => complexHessian s r c d) q a) p b +
      (ρ₃ (s p) : ℂ) * dbar (fun q => (s q : ℂ)) p b * dz (fun q => (s q : ℂ)) p a * complexHessian s p c d +
      (ρ₂ (s p) : ℂ) * dbar (fun q => dz (fun r => (s r : ℂ)) q a) p b * complexHessian s p c d +
      (ρ₂ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p a * dbar (fun q => complexHessian s q c d) p b +
      (ρ₃ (s p) : ℂ) * dbar (fun q => (s q : ℂ)) p b * dz (fun q => (s q : ℂ)) p c * complexHessian s p a d +
      (ρ₂ (s p) : ℂ) * dbar (fun q => dz (fun r => (s r : ℂ)) q c) p b * complexHessian s p a d +
      (ρ₂ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p c * dbar (fun q => complexHessian s q a d) p b +
      (ρ₃ (s p) : ℂ) * dbar (fun q => (s q : ℂ)) p b * dz (fun q => dz (fun r => (s r : ℂ)) q c) p a * dbar (fun q => (s q : ℂ)) p d +
      (ρ₂ (s p) : ℂ) * dbar (fun q => dz (fun r => dz (fun w => (s w : ℂ)) r c) q a) p b * dbar (fun q => (s q : ℂ)) p d +
      (ρ₂ (s p) : ℂ) * dz (fun q => dz (fun r => (s r : ℂ)) q c) p a * dbar (fun q => dbar (fun r => (s r : ℂ)) q d) p b +
      (ρ₄ (s p) : ℂ) * dbar (fun q => (s q : ℂ)) p b * dz (fun q => (s q : ℂ)) p a * dz (fun q => (s q : ℂ)) p c * dbar (fun q => (s q : ℂ)) p d +
      (ρ₃ (s p) : ℂ) * dbar (fun q => dz (fun r => (s r : ℂ)) q a) p b * dz (fun q => (s q : ℂ)) p c * dbar (fun q => (s q : ℂ)) p d +
      (ρ₃ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p a * dbar (fun q => dz (fun r => (s r : ℂ)) q c) p b * dbar (fun q => (s q : ℂ)) p d +
      (ρ₃ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p a * dz (fun q => (s q : ℂ)) p c * dbar (fun q => dbar (fun r => (s r : ℂ)) q d) p b := by
  have he : (fun q => dz (fun r => complexHessian (ρ₀ ∘ s) r c d) q a) =ᶠ[𝓝 p]
      (fun q =>
        (ρ₁ (s q) : ℂ) * dz (fun r => complexHessian s r c d) q a +
        (ρ₂ (s q) : ℂ) * dz (fun r => (s r : ℂ)) q a * complexHessian s q c d +
        (ρ₂ (s q) : ℂ) * dz (fun r => (s r : ℂ)) q c * complexHessian s q a d +
        (ρ₂ (s q) : ℂ) * dz (fun r => dz (fun w => (s w : ℂ)) r c) q a * dbar (fun r => (s r : ℂ)) q d +
        (ρ₃ (s q) : ℂ) * dz (fun r => (s r : ℂ)) q a * dz (fun r => (s r : ℂ)) q c * dbar (fun r => (s r : ℂ)) q d) := by
    filter_upwards [hs.eventually (by norm_num), hs.continuousAt (hV.mem_nhds hp)] with q hq hnq
    exact dz_complexHessian_real_comp (hq.of_le (by norm_num)) hV hnq h₀ h₁ h₂ a c d
  have hd := hs.differentiableAt (by norm_num)
  have hx : DifferentiableAt ℝ (fun q => (ρ₁ (s q) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p ((h₁ (s p) hp).differentiableAt.comp p hd)
  have hq : DifferentiableAt ℝ (fun q => (ρ₂ (s q) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p ((h₂ (s p) hp).differentiableAt.comp p hd)
  have ht : DifferentiableAt ℝ (fun q => (ρ₃ (s q) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p ((h₃ (s p) hp).differentiableAt.comp p hd)
  have hz (i : Fin 3) : DifferentiableAt ℝ (fun q => dz (fun r => (s r : ℂ)) q i) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 1) (by norm_num) i).differentiableAt (by norm_num)
  have hb (i : Fin 3) : DifferentiableAt ℝ (fun q => dbar (fun r => (s r : ℂ)) q i) p :=
    (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 1) (by norm_num) i).differentiableAt (by norm_num)
  have hh (i j : Fin 3) : DifferentiableAt ℝ (fun q => complexHessian s q i j) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 2) (by norm_num) j) (m := 1) (by norm_num) i).differentiableAt (by norm_num)
  have hzz (i j : Fin 3) : DifferentiableAt ℝ (fun q => dz (fun r => dz (fun w => (s w : ℂ)) r i) q j) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 2) (by norm_num) i) (m := 1) (by norm_num) j).differentiableAt (by norm_num)
  have hhz (i j k : Fin 3) : DifferentiableAt ℝ (fun q => dz (fun r => complexHessian s r i j) q k) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 3) (by norm_num) j) (m := 2) (by norm_num) i) (m := 1) (by norm_num) k).differentiableAt (by norm_num)
  rw [dbar_congr he]
  simp (disch := fun_prop) only [dbar_add, dbar_mul]
  rw [dbar_real_comp hd (h₁ (s p) hp),
    dbar_real_comp hd (h₂ (s p) hp), dbar_real_comp hd (h₃ (s p) hp)]
  ring

lemma dz_complexHessian_barrier {s : Ambient → ℝ} {p : Ambient}
    (hs : ContDiffAt ℝ 3 s p) (hn : s p < 0) (a c d : Fin 3) :
    dz (fun q => complexHessian (logarithmicBarrier ∘ s) q c d) p a =
      (barrierX (s p) : ℂ) * dz (fun q => complexHessian s q c d) p a +
      (barrierQ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p a * complexHessian s p c d +
      (barrierQ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p c * complexHessian s p a d +
      (barrierQ (s p) : ℂ) * dz (fun q => dz (fun r => (s r : ℂ)) q c) p a *
        dbar (fun q => (s q : ℂ)) p d +
      (barrierThird (s p) : ℂ) * dz (fun q => (s q : ℂ)) p a *
        dz (fun q => (s q : ℂ)) p c * dbar (fun q => (s q : ℂ)) p d := by
  have he : (fun q => complexHessian (logarithmicBarrier ∘ s) q c d) =ᶠ[𝓝 p]
      (fun q => (barrierX (s q) : ℂ) * complexHessian s q c d +
       (barrierQ (s q) : ℂ) * dz (fun r => (s r : ℂ)) q c * dbar (fun r => (s r : ℂ)) q d) := by
    filter_upwards [hs.eventually (by norm_num), hs.continuousAt (Iio_mem_nhds hn)] with q hq hnq
    apply complexHessian_real_comp (hq.of_le (by norm_num))
    · filter_upwards [Iio_mem_nhds hnq] with y hy
      exact logarithmicBarrier_hasDerivAt hy
    · exact barrierX_hasDerivAt hnq
  have hx := (_root_.OAI.ContDiffAt.hartogs_real_cast (((barrierX_contDiffAt hn).of_le (show (3 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).comp p hs)).differentiableAt (by norm_num)
  have hq := (_root_.OAI.ContDiffAt.hartogs_real_cast (((barrierQ_contDiffAt hn).of_le (show (3 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).comp p hs)).differentiableAt (by norm_num)
  have hh : DifferentiableAt ℝ (fun q => complexHessian s q c d) p :=
    ((_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 2) (by norm_num) d) (m := 1) (by norm_num) c) :
      ContDiffAt ℝ 1 _ p).differentiableAt (by norm_num)
  have hz : DifferentiableAt ℝ (fun q => dz (fun r => (s r : ℂ)) q c) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 1) (by norm_num) c).differentiableAt (by norm_num)
  have hb : DifferentiableAt ℝ (fun q => dbar (fun r => (s r : ℂ)) q d) p :=
    (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 1) (by norm_num) d).differentiableAt (by norm_num)
  erw [dz_congr he, dz_add (hx.mul hh) ((hq.mul hz).mul hb), dz_mul hx hh,
    dz_mul (hq.mul hz) hb, dz_mul hq hz,
    dz_real_comp (hs.differentiableAt (by norm_num)) (barrierX_hasDerivAt hn),
    dz_real_comp (hs.differentiableAt (by norm_num)) (barrierQ_hasDerivAt hn)]
  dsimp [complexHessian]
  ring

lemma dbar_dz_complexHessian_barrier {s : Ambient → ℝ} {p : Ambient}
    (hs : ContDiffAt ℝ 4 s p) (hn : s p < 0) (a b c d : Fin 3) :
    dbar (fun q => dz (fun r => complexHessian (logarithmicBarrier ∘ s) r c d) q a) p b =
      (barrierQ (s p) : ℂ) * dbar (fun q => (s q : ℂ)) p b * dz (fun q => complexHessian s q c d) p a +
      (barrierX (s p) : ℂ) * dbar (fun q => dz (fun r => complexHessian s r c d) q a) p b +
      (barrierThird (s p) : ℂ) * dbar (fun q => (s q : ℂ)) p b * dz (fun q => (s q : ℂ)) p a * complexHessian s p c d +
      (barrierQ (s p) : ℂ) * dbar (fun q => dz (fun r => (s r : ℂ)) q a) p b * complexHessian s p c d +
      (barrierQ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p a * dbar (fun q => complexHessian s q c d) p b +
      (barrierThird (s p) : ℂ) * dbar (fun q => (s q : ℂ)) p b * dz (fun q => (s q : ℂ)) p c * complexHessian s p a d +
      (barrierQ (s p) : ℂ) * dbar (fun q => dz (fun r => (s r : ℂ)) q c) p b * complexHessian s p a d +
      (barrierQ (s p) : ℂ) * dz (fun q => (s q : ℂ)) p c * dbar (fun q => complexHessian s q a d) p b +
      (barrierThird (s p) : ℂ) * dbar (fun q => (s q : ℂ)) p b * dz (fun q => dz (fun r => (s r : ℂ)) q c) p a * dbar (fun q => (s q : ℂ)) p d +
      (barrierQ (s p) : ℂ) * dbar (fun q => dz (fun r => dz (fun w => (s w : ℂ)) r c) q a) p b * dbar (fun q => (s q : ℂ)) p d +
      (barrierQ (s p) : ℂ) * dz (fun q => dz (fun r => (s r : ℂ)) q c) p a * dbar (fun q => dbar (fun r => (s r : ℂ)) q d) p b +
      (barrierFourth (s p) : ℂ) * dbar (fun q => (s q : ℂ)) p b * dz (fun q => (s q : ℂ)) p a * dz (fun q => (s q : ℂ)) p c * dbar (fun q => (s q : ℂ)) p d +
      (barrierThird (s p) : ℂ) * dbar (fun q => dz (fun r => (s r : ℂ)) q a) p b * dz (fun q => (s q : ℂ)) p c * dbar (fun q => (s q : ℂ)) p d +
      (barrierThird (s p) : ℂ) * dz (fun q => (s q : ℂ)) p a * dbar (fun q => dz (fun r => (s r : ℂ)) q c) p b * dbar (fun q => (s q : ℂ)) p d +
      (barrierThird (s p) : ℂ) * dz (fun q => (s q : ℂ)) p a * dz (fun q => (s q : ℂ)) p c * dbar (fun q => dbar (fun r => (s r : ℂ)) q d) p b := by
  have he : (fun q => dz (fun r => complexHessian (logarithmicBarrier ∘ s) r c d) q a) =ᶠ[𝓝 p]
      (fun q =>
        (barrierX (s q) : ℂ) * dz (fun r => complexHessian s r c d) q a +
        (barrierQ (s q) : ℂ) * dz (fun r => (s r : ℂ)) q a * complexHessian s q c d +
        (barrierQ (s q) : ℂ) * dz (fun r => (s r : ℂ)) q c * complexHessian s q a d +
        (barrierQ (s q) : ℂ) * dz (fun r => dz (fun w => (s w : ℂ)) r c) q a * dbar (fun r => (s r : ℂ)) q d +
        (barrierThird (s q) : ℂ) * dz (fun r => (s r : ℂ)) q a * dz (fun r => (s r : ℂ)) q c * dbar (fun r => (s r : ℂ)) q d) := by
    filter_upwards [hs.eventually (by norm_num), hs.continuousAt (Iio_mem_nhds hn)] with q hq hnq
    exact dz_complexHessian_barrier (hq.of_le (by norm_num)) hnq a c d
  have hd := hs.differentiableAt (by norm_num)
  have hx : DifferentiableAt ℝ (fun q => (barrierX (s q) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p ((barrierX_hasDerivAt hn).differentiableAt.comp p hd)
  have hq : DifferentiableAt ℝ (fun q => (barrierQ (s q) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p ((barrierQ_hasDerivAt hn).differentiableAt.comp p hd)
  have ht : DifferentiableAt ℝ (fun q => (barrierThird (s q) : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p ((barrierThird_hasDerivAt hn).differentiableAt.comp p hd)
  have hz (i : Fin 3) : DifferentiableAt ℝ (fun q => dz (fun r => (s r : ℂ)) q i) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 1) (by norm_num) i).differentiableAt (by norm_num)
  have hb (i : Fin 3) : DifferentiableAt ℝ (fun q => dbar (fun r => (s r : ℂ)) q i) p :=
    (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 1) (by norm_num) i).differentiableAt (by norm_num)
  have hh (i j : Fin 3) : DifferentiableAt ℝ (fun q => complexHessian s q i j) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 2) (by norm_num) j) (m := 1) (by norm_num) i).differentiableAt (by norm_num)
  have hzz (i j : Fin 3) : DifferentiableAt ℝ (fun q => dz (fun r => dz (fun w => (s w : ℂ)) r i) q j) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 2) (by norm_num) i) (m := 1) (by norm_num) j).differentiableAt (by norm_num)
  have hhz (i j k : Fin 3) : DifferentiableAt ℝ (fun q => dz (fun r => complexHessian s r i j) q k) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 3) (by norm_num) j) (m := 2) (by norm_num) i) (m := 1) (by norm_num) k).differentiableAt (by norm_num)
  rw [dbar_congr he]
  simp (disch := fun_prop) only [dbar_add, dbar_mul]
  rw [dbar_real_comp hd (barrierX_hasDerivAt hn),
    dbar_real_comp hd (barrierQ_hasDerivAt hn), dbar_real_comp hd (barrierThird_hasDerivAt hn)]
  ring

lemma dbar_dz_real_eq_hessian {s : Ambient → ℝ} {p : Ambient}
    (hs : ContDiffAt ℝ 2 s p) (a b : Fin 3) :
    dbar (fun q => dz (fun r => (s r : ℂ)) q a) p b = complexHessian s p a b :=
  (dz_dbar_comm (_root_.OAI.ContDiffAt.hartogs_real_cast hs) a b).symm

lemma dz_dz_base_norm_sq (p : Ambient) (a c : Fin 3) :
    dz (fun q => dz (fun r : Ambient => (‖r.1‖ ^ 2 : ℝ)) q c) p a = 0 := by
  have he (q : Ambient) : dz (fun r : Ambient => (‖r.1‖ ^ 2 : ℝ)) q c =
      star (q.1 0 * (if c = 0 then 1 else 0) + q.1 1 * (if c = 1 then 1 else 0)) := by
    rw [dz_base_norm_sq]
    simp only [star_add, star_mul']
    split_ifs <;> simp
  simp only [he]
  have hd : DifferentiableAt ℂ (fun q : Ambient => q.1 0 * (if c = 0 then 1 else 0) +
      q.1 1 * (if c = 1 then 1 else 0)) p := by fun_prop
  rw [dz_conj (hd.restrictScalars ℝ) a, dbar_holomorphic hd, star_zero]

lemma inverseSquare_hasDerivAt {s : ℝ} (hs : 1 - s ≠ 0) :
    HasDerivAt (fun y : ℝ => (1 - y)⁻¹ ^ 2) (inverseCube s) s := by
  refine ((invOneSub_hasDerivAt hs).pow 2).congr_deriv ?_
  dsimp [inverseCube]
  field_simp
  try ring
lemma inverseCube_hasDerivAt {s : ℝ} (hs : 1 - s ≠ 0) :
    HasDerivAt inverseCube (inverseFourth s) s := by
  have hh := ((invOneSub_hasDerivAt hs).pow 3).const_mul 2
  have he : inverseCube = fun y : ℝ => 2 * ((1 - y)⁻¹ ^ 3) := by
    funext y
    simp [inverseCube, div_eq_mul_inv, inv_pow]
  rw [he]
  refine hh.congr_deriv ?_
  dsimp [inverseFourth]
  field_simp
  try ring

lemma psi_hessian_center (w : ℂ) (i j : Fin 3) :
    complexHessian (fun q : Ambient => psi q.1) (0,w) i j = horizontalIdentity i j := by
  rw [show (fun q : Ambient => psi q.1) =
    (fun q : Ambient => -Real.log (1 - ‖q.1‖ ^ 2)) by rfl]
  rw [complexHessian_negLogOneSub]
  · simp only [complexHessian_base_norm_sq, dz_base_norm_sq, dbar_base_norm_sq]
    simp [horizontalIdentity]
  · exact (contDiff_norm_sq ℂ).contDiffAt.comp _ contDiffAt_fst
  · simp

lemma psi_third_center (w : ℂ) (a c d : Fin 3) :
    dz (fun q => complexHessian (fun r : Ambient => psi r.1) q c d) (0,w) a = 0 := by
  have hh := dz_complexHessian_real_comp
    (s := fun q : Ambient => ‖q.1‖ ^ 2)
    (ρ₀ := fun y => -Real.log (1-y)) (ρ₁ := fun y => (1-y)⁻¹)
    (ρ₂ := fun y => (1-y)⁻¹ ^ 2) (ρ₃ := inverseCube)
    ((contDiff_norm_sq ℂ).contDiffAt.comp (0,w) contDiffAt_fst)
    (V := Iio 1) isOpen_Iio (by simp)
    (fun y hy => negLogOneSub_hasDerivAt (ne_of_gt (sub_pos.mpr hy)))
    (fun y hy => by simpa only [inv_pow] using invOneSub_hasDerivAt (ne_of_gt (sub_pos.mpr hy)))
    (fun y hy => inverseSquare_hasDerivAt (ne_of_gt (sub_pos.mpr hy))) a c d
  change dz (fun q => complexHessian (fun r : Ambient => -Real.log (1-‖r.1‖^2)) q c d) (0,w) a = _
  erw [hh]
  simp only [dz_dz_base_norm_sq]
  simp only [complexHessian_base_norm_sq, dz_base_norm_sq, dbar_base_norm_sq]
  simp [dz]

lemma psi_fourth_center (w : ℂ) (a b c d : Fin 3) :
    dbar (fun q => dz (fun r => complexHessian (fun v : Ambient => psi v.1) r c d) q a) (0,w) b =
      horizontalIdentity a b * horizontalIdentity c d + horizontalIdentity c b * horizontalIdentity a d := by
  have hs : ContDiffAt ℝ 4 (fun q : Ambient => ‖q.1‖ ^ 2) (0,w) :=
    (contDiff_norm_sq ℂ).contDiffAt.comp (0,w) contDiffAt_fst
  have hh := dbar_dz_complexHessian_real_comp
    (s := fun q : Ambient => ‖q.1‖ ^ 2)
    (ρ₀ := fun y => -Real.log (1-y)) (ρ₁ := fun y => (1-y)⁻¹)
    (ρ₂ := fun y => (1-y)⁻¹ ^ 2) (ρ₃ := inverseCube) (ρ₄ := inverseFourth)
    hs (V := Iio 1) isOpen_Iio (by simp)
    (fun y hy => negLogOneSub_hasDerivAt (ne_of_gt (sub_pos.mpr hy)))
    (fun y hy => by simpa only [inv_pow] using invOneSub_hasDerivAt (ne_of_gt (sub_pos.mpr hy)))
    (fun y hy => inverseSquare_hasDerivAt (ne_of_gt (sub_pos.mpr hy)))
    (fun y hy => inverseCube_hasDerivAt (ne_of_gt (sub_pos.mpr hy))) a b c d
  change dbar (fun q => dz (fun r => complexHessian (fun v : Ambient => -Real.log (1-‖v.1‖^2)) r c d) q a) (0,w) b = _
  erw [hh]
  erw [dbar_dz_real_eq_hessian (hs.of_le (by norm_num)) a b,
    dbar_dz_real_eq_hessian (hs.of_le (by norm_num)) c b]
  simp only [dz_dz_base_norm_sq]
  simp only [complexHessian_base_norm_sq, dz_base_norm_sq, dbar_base_norm_sq]
  simp [horizontalIdentity, dz, dbar]

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsGauge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

lemma dz_re_holomorphic {f : Ambient → ℂ} {p : Ambient}
    (hf : DifferentiableAt ℂ f p) (i : Fin 3) :
    dz (fun q => ((f q).re : ℂ)) p i = dz f p i / 2 := by
  have he : (fun q => ((f q).re : ℂ)) = fun q => (1/2 : ℂ) * (f q + star (f q)) := by
    funext q
    rw [Complex.re_eq_add_conj]
    change (f q + star (f q)) / 2 = _
    ring
  have hc : DifferentiableAt ℝ (fun q => star (f q)) p :=
    Complex.conjCLE.toContinuousLinearMap.differentiableAt.comp p (hf.restrictScalars ℝ)
  rw [he]
  erw [dz_const_mul ((hf.restrictScalars ℝ).add hc),
    dz_add (hf.restrictScalars ℝ) hc,
    dz_conj (hf.restrictScalars ℝ), dbar_holomorphic hf, star_zero, add_zero]
  ring

lemma dbar_re_holomorphic {f : Ambient → ℂ} {p : Ambient}
    (hf : DifferentiableAt ℂ f p) (i : Fin 3) :
    dbar (fun q => ((f q).re : ℂ)) p i = star (dz f p i) / 2 := by
  erw [dbar_eq_star_dz_real (Complex.reCLM.differentiableAt.comp p (hf.restrictScalars ℝ)), dz_re_holomorphic hf]
  simp

lemma dz_analyticAt {f : Ambient → ℂ} {p : Ambient}
    (hf : AnalyticAt ℂ f p) (i : Fin 3) : AnalyticAt ℂ (fun q => dz f q i) p := by
  have he : (fun q => dz f q i) =ᶠ[𝓝 p] (fun q => fderiv ℂ f q (coordVector i)) := by
    filter_upwards [hf.eventually_analyticAt] with q hq
    exact dz_holomorphic hq.differentiableAt i
  exact (((ContinuousLinearMap.apply ℂ ℂ (coordVector i)).analyticAt _).comp hf.fderiv).congr he.symm

lemma complexHessian_re_holomorphic {f : Ambient → ℂ} {p : Ambient}
    (hf : AnalyticAt ℂ f p) (i j : Fin 3) :
    complexHessian (fun q => (f q).re) p i j = 0 := by
  have he : (fun q => dbar (fun r => ((f r).re : ℂ)) q j) =ᶠ[𝓝 p]
      (fun q => (1/2 : ℂ) * star (dz f q j)) := by
    filter_upwards [hf.eventually_analyticAt] with q hq
    rw [dbar_re_holomorphic hq.differentiableAt]
    ring
  have hc : DifferentiableAt ℝ (fun q => star (dz f q j)) p :=
    Complex.conjCLE.toContinuousLinearMap.differentiableAt.comp p
      ((dz_analyticAt hf j).differentiableAt.restrictScalars ℝ)
  unfold complexHessian
  rw [dz_congr he, dz_const_mul hc,
    dz_conj ((dz_analyticAt hf j).differentiableAt.restrictScalars ℝ),
    dbar_holomorphic (dz_analyticAt hf j).differentiableAt, star_zero, mul_zero]

lemma complexHessian_gauge {f : Ambient → ℝ} {P : Ambient → ℂ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (hP : AnalyticAt ℂ P p) :
    complexHessian (fun q => f q - 2*(P q).re) p = complexHessian f p := by
  have hr : ContDiffAt ℝ 2 (fun q => (P q).re) p :=
    Complex.reCLM.contDiff.contDiffAt.comp p (hP.contDiffAt.restrict_scalars ℝ)
  have he : (fun q => f q - 2*(P q).re) = fun q => f q + (-2)*(P q).re := by
    funext q; ring
  rw [he]
  ext i j
  rw [complexHessian_add hf (contDiffAt_const.mul hr),
    complexHessian_const_mul hr, complexHessian_re_holomorphic hP]
  simp

lemma dz_horizontal (p : Ambient) (i : Fin 2) (j : Fin 3) :
    dz (fun q : Ambient => q.1 i) p j = if j = i.castSucc then 1 else 0 := by
  exact (dz_linear (horizontalCoordinate i) p j).trans (horizontalCoordinate_coordVector i j)

lemma gaugePolynomial_analytic (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ) :
    AnalyticOnNhd ℂ (gaugePolynomial a B) univ := by
  intro p hp
  have h (i : Fin 2) : AnalyticAt ℂ (fun q : Ambient => q.1 i) p :=
    (horizontalCoordinate i).analyticAt p
  unfold gaugePolynomial
  simp only [Fin.sum_univ_two]
  exact ((analyticAt_const.mul (h 0)).add (analyticAt_const.mul (h 1))).add
    (analyticAt_const.mul
      ((((analyticAt_const.mul (h 0)).mul (h 0)).add ((analyticAt_const.mul (h 0)).mul (h 1))).add
       (((analyticAt_const.mul (h 1)).mul (h 0)).add ((analyticAt_const.mul (h 1)).mul (h 1)))))

lemma dz_gaugePolynomial (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ) (p : Ambient)
    (j : Fin 3) :
    dz (gaugePolynomial a B) p j =
      (∑ i, a i * (if j = i.castSucc then 1 else 0)) +
      (1/2 : ℂ) * ∑ i, ∑ k, B i k *
        ((if j = i.castSucc then 1 else 0) * p.1 k + p.1 i * (if j = k.castSucc then 1 else 0)) := by
  unfold gaugePolynomial
  simp only [Fin.sum_univ_two]
  simp (disch := fun_prop) only [dz_add, dz_const_mul, dz_mul, dz_horizontal]
  ring

lemma dz_gaugePolynomial_center (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ) (w : ℂ)
    (i : Fin 2) : dz (gaugePolynomial a B) (0,w) i.castSucc = a i := by
  rw [dz_gaugePolynomial]
  fin_cases i <;> simp [Fin.sum_univ_two]

lemma dz_dz_gaugePolynomial (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ)
    (hB : ∀ i k, B i k = B k i) (p : Ambient) (i k : Fin 2) :
    dz (fun q => dz (gaugePolynomial a B) q k.castSucc) p i.castSucc = B i k := by
  simp only [dz_gaugePolynomial, Fin.sum_univ_two]
  fin_cases i <;> fin_cases k <;>
    simp (disch := fun_prop) only [Fin.reduceFinMk, ↓reduceIte,
      one_mul, mul_one, dz_add, dz_const_mul,
      dz_horizontal]
  all_goals try simp [dz]
  all_goals try rw [hB 0 1]
  all_goals ring

lemma dz_sub {f g : Ambient → ℂ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (i : Fin 3) :
    dz (fun q => f q - g q) p i = dz f p i - dz g p i := by
  simp only [dz, fderiv_fun_sub hf hg, sub_apply]
  ring

lemma dz_gauge {f : Ambient → ℝ} {P : Ambient → ℂ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hP : DifferentiableAt ℂ P p) (i : Fin 3) :
    dz (fun q => (f q - 2*(P q).re : ℝ)) p i =
      dz (fun q => (f q : ℂ)) p i - dz P p i := by
  have hd : DifferentiableAt ℝ (fun q => ((P q).re : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p (Complex.reCLM.differentiableAt.comp p (hP.restrictScalars ℝ))
  have hf' : DifferentiableAt ℝ (fun q => (f q : ℂ)) p := Complex.ofRealCLM.differentiableAt.comp p hf
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [dz_sub hf' (hd.const_mul 2), dz_const_mul hd, dz_re_holomorphic hP]
  ring

lemma dz_dz_gauge {f : Ambient → ℝ} {P : Ambient → ℂ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (hP : AnalyticAt ℂ P p) (i k : Fin 3) :
    dz (fun q => dz (fun r => (f r - 2*(P r).re : ℝ)) q k) p i =
      dz (fun q => dz (fun r => (f r : ℂ)) q k) p i - dz (fun q => dz P q k) p i := by
  have he : (fun q => dz (fun r => (f r - 2*(P r).re : ℝ)) q k) =ᶠ[𝓝 p]
      (fun q => dz (fun r => (f r : ℂ)) q k - dz P q k) := by
    filter_upwards [hf.eventually (by norm_num), hP.eventually_analyticAt] with q hfq hPq
    exact dz_gauge (hfq.differentiableAt (by norm_num)) hPq.differentiableAt k
  rw [dz_congr he, dz_sub ((_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 1) (by norm_num) k).differentiableAt (by norm_num))
    ((dz_analyticAt hP k).differentiableAt.restrictScalars ℝ)]

lemma secondGaugeJet_symm {f : Ambient → ℝ} {p : Ambient} (hf : ContDiffAt ℝ 2 f p)
    (i k : Fin 2) : secondGaugeJet f p i k = secondGaugeJet f p k i :=
  dz_dz_comm (_root_.OAI.ContDiffAt.hartogs_real_cast hf) i.castSucc k.castSucc

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsNormalJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

lemma _root_.OAI.ContDiffAt.hartogs_dzBase {f : Base → ℂ} {p : Base} {m n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f p) (hmn : m + 1 ≤ n) (i : Fin 2) :
    ContDiffAt ℝ m (fun q => dzBase f q i) p := by
  have hd := hf.fderiv_right hmn
  unfold PinchedHartogs.dzBase
  exact ((hd.clm_apply contDiffAt_const).sub
    (contDiffAt_const.mul (hd.clm_apply contDiffAt_const))).div_const 2

lemma dz_dz_lift_base {f : Base → ℂ} {p : Ambient} (hf : ContDiffAt ℝ 2 f p.1)
    (a c : Fin 3) :
    dz (fun q => dz (fun r : Ambient => f r.1) q c) p a =
      !![dzBase (fun z => dzBase f z 0) p.1 0, dzBase (fun z => dzBase f z 1) p.1 0, 0;
         dzBase (fun z => dzBase f z 0) p.1 1, dzBase (fun z => dzBase f z 1) p.1 1, 0;
         0,0,0] a c := by
  have he : (fun q => dz (fun r : Ambient => f r.1) q c) =ᶠ[𝓝 p]
      (fun q => ![dzBase f q.1 0, dzBase f q.1 1, 0] c) := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds (hf.eventually (by norm_num))] with q hq
    change ContDiffAt ℝ 2 f q.1 at hq
    exact dz_lift_base (hq.differentiableAt (by norm_num)) c
  rw [dz_congr he]
  have hd (i : Fin 2) := (_root_.OAI.ContDiffAt.hartogs_dzBase hf (m := 1) (by norm_num) i).differentiableAt (by norm_num)
  fin_cases a <;> fin_cases c
  all_goals first
    | exact dz_lift_base (hd 0) _
    | exact dz_lift_base (hd 1) _
    | simp [dz]

lemma dz_gaugePolynomial_vertical (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ) (p : Ambient) :
    dz (gaugePolynomial a B) p 2 = 0 := by
  rw [dz_gaugePolynomial]
  simp [Fin.sum_univ_two]

lemma dz_dz_gaugePolynomial_vertical_right (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ)
    (p : Ambient) (i : Fin 3) : dz (fun q => dz (gaugePolynomial a B) q 2) p i = 0 := by
  simp only [dz_gaugePolynomial_vertical]
  simp [dz]

lemma dz_dz_gaugePolynomial_vertical_left (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ)
    (p : Ambient) (i : Fin 3) : dz (fun q => dz (gaugePolynomial a B) q i) p 2 = 0 := by
  rw [dz_dz_comm ((gaugePolynomial_analytic a B p (mem_univ p)).contDiffAt.restrict_scalars ℝ)]
  exact dz_dz_gaugePolynomial_vertical_right a B p i

lemma dz_dz_gaugePolynomial_all (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ)
    (hB : ∀ i k, B i k = B k i) (p : Ambient) (i k : Fin 3) :
    dz (fun q => dz (gaugePolynomial a B) q k) p i =
      !![B 0 0, B 0 1, 0; B 1 0, B 1 1, 0; 0,0,0] i k := by
  fin_cases i <;> fin_cases k
  · exact dz_dz_gaugePolynomial a B hB p 0 0
  · exact dz_dz_gaugePolynomial a B hB p 0 1
  · exact dz_dz_gaugePolynomial_vertical_right a B p 0
  · exact dz_dz_gaugePolynomial a B hB p 1 0
  · exact dz_dz_gaugePolynomial a B hB p 1 1
  · exact dz_dz_gaugePolynomial_vertical_right a B p 1
  · exact dz_dz_gaugePolynomial_vertical_left a B p 0
  · exact dz_dz_gaugePolynomial_vertical_left a B p 1
  · exact dz_dz_gaugePolynomial_vertical_right a B p 2

lemma baseGaugePolynomial_analytic (f : Base → ℝ) (w : ℂ) (q : Ambient) :
    AnalyticAt ℂ (baseGaugePolynomial f w) q := gaugePolynomial_analytic _ _ q (mem_univ _)

lemma normalLogWeight_contDiffAt {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ ∞ f q.1) (w : ℂ) : ContDiffAt ℝ ∞ (normalLogWeight f w) q := by
  have hP : AnalyticAt ℂ (fun q => baseGaugePolynomial f w q - q.2) q :=
    (baseGaugePolynomial_analytic f w q).sub ((ContinuousLinearMap.snd ℂ Base ℂ).analyticAt q)
  exact (hf.comp q contDiffAt_fst).sub
    (contDiffAt_const.mul (Complex.reCLM.contDiff.contDiffAt.comp q (hP.contDiffAt.restrict_scalars ℝ)))

lemma normalLogWeight_hessian {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (w : ℂ) :
    complexHessian (normalLogWeight f w) q = complexHessian (fun q : Ambient => f q.1) q :=
  complexHessian_gauge (hf.comp q contDiffAt_fst)
    ((baseGaugePolynomial_analytic f w q).sub ((ContinuousLinearMap.snd ℂ Base ℂ).analyticAt q))

lemma normalLogWeight_first {f : Base → ℝ} (hf : ContDiffAt ℝ 2 f 0) (w : ℂ) (i : Fin 3) :
    dz (fun q => (normalLogWeight f w q : ℂ)) (0,w) i = if i = 2 then 1 else 0 := by
  have hP := (baseGaugePolynomial_analytic f w (0,w)).differentiableAt
  have hv := (ContinuousLinearMap.snd ℂ Base ℂ).differentiableAt (x := (0,w))
  have hf' : DifferentiableAt ℝ (fun q : Ambient => f q.1) (0,w) :=
    (hf.differentiableAt (by norm_num)).comp (0,w) differentiableAt_fst
  unfold normalLogWeight
  erw [dz_gauge hf' (hP.sub hv), dz_sub (hP.restrictScalars ℝ) (hv.restrictScalars ℝ), dz_fiber]
  change dz (fun q : Ambient => (f q.1 : ℂ)) (0,w) i -
    (dz (gaugePolynomial _ _) (0,w) i - (if i = 2 then 1 else 0)) = _
  fin_cases i
  · erw [dz_gaugePolynomial_center _ _ w 0]
    simp [firstGaugeJet]
  · erw [dz_gaugePolynomial_center _ _ w 1]
    simp [firstGaugeJet]
  · have hfc : DifferentiableAt ℝ (fun z => (f z : ℂ)) (0,w).1 :=
      Complex.ofRealCLM.differentiableAt.comp 0 (hf.differentiableAt (by norm_num))
    rw [dz_lift_base hfc, dz_gaugePolynomial]
    simp [Fin.sum_univ_two]

lemma normalLogWeight_pureSecond {f : Base → ℝ} (hf : ContDiffAt ℝ 2 f 0)
    (w : ℂ) (i k : Fin 3) :
    dz (fun q => dz (fun r => (normalLogWeight f w r : ℂ)) q k) (0,w) i = 0 := by
  have hL : ContDiffAt ℝ 2 (fun q : Ambient => f q.1) (0,w) := hf.comp (0,w) contDiffAt_fst
  have hP := baseGaugePolynomial_analytic f w (0,w)
  have hv : AnalyticAt ℂ (fun q : Ambient => q.2) (0,w) :=
    (ContinuousLinearMap.snd ℂ Base ℂ).analyticAt _
  have he : (fun q => dz (fun r => baseGaugePolynomial f w r - r.2) q k) =
      (fun q => dz (baseGaugePolynomial f w) q k - if k = 2 then 1 else 0) := by
    funext q
    erw [dz_sub ((baseGaugePolynomial_analytic f w q).differentiableAt.restrictScalars ℝ)
      (ContinuousLinearMap.snd ℝ Base ℂ).differentiableAt, dz_fiber]
  unfold normalLogWeight
  erw [dz_dz_gauge hL (hP.sub hv), he,
    dz_sub ((dz_analyticAt hP k).differentiableAt.restrictScalars ℝ) (differentiableAt_const _)]
  have hc : dz (fun _ : Ambient => if k = 2 then (1 : ℂ) else 0) (0,w) i = 0 := by simp [dz]
  rw [hc, sub_zero]
  change dz (fun q => dz (fun r : Ambient => (f r.1 : ℂ)) q k) (0,w) i -
    dz (fun q => dz (baseGaugePolynomial f w) q k) (0,w) i = 0
  rw [baseGaugePolynomial, dz_dz_gaugePolynomial_all _ _ (secondGaugeJet_symm hL)]
  have hfc : ContDiffAt ℝ 2 (fun z => (f z : ℂ)) 0 := Complex.ofRealCLM.contDiff.contDiffAt.comp 0 hf
  have hdd (a c : Fin 3) := dz_dz_lift_base (p := (0,w)) hfc a c
  simp only [secondGaugeJet, hdd]
  fin_cases i <;> fin_cases k <;> simp

lemma normalLogWeight_hessian_eventually {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0) (w : ℂ) :
    complexHessian (normalLogWeight f w) =ᶠ[𝓝 (0,w)] complexHessian (fun q : Ambient => f q.1) := by
  have he : ∀ᶠ z in 𝓝 (0 : Base), ContDiffAt ℝ 2 f z := (hf.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).eventually (by norm_num)
  filter_upwards [continuousAt_fst.preimage_mem_nhds he] with q hq
  change ContDiffAt ℝ 2 f q.1 at hq
  exact normalLogWeight_hessian hq w

lemma dbar_dz_dz_real {s : Ambient → ℝ} {p : Ambient}
    (hs : ContDiffAt ℝ 3 s p) (a b c : Fin 3) :
    dbar (fun q => dz (fun r => dz (fun t => (s t : ℂ)) r c) q a) p b =
      dz (fun q => complexHessian s q c b) p a := by
  rw [← dz_dbar_comm (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 2) (by norm_num) c)]
  apply dz_congr
  filter_upwards [hs.eventually (by norm_num)] with q hq
  exact dbar_dz_real_eq_hessian (hq.of_le (by norm_num)) c b

lemma dbar_dbar_real {s : Ambient → ℝ} {p : Ambient}
    (hs : ContDiffAt ℝ 2 s p) (a b : Fin 3) :
    dbar (fun q => dbar (fun r => (s r : ℂ)) q a) p b =
      star (dz (fun q => dz (fun r => (s r : ℂ)) q a) p b) := by
  have he : (fun q => dbar (fun r => (s r : ℂ)) q a) =ᶠ[𝓝 p]
      (fun q => star (dz (fun r => (s r : ℂ)) q a)) := by
    filter_upwards [hs.eventually (by norm_num)] with q hq
    exact dbar_eq_star_dz_real (hq.differentiableAt (by norm_num)) a
  rw [dbar_congr he]
  exact dbar_conj ((_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_real_cast hs) (m := 1) (by norm_num) a).differentiableAt (by norm_num)) b

lemma normalLogWeight_barFirst {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (w : ℂ) (i : Fin 3) :
    dbar (fun q => (normalLogWeight f w q : ℂ)) (0,w) i = if i = 2 then 1 else 0 := by
  rw [dbar_eq_star_dz_real ((normalLogWeight_contDiffAt hf w).differentiableAt (by simp)),
    normalLogWeight_first (hf.of_le (WithTop.coe_le_coe.mpr le_top))]
  split_ifs <;> simp

lemma normalLogWeight_pureBarSecond {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (w : ℂ) (i k : Fin 3) :
    dbar (fun q => dbar (fun r => (normalLogWeight f w r : ℂ)) q k) (0,w) i = 0 := by
  rw [dbar_dbar_real ((normalLogWeight_contDiffAt hf w).of_le (WithTop.coe_le_coe.mpr le_top)),
    normalLogWeight_pureSecond (hf.of_le (WithTop.coe_le_coe.mpr le_top)), star_zero]

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsNormalTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

lemma dbar_dz_congr {f g : Ambient → ℂ} {p : Ambient} (h : f =ᶠ[𝓝 p] g) (i j : Fin 3) :
    dbar (fun q => dz f q i) p j = dbar (fun q => dz g q i) p j := by
  apply dbar_congr
  filter_upwards [h.eventuallyEq_nhds] with q hq
  exact dz_congr hq i

lemma normalLogWeight_third {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (w : ℂ) (a c d : Fin 3) :
    dz (fun q => complexHessian (normalLogWeight f w) q c d) (0,w) a =
      liftedThird f (0,w) a c d := by
  apply dz_congr
  filter_upwards [normalLogWeight_hessian_eventually hf w] with q hq
  exact congrFun (congrFun hq c) d

lemma normalLogWeight_barThird {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (w : ℂ) (b c d : Fin 3) :
    dbar (fun q => complexHessian (normalLogWeight f w) q c d) (0,w) b =
      liftedBarThird f (0,w) b c d := by
  apply dbar_congr
  filter_upwards [normalLogWeight_hessian_eventually hf w] with q hq
  exact congrFun (congrFun hq c) d

lemma normalLogWeight_fourth {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (w : ℂ) (a b c d : Fin 3) :
    dbar (fun q => dz (fun r => complexHessian (normalLogWeight f w) r c d) q a) (0,w) b =
      liftedFourth f (0,w) a b c d := by
  apply dbar_dz_congr
  filter_upwards [normalLogWeight_hessian_eventually hf w] with q hq
  exact congrFun (congrFun hq c) d

lemma normalBarrier_hessian {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) (i j : Fin 3) :
    complexHessian (logarithmicBarrier ∘ normalLogWeight f w) (0,w) i j =
      (barrierX (normalLogWeight f w (0,w)) : ℂ) * liftedHessian f (0,w) i j +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * verticalDelta i * verticalDelta j := by
  rw [complexHessian_barrier (normalLogWeight_contDiffAt (q := (0,w)) hf w) hn,
    normalLogWeight_first (hf.of_le (WithTop.coe_le_coe.mpr le_top)), normalLogWeight_barFirst hf,
    normalLogWeight_hessian (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top))]
  rfl

lemma normalBarrier_third {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) (a c d : Fin 3) :
    dz (fun q => complexHessian (logarithmicBarrier ∘ normalLogWeight f w) q c d) (0,w) a =
      (barrierX (normalLogWeight f w (0,w)) : ℂ) * liftedThird f (0,w) a c d +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * verticalDelta a * liftedHessian f (0,w) c d +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * verticalDelta c * liftedHessian f (0,w) a d +
      (barrierThird (normalLogWeight f w (0,w)) : ℂ) * verticalDelta a * verticalDelta c * verticalDelta d := by
  rw [dz_complexHessian_barrier ((normalLogWeight_contDiffAt (q := (0,w)) hf w).of_le (WithTop.coe_le_coe.mpr le_top)) hn]
  simp only [normalLogWeight_first (hf.of_le (WithTop.coe_le_coe.mpr le_top)), normalLogWeight_barFirst hf,
    normalLogWeight_pureSecond (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    normalLogWeight_hessian (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)), normalLogWeight_third hf,
    mul_zero, zero_mul, add_zero]
  rfl

lemma normalBarrier_fourth {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) (a b c d : Fin 3) :
    dbar (fun q => dz (fun r => complexHessian (logarithmicBarrier ∘ normalLogWeight f w) r c d) q a) (0,w) b =
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * verticalDelta b * liftedThird f (0,w) a c d +
      (barrierX (normalLogWeight f w (0,w)) : ℂ) * liftedFourth f (0,w) a b c d +
      (barrierThird (normalLogWeight f w (0,w)) : ℂ) * verticalDelta b * verticalDelta a * liftedHessian f (0,w) c d +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * liftedHessian f (0,w) a b * liftedHessian f (0,w) c d +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * verticalDelta a * liftedBarThird f (0,w) b c d +
      (barrierThird (normalLogWeight f w (0,w)) : ℂ) * verticalDelta b * verticalDelta c * liftedHessian f (0,w) a d +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * liftedHessian f (0,w) c b * liftedHessian f (0,w) a d +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * verticalDelta c * liftedBarThird f (0,w) b a d +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * liftedThird f (0,w) a c b * verticalDelta d +
      (barrierFourth (normalLogWeight f w (0,w)) : ℂ) * verticalDelta b * verticalDelta a * verticalDelta c * verticalDelta d +
      (barrierThird (normalLogWeight f w (0,w)) : ℂ) * liftedHessian f (0,w) a b * verticalDelta c * verticalDelta d +
      (barrierThird (normalLogWeight f w (0,w)) : ℂ) * verticalDelta a * liftedHessian f (0,w) c b * verticalDelta d := by
  have hs := normalLogWeight_contDiffAt (q := (0,w)) hf w
  rw [dbar_dz_complexHessian_barrier (hs.of_le (WithTop.coe_le_coe.mpr le_top)) hn]
  simp only [normalLogWeight_first (hf.of_le (WithTop.coe_le_coe.mpr le_top)), normalLogWeight_barFirst hf,
    normalLogWeight_pureSecond (hf.of_le (WithTop.coe_le_coe.mpr le_top)), normalLogWeight_pureBarSecond hf,
    dbar_dz_real_eq_hessian (hs.of_le (WithTop.coe_le_coe.mpr le_top)),
    dbar_dz_dz_real (hs.of_le (WithTop.coe_le_coe.mpr le_top)),
    normalLogWeight_hessian (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)), normalLogWeight_third hf,
    normalLogWeight_barThird hf, normalLogWeight_fourth hf, mul_zero, zero_mul, add_zero]
  rfl

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsJetLinearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

lemma complexHessian_lam_add_eventually {f g : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (hg : ContDiffAt ℝ 2 g p) (lam : ℝ) (c d : Fin 3) :
    (fun q => complexHessian (fun r => lam * f r + g r) q c d) =ᶠ[𝓝 p]
      (fun q => (lam : ℂ) * complexHessian f q c d + complexHessian g q c d) := by
  filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with q hq hq'
  rw [complexHessian_add (contDiffAt_const.mul hq) hq', complexHessian_const_mul hq]

lemma dz_complexHessian_lam_add {f g : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 3 f p) (hg : ContDiffAt ℝ 3 g p) (lam : ℝ) (a c d : Fin 3) :
    dz (fun q => complexHessian (fun r => lam * f r + g r) q c d) p a =
      (lam : ℂ) * dz (fun q => complexHessian f q c d) p a +
        dz (fun q => complexHessian g q c d) p a := by
  have hfd := (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 2) (by norm_num) d) (m := 1) (by norm_num) c).differentiableAt (by norm_num)
  have hgd := (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hg) (m := 2) (by norm_num) d) (m := 1) (by norm_num) c).differentiableAt (by norm_num)
  rw [dz_congr (complexHessian_lam_add_eventually (hf.of_le (by norm_num)) (hg.of_le (by norm_num)) lam c d)]
  exact (dz_add ((differentiableAt_const _).mul hfd) hgd a).trans (by erw [dz_const_mul hfd]; rfl)

lemma dbar_dz_complexHessian_lam_add {f g : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 4 f p) (hg : ContDiffAt ℝ 4 g p) (lam : ℝ) (a b c d : Fin 3) :
    dbar (fun q => dz (fun r => complexHessian (fun t => lam * f t + g t) r c d) q a) p b =
      (lam : ℂ) * dbar (fun q => dz (fun r => complexHessian f r c d) q a) p b +
        dbar (fun q => dz (fun r => complexHessian g r c d) q a) p b := by
  have he : (fun q => dz (fun r => complexHessian (fun t => lam * f t + g t) r c d) q a) =ᶠ[𝓝 p]
      (fun q => (lam : ℂ) * dz (fun r => complexHessian f r c d) q a + dz (fun r => complexHessian g r c d) q a) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with q hq hq'
    exact dz_complexHessian_lam_add (hq.of_le (by norm_num)) (hq'.of_le (by norm_num)) lam a c d
  have hfd := (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 3) (by norm_num) d) (m := 2) (by norm_num) c) (m := 1) (by norm_num) a).differentiableAt (by norm_num)
  have hgd := (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hg) (m := 3) (by norm_num) d) (m := 2) (by norm_num) c) (m := 1) (by norm_num) a).differentiableAt (by norm_num)
  rw [dbar_congr he]
  exact (dbar_add ((differentiableAt_const _).mul hfd) hgd b).trans (by erw [dbar_const_mul hfd]; rfl)

lemma normalPotential_contDiffAt {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) :
    ContDiffAt ℝ ∞ (normalPotential f lam w) (0,w) :=
  (contDiffAt_const.mul ((psi_contDiffAt zero_mem_ball).comp (f := fun q : Ambient => q.1) (0,w) contDiffAt_fst)).add
    ((logarithmicBarrier_contDiffAt hn).comp (0,w) (normalLogWeight_contDiffAt (q := (0,w)) hf w))

lemma normalPotential_hessian {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) (i j : Fin 3) :
    complexHessian (normalPotential f lam w) (0,w) i j =
      (lam : ℂ) * horizontalIdentity i j +
      (barrierX (normalLogWeight f w (0,w)) : ℂ) * liftedHessian f (0,w) i j +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * verticalDelta i * verticalDelta j := by
  have hψ : ContDiffAt ℝ 2 (fun q : Ambient => psi q.1) (0,w) :=
    ((psi_contDiffAt zero_mem_ball).of_le (WithTop.coe_le_coe.mpr le_top)).comp (f := fun q : Ambient => q.1) (0,w) contDiffAt_fst
  have hB : ContDiffAt ℝ 2 (logarithmicBarrier ∘ normalLogWeight f w) (0,w) :=
    ((logarithmicBarrier_contDiffAt hn).comp (0,w) (normalLogWeight_contDiffAt (q := (0,w)) hf w)).of_le (WithTop.coe_le_coe.mpr le_top)
  change complexHessian (fun q : Ambient => lam * psi q.1 + (logarithmicBarrier ∘ normalLogWeight f w) q) (0,w) i j = _
  erw [complexHessian_add (contDiffAt_const.mul hψ) hB, complexHessian_const_mul hψ,
    psi_hessian_center, normalBarrier_hessian hf w hn]
  ring

lemma normalPotential_third {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) (a c d : Fin 3) :
    dz (fun q => complexHessian (normalPotential f lam w) q c d) (0,w) a =
      (barrierX (normalLogWeight f w (0,w)) : ℂ) * liftedThird f (0,w) a c d +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * verticalDelta a * liftedHessian f (0,w) c d +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * verticalDelta c * liftedHessian f (0,w) a d +
      (barrierThird (normalLogWeight f w (0,w)) : ℂ) * verticalDelta a * verticalDelta c * verticalDelta d := by
  have hψ : ContDiffAt ℝ 3 (fun q : Ambient => psi q.1) (0,w) :=
    ((psi_contDiffAt zero_mem_ball).of_le (WithTop.coe_le_coe.mpr le_top)).comp (f := fun q : Ambient => q.1) (0,w) contDiffAt_fst
  have hB : ContDiffAt ℝ 3 (logarithmicBarrier ∘ normalLogWeight f w) (0,w) :=
    ((logarithmicBarrier_contDiffAt hn).comp (0,w) (normalLogWeight_contDiffAt (q := (0,w)) hf w)).of_le (WithTop.coe_le_coe.mpr le_top)
  change dz (fun q => complexHessian (fun r : Ambient => lam * psi r.1 + (logarithmicBarrier ∘ normalLogWeight f w) r) q c d) (0,w) a = _
  erw [dz_complexHessian_lam_add hψ hB, psi_third_center, mul_zero, zero_add]
  exact normalBarrier_third hf w hn a c d

lemma normalPotential_fourth {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) (a b c d : Fin 3) :
    dbar (fun q => dz (fun r => complexHessian (normalPotential f lam w) r c d) q a) (0,w) b =
      (lam : ℂ) * (horizontalIdentity a b * horizontalIdentity c d + horizontalIdentity a d * horizontalIdentity c b) +
      dbar (fun q => dz (fun r => complexHessian (logarithmicBarrier ∘ normalLogWeight f w) r c d) q a) (0,w) b := by
  have hψ : ContDiffAt ℝ 4 (fun q : Ambient => psi q.1) (0,w) :=
    ((psi_contDiffAt zero_mem_ball).of_le (WithTop.coe_le_coe.mpr le_top)).comp (f := fun q : Ambient => q.1) (0,w) contDiffAt_fst
  have hB : ContDiffAt ℝ 4 (logarithmicBarrier ∘ normalLogWeight f w) (0,w) :=
    ((logarithmicBarrier_contDiffAt hn).comp (0,w) (normalLogWeight_contDiffAt (q := (0,w)) hf w)).of_le (WithTop.coe_le_coe.mpr le_top)
  change dbar (fun q => dz (fun r => complexHessian (fun t : Ambient => lam * psi t.1 + (logarithmicBarrier ∘ normalLogWeight f w) t) r c d) q a) (0,w) b = _
  erw [dbar_dz_complexHessian_lam_add hψ hB, psi_fourth_center]
  ring

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsLiftedJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

lemma _root_.OAI.ContDiffAt.hartogs_baseHessian {f : Base → ℝ} {z : Base} {m n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f z) (hmn : m + 2 ≤ n) : ContDiffAt ℝ m (baseHessian f) z := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
  exact _root_.OAI.ContDiffAt.hartogs_dzBase (_root_.OAI.ContDiffAt.hartogs_dbarBase hc (m := m+1) (by convert hmn using 1; norm_num [add_assoc]) j) (m := m) le_rfl i

lemma liftedHessian_vertical_left {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (j : Fin 3) : liftedHessian f q 2 j = 0 := by
  dsimp [liftedHessian]
  rw [complexHessian_lift_base hf]
  fin_cases j <;> rfl

lemma liftedHessian_vertical_right {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (i : Fin 3) : liftedHessian f q i 2 = 0 := by
  dsimp [liftedHessian]
  rw [complexHessian_lift_base hf]
  fin_cases i <;> rfl

lemma liftedHessian_horizontal_eventually {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (i j : Fin 2) :
    (fun r => liftedHessian f r i.castSucc j.castSucc) =ᶠ[𝓝 q]
      (fun r => baseHessian f r.1 i j) := by
  filter_upwards [continuousAt_fst.preimage_mem_nhds (hf.eventually (by norm_num))] with r hr
  change ContDiffAt ℝ 2 f r.1 at hr
  exact liftedHessian_horizontal hr i j

lemma liftedHessian_vertical_left_eventually {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (j : Fin 3) :
    (fun r => liftedHessian f r 2 j) =ᶠ[𝓝 q] (fun _ => 0) := by
  filter_upwards [continuousAt_fst.preimage_mem_nhds (hf.eventually (by norm_num))] with r hr
  change ContDiffAt ℝ 2 f r.1 at hr
  exact liftedHessian_vertical_left hr j

lemma liftedHessian_vertical_right_eventually {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (i : Fin 3) :
    (fun r => liftedHessian f r i 2) =ᶠ[𝓝 q] (fun _ => 0) := by
  filter_upwards [continuousAt_fst.preimage_mem_nhds (hf.eventually (by norm_num))] with r hr
  change ContDiffAt ℝ 2 f r.1 at hr
  exact liftedHessian_vertical_right hr i

lemma liftedThird_vertical_middle {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (a d : Fin 3) : liftedThird f q a 2 d = 0 := by
  rw [liftedThird, dz_congr (liftedHessian_vertical_left_eventually hf d)]
  simp [dz]

lemma liftedThird_vertical_right {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (a c : Fin 3) : liftedThird f q a c 2 = 0 := by
  rw [liftedThird, dz_congr (liftedHessian_vertical_right_eventually hf c)]
  simp [dz]

lemma liftedThird_vertical_left_horizontal {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 3 f q.1) (c d : Fin 2) :
    liftedThird f q 2 c.castSucc d.castSucc = 0 := by
  have hd := (contDiffAt_pi.mp (contDiffAt_pi.mp (_root_.OAI.ContDiffAt.hartogs_baseHessian hf (m := 1) (by norm_num)) c) d).differentiableAt (by simp)
  rw [liftedThird, dz_congr (liftedHessian_horizontal_eventually (hf.of_le (by norm_num)) c d), dz_lift_base hd]
  rfl

lemma liftedThird_vertical_left {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 3 f q.1) (c d : Fin 3) : liftedThird f q 2 c d = 0 := by
  refine Fin.lastCases ?_ (fun c => ?_) c
  · exact liftedThird_vertical_middle (hf.of_le (by norm_num)) 2 d
  · refine Fin.lastCases ?_ (fun d => ?_) d
    · exact liftedThird_vertical_right (hf.of_le (by norm_num)) 2 c.castSucc
    · exact liftedThird_vertical_left_horizontal hf c d

lemma liftedFourth_vertical_middle {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (a b d : Fin 3) : liftedFourth f q a b 2 d = 0 := by
  unfold liftedFourth liftedThird
  rw [dbar_dz_congr (liftedHessian_vertical_left_eventually hf d)]
  simp [dz, dbar]

lemma liftedFourth_vertical_right {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (a b c : Fin 3) : liftedFourth f q a b c 2 = 0 := by
  unfold liftedFourth liftedThird
  rw [dbar_dz_congr (liftedHessian_vertical_right_eventually hf c)]
  simp [dz, dbar]

lemma liftedFourth_vertical_left {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 3 f q.1) (b c d : Fin 3) : liftedFourth f q 2 b c d = 0 := by
  have he : (fun r => liftedThird f r 2 c d) =ᶠ[𝓝 q] (fun _ => 0) := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds (hf.eventually (by norm_num))] with r hr
    change ContDiffAt ℝ 3 f r.1 at hr
    exact liftedThird_vertical_left hr c d
  rw [liftedFourth, dbar_congr he]
  simp [dbar]

lemma liftedFourth_vertical_second_horizontal {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 4 f q.1) (a : Fin 3) (c d : Fin 2) :
    liftedFourth f q a 2 c.castSucc d.castSucc = 0 := by
  have hc : ContDiffAt ℝ 2 (fun z => baseHessian f z c d) q.1 :=
    contDiffAt_pi.mp (contDiffAt_pi.mp (_root_.OAI.ContDiffAt.hartogs_baseHessian hf (m := 2) (by norm_num)) c) d
  unfold liftedFourth liftedThird
  rw [dbar_dz_congr (liftedHessian_horizontal_eventually (hf.of_le (by norm_num)) c d)]
  erw [← dz_dbar_comm (hc.comp (f := fun r : Ambient => r.1) q contDiffAt_fst)]
  have he : (fun r : Ambient => dbar (fun t : Ambient => baseHessian f t.1 c d) r 2) =ᶠ[𝓝 q]
      (fun _ => 0) := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds (hc.eventually (by norm_num))] with r hr
    change ContDiffAt ℝ 2 (fun z => baseHessian f z c d) r.1 at hr
    exact dbar_lift_base (hr.differentiableAt (by norm_num)) 2
  erw [dz_congr he]
  simp [dz]

lemma liftedFourth_vertical_second {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 4 f q.1) (a c d : Fin 3) : liftedFourth f q a 2 c d = 0 := by
  refine Fin.lastCases ?_ (fun c => ?_) c
  · exact liftedFourth_vertical_middle (hf.of_le (by norm_num)) a 2 d
  · refine Fin.lastCases ?_ (fun d => ?_) d
    · exact liftedFourth_vertical_right (hf.of_le (by norm_num)) a 2 c.castSucc
    · exact liftedFourth_vertical_second_horizontal hf a c d

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsNormalBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

lemma block3_one : block3 1 1 = (1 : CMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [block3, Matrix.one_apply]

lemma block3_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) (r s : ℂ) :
    block3 A r * block3 B s = block3 (A * B) (r*s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block3, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

lemma block3_inv {A : Matrix (Fin 2) (Fin 2) ℂ} {r : ℂ} (hA : A.det ≠ 0) (hr : r ≠ 0) :
    (block3 A r)⁻¹ = block3 A⁻¹ r⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [block3_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA), mul_inv_cancel₀ hr]
  exact block3_one

lemma normalPotential_hessian_block {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) :
    complexHessian (normalPotential f lam w) (0,w) =
      block3 ((lam : ℂ) • 1 + (barrierX (normalLogWeight f w (0,w)) : ℂ) • baseHessian f 0)
        (barrierQ (normalLogWeight f w (0,w))) := by
  ext i j
  rw [normalPotential_hessian hf lam w hn]
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [liftedHessian_vertical_left (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top))]
    · simp [liftedHessian_vertical_left (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top))]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [liftedHessian_vertical_right (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top))]
    · simp [liftedHessian_horizontal (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
        Matrix.add_apply, Matrix.smul_apply]

lemma sum_fin3_horizontal (f : Fin 3 → ℂ) :
    (∑ i, f i) = (∑ i : Fin 2, f i.castSucc) + f 2 := by
  simpa using Fin.sum_univ_castSucc f

lemma block3_contraction (A : Matrix (Fin 2) (Fin 2) ℂ) (r : ℂ) (u v : Fin 3 → ℂ) :
    (∑ e, ∑ k, block3 A r e k * u e * v k) =
      (∑ e : Fin 2, ∑ k : Fin 2, A e k * u e.castSucc * v k.castSucc) + r * u 2 * v 2 := by
  rw [sum_fin3_horizontal]
  simp only [sum_fin3_horizontal, block3_horizontal, block3_vertical_left, block3_vertical_right,
    block3_vertical, zero_mul, Finset.sum_const_zero, zero_add, add_zero]

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsTensorSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

lemma dbar_complexHessian_conj {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 3 f p) (b c d : Fin 3) :
    dbar (fun q => complexHessian f q c d) p b =
      star (dz (fun q => complexHessian f q d c) p b) := by
  have he : (fun q => complexHessian f q c d) =ᶠ[𝓝 p]
      (fun q => star (complexHessian f q d c)) := by
    filter_upwards [hf.eventually (by norm_num)] with q hq
    exact complexHessian_hermitian (hq.of_le (by norm_num)) c d
  have hd : DifferentiableAt ℝ (fun q => complexHessian f q d c) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 2) (by norm_num) c) (m := 1) (by norm_num) d).differentiableAt (by norm_num)
  rw [dbar_congr he, dbar_conj hd]

lemma dbar_dz_star {f : Ambient → ℂ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (a b : Fin 3) :
    dbar (fun q => dz (fun r => star (f r)) q a) p b =
      star (dz (fun q => dbar f q a) p b) := by
  have he : (fun q => dz (fun r => star (f r)) q a) =ᶠ[𝓝 p]
      (fun q => star (dbar f q a)) := by
    filter_upwards [hf.eventually (by norm_num)] with q hq
    exact dz_conj (hq.differentiableAt (by norm_num)) a
  rw [dbar_congr he, dbar_conj ((_root_.OAI.ContDiffAt.hartogs_dbar hf (m := 1) (by norm_num) a).differentiableAt (by norm_num))]

lemma complexHessian_fourth_reality {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 4 f p) (a b c d : Fin 3) :
    star (dbar (fun q => dz (fun r => complexHessian f r c d) q a) p b) =
      dbar (fun q => dz (fun r => complexHessian f r d c) q b) p a := by
  have he : (fun q => complexHessian f q c d) =ᶠ[𝓝 p]
      (fun q => star (complexHessian f q d c)) := by
    filter_upwards [hf.eventually (by norm_num)] with q hq
    exact complexHessian_hermitian (hq.of_le (by norm_num)) c d
  have hh : ContDiffAt ℝ 2 (fun q => complexHessian f q d c) p :=
    _root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 3) (by norm_num) c) (m := 2) (by norm_num) d
  rw [dbar_dz_congr he, dbar_dz_star hh, star_star, dz_dbar_comm hh]

lemma complexHessian_curvature_hol {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 4 f p) (a b c d : Fin 3) :
    curvature (complexHessian f) p a b c d = curvature (complexHessian f) p c b a d := by
  have he : (fun q => dz (fun r => complexHessian f r c d) q a) =ᶠ[𝓝 p]
      (fun q => dz (fun r => complexHessian f r a d) q c) := by
    filter_upwards [hf.eventually (by norm_num)] with q hq
    exact complexHessian_closed (hq.of_le (by norm_num)) a d c
  unfold curvature
  rw [dbar_congr he]
  congr 1
  apply Finset.sum_congr rfl
  intro e he'
  apply Finset.sum_congr rfl
  intro k hk
  rw [complexHessian_closed (hf.of_le (by norm_num)) a e c]

lemma complexHessian_curvature_reality {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 4 f p) (a b c d : Fin 3) :
    star (curvature (complexHessian f) p a b c d) = curvature (complexHessian f) p b a d c := by
  have hM : (complexHessian f p).IsHermitian := by
    ext i j
    exact (complexHessian_hermitian (hf.of_le (by norm_num)) i j).symm
  have hi (e k : Fin 3) : star ((complexHessian f p)⁻¹ e k) = (complexHessian f p)⁻¹ k e := hM.inv.apply k e
  have hd (i j k : Fin 3) : star (dz (fun q => complexHessian f q i j) p k) = dbar (fun q => complexHessian f q j i) p k :=
    (dbar_complexHessian_conj (hf.of_le (by norm_num)) k j i).symm
  unfold curvature
  simp only [star_add, star_neg, star_sum, star_mul]
  rw [complexHessian_fourth_reality hf]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro e he
  rw [hi, hd, dbar_complexHessian_conj (hf.of_le (by norm_num)), star_star]
  ring

lemma complexHessian_curvature_anti {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 4 f p) (a b c d : Fin 3) :
    curvature (complexHessian f) p a b c d = curvature (complexHessian f) p a d c b := by
  apply star_injective
  rw [complexHessian_curvature_reality hf, complexHessian_curvature_reality hf,
    complexHessian_curvature_hol hf b a d c]

lemma liftedBarThird_conj {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 3 f q.1) (b c d : Fin 3) :
    liftedBarThird f q b c d = star (liftedThird f q b d c) :=
  dbar_complexHessian_conj (hf.comp (f := fun r : Ambient => r.1) q contDiffAt_fst) b c d

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsNormalCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

lemma normalPotential_curvature_split {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (((lam : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (barrierX (normalLogWeight f w (0,w)) : ℂ) • baseHessian f 0)).det ≠ 0)
    (a b c d : Fin 3) :
    curvature (complexHessian (normalPotential f lam w)) (0,w) a b c d =
      -dbar (fun q => dz (fun r => complexHessian (normalPotential f lam w) r c d) q a) (0,w) b +
      (∑ e : Fin 2, ∑ k : Fin 2,
        (((lam : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
          (barrierX (normalLogWeight f w (0,w)) : ℂ) • baseHessian f 0)⁻¹) e k *
          dz (fun r => complexHessian (normalPotential f lam w) r c e.castSucc) (0,w) a *
          star (dz (fun r => complexHessian (normalPotential f lam w) r d k.castSucc) (0,w) b)) +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ)⁻¹ *
        dz (fun r => complexHessian (normalPotential f lam w) r c 2) (0,w) a *
        star (dz (fun r => complexHessian (normalPotential f lam w) r d 2) (0,w) b) := by
  have hs := (normalPotential_contDiffAt hf lam w hn).of_le (m := 3) (WithTop.coe_le_coe.mpr le_top)
  unfold curvature
  simp_rw [dbar_complexHessian_conj hs]
  rw [normalPotential_hessian_block hf lam w hn,
    block3_inv hG (by exact_mod_cast (ne_of_gt (barrierQ_positive hn))), block3_contraction]
  ring

lemma normalPotential_curvature_HVHV {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (((lam : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (barrierX (normalLogWeight f w (0,w)) : ℂ) • baseHessian f 0)).det ≠ 0)
    (a b : Fin 2) :
    curvature (complexHessian (normalPotential f lam w)) (0,w) a.castSucc b.castSucc 2 2 =
      -(barrierQ (normalLogWeight f w (0,w)) : ℂ) * ((1 + 2 * (barrierX (normalLogWeight f w (0,w)) : ℂ)) * baseHessian f 0 a b -
        (barrierQ (normalLogWeight f w (0,w)) : ℂ) * (∑ e : Fin 2, ∑ k : Fin 2,
          (((lam : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (barrierX (normalLogWeight f w (0,w)) : ℂ) • baseHessian f 0)⁻¹) e k * baseHessian f 0 a e * star (baseHessian f 0 b k))) := by
  rw [normalPotential_curvature_split hf lam w hn hG,
    normalPotential_fourth hf lam w hn, normalBarrier_fourth hf w hn]
  simp only [normalPotential_third hf lam w hn, verticalDelta_horizontal, verticalDelta_vertical,
    horizontalIdentity_horizontal, horizontalIdentity_vertical_left, horizontalIdentity_vertical_right,
    liftedBarThird_conj (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_horizontal (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_vertical_left (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_vertical_right (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedThird_vertical_middle (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedFourth_vertical_middle (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    mul_zero, zero_add, add_zero, mul_one, star_zero,
    star_mul, Complex.star_def, Complex.conj_ofReal]
  simp only [Fin.sum_univ_two, barrierThird, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

lemma normalPotential_curvature_HHVV {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (((lam : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (barrierX (normalLogWeight f w (0,w)) : ℂ) • baseHessian f 0)).det ≠ 0)
    (a c : Fin 2) :
    curvature (complexHessian (normalPotential f lam w)) (0,w) a.castSucc 2 c.castSucc 2 = 0 := by
  rw [normalPotential_curvature_split hf lam w hn hG,
    normalPotential_fourth hf lam w hn, normalBarrier_fourth hf w hn]
  simp only [normalPotential_third hf lam w hn, verticalDelta_horizontal, verticalDelta_vertical,
    horizontalIdentity_vertical_right,
    liftedBarThird_conj (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_horizontal (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_vertical_left (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_vertical_right (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedThird_vertical_left (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedThird_vertical_right (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedFourth_vertical_second (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    mul_zero, zero_mul, zero_add, add_zero, mul_one, star_zero,
    Complex.star_def, Complex.conj_ofReal]
  simp

lemma normalPotential_curvature_HVVV {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (((lam : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (barrierX (normalLogWeight f w (0,w)) : ℂ) • baseHessian f 0)).det ≠ 0)
    (a : Fin 2) :
    curvature (complexHessian (normalPotential f lam w)) (0,w) a.castSucc 2 2 2 = 0 := by
  rw [normalPotential_curvature_split hf lam w hn hG,
    normalPotential_fourth hf lam w hn, normalBarrier_fourth hf w hn]
  simp only [normalPotential_third hf lam w hn, verticalDelta_horizontal, verticalDelta_vertical,
    horizontalIdentity_vertical_right,
    liftedBarThird_conj (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_horizontal (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_vertical_left (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_vertical_right (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedThird_vertical_left (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedThird_vertical_middle (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedFourth_vertical_second (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    mul_zero, zero_mul, zero_add, add_zero, mul_one, star_zero,
    Complex.star_def, Complex.conj_ofReal]
  simp

lemma normalPotential_curvature_VVVV {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (((lam : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (barrierX (normalLogWeight f w (0,w)) : ℂ) • baseHessian f 0)).det ≠ 0) :
    curvature (complexHessian (normalPotential f lam w)) (0,w) 2 2 2 2 = -2 * (barrierQ (normalLogWeight f w (0,w)) : ℂ)^2 := by
  rw [normalPotential_curvature_split hf lam w hn hG,
    normalPotential_fourth hf lam w hn, normalBarrier_fourth hf w hn]
  simp only [normalPotential_third hf lam w hn, verticalDelta_horizontal, verticalDelta_vertical,
    horizontalIdentity_vertical_right,
    liftedBarThird_conj (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_vertical_left (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedThird_vertical_left (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedFourth_vertical_left (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    mul_zero, zero_add, add_zero, mul_one, star_zero,
    Complex.star_def, Complex.conj_ofReal]
  have hq : (barrierQ (normalLogWeight f w (0,w)) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (barrierQ_positive hn))
  simp only [Finset.sum_const_zero, barrierThird, barrierFourth, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_pow]
  field_simp
  simp only [barrierQ, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one]
  ring

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.PinchingCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler4409_1 uKahler5342_1 uKahler5693_1 uKahler5694_1 uKahler5695_1 uKahler6181_1 uKahler6341_1 uKahler6602_1 uKahler6602_2 uKahler6609_1 uKahler6612_1 uKahler6615_1 uKahler6620_1 uKahler7053_1 uKahler7224_1

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Complex

namespace PinchedHartogs.PlaneAlgebra
namespace TensorAlgebra
open MatrixAlgebra Matrix
open scoped ComplexOrder

section Rescaling
variable {n : Type uKahler6181_1} [finiteIndex : Fintype n]

omit finiteIndex in
theorem pull_symmetries {n : Type uKahler6181_1} [Fintype n] (r : n → ℝ) (T : Tensor n) (hT : Symmetries T) :
    Symmetries (pullTensor r T) := by
  constructor
  · intro a b c d
    simp only [pullTensor]
    rw [hT.hol a b c d]
    ring
  · intro a b c d
    simp only [pullTensor]
    rw [hT.anti a b c d]
    ring
  · intro a b c d
    simp only [pullTensor, map_mul, Complex.star_def, Complex.conj_ofReal]
    rw [show (starRingEnd ℂ) (T a b c d) = T b a d c from hT.reality a b c d]
    ring

end Rescaling

end TensorAlgebra
end PinchedHartogs.PlaneAlgebra

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsModelBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open Complex
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs
open PlaneAlgebra PlaneAlgebra.MatrixAlgebra PlaneAlgebra.TensorAlgebra

lemma normalCurvature_symmetries {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) :
    Symmetries (normalCurvature f lam w) := by
  apply pull_symmetries
  have hs := (normalPotential_contDiffAt hf lam w hn).of_le (m := 4) (WithTop.coe_le_coe.mpr le_top)
  exact ⟨fun a b c d => complexHessian_curvature_hol hs _ _ _ _,
    fun a b c d => complexHessian_curvature_anti hs _ _ _ _,
    fun a b c d => complexHessian_curvature_reality hs _ _ _ _⟩

lemma tensor_symmetries_sub {T Q : Tensor Index} (hT : Symmetries T) (hQ : Symmetries Q) :
    Symmetries (T-Q) := by
  constructor
  · intro a b c d; simp only [Pi.sub_apply, hT.hol a b c d, hQ.hol a b c d]
  · intro a b c d; simp only [Pi.sub_apply, hT.anti a b c d, hQ.anti a b c d]
  · intro a b c d; simp only [Pi.sub_apply, star_sub, hT.reality a b c d, hQ.reality a b c d]

lemma tensor_symmetries_smul {T : Tensor Index} (hT : Symmetries T) (r : ℝ) :
    Symmetries (r • T) := by
  constructor
  · intro a b c d; simp only [Pi.smul_apply, hT.hol a b c d]
  · intro a b c d; simp only [Pi.smul_apply, hT.anti a b c d]
  · intro a b c d; simp only [Pi.smul_apply, star_smul, star_trivial, hT.reality a b c d]

lemma tensor_S_symmetries (A : Matrix Index Index ℂ) (hA : A.IsHermitian) : Symmetries (S A) := by
  constructor
  · intro a b c d; simp only [S]; ring
  · intro a b c d; simp only [S]; ring
  · intro a b c d
    simp only [S, star_add, star_mul]
    rw [show star (A a b) = A b a from hA.apply b a,
      show star (A c d) = A d c from hA.apply d c,
      show star (A a d) = A d a from hA.apply d a,
      show star (A c b) = A b c from hA.apply b c]
    ring

lemma block_isHermitian (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian) (r : ℝ) :
    (block A r).IsHermitian := by
  ext a b
  cases a <;> cases b <;> simp [Matrix.conjTranspose, block]
  exact hA.apply _ _

lemma principal_symmetries (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian) (lam x : ℝ) :
    Symmetries (curvatureModel A lam x 0 0) := by
  simp only [curvatureModel, add_zero]
  apply tensor_symmetries_sub
  · exact tensor_symmetries_sub
      (tensor_symmetries_sub (tensor_symmetries_smul (tensor_S_symmetries _ (block_isHermitian _ Matrix.isHermitian_one _)) _)
        (tensor_symmetries_smul (tensor_S_symmetries _ (block_isHermitian _ hA _)) _))
      (tensor_S_symmetries _ (block_isHermitian _ Matrix.isHermitian_zero _))
  · exact tensor_symmetries_sub
      (tensor_symmetries_sub (tensor_S_symmetries _ (block_isHermitian _ (mixedMatrix_hermitian A hA _ _) _))
        (tensor_S_symmetries _ (block_isHermitian _ (mixedMatrix_hermitian A hA _ _) _)))
      (tensor_S_symmetries _ (block_isHermitian _ Matrix.isHermitian_zero _))

lemma tensor_split_of_low_blocks {T : Tensor Index} (hT : Symmetries T)
    (h0 : T none none none none = 0)
    (h1 : ∀ a, T (some a) none none none = 0)
    (h2 : ∀ a b, T (some a) (some b) none none = 0)
    (h2' : ∀ a c, T (some a) none (some c) none = 0) :
    T = horizontalPart 4 T + horizontalPart 3 T := by
  ext a b c d
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [horizontalPart, horizontalCount]
  all_goals first
    | exact h0
    | exact h1 _
    | exact h2 _ _
    | exact h2' _ _
    | rfl
    | (rw [hT.hol]; exact h1 _)
    | (rw [hT.hol]; exact h2 _ _)
    | (rw [hT.anti]; exact h2 _ _)
    | (rw [hT.hol, hT.anti]; exact h2 _ _)
    | (apply star_injective; rw [hT.reality, star_zero]; exact h1 _)
    | (apply star_injective; rw [hT.reality, star_zero, hT.hol]; exact h1 _)
    | (apply star_injective; rw [hT.reality, star_zero]; exact h2' _ _)

lemma complex_horizontalMetric (A : Matrix (Fin 2) (Fin 2) ℂ) (lam x : ℝ) :
    (lam : ℂ) • 1 + (x : ℂ) • A = horizontalMetric A lam x := by
  ext i j
  simp [horizontalMetric, Complex.real_smul]

lemma mixedMatrix_component (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian)
    (lam x : ℝ) (a b : Fin 2) :
    mixedMatrix A lam x a b =
      (1 + 2 * (x : ℂ)) * A a b - ((x * (1+x) : ℝ) : ℂ) *
        (∑ e : Fin 2, ∑ k : Fin 2, (horizontalMetric A lam x)⁻¹ e k * A a e * star (A b k)) := by
  simp only [mixedMatrix, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul,
    Matrix.mul_apply, Fin.sum_univ_two, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [show star (A b 0) = A 0 b from hA.apply 0 b,
    show star (A b 1) = A 1 b from hA.apply 1 b]
  ring

lemma sqrt_normalization (q : ℝ) (hq : 0 < q) :
    (((Real.sqrt q)⁻¹ : ℝ) : ℂ)^2 * (q : ℂ) = 1 ∧
    (((Real.sqrt q)⁻¹ : ℝ) : ℂ) * (q : ℂ) = (Real.sqrt q : ℂ) ∧
    (((Real.sqrt q)⁻¹ : ℝ) : ℂ)^4 * (q : ℂ)^2 = 1 := by
  have hr : (Real.sqrt q : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hq))
  have hs : (Real.sqrt q : ℂ)^2 = (q : ℂ) := by exact_mod_cast Real.sq_sqrt hq.le
  rw [Complex.ofReal_inv, ← hs]
  constructor
  · field_simp
  · constructor <;> field_simp

lemma normalCurvature_HVHV {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w)))).det ≠ 0)
    (a b : Fin 2) :
    normalCurvature f lam w (some a) (some b) none none =
      -mixedMatrix (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w))) a b := by
  have hG' := hG
  rw [← complex_horizontalMetric] at hG'
  simp only [normalCurvature, pullTensor, verticalScale, normalIndex, Complex.ofReal_one, one_mul, mul_one]
  erw [normalPotential_curvature_HVHV hf lam w hn hG', complex_horizontalMetric,
    mixedMatrix_component _ (baseHessian_isHermitian (hf.of_le (WithTop.coe_le_coe.mpr le_top)))]
  have hs := (sqrt_normalization (barrierQ (normalLogWeight f w (0,w))) (barrierQ_positive hn)).1
  change _ * (barrierQ _ : ℂ) = 1 at hs
  change _ = -((1 + 2 * (barrierX (normalLogWeight f w (0,w)) : ℂ)) * baseHessian f 0 a b - (barrierQ (normalLogWeight f w (0,w)) : ℂ) * _)
  linear_combination -((1 + 2 * (barrierX (normalLogWeight f w (0,w)) : ℂ)) * baseHessian f 0 a b - (barrierQ (normalLogWeight f w (0,w)) : ℂ) *
    (∑ e : Fin 2, ∑ k : Fin 2, (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w))))⁻¹ e k * baseHessian f 0 a e * star (baseHessian f 0 b k))) * hs

lemma normalCurvature_HHVV {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w)))).det ≠ 0)
    (a c : Fin 2) : normalCurvature f lam w (some a) none (some c) none = 0 := by
  have hG' := hG
  rw [← complex_horizontalMetric] at hG'
  simp only [normalCurvature, pullTensor, verticalScale, normalIndex, Complex.ofReal_one, one_mul, mul_one]
  rw [normalPotential_curvature_HHVV hf lam w hn hG']
  simp

lemma normalCurvature_HVVV {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w)))).det ≠ 0)
    (a : Fin 2) : normalCurvature f lam w (some a) none none none = 0 := by
  have hG' := hG
  rw [← complex_horizontalMetric] at hG'
  simp only [normalCurvature, pullTensor, verticalScale, normalIndex, Complex.ofReal_one, one_mul]
  rw [normalPotential_curvature_HVVV hf lam w hn hG']
  simp

lemma normalCurvature_VVVV {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w)))).det ≠ 0)
     : normalCurvature f lam w none none none none = -2 := by
  have hG' := hG
  rw [← complex_horizontalMetric] at hG'
  simp only [normalCurvature, pullTensor, verticalScale, normalIndex]
  rw [normalPotential_curvature_VVVV hf lam w hn hG']
  have hs := (sqrt_normalization (barrierQ (normalLogWeight f w (0,w))) (barrierQ_positive hn)).2.2
  linear_combination -2 * hs

lemma principal_HVHV (A : Matrix (Fin 2) (Fin 2) ℂ) (lam x : ℝ) (a b : Fin 2) :
    curvatureModel A lam x 0 0 (some a) (some b) none none = -mixedMatrix A lam x a b := by
  simp [curvatureModel, S, block]

lemma principal_HHVV (A : Matrix (Fin 2) (Fin 2) ℂ) (lam x : ℝ) (a c : Fin 2) :
    curvatureModel A lam x 0 0 (some a) none (some c) none = 0 := by
  simp [curvatureModel, S, block]

lemma principal_HVVV (A : Matrix (Fin 2) (Fin 2) ℂ) (lam x : ℝ) (a : Fin 2) :
    curvatureModel A lam x 0 0 (some a) none none none = 0 := by
  simp [curvatureModel, S, block]

lemma principal_VVVV (A : Matrix (Fin 2) (Fin 2) ℂ) (lam x : ℝ)  :
    curvatureModel A lam x 0 0 none none none none = -2 := by
  norm_num [curvatureModel, S, block, Complex.real_smul]

lemma normalError_symmetries {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) :
    Symmetries (normalError f lam w) :=
  tensor_symmetries_sub (normalCurvature_symmetries hf lam w hn)
    (principal_symmetries _ (baseHessian_isHermitian (hf.of_le (WithTop.coe_le_coe.mpr le_top))) _ _)

lemma normalCurvature_model_oai {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w)))).det ≠ 0) :
    normalCurvature f lam w = curvatureModel (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w)))
      (horizontalPart 4 (normalError f lam w)) (horizontalPart 3 (normalError f lam w)) := by
  have hs := tensor_split_of_low_blocks (normalError_symmetries hf lam w hn)
    (by simp only [normalError, Pi.sub_apply, normalCurvature_VVVV hf lam w hn hG, principal_VVVV, sub_self])
    (fun a => by simp only [normalError, Pi.sub_apply, normalCurvature_HVVV hf lam w hn hG, principal_HVVV, sub_self])
    (fun a b => by simp only [normalError, Pi.sub_apply, normalCurvature_HVHV hf lam w hn hG, principal_HVHV, sub_self])
    (fun a c => by simp only [normalError, Pi.sub_apply, normalCurvature_HHVV hf lam w hn hG, principal_HHVV, sub_self])
  have he (T4 T3 : Tensor Index) : curvatureModel (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w))) T4 T3 =
      curvatureModel (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w))) 0 0 + (T4+T3) := by
    simp only [curvatureModel, add_zero, add_assoc]
  rw [he, ← hs]
  unfold normalError
  abel

end PinchedHartogs

end

end OAI
end

theorem solution : type_of% @OAI.PinchedHartogs.normalCurvature_model_oai := @OAI.PinchedHartogs.normalCurvature_model_oai
