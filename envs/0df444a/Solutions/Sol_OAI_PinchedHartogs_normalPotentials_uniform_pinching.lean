-- Prove2me | solution 1 for OAI.PinchedHartogs.normalPotentials_uniform_pinching
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:15:53.027591+00:00
-- url     : https://prove2.me/submissions/3a4e59cd-b61f-448b-8fe7-2fcf803eeef5

import Mathlib
import Definitions.Def_PinchedKahler
import Definitions.Def_OAIQWPH001
import Theorems.Thm_OAI_PinchedHartogs_normalCurvature_model
import Theorems.Thm_OAI_PinchedHartogs_normalErrors_bounds

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

lemma psi_hessian_center (w : ℂ) (i j : Fin 3) :
    complexHessian (fun q : Ambient => psi q.1) (0,w) i j = horizontalIdentity i j := by
  rw [show (fun q : Ambient => psi q.1) =
    (fun q : Ambient => -Real.log (1 - ‖q.1‖ ^ 2)) by rfl]
  rw [complexHessian_negLogOneSub]
  · simp only [complexHessian_base_norm_sq, dz_base_norm_sq, dbar_base_norm_sq]
    simp [horizontalIdentity]
  · exact (contDiff_norm_sq ℂ).contDiffAt.comp _ contDiffAt_fst
  · simp

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

lemma normalLogWeight_barFirst {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (w : ℂ) (i : Fin 3) :
    dbar (fun q => (normalLogWeight f w q : ℂ)) (0,w) i = if i = 2 then 1 else 0 := by
  rw [dbar_eq_star_dz_real ((normalLogWeight_contDiffAt hf w).differentiableAt (by simp)),
    normalLogWeight_first (hf.of_le (WithTop.coe_le_coe.mpr le_top))]
  split_ifs <;> simp

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

lemma normalBarrier_hessian {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) (i j : Fin 3) :
    complexHessian (logarithmicBarrier ∘ normalLogWeight f w) (0,w) i j =
      (barrierX (normalLogWeight f w (0,w)) : ℂ) * liftedHessian f (0,w) i j +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * verticalDelta i * verticalDelta j := by
  rw [complexHessian_barrier (normalLogWeight_contDiffAt (q := (0,w)) hf w) hn,
    normalLogWeight_first (hf.of_le (WithTop.coe_le_coe.mpr le_top)), normalLogWeight_barFirst hf,
    normalLogWeight_hessian (q := (0,w)) (hf.of_le (WithTop.coe_le_coe.mpr le_top))]
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
namespace PinchedHartogs
namespace PlaneAlgebra

variable (V : Type uKahler4409_1) [AddCommGroup V] [Module ℂ V]

variable {V}
namespace HForm
variable (h E : HForm V) (u v w : V) (c : ℂ)

theorem nonneg_of_pos (hh : h.Pos) : h.Nonneg := by
  intro u
  by_cases hu : u = 0
  · simp [hu]
  · exact (hh u hu).le

theorem gram (hh : h.Nonneg) : h.imag u v ^ 2 ≤ h.area u v := by
  let := h.toCore hh
  have H := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) u v
  change ‖h v u‖ * ‖h u v‖ ≤ h.q u * h.q v at H
  rw [h.hermitian, norm_star, ← pow_two] at H
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at H
  dsimp [imag, area]
  linarith

theorem area_nonneg (hh : h.Nonneg) : 0 ≤ h.area u v :=
  (sq_nonneg _).trans (h.gram u v hh)

theorem q_shear (a : ℝ) (u v : V) :
    h.q (v - (a : ℂ) • u) = h.q v + a ^ 2 * h.q u - 2 * a * (h u v).re := by
  rw [q_sub, q_real_smul, map_smul_right, h.hermitian u v]
  simp [Complex.mul_re]
  ring

theorem imag_shear (a t : ℝ) (u v : V) :
    h.imag ((t : ℂ) • u) (v - (a : ℂ) • u) = t * h.imag u v := by
  simp only [imag, map_smul_left, map_sub_right, map_smul_right, Complex.mul_im,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, star_def,
    Complex.conj_re, Complex.conj_im, h.diag_im, mul_zero, zero_mul, add_zero, sub_zero, neg_zero]

theorem imaginary_bound_equal (L : ℝ) (hL : 1 ≤ L)
    (hl : h.Below E) (hu : ∀ w, E.q w ≤ L * h.q w)
    (heq : h.q u = h.q v) :
    |E.imag u v| ≤ ((L - 1) * h.q u + (L + 1) * |h.imag u v|) / 2 := by
  have hp := sub_le_sub (hu (u + Complex.I • v)) (hl (u - Complex.I • v))
  have hm := sub_le_sub (hu (u - Complex.I • v)) (hl (u + Complex.I • v))
  simp only [q_add_I, q_sub_I, ← heq] at hp hm
  have hb1 := le_abs_self (h.imag u v)
  have hb2 := neg_abs_le (h.imag u v)
  have hn1 := mul_nonneg (show 0 ≤ L + 1 by linarith) (sub_nonneg.mpr hb1)
  have hn2 := mul_nonneg (show 0 ≤ L + 1 by linarith) (sub_nonneg.mpr hb2)
  rw [abs_le]
  constructor <;> linarith

theorem imaginary_bound (hh : h.Pos) (L : ℝ) (hL : 1 ≤ L)
    (hl : h.Below E) (hu : ∀ w, E.q w ≤ L * h.q w)
    (ha : 0 < h.area u v) :
    |E.imag u v| ≤ ((L - 1) * Real.sqrt (h.area u v) +
      (L + 1) * |h.imag u v|) / 2 := by
  have hn := h.nonneg_of_pos hh
  have hu0 : u ≠ 0 := by
    intro he; subst u
    simp [area] at ha
  have hqu : 0 < h.q u := hh u hu0
  have hs : 0 < Real.sqrt (h.area u v) := Real.sqrt_pos.mpr ha
  have hs2 := Real.sq_sqrt ha.le
  let a : ℝ := (h u v).re / h.q u
  let t : ℝ := Real.sqrt (h.area u v) / h.q u
  have ht : 0 < t := div_pos hs hqu
  have hqx : h.q ((t : ℂ) • u) = h.area u v / h.q u := by
    rw [q_real_smul]
    dsimp [t]
    rw [div_pow, hs2]
    field_simp
  have hqy : h.q (v - (a : ℂ) • u) = h.area u v / h.q u := by
    rw [q_shear]
    dsimp [a, area]
    field_simp
    ; ring
  have H := h.imaginary_bound_equal E ((t : ℂ) • u) (v - (a : ℂ) • u)
    L hL hl hu (hqx.trans hqy.symm)
  rw [imag_shear, imag_shear, abs_mul, abs_mul, abs_of_pos ht, hqx] at H
  have hta : h.area u v / h.q u = t * Real.sqrt (h.area u v) := by
    dsimp [t]
    rw [div_mul_eq_mul_div, ← pow_two, hs2]
  rw [hta] at H
  have H' : t * |E.imag u v| ≤ t *
      (((L - 1) * Real.sqrt (h.area u v) + (L + 1) * |h.imag u v|) / 2) := by
    linarith [H]
  exact le_of_mul_le_mul_left H' ht

theorem q_eq_zero_iff (hh : h.Pos) : h.q u = 0 ↔ u = 0 := by
  constructor
  · intro hz
    by_contra hu
    have hp := hh u hu
    linarith
  · rintro rfl
    exact h.q_zero

theorem dependent_of_area_zero (hh : h.Pos) (hu : u ≠ 0) (ha : h.area u v = 0) :
    ∃ a : ℝ, v = (a : ℂ) • u := by
  have hqu : 0 < h.q u := hh u hu
  let a : ℝ := (h u v).re / h.q u
  refine ⟨a, ?_⟩
  have hq : h.q (v - (a : ℂ) • u) = 0 := by
    rw [q_shear]
    dsimp [a]
    have heq : h.q v + ((h u v).re / h.q u) ^ 2 * h.q u -
        2 * ((h u v).re / h.q u) * (h u v).re = h.area u v / h.q u := by
      dsimp [area]
      field_simp
      ; ring
    rw [heq, ha, zero_div]
  exact sub_eq_zero.mp ((h.q_eq_zero_iff _ hh).mp hq)

theorem imag_eq_zero_of_area_zero (hh : h.Pos) (ha : h.area u v = 0) : E.imag u v = 0 := by
  by_cases hu : u = 0
  · simp [hu, imag]
  · obtain ⟨a, rfl⟩ := h.dependent_of_area_zero u v hh hu ha
    simp only [imag, map_smul_right, star_def, conj_ofReal, mul_im, ofReal_re,
      ofReal_im, diag_im, mul_zero, zero_mul, add_zero]

theorem area_pos [Module ℝ V] [IsScalarTower ℝ ℂ V] (hh : h.Pos)
    (hind : LinearIndependent ℝ ![u, v]) : 0 < h.area u v := by
  have hn := h.area_nonneg u v (h.nonneg_of_pos hh)
  by_contra H
  have hz : h.area u v = 0 := le_antisymm (le_of_not_gt H) hn
  obtain ⟨hv, hi⟩ := linearIndependent_fin2.mp hind
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hv hi
  obtain ⟨a, heq⟩ := h.dependent_of_area_zero v u hh hv (by rwa [area_symm])
  apply hi a
  rw [← IsScalarTower.algebraMap_smul ℂ a v]
  exact heq.symm

theorem withVertical_pos (hh : h.Pos) : h.withVertical.Pos := by
  intro p hp
  rw [withVertical_q]
  have hn := h.nonneg_of_pos hh p.1
  by_cases hz : p.1 = 0
  · have hv : p.2 ≠ 0 := by
      intro hv
      apply hp
      exact Prod.ext hz hv
    have := Complex.normSq_pos.mpr hv
    simpa [hz] using this
  · exact add_pos_of_pos_of_nonneg (hh p.1 hz) (Complex.normSq_nonneg _)

theorem area_le_of_bound (hh : h.Pos) (hE : E.Nonneg) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ w, E.q w ≤ C * h.q w) : E.area u v ≤ C ^ 2 * h.area u v := by
  by_cases hu : u = 0
  · simp [hu, area]
  have hqu := hh u hu
  let a : ℝ := (h u v).re / h.q u
  let w : V := v - (a : ℂ) • u
  have hw : h.q w = h.area u v / h.q u := by
    rw [q_shear]
    dsimp [a, area]
    field_simp
    ; ring
  have hgram : E.area u v ≤ E.q u * E.q w := by
    change E.area u v ≤ E.q u * E.q (v - (a : ℂ) • u)
    rw [E.q_shear a u v]
    dsimp [area]
    linarith only [sq_nonneg (E.q u * a - (E u v).re)]
  have hmul := mul_le_mul (hbound u) (hbound w) (hE w)
    (mul_nonneg hC hqu.le)
  rw [hw] at hmul
  have halg : C * h.q u * (C * (h.area u v / h.q u)) = C ^ 2 * h.area u v := by
    field_simp
  rw [halg] at hmul
  exact hgram.trans hmul

theorem area_ge_of_bound (hh : h.Pos) (hE : E.Pos) (c : ℝ) (hc : 0 < c)
    (hbound : ∀ w, c * h.q w ≤ E.q w) : c ^ 2 * h.area u v ≤ E.area u v := by
  have H := E.area_le_of_bound h u v hE (h.nonneg_of_pos hh) (1 / c)
    (by positivity) (fun w ↦ by
      have H := (le_div_iff₀ hc).mpr (show h.q w * c ≤ E.q w by simpa [mul_comm] using hbound w)
      simpa [div_eq_mul_inv, mul_comm] using H)
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have H' := mul_le_mul_of_nonneg_left H hc2.le
  have heq : c ^ 2 * ((1 / c) ^ 2 * E.area u v) = E.area u v := by field_simp
  rwa [heq] at H'

theorem scale_pos (hh : h.Pos) {a : ℝ} (ha : 0 < a) : (h.scale a).Pos := by
  intro u hu
  rw [scale_q]
  exact mul_pos ha (hh u hu)

end HForm

variable (h E : HForm V) (u v : V) (y z : ℂ)

theorem vertical_area_eq : verticalArea y z = verticalImag y z ^ 2 := by
  simp [verticalArea, verticalImag, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem xi_q : h.q (xi u v y z) = mixed h u v y z + 2 * h.imag u v * verticalImag y z := by
  simp only [xi, HForm.q_sub, HForm.q_smul, HForm.map_smul_left, HForm.map_smul_right]
  simp [mixed, HForm.imag, verticalImag, Complex.normSq_apply, Complex.mul_re,
    Complex.mul_im]
  ring

theorem augmented_area : h.withVertical.area (u, y) (v, z) =
    h.area u v + verticalArea y z + mixed h u v y z := by
  rw [HForm.area, HForm.withVertical_q, HForm.withVertical_q]
  change (h.q u + Complex.normSq y) * (h.q v + Complex.normSq z) -
    (h u v + y * star z).re ^ 2 = _
  simp only [Complex.add_re, HForm.area, verticalArea, mixed]
  ring

theorem P_xi : P h E u v y z = h.area u v + 3 * h.imag u v ^ 2 +
    4 * verticalImag y z ^ 2 + E.q (xi u v y z) +
    4 * E.imag u v * verticalImag y z := by
  rw [P, vertical_area_eq, xi_q]
  ring

private theorem root_interpolate {A b : ℝ} (hA : 0 ≤ A) :
    (Real.sqrt A + 3 * |b|) / 2 ≤ Real.sqrt (A + 3 * b ^ 2) := by
  have hpos : 0 ≤ A + 3 * b ^ 2 := by positivity
  have hsA := Real.sq_sqrt hA
  have hsB := Real.sq_sqrt hpos
  have hnA := Real.sqrt_nonneg A
  have hnB := Real.sqrt_nonneg (A + 3 * b ^ 2)
  have hab := abs_nonneg b
  have hab2 : |b| ^ 2 = b ^ 2 := sq_abs b
  nlinarith [sq_nonneg (Real.sqrt A - |b|)]

theorem pinch_square_with_xi (hh : h.Pos) (hl : h.Below E) (beta : ℝ)
    (hu : ∀ w, E.q w ≤ (2 - beta) * h.q w) (ha : 0 < h.area u v) :
    (Real.sqrt (h.area u v + 3 * h.imag u v ^ 2) - 2 * |verticalImag y z|) ^ 2 +
      2 * beta * (Real.sqrt (h.area u v) + |h.imag u v|) * |verticalImag y z| ≤
        P h E u v y z - E.q (xi u v y z) := by
  have hu0 : u ≠ 0 := by
    intro he; subst u; simp [HForm.area] at ha
  have hqu := hh u hu0
  have hL : 1 ≤ 2 - beta := by nlinarith [hl u, hu u]
  have hi := h.imaginary_bound E u v hh (2 - beta) hL hl hu ha
  have hr := root_interpolate (b := h.imag u v) ha.le
  have hib : |E.imag u v| ≤ Real.sqrt (h.area u v + 3 * h.imag u v ^ 2) -
      beta * (Real.sqrt (h.area u v) + |h.imag u v|) / 2 := by linarith [hi, hr]
  have hm := mul_le_mul_of_nonneg_right hib (abs_nonneg (verticalImag y z))
  have hab : -(|E.imag u v| * |verticalImag y z|) ≤ E.imag u v * verticalImag y z := by
    rw [← abs_mul]
    exact neg_abs_le _
  have hs := Real.sq_sqrt (show 0 ≤ h.area u v + 3 * h.imag u v ^ 2 by positivity)
  have hv := sq_abs (verticalImag y z)
  rw [P_xi]
  linarith

theorem pinch_zero_area [Module ℝ V] [IsScalarTower ℝ ℂ V]
    (hh : h.Pos) (hl : h.Below E)
    (hind : LinearIndependent ℝ ![(u, y), (v, z)])
    (haz : h.area u v * verticalArea y z = 0) : 0 < P h E u v y z := by
  have hn := h.nonneg_of_pos hh
  have hcross : h.imag u v * verticalImag y z = 0 ∧ E.imag u v * verticalImag y z = 0 := by
    rcases mul_eq_zero.mp haz with ha | hU
    · exact ⟨by rw [h.imag_eq_zero_of_area_zero h u v hh ha, zero_mul],
        by rw [h.imag_eq_zero_of_area_zero E u v hh ha, zero_mul]⟩
    · rw [vertical_area_eq] at hU
      have hv : verticalImag y z = 0 := sq_eq_zero_iff.mp hU
      simp [hv]
  have hpos := h.withVertical.area_pos (u, y) (v, z) (h.withVertical_pos hh) hind
  rw [augmented_area] at hpos
  have hXi := xi_q h u v y z
  have hE := hl (xi u v y z)
  have hA := h.area_nonneg u v hn
  have hU : 0 ≤ verticalArea y z := by rw [vertical_area_eq]; positivity
  rw [P_xi]
  rw [vertical_area_eq] at hpos hU
  linarith [sq_nonneg (h.imag u v)]

private theorem square_gap_core {s t b r delta q : ℝ}
    (ht : 0 ≤ t) (hbs : 0 ≤ b) (hbt : b ≤ t) (hst : t ≤ s) (hsts : s ≤ 2 * t)
    (hr : 0 ≤ r) (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1) (hq : 1 ≤ q) :
    (s - 2 * r) ^ 2 / 4 + delta * t ^ 2 / 8 - 5 * t ^ 2 / (4 * q) ≤
      (s - 2 * r) ^ 2 + 2 * (delta - 1 / (4 * q)) * (t + b) * r := by
  have hq0 : 0 < q := by linarith
  have htr : t * r ≤ (5 * t ^ 2 + (s - 2 * r) ^ 2) / 4 := by
    have H := mul_nonneg (show 0 ≤ 2 * t by positivity) (sub_nonneg.mpr hsts)
    linarith only [H, sq_nonneg (s - 2 * r + t)]
  have hgap : delta * t ^ 2 / 8 ≤ (s - 2 * r) ^ 2 / 2 + 2 * delta * t * r := by
    by_cases H : t / 4 ≤ r
    · have H' := mul_nonneg (show 0 ≤ delta * t by positivity) (sub_nonneg.mpr H)
      have H'' := mul_nonneg hd0 (sq_nonneg t)
      linarith only [H', H'', sq_nonneg (s - 2 * r)]
    · have hd : t / 2 ≤ s - 2 * r := by linarith only [hst, H]
      have H' : t ^ 2 / 4 ≤ (s - 2 * r) ^ 2 := by
        have hp := mul_nonneg (sub_nonneg.mpr hd)
          (show 0 ≤ s - 2 * r + t / 2 by linarith only [hd, ht])
        linarith only [hp]
      have hdA := mul_le_mul_of_nonneg_right hd1 (sq_nonneg t)
      have hpos : 0 ≤ delta * t * r := by positivity
      linarith only [H', hdA, hpos]
  have hpos : 2 * delta * t * r ≤ 2 * delta * (t + b) * r := by
    have H : 0 ≤ 2 * delta * b * r := by positivity
    linarith only [H]
  have hneg : (t + b) * r / (2 * q) ≤ t * r / q := by
    apply (div_le_iff₀ (show 0 < 2 * q by positivity)).mpr
    have H := mul_le_mul_of_nonneg_right hbt hr
    field_simp
    linarith only [H]
  have htrq := div_le_div_of_nonneg_right htr hq0.le
  have hsqQ : (s - 2 * r) ^ 2 / (4 * q) ≤ (s - 2 * r) ^ 2 / 4 := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num)
    linarith
  have hid : (s - 2 * r) ^ 2 + 2 * (delta - 1 / (4 * q)) * (t + b) * r =
      (s - 2 * r) ^ 2 + 2 * delta * (t + b) * r - (t + b) * r / (2 * q) := by ring
  have hid2 : (5 * t ^ 2 + (s - 2 * r) ^ 2) / 4 / q =
      5 * t ^ 2 / (4 * q) + (s - 2 * r) ^ 2 / (4 * q) := by ring
  rw [hid2] at htrq
  rw [hid]
  linarith only [hgap, hpos, hneg, htrq, hsqQ]

private theorem sqrt_product_young {L A B : ℝ} (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsq : L ^ 2 = A * B) : L ≤ (A + B) / 2 := by
  have H : L ^ 2 ≤ ((A + B) / 2) ^ 2 := by linarith only [hsq, sq_nonneg (A - B)]
  exact (sq_le_sq₀ hL (by positivity)).mp H

private theorem three_error_absorb {e E c x A X Q : ℝ}
    (hE : 0 ≤ E) (hc : 0 < c) (hx : 0 ≤ x) (hA : 0 ≤ A) (hX : 0 ≤ X)
    (hQ : c * (1 + x) * X ≤ Q)
    (he : |e| ≤ E * Real.sqrt (x * (1 + x)) * Real.sqrt (A * X)) :
    |e| ≤ Q / 2 + E ^ 2 * x / (2 * c) * A := by
  let L := E * Real.sqrt (x * (1 + x)) * Real.sqrt (A * X)
  let R := E ^ 2 * x / c * A
  let Q0 := c * (1 + x) * X
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hQ0 : 0 ≤ Q0 := by dsimp [Q0]; positivity
  have hs1 := Real.sq_sqrt (show 0 ≤ x * (1 + x) by positivity)
  have hs2 := Real.sq_sqrt (mul_nonneg hA hX)
  have hsq : L ^ 2 = R * Q0 := by
    dsimp [L, R, Q0]
    rw [mul_pow, mul_pow, hs1, hs2]
    field_simp
  have H := sqrt_product_young hL hR hQ0 hsq
  have he' : |e| ≤ L := he
  have hid : R / 2 = E ^ 2 * x / (2 * c) * A := by dsimp [R]; ring
  change Q0 ≤ Q at hQ
  linarith only [H, he', hQ, hid]

private theorem threshold_positive {c C E : ℝ} (hc : 0 < c) (hC : c ≤ C) :
    0 < pinchingThreshold c C E := by
  apply lt_of_lt_of_le (show 0 < C + 1 by linarith)
  exact le_max_left _ _

private theorem large_q_coefficient {c C E lam x : ℝ}
    (hc : 0 < c) (hC : c ≤ C) (hE : 0 ≤ E) (hx : 0 ≤ x)
    (hlam : pinchingThreshold c C E ≤ lam) :
    0 < lam - errorCoefficient c E * x - 5 * C ^ 2 / 4 +
      (c ^ 2 / 8) * (c * Real.sqrt (x * (1 + x)) / (lam + C * x)) *
        (x * (1 + x)) := by
  let K := errorCoefficient c E
  let k := thresholdGap c C E
  let M := 5 * C ^ 2 / 4
  have hK : 0 ≤ K := by dsimp [K, errorCoefficient]; positivity
  have hCp : 0 < C := lt_of_lt_of_le hc hC
  have hk : 0 < k := by dsimp [k, thresholdGap]; change 0 < c ^ 3 / (8 * (2 * (K + 1) + C)); positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hClam : C + 1 ≤ lam := (le_max_left _ _).trans hlam
  have hlamrest : max (18 * C ^ 2 + K + 1)
      (max (2 * M + 1) (2 * (K + 1) * ((K + 1) / k + 1))) ≤ lam :=
    (le_max_right _ _).trans hlam
  have hlamM : 2 * M + 1 ≤ lam :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlamrest)
  have hlamX : 2 * (K + 1) * ((K + 1) / k + 1) ≤ lam :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlamrest)
  have hlam0 : 0 < lam := by linarith only [hClam, hCp]
  have hden : 0 < lam + C * x := add_pos_of_pos_of_nonneg hlam0 (mul_nonneg hCp.le hx)
  have hdelta : 0 ≤ c * Real.sqrt (x * (1 + x)) / (lam + C * x) := by positivity
  have hnon : 0 ≤ (c ^ 2 / 8) * (c * Real.sqrt (x * (1 + x)) / (lam + C * x)) * (x * (1 + x)) := by positivity
  change 0 < lam - K * x - M + _
  by_cases H : 2 * (K + 1) * x ≤ lam
  · have hKx : K * x ≤ lam / 2 := by linarith only [H, hx]
    linarith only [hKx, hlamM, hnon]
  · have H' : lam ≤ 2 * (K + 1) * x := (lt_of_not_ge H).le
    have hkp : 0 < 2 * (K + 1) := by linarith
    have hxk : (K + 1) / k + 1 ≤ x :=
      le_of_mul_le_mul_left (hlamX.trans H') hkp
    have hxk' : K + 1 ≤ k * x := by
      have := (div_le_iff₀ hk).mp (show (K + 1) / k ≤ x by linarith only [hxk])
      simpa [mul_comm] using this
    have hq : 0 ≤ x * (1 + x) := by positivity
    have hs2 := Real.sq_sqrt hq
    have hsr := Real.sqrt_nonneg (x * (1 + x))
    have hroot : x ≤ Real.sqrt (x * (1 + x)) := by nlinarith only [hs2, hsr, hx]
    have hkden : 0 < 2 * (K + 1) + C := by positivity
    have hδ : c / (2 * (K + 1) + C) ≤ c * Real.sqrt (x * (1 + x)) / (lam + C * x) := by
      apply (div_le_div_iff₀ hkden hden).mpr
      have H1 := mul_le_mul_of_nonneg_left H' hc.le
      have H2 := mul_le_mul_of_nonneg_left hroot (mul_nonneg hc.le hkden.le)
      linarith only [H1, H2]
    have hg := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hδ (show 0 ≤ c ^ 2 / 8 by positivity)) hq
    have heq : (c ^ 2 / 8) * (c / (2 * (K + 1) + C)) = k := by
      dsimp [k, thresholdGap, K]
      rw [div_mul_div_comm]
      congr 1
    rw [heq] at hg
    have hqx : x ^ 2 ≤ x * (1 + x) := by linarith only [hx]
    have h1 := mul_le_mul_of_nonneg_left hqx hk.le
    have h2 := mul_le_mul_of_nonneg_right hxk' hx
    linarith only [hg, h1, h2, hx, hlamM, hM]

theorem numerator_xi (g h D : HForm V) (lam x e4 e3 : ℝ) (u v : V) (y z : ℂ) :
    numerator g h D lam x e4 e3 u v y z =
      lam * (g.area u v + 3 * g.imag u v ^ 2) +
      x * (1 + x) * (h.area u v + 3 * h.imag u v ^ 2) +
      4 * verticalImag y z ^ 2 + D.q (xi u v y z) +
      4 * D.imag u v * verticalImag y z - e4 - e3 := by
  rw [numerator, xi_q, vertical_area_eq]
  ring

private theorem delta_bounds {c C lam x : ℝ} (hc : 0 < c) (hC : c ≤ C)
    (hx : 0 ≤ x) (hlam : C ≤ lam) (hlam0 : 0 < lam) :
    0 ≤ c * Real.sqrt (x * (1 + x)) / (lam + C * x) ∧
      c * Real.sqrt (x * (1 + x)) / (lam + C * x) ≤ 1 := by
  have hCp : 0 < C := lt_of_lt_of_le hc hC
  have hden : 0 < lam + C * x := by positivity
  have hsr := Real.sqrt_nonneg (x * (1 + x))
  have hs2 := Real.sq_sqrt (show 0 ≤ x * (1 + x) by positivity)
  have hsr' : Real.sqrt (x * (1 + x)) ≤ 1 + x := by
    nlinarith only [hsr, hs2, hx]
  constructor
  · positivity
  · apply (div_le_iff₀ hden).mpr
    have H1 := mul_le_mul_of_nonneg_left hsr' hc.le
    have H2 := mul_le_mul_of_nonneg_right hC (show 0 ≤ 1 + x by positivity)
    linarith only [H1, H2, hlam]

private theorem scaled_square_gap (h D : HForm V) (u v : V) (y z : ℂ)
    {x delta : ℝ} (hh : h.Pos) (hx : 0 ≤ x) (hq : 1 ≤ x * (1 + x))
    (ha : 0 < h.area u v) (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1)
    (hDl : ∀ w, (1 + x) * h.q w ≤ D.q w)
    (hDu : ∀ w, D.q w ≤ (2 + 1 / (4 * (x * (1 + x))) - delta) *
      Real.sqrt (x * (1 + x)) * h.q w) :
    D.q (xi u v y z) + delta * (x * (1 + x)) * h.area u v / 8 -
      5 * h.area u v / 4 ≤
      x * (1 + x) * (h.area u v + 3 * h.imag u v ^ 2) +
        4 * verticalImag y z ^ 2 + D.q (xi u v y z) +
        4 * D.imag u v * verticalImag y z := by
  let q := x * (1 + x)
  have hq0 : 0 < q := by dsimp [q]; linarith only [hq]
  have hsqp : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0.le
  have hsqu : Real.sqrt q ≤ 1 + x := by
    dsimp [q] at hsq
    nlinarith only [hsq, hx, hsqp]
  let H := h.scale (Real.sqrt q)
  have hHp : H.Pos := h.scale_pos hh hsqp
  have hA : H.area u v = q * h.area u v := by
    rw [HForm.scale_area, hsq]
  have hB : H.imag u v ^ 2 = q * h.imag u v ^ 2 := by
    rw [HForm.scale_imag, mul_pow, hsq]
  have hHa : 0 < H.area u v := by rw [hA]; positivity
  have hl : H.Below D := by
    intro w
    rw [HForm.scale_q]
    exact (mul_le_mul_of_nonneg_right hsqu (h.nonneg_of_pos hh w)).trans (hDl w)
  have hu : ∀ w, D.q w ≤ (2 - (delta - 1 / (4 * q))) * H.q w := by
    intro w
    rw [HForm.scale_q]
    convert hDu w using 1 ; dsimp [q] ; ring
  obtain hbound := pinch_square_with_xi H D u v y z hHp hl (delta - 1 / (4 * q)) hu hHa
  let t := Real.sqrt (H.area u v)
  let b := |H.imag u v|
  let s := Real.sqrt (H.area u v + 3 * H.imag u v ^ 2)
  let r := |verticalImag y z|
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hb : 0 ≤ b := abs_nonneg _
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = H.area u v := Real.sq_sqrt hHa.le
  have hb2 : b ^ 2 = H.imag u v ^ 2 := sq_abs _
  have hs2 : s ^ 2 = H.area u v + 3 * H.imag u v ^ 2 := Real.sq_sqrt (by positivity)
  have hgram := H.gram u v (H.nonneg_of_pos hHp)
  have hbt : b ≤ t := by nlinarith only [hgram, ht2, hb2, ht, hb]
  have hst : t ≤ s := by nlinarith only [ht2, hs2, ht, hs, sq_nonneg (H.imag u v)]
  have hsts : s ≤ 2 * t := by nlinarith only [ht2, hs2, ht, hs, hgram]
  have hgap := square_gap_core ht hb hbt hst hsts (abs_nonneg (verticalImag y z)) hd0 hd1 hq
  change (s - 2 * r) ^ 2 / 4 + delta * t ^ 2 / 8 - 5 * t ^ 2 / (4 * q) ≤ _ at hgap
  change (s - 2 * r) ^ 2 + 2 * (delta - 1 / (4 * q)) * (t + b) * r ≤ _ at hbound
  rw [ht2, hA] at hgap
  have hdiv : 5 * (q * h.area u v) / (4 * q) = 5 * h.area u v / 4 := by
    field_simp
  rw [hdiv] at hgap
  rw [P_xi, hA, hB] at hbound
  change D.q (xi u v y z) + delta * q * h.area u v / 8 - 5 * h.area u v / 4 ≤ _
  linarith only [hbound, hgap, sq_nonneg (s - 2 * r)]

theorem numerator_pos_from_bounds [Module ℝ V] [IsScalarTower ℝ ℂ V]
    (g h D : HForm V) (u v : V) (y z : ℂ) {c C E lam x e4 e3 : ℝ}
    (hg : g.Pos) (hc : 0 < c) (hC : c ≤ C) (hE : 0 ≤ E) (hx : 0 ≤ x)
    (hlam : pinchingThreshold c C E ≤ lam)
    (hhl : ∀ w, c * g.q w ≤ h.q w) (hhu : ∀ w, h.q w ≤ C * g.q w)
    (hDl : ∀ w, (1 + x) * h.q w ≤ D.q w)
    (hDu : ∀ w, D.q w ≤ (1 + 2 * x) * h.q w)
    (hDsharp : 0 < x * (1 + x) → ∀ w,
      D.q w ≤ (2 + 1 / (4 * (x * (1 + x))) -
        c * Real.sqrt (x * (1 + x)) / (lam + C * x)) *
        Real.sqrt (x * (1 + x)) * h.q w)
    (he4 : |e4| ≤ E * x * g.area u v)
    (he3 : |e3| ≤ E * Real.sqrt (x * (1 + x)) *
      Real.sqrt (g.area u v * g.q (xi u v y z)))
    (hind : LinearIndependent ℝ ![(u, y), (v, z)]) :
    0 < numerator g h D lam x e4 e3 u v y z := by
  have hgn := g.nonneg_of_pos hg
  have hh : h.Pos := fun w hw ↦ (mul_pos hc (hg w hw)).trans_le (hhl w)
  have hhn := h.nonneg_of_pos hh
  have hl : h.Below D := by
    intro w
    have H := mul_nonneg hx (hhn w)
    linarith only [H, hDl w]
  have hD : D.Pos := fun w hw ↦ (hh w hw).trans_le (hl w)
  have hDn := D.nonneg_of_pos hD
  have hCp : 0 < C := hc.trans_le hC
  have hA := g.area_nonneg u v hgn
  have hah := h.area_nonneg u v hhn
  have hAU := g.area_le_of_bound h u v hg hhn C hCp.le hhu
  have hAL := g.area_ge_of_bound h u v hg hh c hc hhl
  have hlam0 : 0 < lam := (threshold_positive hc hC).trans_le hlam
  have hClam : C + 1 ≤ lam := (le_max_left _ _).trans hlam
  have hK : 0 ≤ errorCoefficient c E := by dsimp [errorCoefficient]; positivity
  have hDQ : c * (1 + x) * g.q (xi u v y z) ≤ D.q (xi u v y z) := by
    have H := mul_le_mul_of_nonneg_left (hhl (xi u v y z))
      (show 0 ≤ 1 + x by positivity)
    linarith only [H, hDl (xi u v y z)]
  have hErr := three_error_absorb hE hc hx hA (hgn (xi u v y z)) hDQ he3
  by_cases hAz : g.area u v = 0
  · have hhz : h.area u v = 0 := by nlinarith only [hAU, hah, hAz]
    have hgb : g.imag u v = 0 := by
      have H := g.gram u v hgn
      rw [hAz] at H
      exact sq_eq_zero_iff.mp (le_antisymm H (sq_nonneg _))
    have hhb : h.imag u v = 0 := by
      have H := h.gram u v hhn
      rw [hhz] at H
      exact sq_eq_zero_iff.mp (le_antisymm H (sq_nonneg _))
    have he4z : e4 = 0 := by simpa [hAz, abs_nonpos_iff] using he4
    have he3z : e3 = 0 := by simpa [hAz, abs_nonpos_iff] using he3
    have H := pinch_zero_area h D u v y z hh hl hind (by rw [hhz, zero_mul])
    simpa [numerator, P, hAz, hhz, hgb, hhb, he4z, he3z] using H
  have hAp : 0 < g.area u v := lt_of_le_of_ne hA (Ne.symm hAz)
  have hhAp : 0 < h.area u v := (mul_pos (sq_pos_of_pos hc) hAp).trans_le hAL
  have hEq4 : e4 ≤ E * x * g.area u v := (le_abs_self _).trans he4
  have hEq3 : e3 ≤ D.q (xi u v y z) / 2 + E ^ 2 * x / (2 * c) * g.area u v :=
    (le_abs_self _).trans hErr
  have hLamB : 0 ≤ 3 * lam * g.imag u v ^ 2 := by positivity
  have hQ : 0 ≤ D.q (xi u v y z) := hDn _
  rw [numerator_xi]
  by_cases hsmall : x * (1 + x) < 1
  · have hx1 : x ≤ 1 := by linarith only [hsmall, sq_nonneg x]
    have hDbound : ∀ w, D.q w ≤ (3 * C) * g.q w := by
      intro w
      have H1 := mul_le_mul_of_nonneg_left (hhu w) (show 0 ≤ 1 + 2 * x by positivity)
      have H2 := mul_nonneg (show 0 ≤ 2 * (1 - x) * C by positivity) (hgn w)
      linarith only [H1, H2, hDu w]
    have hAD := g.area_le_of_bound D u v hg hDn (3 * C) (by positivity) hDbound
    have hBD : |D.imag u v| ≤ 3 * C * Real.sqrt (g.area u v) := by
      have hs := Real.sq_sqrt hA
      have hb := D.gram u v hDn
      have hbs := sq_abs (D.imag u v)
      have hn : 0 ≤ 3 * C * Real.sqrt (g.area u v) := by positivity
      exact (sq_le_sq₀ (abs_nonneg _) hn).mp (by nlinarith only [hs, hb, hAD, hbs])
    have hprod := mul_le_mul_of_nonneg_right hBD (abs_nonneg (verticalImag y z))
    have hneg : -(|D.imag u v| * |verticalImag y z|) ≤
        D.imag u v * verticalImag y z := by rw [← abs_mul]; exact neg_abs_le _
    have hs := Real.sq_sqrt hA
    have hsv := sq_abs (verticalImag y z)
    have hcross : -18 * C ^ 2 * g.area u v ≤
        4 * verticalImag y z ^ 2 + 4 * D.imag u v * verticalImag y z := by
      have H := sq_nonneg (|verticalImag y z| - 3 * C * Real.sqrt (g.area u v))
      nlinarith only [hprod, hneg, hs, hsv, H, sq_nonneg (verticalImag y z)]
    have hqx : 0 ≤ x * (1 + x) * (h.area u v + 3 * h.imag u v ^ 2) := by positivity
    have hKL : 18 * C ^ 2 + errorCoefficient c E + 1 ≤ lam :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hlam)
    have hcoeff : 0 < lam - 18 * C ^ 2 - errorCoefficient c E := by linarith only [hKL]
    have hstrict := mul_pos hcoeff hAp
    have hEid : E * x * g.area u v + E ^ 2 * x / (2 * c) * g.area u v =
        errorCoefficient c E * x * g.area u v := by dsimp [errorCoefficient]; ring
    have hKbound := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hx1 hK) hA
    linarith only [hstrict, hKbound, hEid, hEq4, hEq3, hLamB, hQ, hqx, hcross]
  · have hlarge : 1 ≤ x * (1 + x) := le_of_not_gt hsmall
    have hq0 : 0 < x * (1 + x) := by linarith only [hlarge]
    let delta := c * Real.sqrt (x * (1 + x)) / (lam + C * x)
    have hd := delta_bounds hc hC hx (by linarith only [hClam]) hlam0
    have hgap := scaled_square_gap h D u v y z hh hx hlarge hhAp hd.1 hd.2 hDl (hDsharp hq0)
    have hterm := mul_le_mul_of_nonneg_left hAL
      (show 0 ≤ delta * (x * (1 + x)) / 8 by dsimp [delta]; positivity)
    have hloss := mul_le_mul_of_nonneg_left hAU (show (0 : ℝ) ≤ 5 / 4 by norm_num)
    have hcoef := large_q_coefficient hc hC hE hx hlam
    have hstrict := mul_pos hcoef hAp
    have hEid : E * x * g.area u v + E ^ 2 * x / (2 * c) * g.area u v =
        errorCoefficient c E * x * g.area u v := by dsimp [errorCoefficient]; ring
    change D.q (xi u v y z) + delta * (x * (1 + x)) * h.area u v / 8 -
      5 * h.area u v / 4 ≤ _ at hgap
    change 0 < (lam - errorCoefficient c E * x - 5 * C ^ 2 / 4 +
      c ^ 2 / 8 * delta * (x * (1 + x))) * g.area u v at hstrict
    linarith only [hstrict, hterm, hloss, hEq4, hEq3, hEid, hgap, hLamB, hQ]

end PlaneAlgebra
end PinchedHartogs

namespace PinchedHartogs.PlaneAlgebra
namespace MatrixAlgebra
open Matrix Unitary
open scoped ComplexOrder
variable {n : Type uKahler5342_1} [finiteIndex : Fintype n] [decidableIndex : DecidableEq n]

omit finiteIndex decidableIndex in
private theorem hermitian_diag_real {n : Type uKahler5342_1} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian) (x : n → ℂ) :
    ((dotProduct (star x) (A *ᵥ x)).re : ℂ) = dotProduct (star x) (A *ᵥ x) := by
  simpa only [form, star_star] using (form A hA).diag_real (star x)

theorem form_nonneg_iff (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (form A hA).Nonneg ↔ A.PosSemidef := by
  constructor
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA
    intro x
    rw [← hermitian_diag_real A hA x]
    exact_mod_cast (show 0 ≤ (dotProduct (star x) (A *ᵥ x)).re by simpa using h (star x))
  · intro h u
    have H := h.dotProduct_mulVec_nonneg (star u)
    simpa only [form_q, star_star] using (Complex.nonneg_iff.mp H).1

theorem nonneg_difference_iff (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A - B).PosSemidef ↔ ∀ u, (form B hB).q u ≤ (form A hA).q u := by
  rw [← form_nonneg_iff (A - B) (hA.sub hB)]
  simp only [HForm.Nonneg, form_q, sub_mulVec, dotProduct_sub, Complex.sub_re, sub_nonneg]

private theorem transport_nonneg (U : Matrix.unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    (conjStarAlgAut ℂ _ U A).PosSemidef ↔ A.PosSemidef := by
  constructor
  · intro h
    have H := h.mul_mul_conjTranspose_same (star (U : Matrix n n ℂ))
    simp [conjStarAlgAut_apply, Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose] at H
    simpa [← Matrix.mul_assoc] using H
  · intro h
    exact h.mul_mul_conjTranspose_same (U : Matrix n n ℂ)

private theorem transport_diagonal_nonneg (U : Matrix.unitaryGroup n ℂ) (d : n → ℝ) :
    (conjStarAlgAut ℂ _ U (diagonal (fun i ↦ (d i : ℂ)))).PosSemidef ↔ ∀ i, 0 ≤ d i := by
  rw [transport_nonneg, Matrix.posSemidef_diagonal_iff]
  simp

private theorem transport_real_smul (U : Matrix.unitaryGroup n ℂ) (A : Matrix n n ℂ) (r : ℝ) :
    conjStarAlgAut ℂ _ U (r • A) = r • conjStarAlgAut ℂ _ U A := by
  simp [conjStarAlgAut_apply]

omit finiteIndex decidableIndex in
private theorem diagonal_real_smul {n : Type uKahler5342_1} [Fintype n] [DecidableEq n] (d : n → ℝ) (r : ℝ) :
    (diagonal (fun i ↦ ((r * d i : ℝ) : ℂ)) : Matrix n n ℂ) =
      r • diagonal (fun i ↦ (d i : ℂ)) := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

omit finiteIndex decidableIndex in
private theorem diagonal_sub_scalar {n : Type uKahler5342_1} [Fintype n] [DecidableEq n] (d : n → ℝ) (r : ℝ) :
    (diagonal (fun i ↦ ((d i - r : ℝ) : ℂ)) : Matrix n n ℂ) =
      diagonal (fun i ↦ (d i : ℂ)) - r • 1 := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

omit finiteIndex decidableIndex in
private theorem scalar_sub_diagonal {n : Type uKahler5342_1} [Fintype n] [DecidableEq n] (d : n → ℝ) (r : ℝ) :
    (diagonal (fun i ↦ ((r - d i : ℝ) : ℂ)) : Matrix n n ℂ) =
      r • 1 - diagonal (fun i ↦ (d i : ℂ)) := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

theorem spectral_interval (A : Matrix n n ℂ) (hA : A.IsHermitian) {c C : ℝ}
    (hl : ∀ w, c * (form 1 Matrix.isHermitian_one).q w ≤ (form A hA).q w)
    (hu : ∀ w, (form A hA).q w ≤ C * (form 1 Matrix.isHermitian_one).q w) :
    ∀ i, c ≤ hA.eigenvalues i ∧ hA.eigenvalues i ≤ C := by
  have hcH : (c • (1 : Matrix n n ℂ)).IsHermitian := Matrix.isHermitian_one.smul (by rfl)
  have hCH : (C • (1 : Matrix n n ℂ)).IsHermitian := Matrix.isHermitian_one.smul (by rfl)
  have hL : (A - c • 1).PosSemidef := (nonneg_difference_iff _ _ hA hcH).mpr (by
    intro w
    simpa only [form_q, smul_mulVec, dotProduct_smul, Complex.smul_re, smul_eq_mul] using hl w)
  have hU : (C • 1 - A).PosSemidef := (nonneg_difference_iff _ _ hCH hA).mpr (by
    intro w
    simpa only [form_q, smul_mulVec, dotProduct_smul, Complex.smul_re, smul_eq_mul] using hu w)
  have eL : conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (diagonal (fun i ↦ ((hA.eigenvalues i - c : ℝ) : ℂ))) = A - c • 1 := by
    rw [diagonal_sub_scalar, map_sub, transport_real_smul, map_one]
    congr 1
    exact hA.spectral_theorem.symm
  have eU : conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (diagonal (fun i ↦ ((C - hA.eigenvalues i : ℝ) : ℂ))) = C • 1 - A := by
    rw [scalar_sub_diagonal, map_sub, transport_real_smul, map_one]
    congr 1
    exact hA.spectral_theorem.symm
  rw [← eL, transport_diagonal_nonneg] at hL
  rw [← eU, transport_diagonal_nonneg] at hU
  intro i
  exact ⟨sub_nonneg.mp (hL i), sub_nonneg.mp (hU i)⟩

omit finiteIndex decidableIndex in
private theorem diagonal_metric {n : Type uKahler5342_1} [Fintype n] [DecidableEq n] (d : n → ℝ) (lam x : ℝ) :
    (diagonal (fun i ↦ ((lam + x * d i : ℝ) : ℂ)) : Matrix n n ℂ) =
      lam • 1 + x • diagonal (fun i ↦ (d i : ℂ)) := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

theorem mixedMatrix_spectral (A : Matrix n n ℂ) (hA : A.IsHermitian) {lam x : ℝ}
    (hden : ∀ i, lam + x * hA.eigenvalues i ≠ 0) :
    mixedMatrix A lam x = conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (diagonal (fun i ↦ (((1 + 2 * x) * hA.eigenvalues i -
        x * (1 + x) * hA.eigenvalues i ^ 2 / (lam + x * hA.eigenvalues i) : ℝ) : ℂ))) := by
  let U := hA.eigenvectorUnitary
  let F := conjStarAlgAut ℂ _ U
  let d := hA.eigenvalues
  have hAe : A = F (diagonal (fun i ↦ (d i : ℂ))) := hA.spectral_theorem
  have hG : horizontalMetric A lam x = F (diagonal (fun i ↦ ((lam + x * d i : ℝ) : ℂ))) := by
    rw [diagonal_metric, map_add, transport_real_smul, transport_real_smul, map_one, ← hAe]
    rfl
  have hInv : (horizontalMetric A lam x)⁻¹ =
      F (diagonal (fun i ↦ (((lam + x * d i)⁻¹ : ℝ) : ℂ))) := by
    apply Matrix.inv_eq_right_inv
    rw [hG, ← map_mul]
    have Hi : (diagonal (fun i ↦ ((lam + x * d i : ℝ) : ℂ)) : Matrix n n ℂ) *
        diagonal (fun i ↦ (((lam + x * d i)⁻¹ : ℝ) : ℂ)) = 1 := by
      rw [diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst j
        simp only [diagonal_apply_eq, one_apply_eq, ← Complex.ofReal_mul]
        rw [mul_inv_cancel₀ (hden i)]
        rfl
      · simp [hij]
    rw [Hi, map_one]
  calc
    mixedMatrix A lam x = F ((1 + 2 * x) • diagonal (fun i ↦ (d i : ℂ)) -
        (x * (1 + x)) • (diagonal (fun i ↦ (d i : ℂ)) *
          diagonal (fun i ↦ (((lam + x * d i)⁻¹ : ℝ) : ℂ)) * diagonal (fun i ↦ (d i : ℂ)))) := by
      rw [map_sub, transport_real_smul, transport_real_smul, map_mul, map_mul, ← hAe, ← hInv]
      rfl
    _ = _ := by
      congr 1
      ext i j
      by_cases hij : i = j
      · subst j
        simp [diagonal_mul_diagonal, d]
        ring
      · simp [diagonal_mul_diagonal, hij]

omit finiteIndex decidableIndex in
private theorem scalar_mixed_bounds {n : Type uKahler5342_1} [Fintype n] [DecidableEq n] {c C d lam x : ℝ}
    (hc : 0 < c) (hdc : c ≤ d) (hdC : d ≤ C) (hlam : C ≤ lam)
    (hlam0 : 0 < lam) (hx : 0 ≤ x) :
    (1 + x) * d ≤ (1 + 2 * x) * d - x * (1 + x) * d ^ 2 / (lam + x * d) ∧
      ((1 + 2 * x) * d - x * (1 + x) * d ^ 2 / (lam + x * d) ≤ (1 + 2 * x) * d) := by
  have hd : 0 < d := hc.trans_le hdc
  have hden : 0 < lam + x * d := by positivity
  have hf0 : 0 ≤ x * (1 + x) * d ^ 2 / (lam + x * d) := by positivity
  have hf1 : x * (1 + x) * d ^ 2 / (lam + x * d) ≤ x * d := by
    apply (div_le_iff₀ hden).mpr
    have H := mul_le_mul_of_nonneg_left (hdC.trans hlam) (show 0 ≤ x * d by positivity)
    linarith only [H]
  constructor <;> linarith only [hf0, hf1]

omit finiteIndex decidableIndex in
private theorem scalar_mixed_sharp {n : Type uKahler5342_1} [Fintype n] [DecidableEq n] {c C d lam x : ℝ}
    (hc : 0 < c) (hdc : c ≤ d) (hdC : d ≤ C) (hlam0 : 0 < lam)
    (hx : 0 ≤ x) (hq : 0 < x * (1 + x)) :
    (1 + 2 * x) * d - x * (1 + x) * d ^ 2 / (lam + x * d) ≤
      (2 + 1 / (4 * (x * (1 + x))) -
        c * Real.sqrt (x * (1 + x)) / (lam + C * x)) *
          Real.sqrt (x * (1 + x)) * d := by
  let q := x * (1 + x)
  have hd : 0 < d := hc.trans_le hdc
  have hC : 0 < C := hd.trans_le hdC
  have hdenD : 0 < lam + x * d := by positivity
  have hdenC : 0 < lam + C * x := by positivity
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  have hsqp : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hu : 1 + 2 * x ≤ (2 + 1 / (4 * q)) * Real.sqrt q := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    have heq : ((2 + 1 / (4 * q)) * Real.sqrt q) ^ 2 - (1 + 2 * x) ^ 2 = 1 / (16 * q) := by
      rw [mul_pow, hsq]
      have hqn : q ≠ 0 := hq.ne'
      field_simp [hqn]
      dsimp [q]
      ring
    have H : 0 ≤ 1 / (16 * q) := by positivity
    linarith only [heq, H]
  have hratio : c / (lam + C * x) ≤ d / (lam + x * d) := by
    apply div_le_div₀ hd.le hdc hdenD
    linarith only [mul_le_mul_of_nonneg_left hdC hx]
  have hf := mul_le_mul_of_nonneg_left hratio (mul_nonneg hq.le hd.le)
  have hprod := mul_le_mul_of_nonneg_right hu hd.le
  have heq : (c * Real.sqrt q / (lam + C * x)) * Real.sqrt q * d =
      q * d * (c / (lam + C * x)) := by
    calc
      _ = c * (Real.sqrt q ^ 2) * d / (lam + C * x) := by ring
      _ = _ := by rw [hsq]; ring
  change (1 + 2 * x) * d - q * d ^ 2 / (lam + x * d) ≤
    (2 + 1 / (4 * q) - c * Real.sqrt q / (lam + C * x)) * Real.sqrt q * d
  change q * d * (c / (lam + C * x)) ≤ q * d * (d / (lam + x * d)) at hf
  calc
    _ = (1 + 2 * x) * d - q * d * (d / (lam + x * d)) := by ring
    _ ≤ (2 + 1 / (4 * q)) * Real.sqrt q * d - q * d * (c / (lam + C * x)) :=
      sub_le_sub hprod hf
    _ = _ := by rw [← heq]; ring

theorem spectral_comparison (U : Matrix.unitaryGroup n ℂ) (d e : n → ℝ)
    (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAe : A = conjStarAlgAut ℂ _ U (diagonal (fun i ↦ (d i : ℂ))))
    (hBe : B = conjStarAlgAut ℂ _ U (diagonal (fun i ↦ (e i : ℂ))))
    (hle : ∀ i, d i ≤ e i) : (form A hA).Below (form B hB) := by
  apply (nonneg_difference_iff B A hB hA).mp
  have H : (conjStarAlgAut ℂ _ U (diagonal (fun i ↦ ((e i - d i : ℝ) : ℂ)))).PosSemidef :=
    (transport_diagonal_nonneg U _).mpr (fun i ↦ sub_nonneg.mpr (hle i))
  have eSub : (diagonal (fun i ↦ ((e i - d i : ℝ) : ℂ)) : Matrix n n ℂ) =
      diagonal (fun i ↦ (e i : ℂ)) - diagonal (fun i ↦ (d i : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [eSub, map_sub, ← hAe, ← hBe] at H
  exact H

private theorem spectral_real_scaling (U : Matrix.unitaryGroup n ℂ) (d : n → ℝ)
    (A : Matrix n n ℂ) (r : ℝ)
    (hAe : A = conjStarAlgAut ℂ _ U (diagonal (fun i ↦ (d i : ℂ)))) :
    r • A = conjStarAlgAut ℂ _ U (diagonal (fun i ↦ ((r * d i : ℝ) : ℂ))) := by
  rw [diagonal_real_smul, transport_real_smul, ← hAe]

theorem form_one_pos : (form (1 : Matrix n n ℂ) Matrix.isHermitian_one).Pos := by
  intro u hu
  rw [form_one_q]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
  apply Finset.sum_pos'
  · intro j _; exact Complex.normSq_nonneg _
  · exact ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩

theorem mixedMatrix_bounds (A : Matrix n n ℂ) (hA : A.IsHermitian) {c C lam x : ℝ}
    (hc : 0 < c) (hlam : C ≤ lam) (hlam0 : 0 < lam) (hx : 0 ≤ x)
    (hl : ∀ w, c * (form 1 Matrix.isHermitian_one).q w ≤ (form A hA).q w)
    (hu : ∀ w, (form A hA).q w ≤ C * (form 1 Matrix.isHermitian_one).q w) :
    let h := form A hA
    let D := form (mixedMatrix A lam x) (mixedMatrix_hermitian A hA lam x)
    (∀ w, (1 + x) * h.q w ≤ D.q w) ∧
    (∀ w, D.q w ≤ (1 + 2 * x) * h.q w) ∧
    (0 < x * (1 + x) → ∀ w, D.q w ≤
      (2 + 1 / (4 * (x * (1 + x))) -
        c * Real.sqrt (x * (1 + x)) / (lam + C * x)) *
          Real.sqrt (x * (1 + x)) * h.q w) := by
  dsimp only
  let d := hA.eigenvalues
  let f := fun i ↦ (1 + 2 * x) * d i - x * (1 + x) * d i ^ 2 / (lam + x * d i)
  let U := hA.eigenvectorUnitary
  have hi := spectral_interval A hA hl hu
  have hdp : ∀ i, 0 < d i := fun i ↦ hc.trans_le (hi i).1
  have hden : ∀ i, lam + x * hA.eigenvalues i ≠ 0 := fun i ↦
    (add_pos_of_pos_of_nonneg hlam0 (mul_nonneg hx (hdp i).le)).ne'
  have hAe : A = conjStarAlgAut ℂ _ U (diagonal (fun i ↦ (d i : ℂ))) := hA.spectral_theorem
  have hDe : mixedMatrix A lam x = conjStarAlgAut ℂ _ U (diagonal (fun i ↦ (f i : ℂ))) :=
    mixedMatrix_spectral A hA hden
  have hb := fun i ↦ scalar_mixed_bounds (n := n) hc (hi i).1 (hi i).2 hlam hlam0 hx
  have hAA : ∀ r : ℝ, (r • A).IsHermitian := fun r ↦ hA.smul (by rfl)
  have hD := mixedMatrix_hermitian A hA lam x
  refine ⟨?_, ?_, ?_⟩
  · have H := spectral_comparison U (fun i ↦ (1 + x) * d i) f
      ((1 + x) • A) (mixedMatrix A lam x) (hAA _) hD
      (spectral_real_scaling U d A _ hAe) hDe (fun i ↦ (hb i).1)
    intro w
    simpa only [form_q, smul_mulVec, dotProduct_smul, Complex.smul_re, smul_eq_mul] using H w
  · have H := spectral_comparison U f (fun i ↦ (1 + 2 * x) * d i)
      (mixedMatrix A lam x) ((1 + 2 * x) • A) hD (hAA _)
      hDe (spectral_real_scaling U d A _ hAe) (fun i ↦ (hb i).2)
    intro w
    simpa only [form_q, smul_mulVec, dotProduct_smul, Complex.smul_re, smul_eq_mul] using H w
  · intro hq
    let r := (2 + 1 / (4 * (x * (1 + x))) -
      c * Real.sqrt (x * (1 + x)) / (lam + C * x)) * Real.sqrt (x * (1 + x))
    have H := spectral_comparison U f (fun i ↦ r * d i)
      (mixedMatrix A lam x) (r • A) hD (hAA _)
      hDe (spectral_real_scaling U d A _ hAe)
      (fun i ↦ scalar_mixed_sharp (n := n) hc (hi i).1 (hi i).2 hlam0 hx hq)
    intro w
    simpa only [form_q, smul_mulVec, dotProduct_smul, Complex.smul_re, smul_eq_mul] using H w

theorem actual_numerator_pos (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (u v : n → ℂ) (y z : ℂ) {c C E lam x e4 e3 : ℝ}
    (hc : 0 < c) (hC : c ≤ C) (hE : 0 ≤ E) (hx : 0 ≤ x)
    (hlam : pinchingThreshold c C E ≤ lam)
    (hl : ∀ w, c * (form 1 Matrix.isHermitian_one).q w ≤ (form A hA).q w)
    (hu : ∀ w, (form A hA).q w ≤ C * (form 1 Matrix.isHermitian_one).q w)
    (he4 : |e4| ≤ E * x * (form 1 Matrix.isHermitian_one).area u v)
    (he3 : |e3| ≤ E * Real.sqrt (x * (1 + x)) *
      Real.sqrt ((form 1 Matrix.isHermitian_one).area u v *
        (form 1 Matrix.isHermitian_one).q (xi u v y z)))
    (hind : LinearIndependent ℝ ![(u, y), (v, z)]) :
    0 < numerator (form 1 Matrix.isHermitian_one) (form A hA)
      (form (mixedMatrix A lam x) (mixedMatrix_hermitian A hA lam x))
        lam x e4 e3 u v y z := by
  have hlam0 : 0 < lam := (threshold_positive hc hC).trans_le hlam
  have hClam : C + 1 ≤ lam := (le_max_left _ _).trans hlam
  obtain ⟨hDl, hDu, hDs⟩ := mixedMatrix_bounds A hA hc (by linarith only [hClam]) hlam0 hx hl hu
  exact numerator_pos_from_bounds _ _ _ u v y z form_one_pos hc hC hE hx hlam
    hl hu hDl hDu hDs he4 he3 hind

end MatrixAlgebra
end PinchedHartogs.PlaneAlgebra

namespace PinchedHartogs.PlaneAlgebra
namespace TensorAlgebra
open MatrixAlgebra Matrix
variable {n : Type uKahler5693_1} [finiteIndex : Fintype n]

theorem eval_hol (T : Tensor n) (hT : Symmetries T) (u v w y : n → ℂ) :
    eval T u v w y = eval T w v u y := by
  unfold eval
  apply Fintype.sum_equiv swapHol
  intro t
  dsimp [swapHol]
  rw [hT.hol t.1 t.2.1 t.2.2.1 t.2.2.2]
  ring

theorem eval_anti (T : Tensor n) (hT : Symmetries T) (u v w y : n → ℂ) :
    eval T u v w y = eval T u y w v := by
  unfold eval
  apply Fintype.sum_equiv swapAnti
  intro t
  dsimp [swapAnti]
  rw [hT.anti t.1 t.2.1 t.2.2.1 t.2.2.2]
  ring

theorem eval_conj (T : Tensor n) (hT : Symmetries T) (u v w y : n → ℂ) :
    star (eval T u v w y) = eval T v u y w := by
  unfold eval
  rw [star_sum]
  apply Fintype.sum_equiv swapConj
  intro t
  dsimp [swapConj]
  simp only [map_mul, starRingEnd_self_apply]
  rw [show (starRingEnd ℂ) (T t.1 t.2.1 t.2.2.1 t.2.2.2) =
    T t.2.1 t.1 t.2.2.2 t.2.2.1 from hT.reality _ _ _ _]
  ring

theorem xiContract_expand (T : Tensor n) (u v : n → ℂ) :
    xiContract T u v = eval T u v u v - eval T u v v u -
      eval T v u u v + eval T v u v u := by
  unfold xiContract eval
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  dsimp [Xi]
  ring

theorem H_xi (T : Tensor n) (hT : Symmetries T) (u v : n → ℂ) :
    H T u v = -(xiContract T u v).re / 2 := by
  rw [xiContract_expand, eval_anti T hT u v v u, eval_hol T hT v u u v,
    ← eval_conj T hT u v u v]
  simp only [H, Complex.add_re, Complex.sub_re, Complex.star_def, Complex.conj_re]
  ring

theorem norm_component_le (T : Tensor n) (a b c d : n) :
    ‖T a b c d‖ ≤ componentNorm T := by
  have H := Finset.single_le_sum
    (fun t (_ : t ∈ (Finset.univ : Finset (Quad n))) ↦
      Complex.normSq_nonneg (T t.1 t.2.1 t.2.2.1 t.2.2.2))
    (Finset.mem_univ (a, b, c, d))
  change Complex.normSq (T a b c d) ≤ _ at H
  rw [Complex.normSq_eq_norm_sq] at H
  exact (Real.le_sqrt (norm_nonneg _)
    (Finset.sum_nonneg (fun _ _ ↦ Complex.normSq_nonneg _))).mpr H

theorem H_abs_bound (T : Tensor n) (hT : Symmetries T) (u v : n → ℂ) :
    |H T u v| ≤ (∑ t : Quad n, ‖T t.1 t.2.1 t.2.2.1 t.2.2.2‖ *
      ‖Xi u v t.1 t.2.1‖ * ‖Xi u v t.2.2.1 t.2.2.2‖) / 2 := by
  rw [H_xi T hT, abs_div, abs_neg]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply (Complex.abs_re_le_norm _).trans
  exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])

theorem xi_horizontal_norm (u v : Fin 2 → ℂ) :
    (∑ i, ∑ j, Complex.normSq (Xi u v i j)) =
      2 * (euclidean.area u v + euclidean.imag u v ^ 2) := by
  simp [euclidean, form, HForm.area, HForm.q, HForm.imag, Xi, dotProduct,
    Fin.sum_univ_two, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem xi_horizontal_bound (u v : Fin 2 → ℂ) (i j : Fin 2) :
    ‖Xi u v i j‖ ≤ 2 * Real.sqrt (euclidean.area u v) := by
  have hA := euclidean.area_nonneg u v (euclidean.nonneg_of_pos form_one_pos)
  have H1 : Complex.normSq (Xi u v i j) ≤ ∑ j, Complex.normSq (Xi u v i j) :=
    Finset.single_le_sum (fun _ _ ↦ Complex.normSq_nonneg _) (Finset.mem_univ j)
  have H2 : (∑ j, Complex.normSq (Xi u v i j)) ≤ ∑ i, ∑ j, Complex.normSq (Xi u v i j) :=
    Finset.single_le_sum (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ Complex.normSq_nonneg _))
      (Finset.mem_univ i)
  have H := H1.trans H2
  rw [xi_horizontal_norm, Complex.normSq_eq_norm_sq] at H
  have hg := euclidean.gram u v (euclidean.nonneg_of_pos form_one_pos)
  have hs := Real.sq_sqrt hA
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (by linarith only [H, hg, hs])

theorem xi_mixed_bound (u v : Fin 2 → ℂ) (y z : ℂ) (i : Fin 2) :
    ‖Xi (lift u y) (lift v z) (some i) none‖ ≤
      Real.sqrt (euclidean.q (xi u v y z)) := by
  have H : Complex.normSq (xi u v y z i) ≤ euclidean.q (xi u v y z) := by
    rw [form_one_q]
    exact Finset.single_le_sum (fun _ _ ↦ Complex.normSq_nonneg _) (Finset.mem_univ i)
  have heq : Xi (lift u y) (lift v z) (some i) none = xi u v y z i := by
    simp [Xi, lift, xi, mul_comm]
  rw [heq, Complex.normSq_eq_norm_sq] at *
  exact (Real.le_sqrt (norm_nonneg _)
    (euclidean.nonneg_of_pos form_one_pos _)).mpr H

omit finiteIndex in
theorem xi_reverse {n : Type uKahler5693_1} [Fintype n] (u v : n → ℂ) (a b : n) : Xi u v b a = -star (Xi u v a b) := by
  simp [Xi, mul_comm]

omit finiteIndex in
private theorem xi_mixed_reverse_bound {n : Type uKahler5693_1} [Fintype n] (u v : Fin 2 → ℂ) (y z : ℂ) (i : Fin 2) :
    ‖Xi (lift u y) (lift v z) none (some i)‖ ≤
      Real.sqrt (euclidean.q (xi u v y z)) := by
  rw [xi_reverse, norm_neg, norm_star]
  exact xi_mixed_bound u v y z i

omit finiteIndex in
private theorem xi_pair_four {n : Type uKahler5693_1} [Fintype n] (u v : Fin 2 → ℂ) (y z : ℂ) (a b c d : Index)
    (hcount : horizontalCount a b c d = 4) :
    ‖Xi (lift u y) (lift v z) a b‖ * ‖Xi (lift u y) (lift v z) c d‖ ≤
      4 * euclidean.area u v := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [horizontalCount] at hcount
  rename_i a b c d
  have hA := euclidean.area_nonneg u v (euclidean.nonneg_of_pos form_one_pos)
  calc
    _ ≤ (2 * Real.sqrt (euclidean.area u v)) *
        (2 * Real.sqrt (euclidean.area u v)) :=
      mul_le_mul (xi_horizontal_bound u v a b) (xi_horizontal_bound u v c d)
        (norm_nonneg _) (by positivity)
    _ = 4 * euclidean.area u v := by linarith only [Real.sq_sqrt hA]

private theorem xi_pair_three (u v : Fin 2 → ℂ) (y z : ℂ) (a b c d : Index)
    (hcount : horizontalCount a b c d = 3) :
    ‖Xi (lift u y) (lift v z) a b‖ * ‖Xi (lift u y) (lift v z) c d‖ ≤
      (2 * Real.sqrt (euclidean.area u v)) * Real.sqrt (euclidean.q (xi u v y z)) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [horizontalCount] at hcount
  · rename_i b c d
    calc
      _ ≤ Real.sqrt (euclidean.q (xi u v y z)) * (2 * Real.sqrt (euclidean.area u v)) :=
        mul_le_mul (xi_mixed_reverse_bound (n := Fin 2) u v y z b) (xi_horizontal_bound u v c d)
          (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by ring
  · rename_i a c d
    calc
      _ ≤ Real.sqrt (euclidean.q (xi u v y z)) * (2 * Real.sqrt (euclidean.area u v)) :=
        mul_le_mul (xi_mixed_bound u v y z a) (xi_horizontal_bound u v c d)
          (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by ring
  · rename_i a b d
    exact mul_le_mul (xi_horizontal_bound u v a b) (xi_mixed_reverse_bound (n := Fin 2) u v y z d)
      (norm_nonneg _) (by positivity)
  · rename_i a b c
    exact mul_le_mul (xi_horizontal_bound u v a b) (xi_mixed_bound u v y z c)
      (norm_nonneg _) (by positivity)

theorem four_error (T : Tensor Index) (hT : Symmetries T) (hs : Supported T 4)
    (u v : Fin 2 → ℂ) (y z : ℂ) :
    |H T (lift u y) (lift v z)| ≤ 162 * componentNorm T * euclidean.area u v := by
  have hA := euclidean.area_nonneg u v (euclidean.nonneg_of_pos form_one_pos)
  have hN : 0 ≤ componentNorm T := Real.sqrt_nonneg _
  refine (H_abs_bound T hT _ _).trans ?_
  calc
    _ ≤ (∑ t : Quad Index, 4 * componentNorm T * euclidean.area u v) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply Finset.sum_le_sum
      intro t _
      by_cases hcount : horizontalCount t.1 t.2.1 t.2.2.1 t.2.2.2 = 4
      · calc
          _ = ‖T t.1 t.2.1 t.2.2.1 t.2.2.2‖ *
              (‖Xi (lift u y) (lift v z) t.1 t.2.1‖ *
               ‖Xi (lift u y) (lift v z) t.2.2.1 t.2.2.2‖) := by ring
          _ ≤ componentNorm T * (4 * euclidean.area u v) :=
            mul_le_mul (norm_component_le T _ _ _ _)
              (xi_pair_four (n := Fin 2) u v y z _ _ _ _ hcount) (by positivity) hN
          _ = _ := by ring
      · rw [hs _ _ _ _ hcount, norm_zero, zero_mul, zero_mul]
        positivity
    _ = _ := by norm_num [Quad, Index]; ring

theorem three_error (T : Tensor Index) (hT : Symmetries T) (hs : Supported T 3)
    (u v : Fin 2 → ℂ) (y z : ℂ) :
    |H T (lift u y) (lift v z)| ≤ 81 * componentNorm T *
      Real.sqrt (euclidean.area u v) * Real.sqrt (euclidean.q (xi u v y z)) := by
  have hN : 0 ≤ componentNorm T := Real.sqrt_nonneg _
  refine (H_abs_bound T hT _ _).trans ?_
  calc
    _ ≤ (∑ t : Quad Index, 2 * componentNorm T * Real.sqrt (euclidean.area u v) *
        Real.sqrt (euclidean.q (xi u v y z))) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply Finset.sum_le_sum
      intro t _
      by_cases hcount : horizontalCount t.1 t.2.1 t.2.2.1 t.2.2.2 = 3
      · calc
          _ = ‖T t.1 t.2.1 t.2.2.1 t.2.2.2‖ *
              (‖Xi (lift u y) (lift v z) t.1 t.2.1‖ *
               ‖Xi (lift u y) (lift v z) t.2.2.1 t.2.2.2‖) := by ring
          _ ≤ componentNorm T * ((2 * Real.sqrt (euclidean.area u v)) *
              Real.sqrt (euclidean.q (xi u v y z))) :=
            mul_le_mul (norm_component_le T _ _ _ _)
              (xi_pair_three u v y z _ _ _ _ hcount) (by positivity) hN
          _ = _ := by ring
      · rw [hs _ _ _ _ hcount, norm_zero, zero_mul, zero_mul]
        positivity
    _ = _ := by norm_num [Quad, Index]; ring

section SymmetricTensor
variable [decidableIndex : DecidableEq n]

omit finiteIndex decidableIndex in
private theorem eval_product {n : Type uKahler5693_1} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) (u v w y : n → ℂ) :
    eval (productTensor A B) u v w y =
      dotProduct u (A *ᵥ star v) * dotProduct w (B *ᵥ star y) := by
  rw [mul_comm (dotProduct u _) (dotProduct w _)]
  simp only [eval, productTensor, Fintype.sum_prod_type, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

omit finiteIndex decidableIndex in
theorem eval_add {n : Type uKahler5693_1} [Fintype n] [DecidableEq n] (T Q : Tensor n) (u v w y : n → ℂ) :
    eval (T + Q) u v w y = eval T u v w y + eval Q u v w y := by
  simp only [eval, Pi.add_apply, add_mul, Finset.sum_add_distrib]

omit finiteIndex decidableIndex in
private theorem eval_permAnti {n : Type uKahler5693_1} [Fintype n] [DecidableEq n] (T : Tensor n) (u v w y : n → ℂ) :
    eval (fun a b c d ↦ T a d c b) u v w y = eval T u y w v := by
  unfold eval
  apply Fintype.sum_equiv swapAnti
  intro t
  dsimp [swapAnti]
  ring

theorem eval_S (A : Matrix n n ℂ) (u v w y : n → ℂ) :
    eval (S A) u v w y = dotProduct u (A *ᵥ star v) * dotProduct w (A *ᵥ star y) +
      dotProduct u (A *ᵥ star y) * dotProduct w (A *ᵥ star v) := by
  change eval (productTensor A A + (fun a b c d ↦ productTensor A A a d c b)) _ _ _ _ = _
  rw [eval_add, eval_product A A u v w y,
    eval_permAnti (productTensor A A) u v w y, eval_product]

theorem H_S (A : Matrix n n ℂ) (hA : A.IsHermitian) (u v : n → ℂ) :
    H (S A) u v = (form A hA).area u v + 3 * (form A hA).imag u v ^ 2 := by
  rw [H, eval_S, eval_S]
  change ((form A hA u u) * (form A hA v v) +
    (form A hA u v) * (form A hA v u)).re -
    ((form A hA u v) * (form A hA u v) +
    (form A hA u v) * (form A hA u v)).re = _
  rw [(form A hA).hermitian u v]
  simp only [HForm.area, HForm.q, HForm.imag, Complex.add_re,
    Complex.mul_re, HForm.diag_im, zero_mul, sub_zero, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

theorem H_add (T Q : Tensor n) (u v : n → ℂ) : H (T + Q) u v = H T u v + H Q u v := by
  simp only [H, eval_add, Complex.add_re]
  ring

omit finiteIndex decidableIndex in
theorem H_sub {n : Type uKahler5693_1} [Fintype n] [DecidableEq n] (T Q : Tensor n) (u v : n → ℂ) : H (T - Q) u v = H T u v - H Q u v := by
  simp only [H, eval, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Complex.sub_re]
  ring

omit finiteIndex decidableIndex in
theorem H_smul {n : Type uKahler5693_1} [Fintype n] [DecidableEq n] (r : ℝ) (T : Tensor n) (u v : n → ℂ) :
    H (r • T) u v = r * H T u v := by
  simp only [H, eval, Pi.smul_apply, Complex.real_smul]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

end SymmetricTensor

private theorem block_pair (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.IsHermitian) (r : ℝ) (u v : Fin 2 → ℂ) (y z : ℂ) :
    (form (block A r) (block_hermitian (n := Fin 2) A hA r)).val (lift u y) (lift v z) =
      (form A hA).val u v + (r : ℂ) * y * star z := by
  simp [form, dotProduct, Matrix.mulVec, Fintype.sum_option, block, lift]
  ring

private theorem horizontal_area (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian)
    (u v : Fin 2 → ℂ) (y z : ℂ) :
    (form (block A 0) (block_hermitian (n := Fin 2) A hA 0)).area (lift u y) (lift v z) =
      (form A hA).area u v := by
  simp only [HForm.area, HForm.q, block_pair A hA, Complex.ofReal_zero, zero_mul, add_zero]

private theorem horizontal_imag (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian)
    (u v : Fin 2 → ℂ) (y z : ℂ) :
    (form (block A 0) (block_hermitian (n := Fin 2) A hA 0)).imag (lift u y) (lift v z) =
      (form A hA).imag u v := by
  simp only [HForm.imag, block_pair A hA, Complex.ofReal_zero, zero_mul, add_zero]

private theorem H_horizontal (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian)
    (u v : Fin 2 → ℂ) (y z : ℂ) :
    H (S (block A 0)) (lift u y) (lift v z) =
      (form A hA).area u v + 3 * (form A hA).imag u v ^ 2 := by
  rw [H_S _ (block_hermitian (n := Fin 2) A hA 0), horizontal_area, horizontal_imag]

private theorem H_augmented (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian)
    (u v : Fin 2 → ℂ) (y z : ℂ) :
    H (S (block A 1)) (lift u y) (lift v z) =
      (form A hA).area u v + 3 * (form A hA).imag u v ^ 2 +
        4 * verticalArea y z + mixed (form A hA) u v y z +
          6 * (form A hA).imag u v * verticalImag y z := by
  rw [H_S _ (block_hermitian (n := Fin 2) A hA 1)]
  have hv := vertical_area_eq y z
  simp only [HForm.area, HForm.q, HForm.imag, block_pair A hA, Complex.ofReal_one,
    one_mul, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  simp only [verticalArea, verticalImag, mixed, HForm.q, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im] at hv ⊢
  linarith only [hv]

private theorem H_vertical (u v : Fin 2 → ℂ) (y z : ℂ) :
    H (S (block 0 1)) (lift u y) (lift v z) = 4 * verticalArea y z := by
  rw [H_augmented _ Matrix.isHermitian_zero]
  simp [form, HForm.area, HForm.q, HForm.imag, mixed]

theorem negative_numerator (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian)
    (lam x : ℝ) (T4 T3 : Tensor Index) (u v : Fin 2 → ℂ) (y z : ℂ) :
    -H (curvatureModel A lam x T4 T3) (lift u y) (lift v z) =
      numerator euclidean (form A hA)
        (form (mixedMatrix A lam x) (mixedMatrix_hermitian A hA lam x))
          lam x (H T4 (lift u y) (lift v z)) (H T3 (lift u y) (lift v z)) u v y z := by
  simp only [curvatureModel, H_add, H_sub, H_smul,
    H_horizontal _ Matrix.isHermitian_one, H_horizontal _ hA,
    H_horizontal _ (mixedMatrix_hermitian A hA lam x), H_vertical,
    H_augmented _ (mixedMatrix_hermitian A hA lam x), numerator, euclidean]
  ring

theorem curvatureModel_negative {c C Ce lam x : ℝ}
    (hc : 0 < c) (hC : c ≤ C) (hCe : 0 ≤ Ce) (hx : 0 ≤ x)
    (hlam : pinchingThreshold c C (162 * Ce) ≤ lam)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian)
    (hl : ∀ w, c * euclidean.q w ≤ (form A hA).q w)
    (hu : ∀ w, (form A hA).q w ≤ C * euclidean.q w)
    (T4 T3 : Tensor Index) (hT4 : Symmetries T4) (hT3 : Symmetries T3)
    (hs4 : Supported T4 4) (hs3 : Supported T3 3)
    (hn4 : componentNorm T4 ≤ Ce * x)
    (hn3 : componentNorm T3 ≤ Ce * Real.sqrt (x * (1 + x)))
    (u v : Fin 2 → ℂ) (y z : ℂ)
    (hind : LinearIndependent ℝ ![(u, y), (v, z)]) :
    H (curvatureModel A lam x T4 T3) (lift u y) (lift v z) < 0 := by
  have he4 : |H T4 (lift u y) (lift v z)| ≤
      (162 * Ce) * x * euclidean.area u v := by
    have hAr := euclidean.area_nonneg u v (euclidean.nonneg_of_pos form_one_pos)
    calc
      _ ≤ 162 * componentNorm T4 * euclidean.area u v := four_error T4 hT4 hs4 u v y z
      _ ≤ 162 * (Ce * x) * euclidean.area u v := by gcongr
      _ = _ := by ring
  have he3 : |H T3 (lift u y) (lift v z)| ≤
      (162 * Ce) * Real.sqrt (x * (1 + x)) *
        Real.sqrt (euclidean.area u v * euclidean.q (xi u v y z)) := by
    have hAr := euclidean.area_nonneg u v (euclidean.nonneg_of_pos form_one_pos)
    calc
      _ ≤ 81 * componentNorm T3 * Real.sqrt (euclidean.area u v) *
          Real.sqrt (euclidean.q (xi u v y z)) := three_error T3 hT3 hs3 u v y z
      _ ≤ 162 * (Ce * Real.sqrt (x * (1 + x))) * Real.sqrt (euclidean.area u v) *
          Real.sqrt (euclidean.q (xi u v y z)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact mul_le_mul (by norm_num) hn3 (Real.sqrt_nonneg _) (by norm_num)
      _ = _ := by rw [Real.sqrt_mul hAr]; ring
  have hp := actual_numerator_pos A hA u v y z hc hC (by positivity : 0 ≤ 162 * Ce)
    hx hlam hl hu he4 he3 hind
  rw [← negative_numerator A hA lam x T4 T3 u v y z] at hp
  linarith only [hp]

end TensorAlgebra
end PinchedHartogs.PlaneAlgebra

namespace PinchedHartogs.PlaneAlgebra
namespace TensorAlgebra
open MatrixAlgebra Matrix
open scoped ComplexOrder

section Rescaling
variable {n : Type uKahler6181_1} [finiteIndex : Fintype n]

theorem eval_pull (r : n → ℝ) (T : Tensor n) (u v w y : n → ℂ) :
    eval (pullTensor r T) u v w y =
      eval T (pullVector r u) (pullVector r v) (pullVector r w) (pullVector r y) := by
  apply Finset.sum_congr rfl
  intro t _
  simp only [pullTensor, pullVector, map_mul, Complex.star_def, Complex.conj_ofReal]
  ring

theorem H_pull (r : n → ℝ) (T : Tensor n) (u v : n → ℂ) :
    H (pullTensor r T) u v = H T (pullVector r u) (pullVector r v) := by
  simp only [H, eval_pull]

omit finiteIndex in
theorem pull_add {n : Type uKahler6181_1} [Fintype n] (r : n → ℝ) (T Q : Tensor n) :
    pullTensor r (T + Q) = pullTensor r T + pullTensor r Q := by
  ext a b c d
  simp only [pullTensor, Pi.add_apply, mul_add]

omit finiteIndex in
theorem pull_sub {n : Type uKahler6181_1} [Fintype n] (r : n → ℝ) (T Q : Tensor n) :
    pullTensor r (T - Q) = pullTensor r T - pullTensor r Q := by
  ext a b c d
  simp only [pullTensor, Pi.sub_apply, mul_sub]

omit finiteIndex in
theorem pull_smul {n : Type uKahler6181_1} [Fintype n] (r : n → ℝ) (s : ℝ) (T : Tensor n) :
    pullTensor r (s • T) = s • pullTensor r T := by
  ext a b c d
  simp only [pullTensor, Pi.smul_apply, Complex.real_smul]
  ring

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

omit finiteIndex in
theorem pull_S {n : Type uKahler6181_1} [Fintype n] [DecidableEq n] (r : n → ℝ) (A : Matrix n n ℂ) :
    pullTensor r (S A) = S (pullMatrix r A) := by
  ext a b c d
  simp only [pullTensor, S, pullMatrix]
  ring

end Rescaling

theorem horizontal_product (r : ℝ) (a b c d : Index) :
    horizontalScale r a * horizontalScale r b * horizontalScale r c * horizontalScale r d =
      r ^ horizontalCount a b c d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [horizontalScale, horizontalCount] <;> ring

theorem pull_supported (r : ℝ) (T : Tensor Index) {j : ℕ} (hs : Supported T j) :
    pullTensor (horizontalScale r) T = (r ^ j) • T := by
  ext a b c d
  by_cases hj : horizontalCount a b c d = j
  · simp only [pullTensor, Pi.smul_apply, Complex.real_smul]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      horizontal_product, hj]
  · simp [pullTensor, hs a b c d hj]

theorem pull_horizontal_matrix (r : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ) :
    pullMatrix (horizontalScale r) (block A s) = block ((r ^ 2) • A) s := by
  ext a b
  cases a <;> cases b <;> simp [pullMatrix, horizontalScale, block, Complex.real_smul,
    pow_two, mul_assoc]

theorem horizontal_pull_lift (r : ℝ) (u : Fin 2 → ℂ) (y : ℂ) :
    pullVector (horizontalScale r) (lift u y) = lift ((r : ℂ) • u) y := by
  ext a
  cases a <;> simp [pullVector, horizontalScale, lift]

theorem horizontal_independent {r : ℝ} (hr : r ≠ 0)
    (u v : Fin 2 → ℂ) (y z : ℂ) (hind : LinearIndependent ℝ ![(u,y), (v,z)]) :
    LinearIndependent ℝ ![((r : ℂ) • u,y), ((r : ℂ) • v,z)] := by
  let e : ((Fin 2 → ℂ) × ℂ) ≃ₗ[ℝ] ((Fin 2 → ℂ) × ℂ) :=
    (LinearEquiv.smulOfNeZero ℝ (Fin 2 → ℂ) (r : ℝ) hr).prodCongr (LinearEquiv.refl ℝ ℂ)
  have h := hind.map' e.toLinearMap e.ker
  have heq : (e.toLinearMap ∘ ![(u,y), (v,z)]) =
      ![((r : ℂ) • u,y), ((r : ℂ) • v,z)] := by
    funext i
    fin_cases i <;> simp [e]
  rw [heq] at h
  exact h

end TensorAlgebra
end PinchedHartogs.PlaneAlgebra

namespace PinchedHartogs.PlaneAlgebra
namespace TensorAlgebra
open MatrixAlgebra Matrix
open scoped ComplexOrder

theorem pull_mixedTensor (r : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    pullTensor (horizontalScale r) (mixedTensor A) = mixedTensor ((r ^ 2) • A) := by
  simp only [mixedTensor, pull_sub, pull_S, pull_horizontal_matrix,
    smul_zero]

theorem S_smul (r : ℝ) (A : Matrix Index Index ℂ) :
    S (r • A) = (r ^ 2) • S A := by
  ext a b c d
  simp only [S, Matrix.smul_apply, Complex.real_smul, Pi.smul_apply, Complex.ofReal_pow]
  ring

theorem block_horizontal_smul (r : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    block (r • A) 0 = r • block A 0 := by
  ext a b
  cases a <;> cases b <;> simp [block]

theorem form_pos_iff {n : Type uKahler6341_1} [finiteIndex : Fintype n] [decidableIndex : DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (form A hA).Pos ↔ A.PosDef := by
  constructor
  · intro h
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hA
    intro u hu
    rw [← hermitian_diag_real A hA u]
    have hus : star u ≠ 0 := by simpa using hu
    exact_mod_cast (show 0 < (dotProduct (star u) (A *ᵥ u)).re by simpa using h (star u) hus)
  · intro h u hu
    have hus : star u ≠ 0 := by simpa using hu
    have H := h.dotProduct_mulVec_pos hus
    simpa only [form_q, star_star] using (Complex.pos_iff.mp H).1

private theorem G_posdef {c lam x : ℝ} (hc : 0 < c) (hlam : 0 < lam) (hx : 0 ≤ x)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian)
    (hl : ∀ w, c * euclidean.q w ≤ (form A hA).q w) :
    (horizontalMetric A lam x).PosDef := by
  apply (form_pos_iff _ (horizontalMetric_hermitian A hA lam x)).mp
  intro u hu
  have hp := form_one_pos u hu
  have hAu : 0 ≤ (form A hA).q u := (mul_nonneg hc.le hp.le).trans (hl u)
  simp only [horizontalMetric, form_q, add_mulVec, smul_mulVec, dotProduct_add,
    dotProduct_smul, Complex.add_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change 0 < lam * euclidean.q u + x * (form A hA).q u
  exact add_pos_of_pos_of_nonneg (mul_pos hlam hp) (mul_nonneg hx hAu)

end TensorAlgebra
end PinchedHartogs.PlaneAlgebra

namespace PinchedHartogs.PlaneAlgebra
namespace TensorAlgebra
open MatrixAlgebra Matrix
open scoped ComplexOrder

private theorem inv_real_smul (A : Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ}
    (hr : r ≠ 0) (hA : IsUnit A) : (r • A)⁻¹ = r⁻¹ • A⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [smul_mul_smul_comm, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA)]
  simp [hr]

theorem compactG_eq (A : Matrix (Fin 2) (Fin 2) ℂ) (lam : ℝ) {t : ℝ} (ht : t ≠ 1) :
    compactG A lam t = (1-t) • horizontalMetric A lam (t/(1-t)) := by
  simp only [compactG, horizontalMetric, smul_add, smul_smul]
  rw [show (1-t)*(t/(1-t)) = t by field_simp]

theorem compactD_eq (A : Matrix (Fin 2) (Fin 2) ℂ) (lam : ℝ) {t : ℝ}
    (ht : t ≠ 1) (hG : IsUnit (horizontalMetric A lam (t/(1-t)))) :
    compactD A lam t = (1-t) • mixedMatrix A lam (t/(1-t)) := by
  have hne : 1-t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  rw [compactD, compactG_eq A lam ht, inv_real_smul _ hne hG,
    Matrix.mul_smul, Matrix.smul_mul]
  simp only [mixedMatrix, smul_sub, smul_smul]
  have h1 : (1-t)*(1+2*(t/(1-t))) = 1+t := by field_simp ; ring
  have h2 : t*(1-t)⁻¹ = (1-t)*((t/(1-t))*(1+t/(1-t))) := by field_simp ; ring
  rw [h1, h2]

private theorem pull_model (A : Matrix (Fin 2) (Fin 2) ℂ) (lam t : ℝ)
    (ht : t < 1) (hG : IsUnit (horizontalMetric A lam (t/(1-t))))
    (T4 T3 : Tensor Index) :
    pullTensor (horizontalScale (Real.sqrt (1-t))) (curvatureModel A lam (t/(1-t)) T4 T3) =
      compactCurvature A lam t
        (pullTensor (horizontalScale (Real.sqrt (1-t))) T4)
        (pullTensor (horizontalScale (Real.sqrt (1-t))) T3) := by
  have htne := ne_of_lt ht
  have hne : 1-t ≠ 0 := by linarith
  have hr : Real.sqrt (1-t)^2 = 1-t := Real.sq_sqrt (by linarith)
  have heq : (t/(1-t)) * (1+t/(1-t)) * (1-t)^2 = t := by field_simp ; ring
  change pullTensor _ (((-lam) • S (block 1 0) -
    (t/(1-t) * (1+t/(1-t))) • S (block A 0) - S (block 0 1) -
    mixedTensor (mixedMatrix A lam (t/(1-t)))) + T4 + T3) = _
  simp only [pull_add, pull_sub, pull_smul, pull_S, pull_horizontal_matrix,
    pull_mixedTensor, hr, smul_zero, block_horizontal_smul, S_smul,
    smul_smul, compactCurvature]
  rw [← compactD_eq A lam htne hG, heq]
  congr 3
  ring_nf

theorem componentNorm_smul (r : ℝ) (T : Tensor Index) :
    componentNorm (r • T) = |r| * componentNorm T := by
  simp only [componentNorm, Complex.normSq_eq_norm_sq, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow,
    ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]

private theorem supported_smul (r : ℝ) (T : Tensor Index) {j : ℕ} (hs : Supported T j) :
    Supported (r • T) j := by
  intro a b c d h
  simp [hs a b c d h]

private theorem symmetries_smul (r : ℝ) (T : Tensor Index) (hT : Symmetries T) :
    Symmetries (r • T) := by
  constructor
  · intro a b c d
    simp only [Pi.smul_apply, hT.hol a b c d]
  · intro a b c d
    simp only [Pi.smul_apply, hT.anti a b c d]
  · intro a b c d
    simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.star_def, Complex.conj_ofReal]
    rw [show (starRingEnd ℂ) (T a b c d) = T b a d c from hT.reality a b c d]

end TensorAlgebra
end PinchedHartogs.PlaneAlgebra

namespace PinchedHartogs.PlaneAlgebra
namespace TensorAlgebra
open MatrixAlgebra Matrix
open scoped ComplexOrder

private theorem compact_scalars {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    let r := Real.sqrt (1-t)
    let x := t/(1-t)
    0 < r ∧ 0 ≤ x ∧ r^4*x = t*(1-t) ∧
      r^3 * Real.sqrt (x*(1+x)) = Real.sqrt (t*(1-t)) := by
  dsimp
  have hs : 0 < 1-t := sub_pos.mpr ht1
  have hr := Real.sqrt_pos.mpr hs
  have hr2 := Real.sq_sqrt hs.le
  have hx : 0 ≤ t/(1-t) := div_nonneg ht0 hs.le
  have hq : 0 ≤ (t/(1-t))*(1+t/(1-t)) := by positivity
  have htx : (t/(1-t))*(1+t/(1-t))*(1-t)^2 = t := by field_simp ; ring
  refine ⟨hr, hx, ?_, ?_⟩
  · calc
      Real.sqrt (1-t)^4 * (t/(1-t)) = (1-t)^2 * (t/(1-t)) := by rw [show Real.sqrt (1-t)^4 = (Real.sqrt (1-t)^2)^2 by ring, hr2]
      _ = t*(1-t) := by field_simp
  · apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt hq, Real.sq_sqrt (mul_nonneg ht0 hs.le)]
    have hr6 : (Real.sqrt (1-t)^3)^2 = (1-t)^3 := by
      rw [show (Real.sqrt (1-t)^3)^2 = (Real.sqrt (1-t)^2)^3 by ring, hr2]
    rw [hr6]
    calc
      (1-t)^3 * (t/(1-t)*(1+t/(1-t))) =
        (t/(1-t)*(1+t/(1-t))*(1-t)^2)*(1-t) := by ring
      _ = _ := by rw [htx]

private theorem componentNorm_eq_zero {T : Tensor Index} (h : componentNorm T = 0) : T = 0 := by
  ext a b c d
  apply norm_eq_zero.mp
  exact le_antisymm (h ▸ norm_component_le T a b c d) (norm_nonneg _)

private theorem independent_lift (u v : Fin 2 → ℂ) (y z : ℂ)
    (hind : LinearIndependent ℝ ![(u,y), (v,z)]) :
    LinearIndependent ℝ ![lift u y, lift v z] := by
  let e := liftEquiv.restrictScalars ℝ
  have h := hind.map' e.toLinearMap e.ker
  have heq : (e.toLinearMap ∘ ![(u,y), (v,z)]) = ![lift u y, lift v z] := by
    funext i
    fin_cases i <;> rfl
  rw [heq] at h
  exact h

private theorem block_pos (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian)
    (hp : (form A hA).Pos) : (form (block A 1) (block_hermitian (n := Fin 2) A hA 1)).Pos := by
  intro w hw
  let u : Fin 2 → ℂ := fun i ↦ w (some i)
  have heq : w = lift u (w none) := by ext a; cases a <;> rfl
  rw [heq, HForm.q, block_pair A hA]
  change 0 < ((form A hA u u) + (1 : ℂ) * w none * star (w none)).re
  simpa only [HForm.withVertical_q, HForm.q, one_mul, Complex.add_re, Complex.mul_conj, Complex.star_def,
    Complex.ofReal_re, HForm.withVertical] using (form A hA).withVertical_pos hp (u,w none)
      (by
        intro h
        apply hw
        ext a
        cases a with
        | none => exact congrArg Prod.snd h
        | some i => exact congrFun (congrArg Prod.fst h) i)

theorem compactCurvature_negative {c C Ce lam t : ℝ}
    (hc : 0 < c) (hC : c ≤ C) (hCe : 0 ≤ Ce) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hlam : pinchingThreshold c C (162 * Ce) ≤ lam)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian)
    (hl : ∀ w, c * euclidean.q w ≤ (form A hA).q w)
    (hu : ∀ w, (form A hA).q w ≤ C * euclidean.q w)
    (E4 E3 : Tensor Index) (hT4 : Symmetries E4) (hT3 : Symmetries E3)
    (hs4 : Supported E4 4) (hs3 : Supported E3 3)
    (hn4 : componentNorm E4 ≤ Ce * (t*(1-t)))
    (hn3 : componentNorm E3 ≤ Ce * Real.sqrt (t*(1-t)))
    (u v : Fin 2 → ℂ) (y z : ℂ)
    (hind : LinearIndependent ℝ ![(u,y), (v,z)]) :
    H (compactCurvature A lam t E4 E3) (lift u y) (lift v z) < 0 := by
  have hlam0 : 0 < lam := (threshold_positive hc hC).trans_le hlam
  have hAp : (form A hA).Pos := fun w hw ↦ (mul_pos hc (form_one_pos w hw)).trans_le (hl w)
  rcases lt_or_eq_of_le ht1 with ht | rfl
  · let r := Real.sqrt (1-t)
    let x := t/(1-t)
    obtain ⟨hr, hx, hr4, hr3⟩ := compact_scalars ht0 ht
    change 0 < r at hr
    change 0 ≤ x at hx
    change r^4*x = t*(1-t) at hr4
    change r^3*Real.sqrt (x*(1+x)) = Real.sqrt (t*(1-t)) at hr3
    let T4 := (r⁻¹^4) • E4
    let T3 := (r⁻¹^3) • E3
    have hp4 : pullTensor (horizontalScale r) T4 = E4 := by
      rw [pull_supported _ _ (supported_smul _ _ hs4)]
      rw [smul_smul]
      simp [hr.ne']
    have hp3 : pullTensor (horizontalScale r) T3 = E3 := by
      rw [pull_supported _ _ (supported_smul _ _ hs3)]
      rw [smul_smul]
      simp [hr.ne']
    have hnorm4 : componentNorm T4 ≤ Ce*x := by
      change componentNorm ((r⁻¹^4) • E4) ≤ _
      rw [componentNorm_smul, abs_of_nonneg (by positivity)]
      calc
        _ ≤ r⁻¹^4 * (Ce*(t*(1-t))) := mul_le_mul_of_nonneg_left hn4 (by positivity)
        _ = Ce*x := by rw [← hr4]; field_simp
    have hnorm3 : componentNorm T3 ≤ Ce*Real.sqrt (x*(1+x)) := by
      change componentNorm ((r⁻¹^3) • E3) ≤ _
      rw [componentNorm_smul, abs_of_nonneg (by positivity)]
      calc
        _ ≤ r⁻¹^3 * (Ce*Real.sqrt (t*(1-t))) := mul_le_mul_of_nonneg_left hn3 (by positivity)
        _ = _ := by rw [← hr3]; field_simp
    have hi := horizontal_independent hr.ne' u v y z hind
    have hneg := curvatureModel_negative hc hC hCe hx hlam A hA hl hu T4 T3
      (symmetries_smul _ _ hT4) (symmetries_smul _ _ hT3)
      (supported_smul _ _ hs4) (supported_smul _ _ hs3) hnorm4 hnorm3
      ((r : ℂ) • u) ((r : ℂ) • v) y z hi
    have heq := pull_model A lam t ht (G_posdef hc hlam0 hx A hA hl).isUnit T4 T3
    change pullTensor (horizontalScale r) (curvatureModel A lam x T4 T3) = _ at heq
    rw [hp4, hp3] at heq
    rw [← heq, H_pull, horizontal_pull_lift, horizontal_pull_lift]
    exact hneg
  · have hz4 : E4 = 0 := componentNorm_eq_zero (le_antisymm (by simpa using hn4) (Real.sqrt_nonneg _))
    have hz3 : E3 = 0 := componentNorm_eq_zero (le_antisymm (by simpa using hn3) (Real.sqrt_nonneg _))
    have hunit := (form_pos_iff A hA).mp hAp |>.isUnit
    have hD : compactD A lam 1 = A := by
      simp only [compactD, compactG, sub_self, zero_mul, zero_smul, one_smul, zero_add]
      rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit), one_mul]
      module
    have heq : compactCurvature A lam 1 E4 E3 = (-1 : ℝ) • S (block A 1) := by
      rw [hz4, hz3]
      simp only [compactCurvature, hD, mixedTensor, sub_self, zero_pow (by norm_num : 2 ≠ 0),
        mul_zero, neg_zero, zero_smul, one_smul, zero_sub, add_zero]
      module
    rw [heq, H_smul, H_S _ (block_hermitian (n := Fin 2) A hA 1)]
    have hp := (form (block A 1) (block_hermitian (n := Fin 2) A hA 1)).area_pos _ _ (block_pos A hA hAp)
      (independent_lift u v y z hind)
    linarith only [hp, sq_nonneg ((form (block A 1) (block_hermitian (n := Fin 2) A hA 1)).imag (lift u y) (lift v z))]

end TensorAlgebra
end PinchedHartogs.PlaneAlgebra

namespace PinchedHartogs.PlaneAlgebra
namespace TensorAlgebra
open MatrixAlgebra Matrix
open scoped ComplexOrder

open scoped Matrix.Norms.Elementwise

private theorem isClosed_setOf_forall {X : Type uKahler6602_1} {ι : Type uKahler6602_2} [TopologicalSpace X]
    {p : X → ι → Prop} (h : ∀ i, IsClosed {x | p x i}) : IsClosed {x | ∀ i, p x i} := by
  simpa only [Set.ofPred_forall] using isClosed_iInter h

private theorem continuous_pairValue {n : Type uKahler6615_1} [finiteIndex : Fintype n] :
    Continuous (fun p : Matrix n n ℂ × (n → ℂ) × (n → ℂ) ↦ pairValue p.1 p.2.1 p.2.2) := by
  unfold pairValue dotProduct Matrix.mulVec
  fun_prop

private theorem continuous_qValue {n : Type uKahler6620_1} [finiteIndex : Fintype n] :
    Continuous (fun p : Matrix n n ℂ × (n → ℂ) ↦ qValue p.1 p.2) := by
  unfold qValue pairValue dotProduct Matrix.mulVec
  fun_prop

private theorem matrix_entry_bound {C : ℝ} (hC : 0 ≤ C) (A : BaseMatrix) (hA : A.IsHermitian)
    (hn : (form A hA).Nonneg) (hu : ∀ w, (form A hA).q w ≤ C * euclidean.q w) :
    ∀ i j, ‖A i j‖ ≤ C := by
  intro i j
  let u : Fin 2 → ℂ := Pi.single i 1
  let v : Fin 2 → ℂ := Pi.single j 1
  have huq : euclidean.q u = 1 := by simp [u]
  have hvq : euclidean.q v = 1 := by simp [v]
  have huv : form A hA u v = A i j := by
    fin_cases i <;> fin_cases j <;> simp [form, dotProduct, Matrix.mulVec, u, v]
  have hi := hu u
  have hj := hu v
  rw [huq, mul_one] at hi
  rw [hvq, mul_one] at hj
  have hm := mul_le_mul hi hj (hn v) hC
  have hg := (form A hA).gram u v hn
  have hnorm : ‖A i j‖^2 ≤ C^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [HForm.imag, HForm.area, huv] at hg
    linarith only [hg, hm]
  exact (sq_le_sq₀ (norm_nonneg _) hC).mp hnorm

private theorem matrixSet_closed (c C : ℝ) : IsClosed (matrixSet c C) := by
  apply IsClosed.inter
  · exact isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  · apply isClosed_setOf_forall
    intro w
    exact (isClosed_le continuous_const
      (continuous_qValue.comp (continuous_id.prodMk continuous_const))).inter
      (isClosed_le (continuous_qValue.comp (continuous_id.prodMk continuous_const)) continuous_const)

private theorem matrixSet_compact {c C : ℝ} (hc : 0 < c) (hC : c ≤ C) :
    IsCompact (matrixSet c C) := by
  have hCp : 0 < C := hc.trans_le hC
  apply (isCompact_closedBall (0 : BaseMatrix) C).of_isClosed_subset (matrixSet_closed c C)
  intro A hA
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg hCp.le).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hCp.le).mpr
  intro j
  apply matrix_entry_bound hCp.le A hA.1 _ _ i j
  · intro w
    exact (mul_nonneg hc.le (euclidean.nonneg_of_pos form_one_pos w)).trans (hA.2 w).1
  · exact fun w ↦ (hA.2 w).2

private theorem pairSet_closed : IsClosed pairSet := by
  refine (isClosed_eq ?_ continuous_const).inter ((isClosed_eq ?_ continuous_const).inter
    (isClosed_eq ?_ continuous_const))
  all_goals simp only [qValue, pairValue, dotProduct, Matrix.mulVec]; fun_prop

private theorem qValue_one (u : FullVector) : qValue 1 u = ∑ i, Complex.normSq (u i) := by
  exact form_one_q u

private theorem norm_le_of_q_one (u : FullVector) (hu : qValue 1 u = 1) : ‖u‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro i
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset Index)) ↦
    Complex.normSq_nonneg (u j)) (Finset.mem_univ i)
  change Complex.normSq (u i) ≤ ∑ j, Complex.normSq (u j) at h
  rw [← qValue_one, hu, Complex.normSq_eq_norm_sq] at h
  nlinarith only [h, norm_nonneg (u i)]

private theorem pairSet_compact : IsCompact pairSet := by
  apply (isCompact_closedBall (0 : FullVector × FullVector) 1).of_isClosed_subset pairSet_closed
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
  exact ⟨norm_le_of_q_one p.1 hp.1, norm_le_of_q_one p.2 hp.2.1⟩

private theorem independent_pairSet (p : FullVector × FullVector) (hp : p ∈ pairSet) :
    LinearIndependent ℝ ![p.1, p.2] := by
  apply linearIndependent_fin2.mpr
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  refine ⟨?_, ?_⟩
  · intro h
    have := hp.2.1
    simp [h, qValue, pairValue] at this
  · intro a h
    have h0 := hp.2.2
    rw [← h] at h0
    change ((form 1 Matrix.isHermitian_one) (a • p.2) p.2).re = 0 at h0
    rw [← IsScalarTower.algebraMap_smul ℂ a p.2, HForm.map_smul_left] at h0
    change (((a : ℂ) * (form 1 Matrix.isHermitian_one) p.2 p.2).re) = 0 at h0
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h0
    change a * qValue 1 p.2 = 0 at h0
    rw [hp.2.1, mul_one] at h0
    subst a
    simp only [zero_smul] at h
    have h1 := hp.1
    rw [← h] at h1
    simp [qValue, pairValue] at h1

end TensorAlgebra
end PinchedHartogs.PlaneAlgebra

namespace PinchedHartogs.PlaneAlgebra
namespace TensorAlgebra
open MatrixAlgebra Matrix
open scoped ComplexOrder

open scoped Matrix.Norms.Elementwise

private theorem continuous_componentNorm : Continuous (componentNorm (n := Index)) := by
  unfold componentNorm
  fun_prop

private theorem norm_le_componentNorm (T : Tensor Index) : ‖T‖ ≤ componentNorm T := by
  have hn := Real.sqrt_nonneg (∑ t : Quad Index, Complex.normSq (T t.1 t.2.1 t.2.2.1 t.2.2.2))
  apply (pi_norm_le_iff_of_nonneg hn).mpr
  intro a
  apply (pi_norm_le_iff_of_nonneg hn).mpr
  intro b
  apply (pi_norm_le_iff_of_nonneg hn).mpr
  intro c
  apply (pi_norm_le_iff_of_nonneg hn).mpr
  intro d
  exact norm_component_le T a b c d

private theorem symmetries_iff (T : Tensor Index) : Symmetries T ↔
    (∀ a b c d, T a b c d = T c b a d) ∧
    (∀ a b c d, T a b c d = T a d c b) ∧
    (∀ a b c d, star (T a b c d) = T b a d c) :=
  ⟨fun h ↦ ⟨h.hol, h.anti, h.reality⟩, fun h ↦ ⟨h.1, h.2.1, h.2.2⟩⟩

private theorem symmetries_closed : IsClosed {T : Tensor Index | Symmetries T} := by
  simp only [symmetries_iff, Set.ofPred_and]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
  all_goals
    apply isClosed_setOf_forall
    intro a
    apply isClosed_setOf_forall
    intro b
    apply isClosed_setOf_forall
    intro c
    apply isClosed_setOf_forall
    intro d
    apply isClosed_eq <;> fun_prop

private theorem supported_closed (j : ℕ) : IsClosed {T : Tensor Index | Supported T j} := by
  unfold Supported
  apply isClosed_setOf_forall
  intro a
  apply isClosed_setOf_forall
  intro b
  apply isClosed_setOf_forall
  intro c
  apply isClosed_setOf_forall
  intro d
  by_cases h : horizontalCount a b c d = j
  · simp [h]
  · simpa [h] using (isClosed_eq (f := fun T : Tensor Index ↦ T a b c d)
      (g := fun _ ↦ (0 : ℂ)) (by fun_prop) continuous_const)

attribute [local instance] OAI.PinchedHartogs.PlaneAlgebra.TensorAlgebra.tensorTopology
attribute [local instance] OAI.PinchedHartogs.PlaneAlgebra.TensorAlgebra.matrixTopology
attribute [local instance] OAI.PinchedHartogs.PlaneAlgebra.TensorAlgebra.pairTopology
private theorem dataSet_closed (c C Ce : ℝ) : IsClosed (dataSet c C Ce) := by
  unfold dataSet
  simp only [Set.ofPred_and]
  refine IsClosed.inter (isClosed_Icc.preimage continuous_fst) (IsClosed.inter
    ((matrixSet_closed c C).preimage (by fun_prop)) (IsClosed.inter
    (symmetries_closed.preimage (by fun_prop)) (IsClosed.inter
    ((supported_closed 4).preimage (by fun_prop)) (IsClosed.inter
    (symmetries_closed.preimage (by fun_prop)) (IsClosed.inter
    ((supported_closed 3).preimage (by fun_prop)) (IsClosed.inter ?_ (IsClosed.inter ?_
    (pairSet_closed.preimage (by fun_prop)))))))))
  · exact isClosed_le (continuous_componentNorm.comp (by fun_prop)) (by fun_prop)
  · exact isClosed_le (continuous_componentNorm.comp (by fun_prop)) (by fun_prop)

private theorem dataSet_compact {c C Ce : ℝ} (hc : 0 < c) (hC : c ≤ C) (hCe : 0 ≤ Ce) :
    IsCompact (dataSet c C Ce) := by
  let box : Set CompactData := Set.Icc 0 1 ×ˢ matrixSet c C ×ˢ
    Metric.closedBall 0 Ce ×ˢ Metric.closedBall 0 Ce ×ˢ pairSet
  have hb : IsCompact box := isCompact_Icc.prod ((matrixSet_compact hc hC).prod
    ((isCompact_closedBall 0 Ce).prod ((isCompact_closedBall 0 Ce).prod pairSet_compact)))
  apply hb.of_isClosed_subset (dataSet_closed c C Ce)
  intro d hd
  have ht0 := hd.1.1
  have ht1 := hd.1.2
  have hq0 : 0 ≤ d.1*(1-d.1) := mul_nonneg ht0 (sub_nonneg.mpr ht1)
  have hq1 : d.1*(1-d.1) ≤ 1 := by linarith only [sq_nonneg (d.1-1/2)]
  have hs : Real.sqrt (d.1*(1-d.1)) ≤ 1 := (Real.sqrt_le_one).mpr hq1
  refine ⟨hd.1, hd.2.1, ?_, ?_, hd.2.2.2.2.2.2.2.2⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_componentNorm _).trans (hd.2.2.2.2.2.2.1.trans
      (by simpa using mul_le_mul_of_nonneg_left hq1 hCe))
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_componentNorm _).trans (hd.2.2.2.2.2.2.2.1.trans
      (by simpa using mul_le_mul_of_nonneg_left hs hCe))

private theorem compactG_pos {c lam t : ℝ} (hc : 0 < c) (hlam : 0 < lam)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (A : BaseMatrix) (hA : A.IsHermitian)
    (hl : ∀ w, c * euclidean.q w ≤ (form A hA).q w) :
    (form (compactG A lam t) (compactG_hermitian A hA lam t)).Pos := by
  intro w hw
  have hq := form_one_pos w hw
  have hcoeff : 0 < (1-t)*lam+t*c := by
    have hm : 0 < min lam c := lt_min hlam hc
    have h1 := mul_le_mul_of_nonneg_left (min_le_left lam c) (sub_nonneg.mpr ht1)
    have h2 := mul_le_mul_of_nonneg_left (min_le_right lam c) ht0
    linarith only [h1, h2, hm]
  have hAl := mul_le_mul_of_nonneg_left (hl w) ht0
  have hstrict := mul_pos hcoeff hq
  simp only [compactG, form_q, add_mulVec, smul_mulVec, dotProduct_add,
    dotProduct_smul, Complex.add_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change 0 < (1-t)*lam*euclidean.q w+t*(form A hA).q w
  linarith only [hAl, hstrict]

end TensorAlgebra
end PinchedHartogs.PlaneAlgebra

namespace PinchedHartogs.PlaneAlgebra
namespace TensorAlgebra
open MatrixAlgebra Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] OAI.PinchedHartogs.PlaneAlgebra.TensorAlgebra.tensorTopology'
attribute [local instance] OAI.PinchedHartogs.PlaneAlgebra.TensorAlgebra.matrixTopology'
attribute [local instance] OAI.PinchedHartogs.PlaneAlgebra.TensorAlgebra.pairTopology'
attribute [local instance] OAI.PinchedHartogs.PlaneAlgebra.TensorAlgebra.compactDataTopology
private theorem continuous_block : Continuous (fun p : BaseMatrix × ℝ ↦ block p.1 p.2) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  cases a <;> cases b <;> simp only [block] <;> fun_prop

private theorem continuous_S : Continuous (S (n := Index)) := by
  unfold S
  fun_prop

private theorem continuous_mixedTensor : Continuous mixedTensor := by
  unfold mixedTensor
  exact ((continuous_S.comp (continuous_block.comp (continuous_id.prodMk continuous_const))).sub
    (continuous_S.comp (continuous_block.comp (continuous_id.prodMk continuous_const)))).sub continuous_const

private theorem continuous_H : Continuous (fun p : Tensor Index × FullVector × FullVector ↦
    H p.1 p.2.1 p.2.2) := by
  unfold H eval
  fun_prop

private theorem continuousAt_matrix_inverse (A : BaseMatrix) (hA : IsUnit A) :
    ContinuousAt (fun B : BaseMatrix ↦ B⁻¹) A := by
  apply continuousAt_matrix_inv
  have heq : (Ring.inverse : ℂ → ℂ) = Inv.inv := funext Ring.inverse_eq_inv
  rw [heq]
  exact continuousAt_inv₀ ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero

private theorem continuous_compactG (lam : ℝ) :
    Continuous (fun p : BaseMatrix × ℝ ↦ compactG p.1 lam p.2) := by
  unfold compactG
  fun_prop

private theorem continuousAt_compactD (lam : ℝ) (p : BaseMatrix × ℝ)
    (hK : IsUnit (compactG p.1 lam p.2)) :
    ContinuousAt (fun q : BaseMatrix × ℝ ↦ compactD q.1 lam q.2) p := by
  have hInv : ContinuousAt (fun q : BaseMatrix × ℝ ↦ (compactG q.1 lam q.2)⁻¹) p :=
    (continuousAt_matrix_inverse _ hK).comp
      (f := fun q : BaseMatrix × ℝ ↦ compactG q.1 lam q.2) (x := p)
      (continuous_compactG lam).continuousAt
  have hMul : Continuous (fun q : BaseMatrix × BaseMatrix ↦ q.1 * q.2) :=
    continuous_fst.matrix_mul continuous_snd
  have hL : ContinuousAt (fun q : BaseMatrix × ℝ ↦ q.1 * (compactG q.1 lam q.2)⁻¹) p :=
    hMul.continuousAt.comp (f := fun q : BaseMatrix × ℝ ↦ (q.1, (compactG q.1 lam q.2)⁻¹))
      (x := p) (continuous_fst.continuousAt.prodMk hInv)
  have hR : ContinuousAt (fun q : BaseMatrix × ℝ ↦ q.1 * (compactG q.1 lam q.2)⁻¹ * q.1) p :=
    hMul.continuousAt.comp
      (f := fun q : BaseMatrix × ℝ ↦ (q.1 * (compactG q.1 lam q.2)⁻¹, q.1))
      (x := p) (hL.prodMk continuous_fst.continuousAt)
  unfold compactD
  exact ((continuous_const.add continuous_snd).smul continuous_fst).continuousAt.sub
    (continuous_snd.continuousAt.smul hR)

private theorem continuousAt_compactCurvature (lam : ℝ) (d : CompactData)
    (hK : IsUnit (compactG d.2.1 lam d.1)) :
    ContinuousAt (fun e : CompactData ↦ compactCurvature e.2.1 lam e.1 e.2.2.1 e.2.2.2.1) d := by
  have hp : Continuous (fun e : CompactData ↦ (e.2.1,e.1)) := by fun_prop
  have hD : ContinuousAt (fun e : CompactData ↦ compactD e.2.1 lam e.1) d :=
    (continuousAt_compactD lam (d.2.1,d.1) hK).comp
      (f := fun e : CompactData ↦ (e.2.1,e.1)) (x := d) hp.continuousAt
  have hmix : ContinuousAt (fun e : CompactData ↦ mixedTensor (compactD e.2.1 lam e.1)) d :=
    continuous_mixedTensor.continuousAt.comp hD
  have hS : Continuous (fun e : CompactData ↦ S (block e.2.1 0)) :=
    continuous_S.comp (continuous_block.comp
      (show Continuous (fun e : CompactData ↦ (e.2.1, (0:ℝ))) from by fun_prop))
  unfold compactCurvature
  exact (((((show Continuous (fun e : CompactData ↦
    (-(lam*(1-e.1)^2)) • S (block 1 0)) from by fun_prop).sub
      (continuous_fst.smul hS)).sub continuous_const).continuousAt.sub hmix).add
      (by fun_prop)).add (by fun_prop)

private theorem continuous_metricArea : Continuous
    (fun p : BaseMatrix × FullVector × FullVector ↦ metricArea p.1 p.2.1 p.2.2) := by
  have hB : Continuous (fun p : BaseMatrix × FullVector × FullVector ↦ block p.1 1) :=
    continuous_block.comp
      (show Continuous (fun p : BaseMatrix × FullVector × FullVector ↦ (p.1, (1:ℝ)))
        from by fun_prop)
  unfold metricArea
  exact ((continuous_qValue.comp (hB.prodMk continuous_snd.fst)).mul
    (continuous_qValue.comp (hB.prodMk continuous_snd.snd))).sub
    ((Complex.continuous_re.comp (continuous_pairValue.comp (hB.prodMk continuous_snd))).pow 2)

private theorem metricArea_pos {c lam : ℝ} (hc : 0 < c) (hlam : 0 < lam)
    {C Ce : ℝ} (d : CompactData) (hd : d ∈ dataSet c C Ce) :
    0 < metricArea (compactG d.2.1 lam d.1) d.2.2.2.2.1 d.2.2.2.2.2 := by
  let hK := compactG_hermitian d.2.1 hd.2.1.1 lam d.1
  change 0 < (form (block (compactG d.2.1 lam d.1) 1)
    (block_hermitian (n := Fin 2) _ hK 1)).area d.2.2.2.2.1 d.2.2.2.2.2
  apply HForm.area_pos
  · exact block_pos _ hK (compactG_pos hc hlam hd.1.1 hd.1.2 _ hd.2.1.1 (fun w ↦ (hd.2.1.2 w).1))
  · exact independent_pairSet _ hd.2.2.2.2.2.2.2.2

private theorem compactQuotient_negative {c C Ce lam : ℝ} (hc : 0 < c) (hC : c ≤ C)
    (hCe : 0 ≤ Ce) (hlam : pinchingThreshold c C (162*Ce) ≤ lam)
    (d : CompactData) (hd : d ∈ dataSet c C Ce) : compactQuotient lam d < 0 := by
  have hlam0 := (threshold_positive hc hC).trans_le hlam
  have hind := independent_pairSet _ hd.2.2.2.2.2.2.2.2
  let u : Fin 2 → ℂ := fun i ↦ d.2.2.2.2.1 (some i)
  let v : Fin 2 → ℂ := fun i ↦ d.2.2.2.2.2 (some i)
  let y := d.2.2.2.2.1 none
  let z := d.2.2.2.2.2 none
  have hu : d.2.2.2.2.1 = lift u y := by ext a; cases a <;> rfl
  have hv : d.2.2.2.2.2 = lift v z := by ext a; cases a <;> rfl
  have hi : LinearIndependent ℝ ![(u,y), (v,z)] := by
    let e := liftEquiv.symm.restrictScalars ℝ
    have hi := hind.map' e.toLinearMap e.ker
    have heq : (e.toLinearMap ∘ ![d.2.2.2.2.1,d.2.2.2.2.2]) = ![(u,y),(v,z)] := by
      funext i
      fin_cases i <;> rfl
    rwa [heq] at hi
  have hn := compactCurvature_negative hc hC hCe hd.1.1 hd.1.2 hlam d.2.1 hd.2.1.1
    (fun w ↦ (hd.2.1.2 w).1) (fun w ↦ (hd.2.1.2 w).2)
    d.2.2.1 d.2.2.2.1 hd.2.2.1 hd.2.2.2.2.1 hd.2.2.2.1 hd.2.2.2.2.2.1
    hd.2.2.2.2.2.2.1 hd.2.2.2.2.2.2.2.1 u v y z hi
  unfold compactQuotient
  apply div_neg_of_neg_of_pos
  · simpa only [← hu, ← hv] using hn
  · exact mul_pos (by norm_num) (metricArea_pos hc hlam0 d hd)

private theorem compactMetric_continuous (lam : ℝ) :
    Continuous (fun e : CompactData ↦ compactG e.2.1 lam e.1) :=
  (continuous_compactG lam).comp
    (show Continuous (fun e : CompactData ↦ (e.2.1,e.1)) from by fun_prop)

private theorem compactArea_continuous (lam : ℝ) :
    Continuous (fun e : CompactData ↦
      metricArea (compactG e.2.1 lam e.1) e.2.2.2.2.1 e.2.2.2.2.2) :=
  continuous_metricArea.comp (f := fun e : CompactData ↦
    (compactG e.2.1 lam e.1, e.2.2.2.2))
    ((compactMetric_continuous lam).prodMk continuous_snd.snd.snd.snd)

private theorem compactNumerator_continuousAt (lam : ℝ) (d : CompactData)
    (hunit : IsUnit (compactG d.2.1 lam d.1)) :
    ContinuousAt (fun e : CompactData ↦
      H (compactCurvature e.2.1 lam e.1 e.2.2.1 e.2.2.2.1) e.2.2.2.2.1 e.2.2.2.2.2) d := by
  have hR := continuousAt_compactCurvature lam d hunit
  exact continuous_H.continuousAt.comp
    (f := fun e : CompactData ↦
      (compactCurvature e.2.1 lam e.1 e.2.2.1 e.2.2.2.1,e.2.2.2.2)) (x := d)
    (hR.prodMk (show ContinuousAt (fun e : CompactData ↦ e.2.2.2.2) d from by fun_prop))

private theorem compactQuotient_continuous {c C Ce lam : ℝ} (hc : 0 < c) (hlam : 0 < lam) :
    ContinuousOn (compactQuotient lam) (dataSet c C Ce) := by
  intro d hd
  have hp := compactG_pos hc hlam hd.1.1 hd.1.2 _ hd.2.1.1 (fun w ↦ (hd.2.1.2 w).1)
  have hunit := (form_pos_iff _ (compactG_hermitian _ hd.2.1.1 lam d.1)).mp hp |>.isUnit
  have hN := compactNumerator_continuousAt lam d hunit
  exact (hN.div ((continuous_const.mul (compactArea_continuous lam)).continuousAt)
    (ne_of_gt (mul_pos (by norm_num) (metricArea_pos hc hlam d hd)))).continuousWithinAt

theorem compact_uniform_pinching {c C Ce lam : ℝ} (hc : 0 < c) (hC : c ≤ C) (hCe : 0 ≤ Ce)
    (hlam : pinchingThreshold c C (162*Ce) ≤ lam) :
    ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧ ∀ d ∈ dataSet c C Ce,
      -B ≤ compactQuotient lam d ∧ compactQuotient lam d ≤ -A := by
  by_cases hn : (dataSet c C Ce).Nonempty
  · have hs := dataSet_compact hc hC hCe
    have hcont := compactQuotient_continuous (C := C) (Ce := Ce) hc
      ((threshold_positive hc hC).trans_le hlam)
    obtain ⟨p,hp,hmin⟩ := hs.exists_isMinOn hn hcont
    obtain ⟨q,hq,hmax⟩ := hs.exists_isMaxOn hn hcont
    have hneg := compactQuotient_negative hc hC hCe hlam q hq
    refine ⟨-compactQuotient lam q, -compactQuotient lam p, by linarith, ?_, ?_⟩
    · exact neg_le_neg (hmin hq)
    · intro d hd
      simpa only [neg_neg, Set.mem_ofPred_eq] using And.intro (hmin hd) (hmax hd)
  · exact ⟨1,1,by norm_num,le_refl _,fun d hd ↦ False.elim (hn ⟨d,hd⟩)⟩

end TensorAlgebra
end PinchedHartogs.PlaneAlgebra

namespace PinchedHartogs.PlaneAlgebra

namespace HForm
variable {V : Type uKahler7053_1} [AddCommGroup V] [Module ℂ V]

theorem real_pair_shear_scale (h : HForm V) (u v : V) (a r s : ℝ) :
    (h ((r : ℂ) • u) ((s : ℂ) • (v - (a : ℂ) • u))).re =
      r*s*((h u v).re-a*h.q u) := by
  simp only [map_smul_left, map_smul_right, map_sub_right, Complex.star_def,
    Complex.conj_ofReal, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, HForm.q]
  ring

theorem area_shear_scale (h : HForm V) (u v : V) (a r s : ℝ) :
    h.area ((r : ℂ) • u) ((s : ℂ) • (v - (a : ℂ) • u)) =
      (r*s)^2 * h.area u v := by
  rw [area, q_real_smul, q_real_smul, q_shear, real_pair_shear_scale, area]
  ring

end HForm

namespace TensorAlgebra
open MatrixAlgebra Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise

private theorem S_symmetries (A : Matrix Index Index ℂ) (hA : A.IsHermitian) : Symmetries (S A) := by
  constructor
  · intro a b c d
    simp only [S]
    ring
  · intro a b c d
    simp only [S]
    ring
  · intro a b c d
    simp only [S, star_add, star_mul]
    rw [show star (A a b) = A b a from hA.apply b a,
      show star (A c d) = A d c from hA.apply d c,
      show star (A a d) = A d a from hA.apply d a,
      show star (A c b) = A b c from hA.apply b c]
    ring

private theorem symmetries_add (T Q : Tensor Index) (hT : Symmetries T) (hQ : Symmetries Q) :
    Symmetries (T+Q) := by
  constructor
  · intro a b c d; simp only [Pi.add_apply, hT.hol a b c d, hQ.hol a b c d]
  · intro a b c d; simp only [Pi.add_apply, hT.anti a b c d, hQ.anti a b c d]
  · intro a b c d; simp only [Pi.add_apply, star_add, hT.reality a b c d, hQ.reality a b c d]

private theorem symmetries_sub (T Q : Tensor Index) (hT : Symmetries T) (hQ : Symmetries Q) :
    Symmetries (T-Q) := by
  constructor
  · intro a b c d; simp only [Pi.sub_apply, hT.hol a b c d, hQ.hol a b c d]
  · intro a b c d; simp only [Pi.sub_apply, hT.anti a b c d, hQ.anti a b c d]
  · intro a b c d; simp only [Pi.sub_apply, star_sub, hT.reality a b c d, hQ.reality a b c d]

private theorem mixed_symmetries (A : BaseMatrix) (hA : A.IsHermitian) : Symmetries (mixedTensor A) :=
  symmetries_sub _ _ (symmetries_sub _ _ (S_symmetries _ (block_hermitian (n := Fin 2) A hA 1))
    (S_symmetries _ (block_hermitian (n := Fin 2) A hA 0))) (S_symmetries _ (block_hermitian (n := Fin 2) 0 Matrix.isHermitian_zero 1))

private theorem compactD_hermitian (A : BaseMatrix) (hA : A.IsHermitian) (lam t : ℝ) :
    (compactD A lam t).IsHermitian := by
  have H := Matrix.isHermitian_conjTranspose_mul_mul A (compactG_hermitian A hA lam t).inv
  rw [hA.eq] at H
  exact (hA.smul (by rfl)).sub (H.smul (by rfl))

private theorem compactCurvature_symmetries (A : BaseMatrix) (hA : A.IsHermitian)
    (lam t : ℝ) (E4 E3 : Tensor Index) (h4 : Symmetries E4) (h3 : Symmetries E3) :
    Symmetries (compactCurvature A lam t E4 E3) := by
  unfold compactCurvature
  apply symmetries_add _ _ _ h3
  apply symmetries_add _ _ _ h4
  apply symmetries_sub _ _ _ (mixed_symmetries _ (compactD_hermitian A hA lam t))
  apply symmetries_sub _ _ _ (S_symmetries _ (block_hermitian (n := Fin 2) 0 Matrix.isHermitian_zero 1))
  apply symmetries_sub
  · exact symmetries_smul _ _ (S_symmetries _ (block_hermitian (n := Fin 2) 1 Matrix.isHermitian_one 0))
  · exact symmetries_smul _ _ (S_symmetries _ (block_hermitian (n := Fin 2) A hA 0))

private theorem Xi_shear_scale (u v : FullVector) (a r s : ℝ) (i j : Index) :
    Xi ((r : ℂ) • u) ((s : ℂ) • (v-(a : ℂ) • u)) i j =
      ((r*s : ℝ) : ℂ) * Xi u v i j := by
  simp only [Xi, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, map_mul, map_sub,
    Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
  ring

private theorem H_shear_scale (T : Tensor Index) (hT : Symmetries T)
    (u v : FullVector) (a r s : ℝ) :
    H T ((r : ℂ) • u) ((s : ℂ) • (v-(a : ℂ) • u)) = (r*s)^2*H T u v := by
  rw [H_xi T hT, H_xi T hT]
  have heq : xiContract T ((r : ℂ) • u) ((s : ℂ) • (v-(a : ℂ) • u)) =
      (((r*s)^2 : ℝ) : ℂ) * xiContract T u v := by
    simp only [xiContract, Xi_shear_scale, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    simp only [Complex.ofReal_pow]
    ring
  rw [heq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

private theorem normalization (u v : FullVector) (hind : LinearIndependent ℝ ![u,v]) :
    ∃ a r s : ℝ, 0 < r ∧ 0 < s ∧
      (((r : ℂ) • u, (s : ℂ) • (v-(a : ℂ) • u)) : FullVector × FullVector) ∈ pairSet := by
  let h := form (1 : Matrix Index Index ℂ) Matrix.isHermitian_one
  have hpos : h.Pos := form_one_pos
  have hu : u ≠ 0 := by
    have hh := hind.ne_zero (0 : Fin 2)
    simpa using hh
  have hqu : 0 < h.q u := hpos u hu
  have harea : 0 < h.area u v := h.area_pos u v hpos hind
  let a := (h u v).re / h.q u
  let w := v-(a : ℂ) • u
  have hqw : h.q w = h.area u v / h.q u := by
    rw [HForm.q_shear]
    dsimp [a, HForm.area]
    field_simp
    ring
  have hwpos : 0 < h.q w := hqw ▸ div_pos harea hqu
  let r := (Real.sqrt (h.q u))⁻¹
  let s := (Real.sqrt (h.q w))⁻¹
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hqu)
  have hs : 0 < s := inv_pos.mpr (Real.sqrt_pos.mpr hwpos)
  refine ⟨a,r,s,hr,hs,?_,?_,?_⟩
  · change h.q ((r : ℂ) • u) = 1
    rw [HForm.q_real_smul]
    dsimp [r]
    rw [inv_pow, Real.sq_sqrt hqu.le, inv_mul_cancel₀ hqu.ne']
  · change h.q ((s : ℂ) • w) = 1
    rw [HForm.q_real_smul]
    dsimp [s]
    rw [inv_pow, Real.sq_sqrt hwpos.le, inv_mul_cancel₀ hwpos.ne']
  · change (h ((r : ℂ) • u) ((s : ℂ) • (v-(a : ℂ) • u))).re = 0
    rw [HForm.real_pair_shear_scale]
    dsimp [a]
    rw [div_mul_cancel₀ _ hqu.ne', sub_self, mul_zero]

theorem compact_uniform_all_planes {c C Ce lam : ℝ} (hc : 0 < c) (hC : c ≤ C) (hCe : 0 ≤ Ce)
    (hlam : pinchingThreshold c C (162*Ce) ≤ lam) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ A ∈ matrixSet c C,
      ∀ E4 E3 : Tensor Index, Symmetries E4 → Symmetries E3 → Supported E4 4 → Supported E3 3 →
      componentNorm E4 ≤ Ce*(t*(1-t)) → componentNorm E3 ≤ Ce*Real.sqrt (t*(1-t)) →
      ∀ u v : FullVector, LinearIndependent ℝ ![u,v] →
        -b ≤ H (compactCurvature A lam t E4 E3) u v / (2*metricArea (compactG A lam t) u v) ∧
        H (compactCurvature A lam t E4 E3) u v / (2*metricArea (compactG A lam t) u v) ≤ -a := by
  obtain ⟨a,b,ha,hab,hbound⟩ := compact_uniform_pinching hc hC hCe hlam
  refine ⟨a,b,ha,hab,?_⟩
  intro t ht A hA E4 E3 h4 h3 hs4 hs3 hn4 hn3 u v hind
  obtain ⟨k,r,s,hr,hs,hp⟩ := normalization u v hind
  let p : FullVector × FullVector := ((r : ℂ) • u, (s : ℂ) • (v-(k : ℂ) • u))
  let d : CompactData := (t,A,E4,E3,p)
  have hd : d ∈ dataSet c C Ce := ⟨ht,hA,h4,hs4,h3,hs3,hn4,hn3,hp⟩
  have hBd := hbound d hd
  have heq : compactQuotient lam d =
      H (compactCurvature A lam t E4 E3) u v / (2*metricArea (compactG A lam t) u v) := by
    change H _ ((r : ℂ) • u) ((s : ℂ) • (v-(k : ℂ) • u)) /
      (2*metricArea _ ((r : ℂ) • u) ((s : ℂ) • (v-(k : ℂ) • u))) = _
    rw [H_shear_scale _ (compactCurvature_symmetries A hA.1 lam t E4 E3 h4 h3)]
    have hK := compactG_hermitian A hA.1 lam t
    have heqA : metricArea (compactG A lam t) ((r : ℂ) • u) ((s : ℂ) • (v-(k : ℂ) • u)) =
        (r*s)^2*metricArea (compactG A lam t) u v :=
      (form (block (compactG A lam t) 1) (block_hermitian (n := Fin 2) _ hK 1)).area_shear_scale u v k r s
    rw [heqA, mul_left_comm 2, mul_div_mul_left _ _ (pow_ne_zero _ (mul_pos hr hs).ne')]
  rwa [heq] at hBd

end TensorAlgebra
end PinchedHartogs.PlaneAlgebra

namespace PinchedHartogs.PlaneAlgebra
namespace TensorAlgebra
open MatrixAlgebra Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise

theorem pairValue_pull {n : Type uKahler7224_1} [finiteIndex : Fintype n] (r : n → ℝ)
    (A : Matrix n n ℂ) (u v : n → ℂ) :
    pairValue (pullMatrix r A) u v = pairValue A (pullVector r u) (pullVector r v) := by
  simp only [pairValue, dotProduct, Matrix.mulVec, pullMatrix, pullVector,
    Pi.star_apply, star_mul, Complex.star_def, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem metricArea_pull (r : ℝ) (A : BaseMatrix) (u v : FullVector) :
    metricArea ((r^2) • A) u v =
      metricArea A (pullVector (horizontalScale r) u) (pullVector (horizontalScale r) v) := by
  unfold metricArea qValue
  rw [← pull_horizontal_matrix r A 1]
  simp only [pairValue_pull]

private theorem horizontalPull_independent {r : ℝ} (hr : r ≠ 0)
    (u v : FullVector) (hind : LinearIndependent ℝ ![u,v]) :
    LinearIndependent ℝ ![pullVector (horizontalScale r) u, pullVector (horizontalScale r) v] := by
  let e := (horizontalPullEquiv r hr).restrictScalars ℝ
  have hi := hind.map' e.toLinearMap e.ker
  have heq : (e.toLinearMap ∘ ![u,v]) =
      ![pullVector (horizontalScale r) u, pullVector (horizontalScale r) v] := by
    funext i
    fin_cases i <;> rfl
  rwa [heq] at hi

theorem curvatureModel_uniform_pinching {c C Ce lam : ℝ}
    (hc : 0 < c) (hC : c ≤ C) (hCe : 0 ≤ Ce)
    (hlam : pinchingThreshold c C (162*Ce) ≤ lam) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ x : ℝ, 0 ≤ x → ∀ (A : BaseMatrix) (hA : A.IsHermitian),
      (∀ w, c * euclidean.q w ≤ (form A hA).q w) →
      (∀ w, (form A hA).q w ≤ C * euclidean.q w) →
      ∀ T4 T3 : Tensor Index, Symmetries T4 → Symmetries T3 →
      Supported T4 4 → Supported T3 3 →
      componentNorm T4 ≤ Ce*x → componentNorm T3 ≤ Ce*Real.sqrt (x*(1+x)) →
      ∀ u v : FullVector, LinearIndependent ℝ ![u,v] →
        -b ≤ H (curvatureModel A lam x T4 T3) u v /
          (2*metricArea (horizontalMetric A lam x) u v) ∧
        H (curvatureModel A lam x T4 T3) u v /
          (2*metricArea (horizontalMetric A lam x) u v) ≤ -a := by
  obtain ⟨a,b,ha,hab,hbound⟩ := compact_uniform_all_planes hc hC hCe hlam
  refine ⟨a,b,ha,hab,?_⟩
  intro x hx A hA hl hu T4 T3 h4 h3 hs4 hs3 hn4 hn3 u v hind
  let t := x/(1+x)
  have hx1 : 0 < 1+x := by linarith
  have ht0 : 0 ≤ t := div_nonneg hx hx1.le
  have ht1 : t < 1 := (div_lt_one hx1).mpr (by linarith)
  have hxt : t/(1-t) = x := by
    dsimp [t]
    field_simp
    ; ring
  let r := Real.sqrt (1-t)
  obtain ⟨hr,hxt0,hr4,hr3⟩ := compact_scalars ht0 ht1
  change 0 < r at hr
  rw [hxt] at hr4 hr3
  change r^4*x = t*(1-t) at hr4
  change r^3*Real.sqrt (x*(1+x)) = Real.sqrt (t*(1-t)) at hr3
  let E4 := pullTensor (horizontalScale r) T4
  let E3 := pullTensor (horizontalScale r) T3
  have he4 : E4 = (r^4) • T4 := pull_supported r T4 hs4
  have he3 : E3 = (r^3) • T3 := pull_supported r T3 hs3
  have hne4 : componentNorm E4 ≤ Ce*(t*(1-t)) := by
    rw [he4, componentNorm_smul, abs_of_pos (pow_pos hr _), ← hr4]
    calc
      _ ≤ r^4*(Ce*x) := mul_le_mul_of_nonneg_left hn4 (by positivity)
      _ = _ := by ring
  have hne3 : componentNorm E3 ≤ Ce*Real.sqrt (t*(1-t)) := by
    rw [he3, componentNorm_smul, abs_of_pos (pow_pos hr _), ← hr3]
    calc
      _ ≤ r^3*(Ce*Real.sqrt (x*(1+x))) := mul_le_mul_of_nonneg_left hn3 (by positivity)
      _ = _ := by ring
  let u' := pullVector (horizontalScale r⁻¹) u
  let v' := pullVector (horizontalScale r⁻¹) v
  have hi : LinearIndependent ℝ ![u',v'] := horizontalPull_independent (inv_ne_zero hr.ne') u v hind
  have hAs : A ∈ matrixSet c C := ⟨hA,fun w ↦ ⟨hl w,hu w⟩⟩
  have hsE4 : Supported E4 4 := by rw [he4]; exact supported_smul _ _ hs4
  have hsE3 : Supported E3 3 := by rw [he3]; exact supported_smul _ _ hs3
  have hb := hbound t ⟨ht0,ht1.le⟩ A hAs E4 E3
    (pull_symmetries _ _ h4) (pull_symmetries _ _ h3) hsE4 hsE3 hne4 hne3 u' v' hi
  have hunit := (G_posdef hc ((threshold_positive hc hC).trans_le hlam) hx A hA hl).isUnit
  have hunit' : IsUnit (horizontalMetric A lam (t/(1-t))) := by rwa [hxt]
  have hmodel := pull_model A lam t ht1 hunit' T4 T3
  rw [hxt] at hmodel
  change pullTensor (horizontalScale r) (curvatureModel A lam x T4 T3) =
    compactCurvature A lam t E4 E3 at hmodel
  have hmet : compactG A lam t = (r^2) • horizontalMetric A lam x := by
    rw [compactG_eq A lam (ne_of_lt ht1), hxt]
    dsimp [r]
    rw [Real.sq_sqrt (sub_nonneg.mpr ht1.le)]
  have hu' : pullVector (horizontalScale r) u' = u :=
    (horizontalPullEquiv r hr.ne').apply_symm_apply u
  have hv' : pullVector (horizontalScale r) v' = v :=
    (horizontalPullEquiv r hr.ne').apply_symm_apply v
  rwa [← hmodel, H_pull, hmet, metricArea_pull, hu', hv'] at hb

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

lemma horizontalPart_supported (j : ℕ) (T : Tensor Index) : Supported (horizontalPart j T) j := by
  intro a b c d h
  simp [horizontalPart, h]

lemma horizontalPart_symmetries (j : ℕ) (T : Tensor Index) (hT : Symmetries T) :
    Symmetries (horizontalPart j T) := by
  have hh (a b c d : Index) : horizontalCount a b c d = horizontalCount c b a d := by
    unfold horizontalCount; omega
  have ha (a b c d : Index) : horizontalCount a b c d = horizontalCount a d c b := by
    unfold horizontalCount; omega
  have hr (a b c d : Index) : horizontalCount a b c d = horizontalCount b a d c := by
    unfold horizontalCount; omega
  constructor
  · intro a b c d; simp only [horizontalPart, hh a b c d, hT.hol a b c d]
  · intro a b c d; simp only [horizontalPart, ha a b c d, hT.anti a b c d]
  · intro a b c d; simp only [horizontalPart, hr a b c d, apply_ite star, star_zero, hT.reality a b c d]

lemma complex_horizontalMetric (A : Matrix (Fin 2) (Fin 2) ℂ) (lam x : ℝ) :
    (lam : ℂ) • 1 + (x : ℂ) • A = horizontalMetric A lam x := by
  ext i j
  simp [horizontalMetric, Complex.real_smul]

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

lemma normalError_symmetries {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) :
    Symmetries (normalError f lam w) :=
  tensor_symmetries_sub (normalCurvature_symmetries hf lam w hn)
    (principal_symmetries _ (baseHessian_isHermitian (hf.of_le (WithTop.coe_le_coe.mpr le_top))) _ _)

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsMatrixBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler7661_1

open scoped ContDiff
open Complex
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
namespace PinchedHartogs
open PlaneAlgebra PlaneAlgebra.MatrixAlgebra PlaneAlgebra.TensorAlgebra Matrix Unitary

lemma positive_horizontalMetric {c lam x : ℝ} (hc : 0 < c) (hlam : 0 < lam) (hx : 0 ≤ x)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian)
    (hl : ∀ w, c * euclidean.q w ≤ (form A hA).q w) :
    (horizontalMetric A lam x).PosDef := by
  apply (form_pos_iff _ (horizontalMetric_hermitian A hA lam x)).mp
  intro u hu
  have hp := form_one_pos u hu
  have hAu : 0 ≤ (form A hA).q u := (mul_nonneg hc.le hp.le).trans (hl u)
  simp only [horizontalMetric, form, HForm.q, add_mulVec, smul_mulVec, dotProduct_add,
    dotProduct_smul, Complex.add_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change 0 < lam * euclidean.q u + x * (form A hA).q u
  exact add_pos_of_pos_of_nonneg (mul_pos hlam hp) (mul_nonneg hx hAu)

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
namespace PinchedHartogs
open PlaneAlgebra PlaneAlgebra.MatrixAlgebra PlaneAlgebra.TensorAlgebra Matrix

lemma sum_normalIndex (f : Fin 3 → ℂ) : (∑ i, f i) = ∑ a : Index, f (normalIndex a) :=
  (normalIndexEquiv.sum_comp f).symm

lemma normalFrame_coordinates (r : ℝ) (hr : r ≠ 0) (u : FullVector) (a : Index) :
    coordinates (normalFrameEquiv r hr u) (normalIndex a) = (verticalScale r a : ℂ) * u a := by
  change coordinateLinearEquiv (normalFrameEquiv r hr u) (normalIndex a) = _
  simp only [normalFrameEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  change (verticalScale r (normalIndexEquiv.symm (normalIndexEquiv a)) : ℂ) *
    u (normalIndexEquiv.symm (normalIndexEquiv a)) = _
  rw [Equiv.symm_apply_apply]

lemma tensorValue_normalFrame (R : CurvatureTensor) (r : ℝ) (hr : r ≠ 0) (u v w y : FullVector) :
    tensorValue R (normalFrameEquiv r hr u) (normalFrameEquiv r hr v)
      (normalFrameEquiv r hr w) (normalFrameEquiv r hr y) =
      eval (pullTensor (verticalScale r) (fun a b c d => R (normalIndex a) (normalIndex b) (normalIndex c) (normalIndex d))) u v w y := by
  rw [eval_pull]
  simp only [tensorValue, eval, Fintype.sum_prod_type]
  simp_rw [sum_normalIndex, normalFrame_coordinates]
  rfl

lemma hermitianValue_normalFrame (A : CMatrix) (r : ℝ) (hr : r ≠ 0) (u v : FullVector) :
    hermitianValue A (normalFrameEquiv r hr u) (normalFrameEquiv r hr v) =
      pairValue (pullMatrix (verticalScale r) (fun a b => A (normalIndex a) (normalIndex b))) u v := by
  erw [pairValue_pull]
  simp only [hermitianValue, pairValue, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  simp_rw [sum_normalIndex, normalFrame_coordinates]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [pullVector]
  ring

lemma normalPotential_frame_metric {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) :
    pullMatrix (verticalScale ((Real.sqrt (barrierQ (normalLogWeight f w (0,w))))⁻¹))
        (fun a b => complexHessian (normalPotential f lam w) (0,w) (normalIndex a) (normalIndex b)) =
      block (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w)))) 1 := by
  rw [normalPotential_hessian_block hf lam w hn, complex_horizontalMetric]
  have hs := (sqrt_normalization (barrierQ (normalLogWeight f w (0,w))) (barrierQ_positive hn)).1
  ext a b
  cases a <;> cases b <;> simp only [pullMatrix, verticalScale, normalIndex]
  · simpa [block3, block, pow_two] using hs
  · rename_i b; fin_cases b <;> simp [block3, block]
  · rename_i a; fin_cases a <;> simp [block3, block]
  · rename_i a b; fin_cases a <;> fin_cases b <;> simp [block3, block]

lemma normalPotential_sectional {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) (u v : FullVector) :
    sectional (complexHessian (normalPotential f lam w)) (0,w)
      (normalFrameEquiv ((Real.sqrt (barrierQ (normalLogWeight f w (0,w))))⁻¹)
        (inv_ne_zero (Real.sqrt_pos.mpr (barrierQ_positive hn)).ne') u)
      (normalFrameEquiv ((Real.sqrt (barrierQ (normalLogWeight f w (0,w))))⁻¹)
        (inv_ne_zero (Real.sqrt_pos.mpr (barrierQ_positive hn)).ne') v) =
    H (normalCurvature f lam w) u v /
      (2*metricArea (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w)))) u v) := by
  simp only [sectional, tensorValue_normalFrame, normalCurvature, H,
    realArea, hermitianValue_normalFrame, normalPotential_frame_metric hf lam w hn,
    metricArea, qValue]

lemma metricThreshold_pos {c C : ℝ} (hc : 0 < c) (hC : c ≤ C) : 0 < metricThreshold c C := by
  exact lt_of_lt_of_le (show 0 < C+1 by linarith) (le_max_left _ _)

lemma normalPotentials_uniform_pinching_oai {c C lam : ℝ} (hc : 0 < c) (hC : c ≤ C)
    (hlam : metricThreshold c C ≤ lam) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ (f : Base → ℝ) (hf : ContDiffAt ℝ ∞ f 0),
      (∀ u, c * euclidean.q u ≤ (form (baseHessian f 0)
        (baseHessian_isHermitian (hf.of_le (WithTop.coe_le_coe.mpr le_top)))).q u) →
      (∀ u, (form (baseHessian f 0)
        (baseHessian_isHermitian (hf.of_le (WithTop.coe_le_coe.mpr le_top)))).q u ≤ C * euclidean.q u) →
      (∀ i j k : Fin 2, ‖liftedThird f (0,0) i.castSucc j.castSucc k.castSucc‖ ≤ C) →
      (∀ i j k l : Fin 2, ‖liftedFourth f (0,0) i.castSucc j.castSucc k.castSucc l.castSucc‖ ≤ C) →
      ∀ w : ℂ, normalLogWeight f w (0,w) < 0 →
      ∀ u v : Ambient, LinearIndependent ℝ ![u,v] →
        -b ≤ sectional (complexHessian (normalPotential f lam w)) (0,w) u v ∧
          sectional (complexHessian (normalPotential f lam w)) (0,w) u v ≤ -a := by
  have hCp : 0 ≤ C := hc.le.trans hC
  have he : 0 ≤ metricErrorConstant c C := by unfold metricErrorConstant; positivity
  have hlp : 0 < lam := (metricThreshold_pos hc hC).trans_le hlam
  obtain ⟨a,b,ha,hab,hbound⟩ := curvatureModel_uniform_pinching hc hC he hlam
  refine ⟨a,b,ha,hab,?_⟩
  intro f hf hl hu hJ hB w hn u v hind
  let x := barrierX (normalLogWeight f w (0,w))
  let q := barrierQ (normalLogWeight f w (0,w))
  have hx : 0 ≤ x := (barrierX_positive hn).le
  have hH := baseHessian_isHermitian (hf.of_le (m := 2) (WithTop.coe_le_coe.mpr le_top))
  have hG : (horizontalMetric (baseHessian f 0) lam x).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (positive_horizontalMetric hc hlp hx _ hH hl).isUnit)
  let L := normalFrameEquiv ((Real.sqrt q)⁻¹) (inv_ne_zero (Real.sqrt_pos.mpr (barrierQ_positive hn)).ne')
  have hi : LinearIndependent ℝ ![L.symm u,L.symm v] := by
    convert hind.map' (L.symm.restrictScalars ℝ).toLinearMap
      (LinearMap.ker_eq_bot_of_injective (L.symm.restrictScalars ℝ).injective) using 1
    all_goals first | rfl | (ext i; fin_cases i <;> rfl)
  have hbnd := normalErrors_bounds hf hc hC hlp hl hu hJ hB w hn
  have hs := normalError_symmetries hf lam w hn
  have hbd := hbound x hx (baseHessian f 0) hH hl hu
    (horizontalPart 4 (normalError f lam w)) (horizontalPart 3 (normalError f lam w))
    (horizontalPart_symmetries 4 _ hs) (horizontalPart_symmetries 3 _ hs)
    (horizontalPart_supported 4 _) (horizontalPart_supported 3 _) hbnd.1 hbnd.2
    (L.symm u) (L.symm v) hi
  rw [← normalCurvature_model hf lam w hn hG] at hbd
  have heq := normalPotential_sectional hf lam w hn (L.symm u) (L.symm v)
  change sectional _ _ (L (L.symm u)) (L (L.symm v)) = _ at heq
  rw [L.apply_symm_apply, L.apply_symm_apply] at heq
  rwa [heq]

end PinchedHartogs

end

end OAI
end

theorem solution : type_of% @OAI.PinchedHartogs.normalPotentials_uniform_pinching_oai := @OAI.PinchedHartogs.normalPotentials_uniform_pinching_oai
