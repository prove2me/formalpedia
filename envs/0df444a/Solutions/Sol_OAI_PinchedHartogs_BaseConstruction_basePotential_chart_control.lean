-- Prove2me | solution 1 for OAI.PinchedHartogs.BaseConstruction.basePotential_chart_control
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:06:41.717866+00:00
-- url     : https://prove2.me/submissions/950f884a-461e-4477-b9f3-54c97052a68c

import Mathlib
import Definitions.Def_PinchedKahler
import Definitions.Def_OAIQWPH000
import Definitions.Def_OAIQWPH001
import Theorems.Thm_OAI_PinchedHartogs_BaseConstruction_analytic_jet_bound
import Theorems.Thm_OAI_PinchedHartogs_BaseConstruction_testSeries_chart_uniform_jets

section
-- module Solutions.OAIQW_PinchedHartogs.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

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

lemma dbar_fiber (p : Ambient) (i : Fin 3) :
    dbar (fun q => q.2) p i = 0 := by
  have hd : fderiv ℝ (fun q : Ambient => q.2) p = ContinuousLinearMap.snd ℝ Base ℂ :=
    (ContinuousLinearMap.snd ℝ Base ℂ).fderiv
  fin_cases i <;> simp [dbar, hd, coordVector]

lemma dbar_fiber_norm_sq (p : Ambient) (j : Fin 3) :
    dbar (fun q : Ambient => (‖q.2‖ ^ 2 : ℝ)) p j = p.2 * (if j = 2 then 1 else 0) := by
  have he (q : Ambient) : ((‖q.2‖ ^ 2 : ℝ) : ℂ) = q.2 * star q.2 := by
    simpa only [Complex.normSq_eq_norm_sq, Complex.star_def] using (Complex.mul_conj q.2).symm
  simp only [he]
  rw [dbar_mul (by fun_prop) (by fun_prop), dbar_fiber, dbar_conj (by fun_prop), dz_fiber]
  split_ifs <;> simp

lemma dz_fiber_norm_sq (p : Ambient) (j : Fin 3) :
    dz (fun q : Ambient => (‖q.2‖ ^ 2 : ℝ)) p j = star p.2 * (if j = 2 then 1 else 0) := by
  have hd : DifferentiableAt ℝ (fun q : Ambient => ‖q.2‖ ^ 2) p :=
    (contDiff_norm_sq ℂ (n := 1)).differentiable (by simp) |>.differentiableAt |>.comp p (by fun_prop)
  have h := dbar_eq_star_dz_real hd j
  rw [dbar_fiber_norm_sq] at h
  have := congrArg star h
  split_ifs at * <;> simpa using this.symm

lemma complexHessian_fiber_norm_sq (p : Ambient) (i j : Fin 3) :
    complexHessian (fun q : Ambient => ‖q.2‖ ^ 2) p i j =
      (if i = 2 then 1 else 0) * (if j = 2 then 1 else 0) := by
  unfold complexHessian
  simp only [dbar_fiber_norm_sq]
  by_cases hj : j = 2
  · simp only [hj, ite_eq_left, mul_one]
    exact dz_fiber p i
  · simp [hj, dz]

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

lemma hermitianValue_lift_base {f : Base → ℝ} {p : Ambient} (hf : ContDiffAt ℝ 2 f p.1)
    (u v : Ambient) :
    hermitianValue (complexHessian (fun q : Ambient => f q.1) p) u v =
      ∑ i, ∑ j, baseHessian f p.1 i j * u.1 i * star (v.1 j) := by
  simp [hermitianValue, complexHessian_lift_base hf, Fin.sum_univ_three, Fin.sum_univ_two, coordinates]

lemma coordinates_real_decomposition (u : Ambient) :
    u = ∑ i : Fin 3, ((coordinates u i).re • coordVector i +
      (coordinates u i).im • (Complex.I • coordVector i)) := by
  apply Prod.ext
  · ext j
    fin_cases j <;>
      simp [Fin.sum_univ_three, coordinates, coordVector, Complex.re_add_im, Complex.real_smul]
  · simp [Fin.sum_univ_three, coordinates, coordVector, Complex.re_add_im, Complex.real_smul]

private lemma wirtinger_pair_algebra (a b z : ℂ) :
    (a - Complex.I * b) / 2 * z + (a + Complex.I * b) / 2 * star z =
      (z.re : ℂ) * a + (z.im : ℂ) * b := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

lemma fderiv_wirtinger (f : Ambient → ℂ) (p u : Ambient) :
    fderiv ℝ f p u = ∑ i : Fin 3,
      (dz f p i * coordinates u i + dbar f p i * star (coordinates u i)) := by
  conv_lhs => rw [coordinates_real_decomposition u]
  simp only [map_sum, map_add, map_smul, Complex.real_smul]
  apply Finset.sum_congr rfl
  intro i hi
  exact (wirtinger_pair_algebra _ _ _).symm

lemma coordinates_equiv (u : Ambient) : coordinates u = coordinateEquiv u := rfl

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

lemma coordinates_complex_smul (c : ℂ) (u : Ambient) :
    coordinates (c • u) = c • coordinates u := by
  funext i
  fin_cases i <;> rfl

private lemma complex_direction_algebra (a b z : ℂ) :
    (a * z + b * star z - Complex.I * (a * (Complex.I * z) + b * star (Complex.I * z))) / 2 =
      a * z := by
  simp only [star_mul', Complex.star_def, Complex.conj_I]
  linear_combination (b * starRingEnd ℂ z - a * z) / 2 * Complex.I_sq

private lemma anticomplex_direction_algebra (a b z : ℂ) :
    (a * z + b * star z + Complex.I * (a * (Complex.I * z) + b * star (Complex.I * z))) / 2 =
      b * star z := by
  simp only [star_mul', Complex.star_def, Complex.conj_I]
  linear_combination (a * z - b * starRingEnd ℂ z) / 2 * Complex.I_sq

lemma fderiv_complex_direction (f : Ambient → ℂ) (p u : Ambient) :
    (fderiv ℝ f p u - Complex.I * fderiv ℝ f p (Complex.I • u)) / 2 =
      ∑ i, dz f p i * coordinates u i := by
  rw [fderiv_wirtinger f p u, fderiv_wirtinger f p (Complex.I • u)]
  simp only [coordinates_complex_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  exact complex_direction_algebra _ _ _

lemma fderiv_anticomplex_direction (f : Ambient → ℂ) (p u : Ambient) :
    (fderiv ℝ f p u + Complex.I * fderiv ℝ f p (Complex.I • u)) / 2 =
      ∑ i, dbar f p i * star (coordinates u i) := by
  rw [fderiv_wirtinger f p u, fderiv_wirtinger f p (Complex.I • u)]
  simp only [coordinates_complex_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  exact anticomplex_direction_algebra _ _ _

lemma dz_comp_holomorphic {f : Ambient → ℂ} {F : Ambient → Ambient} {p : Ambient}
    (hf : DifferentiableAt ℝ f (F p)) (hF : DifferentiableAt ℂ F p) (i : Fin 3) :
    dz (f ∘ F) p i = ∑ a, dz f (F p) a * complexJacobian F p a i := by
  have hd := (hf.hasFDerivAt.comp p (hF.hasFDerivAt.restrictScalars ℝ)).fderiv
  rw [dz, hd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    map_smul]
  exact fderiv_complex_direction f (F p) (fderiv ℂ F p (coordVector i))

lemma dbar_comp_holomorphic {f : Ambient → ℂ} {F : Ambient → Ambient} {p : Ambient}
    (hf : DifferentiableAt ℝ f (F p)) (hF : DifferentiableAt ℂ F p) (i : Fin 3) :
    dbar (f ∘ F) p i = ∑ a, dbar f (F p) a * star (complexJacobian F p a i) := by
  have hd := (hf.hasFDerivAt.comp p (hF.hasFDerivAt.restrictScalars ℝ)).fderiv
  rw [dbar, hd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    map_smul]
  exact fderiv_anticomplex_direction f (F p) (fderiv ℂ F p (coordVector i))

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

lemma dz_sum {ι : Type uKahler2074_1} (s : Finset ι) {f : ι → Ambient → ℂ} {p : Ambient}
    (hf : ∀ j ∈ s, DifferentiableAt ℝ (f j) p) (i : Fin 3) :
    dz (fun q => ∑ j ∈ s, f j q) p i = ∑ j ∈ s, dz (f j) p i := by
  simp only [dz, fderiv_fun_sum hf, sum_apply,
    Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]

lemma complexJacobian_analyticAt {F : Ambient → Ambient} {p : Ambient}
    (hF : AnalyticAt ℂ F p) (a i : Fin 3) :
    AnalyticAt ℂ (fun q => complexJacobian F q a i) p := by
  let ev : (Ambient →L[ℂ] Ambient) →L[ℂ] Ambient :=
    ContinuousLinearMap.apply ℂ Ambient (coordVector i)
  let L : Ambient →L[ℂ] ℂ := (ContinuousLinearMap.proj a).comp coordinateEquiv.toContinuousLinearMap
  exact ((L.comp ev).analyticAt _).comp hF.fderiv

lemma complexHessian_comp_holomorphic {f : Ambient → ℝ} {F : Ambient → Ambient}
    {p : Ambient} (hf : ContDiffAt ℝ 2 f (F p)) (hF : AnalyticAt ℂ F p) (i j : Fin 3) :
    complexHessian (f ∘ F) p i j =
      ∑ a, ∑ b, complexHessian f (F p) a b * complexJacobian F p a i *
        star (complexJacobian F p b j) := by
  have hdF := hF.differentiableAt
  have he : (fun q => dbar (fun r => (f (F r) : ℂ)) q j) =ᶠ[𝓝 p]
      (fun q => ∑ b, dbar (fun r => (f r : ℂ)) (F q) b * star (complexJacobian F q b j)) := by
    filter_upwards [hF.eventually_analyticAt,
      hdF.continuousAt (hf.eventually (by norm_num))] with q hFq hfq
    change ContDiffAt ℝ 2 f (F q) at hfq
    exact dbar_comp_holomorphic
      ((_root_.OAI.ContDiffAt.hartogs_real_cast hfq).differentiableAt (by norm_num)) hFq.differentiableAt j
  have hdb (b : Fin 3) : DifferentiableAt ℝ (fun q => dbar (fun r => (f r : ℂ)) q b) (F p) :=
    (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 1) (by norm_num) b).differentiableAt (by norm_num)
  have hJ (a i : Fin 3) := (complexJacobian_analyticAt hF a i).differentiableAt
  change dz (fun q => dbar (fun r => (f (F r) : ℂ)) q j) p i = _
  rw [dz_congr he]
  have hs := dz_sum Finset.univ (fun b hb =>
    ((hdb b).comp p (hdF.restrictScalars ℝ)).mul ((hJ b j).restrictScalars ℝ).star) i
  change dz (fun q => ∑ b, dbar (fun r => (f r : ℂ)) (F q) b *
    star (complexJacobian F q b j)) p i = _ at hs
  rw [hs]
  calc
    _ = ∑ b, ∑ a, complexHessian f (F p) a b * complexJacobian F p a i *
        star (complexJacobian F p b j) := by
      apply Finset.sum_congr rfl
      intro b hb
      change dz (fun q => dbar (fun r => (f r : ℂ)) (F q) b *
        star (complexJacobian F q b j)) p i = _
      have hm := dz_mul ((hdb b).comp p (hdF.restrictScalars ℝ))
        ((hJ b j).restrictScalars ℝ).star i
      change dz (fun q => dbar (fun r => (f r : ℂ)) (F q) b *
        star (complexJacobian F q b j)) p i = _ at hm
      rw [hm, dz_conj ((hJ b j).restrictScalars ℝ), dbar_holomorphic (hJ b j)]
      simp only [star_zero, mul_zero, add_zero]
      have hc := dz_comp_holomorphic (hdb b) hdF i
      rw [hc, Finset.sum_mul]
      rfl
    _ = _ := Finset.sum_comm

lemma complexHessian_pullback {f : Ambient → ℝ} {F : Ambient → Ambient} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f (F p)) (hF : AnalyticAt ℂ F p) :
    complexHessian (f ∘ F) p = pullbackMetric (complexHessian f) F p := by
  ext i j
  rw [complexHessian_comp_holomorphic hf hF]
  simp only [pullbackMetric, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.conjTranspose_apply, jacobianMatrix, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma hermitianValue_dot (h : CMatrix) (u v : Ambient) :
    hermitianValue h u v = coordinates u ⬝ᵥ (h *ᵥ star (coordinates v)) := by
  simp only [hermitianValue, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma hermitianValue_matrixPull (A h : CMatrix) (u v : Ambient) :
    hermitianValue (matrixPull A h) u v = hermitianValue h (matrixPush A u) (matrixPush A v) := by
  simp only [hermitianValue_dot, matrixPull, matrixPush, coordinates_equiv_symm,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_conjTranspose, star_star, Matrix.vecMul_transpose]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

lemma coordinates_complex_decomposition (u : Ambient) :
    u = ∑ i, coordinates u i • coordVector i := by
  apply coordinateEquiv.injective
  ext j
  fin_cases j <;> simp [Fin.sum_univ_three, coordinates, coordVector, coordinateEquiv,
    coordinateLinearEquiv]

lemma matrixPush_jacobian (F : Ambient → Ambient) (p u : Ambient) :
    matrixPush (jacobianMatrix F p) u = fderiv ℂ F p u := by
  apply coordinateEquiv.injective
  simp only [matrixPush, ContinuousLinearEquiv.apply_symm_apply]
  change (jacobianMatrix F p) *ᵥ coordinates u = coordinates (fderiv ℂ F p u)
  conv_rhs => rw [coordinates_complex_decomposition u]
  ext a
  simp only [map_sum, map_smul, coordinates_equiv, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct, jacobianMatrix, Matrix.of_apply, complexJacobian]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

lemma hermitianValue_pullback (g : Ambient → CMatrix) (F : Ambient → Ambient) (p u v : Ambient) :
    hermitianValue (pullbackMetric g F p) u v =
      hermitianValue (g (F p)) (fderiv ℂ F p u) (fderiv ℂ F p v) := by
  change hermitianValue (matrixPull (jacobianMatrix F p) (g (F p))) u v = _
  rw [hermitianValue_matrixPull, matrixPush_jacobian, matrixPush_jacobian]

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
-- module Solutions.OAIQW_PinchedHartogs.HartogsCharts
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

lemma centeredChart_norm_identity {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) (z : Base) (hd : 1 + (r : ℂ) * z 0 ≠ 0) :
    1 - ‖centeredChart r U z‖ ^ 2 =
      (1-r^2) * (1-‖z‖^2) / ‖1 + (r : ℂ) * z 0‖^2 := by
  have hsq : (Real.sqrt (1-r^2))^2 = 1-r^2 := Real.sq_sqrt (by nlinarith)
  have hdn : ‖1 + (r : ℂ) * z 0‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hd)
  simp only [centeredChart, LinearIsometryEquiv.norm_map, EuclideanSpace.norm_sq_eq,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    div_pow, mul_pow, sq_abs, hsq]
  field_simp [hdn]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
  ring

lemma centeredChart_den_ne_zero {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {z : Base} (hz : z ∈ ball) : 1 + (r : ℂ) * z 0 ≠ 0 := by
  have hz0 := PiLp.norm_apply_le (p := (2 : ENNReal)) z 0
  have hnz : ‖z‖ < 1 := hz
  have hm : ‖(r : ℂ) * z 0‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    have := norm_nonneg (z 0)
    nlinarith
  intro he
  have hh : (r : ℂ) * z 0 = -1 := by linear_combination he
  rw [hh] at hm
  norm_num at hm

lemma centeredChart_mapsTo {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) : MapsTo (centeredChart r U) ball ball := by
  intro z hz
  have hd := centeredChart_den_ne_zero hr hr1 hz
  have he := centeredChart_norm_identity hr hr1 U z hd
  have hpos : 0 < (1-r^2) * (1-‖z‖^2) / ‖1 + (r : ℂ)*z 0‖^2 := by
    apply div_pos
    · apply mul_pos <;> have hn : ‖z‖ < 1 := hz <;> nlinarith [norm_nonneg z]
    · exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hd)
  change ‖centeredChart r U z‖ < 1
  nlinarith [norm_nonneg (centeredChart r U z)]

lemma psi_centeredChart {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) {z : Base} (hz : z ∈ ball) :
    psi (centeredChart r U z) = psi z - Real.log (1-r^2) +
      2 * (Complex.log (1+(r : ℂ)*z 0)).re := by
  have hd := centeredChart_den_ne_zero hr hr1 hz
  have hrp : 0 < 1-r^2 := by nlinarith
  have hzp : 0 < 1-‖z‖^2 := by have h : ‖z‖ < 1 := hz; nlinarith [norm_nonneg z]
  have hdp : ‖1+(r : ℂ)*z 0‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hd)
  simp only [psi, centeredChart_norm_identity hr hr1 U z hd, Complex.log_re,
    Real.log_div (mul_pos hrp hzp).ne' hdp, Real.log_mul hrp.ne' hzp.ne', Real.log_pow]
  ring

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

lemma complexHessian_congr {f g : Ambient → ℝ} {p : Ambient}
    (he : f =ᶠ[𝓝 p] g) : complexHessian f p = complexHessian g p := by
  ext i j
  apply dz_congr
  filter_upwards [he.eventually_nhds] with q hq
  apply dbar_congr _ j
  filter_upwards [hq] with r hr
  exact congrArg Complex.ofReal hr

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

lemma psi_chart_hessian_eventually {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) (w : ℂ) :
    complexHessian (fun q : Ambient => psi (centeredChart r U q.1)) =ᶠ[𝓝 (0,w)]
      complexHessian (fun q : Ambient => psi q.1) := by
  let P : Ambient → ℂ := fun q => (Real.log (1-r^2) / 2 : ℝ) - Complex.log (1+(r : ℂ)*q.1 0)
  have hP : AnalyticAt ℂ P (0,w) := by
    have hd : AnalyticAt ℂ (fun q : Ambient => 1 + (r : ℂ)*q.1 0) (0,w) :=
      analyticAt_const.add (analyticAt_const.mul ((horizontalCoordinate 0).analyticAt _))
    exact analyticAt_const.sub ((analyticAt_clog (by simp)).comp hd)
  have hb : ∀ᶠ q : Ambient in 𝓝 (0,w), q.1 ∈ ball :=
    continuous_fst.continuousAt (isOpen_ball.mem_nhds (by simp [ball]))
  have he : (fun q : Ambient => psi (centeredChart r U q.1)) =ᶠ[𝓝 (0,w)]
      (fun q => psi q.1 - 2*(P q).re) := by
    filter_upwards [hb] with q hq
    rw [psi_centeredChart hr hr1 U hq]
    simp only [P, Complex.sub_re, Complex.ofReal_re]
    ring
  filter_upwards [he.eventually_nhds, hb, hP.eventually_analyticAt] with q heq hq hPq
  rw [complexHessian_congr heq]
  apply complexHessian_gauge _ hPq
  exact ((psi_contDiffAt hq).comp q contDiffAt_fst).of_le (by exact WithTop.coe_le_coe.mpr le_top)

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

lemma baseHessian_contDiffAt {f : Base → ℝ} {z : Base} (hf : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (baseHessian f) z := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
  exact _root_.OAI.ContDiffAt.hartogs_dzBase (_root_.OAI.ContDiffAt.hartogs_dbarBase hc (m := ∞) (by simp) j) (by simp) i

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseLogTests
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

open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder
namespace PinchedHartogs
namespace BaseConstruction

lemma bracket_analytic (p : Base) : AnalyticOnNhd ℂ (fun z => bracket z p) univ :=
  fun z _ => (innerSL ℂ p).analyticAt z

lemma peakPolynomial_analytic (P : Finset Sphere) (k : ℕ) :
    AnalyticOnNhd ℂ (peakPolynomial P k) univ := by
  intro z hz
  apply Finset.analyticAt_fun_sum
  intro p hp
  exact (bracket_analytic p z (mem_univ _)).pow k

lemma regularizedLog_eq (a ε : ℝ) (v : ℂ) (hε : ε ≠ 0) :
    regularizedLog a ε v = Real.log (‖1-(a:ℂ)*v‖^2+ε^2)-Real.log (1+ε^2) := by
  apply Real.log_div <;> positivity

lemma regularizedLog_contDiff (a : ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ ∞ (regularizedLog a ε) := by
  have hn : ContDiff ℝ ∞ (fun v : ℂ => ‖1-(a:ℂ)*v‖^2+ε^2) :=
    ((contDiff_norm_sq ℂ).comp (contDiff_const.sub (contDiff_const.mul contDiff_id))).add contDiff_const
  have hh : ContDiff ℝ ∞ (fun v : ℂ => Real.log (‖1-(a:ℂ)*v‖^2+ε^2)-Real.log (1+ε^2)) :=
    (hn.log (fun v => by positivity)).sub contDiff_const
  have he : regularizedLog a ε = (fun v : ℂ => Real.log (‖1-(a:ℂ)*v‖^2+ε^2)-Real.log (1+ε^2)) :=
    funext (fun v => regularizedLog_eq a ε v hε)
  rw [he]
  exact hh

lemma logarithmicTest_contDiff (a : ℝ) {ε : ℝ} (hε : ε ≠ 0) (P : Finset Sphere) (k : ℕ) :
    ContDiff ℝ ∞ (logarithmicTest a ε P k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (regularizedLog_contDiff a hε).contDiffAt.comp z
    (((peakPolynomial_analytic P k) z (mem_univ _)).contDiffAt.restrict_scalars ℝ)

lemma peakPolynomial_zero (P : Finset Sphere) {k : ℕ} (hk : k ≠ 0) :
    peakPolynomial P k 0 = 0 := by simp [peakPolynomial,bracket,hk]

lemma peakPolynomial_homogeneous (P : Finset Sphere) (k : ℕ) (c : ℂ) (z : Base) :
    peakPolynomial P k (c • z) = c^k * peakPolynomial P k z := by
  simp only [peakPolynomial,bracket, inner_smul_right,mul_pow,Finset.mul_sum]

lemma regularizedLog_lipschitz_bound (a : ℝ) {ε : ℝ} (hε : ε ≠ 0) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℂ, ‖v‖ ≤ A → |regularizedLog a ε v| ≤ C*‖v‖ := by
  have hs := regularizedLog_contDiff a hε
  have hc : Continuous (fderiv ℝ (regularizedLog a ε)) := hs.continuous_fderiv (by norm_num)
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:ℂ) A).bddAbove_image hc.norm.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro v hv
  have hbound : ∀ x ∈ Metric.closedBall (0:ℂ) A, ‖fderiv ℝ (regularizedLog a ε) x‖ ≤ max C 0 := by
    intro x hx
    exact (hC (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  have hm := (convex_closedBall (0:ℂ) A).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hs.differentiable (by norm_num) x) hbound
    (show (0:ℂ) ∈ Metric.closedBall 0 A by simpa using hA)
    (show v ∈ Metric.closedBall 0 A by simpa using hv)
  simpa [Real.norm_eq_abs] using hm

private lemma regularizedFiberLog_contDiff {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ ∞ (regularizedFiberLog ε) := by
  have he := sq_pos_of_ne_zero hε
  have hn : ContDiff ℝ ∞ (fun q : Ambient => ‖q.2‖^2+ε^2) :=
    ((contDiff_norm_sq ℂ).comp contDiff_snd).add contDiff_const
  exact (hn.log (fun q => ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) he))).sub contDiff_const

private lemma regularizedFiberLog_hessian {ε : ℝ} (hε : ε ≠ 0) (q : Ambient) (i j : Fin 3) :
    complexHessian (regularizedFiberLog ε) q i j =
      ((ε^2/(‖q.2‖^2+ε^2)^2 : ℝ):ℂ) * (if i=2 then 1 else 0)*(if j=2 then 1 else 0) := by
  have hden : ‖q.2‖^2+ε^2 ≠ 0 := by positivity
  have hρ : ∀ᶠ y in 𝓝 (‖q.2‖^2),
      HasDerivAt (fun s => Real.log (s+ε^2)-Real.log (1+ε^2)) ((y+ε^2)⁻¹) y := by
    filter_upwards [(continuousAt_id.add continuousAt_const).eventually_ne hden] with y hy
    simpa [one_div] using (((hasDerivAt_id y).add_const (ε^2)).log hy).sub_const (Real.log (1+ε^2))
  have hρ' : HasDerivAt (fun s : ℝ => (s+ε^2)⁻¹) (-( (‖q.2‖^2+ε^2)^2)⁻¹) (‖q.2‖^2) := by
    convert ((hasDerivAt_id (‖q.2‖^2)).add_const (ε^2)).inv hden using 1 <;> try rfl
    simp [one_div, neg_div]
  have hh := complexHessian_real_comp
    (((contDiff_norm_sq ℂ).comp contDiff_snd).contDiffAt : ContDiffAt ℝ 2 (fun p : Ambient => ‖p.2‖^2) q)
    hρ hρ' i j
  dsimp only [Function.comp_def] at hh
  rw [complexHessian_fiber_norm_sq,dz_fiber_norm_sq,dbar_fiber_norm_sq] at hh
  change complexHessian (regularizedFiberLog ε) q i j = _ at hh
  rw [hh]
  have hn : star q.2 * q.2 = (‖q.2‖^2 : ℝ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  push_cast
  by_cases hi : i=2 <;> by_cases hj : j=2 <;> simp [hi,hj]
  rw [mul_assoc, ← Complex.star_def, hn]
  have hd : (↑‖q.2‖^2 + (ε:ℂ)^2) ≠ 0 := by exact_mod_cast hden
  field_simp
  ; push_cast; ring

lemma regularizedLog_holomorphic_psh (a : ℝ) {ε : ℝ} (he : ε ≠ 0)
    {f : Base → ℂ} {z : Base} (hf : AnalyticAt ℂ f z) (v : Base) :
    0 ≤ (∑ i, ∑ j, baseHessian (regularizedLog a ε ∘ f) z i j * v i * star (v j)).re := by
  let F : Ambient → Ambient := fun q => (q.1,1-(a:ℂ)*f q.1)
  have hF : AnalyticAt ℂ F (z,0) :=
    ((ContinuousLinearMap.fst ℂ Base ℂ).analyticAt _).prod
      (analyticAt_const.sub (analyticAt_const.mul (hf.comp ((ContinuousLinearMap.fst ℂ Base ℂ).analyticAt _))))
  have hfc : ContDiffAt ℝ 2 (regularizedLog a ε ∘ f) z :=
    ((regularizedLog_contDiff a he).contDiffAt.comp z (hf.contDiffAt.restrict_scalars ℝ)).of_le (WithTop.coe_le_coe.mpr le_top)
  have heq : regularizedFiberLog ε ∘ F = fun q : Ambient => (regularizedLog a ε ∘ f) q.1 := by
    funext q
    exact (regularizedLog_eq a ε (f q.1) he).symm
  have hh := congrArg (fun A => (hermitianValue A (v,0) (v,0)).re)
    (complexHessian_pullback ((regularizedFiberLog_contDiff he).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) hF)
  rw [heq,hermitianValue_lift_base hfc,hermitianValue_pullback] at hh
  rw [hh]
  let u := fderiv ℂ F (z,0) (v,0)
  change 0 ≤ (hermitianValue (complexHessian (regularizedFiberLog ε) (F (z,0))) u u).re
  simp only [hermitianValue,regularizedFiberLog_hessian he,Fin.sum_univ_three]
  simp only [Fin.reduceEq,ite_false,ite_true,mul_zero,zero_mul,zero_add,add_zero]
  have hu : u.2*star u.2 = (‖u.2‖^2:ℝ) := by
    rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  change 0 ≤ (((ε^2/(‖(F (z,0)).2‖^2+ε^2)^2:ℝ):ℂ)*1*1*u.2*star u.2).re
  rw [mul_one,mul_one,mul_assoc,hu]
  simp only [← Complex.ofReal_mul,Complex.ofReal_re]
  positivity

end BaseConstruction
end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseCauchyJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler8342_1 uKahler8342_2 uKahler8392_1 uKahler8392_2

open scoped ContDiff
open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder
noncomputable section

open Set Filter Topology
namespace PinchedHartogs.BaseConstruction

lemma cauchyJetConstant_pos (n : ℕ) : 0 < cauchyJetConstant n := by
  induction n with
  | zero => norm_num [cauchyJetConstant]
  | succ n ih => simp only [cauchyJetConstant]; positivity

lemma analytic_positive_jet_bound {E : Type uKahler8392_1} {F : Type uKahler8392_2} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {c : E} {R A : ℝ} (hR : 0 < R) (hA : 0 ≤ A)
    (hf : AnalyticOnNhd ℂ f (Metric.ball c R))
    (hb : ∀ x ∈ Metric.ball c R, ‖f x-f c‖ ≤ A) {n : ℕ} (hn : 0 < n) :
    ‖iteratedFDeriv ℂ n f c‖ ≤ cauchyJetConstant n*A/(R/2)^n := by
  have hs : AnalyticOnNhd ℂ (fun x => f x-f c) (Metric.ball c R) := hf.sub analyticOnNhd_const
  have hh := analytic_jet_bound (by linarith : R/2<R) (by positivity : 0 ≤ R/2) hA hs hb n c
    (Metric.mem_ball_self (by positivity : 0 < R/2))
  have he : iteratedFDeriv ℂ n (fun x => f x-f c) c=iteratedFDeriv ℂ n f c := by
    change iteratedFDeriv ℂ n (f - fun _ => f c) c = _
    rw [iteratedFDeriv_sub_apply (hf c (Metric.mem_ball_self hR)).contDiffAt contDiffAt_const,
      iteratedFDeriv_const_of_ne (by omega)]
    simp
  rw [he,show R-R/2=R/2 by ring] at hh
  exact hh

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseCompositionJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler8418_1 uKahler8418_2 uKahler8437_1 uKahler8437_2 uKahler8437_3 uKahler8458_1 uKahler8458_2

open scoped ContDiff
open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder
open Set Filter Topology
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma analytic_real_jet_norm {E : Type uKahler8418_1} {F : Type uKahler8418_2} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {x : E} (hf : AnalyticAt ℂ f x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n f x‖=‖iteratedFDeriv ℂ n f x‖ := by
  rw [← (hf.contDiffAt : ContDiffAt ℂ n f x).restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  exact ContinuousMultilinearMap.norm_restrictScalars _

lemma small_power_bound {t B : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hB : 1 ≤ B)
    {i n : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) :
    B*t ≤ (B*t^((n:ℝ)⁻¹))^i := by
  have hn : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [mul_pow,← Real.rpow_mul_natCast ht.le]
  have hex : (n:ℝ)⁻¹*(i:ℝ) ≤ 1 := by
    rw [← div_eq_inv_mul]
    exact (div_le_one hn).mpr (by exact_mod_cast hin)
  have hp : t ≤ t^((n:ℝ)⁻¹*(i:ℝ)) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ht ht1 hex
  exact mul_le_mul (by simpa using pow_le_pow_right₀ hB hi) hp ht.le (by positivity)

lemma norm_composition_jet_linear {E : Type uKahler8437_1} {F : Type uKahler8437_2} {G : Type uKahler8437_3}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : F → G} {s : Set E} (hs : IsOpen s) {x : E} (hx : x ∈ s)
    {n : ℕ} (hn : 1 ≤ n) (hf : ContDiffOn ℝ n f s) (hg : ContDiff ℝ n g)
    {B C t : ℝ} (hB : 1 ≤ B) (ht : 0 < t) (ht1 : t ≤ 1)
    (hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hbound : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ B*t) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ n.factorial*C*B^n*t := by
  have hh := norm_iteratedFDerivWithin_comp_le hg.contDiffOn hf le_rfl uniqueDiffOn_univ
    (hs.uniqueDiffOn) (mapsTo_univ f s) hx
    (C := C) (D := B*t^((n:ℝ)⁻¹))
    (by simpa only [iteratedFDerivWithin_univ] using hC)
    (fun i hi hin => by
      rw [iteratedFDerivWithin_of_isOpen i hs hx]
      exact (hbound i hi hin).trans (small_power_bound ht ht1 hB hi hin))
  rw [iteratedFDerivWithin_of_isOpen n hs hx] at hh
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [mul_pow,← Real.rpow_mul_natCast ht.le,inv_mul_cancel₀ hn0,Real.rpow_one] at hh
  exact hh.trans_eq (by ring)

lemma smooth_jet_bound_compact {E : Type uKahler8458_1} {F : Type uKahler8458_2} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F} (hg : ContDiff ℝ ∞ g)
    {s : Set E} (hs : IsCompact s) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i, i ≤ n → ∀ x ∈ s, ‖iteratedFDeriv ℝ i g x‖ ≤ C := by
  have hex (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ s, ‖iteratedFDeriv ℝ i g x‖ ≤ C := by
    have hc : Continuous (iteratedFDeriv ℝ i g) := ContDiff.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (i:ℕ∞) ≤ ⊤)) hg
    obtain ⟨C,hC⟩ := hs.bddAbove_image hc.norm.continuousOn
    exact ⟨max C 0,le_max_right _ _,fun x hx => (hC (mem_image_of_mem _ hx)).trans (le_max_left _ _)⟩
  choose C hC hbound using hex
  refine ⟨1+∑ j ∈ Finset.range (n+1), C j,?_,?_⟩
  · have := Finset.sum_nonneg (s := Finset.range (n+1)) (fun j _ => hC j)
    linarith
  · intro i hi x hx
    have hh := Finset.single_le_sum (s := Finset.range (n+1)) (fun j _ => hC j) (show i ∈ Finset.range (n+1) by simp; omega)
    exact (hbound i x hx).trans (by linarith)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseLogJetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma regularizedLog_positive_jet_bound (a : ℝ) {ε R A B : ℝ} (he : ε ≠ 0)
    (hR : 0 < R) (hA : 0 ≤ A) (hB : 0 ≤ B) {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Base → ℂ) (c : Base) (t : ℝ),
      AnalyticOnNhd ℂ f (Metric.ball c R) → ‖f c‖ ≤ A → 0 < t → t ≤ 1 →
      (∀ x ∈ Metric.ball c R, ‖f x-f c‖ ≤ B*t) →
      ‖iteratedFDeriv ℝ n (regularizedLog a ε ∘ f) c‖ ≤ C*t := by
  let radius : NNReal := ⟨A, hA⟩
  obtain ⟨C,hC,hCb⟩ := smooth_jet_bound_compact (regularizedLog_contDiff a he)
    (isCompact_closedBall (0:ℂ) (radius : ℝ)) n
  let D : ℝ := 1+∑ i ∈ Finset.range (n+1), cauchyJetConstant i*B/(R/2)^i
  have hterm (i : ℕ) : 0 ≤ cauchyJetConstant i*B/(R/2)^i := by
    exact div_nonneg (mul_nonneg (cauchyJetConstant_pos i).le hB) (by positivity)
  have hD : 1 ≤ D := by
    have hh := Finset.sum_nonneg (s := Finset.range (n+1)) (fun i _ => hterm i)
    dsimp [D]; linarith
  have hDb (i : ℕ) (hi : i ≤ n) : cauchyJetConstant i*B/(R/2)^i ≤ D := by
    have hh := Finset.single_le_sum (s := Finset.range (n+1)) (fun j _ => hterm j)
      (show i ∈ Finset.range (n+1) by simp; omega)
    dsimp [D]; linarith
  refine ⟨n.factorial*C*D^n,by positivity,?_⟩
  intro f c t hf hfc ht ht1 hb
  have hfn : ContDiffOn ℝ n f (Metric.ball c R) := (hf.contDiffOn Metric.isOpen_ball.uniqueDiffOn).restrict_scalars ℝ
  have hh := norm_composition_jet_linear Metric.isOpen_ball (Metric.mem_ball_self hR) hn hfn
    ((regularizedLog_contDiff a he).of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))) hD ht ht1
    (fun i hi => hCb i hi (f c) (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hfc))
    (fun i hi hin => ?_)
  · exact hh
  rw [analytic_real_jet_norm (hf c (Metric.mem_ball_self hR)) i]
  have hbound := analytic_positive_jet_bound hR (mul_nonneg hB ht.le) hf hb (by omega : 0 < i)
  apply hbound.trans
  calc cauchyJetConstant i*(B*t)/(R/2)^i = (cauchyJetConstant i*B/(R/2)^i)*t := by ring
       _ ≤ D*t := mul_le_mul_of_nonneg_right (hDb i hin) ht.le

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler8561_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
namespace PinchedHartogs.BaseConstruction

lemma continuous_integrable {E : Type uKahler8561_1} [NormedAddCommGroup E] {μ : Measure Sphere}
    [IsFiniteMeasure μ] {f : Sphere → E} (hf : Continuous f) : Integrable f μ := by
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseSphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler8786_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma sphereAction_preserves (U : Base ≃ₗᵢ[ℂ] Base) :
    MeasurePreserving (sphereAction U) sigma sigma := by
  have hm : MeasurePreserving (sphereAction U)
      (volume : Measure Base).toSphere (volume : Measure Base).toSphere := by
    refine ⟨(sphereAction U).measurable, ?_⟩
    apply Measure.ext
    intro s hs
    rw [Measure.map_apply (sphereAction U).measurable hs,
      (volume : Measure Base).toSphere_apply' ((sphereAction U).measurable hs),
      (volume : Measure Base).toSphere_apply' hs]
    congr 1
    have he : Ioo (0:ℝ) 1 • ((↑) '' (sphereAction U ⁻¹' s)) =
        U ⁻¹' (Ioo (0:ℝ) 1 • ((↑) '' s)) := by
      ext z
      simp only [mem_preimage, Set.mem_smul, mem_image]
      constructor
      · rintro ⟨r,hr,v,⟨ξ,hξ,rfl⟩,rfl⟩
        exact ⟨r,hr,U (ξ:Base),⟨sphereAction U ξ,hξ,rfl⟩,(realIsometry U).map_smul r ξ |>.symm⟩
      · rintro ⟨r,hr,v,⟨ξ,hξ,rfl⟩,hz⟩
        refine ⟨r,hr,U.symm (ξ:Base),⟨(sphereAction U).symm ξ, ?_, rfl⟩,?_⟩
        · simpa using hξ
        · apply U.injective
          rw [← hz]
          calc
            U (r • U.symm (ξ:Base)) = r • U (U.symm (ξ:Base)) := (realIsometry U).map_smul _ _
            _ = _ := by rw [U.apply_symm_apply]
    rw [he]
    exact (realIsometry U).measurePreserving.measure_preimage_emb
      U.toHomeomorph.measurableEmbedding _
  exact hm.smul_measure _

lemma sigma_integral_unitary {E : Type uKahler8786_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Base ≃ₗᵢ[ℂ] Base) (f : Sphere → E) :
    (∫ ξ, f (sphereAction U ξ) ∂sigma) = ∫ ξ, f ξ ∂sigma :=
  (sphereAction_preserves U).integral_comp (sphereAction U).measurableEmbedding f

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseRadialMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma radialRI (ξ : Sphere) : radialR ξ^2+radialJ ξ^2 = radialU ξ*radialV ξ := by
  simp [radialR,radialJ,radialU,radialV,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,
    Complex.conj_re,Complex.conj_im]
  ring

lemma radialJ_continuous : Continuous radialJ := by
  exact Complex.continuous_im.comp (((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val).mul
    (((EuclideanSpace.proj 1).continuous.comp continuous_subtype_val).star))

lemma radial_phase_square (n : ℕ) :
    (∫ ξ, radialU ξ^n * radialR ξ^2 ∂sigma) =
      ∫ ξ, radialU ξ^n * radialJ ξ^2 ∂sigma := by
  have hi := sigma_integral_unitary (diagIsometry Complex.I 1 (by simp) (by simp))
    (fun ξ => radialU ξ^n * radialR ξ^2)
  have he : ∀ ξ : Sphere,
      radialU (sphereAction (diagIsometry Complex.I 1 (by simp) (by simp)) ξ)^n *
      radialR (sphereAction (diagIsometry Complex.I 1 (by simp) (by simp)) ξ)^2 =
      radialU ξ^n*radialJ ξ^2 := by
    intro ξ
    simp [radialU,radialR,radialJ,Complex.normSq_mul,mul_assoc]
    left
    ring
  simpa only [he] using hi.symm

lemma radial_square_integral (n : ℕ) :
    2*(∫ ξ, radialU ξ^n*radialR ξ^2 ∂sigma) =
      ∫ ξ, radialU ξ^(n+1)*radialV ξ ∂sigma := by
  have hR : Integrable (fun ξ => radialU ξ^n*radialR ξ^2) sigma :=
    continuous_integrable ((radialU_continuous.pow n).mul (radialR_continuous.pow 2))
  have hJ : Integrable (fun ξ => radialU ξ^n*radialJ ξ^2) sigma :=
    continuous_integrable ((radialU_continuous.pow n).mul (radialJ_continuous.pow 2))
  calc
    _ = (∫ ξ, radialU ξ^n*radialR ξ^2 ∂sigma) +
        (∫ ξ, radialU ξ^n*radialJ ξ^2 ∂sigma) := by rw [← radial_phase_square n]; ring
    _ = ∫ ξ, radialU ξ^n*radialR ξ^2 + radialU ξ^n*radialJ ξ^2 ∂sigma :=
      (integral_add hR hJ).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [← mul_add,radialRI,pow_succ]
      ring

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseRadialMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma hasDerivAt_sphere_integral {F F' : ℝ → Sphere → ℝ}
    (hF : Continuous (fun p : ℝ × Sphere => F p.1 p.2))
    (hF' : Continuous (fun p : ℝ × Sphere => F' p.1 p.2))
    (hd : ∀ t ξ, HasDerivAt (fun r => F r ξ) (F' t ξ) t) (t : ℝ) :
    HasDerivAt (fun r => ∫ ξ, F r ξ ∂sigma) (∫ ξ, F' t ξ ∂sigma) t := by
  obtain ⟨C,hC⟩ := ((isCompact_closedBall t 1).prod (isCompact_univ : IsCompact (univ : Set Sphere))).bddAbove_image hF'.norm.continuousOn
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := sigma)
    (F := F) (F' := F') (bound := fun _ => C) (s := Metric.ball t 1)
    (Metric.ball_mem_nhds t (by norm_num)) ?_ ?_ ?_ ?_ (integrable_const C) ?_).2
  · exact Eventually.of_forall (fun r => (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact continuous_integrable (hF.comp (continuous_const.prodMk continuous_id))
  · exact (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [] with ξ r hr
    exact hC (mem_image_of_mem (fun p : ℝ × Sphere => ‖F' p.1 p.2‖)
      (show (r,ξ) ∈ Metric.closedBall t 1 ×ˢ (univ : Set Sphere) from ⟨Metric.ball_subset_closedBall hr,mem_univ _⟩))
  · exact Eventually.of_forall (fun ξ r _ => hd r ξ)

private lemma rotA_deriv (u v r t : ℝ) : HasDerivAt (rotA u v r) (rotA' u v r t) t := by
  convert (((Real.hasDerivAt_cos t).pow 2 |>.mul_const u).add
    ((Real.hasDerivAt_sin t).pow 2 |>.mul_const v)).add
    ((((Real.hasDerivAt_cos t).const_mul 2).mul (Real.hasDerivAt_sin t)).mul_const r) using 1 <;> try rfl
  all_goals
    (try dsimp [rotA,rotA']); ring

private lemma rotA'_deriv (u v r t : ℝ) : HasDerivAt (rotA' u v r) (rotA'' u v r t) t := by
  convert (((((Real.hasDerivAt_cos t).const_mul 2).mul (Real.hasDerivAt_sin t)).mul_const (v-u)).add
    (((((Real.hasDerivAt_cos t).pow 2).sub ((Real.hasDerivAt_sin t).pow 2)).const_mul 2).mul_const r)) using 1 <;> try rfl
  all_goals
    (try dsimp [rotA',rotA'']); ring

private lemma rotated_radialU (t : ℝ) (ξ : Sphere) :
    radialU (sphereAction (rotationIsometry t) ξ) = rotA (radialU ξ) (radialV ξ) (radialR ξ) t := by
  simp only [radialU,radialV,radialR,rotationIsometry,rotA,sphereAction_coe,suIsometry_zero,Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

private lemma rotF_deriv (n : ℕ) (t : ℝ) (ξ : Sphere) :
    HasDerivAt (fun s => rotF n s ξ) (rotF' n t ξ) t := by
  convert (rotA_deriv (radialU ξ) (radialV ξ) (radialR ξ) t).pow (n+2) using 1 <;> try rfl
  all_goals
    (try simp only [rotF',Nat.cast_add,Nat.cast_ofNat]); try rfl

private lemma rotF'_deriv (n : ℕ) (t : ℝ) (ξ : Sphere) :
    HasDerivAt (fun s => rotF' n s ξ) (rotF'' n t ξ) t := by
  convert ((((rotA_deriv (radialU ξ) (radialV ξ) (radialR ξ) t).pow (n+1)).const_mul (n+2:ℝ)).mul
    (rotA'_deriv (radialU ξ) (radialV ξ) (radialR ξ) t)) using 1 <;> try rfl
  all_goals
    (try simp only [rotF'',Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,Pi.pow_apply]); ring

attribute [local fun_prop] radialU_continuous radialV_continuous radialR_continuous

private lemma rotF_continuous (n : ℕ) : Continuous (fun p : ℝ × Sphere => rotF n p.1 p.2) := by
  unfold rotF rotA
  fun_prop
private lemma rotF'_continuous (n : ℕ) : Continuous (fun p : ℝ × Sphere => rotF' n p.1 p.2) := by
  unfold rotF' rotA rotA'
  fun_prop
private lemma rotF''_continuous (n : ℕ) : Continuous (fun p : ℝ × Sphere => rotF'' n p.1 p.2) := by
  unfold rotF'' rotA rotA' rotA''
  fun_prop

lemma radial_moment_recurrence (n : ℕ) :
    (n+3 : ℝ)*(∫ ξ, radialU ξ^(n+2) ∂sigma) =
      (n+2 : ℝ)*(∫ ξ, radialU ξ^(n+1) ∂sigma) := by
  have hconst : ∀ t, (∫ ξ, rotF n t ξ ∂sigma) = ∫ ξ, radialU ξ^(n+2) ∂sigma := by
    intro t
    simpa only [rotated_radialU,rotF] using sigma_integral_unitary (rotationIsometry t)
      (fun ξ => radialU ξ^(n+2))
  have hzero : ∀ t, (∫ ξ, rotF' n t ξ ∂sigma) = 0 := by
    intro t
    have hc : HasDerivAt (fun s => ∫ ξ, rotF n s ξ ∂sigma) 0 t := by
      simpa only [hconst] using hasDerivAt_const t (∫ ξ, radialU ξ^(n+2) ∂sigma)
    exact (hasDerivAt_sphere_integral (rotF_continuous n) (rotF'_continuous n) (rotF_deriv n) t).unique hc
  have hsecond : (∫ ξ, rotF'' n 0 ξ ∂sigma) = 0 := by
    have hc : HasDerivAt (fun s => ∫ ξ, rotF' n s ξ ∂sigma) 0 0 := by
      simpa only [hzero] using hasDerivAt_const (0:ℝ) (0:ℝ)
    exact (hasDerivAt_sphere_integral (rotF'_continuous n) (rotF''_continuous n) (rotF'_deriv n) 0).unique hc
  have he : ∀ ξ : Sphere, rotF'' n 0 ξ = (n+2:ℝ)*
      (4*(n+1:ℝ)*(radialU ξ^n*radialR ξ^2)+
        2*(radialU ξ^(n+1)*radialV ξ)-2*radialU ξ^(n+2)) := by
    intro ξ
    simp only [rotF'',rotA,rotA',rotA'',Real.cos_zero,Real.sin_zero,zero_mul,mul_zero,one_pow,one_mul,add_zero,sub_zero,pow_succ]
    ring
  simp_rw [he] at hsecond
  have hR : Integrable (fun ξ => radialU ξ^n*radialR ξ^2) sigma :=
    continuous_integrable ((radialU_continuous.pow n).mul (radialR_continuous.pow 2))
  have hUV : Integrable (fun ξ => radialU ξ^(n+1)*radialV ξ) sigma :=
    continuous_integrable ((radialU_continuous.pow (n+1)).mul radialV_continuous)
  have hU : Integrable (fun ξ => radialU ξ^(n+2)) sigma := continuous_integrable (radialU_continuous.pow (n+2))
  have hparts := integral_sub (μ := sigma)
    (f := fun ξ => 4*(n+1:ℝ)*(radialU ξ^n*radialR ξ^2)+2*(radialU ξ^(n+1)*radialV ξ))
    (g := fun ξ => 2*radialU ξ^(n+2))
    ((hR.const_mul (4*(n+1:ℝ))).add (hUV.const_mul 2)) (hU.const_mul 2)
  have hparts' := integral_add (μ := sigma)
    (f := fun ξ => 4*(n+1:ℝ)*(radialU ξ^n*radialR ξ^2))
    (g := fun ξ => 2*(radialU ξ^(n+1)*radialV ξ))
    (hR.const_mul (4*(n+1:ℝ))) (hUV.const_mul 2)
  rw [integral_const_mul,hparts,hparts',integral_const_mul,integral_const_mul,integral_const_mul] at hsecond
  have huv : (∫ ξ, radialU ξ^(n+1)*radialV ξ ∂sigma) =
      (∫ ξ, radialU ξ^(n+1) ∂sigma)-(∫ ξ, radialU ξ^(n+2) ∂sigma) := by
    rw [← integral_sub (f := fun ξ => radialU ξ^(n+1)) (g := fun ξ => radialU ξ^(n+2))
      (continuous_integrable (radialU_continuous.pow (n+1))) hU]
    apply integral_congr_ae
    filter_upwards [] with ξ
    have hv : radialV ξ = 1-radialU ξ := by linarith [radialUV ξ]
    rw [hv,show n+2 = (n+1)+1 from rfl,pow_succ]
    ring
  have hs := radial_square_integral n
  rw [huv] at hs hsecond
  have hn : (0:ℝ) < n+2 := by positivity
  have hh := (mul_eq_zero.mp hsecond).resolve_left hn.ne'
  linear_combination (n+1:ℝ)*hs-hh/2

lemma radial_first_moment : (∫ ξ, radialU ξ ∂sigma) = 1/2 := by
  have hi := sigma_integral_unitary (suIsometry 0 1 (by simp)) radialU
  have he : ∀ ξ : Sphere, radialU (sphereAction (suIsometry 0 1 (by simp)) ξ) = radialV ξ := by
    intro ξ
    simp [radialU,radialV]
  simp_rw [he] at hi
  have huv : (∫ ξ, radialU ξ ∂sigma)+(∫ ξ, radialV ξ ∂sigma) = 1 := by
    rw [← integral_add (continuous_integrable radialU_continuous) (continuous_integrable radialV_continuous)]
    simp_rw [radialUV]
    simp
  linarith

lemma radial_moment (n : ℕ) : (∫ ξ, radialU ξ^n ∂sigma) = 1/(n+1:ℝ) := by
  rcases n with _|n
  · simp
  induction n with
  | zero => simpa only [Nat.zero_add,Nat.cast_one,pow_one,show (1:ℝ)+1 = 2 by norm_num] using radial_first_moment
  | succ n ih =>
    have hr := radial_moment_recurrence n
    rw [ih] at hr
    have hn : (n+2:ℝ) ≠ 0 := by positivity
    have hn' : (n+3:ℝ) ≠ 0 := by positivity
    simp only [Nat.cast_add,Nat.cast_one] at *
    field_simp at hr ⊢
    nlinarith

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseRadialLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler9159_1 uKahler9161_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma radialUnit_continuous : Continuous radialUnit := radialU_continuous.subtype_mk _

lemma unit_moment (n : ℕ) : (∫ t : unitInterval, (t:ℝ)^n) = 1/(n+1:ℝ) := by
  rw [unitInterval.volume_def,integral_subtype_comap measurableSet_Icc (fun t : ℝ => t^n)]
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),integral_pow]
  simp

lemma radial_polynomial_integral (p : Polynomial ℝ) :
    (∫ ξ, p.eval (radialU ξ) ∂sigma) = ∫ t : unitInterval, p.eval (t:ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    rw [integral_add,integral_add,hp,hq]
    all_goals first
      | exact continuous_integrable (p.continuous.comp radialU_continuous)
      | exact continuous_integrable (q.continuous.comp radialU_continuous)
      | exact (p.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      | exact (q.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  | monomial n a =>
    simp only [Polynomial.eval_monomial,integral_const_mul,radial_moment,unit_moment]

lemma radial_continuous_integral (f : C(unitInterval,ℝ)) :
    (∫ ξ, f (radialUnit ξ) ∂sigma) = ∫ t : unitInterval, f t := by
  let L := integralCM sigma radialUnit radialUnit_continuous
  let R := integralCM (volume : Measure unitInterval) id continuous_id
  have hc : IsClosed {f : C(unitInterval,ℝ) | L f = R f} := isClosed_eq L.continuous R.continuous
  have hpoly : (polynomialFunctions (Icc (0:ℝ) 1) : Set C(unitInterval,ℝ)) ⊆ {f | L f = R f} := by
    rw [polynomialFunctions_coe]
    rintro _ ⟨p,rfl⟩
    exact radial_polynomial_integral p
  have hcl := hc.closure_subset_iff.mpr hpoly
  have hd : closure (polynomialFunctions (Icc (0:ℝ) 1) : Set C(unitInterval,ℝ)) = univ := by
    simpa only [Subalgebra.topologicalClosure_coe,show ((⊤ : Subalgebra ℝ C(unitInterval,ℝ)) : Set C(unitInterval,ℝ)) = univ from rfl] using
      congrArg (fun A : Subalgebra ℝ C(unitInterval,ℝ) => (A : Set C(unitInterval,ℝ)))
        (polynomialFunctions.topologicalClosure (Icc (0:ℝ) 1))
  exact hcl (by rw [hd]; trivial)

lemma radial_law : Measure.map radialUnit sigma = (volume : Measure unitInterval) := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_map (f := fun x => f x) radialUnit_continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  exact radial_continuous_integral f.toContinuousMap

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma bloch_continuous : Continuous bloch := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact radialU_continuous
  · exact radialR_continuous
  · exact radialJ_continuous

lemma bracket_coordinates (z p : Base) : bracket z p = z 0*star (p 0)+z 1*star (p 1) := by
  simp [bracket,Fin.sum_univ_two,inner]

lemma bracket_radial_identity (ξ p : Sphere) :
    ‖bracket (ξ:Base) (p:Base)‖^2 = radialU ξ*radialU p+radialV ξ*radialV p+
      2*(radialR ξ*radialR p+radialJ ξ*radialJ p) := by
  rw [← Complex.normSq_eq_norm_sq,bracket_coordinates]
  simp only [radialU,radialV,radialR,radialJ,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

lemma bloch_dist_sq (ξ p : Sphere) :
    dist (bloch ξ) (bloch p)^2 = 1-‖bracket (ξ:Base) (p:Base)‖^2 := by
  rw [dist_eq_norm,EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three,PiLp.sub_apply]
  change |radialU ξ-radialU p|^2+|radialR ξ-radialR p|^2+|radialJ ξ-radialJ p|^2 = _
  simp only [sq_abs]
  rw [bracket_radial_identity]
  have hvξ : radialV ξ = 1-radialU ξ := by linarith [radialUV ξ]
  have hvp : radialV p = 1-radialU p := by linarith [radialUV p]
  have hξ := radialRI ξ
  have hp := radialRI p
  rw [hvξ] at hξ ⊢
  rw [hvp] at hp ⊢
  linarith

lemma projectiveDistance_eq_dist (ξ p : Sphere) : projectiveDistance ξ p = dist (bloch ξ) (bloch p) := by
  rw [projectiveDistance,← bloch_dist_sq,Real.sqrt_sq (dist_nonneg)]

lemma projectiveDistance_triangle (ξ p q : Sphere) :
    projectiveDistance ξ q ≤ projectiveDistance ξ p+projectiveDistance p q := by
  simp only [projectiveDistance_eq_dist]
  exact dist_triangle _ _ _

lemma projectiveDistance_nonneg (ξ p : Sphere) : 0 ≤ projectiveDistance ξ p := Real.sqrt_nonneg _
lemma projectiveDistance_symm (ξ p : Sphere) : projectiveDistance ξ p = projectiveDistance p ξ := by
  simp only [projectiveDistance_eq_dist,dist_comm]

lemma projectiveDistance_continuous (p : Sphere) : Continuous (fun ξ => projectiveDistance ξ p) := by
  simpa only [projectiveDistance_eq_dist] using bloch_continuous.dist continuous_const

lemma projectiveDistance_sq (ξ p : Sphere) : projectiveDistance ξ p^2 = 1-‖bracket (ξ:Base) (p:Base)‖^2 := by
  rw [projectiveDistance_eq_dist,bloch_dist_sq]

lemma adaptedIsometry_zero (p : Sphere) (z : Base) : adaptedIsometry p z 0 = bracket z (p:Base) := by
  simp only [adaptedIsometry,suIsometry_zero,bracket_coordinates]
  ring

lemma adapted_radialU (ξ p : Sphere) : radialU (sphereAction (adaptedIsometry p) ξ) = ‖bracket (ξ:Base) (p:Base)‖^2 := by
  simp only [radialU,sphereAction_coe,adaptedIsometry_zero,Complex.normSq_eq_norm_sq]

lemma projective_cap_measure (p : Sphere) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    sigma {ξ | projectiveDistance ξ p < s} = ENNReal.ofReal (s^2) := by
  let a : unitInterval := ⟨1-s^2,by constructor <;> nlinarith⟩
  have he : {ξ | projectiveDistance ξ p < s} =
      (sphereAction (adaptedIsometry p)) ⁻¹' (radialUnit ⁻¹' Ioi a) := by
    ext ξ
    change projectiveDistance ξ p < s ↔ (a:ℝ) < radialU (sphereAction (adaptedIsometry p) ξ)
    rw [adapted_radialU]
    dsimp [a]
    have hp := projectiveDistance_sq ξ p
    have hnn := projectiveDistance_nonneg ξ p
    constructor <;> intro h <;> nlinarith
  rw [he,(sphereAction_preserves (adaptedIsometry p)).measure_preimage_emb (sphereAction _).measurableEmbedding,
    ← Measure.map_apply radialUnit_continuous.measurable measurableSet_Ioi,radial_law,unitInterval.volume_Ioi]
  congr 1
  dsimp [a]
  ring

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma projectiveCap_measurable (p : Sphere) (s : ℝ) : MeasurableSet (projectiveCap p s) :=
  (projectiveDistance_continuous p).measurable measurableSet_Iio

lemma projectiveCap_real (p : Sphere) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    sigma.real (projectiveCap p s) = s^2 := by
  rw [measureReal_def,projectiveCap,projective_cap_measure p hs hs1,ENNReal.toReal_ofReal (sq_nonneg _)]

lemma separated_caps_disjoint {ρ : ℝ} {P : Finset Sphere} (hP : ProjectivelySeparated ρ P) :
    (P : Set Sphere).PairwiseDisjoint (fun p => projectiveCap p (ρ/2)) := by
  intro p hp q hq hpq
  apply disjoint_left.mpr
  intro ξ hξp hξq
  have ht := projectiveDistance_triangle p ξ q
  rw [projectiveDistance_symm p ξ] at ht
  have hs := hP p hp q hq hpq
  change projectiveDistance ξ p < ρ/2 at hξp
  change projectiveDistance ξ q < ρ/2 at hξq
  linarith

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma separated_local_count {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : 1 ≤ k)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P)
    (ξ : Sphere) {u : ℝ} (hu : 0 ≤ u) :
    ((P.filter (fun p => projectiveDistance ξ p < u/Real.sqrt k)).card : ℝ) ≤ 9*(u+1/3)^2 := by
  classical
  let S := P.filter (fun p => projectiveDistance ξ p < u/Real.sqrt k)
  have hk0 : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hs : 1 ≤ Real.sqrt (k:ℝ) := (Real.one_le_sqrt).mpr (by exact_mod_cast hk)
  have hs0 : 0 < Real.sqrt (k:ℝ) := lt_of_lt_of_le zero_lt_one hs
  let r := 1/(3*Real.sqrt (k:ℝ))
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by dsimp [r]; apply (div_le_one (by positivity)).mpr; linarith
  have hsep : ProjectivelySeparated (2*r) S := by
    intro p hp q hq hpq
    have ht := hP p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 hpq
    have he : 2*r ≤ D/Real.sqrt (k:ℝ) := by dsimp [r]; field_simp; linarith
    exact he.trans ht
  have hd := separated_caps_disjoint hsep
  have he : 2*r/2 = r := by ring
  rw [he] at hd
  have hm : sigma.real (⋃ p ∈ S, projectiveCap p r) = (S.card:ℝ)*r^2 := by
    rw [measureReal_biUnion_finset hd (fun p _ => projectiveCap_measurable p r)]
    simp only [projectiveCap_real _ hr.le hr1,Finset.sum_const,nsmul_eq_mul]
  have hsmall : (⋃ p ∈ S, projectiveCap p r) ⊆ projectiveCap ξ ((u+1/3)/Real.sqrt (k:ℝ)) := by
    intro η hη
    obtain ⟨p,hp,hηp⟩ := mem_iUnion₂.mp hη
    have hp' := (Finset.mem_filter.mp hp).2
    change projectiveDistance η p < r at hηp
    change projectiveDistance η ξ < _
    have ht := projectiveDistance_triangle η p ξ
    rw [projectiveDistance_symm p ξ] at ht
    dsimp [r] at hηp
    have he : u/Real.sqrt (k:ℝ)+1/(3*Real.sqrt (k:ℝ)) = (u+1/3)/Real.sqrt (k:ℝ) := by field_simp
    linarith
  have hb : (S.card:ℝ)*r^2 ≤ ((u+1/3)/Real.sqrt (k:ℝ))^2 := by
    by_cases hh : (u+1/3)/Real.sqrt (k:ℝ) ≤ 1
    · rw [← hm]
      simpa only [projectiveCap_real _ (by positivity : 0 ≤ (u+1/3)/Real.sqrt (k:ℝ)) hh] using measureReal_mono (μ := sigma) hsmall
    · have hv := measureReal_mono (μ := sigma) (subset_univ (⋃ p ∈ S, projectiveCap p r))
      rw [hm] at hv
      have hv1 : sigma.real univ = 1 := by simp [measureReal_def]
      rw [hv1] at hv
      have hh' : 1 < (u+1/3)/Real.sqrt (k:ℝ) := lt_of_not_ge hh
      nlinarith
  change (S.card:ℝ) ≤ _
  dsimp [r] at hb
  have hsq := Real.sq_sqrt hk0.le
  field_simp at hb
  linarith

lemma peak_exponential_bound (ξ p : Sphere) (k : ℕ) :
    ‖bracket (ξ:Base) (p:Base)‖^k ≤ Real.exp (-(k:ℝ)*projectiveDistance ξ p^2/2) := by
  have hd := projectiveDistance_sq ξ p
  have he := Real.one_sub_le_exp_neg (projectiveDistance ξ p^2)
  have hp := pow_le_pow_left₀ (sq_nonneg ‖bracket (ξ:Base) (p:Base)‖) (show ‖bracket (ξ:Base) (p:Base)‖^2 ≤ Real.exp (-projectiveDistance ξ p^2) by linarith) k
  rw [← Real.exp_nat_mul] at hp
  have he' : Real.exp (-(k:ℝ)*projectiveDistance ξ p^2/2)^2 = Real.exp ((k:ℝ)*(-projectiveDistance ξ p^2)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hp' : (‖bracket (ξ:Base) (p:Base)‖^k)^2 ≤ Real.exp (-(k:ℝ)*projectiveDistance ξ p^2/2)^2 := by simpa only [he',← pow_mul,mul_comm k 2] using hp
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hp'

lemma gaussian_sequence_summable : Summable (fun n : ℕ => 9*((n:ℝ)+2)^2*Real.exp (-(n:ℝ)^2/4)) := by
  have he : ‖Real.exp (-1:ℝ)‖ < 1 := by rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]; exact Real.exp_lt_one_iff.mpr (by norm_num)
  have h0 := summable_geometric_of_norm_lt_one he
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 he
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 he
  have hsum : Summable (fun n : ℕ => 9*Real.exp 1*((n:ℝ)+2)^2*Real.exp (-(n:ℝ))) := by
    apply Summable.congr (((h2.add (h1.mul_left 4)).add (h0.mul_left 4)).mul_left (9*Real.exp 1))
    intro n
    rw [← Real.exp_nat_mul]
    simp only [mul_neg,mul_one]
    ring
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hsum
  intro n
  have hn : -(n:ℝ)^2/4 ≤ 1-(n:ℝ) := by linarith [sq_nonneg ((n:ℝ)-2)]
  have hp := Real.exp_le_exp.mpr hn
  rw [Real.exp_sub] at hp
  have heq : Real.exp 1/Real.exp (n:ℝ) = Real.exp 1*Real.exp (-(n:ℝ)) := by rw [Real.exp_neg,div_eq_mul_inv]
  rw [heq] at hp
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 9*((n:ℝ)+2)^2 by positivity)
  linarith

lemma gaussianConstant_pos : 0 < gaussianConstant := by
  have h := gaussian_sequence_summable.le_tsum 0 (fun n hn => by positivity)
  norm_num at h
  exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 36) h

lemma gaussian_full_sum {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : 1 ≤ k)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P) (ξ : Sphere) :
    (∑ p ∈ P, Real.exp (-(Real.sqrt k*projectiveDistance ξ p)^2/4)) ≤ gaussianConstant := by
  classical
  let t : Sphere → ℝ := fun p => Real.sqrt k*projectiveDistance ξ p
  let f : Sphere → ℕ := fun p => ⌊t p⌋₊
  let N := P.sup f+1
  have hmap : ∀ p ∈ P, f p ∈ Finset.range N := by
    intro p hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hp))
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun p => Real.exp (-(t p)^2/4))]
  have hs0 : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < k))
  have hbin : ∀ n : ℕ, (∑ p ∈ P with f p = n, Real.exp (-(t p)^2/4)) ≤
      9*((n:ℝ)+2)^2*Real.exp (-(n:ℝ)^2/4) := by
    intro n
    have hsub : P.filter (fun p => f p=n) ⊆ P.filter (fun p => projectiveDistance ξ p < ((n:ℝ)+1)/Real.sqrt k) := by
      intro p hp
      obtain ⟨hpP,hpn⟩ := Finset.mem_filter.mp hp
      refine Finset.mem_filter.mpr ⟨hpP,?_⟩
      apply (lt_div_iff₀ hs0).mpr
      have hn := Nat.lt_floor_add_one (t p)
      change t p < (f p:ℝ)+1 at hn
      rw [hpn] at hn
      simpa only [t,mul_comm] using hn
    have hc := (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card hsub)
    have hcount := separated_local_count hD hk hP ξ (show 0 ≤ (n:ℝ)+1 by positivity)
    have hcount' : ((P.filter (fun p => f p=n)).card:ℝ) ≤ 9*((n:ℝ)+2)^2 := by
      have hc' := hc.trans hcount
      linarith [show (0:ℝ) ≤ n by positivity]
    calc
      _ ≤ ∑ p ∈ P with f p=n, Real.exp (-(n:ℝ)^2/4) := by
        apply Finset.sum_le_sum
        intro p hp
        have hn := Nat.floor_le (show 0 ≤ t p from mul_nonneg hs0.le (projectiveDistance_nonneg ξ p))
        change (f p:ℝ) ≤ t p at hn
        rw [(Finset.mem_filter.mp hp).2] at hn
        apply Real.exp_le_exp.mpr
        nlinarith [show (0:ℝ) ≤ n by positivity]
      _ = ((P.filter (fun p => f p=n)).card:ℝ)*Real.exp (-(n:ℝ)^2/4) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcount' (Real.exp_pos _).le
  exact (Finset.sum_le_sum (fun n _ => hbin n)).trans
    (gaussian_sequence_summable.sum_le_tsum _ (fun n hn => by positivity))

lemma peak_gaussian {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : 1 ≤ k)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P)
    (ξ : Sphere) {u : ℝ} (hu : 0 ≤ u) :
    (∑ p ∈ P with u ≤ Real.sqrt k*projectiveDistance ξ p, ‖bracket (ξ:Base) (p:Base)‖^k)
      ≤ gaussianConstant*Real.exp (-u^2/4) := by
  classical
  have hk0 : (0:ℝ) ≤ k := by positivity
  have hs := Real.sq_sqrt hk0
  let S := P.filter (fun p => u ≤ Real.sqrt k*projectiveDistance ξ p)
  have hp : ∀ p ∈ S, ‖bracket (ξ:Base) (p:Base)‖^k ≤
      Real.exp (-u^2/4)*Real.exp (-(Real.sqrt k*projectiveDistance ξ p)^2/4) := by
    intro p hp
    apply (peak_exponential_bound ξ p k).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ht := (Finset.mem_filter.mp hp).2
    have hz : 0 ≤ Real.sqrt k*projectiveDistance ξ p := mul_nonneg (Real.sqrt_nonneg _) (projectiveDistance_nonneg _ _)
    have he : (Real.sqrt k*projectiveDistance ξ p)^2 = (k:ℝ)*projectiveDistance ξ p^2 := by rw [mul_pow,hs]
    nlinarith
  calc
    _ ≤ ∑ p ∈ S, Real.exp (-u^2/4)*Real.exp (-(Real.sqrt k*projectiveDistance ξ p)^2/4) := Finset.sum_le_sum hp
    _ = Real.exp (-u^2/4)*(∑ p ∈ S, Real.exp (-(Real.sqrt k*projectiveDistance ξ p)^2/4)) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-u^2/4)*(∑ p ∈ P, Real.exp (-(Real.sqrt k*projectiveDistance ξ p)^2/4)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun p hp hn => (Real.exp_pos _).le)
    _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left (gaussian_full_sum hD hk hP ξ) (Real.exp_pos (-u^2/4)).le

lemma peak_sphere_bound {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : 1 ≤ k)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P) (ξ : Sphere) :
    ‖peakPolynomial P k (ξ:Base)‖ ≤ gaussianConstant := by
  classical
  have h := peak_gaussian hD hk hP ξ (u := 0) le_rfl
  have hn : ∀ p : Sphere, 0 ≤ Real.sqrt k*projectiveDistance ξ p := fun p => mul_nonneg (Real.sqrt_nonneg _) (projectiveDistance_nonneg _ _)
  simp only [hn,Finset.filter_true,zero_pow (by norm_num : (2:ℕ) ≠ 0),neg_zero,zero_div,Real.exp_zero,mul_one] at h
  apply (norm_sum_le _ _).trans
  simpa only [norm_pow] using h

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePeakBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma peak_global_bound {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : 1 ≤ k)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P) (z : Base) :
    ‖peakPolynomial P k z‖ ≤ gaussianConstant*‖z‖^k := by
  by_cases hz : z=0
  · subst z
    simp [peakPolynomial_zero P (by omega : k ≠ 0),show k ≠ 0 by omega]
  have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let ξ : Sphere := ⟨(‖z‖:ℂ)⁻¹ • z, by
    simp only [Metric.mem_sphere,dist_zero_right,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_norm]
    field_simp⟩
  have he : (‖z‖:ℂ) • (ξ:Base) = z := by
    exact smul_inv_smul₀ (by exact_mod_cast hzn : (‖z‖:ℂ) ≠ 0) z
  rw [← he,peakPolynomial_homogeneous,norm_mul,norm_pow]
  have hh := peak_sphere_bound hD hk hP ξ
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ ‖(‖z‖:ℂ)‖^k by positivity)
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_norm,he,mul_comm] using hm

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseChartScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma chart_small_ball {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {z : Base} (hz : ‖z‖ < (1/32:ℝ)) :
    1/2 ≤ ‖1+(r:ℂ)*z 0‖ ∧ ‖1+(r:ℂ)*z 0‖ ≤ 2 := by
  have hz0 := PiLp.norm_apply_le (p := (2:ENNReal)) z 0
  have hm : ‖(r:ℂ)*z 0‖ ≤ 1/32 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]
    have := norm_nonneg (z 0)
    nlinarith
  have hupper := norm_add_le (1:ℂ) ((r:ℂ)*z 0)
  have hlower := norm_add_le (1+(r:ℂ)*z 0) (-((r:ℂ)*z 0))
  simp only [norm_one] at hupper
  simp only [add_neg_cancel_right,norm_one,norm_neg] at hlower
  constructor <;> linarith

lemma chart_norm_deficit {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) {z : Base} (hz : ‖z‖ < (1/32:ℝ)) :
    ‖centeredChart r U z‖ ≤ 1-(1-r)/16 := by
  have hzb : z ∈ ball := by change ‖z‖ < 1; linarith
  have hd := centeredChart_den_ne_zero hr hr1 hzb
  have he := centeredChart_norm_identity hr hr1 U z hd
  have hnorm : ‖centeredChart r U z‖ < 1 := centeredChart_mapsTo hr hr1 U hzb
  have hden := chart_small_ball hr hr1 hz
  have hsqden : ‖1+(r:ℂ)*z 0‖^2 ≤ 4 := by nlinarith [norm_nonneg (1+(r:ℂ)*z 0)]
  have hnum : (1-r)/2 ≤ (1-r^2)*(1-‖z‖^2) := by
    have hn : ‖z‖^2 ≤ 1/2 := by nlinarith [norm_nonneg z]
    have hrr : 1-r ≤ 1-r^2 := by nlinarith
    nlinarith
  have hdiv : (1-r)/8 ≤ (1-r^2)*(1-‖z‖^2)/‖1+(r:ℂ)*z 0‖^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < ‖1+(r:ℂ)*z 0‖))).2
    nlinarith
  rw [← he] at hdiv
  nlinarith [norm_nonneg (centeredChart r U z)]

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseLocalSmoothSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler10013_1 uKahler10013_2 uKahler10035_1 uKahler10035_2 uKahler9999_1 uKahler9999_2

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma local_jet_series_derivative {E : Type uKahler9999_1} {F : Type uKahler9999_2} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℕ → E → F} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    {s : Set E} (hs : IsOpen s) (hc : IsPreconnected s) {x : E} (hx : x ∈ s)
    {v : ℕ → ℕ → ℝ} (hv : ∀ n, Summable (v n))
    (hb : ∀ n j y, y ∈ s → ‖iteratedFDeriv ℝ n (f j) y‖ ≤ v n j) (n : ℕ) :
    HasFDerivAt (fun y => ∑' j, iteratedFDeriv ℝ n (f j) y)
      (∑' j, fderiv ℝ (iteratedFDeriv ℝ n (f j)) x) x := by
  apply hasFDerivAt_tsum_of_isPreconnected (hv (n+1)) hs hc
    (fun j y _ => ((hf j).differentiable_iteratedFDeriv (by exact_mod_cast (ENat.natCast_lt_top n))).differentiableAt.hasFDerivAt)
    (fun j y hy => ?_) hx
    (Summable.of_norm_bounded (hv n) (fun j => hb n j x hx)) hx
  simpa only [norm_fderiv_iteratedFDeriv] using hb (n+1) j y hy

lemma local_iteratedFDeriv_tsum {E : Type uKahler10013_1} {F : Type uKahler10013_2} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℕ → E → F} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    {s : Set E} (hs : IsOpen s) (hc : IsPreconnected s)
    {v : ℕ → ℕ → ℝ} (hv : ∀ n, Summable (v n))
    (hb : ∀ n j y, y ∈ s → ‖iteratedFDeriv ℝ n (f j) y‖ ≤ v n j) (n : ℕ) :
    EqOn (iteratedFDeriv ℝ n (fun y => ∑' j, f j y))
      (fun y => ∑' j, iteratedFDeriv ℝ n (f j) y) s := by
  induction n with
  | zero =>
    intro x hx
    simp_rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.map_tsum
  | succ n ih =>
    intro x hx
    have he : iteratedFDeriv ℝ n (fun y => ∑' j, f j y) =ᶠ[𝓝 x]
        (fun y => ∑' j, iteratedFDeriv ℝ n (f j) y) :=
      Filter.eventuallyEq_of_mem (hs.mem_nhds hx) (fun y hy => ih hy)
    simp_rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply]
    rw [he.fderiv_eq,(local_jet_series_derivative hf hs hc hx hv hb n).fderiv]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) F).symm.toContinuousLinearEquiv.map_tsum

lemma local_contDiff_tsum {E : Type uKahler10035_1} {F : Type uKahler10035_2} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℕ → E → F} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    {s : Set E} (hs : IsOpen s) (hc : IsPreconnected s)
    {v : ℕ → ℕ → ℝ} (hv : ∀ n, Summable (v n))
    (hb : ∀ n j y, y ∈ s → ‖iteratedFDeriv ℝ n (f j) y‖ ≤ v n j) :
    ContDiffOn ℝ ∞ (fun y => ∑' j, f j y) s := by
  apply contDiffOn_of_differentiableOn
  intro n hn x hx
  have he : iteratedFDerivWithin ℝ n (fun y => ∑' j, f j y) s =ᶠ[𝓝 x]
      (fun y => ∑' j, iteratedFDeriv ℝ n (f j) y) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    rw [iteratedFDerivWithin_of_isOpen n hs hy]
    exact local_iteratedFDeriv_tsum hf hs hc hv hb n hy
  exact ((local_jet_series_derivative hf hs hc hx hv hb n).differentiableAt.congr_of_eventuallyEq he).differentiableWithinAt

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePotentialSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma lacunary_degree_ge {Q : ℕ} (hQ : 2 ≤ Q) (j : ℕ) : j+1 ≤ Q^(j+1) := by
  have hh : j+1 ≤ 2^(j+1) := (Nat.lt_two_pow_self (n := j+1)).le
  exact hh.trans (Nat.pow_le_pow_left hQ _)

lemma summable_lacunary {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) {Q : ℕ} (hQ : 2 ≤ Q) :
    Summable (fun j : ℕ => R^(Q^(j+1))) := by
  apply Summable.of_nonneg_of_le (fun j => pow_nonneg hR _) _
    ((summable_geometric_of_lt_one hR hR1).mul_right R)
  intro j
  rw [← pow_succ]
  exact pow_le_pow_of_le_one hR hR1.le (lacunary_degree_ge hQ j)

lemma logarithmicTest_local_jets (a : ℝ) {ε D r R : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D)
    (hr : 0 ≤ r) (hrR : r < R) (hR1 : R < 1) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ P : Finset Sphere,
      ProjectivelySeparated (D/Real.sqrt k) P → ∀ z ∈ Metric.ball (0:Base) r,
      ‖iteratedFDeriv ℝ n (logarithmicTest a ε P k) z‖ ≤ C*R^k := by
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  have hG : 0 < gaussianConstant := gaussianConstant_pos
  by_cases hn : n=0
  · subst n
    obtain ⟨C,hC,hCb⟩ := regularizedLog_lipschitz_bound a he hG.le
    refine ⟨C*gaussianConstant,by positivity,?_⟩
    intro k hk P hP z hz
    have hzn : ‖z‖ ≤ R := (show ‖z‖ < r by simpa using hz).le.trans hrR.le
    have hp := (peak_global_bound hD hk hP z).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hzn _) hG.le)
    have hpG : ‖peakPolynomial P k z‖ ≤ gaussianConstant := hp.trans (by
      exact mul_le_of_le_one_right hG.le (pow_le_one₀ hR.le hR1.le))
    rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs]
    exact (hCb _ hpG).trans ((mul_le_mul_of_nonneg_left hp hC).trans_eq (by ring))
  · let ρ : ℝ := (R-r)/2
    have hρ : 0 < ρ := by dsimp [ρ]; linarith
    obtain ⟨C,hC,hCb⟩ := regularizedLog_positive_jet_bound a he hρ hG.le
      (by positivity : 0 ≤ 2*gaussianConstant) (by omega : 1 ≤ n)
    refine ⟨C,hC,?_⟩
    intro k hk P hP z hz
    have hzn : ‖z‖ < r := by simpa using hz
    have hpr (x : Base) (hx : ‖x‖ ≤ R) : ‖peakPolynomial P k x‖ ≤ gaussianConstant*R^k :=
      (peak_global_bound hD hk hP x).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _) hG.le)
    have hnormz := hpr z (by linarith)
    have hpG : ‖peakPolynomial P k z‖ ≤ gaussianConstant := hnormz.trans
      (mul_le_of_le_one_right hG.le (pow_le_one₀ hR.le hR1.le))
    apply hCb (peakPolynomial P k) z (R^k) ((peakPolynomial_analytic P k).mono (subset_univ _)) hpG
      (pow_pos hR _) (pow_le_one₀ hR.le hR1.le)
    intro x hx
    have hdist : dist x z < ρ := hx
    have htriangle := dist_triangle x z 0
    have hxR : ‖x‖ ≤ R := by rw [dist_zero_right,dist_zero_right] at htriangle; dsimp [ρ] at hdist; linarith
    exact (norm_sub_le _ _).trans (by linarith [hpr x hxR])

lemma testSeries_contDiffOn (a : ℝ) {ε D : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere)
    (hP : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1)))) :
    ContDiffOn ℝ ∞ (fun z => ∑' j, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) z) ball := by
  intro z hz
  have hz1 : ‖z‖ < 1 := hz
  let r := (‖z‖+1)/2
  let R := (r+1)/2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hzR : z ∈ Metric.ball 0 r := by simpa [r] using (by linarith : ‖z‖ < (‖z‖+1)/2)
  choose C hC hb using (fun n => logarithmicTest_local_jets a he hD hr hrR hR1 n)
  have hs := local_contDiff_tsum (fun j => logarithmicTest_contDiff a he _ _)
    Metric.isOpen_ball (convex_ball (0:Base) r).isPreconnected
    (fun n => (summable_lacunary (hr.trans hrR.le) hR1 hQ).mul_left (C n))
    (fun n j y hy => hb n (Q^(j+1)) (Nat.one_le_pow _ _ (by omega)) _ (hP j) y hy)
  exact (hs.contDiffAt (Metric.isOpen_ball.mem_nhds hzR)).contDiffWithinAt

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseLocalSmoothSeriesOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler10148_1 uKahler10148_2 uKahler10162_1 uKahler10162_2 uKahler10184_1 uKahler10184_2

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma local_jet_series_derivative_on {E : Type uKahler10148_1} {F : Type uKahler10148_2} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℕ → E → F} {s : Set E} (hf : ∀ j y, y ∈ s → ContDiffAt ℝ ∞ (f j) y)
    (hs : IsOpen s) (hc : IsPreconnected s) {x : E} (hx : x ∈ s)
    {v : ℕ → ℕ → ℝ} (hv : ∀ n, Summable (v n))
    (hb : ∀ n j y, y ∈ s → ‖iteratedFDeriv ℝ n (f j) y‖ ≤ v n j) (n : ℕ) :
    HasFDerivAt (fun y => ∑' j, iteratedFDeriv ℝ n (f j) y)
      (∑' j, fderiv ℝ (iteratedFDeriv ℝ n (f j)) x) x := by
  apply hasFDerivAt_tsum_of_isPreconnected (hv (n+1)) hs hc
    (fun j y hy => ((hf j y hy).differentiableAt_iteratedFDeriv (by exact_mod_cast (ENat.natCast_lt_top n))).hasFDerivAt)
    (fun j y hy => ?_) hx
    (Summable.of_norm_bounded (hv n) (fun j => hb n j x hx)) hx
  simpa only [norm_fderiv_iteratedFDeriv] using hb (n+1) j y hy

lemma local_iteratedFDeriv_tsum_on {E : Type uKahler10162_1} {F : Type uKahler10162_2} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℕ → E → F} {s : Set E} (hf : ∀ j y, y ∈ s → ContDiffAt ℝ ∞ (f j) y)
    (hs : IsOpen s) (hc : IsPreconnected s)
    {v : ℕ → ℕ → ℝ} (hv : ∀ n, Summable (v n))
    (hb : ∀ n j y, y ∈ s → ‖iteratedFDeriv ℝ n (f j) y‖ ≤ v n j) (n : ℕ) :
    EqOn (iteratedFDeriv ℝ n (fun y => ∑' j, f j y))
      (fun y => ∑' j, iteratedFDeriv ℝ n (f j) y) s := by
  induction n with
  | zero =>
    intro x hx
    simp_rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.map_tsum
  | succ n ih =>
    intro x hx
    have he : iteratedFDeriv ℝ n (fun y => ∑' j, f j y) =ᶠ[𝓝 x]
        (fun y => ∑' j, iteratedFDeriv ℝ n (f j) y) :=
      Filter.eventuallyEq_of_mem (hs.mem_nhds hx) (fun y hy => ih hy)
    simp_rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply]
    rw [he.fderiv_eq,(local_jet_series_derivative_on hf hs hc hx hv hb n).fderiv]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) F).symm.toContinuousLinearEquiv.map_tsum

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseChartSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma logarithmicTest_chart_contDiffAt (a : ℝ) {ε : ℝ} (he : ε ≠ 0)
    (P : Finset Sphere) (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) {z : Base} (hz : z ∈ ball) :
    ContDiffAt ℝ ∞ (logarithmicTest a ε P k ∘ centeredChart r U) z :=
  (logarithmicTest_contDiff a he P k).contDiffAt.comp z
    ((centeredChart_analyticAt U (centeredChart_den_ne_zero hr hr1 hz)).contDiffAt.restrict_scalars ℝ)

lemma logarithmicTest_chart_local_jets (a : ℝ) {ε D r : ℝ} (he : ε ≠ 0)
    (hD : 1 ≤ D) (hr : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ P : Finset Sphere,
      ProjectivelySeparated (D/Real.sqrt k) P → ∀ U : Base ≃ₗᵢ[ℂ] Base,
      ∀ z ∈ Metric.ball (0:Base) (1/64),
      ‖iteratedFDeriv ℝ n (logarithmicTest a ε P k ∘ centeredChart r U) z‖ ≤ C*(1-(1-r)/16)^k := by
  have hG := gaussianConstant_pos
  let R := 1-(1-r)/16
  have hR : 0 < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hpb (k : ℕ) (hk : 1 ≤ k) (P : Finset Sphere)
      (hP : ProjectivelySeparated (D/Real.sqrt k) P) (U : Base ≃ₗᵢ[ℂ] Base)
      (z : Base) (hz : ‖z‖ < 1/32) :
      ‖peakPolynomial P k (centeredChart r U z)‖ ≤ gaussianConstant*R^k :=
    (peak_global_bound hD hk hP _).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (chart_norm_deficit hr hr1 U hz) k) gaussianConstant_pos.le)
  by_cases hn : n=0
  · subst n
    obtain ⟨C,hC,hCb⟩ := regularizedLog_lipschitz_bound a he gaussianConstant_pos.le
    refine ⟨C*gaussianConstant,by positivity,?_⟩
    intro k hk P hP U z hz
    have hp := hpb k hk P hP U z (by
      have hz' : ‖z‖ < 1/64 := by simpa using hz
      linarith)
    have hpG : ‖peakPolynomial P k (centeredChart r U z)‖ ≤ gaussianConstant :=
      hp.trans (mul_le_of_le_one_right gaussianConstant_pos.le (pow_le_one₀ hR.le hR1.le))
    rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs]
    exact (hCb _ hpG).trans ((mul_le_mul_of_nonneg_left hp hC).trans_eq (by ring))
  · obtain ⟨C,hC,hCb⟩ := regularizedLog_positive_jet_bound a he (by norm_num : (0:ℝ)<1/64)
      gaussianConstant_pos.le (by positivity : 0 ≤ 2*gaussianConstant) (by omega : 1 ≤ n)
    refine ⟨C,hC,?_⟩
    intro k hk P hP U z hz
    have hz' : ‖z‖ < 1/64 := by simpa using hz
    have hsub (x : Base) (hx : x ∈ Metric.ball z (1/64)) : ‖x‖ < 1/32 := by
      have hh := dist_triangle x z 0
      have hx' : dist x z < 1/64 := hx
      simp only [dist_zero_right] at hh
      linarith
    have hf : AnalyticOnNhd ℂ (peakPolynomial P k ∘ centeredChart r U) (Metric.ball z (1/64)) := by
      intro x hx
      have hxb : x ∈ ball := by change ‖x‖ < 1; linarith [hsub x hx]
      exact (peakPolynomial_analytic P k _ (mem_univ _)).comp
        (centeredChart_analyticAt U (centeredChart_den_ne_zero hr hr1 hxb))
    have hp := hpb k hk P hP U z (by linarith)
    have hpG : ‖peakPolynomial P k (centeredChart r U z)‖ ≤ gaussianConstant :=
      hp.trans (mul_le_of_le_one_right gaussianConstant_pos.le (pow_le_one₀ hR.le hR1.le))
    apply hCb _ z (R^k) hf hpG (pow_pos hR _) (pow_le_one₀ hR.le hR1.le)
    intro x hx
    apply (norm_sub_le _ _).trans
    dsimp only [Function.comp_apply]
    linarith [hpb k hk P hP U x (hsub x hx)]

lemma testSeries_chart_iteratedFDeriv (a : ℝ) {ε D : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere)
    (hP : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1))))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (U : Base ≃ₗᵢ[ℂ] Base) (n : ℕ) :
    iteratedFDeriv ℝ n ((fun y => ∑' j, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) y) ∘ centeredChart r U) 0 =
      ∑' j, iteratedFDeriv ℝ n (logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ∘ centeredChart r U) 0 := by
  choose C hC hb using (fun n => logarithmicTest_chart_local_jets a he hD hr hr1 n)
  have hs := summable_lacunary (by linarith : 0 ≤ 1-(1-r)/16) (by linarith : 1-(1-r)/16 < 1) hQ
  exact local_iteratedFDeriv_tsum_on
    (fun j z hz => logarithmicTest_chart_contDiffAt a he _ _ hr hr1 U
      (by
        have hz' : ‖z‖ < 1/64 := by simpa using hz
        change ‖z‖ < 1
        linarith))
    Metric.isOpen_ball (convex_ball (0:Base) (1/64)).isPreconnected
    (fun n => hs.mul_left (C n))
    (fun n j z hz => hb n _ (Nat.one_le_pow _ _ (by omega)) _ (hP j) U z hz) n
    (Metric.mem_ball_self (by norm_num))

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseJetNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma wirtingerCLM_apply (b : Bool) (i : Fin 2) (L : Base →L[ℝ] ℂ) :
    wirtingerCLM b i L = (L (EuclideanSpace.single i 1) +
      (if b then Complex.I else -Complex.I)*L (Complex.I • EuclideanSpace.single i 1))/2 := by
  simp only [wirtingerCLM,smul_apply,add_apply,
    ContinuousLinearMap.apply_apply,smul_eq_mul]
  ring

lemma wirtingerCLM_norm (b : Bool) (i : Fin 2) : ‖wirtingerCLM b i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro L
  rw [wirtingerCLM_apply,norm_div]
  have h1 := L.le_opNorm (EuclideanSpace.single i 1)
  have h2 := L.le_opNorm (Complex.I • EuclideanSpace.single i 1)
  have hn : ‖(if b then Complex.I else -Complex.I)‖=1 := by cases b <;> simp
  have he : ‖(EuclideanSpace.single i 1 : Base)‖=1 := by simp
  simp only [he,norm_smul,Complex.norm_I,mul_one] at h1 h2
  have hh := norm_add_le (L (EuclideanSpace.single i 1))
    ((if b then Complex.I else -Complex.I)*L (Complex.I • EuclideanSpace.single i 1))
  rw [norm_mul,hn,one_mul] at hh
  norm_num only [Complex.norm_ofNat,one_mul]
  linarith

lemma dzBase_asCLM (f : Base → ℂ) (i : Fin 2) :
    (fun z => dzBase f z i)=wirtingerCLM false i ∘ fderiv ℝ f := by
  funext z
  rw [Function.comp_apply,wirtingerCLM_apply]
  simp only [Bool.false_eq_true,ite_false,neg_mul,dzBase,sub_eq_add_neg]

lemma dbarBase_asCLM (f : Base → ℂ) (i : Fin 2) :
    (fun z => dbarBase f z i)=wirtingerCLM true i ∘ fderiv ℝ f := by
  funext z
  rw [Function.comp_apply,wirtingerCLM_apply]
  rfl

lemma norm_jet_dzBase {f : Base → ℂ} {z : Base} (hf : ContDiffAt ℝ ∞ f z) (i : Fin 2) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x => dzBase f x i) z‖ ≤ ‖iteratedFDeriv ℝ (n+1) f z‖ := by
  rw [dzBase_asCLM]
  have hd := hf.fderiv_right (m := ∞) (by simp)
  have hh := (wirtingerCLM false i).norm_iteratedFDeriv_comp_left hd
    (show (n:ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))
  exact hh.trans ((mul_le_mul_of_nonneg_right (wirtingerCLM_norm false i) (norm_nonneg _)).trans_eq (by rw [one_mul,norm_iteratedFDeriv_fderiv]))

lemma norm_jet_dbarBase {f : Base → ℂ} {z : Base} (hf : ContDiffAt ℝ ∞ f z) (i : Fin 2) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x => dbarBase f x i) z‖ ≤ ‖iteratedFDeriv ℝ (n+1) f z‖ := by
  rw [dbarBase_asCLM]
  have hd := hf.fderiv_right (m := ∞) (by simp)
  have hh := (wirtingerCLM true i).norm_iteratedFDeriv_comp_left hd
    (show (n:ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))
  exact hh.trans ((mul_le_mul_of_nonneg_right (wirtingerCLM_norm true i) (norm_nonneg _)).trans_eq (by rw [one_mul,norm_iteratedFDeriv_fderiv]))

lemma norm_jet_ofReal {f : Base → ℝ} {z : Base} (hf : ContDiffAt ℝ ∞ f z) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x => (f x:ℂ)) z‖ ≤ ‖iteratedFDeriv ℝ n f z‖ := by
  have hh := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left hf
    (show (n:ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))
  simpa [Function.comp_def,Complex.ofRealCLM_norm] using hh

lemma norm_jet_baseHessian {f : Base → ℝ} {z : Base} (hf : ContDiffAt ℝ ∞ f z)
    (i j : Fin 2) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x => baseHessian f x i j) z‖ ≤ ‖iteratedFDeriv ℝ (n+2) f z‖ := by
  have hfc := Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
  exact (norm_jet_dzBase (_root_.OAI.ContDiffAt.hartogs_dbarBase hfc (m := ∞) (by simp) j) i n).trans
    ((norm_jet_dbarBase hfc j (n+1)).trans (norm_jet_ofReal hf (n+2)))

lemma norm_baseHessian_le {f : Base → ℝ} {z : Base} (hf : ContDiffAt ℝ ∞ f z) (i j : Fin 2) :
    ‖baseHessian f z i j‖ ≤ ‖iteratedFDeriv ℝ 2 f z‖ := by
  simpa only [norm_iteratedFDeriv_zero,Nat.zero_add] using norm_jet_baseHessian hf i j 0

lemma norm_baseHessian_derivatives_le {f : Base → ℝ} {z : Base} (hf : ContDiffAt ℝ ∞ f z)
    (i j k l : Fin 2) :
    ‖dzBase (fun x => baseHessian f x i j) z k‖+
    ‖dbarBase (fun x => baseHessian f x i j) z l‖+
    ‖dzBase (fun x => dbarBase (fun y => baseHessian f y i j) x l) z k‖ ≤
      2*‖iteratedFDeriv ℝ 3 f z‖+‖iteratedFDeriv ℝ 4 f z‖ := by
  have hh : ContDiffAt ℝ ∞ (fun x => baseHessian f x i j) z :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp (baseHessian_contDiffAt hf) i)) j
  have h1 := (norm_jet_dzBase hh k 0).trans (norm_jet_baseHessian hf i j 1)
  have h2 := (norm_jet_dbarBase hh l 0).trans (norm_jet_baseHessian hf i j 1)
  have h3 := (norm_jet_dzBase (_root_.OAI.ContDiffAt.hartogs_dbarBase hh (by simp) l) k 0).trans
    ((norm_jet_dbarBase hh l 1).trans (norm_jet_baseHessian hf i j 2))
  simp only [norm_iteratedFDeriv_zero] at h1 h2 h3
  linarith

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseHessianJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma dz_dbar_jet {f : Base → ℂ} {z : Base} (hf : ContDiffAt ℝ ∞ f z) (i j : Fin 2) :
    dzBase (fun x => dbarBase f x j) z i = complexHessianJet i j (iteratedFDeriv ℝ 2 f z) := by
  have hd := (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have he := ((wirtingerCLM true j).hasFDerivAt.comp z hd.hasFDerivAt).fderiv
  rw [dbarBase_asCLM] at ⊢
  simp only [dzBase,he,ContinuousLinearMap.comp_apply,wirtingerCLM_apply]
  simp only [complexHessianJet,smul_apply,add_apply,
    sub_apply,ContinuousMultilinearMap.apply_apply,smul_eq_mul,
    iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one,ite_true]
  have hi : Complex.I*Complex.I = -1 := Complex.I_mul_I
  linear_combination -(fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single i 1)
    (Complex.I • EuclideanSpace.single j 1))/4*hi

lemma baseHessian_eq_jet {f : Base → ℝ} {z : Base} (hf : ContDiffAt ℝ ∞ f z) (i j : Fin 2) :
    baseHessian f z i j = realHessianJet i j (iteratedFDeriv ℝ 2 f z) := by
  have hfc : ContDiffAt ℝ ∞ (fun x => (f x:ℂ)) z := Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
  rw [baseHessian,dz_dbar_jet hfc]
  change complexHessianJet i j (iteratedFDeriv ℝ 2 (Complex.ofRealCLM ∘ f) z) = _
  rw [Complex.ofRealCLM.iteratedFDeriv_comp_left hf (WithTop.coe_le_coe.mpr le_top)]
  rfl

lemma baseHessian_value_eq_jet {f : Base → ℝ} {z : Base} (hf : ContDiffAt ℝ ∞ f z) (v : Base) :
    (∑ i, ∑ j, baseHessian f z i j*v i*star (v j)).re =
      realHessianValueJet v (iteratedFDeriv ℝ 2 f z) := by
  simp only [realHessianValueJet,ContinuousLinearMap.comp_apply,sum_apply,
    smul_apply,smul_eq_mul,Complex.reCLM_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [baseHessian_eq_jet hf]
  ring

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseChartUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma testSeries_chart_summable_jets (a : ℝ) {ε D : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere)
    (hP : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1))))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (U : Base ≃ₗᵢ[ℂ] Base) (n : ℕ) :
    Summable (fun j => iteratedFDeriv ℝ n (logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ∘ centeredChart r U) 0) := by
  obtain ⟨C,hC,hb⟩ := logarithmicTest_chart_local_jets a he hD hr hr1 n
  apply Summable.of_norm_bounded
    ((summable_lacunary (by linarith : 0 ≤ 1-(1-r)/16) (by linarith : 1-(1-r)/16 < 1) hQ).mul_left C)
  intro j
  exact hb _ (Nat.one_le_pow _ _ (by omega)) _ (hP j) U 0 (Metric.mem_ball_self (by norm_num))

lemma testSeries_chart_psh (a : ℝ) {ε D : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere)
    (hP : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1))))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (U : Base ≃ₗᵢ[ℂ] Base) (v : Base) :
    0 ≤ (∑ i, ∑ j, baseHessian
      ((fun y => ∑' l, logarithmicTest a ε (P (Q^(l+1))) (Q^(l+1)) y) ∘ centeredChart r U) 0 i j * v i * star (v j)).re := by
  have hf := chartWeight_contDiffAt (testSeries_contDiffOn a he hD hQ P hP) hr hr1 U
  rw [baseHessian_value_eq_jet hf, testSeries_chart_iteratedFDeriv a he hD hQ P hP hr hr1 U 2,
    (realHessianValueJet v).map_tsum (testSeries_chart_summable_jets a he hD hQ P hP hr hr1 U 2)]
  apply tsum_nonneg
  intro l
  rw [← baseHessian_value_eq_jet (logarithmicTest_chart_contDiffAt a he _ _ hr hr1 U (by change ‖(0:Base)‖ < 1; simp))]
  apply regularizedLog_holomorphic_psh a he
  exact (peakPolynomial_analytic _ _ _ (mem_univ _)).comp
    (centeredChart_analyticAt U (z := 0) (by simp))

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseChartNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma iteratedFDeriv_add_mul {f g : Base → ℝ} {z : Base}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) (L : ℝ) (n : ℕ) :
    iteratedFDeriv ℝ n (fun x => f x+L*g x) z =
      iteratedFDeriv ℝ n f z + L • iteratedFDeriv ℝ n g z := by
  have hfn : ContDiffAt ℝ n f z := hf.of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))
  have hgn : ContDiffAt ℝ n g z := hg.of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))
  change iteratedFDeriv ℝ n (f + L • g) z = _
  rw [iteratedFDeriv_add_apply hfn (by simpa only [Pi.smul_def,smul_eq_mul] using contDiffAt_const.mul hgn),
    iteratedFDeriv_const_smul_apply hgn]

lemma baseHessian_add_mul {f g : Base → ℝ} {z : Base}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) (L : ℝ) (i j : Fin 2) :
    baseHessian (fun x => f x+L*g x) z i j = baseHessian f z i j + (L:ℂ)*baseHessian g z i j := by
  rw [baseHessian_eq_jet (hf.add (contDiffAt_const.mul hg)),iteratedFDeriv_add_mul hf hg,
    map_add,map_smul,← baseHessian_eq_jet hf,← baseHessian_eq_jet hg]
  simp only [Complex.real_smul]

lemma psi_baseHessian_chart_eventually {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) :
    baseHessian (psi ∘ centeredChart r U) =ᶠ[𝓝 (0:Base)] baseHessian psi := by
  have he := (psi_chart_hessian_eventually hr hr1 U (0:ℂ)).comp_tendsto
    (continuousAt_id.prodMk continuousAt_const : ContinuousAt (fun z : Base => (z,(0:ℂ))) 0).tendsto
  filter_upwards [he,isOpen_ball.mem_nhds zero_mem_ball] with z hz hzb
  have hψ := psi_contDiffAt hzb
  have hf := (psi_contDiffAt (centeredChart_mapsTo hr hr1 U hzb)).comp z
    ((centeredChart_analyticAt U (centeredChart_den_ne_zero hr hr1 hzb)).contDiffAt.restrict_scalars ℝ)
  ext i j
  have hh := congrArg (fun A => A i.castSucc j.castSucc) hz
  change liftedHessian (psi ∘ centeredChart r U) (z,0) i.castSucc j.castSucc =
    liftedHessian psi (z,0) i.castSucc j.castSucc at hh
  rw [liftedHessian_horizontal (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_horizontal (hψ.of_le (WithTop.coe_le_coe.mpr le_top))] at hh
  exact hh

lemma psi_baseHessian_center (i j : Fin 2) : baseHessian psi 0 i j = if i=j then 1 else 0 := by
  rw [← liftedHessian_horizontal (q := (0,(0:ℂ))) ((psi_contDiffAt zero_mem_ball).of_le (WithTop.coe_le_coe.mpr le_top)) i j]
  change complexHessian (fun q : Ambient => psi q.1) (0,0) i.castSucc j.castSucc = _
  rw [psi_hessian_center]
  fin_cases i <;> fin_cases j <;> norm_num [horizontalIdentity]

lemma psi_baseHessian_value (v : Base) :
    (∑ i, ∑ j, baseHessian psi 0 i j*v i*star (v j)).re = ‖v‖^2 := by
  simp only [psi_baseHessian_center]
  simp only [Fin.sum_univ_two,Fin.reduceEq,ite_true,ite_false,one_mul,zero_mul,zero_add,add_zero]
  simp only [Complex.star_def,Complex.mul_conj,Complex.add_re,Complex.ofReal_re,Complex.normSq_eq_norm_sq]
  rw [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]

lemma baseHessian_chart_normalize {f : Base → ℝ} (hf : ContDiffOn ℝ ∞ f ball)
    (L : ℝ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (U : Base ≃ₗᵢ[ℂ] Base) :
    baseHessian ((fun x => psi x+L*f x) ∘ centeredChart r U) =ᶠ[𝓝 (0:Base)]
      baseHessian (fun z => psi z+L*f (centeredChart r U z)) := by
  filter_upwards [psi_baseHessian_chart_eventually hr hr1 U,isOpen_ball.mem_nhds zero_mem_ball] with z hz hzb
  have hT : ContDiffAt ℝ ∞ (centeredChart r U) z := (centeredChart_analyticAt U (centeredChart_den_ne_zero hr hr1 hzb)).contDiffAt.restrict_scalars ℝ
  have hfc := (hf.contDiffAt (isOpen_ball.mem_nhds (centeredChart_mapsTo hr hr1 U hzb))).comp z hT
  have hψc := (psi_contDiffAt (centeredChart_mapsTo hr hr1 U hzb)).comp z hT
  ext i j
  change baseHessian (fun x => psi (centeredChart r U x)+L*f (centeredChart r U x)) z i j = _
  erw [baseHessian_add_mul hψc hfc L i j,baseHessian_add_mul (psi_contDiffAt hzb) hfc L i j]
  exact congrArg (fun A => A i j + (L:ℂ)*baseHessian (f ∘ centeredChart r U) z i j) hz

lemma baseHessian_congr_derivatives {f g : Base → ℝ} {z : Base}
    (h : baseHessian f =ᶠ[𝓝 z] baseHessian g) (i j k l : Fin 2) :
    dzBase (fun x => baseHessian f x i j) z k = dzBase (fun x => baseHessian g x i j) z k ∧
    dbarBase (fun x => baseHessian f x i j) z l = dbarBase (fun x => baseHessian g x i j) z l ∧
    dzBase (fun x => dbarBase (fun y => baseHessian f y i j) x l) z k =
      dzBase (fun x => dbarBase (fun y => baseHessian g y i j) x l) z k := by
  have he : (fun x => baseHessian f x i j) =ᶠ[𝓝 z] (fun x => baseHessian g x i j) := h.fun_comp (fun A => A i j)
  have hd : (fun x => dbarBase (fun y => baseHessian f y i j) x l) =ᶠ[𝓝 z]
      (fun x => dbarBase (fun y => baseHessian g y i j) x l) := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with x hx
    simp only [dbarBase,hx]
  exact ⟨by simp only [dzBase,he.fderiv_eq],by simp only [dbarBase,he.fderiv_eq],by simp only [dzBase,hd.fderiv_eq]⟩

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePotentialControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma base_matrix_value_bound {H : Matrix (Fin 2) (Fin 2) ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hH : ∀ i j, ‖H i j‖ ≤ C) (v : Base) :
    (∑ i, ∑ j, H i j*v i*star (v j)).re ≤ 4*C*‖v‖^2 := by
  calc
    (∑ i, ∑ j, H i j*v i*star (v j)).re ≤ ‖∑ i, ∑ j, H i j*v i*star (v j)‖ := Complex.re_le_norm _
    _ ≤ ∑ i, ∑ j, ‖H i j*v i*star (v j)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, C*‖v‖^2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul,norm_mul,norm_star,pow_two, ← mul_assoc]
      apply mul_le_mul (mul_le_mul (hH i j) (PiLp.norm_apply_le v i) (norm_nonneg _) hC)
        (PiLp.norm_apply_le v j) (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))
    _ = 4*C*‖v‖^2 := by simp; ring

lemma norm_jet_add_mul {f g : Base → ℝ} {z : Base}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x => f x+L*g x) z‖ ≤
      ‖iteratedFDeriv ℝ n f z‖ + L*‖iteratedFDeriv ℝ n g z‖ := by
  rw [iteratedFDeriv_add_mul hf hg]
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hL])

lemma basePotential_chart_control_oai (a : ℝ) {ε D L : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D) (hL : 0 ≤ L)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere)
    (hP : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1)))) :
    ∃ C : ℝ, ChartControl (basePotential P a ε L Q) 1 C ∧ ChartJets (basePotential P a ε L Q) C := by
  let f : Base → ℝ := fun z => ∑' j, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) z
  have hf : ContDiffOn ℝ ∞ f ball := testSeries_contDiffOn a he hD hQ P hP
  obtain ⟨C₂,hC₂,hb₂⟩ := testSeries_chart_uniform_jets a he hD hQ P hP (by norm_num : 1 ≤ (2:ℕ))
  obtain ⟨C₃,hC₃,hb₃⟩ := testSeries_chart_uniform_jets a he hD hQ P hP (by norm_num : 1 ≤ (3:ℕ))
  obtain ⟨C₄,hC₄,hb₄⟩ := testSeries_chart_uniform_jets a he hD hQ P hP (by norm_num : 1 ≤ (4:ℕ))
  let B₂ := ‖iteratedFDeriv ℝ 2 psi (0:Base)‖+L*C₂
  let B₃ := ‖iteratedFDeriv ℝ 3 psi (0:Base)‖+L*C₃
  let B₄ := ‖iteratedFDeriv ℝ 4 psi (0:Base)‖+L*C₄
  have hB₂ : 0 ≤ B₂ := add_nonneg (norm_nonneg _) (mul_nonneg hL hC₂)
  have hB₃ : 0 ≤ B₃ := add_nonneg (norm_nonneg _) (mul_nonneg hL hC₃)
  have hB₄ : 0 ≤ B₄ := add_nonneg (norm_nonneg _) (mul_nonneg hL hC₄)
  let C := 1+4*B₂+2*B₃+B₄
  refine ⟨C,?_,?_⟩
  · intro r hr hr1 U v
    have hfg := chartWeight_contDiffAt hf hr hr1 U
    have hψ := psi_contDiffAt zero_mem_ball
    have hm : ContDiffAt ℝ ∞ (fun z => psi z+L*f (centeredChart r U z)) 0 :=
      hψ.add (contDiffAt_const.mul hfg)
    have hn := baseHessian_chart_normalize hf L hr hr1 U
    change baseHessian (basePotential P a ε L Q ∘ centeredChart r U) =ᶠ[𝓝 (0:Base)]
      baseHessian (fun z => psi z+L*f (centeredChart r U z)) at hn
    have heq := hn.self_of_nhds
    rw [heq]
    constructor
    · have hpsh := testSeries_chart_psh a he hD hQ P hP hr hr1 U v
      erw [baseHessian_value_eq_jet hm,iteratedFDeriv_add_mul hψ hfg,map_add,map_smul,
        ← baseHessian_value_eq_jet hψ, ← baseHessian_value_eq_jet hfg,psi_baseHessian_value]
      simp only [smul_eq_mul,one_mul]
      exact le_add_of_nonneg_right (mul_nonneg hL hpsh)
    · have hb : ‖iteratedFDeriv ℝ 2 (fun z => psi z+L*f (centeredChart r U z)) 0‖ ≤ B₂ :=
        (norm_jet_add_mul hψ hfg hL 2).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hb₂ r hr hr1 U) hL))
      exact (base_matrix_value_bound hB₂ (fun i j => (norm_baseHessian_le hm i j).trans hb) v).trans
        (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (sq_nonneg _))
  · intro r hr hr1 U i j k l
    have hfg := chartWeight_contDiffAt hf hr hr1 U
    have hψ := psi_contDiffAt zero_mem_ball
    have hm : ContDiffAt ℝ ∞ (fun z => psi z+L*f (centeredChart r U z)) 0 :=
      hψ.add (contDiffAt_const.mul hfg)
    have hn := baseHessian_chart_normalize hf L hr hr1 U
    change baseHessian (basePotential P a ε L Q ∘ centeredChart r U) =ᶠ[𝓝 (0:Base)]
      baseHessian (fun z => psi z+L*f (centeredChart r U z)) at hn
    obtain ⟨hdz,hdbar,hdd⟩ := baseHessian_congr_derivatives hn i j k l
    rw [hdz,hdbar,hdd]
    have hb3 : ‖iteratedFDeriv ℝ 3 (fun z => psi z+L*f (centeredChart r U z)) 0‖ ≤ B₃ :=
      (norm_jet_add_mul hψ hfg hL 3).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hb₃ r hr hr1 U) hL))
    have hb4 : ‖iteratedFDeriv ℝ 4 (fun z => psi z+L*f (centeredChart r U z)) 0‖ ≤ B₄ :=
      (norm_jet_add_mul hψ hfg hL 4).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hb₄ r hr hr1 U) hL))
    exact (norm_baseHessian_derivatives_le hm i j k l).trans (by dsimp only [C]; linarith)

end PinchedHartogs.BaseConstruction

end

end OAI
end

theorem solution : type_of% @OAI.PinchedHartogs.BaseConstruction.basePotential_chart_control_oai := @OAI.PinchedHartogs.BaseConstruction.basePotential_chart_control_oai
