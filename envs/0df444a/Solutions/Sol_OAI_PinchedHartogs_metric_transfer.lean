-- Prove2me | solution 1 for OAI.PinchedHartogs.metric_transfer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T00:36:42.778212+00:00
-- url     : https://prove2.me/submissions/94c41268-f28c-442e-b882-56a6012163a4

import Mathlib
import Definitions.Def_PinchedKahler
import Definitions.Def_OAIQWPH001
import Theorems.Thm_OAI_PinchedHartogs_hartogsMetric_uniform_pinching

section
-- module Solutions.OAIQW_PinchedHartogs.Compat
attribute [-instance] _root_.OAI.PinchedHartogs.BaseConstruction.instMeasurableSpaceCircle_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.MetricCalculus
attribute [-instance] _root_.OAI.PinchedHartogs.BaseConstruction.instCompactSpaceElemBaseSphere _root_.OAI.PinchedHartogs.BaseConstruction.instIsProbabilityMeasureElemBaseSphereSigma _root_.OAI.PinchedHartogs.BaseConstruction.instMeasurableSpaceCircle_solutions
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

lemma complexHessian_mul {f g : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (hg : ContDiffAt ℝ 2 g p) (i j : Fin 3) :
    complexHessian (fun q => f q * g q) p i j =
      (f p : ℂ) * complexHessian g p i j + (g p : ℂ) * complexHessian f p i j +
      dz (fun q => (f q : ℂ)) p i * dbar (fun q => (g q : ℂ)) p j +
      dz (fun q => (g q : ℂ)) p i * dbar (fun q => (f q : ℂ)) p j := by
  have he : (fun q => dbar (fun r => ((f r * g r : ℝ) : ℂ)) q j) =ᶠ[𝓝 p]
      (fun q => dbar (fun r => (f r : ℂ)) q j * (g q : ℂ) +
        (f q : ℂ) * dbar (fun r => (g r : ℂ)) q j) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with q hq hq'
    simp only [Complex.ofReal_mul]
    exact dbar_mul ((_root_.OAI.ContDiffAt.hartogs_real_cast hq).differentiableAt (by norm_num))
      ((_root_.OAI.ContDiffAt.hartogs_real_cast hq').differentiableAt (by norm_num)) j
  have hdf := (_root_.OAI.ContDiffAt.hartogs_real_cast hf).differentiableAt (by norm_num)
  have hdg := (_root_.OAI.ContDiffAt.hartogs_real_cast hg).differentiableAt (by norm_num)
  have hdbf := (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 1) (by norm_num) j).differentiableAt (by norm_num)
  have hdbg := (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hg) (m := 1) (by norm_num) j).differentiableAt (by norm_num)
  unfold complexHessian
  rw [dz_congr he,
    dz_add (f := fun q => dbar (fun r => (f r : ℂ)) q j * (g q : ℂ))
      (g := fun q => (f q : ℂ) * dbar (fun r => (g r : ℂ)) q j)
      (hdbf.mul hdg) (hdf.mul hdbg), dz_mul hdbf hdg, dz_mul hdf hdbg]
  ring

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

lemma complexHessian_rexp {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (i j : Fin 3) :
    complexHessian (fun q => Real.exp (f q)) p i j =
      (Real.exp (f p) : ℂ) * (complexHessian f p i j +
        dz (fun q => (f q : ℂ)) p i * dbar (fun q => (f q : ℂ)) p j) := by
  rw [complexHessian_real_comp hf (Filter.Eventually.of_forall Real.hasDerivAt_exp)
    (Real.hasDerivAt_exp (f p))]
  ring

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

lemma metricPotential_contDiffAt {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (lam : ℝ) {p : Ambient} (hp : p ∈ hartogs φ) :
    ContDiffAt ℝ ∞ (metricPotential φ lam) p := by
  have hdφ : ContDiffAt ℝ ∞ (fun q : Ambient => φ q.1) p :=
    (hφ.contDiffAt (isOpen_ball.mem_nhds hp.1)).comp p contDiffAt_fst
  have ht : ContDiffAt ℝ ∞ (fun q : Ambient => Real.exp (φ q.1) * ‖q.2‖ ^ 2) p :=
    hdφ.exp.mul ((contDiff_norm_sq ℂ).contDiffAt.comp p contDiffAt_snd)
  exact (contDiffAt_const.mul ((psi_contDiffAt hp.1).comp p contDiffAt_fst)).sub
    ((contDiffAt_const.sub ht).log (sub_pos.mpr hp.2).ne')

lemma complexHessian_contDiffAt {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ ∞ f p) : ContDiffAt ℝ ∞ (complexHessian f) p := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact _root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := ∞) (by simp) j) (by simp) i

lemma hartogsMetric_contDiffOn {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball) (lam : ℝ) :
    ContDiffOn ℝ ∞ (hartogsMetric φ lam) (hartogs φ) := by
  intro p hp
  exact (complexHessian_contDiffAt (metricPotential_contDiffAt hφ lam hp)).contDiffWithinAt

lemma dz_real_mul {f g : Ambient → ℝ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (i : Fin 3) :
    dz (fun q => ((f q * g q : ℝ) : ℂ)) p i =
      dz (fun q => (f q : ℂ)) p i * (g p : ℂ) + (f p : ℂ) * dz (fun q => (g q : ℂ)) p i := by
  simp only [Complex.ofReal_mul]
  exact dz_mul (Complex.ofRealCLM.differentiableAt.comp p hf)
    (Complex.ofRealCLM.differentiableAt.comp p hg) i

lemma dbar_real_mul {f g : Ambient → ℝ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (i : Fin 3) :
    dbar (fun q => ((f q * g q : ℝ) : ℂ)) p i =
      dbar (fun q => (f q : ℂ)) p i * (g p : ℂ) + (f p : ℂ) * dbar (fun q => (g q : ℂ)) p i := by
  simp only [Complex.ofReal_mul]
  exact dbar_mul (Complex.ofRealCLM.differentiableAt.comp p hf)
    (Complex.ofRealCLM.differentiableAt.comp p hg) i

lemma complexHessian_fiberPotential {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (hp : Real.exp (f p) * ‖p.2‖ ^ 2 < 1) (i j : Fin 3) :
    complexHessian (fun q => -Real.log (1 - Real.exp (f q) * ‖q.2‖ ^ 2)) p i j =
      ((Real.exp (f p) * ‖p.2‖ ^ 2 / (1 - Real.exp (f p) * ‖p.2‖ ^ 2) : ℝ) : ℂ) *
        complexHessian f p i j +
      ((Real.exp (f p) / (1 - Real.exp (f p) * ‖p.2‖ ^ 2) ^ 2 : ℝ) : ℂ) *
        ((if i = 2 then 1 else 0) + p.2 * dz (fun q => (f q : ℂ)) p i) *
        ((if j = 2 then 1 else 0) + star p.2 * dbar (fun q => (f q : ℂ)) p j) := by
  have hr : ContDiffAt ℝ 2 (fun q : Ambient => ‖q.2‖ ^ 2) p :=
    (contDiff_norm_sq ℂ).contDiffAt.comp p contDiffAt_snd
  have hef := hf.exp
  have ht := hef.mul hr
  have hdf := hf.differentiableAt (by norm_num)
  have hdr := hr.differentiableAt (by norm_num)
  have hde := hef.differentiableAt (by norm_num)
  rw [complexHessian_negLogOneSub ht (sub_pos.mpr hp).ne',
    complexHessian_mul hef hr, complexHessian_rexp hf, complexHessian_fiber_norm_sq,
    dz_real_mul hde hdr, dbar_real_mul hde hdr,
    dz_real_comp hdf (Real.hasDerivAt_exp _), dbar_real_comp hdf (Real.hasDerivAt_exp _),
    dz_fiber_norm_sq, dbar_fiber_norm_sq]
  have hn : ((‖p.2‖ ^ 2 : ℝ) : ℂ) = p.2 * star p.2 := by
    simpa only [Complex.normSq_eq_norm_sq, Complex.star_def] using (Complex.mul_conj p.2).symm
  have hD : (1 : ℂ) - (Real.exp (f p) : ℂ) * (p.2 * star p.2) ≠ 0 := by
    rw [← hn, ← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr (sub_pos.mpr hp).ne'
  simp only [Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_mul, Complex.ofReal_div] at *
  rw [hn]
  field_simp
  ring

lemma hartogsMetric_smooth_form {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (lam : ℝ) {p : Ambient} (hp : p ∈ hartogs φ) (i j : Fin 3) :
    hartogsMetric φ lam p i j =
      (lam : ℂ) * complexHessian (fun q : Ambient => psi q.1) p i j +
      ((Real.exp (φ p.1) * ‖p.2‖ ^ 2 / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2) : ℝ) : ℂ) *
        complexHessian (fun q : Ambient => φ q.1) p i j +
      ((Real.exp (φ p.1) / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2) ^ 2 : ℝ) : ℂ) *
        ((if i = 2 then 1 else 0) + p.2 * dz (fun q : Ambient => (φ q.1 : ℂ)) p i) *
        ((if j = 2 then 1 else 0) + star p.2 * dbar (fun q : Ambient => (φ q.1 : ℂ)) p j) := by
  have hψ : ContDiffAt ℝ 2 (fun q : Ambient => psi q.1) p :=
    ((psi_contDiffAt hp.1).comp p contDiffAt_fst).of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hφp : ContDiffAt ℝ 2 (fun q : Ambient => φ q.1) p :=
    ((hφ.contDiffAt (isOpen_ball.mem_nhds hp.1)).comp p contDiffAt_fst).of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hr : ContDiffAt ℝ 2 (fun q : Ambient => ‖q.2‖ ^ 2) p :=
    (contDiff_norm_sq ℂ).contDiffAt.comp p contDiffAt_snd
  have hlog := ((contDiffAt_const.sub (hφp.exp.mul hr)).log (sub_pos.mpr hp.2).ne').neg
  have he : metricPotential φ lam = (fun q : Ambient =>
      lam * psi q.1 + -Real.log (1 - Real.exp (φ q.1) * ‖q.2‖ ^ 2)) := by
    funext q
    exact sub_eq_add_neg _ _
  unfold hartogsMetric
  rw [he]
  rw [complexHessian_add (contDiffAt_const.mul hψ) hlog, complexHessian_const_mul hψ,
    complexHessian_fiberPotential hφp hp.2]
  ring

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

lemma hartogsMetric_hermitian {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (lam : ℝ) {p : Ambient} (hp : p ∈ hartogs φ) (i j : Fin 3) :
    hartogsMetric φ lam p i j = star (hartogsMetric φ lam p j i) :=
  complexHessian_hermitian ((metricPotential_contDiffAt hφ lam hp).of_le (by exact WithTop.coe_le_coe.mpr le_top)) i j

lemma hartogsMetric_closed {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (lam : ℝ) {p : Ambient} (hp : p ∈ hartogs φ) (i j k : Fin 3) :
    dz (fun q => hartogsMetric φ lam q k j) p i =
      dz (fun q => hartogsMetric φ lam q i j) p k :=
  complexHessian_closed ((metricPotential_contDiffAt hφ lam hp).of_le (by exact WithTop.coe_le_coe.mpr le_top)) i j k

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

lemma hermitianValue_add (A B : CMatrix) (u v : Ambient) :
    hermitianValue (A + B) u v = hermitianValue A u v + hermitianValue B u v := by
  simp [hermitianValue, add_mul, Finset.sum_add_distrib]

lemma hermitianValue_smul (c : ℂ) (A : CMatrix) (u v : Ambient) :
    hermitianValue (c • A) u v = c * hermitianValue A u v := by
  simp [hermitianValue, Finset.mul_sum, mul_assoc]

lemma hermitianValue_rank_one (a : Fin 3 → ℂ) (u v : Ambient) :
    hermitianValue (fun i j => a i * star (a j)) u v =
      (∑ i, a i * coordinates u i) * star (∑ i, a i * coordinates v i) := by
  simp [hermitianValue, Fin.sum_univ_three, star_add, star_mul]
  ring

lemma hermitianValue_rank_one_self (a : Fin 3 → ℂ) (u : Ambient) :
    (hermitianValue (fun i j => a i * star (a j)) u u).re =
      ‖∑ i, a i * coordinates u i‖ ^ 2 := by
  rw [hermitianValue_rank_one]
  simpa only [Complex.normSq_eq_norm_sq, Complex.star_def, Complex.ofReal_re] using
    congrArg Complex.re (Complex.mul_conj (∑ i, a i * coordinates u i))

lemma hermitianValue_base_norm_sq (p u v : Ambient) :
    hermitianValue (complexHessian (fun q : Ambient => ‖q.1‖ ^ 2) p) u v =
      u.1 0 * star (v.1 0) + u.1 1 * star (v.1 1) := by
  simp [hermitianValue, complexHessian_base_norm_sq, Fin.sum_univ_three, coordinates]

lemma hermitianValue_base_norm_sq_self (p u : Ambient) :
    (hermitianValue (complexHessian (fun q : Ambient => ‖q.1‖ ^ 2) p) u u).re = ‖u.1‖ ^ 2 := by
  rw [hermitianValue_base_norm_sq, Complex.add_re, base_norm_sq_coordinates]
  simp only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq, coordCLM_apply, coordinates, Matrix.cons_val_zero, Matrix.cons_val_one]

lemma hermitianValue_psi_self {p : Ambient} (hp : p.1 ∈ ball) (u : Ambient) :
    (hermitianValue (complexHessian (fun q : Ambient => psi q.1) p) u u).re =
      (1 - ‖p.1‖ ^ 2)⁻¹ * ‖u.1‖ ^ 2 + ((1 - ‖p.1‖ ^ 2) ^ 2)⁻¹ *
        ‖star (p.1 0) * u.1 0 + star (p.1 1) * u.1 1‖ ^ 2 := by
  have hρ : 0 < 1 - ‖p.1‖ ^ 2 := by
    have := norm_nonneg p.1
    change ‖p.1‖ < 1 at hp
    nlinarith
  have hf : ContDiffAt ℝ 2 (fun q : Ambient => ‖q.1‖ ^ 2) p :=
    (contDiff_norm_sq ℂ).contDiffAt.comp p contDiffAt_fst
  let a : Fin 3 → ℂ := ![star (p.1 0), star (p.1 1), 0]
  let R : CMatrix := fun i j => a i * star (a j)
  have hm : complexHessian (fun q : Ambient => psi q.1) p =
      ((1 - ‖p.1‖ ^ 2)⁻¹ : ℝ) • complexHessian (fun q : Ambient => ‖q.1‖ ^ 2) p +
      (((1 - ‖p.1‖ ^ 2) ^ 2)⁻¹ : ℝ) • R := by
    ext i j
    change complexHessian (fun q : Ambient => -Real.log (1 - ‖q.1‖ ^ 2)) p i j =
      (((1 - ‖p.1‖ ^ 2)⁻¹ : ℝ) : ℂ) * complexHessian (fun q : Ambient => ‖q.1‖ ^ 2) p i j +
      ((((1 - ‖p.1‖ ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) * (a i * star (a j))
    rw [complexHessian_negLogOneSub hf hρ.ne', dz_base_norm_sq, dbar_base_norm_sq]
    fin_cases i <;> fin_cases j <;> simp [a, mul_assoc]
  rw [hm, hermitianValue_add]
  have hsm (t : ℝ) (M : CMatrix) : (hermitianValue (t • M) u u).re = t * (hermitianValue M u u).re := by
    change (hermitianValue ((t : ℂ) • M) u u).re = _
    rw [hermitianValue_smul]
    simp
  rw [Complex.add_re, hsm, hsm, hermitianValue_base_norm_sq_self]
  change _ = _
  rw [show R = (fun i j => a i * star (a j)) from rfl, hermitianValue_rank_one_self]
  simp [a, Fin.sum_univ_three, coordinates]

lemma hermitianValue_real_smul (c : ℝ) (A : CMatrix) (u v : Ambient) :
    (hermitianValue (c • A) u v).re = c * (hermitianValue A u v).re := by
  change (hermitianValue ((c : ℂ) • A) u v).re = _
  rw [hermitianValue_smul]
  simp

lemma hartogsMetric_value {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (lam : ℝ) {p : Ambient} (hp : p ∈ hartogs φ) (u : Ambient) :
    (hermitianValue (hartogsMetric φ lam p) u u).re =
      lam * (hermitianValue (complexHessian (fun q : Ambient => psi q.1) p) u u).re +
      (Real.exp (φ p.1) * ‖p.2‖ ^ 2 / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2)) *
        (∑ i, ∑ j, baseHessian φ p.1 i j * u.1 i * star (u.1 j)).re +
      (Real.exp (φ p.1) / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2) ^ 2) *
        ‖u.2 + p.2 * (dzBase (fun z => (φ z : ℂ)) p.1 0 * u.1 0 +
          dzBase (fun z => (φ z : ℂ)) p.1 1 * u.1 1)‖ ^ 2 := by
  have hf : ContDiffAt ℝ 2 φ p.1 :=
    (hφ.contDiffAt (isOpen_ball.mem_nhds hp.1)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hdf := hf.differentiableAt (by norm_num)
  have hd : DifferentiableAt ℝ (fun q : Ambient => φ q.1) p := hdf.comp p differentiableAt_fst
  let a : Fin 3 → ℂ := fun i => (if i = 2 then 1 else 0) +
    p.2 * dz (fun q : Ambient => (φ q.1 : ℂ)) p i
  have ha (j : Fin 3) : star (a j) = (if j = 2 then 1 else 0) +
      star p.2 * dbar (fun q : Ambient => (φ q.1 : ℂ)) p j := by
    rw [dbar_eq_star_dz_real hd]
    simp [a]
  let R : CMatrix := fun i j => a i * star (a j)
  have hm : hartogsMetric φ lam p =
      lam • complexHessian (fun q : Ambient => psi q.1) p +
      (Real.exp (φ p.1) * ‖p.2‖ ^ 2 / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2)) •
        complexHessian (fun q : Ambient => φ q.1) p +
      (Real.exp (φ p.1) / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2) ^ 2) •
        R := by
    ext i j
    change hartogsMetric φ lam p i j =
      (lam : ℂ) * complexHessian (fun q : Ambient => psi q.1) p i j +
      ((Real.exp (φ p.1) * ‖p.2‖ ^ 2 / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2) : ℝ) : ℂ) *
        complexHessian (fun q : Ambient => φ q.1) p i j +
      ((Real.exp (φ p.1) / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2) ^ 2 : ℝ) : ℂ) *
        (a i * star (a j))
    rw [hartogsMetric_smooth_form hφ lam hp, ha]
    simp only [a]
    ring
  rw [hm, hermitianValue_add, hermitianValue_add, Complex.add_re, Complex.add_re,
    hermitianValue_real_smul, hermitianValue_real_smul, hermitianValue_real_smul,
    hermitianValue_lift_base hf]
  rw [show R = (fun i j => a i * star (a j)) from rfl, hermitianValue_rank_one_self]
  have hdc : DifferentiableAt ℝ (fun z => (φ z : ℂ)) p.1 :=
    Complex.ofRealCLM.differentiableAt.comp p.1 hdf
  have hz (i : Fin 3) := dz_lift_base (p := p) hdc i
  have hasum : (∑ i, a i * coordinates u i) = u.2 + p.2 *
      (dzBase (fun z => (φ z : ℂ)) p.1 0 * u.1 0 +
        dzBase (fun z => (φ z : ℂ)) p.1 1 * u.1 1) := by
    simp [a, hz, Fin.sum_univ_three, coordinates]
    ring
  rw [hasum]

lemma hartogsMetric_positive {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (hpsh : IsPshBase φ) {lam : ℝ} (hlam : 0 < lam) {p : Ambient} (hp : p ∈ hartogs φ)
    {u : Ambient} (hu : u ≠ 0) :
    0 < (hermitianValue (hartogsMetric φ lam p) u u).re := by
  rw [hartogsMetric_value hφ lam hp, hermitianValue_psi_self hp.1]
  have hD : 0 < 1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2 := sub_pos.mpr hp.2
  have hρ : 0 < 1 - ‖p.1‖ ^ 2 := by
    have hn := norm_nonneg p.1
    have hz : ‖p.1‖ < 1 := hp.1
    nlinarith
  have hx : 0 ≤ Real.exp (φ p.1) * ‖p.2‖ ^ 2 / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2) := by positivity
  have hH := hpsh p.1 hp.1 u.1
  have hB := mul_nonneg hx hH
  have hV : 0 < Real.exp (φ p.1) / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2) ^ 2 := by positivity
  by_cases huz : u.1 = 0
  · have huw : u.2 ≠ 0 := by
      intro h
      exact hu (Prod.ext huz h)
    simp only [huz, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add,
      PiLp.zero_apply, add_zero]
    have hvpos : 0 < ‖u.2‖ ^ 2 := pow_pos (norm_pos_iff.mpr huw) _
    simpa using mul_pos hV hvpos
  · have hi : 0 < (1 - ‖p.1‖ ^ 2)⁻¹ * ‖u.1‖ ^ 2 := by positivity
    have hi2 : 0 ≤ ((1 - ‖p.1‖ ^ 2) ^ 2)⁻¹ *
        ‖star (p.1 0) * u.1 0 + star (p.1 1) * u.1 1‖ ^ 2 := by positivity
    have hvnonneg := mul_nonneg hV.le (sq_nonneg ‖u.2 + p.2 *
      (dzBase (fun z => (φ z : ℂ)) p.1 0 * u.1 0 + dzBase (fun z => (φ z : ℂ)) p.1 1 * u.1 1)‖)
    have hh := mul_pos hlam (add_pos_of_pos_of_nonneg hi hi2)
    linarith

theorem hartogsMetric_isKahler {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (hpsh : IsPshBase φ) {lam : ℝ} (hlam : 0 < lam) :
    IsKahlerMetric (hartogs φ) (hartogsMetric φ lam) := by
  refine ⟨hartogsMetric_contDiffOn hφ lam, (fun p hp => hartogsMetric_hermitian hφ lam hp), ?_, (fun p hp => hartogsMetric_closed hφ lam hp)⟩
  intro p hp u hu
  exact hartogsMetric_positive hφ hpsh hlam hp hu

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

lemma fderiv_real_wirtinger {f : Ambient → ℝ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (u : Ambient) :
    fderiv ℝ f p u = 2 * (∑ i, dz (fun q => (f q : ℂ)) p i * coordinates u i).re := by
  have h := congrArg Complex.re (fderiv_wirtinger (fun q => (f q : ℂ)) p u)
  rw [fderiv_real_cast hf] at h
  simpa [dbar_eq_star_dz_real hf, star_mul, ← star_mul, Complex.add_re,
    Finset.sum_add_distrib, ← two_mul, mul_comm, ← Finset.sum_mul] using h

lemma dz_psi {p : Ambient} (hp : p.1 ∈ ball) (i : Fin 3) :
    dz (fun q : Ambient => (psi q.1 : ℂ)) p i =
      ((1 - ‖p.1‖ ^ 2)⁻¹ : ℝ) *
        (star (p.1 0) * (if i = 0 then 1 else 0) + star (p.1 1) * (if i = 1 then 1 else 0)) := by
  have hρ : 0 < 1 - ‖p.1‖ ^ 2 := by
    have hn := norm_nonneg p.1
    change ‖p.1‖ < 1 at hp
    nlinarith
  have hf : DifferentiableAt ℝ (fun q : Ambient => ‖q.1‖ ^ 2) p :=
    ((contDiff_norm_sq ℂ (n := 1)).contDiffAt.comp p contDiffAt_fst).differentiableAt (by norm_num)
  exact (dz_real_comp hf (negLogOneSub_hasDerivAt hρ.ne') i).trans (by rw [dz_base_norm_sq])

lemma fderiv_psi {p : Ambient} (hp : p.1 ∈ ball) (u : Ambient) :
    fderiv ℝ (fun q : Ambient => psi q.1) p u =
      2 * (1 - ‖p.1‖ ^ 2)⁻¹ * (star (p.1 0) * u.1 0 + star (p.1 1) * u.1 1).re := by
  have hf : DifferentiableAt ℝ (fun q : Ambient => psi q.1) p :=
    ((psi_contDiffAt hp).comp p contDiffAt_fst).differentiableAt (by simp)
  rw [fderiv_real_wirtinger hf]
  have hs : (∑ i, dz (fun q : Ambient => (psi q.1 : ℂ)) p i * coordinates u i) =
      (((1 - ‖p.1‖ ^ 2)⁻¹ : ℝ) : ℂ) *
        (star (p.1 0) * u.1 0 + star (p.1 1) * u.1 1) := by
    simp only [dz_psi hp, Fin.sum_univ_three]
    norm_num [coordinates, show (2 : Fin 3) ≠ 0 from by decide,
      show (2 : Fin 3) ≠ 1 from by decide]
    ring
  rw [hs, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma psi_derivative_sq_le {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (hpsh : IsPshBase φ) {lam : ℝ} (hlam : 0 < lam) {p : Ambient} (hp : p ∈ hartogs φ)
    (u : Ambient) :
    lam * (fderiv ℝ (fun q : Ambient => psi q.1) p u) ^ 2 ≤
      4 * (hermitianValue (hartogsMetric φ lam p) u u).re := by
  rw [fderiv_psi hp.1, hartogsMetric_value hφ lam hp, hermitianValue_psi_self hp.1]
  have hD : 0 < 1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2 := sub_pos.mpr hp.2
  have hρ : 0 < 1 - ‖p.1‖ ^ 2 := by
    have hn := norm_nonneg p.1
    have hz : ‖p.1‖ < 1 := hp.1
    nlinarith
  have hx : 0 ≤ Real.exp (φ p.1) * ‖p.2‖ ^ 2 / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2) := by positivity
  have hH := mul_nonneg hx (hpsh p.1 hp.1 u.1)
  have hV : 0 ≤ Real.exp (φ p.1) / (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2) ^ 2 *
      ‖u.2 + p.2 * (dzBase (fun z => (φ z : ℂ)) p.1 0 * u.1 0 +
        dzBase (fun z => (φ z : ℂ)) p.1 1 * u.1 1)‖ ^ 2 := by positivity
  have hN : 0 ≤ (1 - ‖p.1‖ ^ 2)⁻¹ * ‖u.1‖ ^ 2 := by positivity
  have hsq (z : ℂ) : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    linarith [sq_nonneg z.im]
  have hS := mul_le_mul_of_nonneg_left (hsq (star (p.1 0) * u.1 0 + star (p.1 1) * u.1 1))
    (show 0 ≤ lam * ((1 - ‖p.1‖ ^ 2) ^ 2)⁻¹ by positivity)
  simp only [← inv_pow] at hS ⊢
  linarith [mul_nonneg hlam.le hN]

lemma fiberPotential_contDiffAt {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    {p : Ambient} (hp : p ∈ hartogs φ) : ContDiffAt ℝ ∞ (fiberPotential φ) p := by
  have hf := (hφ.contDiffAt (isOpen_ball.mem_nhds hp.1)).comp p contDiffAt_fst
  exact ((contDiffAt_const.sub (hf.exp.mul
    ((contDiff_norm_sq ℂ).contDiffAt.comp p contDiffAt_snd))).log (sub_pos.mpr hp.2).ne').neg

lemma dz_fiberPotential {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    {p : Ambient} (hp : p ∈ hartogs φ) (i : Fin 3) :
    dz (fun q => (fiberPotential φ q : ℂ)) p i =
      ((Real.exp (φ p.1) / (1 - fiberParameter φ p) : ℝ) : ℂ) * star p.2 *
        ((if i = 2 then 1 else 0) + p.2 * dz (fun q : Ambient => (φ q.1 : ℂ)) p i) := by
  have hf : DifferentiableAt ℝ (fun q : Ambient => φ q.1) p :=
    ((hφ.contDiffAt (isOpen_ball.mem_nhds hp.1)).comp p contDiffAt_fst).differentiableAt (by simp)
  have hr : DifferentiableAt ℝ (fun q : Ambient => ‖q.2‖ ^ 2) p :=
    ((contDiff_norm_sq ℂ (n := 1)).contDiffAt.comp p contDiffAt_snd).differentiableAt (by norm_num)
  have he := hf.exp
  change dz (fun q : Ambient => ((-Real.log (1 - Real.exp (φ q.1) * ‖q.2‖ ^ 2) : ℝ) : ℂ)) p i = _
  have ht : DifferentiableAt ℝ (fun q : Ambient => Real.exp (φ q.1) * ‖q.2‖ ^ 2) p := he.mul hr
  rw [dz_real_comp ht (negLogOneSub_hasDerivAt (sub_pos.mpr hp.2).ne'),
    dz_real_mul he hr, dz_real_comp hf (Real.hasDerivAt_exp _), dz_fiber_norm_sq]
  have hn : ((‖p.2‖ ^ 2 : ℝ) : ℂ) = p.2 * star p.2 := by
    simpa only [Complex.normSq_eq_norm_sq, Complex.star_def] using (Complex.mul_conj p.2).symm
  simp only [fiberParameter, Complex.ofReal_inv, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
  rw [hn]
  ring

lemma fderiv_fiberPotential {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    {p : Ambient} (hp : p ∈ hartogs φ) (u : Ambient) :
    fderiv ℝ (fiberPotential φ) p u =
      2 * (Real.exp (φ p.1) / (1 - fiberParameter φ p)) * (star p.2 * thetaValue φ p u).re := by
  rw [fderiv_real_wirtinger ((fiberPotential_contDiffAt hφ hp).differentiableAt (by simp))]
  have hdc : DifferentiableAt ℝ (fun z : Base => (φ z : ℂ)) p.1 :=
    Complex.ofRealCLM.differentiableAt.comp p.1
      ((hφ.contDiffAt (isOpen_ball.mem_nhds hp.1)).differentiableAt (by simp))
  have hs : (∑ i, dz (fun q : Ambient => (fiberPotential φ q : ℂ)) p i * coordinates u i) =
      ((Real.exp (φ p.1) / (1 - fiberParameter φ p) : ℝ) : ℂ) *
        (star p.2 * thetaValue φ p u) := by
    simp only [dz_fiberPotential hφ hp, dz_lift_base hdc, Fin.sum_univ_three]
    simp [coordinates, thetaValue, show (0 : Fin 3) ≠ 2 from by decide,
      show (1 : Fin 3) ≠ 2 from by decide, Matrix.cons_val_two]
    ring
  rw [hs, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma fiberPotential_derivative_sq_le {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (hpsh : IsPshBase φ) {lam : ℝ} (hlam : 0 < lam) {p : Ambient} (hp : p ∈ hartogs φ)
    (u : Ambient) :
    (fderiv ℝ (fiberPotential φ) p u) ^ 2 ≤
      4 * (hermitianValue (hartogsMetric φ lam p) u u).re := by
  have hD : 0 < 1 - fiberParameter φ p := sub_pos.mpr hp.2
  have ht : 0 ≤ fiberParameter φ p := by unfold fiberParameter; positivity
  have ht1 : fiberParameter φ p < 1 := hp.2
  have hi : 0 ≤ (hermitianValue (complexHessian (fun q : Ambient => psi q.1) p) u u).re := by
    rw [hermitianValue_psi_self hp.1]
    have hρ : 0 < 1 - ‖p.1‖ ^ 2 := by
      have hn := norm_nonneg p.1
      have hz : ‖p.1‖ < 1 := hp.1
      nlinarith
    positivity
  have hh := mul_nonneg (div_nonneg ht hD.le) (hpsh p.1 hp.1 u.1)
  have hv : 0 ≤ Real.exp (φ p.1) / (1 - fiberParameter φ p) ^ 2 * ‖thetaValue φ p u‖ ^ 2 := by positivity
  have hm : Real.exp (φ p.1) / (1 - fiberParameter φ p) ^ 2 * ‖thetaValue φ p u‖ ^ 2 ≤
      (hermitianValue (hartogsMetric φ lam p) u u).re := by
    rw [hartogsMetric_value hφ lam hp]
    change _ ≤ lam * _ + fiberParameter φ p / (1 - fiberParameter φ p) * _ +
      Real.exp (φ p.1) / (1 - fiberParameter φ p) ^ 2 * ‖thetaValue φ p u‖ ^ 2
    linarith [mul_nonneg hlam.le hi]
  have hs : (star p.2 * thetaValue φ p u).re ^ 2 ≤ ‖p.2‖ ^ 2 * ‖thetaValue φ p u‖ ^ 2 := by
    have hh := Complex.sq_norm_sub_sq_re (star p.2 * thetaValue φ p u)
    rw [norm_mul, norm_star, mul_pow] at hh
    linarith [sq_nonneg (star p.2 * thetaValue φ p u).im]
  rw [fderiv_fiberPotential hφ hp]
  have hs' := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ (Real.exp (φ p.1) / (1 - fiberParameter φ p)) ^ 2 by positivity)
  have he : (Real.exp (φ p.1) / (1 - fiberParameter φ p)) ^ 2 *
      (‖p.2‖ ^ 2 * ‖thetaValue φ p u‖ ^ 2) = fiberParameter φ p *
        (Real.exp (φ p.1) / (1 - fiberParameter φ p) ^ 2 * ‖thetaValue φ p u‖ ^ 2) := by
    simp only [fiberParameter, div_pow]
    ring
  rw [he] at hs'
  linarith [mul_nonneg (sub_nonneg.mpr ht1.le) hv]

lemma norm_exp_half_smul_sq (a : ℝ) (w : ℂ) :
    ‖Real.exp (a / 2) • w‖ ^ 2 = Real.exp a * ‖w‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, exp_half_sq]

lemma fiberParameter_exp_neg_half (φ : Base → ℝ) (z : Base) (w : ℂ) :
    fiberParameter φ (z, Real.exp (-φ z / 2) • w) = ‖w‖ ^ 2 := by
  unfold fiberParameter
  rw [norm_exp_half_smul_sq, ← mul_assoc, ← Real.exp_add]
  simp

lemma hartogsCompactSet_subset {φ : Base → ℝ} {ρ τ : ℝ} (hρ : ρ < 1) (hτ : τ < 1) :
    hartogsCompactSet φ ρ τ ⊆ hartogs φ := by
  intro p hp
  exact ⟨lt_of_le_of_lt hp.1 hρ, lt_of_le_of_lt hp.2 hτ⟩

lemma hartogsCompactSet_isCompact {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    {ρ τ : ℝ} (hρ : ρ < 1) (hτ : 0 ≤ τ) : IsCompact (hartogsCompactSet φ ρ τ) := by
  let K : Set Ambient := Metric.closedBall (0 : Base) ρ ×ˢ Metric.closedBall (0 : ℂ) (Real.sqrt τ)
  let F : Ambient → Ambient := fun p => (p.1, Real.exp (-φ p.1 / 2) • p.2)
  have hK : IsCompact K := (isCompact_closedBall (0 : Base) ρ).prod
    (isCompact_closedBall (0 : ℂ) (Real.sqrt τ))
  have hz : ∀ p ∈ K, p.1 ∈ ball := by
    intro p hp
    exact lt_of_le_of_lt (by simpa using hp.1) hρ
  have hF : ContinuousOn F K := continuousOn_fst.prodMk
    ((Real.continuous_exp.comp_continuousOn
      (((hφ.continuousOn.comp continuousOn_fst hz).neg).div_const 2)).smul continuousOn_snd)
  have he : F '' K = hartogsCompactSet φ ρ τ := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨by simpa [F] using hq.1, ?_⟩
      change fiberParameter φ (q.1, Real.exp (-φ q.1 / 2) • q.2) ≤ τ
      rw [fiberParameter_exp_neg_half]
      have hn : ‖q.2‖ ≤ Real.sqrt τ := by simpa using hq.2
      nlinarith [Real.sq_sqrt hτ, norm_nonneg q.2]
    · intro hp
      refine ⟨(p.1, Real.exp (φ p.1 / 2) • p.2), ?_, ?_⟩
      · refine ⟨by simpa using hp.1, ?_⟩
        change dist (Real.exp (φ p.1 / 2) • p.2) 0 ≤ Real.sqrt τ
        rw [dist_zero_right]
        have hh := norm_exp_half_smul_sq (φ p.1) p.2
        have ht : Real.exp (φ p.1) * ‖p.2‖ ^ 2 ≤ τ := hp.2
        nlinarith [Real.sq_sqrt hτ, Real.sqrt_nonneg τ, norm_nonneg (Real.exp (φ p.1 / 2) • p.2)]
      · refine Prod.ext (by rfl) ?_
        change Real.exp (-φ p.1 / 2) • (Real.exp (φ p.1 / 2) • p.2) = p.2
        rw [smul_smul, ← Real.exp_add]
        have hh : -φ p.1 / 2 + φ p.1 / 2 = 0 := by ring
        rw [hh, Real.exp_zero, one_smul]
  rw [← he]
  exact hK.image_of_continuousOn hF

lemma hartogs_barrier_sublevels_compact {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (a b : ℝ) : ∃ K : Set Ambient, IsCompact K ∧ K ⊆ hartogs φ ∧
      ∀ p ∈ hartogs φ, fiberPotential φ p ≤ a → psi p.1 ≤ b → p ∈ K := by
  let τ := max 0 (1 - Real.exp (-a))
  let ρ := Real.sqrt (max 0 (1 - Real.exp (-b)))
  have hτ0 : 0 ≤ τ := le_max_left _ _
  have hτ1 : τ < 1 := max_lt (by norm_num) (by linarith [Real.exp_pos (-a)])
  have hρ1 : ρ < 1 := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr
    rw [one_pow]
    exact max_lt (by norm_num) (by linarith [Real.exp_pos (-b)])
  refine ⟨hartogsCompactSet φ ρ τ, hartogsCompactSet_isCompact hφ hρ1 hτ0,
    hartogsCompactSet_subset hρ1 hτ1, ?_⟩
  intro p hp ha hb
  have hD : 0 < 1 - fiberParameter φ p := sub_pos.mpr hp.2
  have hψ : 0 < 1 - ‖p.1‖ ^ 2 := by
    have hz : ‖p.1‖ < 1 := hp.1
    nlinarith [norm_nonneg p.1]
  have ha' : Real.exp (-a) ≤ 1 - fiberParameter φ p := by
    rw [← Real.exp_log hD]
    apply Real.exp_le_exp.mpr
    change -Real.log (1 - fiberParameter φ p) ≤ a at ha
    linarith
  have hb' : Real.exp (-b) ≤ 1 - ‖p.1‖ ^ 2 := by
    rw [← Real.exp_log hψ]
    apply Real.exp_le_exp.mpr
    change -Real.log (1 - ‖p.1‖ ^ 2) ≤ b at hb
    linarith
  refine ⟨?_, ?_⟩
  · have hh : ‖p.1‖ ^ 2 ≤ max 0 (1 - Real.exp (-b)) := by
      exact (by linarith : ‖p.1‖ ^ 2 ≤ 1 - Real.exp (-b)).trans (le_max_right _ _)
    have hr := Real.sq_sqrt (le_max_left 0 (1 - Real.exp (-b)))
    have hr0 := Real.sqrt_nonneg (max 0 (1 - Real.exp (-b)))
    change ‖p.1‖ ≤ Real.sqrt (max 0 (1 - Real.exp (-b)))
    nlinarith [norm_nonneg p.1]
  · exact (by linarith : fiberParameter φ p ≤ 1 - Real.exp (-a)).trans (le_max_right _ _)

lemma coordinates_equiv (u : Ambient) : coordinates u = coordinateEquiv u := rfl

lemma matrix_isUnit_of_metric_positive {h : CMatrix}
    (hpos : ∀ u : Ambient, u ≠ 0 → 0 < (hermitianValue h u u).re) : IsUnit h := by
  have hk : ∀ v : Target, h.mulVec v = 0 → v = 0 := by
    intro v hv
    by_contra hn
    let u := coordinateEquiv.symm (star v)
    have hu : u ≠ 0 := by
      intro huu
      have hh := congrArg coordinates huu
      simp only [u, coordinates_equiv_symm, coordinates_zero] at hh
      exact hn (star_eq_zero.mp hh)
    have he : hermitianValue h u u = 0 := by
      simp only [hermitianValue, u, coordinates_equiv_symm, Pi.star_apply, star_star]
      calc
        (∑ i, ∑ j, h i j * star (v i) * v j) = ∑ i, star (v i) * (h.mulVec v) i := by
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
          congr 1
          funext i
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = 0 := by simp [hv]
    have hh := hpos u hu
    rw [he, Complex.zero_re] at hh
    exact lt_irrefl _ hh
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  apply sub_eq_zero.mp
  apply hk
  rw [Matrix.mulVec_sub, hvw, sub_self]

lemma matrix_det_ne_zero_of_metric_positive {h : CMatrix}
    (hpos : ∀ u : Ambient, u ≠ 0 → 0 < (hermitianValue h u u).re) : h.det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det h).mp (matrix_isUnit_of_metric_positive hpos)).ne_zero

lemma kahler_metric_det_ne_zero {M : Set Ambient} {g : Ambient → CMatrix}
    (hg : IsKahlerMetric M g) {p : Ambient} (hp : p ∈ M) : (g p).det ≠ 0 :=
  matrix_det_ne_zero_of_metric_positive (hg.2.2.1 p hp)

lemma matrix_contDiffAt_det {E : Type uKahler1607_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {g : E → CMatrix} {p : E} (hg : ContDiffAt ℝ n g p) :
    ContDiffAt ℝ n (fun q => (g q).det) p := by
  simp only [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ hσ
  apply contDiffAt_const.mul
  apply contDiffAt_prod
  intro i hi
  exact contDiffAt_pi.mp (contDiffAt_pi.mp hg (σ i)) i

lemma matrix_contDiffAt_inv {E : Type uKahler1618_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {g : E → CMatrix} {p : E} (hg : ContDiffAt ℝ n g p)
    (hdet : (g p).det ≠ 0) : ContDiffAt ℝ n (fun q => (g q)⁻¹) p := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  apply ((matrix_contDiffAt_det hg).inv hdet).mul
  apply matrix_contDiffAt_det
  apply contDiffAt_pi.mpr
  intro a
  apply contDiffAt_pi.mpr
  intro b
  by_cases ha : a = j
  · subst a
    simp only [Matrix.updateRow_self]
    exact contDiffAt_const
  · simpa only [Matrix.updateRow_ne ha] using contDiffAt_pi.mp (contDiffAt_pi.mp hg a) b

lemma christoffel_contDiffAt {M : Set Ambient} (hM : IsOpen M) {g : Ambient → CMatrix}
    (hg : IsKahlerMetric M g) {p : Ambient} (hp : p ∈ M) (k a c : Fin 3) :
    ContDiffAt ℝ ∞ (fun q => christoffel g q k a c) p := by
  have hgs := hg.1.contDiffAt (hM.mem_nhds hp)
  have hinv := matrix_contDiffAt_inv hgs (kahler_metric_det_ne_zero hg hp)
  apply ContDiffAt.sum
  intro e he
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp hinv e) k).mul
    (_root_.OAI.ContDiffAt.hartogs_dz (contDiffAt_pi.mp (contDiffAt_pi.mp hgs c) e) (by simp) a)

lemma geodesicField_contDiffAt {M : Set Ambient} (hM : IsOpen M) {g : Ambient → CMatrix}
    (hg : IsKahlerMetric M g) {y : Ambient × Ambient} (hy : y.1 ∈ M) :
    ContDiffAt ℝ ∞ (geodesicField g) y := by
  have hs : ContDiffAt ℝ ∞ (fun x : Ambient × Ambient => fun k : Fin 3 =>
      -∑ a, ∑ c, christoffel g x.1 k a c * coordinates x.2 a * coordinates x.2 c) y := by
    apply contDiffAt_pi.mpr
    intro k
    apply ContDiffAt.neg
    apply ContDiffAt.sum
    intro a ha
    apply ContDiffAt.sum
    intro c hc
    exact (((christoffel_contDiffAt hM hg hy k a c).comp y contDiffAt_fst).mul
      (((coordCLM a).restrictScalars ℝ).contDiff.contDiffAt.comp y contDiffAt_snd)).mul
        (((coordCLM c).restrictScalars ℝ).contDiff.contDiffAt.comp y contDiffAt_snd)
  have ht := (coordinateEquiv.symm.contDiff.restrict_scalars ℝ).contDiffAt.comp y hs
  exact contDiffAt_snd.prodMk ht

lemma hermitianValue_conj {h : CMatrix} (hh : ∀ i j, h i j = star (h j i))
    (u v : Ambient) : hermitianValue h v u = star (hermitianValue h u v) := by
  simp only [hermitianValue, star_sum, star_mul', star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hh i j]
  simp only [star_star]
  ring

lemma christoffel_contract {g : Ambient → CMatrix} {p : Ambient}
    (hdet : (g p).det ≠ 0) (a c j : Fin 3) :
    (∑ k, g p k j * christoffel g p k a c) = dz (fun q => g q c j) p a := by
  simp only [christoffel, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ e, ∑ k, g p k j * ((g p)⁻¹ e k * dz (fun q => g q c e) p a)) =
        ∑ e, ((g p)⁻¹ * g p) e j * dz (fun q => g q c e) p a := by
      apply Finset.sum_congr rfl
      intro e he
      simp only [Matrix.mul_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = _ := by simp [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_apply]

lemma acceleration_contract {g : Ambient → CMatrix} {p : Ambient}
    (hdet : (g p).det ≠ 0) (v : Ambient) :
    hermitianValue (g p) (geodesicAcceleration g p v) v = -connectionCubic g p v := by
  have he (j : Fin 3) : (∑ i, g p i j * coordinates (geodesicAcceleration g p v) i) =
      -∑ a, ∑ c, dz (fun q => g q c j) p a * coordinates v a * coordinates v c := by
    simp only [geodesicAcceleration, coordinates_equiv_symm, mul_neg, Finset.mul_sum,
      Finset.sum_neg_distrib]
    congr 1
    calc
      (∑ i, ∑ a, ∑ c, g p i j *
          (christoffel g p i a c * coordinates v a * coordinates v c)) =
          ∑ a, ∑ c, (∑ i, g p i j * christoffel g p i a c) *
            coordinates v a * coordinates v c := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c hc
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by simp only [christoffel_contract hdet]
  simp only [hermitianValue]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, he, neg_mul, Finset.sum_neg_distrib]
  congr 1
  simp only [connectionCubic, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]

lemma metric_dbar_conj {M : Set Ambient} (hM : IsOpen M) {g : Ambient → CMatrix}
    (hg : IsKahlerMetric M g) {p : Ambient} (hp : p ∈ M) (i j a : Fin 3) :
    dbar (fun q => g q i j) p a = star (dz (fun q => g q j i) p a) := by
  have he : (fun q => g q i j) =ᶠ[𝓝 p] (fun q => star (g q j i)) := by
    filter_upwards [hM.mem_nhds hp] with q hq
    exact hg.2.1 q hq i j
  rw [dbar_congr he, dbar_conj]
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp
    (hg.1.contDiffAt (hM.mem_nhds hp)) j) i).differentiableAt (by simp)

lemma metric_derivative_contract {M : Set Ambient} (hM : IsOpen M) {g : Ambient → CMatrix}
    (hg : IsKahlerMetric M g) {p : Ambient} (hp : p ∈ M) (v : Ambient) :
    (∑ i, ∑ j, fderiv ℝ (fun q => g q i j) p v *
      coordinates v i * star (coordinates v j)) =
      connectionCubic g p v + star (connectionCubic g p v) := by
  simp only [fderiv_wirtinger, metric_dbar_conj hM hg hp,
    Finset.sum_mul, add_mul, Finset.sum_add_distrib, connectionCubic,
    star_sum, star_mul', star_star]
  congr 1
  · rw [Finset.sum_comm]
    simp only [Fin.sum_univ_three]
    ring
  · simp only [Fin.sum_univ_three]
    ring

lemma metric_energy_hasDerivAt_zero {M : Set Ambient} (hM : IsOpen M)
    {g : Ambient → CMatrix} (hg : IsKahlerMetric M g)
    {γ ν : ℝ → Ambient} {t : ℝ} (hp : γ t ∈ M)
    (hγ : HasDerivAt γ (ν t) t)
    (hν : HasDerivAt ν (geodesicAcceleration g (γ t) (ν t)) t) :
    HasDerivAt (fun s => (hermitianValue (g (γ s)) (ν s) (ν s)).re) 0 t := by
  let A := geodesicAcceleration g (γ t) (ν t)
  have hgij (i j : Fin 3) : DifferentiableAt ℝ (fun p => g p i j) (γ t) :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp
      (hg.1.contDiffAt (hM.mem_nhds hp)) i) j).differentiableAt (by simp)
  have hvi (i : Fin 3) : HasDerivAt (fun s => coordinates (ν s) i) (coordinates A i) t :=
    ((coordCLM i).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hν
  let D : ℂ := ∑ i, ∑ j,
    ((fderiv ℝ (fun p => g p i j) (γ t) (ν t) * coordinates (ν t) i +
      g (γ t) i j * coordinates A i) * star (coordinates (ν t) j) +
      g (γ t) i j * coordinates (ν t) i * star (coordinates A j))
  have hd : HasDerivAt (fun s => hermitianValue (g (γ s)) (ν s) (ν s)) D t := by
    apply HasDerivAt.fun_sum
    intro i hi
    apply HasDerivAt.fun_sum
    intro j hj
    exact (((hgij i j).hasFDerivAt.comp_hasDerivAt t hγ).mul (hvi i)).mul (hvi j).star
  have he : D = 0 := by
    have hrewrite : D = (∑ i, ∑ j, fderiv ℝ (fun p => g p i j) (γ t) (ν t) *
        coordinates (ν t) i * star (coordinates (ν t) j)) +
        hermitianValue (g (γ t)) A (ν t) + hermitianValue (g (γ t)) (ν t) A := by
      simp only [D, hermitianValue, add_mul, Finset.sum_add_distrib]
    rw [hrewrite, hermitianValue_conj (hg.2.1 _ hp) A (ν t),
      acceleration_contract (kahler_metric_det_ne_zero hg hp),
      metric_derivative_contract hM hg hp, star_neg]
    ring
  simpa only [he, map_zero, Function.comp_def, Complex.reCLM_apply] using! (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd)

lemma geodesic_energy_hasDerivAt_zero {M : Set Ambient} (hM : IsOpen M)
    {g : Ambient → CMatrix} (hg : IsKahlerMetric M g)
    {y : ℝ → Ambient × Ambient} {t : ℝ} (hp : (y t).1 ∈ M)
    (hy : HasDerivAt y (geodesicField g (y t)) t) :
    HasDerivAt (fun s => metricEnergy g (y s)) 0 t :=
  metric_energy_hasDerivAt_zero hM hg hp hy.fst hy.snd

lemma coordinates_real_smul (c : ℝ) (v : Ambient) :
    coordinates (c • v) = c • coordinates v := by
  funext i
  fin_cases i <;> rfl

lemma hermitianValue_vector_real_smul (h : CMatrix) (c : ℝ) (v : Ambient) :
    (hermitianValue h (c • v) (c • v)).re = c ^ 2 * (hermitianValue h v v).re := by
  have he : hermitianValue h (c • v) (c • v) = (c : ℂ) ^ 2 * hermitianValue h v v := by
    simp only [hermitianValue, coordinates_real_smul, Pi.smul_apply, Complex.real_smul,
      star_mul', Complex.star_def, Complex.conj_ofReal, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  simp [← Complex.ofReal_pow, Complex.mul_re]

lemma metricEnergy_nonneg {M : Set Ambient} {g : Ambient → CMatrix}
    (hg : IsKahlerMetric M g) {p : Ambient} (hp : p ∈ M) (v : Ambient) :
    0 ≤ metricEnergy g (p, v) := by
  by_cases hv : v = 0
  · simp [metricEnergy, hermitianValue, hv, coordinates_zero]
  · exact (hg.2.2.1 p hp v hv).le

lemma metricEnergy_continuousOn {M : Set Ambient} {g : Ambient → CMatrix}
    (hg : ContDiffOn ℝ ∞ g M) : ContinuousOn (metricEnergy g) (M ×ˢ (univ : Set Ambient)) := by
  apply Complex.continuous_re.comp_continuousOn
  apply continuousOn_finsetSum
  intro i hi
  apply continuousOn_finsetSum
  intro j hj
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · exact ((continuous_apply j).comp_continuousOn
        ((continuous_apply i).comp_continuousOn hg.continuousOn)).comp
          continuousOn_fst (fun _ h => h.1)
    · exact (((coordCLM i).continuous).comp continuous_snd).continuousOn
  · exact (continuous_star.comp (((coordCLM j).continuous).comp continuous_snd)).continuousOn

lemma compact_metric_coercivity {M K : Set Ambient} {g : Ambient → CMatrix}
    (hg : IsKahlerMetric M g) (hK : IsCompact K) (hKM : K ⊆ M) :
    ∃ m : ℝ, 0 < m ∧ ∀ p ∈ K, ∀ v : Ambient,
      m * ‖v‖ ^ 2 ≤ metricEnergy g (p, v) := by
  have hs := hK.prod (isCompact_sphere (0 : Ambient) 1)
  have hc : ContinuousOn (metricEnergy g) (K ×ˢ Metric.sphere (0 : Ambient) 1) :=
    (metricEnergy_continuousOn hg.1).mono (prod_mono hKM (subset_univ _))
  obtain ⟨m, hm, hml⟩ := hs.exists_forall_le' hc (a := 0) (by
    rintro ⟨p, v⟩ ⟨hp, hv⟩
    apply hg.2.2.1 p (hKM hp) v
    intro h0
    simp [h0] at hv)
  refine ⟨m, hm, fun p hp v => ?_⟩
  by_cases hv : v = 0
  · simp [hv, metricEnergy, hermitianValue, coordinates_zero]
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    let u := ‖v‖⁻¹ • v
    have hu : u ∈ Metric.sphere (0 : Ambient) 1 := by
      simp [u, norm_smul, hn]
    have hu' : ‖v‖ • u = v := by simp [u, smul_smul, hn]
    have hh := mul_le_mul_of_nonneg_left (hml (p, u) ⟨hp, hu⟩) (sq_nonneg ‖v‖)
    calc
      m * ‖v‖ ^ 2 ≤ ‖v‖ ^ 2 * metricEnergy g (p, u) := by
        simpa only [mul_comm m] using hh
      _ = metricEnergy g (p, v) := by
        change ‖v‖ ^ 2 * (hermitianValue (g p) u u).re = (hermitianValue (g p) v v).re
        rw [← hermitianValue_vector_real_smul, hu']

lemma geodesic_energy_constant {M : Set Ambient} (hM : IsOpen M)
    {g : Ambient → CMatrix} (hg : IsKahlerMetric M g)
    {y : ℝ → Ambient × Ambient} {a : ℝ} (ha : 0 < a)
    (hy : ∀ t ∈ Ioo (-a) a, HasDerivAt y (geodesicField g (y t)) t ∧ (y t).1 ∈ M)
    {t : ℝ} (ht : t ∈ Ioo (-a) a) : metricEnergy g (y t) = metricEnergy g (y 0) := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (geodesic_energy_hasDerivAt_zero hM hg (hy s hs).2 (hy s hs).1).hasDerivWithinAt)
    (fun s hs => (norm_zero : ‖(0 : ℝ)‖ = 0).le)
    (convex_Ioo (-a) a) (show (0 : ℝ) ∈ Ioo (-a) a from ⟨by linarith, ha⟩) ht
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hh

lemma hartogs_isOpen_smooth {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball) :
    IsOpen (hartogs φ) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hz : ∀ᶠ q : Ambient in 𝓝 p, q.1 ∈ ball :=
    continuousAt_fst (isOpen_ball.mem_nhds hp.1)
  have hf : ContinuousAt (fiberParameter φ) p :=
    (Real.continuous_exp.continuousAt.comp
      ((hφ.continuousOn.continuousAt (isOpen_ball.mem_nhds hp.1)).comp continuousAt_fst)).mul
        (continuousAt_snd.norm.pow 2)
  have ht : ∀ᶠ q in 𝓝 p, fiberParameter φ q < 1 := hf (Iio_mem_nhds hp.2)
  exact hz.and ht

private lemma abs_le_add_one_of_sq_le {r c : ℝ} (hc : 0 ≤ c) (hr : r ^ 2 ≤ c) :
    |r| ≤ c + 1 := by
  linarith [sq_abs r, sq_nonneg (|r| - 1)]

lemma curve_function_bound {M : Set Ambient} {g : Ambient → CMatrix}
    {F : Ambient → ℝ} {y : ℝ → Ambient × Ambient} {a L T : ℝ}
    (ha : 0 < a) (hL : 0 ≤ L)
    (hy : ∀ s ∈ Ioo (-a) a, HasDerivAt y (geodesicField g (y s)) s ∧ (y s).1 ∈ M)
    (hF : ∀ p ∈ M, DifferentiableAt ℝ F p)
    (hbound : ∀ s ∈ Ioo (-a) a, |fderiv ℝ F (y s).1 (y s).2| ≤ L)
    {t : ℝ} (ht : t ∈ Ioo (-a) a) (htT : |t| ≤ T) :
    F (y t).1 ≤ F (y 0).1 + L * T := by
  have hd : ∀ s ∈ Ioo (-a) a, HasDerivAt (fun r => F (y r).1)
      (fderiv ℝ F (y s).1 (y s).2) s := by
    intro s hs
    exact (hF _ (hy s hs).2).hasFDerivAt.comp_hasDerivAt s (hy s hs).1.fst
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hd s hs).hasDerivWithinAt)
    (fun s hs => by simpa only [Real.norm_eq_abs] using hbound s hs)
    (convex_Ioo (-a) a) (show (0 : ℝ) ∈ Ioo (-a) a from ⟨by linarith, ha⟩) ht
  simp only [Real.norm_eq_abs, sub_zero] at hb
  have hbt := (le_abs_self (F (y t).1 - F (y 0).1)).trans hb
  have := mul_le_mul_of_nonneg_left htT hL
  linarith

lemma hartogs_geodesic_compact_containment {φ : Base → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ ball) (hpsh : IsPshBase φ)
    {lam : ℝ} (hlam : 0 < lam) {p : Ambient} (hp : p ∈ hartogs φ) (v : Ambient)
    {T : ℝ} (hT : 0 < T) :
    ∃ K : Set (Ambient × Ambient), IsCompact K ∧
      K ⊆ hartogs φ ×ˢ (univ : Set Ambient) ∧
      ∀ (a : ℝ) (y : ℝ → Ambient × Ambient), 0 < a → y 0 = (p, v) →
        (∀ s ∈ Ioo (-a) a, HasDerivAt y (geodesicField (hartogsMetric φ lam) (y s)) s ∧
          (y s).1 ∈ hartogs φ) →
        ∀ t ∈ Ioo (-a) a, |t| ≤ T → y t ∈ K := by
  let g := hartogsMetric φ lam
  have hg := hartogsMetric_isKahler hφ hpsh hlam
  let E := metricEnergy g (p, v)
  have hE : 0 ≤ E := metricEnergy_nonneg hg hp v
  let Lψ := 4 * E / lam + 1
  let Lf := 4 * E + 1
  have hLψ : 0 ≤ Lψ := by dsimp [Lψ]; positivity
  have hLf : 0 ≤ Lf := by dsimp [Lf]; positivity
  obtain ⟨K, hK, hKM, hKB⟩ := hartogs_barrier_sublevels_compact hφ
    (fiberPotential φ p + Lf * T) (psi p.1 + Lψ * T)
  obtain ⟨m, hm, hml⟩ := compact_metric_coercivity hg hK hKM
  let R := E / m + T + 1
  refine ⟨K ×ˢ Metric.closedBall (0 : Ambient) R,
    hK.prod (isCompact_closedBall _ _), prod_mono hKM (subset_univ _), ?_⟩
  intro a y ha hy0 hy t ht htT
  have he (s : ℝ) (hs : s ∈ Ioo (-a) a) : metricEnergy g (y s) = E := by
    simpa only [hy0] using geodesic_energy_constant (hartogs_isOpen_smooth hφ) hg ha hy hs
  have hpos : (y t).1 ∈ K := by
    apply hKB _ (hy t ht).2
    · have hbound (s : ℝ) (hs : s ∈ Ioo (-a) a) :
          |fderiv ℝ (fiberPotential φ) (y s).1 (y s).2| ≤ Lf := by
        have hh := fiberPotential_derivative_sq_le hφ hpsh hlam (hy s hs).2 (y s).2
        change _ ≤ 4 * metricEnergy g (y s) at hh
        rw [he s hs] at hh
        exact abs_le_add_one_of_sq_le (by positivity) hh
      simpa only [hy0, Function.comp_def] using! curve_function_bound ha hLf hy
        (fun q hq => (fiberPotential_contDiffAt hφ hq).differentiableAt (by simp)) hbound ht htT
    · have hbound (s : ℝ) (hs : s ∈ Ioo (-a) a) :
          |fderiv ℝ (fun q : Ambient => psi q.1) (y s).1 (y s).2| ≤ Lψ := by
        have hh := psi_derivative_sq_le hφ hpsh hlam (hy s hs).2 (y s).2
        change _ ≤ 4 * metricEnergy g (y s) at hh
        rw [he s hs] at hh
        apply abs_le_add_one_of_sq_le (by positivity)
        exact (le_div_iff₀ hlam).mpr (by simpa only [mul_comm lam] using hh)
      simpa only [hy0, Function.comp_def] using! curve_function_bound ha hLψ hy
        (fun q hq => ((psi_contDiffAt hq.1).comp q contDiffAt_fst).differentiableAt (by simp))
        hbound ht htT
  refine ⟨hpos, ?_⟩
  have hv := hml (y t).1 hpos (y t).2
  change m * ‖(y t).2‖ ^ 2 ≤ metricEnergy g (y t) at hv
  rw [he t ht] at hv
  have hv' : ‖(y t).2‖ ^ 2 ≤ E / m :=
    (le_div_iff₀ hm).mpr (by simpa only [mul_comm m] using hv)
  rw [Metric.mem_closedBall, dist_zero_right]
  have hnorm : ‖(y t).2‖ ≤ E / m + 1 := by
    simpa only [abs_norm] using abs_le_add_one_of_sq_le (by positivity) hv'
  dsimp [R]
  linarith

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsCurvature
attribute [-instance] _root_.OAI.PinchedHartogs.BaseConstruction.instCompactSpaceElemBaseSphere _root_.OAI.PinchedHartogs.BaseConstruction.instIsProbabilityMeasureElemBaseSphereSigma _root_.OAI.PinchedHartogs.BaseConstruction.instMeasurableSpaceCircle_solutions
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
-- module Solutions.OAIQW_PinchedHartogs.HartogsCharts
attribute [-instance] _root_.OAI.PinchedHartogs.BaseConstruction.instCompactSpaceElemBaseSphere _root_.OAI.PinchedHartogs.BaseConstruction.instIsProbabilityMeasureElemBaseSphereSigma _root_.OAI.PinchedHartogs.BaseConstruction.instMeasurableSpaceCircle_solutions
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

lemma exists_centeredChart {z : Base} (hz : z ∈ ball) :
    ∃ (r : ℝ) (U : Base ≃ₗᵢ[ℂ] Base), 0 ≤ r ∧ r < 1 ∧ centeredChart r U 0 = z := by
  classical
  by_cases hz0 : z = 0
  · subst z
    exact ⟨0, LinearIsometryEquiv.refl ℂ Base, by norm_num, by norm_num,
      by simp [centeredChart_zero]⟩
  let v : Base := (‖z‖⁻¹ : ℂ) • z
  have hv : ‖v‖ = 1 := by
    simp [v, norm_smul, norm_ne_zero_iff.mpr hz0]
  have ho : Orthonormal ℂ (({0} : Set (Fin 2)).domRestrict (fun _ : Fin 2 => v)) := by
    constructor
    · intro i
      exact hv
    · intro i j hij
      exact (hij (Subsingleton.elim _ _)).elim
  obtain ⟨b, hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨‖z‖, b.repr.symm, norm_nonneg _, hz, ?_⟩
  rw [centeredChart_zero, map_smul, b.repr_symm_single, hb 0 (by simp)]
  dsimp [v]
  rw [← Complex.coe_smul, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz0)), one_smul]

lemma fderiv_centeredChart_zero (r : ℝ) (U : Base ≃ₗᵢ[ℂ] Base) (u : Base) :
    fderiv ℂ (centeredChart r U) 0 u =
      U (WithLp.toLp 2 ![(1-(r : ℂ)^2)*u 0, (Real.sqrt (1-r^2) : ℂ)*u 1]) := by
  have hG : HasDerivAt (fun y : ℂ => ((r : ℂ)+y)/(1+(r : ℂ)*y))
      (1-(r : ℂ)^2) 0 := by
    convert ((hasDerivAt_const 0 (r : ℂ)).add (hasDerivAt_id 0)).div
      ((hasDerivAt_const 0 (1 : ℂ)).add ((hasDerivAt_id 0).const_mul (r : ℂ))) (by simp) using 1 <;> try rfl
    simp
    ring
  have h0 : HasFDerivAt (fun z : Base => ((r : ℂ)+z 0)/(1+(r : ℂ)*z 0))
      ((1-(r : ℂ)^2) • baseCoordinate 0) 0 := by
    have hg : HasDerivAt (fun y : ℂ => ((r : ℂ)+y)/(1+(r : ℂ)*y))
        (1-(r : ℂ)^2) ((baseCoordinate 0) (0 : Base)) := by simpa using hG
    exact hg.comp_hasFDerivAt (0 : Base) (baseCoordinate 0).hasFDerivAt
  have hden : DifferentiableAt ℂ (fun z : Base => (1+(r : ℂ)*z 0)⁻¹) 0 :=
    ((analyticAt_const.add (analyticAt_const.mul ((baseCoordinate 0).analyticAt 0))).inv (by simp)).differentiableAt
  have h1 : HasFDerivAt (fun z : Base => (Real.sqrt (1-r^2) : ℂ)*z 1/(1+(r : ℂ)*z 0))
      ((Real.sqrt (1-r^2) : ℂ) • baseCoordinate 1) 0 := by
    have hA : HasFDerivAt (fun z : Base => (Real.sqrt (1-r^2) : ℂ) * z 1)
        ((Real.sqrt (1-r^2) : ℂ) • baseCoordinate 1) (0 : Base) :=
      (baseCoordinate 1).hasFDerivAt.const_mul _
    have hB : HasFDerivAt (fun z : Base => (1+(r : ℂ)*z 0)⁻¹)
        (fderiv ℂ (fun z : Base => (1+(r : ℂ)*z 0)⁻¹) 0) (0 : Base) := hden.hasFDerivAt
    have hh : HasFDerivAt
        (fun z : Base => ((Real.sqrt (1-r^2) : ℂ)*z 1) * (1+(r : ℂ)*z 0)⁻¹)
        (((Real.sqrt (1-r^2) : ℂ) * (0 : Base) 1) • fderiv ℂ (fun z : Base => (1+(r : ℂ)*z 0)⁻¹) 0 +
          (1+(r : ℂ)*(0 : Base) 0)⁻¹ • ((Real.sqrt (1-r^2) : ℂ) • baseCoordinate 1))
        (0 : Base) := hA.mul hB
    have hh' := hh.congr_fderiv (show
        (((Real.sqrt (1-r^2) : ℂ) * (0 : Base) 1) • fderiv ℂ (fun z : Base => (1+(r : ℂ)*z 0)⁻¹) 0 +
          (1+(r : ℂ)*(0 : Base) 0)⁻¹ • ((Real.sqrt (1-r^2) : ℂ) • baseCoordinate 1)) =
        ((Real.sqrt (1-r^2) : ℂ) • baseCoordinate 1) by
      ext z
      simp)
    simpa only [div_eq_mul_inv] using hh'
  have hp : HasFDerivAt (fun z : Base => ![((r : ℂ)+z 0)/(1+(r : ℂ)*z 0),
      (Real.sqrt (1-r^2) : ℂ)*z 1/(1+(r : ℂ)*z 0)])
      (ContinuousLinearMap.pi ![(1-(r : ℂ)^2) • baseCoordinate 0,
        (Real.sqrt (1-r^2) : ℂ) • baseCoordinate 1]) 0 := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact h0
    · exact h1
  have hh := U.toContinuousLinearEquiv.hasFDerivAt.comp 0
    (baseCoordinateEquiv.symm.hasFDerivAt.comp 0 hp)
  change HasFDerivAt (centeredChart r U) _ 0 at hh
  rw [hh.fderiv]
  change U (baseCoordinateEquiv.symm _) = U _
  congr 1
  ext i
  fin_cases i <;> rfl

lemma fderiv_centeredChart_zero_injective {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) : Function.Injective (fderiv ℂ (centeredChart r U) 0) := by
  have hpos : 0 < 1-r^2 := by nlinarith
  have h0 : (1-(r : ℂ)^2) ≠ 0 := by exact_mod_cast hpos.ne'
  have h1 : (Real.sqrt (1-r^2) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  intro u v huv
  rw [fderiv_centeredChart_zero, fderiv_centeredChart_zero] at huv
  have he := U.injective huv
  have ha := congrArg (fun z : Base => z 0) he
  have hb := congrArg (fun z : Base => z 1) he
  ext i
  fin_cases i
  · exact mul_left_cancel₀ h0 ha
  · exact mul_left_cancel₀ h1 hb

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsFrame
attribute [-instance] _root_.OAI.PinchedHartogs.BaseConstruction.instMeasurableSpaceCircle_solutions
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

lemma metricThreshold_pos {c C : ℝ} (hc : 0 < c) (hC : c ≤ C) : 0 < metricThreshold c C := by
  exact lt_of_lt_of_le (show 0 < C+1 by linarith) (le_max_left _ _)

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsTransferTools
attribute [-instance] _root_.OAI.PinchedHartogs.BaseConstruction.instCompactSpaceElemBaseSphere _root_.OAI.PinchedHartogs.BaseConstruction.instIsProbabilityMeasureElemBaseSphereSigma _root_.OAI.PinchedHartogs.BaseConstruction.instMeasurableSpaceCircle_solutions
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

lemma liftBaseMap_analyticAt {C : Base → Base} {p : Ambient} (hC : AnalyticAt ℂ C p.1) :
    AnalyticAt ℂ (liftBaseMap C) p :=
  (hC.comp ((ContinuousLinearMap.fst ℂ Base ℂ).analyticAt p)).prod
    ((ContinuousLinearMap.snd ℂ Base ℂ).analyticAt p)

lemma fderiv_liftBaseMap {C : Base → Base} {p : Ambient} (hC : DifferentiableAt ℂ C p.1)
    (u : Ambient) : fderiv ℂ (liftBaseMap C) p u = (fderiv ℂ C p.1 u.1,u.2) := by
  have hh := (hC.hasFDerivAt.comp p (ContinuousLinearMap.fst ℂ Base ℂ).hasFDerivAt).prodMk
    (ContinuousLinearMap.snd ℂ Base ℂ).hasFDerivAt
  change HasFDerivAt (liftBaseMap C) _ p at hh
  rw [hh.fderiv]
  rfl

lemma baseHessian_value_comp {f : Base → ℝ} {C : Base → Base} {z : Base}
    (hf : ContDiffAt ℝ 2 f (C z)) (hC : AnalyticAt ℂ C z) (u v : Base) :
    (∑ i, ∑ j, baseHessian (f ∘ C) z i j * u i * star (v j)) =
      ∑ i, ∑ j, baseHessian f (C z) i j * (fderiv ℂ C z u) i * star ((fderiv ℂ C z v) j) := by
  have hfc : ContDiffAt ℝ 2 (f ∘ C) z := hf.comp z (hC.contDiffAt.restrict_scalars ℝ)
  have he := complexHessian_pullback
    (hf.comp (f := fun q : Ambient => q.1) (liftBaseMap C (z,0)) contDiffAt_fst)
    (liftBaseMap_analyticAt (p := (z,0)) hC)
  have hh := congrArg (fun A => hermitianValue A (u,0) (v,0)) he
  change hermitianValue (complexHessian (fun q : Ambient => (f ∘ C) q.1) (z,0)) (u,0) (v,0) = _ at hh
  erw [hermitianValue_lift_base hfc, hermitianValue_pullback,
    fderiv_liftBaseMap hC.differentiableAt, fderiv_liftBaseMap hC.differentiableAt,
    hermitianValue_lift_base hf] at hh
  exact hh

lemma chartControl_psh {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    {c C : ℝ} (hc : 0 ≤ c) (hctl : ChartControl φ c C) : IsPshBase φ := by
  intro z hz v
  obtain ⟨r,U,hr,hr1,hz0⟩ := exists_centeredChart hz
  have hi := fderiv_centeredChart_zero_injective hr hr1 U
  have hsurj := (LinearMap.injective_iff_surjective (f := (fderiv ℂ (centeredChart r U) 0).toLinearMap)).mp hi
  obtain ⟨u,hu⟩ := hsurj v
  have hf : ContDiffAt ℝ 2 φ (centeredChart r U 0) :=
    (hφ.contDiffAt (isOpen_ball.mem_nhds (by rw [hz0]; exact hz))).of_le (WithTop.coe_le_coe.mpr le_top)
  have he := baseHessian_value_comp hf (centeredChart_analyticAt U (z := 0) (by simp)) u u
  change fderiv ℂ (centeredChart r U) 0 u = v at hu
  erw [hu,hz0] at he
  rw [← he]
  exact (mul_nonneg hc (sq_nonneg _)).trans (hctl r hr hr1 U u).1

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsCompletenessSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler16710_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
noncomputable section

open Set Filter Topology Metric
open scoped ContDiff NNReal

namespace CompactODE

variable {E : Type uKahler16710_1} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma CurveOn.mono [CompleteSpace E] {V : E → E} {S : Set E} {γ : ℝ → E} {J K : Set ℝ}
    (h : CurveOn V S γ J) (hK : K ⊆ J) : CurveOn V S γ K :=
  fun t ht => h t (hK ht)

lemma local_uniform {V : E → E} {S : Set E} {x₀ : E}
    (hS : IsOpen S) (hx₀ : x₀ ∈ S) (hV : ContDiffAt ℝ 1 V x₀) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ closedBall x₀ r,
      ∃ γ : ℝ → E, γ 0 = x ∧ CurveOn V S γ (Ioo (-ε) ε) := by
  obtain ⟨K, s, hs, hl⟩ := hV.exists_lipschitzOnWith
  obtain ⟨a, ha, has⟩ := Metric.mem_nhds_iff.mp (inter_mem hs (hS.mem_nhds hx₀))
  have has' : ball x₀ a ⊆ s := fun _ h => (has h).1
  have haS : closedBall x₀ (a / 2) ⊆ S := fun _ h =>
    (has (closedBall_subset_ball (half_lt_self ha) h)).2
  set L := K * a + ‖V x₀‖ + 1 with hL
  have hL0 : 0 < L := by positivity
  have hb (x : E) (hx : x ∈ closedBall x₀ (a / 2)) : ‖V x‖ ≤ L := by
    rw [hL]
    calc
      ‖V x‖ ≤ ‖V x - V x₀‖ + ‖V x₀‖ := norm_le_norm_sub_add _ _
      _ ≤ K * ‖x - x₀‖ + ‖V x₀‖ := by
        gcongr
        apply hl.norm_sub_le _ (mem_of_mem_nhds hs)
        exact has' (closedBall_subset_ball (half_lt_self ha) hx)
      _ ≤ K * a + ‖V x₀‖ := by
        gcongr
        rw [← mem_closedBall_iff_norm]
        exact closedBall_subset_closedBall (half_le_self ha.le) hx
      _ ≤ L := le_add_of_nonneg_right zero_le_one
  let ε := a / L / 2 / 2
  have hε : 0 < ε := by positivity
  let A : ℝ≥0 := ⟨a / 2, (half_pos ha).le⟩
  let LL : ℝ≥0 := ⟨L, hL0.le⟩
  let tzero : Icc (-ε) ε := ⟨0, by simp [hε.le]⟩
  have hpl : IsPicardLindelof (fun _ => V) (tmin := -ε) (tmax := ε)
      tzero x₀ A (A / 2) LL K := by
    apply IsPicardLindelof.of_time_independent hb
      (hl.mono (subset_trans (closedBall_subset_ball (half_lt_self ha)) has'))
    change L * max (ε - 0) (0 - -ε) ≤ (a / 2) - (a / 2 / 2)
    simp only [sub_zero, sub_neg_eq_add, zero_add, max_self]
    dsimp [ε]
    field_simp
    linarith
  refine ⟨a / 2 / 2, by positivity, ε, hε, fun x hx => ?_⟩
  have hx' : x ∈ closedBall x₀ ((A / 2 : ℝ≥0) : ℝ) := hx
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hpl hx'
  refine ⟨α.compProj, ?_, fun t ht => ⟨?_, ?_⟩⟩
  · change α.compProj (tzero : ℝ) = x
    rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · have hd : HasDerivWithinAt α.compProj (V (α.compProj t)) (Icc (-ε) ε) t := by
      apply ODE.hasDerivWithinAt_picard_Icc (show (0 : ℝ) ∈ Icc (-ε) ε by simp [hε.le])
        hpl.continuousOn_uncurry α.continuous_compProj.continuousOn
        (fun _ ht' => α.compProj_mem_closedBall hpl.mul_max_le) x (Ioo_subset_Icc_self ht)
        |>.congr_of_mem _ (Ioo_subset_Icc_self ht)
      intro t' ht'
      nth_rw 1 [← hα]
      rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
    exact hd.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  · exact haS (α.compProj_mem_closedBall hpl.mul_max_le)

omit [CompleteSpace E] in
lemma local_unique [CompleteSpace E] {V : E → E} {γ δ : ℝ → E} {t₀ : ℝ}
    (hV : ContDiffAt ℝ 1 V (γ t₀))
    (hγ : ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (V (γ t)) t)
    (hδ : ∀ᶠ t in 𝓝 t₀, HasDerivAt δ (V (δ t)) t)
    (heq : γ t₀ = δ t₀) : γ =ᶠ[𝓝 t₀] δ := by
  obtain ⟨K, s, hs, hL⟩ := hV.exists_lipschitzOnWith
  have hγs : ∀ᶠ t in 𝓝 t₀, γ t ∈ s := (hγ.self_of_nhds.continuousAt) hs
  have hδs : ∀ᶠ t in 𝓝 t₀, δ t ∈ s := (hδ.self_of_nhds.continuousAt) (heq ▸ hs)
  exact ODE_solution_unique_of_eventually (v := fun _ => V) (s := fun _ => s)
    (Eventually.of_forall fun _ => hL) (hγ.and hγs) (hδ.and hδs) heq

lemma unique_Ioo {V : E → E} {S : Set E} {γ δ : ℝ → E} {a b t₀ : ℝ}
    (hV : ∀ x ∈ S, ContDiffAt ℝ 1 V x) (ht₀ : t₀ ∈ Ioo a b)
    (hγ : CurveOn V S γ (Ioo a b)) (hδ : CurveOn V S δ (Ioo a b))
    (heq : γ t₀ = δ t₀) : EqOn γ δ (Ioo a b) := by
  set s := {t | γ t = δ t} ∩ Ioo a b with hs
  suffices hsub : Ioo a b ⊆ s from fun t ht => (hsub ht).1
  apply isPreconnected_Ioo.subset_of_closure_inter_subset (s := Ioo a b) (u := s) _
    ⟨t₀, ⟨ht₀, ⟨heq, ht₀⟩⟩⟩
  · rw [hs, inter_comm, ← Subtype.image_preimage_val, inter_comm, ← Subtype.image_preimage_val,
      image_subset_image_iff Subtype.val_injective, preimage_ofPred_eq]
    intro t ht
    rw [mem_preimage, ← closure_subtype] at ht
    revert ht t
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      exact (hγ t ht).1.continuousAt.comp continuousAt_subtype_val
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      exact (hδ t ht).1.continuousAt.comp continuousAt_subtype_val
  · rw [isOpen_iff_mem_nhds]
    intro t ht
    have hmem := Ioo_mem_nhds ht.2.1 ht.2.2
    have hloc : γ =ᶠ[𝓝 t] δ := local_unique (hV (γ t) (hγ t ht.2).2)
      (Filter.Eventually.mono hmem fun t' ht' => (hγ t' ht').1)
      (Filter.Eventually.mono hmem fun t' ht' => (hδ t' ht').1) ht.1
    exact (hloc.and hmem).mono fun _ h => h

lemma compact_uniform {V : E → E} {S K : Set E} (hS : IsOpen S)
    (hV : ∀ x ∈ S, ContDiffAt ℝ 1 V x) (hK : IsCompact K) (hKS : K ⊆ S) :
    ∃ ε > (0 : ℝ), ∀ x ∈ K, ∃ γ : ℝ → E, γ 0 = x ∧ CurveOn V S γ (Ioo (-ε) ε) := by
  classical
  have hl (x : K) := local_uniform hS (hKS x.2) (hV x (hKS x.2))
  choose r hr ε hε H using hl
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => ball (x : E) (r x))
    (fun _ => isOpen_ball) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr _)⟩)
  have hmin : ∃ d > (0 : ℝ), ∀ x ∈ t, d ≤ ε x := by
    clear ht
    induction t using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert x t hx ih =>
      obtain ⟨d, hd, hdt⟩ := ih
      exact ⟨min d (ε x), lt_min hd (hε x), fun y hy => by
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hdt y hy)⟩
  obtain ⟨d, hd, hdt⟩ := hmin
  refine ⟨d, hd, fun x hx => ?_⟩
  obtain ⟨z, hzt, hzx⟩ := mem_iUnion₂.mp (ht hx)
  obtain ⟨γ, hγ0, hγ⟩ := H z x (ball_subset_closedBall hzx)
  exact ⟨γ, hγ0, hγ.mono (Ioo_subset_Ioo (neg_le_neg (hdt z hzt)) (hdt z hzt))⟩

lemma eqOn_piecewise {V : E → E} {S : Set E} {γ δ : ℝ → E} {a b a' b' t₀ : ℝ}
    (hV : ∀ x ∈ S, ContDiffAt ℝ 1 V x)
    (hγ : CurveOn V S γ (Ioo a b)) (hδ : CurveOn V S δ (Ioo a' b'))
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo a' b') (heq : γ t₀ = δ t₀) :
    EqOn (piecewise (Ioo a b) γ δ) δ (Ioo a' b') := by
  classical
  have H : EqOn γ δ (Ioo (max a a') (min b b')) :=
    unique_Ioo hV ⟨max_lt ht₀.1.1 ht₀.2.1, lt_min ht₀.1.2 ht₀.2.2⟩
      (hγ.mono (Ioo_subset_Ioo (le_max_left ..) (min_le_left ..)))
      (hδ.mono (Ioo_subset_Ioo (le_max_right ..) (min_le_right ..))) heq
  intro t ht
  by_cases hmem : t ∈ Ioo a b
  · rw [piecewise, ite_eq_left hmem]
    exact H ⟨max_lt hmem.1 ht.1, lt_min hmem.2 ht.2⟩
  · rw [piecewise, ite_eq_right hmem]

lemma curveOn_piecewise {V : E → E} {S : Set E} {γ δ : ℝ → E} {a b a' b' t₀ : ℝ}
    (hV : ∀ x ∈ S, ContDiffAt ℝ 1 V x)
    (hγ : CurveOn V S γ (Ioo a b)) (hδ : CurveOn V S δ (Ioo a' b'))
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo a' b') (heq : γ t₀ = δ t₀) :
    CurveOn V S (piecewise (Ioo a b) γ δ) (Ioo a b ∪ Ioo a' b') := by
  classical
  intro t ht
  by_cases hmem : t ∈ Ioo a b
  · have hev : piecewise (Ioo a b) γ δ =ᶠ[𝓝 t] γ := by
      filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with s hs
      exact piecewise_eq_of_mem _ _ _ hs
    rw [hev.self_of_nhds]
    exact ⟨(hγ t hmem).1.congr_of_eventuallyEq hev, (hγ t hmem).2⟩
  · have hmem' : t ∈ Ioo a' b' := ht.resolve_left hmem
    have hev : piecewise (Ioo a b) γ δ =ᶠ[𝓝 t] δ := by
      filter_upwards [Ioo_mem_nhds hmem'.1 hmem'.2] with s hs
      exact eqOn_piecewise hV hγ hδ ht₀ heq hs
    rw [hev.self_of_nhds]
    exact ⟨(hδ t hmem').1.congr_of_eventuallyEq hev, (hδ t hmem').2⟩

omit [CompleteSpace E] in
lemma curveOn_shift [CompleteSpace E] {V : E → E} {S : Set E} {γ : ℝ → E} {ε s : ℝ}
    (hγ : CurveOn V S γ (Ioo (-ε) ε)) :
    CurveOn V S (fun t => γ (t - s)) (Ioo (s - ε) (s + ε)) := by
  intro t ht
  have hm : t - s ∈ Ioo (-ε) ε := by constructor <;> linarith [ht.1, ht.2]
  refine ⟨?_, (hγ (t - s) hm).2⟩
  simpa [Function.comp_def] using! (hγ (t - s) hm).1.scomp t ((hasDerivAt_id t).sub_const s)

lemma global_from_intervals {V : E → E} {S : Set E} {x : E}
    (hV : ∀ p ∈ S, ContDiffAt ℝ 1 V p)
    (h : ∀ a : ℝ, ∃ γ : ℝ → E, γ 0 = x ∧ CurveOn V S γ (Ioo (-a) a)) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (V (γ t)) t ∧ γ t ∈ S := by
  choose γ hγ0 hγ using h
  have hEq {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) : EqOn (γ b) (γ a) (Ioo (-b) b) := by
    apply unique_Ioo hV ⟨by linarith, hb⟩ (hγ b)
      ((hγ a).mono (Ioo_subset_Ioo (neg_le_neg hba) hba))
    rw [hγ0, hγ0]
  let Γ : ℝ → E := fun t => γ (|t| + 1) t
  have hΓ {a : ℝ} : EqOn Γ (γ a) (Ioo (-a) a) := by
    intro t ht
    by_cases hlt : |t| + 1 < a
    · exact hEq (by positivity) hlt.le (abs_lt.mp (lt_add_one _))
    · exact (hEq (by linarith [ht.1, ht.2]) (le_of_not_gt hlt) ht).symm
  refine ⟨Γ, hγ0 _, fun t => ?_⟩
  have ht : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := abs_lt.mp (lt_add_one _)
  have hev : Γ =ᶠ[𝓝 t] γ (|t| + 1) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hΓ hs
  rw [hev.self_of_nhds]
  exact ⟨(hγ _ t ht).1.congr_of_eventuallyEq hev, (hγ _ t ht).2⟩

theorem global_of_compact_containment {V : E → E} {S : Set E} {x : E}
    (hS : IsOpen S) (hx : x ∈ S) (hV : ∀ p ∈ S, ContDiffAt ℝ 1 V p)
    (hcontain : ∀ T : ℝ, 0 < T → ∃ K : Set E, IsCompact K ∧ K ⊆ S ∧
      ∀ (a : ℝ) (γ : ℝ → E), 0 < a → γ 0 = x → CurveOn V S γ (Ioo (-a) a) →
        ∀ t ∈ Ioo (-a) a, |t| ≤ T → γ t ∈ K) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (V (γ t)) t ∧ γ t ∈ S := by
  classical
  let s : Set ℝ := {a | ∃ γ : ℝ → E, γ 0 = x ∧ CurveOn V S γ (Ioo (-a) a)}
  obtain ⟨r, hr, ε₀, hε₀, H₀⟩ := local_uniform hS hx (hV x hx)
  have hs₀ : ε₀ ∈ s := H₀ x (mem_closedBall_self hr.le)
  suffices hn : ¬BddAbove s by
    rw [not_bddAbove_iff] at hn
    apply global_from_intervals hV
    intro a
    obtain ⟨b, ⟨γ, hγ0, hγ⟩, hab⟩ := hn a
    exact ⟨γ, hγ0, hγ.mono (Ioo_subset_Ioo (neg_le_neg hab.le) hab.le)⟩
  intro hbdd
  let T := sSup s
  have hε₀T : ε₀ ≤ T := le_csSup hbdd hs₀
  have hT : 0 < T := hε₀.trans_le hε₀T
  obtain ⟨K, hK, hKS, hbound⟩ := hcontain T hT
  obtain ⟨d, hd, H⟩ := compact_uniform hS hV hK hKS
  let ε := min d T
  have hε : 0 < ε := lt_min hd hT
  have hεd : ε ≤ d := min_le_left _ _
  have hεT : ε ≤ T := min_le_right _ _
  have H' : ∀ y ∈ K, ∃ γ : ℝ → E, γ 0 = y ∧ CurveOn V S γ (Ioo (-ε) ε) := by
    intro y hy
    obtain ⟨γ, hγ0, hγ⟩ := H y hy
    exact ⟨γ, hγ0, hγ.mono (Ioo_subset_Ioo (neg_le_neg hεd) hεd)⟩
  obtain ⟨a, ha, hlt⟩ := Real.add_neg_lt_sSup (⟨ε₀, hs₀⟩ : s.Nonempty)
    (ε := -(ε / 2)) (by linarith)
  change T + -(ε / 2) < a at hlt
  obtain ⟨γ, hγ0, hγ⟩ := ha
  have ha0 : 0 < a := by linarith
  have htpos : 0 < T - ε / 2 := by linarith
  have ht : T - ε / 2 ∈ Ioo (-a) a := by constructor <;> linarith
  have hnt : -(T - ε / 2) ∈ Ioo (-a) a := by constructor <;> linarith
  obtain ⟨γ₁, hγ₁0, hγ₁⟩ := H' (γ (-(T - ε / 2)))
    (hbound a γ ha0 hγ0 hγ _ hnt (by rw [abs_neg, abs_of_pos htpos]; linarith))
  obtain ⟨γ₂, hγ₂0, hγ₂⟩ := H' (γ (T - ε / 2))
    (hbound a γ ha0 hγ0 hγ _ ht (by rw [abs_of_pos htpos]; linarith))
  let δ₁ : ℝ → E := fun t => γ₁ (t - -(T - ε / 2))
  let δ₂ : ℝ → E := fun t => γ₂ (t - (T - ε / 2))
  have hd₁ : CurveOn V S δ₁ (Ioo (-(T - ε / 2) - ε) (-(T - ε / 2) + ε)) :=
    curveOn_shift hγ₁
  have hd₂ : CurveOn V S δ₂ (Ioo ((T - ε / 2) - ε) ((T - ε / 2) + ε)) :=
    curveOn_shift hγ₂
  have he₁ : γ (-(T - ε / 2)) = δ₁ (-(T - ε / 2)) := by simp [δ₁, hγ₁0]
  have he₂ : γ (T - ε / 2) = δ₂ (T - ε / 2) := by simp [δ₂, hγ₂0]
  let γleft : ℝ → E := piecewise (Ioo (-a) a) γ δ₁
  have hleft : CurveOn V S γleft (Ioo (-(T + ε / 2)) a) := by
    apply (curveOn_piecewise hV hγ hd₁ ⟨hnt, ⟨by linarith, by linarith⟩⟩ he₁).mono
    intro t ht'
    by_cases hta : -a < t
    · exact Or.inl ⟨hta, ht'.2⟩
    · right
      constructor <;> linarith [ht'.1, le_of_not_gt hta]
  let Γ : ℝ → E := piecewise (Ioo (-(T + ε / 2)) a) γleft δ₂
  have hext : CurveOn V S Γ (Ioo (-(T + ε / 2)) (T + ε / 2)) := by
    apply (curveOn_piecewise hV hleft hd₂
      ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      (show γleft (T - ε / 2) = δ₂ (T - ε / 2) from by
        simpa only [γleft, piecewise, ite_eq_left ht] using he₂)).mono
    intro t ht'
    by_cases hta : t < a
    · exact Or.inl ⟨ht'.1, hta⟩
    · right
      constructor <;> linarith [ht'.2, le_of_not_gt hta]
  have hΓ0 : Γ 0 = x := by
    have houter : (0 : ℝ) ∈ Ioo (-(T + ε / 2)) a := ⟨by linarith, ha0⟩
    have hinner : (0 : ℝ) ∈ Ioo (-a) a := ⟨by linarith, ha0⟩
    simp only [Γ, γleft, piecewise, ite_eq_left houter, ite_eq_left hinner, hγ0]
  have hend : T + ε / 2 ∈ s := ⟨Γ, hΓ0, hext⟩
  have := le_csSup hbdd hend
  change T + ε / 2 ≤ T at this
  linarith

omit [CompleteSpace E] in
lemma contDiff_of_hasDerivAt [CompleteSpace E] {V : E → E} {γ : ℝ → E}
    (hV : ∀ t, ContDiffAt ℝ ∞ V (γ t))
    (hγ : ∀ t, HasDerivAt γ (V (γ t)) t) : ContDiff ℝ ∞ γ := by
  have hd : deriv γ = V ∘ γ := funext fun t => (hγ t).deriv
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt)
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
    refine ⟨fun t => (hγ t).differentiableAt, by simp, ?_⟩
    rw [hd]
    apply contDiff_iff_contDiffAt.mpr
    intro t
    exact ((hV t).of_le (by exact WithTop.coe_le_coe.mpr le_top)).comp t ih.contDiffAt

end CompactODE

namespace PinchedHartogs

theorem hartogsMetric_geodesicallyComplete {φ : Base → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ ball) (hpsh : IsPshBase φ) {lam : ℝ} (hlam : 0 < lam) :
    GeodesicallyComplete (hartogs φ) (hartogsMetric φ lam) := by
  intro p hp v
  let g := hartogsMetric φ lam
  have hg := hartogsMetric_isKahler hφ hpsh hlam
  have hM := hartogs_isOpen_smooth hφ
  have hS : IsOpen (hartogs φ ×ˢ (univ : Set Ambient)) := hM.prod isOpen_univ
  have hV (y : Ambient × Ambient) (hy : y ∈ hartogs φ ×ˢ (univ : Set Ambient)) :
      ContDiffAt ℝ 1 (geodesicField g) y :=
    (geodesicField_contDiffAt hM hg hy.1).of_le (by simp)
  obtain ⟨y, hy0, hy⟩ := CompactODE.global_of_compact_containment hS
    (show (p, v) ∈ hartogs φ ×ˢ (univ : Set Ambient) from ⟨hp, mem_univ _⟩) hV (by
      intro T hT
      obtain ⟨K, hK, hKS, hB⟩ := hartogs_geodesic_compact_containment hφ hpsh hlam hp v hT
      refine ⟨K, hK, hKS, ?_⟩
      intro a y ha hy0 hy t ht htT
      exact hB a y ha hy0 (fun s hs => ⟨(hy s hs).1, (hy s hs).2.1⟩) t ht htT)
  have hys : ContDiff ℝ ∞ y := CompactODE.contDiff_of_hasDerivAt
    (fun t => geodesicField_contDiffAt hM hg (hy t).2.1) (fun t => (hy t).1)
  let γ : ℝ → Ambient := fun t => (y t).1
  have hγ (t : ℝ) : HasDerivAt γ (y t).2 t := (hy t).1.fst
  have hν (t : ℝ) : HasDerivAt (fun s => (y s).2) (geodesicAcceleration g (y t).1 (y t).2) t :=
    (hy t).1.snd
  have hdγ : deriv γ = fun t => (y t).2 := funext fun t => (hγ t).deriv
  refine ⟨γ, contDiff_fst.comp hys, (fun t => (hy t).2.1), ?_, ?_, ?_⟩
  · exact congrArg Prod.fst hy0
  · rw [hdγ]
    exact congrArg Prod.snd hy0
  · intro t k
    rw [hdγ, (hν t).deriv]
    simp only [geodesicAcceleration, coordinates_equiv_symm, g, γ, neg_add_cancel]

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsTopologySupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology Metric
open scoped ContDiff NNReal
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs

theorem hartogs_contractible (φ : Base → ℝ) (hφ : ContinuousOn φ ball) :
    ContractibleSpace (hartogs φ) := by
  let : ContractibleSpace ball := by
    rw [ball_eq]
    exact (convex_ball (0 : Base) 1).contractibleSpace ⟨0, by simp⟩
  let : ContractibleSpace (Metric.ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, by simp⟩
  exact (hartogsHomeomorph φ hφ).contractibleSpace

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology Metric
open scoped ContDiff NNReal
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs

theorem metric_transfer_oai : MetricTransfer := by
  intro c C hc hC
  refine ⟨metricThreshold c C,metricThreshold_pos hc hC,?_⟩
  intro φ hφ hctl hj lam hlam
  have hpsh := chartControl_psh hφ hc.le hctl
  have hlp := (metricThreshold_pos hc hC).trans_le hlam
  exact ⟨hartogs_contractible φ hφ.continuousOn, hartogsMetric_isKahler hφ hpsh hlp,
    hartogsMetric_geodesicallyComplete hφ hpsh hlp,
    hartogsMetric_uniform_pinching hφ hc hC hctl hj hlam⟩

end PinchedHartogs

end

end OAI
end

theorem solution : type_of% @OAI.PinchedHartogs.metric_transfer_oai := @OAI.PinchedHartogs.metric_transfer_oai
