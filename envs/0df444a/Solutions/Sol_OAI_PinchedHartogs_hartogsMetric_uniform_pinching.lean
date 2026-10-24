-- Prove2me | solution 1 for OAI.PinchedHartogs.hartogsMetric_uniform_pinching
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:11:52.315426+00:00
-- url     : https://prove2.me/submissions/daca15b6-27cc-48d6-a7d8-a396250c4e07

import Mathlib
import Definitions.Def_PinchedKahler
import Definitions.Def_OAIQWPH001
import Theorems.Thm_OAI_PinchedHartogs_normalPotentials_uniform_pinching

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

lemma dbar_sum {ι : Type uKahler2080_1} (s : Finset ι) {f : ι → Ambient → ℂ} {p : Ambient}
    (hf : ∀ j ∈ s, DifferentiableAt ℝ (f j) p) (i : Fin 3) :
    dbar (fun q => ∑ j ∈ s, f j q) p i = ∑ j ∈ s, dbar (f j) p i := by
  simp only [dbar, fderiv_fun_sum hf, sum_apply,
    Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]

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

lemma matrix_diff_entry {g : Ambient → CMatrix} {p : Ambient}
    (hg : DifferentiableAt ℝ g p) (i j : Fin 3) :
    DifferentiableAt ℝ (fun q => g q i j) p :=
  differentiableAt_pi.mp (differentiableAt_pi.mp hg i) j

lemma matrix_diff_mul {f g : Ambient → CMatrix} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    DifferentiableAt ℝ (fun q => f q * g q) p := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  change DifferentiableAt ℝ (fun q => ∑ k, f q i k * g q k j) p
  exact DifferentiableAt.fun_sum fun k hk => (matrix_diff_entry hf i k).mul (matrix_diff_entry hg k j)

lemma dzMatrix_mul {f g : Ambient → CMatrix} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (a : Fin 3) :
    dzMatrix (fun q => f q * g q) p a = dzMatrix f p a * g p + f p * dzMatrix g p a := by
  ext i j
  change dz (fun q => ∑ k, f q i k * g q k j) p a =
    (∑ k, dz (fun q => f q i k) p a * g p k j) +
      ∑ k, f p i k * dz (fun q => g q k j) p a
  have hs := dz_sum Finset.univ (fun k hk =>
    (matrix_diff_entry hf i k).mul (matrix_diff_entry hg k j)) a
  change dz (fun q => ∑ k, f q i k * g q k j) p a = _ at hs
  rw [hs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact dz_mul (matrix_diff_entry hf i k) (matrix_diff_entry hg k j) a

lemma dbarMatrix_mul {f g : Ambient → CMatrix} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (a : Fin 3) :
    dbarMatrix (fun q => f q * g q) p a = dbarMatrix f p a * g p + f p * dbarMatrix g p a := by
  ext i j
  change dbar (fun q => ∑ k, f q i k * g q k j) p a =
    (∑ k, dbar (fun q => f q i k) p a * g p k j) +
      ∑ k, f p i k * dbar (fun q => g q k j) p a
  have hs := dbar_sum Finset.univ (fun k hk =>
    (matrix_diff_entry hf i k).mul (matrix_diff_entry hg k j)) a
  change dbar (fun q => ∑ k, f q i k * g q k j) p a = _ at hs
  rw [hs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact dbar_mul (matrix_diff_entry hf i k) (matrix_diff_entry hg k j) a

lemma dbarMatrix_add {f g : Ambient → CMatrix} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (a : Fin 3) :
    dbarMatrix (fun q => f q + g q) p a = dbarMatrix f p a + dbarMatrix g p a := by
  ext i j
  exact dbar_add (matrix_diff_entry hf i j) (matrix_diff_entry hg i j) a

lemma dzMatrix_congr {f g : Ambient → CMatrix} {p : Ambient}
    (h : f =ᶠ[𝓝 p] g) (a : Fin 3) : dzMatrix f p a = dzMatrix g p a := by
  ext i j
  exact dz_congr (h.mono fun q hq => congrFun (congrFun hq i) j) a

lemma dbarMatrix_congr {f g : Ambient → CMatrix} {p : Ambient}
    (h : f =ᶠ[𝓝 p] g) (a : Fin 3) : dbarMatrix f p a = dbarMatrix g p a := by
  ext i j
  exact dbar_congr (h.mono fun q hq => congrFun (congrFun hq i) j) a

lemma matrix_contDiffAt_dz {g : Ambient → CMatrix} {p : Ambient} {m n : WithTop ℕ∞}
    (hg : ContDiffAt ℝ n g p) (hm : m + 1 ≤ n) (a : Fin 3) :
    ContDiffAt ℝ m (fun q => dzMatrix g q a) p := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact _root_.OAI.ContDiffAt.hartogs_dz (contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j) hm a

lemma curvatureMatrix_apply (g : Ambient → CMatrix) (p : Ambient) (a b c d : Fin 3) :
    curvatureMatrix g p a b c d = curvature g p a b c d := by
  simp only [curvatureMatrix, curvature, Matrix.neg_apply, Matrix.add_apply,
    Matrix.mul_apply, dzMatrix, dbarMatrix, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma gauge_curvature_algebra (A M B Az Mz Mb Bb Mzb : CMatrix)
    (hA : A.det ≠ 0) (hM : M.det ≠ 0) (hB : B.det ≠ 0) :
    -(Az * Mb * B + A * Mzb * B + (Az * M + A * Mz) * Bb) +
      (Az * M + A * Mz) * B * (A * M * B)⁻¹ * (A * Mb * B + A * M * Bb) =
        A * (-Mzb + Mz * M⁻¹ * Mb) * B := by
  have hA' : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hM' : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have hB' : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  simp only [Matrix.mul_inv_rev, mul_add, add_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left B _ hB',
    Matrix.nonsing_inv_mul_cancel_left A _ hA',
    Matrix.mul_nonsing_inv_cancel_left M _ hM',
    Matrix.nonsing_inv_mul_cancel_left M _ hM']
  noncomm_ring

lemma curvatureMatrix_gauge {A M B : Ambient → CMatrix} {p : Ambient}
    (hA : ContDiffAt ℝ 2 A p) (hM : ContDiffAt ℝ 2 M p) (hB : ContDiffAt ℝ 2 B p)
    (hAdbar : ∀ᶠ q in 𝓝 p, ∀ a, dbarMatrix A q a = 0)
    (hBdz : ∀ᶠ q in 𝓝 p, ∀ a, dzMatrix B q a = 0)
    (hAdet : (A p).det ≠ 0) (hMdet : (M p).det ≠ 0) (hBdet : (B p).det ≠ 0)
    (a b : Fin 3) :
    curvatureMatrix (fun q => A q * M q * B q) p a b =
      A p * curvatureMatrix M p a b * B p := by
  have hAd := hA.differentiableAt (by norm_num)
  have hMd := hM.differentiableAt (by norm_num)
  have hBd := hB.differentiableAt (by norm_num)
  have hAzd := (matrix_contDiffAt_dz hA (m := 1) (by norm_num) a).differentiableAt (by norm_num)
  have hMzd := (matrix_contDiffAt_dz hM (m := 1) (by norm_num) a).differentiableAt (by norm_num)
  have hAb : dbarMatrix A p b = 0 := (hAdbar.self_of_nhds) b
  have hBza : dzMatrix B p a = 0 := (hBdz.self_of_nhds) a
  have hAzb : dbarMatrix (fun q => dzMatrix A q a) p b = 0 := by
    ext i j
    change dbar (fun q => dz (fun r => A r i j) q a) p b = 0
    rw [← dz_dbar_comm (contDiffAt_pi.mp (contDiffAt_pi.mp hA i) j) a b]
    have he : (fun q => dbar (fun r => A r i j) q b) =ᶠ[𝓝 p] (fun _ => 0) := by
      filter_upwards [hAdbar] with q hq
      exact congrFun (congrFun (hq b) i) j
    rw [dz_congr he]
    simp [dz]
  have hfirst : (fun q => dzMatrix (fun r => A r * M r * B r) q a) =ᶠ[𝓝 p]
      (fun q => (dzMatrix A q a * M q + A q * dzMatrix M q a) * B q) := by
    filter_upwards [hA.eventually (by norm_num), hM.eventually (by norm_num),
      hB.eventually (by norm_num), hBdz] with q hAq hMq hBq hBzq
    rw [dzMatrix_mul (matrix_diff_mul (hAq.differentiableAt (by norm_num))
      (hMq.differentiableAt (by norm_num))) (hBq.differentiableAt (by norm_num)),
      dzMatrix_mul (hAq.differentiableAt (by norm_num)) (hMq.differentiableAt (by norm_num)),
      hBzq a, mul_zero, add_zero]
  have hsecond : dbarMatrix (fun q => dzMatrix (fun r => A r * M r * B r) q a) p b =
      dzMatrix A p a * dbarMatrix M p b * B p +
      A p * dbarMatrix (fun q => dzMatrix M q a) p b * B p +
      (dzMatrix A p a * M p + A p * dzMatrix M p a) * dbarMatrix B p b := by
    have hsumd : DifferentiableAt ℝ
        (fun q => dzMatrix A q a * M q + A q * dzMatrix M q a) p :=
      (matrix_diff_mul hAzd hMd).add (matrix_diff_mul hAd hMzd)
    rw [dbarMatrix_congr hfirst,
      dbarMatrix_mul hsumd hBd,
      dbarMatrix_add (matrix_diff_mul hAzd hMd) (matrix_diff_mul hAd hMzd),
      dbarMatrix_mul hAzd hMd, dbarMatrix_mul hAd hMzd, hAzb, hAb]
    simp only [zero_mul, zero_add, add_mul]
  have hbar : dbarMatrix (fun q => A q * M q * B q) p b =
      A p * dbarMatrix M p b * B p + A p * M p * dbarMatrix B p b := by
    rw [dbarMatrix_mul (matrix_diff_mul hAd hMd) hBd, dbarMatrix_mul hAd hMd, hAb]
    simp only [zero_mul, zero_add]
  have hpoint : dzMatrix (fun q => A q * M q * B q) p a =
      (dzMatrix A p a * M p + A p * dzMatrix M p a) * B p := hfirst.self_of_nhds
  unfold curvatureMatrix
  rw [hsecond, hpoint, hbar]
  exact gauge_curvature_algebra _ _ _ _ _ _ _ _ hAdet hMdet hBdet

lemma dbarMatrix_smul {f : Ambient → ℂ} {g : Ambient → CMatrix} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (a : Fin 3) :
    dbarMatrix (fun q => f q • g q) p a = dbar f p a • g p + f p • dbarMatrix g p a := by
  ext i j
  exact dbar_mul hf (matrix_diff_entry hg i j) a

lemma dbarMatrix_sum {ι : Type uKahler2312_1} (s : Finset ι) {f : ι → Ambient → CMatrix} {p : Ambient}
    (hf : ∀ k ∈ s, DifferentiableAt ℝ (f k) p) (a : Fin 3) :
    dbarMatrix (fun q => ∑ k ∈ s, f k q) p a = ∑ k ∈ s, dbarMatrix (f k) p a := by
  ext i j
  simpa only [dbarMatrix, Matrix.of_apply, Matrix.sum_apply] using
    dbar_sum s (fun k hk => matrix_diff_entry (hf k hk) i j) a

lemma dzMatrix_comp_holomorphic {g : Ambient → CMatrix} {F : Ambient → Ambient} {p : Ambient}
    (hg : DifferentiableAt ℝ g (F p)) (hF : DifferentiableAt ℂ F p) (a : Fin 3) :
    dzMatrix (g ∘ F) p a = ∑ e, complexJacobian F p e a • dzMatrix g (F p) e := by
  ext i j
  simpa only [dzMatrix, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    mul_comm, Function.comp_def] using dz_comp_holomorphic (matrix_diff_entry hg i j) hF a

lemma dbarMatrix_comp_holomorphic {g : Ambient → CMatrix} {F : Ambient → Ambient} {p : Ambient}
    (hg : DifferentiableAt ℝ g (F p)) (hF : DifferentiableAt ℂ F p) (a : Fin 3) :
    dbarMatrix (g ∘ F) p a = ∑ e, star (complexJacobian F p e a) • dbarMatrix g (F p) e := by
  ext i j
  simpa only [dbarMatrix, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    mul_comm, Function.comp_def] using dbar_comp_holomorphic (matrix_diff_entry hg i j) hF a

lemma curvatureMatrix_comp_holomorphic {g : Ambient → CMatrix} {F : Ambient → Ambient}
    {p : Ambient} (hg : ContDiffAt ℝ 2 g (F p)) (hF : AnalyticAt ℂ F p) (a b : Fin 3) :
    curvatureMatrix (g ∘ F) p a b = ∑ e, ∑ f,
      (complexJacobian F p e a * star (complexJacobian F p f b)) •
        curvatureMatrix g (F p) e f := by
  have hgd := hg.differentiableAt (by norm_num)
  have hFd := hF.differentiableAt
  have hJ (e i : Fin 3) := (complexJacobian_analyticAt hF e i).differentiableAt
  have hgzd (e : Fin 3) :=
    (matrix_contDiffAt_dz hg (m := 1) (by norm_num) e).differentiableAt (by norm_num)
  have hgzF (e : Fin 3) := (hgzd e).comp p (hFd.restrictScalars ℝ)
  have he : (fun q => dzMatrix (g ∘ F) q a) =ᶠ[𝓝 p]
      (fun q => ∑ e, complexJacobian F q e a • dzMatrix g (F q) e) := by
    filter_upwards [hF.eventually_analyticAt,
      hFd.continuousAt (hg.eventually (by norm_num))] with q hFq hgq
    change ContDiffAt ℝ 2 g (F q) at hgq
    exact dzMatrix_comp_holomorphic (hgq.differentiableAt (by norm_num)) hFq.differentiableAt a
  have hsecond : dbarMatrix (fun q => dzMatrix (g ∘ F) q a) p b =
      ∑ e, ∑ f, (complexJacobian F p e a * star (complexJacobian F p f b)) •
        dbarMatrix (fun q => dzMatrix g q e) (F p) f := by
    rw [dbarMatrix_congr he]
    have hs := dbarMatrix_sum Finset.univ
      (fun e he => ((hJ e a).restrictScalars ℝ).smul (hgzF e)) b
    change dbarMatrix (fun q => ∑ e, complexJacobian F q e a • dzMatrix g (F q) e) p b = _ at hs
    rw [hs]
    apply Finset.sum_congr rfl
    intro e he
    have hm := dbarMatrix_smul ((hJ e a).restrictScalars ℝ) (hgzF e) b
    change dbarMatrix (fun q => complexJacobian F q e a • dzMatrix g (F q) e) p b = _ at hm
    change dbarMatrix (fun q => complexJacobian F q e a • dzMatrix g (F q) e) p b = _
    rw [hm, dbar_holomorphic (hJ e a), zero_smul, zero_add,
      dbarMatrix_comp_holomorphic (hgzd e) hFd, Finset.smul_sum]
    simp only [smul_smul]
  unfold curvatureMatrix
  rw [hsecond, dzMatrix_comp_holomorphic hgd hFd, dbarMatrix_comp_holomorphic hgd hFd]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
    smul_add, smul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, Function.comp_apply,
    Finset.smul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro f hf
  rw [mul_comm (star (complexJacobian F p f b))]

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

lemma curvatureMatrix_pullback {g : Ambient → CMatrix} {F : Ambient → Ambient} {p : Ambient}
    (hg : ContDiffAt ℝ 2 g (F p)) (hF : AnalyticAt ℂ F p)
    (hgdet : (g (F p)).det ≠ 0) (hJdet : (jacobianMatrix F p).det ≠ 0) (a b : Fin 3) :
    curvatureMatrix (pullbackMetric g F) p a b =
      (jacobianMatrix F p)ᵀ * (∑ e, ∑ f,
        (complexJacobian F p e a * star (complexJacobian F p f b)) •
          curvatureMatrix g (F p) e f) * (jacobianMatrix F p)ᵀᴴ := by
  have hAa (i j : Fin 3) : AnalyticAt ℂ (fun q => (jacobianMatrix F q)ᵀ i j) p :=
    complexJacobian_analyticAt hF j i
  have hA : ContDiffAt ℝ 2 (fun q => (jacobianMatrix F q)ᵀ) p := by
    exact contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j =>
      (hAa i j).contDiffAt.restrict_scalars ℝ
  have hB : ContDiffAt ℝ 2 (fun q => (jacobianMatrix F q)ᵀᴴ) p := by
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    exact Complex.conjCLE.toContinuousLinearMap.contDiff.contDiffAt.comp p
      ((hAa j i).contDiffAt (n := 2) |>.restrict_scalars ℝ)
  have hM : ContDiffAt ℝ 2 (g ∘ F) p :=
    hg.comp p (hF.contDiffAt.restrict_scalars ℝ)
  have hAdb : ∀ᶠ q in 𝓝 p, ∀ i, dbarMatrix (fun r => (jacobianMatrix F r)ᵀ) q i = 0 := by
    filter_upwards [hF.eventually_analyticAt] with q hq
    intro i
    ext e f
    exact dbar_holomorphic (complexJacobian_analyticAt hq f e).differentiableAt i
  have hBdz : ∀ᶠ q in 𝓝 p, ∀ i, dzMatrix (fun r => (jacobianMatrix F r)ᵀᴴ) q i = 0 := by
    filter_upwards [hF.eventually_analyticAt] with q hq
    intro i
    ext e f
    change dz (fun r => star (complexJacobian F r e f)) q i = 0
    rw [dz_conj ((complexJacobian_analyticAt hq e f).differentiableAt.restrictScalars ℝ),
      dbar_holomorphic (complexJacobian_analyticAt hq e f).differentiableAt, star_zero]
  have hAne : (jacobianMatrix F p)ᵀ.det ≠ 0 := by simpa only [Matrix.det_transpose] using hJdet
  have hBne : (jacobianMatrix F p)ᵀᴴ.det ≠ 0 := by
    simpa only [Matrix.det_conjTranspose, star_ne_zero] using hAne
  have hh := curvatureMatrix_gauge hA hM hB hAdb hBdz hAne hgdet hBne a b
  change curvatureMatrix (pullbackMetric g F) p a b =
    (jacobianMatrix F p)ᵀ * curvatureMatrix (g ∘ F) p a b * (jacobianMatrix F p)ᵀᴴ at hh
  rw [hh, curvatureMatrix_comp_holomorphic hg hF]

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

lemma matrixPull_apply (A h : CMatrix) (i j : Fin 3) :
    matrixPull A h i j = ∑ a, ∑ b, h a b * A a i * star (A b j) := by
  simp only [matrixPull, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

lemma hermitianValue_sum {ι : Type uKahler2472_1} (s : Finset ι) (h : ι → CMatrix) (u v : Ambient) :
    hermitianValue (∑ k ∈ s, h k) u v = ∑ k ∈ s, hermitianValue (h k) u v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermitianValue]
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk, hermitianValue, Matrix.add_apply, add_mul,
      Finset.sum_add_distrib] at *
    rw [ih]

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

lemma tensorValue_as_hermitianValue (R : CurvatureTensor) (u v w y : Ambient) :
    tensorValue R u v w y = hermitianValue (tensorPairMatrix R w y) u v := by
  simp only [tensorValue, hermitianValue, tensorPairMatrix, Matrix.of_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  ring

lemma tensorPairMatrix_curvature_apply (g : Ambient → CMatrix) (p w y : Ambient) (a b : Fin 3) :
    tensorPairMatrix (curvature g p) w y a b = hermitianValue (curvatureMatrix g p a b) w y := by
  have he : Matrix.of (curvature g p a b) = curvatureMatrix g p a b := by
    ext c d
    exact (curvatureMatrix_apply g p a b c d).symm
  change hermitianValue (Matrix.of (curvature g p a b)) w y = _
  rw [he]

lemma tensorPairMatrix_pullback {g : Ambient → CMatrix} {F : Ambient → Ambient} {p : Ambient}
    (hg : ContDiffAt ℝ 2 g (F p)) (hF : AnalyticAt ℂ F p)
    (hgdet : (g (F p)).det ≠ 0) (hJdet : (jacobianMatrix F p).det ≠ 0) (w y : Ambient) :
    tensorPairMatrix (curvature (pullbackMetric g F) p) w y =
      matrixPull (jacobianMatrix F p) (tensorPairMatrix (curvature g (F p))
        (matrixPush (jacobianMatrix F p) w) (matrixPush (jacobianMatrix F p) y)) := by
  ext a b
  rw [tensorPairMatrix_curvature_apply, curvatureMatrix_pullback hg hF hgdet hJdet]
  change hermitianValue (matrixPull (jacobianMatrix F p) _) w y = _
  rw [hermitianValue_matrixPull, matrixPull_apply]
  simp only [hermitianValue_sum, hermitianValue_smul]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro f hf
  rw [tensorPairMatrix_curvature_apply]
  change (complexJacobian F p e a * star (complexJacobian F p f b)) * _ =
    _ * complexJacobian F p e a * star (complexJacobian F p f b)
  ring

lemma tensorValue_curvature_pullback {g : Ambient → CMatrix} {F : Ambient → Ambient} {p : Ambient}
    (hg : ContDiffAt ℝ 2 g (F p)) (hF : AnalyticAt ℂ F p)
    (hgdet : (g (F p)).det ≠ 0) (hJdet : (jacobianMatrix F p).det ≠ 0) (u v w y : Ambient) :
    tensorValue (curvature (pullbackMetric g F) p) u v w y =
      tensorValue (curvature g (F p)) (fderiv ℂ F p u) (fderiv ℂ F p v)
        (fderiv ℂ F p w) (fderiv ℂ F p y) := by
  rw [tensorValue_as_hermitianValue, tensorPairMatrix_pullback hg hF hgdet hJdet,
    hermitianValue_matrixPull, ← tensorValue_as_hermitianValue]
  simp only [matrixPush_jacobian]

lemma hermitianValue_pullback (g : Ambient → CMatrix) (F : Ambient → Ambient) (p u v : Ambient) :
    hermitianValue (pullbackMetric g F p) u v =
      hermitianValue (g (F p)) (fderiv ℂ F p u) (fderiv ℂ F p v) := by
  change hermitianValue (matrixPull (jacobianMatrix F p) (g (F p))) u v = _
  rw [hermitianValue_matrixPull, matrixPush_jacobian, matrixPush_jacobian]

lemma sectional_pullback {g : Ambient → CMatrix} {F : Ambient → Ambient} {p : Ambient}
    (hg : ContDiffAt ℝ 2 g (F p)) (hF : AnalyticAt ℂ F p)
    (hgdet : (g (F p)).det ≠ 0) (hJdet : (jacobianMatrix F p).det ≠ 0) (u v : Ambient) :
    sectional (pullbackMetric g F) p u v =
      sectional g (F p) (fderiv ℂ F p u) (fderiv ℂ F p v) := by
  simp only [sectional, tensorValue_curvature_pullback hg hF hgdet hJdet, realArea,
    hermitianValue_pullback]

lemma curvatureMatrix_congr {g h : Ambient → CMatrix} {p : Ambient}
    (he : g =ᶠ[𝓝 p] h) (a b : Fin 3) : curvatureMatrix g p a b = curvatureMatrix h p a b := by
  have hz : (fun q => dzMatrix g q a) =ᶠ[𝓝 p] fun q => dzMatrix h q a :=
    he.eventually_nhds.mono fun q hq => dzMatrix_congr hq a
  have hp : g p = h p := he.self_of_nhds
  rw [curvatureMatrix, curvatureMatrix, dbarMatrix_congr hz,
    dzMatrix_congr he, dbarMatrix_congr he, hp]

lemma curvature_congr {g h : Ambient → CMatrix} {p : Ambient}
    (he : g =ᶠ[𝓝 p] h) : curvature g p = curvature h p := by
  funext a b c d
  rw [← curvatureMatrix_apply, ← curvatureMatrix_apply, curvatureMatrix_congr he]

lemma sectional_congr {g h : Ambient → CMatrix} {p : Ambient}
    (he : g =ᶠ[𝓝 p] h) (u v : Ambient) : sectional g p u v = sectional h p u v := by
  have hp : g p = h p := he.self_of_nhds
  rw [sectional, sectional, curvature_congr he, hp]

lemma sectional_complexHessian_comp {f : Ambient → ℝ} {F : Ambient → Ambient} {p : Ambient}
    (hf : ContDiffAt ℝ ∞ f (F p)) (hF : AnalyticAt ℂ F p)
    (hfdet : (complexHessian f (F p)).det ≠ 0) (hJdet : (jacobianMatrix F p).det ≠ 0)
    (u v : Ambient) :
    sectional (complexHessian (f ∘ F)) p u v =
      sectional (complexHessian f) (F p) (fderiv ℂ F p u) (fderiv ℂ F p v) := by
  have hf2 : ContDiffAt ℝ 2 f (F p) := hf.of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have he : complexHessian (f ∘ F) =ᶠ[𝓝 p] pullbackMetric (complexHessian f) F := by
    filter_upwards [hF.eventually_analyticAt,
      hF.differentiableAt.continuousAt (hf2.eventually (by norm_num))] with q hFq hfq
    change ContDiffAt ℝ 2 f (F q) at hfq
    exact complexHessian_pullback hfq hFq
  rw [sectional_congr he]
  exact sectional_pullback ((complexHessian_contDiffAt hf).of_le
    (by exact WithTop.coe_le_coe.mpr le_top)) hF hfdet hJdet u v

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

lemma logarithmicBarrier_contDiffAt {s : ℝ} (hs : s < 0) : ContDiffAt ℝ ∞ logarithmicBarrier s :=
  ((contDiffAt_const.sub Real.contDiff_exp.contDiffAt).log (barrier_den_ne_zero hs)).neg

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

lemma fiberGaugeMap_analyticAt {C : Base → Base} {P : Ambient → ℂ} {p : Ambient}
    (hC : AnalyticAt ℂ C p.1) (hP : AnalyticAt ℂ P p) :
    AnalyticAt ℂ (fiberGaugeMap C P) p := by
  have hc : AnalyticAt ℂ (fun q : Ambient => C q.1) p :=
    hC.comp ((ContinuousLinearMap.fst ℂ Base ℂ).analyticAt p)
  have hv : AnalyticAt ℂ (fun q : Ambient => q.2 - P q) p :=
    ((ContinuousLinearMap.snd ℂ Base ℂ).analyticAt p).sub hP
  exact hc.prod (analyticAt_cexp.comp hv)

lemma metricPotential_fiberGauge (φ : Base → ℝ) (C : Base → Base) (P : Ambient → ℂ)
    (lam : ℝ) (q : Ambient) :
    metricPotential φ lam (fiberGaugeMap C P q) =
      lam * psi (C q.1) + logarithmicBarrier (gaugeLogParameter φ C P q) := by
  simp only [metricPotential, fiberGaugeMap, logarithmicBarrier, gaugeLogParameter,
    Complex.norm_exp, Real.exp_add]
  rw [show Real.exp (2*(q.2-P q).re) = (Real.exp (q.2-P q).re)^2 by
    rw [show (2 : ℝ)*(q.2-P q).re = (q.2-P q).re + (q.2-P q).re by ring, Real.exp_add]; ring]
  ring

lemma gaugeLogParameter_neg {φ : Base → ℝ} {C : Base → Base} {P : Ambient → ℂ}
    {q : Ambient} (hq : fiberGaugeMap C P q ∈ hartogs φ) :
    gaugeLogParameter φ C P q < 0 := by
  have he : Real.exp (gaugeLogParameter φ C P q) =
      Real.exp (φ (C q.1)) * ‖Complex.exp (q.2-P q)‖^2 := by
    simp only [gaugeLogParameter, Real.exp_add, Complex.norm_exp]
    rw [show (2 : ℝ)*(q.2-P q).re = (q.2-P q).re + (q.2-P q).re by ring, Real.exp_add]
    ring
  exact Real.exp_lt_one_iff.mp (he.trans_lt hq.2)

lemma jacobianMatrix_det_of_fderiv_injective {F : Ambient → Ambient} {p : Ambient}
    (hF : Function.Injective (fderiv ℂ F p)) : (jacobianMatrix F p).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u v huv
  apply coordinateEquiv.symm.injective
  apply hF
  rw [← matrixPush_jacobian, ← matrixPush_jacobian]
  exact congrArg coordinateEquiv.symm huv

lemma fderiv_fiberGaugeMap {C : Base → Base} {P : Ambient → ℂ} {p : Ambient}
    (hC : DifferentiableAt ℂ C p.1) (hP : DifferentiableAt ℂ P p) (u : Ambient) :
    fderiv ℂ (fiberGaugeMap C P) p u =
      (fderiv ℂ C p.1 u.1, Complex.exp (p.2-P p) * (u.2 - fderiv ℂ P p u)) := by
  have hh : HasFDerivAt (fiberGaugeMap C P)
      ((fderiv ℂ C p.1).comp (ContinuousLinearMap.fst ℂ Base ℂ) |>.prod
        (Complex.exp (p.2-P p) • ((ContinuousLinearMap.snd ℂ Base ℂ) - fderiv ℂ P p))) p :=
    (hC.hasFDerivAt.comp p (ContinuousLinearMap.fst ℂ Base ℂ).hasFDerivAt).prodMk
      ((Complex.hasDerivAt_exp (p.2-P p)).comp_hasFDerivAt p
        ((ContinuousLinearMap.snd ℂ Base ℂ).hasFDerivAt.sub hP.hasFDerivAt))
  rw [hh.fderiv]
  rfl

lemma fderiv_gaugePolynomial_vertical (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ)
    (p : Ambient) (w : ℂ) : fderiv ℂ (gaugePolynomial a B) p (0,w) = 0 := by
  have hp := (gaugePolynomial_analytic a B p (mem_univ p)).differentiableAt
  have hr := (hp.hasFDerivAt.restrictScalars ℝ).fderiv
  have he := fderiv_wirtinger (gaugePolynomial a B) p (0,w)
  rw [hr] at he
  change fderiv ℂ (gaugePolynomial a B) p (0,w) = _ at he
  rw [he]
  simp only [dbar_holomorphic hp, dz_gaugePolynomial, coordinates, Fin.sum_univ_three]
  simp

lemma fderiv_fiberGaugeMap_injective {C : Base → Base} {p : Ambient}
    (hC : DifferentiableAt ℂ C p.1) (hCi : Function.Injective (fderiv ℂ C p.1))
    (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ) :
    Function.Injective (fderiv ℂ (fiberGaugeMap C (gaugePolynomial a B)) p) := by
  have hP := (gaugePolynomial_analytic a B p (mem_univ p)).differentiableAt
  let L := fderiv ℂ (gaugePolynomial a B) p
  have hv (u : Ambient) : L u = L (u.1,0) := by
    have he : u = (u.1,0) + (0,u.2) := by ext <;> simp
    conv_lhs => rw [he, map_add, fderiv_gaugePolynomial_vertical, add_zero]
  intro u v huv
  rw [fderiv_fiberGaugeMap hC hP, fderiv_fiberGaugeMap hC hP] at huv
  have hbase : u.1 = v.1 := hCi (congrArg Prod.fst huv)
  have hfib := congrArg Prod.snd huv
  have hexp := Complex.exp_ne_zero (p.2-gaugePolynomial a B p)
  have hd : L u = L v := by rw [hv u, hv v, hbase]
  have hvertical : u.2 = v.2 := by
    have h := mul_left_cancel₀ hexp hfib
    change u.2 - L u = v.2 - L v at h
    rw [hd] at h
    linear_combination h
  exact Prod.ext hbase hvertical

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

lemma baseGaugePolynomial_analytic (f : Base → ℝ) (w : ℂ) (q : Ambient) :
    AnalyticAt ℂ (baseGaugePolynomial f w) q := gaugePolynomial_analytic _ _ q (mem_univ _)

lemma normalLogWeight_contDiffAt {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ ∞ f q.1) (w : ℂ) : ContDiffAt ℝ ∞ (normalLogWeight f w) q := by
  have hP : AnalyticAt ℂ (fun q => baseGaugePolynomial f w q - q.2) q :=
    (baseGaugePolynomial_analytic f w q).sub ((ContinuousLinearMap.snd ℂ Base ℂ).analyticAt q)
  exact (hf.comp q contDiffAt_fst).sub
    (contDiffAt_const.mul (Complex.reCLM.contDiff.contDiffAt.comp q (hP.contDiffAt.restrict_scalars ℝ)))

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

lemma liftedHessian_horizontal_eventually {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (i j : Fin 2) :
    (fun r => liftedHessian f r i.castSucc j.castSucc) =ᶠ[𝓝 q]
      (fun r => baseHessian f r.1 i j) := by
  filter_upwards [continuousAt_fst.preimage_mem_nhds (hf.eventually (by norm_num))] with r hr
  change ContDiffAt ℝ 2 f r.1 at hr
  exact liftedHessian_horizontal hr i j

lemma liftedThird_horizontal {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 3 f q.1) (a c d : Fin 2) :
    liftedThird f q a.castSucc c.castSucc d.castSucc =
      dzBase (fun z => baseHessian f z c d) q.1 a := by
  have hd := (contDiffAt_pi.mp (contDiffAt_pi.mp (_root_.OAI.ContDiffAt.hartogs_baseHessian hf (m := 1) (by norm_num)) c) d).differentiableAt (by simp)
  rw [liftedThird, dz_congr (liftedHessian_horizontal_eventually (hf.of_le (by norm_num)) c d), dz_lift_base hd]
  fin_cases a <;> rfl

lemma liftedFourth_horizontal {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 4 f q.1) (a b c d : Fin 2) :
    liftedFourth f q a.castSucc b.castSucc c.castSucc d.castSucc =
      dzBase (fun z => dbarBase (fun t => baseHessian f t c d) z b) q.1 a := by
  have hc : ContDiffAt ℝ 2 (fun z => baseHessian f z c d) q.1 := contDiffAt_pi.mp (contDiffAt_pi.mp (_root_.OAI.ContDiffAt.hartogs_baseHessian hf (m := 2) (by norm_num)) c) d
  unfold liftedFourth liftedThird
  rw [dbar_dz_congr (liftedHessian_horizontal_eventually (hf.of_le (by norm_num)) c d)]
  erw [← dz_dbar_comm (hc.comp (f := fun r : Ambient => r.1) q contDiffAt_fst)]
  have he : (fun r : Ambient => dbar (fun t : Ambient => baseHessian f t.1 c d) r b.castSucc) =ᶠ[𝓝 q]
      (fun r => dbarBase (fun t => baseHessian f t c d) r.1 b) := by
    have hf2 := hc.of_le (show (2 : WithTop ℕ∞) ≤ 2 from le_rfl)
    filter_upwards [continuousAt_fst.preimage_mem_nhds (hf2.eventually (by norm_num))] with r hr
    change ContDiffAt ℝ 2 (fun z => baseHessian f z c d) r.1 at hr
    rw [dbar_lift_base (hr.differentiableAt (by norm_num))]
    fin_cases b <;> rfl
  erw [dz_congr he, dz_lift_base ((_root_.OAI.ContDiffAt.hartogs_dbarBase hc (m := 1) (by norm_num) b).differentiableAt (by norm_num))]
  fin_cases a <;> rfl

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

end HForm

end PlaneAlgebra
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

lemma metricThreshold_pos {c C : ℝ} (hc : 0 < c) (hC : c ≤ C) : 0 < metricThreshold c C := by
  exact lt_of_lt_of_le (show 0 < C+1 by linarith) (le_max_left _ _)

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsTransferTools
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

lemma euclidean_q_base (u : Fin 2 → ℂ) : euclidean.q u = ‖(WithLp.toLp 2 u : Base)‖^2 := by
  simp only [euclidean, HForm.q, form, Matrix.one_mulVec, dotProduct, Pi.star_apply]
  rw [PiLp.norm_sq_eq_of_L2, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, -Complex.ofReal_pow]

lemma form_q_base (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian) (u : Fin 2 → ℂ) :
    (form A hA).q u = (∑ i, ∑ j, A i j * u i * star (u j)).re := by
  simp only [HForm.q, form, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma chartControl_form_bounds {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    {c C : ℝ} (hctl : ChartControl φ c C) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) :
    (∀ u, c * euclidean.q u ≤ (form (baseHessian (φ ∘ centeredChart r U) 0)
      (baseHessian_isHermitian ((chartWeight_contDiffAt hφ hr hr1 U).of_le (WithTop.coe_le_coe.mpr le_top)))).q u) ∧
    (∀ u, (form (baseHessian (φ ∘ centeredChart r U) 0)
      (baseHessian_isHermitian ((chartWeight_contDiffAt hφ hr hr1 U).of_le (WithTop.coe_le_coe.mpr le_top)))).q u ≤ C*euclidean.q u) := by
  constructor <;> intro u <;> rw [euclidean_q_base, form_q_base]
  · exact (hctl r hr hr1 U (WithLp.toLp 2 u)).1
  · exact (hctl r hr hr1 U (WithLp.toLp 2 u)).2

lemma chartJets_lifted_bounds {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    {C : ℝ} (hj : ChartJets φ C) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) :
    (∀ i j k : Fin 2, ‖liftedThird (φ ∘ centeredChart r U) (0,0) i.castSucc j.castSucc k.castSucc‖ ≤ C) ∧
    (∀ i j k l : Fin 2, ‖liftedFourth (φ ∘ centeredChart r U) (0,0) i.castSucc j.castSucc k.castSucc l.castSucc‖ ≤ C) := by
  have hf := chartWeight_contDiffAt hφ hr hr1 U
  constructor
  · intro i j k
    rw [liftedThird_horizontal (hf.of_le (WithTop.coe_le_coe.mpr le_top))]
    have hh := hj r hr hr1 U j k i 0
    linarith only [hh, norm_nonneg (dbarBase (fun z => baseHessian (φ ∘ centeredChart r U) z j k) 0 0),
      norm_nonneg (dzBase (fun z => dbarBase (fun q => baseHessian (φ ∘ centeredChart r U) q j k) z 0) 0 i)]
  · intro i j k l
    rw [liftedFourth_horizontal (hf.of_le (WithTop.coe_le_coe.mpr le_top))]
    have hh := hj r hr hr1 U k l i j
    linarith only [hh, norm_nonneg (dzBase (fun z => baseHessian (φ ∘ centeredChart r U) z k l) 0 i),
      norm_nonneg (dbarBase (fun z => baseHessian (φ ∘ centeredChart r U) z k l) 0 j)]

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsGaugeTransfer
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
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
namespace PinchedHartogs
open PlaneAlgebra PlaneAlgebra.MatrixAlgebra PlaneAlgebra.TensorAlgebra Matrix

lemma gaugeLogParameter_normal (φ : Base → ℝ) (r : ℝ) (U : Base ≃ₗᵢ[ℂ] Base)
    (w : ℂ) : gaugeLogParameter φ (centeredChart r U) (baseGaugePolynomial (φ ∘ centeredChart r U) w) =
      normalLogWeight (φ ∘ centeredChart r U) w := by
  funext q
  simp only [gaugeLogParameter, normalLogWeight, Function.comp_apply, Complex.sub_re]
  ring

lemma metricPotential_normalGauge (φ : Base → ℝ) (r : ℝ) (U : Base ≃ₗᵢ[ℂ] Base)
    (lam : ℝ) (w : ℂ) :
    metricPotential φ lam ∘ fiberGaugeMap (centeredChart r U) (baseGaugePolynomial (φ ∘ centeredChart r U) w) =
      (fun q => lam * psi (centeredChart r U q.1) + logarithmicBarrier (normalLogWeight (φ ∘ centeredChart r U) w q)) := by
  funext q
  rw [Function.comp_apply, metricPotential_fiberGauge, gaugeLogParameter_normal]

lemma normalGauge_hessian_eventually {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (U : Base ≃ₗᵢ[ℂ] Base) (lam : ℝ) (w : ℂ)
    (hn : normalLogWeight (φ ∘ centeredChart r U) w (0,w) < 0) :
    complexHessian (metricPotential φ lam ∘ fiberGaugeMap (centeredChart r U)
        (baseGaugePolynomial (φ ∘ centeredChart r U) w)) =ᶠ[𝓝 (0,w)]
      complexHessian (normalPotential (φ ∘ centeredChart r U) lam w) := by
  rw [metricPotential_normalGauge]
  have hf := chartWeight_contDiffAt hφ hr hr1 U
  have hB : ContDiffAt ℝ 2 (logarithmicBarrier ∘ normalLogWeight (φ ∘ centeredChart r U) w) (0,w) :=
    ((logarithmicBarrier_contDiffAt hn).comp (0,w) (normalLogWeight_contDiffAt (q := (0,w)) hf w)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hp : ContDiffAt ℝ 2 (fun q : Ambient => psi q.1) (0,w) :=
    ((psi_contDiffAt zero_mem_ball).comp (0,w) contDiffAt_fst).of_le (WithTop.coe_le_coe.mpr le_top)
  have ht : ContDiffAt ℝ 2 (fun q : Ambient => psi (centeredChart r U q.1)) (0,w) :=
    (((psi_contDiffAt (centeredChart_zero_mem hr hr1 U)).comp 0
      ((centeredChart_analyticAt U (z := 0) (by simp)).contDiffAt.restrict_scalars ℝ)).comp
      (0,w) contDiffAt_fst).of_le (WithTop.coe_le_coe.mpr le_top)
  filter_upwards [hB.eventually (by norm_num), hp.eventually (by norm_num), ht.eventually (by norm_num),
    psi_chart_hessian_eventually hr hr1 U w] with q hBq hpq htq heq
  ext i j
  change complexHessian (fun q => lam*psi (centeredChart r U q.1) + (logarithmicBarrier ∘ normalLogWeight (φ ∘ centeredChart r U) w) q) q i j =
    complexHessian (fun q => lam*psi q.1 + (logarithmicBarrier ∘ normalLogWeight (φ ∘ centeredChart r U) w) q) q i j
  rw [complexHessian_add (contDiffAt_const.mul htq) hBq,
    complexHessian_add (contDiffAt_const.mul hpq) hBq,
    complexHessian_const_mul htq, complexHessian_const_mul hpq, heq]

lemma sectional_normalGauge {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (hpsh : IsPshBase φ) {lam : ℝ} (hlam : 0 < lam)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (U : Base ≃ₗᵢ[ℂ] Base)
    (w : ℂ) (hp : (centeredChart r U 0,Complex.exp w) ∈ hartogs φ) (u v : Ambient) :
    sectional (complexHessian (normalPotential (φ ∘ centeredChart r U) lam w)) (0,w) u v =
      sectional (hartogsMetric φ lam) (centeredChart r U 0,Complex.exp w)
        (fderiv ℂ (fiberGaugeMap (centeredChart r U) (baseGaugePolynomial (φ ∘ centeredChart r U) w)) (0,w) u)
        (fderiv ℂ (fiberGaugeMap (centeredChart r U) (baseGaugePolynomial (φ ∘ centeredChart r U) w)) (0,w) v) := by
  let F := fiberGaugeMap (centeredChart r U) (baseGaugePolynomial (φ ∘ centeredChart r U) w)
  have hFc : F (0,w) = (centeredChart r U 0,Complex.exp w) := by simp [F, fiberGaugeMap, baseGaugePolynomial]
  have hFp : F (0,w) ∈ hartogs φ := hFc ▸ hp
  have hn : normalLogWeight (φ ∘ centeredChart r U) w (0,w) < 0 := by
    rw [← gaugeLogParameter_normal]
    exact gaugeLogParameter_neg hFp
  have hT := centeredChart_analyticAt (r := r) U (z := 0) (by simp)
  have hF := fiberGaugeMap_analyticAt (p := (0,w)) hT (baseGaugePolynomial_analytic (φ ∘ centeredChart r U) w (0,w))
  have hJ := jacobianMatrix_det_of_fderiv_injective
    (fderiv_fiberGaugeMap_injective (p := (0,w)) hT.differentiableAt
      (fderiv_centeredChart_zero_injective hr hr1 U) (firstGaugeJet (fun q : Ambient => (φ ∘ centeredChart r U) q.1) (0,w))
      (secondGaugeJet (fun q : Ambient => (φ ∘ centeredChart r U) q.1) (0,w)))
  have he := sectional_complexHessian_comp (metricPotential_contDiffAt hφ lam hFp) hF
    (kahler_metric_det_ne_zero (hartogsMetric_isKahler hφ hpsh hlam) hFp) hJ u v
  rw [sectional_congr (normalGauge_hessian_eventually hφ hr hr1 U lam w hn), hFc] at he
  exact he

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsCurvatureContinuity
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
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
namespace PinchedHartogs
open PlaneAlgebra PlaneAlgebra.MatrixAlgebra PlaneAlgebra.TensorAlgebra Matrix

lemma hermitianValue_pairValue (A : CMatrix) (u v : Ambient) :
    hermitianValue A u v = pairValue A (coordinates u) (coordinates v) := by
  simp only [hermitianValue, pairValue, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma realArea_positive {A : CMatrix} (hA : A.IsHermitian)
    (hpos : ∀ u : Ambient, u ≠ 0 → 0 < (hermitianValue A u u).re)
    {u v : Ambient} (hind : LinearIndependent ℝ ![u,v]) : 0 < realArea A u v := by
  have hp : (form A hA).Pos := by
    intro w hw
    have hh := hpos (coordinateEquiv.symm w) (coordinateEquiv.symm.map_ne_zero_iff.mpr hw)
    rwa [hermitianValue_pairValue, coordinates_equiv_symm] at hh
  have hi : LinearIndependent ℝ ![coordinates u,coordinates v] := by
    convert hind.map' (coordinateLinearEquiv.restrictScalars ℝ).toLinearMap
      (LinearMap.ker_eq_bot_of_injective (coordinateLinearEquiv.restrictScalars ℝ).injective) using 1
    all_goals first | rfl | (ext i; fin_cases i <;> rfl)
  have hh := (form A hA).area_pos (coordinates u) (coordinates v) hp hi
  simp only [realArea, hermitianValue_pairValue]
  exact hh

lemma metric_isHermitian {M : Set Ambient} {g : Ambient → CMatrix}
    (hg : IsKahlerMetric M g) {p : Ambient} (hp : p ∈ M) : (g p).IsHermitian := by
  ext i j
  exact (hg.2.1 p hp i j).symm

lemma curvature_continuousAt {g : Ambient → CMatrix} {p : Ambient}
    (hg : ContDiffAt ℝ 2 g p) (hdet : (g p).det ≠ 0) : ContinuousAt (curvature g) p := by
  have hcomp (i j : Fin 3) : ContDiffAt ℝ 2 (fun q => g q i j) p :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  have hi := (matrix_contDiffAt_inv hg hdet).continuousAt
  apply continuousAt_pi.mpr
  intro a
  apply continuousAt_pi.mpr
  intro b
  apply continuousAt_pi.mpr
  intro c
  apply continuousAt_pi.mpr
  intro d
  change ContinuousAt (fun q => -dbar (fun r => dz (fun t => g t c d) r a) q b +
    ∑ e, ∑ k, (g q)⁻¹ e k * dz (fun r => g r c e) q a * dbar (fun r => g r k d) q b) p
  apply ContinuousAt.add
  · exact (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_dz (hcomp c d) (m := 1) (by norm_num) a) (m := 0) (by norm_num) b).continuousAt.neg
  · apply tendsto_finsetSum
    intro e he
    apply tendsto_finsetSum
    intro k hk
    exact ((continuousAt_pi.mp (continuousAt_pi.mp hi e) k).mul
      (_root_.OAI.ContDiffAt.hartogs_dz (hcomp c e) (m := 1) (by norm_num) a).continuousAt).mul
      (_root_.OAI.ContDiffAt.hartogs_dbar (hcomp k d) (m := 1) (by norm_num) b).continuousAt

lemma tensorValue_continuousAt {R : Ambient → CurvatureTensor} {p : Ambient}
    (hR : ContinuousAt R p) (u v w y : Ambient) :
    ContinuousAt (fun q => tensorValue (R q) u v w y) p := by
  unfold tensorValue
  apply tendsto_finsetSum
  intro a ha
  apply tendsto_finsetSum
  intro b hb
  apply tendsto_finsetSum
  intro c hc
  apply tendsto_finsetSum
  intro d hd
  exact ((((continuousAt_pi.mp (continuousAt_pi.mp (continuousAt_pi.mp (continuousAt_pi.mp hR a) b) c) d).mul
    continuousAt_const).mul continuousAt_const).mul continuousAt_const).mul continuousAt_const

lemma hermitianValue_continuousAt {g : Ambient → CMatrix} {p : Ambient}
    (hg : ContinuousAt g p) (u v : Ambient) : ContinuousAt (fun q => hermitianValue (g q) u v) p := by
  unfold hermitianValue
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  exact ((continuousAt_pi.mp (continuousAt_pi.mp hg i) j).mul continuousAt_const).mul continuousAt_const

lemma sectional_continuousAt {M : Set Ambient} {g : Ambient → CMatrix}
    (hM : IsOpen M) (hg : IsKahlerMetric M g) {p : Ambient} (hp : p ∈ M)
    {u v : Ambient} (hind : LinearIndependent ℝ ![u,v]) :
    ContinuousAt (fun q => sectional g q u v) p := by
  have hgs := hg.1.contDiffAt (hM.mem_nhds hp)
  have hR := curvature_continuousAt (hgs.of_le (WithTop.coe_le_coe.mpr le_top)) (kahler_metric_det_ne_zero hg hp)
  have ha : 0 < realArea (g p) u v := realArea_positive (metric_isHermitian hg hp) (hg.2.2.1 p hp) hind
  apply ContinuousAt.div
  · exact (Complex.continuous_re.continuousAt.comp (tensorValue_continuousAt hR u u v v)).sub
      (Complex.continuous_re.continuousAt.comp (tensorValue_continuousAt hR u v u v))
  · apply continuousAt_const.mul
    apply ContinuousAt.sub
    · exact (Complex.continuous_re.continuousAt.comp (hermitianValue_continuousAt hgs.continuousAt u u)).mul
        (Complex.continuous_re.continuousAt.comp (hermitianValue_continuousAt hgs.continuousAt v v))
    · exact (Complex.continuous_re.continuousAt.comp (hermitianValue_continuousAt hgs.continuousAt u v)).pow 2
  · exact mul_ne_zero (by norm_num) ha.ne'

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsPinching
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
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
namespace PinchedHartogs
open PlaneAlgebra PlaneAlgebra.MatrixAlgebra PlaneAlgebra.TensorAlgebra Matrix

theorem hartogsMetric_uniform_pinching_oai {φ : Base → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ ball) {c C lam : ℝ} (hc : 0 < c) (hC : c ≤ C)
    (hctl : ChartControl φ c C) (hj : ChartJets φ C) (hlam : metricThreshold c C ≤ lam) :
    ∃ a b : ℝ, IsNegativelyPinched (hartogs φ) (hartogsMetric φ lam) a b := by
  have hpsh := chartControl_psh hφ hc.le hctl
  have hlp : 0 < lam := (metricThreshold_pos hc hC).trans_le hlam
  obtain ⟨a,b,ha,hab,hbound⟩ := normalPotentials_uniform_pinching hc hC hlam
  have hnonzero (p : Ambient) (hp : p ∈ hartogs φ) (hp0 : p.2 ≠ 0)
      (u v : Ambient) (hind : LinearIndependent ℝ ![u,v]) :
      -b ≤ sectional (hartogsMetric φ lam) p u v ∧
      sectional (hartogsMetric φ lam) p u v ≤ -a := by
    obtain ⟨r,U,hr,hr1,hz0⟩ := exists_centeredChart hp.1
    let w := Complex.log p.2
    have hw : Complex.exp w = p.2 := Complex.exp_log hp0
    have hpp : (centeredChart r U 0,Complex.exp w) = p := by rw [hz0,hw]
    have hpm : (centeredChart r U 0,Complex.exp w) ∈ hartogs φ := hpp ▸ hp
    let F := fiberGaugeMap (centeredChart r U) (baseGaugePolynomial (φ ∘ centeredChart r U) w)
    have hFc : F (0,w) = (centeredChart r U 0,Complex.exp w) := by simp [F, fiberGaugeMap, baseGaugePolynomial]
    have hn : normalLogWeight (φ ∘ centeredChart r U) w (0,w) < 0 := by
      rw [← gaugeLogParameter_normal]
      apply gaugeLogParameter_neg
      change F (0,w) ∈ hartogs φ
      rwa [hFc]
    have hT := centeredChart_analyticAt (r := r) U (z := 0) (by simp)
    have hi : Function.Injective (fderiv ℂ F (0,w)) :=
      fderiv_fiberGaugeMap_injective (p := (0,w)) hT.differentiableAt
        (fderiv_centeredChart_zero_injective hr hr1 U)
        (firstGaugeJet (fun q : Ambient => (φ ∘ centeredChart r U) q.1) (0,w))
        (secondGaugeJet (fun q : Ambient => (φ ∘ centeredChart r U) q.1) (0,w))
    let L : Ambient ≃ₗ[ℂ] Ambient := LinearEquiv.ofBijective (fderiv ℂ F (0,w)).toLinearMap
      ⟨hi, (LinearMap.injective_iff_surjective (f := (fderiv ℂ F (0,w)).toLinearMap)).mp hi⟩
    have hind' : LinearIndependent ℝ ![L.symm u,L.symm v] := by
      convert hind.map' (L.symm.restrictScalars ℝ).toLinearMap
        (LinearMap.ker_eq_bot_of_injective (L.symm.restrictScalars ℝ).injective) using 1
      all_goals first | rfl | (funext i; fin_cases i <;> rfl)
    have hc' := chartControl_form_bounds hφ hctl hr hr1 U
    have hj' := chartJets_lifted_bounds hφ hj hr hr1 U
    have hb := hbound (φ ∘ centeredChart r U) (chartWeight_contDiffAt hφ hr hr1 U)
      hc'.1 hc'.2 hj'.1 hj'.2 w hn (L.symm u) (L.symm v) hind'
    have he := sectional_normalGauge hφ hpsh hlp hr hr1 U w hpm (L.symm u) (L.symm v)
    change sectional _ _ (L.symm u) (L.symm v) =
      sectional _ _ (L (L.symm u)) (L (L.symm v)) at he
    rw [L.apply_symm_apply,L.apply_symm_apply,hpp] at he
    rwa [he] at hb
  refine ⟨a,b,ha,hab,?_⟩
  intro p hp u v hind
  by_cases hp0 : p.2 = 0
  · let ps : ℕ → Ambient := fun n => (p.1,(1 / (n+1 : ℂ)))
    have ht : Tendsto ps atTop (𝓝 p) := by
      have hh := (tendsto_const_nhds (x := p.1)).prodMk
        (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1/(n+1 : ℂ)) atTop (𝓝 0))
      rw [← nhds_prod_eq] at hh
      simpa [ps,← hp0] using hh
    have hev : ∀ᶠ n in atTop, ps n ∈ hartogs φ := ht.eventually ((hartogs_isOpen_smooth hφ).mem_nhds hp)
    have hb : ∀ᶠ n in atTop, -b ≤ sectional (hartogsMetric φ lam) (ps n) u v ∧
        sectional (hartogsMetric φ lam) (ps n) u v ≤ -a := by
      filter_upwards [hev] with n hn
      apply hnonzero (ps n) hn _ u v hind
      change 1/(n+1 : ℂ) ≠ 0
      exact div_ne_zero one_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)
    have hlim := (sectional_continuousAt (hartogs_isOpen_smooth hφ)
      (hartogsMetric_isKahler hφ hpsh hlp) hp hind).tendsto.comp ht
    exact ⟨ge_of_tendsto hlim (hb.mono fun _ h => h.1), le_of_tendsto hlim (hb.mono fun _ h => h.2)⟩
  · exact hnonzero p hp hp0 u v hind

end PinchedHartogs

end

end OAI
end

theorem solution : type_of% @OAI.PinchedHartogs.hartogsMetric_uniform_pinching_oai := @OAI.PinchedHartogs.hartogsMetric_uniform_pinching_oai
