-- Prove2me | solution 1 for OAI.BoundedRecovery.bounded_recovery
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T20:38:21.171115+00:00
-- url     : https://prove2.me/submissions/57ae94d1-a252-4f17-b119-7bb8999ca158

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_OAIQWBDR002

section
-- module Solutions.OAIQW_BoundedRecovery.SpectralCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unitary spectral characters, spectral support, and half-exponential bounds. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section

namespace BoundedRecovery

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace RealSpectralCalculus

lemma HasSpectralSupport.smul {D : RealSpectralCalculus H} {I : Set ℝ} {h : H}
    (hh : D.HasSpectralSupport I h) (c : ℂ) : D.HasSpectralSupport I (c • h) := by
  intro f hf
  simp [map_smul, hh f hf]

lemma HasSpectralSupport.fixed {D : RealSpectralCalculus H} {I : Set ℝ} {h : H}
    (hh : D.HasSpectralSupport I h) {f : BoundedContinuousFunction ℝ ℂ}
    (heq : ∀ u ∈ I, f u = 1) : D.calculus f h = h := by
  simpa using hh.congr (g := 1) heq

lemma support_calculus_apply (D : RealSpectralCalculus H) (I : Set ℝ)
    (f : BoundedContinuousFunction ℝ ℂ) (hf : ∀ u ∉ I, f u = 0) (h : H) :
    D.HasSpectralSupport I (D.calculus f h) := by
  intro g hg
  change (D.calculus g * D.calculus f) h = 0
  rw [← map_mul]
  have heq : g * f = 0 := by
    ext u
    by_cases hu : u ∈ I
    · simp [hg u hu]
    · simp [hf u hu]
  simp [heq]

lemma norm_upperHalfExponential_le (b : ℝ) :
    ‖upperHalfExponential b‖ ≤ Real.exp (b / 2) := by
  apply (BoundedContinuousFunction.norm_le (Real.exp_pos _).le).mpr
  intro u
  change ‖(Real.exp (min b u / 2) : ℂ)‖ ≤ _
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))

lemma norm_halfGraph_le {D : RealSpectralCalculus H} {I : Set ℝ} {h q : H}
    (hh : D.HasSpectralSupport I h) {b : ℝ} (hb : ∀ u ∈ I, u ≤ b)
    (hq : (h, q) ∈ D.halfGraph) : ‖q‖ ≤ Real.exp (b / 2) * ‖h‖ := by
  have he : q = D.calculus (upperHalfExponential b) h :=
    tendsto_nhds_unique hq (hh.halfGraph hb)
  rw [he]
  exact (D.norm_calculus_apply_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_upperHalfExponential_le b) (norm_nonneg _))

end RealSpectralCalculus

end BoundedRecovery

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.TomitaResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resolvents of the half-exponential and the closed Tomita graph. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace RealSpectralCalculus

lemma halfGraph_nonneg (D : RealSpectralCalculus H) {x y : H}
    (hxy : (x,y) ∈ D.halfGraph) : 0 ≤ (inner ℂ x y).re := by
  have hpos (n : ℕ) : 0 ≤ (inner ℂ x (D.calculus (halfExponentialCutoff n) x)).re := by
    let f : BoundedContinuousFunction ℝ ℂ :=
      BoundedContinuousFunction.ofNormedAddCommGroup
        (fun u : ℝ => (Real.exp (min (n : ℝ) u / 4) : ℂ))
        (by fun_prop) (Real.exp ((n : ℝ) / 4)) (by
          intro u
          simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_exp.mpr
            (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)))
    have hf : halfExponentialCutoff n = star f * f := by
      ext u
      change (Real.exp (min (n:ℝ) u / 2) : ℂ) =
        star (Real.exp (min (n:ℝ) u / 4) : ℂ) * (Real.exp (min (n:ℝ) u / 4) : ℂ)
      rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      ring
    rw [hf, map_mul, map_star]
    change 0 ≤ (inner ℂ x ((D.calculus f).adjoint (D.calculus f x))).re
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_nonneg (𝕜 := ℂ)
  have ht : Tendsto (fun n => inner ℂ x (D.calculus (halfExponentialCutoff n) x))
      atTop (𝓝 (inner ℂ x y)) := tendsto_const_nhds.inner hxy
  exact ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp ht)
    (Filter.Eventually.of_forall hpos)

end RealSpectralCalculus
namespace StandardModularData

lemma tomita_graph_inner_xi (S : StandardModularData H) {x y : H}
    (hxy : (x,y) ∈ closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)}) :
    inner ℂ y S.xi = inner ℂ S.xi x := by
  have hc : IsClosed {p : H × H | inner ℂ p.2 S.xi = inner ℂ S.xi p.1} :=
    isClosed_eq (continuous_snd.inner continuous_const) (continuous_const.inner continuous_fst)
  apply (closure_minimal (s := {p : H × H | ∃ a : H →L[ℂ] H,
    a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)}) ?_ hc) hxy
  rintro p ⟨a, _ha, rfl⟩
  exact ContinuousLinearMap.adjoint_inner_left a S.xi S.xi

lemma halfGraph_xi_Jxi (S : StandardModularData H) :
    (S.xi, S.J S.xi) ∈ S.D.halfGraph := by
  have hcore : (S.xi,S.xi) ∈ closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)} := by
    apply subset_closure
    exact ⟨1, S.M.one_mem, by simp⟩
  rw [S.tomita_graph] at hcore
  obtain ⟨q,hq,he⟩ := hcore
  dsimp only at he hq
  have hqeq : q = S.J S.xi := by
    rw [he, S.conjugation]
  rwa [hqeq] at hq

lemma halfGraph_Jxi_xi (S : StandardModularData H) :
    (S.J S.xi, S.xi) ∈ S.D.halfGraph := by
  rw [S.D.halfGraph_adjoint_iff]
  intro a b hab
  have htom : (a,S.J b) ∈ closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)} := by
    rw [S.tomita_graph]
    exact ⟨b,hab,rfl⟩
  rw [← S.tomita_graph_inner_xi htom, S.J_inner_flip]

lemma J_fixes_xi (S : StandardModularData H) : S.J S.xi = S.xi := by
  have hg := S.D.halfGraph_sub S.halfGraph_xi_Jxi S.halfGraph_Jxi_xi
  have hp := S.D.halfGraph_nonneg hg
  have he : S.J S.xi - S.xi = -(S.xi - S.J S.xi) := by abel
  rw [he, inner_neg_right, Complex.neg_re] at hp
  change 0 ≤ -RCLike.re (inner ℂ (S.xi - S.J S.xi) (S.xi - S.J S.xi)) at hp
  rw [← norm_sq_eq_re_inner] at hp
  have hn : ‖S.xi - S.J S.xi‖ = 0 := by nlinarith [norm_nonneg (S.xi - S.J S.xi)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

lemma halfGraph_xi (S : StandardModularData H) :
    (S.xi, S.xi) ∈ S.D.halfGraph := by
  simpa only [S.J_fixes_xi] using S.halfGraph_xi_Jxi

lemma halfResolvent_xi (S : StandardModularData H) :
    S.D.calculus halfResolvent S.xi = (1/2:ℂ) • S.xi := by
  have he := (S.D.halfGraph_iff_resolvent _ _).mp S.halfGraph_xi
  rw [map_add] at he
  calc
    S.D.calculus halfResolvent S.xi = (1/2:ℂ) •
        (S.D.calculus halfResolvent S.xi + S.D.calculus halfResolvent S.xi) := by
      rw [smul_add, ← add_smul]
      norm_num
    _ = _ := by rw [he]

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery

lemma regularizedQuotient_remainder (f : BoundedContinuousFunction ℝ ℂ)
    (g : BoundedContinuousFunction ℝ ℝ) {k : ℝ} (hk : 0 < k) (u : ℝ) :
    (f - regularizedQuotient f g k hk * realMultiplier g) u =
      f u * ((k / ((g u)^2 + k) : ℝ) : ℂ) := by
  change f u - (f u * ((g u / ((g u)^2 + k) : ℝ) : ℂ)) * (g u : ℂ) = _
  have hd : (g u)^2 + k ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) hk)
  have hdc : ((g u : ℂ)^2 + (k : ℂ)) ≠ 0 := by exact_mod_cast hd
  push_cast
  field_simp
  ring

lemma exists_multiplier_approx (g : BoundedContinuousFunction ℝ ℝ) (s : ℝ)
    (hsep : ∀ d : ℝ, 0 < d → ∃ c : ℝ, 0 < c ∧
      ∀ u : ℝ, d ≤ |u-s| → c ≤ |g u|)
    (f : BoundedContinuousFunction ℝ ℂ) (hf : f s = 0) {eps : ℝ} (heps : 0 < eps) :
    ∃ q : BoundedContinuousFunction ℝ ℂ, ‖f - q * realMultiplier g‖ ≤ eps := by
  obtain ⟨d, hd, hdf⟩ := Metric.continuousAt_iff.mp f.continuous.continuousAt eps heps
  obtain ⟨c,hc,hcg⟩ := hsep d hd
  let k : ℝ := eps * c^2 / (‖f‖+1)
  have hk : 0 < k := by dsimp [k]; positivity
  have hkeq : (‖f‖+1)*k = eps*c^2 := by
    dsimp only [k]
    field_simp
  refine ⟨regularizedQuotient f g k hk, (BoundedContinuousFunction.norm_le heps.le).mpr ?_⟩
  intro u
  rw [regularizedQuotient_remainder, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos hk (add_pos_of_nonneg_of_pos (sq_nonneg _) hk)), ← mul_div_assoc]
  apply (div_le_iff₀ (add_pos_of_nonneg_of_pos (sq_nonneg _) hk)).mpr
  by_cases hu : |u-s| < d
  · have hfu : ‖f u‖ < eps := by
      simpa only [Real.dist_eq, hf, dist_zero_right] using hdf hu
    calc
      ‖f u‖ * k ≤ eps * k := mul_le_mul_of_nonneg_right hfu.le hk.le
      _ ≤ eps * ((g u)^2+k) := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (g u)]) heps.le
  · have hgu := hcg u (le_of_not_gt hu)
    have hgsq : c^2 ≤ (g u)^2 := by nlinarith [sq_abs (g u)]
    calc
      ‖f u‖ * k ≤ (‖f‖+1)*k := mul_le_mul_of_nonneg_right ((f.norm_coe_le_norm u).trans (by linarith)) hk.le
      _ = eps*c^2 := hkeq
      _ ≤ eps*((g u)^2+k) := mul_le_mul_of_nonneg_left (by linarith) heps.le

end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace RealSpectralCalculus

lemma kernel_of_separated_zero (D : RealSpectralCalculus H)
    (g : BoundedContinuousFunction ℝ ℝ) (s : ℝ)
    (hsep : ∀ d : ℝ, 0 < d → ∃ c : ℝ, 0 < c ∧
      ∀ u : ℝ, d ≤ |u-s| → c ≤ |g u|)
    {x : H} (hx : D.calculus (realMultiplier g) x = 0)
    (f : BoundedContinuousFunction ℝ ℂ) (hf : f s = 0) : D.calculus f x = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro eps heps
  have hden : 0 < ‖x‖+1 := by positivity
  obtain ⟨q,hq⟩ := exists_multiplier_approx g s hsep f hf (div_pos heps hden)
  have hprod : D.calculus (q * realMultiplier g) x = 0 := by
    rw [map_mul]
    change D.calculus q (D.calculus (realMultiplier g) x) = 0
    rw [hx, map_zero]
  have heq : D.calculus f x = D.calculus (f - q * realMultiplier g) x := by
    rw [map_sub, sub_apply, hprod, sub_zero]
  rw [heq, zero_add]
  calc
    ‖D.calculus (f - q * realMultiplier g) x‖ ≤ ‖f - q * realMultiplier g‖ * ‖x‖ :=
      D.norm_calculus_apply_le _ _
    _ ≤ (eps/(‖x‖+1)) * ‖x‖ := mul_le_mul_of_nonneg_right hq (norm_nonneg _)
    _ ≤ eps := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith

end RealSpectralCalculus

lemma centeredHalfResolvent_strictAnti : StrictAnti centeredHalfResolvent := by
  intro a b hab
  change (Real.exp (b/2)+1)⁻¹ - 1/2 < (Real.exp (a/2)+1)⁻¹ - 1/2
  apply sub_lt_sub_right
  apply (inv_lt_inv₀ (by positivity) (by positivity)).mpr
  have he := Real.exp_lt_exp.mpr (show a/2 < b/2 by linarith)
  linarith

lemma centeredHalfResolvent_separated (d : ℝ) (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : ℝ, d ≤ |u-0| → c ≤ |centeredHalfResolvent u| := by
  have hp : 0 < centeredHalfResolvent (-d) := by
    simpa only [centeredHalfResolvent_zero] using
      centeredHalfResolvent_strictAnti (show -d < 0 by linarith)
  have hn : centeredHalfResolvent d < 0 := by
    simpa only [centeredHalfResolvent_zero] using centeredHalfResolvent_strictAnti hd
  refine ⟨min (centeredHalfResolvent (-d)) (-centeredHalfResolvent d), lt_min hp (by linarith), ?_⟩
  intro u hu
  rw [sub_zero, le_abs] at hu
  rcases hu with hu | hu
  · have ht := centeredHalfResolvent_strictAnti.antitone hu
    have hneg : centeredHalfResolvent u < 0 := ht.trans_lt hn
    rw [abs_of_neg hneg]
    exact (min_le_right _ _).trans (neg_le_neg ht)
  · have ht := centeredHalfResolvent_strictAnti.antitone (show u ≤ -d by linarith)
    have hpos : 0 < centeredHalfResolvent u := hp.trans_le ht
    rw [abs_of_pos hpos]
    exact (min_le_left _ _).trans ht

lemma realMultiplier_centeredHalfResolvent :
    realMultiplier centeredHalfResolvent = halfResolvent - (1/2 : ℂ) • 1 := by
  ext u
  change (((Real.exp (u/2)+1)⁻¹ - 1/2 : ℝ) : ℂ) =
    (((Real.exp (u/2)+1)⁻¹ : ℝ) : ℂ) - (1/2 : ℂ) * 1
  push_cast
  ring

namespace StandardModularData

lemma xi_spectralSupport (S : StandardModularData H) :
    S.D.HasSpectralSupport {0} S.xi := by
  intro f hf
  apply S.D.kernel_of_separated_zero centeredHalfResolvent 0 centeredHalfResolvent_separated _ f
    (hf 0 (mem_singleton 0))
  rw [realMultiplier_centeredHalfResolvent, map_sub, map_smul, map_one, sub_apply,
    smul_apply, one_apply_eq_self, S.halfResolvent_xi, sub_self]

lemma fixes_xi (S : StandardModularData H) (t : ℝ) : S.D.unitary t S.xi = S.xi := by
  have he := S.xi_spectralSupport (spectralCharacter t - 1) (by
    intro u hu
    rcases mem_singleton_iff.mp hu with rfl
    simp)
  simpa only [map_sub, map_one, sub_apply, one_apply_eq_self, sub_eq_zero, RealSpectralCalculus.unitary] using he

end StandardModularData
end BoundedRecovery

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.PolarCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous functional calculus and bounded polar truncation in C*-algebras. -/

universe uA

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section

namespace BoundedRecovery

lemma cutoffFunction_error_bound {K r : ℝ} (hK : 0 < K) (hr : 0 ≤ r) :
    (1 - cutoffFunction K r) * r * (1 - cutoffFunction K r) ≤ r ^ 2 / K ^ 2 := by
  have hq0 := cutoffFunction_nonneg (r := r) hK
  have hq1 := cutoffFunction_le_one (r := r) hK
  by_cases h : Real.sqrt r ≤ K
  · rw [cutoffFunction_eq_one hK h]
    simp only [sub_self, zero_mul, mul_zero]
    positivity
  · have hKr : K ^ 2 ≤ r := by
      have hs := Real.sq_sqrt hr
      nlinarith [Real.sqrt_nonneg r]
    have hsq : (1 - cutoffFunction K r) ^ 2 ≤ 1 := by nlinarith
    calc
      (1 - cutoffFunction K r) * r * (1 - cutoffFunction K r) =
          r * (1 - cutoffFunction K r) ^ 2 := by ring
      _ ≤ r * 1 := mul_le_mul_of_nonneg_left hsq hr
      _ ≤ r ^ 2 / K ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hK)).mpr
        nlinarith [mul_le_mul_of_nonneg_left hKr hr]

section CStarCutoff

variable {A : Type uA} [CStarAlgebra A]

lemma polarCutoff_error_square (z : A) {K : ℝ} (hK : 0 < K) :
    star (z - polarCutoff z K) * (z - polarCutoff z K) =
      cfc (fun r => (1 - cutoffFunction K r) * r * (1 - cutoffFunction K r))
        (star z * z) := by
  have hc : Continuous (fun r => 1 - cutoffFunction K r) :=
    continuous_const.sub (cutoffFunction_continuous hK)
  have ha : IsSelfAdjoint (star z * z) := by
    simp [IsSelfAdjoint]
  have hq : IsSelfAdjoint (cfc (cutoffFunction K) (star z * z)) := IsSelfAdjoint.cfc
  rw [cfc_mul (fun r => (1 - cutoffFunction K r) * r) (fun r => 1 - cutoffFunction K r)
      (star z * z) (hc.mul continuous_id).continuousOn hc.continuousOn,
    cfc_mul (fun r => 1 - cutoffFunction K r) (fun r => r) (star z * z)
      hc.continuousOn continuous_id.continuousOn, cfc_id' ℝ _ ha,
    cfc_sub _ _ _ continuous_const.continuousOn (cutoffFunction_continuous hK).continuousOn,
    cfc_const _ _ ha]
  simp only [map_one, polarCutoff, star_sub, star_mul, hq.star_eq]
  noncomm_ring

variable [PartialOrder A] [StarOrderedRing A]

lemma polarCutoff_error_le (z : A) {K : ℝ} (hK : 0 < K) :
    star (z - polarCutoff z K) * (z - polarCutoff z K) ≤
      (K ^ 2)⁻¹ • (star z * z) ^ 2 := by
  have ha : IsSelfAdjoint (star z * z) := by
    simp [IsSelfAdjoint]
  rw [polarCutoff_error_square z hK, ← cfc_pow_id (R := ℝ) _ 2 ha,
    ← cfc_const_mul (K ^ 2)⁻¹ (fun r : ℝ => r ^ 2) (star z * z)]
  have hc : Continuous (fun r => 1 - cutoffFunction K r) :=
    continuous_const.sub (cutoffFunction_continuous hK)
  apply cfc_mono (hf := ((hc.mul continuous_id).mul hc).continuousOn)
    (hg := (continuous_const.mul (continuous_id.pow 2)).continuousOn)
  intro r hr
  have hpos : 0 ≤ r := spectrum_nonneg_of_nonneg (star_mul_self_nonneg z) hr
  simpa [div_eq_mul_inv, mul_comm] using cutoffFunction_error_bound hK hpos

end CStarCutoff

end BoundedRecovery

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.StrongIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong operator integrals and positivity under Gaussian integration. -/

universe uE uX uY

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoundedRecovery
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma norm_strongIntegral_le (k : ℝ → ℂ) (hk : Integrable k) (F : ℝ → E →L[ℂ] E)
    (hF : ∀ h, Continuous (fun t => F t h)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t, ‖F t‖ ≤ C) :
    ‖strongIntegral k hk F hF C hbound‖ ≤ (∫ t, ‖k t‖) * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (integral_nonneg (fun _ => norm_nonneg _)) hC)
  intro h
  exact (norm_integral_smul_bounded_orbit hk
    (fun t => (F t).le_opNorm h |>.trans (mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _)))).trans_eq
      (mul_assoc _ _ _).symm

end BoundedRecovery

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.FourierKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier kernels and uniform bounds for Gaussian multipliers. -/

universe u uι

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace BoundedRecovery

lemma continuous_kernelFourier : Continuous kernelFourier := by
  apply continuous_of_dominated (bound := kernelScalar)
  · intro t
    exact (integrable_fourierKernel t).aestronglyMeasurable
  · intro t
    filter_upwards [] with r
    simp only [norm_mul,spectralCharacter_norm,one_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (kernelScalar_pos r),le_refl]
  · exact integrable_kernelScalar
  · filter_upwards [] with r
    change Continuous (fun t : ℝ => Complex.exp (((t*r:ℝ):ℂ)*Complex.I)*(kernelScalar r:ℂ))
    fun_prop

lemma kernelFourier_zero : kernelFourier 0 = (kernelMass:ℂ) := by
  unfold kernelFourier kernelMass
  simp only [spectralCharacter_zero,BoundedContinuousFunction.coe_one,Pi.one_apply,one_mul]
  exact integral_ofReal

end BoundedRecovery

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.StrongLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong spectral limits and orbit limits. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma tendsto_apply_of_tendsto_xi (S : StandardModularData H)
    (a : ℕ → S.M.toStarSubalgebra) (b : S.M.toStarSubalgebra)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C)
    (hx : Tendsto (fun n => (a n:H →L[ℂ] H) S.xi) atTop (𝓝 ((b:H →L[ℂ] H) S.xi))) (h : H) :
    Tendsto (fun n => (a n:H →L[ℂ] H) h) atTop (𝓝 ((b:H →L[ℂ] H) h)) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  have hd := commutant_cyclic S.M S.xi S.separating
  obtain ⟨v,⟨c,hc,rfl⟩,hv⟩ := hd.exists_dist_lt h
    (show 0 < eps/(3*(C+‖b‖+1)) by positivity)
  have hv' : ‖h-c S.xi‖ < eps/(3*(C+‖b‖+1)) := by simpa only [dist_eq_norm] using hv
  have he (d : S.M.toStarSubalgebra) : (d:H →L[ℂ] H) (c S.xi) = c ((d:H →L[ℂ] H) S.xi) :=
    congrArg (fun f : H →L[ℂ] H => f S.xi) (VonNeumannAlgebra.mem_commutant_iff.mp hc d d.property)
  have ht : Tendsto (fun n => (a n:H →L[ℂ] H) (c S.xi)) atTop (𝓝 ((b:H →L[ℂ] H) (c S.xi))) := by
    simpa only [he,Function.comp_def] using (c.continuous.tendsto ((b:H →L[ℂ] H) S.xi)).comp hx
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp ht (eps/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hmid : ‖(a n:H →L[ℂ] H) (c S.xi)-(b:H →L[ℂ] H) (c S.xi)‖ < eps/3 := by
    simpa only [dist_eq_norm] using hN n hn
  rw [dist_eq_norm]
  have heq : (a n:H →L[ℂ] H) h-(b:H →L[ℂ] H) h =
      ((a n:H →L[ℂ] H) (h-c S.xi)-(b:H →L[ℂ] H) (h-c S.xi))+
      ((a n:H →L[ℂ] H) (c S.xi)-(b:H →L[ℂ] H) (c S.xi)) := by
    simp only [map_sub]
    abel
  rw [heq]
  calc
    _ ≤ ‖(a n:H →L[ℂ] H) (h-c S.xi)-(b:H →L[ℂ] H) (h-c S.xi)‖+
        ‖(a n:H →L[ℂ] H) (c S.xi)-(b:H →L[ℂ] H) (c S.xi)‖ := norm_add_le _ _
    _ ≤ C*‖h-c S.xi‖+‖b‖*‖h-c S.xi‖+
        ‖(a n:H →L[ℂ] H) (c S.xi)-(b:H →L[ℂ] H) (c S.xi)‖ := by
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add
        (((a n:H →L[ℂ] H).le_opNorm _).trans (mul_le_mul_of_nonneg_right (ha n) (norm_nonneg _)))
        ((b:H →L[ℂ] H).le_opNorm _))
    _ ≤ (C+‖b‖+1)*‖h-c S.xi‖+
        ‖(a n:H →L[ℂ] H) (c S.xi)-(b:H →L[ℂ] H) (c S.xi)‖ := by
      nlinarith [norm_nonneg (h-c S.xi)]
    _ < (C+‖b‖+1)*(eps/(3*(C+‖b‖+1)))+eps/3 :=
      add_lt_add (mul_lt_mul_of_pos_left hv' (by positivity)) hmid
    _ < eps := by
      field_simp
      nlinarith [norm_nonneg b]

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace BoundedRecovery

lemma kernelFourier_star (t : ℝ) : star (kernelFourier t) = kernelFourier t := by
  unfold kernelFourier
  rw [Complex.star_def,← integral_conj,
    ← integral_neg_eq_self (fun r => spectralCharacter t r*(kernelScalar r:ℂ)) volume]
  apply integral_congr_ae
  filter_upwards [] with r
  simp only [map_mul,spectralCharacter_arg_neg,kernelScalar_even,Complex.conj_ofReal,Complex.star_def]

lemma kernelFourier_eq_real (t : ℝ) : ((kernelFourier t).re:ℂ) = kernelFourier t :=
  Complex.conj_eq_iff_re.mp (kernelFourier_star t)

lemma kernelFourier_positive_near_zero : ∃ d : ℝ, 0 < d ∧
    ∀ t : ℝ, |t| < d → 0 < (kernelFourier t).re := by
  have hp : 0 < (kernelFourier 0).re := by rw [kernelFourier_zero,Complex.ofReal_re]; exact kernelMass_pos
  have he : ∀ᶠ t in 𝓝 (0:ℝ), 0 < (kernelFourier t).re :=
    (Complex.continuous_re.comp continuous_kernelFourier).continuousAt.eventually (eventually_gt_nhds hp)
  obtain ⟨d,hd,hdt⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨d,hd,fun t ht => hdt ?_⟩
  simpa only [Real.dist_eq,sub_zero] using ht

end BoundedRecovery

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.FourierOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized Fourier operators, Schwarz inequalities, and multiplication. -/

universe u uA uB uM

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma fourierKernel_xi (S : StandardModularData H) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) :
    (S.fourierKernel t b:H →L[ℂ] H) S.xi =
      kernelFourier t • S.D.unitary t (S.J ((↑(star b):H →L[ℂ] H) S.xi)) :=
  (Classical.choose_spec (S.exists_fourierKernel_lift t b)).2.2

lemma fourierKernel_strong_tendsto (S : StandardModularData H) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) (h : H) :
    Tendsto (fun n => (S.kernelAverage n t b:H →L[ℂ] H) h) atTop
      (𝓝 ((S.fourierKernel t b:H →L[ℂ] H) h)) := by
  apply S.tendsto_apply_of_tendsto_xi _ _
    (mul_nonneg (mul_nonneg (by norm_num) kernelMass_pos.le) (norm_nonneg b))
    (fun n => S.norm_kernelAverage_le n t b)
  simpa only [S.kernelAverage_xi,S.fourierKernel_xi] using
    S.D.kernelMultiplier_strong_tendsto t (S.J ((↑(star b):H →L[ℂ] H) S.xi))

lemma fourierKernel_add (S : StandardModularData H) (t : ℝ)
    (b c : S.M.commutant.toStarSubalgebra) :
    S.fourierKernel t (b+c) = S.fourierKernel t b + S.fourierKernel t c := by
  apply S.eq_of_xi
  change (S.fourierKernel t (b+c):H →L[ℂ] H) S.xi =
    (S.fourierKernel t b:H →L[ℂ] H) S.xi + (S.fourierKernel t c:H →L[ℂ] H) S.xi
  simp only [S.fourierKernel_xi,star_add]
  change kernelFourier t • S.D.unitary t (S.J ((star (b:H →L[ℂ] H)+star (c:H →L[ℂ] H)) S.xi)) = _
  simp only [add_apply,map_add,smul_add,StarMemClass.coe_star]

lemma fourierKernel_smul (S : StandardModularData H) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) (z : ℂ) :
    S.fourierKernel t (z • b) = z • S.fourierKernel t b := by
  apply S.eq_of_xi
  change (S.fourierKernel t (z • b):H →L[ℂ] H) S.xi = z • (S.fourierKernel t b:H →L[ℂ] H) S.xi
  simp only [S.fourierKernel_xi,star_smul]
  change kernelFourier t • S.D.unitary t (S.J ((star z • star (b:H →L[ℂ] H)) S.xi)) = _
  simp only [smul_apply,map_smulₛₗ,Complex.star_def,starRingEnd_self_apply,
    RingHom.id_apply,StarMemClass.coe_star]
  exact smul_comm _ _ _

lemma fourierKernel_one (S : StandardModularData H) (t : ℝ) :
    S.fourierKernel t 1 = kernelFourier t • 1 := by
  apply S.eq_of_xi
  rw [S.fourierKernel_xi]
  simp only [star_one,OneMemClass.coe_one,one_apply_eq_self]
  change kernelFourier t • S.D.unitary t (S.J S.xi) = kernelFourier t • S.xi
  rw [S.J_fixes_xi,S.fixes_xi]

lemma fourierKernel_star (S : StandardModularData H) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) :
    star (S.fourierKernel t b) = S.fourierKernel t (star b) := by
  apply Subtype.ext
  ext h
  apply ext_inner_left ℂ
  intro k
  rw [StarMemClass.coe_star,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  have hx := (S.fourierKernel_strong_tendsto t b k).inner (𝕜 := ℂ) (tendsto_const_nhds (x := h))
  have hy := (tendsto_const_nhds (x := k)).inner (𝕜 := ℂ) (S.fourierKernel_strong_tendsto t (star b) h)
  simp only [← S.kernelAverage_star,StarMemClass.coe_star,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right] at hy
  exact tendsto_nhds_unique hx hy

lemma fourierKernel_gram_vector_nonneg (S : StandardModularData H)
    {m : Type uM} [Fintype m] (t : ℝ)
    (b : m → S.M.commutant.toStarSubalgebra) (h : m → H) :
    0 ≤ (∑ i,∑ j,inner ℂ (h i) ((S.fourierKernel t (star (b j)*b i):H →L[ℂ] H) (h j))).re := by
  have ht : Tendsto (fun n => ∑ i,∑ j,inner ℂ (h i)
      ((S.kernelAverage n t (star (b j)*b i):H →L[ℂ] H) (h j))) atTop
      (𝓝 (∑ i,∑ j,inner ℂ (h i)
        ((S.fourierKernel t (star (b j)*b i):H →L[ℂ] H) (h j)))) := by
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact tendsto_const_nhds.inner (S.fourierKernel_strong_tendsto t _ _)
  exact ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp ht)
    (Filter.Eventually.of_forall (fun n => S.kernelAverage_gram_vector_nonneg n t b h))

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma normalizedFourier_add (S : StandardModularData H) (t : ℝ)
    (b c : S.M.commutant.toStarSubalgebra) :
    S.normalizedFourier t (b+c) = S.normalizedFourier t b + S.normalizedFourier t c := by
  simp only [normalizedFourier,S.fourierKernel_add,smul_add]

lemma normalizedFourier_smul (S : StandardModularData H) (t : ℝ)
    (z : ℂ) (b : S.M.commutant.toStarSubalgebra) :
    S.normalizedFourier t (z • b) = z • S.normalizedFourier t b := by
  simp only [normalizedFourier,S.fourierKernel_smul,smul_comm z]

lemma normalizedFourier_star (S : StandardModularData H) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) :
    star (S.normalizedFourier t b) = S.normalizedFourier t (star b) := by
  simp only [normalizedFourier,star_smul,star_inv₀,kernelFourier_star,S.fourierKernel_star]

lemma normalizedFourier_one (S : StandardModularData H) (t : ℝ)
    (ht : kernelFourier t ≠ 0) : S.normalizedFourier t 1 = 1 := by
  simp only [normalizedFourier,S.fourierKernel_one,smul_smul,inv_mul_cancel₀ ht,one_smul]

lemma normalizedFourier_xi (S : StandardModularData H) (t : ℝ)
    (ht : kernelFourier t ≠ 0) (b : S.M.commutant.toStarSubalgebra) :
    (S.normalizedFourier t b:H →L[ℂ] H) S.xi =
      S.D.unitary t (S.J ((↑(star b):H →L[ℂ] H) S.xi)) := by
  change (kernelFourier t)⁻¹ • ((S.fourierKernel t b:H →L[ℂ] H) S.xi) = _
  rw [S.fourierKernel_xi,smul_smul,inv_mul_cancel₀ ht,one_smul]

lemma kernelFourier_ne_zero {t : ℝ} (ht : 0 < (kernelFourier t).re) : kernelFourier t ≠ 0 := by
  intro he
  simp only [he,Complex.zero_re] at ht
  exact lt_irrefl _ ht

lemma normalizedFourier_gram_vector_nonneg (S : StandardModularData H) (t : ℝ)
    (ht : 0 < (kernelFourier t).re) {m : Type uM} [Fintype m]
    (b : m → S.M.commutant.toStarSubalgebra) (h : m → H) :
    0 ≤ (∑ i,∑ j,inner ℂ (h i) ((S.normalizedFourier t (star (b j)*b i):H →L[ℂ] H) (h j))).re := by
  change 0 ≤ (∑ i,∑ j,inner ℂ (h i)
    ((kernelFourier t)⁻¹ • ((S.fourierKernel t (star (b j)*b i):H →L[ℂ] H) (h j)))).re
  simp only [inner_smul_right,← Finset.mul_sum]
  rw [← kernelFourier_eq_real t,← Complex.ofReal_inv,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_nonneg (inv_nonneg.mpr ht.le) (S.fourierKernel_gram_vector_nonneg t b h)

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma normalizedFourier_schwarz (S : StandardModularData H) (t : ℝ)
    (ht : 0 < (kernelFourier t).re) (b : S.M.commutant.toStarSubalgebra) :
    S.normalizedFourier t b * star (S.normalizedFourier t b) ≤
      S.normalizedFourier t (star b*b) := by
  rw [← sub_nonneg]
  change 0 ≤ (S.normalizedFourier t (star b*b):H →L[ℂ] H) -
    (S.normalizedFourier t b:H →L[ℂ] H)*star (S.normalizedFourier t b:H →L[ℂ] H)
  rw [ContinuousLinearMap.nonneg_iff_isPositive,ContinuousLinearMap.isPositive_def']
  refine ⟨?_,fun h => ?_⟩
  · show star _ = _
    simp only [star_sub,star_mul,star_star,← StarMemClass.coe_star,S.normalizedFourier_star]
  · let y : H := (S.normalizedFourier t (star b):H →L[ℂ] H) h
    have hp := S.normalizedFourier_gram_vector_nonneg t ht
      (![1,b] : Fin 2 → S.M.commutant.toStarSubalgebra) (![(-y),h] : Fin 2 → H)
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one,star_one,one_mul,mul_one,S.normalizedFourier_one t (kernelFourier_ne_zero ht),
      OneMemClass.coe_one,one_apply_eq_self,map_neg,inner_neg_left,inner_neg_right] at hp
    have hy : inner ℂ h ((S.normalizedFourier t b:H →L[ℂ] H) y) = inner ℂ y y := by
      rw [← star_star b,← S.normalizedFourier_star,StarMemClass.coe_star,
        ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
    change 0 ≤ (inner ℂ (((S.normalizedFourier t (star b*b):H →L[ℂ] H) -
      (S.normalizedFourier t b:H →L[ℂ] H)*star (S.normalizedFourier t b:H →L[ℂ] H)) h) h).re
    rw [← inner_conj_symm,Complex.conj_re]
    simp only [sub_apply,mul_apply_eq_comp,← StarMemClass.coe_star,S.normalizedFourier_star,
      inner_sub_right]
    change 0 ≤ (inner ℂ h ((S.normalizedFourier t (star b*b):H →L[ℂ] H) h) -
      inner ℂ h ((S.normalizedFourier t b:H →L[ℂ] H) y)).re
    rw [hy]
    change 0 ≤ (- -inner ℂ y y + -inner ℂ y y +
      (-inner ℂ h ((S.normalizedFourier t b:H →L[ℂ] H) y) +
      inner ℂ h ((S.normalizedFourier t (star b*b):H →L[ℂ] H) h))).re at hp
    rw [hy] at hp
    simpa only [neg_neg,add_neg_cancel,zero_add,sub_eq_add_neg,add_comm] using hp

lemma phi_normalizedFourier (S : StandardModularData H) (t : ℝ)
    (ht : kernelFourier t ≠ 0) (b : S.M.commutant.toStarSubalgebra) :
    S.phi (S.normalizedFourier t b) = S.commutantData.phi b := by
  change inner ℂ S.xi ((S.normalizedFourier t b:H →L[ℂ] H) S.xi) =
    inner ℂ S.xi ((b:H →L[ℂ] H) S.xi)
  rw [S.normalizedFourier_xi t ht]
  rw [← star_star (S.D.unitary t),ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  rw [S.D.unitary_star,S.fixes_xi]
  have he (x : H) : inner ℂ S.xi (S.J x) = inner ℂ x S.xi := by
    have h := S.J_inner_flip S.xi (S.J x)
    rw [S.J_fixes_xi,S.conjugation x] at h
    exact h
  rw [he,StarMemClass.coe_star,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

lemma phi_faithful_nonneg (S : StandardModularData H) (a : S.M.toStarSubalgebra)
    (ha : 0 ≤ a) (hz : (S.phi a).re = 0) : a = 0 := by
  obtain ⟨d,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  rw [S.phi_faithful d hz,star_zero,mul_zero]

lemma normalizedFourier_star_square (S : StandardModularData H) (t : ℝ)
    (ht : 0 < (kernelFourier t).re) (b : S.M.commutant.toStarSubalgebra) :
    S.normalizedFourier t (star b*b) =
      S.normalizedFourier t b * star (S.normalizedFourier t b) := by
  apply sub_eq_zero.mp
  apply S.phi_faithful_nonneg _ (sub_nonneg.mpr (S.normalizedFourier_schwarz t ht b))
  rw [map_sub,Complex.sub_re,S.phi_normalizedFourier t (kernelFourier_ne_zero ht)]
  have hv : (S.commutantData.phi (star b*b)).re = ‖(b:H →L[ℂ] H) S.xi‖^2 :=
    S.commutantData.phi_star_mul b
  rw [hv]
  have he : (S.phi (S.normalizedFourier t b * star (S.normalizedFourier t b))).re =
      ‖(b:H →L[ℂ] H) S.xi‖^2 := by
    nth_rw 1 [← star_star (S.normalizedFourier t b)]
    rw [S.phi_star_mul,S.normalizedFourier_star,S.normalizedFourier_xi t (kernelFourier_ne_zero ht),
      star_star,S.D.norm_unitary_apply,S.J.norm_map]
  rw [he,sub_self]

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery

lemma sesq_zero_of_diagonal {A : Type uA} {B : Type uB} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (f : A → A → B)
    (ha : ∀ a b c, f (a+b) c = f a c + f b c)
    (hb : ∀ a b c, f a (b+c) = f a b + f a c)
    (hs : ∀ (z : ℂ) a b, f (z • a) b = star z • f a b)
    (ht : ∀ (z : ℂ) a b, f a (z • b) = z • f a b)
    (hd : ∀ a, f a a = 0) (a b : A) : f a b = 0 := by
  have h1 : f a b + f b a = 0 := by
    have h := hd (a+b)
    simpa only [ha,hb,hd,zero_add,add_zero] using h
  have h2 : Complex.I • f a b + star Complex.I • f b a = 0 := by
    have h := hd (a+Complex.I • b)
    simpa only [ha,hb,hs,ht,hd,smul_zero,zero_add,add_zero] using h
  have hba : f b a = -f a b := eq_neg_of_add_eq_zero_right h1
  rw [hba,Complex.star_def,Complex.conj_I,neg_smul,smul_neg,neg_neg,← two_smul ℂ] at h2
  have hI : Complex.I • f a b = 0 := (smul_eq_zero.mp h2).resolve_left (by norm_num)
  exact (smul_eq_zero.mp hI).resolve_left Complex.I_ne_zero

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma normalizedFourier_star_mul (S : StandardModularData H) (t : ℝ)
    (ht : 0 < (kernelFourier t).re) (b c : S.M.commutant.toStarSubalgebra) :
    S.normalizedFourier t (star b*c) =
      S.normalizedFourier t c * star (S.normalizedFourier t b) := by
  apply sub_eq_zero.mp
  let f : S.M.commutant.toStarSubalgebra → S.M.commutant.toStarSubalgebra → S.M.toStarSubalgebra :=
    fun b c => S.normalizedFourier t (star b*c) - S.normalizedFourier t c * star (S.normalizedFourier t b)
  show f b c = 0
  apply sesq_zero_of_diagonal f
  · intro a b c
    dsimp only [f]
    simp only [star_add,add_mul,S.normalizedFourier_add,mul_add]
    abel
  · intro a b c
    dsimp only [f]
    simp only [mul_add,S.normalizedFourier_add,add_mul]
    abel
  · intro z a b
    dsimp only [f]
    simp only [star_smul,smul_mul_assoc,S.normalizedFourier_smul,mul_smul_comm,smul_sub]
  · intro z a b
    dsimp only [f]
    simp only [mul_smul_comm,S.normalizedFourier_smul,smul_mul_assoc,smul_sub]
  · intro a
    exact sub_eq_zero.mpr (S.normalizedFourier_star_square t ht a)

lemma normalizedFourier_mul (S : StandardModularData H) (t : ℝ)
    (ht : 0 < (kernelFourier t).re) (b c : S.M.commutant.toStarSubalgebra) :
    S.normalizedFourier t (b*c) = S.normalizedFourier t c * S.normalizedFourier t b := by
  simpa only [star_star,S.normalizedFourier_star] using S.normalizedFourier_star_mul t ht (star b) c

end StandardModularData
end BoundedRecovery

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.ModularCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial Tomita conjugation and modular covariance. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma normalizedFourier_on_dense (S : StandardModularData H) (t : ℝ)
    (ht : 0 < (kernelFourier t).re) (b : S.M.commutant.toStarSubalgebra) (x : H) :
    (S.normalizedFourier t b:H →L[ℂ] H) (S.D.unitary t (S.J x)) =
      S.D.unitary t (S.J ((star (b:H →L[ℂ] H)) x)) := by
  refine (commutant_cyclic S.M S.xi S.separating).induction ?_ ?_ x
  · rintro v ⟨c,hc,rfl⟩
    let c' : S.M.commutant.toStarSubalgebra := ⟨c,hc⟩
    have he := congrArg (fun a : S.M.toStarSubalgebra => (a:H →L[ℂ] H) S.xi)
      (S.normalizedFourier_mul t ht (star c') b)
    change (S.normalizedFourier t (star c'*b):H →L[ℂ] H) S.xi =
      (S.normalizedFourier t b:H →L[ℂ] H) ((S.normalizedFourier t (star c'):H →L[ℂ] H) S.xi) at he
    simp only [S.normalizedFourier_xi t (kernelFourier_ne_zero ht),star_mul,star_star] at he
    exact he.symm
  · exact isClosed_eq
      ((S.normalizedFourier t b:H →L[ℂ] H).continuous.comp ((S.D.unitary t).continuous.comp S.J.continuous))
      ((S.D.unitary t).continuous.comp (S.J.continuous.comp (star (b:H →L[ℂ] H)).continuous))

lemma normalizedFourier_spatial (S : StandardModularData H) (t : ℝ)
    (ht : 0 < (kernelFourier t).re) (b : S.M.commutant.toStarSubalgebra) :
    (S.normalizedFourier t b:H →L[ℂ] H) = S.sigma t (S.jConjugate (star (b:H →L[ℂ] H))) := by
  ext h
  have he := S.normalizedFourier_on_dense t ht b (S.J (S.D.unitary (-t) h))
  rw [S.conjugation] at he
  have hu : S.D.unitary t (S.D.unitary (-t) h) = h := by
    change (S.D.unitary t*S.D.unitary (-t)) h = h
    rw [S.D.unitary_mul_neg]
    rfl
  rw [hu] at he
  exact he

lemma sigma_jConjugate_mem (S : StandardModularData H) (t : ℝ)
    (ht : 0 < (kernelFourier t).re) (b : H →L[ℂ] H) (hb : b ∈ S.M.commutant) :
    S.sigma t (S.jConjugate b) ∈ S.M := by
  let c : S.M.commutant.toStarSubalgebra := ⟨star b,star_mem hb⟩
  have he := S.normalizedFourier_spatial t ht c
  change (S.normalizedFourier t c:H →L[ℂ] H) = S.sigma t (S.jConjugate (star (star b))) at he
  rw [star_star] at he
  exact he ▸ (S.normalizedFourier t c).property

lemma jConjugate_mem (S : StandardModularData H) (b : H →L[ℂ] H) (hb : b ∈ S.M.commutant) :
    S.jConjugate b ∈ S.M := by
  have hp : 0 < (kernelFourier 0).re := by
    rw [kernelFourier_zero,Complex.ofReal_re]
    exact kernelMass_pos
  simpa only [S.sigma_zero] using S.sigma_jConjugate_mem 0 hp b hb

lemma jConjugate_mem_commutant (S : StandardModularData H) (a : H →L[ℂ] H) (ha : a ∈ S.M) :
    S.jConjugate a ∈ S.M.commutant := by
  apply S.commutantData.jConjugate_mem a
  change a ∈ S.M.commutant.commutant
  simpa only [VonNeumannAlgebra.commutant_commutant] using ha

lemma sigma_mem_of_fourier_positive (S : StandardModularData H) (t : ℝ)
    (ht : 0 < (kernelFourier t).re) (a : H →L[ℂ] H) (ha : a ∈ S.M) :
    S.sigma t a ∈ S.M := by
  have hh := S.sigma_jConjugate_mem t ht (S.jConjugate a) (S.jConjugate_mem_commutant a ha)
  simpa only [S.jConjugate_involutive] using hh

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma modular_covariance (S : StandardModularData H) (t : ℝ) (a : H →L[ℂ] H) (ha : a ∈ S.M) :
    S.D.unitary t * a * S.D.unitary (-t) ∈ S.M := by
  obtain ⟨d,hd,hdt⟩ := kernelFourier_positive_near_zero
  have hlocal (r : ℝ) (hr : |r| < d) (b : H →L[ℂ] H) (hb : b ∈ S.M) : S.sigma r b ∈ S.M :=
    S.sigma_mem_of_fourier_positive r (hdt r hr) b hb
  have hiterate (r : ℝ) (hr : |r| < d) (n : ℕ) : S.sigma ((n:ℝ)*r) a ∈ S.M := by
    induction n with
    | zero => simpa only [Nat.cast_zero,zero_mul,S.sigma_zero] using ha
    | succ n ih =>
      rw [Nat.cast_succ,add_mul,one_mul,add_comm,S.sigma_add_time]
      exact hlocal r hr _ ih
  obtain ⟨n,hn⟩ := exists_nat_gt (|t|/d+1)
  have hnpos : 0 < (n:ℝ) := by have := div_nonneg (abs_nonneg t) hd.le; linarith
  have hdiv : |t/(n:ℝ)| < d := by
    rw [abs_div,abs_of_pos hnpos,div_lt_iff₀ hnpos]
    have he : |t|/d < (n:ℝ) := by linarith
    have hh := (div_lt_iff₀ hd).mp he
    nlinarith
  have hh := hiterate (t/(n:ℝ)) hdiv n
  have he : (n:ℝ)*(t/(n:ℝ)) = t := by field_simp
  rwa [he] at hh

end StandardModularData
end BoundedRecovery

end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.ErgodicAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hilbert-space and predual ergodic averaging for the modular action. -/

universe u uE uF uι

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma sigma_mem (S : StandardModularData H) (t : ℝ) {a : H →L[ℂ] H} (ha : a ∈ S.M) :
    S.sigma t a ∈ S.M := S.modular_covariance t a ha

@[simp] lemma sigma_apply_xi (S : StandardModularData H) (t : ℝ) (a : H →L[ℂ] H) :
    S.sigma t a S.xi = S.D.unitary t (a S.xi) := by
  simp [sigma, S.fixes_xi]

lemma sigma_mul (S : StandardModularData H) (t : ℝ) (a b : H →L[ℂ] H) :
    S.sigma t (a * b) = S.sigma t a * S.sigma t b := by
  simp only [sigma]
  have h := S.D.unitary_neg_mul t
  calc
    _ = S.D.unitary t * a * (1 * b) * S.D.unitary (-t) := by simp [mul_assoc]
    _ = _ := by rw [← h]; simp only [mul_assoc]

lemma sigma_star (S : StandardModularData H) (t : ℝ) (a : H →L[ℂ] H) :
    S.sigma t (star a) = star (S.sigma t a) := by
  simp [sigma, star_mul, mul_assoc]

lemma state_sigma (S : StandardModularData H) (t : ℝ) (a : H →L[ℂ] H) :
    S.state (S.sigma t a) = S.state a := by
  simp only [state, sigma_apply_xi]
  rw [← ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (star (S.D.unitary t) S.xi) (a S.xi) = _
  rw [S.D.unitary_star, S.fixes_xi]

lemma fixed_of_fixed_vector (S : StandardModularData H) {a : H →L[ℂ] H}
    (ha : a ∈ S.M) (hv : ∀ t, S.D.unitary t (a S.xi) = a S.xi) :
    ∀ t, S.sigma t a = a := by
  intro t
  apply sub_eq_zero.mp
  apply S.separating _ (sub_mem (S.sigma_mem t ha) ha)
  simp [hv]

lemma norm_star_apply_xi_le (S : StandardModularData H) {a : H →L[ℂ] H}
    (ha : a ∈ S.M) {I : Set ℝ} (hband : S.D.HasSpectralSupport I (a S.xi))
    {b : ℝ} (hb : ∀ u ∈ I, u ≤ b) :
    ‖star a S.xi‖ ≤ Real.exp (b / 2) * ‖a S.xi‖ := by
  have hg : (a S.xi, star a S.xi) ∈ closure {p : H × H | ∃ c : H →L[ℂ] H,
      c ∈ S.M ∧ p = (c S.xi, star c S.xi)} := subset_closure ⟨a, ha, rfl⟩
  rw [S.tomita_graph] at hg
  obtain ⟨q, hq, heq⟩ := hg
  change star a S.xi = S.J q at heq
  rw [heq, S.J.norm_map]
  exact RealSpectralCalculus.norm_halfGraph_le hband hb hq

lemma state_star_mul (S : StandardModularData H) (a : H →L[ℂ] H) :
    S.state (star a * a) = (‖a S.xi‖ ^ 2 : ℝ) := by
  change inner ℂ S.xi (ContinuousLinearMap.adjoint a (a S.xi)) = _
  rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

end StandardModularData

end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology
namespace BoundedRecovery

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma convex_bounded_orbit (M : VonNeumannAlgebra H) (xi : H) (C : ℝ) :
    Convex ℝ {v : H | ∃ a : H →L[ℂ] H, a ∈ M ∧ ‖a‖ ≤ C ∧ a xi = v} := by
  rintro x ⟨a, ha, han, rfl⟩ y ⟨b, hb, hbn, rfl⟩ r q hr hq hrq
  refine ⟨(r : ℂ) • a + (q : ℂ) • b,
    add_mem (M.toStarSubalgebra.smul_mem ha _) (M.toStarSubalgebra.smul_mem hb _), ?_, ?_⟩
  · calc
      _ ≤ ‖(r : ℂ) • a‖ + ‖(q : ℂ) • b‖ := norm_add_le _ _
      _ = r * ‖a‖ + q * ‖b‖ := by simp [norm_smul, abs_of_nonneg hr, abs_of_nonneg hq]
      _ ≤ r * C + q * C := add_le_add (mul_le_mul_of_nonneg_left han hr)
        (mul_le_mul_of_nonneg_left hbn hq)
      _ = C := by rw [← add_mul, hrq, one_mul]
  · simp

lemma small_on_separating_controls_vector (M : VonNeumannAlgebra H) (xi : H)
    (hsep : ∀ a : H →L[ℂ] H, a ∈ M → a xi = 0 → a = 0)
    (h : H) {C eps : ℝ} (hC : 0 ≤ C) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ a : H →L[ℂ] H, a ∈ M → ‖a‖ ≤ C →
      ‖a xi‖ < delta → ‖a h‖ < eps := by
  have hd := commutant_cyclic M xi hsep
  obtain ⟨v,hv,hvdist⟩ := Metric.mem_closure_iff.mp (hd h)
    (eps / (2 * (C+1))) (by positivity)
  obtain ⟨b,hb,rfl⟩ := hv
  have hbcomm (a : H →L[ℂ] H) (ha : a ∈ M) : a * b = b * a :=
    (VonNeumannAlgebra.mem_commutant_iff.mp hb) a ha
  refine ⟨eps / (2 * (‖b‖+1)), by positivity, ?_⟩
  intro a ha hab haxi
  have hsmall : ‖h-b xi‖ < eps / (2*(C+1)) := by
    simpa only [dist_eq_norm] using hvdist
  have hfirst : C * ‖h-b xi‖ < eps/2 := by
    calc
      _ ≤ (C+1) * ‖h-b xi‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (C+1) * (eps/(2*(C+1))) := mul_lt_mul_of_pos_left hsmall (by positivity)
      _ = eps/2 := by field_simp
  have hsecond : ‖b‖ * ‖a xi‖ < eps/2 := by
    calc
      _ ≤ (‖b‖+1) * ‖a xi‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (‖b‖+1) * (eps/(2*(‖b‖+1))) := mul_lt_mul_of_pos_left haxi (by positivity)
      _ = eps/2 := by field_simp
  have heq : a h = a (h-b xi) + b (a xi) := by
    have hc := congrArg (fun q : H →L[ℂ] H => q xi) (hbcomm a ha)
    change a (b xi) = b (a xi) at hc
    rw [map_sub, ← hc, sub_add_cancel]
  rw [heq]
  calc
    _ ≤ ‖a (h-b xi)‖ + ‖b (a xi)‖ := norm_add_le _ _
    _ ≤ C * ‖h-b xi‖ + ‖b‖ * ‖a xi‖ := add_le_add
      ((a.le_opNorm _).trans (mul_le_mul_of_nonneg_right hab (norm_nonneg _))) (b.le_opNorm _)
    _ < eps := by linarith

end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology
namespace BoundedRecovery

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma convex_minimizer_unique {K : Set E} (hK : Convex ℝ K) {v w : E}
    (hv : v ∈ K) (hw : w ∈ K)
    (hvm : ‖(0 : E) - v‖ = ⨅ a : K, ‖(0 : E) - a‖)
    (hwm : ‖(0 : E) - w‖ = ⨅ a : K, ‖(0 : E) - a‖) : v = w := by
  have h₁ := (norm_eq_iInf_iff_real_inner_le_zero hK hv).mp hvm w hw
  have h₂ := (norm_eq_iInf_iff_real_inner_le_zero hK hw).mp hwm v hv
  have hn := norm_sub_sq_real v w
  have hi := real_inner_comm v w
  simp only [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at h₁ h₂
  have hz : ‖v - w‖ = 0 := by nlinarith [norm_nonneg (v - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

lemma exists_fixed_in_closed_convex_orbit
    (U : ℝ → E →L[ℝ] E) (hadd : ∀ t r, U (t + r) = U t * U r)
    (hnorm : ∀ t v, ‖U t v‖ = ‖v‖) (x : E) :
    ∃ v ∈ closure (convexHull ℝ (Set.range (fun t => U t x))), ∀ t, U t v = v := by
  let K := closure (convexHull ℝ (Set.range (fun t => U t x)))
  have hK : Convex ℝ K := (convex_convexHull ℝ _).closure
  have hne : K.Nonempty := ⟨U 0 x, subset_closure (subset_convexHull ℝ _ ⟨0, rfl⟩)⟩
  obtain ⟨v, hv, hvm⟩ := exists_norm_eq_iInf_of_complete_convex hne isClosed_closure.isComplete hK 0
  refine ⟨v, hv, fun t => ?_⟩
  have hinv : Set.MapsTo (U t) K K := by
    apply closure_minimal ?_ (isClosed_closure.preimage (U t).continuous)
    apply convexHull_min ?_ (hK.linear_preimage (U t).toLinearMap)
    rintro y ⟨r, rfl⟩
    apply subset_closure
    apply subset_convexHull
    exact ⟨t + r, by change U (t + r) x = U t (U r x); rw [hadd]; rfl⟩
  apply convex_minimizer_unique hK (hinv hv) hv
  · simpa only [zero_sub, norm_neg, hnorm] using hvm
  · exact hvm

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma map_mem_closed_convexHull [NormedSpace ℝ E] {F : Type uF}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {s : Set E} {x : E}
    (hx : x ∈ closure (convexHull ℝ s)) :
    L x ∈ closure (convexHull ℝ (L '' s)) := by
  apply (closure_minimal (convexHull_min ?_
    ((convex_convexHull ℝ _).closure.linear_preimage L.toLinearMap))
    (isClosed_closure.preimage L.continuous)) hx
  intro y hy
  exact subset_closure (subset_convexHull ℝ _ (Set.mem_image_of_mem L hy))

end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace StandardModularData

lemma inner_fixed_on_closed_convex_orbit (S : StandardModularData H) (a : H →L[ℂ] H)
    {v : H} (hv : v ∈ closure (convexHull ℝ (Set.range (fun t => S.D.unitary t (a S.xi))))) :
    inner ℂ S.xi v = S.state a := by
  have hconv : Convex ℝ {w : H | inner ℂ S.xi w = S.state a} :=
    (convex_singleton (S.state a)).linear_preimage ((innerSL ℂ S.xi).toLinearMap.restrictScalars ℝ)
  apply (closure_minimal (convexHull_min ?_ hconv)
    (isClosed_eq (by fun_prop) continuous_const)) hv
  rintro w ⟨t, rfl⟩
  change inner ℂ S.xi (S.D.unitary t (a S.xi)) = S.state a
  rw [← S.sigma_apply_xi]
  exact S.state_sigma t a

lemma fixed_eq_state_of_mem_closed_convex_orbit (S : StandardModularData H)
    (hscalar : S.ScalarCentralizer) {a : H →L[ℂ] H} (ha : a ∈ S.M)
    {v : H} (hv : v ∈ closure (convexHull ℝ (Set.range (fun t => S.D.unitary t (a S.xi)))))
    (hfix : ∀ t, S.D.unitary t v = v) : v = S.state a • S.xi := by
  have hsub : closure (convexHull ℝ (Set.range (fun t => S.D.unitary t (a S.xi)))) ⊆
      {w : H | ∃ b : H →L[ℂ] H, b ∈ S.M ∧ ‖b‖ ≤ ‖a‖ ∧ b S.xi = w} := by
    apply closure_minimal ?_ (isClosed_bounded_orbit S.M S.xi S.separating (norm_nonneg _))
    apply convexHull_min ?_ (convex_bounded_orbit S.M S.xi ‖a‖)
    rintro w ⟨t, rfl⟩
    exact ⟨S.sigma t a, S.sigma_mem t ha, (S.norm_sigma t a).le, S.sigma_apply_xi t a⟩
  obtain ⟨b, hb, _, hbv⟩ := hsub hv
  obtain ⟨c, hc⟩ := hscalar b hb (S.fixed_of_fixed_vector hb (by simpa only [hbv] using hfix))
  have hvc : v = c • S.xi := by rw [hc] at hbv; simpa using hbv.symm
  have hinner := S.inner_fixed_on_closed_convex_orbit a hv
  rw [hvc, inner_smul_right, inner_self_eq_one_of_norm_eq_one S.norm_xi, mul_one] at hinner
  exact hvc.trans (congrArg (fun d : ℂ => d • S.xi) hinner)

lemma pair_state_mem_closed_convex_orbit (S : StandardModularData H)
    (hscalar : S.ScalarCentralizer) {a b : H →L[ℂ] H} (ha : a ∈ S.M) (hb : b ∈ S.M) :
    WithLp.toLp 2 (S.state a • S.xi, S.state b • S.xi) ∈ closure (convexHull ℝ
      (Set.range (fun t => WithLp.toLp 2
        (S.D.unitary t (a S.xi), S.D.unitary t (b S.xi))))) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  let L (t : ℝ) : H →ₗᵢ[ℝ] H :=
    { toLinearMap := (S.D.unitary t).toLinearMap.restrictScalars ℝ
      norm_map' := S.D.norm_unitary_apply t }
  let V (t : ℝ) : WithLp 2 (H × H) →L[ℝ] WithLp 2 (H × H) :=
    ((L t).withLpProdMap 2 (L t)).toContinuousLinearMap
  have hV (t r : ℝ) : V (t + r) = V t * V r := by
    apply ContinuousLinearMap.ext
    intro w
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change S.D.unitary (t + r) w.fst = S.D.unitary t (S.D.unitary r w.fst)
      rw [S.D.unitary_add]
      rfl
    · change S.D.unitary (t + r) w.snd = S.D.unitary t (S.D.unitary r w.snd)
      rw [S.D.unitary_add]
      rfl
  obtain ⟨v, hv, hfix⟩ := exists_fixed_in_closed_convex_orbit V hV
    (fun t w => ((L t).withLpProdMap 2 (L t)).norm_map w) (WithLp.toLp 2 (a S.xi, b S.xi))
  have hv₁ : v.fst ∈ closure (convexHull ℝ (Set.range (fun t => S.D.unitary t (a S.xi)))) := by
    have hh := map_mem_closed_convexHull (WithLp.fstL 2 ℝ H H) hv
    rw [← Set.range_comp'] at hh
    exact hh
  have hv₂ : v.snd ∈ closure (convexHull ℝ (Set.range (fun t => S.D.unitary t (b S.xi)))) := by
    have hh := map_mem_closed_convexHull (WithLp.sndL 2 ℝ H H) hv
    rw [← Set.range_comp'] at hh
    exact hh
  have he₁ : v.fst = S.state a • S.xi := S.fixed_eq_state_of_mem_closed_convex_orbit
    hscalar ha hv₁ (fun t => congrArg WithLp.fst (hfix t))
  have he₂ : v.snd = S.state b • S.xi := S.fixed_eq_state_of_mem_closed_convex_orbit
    hscalar hb hv₂ (fun t => congrArg WithLp.snd (hfix t))
  have he : v = WithLp.toLp 2 (S.state a • S.xi, S.state b • S.xi) :=
    WithLp.ofLp_injective 2 (Prod.ext he₁ he₂)
  rw [he] at hv
  exact hv

lemma exists_finite_average_pair (S : StandardModularData H)
    (hscalar : S.ScalarCentralizer) {a b : H →L[ℂ] H} (ha : a ∈ S.M) (hb : b ∈ S.M)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ (n : ℕ) (p t : Fin n → ℝ), (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
      ‖(∑ i, p i • S.D.unitary (t i) (a S.xi)) - S.state a • S.xi‖ < eps ∧
      ‖(∑ i, p i • S.D.unitary (t i) (b S.xi)) - S.state b • S.xi‖ < eps := by
  classical
  obtain ⟨v, hv, hvdist⟩ := Metric.mem_closure_iff.mp
    (S.pair_state_mem_closed_convex_orbit hscalar ha hb) eps heps
  obtain ⟨ι, inst, p, z, hp, hsum, hz, hveq⟩ := mem_convexHull_iff_exists_fintype.mp hv
  let := inst
  choose t ht using hz
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, p ∘ e, t ∘ e, fun i => hp _, ?_, ?_, ?_⟩
  · simpa only [Function.comp_apply, Equiv.sum_comp] using hsum
  · have hh := lt_of_le_of_lt (WithLp.norm_fst_le H
      (v - WithLp.toLp 2 (S.state a • S.xi, S.state b • S.xi)))
      (by simpa only [dist_eq_norm, norm_sub_rev] using hvdist)
    change ‖(WithLp.fstL 2 ℝ H H) (v - WithLp.toLp 2 (S.state a • S.xi, S.state b • S.xi))‖ < eps at hh
    rw [← hveq, map_sub, map_sum] at hh
    have hzfst (i : ι) : (z i).fst = S.D.unitary (t i) (a S.xi) :=
      congrArg WithLp.fst (ht i).symm
    simp only [map_smul, WithLp.fstL_apply, WithLp.toLp_fst, hzfst] at hh
    rw [← e.sum_comp (fun i => p i • S.D.unitary (t i) (a S.xi))] at hh
    exact hh
  · have hh := lt_of_le_of_lt (WithLp.norm_snd_le H
      (v - WithLp.toLp 2 (S.state a • S.xi, S.state b • S.xi)))
      (by simpa only [dist_eq_norm, norm_sub_rev] using hvdist)
    change ‖(WithLp.sndL 2 ℝ H H) (v - WithLp.toLp 2 (S.state a • S.xi, S.state b • S.xi))‖ < eps at hh
    rw [← hveq, map_sub, map_sum] at hh
    have hzsnd (i : ι) : (z i).snd = S.D.unitary (t i) (b S.xi) :=
      congrArg WithLp.snd (ht i).symm
    simp only [map_smul, WithLp.sndL_apply, WithLp.toLp_snd, hzsnd] at hh
    rw [← e.sum_comp (fun i => p i • S.D.unitary (t i) (b S.xi))] at hh
    exact hh

end StandardModularData
end BoundedRecovery

noncomputable section
open scoped ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma re_vectorState_sq (xi : H) {a : H →L[ℂ] H} (ha : IsSelfAdjoint a) :
    (vectorStateLM xi (a ^ 2)).re = ‖a xi‖ ^ 2 := by
  have he : a ^ 2 = star a * a := by rw [ha.star_eq, pow_two]
  rw [he, vectorState_star_mul]
  rfl

end BoundedRecovery

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma sigma_sum {ι : Type uι} [Fintype ι] (S : StandardModularData H) (t : ℝ)
    (a : ι → H →L[ℂ] H) : S.sigma t (∑ i, a i) = ∑ i, S.sigma t (a i) :=
  map_sum (S.sigmaLinear t) a Finset.univ

lemma sigma_real_smul (S : StandardModularData H) (t c : ℝ) (a : H →L[ℂ] H) :
    S.sigma t (c • a) = c • S.sigma t a := (S.sigmaLinear t).map_smul_of_tower c a

lemma state_sandwich (S : StandardModularData H) (y a : H →L[ℂ] H) :
    S.state (star y * a * y) = inner ℂ (y S.xi) (a (y S.xi)) := by
  change inner ℂ S.xi (ContinuousLinearMap.adjoint y (a (y S.xi))) = _
  exact ContinuousLinearMap.adjoint_inner_right y S.xi (a (y S.xi))

lemma state_covariant_sandwich (S : StandardModularData H) (t : ℝ) (y a : H →L[ℂ] H) :
    S.state (star (S.sigma t y) * a * S.sigma t y) =
      S.state (star y * S.sigma (-t) a * y) := by
  rw [← S.state_sigma (-t) (star (S.sigma t y) * a * S.sigma t y)]
  simp only [S.sigma_mul, S.sigma_star, ← S.sigma_add_time, neg_add_cancel, S.sigma_zero]

lemma norm_state_real_star_mul (S : StandardModularData H) (y : H →L[ℂ] H) :
    ‖y S.xi‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  have h := y.le_opNorm S.xi
  rw [S.norm_xi, mul_one] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

lemma state_star_mul_re (S : StandardModularData H) (y : H →L[ℂ] H) :
    (S.state (star y * y)).re = ‖y S.xi‖ ^ 2 := by rw [S.state_star_mul]; rfl

lemma state_mul_star (S : StandardModularData H) (y : H →L[ℂ] H) :
    S.state (y * star y) = (‖star y S.xi‖ ^ 2 : ℝ) := by
  simpa only [star_star] using S.state_star_mul (star y)

lemma state_sq_re (S : StandardModularData H) {a : H →L[ℂ] H} (ha : IsSelfAdjoint a) :
    (S.state (a ^ 2)).re = ‖a S.xi‖ ^ 2 := re_vectorState_sq S.xi ha

end StandardModularData
end BoundedRecovery

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.FiniteMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous finite approximations of modular moments. -/

universe u uE uι

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
namespace BoundedRecovery
variable {ι : Type uι} [Fintype ι]
lemma norm_sum_probability_smul_le {E : Type uE} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : (∑ i, p i) = 1)
    (f : ι → E) {C : ℝ} (hf : ∀ i, ‖f i‖ ≤ C) : ‖∑ i, p i • f i‖ ≤ C := by
  calc
    _ ≤ ∑ i, ‖p i • f i‖ := norm_sum_le _ _
    _ = ∑ i, p i * ‖f i‖ := by simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hp _)]
    _ ≤ ∑ i, p i * C := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i) (hp i))
    _ = C := by rw [← Finset.sum_mul, hsum, one_mul]
end BoundedRecovery

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData
variable {ι : Type uι} [Fintype ι]

lemma real_smul_mem (S : StandardModularData H) {a : H →L[ℂ] H} (ha : a ∈ S.M) (r : ℝ) :
    r • a ∈ S.M := by
  have hm := S.M.toStarSubalgebra.smul_mem ha (algebraMap ℝ ℂ r)
  rw [algebraMap_smul] at hm
  exact hm

lemma modularAverage_mem (S : StandardModularData H) (p t : ι → ℝ) {a : H →L[ℂ] H}
    (ha : a ∈ S.M) : S.modularAverage p t a ∈ S.M := by
  exact sum_mem (fun i _ => S.real_smul_mem (S.sigma_mem (t i) ha) (p i))

lemma norm_modularAverage_le (S : StandardModularData H) (p t : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : (∑ i, p i) = 1) (a : H →L[ℂ] H) :
    ‖S.modularAverage p t a‖ ≤ ‖a‖ :=
  norm_sum_probability_smul_le p hp hsum _ (fun i => (S.norm_sigma (t i) a).le)

lemma modularAverage_apply_xi (S : StandardModularData H) (p t : ι → ℝ) (a : H →L[ℂ] H) :
    S.modularAverage p t a S.xi = ∑ i, p i • S.D.unitary (t i) (a S.xi) := by
  simp only [modularAverage, sum_apply, smul_apply, S.sigma_apply_xi]

lemma norm_modularAverage_apply_xi_sub_le (S : StandardModularData H) (p t : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : (∑ i, p i) = 1) (a : H →L[ℂ] H) (c : ℂ) :
    ‖S.modularAverage p t a S.xi - c • S.xi‖ ≤ ‖a S.xi - c • S.xi‖ := by
  have he : S.modularAverage p t a S.xi - c • S.xi =
      ∑ i, p i • S.D.unitary (t i) (a S.xi - c • S.xi) := by
    simp only [map_sub, map_smul, S.fixes_xi, smul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_smul, hsum, one_smul, S.modularAverage_apply_xi]
  rw [he]
  exact norm_sum_probability_smul_le p hp hsum _ (fun i => (S.D.norm_unitary_apply (t i) _).le)

lemma modularAverage_sandwich (S : StandardModularData H) (p t : ι → ℝ) (y b : H →L[ℂ] H) :
    (∑ i, p i * (S.state (star (S.sigma (t i) y) * b * S.sigma (t i) y)).re) =
      (inner ℂ (y S.xi) (S.modularAverage p (fun i => -t i) b (y S.xi))).re := by
  simp_rw [S.state_covariant_sandwich, S.state_sandwich]
  simp only [modularAverage, sum_apply, smul_apply, inner_sum, inner_smul_right_eq_smul, Complex.re_sum, Complex.smul_re, smul_eq_mul]

lemma averageSquare_eq (S : StandardModularData H) (p t : ι → ℝ) (y : H →L[ℂ] H) :
    (∑ i, p i • (star (S.sigma (t i) y) * S.sigma (t i) y)) =
      S.modularAverage p t (star y * y) := by
  simp only [modularAverage, S.sigma_mul, S.sigma_star]

lemma averageReverseSquare_eq (S : StandardModularData H) (p t : ι → ℝ) (y : H →L[ℂ] H) :
    (∑ i, p i • (S.sigma (t i) y * star (S.sigma (t i) y))) =
      S.modularAverage p t (y * star y) := by
  simp only [modularAverage, S.sigma_mul, S.sigma_star]

lemma isSelfAdjoint_averageSquare (p : ι → ℝ) (z : ι → H →L[ℂ] H) :
    IsSelfAdjoint (∑ i, p i • (star (z i) * z i)) := by
  simp only [IsSelfAdjoint, star_sum, star_smul, star_trivial, star_mul, star_star]

omit [CompleteSpace H] in
lemma re_inner_operator_le_of_small (h : H) (a : H →L[ℂ] H) (b : ℝ)
    (hsmall : ‖(a - b • (1 : H →L[ℂ] H)) h‖ < 1 / (‖h‖+1)) :
    (inner ℂ h (a h)).re < b * ‖h‖ ^ 2 + 1 := by
  let e := a - b • (1 : H →L[ℂ] H)
  have he : a h = e h + b • h := by simp [e]
  have hb : (inner ℂ h (b • h)).re = b * ‖h‖ ^ 2 := by
    rw [inner_smul_right_eq_smul, Complex.smul_re]
    simp only [smul_eq_mul]
    congr 1
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [he, inner_add_right, Complex.add_re, hb]
  have hi : (inner ℂ h (e h)).re ≤ ‖h‖ * ‖e h‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hn : ‖h‖ * ‖e h‖ < 1 := by
    calc
      _ ≤ (‖h‖+1) * ‖e h‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (‖h‖+1) * (1/(‖h‖+1)) := mul_lt_mul_of_pos_left hsmall (by positivity)
      _ = 1 := by field_simp
  linarith

end StandardModularData
end BoundedRecovery

end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.Mean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed free-ultrafilter mean of symmetric Lebesgue averages and orbit defects. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma exists_finite_moment_average (S : StandardModularData H)
    (hscalar : S.ScalarCentralizer) {y : H →L[ℂ] H} (hy : y ∈ S.M) :
    ∃ (n : ℕ) (p t : Fin n → ℝ), (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
      (S.state ((S.modularAverage p t (star y * y)) ^ 2)).re ≤
        (‖y S.xi‖ ^ 2 + 1) ^ 2 ∧
      (∑ i, p i * (S.state (star (S.sigma (t i) y) *
        S.modularAverage p t (y * star y) * S.sigma (t i) y)).re) ≤
        ‖y S.xi‖ ^ 2 * ‖star y S.xi‖ ^ 2 + 1 := by
  let q : ℝ := ‖y S.xi‖ ^ 2
  let b : ℝ := ‖star y S.xi‖ ^ 2
  have hq : 0 ≤ q := sq_nonneg _
  have hb : 0 ≤ b := sq_nonneg _
  have hbn : b ≤ ‖y‖ ^ 2 := by
    simpa only [b, norm_star] using S.norm_state_real_star_mul (star y)
  have hyn : 0 ≤ 2 * ‖y‖ ^ 2 := by positivity
  obtain ⟨delta,hdelta,hcontrol⟩ := small_on_separating_controls_vector
    S.M S.xi S.separating (y S.xi) hyn (show 0 < 1/(‖y S.xi‖+1) by positivity)
  obtain ⟨n,p,t,hp,hsum,hA,hB⟩ := S.exists_finite_average_pair hscalar
    (mul_mem (star_mem hy) hy) (mul_mem hy (star_mem hy)) (lt_min one_pos hdelta)
  let A := S.modularAverage p t (star y * y)
  let B := S.modularAverage p t (y * star y)
  let C := S.modularAverage p (fun i => -t i) B
  have hAsmall : ‖A S.xi - (q : ℂ) • S.xi‖ < 1 := by
    have := hA.trans_le (min_le_left _ _)
    simpa only [A, S.modularAverage_apply_xi, S.state_star_mul, q] using this
  have hBsmall : ‖B S.xi - (b : ℂ) • S.xi‖ < delta := by
    have := hB.trans_le (min_le_right _ _)
    simpa only [B, S.modularAverage_apply_xi, S.state_mul_star, b] using this
  have hCsmall : ‖C S.xi - (b : ℂ) • S.xi‖ < delta :=
    (S.norm_modularAverage_apply_xi_sub_le p (fun i => -t i) hp hsum B b).trans_lt hBsmall
  have hBmem : B ∈ S.M := S.modularAverage_mem p t (mul_mem hy (star_mem hy))
  have hCmem : C ∈ S.M := S.modularAverage_mem p _ hBmem
  have hCn : ‖C‖ ≤ ‖y‖ ^ 2 := by
    calc
      _ ≤ ‖B‖ := S.norm_modularAverage_le p _ hp hsum B
      _ ≤ ‖y * star y‖ := S.norm_modularAverage_le p t hp hsum _
      _ = ‖y‖ ^ 2 := by rw [CStarRing.norm_self_mul_star, pow_two]
  have hCbn : ‖C - b • (1 : H →L[ℂ] H)‖ ≤ 2 * ‖y‖ ^ 2 := by
    calc
      _ ≤ ‖C‖ + ‖b • (1 : H →L[ℂ] H)‖ := norm_sub_le _ _
      _ ≤ ‖y‖ ^ 2 + b := add_le_add hCn (by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
        exact mul_le_of_le_one_right hb ContinuousLinearMap.norm_id_le)
      _ ≤ _ := by linarith
  have hCd : ‖(C - b • (1 : H →L[ℂ] H)) S.xi‖ < delta := by
    change ‖C S.xi - b • S.xi‖ < delta
    rwa [← algebraMap_smul ℂ b S.xi]
  refine ⟨n,p,t,hp,hsum,?_,?_⟩
  · have hAn : ‖A S.xi‖ ≤ q + 1 := by
      have hc : ‖(q : ℂ) • S.xi‖ = q := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq, S.norm_xi, mul_one]
      have hh := norm_le_norm_sub_add (A S.xi) ((q : ℂ) • S.xi)
      rw [hc] at hh
      linarith
    have hAA : IsSelfAdjoint A := by
      dsimp only [A]
      rw [← S.averageSquare_eq]
      exact isSelfAdjoint_averageSquare p _
    rw [S.state_sq_re hAA]
    exact pow_le_pow_left₀ (norm_nonneg _) hAn 2
  · rw [S.modularAverage_sandwich]
    have hh := hcontrol (C - b • (1 : H →L[ℂ] H))
      (sub_mem hCmem (S.real_smul_mem (one_mem S.M) b)) hCbn hCd
    have hr := re_inner_operator_le_of_small (y S.xi) C b hh
    dsimp [q,b] at *
    nlinarith

end StandardModularData
end BoundedRecovery

namespace BoundedRecovery

lemma symmetricAverage_mono (f g : BoundedContinuousFunction ℝ ℝ)
    (hfg : ∀ t, f t ≤ g t) (k : ℕ) : symmetricAverage f k ≤ symmetricAverage g k := by
  unfold symmetricAverage
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact intervalIntegral.integral_mono_on (by linarith [Nat.cast_nonneg (α := ℝ) k])
    (f.continuous.intervalIntegrable _ _) (g.continuous.intervalIntegrable _ _)
    (fun t _ => hfg t)

lemma fixedMean_mono (omega : Ultrafilter ℕ) (f g : BoundedContinuousFunction ℝ ℝ)
    (hfg : ∀ t, f t ≤ g t) : fixedMean omega f ≤ fixedMean omega g := by
  exact le_of_tendsto_of_tendsto (tendsto_symmetricAverage_mean omega f)
    (tendsto_symmetricAverage_mean omega g)
    (Filter.Eventually.of_forall (symmetricAverage_mono f g hfg))

lemma symmetricAverage_const (c : ℝ) {k : ℕ} (hk : k ≠ 0) :
    symmetricAverage (fun _ => c) k = c := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  simp only [symmetricAverage, intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

lemma fixedMean_const (omega : Ultrafilter ℕ) (hω : (omega : Filter ℕ) ≤ atTop) (c : ℝ) :
    fixedMean omega (fun _ => c) = c := by
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [hω (eventually_ge_atTop 1)] with k hk
  exact (symmetricAverage_const c (by omega)).symm

lemma norm_symmetricAverage_translate_sub_le (f : BoundedContinuousFunction ℝ ℝ)
    (r : ℝ) (k : ℕ) :
    ‖symmetricAverage (translateBCF f r) k - symmetricAverage f k‖ ≤
      (2 * (k : ℝ))⁻¹ * (2 * ‖f‖ * |r|) := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (f.continuous.intervalIntegrable (-(k : ℝ)) (k : ℝ))
    (f.continuous.intervalIntegrable (k : ℝ) ((k : ℝ)+r))
  have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (f.continuous.intervalIntegrable (-(k : ℝ)) (-(k : ℝ)+r))
    (f.continuous.intervalIntegrable (-(k : ℝ)+r) ((k : ℝ)+r))
  have he : (∫ t in -(k : ℝ)+r..(k : ℝ)+r, f t) - (∫ t in -(k : ℝ)..(k : ℝ), f t) =
      (∫ t in (k : ℝ)..(k : ℝ)+r, f t) - (∫ t in -(k : ℝ)..-(k : ℝ)+r, f t) := by
    linarith
  have hb (a : ℝ) : ‖∫ t in a..a+r, f t‖ ≤ ‖f‖ * |r| := by
    simpa only [add_sub_cancel_left] using intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := a+r) (fun t _ => f.norm_coe_le_norm t)
  simp only [symmetricAverage, translateBCF_apply,
    intervalIntegral.integral_comp_add_right, ← mul_sub, he, norm_mul]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 * (k : ℝ))⁻¹)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_sub_le _ _).trans (by linarith [hb (k : ℝ), hb (-(k : ℝ))])

lemma tendsto_symmetricAverage_translate_sub (f : BoundedContinuousFunction ℝ ℝ) (r : ℝ) :
    Tendsto (fun k => symmetricAverage (translateBCF f r) k - symmetricAverage f k)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm (norm_symmetricAverage_translate_sub_le f r)
  have hk : Tendsto (fun k : ℕ => 2 * (k : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun k => by linarith [Nat.cast_nonneg (α := ℝ) k])
      (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop)
  simpa only [zero_mul, Function.comp_apply] using (tendsto_inv_atTop_zero.comp hk).mul_const (2*‖f‖*|r|)

lemma fixedMean_translate (omega : Ultrafilter ℕ) (hω : (omega : Filter ℕ) ≤ atTop)
    (f : BoundedContinuousFunction ℝ ℝ) (r : ℝ) :
    fixedMean omega (translateBCF f r) = fixedMean omega f := by
  apply sub_eq_zero.mp
  exact tendsto_nhds_unique
    ((tendsto_symmetricAverage_mean omega (translateBCF f r)).sub
      (tendsto_symmetricAverage_mean omega f))
    ((tendsto_symmetricAverage_translate_sub f r).mono_left hω)

lemma exists_lt_of_lt_fixedMean (omega : Ultrafilter ℕ) (hω : (omega : Filter ℕ) ≤ atTop)
    (f : BoundedContinuousFunction ℝ ℝ) {c : ℝ} (hc : c < fixedMean omega f) :
    ∃ t, c < f t := by
  by_contra! hn
  have hm := fixedMean_mono omega f (BoundedContinuousFunction.const ℝ c) hn
  rw [show (BoundedContinuousFunction.const ℝ c : ℝ → ℝ) = (fun _ => c) from rfl,
    fixedMean_const omega hω c] at hm
  exact (not_le_of_gt hc) hm

end BoundedRecovery

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace RealSpectralCalculus

lemma norm_orbitDefect_sub_le (D : RealSpectralCalculus H) (T : H →L[ℂ] H) (h k : H) :
    ‖D.orbitDefect T h - D.orbitDefect T k‖ ≤ ‖T‖ ^ 2 * (‖h‖+‖k‖) * ‖h-k‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro t
  change ‖‖T (D.unitary t h)‖ ^ 2 - ‖T (D.unitary t k)‖ ^ 2‖ ≤ _
  have hb (v : H) : ‖T (D.unitary t v)‖ ≤ ‖T‖ * ‖v‖ := by
    simpa only [D.norm_unitary_apply] using T.le_opNorm (D.unitary t v)
  have hd : |‖T (D.unitary t h)‖ - ‖T (D.unitary t k)‖| ≤ ‖T‖ * ‖h-k‖ := by
    exact (abs_norm_sub_norm_le _ _).trans (by simpa only [map_sub] using hb (h-k))
  rw [Real.norm_eq_abs, sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [mul_comm]
  calc
    _ ≤ (‖T‖ * ‖h-k‖) * (‖T‖ * ‖h‖ + ‖T‖ * ‖k‖) :=
      mul_le_mul hd (add_le_add (hb h) (hb k)) (by positivity) (by positivity)
    _ = _ := by ring

lemma abs_mean_orbitDefect_sub_le (D : RealSpectralCalculus H) (omega : Ultrafilter ℕ)
    (T : H →L[ℂ] H) (h k : H) :
    |fixedMean omega (D.orbitDefect T h) - fixedMean omega (D.orbitDefect T k)| ≤
      ‖T‖ ^ 2 * (‖h‖+‖k‖) * ‖h-k‖ := by
  have hm := norm_fixedMean_le omega (D.orbitDefect T h - D.orbitDefect T k)
  change ‖meanCLM omega (D.orbitDefect T h - D.orbitDefect T k)‖ ≤ _ at hm
  rw [map_sub] at hm
  exact hm.trans (D.norm_orbitDefect_sub_le T h k)

lemma mean_orbitDefect_nonneg (D : RealSpectralCalculus H) (omega : Ultrafilter ℕ)
    (T : H →L[ℂ] H) (h : H) : 0 ≤ fixedMean omega (D.orbitDefect T h) := by
  have hh := fixedMean_mono omega 0 (D.orbitDefect T h) (fun t => sq_nonneg _)
  have hz : fixedMean omega (0 : BoundedContinuousFunction ℝ ℝ) = 0 :=
    (meanCLM omega).map_zero
  rwa [hz] at hh

end RealSpectralCalculus
end BoundedRecovery

end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.FourthMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact noncommutative fourth-moment pairings and overlap subtraction. -/

universe u uA uB uι

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData
variable {ι : Type uι} [Fintype ι]

lemma modularAverage_add_time (S : StandardModularData H) (p t : ι → ℝ)
    (r : ℝ) (a : H →L[ℂ] H) :
    S.modularAverage p (fun i => r + t i) a = S.sigma r (S.modularAverage p t a) := by
  simp only [modularAverage, S.sigma_sum, S.sigma_real_smul, S.sigma_add_time]

lemma average_square_state_translate (S : StandardModularData H) (p t : ι → ℝ)
    (r : ℝ) (a : H →L[ℂ] H) :
    S.state ((S.modularAverage p (fun i => r+t i) a)^2) =
      S.state ((S.modularAverage p t a)^2) := by
  rw [S.modularAverage_add_time, pow_two, ← S.sigma_mul, S.state_sigma, ← pow_two]

lemma average_sandwich_state_translate (S : StandardModularData H) (p t : ι → ℝ)
    (r : ℝ) (y : H →L[ℂ] H) :
    (∑ i, p i * (S.state (star (S.sigma (r+t i) y) *
      S.modularAverage p (fun j => r+t j) (y*star y) * S.sigma (r+t i) y)).re) =
    (∑ i, p i * (S.state (star (S.sigma (t i) y) *
      S.modularAverage p t (y*star y) * S.sigma (t i) y)).re) := by
  simp only [S.modularAverage_add_time, S.sigma_add_time, ← S.sigma_star,
    ← S.sigma_mul, S.state_sigma]

lemma exists_translate_defect (S : StandardModularData H) (omega : Ultrafilter ℕ)
    (hω : (omega : Filter ℕ) ≤ atTop) (T : H →L[ℂ] H) (y : H →L[ℂ] H)
    (p t : ι → ℝ) (hsum : (∑ i, p i) = 1) {gamma : ℝ}
    (hg : gamma < fixedMean omega (S.D.orbitDefect T (y S.xi))) :
    ∃ r : ℝ, gamma < ∑ i, p i * ‖T (S.sigma (r+t i) y S.xi)‖ ^ 2 := by
  let f := S.D.orbitDefect T (y S.xi)
  let F : BoundedContinuousFunction ℝ ℝ := ∑ i, p i • translateBCF f (t i)
  have hmean : fixedMean omega F = fixedMean omega f := by
    change meanCLM omega (∑ i, p i • translateBCF f (t i)) = fixedMean omega f
    rw [map_sum]
    simp only [map_smul, meanCLM_apply, fixedMean_translate omega hω]
    rw [← Finset.sum_smul, hsum, one_smul]
  obtain ⟨r,hr⟩ := exists_lt_of_lt_fixedMean omega hω F (by rwa [hmean])
  refine ⟨r, ?_⟩
  simpa only [F, BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.smul_apply,
    translateBCF_apply, f, RealSpectralCalculus.orbitDefect_apply, S.sigma_apply_xi, smul_eq_mul] using hr

lemma exists_finite_defect_moment_average (S : StandardModularData H)
    (hscalar : S.ScalarCentralizer) (omega : Ultrafilter ℕ)
    (hω : (omega : Filter ℕ) ≤ atTop) (T : H →L[ℂ] H) {y : H →L[ℂ] H}
    (hy : y ∈ S.M) {gamma : ℝ}
    (hg : gamma < fixedMean omega (S.D.orbitDefect T (y S.xi))) :
    ∃ (n : ℕ) (p t : Fin n → ℝ), (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
      gamma ≤ ∑ i, p i * ‖T (S.sigma (t i) y S.xi)‖ ^ 2 ∧
      (S.state ((S.modularAverage p t (star y * y)) ^ 2)).re +
      (∑ i, p i * (S.state (star (S.sigma (t i) y) *
        S.modularAverage p t (y * star y) * S.sigma (t i) y)).re) ≤
        (‖y S.xi‖ ^ 2 + 1) ^ 2 + ‖y S.xi‖ ^ 2 * ‖star y S.xi‖ ^ 2 + 1 := by
  obtain ⟨n,p,t,hp,hsum,hA,hB⟩ := S.exists_finite_moment_average hscalar hy
  obtain ⟨r,hr⟩ := S.exists_translate_defect omega hω T y p t hsum hg
  refine ⟨n,p,(fun i => r+t i),hp,hsum,hr.le,?_⟩
  rw [S.average_square_state_translate, S.average_sandwich_state_translate]
  linarith

end StandardModularData
end BoundedRecovery

noncomputable section

namespace BoundedRecovery

section AlgebraicPhases

variable {A : Type uA} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

lemma phase_quadratic_step (x y b : A) :
    phaseAverage (fun i => star (x + phase i • y) * b * (x + phase i • y)) =
      star x * b * x + star y * b * y := by
  simp only [phaseAverage, Fin.sum_univ_succ, phase, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero,
    one_smul, neg_smul, star_add, star_smul,
    Complex.star_def, map_neg, map_one, Complex.conj_I,
    mul_add, add_mul, smul_mul_assoc, mul_smul_comm]
  match_scalars <;> ring_nf
  all_goals norm_num [Complex.I_sq]

lemma phase_fourth_step (x y : A) :
    phaseAverage (fun i => (star (x + phase i • y) * (x + phase i • y)) ^ 2) =
      (star x * x) ^ 2 + (star y * y) ^ 2 +
        star x * x * (star y * y) + star y * y * (star x * x) +
        star x * (y * star y) * x + star y * (x * star x) * y := by
  simp only [phaseAverage, Fin.sum_univ_succ, phase, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero,
    one_smul, neg_smul, star_add, star_smul,
    Complex.star_def, map_neg, map_one, Complex.conj_I, pow_two,
    mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
    mul_assoc]
  match_scalars <;> ring_nf
  all_goals norm_num [Complex.I_sq]

lemma phase_reverse_quadratic_step (x y b : A) :
    phaseAverage (fun i => (x + phase i • y) * b * star (x + phase i • y)) =
      x * b * star x + y * b * star y := by
  simp only [phaseAverage, Fin.sum_univ_succ, phase, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, one_smul, neg_smul, star_add,
    star_smul, Complex.star_def, map_neg, map_one, Complex.conj_I,
    mul_add, add_mul, smul_mul_assoc, mul_smul_comm]
  match_scalars <;> ring_nf
  all_goals norm_num [Complex.I_sq]

end AlgebraicPhases

section PhaseExpectation
variable {A : Type uA} [AddCommMonoid A] [Module ℂ A]

lemma phaseExpectation_add (n : ℕ) (f g : (Fin n → Fin 4) → A) :
    phaseExpectation n (fun e => f e + g e) = phaseExpectation n f + phaseExpectation n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [phaseExpectation, Finset.sum_add_distrib, smul_add]
    exact ih _ _

lemma phaseExpectation_const (n : ℕ) (a : A) : phaseExpectation n (fun _ => a) = a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : (1 / 4 : ℂ) • ∑ _i : Fin 4, a = a := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      module
    simp only [phaseExpectation, h, ih]

lemma phaseExpectation_map {B : Type uB} [AddCommMonoid B] [Module ℂ B]
    (L : A →ₗ[ℂ] B) (n : ℕ) (f : (Fin n → Fin 4) → A) :
    phaseExpectation n (fun e => L (f e)) = L (phaseExpectation n f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [phaseExpectation, ← map_sum, ← map_smul]
    exact ih _

end PhaseExpectation

section RingExpectation
variable {A : Type uA} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

omit [StarRing A] [StarModule ℂ A] in
lemma phaseExpectation_mul_left (n : ℕ) (f : (Fin n → Fin 4) → A) (a : A) :
    phaseExpectation n (fun e => a * f e) = a * phaseExpectation n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [phaseExpectation, ← Finset.mul_sum, ← mul_smul_comm]
    exact ih _

omit [StarRing A] [StarModule ℂ A] in
lemma phaseExpectation_mul_right (n : ℕ) (f : (Fin n → Fin 4) → A) (a : A) :
    phaseExpectation n (fun e => f e * a) = phaseExpectation n f * a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [phaseExpectation, ← Finset.sum_mul, ← smul_mul_assoc]
    exact ih _

omit [StarRing A] [StarModule ℂ A] in
lemma phaseSum_succ {n : ℕ} (a : Fin (n + 1) → A) (i : Fin 4) (e : Fin n → Fin 4) :
    phaseSum a (Fin.cons i e) = phaseSum (fun j => a j.succ) e + phase i • a 0 := by
  simp [phaseSum, Fin.sum_univ_succ, add_comm]

lemma phaseExpectation_quadratic (n : ℕ) (a : Fin n → A) (b : A) :
    phaseExpectation n (fun e => star (phaseSum a e) * b * phaseSum a e) =
      ∑ i, star (a i) * b * a i := by
  induction n with
  | zero => simp [phaseExpectation, phaseSum]
  | succ n ih =>
    simp only [phaseExpectation, phaseSum_succ]
    change phaseExpectation n (fun e => phaseAverage
      (fun i => star (phaseSum (fun j => a j.succ) e + phase i • a 0) * b *
        (phaseSum (fun j => a j.succ) e + phase i • a 0))) = _
    simp only [phase_quadratic_step, phaseExpectation_add, phaseExpectation_const, ih,
      Fin.sum_univ_succ]
    exact add_comm _ _

lemma phaseExpectation_reverse_quadratic (n : ℕ) (a : Fin n → A) (b : A) :
    phaseExpectation n (fun e => phaseSum a e * b * star (phaseSum a e)) =
      ∑ i, a i * b * star (a i) := by
  induction n with
  | zero => simp [phaseExpectation, phaseSum]
  | succ n ih =>
    simp only [phaseExpectation, phaseSum_succ]
    change phaseExpectation n (fun e => phaseAverage
      (fun i => (phaseSum (fun j => a j.succ) e + phase i • a 0) * b *
        star (phaseSum (fun j => a j.succ) e + phase i • a 0))) = _
    simp only [phase_reverse_quadratic_step, phaseExpectation_add, phaseExpectation_const, ih,
      Fin.sum_univ_succ]
    exact add_comm _ _

lemma phaseExpectation_square (n : ℕ) (a : Fin n → A) :
    phaseExpectation n (fun e => star (phaseSum a e) * phaseSum a e) =
      ∑ i, star (a i) * a i := by
  simpa using phaseExpectation_quadratic n a 1

lemma phaseExpectation_reverse_square (n : ℕ) (a : Fin n → A) :
    phaseExpectation n (fun e => phaseSum a e * star (phaseSum a e)) =
      ∑ i, a i * star (a i) := by
  simpa using phaseExpectation_reverse_quadratic n a 1

lemma phaseExpectation_fourth (n : ℕ) (a : Fin n → A) :
    phaseExpectation n (fun e => (star (phaseSum a e) * phaseSum a e) ^ 2) =
      (∑ i, star (a i) * a i) ^ 2 +
        (∑ i, star (a i) * (∑ j, a j * star (a j)) * a i) -
        ∑ i, (star (a i) * a i) ^ 2 := by
  induction n with
  | zero => simp [phaseExpectation, phaseSum]
  | succ n ih =>
    simp only [phaseExpectation, phaseSum_succ]
    change phaseExpectation n (fun e => phaseAverage
      (fun i => (star (phaseSum (fun j => a j.succ) e + phase i • a 0) *
        (phaseSum (fun j => a j.succ) e + phase i • a 0)) ^ 2)) = _
    simp only [phase_fourth_step, phaseExpectation_add, phaseExpectation_const,
      phaseExpectation_mul_right, phaseExpectation_mul_left, phaseExpectation_square,
      phaseExpectation_reverse_square, phaseExpectation_quadratic, ih]
    simp only [Fin.sum_univ_succ, mul_add, add_mul, Finset.sum_add_distrib]
    noncomm_ring

end RingExpectation

lemma phaseMean_mono (n : ℕ) {f g : (Fin n → Fin 4) → ℝ} (h : ∀ e, f e ≤ g e) :
    phaseMean n f ≤ phaseMean n g := by
  induction n with
  | zero => exact h _
  | succ n ih =>
    apply ih
    intro e
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => h (Fin.cons i e))) (by norm_num)

lemma phaseMean_const (n : ℕ) (c : ℝ) : phaseMean n (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hx : (1 / 4 : ℝ) * ∑ _i : Fin 4, c = c := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      ring
    simp only [phaseMean, hx, ih]

lemma phaseMean_add (n : ℕ) (f g : (Fin n → Fin 4) → ℝ) :
    phaseMean n (fun e => f e + g e) = phaseMean n f + phaseMean n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [phaseMean, Finset.sum_add_distrib, mul_add]; exact ih _ _

lemma phaseMean_mul (n : ℕ) (c : ℝ) (f : (Fin n → Fin 4) → ℝ) :
    phaseMean n (fun e => c * f e) = c * phaseMean n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [phaseMean, ← Finset.mul_sum, mul_left_comm (1 / 4 : ℝ) c]
    exact ih _

lemma exists_phaseMean_le (n : ℕ) (f : (Fin n → Fin 4) → ℝ) :
    ∃ e, phaseMean n f ≤ f e := by
  classical
  obtain ⟨e, _, he⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  refine ⟨e, ?_⟩
  simpa only [phaseMean_const] using phaseMean_mono n (fun e' => he e' (Finset.mem_univ _))

lemma phaseMean_re (n : ℕ) (f : (Fin n → Fin 4) → ℂ) :
    phaseMean n (fun e => (f e).re) = (phaseExpectation n f).re := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [phaseMean, phaseExpectation]
    rw [← ih]
    congr 1
    funext e
    simp

end BoundedRecovery

noncomputable section
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma state_T_square (S : StandardModularData H) (T z : H →L[ℂ] H) :
    (S.state (star z * (star T * T) * z)).re = ‖T (z S.xi)‖ ^ 2 := by
  have he : star z * (star T * T) * z = star (T * z) * (T * z) := by
    simp only [star_mul]
    noncomm_ring
  rw [he, S.state_star_mul_re]
  rfl

lemma real_sqrt_sandwich {p : ℝ} (hp : 0 ≤ p) (z b : H →L[ℂ] H) :
    star (Real.sqrt p • z) * b * (Real.sqrt p • z) = p • (star z * b * z) := by
  simp only [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [← pow_two, Real.sq_sqrt hp]

lemma real_sqrt_square {p : ℝ} (hp : 0 ≤ p) (z : H →L[ℂ] H) :
    star (Real.sqrt p • z) * (Real.sqrt p • z) = p • (star z * z) := by
  simpa only [mul_one] using real_sqrt_sandwich hp z 1

lemma real_sqrt_reverse_square {p : ℝ} (hp : 0 ≤ p) (z : H →L[ℂ] H) :
    (Real.sqrt p • z) * star (Real.sqrt p • z) = p • (z * star z) := by
  simp only [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [← pow_two, Real.sq_sqrt hp]

lemma phaseMean_defect (S : StandardModularData H) (T : H →L[ℂ] H)
    (n : ℕ) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (z : Fin n → H →L[ℂ] H) :
    phaseMean n (fun e => ‖T (phaseSum (fun i => Real.sqrt (p i) • z i) e S.xi)‖ ^ 2) =
      ∑ i, p i * ‖T (z i S.xi)‖ ^ 2 := by
  simp_rw [← S.state_T_square T]
  rw [phaseMean_re]
  change (phaseExpectation n (fun e => vectorStateLM S.xi
    (star (phaseSum (fun i => Real.sqrt (p i) • z i) e) * (star T * T) *
      phaseSum (fun i => Real.sqrt (p i) • z i) e))).re = _
  rw [phaseExpectation_map, phaseExpectation_quadratic]
  simp only [real_sqrt_sandwich (hp _), map_sum, LinearMap.map_smul_of_tower,
    Complex.re_sum, Complex.smul_re, smul_eq_mul]
  rfl

lemma phaseMean_fourth_le (S : StandardModularData H)
    (n : ℕ) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (z : Fin n → H →L[ℂ] H) :
    phaseMean n (fun e => (S.state ((star (phaseSum (fun i => Real.sqrt (p i) • z i) e) *
      phaseSum (fun i => Real.sqrt (p i) • z i) e) ^ 2)).re) ≤
      (S.state ((∑ i, p i • (star (z i) * z i)) ^ 2)).re +
      ∑ i, p i * (S.state (star (z i) * (∑ j, p j • (z j * star (z j))) * z i)).re := by
  let a (i : Fin n) := Real.sqrt (p i) • z i
  rw [phaseMean_re]
  change (phaseExpectation n (fun e => vectorStateLM S.xi
    ((star (phaseSum a e) * phaseSum a e) ^ 2))).re ≤ _
  rw [phaseExpectation_map, phaseExpectation_fourth, map_sub, map_add, Complex.sub_re, Complex.add_re]
  have hsum : 0 ≤ (vectorStateLM S.xi (∑ i, (star (a i) * a i)^2)).re := by
    rw [map_sum, Complex.re_sum]
    apply Finset.sum_nonneg
    intro i _
    rw [re_vectorState_sq S.xi (IsSelfAdjoint.star_mul_self _)]
    positivity
  have hA : ∑ i, star (a i) * a i = ∑ i, p i • (star (z i) * z i) := by
    simp only [a, real_sqrt_square (hp _)]
  have hB : ∑ i, a i * star (a i) = ∑ i, p i • (z i * star (z i)) := by
    simp only [a, real_sqrt_reverse_square (hp _)]
  rw [hA, hB]
  have hC : (vectorStateLM S.xi
      (∑ i, star (a i) * (∑ j, p j • (z j * star (z j))) * a i)).re =
      ∑ i, p i * (S.state (star (z i) * (∑ j, p j • (z j * star (z j))) * z i)).re := by
    simp only [a, real_sqrt_sandwich (hp _), map_sum, LinearMap.map_smul_of_tower,
      Complex.re_sum, Complex.smul_re, smul_eq_mul]
    rfl
  rw [hC]
  exact sub_le_self _ hsum

end StandardModularData
end BoundedRecovery

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.FourierLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polar truncation and Fourier localization with a width-independent L1 bound. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma polarCutoff_vector_error_sq (xi : H) (z : H →L[ℂ] H) {K : ℝ} (hK : 0 < K) :
    ‖(z - polarCutoff z K) xi‖ ^ 2 ≤
      (K ^ 2)⁻¹ * (vectorStateLM xi ((star z * z) ^ 2)).re := by
  have hh := re_vectorState_mono xi (polarCutoff_error_le z hK)
  rw [vectorState_star_mul, LinearMap.map_smul_of_tower, Complex.smul_re] at hh
  exact hh

end BoundedRecovery

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace RealSpectralCalculus

lemma integral_character_mul (f : BoundedContinuousFunction ℝ ℂ)
    (k : ℝ → ℂ) (hk : Integrable k)
    (hfk : ∀ u, f u = ∫ t, k t * spectralCharacter t u)
    (q : BoundedContinuousFunction ℝ ℂ) (hq : HasCompactSupport (q : ℝ → ℂ)) :
    Integrable (fun t => k t • (spectralCharacter t * q)) ∧
      (∫ t, k t • (spectralCharacter t * q)) = f * q := by
  have hbound (t : ℝ) : ‖spectralCharacter t * q‖ ≤ ‖q‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro u
    change ‖spectralCharacter t u * q u‖ ≤ ‖q‖
    simpa only [norm_mul, spectralCharacter_norm, one_mul] using q.norm_coe_le_norm u
  have hi := integrable_smul_bounded_orbit hk (continuous_character_mul q hq) hbound
  refine ⟨hi, ?_⟩
  ext u
  have hEval := (BoundedContinuousFunction.evalCLM ℂ u).integral_comp_comm hi
  change (∫ t, k t • (spectralCharacter t * q)) u = f u * q u
  change (BoundedContinuousFunction.evalCLM ℂ u) (∫ t, k t • (spectralCharacter t * q)) = _
  rw [← hEval, hfk u, ← integral_mul_const]
  congr 1
  funext t
  change k t * (spectralCharacter t u * q u) = k t * spectralCharacter t u * q u
  ring

lemma calculus_eq_integratedUnitary (D : RealSpectralCalculus H)
    (f : BoundedContinuousFunction ℝ ℂ) (k : ℝ → ℂ) (hk : Integrable k)
    (hfk : ∀ u, f u = ∫ t, k t * spectralCharacter t u) :
    D.calculus f = D.integratedUnitary k hk := by
  have hclosed : IsClosed {h : H | D.calculus f h = D.integratedUnitary k hk h} :=
    isClosed_eq (D.calculus f).continuous (D.integratedUnitary k hk).continuous
  have hsub : {h : H | ∃ q : BoundedContinuousFunction ℝ ℂ,
      HasCompactSupport (q : ℝ → ℂ) ∧ ∃ v : H, D.calculus q v = h} ⊆
      {h : H | D.calculus f h = D.integratedUnitary k hk h} := by
    rintro h ⟨q, hq, v, rfl⟩
    obtain ⟨hi, heq⟩ := integral_character_mul f k hk hfk q hq
    change (D.calculus f * D.calculus q) v = _
    rw [← map_mul, ← heq]
    have hc := D.calculusCLM.integral_comp_comm hi
    change (D.calculusCLM (∫ t, k t • (spectralCharacter t * q))) v = _
    rw [← hc, ContinuousLinearMap.integral_apply (D.calculusCLM.integrable_comp hi)]
    change (∫ t, D.calculus (k t • (spectralCharacter t * q)) v) =
      ∫ t, k t • D.unitary t (D.calculus q v)
    simp only [map_smul, map_mul, smul_apply, mul_apply_eq_comp, unitary]
  have hall := closure_minimal hsub hclosed
  rw [D.nondegenerate.closure_eq] at hall
  exact ContinuousLinearMap.ext (fun h => hall (mem_univ h))

lemma calculus_apply_eq_integral (D : RealSpectralCalculus H)
    (f : BoundedContinuousFunction ℝ ℂ) (k : ℝ → ℂ) (hk : Integrable k)
    (hfk : ∀ u, f u = ∫ t, k t * spectralCharacter t u) (h : H) :
    D.calculus f h = ∫ t, k t • D.unitary t h := by
  rw [D.calculus_eq_integratedUnitary f k hk hfk]
  rfl
end RealSpectralCalculus

namespace StandardModularData

lemma norm_fourierFilter_le (S : StandardModularData H) (k : ℝ → ℂ) (hk : Integrable k)
    (a : H →L[ℂ] H) : ‖S.fourierFilter k hk a‖ ≤ (∫ t, ‖k t‖) * ‖a‖ :=
  norm_strongIntegral_le k hk _ _ (norm_nonneg a) _

lemma fourierFilter_mem (S : StandardModularData H) (k : ℝ → ℂ) (hk : Integrable k)
    {a : H →L[ℂ] H} (ha : a ∈ S.M) : S.fourierFilter k hk a ∈ S.M := by
  rw [← S.M.commutant_commutant, VonNeumannAlgebra.mem_commutant_iff]
  intro b hb
  apply ContinuousLinearMap.ext
  intro h
  have hi := integrable_smul_bounded_orbit hk (S.continuous_sigma_apply a h)
    (fun t => (S.sigma t a).le_opNorm h |>.trans_eq (by rw [S.norm_sigma]))
  change b (∫ t, k t • S.sigma t a h) = ∫ t, k t • S.sigma t a (b h)
  rw [← b.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [map_smul]
  congr 1
  have heq := (VonNeumannAlgebra.mem_commutant_iff.mp hb) (S.sigma t a) (S.sigma_mem t ha)
  exact (congrArg (fun c : H →L[ℂ] H => c h) heq).symm

lemma fourierFilter_apply_xi (S : StandardModularData H)
    (f : BoundedContinuousFunction ℝ ℂ) (k : ℝ → ℂ) (hk : Integrable k)
    (hfk : ∀ u, f u = ∫ t, k t * spectralCharacter t u) (a : H →L[ℂ] H) :
    S.fourierFilter k hk a S.xi = S.D.calculus f (a S.xi) := by
  rw [S.D.calculus_apply_eq_integral f k hk hfk]
  change (∫ t, k t • S.sigma t a S.xi) = _
  simp only [S.sigma_apply_xi]

end StandardModularData
end BoundedRecovery

noncomputable section
open Set MeasureTheory
open scoped FourierTransform
namespace BoundedRecovery

lemma bump0_fourier (u : ℝ) :
    (bump0 u : ℂ) = ∫ t, baseKernel t * Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) := by
  have hi := congrArg (fun f : SchwartzMap ℝ ℂ => f (u / (2 * Real.pi)))
    (FourierPair.fourierInv_fourier_eq (F := SchwartzMap ℝ ℂ) bumpSchwartz)
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at hi
  rw [bumpSchwartz_apply] at hi
  have hpi : 2 * Real.pi ≠ 0 := by positivity
  have he : 2 * Real.pi * (u / (2 * Real.pi)) = u := by field_simp
  rw [he] at hi
  rw [← hi]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
  change Complex.exp (((2 * Real.pi * ((u / (2 * Real.pi)) * t) : ℝ) : ℂ) * Complex.I) *
    (𝓕 bumpSchwartz) t = _
  have he' : 2 * Real.pi * ((u / (2 * Real.pi)) * t) = t * u := by field_simp
  rw [he']
  exact mul_comm _ _

lemma norm_bandMultiplier_le (s rho : ℝ) : ‖bandMultiplier s rho‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro u
  simpa only [bandMultiplier_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg bump0.nonneg] using (bump0.le_one (x := (u-s)/rho))

lemma bandMultiplier_one {s rho u : ℝ} (hrho : 0 < rho)
    (hu : u ∈ Icc (s-rho) (s+rho)) : bandMultiplier s rho u = 1 := by
  rw [bandMultiplier_apply, bump0.one_of_mem_closedBall]
  · simp
  · rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    change |(u-s)/rho| ≤ 1
    rw [abs_div, abs_of_pos hrho, div_le_one hrho]
    exact abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩

lemma bandMultiplier_zero {s rho u : ℝ} (hrho : 0 < rho)
    (hu : u ∉ Icc (s-2*rho) (s+2*rho)) : bandMultiplier s rho u = 0 := by
  rw [bandMultiplier_apply, bump0.zero_of_le_dist]
  · simp
  · rw [dist_zero_right, Real.norm_eq_abs]
    change 2 ≤ |(u-s)/rho|
    rw [abs_div, abs_of_pos hrho, le_div_iff₀ hrho]
    by_cases h : s-2*rho ≤ u
    · have h' : s+2*rho < u := lt_of_not_ge (fun hh => hu ⟨h,hh⟩)
      exact (by linarith : 2 * rho ≤ u-s).trans (le_abs_self _)
    · have h' : u < s-2*rho := lt_of_not_ge h
      exact (by linarith : 2 * rho ≤ -(u-s)).trans (neg_le_abs _)

lemma norm_bandKernel {s rho : ℝ} (hrho : 0 < rho) (t : ℝ) :
    ‖bandKernel s rho t‖ = rho * ‖baseKernel (rho*t)‖ := by
  simp [bandKernel, Complex.norm_exp, abs_of_pos hrho]

lemma integral_norm_bandKernel {s rho : ℝ} (hrho : 0 < rho) :
    (∫ t, ‖bandKernel s rho t‖) = ∫ t, ‖baseKernel t‖ := by
  simp_rw [norm_bandKernel hrho]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun t => ‖baseKernel t‖) rho]
  simp only [smul_eq_mul, abs_of_pos (inv_pos.mpr hrho)]
  rw [← mul_assoc, mul_inv_cancel₀ hrho.ne', one_mul]

lemma bandMultiplier_fourier {s rho : ℝ} (hrho : 0 < rho) (u : ℝ) :
    bandMultiplier s rho u =
      ∫ t, bandKernel s rho t * Complex.exp (((t*u : ℝ) : ℂ) * Complex.I) := by
  rw [bandMultiplier_apply, bump0_fourier]
  have he (t : ℝ) :
      bandKernel s rho t * Complex.exp (((t*u : ℝ) : ℂ) * Complex.I) =
      (rho : ℂ) * (baseKernel (rho*t) *
        Complex.exp ((((rho*t)*((u-s)/rho) : ℝ) : ℂ) * Complex.I)) := by
    unfold bandKernel
    rw [show (rho : ℂ) * Complex.exp (((-s*t : ℝ) : ℂ) * Complex.I) * baseKernel (rho*t) *
      Complex.exp (((t*u : ℝ) : ℂ) * Complex.I) =
      (rho : ℂ) * (baseKernel (rho*t) * (Complex.exp (((-s*t : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((t*u : ℝ) : ℂ) * Complex.I))) by ring, ← Complex.exp_add]
    congr 3
    have heR : -s*t + t*u = (rho*t)*((u-s)/rho) := by field_simp; ring
    rw [← add_mul, ← Complex.ofReal_add, heR]
  simp_rw [he]
  rw [integral_const_mul, Measure.integral_comp_mul_left
    (fun t => baseKernel t * Complex.exp (((t*((u-s)/rho) : ℝ) : ℂ) * Complex.I)) rho]
  rw [abs_of_pos (inv_pos.mpr hrho)]
  simp only [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hrho.ne',
    Complex.ofReal_one, one_mul]

end BoundedRecovery

noncomputable section
open Set MeasureTheory
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma filterL1_nonneg : 0 ≤ filterL1 := integral_nonneg (fun _ => norm_nonneg _)

namespace StandardModularData

lemma bandFilter_mem (S : StandardModularData H) (s rho : ℝ) (hrho : 0 < rho)
    {a : H →L[ℂ] H} (ha : a ∈ S.M) : S.bandFilter s rho hrho a ∈ S.M :=
  S.fourierFilter_mem _ _ ha

lemma norm_bandFilter_le (S : StandardModularData H) (s rho : ℝ) (hrho : 0 < rho)
    (a : H →L[ℂ] H) : ‖S.bandFilter s rho hrho a‖ ≤ filterL1 * ‖a‖ := by
  have hh := S.norm_fourierFilter_le (bandKernel s rho) (bandKernel_integrable hrho) a
  rw [integral_norm_bandKernel hrho] at hh
  exact hh

lemma bandFilter_apply_xi (S : StandardModularData H) (s rho : ℝ) (hrho : 0 < rho)
    (a : H →L[ℂ] H) : S.bandFilter s rho hrho a S.xi = S.D.calculus (bandMultiplier s rho) (a S.xi) :=
  S.fourierFilter_apply_xi _ _ _ (bandMultiplier_fourier hrho) a

lemma bandFilter_support (S : StandardModularData H) (s rho : ℝ) (hrho : 0 < rho)
    (a : H →L[ℂ] H) : S.D.HasSpectralSupport (Icc (s-2*rho) (s+2*rho))
      (S.bandFilter s rho hrho a S.xi) := by
  rw [S.bandFilter_apply_xi]
  exact S.D.support_calculus_apply _ _ (fun _u hu => bandMultiplier_zero hrho hu) _

lemma bandMultiplier_fixes (S : StandardModularData H) {s rho : ℝ} (hrho : 0 < rho)
    {h : H} (hh : S.D.HasSpectralSupport (Icc (s-rho) (s+rho)) h) :
    S.D.calculus (bandMultiplier s rho) h = h := hh.fixed (fun _u hu => bandMultiplier_one hrho hu)

lemma bandMultiplier_contracts (S : StandardModularData H) (s rho : ℝ) (h : H) :
    ‖S.D.calculus (bandMultiplier s rho) h‖ ≤ ‖h‖ := by
  calc
    _ ≤ ‖bandMultiplier s rho‖ * ‖h‖ := S.D.norm_calculus_apply_le _ _
    _ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right (norm_bandMultiplier_le s rho) (norm_nonneg _)
    _ = _ := one_mul _

lemma bandFilter_vector_error_le (S : StandardModularData H) {s rho : ℝ} (hrho : 0 < rho)
    (a : H →L[ℂ] H) {h : H} (hh : S.D.HasSpectralSupport (Icc (s-rho) (s+rho)) h) :
    ‖S.bandFilter s rho hrho a S.xi - h‖ ≤ ‖a S.xi - h‖ := by
  rw [S.bandFilter_apply_xi, ← S.bandMultiplier_fixes hrho hh, ← map_sub]
  rw [S.bandMultiplier_fixes hrho hh]
  exact S.bandMultiplier_contracts s rho _

lemma exists_band_representative (S : StandardModularData H) {s rho : ℝ} (hrho : 0 < rho)
    {h : H} (hh : S.D.HasSpectralSupport (Icc (s-rho) (s+rho)) h) (hn : ‖h‖ = 1)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ y : H →L[ℂ] H, y ∈ S.M ∧ ‖y S.xi‖ ≤ 2 ∧ ‖y S.xi - h‖ < eps ∧
      S.D.HasSpectralSupport (Icc (s-2*rho) (s+2*rho)) (y S.xi) := by
  obtain ⟨v,⟨a,ha,rfl⟩,hd⟩ := Metric.mem_closure_iff.mp (S.cyclic h) (min eps 1) (lt_min heps one_pos)
  have hsmall : ‖a S.xi - h‖ < min eps 1 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hd
  have hb := (S.bandFilter_vector_error_le hrho a hh).trans_lt hsmall
  have hbn : ‖S.bandFilter s rho hrho a S.xi‖ ≤ 2 := by
    have hh' := norm_le_norm_sub_add (S.bandFilter s rho hrho a S.xi) h
    rw [hn] at hh'
    have := hb.trans_le (min_le_right _ _)
    linarith
  exact ⟨S.bandFilter s rho hrho a, S.bandFilter_mem s rho hrho ha, hbn,
    hb.trans_le (min_le_left _ _), S.bandFilter_support s rho hrho a⟩

end StandardModularData
end BoundedRecovery

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.Recovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniformly bounded recovery on exact factor-four spectral bands. -/

universe u uι

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma RealSpectralCalculus.HasSpectralSupport.real_smul {D : RealSpectralCalculus H}
    {I : Set ℝ} {h : H} (hh : D.HasSpectralSupport I h) (r : ℝ) :
    D.HasSpectralSupport I (r • h) := by
  rw [← algebraMap_smul ℂ r h]
  exact hh.smul _

lemma RealSpectralCalculus.HasSpectralSupport.sum {D : RealSpectralCalculus H}
    {I : Set ℝ} {ι : Type uι} [Fintype ι] {h : ι → H}
    (hh : ∀ i, D.HasSpectralSupport I (h i)) : D.HasSpectralSupport I (∑ i, h i) := by
  intro f hf
  simp only [map_sum, hh _ f hf, Finset.sum_const_zero]

lemma phaseSum_mem (M : VonNeumannAlgebra H) {n : ℕ} (a : Fin n → H →L[ℂ] H)
    (ha : ∀ i, a i ∈ M) (e : Fin n → Fin 4) : phaseSum a e ∈ M :=
  sum_mem (fun i _ => M.toStarSubalgebra.smul_mem (ha i) _)

lemma phaseSum_vector_support (D : RealSpectralCalculus H) (xi : H) {I : Set ℝ} {n : ℕ}
    (a : Fin n → H →L[ℂ] H) (ha : ∀ i, D.HasSpectralSupport I (a i xi))
    (e : Fin n → Fin 4) : D.HasSpectralSupport I (phaseSum a e xi) := by
  simp only [phaseSum, sum_apply, smul_apply]
  exact RealSpectralCalculus.HasSpectralSupport.sum (fun i => (ha i).smul _)

omit [CompleteSpace H] [InnerProductSpace ℂ H] in
lemma norm_sq_le_twice_sum (x y : H) :
    ‖x‖ ^ 2 ≤ 2 * ‖y‖ ^ 2 + 2 * ‖x-y‖ ^ 2 := by
  have hh := pow_le_pow_left₀ (norm_nonneg x) (norm_le_norm_sub_add x y) 2
  nlinarith [sq_nonneg (‖y‖-‖x-y‖)]

namespace StandardModularData

lemma bounded_recovery_finite_step (S : StandardModularData H) (T : H →L[ℂ] H)
    {s d gamma Q K : ℝ} (hd : 0 < d) (hg : 0 < gamma) (hK : 0 < K)
    (hcut : ‖T‖ ^ 2 * (K ^ 2)⁻¹ * Q ≤ gamma / 4)
    {y : H →L[ℂ] H} (hy : y ∈ S.M)
    (hband : S.D.HasSpectralSupport (Icc (s-d) (s+d)) (y S.xi))
    (n : ℕ) (p t : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hdef : gamma ≤ ∑ i, p i * ‖T (S.sigma (t i) y S.xi)‖ ^ 2)
    (hmom : (S.state ((S.modularAverage p t (star y * y)) ^ 2)).re +
      (∑ i, p i * (S.state (star (S.sigma (t i) y) *
        S.modularAverage p t (y * star y) * S.sigma (t i) y)).re) ≤ Q) :
    ∃ v : H →L[ℂ] H, v ∈ S.M ∧ ‖v‖ ≤ filterL1 * K ∧
      Real.sqrt gamma / 2 ≤ ‖T (v S.xi)‖ ∧
      S.D.HasSpectralSupport (Icc (s-2*d) (s+2*d)) (v S.xi) := by
  let a (i : Fin n) := Real.sqrt (p i) • S.sigma (t i) y
  let z (e : Fin n → Fin 4) := phaseSum a e
  let v (e : Fin n → Fin 4) := S.bandFilter s d hd (polarCutoff (z e) K)
  have hzm (e) : z e ∈ S.M := phaseSum_mem S.M a
    (fun i => S.real_smul_mem (S.sigma_mem (t i) hy) _) e
  have hzb (e) : S.D.HasSpectralSupport (Icc (s-d) (s+d)) (z e S.xi) := by
    apply phaseSum_vector_support
    intro i
    simp only [a, smul_apply, S.sigma_apply_xi]
    exact (hband.unitary (t i)).real_smul _
  have hvnorm (e) : ‖v e‖ ≤ filterL1 * K :=
    (S.norm_bandFilter_le s d hd _).trans
      (mul_le_mul_of_nonneg_left (norm_polarCutoff_le _ hK) filterL1_nonneg)
  have hfourth : phaseMean n (fun e => (S.state ((star (z e) * z e)^2)).re) ≤ Q := by
    have hh := S.phaseMean_fourth_le n p hp (fun i => S.sigma (t i) y)
    rw [S.averageSquare_eq, S.averageReverseSquare_eq] at hh
    exact hh.trans hmom
  have hzd : gamma ≤ phaseMean n (fun e => ‖T (z e S.xi)‖^2) := by
    rw [S.phaseMean_defect T n p hp]
    exact hdef
  have herr (e) : ‖z e S.xi - v e S.xi‖ ^ 2 ≤
      (K ^ 2)⁻¹ * (S.state ((star (z e) * z e)^2)).re := by
    have hf := S.bandFilter_vector_error_le hd (polarCutoff (z e) K) (hzb e)
    have he : ‖z e S.xi - v e S.xi‖ ≤ ‖(z e - polarCutoff (z e) K) S.xi‖ := by
      simpa only [v, sub_apply, norm_sub_rev] using hf
    exact (pow_le_pow_left₀ (norm_nonneg _) he 2).trans (polarCutoff_vector_error_sq S.xi (z e) hK)
  have hdet (e) : ‖T (z e S.xi)‖ ^ 2 ≤ 2 * ‖T (v e S.xi)‖ ^ 2 +
      (2 * ‖T‖ ^ 2 * (K ^ 2)⁻¹) * (S.state ((star (z e) * z e)^2)).re := by
    have hh := norm_sq_le_twice_sum (T (z e S.xi)) (T (v e S.xi))
    have ht : ‖T (z e S.xi) - T (v e S.xi)‖ ^ 2 ≤
        ‖T‖ ^ 2 * ‖z e S.xi - v e S.xi‖ ^ 2 := by
      rw [← map_sub]
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm _) 2
    have hn := mul_le_mul_of_nonneg_left (herr e) (sq_nonneg ‖T‖)
    nlinarith
  have hmean := phaseMean_mono n hdet
  rw [phaseMean_add, phaseMean_mul, phaseMean_mul] at hmean
  have hfourth' := mul_le_mul_of_nonneg_left hfourth
    (show 0 ≤ 2 * ‖T‖^2 * (K^2)⁻¹ by positivity)
  have hvd : gamma / 4 ≤ phaseMean n (fun e => ‖T (v e S.xi)‖ ^ 2) := by
    nlinarith
  obtain ⟨e,he⟩ := exists_phaseMean_le n (fun e => ‖T (v e S.xi)‖ ^ 2)
  refine ⟨v e, S.bandFilter_mem s d hd (polarCutoff_mem S.M (hzm e) K), hvnorm e, ?_,
    S.bandFilter_support s d hd _⟩
  have hs := Real.sq_sqrt hg.le
  have hn := Real.sqrt_nonneg gamma
  have hnorm := norm_nonneg (T (v e S.xi))
  nlinarith

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma recoveryMomentBound_pos (s : ℝ) : 0 < recoveryMomentBound s := by
  unfold recoveryMomentBound
  positivity

omit [CompleteSpace H] in
lemma exists_recovery_cutoff (T : H →L[ℂ] H) {gamma : ℝ} (hg : 0 < gamma) (s : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ‖T‖^2 * (K^2)⁻¹ * recoveryMomentBound s ≤ gamma/4 := by
  let A := 4 * ‖T‖^2 * recoveryMomentBound s / gamma
  let K := A+1
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (by have := (recoveryMomentBound_pos s).le; positivity) hg.le
  have hK : 0 < K := by dsimp [K]; linarith
  have hKsq : A ≤ K^2 := by dsimp [K]; nlinarith [sq_nonneg A]
  have hh : 4 * ‖T‖^2 * recoveryMomentBound s ≤ K^2 * gamma := (div_le_iff₀ hg).mp hKsq
  refine ⟨K,hK,?_⟩
  have he : ‖T‖^2 * (K^2)⁻¹ * recoveryMomentBound s =
      (‖T‖^2 * recoveryMomentBound s) / K^2 := by ring
  rw [he]
  apply (div_le_iff₀ (sq_pos_of_pos hK)).mpr
  nlinarith

namespace StandardModularData

lemma moment_bound_of_narrow_band (S : StandardModularData H) {s rho : ℝ}
    (hwidth : 2*rho ≤ 1) {y : H →L[ℂ] H} (hy : y ∈ S.M) (hn : ‖y S.xi‖ ≤ 2)
    (hband : S.D.HasSpectralSupport (Icc (s-2*rho) (s+2*rho)) (y S.xi)) :
    (‖y S.xi‖^2+1)^2 + ‖y S.xi‖^2 * ‖star y S.xi‖^2 + 1 ≤ recoveryMomentBound s := by
  have hstar := S.norm_star_apply_xi_le hy hband
    (b := s+1) (fun u hu => le_trans hu.2 (by linarith))
  have hexp : (Real.exp ((s+1)/2))^2 = Real.exp (s+1) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsquare : ‖star y S.xi‖^2 ≤ Real.exp (s+1) * ‖y S.xi‖^2 := by
    simpa only [mul_pow, hexp] using pow_le_pow_left₀ (norm_nonneg _) hstar 2
  let q := ‖y S.xi‖^2
  let b := ‖star y S.xi‖^2
  have hq : q ≤ 4 := by
    simpa only [show (2:ℝ)^2 = 4 by norm_num] using pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hq0 : 0 ≤ q := sq_nonneg _
  have hb0 : 0 ≤ b := sq_nonneg _
  have hb : b ≤ 4 * Real.exp (s+1) := by
    calc
      b ≤ Real.exp (s+1) * q := hsquare
      _ ≤ Real.exp (s+1) * 4 := mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  have hprod : q*b ≤ 16 * Real.exp (s+1) := by
    calc
      _ ≤ 4*b := mul_le_mul_of_nonneg_right hq hb0
      _ ≤ 4*(4*Real.exp (s+1)) := mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = _ := by ring
  change (q+1)^2 + q*b + 1 ≤ recoveryMomentBound s
  unfold recoveryMomentBound
  nlinarith

lemma exists_band_representative_with_defect (S : StandardModularData H)
    (omega : Ultrafilter ℕ) (T : H →L[ℂ] H) {s rho gamma : ℝ}
    (hrho : 0 < rho) (hg : 0 < gamma) {h : H} (hn : ‖h‖ = 1)
    (hband : S.D.HasSpectralSupport (Icc (s-rho) (s+rho)) h)
    (hdef : 4*gamma ≤ fixedMean omega (S.D.orbitDefect T h)) :
    ∃ y : H →L[ℂ] H, y ∈ S.M ∧ ‖y S.xi‖ ≤ 2 ∧
      S.D.HasSpectralSupport (Icc (s-2*rho) (s+2*rho)) (y S.xi) ∧
      gamma < fixedMean omega (S.D.orbitDefect T (y S.xi)) := by
  let eps := gamma / (3 * (‖T‖^2+1))
  have heps : 0 < eps := by dsimp [eps]; positivity
  obtain ⟨y,hy,hyn,hyclose,hyband⟩ := S.exists_band_representative hrho hband hn heps
  refine ⟨y,hy,hyn,hyband,?_⟩
  have hdiff := S.D.abs_mean_orbitDefect_sub_le omega T (y S.xi) h
  have hbound : ‖T‖^2 * (‖y S.xi‖+‖h‖) * ‖y S.xi-h‖ < gamma := by
    calc
      _ ≤ 3 * (‖T‖^2+1) * ‖y S.xi-h‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [hn]
        have := sq_nonneg ‖T‖
        nlinarith
      _ < 3 * (‖T‖^2+1) * eps := mul_lt_mul_of_pos_left hyclose (by positivity)
      _ = gamma := by dsimp [eps]; field_simp
  have habs := hdiff.trans_lt hbound
  have hlo := (abs_lt.mp habs).1
  linarith

lemma bounded_recovery_single (S : StandardModularData H) (hscalar : S.ScalarCentralizer)
    (omega : Ultrafilter ℕ) (hω : (omega : Filter ℕ) ≤ atTop) (T : H →L[ℂ] H)
    {s rho gamma K : ℝ} (hrho : 0 < rho) (hwidth : 2*rho ≤ 1)
    (hg : 0 < gamma) (hK : 0 < K)
    (hcut : ‖T‖^2 * (K^2)⁻¹ * recoveryMomentBound s ≤ gamma/4)
    {h : H} (hn : ‖h‖ = 1) (hband : S.D.HasSpectralSupport (Icc (s-rho) (s+rho)) h)
    (hdef : 4*gamma ≤ fixedMean omega (S.D.orbitDefect T h)) :
    ∃ v : H →L[ℂ] H, v ∈ S.M ∧ ‖v‖ ≤ filterL1*K ∧ Real.sqrt gamma/2 ≤ ‖T (v S.xi)‖ ∧
      S.D.HasSpectralSupport (Icc (s-4*rho) (s+4*rho)) (v S.xi) := by
  obtain ⟨y,hy,hyn,hyband,hydef⟩ := S.exists_band_representative_with_defect omega T hrho hg hn hband hdef
  obtain ⟨n,p,t,hp,_hsum,hpd,hpm⟩ := S.exists_finite_defect_moment_average hscalar omega hω T hy hydef
  have hbound := hpm.trans (S.moment_bound_of_narrow_band hwidth hy hyn hyband)
  have he := S.bounded_recovery_finite_step T (mul_pos (by norm_num : (0:ℝ)<2) hrho) hg hK
    hcut hy hyband n p t hp hpd hbound
  simpa only [← mul_assoc, show (2 : ℝ) * 2 = 4 from by norm_num] using he

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem bounded_recovery_oai (S : StandardModularData H) (hscalar : S.ScalarCentralizer)
    (omega : Ultrafilter ℕ) (hfree : (omega : Filter ℕ) ≤ Filter.atTop)
    (T : H →L[ℂ] H) (s : ℝ) (delta : ℕ → ℝ) (hdelta : ∀ n, 0 < delta n)
    (hdelta0 : Tendsto delta atTop (𝓝 0)) (h : ℕ → H) (hunit : ∀ n, ‖h n‖ = 1)
    (hband : ∀ n, S.D.HasSpectralSupport (Icc (s - delta n) (s + delta n)) (h n))
    (hpositive : 0 < Filter.limsup
      (fun n => fixedMean omega (fun t => ‖T (S.D.unitary t (h n))‖ ^ 2)) atTop) :
    RecoveryConclusion S T s delta := by
  let a : ℕ → ℝ := fun n => fixedMean omega (S.D.orbitDefect T (h n))
  let gamma : ℝ := Filter.limsup a atTop / 8
  have hpos : 0 < Filter.limsup a atTop := hpositive
  have hg : 0 < gamma := by dsimp [gamma]; positivity
  have hlt : 4 * gamma < Filter.limsup a atTop := by dsimp [gamma]; linarith
  have hco := Filter.isCoboundedUnder_le_of_le atTop
    (fun n => S.D.mean_orbitDefect_nonneg omega T (h n))
  have hfreq : ∃ᶠ n in atTop, 4 * gamma < a n :=
    Filter.frequently_lt_of_lt_limsup hco hlt
  have hw : ∀ᶠ n in atTop, 2 * delta n ≤ 1 := by
    filter_upwards [hdelta0.eventually_lt_const (by norm_num : (0:ℝ) < 1/2)] with n hn
    linarith
  obtain ⟨nj,hnj,hs⟩ := Filter.extraction_of_frequently_atTop (hfreq.and_eventually hw)
  obtain ⟨K,hK,hcut⟩ := exists_recovery_cutoff T hg s
  have hex : ∀ j, ∃ v : H →L[ℂ] H, v ∈ S.M ∧ ‖v‖ ≤ filterL1*K ∧
      Real.sqrt gamma/2 ≤ ‖T (v S.xi)‖ ∧
      S.D.HasSpectralSupport (Icc (s-4*delta (nj j)) (s+4*delta (nj j))) (v S.xi) := by
    intro j
    exact S.bounded_recovery_single hscalar omega hfree T (hdelta _) (hs j).2 hg hK
      hcut (hunit _) (hband _) (hs j).1.le
  choose v hv using hex
  refine ⟨nj,hnj,v,filterL1*K,Real.sqrt gamma/2,?_,hv⟩
  exact div_pos (Real.sqrt_pos.mpr hg) (by norm_num)

end BoundedRecovery

end
end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.BoundedRecovery.bounded_recovery_oai.{u} := @OAI.BoundedRecovery.bounded_recovery_oai.{u}
