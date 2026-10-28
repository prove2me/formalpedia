-- Prove2me | solution 1 for OAI.StructuralCrouzeixReference.challenge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:39:53.438226+00:00
-- url     : https://prove2.me/submissions/debe5f2f-977b-4767-938e-ad6a2001eb14

import Mathlib
import Definitions.Def_StructuralCrouzeix
import Definitions.Def_OAIW2SC000
import Theorems.Thm_OAI_StructuralCrouzeix_optimal_metric_bundle

section
-- module Solutions.OAIW2_StructCrouzeix.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_PoissonBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
section

lemma continuousOn_unit_poisson {w : ℂ} (hw : ‖w‖ < 1) :
    ContinuousOn (poissonKernel 0 w) (sphere 0 1) := by
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  apply Complex.continuous_re.comp_continuousOn
  simpa using continuousOn_herglotzRieszKernel_sphere
    (c := 0) (R := 1) (by simpa using hw)

lemma unit_poisson_nonneg {w t : ℂ} (hw : ‖w‖ < 1) (ht : t ∈ sphere 0 1) :
    0 ≤ poissonKernel 0 w t := by
  have ht' : ‖t‖ = 1 := by simpa using ht
  simp only [poissonKernel_def, sub_zero, ht']
  apply div_nonneg _ (sq_nonneg _)
  nlinarith [norm_nonneg w]

lemma unit_poisson_normalized {w : ℂ} (hw : ‖w‖ < 1) :
    Real.circleAverage (poissonKernel 0 w) 0 1 = 1 := by
  have h := (differentiable_const (c := (1 : ℂ))).diffContOnCl
    (s := ball (0 : ℂ) 1) |>.circleAverage_poissonKernel_smul (by simpa using hw)
  have hi : CircleIntegrable (poissonKernel 0 w) 0 1 :=
    (continuousOn_unit_poisson hw).circleIntegrable (by norm_num)
  have he := Complex.ofRealCLM.circleAverage_comp_comm hi
  apply Complex.ofReal_injective
  change Complex.ofReal (Real.circleAverage (poissonKernel 0 w) 0 1) = (1 : ℂ)
  change Complex.ofRealCLM (Real.circleAverage (poissonKernel 0 w) 0 1) = (1 : ℂ)
  rw [← he]
  change Real.circleAverage (fun t => poissonKernel 0 w t • (1 : ℂ)) 0 1 = 1 at h
  simpa [Function.comp_def, Complex.real_smul] using h

lemma poissonExtension_error_bound {f : ℂ → ℝ}
    (hf : ContinuousOn f (sphere 0 1)) {p w : ℂ} {δ ε M : ℝ}
    (hδ : 0 < δ) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hw : ‖w‖ < 1) (hwp : dist w p < δ/2)
    (hbound : ∀ t ∈ sphere 0 1, |f t-f p| ≤ M)
    (hsmall : ∀ t ∈ sphere 0 1, dist t p < δ → |f t-f p| ≤ ε) :
    |poissonExtension f w - f p| ≤ ε + (M/(δ/2)^2)*(1-‖w‖^2) := by
  let P := poissonKernel 0 w
  have hPc : ContinuousOn P (sphere 0 1) := continuousOn_unit_poisson hw
  have hfc : ContinuousOn (fun t => f t-f p) (sphere 0 1) := hf.sub continuousOn_const
  have hPmean : Real.circleAverage P 0 1 = 1 := unit_poisson_normalized hw
  have herr : poissonExtension f w-f p =
      Real.circleAverage (fun t => P t*(f t-f p)) 0 1 := by
    simp only [mul_sub]
    rw [Real.circleAverage_fun_sub]
    · simp only [mul_comm _ (f p)]
      have hh : Real.circleAverage (fun t => f p * P t) 0 1 = f p := by
        change Real.circleAverage (fun t => f p • P t) 0 1 = f p
        rw [Real.circleAverage_fun_smul, hPmean]; simp
      rw [hh]
      rfl
    · exact (hPc.mul hf).circleIntegrable (by norm_num)
    · exact (hPc.mul continuousOn_const).circleIntegrable (by norm_num)
  have hpoint : ∀ t ∈ sphere 0 1,
      |P t*(f t-f p)| ≤ ε*P t+(M/(δ/2)^2)*(1-‖w‖^2) := by
    intro t ht
    have hn : 0 ≤ P t := unit_poisson_nonneg hw ht
    rw [abs_mul, abs_of_nonneg hn]
    have hnum : 0 ≤ 1-‖w‖^2 := by nlinarith [norm_nonneg w]
    have htail : 0 ≤ (M/(δ/2)^2)*(1-‖w‖^2) := by positivity
    by_cases htp : dist t p < δ
    · calc P t*|f t-f p| ≤ P t*ε := mul_le_mul_of_nonneg_left (hsmall t ht htp) hn
           _ ≤ ε*P t+(M/(δ/2)^2)*(1-‖w‖^2) := by nlinarith
    · have hdist : δ/2 ≤ ‖t-w‖ := by
        have htr := dist_triangle t w p
        have htw : δ/2 ≤ dist t w := by
          simp only [not_lt] at htp
          linarith
        simpa [dist_eq_norm] using htw
      have hden : (δ/2)^2 ≤ ‖t-w‖^2 := by nlinarith [norm_nonneg (t-w)]
      have hp : P t ≤ (1-‖w‖^2)/(δ/2)^2 := by
        have ht' : ‖t‖ = 1 := by simpa using ht
        dsimp [P]
        simp only [poissonKernel_def, sub_zero, ht', one_pow]
        exact div_le_div_of_nonneg_left hnum (by positivity) hden
      calc
        P t*|f t-f p| ≤ P t*M := mul_le_mul_of_nonneg_left (hbound t ht) hn
        _ ≤ ((1-‖w‖^2)/(δ/2)^2)*M := mul_le_mul_of_nonneg_right hp hM
        _ = (M/(δ/2)^2)*(1-‖w‖^2) := by ring
        _ ≤ ε*P t+(M/(δ/2)^2)*(1-‖w‖^2) := by nlinarith [mul_nonneg hε hn]
  rw [herr]
  calc
    |Real.circleAverage (fun t => P t*(f t-f p)) 0 1| ≤
        Real.circleAverage (fun t => |P t*(f t-f p)|) 0 1 :=
      Real.abs_circleAverage_le_circleAverage_abs
    _ ≤ Real.circleAverage (fun t => ε*P t+(M/(δ/2)^2)*(1-‖w‖^2)) 0 1 := by
      apply Real.circleAverage_mono
      · exact ((hPc.mul hfc).abs).circleIntegrable (by norm_num)
      · exact ((continuousOn_const.mul hPc).add continuousOn_const).circleIntegrable (by norm_num)
      · simpa using hpoint
    _ = ε+(M/(δ/2)^2)*(1-‖w‖^2) := by
      rw [Real.circleAverage_fun_add]
      · change Real.circleAverage (fun t => ε • P t) 0 1 + _ = _
        rw [Real.circleAverage_fun_smul, hPmean, Real.circleAverage_const]
        simp
      · exact (continuousOn_const.mul hPc).circleIntegrable (by norm_num)
      · exact continuousOn_const.circleIntegrable (by norm_num)

theorem poissonExtension_tendsto_boundary {f : ℂ → ℝ}
    (hf : ContinuousOn f (sphere 0 1)) {p : ℂ} (hp : p ∈ sphere 0 1) :
    Tendsto (poissonExtension f) (𝓝[ball 0 1] p) (𝓝 (f p)) := by
  obtain ⟨M,hM⟩ := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn
    (hf.sub (continuousOn_const (c := f p)))
  have hM0 : 0 ≤ M := by simpa using hM p hp
  have hpn : ‖p‖ = 1 := by simpa using hp
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ,hδ,hsmall⟩ := Metric.continuousWithinAt_iff.mp (hf p hp) (ε/2) (by positivity)
  let K := M/(δ/2)^2
  have hc : ContinuousAt (fun w : ℂ => K*(1-‖w‖^2)) p := by fun_prop
  obtain ⟨η,hη,hηdef⟩ := Metric.continuousAt_iff.mp hc (ε/2) (by positivity)
  refine ⟨min (δ/2) η, lt_min (by positivity) hη, ?_⟩
  intro w hw hwp
  have hwpδ : dist w p < δ/2 := lt_of_lt_of_le hwp (min_le_left _ _)
  have hwpη : dist w p < η := lt_of_lt_of_le hwp (min_le_right _ _)
  have htail : K*(1-‖w‖^2) < ε/2 := by
    have hh := hηdef hwpη
    simp only [hpn, one_pow, sub_self, mul_zero, dist_zero_right] at hh
    exact (le_abs_self _).trans_lt hh
  have hh := poissonExtension_error_bound hf (ε := ε/2) (M := M) hδ (by positivity) hM0
    (by simpa using hw) hwpδ
    (fun t ht => by simpa [Real.norm_eq_abs] using hM t ht)
    (fun t ht htp => by simpa [Real.dist_eq] using (hsmall ht htp).le)
  rw [Real.dist_eq]
  apply hh.trans_lt
  dsimp [K] at htail
  linarith

theorem harmonicOnNhd_poissonExtension {f : ℂ → ℝ}
    (hf : ContinuousOn f (sphere 0 1)) :
    InnerProductSpace.HarmonicOnNhd (poissonExtension f) (ball 0 1) := by
  let H : ℂ → ℂ := fun w => Real.circleAverage
    (fun t => herglotzRieszKernel 0 w t • (f t : ℂ)) 0 1
  have ha : AnalyticOnNhd ℂ H (ball 0 1) :=
    (analyticOnNhd_circleAverage_herglotzRieszKernel_smul
      ((Complex.continuous_ofReal.comp_continuousOn hf).circleIntegrable (by norm_num))).mono
      (fun z hz => by simpa using hz)
  intro w hw
  apply (InnerProductSpace.harmonicAt_congr_nhds (f₁ := fun z => (H z).re) ?_).mp
    ((ha w hw).harmonicAt_re)
  filter_upwards [isOpen_ball.mem_nhds hw] with z hz
  have hh := re_circleAverage_herglotzRieszKernel_smul
    (hf.circleIntegrable (by norm_num))
    (by simpa using hz)
  simpa [H, poissonExtension, poissonKernel_eq_re_herglotzRieszKernel, Pi.smul_apply,
    smul_eq_mul, Pi.mul_def, Function.comp_def] using hh

lemma diskDirichlet_eq_boundary {f : ℂ → ℝ} {p : ℂ} (hp : p ∈ sphere 0 1) :
    diskDirichlet f p = f p := by
  have h : ‖p‖ = 1 := by simpa using hp
  simp [diskDirichlet,h]

theorem harmonicOnNhd_diskDirichlet {f : ℂ → ℝ}
    (hf : ContinuousOn f (sphere 0 1)) :
    InnerProductSpace.HarmonicOnNhd (diskDirichlet f) (ball 0 1) := by
  intro w hw
  apply (InnerProductSpace.harmonicAt_congr_nhds (f₁ := poissonExtension f) ?_).mp
    (harmonicOnNhd_poissonExtension hf w hw)
  filter_upwards [isOpen_ball.mem_nhds hw] with z hz
  simp only [diskDirichlet, ite_eq_left (show ‖z‖ < 1 by simpa using hz)]

theorem continuousOn_diskDirichlet {f : ℂ → ℝ}
    (hf : ContinuousOn f (sphere 0 1)) :
    ContinuousOn (diskDirichlet f) (closedBall 0 1) := by
  intro p hp
  by_cases hpi : ‖p‖ < 1
  · have h := (harmonicOnNhd_diskDirichlet hf p (by simpa using hpi)).1.continuousAt
    exact h.continuousWithinAt
  · have hpn : ‖p‖ = 1 := by
      have h : ‖p‖ ≤ 1 := by simpa using hp
      exact le_antisymm h (not_lt.mp hpi)
    have hps : p ∈ sphere 0 1 := by simpa using hpn
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ,hδ,hδdef⟩ := Metric.tendsto_nhdsWithin_nhds.mp
      (poissonExtension_tendsto_boundary hf hps) ε hε
    obtain ⟨η,hη,hηdef⟩ := Metric.continuousWithinAt_iff.mp (hf p hps) ε hε
    refine ⟨min δ η, lt_min hδ hη, ?_⟩
    intro w hw hwp
    rw [diskDirichlet_eq_boundary hps]
    by_cases hwi : ‖w‖ < 1
    · rw [diskDirichlet, ite_eq_left hwi]
      exact hδdef (by simpa using hwi) (lt_of_lt_of_le hwp (min_le_left _ _))
    · rw [diskDirichlet, ite_eq_right hwi]
      apply hηdef _ (lt_of_lt_of_le hwp (min_le_right _ _))
      have hwn : ‖w‖ ≤ 1 := by simpa using hw
      simpa using le_antisymm hwn (not_lt.mp hwi)

end

open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
section

lemma harmonic_eventually_eq_of_isLocalMax {u : ℂ → ℝ} {p : ℂ}
    (hu : HarmonicAt u p) (hm : IsLocalMax u p) :
    ∀ᶠ z in 𝓝 p, u z = u p := by
  obtain ⟨r,hr,hrs⟩ := Metric.eventually_nhds_iff.mp hu.eventually
  have hur : HarmonicOnNhd u (ball p r) := fun z hz => hrs (by simpa [dist_comm] using hz)
  obtain ⟨H,hHa,hHu⟩ := hur.exists_analyticOnNhd_ball_re_eq
  have hp : p ∈ ball p r := mem_ball_self hr
  have hdiff : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (fun z => Complex.exp (H z)) z := by
    filter_upwards [isOpen_ball.mem_nhds hp] with z hz
    exact Complex.differentiable_exp.differentiableAt.comp z (hHa z hz).differentiableAt
  have hmax : IsLocalMax (norm ∘ fun z => Complex.exp (H z)) p := by
    filter_upwards [hm, isOpen_ball.mem_nhds hp] with z hz hzr
    simp only [Function.comp_def, Complex.norm_exp, hHu hzr, hHu hp]
    exact Real.exp_le_exp.mpr hz
  filter_upwards [Complex.norm_eventually_eq_of_isLocalMax hdiff hmax,
    isOpen_ball.mem_nhds hp] with z hz hzr
  simp only [Complex.norm_exp] at hz
  exact (hHu hzr).symm.trans ((Real.exp_injective hz).trans (hHu hp))

lemma harmonic_eqOn_of_isPreconnected_of_isMaxOn {u : ℂ → ℝ} {U : Set ℂ} {p : ℂ}
    (hUc : IsPreconnected U) (hUo : IsOpen U) (hu : HarmonicOnNhd u U)
    (hp : p ∈ U) (hm : IsMaxOn u U p) : EqOn u (fun _ => u p) U := by
  let V := U ∩ {z | IsMaxOn u U z}
  have hV : ∀ z ∈ V, u z = u p := fun z hz => le_antisymm (hm hz.1) (hz.2 hp)
  have hVo : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have hh := harmonic_eventually_eq_of_isLocalMax (hu z hz.1)
      (hz.2.isLocalMax (hUo.mem_nhds hz.1))
    filter_upwards [hUo.mem_nhds hz.1, hh] with w hw huw
    exact ⟨hw, fun t ht => (hz.2 ht).trans_eq huw.symm⟩
  let W := U ∩ {z | u z ≠ u p}
  have hWo : IsOpen W := hu.continuousOn.isOpen_inter_preimage hUo isOpen_ne
  have hdis : Disjoint V W := disjoint_left.mpr fun z hv hw => hw.2 (hV z hv)
  have hcover : U ⊆ V ∪ W := by
    intro z hz
    by_cases he : u z = u p
    · exact Or.inl ⟨hz, fun t ht => (hm ht).trans_eq he.symm⟩
    · exact Or.inr ⟨hz,he⟩
  have hsub : U ⊆ V := hUc.subset_left_of_subset_union hVo hWo hdis hcover ⟨p,hp,hp,hm⟩
  exact fun z hz => hV z (hsub hz)

theorem harmonic_exists_mem_frontier_isMaxOn {u : ℂ → ℝ} {U : Set ℂ}
    (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    (hu : HarmonicOnNhd u U) (huc : ContinuousOn u (closure U)) :
    ∃ p ∈ frontier U, IsMaxOn u (closure U) p := by
  have hc : IsCompact (closure U) := hUb.isCompact_closure
  obtain ⟨w,hw,hm⟩ := hc.exists_isMaxOn hUne.closure huc
  rw [closure_eq_interior_union_frontier, mem_union] at hw
  rcases hw with hw | hw
  · have hne : interior U ≠ univ := ne_top_of_le_ne_top hc.ne_univ interior_subset_closure
    obtain ⟨z,hz,hzw⟩ := exists_mem_frontier_infDist_compl_eq_dist hw hne
    have hd : 0 < dist w z := by
      apply dist_pos.mpr
      intro he
      subst z
      exact Set.disjoint_left.mp (disjoint_interior_frontier (s := U)) hw (frontier_interior_subset hz)
    have hball : ball w (dist w z) ⊆ U := by
      rw [← hzw]
      exact ball_infDist_compl_subset.trans interior_subset
    have hconst := harmonic_eqOn_of_isPreconnected_of_isMaxOn
      (convex_ball w (dist w z)).isPreconnected isOpen_ball (hu.mono hball)
      (mem_ball_self hd) (hm.on_subset (hball.trans subset_closure))
    have hcl : EqOn u (fun _ => u w) (closure (ball w (dist w z))) :=
      hconst.of_subset_closure (huc.mono (closure_mono hball)) continuousOn_const subset_closure Subset.rfl
    have hze : u z = u w := hcl (by rw [closure_ball _ hd.ne']; simp [dist_comm])
    exact ⟨z,frontier_interior_subset hz, fun t ht => (hm ht).trans_eq hze.symm⟩
  · exact ⟨w,hw,hm⟩

theorem harmonic_le_of_frontier_le {u : ℂ → ℝ} {U : Set ℂ} {C : ℝ}
    (hUb : Bornology.IsBounded U) (hu : HarmonicOnNhd u U)
    (huc : ContinuousOn u (closure U)) (hbd : ∀ z ∈ frontier U, u z ≤ C)
    {z : ℂ} (hz : z ∈ closure U) : u z ≤ C := by
  have hUne : U.Nonempty := by
    by_contra hn
    have he : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [he] at hz
  obtain ⟨p,hp,hm⟩ := harmonic_exists_mem_frontier_isMaxOn hUb hUne hu huc
  exact (hm hz).trans (hbd p hp)

theorem harmonic_eqOn_closure_of_eqOn_frontier {u v : ℂ → ℝ} {U : Set ℂ}
    (hUb : Bornology.IsBounded U) (hu : HarmonicOnNhd u U) (hv : HarmonicOnNhd v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hbd : EqOn u v (frontier U)) : EqOn u v (closure U) := by
  intro z hz
  apply le_antisymm
  · have hh := harmonic_le_of_frontier_le hUb (hu.sub hv) (huc.sub hvc)
      (C := 0) (fun t ht => by simp [hbd ht]) hz
    exact sub_nonpos.mp hh
  · have hh := harmonic_le_of_frontier_le hUb (hv.sub hu) (hvc.sub huc)
      (C := 0) (fun t ht => by simp [hbd ht]) hz
    exact sub_nonpos.mp hh

end

open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate

lemma circleAverage_conj {g : ℂ → ℝ} :
    Real.circleAverage (fun z => g (conj z)) 0 1 = Real.circleAverage g 0 1 := by
  rw [← Real.circleAverage_zero_one_congr_inv (f := g)]
  apply Real.circleAverage_congr_sphere
  intro z hz
  have hn : ‖z‖ = 1 := by simpa using hz
  simp only [Complex.inv_eq_conj hn]

lemma unit_poisson_conj (w t : ℂ) :
    poissonKernel 0 (conj w) (conj t) = poissonKernel 0 w t := by
  simp only [poissonKernel_def, sub_zero, ← map_sub, Complex.norm_conj]

lemma poissonExtension_odd {f : ℂ → ℝ}
    (hodd : ∀ z ∈ sphere (0 : ℂ) 1, f (conj z) = -f z) (w : ℂ) :
    poissonExtension f (conj w) = -poissonExtension f w := by
  unfold poissonExtension
  rw [← circleAverage_conj (g := fun t => poissonKernel 0 (conj w) t * f t)]
  calc
    _ = Real.circleAverage (fun t => -(poissonKernel 0 w t * f t)) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro t ht
      change poissonKernel 0 (conj w) (conj t) * f (conj t) = -(poissonKernel 0 w t * f t)
      rw [unit_poisson_conj, hodd t (by simpa using ht)]
      ring
    _ = _ := by simp [Real.circleAverage, intervalIntegral.integral_neg]

lemma diskDirichlet_zero_real {f : ℂ → ℝ}
    (hodd : ∀ z ∈ sphere (0 : ℂ) 1, f (conj z) = -f z)
    {z : ℂ} (hz : ‖z‖ < 1) (hzi : z.im = 0) : diskDirichlet f z = 0 := by
  have hc : conj z = z := Complex.conj_eq_iff_im.mpr hzi
  have hh := poissonExtension_odd hodd z
  rw [hc] at hh
  simp only [diskDirichlet, ite_eq_left hz]
  linarith

lemma upperDisk_isOpen : IsOpen upperDisk :=
  isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)

lemma closure_upperDisk_subset : closure upperDisk ⊆ upperClosedDisk := by
  apply closure_minimal
  · intro z hz
    exact ⟨ball_subset_closedBall hz.1, le_of_lt (show 0 < z.im from hz.2)⟩
  · exact isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_im)

lemma upper_frontier_or {z : ℂ} (hz : z ∈ frontier upperDisk) : ‖z‖ = 1 ∨ z.im = 0 := by
  have hc := closure_upperDisk_subset hz.1
  have hn : ‖z‖ ≤ 1 := by simpa using hc.1
  by_cases he : ‖z‖ = 1
  · exact Or.inl he
  · right
    by_contra hi
    have hi' : 0 < z.im := lt_of_le_of_ne hc.2 (Ne.symm hi)
    apply hz.2
    rw [upperDisk_isOpen.interior_eq]
    exact ⟨by simpa using lt_of_le_of_ne hn he, hi'⟩

lemma oddBoundary_odd {u : ℂ → ℝ}
    (hzero : ∀ z ∈ upperClosedDisk, z.im = 0 → u z = 0)
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) : oddBoundary u (conj z) = -oddBoundary u z := by
  have hn : ‖z‖ = 1 := by simpa using hz
  by_cases hzi : z.im = 0
  · have hc : conj z = z := Complex.conj_eq_iff_im.mpr hzi
    have hu := hzero z ⟨by simp [hn], by simp [hzi]⟩ hzi
    simp [oddBoundary,hc,hzi,hu]
  · by_cases hpos : 0 ≤ z.im
    · have hpos' : 0 < z.im := lt_of_le_of_ne hpos (Ne.symm hzi)
      have hh : ¬0 ≤ (conj z).im := by simp only [Complex.conj_im]; linarith
      simp only [oddBoundary, ite_eq_left hpos, ite_eq_right hh, Complex.conj_conj]
    · have hh : 0 ≤ (conj z).im := by simp only [Complex.conj_im]; linarith
      simp only [oddBoundary, ite_eq_right hpos, ite_eq_left hh, neg_neg]

lemma continuousOn_oddBoundary {u : ℂ → ℝ}
    (hu : ContinuousOn u upperClosedDisk)
    (hzero : ∀ z ∈ upperClosedDisk, z.im = 0 → u z = 0) :
    ContinuousOn (oddBoundary u) (sphere 0 1) := by
  have hup : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
  have hdown : closure {z : ℂ | ¬0 ≤ z.im} ⊆ {z | z.im ≤ 0} := by
    apply closure_minimal
    · intro z hz
      exact (lt_of_not_ge hz).le
    · exact isClosed_le Complex.continuous_im continuous_const
  have hfront : ∀ z ∈ frontier {z : ℂ | 0 ≤ z.im}, z.im = 0 := by
    intro z hz
    have hp : 0 ≤ z.im := by simpa [hup.closure_eq] using hz.1
    have hm : z.im ≤ 0 := by
      have hh : z ∈ closure {z : ℂ | ¬0 ≤ z.im} := by
        change z ∈ closure ({z : ℂ | 0 ≤ z.im}ᶜ)
        rw [closure_compl]
        exact hz.2
      exact hdown hh
    exact le_antisymm hm hp
  apply ContinuousOn.if
  · intro z hz
    have hzi := hfront z hz.2
    have hn : ‖z‖ = 1 := by simpa using hz.1
    have hc : conj z = z := Complex.conj_eq_iff_im.mpr hzi
    rw [hc, hzero z ⟨by simp [hn], by simp [hzi]⟩ hzi, neg_zero]
  · apply hu.mono
    intro z hz
    exact ⟨sphere_subset_closedBall hz.1, by simpa [hup.closure_eq] using hz.2⟩
  · apply ContinuousOn.neg
    apply hu.comp Complex.continuous_conj.continuousOn
    intro z hz
    exact ⟨by simpa using (sphere_subset_closedBall hz.1), by
      simp only [mem_ofPred_eq, Complex.conj_im, neg_nonneg]; exact hdown hz.2⟩


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_HerglotzReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate

open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
section

lemma circleAverage_pos_at_I {g : ℂ → ℝ} (hg : ContinuousOn g (sphere 0 1))
    (hpos : ∀ z ∈ sphere (0 : ℂ) 1, 0 ≤ g z) (hI : 0 < g I) :
    0 < Real.circleAverage g 0 1 := by
  unfold Real.circleAverage
  apply smul_pos (by positivity)
  apply intervalIntegral.integral_pos Real.two_pi_pos
  · apply hg.comp (continuous_circleMap 0 1).continuousOn
    intro θ _
    simp
  · intro θ _
    apply hpos
    simp
  · refine ⟨Real.pi / 2, ⟨by positivity, by linarith [Real.pi_pos]⟩, ?_⟩
    simpa [circleMap_pi_div_two] using hI

lemma analyticOnNhd_herglotzExtension {f : ℂ → ℝ} (hf : ContinuousOn f (sphere 0 1)) :
    AnalyticOnNhd ℂ (herglotzExtension f) (ball 0 1) :=
  (analyticOnNhd_circleAverage_herglotzRieszKernel_smul
    ((Complex.continuous_ofReal.comp_continuousOn hf).circleIntegrable (by norm_num))).mono
    (fun z hz => by simpa using hz)

lemma re_herglotzExtension {f : ℂ → ℝ} (hf : ContinuousOn f (sphere 0 1))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    (herglotzExtension f w).re = poissonExtension f w := by
  have hh := re_circleAverage_herglotzRieszKernel_smul
    (hf.circleIntegrable (by norm_num))
    (by simpa using hw)
  simpa [herglotzExtension, poissonExtension, poissonKernel_eq_re_herglotzRieszKernel,
    Pi.smul_apply, smul_eq_mul, Pi.mul_def, Function.comp_def] using hh

lemma hasDerivAt_herglotzExtension_zero {f : ℂ → ℝ}
    (hf : ContinuousOn f (sphere 0 1)) :
    HasDerivAt (herglotzExtension f)
      (Real.circleAverage (fun t => (2 * conj t) * (f t : ℂ)) 0 1) 0 := by
  have hh := hasDerivAt_circleAverage_herglotzRieszKernel_smul
    ((Complex.continuous_ofReal.comp_continuousOn hf).circleIntegrable (by norm_num))
    (show (0 : ℂ) ∈ Metric.ball 0 (1 : ℝ) by simp)
  apply hh.congr_deriv
  symm
  apply Real.circleAverage_congr_sphere
  intro t ht
  have hn : ‖t‖ = 1 := by simpa using ht
  have ht0 : t ≠ 0 := by intro h; simp [h] at hn
  change (2 * conj t) * (f t : ℂ) = (2 * t / (t - 0) ^ 2) • (f t : ℂ)
  rw [← Complex.inv_eq_conj hn]
  simp only [sub_zero, smul_eq_mul]
  congr 1
  field_simp

lemma im_deriv_herglotzExtension_zero {f : ℂ → ℝ}
    (hf : ContinuousOn f (sphere 0 1)) :
    (deriv (herglotzExtension f) 0).im =
      Real.circleAverage (fun t => -2 * t.im * f t) 0 1 := by
  rw [(hasDerivAt_herglotzExtension_zero hf).deriv]
  have hi : CircleIntegrable (fun t => (2 * conj t) * (f t : ℂ)) 0 1 := by
    exact ((continuous_const.mul Complex.continuous_conj).continuousOn.mul
      (Complex.continuous_ofReal.comp_continuousOn hf)).circleIntegrable (by norm_num)
  have he := Complex.imCLM.circleAverage_comp_comm hi
  change Complex.imCLM (Real.circleAverage (fun t => (2 * conj t) * (f t : ℂ)) 0 1) = _
  rw [← he]
  apply Real.circleAverage_congr_sphere
  intro t _
  simp [Complex.mul_im, mul_assoc]

theorem herglotz_oddBoundary_deriv_ne_zero {u : ℂ → ℝ}
    (huc : ContinuousOn u upperClosedDisk)
    (hzero : ∀ z ∈ upperClosedDisk, z.im = 0 → u z = 0)
    (hneg : ∀ z ∈ sphere (0 : ℂ) 1, 0 < z.im → u z < 0) :
    deriv (herglotzExtension (oddBoundary u)) 0 ≠ 0 := by
  have hf := continuousOn_oddBoundary huc hzero
  have hn : ∀ t ∈ sphere (0 : ℂ) 1, 0 ≤ -2 * t.im * oddBoundary u t := by
    intro t ht
    by_cases hp : 0 ≤ t.im
    · rw [oddBoundary, ite_eq_left hp]
      by_cases he : t.im = 0
      · simp [he]
      · have hh := hneg t ht (lt_of_le_of_ne hp (Ne.symm he))
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) hh.le
    · rw [oddBoundary, ite_eq_right hp]
      have hh := hneg (conj t) (by simpa using ht) (by simp; linarith)
      exact mul_nonneg (by linarith) (by linarith)
  have hp : 0 < Real.circleAverage (fun t => -2 * t.im * oddBoundary u t) 0 1 := by
    apply circleAverage_pos_at_I
      ((continuous_const.mul Complex.continuous_im).continuousOn.mul hf) hn
    have hi : u I < 0 := hneg I (by simp) (by simp)
    change 0 < -2 * I.im * oddBoundary u I
    simp only [oddBoundary, Complex.I_im, show (0 : ℝ) ≤ 1 by norm_num, ite_true]
    linarith
  rw [← im_deriv_herglotzExtension_zero hf] at hp
  intro he
  simp [he] at hp

theorem holomorphic_reflection_modulus {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u upperDisk) (huc : ContinuousOn u upperClosedDisk)
    (hzero : ∀ z ∈ upperClosedDisk, z.im = 0 → u z = 0)
    (hneg : ∀ z ∈ sphere (0 : ℂ) 1, 0 < z.im → u z < 0) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (ball 0 1) ∧
      (∀ z, F z ≠ 0) ∧ deriv F 0 ≠ 0 ∧
      (∀ z ∈ upperDisk, ‖F z‖ = Real.exp (u z)) := by
  let f := oddBoundary u
  let H := herglotzExtension f
  have hf : ContinuousOn f (sphere 0 1) := continuousOn_oddBoundary huc hzero
  have hH : AnalyticOnNhd ℂ H (ball 0 1) := analyticOnNhd_herglotzExtension hf
  have hEq : EqOn (diskDirichlet f) u (closure upperDisk) := by
    apply harmonic_eqOn_closure_of_eqOn_frontier
      (isBounded_ball.subset inter_subset_left)
      ((harmonicOnNhd_diskDirichlet hf).mono inter_subset_left) hu
      ((continuousOn_diskDirichlet hf).mono (closure_upperDisk_subset.trans inter_subset_left))
      (huc.mono closure_upperDisk_subset)
    intro z hz
    have hc := closure_upperDisk_subset hz.1
    rcases upper_frontier_or hz with hn | hi
    · rw [diskDirichlet_eq_boundary (by simpa using hn)]
      exact ite_eq_left hc.2
    · have hn : ‖z‖ ≤ 1 := by simpa using hc.1
      by_cases he : ‖z‖ = 1
      · rw [diskDirichlet_eq_boundary (by simpa using he)]
        exact ite_eq_left hc.2
      · rw [diskDirichlet_zero_real (fun _ hz => oddBoundary_odd hzero hz)
          (lt_of_le_of_ne hn he) hi, hzero z hc hi]
  refine ⟨fun z => Complex.exp (H z), ?_, fun z => Complex.exp_ne_zero _, ?_, ?_⟩
  · intro z hz
    exact analyticAt_cexp.comp (hH z hz)
  · have hh := (Complex.hasDerivAt_exp (H 0)).comp 0
      ((hH 0 (by simp)).differentiableAt.hasDerivAt)
    change deriv (Complex.exp ∘ H) 0 ≠ 0
    rw [hh.deriv]
    exact mul_ne_zero (Complex.exp_ne_zero _) (herglotz_oddBoundary_deriv_ne_zero huc hzero hneg)
  · intro z hz
    rw [Complex.norm_exp, re_herglotzExtension hf hz.1]
    have hh := hEq (subset_closure hz)
    simpa [diskDirichlet, show ‖z‖ < 1 by simpa using hz.1] using congrArg Real.exp hh

theorem holomorphic_reflection_upperDisk {g : ℂ → ℂ} {u : ℂ → ℝ}
    (hg : AnalyticOnNhd ℂ g upperDisk)
    (hu : HarmonicOnNhd u upperDisk) (huc : ContinuousOn u upperClosedDisk)
    (hzero : ∀ z ∈ upperClosedDisk, z.im = 0 → u z = 0)
    (hneg : ∀ z ∈ sphere (0 : ℂ) 1, 0 < z.im → u z < 0)
    (hmod : ∀ z ∈ upperDisk, ‖g z‖ = Real.exp (u z)) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (ball 0 1) ∧
      (∀ z, G z ≠ 0) ∧ deriv G 0 ≠ 0 ∧ EqOn G g upperDisk := by
  obtain ⟨F,hFa,hFn,hFd,hFm⟩ := holomorphic_reflection_modulus hu huc hzero hneg
  let q : ℂ → ℂ := fun z => g z / F z
  have hqa : AnalyticOnNhd ℂ q upperDisk := fun z hz => (hg z hz).div (hFa z hz.1) (hFn z)
  have hqn : ∀ z ∈ upperDisk, ‖q z‖ = 1 := by
    intro z hz
    simp only [q, norm_div, hmod z hz, hFm z hz, div_self (Real.exp_ne_zero _)]
  let p : ℂ := (1/2 : ℝ) • I
  have hp : p ∈ upperDisk := by
    constructor
    · norm_num [p, mem_ball, dist_zero_right, norm_smul]
    · simp [p]
  have hc : IsPreconnected upperDisk := by
    exact ((convex_ball (0 : ℂ) 1).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hc upperDisk_isOpen
    hqa.differentiableOn hp (show IsMaxOn (norm ∘ q) upperDisk p from
      fun z hz => by simp [hqn z hz, hqn p hp])
  have hqp : q p ≠ 0 := norm_ne_zero_iff.mp (by rw [hqn p hp]; norm_num)
  refine ⟨fun z => q p * F z, ?_, fun z => mul_ne_zero hqp (hFn z), ?_, ?_⟩
  · intro z hz
    exact analyticAt_const.mul (hFa z hz)
  · have hd := ((hFa 0 (by simp)).differentiableAt.hasDerivAt).const_mul (q p)
    rw [hd.deriv]
    exact mul_ne_zero hqp hFd
  · intro z hz
    have he : q z = q p := hconst hz
    rw [← he]
    exact div_mul_cancel₀ _ (hFn z)


open Set Filter Metric Complex
open scoped Topology

lemma upperLogNorm_eventuallyEq (g : ℂ → ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    upperLogNorm g =ᶠ[𝓝 z] (fun w => Real.log ‖g w‖) := by
  filter_upwards [Complex.continuous_im.continuousAt.eventually_ne hz] with w hw
  exact ite_eq_right hw

lemma upperLogNorm_continuousOn {g : ℂ → ℂ}
    (hg : ∀ z ∈ upperClosedDisk, 0 < z.im → AnalyticAt ℂ g z)
    (hn : ∀ z ∈ upperClosedDisk, 0 < z.im → g z ≠ 0)
    (hb : ∀ p ∈ upperClosedDisk, p.im = 0 →
      Tendsto (fun z => ‖g z‖) (𝓝[{z : ℂ | 0 < z.im}] p) (𝓝 1)) :
    ContinuousOn (upperLogNorm g) upperClosedDisk := by
  intro p hp
  by_cases hz : p.im = 0
  · have hpos : ContinuousWithinAt (upperLogNorm g) {z : ℂ | 0 < z.im} p := by
      change Tendsto (upperLogNorm g) _ (𝓝 (upperLogNorm g p))
      rw [upperLogNorm, ite_eq_left hz]
      have ht := (hb p hp hz).log (by norm_num : (1 : ℝ) ≠ 0)
      rw [Real.log_one] at ht
      apply ht.congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (ite_eq_right (ne_of_gt hz)).symm
    have hreal : ContinuousWithinAt (upperLogNorm g) {z : ℂ | z.im = 0} p := by
      apply (continuousWithinAt_const (b := (0 : ℝ))).congr
      · intro z hz
        exact ite_eq_left hz
      · exact ite_eq_left hz
    apply (hreal.union hpos).mono
    intro z hz
    by_cases he : z.im = 0
    · exact Or.inl he
    · exact Or.inr (lt_of_le_of_ne hz.2 (Ne.symm he))
  · have hp' : 0 < p.im := lt_of_le_of_ne hp.2 (Ne.symm hz)
    have hc := ((hg p hp hp').continuousAt.norm.log (norm_ne_zero_iff.mpr (hn p hp hp')))
    exact (hc.congr (upperLogNorm_eventuallyEq g hz).symm).continuousWithinAt

theorem conformal_reflection_upperDisk {g : ℂ → ℂ}
    (hg : ∀ z ∈ upperClosedDisk, 0 < z.im → AnalyticAt ℂ g z)
    (hn : ∀ z ∈ upperClosedDisk, 0 < z.im → g z ≠ 0)
    (hsmall : ∀ z ∈ upperClosedDisk, 0 < z.im → ‖g z‖ < 1)
    (hb : ∀ p ∈ upperClosedDisk, p.im = 0 →
      Tendsto (fun z => ‖g z‖) (𝓝[{z : ℂ | 0 < z.im}] p) (𝓝 1)) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (ball 0 1) ∧
      (∀ z, G z ≠ 0) ∧ deriv G 0 ≠ 0 ∧ EqOn G g upperDisk := by
  have hsub : upperDisk ⊆ upperClosedDisk := by
    intro z hz
    exact ⟨ball_subset_closedBall hz.1, show (0 : ℝ) ≤ z.im from hz.2.le⟩
  apply holomorphic_reflection_upperDisk (u := upperLogNorm g)
  · exact fun z hz => hg z (hsub hz) hz.2
  · intro z hz
    rw [harmonicAt_congr_nhds (upperLogNorm_eventuallyEq g (ne_of_gt hz.2))]
    exact (hg z (hsub hz) hz.2).harmonicAt_log_norm (hn z (hsub hz) hz.2)
  · exact upperLogNorm_continuousOn hg hn hb
  · intro z _ hz
    exact ite_eq_left hz
  · intro z hz him
    rw [upperLogNorm, ite_eq_right (ne_of_gt him)]
    have hc : z ∈ upperClosedDisk := ⟨sphere_subset_closedBall hz,him.le⟩
    exact Real.log_neg (norm_pos_iff.mpr (hn z hc him)) (hsmall z hc him)
  · intro z hz
    rw [upperLogNorm, ite_eq_right (ne_of_gt hz.2),
      Real.exp_log (norm_pos_iff.mpr (hn z (hsub hz) hz.2))]

end

open Set Filter Metric
open scoped Topology

theorem compact_local_injective_collar {K : Set ℂ} (hK : IsCompact K)
    {f : ℂ → ℂ} (hcont : ∀ z ∈ K, ContinuousAt f z) (hinj : InjOn f K)
    (hloc : ∀ z ∈ K, ∃ U ∈ 𝓝 z, InjOn f U) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ InjOn f U := by
  let R : Set (ℂ × ℂ) := {p | f p.1 = f p.2 → p.1 = p.2}
  have hR : R ∈ 𝓝ˢ (K ×ˢ K) := by
    rw [mem_nhdsSet_iff_forall]
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    by_cases hxy : x = y
    · subst y
      obtain ⟨U,hU,hUi⟩ := hloc x hx
      apply mem_of_superset (show U ×ˢ U ∈ 𝓝 (x,x) by
        rw [nhds_prod_eq]; exact prod_mem_prod hU hU)
      rintro ⟨a,b⟩ ⟨ha,hb⟩
      exact hUi ha hb
    · have hne : f x - f y ≠ 0 := sub_ne_zero.mpr (fun he => hxy (hinj hx hy he))
      have hc : ContinuousAt (fun p : ℂ × ℂ => f p.1 - f p.2) (x,y) :=
        ((hcont x hx).comp continuousAt_fst).sub ((hcont y hy).comp continuousAt_snd)
      filter_upwards [hc.eventually_ne hne] with p hp
      exact fun he => False.elim (hp (sub_eq_zero.mpr he))
  rw [hK.nhdsSet_prod_eq hK, mem_prod_self_iff] at hR
  obtain ⟨V,hV,hVR⟩ := hR
  obtain ⟨U,hU,hKU,hUV⟩ := mem_nhdsSet_iff_exists.mp hV
  refine ⟨U,hU,hKU,?_⟩
  intro x hx y hy he
  have hr := hVR (show (x,y) ∈ V ×ˢ V from ⟨hUV hx,hUV hy⟩)
  exact hr he

theorem analytic_compact_injective_collar {K : Set ℂ} (hK : IsCompact K)
    {f : ℂ → ℂ} (ha : AnalyticOnNhd ℂ f K) (hd : ∀ z ∈ K, deriv f z ≠ 0)
    (hi : InjOn f K) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ InjOn f U ∧ AnalyticOnNhd ℂ f U := by
  obtain ⟨U,hU,hKU,hUi⟩ := compact_local_injective_collar hK
    (fun z hz => (ha z hz).continuousAt) hi (by
      intro z hz
      have he := (ha z hz).hasStrictDerivAt.eventually_left_inverse (hd z hz)
      refine ⟨_,he,?_⟩
      intro x hx y hy hxy
      rw [← hx, ← hy, hxy])
  let W := {z | AnalyticAt ℂ f z}
  have hW : IsOpen W := isOpen_analyticAt ℂ f
  refine ⟨U ∩ W,hU.inter hW,fun z hz => ⟨hKU hz,ha z hz⟩,
    hUi.mono inter_subset_left,fun z hz => hz.2⟩

theorem conformal_modulus_boundary {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (hf : MapsTo f U (ball 0 1)) (hg : ContinuousOn g (ball 0 1))
    (hgU : MapsTo g (ball 0 1) U) (hgf : ∀ z ∈ U, g (f z) = z)
    {p : ℂ} (hp : p ∈ frontier U) :
    Tendsto (fun z => ‖f z‖) (𝓝[U] p) (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨r,hr,hra⟩ := exists_between (max_lt ha (by norm_num : (0:ℝ) < 1))
    have har : a < r := lt_of_le_of_lt (le_max_left a 0) hr
    have hsub : closedBall (0:ℂ) r ⊆ ball 0 1 := closedBall_subset_ball hra
    have hK : IsCompact (g '' closedBall (0:ℂ) r) :=
      (isCompact_closedBall 0 r).image_of_continuousOn (hg.mono hsub)
    have hpU : p ∉ U := by
      rw [hU.frontier_eq] at hp
      exact hp.2
    have hpK : p ∉ g '' closedBall (0:ℂ) r := fun ⟨z,hz,he⟩ => hpU (he ▸ hgU (hsub hz))
    have hn : (g '' closedBall (0:ℂ) r)ᶜ ∈ 𝓝 p := hK.isClosed.isOpen_compl.mem_nhds hpK
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hn] with z hz hzK
    have hnz : r < ‖f z‖ := by
      by_contra h
      have hfz : f z ∈ closedBall (0:ℂ) r := by simpa using le_of_not_gt h
      exact hzK ⟨f z,hfz,hgf z hz⟩
    exact har.trans hnz
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (mem_ball_zero_iff.mp (hf hz)).trans hb


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ConformalGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_1 u_2

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology

open Set Filter Metric Complex
open scoped Topology
section

theorem noncritical_holomorphic_inverse {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) (hinj : InjOn f U)
    (hd : ∀ z ∈ U, deriv f z ≠ 0) :
    IsOpen (f '' U) ∧ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (f '' U) ∧
      MapsTo g (f '' U) U ∧ (∀ z ∈ U, g (f z) = z) ∧
      (∀ w ∈ f '' U, f (g w) = w) := by
  classical
  have hopen : ∀ s ⊆ U, IsOpen s → IsOpen (f '' s) := by
    intro s hsU hs
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨z,hz,rfl⟩
    rw [← (hf z (hsU hz)).hasStrictDerivAt.map_nhds_eq (hd z (hsU hz))]
    exact image_mem_map (hs.mem_nhds hz)
  let e₀ := hinj.toPartialEquiv f U
  have ho : IsOpenMap (e₀.source.domRestrict e₀) := by
    intro s hs
    have hsub : (Subtype.val '' s : Set ℂ) ⊆ U := by
      rintro _ ⟨z,hz,rfl⟩
      exact z.property
    have hh := hopen (Subtype.val '' s) hsub (hU.isOpenMap_subtype_val s hs)
    convert hh using 1
    exact (Set.image_image f Subtype.val s).symm
  let e : OpenPartialHomeomorph ℂ ℂ :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict e₀ hf.continuousOn ho hU
  have hg : AnalyticOnNhd ℂ (e.symm : ℂ → ℂ) e.target := by
    apply DifferentiableOn.analyticOnNhd _ e.open_target
    intro w hw
    have hz := e.map_target hw
    have hi := (hf (e.symm w) hz).hasStrictDerivAt.to_local_left_inverse
      (hd _ hz) (e.eventually_left_inverse hz)
    have hew : f (e.symm w) = w := e.right_inv hw
    rw [hew] at hi
    exact hi.hasDerivAt.differentiableAt.differentiableWithinAt
  exact ⟨hopen U Subset.rfl hU,e.symm,hg,e.symm.mapsTo,(fun z hz => e.left_inv hz),(fun w hw => e.right_inv hw)⟩


open Set Filter Metric Complex
open scoped Topology

theorem conformal_chart_extension {U : Set ℂ} (hU : IsOpen U)
    {f g : ℂ → ℂ} (hfa : AnalyticOnNhd ℂ f U)
    (hf : MapsTo f U (ball 0 1)) (hg : ContinuousOn g (ball 0 1))
    (hgU : MapsTo g (ball 0 1) U) (hgf : ∀ z ∈ U, g (f z) = z)
    {χ : ℂ → ℂ} (hχa : AnalyticOnNhd ℂ χ (ball 0 2))
    (hχi : InjOn χ (ball 0 2)) (hχd : ∀ z ∈ ball 0 2, deriv χ z ≠ 0)
    (hside : ∀ z ∈ ball 0 2, χ z ∈ U ↔ 0 < z.im)
    (hboundary : ∀ z ∈ ball 0 2, z.im = 0 → χ z ∈ frontier U)
    (hn : ∀ z ∈ upperClosedDisk, 0 < z.im → f (χ z) ≠ 0) :
    ∃ V : Set ℂ, IsOpen V ∧ χ 0 ∈ V ∧
      ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F V ∧ deriv F (χ 0) ≠ 0 ∧
        EqOn F f (V ∩ U) := by
  have h12 : closedBall (0 : ℂ) 1 ⊆ ball 0 2 := closedBall_subset_ball (by norm_num)
  have hca : ∀ z ∈ upperClosedDisk, 0 < z.im → AnalyticAt ℂ (f ∘ χ) z := by
    intro z hz him
    exact (hfa _ ((hside z (h12 hz.1)).mpr him)).comp (hχa z (h12 hz.1))
  obtain ⟨G,hGa,hGn,hGd,hGe⟩ := conformal_reflection_upperDisk hca hn
    (fun z hz him => mem_ball_zero_iff.mp (hf ((hside z (h12 hz.1)).mpr him))) (by
      intro p hp hpi
      have hp2 := h12 hp.1
      have hb := conformal_modulus_boundary hU hf hg hgU hgf (hboundary p hp2 hpi)
      apply hb.comp
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(hχa p hp2).continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hp2)] with z him hz
      exact (hside z hz).mpr him)
  obtain ⟨ho,ψ,hψa,hψto,hψχ,hχψ⟩ := noncritical_holomorphic_inverse isOpen_ball hχa hχi hχd
  let V := χ '' ball (0 : ℂ) 1
  have hVsub : V ⊆ χ '' ball 0 2 := image_mono (ball_subset_ball (by norm_num))
  have hVo : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨z,hz,rfl⟩
    have hz2 := (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)) hz
    rw [← (hχa z hz2).hasStrictDerivAt.map_nhds_eq (hχd z hz2)]
    exact image_mem_map (isOpen_ball.mem_nhds hz)
  have h02 : (0 : ℂ) ∈ ball 0 2 := by simp
  have hψ0 : ψ (χ 0) = 0 := hψχ 0 h02
  have hpV : χ 0 ∈ V := ⟨0,by simp,rfl⟩
  have hψd : deriv ψ (χ 0) ≠ 0 := by
    have hc := ((hψa _ (hVsub hpV)).differentiableAt.hasDerivAt).comp 0
      ((hχa 0 h02).differentiableAt.hasDerivAt)
    have he : (ψ ∘ χ) =ᶠ[𝓝 (0 : ℂ)] id := by
      filter_upwards [isOpen_ball.mem_nhds h02] with z hz
      exact hψχ z hz
    have hd := (hc.congr_of_eventuallyEq he.symm).unique (hasDerivAt_id 0)
    intro h
    simp [h] at hd
  refine ⟨V,hVo,hpV,G ∘ ψ,?_,?_,?_⟩
  · intro z hz
    obtain ⟨w,hw,rfl⟩ := hz
    have hw2 := (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)) hw
    apply (hGa w hw).comp_of_eq (hψa _ ⟨w,hw2,rfl⟩)
    exact hψχ w hw2
  · have hd := ((hGa 0 (by simp)).differentiableAt.hasDerivAt).comp_of_eq (χ 0)
      ((hψa _ (hVsub hpV)).differentiableAt.hasDerivAt) hψ0.symm
    rw [hd.deriv]
    exact mul_ne_zero hGd hψd
  · rintro z ⟨⟨w,hw,rfl⟩,hwu⟩
    have hw2 := (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)) hw
    dsimp only [Function.comp_def]
    rw [hψχ w hw2]
    exact hGe ⟨hw,(hside w hw2).mp hwu⟩

end

open Set Filter Metric Complex
open scoped Topology
section

theorem analytic_family_gluing {ι : Type u_1} (U : ι → Set ℂ)
    (hU : ∀ i, IsOpen (U i)) (f : ι → ℂ → ℂ)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) (U i))
    (he : ∀ i j, EqOn (f i) (f j) (U i ∩ U j)) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (⋃ i, U i) ∧ ∀ i, EqOn F (f i) (U i) := by
  classical
  let F : ℂ → ℂ := fun z => if h : ∃ i, z ∈ U i then f h.choose z else 0
  have hFe (i : ι) : EqOn F (f i) (U i) := by
    intro z hz
    have hh : ∃ i, z ∈ U i := ⟨i,hz⟩
    rw [show F z = f hh.choose z by simp only [F,dite_eq_left hh]]
    exact he hh.choose i ⟨hh.choose_spec,hz⟩
  refine ⟨F,?_,hFe⟩
  intro z hz
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  apply (hf i z hi).congr
  filter_upwards [(hU i).mem_nhds hi] with w hw
  exact (hFe i hw).symm

lemma analytic_boundary_lens_agreement {U : Set ℂ} (hU : IsOpen U)
    {p q : ℂ} (hp : p ∈ frontier U) (hq : q ∈ frontier U)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {F G f : ℂ → ℂ} (hFa : AnalyticOnNhd ℂ F (ball p r))
    (hGa : AnalyticOnNhd ℂ G (ball q s))
    (hFe : EqOn F f (ball p r ∩ U)) (hGe : EqOn G f (ball q s ∩ U))
    (hm : (ball p (r/3) ∩ ball q (s/3)).Nonempty) :
    EqOn F G (ball p r ∩ ball q s) := by
  have hc : IsPreconnected (ball p r ∩ ball q s) :=
    ((convex_ball p r).inter (convex_ball q s)).isPreconnected
  have hopen : IsOpen (ball p r ∩ ball q s) := isOpen_ball.inter isOpen_ball
  have hmeet : (ball p r ∩ ball q s ∩ U).Nonempty := by
    obtain ⟨z,hzp,hzq⟩ := hm
    have hpq : dist p q < (r+s)/3 := by
      calc dist p q ≤ dist p z + dist z q := dist_triangle _ _ _
        _ < r/3+s/3 := add_lt_add (by simpa only [mem_ball,dist_comm] using hzp) hzq
        _ = (r+s)/3 := by ring
    rcases le_total s r with hsr | hrs
    · have hmem : q ∈ ball p r ∩ ball q s := by
        constructor
        · rw [mem_ball,dist_comm]
          linarith
        · exact mem_ball_self hs
      exact (mem_closure_iff.mp hq.1 _ hopen hmem)
    · have hmem : p ∈ ball p r ∩ ball q s := by
        constructor
        · exact mem_ball_self hr
        · rw [mem_ball]
          linarith
      exact (mem_closure_iff.mp hp.1 _ hopen hmem)
  obtain ⟨z,hz,hzu⟩ := hmeet
  apply (hFa.mono inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
    (hGa.mono inter_subset_right) hc hz
  filter_upwards [(hopen.inter hU).mem_nhds ⟨hz,hzu⟩] with w hw
  exact (hFe ⟨hw.1.1,hw.2⟩).trans (hGe ⟨hw.1.2,hw.2⟩).symm

theorem analytic_boundary_patch {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hd : ∀ z ∈ U, deriv f z ≠ 0)
    (hloc : ∀ p ∈ frontier U, ∃ V : Set ℂ, IsOpen V ∧ p ∈ V ∧
      ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F V ∧ deriv F p ≠ 0 ∧ EqOn F f (V ∩ U)) :
    ∃ W : Set ℂ, IsOpen W ∧ closure U ⊆ W ∧ ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F W ∧ EqOn F f U ∧ ∀ z ∈ closure U, deriv F z ≠ 0 := by
  classical
  have hballs (p : frontier U) : ∃ r : ℝ, 0 < r ∧ ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F (ball (p : ℂ) r) ∧ deriv F p ≠ 0 ∧
      EqOn F f (ball (p : ℂ) r ∩ U) := by
    obtain ⟨V,hVo,hp,F,hFa,hFd,hFe⟩ := hloc p p.property
    obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hVo p hp
    exact ⟨r,hr,F,hFa.mono hrV,hFd,fun z hz => hFe ⟨hrV hz.1,hz.2⟩⟩
  choose r hr g hga hgd hge using hballs
  let V : Option (frontier U) → Set ℂ := fun i => match i with
    | none => U
    | some p => ball (p : ℂ) (r p/3)
  let G : Option (frontier U) → ℂ → ℂ := fun i => match i with
    | none => f
    | some p => g p
  have hvo (i) : IsOpen (V i) := by cases i <;> simp only [V]; exact hU; exact isOpen_ball
  have hga' (i) : AnalyticOnNhd ℂ (G i) (V i) := by
    cases i with
    | none => exact hf
    | some p => exact (hga p).mono (ball_subset_ball (by have := hr p; linarith))
  have hcompat (i j) : EqOn (G i) (G j) (V i ∩ V j) := by
    cases i with
    | none =>
      cases j with
      | none => exact fun _ _ => rfl
      | some q =>
        intro z hz
        exact (hge q ⟨ball_subset_ball (by have := hr q; linarith) hz.2,hz.1⟩).symm
    | some p =>
      cases j with
      | none =>
        intro z hz
        exact hge p ⟨ball_subset_ball (by have := hr p; linarith) hz.1,hz.2⟩
      | some q =>
        intro z hz
        have he := analytic_boundary_lens_agreement hU p.property q.property
          (hr p) (hr q) (hga p) (hga q) (hge p) (hge q) ⟨z,hz⟩
        exact he ⟨ball_subset_ball (by have := hr p; linarith) hz.1,
          ball_subset_ball (by have := hr q; linarith) hz.2⟩
  obtain ⟨F,hFa,hFe⟩ := analytic_family_gluing V hvo G hga' hcompat
  refine ⟨⋃ i, V i,isOpen_iUnion hvo,?_,F,hFa,hFe none,?_⟩
  · intro z hz
    by_cases hzu : z ∈ U
    · exact mem_iUnion.mpr ⟨none,hzu⟩
    · have hzf : z ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hz,hzu⟩
      exact mem_iUnion.mpr ⟨some ⟨z,hzf⟩,mem_ball_self (div_pos (hr ⟨z,hzf⟩) (by norm_num))⟩
  · intro z hz
    by_cases hzu : z ∈ U
    · have he : F =ᶠ[𝓝 z] f := Filter.Eventually.mono (hU.mem_nhds hzu) (hFe none)
      rw [he.deriv_eq]
      exact hd z hzu
    · have hzf : z ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hz,hzu⟩
      let p : frontier U := ⟨z,hzf⟩
      have hp : z ∈ V (some p) := mem_ball_self (div_pos (hr p) (by norm_num))
      have he : F =ᶠ[𝓝 z] g p := Filter.Eventually.mono ((hvo (some p)).mem_nhds hp) (hFe (some p))
      rw [he.deriv_eq]
      exact hgd p

end

open Set Metric Filter Topology

lemma bounded_holomorphic_local_deriv {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hb : ∀ z ∈ U, ‖f z‖ ≤ 1)
    {x : ℂ} {r : ℝ} (hr : 0 < r) (hx : closedBall x (2*r) ⊆ U)
    {y : ℂ} (hy : y ∈ ball x r) : ‖deriv f y‖ ≤ 1/r := by
  have hs : closedBall y r ⊆ U := by
    intro z hz
    apply hx
    rw [mem_closedBall] at hz ⊢
    have hh := dist_triangle z y x
    have hy' : dist y x < r := hy
    linarith
  rw [← Complex.cderiv_eq_deriv hU hf hr hs]
  exact Complex.norm_cderiv_le hr (fun z hz => hb z (hs (sphere_subset_closedBall hz)))

lemma bounded_holomorphic_local_lipschitz {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hb : ∀ z ∈ U, ‖f z‖ ≤ 1)
    {x : ℂ} {r : ℝ} (hr : 0 < r) (hx : closedBall x (2*r) ⊆ U)
    {y z : ℂ} (hy : y ∈ ball x r) (hz : z ∈ ball x r) :
    ‖f z-f y‖ ≤ (1/r)*‖z-y‖ := by
  apply (convex_ball x r).norm_image_sub_le_of_norm_deriv_le ?_ ?_ hy hz
  · intro w hw
    apply hf.differentiableAt (hU.mem_nhds (hx ?_))
    exact mem_closedBall.mpr (le_trans (mem_ball.mp hw).le (by linarith))
  · intro w hw
    exact bounded_holomorphic_local_deriv hU hf hb hr hx hw

theorem bounded_holomorphic_equicontinuous {ι : Type u_2} {U : Set ℂ} (hU : IsOpen U)
    (F : ι → ℂ → ℂ) (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hb : ∀ i z, z ∈ U → ‖F i z‖ ≤ 1) : EquicontinuousOn F U := by
  intro x hx
  apply EquicontinuousAt.equicontinuousWithinAt
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨R,hR,hRU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  let r := R/2
  have hr : 0 < r := half_pos hR
  have hrU : closedBall x (2*r) ⊆ U := by
    have he : 2*r = R := by dsimp [r]; ring
    rwa [he]
  refine ⟨min r (ε*r),lt_min hr (mul_pos hε hr),?_⟩
  intro y hy i
  have hyr : y ∈ ball x r := lt_of_lt_of_le hy (min_le_left _ _)
  have hl := bounded_holomorphic_local_lipschitz hU (hF i) (hb i) hr hrU
    (mem_ball_self hr) hyr
  rw [dist_eq_norm] at hy ⊢
  have hye : ‖y-x‖ < ε*r := lt_of_lt_of_le hy (min_le_right _ _)
  rw [norm_sub_rev]
  calc
    ‖F i y-F i x‖ ≤ (1/r)*‖y-x‖ := hl
    _ < (1/r)*(ε*r) := mul_lt_mul_of_pos_left hye (one_div_pos.mpr hr)
    _ = ε := by field_simp

theorem bounded_holomorphic_subsequence {U : Set ℂ} (hU : IsOpen U)
    (F : ℕ → ℂ → ℂ) (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hb : ∀ i z, z ∈ U → ‖F i z‖ ≤ 1) :
    ∃ (f : ℂ → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (F ∘ φ) f atTop U ∧
      DifferentiableOn ℂ f U ∧ (∀ z ∈ U, ‖f z‖ ≤ 1) := by
  classical
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let C : ℕ → C(U,ℂ) := fun n => ⟨U.domRestrict (F n), (hF n).continuousOn.domRestrict⟩
  have hE : Equicontinuous (fun n (x : U) => C n x) :=
    (equicontinuous_restrict_iff F).mpr (bounded_holomorphic_equicontinuous hU F hF hb)
  have hEc : Equicontinuous (fun g : range C => ((g : C(U,ℂ)) : U → ℂ)) := by
    have hh := hE.comp (fun g : range C => g.property.choose)
    convert hh using 1
    funext g x
    exact congrArg (fun q : C(U,ℂ) => q x) g.property.choose_spec.symm
  have hc : IsCompact (closure (range C)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun g : C(U,ℂ) => (g : U → ℂ))
      (𝔖 := {K | IsCompact K}) (fun _ h => h)
      (show IsClosedEmbedding ContinuousMap.toUniformOnFunIsCompact from
        ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, by
          rw [ContinuousMap.range_toUniformOnFunIsCompact]
          exact UniformOnFun.isClosed_setOfPred_continuous
            CompactlyCoherentSpace.isCoherentWith⟩)
    · intro K _
      exact hEc.equicontinuousOn K
    · intro K _ x _
      refine ⟨closedBall (0 : ℂ) 1,isCompact_closedBall _ _,?_⟩
      rintro _ ⟨n,rfl⟩
      simpa [C, mem_closedBall, dist_zero_right] using hb n x x.property
  obtain ⟨a,_,φ,hφ,ha⟩ := hc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  let f : ℂ → ℂ := fun z => if hz : z ∈ U then a ⟨z,hz⟩ else 0
  have hl : TendstoLocallyUniformlyOn (F ∘ φ) f atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    have hh := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp ha
    have he : f ∘ (Subtype.val : U → ℂ) = (a : U → ℂ) := by
      funext x
      exact dite_eq_left x.property
    rw [he]
    exact hh
  refine ⟨f,φ,hφ,hl,hl.differentiableOn (Eventually.of_forall (fun n => hF (φ n))) hU,?_⟩
  intro z hz
  exact le_of_tendsto (hl.tendsto_at hz).norm (Eventually.of_forall (fun n => hb (φ n) z hz))

theorem zero_free_locally_uniform_limit {U : Set ℂ} (hU : IsOpen U)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hn : ∀ n z, z ∈ U → F n z ≠ 0)
    (hl : TendstoLocallyUniformlyOn F f atTop U)
    {x : ℂ} (hx : x ∈ U) (hfx : f x = 0) : f =ᶠ[𝓝 x] 0 := by
  have hf := hl.differentiableOn (Eventually.of_forall hF) hU
  rcases (hf.analyticOnNhd hU x hx).eventually_eq_zero_or_eventually_ne_zero with he | he
  · exact he
  obtain ⟨R,hR,hRe⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp he
  obtain ⟨S,hS,hSU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  let r := min (R/2) S
  have hr : 0 < r := lt_min (half_pos hR) hS
  have hrR : r < R := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hR)
  have hrU : closedBall x r ⊆ U :=
    (closedBall_subset_closedBall (min_le_right _ _)).trans hSU
  have hne : ∀ z ∈ sphere x r, f z ≠ 0 := by
    intro z hz
    apply hRe
    refine ⟨?_,?_⟩
    · exact lt_of_eq_of_lt (mem_sphere.mp hz) hrR
    · simp only [mem_compl_iff, mem_singleton_iff]
      intro hzx
      exact hr.ne' (by simpa [hzx] using (mem_sphere.mp hz).symm)
  obtain ⟨w,hw,hmin⟩ := (isCompact_sphere x r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le)
    (hf.continuousOn.norm.mono (sphere_subset_closedBall.trans hrU))
  let δ := ‖f w‖/2
  have hδ : 0 < δ := half_pos (norm_pos_iff.mpr (hne w hw))
  have hlu := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hl
    (sphere x r) (sphere_subset_closedBall.trans hrU) (isCompact_sphere x r)
  have hevent : ∀ᶠ n in atTop, δ ≤ ‖F n x‖ := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlu δ hδ] with n hn'
    have hb : ∀ z ∈ sphere x r, δ ≤ ‖F n z‖ := by
      intro z hz
      have h1 := norm_sub_norm_le (f z) (F n z)
      have h2 := hn' z hz
      rw [dist_eq_norm] at h2
      have h3 : ‖f w‖ ≤ ‖f z‖ := hmin hz
      dsimp [δ] at *
      linarith
    have hd : DiffContOnCl ℂ (fun z => (F n z)⁻¹) (ball x r) := by
      apply ((hF n).mono ?_).diffContOnCl.inv
      · intro z hz
        exact hn n z (hrU (by simpa [closure_ball x hr.ne'] using hz))
      · simpa [closure_ball x hr.ne'] using hrU
    have hi := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := x) (r := r))
      hd (C := δ⁻¹) (fun z hz => ?_) (subset_closure (mem_ball_self hr))
    · rw [norm_inv] at hi
      exact (inv_le_inv₀ (norm_pos_iff.mpr (hn n x hx)) hδ).mp hi
    · rw [frontier_ball x hr.ne'] at hz
      rw [norm_inv]
      exact (inv_le_inv₀ (norm_pos_iff.mpr (hn n z (hrU (sphere_subset_closedBall hz)))) hδ).mpr (hb z hz)
  have hc := ge_of_tendsto (hl.tendsto_at hx).norm hevent
  rw [hfx, norm_zero] at hc
  exact (not_le_of_gt hδ hc).elim

theorem injOn_locally_uniform_limit {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U) (hi : ∀ n, InjOn (F n) U)
    (hl : TendstoLocallyUniformlyOn F f atTop U)
    {a : ℂ} (ha : a ∈ U) (hda : deriv f a ≠ 0) : InjOn f U := by
  have hf := hl.differentiableOn (Eventually.of_forall hF) hU
  intro x hx y hy hxy
  by_contra hne
  let V := U \ {x}
  have hV : IsOpen V := hU.inter isClosed_singleton.isOpen_compl
  have hyV : y ∈ V := ⟨hy,by simpa using Ne.symm hne⟩
  have hconst : TendstoLocallyUniformlyOn (fun n (_ : ℂ) => F n x)
      (fun _ : ℂ => f x) atTop U :=
    (hl.tendsto_at hx).tendstoUniformly_const.tendstoLocallyUniformly.tendstoLocallyUniformlyOn
  have hl' : TendstoLocallyUniformlyOn (fun n z => F n z-F n x)
      (fun z => f z-f x) atTop V := (hl.sub hconst).mono sdiff_subset
  have he := zero_free_locally_uniform_limit hV
    (fun n => ((hF n).sub_const (F n x)).mono sdiff_subset)
    (fun n z hz he => hz.2 (by simpa using hi n hz.1 hx (sub_eq_zero.mp he)))
    hl' hyV (sub_eq_zero.mpr hxy.symm)
  have heU := ((hf.sub_const (f x)).analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hy he
  have hea : f =ᶠ[𝓝 a] (fun _ => f x) := by
    filter_upwards [hU.mem_nhds ha] with z hz
    exact sub_eq_zero.mp (heU hz)
  apply hda
  rw [hea.deriv_eq]
  exact deriv_const a (f x)

lemma exists_normalized_univalent {U : Set ℂ} (hUb : Bornology.IsBounded U) (a : ℂ) :
    ∃ f, NormalizedUnivalent U a f ∧ deriv f a ≠ 0 := by
  obtain ⟨R,hR,hUR⟩ := hUb.subset_ball_lt 0 a
  let f : ℂ → ℂ := fun z => (z-a)/(R:ℂ)
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hd : ∀ z, HasDerivAt f (1/(R:ℂ)) z := fun z =>
    ((hasDerivAt_id z).sub_const a).div_const (R:ℂ)
  refine ⟨f,⟨(fun z _ => (hd z).differentiableAt.differentiableWithinAt),?_,?_,?_⟩,?_⟩
  · intro z _ w _ he
    have h : z-a = w-a := (div_left_inj' hRc).mp he
    linear_combination h
  · intro z hz
    rw [mem_ball_zero_iff]
    change ‖(z-a)/(R:ℂ)‖ < 1
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, div_lt_one hR]
    simpa [mem_ball,dist_eq_norm] using hUR hz
  · simp [f]
  · rw [(hd a).deriv]
    exact one_div_ne_zero hRc

theorem exists_extremal_univalent {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) (hUb : Bornology.IsBounded U) {a : ℂ} (ha : a ∈ U) :
    ∃ f, NormalizedUnivalent U a f ∧ deriv f a ≠ 0 ∧
      ∀ g, NormalizedUnivalent U a g → ‖deriv g a‖ ≤ ‖deriv f a‖ := by
  classical
  obtain ⟨f₀,hf₀,hd₀⟩ := exists_normalized_univalent hUb a
  let S : Set ℝ := {r | ∃ f, NormalizedUnivalent U a f ∧ ‖deriv f a‖ = r}
  have hS : S.Nonempty := ⟨_,f₀,hf₀,rfl⟩
  obtain ⟨R,hR,hRU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds ha)
  let r := R/2
  have hr : 0 < r := half_pos hR
  have hrU : closedBall a (2*r) ⊆ U := by
    convert hRU using 1
    dsimp [r]
    congr 1
    ring
  have hSb : BddAbove S := by
    refine ⟨1/r,?_⟩
    rintro t ⟨g,hg,rfl⟩
    exact bounded_holomorphic_local_deriv hU hg.1
      (fun z hz => (mem_ball_zero_iff.mp (hg.2.2.1 hz)).le) hr hrU (mem_ball_self hr)
  have hpos : 0 < sSup S := lt_of_lt_of_le (norm_pos_iff.mpr hd₀)
    (le_csSup hSb ⟨f₀,hf₀,rfl⟩)
  obtain ⟨u,_,hu,hum⟩ := exists_seq_tendsto_sSup hS hSb
  choose F hFn hFd using hum
  obtain ⟨f,φ,hφ,hl,hf,hb⟩ := bounded_holomorphic_subsequence hU F
    (fun n => (hFn n).1) (fun n z hz => (mem_ball_zero_iff.mp ((hFn n).2.2.1 hz)).le)
  have hder := (hl.deriv (Eventually.of_forall (fun n => (hFn (φ n)).1)) hU).tendsto_at ha
  have hu' : Tendsto (fun n => ‖deriv (F (φ n)) a‖) atTop (𝓝 (sSup S)) := by
    simpa only [Function.comp_def, hFd] using hu.comp hφ.tendsto_atTop
  have he : ‖deriv f a‖ = sSup S := tendsto_nhds_unique hder.norm hu'
  have hda : deriv f a ≠ 0 := norm_pos_iff.mp (he ▸ hpos)
  have hfa : f a = 0 := by
    have h0 : Tendsto (fun n => F (φ n) a) atTop (𝓝 (0 : ℂ)) := by
      simp only [(hFn _).2.2.2]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hl.tendsto_at ha) h0
  have hmaps : MapsTo f U (ball 0 1) := by
    intro z hz
    rw [mem_ball_zero_iff]
    refine lt_of_le_of_ne (hb z hz) ?_
    intro heq
    have hmax : IsMaxOn (norm ∘ f) U z := fun w hw => (hb w hw).trans_eq heq.symm
    have hc := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUc hU hf hz hmax ha
    change f a = f z at hc
    have : f z = 0 := hc.symm.trans hfa
    simp [this] at heq
  refine ⟨f,⟨hf,injOn_locally_uniform_limit hU hUc
      (fun n => (hFn (φ n)).1) (fun n => (hFn (φ n)).2.1) hl ha hda,hmaps,hfa⟩,hda,?_⟩
  intro g hg
  rw [he]
  exact le_csSup hSb ⟨g,hg,rfl⟩


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DiskMapping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Metric Filter Topology

open Set Metric Filter Topology
section

lemma diskAut_den_ne {b z : ℂ} (hb : ‖b‖ < 1) (hz : ‖z‖ < 1) :
    1-star b*z ≠ 0 := by
  have h : ‖star b*z‖ < 1 := by
    rw [norm_mul, norm_star]
    nlinarith [norm_nonneg b,norm_nonneg z]
  exact sub_ne_zero.mpr (by intro he; rw [← he, norm_one] at h; exact (lt_irrefl _ h))

lemma diskAut_normSq_identity (b z : ℂ) :
    Complex.normSq (1-star b*z)-Complex.normSq (z-b) =
      (1-Complex.normSq b)*(1-Complex.normSq z) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

lemma diskAut_maps {b z : ℂ} (hb : ‖b‖ < 1) (hz : ‖z‖ < 1) :
    ‖diskAut b z‖ < 1 := by
  have hden := diskAut_den_ne hb hz
  have he := diskAut_normSq_identity b z
  simp only [Complex.normSq_eq_norm_sq] at he
  have hpos : 0 < (1-‖b‖^2)*(1-‖z‖^2) := by
    apply mul_pos <;> nlinarith [norm_nonneg b,norm_nonneg z]
  rw [diskAut, norm_div, div_lt_one (norm_pos_iff.mpr hden)]
  nlinarith [norm_nonneg (1-star b*z),norm_nonneg (z-b)]

lemma diskAut_inj {b : ℂ} (hb : ‖b‖ < 1) : InjOn (diskAut b) (ball 0 1) := by
  intro z hz w hw he
  rw [mem_ball_zero_iff] at hz hw
  have hdenz := diskAut_den_ne hb hz
  have hdenw := diskAut_den_ne hb hw
  have hbb := diskAut_den_ne hb hb
  have he' : (z-b)*(1-star b*w) = (w-b)*(1-star b*z) :=
    (div_eq_div_iff hdenz hdenw).mp he
  have hm : (1-star b*b)*(z-w) = 0 := by linear_combination he'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hbb)

lemma diskAut_deriv {b z : ℂ} (hb : ‖b‖ < 1) (hz : ‖z‖ < 1) :
    HasDerivAt (diskAut b) ((1-star b*b)/(1-star b*z)^2) z := by
  have hd : HasDerivAt (diskAut b)
      ((1 * (1-star b*z)-(z-b)*(0-star b*1))/(1-star b*z)^2) z :=
    (((hasDerivAt_id z).sub_const b).div
      ((hasDerivAt_const z (1:ℂ)).sub ((hasDerivAt_id z).const_mul (star b)))
      (diskAut_den_ne hb hz))
  convert hd using 1 ; ring

lemma diskAut_zero (b : ℂ) : diskAut b 0 = -b := by simp [diskAut]
lemma diskAut_self (b : ℂ) : diskAut b b = 0 := by simp [diskAut]

lemma diskAut_deriv_zero_norm {b : ℂ} (hb : ‖b‖ < 1) :
    ‖deriv (diskAut b) 0‖ = 1-‖b‖^2 := by
  rw [(diskAut_deriv hb (by simp : ‖(0:ℂ)‖ < 1)).deriv]
  have he : star b*b = (‖b‖^2 : ℝ) := by
    change (starRingEnd ℂ) b*b = _
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [he]
  simp only [mul_zero, sub_zero, one_pow, div_one]
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_of_nonneg]
  nlinarith [norm_nonneg b]

lemma diskAut_deriv_self_norm {b : ℂ} (hb : ‖b‖ < 1) :
    ‖deriv (diskAut b) b‖ = (1-‖b‖^2)⁻¹ := by
  rw [(diskAut_deriv hb hb).deriv]
  have hden := diskAut_den_ne hb hb
  have hs : (1-star b*b)/(1-star b*b)^2 = (1-star b*b)⁻¹ := by
    rw [pow_two, div_mul_eq_div_div, div_self hden, one_div]
  rw [hs,norm_inv]
  have hh := diskAut_deriv_zero_norm hb
  rw [(diskAut_deriv hb (by simp : ‖(0:ℂ)‖ < 1)).deriv] at hh
  simpa using congrArg Inv.inv hh

lemma holomorphic_square_root {U : Set ℂ} (hU : IsOpen U) (hUc : IsSimplyConnected U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hf0 : ∀ z ∈ U, f z ≠ 0) :
    ∃ g, DifferentiableOn ℂ g U ∧ (∀ z, g z ^ 2 = f z) ∧
      ∀ z ∈ U, HasDerivAt g (deriv f z / (2*g z)) z := by
  obtain ⟨g,hgc,hg⟩ := Complex.exists_continuousOn_pow_eq hUc hU hf.continuousOn
    (by rintro ⟨z,hz,he⟩; exact hf0 z hz he) two_ne_zero
  have hg0 : ∀ z ∈ U, g z ≠ 0 := by
    intro z hz he
    exact hf0 z hz (by rw [← hg z,he]; simp)
  have hd : ∀ z ∈ U, HasDerivAt g (deriv f z / (2*g z)) z := by
    intro z hz
    have hh := HasDerivAt.of_comp_left (hgc.continuousAt (hU.mem_nhds hz))
      (hasDerivAt_pow 2 (g z)) ((hf z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
      (by simpa using mul_ne_zero (two_ne_zero : (2:ℂ) ≠ 0) (hg0 z hz))
      (Eventually.of_forall hg)
    simpa using hh
  exact ⟨g,(fun z hz => (hd z hz).differentiableAt.differentiableWithinAt),hg,hd⟩


lemma square_root_improvement {U : Set ℂ} (hU : IsOpen U) (hUc : IsSimplyConnected U)
    {a : ℂ} (ha : a ∈ U) {f : ℂ → ℂ} (hf : NormalizedUnivalent U a f)
    (hdf : deriv f a ≠ 0) {b : ℂ} (hb : b ∈ ball 0 1) (hbout : b ∉ f '' U) :
    ∃ ψ, NormalizedUnivalent U a ψ ∧ ‖deriv f a‖ < ‖deriv ψ a‖ := by
  have hbn : ‖b‖ < 1 := mem_ball_zero_iff.mp hb
  have hfn : ∀ z ∈ U, ‖f z‖ < 1 := fun z hz => mem_ball_zero_iff.mp (hf.2.2.1 hz)
  have hb0 : b ≠ 0 := by
    intro he
    exact hbout ⟨a,ha,hf.2.2.2.trans he.symm⟩
  let k : ℂ → ℂ := diskAut b ∘ f
  have hkd : ∀ z ∈ U, HasDerivAt k
      (deriv (diskAut b) (f z) * deriv f z) z := by
    intro z hz
    exact (diskAut_deriv hbn (hfn z hz)).differentiableAt.hasDerivAt.comp z
      ((hf.1 z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hk : DifferentiableOn ℂ k U := fun z hz =>
    (hkd z hz).differentiableAt.differentiableWithinAt
  have hk0 : ∀ z ∈ U, k z ≠ 0 := by
    intro z hz he
    have : f z = b := sub_eq_zero.mp ((div_eq_zero_iff.mp he).resolve_right
      (diskAut_den_ne hbn (hfn z hz)))
    exact hbout ⟨z,hz,this⟩
  obtain ⟨g,hgd,hg,hgder⟩ := holomorphic_square_root hU hUc hk hk0
  have hgn : ∀ z ∈ U, ‖g z‖ < 1 := by
    intro z hz
    have he : ‖g z‖^2 = ‖k z‖ := by simpa only [norm_pow] using congrArg norm (hg z)
    have hklt : ‖k z‖ < 1 := diskAut_maps hbn (hfn z hz)
    nlinarith [norm_nonneg (g z)]
  have hginj : InjOn g U := by
    intro z hz w hw he
    apply hf.2.1 hz hw
    apply diskAut_inj hbn (hf.2.2.1 hz) (hf.2.2.1 hw)
    change k z = k w
    rw [← hg z, ← hg w,he]
  let β := g a
  have hβ : ‖β‖ < 1 := hgn a ha
  have hβsq : ‖β‖^2 = ‖b‖ := by
    have he := congrArg norm (hg a)
    simpa only [norm_pow,k,Function.comp_apply,hf.2.2.2,diskAut_zero,norm_neg] using he
  have hβpos : 0 < ‖β‖ := by
    have := norm_pos_iff.mpr hb0
    nlinarith [norm_nonneg β]
  let ψ : ℂ → ℂ := diskAut β ∘ g
  have hψder : ∀ z ∈ U, HasDerivAt ψ
      (deriv (diskAut β) (g z) * deriv g z) z := by
    intro z hz
    exact (diskAut_deriv hβ (hgn z hz)).differentiableAt.hasDerivAt.comp z
      ((hgd z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
  refine ⟨ψ,⟨(fun z hz => (hψder z hz).differentiableAt.differentiableWithinAt),?_,?_,?_⟩,?_⟩
  · exact (diskAut_inj hβ).comp hginj (fun z hz => mem_ball_zero_iff.mpr (hgn z hz))
  · intro z hz
    exact mem_ball_zero_iff.mpr (diskAut_maps hβ (hgn z hz))
  · exact diskAut_self β
  · have hkda : ‖deriv k a‖ = (1-‖b‖^2)*‖deriv f a‖ := by
      rw [(hkd a ha).deriv,norm_mul,hf.2.2.2,diskAut_deriv_zero_norm hbn]
    have he : ‖deriv ψ a‖ = (1-‖β‖^2)⁻¹ *
        ((1-‖b‖^2)*‖deriv f a‖/(2*‖β‖)) := by
      rw [(hψder a ha).deriv,norm_mul]
      change ‖deriv (diskAut β) β‖ * ‖deriv g a‖ = _
      rw [diskAut_deriv_self_norm hβ,(hgder a ha).deriv,norm_div,norm_mul]
      rw [hkda]
      norm_num [β]
    have hpos : 0 < 1-‖β‖^2 := by nlinarith [norm_nonneg β]
    have hratio : (1-‖β‖^2)⁻¹ * ((1-‖b‖^2)*‖deriv f a‖/(2*‖β‖)) =
        ((1+‖β‖^2)/(2*‖β‖))*‖deriv f a‖ := by
      rw [← hβsq]
      field_simp
      ring
    rw [he,hratio]
    have hr : 1 < (1+‖β‖^2)/(2*‖β‖) := by
      rw [one_lt_div (by positivity)]
      nlinarith [sq_pos_of_pos (sub_pos.mpr hβ)]
    exact lt_mul_of_one_lt_left (norm_pos_iff.mpr hdf) hr

theorem bounded_riemann_mapping {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) (hUb : Bornology.IsBounded U) {a : ℂ} (ha : a ∈ U) :
    ∃ f, NormalizedUnivalent U a f ∧ deriv f a ≠ 0 ∧ f '' U = ball 0 1 := by
  obtain ⟨f,hf,hdf,hext⟩ := exists_extremal_univalent hU
    hUc.isPathConnected.isConnected.isPreconnected hUb ha
  refine ⟨f,hf,hdf,Subset.antisymm hf.2.2.1.image_subset ?_⟩
  intro b hb
  by_contra hbout
  obtain ⟨ψ,hψ,hlt⟩ := square_root_improvement hU hUc ha hf hdf hb hbout
  exact not_lt_of_ge (hext ψ hψ) hlt

end

open Set Filter Topology Complex

section

theorem partialHomeomorph_analytic_inverse
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he : AnalyticOnNhd ℂ (e : ℂ → ℂ) e.source)
    (hconn : IsPreconnected e.source) {a : ℂ} (ha : a ∈ e.source)
    (hda : deriv (e : ℂ → ℂ) a ≠ 0) :
    AnalyticOnNhd ℂ (e.symm : ℂ → ℂ) e.target := by
  intro w hw
  let z := e.symm w
  have hz : z ∈ e.source := e.map_target hw
  have hzw : e z = w := e.right_inv hw
  have hcrit : ∀ᶠ u in 𝓝[≠] z, deriv (e : ℂ → ℂ) u ≠ 0 := by
    rcases (he.deriv z hz).eventually_eq_zero_or_eventually_ne_zero with hc | hc
    · exfalso
      exact hda (he.deriv.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz hc ha)
    · exact hc
  have hinv : Tendsto (e.symm : ℂ → ℂ) (𝓝[≠] w) (𝓝[≠] z) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(e.continuousAt_symm hw).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    simpa only [mem_compl_iff, mem_singleton_iff, z] using e.symm.eventually_ne_nhdsWithin hw
  have hne := hinv.eventually hcrit
  have hmem : ∀ᶠ u in 𝓝[≠] w, u ∈ e.target :=
    eventually_nhdsWithin_of_eventually_nhds (e.open_target.mem_nhds hw)
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _
    (e.continuousAt_symm hw)
  filter_upwards [hne, hmem] with u hdu hu
  have hv := e.map_target hu
  have hi := (he (e.symm u) hv).hasStrictDerivAt.to_local_left_inverse hdu
    (e.eventually_left_inverse hv)
  simpa only [e.right_inv hu] using hi.hasDerivAt.differentiableAt

theorem partialHomeomorph_deriv_ne_zero
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he : AnalyticOnNhd ℂ (e : ℂ → ℂ) e.source)
    (hconn : IsPreconnected e.source) {a : ℂ} (ha : a ∈ e.source)
    (hda : deriv (e : ℂ → ℂ) a ≠ 0) {z : ℂ} (hz : z ∈ e.source) :
    deriv (e : ℂ → ℂ) z ≠ 0 := by
  have hi := partialHomeomorph_analytic_inverse e he hconn ha hda
  have hc := (hi (e z) (e.map_source hz)).hasStrictDerivAt.hasDerivAt.comp z (he z hz).hasStrictDerivAt.hasDerivAt
  have heq : (e.symm ∘ e : ℂ → ℂ) =ᶠ[𝓝 z] id := e.eventually_left_inverse hz
  have hn : deriv (e.symm : ℂ → ℂ) (e z) * deriv (e : ℂ → ℂ) z = 1 :=
    (hc.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id z)
  intro h
  simp [h] at hn

theorem holomorphic_injective_inverse {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hf : AnalyticOnNhd ℂ f U) (hinj : InjOn f U)
    {a : ℂ} (ha : a ∈ U) (hda : deriv f a ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (f '' U) ∧
      MapsTo g (f '' U) U ∧ (∀ z ∈ U, g (f z) = z) ∧
      (∀ w ∈ f '' U, f (g w) = w) ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  classical
  have hopen : ∀ s ⊆ U, IsOpen s → IsOpen (f '' s) := by
    rcases hf.is_constant_or_isOpen hconn with hc | hc
    · rcases hc with ⟨c, hc⟩
      have heq : f =ᶠ[𝓝 a] fun _ => c :=
        (hU.eventually_mem ha).mono fun z hz => hc z hz
      exact False.elim (hda ((hasDerivAt_const a c).congr_of_eventuallyEq heq).deriv)
    · exact hc
  let e₀ := hinj.toPartialEquiv f U
  have ho : IsOpenMap (e₀.source.domRestrict e₀) := by
    intro s hs
    have hsub : (Subtype.val '' s : Set ℂ) ⊆ U := by
      rintro _ ⟨z, hz, rfl⟩
      exact z.property
    have hh := hopen (Subtype.val '' s) hsub (hU.isOpenMap_subtype_val s hs)
    convert hh using 1
    exact (Set.image_image f Subtype.val s).symm
  let e : OpenPartialHomeomorph ℂ ℂ :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict e₀ hf.continuousOn ho hU
  refine ⟨e.symm, partialHomeomorph_analytic_inverse e hf hconn ha hda,
    e.symm.mapsTo, ?_, ?_, ?_⟩
  · intro z hz
    exact e.left_inv hz
  · intro w hw
    exact e.right_inv hw
  · intro z hz
    exact partialHomeomorph_deriv_ne_zero e hf hconn ha hda hz

end

open Complex
lemma analytic_local_inverse_neighborhood {F : ℂ → ℂ} {p : ℂ}
    (ha : AnalyticAt ℂ F p) (hd : deriv F p ≠ 0) :
    ∃ V : Set ℂ, IsOpen V ∧ p ∈ V ∧ IsOpen (F '' V) ∧
      ∃ ψ : ℂ → ℂ, AnalyticOnNhd ℂ ψ (F '' V) ∧
        (∀ z ∈ V, ψ (F z) = z) ∧ (∀ w ∈ F '' V, F (ψ w) = w) := by
  have he : ∀ᶠ z in 𝓝 p, AnalyticAt ℂ F z ∧ deriv F z ≠ 0 ∧
      ha.hasStrictDerivAt.localInverse F (deriv F p) p hd (F z) = z := by
    filter_upwards [ha.eventually_analyticAt,ha.deriv.continuousAt.eventually_ne hd,
      ha.hasStrictDerivAt.eventually_left_inverse hd] with z hza hzd hze
    exact ⟨hza,hzd,hze⟩
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp he
  have hi : InjOn F (ball p r) := by
    intro x hx y hy hxy
    rw [← (hrV hx).2.2, ← (hrV hy).2.2,hxy]
  obtain ⟨ho,ψ,hψa,hψto,hψF,hFψ⟩ := noncritical_holomorphic_inverse
    isOpen_ball (fun z hz => (hrV hz).1) hi (fun z hz => (hrV hz).2.1)
  exact ⟨ball p r,isOpen_ball,mem_ball_self hr,ho,ψ,hψa,hψF,hFψ⟩

lemma conformal_extension_boundary_norm {U : Set ℂ} (hU : IsOpen U)
    {f g F : ℂ → ℂ} (hf : MapsTo f U (ball 0 1))
    (hg : ContinuousOn g (ball 0 1)) (hgU : MapsTo g (ball 0 1) U)
    (hgf : ∀ z ∈ U, g (f z) = z) (he : EqOn F f U)
    {p : ℂ} (hp : p ∈ frontier U) (hFc : ContinuousAt F p) : ‖F p‖ = 1 := by
  have := mem_closure_iff_nhdsWithin_neBot.mp hp.1
  have hlim := conformal_modulus_boundary hU hf hg hgU hgf hp
  have heq : (fun z => ‖F z‖) =ᶠ[𝓝[U] p] (fun z => ‖f z‖) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [he hz]
  exact tendsto_nhds_unique (hFc.norm.tendsto.mono_left nhdsWithin_le_nhds)
    (hlim.congr' heq.symm)

theorem conformal_inverse_boundary_limit {U : Set ℂ} (hU : IsOpen U)
    {F g : ℂ → ℂ} (hf : MapsTo F U (ball 0 1))
    (hgf : ∀ z ∈ U, g (F z) = z)
    (hb : ∀ z ∈ frontier U, ‖F z‖ = 1)
    {p : ℂ} (hp : p ∈ frontier U) (ha : AnalyticAt ℂ F p)
    (hd : deriv F p ≠ 0) : Tendsto g (𝓝[ball 0 1] (F p)) (𝓝 p) := by
  obtain ⟨V,hVo,hpV,hWo,ψ,hψa,hψF,hFψ⟩ := analytic_local_inverse_neighborhood ha hd
  have hpW : F p ∈ F '' V := ⟨p,hpV,rfl⟩
  obtain ⟨r,hr,hrW⟩ := Metric.isOpen_iff.mp hWo (F p) hpW
  let L := ball (F p) r ∩ ball (0 : ℂ) 1
  have hLc : IsPreconnected L := ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
  have hψc : ContinuousOn ψ L := hψa.continuousOn.mono (fun _ hz => hrW hz.1)
  have hpc : IsPreconnected (ψ '' L) := hLc.image ψ hψc
  have hmeet : (ψ '' L ∩ U).Nonempty := by
    have hN : V ∩ F ⁻¹' ball (F p) r ∈ 𝓝 p :=
      inter_mem (hVo.mem_nhds hpV) (ha.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr)))
    obtain ⟨z,hz,hzu⟩ := mem_closure_iff_nhds.mp hp.1 _ hN
    refine ⟨z,⟨F z,⟨hz.2,hf hzu⟩,hψF z hz.1⟩,hzu⟩
  have hto : MapsTo ψ L U := by
    have hs : ψ '' L ⊆ U := hpc.subset_of_closure_inter_subset hU hmeet (by
      rintro z ⟨hzc,ζ,hζ,rfl⟩
      by_contra hn
      have hzb : ψ ζ ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hzc,hn⟩
      have hh := hb _ hzb
      rw [hFψ ζ (hrW hζ.1)] at hh
      have hl := mem_ball_zero_iff.mp hζ.2
      linarith)
    exact fun z hz => hs ⟨z,hz,rfl⟩
  have he : g =ᶠ[𝓝[ball 0 1] (F p)] ψ := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr))] with z hz hzr
    have hh := hgf (ψ z) (hto ⟨hzr,hz⟩)
    rwa [hFψ z (hrW hzr)] at hh
  have hlim := (hψa _ hpW).continuousAt.tendsto.mono_left
    (show 𝓝[ball 0 1] (F p) ≤ 𝓝 (F p) from nhdsWithin_le_nhds)
  rw [hψF p hpV] at hlim
  exact hlim.congr' he.symm

theorem conformal_extension_injOn_closure {U : Set ℂ} (hU : IsOpen U)
    {F g : ℂ → ℂ} (hf : MapsTo F U (ball 0 1))
    (hgf : ∀ z ∈ U, g (F z) = z)
    (hb : ∀ z ∈ frontier U, ‖F z‖ = 1)
    (ha : AnalyticOnNhd ℂ F (closure U)) (hd : ∀ z ∈ closure U, deriv F z ≠ 0) :
    InjOn F (closure U) := by
  intro p hp q hq he
  by_cases hpu : p ∈ U
  · by_cases hqu : q ∈ U
    · rw [← hgf p hpu, ← hgf q hqu,he]
    · have hqb : q ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hq,hqu⟩
      have hh := mem_ball_zero_iff.mp (hf hpu)
      rw [he,hb q hqb] at hh
      exact (lt_irrefl _ hh).elim
  · have hpb : p ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hp,hpu⟩
    by_cases hqu : q ∈ U
    · have hh := mem_ball_zero_iff.mp (hf hqu)
      rw [← he,hb p hpb] at hh
      exact (lt_irrefl _ hh).elim
    · have hqb : q ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hq,hqu⟩
      have hFp : F p ∈ closure (ball (0 : ℂ) 1) := by
        rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
        simp [hb p hpb]
      have := mem_closure_iff_nhdsWithin_neBot.mp hFp
      have hlp := conformal_inverse_boundary_limit hU hf hgf hb hpb (ha p hp) (hd p hp)
      have hlq := conformal_inverse_boundary_limit hU hf hgf hb hqb (ha q hq) (hd q hq)
      rw [← he] at hlq
      exact tendsto_nhds_unique hlp hlq


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ConvexBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Metric Filter Topology
open Set Metric Filter Topology
open Set Filter Topology Complex

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
namespace CompleteCrouzeix

section

section

lemma analytic_chart_rescale_avoid {U : Set ℂ} {χ : ℂ → ℂ} {a : ℂ}
    (ha : AnalyticAt ℂ χ 0) (hd : deriv χ 0 ≠ 0)
    (hs : ∀ᶠ z : ℂ in 𝓝 0, χ z ∈ U ↔ 0 < z.im)
    (hb : ∀ᶠ z : ℂ in 𝓝 0, z.im = 0 → χ z ∈ frontier U)
    (hav : ∀ᶠ z : ℂ in 𝓝 0, χ z ≠ a) :
    ∃ ψ : ℂ → ℂ, ψ 0 = χ 0 ∧ AnalyticOnNhd ℂ ψ (ball 0 2) ∧
      InjOn ψ (ball 0 2) ∧ (∀ z ∈ ball 0 2, deriv ψ z ≠ 0) ∧
      (∀ z ∈ ball 0 2, ψ z ∈ U ↔ 0 < z.im) ∧
      (∀ z ∈ ball 0 2, z.im = 0 → ψ z ∈ frontier U) ∧
      (∀ z ∈ ball 0 2, ψ z ≠ a) := by
  have hi := ha.hasStrictDerivAt.eventually_left_inverse hd
  have hd' := ha.deriv.continuousAt.eventually_ne hd
  have hall := ha.eventually_analyticAt.and (hi.and (hd'.and (hs.and (hb.and hav))))
  obtain ⟨r,hr,hrall⟩ := Metric.mem_nhds_iff.mp hall
  let b : ℝ := r/3
  have ha0 : 0 < b := by dsimp [b]; positivity
  have han : (b : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  let ψ : ℂ → ℂ := fun z => χ ((b : ℂ)*z)
  have hmul : ∀ z ∈ ball (0 : ℂ) 2, (b : ℂ)*z ∈ ball 0 r := by
    intro z hz
    rw [mem_ball_zero_iff,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha0]
    have hz' : ‖z‖ < 2 := mem_ball_zero_iff.mp hz
    dsimp [b]
    nlinarith
  refine ⟨ψ,by simp [ψ],?_,?_,?_,?_,?_,?_⟩
  · intro z hz
    exact (hrall (hmul z hz)).1.comp (analyticAt_const.fun_mul analyticAt_id)
  · intro z hz w hw he
    have hzi := (hrall (hmul z hz)).2.1
    have hwi := (hrall (hmul w hw)).2.1
    apply mul_left_cancel₀ han
    rw [← hzi,← hwi]
    exact congrArg _ he
  · intro z hz
    have hdχ := (hrall (hmul z hz)).1.differentiableAt.hasDerivAt
    have hdd := hdχ.comp z ((hasDerivAt_id z).const_mul (b : ℂ))
    have he : deriv ψ z = deriv χ ((b : ℂ)*z)*((b : ℂ)*1) := hdd.deriv
    rw [he]
    exact mul_ne_zero (hrall (hmul z hz)).2.2.1 (mul_ne_zero han one_ne_zero)
  · intro z hz
    change χ ((b : ℂ)*z) ∈ U ↔ 0 < z.im
    rw [(hrall (hmul z hz)).2.2.2.1]
    simpa using mul_pos_iff_of_pos_left ha0
  · intro z hz him
    apply (hrall (hmul z hz)).2.2.2.2.1
    simp [him]
  · intro z hz
    exact (hrall (hmul z hz)).2.2.2.2.2


open Set Filter Metric Complex
open scoped Topology

lemma analytic_noncritical_set_open (F : ℂ → ℂ) :
    IsOpen {z | AnalyticAt ℂ F z ∧ deriv F z ≠ 0} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  exact hz.1.eventually_analyticAt.and (hz.1.deriv.continuousAt.eventually_ne hz.2)

theorem analytic_domain_disk_coordinate {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) (hUb : Bornology.IsBounded U) {a : ℂ} (ha : a ∈ U)
    (hchart : ∀ p ∈ frontier U, LocalAnalyticBoundary U p) :
    Nonempty (DiskCoordinate U a) := by
  obtain ⟨f,hf,hdfa,hfimage⟩ := bounded_riemann_mapping hU hUc hUb ha
  have hfa : AnalyticOnNhd ℂ f U := hf.1.analyticOnNhd hU
  obtain ⟨g,hga,hgto,hgf,hfg,hfd⟩ := holomorphic_injective_inverse hU
    hUc.isPathConnected.isConnected.isPreconnected hfa hf.2.1 ha hdfa
  rw [hfimage] at hga hgto hfg
  have hloc : ∀ p ∈ frontier U, ∃ V : Set ℂ, IsOpen V ∧ p ∈ V ∧
      ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F V ∧ deriv F p ≠ 0 ∧ EqOn F f (V ∩ U) := by
    intro p hp
    obtain ⟨χ,hχ0,hχa,hχd,hχs,hχb⟩ := hchart p hp
    have hpa : p ≠ a := by
      intro he
      have hpnot : p ∉ U := by rw [hU.frontier_eq] at hp; exact hp.2
      exact hpnot (he ▸ ha)
    have hav : ∀ᶠ z : ℂ in 𝓝 0, χ z ≠ a := hχa.continuousAt.eventually_ne (hχ0 ▸ hpa)
    obtain ⟨ψ,hψ0,hψa,hψi,hψd,hψs,hψb,hψav⟩ :=
      analytic_chart_rescale_avoid hχa hχd hχs hχb hav
    have hn : ∀ z ∈ upperClosedDisk, 0 < z.im → f (ψ z) ≠ 0 := by
      intro z hz him he
      have hz2 : z ∈ ball (0 : ℂ) 2 := closedBall_subset_ball (by norm_num : (1 : ℝ)<2) hz.1
      have hpu := (hψs z hz2).mpr him
      apply hψav z hz2
      exact hf.2.1 hpu ha (he.trans hf.2.2.2.symm)
    obtain ⟨V,hVo,hpV,F,hFa,hFd,hFe⟩ := conformal_chart_extension hU hfa hf.2.2.1
      hga.continuousOn hgto hgf hψa hψi hψd hψs hψb hn
    have hψp : ψ 0 = p := hψ0.trans hχ0
    exact ⟨V,hVo,hψp ▸ hpV,F,hFa,hψp ▸ hFd,hFe⟩
  obtain ⟨W,hWo,hUW,F,hFa,hFe,hFd⟩ := analytic_boundary_patch hU hfa hfd hloc
  have hFc : AnalyticOnNhd ℂ F (closure U) := hFa.mono hUW
  have hFto : MapsTo F U (ball 0 1) := by intro z hz; rw [hFe hz]; exact hf.2.2.1 hz
  have hgF : ∀ z ∈ U, g (F z) = z := by intro z hz; rw [hFe hz]; exact hgf z hz
  have hFb : ∀ p ∈ frontier U, ‖F p‖ = 1 := by
    intro p hp
    exact conformal_extension_boundary_norm hU hf.2.2.1 hga.continuousOn hgto hgf hFe hp
      (hFc p hp.1).continuousAt
  have hFi := conformal_extension_injOn_closure hU hFto hgF hFb hFc hFd
  have hK : IsCompact (closure U) := isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure,hUb.closure⟩
  obtain ⟨V₀,hV₀o,hUV₀,hV₀i,hV₀a⟩ := analytic_compact_injective_collar hK hFc hFd hFi
  let V := V₀ ∩ {z | AnalyticAt ℂ F z ∧ deriv F z ≠ 0}
  have hVo : IsOpen V := hV₀o.inter (analytic_noncritical_set_open F)
  have hUV : closure U ⊆ V := fun z hz => ⟨hUV₀ hz,hFc z hz,hFd z hz⟩
  have hVi : InjOn F V := hV₀i.mono inter_subset_left
  have hVa : AnalyticOnNhd ℂ F V := hV₀a.mono inter_subset_left
  have hVd : ∀ z ∈ V, deriv F z ≠ 0 := fun z hz => hz.2.2
  obtain ⟨hFo,G,hGa,hGto,hGF,hFG⟩ := noncritical_holomorphic_inverse hVo hVa hVi hVd
  have hFimage : F '' U = ball 0 1 := by rw [hFe.image_eq,hfimage]
  have hcl : closedBall (0 : ℂ) 1 ⊆ F '' closure U := by
    rw [← closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0),← hFimage]
    exact closure_minimal (image_mono subset_closure) (hK.image_of_continuousOn hFc.continuousOn).isClosed
  exact ⟨⟨V,hVo,hUV,F,G,hVa,hVi,hVd,hFo,hGa,hGto,hGF,hFG,
    hcl.trans (image_mono hUV),hFimage,(hFe ha).trans hf.2.2.2⟩⟩

end

open Set Filter Metric Complex
open scoped Topology
namespace DiskCoordinate
variable {U : Set ℂ} {a : ℂ} (D : DiskCoordinate U a)

lemma inverse_injective : InjOn D.fromDisk (D.toDisk '' D.outer) := by
  intro w hw z hz he
  rw [← D.right_inverse w hw,← D.right_inverse z hz,he]

lemma inverse_noncritical (w : ℂ) (hw : w ∈ D.toDisk '' D.outer) : deriv D.fromDisk w ≠ 0 := by
  have hd := (D.analytic_to (D.fromDisk w) (D.inverse_map hw)).differentiableAt.hasDerivAt.comp w
    (D.analytic_from w hw).differentiableAt.hasDerivAt
  have he : (D.toDisk ∘ D.fromDisk) =ᶠ[𝓝 w] id := by
    filter_upwards [D.image_open.mem_nhds hw] with z hz
    exact D.right_inverse z hz
  have hed := hd.congr_of_eventuallyEq he.symm
  have hmul : deriv D.toDisk (D.fromDisk w)*deriv D.fromDisk w = 1 :=
    hed.unique (hasDerivAt_id w)
  intro hn
  simp [hn] at hmul

lemma exists_inverse_radius : ∃ R : ℝ, 1 < R ∧ ball (0 : ℂ) R ⊆ D.toDisk '' D.outer := by
  obtain ⟨δ,hδ,hδsub⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open
    D.image_open D.closedDisk_subset
  have he := thickening_closedBall hδ (by norm_num : (0 : ℝ) ≤ 1) (0 : ℂ)
  exact ⟨δ+1,by linarith,he ▸ hδsub⟩

lemma inverse_base (ha : a ∈ U) : D.fromDisk 0 = a := by
  rw [← D.base_zero,D.left_inverse a (D.closure_subset (subset_closure ha))]

lemma inverse_mem_closure_iff {w : ℂ} (hw : w ∈ D.toDisk '' D.outer) :
    D.fromDisk w ∈ closure U ↔ w ∈ closedBall 0 1 := by
  constructor
  · intro h
    have he := D.closure_maps h
    rwa [D.right_inverse w hw] at he
  · exact D.inverse_closed w

end DiskCoordinate
end

open Set Metric Filter Complex
open scoped Topology BigOperators ComplexConjugate

end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ConvexExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_23 u_24 u_25

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Metric Filter Topology
open Set Metric Filter Topology
open Set Filter Topology Complex
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Metric Filter Complex
open scoped Topology BigOperators ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate

open Set Filter Metric Complex
open scoped Topology
section

lemma invertedExterior_open {K : Set ℂ} {a : ℂ}
    (hK : IsCompact K) : IsOpen (invertedExterior K a) := by
  rw [isOpen_iff_mem_nhds]
  intro w hw
  by_cases hw0 : w = 0
  · subst w
    obtain ⟨R,hR,hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : ℂ)
    let r : ℝ := (R+‖a‖+1)⁻¹
    have hden : 0 < R+‖a‖+1 := by positivity
    have hr : 0 < r := inv_pos.mpr hden
    apply mem_of_superset (ball_mem_nhds 0 hr)
    intro z hz
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    · right
      intro hk
      have he := mem_ball_zero_iff.mp (hKR hk)
      have hb := norm_sub_le (a+z⁻¹) a
      have hl : R+‖a‖+1 < ‖z⁻¹‖ := by
        rw [norm_inv]
        have hz' : ‖z‖ < (R+‖a‖+1)⁻¹ := mem_ball_zero_iff.mp hz
        exact (lt_inv_comm₀ hden (norm_pos_iff.mpr hz0)).mpr hz'
      have hsub : a+z⁻¹-a = z⁻¹ := by ring
      rw [hsub] at hb
      linarith
  · have hw := hw.resolve_left hw0
    have hc : ContinuousAt (fun z : ℂ => a+z⁻¹) w := continuousAt_const.add (continuousAt_inv₀ hw0)
    exact mem_of_superset (hc.preimage_mem_nhds (hK.isClosed.isOpen_compl.mem_nhds hw))
      (fun z hz => Or.inr hz)

lemma invertedExterior_bounded {K : Set ℂ} {a : ℂ}
    (ha : a ∈ interior K) : Bornology.IsBounded (invertedExterior K a) := by
  obtain ⟨r,hr,hrK⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ha)
  apply (isBounded_closedBall (x := (0 : ℂ)) (r := r⁻¹)).subset
  intro w hw
  rw [mem_closedBall_zero_iff]
  by_cases hw0 : w = 0
  · simp [hw0,hr.le]
  · by_contra hn
    have hn' : r⁻¹ < ‖w‖ := lt_of_not_ge hn
    apply hw.resolve_left hw0
    apply hrK
    rw [mem_ball,dist_eq_norm]
    have he : a+w⁻¹-a = w⁻¹ := by ring
    rw [he,norm_inv]
    exact (inv_lt_comm₀ (norm_pos_iff.mpr hw0) hr).mpr hn'

lemma invertedExterior_starConvex {K : Set ℂ} {a : ℂ}
    (hK : Convex ℝ K) (ha : a ∈ K) : StarConvex ℝ 0 (invertedExterior K a) := by
  intro w hw s t hs ht hst
  simp only [smul_zero,zero_add]
  by_cases ht0 : t = 0
  · simp [ht0]
  by_cases hw0 : w = 0
  · simp [hw0]
  right
  intro hz
  apply hw.resolve_left hw0
  have ht1 : t ≤ 1 := by linarith
  have hb := hK ha hz (sub_nonneg.mpr ht1) ht (by ring : 1-t+t=1)
  convert hb using 1
  simp only [Complex.real_smul,Complex.ofReal_sub,Complex.ofReal_one]
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  field_simp [htc, hw0]
  ring

lemma invertedExterior_simplyConnected {K : Set ℂ} {a : ℂ}
    (hK : Convex ℝ K) (ha : a ∈ K) : SimplyConnectedSpace (invertedExterior K a) := by
  let := (invertedExterior_starConvex hK ha).contractibleSpace ⟨0,zero_mem_invertedExterior K a⟩
  infer_instance

lemma invertedExterior_frontier {U : Set ℂ} {a p : ℂ}
    (hU : IsOpen U) (hK : IsCompact (closure U)) (_ha : a ∈ U)
    (hp : p ∈ frontier (invertedExterior (closure U) a)) :
    p ≠ 0 ∧ a+p⁻¹ ∈ frontier U := by
  have hV := invertedExterior_open (a := a) hK
  have hpnot : p ∉ invertedExterior (closure U) a := by rw [hV.frontier_eq] at hp; exact hp.2
  have hp0 : p ≠ 0 := fun he => hpnot (he ▸ zero_mem_invertedExterior (closure U) a)
  have hpK : a+p⁻¹ ∈ closure U := not_not.mp (fun hn => hpnot (Or.inr hn))
  refine ⟨hp0,?_⟩
  rw [hU.frontier_eq]
  refine ⟨hpK,?_⟩
  intro hpu
  have hc : ContinuousAt (fun z : ℂ => a+z⁻¹) p := continuousAt_const.add (continuousAt_inv₀ hp0)
  have he := hc.preimage_mem_nhds (hU.mem_nhds hpu)
  have hne : ∀ᶠ z : ℂ in 𝓝 p, z ≠ 0 := eventually_ne_nhds hp0
  have hass : ∀ᶠ z : ℂ in 𝓝 p, z ∉ invertedExterior (closure U) a := by
    filter_upwards [he,hne] with z hz hn
    exact fun h => h.resolve_left hn (subset_closure hz)
  exact (mem_closure_iff_frequently.mp hp.1).and_eventually hass |>.exists |>.elim
    (fun z hz => hz.2 hz.1)


lemma local_side_frontier {U : Set ℂ} (hU : IsOpen U) {χ : ℂ → ℂ}
    (ha : ∀ᶠ z : ℂ in 𝓝 0, ContinuousAt χ z)
    (hs : ∀ᶠ z : ℂ in 𝓝 0, χ z ∈ U ↔ 0 < z.im) :
    ∀ᶠ z : ℂ in 𝓝 0, z.im = 0 → χ z ∈ frontier U := by
  obtain ⟨r,hr,hrall⟩ := Metric.mem_nhds_iff.mp (ha.and hs)
  apply mem_of_superset (ball_mem_nhds 0 hr)
  intro z hz him
  rw [hU.frontier_eq]
  refine ⟨?_,fun h => by simpa [him] using (hrall hz).2.mp h⟩
  have hzc : z ∈ closure {w : ℂ | 0 < w.im} := by simp [him]
  have hzbc : z ∈ closure (ball (0 : ℂ) r ∩ {w : ℂ | 0 < w.im}) :=
    mem_closure_iff_frequently.mpr (((mem_closure_iff_frequently.mp hzc).and_eventually
      (isOpen_ball.mem_nhds hz)).mono (fun w hw => ⟨hw.2,hw.1⟩))
  have he := mem_closure_image (hrall hz).1 hzbc
  exact closure_mono (by rintro w ⟨v,hv,rfl⟩; exact (hrall hv.1).2.mpr hv.2) he
end

lemma invertedExterior_mem_closure_iff {K : Set ℂ} {a w : ℂ} (hw : w ≠ 0) :
    w ∈ closure (invertedExterior K a) ↔ a+w⁻¹ ∉ interior K := by
  constructor
  · intro h hib
    have hc : ContinuousAt (fun z : ℂ => a+z⁻¹) w := continuousAt_const.add (continuousAt_inv₀ hw)
    have hb := hc.preimage_mem_nhds (isOpen_interior.mem_nhds hib)
    have hn := eventually_ne_nhds hw
    have he : ∀ᶠ z : ℂ in 𝓝 w, z ∉ invertedExterior K a := by
      filter_upwards [hb,hn] with z hz hzn
      exact fun h => h.resolve_left hzn (interior_subset hz)
    obtain ⟨z,hz,hzn⟩ := ((mem_closure_iff_frequently.mp h).and_eventually he).exists
    exact hzn hz
  · intro h
    have hc : ContinuousAt (fun z : ℂ => (z-a)⁻¹) (a+w⁻¹) :=
      (continuousAt_id.sub continuousAt_const).inv₀ (by simpa using inv_ne_zero hw)
    have hz : a+w⁻¹ ∈ closure Kᶜ := by simpa only [closure_compl,mem_compl_iff] using h
    have he := mem_closure_image hc hz
    have hsub : (fun z : ℂ => (z-a)⁻¹) '' Kᶜ ⊆ invertedExterior K a := by
      rintro z ⟨v,hv,rfl⟩
      right
      simpa only [inv_inv,add_sub_cancel,mem_compl_iff] using hv
    have hm := closure_mono hsub he
    simpa using hm

lemma invertedExterior_frontier_iff {U : Set ℂ} {a w : ℂ}
    (hU : IsOpen U) (hK : IsCompact (closure U)) (hreg : interior (closure U) = U)
    (hw : w ≠ 0) :
    w ∈ frontier (invertedExterior (closure U) a) ↔ a+w⁻¹ ∈ frontier U := by
  rw [(invertedExterior_open (a := a) hK).frontier_eq,hU.frontier_eq]
  change (w ∈ closure (invertedExterior (closure U) a) ∧ ¬ (w=0 ∨ a+w⁻¹ ∉ closure U)) ↔ _
  rw [invertedExterior_mem_closure_iff hw,hreg,or_iff_right hw]
  simp only [not_not,Set.mem_sdiff]
  exact and_comm

end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_BoundaryNormals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_26 u_27

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Metric Filter Topology
open Set Metric Filter Topology
open Set Filter Topology Complex
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Metric Filter Complex
open scoped Topology BigOperators ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology

section
lemma invertedExterior_local_chart {K : Set ℂ} {a p : ℂ}
    (hK : IsCompact K) {χ : ℂ → ℂ} (hχ0 : χ 0 = p)
    (hχa : AnalyticAt ℂ χ 0) (hχd : deriv χ 0 ≠ 0) (hpa : p ≠ a)
    (hχs : ∀ᶠ z : ℂ in 𝓝 0, χ z ∈ K ↔ 0 ≤ z.im) :
    ∃ ψ : ℂ → ℂ, ψ 0 = (p-a)⁻¹ ∧ AnalyticAt ℂ ψ 0 ∧ deriv ψ 0 ≠ 0 ∧
      (∀ᶠ z : ℂ in 𝓝 0, ψ z ∈ invertedExterior K a ↔ 0 < z.im) ∧
      (∀ᶠ z : ℂ in 𝓝 0, z.im = 0 → ψ z ∈ frontier (invertedExterior K a)) := by
  let ψ : ℂ → ℂ := fun z => (χ (-z)-a)⁻¹
  have hne : χ (-(0 : ℂ))-a ≠ 0 := by simpa [hχ0] using sub_ne_zero.mpr hpa
  have hχan : AnalyticAt ℂ χ (-(0 : ℂ)) := by simpa using hχa
  have han : AnalyticAt ℂ (fun z : ℂ => -z) 0 := analyticAt_id.neg
  have ha : AnalyticAt ℂ ψ 0 := ((hχan.comp han).sub analyticAt_const).inv hne
  have hdχ := hχa.differentiableAt.hasDerivAt
  have hd := ((hdχ.comp_of_eq 0 (hasDerivAt_id (0 : ℂ)).neg (by simp)).sub_const a).inv hne
  have hψd : deriv ψ 0 ≠ 0 := by
    have hed : deriv ψ 0 = -(deriv χ 0 * -1) / (χ (-0)-a)^2 := hd.deriv
    rw [hed]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hχd (neg_ne_zero.mpr one_ne_zero)))
      (pow_ne_zero 2 hne)
  have hcn : ContinuousAt (fun z : ℂ => -z) 0 := continuousAt_id.neg
  have hsn : ∀ᶠ z : ℂ in 𝓝 0, χ (-z) ∈ K ↔ 0 ≤ (-z).im :=
    hcn.tendsto.eventually (by simpa using hχs)
  have hen : ∀ᶠ z : ℂ in 𝓝 0, χ (-z)-a ≠ 0 :=
    ((hχan.continuousAt.comp hcn).sub continuousAt_const).eventually_ne hne
  have hs : ∀ᶠ z : ℂ in 𝓝 0, ψ z ∈ invertedExterior K a ↔ 0 < z.im := by
    filter_upwards [hsn,hen] with z hz hn
    have he : a+(ψ z)⁻¹ = χ (-z) := by dsimp [ψ]; rw [inv_inv]; ring
    change ψ z = 0 ∨ a+(ψ z)⁻¹ ∉ K ↔ 0 < z.im
    rw [he,or_iff_right (inv_ne_zero hn),hz]
    simp
  refine ⟨ψ,by simp [ψ,hχ0],ha,hψd,hs,?_⟩
  exact local_side_frontier (invertedExterior_open hK)
    (ha.eventually_analyticAt.mono (fun z hz => hz.continuousAt)) hs

open Set Filter Metric Complex
open scoped Topology

end

section

lemma reciprocal_simple_zero_laurent {H : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hHa : AnalyticOnNhd ℂ H (ball 0 R)) (hHi : InjOn H (ball 0 R))
    (hH0 : H 0 = 0) (hHd : deriv H 0 ≠ 0) (c : ℂ) :
    ∃ a : ℂ, ∃ h : ℂ → ℂ, a ≠ 0 ∧ AnalyticOnNhd ℂ h (ball 0 R) ∧
      ∀ t : ℂ, R⁻¹ < ‖t‖ → exteriorMap a c h t = c+(H t⁻¹)⁻¹ := by
  have h0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  let k := dslope H 0
  have hka : AnalyticOnNhd ℂ k (ball 0 R) := analyticOnNhd_dslope isOpen_ball hHa h0
  have hkn : ∀ z ∈ ball 0 R, k z ≠ 0 := fun z hz => dslope_ne_zero_of_injOn hHi h0 hz hHd
  let q : ℂ → ℂ := fun z => (k z)⁻¹
  have hqa : AnalyticOnNhd ℂ q (ball 0 R) := fun z hz => (hka z hz).inv (hkn z hz)
  let h := dslope q 0
  refine ⟨q 0,h,inv_ne_zero (hkn 0 h0),analyticOnNhd_dslope isOpen_ball hqa h0,?_⟩
  intro t ht
  have ht0 : t ≠ 0 := by intro he; simp [he] at ht; exact (not_lt_of_ge hR.le) ht
  have hinv : t⁻¹ ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff,norm_inv]
    exact (inv_lt_comm₀ (norm_pos_iff.mpr ht0) hR).mpr ht
  have hk : t⁻¹*k t⁻¹ = H t⁻¹ := by simpa [k,hH0,smul_eq_mul] using sub_smul_dslope H 0 t⁻¹
  have hq : t⁻¹*h t⁻¹ = q t⁻¹-q 0 := by simpa [h,smul_eq_mul] using sub_smul_dslope q 0 t⁻¹
  have he : H t⁻¹ ≠ 0 := by
    intro hh
    exact (inv_ne_zero ht0) (hHi hinv h0 (hh.trans hH0.symm))
  dsimp [exteriorMap]
  rw [← hk]
  dsimp [q]
  have hq' : h t⁻¹ = t*((k t⁻¹)⁻¹-(k 0)⁻¹) := by
    calc _ = t*(t⁻¹*h t⁻¹) := by rw [← mul_assoc,mul_inv_cancel₀ ht0,one_mul]
         _ = _ := by rw [hq]
  rw [hq',mul_inv_rev]
  simp only [inv_inv]
  ring


open Set Filter Metric Complex
open scoped Topology

lemma exteriorCoordinate_of_disk_inversion {U : Set ℂ} {c : ℂ}
    (hU : IsOpen U) (hK : IsCompact (closure U)) (hc : c ∈ U)
    (hreg : interior (closure U) = U)
    (D : DiskCoordinate (invertedExterior (closure U) c) 0) :
    Nonempty (ExteriorCoordinate U) := by
  let V := invertedExterior (closure U) c
  let H := D.fromDisk
  obtain ⟨R,hR,hRD⟩ := D.exists_inverse_radius
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hRinv : R⁻¹ < 1 := (inv_lt_one₀ hR0).mpr hR
  have hHa : AnalyticOnNhd ℂ H (ball 0 R) := D.analytic_from.mono hRD
  have hHi : InjOn H (ball 0 R) := D.inverse_injective.mono hRD
  have hH0 : H 0 = 0 := D.inverse_base (zero_mem_invertedExterior (closure U) c)
  have hHd : ∀ z ∈ ball (0 : ℂ) R, deriv H z ≠ 0 := fun z hz => D.inverse_noncritical z (hRD hz)
  have h0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR0
  obtain ⟨a,h,ha,hah,he⟩ := reciprocal_simple_zero_laurent hR0 hHa hHi hH0 (hHd 0 h0) c
  let G := exteriorMap a c h
  let X := {t : ℂ | R⁻¹ < ‖t‖}
  have hX : IsOpen X := isOpen_lt continuous_const continuous_norm
  have ht0 : ∀ t ∈ X, t ≠ 0 := by
    intro t ht hn
    have hp := inv_pos.mpr hR0
    simp only [X,mem_ofPred_eq,hn,norm_zero] at ht
    linarith
  have hinv : ∀ t ∈ X, t⁻¹ ∈ ball (0 : ℂ) R := by
    intro t ht
    rw [mem_ball_zero_iff,norm_inv]
    exact (inv_lt_comm₀ (norm_pos_iff.mpr (ht0 t ht)) hR0).mpr ht
  have hHn : ∀ t ∈ X, H t⁻¹ ≠ 0 := by
    intro t ht hn
    exact (inv_ne_zero (ht0 t ht)) (hHi (hinv t ht) h0 (hn.trans hH0.symm))
  have hGX : ∀ t ∈ X, G t = c+(H t⁻¹)⁻¹ := he
  have hGi : InjOn G X := by
    intro s hs t ht hst
    rw [hGX s hs,hGX t ht] at hst
    exact inv_injective (hHi (hinv s hs) (hinv t ht) (inv_injective (add_left_cancel hst)))
  have hGd : ∀ t ∈ X, deriv G t ≠ 0 := by
    intro t ht
    have hdH := (hHa t⁻¹ (hinv t ht)).differentiableAt.hasDerivAt
    have hdi := hasDerivAt_inv (ht0 t ht)
    have hdHinv := (hdH.comp t hdi).inv (hHn t ht)
    have hdc := hdHinv.const_add c
    have hevt : G =ᶠ[𝓝 t] (fun z => c+(H z⁻¹)⁻¹) := by
      filter_upwards [hX.mem_nhds ht] with z hz
      exact hGX z hz
    have hdd := hdc.congr_of_eventuallyEq hevt
    rw [hdd.deriv]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (hHd _ (hinv t ht))
      (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 (ht0 t ht)))))) (pow_ne_zero 2 (hHn t ht))
  have hGb : G '' sphere 0 1 = frontier U := by
    apply Subset.antisymm
    · rintro z ⟨t,ht,rfl⟩
      have htn : ‖t‖ = 1 := mem_sphere_zero_iff_norm.mp ht
      have htX : t ∈ X := by change R⁻¹ < ‖t‖; rwa [htn]
      have hit : t⁻¹ ∈ sphere (0 : ℂ) 1 := by simp [htn]
      have hHv : H t⁻¹ ∈ frontier V := D.inverse_sphere_frontier (invertedExterior_open hK) ▸ mem_image_of_mem H hit
      rw [hGX t htX]
      exact (invertedExterior_frontier_iff hU hK hreg (hHn t htX)).mp hHv
    · intro z hz
      have hzc : z ≠ c := by intro hec; exact (hU.frontier_eq ▸ hz).2 (hec ▸ hc)
      let w := (z-c)⁻¹
      have hw0 : w ≠ 0 := inv_ne_zero (sub_ne_zero.mpr hzc)
      have hwe : c+w⁻¹ = z := by dsimp [w]; rw [inv_inv]; ring
      have hwv : w ∈ frontier V := (invertedExterior_frontier_iff hU hK hreg hw0).mpr (hwe ▸ hz)
      obtain ⟨s,hs,hse⟩ := D.inverse_sphere_frontier (invertedExterior_open hK) ▸ hwv
      have hsn : ‖s‖ = 1 := mem_sphere_zero_iff_norm.mp hs
      have htX : s⁻¹ ∈ X := by simp [X,hsn,hRinv]
      refine ⟨s⁻¹,?_,?_⟩
      · simp [hsn]
      · rw [hGX s⁻¹ htX,inv_inv]
        change c+(D.fromDisk s)⁻¹ = z
        rw [hse,hwe]
  have hinner : ∀ t ∈ X, G t ∈ U ↔ t ∈ ball (0 : ℂ) 1 := by
    intro t ht
    have hcl := invertedExterior_mem_closure_iff (K := closure U) (a := c) (hHn t ht)
    rw [hreg,← hGX t ht, D.inverse_mem_closure_iff (hRD (hinv t ht))] at hcl
    have htpos := norm_pos_iff.mpr (ht0 t ht)
    rw [mem_closedBall_zero_iff,norm_inv] at hcl
    rw [mem_ball_zero_iff]
    have he : ‖t‖⁻¹ ≤ 1 ↔ 1 ≤ ‖t‖ := (inv_le_one₀ htpos)
    rw [he] at hcl
    simpa only [not_not, not_le] using (not_congr hcl.symm)
  have hout : ∀ t, 1 < ‖t‖ → G t ∉ closure U := by
    intro t ht
    have htX : t ∈ X := lt_trans hRinv ht
    have hib : t⁻¹ ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff,norm_inv]
      exact (inv_lt_one₀ (norm_pos_iff.mpr (ht0 t htX))).mpr ht
    have hv : H t⁻¹ ∈ V := D.inverse_ball t⁻¹ hib
    rw [hGX t htX]
    exact hv.resolve_left (hHn t htX)
  exact ⟨⟨R,hR,a,c,h,ha,hah,hGi,hGd,hGb,hinner,hout⟩⟩
end

open Set Filter Metric Complex
open scoped Topology ComplexConjugate


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_CircleIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_30 u_31 u_32 u_33 u_34

open Set Filter Metric Complex
open scoped Topology ComplexConjugate

open MeasureTheory Set Complex
open scoped Topology Real

open MeasureTheory Set Metric Complex Filter
open scoped Topology
section

lemma compact_parametric_hasDerivAt {α : Type u_31} [TopologicalSpace α]
    [CompactSpace α] [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {U : Set ℂ} (hU : IsOpen U)
    {f f' : ℂ → α → ℂ}
    (hf : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hf' : ContinuousOn (Function.uncurry f') (U ×ˢ univ))
    (hd : ∀ z ∈ U, ∀ t, HasDerivAt (fun w => f w t) (f' z t) z)
    {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun w => ∫ t, f w t ∂μ) (∫ t, f' z t ∂μ) z := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  have hs : closedBall z (ε/2) ⊆ U := by
    exact (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨C,hC⟩ := (isCompact_closedBall z (ε/2)).prod isCompact_univ
    |>.exists_bound_of_continuousOn (hf'.mono (prod_mono hs (Subset.refl _)))
  have hc (w : ℂ) (hw : w ∈ U) : Continuous (f w) := by
    exact hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun t => ⟨hw,mem_univ t⟩)
  have hc' (w : ℂ) (hw : w ∈ U) : Continuous (f' w) := by
    exact hf'.comp_continuous (continuous_const.prodMk continuous_id)
      (fun t => ⟨hw,mem_univ t⟩)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := f) (F' := f') (bound := fun _ : α => C)
    (closedBall_mem_nhds z (by linarith : 0 < ε/2)) ?_ ?_ ?_ ?_ (integrable_const C) ?_).2
  · filter_upwards [hU.mem_nhds hz] with w hw
    exact (hc w hw).aestronglyMeasurable
  · exact (hc z hz).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (hc' z hz).aestronglyMeasurable
  · filter_upwards [] with t
    intro w hw
    exact hC (w,t) ⟨hw,mem_univ t⟩
  · filter_upwards [] with t
    intro w hw
    exact hd w (hs hw) t

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ExteriorProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_45

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
open scoped ComplexConjugate InnerProductSpace
open Set Metric Filter Complex
open scoped Topology

open MeasureTheory Set Complex
open scoped Topology
section

lemma interval_integral_swap_continuous {f : ℝ → ℝ → ℂ}
    (hf : ContinuousOn (Function.uncurry f) (Icc (0:ℝ) 1 ×ˢ Icc 0 1)) :
    (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, f s t) =
      ∫ t in (0:ℝ)..1, ∫ s in (0:ℝ)..1, f s t := by
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  apply integral_integral_swap
  rw [Measure.prod_restrict]
  exact hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

lemma analytic_segment_integral {U : Set ℂ} (hU : Convex ℝ U)
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U) {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U) :
    (∫ r in (0:ℝ)..1, (w-z) * deriv F (z + (r:ℂ)*(w-z))) = F w - F z := by
  have hm : MapsTo (fun r : ℝ => z + (r:ℂ)*(w-z)) (Icc 0 1) U := by
    intro r hr
    simpa only [Complex.real_smul] using hU.add_smul_sub_mem hz hw hr
  have hc : ContinuousOn (fun r : ℝ => (w-z) * deriv F (z+(r:ℂ)*(w-z))) (Icc 0 1) :=
    continuousOn_const.mul (hF.deriv.continuousOn.comp (by fun_prop) hm)
  have hd : ∀ r ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun r : ℝ => F (z+(r:ℂ)*(w-z)))
        ((w-z)*deriv F (z+(r:ℂ)*(w-z))) r := by
    intro r hr
    have hi := (((hasDerivAt_id r).ofReal_comp).mul_const (w-z)).const_add z
    simpa only [Function.comp_def, ofReal_one, one_mul, mul_one, id_eq, mul_comm] using
      ((hF _ (hm hr)).differentiableAt.hasDerivAt).comp r hi
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
    (fun r hr => hd r (by simpa using hr))
    (show ContinuousOn _ (uIcc (0:ℝ) 1) by simpa using hc).intervalIntegrable
  simpa using he

theorem convex_closed_curve_remainder {U : Set ℂ} (hU : Convex ℝ U)
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U)
    {γ γ' : ℝ → ℂ} (hγ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt γ (γ' t) t)
    (hγ' : ContinuousOn γ' (Icc 0 1)) (hend : γ 1 = γ 0)
    (hcurve : MapsTo γ (Icc 0 1) U) {z : ℂ} (hz : z ∈ U)
    (hne : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ z) :
    (∫ t in (0:ℝ)..1, γ' t / (γ t-z) * (F (γ t)-F z)) = 0 := by
  have hcγ : ContinuousOn γ (Icc (0:ℝ) 1) := fun t ht =>
    (hγ t ht).continuousAt.continuousWithinAt
  have hm : MapsTo (fun p : ℝ × ℝ => z+(p.2:ℂ)*(γ p.1-z))
      (Icc 0 1 ×ˢ Icc 0 1) U := by
    intro p hp
    simpa only [Complex.real_smul] using hU.add_smul_sub_mem hz (hcurve hp.1) hp.2
  have hpath : ContinuousOn (fun p : ℝ × ℝ => z+(p.2:ℂ)*(γ p.1-z))
      (Icc 0 1 ×ˢ Icc 0 1) := by
    exact continuousOn_const.add
      ((continuous_ofReal.continuousOn.comp continuousOn_snd (fun _ hp => hp.2)).mul
        ((hcγ.comp continuousOn_fst (fun _ hp => hp.1)).sub continuousOn_const))
  have hc : ContinuousOn
      (fun p : ℝ × ℝ => γ' p.1 * deriv F (z+(p.2:ℂ)*(γ p.1-z)))
      (Icc 0 1 ×ˢ Icc 0 1) :=
    (hγ'.comp continuousOn_fst (fun _ hp => hp.1)).mul
      (hF.deriv.continuousOn.comp hpath hm)
  have hinner : ∀ r ∈ Icc (0:ℝ) 1,
      (∫ t in (0:ℝ)..1, γ' t * deriv F (z+(r:ℂ)*(γ t-z))) = 0 := by
    intro r hr
    have hct : ContinuousOn (fun t => γ' t * deriv F (z+(r:ℂ)*(γ t-z))) (Icc 0 1) :=
      hc.comp (continuousOn_id.prodMk continuousOn_const) (fun t ht => ⟨ht,hr⟩)
    by_cases hr0 : r = 0
    · subst r
      simp only [ofReal_zero, zero_mul, add_zero]
      rw [intervalIntegral.integral_mul_const]
      have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
        (fun t ht => hγ t (by simpa using ht)) (show ContinuousOn _ (uIcc (0:ℝ) 1) by simpa using hγ').intervalIntegrable
      rw [hi,hend,sub_self,zero_mul]
    · have hd : ∀ t ∈ Icc (0:ℝ) 1,
          HasDerivAt (fun t => F (z+(r:ℂ)*(γ t-z)))
            ((r:ℂ)*(γ' t*deriv F (z+(r:ℂ)*(γ t-z)))) t := by
        intro t ht
        have hi : HasDerivAt (fun t => z+(r:ℂ)*(γ t-z)) ((r:ℂ)*γ' t) t :=
          (((hγ t ht).sub_const z).const_mul (r:ℂ)).const_add z
        have he := ((hF (z+(r:ℂ)*(γ t-z)) (hm (x := (t,r)) ⟨ht,hr⟩)).differentiableAt.hasDerivAt).comp t hi
        simpa only [Function.comp_def, mul_left_comm, mul_comm, mul_assoc] using he
      have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
        (fun t ht => hd t (by simpa using ht))
        (show ContinuousOn (fun t => (r:ℂ)*(γ' t*deriv F (z+(r:ℂ)*(γ t-z)))) (uIcc (0:ℝ) 1) by
          simpa using continuousOn_const.fun_mul hct).intervalIntegrable
      rw [intervalIntegral.integral_const_mul,hend,sub_self] at hi
      exact (mul_eq_zero.mp hi).resolve_left (ofReal_ne_zero.mpr hr0)
  calc
    _ = ∫ t in (0:ℝ)..1, ∫ r in (0:ℝ)..1,
        γ' t * deriv F (z+(r:ℂ)*(γ t-z)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (0:ℝ) 1 := by simpa using ht
      change γ' t / (γ t-z) * (F (γ t)-F z) = _
      rw [← analytic_segment_integral hU hF hz (hcurve ht'),
        ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r hr
      field_simp [sub_ne_zero.mpr (hne t ht')]
    _ = ∫ r in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
        γ' t * deriv F (z+(r:ℂ)*(γ t-z)) := interval_integral_swap_continuous hc
    _ = ∫ r in (0:ℝ)..1, (0:ℂ) := by
      apply intervalIntegral.integral_congr
      intro r hr
      exact hinner r (by simpa using hr)
    _ = 0 := intervalIntegral.integral_zero

theorem convex_closed_curve_cauchy {U : Set ℂ} (hU : Convex ℝ U)
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U)
    {γ γ' : ℝ → ℂ} (hγ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt γ (γ' t) t)
    (hγ' : ContinuousOn γ' (Icc 0 1)) (hend : γ 1 = γ 0)
    (hcurve : MapsTo γ (Icc 0 1) U) {z : ℂ} (hz : z ∈ U)
    (hne : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ z) :
    (∫ t in (0:ℝ)..1, γ' t / (γ t-z) * F (γ t)) =
      (∫ t in (0:ℝ)..1, γ' t / (γ t-z)) * F z := by
  have hcγ : ContinuousOn γ (Icc (0:ℝ) 1) := fun t ht =>
    (hγ t ht).continuousAt.continuousWithinAt
  have hquot : ContinuousOn (fun t => γ' t / (γ t-z)) (Icc (0:ℝ) 1) :=
    hγ'.div (hcγ.sub continuousOn_const) (fun t ht => sub_ne_zero.mpr (hne t ht))
  have h1 : IntervalIntegrable (fun t => γ' t / (γ t-z) * F (γ t)) volume 0 1 :=
    (show ContinuousOn _ (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Pi.mul_apply, Function.comp_def] using hquot.fun_mul (hF.continuousOn.comp hcγ hcurve)).intervalIntegrable
  have h2 : IntervalIntegrable (fun t => γ' t / (γ t-z) * F z) volume 0 1 :=
    (show ContinuousOn _ (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Pi.mul_apply] using hquot.fun_mul (continuousOn_const (c := F z))).intervalIntegrable
  have he := convex_closed_curve_remainder hU hF hγ hγ' hend hcurve hz hne
  simp_rw [mul_sub] at he
  rw [intervalIntegral.integral_sub h1 h2,
    intervalIntegral.integral_mul_const] at he
  exact sub_eq_zero.mp he

end

open MeasureTheory Set Complex Metric
open scoped Topology
section

lemma reciprocalResolventDenom_ne_zero {a b : ℂ} {h : ℂ → ℂ} {z : ℂ}
    (ha : a ≠ 0) (hz : ∀ t : ℂ, 1 ≤ ‖t‖ → exteriorMap a b h t ≠ z)
    {s : ℂ} (hs : s ∈ closedBall 0 1) :
    reciprocalResolventDenom a b h z s ≠ 0 := by
  by_cases hs0 : s = 0
  · subst s; simpa [reciprocalResolventDenom] using ha
  have hsi : 1 ≤ ‖s⁻¹‖ := by
    rw [norm_inv]
    exact (one_le_inv₀ (norm_pos_iff.mpr hs0)).mpr (by simpa using hs)
  have he : reciprocalResolventDenom a b h z s = s*(exteriorMap a b h s⁻¹-z) := by
    simp only [reciprocalResolventDenom, exteriorMap, inv_inv]
    field_simp
    ring
  rw [he]
  exact mul_ne_zero hs0 (sub_ne_zero.mpr (hz _ hsi))

lemma reciprocalResolvent_analytic {a b : ℂ} {h : ℂ → ℂ} {z : ℂ}
    (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (closedBall 0 1))
    (hz : ∀ t : ℂ, 1 ≤ ‖t‖ → exteriorMap a b h t ≠ z) :
    AnalyticOnNhd ℂ (reciprocalResolvent a b h z) (closedBall 0 1) := by
  intro s hs
  exact (analyticAt_const.sub ((analyticAt_id.pow 2).mul (hh.deriv s hs))).div
    (analyticAt_const.add (analyticAt_id.mul ((analyticAt_const.add (hh s hs)).sub
      analyticAt_const))) (reciprocalResolventDenom_ne_zero ha hz hs)

lemma reciprocalResolvent_eq {a b : ℂ} {h : ℂ → ℂ} {z t : ℂ}
    (ht : t ≠ 0) (hh : DifferentiableAt ℂ h t⁻¹) :
    reciprocalResolvent a b h z t⁻¹ =
      t*deriv (exteriorMap a b h) t / (exteriorMap a b h t-z) := by
  rw [(hasDerivAt_exteriorMap ht hh).deriv]
  simp only [reciprocalResolvent, reciprocalResolventDenom, exteriorMap]
  have he : a+t⁻¹*(b+h t⁻¹-z) = t⁻¹*(a*t+b+h t⁻¹-z) := by
    field_simp; ring
  rw [he, div_mul_eq_div_div, div_inv_eq_mul]
  congr 1
  field_simp

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_10
theorem exterior_cauchy_kernel_integral {a b : ℂ} {h : ℂ → ℂ} {z : ℂ}
    (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (closedBall 0 1))
    (hz : ∀ t : ℂ, 1 ≤ ‖t‖ → exteriorMap a b h t ≠ z) :
    (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv (exteriorMap a b h) (t.toCircle : ℂ) /
        (exteriorMap a b h (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1 := by
  calc
    _ = ∫ t : UnitAddCircle, reciprocalResolvent a b h z (t.toCircle : ℂ)⁻¹
        ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with t
      apply (reciprocalResolvent_eq (Circle.coe_ne_zero _)
        (hh _ (by simp [mem_closedBall, dist_eq_norm, Circle.norm_coe])).differentiableAt).symm
    _ = reciprocalResolvent a b h z 0 :=
      integral_reciprocal_analytic (reciprocalResolvent_analytic ha hh hz)
    _ = 1 := by simp [reciprocalResolvent, reciprocalResolventDenom, ha]

lemma unitAddCircle_integral_eq_unitInterval {E : Type u_45}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E) :
    (∫ t : UnitAddCircle, f (t.toCircle : ℂ) ∂AddCircle.haarAddCircle) =
      ∫ r in (0:ℝ)..1, f (circleMap 0 1 (2*Real.pi*r)) := by
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage 1 0]
  simp only [inv_one, one_smul, zero_add]
  apply intervalIntegral.integral_congr
  intro r hr
  simp only [AddCircle.toCircle_apply_mk, Circle.coe_exp, circleMap,
    ofReal_one, one_mul, zero_add, div_one]

theorem circle_convex_cauchy {U : Set ℂ} (hU : Convex ℝ U)
    {F G : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U)
    (hG : AnalyticOnNhd ℂ G (sphere 0 1))
    (hcurve : MapsTo G (sphere 0 1) U) {z : ℂ} (hz : z ∈ U)
    (hne : ∀ t ∈ sphere (0:ℂ) 1, G t ≠ z)
    (hmass : (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ) / (G (t.toCircle : ℂ)-z)
        ∂AddCircle.haarAddCircle) = 1) :
    (∫ t : UnitAddCircle,
      ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ) / (G (t.toCircle : ℂ)-z)) *
        F (G (t.toCircle : ℂ)) ∂AddCircle.haarAddCircle) = F z := by
  let τ : ℝ → ℂ := fun r => circleMap 0 1 (2*Real.pi*r)
  let c : ℂ := (2*Real.pi:ℝ)*I
  have hc : c ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)) I_ne_zero
  have hτ (r : ℝ) : τ r ∈ sphere (0:ℂ) 1 := by
    exact circleMap_mem_sphere 0 (by norm_num) _
  have hτc : Continuous τ := by dsimp [τ]; fun_prop
  have hτd (r : ℝ) : HasDerivAt τ (c*τ r) r := by
    have he := (hasDerivAt_circleMap 0 1 (2*Real.pi*r)).scomp r
      ((hasDerivAt_id r).const_mul (2*Real.pi))
    simpa only [Function.comp_def, id_eq, mul_one, one_mul, Complex.real_smul, τ, c,
      mul_assoc, mul_left_comm, mul_comm] using he
  have hγ (r : ℝ) : HasDerivAt (fun r => G (τ r)) (c*(τ r*deriv G (τ r))) r := by
    simpa only [Function.comp_def, mul_assoc, mul_comm, mul_left_comm] using
      ((hG _ (hτ r)).differentiableAt.hasDerivAt).comp r (hτd r)
  have hγ' : ContinuousOn (fun r => c*(τ r*deriv G (τ r))) (Icc (0:ℝ) 1) := by
    exact continuousOn_const.fun_mul (hτc.continuousOn.fun_mul
      (hG.deriv.continuousOn.comp hτc.continuousOn (fun r _ => hτ r)))
  have hend : G (τ 1) = G (τ 0) := by
    congr 1
    simpa [τ] using (periodic_circleMap 0 1) 0
  have he := convex_closed_curve_cauchy hU hF (fun r _ => hγ r) hγ' hend
    (fun r _ => hcurve (hτ r)) hz (fun r _ => hne _ (hτ r))
  have h1 : (fun r => c*(τ r*deriv G (τ r)) / (G (τ r)-z) * F (G (τ r))) =
      (fun r => c*((τ r*deriv G (τ r) / (G (τ r)-z))*F (G (τ r)))) := by
    funext r; ring
  have h2 : (fun r => c*(τ r*deriv G (τ r)) / (G (τ r)-z)) =
      (fun r => c*(τ r*deriv G (τ r) / (G (τ r)-z))) := by
    funext r; ring
  rw [h1,h2,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at he
  erw [unitAddCircle_integral_eq_unitInterval (fun t : ℂ => t*deriv G t/(G t-z))] at hmass
  erw [unitAddCircle_integral_eq_unitInterval (fun t : ℂ => (t*deriv G t/(G t-z))*F (G t))]
  change (∫ r in (0:ℝ)..1, (τ r*deriv G (τ r) / (G (τ r)-z))*F (G (τ r))) = F z
  change (∫ r in (0:ℝ)..1, τ r*deriv G (τ r) / (G (τ r)-z)) = 1 at hmass
  rw [hmass,mul_one] at he
  exact mul_left_cancel₀ hc he

end

open Set Metric Complex MeasureTheory
open scoped Topology


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_HolomorphicEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix


universe u_61 u_62 u_63 u_64

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
section

variable {A : Type u_61} [Ring A] [Algebra ℂ A]

lemma scalarJetEval_add {f g : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) (hg : AnalyticAt ℂ g β) (N : A) (s : ℕ) :
    scalarJetEval β N s (fun z => f z + g z) =
      scalarJetEval β N s f + scalarJetEval β N s g := by
  unfold scalarJetEval
  simp only [iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt,
    add_div, add_smul, Finset.sum_add_distrib]

lemma scalarJetEval_const {N : A} {s : ℕ} (hs : N^s = 0) (β c : ℂ) :
    scalarJetEval β N s (fun _ => c) = algebraMap ℂ A c := by
  simpa using scalarJetEval_polynomial hs β (C c)

lemma scalarJetEval_pow {f : ℂ → ℂ} {β : ℂ} (hf : AnalyticAt ℂ f β)
    {N : A} {s : ℕ} (hs : N^s = 0) (k : ℕ) :
    scalarJetEval β N s (fun z => f z ^ k) = (scalarJetEval β N s f) ^ k := by
  induction k with
  | zero => simpa using scalarJetEval_const hs β 1
  | succ k ih =>
    simp only [pow_succ]
    rw [scalarJetEval_mul (hf.fun_pow k) hf hs, ih]

lemma scalarJetEval_polynomial_comp {f : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) {N : A} {s : ℕ} (hs : N^s = 0) (p : ℂ[X]) :
    scalarJetEval β N s (fun z => p.eval (f z)) =
      Polynomial.aeval (scalarJetEval β N s f) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add, map_add]
    rw [scalarJetEval_add ((AnalyticOnNhd.eval_polynomial p (f β) (Set.mem_univ _)).fun_comp hf) ((AnalyticOnNhd.eval_polynomial q (f β) (Set.mem_univ _)).fun_comp hf), hp, hq]
  | monomial k c =>
    simp only [Polynomial.eval_monomial, Polynomial.aeval_monomial]
    rw [scalarJetEval_mul (analyticAt_const ..) (hf.fun_pow k) hs,
      scalarJetEval_const hs, scalarJetEval_pow hf hs]

lemma analytic_first_order_remainder {f : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R β ∧ ∀ᶠ z in nhds β,
      f z - f β = (z-β)*R z := by
  obtain ⟨R, hR, he⟩ := analytic_taylor_remainder hf 1
  refine ⟨R, hR, ?_⟩
  filter_upwards [he] with z hz
  simpa [jetPolynomial_eval, sub_eq_iff_eq_add, add_comm] using hz

lemma scalarJetEval_nilpotent_part {f : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) {N : A} {s : ℕ} (hs : N^s = 0) :
    (scalarJetEval β N s f - algebraMap ℂ A (f β)) ^ s = 0 := by
  obtain ⟨R, hR, he⟩ := analytic_first_order_remainder hf
  have hzero : scalarJetEval β N s (fun z => (f z - f β)^s) =
      scalarJetEval β N s (fun _ => (0 : ℂ)) := by
    apply scalarJetEval_eq_of_remainder (by fun_prop) (analyticAt_const ..) (hR.fun_pow s)
    filter_upwards [he] with z hz
    rw [sub_zero, hz, mul_pow]
  rw [scalarJetEval_pow (by fun_prop) hs,
    scalarJetEval_sub hf (analyticAt_const ..), scalarJetEval_const hs,
    scalarJetEval_const hs, map_zero] at hzero
  exact hzero

lemma scalarJetEval_comp {f g : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) (hg : AnalyticAt ℂ g (f β))
    {N : A} {s : ℕ} (hs : N^s = 0) :
    scalarJetEval β N s (fun z => g (f z)) =
      scalarJetEval (f β) (scalarJetEval β N s f - algebraMap ℂ A (f β)) s g := by
  let p := jetPolynomial (f β) s g
  obtain ⟨R, hR, he⟩ := analytic_taylor_remainder hg s
  obtain ⟨S, hS, hj⟩ := analytic_first_order_remainder hf
  have hRp : AnalyticAt ℂ (fun z => S z ^ s * R (f z)) β :=
    (hS.fun_pow s).fun_mul (hR.fun_comp hf)
  have hpoly : scalarJetEval β N s (fun z => g (f z)) =
      scalarJetEval β N s (fun z => p.eval (f z)) := by
    apply scalarJetEval_eq_of_remainder (hg.fun_comp hf) ((AnalyticOnNhd.eval_polynomial p (f β) (Set.mem_univ _)).fun_comp hf) hRp
    filter_upwards [hf.continuousAt.eventually he, hj] with z hz hw
    change g (f z) = p.eval (f z) + (f z-f β)^s * R (f z) at hz
    rw [hz, hw, mul_pow]
    ring
  rw [hpoly, scalarJetEval_polynomial_comp hf hs,
    scalarJetEval_taylor hg (scalarJetEval_nilpotent_part hf hs), sub_add_cancel]

end

open Module Set
open scoped DirectSum
variable {V : Type u_63} [AddCommGroup V] [Module ℂ V] [instFiniteDimensionalℂV : FiniteDimensional ℂ V]

lemma scalarJetEval_intertwine
    {V : Type u_63} [AddCommGroup V] [_root_.Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type u_64} [AddCommGroup W] [Module ℂ W]
    (L : W →ₗ[ℂ] V) (S : Module.End ℂ W) (T : Module.End ℂ V)
    (h : ∀ x, T (L x) = L (S x)) (β : ℂ) (s : ℕ) (f : ℂ → ℂ) (x : W) :
    scalarJetEval β T s f (L x) = L (scalarJetEval β S s f x) := by
  have hp (k : ℕ) (x : W) : (T^k) (L x) = L ((S^k) x) := by
    induction k generalizing x with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, h,
        pow_succ', Module.End.mul_apply]
  simp only [scalarJetEval, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, hp]

lemma primaryEval_on_generalized (T : Module.End ℂ V) (f : ℂ → ℂ)
    (β : ℂ) (x : T.maxGenEigenspace β) :
    primaryEval T f (x : V) =
      scalarJetEval β (T - algebraMap ℂ (Module.End ℂ V) β) (finrank ℂ V) f (x : V) := by
  rw [primaryEval_coe]
  exact (scalarJetEval_intertwine (T.maxGenEigenspace β).subtype
    (primaryNilpotent T β) (T - algebraMap ℂ (Module.End ℂ V) β)
    (fun _ => rfl) β (finrank ℂ V) f x).symm

lemma primaryEval_mapsTo_generalized (T : Module.End ℂ V) {f : ℂ → ℂ}
    (β : ℂ) (hf : AnalyticAt ℂ f β) :
    MapsTo (T.maxGenEigenspace β).subtype Set.univ
      ((primaryEval T f).maxGenEigenspace (f β)) := by
  intro x _
  change (x : V) ∈ (primaryEval T f).maxGenEigenspace (f β)
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
    Module.End.mem_genEigenspace_nat, LinearMap.mem_ker]
  have hp (k : ℕ) (x : T.maxGenEigenspace β) :
      ((primaryEval T f - algebraMap ℂ (Module.End ℂ V) (f β))^k) (x : V) =
        (((scalarJetEval β (primaryNilpotent T β) (finrank ℂ V) f -
          algebraMap ℂ (Module.End ℂ (T.maxGenEigenspace β)) (f β))^k) x : V) := by
    induction k generalizing x with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, LinearMap.sub_apply,
        primaryEval_coe, pow_succ', Module.End.mul_apply]
      rfl
  have he := hp (finrank ℂ V) x
  rw [scalarJetEval_nilpotent_part hf (primaryNilpotent_pow T β)] at he
  simpa only [Algebra.algebraMap_eq_smul_one,
    LinearMap.zero_apply, Submodule.coe_zero] using he

lemma primaryEval_comp (T : Module.End ℂ V) {f g : ℂ → ℂ}
    (hf : ∀ β ∈ spectrum ℂ T, AnalyticAt ℂ f β)
    (hg : ∀ β ∈ spectrum ℂ T, AnalyticAt ℂ g (f β)) :
    primaryEval T (fun z => g (f z)) = primaryEval (primaryEval T f) g := by
  apply primary_end_ext (T := T)
  intro β x
  by_cases hβ : β ∈ spectrum ℂ T
  · have hx : (x : V) ∈ (primaryEval T f).maxGenEigenspace (f β) :=
      primaryEval_mapsTo_generalized T β (hf β hβ) (by trivial : x ∈ Set.univ)
    rw [primaryEval_coe, primaryEval_on_generalized (primaryEval T f) g (f β) ⟨x, hx⟩]
    rw [scalarJetEval_comp (hf β hβ) (hg β hβ) (primaryNilpotent_pow T β)]
    symm
    apply scalarJetEval_intertwine (T.maxGenEigenspace β).subtype
    intro y
    change primaryEval T f (y : V) - (f β) • (y : V) = _
    rw [primaryEval_coe]
    rfl
  · have hspace : T.maxGenEigenspace β = ⊥ := by
      by_contra hn
      have he : T.HasGenEigenvalue β (finrank ℂ V) := by
        rwa [T.maxGenEigenspace_eq_genEigenspace_finrank β] at hn
      exact hβ (Module.End.hasEigenvalue_of_hasGenEigenvalue he).mem_spectrum
    have hx : x = 0 := by
      apply Subtype.ext
      simpa [hspace] using x.property
    simp [hx]

lemma primaryEval_intertwine (S T L : Module.End ℂ V)
    (h : ∀ x, T (L x) = L (S x)) (f : ℂ → ℂ) :
    primaryEval T f * L = L * primaryEval S f := by
  apply primary_end_ext (T := S)
  intro β x
  have hsub (y : V) :
      (T - algebraMap ℂ (Module.End ℂ V) β) (L y) =
        L ((S - algebraMap ℂ (Module.End ℂ V) β) y) := by
    simp only [LinearMap.sub_apply, algebraMap_end_apply, map_sub, map_smul, h]
  have hp (k : ℕ) (y : V) :
      ((T - algebraMap ℂ (Module.End ℂ V) β)^k) (L y) =
        L (((S - algebraMap ℂ (Module.End ℂ V) β)^k) y) := by
    induction k generalizing y with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, hsub, pow_succ', Module.End.mul_apply]
  have hx : L (x : V) ∈ T.maxGenEigenspace β := by
    have he := x.property
    simp only [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
      Module.End.mem_genEigenspace_nat, LinearMap.mem_ker] at he ⊢
    simpa only [Algebra.algebraMap_eq_smul_one, he, map_zero] using hp (finrank ℂ V) x
  change primaryEval T f (L x) = L (primaryEval S f x)
  rw [primaryEval_on_generalized T f β ⟨L x, hx⟩, primaryEval_on_generalized S f β x]
  exact scalarJetEval_intertwine L _ _ hsub β (finrank ℂ V) f x


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DiskCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_65 u_66 u_67 u_68 u_69 u_70 u_71 u_72 u_73 u_74 u_75 u_76 u_77 u_78 u_79 u_80

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset

section
open Filter Topology Set Module
variable {n : Type u_67} [Fintype n] [DecidableEq n]

lemma matrixAnalyticEval_polynomial (A : Matrix n n ℂ) (p : ℂ[X]) :
    matrixAnalyticEval A (fun z => p.eval z) = Polynomial.aeval A p := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, AlgEquiv.apply_symm_apply, primaryEval_polynomial,
    Polynomial.aeval_algHom_apply]

end

open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

open MeasureTheory
variable {n : Type u_73} [instFintypeN : Fintype n] [instDecidableEqN : DecidableEq n]

open scoped Kronecker

variable {m : Type u_74} [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

lemma contraction_block_iff (C : Matrix m m ℂ) :
    (Matrix.fromBlocks 1 C Cᴴ 1).PosSemidef ↔ ‖C‖ ≤ 1 := by
  let : Invertible (1 : Matrix m m ℂ) := invertibleOne
  rw [Matrix.PosDef.fromBlocks₁₁ C (1 : Matrix m m ℂ) Matrix.PosDef.one]
  simp only [inv_one, Matrix.mul_one]
  change Cᴴ*C ≤ 1 ↔ ‖C‖ ≤ 1
  rw [← CStarAlgebra.norm_le_one_iff_of_nonneg (Cᴴ*C)
    (Matrix.posSemidef_conjTranspose_mul_self C).nonneg,
    Matrix.l2_opNorm_conjTranspose_mul_self]
  constructor <;> intro h <;> nlinarith [norm_nonneg C]

lemma positive_density_block
    {n : Type u_73} [Fintype n] [DecidableEq n] {m : Type u_74} [Fintype m] [DecidableEq m]
    {L : Matrix n n ℂ} (hL : L.PosSemidef)
    {F : Matrix m m ℂ} (hF : ‖F‖ ≤ 1) :
    (Matrix.fromBlocks (L ⊗ₖ 1) (L ⊗ₖ F) (L ⊗ₖ F)ᴴ (L ⊗ₖ 1)).PosSemidef := by
  have h := (hL.kronecker ((contraction_block_iff F).mpr hF)).submatrix
    (Equiv.prodSumDistrib n m m).symm
  have he : Matrix.fromBlocks (L ⊗ₖ 1) (L ⊗ₖ F) (L ⊗ₖ F)ᴴ (L ⊗ₖ 1) =
      (L ⊗ₖ Matrix.fromBlocks 1 F Fᴴ 1).submatrix
        (Equiv.prodSumDistrib n m m).symm (Equiv.prodSumDistrib n m m).symm := by
    rw [Matrix.conjTranspose_kronecker, hL.isHermitian.eq]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> rfl
  rwa [he]

lemma matrix_integral_entry {X : Type u_75} [MeasurableSpace X] {μ : Measure X}
    {L : X → Matrix n n ℂ} (hL : Integrable L μ) (i j : n) :
    (∫ t, L t ∂μ) i j = ∫ t, L t i j ∂μ :=
  ((entryCLM i j).integral_comp_comm hL).symm

lemma integral_kron_const {X : Type u_76} [MeasurableSpace X] {μ : Measure X}
    {L : X → Matrix n n ℂ} (hL : Integrable L μ) (B : Matrix m m ℂ) :
    (∫ t, L t ⊗ₖ B ∂μ) = (∫ t, L t ∂μ) ⊗ₖ B :=
  (kronCLM B).integral_comp_comm hL

lemma integral_fromBlocks {X : Type u_77} [MeasurableSpace X] {μ : Measure X}
    {A B C D : X → Matrix n n ℂ}
    (hA : Integrable A μ) (hB : Integrable B μ) (hC : Integrable C μ) (hD : Integrable D μ) :
    (∫ t, Matrix.fromBlocks (A t) (B t) (C t) (D t) ∂μ) =
      Matrix.fromBlocks (∫ t, A t ∂μ) (∫ t, B t ∂μ) (∫ t, C t ∂μ) (∫ t, D t ∂μ) := by
  let e : (Matrix n n ℂ × Matrix n n ℂ × Matrix n n ℂ × Matrix n n ℂ) →L[ℂ]
      Matrix (n⊕n) (n⊕n) ℂ :=
    (show (Matrix n n ℂ × Matrix n n ℂ × Matrix n n ℂ × Matrix n n ℂ) →ₗ[ℂ]
      Matrix (n⊕n) (n⊕n) ℂ from
      { toFun := fun X => Matrix.fromBlocks X.1 X.2.1 X.2.2.1 X.2.2.2
        map_add' := fun X Y => by ext i j; rcases i with i | i <;> rcases j with j | j <;> rfl
        map_smul' := fun c X => by ext i j; rcases i with i | i <;> rcases j with j | j <;> rfl
      }).toContinuousLinearMap
  have h := e.integral_comp_comm (hA.prodMk (hB.prodMk (hC.prodMk hD)))
  change (∫ t, Matrix.fromBlocks (A t) (B t) (C t) (D t) ∂μ) =
    Matrix.fromBlocks (∫ t, (A t, B t, C t, D t) ∂μ).1
      (∫ t, (A t, B t, C t, D t) ∂μ).2.1
      (∫ t, (A t, B t, C t, D t) ∂μ).2.2.1
      (∫ t, (A t, B t, C t, D t) ∂μ).2.2.2 at h
  simpa only [integral_pair hA (hB.prodMk (hC.prodMk hD)),
    integral_pair hB (hC.prodMk hD), integral_pair hC hD] using h

lemma integral_conjTranspose {X : Type u_78} [MeasurableSpace X] {μ : Measure X}
    {L : X → Matrix n n ℂ} (hL : Integrable L μ) :
    (∫ t, (L t)ᴴ ∂μ) = (∫ t, L t ∂μ)ᴴ :=
  conjTransposeRCLM.integral_comp_comm hL

theorem norm_integral_density_kron {X : Type u_79} [MeasurableSpace X] {μ : Measure X}
    {L : X → Matrix n n ℂ} {F : X → Matrix m m ℂ}
    (hL : Integrable L μ) (hLF : Integrable (fun t => L t ⊗ₖ F t) μ)
    (hpos : ∀ t, (L t).PosSemidef) (hmass : ∫ t, L t ∂μ = 1)
    (hF : ∀ t, ‖F t‖ ≤ 1) : ‖∫ t, L t ⊗ₖ F t ∂μ‖ ≤ 1 := by
  have hd (t : X) := positive_density_block (hpos t) (hF t)
  have hnonneg : 0 ≤ ∫ t, Matrix.fromBlocks (L t ⊗ₖ 1) (L t ⊗ₖ F t)
      (L t ⊗ₖ F t)ᴴ (L t ⊗ₖ 1) ∂μ :=
    integral_nonneg (fun t => (hd t).nonneg)
  have hdiag : Integrable (fun t => L t ⊗ₖ (1 : Matrix m m ℂ)) μ :=
    (kronCLM (1 : Matrix m m ℂ)).integrable_comp hL
  have hstar : Integrable (fun t => (L t ⊗ₖ F t)ᴴ) μ :=
    conjTransposeRCLM.integrable_comp hLF
  rw [integral_fromBlocks hdiag hLF hstar hdiag, integral_kron_const hL,
    hmass, Matrix.one_kronecker_one, integral_conjTranspose hLF] at hnonneg
  exact (contraction_block_iff _).mp (Matrix.nonneg_iff_posSemidef.mp hnonneg)

lemma continuous_kron
    {n : Type u_73} [Fintype n] [DecidableEq n] {m : Type u_74} [Fintype m] [DecidableEq m]
    {X : Type u_80} [TopologicalSpace X]
    {L : X → Matrix n n ℂ} {F : X → Matrix m m ℂ}
    (hL : Continuous L) (hF : Continuous F) : Continuous (fun t => L t ⊗ₖ F t) := by
  apply continuous_matrix
  intro i j
  exact ((entryCLM i.1 j.1).continuous.comp hL).mul
    ((entryCLM i.2 j.2).continuous.comp hF)


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_CompleteResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_81 u_82 u_83 u_84 u_85 u_86 u_87 u_88 u_89 u_90

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

section
open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker

variable {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

lemma matrixAnalyticEval_id (D : Matrix n n ℂ) :
    matrixAnalyticEval D (fun z => z) = D := by
  simpa using matrixAnalyticEval_polynomial D (Polynomial.X : ℂ[X])

lemma completeAnalyticEval_const
    {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) (C : Matrix m m ℂ) :
    completeAnalyticEval D (fun _ => C) = (1 : Matrix n n ℂ) ⊗ₖ C := by
  ext i j
  simp only [completeAnalyticEval, matrixAnalyticEval_const, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply]
  ring

end

open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_89} {m : Type u_90} [Fintype n] [DecidableEq n] [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

lemma completeAnalyticEval_eqOn
    {n : Type u_89} {m : Type u_90} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) {F G : ℂ → Matrix m m ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hDU : spectrum ℂ D ⊆ U) (he : EqOn F G U) :
    completeAnalyticEval D F = completeAnalyticEval D G := by
  ext i j
  unfold completeAnalyticEval
  apply congrArg (fun M : Matrix n n ℂ => M i.1 j.1)
  apply matrixAnalyticEval_eventuallyEq
  intro z hz
  filter_upwards [hU.mem_nhds (hDU hz)] with w hw
  rw [he hw]

lemma matrix_entry_analytic {f : ℂ → Matrix m m ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (i j : m) : AnalyticAt ℂ (fun w => f w i j) z := by
  let L : Matrix m m ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => M i j, map_add' := by intros; rfl, map_smul' := by intros; rfl }
  exact (L.toContinuousLinearMap.analyticAt (f z)).comp hf


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_PolynomialCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_91 u_92 u_93 u_94 u_95 u_96 u_97 u_98 u_99 u_100 u_101 u_102 u_103 u_104 u_105 u_106 u_107

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

section
open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_96} {m : Type u_97} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma matrixAnalyticEval_comp (A : Matrix n n ℂ) {f g : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ g (f z)) :
    matrixAnalyticEval A (fun z => g (f z)) = matrixAnalyticEval (matrixAnalyticEval A f) g := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, AlgEquiv.apply_symm_apply]
  exact primaryEval_comp _ (fun z hz => hf z (by simpa using hz))
    (fun z hz => hg z (by simpa using hz))

lemma completeAnalyticEval_comp
    {n : Type u_96} {m : Type u_97} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (A : Matrix n n ℂ) {f : ℂ → ℂ} {F : ℂ → Matrix m m ℂ}
    (hf : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ f z)
    (hF : ∀ i j, ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ (fun w => F w i j) (f z)) :
    completeAnalyticEval A (fun z => F (f z)) = completeAnalyticEval (matrixAnalyticEval A f) F := by
  ext i j
  simp only [completeAnalyticEval]
  rw [matrixAnalyticEval_comp A hf (hF _ _)]

lemma matrixAnalyticEval_intertwine (A B L : Matrix n n ℂ) (hL : A*L=L*B) (f : ℂ → ℂ) :
    matrixAnalyticEval A f * L = L * matrixAnalyticEval B f := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [map_mul, matrixAnalyticEval, AlgEquiv.apply_symm_apply]
  apply primaryEval_intertwine
  intro x
  have he := congrArg (Matrix.toLinAlgEquiv' : Matrix n n ℂ ≃ₐ[ℂ] Module.End ℂ (n → ℂ)) hL
  simp only [map_mul] at he
  exact LinearMap.congr_fun he x

lemma matrixAnalyticEval_similarity {S : Matrix n n ℂ} (hS : IsUnit S)
    (A : Matrix n n ℂ) (f : ℂ → ℂ) :
    matrixAnalyticEval (S*A*S⁻¹) f = S*matrixAnalyticEval A f*S⁻¹ := by
  have hi : S⁻¹*S=1 := Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  have hi' : S*S⁻¹=1 := Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  have he := matrixAnalyticEval_intertwine (S*A*S⁻¹) A S (by rw [mul_assoc, mul_assoc, hi, mul_one]) f
  have h := congrArg (fun M => M*S⁻¹) he
  simpa only [mul_assoc, hi', mul_one] using h

lemma completeAnalyticEval_similarity {S : Matrix n n ℂ} (hS : IsUnit S)
    (A : Matrix n n ℂ) (F : ℂ → Matrix m m ℂ) :
    completeAnalyticEval (S*A*S⁻¹) F = (S ⊗ₖ (1 : Matrix m m ℂ)) *
      completeAnalyticEval A F * (S⁻¹ ⊗ₖ (1 : Matrix m m ℂ)) := by
  ext i j
  simp only [completeAnalyticEval, matrixAnalyticEval_similarity hS, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ite_mul, zero_mul, Finset.sum_ite_eq]

end

section
open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_98} {m : Type u_99} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma baseMatrixHom_norm (A : Matrix n n ℂ) : ‖baseMatrixHom (m := m) A‖ ≤ ‖A‖ :=
  NonUnitalStarAlgHom.norm_apply_le (baseMatrixHom (m := m)) A

end

open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_CauchyEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_108 u_109 u_110 u_111 u_112 u_113 u_114 u_115

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

section IntegralJets
open MeasureTheory Set Metric Complex Filter
open scoped Topology
variable {α : Type u_108} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
  [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]

lemma cauchyJet_hasDerivAt
    {α : Type u_108} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
    (s v : α → ℂ) (k : ℕ) {z : ℂ} {t : α}
    (hn : s t ≠ z) :
    HasDerivAt (fun w => cauchyJet s v k w t) (cauchyJet s v (k+1) z t) z := by
  have he := (hasDerivAt_const z ((k.factorial : ℂ)*v t)).div
    (((hasDerivAt_id z).const_sub (s t)).pow (k+1))
    (pow_ne_zero _ (sub_ne_zero.mpr hn))
  convert he using 1 <;> try rfl
  change ((k+1).factorial : ℂ)*v t/(s t-z)^(k+1+1) = _
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp only [id_eq, zero_mul, mul_neg_one, zero_sub]
  simp only [Pi.pow_apply, Nat.add_sub_cancel, pow_succ]
  field_simp

lemma cauchyJet_continuousOn
    {α : Type u_108} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
    {s v : α → ℂ} (hs : Continuous s) (hv : Continuous v)
    {U : Set ℂ} (hne : ∀ z ∈ U, ∀ t, s t ≠ z) (k : ℕ) :
    ContinuousOn (Function.uncurry (cauchyJet s v k)) (U ×ˢ univ) := by
  exact (continuous_const.mul (hv.comp continuous_snd)).continuousOn.div
    (((hs.comp continuous_snd).continuousOn.sub continuousOn_fst).pow (k+1))
    (fun p hp => pow_ne_zero _ (sub_ne_zero.mpr (hne p.1 hp.1 p.2)))

lemma cauchyJet_integrable {s v : α → ℂ} (hs : Continuous s) (hv : Continuous v)
    {z : ℂ} (hne : ∀ t, s t ≠ z) (k : ℕ) :
    Integrable (cauchyJet s v k z) μ := by
  exact ((continuous_const.mul hv).div ((hs.sub continuous_const).pow (k+1))
    (fun t => pow_ne_zero _ (sub_ne_zero.mpr (hne t)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma iteratedDeriv_cauchyIntegral {s v : α → ℂ} (hs : Continuous s) (hv : Continuous v)
    {U : Set ℂ} (hU : IsOpen U) (hne : ∀ z ∈ U, ∀ t, s t ≠ z) (k : ℕ)
    {z : ℂ} (hz : z ∈ U) :
    iteratedDeriv k (fun w => ∫ t, v t/(s t-w) ∂μ) z = ∫ t, cauchyJet s v k z t ∂μ := by
  induction k generalizing z with
  | zero => simp [cauchyJet]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (fun w => ∫ t, v t/(s t-w) ∂μ) =ᶠ[nhds z]
        fun w => ∫ t, cauchyJet s v k w t ∂μ :=
      Filter.Eventually.mono (hU.mem_nhds hz) fun w hw => ih hw
    rw [he.deriv_eq]
    exact (compact_parametric_hasDerivAt hU (cauchyJet_continuousOn hs hv hne k)
      (cauchyJet_continuousOn hs hv hne (k+1))
      (fun w hw t => cauchyJet_hasDerivAt s v k (hne w hw t)) hz).deriv

lemma iteratedDeriv_cauchyKernel (s v : α → ℂ) (k : ℕ) {z : ℂ} {t : α}
    (hne : s t ≠ z) :
    iteratedDeriv k (fun w => v t/(s t-w)) z = cauchyJet s v k z t := by
  induction k generalizing z with
  | zero => simp [cauchyJet]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (fun w => v t/(s t-w)) =ᶠ[nhds z]
        fun w => cauchyJet s v k w t :=
      Filter.Eventually.mono (isClosed_singleton.isOpen_compl.mem_nhds (show z ∈ ({s t} : Set ℂ)ᶜ from
        fun h => hne h.symm)) fun w hw => ih (fun h => hw h.symm)
    rw [he.deriv_eq]
    exact (cauchyJet_hasDerivAt s v k hne).deriv

end IntegralJets

section
open MeasureTheory Set Filter Module
open scoped Topology Matrix.Norms.L2Operator
variable {α : Type u_109} [MeasurableSpace α] {μ : Measure α}
  {n : Type u_110} [Fintype n] [DecidableEq n]

lemma matrix_integral_mulVec {F : α → Matrix n n ℂ} (hF : Integrable F μ) (x : n → ℂ) :
    (∫ t, F t ∂μ) *ᵥ x = ∫ t, F t *ᵥ x ∂μ := by
  let L : Matrix n n ℂ →L[ℂ] (n → ℂ) :=
    (show Matrix n n ℂ →ₗ[ℂ] (n → ℂ) from
      { toFun := fun B => B *ᵥ x
        map_add' := fun B C => Matrix.add_mulVec B C x
        map_smul' := fun c B => Matrix.smul_mulVec c B x }).toContinuousLinearMap
  exact (L.integral_comp_comm hF).symm

lemma matrixAnalyticEval_integral (A : Matrix n n ℂ) {F : ℂ → α → ℂ}
    (hi : Integrable (fun t => matrixAnalyticEval A (fun z => F z t)) μ)
    (hj : ∀ β ∈ spectrum ℂ A, ∀ k < Fintype.card n,
      Integrable (fun t => iteratedDeriv k (fun z => F z t) β) μ)
    (hd : ∀ β ∈ spectrum ℂ A, ∀ k < Fintype.card n,
      iteratedDeriv k (fun z => ∫ t, F z t ∂μ) β =
        ∫ t, iteratedDeriv k (fun z => F z t) β ∂μ) :
    matrixAnalyticEval A (fun z => ∫ t, F z t ∂μ) =
      ∫ t, matrixAnalyticEval A (fun z => F z t) ∂μ := by
  apply Matrix.toLinAlgEquiv'.injective
  apply primary_end_ext_spectrum (T := Matrix.toLinAlgEquiv' A)
  intro β hβ x
  have hb : β ∈ spectrum ℂ A := by simpa only [AlgEquiv.spectrum_eq] using hβ
  have he (f : ℂ → ℂ) :
      Matrix.toLinAlgEquiv' (matrixAnalyticEval A f) (x : n → ℂ) =
        ∑ k ∈ Finset.range (Fintype.card n),
          (iteratedDeriv k f β / (k.factorial : ℂ)) •
          (((primaryNilpotent (Matrix.toLinAlgEquiv' A) β)^k) x : n → ℂ) := by
    simp only [matrixAnalyticEval, AlgEquiv.apply_symm_apply, primaryEval_coe,
      scalarJetEval, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul]
    simp
  rw [he, Matrix.toLinAlgEquiv'_apply, matrix_integral_mulVec hi]
  simp_rw [← Matrix.toLinAlgEquiv'_apply,he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [hd β hb k (Finset.mem_range.mp hk),integral_smul_const,integral_div]
  · intro k hk
    exact ((hj β hb k (Finset.mem_range.mp hk)).div_const _).smul_const _

lemma matrixAnalyticEval_resolvent (A : Matrix n n ℂ) {s : ℂ}
    (hs : s ∉ spectrum ℂ A) :
    matrixAnalyticEval A (fun z => (s-z)⁻¹) = (s • (1 : Matrix n n ℂ)-A)⁻¹ := by
  have hn (z : ℂ) (hz : z ∈ spectrum ℂ A) : s-z ≠ 0 :=
    sub_ne_zero.mpr (fun h => hs (h ▸ hz))
  have hf (z : ℂ) (_ : z ∈ spectrum ℂ A) : AnalyticAt ℂ (fun z => s-z) z :=
    analyticAt_const.sub analyticAt_id
  have hg (z : ℂ) (hz : z ∈ spectrum ℂ A) : AnalyticAt ℂ (fun z => (s-z)⁻¹) z :=
    (hf z hz).inv (hn z hz)
  have he : matrixAnalyticEval A (fun _ => 1) =
      matrixAnalyticEval A (fun z => (s-z)⁻¹*(s-z)) := by
    apply matrixAnalyticEval_eventuallyEq
    intro z hz
    filter_upwards [(hf z hz).continuousAt.eventually_ne (hn z hz)] with w hw
    exact (inv_mul_cancel₀ hw).symm
  rw [matrixAnalyticEval_const, map_one, matrixAnalyticEval_mul A hg hf,
    matrixAnalyticEval_sub A (f := fun _ => s) (g := fun z => z)
      (fun _ _ => analyticAt_const) (fun _ _ => analyticAt_id),
    matrixAnalyticEval_const,matrixAnalyticEval_id,Algebra.algebraMap_eq_smul_one] at he
  exact (Matrix.inv_eq_left_inv he.symm).symm

lemma matrixAnalyticEval_cauchyKernel (A : Matrix n n ℂ) {s : ℂ}
    (hs : s ∉ spectrum ℂ A) (v : ℂ) :
    matrixAnalyticEval A (fun z => v/(s-z)) = v • (s • (1 : Matrix n n ℂ)-A)⁻¹ := by
  have hg : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ (fun z => (s-z)⁻¹) z := by
    intro z hz
    have hn : s ≠ z := fun h => hs (h ▸ hz)
    exact (analyticAt_const.sub analyticAt_id).inv (sub_ne_zero.mpr hn)
  simp_rw [div_eq_mul_inv]
  rw [matrixAnalyticEval_mul A (fun _ _ => analyticAt_const) hg,
    matrixAnalyticEval_const,matrixAnalyticEval_resolvent A hs]
  simp only [Algebra.smul_def]

end

section
open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator
variable {α : Type u_111} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
  [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {n : Type u_112} [Fintype n] [DecidableEq n]

theorem matrix_cauchy_integral_evaluation (A : Matrix n n ℂ)
    {s v : α → ℂ} (hs : Continuous s) (hv : Continuous v)
    {U : Set ℂ} (hU : IsOpen U) (hAU : spectrum ℂ A ⊆ U)
    (hne : ∀ z ∈ U, ∀ t, s t ≠ z) :
    matrixAnalyticEval A (fun z => ∫ t, v t/(s t-z) ∂μ) =
      ∫ t, v t • (s t • (1 : Matrix n n ℂ)-A)⁻¹ ∂μ := by
  have hn (t : α) : s t ∉ spectrum ℂ A := fun h => hne _ (hAU h) t rfl
  have he (t : α) := matrixAnalyticEval_cauchyKernel A (hn t) (v t)
  have hi : Integrable (fun t => matrixAnalyticEval A (fun z => v t/(s t-z))) μ := by
    simp_rw [he]
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    apply hv.smul
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (matrix_resolvent_analytic A (hn t)).continuousAt.comp hs.continuousAt
  rw [matrixAnalyticEval_integral A hi]
  · exact integral_congr_ae (Filter.Eventually.of_forall he)
  · intro β hβ k _
    have hd : (fun t => iteratedDeriv k (fun z => v t/(s t-z)) β) = cauchyJet s v k β :=
      funext fun t => iteratedDeriv_cauchyKernel s v k (hne β (hAU hβ) t)
    rw [hd]
    exact cauchyJet_integrable hs hv (hne β (hAU hβ)) k
  · intro β hβ k _
    rw [iteratedDeriv_cauchyIntegral hs hv hU hne k (hAU hβ)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
      (iteratedDeriv_cauchyKernel s v k (hne β (hAU hβ) t)).symm)

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker
variable {α : Type u_113} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
  [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {n : Type u_114} {m : Type u_115} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem complete_cauchy_integral_evaluation (A : Matrix n n ℂ)
    {s v : α → ℂ} (hs : Continuous s) (hv : Continuous v)
    {B : α → Matrix m m ℂ} (hB : Continuous B)
    {U : Set ℂ} (hU : IsOpen U) (hAU : spectrum ℂ A ⊆ U)
    (hne : ∀ z ∈ U, ∀ t, s t ≠ z) :
    completeAnalyticEval A (fun z i j => ∫ t, v t*B t i j/(s t-z) ∂μ) =
      ∫ t, (v t • (s t • (1 : Matrix n n ℂ)-A)⁻¹) ⊗ₖ B t ∂μ := by
  have hn (t : α) : s t ∉ spectrum ℂ A := fun h => hne _ (hAU h) t rfl
  have hrc := hv.smul (matrix_resolvent_continuous A hs hn)
  have hbc (i j : m) : Continuous (fun t => B t i j) := (entryCLM i j).continuous.comp hB
  have hri : Integrable (fun t => (v t • (s t • (1 : Matrix n n ℂ)-A)⁻¹) ⊗ₖ B t) μ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    apply continuous_matrix
    intro i j
    change Continuous (fun t => (v t • (s t • (1 : Matrix n n ℂ)-A)⁻¹) i.1 j.1 * B t i.2 j.2)
    exact ((entryCLM i.1 j.1).continuous.comp hrc).mul (hbc i.2 j.2)
  ext i j
  dsimp only [completeAnalyticEval]
  have he := matrix_cauchy_integral_evaluation (μ := μ) A (s := s) (v := fun t => v t*B t i.2 j.2) hs (hv.mul (hbc i.2 j.2)) hU hAU hne
  rw [he,
    matrix_integral_entry hri]
  have ht : Integrable (fun t => (v t*B t i.2 j.2) • (s t • (1 : Matrix n n ℂ)-A)⁻¹) μ :=
    ((hv.mul (hbc i.2 j.2)).smul (matrix_resolvent_continuous A hs hn)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [matrix_integral_entry ht]
  apply integral_congr_ae
  filter_upwards [] with t
  change (v t*B t i.2 j.2) * (s t • (1 : Matrix n n ℂ)-A)⁻¹ i.1 j.1 =
    (v t*(s t • (1 : Matrix n n ℂ)-A)⁻¹ i.1 j.1)*B t i.2 j.2
  ring


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_BoundaryRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix


universe u_116 u_117 u_118 u_119 u_120 u_121 u_122 u_123 u_124 u_125 u_126 u_127 u_128 u_129 u_130 u_131 u_132 u_133 u_134 u_135 u_136 u_137 u_138 u_139 u_140 u_141 u_142 u_143 u_144 u_145 u_146 u_147 u_148 u_149 u_150 u_151 u_152 u_153

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset


open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder


open Set Filter Metric Complex
open scoped Topology ComplexConjugate

open MeasureTheory Set Complex
open scoped Topology Real

open MeasureTheory Set Complex
open scoped Topology

open MeasureTheory Set Complex Metric
open scoped Topology

section
open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_150} {m : Type u_151} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma boundaryDiskDensity_nonneg {D : Matrix n n ℂ} (hD : spectralRadius ℂ D < 1)
    (hc : Dᴴ*D ≤ 1) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ boundaryDiskDensity D z := by
  let E : Matrix n n ℂ := 1-z⁻¹ • D
  let R : Matrix n n ℂ := E⁻¹
  have hu : IsUnit E := stable_disk_inverse_isUnit hD (by simp [norm_inv, hz])
  have hER : E*R = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det E).mp hu)
  have hzz : star z⁻¹ * z⁻¹ = 1 := by
    change conj z⁻¹ * z⁻¹ = 1
    rw [RCLike.conj_mul, norm_inv, hz]
    norm_num
  have hdef : Eᴴ+E-Eᴴ*E = 1-Dᴴ*D := by
    dsimp [E]
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,Matrix.conjTranspose_smul]
    simp only [sub_mul,mul_sub,Matrix.one_mul,Matrix.mul_one,Matrix.smul_mul,Matrix.mul_smul,
      smul_smul,mul_comm z⁻¹ (star z⁻¹),hzz,one_smul]
    abel
  have hcong : Rᴴ*(1-Dᴴ*D)*R = boundaryDiskDensity D z := by
    rw [← hdef]
    have hs := congrArg Matrix.conjTranspose hER
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_one] at hs
    change Rᴴ*(Eᴴ+E-Eᴴ*E)*R = R+Rᴴ-1
    calc
      _ = (Rᴴ*Eᴴ)*R + Rᴴ*(E*R) - (Rᴴ*Eᴴ)*(E*R) := by noncomm_ring
      _ = _ := by rw [hs,hER]; simp
  rw [← hcong]
  exact (Matrix.PosSemidef.conjTranspose_mul_mul_same
    (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hc)) R).nonneg

lemma coordinate_circle_cauchy {ψ H : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hH : AnalyticOnNhd ℂ H (closedBall 0 1))
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1)
    {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) :
    (∫ t : UnitAddCircle, ((t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
      (ψ (t.toCircle : ℂ)-z))*H (ψ (t.toCircle : ℂ))
        ∂AddCircle.haarAddCircle) = H z := by
  apply circle_convex_cauchy (convex_closedBall (0:ℂ) 1) hH hψ
    (fun t ht => by simpa [mem_closedBall] using (hb t ht).le)
    (ball_subset_closedBall hz) _ (hmass z hz)
  intro t ht he
  have hh := hb t ht
  rw [he] at hh
  have hz' : ‖z‖ < 1 := by simpa using hz
  exact (ne_of_lt hz') hh

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_152} {m : Type u_153} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma coordinate_circle_cauchy_matrix {ψ : ℂ → ℂ} {J : ℂ → Matrix n n ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hJ : ∀ i j, AnalyticOnNhd ℂ (fun z => J z i j) (closedBall 0 1))
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1) :
    (∫ t : UnitAddCircle,
      ((t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ)) •
        J (ψ (t.toCircle : ℂ)) ∂AddCircle.haarAddCircle) = J 0 := by
  have ht (t : UnitAddCircle) : (t.toCircle : ℂ) ∈ sphere (0:ℂ) 1 := by simp [Circle.norm_coe]
  have hc : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)) := by fun_prop
  have hψc := hψ.continuousOn.comp_continuous hc ht
  have hψd := hψ.deriv.continuousOn.comp_continuous hc ht
  have hjc : Continuous (fun t : UnitAddCircle =>
      (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ)) :=
    (hc.mul hψd).div hψc (fun t => norm_ne_zero_iff.mp (by rw [hb _ (ht t)]; norm_num))
  have hJc : Continuous (fun t : UnitAddCircle => J (ψ (t.toCircle : ℂ))) := by
    apply continuous_matrix
    intro i j
    exact (hJ i j).continuousOn.comp_continuous hψc
      (fun t => by simpa [mem_closedBall] using (hb _ (ht t)).le)
  have hi := (hjc.smul hJc).integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  ext i j
  erw [matrix_integral_entry hi]
  convert! coordinate_circle_cauchy hψ hb (hJ i j) hmass (z := 0) (by simp) using 1
  apply integral_congr_ae
  filter_upwards [] with t
  change (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ) *
      J (ψ (t.toCircle : ℂ)) i j =
    (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/(ψ (t.toCircle : ℂ)-0) *
      J (ψ (t.toCircle : ℂ)) i j
  rw [sub_zero]

theorem complete_pulled_disk_representation {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) {ψ : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1)
    {H : ℂ → Matrix m m ℂ}
    (hH : ∀ i j, AnalyticOnNhd ℂ (fun z => H z i j) (closedBall 0 1)) :
    (∫ t : UnitAddCircle,
      (((t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ)) •
        boundaryDiskDensity D (ψ (t.toCircle : ℂ))) ⊗ₖ
          H (ψ (t.toCircle : ℂ)) ∂AddCircle.haarAddCircle) = completeAnalyticEval D H := by
  let c : UnitAddCircle → ℂ := fun t => (t.toCircle : ℂ)
  let s : UnitAddCircle → ℂ := fun t => ψ (c t)
  let v : UnitAddCircle → ℂ := fun t => c t*deriv ψ (c t)
  let j : UnitAddCircle → ℂ := fun t => v t/s t
  have ht (t : UnitAddCircle) : c t ∈ sphere (0:ℂ) 1 := by simp [c, Circle.norm_coe]
  have hc : Continuous c := by dsimp [c]; fun_prop
  have hs : Continuous s := hψ.continuousOn.comp_continuous hc ht
  have hv : Continuous v := hc.mul (hψ.deriv.continuousOn.comp_continuous hc ht)
  have hsn (t : UnitAddCircle) : s t ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [show ‖s t‖ = 1 from hb _ (ht t)]; norm_num)
  have hj : Continuous j := hv.div hs hsn
  have hsb (t : UnitAddCircle) : s t ∈ closedBall (0:ℂ) 1 := by
    simpa [mem_closedBall] using (hb _ (ht t)).le
  have hHc : Continuous (fun t => H (s t)) := by
    apply continuous_matrix
    intro a b
    exact (hH a b).continuousOn.comp_continuous hs hsb
  have hspec : spectrum ℂ D ⊆ ball (0:ℂ) 1 := fun z hz => by
    simpa using stable_spectrum_norm_lt_one hD hz
  have hne (z : ℂ) (hz : z ∈ ball (0:ℂ) 1) (t : UnitAddCircle) : s t ≠ z := by
    intro he
    have hh : ‖s t‖ = 1 := hb _ (ht t)
    rw [he] at hh
    have hz' : ‖z‖ < 1 := by simpa using hz
    exact (ne_of_lt hz') hh
  let K : UnitAddCircle → Matrix (n × m) (n × m) ℂ :=
    fun t => (v t • (s t • (1 : Matrix n n ℂ)-D)⁻¹) ⊗ₖ H (s t)
  let B : UnitAddCircle → Matrix (n × m) (n × m) ℂ :=
    fun t => j t • ((1-s t • Dᴴ)⁻¹ ⊗ₖ H (s t))
  let C : UnitAddCircle → Matrix (n × m) (n × m) ℂ :=
    fun t => j t • ((1 : Matrix n n ℂ) ⊗ₖ H (s t))
  have hKc : Continuous K := continuous_kron
    (hv.smul (matrix_resolvent_continuous D hs (fun t hz => hne _ (hspec hz) t rfl))) hHc
  have hR : AnalyticOnNhd ℂ (fun z : ℂ => (1-z • Dᴴ)⁻¹) (closedBall 0 1) := by
    intro z hz
    exact scalar_matrix_inverse_analytic (stable_star_disk_inverse_isUnit hD (by simpa using hz))
  have hBc : Continuous B := hj.smul (continuous_kron
    (hR.continuousOn.comp_continuous hs hsb) hHc)
  have hCc : Continuous C := hj.smul (continuous_kron continuous_const hHc)
  have hKi := hKc.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have hBi := hBc.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have hCi := hCc.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have hKe : (∫ t, K t ∂AddCircle.haarAddCircle) = completeAnalyticEval D H := by
    rw [← complete_cauchy_integral_evaluation D hs hv hHc isOpen_ball hspec hne]
    apply completeAnalyticEval_eqOn D isOpen_ball hspec
    intro z hz
    ext a b
    have he := coordinate_circle_cauchy hψ hb (hH a b) hmass hz
    convert he using 1
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [v,s,c]
    ring
  have hBe : (∫ t, B t ∂AddCircle.haarAddCircle) = (1 : Matrix n n ℂ) ⊗ₖ H 0 := by
    have he := coordinate_circle_cauchy_matrix hψ hb
      (J := fun z => (1-z • Dᴴ)⁻¹ ⊗ₖ H z)
      (fun a b z hz => (matrix_entry_analytic (hR z hz) a.1 b.1).mul (hH a.2 b.2 z hz)) hmass
    simpa only [B,j,v,s,c,zero_smul,sub_zero,inv_one] using he
  have hCe : (∫ t, C t ∂AddCircle.haarAddCircle) = (1 : Matrix n n ℂ) ⊗ₖ H 0 := by
    exact coordinate_circle_cauchy_matrix hψ hb
      (J := fun z => (1 : Matrix n n ℂ) ⊗ₖ H z)
      (fun a b z hz => analyticAt_const.mul (hH a.2 b.2 z hz)) hmass
  calc
    _ = ∫ t, (K t+B t-C t) ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [boundaryDiskDensity_eq hD (hb _ (ht t))]
      change (j t • (s t • (s t • (1 : Matrix n n ℂ)-D)⁻¹ +
        (1-s t • Dᴴ)⁻¹-1)) ⊗ₖ H (s t) = K t+B t-C t
      dsimp [K,B,C,j]
      ext ⟨a₁,a₂⟩ ⟨b₁,b₂⟩
      simp only [Matrix.kronecker_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.add_apply, Matrix.sub_apply]
      field_simp [hsn t]
    _ = completeAnalyticEval D H := by
      erw [integral_sub (hKi.add hBi) hCi, integral_add hKi hBi, hKe,hBe,hCe]
      abel


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_PulledDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_154 u_155 u_156

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Complex
open scoped Topology
open MeasureTheory Set Complex Metric
open scoped Topology

section
open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_154} [Fintype n] [DecidableEq n]

lemma pulledDiskDensity_nonneg {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) (hDc : Dᴴ*D ≤ 1) {ψ : ℂ → ℂ}
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hj : ∀ t ∈ sphere (0:ℂ) 1, 0 ≤ t*deriv ψ t/ψ t) (t : UnitAddCircle) :
    0 ≤ pulledDiskDensity D ψ t := by
  have ht : (t.toCircle : ℂ) ∈ sphere (0:ℂ) 1 := by simp [Circle.norm_coe]
  exact ((Matrix.nonneg_iff_posSemidef.mp (boundaryDiskDensity_nonneg hD hDc (hb _ ht))).smul
    (hj _ ht)).nonneg

theorem pulledDiskDensity_mass {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) {ψ : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1) :
    (∫ t : UnitAddCircle, pulledDiskDensity D ψ t ∂AddCircle.haarAddCircle) = 1 := by
  have he := complete_pulled_disk_representation (m := Unit) hD hψ hb hmass
    (H := fun _ => (1 : Matrix Unit Unit ℂ)) (fun _ _ _ _ => analyticAt_const)
  rw [completeAnalyticEval_const] at he
  have hc := pulledDiskDensity_continuous hD hψ hb
  have hi := hc.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle)
    (HasCompactSupport.of_compactSpace _)
  have hkc : Continuous (fun t : UnitAddCircle =>
      (pulledDiskDensity D ψ t) ⊗ₖ (1 : Matrix Unit Unit ℂ)) :=
    continuous_kron hc continuous_const
  have hki := hkc.integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  change (∫ t : UnitAddCircle, (pulledDiskDensity D ψ t) ⊗ₖ (1 : Matrix Unit Unit ℂ)
    ∂AddCircle.haarAddCircle) = (1 : Matrix n n ℂ) ⊗ₖ (1 : Matrix Unit Unit ℂ) at he
  ext i j
  have hh := congrArg (fun M : Matrix (n × Unit) (n × Unit) ℂ => M (i,()) (j,())) he
  erw [matrix_integral_entry hki] at hh
  erw [matrix_integral_entry hi]
  simpa only [Matrix.kronecker_apply, Matrix.one_apply_eq, mul_one] using hh

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_155} {m : Type u_156} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem interior_coordinate_exterior_representation (A : Matrix n n ℂ)
    {f g ψ G : ℂ → ℂ} {v : ℂ → Matrix m m ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hAU : spectrum ℂ A ⊆ U)
    (hf : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ f z)
    (hfd : ∀ z ∈ spectrum ℂ A, f z ∈ closedBall (0:ℂ) 1)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 1))
    (hgf : ∀ z ∈ U, g (f z) = z)
    (hv : AnalyticOnNhd ℂ v (g '' closedBall 0 1))
    (hD : spectralRadius ℂ (matrixAnalyticEval A f) < 1)
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hgb : ∀ t ∈ sphere (0:ℂ) 1, g (ψ t) = G t)
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1) :
    completeAnalyticEval A v =
      ∫ t : UnitAddCircle, pulledDiskDensity (matrixAnalyticEval A f) ψ t ⊗ₖ
        v (G (t.toCircle : ℂ)) ∂AddCircle.haarAddCircle := by
  have hvg : AnalyticOnNhd ℂ (fun z => v (g z)) (closedBall 0 1) := by
    intro z hz
    exact (hv (g z) ⟨z,hz,rfl⟩).comp (hg z hz)
  have he : completeAnalyticEval A v =
      completeAnalyticEval (matrixAnalyticEval A f) (fun z => v (g z)) := by
    rw [← completeAnalyticEval_comp A hf
      (F := fun z => v (g z)) (fun i j z hz => matrix_entry_analytic (hvg (f z) (hfd z hz)) i j)]
    apply completeAnalyticEval_eqOn A hU hAU
    intro z hz
    change v z = v (g (f z))
    rw [hgf z hz]
  rw [he, ← complete_pulled_disk_representation hD hψ hb hmass
    (fun i j z hz => matrix_entry_analytic (hvg z hz) i j)]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [hgb _ (by simp [Circle.norm_coe])]
  rfl


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_OptimalExtremal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_188 u_189 u_190

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators Matrix.Norms.L2Operator
open Set Filter Metric Topology
open Set Filter Metric Topology
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder Pointwise
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

section
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n : Type u_189} [Fintype n] [DecidableEq n] [Nonempty n]

lemma metric_sqrt_isUnit
    {n : Type u_189} [Fintype n] [DecidableEq n] [Nonempty n]
    {H : Matrix n n ℂ} (hH : H.PosDef) : IsUnit (CFC.sqrt H) :=
  (CFC.isUnit_sqrt_iff H hH.posSemidef.nonneg).mpr hH.isUnit

theorem metric_similarity_contraction {T H : Matrix n n ℂ} {τ : ℝ}
    (hf : MetricFeasible T τ H) (hp : H.PosDef) :
    ‖CFC.sqrt H * T * (CFC.sqrt H)⁻¹‖ ≤ 1 := by
  let S := CFC.sqrt H
  have hS : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)).isHermitian
  have hs2 : S*S = H := CFC.sqrt_mul_sqrt_self H hp.posSemidef.nonneg
  have hu : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp (metric_sqrt_isUnit hp)
  have hi : S⁻¹*S = 1 := Matrix.nonsing_inv_mul S hu
  have hi' : S*S⁻¹ = 1 := Matrix.mul_nonsing_inv S hu
  have hp0 : (H-Tᴴ*H*T).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hf.2.2)
  have hpc := hp0.conjTranspose_mul_mul_same S⁻¹
  have hid : S⁻¹ᴴ*(H-Tᴴ*H*T)*S⁻¹ = 1-(S*T*S⁻¹)ᴴ*(S*T*S⁻¹) := by
    rw [hS.inv.eq,Matrix.mul_sub,Matrix.sub_mul]
    have h1 : S⁻¹*H*S⁻¹ = 1 := by
      rw [← hs2,← Matrix.mul_assoc,hi,Matrix.one_mul,hi']
    rw [h1,Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,hS.inv.eq,hS.eq]
    congr 1
    rw [← hs2]
    noncomm_ring
  rw [hid] at hpc
  have hle : (S*T*S⁻¹)ᴴ*(S*T*S⁻¹) ≤ 1 := hpc
  have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (Matrix.posSemidef_conjTranspose_mul_self (S*T*S⁻¹)).nonneg).mpr hle
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hn
  nlinarith [norm_nonneg (S*T*S⁻¹)]

end

open Filter Topology Set Metric
open scoped Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_190} [Fintype n] [DecidableEq n] [Nonempty n]

lemma spectrum_matrix_similarity
    {n : Type u_190} [Fintype n] [DecidableEq n] [Nonempty n]
    {S : Matrix n n ℂ} (hS : IsUnit S) (T : Matrix n n ℂ) :
    spectrum ℂ (S*T*S⁻¹) = spectrum ℂ T := by
  rw [← hS.unit_spec, ← Matrix.coe_units_inv]
  exact spectrum.units_conjugate


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ConformalJacobian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open Set Filter Metric Complex
open scoped Topology ComplexConjugate InnerProductSpace
namespace CompleteCrouzeix

lemma circle_log_derivative_real {ψ : ℂ → ℂ} {t : ℂ}
    (ht : ‖t‖ = 1) (hψ : DifferentiableAt ℂ ψ t)
    (hb : ∀ z : ℂ, ‖z‖ = 1 → ‖ψ z‖ = 1) :
    (t*deriv ψ t/ψ t).im = 0 := by
  have hp : ‖ψ t‖ = 1 := hb t ht
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => exp ((s:ℂ)*I)*t)
      (exp ((s:ℂ)*I)*I*t) s := by
    simpa using (((hasDerivAt_id s).ofReal_comp.mul_const I).cexp.mul_const t)
  have he : HasDerivAt (fun s : ℝ => ψ (exp ((s:ℂ)*I)*t))
      (I*t*deriv ψ t) 0 := by
    simpa only [ofReal_zero, zero_mul, exp_zero, one_mul, Function.comp_def,
      smul_eq_mul] using (show HasDerivAt ψ (deriv ψ t) (exp (((0:ℝ):ℂ)*I)*t) from by simpa using hψ.hasDerivAt).scomp 0 (hd 0)
  have hn : (fun s : ℝ => ‖ψ (exp ((s:ℂ)*I)*t)‖^2) = fun _ => (1:ℝ) := by
    funext s
    rw [hb _ (by rw [norm_mul, norm_exp_ofReal_mul_I, ht, one_mul]), one_pow]
  have heq := he.norm_sq
  rw [hn] at heq
  have hz := heq.unique (hasDerivAt_const (0:ℝ) (1:ℝ))
  have hi : inner ℝ (ψ t) (I*t*deriv ψ t) = -(conj (ψ t)*(t*deriv ψ t)).im := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']
    change (conj (ψ t)*(I*t*deriv ψ t)).re = _
    rw [show conj (ψ t)*(I*t*deriv ψ t) = I*(conj (ψ t)*(t*deriv ψ t)) by ring]
    simp
  simp only [ofReal_zero, zero_mul, exp_zero, one_mul] at hz
  rw [hi] at hz
  have hconj : (ψ t)⁻¹ = conj (ψ t) := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hp]
    simp
  rw [div_eq_mul_inv, hconj, mul_comm (t*deriv ψ t)]
  linarith

lemma circle_log_derivative_nonneg {ψ : ℂ → ℂ} {t : ℂ}
    (_ht : ‖t‖ = 1) (hψ : DifferentiableAt ℂ ψ t)
    (hb : ‖ψ t‖ = 1)
    (hin : ∀ᶠ r : ℝ in 𝓝[Iic 1] 1, ‖ψ ((r:ℂ)*t)‖ ≤ 1) :
    0 ≤ (t*deriv ψ t/ψ t).re := by
  have hd : HasDerivAt (fun r : ℝ => (r:ℂ)*t) t 1 := by
    simpa using (hasDerivAt_id (1:ℝ)).ofReal_comp.mul_const t
  have he : HasDerivAt (fun r : ℝ => ψ ((r:ℂ)*t)) (t*deriv ψ t) 1 := by
    simpa only [ofReal_one, one_mul, Function.comp_def, smul_eq_mul] using
      (show HasDerivAt ψ (deriv ψ t) (((1:ℝ):ℂ)*t) from by simpa using hψ.hasDerivAt).scomp 1 hd
  have hm : IsLocalMaxOn (fun r : ℝ => ‖ψ ((r:ℂ)*t)‖^2) (Iic 1) 1 := by
    filter_upwards [hin] with r hr
    simpa only [ofReal_one, one_mul, hb, one_pow] using
      (pow_le_pow_left₀ (norm_nonneg _) hr 2)
  have hy : (-1:ℝ) ∈ posTangentConeAt (Iic (1:ℝ)) 1 := by
    apply mem_posTangentConeAt_of_segment_subset
    apply (convex_Iic (1:ℝ)).segment_subset <;> simp
  have hh := hm.hasFDerivWithinAt_nonpos he.norm_sq.hasFDerivAt.hasFDerivWithinAt hy
  simp only [ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, ofReal_one, one_mul] at hh
  have hi : inner ℝ (ψ t) (t*deriv ψ t) = (conj (ψ t)*(t*deriv ψ t)).re := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']; rfl
  rw [hi] at hh
  have hconj : (ψ t)⁻¹ = conj (ψ t) := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hb]
    simp
  rw [div_eq_mul_inv, hconj, mul_comm (t*deriv ψ t)]
  linarith

end CompleteCrouzeix

end

end
end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ConformalWinding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix


open Set Filter Metric Complex
open scoped Topology ComplexConjugate

open MeasureTheory Set Complex
open scoped Topology Real

open MeasureTheory Set Complex
open scoped Topology

open MeasureTheory Set Complex Metric
open scoped Topology

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_54
lemma circle_convex_integral_zero {K : Set ℂ} (hK : Convex ℝ K)
    {J G : ℂ → ℂ} (hJ : AnalyticOnNhd ℂ J K)
    (hG : AnalyticOnNhd ℂ G (sphere 0 1))
    (hcurve : MapsTo G (sphere 0 1) K) {a : ℂ} (ha : a ∈ K)
    (hne : ∀ t ∈ sphere (0:ℂ) 1, G t ≠ a)
    (hmass : (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ) / (G (t.toCircle : ℂ)-a)
        ∂AddCircle.haarAddCircle) = 1) :
    (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)*
      J (G (t.toCircle : ℂ)) ∂AddCircle.haarAddCircle) = 0 := by
  have hF : AnalyticOnNhd ℂ (fun z => (z-a)*J z) K := by
    intro z hz; exact (analyticAt_id.sub analyticAt_const).mul (hJ z hz)
  have he := circle_convex_cauchy hK hF hG hcurve ha hne hmass
  simpa only [sub_self, zero_mul] using
    (show (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)*J (G (t.toCircle : ℂ))
        ∂AddCircle.haarAddCircle) = (a-a)*J a from by
      calc
        _ = ∫ t : UnitAddCircle,
          ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)/(G (t.toCircle : ℂ)-a))*
            ((G (t.toCircle : ℂ)-a)*J (G (t.toCircle : ℂ)))
              ∂AddCircle.haarAddCircle := by
          apply integral_congr_ae
          filter_upwards [] with t
          have ht : (t.toCircle : ℂ) ∈ sphere (0:ℂ) 1 := by
            simp [Circle.norm_coe]
          field_simp [sub_ne_zero.mpr (hne _ ht)]
        _ = _ := he)

lemma logarithmic_dslope_derivative {f : ℂ → ℂ} {a z : ℂ}
    (hfa : f z ≠ f a) (hza : z ≠ a) (hf : DifferentiableAt ℂ f z) :
    deriv f z / (f z-f a) = 1/(z-a) + deriv (dslope f a) z / dslope f a z := by
  have hd : deriv (dslope f a) z =
      (deriv f z*(z-a)-(f z-f a))/(z-a)^2 := by
    rw [(dslope_eventuallyEq_slope_of_ne f hza).deriv_eq]
    rw [show slope f a = (fun w => (f w-f a)/(w-a)) from
      funext (fun w => slope_def_field f a w)]
    simpa only [Pi.div_apply, id_eq, mul_one] using
      ((hf.hasDerivAt.sub_const (f a)).fun_div
        ((hasDerivAt_id z).sub_const a) (sub_ne_zero.mpr hza)).deriv
  rw [hd, dslope_of_ne _ hza, slope_def_field]
  field_simp
  ring

theorem conformal_circle_mass {K V : Set ℂ} (hK : Convex ℝ K)
    (hV : IsOpen V) (hKV : K ⊆ V) {f G : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f V) (hfi : InjOn f V)
    (hG : AnalyticOnNhd ℂ G (sphere 0 1))
    (hcurve : MapsTo G (sphere 0 1) K) {a : ℂ} (ha : a ∈ K)
    (hfa : deriv f a ≠ 0)
    (hne : ∀ t ∈ sphere (0:ℂ) 1, G t ≠ a)
    (hmass : (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ) / (G (t.toCircle : ℂ)-a)
        ∂AddCircle.haarAddCircle) = 1) :
    (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv (f ∘ G) (t.toCircle : ℂ) /
        (f (G (t.toCircle : ℂ))-f a) ∂AddCircle.haarAddCircle) = 1 := by
  let J : ℂ → ℂ := fun z => deriv (dslope f a) z / dslope f a z
  have hq := analyticOnNhd_dslope hV hf (hKV ha)
  have hJ : AnalyticOnNhd ℂ J K := by
    intro z hz
    exact (hq.deriv z (hKV hz)).div (hq z (hKV hz))
      (dslope_ne_zero_of_injOn hfi (hKV ha) (hKV hz) hfa)
  have hz := circle_convex_integral_zero hK hJ hG hcurve ha hne hmass
  have ht (t : UnitAddCircle) : (t.toCircle : ℂ) ∈ sphere (0:ℂ) 1 := by
    simp [Circle.norm_coe]
  have htc : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)) :=
    by fun_prop
  have hgc : Continuous (fun t : UnitAddCircle => G (t.toCircle : ℂ)) :=
    hG.continuousOn.comp_continuous htc ht
  have hdgc : Continuous (fun t : UnitAddCircle => deriv G (t.toCircle : ℂ)) :=
    hG.deriv.continuousOn.comp_continuous htc ht
  have h₁ : Integrable (fun t : UnitAddCircle =>
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)/(G (t.toCircle : ℂ)-a))
        AddCircle.haarAddCircle :=
    ((htc.mul hdgc).div (hgc.sub continuous_const)
      (fun t => sub_ne_zero.mpr (hne _ (ht t)))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h₂ : Integrable (fun t : UnitAddCircle =>
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)*J (G (t.toCircle : ℂ)))
        AddCircle.haarAddCircle :=
    ((htc.mul hdgc).mul
      (hJ.continuousOn.comp_continuous hgc (fun t => hcurve (ht t)))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ t : UnitAddCircle,
      ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)/(G (t.toCircle : ℂ)-a) +
        (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)*J (G (t.toCircle : ℂ)))
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with t
      have he : f (G (t.toCircle : ℂ)) ≠ f a :=
        fun he => hne _ (ht t) (hfi (hKV (hcurve (ht t))) (hKV ha) he)
      rw [deriv_comp _ (hf _ (hKV (hcurve (ht t)))).differentiableAt
        (hG _ (ht t)).differentiableAt]
      have heq := logarithmic_dslope_derivative he (hne _ (ht t))
        (hf _ (hKV (hcurve (ht t)))).differentiableAt
      change _ = _ + _*J _
      dsimp [J]
      linear_combination ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ))*heq
    _ = 1 := by rw [integral_add h₁ h₂, hmass, hz, add_zero]


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ResolventPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexConjugate InnerProductSpace
namespace CompleteCrouzeix

lemma eigenvalue_mem_numericalRange {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    {z : ℂ} {x : EuclideanSpace ℂ (Fin n)} (hx : x ≠ 0)
    (he : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A x = z • x) :
    z ∈ numericalRange A := by
  let y := (‖x‖⁻¹ : ℝ) • x
  have hy : ‖y‖ = 1 := by simp [y, norm_smul, norm_ne_zero_iff.mpr hx]
  have he' : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A y = z • y := by
    simp [y, ContinuousLinearMap.map_smul_of_tower, he, smul_comm (‖x‖⁻¹ : ℝ) z]
  refine ⟨y, hy, ?_⟩
  rw [he', inner_smul_right, inner_self_eq_norm_sq_to_K, hy]
  simp

theorem spectrum_subset_numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ A ⊆ numericalRange A := by
  intro z hz
  have hz' : z ∈ spectrum ℂ A.toLin' := by simpa using hz
  obtain ⟨v,hv⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hz').exists_hasEigenvector
  let x : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 v
  apply eigenvalue_mem_numericalRange (x := x)
  · simpa [x] using hv.2
  · change WithLp.toLp 2 (A.toLin' v) = z • WithLp.toLp 2 v
    rw [hv.apply_eq_smul]
    rfl

end CompleteCrouzeix

end

end
end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DomainCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_244

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
lemma inverse_ψ {t : ℂ} (ht : t ∈ sphere (0:ℂ) 1) : D.interior.fromDisk (D.ψ t) = D.G t :=
  D.interior.left_inverse _ (D.interior.closure_subset (D.G_boundary ht).1)
lemma ψ_jacobian {t : ℂ} (ht : t ∈ sphere (0:ℂ) 1) :
    0 ≤ t*deriv D.ψ t/D.ψ t := by
  rw [Complex.nonneg_iff]
  refine ⟨circle_log_derivative_nonneg (mem_sphere_zero_iff_norm.mp ht)
    (D.ψ_analytic t ht).differentiableAt (D.ψ_boundary ht) ?_,
    (circle_log_derivative_real (mem_sphere_zero_iff_norm.mp ht)
    (D.ψ_analytic t ht).differentiableAt (fun z hz => D.ψ_boundary (mem_sphere_zero_iff_norm.mpr hz))).symm⟩
  have hi : D.exterior.radius⁻¹ < 1 := inv_lt_one_of_one_lt₀ D.exterior.radius_gt
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (lt_mem_nhds hi)] with r hr hri
  have hr0 : 0 < r := (inv_pos.mpr (zero_lt_one.trans D.exterior.radius_gt)).trans hri
  have hnorm : ‖(r:ℂ)*t‖ = r := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr0,mem_sphere_zero_iff_norm.mp ht,mul_one]
  change ‖D.interior.toDisk (D.G ((r:ℂ)*t))‖ ≤ 1
  apply mem_closedBall_zero_iff.mp (D.interior.closure_maps _)
  rcases lt_or_eq_of_le (show r ≤ 1 from hr) with hlt|rfl
  · exact subset_closure ((D.exterior.interior_iff _ (by simpa only [hnorm] using hri)).mpr
      (mem_ball_zero_iff.mpr (by simpa only [hnorm] using hlt)))
  · simpa only [ofReal_one,one_mul] using (D.G_boundary ht).1
lemma G_mass {z : ℂ} (hz : z ∈ D.domain) :
    (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv D.G (t.toCircle : ℂ) /
      (D.G (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1 := by
  apply exterior_cauchy_kernel_integral D.exterior.leading_ne
    (D.exterior.analytic_regular.mono (closedBall_subset_ball D.exterior.radius_gt))
  intro t ht
  exact D.G_ne_interior hz ht
lemma ψ_mass {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) :
    (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv D.ψ (t.toCircle : ℂ) /
      (D.ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1 := by
  have ha := D.interior.inverse_ball z hz
  have hfa := D.interior.right_inverse z (D.interior.closedDisk_subset (ball_subset_closedBall hz))
  have hm := conformal_circle_mass D.convex.closure D.interior.outer_open
    D.interior.closure_subset D.interior.analytic_to D.interior.injective_to D.G_analytic
    (fun t ht => (D.G_boundary ht).1) (subset_closure ha)
    (D.interior.noncritical_to _ (D.interior.closure_subset (subset_closure ha)))
    (fun t ht => D.G_ne_interior ha (mem_sphere_zero_iff_norm.mp ht).ge) (D.G_mass ha)
  simpa only [hfa,ψ,Function.comp_apply] using hm
end AdmissibleDomain

end CompleteCrouzeix

end

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_BoundaryCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_245 u_246

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
variable {n : Type u_245} {m : Type u_246} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
attribute [local instance] OAI.CompleteCrouzeix.AdmissibleDomain.instFactLtRealOfNat
lemma positive_representation [Nonempty n] (A : Matrix n n ℂ)
    (hA : spectrum ℂ A ⊆ D.domain) {v : ℂ → Matrix m m ℂ}
    (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    completeAnalyticEval A v = ∫ t : UnitAddCircle,
      pulledDiskDensity (matrixAnalyticEval A D.interior.toDisk) D.ψ t ⊗ₖ
        D.trace v hv t ∂AddCircle.haarAddCircle := by
  have hf (z : ℂ) (hz : z ∈ spectrum ℂ A) :=
    D.interior.analytic_to z (D.interior.closure_subset (subset_closure (hA hz)))
  apply interior_coordinate_exterior_representation A D.isOpen hA hf
    (fun z hz => ball_subset_closedBall (D.toDisk_maps (hA hz)))
    (D.interior.analytic_from.mono D.interior.closedDisk_subset)
    (fun z hz => D.interior.left_inverse z (D.interior.closure_subset (subset_closure hz)))
    (hv.mono (by rintro z ⟨w,hw,rfl⟩; exact D.interior.inverse_closed w hw))
    (matrixAnalyticEval_stable A hf (fun z hz => mem_ball_zero_iff.mp (D.toDisk_maps (hA hz))))
    D.ψ_analytic (fun _ ht => D.ψ_boundary ht) (fun _ ht => D.inverse_ψ ht) (fun _ hz => D.ψ_mass hz)
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_PositiveDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u_253 u_254

namespace CompleteCrouzeix
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace AdmissibleDomain

section
variable (D : AdmissibleDomain)
variable {n : Type u_253} {m : Type u_254} [Fintype n] [DecidableEq n] [Nonempty n] [Fintype m] [DecidableEq m]
lemma positiveDensity_nonneg (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    (hc : (matrixAnalyticEval A D.interior.toDisk)ᴴ * matrixAnalyticEval A D.interior.toDisk ≤ 1)
    (t : UnitAddCircle) : 0 ≤ D.positiveDensity A hA t :=
  pulledDiskDensity_nonneg (D.coordinate_stable A hA) hc
    (fun _ ht => D.ψ_boundary ht) (fun _ ht => D.ψ_jacobian ht) t
attribute [local instance] OAI.CompleteCrouzeix.AdmissibleDomain.instFactLtRealOfNat_2
lemma positiveDensity_mass (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain) :
    (∫ t, D.positiveDensity A hA t ∂AddCircle.haarAddCircle) = 1 :=
  pulledDiskDensity_mass (D.coordinate_stable A hA) D.ψ_analytic
    (fun _ ht => D.ψ_boundary ht) (fun _ hz => D.ψ_mass hz)
lemma positiveDensity_representation (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    {v : ℂ → Matrix m m ℂ} (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    completeAnalyticEval A v = ∫ t, D.positiveDensity A hA t ⊗ₖ D.trace v hv t
      ∂AddCircle.haarAddCircle := D.positive_representation A hA hv
end
end AdmissibleDomain
end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_MetricNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_258

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
variable {n : Type u_258} [Fintype n] [DecidableEq n] [Nonempty n]
lemma matrix_contractivity_iff {n : Type u_258} [Fintype n] [DecidableEq n] [Nonempty n]
    (B : Matrix n n ℂ) : Bᴴ*B ≤ 1 ↔ ‖B‖ ≤ 1 := by
  have hn := CStarAlgebra.norm_le_one_iff_of_nonneg (Bᴴ*B)
    (Matrix.posSemidef_conjTranspose_mul_self B).nonneg
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hn
  constructor
  · intro h
    have hh := hn.mpr h
    nlinarith [norm_nonneg B]
  · intro h
    apply hn.mp
    nlinarith [norm_nonneg B]
end CompleteCrouzeix

end

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.StructuralCrouzeix_GeometryBasics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
namespace CompleteCrouzeix
open Set Filter Metric Complex
open scoped Topology

lemma convex_analytic_interior_coordinate {U : Set ℂ}
    (hU : IsOpen U) (hcv : Convex ℝ U) (hK : IsCompact (closure U))
    {a : ℂ} (ha : a ∈ U)
    (hchart : ∀ p ∈ frontier U, LocalAnalyticBoundary U p) :
    Nonempty (DiskCoordinate U a) := by
  have := hcv.contractibleSpace ⟨a, ha⟩
  exact analytic_domain_disk_coordinate hU
    (by change SimplyConnectedSpace U; infer_instance)
    (hK.isBounded.subset subset_closure) ha hchart

lemma convex_closed_analytic_exterior_coordinate {U : Set ℂ}
    (hU : IsOpen U) (hcv : Convex ℝ U) (hK : IsCompact (closure U))
    {a : ℂ} (ha : a ∈ U)
    (hchart : ∀ p ∈ frontier U, LocalClosedAnalyticBoundary U p) :
    Nonempty (ExteriorCoordinate U) := by
  have := invertedExterior_simplyConnected hcv.closure (subset_closure ha)
  have hcharts : ∀ p ∈ frontier (invertedExterior (closure U) a),
      LocalAnalyticBoundary (invertedExterior (closure U) a) p := by
    intro p hp
    obtain ⟨hp0, hzp⟩ := invertedExterior_frontier hU hK ha hp
    obtain ⟨χ, hχ0, hχa, hχd, _, _, hχc⟩ := hchart _ hzp
    have hza : a + p⁻¹ ≠ a := by simpa using inv_ne_zero hp0
    obtain ⟨ψ, hψ0, hψa, hψd, hψs, hψb⟩ :=
      invertedExterior_local_chart hK hχ0 hχa hχd hza hχc
    exact ⟨ψ, by simpa only [add_sub_cancel_left, inv_inv] using hψ0, hψa, hψd, hψs, hψb⟩
  obtain ⟨D⟩ := analytic_domain_disk_coordinate (invertedExterior_open hK)
    (by change SimplyConnectedSpace (invertedExterior (closure U) a); infer_instance)
    (invertedExterior_bounded (hU.subset_interior_closure ha))
    (zero_mem_invertedExterior (closure U) a) hcharts
  exact exteriorCoordinate_of_disk_inversion hU hK ha
    ((hcv.interior_closure_eq_interior_of_nonempty_interior
      (by rw [hU.interior_eq]; exact ⟨a, ha⟩)).trans hU.interior_eq) D
end CompleteCrouzeix
end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.StructuralCrouzeix_ClosedSide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
namespace CompleteCrouzeix
open Set Filter Metric Complex
open scoped Topology

lemma LocalAnalyticBoundary.closedSide {U : Set ℂ} {p : ℂ}
    (h : LocalAnalyticBoundary U p) : LocalClosedAnalyticBoundary U p := by
  obtain ⟨χ,hχ0,hχa,hχd,hs,hb⟩ := h
  obtain ⟨V,hVo,h0V,hχVo,ψ,hψa,hleft,hright⟩ :=
    analytic_local_inverse_neighborhood hχa hχd
  have hVevent : ∀ᶠ z : ℂ in 𝓝 0, z ∈ V := hVo.mem_nhds h0V
  obtain ⟨r,hr,hrall⟩ := Metric.mem_nhds_iff.mp
    (hVevent.and (hs.and hb))
  refine ⟨χ,hχ0,hχa,hχd,hs,hb,?_⟩
  apply mem_of_superset (ball_mem_nhds 0 hr)
  intro z hz
  have hzV : z ∈ V := (hrall hz).1
  have hzψ : ψ (χ z) = z := hleft z hzV
  have hzimage : χ z ∈ χ '' V := ⟨z,hzV,rfl⟩
  constructor
  · intro hcl
    by_contra hn
    have him : z.im < 0 := lt_of_not_ge hn
    have hψc : ContinuousAt ψ (χ z) := (hψa (χ z) hzimage).continuousAt
    have hnear : ∀ᶠ y in 𝓝 (χ z), ψ y ∈ ball 0 r :=
      hψc.preimage_mem_nhds (by simpa only [hzψ] using isOpen_ball.mem_nhds hz)
    have him_cont : Tendsto (fun y : ℂ => (ψ y).im) (𝓝 (χ z))
        (𝓝 ((ψ (χ z)).im)) := Complex.continuous_im.continuousAt.comp hψc
    have hnegative : ∀ᶠ y in 𝓝 (χ z), (ψ y).im < 0 :=
      him_cont.eventually (by simpa only [hzψ] using (gt_mem_nhds him))
    have hnot : ∀ᶠ y in 𝓝 (χ z), y ∉ U := by
      filter_upwards [hχVo.mem_nhds hzimage,hnear,hnegative] with y hy hry hiy
      intro hyU
      have hχU : χ (ψ y) ∈ U := by rw [hright y hy]; exact hyU
      have hi := (hrall hry).2.1.mp hχU
      exact (not_lt_of_ge hiy.le) hi
    obtain ⟨_,hyU,hyn⟩ :=
      ((mem_closure_iff_frequently.mp hcl).and_eventually hnot).exists
    exact hyn hyU
  · intro him
    rcases eq_or_lt_of_le him with heq | hpos
    · exact ((hrall hz).2.2 heq.symm).1
    · exact subset_closure ((hrall hz).2.1.mpr hpos)

lemma convex_analytic_exterior_coordinate {U : Set ℂ}
    (hU : IsOpen U) (hcv : Convex ℝ U) (hK : IsCompact (closure U))
    {a : ℂ} (ha : a ∈ U)
    (hchart : ∀ p ∈ frontier U, LocalAnalyticBoundary U p) :
    Nonempty (ExteriorCoordinate U) :=
  convex_closed_analytic_exterior_coordinate hU hcv hK ha
    (fun p hp => (hchart p hp).closedSide)

end CompleteCrouzeix
end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.StructuralCrouzeix_OrientBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
namespace StructuralCrouzeix
open CompleteCrouzeix Set Filter Metric Complex
open scoped Topology

private lemma preconnected_avoiding_frontier {U S : Set ℂ}
    (hU : IsOpen U) (hS : IsPreconnected S)
    (havoid : ∀ z ∈ S, z ∉ frontier U) :
    S ⊆ U ∨ S ⊆ (closure U)ᶜ := by
  apply hS.subset_or_subset hU isClosed_closure.isOpen_compl
  · exact Set.disjoint_left.mpr (fun z hz hn => hn (subset_closure hz))
  · intro z hz
    by_cases hi : z ∈ U
    · exact Or.inl hi
    · right
      intro hc
      apply havoid z hz
      rw [hU.frontier_eq]
      exact ⟨hc,hi⟩

theorem RegularAnalyticBoundaryAt.orient {U : Set ℂ} {p : ℂ}
    (hU : IsOpen U) (hcv : Convex ℝ U) (hne : U.Nonempty)
    (hp : p ∈ frontier U) (hchart : RegularAnalyticBoundaryAt U p) :
    LocalAnalyticBoundary U p := by
  obtain ⟨χ,hχ0,hχa,hχd,hboundary⟩ := hchart
  obtain ⟨r,hr,hrall⟩ := Metric.mem_nhds_iff.mp
    (hχa.eventually_analyticAt.and hboundary)
  let B : Set ℂ := ball 0 r
  let P : Set ℂ := B ∩ {z : ℂ | 0 < z.im}
  let N : Set ℂ := B ∩ {z : ℂ | z.im < 0}
  have hca : AnalyticOnNhd ℂ χ B := fun z hz => (hrall hz).1
  have hPc : Convex ℝ P :=
    (convex_ball (0 : ℂ) r).inter ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hNc : Convex ℝ N :=
    (convex_ball (0 : ℂ) r).inter ((convex_Iio (0 : ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hPi := hPc.isPreconnected.image χ (hca.continuousOn.mono inter_subset_left)
  have hNi := hNc.isPreconnected.image χ (hca.continuousOn.mono inter_subset_left)
  have hPa : ∀ y ∈ χ '' P, y ∉ frontier U := by
    rintro y ⟨z,hz,rfl⟩ hf
    have hi := (hrall hz.1).2.mp hf
    exact (ne_of_gt hz.2) hi
  have hNa : ∀ y ∈ χ '' N, y ∉ frontier U := by
    rintro y ⟨z,hz,rfl⟩ hf
    have hi := (hrall hz.1).2.mp hf
    exact (ne_of_lt hz.2) hi
  have hP := preconnected_avoiding_frontier hU hPi hPa
  have hN := preconnected_avoiding_frontier hU hNi hNa
  have hnb : χ '' B ∈ 𝓝 p := by
    rw [← hχ0, ← hχa.hasStrictDerivAt.map_nhds_eq hχd]
    exact image_mem_map (ball_mem_nhds 0 hr)
  have hpnot : p ∉ U := by rw [hU.frontier_eq] at hp; exact hp.2
  have hregular : interior (closure U) = U :=
    (hcv.interior_closure_eq_interior_of_nonempty_interior
      (by rw [hU.interior_eq]; exact hne)).trans hU.interior_eq
  have hnotboth (hPU : χ '' P ⊆ U) (hNU : χ '' N ⊆ U) : False := by
    have hbcl : χ '' B ⊆ closure U := by
      rintro y ⟨z,hz,rfl⟩
      rcases lt_trichotomy z.im 0 with hn | he | hp
      · exact subset_closure (hNU ⟨z,⟨hz,hn⟩,rfl⟩)
      · exact ((hrall hz).2.mpr he).1
      · exact subset_closure (hPU ⟨z,⟨hz,hp⟩,rfl⟩)
    have hpi : p ∈ interior (closure U) :=
      mem_interior_iff_mem_nhds.mpr (mem_of_superset hnb hbcl)
    exact hpnot (hregular ▸ hpi)
  have hnotneither (hPO : χ '' P ⊆ (closure U)ᶜ)
      (hNO : χ '' N ⊆ (closure U)ᶜ) : False := by
    have hbnot : ∀ y ∈ χ '' B, y ∉ U := by
      rintro y ⟨z,hz,rfl⟩ hi
      rcases lt_trichotomy z.im 0 with hn | he | hp
      · exact hNO ⟨z,⟨hz,hn⟩,rfl⟩ (subset_closure hi)
      · have hf := (hrall hz).2.mpr he
        rw [hU.frontier_eq] at hf
        exact hf.2 hi
      · exact hPO ⟨z,⟨hz,hp⟩,rfl⟩ (subset_closure hi)
    have he : ∀ᶠ y in 𝓝 p, y ∉ U := mem_of_superset hnb hbnot
    obtain ⟨y,hy,hyn⟩ := ((mem_closure_iff_frequently.mp hp.1).and_eventually he).exists
    exact hyn hy
  have hsideP (hPU : χ '' P ⊆ U) (hNO : χ '' N ⊆ (closure U)ᶜ) :
      ∀ z ∈ B, χ z ∈ U ↔ 0 < z.im := by
    intro z hz
    constructor
    · intro hi
      by_contra hn
      rcases lt_or_eq_of_le (le_of_not_gt hn) with hneg | heq
      · exact hNO ⟨z,⟨hz,hneg⟩,rfl⟩ (subset_closure hi)
      · have hf := (hrall hz).2.mpr heq
        rw [hU.frontier_eq] at hf
        exact hf.2 hi
    · intro hi
      exact hPU ⟨z,⟨hz,hi⟩,rfl⟩
  have hsideN (hPO : χ '' P ⊆ (closure U)ᶜ) (hNU : χ '' N ⊆ U) :
      ∀ z ∈ B, χ z ∈ U ↔ z.im < 0 := by
    intro z hz
    constructor
    · intro hi
      by_contra hn
      rcases eq_or_lt_of_le (le_of_not_gt hn) with heq | hpos
      · have hf := (hrall hz).2.mpr heq.symm
        rw [hU.frontier_eq] at hf
        exact hf.2 hi
      · exact hPO ⟨z,⟨hz,hpos⟩,rfl⟩ (subset_closure hi)
    · intro hi
      exact hNU ⟨z,⟨hz,hi⟩,rfl⟩
  rcases hP with hPU | hPO
  · have hNO : χ '' N ⊆ (closure U)ᶜ := hN.resolve_left (hnotboth hPU)
    refine ⟨χ,hχ0,hχa,hχd,?_,?_⟩
    · exact mem_of_superset (ball_mem_nhds 0 hr) (hsideP hPU hNO)
    · filter_upwards [hboundary] with z hz
      exact hz.mpr
  · have hNU : χ '' N ⊆ U := hN.resolve_right (hnotneither hPO)
    let ψ : ℂ → ℂ := fun z => χ (-z)
    have ha : AnalyticAt ℂ ψ 0 := by
      exact (show AnalyticAt ℂ χ (-(0 : ℂ)) by simpa only [neg_zero] using hχa).comp
        (analyticAt_id.neg : AnalyticAt ℂ (fun z : ℂ => -z) 0)
    have hd : deriv ψ 0 ≠ 0 := by
      have he := hχa.differentiableAt.hasDerivAt.comp_of_eq 0
        (hasDerivAt_id (0 : ℂ)).neg (by simp)
      change deriv (χ ∘ (-id)) 0 ≠ 0
      rw [he.deriv]
      exact mul_ne_zero hχd (neg_ne_zero.mpr one_ne_zero)
    refine ⟨ψ,by simpa only [ψ, neg_zero] using hχ0,ha,hd,?_,?_⟩
    · apply mem_of_superset (ball_mem_nhds 0 hr)
      intro z hz
      have hneg : -z ∈ B := by simpa only [B, mem_ball_zero_iff,norm_neg] using hz
      change χ (-z) ∈ U ↔ 0 < z.im
      simpa only [neg_im, neg_lt_zero] using hsideN hPO hNU (-z) hneg
    · apply mem_of_superset (ball_mem_nhds 0 hr)
      intro z hz him
      have hneg : -z ∈ B := by simpa only [B, mem_ball_zero_iff,norm_neg] using hz
      apply (hrall hneg).2.mpr
      simp only [neg_im,him,neg_zero]

end StructuralCrouzeix
end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.StructuralCrouzeix_SharedDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)

attribute [local instance] OAI.CompleteCrouzeix.AdmissibleDomain.instFactLtRealOfNat_5
theorem positiveDensity_analytic_bound
    {n m : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    [Fintype m] [DecidableEq m]
    (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    (hc : (matrixAnalyticEval A D.interior.toDisk)ᴴ *
      matrixAnalyticEval A D.interior.toDisk ≤ 1)
    (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain))
    {b : ℝ} (hb : 0 ≤ b) (hbound : ∀ z ∈ closure D.domain, ‖v z‖ ≤ b) :
    ‖completeAnalyticEval A v‖ ≤ b := by
  by_cases hb0 : b = 0
  · subst b
    rw [D.positiveDensity_representation A hA hv]
    have hz (t : UnitAddCircle) : D.trace v hv t = 0 :=
      norm_eq_zero.mp (le_antisymm
        (hbound _ (frontier_subset_closure (D.G_boundary t.toCircle.property))) (norm_nonneg _))
    simp only [hz, Matrix.kronecker_zero, integral_zero, norm_zero, le_refl]
  · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    let L := D.positiveDensity A hA
    let F : C(UnitAddCircle, Matrix m m ℂ) := (b⁻¹ : ℝ) • D.trace v hv
    have hn : ‖∫ t, L t ⊗ₖ F t ∂AddCircle.haarAddCircle‖ ≤ 1 := by
      apply norm_integral_density_kron
      · exact L.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact (continuous_kron L.continuous F.continuous).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · intro t
        exact Matrix.nonneg_iff_posSemidef.mp (D.positiveDensity_nonneg A hA hc t)
      · exact D.positiveDensity_mass A hA
      · intro t
        change ‖(b⁻¹ : ℝ) • D.trace v hv t‖ ≤ 1
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hbp)]
        calc
          _ ≤ b⁻¹ * b := mul_le_mul_of_nonneg_left
            (hbound _ (frontier_subset_closure (D.G_boundary t.toCircle.property))) (inv_nonneg.mpr hb)
          _ = 1 := inv_mul_cancel₀ hb0
    have he : (∫ t, L t ⊗ₖ F t ∂AddCircle.haarAddCircle) =
        (b⁻¹ : ℝ) • completeAnalyticEval A v := by
      change (∫ t, L t ⊗ₖ ((b⁻¹ : ℝ) • D.trace v hv t) ∂AddCircle.haarAddCircle) = _
      simp_rw [Matrix.kronecker_smul]
      rw [integral_smul, ← D.positiveDensity_representation A hA hv]
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hbp)] at hn
    have hh := mul_le_mul_of_nonneg_left hn hb
    simpa only [← mul_assoc, mul_inv_cancel₀ hb0, one_mul, mul_one] using hh

theorem complete_analytic_similarity_bound_nonneg
    {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    {S A : Matrix n n ℂ} (hS : IsUnit S)
    (F : ℂ → Matrix m m ℂ) {b : ℝ} (hb : 0 ≤ b)
    (hF : ‖completeAnalyticEval (S*A*S⁻¹) F‖ ≤ b) :
    ‖completeAnalyticEval A F‖ ≤ (‖S‖ * ‖S⁻¹‖) * b := by
  let R := baseMatrixHom (m := m) S
  let R' := baseMatrixHom (m := m) S⁻¹
  have hi : S⁻¹*S=1 := Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  have hR : R'*R=1 := by
    change baseMatrixHom (m := m) S⁻¹ * baseMatrixHom S=1
    rw [← map_mul, hi, map_one]
  have he : completeAnalyticEval A F = R'*completeAnalyticEval (S*A*S⁻¹) F*R := by
    rw [completeAnalyticEval_similarity hS]
    change completeAnalyticEval A F = R'*(R*completeAnalyticEval A F*R')*R
    calc
      _ = 1*completeAnalyticEval A F*1 := by simp
      _ = _ := by rw [← hR]; noncomm_ring
  rw [he]
  calc
    _ ≤ ‖R'‖ * ‖completeAnalyticEval (S*A*S⁻¹) F‖ * ‖R‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ‖S⁻¹‖ * b * ‖S‖ := mul_le_mul
      (mul_le_mul (baseMatrixHom_norm S⁻¹) hF (norm_nonneg _) (norm_nonneg _))
      (baseMatrixHom_norm S) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hb)
    _ = _ := by ring

theorem common_positiveDensity_for_metric
    {n : ℕ} [Nonempty (Fin n)]
    (A H : Matrix (Fin n) (Fin n) ℂ) {τ : ℝ}
    (hW : numericalRange A ⊆ D.domain)
    (hf : MetricFeasible (matrixAnalyticEval A D.interior.toDisk) τ H) :
    ∃ Λ : C(UnitAddCircle, Matrix (Fin n) (Fin n) ℂ),
      (∀ t, 0 ≤ Λ t) ∧
      (∫ t, Λ t ∂AddCircle.haarAddCircle) = 1 ∧
      ∀ (m : ℕ) (v : ℂ → Matrix (Fin m) (Fin m) ℂ)
        (_ : AnalyticOnNhd ℂ v (closure D.domain)),
        completeAnalyticEval (CFC.sqrt H * A * (CFC.sqrt H)⁻¹) v =
          ∫ t, Λ t ⊗ₖ v (D.G t.toCircle) ∂AddCircle.haarAddCircle ∧
        (∀ (b : ℝ), 0 ≤ b → (∀ z ∈ closure D.domain, ‖v z‖ ≤ b) →
          ‖completeAnalyticEval A v‖ ≤ (‖CFC.sqrt H‖ * ‖(CFC.sqrt H)⁻¹‖) * b) := by
  have hp : H.PosDef := by
    have hh := Matrix.PosDef.one.add_posSemidef (hf.1 : (H - 1).PosSemidef)
    simpa only [add_sub_cancel] using hh
  let S := CFC.sqrt H
  have hu : IsUnit S := metric_sqrt_isUnit hp
  have hA : spectrum ℂ A ⊆ D.domain := (spectrum_subset_numericalRange A).trans hW
  have hA' : spectrum ℂ (S * A * S⁻¹) ⊆ D.domain := by
    rwa [spectrum_matrix_similarity hu]
  have hc : (matrixAnalyticEval (S * A * S⁻¹) D.interior.toDisk)ᴴ *
      matrixAnalyticEval (S * A * S⁻¹) D.interior.toDisk ≤ 1 := by
    rw [matrixAnalyticEval_similarity hu]
    exact (matrix_contractivity_iff _).mpr (metric_similarity_contraction hf hp)
  refine ⟨D.positiveDensity (S * A * S⁻¹) hA',
    D.positiveDensity_nonneg _ hA' hc, D.positiveDensity_mass _ hA', ?_⟩
  intro m v hv
  constructor
  · exact D.positiveDensity_representation _ hA' hv
  · intro b hb hbound
    exact complete_analytic_similarity_bound_nonneg hu v hb
      (D.positiveDensity_analytic_bound _ hA' hc v hv hb hbound)

end AdmissibleDomain
end CompleteCrouzeix
end
end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.StructuralCrouzeix_SharedMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)

lemma analyticRangeMaximum_bddAbove {m : Type*} [Fintype m] [DecidableEq m]
    (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    BddAbove ((fun z => ‖v z‖) '' closure D.domain) := by
  exact (D.compact_closure.image_of_continuousOn hv.continuousOn.norm).bddAbove

theorem analyticRangeMaximum_attained {m : Type*} [Fintype m] [DecidableEq m]
    (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    ∃ z ∈ closure D.domain, D.analyticRangeMaximum v = ‖v z‖ := by
  have hne : (closure D.domain).Nonempty := ⟨D.base, subset_closure D.base_mem⟩
  obtain ⟨z, hz, hmax⟩ := D.compact_closure.exists_isMaxOn hne hv.continuousOn.norm
  refine ⟨z, hz, ?_⟩
  change sSup ((fun w => ‖v w‖) '' closure D.domain) = ‖v z‖
  apply le_antisymm
  · apply csSup_le (hne.image _)
    rintro r ⟨w, hw, rfl⟩
    exact hmax hw
  · exact le_csSup (D.analyticRangeMaximum_bddAbove v hv) ⟨z, hz, rfl⟩

lemma analyticRangeMaximum_nonneg {m : Type*} [Fintype m] [DecidableEq m]
    (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    0 ≤ D.analyticRangeMaximum v := by
  obtain ⟨z, hz, he⟩ := D.analyticRangeMaximum_attained v hv
  rw [he]
  exact norm_nonneg _

lemma norm_le_analyticRangeMaximum {m : Type*} [Fintype m] [DecidableEq m]
    (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain))
    {z : ℂ} (hz : z ∈ closure D.domain) : ‖v z‖ ≤ D.analyticRangeMaximum v := by
  exact le_csSup (D.analyticRangeMaximum_bddAbove v hv) ⟨z, hz, rfl⟩

attribute [local instance] OAI.CompleteCrouzeix.AdmissibleDomain.instFactLtRealOfNat_6
theorem common_positiveDensity_maximum_for_metric
    {n : ℕ} [Nonempty (Fin n)]
    (A H : Matrix (Fin n) (Fin n) ℂ) {τ : ℝ}
    (hW : numericalRange A ⊆ D.domain)
    (hf : MetricFeasible (matrixAnalyticEval A D.interior.toDisk) τ H) :
    ∃ Λ : C(UnitAddCircle, Matrix (Fin n) (Fin n) ℂ),
      (∀ t, 0 ≤ Λ t) ∧
      (∫ t, Λ t ∂AddCircle.haarAddCircle) = 1 ∧
      ∀ (m : ℕ), 0 < m →
      ∀ (v : ℂ → Matrix (Fin m) (Fin m) ℂ)
        (_ : AnalyticOnNhd ℂ v (closure D.domain)),
        completeAnalyticEval (CFC.sqrt H * A * (CFC.sqrt H)⁻¹) v =
          ∫ t, Λ t ⊗ₖ v (D.G t.toCircle) ∂AddCircle.haarAddCircle ∧
        ‖completeAnalyticEval A v‖ ≤
          (‖CFC.sqrt H‖ * ‖(CFC.sqrt H)⁻¹‖) * D.analyticRangeMaximum v := by
  obtain ⟨Λ, hpos, hmass, hrep⟩ := D.common_positiveDensity_for_metric A H hW hf
  refine ⟨Λ, hpos, hmass, ?_⟩
  intro m hm v hv
  obtain ⟨he, hb⟩ := hrep m v hv
  exact ⟨he, hb (D.analyticRangeMaximum v) (D.analyticRangeMaximum_nonneg v hv)
    (fun z hz => D.norm_le_analyticRangeMaximum v hv hz)⟩

end AdmissibleDomain
end CompleteCrouzeix
end
end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.StructuralCrouzeix_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Kronecker
namespace StructuralCrouzeix
open CompleteCrouzeix

lemma IsAdmissible.sided_boundary {U : Set ℂ} (hU : IsAdmissible U) :
    ∀ p ∈ frontier U, LocalAnalyticBoundary U p := by
  intro p hp
  exact RegularAnalyticBoundaryAt.orient hU.isOpen hU.convex hU.nonempty hp
    (hU.regular p hp)

theorem IsAdmissible.coordinates {U : Set ℂ} (hU : IsAdmissible U) :
    (∀ a ∈ U, Nonempty (DiskCoordinate U a)) ∧ Nonempty (ExteriorCoordinate U) := by
  constructor
  · intro a ha
    exact convex_analytic_interior_coordinate hU.isOpen hU.convex hU.compact_closure
      ha hU.sided_boundary
  · obtain ⟨a,ha⟩ := hU.nonempty
    exact convex_analytic_exterior_coordinate hU.isOpen hU.convex hU.compact_closure
      ha hU.sided_boundary

lemma bundleDomain_boundaryPoint {U : Set ℂ} (hU : IsAdmissible U)
    (a : ℂ) (ha : a ∈ U) (f : DiskCoordinate U a) (G : ExteriorCoordinate U)
    (t : UnitAddCircle) :
    (bundleDomain hU a ha f G).G (t.toCircle : ℂ) = boundaryPoint G t := rfl

theorem fullEndpoint : FullEndpoint := by
  intro U hU
  obtain ⟨hinterior,hexterior⟩ := hU.coordinates
  refine ⟨hinterior,hexterior,?_⟩
  intro a ha f G n hn A hW
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let D := bundleDomain hU a ha f G
  have hWD : numericalRange A ⊆ D.domain := hW
  obtain ⟨hstrict,κ,hκlo,hκhi,hattained,hall⟩ := optimal_metric_bundle D A hWD
  refine ⟨hstrict,κ,hκlo,hκhi,hattained,?_⟩
  intro H hH
  obtain ⟨hp,hu,heval,hcontract,hstable,hcondition,hminimal⟩ := hall H hH
  refine ⟨hp,hu,heval,hcontract,hstable,hcondition,hminimal,?_⟩
  obtain ⟨Λ,hpos,hmass,hrep⟩ := D.common_positiveDensity_maximum_for_metric A H hWD hH.1
  refine ⟨Λ,(fun t => Matrix.nonneg_iff_posSemidef.mp (hpos t)),hmass,?_⟩
  intro m hm v hv
  obtain ⟨he,hb⟩ := hrep m hm v hv
  constructor
  · change completeAnalyticEval (CFC.sqrt H * A * (CFC.sqrt H)⁻¹) v =
      ∫ t, Λ t ⊗ₖ v (boundaryPoint G t) ∂AddCircle.haarAddCircle
    change completeAnalyticEval (CFC.sqrt H * A * (CFC.sqrt H)⁻¹) v =
      ∫ t, Λ t ⊗ₖ v ((bundleDomain hU a ha f G).G t.toCircle)
        ∂AddCircle.haarAddCircle at he
    simpa only [bundleDomain_boundaryPoint] using he
  · change ‖completeAnalyticEval A v‖ ≤
      (‖CFC.sqrt H‖ * ‖(CFC.sqrt H)⁻¹‖) * analyticSupNorm U v at hb
    rwa [hcondition] at hb

end StructuralCrouzeix
end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.StructuralCrouzeix_UnitDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
open Set Filter Metric Complex
open scoped Topology
namespace StructuralCrouzeix

theorem isAdmissible_unitDisk : IsAdmissible (ball (0 : ℂ) 1) := by
  have hfront : frontier (ball (0 : ℂ) 1) = sphere (0 : ℂ) 1 :=
    frontier_ball _ one_ne_zero
  refine ⟨isOpen_ball, isBounded_ball, convex_ball _ _,
    ⟨0, mem_ball_self zero_lt_one⟩, ?_, ?_⟩
  · change Nonempty (↥(sphere (0 : ℂ) 1) ≃ₜ ↥(frontier (ball (0 : ℂ) 1)))
    exact ⟨Homeomorph.setCongr hfront.symm⟩
  · intro p hp
    have hpn : ‖p‖ = 1 := mem_sphere_zero_iff_norm.mp (hfront ▸ hp)
    have hp0 : p ≠ 0 := by
      intro he
      simp [he] at hpn
    let χ : ℂ → ℂ := fun z => p * exp (I * z)
    have hχa : AnalyticAt ℂ χ 0 :=
      analyticAt_const.mul ((analyticAt_const.mul analyticAt_id).cexp')
    have hχd : HasDerivAt χ (p * I) 0 := by
      simpa only [χ, id_eq, mul_zero, Complex.exp_zero, one_mul, mul_one] using
        ((((hasDerivAt_id (0 : ℂ)).const_mul I).cexp).const_mul p)
    refine ⟨χ, by simp only [χ, mul_zero, Complex.exp_zero, mul_one], hχa, ?_, ?_⟩
    · rw [hχd.deriv]
      exact mul_ne_zero hp0 I_ne_zero
    · apply Filter.Eventually.of_forall
      intro z
      rw [hfront, mem_sphere_zero_iff_norm]
      change ‖p * exp (I * z)‖ = 1 ↔ z.im = 0
      rw [norm_mul, hpn, one_mul, Complex.norm_exp, Real.exp_eq_one_iff]
      simp [Complex.mul_re]
end StructuralCrouzeix
end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.StructuralCrouzeix_Endpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace StructuralCrouzeixReference
theorem challenge_oai : StructuralCrouzeix.FullEndpoint ∧
    StructuralCrouzeix.IsAdmissible (Metric.ball (0 : ℂ) 1) :=
  ⟨StructuralCrouzeix.fullEndpoint, StructuralCrouzeix.isAdmissible_unitDisk⟩
end StructuralCrouzeixReference

end OAI
end

theorem solution : type_of% @OAI.StructuralCrouzeixReference.challenge_oai := @OAI.StructuralCrouzeixReference.challenge_oai
