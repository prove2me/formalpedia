-- Prove2me | solution 1 for OAI.GaussianPropeller.HeatMaximum.heat_concave
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:10:36.400459+00:00
-- url     : https://prove2.me/submissions/3919336a-13dd-47d6-a60d-6bfec884df6c

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/HeatMaximum.lean:L416-L450
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.HeatMaximum.heat_concave. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Theorems.Thm_OAI_GaussianPropeller_HeatMaximum_min_gradient_left

-- ---- from OAI.Probability.GaussianPropeller.HeatMaximum ----
namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace

open Set Filter
open scoped Topology RealInnerProductSpace

namespace GaussianPropeller.HeatMaximum

lemma second_deriv_nonneg_of_localMin {f g : ℝ → ℝ} {d : ℝ}
    (hf : ∀ s, HasDerivAt f (g s) s) (hg : HasDerivAt g d 0)
    (hm : IsLocalMin f 0) : 0 ≤ d := by
  by_contra hd
  have hd0 : d < 0 := lt_of_not_ge hd
  have hg0 : g 0 = 0 := hm.hasDerivAt_eq_zero (hf 0)
  have ht := hg.tendsto_slope.eventually (Iio_mem_nhds hd0)
  have hne : ∀ᶠ s in 𝓝[>] (0:ℝ), g s < 0 := by
    have ht' := ht.filter_mono (nhdsWithin_mono (0:ℝ) (by
      intro x hx; exact ne_of_gt hx))
    filter_upwards [ht', self_mem_nhdsWithin] with s hs hs0
    rw [slope_def_field, hg0, sub_zero, sub_zero] at hs
    simpa only [zero_mul] using (div_lt_iff₀ (show 0 < s from hs0)).mp hs
  obtain ⟨a, ha, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hne
  obtain ⟨b, hb, hmin⟩ := Metric.mem_nhds_iff.mp hm
  let c := min a b / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hca : c < a := by dsimp [c]; have := min_le_left a b; linarith
  have hcb : c < b := by dsimp [c]; have := min_le_right a b; linarith
  have hant : StrictAntiOn f (Icc 0 c) := strictAntiOn_of_deriv_neg (convex_Icc 0 c)
    (fun x _ => (hf x).continuousAt.continuousWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      rw [(hf x).deriv]
      apply hsub
      exact ⟨by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx.1] using hx.2.trans hca,
        hx.1⟩)
  have hlt : f c < f 0 := hant (by simp [hc.le]) (by simp [hc.le]) hc
  have hge : f 0 ≤ f c := by
    apply hmin
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hc] using hcb
  exact (not_lt_of_ge hge) hlt

lemma deriv_nonpos_of_min_on_left {f : ℝ → ℝ} {a t d : ℝ} (hat : a < t)
    (hm : ∀ s ∈ Icc a t, f t ≤ f s) (hd : HasDerivAt f d t) : d ≤ 0 := by
  have ht := hd.tendsto_slope.mono_left (nhdsWithin_mono t (by
    intro s hs; exact ne_of_lt hs : Iio t ⊆ {t}ᶜ))
  apply le_of_tendsto ht
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (a := a) hat), self_mem_nhdsWithin] with s ha hs
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hm s ⟨ha.le,hs.le⟩))
    (sub_nonpos.mpr hs.le)

lemma square_norm_difference_bound {E : Type uE} [NormedAddCommGroup E]
    {p q : E} {L b r : ℝ} (_hL : 0 ≤ L) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hp : ‖p‖ ≤ L) (hq : ‖q‖ ≤ L) (hpq : ‖p-q‖ ≤ 2*b*r) :
    |‖p‖^2-‖q‖^2| ≤ 4*L*b*r := by
  have hn := abs_norm_sub_norm_le p q
  have heq : ‖p‖^2-‖q‖^2 = (‖p‖-‖q‖)*(‖p‖+‖q‖) := by ring
  rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖p‖+‖q‖)]
  calc
    _ ≤ (2*b*r)*(2*L) := mul_le_mul (hn.trans hpq) (by linarith) (by positivity) (by positivity)
    _ = _ := by ring

lemma weighted_linear_le_quadratic {a b r s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a+b=1) : a*r+b*s ≤ 1+a*r^2+b*s^2 := by
  have hr : r ≤ 1+r^2 := by nlinarith only [sq_nonneg (r-1/2)]
  have hs : s ≤ 1+s^2 := by nlinarith only [sq_nonneg (s-1/2)]
  nlinarith only [mul_le_mul_of_nonneg_left hr ha, mul_le_mul_of_nonneg_left hs hb, hab]

lemma reaction_bound {E : Type uE} [NormedAddCommGroup E]
    {p₀ p₁ p₂ : E} {a b σ L M r s v₀ v₁ v₂ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (hσ : 0 ≤ σ)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hp₀ : ‖p₀‖ ≤ L) (hp₁ : ‖p₁‖ ≤ L) (hp₂ : ‖p₂‖ ≤ L)
    (hv₁ : |v₁| ≤ M+L*r) (hv₂ : |v₂| ≤ M+L*s)
    (hp₁₀ : ‖p₀-p₁‖ ≤ 2*σ*r) (hp₂₀ : ‖p₀-p₂‖ ≤ 2*σ*s)
    (hdef : v₀-a*v₁-b*v₂+σ*(1+a*r^2+b*s^2) ≤ 0) :
    v₀*‖p₀‖^2-a*v₁*‖p₁‖^2-b*v₂*‖p₂‖^2 ≤
      4*L*σ*(M+L)*(1+a*r^2+b*s^2) := by
  have h1 := square_norm_difference_bound hL hσ hr hp₀ hp₁ hp₁₀
  have h2 := square_norm_difference_bound hL hσ hs hp₀ hp₂ hp₂₀
  have hv : v₀-a*v₁-b*v₂ ≤ 0 := by
    have : 0 ≤ σ*(1+a*r^2+b*s^2) := by positivity
    linarith only [hdef,this]
  have hh1 : v₁*(‖p₀‖^2-‖p₁‖^2) ≤ (M+L*r)*(4*L*σ*r) := by
    calc
      _ ≤ |v₁*(‖p₀‖^2-‖p₁‖^2)| := le_abs_self _
      _ = |v₁| * |‖p₀‖^2-‖p₁‖^2| := abs_mul _ _
      _ ≤ _ := mul_le_mul hv₁ h1 (abs_nonneg _) (by positivity)
  have hh2 : v₂*(‖p₀‖^2-‖p₂‖^2) ≤ (M+L*s)*(4*L*σ*s) := by
    calc
      _ ≤ |v₂*(‖p₀‖^2-‖p₂‖^2)| := le_abs_self _
      _ = |v₂| * |‖p₀‖^2-‖p₂‖^2| := abs_mul _ _
      _ ≤ _ := mul_le_mul hv₂ h2 (abs_nonneg _) (by positivity)
  have hb1 := mul_le_mul_of_nonneg_left hh1 ha
  have hb2 := mul_le_mul_of_nonneg_left hh2 hb
  have hb0 := mul_nonpos_of_nonpos_of_nonneg hv (sq_nonneg ‖p₀‖)
  have hc := weighted_linear_le_quadratic ha hb hab (r := r) (s := s)
  have hc' : M*(a*r+b*s)+L*(a*r^2+b*s^2) ≤ (M+L)*(1+a*r^2+b*s^2) := by
    nlinarith only [mul_le_mul_of_nonneg_left hc hM,hL]
  have hc'' := mul_le_mul_of_nonneg_left hc' (by positivity : 0 ≤ 4*L*σ)
  nlinarith only [hb0,hb1,hb2,hc'']

section Spatial
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasDerivAt_line {v : E → ℝ} {p : E → E}
    (hp : ∀ x, HasFDerivAt v (innerSL ℝ (p x)) x) (x e : E) (s : ℝ) :
    HasDerivAt (fun s : ℝ => v (x+s • e)) (⟪p (x+s • e),e⟫) s := by
  convert (hp (x+s • e)).comp_hasDerivAt s
    (((hasDerivAt_id s).smul_const e).const_add x) using 1 <;> first | rfl | simp

lemma min_gradient_right {v : E → ℝ} {p : E → E} {a b σ : ℝ} {x y : E}
    (hp : ∀ x, HasFDerivAt v (innerSL ℝ (p x)) x) (hb : 0 < b)
    (hm : ∀ x' y', deficit v a b σ x y ≤ deficit v a b σ x' y') :
    p (a • x+b • y)-p y = -(2*σ) • y := by
  have hs (x y : E) : deficit v b a σ y x = deficit v a b σ x y := by
    unfold deficit
    rw [add_comm (b • y) (a • x)]
    ring
  have hh := min_gradient_left hp hb (x := y) (y := x) (a := b) (b := a)
    (fun y' x' => by rw [hs,hs]; exact hm x' y')
  simpa only [add_comm (b • y) (a • x)] using hh

lemma min_hessian_diagonal {v : E → ℝ} {p : E → E} {H : E → E → ℝ}
    {a b σ : ℝ} {x y : E} (hab : a+b=1)
    (hp : ∀ x, HasFDerivAt v (innerSL ℝ (p x)) x)
    (hH : ∀ x e, HasDerivAt (fun s : ℝ => ⟪p (x+s • e),e⟫) (H x e) 0)
    (hm : ∀ x' y', deficit v a b σ x y ≤ deficit v a b σ x' y') (e : E) :
    0 ≤ H (a • x+b • y) e-a*H x e-b*H y e+2*σ*‖e‖^2 := by
  let z := a • x+b • y
  have hz (s : ℝ) : a • (x+s • e)+b • (y+s • e) = z+s • e := by
    dsimp only [z]
    simp only [smul_add, smul_smul]
    rw [add_add_add_comm, ← add_smul, ← add_mul, hab, one_mul]
  let F (s : ℝ) := v (z+s • e)-a*v (x+s • e)-b*v (y+s • e)+
    σ*(1+a*‖x+s • e‖^2+b*‖y+s • e‖^2)
  let G (s : ℝ) := ⟪p (z+s • e),e⟫-a*⟪p (x+s • e),e⟫-b*⟪p (y+s • e),e⟫+
    σ*(a*(2*⟪x+s • e,e⟫)+b*(2*⟪y+s • e,e⟫))
  have hf (s : ℝ) : HasDerivAt F (G s) s := by
    have hx := (((hasDerivAt_id s).smul_const e).const_add x).norm_sq
    have hy := (((hasDerivAt_id s).smul_const e).const_add y).norm_sq
    convert (((hasDerivAt_line hp z e s).sub ((hasDerivAt_line hp x e s).const_mul a)).sub
      ((hasDerivAt_line hp y e s).const_mul b)).add
      ((((hx.const_mul a).const_add 1).add (hy.const_mul b)).const_mul σ) using 1 <;>
      first | rfl | simp [G]
  have hi (x : E) : HasDerivAt (fun s : ℝ => ⟪x+s • e,e⟫) (‖e‖^2) 0 := by
    convert ((((hasDerivAt_id (0:ℝ)).smul_const e).const_add x).inner (𝕜 := ℝ)
      (hasDerivAt_const (0:ℝ) e)) using 1 <;> first | rfl | simp
  have hg : HasDerivAt G (H z e-a*H x e-b*H y e+2*σ*‖e‖^2) 0 := by
    convert (((hH z e).sub ((hH x e).const_mul a)).sub ((hH y e).const_mul b)).add
      ((((hi x).const_mul 2 |>.const_mul a).add ((hi y).const_mul 2 |>.const_mul b)).const_mul σ) using 1
    all_goals first | rfl | (have hh := congrArg (fun u : ℝ => 2*σ*‖e‖^2*u) hab; nlinarith only [hh])
  have hmin : IsLocalMin F 0 := by
    apply Filter.Eventually.of_forall
    intro s
    simpa only [deficit,hz,zero_smul,add_zero,F,z] using hm (x+s • e) (y+s • e)
  exact second_deriv_nonneg_of_localMin hf hg hmin

lemma min_laplacian_bound {ι : Type uι} [Fintype ι] (basis : ι → E)
    (hbasis : ∀ i, ‖basis i‖ = 1)
    {v : E → ℝ} {p : E → E} {H : E → E → ℝ}
    {a b σ : ℝ} {x y : E} (hab : a+b=1)
    (hp : ∀ x, HasFDerivAt v (innerSL ℝ (p x)) x)
    (hH : ∀ x e, HasDerivAt (fun s : ℝ => ⟪p (x+s • e),e⟫) (H x e) 0)
    (hm : ∀ x' y', deficit v a b σ x y ≤ deficit v a b σ x' y') :
    -2*σ*(Fintype.card ι : ℝ) ≤
      (∑ i, H (a • x+b • y) (basis i))-a*(∑ i, H x (basis i))-b*(∑ i, H y (basis i)) := by
  have hh := Finset.sum_nonneg (fun (i : ι) (_ : i ∈ Finset.univ) =>
    min_hessian_diagonal hab hp hH hm (basis i))
  simp only [hbasis,one_pow,mul_one,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  linarith only [hh]

lemma no_forbidden_minimum {ι : Type uι} [Fintype ι] (basis : ι → E)
    (hbasis : ∀ i, ‖basis i‖ = 1)
    {v : ℝ → E → ℝ} {p : E → E} {H : E → E → ℝ} {σf : ℝ → ℝ}
    {a b L M t : ℝ} {x y : E} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (ht : 0 < t) (hσ : 0 < σf t)
    (hp : ∀ x, HasFDerivAt (v t) (innerSL ℝ (p x)) x)
    (hH : ∀ x e, HasDerivAt (fun s : ℝ => ⟪p (x+s • e),e⟫) (H x e) 0)
    (hvt : ∀ x, HasDerivAt (fun s => v s x)
      (((∑ i, H x (basis i))-v t x*‖p x‖^2)/2) t)
    (hσt : HasDerivAt σf (((Fintype.card ι : ℝ)+2*L*(M+L)+1)*σf t) t)
    (hpbound : ∀ x, ‖p x‖ ≤ L) (hvbound : ∀ x, |v t x| ≤ M+L*‖x‖)
    (hm : ∀ x' y', deficit (v t) a b (σf t) x y ≤ deficit (v t) a b (σf t) x' y')
    (hmTime : ∀ s ∈ Icc 0 t, deficit (v t) a b (σf t) x y ≤ deficit (v s) a b (σf s) x y)
    (hneg : deficit (v t) a b (σf t) x y ≤ 0) : False := by
  let z := a • x+b • y
  have hx := min_gradient_left hp ha hm
  have hy := min_gradient_right hp hb hm
  have hxnorm : ‖p z-p x‖ ≤ 2*(σf t)*‖x‖ := by
    rw [hx,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos (by positivity)]
  have hynorm : ‖p z-p y‖ ≤ 2*(σf t)*‖y‖ := by
    rw [hy,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos (by positivity)]
  have hr := reaction_bound ha.le hb.le hab hσ.le hL hM (norm_nonneg x) (norm_nonneg y)
    (hpbound z) (hpbound x) (hpbound y) (hvbound x) (hvbound y) hxnorm hynorm hneg
  have hl := min_laplacian_bound basis hbasis hab hp hH hm
  have hd : HasDerivAt (fun s => deficit (v s) a b (σf s) x y)
      ((((∑ i, H z (basis i))-v t z*‖p z‖^2)/2) -
       a*(((∑ i, H x (basis i))-v t x*‖p x‖^2)/2) -
       b*(((∑ i, H y (basis i))-v t y*‖p y‖^2)/2) +
       (((Fintype.card ι : ℝ)+2*L*(M+L)+1)*σf t)*(1+a*‖x‖^2+b*‖y‖^2)) t := by
    exact (((hvt z).sub ((hvt x).const_mul a)).sub ((hvt y).const_mul b)).add
      (hσt.mul_const _)
  have hnonpos := deriv_nonpos_of_min_on_left ht hmTime hd
  have hQ : 0 ≤ a*‖x‖^2+b*‖y‖^2 := by positivity
  have hcard : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hσQ : 0 ≤ σf t*(a*‖x‖^2+b*‖y‖^2) := mul_nonneg hσ.le hQ
  have hcardQ : 0 ≤ (Fintype.card ι : ℝ)*(σf t*(a*‖x‖^2+b*‖y‖^2)) :=
    mul_nonneg hcard hσQ
  change -2*(σf t)*(Fintype.card ι : ℝ) ≤
    (∑ i, H z (basis i))-a*(∑ i, H x (basis i))-b*(∑ i, H y (basis i)) at hl
  nlinarith only [hr,hl,hnonpos,hσ,hσQ,hcardQ]

lemma deficit_lower {v : E → ℝ} {a b σ L M ε : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (hL : 0 ≤ L)
    (hε : 0 < ε) (hσε : ε ≤ σ) (hv : ∀ x, |v x| ≤ M+L*‖x‖) (x y : E) :
    ε/2*(a*‖x‖^2+b*‖y‖^2)-2*M-2*L^2/ε ≤ deficit v a b σ x y := by
  have hnz : ‖a • x+b • y‖ ≤ a*‖x‖+b*‖y‖ := by
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb] using norm_add_le (a • x) (b • y)
  have hvz := (abs_le.mp (hv (a • x+b • y))).1
  have hvx := (abs_le.mp (hv x)).2
  have hvy := (abs_le.mp (hv y)).2
  have hvz' : -(M+L*(a*‖x‖+b*‖y‖)) ≤ v (a • x+b • y) := by
    nlinarith only [hvz,mul_le_mul_of_nonneg_left hnz hL]
  have hQ : 0 ≤ a*‖x‖^2+b*‖y‖^2 := by positivity
  have hbarr := mul_le_mul_of_nonneg_right hσε (by positivity : 0 ≤ 1+a*‖x‖^2+b*‖y‖^2)
  have hYoung (r : ℝ) : 2*L*r ≤ ε/2*r^2+2*L^2/ε := by
    have hid : ε/2*r^2+2*L^2/ε-2*L*r = (ε*r-2*L)^2/(2*ε) := by
      field_simp
      ring
    have hh := div_nonneg (sq_nonneg (ε*r-2*L)) (by positivity : 0 ≤ 2*ε)
    rw [← hid] at hh
    linarith only [hh]
  have hx := mul_le_mul_of_nonneg_left (hYoung ‖x‖) ha
  have hy := mul_le_mul_of_nonneg_left (hYoung ‖y‖) hb
  have hi : (a+b)*(2*L^2/ε) = 2*L^2/ε := by rw [hab,one_mul]
  have hMab := congrArg (fun u : ℝ => M*u) hab
  unfold deficit
  nlinarith only [hMab,hvz',mul_le_mul_of_nonneg_left hvx ha,mul_le_mul_of_nonneg_left hvy hb,
    hbarr,hx,hy,hi,hε]

omit [InnerProductSpace ℝ E] in
lemma exists_negative_minimum [InnerProductSpace ℝ E] [ProperSpace E]
    {F : ℝ → E → E → ℝ} {T R : ℝ} {x₀ y₀ : E}
    (hF : Continuous (fun q : ℝ × E × E => F q.1 q.2.1 q.2.2))
    (hT : 0 ≤ T) (hnegative : F T x₀ y₀ < 0)
    (hinitial : ∀ x y, 0 ≤ F 0 x y)
    (hcoercive : ∀ t ∈ Icc 0 T, ∀ x y,
      R ≤ ‖x‖ ∨ R ≤ ‖y‖ → 0 ≤ F t x y) :
    ∃ t ∈ Ioc 0 T, ∃ x y, F t x y < 0 ∧
      (∀ x' y', F t x y ≤ F t x' y') ∧
      (∀ s ∈ Icc 0 t, F t x y ≤ F s x y) := by
  let K := Icc 0 T ×ˢ (Metric.closedBall (0:E) R ×ˢ Metric.closedBall (0:E) R)
  have hx₀ : ‖x₀‖ ≤ R := by
    by_contra hh
    exact (not_lt_of_ge (hcoercive T ⟨hT,le_rfl⟩ x₀ y₀ (Or.inl (le_of_not_ge hh)))) hnegative
  have hy₀ : ‖y₀‖ ≤ R := by
    by_contra hh
    exact (not_lt_of_ge (hcoercive T ⟨hT,le_rfl⟩ x₀ y₀ (Or.inr (le_of_not_ge hh)))) hnegative
  have hmem : (T,x₀,y₀) ∈ K := by
    exact ⟨⟨hT,le_rfl⟩, by simpa using hx₀, by simpa using hy₀⟩
  have hK : IsCompact K := isCompact_Icc.prod ((isCompact_closedBall (0:E) R).prod (isCompact_closedBall (0:E) R))
  obtain ⟨w, hw, hmin⟩ := hK.exists_isMinOn ⟨_,hmem⟩ hF.continuousOn
  have hn : F w.1 w.2.1 w.2.2 < 0 := (hmin hmem).trans_lt hnegative
  have ht0 : 0 < w.1 := by
    have ht : 0 ≤ w.1 := hw.1.1
    rcases ht.eq_or_lt with ht' | ht'
    · have hh := hinitial w.2.1 w.2.2
      rw [← ht'] at hn
      exact (not_lt_of_ge hh hn).elim
    · exact ht'
  refine ⟨w.1,⟨ht0,hw.1.2⟩,w.2.1,w.2.2,hn,?_,?_⟩
  · intro x y
    by_cases hx : ‖x‖ ≤ R
    · by_cases hy : ‖y‖ ≤ R
      · apply hmin (a := (w.1,x,y))
        exact ⟨hw.1,by simpa using hx,by simpa using hy⟩
      · exact hn.le.trans (hcoercive w.1 hw.1 x y (Or.inr (le_of_not_ge hy)))
    · exact hn.le.trans (hcoercive w.1 hw.1 x y (Or.inl (le_of_not_ge hx)))
  · intro s hs
    apply hmin (a := (s,w.2.1,w.2.2))
    exact ⟨⟨hs.1,hs.2.trans hw.1.2⟩,hw.2⟩

lemma deficit_coercive_radius {a b ε L M : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a+b=1) (hε : 0 < ε) (hL : 0 ≤ L) (hM : 0 ≤ M) :
    ∃ R : ℝ, ∀ (v : E → ℝ) (σ : ℝ), ε ≤ σ →
      (∀ x, |v x| ≤ M+L*‖x‖) → ∀ x y,
      R ≤ ‖x‖ ∨ R ≤ ‖y‖ → 0 ≤ deficit v a b σ x y := by
  let δ := min a b
  have hδ : 0 < δ := lt_min ha hb
  let C := 2*M+2*L^2/ε+1
  have hC : 0 < C := by dsimp only [C]; positivity
  let R := Real.sqrt (2*C/(ε*δ))
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R^2 = 2*C/(ε*δ) := Real.sq_sqrt (by positivity)
  have hid : ε/2*δ*R^2-2*M-2*L^2/ε = 1 := by
    rw [hR2]
    dsimp only [C]
    field_simp
    ring
  refine ⟨R,?_⟩
  intro v σ hσε hv x y hout
  have hQ : δ*R^2 ≤ a*‖x‖^2+b*‖y‖^2 := by
    rcases hout with hx | hy
    · have hsq : R^2 ≤ ‖x‖^2 := sq_le_sq₀ hR (norm_nonneg x) |>.mpr hx
      nlinarith only [mul_le_mul_of_nonneg_left hsq hδ.le,
        mul_le_mul_of_nonneg_right (min_le_left a b) (sq_nonneg ‖x‖),
        mul_nonneg hb.le (sq_nonneg ‖y‖)]
    · have hsq : R^2 ≤ ‖y‖^2 := sq_le_sq₀ hR (norm_nonneg y) |>.mpr hy
      nlinarith only [mul_le_mul_of_nonneg_left hsq hδ.le,
        mul_le_mul_of_nonneg_right (min_le_right a b) (sq_nonneg ‖y‖),
        mul_nonneg ha.le (sq_nonneg ‖x‖)]
  have hh := deficit_lower ha.le hb.le hab hL hε hσε hv x y
  have hh' := mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ ε/2)
  nlinarith only [hh,hh',hid]

lemma heat_deficit_nonneg [ProperSpace E] {ι : Type uι} [Fintype ι] (basis : ι → E)
    (hbasis : ∀ i, ‖basis i‖ = 1)
    {v : ℝ → E → ℝ} {p : ℝ → E → E} {H : ℝ → E → E → ℝ}
    {T a b ε L M : ℝ} (hT : 0 ≤ T) (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hε : 0 < ε) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hv : Continuous (fun q : ℝ × E => v q.1 q.2))
    (hinitial : ConcaveOn ℝ univ (v 0))
    (hp : ∀ t ∈ Ioc 0 T, ∀ x, HasFDerivAt (v t) (innerSL ℝ (p t x)) x)
    (hH : ∀ t ∈ Ioc 0 T, ∀ x e, HasDerivAt (fun s : ℝ => ⟪p t (x+s • e),e⟫) (H t x e) 0)
    (hvt : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivAt (fun s => v s x)
      (((∑ i, H t x (basis i))-v t x*‖p t x‖^2)/2) t)
    (hpbound : ∀ t ∈ Ioc 0 T, ∀ x, ‖p t x‖ ≤ L)
    (hvbound : ∀ t ∈ Icc 0 T, ∀ x, |v t x| ≤ M+L*‖x‖) (x y : E) :
    0 ≤ deficit (v T) a b (ε*Real.exp (((Fintype.card ι : ℝ)+2*L*(M+L)+1)*T)) x y := by
  let A := (Fintype.card ι : ℝ)+2*L*(M+L)+1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let σf (t : ℝ) := ε*Real.exp (A*t)
  have hσcont : Continuous σf := by dsimp [σf]; fun_prop
  have hσpos (t : ℝ) : 0 < σf t := by dsimp [σf]; positivity
  have hσlower {t : ℝ} (ht : 0 ≤ t) : ε ≤ σf t := by
    have hh := Real.one_le_exp_iff.mpr (mul_nonneg hA ht)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hε.le
  have hσt (t : ℝ) : HasDerivAt σf (A*σf t) t := by
    convert ((((hasDerivAt_id t).const_mul A).exp).const_mul ε) using 1 <;>
      first | rfl | (dsimp [σf]; ring)
  obtain ⟨R,hR⟩ := deficit_coercive_radius (E := E) ha hb hab hε hL hM
  let F (t : ℝ) (x y : E) := deficit (v t) a b (σf t) x y
  have hF : Continuous (fun q : ℝ × E × E => F q.1 q.2.1 q.2.2) := by
    have hz : Continuous (fun q : ℝ × E × E => v q.1 (a • q.2.1+b • q.2.2)) :=
      hv.comp (show Continuous (fun q : ℝ × E × E => (q.1,a • q.2.1+b • q.2.2)) from by fun_prop)
    have hx : Continuous (fun q : ℝ × E × E => v q.1 q.2.1) := hv.comp (show Continuous (fun q : ℝ × E × E => (q.1,q.2.1)) from by fun_prop)
    have hy : Continuous (fun q : ℝ × E × E => v q.1 q.2.2) := hv.comp (show Continuous (fun q : ℝ × E × E => (q.1,q.2.2)) from by fun_prop)
    dsimp only [F,deficit]
    fun_prop
  have hi (x y : E) : 0 ≤ F 0 x y := by
    have hh := hinitial.2 (mem_univ x) (mem_univ y) ha.le hb.le hab
    simp only [smul_eq_mul] at hh
    have hh' : 0 ≤ σf 0*(1+a*‖x‖^2+b*‖y‖^2) := by positivity
    dsimp only [F,deficit]
    linarith only [hh,hh']
  have hc (t : ℝ) (ht : t ∈ Icc 0 T) (x y : E) (hout : R ≤ ‖x‖ ∨ R ≤ ‖y‖) :
      0 ≤ F t x y := hR (v t) (σf t) (hσlower ht.1) (hvbound t ht) x y hout
  by_contra hneg
  obtain ⟨t,ht,x',y',hn,hm,hmt⟩ := exists_negative_minimum hF hT (lt_of_not_ge hneg) hi hc
  exact no_forbidden_minimum basis hbasis ha hb hab hL hM ht.1 (hσpos t)
    (hp t ht) (hH t ht) (hvt t ht) (hσt t) (hpbound t ht) (hvbound t ⟨ht.1.le,ht.2⟩)
    hm hmt hn.le

lemma heat_concave [ProperSpace E] {ι : Type uι} [Fintype ι] (basis : ι → E)
    (hbasis : ∀ i, ‖basis i‖ = 1)
    {v : ℝ → E → ℝ} {p : ℝ → E → E} {H : ℝ → E → E → ℝ}
    {T L M : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hv : Continuous (fun q : ℝ × E => v q.1 q.2))
    (hinitial : ConcaveOn ℝ univ (v 0))
    (hp : ∀ t ∈ Ioc 0 T, ∀ x, HasFDerivAt (v t) (innerSL ℝ (p t x)) x)
    (hH : ∀ t ∈ Ioc 0 T, ∀ x e, HasDerivAt (fun s : ℝ => ⟪p t (x+s • e),e⟫) (H t x e) 0)
    (hvt : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivAt (fun s => v s x)
      (((∑ i, H t x (basis i))-v t x*‖p t x‖^2)/2) t)
    (hpbound : ∀ t ∈ Ioc 0 T, ∀ x, ‖p t x‖ ≤ L)
    (hvbound : ∀ t ∈ Icc 0 T, ∀ x, |v t x| ≤ M+L*‖x‖) :
    ConcaveOn ℝ univ (v T) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  rcases ha.eq_or_lt with rfl | ha
  · have hb1 : b=1 := by linarith only [hab]
    simp [hb1]
  rcases hb.eq_or_lt with rfl | hb
  · have ha1 : a=1 := by linarith only [hab]
    simp [ha1]
  by_contra hbad
  have hbad' : 0 < a*v T x+b*v T y-v T (a • x+b • y) := by linarith only [lt_of_not_ge hbad]
  let c := Real.exp (((Fintype.card ι : ℝ)+2*L*(M+L)+1)*T)*(1+a*‖x‖^2+b*‖y‖^2)
  have hc : 0 < c := by dsimp only [c]; positivity
  let ε := (a*v T x+b*v T y-v T (a • x+b • y))/(2*c)
  have hε : 0 < ε := div_pos hbad' (by positivity)
  have hh := heat_deficit_nonneg basis hbasis hT ha hb hab hε hL hM hv hinitial hp hH hvt hpbound hvbound x y
  have heq : ε*c = (a*v T x+b*v T y-v T (a • x+b • y))/2 := by
    dsimp only [ε]
    field_simp
  dsimp only [deficit] at hh
  dsimp only [c] at heq
  nlinarith only [hh,heq,hbad']

end Spatial
end GaussianPropeller.HeatMaximum

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.HeatMaximum
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace


theorem solution.{uE,uι} : type_of% @_root_.OAI.GaussianPropeller.HeatMaximum.heat_concave.{uE,uι} := @_root_.OAI.GaussianPropeller.HeatMaximum.heat_concave.{uE,uι}
