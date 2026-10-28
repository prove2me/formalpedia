-- Prove2me | solution 1 for OAI.SmoothObstruction.ManifoldCoordinates.gauge_original_germ_sharp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:17:46.541449+00:00
-- url     : https://prove2.me/submissions/34184c34-0219-426f-90cb-a2e09649cfbb

import Mathlib
import Definitions.Def_OAIQ5T3000
import Theorems.Thm_OAI_SmoothObstruction_EuclideanSplitting_endpoint_bounds
import Theorems.Thm_OAI_SmoothObstruction_ManifoldCoordinates_family_original_germ_uniform

section
-- module Solutions.OAIQ5_T3.Compat
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_ExteriorPowers
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped ContDiff BigOperators
open Module

namespace SmoothObstruction.ExteriorStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Exterior powers depend smoothly on the input operator. -/
theorem contDiff_exterior (p : ℕ) :
    ContDiff ℝ ∞ (exterior (E := E) p) := by
  apply contDiff_clm_apply_iff.mpr
  intro v
  have hv : v ∈ Submodule.span ℝ (Set.range (exteriorPower.ιMulti ℝ p (M := E))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, rfl⟩ := hv
    simp only [exterior_apply, exteriorPower.map_apply_ιMulti]
    apply (contDiff_wedge p).comp
    exact contDiff_pi.mpr fun i => contDiff_id.clm_apply contDiff_const
  | zero => simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : E →L[ℝ] E => (0 : ⋀[ℝ]^p E)))
  | add x y hx hy ihx ihy => simpa only [map_add] using ihx.add ihy
  | smul a x hx ih => simpa only [map_smul] using ih.const_smul a

/-- A uniform one-step exterior error on every bounded operator ball. -/
theorem exists_exterior_lipschitz (p : ℕ) (K : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A B : E →L[ℝ] E),
      ‖A‖ ≤ K → ‖B - A‖ ≤ 1 →
      ‖exterior p B - exterior p A‖ ≤ C * ‖B - A‖ := by
  obtain ⟨C, hC⟩ := (contDiff_exterior (E := E) p).contDiffOn.exists_lipschitzOnWith
    (by simp) (convex_closedBall (0 : E →L[ℝ] E) (K + 1)) (isCompact_closedBall 0 (K + 1))
  refine ⟨C, C.coe_nonneg, fun A B hA hBA => ?_⟩
  have hB : ‖B‖ ≤ K + 1 := by
    calc
      ‖B‖ = ‖(B - A) + A‖ := by rw [sub_add_cancel]
      _ ≤ ‖B - A‖ + ‖A‖ := norm_add_le _ _
      _ ≤ K + 1 := by linarith
  have hAmem : A ∈ Metric.closedBall (0 : E →L[ℝ] E) (K + 1) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hA.trans (by linarith)
  have hBmem : B ∈ Metric.closedBall (0 : E →L[ℝ] E) (K + 1) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hB
  simpa only [dist_eq_norm] using hC.dist_le_mul B hBmem A hAmem

/-- The same one-step constant works for every exterior degree up to `d`. -/
theorem exists_uniform_exterior_lipschitz (d : ℕ) (K : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℕ), p ≤ d → ∀ (A B : E →L[ℝ] E),
      ‖A‖ ≤ K → ‖B - A‖ ≤ 1 →
      ‖exterior p B - exterior p A‖ ≤ C * ‖B - A‖ := by
  choose C hCpos hC using fun p : Fin (d + 1) => exists_exterior_lipschitz (E := E) p.val K
  refine ⟨∑ p, C p, Finset.sum_nonneg (fun p _ => hCpos p), ?_⟩
  intro p hp A B hA hBA
  let q : Fin (d + 1) := ⟨p, by omega⟩
  have hle : C q ≤ ∑ i, C i := Finset.single_le_sum (fun i _ => hCpos i) (Finset.mem_univ q)
  exact (hC q A B hA hBA).trans (mul_le_mul_of_nonneg_right hle (norm_nonneg _))

end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.ExteriorStability
open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exterior_smul (p : ℕ) (c : ℝ) (A : E →L[ℝ] E) :
    exterior p (c • A)=c^p • exterior p A := by
  apply ContinuousLinearMap.coe_injective
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change exteriorPower.map p (c • A).toLinearMap (exteriorPower.ιMulti ℝ p v) =
    c^p • exteriorPower.map p A.toLinearMap (exteriorPower.ιMulti ℝ p v)
  simp only [exteriorPower.map_apply_ιMulti,Function.comp_def,
    ContinuousLinearMap.coe_coe,smul_apply]
  simpa using (exteriorPower.ιMulti ℝ p (M:=E)).map_smul_univ (fun _ => c) (fun i => A (v i))

/-- A fixed dimensional polynomial bound sufficient to absorb changes of
gauge into the source's exp(Cbn) factor, with exterior degree zero included. -/
theorem exists_power_bound (p : ℕ) : ∃ C : ℝ,1≤C ∧ ∀ A : E →L[ℝ] E,
    ‖exterior p A‖≤C*(max 1 ‖A‖)^p := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : E →L[ℝ] E) 1).exists_bound_of_continuousOn
    (f:=exterior (E:=E) p) (contDiff_exterior p).continuous.continuousOn
  refine ⟨max C 1,le_max_right _ _,?_⟩
  intro A
  let r := max 1 ‖A‖
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hAr : ‖r⁻¹ • A‖≤1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_iff₀ hr).mpr (by simpa only [mul_one] using le_max_right (1:ℝ) ‖A‖)
  have ha := hC (r⁻¹ • A) (by simpa only [mem_closedBall,dist_zero_right] using hAr)
  have he : A=r • (r⁻¹ • A) := by rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  calc
    _ = ‖r^p • exterior p (r⁻¹ • A)‖ := by
      congr 1
      conv_lhs => rw [he,exterior_smul]
    _ ≤ r^p*‖exterior p (r⁻¹ • A)‖ := by
      simpa only [Real.norm_eq_abs,abs_of_pos (pow_pos hr p)] using
        ContinuousLinearMap.opNorm_smul_le (r^p) (exterior p (r⁻¹ • A))
    _ ≤ r^p*(max C 1) := mul_le_mul_of_nonneg_left (ha.trans (le_max_left _ _)) (pow_nonneg hr.le p)
    _ = _ := by ring

variable {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ E] in
/-- A convenient basis norm bound; no singular-value theorem is needed. -/
lemma norm_le_sum_basis (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) :
    ‖T‖≤∑ i,‖T (b i)‖ := by
  classical
  apply T.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro x
  have hrepr : x=∑ i,(b.repr x i) • b i := (b.sum_repr x).symm
  calc
    ‖T x‖ = ‖∑ i,(b.repr x i) • T (b i)‖ := by
      conv_lhs => rw [hrepr]
      simp only [map_sum,map_smul]
    _ ≤ ∑ i,‖(b.repr x i) • T (b i)‖ := norm_sum_le _ _
    _ ≤ ∑ i,‖x‖*‖T (b i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,b.repr_apply_apply]
      have hh := norm_inner_le_norm (𝕜:=ℝ) (b i) x
      rw [b.norm_eq_one,one_mul] at hh
      exact mul_le_mul_of_nonneg_right hh (norm_nonneg _)
    _ = _ := by rw [←Finset.mul_sum]; ring

variable [LinearOrder ι]

lemma exterior_eigen_basis (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (T : E →L[ℝ] E) (a : ι → ℝ) (ha : ∀ i,T (b i)=a i • b i)
    (s : powersetCard ι p) : exterior p T ((b.exteriorPower p) s)=
      (∏ i : Fin p,a (powersetCard.ofFinEmbEquiv.symm s i)) • ((b.exteriorPower p) s) := by
  have hb : (b.exteriorPower p) s=exteriorPower.ιMulti ℝ p
      (fun i => b (powersetCard.ofFinEmbEquiv.symm s i)) := by
    change (b.exteriorPower p).toBasis s=_
    rw [b.toBasis_exteriorPower,exteriorPower.coe_basis]
    rfl
  rw [hb,exterior_apply,exteriorPower.map_apply_ιMulti]
  simp only [Function.comp_def,ContinuousLinearMap.coe_coe,ha]
  exact (exteriorPower.ιMulti ℝ p (M:=E)).map_smul_univ _ _

/-- The complete exterior product estimate in a diagonal gauge depends on
the SUM of selected rates, not on a coarser maximum single rate. -/
lemma exterior_diagonal_bound (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (T : E →L[ℝ] E) (a : ι → ℝ) (ha : ∀ i,T (b i)=a i • b i)
    {K : ℝ} (hK : ∀ s : powersetCard ι p,
      |∏ i : Fin p,a (powersetCard.ofFinEmbEquiv.symm s i)|≤K) :
    ‖exterior p T‖≤(Fintype.card (powersetCard ι p):ℝ)*K := by
  apply (norm_le_sum_basis (b.exteriorPower p) (exterior p T)).trans
  calc
    _ ≤ ∑ _s : powersetCard ι p,K := by
      apply Finset.sum_le_sum
      intro s _
      rw [exterior_eigen_basis b p T a ha s,norm_smul,(b.exteriorPower p).norm_eq_one,mul_one,Real.norm_eq_abs]
      exact hK s
    _ = _ := by simp
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.ExteriorStability
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

omit [Fintype ι] in
lemma eigen_exp_product (p : ℕ) (lam : ι → ℝ) (l : ℝ) (s : powersetCard ι p) :
    (∏ i : Fin p,Real.exp (l*lam (powersetCard.ofFinEmbEquiv.symm s i))) =
      Real.exp (l*∑ i : Fin p,lam (powersetCard.ofFinEmbEquiv.symm s i)) := by
  rw [Finset.mul_sum,Real.exp_sum]

lemma exterior_rate_upper (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (D : E →L[ℝ] E) (lam : ι → ℝ) {l Λ : ℝ} (hl : 0≤l)
    (ha : ∀ i,D (b i)=Real.exp (l*lam i) • b i)
    (hm : ∀ s : powersetCard ι p,∑ i : Fin p,lam (powersetCard.ofFinEmbEquiv.symm s i)≤Λ) :
    ‖exterior p D‖≤(Fintype.card (powersetCard ι p):ℝ)*Real.exp (l*Λ) := by
  apply exterior_diagonal_bound b p D _ ha
  intro s
  rw [eigen_exp_product,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hm s) hl)

/-- An explicit subinterval exterior bound after changing a finite gauge.
This allows negative Λ, so that it is suitable for relative minor transfer. -/
theorem exterior_gauge_bound (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (U V D : E →L[ℝ] E) (lam : ι → ℝ) {l Λ G C : ℝ}
    (hl : 0≤l) (hG : 1≤G) (hC : 0≤C)
    (hpoly : ∀ A : E →L[ℝ] E,‖exterior p A‖≤C*(max 1 ‖A‖)^p)
    (hU : ‖U‖≤G) (hV : ‖V‖≤G)
    (ha : ∀ i,D (b i)=Real.exp (l*lam i) • b i)
    (hm : ∀ s : powersetCard ι p,∑ i : Fin p,lam (powersetCard.ofFinEmbEquiv.symm s i)≤Λ) :
    ‖exterior p (U*D*V)‖≤C^2*G^(2*p)*
      (Fintype.card (powersetCard ι p):ℝ)*Real.exp (l*Λ) := by
  have hGU : ‖exterior p U‖≤C*G^p := (hpoly U).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (max_le hG hU) p) hC)
  have hGV : ‖exterior p V‖≤C*G^p := (hpoly V).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (max_le hG hV) p) hC)
  have hD := exterior_rate_upper b p D lam hl ha hm
  rw [exterior_mul,exterior_mul]
  calc
    _ ≤ ‖exterior p U‖*‖exterior p D‖*‖exterior p V‖ :=
      (ContinuousLinearMap.opNorm_comp_le (exterior p U * exterior p D) (exterior p V)).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le (exterior p U) (exterior p D))
          (ContinuousLinearMap.opNorm_nonneg _))
    _ ≤ (C*G^p)*((Fintype.card (powersetCard ι p):ℝ)*Real.exp (l*Λ))*(C*G^p) := by
      apply mul_le_mul (mul_le_mul hGU hD (ContinuousLinearMap.opNorm_nonneg _) (by positivity)) hGV
        (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
    _ = _ := by rw [show 2*p=p+p by omega,pow_add]; ring

end SmoothObstruction.ExteriorStability

end

section

namespace SmoothObstruction.RateSums
open Finset
variable {ι : Type*} [DecidableEq ι]

lemma sdiff_card_eq {S F : Finset ι} (hcard : S.card=F.card) :
    (S\F).card=(F\S).card := by
  have hS := card_sdiff_add_card_inter S F
  have hF := card_sdiff_add_card_inter F S
  rw [inter_comm F S] at hF
  omega

/-- Every nonfast minor of maximal fast degree loses at least two gap units.
Nothing here requires positive fast rates or negative slow rates. -/
theorem strict_rate_sum_gap (lam : ι → ℝ) (F S : Finset ι)
    {γ g : ℝ} (hg : 0≤g) (hcard : S.card=F.card) (hne : S≠F)
    (hf : ∀ j∈F,γ+g≤lam j) (hs : ∀ j∉F,lam j≤γ-g) :
    ∑ j∈S,lam j ≤ (∑ j∈F,lam j)-2*g := by
  have hc : (S\F).card=(F\S).card := sdiff_card_eq hcard
  have hnon : (S\F).Nonempty := by
    by_contra hh
    have hempty := not_nonempty_iff_eq_empty.mp hh
    have hsub := sdiff_eq_empty_iff_subset.mp hempty
    exact hne (eq_of_subset_of_card_le hsub (by omega))
  have hcp : 1≤((S\F).card:ℝ) := by
    exact_mod_cast hnon.card_pos
  have hslow : ∑ j∈S\F,lam j≤(S\F).card*(γ-g) := by
    calc
      _ ≤ ∑ _j∈S\F,(γ-g) := sum_le_sum fun j hj => hs j (mem_sdiff.mp hj).2
      _ = _ := by simp; ring
  have hfast : (S\F).card*(γ+g)≤∑ j∈F\S,lam j := by
    rw [hc]
    calc
      _ = ∑ _j∈F\S,(γ+g) := by simp; ring
      _ ≤ _ := sum_le_sum fun j hj => hf j (mem_sdiff.mp hj).1
  have hS := sum_sdiff (s₁:=S∩F) (s₂:=S) (inter_subset_left) (f:=lam)
  have hF := sum_sdiff (s₁:=S∩F) (s₂:=F) (inter_subset_right) (f:=lam)
  have hdS : S\(S∩F)=S\F := by ext j; simp
  have hdF : F\(S∩F)=F\S := by ext j; simp
  rw [hdS] at hS
  rw [hdF] at hF
  nlinarith [mul_nonneg (sub_nonneg.mpr hcp) hg]

theorem rate_sum_max (lam : ι → ℝ) (F S : Finset ι)
    {γ g : ℝ} (hg : 0≤g) (hcard : S.card=F.card)
    (hf : ∀ j∈F,γ+g≤lam j) (hs : ∀ j∉F,lam j≤γ-g) :
    ∑ j∈S,lam j ≤ ∑ j∈F,lam j := by
  by_cases he : S=F
  · simp [he]
  · exact (strict_rate_sum_gap lam F S hg hcard he hf hs).trans (by linarith)
end SmoothObstruction.RateSums

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_Splitting
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.EuclideanSplitting
variable {d : ℕ}

lemma transition_one_step (A U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (hUV : ∀ t, U t*V t=1) (t : ℕ)
    (hA : A t*U t=U (t+1)*rate lam 1) :
    A t=transition U V lam t (t+1) := by
  have ht : ((t+1:ℕ):ℝ)-t=1 := by push_cast; ring
  dsimp [transition]
  rw [ht]
  calc
    _ = (A t*U t)*V t := by rw [mul_assoc,hUV,mul_one]
    _ = _ := by rw [hA]

lemma propagator_eq_transition (A U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (hUV : ∀ t, U t*V t=1) (hVU : ∀ t, V t*U t=1)
    (N : ℕ) (hA : ∀ t < N, A t*U t=U (t+1)*rate lam 1)
    (s l : ℕ) (hl : s+l ≤ N) :
    propagator A s l=transition U V lam s (s+l) := by
  induction l with
  | zero => simpa only [Nat.add_zero,propagator] using (transition_self U V lam hUV s).symm
  | succ l ih =>
    rw [propagator,ih (by omega),transition_one_step A U V lam hUV (s+l) (hA _ (by omega)),
      transition_comp U V lam hVU]
    rfl

end SmoothObstruction.EuclideanSplitting

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_Charts
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.CarriedCharts
open Set Metric
variable {M : Type*} [MetricSpace M] {ι : Type*} [Fintype ι]

lemma finite_positive_lower (r : ι → ℝ) (hr : ∀ i,0 < r i) :
    ∃ a : ℝ,0 < a ∧ ∀ i,a ≤ r i := by
  classical
  have hh (s : Finset ι) : ∃ a : ℝ,0 < a ∧ ∀ i∈s,a ≤ r i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨a,ha,has⟩ := ih
      refine ⟨min a (r i),lt_min ha (hr i),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hj|hj
      · subst j; exact min_le_right _ _
      · exact (min_le_left _ _).trans (has j hj)
  obtain ⟨a,ha,hh⟩ := hh Finset.univ
  exact ⟨a,ha,fun i => hh i (Finset.mem_univ i)⟩

end SmoothObstruction.CarriedCharts

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The actual derivative cocycle is the derivative of the actual local
coordinate map. Charts may be independently selected at each endpoint;
the formula is valid on half-space models without changing derivatives. -/
theorem coord_eq_fderivWithin (S : Diffeomorph I I M M ∞) (a b x : M)
    (hx : x∈domain I S a b) :
    fderivWithin ℝ (localMap I S a b) (range I) ((extChartAt I a) x)=coord I S a b x := by
  have hit : (extChartAt I a) x∈(extChartAt I a).target :=
    (extChartAt I a).map_source (by simpa only [extChartAt_source] using hx.1)
  have hir : (extChartAt I a) x∈range I := extChartAt_target_subset_range a hit
  have huniq : UniqueMDiffWithinAt (𝓘(ℝ,E (d:=d))) (range I) ((extChartAt I a) x) :=
    (I.uniqueDiffOn _ hir).uniqueMDiffWithinAt
  have hs := mdifferentiableWithinAt_extChartAt_symm (I:=I) hit
  have hf : MDifferentiableAt I (𝓘(ℝ,E (d:=d))) (extChartAt I b ∘ S) x :=
    (mdifferentiableAt_extChartAt hx.2).comp x (S.contMDiff.mdifferentiable (by simp) x)
  have hcomp := mfderiv_comp_mfderivWithin_of_eq hf hs huniq
    ((extChartAt I a).left_inv (by simpa only [extChartAt_source] using hx.1))
  have hchain := mfderiv_comp x (mdifferentiableAt_extChartAt (I:=I) hx.2)
    (S.contMDiff.mdifferentiable (by simp) x)
  rw [hchain] at hcomp
  have hcoord := inTangentCoordinates_eq_mfderiv_comp
    (I:=I) (I':=I) (f:=fun p : M×M => p.1) (g:=fun p : M×M => p.2)
    (ϕ:=fun p => mfderiv I I S p.1) (x₀:=(a,b)) (x:=(x,S x)) hx.1 hx.2
  change coord I S a b x=_ at hcoord
  rw [mfderivWithin_eq_fderivWithin] at hcomp
  have he := hcomp.trans hcoord.symm
  change fderivWithin ℝ ((extChartAt I b ∘ S) ∘ (extChartAt I a).symm)
    (range I) ((extChartAt I a) x)=coord I S a b x at he
  simpa only [localMap,Function.comp_assoc] using he

/-- In an interior orbit tube this is an ordinary derivative, exactly the
input of the finite-array nonlinear construction. -/
theorem hasFDerivAt_localMap (S : Diffeomorph I I M M ∞) (a b x : M)
    (hx : x∈domain I S a b)
    (hint : (extChartAt I a) x∈interior (range I)) :
    HasFDerivAt (localMap I S a b) (coord I S a b x) ((extChartAt I a) x) := by
  have hs := mdifferentiableWithinAt_extChartAt_symm (I:=I)
    ((extChartAt I a).map_source (by simpa only [extChartAt_source] using hx.1))
  have hf : MDifferentiableAt I (𝓘(ℝ,E (d:=d))) (extChartAt I b ∘ S) x :=
    (mdifferentiableAt_extChartAt hx.2).comp x (S.contMDiff.mdifferentiable (by simp) x)
  have hh := hf.comp_mdifferentiableWithinAt_of_eq _ hs ((extChartAt I a).left_inv (by simpa only [extChartAt_source] using hx.1))
  have hd : DifferentiableWithinAt ℝ (localMap I S a b) (range I) ((extChartAt I a) x) := by
    exact mdifferentiableWithinAt_iff_differentiableWithinAt.mp hh
  rw [←coord_eq_fderivWithin I S a b x hx]
  exact hd.hasFDerivWithinAt.hasFDerivAt (mem_interior_iff_mem_nhds.mp hint)
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Actual coordinate expressions are genuinely smooth in every retained
interior tube. For a boundary model no smooth extension is assumed here:
the statement uses the interior of the original model range. -/
theorem contDiffAt_localMap (S : Diffeomorph I I M M ∞) (a b x : M)
    (hx : x∈domain I S a b)
    (hint : (extChartAt I a) x∈interior (range I)) :
    ContDiffAt ℝ ∞ (localMap I S a b) ((extChartAt I a) x) := by
  have hs := contMDiffWithinAt_extChartAt_symm_range (I:=I) (n:=∞) a
    ((extChartAt I a).map_source (by simpa only [extChartAt_source] using hx.1))
  have hf : ContMDiffAt I (𝓘(ℝ,E (d:=d))) ∞ (extChartAt I b ∘ S) x :=
    (contMDiffAt_extChartAt' (I:=I) hx.2).comp x (S.contMDiff x)
  have hh := hf.comp_contMDiffWithinAt_of_eq hs
    ((extChartAt I a).left_inv (by simpa only [extChartAt_source] using hx.1))
  have hd : ContDiffWithinAt ℝ ∞ (localMap I S a b) (range I)
      ((extChartAt I a) x) := contMDiffWithinAt_iff_contDiffWithinAt.mp hh
  exact hd.contDiffAt (mem_interior_iff_mem_nhds.mp hint)

end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.CarriedCharts
open Set Metric Filter Topology
open scoped ContDiff
variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

/-- Uniform C2 bounds up to a closed model boundary, WITHOUT an extension
assumption. Ordinary derivatives are taken only in the original interior;
the bound is independent of distance to the boundary. -/
theorem uniform_c2_boundary (f : ι → E → F) (K U : ι → Set E) (H : Set E)
    (hK : ∀ i,IsCompact (K i)) (hU : ∀ i,IsOpen (U i)) (hH : IsClosed H)
    (hKU : ∀ i,K i⊆U i) (huniq : ∀ i,UniqueDiffOn ℝ (U i∩H))
    (hf : ∀ i,ContDiffOn ℝ ∞ (f i) (U i∩H)) :
    ∃ r C : ℝ,0 < r ∧ 1 ≤ C ∧ ∀ i x,x∈K i →
      closedBall x r⊆U i ∧ ∀ y∈closedBall x r,y∈interior H →
        ContDiffAt ℝ ∞ (f i) y ∧
        ‖fderiv ℝ (f i) y‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ (f i)) y‖ ≤ C := by
  have hex (i : ι) : ∃ r : ℝ,0 < r ∧ cthickening r (K i)⊆U i :=
    (hK i).exists_cthickening_subset_open (hU i) (hKU i)
  choose r hr hrU using hex
  obtain ⟨a,ha,har⟩ := finite_positive_lower r hr
  let s (i : ι) := U i∩H
  let f₁ (i : ι) := fderivWithin ℝ (f i) (s i)
  let f₂ (i : ι) := fderivWithin ℝ (f₁ i) (s i)
  have hf₁ (i : ι) : ContDiffOn ℝ ∞ (f₁ i) (s i) :=
    (hf i).fderivWithin (huniq i) (by simp)
  have hf₂ (i : ι) : ContDiffOn ℝ ∞ (f₂ i) (s i) :=
    (hf₁ i).fderivWithin (huniq i) (by simp)
  have hb (i : ι) : ∃ C : ℝ,∀ y∈cthickening (r i) (K i)∩H,
      ‖f₁ i y‖ ≤ C ∧ ‖f₂ i y‖ ≤ C := by
    have hcomp : IsCompact (cthickening (r i) (K i)∩H) := (hK i).cthickening.inter_right hH
    have hsub : cthickening (r i) (K i)∩H⊆s i := fun y hy => ⟨hrU i hy.1,hy.2⟩
    obtain ⟨A,hA⟩ := hcomp.exists_bound_of_continuousOn (f := f₁ i)
      ((hf₁ i).continuousOn.mono hsub)
    obtain ⟨B,hB⟩ := hcomp.exists_bound_of_continuousOn (f := f₂ i)
      ((hf₂ i).continuousOn.mono hsub)
    exact ⟨max A B,fun y hy => ⟨(hA y hy).trans (le_max_left _ _),
      (hB y hy).trans (le_max_right _ _)⟩⟩
  choose C hC using hb
  let D : ℝ := 1+∑ i,|C i|
  have hD : 1 ≤ D := by
    dsimp [D]
    have hh : 0≤∑ i,|C i| := Finset.sum_nonneg (fun i _ => abs_nonneg (C i))
    linarith
  have hCD (i : ι) : C i ≤ D := by
    have hh : |C i| ≤ ∑ j,|C j| := Finset.single_le_sum (fun j _ => abs_nonneg (C j))
      (Finset.mem_univ i)
    dsimp [D]
    linarith [le_abs_self (C i)]
  refine ⟨a,D,ha,hD,fun i x hx => ?_⟩
  have hball : closedBall x a⊆cthickening (r i) (K i) :=
    (closedBall_subset_closedBall (har i)).trans (closedBall_subset_cthickening hx (r i))
  refine ⟨hball.trans (hrU i),fun y hy hyH => ?_⟩
  have hyU := hrU i (hball hy)
  have hys : s i∈𝓝 y := inter_mem ((hU i).mem_nhds hyU) (mem_interior_iff_mem_nhds.mp hyH)
  have heq : f₁ i =ᶠ[𝓝 y] fderiv ℝ (f i) := by
    filter_upwards [((hU i).inter isOpen_interior).mem_nhds ⟨hyU,hyH⟩] with z hz
    exact fderivWithin_of_mem_nhds (inter_mem ((hU i).mem_nhds hz.1)
      (mem_interior_iff_mem_nhds.mp hz.2))
  have hfirst : f₁ i y=fderiv ℝ (f i) y := heq.eq_of_nhds
  have hsecond : f₂ i y=fderiv ℝ (fderiv ℝ (f i)) y :=
    (fderivWithin_of_mem_nhds hys).trans heq.fderiv_eq
  have hb' := hC i y ⟨hball hy,interior_subset hyH⟩
  rw [hfirst,hsecond] at hb'
  exact ⟨(hf i y ⟨hyU,interior_subset hyH⟩).contDiffAt hys,
    hb'.1.trans (hCD i),hb'.2.trans (hCD i)⟩
end SmoothObstruction.CarriedCharts

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
lemma isOpen_domainU (S : Diffeomorph I I M M ∞) (a b : M) : IsOpen (domainU I S a b) :=
  ((chartAt H a).isOpen_inter_preimage_symm
    ((chartAt H b).open_source.preimage S.continuous)).preimage I.continuous_symm

omit [IsManifold I ∞ M] in
lemma map_mem_domainU (S : Diffeomorph I I M M ∞) (a b x : M)
    (hx : x∈domain I S a b) : (extChartAt I a) x∈domainU I S a b := by
  have ht := (extChartAt I a).map_source (by simpa only [extChartAt_source] using hx.1)
  have htar : I.symm ((extChartAt I a) x)∈(chartAt H a).target := by
    rw [extChartAt,OpenPartialHomeomorph.extend_target] at ht
    exact ht.1
  refine ⟨htar,?_⟩
  change S ((extChartAt I a).symm ((extChartAt I a) x))∈(chartAt H b).source
  rw [(extChartAt I a).left_inv (by simpa only [extChartAt_source] using hx.1)]
  exact hx.2

theorem contDiffOn_localMap (S : Diffeomorph I I M M ∞) (a b : M) :
    ContDiffOn ℝ ∞ (localMap I S a b) (domainU I S a b∩range I) := by
  intro y hy
  have hyt : y∈(extChartAt I a).target := by
    rw [extChartAt,OpenPartialHomeomorph.extend_target]
    exact ⟨hy.1.1,hy.2⟩
  have hby : S ((extChartAt I a).symm y)∈(chartAt H b).source := hy.1.2
  have hf : ContMDiffAt I (𝓘(ℝ,E (d:=d))) ∞ (extChartAt I b ∘ S)
      ((extChartAt I a).symm y) :=
    (contMDiffAt_extChartAt' (I:=I) hby).comp _ (S.contMDiff _)
  have hh := hf.comp_contMDiffWithinAt y
    (contMDiffWithinAt_extChartAt_symm_range (I:=I) (n:=∞) a hyt)
  have hd : ContDiffWithinAt ℝ ∞ (localMap I S a b) (range I) y :=
    contMDiffWithinAt_iff_contDiffWithinAt.mp hh
  exact hd.mono inter_subset_right

/-- Genuine uniform first and second derivative bounds for all actually
used local chart pairs. Valid for the closed half-space model, uniformly
as the reference point approaches the boundary. No extension theorem or
long-iterate C2 bound has been assumed. -/
theorem actual_uniform_c2 [T2Space M] {ι : Type*} [Fintype ι]
    (hclosed : IsClosed (range I)) (S : Diffeomorph I I M M ∞)
    (a : ι → M) (K : ι → Set M) (hK : ∀ i,IsCompact (K i))
    (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C : ℝ,0 < r ∧ 1 ≤ C ∧ ∀ i j x,x∈K i → S x∈K j →
      closedBall ((extChartAt I (a i)) x) r⊆domainU I S (a i) (a j) ∧
      ∀ y∈closedBall ((extChartAt I (a i)) x) r,y∈interior (range I) →
        ContDiffAt ℝ ∞ (localMap I S (a i) (a j)) y ∧
        ‖fderiv ℝ (localMap I S (a i) (a j)) y‖ ≤ C ∧
        ‖fderiv ℝ (fderiv ℝ (localMap I S (a i) (a j))) y‖ ≤ C := by
  let L (ij : ι×ι) := (extChartAt I (a ij.1)) '' (K ij.1∩S ⁻¹' K ij.2)
  have hcomp (ij : ι×ι) : IsCompact (L ij) :=
    ((hK ij.1).inter_right ((hK ij.2).isClosed.preimage S.continuous)).image_of_continuousOn
      ((continuousOn_extChartAt (I:=I) (a ij.1)).mono (fun x hx => by simpa only [extChartAt_source] using hKU _ hx.1))
  have hsub (ij : ι×ι) : L ij⊆domainU I S (a ij.1) (a ij.2) := by
    rintro z ⟨x,hx,rfl⟩
    exact map_mem_domainU I S (a ij.1) (a ij.2) x ⟨hKU _ hx.1,hKU _ hx.2⟩
  obtain ⟨r,C,hr,hC,hh⟩ := CarriedCharts.uniform_c2_boundary
    (fun ij : ι×ι => localMap I S (a ij.1) (a ij.2)) L
    (fun ij => domainU I S (a ij.1) (a ij.2)) (range I) hcomp
    (fun ij => isOpen_domainU I S (a ij.1) (a ij.2)) hclosed hsub
    (fun ij => by simpa only [inter_comm] using
      I.uniqueDiffOn.inter (isOpen_domainU I S (a ij.1) (a ij.2)))
    (fun ij => contDiffOn_localMap I S (a ij.1) (a ij.2))
  exact ⟨r,C,hr,hC,fun i j x hx hSx => hh (i,j) ((extChartAt I (a i)) x) ⟨x,⟨hx,hSx⟩,rfl⟩⟩
end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_ShortDerivative
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.RelativeProduct

variable {R : Type*}

/-- Exact variation-of-constants expansion; no commutativity is used. -/
theorem difference [Ring R] (A B : ℕ → R) (s n : ℕ) :
    segment B s n - segment A s n =
      ∑ j ∈ Finset.range n,
        segment A (s + j + 1) (n - (j + 1)) *
          (B (s + j) - A (s + j)) * segment B s j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, segment_zero, one_mul]
    have hsum :
        (∑ j ∈ Finset.range n,
          segment A (s + j + 1) (n + 1 - (j + 1)) *
            (B (s + j) - A (s + j)) * segment B s j) =
          A (s + n) * (segment B s n - segment A s n) := by
      rw [ih, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjn : j < n := Finset.mem_range.mp hj
      have hlen : n + 1 - (j + 1) = (n - (j + 1)) + 1 := by omega
      have hidx : s + j + 1 + (n - (j + 1)) = s + n := by omega
      rw [hlen, segment_succ, hidx]
      simp only [mul_assoc]
    rw [hsum, segment_succ, segment_succ]
    noncomm_ring

/-- Uniform subinterval bounds yield a relative error, rather than a
bound obtained by multiplying one-step bounds. -/
theorem norm_difference_le [NormedRing R] (A B : ℕ → R)
    (s m : ℕ) (L δ : ℝ) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hA : ∀ t k : ℕ, s ≤ t → t + k ≤ s + m → ‖segment A t k‖ ≤ L)
    (hBA : ∀ t : ℕ, s ≤ t → t < s + m → ‖B t - A t‖ ≤ δ) :
    ‖segment B s m - segment A s m‖ ≤ L * ((1 + L * δ) ^ m - 1) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have hB (j : ℕ) (hj : j < m) :
        ‖segment B s j‖ ≤ L * (1 + L * δ) ^ j := by
      have herr := ih j hj (fun t k ht hk => hA t k ht (by omega))
        (fun t ht htm => hBA t ht (by omega))
      calc
        ‖segment B s j‖ = ‖(segment B s j - segment A s j) + segment A s j‖ := by
          rw [sub_add_cancel]
        _ ≤ ‖segment B s j - segment A s j‖ + ‖segment A s j‖ := norm_add_le _ _
        _ ≤ L * ((1 + L * δ) ^ j - 1) + L :=
          add_le_add herr (hA s j le_rfl (by omega))
        _ = L * (1 + L * δ) ^ j := by ring
    rw [difference]
    calc
      ‖∑ j ∈ Finset.range m,
          segment A (s + j + 1) (m - (j + 1)) *
            (B (s + j) - A (s + j)) * segment B s j‖
          ≤ ∑ j ∈ Finset.range m,
            ‖segment A (s + j + 1) (m - (j + 1)) *
              (B (s + j) - A (s + j)) * segment B s j‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range m, L * δ * (L * (1 + L * δ) ^ j) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjm : j < m := Finset.mem_range.mp hj
        calc
          _ ≤ ‖segment A (s + j + 1) (m - (j + 1))‖ *
              ‖B (s + j) - A (s + j)‖ * ‖segment B s j‖ :=
            (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ L * δ * (L * (1 + L * δ) ^ j) := by
            gcongr
            · exact hA (s + j + 1) (m - (j + 1)) (by omega) (by omega)
            · exact hBA (s + j) (by omega) (by omega)
            · exact hB j hjm
      _ = L * ((1 + L * δ) ^ m - 1) := by
        have hgeom := geom_sum_mul (1 + L * δ) m
        simp only [add_sub_cancel_left] at hgeom
        rw [← hgeom, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

/-- Scalar normalization of a whole interval. -/
theorem segment_smul [NormedRing R] [NormedAlgebra ℝ R]
    (A : ℕ → R) (c : ℝ) (s n : ℕ) :
    segment (fun t => c • A t) s n = c ^ n • segment A s n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [segment_succ, ih, smul_mul_smul_comm, pow_succ']

private theorem exp_cancel (σ a : ℝ) (n : ℕ) :
    Real.exp (-σ) ^ n * Real.exp (σ * n + a) = Real.exp a := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

/-- The relative perturbation bound with its exact exponential weight. -/
theorem norm_difference_le_exp_exact [NormedRing R] [NormedAlgebra ℝ R]
    (A B : ℕ → R) (s m : ℕ) (σ a δ : ℝ) (hδ : 0 ≤ δ)
    (hA : ∀ t k : ℕ, s ≤ t → t + k ≤ s + m →
      ‖segment A t k‖ ≤ Real.exp (σ * k + a))
    (hBA : ∀ t : ℕ, s ≤ t → t < s + m → ‖B t - A t‖ ≤ δ) :
    ‖segment B s m - segment A s m‖ ≤
      Real.exp (σ * m + a) * ((1 + δ * Real.exp (a - σ)) ^ m - 1) := by
  let c := Real.exp (-σ)
  have hc : 0 < c := Real.exp_pos _
  have hnorm (D : ℕ → R) (t k : ℕ) :
      ‖segment (fun i => c • D i) t k‖ = c ^ k * ‖segment D t k‖ := by
    rw [segment_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc.le k)]
  have hnormsub (t k : ℕ) :
      ‖segment (fun i => c • B i) t k - segment (fun i => c • A i) t k‖ =
        c ^ k * ‖segment B t k - segment A t k‖ := by
    rw [segment_smul, segment_smul, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hc.le k)]
  have hAnorm (t k : ℕ) (ht : s ≤ t) (hk : t + k ≤ s + m) :
      ‖segment (fun i => c • A i) t k‖ ≤ Real.exp a := by
    rw [hnorm]
    calc
      _ ≤ c ^ k * Real.exp (σ * k + a) :=
        mul_le_mul_of_nonneg_left (hA t k ht hk) (pow_nonneg hc.le k)
      _ = Real.exp a := exp_cancel σ a k
  have hBAnorm (t : ℕ) (ht : s ≤ t) (htm : t < s + m) :
      ‖c • B t - c • A t‖ ≤ c * δ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (hBA t ht htm) hc.le
  have herr := norm_difference_le (fun t => c • A t) (fun t => c • B t)
    s m (Real.exp a) (c * δ) (Real.exp_pos a).le (mul_nonneg hc.le hδ)
    hAnorm hBAnorm
  rw [hnormsub] at herr
  have hcoef : Real.exp a * (c * δ) = δ * Real.exp (a - σ) := by
    dsimp [c]
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
  rw [hcoef] at herr
  apply (mul_le_mul_iff_right₀ (pow_pos hc m)).mp
  simpa only [← mul_assoc, c, exp_cancel] using herr

/-- Quantitative core of the source exterior-product perturbation lemma.
Applying this to exterior powers with one-step error `δ = C * ε` gives
exactly its stated finite-product bound. -/
theorem norm_difference_le_exp [NormedRing R] [NormedAlgebra ℝ R]
    (A B : ℕ → R) (s m : ℕ) (σ a δ : ℝ) (hδ : 0 ≤ δ)
    (hA : ∀ t k : ℕ, s ≤ t → t + k ≤ s + m →
      ‖segment A t k‖ ≤ Real.exp (σ * k + a))
    (hBA : ∀ t : ℕ, s ≤ t → t < s + m → ‖B t - A t‖ ≤ δ) :
    ‖segment B s m - segment A s m‖ ≤
      Real.exp (σ * m + a) * ((1 + δ * Real.exp (a + |σ|)) ^ m - 1) := by
  refine (norm_difference_le_exp_exact A B s m σ a δ hδ hA hBA).trans ?_
  gcongr
  linarith [neg_le_abs σ]

end SmoothObstruction.RelativeProduct

namespace SmoothObstruction.ShortDerivative
open Set Finset
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma orbit_eq_iterate (f : ℕ → E → E) (x : ℕ → E) (N : ℕ)
    (hx : ∀ t<N,f t (x t)=x (t+1)) : ∀ t≤N,iterate f t (x 0)=x t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
    change f t (iterate f t (x 0))=x (t+1)
    rw [ih (by omega),hx t (by omega)]

lemma derivative_iterate (f : ℕ → E → E) (x : ℕ → E)
    (A : ℕ → E →L[ℝ] E) (N : ℕ)
    (hx : ∀ t<N,f t (x t)=x (t+1))
    (hd : ∀ t<N,HasFDerivAt (f t) (A t) (x t)) :
    HasFDerivAt (iterate f N) (RelativeProduct.segment A 0 N) (x 0) := by
  induction N with
  | zero => exact hasFDerivAt_id _
  | succ N ih =>
    have hN := ih (fun t ht => hx t (by omega)) (fun t ht => hd t (by omega))
    have he := orbit_eq_iterate f x (N+1) hx N (by omega)
    have hdN := hd N (by omega)
    rw [←he] at hdN
    have h := hdN.comp (x 0) hN
    simpa only [iterate,RelativeProduct.segment_succ,Nat.zero_add,ContinuousLinearMap.mul_def] using h

end SmoothObstruction.ShortDerivative

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_SmoothScales
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Filter Topology
open scoped Real

namespace SmoothObstruction.ExteriorStability

open RelativeProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Exterior powers commute with the source's time-ordered product. -/
theorem exterior_segment (p : ℕ) (A : ℕ → E →L[ℝ] E) (s n : ℕ) :
    exterior p (segment A s n) = segment (fun t => exterior p (A t)) s n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [segment_succ, exterior_mul, ih]

/-- Finite-product assertion of manuscript Lemma `lem:relative-exterior`,
in the canonical exterior Euclidean operator norm. The one-step constant
is uniform over all exterior degrees `p ≤ d`, all products and all lengths.
The proof actually does not need `a ≥ 0`, `m ≥ 1`, or `K ≥ 1`; the source
assumptions are retained in the final source-specialized statement. -/
theorem relative_exterior_core (d : ℕ) (K : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℕ), p ≤ d →
      ∀ (A B : ℕ → E →L[ℝ] E) (m : ℕ) (σ a ε : ℝ),
      0 ≤ ε → ε ≤ 1 →
      (∀ t < m, ‖A t‖ ≤ K) →
      (∀ t < m, ‖B t - A t‖ ≤ ε) →
      (∀ s k : ℕ, s + k ≤ m →
        ‖exterior p (segment A s k)‖ ≤ Real.exp (σ * k + a)) →
      ‖exterior p (segment B 0 m) - exterior p (segment A 0 m)‖ ≤
        Real.exp (σ * m + a) * ((1 + C * ε * Real.exp (a + |σ|)) ^ m - 1) := by
  obtain ⟨C, hCpos, hC⟩ := exists_uniform_exterior_lipschitz (E := E) d K
  refine ⟨C, hCpos, ?_⟩
  intro p hp A B m σ a ε hε hε₁ hA hBA hseg
  simp only [exterior_segment]
  apply norm_difference_le_exp (fun t => exterior p (A t))
    (fun t => exterior p (B t)) 0 m σ a (C * ε) (mul_nonneg hCpos hε)
  · intro t k _ htk
    simpa only [← exterior_segment, Nat.zero_add] using hseg t k (by omega)
  · intro t _ ht
    exact (hC p hp (A t) (B t) (hA t (by omega)) ((hBA t (by omega)).trans hε₁)).trans
      (mul_le_mul_of_nonneg_left (hBA t (by omega)) hCpos)

end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.RelativeAsymptotics
lemma exp_sub_one_le (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  nlinarith
lemma pow_one_add_sub_one_le (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (1 + x)^n - 1 ≤ n * x * Real.exp (n * x) := by
  have h : (1 + x)^n ≤ Real.exp (n * x) := by
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by positivity)
    simpa [add_comm] using Real.add_one_le_exp x
  exact (sub_le_sub_right h 1).trans (exp_sub_one_le _)

lemma normalized_estimate (x σ a c C ε : ℝ) (m : ℕ) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hx : x ≤ Real.exp (σ * m + a) * ((1 + C * ε * Real.exp (a + |σ|)) ^ m - 1)) :
    x / Real.exp (σ * m - c) ≤
      (C * m * ε * Real.exp (2 * a + c + |σ|)) *
        Real.exp (C * m * ε * Real.exp (a + |σ|)) := by
  have hnorm := mul_le_mul_of_nonneg_left
    (pow_one_add_sub_one_le (C * ε * Real.exp (a + |σ|)) (by positivity) m)
    (Real.exp_pos (σ * m + a)).le
  apply (div_le_div_of_nonneg_right (hx.trans hnorm) (Real.exp_pos _).le).trans
  apply le_of_eq
  have he : Real.exp (σ * m + a) = Real.exp (σ * m - c) * Real.exp (a + c) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  have he₂ : Real.exp (a + c) * Real.exp (a + |σ|) = Real.exp (2 * a + c + |σ|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he₃ : (m : ℝ) * (C * ε * Real.exp (a + |σ|)) = C * m * ε * Real.exp (a + |σ|) := by ring
  rw [he₃]
  field_simp
  ring_nf at he₂ ⊢
  rw [← he₂]
  ring

end SmoothObstruction.RelativeAsymptotics

namespace SmoothObstruction.RelativeAsymptotics
open Filter Topology

lemma uniform_relative_bound (x σ a ε b n C C₀ C₁ C₂ C₃ : ℝ) (m : ℕ)
    (hb : 0 ≤ b) (hn : 0 ≤ n) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hC₃ : 0 ≤ C₃)
    (ha0 : 0 ≤ a) (hε : 0 ≤ ε) (hm : (m : ℝ) ≤ 2 * n)
    (ha : a ≤ C₁ * b * n) (hσ : |σ| ≤ C₂)
    (hεle : ε ≤ C₃ * Real.exp (-(3 / 2 : ℝ) * SmoothScales.B b * n))
    (hx : x ≤ Real.exp (σ * m + a) *
      ((1 + C * ε * Real.exp (a + |σ|)) ^ m - 1)) :
    x / Real.exp (σ * m - C₀ * b * n) ≤
      envelope C C₀ C₁ C₂ C₃ b n * Real.exp (envelope C C₀ C₁ C₂ C₃ b n) := by
  let U := C * m * ε * Real.exp (a + |σ|)
  let D := C * m * ε * Real.exp (2 * a + C₀ * b * n + |σ|)
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hUD : U ≤ D := by
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have : 0 ≤ C₀ * b * n := by positivity
    linarith
  have hDV : D ≤ envelope C C₀ C₁ C₂ C₃ b n := by
    have hexp : 2 * a + C₀ * b * n + |σ| ≤
        (2 * C₁ + C₀) * b * n + C₂ := by nlinarith
    have hprod : C * m * ε ≤ C * (2 * n) *
        (C₃ * Real.exp (-(3 / 2 : ℝ) * SmoothScales.B b * n)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hm hC) hεle hε (by positivity)
    calc
      D ≤ C * (2 * n) * (C₃ * Real.exp (-(3 / 2 : ℝ) * SmoothScales.B b * n)) *
          Real.exp ((2 * C₁ + C₀) * b * n + C₂) :=
        mul_le_mul hprod (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)
      _ = _ := by
        dsimp [envelope]
        rw [Real.exp_add ((2 * C₁ + C₀) * b * n) C₂,
          Real.exp_add (-(3 / 2 : ℝ) * SmoothScales.B b * n)]
        ring
  exact (normalized_estimate x σ a (C₀*b*n) C ε m hC hε hx).trans
    (mul_le_mul hDV (Real.exp_le_exp.mpr (hUD.trans hDV)) (Real.exp_pos _).le (hD0.trans hDV))

end SmoothObstruction.RelativeAsymptotics

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_SpectralBins
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.EuclideanSplitting
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

lemma mem_coordinateSpace (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    x∈coordinateSpace S ↔ ∀ j∉S,x j=0 := by
  rw [coordinateSpace,Submodule.map_equiv_eq_comap_symm]
  exact Pi.mem_spanSubset_iff

lemma finrank_coordinateSpace (S : Finset (Fin d)) :
    Module.finrank ℝ (coordinateSpace S)=S.card := by
  rw [coordinateSpace,LinearEquiv.finrank_map_eq,Pi.dim_spanSubset,Set.ncard_coe_finset]

lemma mask_apply (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (mask S) x) j=if j∈S then x j else 0 := by
  change ((mask S)*ᵥ (WithLp.ofLp x)) j=_
  rw [mask,Matrix.mulVec_diagonal]
  split <;> simp_all

lemma coordinateSpace_fixed (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    x∈coordinateSpace S ↔ Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (mask S) x=x := by
  rw [mem_coordinateSpace]
  constructor
  · intro hx
    ext j
    rw [mask_apply]
    split_ifs with hj
    · rfl
    · exact (hx j hj).symm
  · intro hx j hj
    have he := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x j) hx
    rw [mask_apply,ite_eq_right hj] at he
    exact he.symm

lemma finrank_groupSpace (U V : Matrix (Fin d) (Fin d) ℝ)
    (hUV : U*V=1) (hVU : V*U=1) (S : Finset (Fin d)) :
    Module.finrank ℝ (groupSpace U V hUV hVU S)=S.card := by
  rw [groupSpace,LinearEquiv.finrank_map_eq,finrank_coordinateSpace]

lemma groupSpace_fixed (U V : Matrix (Fin d) (Fin d) ℝ)
    (hUV : U*V=1) (hVU : V*U=1) (S : Finset (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) :
    x∈groupSpace U V hUV hVU S ↔
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U*mask S*V) x=x := by
  rw [groupSpace,Submodule.map_equiv_eq_comap_symm]
  change (gaugeEquiv U V hUV hVU).symm x∈coordinateSpace S ↔ _
  rw [coordinateSpace_fixed]
  constructor
  · intro hx
    have he := congrArg (gaugeEquiv U V hUV hVU) hx
    rw [(gaugeEquiv U V hUV hVU).apply_symm_apply] at he
    simpa only [gaugeEquiv_apply,gaugeEquiv_symm_apply,map_mul,
      mul_apply_eq_comp] using he
  · intro hx
    apply (gaugeEquiv U V hUV hVU).injective
    rw [(gaugeEquiv U V hUV hVU).apply_symm_apply]
    simpa only [gaugeEquiv_apply,gaugeEquiv_symm_apply,map_mul,
      mul_apply_eq_comp] using hx

end SmoothObstruction.EuclideanSplitting

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_GreenOperator
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.EuclideanSplitting
variable {d : ℕ} (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1) (S : Finset (Fin d))

lemma splitting_slow_range (t : ℕ) :
    ((splitting U V lam hUV hVU S).slow t).range=
      groupSpace (U t) (V t) (hUV t) (hVU t) S := by
  ext x
  rw [groupSpace_fixed]
  constructor
  · rintro ⟨y,rfl⟩
    exact (splitting U V lam hUV hVU S).slow_self t y
  · intro hx
    exact ⟨x,hx⟩

lemma splitting_fast_range (t : ℕ) :
    ((splitting U V lam hUV hVU S).fast t).range=
      groupSpace (U t) (V t) (hUV t) (hVU t) Sᶜ :=
  splitting_slow_range U V lam hUV hVU Sᶜ t
end SmoothObstruction.EuclideanSplitting

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_SplittingStability
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

lemma rate_eigen (lam : Fin d → ℝ) (l : ℝ) (j : Fin d) :
    Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam l) (EuclideanSpace.basisFun (Fin d) ℝ j)=
      Real.exp (l*lam j) • EuclideanSpace.basisFun (Fin d) ℝ j := by
  ext i
  change ((rate lam l)*ᵥ (EuclideanSpace.basisFun (Fin d) ℝ j)) i=_
  simp only [rate,Matrix.mulVec_diagonal,EuclideanSpace.basisFun_apply,
    PiLp.single_apply,PiLp.smul_apply,smul_eq_mul]
  by_cases hi : i=j
  · subst i; simp
  · simp [hi]

lemma selected_sum {p : ℕ} (s : powersetCard (Fin d) p) (lam : Fin d → ℝ) :
    (∑ i : Fin p,lam (powersetCard.ofFinEmbEquiv.symm s i))=∑ j∈s.val,lam j := by
  rw [powersetCard.ofFinEmbEquiv_symm_apply]
  have he := Finset.sum_map (s:=Finset.univ) (s.val.orderEmbOfFin s.prop).toEmbedding lam
  have hm : Finset.map (s.val.orderEmbOfFin s.prop).toEmbedding Finset.univ=s.val :=
    Finset.map_orderEmbOfFin_univ s.val s.prop
  rw [hm] at he
  exact he.symm

/-- The dominant exterior estimate of the actual matrix transition uses the
sum over the selected fast rates on every subinterval, not a coarse norm. -/
theorem transition_exterior_bound
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (S : Finset (Fin d)) {s t : ℕ} (hst : s≤t) {γ g K C : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hU : ‖U t‖≤Real.exp K) (hV : ‖V s‖≤Real.exp K)
    (hpoly : ∀ A : (EuclideanSpace ℝ (Fin d)) →L[ℝ] _,
      ‖exterior S.card A‖≤C*(max 1 ‖A‖)^S.card) :
    ‖exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t))‖≤
      C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
        Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j)) := by
  have hm (q : powersetCard (Fin d) S.card) :
      (∑ i : Fin S.card,lam (powersetCard.ofFinEmbEquiv.symm q i))≤∑ j∈S,lam j := by
    rw [selected_sum]
    exact RateSums.rate_sum_max lam S q.val hg q.prop hfast hslow
  have he := exterior_gauge_bound (EuclideanSpace.basisFun (Fin d) ℝ) S.card
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U t))
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (V s))
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam ((t:ℝ)-s))) lam
    (sub_nonneg.mpr (by exact_mod_cast hst) : 0≤(t:ℝ)-s)
    (Real.one_le_exp_iff.mpr hK) hC hpoly
    (by simpa only [Matrix.l2_opNorm_toEuclideanCLM] using hU)
    (by simpa only [Matrix.l2_opNorm_toEuclideanCLM] using hV)
    (rate_eigen lam _) hm
  simpa only [transition,map_mul] using he

end SmoothObstruction.EuclideanSplitting

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_AsymptoticSplitting
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Filter Topology
open scoped Real

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability RelativeProduct
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

lemma segment_toEuclidean (A : ℕ → Matrix (Fin d) (Fin d) ℝ) (s l : ℕ) :
    segment (fun t => Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t)) s l =
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (propagator A s l) := by
  induction l with
  | zero => simp [RelativeProduct.segment, propagator]
  | succ l ih => simp only [segment_succ, propagator, ih, map_mul]

/-- No product bounds are assumed: every interval follows from the actual
coordinate derivative equations and the uniformly bounded finite gauges. -/
theorem actual_interval_exterior
    (A U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (S : Finset (Fin d)) (N : ℕ) {γ g K C : ℝ}
    (hUV : ∀ t, U t * V t = 1) (hVU : ∀ t, V t * U t = 1)
    (hA : ∀ t < N, A t * U t = U (t+1) * rate lam 1)
    (hg : 0 ≤ g) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hfast : ∀ j ∈ S, γ + g ≤ lam j) (hslow : ∀ j ∉ S, lam j ≤ γ - g)
    (hU : ∀ t ≤ N, ‖U t‖ ≤ Real.exp K) (hV : ∀ t ≤ N, ‖V t‖ ≤ Real.exp K)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card A‖ ≤ C * (max 1 ‖A‖)^S.card)
    (s l : ℕ) (hsl : s + l ≤ N) :
    ‖exterior S.card (segment (fun t => Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t)) s l)‖ ≤
      C^2 * (Real.exp K)^(2*S.card) * (Fintype.card (powersetCard (Fin d) S.card) : ℝ) *
        Real.exp ((∑ j ∈ S, lam j) * l) := by
  rw [segment_toEuclidean, propagator_eq_transition A U V lam hUV hVU N hA s l hsl]
  convert transition_exterior_bound U V lam S (by omega : s ≤ s+l)
    hg hK hC hfast hslow (hU _ hsl) (hV _ (by omega)) hpoly using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  push_cast
  ring

lemma absorb_prefactor {C R H K D z : ℝ} {p d : ℕ}
    (_hC : 0 ≤ C) (_hR : 0 ≤ R) (hRH : R ≤ H) (hH : 0 ≤ H)
    (hp : p ≤ d) (hD : 0 ≤ D) (hz : 1 ≤ z) (hK : K ≤ D*z) :
    C^2 * (Real.exp K)^(2*p) * R ≤ Real.exp ((C^2*H + 2*d*D)*z) := by
  have hz0 : 0 ≤ z := by linarith
  have hKR : (2*p:ℕ)*K ≤ (2*d:ℕ)*D*z := by
    have hp' : (p:ℝ) ≤ d := by exact_mod_cast hp
    have h₁ := mul_le_mul_of_nonneg_left hK (show 0 ≤ ((2*p:ℕ):ℝ) by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hp' (mul_nonneg hD hz0)
    push_cast at h₁ ⊢
    nlinarith
  have hconst : C^2 * R ≤ Real.exp (C^2*H*z) := by
    calc
      _ ≤ C^2*H := mul_le_mul_of_nonneg_left hRH (sq_nonneg _)
      _ ≤ C^2*H*z := le_mul_of_one_le_right (by positivity) hz
      _ ≤ _ := (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  calc
    _ = (C^2*R) * Real.exp ((2*p:ℕ)*K) := by rw [Real.exp_nat_mul]; ring
    _ ≤ Real.exp (C^2*H*z) * Real.exp ((2*d:ℕ)*D*z) :=
      mul_le_mul hconst (Real.exp_le_exp.mpr hKR) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

/-- One exponential constant works for every possible fast rank, including
zero. Dimension dependent polynomial norms and gauge prefactors are derived,
not added as assumptions about the derivative cocycle. -/
theorem exists_uniform_interval_constant (d : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (A U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
      (lam : Fin d → ℝ) (S : Finset (Fin d)) (N : ℕ) (γ g K z : ℝ),
      1 ≤ z → 0 ≤ g → 0 ≤ K → K ≤ D*z →
      (∀ t, U t * V t = 1) → (∀ t, V t * U t = 1) →
      (∀ t < N, A t * U t = U (t+1) * rate lam 1) →
      (∀ j ∈ S, γ+g ≤ lam j) → (∀ j ∉ S, lam j ≤ γ-g) →
      (∀ t ≤ N, ‖U t‖ ≤ Real.exp K) → (∀ t ≤ N, ‖V t‖ ≤ Real.exp K) →
      ∀ s l : ℕ, s+l ≤ N →
        ‖exterior S.card (segment (fun t => Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t)) s l)‖ ≤
          Real.exp ((∑ j ∈ S, lam j)*l + C₁*z) := by
  choose C hC hpoly using fun p : Fin (d+1) =>
    exists_power_bound (E:=EuclideanSpace ℝ (Fin d)) p.val
  let C' : ℝ := ∑ p, C p
  let H : ℝ := ∑ p : Fin (d+1), (Fintype.card (powersetCard (Fin d) p.val) : ℝ)
  have hC0 (p : Fin (d+1)) : 0 ≤ C p := le_trans zero_le_one (hC p)
  have hC' : 0 ≤ C' := Finset.sum_nonneg fun p _ => hC0 p
  have hH : 0 ≤ H := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  refine ⟨C'^2*H + 2*d*D, by positivity, ?_⟩
  intro A U V lam S N γ g K z hz hg hK hKD hUV hVU hA hf hs hU hV s l hsl
  have hp : S.card ≤ d := by simpa using S.card_le_univ
  let p : Fin (d+1) := ⟨S.card, by omega⟩
  have hCp : C p ≤ C' := Finset.single_le_sum (fun q _ => hC0 q) (Finset.mem_univ p)
  have hHp : (Fintype.card (powersetCard (Fin d) S.card):ℝ) ≤ H :=
    by
    change (Fintype.card (powersetCard (Fin d) p.val):ℝ) ≤
      ∑ q : Fin (d+1), (Fintype.card (powersetCard (Fin d) q.val):ℝ)
    exact Finset.single_le_sum
      (f:=fun q : Fin (d+1) => (Fintype.card (powersetCard (Fin d) q.val):ℝ))
      (fun q _ => Nat.cast_nonneg _) (Finset.mem_univ p)
  have hpower : ∀ T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card T‖ ≤ C' * (max 1 ‖T‖)^S.card := fun T =>
    (hpoly p T).trans (mul_le_mul_of_nonneg_right hCp (pow_nonneg (by positivity) _))
  calc
    _ ≤ C'^2 * (Real.exp K)^(2*S.card) * (Fintype.card (powersetCard (Fin d) S.card):ℝ) *
        Real.exp ((∑ j ∈ S, lam j)*l) :=
      actual_interval_exterior A U V lam S N hUV hVU hA hg hK hC' hf hs hU hV hpower s l hsl
    _ ≤ Real.exp ((C'^2*H + 2*d*D)*z) * Real.exp ((∑ j ∈ S, lam j)*l) :=
      mul_le_mul_of_nonneg_right (absorb_prefactor hC' (Nat.cast_nonneg _) hHp hH hp hD hz hKD)
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.EuclideanSplitting
open ExteriorStability RelativeProduct
open scoped Matrix.Norms.L2Operator

lemma rate_sum_abs_le {d : ℕ} (lam : Fin d → ℝ) (S : Finset (Fin d))
    {R : ℝ} (hR : 0 ≤ R) (hlam : ∀ i, |lam i| ≤ R) :
    |∑ i ∈ S, lam i| ≤ d * R := by
  calc
    _ ≤ ∑ i ∈ S, |lam i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ S, R := Finset.sum_le_sum fun i _ => hlam i
    _ = S.card * R := by simp
    _ ≤ d * R := mul_le_mul_of_nonneg_right (by exact_mod_cast (show S.card ≤ d by simpa using S.card_le_univ)) hR

/-- Choice-independent relative stability on ALL actual gauged intervals
at once. The only perturbation hypothesis is the genuine one-step derivative
error; all subinterval exterior bounds are proved from the gauge equations.
The same numerical envelope works for every fast rank and every witness. -/
theorem uniform_relative_gauged (d : ℕ) (K₀ D : ℝ) (hD : 0 ≤ D) :
    ∃ C C₁ : ℝ, 0 ≤ C ∧ 0 ≤ C₁ ∧
      ∀ (A U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
        (T : ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
        (lam : Fin d → ℝ) (S : Finset (Fin d)) (m : ℕ)
        (γ g K b n C₀ R C₃ ε : ℝ),
        0 ≤ b → 0 ≤ n → 1 ≤ b*n → 0 ≤ C₀ → 0 ≤ R → 0 ≤ C₃ →
        0 ≤ g → 0 ≤ K → K ≤ D*(b*n) → (m:ℝ) ≤ 2*n →
        (∀ t, U t*V t=1) → (∀ t,V t*U t=1) →
        (∀ t < m,A t*U t=U (t+1)*rate lam 1) →
        (∀ i,|lam i| ≤ R) →
        (∀ j ∈ S, γ+g ≤ lam j) → (∀ j ∉ S, lam j ≤ γ-g) →
        (∀ t ≤ m, ‖U t‖ ≤ Real.exp K) → (∀ t ≤ m, ‖V t‖ ≤ Real.exp K) →
        0 ≤ ε → ε ≤ 1 → ε ≤ C₃*Real.exp (-(3/2:ℝ)*SmoothScales.B b*n) →
        (∀ t < m, ‖A t‖ ≤ K₀) →
        (∀ t < m, ‖T t-Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t)‖ ≤ ε) →
        ‖exterior S.card (segment T 0 m) -
          exterior S.card (segment (fun t => Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t)) 0 m)‖ /
            Real.exp ((∑ j ∈ S,lam j)*m-C₀*b*n) ≤
          RelativeAsymptotics.envelope C C₀ C₁ (d*R) C₃ b n *
            Real.exp (RelativeAsymptotics.envelope C C₀ C₁ (d*R) C₃ b n) := by
  obtain ⟨C,hC,hrel⟩ := relative_exterior_core (E:=EuclideanSpace ℝ (Fin d)) d K₀
  obtain ⟨C₁,hC₁,hinterval⟩ := exists_uniform_interval_constant d D hD
  refine ⟨C,C₁,hC,hC₁,?_⟩
  intro A U V T lam S m γ g K b n C₀ R C₃ ε hb hn hbn hC₀ hR hC₃
    hg hK hKD hm hUV hVU hA hlam hf hs hU hV hε hε₁ hεle hnorm hnear
  have hseg := hinterval A U V lam S m γ g K (b*n) hbn hg hK hKD hUV hVU hA hf hs hU hV
  have hp : S.card ≤ d := by simpa using S.card_le_univ
  have hbound := hrel S.card hp
    (fun t => Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t)) T m
    (∑ j ∈ S,lam j) (C₁*(b*n)) ε hε hε₁
    (fun t ht => by simpa only [Matrix.l2_opNorm_toEuclideanCLM] using hnorm t ht) hnear hseg
  exact RelativeAsymptotics.uniform_relative_bound _ _ _ _ b n C C₀ C₁ (d*R) C₃ m
    hb hn hC hC₀ hC₃ (by positivity) hε hm (by ring_nf; rfl)
    (rate_sum_abs_le lam S hR hlam) hεle hbound
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.EuclideanSplitting
open Set ExteriorStability RelativeProduct ShortDerivative
open scoped Matrix.Norms.L2Operator

/-- The uniform, all-rank, choice-independent relative error for derivatives
of actual nonlinear orbit compositions. All interval bounds are derived from
the genuine gauge equations, and the perturbations from the one-step C²
bounds and the orbit tube. No long-iterate regularity bound is assumed. -/
theorem actual_uniform_relative (d : ℕ) (K₀ Dg : ℝ) (hDg : 0 ≤ Dg) :
    ∃ C C₁ : ℝ, 0 ≤ C ∧ 0 ≤ C₁ ∧
      ∀ (f : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (x y : ℕ → EuclideanSpace ℝ (Fin d)) (s : ℕ → Set (EuclideanSpace ℝ (Fin d)))
        (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
        (S : Finset (Fin d)) (m : ℕ) (γ g K b n C₀ R D : ℝ),
        0 ≤ b → 0 ≤ n → 1 ≤ b*n → 0 ≤ C₀ → 0 ≤ R → 0 ≤ D →
        0 ≤ g → 0 ≤ K → K ≤ Dg*(b*n) → (m:ℝ) ≤ 2*n →
        (∀ t, U t*V t=1) → (∀ t,V t*U t=1) →
        (∀ t < m, (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
          (fderiv ℝ (f t) (x t))*U t=U (t+1)*rate lam 1) →
        (∀ i,|lam i| ≤ R) →
        (∀ j ∈ S, γ+g ≤ lam j) → (∀ j ∉ S, lam j ≤ γ-g) →
        (∀ t ≤ m, ‖U t‖ ≤ Real.exp K) → (∀ t ≤ m, ‖V t‖ ≤ Real.exp K) →
        D*Real.exp (-(3/2:ℝ)*SmoothScales.B b*n) ≤ 1 →
        (∀ t < m, f t (x t)=x (t+1) ∧ f t (y t)=y (t+1)) →
        (∀ t < m, x t∈s t ∧ y t∈s t ∧ Convex ℝ (s t) ∧
          (∀ z∈s t,DifferentiableAt ℝ (f t) z) ∧
          (∀ z∈s t,DifferentiableAt ℝ (fderiv ℝ (f t)) z) ∧
          (∀ z∈s t,‖fderiv ℝ (f t) z‖≤K₀) ∧
          (∀ z∈s t,‖fderiv ℝ (fderiv ℝ (f t)) z‖≤D)) →
        (∀ t < m,‖y t-x t‖≤Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)) →
        ‖exterior S.card (fderiv ℝ (iterate f m) (y 0)) -
          exterior S.card (fderiv ℝ (iterate f m) (x 0))‖ /
            Real.exp ((∑ j ∈ S,lam j)*m-C₀*b*n) ≤
          RelativeAsymptotics.envelope C C₀ C₁ (d*R) D b n *
            Real.exp (RelativeAsymptotics.envelope C C₀ C₁ (d*R) D b n) := by
  obtain ⟨C,C₁,hC,hC₁,hh⟩ := uniform_relative_gauged d K₀ Dg hDg
  refine ⟨C,C₁,hC,hC₁,?_⟩
  intro f x y s U V lam S m γ g K b n C₀ R D hb hn hbn hC₀ hR hD
    hg hK hKD hm hUV hVU hA hlam hf hs hU hV hε horbit hpatch hshadow
  let A := fun t => (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm (fderiv ℝ (f t) (x t))
  let T := fun t => fderiv ℝ (f t) (y t)
  have he (t : ℕ) : Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t)=fderiv ℝ (f t) (x t) := by
    exact (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).apply_symm_apply _
  have hnorm (t : ℕ) (ht : t < m) : ‖A t‖≤K₀ := by
    rw [←Matrix.l2_opNorm_toEuclideanCLM,he]
    exact (hpatch t ht).2.2.2.2.2.1 _ (hpatch t ht).1
  have hnear (t : ℕ) (ht : t < m) : ‖T t-Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t)‖≤
      D*Real.exp (-(3/2:ℝ)*SmoothScales.B b*n) := by
    rw [he]
    obtain ⟨hx,hy,hconv,hf,hff,_,hsecond⟩ := hpatch t ht
    exact (hconv.norm_image_sub_le_of_norm_fderiv_le hff hsecond hx hy).trans
      (mul_le_mul_of_nonneg_left (hshadow t ht) hD)
  have hbound := hh A U V T lam S m γ g K b n C₀ R D
    (D*Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)) hb hn hbn hC₀ hR hD hg hK hKD hm
    hUV hVU hA hlam hf hs hU hV (by positivity) hε le_rfl hnorm hnear
  have hx := derivative_iterate f x
    (fun t => Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t)) m (fun t ht => (horbit t ht).1)
    (fun t ht => by rw [he]; exact ((hpatch t ht).2.2.2.1 _ (hpatch t ht).1).hasFDerivAt)
  have hy := derivative_iterate f y T m (fun t ht => (horbit t ht).2)
    (fun t ht => ((hpatch t ht).2.2.2.1 _ (hpatch t ht).2.1).hasFDerivAt)
  rwa [←hx.fderiv,←hy.fderiv] at hbound
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The nonautonomous chart composition has exactly the same germ as the
actual long iterate in the two endpoint charts. Intermediate chart codes
therefore never have to be encoded in the partition or switch labels. -/
theorem iterate_localMap_germ (S : Diffeomorph I I M M ∞) (a : ℕ → M) (x : M)
    (N : ℕ) (hx : ∀ t≤N,(S^[t]) x∈(extChartAt I (a t)).source)
    (hint : (extChartAt I (a 0)) x∈interior (range I)) :
    ShortDerivative.iterate (fun t => localMap I S (a t) (a (t+1))) N =ᶠ[𝓝 ((extChartAt I (a 0)) x)]
      extChartAt I (a N) ∘ S^[N] ∘ (extChartAt I (a 0)).symm := by
  have hx0 : x∈(extChartAt I (a 0)).source := hx 0 (Nat.zero_le _)
  induction N with
  | zero =>
    have ht := extChartAt_target_mem_nhdsWithin' hx0
    rw [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp hint)] at ht
    filter_upwards [ht] with u hu
    exact ((extChartAt I (a 0)).right_inv hu).symm
  | succ N ih =>
    have hi := ih (fun t ht => hx t (by omega))
    have hc : ContinuousAt (S^[N] ∘ (extChartAt I (a 0)).symm) ((extChartAt I (a 0)) x) :=
      (S.continuous.iterate N).continuousAt.comp (continuousAt_extChartAt_symm' hx0)
    have hs : ∀ᶠ u in 𝓝 ((extChartAt I (a 0)) x),
        (S^[N]) ((extChartAt I (a 0)).symm u)∈(extChartAt I (a N)).source := by
      apply hc.preimage_mem_nhds
      apply (isOpen_extChartAt_source (I := I) (a N)).mem_nhds
      simpa only [Function.comp_apply,(extChartAt I (a 0)).left_inv hx0] using hx N (by omega)
    filter_upwards [hi,hs] with u hu hsu
    change (extChartAt I (a (N+1))) (S ((extChartAt I (a N)).symm
      (ShortDerivative.iterate (fun t => localMap I S (a t) (a (t+1))) N u))) = _
    rw [hu]
    simp only [Function.comp_apply,(extChartAt I (a N)).left_inv hsu,Function.iterate_succ_apply']
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology Metric EuclideanSplitting ExteriorStability ShortDerivative
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- The relative exterior estimate for the ACTUAL long iterate, in the old
input's endpoint charts. The constants are uniform over all ranks, rates,
gauges and selectors. The tube condition is imposed on the genuine new orbit;
no assumed derivative or determinant estimate is used. -/
theorem actual_endpoint_relative (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (L : ι → Set M)
    (hL : ∀ i,IsCompact (L i)) (hLU : ∀ i,L i⊆(chartAt H (a i)).source)
    (Dg : ℝ) (hDg : 0≤Dg) :
    ∃ r K₀ C C₁ : ℝ,0 < r ∧ 1≤K₀ ∧ 0≤C ∧ 0≤C₁ ∧
      ∀ (c : M → ι) (x y : M) (m : ℕ)
        (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
        (T : Finset (Fin d)) (γ g K b n C₀ R : ℝ),
        (∀ z,z∈L (c z)) → 0≤b → 0≤n → 1≤b*n → 0≤C₀ → 0≤R →
        0≤g → 0≤K → K≤Dg*(b*n) → (m:ℝ)≤2*n →
        (∀ t,U t*V t=1) → (∀ t,V t*U t=1) →
        (∀ t < m,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
          (coord I S (a (c (S^[t] x))) (a (c (S^[t+1] x))) (S^[t] x))*U t=
            U (t+1)*rate lam 1) →
        (∀ i,|lam i|≤R) → (∀ j∈T,γ+g≤lam j) → (∀ j∉T,lam j≤γ-g) →
        (∀ t ≤ m,‖U t‖≤Real.exp K) → (∀ t ≤ m,‖V t‖≤Real.exp K) →
        K₀*Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)≤1 →
        Real.exp (-(3/2:ℝ)*SmoothScales.B b*n) ≤ r →
        (∀ t ≤ m,(S^[t]) y∈(extChartAt I (a (c (S^[t] x)))).source) →
        (∀ t ≤ m,‖(extChartAt I (a (c (S^[t] x)))) (S^[t] y)-
          (extChartAt I (a (c (S^[t] x)))) (S^[t] x)‖≤
            Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)) →
        (∀ t ≤ m,closedBall ((extChartAt I (a (c (S^[t] x)))) (S^[t] x))
          (Real.exp (-(3/2:ℝ)*SmoothScales.B b*n))⊆interior (range I)) →
        let F := extChartAt I (a (c (S^[m] x))) ∘ S^[m] ∘ (extChartAt I (a (c x))).symm
        let ux := (extChartAt I (a (c x))) x
        let uy := (extChartAt I (a (c x))) y
        ‖exterior T.card (fderiv ℝ F uy)-exterior T.card (fderiv ℝ F ux)‖ /
          Real.exp ((∑ j∈T,lam j)*m-C₀*b*n)≤
            RelativeAsymptotics.envelope C C₀ C₁ (d*R) K₀ b n *
              Real.exp (RelativeAsymptotics.envelope C C₀ C₁ (d*R) K₀ b n) := by
  obtain ⟨r,K₀,hr,hK₀,hc₂⟩ := actual_uniform_c2 I hclosed S a L hL hLU
  obtain ⟨C,C₁,hC,hC₁,hrel⟩ := actual_uniform_relative d K₀ Dg hDg
  refine ⟨r,K₀,C,C₁,hr,hK₀,hC,hC₁,?_⟩
  intro c x y m U V lam T γ g K b n C₀ R hc hb hn hbn hC₀ hR hg hK hKD hm
    hUV hVU hstep hlam hfast hslow hU hV hε hεr hychart htube hsafe F ux uy
  let ca (t : ℕ) := a (c (S^[t] x))
  let xv (t : ℕ) := (extChartAt I (ca t)) (S^[t] x)
  let yv (t : ℕ) := (extChartAt I (ca t)) (S^[t] y)
  let δ := Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)
  let f (t : ℕ) := localMap I S (ca t) (ca (t+1))
  let s (t : ℕ) := closedBall (xv t) δ
  have hxchart (t : ℕ) : S^[t] x∈(extChartAt I (ca t)).source  := by
    simpa only [extChartAt_source,ca] using hLU (c (S^[t] x)) (hc (S^[t] x))
  have hxc (t : ℕ) : xv t∈s t := mem_closedBall_self (Real.exp_nonneg _)
  have hyc (t : ℕ) (ht : t ≤ m) : yv t∈s t := by
    exact mem_closedBall.mpr (by simpa only [dist_eq_norm] using htube t ht)
  have hreg (t : ℕ) (ht : t < m) (z : EuclideanSpace ℝ (Fin d)) (hz : z∈s t) :
      ContDiffAt ℝ ∞ (f t) z ∧ ‖fderiv ℝ (f t) z‖≤K₀ ∧
        ‖fderiv ℝ (fderiv ℝ (f t)) z‖≤K₀ := by
    have hh := hc₂ (c (S^[t] x)) (c (S^[t+1] x)) (S^[t] x) (hc _)
      (by simpa only [Function.iterate_succ_apply'] using hc (S^[t+1] x))
    exact hh.2 z (closedBall_subset_closedBall hεr hz) (hsafe t ht.le hz)
  have hstep' (t : ℕ) (ht : t < m) :
      (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm (fderiv ℝ (f t) (xv t))*U t=
        U (t+1)*rate lam 1 := by
    have hsrc : S (S^[t] x)∈(chartAt H (ca (t+1))).source := by
      simpa only [extChartAt_source,Function.iterate_succ_apply'] using hxchart (t+1)
    have hd := hasFDerivAt_localMap I S (ca t) (ca (t+1)) (S^[t] x)
      ⟨by simpa only [extChartAt_source] using hxchart t,hsrc⟩ (hsafe t ht.le (hxc t))
    rw [show fderiv ℝ (f t) (xv t)=coord I S (ca t) (ca (t+1)) (S^[t] x) from hd.fderiv]
    exact hstep t ht
  have horbit (t : ℕ) (ht : t < m) : f t (xv t)=xv (t+1) ∧ f t (yv t)=yv (t+1) := by
    simp only [f,localMap,Function.comp_apply,xv,yv,
      (extChartAt I (ca t)).left_inv (hxchart t),
      (extChartAt I (ca t)).left_inv (hychart t ht.le),Function.iterate_succ_apply']
    trivial
  have he := hrel f xv yv s U V lam T m γ g K b n C₀ R K₀ hb hn hbn hC₀ hR
    (by linarith) hg hK hKD hm hUV hVU hstep' hlam hfast hslow hU hV hε horbit
    (fun t ht => ⟨hxc t,hyc t ht.le,convex_closedBall _ _,
      fun z hz => (hreg t ht z hz).1.differentiableAt (by simp),
      fun z hz => ((hreg t ht z hz).1.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp),
      fun z hz => (hreg t ht z hz).2.1,fun z hz => (hreg t ht z hz).2.2⟩)
    (fun t ht => htube t ht.le)
  have egx := iterate_localMap_germ I S ca x m (fun t _ => hxchart t)
    (hsafe 0 (Nat.zero_le _) (hxc 0))
  have egy := iterate_localMap_germ I S ca y m hychart
    (hsafe 0 (Nat.zero_le _) (hyc 0 (Nat.zero_le _)))
  dsimp only [f,xv,yv] at he
  simp only [Function.iterate_zero_apply] at he
  rw [egx.fderiv_eq (𝕜:=ℝ),egy.fderiv_eq (𝕜:=ℝ)] at he
  exact he
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ShortDerivative
open scoped ContDiff Matrix.Norms.L2Operator
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma contDiffAt_iterate (f : ℕ → E → E) (x : ℕ → E) (N : ℕ)
    (hx : ∀ t<N,f t (x t)=x (t+1))
    (hf : ∀ t<N,ContDiffAt ℝ ∞ (f t) (x t)) :
    ContDiffAt ℝ ∞ (iterate f N) (x 0) := by
  induction N with
  | zero => exact contDiffAt_id
  | succ N ih =>
    have hi := ih (fun t ht => hx t (by omega)) (fun t ht => hf t (by omega))
    have he := orbit_eq_iterate f x (N+1) hx N (by omega)
    have hN := hf N (by omega)
    rw [←he] at hN
    exact hN.comp (x 0) hi
end SmoothObstruction.ShortDerivative

namespace SmoothObstruction.EuclideanSplitting
open ShortDerivative RelativeProduct
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A gauge for the actual one-step differentials identifies the derivative
of the true orbit composition with its genuine transition matrix. -/
lemma derivative_transition (f : ℕ → E → E) (x : ℕ → E)
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ) (N : ℕ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (hx : ∀ t<N,f t (x t)=x (t+1))
    (hd : ∀ t<N,DifferentiableAt ℝ (f t) (x t))
    (hstep : ∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (fderiv ℝ (f t) (x t))*U t=U (t+1)*rate lam 1) :
    HasFDerivAt (iterate f N)
      (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam 0 N)) (x 0) := by
  let A := fun t => (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm (fderiv ℝ (f t) (x t))
  have he (t : ℕ) : Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t)=fderiv ℝ (f t) (x t) :=
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).apply_symm_apply _
  have hh := derivative_iterate f x (fun t => Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t))
    N hx (fun t ht => by rw [he]; exact (hd t ht).hasFDerivAt)
  rw [segment_toEuclidean,propagator_eq_transition A U V lam hUV hVU N hstep 0 N (by omega)] at hh
  simpa only [Nat.zero_add] using hh
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology ShortDerivative EuclideanSplitting
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Regularity of the actual endpoint expression in the old charts, not a
formal composition with unrelated derivatives. -/
theorem actual_endpoint_smooth (S : Diffeomorph I I M M ∞) (a : ℕ → M) (x : M) (n : ℕ)
    (hx : ∀ t ≤ n,S^[t] x∈(extChartAt I (a t)).source)
    (hi : ∀ t ≤ n,(extChartAt I (a t)) (S^[t] x)∈interior (range I)) :
    ContDiffAt ℝ ∞ (extChartAt I (a n) ∘ S^[n] ∘ (extChartAt I (a 0)).symm)
      ((extChartAt I (a 0)) x) := by
  let f (t : ℕ) := localMap I S (a t) (a (t+1))
  let u (t : ℕ) := (extChartAt I (a t)) (S^[t] x)
  have hf (t : ℕ) (ht : t < n) : ContDiffAt ℝ ∞ (f t) (u t) := by
    apply contDiffAt_localMap I S (a t) (a (t+1)) (S^[t] x)
    · exact ⟨by simpa only [extChartAt_source] using hx t ht.le,
        by simpa only [extChartAt_source,Set.mem_preimage,Function.iterate_succ_apply'] using hx (t+1) (by omega)⟩
    · exact hi t ht.le
  have ho (t : ℕ) (ht : t < n) : f t (u t)=u (t+1) := by
    simp only [f,u,localMap,Function.comp_apply,(extChartAt I (a t)).left_inv (hx t ht.le),
      Function.iterate_succ_apply']
  have hs := ShortDerivative.contDiffAt_iterate f u n ho hf
  have he := iterate_localMap_germ I S a x n hx (by simpa using hi 0 (Nat.zero_le n))
  exact hs.congr_of_eventuallyEq he.symm

/-- The old endpoint differential is exactly the transition of its real
one-step gauge. This equality permits relative exterior control to feed the
leading-minor estimate at zero rank as well as positive rank. -/
theorem actual_endpoint_differential (S : Diffeomorph I I M M ∞) (a : ℕ → M)
    (x : M) (n : ℕ) (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hx : ∀ t ≤ n,S^[t] x∈(extChartAt I (a t)).source)
    (hi : ∀ t ≤ n,(extChartAt I (a t)) (S^[t] x)∈interior (range I))
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (hstep : ∀ t < n,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I S (a t) (a (t+1)) (S^[t] x))*U t=U (t+1)*rate lam 1) :
    HasFDerivAt (extChartAt I (a n) ∘ S^[n] ∘ (extChartAt I (a 0)).symm)
      (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam 0 n))
        ((extChartAt I (a 0)) x) := by
  let f (t : ℕ) := localMap I S (a t) (a (t+1))
  let u (t : ℕ) := (extChartAt I (a t)) (S^[t] x)
  have hf (t : ℕ) (ht : t < n) : HasFDerivAt (f t)
      (coord I S (a t) (a (t+1)) (S^[t] x)) (u t) := by
    apply hasFDerivAt_localMap I S (a t) (a (t+1)) (S^[t] x)
    · exact ⟨by simpa only [extChartAt_source] using hx t ht.le,
        by simpa only [extChartAt_source,Set.mem_preimage,Function.iterate_succ_apply'] using hx (t+1) (by omega)⟩
    · exact hi t ht.le
  have ho (t : ℕ) (ht : t < n) : f t (u t)=u (t+1) := by
    simp only [f,u,localMap,Function.comp_apply,(extChartAt I (a t)).left_inv (hx t ht.le),
      Function.iterate_succ_apply']
  have hs := EuclideanSplitting.derivative_transition f u U V lam n hUV hVU ho
    (fun t ht => (hf t ht).differentiableAt)
    (fun t ht => by rw [(hf t ht).fderiv]; exact hstep t ht)
  have he := iterate_localMap_germ I S a x n hx (by simpa using hi 0 (Nat.zero_le n))
  exact hs.congr_of_eventuallyEq he.symm
end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_TubeProjection
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.ManifoldCoordinates
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} (S : Diffeomorph I I M M ∞) (a : ι → M) (c : M → ι)
    {n : ℕ} {B R : ℝ} {x : M}

/-- The two true middle subspaces agree exactly. -/
lemma BilateralGauge.backwardSpace_zero (A : BilateralGauge I S a c n B R x)
    (T : Finset (Fin d)) :
    A.backwardSpace I S a c 0 T=A.forwardSpace I S a c 0 T := by
  simp only [BilateralGauge.backwardSpace,BilateralGauge.forwardSpace,A.centerU,A.centerV]
end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_EndpointFrames
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Filter Topology
open scoped Real

namespace SmoothObstruction.EndpointFrame
open Set Matrix
open scoped EuclideanGeometry
variable {d p : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Finite endpoint coordinates are selected from a genuine ambient orthonormal
basis, including the empty and full-dimensional endpoint groups. -/
theorem exists_frame (W : Submodule ℝ E) (hdim : Module.finrank ℝ W=p) :
    ∃ (b : OrthonormalBasis (Fin d) ℝ E) (r : powersetCard (Fin d) p),
      (∀ j∈r,b j∈W) ∧ (∀ j∉r,b j∈Wᗮ) ∧
      (∀ x∈W,∀ j∉r,b.repr x j=0) := by
  classical
  let V : Bool → Submodule ℝ E := fun q => if q then W else Wᗮ
  have hV : DirectSum.IsInternal V := by
    apply (DirectSum.isInternal_submodule_iff_isCompl V (i:=true) (j:=false) (by decide)
      (by ext q; cases q <;> simp)).mpr
    exact W.isCompl_orthogonal
  have horth : OrthogonalFamily ℝ (fun q => V q) (fun q => (V q).subtypeₗᵢ) := by
    intro i j hij x y
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact Submodule.inner_left_of_mem_orthogonal y.property x.property
    · exact Submodule.inner_right_of_mem_orthogonal x.property y.property
    · exact (hij rfl).elim
  have hn : Module.finrank ℝ E=d := finrank_euclideanSpace_fin
  let b := hV.subordinateOrthonormalBasis hn horth
  let c : Fin d → Bool := fun j => hV.subordinateOrthonormalBasisIndex hn j horth
  let r₀ : Finset (Fin d) := Finset.univ.filter (fun j => c j=true)
  have hc : r₀.card=p := by
    exact (hV.card_filter_subordinateOrthonormalBasisIndex_eq hn horth true).trans hdim
  let r : powersetCard (Fin d) p := ⟨r₀,hc⟩
  have hb (j : Fin d) : b j∈V (c j) :=
    hV.subordinateOrthonormalBasis_subordinate hn j horth
  have hmem (j : Fin d) : j∈r ↔ c j=true := by
    change j∈r₀ ↔ c j=true
    simp only [r₀,Finset.mem_filter,Finset.mem_univ,true_and]
  have hy (j : Fin d) (hj : j∈r) : b j∈W := by
    simpa only [(hmem j).mp hj,V,ite_true] using hb j
  have hz (j : Fin d) (hj : j∉r) : b j∈Wᗮ := by
    have ht : c j=false := Bool.eq_false_of_not_eq_true (fun h => hj ((hmem j).mpr h))
    simpa only [ht,V,Bool.false_eq_true,ite_false] using hb j
  refine ⟨b,r,hy,hz,?_⟩
  intro x hx j hj
  rw [b.repr_apply_apply]
  exact Submodule.inner_left_of_mem_orthogonal hx (hz j hj)

end SmoothObstruction.EndpointFrame

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric EuclideanSplitting ExteriorStability EndpointFrame
open scoped ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- A genuine old-chart endpoint map has the controlled minor used in the
four-equation inverse theorem. Every nonlinear derivative estimate is derived
from the original orbit tube and the real one-step gauge. Constants precede
all ranks, bins, times and gauge choices. -/
theorem actual_endpoint_minor (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (L : ι → Set M)
    (hL : ∀ i,IsCompact (L i)) (hLU : ∀ i,L i⊆(chartAt H (a i)).source)
    (Dg : ℝ) (hDg : 0≤Dg) :
    ∃ r K₀ Crel C₁ : ℝ,0 < r ∧ 1≤K₀ ∧ 0≤Crel ∧ 0≤C₁ ∧
      ∀ {p q : ℕ} (c : M → ι) (x y : M) (m : ℕ)
        (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
        (T : Finset (Fin d)) (_ : T.card=p) (γ g K b n R C δ β : ℝ),
        (∀ z,z∈L (c z)) → 0≤b → 0≤n → 1≤b*n → 0≤R →
        0≤g → 0≤K → K≤Dg*(b*n) → (m : ℝ)≤2*n → 0≤C → 0≤δ →
        ∀ (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1),
        (∀ t < m,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
          (coord I S (a (c (S^[t] x))) (a (c (S^[t+1] x))) (S^[t] x))*U t=
            U (t+1)*rate lam 1) →
        (∀ i,|lam i|≤R) → (∀ j∈T,γ+g≤lam j) → (∀ j∉T,lam j≤γ-g) →
        (∀ t ≤ m,‖U t‖≤Real.exp K) → (∀ t ≤ m,‖V t‖≤Real.exp K) →
        K₀*Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)≤1 →
        Real.exp (-(3/2:ℝ)*SmoothScales.B b*n) ≤ r →
        (∀ t ≤ m,(S^[t]) y∈(extChartAt I (a (c (S^[t] x)))).source) →
        (∀ t ≤ m,‖(extChartAt I (a (c (S^[t] x)))) (S^[t] y)-
          (extChartAt I (a (c (S^[t] x)))) (S^[t] x)‖≤
            Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)) →
        (∀ t ≤ m,closedBall ((extChartAt I (a (c (S^[t] x)))) (S^[t] x))
          (Real.exp (-(3/2:ℝ)*SmoothScales.B b*n))⊆interior (range I)) →
        (∀ A : E₀ →L[ℝ] E₀,‖exterior p A‖≤C*(max 1 ‖A‖)^p) →
        ∀ (W G Gslow : Submodule ℝ E₀) (_ : Module.finrank ℝ W=p),
        (‖(groupSpace (U m) (V m) (hUV m) (hVU m) T).starProjection-
          W.starProjection‖≤1/2) →
        (‖(groupSpace (U 0) (V 0) (hUV 0) (hVU 0) T).starProjection-
          G.starProjection‖≤δ) →
        (‖(groupSpace (U 0) (V 0) (hUV 0) (hVU 0) Tᶜ).starProjection-
          Gslow.starProjection‖≤δ) →
        ∀ (bE : OrthonormalBasis (Fin d) ℝ E₀) (rE : powersetCard (Fin d) p),
        (∀ j∈rE,bE j∈W) → (∀ v∈W,∀ j∉rE,bE.repr v j=0) →
        ∀ (v : Fin p → E₀) (z : Fin q → E₀),Orthonormal ℝ v →
        (∀ i,v i∈G) → (∀ j,z j∈Gslow) → (∀ j,‖z j‖≤1) →
        let L₀ := (C*(Real.exp K)^p)^2*(C*2^p)
        let N₀ := C*(C^2*(Real.exp K)^(2*p)*(Fintype.card (powersetCard (Fin d) p) : ℝ))
        let N₁ := C*(C*(Real.exp K)^p)^2*(Fintype.card (powersetCard (Fin d) p) : ℝ)*‖continuousWedge (E := E₀) p‖
        let ζ := RelativeAsymptotics.envelope Crel 0 C₁ (d*R) K₀ b n *
          Real.exp (RelativeAsymptotics.envelope Crel 0 C₁ (d*R) K₀ b n)
        let ε := 2*L₀*C*ζ*‖continuousWedge (E := E₀) p‖
        let θ := 2*L₀*(N₁*Real.exp (-2*g*m)+N₀*unitWedgeConstant (E := E₀) p*δ)
        (frameWedgeConstant (E := E₀) p*δ)*(1+L₀*N₀)≤1/2 →
        ε≤1/100 → (θ+ε)/(1-ε)≤β →
        let F := extChartAt I (a (c (S^[m] x))) ∘ S^[m] ∘ (extChartAt I (a (c x))).symm
        GoodEndpoint β bE rE v z F ((extChartAt I (a (c x))) y)
          (endpointMatrix bE p rE (fderiv ℝ F ((extChartAt I (a (c x))) x)) v) := by
  obtain ⟨r,K₀,Crel,C₁,hr,hK₀,hCrel,hC₁,hrel⟩ :=
    actual_endpoint_relative I hclosed S a L hL hLU Dg hDg
  refine ⟨r,K₀,Crel,C₁,hr,hK₀,hCrel,hC₁,?_⟩
  intro p q c x y m U V lam T hTp γ g K b n R C δ β hc hb hn hbn hR
    hg hK hKD hm hC hδ hUV hVU hstep hlam hfast hslow hU hV hε hεr
    hychart htube hsafe hpoly W G Gslow hdim hend hstart hstartSlow bE rE hrE hcoords
    v z horth hv hz hznorm L₀ N₀ N₁ ζ ε θ hsmall hεsmall hgraph F
  subst p
  let p := T.card
  let ca (t : ℕ) := a (c (S^[t] x))
  have hxchart (t : ℕ) : S^[t] x∈(extChartAt I (ca t)).source := by
    simpa only [extChartAt_source,ca] using hLU (c (S^[t] x)) (hc (S^[t] x))
  have hxint (t : ℕ) (ht : t ≤ m) :
      (extChartAt I (ca t)) (S^[t] x)∈interior (range I) :=
    hsafe t ht (mem_closedBall_self (Real.exp_nonneg _))
  have hyint (t : ℕ) (ht : t ≤ m) :
      (extChartAt I (ca t)) (S^[t] y)∈interior (range I) :=
    hsafe t ht (mem_closedBall.mpr (by simpa only [dist_eq_norm] using htube t ht))
  have hd := actual_endpoint_differential I S ca x m U V lam
    (fun t _ => hxchart t) hxint hUV hVU hstep
  have hcd := actual_endpoint_smooth I S ca y m hychart hyint
  have hdf := hd.fderiv
  change fderiv ℝ F ((extChartAt I (a (c x))) x)=_ at hdf
  have hpert := hrel c x y m U V lam T γ g K b n 0 R hc hb hn hbn (by norm_num)
    hR hg hK hKD hm hUV hVU hstep hlam hfast hslow hU hV hε hεr hychart htube hsafe
  simp only [zero_mul,sub_zero] at hpert
  rw [hdf] at hpert
  have hdiff : ‖exterior p (fderiv ℝ F ((extChartAt I (a (c x))) y))-
      exterior p (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam 0 m))‖≤
      ζ*Real.exp ((m : ℝ)*(∑ j∈T,lam j)) := by
    simpa only [F,ζ,mul_comm (m : ℝ)] using (div_le_iff₀ (Real.exp_pos _)).mp hpert
  have hζ : 0≤ζ := by dsimp [ζ,RelativeAsymptotics.envelope]; positivity
  have heps : ε<1 := lt_of_le_of_lt hεsmall (by norm_num)
  have hminor := endpoint_bounds U V lam hUV hVU T rfl m hg hK hC hδ hfast hslow
    (hU 0 (Nat.zero_le m)) (hU m le_rfl) (hV 0 (Nat.zero_le m)) (hV m le_rfl)
    hpoly W G Gslow hdim hend hstart hstartSlow bE rE hrE hcoords
    v horth hv z hz hznorm hsmall (fderiv ℝ F ((extChartAt I (a (c x))) y)) hζ heps hdiff
  change ContDiffAt ℝ ∞ F ((extChartAt I (a (c x))) y) at hcd
  dsimp only [GoodEndpoint]
  rw [hdf]
  exact ⟨hcd,hminor.1,hminor.2.2.1.trans hεsmall,
    fun i j => (hminor.2.2.2 i j).trans hgraph⟩
end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_EndpointMass
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric EuclideanSplitting ExteriorStability EndpointFrame
open scoped ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- The original orbit-tube endpoint minor, now with the actual bilateral
finite-time gauge. This is uniform in every starting bin and every rank. -/
theorem gauge_endpoint_minor (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (L : ι → Set M)
    (hL : ∀ i,IsCompact (L i)) (hLU : ∀ i,L i⊆(chartAt H (a i)).source)
    (Dg : ℝ) (hDg : 0≤Dg) :
    ∃ r K₀ Crel C₁ : ℝ,0 < r ∧ 1≤K₀ ∧ 0≤Crel ∧ 0≤C₁ ∧
      ∀ {p q : ℕ} (c : M → ι) (x y : M) (n : ℕ) (b R C δ β γ g : ℝ)
        (A : BilateralGauge I S a c n (Dg*(b*n)) R x)
        (T : Finset (Fin d)) (_ : T.card=p),
        (∀ z,z∈L (c z)) → 0≤b → 1≤b*n → 0≤R → 0≤g → 0≤C → 0≤δ →
        (∀ j∈T,γ+g≤A.lam j) → (∀ j∉T,A.lam j≤γ-g) →
        let ρ := Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)
        K₀*ρ≤1 → ρ ≤ r → originalTube I S a c (n:=n) ρ x y →
        (∀ t : Fin (n+1),closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) ρ⊆interior (range I)) →
        (∀ B : E₀ →L[ℝ] E₀,‖exterior p B‖≤C*(max 1 ‖B‖)^p) →
        ∀ (W G Gslow : Submodule ℝ E₀),Module.finrank ℝ W=p →
        (‖(A.forwardSpace I S a c n T).starProjection-W.starProjection‖≤1/2) →
        (‖(A.forwardSpace I S a c 0 T).starProjection-G.starProjection‖≤δ) →
        (‖(A.forwardSpace I S a c 0 Tᶜ).starProjection-Gslow.starProjection‖≤δ) →
        ∀ (bE : OrthonormalBasis (Fin d) ℝ E₀) (rE : powersetCard (Fin d) p),
        (∀ j∈rE,bE j∈W) → (∀ v∈W,∀ j∉rE,bE.repr v j=0) →
        ∀ (v : Fin p → E₀) (z : Fin q → E₀),Orthonormal ℝ v →
        (∀ i,v i∈G) → (∀ j,z j∈Gslow) → (∀ j,‖z j‖≤1) →
        let K := Dg*(b*n)
        let L₀ := (C*(Real.exp K)^p)^2*(C*2^p)
        let N₀ := C*(C^2*(Real.exp K)^(2*p)*(Fintype.card (powersetCard (Fin d) p) : ℝ))
        let N₁ := C*(C*(Real.exp K)^p)^2*(Fintype.card (powersetCard (Fin d) p) : ℝ)*‖continuousWedge (E := E₀) p‖
        let ζ := RelativeAsymptotics.envelope Crel 0 C₁ (d*R) K₀ b n *
          Real.exp (RelativeAsymptotics.envelope Crel 0 C₁ (d*R) K₀ b n)
        let ε := 2*L₀*C*ζ*‖continuousWedge (E := E₀) p‖
        let θ := 2*L₀*(N₁*Real.exp (-2*g*n)+N₀*unitWedgeConstant (E := E₀) p*δ)
        (frameWedgeConstant (E := E₀) p*δ)*(1+L₀*N₀)≤1/2 →
        ε≤1/100 → (θ+ε)/(1-ε)≤β →
        let F := extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I (a (c x))).symm
        GoodEndpoint β bE rE v z F ((extChartAt I (a (c x))) y)
          (endpointMatrix bE p rE (fderiv ℝ F ((extChartAt I (a (c x))) x)) v) := by
  obtain ⟨r,K₀,Crel,C₁,hr,hK₀,hCrel,hC₁,hh⟩ := actual_endpoint_minor I hclosed S a L hL hLU Dg hDg
  refine ⟨r,K₀,Crel,C₁,hr,hK₀,hCrel,hC₁,?_⟩
  intro p q c x y n b R C δ β γ g A T hTp hc hb hbn hR hg hC hδ hfast hslow ρ hρ hρr ht hs
  apply hh c x y n A.UF A.VF A.lam T hTp γ g (Dg*(b*n)) b n R C δ β hc hb
    (Nat.cast_nonneg n) hbn hR hg (by positivity) le_rfl (by nlinarith [show (0:ℝ)≤(n:ℝ) from Nat.cast_nonneg n]) hC hδ
    (fun t => (A.invF t).1) (fun t => (A.invF t).2) A.stepF A.rate_bound hfast hslow
    (fun t ht => (A.normF t ht).1) (fun t ht => (A.normF t ht).2) hρ hρr
    (fun t htn => by simpa only [extChartAt_source] using (ht ⟨t,by omega⟩).1) (fun t htn => (ht ⟨t,by omega⟩).2)
    (fun t htn => hs ⟨t,by omega⟩)
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric EuclideanSplitting ExteriorStability EndpointFrame
open scoped ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- One authentic frame and one original leading matrix control the whole
old-chart orbit tube. Neither the frame nor the normalization is reselected
at the perturbed point. -/
theorem gauge_endpoint_family (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (L : ι → Set M)
    (hL : ∀ i,IsCompact (L i)) (hLU : ∀ i,L i⊆(chartAt H (a i)).source)
    (Dg : ℝ) (hDg : 0≤Dg) :
    ∃ r K₀ Crel C₁ : ℝ,0 < r ∧ 1≤K₀ ∧ 0≤Crel ∧ 0≤C₁ ∧
      ∀ {p q : ℕ} (c : M → ι) (x : M) (n : ℕ) (b R C δ β γ g : ℝ)
        (A : BilateralGauge I S a c n (Dg*(b*n)) R x)
        (T : Finset (Fin d)) (_ : T.card=p),
        (∀ z,z∈L (c z)) → 0≤b → 1≤b*n → 0≤R → 0≤g → 0≤C → 0≤δ →
        (∀ j∈T,γ+g≤A.lam j) → (∀ j∉T,A.lam j≤γ-g) →
        let ρ := Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)
        K₀*ρ≤1 → ρ ≤ r →
        (∀ t : Fin (n+1),closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) ρ⊆interior (range I)) →
        (∀ B : E₀ →L[ℝ] E₀,‖exterior p B‖≤C*(max 1 ‖B‖)^p) →
        ∀ (W G Gslow : Submodule ℝ E₀),Module.finrank ℝ W=p →
        (‖(A.forwardSpace I S a c n T).starProjection-W.starProjection‖≤1/2) →
        (‖(A.forwardSpace I S a c 0 T).starProjection-G.starProjection‖≤δ) →
        (‖(A.forwardSpace I S a c 0 Tᶜ).starProjection-Gslow.starProjection‖≤δ) →
        ∀ (u : OrthonormalBasis (Fin p) ℝ G) (v : OrthonormalBasis (Fin q) ℝ Gslow),
        EndpointBudget.admissible d p Dg R C K₀ Crel C₁ b n g δ β →
        ∃ (bE : OrthonormalBasis (Fin d) ℝ E₀) (rE : powersetCard (Fin d) p)
          (D : Matrix (Fin p) (Fin p) ℝ),
          (∀ j∈rE,bE j∈W) ∧ (∀ v∈W,∀ j∉rE,bE.repr v j=0) ∧
          ∀ y,originalTube I S a c (n:=n) ρ x y →
            let F := extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I (a (c x))).symm
            GoodEndpoint β bE rE (fun i => (u i:E₀)) (fun i => (v i:E₀)) F
              ((extChartAt I (a (c x))) y) D := by
  obtain ⟨r,K₀,Crel,C₁,hr,hK₀,hCrel,hC₁,hm⟩ := gauge_endpoint_minor I hclosed S a L hL hLU Dg hDg
  refine ⟨r,K₀,Crel,C₁,hr,hK₀,hCrel,hC₁,?_⟩
  intro p q c x n b R C δ β γ g A T hTp hc hb hbn hR hg hC hδ hf hs ρ hρ hρr hsafe hpoly
    W G Gslow hdim hend hstart hstartSlow u v hbud
  obtain ⟨bE,rE,hrE,_,hzero⟩ := EndpointFrame.exists_frame W hdim
  let F := extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I (a (c x))).symm
  let D := endpointMatrix bE p rE (fderiv ℝ F ((extChartAt I (a (c x))) x)) (fun i => (u i:E₀))
  refine ⟨bE,rE,D,hrE,hzero,?_⟩
  intro y hy
  have hu : Orthonormal ℝ (fun i => (u i:E₀)) := u.orthonormal.comp_linearIsometry G.subtypeₗᵢ
  have hvnorm (i : Fin q) : ‖(v i:E₀)‖≤1 := by
    change ‖v i‖≤1
    exact le_of_eq (v.norm_eq_one i)
  exact hm c x y n b R C δ β γ g A T hTp hc hb hbn hR hg hC hδ hf hs hρ hρr hy hsafe
    hpoly W G Gslow hdim hend hstart hstartSlow bE rE hrE hzero
    (fun i => (u i:E₀)) (fun i => (v i:E₀)) hu (fun i => (u i).property)
    (fun i => (v i).property) hvnorm hbud.1 hbud.2.1 hbud.2.2

end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_GlobalSwitching
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric EuclideanSplitting ExteriorStability EndpointFrame
open scoped ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- Both original endpoint families from a SINGLE bilateral gauge. The inverse
family uses exactly its reversed gauge, not an unrelated certificate. All
constants precede ranks, labels, gauges, and the common starting bases. -/
theorem bilateral_endpoint_control (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (L : ι → Set M)
    (hL : ∀ i,IsCompact (L i)) (hLU : ∀ i,L i⊆(chartAt H (a i)).source)
    (Dg : ℝ) (hDg : 0≤Dg) :
    ∃ rF K₀F CreF C₁F rB K₀B CreB C₁B : ℝ,
      0 < rF ∧ 1≤K₀F ∧ 0≤CreF ∧ 0≤C₁F ∧ 0 < rB ∧ 1≤K₀B ∧ 0≤CreB ∧ 0≤C₁B ∧
      ∀ {p q : ℕ} (c : M → ι) (x : M) (n : ℕ) (b R C δ β γ g : ℝ)
        (A : BilateralGauge I S a c n (Dg*(b*n)) R x)
        (T : Finset (Fin d)) (_ : T.card=p) (_ : Tᶜ.card=q),
        (∀ z,z∈L (c z)) → 0≤b → 1≤b*n → 0≤R → 0≤g → 0≤C → 0≤δ →
        (∀ j∈T,γ+g≤A.lam j) → (∀ j∉T,A.lam j≤γ-g) →
        let ρ := Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)
        K₀F*ρ≤1 → ρ ≤ rF → K₀B*ρ≤1 → ρ ≤ rB →
        (∀ t : Fin (n+1),closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) ρ⊆interior (range I)) →
        (∀ B : E₀ →L[ℝ] E₀,‖exterior p B‖≤C*(max 1 ‖B‖)^p) →
        (∀ B : E₀ →L[ℝ] E₀,‖exterior q B‖≤C*(max 1 ‖B‖)^q) →
        ∀ (Wf Wb U V : Submodule ℝ E₀),Module.finrank ℝ Wf=p → Module.finrank ℝ Wb=q →
        (‖(A.forwardSpace I S a c n T).starProjection-Wf.starProjection‖≤1/2) →
        (‖(A.backwardSpace I S a c n Tᶜ).starProjection-Wb.starProjection‖≤1/2) →
        (‖(A.forwardSpace I S a c 0 T).starProjection-U.starProjection‖≤δ) →
        (‖(A.forwardSpace I S a c 0 Tᶜ).starProjection-V.starProjection‖≤δ) →
        ∀ (u : OrthonormalBasis (Fin p) ℝ U) (v : OrthonormalBasis (Fin q) ℝ V),
        EndpointBudget.admissible d p Dg R C K₀F CreF C₁F b n g δ β →
        EndpointBudget.admissible d q Dg R C K₀B CreB C₁B b n g δ β →
        OriginalEndpointControl I S a c n ρ β Wf (fun i => (u i:E₀)) (fun i => (v i:E₀)) x ∧
        OriginalEndpointControl I S.symm a c n ρ β Wb (fun i => (v i:E₀)) (fun i => (u i:E₀)) x := by
  obtain ⟨rF,K₀F,CreF,C₁F,hrF,hKF,hCrF,hCF,hF⟩ := gauge_endpoint_family I hclosed S a L hL hLU Dg hDg
  obtain ⟨rB,K₀B,CreB,C₁B,hrB,hKB,hCrB,hCB,hB⟩ := gauge_endpoint_family I hclosed S.symm a L hL hLU Dg hDg
  refine ⟨rF,K₀F,CreF,C₁F,rB,K₀B,CreB,C₁B,hrF,hKF,hCrF,hCF,hrB,hKB,hCrB,hCB,?_⟩
  intro p q c x n b R C δ β γ g A T hTp hTq hc hb hbn hR hg hC hδ hf hs ρ hρF hrF' hρB hrB'
    hsafe hpolyF hpolyB Wf Wb U V hdimF hdimB hendF hendB hstartF hstartB u v hbudF hbudB
  constructor
  · exact hF c x n b R C δ β γ g A T hTp hc hb hbn hR hg hC hδ hf hs hρF hrF'
      (fun t => (hsafe t).1) hpolyF Wf U V hdimF hendF hstartF hstartB u v hbudF
  · have hf' (j : Fin d) (hj : j∈Tᶜ) : -γ+g≤(A.reverse I S a c).lam j := by
      have h := hs j (Finset.mem_compl.mp hj)
      change -γ+g≤ -A.lam j
      linarith
    have hs' (j : Fin d) (hj : j∉Tᶜ) : (A.reverse I S a c).lam j≤ -γ-g := by
      have h := hf j (by simpa only [Finset.mem_compl,not_not] using hj)
      change -A.lam j≤ -γ-g
      linarith
    apply hB c x n b R C δ β (-γ) g (A.reverse I S a c) Tᶜ hTq hc hb hbn hR hg hC hδ
      hf' hs' hρB hrB' (fun t => (hsafe t).2) hpolyB Wb V U hdimB
    · simpa only [BilateralGauge.reverse_forwardSpace] using hendB
    · simpa only [BilateralGauge.reverse_forwardSpace,BilateralGauge.backwardSpace_zero] using hstartB
    · simpa only [BilateralGauge.reverse_forwardSpace,BilateralGauge.backwardSpace_zero,compl_compl] using hstartF
    · exact hbudB
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set EuclideanSplitting
open scoped ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (S : Diffeomorph I I M M ∞) {ι : Type*} (a : ι → M) (c : M → ι)
    {n : ℕ} {B R : ℝ} {x : M} (A : BilateralGauge I S a c n B R x)

lemma BilateralGauge.forwardSpace_compl (t : ℕ) (T : Finset (Fin d)) :
    IsCompl (A.forwardSpace I S a c t T) (A.forwardSpace I S a c t Tᶜ) := by
  have hh := (EuclideanSplitting.splitting A.UF A.VF A.lam
    (fun t => (A.invF t).1) (fun t => (A.invF t).2) T).ranges_isCompl t
  rw [EuclideanSplitting.splitting_slow_range,EuclideanSplitting.splitting_fast_range] at hh
  exact hh

/-- The common starting bases are orthonormal within each actual gauge group;
no global orthogonality or conditioning of their union is postulated. -/
theorem BilateralGauge.forwardSpace_bases (t : ℕ) (T : Finset (Fin d)) :
    Nonempty (OrthonormalBasis (Fin T.card) ℝ (A.forwardSpace I S a c t T)) ∧
    Nonempty (OrthonormalBasis (Fin (d-T.card)) ℝ (A.forwardSpace I S a c t Tᶜ)) := by
  have hF : Module.finrank ℝ (A.forwardSpace I S a c t T)=T.card := finrank_groupSpace _ _ _ _ _
  have hB : Module.finrank ℝ (A.forwardSpace I S a c t Tᶜ)=d-T.card := by
    rw [show Module.finrank ℝ (A.forwardSpace I S a c t Tᶜ)=Tᶜ.card from finrank_groupSpace _ _ _ _ _]
    simp only [Finset.card_compl,Fintype.card_fin]
  exact ⟨⟨(stdOrthonormalBasis ℝ _).reindex (finCongr hF)⟩,
    ⟨(stdOrthonormalBasis ℝ _).reindex (finCongr hB)⟩⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology EndpointFrame
open scoped Manifold ContDiff
variable {d p q : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    {ι : Type*}
lemma OriginalEndpointControl.mono {S : Diffeomorph I I M M ∞} {a : ι → M} {c : M → ι}
    {n : ℕ} {ρ σ β : ℝ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    {u : Fin p → EuclideanSpace ℝ (Fin d)} {v : Fin q → EuclideanSpace ℝ (Fin d)} {x : M}
    (h : OriginalEndpointControl I S a c n σ β W u v x) (hρ : ρ≤σ) :
    OriginalEndpointControl I S a c n ρ β W u v x := by
  obtain ⟨b,r,D,hb,hr,hg⟩ := h
  exact ⟨b,r,D,hb,hr,fun y hy => hg y (fun t => ⟨(hy t).1,(hy t).2.trans hρ⟩)⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology EndpointFrame
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

omit [MeasurableSpace M] [BorelSpace M] in
/-- A genuine pair germ from three bilateral gauges in the ORIGINAL atlas.
All radii and minor tolerances precede the finite labels and the fast rank. -/
theorem gauge_original_germ_sharp_oai (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    (Dg : ℝ) (hDg : 0≤Dg) :
    ∃ r Cg β K₀F CreF C₁F K₀B CreB C₁B : ℝ,
      0 < r ∧ 1≤Cg ∧ 0<β ∧ 1≤K₀F ∧ 0≤CreF ∧ 0≤C₁F ∧
      1≤K₀B ∧ 0≤CreB ∧ 0≤C₁B ∧
      ∀ {A J : Type*} (c : M → ι)
        (P : M → A) (L : M → J) (R : Set M)
        (Wf Wb : A×A → Submodule ℝ E₀) (n : ℕ) (b R₀ Cext δ ε γ g ρ : ℝ)
        (Φ : M×M → M×M) (G : Set (M×M)) (x y : M),
        let σ := Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)
        (∀ z,z∈K (c z)) → (∀ u v,P u=P v → c u=c v) → c x=c y →
        0≤b → 1≤b*n → 0≤R₀ → 0≤Cext → 0≤ε → 0≤g →
        0≤ρ → ρ≤σ → σ ≤ r → Cg*ρ<δ → K₀F*σ≤1 → K₀B*σ≤1 →
        (∀ p≤d,∀ B : E₀ →L[ℝ] E₀,‖ExteriorStability.exterior p B‖≤Cext*(max 1 ‖B‖)^p) →
        (∀ p≤d,EndpointBudget.admissible d p Dg R₀ Cext K₀F CreF C₁F b n g ε β) →
        (∀ p≤d,EndpointBudget.admissible d p Dg R₀ Cext K₀B CreB C₁B b n g ε β) →
        (∀ u∈G,u.1∈R ∧ u.2∈R ∧ L u.1=L u.2) →
        (∀ u∈R,∀ v∈R,L u=L v → ∀ z,
          originalTube I S a c (n:=n) δ u z → originalTube I S.symm a c (n:=n) δ v z →
          originalEndpoint I S a c (n:=n) (Wf (P u,P (S^[n] u))) u z →
          originalEndpoint I S.symm a c (n:=n) (Wb (P v,P (S.symm^[n] v))) v z → z=(Φ (u,v)).1) →
        (∀ u∈R,∀ v∈R,L u=L v →
          originalTube I S a c (n:=n) δ v (Φ (u,v)).2 ∧
          originalTube I S.symm a c (n:=n) δ u (Φ (u,v)).2 ∧
          originalEndpoint I S a c (n:=n) (Wf (P v,P (S^[n] v))) v (Φ (u,v)).2 ∧
          originalEndpoint I S.symm a c (n:=n) (Wb (P u,P (S.symm^[n] u))) u (Φ (u,v)).2) →
        (∀ t : Fin (n+1),
          closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) σ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) σ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S^[t.val] y)))) (S^[t.val] y)) σ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] y)))) (S.symm^[t.val] y)) σ⊆interior (range I)) →
        let z := (Φ (x,y)).1
        let w := (Φ (x,y)).2
        originalTube I S a c (n:=n) ρ x z → originalTube I S.symm a c (n:=n) ρ y z →
        originalTube I S a c (n:=n) ρ y w → originalTube I S.symm a c (n:=n) ρ x w →
        let a₀ := a (c x)
        let X := (extChartAt I a₀) x
        let Y := (extChartAt I a₀) y
        ∀ (x₀ : M) (Ar : BilateralGauge I S a c n (Dg*(b*n)) R₀ x₀)
          (Ax : BilateralGauge I S a c n (Dg*(b*n)) R₀ x)
          (Ay : BilateralGauge I S a c n (Dg*(b*n)) R₀ y)
          (Tr Tx Ty : Finset (Fin d)),Tx.card=Tr.card → Ty.card=Tr.card →
          (∀ j∈Tx,γ+g≤Ax.lam j) → (∀ j∉Tx,Ax.lam j≤γ-g) →
          (∀ j∈Ty,γ+g≤Ay.lam j) → (∀ j∉Ty,Ay.lam j≤γ-g) →
          Module.finrank ℝ (Wf (P x,P (S^[n] x)))=Tr.card →
          Module.finrank ℝ (Wf (P y,P (S^[n] y)))=Tr.card →
          Module.finrank ℝ (Wb (P x,P (S.symm^[n] x)))=d-Tr.card →
          Module.finrank ℝ (Wb (P y,P (S.symm^[n] y)))=d-Tr.card →
          ‖(Ax.forwardSpace I S a c n Tx).starProjection-(Wf (P x,P (S^[n] x))).starProjection‖≤1/2 →
          ‖(Ay.forwardSpace I S a c n Ty).starProjection-(Wf (P y,P (S^[n] y))).starProjection‖≤1/2 →
          ‖(Ax.backwardSpace I S a c n Txᶜ).starProjection-(Wb (P x,P (S.symm^[n] x))).starProjection‖≤1/2 →
          ‖(Ay.backwardSpace I S a c n Tyᶜ).starProjection-(Wb (P y,P (S.symm^[n] y))).starProjection‖≤1/2 →
          ‖(Ax.forwardSpace I S a c 0 Tx).starProjection-(Ar.forwardSpace I S a c 0 Tr).starProjection‖≤ε →
          ‖(Ay.forwardSpace I S a c 0 Ty).starProjection-(Ar.forwardSpace I S a c 0 Tr).starProjection‖≤ε →
          ‖(Ax.forwardSpace I S a c 0 Txᶜ).starProjection-(Ar.forwardSpace I S a c 0 Trᶜ).starProjection‖≤ε →
          ‖(Ay.forwardSpace I S a c 0 Tyᶜ).starProjection-(Ar.forwardSpace I S a c 0 Trᶜ).starProjection‖≤ε →
          originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z →
          originalEndpoint I S a c (n:=n) (Wf (P y,P (S^[n] y))) y w →
          originalEndpoint I S.symm a c (n:=n) (Wb (P x,P (S.symm^[n] x))) x w →
          originalEndpoint I S.symm a c (n:=n) (Wb (P y,P (S.symm^[n] y))) y z →
          (∀ᶠ t in 𝓝 (X,Y),
            P ((extChartAt I a₀).symm t.1)=P x ∧ P ((extChartAt I a₀).symm t.2)=P y ∧
            P (S^[n] ((extChartAt I a₀).symm t.1))=P (S^[n] x) ∧
            P (S^[n] ((extChartAt I a₀).symm t.2))=P (S^[n] y) ∧
            P (S.symm^[n] ((extChartAt I a₀).symm t.1))=P (S.symm^[n] x) ∧
            P (S.symm^[n] ((extChartAt I a₀).symm t.2))=P (S.symm^[n] y)) →
          let e := Prod.map (ChartDensity.coordinates I a₀) (ChartDensity.coordinates I a₀)
          let s := Prod.map (ChartDensity.inverse I a₀) (ChartDensity.inverse I a₀)
          ∃ Ψ : E₀×E₀ → E₀×E₀,HasFDerivAt Ψ (fderiv ℝ Ψ (X,Y)) (X,Y) ∧
            (81/121:ℝ)≤|(fderiv ℝ Ψ (X,Y)).det| ∧
            Ψ =ᶠ[𝓝[ChartDomination.coordinateSet e s G] (X,Y)] (e ∘ Φ ∘ s) := by
  classical
  obtain ⟨rG,Cg,β,hrG,hCg,hβ,hgerm⟩ := family_original_germ_uniform I hclosed a K hK hKU
  obtain ⟨rF,K₀F,CreF,C₁F,rB,K₀B,CreB,C₁B,hrF,hKF,hCrF,hCF,hrB,hKB,hCrB,hCB,hcontrol⟩ :=
    bilateral_endpoint_control I hclosed S a K hK hKU Dg hDg
  refine ⟨min rG (min rF rB),Cg,β,K₀F,CreF,C₁F,K₀B,CreB,C₁B,
    lt_min hrG (lt_min hrF hrB),hCg,hβ,hKF,hCrF,hCF,hKB,hCrB,hCB,?_⟩
  intro A J c P L R Wf Wb n b R₀ Cext δ ε γ g ρ Φ G x y σ hc hPc hcxy
    hb hbn hR₀ hCext hε hg hρ hρσ hσr hρδ hρF hρB hpoly hbudF hbudB
    hG huniq hsecond hsafe z w ht1 ht2 ht3 ht4 a₀ X Y
    x₀ Ar Ax Ay Tr Tx Ty hTx hTy hfx hsx hfy hsy hdimFx hdimFy hdimBx hdimBy
    hendFx hendFy hendBx hendBy hstartFx hstartFy hstartBx hstartBy he₀ he₁ he₂ he₃ hlabels e s
  let U := Ar.forwardSpace I S a c 0 Tr
  let V := Ar.forwardSpace I S a c 0 Trᶜ
  have hcompl : IsCompl U V := Ar.forwardSpace_compl I S a c 0 Tr
  obtain ⟨⟨u⟩,⟨v⟩⟩ := Ar.forwardSpace_bases I S a c 0 Tr
  have hp : Tr.card≤d := by simpa using Tr.card_le_univ
  have hq : d-Tr.card≤d := Nat.sub_le _ _
  have hTx' : Txᶜ.card=d-Tr.card := by simp only [Finset.card_compl,Fintype.card_fin,hTx]
  have hTy' : Tyᶜ.card=d-Tr.card := by simp only [Finset.card_compl,Fintype.card_fin,hTy]
  have hρrG := hρσ.trans (hσr.trans (min_le_left _ _))
  have hρrF := hσr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρrB := hσr.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcx := hcontrol c x n b R₀ Cext ε β γ g Ax Tx hTx hTx' hc hb hbn hR₀ hg hCext hε
    hfx hsx hρF hρrF hρB hρrB (fun t => ⟨(hsafe t).1,(hsafe t).2.1⟩)
    (hpoly _ hp) (hpoly _ hq) (Wf (P x,P (S^[n] x))) (Wb (P x,P (S.symm^[n] x))) U V
    hdimFx hdimBx hendFx hendBx hstartFx hstartBx u v (hbudF _ hp) (hbudB _ hq)
  have hcy := hcontrol c y n b R₀ Cext ε β γ g Ay Ty hTy hTy' hc hb hbn hR₀ hg hCext hε
    hfy hsy hρF hρrF hρB hρrB (fun t => ⟨(hsafe t).2.2.1,(hsafe t).2.2.2⟩)
    (hpoly _ hp) (hpoly _ hq) (Wf (P y,P (S^[n] y))) (Wb (P y,P (S.symm^[n] y))) U V
    hdimFy hdimBy hendFy hendBy hstartFy hstartBy u v (hbudF _ hp) (hbudB _ hq)
  have hsafeρ : ∀ t : Fin (n+1),
      closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) ρ⊆interior (range I) ∧
      closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) ρ⊆interior (range I) ∧
      closedBall ((extChartAt I (a (c (S^[t.val] y)))) (S^[t.val] y)) ρ⊆interior (range I) ∧
      closedBall ((extChartAt I (a (c (S.symm^[t.val] y)))) (S.symm^[t.val] y)) ρ⊆interior (range I) := by
    intro t
    exact ⟨(closedBall_subset_closedBall hρσ).trans (hsafe t).1,
      (closedBall_subset_closedBall hρσ).trans (hsafe t).2.1,
      (closedBall_subset_closedBall hρσ).trans (hsafe t).2.2.1,
      (closedBall_subset_closedBall hρσ).trans (hsafe t).2.2.2⟩
  exact hgerm hp hq S c P L R Wf Wb n ρ δ Φ G x y hc hPc hcxy hρ hρrG hρδ
    hG huniq hsecond hsafeρ ht1 ht2 ht3 ht4 U V hcompl u v
    (hcx.1.mono I hρσ) (hcy.1.mono I hρσ) (hcx.2.mono I hρσ) (hcy.2.mono I hρσ) he₀ he₁ he₂ he₃ hlabels
end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.SmoothObstruction.ManifoldCoordinates.gauge_original_germ_sharp_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.SmoothObstruction.ManifoldCoordinates.gauge_original_germ_sharp_oai.{u_1, u_2, u_3, u_4, u_5}
