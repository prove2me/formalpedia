-- Prove2me | solution 1 for OAI.SmoothObstruction.EuclideanSplitting.endpoint_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:17:00.727983+00:00
-- url     : https://prove2.me/submissions/8fc5d534-a8cf-4031-9d93-05b93b63344c

import Mathlib
import Definitions.Def_OAIQ5T3000

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
open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

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

/-- The fast determinant line has the exact sum rate before either endpoint
change of gauge. This is the genuine volume-line lower input. -/
lemma gauge_line_preimage_lower (p : ℕ) (U V P D : E →L[ℝ] E)
    (hdiag : D=V*P*U) {a K : ℝ}
    (hV : ‖exterior p V‖≤K)
    (v : (⋀[ℝ]^p E)) (hv : exterior p D v=a • v) :
    |a| *‖v‖≤K*‖exterior p P (exterior p U v)‖ := by
  have he : exterior p D v=exterior p V (exterior p P (exterior p U v)) := by
    rw [hdiag,exterior_mul,exterior_mul]
    rfl
  have hn := (exterior p V).le_opNorm (exterior p P (exterior p U v))
  rw [←he,hv,norm_smul,Real.norm_eq_abs] at hn
  exact hn.trans (mul_le_mul_of_nonneg_right hV (norm_nonneg _))

lemma gauge_line_lower (p : ℕ) (U V P D : E →L[ℝ] E)
    (hdiag : D=V*P*U) {a K : ℝ} (hK : 0≤K)
    (hU : ‖exterior p U‖≤K) (hV : ‖exterior p V‖≤K)
    (v : (⋀[ℝ]^p E)) (hv : exterior p D v=a • v) :
    |a| *‖exterior p U v‖≤K^2*‖exterior p P (exterior p U v)‖ := by
  have hU' := ((exterior p U).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hU (norm_nonneg _))
  have hP := gauge_line_preimage_lower p U V P D hdiag hV v hv
  calc
    _ ≤ |a| *(K*‖v‖) := mul_le_mul_of_nonneg_left hU' (abs_nonneg _)
    _ = K*(|a| *‖v‖) := by ring
    _ ≤ K*(K*‖exterior p P (exterior p U v)‖) := mul_le_mul_of_nonneg_left hP hK
    _ = _ := by ring

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

lemma finrank_groupSpace (U V : Matrix (Fin d) (Fin d) ℝ)
    (hUV : U*V=1) (hVU : V*U=1) (S : Finset (Fin d)) :
    Module.finrank ℝ (groupSpace U V hUV hVU S)=S.card := by
  rw [groupSpace,LinearEquiv.finrank_map_eq,finrank_coordinateSpace]

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

namespace SmoothObstruction.CloseProjection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma inverse_norm (U V : Submodule ℝ E)
    (hdim : Module.finrank ℝ U=Module.finrank ℝ V)
    (hclose : ‖U.starProjection-V.starProjection‖ ≤ 1/2) :
    ‖(equiv U V hdim hclose).symm.toContinuousLinearMap‖ ≤ 2 := by
  apply (equiv U V hdim hclose).symm.toContinuousLinearMap.opNorm_le_bound (by norm_num)
  intro y
  have hh := lower U V hclose ((equiv U V hdim hclose).symm y)
  rwa [←equiv_apply U V hdim hclose,(equiv U V hdim hclose).apply_symm_apply] at hh

end SmoothObstruction.CloseProjection

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

/-- The actual nonleading diagonal eigenvalue is smaller by exp(-2g l).
This is valid when the slow rates are positive as well as when negative. -/
lemma nonleading_rate_product (lam : Fin d → ℝ) (S : Finset (Fin d))
    {γ g l : ℝ} (hg : 0≤g) (hl : 0≤l)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (q : powersetCard (Fin d) S.card) (hq : q.val≠S) :
    |∏ i : Fin S.card,Real.exp (l*lam (powersetCard.ofFinEmbEquiv.symm q i))|≤
      Real.exp (l*((∑ j∈S,lam j)-2*g)) := by
  rw [eigen_exp_product,abs_of_pos (Real.exp_pos _),selected_sum]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (RateSums.strict_rate_sum_gap lam S q.val hg q.prop hq hfast hslow) hl)
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ExteriorStability
open Module Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

lemma projectedMinor_eq_det (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (s : powersetCard ι p) (A : E →L[ℝ] E) (v : Fin p → E) :
    projectedMinor b p s A v=
      Matrix.det (fun i j : Fin p => b.repr (A (v i)) (powersetCard.ofFinEmbEquiv.symm s j)) := by
  change (b.exteriorPower p).toBasis.repr (exteriorPower.map p A.toLinearMap
    (exteriorPower.ιMulti ℝ p v)) s=_
  rw [exteriorPower.map_apply_ιMulti,b.toBasis_exteriorPower,
    exteriorPower.basis_repr_apply,exteriorPower.ιMultiDual_apply_ιMulti]
  rfl

lemma projectedMinor_transfer (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (s : powersetCard ι p) (A B : E →L[ℝ] E) (v : Fin p → E) :
    |projectedMinor b p s B v-projectedMinor b p s A v|≤
      ‖exterior p B-exterior p A‖*‖exteriorPower.ιMulti ℝ p v‖ := by
  let e := b.exteriorPower p
  let w := exteriorPower.ιMulti ℝ p v
  have hcoord (z : (⋀[ℝ]^p E)) : |e.repr z s|≤‖z‖ := by
    rw [e.repr_apply_apply,←Real.norm_eq_abs]
    simpa only [e.norm_eq_one,one_mul] using norm_inner_le_norm (𝕜:=ℝ) (e s) z
  have h := hcoord ((exterior p B-exterior p A) w)
  simp only [sub_apply,map_sub] at h
  exact h.trans ((exterior p B-exterior p A).le_opNorm w)

/-- Basis-change and orbit-transfer errors are paid against the true exterior
operator norm. No coarse n-step C² estimate is substituted. -/
lemma projectedMinor_basis_transfer (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (s : powersetCard ι p) (A B : E →L[ℝ] E) (v w : Fin p → E) :
    |projectedMinor b p s B w-projectedMinor b p s A v|≤
      ‖exterior p B-exterior p A‖*‖exteriorPower.ιMulti ℝ p w‖+
      ‖exterior p A‖*‖exteriorPower.ιMulti ℝ p w-exteriorPower.ιMulti ℝ p v‖ := by
  have hb : |projectedMinor b p s A w-projectedMinor b p s A v|≤
      ‖exterior p A‖*‖exteriorPower.ιMulti ℝ p w-exteriorPower.ιMulti ℝ p v‖ := by
    let e := b.exteriorPower p
    have he : projectedMinor b p s A w-projectedMinor b p s A v=
        e.repr (exterior p A (exteriorPower.ιMulti ℝ p w-exteriorPower.ιMulti ℝ p v)) s := by
      simp only [map_sub,e,projectedMinor,PiLp.sub_apply]
    rw [he,e.repr_apply_apply,←Real.norm_eq_abs]
    exact (norm_inner_le_norm (𝕜:=ℝ) (e s) _).trans (by
      rw [e.norm_eq_one,one_mul]
      exact (exterior p A).le_opNorm _)
  exact (abs_sub_le _ _ _).trans
    (add_le_add (projectedMinor_transfer b p s A B w) hb)

end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.ExteriorStability
open Set Module Set.powersetCard
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- A projected top wedge actually lies on the selected determinant line.
In particular its coefficient is its norm, including the empty group. -/
lemma projected_wedge_line (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (s : powersetCard ι p) (v : Fin p → E)
    (hv : ∀ i j,j∉s → b.repr (v i) j=0) :
    exteriorPower.ιMulti ℝ p v=
      projectedMinor b p s (ContinuousLinearMap.id ℝ E) v • (b.exteriorPower p) s := by
  classical
  have hm (q : powersetCard ι p) :
      projectedMinor b p q (ContinuousLinearMap.id ℝ E) v=
        (b.exteriorPower p).repr (exteriorPower.ιMulti ℝ p v) q := by
    unfold projectedMinor
    change (b.exteriorPower p).repr (exterior p 1 _) q=_
    rw [exterior_one]
    rfl
  apply (b.exteriorPower p).repr.injective
  ext q
  by_cases hq : q=s
  · subst q
    simp only [map_smul,OrthonormalBasis.repr_self,PiLp.smul_apply,smul_eq_mul,
      PiLp.single_apply,ite_true,mul_one]
    exact (hm s).symm
  · have hz : projectedMinor b p q (ContinuousLinearMap.id ℝ E) v=0 := by
      rw [projectedMinor_eq_det]
      obtain ⟨j,hjq,hjs⟩ := (exists_mem_notMem_iff_ne q s).mp hq
      obtain ⟨i,rfl⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem q j).mpr hjq
      apply Matrix.det_eq_zero_of_column_eq_zero i
      intro k
      exact hv k _ hjs
    rw [←hm q]
    rw [hz,map_smul,OrthonormalBasis.repr_self]
    simp [hq]

lemma projected_wedge_norm (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (s : powersetCard ι p) (v : Fin p → E)
    (hv : ∀ i j,j∉s → b.repr (v i) j=0) :
    ‖exteriorPower.ιMulti ℝ p v‖=
      |projectedMinor b p s (ContinuousLinearMap.id ℝ E) v| := by
  rw [projected_wedge_line b p s v hv,norm_smul,
    (b.exteriorPower p).norm_eq_one,mul_one,Real.norm_eq_abs]

/-- Quantitative projected leading-volume lower bound from the actual
finite gauge and a left inverse of the endpoint projection on the fast
vectors. The eigenvalue may converge to zero; it is never replaced by 1. -/
theorem projected_gauge_lower (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (s : powersetCard ι p) (U V D A Q J : E →L[ℝ] E)
    (v : Fin p → E) (a K H : ℝ) (hK : 0≤K)
    (hdiag : D=V*A*U)
    (hU : ‖exterior p U‖≤K) (hV : ‖exterior p V‖≤K)
    (hJ : ‖exterior p J‖≤H)
    (heigen : exterior p D (exteriorPower.ιMulti ℝ p v)=
      a • exteriorPower.ιMulti ℝ p v)
    (hleft : ∀ i,J (Q (A (U (v i))))=A (U (v i)))
    (hrange : ∀ i j,j∉s → b.repr (Q (A (U (v i)))) j=0) :
    |a| *‖exterior p U (exteriorPower.ιMulti ℝ p v)‖≤
      K^2*H*|projectedMinor b p s (Q*A*U) v| := by
  have hbase := gauge_line_lower p U V A D hdiag hK hU hV
    (exteriorPower.ιMulti ℝ p v) heigen
  have heq : exterior p J (exterior p Q (exterior p A (exterior p U
      (exteriorPower.ιMulti ℝ p v))))=
      exterior p A (exterior p U (exteriorPower.ιMulti ℝ p v)) := by
    simp only [exterior_apply,exteriorPower.map_apply_ιMulti]
    congr 1
    funext i
    exact hleft i
  have hj := (exterior p J).le_opNorm
    (exterior p Q (exterior p A (exterior p U (exteriorPower.ιMulti ℝ p v))))
  rw [heq] at hj
  have hn : ‖exterior p Q (exterior p A (exterior p U
      (exteriorPower.ιMulti ℝ p v)))‖=|projectedMinor b p s (Q*A*U) v| := by
    simp only [exterior_apply,exteriorPower.map_apply_ιMulti]
    change ‖exteriorPower.ιMulti ℝ p (fun i => Q (A (U (v i))))‖=_
    rw [projected_wedge_norm b p s _ hrange]
    congr 1
    rw [projectedMinor_eq_det,projectedMinor_eq_det]
    rfl
  rw [hn] at hj
  calc
    _ ≤ K^2*‖exterior p A (exterior p U (exteriorPower.ιMulti ℝ p v))‖ := hbase
    _ ≤ K^2*(H*|projectedMinor b p s (Q*A*U) v|) := by
      gcongr
      exact hj.trans (mul_le_mul_of_nonneg_right hJ (abs_nonneg _))
    _ = _ := by ring
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.CloseProjection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma ambientInverse_left (U V : Submodule ℝ E)
    (hdim : Module.finrank ℝ U=Module.finrank ℝ V)
    (hclose : ‖U.starProjection-V.starProjection‖≤1/2) (x : E) (hx : x∈U) :
    ambientInverse U V hdim hclose (V.starProjection x)=x := by
  have hp : V.orthogonalProjectionOnto (V.starProjection x)=V.orthogonalProjectionOnto x := by
    apply Subtype.ext
    change V.starProjection (V.starProjection x)=V.starProjection x
    exact V.starProjection_eq_self_iff.mpr (by simp)
  change ((equiv U V hdim hclose).symm (V.orthogonalProjectionOnto (V.starProjection x)):E)=x
  rw [hp]
  change ((equiv U V hdim hclose).symm (equiv U V hdim hclose ⟨x,hx⟩):E)=x
  rw [ContinuousLinearEquiv.symm_apply_apply]

lemma norm_ambientInverse (U V : Submodule ℝ E)
    (hdim : Module.finrank ℝ U=Module.finrank ℝ V)
    (hclose : ‖U.starProjection-V.starProjection‖≤1/2) :
    ‖ambientInverse U V hdim hclose‖≤2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖(equiv U V hdim hclose).symm (V.orthogonalProjectionOnto x)‖≤2*‖x‖
  apply ((equiv U V hdim hclose).symm.toContinuousLinearMap.le_opNorm _).trans
  apply (mul_le_mul_of_nonneg_right (inverse_norm U V hdim hclose) (norm_nonneg _)).trans
  exact mul_le_mul_of_nonneg_left (V.norm_orthogonalProjectionOnto_apply_le x) (by norm_num)
end SmoothObstruction.CloseProjection

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

lemma transition_group (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (lam : Fin d → ℝ) (s t : ℕ) (S : Finset (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x∈groupSpace (U s) (V s) (hUV s) (hVU s) S) :
    Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t) x∈
      groupSpace (U t) (V t) (hUV t) (hVU t) S := by
  rcases Submodule.mem_map.mp hx with ⟨y,hy,rfl⟩
  apply Submodule.mem_map.mpr
  refine ⟨Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam ((t:ℝ)-s)) y,?_,?_⟩
  · rw [mem_coordinateSpace] at hy ⊢
    intro j hj
    change (rate lam ((t:ℝ)-s)*ᵥ WithLp.ofLp y) j=0
    rw [rate,Matrix.mulVec_diagonal,hy j hj,mul_zero]
  · change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U t)
      (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam ((t:ℝ)-s)) y)=
        Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
          (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U s) y)
    rw [←mul_apply_eq_comp,←mul_apply_eq_comp,←map_mul,←map_mul]
    congr 2
    dsimp [transition]
    rw [mul_assoc _ _ (U s),hVU,mul_one]

end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ExteriorStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The empty as well as every orthonormal determinant line has unit volume. -/
lemma norm_wedge_orthonormal (p : ℕ) (v : Fin p → E) (hv : Orthonormal ℝ v) :
    ‖exteriorPower.ιMulti ℝ p v‖=1 := by
  have hg : Matrix.gram ℝ v=1 := by
    ext i j
    exact (orthonormal_iff_ite.mp hv) i j
  have hh := exteriorPower.inner_ιMulti_self v
  rw [hg,Matrix.det_one,real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg (exteriorPower.ιMulti ℝ p v)]
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

lemma rate_coordinate_wedge (lam : Fin d → ℝ) (l : ℝ) (p : ℕ)
    (q : powersetCard (Fin d) p) (v : Fin p → EuclideanSpace ℝ (Fin d))
    (hv : ∀ i,v i∈coordinateSpace q.val) :
    exterior p (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam l))
      (exteriorPower.ιMulti ℝ p v)=
      Real.exp (l*(∑ j∈q.val,lam j)) • exteriorPower.ιMulti ℝ p v := by
  let b₀ := EuclideanSpace.basisFun (Fin d) ℝ
  have hc : ∀ i j,j∉q → b₀.repr (v i) j=0 := by
    intro i j hj
    exact (mem_coordinateSpace q.val (v i)).mp (hv i) j hj
  have he := exterior_eigen_basis b₀ p
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam l))
    (fun j => Real.exp (l*lam j)) (rate_eigen lam l) q
  rw [eigen_exp_product,selected_sum] at he
  rw [projected_wedge_line b₀ p q v hc,map_smul,he]
  exact smul_comm _ _ _

end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ExteriorStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- A diagonal map on the orthogonal complement of one determinant line. -/
lemma diagonal_missing_line_bound (b : OrthonormalBasis ι ℝ E)
    (T : E →L[ℝ] E) (a : ι → ℝ) (ha : ∀ i,T (b i)=a i • b i)
    (i₀ : ι) (x : E) (hx : b.repr x i₀=0)
    {K : ℝ} (hK : 0≤K) (hbound : ∀ i,i≠i₀ → |a i|≤K) :
    ‖T x‖≤(Fintype.card ι:ℝ)*K*‖x‖ := by
  classical
  have hrepr : x=∑ i,(b.repr x i) • b i := (b.sum_repr x).symm
  calc
    ‖T x‖=‖∑ i,(b.repr x i) • T (b i)‖ := by
      conv_lhs => rw [hrepr]
      simp only [map_sum,map_smul]
    _ ≤ ∑ i,‖(b.repr x i) • T (b i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι,K*‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i=i₀
      · subst i
        simp only [hx,zero_smul,norm_zero]
        positivity
      · rw [ha,norm_smul,norm_smul,b.norm_eq_one,mul_one,Real.norm_eq_abs,Real.norm_eq_abs]
        have hc : |b.repr x i|≤‖x‖ := by
          rw [b.repr_apply_apply,←Real.norm_eq_abs]
          simpa only [b.norm_eq_one,one_mul] using norm_inner_le_norm (𝕜:=ℝ) (b i) x
        calc
          _ ≤ ‖x‖*K := mul_le_mul hc (hbound i hi) (abs_nonneg _) (norm_nonneg _)
          _ = _ := mul_comm _ _
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

lemma coordinate_wedge_missing_fast (S : Finset (Fin d))
    (v : Fin S.card → EuclideanSpace ℝ (Fin d))
    (i₀ : Fin S.card) (hslow : v i₀∈coordinateSpace Sᶜ) :
    ((EuclideanSpace.basisFun (Fin d) ℝ).exteriorPower S.card).repr
      (exteriorPower.ιMulti ℝ S.card v) (⟨S,rfl⟩ : powersetCard (Fin d) S.card)=0 := by
  let b₀ := EuclideanSpace.basisFun (Fin d) ℝ
  have he : projectedMinor b₀ S.card ⟨S,rfl⟩ (ContinuousLinearMap.id ℝ _) v=0 := by
    rw [projectedMinor_eq_det]
    apply Matrix.det_eq_zero_of_row_eq_zero i₀
    intro j
    apply (mem_coordinateSpace Sᶜ _).mp hslow
    simp only [Finset.mem_compl,not_not]
    rw [powersetCard.ofFinEmbEquiv_symm_apply]
    exact Finset.orderEmbOfFin_mem _ _ _
  change (b₀.exteriorPower S.card).repr (exterior S.card 1 (exteriorPower.ιMulti ℝ S.card v)) ⟨S,rfl⟩=0 at he
  rw [exterior_one] at he
  exact he

/-- True nonleading volume suppression for the diagonal propagator, applied
to arbitrary vectors including one slow vector, not merely coordinate
columns. The loss is the exact spectral gap exp(-2g length). -/
lemma rate_nonleading_volume (lam : Fin d → ℝ) (S : Finset (Fin d))
    {γ g l : ℝ} (hg : 0≤g) (hl : 0≤l)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (v : Fin S.card → EuclideanSpace ℝ (Fin d))
    (i₀ : Fin S.card) (hv : v i₀∈coordinateSpace Sᶜ) :
    ‖exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam l))
      (exteriorPower.ιMulti ℝ S.card v)‖≤
      (Fintype.card (powersetCard (Fin d) S.card):ℝ)*
        Real.exp (l*((∑ j∈S,lam j)-2*g))*‖exteriorPower.ιMulti ℝ S.card v‖ := by
  apply diagonal_missing_line_bound
    ((EuclideanSpace.basisFun (Fin d) ℝ).exteriorPower S.card) _
    (fun q => ∏ i : Fin S.card,Real.exp (l*lam (powersetCard.ofFinEmbEquiv.symm q i)))
    (exterior_eigen_basis _ _ _ _ (rate_eigen lam l)) ⟨S,rfl⟩ _
    (coordinate_wedge_missing_fast S v i₀ hv) (Real.exp_nonneg _)
  intro q hq
  apply nonleading_rate_product lam S hg hl hfast hslow q
  intro he
  exact hq (Subtype.ext he)

/-- The actual finite-gauge transition suppresses every maximal starting
wedge containing a slow vector relative to its true fast sum-rate. -/
theorem transition_nonleading_volume
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (S : Finset (Fin d)) {s t : ℕ} (hst : s≤t) {γ g K C : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hU : ‖U t‖≤Real.exp K) (hV : ‖V s‖≤Real.exp K)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card A‖≤C*(max 1 ‖A‖)^S.card)
    (w : Fin S.card → EuclideanSpace ℝ (Fin d))
    (i₀ : Fin S.card) (hw : w i₀∈groupSpace (U s) (V s) (hUV s) (hVU s) Sᶜ) :
    ‖exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t))
      (exteriorPower.ιMulti ℝ S.card w)‖≤
      (C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      Real.exp (((t:ℝ)-s)*((∑ j∈S,lam j)-2*g))*‖exteriorPower.ιMulti ℝ S.card w‖ := by
  let v := fun i => Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (V s) (w i)
  have hv : v i₀∈coordinateSpace Sᶜ := by
    rw [groupSpace,Submodule.map_equiv_eq_comap_symm] at hw
    exact hw
  have he := rate_nonleading_volume lam S hg
    (sub_nonneg.mpr (by exact_mod_cast hst) : 0≤(t:ℝ)-s) hfast hslow v i₀ hv
  have hbnd (M : Matrix (Fin d) (Fin d) ℝ) (hM : ‖M‖≤Real.exp K) :
      ‖exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) M)‖≤C*(Real.exp K)^S.card := by
    apply (hpoly _).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply pow_le_pow_left₀ (by positivity)
    rw [Matrix.l2_opNorm_toEuclideanCLM]
    exact max_le (Real.one_le_exp_iff.mpr hK) hM
  have hwedge : exteriorPower.ιMulti ℝ S.card v=
      exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (V s))
        (exteriorPower.ιMulti ℝ S.card w) := by
    rw [exterior_apply,exteriorPower.map_apply_ιMulti]
    rfl
  have hvb : ‖exteriorPower.ιMulti ℝ S.card v‖≤
      (C*(Real.exp K)^S.card)*‖exteriorPower.ιMulti ℝ S.card w‖ := by
    rw [hwedge]
    exact ((exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (V s))).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hbnd (V s) hV) (norm_nonneg _))
  have htransition : exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t))
      (exteriorPower.ιMulti ℝ S.card w)=
      exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U t))
        (exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam ((t:ℝ)-s)))
          (exteriorPower.ιMulti ℝ S.card v)) := by
    rw [hwedge]
    simp only [transition,map_mul,exterior_mul,mul_apply_eq_comp]
  rw [htransition]
  calc
    _ ≤ ‖exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U t))‖*
      ‖exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam ((t:ℝ)-s)))
        (exteriorPower.ιMulti ℝ S.card v)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (C*(Real.exp K)^S.card)*((Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      Real.exp (((t:ℝ)-s)*((∑ j∈S,lam j)-2*g))*‖exteriorPower.ιMulti ℝ S.card v‖) := by
      exact mul_le_mul (hbnd (U t) hU) he (norm_nonneg _) (by positivity)
    _ ≤ (C*(Real.exp K)^S.card)*((Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      Real.exp (((t:ℝ)-s)*((∑ j∈S,lam j)-2*g))*
        ((C*(Real.exp K)^S.card)*‖exteriorPower.ιMulti ℝ S.card w‖)) := by
      gcongr
    _ = _ := by ring
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ExteriorStability
open Module Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma unit_wedge_bound (p : ℕ) (v : Fin p → E) (hv : ∀ i,‖v i‖≤1) :
    ‖exteriorPower.ιMulti ℝ p v‖≤‖continuousWedge (E:=E) p‖ := by
  have hh := (continuousWedge (E:=E) p).le_opNorm v
  apply hh.trans
  have hp : (∏ i,‖v i‖)≤1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun index _ => hv index)
  exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (mul_one _)

variable {ι : Type*} [Fintype ι] [LinearOrder ι]
lemma projectedMinor_norm_le (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (r : powersetCard ι p) (A : E →L[ℝ] E) (v : Fin p → E) :
    |projectedMinor b p r A v|≤‖exterior p A (exteriorPower.ιMulti ℝ p v)‖ := by
  rw [projectedMinor,(b.exteriorPower p).repr_apply_apply,←Real.norm_eq_abs]
  simpa only [(b.exteriorPower p).norm_eq_one,one_mul] using
    norm_inner_le_norm (𝕜:=ℝ) ((b.exteriorPower p) r) _
end SmoothObstruction.ExteriorStability

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_MinorTransfer
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

/-- Actual endpoint-projected nonleading maximal minors on unit starting
columns. The inter-group conditioning is paid only by the finite gauge. -/
theorem projected_nonleading_minor
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (S : Finset (Fin d)) {s t : ℕ} (hst : s≤t) {γ g K C : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hU : ‖U t‖≤Real.exp K) (hV : ‖V s‖≤Real.exp K)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card A‖≤C*(max 1 ‖A‖)^S.card)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (r : powersetCard (Fin d) S.card)
    (w : Fin S.card → EuclideanSpace ℝ (Fin d)) (hnorm : ∀ i,‖w i‖≤1)
    (i₀ : Fin S.card) (hw : w i₀∈groupSpace (U s) (V s) (hUV s) (hVU s) Sᶜ) :
    |projectedMinor b S.card r
      (W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)) w|≤
      C*(C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      Real.exp (((t:ℝ)-s)*((∑ j∈S,lam j)-2*g))*
        ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖ := by
  have hQ : ‖exterior S.card W.starProjection‖≤C := by
    apply (hpoly _).trans
    rw [max_eq_left W.starProjection_norm_le,one_pow,mul_one]
  have htr := transition_nonleading_volume U V lam hUV hVU S hst hg hK hC
    hfast hslow hU hV hpoly w i₀ hw
  apply (projectedMinor_norm_le b S.card r _ w).trans
  rw [exterior_mul,mul_apply_eq_comp]
  calc
    _ ≤ ‖exterior S.card W.starProjection‖*
      ‖exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t))
        (exteriorPower.ιMulti ℝ S.card w)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ C*((C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      Real.exp (((t:ℝ)-s)*((∑ j∈S,lam j)-2*g))*‖exteriorPower.ιMulti ℝ S.card w‖) :=
      mul_le_mul hQ htr (norm_nonneg _) hC
    _ ≤ C*((C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      Real.exp (((t:ℝ)-s)*((∑ j∈S,lam j)-2*g))*
        ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖) := by
      gcongr
      exact unit_wedge_bound S.card w hnorm
    _ = _ := by ring
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

/-- Actual fast determinant-line bound for arbitrary starting vectors in
the fast group. This permits projection of a common orthonormal frame onto
the actual group without a polar-decomposition choice of bases. -/
theorem fast_minor_volume_lower
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (s t p : ℕ) (q : powersetCard (Fin d) p)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hdim : Module.finrank ℝ W=p)
    (hclose : ‖(groupSpace (U t) (V t) (hUV t) (hVU t) q.val).starProjection-W.starProjection‖≤1/2)
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (r : powersetCard (Fin d) p)
    (hcoords : ∀ x∈W,∀ j∉r,b.repr x j=0)
    (w : Fin p → EuclideanSpace ℝ (Fin d))
    (hw : ∀ i,w i∈groupSpace (U s) (V s) (hUV s) (hVU s) q.val)
    {K C : ℝ} (hK : 0≤K) (hC : 0≤C)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior p A‖≤C*(max 1 ‖A‖)^p)
    (hU : ‖U s‖≤Real.exp K) (hV : ‖V t‖≤Real.exp K) :
    Real.exp (((t:ℝ)-s)*(∑ j∈q.val,lam j))*‖exteriorPower.ιMulti ℝ p w‖≤
      (C*(Real.exp K)^p)^2*(C*2^p)*
        |projectedMinor b p r
          (W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)) w| := by
  let v := fun i => Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (V s) (w i)
  have hv : ∀ i,v i∈coordinateSpace q.val := by
    intro i
    have h := hw i
    rw [groupSpace,Submodule.map_equiv_eq_comap_symm] at h
    exact h
  have huv : ∀ i,Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U s) (v i)=w i := by
    intro i
    dsimp [v]
    rw [←mul_apply_eq_comp,←map_mul,hUV,map_one]
    rfl
  let F := groupSpace (U t) (V t) (hUV t) (hVU t) q.val
  have hd : Module.finrank ℝ F=Module.finrank ℝ W := by
    rw [finrank_groupSpace,hdim,q.prop]
  let J := CloseProjection.ambientInverse F W hd hclose
  have hdiagM : rate lam ((t:ℝ)-s)=V t*transition U V lam s t*U s := by
    symm
    dsimp [transition]
    calc
      _ = (V t*U t)*rate lam ((t:ℝ)-s)*(V s*U s) := by noncomm_ring
      _ = _ := by rw [hVU,hVU,one_mul,mul_one]
  have hdiag : Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam ((t:ℝ)-s))=
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (V t)*
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)*
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U s) := by
    rw [←map_mul,←map_mul,←hdiagM]
  have hbnd (M : Matrix (Fin d) (Fin d) ℝ) (hM : ‖M‖≤Real.exp K) :
      ‖exterior p (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) M)‖≤C*(Real.exp K)^p := by
    apply (hpoly _).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply pow_le_pow_left₀ (by positivity)
    rw [Matrix.l2_opNorm_toEuclideanCLM]
    exact max_le (Real.one_le_exp_iff.mpr hK) hM
  have hJb : ‖exterior p J‖≤C*2^p := (hpoly J).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (max_le (by norm_num) (CloseProjection.norm_ambientInverse F W hd hclose)) p) hC)
  have hh := projected_gauge_lower b p r
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U s))
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (V t))
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam ((t:ℝ)-s)))
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)) W.starProjection J v
    _ (C*(Real.exp K)^p) (C*2^p) (by positivity) hdiag (hbnd (U s) hU)
    (hbnd (V t) hV) hJb (rate_coordinate_wedge lam _ p q v hv)
    (by
      intro i
      rw [huv]
      exact CloseProjection.ambientInverse_left F W hd hclose _
        (transition_group U V hUV hVU lam s t q.val _ (hw i)))
    (by intro i j hj; exact hcoords _ (by simp) j hj)
  have hn : ‖exterior p (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U s))
      (exteriorPower.ιMulti ℝ p v)‖=‖exteriorPower.ιMulti ℝ p w‖ := by
    rw [exterior_apply,exteriorPower.map_apply_ιMulti]
    change ‖exteriorPower.ιMulti ℝ p (fun i => Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U s) (v i))‖=‖exteriorPower.ιMulti ℝ p w‖
    simp_rw [huv]

  have hm : projectedMinor b p r
      (W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)*
        Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U s)) v=
      projectedMinor b p r
        (W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)) w := by
    rw [projectedMinor_eq_det,projectedMinor_eq_det]
    simp only [mul_apply_eq_comp,huv]
  simpa only [abs_of_pos (Real.exp_pos _),hn,hm] using hh
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ExteriorStability
open Set Module
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma projected_orthonormal_volume_lower (p : ℕ) (F : Submodule ℝ E)
    (w : Fin p → E) (horth : Orthonormal ℝ w) {ε : ℝ}
    (herror : ‖exteriorPower.ιMulti ℝ p (fun i => F.starProjection (w i))-
      exteriorPower.ιMulti ℝ p w‖≤ε) :
    1-ε≤‖exteriorPower.ιMulti ℝ p (fun i => F.starProjection (w i))‖ := by
  have ht := norm_sub_norm_le (exteriorPower.ιMulti ℝ p w)
    (exteriorPower.ιMulti ℝ p (fun i => F.starProjection (w i)))
  rw [norm_sub_rev,norm_wedge_orthonormal p w horth] at ht
  linarith

variable {ι : Type*} [Fintype ι] [LinearOrder ι]
/-- Column replacement is paid against the TRUE exterior norm of the old
propagator, hence it is valid even if the determinant line contracts. -/
lemma projectedMinor_column_error (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (r : powersetCard ι p) (A : E →L[ℝ] E) (v w : Fin p → E)
    {ε : ℝ} (hε : ‖exteriorPower.ιMulti ℝ p v-exteriorPower.ιMulti ℝ p w‖≤ε) :
    |projectedMinor b p r A v-projectedMinor b p r A w|≤‖exterior p A‖*ε := by
  have hh := projectedMinor_basis_transfer b p r A A w v
  simp only [sub_self,ContinuousLinearMap.opNorm_zero,zero_mul,zero_add] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hε (ContinuousLinearMap.opNorm_nonneg _))
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.ExteriorStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma one_le_frameWedgeConstant (p : ℕ) : 1≤frameWedgeConstant (E:=E) p :=
  (exists_common_frame_wedge_control (E:=E) p).choose_spec.1

lemma frameWedgeConstant_bound (p : ℕ) (F G : Submodule ℝ E)
    (w : Fin p → E) (δ : ℝ) (hw : ∀ i,w i∈G) (hnorm : ∀ i,‖w i‖≤1)
    (hδ : 0≤δ) (hclose : ‖F.starProjection-G.starProjection‖≤δ) :
    ‖exteriorPower.ιMulti ℝ p (fun i => F.starProjection (w i))-
      exteriorPower.ιMulti ℝ p w‖≤frameWedgeConstant (E:=E) p*δ :=
  (exists_common_frame_wedge_control (E:=E) p).choose_spec.2 F G w δ hw hnorm hδ hclose
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

/-- A common-bin orthonormal reference frame has a nonzero leading minor
at the TRUE sum-rate scale. The proof projects its columns onto the actual
fast space and estimates their wedge; it requires no continuous choice of
Lyapunov bases or unproved orthonormal basis alignment. -/
theorem common_fast_minor_lower
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (S : Finset (Fin d)) {s t : ℕ} (hst : s≤t) {γ g K C δ : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C) (hδ : 0≤δ)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hUs : ‖U s‖≤Real.exp K) (hUt : ‖U t‖≤Real.exp K)
    (hVs : ‖V s‖≤Real.exp K) (hVt : ‖V t‖≤Real.exp K)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card A‖≤C*(max 1 ‖A‖)^S.card)
    (W G : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hdim : Module.finrank ℝ W=S.card)
    (hend : ‖(groupSpace (U t) (V t) (hUV t) (hVU t) S).starProjection-W.starProjection‖≤1/2)
    (hstart : ‖(groupSpace (U s) (V s) (hUV s) (hVU s) S).starProjection-G.starProjection‖≤δ)
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (r : powersetCard (Fin d) S.card)
    (hcoords : ∀ x∈W,∀ j∉r,b.repr x j=0)
    (w : Fin S.card → EuclideanSpace ℝ (Fin d)) (horth : Orthonormal ℝ w)
    (hw : ∀ i,w i∈G)
    (hsmall : (frameWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ)*
      (1+((C*(Real.exp K)^S.card)^2*(C*2^S.card))*
        (C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))))≤1/2) :
    let A := W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
    Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j))/2≤
      ((C*(Real.exp K)^S.card)^2*(C*2^S.card))*|projectedMinor b S.card r A w| ∧
      projectedMinor b S.card r A w≠0 := by
  let F := groupSpace (U s) (V s) (hUV s) (hVU s) S
  let u := fun i => F.starProjection (w i)
  let R := Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j))
  let L₀ := (C*(Real.exp K)^S.card)^2*(C*2^S.card)
  let N₀ := C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))
  let ε := frameWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ
  let A := W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
  have hR : 0<R := Real.exp_pos _
  have hL₀ : 0≤L₀ := by dsimp [L₀]; positivity
  have hN₀ : 0≤N₀ := by dsimp [N₀]; positivity
  have hε : 0≤ε := mul_nonneg ((by norm_num : (0:ℝ)≤1).trans (one_le_frameWedgeConstant _)) hδ
  have he := frameWedgeConstant_bound S.card F G w δ hw (fun i => (horth.norm_eq_one i).le) hδ hstart
  have hv := projected_orthonormal_volume_lower S.card F w horth he
  have hl := fast_minor_volume_lower U V lam hUV hVU s t S.card ⟨S,rfl⟩ W hdim hend b r hcoords
    u (fun _ => by simp [u,F]) hK hC hpoly hUs hVt
  have htr := transition_exterior_bound U V lam S hst hg hK hC hfast hslow hUt hVs hpoly
  have hQ : ‖exterior S.card W.starProjection‖≤C := by
    apply (hpoly _).trans
    rw [max_eq_left W.starProjection_norm_le,one_pow,mul_one]
  have hA : ‖exterior S.card A‖≤N₀*R := by
    dsimp only [A]
    rw [exterior_mul]
    calc
      _ ≤ ‖exterior S.card W.starProjection‖*
          ‖exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t))‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*R) :=
        mul_le_mul hQ htr (ContinuousLinearMap.opNorm_nonneg _) hC
      _ = N₀*R := by dsimp only [N₀]; ring
  have hm : |projectedMinor b S.card r A u-projectedMinor b S.card r A w|≤N₀*R*ε :=
    (projectedMinor_column_error b S.card r A u w he).trans
      (mul_le_mul_of_nonneg_right hA hε)
  have ht : |projectedMinor b S.card r A u|≤|projectedMinor b S.card r A w|+N₀*R*ε := by
    have hh := abs_sub_le (projectedMinor b S.card r A u) (projectedMinor b S.card r A w) 0
    simp only [sub_zero] at hh
    linarith
  have hcalc : R/2≤L₀*|projectedMinor b S.card r A w| := by
    have h1 := mul_le_mul_of_nonneg_left hv hR.le
    have h2 := mul_le_mul_of_nonneg_left ht hL₀
    have h3 := mul_le_mul_of_nonneg_left hsmall hR.le
    change R*‖exteriorPower.ιMulti ℝ S.card u‖≤L₀*|projectedMinor b S.card r A u| at hl
    change R*(1-ε)≤R*‖exteriorPower.ιMulti ℝ S.card u‖ at h1
    change R*(ε*(1+L₀*N₀))≤R*(1/2) at h3
    nlinarith
  refine ⟨hcalc,?_⟩
  intro hz
  change projectedMinor b S.card r A w=0 at hz
  rw [hz,abs_zero,mul_zero] at hcalc
  linarith
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ExteriorStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma one_le_unitWedgeConstant (p : ℕ) : 1≤unitWedgeConstant (E:=E) p := le_max_right _ _

lemma unit_wedge_difference (p : ℕ) (v w : Fin p → E)
    (hv : ∀ i,‖v i‖≤1) (hw : ∀ i,‖w i‖≤1) :
    ‖exteriorPower.ιMulti ℝ p v-exteriorPower.ιMulti ℝ p w‖≤unitWedgeConstant (E:=E) p*‖v-w‖ := by
  have hbound := (exists_wedge_lipschitz (E:=E) p 1).choose_spec.2
  apply (hbound v w ((pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr hv)
    ((pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr hw)).trans
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

/-- The common product frame may mix both groups. Each column is projected
onto its OWN actual group; one uniform wedge constant still suffices. -/
lemma mixed_projected_wedge_difference (p : ℕ) (F G : Fin p → Submodule ℝ E)
    (w : Fin p → E) (hw : ∀ i,w i∈G i) (hnorm : ∀ i,‖w i‖≤1)
    {δ : ℝ} (hδ : 0≤δ) (hclose : ∀ i,‖(F i).starProjection-(G i).starProjection‖≤δ) :
    ‖exteriorPower.ιMulti ℝ p (fun i => (F i).starProjection (w i))-
      exteriorPower.ιMulti ℝ p w‖≤unitWedgeConstant (E:=E) p*δ := by
  have hp : ∀ i,‖(F i).starProjection (w i)‖≤1 :=
    fun i => ((F i).norm_starProjection_apply_le (w i)).trans (hnorm i)
  have hd : ‖(fun i => (F i).starProjection (w i))-w‖≤δ := by
    apply (pi_norm_le_iff_of_nonneg hδ).mpr
    intro i
    have he : (F i).starProjection (w i)-w i=
        ((F i).starProjection-(G i).starProjection) (w i) := by
      rw [_root_.sub_apply,(G i).starProjection_eq_self_iff.mpr (hw i)]
    change ‖(F i).starProjection (w i)-w i‖≤δ
    rw [he]
    exact (((F i).starProjection-(G i).starProjection).le_opNorm (w i)).trans
      ((mul_le_mul (hclose i) (hnorm i) (norm_nonneg _) hδ).trans_eq (mul_one _))
  exact (unit_wedge_difference p _ w hp hnorm).trans
    (mul_le_mul_of_nonneg_left hd ((by norm_num : (0:ℝ)≤1).trans (one_le_unitWedgeConstant p)))
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

/-- Every nonleading minor in the common starting product frame has the
true relative gap term plus a controlled common-subspace replacement term.
No determinant-line rate is assumed nonnegative. -/
theorem common_nonleading_minor
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (S : Finset (Fin d)) {s t : ℕ} (hst : s≤t) {γ g K C δ : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C) (hδ : 0≤δ)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hUt : ‖U t‖≤Real.exp K) (hVs : ‖V s‖≤Real.exp K)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card A‖≤C*(max 1 ‖A‖)^S.card)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (r : powersetCard (Fin d) S.card)
    (F G : Fin S.card → Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hclose : ∀ i,‖(F i).starProjection-(G i).starProjection‖≤δ)
    (w : Fin S.card → EuclideanSpace ℝ (Fin d)) (hnorm : ∀ i,‖w i‖≤1)
    (hw : ∀ i,w i∈G i) (i₀ : Fin S.card)
    (hFi : F i₀=groupSpace (U s) (V s) (hUV s) (hVU s) Sᶜ) :
    let N₀ := C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))
    let N₁ := C*(C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
    |projectedMinor b S.card r
      (W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)) w|≤
      (N₁*Real.exp (-2*g*((t:ℝ)-s))+
        N₀*unitWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ)*
        Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j)) := by
  let u := fun i => (F i).starProjection (w i)
  let R := Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j))
  let N₀ := C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))
  let N₁ := C*(C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
  let ε := unitWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ
  let A := W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
  have hε : 0≤ε := mul_nonneg ((by norm_num : (0:ℝ)≤1).trans (one_le_unitWedgeConstant _)) hδ
  have hu : ∀ i,‖u i‖≤1 := fun i => ((F i).norm_starProjection_apply_le (w i)).trans (hnorm i)
  have hus : u i₀∈groupSpace (U s) (V s) (hUV s) (hVU s) Sᶜ := by
    dsimp [u]
    rw [←hFi]
    simp
  have he := mixed_projected_wedge_difference S.card F G w hw hnorm hδ hclose
  have hold := projected_nonleading_minor U V lam hUV hVU S hst hg hK hC hfast hslow
    hUt hVs hpoly W b r u hu i₀ hus
  have htr := transition_exterior_bound U V lam S hst hg hK hC hfast hslow hUt hVs hpoly
  have hQ : ‖exterior S.card W.starProjection‖≤C := by
    apply (hpoly _).trans
    rw [max_eq_left W.starProjection_norm_le,one_pow,mul_one]
  have hA : ‖exterior S.card A‖≤N₀*R := by
    dsimp only [A]
    rw [exterior_mul]
    calc
      _ ≤ ‖exterior S.card W.starProjection‖*
          ‖exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t))‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*R) :=
        mul_le_mul hQ htr (ContinuousLinearMap.opNorm_nonneg _) hC
      _ = N₀*R := by dsimp only [N₀]; ring
  have hm : |projectedMinor b S.card r A u-projectedMinor b S.card r A w|≤N₀*R*ε :=
    (projectedMinor_column_error b S.card r A u w he).trans
      (mul_le_mul_of_nonneg_right hA hε)
  have hs : Real.exp (((t:ℝ)-s)*((∑ j∈S,lam j)-2*g))=
      Real.exp (-2*g*((t:ℝ)-s))*R := by
    dsimp [R]
    rw [←Real.exp_add]
    congr 1
    ring
  rw [hs] at hold
  have ht := abs_sub_le (projectedMinor b S.card r A w) (projectedMinor b S.card r A u) 0
  simp only [sub_zero] at ht
  rw [abs_sub_comm] at hm
  change |projectedMinor b S.card r A w|≤
    (N₁*Real.exp (-2*g*((t:ℝ)-s))+N₀*unitWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ)*R
  change |projectedMinor b S.card r A u|≤
    C*(C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      (Real.exp (-2*g*((t:ℝ)-s))*R)*‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖ at hold
  dsimp only [N₁,ε] at *
  nlinarith
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

/-- Genuine common-frame minors: the old leading minor is nonzero and every
mixed minor has a relative bound obtained from the actual gauge products.
All smallness requirements refer to subspace distances, not to conclusions
about minors. Rates may be negative and no uniform determinant floor is used. -/
theorem common_minor_separation
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (S : Finset (Fin d)) {s t : ℕ} (hst : s≤t) {γ g K C δ : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C) (hδ : 0≤δ)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hUs : ‖U s‖≤Real.exp K) (hUt : ‖U t‖≤Real.exp K)
    (hVs : ‖V s‖≤Real.exp K) (hVt : ‖V t‖≤Real.exp K)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card A‖≤C*(max 1 ‖A‖)^S.card)
    (W G : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hdim : Module.finrank ℝ W=S.card)
    (hend : ‖(groupSpace (U t) (V t) (hUV t) (hVU t) S).starProjection-W.starProjection‖≤1/2)
    (hstart : ‖(groupSpace (U s) (V s) (hUV s) (hVU s) S).starProjection-G.starProjection‖≤δ)
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (r : powersetCard (Fin d) S.card)
    (hcoords : ∀ x∈W,∀ j∉r,b.repr x j=0)
    (v : Fin S.card → EuclideanSpace ℝ (Fin d)) (horth : Orthonormal ℝ v)
    (hv : ∀ i,v i∈G)
    (F H : Fin S.card → Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hclose : ∀ i,‖(F i).starProjection-(H i).starProjection‖≤δ)
    (w : Fin S.card → EuclideanSpace ℝ (Fin d)) (hnorm : ∀ i,‖w i‖≤1)
    (hw : ∀ i,w i∈H i) (i₀ : Fin S.card)
    (hFi : F i₀=groupSpace (U s) (V s) (hUV s) (hVU s) Sᶜ)
    (hsmall : (frameWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ)*
      (1+((C*(Real.exp K)^S.card)^2*(C*2^S.card))*
        (C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))))≤1/2) :
    let A := W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
    let L₀ := (C*(Real.exp K)^S.card)^2*(C*2^S.card)
    let N₀ := C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))
    let N₁ := C*(C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
    projectedMinor b S.card r A v≠0 ∧
      |projectedMinor b S.card r A w|≤
        (2*L₀*(N₁*Real.exp (-2*g*((t:ℝ)-s))+
          N₀*unitWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ))*
            |projectedMinor b S.card r A v| := by
  have hl := common_fast_minor_lower U V lam hUV hVU S hst hg hK hC hδ hfast hslow
    hUs hUt hVs hVt hpoly W G hdim hend hstart b r hcoords v horth hv hsmall
  have hu := common_nonleading_minor U V lam hUV hVU S hst hg hK hC hδ hfast hslow
    hUt hVs hpoly W b r F H hclose w hnorm hw i₀ hFi
  refine ⟨hl.2,?_⟩
  dsimp only at hl hu ⊢
  let L₀ := (C*(Real.exp K)^S.card)^2*(C*2^S.card)
  let N₀ := C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))
  let N₁ := C*(C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
  let D := N₁*Real.exp (-2*g*((t:ℝ)-s))+
    N₀*unitWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ
  have hD : 0≤D := by
    have hp := (one_le_unitWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card)
    dsimp [D,N₀,N₁]
    positivity
  have hh := mul_le_mul_of_nonneg_left hl.1
    (show 0≤2*D from mul_nonneg (by norm_num) hD)
  dsimp [D,N₀,N₁] at hh
  nlinarith
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ExteriorStability
open Filter Topology Set Asymptotics
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Relative errors preserve nonzero leading minors and all other ratios.
There is no lower absolute bound on `a`. -/
lemma relative_minor_ratios {a a' c c' ε δ : ℝ} (ha : a ≠ 0)
    (hε : 0 ≤ ε) (hε1 : ε < 1) (hδ : 0 ≤ δ)
    (haa : |a'-a| ≤ ε*|a|) (hc : |c| ≤ δ*|a|)
    (hcc : |c'-c| ≤ ε*|a|) :
    a' ≠ 0 ∧ |c'|/|a'| ≤ (δ+ε)/(1-ε) := by
  have hapos := abs_pos.mpr ha
  have hal : (1-ε)*|a| ≤ |a'| := by
    have ht := abs_sub_abs_le_abs_sub a a'
    rw [abs_sub_comm a a'] at ht
    nlinarith
  have hap : 0 < |a'| := lt_of_lt_of_le (mul_pos (by linarith) hapos) hal
  refine ⟨abs_pos.mp hap, (div_le_iff₀ hap).mpr ?_⟩
  have hcup : |c'| ≤ (δ+ε)*|a| := by
    have ht := abs_sub_le c' c 0
    simp only [sub_zero] at ht
    linarith
  apply hcup.trans
  have hd : 0 ≤ (δ+ε)/(1-ε) := div_nonneg (add_nonneg hδ hε) (by linarith)
  have hh := mul_le_mul_of_nonneg_left hal hd
  have he : (δ+ε)/(1-ε)*((1-ε)*|a|)=(δ+ε)*|a| := by
    rw [←mul_assoc,div_mul_cancel₀ _ (by linarith : 1-ε ≠ 0)]
  rwa [he] at hh
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.ExteriorStability
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Fixed endpoint projections preserve the all-subinterval exterior error.
The multiplier is a dimension constant even for a nonpositive rate sum. -/
lemma projected_postcomposition_transfer (b : OrthonormalBasis ι ℝ E)
    (p : ℕ) (r : powersetCard ι p) (Q A B : E →L[ℝ] E)
    (v : Fin p → E) (hv : ∀ i,‖v i‖≤1) {C ε : ℝ} (hC : 0≤C)
    (hQ : ‖exterior p Q‖≤C) (he : ‖exterior p B-exterior p A‖≤ε) :
    |projectedMinor b p r (Q*B) v-projectedMinor b p r (Q*A) v|≤
      C*ε*‖continuousWedge (E:=E) p‖ := by
  have hd : exterior p (Q*B)-exterior p (Q*A)=
      exterior p Q*(exterior p B-exterior p A) := by
    rw [exterior_mul,exterior_mul,mul_sub]
  have hn : ‖exterior p (Q*B)-exterior p (Q*A)‖≤C*ε := by
    rw [hd]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hQ he (ContinuousLinearMap.opNorm_nonneg _) hC)
  exact (projectedMinor_transfer b p r (Q*A) (Q*B) v).trans
    (mul_le_mul hn (unit_wedge_bound p v hv) (norm_nonneg _)
      (mul_nonneg hC ((ContinuousLinearMap.opNorm_nonneg _).trans he)))
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

/-- Finite, quantitative relative-minor control for a perturbed derivative in
common starting/endpoint frames. Old minor bounds are DERIVED from actual
finite gauges and close subspaces. The exterior perturbation is measured at
the true sum-rate scale, not at an absolute determinant floor. -/
theorem common_minor_perturbation
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (S : Finset (Fin d)) {s t : ℕ} (hst : s≤t) {γ g K C δ : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C) (hδ : 0≤δ)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hUs : ‖U s‖≤Real.exp K) (hUt : ‖U t‖≤Real.exp K)
    (hVs : ‖V s‖≤Real.exp K) (hVt : ‖V t‖≤Real.exp K)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card A‖≤C*(max 1 ‖A‖)^S.card)
    (W G : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hdim : Module.finrank ℝ W=S.card)
    (hend : ‖(groupSpace (U t) (V t) (hUV t) (hVU t) S).starProjection-W.starProjection‖≤1/2)
    (hstart : ‖(groupSpace (U s) (V s) (hUV s) (hVU s) S).starProjection-G.starProjection‖≤δ)
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (r : powersetCard (Fin d) S.card)
    (hcoords : ∀ x∈W,∀ j∉r,b.repr x j=0)
    (v : Fin S.card → EuclideanSpace ℝ (Fin d)) (horth : Orthonormal ℝ v)
    (hv : ∀ i,v i∈G)
    (F H : Fin S.card → Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hclose : ∀ i,‖(F i).starProjection-(H i).starProjection‖≤δ)
    (w : Fin S.card → EuclideanSpace ℝ (Fin d)) (hnorm : ∀ i,‖w i‖≤1)
    (hw : ∀ i,w i∈H i) (i₀ : Fin S.card)
    (hFi : F i₀=groupSpace (U s) (V s) (hUV s) (hVU s) Sᶜ)
    (hsmall : (frameWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ)*
      (1+((C*(Real.exp K)^S.card)^2*(C*2^S.card))*
        (C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))))≤1/2)
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    {ζ : ℝ} (hζ : 0≤ζ)
    (hpert : 2*((C*(Real.exp K)^S.card)^2*(C*2^S.card))*C*ζ*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖<1)
    (hdiff : ‖exterior S.card B-
      exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t))‖≤
        ζ*Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j))) :
    let A' := W.starProjection*B
    let L₀ := (C*(Real.exp K)^S.card)^2*(C*2^S.card)
    let N₀ := C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))
    let N₁ := C*(C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
    let θ := 2*L₀*(N₁*Real.exp (-2*g*((t:ℝ)-s))+
      N₀*unitWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ)
    let ε := 2*L₀*C*ζ*‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
    projectedMinor b S.card r A' v≠0 ∧
      |projectedMinor b S.card r A' w|/|projectedMinor b S.card r A' v|≤(θ+ε)/(1-ε) := by
  have hl := common_fast_minor_lower U V lam hUV hVU S hst hg hK hC hδ hfast hslow
    hUs hUt hVs hVt hpoly W G hdim hend hstart b r hcoords v horth hv hsmall
  have hs := common_minor_separation U V lam hUV hVU S hst hg hK hC hδ hfast hslow
    hUs hUt hVs hVt hpoly W G hdim hend hstart b r hcoords v horth hv
    F H hclose w hnorm hw i₀ hFi hsmall
  let A₀ := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
  let A := W.starProjection*A₀
  let R := Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j))
  let L₀ := (C*(Real.exp K)^S.card)^2*(C*2^S.card)
  let V₀ := ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
  let ε := 2*L₀*C*ζ*V₀
  have hL₀ : 0≤L₀ := by dsimp [L₀]; positivity
  have hε : 0≤ε := by dsimp [ε,V₀]; positivity
  have hQ : ‖exterior S.card W.starProjection‖≤C := by
    apply (hpoly _).trans
    rw [max_eq_left W.starProjection_norm_le,one_pow,mul_one]
  have hl' : R≤2*L₀*|projectedMinor b S.card r A v| := by
    have hh : R/2≤L₀*|projectedMinor b S.card r A v| := hl.1
    linarith
  have he (u : Fin S.card → EuclideanSpace ℝ (Fin d)) (hu : ∀ i,‖u i‖≤1) :
      |projectedMinor b S.card r (W.starProjection*B) u-projectedMinor b S.card r A u|≤
        ε*|projectedMinor b S.card r A v| := by
    have hh := projected_postcomposition_transfer b S.card r W.starProjection A₀ B u hu hC hQ hdiff
    calc
      _ ≤ C*(ζ*R)*V₀ := hh
      _ = (C*ζ*V₀)*R := by ring
      _ ≤ (C*ζ*V₀)*(2*L₀*|projectedMinor b S.card r A v|) :=
        mul_le_mul_of_nonneg_left hl' (by dsimp [V₀]; positivity)
      _ = ε*|projectedMinor b S.card r A v| := by dsimp [ε]; ring
  apply relative_minor_ratios hs.1 hε hpert _
    (he v (fun i => (horth.norm_eq_one i).le)) hs.2 (he w hnorm)
  have hp := one_le_unitWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card
  positivity
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ExteriorStability
open Set Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

lemma endpointMatrix_det (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (r : powersetCard ι p) (A : E →L[ℝ] E) (v : Fin p → E) :
    (endpointMatrix b p r A v).det=projectedMinor b p r A v := by
  rw [projectedMinor_eq_det]
  exact (Matrix.det_transpose _).symm

omit [FiniteDimensional ℝ E] in
lemma endpointMatrix_update (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (r : powersetCard ι p) (A : E →L[ℝ] E) (v : Fin p → E)
    (i : Fin p) (z : E) :
    endpointMatrix b p r A (Function.update v i z)=
      (endpointMatrix b p r A v).updateCol i
        (fun j => b.repr (A z) (powersetCard.ofFinEmbEquiv.symm r j)) := by
  ext j k
  by_cases hk : k=i
  · subst k
    simp [endpointMatrix,Matrix.updateCol]
  · simp [endpointMatrix,Matrix.updateCol,hk]

/-- The Cramer minor is the genuine maximal minor with one common starting
fast column replaced by a common slow column. There is no symbolic-minor
proxy in the comparison. -/
lemma endpointMatrix_cramer (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (r : powersetCard ι p) (A : E →L[ℝ] E) (v : Fin p → E)
    {n : ℕ} (w : Fin n → E) (i : Fin p) (j : Fin n) :
    ((endpointMatrix b p r A v).updateCol i (fun k => endpointMatrix b p r A w k j)).det=
      projectedMinor b p r A (Function.update v i (w j)) := by
  calc
    _ = (endpointMatrix b p r A (Function.update v i (w j))).det :=
      congrArg Matrix.det (endpointMatrix_update b p r A v i (w j)).symm
    _ = _ := endpointMatrix_det b p r A _
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.MinorGraph
open Matrix Set Metric
open scoped Matrix.Norms.Elementwise
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
lemma cramer_ratio (A : Matrix m m ℝ) (B : Matrix m n ℝ)
    (hA : A.det≠0) (i : m) (j : n) :
    (A⁻¹*B) i j=(A.updateCol i (fun r => B r j)).det/A.det := by
  have h := congrFun (Matrix.det_smul_inv_mulVec_eq_cramer A (fun r => B r j)
    (isUnit_iff_ne_zero.mpr hA)) i
  change A.det*(A⁻¹*B) i j=(A.updateCol i (fun r => B r j)).det at h
  exact (eq_div_iff hA).mpr (by simpa only [mul_comm] using h)

end SmoothObstruction.MinorGraph

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

/-- The genuine endpoint derivative graph in the common product basis.
The actual exterior perturbation, relative even on contracting determinant
lines, is transferred to Cramer ratios without postulating graph smallness.
Either column group may be empty. -/
theorem common_perturbed_endpoint_graph_bound
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (S : Finset (Fin d)) {s t : ℕ} (hst : s≤t) {γ g K C δ : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C) (hδ : 0≤δ)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hUs : ‖U s‖≤Real.exp K) (hUt : ‖U t‖≤Real.exp K)
    (hVs : ‖V s‖≤Real.exp K) (hVt : ‖V t‖≤Real.exp K)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card A‖≤C*(max 1 ‖A‖)^S.card)
    (W G : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hdim : Module.finrank ℝ W=S.card)
    (hend : ‖(groupSpace (U t) (V t) (hUV t) (hVU t) S).starProjection-W.starProjection‖≤1/2)
    (hstart : ‖(groupSpace (U s) (V s) (hUV s) (hVU s) S).starProjection-G.starProjection‖≤δ)
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (r : powersetCard (Fin d) S.card)
    (hcoords : ∀ x∈W,∀ j∉r,b.repr x j=0)
    (v : Fin S.card → EuclideanSpace ℝ (Fin d)) (horth : Orthonormal ℝ v)
    (hv : ∀ i,v i∈G)
    (Gslow : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hstartSlow : ‖(groupSpace (U s) (V s) (hUV s) (hVU s) Sᶜ).starProjection-Gslow.starProjection‖≤δ)
    {n : ℕ} (z : Fin n → EuclideanSpace ℝ (Fin d))
    (hz : ∀ j,z j∈Gslow) (hznorm : ∀ j,‖z j‖≤1)
    (hsmall : (frameWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ)*
      (1+((C*(Real.exp K)^S.card)^2*(C*2^S.card))*
        (C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))))≤1/2)
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    {ζ : ℝ} (hζ : 0≤ζ)
    (hpert : 2*((C*(Real.exp K)^S.card)^2*(C*2^S.card))*C*ζ*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖<1)
    (hdiff : ‖exterior S.card B-
      exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t))‖≤
        ζ*Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j))) :
    let A := W.starProjection*B
    let Afast := endpointMatrix b S.card r A v
    let Aslow := endpointMatrix b S.card r A z
    let L₀ := (C*(Real.exp K)^S.card)^2*(C*2^S.card)
    let N₀ := C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))
    let N₁ := C*(C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
    let θ := 2*L₀*(N₁*Real.exp (-2*g*((t:ℝ)-s))+
      N₀*unitWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ)
    let ε := 2*L₀*C*ζ*‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
    Afast.det≠0 ∧ ∀ i j, |(Afast⁻¹*Aslow) i j|≤(θ+ε)/(1-ε) := by
  have hl := common_fast_minor_lower U V lam hUV hVU S hst hg hK hC hδ hfast hslow
    hUs hUt hVs hVt hpoly W G hdim hend hstart b r hcoords v horth hv hsmall
  let A₀ := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
  let A := W.starProjection*B
  let R := Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j))
  let L₀ := (C*(Real.exp K)^S.card)^2*(C*2^S.card)
  let V₀ := ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
  let ε := 2*L₀*C*ζ*V₀
  have hL₀ : 0≤L₀ := by dsimp [L₀]; positivity
  have hε : 0≤ε := by dsimp [ε,V₀]; positivity
  have hQ : ‖exterior S.card W.starProjection‖≤C := by
    apply (hpoly _).trans
    rw [max_eq_left W.starProjection_norm_le,one_pow,mul_one]
  have hl' : R≤2*L₀*|projectedMinor b S.card r (W.starProjection*A₀) v| := by
    have hh : R/2≤L₀*|projectedMinor b S.card r (W.starProjection*A₀) v| := hl.1
    linarith
  have he : |projectedMinor b S.card r A v-
      projectedMinor b S.card r (W.starProjection*A₀) v|≤
        ε*|projectedMinor b S.card r (W.starProjection*A₀) v| := by
    have hh := projected_postcomposition_transfer b S.card r W.starProjection A₀ B v
      (fun i => (horth.norm_eq_one i).le) hC hQ hdiff
    calc
      _ ≤ C*(ζ*R)*V₀ := hh
      _ = (C*ζ*V₀)*R := by ring
      _ ≤ (C*ζ*V₀)*(2*L₀*|projectedMinor b S.card r (W.starProjection*A₀) v|) :=
        mul_le_mul_of_nonneg_left hl' (by dsimp [V₀]; positivity)
      _ = ε*|projectedMinor b S.card r (W.starProjection*A₀) v| := by dsimp [ε]; ring
  have hnon := (relative_minor_ratios (c:=0) (c':=0) (δ:=0)
    hl.2 hε hpert le_rfl he (by simp) (by simp; positivity)).1
  have hdet : (endpointMatrix b S.card r A v).det≠0 := by
    rw [endpointMatrix_det]
    exact hnon
  refine ⟨hdet,?_⟩
  intro i j
  let F := fun l : Fin S.card => if l=i then groupSpace (U s) (V s) (hUV s) (hVU s) Sᶜ
    else groupSpace (U s) (V s) (hUV s) (hVU s) S
  let H := fun l : Fin S.card => if l=i then Gslow else G
  let w := Function.update v i (z j)
  have hc : ∀ l,‖(F l).starProjection-(H l).starProjection‖≤δ := by
    intro l
    by_cases hl : l=i
    · simpa only [F,H,ite_eq_left hl] using hstartSlow
    · simpa only [F,H,ite_eq_right hl] using hstart
  have hwm : ∀ l,w l∈H l := by
    intro l
    by_cases hl : l=i
    · subst l
      simpa [w,H] using hz j
    · simpa [w,H,hl] using hv l
  have hwn : ∀ l,‖w l‖≤1 := by
    intro l
    by_cases hl : l=i
    · subst l
      simpa [w] using hznorm j
    · simpa [w,hl] using (horth.norm_eq_one l).le
  have hm := common_minor_perturbation U V lam hUV hVU S hst hg hK hC hδ hfast hslow
    hUs hUt hVs hVt hpoly W G hdim hend hstart b r hcoords v horth hv
    F H hc w hwn hwm i (by simp [F]) hsmall B hζ hpert hdiff
  have hr := congrArg abs (MinorGraph.cramer_ratio (endpointMatrix b S.card r A v)
    (endpointMatrix b S.card r A z) hdet i j)
  simp only [abs_div,endpointMatrix_cramer,endpointMatrix_det] at hr
  exact hr.trans_le hm.2
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

/-- Signed old-to-new leading-minor transfer. In combination with the proved
common perturbed graph bound, this supplies the actual factors used in
`MinorGraph.joint_relative_transfer`. It does not posit their relative error. -/
theorem common_leading_relative_transfer
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (S : Finset (Fin d)) {s t : ℕ} (hst : s≤t) {γ g K C δ : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C) (hδ : 0≤δ)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hUs : ‖U s‖≤Real.exp K) (hUt : ‖U t‖≤Real.exp K)
    (hVs : ‖V s‖≤Real.exp K) (hVt : ‖V t‖≤Real.exp K)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card A‖≤C*(max 1 ‖A‖)^S.card)
    (W G : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hdim : Module.finrank ℝ W=S.card)
    (hend : ‖(groupSpace (U t) (V t) (hUV t) (hVU t) S).starProjection-W.starProjection‖≤1/2)
    (hstart : ‖(groupSpace (U s) (V s) (hUV s) (hVU s) S).starProjection-G.starProjection‖≤δ)
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (r : powersetCard (Fin d) S.card)
    (hcoords : ∀ x∈W,∀ j∉r,b.repr x j=0)
    (v : Fin S.card → EuclideanSpace ℝ (Fin d)) (horth : Orthonormal ℝ v)
    (hv : ∀ i,v i∈G)
    (hsmall : (frameWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ)*
      (1+((C*(Real.exp K)^S.card)^2*(C*2^S.card))*
        (C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))))≤1/2)
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    {ζ : ℝ} (hζ : 0≤ζ)
    (hpert : 2*((C*(Real.exp K)^S.card)^2*(C*2^S.card))*C*ζ*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖<1)
    (hdiff : ‖exterior S.card B-
      exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t))‖≤
        ζ*Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j))) :
    let A := W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
    let A' := W.starProjection*B
    let ε := 2*((C*(Real.exp K)^S.card)^2*(C*2^S.card))*C*ζ*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
    projectedMinor b S.card r A v≠0 ∧ projectedMinor b S.card r A' v≠0 ∧
      |projectedMinor b S.card r A' v/projectedMinor b S.card r A v-1|≤ε := by
  have hl := common_fast_minor_lower U V lam hUV hVU S hst hg hK hC hδ hfast hslow
    hUs hUt hVs hVt hpoly W G hdim hend hstart b r hcoords v horth hv hsmall
  let A₀ := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
  let A := W.starProjection*B
  let R := Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j))
  let L₀ := (C*(Real.exp K)^S.card)^2*(C*2^S.card)
  let V₀ := ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
  let ε := 2*L₀*C*ζ*V₀
  have hL₀ : 0≤L₀ := by dsimp [L₀]; positivity
  have hε : 0≤ε := by dsimp [ε,V₀]; positivity
  have hQ : ‖exterior S.card W.starProjection‖≤C := by
    apply (hpoly _).trans
    rw [max_eq_left W.starProjection_norm_le,one_pow,mul_one]
  have hl' : R≤2*L₀*|projectedMinor b S.card r (W.starProjection*A₀) v| := by
    have hh : R/2≤L₀*|projectedMinor b S.card r (W.starProjection*A₀) v| := hl.1
    linarith
  have he : |projectedMinor b S.card r A v-
      projectedMinor b S.card r (W.starProjection*A₀) v|≤
        ε*|projectedMinor b S.card r (W.starProjection*A₀) v| := by
    have hh := projected_postcomposition_transfer b S.card r W.starProjection A₀ B v
      (fun i => (horth.norm_eq_one i).le) hC hQ hdiff
    calc
      _ ≤ C*(ζ*R)*V₀ := hh
      _ = (C*ζ*V₀)*R := by ring
      _ ≤ (C*ζ*V₀)*(2*L₀*|projectedMinor b S.card r (W.starProjection*A₀) v|) :=
        mul_le_mul_of_nonneg_left hl' (by dsimp [V₀]; positivity)
      _ = ε*|projectedMinor b S.card r (W.starProjection*A₀) v| := by dsimp [ε]; ring
  have hnon := (relative_minor_ratios (c:=0) (c':=0) (δ:=0)
    hl.2 hε hpert le_rfl he (by simp) (by simp; positivity)).1
  refine ⟨hl.2,hnon,?_⟩
  have heq : projectedMinor b S.card r A v/projectedMinor b S.card r (W.starProjection*A₀) v-1=
      (projectedMinor b S.card r A v-projectedMinor b S.card r (W.starProjection*A₀) v)/
        projectedMinor b S.card r (W.starProjection*A₀) v := by
    rw [sub_div,div_self hl.2]
  rw [heq,abs_div]
  exact (div_le_iff₀ (abs_pos.mpr hl.2)).mpr he
end SmoothObstruction.EuclideanSplitting

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

lemma coordinates_projection (W : Submodule ℝ E)
    (b : OrthonormalBasis (Fin d) ℝ E) (r : powersetCard (Fin d) p)
    (hr : ∀ j∈r,b j∈W) (x : E) :
    coordinates b r (W.starProjection x)=coordinates b r x := by
  ext i
  simp only [coordinates_apply,b.repr_apply_apply]
  have hi : powersetCard.ofFinEmbEquiv.symm r i∈r :=
    (powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem r _).mp ⟨i,rfl⟩
  have hh := W.inner_orthogonalProjectionOnto_eq_of_mem_left
    (⟨b (powersetCard.ofFinEmbEquiv.symm r i),hr _ hi⟩ : W) x
  exact hh

end SmoothObstruction.EndpointFrame

namespace SmoothObstruction.ExteriorStability
open Set Matrix EndpointFrame
variable {d p q : ℕ}
local notation "E₀" => EuclideanSpace ℝ (Fin d)

lemma endpointMatrix_projection (W : Submodule ℝ E₀)
    (b : OrthonormalBasis (Fin d) ℝ E₀) (r : powersetCard (Fin d) p)
    (hr : ∀ j∈r,b j∈W) (A : E₀ →L[ℝ] E₀) (v : Fin q → E₀) :
    endpointMatrix b p r (W.starProjection*A) v=endpointMatrix b p r A v := by
  ext i j
  exact congrArg (fun z : EuclideanSpace ℝ (Fin p) => z i)
    (coordinates_projection W b r hr (A (v j)))
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d p q : ℕ}
local notation "E₀" => EuclideanSpace ℝ (Fin d)
/-- Actual endpoint-coordinate matrices with a common input frame. The old
leading volume, its perturbed relative value, and every true graph entry are
controlled together. No lower volume floor, rate sign, positive rank, or
orthogonality between the two input groups is required. -/
theorem endpoint_bounds_oai
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (S : Finset (Fin d)) (hSp : S.card=p) (n : ℕ) {γ g K C δ : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C) (hδ : 0≤δ)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hUs : ‖U 0‖≤Real.exp K) (hUt : ‖U n‖≤Real.exp K)
    (hVs : ‖V 0‖≤Real.exp K) (hVt : ‖V n‖≤Real.exp K)
    (hpoly : ∀ A : E₀ →L[ℝ] E₀,‖exterior p A‖≤C*(max 1 ‖A‖)^p)
    (W G Gslow : Submodule ℝ E₀) (hdim : Module.finrank ℝ W=p)
    (hend : ‖(groupSpace (U n) (V n) (hUV n) (hVU n) S).starProjection-W.starProjection‖≤1/2)
    (hstart : ‖(groupSpace (U 0) (V 0) (hUV 0) (hVU 0) S).starProjection-G.starProjection‖≤δ)
    (hstartSlow : ‖(groupSpace (U 0) (V 0) (hUV 0) (hVU 0) Sᶜ).starProjection-Gslow.starProjection‖≤δ)
    (b : OrthonormalBasis (Fin d) ℝ E₀) (r : powersetCard (Fin d) p)
    (hr : ∀ j∈r,b j∈W) (hcoords : ∀ x∈W,∀ j∉r,b.repr x j=0)
    (v : Fin p → E₀) (horth : Orthonormal ℝ v) (hv : ∀ i,v i∈G)
    (z : Fin q → E₀) (hz : ∀ j,z j∈Gslow) (hznorm : ∀ j,‖z j‖≤1)
    (hsmall : (frameWedgeConstant (E := E₀) p*δ)*
      (1+((C*(Real.exp K)^p)^2*(C*2^p))*
        (C*(C^2*(Real.exp K)^(2*p)*(Fintype.card (powersetCard (Fin d) p):ℝ))))≤1/2)
    (B : E₀ →L[ℝ] E₀) {ζ : ℝ} (hζ : 0≤ζ)
    (hpert : 2*((C*(Real.exp K)^p)^2*(C*2^p))*C*ζ*‖continuousWedge (E := E₀) p‖<1)
    (hdiff : ‖exterior p B-
      exterior p (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (transition U V lam 0 n))‖≤
        ζ*Real.exp ((n:ℝ)*(∑ j∈S,lam j))) :
    let A₀ := endpointMatrix b p r
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (transition U V lam 0 n)) v
    let A := endpointMatrix b p r B v
    let H := endpointMatrix b p r B z
    let L₀ := (C*(Real.exp K)^p)^2*(C*2^p)
    let N₀ := C*(C^2*(Real.exp K)^(2*p)*(Fintype.card (powersetCard (Fin d) p):ℝ))
    let N₁ := C*(C*(Real.exp K)^p)^2*(Fintype.card (powersetCard (Fin d) p):ℝ)*‖continuousWedge (E := E₀) p‖
    let θ := 2*L₀*(N₁*Real.exp (-2*g*n)+N₀*unitWedgeConstant (E := E₀) p*δ)
    let ε := 2*L₀*C*ζ*‖continuousWedge (E := E₀) p‖
    A₀.det≠0 ∧ A.det≠0 ∧ |A.det/A₀.det-1|≤ε ∧ ∀ i j,|(A⁻¹*H) i j|≤(θ+ε)/(1-ε) := by
  subst p
  have hl := common_leading_relative_transfer U V lam hUV hVU S (Nat.zero_le n)
    hg hK hC hδ hfast hslow hUs hUt hVs hVt hpoly W G hdim hend hstart b r hcoords
    v horth hv hsmall B hζ hpert (by simpa only [Nat.cast_zero,sub_zero] using hdiff)
  have hh := common_perturbed_endpoint_graph_bound U V lam hUV hVU S (Nat.zero_le n)
    hg hK hC hδ hfast hslow hUs hUt hVs hVt hpoly W G hdim hend hstart b r hcoords
    v horth hv Gslow hstartSlow z hz hznorm hsmall B hζ hpert
    (by simpa only [Nat.cast_zero,sub_zero] using hdiff)
  dsimp only at hl hh ⊢
  simp only [←endpointMatrix_det,endpointMatrix_projection W b r hr] at hl
  simp only [endpointMatrix_projection W b r hr,Nat.cast_zero,sub_zero] at hh
  exact ⟨hl.1,hl.2.1,hl.2.2,hh.2⟩
end SmoothObstruction.EuclideanSplitting

end

end OAI
end

theorem solution : type_of% @OAI.SmoothObstruction.EuclideanSplitting.endpoint_bounds_oai := @OAI.SmoothObstruction.EuclideanSplitting.endpoint_bounds_oai
