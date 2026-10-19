-- Prove2me | solution 1 for OAI.BackwardIntertwiners.direct_algebra_corollary
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:19:48.026604+00:00
-- url     : https://prove2.me/submissions/d340c3fe-f1a5-4533-b3be-db54627051b6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/AlgebraCorollary.lean:L78-L87
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.BackwardIntertwiners.direct_algebra_corollary.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_BackwardIntertwiners_direct_algebra_corollary) verbatim and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ExplicitWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_HaarBase
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberMaps
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_BackwardWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_GlobalOperators
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ErgodicTransitivity
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_OrdinaryStructure
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_DiagonalSymbols
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_PolarDiagonals
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_HilbertClassification
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_AlgebraCorollary
import Theorems.Thm_OAI_BackwardIntertwiners_forwardOperator_power_norm
import Theorems.Thm_OAI_BackwardIntertwiners_forward_backward_commute
import Theorems.Thm_OAI_BackwardIntertwiners_forward_backward_scalar_transitive

-- ---- from OAI.Analysis.BackwardIntertwiners.GlobalOperators ----
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

section Fields
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma fieldOperator_ae (A : X → Fiber →L[ℂ] Fiber) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ f : X → Fiber, AEStronglyMeasurable f μ → AEStronglyMeasurable (fun x => A x (f x)) μ)
    (f : Lp Fiber 2 μ) : fieldOperator A C hC hA hm f =ᵐ[μ] fun x => A x (f x) :=
  fieldVector_ae A C hA hm f

lemma fieldOperator_norm (A : X → Fiber →L[ℂ] Fiber) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ f : X → Fiber, AEStronglyMeasurable f μ → AEStronglyMeasurable (fun x => A x (f x)) μ) :
    ‖fieldOperator A C hC hA hm‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (fieldVector_norm A C hC hA hm)

lemma scalarMultiplier_ae (g : Lp ℂ ∞ μ) (f : Lp Fiber 2 μ) :
    scalarMultiplier g f =ᵐ[μ] fun x => g x • f x := Lp.coeFn_lpSMul g f
end Fields

lemma forwardFiber_single (x : Base) (j : ℤ) (c : ℂ) :
    forwardFiber x (lp.single 2 j c) = lp.single 2 (j+1) ((explicitBeta x j:ℂ)*c) := by
  ext k
  rw [forwardFiber_apply]
  by_cases hk : k = j+1
  · subst k
    simp
  · have hj : k-1 ≠ j := by omega
    simp only [lp.single_apply_ne _ _ _ hk, lp.single_apply_ne _ _ _ hj, mul_zero]
lemma forwardOperator_ae (f : GlobalHilbert) :
    forwardOperator f =ᵐ[baseMeasure] fun x => forwardFiber x (f x) :=
  fieldOperator_ae _ _ _ _ _ f
lemma forwardOperator_norm_le : ‖forwardOperator‖ ≤ Real.exp (-10) :=
  fieldOperator_norm _ _ _ _ _

lemma forward_scalar_commute (g : Lp ℂ ∞ baseMeasure) :
    forwardOperator * scalarMultiplier g = scalarMultiplier g * forwardOperator := by
  ext1 f
  apply Lp.ext
  filter_upwards [forwardOperator_ae (scalarMultiplier g f), scalarMultiplier_ae g f,
    scalarMultiplier_ae g (forwardOperator f), forwardOperator_ae f] with x h₁ h₂ h₃ h₄
  change forwardOperator (scalarMultiplier g f) x = scalarMultiplier g (forwardOperator f) x
  simp only [h₁,h₂,h₃,h₄,map_smul]

lemma constantBasis_norm (j : ℤ) : ‖constantBasis j‖ = 1 := by
  rw [constantBasis, Lp.norm_const 2 baseMeasure _ (by norm_num), lp.norm_single (by norm_num : (0:ENNReal)<2)]
  simp
lemma constantBasis_ae (j : ℤ) : constantBasis j =ᵐ[baseMeasure] fun _ => lp.single 2 j (1:ℂ) :=
  Lp.coeFn_const _ _ _
lemma forwardOperator_constantBasis_zero :
    forwardOperator (constantBasis 0) = (Real.exp (-10):ℂ) • constantBasis 1 := by
  apply Lp.ext
  filter_upwards [forwardOperator_ae (constantBasis 0), constantBasis_ae 0, constantBasis_ae 1,
    Lp.coeFn_smul (Real.exp (-10):ℂ) (constantBasis 1)] with x h₁ h₂ h₃ h₄
  rw [h₁,h₂,h₄,Pi.smul_apply,h₃,forwardFiber_single,explicitBeta_zero,mul_one]
  rw [← lp.single_smul]
  simp
lemma forwardOperator_norm : ‖forwardOperator‖ = Real.exp (-10) := by
  apply le_antisymm forwardOperator_norm_le
  have h := forwardOperator.le_opNorm (constantBasis 0)
  rw [forwardOperator_constantBasis_zero, norm_smul, constantBasis_norm, constantBasis_norm,
    mul_one, mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at h
  exact h
lemma forwardOperator_ne_zero : forwardOperator ≠ 0 := by
  intro h
  have hh := forwardOperator_norm
  rw [h, norm_zero] at hh
  exact (Real.exp_ne_zero (-10)) hh.symm

end
end BackwardIntertwiners

end OAI

-- ---- from OAI.Analysis.BackwardIntertwiners.HilbertClassification ----
namespace OAI

namespace Hyperinvariant233
open Filter
open scoped Topology
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end Hyperinvariant233

namespace Hyperinvariant233
open Submodule TopologicalSpace
universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [SeparableSpace H]

theorem orthonormal_subtype_countable (w : Set H)
    (hw : Orthonormal ℂ (Subtype.val : w → H)) : Countable w := by
  classical
  let : DiscreteTopology w := discreteTopology_iff_isOpen_singleton.mpr (by
    intro i
    have ho : IsOpen {j : w | (1 / 2 : ℝ) < ‖inner ℂ (i : H) (j : H)‖} :=
      isOpen_lt continuous_const (continuous_const.inner continuous_subtype_val).norm
    have he : {j : w | (1 / 2 : ℝ) < ‖inner ℂ (i : H) (j : H)‖} = {i} := by
      ext j
      rw [Set.mem_ofPred_eq, orthonormal_iff_ite.mp hw i j]
      by_cases hij : i = j <;> norm_num [hij, eq_comm]
    rwa [he] at ho)
  exact separableSpace_iff_countable.mp inferInstance

theorem exists_nat_hilbertBasis (hInf : ¬FiniteDimensional ℂ H) :
    Nonempty (HilbertBasis ℕ ℂ H) := by
  classical
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis ℂ H
  have hw : Orthonormal ℂ (Subtype.val : w → H) := by
    simpa only [hb] using b.orthonormal
  let : Countable w := orthonormal_subtype_countable w hw
  let : Infinite w := by
    refine not_finite_iff_infinite.mp ?_
    intro hfin
    let : Finite w := hfin
    let : Fintype w := Fintype.ofFinite w
    exact hInf (Module.Finite.of_basis b.toOrthonormalBasis.toBasis)
  let e : ℕ ≃ w := Classical.choice (inferInstance : Nonempty (ℕ ≃ w))
  have ho : Orthonormal ℂ (b ∘ e) := b.orthonormal.comp e e.injective
  have hr : Set.range (b ∘ e) = Set.range b := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨e n, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp⟩
  exact ⟨HilbertBasis.mk ho (by rw [hr, b.dense_span])⟩

theorem nonempty_linearIsometryEquiv
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [SeparableSpace K]
    (hH : ¬FiniteDimensional ℂ H) (hK : ¬FiniteDimensional ℂ K) :
    Nonempty (H ≃ₗᵢ[ℂ] K) := by
  obtain ⟨bH⟩ := exists_nat_hilbertBasis hH
  obtain ⟨bK⟩ := exists_nat_hilbertBasis hK
  exact ⟨bH.repr.trans bK.repr.symm⟩

end Hyperinvariant233

end OAI

-- ---- from OAI.Analysis.BackwardIntertwiners.OperatorTransport ----
namespace OAI

namespace Hyperinvariant233
open Filter
open scoped Topology
universe u v
variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem norm_conjugate_le (e : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    ‖e.conjStarAlgEquiv T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖e (T (e.symm x))‖ ≤ ‖T‖ * ‖x‖
  rw [e.norm_map]
  simpa only [e.symm.norm_map] using T.le_opNorm (e.symm x)

theorem norm_conjugate (e : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    ‖e.conjStarAlgEquiv T‖ = ‖T‖ := by
  apply le_antisymm (norm_conjugate_le e T)
  have he : e.symm.conjStarAlgEquiv (e.conjStarAlgEquiv T) = T := by
    ext x
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.symm_apply_apply]
  have h := norm_conjugate_le e.symm (e.conjStarAlgEquiv T)
  rwa [he] at h

theorem transitiveCommutant_conjugate (e : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H)
    (hT : TransitiveCommutant T) : TransitiveCommutant (e.conjStarAlgEquiv T) := by
  intro W hW hInv
  let U : Submodule ℂ H := W.comap e.toLinearMap
  have hU : IsClosed (U : Set H) := hW.preimage e.continuous
  have hUI : ∀ A : H →L[ℂ] H, A * T = T * A → ∀ x ∈ U, A x ∈ U := by
    intro A hA x hx
    change e (A x) ∈ W
    have hc : e.conjStarAlgEquiv A * e.conjStarAlgEquiv T =
        e.conjStarAlgEquiv T * e.conjStarAlgEquiv A := by
      simpa only [map_mul] using congrArg e.conjStarAlgEquiv hA
    have hm := hInv (e.conjStarAlgEquiv A) hc (e x) hx
    simpa using hm
  rcases hT U hU hUI with hz | ho
  · left
    apply le_antisymm _ bot_le
    intro y hy
    have hx : e.symm y ∈ U := by change e (e.symm y) ∈ W; simpa using hy
    rw [hz] at hx
    have hzero : e.symm y = 0 := hx
    have := congrArg e hzero
    simpa using this
  · right
    apply le_antisymm le_top
    intro y _
    have hx : e.symm y ∈ U := by rw [ho]; trivial
    change e (e.symm y) ∈ W at hx
    simpa using hx

theorem mainClaim_transport (e : H ≃ₗᵢ[ℂ] K) (h : MainClaim (H := H)) :
    MainClaim (H := K) := by
  obtain ⟨T, hT0, hq, ht⟩ := h
  refine ⟨e.conjStarAlgEquiv T, ?_, ?_, transitiveCommutant_conjugate e T ht⟩
  · exact fun hzero => hT0 (e.conjStarAlgEquiv.injective (by simpa using hzero))
  · have he : (fun n : ℕ => ‖(e.conjStarAlgEquiv T) ^ n‖ ^ (1 / (n : ℝ))) =
        (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) := by
      funext n
      rw [← map_pow, norm_conjugate]
    rwa [he]

end Hyperinvariant233

namespace Hyperinvariant233
open Filter
open scoped Topology
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem mem_commutant_iff (T A : H →L[ℂ] H) :
    A ∈ commutant T ↔ A * T = T * A := by
  simp only [commutant, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  exact eq_comm

variable [completeSpace : CompleteSpace H]

omit completeSpace in
theorem commutant_isClosed_strong [CompleteSpace H] (T : H →L[ℂ] H) :
    @IsClosed (H →L[ℂ] H) strongOperatorTopology (commutant T : Set (H →L[ℂ] H)) := by
  let : TopologicalSpace (H →L[ℂ] H) := strongOperatorTopology
  have heval : ∀ x : H, Continuous (fun A : H →L[ℂ] H => A x) := by
    intro x
    exact (continuous_apply x).comp continuous_induced_dom
  have hset : (commutant T : Set (H →L[ℂ] H)) =
      ⋂ x : H, {A : H →L[ℂ] H | A (T x) = T (A x)} := by
    ext A
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe, mem_commutant_iff]
    constructor
    · intro h x
      exact congrArg (fun B : H →L[ℂ] H => B x) h
    · intro h
      ext x
      exact h x
  rw [hset]
  exact isClosed_iInter (fun x => isClosed_eq (heval (T x)) (T.continuous.comp (heval x)))

omit completeSpace in
theorem scalar_of_commutant_top [CompleteSpace H] (T : H →L[ℂ] H) (h : commutant T = ⊤) :
    ∃ c : ℂ, algebraMap ℂ (H →L[ℂ] H) c = T := by
  have hc : T ∈ Subalgebra.center ℂ (H →L[ℂ] H) := by
    rw [Subalgebra.mem_center_iff]
    intro A
    apply (mem_commutant_iff T A).mp
    rw [h]
    trivial
  rw [Algebra.IsCentral.center_eq_bot] at hc
  exact Algebra.mem_bot.mp hc

theorem commutant_ne_top_of_nonzero_quasinilpotent [Nontrivial H]
    (T : H →L[ℂ] H) (hT : T ≠ 0)
    (hlim : Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0)) :
    commutant T ≠ ⊤ := by
  intro htop
  obtain ⟨c, hc⟩ := scalar_of_commutant_top T htop
  have hroot (n : ℕ) (hn : n ≠ 0) : ‖T ^ n‖ ^ (1 / (n : ℝ)) = ‖c‖ := by
    rw [← hc, Algebra.algebraMap_eq_smul_one, smul_pow, one_pow,
      norm_smul, norm_pow, norm_one, mul_one, one_div]
    exact Real.pow_rpow_inv_natCast (norm_nonneg c) hn
  have hevent : (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) =ᶠ[atTop]
      (fun _ : ℕ => ‖c‖) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact hroot n (Nat.ne_of_gt hn)
  have hconst : Tendsto (fun _ : ℕ => ‖c‖) atTop (𝓝 0) := hlim.congr' hevent
  have hc0 : ‖c‖ = 0 := tendsto_nhds_unique tendsto_const_nhds hconst
  apply hT
  rw [← hc, norm_eq_zero.mp hc0, map_zero]

theorem fullClaim_of_mainClaim [Nontrivial H] (h : MainClaim (H := H)) :
    FullClaim (H := H) := by
  obtain ⟨T, hT, hlim, htrans⟩ := h
  exact ⟨T, hT, hlim, htrans,
    commutant_ne_top_of_nonzero_quasinilpotent T hT hlim,
    commutant_isClosed_strong T⟩

end Hyperinvariant233

end OAI

-- ---- from OAI.Analysis.BackwardIntertwiners.AlgebraCorollary ----
namespace OAI

namespace BackwardIntertwiners
open Filter Topology MeasureTheory Set
noncomputable section
lemma powerCost_quadratic {n : ℕ} (hn : 2 ≤ n) : (n:ℝ)^2 ≤ 10*(powerCost n:ℝ) := by
  have hr : (n+1)^2 < ((n+1)^2/4+1)*4 := by omega
  have hr' : ((n:ℝ)+1)^2 < ((powerCost n:ℝ)+1)*4 := by exact_mod_cast hr
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [sq_nonneg (n:ℝ)]
lemma rootnorm_tendsto_zero_of_bound (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hbound : ∀ n, a n ≤ Real.exp (-10*(powerCost n:ℝ))) :
    Tendsto (fun n:ℕ=>a n ^ (1/(n:ℝ))) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n=>Real.rpow_nonneg (ha n) _))
    (g:=fun n:ℕ=>Real.exp (-(n:ℝ)))
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have h := Real.rpow_le_rpow (ha n) (hbound n) (one_div_nonneg.mpr hnpos.le)
    rw [←Real.exp_mul] at h
    apply h.trans
    apply Real.exp_le_exp.mpr
    have hc := powerCost_quadratic hn
    have hh : (-10*(powerCost n:ℝ))/n ≤ -(n:ℝ) :=
      (div_le_iff₀ hnpos).mpr (by nlinarith)
    simpa only [one_div,div_eq_mul_inv,one_mul] using hh
  · exact Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
lemma forwardOperator_quasinilpotent :
    Tendsto (fun n : ℕ=>‖forwardOperator^n‖^(1/(n:ℝ))) atTop (𝓝 0) :=
  rootnorm_tendsto_zero_of_bound _ (fun _=>norm_nonneg _) forwardOperator_power_norm
lemma forward_transitiveCommutant : Hyperinvariant233.TransitiveCommutant forwardOperator := by
  intro L hL hInv
  apply forward_backward_scalar_transitive L hL
  · exact hInv forwardOperator rfl
  · exact hInv backwardOperator forward_backward_commute.symm
  · intro g
    exact hInv (scalarMultiplier g) (forward_scalar_commute g).symm
lemma direct_mainClaim : Hyperinvariant233.MainClaim (H:=GlobalHilbert) :=
  ⟨forwardOperator,forwardOperator_ne_zero,forwardOperator_quasinilpotent,forward_transitiveCommutant⟩
open scoped ENNReal
theorem direct_algebra_corollary (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (hInf : ¬FiniteDimensional ℂ H) :
    Hyperinvariant233.FullClaim (H:=H) := by
  let : Nontrivial H := not_subsingleton_iff_nontrivial.mp (by
    intro hs
    let : Subsingleton H := hs
    exact hInf inferInstance)
  obtain ⟨e⟩ := Hyperinvariant233.nonempty_linearIsometryEquiv
    (H:=GlobalHilbert) (K:=H) globalHilbert_infinite hInf
  exact Hyperinvariant233.fullClaim_of_mainClaim (Hyperinvariant233.mainClaim_transport e direct_mainClaim)

end
end BackwardIntertwiners

end OAI

-- ---- mission target ----
open OAI OAI.BackwardIntertwiners
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace OAI
namespace BackwardIntertwiners
theorem _root_.solution (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (hInf : ¬FiniteDimensional ℂ H) :
    Hyperinvariant233.FullClaim (H:=H) := by
  first
    | exact OAI.BackwardIntertwiners.direct_algebra_corollary H hInf
    | exact OAI.BackwardIntertwiners.direct_algebra_corollary
    | (apply OAI.BackwardIntertwiners.direct_algebra_corollary <;> assumption)
    | (intros; apply OAI.BackwardIntertwiners.direct_algebra_corollary <;> assumption)
end BackwardIntertwiners
end OAI
