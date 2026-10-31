-- Prove2me | solution 1 for OAI.Release061.NashPatch.principal_rank_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:01:05.61415+00:00
-- url     : https://prove2.me/submissions/a5c7ce44-db17-4aac-98e7-65febe658d36

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S003

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticImplicitScalar
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061


open Set Filter Topology

theorem analytic_local_inverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {a : E} (hf : AnalyticAt ℂ f a)
    (i : E ≃L[ℂ] F) (hi : HasFDerivAt f (i : E →L[ℂ] F) a) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ a ∈ e.source ∧
      AnalyticAt ℂ e.symm (f a) := by
  have hs : HasStrictFDerivAt f (i : E →L[ℂ] F) a := by
    simpa only [hi.fderiv] using hf.hasStrictFDerivAt
  let e := hs.toOpenPartialHomeomorph f
  refine ⟨e, hs.toOpenPartialHomeomorph_coe, hs.mem_toOpenPartialHomeomorph_source, ?_⟩
  obtain ⟨p, hp⟩ := hf
  have he : (e : E → F) = f := hs.toOpenPartialHomeomorph_coe
  have hpe : HasFPowerSeriesAt e p a := he ▸ hp
  have hcoeff : p 1 = (continuousMultilinearCurryFin1 ℂ E F).symm
      (i : E →L[ℂ] F) := by
    apply (continuousMultilinearCurryFin1 ℂ E F).injective
    simpa using hp.hasFDerivAt.unique hi
  simpa only [he] using
    (e.hasFPowerSeriesAt_symm hs.mem_toOpenPartialHomeomorph_source hpe hcoeff).analyticAt

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialEmptyInterior
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology

theorem PolynomialSignSet.exists_regular_polynomial {X ι : Type*}
    [TopologicalSpace X] {c : X → ι → ℝ} (hc : Continuous c)
    {S : Set X} (hS : PolynomialSignSet c S) :
    ∃ P : MvPolynomial ι ℝ, P ≠ 0 ∧ ∀ x,
      MvPolynomial.eval (c x) P ≠ 0 → S ∈ 𝓝 x ∨ Sᶜ ∈ 𝓝 x := by
  classical
  induction hS with
  | zero p =>
    by_cases hp : p = 0
    · subst p
      refine ⟨1,one_ne_zero,fun x _ => Or.inl ?_⟩
      simp
    · refine ⟨p,hp,fun x hx => Or.inr ?_⟩
      exact ((MvPolynomial.continuous_eval p).comp hc).continuousAt.eventually_ne hx
  | positive p =>
    by_cases hp : p = 0
    · subst p
      refine ⟨1,one_ne_zero,fun x _ => Or.inr ?_⟩
      simp
    · refine ⟨p,hp,fun x hx => ?_⟩
      rcases lt_or_gt_of_ne hx with hneg | hpos
      · right
        filter_upwards [((MvPolynomial.continuous_eval p).comp hc).continuousAt.tendsto.eventually_lt_const hneg]
          with y hy
        exact not_lt_of_ge hy.le
      · exact Or.inl (((MvPolynomial.continuous_eval p).comp hc).continuousAt.tendsto.eventually_const_lt hpos)
  | @compl _ _ ih =>
    obtain ⟨P,hP,hreg⟩ := ih
    refine ⟨P,hP,fun x hx => ?_⟩
    simpa only [compl_compl] using (hreg x hx).symm
  | @union _ _ _ _ ihS ihT =>
    obtain ⟨P,hP,hregP⟩ := ihS
    obtain ⟨Q,hQ,hregQ⟩ := ihT
    refine ⟨P*Q,mul_ne_zero hP hQ,fun x hx => ?_⟩
    have hPQ : MvPolynomial.eval (c x) P ≠ 0 ∧ MvPolynomial.eval (c x) Q ≠ 0 := by
      simpa only [map_mul,mul_ne_zero_iff] using hx
    rcases hregP x hPQ.1 with hs | hs
    · exact Or.inl (Filter.mem_of_superset hs subset_union_left)
    rcases hregQ x hPQ.2 with ht | ht
    · exact Or.inl (Filter.mem_of_superset ht subset_union_right)
    · exact Or.inr (by simpa only [compl_union] using inter_mem hs ht)

theorem PolynomialSignSet.frontier_polynomial {X ι : Type*}
    [TopologicalSpace X] {c : X → ι → ℝ} (hc : Continuous c)
    {S : Set X} (hS : PolynomialSignSet c S) :
    ∃ P : MvPolynomial ι ℝ, P ≠ 0 ∧
      ∀ x ∈ frontier S, MvPolynomial.eval (c x) P = 0 := by
  obtain ⟨P,hP,hreg⟩ := hS.exists_regular_polynomial hc
  refine ⟨P,hP,fun x hx => ?_⟩
  by_contra hne
  rcases hreg x hne with hs | hs
  · exact hx.2 (mem_interior_iff_mem_nhds.mpr hs)
  · have hx' : x ∈ frontier Sᶜ := by simpa only [frontier_compl] using hx
    exact hx'.2 (mem_interior_iff_mem_nhds.mpr hs)

theorem PolynomialSignSet.polynomial_of_empty_interior {X ι : Type*}
    [TopologicalSpace X] {c : X → ι → ℝ} (hc : Continuous c)
    {S : Set X} (hS : PolynomialSignSet c S) (hempty : interior S = ∅) :
    ∃ P : MvPolynomial ι ℝ, P ≠ 0 ∧ ∀ x ∈ S, MvPolynomial.eval (c x) P = 0 := by
  obtain ⟨P,hP,hzero⟩ := hS.frontier_polynomial hc
  refine ⟨P,hP,fun x hx => hzero x ?_⟩
  exact ⟨subset_closure hx,by simp only [hempty,mem_empty_iff_false,not_false_eq_true]⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AlgebraicGraphPolynomial
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology

theorem real_graph_empty_interior {ι : Type*} [Fintype ι]
    (B : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ) :
    interior {x : Option ι → ℝ | (fun i => x (some i)) ∈ B ∧
      x none = f (fun i => x (some i))} = ∅ := by
  classical
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxS := interior_subset hx
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  let y : Option ι → ℝ := x + Pi.single none (r/2)
  have hdist : dist y x < r := by
    rw [dist_eq_norm]
    change ‖x + Pi.single none (r/2) - x‖ < r
    rw [add_sub_cancel_left,Pi.norm_single]
    rw [Real.norm_eq_abs,abs_of_pos (by positivity : 0 < r/2)]
    linarith
  have hyS := hball hdist
  have hyeq := hyS.2
  change y none = _ at hyeq
  simp only [y,Pi.add_apply,Pi.single_eq_same,Pi.single_eq_of_ne (Option.some_ne_none _),add_zero] at hyeq
  linarith [hxS.2,hyeq]

theorem semialgebraic_graph_polynomial {ι : Type*} [Fintype ι]
    (B : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ)
    (hgraph : PolynomialSignSet (id : (Option ι → ℝ) → (Option ι → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = f (fun i => x (some i))}) :
    ∃ P : MvPolynomial (Option ι) ℝ, P ≠ 0 ∧
      ∀ s ∈ B, MvPolynomial.eval (fun a => a.elim (f s) s) P = 0 := by
  obtain ⟨P,hP,hzero⟩ := hgraph.polynomial_of_empty_interior continuous_id
    (real_graph_empty_interior B f)
  exact ⟨P,hP,fun s hs => hzero _ ⟨hs,rfl⟩⟩

theorem algebraic_of_graph_polynomial {R F ι : Type*}
    [Field R] [Field F] [Algebra R F]
    (x : ι → F) (hx : AlgebraicIndependent R x) (y : F)
    (P : MvPolynomial (Option ι) R) (hP : P ≠ 0)
    (hzero : MvPolynomial.aeval (fun a => a.elim y x) P = 0) :
    IsAlgebraic (IntermediateField.adjoin R (range x)) y := by
  let L := IntermediateField.adjoin R (range x)
  let xL : ι → L := fun i => ⟨x i,IntermediateField.subset_adjoin _ _ (mem_range_self i)⟩
  have hxi : Function.Injective (MvPolynomial.aeval xL : MvPolynomial ι R →ₐ[R] L) := by
    apply Function.Injective.of_comp (f := L.val)
    change Function.Injective (L.val ∘ MvPolynomial.aeval xL)
    have heq : L.val.comp (MvPolynomial.aeval xL) = MvPolynomial.aeval x :=
      MvPolynomial.comp_aeval xL L.val
    change Function.Injective (L.val.comp (MvPolynomial.aeval xL))
    rw [heq]
    exact algebraicIndependent_iff_injective_aeval.mp hx
  let Q : Polynomial L := (MvPolynomial.optionEquivLeft R ι P).map (MvPolynomial.aeval xL).toRingHom
  refine ⟨Q,?_,?_⟩
  · have h := (Polynomial.map_injective (MvPolynomial.aeval xL).toRingHom hxi).ne
      ((MvPolynomial.optionEquivLeft R ι).injective.ne hP)
    simpa only [Q, map_zero, Polynomial.map_zero] using h
  · have heval (P : MvPolynomial (Option ι) R) :
        Polynomial.aeval y ((MvPolynomial.optionEquivLeft R ι P).map (MvPolynomial.aeval xL).toRingHom) =
          MvPolynomial.aeval (fun a => a.elim y x) P := by
      induction P using MvPolynomial.induction_on with
      | C c =>
        simp only [MvPolynomial.optionEquivLeft_C,Polynomial.map_C,Polynomial.aeval_C]
        change (algebraMap L F) (MvPolynomial.aeval xL (MvPolynomial.C c)) = _
        rw [MvPolynomial.aeval_C, ← IsScalarTower.algebraMap_apply, MvPolynomial.aeval_C]
      | add p q hp hq => simp only [map_add,Polynomial.map_add,hp,hq]
      | mul_X p i hp =>
        cases i with
        | none => simp only [map_mul,MvPolynomial.optionEquivLeft_X_none,Polynomial.map_mul,
            Polynomial.map_X,Polynomial.aeval_X,MvPolynomial.aeval_X,Option.elim_none,hp]
        | some i =>
          simp only [map_mul,MvPolynomial.optionEquivLeft_X_some,Polynomial.map_mul,
            Polynomial.map_C,Polynomial.aeval_C,MvPolynomial.aeval_X,Option.elim_some,hp]
          change _ * algebraMap L F (MvPolynomial.aeval xL (MvPolynomial.X i)) = _
          rw [MvPolynomial.aeval_X]
          rfl
    exact (heval P).trans hzero

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialRelationDependentPartials
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Algebra KaehlerDifferential _root_.Module
open scoped TensorProduct IntermediateField.algebraAdjoinAdjoin

theorem algebraicIndependent_differentials
    {R K ι : Type*} [Field R] [CharZero R] [Field K] [Algebra R K]
    (x : ι → K) (hx : AlgebraicIndependent R x) :
    LinearIndependent K (fun i => D R K (x i)) := by
  obtain ⟨s,hxs,hs⟩ := exists_isTranscendenceBasis_superset
    ((algebraicIndependent_subtype_range hx.injective).2 hx)
  let q : ι → s := fun i => ⟨x i,hxs (mem_range_self i)⟩
  have hq : Function.Injective q := by
    intro i j hij
    exact hx.injective (congrArg Subtype.val hij)
  have hlin := (transcendenceDifferentialBasis (fun z : s => z.val) hs).linearIndependent.comp q hq
  simpa only [Function.comp_def,transcendenceDifferentialBasis_apply,q] using hlin

end

open Set Algebra KaehlerDifferential _root_.Module

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_DifferentialMemSpanTranscendence
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Algebra KaehlerDifferential _root_.Module
open scoped TensorProduct

theorem differential_mem_span_adjoin {R K κ : Type*}
    [Field R] [Field K] [Algebra R K] (q : κ → K)
    {y : K} (hy : y ∈ IntermediateField.adjoin R (range q)) :
    D R K y ∈ Submodule.span K (range (fun j => D R K (q j))) := by
  have hle : IntermediateField.adjoin R (range q) ≤
      differentialSubfield (Submodule.span K (range (fun j => D R K (q j)))) := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨j,rfl⟩
    exact Submodule.subset_span (mem_range_self j)
  exact hle hy

theorem differential_mem_span_transcendenceBasis
    {R L K ι : Type*} [Field R] [CharZero R] [Field L] [Field K]
    [Algebra R L] [Algebra R K] [Algebra L K] [IsScalarTower R L K]
    (x : ι → L) (hx : IsTranscendenceBasis R x) (y : L) :
    D R K (algebraMap L K y) ∈
      Submodule.span K (range (fun i => D R K (algebraMap L K (x i)))) := by
  let M := Submodule.span K (range (fun i => D R K (algebraMap L K (x i))))
  change _ ∈ M
  rw [← KaehlerDifferential.map_D (R := R) (S := R) (A := L) (B := K)]
  have hmem : D R L y ∈ Submodule.span L (range (transcendenceDifferentialBasis x hx)) := by
    rw [(transcendenceDifferentialBasis x hx).span_eq]
    trivial
  generalize D R L y = z at hmem ⊢
  induction hmem using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i,rfl⟩ := hz
    simp only [transcendenceDifferentialBasis_apply, KaehlerDifferential.map_D]
    exact Submodule.subset_span (mem_range_self i)
  | zero => exact by simp
  | add z w _ _ hz hw => simpa only [map_add] using M.add_mem hz hw
  | smul a z _ hz =>
    rw [map_smul]
    exact (M.restrictScalars L).smul_mem a hz

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticMulZeroGerm
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Algebra KaehlerDifferential _root_.Module

theorem differential_span_rank_eq_trdeg
    {R K κ : Type} [Field R] [CharZero R] [Field K] [Algebra R K]
    (q : κ → K) :
    Module.rank K (Submodule.span K (range (fun j => D R K (q j)))) =
      Algebra.trdeg R (IntermediateField.adjoin R (range q)) := by
  let L := IntermediateField.adjoin R (range q)
  obtain ⟨t,ht⟩ := exists_isTranscendenceBasis R L
  let x : t → K := fun i => i.val.val
  have hx : AlgebraicIndependent R x := ht.1.map' (f := L.val) Subtype.val_injective
  have hlin := algebraicIndependent_differentials x hx
  have hspan : Submodule.span K (range (fun j => D R K (q j))) =
      Submodule.span K (range (fun i => D R K (x i))) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      let y : L := ⟨q j,IntermediateField.subset_adjoin _ _ (mem_range_self j)⟩
      exact differential_mem_span_transcendenceBasis (K := K) (fun i : t => i.val) ht y
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact differential_mem_span_adjoin q i.val.property
  rw [hspan,rank_span hlin]
  calc
    Cardinal.mk (range (fun i => D R K (x i))) = Cardinal.mk t := by
      simpa only [Cardinal.lift_id] using Cardinal.mk_range_eq_of_injective hlin.injective
    _ = _ := ht.cardinalMk_eq_trdeg

end

open Set Filter Topology

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_EtaleDerivationExtensionUnique
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology
variable {n : ℕ}

theorem analyticGerm_aeval {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ι → E → ℂ) (hf : ∀ i, AnalyticAt ℂ (f i) 0)
    (P : MvPolynomial ι ℂ) :
    (MvPolynomial.aeval (fun i => analyticGermOf E (f i) (hf i)) P).val =
      ((fun x => MvPolynomial.eval (fun i => f i x) P) : Filter.Germ (𝓝 (0:E)) ℂ) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.aeval_C,MvPolynomial.eval_C]; rfl
  | add P Q hP hQ =>
    simp only [map_add,Subring.coe_add,hP,hQ]
    rfl
  | mul_X P i hP =>
    simp only [map_mul,MvPolynomial.aeval_X,Subring.coe_mul,hP,MvPolynomial.eval_X]
    rfl

theorem algebraicIndependent_analyticCoordinate :
    AlgebraicIndependent ℂ (analyticCoordinate (n := n)) := by
  rw [algebraicIndependent_iff_ker_eq_bot]
  apply le_antisymm _ bot_le
  intro P hP
  simp only [RingHom.mem_ker,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] at hP
  have he : (fun x : Fin n → ℂ => MvPolynomial.eval x P) =ᶠ[𝓝 0] 0 := by
    apply Filter.Germ.coe_eq.mp
    rw [← analyticGerm_aeval (fun (i : Fin n) (x : Fin n → ℂ) => x i)
      (fun i => (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt _) P]
    exact congrArg Subtype.val hP
  have hzero := (AnalyticOnNhd.eval_mvPolynomial P).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ (0 : Fin n → ℂ)) he
  have : P = 0 := by
    apply MvPolynomial.funext
    intro x
    simpa only [map_zero,Pi.zero_apply] using hzero (mem_univ x)
  simpa only [Ideal.mem_bot] using this

end

open Algebra KaehlerDifferential
open scoped TensorProduct

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AlgebraicIndependentNashPartials
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology Algebra KaehlerDifferential
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem algebraicIndependent_meromorphicCoordinate {n : ℕ} :
    AlgebraicIndependent ℂ (meromorphicCoordinate (n := n)) := by
  exact (algebraicIndependent_analyticCoordinate (n := n)).map'
    (f := IsScalarTower.toAlgHom ℂ (AnalyticGerm (Fin n → ℂ))
      (MeromorphicGermField (Fin n → ℂ)))
    (IsFractionRing.injective _ _)

end

open Set Algebra KaehlerDifferential _root_.Module
open scoped IntermediateField.algebraAdjoinAdjoin

theorem differential_mem_span_of_isAlgebraic_adjoin
    {R F ι : Type*} [Field R] [CharZero R] [Field F] [Algebra R F]
    (x : ι → F) (hx : AlgebraicIndependent R x) (y : F)
    (hy : IsAlgebraic (IntermediateField.adjoin R (range x)) y) :
    D R F y ∈ Submodule.span F (range (fun i => D R F (x i))) := by
  let A := Algebra.adjoin R (range x)
  let L := IntermediateField.adjoin R (range x)
  let C := algebraicClosure L F
  have hA : IsTranscendenceBasis R (hx.aevalEquiv ∘ MvPolynomial.X) :=
    hx.aevalEquiv.isTranscendenceBasis (IsTranscendenceBasis.mvPolynomial ι R)
  have hL := IsTranscendenceBasis.algebraMap_comp (A := L) hA
  have : FaithfulSMul L C := (faithfulSMul_iff_algebraMap_injective L C).mpr
    (algebraMap L C).injective
  have : IsScalarTower R C F := IsScalarTower.of_algebraMap_eq fun r => rfl
  have hC := IsTranscendenceBasis.algebraMap_comp (A := C) hL
  let yC : C := ⟨y,mem_algebraicClosure_iff.mpr hy⟩
  convert differential_mem_span_transcendenceBasis
    (K := F) _ hC yC using 1
  · congr 2
    funext i
    change D R F (x i) = D R F ((hx.aevalEquiv (MvPolynomial.X i) : A) : F)
    simp only [AlgebraicIndependent.aevalEquiv_apply_coe,MvPolynomial.aeval_X]
  · rfl

theorem partials_injective_on_differential_span
    {R F ι : Type*} [Field R] [Field F] [Algebra R F] [Fintype ι] [DecidableEq ι]
    (x : ι → F) (δ : ι → Derivation R F F)
    (hδ : ∀ i j, δ i (x j) = if j = i then 1 else 0)
    {z : Ω[F⁄R]} (hz : z ∈ Submodule.span F (range (fun i => D R F (x i))))
    (hzero : ∀ i, (δ i).liftKaehlerDifferential z = 0) : z = 0 := by
  obtain ⟨c,rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hz
  have hc : ∀ i, c i = 0 := by
    intro i
    simpa only [map_sum,_root_.map_smul,Derivation.liftKaehlerDifferential_comp_D,
      hδ,smul_eq_mul,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      using hzero i
  simp only [hc,zero_smul,Finset.sum_const_zero]

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticNashRank
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Algebra KaehlerDifferential _root_.Module

theorem nash_partial_span_rank_eq_trdeg
    {R F ι κ : Type} [Field R] [CharZero R] [Field F] [Algebra R F]
    [Fintype ι] [DecidableEq ι]
    (x : ι → F) (hx : AlgebraicIndependent R x)
    (δ : ι → Derivation R F F)
    (hδ : ∀ i j, δ i (x j) = if j = i then 1 else 0)
    (q : κ → F) (hqalg : ∀ j, IsAlgebraic (IntermediateField.adjoin R (range x)) (q j)) :
    Module.rank F (Submodule.span F (range (fun j i => δ i (q j)))) =
      Algebra.trdeg R (IntermediateField.adjoin R (range q)) := by
  let Q := Submodule.span F (range (fun j => D R F (q j)))
  let X := Submodule.span F (range (fun i => D R F (x i)))
  let L : Ω[F⁄R] →ₗ[F] (ι → F) := LinearMap.pi fun i => (δ i).liftKaehlerDifferential
  have hQX : Q ≤ X := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact differential_mem_span_of_isAlgebraic_adjoin x hx _ (hqalg j)
  have hinj : Function.Injective (L.comp Q.subtype) := by
    intro a b hab
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply partials_injective_on_differential_span x δ hδ (hQX (Q.sub_mem a.property b.property))
    intro i
    have hi := congrFun hab i
    change (δ i).liftKaehlerDifferential a.val = (δ i).liftKaehlerDifferential b.val at hi
    rw [map_sub,hi,sub_self]
  have heq : LinearMap.range (L.comp Q.subtype) =
      Submodule.span F (range (fun j i => δ i (q j))) := by
    rw [LinearMap.range_comp,Submodule.range_subtype]
    change (Submodule.span F _).map L = _
    rw [Submodule.map_span,← Set.range_comp]
    congr 2
    funext j i
    exact Derivation.liftKaehlerDifferential_comp_D (δ i) (q j)
  rw [← heq,rank_range_of_injective _ hinj]
  exact differential_span_rank_eq_trdeg q

end

open Set Filter Topology

theorem meromorphicGerm_aeval_eq_zero_iff {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : ι → E → ℂ) (hf : ∀ i, AnalyticAt ℂ (f i) 0)
    (P : MvPolynomial ι ℂ) :
    MvPolynomial.aeval (fun i => meromorphicGermOf (f i) (hf i)) P = 0 ↔
      (fun x => MvPolynomial.eval (fun i => f i x) P) =ᶠ[𝓝 (0:E)] 0 := by
  let A := AnalyticGerm E
  let K := MeromorphicGermField E
  have heq : MvPolynomial.aeval (fun i => meromorphicGermOf (f i) (hf i)) P =
      algebraMap A K (MvPolynomial.aeval (fun i => analyticGermOf E (f i) (hf i)) P) := by
    exact (MvPolynomial.comp_aeval_apply (fun i => analyticGermOf E (f i) (hf i)) (IsScalarTower.toAlgHom ℂ A K) P).symm
  rw [heq, map_eq_zero_iff _ (IsFractionRing.injective A K)]
  constructor
  · intro h
    apply Filter.Germ.coe_eq.mp
    rw [← analyticGerm_aeval f hf P]
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    rw [analyticGerm_aeval f hf P]
    exact Filter.Germ.coe_eq.mpr h

theorem analytic_nash_rank {n N : ℕ}
    (f : Fin N → (Fin n → ℂ) → ℂ) (hf : ∀ j, AnalyticAt ℂ (f j) 0)
    (halg : ∀ j, IsAlgebraic (IntermediateField.adjoin ℂ
      (range (meromorphicCoordinate (n := n)))) (meromorphicGermOf (f j) (hf j))) :
    Module.rank (MeromorphicGermField (Fin n → ℂ))
      (Submodule.span (MeromorphicGermField (Fin n → ℂ))
        (range (fun j i => meromorphicPartial i (meromorphicGermOf (f j) (hf j))))) =
      Algebra.trdeg ℂ (IntermediateField.adjoin ℂ (range
        (fun j => meromorphicGermOf (f j) (hf j)))) := by
  exact nash_partial_span_rank_eq_trdeg meromorphicCoordinate
    algebraicIndependent_meromorphicCoordinate meromorphicPartial meromorphicPartial_coordinate
    (fun j => meromorphicGermOf (f j) (hf j)) halg

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticZeroRealPolydisc
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

theorem analytic_zero_of_real_interval {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (ball 0 r))
    (hz : ∀ t : ℝ, |t| < r → f t = 0) : EqOn f 0 (ball 0 r) := by
  apply hf.eqOn_zero_of_preconnected_of_mem_closure (convex_ball (0 : ℂ) r).isPreconnected
    (mem_ball_self hr)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let t := min ε r / 2
  have ht : 0 < t := half_pos (lt_min hε hr)
  have htε : t < ε := lt_of_lt_of_le (half_lt_self (lt_min hε hr)) (min_le_left _ _)
  have htr : t < r := lt_of_lt_of_le (half_lt_self (lt_min hε hr)) (min_le_right _ _)
  refine ⟨(t : ℂ),⟨hz t (by simpa [abs_of_pos ht] using htr),?_⟩,?_⟩
  · simpa using ht.ne'
  · simpa [dist_eq_norm,Complex.norm_real,abs_of_pos ht] using htε

theorem analytic_zero_of_real_polydisc {n : ℕ} {f : (Fin n → ℂ) → ℂ} {r : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (ball 0 r))
    (hz : ∀ x : Fin n → ℝ, ‖x‖ < r → f (fun i => (x i : ℂ)) = 0) :
    EqOn f 0 (ball 0 r) := by
  classical
  have hgen : ∀ S : Finset (Fin n), ∀ z : Fin n → ℂ, ‖z‖ < r →
      (∀ i ∉ S, (z i).im = 0) → f z = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro z hzr hreal
      have heq : z = fun i => ((z i).re : ℂ) := by
        funext i
        exact Complex.ext rfl (by simpa using hreal i (by simp))
      rw [heq]
      apply hz
      apply (pi_norm_lt_iff hr).mpr
      intro i
      exact (Complex.abs_re_le_norm _).trans_lt ((pi_norm_lt_iff hr).mp hzr i)
    | @insert a S ha ih =>
      intro z hzr hreal
      let g : ℂ → ℂ := fun t => f (Function.update z a t)
      have hupdate : ∀ t : ℂ, ‖t‖ < r → ‖Function.update z a t‖ < r := by
        intro t ht
        apply (pi_norm_lt_iff hr).mpr
        intro i
        by_cases hi : i = a
        · subst i; simpa using ht
        · simpa [Function.update_of_ne hi] using (pi_norm_lt_iff hr).mp hzr i
      have hg : AnalyticOnNhd ℂ g (ball 0 r) := by
        intro t ht
        have haffin : AnalyticAt ℂ (fun t : ℂ => Function.update z a t) t := by
          apply analyticAt_pi_iff.mpr
          intro i
          by_cases hi : i = a
          · subst i
            simp only [Function.update_self]
            exact analyticAt_id
          · simpa only [Function.update_of_ne hi] using (analyticAt_const (𝕜 := ℂ) (v := z i) (x := t))
        have htu : Function.update z a t ∈ ball 0 r := by
          simpa only [mem_ball,dist_zero_right] using
            (hupdate t (by simpa only [mem_ball,dist_zero_right] using ht))
        exact (hf _ htu).comp haffin
      have hgr : ∀ t : ℝ, |t| < r → g t = 0 := by
        intro t ht
        apply ih _ (hupdate t (by simpa using ht))
        intro i hi
        by_cases hia : i = a
        · subst i; simp
        · simpa only [Function.update_of_ne hia] using hreal i (by simp [hia,hi])
      have hzero := analytic_zero_of_real_interval hr hg hgr (by
        simpa only [mem_ball,dist_zero_right] using (pi_norm_lt_iff hr).mp hzr a)
      simpa only [g, Function.update_eq_self, Pi.zero_apply] using hzero
  intro z hzball
  exact hgen Finset.univ z (by simpa only [mem_ball,dist_zero_right] using hzball)
    (by intro i hi; exact (hi (Finset.mem_univ i)).elim)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticExtensionSemialgebraicAlgebraic
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric Topology

theorem analytic_germ_zero_of_real_slice {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f 0)
    (hz : (fun x : Fin n → ℝ => f (fun i => (x i : ℂ))) =ᶠ[𝓝 0] 0) :
    f =ᶠ[𝓝 0] 0 := by
  obtain ⟨r,hr,hfr⟩ := hf.exists_ball_analyticOnNhd
  obtain ⟨s,hs,hzs⟩ := Metric.mem_nhds_iff.mp hz
  have hm : 0 < min r s := lt_min hr hs
  have hzero := analytic_zero_of_real_polydisc hm
    (hfr.mono (Metric.ball_subset_ball (min_le_left r s))) (fun x hx => by
      apply hzs
      simpa only [mem_ball,dist_zero_right] using hx.trans_le (min_le_right r s))
  filter_upwards [Metric.ball_mem_nhds (0 : Fin n → ℂ) hm] with x hx
  exact hzero hx

theorem analytic_extension_of_semialgebraic_isAlgebraic {n : ℕ}
    (B : Set (Fin n → ℝ)) (hB : B ∈ 𝓝 0)
    (f : (Fin n → ℝ) → ℝ) (F : (Fin n → ℂ) → ℂ)
    (hF : AnalyticAt ℂ F 0)
    (hext : (fun x : Fin n → ℝ => F (fun i => (x i : ℂ))) =ᶠ[𝓝 0] fun x => (f x : ℂ))
    (hgraph : PolynomialSignSet (id : (Option (Fin n) → ℝ) → (Option (Fin n) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = f (fun i => x (some i))}) :
    IsAlgebraic (IntermediateField.adjoin ℂ (range (meromorphicCoordinate (n := n))))
      (meromorphicGermOf F hF) := by
  obtain ⟨P,hP,hzero⟩ := semialgebraic_graph_polynomial B f hgraph
  let Q : MvPolynomial (Option (Fin n)) ℂ := P.map Complex.ofRealHom
  have hQ : Q ≠ 0 := by
    exact (map_ne_zero_iff (MvPolynomial.map Complex.ofRealHom)
      (MvPolynomial.map_injective _ Complex.ofReal_injective)).mpr hP
  let g : Option (Fin n) → (Fin n → ℂ) → ℂ := fun a z => a.elim (F z) z
  have hg : ∀ a, AnalyticAt ℂ (g a) 0 := by
    intro a
    cases a with
    | none => exact hF
    | some i => exact (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt _
  have hqA : AnalyticAt ℂ (fun z => MvPolynomial.eval (fun a => g a z) Q) 0 :=
    ((AnalyticOnNhd.eval_mvPolynomial Q) _ (mem_univ _)).comp
      (analyticAt_pi_iff.mpr hg)
  have hqzero : (fun z => MvPolynomial.eval (fun a => g a z) Q) =ᶠ[𝓝 (0 : Fin n → ℂ)] 0 := by
    apply analytic_germ_zero_of_real_slice hqA
    filter_upwards [hB,hext] with x hx hex
    change MvPolynomial.eval (fun a => a.elim (F (fun i => (x i : ℂ))) (fun i => (x i : ℂ))) Q = 0
    rw [hex]
    have heq : (fun a : Option (Fin n) => a.elim (f x : ℂ) (fun i => (x i : ℂ))) =
        Complex.ofRealHom ∘ (fun a : Option (Fin n) => a.elim (f x) x) := by
      funext a
      cases a <;> rfl
    rw [heq,MvPolynomial.eval_map,← MvPolynomial.eval₂_comp,hzero x hx]
    rfl
  have hgerm := (meromorphicGerm_aeval_eq_zero_iff g hg Q).mpr hqzero
  have hval : (fun a => meromorphicGermOf (g a) (hg a)) =
      fun a : Option (Fin n) => a.elim (meromorphicGermOf F hF) meromorphicCoordinate := by
    funext a
    cases a <;> rfl
  rw [hval] at hgerm
  exact algebraic_of_graph_polynomial meromorphicCoordinate algebraicIndependent_meromorphicCoordinate
    (meromorphicGermOf F hF) Q hQ hgerm

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_MeromorphicGermDetZero
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Matrix _root_.Module _root_.Matrix.Module

theorem independent_rows_nonzero_minor {K : Type*} [Field K] {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) K) (hA : LinearIndependent K A) :
    ∃ σ : Fin n → Fin d, Matrix.det (fun i j => A i (σ j)) ≠ 0 := by
  classical
  have hspan : Submodule.span K (range A.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_cols,Matrix.rank_eq_finrank_span_row]
    change Module.finrank K (Submodule.span K (range A)) = _
    rw [finrank_span_eq_card hA,Module.finrank_pi,Fintype.card_fin]
  let b := Basis.ofSpan (s := range A.col) (show ⊤ ≤ Submodule.span K (range A.col) by rw [hspan])
  let b' := b.reindex (b.indexEquiv (Pi.basisFun K (Fin n)))
  have hb : ∀ i, ∃ j, A.col j = b' i := by
    intro i
    apply Basis.ofSpan_subset (show ⊤ ≤ Submodule.span K (range A.col) by rw [hspan])
    refine ⟨(b.indexEquiv (Pi.basisFun K (Fin n))).symm i,?_⟩
    change b _ = b.reindex _ i
    simp only [Basis.reindex_apply]
  choose σ hσ using hb
  refine ⟨σ,?_⟩
  apply Matrix.nonsingular_iff_det_ne_zero.mp
  apply Matrix.Nonsingular.of_linearIndependent_col
  have heq : (fun j i => A i (σ j)) = b' := funext hσ
  change LinearIndependent K (fun j i => A i (σ j))
  rw [heq]
  exact b'.linearIndependent

theorem meromorphicGerm_det_eq_zero_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {n : ℕ}
    (f : Fin n → Fin n → E → ℂ) (hf : ∀ i j, AnalyticAt ℂ (f i j) 0) :
    Matrix.det (fun i j => meromorphicGermOf (f i j) (hf i j)) = 0 ↔
      (fun z => Matrix.det (fun i j => f i j z)) =ᶠ[𝓝 (0 : E)] 0 := by
  let A : Matrix (Fin n) (Fin n) (AnalyticGerm E) := fun i j => analyticGermOf E (f i j) (hf i j)
  have hfield : Matrix.det (fun i j => meromorphicGermOf (f i j) (hf i j)) =
      algebraMap (AnalyticGerm E) (MeromorphicGermField E) A.det := by
    exact ((algebraMap (AnalyticGerm E) (MeromorphicGermField E)).map_det A).symm
  rw [hfield,map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  have hgerm : (A.det).val = ((fun z => Matrix.det (fun i j => f i j z)) : Filter.Germ (𝓝 (0:E)) ℂ) := by
    let H := Filter.Germ.coeRingHom (𝓝 (0:E)) (R := ℂ)
    have h := (analyticGermRing E).subtype.map_det A
    calc
      (A.det).val = ((analyticGermRing E).subtype.mapMatrix A).det := h
      _ = (H.mapMatrix f).det := rfl
      _ = H (Matrix.det f) := (H.map_det f).symm
      _ = _ := congrArg H (funext (fun z => (Pi.evalRingHom (fun _ : E => ℂ) z).map_det f))
  constructor
  · intro h
    apply Filter.Germ.coe_eq.mp
    rw [← hgerm,h]
    rfl
  · intro h
    apply Subtype.ext
    rw [hgerm]
    exact Filter.Germ.coe_eq.mpr h

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticGermMatrixRank
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Matrix _root_.Module _root_.Matrix.Module

theorem matrix_rank_nonzero_minor {K : Type*} [Field K] {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) K) :
    ∃ (ρ : Fin A.rank → Fin n) (σ : Fin A.rank → Fin d),
      Matrix.det (fun i j => A (ρ i) (σ j)) ≠ 0 := by
  classical
  let S := Submodule.span K (range A)
  let a : Fin n → S := fun i => ⟨A i,Submodule.subset_span (mem_range_self i)⟩
  have ha : Submodule.span K (range a) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff S _).mpr rfl
  let b := Basis.ofSpan (s := range a) (show ⊤ ≤ Submodule.span K (range a) by rw [ha])
  have hdim : Module.finrank K S = A.rank := (Matrix.rank_eq_finrank_span_row A).symm
  let b' := b.reindex (b.indexEquiv (Module.finBasisOfFinrankEq K S hdim))
  have hb : ∀ i, ∃ j, a j = b' i := by
    intro i
    apply Basis.ofSpan_subset (show ⊤ ≤ Submodule.span K (range a) by rw [ha])
    refine ⟨(b.indexEquiv (Module.finBasisOfFinrankEq K S hdim)).symm i,?_⟩
    change b _ = b.reindex _ i
    simp only [Basis.reindex_apply]
  choose ρ hρ using hb
  have hli : LinearIndependent K (fun i => A (ρ i)) := by
    have hli := b'.linearIndependent.map' S.subtype (LinearMap.ker_eq_bot.mpr S.injective_subtype)
    have heq : (S.subtype ∘ b') = fun i => A (ρ i) := by
      funext i
      rw [Function.comp_apply,← hρ i]
      rfl
    simpa only [heq] using hli
  obtain ⟨σ,hσ⟩ := independent_rows_nonzero_minor (fun i j => A (ρ i) j) hli
  exact ⟨ρ,σ,hσ⟩

theorem analyticAt_complex_matrix_det {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {n : ℕ} {A : E → Matrix (Fin n) (Fin n) ℂ} {x : E}
    (hA : ∀ i j, AnalyticAt ℂ (fun z => A z i j) x) :
    AnalyticAt ℂ (fun z => (A z).det) x := by
  classical
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => hA (σ i) i)

theorem analytic_germ_matrix_rank_le_real_rank {n N d : ℕ}
    (f : Fin N → Fin d → (Fin n → ℂ) → ℂ)
    (hf : ∀ i j, AnalyticAt ℂ (f i j) 0)
    (B : Set (Fin n → ℝ)) (hB : B ∈ 𝓝 0) :
    ∃ x ∈ B, Matrix.rank (fun i j => meromorphicGermOf (f i j) (hf i j)) ≤
      Matrix.rank (fun i j => f i j (fun k => (x k : ℂ))) := by
  classical
  let A : Matrix (Fin N) (Fin d) (MeromorphicGermField (Fin n → ℂ)) :=
    fun i j => meromorphicGermOf (f i j) (hf i j)
  obtain ⟨ρ,σ,hminor⟩ := matrix_rank_nonzero_minor A
  by_contra hn
  push Not at hn
  apply hminor
  apply (meromorphicGerm_det_eq_zero_iff
    (fun i j => f (ρ i) (σ j)) (fun i j => hf (ρ i) (σ j))).mpr
  apply analytic_germ_zero_of_real_slice
    (analyticAt_complex_matrix_det (fun i j => hf (ρ i) (σ j)))
  filter_upwards [hB] with x hx
  by_contra hne
  have hl := Matrix.rank_submatrix_le
    (A := (fun i j => f i j (fun k => (x k : ℂ)) : Matrix (Fin N) (Fin d) ℂ)) ρ σ
  have hr := Matrix.rank_of_det_ne_zero hne
  rw [Fintype.card_fin] at hr
  change Matrix.rank (fun i j => f (ρ i) (σ j) (fun k => (x k : ℂ))) ≤ _ at hl
  rw [hr] at hl
  exact (not_le_of_gt (hn x hx)) hl

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_Vector
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric

open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Complexify
variable {d j : ℕ}

lemma monomial_apply (σ : Fin j → Fin d) (x : Fin j → Fin d → ℂ) :
    monomial σ x = ∏ i, x i (σ i) := by
  simp [monomial,ContinuousMultilinearMap.mkPiAlgebraFin_apply,List.prod_ofFn]

lemma monomial_norm_le (σ : Fin j → Fin d) : ‖monomial σ‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
  intro x
  rw [monomial_apply,one_mul]
  exact (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    (fun i _ => norm_le_pi_norm (x i) (σ i)))

lemma coefficient_norm_le (p : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ) :
    ‖coefficient p‖ ≤ (d : ℝ)^j * ‖p‖ := by
  classical
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : Fin j → Fin d, ‖p‖ := by
      apply Finset.sum_le_sum
      intro σ _
      rw [norm_smul]
      exact (mul_le_mul (p.unit_le_opNorm ((pi_norm_le_iff_of_nonneg zero_le_one).mpr (by
        intro i
        exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by
          intro k
          by_cases h : k = σ i <;> simp [h]))))
        (monomial_norm_le σ) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
    _ = _ := by simp

lemma coordinate_expansion
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ)
    (x : Fin j → Fin d → ℝ) :
    p x = ∑ σ : Fin j → Fin d, p (fun i => Pi.single (σ i) 1) * ∏ i, x i (σ i) := by
  classical
  have hx : x = fun i => ∑ k : Fin d, x i k • Pi.single k 1 := by
    funext i l
    simp [Finset.sum_apply,Pi.single_apply]
  conv_lhs => rw [hx,p.map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [p.map_smul_univ]
  simp only [smul_eq_mul,mul_comm]

lemma coefficient_real
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ)
    (x : Fin j → Fin d → ℝ) :
    coefficient p (fun i k => (x i k : ℂ)) = (p x : ℂ) := by
  classical
  rw [coordinate_expansion]
  simp only [coefficient, sum_apply,smul_apply,monomial_apply,Complex.real_smul,
    Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_prod]

lemma radius_lower_bound (p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ)
    {r : ℝ≥0} (hr : (r : ℝ≥0∞) < p.radius) :
    (r / (d+1 : ℝ≥0) : ℝ≥0) ≤ (series p).radius := by
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  apply (p.summable_norm_mul_pow hr).of_nonneg_of_le
  · intro j; positivity
  · intro j
    have hd : (0 : ℝ) < d+1 := by positivity
    have hd' : (d : ℝ)/(d+1) ≤ 1 := (div_le_one hd).mpr (by linarith)
    calc
      _ ≤ ((d : ℝ)^j*‖p j‖) * ((r : ℝ)/(d+1))^j := by
        exact mul_le_mul_of_nonneg_right (coefficient_norm_le (p j)) (by positivity)
      _ = ‖p j‖ * (r : ℝ)^j * ((d : ℝ)/(d+1))^j := by rw [div_pow,div_pow]; ring
      _ ≤ ‖p j‖ * (r : ℝ)^j * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) hd') (by positivity)
      _ = _ := mul_one _

lemma radius_pos (p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ)
    (hp : 0 < p.radius) : 0 < (series p).radius := by
  obtain ⟨r,hr0,hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp
  apply lt_of_lt_of_le _ (radius_lower_bound p hr)
  exact ENNReal.coe_pos.mpr (div_pos (ENNReal.coe_pos.mp hr0) (by positivity))

lemma norm_real_vector (x : Fin d → ℝ) : ‖fun i => (x i : ℂ)‖ = ‖x‖ := by
  simp only [Pi.norm_def,Complex.nnnorm_real]

lemma series_real {f : (Fin d → ℝ) → ℝ}
    {p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ} {R : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p 0 R) {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < R) {x : Fin d → ℝ} (hx : ‖x‖ < (r : ℝ)/(d+1)) :
    (series p).sum (fun i => (x i : ℂ)) = (f x : ℂ) := by
  have hp : 0 < (series p).radius := radius_pos p hf.radius_pos
  have hxq : (fun i => (x i : ℂ)) ∈ Metric.eball 0 (series p).radius := by
    apply Metric.eball_subset_eball (radius_lower_bound p (hr.trans_le hf.r_le))
    rw [Metric.eball_coe,Metric.mem_ball,dist_zero_right,norm_real_vector]
    simpa only [NNReal.coe_div,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using hx
  have hxp : x ∈ Metric.eball 0 R := by
    apply Metric.eball_subset_eball hr.le
    rw [Metric.eball_coe,Metric.mem_ball,dist_zero_right]
    exact hx.trans_le (div_le_self (by positivity) (le_add_of_nonneg_left (Nat.cast_nonneg d)))
  have H := Complex.ofRealCLM.hasSum (hf.hasSum hxp)
  have Hq := ((series p).hasFPowerSeriesOnBall hp).hasSum hxq
  simp only [zero_add] at H Hq
  simp only [series,coefficient_real] at Hq
  exact Hq.unique H

theorem scalar {f : (Fin d → ℝ) → ℝ} (hf : AnalyticAt ℝ f 0) :
    ∃ g : (Fin d → ℂ) → ℂ, AnalyticAt ℂ g 0 ∧
      ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), g (fun i => (x i : ℂ)) = (f x : ℂ) := by
  obtain ⟨p,R,hp⟩ := hf
  obtain ⟨r,hr0,hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  refine ⟨(series p).sum,((series p).hasFPowerSeriesOnBall (radius_pos p hp.radius_pos)).analyticAt,?_⟩
  have he : 0 < (r : ℝ)/(d+1) := div_pos (ENNReal.coe_pos.mp hr0) (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : Fin d → ℝ) he] with x hx
  exact series_real hp hr (by simpa only [Metric.mem_ball,dist_zero_right] using hx)

end Release061.Complexify

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticZeroNull
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter MeasureTheory
open scoped Topology

theorem analytic_real_zero_null {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set ℝ} (hU : MeasurableSet U) (hc : IsPreconnected U)
    {f : ℝ → F} (hf : AnalyticOnNhd ℝ f U) {p : ℝ} (hp : p ∈ U) (hne : f p ≠ 0) :
    volume {x | x ∈ U ∧ f x = 0} = 0 := by
  have ha := hf.eqOn_zero_or_eventually_ne_zero_of_preconnected hc
  rcases ha with ha | ha
  · exact (hne (ha hp)).elim
  · have hb := ae_restrict_le_codiscreteWithin (μ := volume) hU ha
    have hd := (ae_restrict_iff' hU).mp hb
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hd] with x hx
    exact fun h => hx h.1 h.2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem radialPlane_analytic (p : E × ℝ) (q : E × ℝ) : AnalyticAt ℝ (radialPlane p) q := by
  exact analyticAt_const.add ((analyticAt_snd.smul analyticAt_fst).prod analyticAt_snd)

theorem radialLine_analytic (p : E × ℝ) (y : E) (t : ℝ) : AnalyticAt ℝ (radialLine p y) t := by
  exact (radialPlane_analytic p (y,t)).comp (analyticAt_const.prod analyticAt_id)

theorem analytic_zero_null_convex [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {U : Set (E × ℝ)} (hU : IsOpen U) (hc : Convex ℝ U)
    {f : E × ℝ → F} (hf : AnalyticOnNhd ℝ f U)
    {p : E × ℝ} (hp : p ∈ U) (hne : f p ≠ 0) :
    (μ.prod volume) {x | x ∈ U ∧ f x = 0} = 0 := by
  classical
  let Z : Set (E × ℝ) := {x | x ∈ U ∧ f x = 0}
  have hZ : MeasurableSet Z := by
    have hm : Measurable (U.piecewise f (fun _ => 0)) :=
      hf.continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
    convert hU.measurableSet.inter ((measurableSet_singleton (0 : F)).preimage hm) using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    by_cases hx : x ∈ U <;> simp [Z,hx]
  have hr : Continuous (radialPlane p) := continuous_iff_continuousAt.mpr fun q => (radialPlane_analytic p q).continuousAt
  have hn : (μ.prod volume) (radialPlane p ⁻¹' Z) = 0 := by
    apply Measure.measure_prod_null_of_ae_null (hZ.preimage hr.measurable)
    apply Eventually.of_forall
    intro y
    let I : Set ℝ := radialLine p y ⁻¹' U
    have hI : IsOpen I := hU.preimage (continuous_iff_continuousAt.mpr fun t => (radialLine_analytic p y t).continuousAt)
    have hr0 : radialLine p y 0 = p := by
      change p + ((0 : ℝ) • y,(0 : ℝ)) = p
      rw [zero_smul]
      exact add_zero p
    have h0 : (0 : ℝ) ∈ I := by change radialLine p y 0 ∈ U; simpa only [hr0] using hp
    have hf0 : f (radialLine p y 0) ≠ 0 := by simpa only [hr0] using hne
    exact analytic_real_zero_null hI.measurableSet (hc.affine_preimage (radialLine p y)).isPreconnected
      (fun t ht => (hf _ ht).comp (radialLine_analytic p y t)) h0 hf0
  have himg := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (μ.prod volume) (s := radialPlane p ⁻¹' Z)
    (fun q _ => (radialPlane_analytic p q).differentiableAt.differentiableWithinAt) hn
  have hplane : (μ.prod volume) (Set.univ ×ˢ {p.2}) = 0 := by
    rw [Measure.prod_prod,measure_singleton,mul_zero]
  apply measure_mono_null (t := radialPlane p '' (radialPlane p ⁻¹' Z) ∪ (Set.univ ×ˢ {p.2}))
      _ (measure_union_null himg hplane)
  intro x hx
  by_cases ht : x.2 = p.2
  · exact Or.inr ⟨mem_univ _,ht⟩
  · left
    let q : E × ℝ := ((x.2-p.2)⁻¹ • (x.1-p.1),x.2-p.2)
    have hq : radialPlane p q = x := by
      ext
      · simp only [radialPlane,q,Prod.fst_add,smul_smul]
        rw [mul_inv_cancel₀ (sub_ne_zero.mpr ht),one_smul]
        abel
      · simp [radialPlane,q]
    exact ⟨q,by simpa only [mem_preimage,hq] using hx,hq⟩

theorem analytic_zero_null_connected [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {U : Set (E × ℝ)} (hU : IsOpen U) (hc : IsPreconnected U)
    {f : E × ℝ → F} (hf : AnalyticOnNhd ℝ f U)
    {p : E × ℝ} (hp : p ∈ U) (hne : f p ≠ 0) :
    (μ.prod volume) {x | x ∈ U ∧ f x = 0} = 0 := by
  classical
  have hball : ∀ x ∈ U, ∃ r > 0, Metric.ball x r ⊆ U := fun x hx =>
    Metric.isOpen_iff.mp hU x hx
  choose! r hr hsub using hball
  obtain ⟨T,hTU,hTc,hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (s := U) (f := fun x => Metric.ball x (r x))
    (fun x hx => mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x (hr x hx)))
  have hn : ∀ x ∈ T, (μ.prod volume) {y | y ∈ Metric.ball x (r x) ∧ f y = 0} = 0 := by
    intro x hx
    have hxu := hTU hx
    have he : ∃ y ∈ Metric.ball x (r x), f y ≠ 0 := by
      by_contra! he
      have hz : f =ᶠ[𝓝 x] 0 := by
        filter_upwards [Metric.ball_mem_nhds x (hr x hxu)] with y hy
        exact he y hy
      exact hne (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hxu hz hp)
    obtain ⟨y,hy,hfy⟩ := he
    exact analytic_zero_null_convex μ Metric.isOpen_ball (convex_ball x (r x))
      (hf.mono (hsub x hxu)) hy hfy
  apply measure_mono_null (t := ⋃ x ∈ T, {y | y ∈ Metric.ball x (r x) ∧ f y = 0})
    _ ((measure_biUnion_null_iff hTc).mpr hn)
  intro y hy
  obtain ⟨x,hx,hyx⟩ := mem_iUnion₂.mp (hcov hy.1)
  exact mem_iUnion₂.mpr ⟨x,hx,hyx,hy.2⟩

theorem analytic_zero_null [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {f : E → F} (hf : AnalyticOnNhd ℝ f U)
    {p : E} (hp : p ∈ U) (hne : f p ≠ 0) : μ {x | x ∈ U ∧ f x = 0} = 0 := by
  classical
  rcases subsingleton_or_nontrivial E with hs | hnt
  · have hz : {x | x ∈ U ∧ f x = 0} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hne ((congrArg f (Subsingleton.elim p x)).trans hx.2)
    rw [hz,measure_empty]
  · obtain ⟨n,hd⟩ := Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos (R := ℝ) (M := E)).ne'
    let e : E ≃L[ℝ] ((Fin n → ℝ) × ℝ) := ContinuousLinearEquiv.ofFinrankEq
      (by simpa [Module.finrank_prod,Module.finrank_pi_fintype,Nat.succ_eq_add_one] using hd)
    let U' := e.symm ⁻¹' U
    let f' := f ∘ e.symm
    have hf' : AnalyticOnNhd ℝ f' U' := fun x hx => (hf _ hx).comp (e.symm.analyticAt x)
    have hp' : e p ∈ U' := by simpa only [U',mem_preimage,e.symm_apply_apply] using hp
    have he : f' (e p) ≠ 0 := by simpa only [f',Function.comp_apply,e.symm_apply_apply] using hne
    have hU' : IsOpen U' := hU.preimage e.symm.continuous
    have hc' : IsPreconnected U' := e.symm.toHomeomorph.isPreconnected_preimage.mpr hc
    have hn := analytic_zero_null_connected (volume : Measure (Fin n → ℝ)) hU' hc' hf' hp' he
    let Z' := {x | x ∈ U' ∧ f' x = 0}
    have hZ' : MeasurableSet Z' := by
      have hm : Measurable (U'.piecewise f' (fun _ => 0)) :=
        hf'.continuousOn.measurable_piecewise continuousOn_const hU'.measurableSet
      convert hU'.measurableSet.inter ((measurableSet_singleton (0 : F)).preimage hm) using 1
      all_goals try with_reducible_and_instances rfl
      ext x
      by_cases hx : x ∈ U' <;> simp [Z',hx]
    have hae : ∀ᵐ q ∂(volume : Measure (Fin n → ℝ)).prod volume, q ∈ Z'ᶜ :=
      measure_eq_zero_iff_ae_notMem.mp hn
    have hat := (ae_comp_linearMap_mem_iff e.toLinearMap μ
      ((volume : Measure (Fin n → ℝ)).prod volume) e.surjective hZ'.compl).mpr hae
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hat] with x hx
    have hx' : e x ∈ Z'ᶜ := hx
    simpa [Z',U',f'] using hx'

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CenteredChartGerms
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

theorem Biholomorph.centered_chart_germs {n m : ℕ} {V W : Set (Affine n)}
    {B : Set (Affine m)} (e : Biholomorph W B) (hWV : W ⊆ V)
    (hW : IsOpen ((Subtype.val : V → Affine n) ⁻¹' W)) (hB : IsOpen B)
    {q : Affine n} (hq : q ∈ W) :
    ∃ (F : Affine m → Affine n) (G : Affine n → Affine m),
      F 0 = q ∧ AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ G q ∧
      (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id ∧
      (∀ᶠ y in 𝓝[V] q, F (G y) = y) ∧
      (∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ V) := by
  let b : Affine m := (e.toHomeomorph ⟨q,hq⟩).val
  have hb : b ∈ B := (e.toHomeomorph ⟨q,hq⟩).property
  let f := ambientExtend (fun y : B => (e.toHomeomorph.symm y).val)
  have hf : AnalyticOnNhd ℂ f B := e.holomorphic_invFun.analyticOnNhd_extend hB
  have hfb : f b = q := by
    rw [show f b = (e.toHomeomorph.symm (e.toHomeomorph ⟨q,hq⟩)).val from ambientExtend_apply _ _]
    simp
  obtain ⟨O,hO,hqO,g,hg,hge⟩ := e.holomorphic_toFun ⟨q,hq⟩
  let F : Affine m → Affine n := fun z => f (z+b)
  let G : Affine n → Affine m := fun y => g y-b
  have hF0 : F 0 = q := by simpa only [F,zero_add] using hfb
  have hF : AnalyticAt ℂ F 0 := by
    have htr : AnalyticAt ℂ (fun z : Affine m => z+b) 0 := analyticAt_id.add analyticAt_const
    have hf' : AnalyticAt ℂ f (0+b) := by simpa only [zero_add] using hf b hb
    exact hf'.comp (f := fun z : Affine m => z+b) (x := 0) htr
  have hG : AnalyticAt ℂ G q := (hg q hqO).sub analyticAt_const
  refine ⟨F,G,hF0,hF,hG,?_,?_,?_⟩
  · have hzB : ∀ᶠ z in 𝓝 (0 : Affine m), z+b ∈ B :=
      ((continuous_id.add continuous_const).continuousAt (x := (0 : Affine m))).preimage_mem_nhds
        (by simpa using hB.mem_nhds hb)
    have hzO : ∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ O :=
      hF.continuousAt.preimage_mem_nhds (by simpa only [hF0] using hO.mem_nhds hqO)
    filter_upwards [hzB,hzO] with z hz hz'
    have hfy : f (z+b) = (e.toHomeomorph.symm ⟨z+b,hz⟩).val := ambientExtend_apply (fun y : B => (e.toHomeomorph.symm y).val) ⟨z+b,hz⟩
    have hfw : F z ∈ W := by rw [show F z = f (z+b) from rfl,hfy]; exact (e.toHomeomorph.symm ⟨z+b,hz⟩).property
    have he : g (F z) = z+b := by
      rw [hge ⟨F z,hfw⟩ hz']
      have heq : (⟨F z,hfw⟩ : W) = e.toHomeomorph.symm ⟨z+b,hz⟩ := Subtype.ext hfy
      rw [heq]
      exact congrArg Subtype.val (e.toHomeomorph.apply_symm_apply ⟨z+b,hz⟩)
    change g (F z)-b = z
    rw [he,add_sub_cancel_right]
  · obtain ⟨O',hO',hWO'⟩ := isOpen_induced_iff.mp hW
    have hqO' : q ∈ O' := by
      have hh : (⟨q,hWV hq⟩ : V) ∈ (Subtype.val : V → Affine n) ⁻¹' W := hq
      rwa [← hWO'] at hh
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hO'.mem_nhds hqO'),
      mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hqO)] with y hyV hyO' hyO
    have hyW : y ∈ W := by
      have hh : (⟨y,hyV⟩ : V) ∈ (Subtype.val : V → Affine n) ⁻¹' O' := hyO'
      rwa [hWO'] at hh
    have hgy := hge ⟨y,hyW⟩ hyO
    change f (g y-b+b) = y
    rw [sub_add_cancel,hgy]
    rw [show f (e.toHomeomorph ⟨y,hyW⟩).val =
      (e.toHomeomorph.symm (e.toHomeomorph ⟨y,hyW⟩)).val from ambientExtend_apply _ _]
    simp
  · have hzB : ∀ᶠ z in 𝓝 (0 : Affine m), z+b ∈ B :=
      ((continuous_id.add continuous_const).continuousAt (x := (0 : Affine m))).preimage_mem_nhds
        (by simpa using hB.mem_nhds hb)
    filter_upwards [hzB] with z hz
    change f (z+b) ∈ V
    rw [show f (z+b) = (e.toHomeomorph.symm ⟨z+b,hz⟩).val from ambientExtend_apply (fun y : B => (e.toHomeomorph.symm y).val) ⟨z+b,hz⟩]
    exact hWV (e.toHomeomorph.symm ⟨z+b,hz⟩).property

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ChartDimensionLeCoordinate
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Algebra

theorem trdeg_ge_of_polynomial_local_retraction {m N : ℕ}
    (V : Set (Fin N → ℂ)) (F : (Fin m → ℂ) → (Fin N → ℂ))
    (hF : AnalyticAt ℂ F 0)
    (hFV : ∀ᶠ z in 𝓝 (0 : Fin m → ℂ), F z ∈ V)
    (R : Fin m → MvPolynomial (Fin N) ℂ)
    (hR : (fun z i => MvPolynomial.eval (F z) (R i)) =ᶠ[𝓝 (0 : Fin m → ℂ)] id) :
    (m : Cardinal) ≤ Algebra.trdeg ℂ
      (MvPolynomial (Fin N) ℂ ⧸ MvPolynomial.vanishingIdeal ℂ V) := by
  classical
  let I := MvPolynomial.vanishingIdeal ℂ V
  let Q := MvPolynomial (Fin N) ℂ ⧸ I
  let f : Fin N → (Fin m → ℂ) → ℂ := fun j z => F z j
  have hf (j : Fin N) : AnalyticAt ℂ (f j) 0 :=
    ((ContinuousLinearMap.proj j : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _).comp hF
  let a : Fin N → AnalyticGerm (Fin m → ℂ) := fun j => analyticGermOf _ (f j) (hf j)
  have haI : ∀ P ∈ I, MvPolynomial.aeval a P = 0 := by
    intro P hP
    apply Subtype.ext
    rw [analyticGerm_aeval f hf P]
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hFV] with z hz
    exact MvPolynomial.mem_vanishingIdeal_iff.mp hP _ hz
  let ρ : Q →ₐ[ℂ] AnalyticGerm (Fin m → ℂ) :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval a) haI
  let x : Fin m → Q := fun i => Ideal.Quotient.mkₐ ℂ I (R i)
  have he : ρ ∘ x = analyticCoordinate := by
    funext i
    change MvPolynomial.aeval a (R i) = analyticCoordinate i
    apply Subtype.ext
    rw [analyticGerm_aeval f hf (R i)]
    apply Filter.Germ.coe_eq.mpr
    exact hR.mono fun z hz => congrFun hz i
  have hx : AlgebraicIndependent ℂ x := AlgebraicIndependent.of_comp ρ
    (he.symm ▸ algebraicIndependent_analyticCoordinate)
  simpa only [Cardinal.mk_fintype,Fintype.card_fin] using hx.cardinalMk_le_trdeg

theorem linearCoordinatePolynomial_eval {m N : ℕ}
    (L : (Fin N → ℂ) →L[ℂ] (Fin m → ℂ)) (i : Fin m) (z : Fin N → ℂ) :
    MvPolynomial.eval z (linearCoordinatePolynomial L i) = L z i := by
  classical
  have hz : z = ∑ j : Fin N, z j • Pi.single j (1 : ℂ) := by
    ext k
    simp [Pi.single_apply]
  simp only [linearCoordinatePolynomial,map_sum,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X]
  conv_rhs => rw [hz]
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem trdeg_ge_of_analytic_immersion {m N : ℕ}
    (V : Set (Fin N → ℂ)) (F : (Fin m → ℂ) → (Fin N → ℂ))
    (hF : AnalyticAt ℂ F 0)
    (hFV : ∀ᶠ z in 𝓝 (0 : Fin m → ℂ), F z ∈ V)
    (L : (Fin N → ℂ) →L[ℂ] (Fin m → ℂ))
    (hL : L.comp (fderiv ℂ F 0) = ContinuousLinearMap.id ℂ (Fin m → ℂ)) :
    (m : Cardinal) ≤ Algebra.trdeg ℂ
      (MvPolynomial (Fin N) ℂ ⧸ MvPolynomial.vanishingIdeal ℂ V) := by
  let g : (Fin m → ℂ) → (Fin m → ℂ) := fun z => L (F z) - L (F 0)
  have hg : AnalyticAt ℂ g 0 := ((L.analyticAt _).comp hF).sub analyticAt_const
  have hg0 : g 0 = 0 := sub_self _
  have hgd : HasFDerivAt g (ContinuousLinearEquiv.refl ℂ (Fin m → ℂ) :
      (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) 0 := by
    simpa only [g,Function.comp_def,hL,ContinuousLinearEquiv.coe_refl] using
      ((L.hasFDerivAt.comp 0 hF.differentiableAt.hasFDerivAt).sub_const (L (F 0)))
  obtain ⟨e,he,h0,hea⟩ := analytic_local_inverse hg (ContinuousLinearEquiv.refl ℂ (Fin m → ℂ)) hgd
  have hinv0 : e.symm 0 = 0 := by
    have hh := e.left_inv h0
    rwa [show e 0 = 0 from by rw [he]; exact hg0] at hh
  have hea0 : AnalyticAt ℂ e.symm 0 := hg0 ▸ hea
  have ht : Tendsto e.symm (𝓝 (0 : Fin m → ℂ)) (𝓝 0) := by
    simpa only [ContinuousAt,hinv0] using hea0.continuousAt
  have hF' : AnalyticAt ℂ (F ∘ e.symm) 0 :=
    (hinv0.symm ▸ hF).comp hea0
  have h0t : (0 : Fin m → ℂ) ∈ e.target := by
    have hh := e.map_source h0
    rwa [show e 0 = 0 from by rw [he]; exact hg0] at hh
  let R : Fin m → MvPolynomial (Fin N) ℂ := fun i =>
    linearCoordinatePolynomial L i - MvPolynomial.C (L (F 0) i)
  apply trdeg_ge_of_polynomial_local_retraction V (F ∘ e.symm) hF' (ht hFV) R
  filter_upwards [e.open_target.mem_nhds h0t] with z hz
  funext i
  have hh := congrFun (e.right_inv hz) i
  rw [he] at hh
  simpa only [R,Function.comp_apply,map_sub,linearCoordinatePolynomial_eval,MvPolynomial.eval_C,
    g,Pi.sub_apply,Function.id_def] using hh

theorem chart_dimension_le_coordinate_trdeg {m N : ℕ}
    (V : Set (Fin N → ℂ)) (F : (Fin m → ℂ) → (Fin N → ℂ))
    (G : (Fin N → ℂ) → (Fin m → ℂ))
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (F 0))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Fin m → ℂ)] id)
    (hFV : ∀ᶠ z in 𝓝 (0 : Fin m → ℂ), F z ∈ V) :
    (m : Cardinal) ≤ Algebra.trdeg ℂ
      (MvPolynomial (Fin N) ℂ ⧸ MvPolynomial.vanishingIdeal ℂ V) := by
  apply trdeg_ge_of_analytic_immersion V F hF hFV (fderiv ℂ G (F 0))
  have hcomp := hG.differentiableAt.hasFDerivAt.comp 0 hF.differentiableAt.hasFDerivAt
  have hid := hcomp.congr_of_eventuallyEq hGF.symm
  exact hid.unique (hasFDerivAt_id 0)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ComplexTangentRankAlternative
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set MeasureTheory _root_.Module
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem analyticAt_matrix_det {n : ℕ} {A : E → Matrix (Fin n) (Fin n) ℂ} {x : E}
    (ha : ∀ i j, AnalyticAt ℝ (fun y => A y i j) x) :
    AnalyticAt ℝ (fun y => (A y).det) x := by
  classical
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => ha (σ i) i)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ComplexificationRankLeReal
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Matrix _root_.Module _root_.Matrix.Module

theorem complexification_real_partial {n : ℕ}
    (f : (Fin n → ℂ) → ℂ) (q : (Fin n → ℝ) → ℂ)
    (hf : AnalyticAt ℂ f 0)
    (hext : (fun x : Fin n → ℝ => f (fun i => (x i : ℂ))) =ᶠ[𝓝 0] q) :
    ∀ᶠ x in 𝓝 (0 : Fin n → ℝ), ∀ i : Fin n,
      fderiv ℂ f (fun j => (x j : ℂ)) (Pi.single i 1) =
        fderiv ℝ q x (Pi.single i 1) := by
  have he : Filter.Tendsto (Flatten.realEmbedding n) (𝓝 0) (𝓝 0) := by
    have he := (Flatten.realEmbedding n).continuous.continuousAt (x := 0)
    rw [ContinuousAt,map_zero] at he
    exact he
  have hqeq : (fun x => f (Flatten.realEmbedding n x)) =ᶠ[𝓝 0] q := hext
  filter_upwards [he hf.eventually_analyticAt, hqeq.fderiv (𝕜 := ℝ)] with x hfx hx
  intro i
  have hd := (hfx.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp x
    (Flatten.realEmbedding n).hasFDerivAt
  have hsingle : Flatten.realEmbedding n (Pi.single i 1) = Pi.single i (1 : ℂ) := by
    ext j
    by_cases hji : j = i <;> simp [Flatten.realEmbedding,hji]
  have hv := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℂ => L (Pi.single i 1))
    (hd.fderiv.symm.trans hx)
  change fderiv ℂ f (Flatten.realEmbedding n x) (Flatten.realEmbedding n (Pi.single i 1)) = _ at hv
  rw [hsingle] at hv
  exact hv

theorem complexification_rank_le_real_rank {n N : ℕ}
    (f : Fin N → (Fin n → ℂ) → ℂ) (hf : ∀ j, AnalyticAt ℂ (f j) 0)
    (q : (Fin n → ℝ) → Fin N → ℂ)
    (hext : (fun (x : Fin n → ℝ) j => f j (fun i => (x i : ℂ))) =ᶠ[𝓝 0] q)
    (B : Set (Fin n → ℝ)) (hB : B ∈ 𝓝 0) :
    ∃ x ∈ B, Matrix.rank (fun j i => meromorphicPartial i (meromorphicGermOf (f j) (hf j))) ≤
      Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)) := by
  have he : ∀ j, ∀ᶠ x in 𝓝 (0 : Fin n → ℝ), ∀ i : Fin n,
      fderiv ℂ (f j) (fun k => (x k : ℂ)) (Pi.single i 1) =
        fderiv ℝ (fun y => q y j) x (Pi.single i 1) := by
    intro j
    apply complexification_real_partial (f j) (fun y => q y j) (hf j)
    exact hext.mono fun x hx => congrFun hx j
  let C := B ∩ {x | ∀ j i, fderiv ℂ (f j) (fun k => (x k : ℂ)) (Pi.single i 1) =
    fderiv ℝ (fun y => q y j) x (Pi.single i 1)}
  have hC : C ∈ 𝓝 0 := inter_mem hB (Filter.eventually_all.mpr he)
  obtain ⟨x,hx,hr⟩ := analytic_germ_matrix_rank_le_real_rank
    (fun j i z => fderiv ℂ (f j) z (Pi.single i 1))
    (fun j i => ((ContinuousLinearMap.apply ℂ ℂ (Pi.single i (1 : ℂ) : Fin n → ℂ)).analyticAt _).comp (hf j).fderiv)
    C hC
  refine ⟨x,hx.1,?_⟩
  simp only [meromorphicPartial_germ]
  have heq : (fun j i => fderiv ℂ (f j) (fun k => (x k : ℂ)) (Pi.single i 1)) =
      (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)) :=
    funext fun j => funext (hx.2 j)
  exact hr.trans_eq (congrArg (fun M : Matrix (Fin N) (Fin n) ℂ => M.rank) heq)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NashParametrizationExtension
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology

theorem real_analytic_semialgebraic_nash_extension {n : ℕ}
    (B : Set (Fin n → ℝ)) (hB : B ∈ 𝓝 0)
    (f : (Fin n → ℝ) → ℝ) (hf : AnalyticAt ℝ f 0)
    (hgraph : PolynomialSignSet (id : (Option (Fin n) → ℝ) → (Option (Fin n) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = f (fun i => x (some i))}) :
    ∃ F : (Fin n → ℂ) → ℂ, ∃ hF : AnalyticAt ℂ F 0,
      ((fun x : Fin n → ℝ => F (fun i => (x i : ℂ))) =ᶠ[𝓝 0] fun x => (f x : ℂ)) ∧
      IsAlgebraic (IntermediateField.adjoin ℂ (range (meromorphicCoordinate (n := n))))
        (meromorphicGermOf F hF) := by
  obtain ⟨F,hF,hext⟩ := Complexify.scalar hf
  exact ⟨F,hF,hext,analytic_extension_of_semialgebraic_isAlgebraic B hB f F hF hext hgraph⟩

theorem meromorphicGermOf_add_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g : E → ℂ) (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (c : ℂ) :
    meromorphicGermOf (fun z => f z + c * g z) (hf.add (analyticAt_const.mul hg)) =
      meromorphicGermOf f hf + algebraMap ℂ (MeromorphicGermField E) c * meromorphicGermOf g hg := by
  have h : analyticGermOf E (fun z => f z + c * g z) (hf.add (analyticAt_const.mul hg)) =
      analyticGermOf E f hf + algebraMap ℂ (AnalyticGerm E) c * analyticGermOf E g hg := by
    apply Subtype.ext
    rfl
  simp only [meromorphicGermOf,h,map_add,map_mul,← IsScalarTower.algebraMap_apply]

theorem complex_valued_nash_extension {n : ℕ}
    (B : Set (Fin n → ℝ)) (hB : B ∈ 𝓝 0)
    (q : (Fin n → ℝ) → ℂ) (hq : AnalyticAt ℝ q 0)
    (hre : PolynomialSignSet (id : (Option (Fin n) → ℝ) → (Option (Fin n) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = (q (fun i => x (some i))).re})
    (him : PolynomialSignSet (id : (Option (Fin n) → ℝ) → (Option (Fin n) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = (q (fun i => x (some i))).im}) :
    ∃ F : (Fin n → ℂ) → ℂ, ∃ hF : AnalyticAt ℂ F 0,
      ((fun x : Fin n → ℝ => F (fun i => (x i : ℂ))) =ᶠ[𝓝 0] q) ∧
      IsAlgebraic (IntermediateField.adjoin ℂ (range (meromorphicCoordinate (n := n))))
        (meromorphicGermOf F hF) := by
  obtain ⟨f,hf,he,ha⟩ := real_analytic_semialgebraic_nash_extension B hB
    (fun x => (q x).re) ((Complex.reCLM.analyticAt _).comp hq) hre
  obtain ⟨g,hg,he',ha'⟩ := real_analytic_semialgebraic_nash_extension B hB
    (fun x => (q x).im) ((Complex.imCLM.analyticAt _).comp hq) him
  refine ⟨fun z => f z + Complex.I * g z,hf.add (analyticAt_const.mul hg),?_,?_⟩
  · filter_upwards [he,he'] with x hx hx'
    rw [hx,hx',mul_comm]
    exact Complex.re_add_im (q x)
  · rw [meromorphicGermOf_add_mul f g hf hg Complex.I]
    apply ha.add (IsAlgebraic.mul ?_ ha')
    let L := IntermediateField.adjoin ℂ (range (meromorphicCoordinate (n := n)))
    have hc := isAlgebraic_algebraMap (A := MeromorphicGermField (Fin n → ℂ))
      (algebraMap ℂ L Complex.I)
    simpa only [← IsScalarTower.algebraMap_apply] using hc

theorem nash_parametrization_extension {n N : ℕ}
    (B : Set (Fin n → ℝ)) (hB : B ∈ 𝓝 0)
    (q : (Fin n → ℝ) → Fin N → ℂ) (hq : AnalyticAt ℝ q 0)
    (hre : ∀ j, PolynomialSignSet (id : (Option (Fin n) → ℝ) → (Option (Fin n) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = (q (fun i => x (some i)) j).re})
    (him : ∀ j, PolynomialSignSet (id : (Option (Fin n) → ℝ) → (Option (Fin n) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = (q (fun i => x (some i)) j).im}) :
    ∃ F : Fin N → (Fin n → ℂ) → ℂ, ∃ hF : ∀ j, AnalyticAt ℂ (F j) 0,
      ((fun (x : Fin n → ℝ) j => F j (fun i => (x i : ℂ))) =ᶠ[𝓝 0] q) ∧
      ∀ j, IsAlgebraic (IntermediateField.adjoin ℂ (range (meromorphicCoordinate (n := n))))
        (meromorphicGermOf (F j) (hF j)) := by
  have hqj := analyticAt_pi_iff.mp hq
  choose F hF he ha using fun j => complex_valued_nash_extension B hB
    (fun x => q x j) (hqj j) (hre j) (him j)
  refine ⟨F,hF,?_,ha⟩
  filter_upwards [Filter.eventually_all.mpr he] with x hx
  exact funext hx

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialRelationPropagates
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Algebra

theorem new_polynomial_relation_of_trdeg_lt {R F κ : Type}
    [Field R] [Field F] [Algebra R F]
    (I : Ideal (MvPolynomial κ R)) (q : κ → F)
    (hIq : ∀ P ∈ I, MvPolynomial.aeval q P = 0)
    (hlt : Algebra.trdeg R (IntermediateField.adjoin R (range q)) <
      Algebra.trdeg R (MvPolynomial κ R ⧸ I)) :
    ∃ P : MvPolynomial κ R, P ∉ I ∧ MvPolynomial.aeval q P = 0 := by
  classical
  by_contra hn
  push Not at hn
  let L := IntermediateField.adjoin R (range q)
  let qL : κ → L := fun j => ⟨q j,IntermediateField.subset_adjoin _ _ (mem_range_self j)⟩
  have heval (P : MvPolynomial κ R) : (MvPolynomial.aeval qL P : F) = MvPolynomial.aeval q P := by
    exact MvPolynomial.comp_aeval_apply qL L.val P
  let g : (MvPolynomial κ R ⧸ I) →ₐ[R] L := Ideal.Quotient.liftₐ I
    (MvPolynomial.aeval qL) (fun P hP => by
      apply Subtype.ext
      simpa only [heval,ZeroMemClass.coe_zero] using hIq P hP)
  have hginj : Function.Injective g := by
    apply (injective_iff_map_eq_zero g).mpr
    intro a ha
    obtain ⟨P,rfl⟩ := Ideal.Quotient.mkₐ_surjective R I a
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    by_contra hP
    apply hn P hP
    have hval := congrArg (fun a : L => (a : F)) ha
    change (MvPolynomial.aeval qL P : F) = 0 at hval
    rwa [heval] at hval
  exact (not_le_of_gt hlt) (trdeg_le_of_injective g hginj)

theorem polynomial_relation_propagates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {N : ℕ} {B : Set E} (hB : IsPreconnected B)
    (q : E → Fin N → ℂ) (hq : AnalyticOnNhd ℝ q B)
    (P : MvPolynomial (Fin N) ℂ) {x : E} (hx : x ∈ B)
    (hzero : (fun y => MvPolynomial.eval (q y) P) =ᶠ[𝓝 x] 0) :
    ∀ y ∈ B, MvPolynomial.eval (q y) P = 0 := by
  have hA : AnalyticOnNhd ℝ (fun y => MvPolynomial.eval (q y) P) B := by
    intro y hy
    exact (((AnalyticOnNhd.eval_mvPolynomial P) (q y) (mem_univ _)).restrictScalars (𝕜 := ℝ)).comp (hq y hy)
  exact hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hB hx hzero

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NashCellLowRank
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology

theorem nash_cell_low_rank_proper_relation {n N : ℕ}
    (V : Set (Fin N → ℂ))
    (B : Set (Fin n → ℝ)) (hBo : IsOpen B) (hB : IsPreconnected B) (h0 : 0 ∈ B)
    (q : (Fin n → ℝ) → Fin N → ℂ) (hq : AnalyticOnNhd ℝ q B)
    (hqV : ∀ x ∈ B, q x ∈ V)
    (hre : ∀ j, PolynomialSignSet (id : (Option (Fin n) → ℝ) → (Option (Fin n) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = (q (fun i => x (some i)) j).re})
    (him : ∀ j, PolynomialSignSet (id : (Option (Fin n) → ℝ) → (Option (Fin n) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = (q (fun i => x (some i)) j).im})
    (hrank : ∀ x ∈ B,
      (Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)) : Cardinal) <
      Algebra.trdeg ℂ (MvPolynomial (Fin N) ℂ ⧸ MvPolynomial.vanishingIdeal ℂ V)) :
    ∃ P : MvPolynomial (Fin N) ℂ, (∃ y ∈ V, MvPolynomial.eval y P ≠ 0) ∧
      ∀ x ∈ B, MvPolynomial.eval (q x) P = 0 := by
  classical
  obtain ⟨f,hf,hext,halg⟩ := nash_parametrization_extension B (hBo.mem_nhds h0)
    q (hq 0 h0) hre him
  obtain ⟨x,hx,hr⟩ := complexification_rank_le_real_rank f hf q hext B (hBo.mem_nhds h0)
  let A : Matrix (Fin N) (Fin n) (MeromorphicGermField (Fin n → ℂ)) :=
    fun j i => meromorphicPartial i (meromorphicGermOf (f j) (hf j))
  have hr' : (A.rank : Cardinal) ≤
      (Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)) : Cardinal) := by
    exact_mod_cast hr
  have hgrank : (A.rank : Cardinal) = Algebra.trdeg ℂ
      (IntermediateField.adjoin ℂ (range (fun j => meromorphicGermOf (f j) (hf j)))) := by
    rw [Matrix.rank_eq_finrank_span_row,Module.finrank_eq_rank]
    exact analytic_nash_rank f hf halg
  have hlt := hr'.trans_lt (hrank x hx)
  rw [hgrank] at hlt
  have hIq : ∀ P ∈ MvPolynomial.vanishingIdeal ℂ V,
      MvPolynomial.aeval (fun j => meromorphicGermOf (f j) (hf j)) P = 0 := by
    intro P hP
    apply (meromorphicGerm_aeval_eq_zero_iff f hf P).mpr
    apply analytic_germ_zero_of_real_slice
      (((AnalyticOnNhd.eval_mvPolynomial P) _ (mem_univ _)).comp (analyticAt_pi_iff.mpr hf))
    filter_upwards [hext,hBo.mem_nhds h0] with y hy hyB
    change MvPolynomial.eval (fun j => f j (fun i => (y i : ℂ))) P = 0
    rw [hy]
    exact MvPolynomial.mem_vanishingIdeal_iff.mp hP _ (hqV y hyB)
  obtain ⟨P,hP,hzero⟩ := new_polynomial_relation_of_trdeg_lt
    (MvPolynomial.vanishingIdeal ℂ V) (fun j => meromorphicGermOf (f j) (hf j)) hIq hlt
  refine ⟨P,?_,?_⟩
  · simpa only [MvPolynomial.mem_vanishingIdeal_iff,not_forall,exists_prop,
      MvPolynomial.aeval_eq_eval] using hP
  · apply polynomial_relation_propagates hB q hq P h0
    have he : Tendsto (Flatten.realEmbedding n) (𝓝 0) (𝓝 0) := by
      have he := (Flatten.realEmbedding n).continuous.continuousAt (x := 0)
      rw [ContinuousAt,map_zero] at he
      exact he
    have hz := he ((meromorphicGerm_aeval_eq_zero_iff f hf P).mp hzero)
    filter_upwards [hz,hext] with y hy hy'
    change MvPolynomial.eval (fun j => f j (fun i => (y i : ℂ))) P = 0 at hy
    rwa [hy'] at hy

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NashCellIntrinsicRank
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem analytic_matrix_rank_ae_ge [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {m n : ℕ} {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {A : E → Matrix (Fin m) (Fin n) ℂ}
    (hA : ∀ i j, AnalyticOnNhd ℝ (fun x => A x i j) U)
    {p : E} (hp : p ∈ U) : μ {x | x ∈ U ∧ (A x).rank < (A p).rank} = 0 := by
  obtain ⟨ρ,σ,hminor⟩ := matrix_rank_nonzero_minor (A p)
  have ha : AnalyticOnNhd ℝ (fun x => ((A x).submatrix ρ σ).det) U := by
    intro x hx
    exact analyticAt_matrix_det (fun i j => hA (ρ i) (σ j) x hx)
  have hn := analytic_zero_null μ hU hc ha hp hminor
  apply measure_mono_null (t := {x | x ∈ U ∧ ((A x).submatrix ρ σ).det = 0}) _ hn
  intro x hx
  refine ⟨hx.1,?_⟩
  by_contra hne
  have hr : (A p).rank ≤ (A x).rank := by
    have hr := Matrix.rank_submatrix_le (A x) ρ σ
    rw [Matrix.rank_of_det_ne_zero hne] at hr
    simpa using hr
  exact (not_lt_of_ge hr) hx.2

theorem nash_cell_intrinsic_rank_dichotomy {d m N : ℕ}
    (V : Set (Fin N → ℂ))
    (F : (Fin m → ℂ) → (Fin N → ℂ)) (G : (Fin N → ℂ) → (Fin m → ℂ))
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (F 0))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Fin m → ℂ)] id)
    (hFV : ∀ᶠ z in 𝓝 (0 : Fin m → ℂ), F z ∈ V)
    (B : Set (Fin d → ℝ)) (hBo : IsOpen B) (hB : IsPreconnected B) (h0 : 0 ∈ B)
    (q : (Fin d → ℝ) → Fin N → ℂ) (hq : AnalyticOnNhd ℝ q B)
    (hqV : ∀ x ∈ B, q x ∈ V)
    (hre : ∀ j, PolynomialSignSet (id : (Option (Fin d) → ℝ) → (Option (Fin d) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = (q (fun i => x (some i)) j).re})
    (him : ∀ j, PolynomialSignSet (id : (Option (Fin d) → ℝ) → (Option (Fin d) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = (q (fun i => x (some i)) j).im}) :
    (∃ P : MvPolynomial (Fin N) ℂ, (∃ y ∈ V, MvPolynomial.eval y P ≠ 0) ∧
      ∀ x ∈ B, MvPolynomial.eval (q x) P = 0) ∨
    volume {x | x ∈ B ∧
      Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)) < m} = 0 := by
  classical
  let A : (Fin d → ℝ) → Matrix (Fin N) (Fin d) ℂ :=
    fun x j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)
  by_cases hlow : ∀ x ∈ B, (A x).rank < m
  · left
    apply nash_cell_low_rank_proper_relation V B hBo hB h0 q hq hqV hre him
    intro x hx
    have hm := chart_dimension_le_coordinate_trdeg V F G hF hG hGF hFV
    have hr : ((A x).rank : Cardinal) < (m : Cardinal) := by exact_mod_cast hlow x hx
    exact hr.trans_le hm
  · right
    push Not at hlow
    obtain ⟨p,hp,hrank⟩ := hlow
    have hA : ∀ j i, AnalyticOnNhd ℝ (fun x => A x j i) B := by
      intro j i x hx
      have hj : AnalyticAt ℝ (fun y => q y j) x :=
        ((ContinuousLinearMap.proj j : (Fin N → ℂ) →L[ℝ] ℂ).analyticAt _).comp (hq x hx)
      exact ((ContinuousLinearMap.apply ℝ ℂ (Pi.single i 1)).analyticAt _).comp hj.fderiv
    have hn := analytic_matrix_rank_ae_ge volume hBo hB hA hp
    apply measure_mono_null (t := {x | x ∈ B ∧ (A x).rank < (A p).rank}) _ hn
    intro x hx
    exact ⟨hx.1,lt_of_lt_of_le hx.2 hrank⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicBoundaryFiniteNash
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open SignElimination
open scoped Classical

namespace SemialgebraicOn
lemma coordinate_graph {ι κ : Type*} [Finite κ] {B : Set (ι → ℝ)} {f : (ι → ℝ) → (κ → ℝ)}
    (hf : SemialgebraicOn B f) (j : κ) :
    PolynomialSignSet (id : (Option ι → ℝ) → (Option ι → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = f (fun i => x (some i)) j} := by
  have hh := (hf.reindex (fun _ : Fin 1 => j)).coordinate_preimage
    (fun x : Option ι → ℝ => ((fun i => x (some i)),fun _ : Fin 1 => x none))
    (Sum.elim some (fun _ => none)) (d := id) (by intro x i; cases i <;> rfl)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_ofPred_eq,mem_preimage]
  constructor
  · rintro ⟨hx,he⟩
    exact ⟨hx,funext (fun _ => he)⟩
  · rintro ⟨hx,he⟩
    exact ⟨hx,congrFun he 0⟩
end SemialgebraicOn

namespace NashPatch
variable {n : ℕ}

lemma analytic_complexMap (p : NashPatch (n+n)) : AnalyticOnNhd ℝ p.complexMap p.domain := by
  intro x hx
  exact ((complexRealEquiv n).symm.analyticAt _).comp (p.analytic_toFun x hx)

lemma semialgebraic_complexMap_re (p : NashPatch (n+n)) (j : Fin n) :
    PolynomialSignSet (id : (Option (Fin p.dim) → ℝ) → (Option (Fin p.dim) → ℝ))
      {x | (fun i => x (some i)) ∈ p.domain ∧ x none = (p.complexMap (fun i => x (some i)) j).re} :=
  p.semialgebraic_toFun.coordinate_graph (finSumFinEquiv (.inl j))

lemma semialgebraic_complexMap_im (p : NashPatch (n+n)) (j : Fin n) :
    PolynomialSignSet (id : (Option (Fin p.dim) → ℝ) → (Option (Fin p.dim) → ℝ))
      {x | (fun i => x (some i)) ∈ p.domain ∧ x none = (p.complexMap (fun i => x (some i)) j).im} :=
  p.semialgebraic_toFun.coordinate_graph (finSumFinEquiv (.inr j))

end NashPatch

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicPolynomialNonzero
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology MeasureTheory
open scoped Classical

namespace NashPatch

theorem principal_rank_dichotomy_oai {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (Q : MvPolynomial (Fin n) ℂ)
    (hcharts : ∀ q ∈ MvPolynomial.zeroLocus ℂ I, MvPolynomial.eval q Q ≠ 0 →
      ∃ W : Set (Affine n), W ⊆ MvPolynomial.zeroLocus ℂ I ∧
        IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' W) ∧ q ∈ W ∧
        ∃ B : Set (Affine m), IsOpen B ∧ Nonempty (Biholomorph W B))
    (p : NashPatch (n+n)) (h0 : 0 ∈ p.domain)
    (hpI : ∀ x ∈ p.domain, p.complexMap x ∈ MvPolynomial.zeroLocus ℂ I)
    (hpQ : ∀ x ∈ p.domain, MvPolynomial.eval (p.complexMap x) Q ≠ 0) :
    (∃ P : MvPolynomial (Fin n) ℂ, P ∉ I ∧
      ∀ x ∈ p.domain, MvPolynomial.eval (p.complexMap x) P = 0) ∨
      volume {x | x ∈ p.domain ∧ p.complexRank x < m} = 0 := by
  obtain ⟨W,hWI,hW,hpW,B,hB,⟨e⟩⟩ := hcharts _ (hpI 0 h0) (hpQ 0 h0)
  obtain ⟨F,G,hF0,hF,hG,hGF,_hFG,hFV⟩ := e.centered_chart_germs hWI hW hB hpW
  rcases nash_cell_intrinsic_rank_dichotomy (MvPolynomial.zeroLocus ℂ I) F G hF
    (hF0 ▸ hG) hGF hFV p.domain p.isOpen_domain p.isConnected_domain.isPreconnected h0
    p.complexMap p.analytic_complexMap hpI p.semialgebraic_complexMap_re p.semialgebraic_complexMap_im with h | h
  · left
    obtain ⟨P,⟨y,hy,hyP⟩,hpP⟩ := h
    exact ⟨P,fun hPI => hyP (hy P hPI),hpP⟩
  · exact Or.inr h

end NashPatch
end

open Set
open scoped Classical

end Release061

end

end OAI
end

theorem solution : type_of% @OAI.Release061.NashPatch.principal_rank_dichotomy_oai := @OAI.Release061.NashPatch.principal_rank_dichotomy_oai
