-- Prove2me | solution 1 for OAI.Generator.Tracial.traceOrbit_isSeparable_of_separablePredual_q129
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:16:00.362198+00:00
-- url     : https://prove2.me/submissions/ed64c481-4524-4dc7-ac45-90cc13923d5d

import Mathlib
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ129G006
import Definitions.Def_OAIQ129G012
import Theorems.Thm_OAI_Generator_Tracial_predual_small_of_small_trace_sandwich_q129

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_HilbertLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.predualFunctionals_normed _root_.OAI.Generator.predualFunctionals_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Multiplication and adjoint limits in L2, with the necessary uniform
operator norm bounds stated explicitly. -/

/-! A separating vector for a concrete von Neumann algebra is cyclic for its
commutant. The original representation need not be cyclic for the algebra. -/

/-! Restrict the faithful trace representation to the closure of M times its
trace vector. This constructs a faithful, isometric, cyclic representation on
an actual Hilbert subspace. No Banach predual or WOT-closed image is asserted. -/
namespace Tracial

section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem traceCyclicHom_cyclic :
    Dense (Set.range (fun a : M.toStarSubalgebra => traceCyclicHom τ a (traceCyclicVector τ))) := by
  intro y
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨z,⟨a,rfl⟩,ha⟩ := Metric.mem_closure_iff.mp y.property ε hε
  exact ⟨traceCyclicHom τ a (traceCyclicVector τ),⟨a,rfl⟩,ha⟩

end

/-! The faithful cyclic restriction sends actual algebra balls to compact
weak-operator balls. On each bounded ball it is a closed topological embedding. -/
open scoped Topology
open UltrapowerBridge

end Tracial

/-! A real linear functional continuous for bounded trace-two-norm sequences
is WOT continuous on the unit ball. Closed convex slices of the trace-vector
ball supply the conversion; no identification of the two topologies is assumed. -/
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem traceVector_weak_continuous (C : ℝ) :
    Continuous (fun T : weakOperatorBall M C => toWeakSpace ℂ H (T.val τ.vector)) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro f
  exact (ContinuousLinearMapWOT.continuous_dual_apply τ.vector f).comp continuous_subtype_val

theorem traceFunctionalSlice_convex (f : M.toStarSubalgebra →L[ℝ] ℝ) (r : ℝ) :
    Convex ℝ (traceFunctionalSlice τ f r) := by
  intro x hx y hy s t hs ht hst
  obtain ⟨a, ha, hfa, rfl⟩ := hx
  obtain ⟨b, hb, hfb, rfl⟩ := hy
  refine ⟨s • a + t • b, ?_, ?_, rfl⟩
  · calc
      ‖s • a + t • b‖ ≤ ‖s • a‖ + ‖t • b‖ := norm_add_le _ _
      _ = s * ‖a‖ + t * ‖b‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
      _ ≤ s * 1 + t * 1 := _root_.add_le_add
        (mul_le_mul_of_nonneg_left ha hs) (mul_le_mul_of_nonneg_left hb ht)
      _ = 1 := by simpa only [mul_one] using hst
  · rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    calc
      s*f a+t*f b ≤ s*r+t*r := _root_.add_le_add
        (mul_le_mul_of_nonneg_left hfa hs) (mul_le_mul_of_nonneg_left hfb ht)
      _ = r := by rw [← add_mul, hst, one_mul]

theorem traceFunctionalSlice_isClosed (f : M.toStarSubalgebra →L[ℝ] ℝ)
    (hf : ∀ (a : ℕ → M.toStarSubalgebra) (b : M.toStarSubalgebra),
      (∀ n, ‖a n‖ ≤ 1) → Tendsto (fun n => τ.norm₂ (a n-b)) atTop (𝓝 0) →
      Tendsto (fun n => f (a n)) atTop (𝓝 (f b))) (r : ℝ) :
    IsClosed (traceFunctionalSlice τ f r) := by
  apply IsSeqClosed.isClosed
  intro ξ z hz hlim
  choose a ha hfa he using hz
  have hva : Tendsto (fun n => (a n).val τ.vector) atTop (𝓝 z) := by
    simpa only [he] using hlim
  obtain ⟨b, hb, hbe⟩ := bounded_trace_limit τ a 1 zero_le_one ha z hva
  refine ⟨b, hb, ?_, hbe⟩
  apply le_of_tendsto (hf a b ha ?_) (Eventually.of_forall hfa)
  apply (tendsto_vector_iff_norm₂ τ atTop a b).mp
  rwa [hbe]

theorem unitBall_functional_sublevel_isClosed (f : M.toStarSubalgebra →L[ℝ] ℝ)
    (hf : ∀ (a : ℕ → M.toStarSubalgebra) (b : M.toStarSubalgebra),
      (∀ n, ‖a n‖ ≤ 1) → Tendsto (fun n => τ.norm₂ (a n-b)) atTop (𝓝 0) →
      Tendsto (fun n => f (a n)) atTop (𝓝 (f b))) (r : ℝ) :
    IsClosed {T : weakOperatorBall M 1 | f ⟨T.val.toCLM, T.property.1⟩ ≤ r} := by
  have hclosed := traceFunctionalSlice_isClosed τ f hf r
  have hconvex := traceFunctionalSlice_convex τ f r
  have hw : IsClosed ((toWeakSpace ℂ H) '' traceFunctionalSlice τ f r) := by
    rw [← closure_eq_iff_isClosed, ← hconvex.toWeakSpace_closure ℂ, hclosed.closure_eq]
  have hpre := hw.preimage (traceVector_weak_continuous τ 1)
  convert hpre using 1
  all_goals try with_reducible_and_instances rfl
  ext T
  constructor
  · intro h
    exact ⟨T.val τ.vector, ⟨⟨T.val.toCLM, T.property.1⟩, T.property.2, h, rfl⟩, rfl⟩
  · rintro ⟨ξ, ⟨a, _, hfa, ha⟩, he⟩
    have hv : a.val τ.vector = T.val τ.vector := ha.trans ((toWeakSpace ℂ H).injective he)
    have heq : a = (⟨T.val.toCLM, T.property.1⟩ : M.toStarSubalgebra) := by
      apply sub_eq_zero.mp
      apply τ.separating
      change a.val τ.vector - T.val τ.vector = 0
      exact sub_eq_zero.mpr hv
    change f ⟨T.val.toCLM, T.property.1⟩ ≤ r
    simpa only [heq] using hfa

theorem unitBall_functional_continuous_of_norm₂ (f : M.toStarSubalgebra →L[ℝ] ℝ)
    (hf : ∀ (a : ℕ → M.toStarSubalgebra) (b : M.toStarSubalgebra),
      (∀ n, ‖a n‖ ≤ 1) → Tendsto (fun n => τ.norm₂ (a n-b)) atTop (𝓝 0) →
      Tendsto (fun n => f (a n)) atTop (𝓝 (f b))) :
    Continuous (fun T : weakOperatorBall M 1 => f ⟨T.val.toCLM, T.property.1⟩) := by
  apply continuous_iff_lower_upperSemicontinuous.mpr
  constructor
  · exact lowerSemicontinuous_iff_isClosed_preimage.mpr
      (unitBall_functional_sublevel_isClosed τ f hf)
  · apply upperSemicontinuous_iff_isClosed_preimage.mpr
    intro r
    have hn := unitBall_functional_sublevel_isClosed τ (-f)
      (fun a b ha ht => (hf a b ha ht).neg) (-r)
    change IsClosed {T : weakOperatorBall M 1 | r ≤ f ⟨T.val.toCLM, T.property.1⟩}
    simpa only [neg_apply, neg_le_neg_iff] using hn

end Tracial

/-! On a uniformly operator-norm bounded family in a faithfully vector-traced
von Neumann algebra, L2 convergence implies strong and adjoint-strong convergence
in the original Hilbert space. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_CyclicPredual
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.predualFunctionals_normed _root_.OAI.Generator.predualFunctionals_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A concrete candidate predual: the norm-closed complex span of vector
functionals from the faithful cyclic trace representation, with completeness,
separability, and an isometric evaluation map. -/

/-! Every functional in the constructed norm-closed vector-functional space is
weak-operator continuous on each bounded ball of the original algebra. -/
open Filter
open scoped Topology

/-! Recover every functional on the constructed predual from an actual algebra
element, using compact bounded balls and weak-dual Hahn--Banach separation. -/
open Filter
open scoped Topology

/-! Evaluation surjectivity for any subspace of bounded-unit-ball WOT-continuous
functionals. Compactness and Hahn--Banach supply actual algebra elements. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (F : Submodule ℂ (StrongDual ℂ M.toStarSubalgebra))

theorem functionalSubspaceWeakBall_isCompact (C : ℝ)
    (hF : F ≤ ballContinuousFunctionals M C) : IsCompact (functionalSubspaceWeakBall F C) := by
  let : CompactSpace (weakOperatorBall M C) :=
    isCompact_iff_compactSpace.mp (weakOperatorBall_isCompact M C)
  let f : weakOperatorBall M C → WeakDual ℂ F :=
    fun T => functionalSubspaceWeakEvaluation F ⟨T.val.toCLM,T.property.1⟩
  have hf : Continuous f := by
    apply WeakBilin.continuous_of_continuous_eval
    intro z
    exact hF z.property
  have he : functionalSubspaceWeakBall F C=Set.range f := by
    ext T
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨ContinuousLinearMapWOT.ofCLM a.val,⟨a.property,ha⟩⟩,rfl⟩
    · rintro ⟨a,rfl⟩
      exact ⟨⟨a.val.toCLM,a.property.1⟩,a.property.2,rfl⟩
  rw [he]
  exact isCompact_range hf

theorem functionalSubspaceWeakBall_convex (C : ℝ) : Convex ℝ (functionalSubspaceWeakBall F C) := by
  have h : Convex ℝ {a : M.toStarSubalgebra | ‖a‖ ≤ C} := by
    simpa only [Metric.closedBall,dist_zero_right] using convex_closedBall (0 : M.toStarSubalgebra) C
  exact h.linear_image ((functionalSubspaceWeakEvaluation F).restrictScalars ℝ)

theorem functionalSubspaceEvaluation_unitBall_surjective
    (hF : F ≤ ballContinuousFunctionals M 1)
    (φ : StrongDual ℂ F) (hφ : ‖φ‖ ≤ 1) :
    ∃ a : M.toStarSubalgebra,‖a‖ ≤ 1 ∧ functionalSubspaceEvaluation F a=φ := by
  have hm : StrongDual.toWeakDual φ ∈ functionalSubspaceWeakBall F 1 := by
    by_contra hnot
    obtain ⟨g,u,hgu,hug⟩ := weakDual_separation
      (functionalSubspaceWeakBall_convex F 1) (functionalSubspaceWeakBall_isCompact F 1 hF).isClosed hnot
    obtain ⟨f,hf⟩ := LinearMap.dualEmbedding_surjective
      (topDualPairing ℂ F) g
    have he (a : M.toStarSubalgebra) : g (functionalSubspaceWeakEvaluation F a)=f.val a := by
      rw [← hf]
      rfl
    have heφ : g (StrongDual.toWeakDual φ)=φ f := by
      rw [← hf]
      rfl
    have hu : 0 < u := by
      have h := hgu (functionalSubspaceWeakEvaluation F 0) ⟨0,by simp,rfl⟩
      simpa only [he,map_zero,Complex.zero_re] using h
    have hn : ‖f.val‖ ≤ u := dual_norm_le_of_re_unitBall f.val u hu.le (fun a ha => by
      have hh := (hgu (functionalSubspaceWeakEvaluation F a) ⟨a,ha,rfl⟩).le
      rw [he] at hh
      exact hh)
    have hb : (φ f).re ≤ u := by
      calc
        (φ f).re ≤ ‖φ f‖ := Complex.re_le_norm _
        _ ≤ ‖φ‖*‖f‖ := φ.le_opNorm f
        _ ≤ 1*‖f‖ := mul_le_mul_of_nonneg_right hφ (norm_nonneg f)
        _ = ‖f‖ := one_mul _
        _ ≤ u := hn
    rw [heφ] at hug
    exact (not_lt_of_ge hb) hug
  obtain ⟨a,ha,he⟩ := hm
  exact ⟨a,ha,congrArg WeakDual.toStrongDual he⟩

/-- Unit-ball surjectivity extends by rescaling to the whole dual. -/
theorem functionalSubspaceEvaluation_surjective
    (hF : F ≤ ballContinuousFunctionals M 1) :
    Function.Surjective (functionalSubspaceEvaluation F) := by
  intro φ
  let c : ℂ := (‖φ‖ + 1 : ℝ)
  have hc : c ≠ 0 := by dsimp [c]; exact_mod_cast ne_of_gt (by positivity : 0 < ‖φ‖ + 1)
  have hnorm : ‖c⁻¹ • φ‖ ≤ 1 := by
    rw [norm_smul, norm_inv]
    have hn : ‖c‖ = ‖φ‖ + 1 := by
      dsimp [c]
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hn]
    exact (inv_mul_le_one₀ (by positivity : 0 < ‖φ‖ + 1)).mpr (by linarith)
  obtain ⟨a, _, ha⟩ := functionalSubspaceEvaluation_unitBall_surjective F hF (c⁻¹ • φ) hnorm
  refine ⟨c • a, ?_⟩
  change functionalSubspaceEvaluationLinear F (c • a) = φ
  rw [map_smul]
  change c • functionalSubspaceEvaluation F a = φ
  rw [ha, smul_smul, mul_inv_cancel₀ hc, one_smul]

end

/-! Exact characterization of the cyclic predual by WOT continuity on the
unit ball. No continuity of an arbitrary given-predual evaluation is assumed
or asserted here. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem ballContinuousFunctionals_eq_cyclicPredual :
    ballContinuousFunctionals M 1 = cyclicPredual τ := by
  apply le_antisymm
  · intro f hf
    let F := ballContinuousFunctionals M 1
    let K : Submodule ℂ F := (cyclicPredual τ).comap F.subtype
    let : IsClosed (K : Set F) :=
      (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
    let z : F := ⟨f, hf⟩
    by_contra hz
    have hq : K.mkQ z ≠ 0 := by
      intro heq
      exact hz ((Submodule.Quotient.mk_eq_zero K).mp heq)
    obtain ⟨g, hg⟩ := SeparatingDual.exists_ne_zero (R := ℂ) hq
    obtain ⟨a, ha⟩ := functionalSubspaceEvaluation_surjective F le_rfl (g.comp K.mkQL)
    have ha0 : a = 0 := by
      apply norm_eq_zero.mp
      rw [← cyclicPredualEvaluation_norm τ]
      apply norm_eq_zero.mpr
      ext q
      change q.val a = 0
      let q' : F := ⟨q.val, cyclicPredual_le_ballContinuousFunctionals τ 1 q.property⟩
      have hk : K.mkQ q' = 0 := (Submodule.Quotient.mk_eq_zero K).mpr q.property
      have h := congrArg (fun ψ : StrongDual ℂ F => ψ q') ha
      change q.val a = g (K.mkQ q') at h
      simpa only [hk, map_zero] using h
    apply hg
    have h := congrArg (fun ψ : StrongDual ℂ F => ψ z) ha
    change f a = g (K.mkQ z) at h
    simpa only [ha0, map_zero] using h.symm
  · exact cyclicPredual_le_ballContinuousFunctionals τ 1

theorem mem_cyclicPredual_iff_unitBall_continuous (f : StrongDual ℂ M.toStarSubalgebra) :
    f ∈ cyclicPredual τ ↔
      Continuous (fun T : weakOperatorBall M 1 => f ⟨T.val.toCLM, T.property.1⟩) := by
  rw [← ballContinuousFunctionals_eq_cyclicPredual τ]
  rfl

theorem mem_cyclicPredual_of_unitBall_continuous (f : StrongDual ℂ M.toStarSubalgebra)
    (hf : Continuous (fun T : weakOperatorBall M 1 => f ⟨T.val.toCLM, T.property.1⟩)) :
    f ∈ cyclicPredual τ :=
  (mem_cyclicPredual_iff_unitBall_continuous τ f).mpr hf

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_FunctionalLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.q129Add _root_.OAI.UltrapowerBridge.q129AddCommGroup _root_.OAI.UltrapowerBridge.q129Monoid _root_.OAI.UltrapowerBridge.q129Mul _root_.OAI.UltrapowerBridge.q129MulOneClass _root_.OAI.UltrapowerBridge.q129NAS _root_.OAI.UltrapowerBridge.q129Neg _root_.OAI.UltrapowerBridge.q129One _root_.OAI.UltrapowerBridge.q129Ring _root_.OAI.UltrapowerBridge.q129Semiring _root_.OAI.UltrapowerBridge.q129Sub _root_.OAI.UltrapowerBridge.q129Zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! A functional bounded by a Hilbert-valued linear map factors through one
inner product. The proof uses the actual range, Hahn--Banach, and Riesz. -/

/-! A separable normed space has a countable family of bounded linear
functionals separating its points. All functionals are constructed by
Hahn--Banach at a countable dense family of vectors. -/
section
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace.SeparableSpace E]

theorem exists_countable_total_dual :
    ∃ g : ℕ → StrongDual ℂ E, (∀ n, ‖g n‖ ≤ 1) ∧
      ∀ x : E, (∀ n, g n x = 0) → x = 0 := by
  choose g hg he using fun n => exists_dual_vector'' ℂ (TopologicalSpace.denseSeq E n)
  refine ⟨g, hg, fun x hx => ?_⟩
  by_contra hzero
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hzero
  obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq E).exists_dist_lt x
    (by positivity : 0 < ‖x‖ / 3)
  have hb : ‖TopologicalSpace.denseSeq E n‖ ≤ ‖TopologicalSpace.denseSeq E n - x‖ := by
    calc
      ‖TopologicalSpace.denseSeq E n‖ =
          ‖g n (TopologicalSpace.denseSeq E n - x)‖ := by
        simp only [map_sub, hx, sub_zero, he, RCLike.norm_ofReal,
          abs_of_nonneg (norm_nonneg _)]
      _ ≤ ‖g n‖ * ‖TopologicalSpace.denseSeq E n - x‖ := (g n).le_opNorm _
      _ ≤ ‖TopologicalSpace.denseSeq E n - x‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hg n) (norm_nonneg _)
  have ht := norm_le_norm_add_norm_sub (TopologicalSpace.denseSeq E n) x
  rw [norm_sub_rev] at ht
  rw [dist_eq_norm] at hn
  rw [norm_sub_rev] at hb
  linarith

end

/-! Hermitian symmetrization and complex polarization for bounded functionals.
No tracial functional or finite factor is supplied to these algebraic lemmas. -/
open scoped CStarAlgebra

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MonotoneTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.UltrapowerBridge.q129Add _root_.OAI.UltrapowerBridge.q129AddCommGroup _root_.OAI.UltrapowerBridge.q129Algebra _root_.OAI.UltrapowerBridge.q129Module _root_.OAI.UltrapowerBridge.q129Monoid _root_.OAI.UltrapowerBridge.q129Mul _root_.OAI.UltrapowerBridge.q129MulOneClass _root_.OAI.UltrapowerBridge.q129NAS _root_.OAI.UltrapowerBridge.q129NUNAS _root_.OAI.UltrapowerBridge.q129Neg _root_.OAI.UltrapowerBridge.q129One _root_.OAI.UltrapowerBridge.q129Ring _root_.OAI.UltrapowerBridge.q129SMul _root_.OAI.UltrapowerBridge.q129Semiring _root_.OAI.UltrapowerBridge.q129StarRing _root_.OAI.UltrapowerBridge.q129Sub _root_.OAI.UltrapowerBridge.q129Zero
attribute [-simp] _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.Generator.Tracial.restrictedTrace_norm₂ _root_.OAI.Generator.Tracial.restrictedTrace_trace _root_.OAI.Generator.Tracial.traceCyclicOperator_apply _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul _root_.OAI.UltrapowerBridge.TracialRepresentation.trace_add _root_.OAI.UltrapowerBridge.TracialRepresentation.trace_smul _root_.OAI.UltrapowerBridge.TracialRepresentation.trace_sub _root_.OAI.UltrapowerBridge.quotientMap_smul _root_.OAI.UltrapowerBridge.quotientMap_star _root_.OAI.UltrapowerBridge.quotientTrace_mk _root_.OAI.UltrapowerBridge.quotientTrace_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Bounded positive monotone nets have actual least upper bounds in M.
Every displayed vector-trace bound passes to the constructed bound. -/

/-! Absolute values in the represented algebra, with ambient order bounds
and the actual trace two-norm. -/
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem ambientAbsoluteValue_nonneg (a : M.toStarSubalgebra) :
    0 ≤ (ambientAbsoluteValue a).val := CFC.abs_nonneg _

theorem ambientAbsoluteValue_norm (a : M.toStarSubalgebra) :
    ‖ambientAbsoluteValue a‖ = ‖a‖ := by
  change ‖CFC.abs a.val‖ = ‖a.val‖
  exact CFC.norm_abs

theorem ambientAbsoluteValue_norm₂ (a : M.toStarSubalgebra) :
    τ.norm₂ (ambientAbsoluteValue a) = τ.norm₂ a := by
  have he : star (ambientAbsoluteValue a)*ambientAbsoluteValue a = star a*a := by
    apply Subtype.ext
    change star (CFC.abs a.val)*CFC.abs a.val = star a.val*a.val
    rw [(CFC.abs_nonneg a.val).isSelfAdjoint.star_eq, CFC.abs_mul_abs]
  have h := congrArg Complex.re (τ.trace_star_mul (ambientAbsoluteValue a))
  rw [he, τ.trace_star_mul] at h
  simp only [← Complex.ofReal_pow, Complex.ofReal_re] at h
  nlinarith [show 0 ≤ τ.norm₂ a from norm_nonneg _,
    show 0 ≤ τ.norm₂ (ambientAbsoluteValue a) from norm_nonneg _]

theorem ambientAbsoluteValue_trace_le_norm₂ (a : M.toStarSubalgebra) :
    (τ.trace (ambientAbsoluteValue a)).re ≤ τ.norm₂ a :=
  (Complex.re_le_norm _).trans ((τ.norm_trace_le_norm₂ _).trans_eq
    (ambientAbsoluteValue_norm₂ τ a))

theorem ambient_le_absoluteValue (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a.val) :
    a.val ≤ (ambientAbsoluteValue a).val := by
  apply sub_nonneg.mp
  change 0 ≤ CFC.abs a.val - a.val
  rw [CFC.abs_sub_self a.val ha]
  exact nsmul_nonneg (CFC.negPart_nonneg a.val) 2

theorem ambient_neg_absoluteValue_le (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a.val) :
    -(ambientAbsoluteValue a).val ≤ a.val := by
  have h : 0 ≤ CFC.abs a.val + a.val := by
    rw [CFC.abs_add_self a.val ha]
    exact nsmul_nonneg (CFC.posPart_nonneg a.val) 2
  apply neg_le_iff_add_nonneg.mpr
  change 0 ≤ a.val + CFC.abs a.val
  simpa only [add_comm] using h

theorem norm₂_realPart_le (a : M.toStarSubalgebra) :
    τ.norm₂ (realPart a) ≤ τ.norm₂ a := by
  have he : τ.norm₂ (realPart a) = (1/2 : ℝ) * τ.norm₂ (a+star a) := by
    rw [realPart_apply_coe]
    change ‖(2 : ℝ)⁻¹ • ((a+star a).val τ.vector)‖ = _
    rw [norm_smul]
    norm_num
    rfl
  rw [he]
  have h := τ.norm₂_add_le a (star a)
  rw [τ.norm₂_star] at h
  linarith

theorem norm₂_imaginaryPart_le (a : M.toStarSubalgebra) :
    τ.norm₂ (imaginaryPart a) ≤ τ.norm₂ a := by
  have h := norm₂_realPart_le τ (Complex.I • (-a))
  have hr : (realPart (Complex.I • (-a)) : M.toStarSubalgebra) = imaginaryPart a := by
    rw [smul_neg, map_neg, realPart_I_smul, neg_neg]
  rw [hr, τ.norm₂_smul, Complex.norm_I, one_mul] at h
  have hn : τ.norm₂ (-a) = τ.norm₂ a := norm_neg _
  rwa [hn] at h

end Tracial

/-! The bounded monotone transform a ↦ 1 - (1+a)⁻¹ of positive operators.
Its bounds prepare a construction of decreasing order majorants from small
trace tails. No tail majorant or predual continuity is asserted here. -/

/-! Decreasing positive order majorants for positive contractions with
summable trace. The finite-tail resolvents and their least upper bounds are
constructed in the actual algebra. -/
open Filter
open scoped Topology BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_PredualOrder
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.q129AddCommGroup _root_.OAI.UltrapowerBridge.q129Monoid _root_.OAI.UltrapowerBridge.q129Mul _root_.OAI.UltrapowerBridge.q129NAS _root_.OAI.UltrapowerBridge.q129NUNAS _root_.OAI.UltrapowerBridge.q129Ring _root_.OAI.UltrapowerBridge.q129SMul _root_.OAI.UltrapowerBridge.q129Semiring _root_.OAI.UltrapowerBridge.q129Zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Operator norm geometry for the original existential Banach-predual gap.
These statements use only concrete Hilbert operators. They do not identify
any predual or prove trace-orbit separability. -/

/-! Bounded self-adjoint sets are weak-star compact for the actual Banach
predual isometry. No predual uniqueness or WOT compatibility is assumed. -/

/-! Positive operator balls are compact in the weak-star topology of the
given Banach predual. The isometry is not assumed weak-operator continuous. -/

/-! Closed and compact order intervals for the given Banach predual.
All inequalities are the concrete operator Loewner order. -/

/-! Monotone order limits in the algebra converge for the actual given
Banach predual. Greatest/least bounds are tested only against members of S,
not against all ambient operators. -/

/-! The actual given predual embeds isometrically into the norm dual of S.
Conjugation accounts for the conjugate-linear predual isometry. These
functionals preserve monotone order limits. No canonical-predual membership
or weak-operator continuity is assumed. -/
section
open Filter
open scoped Topology ComplexConjugate
variable {H X I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (S : StarSubalgebra ℂ (H →L[ℂ] H))
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S)

/-- Given-predual evaluation functionals separate every two algebra elements. -/
theorem predualFunctional_separates (a b : S)
    (h : ∀ x : X, predualFunctional S e x a = predualFunctional S e x b) : a = b := by
  apply e.symm.injective
  ext x
  exact (starRingEnd ℂ).injective (h x)

end

/-! An arbitrary net squeezed into shrinking operator order intervals
converges in the topology of the given Banach predual. The net itself need
not be monotone. No normal-functional decomposition is used. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_PredualRange
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! An actual separable Banach predual for the constructed matrix-generated
factor. The existential convention is exactly Generator.HasSeparablePredual. -/

/-! Separability of the actual cyclic predual implies separability of the
trace-vector orbit. This does not identify an arbitrary given Banach predual
with the cyclic predual. -/
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-- A countable total family of dual evaluations supplies a countable total
family of actual trace vectors. -/
theorem exists_countable_total_traceVectors
    [TopologicalSpace.SeparableSpace (cyclicPredual τ)] :
    ∃ a : ℕ → M.toStarSubalgebra, (∀ n, ‖a n‖ ≤ 1) ∧
      ∀ ξ : traceCyclicSpace τ,
        (∀ n, inner ℂ ξ (traceCyclicHom τ (a n) (traceCyclicVector τ)) = 0) → ξ = 0 := by
  obtain ⟨g, hg, htotal⟩ := exists_countable_total_dual (cyclicPredual τ)
  let a : ℕ → M.toStarSubalgebra := fun n => (cyclicPredualLinearEquiv τ).symm (g n)
  have he (n : ℕ) : cyclicPredualEvaluation τ (a n) = g n :=
    (cyclicPredualLinearEquiv τ).apply_symm_apply (g n)
  refine ⟨a, fun n => ?_, fun ξ hξ => ?_⟩
  · exact ((cyclicPredualLinearEquiv τ).symm.norm_map (g n)).le.trans (hg n)
  · let f : cyclicPredual τ := ⟨cyclicCoefficient τ ξ (traceCyclicVector τ),
        cyclicCoefficient_mem τ ξ (traceCyclicVector τ)⟩
    have hf : f = 0 := htotal f (fun n => by
      rw [← he]
      exact hξ n)
    apply (traceCyclicHom_cyclic τ).eq_zero_of_inner_left ℂ
    rintro _ ⟨b, rfl⟩
    exact congrArg (fun q : cyclicPredual τ => q.val b) hf

theorem traceCyclicSpace_separable_of_cyclicPredual
    [TopologicalSpace.SeparableSpace (cyclicPredual τ)] :
    TopologicalSpace.SeparableSpace (traceCyclicSpace τ) := by
  obtain ⟨a, _, ha⟩ := exists_countable_total_traceVectors τ
  let v : ℕ → traceCyclicSpace τ := fun n => traceCyclicHom τ (a n) (traceCyclicVector τ)
  let V := (Submodule.span ℂ (Set.range v)).topologicalClosure
  have htop : V = ⊤ := by
    apply Submodule.orthogonal_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro ξ hξ
    change ξ = 0
    apply ha ξ
    intro n
    exact (Submodule.mem_orthogonal' V ξ).mp hξ (v n)
      (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩))
  have hs : TopologicalSpace.IsSeparable (V : Set (traceCyclicSpace τ)) :=
    (Set.countable_range v).isSeparable.span.closure
  rw [htop, Submodule.top_coe] at hs
  exact TopologicalSpace.isSeparable_univ_iff.mp hs

theorem traceOrbit_isSeparable_of_cyclicPredual
    [TopologicalSpace.SeparableSpace (cyclicPredual τ)] :
    TopologicalSpace.IsSeparable (Set.range (baseVector τ)) := by
  let := traceCyclicSpace_separable_of_cyclicPredual τ
  apply (TopologicalSpace.isSeparable_range
    (continuous_subtype_val : Continuous (fun ξ : traceCyclicSpace τ => ξ.val))).mono
  rintro ξ ⟨a, rfl⟩
  exact ⟨traceCyclicHom τ a (traceCyclicVector τ), rfl⟩

end Tracial

/-! The given predual as a closed separating subspace of the algebra norm dual, with its evaluation duality. -/
section
open scoped ComplexConjugate
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (S : StarSubalgebra ℂ (H →L[ℂ] H))
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S)

theorem predualFunctionals_isClosed [CompleteSpace X] :
    IsClosed (predualFunctionals S e : Set (StrongDual ℂ S)) :=
  (predualFunctionalIsometry S e).isometry.isClosedEmbedding.isClosed_range

theorem predualFunctionals_separable [TopologicalSpace.SeparableSpace X] :
    TopologicalSpace.SeparableSpace (predualFunctionals S e) :=
  (TopologicalSpace.isSeparable_range (predualFunctionalIsometry S e).continuous).separableSpace

end

/-! Hahn–Banach comparison of preduals from normal-functional membership and evaluation surjectivity. -/
section
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (S : StarSubalgebra ℂ (H →L[ℂ] H))
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S)

/-- A closed separating predual contained in an evaluation predual equals it.
The inclusion is a substantive hypothesis, not supplied by this theorem. -/
theorem predualFunctionals_eq_of_le (F : Submodule ℂ (StrongDual ℂ S))
    (hincl : predualFunctionals S e ≤ F)
    (hdual : ∀ φ : StrongDual ℂ F, ∃ a : S, ∀ f : F, φ f = f.val a) :
    predualFunctionals S e = F := by
  let : NormedAddCommGroup F := inferInstance
  let : NormedSpace ℂ F := inferInstance
  apply le_antisymm hincl
  intro f hf
  let K : Submodule ℂ F := (predualFunctionals S e).comap F.subtype
  let : IsClosed (K : Set F) :=
    (predualFunctionals_isClosed S e).preimage continuous_subtype_val
  let z : F := ⟨f, hf⟩
  by_contra hz
  have hq : K.mkQ z ≠ 0 := by
    intro heq
    exact hz ((Submodule.Quotient.mk_eq_zero K).mp heq)
  obtain ⟨g, hg⟩ := SeparatingDual.exists_ne_zero (R := ℂ) hq
  obtain ⟨a, ha⟩ := hdual (g.comp K.mkQL)
  have ha0 : a = 0 := by
    apply predualFunctional_separates S e a 0
    intro x
    have hmem : predualFunctional S e x ∈ predualFunctionals S e := ⟨x, rfl⟩
    let fx : F := ⟨predualFunctional S e x, hincl hmem⟩
    have hk : K.mkQ fx = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hmem
    have hx := ha fx
    change g (K.mkQ fx) = predualFunctional S e x a at hx
    rw [hk, map_zero] at hx
    simpa only [map_zero] using hx.symm
  apply hg
  have hz' := ha z
  change g (K.mkQ z) = f a at hz'
  simpa only [ha0, map_zero] using hz'

end

/-! Conditional comparison with the constructed cyclic predual. Membership
of the given-predual evaluations in that space is an explicit unproved input;
it is not obtained merely from their order-limit convergence. -/
namespace Tracial
open UltrapowerBridge
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M.toStarSubalgebra)

/-- Normal-functional membership is sufficient for equality with the given predual. -/
theorem predualFunctionals_eq_cyclicPredual_of_membership
    (hmem : ∀ x : X, predualFunctional M.toStarSubalgebra e x ∈ cyclicPredual τ) :
    predualFunctionals M.toStarSubalgebra e = cyclicPredual τ := by
  apply predualFunctionals_eq_of_le M.toStarSubalgebra e (cyclicPredual τ)
  · rintro f ⟨x, rfl⟩
    exact hmem x
  · intro φ
    obtain ⟨a, ha⟩ := cyclicPredualEvaluation_surjective τ φ
    refine ⟨a, fun f => ?_⟩
    exact (congrArg (fun ψ : StrongDual ℂ (cyclicPredual τ) => ψ f) ha).symm

/-- Under the same explicit membership input, separability transfers to the cyclic predual. -/
theorem cyclicPredual_separable_of_given_membership [TopologicalSpace.SeparableSpace X]
    (hmem : ∀ x : X, predualFunctional M.toStarSubalgebra e x ∈ cyclicPredual τ) :
    TopologicalSpace.SeparableSpace (cyclicPredual τ) := by
  rw [← predualFunctionals_eq_cyclicPredual_of_membership τ e hmem]
  exact predualFunctionals_separable M.toStarSubalgebra e

/-! The original given-predual evaluations suffice for trace-orbit separability
once their normal-functional membership (equivalently unit-ball WOT
continuity) is proved. The remaining input is displayed literally. -/

theorem traceOrbit_isSeparable_of_given_membership [TopologicalSpace.SeparableSpace X]
    (hmem : ∀ x : X, predualFunctional M.toStarSubalgebra e x ∈ cyclicPredual τ) :
    TopologicalSpace.IsSeparable (Set.range (baseVector τ)) := by
  let := cyclicPredual_separable_of_given_membership τ e hmem
  exact traceOrbit_isSeparable_of_cyclicPredual τ

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_PredualContinuity
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing
attribute [-simp] _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Given-predual evaluations are uniformly small on operator order
intervals bounded by positive contractions with small trace. This is derived
from the constructed tail majorants, without assuming predual normality. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M.toStarSubalgebra)

/-! Given-predual evaluation is uniformly trace-two-norm continuous on every
operator-norm bounded ball. No WOT continuity premise is used. -/

theorem predual_small_of_small_norm₂_selfAdjoint (x : X) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : M.toStarSubalgebra,
      IsSelfAdjoint a.val → ‖a‖ ≤ 1 → τ.norm₂ a < δ →
      ‖predualFunctional M.toStarSubalgebra e x a‖ < ε := by
  obtain ⟨δ, hδ, hs⟩ := predual_small_of_small_trace_sandwich_q129 τ e x ε hε
  refine ⟨δ, hδ, fun a ha hn ht => hs a (ambientAbsoluteValue a)
    (ambientAbsoluteValue_nonneg a) ?_ ?_ (ambient_neg_absoluteValue_le a ha)
    (ambient_le_absoluteValue a ha)⟩
  · exact (ambientAbsoluteValue_norm a).le.trans hn
  · exact (ambientAbsoluteValue_trace_le_norm₂ τ a).trans_lt ht

theorem predual_small_of_small_norm₂ (x : X) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : M.toStarSubalgebra,
      ‖a‖ ≤ 1 → τ.norm₂ a < δ →
      ‖predualFunctional M.toStarSubalgebra e x a‖ < ε := by
  obtain ⟨δ, hδ, hs⟩ := predual_small_of_small_norm₂_selfAdjoint τ e x (ε/2) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro a hn ht
  have hrsa : IsSelfAdjoint ((realPart a : M.toStarSubalgebra).val) :=
    congrArg (fun b : M.toStarSubalgebra => b.val) (realPart a).property
  have hisa : IsSelfAdjoint ((imaginaryPart a : M.toStarSubalgebra).val) :=
    congrArg (fun b : M.toStarSubalgebra => b.val) (imaginaryPart a).property
  have hr := hs (realPart a) hrsa ((realPart.norm_le a).trans hn)
    ((norm₂_realPart_le τ a).trans_lt ht)
  have hi := hs (imaginaryPart a) hisa ((imaginaryPart.norm_le a).trans hn)
    ((norm₂_imaginaryPart_le τ a).trans_lt ht)
  let f := predualFunctional M.toStarSubalgebra e x
  have he : f a = f (realPart a) + Complex.I * f (imaginaryPart a) := by
    change f a = f (realPart a) + Complex.I • f (imaginaryPart a)
    rw [← map_smul, ← map_add, realPart_add_I_smul_imaginaryPart]
  rw [he]
  have hb := norm_add_le (f (realPart a)) (Complex.I * f (imaginaryPart a))
  rw [norm_mul, Complex.norm_I, one_mul] at hb
  exact hb.trans_lt (by linarith)

theorem predual_norm₂_tendsto_zero_unitBall {I : Type*} {l : Filter I}
    (x : X) (a : I → M.toStarSubalgebra) (hn : ∀ i, ‖a i‖ ≤ 1)
    (ht : Tendsto (fun i => τ.norm₂ (a i)) l (𝓝 0)) :
    Tendsto (fun i => predualFunctional M.toStarSubalgebra e x (a i)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hs⟩ := predual_small_of_small_norm₂ τ e x ε hε
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with i hi
  simpa only [dist_zero_right] using hs (a i) (hn i) hi

theorem predual_norm₂_tendsto_zero {I : Type*} {l : Filter I}
    (x : X) (a : I → M.toStarSubalgebra) (C : ℝ) (hn : ∀ i, ‖a i‖ ≤ C)
    (ht : Tendsto (fun i => τ.norm₂ (a i)) l (𝓝 0)) :
    Tendsto (fun i => predualFunctional M.toStarSubalgebra e x (a i)) l (𝓝 0) := by
  let D : ℝ := |C|+1
  have hD : 0 < D := by dsimp [D]; positivity
  have hDn : ‖((D⁻¹ : ℝ) : ℂ)‖ = D⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hD.le)]
  let b (i : I) : M.toStarSubalgebra := ((D⁻¹ : ℝ) : ℂ) • a i
  have hb (i : I) : ‖b i‖ ≤ 1 := by
    change ‖((D⁻¹ : ℝ) : ℂ) • a i‖ ≤ 1
    rw [norm_smul, hDn]
    apply (inv_mul_le_iff₀ hD).mpr
    rw [mul_one]
    exact (hn i).trans ((le_abs_self C).trans (le_add_of_nonneg_right zero_le_one))
  have hbt : Tendsto (fun i => τ.norm₂ (b i)) l (𝓝 0) := by
    simpa only [b, τ.norm₂_smul, hDn, mul_zero] using ht.const_mul D⁻¹
  have h := (predual_norm₂_tendsto_zero_unitBall τ e x b hb hbt).const_smul (D : ℂ)
  have he (i : I) : (D : ℂ) • predualFunctional M.toStarSubalgebra e x (b i) =
      predualFunctional M.toStarSubalgebra e x (a i) := by
    rw [← map_smul]
    congr 1
    simp only [b, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hD.ne',
      Complex.ofReal_one, one_smul]
  simpa only [he, smul_zero] using h

theorem predual_norm₂_tendsto {I : Type*} {l : Filter I}
    (x : X) (a : I → M.toStarSubalgebra) (b : M.toStarSubalgebra)
    (C : ℝ) (hn : ∀ i, ‖a i‖ ≤ C)
    (ht : Tendsto (fun i => τ.norm₂ (a i-b)) l (𝓝 0)) :
    Tendsto (fun i => predualFunctional M.toStarSubalgebra e x (a i)) l
      (𝓝 (predualFunctional M.toStarSubalgebra e x b)) := by
  have h := predual_norm₂_tendsto_zero τ e x (fun i => a i-b) (C+‖b‖)
    (fun i => (norm_sub_le _ _).trans (_root_.add_le_add (hn i) le_rfl)) ht
  simpa only [map_sub, tendsto_sub_nhds_zero_iff] using h

end

/-! Every evaluation from the given Banach predual belongs to the constructed
cyclic predual. In particular, the original separable-predual hypothesis
supplies trace-orbit separability without an additional continuity premise. -/
open UltrapowerBridge
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M.toStarSubalgebra)

include τ in
theorem predualFunctional_unitBall_continuous (x : X) :
    Continuous (fun T : weakOperatorBall M 1 =>
      predualFunctional M.toStarSubalgebra e x ⟨T.val.toCLM, T.property.1⟩) := by
  let f := predualFunctional M.toStarSubalgebra e x
  have hr := unitBall_functional_continuous_of_norm₂ τ
    (Complex.reCLM.comp (f.restrictScalars ℝ)) (fun a b hn ht =>
      Complex.continuous_re.tendsto _ |>.comp (predual_norm₂_tendsto τ e x a b 1 hn ht))
  have hi := unitBall_functional_continuous_of_norm₂ τ
    (Complex.imCLM.comp (f.restrictScalars ℝ)) (fun a b hn ht =>
      Complex.continuous_im.tendsto _ |>.comp (predual_norm₂_tendsto τ e x a b 1 hn ht))
  have h := (Complex.continuous_ofReal.comp hr).add
    ((Complex.continuous_ofReal.comp hi).mul (continuous_const (y := Complex.I)))
  change Continuous (fun T : weakOperatorBall M 1 =>
    ((f ⟨T.val.toCLM, T.property.1⟩).re : ℂ) +
      ((f ⟨T.val.toCLM, T.property.1⟩).im : ℂ) * Complex.I) at h
  simpa only [Complex.re_add_im] using h

theorem predualFunctional_mem_cyclicPredual (x : X) :
    predualFunctional M.toStarSubalgebra e x ∈ cyclicPredual τ :=
  mem_cyclicPredual_of_unitBall_continuous τ _ (predualFunctional_unitBall_continuous τ e x)

theorem traceOrbit_isSeparable_of_separablePredual_q129_oai
    (hsep : HasSeparablePredual M.toStarSubalgebra) :
    TopologicalSpace.IsSeparable (Set.range (baseVector τ)) := by
  obtain ⟨X, g, s, c, hs, ⟨e⟩⟩ := hsep
  exact traceOrbit_isSeparable_of_given_membership τ e (predualFunctional_mem_cyclicPredual τ e)

end Generator.Tracial

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.traceOrbit_isSeparable_of_separablePredual_q129_oai.{u_1} := @OAI.Generator.Tracial.traceOrbit_isSeparable_of_separablePredual_q129_oai.{u_1}
