-- Prove2me | solution 1 for OAI.Percolation.LocalEndpointRule.quantitative_amplification_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T00:53:40.055973+00:00
-- url     : https://prove2.me/submissions/9507b377-0ee5-4c19-be57-af7b0424e159

import Mathlib
import Definitions.Def_CayleyPercolation
import Definitions.Def_OAIQ040C002

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Graph_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Indexed bond graphs, connectivity, percolation laws, kernels and countability. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}



section Deterministic
variable (G : BondGraph V E) (ω : Set E)

theorem cluster_eq_of_conn {x y : V} (h : Conn G ω x y) :
    cluster G ω x = cluster G ω y := by
  ext z
  exact ⟨fun hxz => conn_trans G ω (conn_symm G ω h) hxz,
    fun hyz => conn_trans G ω h hyz⟩

end Deterministic

section Countability


theorem exists_mem_reachBall {G : BondGraph V E} {x y : V}
    (h : Relation.ReflTransGen (Adj G) x y) : ∃ n, y ∈ reachBall G x n := by
  induction h with
  | refl => exact ⟨0, Set.mem_singleton _⟩
  | @tail y z _ hyz ih =>
    rcases ih with ⟨n, hn⟩
    refine ⟨n + 1, Or.inr ?_⟩
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨y, hn, hyz⟩

end Countability

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel domination, monotone couplings and endpoint bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section KernelLimits
open scoped Topology
open Filter
attribute [local instance] Classical.propDecidable


theorem finiteEmbedding_dense : DenseRange (finiteEmbedding (V := V)) := by
  intro f
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num) f)
  apply Eventually.of_forall
  intro s
  apply subset_closure
  refine ⟨∑ y ∈ s, Finsupp.single y (f y), ?_⟩
  simp



end KernelLimits

section KernelDomination
attribute [local instance] Classical.propDecidable



theorem exists_operator_of_matrix_domination
    (U K : V → V → ℝ) (hU : ∀ x y, 0 ≤ U x y)
    (hKU : ∀ x y, |K x y| ≤ U x y)
    (B : Hilbert V →L[ℂ] Hilbert V)
    (hB : ∀ x y, B (lp.single 2 y (1 : ℂ)) x = (U x y : ℂ)) :
    ∃ A : Hilbert V →L[ℂ] Hilbert V, ‖A‖ ≤ ‖B‖ ∧
      ∀ x y, A (lp.single 2 y (1 : ℂ)) x = (K x y : ℂ) := by
  have hcol (y : V) : Memℓp (fun x => (K x y : ℂ)) 2 := by
    apply (lp.memℓp (B (lp.single 2 y (1 : ℂ)))).mono'
    intro x
    simpa [hB x y, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hU x y)]
      using hKU x y
  let col (y : V) : Hilbert V := ⟨fun x => (K x y : ℂ), hcol y⟩
  let L : (V →₀ ℂ) →ₗ[ℂ] Hilbert V := Finsupp.linearCombination ℂ col
  have hLn (f : V →₀ ℂ) : ‖L f‖ ≤ ‖B‖ * ‖finiteEmbedding f‖ := by
    let g : V →₀ ℂ := f.mapRange (fun z => (‖z‖ : ℂ)) (by simp)
    have hg : finiteEmbedding g = positivePart (finiteEmbedding f) := by
      apply lp.ext
      funext x
      simp [g]
    have hpoint (x : V) : ‖L f x‖ ≤ ‖B (finiteEmbedding g) x‖ := by
      have hright : B (finiteEmbedding g) x =
          (∑ y ∈ f.support, ‖f y‖ * U x y : ℝ) := by
        simp only [finiteEmbedding, g, Finsupp.linearCombination_apply]
        rw [Finsupp.sum_mapRange_index (by simp)]
        simp only [Finsupp.sum, map_sum, map_smul, lp.coeFn_sum, Finset.sum_apply,
          lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hB, Complex.ofReal_sum,
          Complex.ofReal_mul]
      have hnn : 0 ≤ ∑ y ∈ f.support, ‖f y‖ * U x y :=
        Finset.sum_nonneg (fun y _ => mul_nonneg (norm_nonneg _) (hU x y))
      rw [hright, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
      simp only [L, Finsupp.linearCombination_apply, Finsupp.sum,
        lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      calc
        ‖∑ y ∈ f.support, f y * col y x‖ ≤
            ∑ y ∈ f.support, ‖f y * col y x‖ := norm_sum_le _ _
        _ ≤ ∑ y ∈ f.support, ‖f y‖ * U x y := by
          apply Finset.sum_le_sum
          intro y _
          simpa [col, norm_mul, Complex.norm_real, Real.norm_eq_abs] using
            mul_le_mul_of_nonneg_left (hKU x y) (norm_nonneg (f y))
    calc
      ‖L f‖ ≤ ‖B (finiteEmbedding g)‖ := lp.norm_mono (by norm_num) hpoint
      _ ≤ ‖B‖ * ‖finiteEmbedding g‖ := B.le_opNorm _
      _ = ‖B‖ * ‖finiteEmbedding f‖ := by rw [hg, norm_positivePart]
  refine ⟨L.extendOfNorm finiteEmbedding,
    LinearMap.opNorm_extendOfNorm_le finiteEmbedding_dense (norm_nonneg _) hLn, ?_⟩
  intro x y
  have h := LinearMap.extendOfNorm_eq (f := L) finiteEmbedding_dense ⟨‖B‖, hLn⟩
    (Finsupp.single y (1 : ℂ))
  simp only [finiteEmbedding_single] at h
  rw [h]
  simp [L, col]

end KernelDomination

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_ProductMeasure_Association
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Association, disjoint witnesses and the BK inequality. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section Restriction

theorem measurable_set_restrict (s : Set E) :
    Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
  measurable_setOfPred.comp (Measurable.of_eval
    (fun e => (measurable_pi_apply e.val).comp MeasurableEquiv.setOfPred.symm.measurable))

 
theorem law_map_restrict (p : unitInterval) (s : Set E) :
    (law p : Measure (Set E)).map (fun ω => (Subtype.val ⁻¹' ω : Set s)) = law p := by
  have hm := measurable_set_restrict s
  unfold law
  rw [setBernoulli_eq_map, Measure.map_map hm measurable_setOfPred]
  have he : (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ∘
      (fun f : E → Prop => {e | f e}) =
      (fun f : s → Prop => {e | f e}) ∘ s.domRestrict := rfl
  rw [he, ← Measure.map_map measurable_setOfPred (by fun_prop),
    Measure.infinitePi_map_restrict', setBernoulli_eq_map]
  simp only [Set.mem_univ]

end Restriction

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Graph_Paths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bond paths, degree bounds and positivity of the critical parameter. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section DegreeBound
attribute [local instance] Classical.propDecidable

 theorem finite_steps (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    Set.Finite {ey : E × V | G ey.1 = s(x,ey.2)} := by
  apply ((hloc x).prod (finite_neighbors hloc x)).subset
  rintro ⟨e,y⟩ he
  change G e = s(x,y) at he
  exact ⟨by change x ∈ G e; rw [he]; simp, e, he⟩

end DegreeBound

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Sprinkling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sprinkling estimates for finite and infinite graph operators. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section Schur
attribute [local instance] Classical.propDecidable

 
theorem exists_operator_of_row_column_bound (U : V → V → ℝ) (D : ℝ)
    (hD : 0 ≤ D) (hU : ∀ x y, 0 ≤ U x y)
    (hrow : ∀ x (s : Finset V), ∑ y ∈ s, U x y ≤ D)
    (hcol : ∀ y (s : Finset V), ∑ x ∈ s, U x y ≤ D) :
    ∃ A : Hilbert V →L[ℂ] Hilbert V, ‖A‖ ≤ D ∧
      ∀ x y, A (lp.single 2 y (1 : ℂ)) x = (U x y : ℂ) := by
  have hentry (x y : V) : U x y ≤ D := by simpa using hrow x {y}
  have hcm (y : V) : Memℓp (fun x => (U x y : ℂ)) 2 := by
    apply (memℓp_gen_iff'' (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
    refine ⟨D^2, sq_nonneg _, fun s => ?_⟩
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    calc
      ∑ x ∈ s, U x y ^ 2 ≤ ∑ x ∈ s, D * U x y := by
        apply Finset.sum_le_sum
        intro x _
        nlinarith [hentry x y, hU x y]
      _ = D * ∑ x ∈ s, U x y := by rw [Finset.mul_sum]
      _ ≤ D * D := mul_le_mul_of_nonneg_left (hcol y s) hD
      _ = D^2 := by ring
  let col (y : V) : Hilbert V := ⟨fun x => (U x y : ℂ), hcm y⟩
  let L : (V →₀ ℂ) →ₗ[ℂ] Hilbert V := Finsupp.linearCombination ℂ col
  have hn (f : V →₀ ℂ) : ‖L f‖ ≤ D * ‖finiteEmbedding f‖ := by
    apply lp.norm_le_of_forall_sum_le (by norm_num)
      (mul_nonneg hD (norm_nonneg _))
    intro s
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    have hpoint (x : V) : ‖L f x‖^2 ≤ D * ∑ y ∈ f.support, ‖f y‖^2 * U x y := by
      have hn0 : 0 ≤ ∑ y ∈ f.support, ‖f y‖ * U x y :=
        Finset.sum_nonneg fun y _ => mul_nonneg (norm_nonneg _) (hU x y)
      have hn1 : ‖L f x‖ ≤ ∑ y ∈ f.support, ‖f y‖ * U x y := by
        simp only [L, Finsupp.linearCombination_apply, Finsupp.sum, lp.coeFn_sum,
          Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro y _
        simp [col, abs_of_nonneg (hU x y)]
      have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul f.support
        (f := fun y => U x y) (g := fun y => ‖f y‖^2 * U x y)
        (r := fun y => ‖f y‖ * U x y)
        (fun y _ => hU x y)
        (fun y _ => mul_nonneg (sq_nonneg _) (hU x y))
        (fun y _ => by nlinarith)
      exact (sq_le_sq₀ (norm_nonneg _) hn0 |>.mpr hn1).trans
        (hcs.trans (mul_le_mul_of_nonneg_right (hrow x f.support)
          (Finset.sum_nonneg fun y _ => mul_nonneg (sq_nonneg _) (hU x y))))
    calc
      ∑ x ∈ s, ‖L f x‖^2 ≤ ∑ x ∈ s, D * ∑ y ∈ f.support, ‖f y‖^2 * U x y :=
        Finset.sum_le_sum fun x _ => hpoint x
      _ = D * ∑ y ∈ f.support, ‖f y‖^2 * ∑ x ∈ s, U x y := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
      _ ≤ D * ∑ y ∈ f.support, ‖f y‖^2 * D := by
        apply mul_le_mul_of_nonneg_left _ hD
        apply Finset.sum_le_sum
        intro y _
        exact mul_le_mul_of_nonneg_left (hcol y s) (sq_nonneg _)
      _ = D^2 * ∑ y ∈ f.support, ‖finiteEmbedding f y‖^2 := by
        simp only [finiteEmbedding_apply, ← Finset.sum_mul]
        ring
      _ ≤ D^2 * ‖finiteEmbedding f‖^2 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          (lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
            (finiteEmbedding f) f.support)
      _ = (D * ‖finiteEmbedding f‖)^2 := by ring
  refine ⟨L.extendOfNorm finiteEmbedding,
    LinearMap.opNorm_extendOfNorm_le finiteEmbedding_dense hD hn, ?_⟩
  intro x y
  have he := LinearMap.extendOfNorm_eq (f := L) finiteEmbedding_dense ⟨D, hn⟩
    (Finsupp.single y (1 : ℂ))
  simp only [finiteEmbedding_single] at he
  rw [he]
  simp [L, col]

end Schur

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Criticality_Sharpness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Russo formulae, exterior exposure and subcritical sharpness. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SharpnessSusceptibility
open Filter Topology
attribute [local instance] Classical.propDecidable Classical.decEq


theorem internalEdges_mono (G : BondGraph V E) {S T : Set V} (h : S ⊆ T) :
    internalEdges G S ⊆ internalEdges G T := fun _ he x hx => h (he x hx)

end SharpnessSusceptibility

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Exploration_Goodness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pruning, finite and infinite goodness events and uniform bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section PruningGeometry
attribute [local instance] Classical.propDecidable Classical.decEq


theorem conn_first_entry (G : BondGraph V E) (W : Set V) (ω : Set E)
    {x y : V} (hx : x ∉ W) (hy : y ∈ W) (hxy : Conn G ω x y) :
    ∃ a b e, a ∉ W ∧ b ∈ W ∧ e ∈ ω ∧ G e = s(a,b) ∧
      Conn G (ω ∩ internalEdges G Wᶜ) x a := by
  let Entry : Prop := ∃ a b e, a ∉ W ∧ b ∈ W ∧ e ∈ ω ∧ G e = s(a,b) ∧
      Conn G (ω ∩ internalEdges G Wᶜ) x a
  have haux : Conn G (ω ∩ internalEdges G Wᶜ) x y ∨ Entry := by
    clear hy
    induction hxy with
    | refl => exact Or.inl (conn_refl _ _ _)
    | @tail a b hxa hab ih =>
      rcases ih with ih | ih
      · have ha : a ∉ W := conn_internal_endpoint G Wᶜ hx ih
        obtain ⟨e,he,heq⟩ := hab
        by_cases hb : b ∈ W
        · exact Or.inr ⟨a,b,e,ha,hb,he,heq,ih⟩
        · exact Or.inl (ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G Wᶜ e a b heq).mpr ⟨ha,hb⟩⟩,heq⟩)
      · exact Or.inr ih
  rcases haux with h | h
  · exact ((conn_internal_endpoint G Wᶜ hx h) hy).elim
  · exact h


end PruningGeometry

section GoodnessLaw
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurableSet_finite_restriction (Q : Finset E) (A : Set (Set E)) :
    MeasurableSet {ω : Set E | ω ∩ (Q : Set E) ∈ A} := by
  have hm : MeasurableSet {η : Set (Q : Set E) | (Subtype.val '' η : Set E) ∈ A} := .of_discrete
  convert hm.preimage (measurable_set_restrict (Q : Set E)) using 1
  all_goals try with_reducible_and_instances rfl
  ext ω
  have he : (Subtype.val '' (Subtype.val ⁻¹' ω : Set (Q : Set E)) : Set E) = ω ∩ (Q : Set E) := by
    ext e
    simp [and_comm]
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,he]

theorem measurableSet_cappedBadGoodness (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (M : ℕ) (L : ℝ) : MeasurableSet {ω | CappedBadGoodness G ω x M L} := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
  have he : {ω | CappedBadGoodness G ω x M L} =
      {ω | ω ∩ (Q : Set E) ∈ {η | CappedBadGoodness G η x M L}} := by
    ext ω
    exact cappedBadGoodness_local G hloc x M L ω
  rw [he]
  exact measurableSet_finite_restriction Q _


end GoodnessLaw

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Spectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isoperimetric energy, symmetric walks and invariant operator traces. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section IsoperimetricEnergy
attribute [local instance] Classical.propDecidable


theorem neighbors_card_le_degree (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    (neighbors G hloc x).card ≤ degree G x := by
  let : Fintype (Step G x) := (finite_steps G hloc x).fintype
  let p : Step G x → {y // y ∈ neighbors G hloc x} :=
    fun d => ⟨d.val.2, (mem_neighbors G hloc x d.val.2).mpr ⟨d.val.1,d.property⟩⟩
  have hp : Function.Surjective p := by
    intro y
    obtain ⟨e,he⟩ := (mem_neighbors G hloc x y.val).mp y.property
    exact ⟨⟨(e,y.val),he⟩,Subtype.ext rfl⟩
  simpa only [degree,Nat.card_eq_fintype_card,Fintype.card_coe] using
    Fintype.card_le_of_surjective p hp

end IsoperimetricEnergy

section InvariantOperatorTrace
open scoped ComplexOrder InnerProduct
attribute [local instance] Classical.propDecidable

theorem operator_kernel_hasSum (A : Hilbert V →L[ℂ] Hilbert V) (f : Hilbert V) (x : V) :
    HasSum (fun y => matrixCoeff A x y * f y) (A f x) := by
  have h := ((lp.evalCLM ℂ (fun _ : V => ℂ) 2 x).comp A).hasSum
    (lp.hasSum_single (by norm_num : (2:ℝ≥0∞) ≠ ⊤) f)
  change HasSum (fun y => A (lp.single 2 y (f y)) x) (A f x) at h
  have heq : (fun y : V => A (lp.single 2 y (f y)) x) =
      (fun y => matrixCoeff A x y * f y) := by
    funext y
    have he : lp.single (E := fun _ : V => ℂ) 2 y (f y) =
        f y • lp.single 2 y (1:ℂ) := by
      rw [← lp.single_smul]; simp
    simp [he, matrixCoeff, mul_comm]
  rw [heq] at h
  exact h

@[simp] theorem matrixCoeff_mul (A B : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    matrixCoeff (A*B) x y = ∑' z, matrixCoeff A x z * matrixCoeff B z y := by
  exact (operator_kernel_hasSum A (B (lp.single 2 y (1:ℂ))) x).tsum_eq.symm

end InvariantOperatorTrace

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_Geometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical parameters and the geometry, selection and traces of splices. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteExchange
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteExchange_card (M ω η : Finset E) :
    (finiteExchange M ω η).card = (ω \ M).card+(η ∩ M).card := by
  apply Finset.card_union_of_disjoint
  exact Finset.disjoint_left.mpr fun e he he' => (Finset.mem_sdiff.mp he).2 (Finset.mem_inter.mp he').2

theorem finiteExchange_card_sum (M ω η : Finset E) :
    (finiteExchange M ω η).card+(finiteExchange M η ω).card = ω.card+η.card := by
  rw [finiteExchange_card,finiteExchange_card]
  have hω := Finset.card_sdiff_add_card_inter ω M
  have hη := Finset.card_sdiff_add_card_inter η M
  omega

theorem finiteExchange_subset (M Q ω η : Finset E) (hω : ω ⊆ Q) (hη : η ⊆ Q) :
    finiteExchange M ω η ⊆ Q := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact hω (Finset.mem_sdiff.mp he).1
  · exact hη (Finset.mem_inter.mp he).1

 
theorem bernoulliWeight_exchange (M Q ω η : Finset E) (hω : ω ⊆ Q) (hη : η ⊆ Q)
    (p : ℝ) :
    bernoulliWeight Q (finiteExchange M ω η) p * bernoulliWeight Q (finiteExchange M η ω) p =
      bernoulliWeight Q ω p * bernoulliWeight Q η p := by
  have hc := finiteExchange_card_sum M ω η
  have hcω := Finset.card_le_card hω
  have hcη := Finset.card_le_card hη
  have hcω' := Finset.card_le_card (finiteExchange_subset M Q ω η hω hη)
  have hcη' := Finset.card_le_card (finiteExchange_subset M Q η ω hη hω)
  have hd : (Q.card-(finiteExchange M ω η).card)+(Q.card-(finiteExchange M η ω).card) =
      (Q.card-ω.card)+(Q.card-η.card) := by omega
  unfold bernoulliWeight
  calc
    _ = p^((finiteExchange M ω η).card+(finiteExchange M η ω).card) *
      (1-p)^((Q.card-(finiteExchange M ω η).card)+(Q.card-(finiteExchange M η ω).card)) := by
        rw [pow_add,pow_add]; ring
    _ = p^(ω.card+η.card)*(1-p)^((Q.card-ω.card)+(Q.card-η.card)) := by rw [hc,hd]
    _ = _ := by rw [pow_add,pow_add]; ring

end FiniteExchange

section DeletionGoodness
attribute [local instance] Classical.propDecidable Classical.decEq


theorem contactSet_deleted_cluster (G : BondGraph V E) (ω : Set E) (A : Set V)
    (y : V) (hy : y ∉ A) :
    let B := cluster G (ω ∩ internalEdges G Aᶜ) y
    contactSet G ω B = deletionContacts G ω A B := by
  let ζ := ω ∩ internalEdges G Aᶜ
  let B := cluster G ζ y
  have hB : B ⊆ Aᶜ := slit_cluster_subset G A ω y hy
  ext e
  constructor
  · rintro ⟨he,a,b,hab,ha,hb⟩
    refine ⟨he,a,ha,b,?_,hab⟩
    by_contra hbA
    have heζ : e ∈ ζ := ⟨he,(mem_internalEdges_of_ends G Aᶜ e a b hab).mpr ⟨hB ha,hbA⟩⟩
    exact hb ((edge_cluster_sides G ζ y heζ hab).mp ha)
  · rintro ⟨he,a,ha,b,hb,hab⟩
    exact ⟨he,a,b,hab,ha,fun hh => hB hh hb⟩



end DeletionGoodness

section SpliceSelection
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem exists_maximal_splice_index (G : BondGraph V E) (η : ℕ → Set E) (y : ℕ → V)
    (k j : ℕ) (hj : j ≤ k)
    (hchain : ∀ i ∈ Finset.Icc 1 k, Conn G (η i) (y i) (y (i-1)))
    (S : Set V) (hyj : y j ∈ S) (hyk : y k ∉ S) :
    ∃ i ∈ Finset.Icc (j+1) k,
      ((cluster G (η i) (y i)) ∩ S).Nonempty ∧ y i ∉ S ∧
      ∀ l, i < l → l ≤ k → Disjoint (cluster G (η l) (y l)) S := by
  have hjk : j < k := by
    by_contra h
    have hEq : j = k := by omega
    exact hyk (hEq ▸ hyj)
  let T := (Finset.Icc (j+1) k).filter fun i => ((cluster G (η i) (y i)) ∩ S).Nonempty
  have hT : T.Nonempty := by
    refine ⟨j+1,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩,?_⟩⟩
    refine ⟨y j,?_,hyj⟩
    simpa only [Nat.add_sub_cancel,cluster,Set.mem_ofPred_eq] using hchain (j+1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  let i := T.max' hT
  have hi : i ∈ T := Finset.max'_mem T hT
  obtain ⟨hiI,hiS⟩ := Finset.mem_filter.mp hi
  have hiU := (Finset.mem_Icc.mp hiI).2
  have hiL := (Finset.mem_Icc.mp hiI).1
  have hl (l : ℕ) (hil : i < l) (hlk : l ≤ k) : Disjoint (cluster G (η l) (y l)) S := by
    apply Set.disjoint_left.mpr
    intro z hz hzS
    have hlT : l ∈ T := Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega,hlk⟩,⟨z,hz,hzS⟩⟩
    have hli : l ≤ i := Finset.le_max' T l hlT
    omega
  refine ⟨i,hiI,hiS,?_,hl⟩
  intro hyi
  by_cases hik : i = k
  · exact hyk (hik ▸ hyi)
  · have hic : y i ∈ cluster G (η (i+1)) (y (i+1)) := by
      simpa only [Nat.add_sub_cancel,cluster,Set.mem_ofPred_eq] using hchain (i+1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
    exact Set.disjoint_left.mp (hl (i+1) (by omega) (by omega)) hic hyi

 

theorem exists_splice_contact (G : BondGraph V E) (η : Set E) (S : Set V) (y : V)
    (hy : y ∉ S) (hmeet : (cluster G η y ∩ S).Nonempty) :
    ∃ e a b, e ∈ η ∧ G e = s(a,b) ∧ a ∈ S ∧
      b ∈ cluster G (η ∩ internalEdges G Sᶜ) y := by
  obtain ⟨v,hv,hvS⟩ := hmeet
  obtain ⟨b,a,e,_,ha,he,hab,hb⟩ := conn_first_entry G S η hy hvS hv
  exact ⟨e,a,b,he,hab.trans (Sym2.eq_swap),ha,hb⟩

 
theorem splice_cluster_cap (G : BondGraph V E) (ω η : Set E) (x y : V)
    (hy : y ∉ cluster G ω x) (e : E) (a b : V)
    (he : G e = s(a,b)) (heη : e ∈ η) (ha : a ∈ cluster G ω x)
    (hb : b ∈ cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y)
    (N M : ℕ) (hS : (cluster G ω x).Finite) (hN : (cluster G ω x).ncard ≤ N)
    (hC : (cluster G η y).Finite) (hM : (cluster G η y).ncard ≤ M) :
    let S := cluster G ω x
    let B := cluster G (η ∩ internalEdges G Sᶜ) y
    (cluster G (spliceField G S B e ω η) x).Finite ∧
      (cluster G (spliceField G S B e ω η) x).ncard ≤ N+M := by
  let S := cluster G ω x
  let B := cluster G (η ∩ internalEdges G Sᶜ) y
  have hBC : B ⊆ cluster G η y := fun _ hz => conn_mono G Set.inter_subset_left hz
  have hB : B.Finite := hC.subset hBC
  dsimp only
  rw [splice_cluster G ω η x y hy e a b he heη ha hb]
  refine ⟨hS.union hB,?_⟩
  exact (Set.ncard_union_le _ _).trans (Nat.add_le_add hN ((Set.ncard_le_ncard hBC hC).trans hM))



end SpliceSelection

section SpliceTrace
attribute [local instance] Classical.propDecidable Classical.decEq



theorem SpliceTrace.cluster_subset (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) : cluster G ω x ⊆ cluster G ωf x := by
  induction h with
  | stop => exact Set.Subset.rfl
  | @step j i ω e a b rest ωf _ _ _ _ hy he hab ha hb ht ih =>
    apply Set.Subset.trans _ ih
    rw [splice_cluster G ω (η i) x (y i) hy e a b hab he ha hb]
    exact Set.subset_union_left



end SpliceTrace

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_GapCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gap Codes for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SpliceWeight
attribute [local instance] Classical.propDecidable Classical.decEq


theorem domainBits_exchange (Q : Finset E) (M ω η : Set E) :
    domainBits Q (exchangeOn M ω η) =
      finiteExchange (domainBits Q M) (domainBits Q ω) (domainBits Q η) := by
  ext e
  simp only [mem_domainBits,exchangeOn,Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff,
    finiteExchange,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]
  tauto



theorem spliceTupleWeight_nonneg (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (s : SpliceState E) : 0 ≤ spliceTupleWeight Q J p s := by
  exact mul_nonneg (bernoulliWeight_nonneg _ _ p)
    (Finset.prod_nonneg fun _ _ => bernoulliWeight_nonneg _ _ p)

 
theorem spliceTupleWeight_exchange (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (s : SpliceState E) (M : Set E) (i : ℕ) (hi : i ∈ J) :
    spliceTupleWeight Q J p (exchangeState M i s) = spliceTupleWeight Q J p s := by
  unfold spliceTupleWeight
  rw [← Finset.mul_prod_erase J (fun l =>
    bernoulliWeight Q (domainBits Q ((exchangeState M i s).2 l)) p) hi,
    ← Finset.mul_prod_erase J (fun l => bernoulliWeight Q (domainBits Q (s.2 l)) p) hi]
  have herase : (∏ l ∈ J.erase i,
      bernoulliWeight Q (domainBits Q ((exchangeState M i s).2 l)) p) =
      ∏ l ∈ J.erase i, bernoulliWeight Q (domainBits Q (s.2 l)) p := by
    apply Finset.prod_congr rfl
    intro l hl
    rw [exchangeState_away _ _ _ _ (Finset.mem_erase.mp hl).1]
  rw [herase,exchangeState_first,exchangeState_at,← mul_assoc,← mul_assoc,
    domainBits_exchange,domainBits_exchange,
    bernoulliWeight_exchange _ _ _ _ (domainBits_subset Q s.1) (domainBits_subset Q (s.2 i)) p]

 
theorem SpliceExecution.weight (G : BondGraph V E) (x : V)
    (s s' : SpliceState E) (code : List (ℕ × E))
    (h : SpliceExecution G x s code s') (Q : Finset E) (J : Finset ℕ)
    (hJ : ∀ q ∈ code, q.1 ∈ J) (p : ℝ) :
    spliceTupleWeight Q J p s' = spliceTupleWeight Q J p s := by
  induction h with
  | nil => rfl
  | cons s s' s'' q code hstep hrest ih =>
    rw [ih (fun r hr => hJ r (List.mem_cons_of_mem _ hr))]
    obtain ⟨y,a,b,_,_,_,_,_,rfl⟩ := hstep
    exact spliceTupleWeight_exchange Q J p s _ q.1 (hJ q (List.mem_cons_self ..))



end SpliceWeight

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section InverseCodeMass
attribute [local instance] Classical.propDecidable Classical.decEq


theorem volume_contactInterval (K a : ℕ) (ha : a < K) :
    volume (contactInterval K a) = ENNReal.ofReal ((K:ℝ)⁻¹) := by
  have hK : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hleft : (a:ℝ)/K ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨by positivity,(div_le_one hK).mpr ?_⟩
    exact_mod_cast (Nat.le_of_lt ha)
  have hright : ((a+1:ℕ):ℝ)/K ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨by positivity,(div_le_one hK).mpr ?_⟩
    exact_mod_cast (show a+1 ≤ K by omega)
  let lo : unitInterval := ⟨_,hleft⟩
  let hi : unitInterval := ⟨_,hright⟩
  have heq : contactInterval K a = Set.Ico lo hi := rfl
  rw [heq,unitInterval.volume_Ico]
  congr 1
  dsimp only [lo,hi]
  push_cast
  field_simp
  ring



end InverseCodeMass

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_Replay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replay for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RemoteSpliceGeometry
attribute [local instance] Classical.propDecidable Classical.decEq



theorem GraphSeparated.symm (G : BondGraph V E) (A B : Set V)
    (h : GraphSeparated G A B) : GraphSeparated G B A := by
  refine ⟨h.1.symm,?_⟩
  intro b hb a ha hab
  obtain ⟨e,he⟩ := hab
  exact h.2 a ha b hb ⟨e,he.trans (Sym2.eq_swap ..)⟩

theorem GraphSeparated.mono (G : BondGraph V E) {A B C D : Set V}
    (h : GraphSeparated G A B) (hC : C ⊆ A) (hD : D ⊆ B) : GraphSeparated G C D := by
  exact ⟨h.1.mono hC hD,fun c hc d hd => h.2 c (hC hc) d (hD hd)⟩

theorem GraphSeparated.no_shared_incidence (G : BondGraph V E) (A B : Set V)
    (h : GraphSeparated G A B) (e : E) (a b : V) (ha : a ∈ A) (hb : b ∈ B)
    (hea : a ∈ G e) (heb : b ∈ G e) : False := by
  have hne : a ≠ b := by
    rintro rfl
    exact Set.disjoint_left.mp h.1 ha hb
  exact h.2 a ha b hb ⟨e,(Sym2.mem_and_mem_iff hne).mp ⟨hea,heb⟩⟩

 

theorem slit_cluster_remove_remote (G : BondGraph V E) (η : Set E) (S H : Set V)
    (y : V) (hy : y ∉ S)
    (hsep : GraphSeparated G (cluster G (η ∩ internalEdges G Sᶜ) y) H) :
    cluster G (η ∩ internalEdges G (S \ H)ᶜ) y = cluster G (η ∩ internalEdges G Sᶜ) y := by
  apply Set.Subset.antisymm
  · intro v hv
    induction hv with
    | refl => exact conn_refl G _ y
    | @tail a b hya hab ih =>
      obtain ⟨e,he,hab⟩ := hab
      have hbH : b ∉ H := fun hb => hsep.2 a ih b hb ⟨e,hab⟩
      have hbS : b ∉ S := by
        have hb := ((mem_internalEdges_of_ends G _ e a b hab).mp he.2).2
        exact fun h => hb ⟨h,hbH⟩
      have haS := slit_cluster_subset G S η y hy ih
      exact ih.tail ⟨e,⟨he.1,(mem_internalEdges_of_ends G _ e a b hab).mpr ⟨haS,hbS⟩⟩,hab⟩
  · exact fun _ h => conn_mono G
      (Set.inter_subset_inter_right _ (internalEdges_mono G (by
        intro v hv hvS
        exact hv hvS.1))) h

 

theorem spliceMask_remove_remote (G : BondGraph V E) (S B H : Set V) (e : E)
    (hsep : GraphSeparated G B H) : spliceMask G (S \ H) B e = spliceMask G S B e := by
  ext f
  simp only [spliceMask,Set.mem_insert_iff,Set.mem_ofPred_eq]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨⟨b,hb,hbf⟩,hi⟩
    refine ⟨⟨b,hb,hbf⟩,?_⟩
    intro v hv hvS
    have hvH : v ∉ H := fun hh => hsep.no_shared_incidence G B H f b v hb hh hbf hv
    exact hi v hv ⟨hvS,hvH⟩
  · rintro ⟨hb,hi⟩
    exact ⟨hb,fun v hv h => hi v hv h.1⟩

 
theorem spliceMask_incident (G : BondGraph V E) (S B : Set V) (e : E)
    (b : V) (hb : b ∈ B) (heb : b ∈ G e) :
    ∀ f ∈ spliceMask G S B e, ∃ v ∈ B, v ∈ G f := by
  intro f hf
  rcases Set.mem_insert_iff.mp hf with rfl | hf
  · exact ⟨b,hb,heb⟩
  · exact hf.1



end RemoteSpliceGeometry

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RemoteReplay
attribute [local instance] Classical.propDecidable Classical.decEq



theorem SpliceTrace.replay_eq (G : BondGraph V E) (x : V) (η : ℕ → Set E) (y : ℕ → V)
    (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) : replaySplice G x η y steps ω = ωf := by
  induction h with
  | stop => rfl
  | step => assumption

 

theorem SpliceTrace.remote_replay (G : BondGraph V E) (x : V) (η : ℕ → Set E) (y : ℕ → V)
    (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) (H : Set V) (ω₀ : Set E)
    (hroot : cluster G ω₀ x = cluster G ω x \ H)
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω x) H)
    (hzH : y k ∉ H) :
    SpliceTrace G x η y k j ω₀ steps (replaySplice G x η y steps ω₀) ∧
      cluster G (replaySplice G x η y steps ω₀) x = cluster G ωf x \ H ∧
      replayMasks G x η y steps ω₀ = replayMasks G x η y steps ω ∧
      replayContacts G x η y steps ω₀ = replayContacts G x η y steps ω := by
  induction h generalizing ω₀ with
  | stop j ω hs =>
    refine ⟨SpliceTrace.stop j ω₀ ?_,hroot,rfl,rfl⟩
    rw [hroot]
    exact ⟨hs,hzH⟩
  | @step j i ω e a b rest ωf hn hji hik hmax hy he hab ha hb ht ih =>
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let ω' := spliceField G S B e ω (η i)
    let S₀ := cluster G ω₀ x
    let B₀ := cluster G (η i ∩ internalEdges G S₀ᶜ) (y i)
    let ω₀' := spliceField G S₀ B₀ e ω₀ (η i)
    have hC : cluster G ω' x = S ∪ B := splice_cluster G ω (η i) x (y i) hy e a b hab he ha hb
    have hBo : B ⊆ Sᶜ := slit_cluster_subset G S (η i) (y i) hy
    have hretain : cluster G ω' x ⊆ cluster G ωf x := ht.cluster_subset G x η y k i ω' ωf rest
    have hBT : B ⊆ cluster G ωf x \ S := by
      intro v hv
      refine ⟨hretain ?_,hBo hv⟩
      rw [hC]
      exact Or.inr hv
    have hsepB : GraphSeparated G B H := hsep.mono G hBT Set.Subset.rfl
    have hBB : B₀ = B := by
      dsimp only [B₀,S₀]
      rw [hroot]
      exact slit_cluster_remove_remote G (η i) S H (y i) hy hsepB
    have haH : a ∉ H := fun hh => hsepB.2 b hb a hh ⟨e,hab.trans (Sym2.eq_swap ..)⟩
    have ha₀ : a ∈ S₀ := by rw [show S₀ = S \ H from hroot]; exact ⟨ha,haH⟩
    have hy₀ : y i ∉ S₀ := by rw [show S₀ = S \ H from hroot]; exact fun h => hy h.1
    have hb₀ : b ∈ B₀ := hBB.symm ▸ hb
    have hC₀ : cluster G ω₀' x = S₀ ∪ B₀ :=
      splice_cluster G ω₀ (η i) x (y i) hy₀ e a b hab he ha₀ hb₀
    have hroot' : cluster G ω₀' x = cluster G ω' x \ H := by
      rw [hC₀,hC,hBB,show S₀ = S \ H from hroot]
      ext v
      constructor
      · rintro (⟨hv,hvH⟩ | hv)
        · exact ⟨Or.inl hv,hvH⟩
        · exact ⟨Or.inr hv,fun hvH => Set.disjoint_left.mp hsepB.1 hv hvH⟩
      · rintro ⟨hv,hvH⟩
        exact hv.elim (fun h => Or.inl ⟨h,hvH⟩) Or.inr
    have hsep' : GraphSeparated G (cluster G ωf x \ cluster G ω' x) H := by
      apply hsep.mono G _ Set.Subset.rfl
      intro v hv
      refine ⟨hv.1,fun h => hv.2 ?_⟩
      rw [hC]
      exact Or.inl h
    obtain ⟨ht₀,hfinal,hmasks,hcontacts⟩ := ih ω₀' hroot' hsep'
    have hn₀ : y k ∉ S₀ := by rw [show S₀ = S \ H from hroot]; exact fun h => hn h.1
    have hmax₀ : ∀ l, i < l → l ≤ k → Disjoint (cluster G (η l) (y l)) S₀ := by
      intro l hil hlk
      apply (hmax l hil hlk).mono Set.Subset.rfl
      rw [show S₀ = S \ H from hroot]
      exact Set.sdiff_subset
    have hmask : spliceMask G S₀ B₀ e = spliceMask G S B e := by
      rw [hBB,show S₀ = S \ H from hroot,spliceMask_remove_remote G S B H e hsepB]
    refine ⟨SpliceTrace.step j i ω₀ e a b rest _ hn₀ hji hik hmax₀ hy₀ he hab ha₀ hb₀ ht₀,
      hfinal,?_,?_⟩
    · change (i,spliceMask G S₀ B₀ e)::replayMasks G x η y rest ω₀' =
      (i,spliceMask G S B e)::replayMasks G x η y rest ω'
      rw [hmask,hmasks]
    · change contactSet G (η i) B₀::replayContacts G x η y rest ω₀' =
        contactSet G (η i) B::replayContacts G x η y rest ω'
      rw [hBB,hcontacts]

end RemoteReplay

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeterministicReplay
attribute [local instance] Classical.propDecidable Classical.decEq



theorem followsContactRule_cons (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (choose : ℕ → Set E → E) (i : ℕ) (e : E)
    (rest : List (ℕ × E)) (ω : Set E) :
    FollowsContactRule G x η y choose ((i,e)::rest) ω ↔
      choose i (contactSet G (η i)
        (cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i))) = e ∧
      FollowsContactRule G x η y choose rest
        (spliceField G (cluster G ω x)
          (cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)) e ω (η i)) := by
  simp only [FollowsContactRule,replayContacts,List.forall₂_cons]



theorem SpliceTrace.seeded_unique (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ω₁ ω₂ : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η y k j ω c₁ ω₁)
    (h₂ : SpliceTrace G x η y k j ω c₂ ω₂) (choose : ℕ → Set E → E)
    (hc₁ : FollowsContactRule G x η y choose c₁ ω)
    (hc₂ : FollowsContactRule G x η y choose c₂ ω) : c₁ = c₂ ∧ ω₁ = ω₂ := by
  induction h₁ generalizing c₂ ω₂ with
  | stop j ω hs =>
    cases h₂ with
    | stop => exact ⟨rfl,rfl⟩
    | step _ _ _ _ _ _ _ _ hn => exact (hn hs).elim
  | @step j i ω e a b rest ω₁ hn hji hik hmax hy he hab ha hb ht ih =>
    cases h₂ with
    | stop _ _ hs => exact (hn hs).elim
    | step _ l _ f c d tail ω₂ hn₂ hjl hlk hmax₂ hy₂ hf hcd hc hd ht₂ =>
      have haC : a ∈ cluster G (η i) (y i) :=
        (edge_cluster_sides G (η i) (y i) he hab).mpr (conn_mono G Set.inter_subset_left hb)
      have hcC : c ∈ cluster G (η l) (y l) :=
        (edge_cluster_sides G (η l) (y l) hf hcd).mpr (conn_mono G Set.inter_subset_left hd)
      have hil : i = l := by
        rcases lt_trichotomy i l with hil | hil | hli
        · exact (Set.disjoint_left.mp (hmax l hil hlk) hcC hc).elim
        · exact hil
        · exact (Set.disjoint_left.mp (hmax₂ i hli hik) haC ha).elim
      subst l
      obtain ⟨hec,hrest⟩ := (followsContactRule_cons G x η y choose i e rest ω).mp hc₁
      obtain ⟨hfc,htail⟩ := (followsContactRule_cons G x η y choose i f tail ω).mp hc₂
      have hef : e = f := hec.symm.trans hfc
      rw [← hef] at ht₂ htail ⊢
      obtain ⟨hcodes,houts⟩ := ih ω₂ tail ht₂ hrest htail
      exact ⟨congrArg (List.cons (i,e)) hcodes,houts⟩

end DeterministicReplay

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TraceMaskSupport
attribute [local instance] Classical.propDecidable Classical.decEq


theorem SpliceTrace.masks_incident (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) :
    ∀ f ∈ maskUnion (replayMasks G x η y steps ω),
      ∃ b ∈ cluster G ωf x \ cluster G ω x, b ∈ G f := by
  induction h with
  | stop => simp [replayMasks]
  | @step j i ω e a b rest ωf hn hji hik hmax hy he hab ha hb ht ih =>
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let ω' := spliceField G S B e ω (η i)
    have hC : cluster G ω' x = S ∪ B := splice_cluster G ω (η i) x (y i) hy e a b hab he ha hb
    have hB : B ⊆ Sᶜ := slit_cluster_subset G S (η i) (y i) hy
    have hretain := ht.cluster_subset G x η y k i ω' ωf rest
    intro f hf
    change f ∈ maskUnion ((i,spliceMask G S B e)::replayMasks G x η y rest ω') at hf
    rw [maskUnion_cons] at hf
    rcases hf with hf | hf
    · obtain ⟨v,hv,hvf⟩ := spliceMask_incident G S B e b hb (by simp [hab]) f hf
      refine ⟨v,⟨hretain ?_,hB hv⟩,hvf⟩
      rw [hC]
      exact Or.inr hv
    · obtain ⟨v,hv,hvf⟩ := ih f hf
      refine ⟨v,⟨hv.1,fun h => hv.2 ?_⟩,hvf⟩
      rw [hC]
      exact Or.inl h

 
theorem replaySplice_off_masks (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (steps : List (ℕ × E)) (ω : Set E) (f : E)
    (hf : f ∉ maskUnion (replayMasks G x η y steps ω)) :
    f ∈ replaySplice G x η y steps ω ↔ f ∈ ω := by
  induction steps generalizing ω with
  | nil => rfl
  | cons q rest ih =>
    obtain ⟨i,e⟩ := q
    simp only [replayMasks,maskUnion_cons,Set.mem_union,not_or] at hf
    change f ∈ replaySplice G x η y rest _ ↔ f ∈ ω
    rw [ih _ hf.2]
    simp only [spliceField,mem_exchangeOn,ite_eq_right hf.1]

 
theorem SpliceTrace.masks_disjoint (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x)) :
    Disjoint (maskUnion (replayMasks G x η₁ y₁ c₁ ω₁))
      (maskUnion (replayMasks G x η₂ y₂ c₂ ω₂)) := by
  apply Set.disjoint_left.mpr
  intro f hf₁ hf₂
  obtain ⟨a,ha,hea⟩ := h₁.masks_incident G x η₁ y₁ k j₁ ω₁ ωf c₁ f hf₁
  obtain ⟨b,hb,heb⟩ := h₂.masks_incident G x η₂ y₂ k j₂ ω₂ ωf c₂ f hf₂
  exact hsep.no_shared_incidence G _ _ f a b ha hb hea heb

 

theorem conn_delete_rootBridge (G : BondGraph V E) (ω η : Set E) (x z : V)
    (hη : η ⊆ ω) (e : E) (a b : V) (hab : G e = s(a,b))
    (hb : b ∉ cluster G (ω \ {e}) x) (hz : z ∈ cluster G (ω \ {e}) x)
    (hxz : Conn G η x z) : Conn G (η \ {e}) x z := by
  have hc : Conn G (insert e (η \ {e})) x z := conn_mono G (by
    intro f hf
    by_cases hfe : f = e
    · exact Or.inl hfe
    · exact Or.inr ⟨hf,hfe⟩) hxz
  have hs : η \ {e} ⊆ ω \ {e} := Set.sdiff_subset_sdiff_left hη
  rw [conn_insert_iff G _ e a b x z hab] at hc
  rcases hc with hc | ⟨_,hc⟩ | ⟨hc,_⟩
  · exact hc
  · exact (hb (hz.trans (conn_symm G _ (conn_mono G hs hc)))).elim
  · exact (hb (conn_mono G hs hc)).elim

 
theorem cluster_double_cut (G : BondGraph V E) (ω : Set E) (x : V) (e f : E)
    (a b : V) (hab : G f = s(a,b)) (hb : b ∉ cluster G (ω \ {f}) x) :
    cluster G ((ω \ {e}) \ {f}) x = cluster G (ω \ {e}) x ∩ cluster G (ω \ {f}) x := by
  apply Set.Subset.antisymm
  · intro v hv
    exact ⟨conn_mono G Set.sdiff_subset hv,
      conn_mono G (ω₁ := (ω \ {e}) \ {f}) (ω₂ := ω \ {f}) (fun _ h => ⟨h.1.1,h.2⟩) hv⟩
  · intro v hv
    exact conn_delete_rootBridge G ω (ω \ {e}) x v Set.sdiff_subset f a b hab hb hv.2 hv.1

end TraceMaskSupport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section JointRoot
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem mask_not_crossing_remote (G : BondGraph V E) (U : Set E) (A B : Set V)
    (hU : ∀ e ∈ U, ∃ v ∈ B, v ∈ G e) (hBA : B ⊆ A)
    (e : E) (a b : V) (hab : G e = s(a,b)) (haB : a ∉ B) (hbA : b ∉ A) : e ∉ U := by
  intro he
  obtain ⟨v,hv,hve⟩ := hU e he
  have hvab : v = a ∨ v = b := by simpa only [hab,Sym2.mem_iff] using hve
  rcases hvab with rfl | rfl
  · exact haB hv
  · exact hbA (hBA hv)

 

theorem exchange_patch_symm (U₁ U₂ ω₁ ω₂ ωf : Set E)
    (hdis : Disjoint U₁ U₂)
    (h₁ : ∀ e ∉ U₁, e ∈ ω₁ ↔ e ∈ ωf)
    (h₂ : ∀ e ∉ U₂, e ∈ ω₂ ↔ e ∈ ωf) :
    exchangeOn U₂ ω₁ ω₂ = exchangeOn U₁ ω₂ ω₁ := by
  ext e
  by_cases he₁ : e ∈ U₁
  · have he₂ : e ∉ U₂ := fun h => Set.disjoint_left.mp hdis he₁ h
    simp only [mem_exchangeOn,ite_eq_right he₂,ite_eq_left he₁]
  · by_cases he₂ : e ∈ U₂
    · simp only [mem_exchangeOn,ite_eq_left he₂,ite_eq_right he₁]
    · simp only [mem_exchangeOn,ite_eq_right he₁,ite_eq_right he₂]
      exact (h₁ e he₁).trans (h₂ e he₂).symm

 

theorem SpliceTrace.joint_root (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ i₁ i₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (e₁ e₂ : E) (r₁ r₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ ((i₁,e₁)::r₁) ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ ((i₂,e₂)::r₂) ωf)
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x)) :
    cluster G (exchangeOn (maskUnion (replayMasks G x η₂ y₂ ((i₂,e₂)::r₂) ω₂)) ω₁ ω₂) x =
      cluster G ω₁ x ∩ cluster G ω₂ x := by
  let A₁ := cluster G ω₁ x
  let A₂ := cluster G ω₂ x
  let B₁ := cluster G ωf x \ A₁
  let B₂ := cluster G ωf x \ A₂
  let U₁ := maskUnion (replayMasks G x η₁ y₁ ((i₁,e₁)::r₁) ω₁)
  let U₂ := maskUnion (replayMasks G x η₂ y₂ ((i₂,e₂)::r₂) ω₂)
  let ω₀ := exchangeOn U₂ ω₁ ω₂
  have hsub₁ := h₁.cluster_subset G x η₁ y₁ k j₁ ω₁ ωf ((i₁,e₁)::r₁)
  have hsub₂ := h₂.cluster_subset G x η₂ y₂ k j₂ ω₂ ωf ((i₂,e₂)::r₂)
  have hBA₁ : B₁ ⊆ A₂ := by
    intro v hv
    by_contra hn
    exact Set.disjoint_left.mp hsep.1 hv ⟨hv.1,hn⟩
  have hBA₂ : B₂ ⊆ A₁ := by
    intro v hv
    by_contra hn
    exact Set.disjoint_left.mp hsep.1 ⟨hv.1,hn⟩ hv
  have hU₁ : ∀ e ∈ U₁, ∃ v ∈ B₁, v ∈ G e :=
    h₁.masks_incident G x η₁ y₁ k j₁ ω₁ ωf ((i₁,e₁)::r₁)
  have hU₂ : ∀ e ∈ U₂, ∃ v ∈ B₂, v ∈ G e :=
    h₂.masks_incident G x η₂ y₂ k j₂ ω₂ ωf ((i₂,e₂)::r₂)
  have hdis : Disjoint U₁ U₂ := h₁.masks_disjoint G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf
    ((i₁,e₁)::r₁) ((i₂,e₂)::r₂) h₂ hsep
  have hoff₁ : ∀ e ∉ U₁, e ∈ ω₁ ↔ e ∈ ωf := by
    intro e he
    rw [← h₁.replay_eq G x η₁ y₁ k j₁ ω₁ ωf ((i₁,e₁)::r₁)]
    exact (replaySplice_off_masks G x η₁ y₁ ((i₁,e₁)::r₁) ω₁ e he).symm
  have hoff₂ : ∀ e ∉ U₂, e ∈ ω₂ ↔ e ∈ ωf := by
    intro e he
    rw [← h₂.replay_eq G x η₂ y₂ k j₂ ω₂ ωf ((i₂,e₂)::r₂)]
    exact (replaySplice_off_masks G x η₂ y₂ ((i₂,e₂)::r₂) ω₂ e he).symm
  have hsym : ω₀ = exchangeOn U₁ ω₂ ω₁ := exchange_patch_symm U₁ U₂ ω₁ ω₂ ωf hdis hoff₁ hoff₂
  have hcut₁ := h₁.head_cut G x η₁ y₁ k j₁ i₁ ω₁ ωf e₁ r₁
  have hcut₂ := h₂.head_cut G x η₂ y₂ k j₂ i₂ ω₂ ωf e₂ r₂
  obtain ⟨a,b,hab,_,hb,_⟩ := openMarkedPivotal_oriented G ωf {y₂ k} x
    (h₂.seams_pivotal G x η₂ y₂ k j₂ ω₂ ωf ((i₂,e₂)::r₂) (i₂,e₂) (by simp))
  have hdouble : cluster G ((ωf \ {e₁}) \ {e₂}) x = A₁ ∩ A₂ := by
    rw [cluster_double_cut G ωf x e₁ e₂ a b hab hb,hcut₁,hcut₂]
  change cluster G ω₀ x = A₁ ∩ A₂
  apply Set.Subset.antisymm
  · intro v hv
    induction hv with
    | refl => exact ⟨conn_refl G _ x,conn_refl G _ x⟩
    | @tail a b hxa hab ih =>
      obtain ⟨e,he,hab⟩ := hab
      constructor
      · by_contra hb
        have hno := mask_not_crossing_remote G U₂ A₁ B₂ hU₂ hBA₂ e a b hab
          (fun hh => hh.2 ih.2) hb
        have he₁ : e ∈ ω₁ := by simpa only [ω₀,mem_exchangeOn,ite_eq_right hno] using he
        exact hb ((edge_cluster_sides G ω₁ x he₁ hab).mp ih.1)
      · by_contra hb
        have hno := mask_not_crossing_remote G U₁ A₂ B₁ hU₁ hBA₁ e a b hab
          (fun hh => hh.2 ih.1) hb
        have he₂ : e ∈ ω₂ := by simpa only [hsym,mem_exchangeOn,ite_eq_right hno] using he
        exact hb ((edge_cluster_sides G ω₂ x he₂ hab).mp ih.2)
  · intro v hv
    have hc : Conn G ((ωf \ {e₁}) \ {e₂}) x v := by
      change v ∈ cluster G ((ωf \ {e₁}) \ {e₂}) x
      rw [hdouble]
      exact hv
    have hr := conn_restrict_cluster G ((ωf \ {e₁}) \ {e₂}) x (mem_cluster_self G _ x) hc
    apply conn_mono G _ hr
    intro e he
    have hi : e ∈ internalEdges G (A₁ ∩ A₂) := by
      simpa only [hdouble] using he.2
    have hno : e ∉ U₂ := by
      intro hu
      obtain ⟨b,hb,heb⟩ := hU₂ e hu
      exact hb.2 (hi b heb).2
    have he₁ : e ∈ ω₁ := (h₁.internal_agreement G x η₁ y₁ k j₁ ω₁ ωf
      ((i₁,e₁)::r₁) e (fun a ha => (hi a ha).1)).mp he.1.1.1
    simpa only [ω₀,mem_exchangeOn,ite_eq_right hno] using he₁

end JointRoot

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section MaskExecution
attribute [local instance] Classical.propDecidable Classical.decEq


theorem exchangeState_patchFirst (U τ M : Set E) (i : ℕ) (s : SpliceState E)
    (hdis : Disjoint M U) :
    exchangeState M i (patchFirst U τ s) = patchFirst U τ (exchangeState M i s) := by
  apply Prod.ext
  · ext e
    by_cases heM : e ∈ M
    · have heU : e ∉ U := fun he => Set.disjoint_left.mp hdis heM he
      simp only [exchangeState,patchFirst,mem_exchangeOn,ite_eq_left heM,ite_eq_right heU]
    · by_cases heU : e ∈ U <;>
      simp only [exchangeState,patchFirst,mem_exchangeOn,ite_eq_right heM,heU,ite_true,ite_false]
  · funext l
    by_cases hli : l = i
    · subst l
      ext e
      by_cases heM : e ∈ M
      · have heU : e ∉ U := fun he => Set.disjoint_left.mp hdis heM he
        simp only [exchangeState,patchFirst,Function.update_self,mem_exchangeOn,ite_eq_left heM,ite_eq_right heU]
      · simp only [exchangeState,patchFirst,Function.update_self,mem_exchangeOn,ite_eq_right heM]
    · simp only [exchangeState,patchFirst,Function.update_of_ne hli]

 

theorem runMasks_patchFirst (ms : List (ℕ × Set E)) (U τ : Set E) (s : SpliceState E)
    (hdis : Disjoint (maskUnion ms) U) :
    runMasks ms (patchFirst U τ s) = patchFirst U τ (runMasks ms s) := by
  induction ms generalizing s with
  | nil => rfl
  | cons q ms ih =>
    obtain ⟨i,M⟩ := q
    rw [maskUnion_cons,Set.disjoint_union_left] at hdis
    simp only [runMasks]
    rw [exchangeState_patchFirst U τ M i s hdis.1,ih _ hdis.2]



theorem runMasks_weight (ms : List (ℕ × Set E)) (s : SpliceState E)
    (Q : Finset E) (J : Finset ℕ) (p : ℝ) (hJ : ∀ q ∈ ms, q.1 ∈ J) :
    spliceTupleWeight Q J p (runMasks ms s) = spliceTupleWeight Q J p s := by
  induction ms generalizing s with
  | nil => rfl
  | cons q ms ih =>
    obtain ⟨i,M⟩ := q
    rw [runMasks,ih _ (fun q hq => hJ q (List.mem_cons_of_mem _ hq))]
    exact spliceTupleWeight_exchange Q J p s M i (hJ (i,M) (List.mem_cons_self ..))

 

theorem SpliceTrace.joint_replay_state (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x)) :
    let m₁ := replayMasks G x η₁ y₁ c₁ ω₁
    let m₂ := replayMasks G x η₂ y₂ c₂ ω₂
    let ω₀ := exchangeOn (maskUnion m₂) ω₁ ω₂
    runMasks m₁ (ω₀,η₁) = (ω₂,(runMasks m₁ (ω₁,η₁)).2) := by
  intro m₁ m₂ ω₀
  have hdis := h₁.masks_disjoint G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hsep
  have hroot := h₁.runMasks_first G x η₁ y₁ k j₁ ω₁ ωf c₁ η₁ (by intros; rfl)
  have hpatch : exchangeOn (maskUnion m₂) ωf ω₂ = ω₂ := by
    ext e
    by_cases he : e ∈ maskUnion m₂
    · simp only [mem_exchangeOn,ite_eq_left he]
    · simp only [mem_exchangeOn,ite_eq_right he]
      rw [← h₂.replay_eq G x η₂ y₂ k j₂ ω₂ ωf c₂]
      exact replaySplice_off_masks G x η₂ y₂ c₂ ω₂ e he
  change runMasks m₁ (patchFirst (maskUnion m₂) ω₂ (ω₁,η₁)) = _
  rw [runMasks_patchFirst m₁ _ ω₂ _ hdis]
  change (exchangeOn (maskUnion m₂) (runMasks m₁ (ω₁,η₁)).1 ω₂,_) = _
  rw [hroot,hpatch]

end MaskExecution

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section JointReplay
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem SpliceTrace.endpoint_not_mem_of_ne_nil (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf) (hc : c ≠ []) : y k ∉ cluster G ω x := by
  cases h with
  | stop => exact (hc rfl).elim
  | step _ _ _ _ _ _ _ _ hn => exact hn

 

theorem SpliceTrace.joint_virtual (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hc₁ : c₁ ≠ []) (hc₂ : c₂ ≠ [])
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x)) :
    let ω₀ := exchangeOn (maskUnion (replayMasks G x η₂ y₂ c₂ ω₂)) ω₁ ω₂
    SpliceTrace G x η₁ y₁ k j₁ ω₀ c₁ ω₂ ∧
      replayMasks G x η₁ y₁ c₁ ω₀ = replayMasks G x η₁ y₁ c₁ ω₁ ∧
      replayContacts G x η₁ y₁ c₁ ω₀ = replayContacts G x η₁ y₁ c₁ ω₁ := by
  intro ω₀
  have hroot' : cluster G ω₀ x = cluster G ω₁ x ∩ cluster G ω₂ x := by
    cases c₁ with
    | nil => exact (hc₁ rfl).elim
    | cons q r₁ =>
      obtain ⟨i₁,e₁⟩ := q
      cases c₂ with
      | nil => exact (hc₂ rfl).elim
      | cons q r₂ =>
        obtain ⟨i₂,e₂⟩ := q
        exact h₁.joint_root G x η₁ η₂ y₁ y₂ k j₁ j₂ i₁ i₂ ω₁ ω₂ ωf e₁ e₂ r₁ r₂ h₂ hsep
  let H := cluster G ωf x \ cluster G ω₂ x
  have hroot : cluster G ω₀ x = cluster G ω₁ x \ H := by
    rw [hroot']
    ext v
    constructor
    · rintro ⟨h1,h2⟩
      exact ⟨h1,fun hh => hh.2 h2⟩
    · rintro ⟨h1,h2⟩
      refine ⟨h1,?_⟩
      by_contra hn
      exact h2 ⟨h₁.cluster_subset G x η₁ y₁ k j₁ ω₁ ωf c₁ h1,hn⟩
  have hz : y₁ k ∉ H := fun hz => Set.disjoint_left.mp hsep.1
    ⟨h₁.endpoint G x η₁ y₁ k j₁ ω₁ ωf c₁,
      h₁.endpoint_not_mem_of_ne_nil G x η₁ y₁ k j₁ ω₁ ωf c₁ hc₁⟩ hz
  obtain ⟨ht,hout,hm,hcontacts⟩ := h₁.remote_replay G x η₁ y₁ k j₁ ω₁ ωf c₁ H ω₀ hroot hsep hz
  have hf := ht.runMasks_first G x η₁ y₁ k j₁ ω₀ (replaySplice G x η₁ y₁ c₁ ω₀) c₁ η₁
    (by intros; rfl)
  rw [hm] at hf
  have hs := h₁.joint_replay_state G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hsep
  have heq : replaySplice G x η₁ y₁ c₁ ω₀ = ω₂ := hf.symm.trans (congrArg Prod.fst hs)
  rw [heq] at ht
  exact ⟨ht,hm,hcontacts⟩

 

theorem joint_restore_seeded_unique (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (choose₁ choose₂ : ℕ → Set E → E)
    (k j₁ j₂ : ℕ) (ω₁ ω₂ ωf σ₁ σ₂ σf : Set E)
    (c₁ c₂ d₁ d₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (g₁ : SpliceTrace G x η₁ y₁ k j₁ σ₁ d₁ σf)
    (g₂ : SpliceTrace G x η₂ y₂ k j₂ σ₂ d₂ σf)
    (hc₁ : c₁ ≠ []) (hc₂ : c₂ ≠ []) (hd₁ : d₁ ≠ []) (hd₂ : d₂ ≠ [])
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x))
    (gsep : GraphSeparated G (cluster G σf x \ cluster G σ₁ x)
      (cluster G σf x \ cluster G σ₂ x))
    (hr₁ : FollowsContactRule G x η₁ y₁ choose₁ c₁ ω₁)
    (hr₂ : FollowsContactRule G x η₂ y₂ choose₂ c₂ ω₂)
    (gr₁ : FollowsContactRule G x η₁ y₁ choose₁ d₁ σ₁)
    (gr₂ : FollowsContactRule G x η₂ y₂ choose₂ d₂ σ₂)
    (hrestore : exchangeOn (maskUnion (replayMasks G x η₂ y₂ c₂ ω₂)) ω₁ ω₂ =
      exchangeOn (maskUnion (replayMasks G x η₂ y₂ d₂ σ₂)) σ₁ σ₂) :
    c₁ = d₁ ∧ c₂ = d₂ ∧ ωf = σf ∧
      (runMasks (replayMasks G x η₁ y₁ c₁ ω₁) (ω₁,η₁)).2 =
        (runMasks (replayMasks G x η₁ y₁ d₁ σ₁) (σ₁,η₁)).2 ∧
      (runMasks (replayMasks G x η₂ y₂ c₂ ω₂) (ω₂,η₂)).2 =
        (runMasks (replayMasks G x η₂ y₂ d₂ σ₂) (σ₂,η₂)).2 := by
  let ω₀ := exchangeOn (maskUnion (replayMasks G x η₂ y₂ c₂ ω₂)) ω₁ ω₂
  let σ₀ := exchangeOn (maskUnion (replayMasks G x η₂ y₂ d₂ σ₂)) σ₁ σ₂
  obtain ⟨ht,hm,hcontact⟩ := h₁.joint_virtual G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hc₁ hc₂ hsep
  obtain ⟨gt,gm,gcontact⟩ := g₁.joint_virtual G x η₁ η₂ y₁ y₂ k j₁ j₂ σ₁ σ₂ σf d₁ d₂ g₂ hd₁ hd₂ gsep
  have hrc : FollowsContactRule G x η₁ y₁ choose₁ c₁ ω₀ := by
    unfold FollowsContactRule at hr₁ ⊢
    rw [hcontact]
    exact hr₁
  have grc : FollowsContactRule G x η₁ y₁ choose₁ d₁ σ₀ := by
    unfold FollowsContactRule at gr₁ ⊢
    rw [gcontact]
    exact gr₁
  change SpliceTrace G x η₁ y₁ k j₁ σ₀ d₁ σ₂ at gt
  change replayMasks G x η₁ y₁ c₁ ω₀ = _ at hm
  change replayMasks G x η₁ y₁ d₁ σ₀ = _ at gm
  have h00 : ω₀ = σ₀ := hrestore
  rw [← h00] at gt grc
  obtain ⟨hcode₁,hω₂⟩ := ht.seeded_unique G x η₁ y₁ k j₁ ω₀ ω₂ σ₂ c₁ d₁ gt choose₁ hrc grc
  rw [← hω₂] at g₂ gr₂
  obtain ⟨hcode₂,hout⟩ := h₂.seeded_unique G x η₂ y₂ k j₂ ω₂ ωf σf c₂ d₂ g₂ choose₂ hr₂ gr₂
  refine ⟨hcode₁,hcode₂,hout,?_,?_⟩
  · have hs := congrArg Prod.snd (h₁.joint_replay_state G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hsep)
    have gs := congrArg Prod.snd (g₁.joint_replay_state G x η₁ η₂ y₁ y₂ k j₁ j₂ σ₁ σ₂ σf d₁ d₂
      (hω₂ ▸ g₂) gsep)
    change (runMasks _ (ω₀,η₁)).2 = _ at hs
    change (runMasks _ (σ₀,η₁)).2 = _ at gs
    rw [← hs,← gs,← hm,← gm,h00,hcode₁]
  · rw [hcode₂,hω₂]

end JointReplay

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section JointWeight
attribute [local instance] Classical.propDecidable Classical.decEq



theorem jointTupleWeight_nonneg (Q : Finset E) (J₁ J₂ : Finset ℕ)
    (p : unitInterval) (s : JointSpliceState E) : 0 ≤ jointTupleWeight Q J₁ J₂ p s := by
  exact mul_nonneg (spliceTupleWeight_nonneg Q J₁ p (s.1,s.2.1))
    (Finset.prod_nonneg fun _ _ => bernoulliWeight_nonneg _ _ p)

theorem replayMasks_indices_mem (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (c : List (ℕ × E)) (ω : Set E) (J : Finset ℕ)
    (hJ : ∀ q ∈ c, q.1 ∈ J) : ∀ q ∈ replayMasks G x η y c ω, q.1 ∈ J := by
  intro q hq
  have hq' : q.1 ∈ (replayMasks G x η y c ω).map Prod.fst := List.mem_map_of_mem hq
  rw [replayMasks_indices G x η y c ω] at hq'
  obtain ⟨r,hr,he⟩ := List.mem_map.mp hq'
  exact he ▸ hJ r hr

 

theorem SpliceTrace.joint_weight (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x))
    (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (hJ₁ : ∀ q ∈ c₁, q.1 ∈ J₁) (hJ₂ : ∀ q ∈ c₂, q.1 ∈ J₂) :
    let m₁ := replayMasks G x η₁ y₁ c₁ ω₁
    let m₂ := replayMasks G x η₂ y₂ c₂ ω₂
    let ω₀ := exchangeOn (maskUnion m₂) ω₁ ω₂
    jointTupleWeight Q J₁ J₂ p (ωf,(runMasks m₁ (ω₁,η₁)).2,(runMasks m₂ (ω₂,η₂)).2) =
      jointTupleWeight Q J₁ J₂ p (ω₀,η₁,η₂) := by
  intro m₁ m₂ ω₀
  have hw₁ := runMasks_weight m₁ (ω₀,η₁) Q J₁ p
    (replayMasks_indices_mem G x η₁ y₁ c₁ ω₁ J₁ hJ₁)
  rw [h₁.joint_replay_state G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hsep] at hw₁
  have hw₂ := runMasks_weight m₂ (ω₂,η₂) Q J₂ p
    (replayMasks_indices_mem G x η₂ y₂ c₂ ω₂ J₂ hJ₂)
  unfold spliceTupleWeight at hw₁ hw₂
  rw [h₂.runMasks_first G x η₂ y₂ k j₂ ω₂ ωf c₂ η₂ (by intros; rfl)] at hw₂
  unfold jointTupleWeight
  dsimp only at hw₁ hw₂ ⊢
  calc
    _ = (bernoulliWeight Q (domainBits Q ωf) p *
        ∏ i ∈ J₂, bernoulliWeight Q (domainBits Q ((runMasks m₂ (ω₂,η₂)).2 i)) p) *
        ∏ i ∈ J₁, bernoulliWeight Q (domainBits Q ((runMasks m₁ (ω₁,η₁)).2 i)) p := by ring
    _ = (bernoulliWeight Q (domainBits Q ω₂) p *
        ∏ i ∈ J₂, bernoulliWeight Q (domainBits Q (η₂ i)) p) *
        ∏ i ∈ J₁, bernoulliWeight Q (domainBits Q ((runMasks m₁ (ω₁,η₁)).2 i)) p := by rw [hw₂]
    _ = (bernoulliWeight Q (domainBits Q ω₂) p *
        ∏ i ∈ J₁, bernoulliWeight Q (domainBits Q ((runMasks m₁ (ω₁,η₁)).2 i)) p) *
        ∏ i ∈ J₂, bernoulliWeight Q (domainBits Q (η₂ i)) p := by ring
    _ = _ := by rw [hw₁]

end JointWeight

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_ReferenceLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference Laws for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TrajectorySupport
attribute [local instance] Classical.propDecidable Classical.decEq



theorem SpliceTrace.trajectory_hits (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf) (hc : c ≠ []) :
    (cluster G ω x ∩ trajectoryUnion G η y k).Nonempty := by
  cases h with
  | stop => exact (hc rfl).elim
  | step j i ω e a b rest ωf hn hji hik hmax hy he hab ha hb ht =>
    exact ⟨a,ha,(mem_trajectoryUnion G η y k a).mpr ⟨i,by omega,hik,
      (edge_cluster_sides G (η i) (y i) he hab).mpr (conn_mono G Set.inter_subset_left hb)⟩⟩

 

theorem SpliceTrace.added_finite_cap (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j M : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf)
    (hcaps : ∀ i, 1 ≤ i → i ≤ k →
      (cluster G (η i) (y i)).Finite ∧ (cluster G (η i) (y i)).ncard ≤ M) :
    (cluster G ωf x \ cluster G ω x).Finite ∧ (cluster G ωf x \ cluster G ω x).ncard ≤ k*M := by
  obtain ⟨hf,hc⟩ := trajectoryUnion_finite_cap G η y k M hcaps
  have hs := h.added_subset_trajectory G x η y k j ω ωf c
  exact ⟨hf.subset hs,(Set.ncard_le_ncard hs hf).trans hc⟩

end TrajectorySupport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section JointReferenceEvent
attribute [local instance] Classical.propDecidable Classical.decEq

theorem SpliceTrace.joint_restored_field_symm (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x)) :
    (jointRestored G x η₁ η₂ y₂ ω₁ ω₂ c₂).1 =
      (jointRestored G x η₂ η₁ y₁ ω₂ ω₁ c₁).1 := by
  apply exchange_patch_symm _ _ ω₁ ω₂ ωf
    (h₁.masks_disjoint G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hsep)
  · intro e he
    rw [← h₁.replay_eq G x η₁ y₁ k j₁ ω₁ ωf c₁]
    exact (replaySplice_off_masks G x η₁ y₁ c₁ ω₁ e he).symm
  · intro e he
    rw [← h₂.replay_eq G x η₂ y₂ k j₂ ω₂ ωf c₂]
    exact (replaySplice_off_masks G x η₂ y₂ c₂ ω₂ e he).symm

theorem SpliceTrace.joint_restored_root (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hc₁ : c₁ ≠ []) (hc₂ : c₂ ≠ [])
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x)) :
    cluster G (jointRestored G x η₁ η₂ y₂ ω₁ ω₂ c₂).1 x =
      cluster G ω₁ x ∩ cluster G ω₂ x := by
  cases c₁ with
  | nil => exact (hc₁ rfl).elim
  | cons q r₁ =>
    obtain ⟨i₁,e₁⟩ := q
    cases c₂ with
    | nil => exact (hc₂ rfl).elim
    | cons q r₂ =>
      obtain ⟨i₂,e₂⟩ := q
      exact h₁.joint_root G x η₁ η₂ y₁ y₂ k j₁ j₂ i₁ i₂ ω₁ ω₂ ωf e₁ e₂ r₁ r₂ h₂ hsep

 

theorem SpliceTrace.joint_trajectory_hits (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hc₁ : c₁ ≠ []) (hc₂ : c₂ ≠ [])
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x)) :
    let A := cluster G (jointRestored G x η₁ η₂ y₂ ω₁ ω₂ c₂).1 x
    (A ∩ trajectoryUnion G η₁ y₁ k).Nonempty ∧ (A ∩ trajectoryUnion G η₂ y₂ k).Nonempty := by
  intro A
  have hv₁ := (h₁.joint_virtual G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hc₁ hc₂ hsep).1
  have hv₂ := (h₂.joint_virtual G x η₂ η₁ y₂ y₁ k j₂ j₁ ω₂ ω₁ ωf c₂ c₁ h₁ hc₂ hc₁
    (hsep.symm G _ _)).1
  refine ⟨hv₁.trajectory_hits G x η₁ y₁ k j₁ _ ω₂ c₁ hc₁,?_⟩
  change (cluster G (jointRestored G x η₁ η₂ y₂ ω₁ ω₂ c₂).1 x ∩ _).Nonempty
  rw [h₁.joint_restored_field_symm G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hsep]
  exact hv₂.trajectory_hits G x η₂ y₂ k j₂ _ ω₁ c₂ hc₂

 

theorem SpliceTrace.joint_restored_size (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ n M : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hc₁ : c₁ ≠ []) (hc₂ : c₂ ≠ [])
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x))
    (hf : (cluster G ω₁ x).Finite) (hn : n ≤ (cluster G ω₁ x).ncard)
    (h2n : (cluster G ω₁ x).ncard < 2*n)
    (hcap₂ : ∀ i, 1 ≤ i → i ≤ k →
      (cluster G (η₂ i) (y₂ i)).Finite ∧ (cluster G (η₂ i) (y₂ i)).ncard ≤ M) :
    let A := cluster G (jointRestored G x η₁ η₂ y₂ ω₁ ω₂ c₂).1 x
    A.Finite ∧ n-k*M ≤ A.ncard ∧ A.ncard < 2*n := by
  intro A
  have hA : A = cluster G ω₁ x ∩ cluster G ω₂ x :=
    h₁.joint_restored_root G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hc₁ hc₂ hsep
  have hdiff : A = cluster G ω₁ x \ (cluster G ωf x \ cluster G ω₂ x) := by
    rw [hA]
    ext v
    constructor
    · rintro ⟨h1,h2⟩
      exact ⟨h1,fun hh => hh.2 h2⟩
    · rintro ⟨h1,h2⟩
      refine ⟨h1,?_⟩
      by_contra hn
      exact h2 ⟨h₁.cluster_subset G x η₁ y₁ k j₁ ω₁ ωf c₁ h1,hn⟩
  obtain ⟨hBfin,hBcap⟩ := h₂.added_finite_cap G x η₂ y₂ k j₂ M ω₂ ωf c₂ hcap₂
  have hlower := Set.ncard_le_ncard_sdiff_add_ncard (cluster G ω₁ x)
    (cluster G ωf x \ cluster G ω₂ x) hBfin
  rw [← hdiff] at hlower
  refine ⟨hA ▸ hf.inter_of_left _,by omega,?_⟩
  rw [hA]
  exact (Set.ncard_inter_le_ncard_left _ _ hf).trans_lt h2n

end JointReferenceEvent

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SmallHanging
attribute [local instance] Classical.propDecidable Classical.decEq


theorem mem_hangingSide_iff_pivotal (G : BondGraph V E) (ω : Set E) (x z : V)
    (e : E) (he : e ∈ ω) : z ∈ hangingSide G ω x e ↔ OpenMarkedPivotal G ω {z} x e := by
  constructor
  · rintro ⟨hz,hn⟩
    exact ⟨he,⟨z,rfl,hz⟩,fun ⟨y,hy,hxy⟩ => hn ((Set.mem_singleton_iff.mp hy) ▸ hxy)⟩
  · rintro ⟨_,⟨y,hy,hxy⟩,hn⟩
    exact ⟨(Set.mem_singleton_iff.mp hy) ▸ hxy,fun hz => hn ⟨z,rfl,hz⟩⟩

theorem hangingSide_ncard_add_rank (G : BondGraph V E) (ω : Set E) (x : V)
    (e : E) (hC : (cluster G ω x).Finite) :
    (hangingSide G ω x e).ncard + pivotalRank G ω x e = (cluster G ω x).ncard := by
  have hs : cluster G (ω \ {e}) x ⊆ cluster G ω x := fun _ h => conn_mono G Set.sdiff_subset h
  rw [hangingSide,Set.ncard_sdiff hs (hC.subset hs)]
  exact Nat.sub_add_cancel (Set.ncard_le_ncard hs hC)



theorem smallSeparatingBonds_card_le (G : BondGraph V E) (ω : Set E) (x z : V)
    (v : ℕ) (hC : (cluster G ω x).Finite) : (smallSeparatingBonds G ω x z v).card ≤ v := by
  have hh := Finset.card_le_card_of_injOn (s := smallSeparatingBonds G ω x z v)
    (t := Finset.Icc 1 v) (fun e => (hangingSide G ω x e).ncard)
  have hmap : Set.MapsTo (fun e => (hangingSide G ω x e).ncard)
      (↑(smallSeparatingBonds G ω x z v)) (↑(Finset.Icc 1 v)) := by
    intro e he
    obtain ⟨he,hcap⟩ := Finset.mem_filter.mp he
    have hp := (mem_separatingBonds G ω x z e).mp he
    exact Finset.mem_Icc.mpr ⟨(Set.ncard_pos (hangingSide_finite G ω x e hC)).mpr
      ⟨z,(mem_hangingSide_iff_pivotal G ω x z e hp.1).mpr hp⟩,hcap⟩
  have hinj : Set.InjOn (fun e => (hangingSide G ω x e).ncard)
      (↑(smallSeparatingBonds G ω x z v)) := by
    intro e he f hf heq
    apply pivotalRank_injective_of_cluster_finite G ω {z} x hC
      ((mem_separatingBonds G ω x z e).mp (Finset.mem_filter.mp he).1)
      ((mem_separatingBonds G ω x z f).mp (Finset.mem_filter.mp hf).1)
    change (hangingSide G ω x e).ncard = (hangingSide G ω x f).ncard at heq
    have he' := hangingSide_ncard_add_rank G ω x e hC
    have hf' := hangingSide_ncard_add_rank G ω x f hC
    omega
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hh hmap hinj

theorem mem_smallHangingThrough (G : BondGraph V E) (ω : Set E) (x z w : V)
    (v : ℕ) (hC : (cluster G ω x).Finite) : w ∈ smallHangingThrough G ω x z v hC ↔
      ∃ e, OpenMarkedPivotal G ω {z} x e ∧ (hangingSide G ω x e).ncard ≤ v ∧
        w ∈ hangingSide G ω x e := by
  simp [smallHangingThrough, smallSeparatingBonds, and_assoc]

theorem smallHangingThrough_card_le (G : BondGraph V E) (ω : Set E) (x z : V)
    (v : ℕ) (hC : (cluster G ω x).Finite) :
    (smallHangingThrough G ω x z v hC).card ≤ v*v := by
  calc
    _ ≤ ∑ e ∈ smallSeparatingBonds G ω x z v, (hangingSide_finite G ω x e hC).toFinset.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ smallSeparatingBonds G ω x z v, v := by
      apply Finset.sum_le_sum
      intro e he
      rw [← Set.ncard_eq_toFinset_card (hangingSide G ω x e) (hangingSide_finite G ω x e hC)]
      exact (Finset.mem_filter.mp he).2
    _ = (smallSeparatingBonds G ω x z v).card*v := by simp
    _ ≤ v*v := Nat.mul_le_mul_right v (smallSeparatingBonds_card_le G ω x z v hC)

end SmallHanging

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NearHanging
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem hangingSide_laminar (G : BondGraph V E) (ω : Set E) (x : V)
    (e f : E) (he : e ∈ ω) (hf : f ∈ ω) :
    Disjoint (hangingSide G ω x e) (hangingSide G ω x f) ∨
      hangingSide G ω x e ⊆ hangingSide G ω x f ∨
      hangingSide G ω x f ⊆ hangingSide G ω x e := by
  by_cases hd : Disjoint (hangingSide G ω x e) (hangingSide G ω x f)
  · exact Or.inl hd
  obtain ⟨z,hze,hzf⟩ := Set.not_disjoint_iff.mp hd
  by_cases hef : e = f
  · exact Or.inr (Or.inl (hef ▸ Set.Subset.refl _))
  rcases pivotal_rootSides_nested G ω {z} x
    ((mem_hangingSide_iff_pivotal G ω x z e he).mp hze)
    ((mem_hangingSide_iff_pivotal G ω x z f hf).mp hzf) hef with h | h
  · exact Or.inr (Or.inr (Set.sdiff_subset_sdiff_right h.1))
  · exact Or.inr (Or.inl (Set.sdiff_subset_sdiff_right h.1))

theorem graphNeighbors_card_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (A : Finset V) (d : ℕ) (hdeg : ∀ a, degree G a ≤ d) :
    (graphNeighbors G hloc A).card ≤ A.card*d := by
  calc
    _ ≤ ∑ a ∈ A, (neighbors G hloc a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, d := Finset.sum_le_sum fun a _ =>
      (neighbors_card_le_degree G hloc a).trans (hdeg a)
    _ = _ := by simp



theorem nearHangingEndpoints_card_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x z : V) (e : E) (v d : ℕ) (hC : (cluster G ω x).Finite)
    (hcap : (hangingSide G ω x e).ncard ≤ v) (hdeg : ∀ a, degree G a ≤ d) :
    (nearHangingEndpoints G hloc ω x z e v hC).card ≤ v+v^2+d*v^3 := by
  let B := (hangingSide_finite G ω x e hC).toFinset
  let N := graphNeighbors G hloc B
  have hB : B.card ≤ v := by
    simpa only [B,← Set.ncard_eq_toFinset_card (hangingSide G ω x e)
      (hangingSide_finite G ω x e hC)] using hcap
  have hN : N.card ≤ v*d := (graphNeighbors_card_le G hloc B d hdeg).trans
    (Nat.mul_le_mul_right d hB)
  have hU : (N.biUnion fun a => smallHangingThrough G ω x a v hC).card ≤ d*v^3 := by
    calc
      _ ≤ ∑ a ∈ N, (smallHangingThrough G ω x a v hC).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ N, v*v := Finset.sum_le_sum fun a _ => smallHangingThrough_card_le G ω x a v hC
      _ = N.card*(v*v) := by simp
      _ ≤ (v*d)*(v*v) := Nat.mul_le_mul_right (v*v) hN
      _ = d*v^3 := by ring
  calc
    _ ≤ (B ∪ smallHangingThrough G ω x z v hC).card +
        (N.biUnion fun a => smallHangingThrough G ω x a v hC).card := Finset.card_union_le ..
    _ ≤ (B.card + (smallHangingThrough G ω x z v hC).card) + d*v^3 :=
      Nat.add_le_add (Finset.card_union_le ..) hU
    _ ≤ (v+v*v)+d*v^3 := Nat.add_le_add_right
      (Nat.add_le_add hB (smallHangingThrough_card_le G ω x z v hC)) _
    _ = v+v^2+d*v^3 := by ring

theorem mem_nearHangingEndpoints_of_not_separated (G : BondGraph V E)
    (hloc : LocallyFinite G) (ω : Set E) (x z w : V) (e f : E) (v : ℕ)
    (hC : (cluster G ω x).Finite)
    (he : OpenMarkedPivotal G ω {z} x e) (hf : OpenMarkedPivotal G ω {w} x f)
    (hcap : (hangingSide G ω x f).ncard ≤ v)
    (hn : ¬GraphSeparated G (hangingSide G ω x e) (hangingSide G ω x f)) :
    w ∈ nearHangingEndpoints G hloc ω x z e v hC := by
  have hz := (mem_hangingSide_iff_pivotal G ω x z e he.1).mpr he
  have hw := (mem_hangingSide_iff_pivotal G ω x w f hf.1).mpr hf
  rcases hangingSide_laminar G ω x e f he.1 hf.1 with hd | hsub | hsub
  · have hadj : ∃ a ∈ hangingSide G ω x e, ∃ b ∈ hangingSide G ω x f, Adj G a b := by
      by_contra h
      apply hn
      refine ⟨hd,?_⟩
      intro a ha b hb hab
      exact h ⟨a,ha,b,hb,hab⟩
    obtain ⟨a,ha,b,hb,hab⟩ := hadj
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨b,Finset.mem_biUnion.mpr ⟨a,?_,(mem_neighbors G hloc a b).mpr hab⟩,?_⟩
    · exact (hangingSide_finite G ω x e hC).mem_toFinset.mpr ha
    · exact (mem_smallHangingThrough G ω x b w v hC).mpr
        ⟨f,(mem_hangingSide_iff_pivotal G ω x b f hf.1).mp hb,hcap,hw⟩
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact (mem_smallHangingThrough G ω x z w v hC).mpr
      ⟨f,(mem_hangingSide_iff_pivotal G ω x z f hf.1).mp (hsub hz),hcap,hw⟩
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact (hangingSide_finite G ω x e hC).mem_toFinset.mpr (hsub hw)

end NearHanging

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteReferenceLaw
attribute [local instance] Classical.propDecidable Classical.decEq


theorem encodeFiniteJoint_injective (Q : Finset E) (J₁ J₂ : Finset ℕ) :
    Function.Injective (encodeFiniteJoint Q J₁ J₂) := by
  intro a b he
  apply Prod.ext (finiteFieldSet_injective Q (congrArg Prod.fst he))
  exact Prod.ext (finiteFieldFamily_injective Q J₁ (congrArg (fun s => s.2.1) he))
    (finiteFieldFamily_injective Q J₂ (congrArg (fun s => s.2.2) he))

theorem jointTupleWeight_encode (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (s : FiniteJointData Q J₁ J₂) :
    jointTupleWeight Q J₁ J₂ p (encodeFiniteJoint Q J₁ J₂ s) =
      finiteFieldWeight Q p s.1 * finiteFamilyWeight Q J₁ p s.2.1 *
        finiteFamilyWeight Q J₂ p s.2.2 := by
  simp only [jointTupleWeight,encodeFiniteJoint,domainBits_finiteFieldSet,
    prod_fieldFamilyWeight,finiteFieldWeight]



end FiniteReferenceLaw

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteReferenceFactor
attribute [local instance] Classical.propDecidable Classical.decEq



theorem mem_finiteJointDomain_of_support (Q : Finset E) (J₁ J₂ : Finset ℕ)
    (s : JointSpliceState E) (hω : s.1 ⊆ (Q : Set E))
    (hη₁ : ∀ i, s.2.1 i ⊆ (Q : Set E)) (hη₂ : ∀ i, s.2.2 i ⊆ (Q : Set E))
    (hz₁ : ∀ i ∉ J₁, s.2.1 i = ∅) (hz₂ : ∀ i ∉ J₂, s.2.2 i = ∅) :
    s ∈ finiteJointDomain Q J₁ J₂ := by
  let desc (ω : Set E) : FiniteField Q := ⟨domainBits Q ω,Finset.mem_powerset.mpr (domainBits_subset Q ω)⟩
  have hdesc (ω : Set E) (h : ω ⊆ (Q : Set E)) : finiteFieldSet Q (desc ω) = ω := by
    ext e
    simp only [finiteFieldSet,desc,Finset.mem_coe,mem_domainBits]
    exact ⟨fun hh => hh.2,fun hh => ⟨h hh,hh⟩⟩
  let a : FiniteJointData Q J₁ J₂ := (desc s.1,fun i => desc (s.2.1 i),fun i => desc (s.2.2 i))
  apply Finset.mem_image.mpr
  refine ⟨a,Finset.mem_univ _,?_⟩
  apply Prod.ext (hdesc s.1 hω)
  apply Prod.ext
  · funext i
    change (if hi : i ∈ J₁ then finiteFieldSet Q (desc (s.2.1 i)) else ∅) = s.2.1 i
    by_cases hi : i ∈ J₁
    · simp only [hi,dite_true,hdesc _ (hη₁ i)]
    · simp only [hi,dite_false,hz₁ i hi]
  · funext i
    change (if hi : i ∈ J₂ then finiteFieldSet Q (desc (s.2.2 i)) else ∅) = s.2.2 i
    by_cases hi : i ∈ J₂
    · simp only [hi,dite_true,hdesc _ (hη₂ i)]
    · simp only [hi,dite_false,hz₂ i hi]

end FiniteReferenceFactor

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SeededForward
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem exists_seeded_spliceTrace (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k M : ℕ)
    (hchain : ∀ i ∈ Finset.Icc 1 k, Conn G (η i) (y i) (y (i-1)))
    (hcaps : ∀ i ∈ Finset.Icc 1 k, (cluster G (η i) (y i)).Finite ∧
      (cluster G (η i) (y i)).ncard ≤ M)
    (choose : ℕ → Set E → E)
    (hchoose : ∀ i K, K.Finite → K.Nonempty → choose i K ∈ K)
    (j : ℕ) (hj : j ≤ k) (ω : Set E) (hyj : y j ∈ cluster G ω x)
    (N : ℕ) (hfin : (cluster G ω x).Finite) (hN : (cluster G ω x).ncard ≤ N) :
    ∃ steps ωf, SpliceTrace G x η y k j ω steps ωf ∧
      FollowsContactRule G x η y choose steps ω ∧ steps.length ≤ k-j ∧
      y k ∈ cluster G ωf x ∧ (cluster G ωf x).Finite ∧
      (cluster G ωf x).ncard ≤ N+(k-j)*M := by
  generalize hn : k-j = n
  induction n using Nat.strong_induction_on generalizing j ω N with
  | h n ih =>
    by_cases hz : y k ∈ cluster G ω x
    · refine ⟨[],ω,SpliceTrace.stop j ω hz,?_,by simp,hz,hfin,?_⟩
      · exact List.Forall₂.nil
      · exact hN.trans (Nat.le_add_right ..)
    · obtain ⟨i,hiI,hmeet,hyi,hmax⟩ :=
        exists_maximal_splice_index G η y k j hj hchain (cluster G ω x) hyj hz
      obtain ⟨hji,hik⟩ := Finset.mem_Icc.mp hiI
      have hi1 : i ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by omega,hik⟩
      let B := cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)
      let K := contactSet G (η i) B
      have hBC : B ⊆ cluster G (η i) (y i) := fun _ h => conn_mono G Set.inter_subset_left h
      have hBK : K.Finite := contactSet_finite G hloc (η i) B ((hcaps i hi1).1.subset hBC)
      have hK : K.Nonempty := by
        obtain ⟨e,a,b,he,hab,ha,hb⟩ := exists_splice_contact G (η i) (cluster G ω x) (y i) hyi hmeet
        exact ⟨e,he,b,a,hab.trans (Sym2.eq_swap ..),hb,
          fun h => slit_cluster_subset G (cluster G ω x) (η i) (y i) hyi h ha⟩
      let e := choose i K
      have heK : e ∈ contactSet G (η i) B := hchoose i K hBK hK
      change e ∈ contactSet G (η i)
        (cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)) at heK
      rw [contactSet_deleted_cluster G (η i) (cluster G ω x) (y i) hyi] at heK
      obtain ⟨he,b,hb,a,ha,hba⟩ := heK
      have hab : G e = s(a,b) := hba.trans (Sym2.eq_swap ..)
      let ω' := spliceField G (cluster G ω x) B e ω (η i)
      have hcap := splice_cluster_cap G ω (η i) x (y i) hyi e a b hab he ha hb N M hfin hN
        (hcaps i hi1).1 (hcaps i hi1).2
      have hyt : y i ∈ cluster G ω' x := by
        change y i ∈ cluster G (spliceField G (cluster G ω x) B e ω (η i)) x
        rw [splice_cluster G ω (η i) x (y i) hyi e a b hab he ha hb]
        exact Or.inr (mem_cluster_self G _ _)
      obtain ⟨steps,ωf,htrace,hrule,hlen,hconn,hf,hs⟩ :=
        ih (k-i) (by omega) i hik ω' hyt (N+M) hcap.1 hcap.2 rfl
      refine ⟨(i,e)::steps,ωf,
        SpliceTrace.step j i ω e a b steps ωf hz (by omega) hik hmax hyi he hab ha hb htrace,
        ?_,?_,hconn,hf,?_⟩
      · exact (followsContactRule_cons G x η y choose i e steps ω).mpr ⟨rfl,hrule⟩
      · simp only [List.length_cons]
        omega
      · have hm : (k-i+1)*M ≤ (k-j)*M := Nat.mul_le_mul_right M (by omega)
        rw [Nat.add_mul,one_mul] at hm
        calc
          _ ≤ (N+M)+(k-i)*M := hs
          _ ≤ N+(k-j)*M := by omega
          _ = N+n*M := by rw [hn]



end SeededForward
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SpliceLocalSupport
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem reachBall_triangle (G : BondGraph V E) (x y : V) (n m : ℕ)
    (hy : y ∈ reachBall G x n) : reachBall G y m ⊆ reachBall G x (n+m) := by
  induction m with
  | zero => simpa only [reachBall,Nat.add_zero,Set.singleton_subset_iff] using hy
  | succ m ih =>
    intro z hz
    rcases hz with hz | hz
    · exact Or.inl (ih hz)
    · apply Or.inr
      simp only [Set.mem_iUnion,Set.mem_ofPred_eq] at hz ⊢
      obtain ⟨a,ha,haz⟩ := hz
      exact ⟨a,ih ha,haz⟩


end SpliceLocalSupport
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section UniformContactSelector
attribute [local instance] Classical.propDecidable Classical.decEq



theorem uniformRank_val_of_lt_one (K : ℕ) (hK : 0 < K) (t : unitInterval)
    (ht : (t:ℝ) < 1) : (uniformRank K hK t).val = ⌊(K:ℝ)*(t:ℝ)⌋₊ := by
  have hp : (0:ℝ) < K := by exact_mod_cast hK
  have hf : ⌊(K:ℝ)*(t:ℝ)⌋₊ < K := (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg _) t.property.1)).mpr (by nlinarith)
  exact min_eq_left (by omega)

theorem uniformRank_eq_iff (K : ℕ) (hK : 0 < K) (t : unitInterval)
    (ht : (t:ℝ) < 1) (a : Fin K) :
    uniformRank K hK t = a ↔ t ∈ contactInterval K a.val := by
  rw [Fin.ext_iff,uniformRank_val_of_lt_one K hK t ht,
    Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg _) t.property.1)]
  have hp : (0:ℝ) < K := by exact_mod_cast hK
  simp only [contactInterval,Set.mem_ofPred_eq,Nat.cast_add,Nat.cast_one]
  rw [div_le_iff₀ hp,lt_div_iff₀ hp]
  simp only [mul_comm]

theorem volume_uniformRank_fiber (K : ℕ) (hK : 0 < K) (a : Fin K) :
    volume {t : unitInterval | uniformRank K hK t = a} =
      ENNReal.ofReal ((K:ℝ)⁻¹) := by
  rw [← volume_contactInterval K a.val a.isLt]
  apply measure_congr
  filter_upwards [(volume : Measure unitInterval).ae_ne 1] with t ht
  exact propext (uniformRank_eq_iff K hK t (lt_of_le_of_ne t.property.2
    (fun he => ht (Subtype.ext he))) a)



theorem uniformContact_mem (K : Finset E) (hK : K.Nonempty) (t : unitInterval) :
    uniformContact K hK t ∈ K :=
  ((K.equivFin).symm (uniformRank K.card (Finset.card_pos.mpr hK) t)).property

theorem uniformContact_eq_iff (K : Finset E) (hK : K.Nonempty) (t : unitInterval)
    (e : E) (he : e ∈ K) :
    uniformContact K hK t = e ↔
      uniformRank K.card (Finset.card_pos.mpr hK) t = K.equivFin ⟨e,he⟩ := by
  unfold uniformContact
  change ((K.equivFin).symm (uniformRank K.card (Finset.card_pos.mpr hK) t)).val =
    (⟨e,he⟩ : ↥K).val ↔ _
  rw [← Subtype.ext_iff]
  exact K.equivFin.symm_apply_eq

theorem volume_uniformContact_fiber (K : Finset E) (hK : K.Nonempty)
    (e : E) (he : e ∈ K) : volume {t : unitInterval | uniformContact K hK t = e} =
      ENNReal.ofReal ((K.card:ℝ)⁻¹) := by
  simp_rw [uniformContact_eq_iff K hK _ e he]
  exact volume_uniformRank_fiber K.card (Finset.card_pos.mpr hK) _



theorem chooseContact_mem [Nonempty E] (seed : ℕ → unitInterval)
    (i : ℕ) (K : Set E) (hf : K.Finite) (hn : K.Nonempty) :
    chooseContact seed i K ∈ K := by
  simp only [chooseContact,dite_eq_left hf,dite_eq_left hn]
  exact hf.mem_toFinset.mp (uniformContact_mem _ _ _)

end UniformContactSelector
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SeededTraceLaw
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty E]

 
theorem chooseContact_congr (u v : ℕ → unitInterval) (i : ℕ) (K : Set E)
    (h : u i = v i) : chooseContact u i K = chooseContact v i K := by
  unfold chooseContact
  split_ifs <;> simp only [h]


theorem replaySeedFiber_univ (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (c : List (ℕ × E)) (ω : Set E) (i : ℕ)
    (hi : ∀ q ∈ c, i ≠ q.1) : replaySeedFiber G x η y c ω i = Set.univ := by
  induction c generalizing ω with
  | nil => rfl
  | cons q c ih =>
    obtain ⟨j,e⟩ := q
    simp only [replaySeedFiber,ite_eq_right (hi (j,e) (by simp))]
    exact ih _ (fun q hq => hi q (by simp [hq]))

theorem SpliceTrace.follows_iff_seedFiber (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E)
    (c : List (ℕ × E)) (h : SpliceTrace G x η y k j ω c ωf)
    (seed : ℕ → unitInterval) :
    FollowsContactRule G x η y (chooseContact seed) c ω ↔
      ∀ i, 1 ≤ i → i ≤ k → seed i ∈ replaySeedFiber G x η y c ω i := by
  induction h with
  | stop j ω hz => simp [FollowsContactRule,replayContacts,replaySeedFiber]
  | @step j l ω e a b c ωf hn hjl hlk hm hy he hab ha hb ht ih =>
    rw [followsContactRule_cons,ih]
    have htail : replaySeedFiber G x η y c
        (spliceField G (cluster G ω x)
          (cluster G (η l ∩ internalEdges G (cluster G ω x)ᶜ) (y l)) e ω (η l)) l = Set.univ := by
      apply replaySeedFiber_univ
      intro q hq
      have hq' := ht.seam_data G x η y k l _ ωf c q hq
      omega
    constructor
    · rintro ⟨hc,hr⟩ i hi hik
      by_cases hil : i = l
      · subst i
        simp only [replaySeedFiber,ite_true,Set.mem_ofPred_eq]
        exact (chooseContact_congr _ _ l _ rfl).trans hc
      · simpa only [replaySeedFiber,ite_eq_right hil] using hr i hi hik
    · intro hr
      constructor
      · have hh := hr l (by omega) hlk
        simp only [replaySeedFiber,ite_true,Set.mem_ofPred_eq] at hh
        exact (chooseContact_congr _ _ l _ rfl).trans hh
      · intro i hi hik
        by_cases hil : i = l
        · subst i
          rw [htail]
          trivial
        · simpa only [replaySeedFiber,ite_eq_right hil] using hr i hi hik



theorem SpliceTrace.seed_event_eq_pi (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E)
    (c : List (ℕ × E)) (h : SpliceTrace G x η y k j ω c ωf) :
    {u : Fin k → unitInterval | FollowsContactRule G x η y
      (chooseContact (finiteContactSeeds k u)) c ω} =
      Set.pi Set.univ (fun i => replaySeedFiber G x η y c ω (i.val+1)) := by
  ext u
  rw [Set.mem_ofPred_eq,h.follows_iff_seedFiber G x η y k j ω ωf c]
  simp only [Set.mem_pi,Set.mem_univ,true_implies]
  constructor
  · intro hu i
    simpa only [finiteContactSeeds_at] using hu (i.val+1) (by omega) (by omega)
  · intro hu i hi hik
    have hh := hu ⟨i-1,by omega⟩
    have hii : 1 ≤ i ∧ i ≤ k := ⟨hi,hik⟩
    simpa only [finiteContactSeeds,dite_eq_left hii,Nat.sub_add_cancel hi] using hh

 

theorem SpliceTrace.volume_seedFiber (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E)
    (c : List (ℕ × E)) (h : SpliceTrace G x η y k j ω c ωf)
    (hcaps : ∀ i, 1 ≤ i → i ≤ k → (cluster G (η i) (y i)).Finite) :
    ∀ i, volume (replaySeedFiber G x η y c ω i) =
      ENNReal.ofReal ((traceContactCount G η y ωf x c i : ℝ)⁻¹) := by
  induction c generalizing j ω with
  | nil => simp [replaySeedFiber,traceContactCount]
  | cons q c ih =>
    obtain ⟨l,e⟩ := q
    have hcut := h.head_cut G x η y k j l ω ωf e c
    cases h with
    | step j l ω e a b c ωf hn hjl hlk hm hy he hab ha hb ht =>
      intro i
      by_cases hil : i = l
      · subst i
        simp only [replaySeedFiber,ite_true,traceContactCount,seamContactCount,hcut]
        let B := cluster G (η l ∩ internalEdges G (cluster G ω x)ᶜ) (y l)
        let K := contactSet G (η l) B
        have hB : B.Finite := (hcaps l (by omega) hlk).subset (fun _ h => conn_mono G Set.inter_subset_left h)
        have hK : K.Finite := contactSet_finite G hloc (η l) B hB
        have heK : e ∈ K := ⟨he,b,a,hab.trans (Sym2.eq_swap ..),hb,
          fun haB => slit_cluster_subset G (cluster G ω x) (η l) (y l) hy haB ha⟩
        have hnK : K.Nonempty := ⟨e,heK⟩
        change volume {t : unitInterval | chooseContact (fun _ => t) l K = e} = _
        simp only [chooseContact,dite_eq_left hK,dite_eq_left hnK]
        rw [volume_uniformContact_fiber _ _ e (hK.mem_toFinset.mpr heK)]
        rw [← Set.ncard_eq_toFinset_card K hK]
      · simpa only [replaySeedFiber,traceContactCount,ite_eq_right hil] using ih l _ ht i

 
theorem SpliceTrace.seed_probability (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E)
    (c : List (ℕ × E)) (h : SpliceTrace G x η y k j ω c ωf)
    (hcaps : ∀ i, 1 ≤ i → i ≤ k → (cluster G (η i) (y i)).Finite) :
    ((volume : Measure (Fin k → unitInterval))
      {u | FollowsContactRule G x η y (chooseContact (finiteContactSeeds k u)) c ω}).toReal =
      ∏ i : Fin k, (traceContactCount G η y ωf x c (i.val+1):ℝ)⁻¹ := by
  rw [h.seed_event_eq_pi G x η y k j ω ωf c,MeasureTheory.volume_pi,Measure.pi_pi,ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [h.volume_seedFiber G hloc x η y k j ω ωf c hcaps,ENNReal.toReal_ofReal (by positivity)]

end SeededTraceLaw
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_MomentBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moment Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SeededTraceMeasurable
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem uniformRank_fiber_eq (K : ℕ) (hK : 0 < K) (a : Fin K) :
    {t : unitInterval | uniformRank K hK t = a} = contactInterval K a.val ∪
      (if uniformRank K hK 1 = a then {1} else ∅) := by
  ext t
  by_cases ht : t = 1
  · subst t
    have hnot : (1 : unitInterval) ∉ contactInterval K a.val := by
      intro h
      have hp : (0:ℝ) < K := by exact_mod_cast hK
      have hlt := (lt_div_iff₀ hp).mp h.2
      have ha : (a.val:ℝ)+1 ≤ K := by exact_mod_cast (show a.val+1 ≤ K by omega)
      push_cast at hlt
      norm_num at hlt
      linarith
    simp [hnot]
  · have hlt : (t:ℝ) < 1 := lt_of_le_of_ne t.property.2 (fun he => ht (Subtype.ext he))
    have he := uniformRank_eq_iff K hK t hlt a
    simp only [Set.mem_union,Set.mem_ofPred_eq]
    split_ifs <;> simpa [ht] using he

theorem measurableSet_contactInterval (K a : ℕ) : MeasurableSet (contactInterval K a) :=
  (measurableSet_le measurable_const measurable_subtype_coe).inter
    (measurableSet_lt measurable_subtype_coe measurable_const)

theorem measurableSet_uniformRank_fiber (K : ℕ) (hK : 0 < K) (a : Fin K) :
    MeasurableSet {t : unitInterval | uniformRank K hK t = a} := by
  rw [uniformRank_fiber_eq]
  apply (measurableSet_contactInterval K a.val).union
  split_ifs
  · exact measurableSet_singleton _
  · exact MeasurableSet.empty

theorem measurableSet_uniformContact_fiber (K : Finset E) (hK : K.Nonempty) (e : E) :
    MeasurableSet {t : unitInterval | uniformContact K hK t = e} := by
  by_cases he : e ∈ K
  · simp_rw [uniformContact_eq_iff K hK _ e he]
    exact measurableSet_uniformRank_fiber _ _ _
  · have hz : {t : unitInterval | uniformContact K hK t = e} = ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      exact fun h => he (h ▸ uniformContact_mem K hK t)
    rw [hz]
    exact MeasurableSet.empty

theorem measurableSet_chooseContact_fiber [Nonempty E] (i : ℕ) (K : Set E) (e : E) :
    MeasurableSet {t : unitInterval | chooseContact (fun _ => t) i K = e} := by
  unfold chooseContact
  split_ifs
  · exact measurableSet_uniformContact_fiber _ _ _
  · by_cases he : Classical.arbitrary E = e <;> simp [he]
  · by_cases he : Classical.arbitrary E = e <;> simp [he]

theorem measurableSet_replaySeedFiber [Nonempty E] (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (c : List (ℕ × E)) (ω : Set E) (i : ℕ) :
    MeasurableSet (replaySeedFiber G x η y c ω i) := by
  induction c generalizing ω with
  | nil => exact MeasurableSet.univ
  | cons q c ih =>
    obtain ⟨j,e⟩ := q
    simp only [replaySeedFiber]
    split_ifs
    · exact measurableSet_chooseContact_fiber _ _ _
    · exact ih _

theorem SpliceTrace.measurableSet_seed_event [Nonempty E] (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E)
    (c : List (ℕ × E)) (h : SpliceTrace G x η y k j ω c ωf) :
    MeasurableSet {u : Fin k → unitInterval | FollowsContactRule G x η y
      (chooseContact (finiteContactSeeds k u)) c ω} := by
  rw [h.seed_event_eq_pi G x η y k j ω ωf c]
  exact MeasurableSet.univ_pi (fun i => measurableSet_replaySeedFiber G x η y c ω (i.val+1))

end SeededTraceMeasurable
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteTraceDistribution
attribute [local instance] Classical.propDecidable Classical.decEq


theorem SpliceTrace.length_le (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf) : c.length ≤ k-j := by
  induction h with
  | stop => simp
  | step => simp only [List.length_cons]; omega

theorem SpliceTrace.mem_boundedTraceCodes (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf) (Q : Finset E)
    (hQ : ∀ i, 1 ≤ i → i ≤ k → η i ⊆ (Q : Set E)) : c ∈ boundedTraceCodes Q k := by
  rw [Percolation.mem_boundedTraceCodes]
  refine ⟨(h.length_le G x η y k j ω ωf c).trans (Nat.sub_le ..),?_⟩
  intro q hq
  obtain ⟨hj,hk,he,_⟩ := h.seam_data G x η y k j ω ωf c q hq
  exact ⟨by omega,hk,hQ q.1 (by omega) hk he⟩



theorem finite_trace_seed_partition [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k M : ℕ) (Q : Finset E)
    (hQ : ∀ i, 1 ≤ i → i ≤ k → η i ⊆ (Q : Set E))
    (hchain : ∀ i ∈ Finset.Icc 1 k, Conn G (η i) (y i) (y (i-1)))
    (hcaps : ∀ i ∈ Finset.Icc 1 k, (cluster G (η i) (y i)).Finite ∧
      (cluster G (η i) (y i)).ncard ≤ M)
    (j : ℕ) (hj : j ≤ k) (ω : Set E) (hyj : y j ∈ cluster G ω x)
    (hfin : (cluster G ω x).Finite) :
    let S := finiteTraceCodes G x η y k j ω Q
    let A := fun c => {u : Fin k → unitInterval | FollowsContactRule G x η y
      (chooseContact (finiteContactSeeds k u)) c ω}
    (⋃ c ∈ S, A c) = Set.univ ∧ Set.PairwiseDisjoint (↑S) A := by
  intro S A
  constructor
  · apply Set.eq_univ_of_forall
    intro u
    obtain ⟨c,ωf,ht,hr,_⟩ := exists_seeded_spliceTrace G hloc x η y k M hchain hcaps
      (chooseContact (finiteContactSeeds k u)) (chooseContact_mem _) j hj ω hyj _ hfin (le_refl _)
    have hc : c ∈ S := (mem_finiteTraceCodes_iff ..).mpr
      ⟨ht.mem_boundedTraceCodes G x η y k j ω ωf c Q hQ,
        (ht.replay_eq G x η y k j ω ωf c).symm ▸ ht⟩
    exact Set.mem_iUnion.mpr ⟨c,Set.mem_iUnion.mpr ⟨hc,hr⟩⟩
  · intro c hc d hd hcd
    apply Set.disjoint_left.mpr
    intro u huc hud
    have ht := (mem_finiteTraceCodes_iff G x η y k j ω Q c).mp hc
    have hs := (mem_finiteTraceCodes_iff G x η y k j ω Q d).mp hd
    exact hcd (ht.2.seeded_unique G x η y k j ω _ _ c d hs.2
      (chooseContact (finiteContactSeeds k u)) huc hud).1

 
theorem sum_finite_trace_probabilities [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k M : ℕ) (Q : Finset E)
    (hQ : ∀ i, 1 ≤ i → i ≤ k → η i ⊆ (Q : Set E))
    (hchain : ∀ i ∈ Finset.Icc 1 k, Conn G (η i) (y i) (y (i-1)))
    (hcaps : ∀ i ∈ Finset.Icc 1 k, (cluster G (η i) (y i)).Finite ∧
      (cluster G (η i) (y i)).ncard ≤ M)
    (j : ℕ) (hj : j ≤ k) (ω : Set E) (hyj : y j ∈ cluster G ω x)
    (hfin : (cluster G ω x).Finite) :
    (∑ c ∈ finiteTraceCodes G x η y k j ω Q,
      ∏ i : Fin k, (traceContactCount G η y (replaySplice G x η y c ω) x c (i.val+1):ℝ)⁻¹) = 1 := by
  let S := finiteTraceCodes G x η y k j ω Q
  let A := fun c => {u : Fin k → unitInterval | FollowsContactRule G x η y
    (chooseContact (finiteContactSeeds k u)) c ω}
  have hpart := finite_trace_seed_partition G hloc x η y k M Q hQ hchain hcaps j hj ω hyj hfin
  have hm : ∀ c ∈ S, MeasurableSet (A c) := by
    intro c hc
    exact ((mem_finiteTraceCodes_iff G x η y k j ω Q c).mp hc).2.measurableSet_seed_event
      G x η y k j ω _ c
  have hsum : ∑ c ∈ S, volume (A c) = 1 := by
    rw [← measure_biUnion_finset hpart.2 hm,hpart.1,measure_univ]
  have hr := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_sum (fun c _ => measure_ne_top volume (A c)),ENNReal.toReal_one] at hr
  rw [← hr]
  apply Finset.sum_congr rfl
  intro c hc
  exact (((mem_finiteTraceCodes_iff G x η y k j ω Q c).mp hc).2.seed_probability
    G hloc x η y k j ω _ c (fun i hi hik => (hcaps i (Finset.mem_Icc.mpr ⟨hi,hik⟩)).1)).symm

end FiniteTraceDistribution
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteSpliceState
attribute [local instance] Classical.propDecidable Classical.decEq



theorem encodeFiniteSplice_injective (Q : Finset E) (J : Finset ℕ) :
    Function.Injective (encodeFiniteSplice Q J) := by
  intro a b he
  exact Prod.ext (finiteFieldSet_injective Q (congrArg Prod.fst he))
    (finiteFieldFamily_injective Q J (congrArg Prod.snd he))

end FiniteSpliceState

end Percolation

 
open MeasureTheory
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteSwitchDensity
attribute [local instance] Classical.propDecidable Classical.decEq



theorem finiteInverseLoad_density {I : Type*} [Fintype I]
    (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E) (p : ℝ)
    (inp out : I → SpliceState E) (steps : I → List (ℕ × E)) (y : I → ℕ → V)
    (htrace : ∀ a, SpliceTrace G x (inp a).2 (y a) k 0 (inp a).1 (steps a) (out a).1)
    (hex : ∀ a, SpliceExecution G x (inp a) (steps a) (out a))
    (mass : I → ℝ) (B : Finset (SpliceState E)) (hB : ∀ a, out a ∈ B)
    (f : SpliceState E → ℝ) :
    (∑ a, spliceTupleWeight Q (Finset.Icc 1 k) p (inp a) * mass a * f (out a)) =
      ∑ t ∈ B, spliceTupleWeight Q (Finset.Icc 1 k) p t * finiteInverseLoad out mass t * f t := by
  have hw (a : I) : spliceTupleWeight Q (Finset.Icc 1 k) p (inp a) =
      spliceTupleWeight Q (Finset.Icc 1 k) p (out a) := by
    symm
    apply (hex a).weight G x (inp a) (out a) (steps a) Q (Finset.Icc 1 k) _ p
    intro q hq
    have h := (htrace a).seam_data G x (inp a).2 (y a) k 0 (inp a).1 (out a).1 (steps a) q hq
    exact Finset.mem_Icc.mpr ⟨h.1,h.2.1⟩
  simp only [finiteInverseLoad,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [mul_ite,mul_zero,ite_mul,zero_mul]
  rw [Finset.sum_ite_eq,ite_eq_left (hB a),hw a]

end FiniteSwitchDensity

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ContactIntegratedSecondMoment
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_event_mass_le {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : I → Set Ω)
    (hm : ∀ a, MeasurableSet (P a)) (w : I → ℝ) (B : ℝ)
    (hpoint : ∀ u, (∑ a, if u ∈ P a then w a else 0) ≤ B) :
    (∑ a, w a * μ.real (P a)) ≤ B := by
  let f (a : I) : Ω → ℝ := (P a).indicator (fun _ => w a)
  have hf : ∀ a, Integrable (f a) μ := fun a => (integrable_const _).indicator (hm a)
  have hi := integral_mono (integrable_finsetSum _ (fun a _ => hf a))
    (integrable_const B) (fun u => hpoint u)
  change (∫ u, ∑ a, f a u ∂μ) ≤ (∫ _ : Ω, B ∂μ) at hi
  rw [integral_finsetSum _ (fun a _ => hf a)] at hi
  simpa only [f,integral_indicator_const _ (hm _),smul_eq_mul,mul_comm,
    integral_const,probReal_univ,one_smul,mul_one] using hi



end ContactIntegratedSecondMoment

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteRootLoad
attribute [local instance] Classical.propDecidable Classical.decEq



theorem finiteRootLoad_mean (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (f : SpliceState E → ℝ) :
    (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * finiteRootLoad Q J p f ω) =
      ∑ s ∈ finiteSpliceDomain Q J, spliceTupleWeight Q J p s * f s := by
  rw [finiteSpliceDomain,Finset.sum_image (encodeFiniteSplice_injective Q J).injOn,
    Fintype.sum_prod_type]
  simp only [spliceTupleWeight,finiteRootLoad,Finset.mul_sum,encodeFiniteSplice,
    domainBits_finiteFieldSet,prod_fieldFamilyWeight,finiteFieldWeight,mul_assoc]

 

theorem finiteRootLoad_second_moment (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (f₁ f₂ : SpliceState E → ℝ) :
    (∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      finiteRootLoad Q J₁ p f₁ ω * finiteRootLoad Q J₂ p f₂ ω) =
    ∑ s : FiniteJointData Q J₁ J₂, jointTupleWeight Q J₁ J₂ p (encodeFiniteJoint Q J₁ J₂ s) *
      f₁ (finiteFieldSet Q s.1,finiteFieldFamily Q J₁ s.2.1) *
      f₂ (finiteFieldSet Q s.1,finiteFieldFamily Q J₂ s.2.2) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Fintype.sum_prod_type]
  simp only [finiteRootLoad,Finset.mul_sum,Finset.sum_mul,jointTupleWeight_encode]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η₁ _
  apply Finset.sum_congr rfl
  intro η₂ _
  ring


end FiniteRootLoad

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FinitePairLoad
attribute [local instance] Classical.propDecidable Classical.decEq


theorem pairSpliceOutput_mem (Q : Finset E) (J₁ J₂ : Finset ℕ)
    (s t : SpliceState E) (hs : s ∈ finiteSpliceDomain Q J₁)
    (ht : t ∈ finiteSpliceDomain Q J₂) :
    pairSpliceOutput s t ∈ finiteJointDomain Q J₁ J₂ := by
  have h₁ := (mem_finiteSpliceDomain_iff Q J₁ s).mp hs
  have h₂ := (mem_finiteSpliceDomain_iff Q J₂ t).mp ht
  exact mem_finiteJointDomain_of_support Q J₁ J₂ _ h₁.1 h₁.2.1 h₂.2.1 h₁.2.2 h₂.2.2

 
theorem finiteInverseLoad_mul {I₁ I₂ : Type*} [Fintype I₁] [Fintype I₂]
    (out₁ : I₁ → SpliceState E) (out₂ : I₂ → SpliceState E)
    (m₁ : I₁ → ℝ) (m₂ : I₂ → ℝ) (t : JointSpliceState E) :
    finiteInverseLoad out₁ m₁ (t.1,t.2.1) * finiteInverseLoad out₂ m₂ (t.1,t.2.2) =
    ∑ a, ∑ b, if (out₁ a).1 = (out₂ b).1 ∧ pairSpliceOutput (out₁ a) (out₂ b) = t
      then m₁ a * m₂ b else 0 := by
  simp only [finiteInverseLoad,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have he : (out₁ a = (t.1,t.2.1) ∧ out₂ b = (t.1,t.2.2)) ↔
      ((out₁ a).1 = (out₂ b).1 ∧ pairSpliceOutput (out₁ a) (out₂ b) = t) := by
    cases h₁ : out₁ a with | mk r₁ u₁ =>
      cases h₂ : out₂ b with | mk r₂ u₂ =>
        rcases t with ⟨r,u,v⟩
        simpa [pairSpliceOutput,Prod.mk.injEq] using
          (show (r₁ = r ∧ u₁ = u) ∧ (r₂ = r ∧ u₂ = v) ↔
            r₁ = r₂ ∧ r₁ = r ∧ u₁ = u ∧ u₂ = v from by aesop)
  simp only [← he]
  split_ifs <;> simp_all

 

theorem finiteRootLoad_pair_expansion {I₁ I₂ : Type*} [Fintype I₁] [Fintype I₂]
    (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (out₁ : I₁ → SpliceState E) (out₂ : I₂ → SpliceState E)
    (m₁ : I₁ → ℝ) (m₂ : I₂ → ℝ)
    (hs₁ : ∀ a, out₁ a ∈ finiteSpliceDomain Q J₁)
    (hs₂ : ∀ b, out₂ b ∈ finiteSpliceDomain Q J₂) :
    (∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      finiteRootLoad Q J₁ p (finiteInverseLoad out₁ m₁) ω *
      finiteRootLoad Q J₂ p (finiteInverseLoad out₂ m₂) ω) =
    ∑ a, ∑ b, if (out₁ a).1 = (out₂ b).1 then
      jointTupleWeight Q J₁ J₂ p (pairSpliceOutput (out₁ a) (out₂ b)) * m₁ a * m₂ b else 0 := by
  rw [finiteRootLoad_second_moment]
  have hdom : (∑ s : FiniteJointData Q J₁ J₂,
      jointTupleWeight Q J₁ J₂ p (encodeFiniteJoint Q J₁ J₂ s) *
        finiteInverseLoad out₁ m₁ ((encodeFiniteJoint Q J₁ J₂ s).1,(encodeFiniteJoint Q J₁ J₂ s).2.1) *
        finiteInverseLoad out₂ m₂ ((encodeFiniteJoint Q J₁ J₂ s).1,(encodeFiniteJoint Q J₁ J₂ s).2.2)) =
      ∑ t ∈ finiteJointDomain Q J₁ J₂, jointTupleWeight Q J₁ J₂ p t *
        finiteInverseLoad out₁ m₁ (t.1,t.2.1) * finiteInverseLoad out₂ m₂ (t.1,t.2.2) := by
    rw [finiteJointDomain,Finset.sum_image (encodeFiniteJoint_injective Q J₁ J₂).injOn]
  apply hdom.trans
  simp only [mul_assoc,finiteInverseLoad_mul,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases he : (out₁ a).1 = (out₂ b).1
  · simp only [he,true_and,ite_true]
    rw [Finset.sum_ite_eq,ite_eq_left (pairSpliceOutput_mem Q J₁ J₂ _ _ (hs₁ a) (hs₂ b))]
  · simp [he]

theorem traceIndex_output_code_injective (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V) :
    Function.Injective (fun a : FiniteTraceIndex G x k Q A y =>
      (traceIndexOutput G x k Q A y a,traceIndexCode G x k Q A y a)) := by
  intro a b he
  have hc : traceIndexCode G x k Q A y a = traceIndexCode G x k Q A y b := congrArg Prod.snd he
  have ho : traceIndexOutput G x k Q A y a = traceIndexOutput G x k Q A y b := congrArg Prod.fst he
  apply traceIndex_injective G x k Q A y
  apply Prod.ext
  · apply SpliceExecution.input_unique G x _ _ _ (traceIndexCode G x k Q A y a)
      (traceIndex_valid G x k Q A y a).2
    change SpliceExecution G x b.1.val (traceIndexCode G x k Q A y a) (traceIndexOutput G x k Q A y a)
    rw [hc,ho]
    exact (traceIndex_valid G x k Q A y b).2
  · exact hc

end FinitePairLoad

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WeightedJointMass
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem jointRestored_injective {I : Type*}
    (G : BondGraph V E) (x : V) (k : ℕ)
    (η₁ η₂ : I → ℕ → Set E) (y₁ y₂ : (ℕ → Set E) → ℕ → V)
    (choose₁ choose₂ : ℕ → Set E → E)
    (ω₁ ω₂ ωf : I → Set E) (c₁ c₂ : I → List (ℕ × E))
    (hir : Function.Injective (fun a =>
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a),
        c₁ a,c₂ a)))
    (h₁ : ∀ a, SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (c₁ a) (ωf a))
    (h₂ : ∀ a, SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (c₂ a) (ωf a))
    (hc₁ : ∀ a, c₁ a ≠ []) (hc₂ : ∀ a, c₂ a ≠ [])
    (hsep : ∀ a, GraphSeparated G (cluster G (ωf a) x \ cluster G (ω₁ a) x)
      (cluster G (ωf a) x \ cluster G (ω₂ a) x))
    (hr₁ : ∀ a, FollowsContactRule G x (η₁ a) (y₁ (η₁ a)) choose₁ (c₁ a) (ω₁ a))
    (hr₂ : ∀ a, FollowsContactRule G x (η₂ a) (y₂ (η₂ a)) choose₂ (c₂ a) (ω₂ a))
    : Function.Injective (fun a => jointRestored G x (η₁ a) (η₂ a)
      (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (c₂ a)) := by
  let out (a : I) := jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a))
    (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a)
  let rest (a : I) := jointRestored G x (η₁ a) (η₂ a) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (c₂ a)
  change Function.Injective rest
  intro a b he
  have hη₁ : η₁ a = η₁ b := congrArg (fun s : JointSpliceState E => s.2.1) he
  have hη₂ : η₂ a = η₂ b := congrArg (fun s : JointSpliceState E => s.2.2) he
  have gb₁ : SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ b) (c₁ b) (ωf b) := by
    rw [hη₁]; exact h₁ b
  have gb₂ : SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ b) (c₂ b) (ωf b) := by
    rw [hη₂]; exact h₂ b
  have grb₁ : FollowsContactRule G x (η₁ a) (y₁ (η₁ a)) choose₁ (c₁ b) (ω₁ b) := by
    rw [hη₁]; exact hr₁ b
  have grb₂ : FollowsContactRule G x (η₂ a) (y₂ (η₂ a)) choose₂ (c₂ b) (ω₂ b) := by
    rw [hη₂]; exact hr₂ b
  have hfield : exchangeOn (maskUnion (replayMasks G x (η₂ a) (y₂ (η₂ a)) (c₂ a) (ω₂ a))) (ω₁ a) (ω₂ a) =
      exchangeOn (maskUnion (replayMasks G x (η₂ a) (y₂ (η₂ a)) (c₂ b) (ω₂ b))) (ω₁ b) (ω₂ b) := by
    have hh := congrArg Prod.fst he
    simpa only [rest,jointRestored,← hη₂] using hh
  obtain ⟨hcode₁,hcode₂,hfieldf,haux₁,haux₂⟩ := joint_restore_seeded_unique G x
    (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) choose₁ choose₂ k 0 0
    (ω₁ a) (ω₂ a) (ωf a) (ω₁ b) (ω₂ b) (ωf b)
    (c₁ a) (c₂ a) (c₁ b) (c₂ b) (h₁ a) (h₂ a) gb₁ gb₂
    (hc₁ a) (hc₂ a) (hc₁ b) (hc₂ b) (hsep a) (hsep b)
    (hr₁ a) (hr₂ a) grb₁ grb₂ hfield
  have hout : out a = out b := by
    apply Prod.ext hfieldf
    apply Prod.ext
    · simpa only [out,jointOutput,hη₁] using haux₁
    · simpa only [out,jointOutput,hη₂] using haux₂
  exact hir (Prod.ext hout (Prod.ext hcode₁ hcode₂))

 

theorem finite_joint_weighted_mass_le {I : Type*} [Fintype I]
    (G : BondGraph V E) (x : V) (k : ℕ) (p : unitInterval) (Q : Finset E)
    (η₁ η₂ : I → ℕ → Set E) (y₁ y₂ : (ℕ → Set E) → ℕ → V)
    (choose₁ choose₂ : ℕ → Set E → E)
    (ω₁ ω₂ ωf : I → Set E) (c₁ c₂ : I → List (ℕ × E))
    (hir : Function.Injective (fun a =>
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a),
        c₁ a,c₂ a)))
    (h₁ : ∀ a, SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (c₁ a) (ωf a))
    (h₂ : ∀ a, SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (c₂ a) (ωf a))
    (hc₁ : ∀ a, c₁ a ≠ []) (hc₂ : ∀ a, c₂ a ≠ [])
    (hsep : ∀ a, GraphSeparated G (cluster G (ωf a) x \ cluster G (ω₁ a) x)
      (cluster G (ωf a) x \ cluster G (ω₂ a) x))
    (hr₁ : ∀ a, FollowsContactRule G x (η₁ a) (y₁ (η₁ a)) choose₁ (c₁ a) (ω₁ a))
    (hr₂ : ∀ a, FollowsContactRule G x (η₂ a) (y₂ (η₂ a)) choose₂ (c₂ a) (ω₂ a))
    (m₁ m₂ : (ℕ → Set E) → ℝ) (hm₁ : ∀ η, 0 ≤ m₁ η) (hm₂ : ∀ η, 0 ≤ m₂ η)
    (B : Finset (JointSpliceState E))
    (hB : ∀ a, jointRestored G x (η₁ a) (η₂ a) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (c₂ a) ∈ B) :
    (∑ a, jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a)) * m₁ (η₁ a) * m₂ (η₂ a)) ≤
      ∑ s ∈ B, jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p s * m₁ s.2.1 * m₂ s.2.2 := by
  let out (a : I) := jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a))
    (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a)
  let rest (a : I) := jointRestored G x (η₁ a) (η₂ a) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (c₂ a)
  have hinj : Function.Injective rest := jointRestored_injective G x k η₁ η₂ y₁ y₂ choose₁ choose₂
    ω₁ ω₂ ωf c₁ c₂ hir h₁ h₂ hc₁ hc₂ hsep hr₁ hr₂
  have hw : ∀ a, jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p (out a) =
      jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p (rest a) := by
    intro a
    apply (h₁ a).joint_weight G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) k 0 0
      (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a) (h₂ a) (hsep a) Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
    · intro q hq
      have hr := (h₁ a).seam_data G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (ωf a) (c₁ a) q hq
      exact Finset.mem_Icc.mpr ⟨hr.1,hr.2.1⟩
    · intro q hq
      have hr := (h₂ a).seam_data G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (ωf a) (c₂ a) q hq
      exact Finset.mem_Icc.mpr ⟨hr.1,hr.2.1⟩
  change (∑ a, jointTupleWeight Q _ _ p (out a) * m₁ (η₁ a) * m₂ (η₂ a)) ≤ _
  simp_rw [hw]
  change (∑ a, jointTupleWeight Q _ _ p (rest a) * m₁ (rest a).2.1 * m₂ (rest a).2.2) ≤ _
  rw [← Finset.sum_image (f := fun s : JointSpliceState E =>
    jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p s * m₁ s.2.1 * m₂ s.2.2) hinj.injOn]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hs
    exact hB a
  · intro s _ _
    exact mul_nonneg (mul_nonneg (jointTupleWeight_nonneg Q _ _ p s) (hm₁ _)) (hm₂ _)

end WeightedJointMass

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteFamilyIntegral
attribute [local instance] Classical.propDecidable Classical.decEq


theorem finiteFamilyIntegral_nonneg (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (f : (ℕ → Set E) → ℝ) (hf : ∀ η, 0 ≤ f η) : 0 ≤ finiteFamilyIntegral Q J p f := by
  exact Finset.sum_nonneg fun η _ => mul_nonneg (finiteFamilyWeight_nonneg Q J p η) (hf _)

theorem finiteFamilyIntegral_mono (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (f g : (ℕ → Set E) → ℝ) (hfg : ∀ η, f η ≤ g η) :
    finiteFamilyIntegral Q J p f ≤ finiteFamilyIntegral Q J p g := by
  exact Finset.sum_le_sum fun η _ => mul_le_mul_of_nonneg_left (hfg _) (finiteFamilyWeight_nonneg Q J p η)

theorem finiteFamilyIntegral_sum {I : Type*} (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (S : Finset I) (f : I → (ℕ → Set E) → ℝ) :
    finiteFamilyIntegral Q J p (fun η => ∑ i ∈ S, f i η) =
      ∑ i ∈ S, finiteFamilyIntegral Q J p (f i) := by
  simp only [finiteFamilyIntegral,Finset.mul_sum]
  exact Finset.sum_comm

 
theorem finiteJointDomain_integral_factor (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (f₁ f₂ : Set E → (ℕ → Set E) → ℝ) :
    (∑ s ∈ finiteJointDomain Q J₁ J₂, jointTupleWeight Q J₁ J₂ p s * f₁ s.1 s.2.1 * f₂ s.1 s.2.2) =
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      finiteFamilyIntegral Q J₁ p (f₁ (finiteFieldSet Q ω)) *
      finiteFamilyIntegral Q J₂ p (f₂ (finiteFieldSet Q ω)) := by
  rw [finiteJointDomain,Finset.sum_image (encodeFiniteJoint_injective Q J₁ J₂).injOn]
  simp only [jointTupleWeight_encode]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Fintype.sum_prod_type]
  simp only [finiteFamilyIntegral,Finset.mul_sum,Finset.sum_mul,encodeFiniteJoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η₂ _
  apply Finset.sum_congr rfl
  intro η₁ _
  ring

theorem finiteJointDomain_weighted_event_factor (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (P : Set E → Prop) (H₁ H₂ : Set E → (ℕ → Set E) → Prop)
    (m₁ m₂ : (ℕ → Set E) → ℝ) :
    (∑ s ∈ (finiteJointDomain Q J₁ J₂).filter (fun s => P s.1 ∧ H₁ s.1 s.2.1 ∧ H₂ s.1 s.2.2),
      jointTupleWeight Q J₁ J₂ p s * m₁ s.2.1 * m₂ s.2.2) =
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      (if P (finiteFieldSet Q ω) then
        finiteFamilyIntegral Q J₁ p (fun η => if H₁ (finiteFieldSet Q ω) η then m₁ η else 0) *
        finiteFamilyIntegral Q J₂ p (fun η => if H₂ (finiteFieldSet Q ω) η then m₂ η else 0) else 0) := by
  rw [Finset.sum_filter]
  have he : (∑ s ∈ finiteJointDomain Q J₁ J₂,
      if P s.1 ∧ H₁ s.1 s.2.1 ∧ H₂ s.1 s.2.2 then
        jointTupleWeight Q J₁ J₂ p s * m₁ s.2.1 * m₂ s.2.2 else 0) =
    ∑ s ∈ finiteJointDomain Q J₁ J₂, jointTupleWeight Q J₁ J₂ p s *
      (if P s.1 ∧ H₁ s.1 s.2.1 then m₁ s.2.1 else 0) *
      (if H₂ s.1 s.2.2 then m₂ s.2.2 else 0) := by
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> simp_all
  rw [he,finiteJointDomain_integral_factor Q J₁ J₂ p
    (fun ω η => if P ω ∧ H₁ ω η then m₁ η else 0)
    (fun ω η => if H₂ ω η then m₂ η else 0)]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hP : P (finiteFieldSet Q ω)
  · simp only [hP,true_and,ite_true,mul_assoc]
  · simp [hP,finiteFamilyIntegral]

end FiniteFamilyIntegral

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WeightedSeparatedSecondMoment
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_separated_weighted_second_moment_le {I : Type*} [Fintype I]
    (G : BondGraph V E) (x : V) (k n M : ℕ) (p : unitInterval) (Q : Finset E)
    (η₁ η₂ : I → ℕ → Set E) (y₁ y₂ : (ℕ → Set E) → ℕ → V)
    (success₁ success₂ : (ℕ → Set E) → Prop)
    (m₁ m₂ : (ℕ → Set E) → ℝ) (hm₁ : ∀ η, 0 ≤ m₁ η) (hm₂ : ∀ η, 0 ≤ m₂ η)
    (choose₁ choose₂ : ℕ → Set E → E)
    (ω₁ ω₂ ωf : I → Set E) (c₁ c₂ : I → List (ℕ × E))
    (hir : Function.Injective (fun a =>
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a),
        c₁ a,c₂ a)))
    (h₁ : ∀ a, SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (c₁ a) (ωf a))
    (h₂ : ∀ a, SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (c₂ a) (ωf a))
    (hc₁ : ∀ a, c₁ a ≠ []) (hc₂ : ∀ a, c₂ a ≠ [])
    (hsep : ∀ a, GraphSeparated G (cluster G (ωf a) x \ cluster G (ω₁ a) x)
      (cluster G (ωf a) x \ cluster G (ω₂ a) x))
    (hr₁ : ∀ a, FollowsContactRule G x (η₁ a) (y₁ (η₁ a)) choose₁ (c₁ a) (ω₁ a))
    (hr₂ : ∀ a, FollowsContactRule G x (η₂ a) (y₂ (η₂ a)) choose₂ (c₂ a) (ω₂ a))
    (hbin : ∀ a, (cluster G (ω₁ a) x).Finite ∧ n ≤ (cluster G (ω₁ a) x).ncard ∧
      (cluster G (ω₁ a) x).ncard < 2*n)
    (hcap₂ : ∀ a i, 1 ≤ i → i ≤ k → (cluster G (η₂ a i) (y₂ (η₂ a) i)).Finite ∧
      (cluster G (η₂ a i) (y₂ (η₂ a) i)).ncard ≤ M)
    (hsc₁ : ∀ a, success₁ (η₁ a)) (hsc₂ : ∀ a, success₂ (η₂ a))
    (hsω₁ : ∀ a, ω₁ a ⊆ (Q : Set E)) (hsω₂ : ∀ a, ω₂ a ⊆ (Q : Set E))
    (hsη₁ : ∀ a i, η₁ a i ⊆ (Q : Set E)) (hsη₂ : ∀ a i, η₂ a i ⊆ (Q : Set E))
    (hz₁ : ∀ a i, i ∉ Finset.Icc 1 k → η₁ a i = ∅)
    (hz₂ : ∀ a i, i ∉ Finset.Icc 1 k → η₂ a i = ∅) :
    (∑ a, jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a)) * m₁ (η₁ a) * m₂ (η₂ a)) ≤
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      (if (cluster G (finiteFieldSet Q ω) x).Finite ∧
        n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
        (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then
        finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => if success₁ η ∧
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₁ η) k).Nonempty then m₁ η else 0) *
        finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => if success₂ η ∧
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₂ η) k).Nonempty then m₂ η else 0) else 0) := by
  let J := Finset.Icc 1 k
  let P (ω : Set E) := (cluster G ω x).Finite ∧ n-k*M ≤ (cluster G ω x).ncard ∧
    (cluster G ω x).ncard < 2*n
  let H₁ (ω : Set E) (η : ℕ → Set E) := success₁ η ∧
    (cluster G ω x ∩ trajectoryUnion G η (y₁ η) k).Nonempty
  let H₂ (ω : Set E) (η : ℕ → Set E) := success₂ η ∧
    (cluster G ω x ∩ trajectoryUnion G η (y₂ η) k).Nonempty
  let B := (finiteJointDomain Q J J).filter fun s => P s.1 ∧ H₁ s.1 s.2.1 ∧ H₂ s.1 s.2.2
  have hB (a : I) : jointRestored G x (η₁ a) (η₂ a) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (c₂ a) ∈ B := by
    apply Finset.mem_filter.mpr
    refine ⟨mem_finiteJointDomain_of_support Q J J _
      (exchangeOn_subset _ _ _ _ (hsω₁ a) (hsω₂ a)) (hsη₁ a) (hsη₂ a) (hz₁ a) (hz₂ a),?_⟩
    have hroot := (h₁ a).joint_restored_size G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a))
      k 0 0 n M (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a) (h₂ a) (hc₁ a) (hc₂ a) (hsep a)
      (hbin a).1 (hbin a).2.1 (hbin a).2.2 (hcap₂ a)
    have hhits := (h₁ a).joint_trajectory_hits G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a))
      k 0 0 (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a) (h₂ a) (hc₁ a) (hc₂ a) (hsep a)
    exact ⟨hroot,⟨hsc₁ a,hhits.1⟩,hsc₂ a,hhits.2⟩
  have h := finite_joint_weighted_mass_le G x k p Q η₁ η₂ y₁ y₂ choose₁ choose₂ ω₁ ω₂ ωf c₁ c₂
    hir h₁ h₂ hc₁ hc₂ hsep hr₁ hr₂ m₁ m₂ hm₁ hm₂ B hB
  apply h.trans_eq
  convert finiteJointDomain_weighted_event_factor Q J J p P H₁ H₂ m₁ m₂ using 1 <;>
    simp only [B, J, P, H₁, H₂]
  apply Finset.sum_congr rfl
  intro ω _
  apply congrArg (fun z : ℝ => finiteFieldWeight Q p ω * z)
  split_ifs
  · apply congrArg₂ (· * ·)
    · apply congrArg (finiteFamilyIntegral Q (Finset.Icc 1 k) p)
      funext η
      split_ifs <;> rfl
    · apply congrArg (finiteFamilyIntegral Q (Finset.Icc 1 k) p)
      funext η
      split_ifs <;> rfl
  · rfl

end WeightedSeparatedSecondMoment

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section WeightedContactSecondMoment
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_separated_weighted_contact_second_moment_le {I : Type*} [Fintype I] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (k n M : ℕ) (p : unitInterval) (Q : Finset E)
    (η₁ η₂ : I → ℕ → Set E) (y₁ y₂ : (ℕ → Set E) → ℕ → V)
    (success₁ success₂ : (ℕ → Set E) → Prop)
    (m₁ m₂ : (ℕ → Set E) → ℝ) (hm₁ : ∀ η, 0 ≤ m₁ η) (hm₂ : ∀ η, 0 ≤ m₂ η)
    (ω₁ ω₂ ωf : I → Set E) (c₁ c₂ : I → List (ℕ × E))
    (hir : Function.Injective (fun a =>
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a),
        c₁ a,c₂ a)))
    (h₁ : ∀ a, SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (c₁ a) (ωf a))
    (h₂ : ∀ a, SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (c₂ a) (ωf a))
    (hc₁ : ∀ a, c₁ a ≠ []) (hc₂ : ∀ a, c₂ a ≠ [])
    (hsep : ∀ a, GraphSeparated G (cluster G (ωf a) x \ cluster G (ω₁ a) x)
      (cluster G (ωf a) x \ cluster G (ω₂ a) x))
    (hbin : ∀ a, (cluster G (ω₁ a) x).Finite ∧ n ≤ (cluster G (ω₁ a) x).ncard ∧
      (cluster G (ω₁ a) x).ncard < 2*n)
    (hcap₁ : ∀ a i, 1 ≤ i → i ≤ k → (cluster G (η₁ a i) (y₁ (η₁ a) i)).Finite)
    (hcap₂ : ∀ a i, 1 ≤ i → i ≤ k → (cluster G (η₂ a i) (y₂ (η₂ a) i)).Finite ∧
      (cluster G (η₂ a i) (y₂ (η₂ a) i)).ncard ≤ M)
    (hsc₁ : ∀ a, success₁ (η₁ a)) (hsc₂ : ∀ a, success₂ (η₂ a))
    (hsω₁ : ∀ a, ω₁ a ⊆ (Q : Set E)) (hsω₂ : ∀ a, ω₂ a ⊆ (Q : Set E))
    (hsη₁ : ∀ a i, η₁ a i ⊆ (Q : Set E)) (hsη₂ : ∀ a i, η₂ a i ⊆ (Q : Set E))
    (hz₁ : ∀ a i, i ∉ Finset.Icc 1 k → η₁ a i = ∅)
    (hz₂ : ∀ a i, i ∉ Finset.Icc 1 k → η₂ a i = ∅) :
    (∑ a, jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a)) * m₁ (η₁ a) * m₂ (η₂ a) *
      (∏ i : Fin k, (traceContactCount G (η₁ a) (y₁ (η₁ a)) (ωf a) x (c₁ a) (i.val+1):ℝ)⁻¹) *
      (∏ i : Fin k, (traceContactCount G (η₂ a) (y₂ (η₂ a)) (ωf a) x (c₂ a) (i.val+1):ℝ)⁻¹)) ≤
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      (if (cluster G (finiteFieldSet Q ω) x).Finite ∧
        n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
        (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then
        finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => if success₁ η ∧
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₁ η) k).Nonempty then m₁ η else 0) *
        finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => if success₂ η ∧
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₂ η) k).Nonempty then m₂ η else 0) else 0) := by
  let S := Fin k → unitInterval
  let μ : Measure (S × S) := (volume : Measure S).prod volume
  let P₁ (a : I) : Set S := {u | FollowsContactRule G x (η₁ a) (y₁ (η₁ a))
    (chooseContact (finiteContactSeeds k u)) (c₁ a) (ω₁ a)}
  let P₂ (a : I) : Set S := {u | FollowsContactRule G x (η₂ a) (y₂ (η₂ a))
    (chooseContact (finiteContactSeeds k u)) (c₂ a) (ω₂ a)}
  let w (a : I) := jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
    (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a)) * m₁ (η₁ a) * m₂ (η₂ a)
  have hmeas₁ (a : I) : MeasurableSet (P₁ a) :=
    (h₁ a).measurableSet_seed_event G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (ωf a) (c₁ a)
  have hmeas₂ (a : I) : MeasurableSet (P₂ a) :=
    (h₂ a).measurableSet_seed_event G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (ωf a) (c₂ a)
  have hp (a : I) : μ.real (P₁ a ×ˢ P₂ a) =
      (∏ i : Fin k, (traceContactCount G (η₁ a) (y₁ (η₁ a)) (ωf a) x (c₁ a) (i.val+1):ℝ)⁻¹) *
      (∏ i : Fin k, (traceContactCount G (η₂ a) (y₂ (η₂ a)) (ωf a) x (c₂ a) (i.val+1):ℝ)⁻¹) := by
    rw [measureReal_def,Measure.prod_prod,ENNReal.toReal_mul,
      (h₁ a).seed_probability G hloc x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (ωf a) (c₁ a) (hcap₁ a),
      (h₂ a).seed_probability G hloc x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (ωf a) (c₂ a) (fun i hi hik => (hcap₂ a i hi hik).1)]
  conv_lhs => arg 2; ext a; rw [mul_assoc,← hp a]
  apply finite_event_mass_le μ (fun a => P₁ a ×ˢ P₂ a) (fun a => (hmeas₁ a).prod (hmeas₂ a)) w
  intro u
  let J := {a : I // u ∈ P₁ a ×ˢ P₂ a}
  have hb := finite_separated_weighted_second_moment_le G x k n M p Q
    (fun a : J => η₁ a.val) (fun a : J => η₂ a.val) y₁ y₂ success₁ success₂ m₁ m₂ hm₁ hm₂
    (chooseContact (finiteContactSeeds k u.1)) (chooseContact (finiteContactSeeds k u.2))
    (fun a : J => ω₁ a.val) (fun a : J => ω₂ a.val) (fun a : J => ωf a.val)
    (fun a : J => c₁ a.val) (fun a : J => c₂ a.val)
    (fun _ _ he => Subtype.ext (hir he)) (fun a => h₁ a.val) (fun a => h₂ a.val)
    (fun a => hc₁ a.val) (fun a => hc₂ a.val) (fun a => hsep a.val)
    (fun a => a.property.1) (fun a => a.property.2)
    (fun a => hbin a.val) (fun a => hcap₂ a.val) (fun a => hsc₁ a.val) (fun a => hsc₂ a.val)
    (fun a => hsω₁ a.val) (fun a => hsω₂ a.val) (fun a => hsη₁ a.val) (fun a => hsη₂ a.val)
    (fun a => hz₁ a.val) (fun a => hz₂ a.val)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  have he := Finset.sum_subtype (p := fun a => u ∈ P₁ a ×ˢ P₂ a) (F := inferInstance) (Finset.univ.filter (fun a => u ∈ P₁ a ×ˢ P₂ a))
    (by intro a; simp) w
  simpa [Finset.sum_filter,w] using he

end WeightedContactSecondMoment

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Transport_TrajectoryMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trajectory Mass for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section OldPathWeight
attribute [local instance] Classical.propDecidable Classical.decEq


theorem finiteFieldIntegral_nonneg (Q : Finset E) (p : unitInterval) (f : Set E → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ finiteFieldIntegral Q p f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (finiteFieldWeight_nonneg Q p ω) (hf _)

theorem finiteFieldIntegral_sum {I : Type*} (Q : Finset E) (p : ℝ) (S : Finset I)
    (f : I → Set E → ℝ) :
    finiteFieldIntegral Q p (fun ω => ∑ i ∈ S, f i ω) =
      ∑ i ∈ S, finiteFieldIntegral Q p (f i) := by
  simp only [finiteFieldIntegral, Finset.mul_sum]
  exact Finset.sum_comm

 

theorem finiteFamilyIntegral_prod (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (f : ↥J → Set E → ℝ) :
    finiteFamilyIntegral Q J p (fun η => ∏ i : ↥J, f i (η i)) =
      ∏ i : ↥J, finiteFieldIntegral Q p (f i) := by
  simp only [finiteFamilyIntegral, finiteFamilyWeight, finiteFieldFamily_at,
    ← Finset.prod_mul_distrib, finiteFieldIntegral]
  exact (Fintype.prod_sum (fun (i : ↥J) (ω : FiniteField Q) =>
    finiteFieldWeight Q p ω * f i (finiteFieldSet Q ω))).symm



theorem oldPathWeight_integral (Q : Finset E) (k : ℕ) (p : ℝ)
    (q : Set E → V → V → ℝ) (y : ℕ → V) :
    finiteFamilyIntegral Q (Finset.Icc 1 k) p (oldPathWeight k q y) =
      ∏ i : ↥(Finset.Icc 1 k), finiteFieldIntegral Q p (fun ω => q ω (y i) (y (i.val-1))) := by
  unfold oldPathWeight
  exact finiteFamilyIntegral_prod Q (Finset.Icc 1 k) p
    (fun i ω => q ω (y i) (y (i.val-1)))



end OldPathWeight

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IndependentOldRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*}



theorem oldRunWeight_integral (Q : Finset E) (p : ℝ) (k : ℕ)
    (q : Set E → W → W → ℝ) (z : W) (y : Fin k → W) :
    finiteFamilyIntegral Q (Finset.Icc 1 k) p
      (fun η => oldRunWeight (fun i => q (η i)) k z y) =
    oldRunWeight (fun _ => finiteOldKernel Q p q) k z y := by
  calc
    _ = finiteFamilyIntegral Q (Finset.Icc 1 k) p
        (fun η => oldPathWeight k q (oldRunVertices k z y) η) := by
      apply congrArg (finiteFamilyIntegral Q (Finset.Icc 1 k) p)
      funext η
      exact (oldPathWeight_oldRunVertices k q η z y).symm
    _ = ∏ i : ↥(Finset.Icc 1 k), finiteOldKernel Q p q
        (oldRunVertices k z y i) (oldRunVertices k z y (i.val-1)) :=
      oldPathWeight_integral Q k p q _
    _ = oldRunWeight (fun _ => finiteOldKernel Q p q) k z y :=
      oldPathWeight_oldRunVertices k (fun (_ : Set E) => finiteOldKernel Q p q)
        (fun _ => ∅) z y



end IndependentOldRun

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ChoiceForwardDensity
attribute [local instance] Classical.propDecidable Classical.decEq
variable {P : Type*}



theorem sum_traceIndexMass [Nonempty E] (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (k M : ℕ) (Q : Finset E) (A : Finset (SpliceState E))
    (y : SpliceState E → ℕ → V) (s : ↥A)
    (hs : s.val ∈ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hy : y s.val 0 ∈ cluster G s.val.1 x)
    (hchain : ∀ i ∈ Finset.Icc 1 k, Conn G (s.val.2 i) (y s.val i) (y s.val (i-1)))
    (hcaps : ∀ i ∈ Finset.Icc 1 k, (cluster G (s.val.2 i) (y s.val i)).Finite ∧
      (cluster G (s.val.2 i) (y s.val i)).ncard ≤ M) :
    (∑ c : ↥(finiteTraceCodes G x s.val.2 (y s.val) k 0 s.val.1 Q),
      traceIndexMass G x k Q A y ⟨s,c⟩) = 1 := by
  have hs' := (mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) s.val).mp hs
  have hn := sum_finite_trace_probabilities G hloc x s.val.2 (y s.val) k M Q
    (fun i _ _ => hs'.2.1 i) hchain hcaps 0 (Nat.zero_le _) s.val.1 hy
    (cluster_finite_of_finite_edges G (Q.finite_toSet.subset hs'.1) x)
  rw [← Finset.sum_coe_sort (finiteTraceCodes G x s.val.2 (y s.val) k 0 s.val.1 Q)] at hn
  rw [← hn]
  apply Finset.sum_congr rfl
  intro c _
  have ht := ((mem_finiteTraceCodes_iff G x s.val.2 (y s.val) k 0 s.val.1 Q c.val).mp c.property).2
  have hf := ht.runMasks_first G x s.val.2 (y s.val) k 0 s.val.1 _ c.val s.val.2 (by intros; rfl)
  simp only [traceIndexMass,traceIndexOutput,hf]

 
theorem finiteChoiceForwardLoad_mean [Fintype P] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (k M : ℕ) (Q : Finset E) (p : ℝ)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (q : SpliceState E → P → ℝ)
    (hA : ∀ r, A r ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hy : ∀ r s, s ∈ A r → y r s 0 ∈ cluster G s.1 x)
    (hchain : ∀ r s, s ∈ A r → ∀ i ∈ Finset.Icc 1 k, Conn G (s.2 i) (y r s i) (y r s (i-1)))
    (hcaps : ∀ r s, s ∈ A r → ∀ i ∈ Finset.Icc 1 k,
      (cluster G (s.2 i) (y r s i)).Finite ∧ (cluster G (s.2 i) (y r s i)).ncard ≤ M) :
    (∑ t ∈ finiteSpliceDomain Q (Finset.Icc 1 k), spliceTupleWeight Q (Finset.Icc 1 k) p t *
      finiteChoiceForwardLoad G x k Q A y q t) =
      ∑ r, ∑ s ∈ A r, spliceTupleWeight Q (Finset.Icc 1 k) p s * q s r := by
  have hd := finiteInverseLoad_density G x k Q p
    (choiceTraceInput G x k Q A y) (choiceTraceOutput G x k Q A y)
    (choiceTraceCode G x k Q A y) (fun a => y a.1 a.2.1.val)
    (fun a => (traceIndex_valid G x k Q (A a.1) (y a.1) a.2).1)
    (fun a => (traceIndex_valid G x k Q (A a.1) (y a.1) a.2).2)
    (choiceTraceMass G x k Q A y q) (finiteSpliceDomain Q (Finset.Icc 1 k))
    (fun a => traceIndexOutput_mem G x k Q (A a.1) (y a.1) (hA a.1) a.2) (fun _ => 1)
  simp only [mul_one] at hd
  unfold finiteChoiceForwardLoad
  rw [← hd,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r _
  rw [Fintype.sum_sigma,← Finset.sum_coe_sort (A r)
    (fun s => spliceTupleWeight Q (Finset.Icc 1 k) p s * q s r)]
  apply Finset.sum_congr rfl
  intro s _
  change (∑ c : ↥(finiteTraceCodes G x s.val.2 (y r s.val) k 0 s.val.1 Q),
    spliceTupleWeight Q (Finset.Icc 1 k) p s.val *
      (q s.val r * traceIndexMass G x k Q (A r) (y r) ⟨s,c⟩)) = _
  simp only [← mul_assoc,← Finset.mul_sum]
  rw [sum_traceIndexMass G hloc x k M Q (A r) (y r) s (hA r s.property)
    (hy r _ s.property) (hchain r _ s.property) (hcaps r _ s.property),mul_one]

end ChoiceForwardDensity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EndpointRootMass
attribute [local instance] Classical.propDecidable Classical.decEq


theorem auxiliaryTupleWeight_nonneg (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (s : SpliceState E) : 0 ≤ auxiliaryTupleWeight Q J p s :=
  Finset.prod_nonneg fun _ _ => bernoulliWeight_nonneg _ _ p



theorem sum_endpointRootMass {I : Type*} [Fintype I]
    (Q : Finset E) (J : Finset ℕ) (p : ℝ) (out : I → SpliceState E)
    (endpoint : I → V) (m : I → ℝ) (ω : Set E) (S : Finset V) :
    (∑ z ∈ S, endpointRootMass Q J p out endpoint m ω z) =
      ∑ a, if (out a).1 = ω ∧ endpoint a ∈ S then auxiliaryTupleWeight Q J p (out a) * m a else 0 := by
  simp only [endpointRootMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hr : (out a).1 = ω
  · simp only [hr,true_and,Finset.sum_ite_eq]
  · simp [hr]

end EndpointRootMass
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NearPairMass
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_near_pair_mass_le_cover {I₁ I₂ : Type*} [Fintype I₁] [Fintype I₂]
    (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : unitInterval)
    (out₁ : I₁ → SpliceState E) (out₂ : I₂ → SpliceState E)
    (m₁ : I₁ → ℝ) (m₂ : I₂ → ℝ) (hm₁ : ∀ a, 0 ≤ m₁ a) (hm₂ : ∀ b, 0 ≤ m₂ b)
    (endpoint : I₂ → V) (R : I₁ → I₂ → Prop) (S : I₁ → Finset V)
    (hS : ∀ a b, (out₁ a).1 = (out₂ b).1 → R a b → endpoint b ∈ S a) :
    (∑ a, ∑ b, if (out₁ a).1 = (out₂ b).1 ∧ R a b then
      jointTupleWeight Q J₁ J₂ p (pairSpliceOutput (out₁ a) (out₂ b)) * m₁ a * m₂ b else 0) ≤
    ∑ a, spliceTupleWeight Q J₁ p (out₁ a) * m₁ a *
      ∑ z ∈ S a, endpointRootMass Q J₂ p out₂ endpoint m₂ (out₁ a).1 z := by
  apply Finset.sum_le_sum
  intro a _
  rw [sum_endpointRootMass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  by_cases h : (out₁ a).1 = (out₂ b).1 ∧ R a b
  · have hh : (out₂ b).1 = (out₁ a).1 ∧ endpoint b ∈ S a :=
      ⟨h.1.symm,hS a b h.1 h.2⟩
    rw [ite_eq_left h,ite_eq_left hh]
    change (spliceTupleWeight Q J₁ p (out₁ a) * auxiliaryTupleWeight Q J₂ p (out₂ b)) *
      m₁ a * m₂ b ≤ _
    ring_nf
    exact le_refl _
  · rw [ite_eq_right h]
    apply mul_nonneg (mul_nonneg (spliceTupleWeight_nonneg Q J₁ p _) (hm₁ a))
    split_ifs
    · exact mul_nonneg (auxiliaryTupleWeight_nonneg Q J₂ p _) (hm₂ b)
    · exact le_refl 0

 

theorem finite_near_pair_mass_le {I₁ I₂ : Type*} [Fintype I₁] [Fintype I₂]
    (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : unitInterval)
    (out₁ : I₁ → SpliceState E) (out₂ : I₂ → SpliceState E)
    (m₁ : I₁ → ℝ) (m₂ : I₂ → ℝ) (hm₁ : ∀ a, 0 ≤ m₁ a) (hm₂ : ∀ b, 0 ≤ m₂ b)
    (endpoint : I₂ → V) (R : I₁ → I₂ → Prop) (S : I₁ → Finset V)
    (hS : ∀ a b, (out₁ a).1 = (out₂ b).1 → R a b → endpoint b ∈ S a)
    (N : ℕ) (hN : ∀ a, (S a).card ≤ N) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ a z, z ∈ S a → endpointRootMass Q J₂ p out₂ endpoint m₂ (out₁ a).1 z ≤ C) :
    (∑ a, ∑ b, if (out₁ a).1 = (out₂ b).1 ∧ R a b then
      jointTupleWeight Q J₁ J₂ p (pairSpliceOutput (out₁ a) (out₂ b)) * m₁ a * m₂ b else 0) ≤
    (N:ℝ) * C * ∑ a, spliceTupleWeight Q J₁ p (out₁ a) * m₁ a := by
  apply (finite_near_pair_mass_le_cover Q J₁ J₂ p out₁ out₂ m₁ m₂ hm₁ hm₂ endpoint R S hS).trans
  calc
    _ ≤ ∑ a, spliceTupleWeight Q J₁ p (out₁ a) * m₁ a * ((N:ℝ)*C) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (spliceTupleWeight_nonneg Q J₁ p _) (hm₁ a))
      calc
        _ ≤ ∑ _z ∈ S a, C := Finset.sum_le_sum (fun z hz => hb a z hz)
        _ = ((S a).card:ℝ) * C := by simp
        _ ≤ (N:ℝ)*C := mul_le_mul_of_nonneg_right (by exact_mod_cast hN a) hC
    _ = _ := by rw [← Finset.sum_mul]; ring

end NearPairMass
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NearHangingMass
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem SpliceTrace.head_hanging (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j i : ℕ) (ω ωf : Set E) (e : E) (rest : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω ((i,e)::rest) ωf) :
    hangingSide G ωf x e = cluster G ωf x \ cluster G ω x := by
  rw [hangingSide,h.head_cut G x η y k j i ω ωf e rest]

theorem SpliceTrace.head_hanging_cap (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j i M : ℕ) (ω ωf : Set E) (e : E) (rest : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω ((i,e)::rest) ωf)
    (hcaps : ∀ l, 1 ≤ l → l ≤ k →
      (cluster G (η l) (y l)).Finite ∧ (cluster G (η l) (y l)).ncard ≤ M) :
    (hangingSide G ωf x e).ncard ≤ k*M := by
  rw [h.head_hanging G x η y k j i ω ωf e rest]
  exact (h.added_finite_cap G x η y k j M ω ωf ((i,e)::rest) hcaps).2



end NearHangingMass

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section OldRunArrival
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*} [Fintype W]

theorem oldRunArrival_nonneg (K : ℕ → W → W → ℝ) (hK : ∀ i a b, 0 ≤ K i a b)
    (k : ℕ) (z : W) (A : Finset W) : 0 ≤ oldRunArrival K k z A := by
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact oldRunWeight_nonneg K hK k z y
  · exact le_refl 0

theorem oldRunArrival_zero (K : ℕ → W → W → ℝ) (z : W) (A : Finset W) :
    oldRunArrival K 0 z A = if z ∈ A then 1 else 0 := by
  by_cases h : z ∈ A
  · simp [oldRunArrival,oldRunVertices,oldRunWeight,h]
  · simp [oldRunArrival,oldRunVertices,h]

theorem oldRunArrival_succ (K : ℕ → W → W → ℝ) (k : ℕ) (z : W) (A : Finset W) :
    oldRunArrival K (k+1) z A = ∑ a, K (k+1) z a * oldRunArrival K k a A := by
  unfold oldRunArrival
  rw [Fintype.sum_equiv (oldRunConsEquiv k) _
    (fun y => if oldRunVertices k y.1 y.2 0 ∈ A then
      K (k+1) z y.1 * oldRunWeight K k y.1 y.2 else 0)
    (by
      intro y
      by_cases h : oldRunVertices k (y 0) (Fin.tail y) 0 ∈ A
      · simp [oldRunVertices_succ_of_le k z y 0 (Nat.zero_le k),oldRunConsEquiv,oldRunWeight,h]
      · simp [oldRunVertices_succ_of_le k z y 0 (Nat.zero_le k),oldRunConsEquiv,h]),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.mul_sum,mul_ite,mul_zero]

 

theorem sum_oldRunArrival_le (K : ℕ → W → W → ℝ) (hK : ∀ i a b, 0 ≤ K i a b)
    (u : ℝ) (hu : 0 ≤ u) (hcol : ∀ i b, ∑ a, K i a b ≤ u) (k : ℕ) (A : Finset W) :
    (∑ z, oldRunArrival K k z A) ≤ (A.card:ℝ) * u^k := by
  induction k with
  | zero => simp [oldRunArrival_zero]
  | succ k ih =>
    simp only [oldRunArrival_succ]
    rw [Finset.sum_comm]
    calc
      _ = ∑ a, (∑ z, K (k+1) z a) * oldRunArrival K k a A := by
        simp only [Finset.sum_mul]
      _ ≤ ∑ a, u * oldRunArrival K k a A := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_right (hcol _ _) (oldRunArrival_nonneg K hK k a A)
      _ = u * ∑ a, oldRunArrival K k a A := (Finset.mul_sum _ _ _).symm
      _ ≤ u*((A.card:ℝ)*u^k) := mul_le_mul_of_nonneg_left ih hu
      _ = (A.card:ℝ)*u^(k+1) := by ring


end OldRunArrival

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TrajectoryTransport
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

 

theorem RootTransport.real (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (m : V → V → ℝ)
    (hi : ∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y)
    (hr : ∀ x, Summable (m x)) (hc : ∀ y, Summable (fun x => m x y)) :
    (∑ i, weight i * ∑' y, m (root i) y) =
      (∑ i, weight i * ∑' x, m x (root i)) := by
  have ht := htr (fun x y => (m x y:ℂ))
    (fun a ha x y => congrArg Complex.ofReal (hi a ha x y))
    (fun x => Complex.summable_ofReal.mpr (hr x))
    (fun y => Complex.summable_ofReal.mpr (hc y))
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_tsum] using ht

 

theorem transported_column_le (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (m : V → V → ℝ) (hm : ∀ x y, 0 ≤ m x y)
    (hi : ∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y)
    (hr : ∀ x, Summable (m x)) (hcol : ∀ y, Summable (fun x => m x y))
    (B : ℝ) (hB : ∀ x, ∑' y, m x y ≤ B) (y : V) :
    (∑' x, m x y) ≤ c*B := by
  have ht := htr.real root weight Γ m hi hr hcol
  have hb : (∑ i, weight i * ∑' x, m x (root i)) ≤ B := by
    rw [← ht]
    calc
      _ ≤ ∑ i, weight i * B := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hB _) (hw i)
      _ = B := by rw [← Finset.sum_mul,hw1,one_mul]
  obtain ⟨i,a,ha,hay⟩ := hcov y
  have he : (∑' x, m x y) = ∑' x, m x (root i) := by
    rw [← hay,← a.tsum_eq (fun x => m x (a (root i)))]
    exact tsum_congr (fun x => hi a ha x (root i))
  have hn : 0 ≤ ∑' x, m x (root i) := tsum_nonneg (fun x => hm x _)
  have hs : weight i * ∑' x, m x (root i) ≤ ∑ j, weight j * ∑' x, m x (root j) :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hw j) (tsum_nonneg (fun x => hm x (root j))))
      (Finset.mem_univ i)
  rw [he]
  calc
    _ ≤ (c*weight i) * ∑' x, m x (root i) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hmin i) hn
    _ = c * (weight i * ∑' x, m x (root i)) := by ring
    _ ≤ c * (∑ j, weight j * ∑' x, m x (root j)) := mul_le_mul_of_nonneg_left hs hc
    _ ≤ c*B := mul_le_mul_of_nonneg_left hb hc



end TrajectoryTransport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NonnegativeTransport
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

theorem transportCut_mono (G : BondGraph V E) {n m : ℕ} (h : n ≤ m)
    {x y : V} (hxy : transportCut G n x y) : transportCut G m x y :=
  ⟨reachBall_mono G x h hxy.1, reachBall_mono G y h hxy.2⟩

theorem transportCut_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (ha : IsAut G a b) (n : ℕ) (x y : V) :
    transportCut G n (a x) (a y) ↔ transportCut G n x y := by
  simp only [transportCut,mem_reachBall_aut_iff G ha]

theorem exists_transportCut (G : BondGraph V E) (hconn : Connected G)
    (y : V) (Z : Finset V) : ∃ n, ∀ x ∈ Z, transportCut G n x y := by
  induction Z using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x Z _ ih =>
    obtain ⟨n,hn⟩ := ih
    obtain ⟨r,hr⟩ := exists_mem_reachBall (hconn x y)
    obtain ⟨s,hs⟩ := exists_mem_reachBall (hconn y x)
    refine ⟨max n (max r s), ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact ⟨reachBall_mono G z (le_trans (le_max_left r s) (le_max_right n _)) hr,
        reachBall_mono G y (le_trans (le_max_right r s) (le_max_right n _)) hs⟩
    · exact transportCut_mono G (le_max_left n _) (hn z hz)

 

theorem transported_column_of_row_bound (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (m : V → V → ℝ) (hm : ∀ x y, 0 ≤ m x y)
    (hi : ∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y)
    (hr : ∀ x, Summable (m x)) (B : ℝ) (hB : ∀ x, ∑' y, m x y ≤ B) :
    ∀ y, Summable (fun x => m x y) ∧ (∑' x, m x y) ≤ c*B := by
  let cut (n : ℕ) (x y : V) : ℝ := if transportCut G n x y then m x y else 0
  have hn (n : ℕ) (x y : V) : 0 ≤ cut n x y := by
    dsimp [cut]; split_ifs; exact hm x y; exact le_refl 0
  have hcRow (n : ℕ) (x : V) : Summable (cut n x) := by
    apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x n).toFinset)
    intro y hy
    simp only [Set.Finite.mem_toFinset] at hy
    exact ite_eq_right (fun h => hy h.1)
  have hcCol (n : ℕ) (y : V) : Summable (fun x => cut n x y) := by
    apply summable_of_ne_finset_zero (s := (finite_reachBall hloc y n).toFinset)
    intro x hx
    simp only [Set.Finite.mem_toFinset] at hx
    exact ite_eq_right (fun h => hx h.2)
  have hcInv (n : ℕ) : ∀ a ∈ Γ, ∀ x y, cut n (a x) (a y) = cut n x y := by
    intro a ha x y
    obtain ⟨b,hb⟩ := hΓ ha
    simp only [cut,transportCut_aut G hb,hi a ha]
  have hcBound (n : ℕ) (x : V) : (∑' y, cut n x y) ≤ B := by
    apply le_trans ((hcRow n x).tsum_le_tsum (fun y => ?_) (hr x)) (hB x)
    dsimp [cut]; split_ifs; exact le_refl _; exact hm x y
  have hbound (y : V) (Z : Finset V) : (∑ x ∈ Z, m x y) ≤ c*B := by
    obtain ⟨n,hnZ⟩ := exists_transportCut G hconn y Z
    calc
      _ = ∑ x ∈ Z, cut n x y := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (ite_eq_left (hnZ x hx)).symm
      _ ≤ ∑' x, cut n x y := (hcCol n y).sum_le_tsum Z (fun x _ => hn n x y)
      _ ≤ c*B := transported_column_le root weight Γ htr hcov hw hw1 c hc hmin
        (cut n) (hn n) (hcInv n) (hcRow n) (hcCol n) B (hcBound n) y
  intro y
  exact ⟨summable_of_sum_le (fun x => hm x y) (hbound y),
    Real.tsum_le_of_sum_le (fun x => hm x y) (hbound y)⟩



end NonnegativeTransport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteTrajectoryMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*} [Fintype W]

theorem finiteTrajectoryHit_le_sum (G : BondGraph V E) (e : W → V)
    (Q : Finset E) (p : unitInterval) (k : ℕ) (q : Set E → W → W → ℝ)
    (hq : ∀ ω a b, 0 ≤ q ω a b) (z : W) (A : Finset V) :
    finiteTrajectoryHit G e Q p k q z A ≤ ∑ a ∈ A, finiteTrajectoryMass G e Q p k q z a := by
  unfold finiteTrajectoryHit finiteTrajectoryMass
  rw [← finiteFamilyIntegral_sum]
  apply finiteFamilyIntegral_mono
  intro η
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro y _
  have hn := oldRunWeight_nonneg (fun i => q (η i)) (fun _ => hq _) k z y
  by_cases h : ((A:Set V) ∩ trajectoryUnion G η (e ∘ oldRunVertices k z y) k).Nonempty
  · rw [ite_eq_left h]
    obtain ⟨a,ha,hat⟩ := h
    have hs := Finset.single_le_sum (s := A)
      (f := fun a => if a ∈ trajectoryUnion G η (e ∘ oldRunVertices k z y) k then
        oldRunWeight (fun i => q (η i)) k z y else 0)
      (fun a _ => by split_ifs; exact hn; exact le_refl 0) ha
    simpa only [ite_eq_left hat] using hs
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg fun a _ => by split_ifs; exact hn; exact le_refl 0



end FiniteTrajectoryMass

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Transport_EndpointKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint Kernels for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SeparatedTracePair
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_trace_pair_separated_le [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (k n M : ℕ)
    (Q : Finset E) (p : unitInterval)
    (A₁ A₂ : Finset (SpliceState E)) (y₁ y₂ : (ℕ → Set E) → ℕ → V)
    (m₁ m₂ : (ℕ → Set E) → ℝ) (hm₁ : ∀ η, 0 ≤ m₁ η) (hm₂ : ∀ η, 0 ≤ m₂ η)
    (hA₁ : A₁ ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hA₂ : A₂ ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hbin : ∀ s ∈ A₁, (cluster G s.1 x).Finite ∧ n ≤ (cluster G s.1 x).ncard ∧
      (cluster G s.1 x).ncard < 2*n)
    (hcap₁ : ∀ s ∈ A₁, ∀ i, 1 ≤ i → i ≤ k → (cluster G (s.2 i) (y₁ s.2 i)).Finite)
    (hcap₂ : ∀ s ∈ A₂, ∀ i, 1 ≤ i → i ≤ k → (cluster G (s.2 i) (y₂ s.2 i)).Finite ∧
      (cluster G (s.2 i) (y₂ s.2 i)).ncard ≤ M) :
    (∑ a : FiniteTraceIndex G x k Q A₁ (fun s => y₁ s.2),
      ∑ b : FiniteTraceIndex G x k Q A₂ (fun s => y₂ s.2),
      if (traceIndexOutput G x k Q A₁ (fun s => y₁ s.2) a).1 =
          (traceIndexOutput G x k Q A₂ (fun s => y₂ s.2) b).1 ∧
        a.2.val ≠ [] ∧ b.2.val ≠ [] ∧
        GraphSeparated G
          (cluster G (traceIndexOutput G x k Q A₁ (fun s => y₁ s.2) a).1 x \ cluster G a.1.val.1 x)
          (cluster G (traceIndexOutput G x k Q A₁ (fun s => y₁ s.2) a).1 x \ cluster G b.1.val.1 x)
      then jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
        (pairSpliceOutput (traceIndexOutput G x k Q A₁ (fun s => y₁ s.2) a)
          (traceIndexOutput G x k Q A₂ (fun s => y₂ s.2) b)) *
        (m₁ a.1.val.2 * traceIndexMass G x k Q A₁ (fun s => y₁ s.2) a) *
        (m₂ b.1.val.2 * traceIndexMass G x k Q A₂ (fun s => y₂ s.2) b) else 0) ≤
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      (if (cluster G (finiteFieldSet Q ω) x).Finite ∧
        n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
        (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then
        finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => if
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₁ η) k).Nonempty then m₁ η else 0) *
        finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => if
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₂ η) k).Nonempty then m₂ η else 0) else 0) := by
  let T₁ := FiniteTraceIndex G x k Q A₁ (fun s => y₁ s.2)
  let T₂ := FiniteTraceIndex G x k Q A₂ (fun s => y₂ s.2)
  let out₁ := traceIndexOutput G x k Q A₁ (fun s => y₁ s.2)
  let out₂ := traceIndexOutput G x k Q A₂ (fun s => y₂ s.2)
  let P (a : T₁ × T₂) := (out₁ a.1).1 = (out₂ a.2).1 ∧ a.1.2.val ≠ [] ∧ a.2.2.val ≠ [] ∧
    GraphSeparated G (cluster G (out₁ a.1).1 x \ cluster G a.1.1.val.1 x)
      (cluster G (out₁ a.1).1 x \ cluster G a.2.1.val.1 x)
  let I := {a : T₁ × T₂ // P a}
  let η₁ (a : I) := a.val.1.1.val.2
  let η₂ (a : I) := a.val.2.1.val.2
  let ω₁ (a : I) := a.val.1.1.val.1
  let ω₂ (a : I) := a.val.2.1.val.1
  let ωf (a : I) := (out₁ a.val.1).1
  let c₁ (a : I) := a.val.1.2.val
  let c₂ (a : I) := a.val.2.2.val
  have hout (a : I) : jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a))
      (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a) = pairSpliceOutput (out₁ a.val.1) (out₂ a.val.2) := rfl
  have hinj : Function.Injective (fun a : I =>
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a),c₁ a,c₂ a)) := by
    intro a b he
    dsimp only at he
    rw [hout a,hout b] at he
    have ho₁ : out₁ a.val.1 = out₁ b.val.1 := Prod.ext
      (congrArg (fun z : JointSpliceState E × List (ℕ × E) × List (ℕ × E) => z.1.1) he)
      (congrArg (fun z : JointSpliceState E × List (ℕ × E) × List (ℕ × E) => z.1.2.1) he)
    have ho₂ : out₂ a.val.2 = out₂ b.val.2 := Prod.ext
      (a.property.1.symm.trans ((congrArg Prod.fst ho₁).trans b.property.1))
      (congrArg (fun z : JointSpliceState E × List (ℕ × E) × List (ℕ × E) => z.1.2.2) he)
    apply Subtype.ext
    exact Prod.ext
      (traceIndex_output_code_injective G x k Q A₁ (fun s => y₁ s.2)
        (Prod.ext ho₁ (congrArg (fun z => z.2.1) he)))
      (traceIndex_output_code_injective G x k Q A₂ (fun s => y₂ s.2)
        (Prod.ext ho₂ (congrArg (fun z => z.2.2) he)))
  have htr₁ (a : I) : SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (c₁ a) (ωf a) :=
    (traceIndex_valid G x k Q A₁ (fun s => y₁ s.2) a.val.1).1
  have htr₂ (a : I) : SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (c₂ a) (ωf a) := by
    change SpliceTrace G x _ _ _ _ _ _ (out₁ a.val.1).1
    rw [a.property.1]
    exact (traceIndex_valid G x k Q A₂ (fun s => y₂ s.2) a.val.2).1
  have hs₁ (a : I) := (mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) _).mp (hA₁ a.val.1.1.property)
  have hs₂ (a : I) := (mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) _).mp (hA₂ a.val.2.1.property)
  have hb := finite_separated_weighted_contact_second_moment_le G hloc x k n M p Q η₁ η₂ y₁ y₂
    (fun _ => True) (fun _ => True) m₁ m₂ hm₁ hm₂ ω₁ ω₂ ωf c₁ c₂ hinj htr₁ htr₂
    (fun a => a.property.2.1) (fun a => a.property.2.2.1) (fun a => a.property.2.2.2)
    (fun a => hbin _ a.val.1.1.property) (fun a => hcap₁ _ a.val.1.1.property)
    (fun a => hcap₂ _ a.val.2.1.property) (fun _ => trivial) (fun _ => trivial)
    (fun a => (hs₁ a).1) (fun a => (hs₂ a).1) (fun a => (hs₁ a).2.1)
    (fun a => (hs₂ a).2.1) (fun a => (hs₁ a).2.2) (fun a => (hs₂ a).2.2)
  simp only [true_and] at hb
  apply le_trans _ hb
  let w (a : T₁ × T₂) := jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
    (pairSpliceOutput (out₁ a.1) (out₂ a.2)) *
    (m₁ a.1.1.val.2 * traceIndexMass G x k Q A₁ (fun s => y₁ s.2) a.1) *
    (m₂ a.2.1.val.2 * traceIndexMass G x k Q A₂ (fun s => y₂ s.2) a.2)
  have he := Finset.sum_subtype (p := P) (F := inferInstance) (Finset.univ.filter P)
    (by intro a; simp) w
  rw [Finset.sum_filter,Fintype.sum_prod_type] at he
  change (∑ a : T₁, ∑ b : T₂, if P (a,b) then w (a,b) else 0) ≤ _
  rw [he]
  apply Finset.sum_le_sum
  intro a _
  rw [hout a]
  change w a.val ≤ _
  simp only [w,traceIndexMass,η₁,η₂,ωf,c₁,c₂,out₁,out₂]
  rw [← a.property.1]
  exact le_of_eq (by ring)

end SeparatedTracePair

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ChoiceSeparatedMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable {P₁ P₂ : Type*} [Fintype P₁] [Fintype P₂]



theorem finiteChoiceSeparatedPairMass_le [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (k n M : ℕ)
    (Q : Finset E) (p : unitInterval)
    (A₁ : P₁ → Finset (SpliceState E)) (A₂ : P₂ → Finset (SpliceState E))
    (y₁ : P₁ → (ℕ → Set E) → ℕ → V) (y₂ : P₂ → (ℕ → Set E) → ℕ → V)
    (m₁ : P₁ → (ℕ → Set E) → ℝ) (m₂ : P₂ → (ℕ → Set E) → ℝ)
    (hm₁ : ∀ r η, 0 ≤ m₁ r η) (hm₂ : ∀ r η, 0 ≤ m₂ r η)
    (hA₁ : ∀ r, A₁ r ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hA₂ : ∀ r, A₂ r ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hbin : ∀ r s, s ∈ A₁ r → (cluster G s.1 x).Finite ∧ n ≤ (cluster G s.1 x).ncard ∧
      (cluster G s.1 x).ncard < 2*n)
    (hcap₁ : ∀ r s, s ∈ A₁ r → ∀ i, 1 ≤ i → i ≤ k →
      (cluster G (s.2 i) (y₁ r s.2 i)).Finite)
    (hcap₂ : ∀ r s, s ∈ A₂ r → ∀ i, 1 ≤ i → i ≤ k →
      (cluster G (s.2 i) (y₂ r s.2 i)).Finite ∧ (cluster G (s.2 i) (y₂ r s.2 i)).ncard ≤ M) :
    finiteChoiceSeparatedPairMass G x k Q p A₁ A₂ y₁ y₂ m₁ m₂ ≤
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      (if (cluster G (finiteFieldSet Q ω) x).Finite ∧
        n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
        (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then
        finiteChoiceHit G k Q p y₁ m₁ (cluster G (finiteFieldSet Q ω) x) *
        finiteChoiceHit G k Q p y₂ m₂ (cluster G (finiteFieldSet Q ω) x) else 0) := by
  let R (ω : FiniteField Q) := (cluster G (finiteFieldSet Q ω) x).Finite ∧
    n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
    (cluster G (finiteFieldSet Q ω) x).ncard < 2*n
  let H₁ (r : P₁) (ω : FiniteField Q) := finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
    if (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₁ r η) k).Nonempty then m₁ r η else 0)
  let H₂ (r : P₂) (ω : FiniteField Q) := finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
    if (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₂ r η) k).Nonempty then m₂ r η else 0)
  have hb : finiteChoiceSeparatedPairMass G x k Q p A₁ A₂ y₁ y₂ m₁ m₂ ≤
      ∑ r : P₁, ∑ s : P₂, ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
        (if R ω then H₁ r ω * H₂ s ω else 0) := by
    unfold finiteChoiceSeparatedPairMass
    rw [Fintype.sum_sigma]
    apply Finset.sum_le_sum
    intro r _
    conv_lhs => arg 2; ext a; rw [Fintype.sum_sigma]
    conv_lhs => rw [Finset.sum_comm]
    simp only [choiceTraceOutput,choiceTraceInput,choiceTraceCode,choiceTraceMass,
      traceIndexInput,traceIndexCode]
    apply Finset.sum_le_sum
    intro s _
    exact finite_trace_pair_separated_le G hloc x k n M Q p (A₁ r) (A₂ s)
      (y₁ r) (y₂ s) (m₁ r) (m₂ s) (hm₁ r) (hm₂ s) (hA₁ r) (hA₂ s)
      (hbin r) (hcap₁ r) (hcap₂ s)
  apply hb.trans_eq
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext s; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  change (∑ s : P₂, ∑ r : P₁, finiteFieldWeight Q p ω * (if R ω then H₁ r ω * H₂ s ω else 0)) =
    finiteFieldWeight Q p ω * (if R ω then (∑ r : P₁, H₁ r ω) * (∑ s : P₂, H₂ s ω) else 0)
  by_cases h : R ω
  · simp only [ite_eq_left h,← Finset.mul_sum,← Finset.sum_mul]
  · simp only [ite_eq_right h,mul_zero,Finset.sum_const_zero]

end ChoiceSeparatedMass

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section LocalEndpointRule
attribute [local instance] Classical.propDecidable Classical.decEq



namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}



theorem mass_le_one (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x y : V) :
    q.mass ω x y ≤ 1 := by
  have h := (q.summable_mass ω x).sum_le_tsum ({y} : Finset V) (fun z _ => q.nonneg ω x z)
  simpa only [Finset.sum_singleton] using h.trans (q.row_le_one ω x)

 
theorem measurable_mass (q : LocalEndpointRule G hloc O M L) (x y : V) :
    Measurable (fun ω => q.mass ω x y) := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x q.radius).toFinset
  let f : Set (Q : Set E) → ℝ := fun η => q.mass (Subtype.val '' η) x y
  have hm : Measurable f := measurable_of_finite f
  have he : (fun ω => q.mass ω x y) = f ∘ (fun ω : Set E => Subtype.val ⁻¹' ω : Set E → Set (Q : Set E)) := by
    funext ω
    rw [q.locality ω x y]
    congr 1
    ext e
    simp [Q,and_comm]
  rw [he]
  exact hm.comp (measurable_set_restrict (Q : Set E))

theorem integrable_mass (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x y : V) :
    Integrable (fun ω => q.mass ω x y) (law p) := by
  apply Integrable.of_bound (q.measurable_mass x y).aestronglyMeasurable 1
  exact ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs,abs_of_nonneg (q.nonneg ω x y)] using q.mass_le_one ω x y



theorem kernel_nonneg (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x y : V) :
    0 ≤ q.kernel p x y := integral_nonneg (fun ω => q.nonneg ω x y)

theorem kernel_outside_ball_zero (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x y : V)
    (hy : y ∉ reachBall G x M) : q.kernel p x y = 0 := by
  simp only [kernel,q.outside_ball_zero _ x y hy,integral_zero]

theorem summable_kernel (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    Summable (q.kernel p x) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x M).toFinset)
  intro y hy
  apply q.kernel_outside_ball_zero p x y
  simpa only [Set.Finite.mem_toFinset] using hy

 

theorem kernel_row_integral (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    (∑' y, q.kernel p x y) = ∫ ω, (∑' y, q.mass ω x y) ∂law p := by
  let B := (finite_reachBall hloc x M).toFinset
  have h₁ : (∑' y, q.kernel p x y) = ∑ y ∈ B, q.kernel p x y :=
    tsum_eq_sum fun y hy => q.kernel_outside_ball_zero p x y (by simpa only [B,Set.Finite.mem_toFinset] using hy)
  have h₂ (ω : Set E) : (∑' y, q.mass ω x y) = ∑ y ∈ B, q.mass ω x y :=
    tsum_eq_sum fun y hy => q.outside_ball_zero ω x y (by simpa only [B,Set.Finite.mem_toFinset] using hy)
  rw [h₁]
  simp_rw [h₂]
  exact (integral_finsetSum B (fun y _ => q.integrable_mass p x y)).symm

end LocalEndpointRule
end LocalEndpointRule

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section LocalEndpointKernel
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

 

theorem outside_reverse_ball_zero (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x y : V)
    (hx : x ∉ reachBall G y M) : q.mass ω x y = 0 := by
  by_contra h
  obtain ⟨_,_,hc,hfin,hcap,_⟩ := q.support ω x y h
  have he := cluster_eq_of_conn G ω hc
  rw [he] at hfin hcap
  exact hx (finite_cluster_subset_reachBall G ω y hfin M hcap (conn_symm G ω hc))

theorem kernel_outside_reverse_ball_zero (q : LocalEndpointRule G hloc O M L)
    (p : unitInterval) (x y : V) (hx : x ∉ reachBall G y M) : q.kernel p x y = 0 := by
  simp only [kernel,q.outside_reverse_ball_zero _ x y hx,integral_zero]

theorem summable_kernel_column (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (y : V) :
    Summable (fun x => q.kernel p x y) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc y M).toFinset)
  intro x hx
  apply q.kernel_outside_reverse_ball_zero p x y
  simpa only [Set.Finite.mem_toFinset] using hx

theorem mass_zero_of_start_not_mem (q : LocalEndpointRule G hloc O M L) (ω : Set E)
    (x y : V) (hx : x ∉ O) : q.mass ω x y = 0 := by
  by_contra h
  exact hx (q.support ω x y h).1

theorem mass_zero_of_end_not_mem (q : LocalEndpointRule G hloc O M L) (ω : Set E)
    (x y : V) (hy : y ∉ O) : q.mass ω x y = 0 := by
  by_contra h
  exact hy (q.support ω x y h).2.1

theorem kernel_zero_of_start_not_mem (q : LocalEndpointRule G hloc O M L) (p : unitInterval)
    (x y : V) (hx : x ∉ O) : q.kernel p x y = 0 := by
  simp only [kernel,q.mass_zero_of_start_not_mem _ x y hx,integral_zero]

theorem kernel_zero_of_end_not_mem (q : LocalEndpointRule G hloc O M L) (p : unitInterval)
    (x y : V) (hy : y ∉ O) : q.kernel p x y = 0 := by
  simp only [kernel,q.mass_zero_of_end_not_mem _ x y hy,integral_zero]

 

theorem kernel_covariant (q : LocalEndpointRule G hloc O M L) (p : unitInterval)
    (a : V ≃ V) (b : E ≃ E) (ha : IsAut G a b) (x y : V) :
    q.kernel p (a x) (a y) = q.kernel p x y := by
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable
    (q.measurable_mass x y).aestronglyMeasurable
  rw [law_map_preimage_equiv p b] at h
  simpa only [kernel,q.covariance a b ha] using h.symm

theorem successProbability_nonneg (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    0 ≤ q.successProbability p x := tsum_nonneg (q.kernel_nonneg p x)

theorem successProbability_covariant (q : LocalEndpointRule G hloc O M L) (p : unitInterval)
    (a : V ≃ V) (b : E ≃ E) (ha : IsAut G a b) (x : V) :
    q.successProbability p (a x) = q.successProbability p x := by
  unfold successProbability
  rw [← a.tsum_eq (fun y => q.kernel p (a x) y)]
  exact tsum_congr (q.kernel_covariant p a b ha x)

theorem successProbability_orbit (q : LocalEndpointRule G hloc O M L) (p : unitInterval)
    (o x : V) (hx : x ∈ vertexOrbit G o) : q.successProbability p x = q.successProbability p o := by
  obtain ⟨a,b,ha,rfl⟩ := hx
  exact q.successProbability_covariant p a b ha o

theorem kernel_column_covariant (q : LocalEndpointRule G hloc O M L) (p : unitInterval)
    (a : V ≃ V) (b : E ≃ E) (ha : IsAut G a b) (y : V) :
    (∑' x, q.kernel p x (a y)) = ∑' x, q.kernel p x y := by
  rw [← a.tsum_eq (fun x => q.kernel p x (a y))]
  exact tsum_congr (fun x => q.kernel_covariant p a b ha x y)

end LocalEndpointRule
end LocalEndpointKernel

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EndpointTransport
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem kernel_column_orbit (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (y : V) (hy : y ∈ vertexOrbit G o) :
    (∑' x, q.kernel p x y) = ∑' x, q.kernel p x o := by
  obtain ⟨a,b,ha,rfl⟩ := hy
  exact q.kernel_column_covariant p a b ha o

 

theorem kernel_column_eq_success {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L)
    (p : unitInterval) (y : V) (hy : y ∈ vertexOrbit G (root i₀)) :
    (∑' x, q.kernel p x y) = q.successProbability p (root i₀) := by
  let O := vertexOrbit G (root i₀)
  let w : ι → ℝ := fun i => if root i ∈ O then weight i else 0
  have ho : root i₀ ∈ O := by
    refine ⟨Equiv.refl V,Equiv.refl E,?_,rfl⟩
    intro e
    simp
  have hw' (i : ι) : 0 ≤ w i := by
    dsimp [w]
    split_ifs
    · exact hw i
    · exact le_rfl
  have hpos : 0 < ∑ i, w i := by
    have hi : w i₀ ≤ ∑ i, w i := Finset.single_le_sum (fun i _ => hw' i) (Finset.mem_univ i₀)
    have he : w i₀ = weight i₀ := ite_eq_left ho
    rw [he] at hi
    exact hw₀.trans_le hi
  have ht := htr.real root weight Γ (q.kernel p)
    (by intro a ha x z; obtain ⟨b,hb⟩ := hΓ a ha; exact q.kernel_covariant p a b hb x z)
    (q.summable_kernel p) (q.summable_kernel_column p)
  have hr (i : ι) : weight i * (∑' z, q.kernel p (root i) z) =
      w i * q.successProbability p (root i₀) := by
    by_cases hi : root i ∈ O
    · have he := q.successProbability_orbit p (root i₀) (root i) hi
      change weight i * q.successProbability p (root i) = _
      rw [he]
      simp only [w,ite_eq_left hi]
    · simp only [w,ite_eq_right hi,zero_mul]
      have he : (∑' z, q.kernel p (root i) z) = 0 := by
        simp only [q.kernel_zero_of_start_not_mem p _ _ hi,tsum_zero]
      rw [he,mul_zero]
  have hc (i : ι) : weight i * (∑' x, q.kernel p x (root i)) =
      w i * (∑' x, q.kernel p x (root i₀)) := by
    by_cases hi : root i ∈ O
    · rw [q.kernel_column_orbit (root i₀) p (root i) hi]
      simp only [w,ite_eq_left hi]
    · simp only [w,ite_eq_right hi,zero_mul]
      have he : (∑' x, q.kernel p x (root i)) = 0 := by
        simp only [q.kernel_zero_of_end_not_mem p _ _ hi,tsum_zero]
      rw [he,mul_zero]
  simp_rw [hr,hc] at ht
  rw [← Finset.sum_mul,← Finset.sum_mul] at ht
  rw [q.kernel_column_orbit (root i₀) p y hy]
  exact (mul_left_cancel₀ (ne_of_gt hpos) ht).symm

 
theorem kernel_column_le_success {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L)
    (p : unitInterval) (y : V) :
    (∑' x, q.kernel p x y) ≤ q.successProbability p (root i₀) := by
  by_cases hy : y ∈ vertexOrbit G (root i₀)
  · exact (q.kernel_column_eq_success root weight Γ htr hΓ hw i₀ hw₀ p y hy).le
  · simpa only [q.kernel_zero_of_end_not_mem p _ _ hy,tsum_zero] using
      q.successProbability_nonneg p (root i₀)

end LocalEndpointRule
end EndpointTransport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EndpointSchur
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem kernel_row_le_success (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p : unitInterval) (x : V) :
    (∑' y, q.kernel p x y) ≤ q.successProbability p o := by
  by_cases hx : x ∈ vertexOrbit G o
  · exact (q.successProbability_orbit p o x hx).le
  · simpa only [q.kernel_zero_of_start_not_mem p _ _ hx,tsum_zero] using
      q.successProbability_nonneg p o


end LocalEndpointRule
end EndpointSchur

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory
section FiniteLocalIntegral
attribute [local instance] Classical.propDecidable Classical.decEq



theorem finiteFieldWeight_eq_atom (Q : Finset E) (p : unitInterval) (ω : FiniteField Q) :
    finiteFieldWeight Q p ω = (law p : Measure (Set (Q : Set E))).real {finiteFieldEquiv Q ω} := by
  have hn : (finiteFieldEquiv Q ω).ncard = ω.val.card := by
    rw [finiteFieldEquiv_apply,Set.ncard_preimage_of_injective_subset_range Subtype.val_injective]
    · exact Set.ncard_coe_finset _
    · intro e he
      exact ⟨⟨e,Finset.mem_powerset.mp ω.property he⟩,rfl⟩
  rw [law,setBernoulli_real_singleton p (Set.subset_univ _) Set.finite_univ,
    Set.ncard_sdiff' (Set.subset_univ _) Set.finite_univ,hn]
  have hc : Fintype.card (Q : Set E) = Q.card := Fintype.card_coe Q
  simp only [finiteFieldWeight,bernoulliWeight,Set.ncard_univ,Nat.card_eq_fintype_card,hc]

 

theorem integral_finite_local (Q : Finset E) (p : unitInterval) (f : Set E → ℝ)
    (hf : ∀ ω, f ω = f (ω ∩ (Q : Set E))) :
    (∫ ω, f ω ∂law p) = ∑ η : FiniteField Q, finiteFieldWeight Q p η * f (finiteFieldSet Q η) := by
  let g : Set (Q : Set E) → ℝ := fun η => f (Subtype.val '' η)
  have hmap := integral_map (μ := law p) (measurable_set_restrict (Q : Set E)).aemeasurable
    (measurable_of_finite g).aestronglyMeasurable
  rw [law_map_restrict p (Q : Set E)] at hmap
  have he (ω : Set E) : g (Subtype.val ⁻¹' ω) = f ω := by
    rw [hf ω]
    dsimp [g]
    congr 1
    ext e
    simp [and_comm]
  simp_rw [he] at hmap
  rw [← hmap,integral_fintype Integrable.of_finite]
  rw [← (finiteFieldEquiv Q).sum_comp]
  apply Finset.sum_congr rfl
  intro η _
  rw [← finiteFieldWeight_eq_atom]
  simp only [g,finiteFieldEquiv_image,smul_eq_mul]

end FiniteLocalIntegral

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CappedGoodLocality
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_finite_local (Q : Finset E) (f : Set E → ℝ)
    (hf : ∀ ω, f ω = f (ω ∩ (Q : Set E))) : Measurable f := by
  let g : Set (Q : Set E) → ℝ := fun η => f (Subtype.val '' η)
  have he : f = g ∘ (fun ω : Set E => (Subtype.val ⁻¹' ω : Set (Q : Set E))) := by
    funext ω
    rw [hf ω]
    congr 1
    ext e
    simp [and_comm]
  rw [he]
  exact (measurable_of_finite g).comp (measurable_set_restrict (Q : Set E))

theorem integrable_finite_local (Q : Finset E) (p : unitInterval) (f : Set E → ℝ)
    (hf : ∀ ω, f ω = f (ω ∩ (Q : Set E))) : Integrable f (law p) := by
  let g : Set (Q : Set E) → ℝ := fun η => f (Subtype.val '' η)
  have he : f = g ∘ (fun ω : Set E => (Subtype.val ⁻¹' ω : Set (Q : Set E))) := by
    funext ω
    rw [hf ω]
    congr 1
    ext e
    simp [and_comm]
  have hi : Integrable g (Measure.map (fun ω : Set E => (Subtype.val ⁻¹' ω : Set (Q : Set E))) (law p)) := by
    rw [law_map_restrict]
    exact Integrable.of_finite
  rw [he]
  exact hi.comp_measurable (measurable_set_restrict (Q : Set E))

end CappedGoodLocality

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CappedLocalLoad
attribute [local instance] Classical.propDecidable Classical.decEq

namespace CappedLocalLoad
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ}

theorem row_nonneg (q : CappedLocalLoad G hloc O M) (ω : Set E) (x : V) : 0 ≤ q.row ω x :=
  tsum_nonneg (q.nonneg ω x)

theorem integrable_mass (q : CappedLocalLoad G hloc O M) (p : unitInterval) (x y : V) :
    Integrable (fun ω => q.mass ω x y) (law p) :=
  integrable_finite_local _ p _ (q.locality · x y)

theorem integrable_row (q : CappedLocalLoad G hloc O M) (p : unitInterval) (x : V) :
    Integrable (fun ω => q.row ω x) (law p) :=
  integrable_finite_local _ p _ (q.row_locality · x)

theorem integrable_sq_row (q : CappedLocalLoad G hloc O M) (p : unitInterval) (x : V) :
    Integrable (fun ω => q.row ω x ^ 2) (law p) :=
  integrable_finite_local _ p _ (fun ω => congrArg (· ^ 2) (q.row_locality ω x))



end CappedLocalLoad
end CappedLocalLoad

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section TruncationLoss
attribute [local instance] Classical.propDecidable Classical.decEq
namespace CappedLocalLoad
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ}

theorem cap_of_row_ne_zero (q : CappedLocalLoad G hloc O M) (ω : Set E) (x : V)
    (hr : q.row ω x ≠ 0) : (cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M := by
  obtain ⟨y,hy⟩ : ∃ y, q.mass ω x y ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hr (by simp only [row,hn,tsum_zero])
  exact (q.support ω x y hy).2.2.2

theorem truncate_scaled_row (q : CappedLocalLoad G hloc O M) (b : ℝ) (hb : 0 < b)
    (L : ℝ) (ω : Set E) (x : V) :
    b * (∑' y, (q.truncate b hb L).mass ω x y) =
      if q.row ω x ≤ b ∧ CappedGoodness G ω x M L then q.row ω x else 0 := by
  by_cases h : q.row ω x ≤ b ∧ CappedGoodness G ω x M L
  · simp only [truncate,ite_eq_left h,tsum_mul_left,← mul_assoc,mul_inv_cancel₀ hb.ne',one_mul]
    rfl
  · simp only [truncate,ite_eq_right h,tsum_zero,mul_zero]

theorem truncate_mass_le (q : CappedLocalLoad G hloc O M) (b : ℝ) (hb : 0 < b)
    (L : ℝ) (ω : Set E) (x y : V) :
    (q.truncate b hb L).mass ω x y ≤ b⁻¹ * q.mass ω x y := by
  change (if _ then _ else _) ≤ _
  split_ifs
  · rfl
  · exact mul_nonneg (inv_nonneg.mpr hb.le) (q.nonneg ω x y)

 

theorem truncate_pointwise_loss (q : CappedLocalLoad G hloc O M) (b : ℝ) (hb : 0 < b)
    (L : ℝ) (ω : Set E) (x : V) :
    q.row ω x ≤ b * (∑' y, (q.truncate b hb L).mass ω x y) + q.row ω x ^ 2 / b +
      b * ({η | CappedBadGoodness G η x M L}.indicator (1 : Set E → ℝ) ω) := by
  rw [q.truncate_scaled_row b hb L]
  have hs : 0 ≤ q.row ω x ^ 2 / b := div_nonneg (sq_nonneg _) hb.le
  have hi : 0 ≤ ({η | CappedBadGoodness G η x M L}.indicator (1 : Set E → ℝ) ω) := by
    apply Set.indicator_nonneg
    intro η _
    norm_num
  by_cases hr : q.row ω x ≤ b
  · by_cases hg : CappedGoodness G ω x M L
    · simp only [hr,hg,and_self,ite_true]
      nlinarith
    · simp only [hg,and_false,ite_false,zero_add]
      by_cases hz : q.row ω x = 0
      · rw [hz]
        positivity
      · have hc := q.cap_of_row_ne_zero ω x hz
        have hbad : CappedBadGoodness G ω x M L := ⟨hc.1,hc.2,fun h => hg ⟨hc.1,hc.2,h⟩⟩
        rw [Set.indicator_of_mem (show ω ∈ {η | CappedBadGoodness G η x M L} from hbad)]
        change q.row ω x ≤ q.row ω x ^ 2 / b + b * 1
        linarith
  · simp only [hr,false_and,ite_false,zero_add]
    have htail : q.row ω x ≤ q.row ω x ^ 2 / b := by
      apply (le_div_iff₀ hb).mpr
      have ht := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hr)) (q.row_nonneg ω x)
      nlinarith
    exact htail.trans (le_add_of_nonneg_right (mul_nonneg hb.le hi))

 

theorem truncate_mean_loss (q : CappedLocalLoad G hloc O M) (p : unitInterval)
    (b : ℝ) (hb : 0 < b) (L : ℝ) (x : V) :
    (∫ ω, q.row ω x ∂law p) ≤ b * (q.truncate b hb L).successProbability p x +
      (∫ ω, q.row ω x ^ 2 ∂law p) / b + b * (law p).real {ω | CappedBadGoodness G ω x M L} := by
  let t := q.truncate b hb L
  have ht : Integrable (fun ω => ∑' y, t.mass ω x y) (law p) := by
    apply integrable_finite_local
      (incidentSupport G hloc (finite_reachBall hloc x t.radius).toFinset) p
    intro ω
    exact tsum_congr (t.locality ω x)
  have hbad := measurableSet_cappedBadGoodness G hloc x M L
  have hi : Integrable ({ω | CappedBadGoodness G ω x M L}.indicator (1 : Set E → ℝ)) (law p) :=
    (integrable_const (1:ℝ)).indicator hbad
  have h := integral_mono (q.integrable_row p x)
    (((ht.const_mul b).add ((q.integrable_sq_row p x).div_const b)).add (hi.const_mul b))
    (q.truncate_pointwise_loss b hb L · x)
  dsimp only [Pi.add_apply] at h
  have he₁ := integral_add ((ht.const_mul b).add ((q.integrable_sq_row p x).div_const b)) (hi.const_mul b)
  have he₂ := integral_add (ht.const_mul b) ((q.integrable_sq_row p x).div_const b)
  dsimp only [Pi.add_apply] at he₁ he₂
  rw [he₁,he₂,integral_const_mul,integral_div,integral_const_mul,
    integral_indicator_one hbad] at h
  rw [← t.kernel_row_integral p x] at h
  exact h

theorem truncate_success_lower (q : CappedLocalLoad G hloc O M) (p : unitInterval)
    (b : ℝ) (hb : 0 < b) (L : ℝ) (x : V) (a : ℝ)
    (hmean : a ≤ ∫ ω, q.row ω x ∂law p)
    (hmoment : (∫ ω, q.row ω x ^ 2 ∂law p) / b ≤ a/4)
    (hbad : b * (law p).real {ω | CappedBadGoodness G ω x M L} ≤ a/4) :
    a / (2*b) ≤ (q.truncate b hb L).successProbability p x := by
  have hh := q.truncate_mean_loss p b hb L x
  apply (div_le_iff₀ (mul_pos (by norm_num) hb)).mpr
  nlinarith

end CappedLocalLoad
end TruncationLoss

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Amplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Amplification for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AmplificationMarginal
attribute [local instance] Classical.propDecidable Classical.decEq

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}



theorem amplificationMarginal_mean [Nonempty E] (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval) :
    (∫ ω, q.amplificationMarginal Q B x k n z p ω ∂law p) =
      ∑ r, ∑ s ∈ q.amplificationInputs Q B x k n z r,
        spliceTupleWeight Q (Finset.Icc 1 k) p s * q.amplificationWeight B k z s r := by
  rw [integral_finite_local Q p _ (q.amplificationMarginal_local Q B x k n z p)]
  simp only [amplificationMarginal,restrictFiniteField_fieldSet]
  rw [finiteRootLoad_mean]
  apply finiteChoiceForwardLoad_mean G hloc x k M Q p
  · exact q.amplificationInputs_subset Q B x k n z
  · intro r s hs
    exact ((q.mem_amplificationInputs Q B x k n z r s).mp hs).2.2.2.2.2.1
  · intro r s hs i hi
    exact (q.amplificationInputs_chain Q B x k n z r s hs i
      (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2).1
  · intro r s hs i hi
    have hc := q.amplificationInputs_chain Q B x k n z r s hs i
      (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
    exact ⟨hc.2.1,hc.2.2.1⟩

end LocalEndpointRule
end AmplificationMarginal

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AmplificationMeanKernel
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem finiteSpliceDomain_integral_factor (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (f : Set E → ℝ) (g : (ℕ → Set E) → ℝ) :
    (∑ s ∈ finiteSpliceDomain Q J, spliceTupleWeight Q J p s * f s.1 * g s.2) =
      finiteFieldIntegral Q p f * finiteFamilyIntegral Q J p g := by
  have hh := finiteRootLoad_mean Q J p (fun s => f s.1 * g s.2)
  simp only [← mul_assoc] at hh
  rw [← hh]
  simp only [finiteRootLoad,finiteFieldIntegral,finiteFamilyIntegral,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η _
  ring


namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

theorem finiteOldKernel_eq_kernel (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (p : unitInterval) (a b : V)
    (hQ : incidentSupport G hloc (finite_reachBall hloc a q.radius).toFinset ⊆ Q) :
    finiteOldKernel Q p q.mass a b = q.kernel p a b := by
  symm
  exact integral_finite_local Q p _ (finite_local_of_subset _ Q hQ _ (q.locality · a b))

 

theorem amplificationMarginal_mean_kernel [Nonempty E] (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval)
    (hx : x ∈ O) (hz : z.val ∈ O)
    (hQ : ∀ a ∈ B, incidentSupport G hloc (finite_reachBall hloc a q.radius).toFinset ⊆ Q) :
    (∫ ω, q.amplificationMarginal Q B x k n z p ω ∂law p) =
      ∑ r : Fin k → ↥B, finiteBinConnection G Q p x n (amplificationVertices B k z r 0) *
        oldRunWeight (fun _ (a b : ↥B) => q.kernel p a.val b.val) k z r := by
  rw [q.amplificationMarginal_mean Q B x k n z p]
  apply Finset.sum_congr rfl
  intro r _
  let f : Set E → ℝ := fun ω => if n ≤ (cluster G ω x).ncard ∧
      (cluster G ω x).ncard < 2*n ∧ amplificationVertices B k z r 0 ∈ cluster G ω x then 1 else 0
  let g : (ℕ → Set E) → ℝ := fun η =>
    oldRunWeight (fun i (a b : ↥B) => q.mass (η i) a.val b.val) k z r
  have he : (∑ s ∈ q.amplificationInputs Q B x k n z r,
      spliceTupleWeight Q (Finset.Icc 1 k) p s * q.amplificationWeight B k z s r) =
      ∑ s ∈ finiteSpliceDomain Q (Finset.Icc 1 k), spliceTupleWeight Q (Finset.Icc 1 k) p s * f s.1 * g s.2 := by
    rw [amplificationInputs,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s _
    change (if _ then _ else _) = _
    by_cases hw : q.amplificationWeight B k z s r = 0
    · have hg : g s.2 = 0 := hw
      simp [hx,hz,hw,hg]
    · simp only [hx,hz,true_and,hw,ne_eq,not_false_eq_true,and_true]
      by_cases hbin : n ≤ (cluster G s.1 x).ncard ∧ (cluster G s.1 x).ncard < 2*n ∧
          amplificationVertices B k z r 0 ∈ cluster G s.1 x
      · simp [f,hbin,g,amplificationWeight]
      · simp only [hbin,ite_false,f,mul_zero,zero_mul]
  rw [he,finiteSpliceDomain_integral_factor]
  dsimp only [g]
  rw [oldRunWeight_integral Q p k (fun ω (a b : ↥B) => q.mass ω a.val b.val) z r]
  change finiteBinConnection G Q p x n _ * _ = _
  congr 1
  apply congrArg (fun K : ℕ → ↥B → ↥B → ℝ => oldRunWeight K k z r)
  funext i a b
  exact q.finiteOldKernel_eq_kernel Q p a.val b.val (hQ a.val a.property)

end LocalEndpointRule
end AmplificationMeanKernel

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section BinConnection
attribute [local instance] Classical.propDecidable Classical.decEq



theorem binConnectionMass_nonneg (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V) :
    0 ≤ binConnectionMass G n ω x y := by unfold binConnectionMass; split_ifs <;> norm_num

theorem binConnectionMass_symm (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V) :
    binConnectionMass G n ω x y = binConnectionMass G n ω y x := by
  by_cases hc : Conn G ω x y
  · have he := cluster_eq_of_conn G ω hc
    simp only [binConnectionMass,hc,conn_symm G ω hc,and_true,he]
  · have hc' : ¬Conn G ω y x := fun h => hc (conn_symm G ω h)
    simp only [binConnectionMass,hc,hc',and_false,ite_false]

theorem binConnectionMass_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (n : ℕ) (ω : Set E) (x y : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset
    binConnectionMass G n ω x y = binConnectionMass G n (ω ∩ (Q : Set E)) x y := by
  dsimp only
  let Q := incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset
  have hp : ((cluster G ω x).Finite ∧ n ≤ (cluster G ω x).ncard ∧
      (cluster G ω x).ncard < 2*n ∧ Conn G ω x y) ↔
      ((cluster G (ω ∩ (Q : Set E)) x).Finite ∧ n ≤ (cluster G (ω ∩ (Q : Set E)) x).ncard ∧
      (cluster G (ω ∩ (Q : Set E)) x).ncard < 2*n ∧ Conn G (ω ∩ (Q : Set E)) x y) := by
    constructor
    · rintro ⟨hf,hn,hN,hc⟩
      have hs : cluster G ω x ⊆ (finite_reachBall hloc x (2*n)).toFinset := by
        simpa only [Set.Finite.coe_toFinset] using finite_cluster_subset_reachBall G ω x hf (2*n) hN.le
      have he := cluster_restrict_incident_of_full G hloc _ ω x hs
      change cluster G (ω ∩ (Q : Set E)) x = cluster G ω x at he
      refine ⟨he.symm ▸ hf,he.symm ▸ hn,he.symm ▸ hN,?_⟩
      change y ∈ cluster G (ω ∩ (Q : Set E)) x
      rw [he]
      exact hc
    · rintro ⟨hf,hn,hN,hc⟩
      have he := cluster_restrict_of_cap G hloc Q ω x (2*n) (Finset.Subset.refl _) hf hN.le
      exact ⟨he ▸ hf,he ▸ hn,he ▸ hN,conn_mono G Set.inter_subset_left hc⟩
  exact if_congr hp rfl rfl

theorem binConnectionMass_support (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V)
    (h : binConnectionMass G n ω x y ≠ 0) :
    (cluster G ω x).Finite ∧ (cluster G ω x).ncard < 2*n ∧ Conn G ω x y := by
  unfold binConnectionMass at h
  split_ifs at h with hp
  · exact ⟨hp.1,hp.2.2.1,hp.2.2.2⟩
  · exact (h rfl).elim

theorem binConnectionMass_outside (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V)
    (hy : y ∉ reachBall G x (2*n)) : binConnectionMass G n ω x y = 0 := by
  by_contra h
  obtain ⟨hf,hN,hc⟩ := binConnectionMass_support G n ω x y h
  exact hy (finite_cluster_subset_reachBall G ω x hf (2*n) hN.le hc)

theorem binConnection_nonneg (G : BondGraph V E) (p : unitInterval) (n : ℕ) (x y : V) :
    0 ≤ binConnection G p n x y := integral_nonneg fun ω => binConnectionMass_nonneg G n ω x y

theorem binConnection_symm (G : BondGraph V E) (p : unitInterval) (n : ℕ) (x y : V) :
    binConnection G p n x y = binConnection G p n y x :=
  integral_congr_ae (ae_of_all _ fun ω => binConnectionMass_symm G n ω x y)

theorem binConnection_outside (G : BondGraph V E) (p : unitInterval) (n : ℕ) (x y : V)
    (hy : y ∉ reachBall G x (2*n)) : binConnection G p n x y = 0 := by
  simp only [binConnection,fun ω => binConnectionMass_outside G n ω x y hy,integral_zero]

end BinConnection

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteBinConnection
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finiteBinConnection_eq_binConnection (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (p : unitInterval) (x : V) (n : ℕ) (y : V)
    (hQ : incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset ⊆ Q) :
    finiteBinConnection G Q p x n y = binConnection G p n x y := by
  rw [binConnection, integral_finite_local Q p _
    (finite_local_of_subset _ Q hQ _ (fun ω => binConnectionMass_local G hloc n ω x y))]
  unfold finiteBinConnection finiteFieldIntegral
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  have hf : (cluster G (finiteFieldSet Q ω) x).Finite :=
    cluster_finite_of_finite_edges G ω.val.finite_toSet x
  unfold cluster at hf
  simp only [binConnectionMass,cluster,Set.mem_ofPred_eq,hf,true_and]
  exact if_congr Iff.rfl rfl rfl

end FiniteBinConnection

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PositivePathOperator
attribute [local instance] Classical.propDecidable Classical.decEq


namespace PositiveRealMatrix
variable {A H : Hilbert V →L[ℂ] Hilbert V}

theorem real (hA : PositiveRealMatrix A) (x y : V) :
    matrixCoeff A x y = ((matrixCoeff A x y).re : ℂ) := by
  apply Complex.ext
  · rfl
  · exact (hA x y).1

theorem mul_hasSum (hA : PositiveRealMatrix A) (H : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    HasSum (fun z => (matrixCoeff A x z).re * (matrixCoeff H z y).re)
      (matrixCoeff (A*H) x y).re := by
  have h := Complex.reCLM.hasSum (operator_kernel_hasSum A (H (lp.single 2 y (1:ℂ))) x)
  change HasSum (fun z => (matrixCoeff A x z * matrixCoeff H z y).re)
    (matrixCoeff (A*H) x y).re at h
  simpa only [Complex.mul_re,(hA _ _).1,zero_mul,sub_zero] using h

theorem mul (hA : PositiveRealMatrix A) (hH : PositiveRealMatrix H) :
    PositiveRealMatrix (A*H) := by
  intro x y
  constructor
  · have hs := (operator_kernel_hasSum A (H (lp.single 2 y (1:ℂ))) x).summable
    change Summable (fun z => matrixCoeff A x z * matrixCoeff H z y) at hs
    rw [matrixCoeff_mul,Complex.im_tsum hs]
    simp only [Complex.mul_im,(hA _ _).1,(hH _ _).1,mul_zero,zero_mul,add_zero,tsum_zero]
  · rw [← (hA.mul_hasSum H x y).tsum_eq]
    exact tsum_nonneg fun z => mul_nonneg (hA x z).2 (hH z y).2

theorem one : PositiveRealMatrix (1 : Hilbert V →L[ℂ] Hilbert V) := by
  intro x y
  simp only [matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply]
  split_ifs <;> norm_num

theorem pow (hA : PositiveRealMatrix A) (k : ℕ) : PositiveRealMatrix (A^k) := by
  induction k with
  | zero => simpa only [pow_zero] using (one (V := V))
  | succ k ih => rw [pow_succ]; exact ih.mul hA

theorem star (hA : PositiveRealMatrix A) : PositiveRealMatrix (star A) := by
  intro x y
  simpa only [matrixCoeff_adjoint,Complex.star_def,Complex.conj_im,Complex.conj_re,neg_eq_zero] using hA y x

end PositiveRealMatrix

 

theorem oldRun_test_succ {W : Type*} [Fintype W]
    (K : ℕ → W → W → ℝ) (F : W → ℝ) (k : ℕ) (z : W) :
    (∑ r : Fin (k+1) → W, oldRunWeight K (k+1) z r * F (oldRunVertices (k+1) z r 0)) =
      ∑ a : W, K (k+1) z a *
        ∑ r : Fin k → W, oldRunWeight K k a r * F (oldRunVertices k a r 0) := by
  rw [Fintype.sum_equiv (oldRunConsEquiv k) _
    (fun r => K (k+1) z r.1 * oldRunWeight K k r.1 r.2 * F (oldRunVertices k r.1 r.2 0))
      (by intro r; simp only [oldRunWeight,oldRunConsEquiv,Equiv.coe_fn_mk,
        oldRunVertices_succ_of_le k z r 0 (Nat.zero_le k)]), Fintype.sum_prod_type]
  simp only [Finset.mul_sum,mul_assoc]

 

theorem finite_oldRun_operator_domination (A H : Hilbert V →L[ℂ] Hilbert V)
    (hA : PositiveRealMatrix A) (hH : PositiveRealMatrix H)
    (B : Finset V) (k : ℕ) (z : ↥B) (x : V) :
    (∑ r : Fin k → ↥B,
      oldRunWeight (fun _ (a b : ↥B) => (matrixCoeff A a.val b.val).re) k z r *
        (matrixCoeff H (oldRunVertices k z r 0).val x).re) ≤
      (matrixCoeff (A^k*H) z.val x).re := by
  induction k generalizing z with
  | zero => simp [oldRunWeight,oldRunVertices]
  | succ k ih =>
    rw [oldRun_test_succ (fun _ (a b : ↥B) => (matrixCoeff A a.val b.val).re)
      (fun a : ↥B => (matrixCoeff H a.val x).re) k z]
    calc
      _ ≤ ∑ a : ↥B, (matrixCoeff A z.val a.val).re * (matrixCoeff (A^k*H) a.val x).re :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (ih a) (hA z.val a.val).2
      _ ≤ ∑' a, (matrixCoeff A z.val a).re * (matrixCoeff (A^k*H) a x).re := by
        rw [Finset.sum_coe_sort B (fun a => (matrixCoeff A z.val a).re * (matrixCoeff (A^k*H) a x).re)]
        exact (hA.mul_hasSum (A^k*H) z.val x).summable.sum_le_tsum B
          (fun a _ => mul_nonneg (hA z.val a).2 (((hA.pow k).mul hH) a x).2)
      _ = (matrixCoeff (A^(k+1)*H) z.val x).re := by
        rw [(hA.mul_hasSum (A^k*H) z.val x).tsum_eq,pow_succ',mul_assoc]

end PositivePathOperator

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section OrbitBinOperator
attribute [local instance] Classical.propDecidable Classical.decEq

theorem binConnectionMass_covariant (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (n : ℕ) (ω : Set E) (x y : V) :
    binConnectionMass G n (b ⁻¹' ω) x y = binConnectionMass G n ω (a x) (a y) := by
  have hf : (cluster G (b ⁻¹' ω) x).Finite ↔ (cluster G ω (a x)).Finite := by
    rw [← cluster_aut G hab ω x]
    exact (Set.finite_image_iff a.injective.injOn).symm
  have hn : (cluster G (b ⁻¹' ω) x).ncard = (cluster G ω (a x)).ncard := by
    rw [← cluster_aut G hab ω x,Set.ncard_image_of_injective _ a.injective]
  simp only [binConnectionMass,hf,hn,conn_aut_iff G hab]

theorem binConnection_covariant (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (n : ℕ) (x y : V) :
    binConnection G p n (a x) (a y) = binConnection G p n x y := by
  have hm : Measurable (fun ω => binConnectionMass G n ω x y) :=
    measurable_finite_local _ _ (fun ω => binConnectionMass_local G hloc n ω x y)
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable hm.aestronglyMeasurable
  rw [law_map_preimage_equiv p b] at h
  simpa only [binConnection,binConnectionMass_covariant G hab] using h.symm


theorem orbitBinConnection_nonneg (G : BondGraph V E) (p : unitInterval) (o : V)
    (n : ℕ) (x y : V) : 0 ≤ orbitBinConnection G p o n x y := by
  unfold orbitBinConnection
  split_ifs
  · exact binConnection_nonneg G p n x y
  · exact le_rfl

theorem orbitBinConnection_symm (G : BondGraph V E) (p : unitInterval) (o : V)
    (n : ℕ) (x y : V) : orbitBinConnection G p o n x y = orbitBinConnection G p o n y x := by
  simp only [orbitBinConnection,and_comm,binConnection_symm G p n]

theorem orbitBinConnection_covariant (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (n : ℕ) (x y : V) :
    orbitBinConnection G p o n (a x) (a y) = orbitBinConnection G p o n x y := by
  simp only [orbitBinConnection,mem_vertexOrbit_aut_iff G o hab,binConnection_covariant G hloc p hab n]

theorem orbitBinConnection_summable (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (n : ℕ) (x : V) : Summable (orbitBinConnection G p o n x) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x (2*n)).toFinset)
  intro y hy
  have hz := binConnection_outside G p n x y (by simpa only [Set.Finite.mem_toFinset] using hy)
  simp only [orbitBinConnection,hz,ite_self]

theorem orbitBinConnection_row (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (n : ℕ) (x : V) (hx : x ∈ vertexOrbit G o) :
    (∑' y, orbitBinConnection G p o n x y) = binOrbitRow G p o n := by
  obtain ⟨a,b,hab,rfl⟩ := hx
  rw [← a.tsum_eq (fun y => orbitBinConnection G p o n (a o) y)]
  exact tsum_congr (fun y => orbitBinConnection_covariant G hloc p o hab n o y)

theorem orbitBinConnection_row_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (n : ℕ) (x : V) :
    (∑' y, orbitBinConnection G p o n x y) ≤ binOrbitRow G p o n := by
  by_cases hx : x ∈ vertexOrbit G o
  · exact (orbitBinConnection_row G hloc p o n x hx).le
  · simp only [orbitBinConnection,hx,false_and,ite_false,tsum_zero]
    exact tsum_nonneg (orbitBinConnection_nonneg G p o n o)

 

theorem exists_orbitBinConnection_operator (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (n : ℕ) :
    ∃ H : Hilbert V →L[ℂ] Hilbert V, ‖H‖ ≤ binOrbitRow G p o n ∧
      ∀ x y, matrixCoeff H x y = (orbitBinConnection G p o n x y : ℂ) := by
  have hr (x : V) (S : Finset V) : (∑ y ∈ S, orbitBinConnection G p o n x y) ≤ binOrbitRow G p o n :=
    ((orbitBinConnection_summable G hloc p o n x).sum_le_tsum S
      (fun y _ => orbitBinConnection_nonneg G p o n x y)).trans (orbitBinConnection_row_le G hloc p o n x)
  exact exists_operator_of_row_column_bound (orbitBinConnection G p o n) (binOrbitRow G p o n)
    (tsum_nonneg (orbitBinConnection_nonneg G p o n o)) (orbitBinConnection_nonneg G p o n) hr
    (fun y S => by simpa only [orbitBinConnection_symm G p o n] using hr y S)

end OrbitBinOperator

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open MeasureTheory
section AmplificationOperatorDomination
attribute [local instance] Classical.propDecidable Classical.decEq

theorem oldRun_endpoint_mem {W : Type*} (P : W → Prop) (K : ℕ → W → W → ℝ)
    (hK : ∀ i a b, K i a b ≠ 0 → P b) (k : ℕ) (z : W) (hz : P z)
    (r : Fin k → W) (hr : oldRunWeight K k z r ≠ 0) : P (oldRunVertices k z r 0) := by
  induction k generalizing z with
  | zero => exact hz
  | succ k ih =>
    have hm := mul_ne_zero_iff.mp hr
    rw [oldRunVertices_succ_of_le _ _ _ _ (Nat.zero_le k)]
    exact ih (r 0) (hK _ _ _ hm.1) (Fin.tail r) hm.2

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem amplificationMarginal_operator_le [Nonempty E] (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval)
    (hx : x ∈ vertexOrbit G o) (hz : z.val ∈ vertexOrbit G o)
    (hroot : incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset ⊆ Q)
    (hquery : ∀ a ∈ B, incidentSupport G hloc (finite_reachBall hloc a q.radius).toFinset ⊆ Q)
    (A H : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ a b, matrixCoeff A a b = (q.kernel p a b : ℂ))
    (hH : ∀ a b, matrixCoeff H a b = (orbitBinConnection G p o n a b : ℂ)) :
    (∫ ω, q.amplificationMarginal Q B x k n z p ω ∂law p) ≤
      (matrixCoeff (A^k*H) z.val x).re := by
  have hposA : PositiveRealMatrix A := fun a b => by
    rw [hA a b]
    exact ⟨rfl,q.kernel_nonneg p a b⟩
  have hposH : PositiveRealMatrix H := fun a b => by
    rw [hH a b]
    exact ⟨rfl,orbitBinConnection_nonneg G p o n a b⟩
  rw [q.amplificationMarginal_mean_kernel Q B x k n z p hx hz hquery]
  have he : (∑ r : Fin k → ↥B, finiteBinConnection G Q p x n (amplificationVertices B k z r 0) *
      oldRunWeight (fun _ (a b : ↥B) => q.kernel p a.val b.val) k z r) =
      ∑ r : Fin k → ↥B,
        oldRunWeight (fun _ (a b : ↥B) => (matrixCoeff A a.val b.val).re) k z r *
          (matrixCoeff H (oldRunVertices k z r 0).val x).re := by
    apply Finset.sum_congr rfl
    intro r _
    simp only [hA,hH,Complex.ofReal_re,
      finiteBinConnection_eq_binConnection G hloc Q p x n _ hroot]
    by_cases hr : oldRunWeight (fun _ (a b : ↥B) => q.kernel p a.val b.val) k z r = 0
    · simp only [hr,mul_zero,zero_mul]
    · have hy : (oldRunVertices k z r 0).val ∈ vertexOrbit G o :=
        oldRun_endpoint_mem (fun a : ↥B => a.val ∈ vertexOrbit G o)
          (fun _ (a b : ↥B) => q.kernel p a.val b.val)
          (fun _ a b hab => by
            by_contra hb
            exact hab (q.kernel_zero_of_end_not_mem p a.val b.val hb)) k z hz r hr
      rw [orbitBinConnection,ite_eq_left ⟨hy,hx⟩,binConnection_symm G p n]
      exact mul_comm _ _
  rw [he]
  exact finite_oldRun_operator_domination A H hposA hposH B k z x

end LocalEndpointRule

 

theorem exists_operator_of_amplification_domination
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (o : V) (n k : ℕ)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A)
    (F : V → V → ℝ) (hF : ∀ x z, 0 ≤ F x z)
    (hdom : ∀ (H : Hilbert V →L[ℂ] Hilbert V),
      (∀ x y, matrixCoeff H x y = (orbitBinConnection G p o n x y : ℂ)) →
      ∀ x z, F x z ≤ (matrixCoeff (A^k*H) z x).re) :
    ∃ T : Hilbert V →L[ℂ] Hilbert V, ‖T‖ ≤ binOrbitRow G p o n * ‖A‖^k ∧
      ∀ x z, matrixCoeff T x z = (F x z : ℂ) := by
  obtain ⟨H,hHnorm,hH⟩ := exists_orbitBinConnection_operator G hloc p o n
  have hposH : PositiveRealMatrix H := fun x y => by
    rw [hH x y]
    exact ⟨rfl,orbitBinConnection_nonneg G p o n x y⟩
  have hpos := ((hA.pow k).mul hposH).star
  have htr (x z : V) : (matrixCoeff (star (A^k*H)) x z).re = (matrixCoeff (A^k*H) z x).re := by
    simp only [matrixCoeff_adjoint,Complex.star_def,Complex.conj_re]
  obtain ⟨T,hTnorm,hT⟩ := exists_operator_of_matrix_domination
    (fun x z => (matrixCoeff (star (A^k*H)) x z).re) F (fun x z => (hpos x z).2)
    (fun x z => by rw [abs_of_nonneg (hF x z),htr]; exact hdom H hH x z)
    (star (A^k*H)) (fun x z => hpos.real x z)
  refine ⟨T,hTnorm.trans ?_,hT⟩
  have hpow : ∀ j : ℕ, ‖A^j‖ ≤ ‖A‖^j := by
    intro j
    induction j with
    | zero => simpa only [pow_zero, ContinuousLinearMap.one_def] using (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := Hilbert V))
    | succ j ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))
  calc
    ‖star (A^k*H)‖ = ‖A^k*H‖ := by
      change ‖ContinuousLinearMap.adjoint (A^k*H)‖ = _
      exact LinearIsometryEquiv.norm_map _ _
    _ ≤ ‖A^k‖ * ‖H‖ := norm_mul_le _ _
    _ ≤ ‖A‖^k * binOrbitRow G p o n := mul_le_mul (hpow k) hHnorm
      (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
    _ = binOrbitRow G p o n * ‖A‖^k := mul_comm _ _

end AmplificationOperatorDomination

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterVisitKernel
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

theorem conditionalSuccess_nonneg (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x : V) :
    0 ≤ q.conditionalSuccess ω x := tsum_nonneg (q.nonneg ω x)

theorem conditionalSuccess_support (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x : V)
    (h : q.conditionalSuccess ω x ≠ 0) :
    x ∈ O ∧ (cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M := by
  have he : ∃ y, q.mass ω x y ≠ 0 := by
    by_contra hn
    push Not at hn
    exact h (by simp only [conditionalSuccess,hn,tsum_zero])
  obtain ⟨y,hy⟩ := he
  obtain ⟨hx,_,_,hf,hc,_⟩ := q.support ω x y hy
  exact ⟨hx,hf,hc⟩

theorem conditionalSuccess_local (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x : V) :
    q.conditionalSuccess ω x = q.conditionalSuccess
      (ω ∩ (incidentSupport G hloc (finite_reachBall hloc x q.radius).toFinset : Set E)) x :=
  tsum_congr (q.locality ω x)

theorem conditionalSuccess_integrable (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    Integrable (fun ω => q.conditionalSuccess ω x) (law p) :=
  integrable_finite_local _ p _ (fun ω => q.conditionalSuccess_local ω x)

theorem conditionalSuccess_mean (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    (∫ ω, q.conditionalSuccess ω x ∂law p) = q.successProbability p x :=
  (q.kernel_row_integral p x).symm

theorem conditionalSuccess_covariant (q : LocalEndpointRule G hloc O M L)
    (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (ω : Set E) (x : V) :
    q.conditionalSuccess (b ⁻¹' ω) x = q.conditionalSuccess ω (a x) := by
  unfold conditionalSuccess
  simp_rw [q.covariance a b hab]
  exact a.tsum_eq _



theorem clusterVisitMass_nonneg (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x a : V) :
    0 ≤ q.clusterVisitMass ω x a := by
  unfold clusterVisitMass
  split_ifs
  · exact q.conditionalSuccess_nonneg ω x
  · exact le_refl _

theorem clusterVisitMass_outside (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x a : V)
    (ha : a ∉ reachBall G x M) : q.clusterVisitMass ω x a = 0 := by
  by_cases h : q.conditionalSuccess ω x = 0
  · simp only [clusterVisitMass,h,ite_self]
  · obtain ⟨_,hf,hc⟩ := q.conditionalSuccess_support ω x h
    exact ite_eq_right (fun hmem => ha (finite_cluster_subset_reachBall G ω x hf M hc hmem))

theorem clusterVisitMass_local (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x a : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset
    q.clusterVisitMass ω x a = q.clusterVisitMass (ω ∩ (Q : Set E)) x a := by
  dsimp only
  let Q := incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset
  change q.clusterVisitMass ω x a = q.clusterVisitMass (ω ∩ (Q:Set E)) x a
  have he := finite_local_of_subset _ Q
    (incidentSupport_ball_mono G hloc x (le_max_left q.radius M))
    (fun ω => q.conditionalSuccess ω x) (fun ω => q.conditionalSuccess_local ω x) ω
  by_cases h : q.conditionalSuccess ω x = 0
  · have h' : q.conditionalSuccess (ω ∩ (Q:Set E)) x = 0 := he.symm.trans h
    simp only [clusterVisitMass,h,h',ite_self]
  · obtain ⟨_,hf,hc⟩ := q.conditionalSuccess_support ω x h
    have hs : cluster G ω x ⊆ (finite_reachBall hloc x (max q.radius M)).toFinset := by
      simpa only [Set.Finite.coe_toFinset] using
        finite_cluster_subset_reachBall G ω x hf _ (hc.trans (le_max_right _ _))
    have hc' := cluster_restrict_incident_of_full G hloc _ ω x hs
    change cluster G (ω ∩ (Q:Set E)) x = cluster G ω x at hc'
    change (if a ∈ cluster G ω x then _ else _) = (if a ∈ cluster G (ω ∩ (Q:Set E)) x then _ else _)
    rw [hc',he]

theorem clusterVisitMass_integrable (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x a : V) :
    Integrable (fun ω => q.clusterVisitMass ω x a) (law p) :=
  integrable_finite_local _ p _ (fun ω => q.clusterVisitMass_local ω x a)

theorem clusterVisitMass_covariant (q : LocalEndpointRule G hloc O M L)
    (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (ω : Set E) (x y : V) :
    q.clusterVisitMass (b ⁻¹' ω) x y = q.clusterVisitMass ω (a x) (a y) := by
  have hc : y ∈ cluster G (b ⁻¹' ω) x ↔ a y ∈ cluster G ω (a x) := by
    rw [← cluster_aut G hab ω x]
    constructor
    · intro hy; exact ⟨y,hy,rfl⟩
    · rintro ⟨z,hz,he⟩
      exact (a.injective he) ▸ hz
  simp only [clusterVisitMass,hc,q.conditionalSuccess_covariant a b hab]

theorem clusterVisitMass_row_le (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x : V) :
    (∑' a, q.clusterVisitMass ω x a) ≤ M * q.conditionalSuccess ω x := by
  by_cases h : q.conditionalSuccess ω x = 0
  · simp only [clusterVisitMass,h,ite_self,tsum_zero,mul_zero,le_refl]
  obtain ⟨_,hf,hc⟩ := q.conditionalSuccess_support ω x h
  rw [tsum_eq_sum (f := q.clusterVisitMass ω x) (s := hf.toFinset) (fun a ha => ite_eq_right (by simpa only [Set.Finite.mem_toFinset] using ha))]
  have he : (∑ a ∈ hf.toFinset, q.clusterVisitMass ω x a) =
      (hf.toFinset.card:ℝ) * q.conditionalSuccess ω x := by
    calc
      _ = ∑ _a ∈ hf.toFinset, q.conditionalSuccess ω x := Finset.sum_congr rfl (fun a ha => ite_eq_left (hf.mem_toFinset.mp ha))
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  rw [he]
  apply mul_le_mul_of_nonneg_right _ (q.conditionalSuccess_nonneg ω x)
  exact_mod_cast (by simpa only [← Set.ncard_eq_toFinset_card _ hf] using hc)

theorem clusterVisitKernel_nonneg (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x a : V) :
    0 ≤ q.clusterVisitKernel p x a := integral_nonneg (fun ω => q.clusterVisitMass_nonneg ω x a)

theorem clusterVisitKernel_outside (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x a : V)
    (ha : a ∉ reachBall G x M) : q.clusterVisitKernel p x a = 0 := by
  simp only [clusterVisitKernel,q.clusterVisitMass_outside _ x a ha,integral_zero]

theorem clusterVisitKernel_summable (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    Summable (q.clusterVisitKernel p x) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x M).toFinset)
  intro a ha
  exact q.clusterVisitKernel_outside p x a (by simpa only [Set.Finite.mem_toFinset] using ha)

theorem clusterVisitKernel_row_le (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    (∑' a, q.clusterVisitKernel p x a) ≤ M * q.successProbability p x := by
  let B := (finite_reachBall hloc x M).toFinset
  have he (ω : Set E) : (∑' a, q.clusterVisitMass ω x a) = ∑ a ∈ B, q.clusterVisitMass ω x a :=
    tsum_eq_sum (fun a ha => q.clusterVisitMass_outside ω x a (by simpa only [B,Set.Finite.mem_toFinset] using ha))
  rw [tsum_eq_sum (s := B) (fun a ha => q.clusterVisitKernel_outside p x a (by simpa only [B,Set.Finite.mem_toFinset] using ha))]
  simp only [clusterVisitKernel]
  rw [← integral_finsetSum B (fun a _ => q.clusterVisitMass_integrable p x a)]
  calc
    _ ≤ ∫ ω, (M:ℝ) * q.conditionalSuccess ω x ∂law p :=
      integral_mono (integrable_finsetSum B (fun a _ => q.clusterVisitMass_integrable p x a))
        ((q.conditionalSuccess_integrable p x).const_mul _) (fun ω => by rw [← he]; exact q.clusterVisitMass_row_le ω x)
    _ = _ := by rw [integral_const_mul,q.conditionalSuccess_mean]

theorem clusterVisitKernel_covariant (q : LocalEndpointRule G hloc O M L) (p : unitInterval)
    (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (x y : V) :
    q.clusterVisitKernel p (a x) (a y) = q.clusterVisitKernel p x y := by
  have hm : Measurable (fun ω => q.clusterVisitMass ω x y) :=
    measurable_finite_local _ _ (fun ω => q.clusterVisitMass_local ω x y)
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable hm.aestronglyMeasurable
  rw [law_map_preimage_equiv p b] at h
  simpa only [clusterVisitKernel,q.clusterVisitMass_covariant a b hab] using h.symm

end LocalEndpointRule
end ClusterVisitKernel

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section VisitEnvelope
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}



theorem visitEnvelope_nonneg (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (k : ℕ) (x a : V) : 0 ≤ q.visitEnvelope o p k x a := by
  induction k generalizing x with
  | zero => exact le_refl _
  | succ k ih =>
    exact add_nonneg (mul_nonneg (pow_nonneg (q.successProbability_nonneg p o) _) (q.clusterVisitKernel_nonneg p x a))
      (tsum_nonneg (fun y => mul_nonneg (q.kernel_nonneg p x y) (ih y)))

theorem visitEnvelope_covariant (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (k : ℕ) (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (x y : V) :
    q.visitEnvelope o p k (a x) (a y) = q.visitEnvelope o p k x y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
    simp only [visitEnvelope,q.clusterVisitKernel_covariant p a b hab]
    congr 1
    rw [← a.tsum_eq (fun z => q.kernel p (a x) z * q.visitEnvelope o p k z (a y))]
    exact tsum_congr fun z => by rw [q.kernel_covariant p a b hab,ih]

 

theorem visitEnvelope_row_bound (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (k : ℕ) (x : V) :
    Summable (q.visitEnvelope o p k x) ∧
      (∑' a, q.visitEnvelope o p k x a) ≤ (k*M:ℕ) * q.successProbability p o ^ k := by
  let u := q.successProbability p o
  have hu : 0 ≤ u := q.successProbability_nonneg p o
  induction k generalizing x with
  | zero => simp only [visitEnvelope,zero_mul,Nat.cast_zero,pow_zero,mul_one,tsum_zero,le_refl,and_true]; exact summable_zero
  | succ k ih =>
    let B := (finite_reachBall hloc x M).toFinset
    have he (a : V) : (∑' y, q.kernel p x y * q.visitEnvelope o p k y a) =
        ∑ y ∈ B, q.kernel p x y * q.visitEnvelope o p k y a :=
      tsum_eq_sum (fun y hy => by
        rw [q.kernel_outside_ball_zero p x y (by simpa only [B,Set.Finite.mem_toFinset] using hy),zero_mul])
    have ht (a : V) : q.visitEnvelope o p (k+1) x a =
        u^k * q.clusterVisitKernel p x a + ∑ y ∈ B, q.kernel p x y * q.visitEnvelope o p k y a := by
      exact congrArg (_ + ·) (he a)
    have hsum : Summable (fun a => ∑ y ∈ B, q.kernel p x y * q.visitEnvelope o p k y a) :=
      summable_sum (s := B) (fun y _ => (ih y).1.mul_left _)
    have hs := ((q.clusterVisitKernel_summable p x).mul_left (u^k)).add hsum
    have hs' : Summable (q.visitEnvelope o p (k+1) x) := by
      change Summable (fun a => q.visitEnvelope o p (k+1) x a)
      simpa only [ht] using hs
    refine ⟨hs',?_⟩
    simp_rw [ht]
    rw [Summable.tsum_add ((q.clusterVisitKernel_summable p x).mul_left _) hsum,tsum_mul_left,
      Summable.tsum_finsetSum (fun y _ => (ih y).1.mul_left _)]
    simp_rw [tsum_mul_left]
    have hr : (∑ y ∈ B, q.kernel p x y) ≤ u :=
      ((q.summable_kernel p x).sum_le_tsum B (fun y _ => q.kernel_nonneg p x y)).trans
        (q.kernel_row_le_success o p x)
    calc
      _ ≤ u^k * (M*u) + ∑ y ∈ B, q.kernel p x y * ((k*M:ℕ)*u^k) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu _)
          exact (q.clusterVisitKernel_row_le p x).trans
            (mul_le_mul_of_nonneg_left (q.kernel_row_le_success o p x) (Nat.cast_nonneg _))
        · exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (ih y).2 (q.kernel_nonneg p x y)
      _ ≤ u^k * (M*u) + u*((k*M:ℕ)*u^k) := by
        rw [← Finset.sum_mul]
        exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hr (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hu _)))
      _ = ((k+1)*M:ℕ) * q.successProbability p o ^ (k+1) := by
        change _ = ((k+1)*M:ℕ) * u^(k+1)
        simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
        ring

end LocalEndpointRule
end VisitEnvelope

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section MarkedOldRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*}

theorem oldRunWeight_congr (K K' : ℕ → W → W → ℝ) (k : ℕ)
    (h : ∀ i, 1 ≤ i → i ≤ k → ∀ a b, K i a b = K' i a b) (z : W) (r : Fin k → W) :
    oldRunWeight K k z r = oldRunWeight K' k z r := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    simp only [oldRunWeight]
    rw [h (k+1) (by omega) (by omega),ih (fun i hi hik => h i hi (by omega))]

theorem oldRunWeight_prod (K : ℕ → W → W → ℝ) (k : ℕ) (z : W) (r : Fin k → W) :
    oldRunWeight K k z r = ∏ i ∈ Finset.Icc 1 k,
      K i (oldRunVertices k z r i) (oldRunVertices k z r (i-1)) := by
  induction k generalizing z with
  | zero => simp [oldRunWeight]
  | succ k ih =>
    rw [Finset.prod_Icc_succ_top (by omega)]
    have he : (∏ i ∈ Finset.Icc 1 k, K i (oldRunVertices (k+1) z r i)
        (oldRunVertices (k+1) z r (i-1))) = oldRunWeight K k (r 0) (Fin.tail r) := by
      rw [ih]
      apply Finset.prod_congr rfl
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      rw [oldRunVertices_succ_of_le _ _ _ _ hi'.2,
        oldRunVertices_succ_of_le _ _ _ _ (by omega)]
    rw [he,oldRunVertices_last,Nat.add_sub_cancel,
      oldRunVertices_succ_of_le _ _ _ _ (le_refl _),oldRunVertices_last]
    exact mul_comm _ _



theorem markedOldRun_nonneg (K C : ℕ → W → W → ℝ)
    (hK : ∀ i a b, 0 ≤ K i a b) (hC : ∀ i a b, 0 ≤ C i a b)
    (k : ℕ) (z : W) (r : Fin k → W) : 0 ≤ markedOldRun K C k z r := by
  apply Finset.sum_nonneg
  intro i _
  apply oldRunWeight_nonneg
  intro j a b
  split_ifs
  · exact hC j a b
  · exact hK j a b

theorem markedOldRun_succ (K C : ℕ → W → W → ℝ) (k : ℕ) (z : W) (r : Fin (k+1) → W) :
    markedOldRun K C (k+1) z r =
      K (k+1) z (r 0) * markedOldRun K C k (r 0) (Fin.tail r) +
      C (k+1) z (r 0) * oldRunWeight K k (r 0) (Fin.tail r) := by
  unfold markedOldRun
  rw [Finset.sum_Icc_succ_top (by omega),Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hne : k+1 ≠ i := by have := Finset.mem_Icc.mp hi; omega
    simp only [oldRunWeight,ite_eq_right hne]
  · simp only [oldRunWeight,ite_true]
    congr 1
    apply oldRunWeight_congr
    intro i hi hik a b
    exact ite_eq_right (by omega)

theorem sum_markedOldRun_succ [Fintype W] (K C : ℕ → W → W → ℝ) (k : ℕ) (z : W) :
    (∑ r : Fin (k+1) → W, markedOldRun K C (k+1) z r) =
      ∑ b : W, (K (k+1) z b * (∑ r : Fin k → W, markedOldRun K C k b r) +
        C (k+1) z b * (∑ r : Fin k → W, oldRunWeight K k b r)) := by
  rw [Fintype.sum_equiv (oldRunConsEquiv k) _
    (fun r => K (k+1) z r.1 * markedOldRun K C k r.1 r.2 + C (k+1) z r.1 * oldRunWeight K k r.1 r.2)
      (by intro r; exact markedOldRun_succ K C k z r),Fintype.sum_prod_type]
  simp only [Finset.sum_add_distrib,Finset.mul_sum]

 
theorem oldRunWeight_integral_indexed (Q : Finset E) (p : ℝ)
    (q : ℕ → Set E → W → W → ℝ) (k : ℕ) (z : W) (r : Fin k → W) :
    finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => oldRunWeight (fun i => q i (η i)) k z r) =
      oldRunWeight (fun i a b => finiteFieldIntegral Q p (fun ω => q i ω a b)) k z r := by
  calc
    _ = finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
        ∏ i : ↥(Finset.Icc 1 k), q i (η i) (oldRunVertices k z r i)
          (oldRunVertices k z r (i.val-1))) := by
      congr 1
      funext η
      rw [oldRunWeight_prod]
      exact (Finset.prod_coe_sort (Finset.Icc 1 k)
        (fun i => q i (η i) (oldRunVertices k z r i) (oldRunVertices k z r (i-1)))).symm
    _ = ∏ i : ↥(Finset.Icc 1 k), finiteFieldIntegral Q p (fun ω =>
        q i ω (oldRunVertices k z r i) (oldRunVertices k z r (i.val-1))) :=
      finiteFamilyIntegral_prod Q (Finset.Icc 1 k) p
        (fun i ω => q i ω (oldRunVertices k z r i) (oldRunVertices k z r (i.val-1)))
    _ = _ := by
      rw [oldRunWeight_prod]
      exact Finset.prod_coe_sort (Finset.Icc 1 k) (fun i => finiteFieldIntegral Q p
        (fun ω => q i ω (oldRunVertices k z r i) (oldRunVertices k z r (i-1))))

theorem markedOldRun_integral (Q : Finset E) (p : ℝ)
    (q c : ℕ → Set E → W → W → ℝ) (k : ℕ) (z : W) (r : Fin k → W) :
    finiteFamilyIntegral Q (Finset.Icc 1 k) p
      (fun η => markedOldRun (fun i => q i (η i)) (fun i => c i (η i)) k z r) =
      markedOldRun (fun i a b => finiteFieldIntegral Q p (fun ω => q i ω a b))
        (fun i a b => finiteFieldIntegral Q p (fun ω => c i ω a b)) k z r := by
  unfold markedOldRun
  rw [finiteFamilyIntegral_sum]
  apply Finset.sum_congr rfl
  intro i _
  change finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
      oldRunWeight (fun j => (fun ω a b => if j=i then c j ω a b else q j ω a b) (η j)) k z r) = _
  rw [oldRunWeight_integral_indexed Q p (fun j ω a b => if j=i then c j ω a b else q j ω a b) k z r]
  congr 1
  funext j a b
  by_cases h : j = i <;> simp only [h,ite_true,ite_false]

 

theorem trajectory_indicator_le_marked (G : BondGraph V E) (e : W → V)
    (q : Set E → W → W → ℝ) (hq : ∀ ω x y, 0 ≤ q ω x y)
    (k : ℕ) (η : ℕ → Set E) (z : W) (r : Fin k → W) (a : V) :
    (if a ∈ trajectoryUnion G η (e ∘ oldRunVertices k z r) k then
      oldRunWeight (fun i => q (η i)) k z r else 0) ≤
      markedOldRun (fun i => q (η i))
        (fun i x y => if a ∈ cluster G (η i) (e x) then q (η i) x y else 0) k z r := by
  have hC : ∀ i x y, 0 ≤ (if a ∈ cluster G (η i) (e x) then q (η i) x y else 0) := by
    intro i x y; split_ifs; exact hq _ _ _; exact le_refl _
  by_cases ha : a ∈ trajectoryUnion G η (e ∘ oldRunVertices k z r) k
  · rw [ite_eq_left ha]
    obtain ⟨i,hi,hik,hai⟩ := (mem_trajectoryUnion G η (e ∘ oldRunVertices k z r) k a).mp ha
    have he : oldRunWeight (fun j x y => if j=i then
        (if a ∈ cluster G (η j) (e x) then q (η j) x y else 0) else q (η j) x y) k z r =
        oldRunWeight (fun j => q (η j)) k z r := by
      simp_rw [oldRunWeight_prod]
      apply Finset.prod_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        simp only [ite_true,Function.comp_apply] at hai ⊢
        exact ite_eq_left hai
      · exact ite_eq_right hji
    rw [← he]
    unfold markedOldRun
    apply Finset.single_le_sum _ (Finset.mem_Icc.mpr ⟨hi,hik⟩)
    intro j _
    apply oldRunWeight_nonneg
    intro l x y
    split_ifs
    · exact hq _ _ _
    · exact le_refl _
    · exact hq _ _ _
  · rw [ite_eq_right ha]
    exact markedOldRun_nonneg _ _ (fun _ => hq _) hC k z r

end MarkedOldRun

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TrajectoryEnvelopeDomination
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finiteTrajectoryMass_le_marked {W : Type*} [Fintype W]
    (G : BondGraph V E) (e : W → V) (Q : Finset E) (p : unitInterval) (k : ℕ)
    (q : Set E → W → W → ℝ) (hq : ∀ ω x y, 0 ≤ q ω x y) (z : W) (a : V) :
    finiteTrajectoryMass G e Q p k q z a ≤
      ∑ r : Fin k → W, markedOldRun (fun _ => finiteOldKernel Q p q)
        (fun _ x y => finiteFieldIntegral Q p (fun ω => if a ∈ cluster G ω (e x) then q ω x y else 0)) k z r := by
  unfold finiteTrajectoryMass
  calc
    _ ≤ finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => ∑ r : Fin k → W,
        markedOldRun (fun i => q (η i))
          (fun i x y => if a ∈ cluster G (η i) (e x) then q (η i) x y else 0) k z r) :=
      finiteFamilyIntegral_mono Q (Finset.Icc 1 k) p _ _ (fun η => Finset.sum_le_sum (fun r _ =>
        trajectory_indicator_le_marked G e q hq k η z r a))
    _ = _ := by
      rw [finiteFamilyIntegral_sum]
      apply Finset.sum_congr rfl
      intro r _
      exact markedOldRun_integral Q p (fun _ => q)
        (fun _ ω x y => if a ∈ cluster G ω (e x) then q ω x y else 0) k z r

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem finite_marked_step_row_le (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (p : unitInterval) (x a : V)
    (hQ : incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset ⊆ Q) :
    (∑ y : ↥B, finiteFieldIntegral Q p (fun ω =>
      if a ∈ cluster G ω x then q.mass ω x y.val else 0)) ≤ q.clusterVisitKernel p x a := by
  rw [← finiteFieldIntegral_sum]
  have he : q.clusterVisitKernel p x a = finiteFieldIntegral Q p (fun ω => q.clusterVisitMass ω x a) :=
    integral_finite_local Q p _ (finite_local_of_subset _ Q hQ _ (q.clusterVisitMass_local · x a))
  rw [he]
  apply Finset.sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_left _ (finiteFieldWeight_nonneg Q p ω)
  dsimp only
  by_cases ha : a ∈ cluster G (finiteFieldSet Q ω) x
  · simp only [ha,ite_true,clusterVisitMass]
    rw [Finset.sum_coe_sort B (fun y => q.mass (finiteFieldSet Q ω) x y)]
    exact (q.summable_mass _ x).sum_le_tsum B (fun y _ => q.nonneg _ x y)
  · simp only [ha,ite_false,clusterVisitMass,Finset.sum_const_zero,le_refl]

 

theorem sum_markedOldRun_le_envelope (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (p : unitInterval) (k : ℕ) (z : ↥B) (a : V)
    (hQ : ∀ x ∈ B, incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset ⊆ Q) :
    (∑ r : Fin k → ↥B, markedOldRun
      (fun _ => finiteOldKernel Q p (fun ω (x y : ↥B) => q.mass ω x.val y.val))
      (fun _ (x y : ↥B) => finiteFieldIntegral Q p (fun ω =>
        if a ∈ cluster G ω x.val then q.mass ω x.val y.val else 0)) k z r) ≤
      q.visitEnvelope o p k z.val a := by
  let u := q.successProbability p o
  let K : ↥B → ↥B → ℝ := finiteOldKernel Q p (fun ω (x y : ↥B) => q.mass ω x.val y.val)
  let C : ↥B → ↥B → ℝ := fun x y => finiteFieldIntegral Q p (fun ω =>
    if a ∈ cluster G ω x.val then q.mass ω x.val y.val else 0)
  have hK (x y : ↥B) : K x y = q.kernel p x.val y.val :=
    q.finiteOldKernel_eq_kernel Q p x.val y.val
      ((incidentSupport_ball_mono G hloc x.val (le_max_left _ _)).trans (hQ x.val x.property))
  have hKn (x y : ↥B) : 0 ≤ K x y := by rw [hK]; exact q.kernel_nonneg p _ _
  have hCn (x y : ↥B) : 0 ≤ C x y := by
    apply finiteFieldIntegral_nonneg
    intro ω; split_ifs; exact q.nonneg ω _ _; exact le_refl _
  have hKr (x : ↥B) : (∑ y, K x y) ≤ u := by
    simp only [hK]
    rw [Finset.sum_coe_sort B (fun y => q.kernel p x.val y)]
    exact ((q.summable_kernel p x.val).sum_le_tsum B (fun y _ => q.kernel_nonneg p x.val y)).trans
      (q.kernel_row_le_success o p x.val)
  have hCr (x : ↥B) : (∑ y, C x y) ≤ q.clusterVisitKernel p x.val a :=
    q.finite_marked_step_row_le o Q B p x.val a (hQ x.val x.property)
  change (∑ r : Fin k → ↥B, markedOldRun (fun _ => K) (fun _ => C) k z r) ≤ _
  induction k generalizing z with
  | zero => simp [markedOldRun,visitEnvelope]
  | succ k ih =>
    rw [sum_markedOldRun_succ]
    have hs : Summable (fun y => q.kernel p z.val y * q.visitEnvelope o p k y a) := by
      apply summable_of_ne_finset_zero (s := (finite_reachBall hloc z.val M).toFinset)
      intro y hy
      rw [q.kernel_outside_ball_zero p z.val y (by simpa only [Set.Finite.mem_toFinset] using hy),zero_mul]
    calc
      _ ≤ ∑ y : ↥B, (K z y * q.visitEnvelope o p k y.val a + C z y * u^k) :=
        Finset.sum_le_sum fun y _ => add_le_add
          (mul_le_mul_of_nonneg_left (ih y) (hKn z y))
          (mul_le_mul_of_nonneg_left (sum_oldRunWeight_le (fun _ => K) (fun _ => hKn)
            u (q.successProbability_nonneg p o) (fun _ => hKr) k y) (hCn z y))
      _ = (∑ y : ↥B, K z y * q.visitEnvelope o p k y.val a) + (∑ y : ↥B, C z y)*u^k := by
        rw [Finset.sum_add_distrib,Finset.sum_mul]
      _ ≤ (∑' y, q.kernel p z.val y * q.visitEnvelope o p k y a) + q.clusterVisitKernel p z.val a * u^k := by
        apply add_le_add
        · simp only [hK]
          rw [Finset.sum_coe_sort B (fun y => q.kernel p z.val y * q.visitEnvelope o p k y a)]
          exact hs.sum_le_tsum B (fun y _ => mul_nonneg (q.kernel_nonneg p z.val y) (q.visitEnvelope_nonneg o p k y a))
        · exact mul_le_mul_of_nonneg_right (hCr z) (pow_nonneg (q.successProbability_nonneg p o) _)
      _ = q.visitEnvelope o p (k+1) z.val a := by rw [visitEnvelope]; ring

theorem finiteTrajectoryMass_le_envelope (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (p : unitInterval) (k : ℕ) (z : ↥B) (a : V)
    (hQ : ∀ x ∈ B, incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset ⊆ Q) :
    finiteTrajectoryMass G Subtype.val Q p k (fun ω (x y : ↥B) => q.mass ω x.val y.val) z a ≤
      q.visitEnvelope o p k z.val a :=
  (finiteTrajectoryMass_le_marked G Subtype.val Q p k _ (fun ω x y => q.nonneg ω x.val y.val) z a).trans
    (q.sum_markedOldRun_le_envelope o Q B p k z a hQ)

end LocalEndpointRule
end TrajectoryEnvelopeDomination

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_EndpointMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TrajectoryHitTransport
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}
variable {ι : Type*} [Fintype ι]

 

theorem visitEnvelope_column_bound (hconn : Connected G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (k : ℕ) (a : V) :
    Summable (fun z => q.visitEnvelope o p k z a) ∧
      (∑' z, q.visitEnvelope o p k z a) ≤ c*((k*M:ℕ)*q.successProbability p o ^ k) := by
  apply transported_column_of_row_bound G hconn hloc root weight Γ hΓ htr hcov hw hw1 c hc hmin
    (q.visitEnvelope o p k) (q.visitEnvelope_nonneg o p k) _
    (fun z => (q.visitEnvelope_row_bound o p k z).1) _
    (fun z => (q.visitEnvelope_row_bound o p k z).2) a
  intro b hb x y
  obtain ⟨d,hd⟩ := hΓ hb
  exact q.visitEnvelope_covariant o p k b d hd x y

 

theorem finiteTrajectoryHit_sum_le (hconn : Connected G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (p : unitInterval) (k : ℕ) (A : Finset V)
    (hQ : ∀ x ∈ B, incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset ⊆ Q) :
    (∑ z : ↥B, finiteTrajectoryHit G Subtype.val Q p k
      (fun ω (x y : ↥B) => q.mass ω x.val y.val) z A) ≤
      (A.card:ℝ) * (c*((k*M:ℕ)*q.successProbability p o ^ k)) := by
  have hcol := fun a => q.visitEnvelope_column_bound hconn root weight Γ hΓ htr hcov hw hw1 c hc hmin o p k a
  calc
    _ ≤ ∑ z : ↥B, ∑ a ∈ A, q.visitEnvelope o p k z.val a := by
      apply Finset.sum_le_sum
      intro z _
      exact (finiteTrajectoryHit_le_sum G Subtype.val Q p k _ (fun ω x y => q.nonneg ω x.val y.val) z A).trans
        (Finset.sum_le_sum fun a _ => q.finiteTrajectoryMass_le_envelope o Q B p k z a hQ)
    _ = ∑ a ∈ A, ∑ z : ↥B, q.visitEnvelope o p k z.val a := Finset.sum_comm
    _ ≤ ∑ _a ∈ A, c*((k*M:ℕ)*q.successProbability p o ^ k) := by
      apply Finset.sum_le_sum
      intro a _
      rw [Finset.sum_coe_sort B (fun z => q.visitEnvelope o p k z a)]
      exact ((hcol a).1.sum_le_tsum B (fun z _ => q.visitEnvelope_nonneg o p k z a)).trans (hcol a).2
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

end LocalEndpointRule
end TrajectoryHitTransport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AllEndpointHit
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finiteChoiceHit_allRuns {W : Type*} [Fintype W]
    (G : BondGraph V E) (e : W → V) (Q : Finset E) (p : ℝ) (k : ℕ)
    (q : Set E → W → W → ℝ) (A : Finset V) :
    finiteChoiceHit G k Q p
      (fun (r : W × (Fin k → W)) _ => e ∘ oldRunVertices k r.1 r.2)
      (fun r η => oldRunWeight (fun i => q (η i)) k r.1 r.2) (A : Set V) =
      ∑ z : W, finiteTrajectoryHit G e Q p k q z A := by
  unfold finiteChoiceHit finiteTrajectoryHit
  rw [Fintype.sum_prod_type]
  simp only [finiteFamilyIntegral_sum]

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

theorem allAmplificationWeight_nonneg (q : LocalEndpointRule G hloc O M L)
    (B : Finset V) (k : ℕ) (r : ↥B × (Fin k → ↥B)) (η : ℕ → Set E) :
    0 ≤ q.allAmplificationWeight B k r η :=
  oldRunWeight_nonneg (fun i (a b : ↥B) => q.mass (η i) a.val b.val) (fun i a b => q.nonneg (η i) a.val b.val) k r.1 r.2

variable {ι : Type*} [Fintype ι]

theorem allAmplificationHit_bound (hconn : Connected G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (p : unitInterval) (k : ℕ) (A : Set V) (hf : A.Finite)
    (hQ : ∀ x ∈ B, incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset ⊆ Q) :
    finiteChoiceHit G k Q p (allAmplificationVertices B k) (q.allAmplificationWeight B k) A ≤
      (A.ncard:ℝ) * (c*((k*M:ℕ)*q.successProbability p o ^ k)) := by
  have he : finiteChoiceHit G k Q p (allAmplificationVertices B k) (q.allAmplificationWeight B k) A =
      ∑ z : ↥B, finiteTrajectoryHit G Subtype.val Q p k
        (fun ω (a b : ↥B) => q.mass ω a.val b.val) z hf.toFinset := by
    rw [← finiteChoiceHit_allRuns]
    rw [hf.coe_toFinset]
    rfl
  rw [he,Set.ncard_eq_toFinset_card A hf]
  exact q.finiteTrajectoryHit_sum_le hconn root weight Γ hΓ htr hcov hw hw1 c hc hmin o Q B p k hf.toFinset hQ

end LocalEndpointRule
end AllEndpointHit

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AllEndpointSeparated
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteChoiceHit_nonneg {P : Type*} [Fintype P]
    (G : BondGraph V E) (k : ℕ) (Q : Finset E) (p : unitInterval)
    (y : P → (ℕ → Set E) → ℕ → V) (m : P → (ℕ → Set E) → ℝ)
    (hm : ∀ r η, 0 ≤ m r η) (A : Set V) : 0 ≤ finiteChoiceHit G k Q p y m A := by
  apply Finset.sum_nonneg
  intro r _
  apply finiteFamilyIntegral_nonneg
  intro η
  split_ifs
  · exact hm r η
  · exact le_refl _

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}
variable {ι : Type*} [Fintype ι]

 

theorem amplificationSeparatedSecondMoment_le [Nonempty E] (hconn : Connected G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (p : unitInterval) (x : V) (k n : ℕ)
    (hQ : ∀ a ∈ B, incidentSupport G hloc (finite_reachBall hloc a (max q.radius M)).toFinset ⊆ Q) :
    finiteChoiceSeparatedPairMass G x k Q p
      (q.allAmplificationInputs Q B x k n) (q.allAmplificationInputs Q B x k n)
      (allAmplificationVertices B k) (allAmplificationVertices B k)
      (q.allAmplificationWeight B k) (q.allAmplificationWeight B k) ≤
      (((2*n:ℕ):ℝ) * (c*((k*M:ℕ)*q.successProbability p o ^ k)))^2 *
        finiteClusterWindowMass G Q p x (n-k*M) (2*n) := by
  let A := q.allAmplificationInputs Q B x k n
  let y := allAmplificationVertices (E := E) B k
  let m := q.allAmplificationWeight B k
  have hA (r) : A r ⊆ finiteSpliceDomain Q (Finset.Icc 1 k) :=
    q.amplificationInputs_subset Q B x k n r.1 r.2
  have hbin r s (hs : s ∈ A r) : (cluster G s.1 x).Finite ∧
      n ≤ (cluster G s.1 x).ncard ∧ (cluster G s.1 x).ncard < 2*n := by
    have hd := (mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) s).mp (hA r hs)
    have hb := (q.mem_amplificationInputs Q B x k n r.1 r.2 s).mp hs
    exact ⟨cluster_finite_of_finite_edges G (Q.finite_toSet.subset hd.1) x,hb.2.2.2.1,hb.2.2.2.2.1⟩
  have hcap r s (hs : s ∈ A r) (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
      (cluster G (s.2 i) (y r s.2 i)).Finite ∧ (cluster G (s.2 i) (y r s.2 i)).ncard ≤ M := by
    have hd := q.amplificationInputs_chain Q B x k n r.1 r.2 s hs i hi hik
    exact ⟨hd.2.1,hd.2.2.1⟩
  have hm := q.allAmplificationWeight_nonneg B k
  have hb := finiteChoiceSeparatedPairMass_le G hloc x k n M Q p A A y y m m hm hm hA hA hbin
    (fun r s hs i hi hik => (hcap r s hs i hi hik).1) hcap
  let d : ℝ := c*((k*M:ℕ)*q.successProbability p o ^ k)
  have hd : 0 ≤ d := mul_nonneg hc (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (q.successProbability_nonneg p o) _))
  let t : ℝ := ((2*n:ℕ):ℝ)*d
  apply hb.trans
  unfold finiteClusterWindowMass finiteFieldIntegral
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _
  have he : t^2 * (finiteFieldWeight Q p ω * (if (cluster G (finiteFieldSet Q ω) x).Finite ∧
      n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
      (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then 1 else 0)) =
      finiteFieldWeight Q p ω * (if (cluster G (finiteFieldSet Q ω) x).Finite ∧
      n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
      (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then t^2 else 0) := by
    split_ifs <;> ring
  change _ ≤ t^2 * _
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (finiteFieldWeight_nonneg Q p ω)
  by_cases h : (cluster G (finiteFieldSet Q ω) x).Finite ∧
      n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
      (cluster G (finiteFieldSet Q ω) x).ncard < 2*n
  · rw [ite_eq_left h,ite_eq_left h]
    have hhit := q.allAmplificationHit_bound hconn root weight Γ hΓ htr hcov hw hw1 c hc hmin
      o Q B p k (cluster G (finiteFieldSet Q ω) x) h.1 hQ
    have hc' : ((cluster G (finiteFieldSet Q ω) x).ncard:ℝ) ≤ ((2*n:ℕ):ℝ) := by exact_mod_cast h.2.2.le
    have hhit' : finiteChoiceHit G k Q p y m (cluster G (finiteFieldSet Q ω) x) ≤ t :=
      hhit.trans (mul_le_mul_of_nonneg_right hc' hd)
    simpa only [pow_two] using mul_self_le_mul_self
      (finiteChoiceHit_nonneg G k Q p y m hm _) hhit'
  · rw [ite_eq_right h,ite_eq_right h]

end LocalEndpointRule
end AllEndpointSeparated

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AllEndpointMarginal
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem finiteRootLoad_sum {P : Type*} (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (S : Finset P) (f : P → SpliceState E → ℝ) (ω : FiniteField Q) :
    finiteRootLoad Q J p (fun s => ∑ z ∈ S, f z s) ω =
      ∑ z ∈ S, finiteRootLoad Q J p (f z) ω := by
  simp only [finiteRootLoad,Finset.mul_sum]
  exact Finset.sum_comm

 

theorem finiteChoiceForwardLoad_prod {P R : Type*} [Fintype P] [Fintype R]
    (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P × R → Finset (SpliceState E)) (y : P × R → SpliceState E → ℕ → V)
    (m : SpliceState E → P × R → ℝ) (t : SpliceState E) :
    finiteChoiceForwardLoad G x k Q A y m t = ∑ z : P,
      finiteChoiceForwardLoad G x k Q (fun r => A (z,r)) (fun r => y (z,r))
        (fun s r => m s (z,r)) t := by
  unfold finiteChoiceForwardLoad finiteInverseLoad
  rw [Fintype.sum_sigma,Fintype.sum_prod_type]
  simp only [Fintype.sum_sigma,choiceTraceOutput,choiceTraceMass,choiceTraceInput]
  rfl

 
theorem endpointRootMass_choice_prod {P R : Type*} [Fintype P] [Fintype R]
    (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E) (p : ℝ)
    (A : P × R → Finset (SpliceState E)) (y : P × R → SpliceState E → ℕ → V)
    (m : SpliceState E → P × R → ℝ) (e : P → V) (he : Function.Injective e)
    (z : P) (ω : Set E) :
    endpointRootMass Q (Finset.Icc 1 k) p (choiceTraceOutput G x k Q A y)
      (fun a => e a.1.1) (choiceTraceMass G x k Q A y m) ω (e z) =
      ∑ a : FiniteChoiceTraceIndex G x k Q (fun r => A (z,r)) (fun r => y (z,r)),
        if (choiceTraceOutput G x k Q (fun r => A (z,r)) (fun r => y (z,r)) a).1 = ω then
          auxiliaryTupleWeight Q (Finset.Icc 1 k) p
            (choiceTraceOutput G x k Q (fun r => A (z,r)) (fun r => y (z,r)) a) *
          choiceTraceMass G x k Q (fun r => A (z,r)) (fun r => y (z,r)) (fun s r => m s (z,r)) a else 0 := by
  unfold endpointRootMass
  rw [Fintype.sum_sigma,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single z]
  · rw [Fintype.sum_sigma]
    simp only [choiceTraceOutput,choiceTraceMass,choiceTraceInput,and_true]
    rfl
  · intro z' _ hz'
    have hh : e z' ≠ e z := fun h => hz' (he h)
    simp only [hh,and_false,ite_false,Finset.sum_const_zero]
  · intro hz
    exact (hz (Finset.mem_univ z)).elim

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

theorem amplificationRow_eq_load (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : Set E) :
    q.amplificationRow Q B x k n p ω = finiteRootLoad Q (Finset.Icc 1 k) p
      (finiteInverseLoad (q.amplificationOutput Q B x k n) (q.amplificationMass Q B x k n))
      (restrictFiniteField Q ω) := by
  change _ = finiteRootLoad Q (Finset.Icc 1 k) p
    (finiteChoiceForwardLoad G x k Q (q.allAmplificationInputs Q B x k n)
      (fun r s => allAmplificationVertices B k r s.2) (fun s r => q.allAmplificationWeight B k r s.2)) _
  have hf : (finiteChoiceForwardLoad G x k Q (q.allAmplificationInputs Q B x k n)
      (fun r s => allAmplificationVertices B k r s.2) (fun s r => q.allAmplificationWeight B k r s.2)) =
      (fun t => ∑ z : ↥B, finiteChoiceForwardLoad G x k Q (q.amplificationInputs Q B x k n z)
        (fun r _ => amplificationVertices B k z r) (q.amplificationWeight B k z) t) := by
    funext t
    exact finiteChoiceForwardLoad_prod G x k Q (q.allAmplificationInputs Q B x k n)
      (fun r s => allAmplificationVertices B k r s.2) (fun s r => q.allAmplificationWeight B k r s.2) t
  rw [hf,finiteRootLoad_sum]
  rfl

theorem amplificationEndpointMass_eq (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : FiniteField Q) (z : ↥B) :
    endpointRootMass Q (Finset.Icc 1 k) p (q.amplificationOutput Q B x k n)
      (fun a => a.1.1.val) (q.amplificationMass Q B x k n) (finiteFieldSet Q ω) z.val =
      q.amplificationMarginal Q B x k n z p (finiteFieldSet Q ω) := by
  change endpointRootMass Q (Finset.Icc 1 k) p (choiceTraceOutput G x k Q _ _)
    _ (choiceTraceMass G x k Q _ _ _) _ _ = _
  rw [endpointRootMass_choice_prod G x k Q p _ _ _ Subtype.val Subtype.val_injective z]
  unfold amplificationMarginal finiteChoiceForwardLoad
  rw [restrictFiniteField_fieldSet,finiteRootLoad_eq_sum]
  · rfl
  · intro a
    exact traceIndexOutput_mem G x k Q _ _ (q.amplificationInputs_subset Q B x k n z a.1) a.2

end LocalEndpointRule
end AllEndpointMarginal

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AmplificationIndexFacts
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

theorem amplificationOutput_mem (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (a : q.AmplificationIndex Q B x k n) :
    q.amplificationOutput Q B x k n a ∈ finiteSpliceDomain Q (Finset.Icc 1 k) :=
  traceIndexOutput_mem G x k Q _ _ (q.amplificationInputs_subset Q B x k n a.1.1 a.1.2) a.2

theorem amplificationMass_nonneg (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (a : q.AmplificationIndex Q B x k n) :
    0 ≤ q.amplificationMass Q B x k n a :=
  mul_nonneg (q.allAmplificationWeight_nonneg B k a.1 (q.amplificationInput Q B x k n a).2)
    (Finset.prod_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))

theorem amplificationIndex_trace (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (a : q.AmplificationIndex Q B x k n) :
    SpliceTrace G x (q.amplificationInput Q B x k n a).2
      (amplificationVertices B k a.1.1 a.1.2) k 0 (q.amplificationInput Q B x k n a).1
      (q.amplificationCode Q B x k n a) (q.amplificationOutput Q B x k n a).1 :=
  (traceIndex_valid G x k Q _ _ a.2).1

theorem amplificationIndex_support (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (a : q.AmplificationIndex Q B x k n) :
    x ∈ O ∧ a.1.1.val ∈ O ∧ Conn G (q.amplificationOutput Q B x k n a).1 x a.1.1.val ∧
      (cluster G (q.amplificationOutput Q B x k n a).1 x).Finite ∧
      (cluster G (q.amplificationOutput Q B x k n a).1 x).ncard ≤ 2*n+k*M :=
  q.amplificationTrace_support Q B x k n a.1.1 a.1.2 a.2.1.val a.2.1.property _ _
    (q.amplificationIndex_trace Q B x k n a)

theorem amplificationIndex_caps (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (a : q.AmplificationIndex Q B x k n)
    (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
    (cluster G ((q.amplificationInput Q B x k n a).2 i) (amplificationVertices B k a.1.1 a.1.2 i)).Finite ∧
    (cluster G ((q.amplificationInput Q B x k n a).2 i) (amplificationVertices B k a.1.1 a.1.2 i)).ncard ≤ M := by
  have hc := q.amplificationInputs_chain Q B x k n a.1.1 a.1.2 a.2.1.val a.2.1.property i hi hik
  exact ⟨hc.2.1,hc.2.2.1⟩

theorem amplificationEndpointMass_outside (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : Set E)
    (z : V) (hz : z ∉ B) :
    endpointRootMass Q (Finset.Icc 1 k) p (q.amplificationOutput Q B x k n)
      (fun a => a.1.1.val) (q.amplificationMass Q B x k n) ω z = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  split_ifs with h
  · exact (hz (h.2 ▸ a.1.1.property)).elim
  · rfl

 

theorem amplificationEndpointMass_bound (q : LocalEndpointRule G hloc O M L) (hL : 1 ≤ L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : Set E)
    (hω : ω ⊆ (Q : Set E)) (z : V) :
    endpointRootMass Q (Finset.Icc 1 k) p (q.amplificationOutput Q B x k n)
      (fun a => a.1.1.val) (q.amplificationMass Q B x k n) ω z ≤ inverseCodeMass M L ^ k := by
  by_cases hz : z ∈ B
  · let z' : ↥B := ⟨z,hz⟩
    have hfield : finiteFieldSet Q (restrictFiniteField Q ω) = ω := by
      rw [finiteFieldSet_restrict,Set.inter_eq_left.mpr hω]
    rw [← hfield,q.amplificationEndpointMass_eq Q B x k n p _ z']
    exact (q.amplificationMarginal_bounds hL Q B x k n z' p _).2
  · rw [q.amplificationEndpointMass_outside Q B x k n p ω z hz]
    apply pow_nonneg
    exact add_nonneg zero_le_one (Finset.sum_nonneg fun l _ => gapWeight_nonneg L (by linarith) l)

end LocalEndpointRule
end AmplificationIndexFacts

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NoSwitchDensity
attribute [local instance] Classical.propDecidable Classical.decEq

theorem traceIndexMass_nil (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (a : FiniteTraceIndex G x k Q A y) (hc : traceIndexCode G x k Q A y a = []) :
    traceIndexMass G x k Q A y a = 1 := by
  change a.2.val = [] at hc
  simp [traceIndexMass,hc,traceContactCount]

 

theorem finiteChoiceNilLoad_le {P : Type*} [Fintype P]
    (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (m : SpliceState E → P → ℝ) (hm : ∀ s r, 0 ≤ m s r) (t : SpliceState E) :
    finiteInverseLoad (choiceTraceOutput G x k Q A y)
      (fun a => if choiceTraceCode G x k Q A y a = [] then choiceTraceMass G x k Q A y m a else 0) t ≤
      ∑ r, if t ∈ A r then m t r else 0 := by
  let I := FiniteChoiceTraceIndex G x k Q A y
  let S : I → Prop := fun a => choiceTraceOutput G x k Q A y a = t ∧ choiceTraceCode G x k Q A y a = []
  let J := {a : I // S a}
  have hin (a : J) : choiceTraceInput G x k Q A y a.val = t := by
    have he := (traceIndex_valid G x k Q (A a.val.1) (y a.val.1) a.val.2).2
    change SpliceExecution G x (choiceTraceInput G x k Q A y a.val)
      (choiceTraceCode G x k Q A y a.val) (choiceTraceOutput G x k Q A y a.val) at he
    rw [a.property.1,a.property.2,SpliceExecution.nil_iff] at he
    exact he
  have hi : Function.Injective (fun a : J => a.val.1) := by
    intro a b hab
    apply Subtype.ext
    apply choiceTrace_injective G x k Q A y
    exact Prod.ext ((hin a).trans (hin b).symm)
      (Prod.ext hab (a.property.2.trans b.property.2.symm))
  have hm' (a : J) : choiceTraceMass G x k Q A y m a.val = m t a.val.1 := by
    unfold choiceTraceMass
    rw [hin a,traceIndexMass_nil G x k Q (A a.val.1) (y a.val.1) a.val.2 a.property.2,mul_one]
  have hA (a : J) : t ∈ A a.val.1 := (hin a) ▸ a.val.2.1.property
  have he : finiteInverseLoad (choiceTraceOutput G x k Q A y)
      (fun a => if choiceTraceCode G x k Q A y a = [] then choiceTraceMass G x k Q A y m a else 0) t =
      ∑ a : J, m t a.val.1 := by
    unfold finiteInverseLoad
    simp only [← ite_and]
    change (∑ a : I, if S a then choiceTraceMass G x k Q A y m a else 0) = _
    calc
      _ = ∑ a : J, choiceTraceMass G x k Q A y m a.val := by
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype _ (by intro a; simp) _
      _ = _ := Finset.sum_congr rfl (fun a _ => hm' a)
  rw [he]
  have hb := sum_comp_le_sum_of_injective (fun a : J => a.val.1) hi
    (fun r => if t ∈ A r then m t r else 0) (by intro r; split_ifs; exact hm t r; exact le_refl _)
  simpa only [ite_eq_left (hA _)] using hb

end NoSwitchDensity

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AllEndpointNil
attribute [local instance] Classical.propDecidable Classical.decEq

theorem oldRunArrival_integral {W : Type*} [Fintype W]
    (Q : Finset E) (p : ℝ) (k : ℕ) (q : Set E → W → W → ℝ) (z : W) (A : Finset W) :
    finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => oldRunArrival (fun i => q (η i)) k z A) =
      oldRunArrival (fun _ => finiteOldKernel Q p q) k z A := by
  unfold oldRunArrival
  rw [finiteFamilyIntegral_sum]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : oldRunVertices k z r 0 ∈ A
  · simp only [ite_eq_left h]
    exact oldRunWeight_integral Q p k q z r
  · simp [h,finiteFamilyIntegral]

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}



theorem amplificationNilRow_arrival_le (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : FiniteField Q) :
    q.amplificationNilRow Q B x k n p ω ≤
      if n ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧ (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then
        ∑ z : ↥B, oldRunArrival (fun _ => finiteOldKernel Q p (fun η (a b : ↥B) => q.mass η a.val b.val)) k z
          (Finset.univ.filter fun a : ↥B => a.val ∈ cluster G (finiteFieldSet Q ω) x) else 0 := by
  let A : Finset ↥B := Finset.univ.filter fun a : ↥B => a.val ∈ cluster G (finiteFieldSet Q ω) x
  let H := n ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧ (cluster G (finiteFieldSet Q ω) x).ncard < 2*n
  have hb (η : ℕ → Set E) :
      finiteInverseLoad (q.amplificationOutput Q B x k n)
        (fun a => if q.amplificationCode Q B x k n a = [] then q.amplificationMass Q B x k n a else 0)
        (finiteFieldSet Q ω,η) ≤
      if H then ∑ z : ↥B, oldRunArrival (fun i (a b : ↥B) => q.mass (η i) a.val b.val) k z A else 0 := by
    apply (finiteChoiceNilLoad_le G x k Q (q.allAmplificationInputs Q B x k n)
      (fun r s => allAmplificationVertices B k r s.2)
      (fun s r => q.allAmplificationWeight B k r s.2)
      (fun s r => q.allAmplificationWeight_nonneg B k r s.2) (finiteFieldSet Q ω,η)).trans
    rw [Fintype.sum_prod_type]
    by_cases h : H
    · rw [ite_eq_left h]
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro r _
      by_cases hs : (finiteFieldSet Q ω,η) ∈ q.allAmplificationInputs Q B x k n (z,r)
      · rw [ite_eq_left hs]
        have hi := (q.mem_amplificationInputs Q B x k n z r _).mp hs
        have ha : oldRunVertices k z r 0 ∈ A := by
          simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and,amplificationVertices] using hi.2.2.2.2.2.1
        rw [ite_eq_left ha]
        exact le_rfl
      · rw [ite_eq_right hs]
        split_ifs
        · exact oldRunWeight_nonneg _ (fun i a b => q.nonneg (η i) a.val b.val) k z r
        · exact le_refl _
    · rw [ite_eq_right h]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro z _
      apply Finset.sum_eq_zero
      intro r _
      rw [ite_eq_right (by
        intro hs
        have hi := (q.mem_amplificationInputs Q B x k n z r _).mp hs
        exact h ⟨hi.2.2.2.1,hi.2.2.2.2.1⟩)]
  change _ ≤ if H then ∑ z : ↥B,
    oldRunArrival (fun _ => finiteOldKernel Q p (fun η (a b : ↥B) => q.mass η a.val b.val)) k z A else 0
  calc
    _ ≤ finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => if H then
        ∑ z : ↥B, oldRunArrival (fun i (a b : ↥B) => q.mass (η i) a.val b.val) k z A else 0) := by
      apply Finset.sum_le_sum
      intro η _
      exact mul_le_mul_of_nonneg_left (hb _) (finiteFamilyWeight_nonneg Q (Finset.Icc 1 k) p η)
    _ = _ := by
      by_cases h : H
      · simp only [ite_eq_left h,finiteFamilyIntegral_sum]
        apply Finset.sum_congr rfl
        intro z _
        exact oldRunArrival_integral Q p k (fun η (a b : ↥B) => q.mass η a.val b.val) z A
      · simp only [ite_eq_right h,finiteFamilyIntegral,mul_zero,Finset.sum_const_zero]

end LocalEndpointRule
end AllEndpointNil

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section AllEndpointNilBound
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}



theorem amplificationNilRow_bound {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
    (hw : ∀ i, 0 ≤ weight i) (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : FiniteField Q)
    (hQ : ∀ a ∈ B, incidentSupport G hloc (finite_reachBall hloc a q.radius).toFinset ⊆ Q) :
    q.amplificationNilRow Q B x k n p ω ≤ ((2*n:ℕ):ℝ) * q.successProbability p (root i₀)^k := by
  apply (q.amplificationNilRow_arrival_le Q B x k n p ω).trans
  split_ifs with h
  · let A : Finset ↥B := Finset.univ.filter fun a : ↥B => a.val ∈ cluster G (finiteFieldSet Q ω) x
    let K := fun (_ : ℕ) => finiteOldKernel Q p (fun η (a b : ↥B) => q.mass η a.val b.val)
    have hK (i : ℕ) (a b : ↥B) : K i a b = q.kernel p a.val b.val :=
      q.finiteOldKernel_eq_kernel Q p a.val b.val (hQ a.val a.property)
    have hnK (i : ℕ) (a b : ↥B) : 0 ≤ K i a b := by rw [hK i a b]; exact q.kernel_nonneg p a.val b.val
    have hc (i : ℕ) (b : ↥B) : (∑ a, K i a b) ≤ q.successProbability p (root i₀) := by
      simp only [hK]
      rw [Finset.sum_coe_sort B (fun a => q.kernel p a b.val)]
      exact ((q.summable_kernel_column p b.val).sum_le_tsum B (fun a _ => q.kernel_nonneg p a b.val)).trans
        (q.kernel_column_le_success root weight Γ htr hΓ hw i₀ hw₀ p b.val)
    have hf : (cluster G (finiteFieldSet Q ω) x).Finite := cluster_finite_of_finite_edges G
      ω.val.finite_toSet x
    have hcard : A.card ≤ 2*n := by
      have hh : A.card ≤ hf.toFinset.card := Finset.card_le_card_of_injOn Subtype.val
        (by intro a ha; exact hf.mem_toFinset.mpr (Finset.mem_filter.mp ha).2)
        (fun _ _ _ _ he => Subtype.val_injective he)
      rw [← Set.ncard_eq_toFinset_card (cluster G (finiteFieldSet Q ω) x) hf] at hh
      exact hh.trans h.2.le
    calc
      _ ≤ (A.card:ℝ) * q.successProbability p (root i₀)^k :=
        sum_oldRunArrival_le K hnK _ (q.successProbability_nonneg p (root i₀)) hc k A
      _ ≤ ((2*n:ℕ):ℝ) * q.successProbability p (root i₀)^k :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg (q.successProbability_nonneg p (root i₀)) _)
  · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (q.successProbability_nonneg p (root i₀)) _)

end LocalEndpointRule
end AllEndpointNilBound

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section AllEndpointNear
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}



theorem amplificationNearPairMass_bound [Nonempty E]
    (q : LocalEndpointRule G hloc O M L) (hL : 1 ≤ L)
    (Q : Finset E) (B : Finset V) (x : V) (k n d : ℕ) (p : unitInterval)
    (hdeg : ∀ a, degree G a ≤ d) :
    q.amplificationNearPairMass Q B x k n p ≤
      (((k*M)+(k*M)^2+d*(k*M)^3:ℕ):ℝ) * inverseCodeMass M L ^ k *
        ∑ a : q.AmplificationIndex Q B x k n,
          spliceTupleWeight Q (Finset.Icc 1 k) p (q.amplificationOutput Q B x k n a) *
            q.amplificationMass Q B x k n a := by
  let out := q.amplificationOutput Q B x k n
  let code := q.amplificationCode Q B x k n
  let added := q.amplificationAdded Q B x k n
  let m := q.amplificationMass Q B x k n
  let e (a : q.AmplificationIndex Q B x k n) := (code a).headD (0,Classical.choice ‹Nonempty E›) |>.2
  have hfin (a : q.AmplificationIndex Q B x k n) : (cluster G (out a).1 x).Finite :=
    (q.amplificationIndex_support Q B x k n a).2.2.2.1
  have hhead (a : q.AmplificationIndex Q B x k n) (hc : code a ≠ []) :
      OpenMarkedPivotal G (out a).1 {a.1.1.val} x (e a) ∧
      hangingSide G (out a).1 x (e a) = added a ∧
      (hangingSide G (out a).1 x (e a)).ncard ≤ k*M := by
    cases hh : code a with
    | nil => exact (hc hh).elim
    | cons w rest =>
      have ht := q.amplificationIndex_trace Q B x k n a
      change SpliceTrace G x (q.amplificationInput Q B x k n a).2
        (amplificationVertices B k a.1.1 a.1.2) k 0 (q.amplificationInput Q B x k n a).1
        (code a) (out a).1 at ht
      rw [hh] at ht
      have he : e a = w.2 := by simp only [e,hh,List.headD_cons]
      rw [he]
      refine ⟨?_,ht.head_hanging G x _ _ k 0 w.1 _ _ w.2 rest,
        ht.head_hanging_cap G x _ _ k 0 w.1 M _ _ w.2 rest (q.amplificationIndex_caps Q B x k n a)⟩
      simpa only [amplificationVertices,oldRunVertices_last] using
        ht.seams_pivotal G x _ _ k 0 _ _ (w::rest) w (List.mem_cons_self)
  let S (a : q.AmplificationIndex Q B x k n) : Finset V := if code a = [] then ∅ else
    nearHangingEndpoints G hloc (out a).1 x a.1.1.val (e a) (k*M) (hfin a)
  let R (a b : q.AmplificationIndex Q B x k n) := code a ≠ [] ∧ code b ≠ [] ∧
    ¬GraphSeparated G (added a) (added b)
  have hS (a b : q.AmplificationIndex Q B x k n) (he : (out a).1 = (out b).1) (h : R a b) :
      b.1.1.val ∈ S a := by
    obtain ⟨hpa,hea,_⟩ := hhead a h.1
    obtain ⟨hpb,heb,hcb⟩ := hhead b h.2.1
    have hn := h.2.2
    rw [← hea,← heb,← he] at hn
    rw [← he] at hpb hcb
    simp only [S,ite_eq_right h.1]
    exact mem_nearHangingEndpoints_of_not_separated G hloc (out a).1 x a.1.1.val b.1.1.val
      (e a) (e b) (k*M) (hfin a) hpa hpb hcb hn
  have hN (a : q.AmplificationIndex Q B x k n) : (S a).card ≤ (k*M)+(k*M)^2+d*(k*M)^3 := by
    by_cases h : code a = []
    · simp only [S,ite_eq_left h,Finset.card_empty,Nat.zero_le]
    · simp only [S,ite_eq_right h]
      exact nearHangingEndpoints_card_le G hloc (out a).1 x a.1.1.val (e a) (k*M) d
        (hfin a) (hhead a h).2.2 hdeg
  have hC : 0 ≤ inverseCodeMass M L ^ k := pow_nonneg
    (add_nonneg zero_le_one (Finset.sum_nonneg fun l _ => gapWeight_nonneg L (by linarith) l)) _
  simpa only [amplificationNearPairMass,out,m,R,added] using finite_near_pair_mass_le Q (Finset.Icc 1 k) (Finset.Icc 1 k) p out out m m
    (q.amplificationMass_nonneg Q B x k n) (q.amplificationMass_nonneg Q B x k n)
    (fun a => a.1.1.val) R S hS ((k*M)+(k*M)^2+d*(k*M)^3) hN _ hC
    (fun a z _ => q.amplificationEndpointMass_bound hL Q B x k n p (out a).1
      ((mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) (out a)).mp (q.amplificationOutput_mem Q B x k n a)).1 z)

end LocalEndpointRule
end AllEndpointNear

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteThreeClass
attribute [local instance] Classical.propDecidable Classical.decEq



theorem finiteRootLoad_three_classes_le {I : Type*} [Fintype I]
    (Q : Finset E) (J : Finset ℕ) (p : unitInterval) (out : I → SpliceState E)
    (m : I → ℝ) (hm : ∀ a, 0 ≤ m a) (hs : ∀ a, out a ∈ finiteSpliceDomain Q J)
    (C : I → Prop) (R : I → I → Prop) :
    (∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      finiteRootLoad Q J p (finiteInverseLoad out m) ω ^ 2) ≤
      2 * (∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
        finiteRootLoad Q J p (finiteInverseLoad out (fun a => if C a then m a else 0)) ω *
        finiteRootLoad Q J p (finiteInverseLoad out m) ω) +
      commonRootPairMass Q J p out m (fun a b => ¬C a ∧ ¬C b ∧ R a b) +
      commonRootPairMass Q J p out m (fun a b => ¬C a ∧ ¬C b ∧ ¬R a b) := by
  let m₀ := fun a => if C a then m a else 0
  let row := finiteRootLoad Q J p (finiteInverseLoad out m)
  let nilrow := finiteRootLoad Q J p (finiteInverseLoad out m₀)
  have hcross : (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * row ω * nilrow ω) =
      ∑ ω : FiniteField Q, finiteFieldWeight Q p ω * nilrow ω * row ω := by
    apply Finset.sum_congr rfl
    intro ω _
    ring
  have heq : 2 * (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * nilrow ω * row ω) =
      (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * nilrow ω * row ω) +
      (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * row ω * nilrow ω) := by
    rw [hcross]; ring
  change _ ≤ 2 * (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * nilrow ω * row ω) + _ + _
  rw [heq]
  dsimp only [nilrow,row]
  simp only [pow_two,← mul_assoc]
  rw [finiteRootLoad_pair_expansion Q J J p out out m m hs hs,
    finiteRootLoad_pair_expansion Q J J p out out m₀ m hs hs,
    finiteRootLoad_pair_expansion Q J J p out out m m₀ hs hs]
  unfold commonRootPairMass
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  have hw : 0 ≤ jointTupleWeight Q J J p (pairSpliceOutput (out a) (out b)) :=
    jointTupleWeight_nonneg Q J J p _
  have ht : 0 ≤ jointTupleWeight Q J J p (pairSpliceOutput (out a) (out b)) * m a * m b :=
    mul_nonneg (mul_nonneg hw (hm a)) (hm b)
  dsimp only [m₀]
  by_cases hab : (out a).1 = (out b).1
  · simp only [hab,true_and,ite_true]
    by_cases ha : C a <;> by_cases hb : C b <;> by_cases hr : R a b <;>
      simp only [ha,hb,hr,not_true_eq_false,not_false_eq_true,and_true,and_false,
        ite_true,ite_false,mul_zero,zero_mul] <;> linarith
  · simp only [hab,false_and,ite_false,zero_add,le_refl]

end FiniteThreeClass

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section AllEndpointMomentIdentities
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteRootLoad_inverse_mean {I : Type*} [Fintype I]
    (Q : Finset E) (J : Finset ℕ) (p : ℝ) (out : I → SpliceState E) (m : I → ℝ)
    (hs : ∀ a, out a ∈ finiteSpliceDomain Q J) :
    (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * finiteRootLoad Q J p (finiteInverseLoad out m) ω) =
      ∑ a, spliceTupleWeight Q J p (out a) * m a := by
  rw [finiteRootLoad_mean]
  simp only [finiteInverseLoad,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_ite_eq,ite_eq_left (hs a)]

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

theorem amplificationRow_nonneg (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : Set E) :
    0 ≤ q.amplificationRow Q B x k n p ω := by
  rw [q.amplificationRow_eq_load]
  apply finiteRootLoad_nonneg
  intro s _
  exact finiteInverseLoad_nonneg _ _ (q.amplificationMass_nonneg Q B x k n) s

theorem amplificationRow_mean_eq (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) :
    finiteFieldIntegral Q p (q.amplificationRow Q B x k n p) =
      ∑ a : q.AmplificationIndex Q B x k n,
        spliceTupleWeight Q (Finset.Icc 1 k) p (q.amplificationOutput Q B x k n a) *
          q.amplificationMass Q B x k n a := by
  simp only [finiteFieldIntegral,q.amplificationRow_eq_load,restrictFiniteField_fieldSet]
  exact finiteRootLoad_inverse_mean Q (Finset.Icc 1 k) p _ _ (q.amplificationOutput_mem Q B x k n)

 

theorem amplificationSeparated_class_eq (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) :
    commonRootPairMass Q (Finset.Icc 1 k) p (q.amplificationOutput Q B x k n)
      (q.amplificationMass Q B x k n) (fun a b =>
        q.amplificationCode Q B x k n a ≠ [] ∧ q.amplificationCode Q B x k n b ≠ [] ∧
        GraphSeparated G (q.amplificationAdded Q B x k n a) (q.amplificationAdded Q B x k n b)) =
    finiteChoiceSeparatedPairMass G x k Q p
      (q.allAmplificationInputs Q B x k n) (q.allAmplificationInputs Q B x k n)
      (allAmplificationVertices B k) (allAmplificationVertices B k)
      (q.allAmplificationWeight B k) (q.allAmplificationWeight B k) := by
  unfold commonRootPairMass finiteChoiceSeparatedPairMass
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs with ha hb hb
  · rfl
  · exfalso
    apply hb
    dsimp only [amplificationAdded,amplificationOutput,amplificationCode,amplificationInput] at ha
    rcases ha with ⟨he,hca,hcb,hsep⟩
    refine ⟨he,hca,hcb,?_⟩
    simpa only [he] using hsep
  · exfalso
    apply ha
    dsimp only [amplificationAdded,amplificationOutput,amplificationCode,amplificationInput]
    rcases hb with ⟨he,hca,hcb,hsep⟩
    refine ⟨he,hca,hcb,?_⟩
    simpa only [he] using hsep
  · rfl

end LocalEndpointRule
end AllEndpointMomentIdentities

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section AllEndpointSecondMoment
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem amplificationRow_second_moment_le [Nonempty E] (hconn : Connected G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
    (Q : Finset E) (B : Finset V) (p : unitInterval) (x : V) (k n d : ℕ)
    (hdeg : ∀ a, degree G a ≤ d)
    (hQ : ∀ a ∈ B, incidentSupport G hloc (finite_reachBall hloc a (max q.radius M)).toFinset ⊆ Q) :
    finiteFieldIntegral Q p (fun ω => q.amplificationRow Q B x k n p ω ^ 2) ≤
      (((4*n:ℕ):ℝ) * q.successProbability p (root i₀)^k +
        (((k*M)+(k*M)^2+d*(k*M)^3:ℕ):ℝ) * inverseCodeMass M L ^ k) *
          finiteFieldIntegral Q p (q.amplificationRow Q B x k n p) +
      (((2*n:ℕ):ℝ) * (c*((k*M:ℕ)*q.successProbability p (root i₀)^k)))^2 *
        finiteClusterWindowMass G Q p x (n-k*M) (2*n) := by
  let out := q.amplificationOutput Q B x k n
  let m := q.amplificationMass Q B x k n
  let C := fun a => q.amplificationCode Q B x k n a = []
  let R := fun a b => ¬GraphSeparated G (q.amplificationAdded Q B x k n a) (q.amplificationAdded Q B x k n b)
  let row := finiteRootLoad Q (Finset.Icc 1 k) p (finiteInverseLoad out m)
  let nilrow := q.amplificationNilRow Q B x k n p
  let b₀ := ∑ ω : FiniteField Q, finiteFieldWeight Q p ω * row ω
  let bnil := ∑ ω : FiniteField Q, finiteFieldWeight Q p ω * nilrow ω * row ω
  let S := finiteChoiceSeparatedPairMass G x k Q p
    (q.allAmplificationInputs Q B x k n) (q.allAmplificationInputs Q B x k n)
    (allAmplificationVertices B k) (allAmplificationVertices B k)
    (q.allAmplificationWeight B k) (q.allAmplificationWeight B k)
  have hrow (ω : FiniteField Q) : q.amplificationRow Q B x k n p (finiteFieldSet Q ω) = row ω := by
    rw [q.amplificationRow_eq_load,restrictFiniteField_fieldSet]
  have hmean : finiteFieldIntegral Q p (q.amplificationRow Q B x k n p) = b₀ := by
    simp only [finiteFieldIntegral,hrow,b₀]
  have hpart := finiteRootLoad_three_classes_le Q (Finset.Icc 1 k) p out m
    (q.amplificationMass_nonneg Q B x k n) (q.amplificationOutput_mem Q B x k n) C R
  have hnear_eq : commonRootPairMass Q (Finset.Icc 1 k) p out m
      (fun a b => ¬C a ∧ ¬C b ∧ R a b) = q.amplificationNearPairMass Q B x k n p := by
    simp only [commonRootPairMass,amplificationNearPairMass,C,R,out,m]
  have hsep_eq : commonRootPairMass Q (Finset.Icc 1 k) p out m
      (fun a b => ¬C a ∧ ¬C b ∧ ¬R a b) = S := by
    simpa only [C,R,not_not] using q.amplificationSeparated_class_eq Q B x k n p
  rw [hnear_eq,hsep_eq] at hpart
  have hnilfun : finiteInverseLoad out (fun a => @ite ℝ (C a) (Classical.propDecidable _) (m a) 0) =
      finiteInverseLoad (q.amplificationOutput Q B x k n)
        (fun a => if q.amplificationCode Q B x k n a = [] then q.amplificationMass Q B x k n a else 0) := by
    apply congrArg (finiteInverseLoad out)
    funext a
    dsimp only [C,m]
    split_ifs <;> rfl
  rw [hnilfun] at hpart
  change (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * row ω ^ 2) ≤
    2*bnil + q.amplificationNearPairMass Q B x k n p + S at hpart
  have hnil : bnil ≤ ((2*n:ℕ):ℝ) * q.successProbability p (root i₀)^k * b₀ := by
    dsimp only [bnil,b₀]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ω _
    have hr : 0 ≤ row ω := by rw [← hrow]; exact q.amplificationRow_nonneg Q B x k n p _
    have hn := q.amplificationNilRow_bound root weight Γ htr (fun a ha => hΓ ha) hw i₀ hw₀ Q B x k n p ω
      (fun a ha => (incidentSupport_ball_mono G hloc a (le_max_left _ _)).trans (hQ a ha))
    calc
      _ ≤ finiteFieldWeight Q p ω * (((2*n:ℕ):ℝ) * q.successProbability p (root i₀)^k) * row ω :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (finiteFieldWeight_nonneg Q p ω)) hr
      _ = _ := by ring
  have hnear := q.amplificationNearPairMass_bound hL Q B x k n d p hdeg
  rw [← q.amplificationRow_mean_eq Q B x k n p,hmean] at hnear
  have hsep := q.amplificationSeparatedSecondMoment_le hconn root weight Γ hΓ htr hcov hw hw1 c hc hmin
    (root i₀) Q B p x k n hQ
  have hfinal := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hnil (show (0:ℝ) ≤ 2 by norm_num)) hnear) hsep
  rw [hmean]
  simp only [finiteFieldIntegral,hrow]
  apply hpart.trans
  convert hfinal using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

end LocalEndpointRule
end AllEndpointSecondMoment

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Covariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariance for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section CanonicalAmplificationRow
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem amplificationBonds_query {O : Set V} (q : LocalEndpointRule G hloc O M L)
    (k n : ℕ) (x a : V) (ha : a ∈ q.amplificationBall k n x) :
    incidentSupport G hloc (finite_reachBall hloc a (max q.radius M)).toFinset ⊆
      q.amplificationBonds k n x := by
  apply incidentSupport_mono
  intro y hy
  simp only [Set.Finite.mem_toFinset] at hy ⊢
  exact reachBall_triangle G x a (2*n+k*M) (max q.radius M)
    (by simpa only [amplificationBall,Set.Finite.mem_toFinset] using ha) hy

theorem amplificationBonds_root {O : Set V} (q : LocalEndpointRule G hloc O M L)
    (k n : ℕ) (x : V) :
    incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset ⊆
      q.amplificationBonds k n x := by
  apply incidentSupport_ball_mono
  unfold amplificationRadius
  omega

theorem amplificationLoad_row (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (hL : 1 ≤ L) (k n : ℕ) (p : unitInterval) (ω : Set E) (x : V) :
    (q.amplificationLoad o hL k n p).row ω x =
      q.amplificationRow (q.amplificationBonds k n x) (q.amplificationBall k n x) x k n p ω / n := by
  change (∑' z, q.amplifiedMass k n p ω x z) = _
  rw [tsum_eq_sum (s := q.amplificationBall k n x) (fun z hz => by
    simp only [amplifiedMass,dite_eq_right hz])]
  rw [← Finset.sum_coe_sort]
  simp only [amplifiedMass,dite_eq_left (Subtype.prop _)]
  exact (Finset.sum_div _ _ _).symm

theorem amplificationRow_local {O : Set V} (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : Set E) :
    q.amplificationRow Q B x k n p ω = q.amplificationRow Q B x k n p (ω ∩ (Q : Set E)) := by
  unfold amplificationRow
  apply Finset.sum_congr rfl
  intro z _
  exact q.amplificationMarginal_local Q B x k n z p ω

theorem amplificationLoad_mean_finite (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (hL : 1 ≤ L) (k n : ℕ) (p : unitInterval) (x : V) :
    (∫ ω, (q.amplificationLoad o hL k n p).row ω x ∂law p) =
      finiteFieldIntegral (q.amplificationBonds k n x) p
        (q.amplificationRow (q.amplificationBonds k n x) (q.amplificationBall k n x) x k n p) / n := by
  simp_rw [q.amplificationLoad_row o hL k n p]
  rw [integral_div]
  congr 1
  exact integral_finite_local _ p _ (q.amplificationRow_local _ _ x k n p)

theorem amplificationLoad_second_moment_finite (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (hL : 1 ≤ L) (k n : ℕ) (p : unitInterval) (x : V) :
    (∫ ω, (q.amplificationLoad o hL k n p).row ω x ^ 2 ∂law p) =
      finiteFieldIntegral (q.amplificationBonds k n x) p (fun ω =>
        q.amplificationRow (q.amplificationBonds k n x) (q.amplificationBall k n x) x k n p ω ^ 2) / (n:ℝ)^2 := by
  simp_rw [q.amplificationLoad_row o hL k n p,div_pow]
  rw [integral_div]
  congr 1
  exact integral_finite_local _ p _ (fun ω => congrArg (·^2) (q.amplificationRow_local _ _ x k n p ω))

end LocalEndpointRule
end CanonicalAmplificationRow

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section NormalizedAmplificationMoment
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem amplificationLoad_second_moment_le [Nonempty E] (hconn : Connected G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
    (p : unitInterval) (x : V) (k n d : ℕ) (hn : 0 < n)
    (hdeg : ∀ a, degree G a ≤ d) :
    (∫ ω, (q.amplificationLoad (root i₀) hL k n p).row ω x ^ 2 ∂law p) ≤
      (4 * q.successProbability p (root i₀)^k +
        (((k*M)+(k*M)^2+d*(k*M)^3:ℕ):ℝ) * inverseCodeMass M L^k / n) *
          (∫ ω, (q.amplificationLoad (root i₀) hL k n p).row ω x ∂law p) +
      (2 * (c*((k*M:ℕ)*q.successProbability p (root i₀)^k)))^2 *
        finiteClusterWindowMass G (q.amplificationBonds k n x) p x (n-k*M) (2*n) := by
  rw [q.amplificationLoad_second_moment_finite,q.amplificationLoad_mean_finite]
  have h := q.amplificationRow_second_moment_le hconn root weight Γ hΓ htr hcov hw hw1 c hc hmin
    i₀ hw₀ hL (q.amplificationBonds k n x) (q.amplificationBall k n x) p x k n d hdeg
    (fun a ha => q.amplificationBonds_query k n x a ha)
  have hn' : (n:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  apply (div_le_div_of_nonneg_right h (sq_nonneg (n:ℝ))).trans_eq
  push_cast
  field_simp

end LocalEndpointRule
end NormalizedAmplificationMoment

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FinitePathExhaustion
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finitePathTest_succ (B : Finset V) (K : V → V → ℝ) (F : V → ℝ) (k : ℕ) (z : ↥B) :
    finitePathTest B K F (k+1) z = ∑ a : ↥B, K z.val a.val * finitePathTest B K F k a :=
  oldRun_test_succ (fun _ (a b : ↥B) => K a.val b.val) (fun (a : ↥B) => F a.val) k z

 

theorem finitePathTest_support (G : BondGraph V E) (B : Finset V) (K : V → V → ℝ) (F : V → ℝ)
    (O : Set V) (x : V) (R M : ℕ)
    (hK : ∀ a b, K a b ≠ 0 → a ∈ O ∧ a ∈ reachBall G b M)
    (hF : ∀ a, F a ≠ 0 → a ∈ O ∧ a ∈ reachBall G x R)
    (k : ℕ) (z : ↥B) (hz : finitePathTest B K F k z ≠ 0) :
    z.val ∈ O ∧ z.val ∈ reachBall G x (R+k*M) := by
  induction k generalizing z with
  | zero => simpa using hF z.val (by simpa using hz)
  | succ k ih =>
    rw [finitePathTest_succ] at hz
    obtain ⟨a,_,ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
    have hh := mul_ne_zero_iff.mp ha
    obtain ⟨haO,haB⟩ := ih a hh.2
    obtain ⟨hzO,hzB⟩ := hK z.val a.val hh.1
    refine ⟨hzO,?_⟩
    have hg := reachBall_triangle G x a.val (R+k*M) M haB hzB
    simpa only [Nat.add_mul,one_mul,Nat.add_assoc] using hg

 

theorem finitePathTest_total (G : BondGraph V E) (B : Finset V) (K : V → V → ℝ) (F : V → ℝ)
    (O : Set V) (x : V) (R M N : ℕ) (u : ℝ)
    (hK : ∀ a b, K a b ≠ 0 → a ∈ O ∧ a ∈ reachBall G b M)
    (hF : ∀ a, F a ≠ 0 → a ∈ O ∧ a ∈ reachBall G x R)
    (hcolumn : ∀ j < N, ∀ a : ↥B, a.val ∈ O → a.val ∈ reachBall G x (R+j*M) →
      ∑ z : ↥B, K z.val a.val = u) :
    ∀ j ≤ N, (∑ z : ↥B, finitePathTest B K F j z) = u^j * ∑ z : ↥B, F z.val := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    simp_rw [finitePathTest_succ]
    rw [Finset.sum_comm]
    have he : (∑ a : ↥B, ∑ z : ↥B, K z.val a.val * finitePathTest B K F j a) =
        u * ∑ a : ↥B, finitePathTest B K F j a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_mul]
      by_cases ha : finitePathTest B K F j a = 0
      · simp only [ha,mul_zero]
      · obtain ⟨haO,haB⟩ := finitePathTest_support G B K F O x R M hK hF j a ha
        rw [hcolumn j (by omega) a haO haB]
    rw [he,ih (by omega)]
    ring

end FinitePathExhaustion

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section AmplificationBoundaryExhaustion
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem kernel_range_support {O : Set V} (q : LocalEndpointRule G hloc O M L)
    (p : unitInterval) (a b : V) (h : q.kernel p a b ≠ 0) : a ∈ O ∧ a ∈ reachBall G b M := by
  constructor
  · by_contra ha
    exact h (q.kernel_zero_of_start_not_mem p a b ha)
  · by_contra ha
    exact h (q.kernel_outside_reverse_ball_zero p a b ha)

theorem orbitBinConnection_range_support (o : V) (p : unitInterval) (n : ℕ) (x a : V)
    (h : orbitBinConnection G p o n x a ≠ 0) :
    a ∈ vertexOrbit G o ∧ a ∈ reachBall G x (2*n) := by
  have ha : a ∈ vertexOrbit G o := by
    by_contra ha
    exact h (by simp only [orbitBinConnection,ha,and_false,ite_false])
  refine ⟨ha,?_⟩
  by_contra hb
  exact h (by simp only [orbitBinConnection,binConnection_outside G p n x a hb,ite_self])

theorem amplificationBall_column {O : Set V} (q : LocalEndpointRule G hloc O M L)
    (p : unitInterval) (k n j : ℕ) (hj : j < k) (x a : V)
    (ha : a ∈ reachBall G x (2*n+j*M)) :
    (∑ z : ↥(q.amplificationBall k n x), q.kernel p z.val a) = ∑' z, q.kernel p z a := by
  rw [Finset.sum_coe_sort (q.amplificationBall k n x) (fun z => q.kernel p z a)]
  symm
  apply tsum_eq_sum
  intro z hz
  apply q.kernel_outside_reverse_ball_zero
  intro hza
  have hh := reachBall_triangle G x a (2*n+j*M) M ha hza
  have hle : (2*n+j*M)+M ≤ 2*n+k*M := by
    calc
      _ = 2*n+(j+1)*M := by ring
      _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right M (by omega)) _
  exact hz (by
    simpa only [amplificationBall,Set.Finite.mem_toFinset] using (reachBall_mono G x hle hh))

theorem amplificationPath_total {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L)
    (p : unitInterval) (k n : ℕ) (x : V) (hx : x ∈ vertexOrbit G (root i₀)) :
    (∑ z : ↥(q.amplificationBall k n x),
      finitePathTest (q.amplificationBall k n x) (q.kernel p) (orbitBinConnection G p (root i₀) n x) k z) =
      q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n := by
  have ht := finitePathTest_total G (q.amplificationBall k n x) (q.kernel p)
    (orbitBinConnection G p (root i₀) n x) (vertexOrbit G (root i₀)) x (2*n) M k
    (q.successProbability p (root i₀)) (q.kernel_range_support p)
    (orbitBinConnection_range_support (root i₀) p n x) (by
      intro j hj a haO haB
      rw [q.amplificationBall_column p k n j hj x a.val haB]
      exact q.kernel_column_eq_success root weight Γ htr hΓ hw i₀ hw₀ p a.val haO) k le_rfl
  rw [ht]
  congr 1
  rw [Finset.sum_coe_sort (q.amplificationBall k n x) (orbitBinConnection G p (root i₀) n x),← orbitBinConnection_row G hloc p (root i₀) n x hx]
  symm
  apply tsum_eq_sum
  intro z hz
  by_contra h
  have hb := (orbitBinConnection_range_support (root i₀) p n x z h).2
  exact hz (by
    simpa only [amplificationBall,Set.Finite.mem_toFinset] using
      reachBall_mono G x (Nat.le_add_right (2*n) (k*M)) hb)

end LocalEndpointRule
end AmplificationBoundaryExhaustion

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section AmplificationExactMean
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem amplificationMarginal_mean_pathTest [Nonempty E] (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval)
    (hx : x ∈ vertexOrbit G o)
    (hroot : incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset ⊆ Q)
    (hquery : ∀ a ∈ B, incidentSupport G hloc (finite_reachBall hloc a q.radius).toFinset ⊆ Q) :
    (∫ ω, q.amplificationMarginal Q B x k n z p ω ∂law p) =
      finitePathTest B (q.kernel p) (orbitBinConnection G p o n x) k z := by
  by_cases hz : z.val ∈ vertexOrbit G o
  · rw [q.amplificationMarginal_mean_kernel Q B x k n z p hx hz hquery]
    unfold finitePathTest
    apply Finset.sum_congr rfl
    intro r _
    rw [finiteBinConnection_eq_binConnection G hloc Q p x n _ hroot]
    by_cases hr : oldRunWeight (fun _ (a b : ↥B) => q.kernel p a.val b.val) k z r = 0
    · simp only [hr,mul_zero,zero_mul]
    · have hy : (oldRunVertices k z r 0).val ∈ vertexOrbit G o :=
        oldRun_endpoint_mem (fun a : ↥B => a.val ∈ vertexOrbit G o)
          (fun _ (a b : ↥B) => q.kernel p a.val b.val)
          (fun _ a b hab => by
            by_contra hb
            exact hab (q.kernel_zero_of_end_not_mem p a.val b.val hb)) k z hz r hr
      rw [orbitBinConnection,ite_eq_left ⟨hx,hy⟩]
      exact mul_comm _ _
  · have hm (ω : Set E) : q.amplificationMarginal Q B x k n z p ω = 0 := by
      by_contra h
      exact hz (q.amplificationMarginal_support Q B x k n z p ω h).2.1
    simp_rw [hm,integral_zero]
    symm
    by_contra h
    exact hz (finitePathTest_support G B (q.kernel p) (orbitBinConnection G p o n x)
      (vertexOrbit G o) x (2*n) M (q.kernel_range_support p)
      (orbitBinConnection_range_support o p n x) k z h).1

 

theorem amplificationLoad_mean [Nonempty E] {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
    (p : unitInterval) (k n : ℕ) (x : V) (hx : x ∈ vertexOrbit G (root i₀)) :
    (∫ ω, (q.amplificationLoad (root i₀) hL k n p).row ω x ∂law p) =
      q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n / n := by
  simp_rw [q.amplificationLoad_row]
  rw [integral_div]
  congr 1
  unfold amplificationRow
  rw [integral_finsetSum _ (fun z _ => integrable_finite_local _ p _
    (q.amplificationMarginal_local _ _ x k n z p))]
  simp_rw [q.amplificationMarginal_mean_pathTest (root i₀) _ _ x k n _ p hx
    (q.amplificationBonds_root k n x) (fun a ha =>
      (incidentSupport_ball_mono G hloc a (le_max_left _ _)).trans (q.amplificationBonds_query k n x a ha))]
  exact q.amplificationPath_total root weight Γ htr hΓ hw i₀ hw₀ p k n x hx

end LocalEndpointRule
end AmplificationExactMean

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section AmplificationLoadOperator
attribute [local instance] Classical.propDecidable Classical.decEq
namespace CappedLocalLoad
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ}

theorem kernel_nonneg (q : CappedLocalLoad G hloc O M) (p : unitInterval) (x y : V) :
    0 ≤ q.kernel p x y := integral_nonneg (q.nonneg · x y)

end CappedLocalLoad

 
theorem exists_operator_of_scaled_matrix (F : V → V → ℝ) (c C : ℝ) (hc : 0 < c)
    (A : Hilbert V →L[ℂ] Hilbert V) (hAnorm : ‖A‖ ≤ C)
    (hA : ∀ x y, matrixCoeff A x y = (c * F x y : ℂ)) :
    ∃ T : Hilbert V →L[ℂ] Hilbert V, ‖T‖ ≤ C/c ∧
      ∀ x y, matrixCoeff T x y = (F x y : ℂ) := by
  refine ⟨((c⁻¹:ℝ):ℂ) • A,?_,?_⟩
  · rw [norm_smul,Complex.norm_of_nonneg (inv_nonneg.mpr hc.le)]
    simpa only [div_eq_mul_inv,mul_comm] using
      mul_le_mul_of_nonneg_left hAnorm (inv_nonneg.mpr hc.le)
  · intro x y
    change ((c⁻¹:ℝ):ℂ)*matrixCoeff A x y = _
    rw [hA]
    have hc' : (c:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    simp only [Complex.ofReal_inv]
    field_simp

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem amplificationLoad_scaled_kernel [Nonempty E] (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (hL : 1 ≤ L)
    (k n : ℕ) (hn : 0 < n) (p : unitInterval) (x z : V)
    (hz : z ∈ q.amplificationBall k n x) :
    (n:ℝ) * (q.amplificationLoad o hL k n p).kernel p x z =
      ∫ ω, q.amplificationMarginal (q.amplificationBonds k n x) (q.amplificationBall k n x)
        x k n ⟨z,hz⟩ p ω ∂law p := by
  change (n:ℝ) * (∫ ω, q.amplifiedMass k n p ω x z ∂law p) = _
  simp only [amplifiedMass,dite_eq_left hz,integral_div]
  have hn' : (n:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  field_simp

 

theorem amplificationLoad_exists_operator [Nonempty E] (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (hL : 1 ≤ L)
    (k n : ℕ) (hn : 0 < n) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ a b, matrixCoeff A a b = (q.kernel p a b : ℂ)) :
    ∃ T : Hilbert V →L[ℂ] Hilbert V, ‖T‖ ≤ binOrbitRow G p o n * ‖A‖^k / n ∧
      ∀ x z, matrixCoeff T x z = ((q.amplificationLoad o hL k n p).kernel p x z : ℂ) := by
  let F := (q.amplificationLoad o hL k n p).kernel p
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hposA : PositiveRealMatrix A := fun x z => by
    rw [hA]
    exact ⟨rfl,q.kernel_nonneg p x z⟩
  obtain ⟨S,hSnorm,hS⟩ := exists_operator_of_amplification_domination G hloc p o n k A hposA
    (fun x z => (n:ℝ)*F x z) (fun x z => mul_nonneg hn'.le ((q.amplificationLoad o hL k n p).kernel_nonneg p x z))
    (by
      intro H hH x z
      have hposH : PositiveRealMatrix H := fun a b => by
        rw [hH]
        exact ⟨rfl,orbitBinConnection_nonneg G p o n a b⟩
      have hpos := (((hposA.pow k).mul hposH) z x).2
      by_cases hz : z ∈ q.amplificationBall k n x
      · rw [q.amplificationLoad_scaled_kernel o hL k n hn p x z hz]
        by_cases ho : x ∈ vertexOrbit G o ∧ z ∈ vertexOrbit G o
        · exact q.amplificationMarginal_operator_le o _ _ x k n ⟨z,hz⟩ p ho.1 ho.2
            (q.amplificationBonds_root k n x) (fun a ha =>
              (incidentSupport_ball_mono G hloc a (le_max_left _ _)).trans (q.amplificationBonds_query k n x a ha)) A H hA hH
        · have hm (ω : Set E) : q.amplificationMarginal (q.amplificationBonds k n x)
              (q.amplificationBall k n x) x k n ⟨z,hz⟩ p ω = 0 := by
            by_contra h
            have hs := q.amplificationMarginal_support _ _ x k n ⟨z,hz⟩ p ω h
            exact ho ⟨hs.1,hs.2.1⟩
          simpa only [hm,integral_zero] using hpos
      · have he : F x z = 0 := by
          change (∫ ω, q.amplifiedMass k n p ω x z ∂law p) = 0
          simp only [amplifiedMass,dite_eq_right hz,integral_zero]
        simpa only [he,mul_zero] using hpos)
  exact exists_operator_of_scaled_matrix F n _ hn' S hSnorm (by
    intro x z
    simpa only [Complex.ofReal_mul] using hS x z)

end LocalEndpointRule
end AmplificationLoadOperator

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section TruncationOperator
attribute [local instance] Classical.propDecidable Classical.decEq
namespace CappedLocalLoad
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ}

theorem truncate_kernel_le (q : CappedLocalLoad G hloc O M) (p : unitInterval)
    (b : ℝ) (hb : 0 < b) (L : ℝ) (x y : V) :
    (q.truncate b hb L).kernel p x y ≤ b⁻¹ * q.kernel p x y := by
  rw [kernel,← integral_const_mul]
  exact integral_mono ((q.truncate b hb L).integrable_mass p x y)
    ((q.integrable_mass p x y).const_mul b⁻¹) (q.truncate_mass_le b hb L · x y)

 

theorem truncate_exists_operator (q : CappedLocalLoad G hloc O M) (p : unitInterval)
    (b : ℝ) (hb : 0 < b) (L : ℝ)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.kernel p x y : ℂ)) :
    ∃ T : Hilbert V →L[ℂ] Hilbert V, ‖T‖ ≤ ‖A‖/b ∧
      ∀ x y, matrixCoeff T x y = ((q.truncate b hb L).kernel p x y : ℂ) := by
  have hscale (x y : V) : matrixCoeff (((b⁻¹:ℝ):ℂ) • A) x y = (b⁻¹ * q.kernel p x y : ℝ) := by
    change ((b⁻¹:ℝ):ℂ)*matrixCoeff A x y = _
    rw [hA,Complex.ofReal_mul]
  obtain ⟨T,hT,hK⟩ := exists_operator_of_matrix_domination
    (fun x y => b⁻¹ * q.kernel p x y) ((q.truncate b hb L).kernel p)
    (fun x y => mul_nonneg (inv_nonneg.mpr hb.le) (q.kernel_nonneg p x y))
    (fun x y => by
      rw [abs_of_nonneg ((q.truncate b hb L).kernel_nonneg p x y)]
      exact q.truncate_kernel_le p b hb L x y)
    (((b⁻¹:ℝ):ℂ) • A) hscale
  refine ⟨T,hT.trans_eq ?_,hK⟩
  rw [norm_smul,Complex.norm_of_nonneg (inv_nonneg.mpr hb.le)]
  ring

end CappedLocalLoad
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

 
theorem normalize_mass_operator (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (hu : 0 < q.successProbability p o)
    (A : Hilbert V →L[ℂ] Hilbert V) (C : ℝ) (hAnorm : ‖A‖ ≤ C)
    (hA : ∀ x y, matrixCoeff A x y = (q.kernel p x y : ℂ)) :
    ∃ T : Hilbert V →L[ℂ] Hilbert V, ‖T‖ ≤ C/q.successProbability p o ∧
      ∀ x y, matrixCoeff T x y = (q.normalizedKernel o p x y : ℂ) := by
  apply exists_operator_of_scaled_matrix (q.normalizedKernel o p) (q.successProbability p o) C hu A hAnorm
  intro x y
  rw [hA]
  simp only [normalizedKernel,← Complex.ofReal_mul]
  congr 1
  rw [← mul_assoc,mul_inv_cancel₀ hu.ne',one_mul]

 

theorem mass_operator_of_normalized (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (hu : 0 < q.successProbability p o)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ)) :
    ∃ T : Hilbert V →L[ℂ] Hilbert V, ‖T‖ = q.successProbability p o * ‖A‖ ∧
      ∀ x y, matrixCoeff T x y = (q.kernel p x y : ℂ) := by
  refine ⟨(q.successProbability p o : ℂ) • A,?_,?_⟩
  · rw [norm_smul,Complex.norm_of_nonneg hu.le]
  · intro x y
    change (q.successProbability p o : ℂ)*matrixCoeff A x y = _
    rw [hA]
    simp only [normalizedKernel,← Complex.ofReal_mul]
    congr 1
    rw [← mul_assoc,mul_inv_cancel₀ hu.ne',one_mul]

end LocalEndpointRule
end TruncationOperator

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section AmplificationTruncationStep
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem normalized_operator_norm_pos (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (hu : 0 < q.successProbability p o)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ)) : 0 < ‖A‖ := by
  apply norm_pos_iff.mpr
  intro ha
  have hz (y : V) : q.kernel p o y = 0 := by
    have he := hA o y
    rw [ha] at he
    have he' : (q.successProbability p o)⁻¹ * q.kernel p o y = 0 :=
      Complex.ofReal_eq_zero.mp he.symm
    exact (mul_eq_zero.mp he').resolve_left (inv_ne_zero hu.ne')
  have he : q.successProbability p o = 0 := by
    simp only [successProbability,hz,tsum_zero]
  exact hu.ne' he

 

theorem amplification_truncation_step [Nonempty E] {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
    (p : unitInterval) (k n : ℕ) (hn : 0 < n)
    (hu : 0 < q.successProbability p (root i₀))
    (hbin : 0 < binOrbitRow G p (root i₀) n)
    (b L' : ℝ) (hb : 0 < b)
    (hmoment : (∫ ω, (q.amplificationLoad (root i₀) hL k n p).row ω (root i₀)^2 ∂law p) / b ≤
      (q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n / n)/4)
    (hbad : b * (law p).real {ω | CappedBadGoodness G ω (root i₀) (2*n+k*M) L'} ≤
      (q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n / n)/4)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel (root i₀) p x y : ℂ)) :
    ∃ q' : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) (2*n+k*M) L',
      (q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n / n)/(2*b) ≤
        q'.successProbability p (root i₀) ∧
      ∃ A' : Hilbert V →L[ℂ] Hilbert V, 0 < ‖A'‖ ∧ ‖A'‖ ≤ 2*‖A‖^k ∧
        ∀ x y, matrixCoeff A' x y = (q'.normalizedKernel (root i₀) p x y : ℂ) := by
  let load := q.amplificationLoad (root i₀) hL k n p
  let q' := load.truncate b hb L'
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hb₀ : 0 < q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n / n :=
    div_pos (mul_pos (pow_pos hu _) hbin) hn'
  have hself : root i₀ ∈ vertexOrbit G (root i₀) := by
    refine ⟨Equiv.refl V,Equiv.refl E,?_,rfl⟩
    intro e
    simp
  have hmean := q.amplificationLoad_mean root weight Γ htr hΓ hw i₀ hw₀ hL p k n (root i₀) hself
  have hnew := load.truncate_success_lower p b hb L' (root i₀) _ hmean.ge hmoment hbad
  have hu' : 0 < q'.successProbability p (root i₀) :=
    (div_pos hb₀ (mul_pos (by norm_num) hb)).trans_le hnew
  obtain ⟨B,hBnorm,hB⟩ := q.mass_operator_of_normalized (root i₀) p hu A hA
  obtain ⟨C,hCnorm,hC⟩ := q.amplificationLoad_exists_operator (root i₀) hL k n hn p B hB
  obtain ⟨D,hDnorm,hD⟩ := load.truncate_exists_operator p b hb L' C hC
  have hD' : ‖D‖ ≤ (binOrbitRow G p (root i₀) n * (q.successProbability p (root i₀)*‖A‖)^k/n)/b := by
    rw [hBnorm] at hCnorm
    exact hDnorm.trans (div_le_div_of_nonneg_right hCnorm hb.le)
  obtain ⟨A',hA'norm,hA'⟩ := q'.normalize_mass_operator (root i₀) p hu' D _ hD' hD
  refine ⟨q',hnew,A',q'.normalized_operator_norm_pos (root i₀) p hu' A' hA',hA'norm.trans ?_,hA'⟩
  apply (div_le_iff₀ hu').mpr
  apply (div_le_iff₀ hb).mpr
  apply (div_le_iff₀ hn').mpr
  have hret := (div_le_iff₀ (mul_pos (show (0:ℝ)<2 by norm_num) hb)).mp hnew
  have hret' := (div_le_iff₀ hn').mp hret
  rw [mul_pow]
  calc
    _ = (q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n) * ‖A‖^k := by ring
    _ ≤ (q'.successProbability p (root i₀)*(2*b)*n)*‖A‖^k :=
      mul_le_mul_of_nonneg_right hret' (pow_nonneg (norm_nonneg _) _)
    _ = _ := by ring

end LocalEndpointRule
end AmplificationTruncationStep

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Connections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Connections for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterWindowLaw
attribute [local instance] Classical.propDecidable Classical.decEq

theorem clusterWindow_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (lo hi : ℕ) (ω : Set E) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x hi).toFinset
    ClusterWindow G x lo hi ω ↔ ClusterWindow G x lo hi (ω ∩ (Q : Set E)) := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x hi).toFinset
  change ClusterWindow G x lo hi ω ↔ ClusterWindow G x lo hi (ω ∩ (Q : Set E))
  constructor
  · rintro ⟨hf,hl,hh⟩
    have hs : cluster G ω x ⊆ (finite_reachBall hloc x hi).toFinset := by
      simpa only [Set.Finite.coe_toFinset] using finite_cluster_subset_reachBall G ω x hf hi hh.le
    have he := cluster_restrict_incident_of_full G hloc _ ω x hs
    change cluster G (ω ∩ (Q : Set E)) x = cluster G ω x at he
    exact ⟨he.symm ▸ hf,he.symm ▸ hl,he.symm ▸ hh⟩
  · rintro ⟨hf,hl,hh⟩
    have he := cluster_restrict_of_cap G hloc Q ω x hi (Finset.Subset.refl _) hf hh.le
    exact ⟨he ▸ hf,he ▸ hl,he ▸ hh⟩

theorem measurableSet_clusterWindow (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (lo hi : ℕ) : MeasurableSet {ω | ClusterWindow G x lo hi ω} := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x hi).toFinset
  have he : {ω | ClusterWindow G x lo hi ω} =
      {ω | ω ∩ (Q : Set E) ∈ {η | ClusterWindow G x lo hi η}} := by
    ext ω
    exact clusterWindow_local G hloc x lo hi ω
  rw [he]
  exact measurableSet_finite_restriction Q _

theorem finiteClusterWindowMass_eq (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (p : unitInterval) (x : V) (lo hi : ℕ)
    (hQ : incidentSupport G hloc (finite_reachBall hloc x hi).toFinset ⊆ Q) :
    finiteClusterWindowMass G Q p x lo hi = clusterWindowProbability G p x lo hi := by
  let S := incidentSupport G hloc (finite_reachBall hloc x hi).toFinset
  let f : Set E → ℝ := fun ω => if ClusterWindow G x lo hi ω then 1 else 0
  have hf (ω) : f ω = f (ω ∩ (S : Set E)) :=
    if_congr (clusterWindow_local G hloc x lo hi ω) rfl rfl
  have he := integral_finite_local Q p f (finite_local_of_subset S Q hQ f hf)
  trans ∫ ω, f ω ∂law p
  · rw [he]
    unfold finiteClusterWindowMass finiteFieldIntegral
    apply Finset.sum_congr rfl
    intro η _
    congr 1
    unfold f ClusterWindow
    dsimp only
    split_ifs <;> rfl
  change (∫ ω, ({η | ClusterWindow G x lo hi η}.indicator (1 : Set E → ℝ)) ω ∂law p) = _
  exact integral_indicator_one (measurableSet_clusterWindow G hloc x lo hi)

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem finiteClusterWindowMass_amplification (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (k n : ℕ) (p : unitInterval) (x : V) :
    finiteClusterWindowMass G (q.amplificationBonds k n x) p x (n-k*M) (2*n) =
      clusterWindowProbability G p x (n-k*M) (2*n) := by
  apply finiteClusterWindowMass_eq G hloc
  exact incidentSupport_ball_mono G hloc x (by dsimp [amplificationRadius]; omega)

end LocalEndpointRule
end ClusterWindowLaw
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section QuantitativeAmplificationMoment
attribute [local instance] Classical.propDecidable Classical.decEq


theorem amplificationMomentFactor_pos (k M d : ℕ) (c a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) :
    0 < amplificationMomentFactor k M d c a t := by
  unfold amplificationMomentFactor
  positivity

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem amplificationLoad_moment_factor [Nonempty E] (hconn : Connected G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
    (p : unitInterval) (k n d : ℕ) (hn : 0 < n) (hdeg : ∀ x, degree G x ≤ d)
    (a t π : ℝ) (ha : 0 < a) (ht : 0 ≤ t) (hπ : 0 ≤ π)
    (hbin : a*n*π ≤ binOrbitRow G p (root i₀) n)
    (hwindow : clusterWindowProbability G p (root i₀) (n-k*M) (2*n) ≤ t*π)
    (hcode : inverseCodeMass M L^k ≤ n*q.successProbability p (root i₀)^k) :
    (∫ ω, (q.amplificationLoad (root i₀) hL k n p).row ω (root i₀)^2 ∂law p) ≤
      amplificationMomentFactor k M d c a t * q.successProbability p (root i₀)^k *
        (q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n / n) := by
  let u := q.successProbability p (root i₀)
  let B := u^k * binOrbitRow G p (root i₀) n / n
  let D : ℝ := (((k*M)+(k*M)^2+d*(k*M)^3:ℕ):ℝ)
  have hu : 0 ≤ u^k := pow_nonneg (q.successProbability_nonneg p _) _
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hB : a*π*u^k ≤ B := by
    apply (le_div_iff₀ hn').mpr
    calc
      _ = u^k*(a*n*π) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbin hu
  have hB0 : 0 ≤ B := (mul_nonneg (mul_nonneg ha.le hπ) hu).trans hB
  have hcoef : 4*u^k+D*inverseCodeMass M L^k/n ≤ (4+D)*u^k := by
    have h := mul_le_mul_of_nonneg_left hcode (show 0 ≤ D by positivity)
    have h' : D*inverseCodeMass M L^k/n ≤ D*u^k := by
      apply (div_le_iff₀ hn').mpr
      nlinarith only [h]
    nlinarith only [h']
  have hrem : (2*(c*((k*M:ℕ)*u^k)))^2*(t*π) ≤
      ((2*c*(k*M:ℕ))^2*t/a)*u^k*B := by
    have h := mul_le_mul_of_nonneg_left hB
      (show 0 ≤ ((2*c*(k*M:ℕ))^2*t/a)*u^k from
        mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) ht) ha.le) hu)
    calc
      _ = (((2*c*(k*M:ℕ))^2*t/a)*u^k)*(a*π*u^k) := by
        field_simp
      _ ≤ _ := h
  have hself : root i₀ ∈ vertexOrbit G (root i₀) := by
    refine ⟨Equiv.refl V,Equiv.refl E,?_,rfl⟩
    intro e
    simp
  have he := q.amplificationLoad_mean root weight Γ htr
    (fun e he => hΓ he) hw i₀ hw₀ hL p k n (root i₀) hself
  have hm := q.amplificationLoad_second_moment_le hconn root weight Γ hΓ htr hcov hw hw1
    c hc hmin i₀ hw₀ hL p (root i₀) k n d hn hdeg
  rw [he,q.finiteClusterWindowMass_amplification] at hm
  change _ ≤ (4*u^k+D*inverseCodeMass M L^k/n)*B +
    (2*(c*((k*M:ℕ)*u^k)))^2*clusterWindowProbability G p (root i₀) (n-k*M) (2*n) at hm
  calc
    _ ≤ _ := hm
    _ ≤ (4+D)*u^k*B + (2*(c*((k*M:ℕ)*u^k)))^2*(t*π) :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef hB0)
        (mul_le_mul_of_nonneg_left hwindow (sq_nonneg _))
    _ ≤ (4+D)*u^k*B + ((2*c*(k*M:ℕ))^2*t/a)*u^k*B := add_le_add (le_refl _) hrem
    _ = _ := by dsimp [amplificationMomentFactor,D,B,u]; ring

end LocalEndpointRule
end QuantitativeAmplificationMoment
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section QuantitativeAmplificationStep
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem quantitative_amplification_step_oai [Nonempty E] (hconn : Connected G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
    (p : unitInterval) (k n d : ℕ) (hn : 0 < n) (hdeg : ∀ x, degree G x ≤ d)
    (hu : 0 < q.successProbability p (root i₀))
    (a t π L' : ℝ) (ha : 0 < a) (ht : 0 ≤ t) (hπ : 0 < π)
    (hbin : a*n*π ≤ binOrbitRow G p (root i₀) n)
    (hwindow : clusterWindowProbability G p (root i₀) (n-k*M) (2*n) ≤ t*π)
    (hcode : inverseCodeMass M L^k ≤ n*q.successProbability p (root i₀)^k)
    (hbad : 16*amplificationMomentFactor k M d c a t *
      (law p).real {ω | CappedBadGoodness G ω (root i₀) (2*n+k*M) L'} ≤ a*π)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel (root i₀) p x y : ℂ)) :
    ∃ q' : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) (2*n+k*M) L',
      a*π/(8*amplificationMomentFactor k M d c a t) ≤ q'.successProbability p (root i₀) ∧
      ∃ A' : Hilbert V →L[ℂ] Hilbert V, 0 < ‖A'‖ ∧ ‖A'‖ ≤ 2*‖A‖^k ∧
        ∀ x y, matrixCoeff A' x y = (q'.normalizedKernel (root i₀) p x y : ℂ) := by
  let Q := amplificationMomentFactor k M d c a t
  let u := q.successProbability p (root i₀)
  let B := u^k*binOrbitRow G p (root i₀) n / n
  let b := 4*Q*u^k
  have hQ : 0 < Q := amplificationMomentFactor_pos k M d c a t ha ht
  have huk : 0 < u^k := pow_pos hu _
  have hb : 0 < b := mul_pos (mul_pos (by norm_num) hQ) huk
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hbin0 : 0 < binOrbitRow G p (root i₀) n :=
    (mul_pos (mul_pos ha hn') hπ).trans_le hbin
  have hB : a*π*u^k ≤ B := by
    apply (le_div_iff₀ hn').mpr
    calc
      _ = u^k*(a*n*π) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbin huk.le
  have hm := q.amplificationLoad_moment_factor hconn root weight Γ hΓ htr hcov hw hw1
    c hc hmin i₀ hw₀ hL p k n d hn hdeg a t π ha ht hπ.le hbin hwindow hcode
  have hmoment : (∫ ω, (q.amplificationLoad (root i₀) hL k n p).row ω (root i₀)^2 ∂law p)/b ≤ B/4 := by
    apply (div_le_iff₀ hb).mpr
    change _ ≤ Q*u^k*B at hm
    calc
      _ ≤ Q*u^k*B := hm
      _ = _ := by dsimp [b]; ring
  have hbad' : b*(law p).real {ω | CappedBadGoodness G ω (root i₀) (2*n+k*M) L'} ≤ B/4 := by
    have hh := mul_le_mul_of_nonneg_right hbad huk.le
    dsimp [b]
    nlinarith only [hh,hB]
  obtain ⟨q',hq',A',hA'pos,hA'norm,hA'⟩ := q.amplification_truncation_step root weight Γ htr
    (fun e he => hΓ he) hw i₀ hw₀ hL p k n hn hu hbin0 b L' hb hmoment hbad' A hA
  refine ⟨q',?_,A',hA'pos,hA'norm,hA'⟩
  apply le_trans _ hq'
  change a*π/(8*Q) ≤ B/(2*b)
  apply (div_le_div_iff₀ (mul_pos (by norm_num) hQ) (mul_pos (by norm_num) hb)).mpr
  have hh := mul_le_mul_of_nonneg_left hB (show 0 ≤ 8*Q by positivity)
  dsimp [b]
  nlinarith only [hh]

end LocalEndpointRule
end QuantitativeAmplificationStep
end Percolation


end OAI
end

theorem solution.{u, v, u_1} : type_of% @OAI.Percolation.LocalEndpointRule.quantitative_amplification_step_oai.{u, v, u_1} := @OAI.Percolation.LocalEndpointRule.quantitative_amplification_step_oai.{u, v, u_1}
