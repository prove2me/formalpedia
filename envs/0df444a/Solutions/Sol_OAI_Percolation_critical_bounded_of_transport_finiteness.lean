-- Prove2me | solution 1 for OAI.Percolation.critical_bounded_of_transport_finiteness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T00:58:59.871197+00:00
-- url     : https://prove2.me/submissions/c2d2ddac-4d86-4c6d-af0a-ea7f7f270062

import Mathlib
import Definitions.Def_CayleyPercolation
import Definitions.Def_OAIQ040C002
import Theorems.Thm_OAI_Percolation_almost_linear_susceptibility
import Theorems.Thm_OAI_Percolation_critical_rootTriangle_subpower
import Theorems.Thm_OAI_Percolation_exists_finite_scale_obstruction

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

theorem conn_univ_of_connected (h : Connected G) (x y : V) : Conn G Set.univ x y := by
  apply Relation.ReflTransGen.mono (r := Adj G) ?_ x y (h x y)
  rintro a b ⟨e, he⟩
  exact ⟨e, Set.mem_univ _, he⟩

end Deterministic

section Probability
variable (G : BondGraph V E)

theorem twoPoint_le_one (p : unitInterval) (x y : V) : twoPoint G p x y ≤ 1 := by
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using
    (prob_le_one (μ := law p) (s := {ω | Conn G ω x y})))

theorem twoPoint_symm (p : unitInterval) (x y : V) : twoPoint G p x y = twoPoint G p y x := by
  have he : {ω | Conn G ω x y} = {ω | Conn G ω y x} := by
    ext ω
    exact ⟨conn_symm G ω, conn_symm G ω⟩
  simp only [twoPoint, he]

end Probability

section Kernel
attribute [local instance] Classical.propDecidable

 
theorem kernel_extension_unique {K : V → V → ℂ}
    {A B : Hilbert V →L[ℂ] Hilbert V}
    (hA : ∀ x y, (A (lp.single 2 y (1 : ℂ))) x = K x y)
    (hB : ∀ x y, (B (lp.single 2 y (1 : ℂ))) x = K x y) : A = B := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro y
  apply ContinuousLinearMap.ext
  intro z
  apply lp.ext
  funext x
  have hz : lp.single (E := fun _ : V => ℂ) 2 y z =
      z • lp.single (E := fun _ : V => ℂ) 2 y (1 : ℂ) := by
    simpa using (lp.single_smul (E := fun _ : V => ℂ) 2 y z (1 : ℂ))
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    lp.singleContinuousLinearMap_apply, hz, map_smul, lp.coeFn_smul, Pi.smul_apply,
    hA, hB]

theorem HasKernel.unique {G : BondGraph V E} {p : unitInterval}
    {A B : Hilbert V →L[ℂ] Hilbert V} (hA : HasKernel G p A) (hB : HasKernel G p B) :
    A = B := kernel_extension_unique hA hB


end Kernel

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

theorem countable_vertices [Nonempty V] {G : BondGraph V E}
    (hG : LocallyFinite G) (hconn : Connected G) : Countable V := by
  let x : V := Classical.arbitrary V
  have he : (Set.univ : Set V) = ⋃ n, reachBall G x n := by
    ext y
    simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
    exact exists_mem_reachBall (hconn x y)
  apply Set.countable_univ_iff.mp
  rw [he]
  exact Set.countable_iUnion (fun n => (finite_reachBall hG x n).countable)

theorem countable_edges [Countable V] {G : BondGraph V E}
    (hG : LocallyFinite G) : Countable E := by
  have he : (Set.univ : Set E) = ⋃ x, {e | x ∈ G e} := by
    ext e
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
    exact ⟨(G e).out.1, Sym2.out_fst_mem _⟩
  apply Set.countable_univ_iff.mp
  rw [he]
  exact Set.countable_iUnion (fun x => (hG x).countable)

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

 

theorem exists_operator_of_matrix_tendsto
    (A : ℕ → Hilbert V →L[ℂ] Hilbert V) (K : V → V → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ n, ‖A n‖ ≤ M)
    (hlim : ∀ x y, Tendsto (fun n => A n (lp.single 2 y (1 : ℂ)) x)
      atTop (𝓝 (K x y))) :
    ∃ B : Hilbert V →L[ℂ] Hilbert V,
      ‖B‖ ≤ M ∧ ∀ x y, B (lp.single 2 y (1 : ℂ)) x = K x y := by
  have hn (n : ℕ) (f : Hilbert V) : ‖A n f‖ ≤ M * ‖f‖ :=
    (A n).le_opNorm f |>.trans (mul_le_mul_of_nonneg_right (hA n) (norm_nonneg _))
  have hcol (y : V) : Memℓp (fun x => K x y) 2 := by
    apply lp.memℓp_of_tendsto (l := atTop) (F := fun n => A n (lp.single 2 y (1 : ℂ)))
    · apply isBounded_iff_forall_norm_le.mpr
      refine ⟨M, ?_⟩
      rintro _ ⟨n, rfl⟩
      simpa [lp.norm_single] using hn n (lp.single 2 y (1 : ℂ))
    · exact tendsto_pi_nhds.mpr (fun x => hlim x y)
  let col (y : V) : Hilbert V := ⟨fun x => K x y, hcol y⟩
  let L : (V →₀ ℂ) →ₗ[ℂ] Hilbert V := Finsupp.linearCombination ℂ col
  have hLlim (f : V →₀ ℂ) :
      Tendsto (fun n => (A n (finiteEmbedding f) : V → ℂ)) atTop
        (𝓝 (L f : V → ℂ)) := by
    apply tendsto_pi_nhds.mpr
    intro x
    simp only [finiteEmbedding, L, Finsupp.linearCombination_apply, Finsupp.sum,
      map_sum, map_smul, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul]
    exact tendsto_finsetSum _ (fun y _ => (hlim x y).const_mul (f y))
  have hLn (f : V →₀ ℂ) : ‖L f‖ ≤ M * ‖finiteEmbedding f‖ := by
    exact lp.norm_le_of_tendsto (Eventually.of_forall (fun n => hn n _)) (hLlim f)
  refine ⟨L.extendOfNorm finiteEmbedding,
    LinearMap.opNorm_extendOfNorm_le finiteEmbedding_dense hM hLn, ?_⟩
  intro x y
  have h := LinearMap.extendOfNorm_eq (f := L) finiteEmbedding_dense ⟨M, hLn⟩
    (Finsupp.single y (1 : ℂ))
  simp only [finiteEmbedding_single] at h
  rw [h]
  simp [L, col]

end KernelLimits

section Coupling

theorem measurable_threshold (p : unitInterval) :
    Measurable (fun t : unitInterval => t ≤ p) :=
  measurableSet_setOfPred.mp measurableSet_Iic

 
theorem map_threshold (p : unitInterval) :
    (volume : Measure unitInterval).map (fun t => t ≤ p) =
      unitInterval.toNNReal p • Measure.dirac True +
      unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False := by
  apply Measure.ext_of_singleton
  intro b
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    simp [Measure.map_apply (measurable_threshold p), Set.preimage]
    change volume (Set.Iic p) = _
    rw [unitInterval.volume_Iic, ← unitInterval.coe_toNNReal p,
      ENNReal.ofReal_coe_nnreal]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    simp [Measure.map_apply (measurable_threshold p), Set.preimage]
    change volume (Set.Ioi p) = _
    rw [unitInterval.volume_Ioi, ← unitInterval.coe_symm_eq,
      ← unitInterval.coe_toNNReal (unitInterval.symm p), ENNReal.ofReal_coe_nnreal]

 
theorem map_openEdges (p : unitInterval) :
    (labelLaw : Measure (E → unitInterval)).map (fun labels => openEdges labels p) =
      law p := by
  unfold law
  rw [setBernoulli_eq_map]
  have hmeas : Measurable (fun labels : E → unitInterval => fun e => labels e ≤ p) :=
    Measurable.of_eval (fun e => (measurable_threshold p).comp (measurable_pi_apply e))
  have he : (fun labels : E → unitInterval => openEdges labels p) =
      (fun f : E → Prop => {e | f e}) ∘ (fun labels e => labels e ≤ p) := rfl
  rw [he, ← Measure.map_map measurable_setOfPred hmeas]
  unfold labelLaw
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_threshold p)]
  simp only [map_threshold, Set.mem_univ, bernoulliMeasure_def]

end Coupling

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

section CouplingOrder
variable [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable E] in
theorem measurable_openEdges (p : unitInterval) :
    Measurable (fun labels : E → unitInterval => openEdges labels p) :=
  measurable_setOfPred.comp (Measurable.of_eval
    (fun e => (measurable_threshold p).comp (measurable_pi_apply e)))

theorem twoPoint_eq_labelLaw (p : unitInterval) (x y : V) :
    twoPoint G p x y =
      (labelLaw {labels : E → unitInterval | Conn G (openEdges labels p) x y}).toReal := by
  unfold twoPoint
  rw [← map_openEdges p, Measure.map_apply (measurable_openEdges p)
    (measurableSet_conn G x y)]
  rfl

omit [Countable E] in
theorem openEdges_mono (labels : E → unitInterval) : Monotone (openEdges labels) := by
  intro p q hpq e he
  exact he.trans hpq

theorem twoPoint_mono (x y : V) : Monotone (fun p => twoPoint G p x y) := by
  intro p q hpq
  change twoPoint G p x y ≤ twoPoint G q x y
  rw [twoPoint_eq_labelLaw, twoPoint_eq_labelLaw]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro labels h
  exact conn_mono G (openEdges_mono labels hpq) h

end CouplingOrder

section NormOrder
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E] (G : BondGraph V E)

theorem operatorBounded_of_le {p q : unitInterval} (hpq : p ≤ q)
    (hq : OperatorBounded G q) : OperatorBounded G p := by
  obtain ⟨B, hB⟩ := hq
  obtain ⟨A, _, hA⟩ := exists_operator_of_matrix_domination
    (twoPoint G q) (twoPoint G p) (twoPoint_nonneg G q)
    (fun x y => (abs_of_nonneg (twoPoint_nonneg G p x y)).le.trans
      (twoPoint_mono G x y hpq)) B hB
  exact ⟨A, hA⟩

end NormOrder

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

section FiniteAssociation
attribute [local instance] Classical.propDecidable
variable [Fintype E]

private theorem bernoulli_atom_product (p : unitInterval) (ω : Set E) :
    (law p).real {ω} = ∏ e : E, if e ∈ ω then (p : ℝ) else 1 - p := by
  rw [law, setBernoulli_real_singleton p (Set.subset_univ ω) (Set.finite_univ)]
  simp [Finset.prod_ite, ← Set.ncard_coe_finset, Set.sdiff_eq]
  exact Or.inl rfl

private theorem bernoulli_atom_modular (p : unitInterval) (a b : Set E) :
    (law p).real {a} * (law p).real {b} =
      (law p).real {a ∩ b} * (law p).real {a ∪ b} := by
  simp only [bernoulli_atom_product, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  by_cases ha : e ∈ a <;> by_cases hb : e ∈ b <;> simp [ha, hb, mul_comm]

 

theorem association_finite (p : unitInterval) (f g : Set E → ℝ)
    (hf : Monotone f) (hg : Monotone g) (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) :
    (∫ ω, f ω ∂law p) * (∫ ω, g ω ∂law p) ≤ ∫ ω, f ω * g ω ∂law p := by
  have h := fkg f g (fun ω : Set E => (law p).real {ω})
    (fun _ => measureReal_nonneg) hf0 hg0 hf hg
    (fun a b => (bernoulli_atom_modular p a b).le)
  have hsum : (∑ ω : Set E, (law p).real {ω}) = 1 := by
    simp
  rw [hsum, one_mul] at h
  simpa only [integral_fintype Integrable.of_finite, smul_eq_mul] using h

 
theorem association_events_finite (p : unitInterval) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (law p).real A * (law p).real B ≤ (law p).real (A ∩ B) := by
  have hm (S : Set (Set E)) (hS : IsUpperSet S) :
      Monotone (S.indicator (fun _ => (1 : ℝ))) := by
    intro a b hab
    by_cases ha : a ∈ S
    · simp [ha, hS hab ha]
    · simp only [Set.indicator_of_notMem ha]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have he : (fun ω => A.indicator (fun _ => (1 : ℝ)) ω *
      B.indicator (fun _ => (1 : ℝ)) ω) = (A ∩ B).indicator (fun _ => 1) := by
    funext ω
    by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;> simp [ha, hb]
  have h := association_finite p _ _ (hm A hA) (hm B hB)
    (Set.indicator_nonneg (fun _ _ => zero_le_one))
    (Set.indicator_nonneg (fun _ _ => zero_le_one))
  rw [he] at h
  simpa only [integral_indicator_const (1 : ℝ) (.of_discrete : MeasurableSet A),
    integral_indicator_const (1 : ℝ) (.of_discrete : MeasurableSet B),
    integral_indicator_const (1 : ℝ) (.of_discrete : MeasurableSet (A ∩ B)),
    smul_eq_mul, mul_one] using h

end FiniteAssociation

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

section WitnessAssociation
attribute [local instance] Classical.propDecidable
open Filter Topology


theorem association_restricted (p : unitInterval) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) (s : Finset E) :
    (law p).real {ω | ω ∩ (s : Set E) ∈ A} *
      (law p).real {ω | ω ∩ (s : Set E) ∈ B} ≤
      (law p).real {ω | ω ∩ (s : Set E) ∈ A ∩ B} := by
  let A' : Set (Set (s : Set E)) := {η | Subtype.val '' η ∈ A}
  let B' : Set (Set (s : Set E)) := {η | Subtype.val '' η ∈ B}
  have hA' : IsUpperSet A' := fun _ _ h ha => hA (Set.image_mono h) ha
  have hB' : IsUpperSet B' := fun _ _ h hb => hB (Set.image_mono h) hb
  have he (ω : Set E) : Subtype.val '' (Subtype.val ⁻¹' ω : Set (s : Set E)) =
      ω ∩ (s : Set E) := by
    ext e
    simp [and_comm]
  have hl (C : Set (Set E)) :
      (law p : Measure (Set (s : Set E))).real {η | Subtype.val '' η ∈ C} =
      (law p).real {ω | ω ∩ (s : Set E) ∈ C} := by
    rw [← law_map_restrict p (s : Set E), measureReal_def,
      Measure.map_apply (measurable_set_restrict _) .of_discrete]
    simp only [Set.preimage_ofPred_eq, he, measureReal_def]
  have ht := association_events_finite p A' B' hA' hB'
  change (law p).real {η | Subtype.val '' η ∈ A} *
    (law p).real {η | Subtype.val '' η ∈ B} ≤
    (law p).real {η | Subtype.val '' η ∈ A ∩ B} at ht
  simpa only [hl] using ht

 theorem edgeExhaustion_mono [Encodable E] :
    Monotone (edgeExhaustion : ℕ → Finset E) := by
  intro m n h e he
  simp only [edgeExhaustion, Finset.mem_preimage, Finset.mem_range] at he ⊢
  exact he.trans_le h

private theorem subset_edgeExhaustion [Encodable E] (s : Finset E) :
    ∃ n, s ⊆ edgeExhaustion n := by
  refine ⟨s.sup Encodable.encode + 1, ?_⟩
  intro e he
  simp only [edgeExhaustion, Finset.mem_preimage, Finset.mem_range]
  exact Nat.lt_succ_of_le (Finset.le_sup he)

 theorem witness_eq_union [Encodable E] (A : Set (Set E))
    (hA : IsUpperSet A) (hf : FiniteWitness A) :
    A = ⋃ n, {ω | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ A} := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · intro hω
    obtain ⟨s, hs, hsa⟩ := hf ω hω
    obtain ⟨n, hn⟩ := subset_edgeExhaustion s
    exact ⟨n, hA (fun _ he => ⟨hs he, hn he⟩) hsa⟩
  · rintro ⟨n, hn⟩
    exact hA Set.inter_subset_left hn

 

theorem association_finiteWitness [Countable E] (p : unitInterval)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    (law p).real A * (law p).real B ≤ (law p).real (A ∩ B) := by
  let := Encodable.ofCountable E
  have hfAB : FiniteWitness (A ∩ B) := by
    intro ω hω
    obtain ⟨s, hs, hsa⟩ := hfA ω hω.1
    obtain ⟨t, ht, htb⟩ := hfB ω hω.2
    refine ⟨s ∪ t, ?_, hA ?_ hsa, hB ?_ htb⟩
    · simpa only [Finset.coe_union] using Set.union_subset hs ht
    · simp only [Finset.coe_union]; exact Set.subset_union_left
    · simp only [Finset.coe_union]; exact Set.subset_union_right
  have hlim (C : Set (Set E)) (hC : IsUpperSet C) (hfC : FiniteWitness C) :
      Tendsto (fun n => (law p).real {ω | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C})
        atTop (𝓝 ((law p).real C)) := by
    have hm : Monotone (fun n => {ω : Set E | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C}) := by
      intro m n h ω hω
      exact hC (Set.inter_subset_inter_right _ (edgeExhaustion_mono h)) hω
    have h := tendsto_measure_iUnion_atTop (μ := law p) hm
    rw [← witness_eq_union C hC hfC] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  exact le_of_tendsto_of_tendsto
    ((hlim A hA hfA).mul (hlim B hB hfB)) (hlim (A ∩ B) (hA.inter hB) hfAB)
    (Filter.Eventually.of_forall fun n => association_restricted p A B hA hB (edgeExhaustion n))

end WitnessAssociation

section ClusterEvents
attribute [local instance] Classical.propDecidable
open Filter Topology

 
theorem measurableSet_finiteWitness [Countable E] (A : Set (Set E))
    (hA : IsUpperSet A) (hfA : FiniteWitness A) : MeasurableSet A := by
  let := Encodable.ofCountable E
  rw [witness_eq_union A hA hfA]
  apply MeasurableSet.iUnion
  intro n
  let s := edgeExhaustion (E := E) n
  have he : {ω : Set E | ω ∩ (s : Set E) ∈ A} =
      (fun ω => (Subtype.val ⁻¹' ω : Set (s : Set E))) ⁻¹'
        {η | Subtype.val '' η ∈ A} := by
    ext ω
    change ω ∩ (s : Set E) ∈ A ↔ Subtype.val '' (Subtype.val ⁻¹' ω : Set (s : Set E)) ∈ A
    have hi : Subtype.val '' (Subtype.val ⁻¹' ω : Set (s : Set E)) = ω ∩ (s : Set E) := by
      ext e
      simp [and_comm]
    rw [hi]
  change MeasurableSet {ω : Set E | ω ∩ (s : Set E) ∈ A}
  rw [he]
  exact MeasurableSet.preimage .of_discrete (measurable_set_restrict _)

theorem finiteWitness_conn (G : BondGraph V E) (x y : V) :
    FiniteWitness {ω | Conn G ω x y} := by
  intro ω h
  induction h with
  | refl => exact ⟨∅, by simp, by simp⟩
  | @tail b c hab hbc ih =>
    obtain ⟨s, hs, hconn⟩ := ih
    obtain ⟨e, he, hGe⟩ := hbc
    refine ⟨insert e s, ?_, ?_⟩
    · simpa only [Finset.coe_insert] using Set.insert_subset he hs
    · exact (conn_mono G (by simp) hconn).tail ⟨e, by simp, hGe⟩

end ClusterEvents

section Automorphisms
attribute [local instance] Classical.propDecidable


theorem finite_open_probability (p : unitInterval) (s : Finset E) :
    (law p).real {ω | (s : Set E) ⊆ ω} = (p : ℝ) ^ s.card := by
  have he : {ω : Set E | (s : Set E) ⊆ ω} =
      (fun ω => (Subtype.val ⁻¹' ω : Set (s : Set E))) ⁻¹' {Set.univ} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => Set.eq_univ_of_forall fun e => h e.property,
      fun h e he => show (⟨e, he⟩ : (s : Set E)) ∈ (Subtype.val ⁻¹' ω) from
        h.symm ▸ Set.mem_univ _⟩
  unfold Measure.real
  rw [he, ← Measure.map_apply (measurable_set_restrict _) (by measurability),
    law_map_restrict]
  change (law p : Measure (Set (s : Set E))).real {Set.univ} = _
  simp [law, setBernoulli_real_singleton p (Set.Subset.refl _) (Set.toFinite _)]

end Automorphisms

section DisjointWitness
attribute [local instance] Classical.propDecidable


theorem disjointOccurrence_upper (A B : Set (Set E)) : IsUpperSet (DisjointOccurrence A B) := by
  rintro ω η h ⟨s, t, hs, ht, hd, ha, hb⟩
  exact ⟨s, t, hs.trans h, ht.trans h, hd, ha, hb⟩

theorem finiteWitness_disjointOccurrence (A B : Set (Set E)) :
    FiniteWitness (DisjointOccurrence A B) := by
  rintro ω ⟨s, t, hs, ht, hd, ha, hb⟩
  refine ⟨s ∪ t, ?_, s, t, ?_, ?_, hd, ha, hb⟩
  · simpa only [Finset.coe_union] using Set.union_subset hs ht
  · simp
  · simp

theorem disjointOccurrence_mono {A A' B B' : Set (Set E)}
    (hA : A ⊆ A') (hB : B ⊆ B') : DisjointOccurrence A B ⊆ DisjointOccurrence A' B' := by
  rintro ω ⟨s, t, hs, ht, hd, ha, hb⟩
  exact ⟨s, t, hs, ht, hd, hA ha, hB hb⟩


theorem openSection_upper {A : Set (Set E)} (hA : IsUpperSet A) (e : E) :
    IsUpperSet (openSection A e) :=
  fun _ _ h hω => hA (Set.insert_subset_insert h) hω

theorem subset_openSection {A : Set (Set E)} (hA : IsUpperSet A) (e : E) :
    A ⊆ openSection A e := fun ω hω => hA (Set.subset_insert e ω) hω

 
theorem openSection_disjointOccurrence (A B : Set (Set E)) (_hA : IsUpperSet A)
    (hB : IsUpperSet B) (e : E) :
    openSection (DisjointOccurrence A B) e ⊆
      DisjointOccurrence (openSection A e) B ∪ DisjointOccurrence A (openSection B e) := by
  rintro ω ⟨s, t, hs, ht, hd, ha, hb⟩
  by_cases he : e ∈ s
  · left
    have het : e ∉ t := fun h => Finset.disjoint_left.mp hd he h
    refine ⟨s.erase e, t, ?_, ?_, Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hd, ?_, hb⟩
    · intro z hz
      exact (hs (Finset.mem_of_mem_erase hz)).resolve_left (Finset.ne_of_mem_erase hz)
    · intro z hz
      rcases ht hz with rfl | hz'
      · exact (het hz).elim
      · exact hz'
    · change insert e (↑(s.erase e) : Set E) ∈ A
      simpa only [← Finset.coe_insert, Finset.insert_erase he] using ha
  · right
    refine ⟨s, t.erase e, ?_, ?_, Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hd, ha, ?_⟩
    · intro z hz
      rcases hs hz with rfl | hz'
      · exact (he hz).elim
      · exact hz'
    · intro z hz
      exact (ht (Finset.mem_of_mem_erase hz)).resolve_left (Finset.ne_of_mem_erase hz)
    · apply hB ?_ hb
      intro z hz
      by_cases hze : z = e
      · exact Or.inl hze
      · exact Or.inr (Finset.mem_erase.mpr ⟨hze, hz⟩)



theorem finiteProbability_mono (p : unitInterval) (s : Finset E)
    {A B : Set (Set E)} (h : A ⊆ B) : finiteProbability p s A ≤ finiteProbability p s B := by
  apply Finset.sum_le_sum
  intro t _
  split_ifs with ha hb hb
  · exact le_rfl
  · exact (hb (h ha)).elim
  · exact mul_nonneg (pow_nonneg p.2.1 _) (pow_nonneg (sub_nonneg.mpr p.2.2) _)
  · exact le_rfl

theorem finiteProbability_union_add_inter (p : unitInterval) (s : Finset E)
    (A B : Set (Set E)) :
    finiteProbability p s (A ∪ B) + finiteProbability p s (A ∩ B) =
      finiteProbability p s A + finiteProbability p s B := by
  simp only [finiteProbability, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ha : (t : Set E) ∈ A <;> by_cases hb : (t : Set E) ∈ B <;> simp [ha, hb]

theorem finiteProbability_insert (p : unitInterval) (s : Finset E) (e : E) (he : e ∉ s)
    (A : Set (Set E)) :
    finiteProbability p (insert e s) A =
      (1 - p : ℝ) * finiteProbability p s A + (p : ℝ) * finiteProbability p s (openSection A e) := by
  have hd : Disjoint s.powerset (s.powerset.image (insert e)) := by
    apply Finset.disjoint_left.mpr
    intro t ht himg
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp himg
    exact he ((Finset.mem_powerset.mp ht) (by simp))
  have hinj : Set.InjOn (insert e) (↑s.powerset : Set (Finset E)) := by
    intro t ht r hr h
    have ht' : e ∉ t := fun h => he (Finset.mem_powerset.mp ht h)
    have hr' : e ∉ r := fun h => he (Finset.mem_powerset.mp hr h)
    have hh := congrArg (fun t : Finset E => t.erase e) h
    simpa [ht', hr'] using hh
  simp only [finiteProbability, Finset.powerset_insert, Finset.sum_union hd,
    Finset.sum_image hinj, Finset.mul_sum, Finset.card_insert_of_notMem he]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    have hcard := Finset.card_le_card (Finset.mem_powerset.mp ht)
    have hexp : s.card + 1 - t.card = (s.card - t.card) + 1 := by omega
    rw [hexp, pow_succ]
    split_ifs <;> simp_all [mul_comm, mul_left_comm]
  · apply Finset.sum_congr rfl
    intro t ht
    have het : e ∉ t := fun h => he (Finset.mem_powerset.mp ht h)
    simp only [Finset.card_insert_of_notMem het, Nat.add_sub_add_right, pow_succ,
      Finset.coe_insert, openSection, Set.mem_ofPred_eq]
    split_ifs <;> simp_all [mul_assoc, mul_comm]

end DisjointWitness

section FiniteBK
attribute [local instance] Classical.propDecidable



theorem finiteProbability_disjointOccurrence_le_half (p : unitInterval)
    (hp : (p : ℝ) ≤ 1 / 2) (s : Finset E) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    finiteProbability p s (DisjointOccurrence A B) ≤
      finiteProbability p s A * finiteProbability p s B := by
  induction s using Finset.induction_on generalizing A B with
  | empty =>
    simp only [finiteProbability_empty, empty_mem_disjointOccurrence]
    by_cases ha : (∅ : Set E) ∈ A <;> by_cases hb : (∅ : Set E) ∈ B <;> simp [ha, hb]
  | @insert e s he ih =>
    let A1 := openSection A e
    let B1 := openSection B e
    let D00 := DisjointOccurrence A B
    let D10 := DisjointOccurrence A1 B
    let D01 := DisjointOccurrence A B1
    have hD : D00 ⊆ D10 ∩ D01 := by
      intro ω hω
      exact ⟨disjointOccurrence_mono (subset_openSection hA e) (Set.Subset.refl _) hω,
        disjointOccurrence_mono (Set.Subset.refl _) (subset_openSection hB e) hω⟩
    have hsec : finiteProbability p s (openSection D00 e) ≤
        finiteProbability p s D10 + finiteProbability p s D01 - finiteProbability p s D00 := by
      have h1 := finiteProbability_mono p s (openSection_disjointOccurrence A B hA hB e)
      have h2 := finiteProbability_mono p s hD
      have h3 := finiteProbability_union_add_inter p s D10 D01
      change finiteProbability p s (openSection D00 e) ≤
        finiteProbability p s (D10 ∪ D01) at h1
      linarith
    have h00 := ih A B hA hB
    have h10 := ih A1 B (openSection_upper hA e) hB
    have h01 := ih A B1 hA (openSection_upper hB e)
    have ha := finiteProbability_mono p s (subset_openSection hA e)
    have hb := finiteProbability_mono p s (subset_openSection hB e)
    have hcoef : 0 ≤ 1 - 2 * (p : ℝ) := by linarith
    have hdif : 0 ≤ ((p : ℝ) ^ 2) *
        (finiteProbability p s A1 - finiteProbability p s A) *
        (finiteProbability p s B1 - finiteProbability p s B) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr ha)) (sub_nonneg.mpr hb)
    rw [finiteProbability_insert p s e he, finiteProbability_insert p s e he,
      finiteProbability_insert p s e he]
    have hm := mul_le_mul_of_nonneg_left hsec p.2.1
    have hm00 := mul_le_mul_of_nonneg_left h00 hcoef
    have hm10 := mul_le_mul_of_nonneg_left h10 p.2.1
    have hm01 := mul_le_mul_of_nonneg_left h01 p.2.1
    change (1 - (p : ℝ)) * finiteProbability p s D00 +
      (p : ℝ) * finiteProbability p s (openSection D00 e) ≤
      ((1 - (p : ℝ)) * finiteProbability p s A + (p : ℝ) * finiteProbability p s A1) *
      ((1 - (p : ℝ)) * finiteProbability p s B + (p : ℝ) * finiteProbability p s B1)
    nlinarith

end FiniteBK

section BKMeasure
attribute [local instance] Classical.propDecidable
open Filter Topology

 
theorem finiteProbability_univ [Fintype E] (p : unitInterval) (A : Set (Set E)) :
    finiteProbability p Finset.univ A = (law p).real A := by
  have he : (law p).real A = ∑ ω : Set E, if ω ∈ A then (law p).real {ω} else 0 := by
    have h := integral_fintype (μ := law p) (f := A.indicator (fun _ => (1 : ℝ)))
      Integrable.of_finite
    rw [integral_indicator_const (1 : ℝ) (.of_discrete : MeasurableSet A)] at h
    simpa [smul_eq_mul, mul_ite, Set.indicator_apply] using h
  rw [he, finiteProbability]
  apply Finset.sum_bij (fun (t : Finset E) _ => (t : Set E))
  · simp
  · intro a _ b _ h
    exact Finset.coe_injective h
  · intro ω _
    exact ⟨ω.toFinset, by simp, by simp⟩
  · intro t _
    rw [law, setBernoulli_real_singleton p (Set.subset_univ _) Set.finite_univ]
    simp [Set.ncard_sdiff' (Set.subset_univ _) Set.finite_univ, Set.ncard_univ,
      Nat.card_eq_fintype_card]

theorem disjointOccurrence_image {F : Type*} (f : F ↪ E) (A B : Set (Set E)) :
    (fun ω => f '' ω) ⁻¹' DisjointOccurrence A B =
      DisjointOccurrence ((fun ω => f '' ω) ⁻¹' A) ((fun ω => f '' ω) ⁻¹' B) := by
  ext ω
  constructor
  · rintro ⟨s, t, hs, ht, hd, ha, hb⟩
    let s' := s.preimage f f.injective.injOn
    let t' := t.preimage f f.injective.injOn
    have hs' : (s' : Set F) = f ⁻¹' (s : Set E) := by simp [s']
    have ht' : (t' : Set F) = f ⁻¹' (t : Set E) := by simp [t']
    have hsI : f '' (s' : Set F) = (s : Set E) := by
      rw [hs', Set.image_preimage_eq_of_subset]
      exact hs.trans (Set.image_subset_range _ _)
    have htI : f '' (t' : Set F) = (t : Set E) := by
      rw [ht', Set.image_preimage_eq_of_subset]
      exact ht.trans (Set.image_subset_range _ _)
    refine ⟨s', t', ?_, ?_, ?_, ?_, ?_⟩
    · rw [hs']
      exact (Set.preimage_mono hs).trans (by rw [Set.preimage_image_eq _ f.injective])
    · rw [ht']
      exact (Set.preimage_mono ht).trans (by rw [Set.preimage_image_eq _ f.injective])
    · apply Finset.disjoint_left.mpr
      intro x hx hy
      exact Finset.disjoint_left.mp hd (by simpa [s'] using hx) (by simpa [t'] using hy)
    · change f '' (s' : Set F) ∈ A
      rwa [hsI]
    · change f '' (t' : Set F) ∈ B
      rwa [htI]
  · rintro ⟨s, t, hs, ht, hd, ha, hb⟩
    refine ⟨s.map f, t.map f, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [Finset.coe_map] using Set.image_mono hs
    · simpa only [Finset.coe_map] using Set.image_mono ht
    · exact (Finset.disjoint_map f).mpr hd
    · simpa only [Finset.coe_map, Set.mem_preimage] using ha
    · simpa only [Finset.coe_map, Set.mem_preimage] using hb

theorem bk_finite_half [Fintype E] (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (law p).real (DisjointOccurrence A B) ≤ (law p).real A * (law p).real B := by
  simpa only [finiteProbability_univ] using
    finiteProbability_disjointOccurrence_le_half p hp Finset.univ A B hA hB

theorem bk_restricted_half (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) (s : Finset E) :
    (law p).real {ω | ω ∩ (s : Set E) ∈ DisjointOccurrence A B} ≤
      (law p).real {ω | ω ∩ (s : Set E) ∈ A} *
      (law p).real {ω | ω ∩ (s : Set E) ∈ B} := by
  let f : (s : Set E) ↪ E := ⟨Subtype.val, Subtype.val_injective⟩
  have hreal (C : Set (Set E)) :
      (law p).real {ω | ω ∩ (s : Set E) ∈ C} =
        (law p).real {η : Set (s : Set E) | f '' η ∈ C} := by
    rw [← law_map_restrict p (s : Set E)]
    simp only [Measure.real]
    rw [Measure.map_apply (measurable_set_restrict _) MeasurableSet.of_discrete]
    congr 2
    ext ω
    change ω ∩ (s : Set E) ∈ C ↔ f '' (Subtype.val ⁻¹' ω) ∈ C
    have he : f '' (Subtype.val ⁻¹' ω) = ω ∩ (s : Set E) := by
      ext e
      simp [f, and_comm]
    rw [he]
  rw [hreal, hreal, hreal]
  have hh := bk_finite_half p hp ((fun ω => f '' ω) ⁻¹' A)
    ((fun ω => f '' ω) ⁻¹' B)
    (fun _ _ h hω => hA (Set.image_mono h) hω)
    (fun _ _ h hω => hB (Set.image_mono h) hω)
  rw [← disjointOccurrence_image] at hh
  exact hh

 
theorem bk_finiteWitness_half [Countable E] (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    (law p).real (DisjointOccurrence A B) ≤ (law p).real A * (law p).real B := by
  let := Encodable.ofCountable E
  have hlim (C : Set (Set E)) (hC : IsUpperSet C) (hfC : FiniteWitness C) :
      Tendsto (fun n => (law p).real {ω | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C})
        atTop (𝓝 ((law p).real C)) := by
    have hm : Monotone (fun n => {ω : Set E | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C}) := by
      intro m n h ω hω
      exact hC (Set.inter_subset_inter_right _ (edgeExhaustion_mono h)) hω
    have h := tendsto_measure_iUnion_atTop (μ := law p) hm
    rw [← witness_eq_union C hC hfC] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  apply le_of_tendsto_of_tendsto
    (hlim _ (disjointOccurrence_upper A B) (finiteWitness_disjointOccurrence A B))
    ((hlim A hA hfA).mul (hlim B hB hfB))
  exact Filter.Eventually.of_forall fun n => bk_restricted_half p hp A B hA hB (edgeExhaustion n)

end BKMeasure

section ORLift
attribute [local instance] Classical.propDecidable

instance bitLaw_isProbabilityMeasure (q : unitInterval) : IsProbabilityMeasure (bitLaw q) := by
  rw [bitLaw, ← map_threshold q]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

 
theorem map_nonempty (q : unitInterval) (F : Type*) [Fintype F] :
    (law q : Measure (Set F)).map Set.Nonempty = bitLaw (orParameter q (Fintype.card F)) := by
  let μ := (law q : Measure (Set F)).map Set.Nonempty
  have hm : Measurable (Set.Nonempty : Set F → Prop) := .of_discrete
  have : IsProbabilityMeasure μ := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have hfalse : μ.real {False} = (1 - (q : ℝ)) ^ Fintype.card F := by
    change ((law q).map Set.Nonempty).real {False} = _
    simp only [Measure.real, Measure.map_apply hm (measurableSet_singleton _)]
    have he : Set.Nonempty ⁻¹' ({False} : Set Prop) = ({∅} : Set (Set F)) := by
      ext ω
      simp [Set.not_nonempty_iff_eq_empty]
    rw [he]
    change (law q).real {∅} = _
    rw [law, setBernoulli_real_singleton q (Set.empty_subset _) Set.finite_univ]
    simp [Set.ncard_univ, Nat.card_eq_fintype_card]
  have htrue : μ.real {True} = 1 - (1 - (q : ℝ)) ^ Fintype.card F := by
    have he : ({True} : Set Prop) = ({False} : Set Prop)ᶜ := by ext b; simp
    rw [he, measureReal_compl (measurableSet_singleton _), probReal_univ, hfalse]
  apply Measure.ext_of_singleton
  intro b
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change μ.real {b} = (bitLaw (orParameter q (Fintype.card F))).real {b}
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    rw [htrue]
    simp [bitLaw, Measure.real, orParameter]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    rw [hfalse]
    simp [bitLaw, Measure.real, orParameter]

 
theorem finite_image_lift {F : Type*} (f : F → E) {ω : Set F} (s : Finset E)
    (hs : (s : Set E) ⊆ f '' ω) :
    ∃ t : Finset F, (t : Set F) ⊆ ω ∧ f '' (t : Set F) = (s : Set E) := by
  have hex : ∃ t ⊆ f '' ω, t.Finite ∧ t = (s : Set E) :=
    ⟨s, hs, s.finite_toSet, rfl⟩
  obtain ⟨t, ht, htf, hti⟩ := Set.exists_subset_image_finite_and.mp hex
  exact ⟨htf.toFinset, by simpa using ht, by simpa using hti⟩

theorem finiteWitness_image_preimage {F : Type*} (f : F → E) (A : Set (Set E))
    (hA : FiniteWitness A) : FiniteWitness ((fun ω => f '' ω) ⁻¹' A) := by
  intro ω hω
  obtain ⟨s, hs, ha⟩ := hA (f '' ω) hω
  obtain ⟨t, ht, htI⟩ := finite_image_lift f s hs
  exact ⟨t, ht, by simpa only [Set.mem_preimage, htI] using ha⟩

theorem image_preimage_disjointOccurrence {F : Type*} (f : F → E) (A B : Set (Set E)) :
    (fun ω => f '' ω) ⁻¹' DisjointOccurrence A B ⊆
      DisjointOccurrence ((fun ω => f '' ω) ⁻¹' A) ((fun ω => f '' ω) ⁻¹' B) := by
  rintro ω ⟨s, t, hs, ht, hd, ha, hb⟩
  obtain ⟨s', hs', hsI⟩ := finite_image_lift f s hs
  obtain ⟨t', ht', htI⟩ := finite_image_lift f t ht
  refine ⟨s', t', hs', ht', ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    have hxs : f x ∈ (s : Set E) := hsI ▸ Set.mem_image_of_mem f hx
    have hxt : f x ∈ (t : Set E) := htI ▸ Set.mem_image_of_mem f hy
    exact Finset.disjoint_left.mp hd hxs hxt
  · simpa only [Set.mem_preimage, hsI] using ha
  · simpa only [Set.mem_preimage, htI] using hb

end ORLift

section ORLaw
attribute [local instance] Classical.propDecidable

theorem map_exists_bitLaw (q : unitInterval) (F : Type*) [Fintype F] :
    (Measure.infinitePi (fun _ : F => bitLaw q)).map (fun f : F → Prop => ∃ j, f j) =
      bitLaw (orParameter q (Fintype.card F)) := by
  have h := map_nonempty q F
  unfold law at h
  rw [setBernoulli_eq_map, Measure.map_map (Measurable.of_discrete) measurable_setOfPred] at h
  simpa only [Set.mem_univ, Function.comp_def, Set.Nonempty, Set.mem_ofPred_eq,
    bernoulliMeasure_def, bitLaw] using h

theorem measurable_image_fst (F : Type*) [Fintype F] :
    Measurable (fun ω : Set (E × F) => Prod.fst '' ω) := by
  have hm : Measurable (fun ω : Set (E × F) => fun e => ∃ j : F, (e,j) ∈ ω) := by
    apply Measurable.of_eval
    intro e
    apply measurableSet_setOfPred.mp
    have he : {ω : Set (E × F) | ∃ j : F, (e,j) ∈ ω} =
        ⋃ j : F, {ω : Set (E × F) | (e,j) ∈ ω} := by ext ω; simp
    rw [he]
    exact MeasurableSet.iUnion fun j => measurableSet_setOfPred.mpr
      ((measurable_pi_apply (e,j)).comp MeasurableEquiv.setOfPred.symm.measurable)
  have he : (fun ω : Set (E × F) => Prod.fst '' ω) =
      (fun f : E → Prop => {e | f e}) ∘ (fun ω e => ∃ j : F, (e,j) ∈ ω) := by
    funext ω
    ext e
    simp [Prod.exists]
  rw [he]
  exact measurable_setOfPred.comp hm

 
theorem law_map_image_fst (q : unitInterval) (F : Type*) [Fintype F] :
    (law q : Measure (Set (E × F))).map (fun ω => Prod.fst '' ω) =
      law (orParameter q (Fintype.card F)) := by
  let c := MeasurableEquiv.curry E F Prop
  let b := fun f : E → F → Prop => fun e => ∃ j, f e j
  have hb : Measurable b := Measurable.of_eval
    (fun e => (Measurable.of_discrete : Measurable (fun f : F → Prop => ∃j, f j)).comp
      (measurable_pi_apply e))
  unfold law
  rw [setBernoulli_eq_map, Measure.map_map (measurable_image_fst F) measurable_setOfPred]
  simp only [Set.mem_univ]
  have he : (fun ω : Set (E × F) => Prod.fst '' ω) ∘ (fun f => {e | f e}) =
      (fun f : E → Prop => {e | f e}) ∘ b ∘ c := by
    funext f
    ext e
    simp [b, c, Function.comp_def, Prod.exists]
  rw [he, ← Measure.map_map measurable_setOfPred (hb.comp c.measurable),
    ← Measure.map_map hb c.measurable]
  change ((Measure.infinitePi (fun _ : E × F => bitLaw q)).map c |>.map b |>.map
    (fun f : E → Prop => {e | f e})) = _
  rw [Measure.infinitePi_map_curry (fun (_ : E) (_ : F) => bitLaw q)]
  dsimp only [b]
  rw [Measure.infinitePi_map_pi _ (fun _ => Measurable.of_discrete)]
  rw [map_exists_bitLaw q F]
  rw [setBernoulli_eq_map]
  rfl

 
theorem exists_orParameter (p : unitInterval) (hp : p < 1) :
    ∃ m : ℕ, ∃ q : unitInterval, (q : ℝ) ≤ 1 / 2 ∧ orParameter q m = p := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < 1 - (p : ℝ) by exact sub_pos.mpr hp)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  let f := fun x : ℝ => 1 - (1-x)^m
  have hf : Continuous f := by fun_prop
  have h0 : f 0 = 0 := by simp [f]
  have hp' : (p : ℝ) ∈ Set.Icc (f 0) (f (1/2)) := by
    rw [h0]
    refine ⟨p.2.1, ?_⟩
    dsimp [f]
    norm_num at hm ⊢
    linarith
  obtain ⟨q, hq, hqp⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1/2)
    hf.continuousOn hp'
  refine ⟨m, ⟨q, hq.1, hq.2.trans (by norm_num)⟩, hq.2, ?_⟩
  apply Subtype.ext
  exact hqp

end ORLaw

section BK
attribute [local instance] Classical.propDecidable

theorem disjointOccurrence_subset_inter (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) : DisjointOccurrence A B ⊆ A ∩ B := by
  rintro ω ⟨s,t,hs,ht,_,ha,hb⟩
  exact ⟨hA hs ha, hB ht hb⟩

 

theorem bk [Countable E] (p : unitInterval) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    (law p).real (DisjointOccurrence A B) ≤ (law p).real A * (law p).real B := by
  by_cases hp : p = 1
  · subst p
    by_cases hu : Set.univ ∈ DisjointOccurrence A B
    · have ha := (disjointOccurrence_subset_inter A B hA hB hu).1
      have hb := (disjointOccurrence_subset_inter A B hA hB hu).2
      simp [law, Measure.real, hu, ha, hb]
    · simp [law, Measure.real, hu]
      positivity
  · have hp' : p < 1 := lt_of_le_of_ne p.2.2 hp
    obtain ⟨m, q, hq, hqp⟩ := exists_orParameter p hp'
    let f : E × Fin m → E := Prod.fst
    let A' := (fun ω => f '' ω) ⁻¹' A
    let B' := (fun ω => f '' ω) ⁻¹' B
    have hreal (C : Set (Set E)) (hC : MeasurableSet C) :
        (law p).real C = (law q).real ((fun ω : Set (E × Fin m) => f '' ω) ⁻¹' C) := by
      have hh := law_map_image_fst (E := E) q (Fin m)
      simp only [Fintype.card_fin, hqp] at hh
      rw [← hh]
      simp only [Measure.real, Measure.map_apply (measurable_image_fst (Fin m)) hC]
      rfl
    calc
      (law p).real (DisjointOccurrence A B) =
          (law q).real ((fun ω : Set (E × Fin m) => f '' ω) ⁻¹' DisjointOccurrence A B) :=
        hreal _ (measurableSet_finiteWitness _ (disjointOccurrence_upper A B)
          (finiteWitness_disjointOccurrence A B))
      _ ≤ (law q).real (DisjointOccurrence A' B') :=
        measureReal_mono (image_preimage_disjointOccurrence f A B)
      _ ≤ (law q).real A' * (law q).real B' := bk_finiteWitness_half q hq A' B'
        (fun _ _ h hω => hA (Set.image_mono h) hω)
        (fun _ _ h hω => hB (Set.image_mono h) hω)
        (finiteWitness_image_preimage f A hfA) (finiteWitness_image_preimage f B hfB)
      _ = (law p).real A * (law p).real B := by
        rw [hreal A (measurableSet_finiteWitness A hA hfA),
          hreal B (measurableSet_finiteWitness B hB hfB)]

end BK

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Clusters_Uniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cluster events, invariant covers and uniqueness thresholds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section PercolationZeroOne
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E]

omit [Countable V] [Countable E] in
theorem infiniteClusters_nonempty_iff (G : BondGraph V E) (ω : Set E) :
    (infiniteClusters G ω).Nonempty ↔ ∃ x, (cluster G ω x).Infinite := by
  constructor
  · rintro ⟨C, hC, x, rfl⟩
    exact ⟨x, hC⟩
  · rintro ⟨x, hx⟩
    exact ⟨cluster G ω x, hx, x, rfl⟩

end PercolationZeroOne

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

 theorem degree_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (x : V) : degree G (a x) = degree G x :=
  (Nat.card_congr (stepEquiv G h x)).symm

 theorem exists_degree_bound (G : BondGraph V E) (hqt : QuasiTransitive G) :
    ∃ D : ℕ, 0 < D ∧ ∀ x, degree G x ≤ D := by
  obtain ⟨F, hF⟩ := hqt
  refine ⟨(∑ x ∈ F, degree G x) + 1, Nat.zero_lt_succ _, ?_⟩
  intro x
  obtain ⟨o, ho, a, b, hab, rfl⟩ := hF x
  rw [degree_aut G hab]
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) ho).trans (Nat.le_succ _)

end DegreeBound

section SmallParameter
attribute [local instance] Classical.propDecidable

theorem trailLength_upper (G : BondGraph V E) (x : V) (n : ℕ) :
    IsUpperSet (TrailLength G x n) := by
  rintro ω η h ⟨y,l,hl,hn,hlen,ho⟩
  exact ⟨y,l,hl,hn,hlen,fun e he => h (ho e he)⟩

theorem finiteWitness_trailLength (G : BondGraph V E) (x : V) (n : ℕ) :
    FiniteWitness (TrailLength G x n) := by
  rintro ω ⟨y,l,hl,hn,hlen,ho⟩
  exact ⟨l.toFinset, fun e he => ho e (List.mem_toFinset.mp he),
    y,l,hl,hn,hlen, fun e he => List.mem_toFinset.mpr he⟩

theorem finiteWitness_edge (e : E) : FiniteWitness {ω : Set E | e ∈ ω} := by
  intro ω he
  exact ⟨{e}, by simpa using he, by simp⟩

theorem trailLength_succ_subset (G : BondGraph V E) (x : V) (n : ℕ) :
    TrailLength G x (n+1) ⊆ ⋃ d : Step G x,
      DisjointOccurrence {ω | d.val.1 ∈ ω} (TrailLength G d.val.2 n) := by
  rintro ω ⟨y,l,hl,hn,hlen,ho⟩
  cases hl with
  | nil => simp at hlen
  | @cons x z y l e he tail =>
    refine Set.mem_iUnion.mpr ⟨⟨(e,z),he⟩, {e}, l.toFinset, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using ho e (by simp)
    · intro e' he'; exact ho e' (by simpa using Or.inr (List.mem_toFinset.mp he'))
    · simpa using (List.nodup_cons.mp hn).1
    · simp
    · exact ⟨y,l,tail,(List.nodup_cons.mp hn).2, by simpa using hlen,
        fun e' he' => List.mem_toFinset.mpr he'⟩

theorem trailLength_probability_le [Countable E] (G : BondGraph V E)
    (hloc : LocallyFinite G) (D : ℕ) (hD : ∀ x, degree G x ≤ D)
    (p : unitInterval) (x : V) (n : ℕ) :
    (law p).real (TrailLength G x n) ≤ ((D : ℝ) * p) ^ n := by
  induction n generalizing x with
  | zero => simpa only [pow_zero] using (measureReal_le_one (μ := law p) (s := TrailLength G x 0))
  | succ n ih =>
    let : Fintype (Step G x) := (finite_steps G hloc x).fintype
    let F := fun d : Step G x =>
      DisjointOccurrence {ω : Set E | d.val.1 ∈ ω} (TrailLength G d.val.2 n)
    calc
      (law p).real (TrailLength G x (n+1)) ≤ (law p).real (⋃ d, F d) :=
        measureReal_mono (trailLength_succ_subset G x n)
      _ ≤ ∑ d, (law p).real (F d) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _d : Step G x, (p : ℝ) * ((D : ℝ) * p) ^ n := by
        apply Finset.sum_le_sum
        intro d _
        have hb := bk p {ω : Set E | d.val.1 ∈ ω} (TrailLength G d.val.2 n)
          (fun _ _ hω he => hω he) (trailLength_upper G d.val.2 n)
          (finiteWitness_edge _) (finiteWitness_trailLength G d.val.2 n)
        have heq : (law p).real {ω : Set E | d.val.1 ∈ ω} = (p : ℝ) := by
          simpa using finite_open_probability p {d.val.1}
        rw [heq] at hb
        exact hb.trans (mul_le_mul_of_nonneg_left (ih d.val.2) p.2.1)
      _ ≤ (D : ℝ) * ((p : ℝ) * ((D : ℝ) * p) ^ n) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg p.2.1 (pow_nonneg (mul_nonneg (Nat.cast_nonneg D) p.2.1) n))
        exact_mod_cast (show Fintype.card (Step G x) ≤ D by
          simpa only [degree, Nat.card_eq_fintype_card] using hD x)
      _ = ((D : ℝ) * p) ^ (n+1) := by ring

 theorem Along.take {G : BondGraph V E} {x y : V} {l : List E}
    (h : Along G x l y) (n : ℕ) : ∃ z, Along G x (l.take n) z := by
  induction h generalizing n with
  | @nil z => exact ⟨z, by simpa using (Along.nil (G := G) z)⟩
  | @cons x z y l e he ht ih =>
    cases n with
    | zero => exact ⟨x,.nil x⟩
    | succ n =>
      obtain ⟨v,hv⟩ := ih n
      exact ⟨v,.cons e he hv⟩

 theorem infinite_cluster_subset_trailLength (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (n : ℕ) : {ω | (cluster G ω x).Infinite} ⊆ TrailLength G x n := by
  intro ω hω
  obtain ⟨y,hy,hyball⟩ := hω.exists_notMem_finite (finite_reachBall hloc x n)
  obtain ⟨l,hl,hn,ho⟩ := conn_exists_bond_trail G hy
  have hlen : n ≤ l.length := by
    by_contra h
    exact hyball ((reachBall_mono G x (le_of_lt (Nat.lt_of_not_ge h))) hl.mem_reachBall)
  obtain ⟨z,hz⟩ := hl.take n
  exact ⟨z,l.take n,hz,hn.take,List.length_take_of_le hlen,
    fun e he => ho e (List.mem_of_mem_take he)⟩

 theorem infinite_cluster_probability_eq_zero_of_small [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (D : ℕ) (hD : ∀ x, degree G x ≤ D)
    (p : unitInterval) (hp : (D : ℝ) * p < 1) (x : V) :
    law p {ω | (cluster G ω x).Infinite} = 0 := by
  apply (measureReal_eq_zero_iff).mp
  apply le_antisymm _ measureReal_nonneg
  apply ge_of_tendsto (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg (Nat.cast_nonneg D) p.2.1) hp)
  filter_upwards [] with n
  exact (measureReal_mono (infinite_cluster_subset_trailLength G hloc x n)).trans
    (trailLength_probability_le G hloc D hD p x n)

 theorem exists_infinite_cluster_probability_eq_zero_of_small [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (D : ℕ) (hD : ∀ x, degree G x ≤ D)
    (p : unitInterval) (hp : (D : ℝ) * p < 1) :
    law p {ω | (infiniteClusters G ω).Nonempty} = 0 := by
  have heq : {ω | (infiniteClusters G ω).Nonempty} =
      ⋃ x : V, {ω | (cluster G ω x).Infinite} := by
    ext ω
    simp only [Set.mem_ofPred_eq, infiniteClusters_nonempty_iff, Set.mem_iUnion]
  rw [heq, measure_iUnion_null_iff]
  exact infinite_cluster_probability_eq_zero_of_small G hloc D hD p hp

 theorem pc_pos [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G) :
    0 < pc G := by
  obtain ⟨D, hDpos, hD⟩ := exists_degree_bound G hqt
  let t : unitInterval := ⟨1 / ((D : ℝ) + 1), by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) D]⟩
  have ht : (0 : unitInterval) < t := by
    change (0 : ℝ) < 1 / ((D : ℝ) + 1)
    positivity
  apply ht.trans_le
  apply le_sInf
  intro p hp
  by_contra h
  have hp' : (p : ℝ) < 1 / ((D : ℝ) + 1) := lt_of_not_ge h
  have hsmall : (D : ℝ) * p < 1 := by
    have hmul := (lt_div_iff₀ (show (0 : ℝ) < D + 1 by positivity)).mp hp'
    nlinarith [p.2.1]
  have hz := exists_infinite_cluster_probability_eq_zero_of_small G hloc D hD p hsmall
  exact (ne_of_gt hp) hz

end SmallParameter

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

section SprinklingPaths
attribute [local instance] Classical.propDecidable

 
theorem Along.first_outside {G : BondGraph V E} {x y : V} {l : List E}
    (h : Along G x l y) (S : Set E) :
    (∀ e ∈ l, e ∈ S) ∨ ∃ a b e l₁ l₂,
      l = l₁ ++ e :: l₂ ∧ Along G x l₁ a ∧ G e = s(a,b) ∧
      Along G b l₂ y ∧ (∀ d ∈ l₁, d ∈ S) ∧ e ∉ S := by
  induction h with
  | nil => left; simp
  | @cons x z y l e he ht ih =>
    by_cases hes : e ∈ S
    · rcases ih with hall | ⟨a,b,d,l₁,l₂,hl,h₁,hd,h₂,hopen,hnot⟩
      · left
        simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hes hall
      · right
        refine ⟨a,b,d,e::l₁,l₂,by simp [hl], .cons e he h₁, hd, h₂, ?_, hnot⟩
        simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hes hopen
    · right
      exact ⟨x,z,e,[],l,rfl,.nil x,he,ht,by simp,hes⟩

 
theorem conn_first_outside (G : BondGraph V E) (S : Set E) {ω : Set E} {x y : V}
    (h : Conn G ω x y) :
    Conn G (ω ∩ S) x y ∨ ∃ a b e, G e = s(a,b) ∧ e ∉ S ∧
      ω ∈ DisjointOccurrence {η | Conn G (η ∩ S) x a}
        (DisjointOccurrence {η | e ∈ η} {η | Conn G η b y}) := by
  obtain ⟨l,hl,hn,ho⟩ := conn_exists_bond_trail G h
  rcases hl.first_outside S with hall | ⟨a,b,e,l₁,l₂,heq,h₁,he,h₂,hfirst,hnot⟩
  · exact Or.inl (hl.conn fun e he => ⟨ho e he,hall e he⟩)
  · subst l
    have hnod := List.nodup_append.mp hn
    have hen : e ∉ l₂ := (List.nodup_cons.mp hnod.2.1).1
    right
    refine ⟨a,b,e,he,hnot,l₁.toFinset,(e::l₂).toFinset,?_,?_,?_,?_,?_⟩
    · intro d hd
      exact ho d (List.mem_append_left _ (List.mem_toFinset.mp hd))
    · intro d hd
      exact ho d (List.mem_append_right _ (List.mem_toFinset.mp hd))
    · apply Finset.disjoint_left.mpr
      intro d hd hd'
      exact hnod.2.2 d (List.mem_toFinset.mp hd) d (List.mem_toFinset.mp hd') rfl
    · exact h₁.conn (fun d hd => ⟨by simpa using hd, hfirst d hd⟩)
    · refine ⟨{e},l₂.toFinset,?_,?_,?_,by simp,?_⟩
      · simp
      · simp
      · simpa using hen
      · exact h₂.conn (fun d hd => by simpa using hd)

 
theorem law_map_preimage_embedding {F : Type*} (p : unitInterval) (f : F ↪ E) :
    (law p : Measure (Set E)).map (fun ω => f ⁻¹' ω) = law p := by
  have hm : Measurable (fun ω : Set E => f ⁻¹' ω) :=
    measurable_setOfPred.comp (Measurable.of_eval
      (fun e => (measurable_pi_apply (f e)).comp MeasurableEquiv.setOfPred.symm.measurable))
  unfold law
  rw [setBernoulli_eq_map, Measure.map_map hm measurable_setOfPred]
  have he : (fun ω : Set E => f ⁻¹' ω) ∘ (fun g => {e | g e}) =
      (fun g : F → Prop => {e | g e}) ∘ (fun g : E → Prop => fun e => g (f e)) := rfl
  rw [he, ← Measure.map_map measurable_setOfPred (by fun_prop)]
  simp only [Set.mem_univ]
  have hi := (iIndepFun_infinitePi (P := fun _ : E => bernoulliMeasure True False p)
    (X := fun (_ : E) (b : Prop) => b) (fun _ => measurable_id)).precomp f.injective
  have hh := hi.map_fun_eq_infinitePi_map (fun _ => measurable_pi_apply _)
  simp only [Measure.infinitePi_map_eval] at hh
  erw [hh, setBernoulli_eq_map]
  rfl

 

theorem exists_orParameter_small (p : unitInterval) (hp : p < 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ m : ℕ, ∃ q : unitInterval, (q : ℝ) ≤ ε ∧ orParameter q m = p := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < 1 - (p : ℝ) by exact sub_pos.mpr hp)
    (show 1-ε < 1 by linarith)
  let f := fun x : ℝ => 1 - (1-x)^m
  have hf : Continuous f := by fun_prop
  have h0 : f 0 = 0 := by simp [f]
  have hp' : (p : ℝ) ∈ Set.Icc (f 0) (f ε) := by
    rw [h0]
    exact ⟨p.2.1, by dsimp [f]; linarith⟩
  obtain ⟨q,hq,hqp⟩ := intermediate_value_Icc hε.le hf.continuousOn hp'
  exact ⟨m,⟨q,hq.1,hq.2.trans hε1⟩,hq.2,Subtype.ext hqp⟩

end SprinklingPaths

section ColoredSprinkling
attribute [local instance] Classical.propDecidable

 theorem conn_map_edges {F : Type*} (G : BondGraph V E) (f : F → E)
    (ω : Set F) (x y : V) : Conn (G ∘ f) ω x y ↔ Conn G (f '' ω) x y := by
  constructor <;> intro h
  · induction h with
    | refl => exact conn_refl _ _ _
    | @tail a b hab he ih =>
      rcases he with ⟨e,he,heq⟩
      exact ih.tail ⟨f e,Set.mem_image_of_mem _ he,heq⟩
  · induction h with
    | refl => exact conn_refl _ _ _
    | @tail a b hab he ih =>
      rcases he with ⟨e,⟨d,hd,rfl⟩,heq⟩
      exact ih.tail ⟨d,hd,heq⟩

 theorem finiteWitness_inter (A : Set (Set E)) (hA : FiniteWitness A) (S : Set E) :
    FiniteWitness {ω | ω ∩ S ∈ A} := by
  intro ω h
  obtain ⟨s,hs,hsa⟩ := hA (ω ∩ S) h
  refine ⟨s,hs.trans Set.inter_subset_left,?_⟩
  have he : (s : Set E) ∩ S = s := Set.inter_eq_left.mpr (hs.trans Set.inter_subset_right)
  change (s : Set E) ∩ S ∈ A
  rwa [he]

 theorem not_mem_baseColors (m : ℕ) (e : E) (j : Fin (m+1)) :
    (e,j) ∉ baseColors m ↔ j = Fin.last m := by
  constructor
  · intro h
    apply Fin.eq_last_of_not_lt
    intro hj
    apply h
    exact ⟨(e,⟨j.val,hj⟩),Prod.ext rfl (Fin.ext rfl)⟩
  · rintro rfl ⟨⟨e',i⟩,hi⟩
    exact Fin.castSucc_ne_last i (congrArg Prod.snd hi)

 theorem fst_inter_baseColors (m : ℕ) (ω : Set (E × Fin (m+1))) :
    Prod.fst '' (ω ∩ baseColors m) = baseField m ω := by
  ext e
  constructor
  · rintro ⟨⟨e',j⟩,⟨ho,⟨⟨f,i⟩,he⟩⟩,rfl⟩
    refine ⟨(f,i),?_,?_⟩
    · change colorInclusion m (f,i) ∈ ω
      rwa [he]
    · exact congrArg Prod.fst he
  · rintro ⟨⟨e',i⟩,ho,rfl⟩
    exact ⟨colorInclusion m (e',i),⟨ho,Set.mem_range_self _⟩,rfl⟩

 theorem measurable_baseField (m : ℕ) : Measurable (baseField (E := E) m) := by
  apply (measurable_image_fst (Fin m)).comp
  exact measurable_setOfPred.comp (Measurable.of_eval
    (fun e => (measurable_pi_apply (colorInclusion m e)).comp
      MeasurableEquiv.setOfPred.symm.measurable))

 theorem law_map_baseField (q : unitInterval) (m : ℕ) :
    (law q : Measure (Set (E × Fin (m+1)))).map (baseField m) = law (orParameter q m) := by
  have hm : Measurable (fun ω : Set (E × Fin (m+1)) => colorInclusion m ⁻¹' ω) :=
    measurable_setOfPred.comp (Measurable.of_eval
      (fun e => (measurable_pi_apply (colorInclusion m e)).comp
        MeasurableEquiv.setOfPred.symm.measurable))
  change (law q).map ((fun ω : Set (E × Fin m) => Prod.fst '' ω) ∘
    (fun ω => colorInclusion m ⁻¹' ω)) = _
  rw [← Measure.map_map (measurable_image_fst (Fin m)) hm,
    law_map_preimage_embedding, law_map_image_fst, Fintype.card_fin]

 theorem exists_dart (G : BondGraph V E) {e : E} {a b : V} (h : G e = s(a,b)) :
    ∃ j : Bool, dartSource G (e,j) = a ∧ dartTarget G (e,j) = b := by
  have he : s((G e).out.1, (G e).out.2) = s(a,b) := (G e).out_eq.trans h
  rcases Sym2.eq_iff.mp he with h | h
  · exact ⟨true,h⟩
  · exact ⟨false,h.2,h.1⟩

 theorem colored_conn_probability [Countable V] [Countable E] (G : BondGraph V E)
    (q : unitInterval) (m : ℕ) (x y : V) :
    (law q).real {ω : Set (E × Fin m) | Conn (G ∘ Prod.fst) ω x y} =
      twoPoint G (orParameter q m) x y := by
  have h := law_map_image_fst (E := E) q (Fin m)
  simp only [Fintype.card_fin] at h
  rw [twoPoint, ← h, Measure.map_apply (measurable_image_fst (Fin m))
    (measurableSet_conn G x y)]
  congr 1
  ext ω
  exact conn_map_edges G Prod.fst ω x y

 theorem base_conn_probability [Countable V] [Countable E] (G : BondGraph V E)
    (q : unitInterval) (m : ℕ) (x y : V) :
    (law q).real {ω : Set (E × Fin (m+1)) |
      Conn (G ∘ Prod.fst) (ω ∩ baseColors m) x y} =
      twoPoint G (orParameter q m) x y := by
  rw [twoPoint, ← law_map_baseField (E := E) q m,
    Measure.map_apply (measurable_baseField m) (measurableSet_conn G x y)]
  congr 1
  ext ω
  change Conn (G ∘ Prod.fst) (ω ∩ baseColors m) x y ↔ Conn G (baseField m ω) x y
  rw [conn_map_edges, fst_inter_baseColors]

 

 theorem twoPoint_or_succ_le [Countable V] [Fintype E] (G : BondGraph V E) (q : unitInterval)
    (m : ℕ) (x y : V) :
    twoPoint G (orParameter q (m+1)) x y ≤ twoPoint G (orParameter q m) x y +
      (q : ℝ) * ∑ d : E × Bool,
        twoPoint G (orParameter q m) x (dartSource G d) *
        twoPoint G (orParameter q (m+1)) (dartTarget G d) y := by
  let H : BondGraph V (E × Fin (m+1)) := G ∘ Prod.fst
  let A (a : V) : Set (Set (E × Fin (m+1))) :=
    {ω | Conn H (ω ∩ baseColors m) x a}
  let B (b : V) : Set (Set (E × Fin (m+1))) := {ω | Conn H ω b y}
  let C (d : E × Bool) := DisjointOccurrence (A (dartSource G d))
    (DisjointOccurrence {ω | (d.1,Fin.last m) ∈ ω} (B (dartTarget G d)))
  have huA (a : V) : IsUpperSet (A a) :=
    fun _ _ h hω => conn_mono H (Set.inter_subset_inter_left _ h) hω
  have hfA (a : V) : FiniteWitness (A a) :=
    finiteWitness_inter _ (finiteWitness_conn H x a) _
  have huB (b : V) : IsUpperSet (B b) := fun _ _ h hω => conn_mono H h hω
  have hfB (b : V) : FiniteWitness (B b) := finiteWitness_conn H b y
  have hsub : {ω | Conn H ω x y} ⊆ A y ∪ ⋃ d : E × Bool, C d := by
    intro ω hω
    rcases conn_first_outside H (baseColors m) hω with ha | ⟨a,b,⟨e,j⟩,he,hj,hc⟩
    · exact Or.inl ha
    · have hj' := (not_mem_baseColors m e j).mp hj
      subst j
      obtain ⟨k,hk₁,hk₂⟩ := exists_dart G he
      right
      refine Set.mem_iUnion.mpr ⟨(e,k),?_⟩
      simpa only [C,hk₁,hk₂] using hc
  calc
    twoPoint G (orParameter q (m+1)) x y = (law q).real {ω | Conn H ω x y} :=
      (colored_conn_probability G q (m+1) x y).symm
    _ ≤ (law q).real (A y ∪ ⋃ d : E × Bool, C d) := measureReal_mono hsub
    _ ≤ (law q).real (A y) + (law q).real (⋃ d : E × Bool, C d) := measureReal_union_le _ _
    _ ≤ (law q).real (A y) + ∑ d : E × Bool, (law q).real (C d) :=
      add_le_add_right (measureReal_iUnion_fintype_le _) _
    _ ≤ twoPoint G (orParameter q m) x y +
        ∑ d : E × Bool, twoPoint G (orParameter q m) x (dartSource G d) *
          ((q : ℝ) * twoPoint G (orParameter q (m+1)) (dartTarget G d) y) := by
      rw [show (law q).real (A y) = twoPoint G (orParameter q m) x y from
        base_conn_probability G q m x y]
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro d _
      have hb := bk q {ω | (d.1,Fin.last m) ∈ ω} (B (dartTarget G d))
        (fun _ _ hh he => hh he) (huB _) (finiteWitness_edge _) (hfB _)
      have heq : (law q).real {ω : Set (E × Fin (m+1)) | (d.1,Fin.last m) ∈ ω} =
          (q : ℝ) := by simpa using finite_open_probability q {(d.1,Fin.last m)}
      rw [heq, show (law q).real (B (dartTarget G d)) =
        twoPoint G (orParameter q (m+1)) (dartTarget G d) y from
        colored_conn_probability G q (m+1) _ _] at hb
      have ha := bk q (A (dartSource G d))
        (DisjointOccurrence {ω | (d.1,Fin.last m) ∈ ω} (B (dartTarget G d)))
        (huA _) (disjointOccurrence_upper _ _) (hfA _) (finiteWitness_disjointOccurrence _ _)
      rw [show (law q).real (A (dartSource G d)) =
        twoPoint G (orParameter q m) x (dartSource G d) from base_conn_probability G q m _ _] at ha
      exact ha.trans (mul_le_mul_of_nonneg_left hb (twoPoint_nonneg G _ _ _))
    _ = _ := by rw [Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl; intro d _; ring

end ColoredSprinkling

section FiniteGraphOperators
attribute [local instance] Classical.propDecidable

 theorem mem_edgeVertices [Fintype E] (G : BondGraph V E) (x : V) :
    x ∈ edgeVertices G ↔ ∃ e, x ∈ G e := by simp [edgeVertices]

 theorem conn_eq_or_mem_edgeVertices [Fintype E] (G : BondGraph V E)
    {ω : Set E} {x y : V} (h : Conn G ω x y) : x = y ∨ y ∈ edgeVertices G := by
  cases h with
  | refl => exact Or.inl rfl
  | @tail a b hab he =>
    rcases he with ⟨e,_,he⟩
    exact Or.inr ((mem_edgeVertices G y).mpr ⟨e,by rw [he]; simp⟩)

 theorem operatorBounded_finite_edges [Fintype E] (G : BondGraph V E) (p : unitInterval) :
    OperatorBounded G p := by
  have hr (x : V) (s : Finset V) : ∑ y ∈ s, twoPoint G p x y ≤
      (edgeVertices G).card + (1 : ℝ) := by
    let F := insert x (edgeVertices G)
    have bound (y : V) : twoPoint G p x y ≤ if y ∈ F then 1 else 0 := by
      split_ifs with hy
      · exact twoPoint_le_one G p x y
      · have he : {ω | Conn G ω x y} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro ω h
          rcases conn_eq_or_mem_edgeVertices G h with rfl | hmem
          · exact hy (by simp [F])
          · exact hy (by simp [F,hmem])
        simp [twoPoint,he]
    calc
      ∑ y ∈ s, twoPoint G p x y ≤ ∑ y ∈ s, if y ∈ F then (1:ℝ) else 0 :=
        Finset.sum_le_sum (fun y _ => bound y)
      _ = ((s ∩ F).card : ℝ) := by simp
      _ ≤ (F.card : ℝ) := by
        exact_mod_cast Finset.card_le_card Finset.inter_subset_right
      _ ≤ (edgeVertices G).card + (1 : ℝ) := by
        exact_mod_cast Finset.card_insert_le x (edgeVertices G)
  obtain ⟨A,_,hA⟩ := exists_operator_of_row_column_bound (twoPoint G p)
    ((edgeVertices G).card+1) (by positivity) (twoPoint_nonneg G p) hr
    (fun y s => by simpa only [twoPoint_symm G p] using hr y s)
  exact ⟨A,hA⟩

 theorem dart_edge (G : BondGraph V E) (d : E × Bool) :
    G d.1 = s(dartSource G d, dartTarget G d) := by
  rcases d with ⟨e,j⟩
  cases j
  · exact (G e).out_eq.symm.trans (Sym2.eq_swap ..)
  · exact (G e).out_eq.symm

 theorem card_darts_at_source [Fintype E] (G : BondGraph V E) (x : V) :
    Fintype.card {d : E × Bool // dartSource G d = x} ≤ 2 * degree G x := by
  let : Fintype (Step G x) := (finite_steps G (fun _ => Set.toFinite _) x).fintype
  let f : {d : E × Bool // dartSource G d = x} → Step G x × Bool := fun d =>
    (⟨(d.val.1,dartTarget G d.val), by rw [dart_edge G d.val,d.property]⟩,d.val.2)
  have hf : Function.Injective f := by
    intro d d' h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun t : Step G x × Bool => t.1.val.1) h
    · exact congrArg (fun t : Step G x × Bool => t.2) h
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod,Fintype.card_bool,degree,Nat.card_eq_fintype_card,Nat.mul_comm] using hc

 theorem card_darts_at_target [Fintype E] (G : BondGraph V E) (x : V) :
    Fintype.card {d : E × Bool // dartTarget G d = x} ≤ 2 * degree G x := by
  let : Fintype (Step G x) := (finite_steps G (fun _ => Set.toFinite _) x).fintype
  let f : {d : E × Bool // dartTarget G d = x} → Step G x × Bool := fun d =>
    (⟨(d.val.1,dartSource G d.val), by
      rw [dart_edge G d.val,d.property]; exact Sym2.eq_swap ..⟩,d.val.2)
  have hf : Function.Injective f := by
    intro d d' h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun t : Step G x × Bool => t.1.val.1) h
    · exact congrArg (fun t : Step G x × Bool => t.2) h
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod,Fintype.card_bool,degree,Nat.card_eq_fintype_card,Nat.mul_comm] using hc

 theorem adjacencyOperator_apply [Fintype E] (G : BondGraph V E) (f : Hilbert V) :
    adjacencyOperator G f = ∑ d : E × Bool, lp.single 2 (dartSource G d) (f (dartTarget G d)) := by
  simp [adjacencyOperator,lp.singleContinuousLinearMap_apply,
    lp.evalCLM,lp.evalₗ]
  rfl

 theorem adjacencyOperator_norm_le [Fintype E] (G : BondGraph V E)
    (D : ℕ) (hD : ∀ x, degree G x ≤ D) : ‖adjacencyOperator G‖ ≤ 2 * (D : ℝ) := by
  let U (x y : V) : ℝ := ∑ d : E × Bool,
    if dartSource G d = x ∧ dartTarget G d = y then 1 else 0
  have hU : ∀ x y, 0 ≤ U x y := by intro x y; apply Finset.sum_nonneg; intro d _; positivity
  have hmat : ∀ x y, adjacencyOperator G (lp.single 2 y (1:ℂ)) x = (U x y : ℂ) := by
    intro x y
    rw [adjacencyOperator_apply]
    simp only [lp.coeFn_sum,Finset.sum_apply,U,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro d _
    simp only [lp.single_apply]
    by_cases hx : dartSource G d = x <;> by_cases hy : dartTarget G d = y <;>
      simp [hx,hy]
  have hrow (x : V) (s : Finset V) : ∑ y ∈ s, U x y ≤ 2 * (D : ℝ) := by
    calc
      ∑ y ∈ s, U x y = ∑ d : E × Bool,
          ∑ y ∈ s, if dartSource G d = x ∧ dartTarget G d = y then (1:ℝ) else 0 :=
        Finset.sum_comm
      _ ≤ ∑ d : E × Bool, if dartSource G d = x then (1:ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro d _
        by_cases hx : dartSource G d = x
        · simp only [hx,true_and,ite_true]
          rw [Finset.sum_ite_eq]
          split_ifs <;> norm_num
        · simp [hx]
      _ = (Fintype.card {d : E × Bool // dartSource G d = x} : ℝ) := by simp [Fintype.card_subtype]
      _ ≤ 2 * (D : ℝ) := by exact_mod_cast (card_darts_at_source G x).trans (Nat.mul_le_mul_left 2 (hD x))
  have hcol (y : V) (s : Finset V) : ∑ x ∈ s, U x y ≤ 2 * (D : ℝ) := by
    calc
      ∑ x ∈ s, U x y = ∑ d : E × Bool,
          ∑ x ∈ s, if dartSource G d = x ∧ dartTarget G d = y then (1:ℝ) else 0 :=
        Finset.sum_comm
      _ ≤ ∑ d : E × Bool, if dartTarget G d = y then (1:ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro d _
        by_cases hy : dartTarget G d = y
        · simp only [hy,and_true,ite_true]
          rw [Finset.sum_ite_eq]
          split_ifs <;> norm_num
        · simp [hy]
      _ = (Fintype.card {d : E × Bool // dartTarget G d = y} : ℝ) := by simp [Fintype.card_subtype]
      _ ≤ 2 * (D : ℝ) := by exact_mod_cast (card_darts_at_target G y).trans (Nat.mul_le_mul_left 2 (hD y))
  obtain ⟨A,hn,hA⟩ := exists_operator_of_row_column_bound U (2*D) (by positivity) hU hrow hcol
  rwa [kernel_extension_unique hmat hA]

end FiniteGraphOperators

section FiniteSprinklingBound
attribute [local instance] Classical.propDecidable
variable [Countable V] [Fintype E]

 theorem finite_sprinkling_bound (G : BondGraph V E) (q : unitInterval) (m D : ℕ)
    (hD : ∀ x, degree G x ≤ D) (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : HasKernel G (orParameter q m) A) (M : ℝ) (hM : ‖A‖ ≤ M)
    (hq : (q : ℝ) * (2*D) * M < 1) :
    ∃ B : Hilbert V →L[ℂ] Hilbert V, HasKernel G (orParameter q (m+1)) B ∧
      ‖B‖ ≤ M / (1-(q:ℝ)*(2*D)*M) := by
  obtain ⟨B,hB⟩ := operatorBounded_finite_edges G (orParameter q (m+1))
  let R := (adjacencyOperator G).comp B
  let C := A + (q : ℂ) • A.comp R
  let U (x y : V) := twoPoint G (orParameter q m) x y + (q:ℝ) *
    ∑ d : E × Bool, twoPoint G (orParameter q m) x (dartSource G d) *
      twoPoint G (orParameter q (m+1)) (dartTarget G d) y
  have hU : ∀ x y, 0 ≤ U x y := by
    intro x y
    exact add_nonneg (twoPoint_nonneg G _ _ _)
      (mul_nonneg q.2.1 (Finset.sum_nonneg fun d _ =>
        mul_nonneg (twoPoint_nonneg G _ _ _) (twoPoint_nonneg G _ _ _)))
  have hC : ∀ x y, C (lp.single 2 y (1:ℂ)) x = (U x y : ℂ) := by
    intro x y
    simp only [C,add_apply,smul_apply,
      ContinuousLinearMap.comp_apply,R,adjacencyOperator_apply,map_sum,lp.coeFn_add,Pi.add_apply,
      lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.coeFn_sum,Finset.sum_apply,U,
      Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_sum]
    rw [hA x y]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro d _
    have hs (c : ℂ) : (lp.single 2 (dartSource G d) c : Hilbert V) = c • lp.single 2 (dartSource G d) (1:ℂ) := by
      rw [← lp.single_smul]; simp
    rw [hs,map_smul,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,hA,hB]
    ring
  obtain ⟨B',hn,hB'⟩ := exists_operator_of_matrix_domination U
    (twoPoint G (orParameter q (m+1))) hU
    (fun x y => by rw [abs_of_nonneg (twoPoint_nonneg G _ _ _)]; exact twoPoint_or_succ_le G q m x y)
    C hC
  have he : B' = B := kernel_extension_unique hB' hB
  rw [he] at hn
  have hqn : ‖(q : ℂ)‖ = (q : ℝ) := by simp [abs_of_nonneg q.2.1]
  have hcoef : (q : ℝ) * ‖A‖ * (2*D) * ‖B‖ ≤ (q : ℝ) * M * (2*D) * ‖B‖ := by
    gcongr
    exact q.2.1
  have hbnd : ‖B‖ ≤ M + (q : ℝ) * (2*D) * M * ‖B‖ := by
    calc
      ‖B‖ ≤ ‖C‖ := hn
      _ ≤ ‖A‖ + ‖(q : ℂ) • A.comp R‖ := norm_add_le _ _
      _ = ‖A‖ + (q : ℝ) * ‖A.comp R‖ := by rw [norm_smul,hqn]
      _ ≤ ‖A‖ + (q : ℝ) * (‖A‖ * (‖adjacencyOperator G‖ * ‖B‖)) := by
        apply add_le_add_right
        apply mul_le_mul_of_nonneg_left _ q.2.1
        exact (A.opNorm_comp_le R).trans
          (mul_le_mul_of_nonneg_left ((adjacencyOperator G).opNorm_comp_le B) (norm_nonneg _))
      _ ≤ ‖A‖ + (q : ℝ) * (‖A‖ * ((2*D) * ‖B‖)) := by
        gcongr
        · exact q.2.1
        · exact adjacencyOperator_norm_le G D hD
      _ ≤ M + (q : ℝ) * M * (2*D) * ‖B‖ := by
        rw [show (q : ℝ) * (‖A‖ * ((2*D) * ‖B‖)) = (q : ℝ) * ‖A‖ * (2*D) * ‖B‖ by ring]
        exact add_le_add hM hcoef
      _ = _ := by ring
  refine ⟨B,hB,?_⟩
  apply (le_div_iff₀ (sub_pos.mpr hq)).mpr
  nlinarith

end FiniteSprinklingBound

section ExhaustionSprinkling
attribute [local instance] Classical.propDecidable
open Filter Topology
variable [Countable V] [Countable E]

 theorem twoPoint_restrict_edges (G : BondGraph V E) (p : unitInterval) (S : Set E) (x y : V) :
    twoPoint (G ∘ (Subtype.val : S → E)) p x y =
      (law p).real {ω : Set E | Conn G (ω ∩ S) x y} := by
  unfold twoPoint
  rw [← law_map_restrict p S, Measure.map_apply (measurable_set_restrict S)
    (measurableSet_conn (G ∘ Subtype.val) x y)]
  apply congrArg ENNReal.toReal
  congr 1
  ext ω
  change Conn (G ∘ Subtype.val) (Subtype.val ⁻¹' ω) x y ↔ _
  rw [conn_map_edges]
  have he : (Subtype.val '' (Subtype.val ⁻¹' ω : Set S)) = ω ∩ S := by
    ext e
    simp only [Set.mem_image,Set.mem_preimage,Set.mem_inter_iff]
    constructor
    · rintro ⟨d,hd,rfl⟩; exact ⟨hd,d.property⟩
    · rintro ⟨ho,hs⟩; exact ⟨⟨e,hs⟩,ho,rfl⟩
  rw [he]
  rfl

 theorem twoPoint_restrict_le (G : BondGraph V E) (p : unitInterval) (S : Set E) (x y : V) :
    twoPoint (G ∘ (Subtype.val : S → E)) p x y ≤ twoPoint G p x y := by
  rw [twoPoint_restrict_edges]
  exact measureReal_mono (fun ω h => conn_mono G Set.inter_subset_left h) (measure_ne_top _ _)

 omit [Countable V] [Countable E] in
 theorem degree_restrict_le (G : BondGraph V E) (hloc : LocallyFinite G) (S : Set E) (x : V) :
    degree (G ∘ (Subtype.val : S → E)) x ≤ degree G x := by
  let : Fintype (Step G x) := (finite_steps G hloc x).fintype
  let f : Step (G ∘ (Subtype.val : S → E)) x → Step G x :=
    fun d => ⟨(d.val.1.val,d.val.2),d.property⟩
  apply Nat.card_le_card_of_injective f
  intro d d' h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun t : Step G x => t.val.1) h
  · exact congrArg (fun t : Step G x => t.val.2) h

 theorem sprinkling_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (q : unitInterval) (m D : ℕ) (hD : ∀ x, degree G x ≤ D)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : HasKernel G (orParameter q m) A)
    (hq : (q : ℝ) * (2*D) * ‖A‖ < 1) :
    ∃ B : Hilbert V →L[ℂ] Hilbert V, HasKernel G (orParameter q (m+1)) B ∧
      ‖B‖ ≤ ‖A‖ / (1-(q:ℝ)*(2*D)*‖A‖) := by
  let := Encodable.ofCountable E
  let F (n : ℕ) := edgeExhaustion (E := E) n
  let H (n : ℕ) : BondGraph V (F n) := G ∘ Subtype.val
  have hb (n : ℕ) : ∃ B : Hilbert V →L[ℂ] Hilbert V,
      HasKernel (H n) (orParameter q (m+1)) B ∧
      ‖B‖ ≤ ‖A‖ / (1-(q:ℝ)*(2*D)*‖A‖) := by
    obtain ⟨A',hn,hA'⟩ := exists_operator_of_matrix_domination
      (twoPoint G (orParameter q m)) (twoPoint (H n) (orParameter q m))
      (twoPoint_nonneg G _) (fun x y => by
        rw [abs_of_nonneg (twoPoint_nonneg (H n) _ _ _)]
        exact twoPoint_restrict_le G _ (F n) x y) A hA
    exact finite_sprinkling_bound (H n) q m D
      (fun x => (degree_restrict_le G hloc (F n) x).trans (hD x)) A' hA' ‖A‖ hn hq
  choose B hB hn using hb
  have hlim (x y : V) : Tendsto (fun n => twoPoint (H n) (orParameter q (m+1)) x y)
      atTop (𝓝 (twoPoint G (orParameter q (m+1)) x y)) := by
    have hm : Monotone (fun n => {ω : Set E | Conn G (ω ∩ (F n : Set E)) x y}) := by
      intro m n h ω hω
      exact conn_mono G (Set.inter_subset_inter_right _ (edgeExhaustion_mono h)) hω
    have h := tendsto_measure_iUnion_atTop (μ := law (orParameter q (m+1))) hm
    have he := witness_eq_union {ω | Conn G ω x y} (fun _ _ h hc => conn_mono G h hc)
      (finiteWitness_conn G x y)
    change {ω : Set E | Conn G ω x y} = ⋃ n, {ω | Conn G (ω ∩ (F n : Set E)) x y} at he
    rw [← he] at h
    have hr := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
    apply hr.congr'
    apply Filter.Eventually.of_forall
    intro n
    exact (twoPoint_restrict_edges G (orParameter q (m+1)) (F n) x y).symm
  obtain ⟨C,hCn,hC⟩ := exists_operator_of_matrix_tendsto B
    (fun x y => (twoPoint G (orParameter q (m+1)) x y : ℂ))
    (div_nonneg (norm_nonneg _) (sub_pos.mpr hq).le) hn (fun x y => by
      have hBm : ∀ n x y, B n (lp.single 2 y (1:ℂ)) x = (twoPoint (H n) (orParameter q (m+1)) x y : ℂ) := hB
      simp only [hBm]
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp (hlim x y))
  exact ⟨C,hC,hCn⟩

end ExhaustionSprinkling

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

section FiniteRusso
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


theorem bernoulliPolynomial_congr (s : Finset E) {f g : Finset E → ℝ}
    (h : ∀ t ⊆ s, f t = g t) (p : ℝ) :
    bernoulliPolynomial s f p = bernoulliPolynomial s g p := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [h t (Finset.mem_powerset.mp ht)]

theorem bernoulliPolynomial_sub (s : Finset E) (f g : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial s (fun t => f t-g t) p =
      bernoulliPolynomial s f p - bernoulliPolynomial s g p := by
  simp only [bernoulliPolynomial, sub_mul, Finset.sum_sub_distrib]


theorem hasDerivAt_bernoulliPolynomial (s : Finset E) (f : Finset E → ℝ) (p : ℝ) :
    HasDerivAt (bernoulliPolynomial s f)
      (∑ e ∈ s, bernoulliPolynomial (s.erase e) (fun t => f (insert e t)-f t) p) p := by
  induction s using Finset.induction_on generalizing f with
  | empty =>
    convert hasDerivAt_const p (f ∅) using 1 <;> try rfl
    · funext q
      exact bernoulliPolynomial_empty f q
  | @insert e s he ih =>
    have hd := (((hasDerivAt_const p 1).sub (hasDerivAt_id p)).mul (ih f)).add
      ((hasDerivAt_id p).mul (ih (fun t => f (insert e t))))
    have hf : bernoulliPolynomial (insert e s) f =
        fun q => (1-q)*bernoulliPolynomial s f q +
          q*bernoulliPolynomial s (fun t => f (insert e t)) q :=
      funext fun q => bernoulliPolynomial_insert s e he f q
    rw [hf]
    convert hd using 1 <;> try rfl
    have hs : ∑ a ∈ s, bernoulliPolynomial ((insert e s).erase a)
          (fun t => f (insert a t)-f t) p =
        (1-p)*(∑ a ∈ s, bernoulliPolynomial (s.erase a) (fun t => f (insert a t)-f t) p) +
        p*(∑ a ∈ s, bernoulliPolynomial (s.erase a)
          (fun t => f (insert e (insert a t))-f (insert e t)) p) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      have hae : e ≠ a := (ne_of_mem_of_not_mem ha he).symm
      rw [Finset.erase_insert_of_ne hae, bernoulliPolynomial_insert _ e
        (fun hh => he (Finset.mem_of_mem_erase hh))]
      congr 2
      apply bernoulliPolynomial_congr
      intro t _
      rw [Finset.insert_comm e a]
    simp only [Finset.sum_insert he, Finset.erase_insert he, zero_sub, neg_one_mul,
      one_mul, Pi.sub_apply, id_eq]
    rw [hs, bernoulliPolynomial_sub]
    ring

theorem bernoulliPolynomial_nonneg (s : Finset E) (f : Finset E → ℝ) (p : ℝ)
    (hp : p ∈ Set.Icc (0:ℝ) 1) (hf : ∀ t ⊆ s, 0 ≤ f t) :
    0 ≤ bernoulliPolynomial s f p := by
  apply Finset.sum_nonneg
  intro t ht
  exact mul_nonneg (mul_nonneg (hf t (Finset.mem_powerset.mp ht))
    (pow_nonneg hp.1 _)) (pow_nonneg (sub_nonneg.mpr hp.2) _)

theorem bernoulliPolynomial_mono (s : Finset E) (f g : Finset E → ℝ) (p : ℝ)
    (hp : p ∈ Set.Icc (0:ℝ) 1) (hfg : ∀ t ⊆ s, f t ≤ g t) :
    bernoulliPolynomial s f p ≤ bernoulliPolynomial s g p := by
  apply Finset.sum_le_sum
  intro t ht
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hfg t (Finset.mem_powerset.mp ht)) (pow_nonneg hp.1 _))
    (pow_nonneg (sub_nonneg.mpr hp.2) _)

 
theorem bernoulliPolynomial_union (s t : Finset E) (hdis : Disjoint s t)
    (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial (s ∪ t) f p =
      bernoulliPolynomial s (fun a => bernoulliPolynomial t (fun b => f (a ∪ b)) p) p := by
  induction s using Finset.induction_on generalizing f with
  | empty => simp
  | @insert e s he ih =>
    have hed : e ∉ t := (Finset.disjoint_insert_left.mp hdis).1
    have hst : Disjoint s t := (Finset.disjoint_insert_left.mp hdis).2
    rw [Finset.insert_union, bernoulliPolynomial_insert _ e (by simp [he, hed]),
      bernoulliPolynomial_insert s e he, ih hst, ih hst]
    congr 2
    apply bernoulliPolynomial_congr
    intro a _
    apply bernoulliPolynomial_congr
    intro b _
    rw [Finset.insert_union]

 

theorem bernoulliPolynomial_closed_difference (s : Finset E) (e : E) (he : e ∈ s)
    (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial s (fun t => if e ∈ t then 0 else f (insert e t)-f t) p =
      (1-p)*bernoulliPolynomial (s.erase e) (fun t => f (insert e t)-f t) p := by
  have hes : e ∉ s.erase e := Finset.notMem_erase e s
  conv_lhs => rw [← Finset.insert_erase he]
  rw [bernoulliPolynomial_insert _ e hes]
  have hc : bernoulliPolynomial (s.erase e)
      (fun t => if e ∈ t then 0 else f (insert e t)-f t) p =
      bernoulliPolynomial (s.erase e) (fun t => f (insert e t)-f t) p := by
    apply bernoulliPolynomial_congr
    intro t ht
    simp [show e ∉ t from fun h => hes (ht h)]
  rw [hc]
  simp

theorem closed_difference_russo (s : Finset E) (f : Finset E → ℝ) (p : ℝ) :
    (1-p)*deriv (bernoulliPolynomial s f) p =
      ∑ e ∈ s, bernoulliPolynomial s
        (fun t => if e ∈ t then 0 else f (insert e t)-f t) p := by
  rw [(hasDerivAt_bernoulliPolynomial s f p).deriv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  exact (bernoulliPolynomial_closed_difference s e he f p).symm


theorem finiteEventPolynomial_eq (s : Finset E) (A : Set (Set E)) (p : unitInterval) :
    finiteEventPolynomial s A (p : ℝ) = finiteProbability p s A := by
  unfold finiteEventPolynomial bernoulliPolynomial finiteProbability
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : (t : Set E) ∈ A <;> simp [ht]


theorem closedPivotal_difference (A : Set (Set E)) (hA : IsUpperSet A) (e : E)
    (t : Finset E) :
    (if (t : Set E) ∈ closedPivotal A e then (1:ℝ) else 0) =
    (if e ∈ t then 0 else
      (if ((insert e t : Finset E) : Set E) ∈ A then (1:ℝ) else 0) -
      (if (t : Set E) ∈ A then 1 else 0)) := by
  by_cases he : e ∈ t
  · simp [closedPivotal, he]
  · by_cases ha : (t : Set E) ∈ A
    · have hi : insert e (t : Set E) ∈ A := hA (Set.subset_insert e _) ha
      simp [closedPivotal, he, ha, hi]
    · by_cases hi : insert e (t : Set E) ∈ A <;> simp [closedPivotal, he, ha, hi]


end FiniteRusso

section ExteriorExposure
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


theorem mem_unexposed_of_conn (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {x y : V} (hx : x ∈ unexposed G Λ ω) (hxy : Conn G ω x y) :
    y ∈ unexposed G Λ ω := by
  intro z hyz
  exact hx z (hxy.trans hyz)

 
theorem conn_restrict_unexposed (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {x y : V} (hx : x ∈ unexposed G Λ ω) (hxy : Conn G ω x y) :
    Conn G (ω ∩ internalEdges G (unexposed G Λ ω)) x y := by
  induction hxy with
  | refl => exact conn_refl _ _ _
  | @tail y z hxy hyz ih =>
    obtain ⟨e,he,hends⟩ := hyz
    have hy : y ∈ unexposed G Λ ω := mem_unexposed_of_conn G Λ ω hx hxy
    have hz : z ∈ unexposed G Λ ω := mem_unexposed_of_conn G Λ ω hy (.single ⟨e,he,hends⟩)
    exact ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G _ e y z hends).mpr ⟨hy,hz⟩⟩,hends⟩

 
theorem unexposed_boundary_closed (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {e : E} {a b : V} (he : G e = s(a,b))
    (ha : a ∈ unexposed G Λ ω) (hb : b ∉ unexposed G Λ ω) : e ∉ ω := by
  intro ho
  exact hb (mem_unexposed_of_conn G Λ ω ha (.single ⟨e,ho,he⟩))

 

theorem unexposed_insert_crossing (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {e : E} {a b x : V} (he : G e = s(a,b))
    (hx : x ∈ unexposed G Λ ω) (_ha : a ∈ unexposed G Λ ω)
    (hb : b ∉ unexposed G Λ ω) :
    x ∉ unexposed G Λ (insert e ω) ↔
      Conn G (ω ∩ internalEdges G (unexposed G Λ ω)) x a := by
  classical
  constructor
  · intro hn
    obtain ⟨y,hxy,hy⟩ := by simpa [unexposed, not_forall, Classical.not_imp] using hn
    rcases (conn_insert_iff G ω e a b x y he).mp hxy with h | h | h
    · exact (hy (hx y h)).elim
    · exact conn_restrict_unexposed G Λ ω hx h.1
    · exact (hb (mem_unexposed_of_conn G Λ ω hx h.1)).elim
  · intro hxa hn
    have hxa' : Conn G ω x a := conn_mono G Set.inter_subset_left hxa
    apply hb
    intro y hby
    exact hn y ((conn_insert_iff G ω e a b x y he).mpr (Or.inr (Or.inl ⟨hxa',hby⟩)))

 
theorem not_mem_unexposed_of_conn (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {x y : V} (hx : x ∉ unexposed G Λ ω) (hxy : Conn G ω x y) :
    y ∉ unexposed G Λ ω := by
  intro hy
  exact hx (mem_unexposed_of_conn G Λ ω hy (conn_symm G ω hxy))

 
theorem conn_sdiff_internal_unexposed (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {x y : V} (hx : x ∉ unexposed G Λ ω) (hxy : Conn G ω x y) :
    Conn G (ω \ internalEdges G (unexposed G Λ ω)) x y := by
  induction hxy with
  | refl => exact conn_refl _ _ _
  | @tail y z hxy hyz ih =>
    obtain ⟨e,he,hends⟩ := hyz
    have hy : y ∉ unexposed G Λ ω := not_mem_unexposed_of_conn G Λ ω hx hxy
    exact ih.tail ⟨e,⟨he,fun hi => hy ((mem_internalEdges_of_ends G _ e y z hends).mp hi).1⟩,hends⟩

 
theorem unexposed_sdiff_internal (G : BondGraph V E) (Λ : Set V) (ω : Set E) :
    unexposed G Λ (ω \ internalEdges G (unexposed G Λ ω)) = unexposed G Λ ω := by
  ext x
  constructor
  · intro hx
    by_contra hn
    apply hn
    intro y hxy
    exact hx y (conn_sdiff_internal_unexposed G Λ ω hn hxy)
  · intro hx y hxy
    exact hx y (conn_mono G Set.sdiff_subset hxy)

 
theorem unexposed_union_internal (G : BondGraph V E) (Λ : Set V) (ω η : Set E)
    (hη : η ⊆ internalEdges G (unexposed G Λ ω)) :
    unexposed G Λ (ω ∪ η) = unexposed G Λ ω := by
  ext x
  constructor
  · intro hx y hxy
    exact hx y (conn_mono G Set.subset_union_left hxy)
  · intro hx y hxy
    suffices hy : y ∈ unexposed G Λ ω from unexposed_subset G Λ ω hy
    induction hxy with
    | refl => exact hx
    | @tail y z hxy hyz ih =>
      obtain ⟨e,hωe,he⟩ := hyz
      rcases hωe with ho | hηe
      · exact mem_unexposed_of_conn G Λ ω ih (.single ⟨e,ho,he⟩)
      · exact ((mem_internalEdges_of_ends G _ e y z he).mp (hη hηe)).2

 
theorem unexposed_union_eq_iff (G : BondGraph V E) (Λ S : Set V) (a b : Set E)
    (ha : a ⊆ internalEdges G S) (hb : Disjoint b (internalEdges G S)) :
    unexposed G Λ (a ∪ b) = S ↔ unexposed G Λ b = S := by
  constructor
  · intro h
    have he : (a ∪ b) \ internalEdges G S = b := by
      ext e
      constructor
      · rintro ⟨he,hn⟩
        exact he.resolve_left (fun he => hn (ha he))
      · intro he
        exact ⟨Or.inr he,fun hi => Set.disjoint_left.mp hb he hi⟩
    simpa only [h, he] using unexposed_sdiff_internal G Λ (a ∪ b)
  · intro h
    have he := unexposed_union_internal G Λ b a (h ▸ ha)
    simpa only [Set.union_comm b a,h] using he


theorem escapeEvent_isUpperSet (G : BondGraph V E) (Λ : Set V) (x : V) :
    IsUpperSet (escapeEvent G Λ x) := by
  intro ω η hωη hx hη
  apply hx
  intro y hxy
  exact hη y (conn_mono G hωη hxy)

 
theorem escape_closed_pivotal_iff (G : BondGraph V E) (Λ : Set V)
    (ω : Set E) (x : V) (e : E) :
    (e ∉ ω ∧ ω ∉ escapeEvent G Λ x ∧ insert e ω ∈ escapeEvent G Λ x) ↔
      x ∈ unexposed G Λ ω ∧ ∃ a b,
        G e = s(a,b) ∧ a ∈ unexposed G Λ ω ∧ b ∉ unexposed G Λ ω ∧
        Conn G (ω ∩ internalEdges G (unexposed G Λ ω)) x a := by
  classical
  constructor
  · rintro ⟨_,hx,hn⟩
    have hx' : x ∈ unexposed G Λ ω := by simpa [escapeEvent] using hx
    refine ⟨hx',?_⟩
    obtain ⟨⟨a,b⟩,he'⟩ := Sym2.mk_surjective (G e)
    have he : G e = s(a,b) := he'.symm
    obtain ⟨y,hxy,hy⟩ := by simpa [escapeEvent,unexposed,not_forall,Classical.not_imp] using hn
    rcases (conn_insert_iff G ω e a b x y he).mp hxy with h | h | h
    · exact (hy (hx' y h)).elim
    · exact ⟨a,b,he,mem_unexposed_of_conn G Λ ω hx' h.1,
        fun hb => hy (hb y h.2),conn_restrict_unexposed G Λ ω hx' h.1⟩
    · exact ⟨b,a,he.trans (Sym2.eq_swap ..),mem_unexposed_of_conn G Λ ω hx' h.1,
        fun ha => hy (ha y h.2),conn_restrict_unexposed G Λ ω hx' h.1⟩
  · rintro ⟨hx,a,b,he,ha,hb,hxa⟩
    exact ⟨unexposed_boundary_closed G Λ ω he ha hb,by simpa [escapeEvent] using hx,
      (unexposed_insert_crossing G Λ ω he hx ha hb).mpr hxa⟩

attribute [local instance] Classical.decEq

 theorem bernoulliPolynomial_mul_const (s : Finset E) (f : Finset E → ℝ) (c p : ℝ) :
    bernoulliPolynomial s (fun t => f t*c) p = bernoulliPolynomial s f p*c := by
  simp only [bernoulliPolynomial, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  ring

 theorem bernoulliPolynomial_const_mul (s : Finset E) (f : Finset E → ℝ) (c p : ℝ) :
    bernoulliPolynomial s (fun t => c*f t) p = c*bernoulliPolynomial s f p := by
  simpa only [mul_comm c] using bernoulliPolynomial_mul_const s f c p

 theorem bernoulliPolynomial_sum {ι : Type*} (s : Finset E) (I : Finset ι)
    (f : ι → Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial s (fun t => ∑ i ∈ I, f i t) p =
      ∑ i ∈ I, bernoulliPolynomial s (f i) p := by
  classical
  simp only [bernoulliPolynomial, Finset.sum_mul]
  exact Finset.sum_comm



theorem bernoulliPolynomial_exposure (G : BondGraph V E) (Λ S : Set V)
    (s t : Finset E) (hs : (s : Set E) ⊆ internalEdges G S)
    (ht : Disjoint (t : Set E) (internalEdges G S)) (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial (s ∪ t)
      (fun a => (if unexposed G Λ (a : Set E) = S then (1:ℝ) else 0) * f (a ∩ s)) p =
    bernoulliPolynomial t (fun b => if unexposed G Λ (b : Set E) = S then (1:ℝ) else 0) p *
      bernoulliPolynomial s f p := by
  have hdis : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact Set.disjoint_left.mp ht hf (hs he)
  rw [bernoulliPolynomial_union s t hdis]
  trans bernoulliPolynomial s (fun a =>
    bernoulliPolynomial t (fun b => if unexposed G Λ (b : Set E) = S then (1:ℝ) else 0) p * f a) p
  · apply bernoulliPolynomial_congr
    intro a ha
    rw [← bernoulliPolynomial_mul_const]
    apply bernoulliPolynomial_congr
    intro b hb
    have hab : unexposed G Λ ((a ∪ b : Finset E) : Set E) = S ↔
        unexposed G Λ (b : Set E) = S := by
      rw [Finset.coe_union]
      exact unexposed_union_eq_iff G Λ S _ _ (fun _ he => hs (ha he))
        (ht.mono_left (by exact_mod_cast hb))
    have hbs : b ∩ s = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp (hdis.symm.mono_left hb)
    rw [Finset.union_inter_distrib_right,Finset.inter_eq_left.mpr ha,hbs,Finset.union_empty]
    simp only [hab]
  · exact bernoulliPolynomial_const_mul s f _ p


theorem unexposedRegion_subset (G : BondGraph V E) (Λ : Finset V) (ω : Set E) :
    unexposedRegion G Λ ω ⊆ Λ := by
  intro x hx
  apply unexposed_subset G (Λ : Set V) ω
  simpa only [← coe_unexposedRegion,Finset.mem_coe] using hx

 
theorem bernoulliPolynomial_partition_region (G : BondGraph V E) (Λ : Finset V)
    (F : Finset E) (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial F f p = ∑ S ∈ Λ.powerset,
      bernoulliPolynomial F
        (fun t => if unexposed G (Λ : Set V) (t : Set E) = (S : Set V) then f t else 0) p := by
  rw [← bernoulliPolynomial_sum]
  apply bernoulliPolynomial_congr
  intro t _
  symm
  rw [Finset.sum_eq_single (unexposedRegion G Λ (t : Set E))]
  · simp
  · intro S _ hne
    have hh : unexposed G (Λ : Set V) (t : Set E) ≠ (S : Set V) := by
      intro he
      apply hne
      apply Finset.coe_injective
      exact he.symm.trans (coe_unexposedRegion G Λ (t : Set E)).symm
    simp [hh]
  · intro hn
    exact (hn (Finset.mem_powerset.mpr (unexposedRegion_subset G Λ (t : Set E)))).elim


 theorem internalSupport_subset (G : BondGraph V E) (S : Set V) (F : Finset E) :
    internalSupport G S F ⊆ F := Finset.filter_subset _ _

 theorem internalSupport_union_sdiff (G : BondGraph V E) (S : Set V) (F : Finset E) :
    internalSupport G S F ∪ (F \ internalSupport G S F) = F :=
  Finset.union_sdiff_of_subset (internalSupport_subset G S F)

 theorem coe_inter_internalSupport (G : BondGraph V E) (S : Set V) (F t : Finset E)
    (ht : t ⊆ F) : ((t ∩ internalSupport G S F : Finset E) : Set E) =
      (t : Set E) ∩ internalEdges G S := by
  ext e
  simp only [Finset.mem_coe,Finset.mem_inter,internalSupport,Finset.mem_filter,Set.mem_inter_iff]
  exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,ht h.1,h.2⟩⟩


 theorem regionProbability_nonneg (G : BondGraph V E) (Λ S : Set V)
    (F : Finset E) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ regionProbability G Λ S F p := by
  apply bernoulliPolynomial_nonneg _ _ _ hp
  intro t _
  split_ifs <;> norm_num

 
theorem bernoulliPolynomial_exposure_factor (G : BondGraph V E) (Λ S : Set V)
    (F : Finset E) (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial F
      (fun t => (if unexposed G Λ (t : Set E) = S then (1:ℝ) else 0) *
        f (t ∩ internalSupport G S F)) p =
      regionProbability G Λ S F p * bernoulliPolynomial (internalSupport G S F) f p := by
  let s := internalSupport G S F
  let t := F \ s
  have hs : (s : Set E) ⊆ internalEdges G S := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  have ht : Disjoint (t : Set E) (internalEdges G S) := by
    apply Set.disjoint_left.mpr
    intro e he hi
    have he' := Finset.mem_sdiff.mp he
    exact he'.2 (Finset.mem_filter.mpr ⟨he'.1,hi⟩)
  have he : s ∪ t = F := internalSupport_union_sdiff G S F
  have hq : bernoulliPolynomial t
      (fun b => if unexposed G Λ (b : Set E) = S then (1:ℝ) else 0) p =
      regionProbability G Λ S F p := by
    simpa only [he,mul_one,bernoulliPolynomial_const,regionProbability] using
      (bernoulliPolynomial_exposure G Λ S s t hs ht (fun _ => 1) p).symm
  simpa only [he,hq] using bernoulliPolynomial_exposure G Λ S s t hs ht f p


theorem finite_escape_russo (G : BondGraph V E) (Λ : Set V) (x : V)
    (F : Finset E) (p : ℝ) :
    (1-p)*deriv (finiteEventPolynomial F (escapeEvent G Λ x)) p =
      bernoulliPolynomial F (fun t => closedEscapeCount G Λ x F (t : Set E)) p := by
  unfold finiteEventPolynomial
  rw [closed_difference_russo]
  unfold closedEscapeCount
  rw [bernoulliPolynomial_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply bernoulliPolynomial_congr
  intro t _
  exact (closedPivotal_difference _ (escapeEvent_isUpperSet G Λ x) e t).symm

 
theorem closedEscapeCount_expectation (G : BondGraph V E) (Λ : Finset V) (x : V)
    (F : Finset E) (p : ℝ) :
    bernoulliPolynomial F (fun t => closedEscapeCount G Λ x F (t : Set E)) p =
      ∑ S ∈ Λ.powerset, if x ∈ S then
        regionProbability G Λ S F p * boundaryExpectation G S x F p else 0 := by
  rw [bernoulliPolynomial_partition_region G Λ F]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hx : x ∈ S
  · rw [ite_eq_left hx]
    unfold boundaryExpectation
    rw [← bernoulliPolynomial_exposure_factor G Λ S F
      (fun t => crossingCount G S x F (t : Set E)) p]
    apply bernoulliPolynomial_congr
    intro t ht
    by_cases hreg : unexposed G (Λ : Set V) (t : Set E) = (S : Set V)
    · simp only [hreg,ite_true,one_mul]
      apply Finset.sum_congr rfl
      intro e _
      have hc : (t : Set E) ∈ closedPivotal (escapeEvent G Λ x) e ↔
          crossingReach G S x ((t ∩ internalSupport G S F : Finset E) : Set E) e := by
        simpa only [closedPivotal,Set.mem_ofPred_eq,hreg,Finset.mem_coe,hx,true_and,
          coe_inter_internalSupport G S F t ht,crossingReach] using
          escape_closed_pivotal_iff G Λ (t : Set E) x e
      exact if_congr hc rfl rfl
    · simp [hreg]
  · rw [ite_eq_right hx,← bernoulliPolynomial_zero F p]
    apply bernoulliPolynomial_congr
    intro t _
    by_cases hreg : unexposed G (Λ : Set V) (t : Set E) = (S : Set V)
    · simp only [hreg,ite_true]
      apply Finset.sum_eq_zero
      intro e _
      have hn : (t : Set E) ∉ closedPivotal (escapeEvent G Λ x) e := by
        intro he
        have hh := ((escape_closed_pivotal_iff G Λ (t : Set E) x e).mp he).1
        apply hx
        simpa only [hreg,Finset.mem_coe] using hh
      simp [hn]
    · simp [hreg]

 
theorem finite_escape_complement (G : BondGraph V E) (Λ : Finset V) (x : V)
    (F : Finset E) (p : ℝ) :
    1-finiteEventPolynomial F (escapeEvent G Λ x) p =
      ∑ S ∈ Λ.powerset, if x ∈ S then regionProbability G Λ S F p else 0 := by
  have he : 1-finiteEventPolynomial F (escapeEvent G Λ x) p =
      bernoulliPolynomial F
        (fun t => if x ∈ unexposed G (Λ : Set V) (t : Set E) then (1:ℝ) else 0) p := by
    change 1-bernoulliPolynomial F (fun t => if (t : Set E) ∈ escapeEvent G Λ x then 1 else 0) p = _
    rw [show (1:ℝ) = bernoulliPolynomial F (fun _ => 1) p from (bernoulliPolynomial_const F 1 p).symm]
    rw [← bernoulliPolynomial_sub]
    apply bernoulliPolynomial_congr
    intro t _
    by_cases hx : x ∈ unexposed G (Λ : Set V) (t : Set E) <;> simp [escapeEvent,hx,bernoulliPolynomial_const]
  rw [he,bernoulliPolynomial_partition_region G Λ F]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hx : x ∈ S
  · rw [ite_eq_left hx]
    apply bernoulliPolynomial_congr
    intro t _
    by_cases hreg : unexposed G (Λ : Set V) (t : Set E) = (S : Set V) <;> simp [hreg,hx]
  · rw [ite_eq_right hx,← bernoulliPolynomial_zero F p]
    apply bernoulliPolynomial_congr
    intro t _
    by_cases hreg : unexposed G (Λ : Set V) (t : Set E) = (S : Set V) <;> simp [hreg,hx]

 

theorem finite_escape_differential_lower (G : BondGraph V E) (Λ : Finset V) (x : V)
    (F : Finset E) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1)
    (hcost : ∀ S ⊆ Λ, x ∈ S → 1 ≤ p*boundaryExpectation G (S : Set V) x F p) :
    1-finiteEventPolynomial F (escapeEvent G Λ x) p ≤
      p*(1-p)*deriv (finiteEventPolynomial F (escapeEvent G Λ x)) p := by
  rw [mul_assoc,finite_escape_russo,closedEscapeCount_expectation,finite_escape_complement,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hS
  by_cases hx : x ∈ S
  · simp only [ite_eq_left hx]
    have hq := regionProbability_nonneg G Λ S F p hp
    calc
      regionProbability G Λ S F p ≤
          regionProbability G Λ S F p * (p*boundaryExpectation G S x F p) :=
        le_mul_of_one_le_right hq (hcost S (Finset.mem_powerset.mp hS) hx)
      _ = p*(regionProbability G Λ S F p * boundaryExpectation G S x F p) := by ring
  · simp [hx]

 theorem bernoulliPolynomial_monotoneOn (F : Finset E) (f : Finset E → ℝ)
    (hf : ∀ a b, a ⊆ b → f a ≤ f b) :
    MonotoneOn (bernoulliPolynomial F f) (Set.Icc (0:ℝ) 1) := by
  have hd : Differentiable ℝ (bernoulliPolynomial F f) :=
    fun q => (hasDerivAt_bernoulliPolynomial F f q).differentiableAt
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hd.continuous.continuousOn hd.differentiableOn
  intro q hq
  have hq' : q ∈ Set.Icc (0:ℝ) 1 := interior_subset hq
  rw [(hasDerivAt_bernoulliPolynomial F f q).deriv]
  apply Finset.sum_nonneg
  intro e _
  apply bernoulliPolynomial_nonneg _ _ _ hq'
  intro t _
  exact sub_nonneg.mpr (hf t (insert e t) (Finset.subset_insert e t))

 theorem crossingCount_mono (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) {ω η : Set E} (h : ω ⊆ η) :
    crossingCount G S x F ω ≤ crossingCount G S x F η := by
  apply Finset.sum_le_sum
  intro e _
  have hh : crossingReach G S x ω e → crossingReach G S x η e := by
    rintro ⟨a,b,he,ha,hb,hc⟩
    exact ⟨a,b,he,ha,hb,conn_mono G h hc⟩
  by_cases hω : crossingReach G S x ω e
  · simp [hω,hh hω]
  · simp only [ite_eq_right hω]
    split_ifs <;> norm_num

 theorem boundaryExpectation_nonneg (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ boundaryExpectation G S x F p := by
  apply bernoulliPolynomial_nonneg _ _ _ hp
  intro t _
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> norm_num

 theorem boundaryExpectation_monotoneOn (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) : MonotoneOn (boundaryExpectation G S x F) (Set.Icc (0:ℝ) 1) := by
  apply bernoulliPolynomial_monotoneOn
  intro a b hab
  exact crossingCount_mono G S x F (by exact_mod_cast hab)

 theorem boundaryCost_monotoneOn (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) : MonotoneOn (fun p => p*boundaryExpectation G S x F p)
      (Set.Icc (0:ℝ) 1) := by
  intro p hp q hq hpq
  exact mul_le_mul hpq (boundaryExpectation_monotoneOn G S x F hp hq hpq)
    (boundaryExpectation_nonneg G S x F p hp) hq.1

 theorem finiteEventPolynomial_mem_Icc (F : Finset E) (A : Set (Set E))
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    finiteEventPolynomial F A p ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · apply bernoulliPolynomial_nonneg _ _ _ hp
    intro t _
    split_ifs <;> norm_num
  · calc
      finiteEventPolynomial F A p ≤ bernoulliPolynomial F (fun _ => 1) p := by
        apply bernoulliPolynomial_mono _ _ _ _ hp
        intro t _
        split_ifs <;> norm_num
      _ = 1 := bernoulliPolynomial_const F 1 p

 

theorem differential_escape_growth {f : ℝ → ℝ} {r p : ℝ}
    (hr : 0 < r) (hrp : r ≤ p) (hp : p < 1)
    (hf : Differentiable ℝ f) (hbound : ∀ q ∈ Set.Icc r p, f q ∈ Set.Icc (0:ℝ) 1)
    (hineq : ∀ q ∈ Set.Icc r p, 1-f q ≤ q*(1-q)*deriv f q) :
    1-Real.exp (r-p) ≤ f p := by
  have hd (q : ℝ) : HasDerivAt (fun u => Real.exp u*(1-f u))
      (Real.exp q*(1-f q)+Real.exp q*(0-deriv f q)) q :=
    (Real.hasDerivAt_exp q).mul ((hasDerivAt_const q 1).sub (hf q).hasDerivAt)
  have hanti : AntitoneOn (fun q => Real.exp q*(1-f q)) (Set.Icc r p) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc r p)
      (Real.continuous_exp.mul (continuous_const.sub hf.continuous)).continuousOn
      (fun q _ => (hd q).hasDerivWithinAt)
    intro q hq
    have hqi : q ∈ Set.Icc r p := interior_subset hq
    have hq0 : 0 < q := hr.trans_le hqi.1
    have hq1 : q < 1 := hqi.2.trans_lt hp
    have hcoef : 0 < q*(1-q) := mul_pos hq0 (sub_pos.mpr hq1)
    have hder : 0 ≤ deriv f q := nonneg_of_mul_nonneg_right
      ((sub_nonneg.mpr (hbound q hqi).2).trans (hineq q hqi)) hcoef
    have hc : q*(1-q) ≤ 1 := by nlinarith [sq_nonneg q]
    have hsmall : 1-f q ≤ deriv f q := (hineq q hqi).trans
      (mul_le_of_le_one_left hder hc)
    have hn := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos q).le
      (show 1-f q-deriv f q ≤ 0 by linarith)
    nlinarith only [hn]
  have hle := hanti (show r ∈ Set.Icc r p from ⟨le_rfl,hrp⟩)
    (show p ∈ Set.Icc r p from ⟨hrp,le_rfl⟩) hrp
  have he : Real.exp p*(1-f p) ≤ Real.exp r := by
    calc
      Real.exp p*(1-f p) ≤ Real.exp r*(1-f r) := hle
      _ ≤ Real.exp r := mul_le_of_le_one_right (Real.exp_pos r).le
        (by linarith [(hbound r ⟨le_rfl,hrp⟩).1])
  have hfin : 1-f p ≤ Real.exp (r-p) := by
    rw [Real.exp_sub]
    apply (le_div_iff₀ (Real.exp_pos p)).mpr
    simpa only [mul_comm] using he
  linarith

 

theorem finite_escape_probability_lower (G : BondGraph V E) (Λ : Finset V) (x : V)
    (F : Finset E) (r p : ℝ) (hr : 0 < r) (hrp : r < p) (hp : p < 1)
    (hcost : ∀ S ⊆ Λ, x ∈ S → 1 ≤ r*boundaryExpectation G (S : Set V) x F r) :
    0 < 1-Real.exp (r-p) ∧
      1-Real.exp (r-p) ≤ finiteEventPolynomial F (escapeEvent G Λ x) p := by
  have hrI : r ∈ Set.Icc (0:ℝ) 1 := ⟨hr.le,(hrp.trans hp).le⟩
  have hqI (q : ℝ) (hq : q ∈ Set.Icc r p) : q ∈ Set.Icc (0:ℝ) 1 :=
    ⟨hr.le.trans hq.1,hq.2.trans hp.le⟩
  refine ⟨sub_pos.mpr (Real.exp_lt_one_iff.mpr (sub_neg.mpr hrp)),?_⟩
  apply differential_escape_growth hr hrp.le hp
  · intro q
    exact (hasDerivAt_bernoulliPolynomial F _ q).differentiableAt
  · intro q hq
    exact finiteEventPolynomial_mem_Icc F _ q (hqI q hq)
  · intro q hq
    apply finite_escape_differential_lower G Λ x F q (hqI q hq)
    intro S hS hx
    exact (hcost S hS hx).trans (boundaryCost_monotoneOn G S x F hrI (hqI q hq) hq.1)

end ExteriorExposure

section SharpnessBridge
attribute [local instance] Classical.propDecidable Classical.decEq
open Filter Topology

theorem bernoulliPolynomial_map {F : Type*} (f : E ↪ F) (s : Finset E)
    (h : Finset F → ℝ) (p : ℝ) :
    bernoulliPolynomial (s.map f) h p =
      bernoulliPolynomial s (fun t => h (t.map f)) p := by
  induction s using Finset.induction_on generalizing h with
  | empty => simp
  | @insert e s he ih =>
    rw [Finset.map_insert,bernoulliPolynomial_insert _ (f e) (by simpa using he),
      bernoulliPolynomial_insert s e he,ih,ih]
    simp only [Finset.map_insert]

theorem finiteEventPolynomial_restrict (F : Finset E) (A : Set (Set E)) (p : unitInterval) :
    finiteEventPolynomial F A (p : ℝ) = (law p).real {ω | ω ∩ (F : Set E) ∈ A} := by
  let f : (F : Set E) ↪ E := ⟨Subtype.val,Subtype.val_injective⟩
  have hm : (Finset.univ : Finset (F : Set E)).map f = F := by
    ext e
    simp [f]
  have he : finiteEventPolynomial F A (p : ℝ) =
      finiteEventPolynomial (Finset.univ : Finset (F : Set E))
        {η | f '' η ∈ A} (p : ℝ) := by
    unfold finiteEventPolynomial
    calc
      bernoulliPolynomial F (fun t => if (t : Set E) ∈ A then 1 else 0) (p : ℝ) =
        bernoulliPolynomial (Finset.univ.map f) (fun t => if (t : Set E) ∈ A then 1 else 0) (p : ℝ) :=
          congrArg (fun H => bernoulliPolynomial H (fun t => if (t : Set E) ∈ A then 1 else 0) (p : ℝ)) hm.symm
      _ = _ := by
        rw [bernoulliPolynomial_map]
        apply bernoulliPolynomial_congr
        intro t _
        simp only [Finset.coe_map]
        rfl
  rw [he,finiteEventPolynomial_eq,finiteProbability_univ,← law_map_restrict p (F : Set E),
    measureReal_def,Measure.map_apply (measurable_set_restrict _) .of_discrete]
  congr 2
  ext ω
  have hh : f '' (Subtype.val ⁻¹' ω : Set (F : Set E)) = ω ∩ (F : Set E) := by
    ext e
    simp [f,and_comm]
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,hh]


theorem escapeEvent_restrict_incident (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (x : V) (ω : Set E) :
    ω ∩ (incidentSupport G hloc Λ : Set E) ∈ escapeEvent G Λ x ↔
      ω ∈ escapeEvent G Λ x := by
  constructor
  · exact escapeEvent_isUpperSet G Λ x Set.inter_subset_left
  · intro hx
    by_contra hn
    have hx' : x ∈ unexposed G Λ (ω ∩ (incidentSupport G hloc Λ : Set E)) := by
      simpa only [escapeEvent,Set.mem_ofPred_eq,not_not] using hn
    apply hx
    intro y hxy
    have hc : Conn G (ω ∩ (incidentSupport G hloc Λ : Set E)) x y := by
      induction hxy with
      | refl => exact conn_refl _ _ _
      | @tail a b hxa hab ih =>
        obtain ⟨e,he,heab⟩ := hab
        have ha : a ∈ Λ := hx' a ih
        have hF : e ∈ incidentSupport G hloc Λ :=
          (mem_incidentSupport G hloc Λ e).mpr ⟨a,ha,by simp [heab]⟩
        exact ih.tail ⟨e,⟨he,hF⟩,heab⟩
    exact hx' y hc

theorem finite_escape_eq_law (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (x : V) (p : unitInterval) :
    finiteEventPolynomial (incidentSupport G hloc Λ) (escapeEvent G Λ x) (p : ℝ) =
      (law p).real (escapeEvent G Λ x) := by
  rw [finiteEventPolynomial_restrict]
  congr 1
  ext ω
  exact escapeEvent_restrict_incident G hloc Λ x ω

theorem internal_edge_mem_incident (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) {e : E} (he : e ∈ internalEdges G (S : Set V)) :
    e ∈ incidentSupport G hloc S := by
  obtain ⟨⟨a,b⟩,hab⟩ := Sym2.mk_surjective (G e)
  have ha : a ∈ G e := by rw [← hab]; simp
  exact (mem_incidentSupport G hloc S e).mpr ⟨a,he a ha,ha⟩

theorem internalSupport_eq_of_incident_subset (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (F : Finset E) (hF : incidentSupport G hloc S ⊆ F) :
    internalSupport G S F = internalSupport G S (incidentSupport G hloc S) := by
  ext e
  simp only [internalSupport,Finset.mem_filter]
  exact ⟨fun h => ⟨internal_edge_mem_incident G hloc S h.2,h.2⟩,
    fun h => ⟨hF h.1,h.2⟩⟩

theorem crossingCount_eq_of_incident_subset (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (x : V) (F : Finset E) (hF : incidentSupport G hloc S ⊆ F) (ω : Set E) :
    crossingCount G S x F ω = crossingCount G S x (incidentSupport G hloc S) ω := by
  symm
  apply Finset.sum_subset hF
  intro e _ he
  have hn : ¬ crossingReach G S x ω e := by
    rintro ⟨a,b,hab,ha,_,_⟩
    exact he ((mem_incidentSupport G hloc S e).mpr ⟨a,ha,by simp [hab]⟩)
  simp [hn]

theorem boundaryExpectation_eq_of_incident_subset (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (x : V) (F : Finset E) (hF : incidentSupport G hloc S ⊆ F) (p : ℝ) :
    boundaryExpectation G S x F p =
      boundaryExpectation G S x (incidentSupport G hloc S) p := by
  unfold boundaryExpectation
  rw [internalSupport_eq_of_incident_subset G hloc S F hF]
  apply bernoulliPolynomial_congr
  intro t _
  exact crossingCount_eq_of_incident_subset G hloc S x F hF t


theorem measurableSet_escapeEvent (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (x : V) : MeasurableSet (escapeEvent G Λ x) := by
  let F := incidentSupport G hloc Λ
  have he : escapeEvent G Λ x =
      (fun ω => (Subtype.val ⁻¹' ω : Set (F : Set E))) ⁻¹'
        {η | Subtype.val '' η ∈ escapeEvent G Λ x} := by
    ext ω
    have hh : Subtype.val '' (Subtype.val ⁻¹' ω : Set (F : Set E)) = ω ∩ (F : Set E) := by
      ext e
      simp [and_comm]
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,hh]
    exact (escapeEvent_restrict_incident G hloc Λ x ω).symm
  rw [he]
  exact MeasurableSet.preimage .of_discrete (measurable_set_restrict _)

theorem escapeEvent_antitone_domain (G : BondGraph V E) {S Λ : Set V} (hS : S ⊆ Λ)
    (x : V) : escapeEvent G Λ x ⊆ escapeEvent G S x := by
  intro ω hω hn
  apply hω
  intro y hxy
  exact hS (hn y hxy)

theorem vertexExhaustion_mono [Encodable V] :
    Monotone (vertexExhaustion : ℕ → Finset V) := by
  intro m n h x hx
  simp only [vertexExhaustion,Finset.mem_preimage,Finset.mem_range] at hx ⊢
  exact hx.trans_le h

theorem subset_vertexExhaustion [Encodable V] (S : Finset V) :
    ∃ n, S ⊆ vertexExhaustion n := by
  refine ⟨S.sup Encodable.encode+1,?_⟩
  intro x hx
  simp only [vertexExhaustion,Finset.mem_preimage,Finset.mem_range]
  exact Nat.lt_succ_of_le (Finset.le_sup hx)

theorem infinite_cluster_eq_iInter_escape [Encodable V] (G : BondGraph V E) (x : V) :
    {ω | (cluster G ω x).Infinite} = ⋂ n, escapeEvent G (vertexExhaustion (V := V) n : Set V) x := by
  ext ω
  simp only [Set.mem_ofPred_eq,Set.mem_iInter]
  constructor
  · intro hi n hn
    exact hi ((vertexExhaustion n).finite_toSet.subset (by
      intro y hy; exact hn y hy))
  · intro he hf
    obtain ⟨n,hn⟩ := subset_vertexExhaustion hf.toFinset
    apply he n
    intro y hy
    exact hn (hf.mem_toFinset.mpr hy)

 
theorem infinite_cluster_probability_ge_of_escape [Countable V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (p : unitInterval) (c : ℝ)
    (hc : ∀ Λ : Finset V, c ≤ (law p).real (escapeEvent G Λ x)) :
    c ≤ (law p).real {ω | (cluster G ω x).Infinite} := by
  let := Encodable.ofCountable V
  rw [infinite_cluster_eq_iInter_escape]
  have hm : Antitone (fun n => escapeEvent G (vertexExhaustion (V := V) n : Set V) x) := by
    intro m n h
    exact escapeEvent_antitone_domain G (by exact_mod_cast vertexExhaustion_mono h) x
  have ht := tendsto_measure_iInter_atTop (μ := law p)
    (fun n => (measurableSet_escapeEvent G hloc (vertexExhaustion n) x).nullMeasurableSet)
    hm ⟨0,measure_ne_top _ _⟩
  have hr := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  exact ge_of_tendsto hr (Eventually.of_forall (fun n => hc (vertexExhaustion n)))

 

theorem infinite_cluster_probability_pos_of_bad_cost [Countable V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (r p : unitInterval)
    (hr : 0 < r) (hrp : r < p) (hp : p < 1)
    (hcost : ∀ S : Finset V, x ∈ S → 1 ≤ boundaryCost G hloc S x (r : ℝ)) :
    0 < (law p).real {ω | (cluster G ω x).Infinite} := by
  have hc : 0 < 1-Real.exp ((r:ℝ)-(p:ℝ)) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (sub_neg.mpr hrp))
  apply hc.trans_le
  apply infinite_cluster_probability_ge_of_escape G hloc x p
  intro Λ
  rw [← finite_escape_eq_law G hloc Λ x p]
  apply (finite_escape_probability_lower G Λ x (incidentSupport G hloc Λ)
    (r:ℝ) (p:ℝ) hr hrp hp ?_).2
  intro S hS hx
  rw [boundaryExpectation_eq_of_incident_subset G hloc S x _ (incidentSupport_mono G hloc hS)]
  exact hcost S hx

theorem pc_le_of_infinite_cluster_probability_pos (G : BondGraph V E)
    (x : V) (p : unitInterval) (hp : 0 < (law p).real {ω | (cluster G ω x).Infinite}) :
    pc G ≤ p := by
  apply sInf_le
  have hh : 0 < law p {ω | (cluster G ω x).Infinite} := (ENNReal.toReal_pos_iff.mp hp).1
  apply hh.trans_le
  apply measure_mono
  intro ω hω
  exact ⟨cluster G ω x,hω,x,rfl⟩

 
theorem exists_subcritical_testSet [Countable V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (p : unitInterval) (hp : p < pc G) (x : V) :
    ∃ S : Finset V, x ∈ S ∧ boundaryCost G hloc S x (p:ℝ) < 1 := by
  by_cases hz : p = 0
  · exact ⟨{x},by simp,by simp [hz,boundaryCost]⟩
  · have hp0 : 0 < p := bot_lt_iff_ne_bot.mpr hz
    by_contra! hn
    obtain ⟨q,hpq,hqc⟩ := exists_between hp
    have hq1 : q < 1 := hqc.trans_le (show pc G ≤ 1 from (pc G).2.2)
    have hs := infinite_cluster_probability_pos_of_bad_cost G hloc x p q hp0 hpq hq1 hn
    exact (not_le_of_gt hqc) (pc_le_of_infinite_cluster_probability_pos G x q hs)

theorem internalEdges_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (S : Set V) (e : E) :
    b e ∈ internalEdges G (a '' S) ↔ e ∈ internalEdges G S := by
  constructor
  · intro he x hx
    have hh := he (a x) (by rw [h e]; exact Sym2.mem_map.mpr ⟨x,hx,rfl⟩)
    simpa using hh
  · intro he y hy
    rw [h e,Sym2.mem_map] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    exact Set.mem_image_of_mem a (he x hx)

theorem crossingReach_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (S : Set V) (x : V) (ω : Set E) (e : E) :
    crossingReach G (a '' S) (a x) (b '' ω) (b e) ↔ crossingReach G S x ω e := by
  constructor
  · rintro ⟨c,d,he,hc,hd,hconn⟩
    have he' : G e = s(a.symm c,a.symm d) := by
      have hh := congrArg (Sym2.map a.symm) he
      rw [h e,Sym2.map_map,Equiv.symm_comp_self,Sym2.map_id,Sym2.map_mk] at hh
      exact hh
    refine ⟨a.symm c,a.symm d,he',?_,?_,?_⟩
    · simpa using hc
    · simpa using hd
    · have hh := (conn_aut_iff G h (b '' ω) x (a.symm c)).mpr (by simpa using hconn)
      simpa only [Set.preimage_image_eq _ b.injective] using hh
  · rintro ⟨c,d,he,hc,hd,hconn⟩
    refine ⟨a c,a d,?_,by simpa using hc,by simpa using hd,conn_aut G h hconn⟩
    rw [h e,he,Sym2.map_mk]

theorem internalSupport_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (S : Set V) (F : Finset E) :
    internalSupport G (a '' S) (F.map b.toEmbedding) =
      (internalSupport G S F).map b.toEmbedding := by
  ext e
  obtain ⟨d,rfl⟩ := b.surjective e
  simp [internalSupport,internalEdges_aut_iff G h]

theorem crossingCount_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (S : Set V) (x : V) (F : Finset E) (ω : Set E) :
    crossingCount G (a '' S) (a x) (F.map b.toEmbedding) (b '' ω) =
      crossingCount G S x F ω := by
  simp only [crossingCount,Finset.sum_map,Equiv.toEmbedding_apply,crossingReach_aut_iff G h]

theorem boundaryExpectation_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (S : Set V) (x : V) (F : Finset E) (p : ℝ) :
    boundaryExpectation G (a '' S) (a x) (F.map b.toEmbedding) p =
      boundaryExpectation G S x F p := by
  unfold boundaryExpectation
  rw [internalSupport_aut G h,bernoulliPolynomial_map]
  apply bernoulliPolynomial_congr
  intro t _
  simp only [Finset.coe_map,Equiv.coe_toEmbedding]
  exact crossingCount_aut G h S x F t

theorem boundaryCost_aut (G : BondGraph V E) (hloc : LocallyFinite G)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) (S : Finset V) (x : V) (p : ℝ) :
    boundaryCost G hloc (S.map a.toEmbedding) (a x) p = boundaryCost G hloc S x p := by
  unfold boundaryCost
  rw [incidentSupport_aut G hloc h,Finset.coe_map]
  exact congrArg (p*·) (boundaryExpectation_aut G h S x (incidentSupport G hloc S) p)

 

theorem exists_uniform_subcritical_testSets [Countable V] [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) :
    ∃ (L : ℕ) (a : ℝ), 0 ≤ a ∧ a < 1 ∧ ∀ x, ∃ S : Finset V,
      x ∈ S ∧ S.card ≤ L ∧ boundaryCost G hloc S x (p:ℝ) ≤ a := by
  obtain ⟨O,hO⟩ := hqt
  choose S hmem hcost using exists_subcritical_testSet G hloc p hp
  have hOn : O.Nonempty := by
    obtain ⟨o,ho,_⟩ := hO (Classical.arbitrary V)
    exact ⟨o,ho⟩
  let L := O.sup (fun x => (S x).card)
  let a := max 0 (O.sup' hOn (fun x => boundaryCost G hloc (S x) x (p:ℝ)))
  refine ⟨L,a,le_max_left _ _,?_,?_⟩
  · apply max_lt zero_lt_one
    exact (Finset.sup'_lt_iff hOn).mpr (fun x _ => hcost x)
  · intro x
    obtain ⟨o,ho,α,β,hαβ,rfl⟩ := hO x
    refine ⟨(S o).map α.toEmbedding,?_,?_,?_⟩
    · simp only [Finset.mem_map,Equiv.toEmbedding_apply]
      exact ⟨o,hmem o,rfl⟩
    · simpa only [Finset.card_map] using Finset.le_sup (f := fun x => (S x).card) ho
    · rw [boundaryCost_aut G hloc hαβ]
      exact (Finset.le_sup' (f := fun x => boundaryCost G hloc (S x) x (p:ℝ)) ho).trans
        (le_max_right _ _)

end SharpnessBridge

section SharpnessSusceptibility
open Filter Topology
attribute [local instance] Classical.propDecidable Classical.decEq


theorem cut_spec [Nonempty V] (G : BondGraph V E) (S : Set V) {e : E}
    (he : CutExists G S e) :
    G e = s(cutInside G S e,cutOutside G S e) ∧
      cutInside G S e ∈ S ∧ cutOutside G S e ∉ S := by
  simpa only [cutInside,cutOutside,dite_eq_left he] using he.choose_spec.choose_spec

theorem cut_unique [Nonempty V] (G : BondGraph V E) (S : Set V) {e : E} {a b : V}
    (he : G e = s(a,b)) (ha : a ∈ S) (hb : b ∉ S) :
    a = cutInside G S e ∧ b = cutOutside G S e := by
  have hc := cut_spec G S (e := e) ⟨a,b,he,ha,hb⟩
  have hh := Sym2.eq_iff.mp (he.symm.trans hc.1)
  rcases hh with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact ⟨h₁,h₂⟩
  · exact (hc.2.2 (h₁ ▸ ha)).elim

theorem crossingReach_upper (G : BondGraph V E) (S : Set V) (x : V) (e : E) :
    IsUpperSet {ω | crossingReach G S x (ω ∩ internalEdges G S) e} := by
  rintro ω η h ⟨a,b,he,ha,hb,hconn⟩
  exact ⟨a,b,he,ha,hb,conn_mono G (Set.inter_subset_inter_left _ h) hconn⟩

theorem finiteWitness_crossingReach (G : BondGraph V E) (S : Set V) (x : V) (e : E) :
    FiniteWitness {ω | crossingReach G S x (ω ∩ internalEdges G S) e} := by
  rintro ω ⟨a,b,he,ha,hb,hconn⟩
  obtain ⟨t,ht,hc⟩ := finiteWitness_inter {η | Conn G η x a} (finiteWitness_conn G x a)
    (internalEdges G S) ω hconn
  exact ⟨t,ht,a,b,he,ha,hb,hc⟩

 
theorem conn_first_exit [Nonempty V] (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (U : Set E) {ω : Set E} {x y : V} (hx : x ∈ S)
    (hxy : Conn G (ω ∩ U) x y) :
    y ∈ S ∨ ∃ e ∈ incidentSupport G hloc S,
      ω ∈ DisjointOccurrence {η | crossingReach G S x (η ∩ internalEdges G S) e}
        (DisjointOccurrence {η | e ∈ η} {η | Conn G (η ∩ U) (cutOutside G S e) y}) := by
  obtain ⟨l,hl,hn,ho⟩ := conn_exists_bond_trail G hxy
  rcases hl.first_outside (internalEdges G S) with hall |
      ⟨a,b,e,l₁,l₂,heq,h₁,he,h₂,hfirst,hnot⟩
  · exact Or.inl (conn_internal_endpoint G S hx (hl.conn fun e he => ⟨(ho e he).1,hall e he⟩))
  · subst l
    have hnod := List.nodup_append.mp hn
    have hen : e ∉ l₂ := (List.nodup_cons.mp hnod.2.1).1
    have ha : a ∈ S := conn_internal_endpoint G S hx
      (h₁.conn (ω := ω ∩ internalEdges G S) fun d hd =>
        ⟨(ho d (List.mem_append_left _ hd)).1,hfirst d hd⟩)
    have hb : b ∉ S := fun hb => hnot ((mem_internalEdges_of_ends G S e a b he).mpr ⟨ha,hb⟩)
    have hbe := (cut_unique G S he ha hb).2
    refine Or.inr ⟨e,(mem_incidentSupport G hloc S e).mpr ⟨a,ha,by simp [he]⟩,
      l₁.toFinset,(e::l₂).toFinset,?_,?_,?_,?_,?_⟩
    · intro d hd
      exact (ho d (List.mem_append_left _ (List.mem_toFinset.mp hd))).1
    · intro d hd
      exact (ho d (List.mem_append_right _ (List.mem_toFinset.mp hd))).1
    · apply Finset.disjoint_left.mpr
      intro d hd hd'
      exact hnod.2.2 d (List.mem_toFinset.mp hd) d (List.mem_toFinset.mp hd') rfl
    · exact ⟨a,b,he,ha,hb,h₁.conn (fun d hd => ⟨by simpa using hd,hfirst d hd⟩)⟩
    · refine ⟨{e},l₂.toFinset,by simp,by simp,by simpa using hen,by simp,?_⟩
      rw [← hbe]
      exact h₂.conn fun d hd => ⟨by simpa using hd,
        (ho d (List.mem_append_right _ (List.mem_cons_of_mem e hd))).2⟩

 
theorem boundaryExpectation_eq_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (x : V) (p : unitInterval) :
    boundaryExpectation G S x (incidentSupport G hloc S) (p:ℝ) =
      ∑ e ∈ incidentSupport G hloc S,
        (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} := by
  have hI : (internalSupport G S (incidentSupport G hloc S) : Set E) = internalEdges G S := by
    ext e
    simp only [Finset.mem_coe,internalSupport,Finset.mem_filter]
    exact ⟨And.right,fun he => ⟨internal_edge_mem_incident G hloc S he,he⟩⟩
  unfold boundaryExpectation crossingCount bernoulliPolynomial
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  change finiteEventPolynomial (internalSupport G S (incidentSupport G hloc S))
    {ω | crossingReach G S x ω e} (p:ℝ) = _
  rw [finiteEventPolynomial_restrict,hI]
  rfl

 
theorem domainTwoPoint_first_exit [Countable E] [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (S : Finset V) (Λ : Set V) (p : unitInterval)
    (x y : V) (hx : x ∈ S) :
    domainTwoPoint G Λ p x y ≤ (if y ∈ S then (1:ℝ) else 0) +
      ∑ e ∈ incidentSupport G hloc S,
        (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} *
          (p:ℝ) * domainTwoPoint G Λ p (cutOutside G S e) y := by
  by_cases hy : y ∈ S
  · have hnon : 0 ≤ ∑ e ∈ incidentSupport G hloc S,
        (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} *
          (p:ℝ) * domainTwoPoint G Λ p (cutOutside G S e) y := by
      apply Finset.sum_nonneg
      intro e _
      exact mul_nonneg (mul_nonneg (measureReal_nonneg) p.2.1) measureReal_nonneg
    simpa only [ite_eq_left hy,domainTwoPoint] using (measureReal_le_one (μ := law p)
      (s := {ω | Conn G (ω ∩ internalEdges G Λ) x y})).trans (le_add_of_nonneg_right hnon)
  · simp only [ite_eq_right hy,zero_add]
    let A := fun e => {ω | crossingReach G S x (ω ∩ internalEdges G S) e}
    let B := fun e => {ω | Conn G (ω ∩ internalEdges G Λ) (cutOutside G S e) y}
    let F := incidentSupport G hloc S
    let C := fun e => DisjointOccurrence (A e) (DisjointOccurrence {ω | e ∈ ω} (B e))
    have hsub : {ω | Conn G (ω ∩ internalEdges G Λ) x y} ⊆ ⋃ e ∈ F, C e := by
      intro ω hω
      rcases conn_first_exit G hloc S (internalEdges G Λ) hx hω with h | ⟨e,he,h⟩
      · exact (hy h).elim
      · exact Set.mem_iUnion.mpr ⟨e,Set.mem_iUnion.mpr ⟨he,h⟩⟩
    calc
      domainTwoPoint G Λ p x y ≤ (law p).real (⋃ e ∈ F, C e) := measureReal_mono (μ := law p) hsub (measure_ne_top _ _)
      _ ≤ ∑ e ∈ F, (law p).real (C e) := measureReal_biUnion_finset_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro e _
        have hB : IsUpperSet (B e) := fun _ _ h hc =>
          conn_mono G (Set.inter_subset_inter_left _ h) hc
        have hfB : FiniteWitness (B e) := finiteWitness_inter _
          (finiteWitness_conn G _ _) (internalEdges G Λ)
        have hb := bk p (A e) (DisjointOccurrence {ω | e ∈ ω} (B e))
          (crossingReach_upper G S x e) (disjointOccurrence_upper _ _)
          (finiteWitness_crossingReach G S x e) (finiteWitness_disjointOccurrence _ _)
        have hb' := bk p {ω | e ∈ ω} (B e) (fun _ _ h he => h he) hB (finiteWitness_edge e) hfB
        have heq : (law p).real {ω : Set E | e ∈ ω} = (p:ℝ) := by
          simpa using finite_open_probability p {e}
        rw [heq] at hb'
        calc
          (law p).real (C e) ≤ (law p).real (A e) * (law p).real
              (DisjointOccurrence {ω | e ∈ ω} (B e)) := hb
          _ ≤ (law p).real (A e) * ((p:ℝ) * (law p).real (B e)) :=
            mul_le_mul_of_nonneg_left hb' measureReal_nonneg
          _ = _ := (mul_assoc _ _ _).symm

theorem conn_internal_eq_or_mem (G : BondGraph V E) (S : Set V) {ω : Set E} {x y : V}
    (h : Conn G (ω ∩ internalEdges G S) x y) : x = y ∨ x ∈ S ∧ y ∈ S := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    have he' := (mem_internalEdges_of_ends G S e a b heq).mp he.2
    right
    exact ⟨ih.elim (fun h => h.symm ▸ he'.1) And.left,he'.2⟩

theorem domainTwoPoint_zero_of_outside (G : BondGraph V E) (S : Set V) (p : unitInterval)
    {x y : V} (hx : x ∉ S) (hy : y ∈ S) : domainTwoPoint G S p x y = 0 := by
  have he : {ω | Conn G (ω ∩ internalEdges G S) x y} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω h
    rcases conn_internal_eq_or_mem G S h with rfl | h
    · exact hx hy
    · exact hx h.1
  simp only [domainTwoPoint,he,measureReal_empty]

theorem domainRow_le_boundaryCost [Countable E] [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (S Λ : Finset V) (p : unitInterval) (x : V) (hx : x ∈ S)
    (H : ℝ) (hH : ∀ z, ∑ y ∈ Λ, domainTwoPoint G Λ p z y ≤ H) :
    (∑ y ∈ Λ, domainTwoPoint G Λ p x y) ≤ S.card + boundaryCost G hloc S x (p:ℝ) * H := by
  have hind : (∑ y ∈ Λ, if y ∈ S then (1:ℝ) else 0) ≤ (S.card:ℝ) := by
    simp only [← Finset.sum_filter]
    simpa using (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card
      (show Λ.filter (fun y => y ∈ S) ⊆ S from fun y hy => (Finset.mem_filter.mp hy).2))
  calc
    (∑ y ∈ Λ, domainTwoPoint G Λ p x y) ≤
        ∑ y ∈ Λ, ((if y ∈ S then (1:ℝ) else 0) +
          ∑ e ∈ incidentSupport G hloc S,
            (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} *
              (p:ℝ) * domainTwoPoint G Λ p (cutOutside G S e) y) :=
      Finset.sum_le_sum fun y _ => domainTwoPoint_first_exit G hloc S Λ p x y hx
    _ = (∑ y ∈ Λ, if y ∈ S then (1:ℝ) else 0) +
        ∑ e ∈ incidentSupport G hloc S,
          (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} *
            (p:ℝ) * ∑ y ∈ Λ, domainTwoPoint G Λ p (cutOutside G S e) y := by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
      simp only [← Finset.mul_sum]
    _ ≤ S.card + ∑ e ∈ incidentSupport G hloc S,
          (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} * (p:ℝ) * H := by
      apply add_le_add hind
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_left (hH _) (mul_nonneg measureReal_nonneg p.2.1)
    _ = S.card + boundaryCost G hloc S x (p:ℝ) * H := by
      unfold boundaryCost
      rw [boundaryExpectation_eq_sum]
      simp only [← Finset.sum_mul]
      ring

theorem domainRow_uniform_bound [Countable E] [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (p : unitInterval) (L : ℕ) (a : ℝ) (ha : a < 1)
    (htest : ∀ x, ∃ S : Finset V, x ∈ S ∧ S.card ≤ L ∧ boundaryCost G hloc S x (p:ℝ) ≤ a)
    (Λ : Finset V) (x : V) :
    (∑ y ∈ Λ, domainTwoPoint G Λ p x y) ≤ (L:ℝ)/(1-a) := by
  by_cases hΛ : Λ.Nonempty
  · let row := fun z => ∑ y ∈ Λ, domainTwoPoint G Λ p z y
    obtain ⟨z,hz,hmax⟩ := Λ.exists_max_image row hΛ
    have hnon : 0 ≤ row z := Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
    have hH : ∀ w, row w ≤ row z := by
      intro w
      by_cases hw : w ∈ Λ
      · exact hmax w hw
      · have he : row w = 0 := by
          apply Finset.sum_eq_zero
          intro y hy
          exact domainTwoPoint_zero_of_outside G Λ p hw hy
        rwa [he]
    obtain ⟨S,hS,hcard,hcost⟩ := htest z
    have h := domainRow_le_boundaryCost G hloc S Λ p z hS (row z) hH
    have hL : (S.card:ℝ) ≤ (L:ℝ) := Nat.cast_le.mpr hcard
    have hc := mul_le_mul_of_nonneg_right hcost hnon
    have hrow : row z ≤ (L:ℝ)/(1-a) := (le_div_iff₀ (sub_pos.mpr ha)).mpr (by nlinarith)
    exact (hH x).trans hrow
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hΛ,Finset.sum_empty]
    exact div_nonneg (Nat.cast_nonneg _) (sub_pos.mpr ha).le

theorem internalEdges_mono (G : BondGraph V E) {S T : Set V} (h : S ⊆ T) :
    internalEdges G S ⊆ internalEdges G T := fun _ he x hx => h (he x hx)

theorem exists_internal_vertexExhaustion [Encodable V] (G : BondGraph V E) (e : E) :
    ∃ n, e ∈ internalEdges G (vertexExhaustion (V := V) n : Set V) := by
  obtain ⟨⟨a,b⟩,hab⟩ := Sym2.mk_surjective (G e)
  obtain ⟨n,hn⟩ := subset_vertexExhaustion ({a,b} : Finset V)
  refine ⟨n,?_⟩
  rw [mem_internalEdges_of_ends G _ e a b hab.symm]
  exact ⟨hn (by simp),hn (by simp)⟩

theorem conn_domain_exhaustion [Encodable V] (G : BondGraph V E) {ω : Set E} {x y : V}
    (h : Conn G ω x y) :
    ∃ n, Conn G (ω ∩ internalEdges G (vertexExhaustion (V := V) n : Set V)) x y := by
  induction h with
  | refl => exact ⟨0,conn_refl _ _ _⟩
  | @tail a b hxa hab ih =>
    obtain ⟨n,hn⟩ := ih
    obtain ⟨e,he,heq⟩ := hab
    obtain ⟨m,hm⟩ := exists_internal_vertexExhaustion G e
    refine ⟨max n m,?_⟩
    have hnm := internalEdges_mono G (show (vertexExhaustion (V := V) n : Set V) ⊆
        (vertexExhaustion (V := V) (max n m) : Set V) from vertexExhaustion_mono (le_max_left n m))
    have hmm := internalEdges_mono G (show (vertexExhaustion (V := V) m : Set V) ⊆
        (vertexExhaustion (V := V) (max n m) : Set V) from vertexExhaustion_mono (le_max_right n m))
    exact (conn_mono G (Set.inter_subset_inter_right _ hnm) hn).tail ⟨e,⟨he,hmm hm⟩,heq⟩

theorem tendsto_domainTwoPoint [Encodable V] (G : BondGraph V E) (p : unitInterval) (x y : V) :
    Tendsto (fun n => domainTwoPoint G (vertexExhaustion (V := V) n : Set V) p x y)
      atTop (𝓝 (twoPoint G p x y)) := by
  have hm : Monotone (fun n => {ω | Conn G
      (ω ∩ internalEdges G (vertexExhaustion (V := V) n : Set V)) x y}) := by
    intro m n h ω hc
    exact conn_mono G (Set.inter_subset_inter_right _ (internalEdges_mono G
      (show (vertexExhaustion (V := V) m : Set V) ⊆ (vertexExhaustion (V := V) n : Set V) from
        vertexExhaustion_mono h))) hc
  have he : (⋃ n, {ω | Conn G (ω ∩ internalEdges G (vertexExhaustion (V := V) n : Set V)) x y}) =
      {ω | Conn G ω x y} := by
    ext ω
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
    exact ⟨fun ⟨n,h⟩ => conn_mono G Set.inter_subset_left h,conn_domain_exhaustion G⟩
  have h := tendsto_measure_iUnion_atTop (μ := law p) hm
  rw [he] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

 
theorem subcritical_row_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x (F : Finset V), ∑ y ∈ F, twoPoint G p x y ≤ C := by
  let : Encodable V := Encodable.ofCountable V
  obtain ⟨L,a,_,ha,htest⟩ := exists_uniform_subcritical_testSets G hloc hqt p hp
  refine ⟨(L:ℝ)/(1-a),div_nonneg (Nat.cast_nonneg _) (sub_pos.mpr ha).le,?_⟩
  intro x F
  apply le_of_tendsto (tendsto_finsetSum F (fun y _ => tendsto_domainTwoPoint G p x y))
  obtain ⟨N,hN⟩ := subset_vertexExhaustion F
  filter_upwards [eventually_ge_atTop N] with n hn
  have hFn : F ⊆ vertexExhaustion n := hN.trans (vertexExhaustion_mono hn)
  exact (Finset.sum_le_sum_of_subset_of_nonneg hFn (fun _ _ _ => measureReal_nonneg)).trans
    (domainRow_uniform_bound G hloc p L a ha htest (vertexExhaustion n) x)

 
theorem operatorBounded_of_lt_pc [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) : OperatorBounded G p := by
  obtain ⟨C,hC,hrow⟩ := subcritical_row_bound G hloc hqt p hp
  obtain ⟨A,_,hA⟩ := exists_operator_of_row_column_bound (twoPoint G p) C hC
    (twoPoint_nonneg G p) hrow (fun y F => by
      simpa only [twoPoint_symm G p] using hrow y F)
  exact ⟨A,hA⟩

end SharpnessSusceptibility

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


theorem levelIndicator_eq (a : ℝ) :
    levelIndicator a = Set.indicator (Set.Ico 0 a) (fun _ => (1:ℝ)) := by
  funext t
  simp [levelIndicator, Set.indicator_apply, Set.mem_Ico]

theorem integrable_levelIndicator (a : ℝ) : Integrable (levelIndicator a) := by
  rw [levelIndicator_eq]
  exact (integrableOn_const (isCompact_Icc.measure_lt_top.ne) :
    IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Icc 0 a)).mono_set
      Set.Ico_subset_Icc_self |>.integrable_indicator measurableSet_Ico

theorem integral_levelIndicator {a : ℝ} (ha : 0 ≤ a) :
    ∫ t, levelIndicator a t = a := by
  rw [levelIndicator_eq, integral_indicator measurableSet_Ico]
  simp [ha]

theorem abs_sub_levelIndicator {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (fun t => |levelIndicator a t - levelIndicator b t|) =
      Set.indicator (Set.Ico (min a b) (max a b)) (fun _ => (1:ℝ)) := by
  funext t
  rcases le_total a b with hab | hba
  · simp only [min_eq_left hab, max_eq_right hab, Set.indicator_apply, Set.mem_Ico,
      levelIndicator]
    by_cases ht : 0 ≤ t
    · by_cases hta : t < a
      · have htb : t < b := hta.trans_le hab
        have hna : ¬a ≤ t := not_le.mpr hta
        simp [ht,hta,htb,hna]
      · by_cases htb : t < b <;> simp [ht,hta,htb,le_of_not_gt hta]
    · have hna : ¬a ≤ t := fun h => ht (ha.trans h)
      simp [ht,hna]
  · simp only [min_eq_right hba, max_eq_left hba, Set.indicator_apply, Set.mem_Ico,
      levelIndicator]
    by_cases ht : 0 ≤ t
    · by_cases htb : t < b
      · have hta : t < a := htb.trans_le hba
        have hnb : ¬b ≤ t := not_le.mpr htb
        simp [ht,hta,htb,hnb]
      · by_cases hta : t < a <;> simp [ht,hta,htb,le_of_not_gt htb]
    · have hnb : ¬b ≤ t := fun h => ht (hb.trans h)
      simp [ht,hnb]

theorem integrable_abs_sub_levelIndicator (a b : ℝ) :
    Integrable (fun t => |levelIndicator a t - levelIndicator b t|) :=
  ((integrable_levelIndicator a).sub (integrable_levelIndicator b)).abs

theorem integral_abs_sub_levelIndicator {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫ t, |levelIndicator a t - levelIndicator b t| = |a-b| := by
  rw [abs_sub_levelIndicator ha hb, integral_indicator measurableSet_Ico]
  simp only [setIntegral_const, smul_eq_mul, mul_one,
    Real.volume_real_Ico_of_le min_le_max]
  exact (max_sub_min_eq_abs a b).trans (abs_sub_comm _ _)

 
theorem finite_coarea_lower_bound {α : Type*} (S : Finset α) (P : Finset (α × α))
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (hout : ∀ x ∉ S, f x = 0) (h : ℝ)
    (hcut : ∀ A : Finset α, A ⊆ S →
      h * A.card ≤ ∑ e ∈ P,
        |(if e.1 ∈ A then (1:ℝ) else 0) - (if e.2 ∈ A then (1:ℝ) else 0)|) :
    h * ∑ x ∈ S, f x ≤ ∑ e ∈ P, |f e.1 - f e.2| := by
  let F : ℝ → ℝ := fun t => h * ∑ x ∈ S, levelIndicator (f x) t
  let J : ℝ → ℝ := fun t => ∑ e ∈ P,
    |levelIndicator (f e.1) t - levelIndicator (f e.2) t|
  have hF : Integrable F :=
    (integrable_finsetSum S (fun x _ => integrable_levelIndicator (f x))).const_mul h
  have hJ : Integrable J :=
    integrable_finsetSum P (fun e _ => integrable_abs_sub_levelIndicator _ _)
  have hle : ∀ t, F t ≤ J t := by
    intro t
    let A := S.filter (fun x => 0 ≤ t ∧ t < f x)
    have hi (x : α) : levelIndicator (f x) t = if x ∈ A then (1:ℝ) else 0 := by
      by_cases hx : x ∈ S
      · simp [A,levelIndicator,hx]
      · rw [hout x hx]
        have hz : ¬(0 ≤ t ∧ t < 0) := fun ht => (not_lt_of_ge ht.1) ht.2
        simp [A,levelIndicator,hx,hz]
    have hc : ∑ x ∈ S, levelIndicator (f x) t = (A.card : ℝ) := by
      simp [levelIndicator,A,Finset.sum_boole]
    dsimp [F,J]
    rw [hc]
    simpa only [hi] using hcut A (Finset.filter_subset _ _)
  have H := integral_mono hF hJ hle
  dsimp [F,J] at H
  rw [integral_const_mul, integral_finsetSum _
    (fun x _ => integrable_levelIndicator (f x)), integral_finsetSum _
    (fun e _ => integrable_abs_sub_levelIndicator _ _)] at H
  simpa only [integral_levelIndicator (hf _),
    integral_abs_sub_levelIndicator (hf _) (hf _)] using H

theorem hV_mul_card_le (G : BondGraph V E) (A : Finset V) :
    hV G * A.card ≤ (vertexBoundary G A).ncard := by
  by_cases hA : A.Nonempty
  · have hb : BddBelow {r : ℝ | ∃ B : Finset V, B.Nonempty ∧
        r = (vertexBoundary G B).ncard / (B.card : ℝ)} := by
      refine ⟨0, ?_⟩
      rintro _ ⟨B,_,rfl⟩
      positivity
    have hh : hV G ≤ (vertexBoundary G A).ncard / (A.card : ℝ) :=
      csInf_le hb ⟨A,hA,rfl⟩
    exact (le_div_iff₀ (by exact_mod_cast hA.card_pos)).mp hh
  · simp [Finset.not_nonempty_iff_eq_empty.mp hA]

theorem finite_vertexBoundary (G : BondGraph V E) (hloc : LocallyFinite G)
    (A : Finset V) : (vertexBoundary G A).Finite := by
  apply (A.finite_toSet.biUnion (fun x _ => finite_neighbors hloc x)).subset
  rintro y ⟨_,x,hx,hxy⟩
  exact Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr ⟨hx,hxy⟩⟩

theorem subset_neighborClosure (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) : S ⊆ neighborClosure G hloc S := Finset.subset_union_left

theorem neighbor_mem_neighborClosure (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) {x y : V} (hx : x ∈ S) (hxy : Adj G x y) :
    y ∈ neighborClosure G hloc S := by
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x,hx,(mem_neighbors ..).mpr hxy⟩)

theorem adj_symm (G : BondGraph V E) {x y : V} (h : Adj G x y) : Adj G y x := by
  obtain ⟨e,he⟩ := h
  exact ⟨e,he.trans (Sym2.eq_swap)⟩

theorem sum_swap_finiteAdjPairs (G : BondGraph V E) (K : Finset V)
    (f : V × V → ℝ) :
    ∑ e ∈ finiteAdjPairs G K, f e.swap = ∑ e ∈ finiteAdjPairs G K, f e := by
  apply Finset.sum_bij (fun e _ => e.swap)
  · intro e he
    rw [mem_finiteAdjPairs] at he ⊢
    exact ⟨he.2.1,he.1,adj_symm G he.2.2⟩
  · intro a _ b _ h
    exact Prod.swap_injective h
  · intro b hb
    refine ⟨b.swap,?_,Prod.swap_swap b⟩
    rw [mem_finiteAdjPairs] at hb ⊢
    exact ⟨hb.2.1,hb.1,adj_symm G hb.2.2⟩
  · intros; rfl

 
theorem finiteAdjPairs_cut_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (S A : Finset V) (hAS : A ⊆ S) :
    (2 * hV G) * A.card ≤ ∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S),
      |(if e.1 ∈ A then (1:ℝ) else 0) - (if e.2 ∈ A then (1:ℝ) else 0)| := by
  let K := neighborClosure G hloc S
  let P := finiteAdjPairs G K
  let R := P.filter (fun e => e.1 ∈ A ∧ e.2 ∉ A)
  have hs : (finite_vertexBoundary G hloc A).toFinset ⊆ R.image Prod.snd := by
    intro y hy
    have hy' : y ∈ vertexBoundary G A := by simpa using hy
    obtain ⟨hyA,x,hx,hxy⟩ := hy'
    apply Finset.mem_image.mpr
    refine ⟨(x,y),Finset.mem_filter.mpr ⟨?_,hx,hyA⟩,rfl⟩
    exact (mem_finiteAdjPairs G K (x,y)).mpr
      ⟨subset_neighborClosure G hloc S (hAS hx),
        neighbor_mem_neighborClosure G hloc S (hAS hx) hxy,hxy⟩
  have hc : (vertexBoundary G A).ncard ≤ R.card := by
    rw [Set.ncard_eq_toFinset_card (vertexBoundary G A) (finite_vertexBoundary G hloc A)]
    exact (Finset.card_le_card hs).trans (Finset.card_image_le)
  have hcross : hV G * A.card ≤ ∑ e ∈ P,
      if e.1 ∈ A ∧ e.2 ∉ A then (1:ℝ) else 0 := by
    rw [Finset.sum_boole]
    exact (hV_mul_card_le G A).trans (by exact_mod_cast hc)
  have hsplit : ∑ e ∈ P,
      |(if e.1 ∈ A then (1:ℝ) else 0) - (if e.2 ∈ A then (1:ℝ) else 0)| =
      2 * ∑ e ∈ P, if e.1 ∈ A ∧ e.2 ∉ A then (1:ℝ) else 0 := by
    have ht (e : V × V) :
        |(if e.1 ∈ A then (1:ℝ) else 0) - (if e.2 ∈ A then (1:ℝ) else 0)| =
        (if e.1 ∈ A ∧ e.2 ∉ A then (1:ℝ) else 0) +
        (if e.2 ∈ A ∧ e.1 ∉ A then (1:ℝ) else 0) := by
      by_cases h₁ : e.1 ∈ A <;> by_cases h₂ : e.2 ∈ A <;> simp [h₁,h₂]
    simp_rw [ht]
    rw [Finset.sum_add_distrib]
    have he := sum_swap_finiteAdjPairs G K
      (fun e => if e.1 ∈ A ∧ e.2 ∉ A then (1:ℝ) else 0)
    change (∑ e ∈ P, if e.2 ∈ A ∧ e.1 ∉ A then (1:ℝ) else 0) = _ at he
    rw [he]
    ring
  change _ ≤ ∑ e ∈ P, _
  rw [hsplit]
  nlinarith

 
theorem bondGraph_coarea (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (f : V → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hout : ∀ x ∉ S, f x = 0) :
    (2 * hV G) * ∑ x ∈ S, f x ≤
      ∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S), |f e.1 - f e.2| :=
  finite_coarea_lower_bound S _ f hf hout _
    (fun A hAS => finiteAdjPairs_cut_bound G hloc S A hAS)

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

theorem finiteAdjPairs_source_sum_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : ℕ) (hD : ∀ x, degree G x ≤ D) (K : Finset V) (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    ∑ e ∈ finiteAdjPairs G K, f e.1 ≤ (D:ℝ) * ∑ x ∈ K, f x := by
  rw [Finset.mul_sum]
  simp only [finiteAdjPairs,Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_le_sum
  intro x _
  have hc : (K.filter (fun y => Adj G x y)).card ≤ D := by
    apply (Finset.card_le_card ?_).trans ((neighbors_card_le_degree G hloc x).trans (hD x))
    intro y hy
    exact (mem_neighbors G hloc x y).mpr (Finset.mem_filter.mp hy).2
  calc
    (∑ y ∈ K, if Adj G x y then f x else 0) =
        ((K.filter (fun y => Adj G x y)).card:ℝ) * f x := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (D:ℝ) * f x := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hf x)

theorem finiteAdjPairs_square_sum_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : ℕ) (hD : ∀ x, degree G x ≤ D) (S : Finset V) (f : V → ℝ)
    (hout : ∀ x ∉ S, f x = 0) :
    ∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S), (f e.1 + f e.2)^2 ≤
      4 * (D:ℝ) * ∑ x ∈ S, (f x)^2 := by
  let K := neighborClosure G hloc S
  let P := finiteAdjPairs G K
  have hs : ∑ x ∈ K, (f x)^2 = ∑ x ∈ S, (f x)^2 := by
    symm
    apply Finset.sum_subset (subset_neighborClosure G hloc S)
    intro x _ hx
    simp [hout x hx]
  have hfirst := finiteAdjPairs_source_sum_le G hloc D hD K (fun x => (f x)^2) (fun _ => sq_nonneg _)
  rw [hs] at hfirst
  have hsecond := sum_swap_finiteAdjPairs G K (fun e => (f e.1)^2)
  change (∑ e ∈ P, (f e.2)^2) = ∑ e ∈ P, (f e.1)^2 at hsecond
  calc
    (∑ e ∈ P, (f e.1 + f e.2)^2) ≤ ∑ e ∈ P, (2*(f e.1)^2+2*(f e.2)^2) := by
      apply Finset.sum_le_sum
      intro e _
      nlinarith [sq_nonneg (f e.1 - f e.2)]
    _ = 4 * ∑ e ∈ P, (f e.1)^2 := by
      rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,hsecond]
      ring
    _ ≤ 4 * (D:ℝ) * ∑ x ∈ S, (f x)^2 := by
      nlinarith

 

theorem bondGraph_cheeger_energy (G : BondGraph V E) (hloc : LocallyFinite G)
    (hh : 0 < hV G) (D : ℕ) (hD : ∀ x, degree G x ≤ D)
    (S : Finset V) (f : V → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hout : ∀ x ∉ S, f x = 0) :
    (hV G)^2 * ∑ x ∈ S, (f x)^2 ≤
      (D:ℝ) * ∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S), (f e.1-f e.2)^2 := by
  let P := finiteAdjPairs G (neighborClosure G hloc S)
  let N := ∑ x ∈ S, (f x)^2
  let E := ∑ e ∈ P, (f e.1-f e.2)^2
  have hN : 0 ≤ N := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc := bondGraph_coarea G hloc S (fun x => (f x)^2)
    (fun _ => sq_nonneg _) (fun x hx => by rw [hout x hx]; norm_num)
  have ht (e : V × V) : |(f e.1)^2-(f e.2)^2| = |f e.1-f e.2| * (f e.1+f e.2) := by
    rw [show (f e.1)^2-(f e.2)^2 = (f e.1-f e.2)*(f e.1+f e.2) by ring,
      abs_mul,abs_of_nonneg (add_nonneg (hf _) (hf _))]
  simp_rw [ht] at hc
  have hc' : ((2*hV G)*N)^2 ≤
      (∑ e ∈ P, |f e.1-f e.2| * (f e.1+f e.2))^2 := by
    exact sq_le_sq₀ (by positivity) (Finset.sum_nonneg (fun e _ => mul_nonneg (abs_nonneg _)
      (add_nonneg (hf _) (hf _)))) |>.mpr hc
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq P
    (fun e => |f e.1-f e.2|) (fun e => f e.1+f e.2)
  simp only [sq_abs] at hcs
  have hbound := finiteAdjPairs_square_sum_le G hloc D hD S f hout
  have hall : ((2*hV G)*N)^2 ≤ E*(4*(D:ℝ)*N) :=
    (hc'.trans hcs).trans (mul_le_mul_of_nonneg_left hbound hE)
  change (hV G)^2*N ≤ (D:ℝ)*E
  rcases hN.eq_or_lt with hzero | hpos
  · rw [←hzero,mul_zero]
    positivity
  · apply (mul_le_mul_iff_left₀ (by positivity : 0 < 4*N)).mp
    nlinarith [hall]

end IsoperimetricEnergy

section FiniteQuadraticForms
attribute [local instance] Classical.propDecidable

 theorem kernel_finiteEmbedding (A : Hilbert V →L[ℂ] Hilbert V)
    (U : V → V → ℝ) (hA : ∀ x y, A (lp.single 2 y (1 : ℂ)) x = (U x y : ℂ))
    (f : V →₀ ℂ) (x : V) :
    A (finiteEmbedding f) x = ∑ y ∈ f.support, f y * (U x y : ℂ) := by
  simp only [finiteEmbedding, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul]
  change (∑ y ∈ f.support, f y • A (lp.single 2 y (1 : ℂ))) x = _
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    hA, smul_eq_mul]

 theorem symmetric_of_symmetric_kernel (A : Hilbert V →L[ℂ] Hilbert V)
    (U : V → V → ℝ) (hA : ∀ x y, A (lp.single 2 y (1 : ℂ)) x = (U x y : ℂ))
    (hU : ∀ x y, U x y = U y x) : A.toLinearMap.IsSymmetric := by
  apply finiteEmbedding_dense.induction_on₂
    (p := fun f g => inner ℂ (A f) g = inner ℂ f (A g))
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro f g
    simp only [finiteEmbedding_inner_left, finiteEmbedding_inner_right,
      kernel_finiteEmbedding A U hA, map_sum, map_mul, RCLike.star_def,
      Complex.conj_ofReal]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hU y x]
    ring

 theorem norm_le_of_finite_quadratic (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : A.toLinearMap.IsSymmetric) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ f : V →₀ ℂ,
      |(inner ℂ (A (finiteEmbedding f)) (finiteEmbedding f)).re| ≤
        C * ‖finiteEmbedding f‖^2) : ‖A‖ ≤ C := by
  have hall (f : Hilbert V) : |(inner ℂ (A f) f).re| ≤ C * ‖f‖^2 := by
    exact finiteEmbedding_dense.induction_on f
      (p := fun g => |(inner ℂ (A g) g).re| ≤ C * ‖g‖^2)
      (isClosed_le (by fun_prop) (by fun_prop)) h
  rw [A.norm_eq_iSup_rayleighQuotient hA]
  apply ciSup_le
  intro f
  by_cases hf : f = 0
  · simp [hf, hC]
  · rw [ContinuousLinearMap.rayleighQuotient, abs_div, abs_sq]
    exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hf))).mpr (hall f)

 theorem abs_inner_kernel_finite_le (A : Hilbert V →L[ℂ] Hilbert V)
    (U : V → V → ℝ) (hA : ∀ x y, A (lp.single 2 y (1 : ℂ)) x = (U x y : ℂ))
    (hU : ∀ x y, 0 ≤ U x y) (f : V →₀ ℂ) :
    |(inner ℂ (A (finiteEmbedding f)) (finiteEmbedding f)).re| ≤
      ∑ x ∈ f.support, ∑ y ∈ f.support, ‖f x‖ * ‖f y‖ * U x y := by
  change |RCLike.re (inner ℂ (A (finiteEmbedding f)) (finiteEmbedding f))| ≤ _
  rw [inner_re_symm]
  apply (Complex.abs_re_le_norm _).trans
  rw [finiteEmbedding_inner_left]
  simp_rw [kernel_finiteEmbedding A U hA, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro y _
  simp [abs_of_nonneg (hU x y), mul_assoc]

end FiniteQuadraticForms

section SymmetricWalk
attribute [local instance] Classical.propDecidable



 theorem walkKernel_symmetric (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (x y : V) : walkKernel G hloc a x y = walkKernel G hloc a y x := by
  have ha : Adj G x y ↔ Adj G y x := ⟨adj_symm G,adj_symm G⟩
  by_cases h : x = y
  · subst y; rfl
  · simp [walkKernel,h,Ne.symm h,ha]

 theorem walkKernel_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : ℕ) (hD : ∀ x, degree G x ≤ D) (a : ℝ) (ha : 0 ≤ a) (haD : a*D ≤ 1)
    (x y : V) : 0 ≤ walkKernel G hloc a x y := by
  have hn : ((neighbors G hloc x).card : ℝ) ≤ D := by
    exact_mod_cast (neighbors_card_le_degree G hloc x).trans (hD x)
  have hh : 0 ≤ 1-a*(neighbors G hloc x).card := by nlinarith
  unfold walkKernel
  split_ifs <;> positivity

 theorem walkKernel_row_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (x : V) :
    ∑ y ∈ insert x (neighbors G hloc x), walkKernel G hloc a x y = 1 := by
  let N := neighbors G hloc x
  have hf : (insert x N).filter (fun y => Adj G x y) = N := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_insert]
    rw [mem_neighbors]
    exact ⟨fun h => h.2, fun h => ⟨Or.inr h,h⟩⟩
  simp only [walkKernel, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_insert_self,ite_true]
  rw [← Finset.sum_filter,hf]
  simp only [Finset.sum_const, nsmul_eq_mul]
  dsimp [N]
  ring

 theorem walkKernel_row_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : ℕ) (hD : ∀ x, degree G x ≤ D) (a : ℝ) (ha : 0 ≤ a) (haD : a*D ≤ 1)
    (x : V) (S : Finset V) : ∑ y ∈ S, walkKernel G hloc a x y ≤ 1 := by
  let N := insert x (neighbors G hloc x)
  calc
    ∑ y ∈ S, walkKernel G hloc a x y ≤ ∑ y ∈ S ∪ N, walkKernel G hloc a x y :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun y _ _ => walkKernel_nonneg G hloc D hD a ha haD x y)
    _ = ∑ y ∈ N, walkKernel G hloc a x y := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro y _ hy
      have hxy : x ≠ y := by intro h; subst y; exact hy (by simp [N])
      have hna : ¬ Adj G x y := by intro h; exact hy (by simp [N,h])
      simp [walkKernel,hxy,hna]
    _ = 1 := walkKernel_row_sum G hloc a x

 theorem exists_walk_operator (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : ℕ) (hD : ∀ x, degree G x ≤ D) (a : ℝ) (ha : 0 ≤ a) (haD : a*D ≤ 1) :
    ∃ P : Hilbert V →L[ℂ] Hilbert V, ‖P‖ ≤ 1 ∧
      P.toLinearMap.IsSymmetric ∧
      ∀ x y, P (lp.single 2 y (1 : ℂ)) x = (walkKernel G hloc a x y : ℂ) := by
  obtain ⟨P,hP,hK⟩ := exists_operator_of_row_column_bound (walkKernel G hloc a) 1
    zero_le_one (walkKernel_nonneg G hloc D hD a ha haD)
    (walkKernel_row_bound G hloc D hD a ha haD) (by
      intro y S
      simp_rw [walkKernel_symmetric G hloc a]
      exact walkKernel_row_bound G hloc D hD a ha haD y S)
  exact ⟨P,hP,symmetric_of_symmetric_kernel P _ hK (walkKernel_symmetric G hloc a),hK⟩

 theorem finiteAdjPairs_sum (G : BondGraph V E) (K : Finset V) (f : V × V → ℝ) :
    (∑ e ∈ finiteAdjPairs G K, f e) =
      ∑ x ∈ K, ∑ y ∈ K, if Adj G x y then f (x,y) else 0 := by
  simp [finiteAdjPairs,Finset.sum_filter,Finset.sum_product]

 theorem finiteAdjPairs_source_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (f : V → ℝ) (hout : ∀ x ∉ S, f x = 0) :
    (∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S), f e.1) =
      ∑ x ∈ S, ((neighbors G hloc x).card : ℝ) * f x := by
  let K := neighborClosure G hloc S
  rw [finiteAdjPairs_sum]
  have he (x : V) (hx : x ∈ S) :
      K.filter (fun y => Adj G x y) = neighbors G hloc x := by
    ext y
    simp only [Finset.mem_filter,mem_neighbors]
    exact ⟨fun h => h.2,fun h => ⟨neighbor_mem_neighborClosure G hloc S hx h,h⟩⟩
  have hout' : ∀ x ∉ S, (∑ y ∈ K, if Adj G x y then f x else 0) = 0 := by
    intro x hx; simp [hout x hx]
  change (∑ x ∈ K, ∑ y ∈ K, if Adj G x y then f x else 0) = _
  rw [← Finset.sum_subset (subset_neighborClosure G hloc S)
    (fun x _ hx => hout' x hx)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_filter,he x hx]
  simp

 theorem finiteAdjPairs_product_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (f : V → ℝ) (hout : ∀ x ∉ S, f x = 0) :
    (∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S), f e.1 * f e.2) =
      ∑ x ∈ S, ∑ y ∈ S, if Adj G x y then f x*f y else 0 := by
  rw [finiteAdjPairs_sum]
  have hs := subset_neighborClosure G hloc S
  calc
    _ = ∑ x ∈ S, ∑ y ∈ neighborClosure G hloc S,
        if Adj G x y then f x*f y else 0 := by
      symm; apply Finset.sum_subset hs
      intro x _ hx; simp [hout x hx]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      symm; apply Finset.sum_subset hs
      intro y _ hy; simp [hout y hy]

 theorem walkKernel_energy (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (S : Finset V) (f : V → ℝ) (hout : ∀ x ∉ S, f x = 0) :
    (∑ x ∈ S, ∑ y ∈ S, f x*f y*walkKernel G hloc a x y) =
      ∑ x ∈ S, (f x)^2 - a/2 *
        ∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S), (f e.1-f e.2)^2 := by
  let P := finiteAdjPairs G (neighborClosure G hloc S)
  have henergy : (∑ e ∈ P, (f e.1-f e.2)^2) =
      2*(∑ x ∈ S, (neighbors G hloc x).card * (f x)^2) -
      2*(∑ x ∈ S, ∑ y ∈ S, if Adj G x y then f x*f y else 0) := by
    have hs := sum_swap_finiteAdjPairs G (neighborClosure G hloc S)
      (fun e => (f e.1)^2)
    change (∑ e ∈ P,(f e.2)^2) = (∑ e ∈ P,(f e.1)^2) at hs
    have hfirst := finiteAdjPairs_source_sum G hloc S (fun x => (f x)^2)
      (fun x hx => by rw [hout x hx]; norm_num)
    calc
      _ = (∑ e ∈ P, (f e.1)^2) + (∑ e ∈ P,(f e.2)^2) -
          2*(∑ e ∈ P,f e.1*f e.2) := by
        simp_rw [sub_sq]
        rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
        simp_rw [mul_assoc,← Finset.mul_sum]
        ring
      _ = _ := by rw [hs,hfirst,finiteAdjPairs_product_sum G hloc S f hout]; ring
  rw [henergy]
  have hpoint (x : V) (hx : x ∈ S) :
      (∑ y ∈ S, f x*f y*walkKernel G hloc a x y) =
        (f x)^2 - a*((neighbors G hloc x).card*(f x)^2) +
         a*(∑ y ∈ S, if Adj G x y then f x*f y else 0) := by
    simp only [walkKernel,mul_add,Finset.sum_add_distrib]
    have hi : (∑ y ∈ S, f x*f y*(if x=y then 1-a*(neighbors G hloc x).card else 0)) =
        (f x)^2*(1-a*(neighbors G hloc x).card) := by
      simp_rw [mul_ite,mul_zero]
      rw [Finset.sum_ite_eq]
      simp only [hx,ite_true]
      ring
    rw [hi,Finset.mul_sum]
    have hj : (∑ y ∈ S, f x*f y*(if Adj G x y then a else 0)) =
        ∑ y ∈ S, a*(if Adj G x y then f x*f y else 0) := by
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> ring
    rw [hj]
    ring
  simp_rw [Finset.sum_congr rfl hpoint,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,←Finset.mul_sum]
  ring

 

theorem walkKernel_quadratic_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (hh : 0 < hV G) (D : ℕ) (hDp : 0 < D) (hD : ∀ x, degree G x ≤ D)
    (a : ℝ) (ha : 0 ≤ a) (S : Finset V) (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hout : ∀ x ∉ S, f x = 0) :
    (∑ x ∈ S, ∑ y ∈ S, f x*f y*walkKernel G hloc a x y) ≤
      (1 - a*(hV G)^2/(2*D)) * ∑ x ∈ S, (f x)^2 := by
  have hDp' : 0 < (D:ℝ) := by exact_mod_cast hDp
  have hc := bondGraph_cheeger_energy G hloc hh D hD S f hf hout
  have he : ((hV G)^2 * ∑ x ∈ S, (f x)^2)/(D:ℝ) ≤
      ∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S), (f e.1-f e.2)^2 :=
    (div_le_iff₀ hDp').mpr (by simpa only [mul_comm] using hc)
  rw [walkKernel_energy G hloc a S f hout]
  calc
    _ ≤ (∑ x ∈ S, (f x)^2) - a/2 *
        (((hV G)^2 * ∑ x ∈ S, (f x)^2)/(D:ℝ)) :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left he (by positivity)) _
    _ = _ := by ring

 

theorem walk_operator_norm_lt_one (G : BondGraph V E) (hloc : LocallyFinite G)
    (hh : 0 < hV G) (D : ℕ) (hDp : 0 < D) (hD : ∀ x, degree G x ≤ D)
    (a : ℝ) (ha : 0 < a) (haD : a*D ≤ 1)
    (P : Hilbert V →L[ℂ] Hilbert V)
    (hP : ∀ x y, P (lp.single 2 y (1:ℂ)) x = (walkKernel G hloc a x y : ℂ)) :
    ‖P‖ < 1 := by
  let C := max 0 (1-a*(hV G)^2/(2*D))
  have hDp' : 0 < (D:ℝ) := by exact_mod_cast hDp
  have hC : 0 ≤ C := le_max_left _ _
  have hC1 : C < 1 := by
    apply max_lt (by norm_num)
    have : 0 < a*(hV G)^2/(2*D) := by positivity
    linarith
  have hn : ‖P‖ ≤ C := by
    apply norm_le_of_finite_quadratic P
      (symmetric_of_symmetric_kernel P _ hP (walkKernel_symmetric G hloc a)) C hC
    intro f
    calc
      _ ≤ ∑ x ∈ f.support, ∑ y ∈ f.support, ‖f x‖*‖f y‖*walkKernel G hloc a x y :=
        abs_inner_kernel_finite_le P _ hP (walkKernel_nonneg G hloc D hD a ha.le haD) f
      _ ≤ (1-a*(hV G)^2/(2*D)) * ∑ x ∈ f.support, ‖f x‖^2 :=
        walkKernel_quadratic_bound G hloc hh D hDp hD a ha.le f.support
          (fun x => ‖f x‖) (fun _ => norm_nonneg _) (by
            intro x hx; simp [Finsupp.notMem_support_iff.mp hx])
      _ ≤ C * ∑ x ∈ f.support, ‖f x‖^2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      _ = C * ‖finiteEmbedding f‖^2 := by rw [finiteEmbedding_norm_sq]
  exact hn.trans_lt hC1

 

theorem exists_strict_walk_operator (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G) :
    ∃ (D : ℕ) (P : Hilbert V →L[ℂ] Hilbert V), 0 < D ∧
      (∀ x, degree G x ≤ D) ∧ ‖P‖ < 1 ∧ P.toLinearMap.IsSymmetric ∧
      ∀ x y, P (lp.single 2 y (1:ℂ)) x =
        (walkKernel G hloc (1/(2*(D:ℝ))) x y : ℂ) := by
  obtain ⟨D,hDp,hD⟩ := exists_degree_bound G hqt
  have hDp' : 0 < (D:ℝ) := by exact_mod_cast hDp
  have ha : 0 < (1:ℝ)/(2*D) := by positivity
  have haD : (1:ℝ)/(2*D)*D ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  obtain ⟨P,_,hPs,hP⟩ := exists_walk_operator G hloc D hD _ ha.le haD
  exact ⟨D,P,hDp,hD,walk_operator_norm_lt_one G hloc hh D hDp hD _ ha haD P hP,hPs,hP⟩

end SymmetricWalk

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

section CriticalParameter
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem twoPoint_adj_lower [Countable E] (G : BondGraph V E) (p : unitInterval)
    (z x y : V) (hxy : Adj G x y) : (p:ℝ)*twoPoint G p z x ≤ twoPoint G p z y := by
  obtain ⟨e,he⟩ := hxy
  have h := association_finiteWitness p {ω : Set E | e ∈ ω} {ω | Conn G ω z x}
    (fun _ _ hω h => hω h) (fun _ _ hω h => conn_mono G hω h)
    (finiteWitness_edge e) (finiteWitness_conn G z x)
  have hp : (law p).real {ω : Set E | e ∈ ω} = (p:ℝ) := by
    simpa using finite_open_probability p {e}
  rw [hp] at h
  exact h.trans (measureReal_mono (fun ω hω =>
    conn_trans G ω hω.2 (Relation.ReflTransGen.single ⟨e,hω.1,he⟩)))

 
theorem walk_operator_apply (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V)
    (hP : ∀ x y, P (lp.single 2 y (1:ℂ)) x = (walkKernel G hloc a x y : ℂ))
    (f : Hilbert V) (x : V) :
    P f x = ∑ y ∈ insert x (neighbors G hloc x), (walkKernel G hloc a x y : ℂ)*f y := by
  have hz (y : V) (hy : y ∉ insert x (neighbors G hloc x)) : matrixCoeff P x y*f y = 0 := by
    have hxy : x ≠ y := by intro h; subst y; exact hy (Finset.mem_insert_self _ _)
    have hAdj : ¬Adj G x y := fun h => hy (Finset.mem_insert_of_mem ((mem_neighbors ..).mpr h))
    simp only [matrixCoeff,hP,walkKernel,ite_eq_right hxy,ite_eq_right hAdj,add_zero,Complex.ofReal_zero,zero_mul]
  have hsum := (operator_kernel_hasSum P f x).unique (hasSum_sum_of_ne_finset_zero hz)
  simpa only [matrixCoeff,hP] using hsum

 

theorem parameter_le_walk_norm [Countable E] [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (D : ℕ) (hD : ∀ x, degree G x ≤ D)
    (a : ℝ) (ha : 0 ≤ a) (haD : a*D ≤ 1)
    (P : Hilbert V →L[ℂ] Hilbert V)
    (hP : ∀ x y, P (lp.single 2 y (1:ℂ)) x = (walkKernel G hloc a x y : ℂ))
    (p : unitInterval) (hp : OperatorBounded G p) : (p:ℝ) ≤ ‖P‖ := by
  obtain ⟨T,hT⟩ := hp
  let z := Classical.arbitrary V
  let f := T (lp.single 2 z (1:ℂ))
  have hf (x : V) : f x = (twoPoint G p x z : ℂ) := hT x z
  have hf0 : 0 < ‖f‖ := by
    apply norm_pos_iff.mpr
    intro h
    have hval := congrArg (fun g : Hilbert V => g z) h
    simp [hf] at hval
  have hrow (x : V) : (p:ℝ)*twoPoint G p x z ≤
      ∑ y ∈ insert x (neighbors G hloc x), walkKernel G hloc a x y*twoPoint G p y z := by
    calc
      _ = ∑ y ∈ insert x (neighbors G hloc x), walkKernel G hloc a x y*((p:ℝ)*twoPoint G p x z) := by
        rw [← Finset.sum_mul,walkKernel_row_sum,one_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro y hy
        apply mul_le_mul_of_nonneg_left _ (walkKernel_nonneg G hloc D hD a ha haD x y)
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact mul_le_of_le_one_left (twoPoint_nonneg G p y z) p.2.2
        · simpa only [twoPoint_symm G p] using twoPoint_adj_lower G p z x y ((mem_neighbors ..).mp hy)
  have hpoint (x : V) : ‖((p:ℂ) • f) x‖ ≤ ‖P f x‖ := by
    rw [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,hf,← Complex.ofReal_mul,
      Complex.norm_of_nonneg (mul_nonneg p.2.1 (twoPoint_nonneg G p x z)),
      walk_operator_apply G hloc a P hP]
    simp only [hf,← Complex.ofReal_mul,← Complex.ofReal_sum]
    rw [Complex.norm_of_nonneg (le_trans (mul_nonneg p.2.1 (twoPoint_nonneg G p x z)) (hrow x))]
    exact hrow x
  have hn := (lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0) hpoint).trans (P.le_opNorm f)
  rw [norm_smul,Complex.norm_of_nonneg p.2.1] at hn
  exact (mul_le_mul_iff_left₀ hf0).mp hn

 
theorem pc_lt_one_of_nonamenable [Nonempty V] (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hh : 0 < hV G) : pc G < 1 := by
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  obtain ⟨D,P,hD0,hD,hPn,_,hP⟩ := exists_strict_walk_operator G hloc hqt hh
  have hDr : 0 < (D:ℝ) := by exact_mod_cast hD0
  let p : unitInterval := ⟨(‖P‖+1)/2,by constructor <;> linarith [norm_nonneg P]⟩
  have hp1 : p < 1 := by change (‖P‖+1)/2 < 1; linarith
  have ha : 0 ≤ (1:ℝ)/(2*D) := by positivity
  have haD : (1:ℝ)/(2*D)*D ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  apply lt_of_le_of_ne (show pc G ≤ 1 from (pc G).2.2)
  intro he
  have hb := operatorBounded_of_lt_pc G hloc hqt p (he ▸ hp1)
  have hle := parameter_le_walk_norm G hloc D hD _ ha haD P hP p hb
  change (‖P‖+1)/2 ≤ ‖P‖ at hle
  linarith

end CriticalParameter

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Clusters_KernelMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section SusceptibilityTypes
attribute [local instance] Classical.propDecidable Classical.decEq

theorem summable_twoPoint_subcritical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) : Summable (twoPoint G p x) := by
  obtain ⟨_,_,hrow⟩ := subcritical_row_bound G hloc hqt p hp
  exact summable_of_sum_le (twoPoint_nonneg G p x) (hrow x)

theorem susceptibility_one_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) : 1 ≤ susceptibility G p x := by
  have hd : twoPoint G p x x = 1 := by
    have he : {ω : Set E | Conn G ω x x} = Set.univ := Set.eq_univ_of_forall (fun _ => conn_refl G _ x)
    simp only [twoPoint,he,measure_univ,ENNReal.toReal_one]
  rw [←hd]
  exact (summable_twoPoint_subcritical G hloc hqt p hp x).le_tsum x (fun _ _ => twoPoint_nonneg G p _ _)

end SusceptibilityTypes
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_RussoRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Russo Rows for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section RussoRows
attribute [local instance] Classical.propDecidable Classical.decEq



theorem summable_kernel_pair (A B : V → V → ℝ)
    (hA : ∀ x y, 0 ≤ A x y) (hB : ∀ x y, 0 ≤ B x y)
    (hsA : ∀ x, Summable (A x)) (hsB : ∀ x, Summable (B x))
    (C : ℝ) (hC : ∀ x, ∑' y, B x y ≤ C) (x : V) :
    Summable (fun ab : V×V => A x ab.1 * B ab.1 ab.2) := by
  apply (summable_prod_of_nonneg (f := fun ab : V×V => A x ab.1 * B ab.1 ab.2)
    (fun ab => mul_nonneg (hA x ab.1) (hB ab.1 ab.2))).mpr
  refine ⟨fun a => (hsB a).mul_left (A x a),?_⟩
  simp only [tsum_mul_left]
  exact Summable.of_nonneg_of_le (fun a => mul_nonneg (hA x a) (tsum_nonneg (hB a)))
    (fun a => mul_le_mul_of_nonneg_left (hC a) (hA x a)) ((hsA x).mul_right C)

theorem summable_twoPoint_pair [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    Summable (fun ab : V×V => twoPoint G p x ab.1 * twoPoint G p ab.1 ab.2) := by
  obtain ⟨C,_,hrow⟩ := subcritical_row_bound G hloc hqt p hp
  have hs := summable_twoPoint_subcritical G hloc hqt p hp
  exact summable_kernel_pair (twoPoint G p) (twoPoint G p) (twoPoint_nonneg G p)
    (twoPoint_nonneg G p) hs hs C (fun x => (hs x).tsum_le_of_sum_le (hrow x)) x

end RussoRows
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section TriangleDerivative
attribute [local instance] Classical.propDecidable Classical.decEq

theorem summable_realTriangleTerm [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    Summable (fun ab => realTriangleTerm G x ab (p:ℝ)) := by
  simp only [realTriangleTerm,realTwoPoint_coe]
  apply (summable_twoPoint_pair G hloc hqt p hp x).of_nonneg_of_le
  · intro ab
    exact mul_nonneg (mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _)) (twoPoint_nonneg G p _ _)
  · intro ab
    exact mul_le_of_le_one_right (mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _)) (twoPoint_le_one G p _ _)

end TriangleDerivative
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_TraceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section RootTriangleRusso
attribute [local instance] Classical.propDecidable Classical.decEq


theorem realTriangle_one_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) : 1 ≤ realTriangle G x (p:ℝ) := by
  have hh := (summable_realTriangleTerm G hloc hqt p hp x).le_tsum (x,x)
    (fun ab _ => by
      simp only [realTriangleTerm,realTwoPoint_coe]
      exact mul_nonneg (mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _)) (twoPoint_nonneg G p _ _))
  simpa only [realTriangleTerm,realTwoPoint_coe,twoPoint_self,mul_one,realTriangle] using hh

theorem rootTriangle_one_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (p : unitInterval) (hp : p < pc G) : 1 ≤ rootTriangle G root weight (p:ℝ) := by
  calc
    1 = ∑ i, weight i * 1 := by simpa using hw1.symm
    _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
      (realTriangle_one_le G hloc hqt p hp (root i)) (hw i))

end RootTriangleRusso
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TraceNumerics
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem HasKernel.norm_le_susceptibility_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (T : Hilbert V →L[ℂ] Hilbert V)
    (hT : HasKernel G p T) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, susceptibility G p x ≤ C) :
    ‖T‖ ≤ C := by
  have hr (x : V) (s : Finset V) : ∑ y ∈ s, twoPoint G p x y ≤ C :=
    ((summable_twoPoint_subcritical G hloc hqt p hp x).sum_le_tsum s
      (fun y _ => twoPoint_nonneg G p x y)).trans (hb x)
  obtain ⟨S,hS,hK⟩ := exists_operator_of_row_column_bound (twoPoint G p) C hC (twoPoint_nonneg G p)
    hr (fun y s => by simpa only [twoPoint_symm G p] using hr y s)
  rwa [hT.unique hK]

end TraceNumerics
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section QuantitativeSprinkling
attribute [local instance] Classical.propDecidable Classical.decEq

lemma riccati_step (a M n x : ℝ) (ha : 0 ≤ a) (hM : 0 ≤ M) (_hn : 0 ≤ n)
    (_hx : 0 ≤ x) (hb : x ≤ M/(1-a*n*M)) (hh : a*(n+1)*M < 1) :
    a*x < 1 ∧ x/(1-a*x) ≤ M/(1-a*(n+1)*M) := by
  have haM : 0 ≤ a*M := mul_nonneg ha hM
  have hp : 0 < 1-a*n*M := by nlinarith
  have hb' := (le_div_iff₀ hp).mp hb
  have hs : a*(M/(1-a*n*M)) < 1 := by
    rw [←mul_div_assoc,div_lt_one hp]
    nlinarith
  have hax : a*x < 1 := (mul_le_mul_of_nonneg_left hb ha).trans_lt hs
  refine ⟨hax,?_⟩
  apply (div_le_div_iff₀ (sub_pos.mpr hax) (sub_pos.mpr hh)).mpr
  nlinarith

 

theorem sprinkling_iterated_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (q : unitInterval) (m D : ℕ)
    (hD : ∀ x, degree G x ≤ D) (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : HasKernel G (orParameter q m) A) (n : ℕ)
    (hn : (q:ℝ)*(2*D)*(n:ℝ)*‖A‖ < 1) :
    ∃ B : Hilbert V →L[ℂ] Hilbert V, HasKernel G (orParameter q (m+n)) B ∧
      ‖B‖ ≤ ‖A‖/(1-(q:ℝ)*(2*D)*(n:ℝ)*‖A‖) := by
  induction n with
  | zero => exact ⟨A,by simpa using hA,by simp⟩
  | succ n ih =>
    have ha : 0 ≤ (q:ℝ)*(2*D) := mul_nonneg q.2.1 (by positivity)
    have hnext : (q:ℝ)*(2*D)*((n:ℝ)+1)*‖A‖ < 1 := by simpa using hn
    have hprev : (q:ℝ)*(2*D)*(n:ℝ)*‖A‖ < 1 := by
      nlinarith [mul_nonneg ha (norm_nonneg A)]
    obtain ⟨B,hB,hBn⟩ := ih hprev
    obtain ⟨hs,hbound⟩ := riccati_step ((q:ℝ)*(2*D)) ‖A‖ n ‖B‖ ha (norm_nonneg _) (Nat.cast_nonneg _) (norm_nonneg _) hBn hnext
    obtain ⟨C,hC,hCn⟩ := sprinkling_bound G hloc q (m+n) D hD B hB hs
    exact ⟨C,by simpa [Nat.add_assoc] using hC,by simpa using hCn.trans hbound⟩

lemma closed_power_bound (q : unitInterval) (n : ℕ) :
    (1-(q:ℝ))^n * (1+(n:ℝ)*(q:ℝ)) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 0 ≤ (1-(q:ℝ))^n := pow_nonneg (sub_nonneg.mpr q.2.2) _
    have hn : 0 ≤ (n:ℝ)*(q:ℝ)^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    rw [pow_succ,Nat.cast_add,Nat.cast_one]
    nlinarith [mul_nonneg hp hn,mul_nonneg hp (sq_nonneg (q:ℝ))]

lemma orParameter_gap_bound (p q : unitInterval) (m n : ℕ) (hm : orParameter q m = p) :
    (1+(n:ℝ)*(q:ℝ))*(1-(orParameter q (m+n):ℝ)) ≤ 1-(p:ℝ) := by
  have hh := mul_le_mul_of_nonneg_left (closed_power_bound q n) (sub_nonneg.mpr p.2.2)
  have he : 1-(p:ℝ) = (1-(q:ℝ))^m := by rw [←hm]; simp [orParameter]
  rw [he] at hh ⊢
  change (1+(n:ℝ)*(q:ℝ))*(1-(1-(1-(q:ℝ))^(m+n))) ≤ _
  rw [sub_sub_cancel,pow_add]
  nlinarith

end QuantitativeSprinkling
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section QuantitativeOpenness
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem operatorBounded_of_quantitative_gap [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (D : ℕ)
    (hD : ∀ x, degree G x ≤ D) (p r : unitInterval)
    (hp : 0 < p) (hpr : p < r) (hr : r < 1)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : HasKernel G p A)
    (hsmall : ((r:ℝ)-(p:ℝ))*(4*D)*‖A‖ < 1-(r:ℝ)) : OperatorBounded G r := by
  let a := ((r:ℝ)-(p:ℝ))/(1-(r:ℝ))
  have hden : 0 < 1-(r:ℝ) := sub_pos.mpr hr
  have ha : 0 < a := div_pos (sub_pos.mpr hpr) hden
  obtain ⟨m,q,hq,hqp⟩ := exists_orParameter_small p (hpr.trans hr) (min a 1)
    (lt_min ha zero_lt_one) (min_le_right _ _)
  have hq0 : (0:ℝ) < q := by
    by_contra hn
    have hqe : q = 0 := Subtype.ext ((le_of_not_gt hn).antisymm q.2.1)
    have hpe : p = 0 := by rw [←hqp,hqe]; apply Subtype.ext; simp [orParameter]
    exact (ne_of_gt hp) hpe
  let n := ⌈a/(q:ℝ)⌉₊
  have hna : a ≤ (n:ℝ)*(q:ℝ) := (div_le_iff₀ hq0).mp (Nat.le_ceil _)
  have han : (n:ℝ)*(q:ℝ) < a+(q:ℝ) := by
    have hn := Nat.ceil_lt_add_one (div_nonneg ha.le hq0.le)
    have hh := mul_lt_mul_of_pos_right hn hq0
    dsimp only [n] at *
    field_simp at hh
    nlinarith
  have hn2 : (n:ℝ)*(q:ℝ) < 2*a := by linarith [hq.trans (min_le_left _ _)]
  have hbase : (2*a)*(2*D)*‖A‖ < 1 := by
    rw [show (2*a)*(2*D)*‖A‖ = (((r:ℝ)-(p:ℝ))*(4*D)*‖A‖)/(1-(r:ℝ)) by dsimp [a]; ring]
    exact (div_lt_one hden).mpr hsmall
  have hnsmall : (q:ℝ)*(2*D)*(n:ℝ)*‖A‖ < 1 := by
    have hs := mul_le_mul_of_nonneg_right hn2.le (show 0 ≤ (2*(D:ℝ))*‖A‖ by positivity)
    nlinarith
  obtain ⟨B,hB,_⟩ := sprinkling_iterated_bound G hloc q m D hD A (hqp ▸ hA) n hnsmall
  apply operatorBounded_of_le G (q := orParameter q (m+n)) ?_ ⟨B,hB⟩
  have hgap := orParameter_gap_bound p q m n hqp
  have hae : a*(1-(r:ℝ)) = (r:ℝ)-(p:ℝ) := div_mul_cancel₀ _ (ne_of_gt hden)
  have hs := mul_le_mul_of_nonneg_right hna hden.le
  change (r:ℝ) ≤ (orParameter q (m+n):ℝ)
  nlinarith [mul_nonneg (Nat.cast_nonneg n) q.2.1]

 

theorem norm_gap_lower_of_endpoint_unbounded [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (D : ℕ)
    (hD : ∀ x, degree G x ≤ D) (p r : unitInterval)
    (hp : 0 < p) (hpr : p < r) (hr : r < 1)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : HasKernel G p A)
    (hu : ¬OperatorBounded G r) :
    1-(r:ℝ) ≤ ((r:ℝ)-(p:ℝ))*(4*D)*‖A‖ := by
  by_contra h
  exact hu (operatorBounded_of_quantitative_gap G hloc D hD p r hp hpr hr A hA (lt_of_not_ge h))

end QuantitativeOpenness
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NormRatio
attribute [local instance] Classical.propDecidable Classical.decEq



theorem susceptibility_bddAbove [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) : BddAbove (Set.range (susceptibility G p)) := by
  obtain ⟨C,_,hC⟩ := subcritical_row_bound G hloc hqt p hp
  refine ⟨C,?_⟩
  rintro _ ⟨x,rfl⟩
  exact (summable_twoPoint_subcritical G hloc hqt p hp x).tsum_le_of_sum_le (hC x)

theorem susceptibility_le_max [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    susceptibility G p x ≤ maxSusceptibility G p :=
  le_csSup (susceptibility_bddAbove G hloc hqt p hp) (Set.mem_range_self x)

theorem maxSusceptibility_le [Nonempty V] (G : BondGraph V E) (p : unitInterval)
    (C : ℝ) (hC : ∀ x, susceptibility G p x ≤ C) : maxSusceptibility G p ≤ C := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x,rfl⟩
  exact hC x

theorem maxSusceptibility_one_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) : 1 ≤ maxSusceptibility G p := by
  let x : V := Classical.choice inferInstance
  exact (susceptibility_one_le G hloc hqt p hp x).trans (susceptibility_le_max G hloc hqt p hp x)

theorem HasKernel.norm_le_maxSusceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (T : Hilbert V →L[ℂ] Hilbert V)
    (hT : HasKernel G p T) : ‖T‖ ≤ maxSusceptibility G p :=
  hT.norm_le_susceptibility_bound G hloc hqt p hp T _
    (le_trans zero_le_one (maxSusceptibility_one_le G hloc hqt p hp))
    (susceptibility_le_max G hloc hqt p hp)

theorem HasKernel.norm_one_le [Countable E] [Nonempty V]
    (G : BondGraph V E) (p : unitInterval) (T : Hilbert V →L[ℂ] Hilbert V)
    (hT : HasKernel G p T) : 1 ≤ ‖T‖ := by
  let x : V := Classical.choice inferInstance
  have hd : twoPoint G p x x = 1 := twoPoint_self G p x
  have hh := (lp.norm_apply_le_norm (by norm_num : (2:ENNReal) ≠ 0) (T (lp.single 2 x (1:ℂ))) x).trans (T.le_opNorm (lp.single 2 x (1:ℂ)))
  simpa [hT x x,hd,lp.norm_single] using hh

end NormRatio
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SourceNormRatio
attribute [local instance] Classical.propDecidable Classical.decEq

theorem critical_norm_inverse_lower [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hp₁ : (pc G:ℝ) < 1) (hu : ¬OperatorBounded G (pc G)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : unitInterval), 0 < p → p < pc G →
      ∀ T : Hilbert V →L[ℂ] Hilbert V, HasKernel G p T →
        c/((pc G:ℝ)-(p:ℝ)) ≤ ‖T‖ := by
  obtain ⟨D,hDp,hD⟩ := exists_degree_bound G hqt
  have hDpos : 0 < (4*(D:ℝ)) := by positivity
  refine ⟨(1-(pc G:ℝ))/(4*D),div_pos (sub_pos.mpr hp₁) hDpos,?_⟩
  intro p hp hpq T hT
  have hh := norm_gap_lower_of_endpoint_unbounded G hloc D hD p (pc G) hp hpq hp₁ T hT hu
  apply (div_le_iff₀ (sub_pos.mpr (show (p:ℝ)<(pc G:ℝ) from hpq))).mpr
  apply (div_le_iff₀ hDpos).mpr
  nlinarith

 

theorem critical_normRatio_subpower
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (hu : ¬OperatorBounded G (pc G)) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ T : Hilbert V →L[ℂ] Hilbert V, HasKernel G p T →
      1 ≤ maxSusceptibility G p/‖T‖ ∧
      maxSusceptibility G p/‖T‖ ≤ K*((pc G:ℝ)-(p:ℝ))^(-η) := by
  obtain ⟨c,hc,hm⟩ := critical_norm_inverse_lower G hloc hqt hp₁ hu
  obtain ⟨D,hD,hχ⟩ := almost_linear_susceptibility G hloc hconn hqt hh root weight Γ hΓ htr hcov hw hw1 hp₀ hp₁ hfin η hη
  refine ⟨D/c,div_pos hD hc,?_⟩
  intro p hp hpq T hT
  have hδ : 0 < (pc G:ℝ)-(p:ℝ) := sub_pos.mpr hpq
  have hnorm : 0 < ‖T‖ := zero_lt_one.trans_le (hT.norm_one_le G p T)
  have hM := hm p ((half_pos hp₀).trans_le hp) hpq T hT
  have hχb := maxSusceptibility_le G p _ (hχ p hpq)
  have he : ((pc G:ℝ)-(p:ℝ))^(-1-η)*((pc G:ℝ)-(p:ℝ)) = ((pc G:ℝ)-(p:ℝ))^(-η) := by
    calc
      _ = ((pc G:ℝ)-(p:ℝ))^(-1-η)*((pc G:ℝ)-(p:ℝ))^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hδ]; congr 1; ring
  refine ⟨(one_le_div hnorm).mpr (hT.norm_le_maxSusceptibility G hloc hqt p hpq T),?_⟩
  calc
    maxSusceptibility G p/‖T‖ ≤ (D*((pc G:ℝ)-(p:ℝ))^(-1-η))/(c/((pc G:ℝ)-(p:ℝ))) :=
      div_le_div₀ (mul_nonneg hD.le (Real.rpow_nonneg hδ.le _)) hχb (div_pos hc hδ) hM
    _ = (D/c)*((pc G:ℝ)-(p:ℝ))^(-η) := by rw [←he]; field_simp

end SourceNormRatio
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Criticality_ScaleLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic scale limits and quantitative parameter estimates. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open Filter
open scoped Topology

 

theorem log_sublinear_of_subexp (f : ℕ → ℝ) (hf : ∀ n, 1 ≤ f n)
    (hb : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 < K ∧ ∀ n, f n ≤ K*Real.exp (η*(n:ℝ))) :
    Tendsto (fun n => Real.log (f n)/(n:ℝ)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K,hK,hbK⟩ := hb (ε/2) (half_pos hε)
  have hlim := tendsto_const_div_atTop_nhds_zero_nat (Real.log K)
  filter_upwards [hlim.eventually (gt_mem_nhds (half_pos hε)), eventually_ge_atTop (1:ℕ)] with n hn hn1
  have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hlog := Real.log_le_log (zero_lt_one.trans_le (hf n)) (hbK n)
  rw [Real.log_mul hK.ne' (Real.exp_pos _).ne',Real.log_exp] at hlog
  have hdiv := (div_le_div_of_nonneg_right hlog hnpos.le)
  rw [add_div,mul_div_cancel_right₀ _ hnpos.ne'] at hdiv
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (Real.log_nonneg (hf n)) hnpos.le)]
  linarith only [hdiv,hn]

 
theorem tendsto_atTop_of_div_nat_pos (f : ℕ → ℝ) (L : ℝ) (hL : 0 < L)
    (hf : Tendsto (fun n => f n/(n:ℝ)) atTop (𝓝 L)) : Tendsto f atTop atTop := by
  have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_pos hL hf
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  exact mul_div_cancel₀ (f n) (by exact_mod_cast (show n ≠ 0 by omega))

 
theorem tendsto_exp_of_div_nat_neg (f : ℕ → ℝ) (L : ℝ) (hL : L < 0)
    (hf : Tendsto (fun n => f n/(n:ℝ)) atTop (𝓝 L)) :
    Tendsto (fun n => Real.exp (f n)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n => -f n/(n:ℝ)) atTop (𝓝 (-L)) := by
    simpa only [neg_div] using hf.neg
  have ht := tendsto_atTop_of_div_nat_pos (fun n => -f n) (-L) (neg_pos.mpr hL) hn
  simpa only [Function.comp_def,neg_neg] using Real.tendsto_exp_neg_atTop_nhds_zero.comp ht

 

theorem corridor_scale_limits (r C₁ : ℝ) (J : ℕ) (hr : 0 < r) (hC₁ : 0 < C₁) (hJ : 0 < J)
    (R : ℕ → ℝ) (hR : ∀ n, 1 ≤ R n)
    (hlogR : Tendsto (fun n => Real.log (R n)/(n:ℝ)) atTop (𝓝 0)) :
    let k := fun n : ℕ => ⌈r*(n:ℝ)⌉₊
    let j := fun n : ℕ => J+⌈C₁*Real.log (((k n:ℝ)+1)*R n)⌉₊
    Tendsto k atTop atTop ∧
    Tendsto (fun n => (k n:ℝ)/(n:ℝ)) atTop (𝓝 r) ∧
    Tendsto (fun n => (j n:ℝ)/(n:ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun n => Real.log (j n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
  dsimp only
  let k := fun n : ℕ => ⌈r*(n:ℝ)⌉₊
  let j := fun n : ℕ => J+⌈C₁*Real.log (((k n:ℝ)+1)*R n)⌉₊
  have hkt : Tendsto k atTop atTop :=
    tendsto_nat_ceil_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hr)
  have hk : Tendsto (fun n => (k n:ℝ)/(n:ℝ)) atTop (𝓝 r) :=
    (tendsto_nat_ceil_mul_div_atTop hr.le).comp tendsto_natCast_atTop_atTop
  have hkplus : Tendsto (fun n => ((k n:ℝ)+1)/(n:ℝ)) atTop (𝓝 r) := by
    simpa only [add_div,add_zero] using hk.add (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))
  have hkTop : Tendsto (fun n => (k n:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => le_add_of_nonneg_right (show (0:ℝ) ≤ 1 by norm_num))
      (tendsto_natCast_atTop_atTop.comp hkt)
  have hlogk : Tendsto (fun n => Real.log ((k n:ℝ)+1)/(n:ℝ)) atTop (𝓝 0) := by
    have hl : Tendsto (fun n => Real.log ((k n:ℝ)+1)/((k n:ℝ)+1)) atTop (𝓝 0) := by
      simpa only [Function.comp_def,pow_one,one_mul,add_zero] using
        (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp hkTop
    have hh := hl.mul hkplus
    rw [zero_mul] at hh
    apply hh.congr
    intro n
    have hn : (k n:ℝ)+1 ≠ 0 := by positivity
    field_simp
  have hupper : Tendsto (fun n : ℕ => ((J:ℝ)+1)/(n:ℝ) + C₁*(Real.log ((k n:ℝ)+1)/(n:ℝ) + Real.log (R n)/(n:ℝ))) atTop (𝓝 0) := by
    simpa only [add_zero,mul_zero] using
      (tendsto_const_div_atTop_nhds_zero_nat ((J:ℝ)+1)).add ((hlogk.add hlogR).const_mul C₁)
  have hjlim : Tendsto (fun n => (j n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · exact Eventually.of_forall (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hprod : 1 ≤ ((k n:ℝ)+1)*R n := by nlinarith only [hR n,(Nat.cast_nonneg (k n) : (0:ℝ) ≤ _)]
    have harg : 0 ≤ C₁*Real.log (((k n:ℝ)+1)*R n) := mul_nonneg hC₁.le (Real.log_nonneg hprod)
    have hceil := (Nat.ceil_lt_add_one harg).le
    have he : Real.log (((k n:ℝ)+1)*R n) = Real.log ((k n:ℝ)+1)+Real.log (R n) :=
      Real.log_mul (by positivity) (zero_lt_one.trans_le (hR n)).ne'
    dsimp only [j]
    push_cast
    rw [←add_div,←mul_div_assoc,←add_div,←he]
    exact (div_le_div_of_nonneg_right (by linarith only [hceil]) hnpos.le)
  refine ⟨hkt,hk,hjlim,?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hjlim
  · exact Eventually.of_forall (fun n => div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr (show 1 ≤ j n by dsimp [j]; omega))) (Nat.cast_nonneg n))
  · exact Eventually.of_forall (fun n => div_le_div_of_nonneg_right (Real.log_le_self (Nat.cast_nonneg (j n))) (Nat.cast_nonneg n))

 

theorem exists_corridor_scales_of_slopes
    (ρ p₀ C C₁ ε M cm r z : ℝ) (J k₀ : ℕ)
    (hρ : 0 < ρ) (hp₀ : 0 < p₀) (hC₁ : 0 < C₁) (hε : 0 < ε) (hcm : 0 < cm)
    (hJ : 0 < J) (hr : 0 < r) (hz : 0 < z)
    (hzρ : z+r*Real.log ρ < 0) (hzC : z+C*r < 1)
    (m R Q : ℕ → ℝ) (hR : ∀ n, 1 ≤ R n) (hQ : ∀ n, 1 ≤ Q n)
    (hm : ∀ n : ℕ, cm*Real.exp (n:ℝ) ≤ m n)
    (hlogR : Tendsto (fun n => Real.log (R n)/(n:ℝ)) atTop (𝓝 0))
    (hlogQ : Tendsto (fun n => Real.log (Q n)/(n:ℝ)) atTop (𝓝 0)) :
    ∃ (n k : ℕ) (B : ℝ), k₀ ≤ k ∧ 0 < B ∧
      let j := J+⌈C₁*Real.log (((k:ℝ)+1)*R n)⌉₊
      B*ρ^k ≤ 1/4 ∧ B*(j:ℝ)*Real.exp (C*(k:ℝ)) ≤ m n ∧
      (R n)^2*Q n*ρ^k ≤ ε*p₀^(2*j) ∧ M < B*p₀^(2*j) := by
  let k := fun n : ℕ => ⌈r*(n:ℝ)⌉₊
  let j := fun n : ℕ => J+⌈C₁*Real.log (((k n:ℝ)+1)*R n)⌉₊
  let B := fun n : ℕ => Real.exp (z*(n:ℝ))
  obtain ⟨hkt,hk,hj,hlogj⟩ := corridor_scale_limits r C₁ J hr hC₁ hJ R hR hlogR
  change Tendsto k atTop atTop at hkt
  change Tendsto (fun n => (k n:ℝ)/(n:ℝ)) atTop (𝓝 r) at hk
  change Tendsto (fun n => (j n:ℝ)/(n:ℝ)) atTop (𝓝 0) at hj
  change Tendsto (fun n => Real.log (j n:ℝ)/(n:ℝ)) atTop (𝓝 0) at hlogj
  have hn : Tendsto (fun n : ℕ => (n:ℝ)/(n:ℝ)) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_natCast_div_add_atTop (0:ℝ)
  have hβ (n) : Real.exp ((j n:ℝ)*(2*Real.log p₀)) = p₀^(2*j n) := by
    rw [show (j n:ℝ)*(2*Real.log p₀) = ((2*j n:ℕ):ℝ)*Real.log p₀ by push_cast; ring,
      Real.exp_nat_mul,Real.exp_log hp₀]
  have hjpos (n) : (0:ℝ) < j n := Nat.cast_pos.mpr (by dsimp [j]; omega)
  have hlim₁ : Tendsto (fun n : ℕ => (z*(n:ℝ)+(k n:ℝ)*Real.log ρ)/(n:ℝ)) atTop (𝓝 (z+r*Real.log ρ)) := by
    simpa only [mul_one,div_mul_eq_mul_div,←mul_div_assoc,←add_div] using
      (hn.const_mul z).add (hk.mul_const (Real.log ρ))
  have hdec₁ := tendsto_exp_of_div_nat_neg _ _ hzρ hlim₁
  have hlim₂ : Tendsto (fun n : ℕ =>
      (2*Real.log (R n)+Real.log (Q n)+(k n:ℝ)*Real.log ρ-(j n:ℝ)*(2*Real.log p₀))/(n:ℝ))
      atTop (𝓝 (r*Real.log ρ)) := by
    simpa only [mul_zero,zero_add,zero_mul,sub_zero,div_mul_eq_mul_div,←mul_div_assoc,←add_div,←sub_div] using
      (((hlogR.const_mul 2).add hlogQ).add (hk.mul_const (Real.log ρ))).sub (hj.mul_const (2*Real.log p₀))
  have hsl₂ : r*Real.log ρ < 0 := by linarith only [hz,hzρ]
  have hdec₂ := tendsto_exp_of_div_nat_neg _ _ hsl₂ hlim₂
  have hlim₃ : Tendsto (fun n : ℕ =>
      (z*(n:ℝ)+Real.log (j n:ℝ)+C*(k n:ℝ)-(n:ℝ))/(n:ℝ)) atTop (𝓝 (z+C*r-1)) := by
    simpa only [mul_one,add_zero,←mul_div_assoc,←add_div,←sub_div] using
      (((hn.const_mul z).add hlogj).add (hk.const_mul C)).sub hn
  have hdec₃ := tendsto_exp_of_div_nat_neg _ _ (sub_neg.mpr hzC) hlim₃
  have hlim₄ : Tendsto (fun n : ℕ =>
      (z*(n:ℝ)+(j n:ℝ)*(2*Real.log p₀))/(n:ℝ)) atTop (𝓝 z) := by
    simpa only [mul_one,zero_mul,add_zero,div_mul_eq_mul_div,←mul_div_assoc,←add_div] using
      (hn.const_mul z).add (hj.mul_const (2*Real.log p₀))
  have hgrow := Real.tendsto_exp_atTop.comp (tendsto_atTop_of_div_nat_pos _ _ hz hlim₄)
  have hfinal : ∀ᶠ n : ℕ in atTop,
      k₀ ≤ k n ∧ B n*ρ^(k n) ≤ 1/4 ∧
      B n*(j n:ℝ)*Real.exp (C*(k n:ℝ)) ≤ m n ∧
      (R n)^2*Q n*ρ^(k n) ≤ ε*p₀^(2*j n) ∧ M < B n*p₀^(2*j n) := by
    filter_upwards [hkt.eventually_ge_atTop k₀,
      hdec₁.eventually_lt_const (show (0:ℝ) < 1/4 by norm_num),
      hdec₂.eventually_lt_const hε,hdec₃.eventually_lt_const hcm,
      hgrow.eventually_gt_atTop M] with n hk₀ h₁ h₂ h₃ h₄
    have heρ : Real.exp ((k n:ℝ)*Real.log ρ) = ρ^(k n) := by rw [Real.exp_nat_mul,Real.exp_log hρ]
    have heR : Real.exp (2*Real.log (R n)) = (R n)^2 := by
      simpa only [Nat.cast_ofNat,Real.exp_log (zero_lt_one.trans_le (hR n))] using Real.exp_nat_mul (Real.log (R n)) 2
    simp only [Real.exp_add,heρ] at h₁
    simp only [Real.exp_sub,Real.exp_add,heR,Real.exp_log (zero_lt_one.trans_le (hQ n)),heρ,hβ n] at h₂
    simp only [Real.exp_sub,Real.exp_add,Real.exp_log (hjpos n)] at h₃
    change M < Real.exp (z*(n:ℝ)+(j n:ℝ)*(2*Real.log p₀)) at h₄
    rw [Real.exp_add,hβ n] at h₄
    refine ⟨hk₀,h₁.le,?_,(div_le_iff₀ (pow_pos hp₀ _)).mp h₂.le,h₄⟩
    exact ((div_le_iff₀ (Real.exp_pos _)).mp h₃.le).trans (hm n)
  obtain ⟨n,hn⟩ := hfinal.exists
  exact ⟨n,k n,B n,hn.1,Real.exp_pos _,hn.2⟩

 

theorem exists_corridor_scales
    (ρ p₀ C C₁ ε M cm : ℝ) (J k₀ : ℕ)
    (hρ : 0 < ρ) (hρ₁ : ρ < 1) (hp₀ : 0 < p₀) (hC : 0 < C)
    (hC₁ : 0 < C₁) (hε : 0 < ε) (hcm : 0 < cm) (hJ : 0 < J)
    (m R Q : ℕ → ℝ) (hR : ∀ n, 1 ≤ R n) (hQ : ∀ n, 1 ≤ Q n)
    (hm : ∀ n : ℕ, cm*Real.exp (n:ℝ) ≤ m n)
    (hlogR : Tendsto (fun n => Real.log (R n)/(n:ℝ)) atTop (𝓝 0))
    (hlogQ : Tendsto (fun n => Real.log (Q n)/(n:ℝ)) atTop (𝓝 0)) :
    ∃ (n k : ℕ) (B : ℝ), k₀ ≤ k ∧ 0 < B ∧
      let j := J+⌈C₁*Real.log (((k:ℝ)+1)*R n)⌉₊
      B*ρ^k ≤ 1/4 ∧ B*(j:ℝ)*Real.exp (C*(k:ℝ)) ≤ m n ∧
      (R n)^2*Q n*ρ^k ≤ ε*p₀^(2*j) ∧ M < B*p₀^(2*j) := by
  let r := 1/(4*(C+1))
  let z := min (1/4) (-(r*Real.log ρ)/2)
  have hr : 0 < r := by dsimp [r]; positivity
  have hlog : Real.log ρ < 0 := by simpa only [Real.log_one] using Real.log_lt_log hρ hρ₁
  have hz : 0 < z := lt_min (by norm_num) (half_pos (neg_pos.mpr (mul_neg_of_pos_of_neg hr hlog)))
  have hzr : z+r*Real.log ρ < 0 := by
    have hh : z ≤ -(r*Real.log ρ)/2 := min_le_right _ _
    linarith only [hh,mul_neg_of_pos_of_neg hr hlog]
  have hzc : z+C*r < 1 := by
    have hz' : z ≤ 1/4 := min_le_left _ _
    have hr' : r*(4*(C+1)) = 1 := div_mul_cancel₀ 1 (by positivity)
    nlinarith only [hz',hr',hr]
  exact exists_corridor_scales_of_slopes ρ p₀ C C₁ ε M cm r z J k₀
    hρ hp₀ hC₁ hε hcm hJ hr hz hzr hzc m R Q hR hQ hm hlogR hlogQ

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_Labels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Labels for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LazyOrbitReturn
attribute [local instance] Classical.propDecidable Classical.decEq

theorem walkKernel_lazy (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : ℕ) (hD : ∀ x, degree G x ≤ D) (a : ℝ) (ha : 0 ≤ a) (haD : a*D ≤ 1/2)
    (x : V) : 1/2 ≤ walkKernel G hloc a x x := by
  have hn : ((neighbors G hloc x).card : ℝ) ≤ D := by
    exact_mod_cast (neighbors_card_le_degree G hloc x).trans (hD x)
  have hh := mul_le_mul_of_nonneg_left hn ha
  simp only [walkKernel,ite_true]
  split_ifs <;> linarith

end LazyOrbitReturn
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_CollisionTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Collision Tails for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IndependentRawCollisions
attribute [local instance] Classical.propDecidable Classical.decEq



theorem matrixCoeff_norm_le (A : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    ‖matrixCoeff A x y‖ ≤ ‖A‖ := by
  apply (lp.norm_apply_le_norm (by norm_num : (2:ENNReal) ≠ 0) (A (lp.single 2 y (1:ℂ))) x).trans
  simpa using A.le_opNorm (lp.single 2 y (1:ℂ))

end IndependentRawCollisions
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Criticality_Operator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical boundedness of the percolation operator under unimodularity and simple edge indexing. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory Filter
open scoped Topology


theorem criticalApproach_half (q : unitInterval) (n : ℕ) :
    (q:ℝ)/2 ≤ (criticalApproach q n : ℝ) := by
  have he : Real.exp (-(n:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))
  change _ ≤ (q:ℝ)-(q:ℝ)/2*Real.exp (-(n:ℝ))
  nlinarith only [he,q.2.1]

theorem criticalApproach_lt (q : unitInterval) (hq : 0 < (q:ℝ)) (n : ℕ) :
    criticalApproach q n < q := by
  change (q:ℝ)-(q:ℝ)/2*Real.exp (-(n:ℝ)) < q
  exact sub_lt_self _ (mul_pos (half_pos hq) (Real.exp_pos _))

theorem criticalApproach_gap (q : unitInterval) (n : ℕ) :
    (q:ℝ)-(criticalApproach q n:ℝ) = (q:ℝ)/2*Real.exp (-(n:ℝ)) := by
  change (q:ℝ)-((q:ℝ)-(q:ℝ)/2*Real.exp (-(n:ℝ))) = _
  ring

 

theorem log_sublinear_of_geometric_gap (f : ℕ → ℝ) (p₀ : ℝ) (hp₀ : 0 < p₀)
    (hf : ∀ n, 1 ≤ f n)
    (hb : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ, f n ≤ K*(p₀*Real.exp (-(n:ℝ)))^(-η)) :
    Tendsto (fun n => Real.log (f n)/(n:ℝ)) atTop (𝓝 0) := by
  apply log_sublinear_of_subexp f hf
  intro η hη
  obtain ⟨K,hK,hbK⟩ := hb η hη
  refine ⟨K*p₀^(-η),mul_pos hK (Real.rpow_pos_of_pos hp₀ _),fun n => ?_⟩
  have he : (p₀*Real.exp (-(n:ℝ)))^(-η) = p₀^(-η)*Real.exp (η*(n:ℝ)) := by
    rw [Real.mul_rpow hp₀.le (Real.exp_pos _).le,←Real.exp_mul]
    congr 2
    ring
  simpa only [he,mul_assoc] using hbK n

universe u v
variable {V : Type u} {E : Type v}
section AnalyticCritical
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Infinite V] [Nonempty E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

 

theorem critical_bounded_of_fixed_data
    (G : BondGraph V E) (hG : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (a : ℝ) (ha : 0 < a) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d)
    (hpcrit : 0 < (pc G:ℝ)) (hpcrit₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite) :
    OperatorBounded G (pc G) := by
  by_contra hu
  obtain ⟨C,hC,J,hJ,C₁,hC₁,k₀,hk₀,ε,M,hε,_,hbad⟩ :=
    exists_finite_scale_obstruction G hG hconn hloc hqt a ha root weight htr hcov hw hw1 c hc hmin
      P hpos hsym hP hdiag hρ d hd hpcrit hpcrit₁
  let p := criticalApproach (pc G)
  have hpnear (n) : (pc G:ℝ)/2 ≤ (p n:ℝ) := criticalApproach_half (pc G) n
  have hp (n) : p n < pc G := criticalApproach_lt (pc G) hpcrit n
  have hpzero (n) : 0 < (p n:ℝ) := (half_pos hpcrit).trans_le (hpnear n)
  let A := fun n => Classical.choose (operatorBounded_of_lt_pc G hloc hqt (p n) (hp n))
  have hA (n) : HasKernel G (p n) (A n) := Classical.choose_spec (operatorBounded_of_lt_pc G hloc hqt (p n) (hp n))
  let m := fun n => ‖A n‖
  let R := fun n => maxSusceptibility G (p n)/m n
  let Q := fun n => rootTriangle G root weight (p n:ℝ)
  have hR (n) : 1 ≤ R n := (one_le_div (zero_lt_one.trans_le ((hA n).norm_one_le G (p n) (A n)))).mpr
    ((hA n).norm_le_maxSusceptibility G hloc hqt (p n) (hp n) (A n))
  have hQ (n) : 1 ≤ Q n := rootTriangle_one_le G hloc hqt root weight (fun i => (hw i).le) hw1 (p n) (hp n)
  have hlogR : Tendsto (fun n => Real.log (R n)/(n:ℝ)) atTop (𝓝 0) := by
    apply log_sublinear_of_geometric_gap R ((pc G:ℝ)/2) (half_pos hpcrit) hR
    intro η hη
    obtain ⟨K,hK,hRK⟩ := critical_normRatio_subpower G hloc hconn hqt hh root weight (vertexAut G)
      (Set.Subset.refl _) htr hcov hw hw1 hpcrit hpcrit₁ hfin hu η hη
    refine ⟨K,hK,fun n => ?_⟩
    simpa only [p,criticalApproach_gap] using (hRK (p n) (hpnear n) (hp n) (A n) (hA n)).2
  have hlogQ : Tendsto (fun n => Real.log (Q n)/(n:ℝ)) atTop (𝓝 0) := by
    apply log_sublinear_of_geometric_gap Q ((pc G:ℝ)/2) (half_pos hpcrit) hQ
    intro η hη
    obtain ⟨K,hK,hQK⟩ := critical_rootTriangle_subpower G hloc hconn hqt hh root weight (vertexAut G)
      (Set.Subset.refl _) htr hcov hw hw1 hpcrit hpcrit₁ hfin η hη
    refine ⟨K,hK,fun n => ?_⟩
    simpa only [p,criticalApproach_gap] using hQK (p n) (hpnear n) (hp n)
  obtain ⟨cm,hcm,hm⟩ := critical_norm_inverse_lower G hloc hqt hpcrit₁ hu
  have hmlower (n : ℕ) : (cm/((pc G:ℝ)/2))*Real.exp (n:ℝ) ≤ m n := by
    have hh := hm (p n) (hpzero n) (hp n) (A n) (hA n)
    rw [show (pc G:ℝ)-(p n:ℝ) = (pc G:ℝ)/2*Real.exp (-(n:ℝ)) from criticalApproach_gap (pc G) n,
      Real.exp_neg,div_mul_eq_div_div,div_inv_eq_mul] at hh
    exact hh
  have hρpos : 0 < ‖P‖ := by
    let x : V := Classical.arbitrary V
    have hh := (hdiag x).trans ((Complex.re_le_norm _).trans (matrixCoeff_norm_le P x x))
    linarith only [hh]
  obtain ⟨n,k,B,hk,hB,hsmall,htime,herror,hlarge⟩ := exists_corridor_scales
    ‖P‖ ((pc G:ℝ)/2) C C₁ ε M (cm/((pc G:ℝ)/2)) J k₀ hρpos hρ (half_pos hpcrit) hC hC₁ hε
    (div_pos hcm (half_pos hpcrit)) hJ m R Q hR hQ hmlower hlogR hlogQ
  exact hbad (p n) (hpnear n) (hp n) (A n) (hA n) k hk B hB hsmall htime herror hlarge

end AnalyticCritical

 

theorem nonempty_bonds_of_connected [Infinite V] (G : BondGraph V E) (hconn : Connected G) : Nonempty E := by
  classical
  by_contra he
  let : IsEmpty E := not_nonempty_iff.mp he
  obtain ⟨x,y,hxy⟩ := exists_pair_ne V
  have hh := conn_univ_of_connected G hconn x y
  have heq : (Set.univ : Set E) = ∅ := Set.eq_empty_of_isEmpty _
  rw [heq,conn_empty_iff] at hh
  exact hxy hh

 

theorem critical_bounded_of_transport_finiteness_oai [Infinite V]
    (G : BondGraph V E) (hG : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite) :
    OperatorBounded G (pc G) := by
  classical
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  let : Nonempty E := nonempty_bonds_of_connected G hconn
  let : Nonempty ι := ⟨(hcov (Classical.arbitrary V)).choose⟩
  let c := ∑ i, (weight i)⁻¹
  have hc : 0 < c := Finset.sum_pos (fun i _ => inv_pos.mpr (hw i)) Finset.univ_nonempty
  have hmin (i) : 1 ≤ c*weight i := by
    have hi : (weight i)⁻¹ ≤ c := Finset.single_le_sum
      (fun j _ => (inv_pos.mpr (hw j)).le) (Finset.mem_univ i)
    simpa only [inv_mul_cancel₀ (hw i).ne'] using mul_le_mul_of_nonneg_right hi (hw i).le
  obtain ⟨d,P,hdpos,hd,hρ,hPs,hP⟩ := exists_strict_walk_operator G hloc hqt hh
  let a := (1:ℝ)/(2*d)
  have hdr : (0:ℝ) < d := Nat.cast_pos.mpr hdpos
  have ha : 0 < a := by dsimp [a]; positivity
  have had : a*d = 1/2 := by dsimp [a]; field_simp
  have hPe : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ) := hP
  have hPpos : PositiveRealMatrix P := by
    intro x y
    rw [hPe]
    refine ⟨rfl,?_⟩
    exact walkKernel_nonneg G hloc d hd a ha.le (by rw [had]; norm_num) x y
  have hdiag (x) : 1/2 ≤ (matrixCoeff P x x).re := by
    rw [hPe,Complex.ofReal_re]
    exact walkKernel_lazy G hloc d hd a ha.le had.le x
  exact critical_bounded_of_fixed_data G hG hconn hloc hqt hh a ha root weight htr hcov hw hw1 c hc hmin
    P hPpos hPs.isSelfAdjoint hPe hdiag hρ d hd (pc_pos G hloc hqt)
    (pc_lt_one_of_nonamenable G hconn hloc hqt hh) hfin

end Percolation





end OAI
end

theorem solution.{u, v, u_1} : type_of% @OAI.Percolation.critical_bounded_of_transport_finiteness_oai.{u, v, u_1} := @OAI.Percolation.critical_bounded_of_transport_finiteness_oai.{u, v, u_1}
