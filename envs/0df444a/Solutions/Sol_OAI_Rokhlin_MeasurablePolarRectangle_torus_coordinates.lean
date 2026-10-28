-- Prove2me | solution 1 for OAI.Rokhlin.MeasurablePolarRectangle.torus_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:08:53.485635+00:00
-- url     : https://prove2.me/submissions/bfbfbf5c-4b8f-47b5-83e6-278e23ea520c

import Mathlib
import Definitions.Def_OAIQ3Ro002

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Joinings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

namespace StrongUnitary
open MeasureTheory Filter Topology
open scoped Topology
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SecondCountableTopology E]

lemma code_injective : Function.Injective (code : (E ≃ₗᵢ[ℂ] H) → ℕ → H) := by
  intro U V h
  apply DFunLike.ext'
  exact (TopologicalSpace.denseRange_denseSeq E).equalizer U.continuous V.continuous h

lemma code_embedding : IsEmbedding (code : (E ≃ₗᵢ[ℂ] H) → ℕ → H) :=
  ⟨⟨rfl⟩, code_injective⟩

instance t2 : T2Space (E ≃ₗᵢ[ℂ] H) := code_embedding.t2Space
instance metrizable : TopologicalSpace.MetrizableSpace (E ≃ₗᵢ[ℂ] H) := code_embedding.metrizableSpace
instance secondCountable [SecondCountableTopology H] : SecondCountableTopology (E ≃ₗᵢ[ℂ] H) :=
  code_embedding.secondCountableTopology

lemma continuous_eval : Continuous (fun p : (E ≃ₗᵢ[ℂ] H) × E => p.1 p.2) := by
  apply continuous_prod_of_dense_continuous_lipschitzWith' _ 1
    (TopologicalSpace.denseRange_denseSeq E)
  · intro U; exact U.isometry.lipschitz
  · rintro _ ⟨n, rfl⟩
    exact (continuous_apply n).comp code_embedding.continuous

lemma continuous_apply (v : E) : Continuous (fun U : E ≃ₗᵢ[ℂ] H => U v) :=
  continuous_eval.comp (continuous_id.prodMk continuous_const)

lemma continuous_iff {X : Type*} [TopologicalSpace X] {f : X → E ≃ₗᵢ[ℂ] H} :
    Continuous f ↔ ∀ v, Continuous (fun x => f x v) := by
  constructor
  · intro h v; exact (continuous_apply v).comp h
  · intro h
    exact code_embedding.isInducing.continuous_iff.mpr (continuous_pi (fun n => h _))

lemma tendsto_iff {X : Type*} {l : Filter X} {f : X → E ≃ₗᵢ[ℂ] H} {U : E ≃ₗᵢ[ℂ] H} :
    Tendsto f l (𝓝 U) ↔ ∀ v, Tendsto (fun x => f x v) l (𝓝 (U v)) := by
  constructor
  · intro h v; exact ((continuous_apply v).tendsto U).comp h
  · intro h
    exact code_embedding.isInducing.tendsto_nhds_iff.mpr (tendsto_pi_nhds.mpr (fun n => h _))

lemma measurable_iff [SecondCountableTopology H] {X : Type*} [MeasurableSpace X]
    {f : X → E ≃ₗᵢ[ℂ] H} :
    Measurable f ↔ ∀ v, StronglyMeasurable (fun x => f x v) := by
  borelize H
  constructor
  · intro hf v
    exact ((continuous_apply v).measurable.comp hf).stronglyMeasurable
  · intro hf
    have hc : Measurable (code ∘ f) := Measurable.of_eval (fun n => (hf _).measurable)
    rw [measurable_iff_comap_le]
    change MeasurableSpace.comap f (borel _) ≤ _
    rw [show borel (E ≃ₗᵢ[ℂ] H) = MeasurableSpace.comap code (borel (ℕ → H)) from
      borel_comap]
    rw [MeasurableSpace.comap_comp]
    simpa only [← BorelSpace.measurable_eq (α := ℕ → H)] using hc.comap_le

lemma continuous_symm [SecondCountableTopology H] :
    Continuous (fun U : E ≃ₗᵢ[ℂ] H => U.symm) := by
  rw [_root_.continuous_iff_continuousAt]
  intro U
  apply tendsto_iff.mpr
  intro v
  rw [tendsto_iff_dist_tendsto_zero]
  have hh := ((continuous_apply (U.symm v)).tendsto U).dist (tendsto_const_nhds (x := v))
  have he (V : E ≃ₗᵢ[ℂ] H) : dist (V.symm v) (U.symm v) = dist (V (U.symm v)) v := by
    rw [← V.dist_map, V.apply_symm_apply, dist_comm]
  simp only [he, U.apply_symm_apply, dist_self] at hh ⊢
  exact hh

instance topologicalGroup : IsTopologicalGroup (E ≃ₗᵢ[ℂ] E) where
  continuous_mul := continuous_iff.mpr (fun v =>
    continuous_eval.comp (continuous_fst.prodMk ((continuous_apply v).comp continuous_snd)))
  continuous_inv := continuous_symm
end StrongUnitary

namespace StrongUnitary
open MeasureTheory ProbabilityTheory
open scoped Topology
variable {H₁ H₂ H₃ H₄ : Type*}
  [NormedAddCommGroup H₁] [NormedSpace ℂ H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [NormedSpace ℂ H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [NormedSpace ℂ H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [NormedSpace ℂ H₄] [SecondCountableTopology H₄]

omit [SecondCountableTopology H₁] in
lemma continuous_normalizeA (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂) :
    Continuous (normalizeA a₀ d₀) := by
  apply continuous_iff.mpr
  intro v
  exact (d₀.trans a₀).symm.continuous.comp (continuous_apply (d₀ v))
omit [SecondCountableTopology H₃] in
lemma continuous_normalizeB (b₀ : H₄ ≃ₗᵢ[ℂ] H₃) : Continuous (normalizeB b₀) := by
  apply continuous_iff.mpr
  intro v
  exact b₀.symm.continuous.comp (continuous_apply v)
omit [SecondCountableTopology H₁] [SecondCountableTopology H₂] in
lemma continuous_normalizeC (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (b₀ : H₄ ≃ₗᵢ[ℂ] H₃) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂) :
    Continuous (normalizeC a₀ b₀ d₀) := by
  apply continuous_iff.mpr
  intro v
  exact (d₀.trans a₀).symm.continuous.comp (continuous_apply (b₀ v))
omit [SecondCountableTopology H₂] in
lemma continuous_normalizeD (d₀ : H₄ ≃ₗᵢ[ℂ] H₂) : Continuous (normalizeD d₀) := by
  apply continuous_iff.mpr
  intro v
  exact d₀.symm.continuous.comp (continuous_apply v)

omit [SecondCountableTopology H₁] [SecondCountableTopology H₂] [SecondCountableTopology H₃] [SecondCountableTopology H₄] in
lemma normalized_rectangle (a₀ a : H₂ ≃ₗᵢ[ℂ] H₁) (b₀ b : H₄ ≃ₗᵢ[ℂ] H₃)
    (c : H₃ ≃ₗᵢ[ℂ] H₁) (d₀ d : H₄ ≃ₗᵢ[ℂ] H₂)
    (hr : d.trans a = b.trans c) :
    normalizeA a₀ d₀ a * normalizeD d₀ d = normalizeC a₀ b₀ d₀ c * normalizeB b₀ b := by
  ext v
  have hh := congrArg (fun L : H₄ ≃ₗᵢ[ℂ] H₁ => L v) hr
  simpa [normalizeA, normalizeB, normalizeC, normalizeD] using congrArg (d₀.trans a₀).symm hh

end StrongUnitary

section
open MeasureTheory ProbabilityTheory
variable {Z X Y A B : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace A] [MeasurableSpace B]
  {f : X → A} {g : Y → B}
lemma map_pair_fst (μ : Measure (X × Y)) (hf : Measurable f) (hg : Measurable g) :
    (μ.map (Prod.map f g)).map Prod.fst = (μ.map Prod.fst).map f := by
  rw [Measure.map_map measurable_fst (hf.prodMap hg), Measure.map_map hf measurable_fst]
  rfl
lemma map_pair_snd (μ : Measure (X × Y)) (hf : Measurable f) (hg : Measurable g) :
    (μ.map (Prod.map f g)).map Prod.snd = (μ.map Prod.snd).map g := by
  rw [Measure.map_map measurable_snd (hf.prodMap hg), Measure.map_map hg measurable_snd]
  rfl
lemma kernel_map_pair_fst (κ : Kernel Z (X × Y)) (z : Z) (hf : Measurable f) (hg : Measurable g) :
    ((κ.map (Prod.map f g)) z).map Prod.fst = ((κ z).map Prod.fst).map f := by
  rw [Kernel.map_apply κ (hf.prodMap hg), map_pair_fst _ hf hg]
lemma kernel_map_pair_snd (κ : Kernel Z (X × Y)) (z : Z) (hf : Measurable f) (hg : Measurable g) :
    ((κ.map (Prod.map f g)) z).map Prod.snd = ((κ z).map Prod.snd).map g := by
  rw [Kernel.map_apply κ (hf.prodMap hg), map_pair_snd _ hf hg]

end

namespace ConditionalFibres
open MeasureTheory ProbabilityTheory
variable {Ω Z V : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace V]
  {μ : Measure Ω} [SFinite μ] {z : Ω → Z} {v : Ω → V}
  {κ : Kernel Z V} [IsSFiniteKernel κ]

lemma ae_kernel (h : HasCondDistrib v z κ μ) {p : V → Prop}
    (hp : MeasurableSet {v | p v}) (hv : ∀ᵐ ω ∂μ, p (v ω)) :
    ∀ᵐ a ∂μ.map z, ∀ᵐ b ∂κ a, p b := by
  apply Measure.ae_ae_of_ae_compProd (p := fun q => p q.2)
  rw [←h.map_eq]
  exact (ae_map_iff h.aemeasurable (hp.preimage measurable_snd)).mpr hv
end ConditionalFibres

section

open MeasureTheory ContinuousLinearMap InnerProductSpace Filter
open scoped InnerProductSpace ComplexOrder Topology BigOperators


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in

theorem isClosed_positive_operators :
    IsClosed {Q : H →L[ℂ] H | Q.IsPositive} := by
  simp only [ContinuousLinearMap.isPositive_iff_complex, Set.ofPred_forall, Set.ofPred_and]
  exact isClosed_iInter fun x =>
    (isClosed_eq (Complex.continuous_ofReal.comp
      (Complex.continuous_re.comp (((ContinuousLinearMap.apply ℂ H x).continuous).inner
        continuous_const)))
      (((ContinuousLinearMap.apply ℂ H x).continuous).inner continuous_const)).inter
      (isClosed_le continuous_const (Complex.continuous_re.comp
        (((ContinuousLinearMap.apply ℂ H x).continuous).inner continuous_const)))

omit [CompleteSpace H] in

theorem convex_positive_operators :
    Convex ℝ {Q : H →L[ℂ] H | Q.IsPositive} := by
  intro A hA B hB a b ha hb _
  change (a • A + b • B).IsPositive
  have hA' : ((a : ℂ) • A).IsPositive := hA.smul_of_nonneg (by exact_mod_cast ha)
  have hB' : ((b : ℂ) • B).IsPositive := hB.smul_of_nonneg (by exact_mod_cast hb)
  simpa only [Complex.coe_smul] using hA'.add hB'

section Integral
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

theorem positive_compact_integral {F : X → H →L[ℂ] H}
    (hF : Integrable F μ) (hp : ∀ᵐ x ∂μ, (F x).IsPositive)
    (hc : ∀ᵐ x ∂μ, IsCompactOperator (F x)) :
    (∫ x, F x ∂μ).IsPositive ∧ IsCompactOperator (⇑(∫ x, F x ∂μ)) := by
  constructor
  · exact (convex_positive_operators (H := H)).integral_mem
      (isClosed_positive_operators (H := H)) hp hF
  · have hconv : Convex ℝ {Q : H →L[ℂ] H | IsCompactOperator Q} :=
      ((compactOperator (RingHom.id ℂ) H H).restrictScalars ℝ).convex
    exact hconv.integral_mem isClosed_setOfPred_isCompactOperator hc hF

theorem strict_positive_integral {F : X → H →L[ℂ] H}
    (hF : Integrable F μ)
    (hp : ∀ v : H, v ≠ 0 → ∀ᵐ x ∂μ, 0 < (inner ℂ v (F x v)).re) :
    ∀ v : H, v ≠ 0 → 0 < (inner ℂ v ((∫ x, F x ∂μ) v)).re := by
  intro v hv
  have hFi : Integrable (fun x => F x v) μ := (ContinuousLinearMap.apply ℂ H v).integrable_comp hF
  have hinner : Integrable (fun x => inner ℂ v (F x v)) μ :=
    (innerSL ℂ v).integrable_comp hFi
  have hreal : Integrable (fun x => (inner ℂ v (F x v)).re) μ := hinner.re
  rw [ContinuousLinearMap.integral_apply hF]
  have hi := (innerSL ℂ v).integral_comp_comm hFi
  change (∫ x, inner ℂ v (F x v) ∂μ) = inner ℂ v (∫ x, F x v ∂μ) at hi
  rw [← hi]
  change 0 < RCLike.re (∫ x, inner ℂ v (F x v) ∂μ)
  rw [← integral_re hinner]
  apply (integral_pos_iff_support_of_nonneg_ae ((hp v hv).mono fun _ h => h.le) hreal).2
  have : Function.support (fun x => (inner ℂ v (F x v)).re) =ᵐ[μ] Set.univ := by
    filter_upwards [hp v hv] with x hx
    apply propext
    change ((inner ℂ v (F x v)).re ≠ 0) ↔ True
    exact iff_of_true (ne_of_gt hx) trivial
  rw [measure_congr this, measure_univ]
  exact zero_lt_one

omit [CompleteSpace H] in

theorem injective_of_strict_positive (Q : H →L[ℂ] H)
    (hQ : ∀ v : H, v ≠ 0 → 0 < (inner ℂ v (Q v)).re) : Function.Injective Q := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  change Q v = 0 at hv
  by_contra hv'
  have := hQ v hv'
  simp [hv] at this

end Integral
section Conjugation

theorem conjugateOperator_positive (U : H ≃ₗᵢ[ℂ] H) {Q : H →L[ℂ] H}
    (hQ : Q.IsPositive) : (conjugateOperator U Q).IsPositive := by
  have he : conjugateOperator U Q =
      (U : H →L[ℂ] H) ∘L Q ∘L (U : H →L[ℂ] H).adjoint := by
    ext v
    simp only [conjugateOperator_apply, LinearIsometryEquiv.adjoint_eq_symm,
      ContinuousLinearMap.comp_apply]
    rfl
  rw [he]
  exact hQ.conj_adjoint (U : H →L[ℂ] H)

omit [CompleteSpace H] in
theorem conjugateOperator_compact (U : H ≃ₗᵢ[ℂ] H) {Q : H →L[ℂ] H}
    (hQ : IsCompactOperator Q) : IsCompactOperator (conjugateOperator U Q) :=
  (hQ.comp_clm (U.symm : H →L[ℂ] H)).clm_comp (U : H →L[ℂ] H)

omit [CompleteSpace H] in
theorem conjugateOperator_strict_positive (U : H ≃ₗᵢ[ℂ] H) {Q : H →L[ℂ] H}
    (hQ : ∀ v : H, v ≠ 0 → 0 < (inner ℂ v (Q v)).re) :
    ∀ v : H, v ≠ 0 → 0 < (inner ℂ v (conjugateOperator U Q v)).re := by
  intro v hv
  have hUv : U.symm v ≠ 0 := by simpa using hv
  have hi := U.inner_map_map (U.symm v) (Q (U.symm v))
  simp only [LinearIsometryEquiv.apply_symm_apply] at hi
  rw [conjugateOperator_apply, hi]
  exact hQ _ hUv

variable {G : Type*} [Group G] [MeasurableSpace G] {μ : Measure G}
  [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in

theorem averaged_conjugates_commute (U : G →* (H ≃ₗᵢ[ℂ] H)) (Q : H →L[ℂ] H)
    (hm : ∀ g : G, Measurable (fun x : G => g * x))
    (hinv : ∀ g : G, Measure.map (fun x : G => g * x) μ = μ)
    (hF : Integrable (fun x => conjugateOperator (U x) Q) μ) (g : G) :
    (∫ x, conjugateOperator (U x) Q ∂μ) ∘L (U g : H →L[ℂ] H) =
      (U g : H →L[ℂ] H) ∘L (∫ x, conjugateOperator (U x) Q ∂μ) := by
  have hi : conjugateOperator (U g) (∫ x, conjugateOperator (U x) Q ∂μ) =
      ∫ x, conjugateOperator (U x) Q ∂μ := by
    rw [← (conjugateOperator (U g)).integral_comp_comm hF]
    simp_rw [← conjugateOperator_mul, ← map_mul]
    have hmeas : AEStronglyMeasurable (fun x => conjugateOperator (U x) Q)
        (Measure.map (fun x : G => g * x) μ) := by
      rw [hinv g]
      exact hF.aestronglyMeasurable
    rw [← integral_map (hm g).aemeasurable hmeas, hinv g]
  ext v
  have hv := congrArg (fun A : H →L[ℂ] H => A (U g v)) hi
  change (∫ x, conjugateOperator (U x) Q ∂μ) (U g v) =
    U g ((∫ x, conjugateOperator (U x) Q ∂μ) v)
  simpa only [conjugateOperator_apply, LinearIsometryEquiv.symm_apply_apply] using hv.symm

theorem averaged_positive_compact_injective
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (Q : H →L[ℂ] H)
    (hm : ∀ g : G, Measurable (fun x : G => g * x))
    (hinv : ∀ g : G, Measure.map (fun x : G => g * x) μ = μ)
    (hp : Q.IsPositive) (hc : IsCompactOperator Q)
    (hs : ∀ v : H, v ≠ 0 → 0 < (inner ℂ v (Q v)).re)
    (hF : Integrable (fun x => conjugateOperator (U x) Q) μ) :
    ∃ Q₀ : H →L[ℂ] H, Q₀.IsPositive ∧ IsCompactOperator Q₀ ∧ Function.Injective Q₀ ∧
      ∀ g : G, Q₀ ∘L (U g : H →L[ℂ] H) = (U g : H →L[ℂ] H) ∘L Q₀ := by
  let Q₀ : H →L[ℂ] H := ∫ x, conjugateOperator (U x) Q ∂μ
  have hpc := positive_compact_integral hF
    (Filter.Eventually.of_forall fun x => conjugateOperator_positive (U x) hp)
    (Filter.Eventually.of_forall fun x => conjugateOperator_compact (U x) hc)
  refine ⟨Q₀, hpc.1, hpc.2, ?_, averaged_conjugates_commute U Q hm hinv hF⟩
  apply injective_of_strict_positive
  exact strict_positive_integral hF fun v hv =>
    Filter.Eventually.of_forall fun x => conjugateOperator_strict_positive (U x) hs v hv

end Conjugation
section CompactSeed

omit [CompleteSpace H] in
theorem weighted_rankOne_quadratic (w v : H) (c : ℝ) :
    quadraticFormCLM v ((c : ℂ) • rankOne ℂ w w) =
      c * Complex.normSq (inner ℂ w v) := by
  simp only [quadraticFormCLM_apply, smul_apply, rankOne_apply,
    inner_smul_right]
  rw [← inner_conj_symm v w, Complex.mul_conj]
  simp

omit [CompleteSpace H] in
theorem compact_rankOne (v w : H) : IsCompactOperator (rankOne ℂ v w) := by
  exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ w)).clm_comp
    (toSpanSingleton ℂ v)

theorem positive_compact_tsum {F : ℕ → H →L[ℂ] H} (hF : Summable F)
    (hp : ∀ n, (F n).IsPositive) (hc : ∀ n, IsCompactOperator (F n)) :
    (∑' n, F n).IsPositive ∧ IsCompactOperator (⇑(∑' n, F n)) := by
  constructor
  · exact (isClosed_positive_operators (H := H)).mem_of_tendsto hF.hasSum
      (Filter.Eventually.of_forall fun s => ContinuousLinearMap.isPositive_sum s fun n _ => hp n)
  · apply isCompactOperator_of_tendsto hF.hasSum
    exact Filter.Eventually.of_forall fun s =>
      (compactOperator (RingHom.id ℂ) H H).sum_mem fun n _ => hc n

omit [CompleteSpace H] in

theorem dense_sequence_inner_ne_zero {w : ℕ → H} (hw : DenseRange w)
    (v : H) (hv : v ≠ 0) : ∃ n, inner ℂ (w n) v ≠ 0 := by
  by_contra! hn
  have hclosed : IsClosed {x : H | inner ℂ x v = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hsub : Set.range w ⊆ {x : H | inner ℂ x v = 0} := by
    rintro _ ⟨n, rfl⟩
    exact hn n
  have hall := hclosed.closure_subset_iff.mpr hsub
  rw [hw.closure_range] at hall
  exact hv (inner_self_eq_zero.mp (hall (Set.mem_univ v)))

omit [CompleteSpace H] in

theorem weighted_rankOne_tsum_strict {w : ℕ → H} (hw : DenseRange w)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (hs : Summable (fun n => (c n : ℂ) • rankOne ℂ (w n) (w n))) :
    ∀ v : H, v ≠ 0 →
      0 < (inner ℂ v ((∑' n, (c n : ℂ) • rankOne ℂ (w n) (w n)) v)).re := by
  intro v hv
  obtain ⟨n, hn⟩ := dense_sequence_inner_ne_zero hw v hv
  change 0 < quadraticFormCLM v (∑' n, (c n : ℂ) • rankOne ℂ (w n) (w n))
  rw [(quadraticFormCLM v).map_tsum hs]
  have hsum := (quadraticFormCLM v).summable hs
  have hnonneg (m : ℕ) : 0 ≤ quadraticFormCLM v ((c m : ℂ) • rankOne ℂ (w m) (w m)) := by
    rw [weighted_rankOne_quadratic]
    exact mul_nonneg (hc m).le (Complex.normSq_nonneg _)
  have hpos : 0 < quadraticFormCLM v ((c n : ℂ) • rankOne ℂ (w n) (w n)) := by
    rw [weighted_rankOne_quadratic]
    exact mul_pos (hc n) (Complex.normSq_pos.mpr hn)
  exact hpos.trans_le (hsum.le_tsum n fun m _ => hnonneg m)

omit [CompleteSpace H] [InnerProductSpace ℂ H] in
theorem compactSeedWeight_pos (w : ℕ → H) (n : ℕ) : 0 < compactSeedWeight w n := by
  unfold compactSeedWeight
  positivity

omit [CompleteSpace H] in
theorem compactSeedWeight_bound (w : ℕ → H) (n : ℕ) :
    ‖(compactSeedWeight w n : ℂ) • rankOne ℂ (w n) (w n)‖ ≤ (1 / 2 : ℝ) ^ n := by
  rw [norm_smul, norm_rankOne, Complex.norm_real, Real.norm_eq_abs, abs_of_pos
    (compactSeedWeight_pos w n)]
  unfold compactSeedWeight
  rw [← sq, div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 1 + ‖w n‖ ^ 2)).2
  have h : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  nlinarith

end CompactSeed

omit [CompleteSpace H] in

theorem conjugateOperator_rankOne (U : H ≃ₗᵢ[ℂ] H) (v w : H) :
    conjugateOperator U (rankOne ℂ v w) = rankOne ℂ (U v) (U w) := by
  ext x
  simp only [conjugateOperator_apply, rankOne_apply, map_smul]
  congr 1
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (U.inner_map_map w (U.symm x)).symm

theorem norm_conjugateOperator (U : H ≃ₗᵢ[ℂ] H) (Q : H →L[ℂ] H) :
    ‖conjugateOperator U Q‖ = ‖Q‖ :=
  StarAlgEquiv.norm_map U.conjStarAlgEquiv Q

theorem compactSeed_summable (w : ℕ → H) :
    Summable (fun n => (compactSeedWeight w n : ℂ) • rankOne ℂ (w n) (w n)) :=
  summable_geometric_two.of_norm_bounded (compactSeedWeight_bound w)

theorem continuous_conjugate_compactSeed {G : Type*} [TopologicalSpace G]
    (U : G → H ≃ₗᵢ[ℂ] H) (hU : ∀ v, Continuous (fun g => U g v)) (w : ℕ → H) :
    Continuous (fun g => conjugateOperator (U g) (compactSeed w)) := by
  have he (g : G) : conjugateOperator (U g) (compactSeed w) =
      ∑' n, (compactSeedWeight w n : ℂ) • rankOne ℂ (U g (w n)) (U g (w n)) := by
    unfold compactSeed
    rw [(conjugateOperator (U g)).map_tsum (compactSeed_summable w)]
    simp only [map_smul, conjugateOperator_rankOne]
  simp_rw [he]
  refine continuous_tsum (u := fun n => (1 / 2 : ℝ) ^ n) (fun n => ?_)
    summable_geometric_two (fun n g => ?_)
  · simp only [rankOne_def]
    exact (((ContinuousLinearMap.smulRightL ℂ H H).continuous.comp
      ((innerSL ℂ).continuous.comp (hU (w n)))).clm_apply (hU (w n))).const_smul
        (compactSeedWeight w n : ℂ)
  ·
    rw [← conjugateOperator_rankOne, ← map_smul, norm_conjugateOperator]
    exact compactSeedWeight_bound w n

theorem compactSeed_properties {w : ℕ → H} (hw : DenseRange w) :
    (compactSeed w).IsPositive ∧ IsCompactOperator (compactSeed w) ∧
      ∀ v, v ≠ 0 → 0 < (inner ℂ v (compactSeed w v)).re := by
  have hs := compactSeed_summable w
  have hpc := positive_compact_tsum hs
    (fun n => (isPositive_rankOne_self (w n)).smul_of_nonneg
      (by exact_mod_cast (compactSeedWeight_pos w n).le))
    (fun n => (compact_rankOne (w n) (w n)).smul (compactSeedWeight w n : ℂ))
  exact ⟨hpc.1, hpc.2, weighted_rankOne_tsum_strict hw _ (compactSeedWeight_pos w) hs⟩

theorem exists_invariant_positive_compact
    [TopologicalSpace.SeparableSpace H] {G : Type*} [Group G]
    [TopologicalSpace G] [SecondCountableTopology G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsProbabilityMeasure μ]
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (hU : ∀ v, Continuous (fun g => U g v))
    (hinv : ∀ g : G, Measure.map (fun x => g * x) μ = μ) :
    ∃ Q₀ : H →L[ℂ] H, Q₀.IsPositive ∧ IsCompactOperator Q₀ ∧ Function.Injective Q₀ ∧
      ∀ g : G, Q₀ ∘L (U g : H →L[ℂ] H) = (U g : H →L[ℂ] H) ∘L Q₀ := by
  obtain ⟨w, hw⟩ := TopologicalSpace.exists_dense_seq H
  obtain ⟨hp, hc, hs⟩ := compactSeed_properties hw
  apply averaged_positive_compact_injective (μ := μ) U (compactSeed w)
    (fun g => measurable_const.mul measurable_id) hinv hp hc hs
  exact Integrable.of_bound (continuous_conjugate_compactSeed U hU w).aestronglyMeasurable
    ‖compactSeed w‖ (Filter.Eventually.of_forall fun g => (norm_conjugateOperator (U g) _).le)

end

section
open Module.End ContinuousLinearMap
variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma symmetric_joint_total (Q : H →L[ℂ] H) (S : J → H →L[ℂ] H)
    (hQ : Q.IsPositive) (hc : IsCompactOperator Q) (hi : Function.Injective Q)
    (hS : ∀ j, (S j).toLinearMap.IsSymmetric)
    (hQS : ∀ j, Commute Q (S j)) (hSS : ∀ i j, Commute (S i) (S j)) :
    (⨆ χ : J → ℂ, ⨅ j, eigenspace (S j).toLinearMap (χ j)).topologicalClosure = ⊤ := by
  let P := ⨆ χ : J → ℂ, ⨅ j, eigenspace (S j).toLinearMap (χ j)
  have hE (μ : ℂ) : eigenspace Q.toLinearMap μ ≤ P := by
    by_cases hμ : μ = 0
    · subst μ
      intro x hx
      have hx0 : Q x = Q 0 := by simpa [mem_eigenspace_iff] using hx
      exact hi hx0 ▸ P.zero_mem
    let E := eigenspace Q.toLinearMap μ
    let : FiniteDimensional ℂ E := ContinuousLinearMap.finite_dimensional_eigenspace hc μ hμ
    have hInv (j) : ∀ x ∈ E, S j x ∈ E := by
      intro x hx
      apply mem_eigenspace_iff.mpr
      have hx := mem_eigenspace_iff.mp hx
      change Q x = μ • x at hx
      calc
        Q (S j x) = S j (Q x) := congrArg (fun A : H →L[ℂ] H => A x) (hQS j)
        _ = μ • S j x := by rw [hx, map_smul]
    let R : J → E →ₗ[ℂ] E := fun j => (S j).toLinearMap.restrict (hInv j)
    have hRs (j) : (R j).IsSymmetric := (hS j).restrict_invariant (hInv j)
    have hRc (i j) : Commute (R i) (R j) := by
      ext v
      exact congrArg (fun A : H →L[ℂ] H => A (v : H)) (hSS i j)
    have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hRs
      (fun i j _ => hRc i j)
    intro x hx
    have hx' : (⟨x,hx⟩ : E) ∈ ⨆ χ : J → ℂ, ⨅ j, eigenspace (R j) (χ j) := by
      rw [htop]; trivial
    change (⟨x,hx⟩ : E).val ∈ P
    apply Submodule.iSup_induction (motive := fun v : E => (v : H) ∈ P) _ hx'
    · intro χ v hv
      apply (le_iSup (fun χ : J → ℂ => ⨅ j, eigenspace (S j).toLinearMap (χ j)) χ)
      apply (Submodule.mem_iInf _).mpr
      intro j
      have hvj := mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv j)
      exact mem_eigenspace_iff.mpr (congrArg Subtype.val hvj)
    · exact P.zero_mem
    · intro v w hv hw
      exact P.add_mem hv hw
  have hQt : (⨆ μ, eigenspace Q.toLinearMap μ).topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.mpr
      (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hQ.isSymmetric)
  apply top_unique
  rw [←hQt]
  exact Submodule.topologicalClosure_mono (iSup_le hE)

end

section
open Module.End ContinuousLinearMap
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma part_commute {A B : H →L[ℂ] H} (h : Commute A B) (hs : Commute (star A) B) (b : Bool) :
    Commute (unitaryPart A b : H →L[ℂ] H) B := by
  cases b
  · rw [unitaryPart, realPart_apply_coe]
    exact (h.add_left hs).smul_left _
  · rw [unitaryPart, imaginaryPart_apply_coe]
    exact ((h.sub_left hs).smul_left _).smul_left _

lemma parts_commute {A B : H →L[ℂ] H} (h : Commute A B) (hs : Commute (star A) B)
    (ht : Commute A (star B)) (hst : Commute (star A) (star B)) (b c : Bool) :
    Commute (unitaryPart A b : H →L[ℂ] H) (unitaryPart B c : H →L[ℂ] H) :=
  part_commute (part_commute h.symm ht.symm c).symm
    (part_commute hs.symm hst.symm c).symm b

omit [CompleteSpace H] in
lemma unitary_clm_commute {U V : H ≃ₗᵢ[ℂ] H} (h : Commute U V) :
    Commute (U : H →L[ℂ] H) (V : H →L[ℂ] H) := by
  ext x
  exact congrArg (fun W : H ≃ₗᵢ[ℂ] H => W x) h

end

section
open Module.End ContinuousLinearMap
universe u v
variable {H : Type u} {J : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma orthogonal_total_basis (E : J → Submodule ℂ H) [∀ j, CompleteSpace (E j)]
    (ho : OrthogonalFamily ℂ (fun j => E j) (fun j => (E j).subtypeₗᵢ))
    (ht : (⨆ j, E j).topologicalClosure = ⊤) :
    ∃ (I : Type (max u v)) (b : HilbertBasis I ℂ H) (q : I → J), ∀ i, b i ∈ E (q i) := by
  choose W B hB using (fun j => exists_hilbertBasis ℂ (E j))
  let v : (Σ j, W j) → H := fun i => (B i.1 i.2 : H)
  have hv : Orthonormal ℂ v := ho.orthonormal_sigma_orthonormal (fun j => (B j).orthonormal)
  let P := (Submodule.span ℂ (Set.range v)).topologicalClosure
  have hEP (j : J) : E j ≤ P := by
    let R := P.comap (E j).subtype
    have hR : IsClosed (R : Set (E j)) := (Submodule.isClosed_topologicalClosure (Submodule.span ℂ (Set.range v))).preimage
      continuous_subtype_val
    have hBR : Submodule.span ℂ (Set.range (B j)) ≤ R := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨j,i⟩,rfl⟩)
    have htop : (⊤ : Submodule ℂ (E j)) ≤ R := by
      rw [←(B j).dense_span]
      exact Submodule.topologicalClosure_minimal _ hBR hR
    intro x hx
    exact htop (show (⟨x,hx⟩ : E j) ∈ (⊤ : Submodule ℂ (E j)) from trivial)
  have hP : ⊤ ≤ P := by
    rw [←ht]
    exact Submodule.topologicalClosure_minimal _ (iSup_le hEP)
      (Submodule.isClosed_topologicalClosure _)
  refine ⟨Σ j, W j, HilbertBasis.mk hv hP, Sigma.fst, ?_⟩
  intro i
  rw [HilbertBasis.coe_mk]
  exact (B i.1 i.2).property

lemma symmetric_joint_basis (S : J → H →L[ℂ] H)
    (hS : ∀ j, (S j).toLinearMap.IsSymmetric)
    (ht : (⨆ χ : J → ℂ, ⨅ j, eigenspace (S j).toLinearMap (χ j)).topologicalClosure = ⊤) :
    ∃ (I : Type (max u v)) (b : HilbertBasis I ℂ H) (χ : I → J → ℂ),
      ∀ i j, S j (b i) = χ i j • b i := by
  let E (χ : J → ℂ) := ⨅ j, eigenspace (S j).toLinearMap (χ j)
  have hclosed (χ : J → ℂ) : IsClosed (E χ : Set H) := by
    change IsClosed ((⨅ j, eigenspace (S j).toLinearMap (χ j) : Submodule ℂ H) : Set H)
    rw [Submodule.coe_iInf]
    exact isClosed_iInter fun j => ContinuousLinearMap.isClosed_eigenspace (S j) (χ j)
  let (χ : J → ℂ) : CompleteSpace (E χ) := (hclosed χ).completeSpace_coe
  obtain ⟨I,b,χ,hb⟩ := orthogonal_total_basis E
    (LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hS) ht
  refine ⟨I,b,χ,?_⟩
  intro i j
  exact mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp (hb i) j)

end

section
variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H]

lemma hilbertBasis_countable (b : HilbertBasis I ℂ H) : Countable I := by
  classical
  let d := TopologicalSpace.denseSeq H
  let S (n : ℕ) := Function.support (fun i => b.repr (d n) i • b i)
  have hc (n) : (S n).Countable := (b.hasSum_repr (d n)).summable.countable_support
  have ht : (Set.univ : Set I) ⊆ ⋃ n, S n := by
    intro i _
    by_contra hi
    have hz (n : ℕ) : inner ℂ (b i) (d n) = 0 := by
      have hin : i ∉ S n := fun h => hi (Set.mem_iUnion.mpr ⟨n,h⟩)
      have he : b.repr (d n) i • b i = 0 := by simpa only [S, Function.mem_support, not_not] using hin
      have he' : b.repr (d n) i = 0 := (smul_eq_zero.mp he).resolve_right (b.orthonormal.ne_zero i)
      simpa only [b.repr_apply_apply] using he'
    have hz' : ∀ x : H, inner ℂ (b i) x = 0 := by
      exact congrFun ((TopologicalSpace.denseRange_denseSeq H).equalizer
        (continuous_const.inner continuous_id) continuous_const (funext hz))
    have hh := hz' (b i)
    exact b.orthonormal.ne_zero i (inner_self_eq_zero.mp hh)
  exact Set.countable_univ_iff.mp ((Set.countable_iUnion hc).mono ht)

end

section
open Module.End ContinuousLinearMap
universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma unitary_joint_basis {G : Type v} [CommGroup G] (U : G →* (H ≃ₗᵢ[ℂ] H))
    (Q : H →L[ℂ] H) (hQ : Q.IsPositive) (hc : IsCompactOperator Q)
    (hi : Function.Injective Q) (hQU : ∀ g, Commute Q (U g : H →L[ℂ] H)) :
    ∃ (I : Type (max u v)) (b : HilbertBasis I ℂ H) (χ : I → G → ℂ),
      ∀ i g, U g (b i) = χ i g • b i := by
  let S : G × Bool → H →L[ℂ] H := fun p => unitaryPart (U p.1 : H →L[ℂ] H) p.2
  have hcomm (g h : G) : Commute (U g : H →L[ℂ] H) (U h : H →L[ℂ] H) :=
    unitary_clm_commute (by rw [Commute, SemiconjBy, ←map_mul, ←map_mul, mul_comm])
  have hstar (g : G) : star (U g : H →L[ℂ] H) = (U g⁻¹ : H →L[ℂ] H) := by
    simp only [LinearIsometryEquiv.star_eq_symm, map_inv]; rfl
  have hQS (p : G × Bool) : Commute Q (S p) := by
    apply Commute.symm
    apply part_commute (hQU p.1).symm
    rw [hstar]
    exact (hQU p.1⁻¹).symm
  have hSS (p q : G × Bool) : Commute (S p) (S q) := by
    apply parts_commute (hcomm p.1 q.1)
    · rw [hstar]; exact hcomm _ _
    · rw [hstar]; exact hcomm _ _
    · rw [hstar, hstar]; exact hcomm _ _
  have htotal := symmetric_joint_total Q S hQ hc hi
    (fun p => (unitaryPart (U p.1 : H →L[ℂ] H) p.2).property.isSymmetric) hQS hSS
  obtain ⟨I,b,χ,hb⟩ := symmetric_joint_basis S
    (fun p => (unitaryPart (U p.1 : H →L[ℂ] H) p.2).property.isSymmetric) htotal
  refine ⟨I,b,(fun i g => χ i (g,false) + Complex.I * χ i (g,true)),?_⟩
  intro i g
  have hr := hb i (g,false)
  have him := hb i (g,true)
  change (realPart (U g : H →L[ℂ] H) : H →L[ℂ] H) (b i) = χ i (g,false) • b i at hr
  change (imaginaryPart (U g : H →L[ℂ] H) : H →L[ℂ] H) (b i) = χ i (g,true) • b i at him
  have hid := congrArg (fun A : H →L[ℂ] H => A (b i))
    (realPart_add_I_smul_imaginaryPart (U g : H →L[ℂ] H))
  change (U g : H →L[ℂ] H) (b i) = _
  simpa only [add_apply, smul_apply, hr, him, smul_smul, ←add_smul] using hid.symm

end

section
variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [Group G]

lemma continuous_eigenCharacter [TopologicalSpace G]
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (hU : ∀ v, Continuous (fun g => U g v))
    {v : H} (hv : v ≠ 0) (χ : G → ℂ) (he : ∀ g, U g v = χ g • v) :
    Continuous (eigenCharacter U hv χ he) := by
  apply Continuous.subtype_mk
  change Continuous χ
  have heq (g : G) : χ g = inner ℂ v (U g v) / inner ℂ v v := by
    rw [he, inner_smul_right, mul_div_cancel_right₀ _ (inner_self_eq_zero.not.mpr hv)]
  exact ((continuous_const.inner (hU v)).div_const _).congr (fun g => (heq g).symm)

end

section
open MeasureTheory
variable {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]

lemma subgroup_probability (G : Subgroup A) (hG : IsClosed (G : Set A))
    (μ : Measure A) [IsProbabilityMeasure μ] (hs : μ.support = (G : Set A))
    (hinv : ∀ g ∈ G, μ.map (g * ·) = μ) :
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧
      ν.map (fun g : G => (g : A)) = μ ∧
      ∀ g : G, ν.map (g * ·) = ν := by
  have he : MeasurableEmbedding (fun g : G => (g : A)) :=
    MeasurableEmbedding.subtype_coe hG.measurableSet
  have ha : ∀ᵐ a ∂μ, a ∈ Set.range (fun g : G => (g : A)) := by
    have hr : Set.range (fun g : G => (g : A)) = (G : Set A) := by
      ext a
      exact ⟨fun ⟨g,hg⟩ => hg ▸ g.property, fun ha => ⟨⟨a,ha⟩,rfl⟩⟩
    rw [hr, ←hs]
    exact Measure.support_mem_ae
  let ν := μ.comap (fun g : G => (g : A))
  have hn : IsProbabilityMeasure ν := isProbabilityMeasure_comap he.injective ha he.measurableSet_image'
  have hmap : ν.map (fun g : G => (g : A)) = μ := by
    change Measure.map _ (Measure.comap _ _) = _
    rw [he.map_comap, Measure.restrict_eq_self_of_ae_mem ha]
  refine ⟨ν,hn,hmap,?_⟩
  intro g
  have hmg : Measurable (g * · : G → G) :=
    (continuous_const.mul continuous_id).measurable
  apply he.map_injective
  rw [Measure.map_map he.measurable hmg, hmap]
  change Measure.map (fun x : G => (g : A) * (x : A)) ν = μ
  have hcomp := Measure.map_map (μ := ν)
    (measurable_const.mul measurable_id : Measurable (fun x : A => (g : A) * x)) he.measurable
  exact hcomp.symm.trans ((congrArg (Measure.map (fun x : A => (g : A) * x)) hmap).trans
    (hinv g g.property))
end

namespace StrongUnitary
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [SecondCountableTopology H]

lemma polar_spectral (G : Subgroup (H ≃ₗᵢ[ℂ] H)) (hG : IsClosed (G : Set (H ≃ₗᵢ[ℂ] H)))
    (μ : Measure (H ≃ₗᵢ[ℂ] H)) [IsProbabilityMeasure μ]
    (hs : μ.support = (G : Set (H ≃ₗᵢ[ℂ] H)))
    (hcomm : ∀ g ∈ G, ∀ h ∈ G, g*h = h*g)
    (hinv : ∀ g ∈ G, μ.map (g * ·) = μ) :
    ∃ (I : Type u) (_ : Countable I) (b : HilbertBasis I ℂ H)
      (γ : I → G →* Circle),
      (∀ i, Continuous (γ i)) ∧ ∀ i (g : G), (g : H ≃ₗᵢ[ℂ] H) (b i) = (γ i g : ℂ) • b i := by
  let : SecondCountableTopology G :=
    TopologicalSpace.Subtype.secondCountableTopology (G : Set (H ≃ₗᵢ[ℂ] H))
  let : CommGroup G := {
    (inferInstance : Group G) with
    mul_comm := fun g h => Subtype.ext (hcomm g g.property h h.property) }
  obtain ⟨ν,hn,hν,hiν⟩ := subgroup_probability G hG μ hs hinv
  let := hn
  let U : G →* (H ≃ₗᵢ[ℂ] H) := G.subtype
  have hUc (v : H) : Continuous (fun g : G => U g v) :=
    (continuous_apply v).comp continuous_subtype_val
  obtain ⟨Q,hQ,hQc,hQi,hQcU⟩ := exists_invariant_positive_compact ν U hUc hiν
  obtain ⟨I,b,χ,hb⟩ := unitary_joint_basis U Q hQ hQc hQi hQcU
  have hbne (i : I) : b i ≠ 0 := b.orthonormal.ne_zero i
  let γ (i : I) := eigenCharacter U (hbne i) (χ i) (hb i)
  refine ⟨I,hilbertBasis_countable b,b,γ,?_,?_⟩
  · intro i
    exact continuous_eigenCharacter U hUc (hbne i) (χ i) (hb i)
  · intro i g
    exact hb i g

end StrongUnitary

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Tensors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory
open scoped ENNReal
variable {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure Ω} {a a' : Ω → A} {b : Ω → B}

lemma lpMeas_comap_congr (he : a =ᵐ[μ] a') :
    lpMeas ℂ ℂ (MeasurableSpace.comap a inferInstance) 2 μ =
      lpMeas ℂ ℂ (MeasurableSpace.comap a' inferInstance) 2 μ := by
  suffices h : ∀ (a a' : Ω → A), a =ᵐ[μ] a' →
      lpMeas ℂ ℂ (MeasurableSpace.comap a inferInstance) 2 μ ≤
        lpMeas ℂ ℂ (MeasurableSpace.comap a' inferInstance) 2 μ from
    le_antisymm (h a a' he) (h a' a he.symm)
  intro a a' hae f hf
  have hm := mem_lpMeas_iff_aestronglyMeasurable.mp hf
  obtain ⟨g,hg,hgcomp⟩ := hm.stronglyMeasurable_mk.exists_eq_measurable_comp
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  have hstrong : StronglyMeasurable[MeasurableSpace.comap a' inferInstance] (g ∘ a') :=
    hg.comp_measurable (Measurable.of_comap_le le_rfl)
  apply hstrong.aestronglyMeasurable.congr
  filter_upwards [hm.ae_eq_mk,hae] with ω hfω haω
  exact (congrArg g haω).symm.trans ((congrFun hgcomp ω).symm.trans hfω.symm)

end

section
open MeasureTheory
lemma comap_eq_of_measurable_leftInverse {X Y Z : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] (a : X → Y)
    (f : Y → Z) (g : Z → Y) (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) :
    MeasurableSpace.comap (f ∘ a) inferInstance = MeasurableSpace.comap a inferInstance := by
  apply le_antisymm
  · rw [←MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hf.comap_le
  · have he : a = g ∘ (f ∘ a) := funext fun x => (hgf (a x)).symm
    conv_lhs => rw [he,←MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hg.comap_le
namespace StrongUnitary
variable {X H₁ H₂ H₃ H₄ : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H₁] [NormedSpace ℂ H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [NormedSpace ℂ H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [NormedSpace ℂ H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [NormedSpace ℂ H₄] [SecondCountableTopology H₄]

omit [SecondCountableTopology H₁] in
lemma comap_normalizeA (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂)
    (a : X → H₂ ≃ₗᵢ[ℂ] H₁) :
    MeasurableSpace.comap (normalizeA a₀ d₀ ∘ a) inferInstance =
      MeasurableSpace.comap a inferInstance := by
  let g (u : H₄ ≃ₗᵢ[ℂ] H₄) := d₀.symm.trans (u.trans (d₀.trans a₀))
  have hg : Continuous g := by
    apply continuous_iff.mpr
    intro v
    exact (d₀.trans a₀).continuous.comp (continuous_apply (d₀.symm v))
  apply comap_eq_of_measurable_leftInverse a _ g (continuous_normalizeA a₀ d₀).measurable hg.measurable
  intro u
  ext v
  simp [g,normalizeA]

omit [SecondCountableTopology H₃] in
lemma comap_normalizeB (b₀ : H₄ ≃ₗᵢ[ℂ] H₃) (b : X → H₄ ≃ₗᵢ[ℂ] H₃) :
    MeasurableSpace.comap (normalizeB b₀ ∘ b) inferInstance =
      MeasurableSpace.comap b inferInstance := by
  let g (u : H₄ ≃ₗᵢ[ℂ] H₄) := u.trans b₀
  have hg : Continuous g := by
    apply continuous_iff.mpr
    intro v
    exact b₀.continuous.comp (continuous_apply v)
  apply comap_eq_of_measurable_leftInverse b _ g (continuous_normalizeB b₀).measurable hg.measurable
  intro u
  ext v
  simp [g,normalizeB]

end StrongUnitary
end

namespace StrongUnitary

open MeasureTheory

section MeasurableEigenvalues
variable {H I X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [SecondCountableTopology H] [MeasurableSpace X]

lemma measurable_of_eigenvalues (b : HilbertBasis I ℂ H) (U : X → H ≃ₗᵢ[ℂ] H)
    (χ : I → X → ℂ) (hχ : ∀ i, Measurable (χ i))
    (he : ∀ i x, U x (b i) = χ i x • b i) : Measurable U := by
  borelize H
  let : Countable I := hilbertBasis_countable b
  apply measurable_iff.mpr
  intro v
  have hes (x : X) : (∑' i, (b.repr v i * χ i x) • b i) = U x v := by
    have hs := (U x : H →L[ℂ] H).hasSum (b.hasSum_repr v)
    change HasSum (fun i => U x (b.repr v i • b i)) (U x v) at hs
    simpa only [map_smul, he, smul_smul] using hs.tsum_eq
  have hm : Measurable (fun x => ∑' i, (b.repr v i * χ i x) • b i) :=
    Measurable.tsum (fun i => (measurable_const.mul (hχ i)).smul measurable_const)
  simpa only [hes] using hm.stronglyMeasurable

end MeasurableEigenvalues


section
variable {H I X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [SecondCountableTopology H]

attribute [local instance] OAI.Rokhlin.StrongUnitary.instMeasurableSpaceCircle_solutions
lemma measurable_iff_eigenCoords [MeasurableSpace X]
    (b : HilbertBasis I ℂ H) (U : X → H ≃ₗᵢ[ℂ] H) (γ : X → I → Circle)
    (he : ∀ i x, U x (b i) = (γ x i : ℂ) • b i) :
    Measurable U ↔ Measurable γ := by
  borelize H
  constructor
  · intro hU
    apply Measurable.of_eval
    intro i
    apply Measurable.subtype_mk
    have hm : Measurable (fun x => inner ℂ (b i) (U x (b i))) :=
      (measurable_const (a := b i)).inner (𝕜 := ℂ) ((continuous_apply (b i)).measurable.comp hU)
    have heq (x : X) : (γ x i : ℂ) = inner ℂ (b i) (U x (b i)) := by
      rw [he, inner_smul_right]
      simp [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    exact heq x
  · intro hγ
    apply measurable_of_eigenvalues b U (fun i x => (γ x i : ℂ)) _ he
    intro i
    exact measurable_subtype_coe.comp ((measurable_pi_apply i).comp hγ)

lemma comap_eigenCoords (b : HilbertBasis I ℂ H)
    (U : X → H ≃ₗᵢ[ℂ] H) (γ : X → I → Circle)
    (he : ∀ i x, U x (b i) = (γ x i : ℂ) • b i) :
    MeasurableSpace.comap U inferInstance = MeasurableSpace.comap γ inferInstance := by
  apply le_antisymm
  · let : MeasurableSpace X := MeasurableSpace.comap γ inferInstance
    have hm : Measurable γ := Measurable.of_comap_le le_rfl
    exact ((measurable_iff_eigenCoords b U γ he).mpr hm).comap_le
  · let : MeasurableSpace X := MeasurableSpace.comap U inferInstance
    have hm : Measurable U := Measurable.of_comap_le le_rfl
    exact ((measurable_iff_eigenCoords b U γ he).mp hm).comap_le
end

variable {H J X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [SecondCountableTopology H]
attribute [local instance] OAI.Rokhlin.StrongUnitary.instMeasurableSpaceCircle_solutions_1
local instance instBorelSpaceCircle_solutions_1 : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))

omit [CompleteSpace H] in
lemma measurable_subgroupVersion (S : Subgroup (H ≃ₗᵢ[ℂ] H))
    (hS : IsClosed (S : Set (H ≃ₗᵢ[ℂ] H))) : Measurable (subgroupVersion S) := by
  classical
  exact Measurable.dite measurable_id measurable_const hS.measurableSet

omit [CompleteSpace H] [SecondCountableTopology H] in
lemma subgroupVersion_coe (S : Subgroup (H ≃ₗᵢ[ℂ] H)) {g : H ≃ₗᵢ[ℂ] H} (hg : g ∈ S) :
    (subgroupVersion S g : H ≃ₗᵢ[ℂ] H) = g := by simp [subgroupVersion,hg]

omit [CompleteSpace H] in
lemma measurable_spectralCoords (S : Subgroup (H ≃ₗᵢ[ℂ] H))
    (hS : IsClosed (S : Set (H ≃ₗᵢ[ℂ] H))) (γ : J → S →* Circle)
    (hγ : ∀ j, Continuous (γ j)) : Measurable (spectralCoords S γ) :=
  Measurable.of_eval fun j => (hγ j).measurable.comp (measurable_subgroupVersion S hS)

omit [CompleteSpace H] [SecondCountableTopology H] in
lemma spectralCoords_mul_inv (S : Subgroup (H ≃ₗᵢ[ℂ] H)) (γ : J → S →* Circle)
    {g h : H ≃ₗᵢ[ℂ] H} (hg : g ∈ S) (hh : h ∈ S) :
    spectralCoords S γ (g*h⁻¹) = spectralCoords S γ g * (spectralCoords S γ h)⁻¹ := by
  have hs : subgroupVersion S (g*h⁻¹) = subgroupVersion S g * (subgroupVersion S h)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul,Subgroup.coe_inv,subgroupVersion_coe S hg,
      subgroupVersion_coe S hh,subgroupVersion_coe S (S.mul_mem hg (S.inv_mem hh))]
  funext j
  simp only [spectralCoords,hs,map_mul,map_inv,Pi.mul_apply,Pi.inv_apply]

lemma lpMeas_spectralCoords [MeasurableSpace X] (μ : Measure X)
    (S : Subgroup (H ≃ₗᵢ[ℂ] H)) (b : HilbertBasis J ℂ H) (γ : J → S →* Circle)
    (heig : ∀ j (g : S), (g : H ≃ₗᵢ[ℂ] H) (b j) = (γ j g : ℂ) • b j)
    (U : X → H ≃ₗᵢ[ℂ] H) (hU : ∀ᵐ x ∂μ, U x ∈ S) :
    lpMeas ℂ ℂ (MeasurableSpace.comap U inferInstance) 2 μ =
      lpMeas ℂ ℂ (MeasurableSpace.comap (spectralCoords S γ ∘ U) inferInstance) 2 μ := by
  let V (x : X) : H ≃ₗᵢ[ℂ] H := subgroupVersion S (U x)
  have huv : U =ᵐ[μ] V := hU.mono fun x hx => (subgroupVersion_coe S hx).symm
  rw [lpMeas_comap_congr huv]
  rw [comap_eigenCoords b V (spectralCoords S γ ∘ U) (fun j x => heig j (subgroupVersion S (U x)))]
  rfl


end StrongUnitary

section
open MeasureTheory ProbabilityTheory

lemma exists_const_of_ae_prod_eq {X Y V : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : X → V} {g : Y → V}
    (h : ∀ᵐ p ∂μ.prod ν, f p.1 = g p.2) :
    ∃ v, f =ᵐ[μ] (fun _ => v) ∧ g =ᵐ[ν] (fun _ => v) := by
  have hh : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, f x = g y := Measure.ae_ae_of_ae_prod h
  obtain ⟨x₀,hx₀⟩ := hh.exists
  refine ⟨f x₀, ?_, hx₀.mono (fun _ hy => hy.symm)⟩
  filter_upwards [hh] with x hx
  obtain ⟨y,hy,h0y⟩ := (hx.and hx₀).exists
  exact hy.trans h0y.symm

lemma measurable_conull_subset {Z : Type*} [MeasurableSpace Z] {σ : Measure Z}
    {p : Z → Prop} (h : ∀ᵐ z ∂σ, p z) :
    ∃ s : Set Z, MeasurableSet s ∧ (∀ᵐ z ∂σ, z ∈ s) ∧ ∀ z ∈ s, p z := by
  obtain ⟨t,ht,htm,ht0⟩ := exists_measurable_superset_of_null (ae_iff.mp h)
  refine ⟨tᶜ, htm.compl, ?_, ?_⟩
  · apply mem_ae_iff.mpr
    change σ (tᶜ)ᶜ = 0
    simpa only [compl_compl] using ht0
  · intro z hz
    by_contra hp
    exact hz (ht hp)

lemma exists_measurable_common_unitary {Z X Y H : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SecondCountableTopology H] [CompleteSpace H]
    {σ : Measure Z} (κ : Kernel Z X) (ξ : Kernel Z Y)
    [IsMarkovKernel κ] [IsMarkovKernel ξ]
    (f : X → H ≃ₗᵢ[ℂ] H) (g : Y → H ≃ₗᵢ[ℂ] H)
    (hf : Measurable f)
    (heq : ∀ᵐ z ∂σ, ∀ᵐ p ∂(κ z).prod (ξ z), f p.1 = g p.2) :
    ∃ U : Z → H ≃ₗᵢ[ℂ] H, Measurable U ∧
      ∀ᵐ z ∂σ, f =ᵐ[κ z] (fun _ => U z) ∧ g =ᵐ[ξ z] (fun _ => U z) := by
  classical
  have he : ∀ᵐ z ∂σ, ∃ U, f =ᵐ[κ z] (fun _ => U) ∧ g =ᵐ[ξ z] (fun _ => U) :=
    heq.mono fun _ hz => exists_const_of_ae_prod_eq hz
  obtain ⟨s,hsm,hs,hsprop⟩ := measurable_conull_subset he
  choose U₀ hU₀ using fun z : s => hsprop z z.property
  let U : Z → H ≃ₗᵢ[ℂ] H := fun z => if hz : z ∈ s then U₀ ⟨z,hz⟩ else 1
  refine ⟨U, ?_, ?_⟩
  · apply StrongUnitary.measurable_iff.mpr
    intro v
    have hev : (fun z => U z v) = s.piecewise (fun z => ∫ x, f x v ∂κ z) (fun _ => v) := by
      funext z
      by_cases hz : z ∈ s
      · simp only [U, dite_eq_left hz, Set.piecewise_eq_of_mem s _ _ hz]
        calc
          U₀ ⟨z,hz⟩ v = ∫ _x, U₀ ⟨z,hz⟩ v ∂κ z := by simp
          _ = ∫ x, f x v ∂κ z := integral_congr_ae ((hU₀ ⟨z,hz⟩).1.fun_comp (fun A => A v)).symm
      · simp [U, hz]
    rw [hev]
    exact ((StrongUnitary.measurable_iff.mp hf v).integral_kernel).piecewise hsm stronglyMeasurable_const
  · filter_upwards [hs] with z hz
    simpa only [U,dite_eq_left hz] using hU₀ ⟨z,hz⟩

namespace StrongUnitary

lemma rectangle_ratio_eq {G : Type*} [Group G] {a b c d : G}
    (hbd : Commute b d) (h : a * d = c * b) : a * b⁻¹ = c * d⁻¹ := by
  apply mul_inv_eq_iff_eq_mul.mpr
  calc
    a = c * b * d⁻¹ := by rw [←h, mul_assoc, mul_inv_cancel, mul_one]
    _ = (c * d⁻¹) * b := by rw [mul_assoc, hbd.inv_right.eq, ←mul_assoc]

variable {Z H : Type*} [MeasurableSpace Z]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] [SecondCountableTopology H]

lemma measurable_corner_ratio (σ : Measure Z)
    (κ ξ : Kernel Z ((H ≃ₗᵢ[ℂ] H) × (H ≃ₗᵢ[ℂ] H)))
    [IsMarkovKernel κ] [IsMarkovKernel ξ]
    (ρ τ : ProbabilityMeasure (H ≃ₗᵢ[ℂ] H)) (G : Subgroup (H ≃ₗᵢ[ℂ] H))
    (hρ : (ρ : Measure _).support = (G : Set (H ≃ₗᵢ[ℂ] H))) (hτ : (τ : Measure _).support = (G : Set (H ≃ₗᵢ[ℂ] H)))
    (hcomm : ∀ u ∈ G, ∀ v ∈ G, u * v = v * u)
    (hm : ∀ᵐ z ∂σ, (κ z).map Prod.fst = ρ ∧ (κ z).map Prod.snd = ρ ∧
      (ξ z).map Prod.fst = τ ∧ (ξ z).map Prod.snd = τ)
    (hr : ∀ᵐ z ∂σ, ∀ᵐ p ∂(κ z).prod (ξ z), p.1.1*p.2.2 = p.2.1*p.1.2) :
    ∃ U : Z → H ≃ₗᵢ[ℂ] H, Measurable U ∧ ∀ᵐ z ∂σ, U z ∈ G ∧
      (∀ᵐ p ∂κ z, p.1 * p.2⁻¹ = U z) ∧
      (∀ᵐ p ∂ξ z, p.1 * p.2⁻¹ = U z) := by
  have hρm : ∀ᵐ u ∂(ρ : Measure _), u ∈ G := by
    change (G : Set (H ≃ₗᵢ[ℂ] H)) ∈ ae (ρ : Measure _)
    rw [←hρ]
    exact Measure.support_mem_ae
  have hτm : ∀ᵐ u ∂(τ : Measure _), u ∈ G := by
    change (G : Set (H ≃ₗᵢ[ℂ] H)) ∈ ae (τ : Measure _)
    rw [←hτ]
    exact Measure.support_mem_ae
  have hpairs : ∀ᵐ z ∂σ, (∀ᵐ p ∂κ z, p.1 ∈ G ∧ p.2 ∈ G) ∧
      (∀ᵐ p ∂ξ z, p.1 ∈ G ∧ p.2 ∈ G) := by
    filter_upwards [hm] with z hz
    constructor
    · have ha := ae_of_ae_map measurable_fst.aemeasurable (hz.1 ▸ hρm)
      have hb := ae_of_ae_map measurable_snd.aemeasurable (hz.2.1 ▸ hρm)
      exact ha.and hb
    · have hc := ae_of_ae_map measurable_fst.aemeasurable (hz.2.2.1 ▸ hτm)
      have hd := ae_of_ae_map measurable_snd.aemeasurable (hz.2.2.2 ▸ hτm)
      exact hc.and hd
  have he : ∀ᵐ z ∂σ, ∀ᵐ p ∂(κ z).prod (ξ z), p.1.1 * p.1.2⁻¹ = p.2.1 * p.2.2⁻¹ := by
    filter_upwards [hpairs,hr] with z hz hzr
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hz.1,
      Measure.quasiMeasurePreserving_snd.ae hz.2,hzr] with p hp hq hrect
    exact rectangle_ratio_eq (hcomm _ hp.2 _ hq.2) hrect
  obtain ⟨U,hU,heU⟩ := exists_measurable_common_unitary κ ξ
    (fun p => p.1 * p.2⁻¹) (fun p => p.1 * p.2⁻¹)
    (measurable_fst.mul measurable_snd.inv) he
  refine ⟨U,hU,?_⟩
  filter_upwards [hpairs,heU] with z hz hzu
  obtain ⟨p,hp,heq⟩ := (hz.1.and hzu.1).exists
  change p.1 * p.2⁻¹ = U z at heq
  exact ⟨heq ▸ G.mul_mem hp.1 (G.inv_mem hp.2), hzu⟩

end StrongUnitary

namespace ConditionalFibres
lemma ae_of_ae_kernel {Ω Z V : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [MeasurableSpace V] {μ : Measure Ω} {z : Ω → Z} {v : Ω → V}
    {κ : Kernel Z V} (h : HasCondDistrib v z κ μ) {p : Z × V → Prop}
    (hp : MeasurableSet {q | p q}) (hv : ∀ᵐ a ∂μ.map z, ∀ᵐ b ∂κ a, p (a,b)) :
    ∀ᵐ ω ∂μ, p (z ω,v ω) := by
  have hh := Measure.ae_compProd_of_ae_ae hp hv
  rw [←h.map_eq] at hh
  exact ae_of_ae_map h.aemeasurable hh
end ConditionalFibres
namespace StrongUnitary
attribute [local instance] OAI.Rokhlin.StrongUnitary.instMeasurableSpaceCircle_solutions_2
local instance instBorelSpaceCircle_solutions_2 : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))
universe u
variable {Ω Z X Y C D : Type*} {H : Type u}
  [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [SecondCountableTopology H]
  {μ : Measure Ω} {ν : Measure X} {η : Measure Y} {ξC : Measure C} {ξD : Measure D}
  {z : Ω → Z} {x : Ω → X} {y : Ω → Y} {c : Ω → C} {d : Ω → D}

lemma spectral_corner
    (G : Subgroup (H ≃ₗᵢ[ℂ] H)) (hG : IsClosed (G : Set (H ≃ₗᵢ[ℂ] H)))
    (ρ τ : ProbabilityMeasure (H ≃ₗᵢ[ℂ] H))
    (hρ : (ρ : Measure _).support = (G : Set (H ≃ₗᵢ[ℂ] H)))
    (hτ : (τ : Measure _).support = (G : Set (H ≃ₗᵢ[ℂ] H)))
    (hcomm : ∀ g ∈ G, ∀ h ∈ G, g*h = h*g)
    (hinv : ∀ g ∈ G, (ρ : Measure _).map (g * ·) = ρ)
    (a : X → H ≃ₗᵢ[ℂ] H) (b : Y → H ≃ₗᵢ[ℂ] H)
    (f : C → H ≃ₗᵢ[ℂ] H) (g : D → H ≃ₗᵢ[ℂ] H)
    (ha : MeasurePreserving a ν ρ) (hb : MeasurePreserving b η ρ)
    (hf : MeasurePreserving f ξC τ) (hg : MeasurePreserving g ξD τ)
    (κ ξ : Kernel Z ((H ≃ₗᵢ[ℂ] H) × (H ≃ₗᵢ[ℂ] H)))
    [IsMarkovKernel κ] [IsMarkovKernel ξ]
    (hκ : HasCondDistrib (fun ω => (a (x ω),b (y ω))) z κ μ)
    (hξ : HasCondDistrib (fun ω => (f (c ω),g (d ω))) z ξ μ)
    (hm : ∀ᵐ t ∂μ.map z, (κ t).map Prod.fst = ρ ∧ (κ t).map Prod.snd = ρ ∧
      (ξ t).map Prod.fst = τ ∧ (ξ t).map Prod.snd = τ)
    (hr : ∀ᵐ t ∂μ.map z, ∀ᵐ p ∂(κ t).prod (ξ t), p.1.1*p.2.2 = p.2.1*p.1.2) :
    ∃ (J : Type u) (_ : Countable J)
      (A : X → J → Circle) (B : Y → J → Circle)
      (F : C → J → Circle) (Q : D → J → Circle) (K : Z → J → Circle),
      Measurable A ∧ Measurable B ∧ Measurable F ∧ Measurable Q ∧ Measurable K ∧
      lpMeas ℂ ℂ (MeasurableSpace.comap a inferInstance) 2 ν =
        lpMeas ℂ ℂ (MeasurableSpace.comap A inferInstance) 2 ν ∧
      lpMeas ℂ ℂ (MeasurableSpace.comap b inferInstance) 2 η =
        lpMeas ℂ ℂ (MeasurableSpace.comap B inferInstance) 2 η ∧
      (∀ᵐ ω ∂μ, K (z ω) = A (x ω) * (B (y ω))⁻¹) ∧
      (∀ᵐ ω ∂μ, K (z ω) = F (c ω) * (Q (d ω))⁻¹) := by
  obtain ⟨U,hU,hUr⟩ := measurable_corner_ratio (μ.map z) κ ξ ρ τ G hρ hτ hcomm hm hr
  obtain ⟨J,hJ,e,γ,hγ,he⟩ := polar_spectral G hG ρ hρ hcomm hinv
  let sc := spectralCoords G γ
  have hsc : Measurable sc := measurable_spectralCoords G hG γ hγ
  have hgρ : ∀ᵐ v ∂(ρ : Measure _), v ∈ G := by
    change (G : Set (H ≃ₗᵢ[ℂ] H)) ∈ ae (ρ : Measure _)
    rw [←hρ]
    exact Measure.support_mem_ae
  have hgτ : ∀ᵐ v ∂(τ : Measure _), v ∈ G := by
    change (G : Set (H ≃ₗᵢ[ℂ] H)) ∈ ae (τ : Measure _)
    rw [←hτ]
    exact Measure.support_mem_ae
  have hmκ : ∀ᵐ t ∂μ.map z, ∀ᵐ p ∂κ t, p.1 ∈ G ∧ p.2 ∈ G := by
    filter_upwards [hm] with t ht
    exact (ae_of_ae_map measurable_fst.aemeasurable (ht.1 ▸ hgρ)).and
      (ae_of_ae_map measurable_snd.aemeasurable (ht.2.1 ▸ hgρ))
  have hmξ : ∀ᵐ t ∂μ.map z, ∀ᵐ p ∂ξ t, p.1 ∈ G ∧ p.2 ∈ G := by
    filter_upwards [hm] with t ht
    exact (ae_of_ae_map measurable_fst.aemeasurable (ht.2.2.1 ▸ hgτ)).and
      (ae_of_ae_map measurable_snd.aemeasurable (ht.2.2.2 ▸ hgτ))
  refine ⟨J,hJ,sc ∘ a,sc ∘ b,sc ∘ f,sc ∘ g,sc ∘ U,
    hsc.comp ha.measurable,hsc.comp hb.measurable,hsc.comp hf.measurable,
    hsc.comp hg.measurable,hsc.comp hU,?_,?_,?_,?_⟩
  · exact lpMeas_spectralCoords ν G e γ he a (ha.quasiMeasurePreserving.ae hgρ)
  · exact lpMeas_spectralCoords η G e γ he b (hb.quasiMeasurePreserving.ae hgρ)
  · have hh : ∀ᵐ t ∂μ.map z, ∀ᵐ p ∂κ t, sc (U t) = sc p.1 * (sc p.2)⁻¹ := by
      filter_upwards [hUr,hmκ] with t ht hm
      filter_upwards [ht.2.1,hm] with p hp hmem
      rw [←hp]
      exact spectralCoords_mul_inv G γ hmem.1 hmem.2
    exact ConditionalFibres.ae_of_ae_kernel hκ
      (measurableSet_eq_fun ((hsc.comp hU).comp measurable_fst)
        ((hsc.comp measurable_snd.fst).mul (hsc.comp measurable_snd.snd).inv)) hh
  · have hh : ∀ᵐ t ∂μ.map z, ∀ᵐ p ∂ξ t, sc (U t) = sc p.1 * (sc p.2)⁻¹ := by
      filter_upwards [hUr,hmξ] with t ht hm
      filter_upwards [ht.2.2,hm] with p hp hmem
      rw [←hp]
      exact spectralCoords_mul_inv G γ hmem.1 hmem.2
    exact ConditionalFibres.ae_of_ae_kernel hξ
      (measurableSet_eq_fun ((hsc.comp hU).comp measurable_fst)
        ((hsc.comp measurable_snd.fst).mul (hsc.comp measurable_snd.snd).inv)) hh
end StrongUnitary
end

section
open MeasureTheory ProbabilityTheory ContinuousLinearMap
universe u
variable {Ω Z X Y C D H₁ H₂ H₃ : Type*} {H₄ : Type u}
  [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄] [SecondCountableTopology H₄]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {μX : Measure X} {μY : Measure Y} {μC : Measure C} {μD : Measure D}
  [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
  [IsProbabilityMeasure μC] [IsProbabilityMeasure μD]
  {x : Ω → X} {y : Ω → Y} {c : Ω → C} {d : Ω → D}
  {F : X → H₂ →L[ℂ] H₁} {G : Y → H₄ →L[ℂ] H₃}
  {K : C → H₃ →L[ℂ] H₁} {N : D → H₄ →L[ℂ] H₂}

attribute [local instance] OAI.Rokhlin.instMeasurableSpaceCircle_solutions
omit [SecondCountableTopology H₁] [IsProbabilityMeasure μY] [IsProbabilityMeasure μD] in

lemma MeasurablePolarRectangle.torus_coordinates_oai
    (R : MeasurablePolarRectangle μ μX μY μC μD F G K N x y c d)
    (hR : R.HasHaarNormalization)
    {z : Ω → Z}
    (κ : Kernel Z (X × Y)) (ξ : Kernel Z (C × D)) [IsMarkovKernel κ] [IsMarkovKernel ξ]
    (hκ : HasCondDistrib (fun ω => (x ω,y ω)) z κ μ)
    (hξ : HasCondDistrib (fun ω => (c ω,d ω)) z ξ μ)
    (hpair : HasCondDistrib (fun ω => ((x ω,y ω),(c ω,d ω))) z (κ ×ₖ ξ) μ)
    (hκm : ∀ᵐ v ∂μ.map z, (κ v).map Prod.fst = μX ∧ (κ v).map Prod.snd = μY)
    (hξm : ∀ᵐ v ∂μ.map z, (ξ v).map Prod.fst = μC ∧ (ξ v).map Prod.snd = μD) :
    ∃ (J : Type u) (_ : Countable J)
      (A : X → J → Circle) (B : Y → J → Circle)
      (P : C → J → Circle) (Q : D → J → Circle) (H : Z → J → Circle),
      Measurable A ∧ Measurable B ∧ Measurable P ∧ Measurable Q ∧ Measurable H ∧
      lpMeas ℂ ℂ (MeasurableSpace.comap R.a.unitary inferInstance) 2 μX =
        lpMeas ℂ ℂ (MeasurableSpace.comap A inferInstance) 2 μX ∧
      lpMeas ℂ ℂ (MeasurableSpace.comap R.b.unitary inferInstance) 2 μY =
        lpMeas ℂ ℂ (MeasurableSpace.comap B inferInstance) 2 μY ∧
      (∀ᵐ ω ∂μ, H (z ω) = A (x ω) * (B (y ω))⁻¹) ∧
      (∀ᵐ ω ∂μ, H (z ω) = P (c ω) * (Q (d ω))⁻¹) := by
  obtain ⟨a₀,b₀,d₀,S,hS,hAB,hCD,hρ,hτ,hcomm,hinv⟩ := hR
  let na := StrongUnitary.normalizeA a₀ d₀
  let nb := StrongUnitary.normalizeB b₀
  let nc := StrongUnitary.normalizeC a₀ b₀ d₀
  let nd := StrongUnitary.normalizeD d₀
  have hna : Measurable na := (StrongUnitary.continuous_normalizeA a₀ d₀).measurable
  have hnb : Measurable nb := (StrongUnitary.continuous_normalizeB b₀).measurable
  have hnc : Measurable nc := (StrongUnitary.continuous_normalizeC a₀ b₀ d₀).measurable
  have hnd : Measurable nd := (StrongUnitary.continuous_normalizeD d₀).measurable
  let aa := na ∘ R.a.unitary
  let bb := nb ∘ R.b.unitary
  let cc := nc ∘ R.p.unitary
  let dd := nd ∘ R.q.unitary
  have ha : Measurable aa := hna.comp R.a.measurable
  have hb : Measurable bb := hnb.comp R.b.measurable
  have hc : Measurable cc := hnc.comp R.p.measurable
  have hd : Measurable dd := hnd.comp R.q.measurable
  let ρ : ProbabilityMeasure (H₄ ≃ₗᵢ[ℂ] H₄) :=
    ⟨μX.map aa,(fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) ha.aemeasurable⟩
  let τ : ProbabilityMeasure (H₄ ≃ₗᵢ[ℂ] H₄) :=
    ⟨μC.map cc,(fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) hc.aemeasurable⟩
  have hρeq : (μX.map R.a.unitary).map na = (ρ : Measure _) :=
    Measure.map_map hna R.a.measurable
  have hτeq : (μC.map R.p.unitary).map nc = (τ : Measure _) :=
    Measure.map_map hnc R.p.measurable
  change (μX.map R.a.unitary).map na = (μY.map R.b.unitary).map nb at hAB
  change (μC.map R.p.unitary).map nc = (μD.map R.q.unitary).map nd at hCD
  have hab : μY.map bb = (ρ : Measure _) :=
    (Measure.map_map hnb R.b.measurable).symm.trans (hAB.symm.trans hρeq)
  have hcd : μD.map dd = (τ : Measure _) :=
    (Measure.map_map hnd R.q.measurable).symm.trans (hCD.symm.trans hτeq)
  let α := κ.map (Prod.map aa bb)
  let β := ξ.map (Prod.map cc dd)
  let : IsMarkovKernel α := Kernel.IsMarkovKernel.map κ (ha.prodMap hb)
  let : IsMarkovKernel β := Kernel.IsMarkovKernel.map ξ (hc.prodMap hd)
  have hα : HasCondDistrib (fun ω => (aa (x ω),bb (y ω))) z α μ := hκ.comp_left (ha.prodMap hb)
  have hβ : HasCondDistrib (fun ω => (cc (c ω),dd (d ω))) z β μ := hξ.comp_left (hc.prodMap hd)
  have hm : ∀ᵐ v ∂μ.map z, (α v).map Prod.fst = ρ ∧ (α v).map Prod.snd = ρ ∧
      (β v).map Prod.fst = τ ∧ (β v).map Prod.snd = τ := by
    filter_upwards [hκm,hξm] with v hv hw
    dsimp only [α,β]
    rw [kernel_map_pair_fst _ _ ha hb,kernel_map_pair_snd _ _ ha hb,
      kernel_map_pair_fst _ _ hc hd,kernel_map_pair_snd _ _ hc hd,hv.1,hv.2,hw.1,hw.2,hab,hcd]
    exact ⟨rfl,rfl,rfl,rfl⟩
  have hr : ∀ᵐ v ∂μ.map z, ∀ᵐ w ∂(α v).prod (β v), w.1.1*w.2.2 = w.2.1*w.1.2 := by
    have hh := hpair.comp_left ((ha.prodMap hb).prodMap (hc.prodMap hd))
    have he : (κ ×ₖ ξ).map (Prod.map (Prod.map aa bb) (Prod.map cc dd)) = α ×ₖ β :=
      (Kernel.map_prod_map κ ξ (ha.prodMap hb) (hc.prodMap hd)).symm
    rw [he] at hh
    have hr := ConditionalFibres.ae_kernel hh
      (isClosed_eq (continuous_fst.fst.mul continuous_snd.snd)
        (continuous_snd.fst.mul continuous_fst.snd)).measurableSet
      (R.rectangle.mono (fun ω hω => StrongUnitary.normalized_rectangle a₀
        (R.a.unitary (x ω)) b₀ (R.b.unitary (y ω)) (R.p.unitary (c ω)) d₀ (R.q.unitary (d ω)) hω))
    simpa only [Kernel.prod_apply, Pi.mul_apply] using hr
  have hρs : (ρ : Measure _).support = (S : Set (H₄ ≃ₗᵢ[ℂ] H₄)) := by rw [←hρeq]; exact hρ
  have hτs : (τ : Measure _).support = (S : Set (H₄ ≃ₗᵢ[ℂ] H₄)) := by rw [←hτeq]; exact hτ
  have hρi : ∀ g ∈ S, (ρ : Measure _).map (g*·) = ρ := by rw [←hρeq]; exact hinv
  obtain ⟨J,hJ,A,B,P,Q,H,hA,hB,hP,hQ,hH,hfa,hfb,hra,hrb⟩ :=
    StrongUnitary.spectral_corner S hS ρ τ hρs hτs hcomm hρi aa bb cc dd
      ⟨ha,rfl⟩ ⟨hb,hab⟩ ⟨hc,rfl⟩ ⟨hd,hcd⟩ α β hα hβ hm hr
  refine ⟨J,hJ,A,B,P,Q,H,hA,hB,hP,hQ,hH,?_,?_,hra,hrb⟩
  · rw [←StrongUnitary.comap_normalizeA a₀ d₀ R.a.unitary]
    exact hfa
  · rw [←StrongUnitary.comap_normalizeB b₀ R.b.unitary]
    exact hfb
end


end Rokhlin

end

end OAI
end

theorem solution.{u, u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9} : type_of% @OAI.Rokhlin.MeasurablePolarRectangle.torus_coordinates_oai.{u, u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9} := @OAI.Rokhlin.MeasurablePolarRectangle.torus_coordinates_oai.{u, u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9}
