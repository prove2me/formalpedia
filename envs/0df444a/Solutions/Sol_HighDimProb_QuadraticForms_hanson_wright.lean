-- Prove2me | solution 1 for HighDimProb.QuadraticForms.hanson_wright
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-01T18:02:55.567892+00:00
-- url     : https://prove2.me/submissions/a99eb184-018e-47f5-8154-35f05507b34a

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm
import Definitions.Def_HighDimProb_QuadraticForms_FrobeniusNorm
import Definitions.Def_HighDimProb_QuadraticForms_OperatorNorm

set_option autoImplicit false



-- DecouplingConditional

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory

namespace DecouplingProof

noncomputable def selectedSigma {I Ω : Type*} [MeasurableSpace Ω]
    (Z : I → Ω → ℝ) (S : Finset I) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (i : S) => Z i ω) inferInstance

lemma selectedSigma_le {I Ω : Type*} [MeasurableSpace Ω]
    (Z : I → Ω → ℝ) (hZ : ∀ i, Measurable (Z i)) (S : Finset I) :
    selectedSigma Z S ≤ ‹MeasurableSpace Ω› :=
  (measurable_pi_lambda _ (fun (i : S) => hZ i)).comap_le

lemma selected_measurable {I Ω : Type*} [MeasurableSpace Ω]
    (Z : I → Ω → ℝ) (S : Finset I) {i : I} (hi : i ∈ S) :
    Measurable[selectedSigma Z S] (Z i) := by
  have hv : Measurable[selectedSigma Z S] (fun ω (j : S) => Z j ω) := comap_measurable _
  simpa only [Function.comp_def] using (measurable_pi_apply (⟨i, hi⟩ : S)).comp hv

lemma outside_indep {I Ω : Type*} [MeasurableSpace Ω] [DecidableEq I]
    (P : Measure Ω) (Z : I → Ω → ℝ) (hZ : ∀ i, Measurable (Z i))
    (hI : iIndepFun Z P) (S : Finset I) {i : I} (hi : i ∉ S) :
    IndepFun (Z i) (fun ω (j : S) => Z j ω) P := by
  have h := hI.indepFun_finset {i} S (by simpa using hi) hZ
  simpa only [Function.comp_def, Pi.mul_apply, id_eq] using h.comp (measurable_pi_apply ⟨i, by simp⟩) measurable_id

lemma outside_pair_indep {I Ω : Type*} [MeasurableSpace Ω] [DecidableEq I]
    (P : Measure Ω) (Z : I → Ω → ℝ) (hZ : ∀ i, Measurable (Z i))
    (hI : iIndepFun Z P) (S : Finset I) {i j : I} (hi : i ∉ S) (hj : j ∉ S) :
    IndepFun (fun ω => Z i ω * Z j ω) (fun ω (k : S) => Z k ω) P := by
  have h := hI.indepFun_finset {i, j} S (by simpa [Finset.disjoint_left] using
    (show ∀ k ∈ ({i, j} : Finset I), k ∉ S by simp_all)) hZ
  simpa only [Function.comp_def, Pi.mul_apply, id_eq] using h.comp
    ((measurable_pi_apply ⟨i, by simp⟩).mul (measurable_pi_apply ⟨j, by simp⟩))
    measurable_id

lemma outside_condExp_zero {I Ω : Type*} [MeasurableSpace Ω] [DecidableEq I]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : I → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i)) (hI : iIndepFun Z P)
    (hmean : ∀ i, ∫ ω, Z i ω ∂P = 0) (S : Finset I) {i : I} (hi : i ∉ S) :
    P[Z i | selectedSigma Z S] =ᵐ[P] (fun _ => 0) := by
  have h := condExp_indep_eq (hZ i).comap_le (selectedSigma_le Z hZ S)
    (comap_measurable (Z i)).stronglyMeasurable (outside_indep P Z hZ hI S hi)
  simpa [hmean i] using h

lemma pair_condExp {I Ω : Type*} [MeasurableSpace Ω] [DecidableEq I]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : I → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i)) (hI : iIndepFun Z P)
    (hInt : ∀ i, Integrable (Z i) P) (hmean : ∀ i, ∫ ω, Z i ω ∂P = 0)
    (S : Finset I) {i j : I} (hij : i ≠ j) :
    P[Z i * Z j | selectedSigma Z S] =ᵐ[P]
      (fun ω => if i ∈ S ∧ j ∈ S then Z i ω * Z j ω else 0) := by
  have hprod := (hI.indepFun hij).integrable_mul (hInt i) (hInt j)
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · apply Filter.Eventually.of_forall
      intro ω
      simpa [hi, hj] using congr_fun
        (condExp_of_stronglyMeasurable (selectedSigma_le Z hZ S)
          ((selected_measurable Z S hi).mul (selected_measurable Z S hj)).stronglyMeasurable hprod) ω
    · have hp := condExp_mul_of_stronglyMeasurable_left
        (selected_measurable Z S hi).stronglyMeasurable hprod (hInt j)
      have hz := outside_condExp_zero P Z hZ hI hmean S hj
      filter_upwards [hp, hz] with ω hω hzω
      simpa [hi, hj, hzω] using hω
  · by_cases hj : j ∈ S
    · have hp := condExp_mul_of_stronglyMeasurable_right
        (selected_measurable Z S hj).stronglyMeasurable hprod (hInt i)
      have hz := outside_condExp_zero P Z hZ hI hmean S hi
      filter_upwards [hp, hz] with ω hω hzω
      simpa [hi, hj, hzω] using hω
    · have h := condExp_indep_eq ((hZ i).mul (hZ j)).comap_le (selectedSigma_le Z hZ S)
        (comap_measurable (Z i * Z j)).stronglyMeasurable (outside_pair_indep P Z hZ hI S hi hj)
      have hzero : ∫ ω, (Z i * Z j) ω ∂P = 0 := by
        rw [(hI.indepFun hij).integral_mul_eq_mul_integral (hInt i).aestronglyMeasurable (hInt j).aestronglyMeasurable, hmean i, zero_mul]
      rw [hzero] at h
      simpa [hi, hj] using h

lemma convex_condExp_bound {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) (Y U : Ω → ℝ) (hY : Integrable Y P)
    (hU : @Measurable Ω ℝ mΩ _ U) (hEq : P[Y | m] =ᵐ[P] U)
    (F : ℝ → ℝ) (hF : ConvexOn ℝ Set.univ F) (hFY : Integrable (F ∘ Y) P) :
    Integrable (F ∘ U) P ∧ ∫ ω, F (U ω) ∂P ≤ ∫ ω, F (Y ω) ∂P := by
  have hFc : Continuous F := continuousOn_univ.mp (hF.continuousOn isOpen_univ)
  have hUint : Integrable U P := integrable_condExp.congr hEq
  have hJ := hF.map_condExp_le_of_finiteDimensional (μ := P) (f := Y) hm hY hFY
  have hupper : F ∘ U ≤ᵐ[P] P[F ∘ Y | m] := by
    filter_upwards [hJ, hEq] with ω hJω heq
    simpa [Function.comp_def, heq] using hJω
  obtain ⟨a, b, hab⟩ := ConvexOn.exists_affine_le_real isClosed_univ
    (hFc.lowerSemicontinuous.lowerSemicontinuousOn Set.univ) hF
  have hint : Integrable (F ∘ U) P := integrable_of_le_of_le
    (hFc.measurable.comp hU).aestronglyMeasurable
    (Eventually.of_forall (fun ω => hab (U ω) (Set.mem_univ _))) hupper
    ((hUint.const_mul a).add (integrable_const b)) integrable_condExp
  refine ⟨hint, ?_⟩
  calc ∫ ω, F (U ω) ∂P ≤ ∫ ω, P[F ∘ Y | m] ω ∂P :=
      integral_mono_ae hint integrable_condExp hupper
    _ = ∫ ω, F (Y ω) ∂P := integral_condExp hm

end DecouplingProof


-- DecouplingMasks

open scoped BigOperators

namespace DecouplingProof

def flipMask {I : Type*} [DecidableEq I] (i : I) (τ : I → Bool) : I → Bool :=
  Function.update τ i (!(τ i))

lemma flipMask_involutive {I : Type*} [DecidableEq I] (i : I) :
    Function.Involutive (flipMask i) := by
  intro τ
  funext k
  by_cases hk : k = i
  · subst k; simp [flipMask]
  · simp [flipMask, hk]

lemma sum_mask_pair {I : Type*} [Fintype I] [DecidableEq I]
    {i j : I} (hij : i ≠ j) (c : ℝ) :
    (∑ τ : I → Bool, if τ i = true ∧ τ j = false then c else 0) =
      (Fintype.card (I → Bool) : ℝ) * c / 4 := by
  let f : Bool → Bool → ℝ := fun a b =>
    ∑ τ : I → Bool, if τ i = a ∧ τ j = b then c else 0
  have hfi (a b : Bool) : f (!a) b = f a b := by
    dsimp [f]
    exact Fintype.sum_bijective (flipMask i) (flipMask_involutive i).bijective _ _
      (fun τ => by
        simp only [flipMask, Function.update_self, Function.update_of_ne hij.symm]
        cases a <;> cases τ i <;> simp)
  have hfj (a b : Bool) : f a (!b) = f a b := by
    dsimp [f]
    exact Fintype.sum_bijective (flipMask j) (flipMask_involutive j).bijective _ _
      (fun τ => by
        simp only [flipMask, Function.update_self, Function.update_of_ne hij]
        cases b <;> cases τ j <;> simp)
  have hall : f true true + f true false + f false true + f false false =
      (Fintype.card (I → Bool) : ℝ) * c := by
    dsimp [f]
    simp only [← Finset.sum_add_distrib]
    calc
      _ = ∑ τ : I → Bool, c := by
        apply Finset.sum_congr rfl
        intro τ _
        cases τ i <;> cases τ j <;> simp
      _ = _ := by simp [nsmul_eq_mul]
  have h1 := hfi true true
  have h2 := hfi true false
  have h3 := hfj true true
  change f true false = _
  simp only [Bool.not_true] at h1 h2 h3
  linarith

def cross {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Bool)
    (x y : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, if τ i = true ∧ τ j = false then A i j * x i * y j else 0

lemma average_cross {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, A i i = 0)
    (x : Fin n → ℝ) :
    (Fintype.card (Fin n → Bool) : ℝ)⁻¹ *
      (∑ τ : Fin n → Bool, 4 * cross A τ x x) = ∑ i, ∑ j, A i j * x i * x j := by
  classical
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) ≠ 0 := by positivity
  have hs : (∑ τ : Fin n → Bool, cross A τ x x) =
      ∑ i, ∑ j, (Fintype.card (Fin n → Bool) : ℝ) * (A i j * x i * x j) / 4 := by
    simp only [cross]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j
    · subst j; simp [hA i]
    · exact sum_mask_pair hij _
  rw [← Finset.mul_sum, hs]
  simp only [div_eq_mul_inv, ← Finset.mul_sum, ← Finset.sum_mul]
  field_simp
  <;> ring

lemma convex_average_cross {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, A i i = 0) (F : ℝ → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (x : Fin n → ℝ) :
    F (∑ i, ∑ j, A i j * x i * x j) ≤
      (Fintype.card (Fin n → Bool) : ℝ)⁻¹ *
        ∑ τ : Fin n → Bool, F (4 * cross A τ x x) := by
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) ≠ 0 := by positivity
  have h := hF.map_sum_le (t := Finset.univ)
    (w := fun _ : Fin n → Bool => (Fintype.card (Fin n → Bool) : ℝ)⁻¹)
    (p := fun τ => 4 * cross A τ x x)
    (by intros; positivity) (by simp [hcard]) (by intros; trivial)
  simp only [smul_eq_mul] at h
  rw [← Finset.mul_sum, average_cross A hA x] at h
  simpa only [← Finset.mul_sum] using h

end DecouplingProof


-- DecouplingProjection

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory

namespace DecouplingProof

noncomputable def selectedIndices {n : ℕ} (τ : Fin n → Bool) : Finset (Fin n ⊕ Fin n) := by
  classical
  exact Finset.univ.filter (Sum.elim (fun i => τ i = true) (fun j => τ j = false))

@[simp] lemma selected_left {n : ℕ} (τ : Fin n → Bool) (i : Fin n) :
    Sum.inl i ∈ selectedIndices τ ↔ τ i = true := by simp [selectedIndices]

@[simp] lemma selected_right {n : ℕ} (τ : Fin n → Bool) (i : Fin n) :
    Sum.inr i ∈ selectedIndices τ ↔ τ i = false := by simp [selectedIndices]

lemma condExp_sum {I Ω : Type*} [Fintype I] [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) {m : MeasurableSpace Ω} (T U : I → Ω → ℝ)
    (hInt : ∀ i, Integrable (T i) P) (hEq : ∀ i, P[T i | m] =ᵐ[P] U i) :
    P[∑ i, T i | m] =ᵐ[P] ∑ i, U i := by
  have hs := condExp_finsetSum (s := Finset.univ) (fun i _ => hInt i) m
  filter_upwards [hs, ae_all_iff.mpr hEq] with ω hsω heq
  simp only [Finset.sum_apply] at hsω ⊢
  rw [hsω]
  exact Finset.sum_congr rfl (fun i _ => heq i)

lemma cross_bound {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X X' : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hX' : ∀ i, Measurable (X' i))
    (hI : iIndepFun (Sum.elim X X') P)
    (hInt : ∀ i, Integrable (X i) P) (hInt' : ∀ i, Integrable (X' i) P)
    (hmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hmean' : ∀ i, ∫ ω, X' i ω ∂P = 0)
    (A : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Bool)
    (F : ℝ → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (hF2 : Integrable (fun ω => F (4 * ∑ i, ∑ j, A i j * X i ω * X' j ω)) P) :
    Integrable (fun ω => F (4 * cross A τ (fun i => X i ω) (fun i => X' i ω))) P ∧
    (∫ ω, F (4 * cross A τ (fun i => X i ω) (fun i => X' i ω)) ∂P) ≤
      ∫ ω, F (4 * ∑ i, ∑ j, A i j * X i ω * X' j ω) ∂P := by
  classical
  let Z : Fin n ⊕ Fin n → Ω → ℝ := Sum.elim X X'
  have hZ : ∀ k, Measurable (Z k) := by intro k; cases k <;> simp_all [Z]
  have hZi : ∀ k, Integrable (Z k) P := by intro k; cases k <;> simp_all [Z]
  have hZm : ∀ k, ∫ ω, Z k ω ∂P = 0 := by intro k; cases k <;> simp_all [Z]
  have hm := selectedSigma_le Z hZ (selectedIndices τ)
  let T : Fin n → Fin n → Ω → ℝ := fun i j => (4 * A i j) • (X i * X' j)
  let U : Fin n → Fin n → Ω → ℝ := fun i j ω =>
    (4 * A i j) * (if τ i = true ∧ τ j = false then X i ω * X' j ω else 0)
  have hT : ∀ i j, Integrable (T i j) P := by
    intro i j
    exact ((hI.indepFun (show Sum.inl i ≠ Sum.inr j by simp)).integrable_mul
      (hInt i) (hInt' j)).const_mul (4 * A i j)
  have hTU : ∀ i j, P[T i j | selectedSigma Z (selectedIndices τ)] =ᵐ[P] U i j := by
    intro i j
    have hp := pair_condExp P Z hZ hI hZi hZm (selectedIndices τ)
      (show Sum.inl i ≠ Sum.inr j by simp)
    have hc := condExp_smul (μ := P) (4 * A i j) (X i * X' j) (selectedSigma Z (selectedIndices τ))
    filter_upwards [hp, hc] with ω hpω hcω
    have hp' : P[X i * X' j | selectedSigma Z (selectedIndices τ)] ω =
        (if τ i = true ∧ τ j = false then X i ω * X' j ω else 0) := by
      simpa only [Z, Sum.elim_inl, Sum.elim_inr, selected_left, selected_right] using hpω
    simp only [Pi.smul_apply, smul_eq_mul] at hcω
    rw [hp'] at hcω
    simpa only [T, U, Pi.smul_apply, smul_eq_mul] using hcω
  have hsum := condExp_sum P (fun i => ∑ j, T i j) (fun i => ∑ j, U i j)
    (fun i => integrable_finsetSum' _ (fun j _ => hT i j))
    (fun i => condExp_sum P (T i) (U i) (hT i) (hTU i))
  have hTdef : (∑ i, ∑ j, T i j) =
      (fun ω => 4 * ∑ i, ∑ j, A i j * X i ω * X' j ω) := by
    funext ω
    simp only [Finset.sum_apply, T, Pi.smul_apply, smul_eq_mul, Pi.mul_apply,
      Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  have hUdef : (∑ i, ∑ j, U i j) =
      (fun ω => 4 * cross A τ (fun i => X i ω) (fun i => X' i ω)) := by
    funext ω
    simp only [Finset.sum_apply, U, cross, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    split_ifs <;> ring
  rw [hTdef, hUdef] at hsum
  apply convex_condExp_bound P hm _ _ _ _ hsum F hF hF2
  · rw [← hTdef]
    exact integrable_finsetSum' _ (fun i _ => integrable_finsetSum' _ (fun j _ => hT i j))
  · apply measurable_const.mul
    unfold cross
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    split_ifs
    · exact (measurable_const.mul (hX i)).mul (hX' j)
    · exact measurable_const

end DecouplingProof


-- DecouplingLaw

open MeasureTheory ProbabilityTheory

namespace DecouplingProof

def mixedIndex {n : ℕ} (τ : Fin n → Bool) (i : Fin n) : Fin n ⊕ Fin n :=
  if τ i = true then Sum.inl i else Sum.inr i

lemma mixedIndex_injective {n : ℕ} (τ : Fin n → Bool) :
    Function.Injective (mixedIndex τ) := by
  intro i j hij
  unfold mixedIndex at hij
  split_ifs at hij <;> simp_all

lemma cross_identDistrib {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X X' : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hX' : ∀ i, Measurable (X' i))
    (hI : iIndepFun (Sum.elim X X') P)
    (hd : ∀ i, IdentDistrib (X' i) (X i) P P)
    (A : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Bool)
    (F : ℝ → ℝ) (hF : Continuous F) :
    IdentDistrib (fun ω => F (4 * cross A τ (fun i => X i ω) (fun i => X i ω)))
      (fun ω => F (4 * cross A τ (fun i => X i ω) (fun i => X' i ω))) P P := by
  classical
  let Z := Sum.elim X X'
  have hcoord : ∀ i, IdentDistrib (Z (mixedIndex τ i)) (X i) P P := by
    intro i
    by_cases hi : τ i = true
    · simpa [Z, mixedIndex, hi] using IdentDistrib.refl (hX i).aemeasurable
    · simpa [Z, mixedIndex, hi] using hd i
  have hxind : iIndepFun X P := by
    simpa only [Sum.elim_inl] using hI.precomp
      (g := (Sum.inl : Fin n → Fin n ⊕ Fin n)) Sum.inl_injective
  have htuple := IdentDistrib.pi hcoord
    (hI.precomp (g := mixedIndex τ) (mixedIndex_injective τ)) hxind
  have hfun : Measurable (fun x : Fin n → ℝ => F (4 * cross A τ x x)) := by
    apply hF.measurable.comp
    apply measurable_const.mul
    unfold cross
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    split_ifs
    · exact (measurable_const.mul (measurable_pi_apply i)).mul (measurable_pi_apply j)
    · exact measurable_const
  have hcomp := htuple.comp hfun
  have hcross : (fun ω => F (4 * cross A τ (fun i => Z (mixedIndex τ i) ω)
      (fun i => Z (mixedIndex τ i) ω))) =
      (fun ω => F (4 * cross A τ (fun i => X i ω) (fun i => X' i ω))) := by
    funext ω
    congr 2
    unfold cross
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    by_cases hij : τ i = true ∧ τ j = false
    · simp [hij, Z, mixedIndex, hij.1, hij.2]
    · simp [hij]
  change IdentDistrib (fun ω => F (4 * cross A τ (fun i => Z (mixedIndex τ i) ω)
    (fun i => Z (mixedIndex τ i) ω)))
    (fun ω => F (4 * cross A τ (fun i => X i ω) (fun i => X i ω))) P P at hcomp
  rw [hcross] at hcomp
  exact hcomp.symm

end DecouplingProof


-- HansonDecouplingNonneg

open MeasureTheory ProbabilityTheory

open DecouplingProof

namespace HighDimProb.QuadraticForms

/-- **Theorem 6.1.1** (Decoupling), Vershynin, *High-Dimensional Probability* (2018), p. 136.

Let `A` be an `n × n`, diagonal-free matrix (i.e. the diagonal entries of `A` equal zero). Let
`X = (X₁, …, Xₙ)` be a random vector with independent mean zero coordinates `Xᵢ`. Then, for
every convex function `F : ℝ → ℝ`, one has `E F(XᵀAX) ≤ E F(4XᵀAX′)`, where `X′` is an
independent copy of `X`. -/
theorem convex_decoupling_nonneg {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X X' : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i)) (hX'_meas : ∀ i, Measurable (X' i))
    (hindep : iIndepFun (Sum.elim X X') P)
    (hX_int : ∀ i, Integrable (X i) P) (hX'_int : ∀ i, Integrable (X' i) P)
    (hX_mean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hX'_dist : ∀ i, IdentDistrib (X' i) (X i) P P)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, A i i = 0)
    (F : ℝ → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (hF0 : ∀ x, 0 ≤ F x)
    (hF2 : Integrable (fun ω => F (4 * ∑ i, ∑ j, A i j * X i ω * X' j ω)) P) :
    Integrable (fun ω => F (∑ i, ∑ j, A i j * X i ω * X j ω)) P ∧
    ∫ ω, F (∑ i, ∑ j, A i j * X i ω * X j ω) ∂P ≤
      ∫ ω, F (4 * ∑ i, ∑ j, A i j * X i ω * X' j ω) ∂P  := by
  classical
  have hmean' : ∀ i, ∫ ω, X' i ω ∂P = 0 := by
    intro i
    rw [(hX'_dist i).integral_eq, hX_mean i]
  have hFc : Continuous F := continuousOn_univ.mp (hF.continuousOn isOpen_univ)
  have hparts : ∀ τ : Fin n → Bool,
      Integrable (fun ω => F (4 * cross A τ (fun i => X i ω) (fun i => X i ω))) P ∧
      (∫ ω, F (4 * cross A τ (fun i => X i ω) (fun i => X i ω)) ∂P) ≤
        ∫ ω, F (4 * ∑ i, ∑ j, A i j * X i ω * X' j ω) ∂P := by
    intro τ
    obtain ⟨hcInt, hcLe⟩ := cross_bound P X X' hX_meas hX'_meas hindep
      hX_int hX'_int hX_mean hmean' A τ F hF hF2
    have hd := cross_identDistrib P X X' hX_meas hX'_meas hindep hX'_dist A τ F hFc
    exact ⟨hd.integrable_iff.mpr hcInt, hd.integral_eq.trans_le hcLe⟩
  let w : ℝ := (Fintype.card (Fin n → Bool) : ℝ)⁻¹
  have hIntAvg : Integrable (fun ω => w *
      ∑ τ : Fin n → Bool, F (4 * cross A τ (fun i => X i ω) (fun i => X i ω))) P :=
    (integrable_finsetSum _ (fun τ _ => (hparts τ).1)).const_mul w
  have hQm : Measurable (fun ω => ∑ i, ∑ j, A i j * X i ω * X j ω) := by
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    exact ((hX_meas i).const_mul _).mul (hX_meas j)
  have hF1 : Integrable (fun ω => F (∑ i, ∑ j, A i j * X i ω * X j ω)) P := by
    refine hIntAvg.mono' (hFc.measurable.comp hQm).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 _)]
    exact convex_average_cross A hA F hF (fun i => X i ω)
  refine ⟨hF1, ?_⟩
  calc
    (∫ ω, F (∑ i, ∑ j, A i j * X i ω * X j ω) ∂P) ≤
        ∫ ω, w * ∑ τ : Fin n → Bool,
          F (4 * cross A τ (fun i => X i ω) (fun i => X i ω)) ∂P :=
      integral_mono hF1 hIntAvg (fun ω => convex_average_cross A hA F hF (fun i => X i ω))
    _ = w * ∑ τ : Fin n → Bool,
        ∫ ω, F (4 * cross A τ (fun i => X i ω) (fun i => X i ω)) ∂P := by
      rw [integral_const_mul]
      congr 1
      exact integral_finsetSum _ (fun τ _ => (hparts τ).1)
    _ ≤ w * ∑ _τ : Fin n → Bool,
        ∫ ω, F (4 * ∑ i, ∑ j, A i j * X i ω * X' j ω) ∂P := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum (fun τ _ => (hparts τ).2)
      · positivity
    _ = _ := by
      simp [w, nsmul_eq_mul, ← mul_assoc]




end HighDimProb.QuadraticForms


-- HansonScalarMGF

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real

-- Scalar MGF conversion adapted from Nickrobbins95's accepted General Hoeffding proof
-- (submission 565f5a69-62e2-4ba5-b641-a7dcb105f2ee).
namespace HansonWrightMGF

lemma hdpc_exp_le_add_exp_sq (x : ℝ) : exp x ≤ x + exp (x ^ 2) := by
  rcases le_or_gt |x| 1 with hx | hx
  · have h1 := Real.abs_exp_sub_one_sub_id_le hx
    have h2 := Real.add_one_le_exp (x ^ 2)
    have h3 := (abs_le.1 h1).2
    linarith
  · rcases le_or_gt 0 x with h0 | h0
    · have hx1 : 1 < x := by rwa [abs_of_nonneg h0] at hx
      have h4 : x ≤ x ^ 2 := by nlinarith
      have h5 := exp_le_exp.2 h4
      linarith
    · have hx1 : x < -1 := by
        rw [abs_of_neg h0] at hx; linarith
      have h4 : exp x ≤ 1 := Real.exp_le_one_iff.2 h0.le
      have h5 := Real.add_one_le_exp (x ^ 2)
      nlinarith

lemma hdpc_pt1 (l b σ : ℝ) :
    exp (l * (σ * b)) ≤ exp (l ^ 2 * σ ^ 2 / 2) * (1 / 2 + exp (b ^ 2) / 2) := by
  have h1 : l * (σ * b) ≤ l ^ 2 * σ ^ 2 / 2 + b ^ 2 / 2 := by
    nlinarith [sq_nonneg (l * σ - b)]
  have h2 : exp (b ^ 2 / 2) ≤ 1 / 2 + exp (b ^ 2) / 2 := by
    have hz : exp (b ^ 2) = exp (b ^ 2 / 2) ^ 2 := by rw [sq (exp _), ← exp_add]; ring_nf
    nlinarith [sq_nonneg (exp (b ^ 2 / 2) - 1)]
  calc exp (l * (σ * b)) ≤ exp (l ^ 2 * σ ^ 2 / 2 + b ^ 2 / 2) := exp_le_exp.2 h1
    _ = exp (l ^ 2 * σ ^ 2 / 2) * exp (b ^ 2 / 2) := exp_add _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (exp_pos _).le

lemma hdpc_pt2 (l b σ : ℝ) (hq : l ^ 2 * σ ^ 2 ≤ 1) :
    exp (l * (σ * b)) ≤ l * (σ * b) + (1 - l ^ 2 * σ ^ 2) + l ^ 2 * σ ^ 2 * exp (b ^ 2) := by
  have h1 := hdpc_exp_le_add_exp_sq (l * (σ * b))
  have h2 : (l * (σ * b)) ^ 2 = l ^ 2 * σ ^ 2 * b ^ 2 + (1 - l ^ 2 * σ ^ 2) * 0 := by ring
  have hq0 : 0 ≤ l ^ 2 * σ ^ 2 := by positivity
  have h3 := convexOn_exp.2 (Set.mem_univ (b ^ 2)) (Set.mem_univ (0 : ℝ)) hq0 (sub_nonneg.2 hq)
    (by ring : l ^ 2 * σ ^ 2 + (1 - l ^ 2 * σ ^ 2) = 1)
  simp only [smul_eq_mul] at h3
  rw [h2] at h1
  rw [exp_zero] at h3
  linarith

lemma hdpc_subG {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (hmean : ∫ ω, Y ω ∂P = 0) (σ : ℝ) (hσ : 0 < σ)
    (hint : Integrable (fun ω => exp (Y ω ^ 2 / σ ^ 2)) P)
    (hle : ∫ ω, exp (Y ω ^ 2 / σ ^ 2) ∂P ≤ 2) :
    HasSubgaussianMGF Y (2 * σ ^ 2).toNNReal P := by
  have hYσ : ∀ ω, σ * (Y ω / σ) = Y ω := fun ω => by field_simp
  have hYσ2 : ∀ ω, (Y ω / σ) ^ 2 = Y ω ^ 2 / σ ^ 2 := fun ω => div_pow _ _ _
  have hpt1 : ∀ l ω, exp (l * Y ω) ≤
      exp (l ^ 2 * σ ^ 2 / 2) * (1 / 2 + exp (Y ω ^ 2 / σ ^ 2) / 2) := by
    intro l ω
    have h := hdpc_pt1 l (Y ω / σ) σ
    rwa [hYσ, hYσ2] at h
  have hintE : ∀ l, Integrable (fun ω => exp (l * Y ω)) P := by
    intro l
    refine Integrable.mono' (((integrable_const (1 / 2 : ℝ)).add (hint.div_const 2)).const_mul
      (exp (l ^ 2 * σ ^ 2 / 2))) ((hY.const_mul l).exp.aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact hpt1 l ω
  have hYint : Integrable Y P := by
    refine Integrable.mono' (hint.const_mul σ) hY.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    have h1 : |Y ω / σ| ≤ exp ((Y ω / σ) ^ 2) := by
      nlinarith [sq_nonneg (|Y ω / σ| - 1 / 2), sq_abs (Y ω / σ),
        add_one_le_exp ((Y ω / σ) ^ 2)]
    rw [hYσ2, abs_div, abs_of_pos hσ, div_le_iff₀ hσ] at h1
    linarith [mul_comm σ (exp (Y ω ^ 2 / σ ^ 2))]
  refine ⟨hintE, fun l => ?_⟩
  have htarget : ((2 * σ ^ 2).toNNReal : ℝ) * l ^ 2 / 2 = l ^ 2 * σ ^ 2 := by
    rw [Real.coe_toNNReal _ (by positivity)]; ring
  rw [htarget, mgf]
  rcases le_or_gt (l ^ 2 * σ ^ 2) 1 with hq | hq
  · have hpt2 : ∀ ω, exp (l * Y ω) ≤
        l * Y ω + (1 - l ^ 2 * σ ^ 2) + l ^ 2 * σ ^ 2 * exp (Y ω ^ 2 / σ ^ 2) := by
      intro ω
      have h := hdpc_pt2 l (Y ω / σ) σ hq
      rwa [hYσ, hYσ2] at h
    have hI1 : Integrable (fun ω => l * Y ω + (1 - l ^ 2 * σ ^ 2)) P :=
      (hYint.const_mul l).add (integrable_const _)
    have hI2 : Integrable (fun ω => l ^ 2 * σ ^ 2 * exp (Y ω ^ 2 / σ ^ 2)) P := hint.const_mul _
    calc ∫ ω, exp (l * Y ω) ∂P
        ≤ ∫ ω, (l * Y ω + (1 - l ^ 2 * σ ^ 2) + l ^ 2 * σ ^ 2 * exp (Y ω ^ 2 / σ ^ 2)) ∂P :=
          integral_mono (hintE l) (hI1.add hI2) hpt2
      _ = l * ∫ ω, Y ω ∂P + (1 - l ^ 2 * σ ^ 2) +
            l ^ 2 * σ ^ 2 * ∫ ω, exp (Y ω ^ 2 / σ ^ 2) ∂P := by
          rw [integral_add hI1 hI2, integral_add (hYint.const_mul l) (integrable_const _),
            integral_const_mul, integral_const_mul, integral_const]
          simp
      _ ≤ 1 + l ^ 2 * σ ^ 2 := by
          rw [hmean]
          have hq0 : 0 ≤ l ^ 2 * σ ^ 2 := by positivity
          nlinarith
      _ ≤ exp (l ^ 2 * σ ^ 2) := by linarith [add_one_le_exp (l ^ 2 * σ ^ 2)]
  · have hI : Integrable
        (fun ω => exp (l ^ 2 * σ ^ 2 / 2) * (1 / 2 + exp (Y ω ^ 2 / σ ^ 2) / 2)) P :=
      ((integrable_const (1 / 2 : ℝ)).add (hint.div_const 2)).const_mul _
    calc ∫ ω, exp (l * Y ω) ∂P
        ≤ ∫ ω, exp (l ^ 2 * σ ^ 2 / 2) * (1 / 2 + exp (Y ω ^ 2 / σ ^ 2) / 2) ∂P :=
          integral_mono (hintE l) hI (hpt1 l)
      _ = exp (l ^ 2 * σ ^ 2 / 2) * (1 / 2 + (∫ ω, exp (Y ω ^ 2 / σ ^ 2) ∂P) / 2) := by
          rw [integral_const_mul, integral_add (integrable_const _) (hint.div_const 2),
            integral_const, integral_div]
          simp
      _ ≤ exp (l ^ 2 * σ ^ 2 / 2) * exp (l ^ 2 * σ ^ 2 / 2) := by
          apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
          have h1 := add_one_le_exp (1 / 2 : ℝ)
          have h2 : exp (1 / 2 : ℝ) ≤ exp (l ^ 2 * σ ^ 2 / 2) := exp_le_exp.2 (by linarith)
          linarith
      _ = exp (l ^ 2 * σ ^ 2) := by rw [← exp_add]; ring_nf

lemma hdpc_const_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (h : HasSubgaussianMGF Y c.toNNReal P) (r : ℝ) :
    HasSubgaussianMGF (fun ω => r * Y ω) (r ^ 2 * c).toNNReal P := by
  have h1 := h.const_mul r
  convert h1 using 1
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (by positivity)]
  show r ^ 2 * c = r ^ 2 * (c.toNNReal : ℝ)
  rw [Real.coe_toNNReal _ hc]


end HansonWrightMGF


-- HansonBilinearMGF

open MeasureTheory ProbabilityTheory Real HighDimProb.Concentration

namespace HansonWrightMGF

lemma subgaussianMGF_of_norm_bound {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (hY : Measurable Y) (hmean : ∫ ω, Y ω ∂P = 0)
    (hsg : ∃ s > 0, Integrable (fun ω => exp (Y ω ^ 2 / s ^ 2)) P ∧
      ∫ ω, exp (Y ω ^ 2 / s ^ 2) ∂P ≤ 2)
    {K : ℝ} (hK : 0 < K) (hnorm : subgaussianNorm P Y ≤ K) :
    HasSubgaussianMGF Y (8 * K ^ 2).toNNReal P := by
  obtain ⟨s0, hs0, hint0, hle0⟩ := hsg
  have hne : ({s : ℝ | 0 < s ∧ Integrable (fun ω => exp (Y ω ^ 2 / s ^ 2)) P ∧
      ∫ ω, exp (Y ω ^ 2 / s ^ 2) ∂P ≤ 2}).Nonempty := ⟨s0, hs0, hint0, hle0⟩
  have hlt : subgaussianNorm P Y < 2 * K := by linarith
  unfold subgaussianNorm at hlt
  obtain ⟨s, ⟨hs, hints, hles⟩, hs2⟩ := exists_lt_of_csInf_lt hne hlt
  have hmono : ∀ ω, exp (Y ω ^ 2 / (2 * K) ^ 2) ≤ exp (Y ω ^ 2 / s ^ 2) := fun ω =>
    exp_le_exp.2 (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (pow_le_pow_left₀ hs.le hs2.le 2))
  have hint2 : Integrable (fun ω => exp (Y ω ^ 2 / (2 * K) ^ 2)) P :=
    hints.mono' ((hY.pow_const 2).div_const _).exp.aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]; exact hmono ω)
  have hle2 := (integral_mono hint2 hints hmono).trans hles
  have h := hdpc_subG P Y hY hmean (2 * K) (by positivity) hint2 hle2
  have heq : 2 * (2 * K) ^ 2 = 8 * K ^ 2 := by ring
  simpa only [heq] using h

lemma linear_mgf {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ι → Ω → ℝ)
    (hind : iIndepFun Y P) {K : ℝ}
    (hsub : ∀ j, HasSubgaussianMGF (Y j) (8 * K ^ 2).toNNReal P)
    (a : ι → ℝ) (l : ℝ) :
    Integrable (fun ω => exp (l * ∑ j, a j * Y j ω)) P ∧
      ∫ ω, exp (l * ∑ j, a j * Y j ω) ∂P ≤
        exp (4 * l ^ 2 * K ^ 2 * ∑ j, a j ^ 2) := by
  classical
  have hind' : iIndepFun (fun j ω => a j * Y j ω) P :=
    hind.comp (fun j x => a j * x) (fun _ => measurable_const.mul measurable_id)
  have hsub' : ∀ j ∈ (Finset.univ : Finset ι),
      HasSubgaussianMGF (fun ω => a j * Y j ω) (a j ^ 2 * (8 * K ^ 2)).toNNReal P :=
    fun j _ => hdpc_const_mul (by positivity) (hsub j) (a j)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hind' hsub'
  refine ⟨hsum.integrable_exp_mul l, ?_⟩
  have hbound := hsum.mgf_le l
  have hcoef : ((∑ j, (a j ^ 2 * (8 * K ^ 2)).toNNReal : NNReal) : ℝ) =
      (∑ j, a j ^ 2) * (8 * K ^ 2) := by
    rw [NNReal.coe_sum]
    rw [Finset.sum_congr rfl (fun j _ => Real.coe_toNNReal _
      (by positivity : (0 : ℝ) ≤ a j ^ 2 * (8 * K ^ 2))), Finset.sum_mul]
  rw [mgf, hcoef] at hbound
  convert hbound using 1 <;> ring

end HansonWrightMGF

namespace HighDimProb.QuadraticForms

/-- Integrating out the independent subgaussian vector reduces a bilinear MGF to
an exponential moment of the squared Euclidean norm of the coefficient vector.
The integrability hypothesis on that moment also proves integrability on the left. -/
theorem bilinear_mgf_reduction {n m : ℕ} {Ω Ω' : Type}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : Fin n → Ω → ℝ) (Y : Fin m → Ω' → ℝ)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hind : iIndepFun Y Q) (hmean : ∀ j, ∫ ω, Y j ω ∂Q = 0)
    (hsg : ∀ j, ∃ s > 0, Integrable (fun ω => exp (Y j ω ^ 2 / s ^ 2)) Q ∧
      ∫ ω, exp (Y j ω ^ 2 / s ^ 2) ∂Q ≤ 2)
    (A : Matrix (Fin n) (Fin m) ℝ) {K : ℝ} (hK : 0 < K)
    (hnorm : ∀ j, HighDimProb.Concentration.subgaussianNorm Q (Y j) ≤ K)
    (l : ℝ)
    (hbound : Integrable (fun ω =>
      exp (4 * l ^ 2 * K ^ 2 * ∑ j, (∑ i, A i j * X i ω) ^ 2)) P) :
    Integrable (fun z : Ω × Ω' =>
      exp (l * ∑ i, ∑ j, A i j * X i z.1 * Y j z.2)) (P.prod Q) ∧
    (∫ z : Ω × Ω', exp (l * ∑ i, ∑ j, A i j * X i z.1 * Y j z.2) ∂P.prod Q) ≤
      ∫ ω, exp (4 * l ^ 2 * K ^ 2 * ∑ j, (∑ i, A i j * X i ω) ^ 2) ∂P := by
  classical
  have hsub := fun j => HansonWrightMGF.subgaussianMGF_of_norm_bound Q (Y j)
    (hY j) (hmean j) (hsg j) hK (hnorm j)
  have hrepr : ∀ x y, (∑ i, ∑ j, A i j * X i x * Y j y) =
      ∑ j, (∑ i, A i j * X i x) * Y j y := by
    intro x y
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_mul]
  have hsection : ∀ x,
      Integrable (fun y => exp (l * ∑ i, ∑ j, A i j * X i x * Y j y)) Q ∧
      (∫ y, exp (l * ∑ i, ∑ j, A i j * X i x * Y j y) ∂Q) ≤
        exp (4 * l ^ 2 * K ^ 2 * ∑ j, (∑ i, A i j * X i x) ^ 2) := by
    intro x
    simp_rw [hrepr]
    exact HansonWrightMGF.linear_mgf Q Y hind hsub (fun j => ∑ i, A i j * X i x) l
  have hmeas : Measurable (fun z : Ω × Ω' =>
      exp (l * ∑ i, ∑ j, A i j * X i z.1 * Y j z.2)) := by
    apply Measurable.exp
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    exact (measurable_const.mul ((hX i).comp measurable_fst)).mul
      ((hY j).comp measurable_snd)
  have hinner : Integrable (fun x =>
      ∫ y, exp (l * ∑ i, ∑ j, A i j * X i x * Y j y) ∂Q) P := by
    refine hbound.mono' hmeas.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable ?_
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => (exp_pos _).le))]
    exact (hsection x).2
  have hfull : Integrable (fun z : Ω × Ω' =>
      exp (l * ∑ i, ∑ j, A i j * X i z.1 * Y j z.2)) (P.prod Q) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ (fun x => (hsection x).1), ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_pos (exp_pos _)] using hinner
  refine ⟨hfull, ?_⟩
  rw [integral_prod _ hfull]
  exact integral_mono hinner hbound (fun x => (hsection x).2)

end HighDimProb.QuadraticForms


-- HansonGaussianLaplace

open MeasureTheory ProbabilityTheory Real

namespace HansonWrightGaussian

lemma gaussian_sq_laplace (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1 / 4) :
    Integrable (fun x : ℝ => exp (a * x ^ 2)) (gaussianReal 0 1) ∧
      (∫ x : ℝ, exp (a * x ^ 2) ∂gaussianReal 0 1) ≤ exp (2 * a) := by
  have hb : 0 < 1 / 2 - a := by linarith
  have hd : 0 < 1 - 2 * a := by linarith
  have hp : 0 < 2 * Real.pi := by positivity
  have hw : ∀ x : ℝ, gaussianPDFReal 0 1 x * exp (a * x ^ 2) =
      (sqrt (2 * Real.pi))⁻¹ * exp (-(1 / 2 - a) * x ^ 2) := by
    intro x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← exp_add]
    congr 2
    ring
  have hwi : Integrable (fun x : ℝ => gaussianPDFReal 0 1 x * exp (a * x ^ 2)) := by
    simp_rw [hw]
    exact (integrable_exp_neg_mul_sq hb).const_mul _
  have hi : Integrable (fun x : ℝ => exp (a * x ^ 2)) (gaussianReal 0 1) := by
    rw [gaussianReal_of_var_ne_zero _ (one_ne_zero : (1 : NNReal) ≠ 0)]
    apply (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)).mpr
    simpa only [toReal_gaussianPDF, smul_eq_mul] using hwi
  have heq : (∫ x : ℝ, exp (a * x ^ 2) ∂gaussianReal 0 1) =
      (sqrt (2 * Real.pi))⁻¹ * sqrt (Real.pi / (1 / 2 - a)) := by
    rw [integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : NNReal) ≠ 0)]
    simp_rw [smul_eq_mul, hw]
    rw [integral_const_mul, integral_gaussian]
  refine ⟨hi, ?_⟩
  rw [heq]
  set R := (sqrt (2 * Real.pi))⁻¹ * sqrt (Real.pi / (1 / 2 - a))
  have hR : 0 ≤ R := by positivity
  have hsq : R ^ 2 * (1 - 2 * a) = 1 := by
    dsimp [R]
    rw [mul_pow, inv_pow, sq_sqrt hp.le, sq_sqrt (by positivity)]
    field_simp
  have hex : 1 ≤ exp (4 * a) * (1 - 2 * a) := by
    have h := mul_le_mul_of_nonneg_right (add_one_le_exp (4 * a)) hd.le
    nlinarith
  have he2 : exp (2 * a) ^ 2 = exp (4 * a) := by
    rw [sq, ← exp_add]
    congr 1
    ring
  have hsqle : R ^ 2 ≤ exp (2 * a) ^ 2 := by
    apply le_of_mul_le_mul_right (show R ^ 2 * (1 - 2 * a) ≤
      exp (2 * a) ^ 2 * (1 - 2 * a) from ?_) hd
    rw [hsq, he2]
    exact hex
  exact (sq_le_sq₀ hR (exp_pos _).le).mp hsqle

lemma gaussian_pi_sq_laplace {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hd' : ∀ i, d i ≤ 1 / 4) :
    Integrable (fun x : ι → ℝ => exp (∑ i, d i * x i ^ 2))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) ∧
    (∫ x : ι → ℝ, exp (∑ i, d i * x i ^ 2)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) ≤ exp (2 * ∑ i, d i) := by
  classical
  have hc := fun i => gaussian_sq_laplace (d i) (hd i) (hd' i)
  refine ⟨?_, ?_⟩
  · simp_rw [exp_sum]
    exact Integrable.fintype_prod_dep (fun i => (hc i).1)
  · simp_rw [exp_sum]
    rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => exp (d i * x ^ 2))]
    calc (∏ i, ∫ x : ℝ, exp (d i * x ^ 2) ∂gaussianReal 0 1)
        ≤ ∏ i, exp (2 * d i) :=
          Finset.prod_le_prod (fun i _ => integral_nonneg (fun _ => (exp_pos _).le))
            (fun i _ => (hc i).2)
      _ = exp (2 * ∑ i, d i) := by rw [← exp_sum, Finset.mul_sum]

end HansonWrightGaussian


-- HansonGramSpectrum

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace

namespace HansonWrightGaussian

lemma gram_spectral_data {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (T : E →L[ℝ] F) (hn : Module.finrank ℝ E = n)
    (b0 : OrthonormalBasis (Fin n) ℝ E) :
    ∃ (b : OrthonormalBasis (Fin n) ℝ E) (d : Fin n → ℝ),
      (∀ i, 0 ≤ d i ∧ d i ≤ ‖T‖ ^ 2) ∧
      (∀ x : E, ‖T x‖ ^ 2 = ∑ i, d i * (b.repr x i) ^ 2) ∧
      (∑ i, d i) = ∑ i, ‖T (b0 i)‖ ^ 2 := by
  classical
  let G : E →ₗ[ℝ] E := (T.adjoint.comp T).toLinearMap
  have hs : G.IsSymmetric := by
    intro x y
    change ⟪T.adjoint (T x), y⟫ = ⟪x, T.adjoint (T y)⟫
    rw [T.adjoint_inner_left, T.adjoint_inner_right]
  let b := hs.eigenvectorBasis hn
  let d := hs.eigenvalues hn
  have heig : ∀ i, G (b i) = d i • b i := hs.apply_eigenvectorBasis hn
  have he : ∀ i, ‖T (b i)‖ ^ 2 = d i := by
    intro i
    rw [T.apply_norm_sq_eq_inner_adjoint_right]
    change ⟪b i, G (b i)⟫ = d i
    rw [heig, real_inner_smul_right, real_inner_self_eq_norm_sq, b.norm_eq_one]
    ring
  refine ⟨b, d, ?_, ?_, ?_⟩
  · intro i
    refine ⟨by rw [← he]; positivity, ?_⟩
    rw [← he]
    have hle := T.le_opNorm (b i)
    rw [b.norm_eq_one, mul_one] at hle
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  · intro x
    rw [T.apply_norm_sq_eq_inner_adjoint_right]
    change ⟪x, G x⟫ = _
    rw [← b.sum_inner_mul_inner x (G x)]
    apply Finset.sum_congr rfl
    intro i _
    have hrepr : b.repr (G x) i = d i * b.repr x i :=
      hs.eigenvectorBasis_apply_self_apply hn x i
    rw [b.repr_apply_apply, b.repr_apply_apply] at hrepr
    rw [hrepr, b.repr_apply_apply]
    simp only [real_inner_comm]
    ring
  · have htrace : G.trace ℝ E = ∑ i, d i := hs.trace_eq_sum_eigenvalues hn
    rw [← htrace, LinearMap.trace_eq_sum_inner G b0]
    apply Finset.sum_congr rfl
    intro i _
    have h := T.apply_norm_sq_eq_inner_adjoint_right (b0 i)
    exact h.symm

end HansonWrightGaussian


-- HansonGaussianOperator

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace

namespace HansonWrightGaussian

lemma gaussian_operator_sq_laplace {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    (T : E →L[ℝ] F) (hn : Module.finrank ℝ E = n)
    (b0 : OrthonormalBasis (Fin n) ℝ E) {u : ℝ} (hu : 0 ≤ u)
    (hub : u * ‖T‖ ^ 2 ≤ 1 / 4) :
    Integrable (fun x : E => exp (u * ‖T x‖ ^ 2)) (stdGaussian E) ∧
      (∫ x : E, exp (u * ‖T x‖ ^ 2) ∂stdGaussian E) ≤
        exp (2 * u * ∑ i, ‖T (b0 i)‖ ^ 2) := by
  classical
  obtain ⟨b, d, hd, hdiag, hsum⟩ := gram_spectral_data T hn b0
  have hc := gaussian_pi_sq_laplace (fun i => u * d i)
    (fun i => mul_nonneg hu (hd i).1)
    (fun i => (mul_le_mul_of_nonneg_left (hd i).2 hu).trans hub)
  have hrepr : ∀ x : Fin n → ℝ,
      exp (u * ‖T (∑ i, x i • b i)‖ ^ 2) = exp (∑ i, (u * d i) * x i ^ 2) := by
    intro x
    rw [hdiag, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hx : (∑ j, x j • b j) = b.repr.symm (WithLp.toLp 2 x) := b.sum_repr_symm _
    rw [hx, LinearIsometryEquiv.apply_symm_apply]
    change u * (d i * x i ^ 2) = (u * d i) * x i ^ 2
    ring
  have hm : Measurable (fun x : Fin n → ℝ => ∑ i, x i • b i) :=
    Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).smul measurable_const)
  rw [stdGaussian_eq_map_pi_orthonormalBasis b]
  have hi : Integrable (fun x : E => exp (u * ‖T x‖ ^ 2))
      ((Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map (fun x => ∑ i, x i • b i)) := by
    rw [integrable_map_measure (by fun_prop) hm.aemeasurable]
    simp only [Function.comp_def]
    simp_rw [hrepr]
    exact hc.1
  refine ⟨hi, ?_⟩
  rw [integral_map hm.aemeasurable (by fun_prop)]
  simp_rw [hrepr]
  have hr : 2 * ∑ i, u * d i = 2 * u * ∑ i, ‖T (b0 i)‖ ^ 2 := by
    rw [← Finset.mul_sum, hsum]
    ring
  simpa only [hr] using hc.2

end HansonWrightGaussian


-- HansonMatrixNorms

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace

namespace HighDimProb.QuadraticForms

lemma frobeniusNorm_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    frobeniusNorm A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  exact sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)

lemma matrix_basis_energy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2) =
      frobeniusNorm A ^ 2 := by
  classical
  rw [frobeniusNorm_sq]
  have hcol : ∀ i j, (Matrix.toEuclideanCLM (𝕜 := ℝ) A
      (EuclideanSpace.basisFun (Fin n) ℝ i)) j = A j i := by
    intro i j
    rw [EuclideanSpace.basisFun_apply]
    change Matrix.mulVec A (Pi.single i 1) j = A j i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  simp_rw [EuclideanSpace.real_norm_sq_eq, hcol]
  exact Finset.sum_comm

lemma opNorm_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    opNorm A.transpose = opNorm A := by
  have ht : A.transpose = star A := by ext i j; simp
  unfold opNorm
  rw [ht]
  simpa only [map_star] using
    (norm_star (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A))

lemma frobeniusNorm_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    frobeniusNorm A.transpose = frobeniusNorm A := by
  unfold frobeniusNorm
  congr 1
  exact Finset.sum_comm

end HighDimProb.QuadraticForms


-- HansonGaussianMatrix

open MeasureTheory ProbabilityTheory Real

namespace HighDimProb.QuadraticForms

theorem gaussian_matrix_sq_laplace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hub : u * opNorm A ^ 2 ≤ 1 / 4) :
    Integrable (fun x : Fin n → ℝ => exp (u * ∑ i, (∑ j, A i j * x j) ^ 2))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) ∧
    (∫ x : Fin n → ℝ, exp (u * ∑ i, (∑ j, A i j * x j) ^ 2)
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) ≤
        exp (2 * u * frobeniusNorm A ^ 2) := by
  classical
  have hs := HansonWrightGaussian.gaussian_operator_sq_laplace
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A) (by simp)
    (EuclideanSpace.basisFun (Fin n) ℝ) hu hub
  have hnorm : ∀ x : Fin n → ℝ,
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (WithLp.toLp 2 x)‖ ^ 2 =
        ∑ i, (∑ j, A i j * x j) ^ 2 := by
    intro x
    rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [← map_pi_eq_stdGaussian (ι := Fin n)] at hs
  have hi := (integrable_map_measure (by fun_prop) (by fun_prop)).mp hs.1
  have hle := hs.2
  rw [integral_map (by fun_prop) (by fun_prop)] at hle
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_def, hnorm] using hi
  · rw [matrix_basis_energy] at hle
    simpa only [hnorm] using hle

end HighDimProb.QuadraticForms


-- HansonGaussianLinear

open MeasureTheory ProbabilityTheory Real

namespace HansonWrightGaussian

lemma gaussian_linear_mgf {ι : Type*} [Fintype ι] (a : ι → ℝ) (s : ℝ) :
    Integrable (fun x : ι → ℝ => exp (s * ∑ i, a i * x i))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) ∧
    (∫ x : ι → ℝ, exp (s * ∑ i, a i * x i)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = exp (s ^ 2 / 2 * ∑ i, a i ^ 2) := by
  classical
  have hr : ∀ x : ι → ℝ, s * ∑ i, a i * x i = ∑ i, (s * a i) * x i := by
    intro x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hc : ∀ i, (∫ x : ℝ, exp ((s * a i) * x) ∂gaussianReal 0 1) =
      exp ((s * a i) ^ 2 / 2) := by
    intro i
    simpa only [mgf, NNReal.coe_one, zero_mul, zero_add, one_mul] using
      congr_fun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) (s * a i)
  refine ⟨?_, ?_⟩
  · simp_rw [hr, exp_sum]
    exact Integrable.fintype_prod_dep
      (fun i => integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (s * a i))
  · simp_rw [hr, exp_sum]
    rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => exp ((s * a i) * x))]
    simp_rw [hc]
    rw [← exp_sum, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

end HansonWrightGaussian


-- HansonGaussianComparison

open MeasureTheory ProbabilityTheory Real HighDimProb.Concentration

namespace HighDimProb.QuadraticForms

theorem subgaussian_matrix_sq_laplace {n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hsg : ∀ i, ∃ s > 0, Integrable (fun ω => exp (X i ω ^ 2 / s ^ 2)) P ∧
      ∫ ω, exp (X i ω ^ 2 / s ^ 2) ∂P ≤ 2)
    (A : Matrix (Fin n) (Fin n) ℝ) {K : ℝ} (hK : 0 < K)
    (hnorm : ∀ i, subgaussianNorm P (X i) ≤ K) {u : ℝ} (hu : 0 ≤ u)
    (hub : 8 * u * K ^ 2 * opNorm A ^ 2 ≤ 1 / 4) :
    Integrable (fun ω => exp (u * ∑ j, (∑ i, A i j * X i ω) ^ 2)) P ∧
    (∫ ω, exp (u * ∑ j, (∑ i, A i j * X i ω) ^ 2) ∂P) ≤
      exp (16 * u * K ^ 2 * frobeniusNorm A ^ 2) := by
  classical
  let G := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let s := sqrt (2 * u)
  have hs : s ^ 2 = 2 * u := sq_sqrt (by positivity)
  have hfac : 4 * s ^ 2 * K ^ 2 = 8 * u * K ^ 2 := by rw [hs]; ring
  have hg := gaussian_matrix_sq_laplace A (u := 8 * u * K ^ 2) (by positivity) hub
  have hb := bilinear_mgf_reduction G P (fun i (g : Fin n → ℝ) => g i) X
    (fun i => measurable_pi_apply i) hX hind hmean hsg A.transpose hK hnorm s
    (by simpa only [Matrix.transpose_apply, hfac] using hg.1)
  have hrepr : ∀ g : Fin n → ℝ, ∀ ω : Ω,
      (∑ i, ∑ j, A.transpose i j * g i * X j ω) =
        ∑ i, (∑ j, A j i * X j ω) * g i := by
    intro g ω
    simp only [Matrix.transpose_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hinner : ∀ ω : Ω,
      (∫ g : Fin n → ℝ, exp (s * ∑ i, ∑ j, A.transpose i j * g i * X j ω) ∂G) =
        exp (u * ∑ j, (∑ i, A i j * X i ω) ^ 2) := by
    intro ω
    simp_rw [hrepr]
    have h := (HansonWrightGaussian.gaussian_linear_mgf
      (fun j => ∑ i, A i j * X i ω) s).2
    have hc : s ^ 2 / 2 = u := by rw [hs]; ring
    simpa only [hc] using h
  have hi := hb.1.integral_prod_right
  refine ⟨?_, ?_⟩
  · simpa only [hinner] using hi
  · have hle := hb.2
    rw [integral_prod_symm _ hb.1] at hle
    simp only [hinner] at hle
    simp only [Matrix.transpose_apply, hfac] at hle
    have hg' : (∫ g : Fin n → ℝ, exp (8 * u * K ^ 2 * ∑ i, (∑ j, A i j * g j) ^ 2) ∂G) ≤
        exp (16 * u * K ^ 2 * frobeniusNorm A ^ 2) := by
      convert hg.2 using 1 <;> ring
    exact hle.trans hg'

end HighDimProb.QuadraticForms


-- HansonPositiveMGF

open MeasureTheory ProbabilityTheory Real

-- Elementary exponential bounds adapted from Nickrobbins95's accepted
-- norm-concentration proof, submission 8050e4ce-6d8e-41f1-a560-8bf0bc89bde0.
namespace HansonWrightDiagonal

lemma cn_exp_le (x : ℝ) : exp x ≤ 1 + x + x ^ 2 + x ^ 2 * exp x := by
  have hex := exp_pos x
  rcases le_or_gt |x| 1 with hx | hx
  · have h1 := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le hx)).2
    have h2 : 0 ≤ x ^ 2 * exp x := by positivity
    linarith
  · rcases le_or_gt 0 x with h0 | h0
    · have hx1 : 1 < x := by rwa [abs_of_nonneg h0] at hx
      have h4 : 1 ≤ x ^ 2 := by nlinarith
      nlinarith
    · have hx1 : x < -1 := by
        rw [abs_of_neg h0] at hx; linarith
      have h4 : exp x ≤ 1 := Real.exp_le_one_iff.2 h0.le
      nlinarith

lemma cn_exp_half_le_two : exp (1 / 2 : ℝ) ≤ 2 := by
  have h1 : exp (1 / 2 : ℝ) * exp (1 / 2) = exp 1 := by rw [← exp_add]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 := exp_pos (1 / 2 : ℝ)
  nlinarith

lemma positive_centered_pointwise (q m r : ℝ) (hq : 0 ≤ q) (hm : 0 ≤ m)
    (hm' : m ≤ 1) (hr : |r| ≤ 1 / 2) :
    exp (r * (q - m)) ≤ 2 * exp (q / 2) ∧
    exp (r * (q - m)) ≤ 1 + r * (q - m) + 27 * r ^ 2 * exp q := by
  set h := exp (q / 2) with hh
  have hh1 : 1 ≤ h := one_le_exp (by linarith)
  have hE : exp q = h * h := by rw [hh, ← exp_add]; ring_nf
  have hq2 : q ^ 2 ≤ 8 * h := by
    have := quadratic_le_exp_of_nonneg (x := q / 2) (by linarith)
    nlinarith
  set x := r * (q - m) with hx
  have hx2 : x ^ 2 ≤ r ^ 2 * (8 * h + 1) := by
    have h1 : x ^ 2 = r ^ 2 * (q - m) ^ 2 := by rw [hx]; ring
    have h2 : (q - m) ^ 2 ≤ 8 * h + 1 := by nlinarith
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have hB : exp x ≤ 2 * h := by
    have h1 : x ≤ |r| * q + |r| * m := by
      have := neg_abs_le r
      have := le_abs_self r
      rw [hx]
      nlinarith
    have h2 : |r| * q ≤ q / 2 := by nlinarith
    have h3 : |r| * m ≤ 1 / 2 := by nlinarith [abs_nonneg r]
    calc exp x ≤ exp (q / 2 + 1 / 2) := exp_le_exp.2 (by linarith)
      _ = h * exp (1 / 2) := by rw [exp_add]
      _ ≤ h * 2 := mul_le_mul_of_nonneg_left cn_exp_half_le_two (by linarith)
      _ = 2 * h := by ring
  refine ⟨hB, ?_⟩
  have hx2e : x ^ 2 * exp x ≤ r ^ 2 * (8 * h + 1) * (2 * h) :=
    mul_le_mul hx2 hB (exp_pos _).le (by positivity)
  have hmain := cn_exp_le x
  have hhh : h ≤ h * h := by nlinarith
  have hqbound : (8 * h + 1) + (8 * h + 1) * (2 * h) ≤ 27 * (h * h) := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hqbound (sq_nonneg r)
  rw [hE]
  nlinarith

lemma positive_centered_mgf {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y)
    (hY0 : ∀ ω, 0 ≤ Y ω) (hI : Integrable (fun ω => exp (Y ω)) P)
    (hE : ∫ ω, exp (Y ω) ∂P ≤ 2) (r : ℝ) (hr : |r| ≤ 1 / 2) :
    Integrable Y P ∧
    Integrable (fun ω => exp (r * (Y ω - ∫ ω, Y ω ∂P))) P ∧
    (∫ ω, exp (r * (Y ω - ∫ ω, Y ω ∂P)) ∂P) ≤ exp (54 * r ^ 2) := by
  have hYI : Integrable Y P := by
    refine (hI.sub (integrable_const 1)).mono' hY.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hY0 ω)]
    simp only [Pi.sub_apply]
    linarith [add_one_le_exp (Y ω)]
  have hm0 : 0 ≤ ∫ ω, Y ω ∂P := integral_nonneg hY0
  have hm1 : (∫ ω, Y ω ∂P) ≤ 1 := by
    have h := integral_mono hYI (hI.sub (integrable_const 1))
      (fun ω => by
        change Y ω ≤ exp (Y ω) - 1
        linarith [add_one_le_exp (Y ω)])
    simp only [Pi.sub_apply] at h
    rw [integral_sub hI (integrable_const 1), integral_const] at h
    simp at h
    linarith
  have hpt := fun ω => positive_centered_pointwise (Y ω) (∫ ω, Y ω ∂P) r
    (hY0 ω) hm0 hm1 hr
  have hIhalf : Integrable (fun ω => exp (Y ω / 2)) P := by
    refine hI.mono' (hY.div_const 2).exp.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_exp.2 (by linarith [hY0 ω])
  have hi : Integrable (fun ω => exp (r * (Y ω - ∫ ω, Y ω ∂P))) P := by
    refine (hIhalf.const_mul 2).mono' (by fun_prop) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact (hpt ω).1
  refine ⟨hYI, hi, ?_⟩
  have hcenter : Integrable (fun ω => Y ω - ∫ ω, Y ω ∂P) P :=
    hYI.sub (integrable_const _)
  have hscaled : Integrable (fun ω => r * (Y ω - ∫ ω, Y ω ∂P)) P :=
    hcenter.const_mul r
  have hlin : Integrable (fun ω => 1 + r * (Y ω - ∫ ω, Y ω ∂P)) P :=
    (integrable_const 1).add hscaled
  calc (∫ ω, exp (r * (Y ω - ∫ ω, Y ω ∂P)) ∂P)
      ≤ ∫ ω, (1 + r * (Y ω - ∫ ω, Y ω ∂P) + 27 * r ^ 2 * exp (Y ω)) ∂P :=
        integral_mono hi (hlin.add (hI.const_mul _)) (fun ω => (hpt ω).2)
    _ = 1 + 27 * r ^ 2 * ∫ ω, exp (Y ω) ∂P := by
      rw [integral_add hlin (hI.const_mul _),
        integral_add (integrable_const _) hscaled,
        integral_const_mul, integral_const_mul, integral_sub hYI (integrable_const _)]
      simp
    _ ≤ 1 + 54 * r ^ 2 := by nlinarith [sq_nonneg r]
    _ ≤ exp (54 * r ^ 2) := by linarith [add_one_le_exp (54 * r ^ 2)]

end HansonWrightDiagonal


-- HansonOrlicz

open MeasureTheory ProbabilityTheory Real

namespace HighDimProb.Concentration

lemma exp_square_at_norm_bound {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y)
    (hsg : ∃ s > 0, Integrable (fun ω => exp (Y ω ^ 2 / s ^ 2)) P ∧
      ∫ ω, exp (Y ω ^ 2 / s ^ 2) ∂P ≤ 2)
    {K : ℝ} (hK : 0 < K) (hnorm : subgaussianNorm P Y ≤ K) :
    Integrable (fun ω => exp (Y ω ^ 2 / (2 * K) ^ 2)) P ∧
      ∫ ω, exp (Y ω ^ 2 / (2 * K) ^ 2) ∂P ≤ 2 := by
  obtain ⟨s0, hs0, hint0, hle0⟩ := hsg
  have hne : ({s : ℝ | 0 < s ∧ Integrable (fun ω => exp (Y ω ^ 2 / s ^ 2)) P ∧
      ∫ ω, exp (Y ω ^ 2 / s ^ 2) ∂P ≤ 2}).Nonempty := ⟨s0, hs0, hint0, hle0⟩
  have hlt : subgaussianNorm P Y < 2 * K := by linarith
  unfold subgaussianNorm at hlt
  obtain ⟨s, ⟨hs, hints, hles⟩, hs2⟩ := exists_lt_of_csInf_lt hne hlt
  have hmono : ∀ ω, exp (Y ω ^ 2 / (2 * K) ^ 2) ≤ exp (Y ω ^ 2 / s ^ 2) := fun ω =>
    exp_le_exp.2 (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (pow_le_pow_left₀ hs.le hs2.le 2))
  have hint2 : Integrable (fun ω => exp (Y ω ^ 2 / (2 * K) ^ 2)) P :=
    hints.mono' ((hY.pow_const 2).div_const _).exp.aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]; exact hmono ω)
  exact ⟨hint2, (integral_mono hint2 hints hmono).trans hles⟩

end HighDimProb.Concentration


-- HansonDiagonalMGF

open MeasureTheory ProbabilityTheory Real

namespace HansonWrightDiagonal

lemma diagonal_mgf {n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (σ : ℝ) (hσ : 0 < σ)
    (hsg : ∀ i, Integrable (fun ω => exp (X i ω ^ 2 / σ ^ 2)) P ∧
      ∫ ω, exp (X i ω ^ 2 / σ ^ 2) ∂P ≤ 2)
    (a : Fin n → ℝ) (s : ℝ) (hs : ∀ i, |s * a i * σ ^ 2| ≤ 1 / 2) :
    (∀ i, Integrable (fun ω => X i ω ^ 2) P) ∧
    Integrable (fun ω => exp (s * ∑ i, a i * (X i ω ^ 2 - ∫ ω, X i ω ^ 2 ∂P))) P ∧
    (∫ ω, exp (s * ∑ i, a i * (X i ω ^ 2 - ∫ ω, X i ω ^ 2 ∂P)) ∂P) ≤
      exp (54 * s ^ 2 * σ ^ 4 * ∑ i, a i ^ 2) := by
  classical
  let Y : Fin n → Ω → ℝ := fun i ω => X i ω ^ 2 / σ ^ 2
  have hm : ∀ i, Measurable (Y i) := fun i => (hX i).pow_const 2 |>.div_const _
  have hy0 : ∀ i ω, 0 ≤ Y i ω := by intro i ω; dsimp [Y]; positivity
  have hc := fun i => positive_centered_mgf P (Y i) (hm i) (hy0 i)
    (hsg i).1 (hsg i).2 (s * a i * σ ^ 2) (hs i)
  have hscale : ∀ i ω, σ ^ 2 * Y i ω = X i ω ^ 2 := by
    intro i ω
    dsimp [Y]
    field_simp
  have hXi : ∀ i, Integrable (fun ω => X i ω ^ 2) P := by
    intro i
    exact ((hc i).1.const_mul (σ ^ 2)).congr (ae_of_all _ fun ω => hscale i ω)
  have hmean : ∀ i, ∫ ω, X i ω ^ 2 ∂P = σ ^ 2 * ∫ ω, Y i ω ∂P := by
    intro i
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun ω => (hscale i ω).symm)
  let W : Fin n → Ω → ℝ := fun i ω => a i * (X i ω ^ 2 - ∫ ω, X i ω ^ 2 ∂P)
  have hw : ∀ i ω, s * W i ω = (s * a i * σ ^ 2) * (Y i ω - ∫ ω, Y i ω ∂P) := by
    intro i ω
    dsimp [W]
    rw [hmean, ← hscale]
    ring
  have hWi : ∀ i, Integrable (fun ω => exp (s * W i ω)) P := by
    intro i
    simpa only [hw] using (hc i).2.1
  have hWb : ∀ i, mgf (W i) P s ≤ exp (54 * (s * a i * σ ^ 2) ^ 2) := by
    intro i
    simpa only [mgf, hw] using (hc i).2.2
  have hWm : ∀ i, Measurable (W i) := by
    intro i
    exact (((hX i).pow_const 2).sub_const _).const_mul _
  have hWind : iIndepFun W P := hind.comp
    (fun i x => a i * (x ^ 2 - ∫ ω, X i ω ^ 2 ∂P)) (fun _ => by fun_prop)
  have hiW : Integrable (fun ω => exp (s * (∑ i, W i) ω)) P :=
    hWind.integrable_exp_mul_sum hWm (fun i _ => hWi i)
  have hsum : mgf (∑ i, W i) P s ≤
      exp (54 * s ^ 2 * σ ^ 4 * ∑ i, a i ^ 2) := by
    rw [hWind.mgf_sum hWm]
    calc (∏ i, mgf (W i) P s) ≤ ∏ i, exp (54 * (s * a i * σ ^ 2) ^ 2) :=
        Finset.prod_le_prod (fun _ _ => mgf_nonneg) (fun i _ => hWb i)
      _ = exp (54 * s ^ 2 * σ ^ 4 * ∑ i, a i ^ 2) := by
        rw [← exp_sum, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring

  refine ⟨hXi, ?_, ?_⟩
  · simpa only [Finset.sum_apply, W] using hiW
  · simpa only [mgf, Finset.sum_apply, W] using hsum

end HansonWrightDiagonal


-- HansonIndependentCopy

open MeasureTheory ProbabilityTheory

namespace HansonWrightCopy

lemma product_copy_indep {ι Ω : Type} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) :
    iIndepFun (Sum.elim (fun i (z : Ω × Ω) => X i z.1)
      (fun i (z : Ω × Ω) => X i z.2)) (P.prod P) := by
  classical
  let Z : ι ⊕ ι → Ω × Ω → ℝ := Sum.elim (fun i z => X i z.1) (fun i z => X i z.2)
  let μ : ι ⊕ ι → Measure ℝ := Sum.elim (fun i => P.map (X i)) (fun i => P.map (X i))
  haveI : ∀ k, IsProbabilityMeasure (μ k) := by
    intro k
    cases k with
    | inl i => exact Measure.isProbabilityMeasure_map (hX i).aemeasurable
    | inr i => exact Measure.isProbabilityMeasure_map (hX i).aemeasurable
  have hZm : ∀ k, Measurable (Z k) := by
    intro k
    cases k with
    | inl i => exact (hX i).comp measurable_fst
    | inr i => exact (hX i).comp measurable_snd
  have hmargin : ∀ k, (P.prod P).map (Z k) = μ k := by
    intro k
    cases k with
    | inl i =>
      change (P.prod P).map (X i ∘ Prod.fst) = P.map (X i)
      rw [← Measure.map_map (hX i) measurable_fst, Measure.map_fst_prod]
      simp
    | inr i =>
      change (P.prod P).map (X i ∘ Prod.snd) = P.map (X i)
      rw [← Measure.map_map (hX i) measurable_snd, Measure.map_snd_prod]
      simp
  have htuple : Measurable (fun ω i => X i ω) := measurable_pi_lambda _ hX
  have hlaw := hind.map_fun_eq_pi_map (fun i => (hX i).aemeasurable)
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ ι => ℝ)
  have heq : (fun z k => Z k z) = e.symm ∘
      Prod.map (fun ω i => X i ω) (fun ω i => X i ω) := by
    funext z k
    cases k <;> rfl
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun k => (hZm k).aemeasurable)).mpr
  simp_rw [hmargin]
  rw [heq, ← Measure.map_map e.symm.measurable (htuple.prodMap htuple),
    ← Measure.map_prod_map P P htuple htuple]
  simp only [hlaw]
  exact (measurePreserving_sumPiEquivProdPi_symm μ).map_eq

lemma fst_identDistrib {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Measurable X) :
    IdentDistrib (fun z : Ω × Ω => X z.1) X (P.prod P) P := by
  refine ⟨(hX.comp measurable_fst).aemeasurable, hX.aemeasurable, ?_⟩
  change (P.prod P).map (X ∘ Prod.fst) = P.map X
  rw [← Measure.map_map hX measurable_fst, Measure.map_fst_prod]
  simp

lemma snd_identDistrib {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Measurable X) :
    IdentDistrib (fun z : Ω × Ω => X z.2) X (P.prod P) P := by
  refine ⟨(hX.comp measurable_snd).aemeasurable, hX.aemeasurable, ?_⟩
  change (P.prod P).map (X ∘ Prod.snd) = P.map X
  rw [← Measure.map_map hX measurable_snd, Measure.map_snd_prod]
  simp

end HansonWrightCopy


-- HansonOffDiagonalMGF

open MeasureTheory ProbabilityTheory Real HighDimProb.Concentration

namespace HighDimProb.QuadraticForms

lemma off_diagonal_mgf {n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hXi : ∀ i, Integrable (X i) P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hsg : ∀ i, ∃ t > 0, Integrable (fun ω => exp (X i ω ^ 2 / t ^ 2)) P ∧
      ∫ ω, exp (X i ω ^ 2 / t ^ 2) ∂P ≤ 2)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, A i i = 0)
    {K : ℝ} (hK : 0 < K) (hnorm : ∀ i, subgaussianNorm P (X i) ≤ K)
    (s : ℝ) (hs : 512 * s ^ 2 * K ^ 4 * opNorm A ^ 2 ≤ 1 / 4) :
    Integrable (fun ω => exp (s * ∑ i, ∑ j, A i j * X i ω * X j ω)) P ∧
    (∫ ω, exp (s * ∑ i, ∑ j, A i j * X i ω * X j ω) ∂P) ≤
      exp (1024 * s ^ 2 * K ^ 4 * frobeniusNorm A ^ 2) := by
  classical
  have hcoef : 4 * (4 * s) ^ 2 * K ^ 2 = 64 * s ^ 2 * K ^ 2 := by ring
  have hg := subgaussian_matrix_sq_laplace P X hX hind hmean hsg A hK hnorm
    (u := 64 * s ^ 2 * K ^ 2) (by positivity) (by nlinarith [hs])
  have hb := bilinear_mgf_reduction P P X X hX hX hind hmean hsg A hK hnorm (4 * s)
    (by simpa only [hcoef] using hg.1)
  have hF2 : Integrable (fun z : Ω × Ω =>
      exp (s * (4 * ∑ i, ∑ j, A i j * X i z.1 * X j z.2))) (P.prod P) := by
    convert hb.1 using 1
    funext z
    congr 1
    ring
  have hF : ConvexOn ℝ Set.univ (fun x : ℝ => exp (s * x)) := by
    simpa only [Set.preimage_univ, Function.comp_def, LinearMap.mulLeft_apply] using
      convexOn_exp.comp_linearMap (LinearMap.mulLeft ℝ s)
  have hd := convex_decoupling_nonneg (P.prod P)
    (fun i z => X i z.1) (fun i z => X i z.2)
    (fun i => (hX i).comp measurable_fst) (fun i => (hX i).comp measurable_snd)
    (HansonWrightCopy.product_copy_indep P X hX hind)
    (fun i => (HansonWrightCopy.fst_identDistrib P (hX i)).integrable_iff.mpr (hXi i))
    (fun i => (HansonWrightCopy.snd_identDistrib P (hX i)).integrable_iff.mpr (hXi i))
    (fun i => (HansonWrightCopy.fst_identDistrib P (hX i)).integral_eq.trans (hmean i))
    (fun i => (HansonWrightCopy.snd_identDistrib P (hX i)).trans
      (HansonWrightCopy.fst_identDistrib P (hX i)).symm)
    A hA (fun x => exp (s * x)) hF (fun _ => (exp_pos _).le) hF2
  have hm : Measurable (fun ω => exp (s * ∑ i, ∑ j, A i j * X i ω * X j ω)) := by
    apply Measurable.exp
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    exact ((hX i).const_mul _).mul (hX j)
  have hdist := HansonWrightCopy.fst_identDistrib P hm
  refine ⟨hdist.integrable_iff.mp hd.1, ?_⟩
  have hble : (∫ z : Ω × Ω, exp (s * (4 * ∑ i, ∑ j, A i j * X i z.1 * X j z.2))
      ∂P.prod P) ≤ exp (1024 * s ^ 2 * K ^ 4 * frobeniusNorm A ^ 2) := by
    have h := hb.2
    simp only [hcoef] at h
    have hg' : (∫ ω, exp (64 * s ^ 2 * K ^ 2 * ∑ j, (∑ i, A i j * X i ω) ^ 2) ∂P) ≤
        exp (1024 * s ^ 2 * K ^ 4 * frobeniusNorm A ^ 2) := by
      convert hg.2 using 1 <;> ring
    calc (∫ z : Ω × Ω, exp (s * (4 * ∑ i, ∑ j, A i j * X i z.1 * X j z.2)) ∂P.prod P)
        = ∫ z : Ω × Ω, exp ((4 * s) * ∑ i, ∑ j, A i j * X i z.1 * X j z.2) ∂P.prod P := by
          apply integral_congr_ae
          apply ae_of_all
          intro z
          congr 1
          ring
      _ ≤ _ := h.trans hg'
  have hle := hd.2.trans hble
  rw [hdist.integral_eq] at hle
  exact hle

end HighDimProb.QuadraticForms


-- HansonSplitMatrix

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace Matrix.Norms.L2Operator

namespace HighDimProb.QuadraticForms

lemma matrix_diagonal_entry_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    |A i i| ≤ opNorm A := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  have he : ⟪b i, T (b i)⟫ = A i i := by
    rw [EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_apply]
    change Matrix.mulVec A (Pi.single i 1) i = A i i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  calc |A i i| = |⟪b i, T (b i)⟫| := by rw [he]
    _ ≤ ‖b i‖ * ‖T (b i)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖b i‖ * (‖T‖ * ‖b i‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
    _ = opNorm A := by rw [b.norm_eq_one]; simp [T, opNorm]

lemma split_matrix_bounds {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    opNorm (A - Matrix.diagonal (fun i => A i i)) ≤ 2 * opNorm A ∧
    frobeniusNorm (A - Matrix.diagonal (fun i => A i i)) ^ 2 ≤ frobeniusNorm A ^ 2 ∧
    (∑ i, A i i ^ 2) ≤ frobeniusNorm A ^ 2 := by
  classical
  have hD : ‖Matrix.diagonal (fun i => A i i)‖ ≤ ‖A‖ := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg A)).mpr
    intro i
    exact matrix_diagonal_entry_bound A i
  refine ⟨?_, ?_, ?_⟩
  · change ‖A - Matrix.diagonal (fun i => A i i)‖ ≤ 2 * ‖A‖
    have h := norm_sub_le A (Matrix.diagonal fun i => A i i)
    linarith
  · rw [frobeniusNorm_sq, frobeniusNorm_sq]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i = j
    · subst j
      simpa using sq_nonneg (A i i)
    · simp [Matrix.sub_apply, Matrix.diagonal_apply, hij]
  · rw [frobeniusNorm_sq]
    apply Finset.sum_le_sum
    intro i _
    exact Finset.single_le_sum (fun j _ => sq_nonneg (A i j)) (Finset.mem_univ i)

end HighDimProb.QuadraticForms


-- HansonQuadraticMean

open MeasureTheory ProbabilityTheory

namespace HighDimProb.QuadraticForms

lemma quadratic_mean {n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hind : iIndepFun X P) (hXi : ∀ i, Integrable (X i) P)
    (hXs : ∀ i, Integrable (fun ω => X i ω ^ 2) P)
    (hmean : ∀ i, ∫ ω, X i ω ∂P = 0) (A : Matrix (Fin n) (Fin n) ℝ) :
    (∫ ω, ∑ i, ∑ j, A i j * X i ω * X j ω ∂P) =
      ∑ i, A i i * ∫ ω, X i ω ^ 2 ∂P := by
  classical
  have hprod : ∀ i j, Integrable (fun ω => X i ω * X j ω) P := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa only [sq] using hXs i
    · exact (hind.indepFun hij).integrable_mul (hXi i) (hXi j)
  have hterm : ∀ i j, Integrable (fun ω => A i j * X i ω * X j ω) P := by
    intro i j
    simpa only [mul_assoc] using (hprod i j).const_mul (A i j)
  have hentry : ∀ i j, (∫ ω, A i j * X i ω * X j ω ∂P) =
      if j = i then A i i * ∫ ω, X i ω ^ 2 ∂P else 0 := by
    intro i j
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    by_cases hji : j = i
    · subst j
      simp [sq]
    · simp only [hji, ite_false]
      have he := (hind.indepFun (Ne.symm hji)).integral_mul_eq_mul_integral
        (hXi i).aestronglyMeasurable (hXi j).aestronglyMeasurable
      simp only [Pi.mul_apply] at he
      rw [he, hmean i]
      ring
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hterm i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hterm i j)]
  simp only [hentry]
  simp

lemma quadratic_remove_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    (∑ i, ∑ j, (A - Matrix.diagonal (fun i => A i i)) i j * x i * x j) =
      (∑ i, ∑ j, A i j * x i * x j) - ∑ i, A i i * x i ^ 2 := by
  classical
  simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [Matrix.diagonal_apply, ite_mul, sq, mul_assoc]

end HighDimProb.QuadraticForms


-- HansonCenteredMGF

open MeasureTheory ProbabilityTheory Real HighDimProb.Concentration

namespace HighDimProb.QuadraticForms

lemma centered_quadratic_mgf {n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hXi : ∀ i, Integrable (X i) P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hsg : ∀ i, ∃ t > 0, Integrable (fun ω => exp (X i ω ^ 2 / t ^ 2)) P ∧
      ∫ ω, exp (X i ω ^ 2 / t ^ 2) ∂P ≤ 2)
    (A : Matrix (Fin n) (Fin n) ℝ) {K : ℝ} (hK : 0 < K)
    (hnorm : ∀ i, subgaussianNorm P (X i) ≤ K)
    (s : ℝ) (hs : |s| * K ^ 2 * opNorm A ≤ 1 / 256) :
    Integrable (fun ω => exp (s * ((∑ i, ∑ j, A i j * X i ω * X j ω) -
      ∫ ω, ∑ i, ∑ j, A i j * X i ω * X j ω ∂P))) P ∧
    (∫ ω, exp (s * ((∑ i, ∑ j, A i j * X i ω * X j ω) -
      ∫ ω, ∑ i, ∑ j, A i j * X i ω * X j ω ∂P)) ∂P) ≤
      exp (4096 * s ^ 2 * K ^ 4 * frobeniusNorm A ^ 2) := by
  classical
  let B := A - Matrix.diagonal (fun i => A i i)
  have hB := split_matrix_bounds A
  have hentry := matrix_diagonal_entry_bound A
  have hσ := fun i => exp_square_at_norm_bound P (X i) (hX i) (hsg i) hK (hnorm i)
  have hdsmall : ∀ i, |(2 * s) * A i i * (2 * K) ^ 2| ≤ 1 / 2 := by
    intro i
    calc |(2 * s) * A i i * (2 * K) ^ 2|
        = 8 * (|s| * K ^ 2 * |A i i|) := by simp only [abs_mul, abs_sq]; norm_num; ring
      _ ≤ 8 * (|s| * K ^ 2 * opNorm A) := by gcongr; exact hentry i
      _ ≤ 1 / 2 := by linarith
  have hd := HansonWrightDiagonal.diagonal_mgf P X hX hind (2 * K) (by positivity)
    hσ (fun i => A i i) (2 * s) hdsmall
  have hnormB : opNorm B ^ 2 ≤ 4 * opNorm A ^ 2 := by
    have h : opNorm B ^ 2 ≤ (2 * opNorm A) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) B)) hB.1 2
    nlinarith only [h]
  have hsq : s ^ 2 * K ^ 4 * opNorm A ^ 2 ≤ (1 / 256 : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (mul_nonneg (mul_nonneg (abs_nonneg s) (sq_nonneg K)) (norm_nonneg _)) hs 2
    simpa only [mul_pow, sq_abs, ← pow_mul, opNorm, (by decide : (2 : ℕ) * 2 = 4)] using h
  have hosmall : 512 * (2 * s) ^ 2 * K ^ 4 * opNorm B ^ 2 ≤ 1 / 4 := by
    have h := mul_le_mul_of_nonneg_left hnormB
      (by positivity : 0 ≤ 512 * (2 * s) ^ 2 * K ^ 4)
    nlinarith only [h, hsq]
  have ho := off_diagonal_mgf P X hX hind hXi hmean hsg B
    (by intro i; simp [B]) hK hnorm (2 * s) hosmall
  let D : Ω → ℝ := fun ω => ∑ i, A i i * (X i ω ^ 2 - ∫ ω, X i ω ^ 2 ∂P)
  let O : Ω → ℝ := fun ω => ∑ i, ∑ j, B i j * X i ω * X j ω
  let Z : Ω → ℝ := fun ω => (∑ i, ∑ j, A i j * X i ω * X j ω) -
    ∫ ω, ∑ i, ∑ j, A i j * X i ω * X j ω ∂P
  have hZ : ∀ ω, Z ω = D ω + O ω := by
    intro ω
    have hm := quadratic_mean P X hind hXi hd.1 hmean A
    have hb := quadratic_remove_diagonal A (fun i => X i ω)
    dsimp [Z, D, O]
    rw [hm]
    simp only [mul_sub, Finset.sum_sub_distrib]
    change _ = _ + ∑ i, ∑ j, (A - Matrix.diagonal (fun i => A i i)) i j * X i ω * X j ω
    linarith only [hb]
  have hdI : Integrable (fun ω => exp ((2 * s) * D ω)) P := hd.2.1
  have hoI : Integrable (fun ω => exp ((2 * s) * O ω)) P := ho.1
  have hdl : (∫ ω, exp ((2 * s) * D ω) ∂P) ≤
      exp (4096 * s ^ 2 * K ^ 4 * frobeniusNorm A ^ 2) := by
    apply hd.2.2.trans
    apply exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hB.2.2 (by positivity : 0 ≤ 3456 * s ^ 2 * K ^ 4)
    nlinarith only [h, (by positivity : 0 ≤ s ^ 2 * K ^ 4 * frobeniusNorm A ^ 2)]
  have hol : (∫ ω, exp ((2 * s) * O ω) ∂P) ≤
      exp (4096 * s ^ 2 * K ^ 4 * frobeniusNorm A ^ 2) := by
    apply ho.2.trans
    apply exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hB.2.1
      (by positivity : 0 ≤ 4096 * s ^ 2 * K ^ 4)
    nlinarith only [h]
  have hexp2 : ∀ x : ℝ, exp ((2 * s) * x) = exp (s * x) ^ 2 := by
    intro x
    rw [sq, ← exp_add]
    congr 1
    ring
  have hpt : ∀ ω, exp (s * Z ω) ≤ (exp ((2 * s) * D ω) + exp ((2 * s) * O ω)) / 2 := by
    intro ω
    rw [hZ, mul_add, exp_add, hexp2, hexp2]
    nlinarith [sq_nonneg (exp (s * D ω) - exp (s * O ω))]
  have hZm : Measurable Z := by
    apply Measurable.sub_const
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    exact ((hX i).const_mul _).mul (hX j)
  have hbound : Integrable (fun ω =>
      (exp ((2 * s) * D ω) + exp ((2 * s) * O ω)) / 2) P := (hdI.add hoI).div_const 2
  have hi : Integrable (fun ω => exp (s * Z ω)) P := by
    refine hbound.mono' (hZm.const_mul s).exp.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact hpt ω
  refine ⟨hi, ?_⟩
  calc (∫ ω, exp (s * Z ω) ∂P)
      ≤ ∫ ω, (exp ((2 * s) * D ω) + exp ((2 * s) * O ω)) / 2 ∂P :=
        integral_mono hi hbound hpt
    _ = ((∫ ω, exp ((2 * s) * D ω) ∂P) + ∫ ω, exp ((2 * s) * O ω) ∂P) / 2 := by
      rw [integral_div, integral_add hdI hoI]
    _ ≤ exp (4096 * s ^ 2 * K ^ 4 * frobeniusNorm A ^ 2) := by linarith

end HighDimProb.QuadraticForms


-- HansonBernsteinTail

open MeasureTheory ProbabilityTheory Real

namespace HansonWrightTail

lemma choose_parameter {V W t : ℝ} (hV : 0 < V) (hW : 0 < W) (ht : 0 ≤ t) :
    ∃ s : ℝ, 0 ≤ s ∧ s * W ≤ 1 / 256 ∧
      -s * t + 4096 * s ^ 2 * V ≤ -(1 / 16384 * min (t ^ 2 / V) (t / W)) := by
  let s := min (t / (8192 * V)) (1 / (256 * W))
  have hs0 : 0 ≤ s := le_min (by positivity) (by positivity)
  have hsmall : s * W ≤ 1 / 256 := by
    have h := mul_le_mul_of_nonneg_right (min_le_right (t / (8192 * V)) (1 / (256 * W))) hW.le
    have he : 1 / (256 * W) * W = (1 / 256 : ℝ) := by field_simp
    simpa only [he] using h
  have hopt : s * (8192 * V) ≤ t := by
    have h : s ≤ t / (8192 * V) := min_le_left _ _
    exact (le_div_iff₀ (by positivity)).mp h
  have hp := mul_le_mul_of_nonneg_left hopt hs0
  have hcost : -s * t + 4096 * s ^ 2 * V ≤ -s * t / 2 := by nlinarith only [hp]
  refine ⟨s, hs0, hsmall, hcost.trans ?_⟩
  rcases le_or_gt (t / (8192 * V)) (1 / (256 * W)) with h | h
  · have hs : s = t / (8192 * V) := min_eq_left h
    rw [hs]
    have he : -(t / (8192 * V)) * t / 2 = -(1 / 16384 * (t ^ 2 / V)) := by
      field_simp
      ring
    rw [he]
    have hm := min_le_left (t ^ 2 / V) (t / W)
    linarith
  · have hs : s = 1 / (256 * W) := min_eq_right h.le
    rw [hs]
    have he : -(1 / (256 * W)) * t / 2 = -(1 / 512 * (t / W)) := by ring
    rw [he]
    have hm := min_le_right (t ^ 2 / V) (t / W)
    have htw : 0 ≤ t / W := by positivity
    linarith

lemma two_sided_tail {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ)
    {V W : ℝ} (hV : 0 < V) (hW : 0 < W)
    (hmgf : ∀ s : ℝ, |s| * W ≤ 1 / 256 →
      Integrable (fun ω => exp (s * Z ω)) P ∧
      (∫ ω, exp (s * Z ω) ∂P) ≤ exp (4096 * s ^ 2 * V))
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t ≤ |Z ω|} ≤
      2 * exp (-(1 / 16384 * min (t ^ 2 / V) (t / W))) := by
  obtain ⟨s, hs, hsmall, hcost⟩ := choose_parameter hV hW ht
  have hsp : |s| * W ≤ 1 / 256 := by simpa only [abs_of_nonneg hs] using hsmall
  have hsn : |-s| * W ≤ 1 / 256 := by simpa only [abs_neg] using hsp
  have hp := hmgf s hsp
  have hn := hmgf (-s) hsn
  have hup : P.real {ω | t ≤ Z ω} ≤ exp (-(1 / 16384 * min (t ^ 2 / V) (t / W))) := by
    calc P.real {ω | t ≤ Z ω} ≤ exp (-s * t) * mgf Z P s :=
        measure_ge_le_exp_mul_mgf t hs hp.1
      _ ≤ exp (-s * t) * exp (4096 * s ^ 2 * V) :=
        mul_le_mul_of_nonneg_left hp.2 (exp_pos _).le
      _ = exp (-s * t + 4096 * s ^ 2 * V) := (exp_add _ _).symm
      _ ≤ _ := exp_le_exp.mpr hcost
  have hni : Integrable (fun ω => exp (s * (-Z ω))) P := by
    simpa only [mul_neg, neg_mul] using hn.1
  have hnb : mgf (fun ω => -Z ω) P s ≤ exp (4096 * s ^ 2 * V) := by
    simpa only [mgf, mul_neg, neg_mul, neg_sq] using hn.2
  have hlo : P.real {ω | t ≤ -Z ω} ≤ exp (-(1 / 16384 * min (t ^ 2 / V) (t / W))) := by
    calc P.real {ω | t ≤ -Z ω} ≤ exp (-s * t) * mgf (fun ω => -Z ω) P s :=
        measure_ge_le_exp_mul_mgf t hs hni
      _ ≤ exp (-s * t) * exp (4096 * s ^ 2 * V) :=
        mul_le_mul_of_nonneg_left hnb (exp_pos _).le
      _ = exp (-s * t + 4096 * s ^ 2 * V) := (exp_add _ _).symm
      _ ≤ _ := exp_le_exp.mpr hcost
  have hsubset : {ω | t ≤ |Z ω|} ⊆ {ω | t ≤ Z ω} ∪ {ω | t ≤ -Z ω} := by
    intro ω hω
    change t ≤ |Z ω| at hω
    change t ≤ Z ω ∨ t ≤ -Z ω
    exact le_abs.mp hω
  calc P.real {ω | t ≤ |Z ω|} ≤ P.real ({ω | t ≤ Z ω} ∪ {ω | t ≤ -Z ω}) :=
      measureReal_mono hsubset
    _ ≤ P.real {ω | t ≤ Z ω} + P.real {ω | t ≤ -Z ω} := measureReal_union_le _ _
    _ ≤ _ := by linarith

end HansonWrightTail


-- HansonMain

open MeasureTheory ProbabilityTheory

open HighDimProb.QuadraticForms

/-- **Theorem 6.2.1** (Hanson-Wright inequality), Vershynin, *High-Dimensional Probability*
(2018), p. 139.

Let `X = (X₁, …, Xₙ) ∈ ℝⁿ` be a random vector with independent, mean zero, sub-gaussian
coordinates. Let `A` be an `n × n` matrix. Then, for every `t ≥ 0`,

`P{|XᵀAX − E XᵀAX| ≥ t} ≤ 2 exp[−c min(t²/(K⁴‖A‖_F²), t/(K²‖A‖))]`,

where `K = maxᵢ ‖Xᵢ‖_{ψ₂}` and `c > 0` is an absolute constant (not depending on `n`, `X`, `A`,
or `t`). -/
theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Fin n → Ω → ℝ),
        (∀ i, Measurable (X i)) →
        iIndepFun X P →
        (∀ i, Integrable (X i) P) →
        (∀ i, ∫ ω, X i ω ∂P = 0) →
        (∀ i, ∃ s > 0, Integrable (fun ω => Real.exp ((X i ω) ^ 2 / s ^ 2)) P ∧
                       ∫ ω, Real.exp ((X i ω) ^ 2 / s ^ 2) ∂P ≤ 2) →
        ∀ (A : Matrix (Fin n) (Fin n) ℝ),
        Integrable (fun ω => ∑ i, ∑ j, A i j * X i ω * X j ω) P →
        ∀ {t : ℝ}, 0 ≤ t →
        P.real {ω | t ≤ |∑ i, ∑ j, A i j * X i ω * X j ω -
                          ∫ ω, ∑ i, ∑ j, A i j * X i ω * X j ω ∂P|} ≤
          2 * Real.exp (-(c * min
            (t ^ 2 / ((⨆ i, HighDimProb.Concentration.subgaussianNorm P (X i)) ^ 4 *
                       frobeniusNorm A ^ 2))
            (t / ((⨆ i, HighDimProb.Concentration.subgaussianNorm P (X i)) ^ 2 *
                   opNorm A))))  := by
  refine ⟨1 / 16384, by norm_num, ?_⟩
  intro n Ω _ P _ X hX hind hXi hmean hsg A hQ t ht
  let K := ⨆ i, HighDimProb.Concentration.subgaussianNorm P (X i)
  let V := K ^ 4 * frobeniusNorm A ^ 2
  let W := K ^ 2 * opNorm A
  let Z : Ω → ℝ := fun ω => (∑ i, ∑ j, A i j * X i ω * X j ω) -
    ∫ ω, ∑ i, ∑ j, A i j * X i ω * X j ω ∂P
  change P.real {ω | t ≤ |Z ω|} ≤ 2 * Real.exp (-(1 / 16384 * min (t ^ 2 / V) (t / W)))
  have hVnn : 0 ≤ V := by dsimp [V]; positivity
  have hWnn : 0 ≤ W := mul_nonneg (sq_nonneg K) (norm_nonneg _)
  by_cases hV : V = 0
  · rw [hV, div_zero, min_eq_left (div_nonneg ht hWnn), mul_zero, neg_zero, Real.exp_zero]
    exact measureReal_le_one.trans (by norm_num)
  by_cases hW : W = 0
  · rw [hW, div_zero, min_eq_right (div_nonneg (sq_nonneg t) hVnn),
      mul_zero, neg_zero, Real.exp_zero]
    exact measureReal_le_one.trans (by norm_num)
  have hVp : 0 < V := lt_of_le_of_ne hVnn (Ne.symm hV)
  have hWp : 0 < W := lt_of_le_of_ne hWnn (Ne.symm hW)
  have hnormnn : ∀ i, 0 ≤ HighDimProb.Concentration.subgaussianNorm P (X i) := by
    intro i
    exact Real.sInf_nonneg (fun s hs => hs.1.le)
  have hKnn : 0 ≤ K := Real.iSup_nonneg hnormnn
  have hKne : K ≠ 0 := by
    intro hk
    apply hW
    dsimp [W]
    rw [hk]
    ring
  have hKp : 0 < K := lt_of_le_of_ne hKnn (Ne.symm hKne)
  have hbdd : BddAbove (Set.range (fun i : Fin n => HighDimProb.Concentration.subgaussianNorm P (X i))) :=
    (Set.finite_range _).bddAbove
  have hnorm : ∀ i, HighDimProb.Concentration.subgaussianNorm P (X i) ≤ K := by
    intro i
    exact le_ciSup hbdd i
  apply HansonWrightTail.two_sided_tail P Z hVp hWp (t := t) _ ht
  intro s hs
  have h := centered_quadratic_mgf P X hX hind hXi hmean hsg A hKp hnorm s
    (by simpa only [W, mul_assoc] using hs)
  simpa only [Z, V, mul_assoc] using h
