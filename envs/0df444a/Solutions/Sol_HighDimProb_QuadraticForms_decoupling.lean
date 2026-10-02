-- Prove2me | solution 1 for HighDimProb.QuadraticForms.decoupling
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-01T13:23:32.334642+00:00
-- url     : https://prove2.me/submissions/28f151a8-8c83-4bdc-96e8-042d0e2eb5f7

import Mathlib


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


open MeasureTheory ProbabilityTheory

open DecouplingProof

/-- **Theorem 6.1.1** (Decoupling), Vershynin, *High-Dimensional Probability* (2018), p. 136.

Let `A` be an `n × n`, diagonal-free matrix (i.e. the diagonal entries of `A` equal zero). Let
`X = (X₁, …, Xₙ)` be a random vector with independent mean zero coordinates `Xᵢ`. Then, for
every convex function `F : ℝ → ℝ`, one has `E F(XᵀAX) ≤ E F(4XᵀAX′)`, where `X′` is an
independent copy of `X`. -/
theorem solution {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X X' : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i)) (hX'_meas : ∀ i, Measurable (X' i))
    (hindep : iIndepFun (Sum.elim X X') P)
    (hX_int : ∀ i, Integrable (X i) P) (hX'_int : ∀ i, Integrable (X' i) P)
    (hX_mean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hX'_dist : ∀ i, IdentDistrib (X' i) (X i) P P)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, A i i = 0)
    (F : ℝ → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (hF1 : Integrable (fun ω => F (∑ i, ∑ j, A i j * X i ω * X j ω)) P)
    (hF2 : Integrable (fun ω => F (4 * ∑ i, ∑ j, A i j * X i ω * X' j ω)) P) :
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




